#include <linux/bpf.h>
#include <linux/if_ether.h>
#include <linux/ip.h>
#include <linux/ipv6.h>
#include <linux/udp.h>
#include <linux/tcp.h>
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_endian.h>

#define IP_CSUM_OFF(ETH_HLEN + offsetof(struct iphdr, check))
#define IPV6_CSUM_OFF(sizeof(struct ipv6hdr) + offsetof(struct udphdr, check))

struct challenge {
  __u64 timestamp;
  __u32 cookie;
  __u8 mac[6];
};

struct {
  __uint(type, BPF_MAP_TYPE_LRU_HASH);
  __type(key, __u32); // src IP (v4) ili hash za v6
  __type(value, struct challenge);
  __uint(max_entries, 1000000);
}
challenge_sent SEC(".maps");

struct {
  __uint(type, BPF_MAP_TYPE_LRU_PERCPU_HASH);
  __type(key, __u32);
  __type(value, __u64); // timestamp kad je prošao challenge
  __uint(max_entries, 2000000);
}
whitelist SEC(".maps");

// Lista legit portova (dodaj svoje ako treba)
static __u16 legit_ports[] = {
  53,
  1194,
  2896,
  2300,
  3659,
  4970,
  4971,
  4972,
  4973,
  4974,
  4975,
  4976,
  4977,
  4978,
  4979,
  4980,
  7000,
  8999, // 7000-8999 kao range
  9000,
  9999, // 9000-9999
  22000,
  22126,
  27000,
  27500,
  28015,
  30000,
  32000,
  51820
};

static inline int is_legit_port(__u16 port) {
  __u16 dport = bpf_ntohs(port);
  if (dport == 53 || dport == 1194 || dport == 2896 || dport == 2300 || dport == 3659 || dport == 28015 || dport == 51820)
    return 1;
  if (dport >= 4970 && dport <= 4980) return 1;
  if (dport >= 7000 && dport <= 8999) return 1;
  if (dport >= 9000 && dport <= 9999) return 1;
  if (dport >= 22000 && dport <= 22126) return 1;
  if (dport >= 27000 && dport <= 27500) return 1;
  if (dport >= 30000 && dport <= 32000) return 1;
  return 0;
}

// Generiše random cookie (koristi src port + time)
static inline __u32 gen_cookie(__u16 src_port, __u64 ts) {
  return bpf_get_prandom_u32() ^ src_port ^ (ts & 0xffffffff);
}

// Provera da li je payload "legit" za određeni protokol (prvih par bajtova)
static inline int payload_looks_legit(void * data, void * data_end, __u16 dport) {
  // DNS
  if (dport == 53) {
    if (data + 12 > data_end) return 0;
    __u16 flags = * (__u16 * )(data + 2);
    return (bpf_ntohs(flags) & 0x8000) == 0; // QR=0 (query)
  }
  // OpenVPN
  if (dport == 1194) return ( * (char * ) data & 0x38) >> 3 == 7; // P_CONTROL_HARD_RESET_CLIENT_V2/3
  // Wireguard
  if (dport == 51820) return data + 4 <= data_end && * (char * ) data == 1; // type 1 handshake initiation
  // Steam A2S
  if (dport >= 27000 && dport <= 27500) return data + 4 <= data_end && * (__u32 * ) data == 0xffffffff;
  // RakNet (Rust, Unturned)
  if (dport == 28015) return data + 1 <= data_end && * (char * ) data == '\x05'; // offline message

  if (dport == 7777 || (dport >= 7000 && dport <= 8999)) {
    if (data + 1 > data_end) return 0;
    __u8 first = * (__u8 * ) data;
    if (first == 0x01 || first == 0x02) return 1;
  }

  // AltV (obično 7788 UDP, ali i u 7000-8999 range)
  if (dport == 7788 || (dport >= 7000 && dport <= 8999)) {
    if (data + 4 <= data_end) {
      if ( * (__u32 * ) data == 0x544C41) // "ALT\0" little-endian
        return 1;
    }
  }

  // FiveM / RedM / RedM (30000-32000 UDP + TCP init)
  if (dport >= 30000 && dport <= 32000) {
    if (data + 8 <= data_end && * (__u32 * ) data == 0xffffffff) {
      char * str = (char * )(data + 4);
      if (bpf_strncmp(str, 7, "getinfo") == 0 || bpf_strncmp(str, 4, "info") == 0)
        return 1;
    }
    // FiveM connect packe
    if (data + 16 <= data_end) {
      if ( * (__u64 * ) data == 0x0000000000000000 && * (__u64 * )(data + 8) == 0x636F6E6E656374) // "connect\0"
        return 1;
    }
  }

  // Mordhau (frequently in 7000-8999 + 15000)
  if (dport >= 7000 && dport <= 8999 || dport == 15000 || dport == 7777 || dport == 27015) {
    // Mordhau beacon: počinje sa 0x00 0x00 0x00 0x00 ili 0x01 0x00 0x00 0x00
    if (data + 4 <= data_end && * (__u32 * ) data <= 0x00000001)
      return 1;
  }

  // Squad (često 7787, 21114, 27165 itd.)
  if (dport == 7787 || dport == 21114 || dport == 27165 || dport >= 7000 && dport <= 8999) {
    if (data + 2 <= data_end && * (__u16 * ) data == 0x0000)
      return 1;
  }

  // Hell Let Loose
  if (dport == 8778 || dport == 27015 || (dport >= 7000 && dport <= 8999)) {
    if (data + 4 <= data_end && * (__u32 * ) data == 0x00000000)
      return 1;
  }

  // ARK: Survival Evolved (query port = gameport + 15 000, npr. 7777 + 15000 = 22777)
  if (dport >= 19132 && dport <= 65535) { // ARK query portovi su visoki
    if (data + 5 <= data_end && * (__u32 * ) data == 0xffffffff && * (__u8 * )(data + 4) == 'T')
      return 1; // \xFF\xFF\xFF\xFF TSource Engine Query
  }

  // Unturned (RakNet-based, često 27015-27030)
  if (dport >= 27015 && dport <= 27030) {
    if (data + 1 <= data_end) {
      __u8 id = * (__u8 * ) data;
      // Unturned offline message ID: 0x05 - 0x0E su legit
      if (id >= 0x05 && id <= 0x0E)
        return 1;
    }
  }
  return 1; // ostali protokoli – prihvatamo prvi paket
}

SEC("xdp")
int xdp_anti_ddos(struct xdp_md * ctx) {
  void * data = (void * )(long) ctx -> data;
  void * data_end = (void * )(long) ctx -> data_end;

  struct ethhdr * eth = data;
  if (data + sizeof( * eth) > data_end) return XDP_PASS;

  if (eth -> h_proto == bpf_htons(ETH_P_IP)) {
    struct iphdr * ip = data + sizeof( * eth);
    if ((void * ) & ip[1] > data_end) return XDP_PASS;

    if (ip -> protocol == IPPROTO_UDP) {
      struct udphdr * udp = (void * )(ip + 1);
      if ((void * )(udp + 1) > data_end) return XDP_PASS;

      __u16 dport = bpf_ntohs(udp -> dest);

      if (!is_legit_port(udp -> dest)) return XDP_PASS; // nije naš port → kernel

      __u32 src_ip = ip -> saddr;
      __u64 ts = bpf_ktime_get_ns();

      // Proveri whitelist
      __u64 * wl_ts = bpf_map_lookup_elem( & whitelist, & src_ip);
      if (wl_ts && ts - * wl_ts < 180000000000 ULL) // 180 sekundi whitelist
        return XDP_PASS;

      void * payload = (void * )(udp + 1);
      int legit = payload_looks_legit(payload, data_end, dport);

      // Ako je ovo odgovor na challenge (drugi paket sa istim cookie-om)
      if (data_end - payload >= 8) {
        __u32 * maybe_cookie = payload;
        struct challenge * ch = bpf_map_lookup_elem( & challenge_sent, & src_ip);
        if (ch && ch -> cookie == * maybe_cookie && ts - ch -> timestamp < 5000000000 ULL) { // 5s
          __u64 now = bpf_ktime_get_ns();
          bpf_map_update_elem( & whitelist, & src_ip, & now, BPF_ANY);
          bpf_map_delete_elem( & challenge_sent, & src_ip);
          return XDP_PASS;
        }
      }

      // Ako payload izgleda legit → pošalji challenge
      if (legit) {
        __u32 cookie = gen_cookie(udp -> source, ts);
        struct challenge ch = {
          .timestamp = ts,
          .cookie = cookie
        };

        bpf_map_update_elem( & challenge_sent, & src_ip, & ch, BPF_ANY);

        // Pošalji challenge paket (cookie kao payload)
        char challenge_pkt[64] = {
          0
        };
        __builtin_memcpy(challenge_pkt, eth, data_end - data);
        struct iphdr * rip = (void * )(challenge_pkt + sizeof( * eth));
        struct udphdr * rudp = (void * )(rip + 1);
        __u32 * payload_out = (__u32 * )(rudp + 1);

        rip -> ttl = 64;
        rip -> saddr = ip -> daddr;
        rip -> daddr = ip -> saddr;
        rudp -> source = udp -> dest;
        rudp -> dest = udp -> source;
        rudp -> len = bpf_htons(sizeof(struct udphdr) + 8);
        * payload_out = cookie;

        bpf_xdp_adjust_head(ctx, -(int) sizeof(__u32)); 
        return bpf_redirect_map( & tx_port, 0, 0); 
      }

      return XDP_DROP;
    }

    if (ip -> protocol == IPPROTO_TCP) {
      // Za igre koje koriste TCP init (FiveM, SCUM, RedM)
      struct tcphdr * tcp = (void * )(ip + 1);
      if ((void * )(tcp + 1) > data_end) return XDP_PASS;
      __u16 dport = bpf_ntohs(tcp -> dest);
      if ((dport >= 30000 && dport <= 32000) || dport == 2895) {
        if (tcp -> syn && !tcp -> ack) // dozvoli TCP handshake
          return XDP_PASS;
      }
    }
  }

  return XDP_PASS;
}

char _license[] SEC("license") = "GPL";
