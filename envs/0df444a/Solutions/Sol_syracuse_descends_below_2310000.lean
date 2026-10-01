-- Prove2me | solution 1 for syracuse_descends_below_2310000
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T18:58:33.635482+00:00
-- url     : https://prove2.me/submissions/5c6b994d-ec15-42cd-badd-c9ce7bca2de1

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_2167436
import Theorems.Thm_syracuse_descends_range_2167435_2169435
import Theorems.Thm_syracuse_descends_range_2169435_2171435
import Theorems.Thm_syracuse_descends_range_2171435_2173435
import Theorems.Thm_syracuse_descends_range_2173435_2175435
import Theorems.Thm_syracuse_descends_range_2175435_2177435
import Theorems.Thm_syracuse_descends_range_2177435_2179435
import Theorems.Thm_syracuse_descends_range_2179435_2181435
import Theorems.Thm_syracuse_descends_range_2181435_2183435
import Theorems.Thm_syracuse_descends_range_2183435_2185435
import Theorems.Thm_syracuse_descends_range_2185435_2187435
import Theorems.Thm_syracuse_descends_range_2187435_2189435
import Theorems.Thm_syracuse_descends_range_2189435_2191435
import Theorems.Thm_syracuse_descends_range_2191435_2193435
import Theorems.Thm_syracuse_descends_range_2193435_2195435
import Theorems.Thm_syracuse_descends_range_2195435_2197435
import Theorems.Thm_syracuse_descends_range_2197435_2199435
import Theorems.Thm_syracuse_descends_range_2199435_2201435
import Theorems.Thm_syracuse_descends_range_2201435_2203435
import Theorems.Thm_syracuse_descends_range_2203435_2205435
import Theorems.Thm_syracuse_descends_range_2205435_2207435
import Theorems.Thm_syracuse_descends_range_2207435_2209435
import Theorems.Thm_syracuse_descends_range_2209435_2211435
import Theorems.Thm_syracuse_descends_range_2211435_2213435
import Theorems.Thm_syracuse_descends_range_2213435_2215435
import Theorems.Thm_syracuse_descends_range_2215435_2217435
import Theorems.Thm_syracuse_descends_range_2217435_2219435
import Theorems.Thm_syracuse_descends_range_2219435_2221435
import Theorems.Thm_syracuse_descends_range_2221435_2223435
import Theorems.Thm_syracuse_descends_range_2223435_2225435
import Theorems.Thm_syracuse_descends_range_2225435_2227435
import Theorems.Thm_syracuse_descends_range_2227435_2229435
import Theorems.Thm_syracuse_descends_range_2229435_2231435
import Theorems.Thm_syracuse_descends_range_2231435_2233435
import Theorems.Thm_syracuse_descends_range_2233435_2235435
import Theorems.Thm_syracuse_descends_range_2235435_2237435
import Theorems.Thm_syracuse_descends_range_2237435_2239435
import Theorems.Thm_syracuse_descends_range_2239435_2241435
import Theorems.Thm_syracuse_descends_range_2241435_2243435
import Theorems.Thm_syracuse_descends_range_2243435_2245435
import Theorems.Thm_syracuse_descends_range_2245435_2247435
import Theorems.Thm_syracuse_descends_range_2247435_2249435
import Theorems.Thm_syracuse_descends_range_2249435_2251435
import Theorems.Thm_syracuse_descends_range_2251435_2253435
import Theorems.Thm_syracuse_descends_range_2253435_2255435
import Theorems.Thm_syracuse_descends_range_2255435_2257435
import Theorems.Thm_syracuse_descends_range_2257435_2259435
import Theorems.Thm_syracuse_descends_range_2259435_2261435
import Theorems.Thm_syracuse_descends_range_2261435_2263435
import Theorems.Thm_syracuse_descends_range_2263435_2265435
import Theorems.Thm_syracuse_descends_range_2265435_2267435
import Theorems.Thm_syracuse_descends_range_2267435_2269435
import Theorems.Thm_syracuse_descends_range_2269435_2271435
import Theorems.Thm_syracuse_descends_range_2271435_2273435
import Theorems.Thm_syracuse_descends_range_2273435_2275435
import Theorems.Thm_syracuse_descends_range_2275435_2277435
import Theorems.Thm_syracuse_descends_range_2277435_2279435
import Theorems.Thm_syracuse_descends_range_2279435_2281435
import Theorems.Thm_syracuse_descends_range_2281435_2283435
import Theorems.Thm_syracuse_descends_range_2283435_2285435
import Theorems.Thm_syracuse_descends_range_2285435_2287435
import Theorems.Thm_syracuse_descends_range_2287435_2289435
import Theorems.Thm_syracuse_descends_range_2289435_2291435
import Theorems.Thm_syracuse_descends_range_2291435_2293435
import Theorems.Thm_syracuse_descends_range_2293435_2295435
import Theorems.Thm_syracuse_descends_range_2295435_2297435
import Theorems.Thm_syracuse_descends_range_2297435_2299435
import Theorems.Thm_syracuse_descends_range_2299435_2301435
import Theorems.Thm_syracuse_descends_range_2301435_2303435
import Theorems.Thm_syracuse_descends_range_2303435_2305435
import Theorems.Thm_syracuse_descends_range_2305435_2307435
import Theorems.Thm_syracuse_descends_range_2307435_2309435
import Theorems.Thm_syracuse_descends_range_2309435_2309999

set_option maxHeartbeats 1000000
theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 2310000) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 2167436 with hp | hp
  · exact syracuse_descends_below_2167436 m h1 hp hodd
  rcases Nat.lt_or_ge m 2169436 with hz0 | hz0
  · exact syracuse_descends_range_2167435_2169435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2171436 with hz1 | hz1
  · exact syracuse_descends_range_2169435_2171435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2173436 with hz2 | hz2
  · exact syracuse_descends_range_2171435_2173435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2175436 with hz3 | hz3
  · exact syracuse_descends_range_2173435_2175435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2177436 with hz4 | hz4
  · exact syracuse_descends_range_2175435_2177435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2179436 with hz5 | hz5
  · exact syracuse_descends_range_2177435_2179435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2181436 with hz6 | hz6
  · exact syracuse_descends_range_2179435_2181435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2183436 with hz7 | hz7
  · exact syracuse_descends_range_2181435_2183435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2185436 with hz8 | hz8
  · exact syracuse_descends_range_2183435_2185435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2187436 with hz9 | hz9
  · exact syracuse_descends_range_2185435_2187435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2189436 with hz10 | hz10
  · exact syracuse_descends_range_2187435_2189435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2191436 with hz11 | hz11
  · exact syracuse_descends_range_2189435_2191435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2193436 with hz12 | hz12
  · exact syracuse_descends_range_2191435_2193435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2195436 with hz13 | hz13
  · exact syracuse_descends_range_2193435_2195435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2197436 with hz14 | hz14
  · exact syracuse_descends_range_2195435_2197435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2199436 with hz15 | hz15
  · exact syracuse_descends_range_2197435_2199435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2201436 with hz16 | hz16
  · exact syracuse_descends_range_2199435_2201435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2203436 with hz17 | hz17
  · exact syracuse_descends_range_2201435_2203435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2205436 with hz18 | hz18
  · exact syracuse_descends_range_2203435_2205435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2207436 with hz19 | hz19
  · exact syracuse_descends_range_2205435_2207435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2209436 with hz20 | hz20
  · exact syracuse_descends_range_2207435_2209435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2211436 with hz21 | hz21
  · exact syracuse_descends_range_2209435_2211435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2213436 with hz22 | hz22
  · exact syracuse_descends_range_2211435_2213435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2215436 with hz23 | hz23
  · exact syracuse_descends_range_2213435_2215435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2217436 with hz24 | hz24
  · exact syracuse_descends_range_2215435_2217435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2219436 with hz25 | hz25
  · exact syracuse_descends_range_2217435_2219435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2221436 with hz26 | hz26
  · exact syracuse_descends_range_2219435_2221435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2223436 with hz27 | hz27
  · exact syracuse_descends_range_2221435_2223435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2225436 with hz28 | hz28
  · exact syracuse_descends_range_2223435_2225435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2227436 with hz29 | hz29
  · exact syracuse_descends_range_2225435_2227435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2229436 with hz30 | hz30
  · exact syracuse_descends_range_2227435_2229435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2231436 with hz31 | hz31
  · exact syracuse_descends_range_2229435_2231435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2233436 with hz32 | hz32
  · exact syracuse_descends_range_2231435_2233435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2235436 with hz33 | hz33
  · exact syracuse_descends_range_2233435_2235435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2237436 with hz34 | hz34
  · exact syracuse_descends_range_2235435_2237435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2239436 with hz35 | hz35
  · exact syracuse_descends_range_2237435_2239435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2241436 with hz36 | hz36
  · exact syracuse_descends_range_2239435_2241435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2243436 with hz37 | hz37
  · exact syracuse_descends_range_2241435_2243435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2245436 with hz38 | hz38
  · exact syracuse_descends_range_2243435_2245435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2247436 with hz39 | hz39
  · exact syracuse_descends_range_2245435_2247435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2249436 with hz40 | hz40
  · exact syracuse_descends_range_2247435_2249435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2251436 with hz41 | hz41
  · exact syracuse_descends_range_2249435_2251435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2253436 with hz42 | hz42
  · exact syracuse_descends_range_2251435_2253435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2255436 with hz43 | hz43
  · exact syracuse_descends_range_2253435_2255435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2257436 with hz44 | hz44
  · exact syracuse_descends_range_2255435_2257435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2259436 with hz45 | hz45
  · exact syracuse_descends_range_2257435_2259435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2261436 with hz46 | hz46
  · exact syracuse_descends_range_2259435_2261435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2263436 with hz47 | hz47
  · exact syracuse_descends_range_2261435_2263435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2265436 with hz48 | hz48
  · exact syracuse_descends_range_2263435_2265435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2267436 with hz49 | hz49
  · exact syracuse_descends_range_2265435_2267435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2269436 with hz50 | hz50
  · exact syracuse_descends_range_2267435_2269435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2271436 with hz51 | hz51
  · exact syracuse_descends_range_2269435_2271435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2273436 with hz52 | hz52
  · exact syracuse_descends_range_2271435_2273435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2275436 with hz53 | hz53
  · exact syracuse_descends_range_2273435_2275435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2277436 with hz54 | hz54
  · exact syracuse_descends_range_2275435_2277435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2279436 with hz55 | hz55
  · exact syracuse_descends_range_2277435_2279435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2281436 with hz56 | hz56
  · exact syracuse_descends_range_2279435_2281435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2283436 with hz57 | hz57
  · exact syracuse_descends_range_2281435_2283435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2285436 with hz58 | hz58
  · exact syracuse_descends_range_2283435_2285435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2287436 with hz59 | hz59
  · exact syracuse_descends_range_2285435_2287435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2289436 with hz60 | hz60
  · exact syracuse_descends_range_2287435_2289435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2291436 with hz61 | hz61
  · exact syracuse_descends_range_2289435_2291435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2293436 with hz62 | hz62
  · exact syracuse_descends_range_2291435_2293435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2295436 with hz63 | hz63
  · exact syracuse_descends_range_2293435_2295435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2297436 with hz64 | hz64
  · exact syracuse_descends_range_2295435_2297435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2299436 with hz65 | hz65
  · exact syracuse_descends_range_2297435_2299435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2301436 with hz66 | hz66
  · exact syracuse_descends_range_2299435_2301435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2303436 with hz67 | hz67
  · exact syracuse_descends_range_2301435_2303435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2305436 with hz68 | hz68
  · exact syracuse_descends_range_2303435_2305435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2307436 with hz69 | hz69
  · exact syracuse_descends_range_2305435_2307435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2309436 with hz70 | hz70
  · exact syracuse_descends_range_2307435_2309435 m (by omega) (by omega) hodd
  exact syracuse_descends_range_2309435_2309999 m (by omega) (by omega) hodd
