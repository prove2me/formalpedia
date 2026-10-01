-- Prove2me | solution 1 for syracuse_descends_below_2167436
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T18:55:18.97516+00:00
-- url     : https://prove2.me/submissions/67cc6ccc-2aa6-4827-a609-5e892ce09f81

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_below_2025436
import Theorems.Thm_syracuse_descends_range_2025435_2027435
import Theorems.Thm_syracuse_descends_range_2027435_2029435
import Theorems.Thm_syracuse_descends_range_2029435_2031435
import Theorems.Thm_syracuse_descends_range_2031435_2033435
import Theorems.Thm_syracuse_descends_range_2033435_2035435
import Theorems.Thm_syracuse_descends_range_2035435_2037435
import Theorems.Thm_syracuse_descends_range_2037435_2039435
import Theorems.Thm_syracuse_descends_range_2039435_2041435
import Theorems.Thm_syracuse_descends_range_2041435_2043435
import Theorems.Thm_syracuse_descends_range_2043435_2045435
import Theorems.Thm_syracuse_descends_range_2045435_2047435
import Theorems.Thm_syracuse_descends_range_2047435_2049435
import Theorems.Thm_syracuse_descends_range_2049435_2051435
import Theorems.Thm_syracuse_descends_range_2051435_2053435
import Theorems.Thm_syracuse_descends_range_2053435_2055435
import Theorems.Thm_syracuse_descends_range_2055435_2057435
import Theorems.Thm_syracuse_descends_range_2057435_2059435
import Theorems.Thm_syracuse_descends_range_2059435_2061435
import Theorems.Thm_syracuse_descends_range_2061435_2063435
import Theorems.Thm_syracuse_descends_range_2063435_2065435
import Theorems.Thm_syracuse_descends_range_2065435_2067435
import Theorems.Thm_syracuse_descends_range_2067435_2069435
import Theorems.Thm_syracuse_descends_range_2069435_2071435
import Theorems.Thm_syracuse_descends_range_2071435_2073435
import Theorems.Thm_syracuse_descends_range_2073435_2075435
import Theorems.Thm_syracuse_descends_range_2075435_2077435
import Theorems.Thm_syracuse_descends_range_2077435_2079435
import Theorems.Thm_syracuse_descends_range_2079435_2081435
import Theorems.Thm_syracuse_descends_range_2081435_2083435
import Theorems.Thm_syracuse_descends_range_2083435_2085435
import Theorems.Thm_syracuse_descends_range_2085435_2087435
import Theorems.Thm_syracuse_descends_range_2087435_2089435
import Theorems.Thm_syracuse_descends_range_2089435_2091435
import Theorems.Thm_syracuse_descends_range_2091435_2093435
import Theorems.Thm_syracuse_descends_range_2093435_2095435
import Theorems.Thm_syracuse_descends_range_2095435_2097435
import Theorems.Thm_syracuse_descends_range_2097435_2099435
import Theorems.Thm_syracuse_descends_range_2099435_2101435
import Theorems.Thm_syracuse_descends_range_2101435_2103435
import Theorems.Thm_syracuse_descends_range_2103435_2105435
import Theorems.Thm_syracuse_descends_range_2105435_2107435
import Theorems.Thm_syracuse_descends_range_2107435_2109435
import Theorems.Thm_syracuse_descends_range_2109435_2111435
import Theorems.Thm_syracuse_descends_range_2111435_2113435
import Theorems.Thm_syracuse_descends_range_2113435_2115435
import Theorems.Thm_syracuse_descends_range_2115435_2117435
import Theorems.Thm_syracuse_descends_range_2117435_2119435
import Theorems.Thm_syracuse_descends_range_2119435_2121435
import Theorems.Thm_syracuse_descends_range_2121435_2123435
import Theorems.Thm_syracuse_descends_range_2123435_2125435
import Theorems.Thm_syracuse_descends_range_2125435_2127435
import Theorems.Thm_syracuse_descends_range_2127435_2129435
import Theorems.Thm_syracuse_descends_range_2129435_2131435
import Theorems.Thm_syracuse_descends_range_2131435_2133435
import Theorems.Thm_syracuse_descends_range_2133435_2135435
import Theorems.Thm_syracuse_descends_range_2135435_2137435
import Theorems.Thm_syracuse_descends_range_2137435_2139435
import Theorems.Thm_syracuse_descends_range_2139435_2141435
import Theorems.Thm_syracuse_descends_range_2141435_2143435
import Theorems.Thm_syracuse_descends_range_2143435_2145435
import Theorems.Thm_syracuse_descends_range_2145435_2147435
import Theorems.Thm_syracuse_descends_range_2147435_2149435
import Theorems.Thm_syracuse_descends_range_2149435_2151435
import Theorems.Thm_syracuse_descends_range_2151435_2153435
import Theorems.Thm_syracuse_descends_range_2153435_2155435
import Theorems.Thm_syracuse_descends_range_2155435_2157435
import Theorems.Thm_syracuse_descends_range_2157435_2159435
import Theorems.Thm_syracuse_descends_range_2159435_2161435
import Theorems.Thm_syracuse_descends_range_2161435_2163435
import Theorems.Thm_syracuse_descends_range_2163435_2165435
import Theorems.Thm_syracuse_descends_range_2165435_2167435

set_option maxHeartbeats 1000000
theorem solution (m : ℕ) (h1 : 1 < m) (hlt : m < 2167436) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 2025436 with hp | hp
  · exact syracuse_descends_below_2025436 m h1 hp hodd
  rcases Nat.lt_or_ge m 2027436 with hz0 | hz0
  · exact syracuse_descends_range_2025435_2027435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2029436 with hz1 | hz1
  · exact syracuse_descends_range_2027435_2029435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2031436 with hz2 | hz2
  · exact syracuse_descends_range_2029435_2031435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2033436 with hz3 | hz3
  · exact syracuse_descends_range_2031435_2033435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2035436 with hz4 | hz4
  · exact syracuse_descends_range_2033435_2035435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2037436 with hz5 | hz5
  · exact syracuse_descends_range_2035435_2037435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2039436 with hz6 | hz6
  · exact syracuse_descends_range_2037435_2039435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2041436 with hz7 | hz7
  · exact syracuse_descends_range_2039435_2041435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2043436 with hz8 | hz8
  · exact syracuse_descends_range_2041435_2043435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2045436 with hz9 | hz9
  · exact syracuse_descends_range_2043435_2045435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2047436 with hz10 | hz10
  · exact syracuse_descends_range_2045435_2047435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2049436 with hz11 | hz11
  · exact syracuse_descends_range_2047435_2049435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2051436 with hz12 | hz12
  · exact syracuse_descends_range_2049435_2051435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2053436 with hz13 | hz13
  · exact syracuse_descends_range_2051435_2053435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2055436 with hz14 | hz14
  · exact syracuse_descends_range_2053435_2055435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2057436 with hz15 | hz15
  · exact syracuse_descends_range_2055435_2057435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2059436 with hz16 | hz16
  · exact syracuse_descends_range_2057435_2059435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2061436 with hz17 | hz17
  · exact syracuse_descends_range_2059435_2061435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2063436 with hz18 | hz18
  · exact syracuse_descends_range_2061435_2063435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2065436 with hz19 | hz19
  · exact syracuse_descends_range_2063435_2065435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2067436 with hz20 | hz20
  · exact syracuse_descends_range_2065435_2067435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2069436 with hz21 | hz21
  · exact syracuse_descends_range_2067435_2069435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2071436 with hz22 | hz22
  · exact syracuse_descends_range_2069435_2071435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2073436 with hz23 | hz23
  · exact syracuse_descends_range_2071435_2073435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2075436 with hz24 | hz24
  · exact syracuse_descends_range_2073435_2075435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2077436 with hz25 | hz25
  · exact syracuse_descends_range_2075435_2077435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2079436 with hz26 | hz26
  · exact syracuse_descends_range_2077435_2079435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2081436 with hz27 | hz27
  · exact syracuse_descends_range_2079435_2081435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2083436 with hz28 | hz28
  · exact syracuse_descends_range_2081435_2083435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2085436 with hz29 | hz29
  · exact syracuse_descends_range_2083435_2085435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2087436 with hz30 | hz30
  · exact syracuse_descends_range_2085435_2087435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2089436 with hz31 | hz31
  · exact syracuse_descends_range_2087435_2089435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2091436 with hz32 | hz32
  · exact syracuse_descends_range_2089435_2091435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2093436 with hz33 | hz33
  · exact syracuse_descends_range_2091435_2093435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2095436 with hz34 | hz34
  · exact syracuse_descends_range_2093435_2095435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2097436 with hz35 | hz35
  · exact syracuse_descends_range_2095435_2097435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2099436 with hz36 | hz36
  · exact syracuse_descends_range_2097435_2099435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2101436 with hz37 | hz37
  · exact syracuse_descends_range_2099435_2101435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2103436 with hz38 | hz38
  · exact syracuse_descends_range_2101435_2103435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2105436 with hz39 | hz39
  · exact syracuse_descends_range_2103435_2105435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2107436 with hz40 | hz40
  · exact syracuse_descends_range_2105435_2107435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2109436 with hz41 | hz41
  · exact syracuse_descends_range_2107435_2109435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2111436 with hz42 | hz42
  · exact syracuse_descends_range_2109435_2111435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2113436 with hz43 | hz43
  · exact syracuse_descends_range_2111435_2113435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2115436 with hz44 | hz44
  · exact syracuse_descends_range_2113435_2115435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2117436 with hz45 | hz45
  · exact syracuse_descends_range_2115435_2117435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2119436 with hz46 | hz46
  · exact syracuse_descends_range_2117435_2119435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2121436 with hz47 | hz47
  · exact syracuse_descends_range_2119435_2121435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2123436 with hz48 | hz48
  · exact syracuse_descends_range_2121435_2123435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2125436 with hz49 | hz49
  · exact syracuse_descends_range_2123435_2125435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2127436 with hz50 | hz50
  · exact syracuse_descends_range_2125435_2127435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2129436 with hz51 | hz51
  · exact syracuse_descends_range_2127435_2129435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2131436 with hz52 | hz52
  · exact syracuse_descends_range_2129435_2131435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2133436 with hz53 | hz53
  · exact syracuse_descends_range_2131435_2133435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2135436 with hz54 | hz54
  · exact syracuse_descends_range_2133435_2135435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2137436 with hz55 | hz55
  · exact syracuse_descends_range_2135435_2137435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2139436 with hz56 | hz56
  · exact syracuse_descends_range_2137435_2139435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2141436 with hz57 | hz57
  · exact syracuse_descends_range_2139435_2141435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2143436 with hz58 | hz58
  · exact syracuse_descends_range_2141435_2143435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2145436 with hz59 | hz59
  · exact syracuse_descends_range_2143435_2145435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2147436 with hz60 | hz60
  · exact syracuse_descends_range_2145435_2147435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2149436 with hz61 | hz61
  · exact syracuse_descends_range_2147435_2149435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2151436 with hz62 | hz62
  · exact syracuse_descends_range_2149435_2151435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2153436 with hz63 | hz63
  · exact syracuse_descends_range_2151435_2153435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2155436 with hz64 | hz64
  · exact syracuse_descends_range_2153435_2155435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2157436 with hz65 | hz65
  · exact syracuse_descends_range_2155435_2157435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2159436 with hz66 | hz66
  · exact syracuse_descends_range_2157435_2159435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2161436 with hz67 | hz67
  · exact syracuse_descends_range_2159435_2161435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2163436 with hz68 | hz68
  · exact syracuse_descends_range_2161435_2163435 m (by omega) (by omega) hodd
  rcases Nat.lt_or_ge m 2165436 with hz69 | hz69
  · exact syracuse_descends_range_2163435_2165435 m (by omega) (by omega) hodd
  exact syracuse_descends_range_2165435_2167435 m (by omega) (by omega) hodd
