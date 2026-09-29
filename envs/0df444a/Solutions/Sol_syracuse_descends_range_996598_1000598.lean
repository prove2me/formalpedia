-- Prove2me | solution 1 for syracuse_descends_range_996598_1000598
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:13.112568+00:00
-- url     : https://prove2.me/submissions/f2bee360-d50e-48e3-ac8b-0fc9002332a2

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B2129933 : Blo 996598 2129933 := bbase (se 3 (by rfl) ⟨399362, by rfl⟩ : syracuseStep 2129933 = 798725) (by norm_num)
theorem B2523221 : Blo 996598 2523221 := bbase (se 8 (by rfl) ⟨14784, by rfl⟩ : syracuseStep 2523221 = 29569) (by norm_num)
theorem B3375269 : Blo 996598 3375269 := bbase (se 4 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 3375269 = 632863) (by norm_num)
theorem B2523413 : Blo 996598 2523413 := bbase (se 6 (by rfl) ⟨59142, by rfl⟩ : syracuseStep 2523413 = 118285) (by norm_num)
theorem B3604757 : Blo 996598 3604757 := bbase (se 6 (by rfl) ⟨84486, by rfl⟩ : syracuseStep 3604757 = 168973) (by norm_num)
theorem B2130293 : Blo 996598 2130293 := bbase (se 5 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 2130293 = 199715) (by norm_num)
theorem B1081817 : Blo 996598 1081817 := bbase (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) (by norm_num)
theorem B3375701 : Blo 996598 3375701 := bbase (se 8 (by rfl) ⟨19779, by rfl⟩ : syracuseStep 3375701 = 39559) (by norm_num)
theorem B3605093 : Blo 996598 3605093 := bbase (se 4 (by rfl) ⟨337977, by rfl⟩ : syracuseStep 3605093 = 675955) (by norm_num)
theorem B2523757 : Blo 996598 2523757 := bbase (se 3 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 2523757 = 946409) (by norm_num)
theorem B2523869 : Blo 996598 2523869 := bbase (se 3 (by rfl) ⟨473225, by rfl⟩ : syracuseStep 2523869 = 946451) (by norm_num)
theorem B5047109 : Blo 996598 5047109 := bbase (se 4 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 5047109 = 946333) (by norm_num)
theorem B17302421 : Blo 996598 17302421 := bbase (se 6 (by rfl) ⟨405525, by rfl⟩ : syracuseStep 17302421 = 811051) (by norm_num)
theorem B2524061 : Blo 996598 2524061 := bbase (se 3 (by rfl) ⟨473261, by rfl⟩ : syracuseStep 2524061 = 946523) (by norm_num)
theorem B7570421 : Blo 996598 7570421 := bbase (se 5 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 7570421 = 709727) (by norm_num)
theorem B3376133 : Blo 996598 3376133 := bbase (se 4 (by rfl) ⟨316512, by rfl⟩ : syracuseStep 3376133 = 633025) (by norm_num)
theorem B5407829 : Blo 996598 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B2884805 : Blo 996598 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B2131181 : Blo 996598 2131181 := bbase (se 3 (by rfl) ⟨399596, by rfl⟩ : syracuseStep 2131181 = 799193) (by norm_num)
theorem B2524405 : Blo 996598 2524405 := bbase (se 5 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 2524405 = 236663) (by norm_num)
theorem B2524517 : Blo 996598 2524517 := bbase (se 4 (by rfl) ⟨236673, by rfl⟩ : syracuseStep 2524517 = 473347) (by norm_num)
theorem B1213849 : Blo 996598 1213849 := bbase (se 2 (by rfl) ⟨455193, by rfl⟩ : syracuseStep 1213849 = 910387) (by norm_num)
theorem B3376565 : Blo 996598 3376565 := bbase (se 5 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 3376565 = 316553) (by norm_num)
theorem B2131429 : Blo 996598 2131429 := bbase (se 4 (by rfl) ⟨199821, by rfl⟩ : syracuseStep 2131429 = 399643) (by norm_num)
theorem B2524709 : Blo 996598 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B1279645 : Blo 996598 1279645 := bbase (se 3 (by rfl) ⟨239933, by rfl⟩ : syracuseStep 1279645 = 479867) (by norm_num)
theorem B1083065 : Blo 996598 1083065 := bbase (se 2 (by rfl) ⟨406149, by rfl⟩ : syracuseStep 1083065 = 812299) (by norm_num)
theorem B3376997 : Blo 996598 3376997 := bbase (se 4 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 3376997 = 633187) (by norm_num)
theorem B2525053 : Blo 996598 2525053 := bbase (se 3 (by rfl) ⟨473447, by rfl⟩ : syracuseStep 2525053 = 946895) (by norm_num)
theorem B2131933 : Blo 996598 2131933 := bbase (se 3 (by rfl) ⟨399737, by rfl⟩ : syracuseStep 2131933 = 799475) (by norm_num)
theorem B2525165 : Blo 996598 2525165 := bbase (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) (by norm_num)
theorem B1443901 : Blo 996598 1443901 := bbase (se 3 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 1443901 = 541463) (by norm_num)
theorem B5048405 : Blo 996598 5048405 := bbase (se 8 (by rfl) ⟨29580, by rfl⟩ : syracuseStep 5048405 = 59161) (by norm_num)
theorem B4262053 : Blo 996598 4262053 := bbase (se 4 (by rfl) ⟨399567, by rfl⟩ : syracuseStep 4262053 = 799135) (by norm_num)
theorem B2525357 : Blo 996598 2525357 := bbase (se 3 (by rfl) ⟨473504, by rfl⟩ : syracuseStep 2525357 = 947009) (by norm_num)
theorem B1706309 : Blo 996598 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B2525701 : Blo 996598 2525701 := bbase (se 4 (by rfl) ⟨236784, by rfl⟩ : syracuseStep 2525701 = 473569) (by norm_num)
theorem B2394677 : Blo 996598 2394677 := bbase (se 5 (by rfl) ⟨112250, by rfl⟩ : syracuseStep 2394677 = 224501) (by norm_num)
theorem B2525813 : Blo 996598 2525813 := bbase (se 5 (by rfl) ⟨118397, by rfl⟩ : syracuseStep 2525813 = 236795) (by norm_num)
theorem B2526005 : Blo 996598 2526005 := bbase (se 5 (by rfl) ⟨118406, by rfl⟩ : syracuseStep 2526005 = 236813) (by norm_num)
theorem B2132821 : Blo 996598 2132821 := bbase (se 9 (by rfl) ⟨6248, by rfl⟩ : syracuseStep 2132821 = 12497) (by norm_num)
theorem B2395253 : Blo 996598 2395253 := bbase (se 5 (by rfl) ⟨112277, by rfl⟩ : syracuseStep 2395253 = 224555) (by norm_num)
theorem B2526349 : Blo 996598 2526349 := bbase (se 3 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 2526349 = 947381) (by norm_num)
theorem B2526461 : Blo 996598 2526461 := bbase (se 3 (by rfl) ⟨473711, by rfl⟩ : syracuseStep 2526461 = 947423) (by norm_num)
theorem B2133317 : Blo 996598 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B5049701 : Blo 996598 5049701 := bbase (se 4 (by rfl) ⟨473409, by rfl⟩ : syracuseStep 5049701 = 946819) (by norm_num)
theorem B2526653 : Blo 996598 2526653 := bbase (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) (by norm_num)
theorem B2395637 : Blo 996598 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B2526997 : Blo 996598 2526997 := bbase (se 6 (by rfl) ⟨59226, by rfl⟩ : syracuseStep 2526997 = 118453) (by norm_num)
theorem B2527109 : Blo 996598 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B2527301 : Blo 996598 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B1347773 : Blo 996598 1347773 := bbase (se 3 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 1347773 = 505415) (by norm_num)
theorem B2134205 : Blo 996598 2134205 := bbase (se 3 (by rfl) ⟨400163, by rfl⟩ : syracuseStep 2134205 = 800327) (by norm_num)
theorem B2134325 : Blo 996598 2134325 := bbase (se 5 (by rfl) ⟨100046, by rfl⟩ : syracuseStep 2134325 = 200093) (by norm_num)
theorem B2527645 : Blo 996598 2527645 := bbase (se 3 (by rfl) ⟨473933, by rfl⟩ : syracuseStep 2527645 = 947867) (by norm_num)
theorem B2200069 : Blo 996598 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B2527757 : Blo 996598 2527757 := bbase (se 3 (by rfl) ⟨473954, by rfl⟩ : syracuseStep 2527757 = 947909) (by norm_num)
theorem B5050997 : Blo 996598 5050997 := bbase (se 5 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 5050997 = 473531) (by norm_num)
theorem B1217173 : Blo 996598 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B2527949 : Blo 996598 2527949 := bbase (se 3 (by rfl) ⟨473990, by rfl⟩ : syracuseStep 2527949 = 947981) (by norm_num)
theorem B2134957 : Blo 996598 2134957 := bbase (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) (by norm_num)
theorem B2528293 : Blo 996598 2528293 := bbase (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) (by norm_num)
theorem B4265045 : Blo 996598 4265045 := bbase (se 8 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 4265045 = 49981) (by norm_num)
theorem B1709149 : Blo 996598 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B2528405 : Blo 996598 2528405 := bbase (se 6 (by rfl) ⟨59259, by rfl⟩ : syracuseStep 2528405 = 118519) (by norm_num)
theorem B2397397 : Blo 996598 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B2528597 : Blo 996598 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B4560229 : Blo 996598 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B4789621 : Blo 996598 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B1709429 : Blo 996598 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B1644197 : Blo 996598 1644197 := bbase (se 4 (by rfl) ⟨154143, by rfl⟩ : syracuseStep 1644197 = 308287) (by norm_num)
theorem B2528941 : Blo 996598 2528941 := bbase (se 3 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 2528941 = 948353) (by norm_num)
theorem B2529053 : Blo 996598 2529053 := bbase (se 3 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 2529053 = 948395) (by norm_num)
theorem B2135845 : Blo 996598 2135845 := bbase (se 4 (by rfl) ⟨200235, by rfl⟩ : syracuseStep 2135845 = 400471) (by norm_num)
theorem B3839845 : Blo 996598 3839845 := bbase (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) (by norm_num)
theorem B5052293 : Blo 996598 5052293 := bbase (se 4 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 5052293 = 947305) (by norm_num)
theorem B2135965 : Blo 996598 2135965 := bbase (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) (by norm_num)
theorem B2529245 : Blo 996598 2529245 := bbase (se 3 (by rfl) ⟨474233, by rfl⟩ : syracuseStep 2529245 = 948467) (by norm_num)
theorem B1710101 : Blo 996598 1710101 := bbase (se 6 (by rfl) ⟨40080, by rfl⟩ : syracuseStep 1710101 = 80161) (by norm_num)
theorem B4266053 : Blo 996598 4266053 := bbase (se 4 (by rfl) ⟨399942, by rfl⟩ : syracuseStep 4266053 = 799885) (by norm_num)
theorem B2562173 : Blo 996598 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B2136221 : Blo 996598 2136221 := bbase (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) (by norm_num)
theorem B2398405 : Blo 996598 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B2398501 : Blo 996598 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B2529589 : Blo 996598 2529589 := bbase (se 5 (by rfl) ⟨118574, by rfl⟩ : syracuseStep 2529589 = 237149) (by norm_num)
theorem B2529701 : Blo 996598 2529701 := bbase (se 4 (by rfl) ⟨237159, by rfl⟩ : syracuseStep 2529701 = 474319) (by norm_num)
theorem B8526293 : Blo 996598 8526293 := bbase (se 7 (by rfl) ⟨99917, by rfl⟩ : syracuseStep 8526293 = 199835) (by norm_num)
theorem B9607733 : Blo 996598 9607733 := bbase (se 5 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 9607733 = 900725) (by norm_num)
theorem B2529893 : Blo 996598 2529893 := bbase (se 4 (by rfl) ⟨237177, by rfl⟩ : syracuseStep 2529893 = 474355) (by norm_num)
theorem B6396565 : Blo 996598 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B2562749 : Blo 996598 2562749 := bbase (se 3 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 2562749 = 961031) (by norm_num)
theorem B2399021 : Blo 996598 2399021 := bbase (se 3 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 2399021 = 899633) (by norm_num)
theorem B2693957 : Blo 996598 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B1121197 : Blo 996598 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B2530237 : Blo 996598 2530237 := bbase (se 3 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 2530237 = 948839) (by norm_num)
theorem B1121233 : Blo 996598 1121233 := bbase (se 2 (by rfl) ⟨420462, by rfl⟩ : syracuseStep 1121233 = 840925) (by norm_num)
theorem B1121269 : Blo 996598 1121269 := bbase (se 5 (by rfl) ⟨52559, by rfl⟩ : syracuseStep 1121269 = 105119) (by norm_num)
theorem B1121305 : Blo 996598 1121305 := bbase (se 2 (by rfl) ⟨420489, by rfl⟩ : syracuseStep 1121305 = 840979) (by norm_num)
theorem B2530349 : Blo 996598 2530349 := bbase (se 3 (by rfl) ⟨474440, by rfl⟩ : syracuseStep 2530349 = 948881) (by norm_num)
theorem B1121341 : Blo 996598 1121341 := bbase (se 3 (by rfl) ⟨210251, by rfl⟩ : syracuseStep 1121341 = 420503) (by norm_num)
theorem B1711181 : Blo 996598 1711181 := bbase (se 3 (by rfl) ⟨320846, by rfl⟩ : syracuseStep 1711181 = 641693) (by norm_num)
theorem B1121377 : Blo 996598 1121377 := bbase (se 2 (by rfl) ⟨420516, by rfl⟩ : syracuseStep 1121377 = 841033) (by norm_num)
theorem B1121413 : Blo 996598 1121413 := bbase (se 4 (by rfl) ⟨105132, by rfl⟩ : syracuseStep 1121413 = 210265) (by norm_num)
theorem B5053589 : Blo 996598 5053589 := bbase (se 6 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 5053589 = 236887) (by norm_num)
theorem B1121449 : Blo 996598 1121449 := bbase (se 2 (by rfl) ⟨420543, by rfl⟩ : syracuseStep 1121449 = 841087) (by norm_num)
theorem B1121485 : Blo 996598 1121485 := bbase (se 3 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 1121485 = 420557) (by norm_num)
theorem B2530541 : Blo 996598 2530541 := bbase (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) (by norm_num)
theorem B1121521 : Blo 996598 1121521 := bbase (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) (by norm_num)
theorem B1121557 : Blo 996598 1121557 := bbase (se 6 (by rfl) ⟨26286, by rfl⟩ : syracuseStep 1121557 = 52573) (by norm_num)
theorem B1121593 : Blo 996598 1121593 := bbase (se 2 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 1121593 = 841195) (by norm_num)
theorem B2399549 : Blo 996598 2399549 := bbase (se 3 (by rfl) ⟨449915, by rfl⟩ : syracuseStep 2399549 = 899831) (by norm_num)
theorem B1121629 : Blo 996598 1121629 := bbase (se 3 (by rfl) ⟨210305, by rfl⟩ : syracuseStep 1121629 = 420611) (by norm_num)
theorem B1121665 : Blo 996598 1121665 := bbase (se 2 (by rfl) ⟨420624, by rfl⟩ : syracuseStep 1121665 = 841249) (by norm_num)
theorem B1121701 : Blo 996598 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B1121737 : Blo 996598 1121737 := bbase (se 2 (by rfl) ⟨420651, by rfl⟩ : syracuseStep 1121737 = 841303) (by norm_num)
theorem B1121773 : Blo 996598 1121773 := bbase (se 3 (by rfl) ⟨210332, by rfl⟩ : syracuseStep 1121773 = 420665) (by norm_num)
theorem B1121809 : Blo 996598 1121809 := bbase (se 2 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 1121809 = 841357) (by norm_num)
theorem B2563613 : Blo 996598 2563613 := bbase (se 3 (by rfl) ⟨480677, by rfl⟩ : syracuseStep 2563613 = 961355) (by norm_num)
theorem B2399789 : Blo 996598 2399789 := bbase (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) (by norm_num)
theorem B1121845 : Blo 996598 1121845 := bbase (se 5 (by rfl) ⟨52586, by rfl⟩ : syracuseStep 1121845 = 105173) (by norm_num)
theorem B2530885 : Blo 996598 2530885 := bbase (se 4 (by rfl) ⟨237270, by rfl⟩ : syracuseStep 2530885 = 474541) (by norm_num)
theorem B1121881 : Blo 996598 1121881 := bbase (se 2 (by rfl) ⟨420705, by rfl⟩ : syracuseStep 1121881 = 841411) (by norm_num)
theorem B1121917 : Blo 996598 1121917 := bbase (se 3 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 1121917 = 420719) (by norm_num)
theorem B1351309 : Blo 996598 1351309 := bbase (se 3 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 1351309 = 506741) (by norm_num)
theorem B1121953 : Blo 996598 1121953 := bbase (se 2 (by rfl) ⟨420732, by rfl⟩ : syracuseStep 1121953 = 841465) (by norm_num)
theorem B2530997 : Blo 996598 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1121989 : Blo 996598 1121989 := bbase (se 4 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 1121989 = 210373) (by norm_num)
theorem B1122025 : Blo 996598 1122025 := bbase (se 2 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 1122025 = 841519) (by norm_num)
theorem B1122061 : Blo 996598 1122061 := bbase (se 3 (by rfl) ⟨210386, by rfl⟩ : syracuseStep 1122061 = 420773) (by norm_num)
theorem B1154837 : Blo 996598 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B1122097 : Blo 996598 1122097 := bbase (se 2 (by rfl) ⟨420786, by rfl⟩ : syracuseStep 1122097 = 841573) (by norm_num)
theorem B4267829 : Blo 996598 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B1122133 : Blo 996598 1122133 := bbase (se 9 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 1122133 = 6575) (by norm_num)
theorem B2531189 : Blo 996598 2531189 := bbase (se 5 (by rfl) ⟨118649, by rfl⟩ : syracuseStep 2531189 = 237299) (by norm_num)
theorem B1122169 : Blo 996598 1122169 := bbase (se 2 (by rfl) ⟨420813, by rfl⟩ : syracuseStep 1122169 = 841627) (by norm_num)
theorem B1122205 : Blo 996598 1122205 := bbase (se 3 (by rfl) ⟨210413, by rfl⟩ : syracuseStep 1122205 = 420827) (by norm_num)
theorem B1122241 : Blo 996598 1122241 := bbase (se 2 (by rfl) ⟨420840, by rfl⟩ : syracuseStep 1122241 = 841681) (by norm_num)
theorem B1122277 : Blo 996598 1122277 := bbase (se 4 (by rfl) ⟨105213, by rfl⟩ : syracuseStep 1122277 = 210427) (by norm_num)
theorem B1122313 : Blo 996598 1122313 := bbase (se 2 (by rfl) ⟨420867, by rfl⟩ : syracuseStep 1122313 = 841735) (by norm_num)
theorem B1122349 : Blo 996598 1122349 := bbase (se 3 (by rfl) ⟨210440, by rfl⟩ : syracuseStep 1122349 = 420881) (by norm_num)
theorem B1122385 : Blo 996598 1122385 := bbase (se 2 (by rfl) ⟨420894, by rfl⟩ : syracuseStep 1122385 = 841789) (by norm_num)
theorem B1122421 : Blo 996598 1122421 := bbase (se 5 (by rfl) ⟨52613, by rfl⟩ : syracuseStep 1122421 = 105227) (by norm_num)
theorem B16425109 : Blo 996598 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B17080469 : Blo 996598 17080469 := bbase (se 6 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 17080469 = 800647) (by norm_num)
theorem B1024153 : Blo 996598 1024153 := bbase (se 2 (by rfl) ⟨384057, by rfl⟩ : syracuseStep 1024153 = 768115) (by norm_num)
theorem B1122457 : Blo 996598 1122457 := bbase (se 2 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 1122457 = 841843) (by norm_num)
theorem B1122493 : Blo 996598 1122493 := bbase (se 3 (by rfl) ⟨210467, by rfl⟩ : syracuseStep 1122493 = 420935) (by norm_num)
theorem B2531533 : Blo 996598 2531533 := bbase (se 3 (by rfl) ⟨474662, by rfl⟩ : syracuseStep 2531533 = 949325) (by norm_num)
theorem B1122529 : Blo 996598 1122529 := bbase (se 2 (by rfl) ⟨420948, by rfl⟩ : syracuseStep 1122529 = 841897) (by norm_num)
theorem B1122565 : Blo 996598 1122565 := bbase (se 4 (by rfl) ⟨105240, by rfl⟩ : syracuseStep 1122565 = 210481) (by norm_num)
theorem B1122601 : Blo 996598 1122601 := bbase (se 2 (by rfl) ⟨420975, by rfl⟩ : syracuseStep 1122601 = 841951) (by norm_num)
theorem B2531645 : Blo 996598 2531645 := bbase (se 3 (by rfl) ⟨474683, by rfl⟩ : syracuseStep 2531645 = 949367) (by norm_num)
theorem B1122637 : Blo 996598 1122637 := bbase (se 3 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 1122637 = 420989) (by norm_num)
theorem B1122673 : Blo 996598 1122673 := bbase (se 2 (by rfl) ⟨421002, by rfl⟩ : syracuseStep 1122673 = 842005) (by norm_num)
theorem B1122709 : Blo 996598 1122709 := bbase (se 6 (by rfl) ⟨26313, by rfl⟩ : syracuseStep 1122709 = 52627) (by norm_num)
theorem B5054885 : Blo 996598 5054885 := bbase (se 4 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 5054885 = 947791) (by norm_num)
theorem B1122745 : Blo 996598 1122745 := bbase (se 2 (by rfl) ⟨421029, by rfl⟩ : syracuseStep 1122745 = 842059) (by norm_num)
theorem B1122781 : Blo 996598 1122781 := bbase (se 3 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 1122781 = 421043) (by norm_num)
theorem B2531837 : Blo 996598 2531837 := bbase (se 3 (by rfl) ⟨474719, by rfl⟩ : syracuseStep 2531837 = 949439) (by norm_num)
theorem B1122817 : Blo 996598 1122817 := bbase (se 2 (by rfl) ⟨421056, by rfl⟩ : syracuseStep 1122817 = 842113) (by norm_num)
theorem B1122853 : Blo 996598 1122853 := bbase (se 4 (by rfl) ⟨105267, by rfl⟩ : syracuseStep 1122853 = 210535) (by norm_num)
theorem B1122889 : Blo 996598 1122889 := bbase (se 2 (by rfl) ⟨421083, by rfl⟩ : syracuseStep 1122889 = 842167) (by norm_num)
theorem B7578197 : Blo 996598 7578197 := bbase (se 8 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 7578197 = 88807) (by norm_num)
theorem B1122925 : Blo 996598 1122925 := bbase (se 3 (by rfl) ⟨210548, by rfl⟩ : syracuseStep 1122925 = 421097) (by norm_num)
theorem B1122961 : Blo 996598 1122961 := bbase (se 2 (by rfl) ⟨421110, by rfl⟩ : syracuseStep 1122961 = 842221) (by norm_num)
theorem B1122997 : Blo 996598 1122997 := bbase (se 5 (by rfl) ⟨52640, by rfl⟩ : syracuseStep 1122997 = 105281) (by norm_num)
theorem B1123033 : Blo 996598 1123033 := bbase (se 2 (by rfl) ⟨421137, by rfl⟩ : syracuseStep 1123033 = 842275) (by norm_num)
theorem B1123069 : Blo 996598 1123069 := bbase (se 3 (by rfl) ⟨210575, by rfl⟩ : syracuseStep 1123069 = 421151) (by norm_num)
theorem B2564885 : Blo 996598 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B1123105 : Blo 996598 1123105 := bbase (se 2 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 1123105 = 842329) (by norm_num)
theorem B5481269 : Blo 996598 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B1123141 : Blo 996598 1123141 := bbase (se 4 (by rfl) ⟨105294, by rfl⟩ : syracuseStep 1123141 = 210589) (by norm_num)
theorem B2532181 : Blo 996598 2532181 := bbase (se 9 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 2532181 = 14837) (by norm_num)
theorem B1123177 : Blo 996598 1123177 := bbase (se 2 (by rfl) ⟨421191, by rfl⟩ : syracuseStep 1123177 = 842383) (by norm_num)
theorem B1123213 : Blo 996598 1123213 := bbase (se 3 (by rfl) ⟨210602, by rfl⟩ : syracuseStep 1123213 = 421205) (by norm_num)
theorem B1123249 : Blo 996598 1123249 := bbase (se 2 (by rfl) ⟨421218, by rfl⟩ : syracuseStep 1123249 = 842437) (by norm_num)
theorem B2532293 : Blo 996598 2532293 := bbase (se 4 (by rfl) ⟨237402, by rfl⟩ : syracuseStep 2532293 = 474805) (by norm_num)
theorem B1123285 : Blo 996598 1123285 := bbase (se 7 (by rfl) ⟨13163, by rfl⟩ : syracuseStep 1123285 = 26327) (by norm_num)
theorem B1123321 : Blo 996598 1123321 := bbase (se 2 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 1123321 = 842491) (by norm_num)
theorem B1123357 : Blo 996598 1123357 := bbase (se 3 (by rfl) ⟨210629, by rfl⟩ : syracuseStep 1123357 = 421259) (by norm_num)
theorem B1123393 : Blo 996598 1123393 := bbase (se 2 (by rfl) ⟨421272, by rfl⟩ : syracuseStep 1123393 = 842545) (by norm_num)
theorem B1123429 : Blo 996598 1123429 := bbase (se 4 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 1123429 = 210643) (by norm_num)
theorem B2532485 : Blo 996598 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B1123465 : Blo 996598 1123465 := bbase (se 2 (by rfl) ⟨421299, by rfl⟩ : syracuseStep 1123465 = 842599) (by norm_num)
theorem B1123501 : Blo 996598 1123501 := bbase (se 3 (by rfl) ⟨210656, by rfl⟩ : syracuseStep 1123501 = 421313) (by norm_num)
theorem B1123537 : Blo 996598 1123537 := bbase (se 2 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 1123537 = 842653) (by norm_num)
theorem B2401501 : Blo 996598 2401501 := bbase (se 3 (by rfl) ⟨450281, by rfl⟩ : syracuseStep 2401501 = 900563) (by norm_num)
theorem B1123573 : Blo 996598 1123573 := bbase (se 5 (by rfl) ⟨52667, by rfl⟩ : syracuseStep 1123573 = 105335) (by norm_num)
theorem B1123609 : Blo 996598 1123609 := bbase (se 2 (by rfl) ⟨421353, by rfl⟩ : syracuseStep 1123609 = 842707) (by norm_num)
theorem B1123645 : Blo 996598 1123645 := bbase (se 3 (by rfl) ⟨210683, by rfl⟩ : syracuseStep 1123645 = 421367) (by norm_num)
theorem B1123681 : Blo 996598 1123681 := bbase (se 2 (by rfl) ⟨421380, by rfl⟩ : syracuseStep 1123681 = 842761) (by norm_num)
theorem B1516909 : Blo 996598 1516909 := bbase (se 3 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 1516909 = 568841) (by norm_num)
theorem B1123717 : Blo 996598 1123717 := bbase (se 4 (by rfl) ⟨105348, by rfl⟩ : syracuseStep 1123717 = 210697) (by norm_num)
theorem B1123753 : Blo 996598 1123753 := bbase (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) (by norm_num)
theorem B1123789 : Blo 996598 1123789 := bbase (se 3 (by rfl) ⟨210710, by rfl⟩ : syracuseStep 1123789 = 421421) (by norm_num)
theorem B4793813 : Blo 996598 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B1123825 : Blo 996598 1123825 := bbase (se 2 (by rfl) ⟨421434, by rfl⟩ : syracuseStep 1123825 = 842869) (by norm_num)
theorem B1123861 : Blo 996598 1123861 := bbase (se 6 (by rfl) ⟨26340, by rfl⟩ : syracuseStep 1123861 = 52681) (by norm_num)
theorem B1123897 : Blo 996598 1123897 := bbase (se 2 (by rfl) ⟨421461, by rfl⟩ : syracuseStep 1123897 = 842923) (by norm_num)
theorem B1123933 : Blo 996598 1123933 := bbase (se 3 (by rfl) ⟨210737, by rfl⟩ : syracuseStep 1123933 = 421475) (by norm_num)
theorem B1123969 : Blo 996598 1123969 := bbase (se 2 (by rfl) ⟨421488, by rfl⟩ : syracuseStep 1123969 = 842977) (by norm_num)
theorem B1124005 : Blo 996598 1124005 := bbase (se 4 (by rfl) ⟨105375, by rfl⟩ : syracuseStep 1124005 = 210751) (by norm_num)
theorem B5056181 : Blo 996598 5056181 := bbase (se 5 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 5056181 = 474017) (by norm_num)
theorem B1124041 : Blo 996598 1124041 := bbase (se 2 (by rfl) ⟨421515, by rfl⟩ : syracuseStep 1124041 = 843031) (by norm_num)
theorem B1124077 : Blo 996598 1124077 := bbase (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) (by norm_num)
theorem B1124113 : Blo 996598 1124113 := bbase (se 2 (by rfl) ⟨421542, by rfl⟩ : syracuseStep 1124113 = 843085) (by norm_num)
theorem B1124149 : Blo 996598 1124149 := bbase (se 5 (by rfl) ⟨52694, by rfl⟩ : syracuseStep 1124149 = 105389) (by norm_num)
theorem B2565949 : Blo 996598 2565949 := bbase (se 3 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 2565949 = 962231) (by norm_num)
theorem B1124185 : Blo 996598 1124185 := bbase (se 2 (by rfl) ⟨421569, by rfl⟩ : syracuseStep 1124185 = 843139) (by norm_num)
theorem B1124221 : Blo 996598 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B1124257 : Blo 996598 1124257 := bbase (se 2 (by rfl) ⟨421596, by rfl⟩ : syracuseStep 1124257 = 843193) (by norm_num)
theorem B1124293 : Blo 996598 1124293 := bbase (se 4 (by rfl) ⟨105402, by rfl⟩ : syracuseStep 1124293 = 210805) (by norm_num)
theorem B1419221 : Blo 996598 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B4106213 : Blo 996598 4106213 := bbase (se 4 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 4106213 = 769915) (by norm_num)
theorem B3123173 : Blo 996598 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B1124329 : Blo 996598 1124329 := bbase (se 2 (by rfl) ⟨421623, by rfl⟩ : syracuseStep 1124329 = 843247) (by norm_num)
theorem B1124365 : Blo 996598 1124365 := bbase (se 3 (by rfl) ⟨210818, by rfl⟩ : syracuseStep 1124365 = 421637) (by norm_num)
theorem B1124401 : Blo 996598 1124401 := bbase (se 2 (by rfl) ⟨421650, by rfl⟩ : syracuseStep 1124401 = 843301) (by norm_num)
theorem B1124437 : Blo 996598 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B1124473 : Blo 996598 1124473 := bbase (se 2 (by rfl) ⟨421677, by rfl⟩ : syracuseStep 1124473 = 843355) (by norm_num)
theorem B1124509 : Blo 996598 1124509 := bbase (se 3 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 1124509 = 421691) (by norm_num)
theorem B1124545 : Blo 996598 1124545 := bbase (se 2 (by rfl) ⟨421704, by rfl⟩ : syracuseStep 1124545 = 843409) (by norm_num)
theorem B1124581 : Blo 996598 1124581 := bbase (se 4 (by rfl) ⟨105429, by rfl⟩ : syracuseStep 1124581 = 210859) (by norm_num)
theorem B1124617 : Blo 996598 1124617 := bbase (se 2 (by rfl) ⟨421731, by rfl⟩ : syracuseStep 1124617 = 843463) (by norm_num)
theorem B1124653 : Blo 996598 1124653 := bbase (se 3 (by rfl) ⟨210872, by rfl⟩ : syracuseStep 1124653 = 421745) (by norm_num)
theorem B1124689 : Blo 996598 1124689 := bbase (se 2 (by rfl) ⟨421758, by rfl⟩ : syracuseStep 1124689 = 843517) (by norm_num)
theorem B1026389 : Blo 996598 1026389 := bbase (se 10 (by rfl) ⟨1503, by rfl⟩ : syracuseStep 1026389 = 3007) (by norm_num)
theorem B1124725 : Blo 996598 1124725 := bbase (se 5 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 1124725 = 105443) (by norm_num)
theorem B1681789 : Blo 996598 1681789 := bbase (se 3 (by rfl) ⟨315335, by rfl⟩ : syracuseStep 1681789 = 630671) (by norm_num)
theorem B1124761 : Blo 996598 1124761 := bbase (se 2 (by rfl) ⟨421785, by rfl⟩ : syracuseStep 1124761 = 843571) (by norm_num)
theorem B1124797 : Blo 996598 1124797 := bbase (se 3 (by rfl) ⟨210899, by rfl⟩ : syracuseStep 1124797 = 421799) (by norm_num)
theorem B1518029 : Blo 996598 1518029 := bbase (se 3 (by rfl) ⟨284630, by rfl⟩ : syracuseStep 1518029 = 569261) (by norm_num)
theorem B1681877 : Blo 996598 1681877 := bbase (se 7 (by rfl) ⟨19709, by rfl⟩ : syracuseStep 1681877 = 39419) (by norm_num)
theorem B1124833 : Blo 996598 1124833 := bbase (se 2 (by rfl) ⟨421812, by rfl⟩ : syracuseStep 1124833 = 843625) (by norm_num)
theorem B1419773 : Blo 996598 1419773 := bbase (se 3 (by rfl) ⟨266207, by rfl⟩ : syracuseStep 1419773 = 532415) (by norm_num)
theorem B1518077 : Blo 996598 1518077 := bbase (se 3 (by rfl) ⟨284639, by rfl⟩ : syracuseStep 1518077 = 569279) (by norm_num)
theorem B1124869 : Blo 996598 1124869 := bbase (se 4 (by rfl) ⟨105456, by rfl⟩ : syracuseStep 1124869 = 210913) (by norm_num)
theorem B1124905 : Blo 996598 1124905 := bbase (se 2 (by rfl) ⟨421839, by rfl⟩ : syracuseStep 1124905 = 843679) (by norm_num)
theorem B6400565 : Blo 996598 6400565 := bbase (se 5 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 6400565 = 600053) (by norm_num)
theorem B1124941 : Blo 996598 1124941 := bbase (se 3 (by rfl) ⟨210926, by rfl⟩ : syracuseStep 1124941 = 421853) (by norm_num)
theorem B1682005 : Blo 996598 1682005 := bbase (se 8 (by rfl) ⟨9855, by rfl⟩ : syracuseStep 1682005 = 19711) (by norm_num)
theorem B1124977 : Blo 996598 1124977 := bbase (se 2 (by rfl) ⟨421866, by rfl⟩ : syracuseStep 1124977 = 843733) (by norm_num)
theorem B2402941 : Blo 996598 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B2468501 : Blo 996598 2468501 := bbase (se 6 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 2468501 = 115711) (by norm_num)
theorem B1125013 : Blo 996598 1125013 := bbase (se 6 (by rfl) ⟨26367, by rfl⟩ : syracuseStep 1125013 = 52735) (by norm_num)
theorem B1682093 : Blo 996598 1682093 := bbase (se 3 (by rfl) ⟨315392, by rfl⟩ : syracuseStep 1682093 = 630785) (by norm_num)
theorem B1125049 : Blo 996598 1125049 := bbase (se 2 (by rfl) ⟨421893, by rfl⟩ : syracuseStep 1125049 = 843787) (by norm_num)
theorem B1125085 : Blo 996598 1125085 := bbase (se 3 (by rfl) ⟨210953, by rfl⟩ : syracuseStep 1125085 = 421907) (by norm_num)
theorem B1125121 : Blo 996598 1125121 := bbase (se 2 (by rfl) ⟨421920, by rfl⟩ : syracuseStep 1125121 = 843841) (by norm_num)
theorem B1125157 : Blo 996598 1125157 := bbase (se 4 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 1125157 = 210967) (by norm_num)
theorem B1682221 : Blo 996598 1682221 := bbase (se 3 (by rfl) ⟨315416, by rfl⟩ : syracuseStep 1682221 = 630833) (by norm_num)
theorem B1125193 : Blo 996598 1125193 := bbase (se 2 (by rfl) ⟨421947, by rfl⟩ : syracuseStep 1125193 = 843895) (by norm_num)
theorem B1125229 : Blo 996598 1125229 := bbase (se 3 (by rfl) ⟨210980, by rfl⟩ : syracuseStep 1125229 = 421961) (by norm_num)
theorem B1682309 : Blo 996598 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B1125265 : Blo 996598 1125265 := bbase (se 2 (by rfl) ⟨421974, by rfl⟩ : syracuseStep 1125265 = 843949) (by norm_num)
theorem B1125301 : Blo 996598 1125301 := bbase (se 5 (by rfl) ⟨52748, by rfl⟩ : syracuseStep 1125301 = 105497) (by norm_num)
theorem B5057477 : Blo 996598 5057477 := bbase (se 4 (by rfl) ⟨474138, by rfl⟩ : syracuseStep 5057477 = 948277) (by norm_num)
theorem B1125337 : Blo 996598 1125337 := bbase (se 2 (by rfl) ⟨422001, by rfl⟩ : syracuseStep 1125337 = 844003) (by norm_num)
theorem B1518581 : Blo 996598 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B1125373 : Blo 996598 1125373 := bbase (se 3 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 1125373 = 422015) (by norm_num)
theorem B1682437 : Blo 996598 1682437 := bbase (se 4 (by rfl) ⟨157728, by rfl⟩ : syracuseStep 1682437 = 315457) (by norm_num)
theorem B1125409 : Blo 996598 1125409 := bbase (se 2 (by rfl) ⟨422028, by rfl⟩ : syracuseStep 1125409 = 844057) (by norm_num)
theorem B1125445 : Blo 996598 1125445 := bbase (se 4 (by rfl) ⟨105510, by rfl⟩ : syracuseStep 1125445 = 211021) (by norm_num)
theorem B1682525 : Blo 996598 1682525 := bbase (se 3 (by rfl) ⟨315473, by rfl⟩ : syracuseStep 1682525 = 630947) (by norm_num)
theorem B1125481 : Blo 996598 1125481 := bbase (se 2 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 1125481 = 844111) (by norm_num)
theorem B1125517 : Blo 996598 1125517 := bbase (se 3 (by rfl) ⟨211034, by rfl⟩ : syracuseStep 1125517 = 422069) (by norm_num)
theorem B5680277 : Blo 996598 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B1125553 : Blo 996598 1125553 := bbase (se 2 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 1125553 = 844165) (by norm_num)
theorem B1125589 : Blo 996598 1125589 := bbase (se 7 (by rfl) ⟨13190, by rfl⟩ : syracuseStep 1125589 = 26381) (by norm_num)
theorem B1682653 : Blo 996598 1682653 := bbase (se 3 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 1682653 = 630995) (by norm_num)
theorem B2403557 : Blo 996598 2403557 := bbase (se 4 (by rfl) ⟨225333, by rfl⟩ : syracuseStep 2403557 = 450667) (by norm_num)
theorem B1420525 : Blo 996598 1420525 := bbase (se 3 (by rfl) ⟨266348, by rfl⟩ : syracuseStep 1420525 = 532697) (by norm_num)
theorem B9612533 : Blo 996598 9612533 := bbase (se 5 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 9612533 = 901175) (by norm_num)
theorem B1125625 : Blo 996598 1125625 := bbase (se 2 (by rfl) ⟨422109, by rfl⟩ : syracuseStep 1125625 = 844219) (by norm_num)
theorem B1125661 : Blo 996598 1125661 := bbase (se 3 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 1125661 = 422123) (by norm_num)
theorem B1682741 : Blo 996598 1682741 := bbase (se 5 (by rfl) ⟨78878, by rfl⟩ : syracuseStep 1682741 = 157757) (by norm_num)
theorem B2403749 : Blo 996598 2403749 := bbase (se 4 (by rfl) ⟨225351, by rfl⟩ : syracuseStep 2403749 = 450703) (by norm_num)
theorem B1682869 : Blo 996598 1682869 := bbase (se 5 (by rfl) ⟨78884, by rfl⟩ : syracuseStep 1682869 = 157769) (by norm_num)
theorem B14396885 : Blo 996598 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B3419653 : Blo 996598 3419653 := bbase (se 4 (by rfl) ⟨320592, by rfl⟩ : syracuseStep 3419653 = 641185) (by norm_num)
theorem B1682957 : Blo 996598 1682957 := bbase (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) (by norm_num)
theorem B1683085 : Blo 996598 1683085 := bbase (se 3 (by rfl) ⟨315578, by rfl⟩ : syracuseStep 1683085 = 631157) (by norm_num)
theorem B2404037 : Blo 996598 2404037 := bbase (se 4 (by rfl) ⟨225378, by rfl⟩ : syracuseStep 2404037 = 450757) (by norm_num)
theorem B1683173 : Blo 996598 1683173 := bbase (se 4 (by rfl) ⟨157797, by rfl⟩ : syracuseStep 1683173 = 315595) (by norm_num)
theorem B1683301 : Blo 996598 1683301 := bbase (se 4 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 1683301 = 315619) (by norm_num)
theorem B1683389 : Blo 996598 1683389 := bbase (se 3 (by rfl) ⟨315635, by rfl⟩ : syracuseStep 1683389 = 631271) (by norm_num)
theorem B4272101 : Blo 996598 4272101 := bbase (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) (by norm_num)
theorem B1421317 : Blo 996598 1421317 := bbase (se 4 (by rfl) ⟨133248, by rfl⟩ : syracuseStep 1421317 = 266497) (by norm_num)
theorem B1683517 : Blo 996598 1683517 := bbase (se 3 (by rfl) ⟨315659, by rfl⟩ : syracuseStep 1683517 = 631319) (by norm_num)
theorem B4796501 : Blo 996598 4796501 := bbase (se 8 (by rfl) ⟨28104, by rfl⟩ : syracuseStep 4796501 = 56209) (by norm_num)
theorem B1683605 : Blo 996598 1683605 := bbase (se 6 (by rfl) ⟨39459, by rfl⟩ : syracuseStep 1683605 = 78919) (by norm_num)
theorem B5058773 : Blo 996598 5058773 := bbase (se 7 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 5058773 = 118565) (by norm_num)
theorem B1683733 : Blo 996598 1683733 := bbase (se 6 (by rfl) ⟨39462, by rfl⟩ : syracuseStep 1683733 = 78925) (by norm_num)
theorem B5681461 : Blo 996598 5681461 := bbase (se 5 (by rfl) ⟨266318, by rfl⟩ : syracuseStep 5681461 = 532637) (by norm_num)
theorem B1421653 : Blo 996598 1421653 := bbase (se 10 (by rfl) ⟨2082, by rfl⟩ : syracuseStep 1421653 = 4165) (by norm_num)
theorem B1683821 : Blo 996598 1683821 := bbase (se 3 (by rfl) ⟨315716, by rfl⟩ : syracuseStep 1683821 = 631433) (by norm_num)
theorem B1683949 : Blo 996598 1683949 := bbase (se 3 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 1683949 = 631481) (by norm_num)
theorem B1421869 : Blo 996598 1421869 := bbase (se 3 (by rfl) ⟨266600, by rfl⟩ : syracuseStep 1421869 = 533201) (by norm_num)
theorem B1684037 : Blo 996598 1684037 := bbase (se 4 (by rfl) ⟨157878, by rfl⟩ : syracuseStep 1684037 = 315757) (by norm_num)
theorem B1684165 : Blo 996598 1684165 := bbase (se 4 (by rfl) ⟨157890, by rfl⟩ : syracuseStep 1684165 = 315781) (by norm_num)
theorem B1684253 : Blo 996598 1684253 := bbase (se 3 (by rfl) ⟨315797, by rfl⟩ : syracuseStep 1684253 = 631595) (by norm_num)
theorem B1684381 : Blo 996598 1684381 := bbase (se 3 (by rfl) ⟨315821, by rfl⟩ : syracuseStep 1684381 = 631643) (by norm_num)
theorem B1422245 : Blo 996598 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B1684469 : Blo 996598 1684469 := bbase (se 5 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 1684469 = 157919) (by norm_num)
theorem B1684597 : Blo 996598 1684597 := bbase (se 5 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 1684597 = 157931) (by norm_num)
theorem B3552389 : Blo 996598 3552389 := bbase (se 4 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 3552389 = 666073) (by norm_num)
theorem B1684685 : Blo 996598 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B1684813 : Blo 996598 1684813 := bbase (se 3 (by rfl) ⟨315902, by rfl⟩ : syracuseStep 1684813 = 631805) (by norm_num)
theorem B1684901 : Blo 996598 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B5060069 : Blo 996598 5060069 := bbase (se 4 (by rfl) ⟨474381, by rfl⟩ : syracuseStep 5060069 = 948763) (by norm_num)
theorem B6829589 : Blo 996598 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B1685029 : Blo 996598 1685029 := bbase (se 4 (by rfl) ⟨157971, by rfl⟩ : syracuseStep 1685029 = 315943) (by norm_num)
theorem B1685117 : Blo 996598 1685117 := bbase (se 3 (by rfl) ⟨315959, by rfl⟩ : syracuseStep 1685117 = 631919) (by norm_num)
theorem B4863701 : Blo 996598 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B4273877 : Blo 996598 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B1685245 : Blo 996598 1685245 := bbase (se 3 (by rfl) ⟨315983, by rfl⟩ : syracuseStep 1685245 = 631967) (by norm_num)
theorem B2242349 : Blo 996598 2242349 := bbase (se 3 (by rfl) ⟨420440, by rfl⟩ : syracuseStep 2242349 = 840881) (by norm_num)
theorem B1685333 : Blo 996598 1685333 := bbase (se 9 (by rfl) ⟨4937, by rfl⟩ : syracuseStep 1685333 = 9875) (by norm_num)
theorem B2242421 : Blo 996598 2242421 := bbase (se 5 (by rfl) ⟨105113, by rfl⟩ : syracuseStep 2242421 = 210227) (by norm_num)
theorem B2242493 : Blo 996598 2242493 := bbase (se 3 (by rfl) ⟨420467, by rfl⟩ : syracuseStep 2242493 = 840935) (by norm_num)
theorem B1685461 : Blo 996598 1685461 := bbase (se 7 (by rfl) ⟨19751, by rfl⟩ : syracuseStep 1685461 = 39503) (by norm_num)
theorem B2242565 : Blo 996598 2242565 := bbase (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) (by norm_num)
theorem B1685549 : Blo 996598 1685549 := bbase (se 3 (by rfl) ⟨316040, by rfl⟩ : syracuseStep 1685549 = 632081) (by norm_num)
theorem B2242637 : Blo 996598 2242637 := bbase (se 3 (by rfl) ⟨420494, by rfl⟩ : syracuseStep 2242637 = 840989) (by norm_num)
theorem B4110421 : Blo 996598 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B2275445 : Blo 996598 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B2242709 : Blo 996598 2242709 := bbase (se 6 (by rfl) ⟨52563, by rfl⟩ : syracuseStep 2242709 = 105127) (by norm_num)
theorem B1685677 : Blo 996598 1685677 := bbase (se 3 (by rfl) ⟨316064, by rfl⟩ : syracuseStep 1685677 = 632129) (by norm_num)
theorem B2242781 : Blo 996598 2242781 := bbase (se 3 (by rfl) ⟨420521, by rfl⟩ : syracuseStep 2242781 = 841043) (by norm_num)
theorem B5683445 : Blo 996598 5683445 := bbase (se 5 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 5683445 = 532823) (by norm_num)
theorem B1685765 : Blo 996598 1685765 := bbase (se 4 (by rfl) ⟨158040, by rfl⟩ : syracuseStep 1685765 = 316081) (by norm_num)
theorem B2242853 : Blo 996598 2242853 := bbase (se 4 (by rfl) ⟨210267, by rfl⟩ : syracuseStep 2242853 = 420535) (by norm_num)
theorem B1423669 : Blo 996598 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B3193157 : Blo 996598 3193157 := bbase (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) (by norm_num)
theorem B2242925 : Blo 996598 2242925 := bbase (se 3 (by rfl) ⟨420548, by rfl⟩ : syracuseStep 2242925 = 841097) (by norm_num)
theorem B1685893 : Blo 996598 1685893 := bbase (se 4 (by rfl) ⟨158052, by rfl⟩ : syracuseStep 1685893 = 316105) (by norm_num)
theorem B2242997 : Blo 996598 2242997 := bbase (se 5 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 2242997 = 210281) (by norm_num)
theorem B3422677 : Blo 996598 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B1685981 : Blo 996598 1685981 := bbase (se 3 (by rfl) ⟨316121, by rfl⟩ : syracuseStep 1685981 = 632243) (by norm_num)
theorem B2243069 : Blo 996598 2243069 := bbase (se 3 (by rfl) ⟨420575, by rfl⟩ : syracuseStep 2243069 = 841151) (by norm_num)
theorem B2341405 : Blo 996598 2341405 := bbase (se 3 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 2341405 = 878027) (by norm_num)
theorem B2243141 : Blo 996598 2243141 := bbase (se 4 (by rfl) ⟨210294, by rfl⟩ : syracuseStep 2243141 = 420589) (by norm_num)
theorem B1686109 : Blo 996598 1686109 := bbase (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) (by norm_num)
theorem B2701925 : Blo 996598 2701925 := bbase (se 4 (by rfl) ⟨253305, by rfl⟩ : syracuseStep 2701925 = 506611) (by norm_num)
theorem B2243213 : Blo 996598 2243213 := bbase (se 3 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 2243213 = 841205) (by norm_num)
theorem B1686197 : Blo 996598 1686197 := bbase (se 5 (by rfl) ⟨79040, by rfl⟩ : syracuseStep 1686197 = 158081) (by norm_num)
theorem B2243285 : Blo 996598 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B5061365 : Blo 996598 5061365 := bbase (se 5 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 5061365 = 474503) (by norm_num)
theorem B2243357 : Blo 996598 2243357 := bbase (se 3 (by rfl) ⟨420629, by rfl⟩ : syracuseStep 2243357 = 841259) (by norm_num)
theorem B1686325 : Blo 996598 1686325 := bbase (se 5 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 1686325 = 158093) (by norm_num)
theorem B2243429 : Blo 996598 2243429 := bbase (se 4 (by rfl) ⟨210321, by rfl⟩ : syracuseStep 2243429 = 420643) (by norm_num)
theorem B1424261 : Blo 996598 1424261 := bbase (se 4 (by rfl) ⟨133524, by rfl⟩ : syracuseStep 1424261 = 267049) (by norm_num)
theorem B1686413 : Blo 996598 1686413 := bbase (se 3 (by rfl) ⟨316202, by rfl⟩ : syracuseStep 1686413 = 632405) (by norm_num)
theorem B2243501 : Blo 996598 2243501 := bbase (se 3 (by rfl) ⟨420656, by rfl⟩ : syracuseStep 2243501 = 841313) (by norm_num)
theorem B2702261 : Blo 996598 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B1424341 : Blo 996598 1424341 := bbase (se 7 (by rfl) ⟨16691, by rfl⟩ : syracuseStep 1424341 = 33383) (by norm_num)
theorem B2243573 : Blo 996598 2243573 := bbase (se 5 (by rfl) ⟨105167, by rfl⟩ : syracuseStep 2243573 = 210335) (by norm_num)
theorem B1686541 : Blo 996598 1686541 := bbase (se 3 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 1686541 = 632453) (by norm_num)
theorem B2243645 : Blo 996598 2243645 := bbase (se 3 (by rfl) ⟨420683, by rfl⟩ : syracuseStep 2243645 = 841367) (by norm_num)
theorem B2276429 : Blo 996598 2276429 := bbase (se 3 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 2276429 = 853661) (by norm_num)
theorem B1424461 : Blo 996598 1424461 := bbase (se 3 (by rfl) ⟨267086, by rfl⟩ : syracuseStep 1424461 = 534173) (by norm_num)
theorem B1686629 : Blo 996598 1686629 := bbase (se 4 (by rfl) ⟨158121, by rfl⟩ : syracuseStep 1686629 = 316243) (by norm_num)
theorem B2243717 : Blo 996598 2243717 := bbase (se 4 (by rfl) ⟨210348, by rfl⟩ : syracuseStep 2243717 = 420697) (by norm_num)
theorem B1424557 : Blo 996598 1424557 := bbase (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) (by norm_num)
theorem B2243789 : Blo 996598 2243789 := bbase (se 3 (by rfl) ⟨420710, by rfl⟩ : syracuseStep 2243789 = 841421) (by norm_num)
theorem B1686757 : Blo 996598 1686757 := bbase (se 4 (by rfl) ⟨158133, by rfl⟩ : syracuseStep 1686757 = 316267) (by norm_num)
theorem B2243861 : Blo 996598 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B1686845 : Blo 996598 1686845 := bbase (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) (by norm_num)
theorem B2243933 : Blo 996598 2243933 := bbase (se 3 (by rfl) ⟨420737, by rfl⟩ : syracuseStep 2243933 = 841475) (by norm_num)
theorem B2244005 : Blo 996598 2244005 := bbase (se 4 (by rfl) ⟨210375, by rfl⟩ : syracuseStep 2244005 = 420751) (by norm_num)
theorem B3784117 : Blo 996598 3784117 := bbase (se 5 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 3784117 = 354761) (by norm_num)
theorem B1686973 : Blo 996598 1686973 := bbase (se 3 (by rfl) ⟨316307, by rfl⟩ : syracuseStep 1686973 = 632615) (by norm_num)
theorem B2244077 : Blo 996598 2244077 := bbase (se 3 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 2244077 = 841529) (by norm_num)
theorem B1687061 : Blo 996598 1687061 := bbase (se 6 (by rfl) ⟨39540, by rfl⟩ : syracuseStep 1687061 = 79081) (by norm_num)
theorem B1064497 : Blo 996598 1064497 := bbase (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) (by norm_num)
theorem B2244149 : Blo 996598 2244149 := bbase (se 5 (by rfl) ⟨105194, by rfl⟩ : syracuseStep 2244149 = 210389) (by norm_num)
theorem B2244221 : Blo 996598 2244221 := bbase (se 3 (by rfl) ⟨420791, by rfl⟩ : syracuseStep 2244221 = 841583) (by norm_num)
theorem B1687189 : Blo 996598 1687189 := bbase (se 6 (by rfl) ⟨39543, by rfl⟩ : syracuseStep 1687189 = 79087) (by norm_num)
theorem B1064621 : Blo 996598 1064621 := bbase (se 3 (by rfl) ⟨199616, by rfl⟩ : syracuseStep 1064621 = 399233) (by norm_num)
theorem B2244293 : Blo 996598 2244293 := bbase (se 4 (by rfl) ⟨210402, by rfl⟩ : syracuseStep 2244293 = 420805) (by norm_num)
theorem B3784421 : Blo 996598 3784421 := bbase (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) (by norm_num)
theorem B1687277 : Blo 996598 1687277 := bbase (se 3 (by rfl) ⟨316364, by rfl⟩ : syracuseStep 1687277 = 632729) (by norm_num)
theorem B4112117 : Blo 996598 4112117 := bbase (se 5 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 4112117 = 385511) (by norm_num)
theorem B2244365 : Blo 996598 2244365 := bbase (se 3 (by rfl) ⟨420818, by rfl⟩ : syracuseStep 2244365 = 841637) (by norm_num)
theorem B4046645 : Blo 996598 4046645 := bbase (se 5 (by rfl) ⟨189686, by rfl⟩ : syracuseStep 4046645 = 379373) (by norm_num)
theorem B2244437 : Blo 996598 2244437 := bbase (se 9 (by rfl) ⟨6575, by rfl⟩ : syracuseStep 2244437 = 13151) (by norm_num)
theorem B1687405 : Blo 996598 1687405 := bbase (se 3 (by rfl) ⟨316388, by rfl⟩ : syracuseStep 1687405 = 632777) (by norm_num)
theorem B1261433 : Blo 996598 1261433 := bbase (se 2 (by rfl) ⟨473037, by rfl⟩ : syracuseStep 1261433 = 946075) (by norm_num)
theorem B2244509 : Blo 996598 2244509 := bbase (se 3 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 2244509 = 841691) (by norm_num)
theorem B1064873 : Blo 996598 1064873 := bbase (se 2 (by rfl) ⟨399327, by rfl⟩ : syracuseStep 1064873 = 798655) (by norm_num)
theorem B1261489 : Blo 996598 1261489 := bbase (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) (by norm_num)
theorem B1687493 : Blo 996598 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B2244581 : Blo 996598 2244581 := bbase (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) (by norm_num)
theorem B5062661 : Blo 996598 5062661 := bbase (se 4 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 5062661 = 949249) (by norm_num)
theorem B1261585 : Blo 996598 1261585 := bbase (se 2 (by rfl) ⟨473094, by rfl⟩ : syracuseStep 1261585 = 946189) (by norm_num)
theorem B2244653 : Blo 996598 2244653 := bbase (se 3 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 2244653 = 841745) (by norm_num)
theorem B1687621 : Blo 996598 1687621 := bbase (se 4 (by rfl) ⟨158214, by rfl⟩ : syracuseStep 1687621 = 316429) (by norm_num)
theorem B2244725 : Blo 996598 2244725 := bbase (se 5 (by rfl) ⟨105221, by rfl⟩ : syracuseStep 2244725 = 210443) (by norm_num)
theorem B1687709 : Blo 996598 1687709 := bbase (se 3 (by rfl) ⟨316445, by rfl⟩ : syracuseStep 1687709 = 632891) (by norm_num)
theorem B7585973 : Blo 996598 7585973 := bbase (se 5 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 7585973 = 711185) (by norm_num)
theorem B1261757 : Blo 996598 1261757 := bbase (se 3 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 1261757 = 473159) (by norm_num)
theorem B2244797 : Blo 996598 2244797 := bbase (se 3 (by rfl) ⟨420899, by rfl⟩ : syracuseStep 2244797 = 841799) (by norm_num)
theorem B1261813 : Blo 996598 1261813 := bbase (se 5 (by rfl) ⟨59147, by rfl⟩ : syracuseStep 1261813 = 118295) (by norm_num)
theorem B1753349 : Blo 996598 1753349 := bbase (se 4 (by rfl) ⟨164376, by rfl⟩ : syracuseStep 1753349 = 328753) (by norm_num)
theorem B2244869 : Blo 996598 2244869 := bbase (se 4 (by rfl) ⟨210456, by rfl⟩ : syracuseStep 2244869 = 420913) (by norm_num)
theorem B1687837 : Blo 996598 1687837 := bbase (se 3 (by rfl) ⟨316469, by rfl⟩ : syracuseStep 1687837 = 632939) (by norm_num)
theorem B2244941 : Blo 996598 2244941 := bbase (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) (by norm_num)
theorem B1261909 : Blo 996598 1261909 := bbase (se 10 (by rfl) ⟨1848, by rfl⟩ : syracuseStep 1261909 = 3697) (by norm_num)
theorem B20496725 : Blo 996598 20496725 := bbase (se 10 (by rfl) ⟨30024, by rfl⟩ : syracuseStep 20496725 = 60049) (by norm_num)
theorem B1065317 : Blo 996598 1065317 := bbase (se 4 (by rfl) ⟨99873, by rfl⟩ : syracuseStep 1065317 = 199747) (by norm_num)
theorem B1687925 : Blo 996598 1687925 := bbase (se 5 (by rfl) ⟨79121, by rfl⟩ : syracuseStep 1687925 = 158243) (by norm_num)
theorem B2245013 : Blo 996598 2245013 := bbase (se 6 (by rfl) ⟨52617, by rfl⟩ : syracuseStep 2245013 = 105235) (by norm_num)
theorem B5685653 : Blo 996598 5685653 := bbase (se 6 (by rfl) ⟨133257, by rfl⟩ : syracuseStep 5685653 = 266515) (by norm_num)
theorem B6406613 : Blo 996598 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B2245085 : Blo 996598 2245085 := bbase (se 3 (by rfl) ⟨420953, by rfl⟩ : syracuseStep 2245085 = 841907) (by norm_num)
theorem B1688053 : Blo 996598 1688053 := bbase (se 5 (by rfl) ⟨79127, by rfl⟩ : syracuseStep 1688053 = 158255) (by norm_num)
theorem B1262081 : Blo 996598 1262081 := bbase (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) (by norm_num)
theorem B3195413 : Blo 996598 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B2245157 : Blo 996598 2245157 := bbase (se 4 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 2245157 = 420967) (by norm_num)
theorem B1262137 : Blo 996598 1262137 := bbase (se 2 (by rfl) ⟨473301, by rfl⟩ : syracuseStep 1262137 = 946603) (by norm_num)
theorem B1688141 : Blo 996598 1688141 := bbase (se 3 (by rfl) ⟨316526, by rfl⟩ : syracuseStep 1688141 = 633053) (by norm_num)
theorem B1065565 : Blo 996598 1065565 := bbase (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) (by norm_num)
theorem B2245229 : Blo 996598 2245229 := bbase (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) (by norm_num)
theorem B3195541 : Blo 996598 3195541 := bbase (se 6 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 3195541 = 149791) (by norm_num)
theorem B1262233 : Blo 996598 1262233 := bbase (se 2 (by rfl) ⟨473337, by rfl⟩ : syracuseStep 1262233 = 946675) (by norm_num)
theorem B2245301 : Blo 996598 2245301 := bbase (se 5 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 2245301 = 210497) (by norm_num)
theorem B1688269 : Blo 996598 1688269 := bbase (se 3 (by rfl) ⟨316550, by rfl⟩ : syracuseStep 1688269 = 633101) (by norm_num)
theorem B2245373 : Blo 996598 2245373 := bbase (se 3 (by rfl) ⟨421007, by rfl⟩ : syracuseStep 2245373 = 842015) (by norm_num)
theorem B1688357 : Blo 996598 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B1262405 : Blo 996598 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B2245445 : Blo 996598 2245445 := bbase (se 4 (by rfl) ⟨210510, by rfl⟩ : syracuseStep 2245445 = 421021) (by norm_num)
theorem B1262461 : Blo 996598 1262461 := bbase (se 3 (by rfl) ⟨236711, by rfl⟩ : syracuseStep 1262461 = 473423) (by norm_num)
theorem B2245517 : Blo 996598 2245517 := bbase (se 3 (by rfl) ⟨421034, by rfl⟩ : syracuseStep 2245517 = 842069) (by norm_num)
theorem B1688485 : Blo 996598 1688485 := bbase (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) (by norm_num)
theorem B2245589 : Blo 996598 2245589 := bbase (se 7 (by rfl) ⟨26315, by rfl⟩ : syracuseStep 2245589 = 52631) (by norm_num)
theorem B1262557 : Blo 996598 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1066009 : Blo 996598 1066009 := bbase (se 2 (by rfl) ⟨399753, by rfl⟩ : syracuseStep 1066009 = 799507) (by norm_num)
theorem B2245661 : Blo 996598 2245661 := bbase (se 3 (by rfl) ⟨421061, by rfl⟩ : syracuseStep 2245661 = 842123) (by norm_num)
theorem B3032101 : Blo 996598 3032101 := bbase (se 4 (by rfl) ⟨284259, by rfl⟩ : syracuseStep 3032101 = 568519) (by norm_num)
theorem B1066069 : Blo 996598 1066069 := bbase (se 8 (by rfl) ⟨6246, by rfl⟩ : syracuseStep 1066069 = 12493) (by norm_num)
theorem B2245733 : Blo 996598 2245733 := bbase (se 4 (by rfl) ⟨210537, by rfl⟩ : syracuseStep 2245733 = 421075) (by norm_num)
theorem B7193717 : Blo 996598 7193717 := bbase (se 5 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 7193717 = 674411) (by norm_num)
theorem B1262729 : Blo 996598 1262729 := bbase (se 2 (by rfl) ⟨473523, by rfl⟩ : syracuseStep 1262729 = 947047) (by norm_num)
theorem B2245805 : Blo 996598 2245805 := bbase (se 3 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 2245805 = 842177) (by norm_num)
theorem B1262785 : Blo 996598 1262785 := bbase (se 2 (by rfl) ⟨473544, by rfl⟩ : syracuseStep 1262785 = 947089) (by norm_num)
theorem B2245877 : Blo 996598 2245877 := bbase (se 5 (by rfl) ⟨105275, by rfl⟩ : syracuseStep 2245877 = 210551) (by norm_num)
theorem B5063957 : Blo 996598 5063957 := bbase (se 6 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 5063957 = 237373) (by norm_num)
theorem B1262881 : Blo 996598 1262881 := bbase (se 2 (by rfl) ⟨473580, by rfl⟩ : syracuseStep 1262881 = 947161) (by norm_num)
theorem B2245949 : Blo 996598 2245949 := bbase (se 3 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 2245949 = 842231) (by norm_num)
theorem B2246021 : Blo 996598 2246021 := bbase (se 4 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 2246021 = 421129) (by norm_num)
theorem B1066385 : Blo 996598 1066385 := bbase (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) (by norm_num)
theorem B1263053 : Blo 996598 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B2246093 : Blo 996598 2246093 := bbase (se 3 (by rfl) ⟨421142, by rfl⟩ : syracuseStep 2246093 = 842285) (by norm_num)
theorem B1263109 : Blo 996598 1263109 := bbase (se 4 (by rfl) ⟨118416, by rfl⟩ : syracuseStep 1263109 = 236833) (by norm_num)
theorem B2246165 : Blo 996598 2246165 := bbase (se 6 (by rfl) ⟨52644, by rfl⟩ : syracuseStep 2246165 = 105289) (by norm_num)
theorem B11388437 : Blo 996598 11388437 := bbase (se 6 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 11388437 = 533833) (by norm_num)
theorem B2246237 : Blo 996598 2246237 := bbase (se 3 (by rfl) ⟨421169, by rfl⟩ : syracuseStep 2246237 = 842339) (by norm_num)
theorem B1263205 : Blo 996598 1263205 := bbase (se 4 (by rfl) ⟨118425, by rfl⟩ : syracuseStep 1263205 = 236851) (by norm_num)
theorem B1197713 : Blo 996598 1197713 := bbase (se 2 (by rfl) ⟨449142, by rfl⟩ : syracuseStep 1197713 = 898285) (by norm_num)
theorem B2246309 : Blo 996598 2246309 := bbase (se 4 (by rfl) ⟨210591, by rfl⟩ : syracuseStep 2246309 = 421183) (by norm_num)
theorem B2246381 : Blo 996598 2246381 := bbase (se 3 (by rfl) ⟨421196, by rfl⟩ : syracuseStep 2246381 = 842393) (by norm_num)
theorem B1263377 : Blo 996598 1263377 := bbase (se 2 (by rfl) ⟨473766, by rfl⟩ : syracuseStep 1263377 = 947533) (by norm_num)
theorem B3786533 : Blo 996598 3786533 := bbase (se 4 (by rfl) ⟨354987, by rfl⟩ : syracuseStep 3786533 = 709975) (by norm_num)
theorem B2246453 : Blo 996598 2246453 := bbase (se 5 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 2246453 = 210605) (by norm_num)
theorem B1263433 : Blo 996598 1263433 := bbase (se 2 (by rfl) ⟨473787, by rfl⟩ : syracuseStep 1263433 = 947575) (by norm_num)
theorem B1066829 : Blo 996598 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B2246525 : Blo 996598 2246525 := bbase (se 3 (by rfl) ⟨421223, by rfl⟩ : syracuseStep 2246525 = 842447) (by norm_num)
theorem B1066889 : Blo 996598 1066889 := bbase (se 2 (by rfl) ⟨400083, by rfl⟩ : syracuseStep 1066889 = 800167) (by norm_num)
theorem B1263529 : Blo 996598 1263529 := bbase (se 2 (by rfl) ⟨473823, by rfl⟩ : syracuseStep 1263529 = 947647) (by norm_num)
theorem B2246597 : Blo 996598 2246597 := bbase (se 4 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 2246597 = 421237) (by norm_num)
theorem B1198049 : Blo 996598 1198049 := bbase (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) (by norm_num)
theorem B1067017 : Blo 996598 1067017 := bbase (se 2 (by rfl) ⟨400131, by rfl⟩ : syracuseStep 1067017 = 800263) (by norm_num)
theorem B2246669 : Blo 996598 2246669 := bbase (se 3 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 2246669 = 842501) (by norm_num)
theorem B3786821 : Blo 996598 3786821 := bbase (se 4 (by rfl) ⟨355014, by rfl⟩ : syracuseStep 3786821 = 710029) (by norm_num)
theorem B1198165 : Blo 996598 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B1263701 : Blo 996598 1263701 := bbase (se 8 (by rfl) ⟨7404, by rfl⟩ : syracuseStep 1263701 = 14809) (by norm_num)
theorem B2246741 : Blo 996598 2246741 := bbase (se 8 (by rfl) ⟨13164, by rfl⟩ : syracuseStep 2246741 = 26329) (by norm_num)
theorem B1263757 : Blo 996598 1263757 := bbase (se 3 (by rfl) ⟨236954, by rfl⟩ : syracuseStep 1263757 = 473909) (by norm_num)
theorem B1198237 : Blo 996598 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B2246813 : Blo 996598 2246813 := bbase (se 3 (by rfl) ⟨421277, by rfl⟩ : syracuseStep 2246813 = 842555) (by norm_num)
theorem B1198261 : Blo 996598 1198261 := bbase (se 5 (by rfl) ⟨56168, by rfl⟩ : syracuseStep 1198261 = 112337) (by norm_num)
theorem B2246885 : Blo 996598 2246885 := bbase (se 4 (by rfl) ⟨210645, by rfl⟩ : syracuseStep 2246885 = 421291) (by norm_num)
theorem B4802789 : Blo 996598 4802789 := bbase (se 4 (by rfl) ⟨450261, by rfl⟩ : syracuseStep 4802789 = 900523) (by norm_num)
theorem B1263853 : Blo 996598 1263853 := bbase (se 3 (by rfl) ⟨236972, by rfl⟩ : syracuseStep 1263853 = 473945) (by norm_num)
theorem B2246957 : Blo 996598 2246957 := bbase (se 3 (by rfl) ⟨421304, by rfl⟩ : syracuseStep 2246957 = 842609) (by norm_num)
theorem B1198405 : Blo 996598 1198405 := bbase (se 4 (by rfl) ⟨112350, by rfl⟩ : syracuseStep 1198405 = 224701) (by norm_num)
theorem B4802885 : Blo 996598 4802885 := bbase (se 4 (by rfl) ⟨450270, by rfl⟩ : syracuseStep 4802885 = 900541) (by norm_num)
theorem B2247029 : Blo 996598 2247029 := bbase (se 5 (by rfl) ⟨105329, by rfl⟩ : syracuseStep 2247029 = 210659) (by norm_num)
theorem B1264025 : Blo 996598 1264025 := bbase (se 2 (by rfl) ⟨474009, by rfl⟩ : syracuseStep 1264025 = 948019) (by norm_num)
theorem B2247101 : Blo 996598 2247101 := bbase (se 3 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 2247101 = 842663) (by norm_num)
theorem B1067461 : Blo 996598 1067461 := bbase (se 4 (by rfl) ⟨100074, by rfl⟩ : syracuseStep 1067461 = 200149) (by norm_num)
theorem B1264081 : Blo 996598 1264081 := bbase (se 2 (by rfl) ⟨474030, by rfl⟩ : syracuseStep 1264081 = 948061) (by norm_num)
theorem B2247173 : Blo 996598 2247173 := bbase (se 4 (by rfl) ⟨210672, by rfl⟩ : syracuseStep 2247173 = 421345) (by norm_num)
theorem B5065253 : Blo 996598 5065253 := bbase (se 4 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 5065253 = 949735) (by norm_num)
theorem B1264177 : Blo 996598 1264177 := bbase (se 2 (by rfl) ⟨474066, by rfl⟩ : syracuseStep 1264177 = 948133) (by norm_num)
theorem B1067581 : Blo 996598 1067581 := bbase (se 3 (by rfl) ⟨200171, by rfl⟩ : syracuseStep 1067581 = 400343) (by norm_num)
theorem B2247245 : Blo 996598 2247245 := bbase (se 3 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 2247245 = 842717) (by norm_num)
theorem B2247317 : Blo 996598 2247317 := bbase (se 6 (by rfl) ⟨52671, by rfl⟩ : syracuseStep 2247317 = 105343) (by norm_num)
theorem B2247389 : Blo 996598 2247389 := bbase (se 3 (by rfl) ⟨421385, by rfl⟩ : syracuseStep 2247389 = 842771) (by norm_num)
theorem B1264349 : Blo 996598 1264349 := bbase (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) (by norm_num)
theorem B1264405 : Blo 996598 1264405 := bbase (se 6 (by rfl) ⟨29634, by rfl⟩ : syracuseStep 1264405 = 59269) (by norm_num)
theorem B2247461 : Blo 996598 2247461 := bbase (se 4 (by rfl) ⟨210699, by rfl⟩ : syracuseStep 2247461 = 421399) (by norm_num)
theorem B1067833 : Blo 996598 1067833 := bbase (se 2 (by rfl) ⟨400437, by rfl⟩ : syracuseStep 1067833 = 800875) (by norm_num)
theorem B1067837 : Blo 996598 1067837 := bbase (se 3 (by rfl) ⟨200219, by rfl⟩ : syracuseStep 1067837 = 400439) (by norm_num)
theorem B2247533 : Blo 996598 2247533 := bbase (se 3 (by rfl) ⟨421412, by rfl⟩ : syracuseStep 2247533 = 842825) (by norm_num)
theorem B1264501 : Blo 996598 1264501 := bbase (se 5 (by rfl) ⟨59273, by rfl⟩ : syracuseStep 1264501 = 118547) (by norm_num)
theorem B2247605 : Blo 996598 2247605 := bbase (se 5 (by rfl) ⟨105356, by rfl⟩ : syracuseStep 2247605 = 210713) (by norm_num)
theorem B2247677 : Blo 996598 2247677 := bbase (se 3 (by rfl) ⟨421439, by rfl⟩ : syracuseStep 2247677 = 842879) (by norm_num)
theorem B1264673 : Blo 996598 1264673 := bbase (se 2 (by rfl) ⟨474252, by rfl⟩ : syracuseStep 1264673 = 948505) (by norm_num)
theorem B2247749 : Blo 996598 2247749 := bbase (se 4 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 2247749 = 421453) (by norm_num)
theorem B1264729 : Blo 996598 1264729 := bbase (se 2 (by rfl) ⟨474273, by rfl⟩ : syracuseStep 1264729 = 948547) (by norm_num)
theorem B2247821 : Blo 996598 2247821 := bbase (se 3 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 2247821 = 842933) (by norm_num)
theorem B1264825 : Blo 996598 1264825 := bbase (se 2 (by rfl) ⟨474309, by rfl⟩ : syracuseStep 1264825 = 948619) (by norm_num)
theorem B2247893 : Blo 996598 2247893 := bbase (se 7 (by rfl) ⟨26342, by rfl⟩ : syracuseStep 2247893 = 52685) (by norm_num)
theorem B3788005 : Blo 996598 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B2247965 : Blo 996598 2247965 := bbase (se 3 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 2247965 = 842987) (by norm_num)
theorem B2248037 : Blo 996598 2248037 := bbase (se 4 (by rfl) ⟨210753, by rfl⟩ : syracuseStep 2248037 = 421507) (by norm_num)
theorem B1264997 : Blo 996598 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B1822061 : Blo 996598 1822061 := bbase (se 3 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 1822061 = 683273) (by norm_num)
theorem B1068401 : Blo 996598 1068401 := bbase (se 2 (by rfl) ⟨400650, by rfl⟩ : syracuseStep 1068401 = 801301) (by norm_num)
theorem B1265053 : Blo 996598 1265053 := bbase (se 3 (by rfl) ⟨237197, by rfl⟩ : syracuseStep 1265053 = 474395) (by norm_num)
theorem B2248109 : Blo 996598 2248109 := bbase (se 3 (by rfl) ⟨421520, by rfl⟩ : syracuseStep 2248109 = 843041) (by norm_num)
theorem B3198437 : Blo 996598 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B2248181 : Blo 996598 2248181 := bbase (se 5 (by rfl) ⟨105383, by rfl⟩ : syracuseStep 2248181 = 210767) (by norm_num)
theorem B6082037 : Blo 996598 6082037 := bbase (se 5 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 6082037 = 570191) (by norm_num)
theorem B1265149 : Blo 996598 1265149 := bbase (se 3 (by rfl) ⟨237215, by rfl⟩ : syracuseStep 1265149 = 474431) (by norm_num)
theorem B1199621 : Blo 996598 1199621 := bbase (se 4 (by rfl) ⟨112464, by rfl⟩ : syracuseStep 1199621 = 224929) (by norm_num)
theorem B3788309 : Blo 996598 3788309 := bbase (se 6 (by rfl) ⟨88788, by rfl⟩ : syracuseStep 3788309 = 177577) (by norm_num)
theorem B2248253 : Blo 996598 2248253 := bbase (se 3 (by rfl) ⟨421547, by rfl⟩ : syracuseStep 2248253 = 843095) (by norm_num)
theorem B2248325 : Blo 996598 2248325 := bbase (se 4 (by rfl) ⟨210780, by rfl⟩ : syracuseStep 2248325 = 421561) (by norm_num)
theorem B1265321 : Blo 996598 1265321 := bbase (se 2 (by rfl) ⟨474495, by rfl⟩ : syracuseStep 1265321 = 948991) (by norm_num)
theorem B2248397 : Blo 996598 2248397 := bbase (se 3 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 2248397 = 843149) (by norm_num)
theorem B1265377 : Blo 996598 1265377 := bbase (se 2 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 1265377 = 949033) (by norm_num)
theorem B2248469 : Blo 996598 2248469 := bbase (se 6 (by rfl) ⟨52698, by rfl⟩ : syracuseStep 2248469 = 105397) (by norm_num)
theorem B1199929 : Blo 996598 1199929 := bbase (se 2 (by rfl) ⟨449973, by rfl⟩ : syracuseStep 1199929 = 899947) (by norm_num)
theorem B1265473 : Blo 996598 1265473 := bbase (se 2 (by rfl) ⟨474552, by rfl⟩ : syracuseStep 1265473 = 949105) (by norm_num)
theorem B2248541 : Blo 996598 2248541 := bbase (se 3 (by rfl) ⟨421601, by rfl⟩ : syracuseStep 2248541 = 843203) (by norm_num)
theorem B1494917 : Blo 996598 1494917 := bbase (se 4 (by rfl) ⟨140148, by rfl⟩ : syracuseStep 1494917 = 280297) (by norm_num)
theorem B1494941 : Blo 996598 1494941 := bbase (se 3 (by rfl) ⟨280301, by rfl⟩ : syracuseStep 1494941 = 560603) (by norm_num)
theorem B1200029 : Blo 996598 1200029 := bbase (se 3 (by rfl) ⟨225005, by rfl⟩ : syracuseStep 1200029 = 450011) (by norm_num)
theorem B2248613 : Blo 996598 2248613 := bbase (se 4 (by rfl) ⟨210807, by rfl⟩ : syracuseStep 2248613 = 421615) (by norm_num)
theorem B1494965 : Blo 996598 1494965 := bbase (se 5 (by rfl) ⟨70076, by rfl⟩ : syracuseStep 1494965 = 140153) (by norm_num)
theorem B1494989 : Blo 996598 1494989 := bbase (se 3 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 1494989 = 560621) (by norm_num)
theorem B1495013 : Blo 996598 1495013 := bbase (se 4 (by rfl) ⟨140157, by rfl⟩ : syracuseStep 1495013 = 280315) (by norm_num)
theorem B2248685 : Blo 996598 2248685 := bbase (se 3 (by rfl) ⟨421628, by rfl⟩ : syracuseStep 2248685 = 843257) (by norm_num)
theorem B1265645 : Blo 996598 1265645 := bbase (se 3 (by rfl) ⟨237308, by rfl⟩ : syracuseStep 1265645 = 474617) (by norm_num)
theorem B1495037 : Blo 996598 1495037 := bbase (se 3 (by rfl) ⟨280319, by rfl⟩ : syracuseStep 1495037 = 560639) (by norm_num)
theorem B1495061 : Blo 996598 1495061 := bbase (se 6 (by rfl) ⟨35040, by rfl⟩ : syracuseStep 1495061 = 70081) (by norm_num)
theorem B1265701 : Blo 996598 1265701 := bbase (se 4 (by rfl) ⟨118659, by rfl⟩ : syracuseStep 1265701 = 237319) (by norm_num)
theorem B1495085 : Blo 996598 1495085 := bbase (se 3 (by rfl) ⟨280328, by rfl⟩ : syracuseStep 1495085 = 560657) (by norm_num)
theorem B2248757 : Blo 996598 2248757 := bbase (se 5 (by rfl) ⟨105410, by rfl⟩ : syracuseStep 2248757 = 210821) (by norm_num)
theorem B1495109 : Blo 996598 1495109 := bbase (se 4 (by rfl) ⟨140166, by rfl⟩ : syracuseStep 1495109 = 280333) (by norm_num)
theorem B1495133 : Blo 996598 1495133 := bbase (se 3 (by rfl) ⟨280337, by rfl⟩ : syracuseStep 1495133 = 560675) (by norm_num)
theorem B1495157 : Blo 996598 1495157 := bbase (se 5 (by rfl) ⟨70085, by rfl⟩ : syracuseStep 1495157 = 140171) (by norm_num)
theorem B2248829 : Blo 996598 2248829 := bbase (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) (by norm_num)
theorem B1265797 : Blo 996598 1265797 := bbase (se 4 (by rfl) ⟨118668, by rfl⟩ : syracuseStep 1265797 = 237337) (by norm_num)
theorem B1495181 : Blo 996598 1495181 := bbase (se 3 (by rfl) ⟨280346, by rfl⟩ : syracuseStep 1495181 = 560693) (by norm_num)
theorem B1495205 : Blo 996598 1495205 := bbase (se 4 (by rfl) ⟨140175, by rfl⟩ : syracuseStep 1495205 = 280351) (by norm_num)
theorem B1495229 : Blo 996598 1495229 := bbase (se 3 (by rfl) ⟨280355, by rfl⟩ : syracuseStep 1495229 = 560711) (by norm_num)
theorem B2248901 : Blo 996598 2248901 := bbase (se 4 (by rfl) ⟨210834, by rfl⟩ : syracuseStep 2248901 = 421669) (by norm_num)
theorem B4804805 : Blo 996598 4804805 := bbase (se 4 (by rfl) ⟨450450, by rfl⟩ : syracuseStep 4804805 = 900901) (by norm_num)
theorem B1495253 : Blo 996598 1495253 := bbase (se 7 (by rfl) ⟨17522, by rfl⟩ : syracuseStep 1495253 = 35045) (by norm_num)
theorem B1495277 : Blo 996598 1495277 := bbase (se 3 (by rfl) ⟨280364, by rfl⟩ : syracuseStep 1495277 = 560729) (by norm_num)
theorem B1495301 : Blo 996598 1495301 := bbase (se 4 (by rfl) ⟨140184, by rfl⟩ : syracuseStep 1495301 = 280369) (by norm_num)
theorem B2248973 : Blo 996598 2248973 := bbase (se 3 (by rfl) ⟨421682, by rfl⟩ : syracuseStep 2248973 = 843365) (by norm_num)
theorem B1495325 : Blo 996598 1495325 := bbase (se 3 (by rfl) ⟨280373, by rfl⟩ : syracuseStep 1495325 = 560747) (by norm_num)
theorem B1200433 : Blo 996598 1200433 := bbase (se 2 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 1200433 = 900325) (by norm_num)
theorem B1265969 : Blo 996598 1265969 := bbase (se 2 (by rfl) ⟨474738, by rfl⟩ : syracuseStep 1265969 = 949477) (by norm_num)
theorem B1495349 : Blo 996598 1495349 := bbase (se 5 (by rfl) ⟨70094, by rfl⟩ : syracuseStep 1495349 = 140189) (by norm_num)
theorem B1495373 : Blo 996598 1495373 := bbase (se 3 (by rfl) ⟨280382, by rfl⟩ : syracuseStep 1495373 = 560765) (by norm_num)
theorem B2249045 : Blo 996598 2249045 := bbase (se 10 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 2249045 = 6589) (by norm_num)
theorem B1495397 : Blo 996598 1495397 := bbase (se 4 (by rfl) ⟨140193, by rfl⟩ : syracuseStep 1495397 = 280387) (by norm_num)
theorem B1266025 : Blo 996598 1266025 := bbase (se 2 (by rfl) ⟨474759, by rfl⟩ : syracuseStep 1266025 = 949519) (by norm_num)
theorem B1495421 : Blo 996598 1495421 := bbase (se 3 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 1495421 = 560783) (by norm_num)
theorem B1495445 : Blo 996598 1495445 := bbase (se 6 (by rfl) ⟨35049, by rfl⟩ : syracuseStep 1495445 = 70099) (by norm_num)
theorem B2249117 : Blo 996598 2249117 := bbase (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) (by norm_num)
theorem B1495469 : Blo 996598 1495469 := bbase (se 3 (by rfl) ⟨280400, by rfl⟩ : syracuseStep 1495469 = 560801) (by norm_num)
theorem B1495493 : Blo 996598 1495493 := bbase (se 4 (by rfl) ⟨140202, by rfl⟩ : syracuseStep 1495493 = 280405) (by norm_num)
theorem B1266121 : Blo 996598 1266121 := bbase (se 2 (by rfl) ⟨474795, by rfl⟩ : syracuseStep 1266121 = 949591) (by norm_num)
theorem B1495517 : Blo 996598 1495517 := bbase (se 3 (by rfl) ⟨280409, by rfl⟩ : syracuseStep 1495517 = 560819) (by norm_num)
theorem B2249189 : Blo 996598 2249189 := bbase (se 4 (by rfl) ⟨210861, by rfl⟩ : syracuseStep 2249189 = 421723) (by norm_num)
theorem B1495541 : Blo 996598 1495541 := bbase (se 5 (by rfl) ⟨70103, by rfl⟩ : syracuseStep 1495541 = 140207) (by norm_num)
theorem B2839045 : Blo 996598 2839045 := bbase (se 4 (by rfl) ⟨266160, by rfl⟩ : syracuseStep 2839045 = 532321) (by norm_num)
theorem B1495565 : Blo 996598 1495565 := bbase (se 3 (by rfl) ⟨280418, by rfl⟩ : syracuseStep 1495565 = 560837) (by norm_num)
theorem B1495589 : Blo 996598 1495589 := bbase (se 4 (by rfl) ⟨140211, by rfl⟩ : syracuseStep 1495589 = 280423) (by norm_num)
theorem B2249261 : Blo 996598 2249261 := bbase (se 3 (by rfl) ⟨421736, by rfl⟩ : syracuseStep 2249261 = 843473) (by norm_num)
theorem B1495613 : Blo 996598 1495613 := bbase (se 3 (by rfl) ⟨280427, by rfl⟩ : syracuseStep 1495613 = 560855) (by norm_num)
theorem B1495637 : Blo 996598 1495637 := bbase (se 8 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 1495637 = 17527) (by norm_num)
theorem B1495661 : Blo 996598 1495661 := bbase (se 3 (by rfl) ⟨280436, by rfl⟩ : syracuseStep 1495661 = 560873) (by norm_num)
theorem B2249333 : Blo 996598 2249333 := bbase (se 5 (by rfl) ⟨105437, by rfl⟩ : syracuseStep 2249333 = 210875) (by norm_num)
theorem B1266293 : Blo 996598 1266293 := bbase (se 5 (by rfl) ⟨59357, by rfl⟩ : syracuseStep 1266293 = 118715) (by norm_num)
theorem B1495685 : Blo 996598 1495685 := bbase (se 4 (by rfl) ⟨140220, by rfl⟩ : syracuseStep 1495685 = 280441) (by norm_num)
theorem B1495709 : Blo 996598 1495709 := bbase (se 3 (by rfl) ⟨280445, by rfl⟩ : syracuseStep 1495709 = 560891) (by norm_num)
theorem B2839205 : Blo 996598 2839205 := bbase (se 4 (by rfl) ⟨266175, by rfl⟩ : syracuseStep 2839205 = 532351) (by norm_num)
theorem B1266349 : Blo 996598 1266349 := bbase (se 3 (by rfl) ⟨237440, by rfl⟩ : syracuseStep 1266349 = 474881) (by norm_num)
theorem B1200817 : Blo 996598 1200817 := bbase (se 2 (by rfl) ⟨450306, by rfl⟩ : syracuseStep 1200817 = 900613) (by norm_num)
theorem B1495733 : Blo 996598 1495733 := bbase (se 5 (by rfl) ⟨70112, by rfl⟩ : syracuseStep 1495733 = 140225) (by norm_num)
theorem B2249405 : Blo 996598 2249405 := bbase (se 3 (by rfl) ⟨421763, by rfl⟩ : syracuseStep 2249405 = 843527) (by norm_num)
theorem B1495757 : Blo 996598 1495757 := bbase (se 3 (by rfl) ⟨280454, by rfl⟩ : syracuseStep 1495757 = 560909) (by norm_num)
theorem B1495781 : Blo 996598 1495781 := bbase (se 4 (by rfl) ⟨140229, by rfl⟩ : syracuseStep 1495781 = 280459) (by norm_num)
theorem B1495805 : Blo 996598 1495805 := bbase (se 3 (by rfl) ⟨280463, by rfl⟩ : syracuseStep 1495805 = 560927) (by norm_num)
theorem B2249477 : Blo 996598 2249477 := bbase (se 4 (by rfl) ⟨210888, by rfl⟩ : syracuseStep 2249477 = 421777) (by norm_num)
theorem B3363605 : Blo 996598 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B1495829 : Blo 996598 1495829 := bbase (se 6 (by rfl) ⟨35058, by rfl⟩ : syracuseStep 1495829 = 70117) (by norm_num)
theorem B1495853 : Blo 996598 1495853 := bbase (se 3 (by rfl) ⟨280472, by rfl⟩ : syracuseStep 1495853 = 560945) (by norm_num)
theorem B1495877 : Blo 996598 1495877 := bbase (se 4 (by rfl) ⟨140238, by rfl⟩ : syracuseStep 1495877 = 280477) (by norm_num)
theorem B2249549 : Blo 996598 2249549 := bbase (se 3 (by rfl) ⟨421790, by rfl⟩ : syracuseStep 2249549 = 843581) (by norm_num)
theorem B19452757 : Blo 996598 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B1495901 : Blo 996598 1495901 := bbase (se 3 (by rfl) ⟨280481, by rfl⟩ : syracuseStep 1495901 = 560963) (by norm_num)
theorem B1495925 : Blo 996598 1495925 := bbase (se 5 (by rfl) ⟨70121, by rfl⟩ : syracuseStep 1495925 = 140243) (by norm_num)
theorem B1495949 : Blo 996598 1495949 := bbase (se 3 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 1495949 = 560981) (by norm_num)
theorem B2839445 : Blo 996598 2839445 := bbase (se 6 (by rfl) ⟨66549, by rfl⟩ : syracuseStep 2839445 = 133099) (by norm_num)
theorem B2249621 : Blo 996598 2249621 := bbase (se 6 (by rfl) ⟨52725, by rfl⟩ : syracuseStep 2249621 = 105451) (by norm_num)
theorem B1495973 : Blo 996598 1495973 := bbase (se 4 (by rfl) ⟨140247, by rfl⟩ : syracuseStep 1495973 = 280495) (by norm_num)
theorem B1495997 : Blo 996598 1495997 := bbase (se 3 (by rfl) ⟨280499, by rfl⟩ : syracuseStep 1495997 = 560999) (by norm_num)
theorem B1496021 : Blo 996598 1496021 := bbase (se 7 (by rfl) ⟨17531, by rfl⟩ : syracuseStep 1496021 = 35063) (by norm_num)
theorem B2249693 : Blo 996598 2249693 := bbase (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) (by norm_num)
theorem B1463269 : Blo 996598 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B1496045 : Blo 996598 1496045 := bbase (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) (by norm_num)
theorem B1496069 : Blo 996598 1496069 := bbase (se 4 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 1496069 = 280513) (by norm_num)
theorem B1496093 : Blo 996598 1496093 := bbase (se 3 (by rfl) ⟨280517, by rfl⟩ : syracuseStep 1496093 = 561035) (by norm_num)
theorem B2249765 : Blo 996598 2249765 := bbase (se 4 (by rfl) ⟨210915, by rfl⟩ : syracuseStep 2249765 = 421831) (by norm_num)
theorem B1496117 : Blo 996598 1496117 := bbase (se 5 (by rfl) ⟨70130, by rfl⟩ : syracuseStep 1496117 = 140261) (by norm_num)
theorem B1496141 : Blo 996598 1496141 := bbase (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) (by norm_num)
theorem B2839637 : Blo 996598 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B1496165 : Blo 996598 1496165 := bbase (se 4 (by rfl) ⟨140265, by rfl⟩ : syracuseStep 1496165 = 280531) (by norm_num)
theorem B2249837 : Blo 996598 2249837 := bbase (se 3 (by rfl) ⟨421844, by rfl⟩ : syracuseStep 2249837 = 843689) (by norm_num)
theorem B1496189 : Blo 996598 1496189 := bbase (se 3 (by rfl) ⟨280535, by rfl⟩ : syracuseStep 1496189 = 561071) (by norm_num)
theorem B1496213 : Blo 996598 1496213 := bbase (se 6 (by rfl) ⟨35067, by rfl⟩ : syracuseStep 1496213 = 70135) (by norm_num)
theorem B1496237 : Blo 996598 1496237 := bbase (se 3 (by rfl) ⟨280544, by rfl⟩ : syracuseStep 1496237 = 561089) (by norm_num)
theorem B1201325 : Blo 996598 1201325 := bbase (se 3 (by rfl) ⟨225248, by rfl⟩ : syracuseStep 1201325 = 450497) (by norm_num)
theorem B2249909 : Blo 996598 2249909 := bbase (se 5 (by rfl) ⟨105464, by rfl⟩ : syracuseStep 2249909 = 210929) (by norm_num)
theorem B3364037 : Blo 996598 3364037 := bbase (se 4 (by rfl) ⟨315378, by rfl⟩ : syracuseStep 3364037 = 630757) (by norm_num)
theorem B1496261 : Blo 996598 1496261 := bbase (se 4 (by rfl) ⟨140274, by rfl⟩ : syracuseStep 1496261 = 280549) (by norm_num)
theorem B1496285 : Blo 996598 1496285 := bbase (se 3 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 1496285 = 561107) (by norm_num)
theorem B1496309 : Blo 996598 1496309 := bbase (se 5 (by rfl) ⟨70139, by rfl⟩ : syracuseStep 1496309 = 140279) (by norm_num)
theorem B2249981 : Blo 996598 2249981 := bbase (se 3 (by rfl) ⟨421871, by rfl⟩ : syracuseStep 2249981 = 843743) (by norm_num)
theorem B1496333 : Blo 996598 1496333 := bbase (se 3 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 1496333 = 561125) (by norm_num)
theorem B1496357 : Blo 996598 1496357 := bbase (se 4 (by rfl) ⟨140283, by rfl⟩ : syracuseStep 1496357 = 280567) (by norm_num)
theorem B1496381 : Blo 996598 1496381 := bbase (se 3 (by rfl) ⟨280571, by rfl⟩ : syracuseStep 1496381 = 561143) (by norm_num)
theorem B5199173 : Blo 996598 5199173 := bbase (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) (by norm_num)
theorem B2250053 : Blo 996598 2250053 := bbase (se 4 (by rfl) ⟨210942, by rfl⟩ : syracuseStep 2250053 = 421885) (by norm_num)
theorem B2053453 : Blo 996598 2053453 := bbase (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) (by norm_num)
theorem B1496405 : Blo 996598 1496405 := bbase (se 15 (by rfl) ⟨68, by rfl⟩ : syracuseStep 1496405 = 137) (by norm_num)
theorem B1496429 : Blo 996598 1496429 := bbase (se 3 (by rfl) ⟨280580, by rfl⟩ : syracuseStep 1496429 = 561161) (by norm_num)
theorem B1496453 : Blo 996598 1496453 := bbase (se 4 (by rfl) ⟨140292, by rfl⟩ : syracuseStep 1496453 = 280585) (by norm_num)
theorem B2250125 : Blo 996598 2250125 := bbase (se 3 (by rfl) ⟨421898, by rfl⟩ : syracuseStep 2250125 = 843797) (by norm_num)
theorem B1496477 : Blo 996598 1496477 := bbase (se 3 (by rfl) ⟨280589, by rfl⟩ : syracuseStep 1496477 = 561179) (by norm_num)
theorem B1496501 : Blo 996598 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B1496525 : Blo 996598 1496525 := bbase (se 3 (by rfl) ⟨280598, by rfl⟩ : syracuseStep 1496525 = 561197) (by norm_num)
theorem B2250197 : Blo 996598 2250197 := bbase (se 7 (by rfl) ⟨26369, by rfl⟩ : syracuseStep 2250197 = 52739) (by norm_num)
theorem B1496549 : Blo 996598 1496549 := bbase (se 4 (by rfl) ⟨140301, by rfl⟩ : syracuseStep 1496549 = 280603) (by norm_num)
theorem B1496573 : Blo 996598 1496573 := bbase (se 3 (by rfl) ⟨280607, by rfl⟩ : syracuseStep 1496573 = 561215) (by norm_num)
theorem B1201673 : Blo 996598 1201673 := bbase (se 2 (by rfl) ⟨450627, by rfl⟩ : syracuseStep 1201673 = 901255) (by norm_num)
theorem B1496597 : Blo 996598 1496597 := bbase (se 6 (by rfl) ⟨35076, by rfl⟩ : syracuseStep 1496597 = 70153) (by norm_num)
theorem B4052501 : Blo 996598 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B2250269 : Blo 996598 2250269 := bbase (se 3 (by rfl) ⟨421925, by rfl⟩ : syracuseStep 2250269 = 843851) (by norm_num)
theorem B1496621 : Blo 996598 1496621 := bbase (se 3 (by rfl) ⟨280616, by rfl⟩ : syracuseStep 1496621 = 561233) (by norm_num)
theorem B9229877 : Blo 996598 9229877 := bbase (se 5 (by rfl) ⟨432650, by rfl⟩ : syracuseStep 9229877 = 865301) (by norm_num)
theorem B1496645 : Blo 996598 1496645 := bbase (se 4 (by rfl) ⟨140310, by rfl⟩ : syracuseStep 1496645 = 280621) (by norm_num)
theorem B3790421 : Blo 996598 3790421 := bbase (se 8 (by rfl) ⟨22209, by rfl⟩ : syracuseStep 3790421 = 44419) (by norm_num)
theorem B4806229 : Blo 996598 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B1496669 : Blo 996598 1496669 := bbase (se 3 (by rfl) ⟨280625, by rfl⟩ : syracuseStep 1496669 = 561251) (by norm_num)
theorem B2250341 : Blo 996598 2250341 := bbase (se 4 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 2250341 = 421939) (by norm_num)
theorem B3364469 : Blo 996598 3364469 := bbase (se 5 (by rfl) ⟨157709, by rfl⟩ : syracuseStep 3364469 = 315419) (by norm_num)
theorem B1496693 : Blo 996598 1496693 := bbase (se 5 (by rfl) ⟨70157, by rfl⟩ : syracuseStep 1496693 = 140315) (by norm_num)
theorem B3200629 : Blo 996598 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B1496717 : Blo 996598 1496717 := bbase (se 3 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 1496717 = 561269) (by norm_num)
theorem B1496741 : Blo 996598 1496741 := bbase (se 4 (by rfl) ⟨140319, by rfl⟩ : syracuseStep 1496741 = 280639) (by norm_num)
theorem B2250413 : Blo 996598 2250413 := bbase (se 3 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 2250413 = 843905) (by norm_num)
theorem B1496765 : Blo 996598 1496765 := bbase (se 3 (by rfl) ⟨280643, by rfl⟩ : syracuseStep 1496765 = 561287) (by norm_num)
theorem B1496789 : Blo 996598 1496789 := bbase (se 7 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 1496789 = 35081) (by norm_num)
theorem B1496813 : Blo 996598 1496813 := bbase (se 3 (by rfl) ⟨280652, by rfl⟩ : syracuseStep 1496813 = 561305) (by norm_num)
theorem B2250485 : Blo 996598 2250485 := bbase (se 5 (by rfl) ⟨105491, by rfl⟩ : syracuseStep 2250485 = 210983) (by norm_num)
theorem B1496837 : Blo 996598 1496837 := bbase (se 4 (by rfl) ⟨140328, by rfl⟩ : syracuseStep 1496837 = 280657) (by norm_num)
theorem B1496861 : Blo 996598 1496861 := bbase (se 3 (by rfl) ⟨280661, by rfl⟩ : syracuseStep 1496861 = 561323) (by norm_num)
theorem B1496885 : Blo 996598 1496885 := bbase (se 5 (by rfl) ⟨70166, by rfl⟩ : syracuseStep 1496885 = 140333) (by norm_num)
theorem B2250557 : Blo 996598 2250557 := bbase (se 3 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 2250557 = 843959) (by norm_num)
theorem B1201981 : Blo 996598 1201981 := bbase (se 3 (by rfl) ⟨225371, by rfl⟩ : syracuseStep 1201981 = 450743) (by norm_num)
theorem B1496909 : Blo 996598 1496909 := bbase (se 3 (by rfl) ⟨280670, by rfl⟩ : syracuseStep 1496909 = 561341) (by norm_num)
theorem B14374741 : Blo 996598 14374741 := bbase (se 9 (by rfl) ⟨42113, by rfl⟩ : syracuseStep 14374741 = 84227) (by norm_num)
theorem B1300313 : Blo 996598 1300313 := bbase (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) (by norm_num)
theorem B1496933 : Blo 996598 1496933 := bbase (se 4 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 1496933 = 280675) (by norm_num)
theorem B3790709 : Blo 996598 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B1496957 : Blo 996598 1496957 := bbase (se 3 (by rfl) ⟨280679, by rfl⟩ : syracuseStep 1496957 = 561359) (by norm_num)
theorem B2250629 : Blo 996598 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B1496981 : Blo 996598 1496981 := bbase (se 6 (by rfl) ⟨35085, by rfl⟩ : syracuseStep 1496981 = 70171) (by norm_num)
theorem B1497005 : Blo 996598 1497005 := bbase (se 3 (by rfl) ⟨280688, by rfl⟩ : syracuseStep 1497005 = 561377) (by norm_num)
theorem B1497029 : Blo 996598 1497029 := bbase (se 4 (by rfl) ⟨140346, by rfl⟩ : syracuseStep 1497029 = 280693) (by norm_num)
theorem B2250701 : Blo 996598 2250701 := bbase (se 3 (by rfl) ⟨422006, by rfl⟩ : syracuseStep 2250701 = 844013) (by norm_num)
theorem B1497053 : Blo 996598 1497053 := bbase (se 3 (by rfl) ⟨280697, by rfl⟩ : syracuseStep 1497053 = 561395) (by norm_num)
theorem B1497077 : Blo 996598 1497077 := bbase (se 5 (by rfl) ⟨70175, by rfl⟩ : syracuseStep 1497077 = 140351) (by norm_num)
theorem B1497101 : Blo 996598 1497101 := bbase (se 3 (by rfl) ⟨280706, by rfl⟩ : syracuseStep 1497101 = 561413) (by norm_num)
theorem B2250773 : Blo 996598 2250773 := bbase (se 6 (by rfl) ⟨52752, by rfl⟩ : syracuseStep 2250773 = 105505) (by norm_num)
theorem B3364901 : Blo 996598 3364901 := bbase (se 4 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 3364901 = 630919) (by norm_num)
theorem B1497125 : Blo 996598 1497125 := bbase (se 4 (by rfl) ⟨140355, by rfl⟩ : syracuseStep 1497125 = 280711) (by norm_num)
theorem B2840629 : Blo 996598 2840629 := bbase (se 5 (by rfl) ⟨133154, by rfl⟩ : syracuseStep 2840629 = 266309) (by norm_num)
theorem B1497149 : Blo 996598 1497149 := bbase (se 3 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 1497149 = 561431) (by norm_num)
theorem B1497173 : Blo 996598 1497173 := bbase (se 8 (by rfl) ⟨8772, by rfl⟩ : syracuseStep 1497173 = 17545) (by norm_num)
theorem B2250845 : Blo 996598 2250845 := bbase (se 3 (by rfl) ⟨422033, by rfl⟩ : syracuseStep 2250845 = 844067) (by norm_num)
theorem B1136737 : Blo 996598 1136737 := bbase (se 2 (by rfl) ⟨426276, by rfl⟩ : syracuseStep 1136737 = 852553) (by norm_num)
theorem B1497197 : Blo 996598 1497197 := bbase (se 3 (by rfl) ⟨280724, by rfl⟩ : syracuseStep 1497197 = 561449) (by norm_num)
theorem B1136773 : Blo 996598 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B1497221 : Blo 996598 1497221 := bbase (se 4 (by rfl) ⟨140364, by rfl⟩ : syracuseStep 1497221 = 280729) (by norm_num)
theorem B1497245 : Blo 996598 1497245 := bbase (se 3 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 1497245 = 561467) (by norm_num)
theorem B2250917 : Blo 996598 2250917 := bbase (se 4 (by rfl) ⟨211023, by rfl⟩ : syracuseStep 2250917 = 422047) (by norm_num)
theorem B1497269 : Blo 996598 1497269 := bbase (se 5 (by rfl) ⟨70184, by rfl⟩ : syracuseStep 1497269 = 140369) (by norm_num)
theorem B1497293 : Blo 996598 1497293 := bbase (se 3 (by rfl) ⟨280742, by rfl⟩ : syracuseStep 1497293 = 561485) (by norm_num)
theorem B1497317 : Blo 996598 1497317 := bbase (se 4 (by rfl) ⟨140373, by rfl⟩ : syracuseStep 1497317 = 280747) (by norm_num)
theorem B2250989 : Blo 996598 2250989 := bbase (se 3 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 2250989 = 844121) (by norm_num)
theorem B1497341 : Blo 996598 1497341 := bbase (se 3 (by rfl) ⟨280751, by rfl⟩ : syracuseStep 1497341 = 561503) (by norm_num)
theorem B1497365 : Blo 996598 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B1497389 : Blo 996598 1497389 := bbase (se 3 (by rfl) ⟨280760, by rfl⟩ : syracuseStep 1497389 = 561521) (by norm_num)
theorem B2251061 : Blo 996598 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B1497413 : Blo 996598 1497413 := bbase (se 4 (by rfl) ⟨140382, by rfl⟩ : syracuseStep 1497413 = 280765) (by norm_num)
theorem B1497437 : Blo 996598 1497437 := bbase (se 3 (by rfl) ⟨280769, by rfl⟩ : syracuseStep 1497437 = 561539) (by norm_num)
theorem B1497461 : Blo 996598 1497461 := bbase (se 5 (by rfl) ⟨70193, by rfl⟩ : syracuseStep 1497461 = 140387) (by norm_num)
theorem B2251133 : Blo 996598 2251133 := bbase (se 3 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 2251133 = 844175) (by norm_num)
theorem B1497485 : Blo 996598 1497485 := bbase (se 3 (by rfl) ⟨280778, by rfl⟩ : syracuseStep 1497485 = 561557) (by norm_num)
theorem B1497509 : Blo 996598 1497509 := bbase (se 4 (by rfl) ⟨140391, by rfl⟩ : syracuseStep 1497509 = 280783) (by norm_num)
theorem B3201461 : Blo 996598 3201461 := bbase (se 5 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 3201461 = 300137) (by norm_num)
theorem B5757365 : Blo 996598 5757365 := bbase (se 5 (by rfl) ⟨269876, by rfl⟩ : syracuseStep 5757365 = 539753) (by norm_num)
theorem B1497533 : Blo 996598 1497533 := bbase (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) (by norm_num)
theorem B2251205 : Blo 996598 2251205 := bbase (se 4 (by rfl) ⟨211050, by rfl⟩ : syracuseStep 2251205 = 422101) (by norm_num)
theorem B1137097 : Blo 996598 1137097 := bbase (se 2 (by rfl) ⟨426411, by rfl⟩ : syracuseStep 1137097 = 852823) (by norm_num)
theorem B3365333 : Blo 996598 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B1497557 : Blo 996598 1497557 := bbase (se 7 (by rfl) ⟨17549, by rfl⟩ : syracuseStep 1497557 = 35099) (by norm_num)
theorem B3594725 : Blo 996598 3594725 := bbase (se 4 (by rfl) ⟨337005, by rfl⟩ : syracuseStep 3594725 = 674011) (by norm_num)
theorem B1497581 : Blo 996598 1497581 := bbase (se 3 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 1497581 = 561593) (by norm_num)
theorem B1497605 : Blo 996598 1497605 := bbase (se 4 (by rfl) ⟨140400, by rfl⟩ : syracuseStep 1497605 = 280801) (by norm_num)
theorem B2251277 : Blo 996598 2251277 := bbase (se 3 (by rfl) ⟨422114, by rfl⟩ : syracuseStep 2251277 = 844229) (by norm_num)
theorem B1497629 : Blo 996598 1497629 := bbase (se 3 (by rfl) ⟨280805, by rfl⟩ : syracuseStep 1497629 = 561611) (by norm_num)
theorem B1497653 : Blo 996598 1497653 := bbase (se 5 (by rfl) ⟨70202, by rfl⟩ : syracuseStep 1497653 = 140405) (by norm_num)
theorem B4381253 : Blo 996598 4381253 := bbase (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) (by norm_num)
theorem B1497677 : Blo 996598 1497677 := bbase (se 3 (by rfl) ⟨280814, by rfl⟩ : syracuseStep 1497677 = 561629) (by norm_num)
theorem B1497701 : Blo 996598 1497701 := bbase (se 4 (by rfl) ⟨140409, by rfl⟩ : syracuseStep 1497701 = 280819) (by norm_num)
theorem B1497725 : Blo 996598 1497725 := bbase (se 3 (by rfl) ⟨280823, by rfl⟩ : syracuseStep 1497725 = 561647) (by norm_num)
theorem B1497749 : Blo 996598 1497749 := bbase (se 6 (by rfl) ⟨35103, by rfl⟩ : syracuseStep 1497749 = 70207) (by norm_num)
theorem B1497773 : Blo 996598 1497773 := bbase (se 3 (by rfl) ⟨280832, by rfl⟩ : syracuseStep 1497773 = 561665) (by norm_num)
theorem B1497797 : Blo 996598 1497797 := bbase (se 4 (by rfl) ⟨140418, by rfl⟩ : syracuseStep 1497797 = 280837) (by norm_num)
theorem B1497821 : Blo 996598 1497821 := bbase (se 3 (by rfl) ⟨280841, by rfl⟩ : syracuseStep 1497821 = 561683) (by norm_num)
theorem B1497845 : Blo 996598 1497845 := bbase (se 5 (by rfl) ⟨70211, by rfl⟩ : syracuseStep 1497845 = 140423) (by norm_num)
theorem B3595013 : Blo 996598 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B1497869 : Blo 996598 1497869 := bbase (se 3 (by rfl) ⟨280850, by rfl⟩ : syracuseStep 1497869 = 561701) (by norm_num)
theorem B1497893 : Blo 996598 1497893 := bbase (se 4 (by rfl) ⟨140427, by rfl⟩ : syracuseStep 1497893 = 280855) (by norm_num)
theorem B1497917 : Blo 996598 1497917 := bbase (se 3 (by rfl) ⟨280859, by rfl⟩ : syracuseStep 1497917 = 561719) (by norm_num)
theorem B1497941 : Blo 996598 1497941 := bbase (se 9 (by rfl) ⟨4388, by rfl⟩ : syracuseStep 1497941 = 8777) (by norm_num)
theorem B1497965 : Blo 996598 1497965 := bbase (se 3 (by rfl) ⟨280868, by rfl⟩ : syracuseStep 1497965 = 561737) (by norm_num)
theorem B3365765 : Blo 996598 3365765 := bbase (se 4 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 3365765 = 631081) (by norm_num)
theorem B1497989 : Blo 996598 1497989 := bbase (se 4 (by rfl) ⟨140436, by rfl⟩ : syracuseStep 1497989 = 280873) (by norm_num)
theorem B1498013 : Blo 996598 1498013 := bbase (se 3 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 1498013 = 561755) (by norm_num)
theorem B1498037 : Blo 996598 1498037 := bbase (se 5 (by rfl) ⟨70220, by rfl⟩ : syracuseStep 1498037 = 140441) (by norm_num)
theorem B1498061 : Blo 996598 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B1498085 : Blo 996598 1498085 := bbase (se 4 (by rfl) ⟨140445, by rfl⟩ : syracuseStep 1498085 = 280891) (by norm_num)
theorem B1137649 : Blo 996598 1137649 := bbase (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) (by norm_num)
theorem B1498109 : Blo 996598 1498109 := bbase (se 3 (by rfl) ⟨280895, by rfl⟩ : syracuseStep 1498109 = 561791) (by norm_num)
theorem B3791893 : Blo 996598 3791893 := bbase (se 6 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 3791893 = 177745) (by norm_num)
theorem B1498133 : Blo 996598 1498133 := bbase (se 6 (by rfl) ⟨35112, by rfl⟩ : syracuseStep 1498133 = 70225) (by norm_num)
theorem B1498157 : Blo 996598 1498157 := bbase (se 3 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 1498157 = 561809) (by norm_num)
theorem B1498181 : Blo 996598 1498181 := bbase (se 4 (by rfl) ⟨140454, by rfl⟩ : syracuseStep 1498181 = 280909) (by norm_num)
theorem B1498205 : Blo 996598 1498205 := bbase (se 3 (by rfl) ⟨280913, by rfl⟩ : syracuseStep 1498205 = 561827) (by norm_num)
theorem B1498229 : Blo 996598 1498229 := bbase (se 5 (by rfl) ⟨70229, by rfl⟩ : syracuseStep 1498229 = 140459) (by norm_num)
theorem B2841733 : Blo 996598 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B1498253 : Blo 996598 1498253 := bbase (se 3 (by rfl) ⟨280922, by rfl⟩ : syracuseStep 1498253 = 561845) (by norm_num)
theorem B1498277 : Blo 996598 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B1498301 : Blo 996598 1498301 := bbase (se 3 (by rfl) ⟨280931, by rfl⟩ : syracuseStep 1498301 = 561863) (by norm_num)
theorem B1498325 : Blo 996598 1498325 := bbase (se 7 (by rfl) ⟨17558, by rfl⟩ : syracuseStep 1498325 = 35117) (by norm_num)
theorem B1498349 : Blo 996598 1498349 := bbase (se 3 (by rfl) ⟨280940, by rfl⟩ : syracuseStep 1498349 = 561881) (by norm_num)
theorem B1498373 : Blo 996598 1498373 := bbase (se 4 (by rfl) ⟨140472, by rfl⟩ : syracuseStep 1498373 = 280945) (by norm_num)
theorem B1498397 : Blo 996598 1498397 := bbase (se 3 (by rfl) ⟨280949, by rfl⟩ : syracuseStep 1498397 = 561899) (by norm_num)
theorem B3366197 : Blo 996598 3366197 := bbase (se 5 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 3366197 = 315581) (by norm_num)
theorem B1498421 : Blo 996598 1498421 := bbase (se 5 (by rfl) ⟨70238, by rfl⟩ : syracuseStep 1498421 = 140477) (by norm_num)
theorem B3792197 : Blo 996598 3792197 := bbase (se 4 (by rfl) ⟨355518, by rfl⟩ : syracuseStep 3792197 = 711037) (by norm_num)
theorem B1498445 : Blo 996598 1498445 := bbase (se 3 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 1498445 = 561917) (by norm_num)
theorem B1498469 : Blo 996598 1498469 := bbase (se 4 (by rfl) ⟨140481, by rfl⟩ : syracuseStep 1498469 = 280963) (by norm_num)
theorem B1498493 : Blo 996598 1498493 := bbase (se 3 (by rfl) ⟨280967, by rfl⟩ : syracuseStep 1498493 = 561935) (by norm_num)
theorem B1498517 : Blo 996598 1498517 := bbase (se 6 (by rfl) ⟨35121, by rfl⟩ : syracuseStep 1498517 = 70243) (by norm_num)
theorem B1596829 : Blo 996598 1596829 := bbase (se 3 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 1596829 = 598811) (by norm_num)
theorem B1498541 : Blo 996598 1498541 := bbase (se 3 (by rfl) ⟨280976, by rfl⟩ : syracuseStep 1498541 = 561953) (by norm_num)
theorem B1498565 : Blo 996598 1498565 := bbase (se 4 (by rfl) ⟨140490, by rfl⟩ : syracuseStep 1498565 = 280981) (by norm_num)
theorem B1498589 : Blo 996598 1498589 := bbase (se 3 (by rfl) ⟨280985, by rfl⟩ : syracuseStep 1498589 = 561971) (by norm_num)
theorem B1498613 : Blo 996598 1498613 := bbase (se 5 (by rfl) ⟨70247, by rfl⟩ : syracuseStep 1498613 = 140495) (by norm_num)
theorem B6839797 : Blo 996598 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B1498637 : Blo 996598 1498637 := bbase (se 3 (by rfl) ⟨280994, by rfl⟩ : syracuseStep 1498637 = 561989) (by norm_num)
theorem B2022941 : Blo 996598 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B1498661 : Blo 996598 1498661 := bbase (se 4 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 1498661 = 280999) (by norm_num)
theorem B1498685 : Blo 996598 1498685 := bbase (se 3 (by rfl) ⟨281003, by rfl⟩ : syracuseStep 1498685 = 562007) (by norm_num)
theorem B1498709 : Blo 996598 1498709 := bbase (se 8 (by rfl) ⟨8781, by rfl⟩ : syracuseStep 1498709 = 17563) (by norm_num)
theorem B1498733 : Blo 996598 1498733 := bbase (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) (by norm_num)
theorem B1498757 : Blo 996598 1498757 := bbase (se 4 (by rfl) ⟨140508, by rfl⟩ : syracuseStep 1498757 = 281017) (by norm_num)
theorem B1498781 : Blo 996598 1498781 := bbase (se 3 (by rfl) ⟨281021, by rfl⟩ : syracuseStep 1498781 = 562043) (by norm_num)
theorem B1498805 : Blo 996598 1498805 := bbase (se 5 (by rfl) ⟨70256, by rfl⟩ : syracuseStep 1498805 = 140513) (by norm_num)
theorem B1498829 : Blo 996598 1498829 := bbase (se 3 (by rfl) ⟨281030, by rfl⟩ : syracuseStep 1498829 = 562061) (by norm_num)
theorem B3366629 : Blo 996598 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B1498853 : Blo 996598 1498853 := bbase (se 4 (by rfl) ⟨140517, by rfl⟩ : syracuseStep 1498853 = 281035) (by norm_num)
theorem B1498877 : Blo 996598 1498877 := bbase (se 3 (by rfl) ⟨281039, by rfl⟩ : syracuseStep 1498877 = 562079) (by norm_num)
theorem B1498901 : Blo 996598 1498901 := bbase (se 6 (by rfl) ⟨35130, by rfl⟩ : syracuseStep 1498901 = 70261) (by norm_num)
theorem B7593749 : Blo 996598 7593749 := bbase (se 6 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 7593749 = 355957) (by norm_num)
theorem B1498925 : Blo 996598 1498925 := bbase (se 3 (by rfl) ⟨281048, by rfl⟩ : syracuseStep 1498925 = 562097) (by norm_num)
theorem B1498949 : Blo 996598 1498949 := bbase (se 4 (by rfl) ⟨140526, by rfl⟩ : syracuseStep 1498949 = 281053) (by norm_num)
theorem B1892173 : Blo 996598 1892173 := bbase (se 3 (by rfl) ⟨354782, by rfl⟩ : syracuseStep 1892173 = 709565) (by norm_num)
theorem B1498973 : Blo 996598 1498973 := bbase (se 3 (by rfl) ⟨281057, by rfl⟩ : syracuseStep 1498973 = 562115) (by norm_num)
theorem B1498997 : Blo 996598 1498997 := bbase (se 5 (by rfl) ⟨70265, by rfl⟩ : syracuseStep 1498997 = 140531) (by norm_num)
theorem B1499021 : Blo 996598 1499021 := bbase (se 3 (by rfl) ⟨281066, by rfl⟩ : syracuseStep 1499021 = 562133) (by norm_num)
theorem B1499045 : Blo 996598 1499045 := bbase (se 4 (by rfl) ⟨140535, by rfl⟩ : syracuseStep 1499045 = 281071) (by norm_num)
theorem B4054949 : Blo 996598 4054949 := bbase (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) (by norm_num)
theorem B1499069 : Blo 996598 1499069 := bbase (se 3 (by rfl) ⟨281075, by rfl⟩ : syracuseStep 1499069 = 562151) (by norm_num)
theorem B1499093 : Blo 996598 1499093 := bbase (se 7 (by rfl) ⟨17567, by rfl⟩ : syracuseStep 1499093 = 35135) (by norm_num)
theorem B1892317 : Blo 996598 1892317 := bbase (se 3 (by rfl) ⟨354809, by rfl⟩ : syracuseStep 1892317 = 709619) (by norm_num)
theorem B1499117 : Blo 996598 1499117 := bbase (se 3 (by rfl) ⟨281084, by rfl⟩ : syracuseStep 1499117 = 562169) (by norm_num)
theorem B1499141 : Blo 996598 1499141 := bbase (se 4 (by rfl) ⟨140544, by rfl⟩ : syracuseStep 1499141 = 281089) (by norm_num)
theorem B1925141 : Blo 996598 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B1499165 : Blo 996598 1499165 := bbase (se 3 (by rfl) ⟨281093, by rfl⟩ : syracuseStep 1499165 = 562187) (by norm_num)
theorem B1499189 : Blo 996598 1499189 := bbase (se 5 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 1499189 = 140549) (by norm_num)
theorem B1597501 : Blo 996598 1597501 := bbase (se 3 (by rfl) ⟨299531, by rfl⟩ : syracuseStep 1597501 = 599063) (by norm_num)
theorem B1499213 : Blo 996598 1499213 := bbase (se 3 (by rfl) ⟨281102, by rfl⟩ : syracuseStep 1499213 = 562205) (by norm_num)
theorem B1499237 : Blo 996598 1499237 := bbase (se 4 (by rfl) ⟨140553, by rfl⟩ : syracuseStep 1499237 = 281107) (by norm_num)
theorem B1892477 : Blo 996598 1892477 := bbase (se 3 (by rfl) ⟨354839, by rfl⟩ : syracuseStep 1892477 = 709679) (by norm_num)
theorem B1499261 : Blo 996598 1499261 := bbase (se 3 (by rfl) ⟨281111, by rfl⟩ : syracuseStep 1499261 = 562223) (by norm_num)
theorem B3367061 : Blo 996598 3367061 := bbase (se 6 (by rfl) ⟨78915, by rfl⟩ : syracuseStep 3367061 = 157831) (by norm_num)
theorem B1499285 : Blo 996598 1499285 := bbase (se 6 (by rfl) ⟨35139, by rfl⟩ : syracuseStep 1499285 = 70279) (by norm_num)
theorem B1499309 : Blo 996598 1499309 := bbase (se 3 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 1499309 = 562241) (by norm_num)
theorem B1499333 : Blo 996598 1499333 := bbase (se 4 (by rfl) ⟨140562, by rfl⟩ : syracuseStep 1499333 = 281125) (by norm_num)
theorem B1499357 : Blo 996598 1499357 := bbase (se 3 (by rfl) ⟨281129, by rfl⟩ : syracuseStep 1499357 = 562259) (by norm_num)
theorem B3039461 : Blo 996598 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B1499381 : Blo 996598 1499381 := bbase (se 5 (by rfl) ⟨70283, by rfl⟩ : syracuseStep 1499381 = 140567) (by norm_num)
theorem B3203333 : Blo 996598 3203333 := bbase (se 4 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 3203333 = 600625) (by norm_num)
theorem B1892621 : Blo 996598 1892621 := bbase (se 3 (by rfl) ⟨354866, by rfl⟩ : syracuseStep 1892621 = 709733) (by norm_num)
theorem B1499405 : Blo 996598 1499405 := bbase (se 3 (by rfl) ⟨281138, by rfl⟩ : syracuseStep 1499405 = 562277) (by norm_num)
theorem B1499429 : Blo 996598 1499429 := bbase (se 4 (by rfl) ⟨140571, by rfl⟩ : syracuseStep 1499429 = 281143) (by norm_num)
theorem B1499453 : Blo 996598 1499453 := bbase (se 3 (by rfl) ⟨281147, by rfl⟩ : syracuseStep 1499453 = 562295) (by norm_num)
theorem B1499477 : Blo 996598 1499477 := bbase (se 10 (by rfl) ⟨2196, by rfl⟩ : syracuseStep 1499477 = 4393) (by norm_num)
theorem B1499501 : Blo 996598 1499501 := bbase (se 3 (by rfl) ⟨281156, by rfl⟩ : syracuseStep 1499501 = 562313) (by norm_num)
theorem B1499525 : Blo 996598 1499525 := bbase (se 4 (by rfl) ⟨140580, by rfl⟩ : syracuseStep 1499525 = 281161) (by norm_num)
theorem B1499549 : Blo 996598 1499549 := bbase (se 3 (by rfl) ⟨281165, by rfl⟩ : syracuseStep 1499549 = 562331) (by norm_num)
theorem B1499573 : Blo 996598 1499573 := bbase (se 5 (by rfl) ⟨70292, by rfl⟩ : syracuseStep 1499573 = 140585) (by norm_num)
theorem B1139141 : Blo 996598 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B1499597 : Blo 996598 1499597 := bbase (se 3 (by rfl) ⟨281174, by rfl⟩ : syracuseStep 1499597 = 562349) (by norm_num)
theorem B1499621 : Blo 996598 1499621 := bbase (se 4 (by rfl) ⟨140589, by rfl⟩ : syracuseStep 1499621 = 281179) (by norm_num)
theorem B1499645 : Blo 996598 1499645 := bbase (se 3 (by rfl) ⟨281183, by rfl⟩ : syracuseStep 1499645 = 562367) (by norm_num)
theorem B1499669 : Blo 996598 1499669 := bbase (se 6 (by rfl) ⟨35148, by rfl⟩ : syracuseStep 1499669 = 70297) (by norm_num)
theorem B1892909 : Blo 996598 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B1499693 : Blo 996598 1499693 := bbase (se 3 (by rfl) ⟨281192, by rfl⟩ : syracuseStep 1499693 = 562385) (by norm_num)
theorem B3367493 : Blo 996598 3367493 := bbase (se 4 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 3367493 = 631405) (by norm_num)
theorem B1499717 : Blo 996598 1499717 := bbase (se 4 (by rfl) ⟨140598, by rfl⟩ : syracuseStep 1499717 = 281197) (by norm_num)
theorem B1499741 : Blo 996598 1499741 := bbase (se 3 (by rfl) ⟨281201, by rfl⟩ : syracuseStep 1499741 = 562403) (by norm_num)
theorem B2843237 : Blo 996598 2843237 := bbase (se 4 (by rfl) ⟨266553, by rfl⟩ : syracuseStep 2843237 = 533107) (by norm_num)
theorem B1499765 : Blo 996598 1499765 := bbase (se 5 (by rfl) ⟨70301, by rfl⟩ : syracuseStep 1499765 = 140603) (by norm_num)
theorem B1499789 : Blo 996598 1499789 := bbase (se 3 (by rfl) ⟨281210, by rfl⟩ : syracuseStep 1499789 = 562421) (by norm_num)
theorem B1499813 : Blo 996598 1499813 := bbase (se 4 (by rfl) ⟨140607, by rfl⟩ : syracuseStep 1499813 = 281215) (by norm_num)
theorem B1499837 : Blo 996598 1499837 := bbase (se 3 (by rfl) ⟨281219, by rfl⟩ : syracuseStep 1499837 = 562439) (by norm_num)
theorem B1893061 : Blo 996598 1893061 := bbase (se 4 (by rfl) ⟨177474, by rfl⟩ : syracuseStep 1893061 = 354949) (by norm_num)
theorem B1499861 : Blo 996598 1499861 := bbase (se 7 (by rfl) ⟨17576, by rfl⟩ : syracuseStep 1499861 = 35153) (by norm_num)
theorem B1499885 : Blo 996598 1499885 := bbase (se 3 (by rfl) ⟨281228, by rfl⟩ : syracuseStep 1499885 = 562457) (by norm_num)
theorem B3597061 : Blo 996598 3597061 := bbase (se 4 (by rfl) ⟨337224, by rfl⟩ : syracuseStep 3597061 = 674449) (by norm_num)
theorem B1499909 : Blo 996598 1499909 := bbase (se 4 (by rfl) ⟨140616, by rfl⟩ : syracuseStep 1499909 = 281233) (by norm_num)
theorem B1499933 : Blo 996598 1499933 := bbase (se 3 (by rfl) ⟨281237, by rfl⟩ : syracuseStep 1499933 = 562475) (by norm_num)
theorem B1499957 : Blo 996598 1499957 := bbase (se 5 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 1499957 = 140621) (by norm_num)
theorem B1499981 : Blo 996598 1499981 := bbase (se 3 (by rfl) ⟨281246, by rfl⟩ : syracuseStep 1499981 = 562493) (by norm_num)
theorem B1500005 : Blo 996598 1500005 := bbase (se 4 (by rfl) ⟨140625, by rfl⟩ : syracuseStep 1500005 = 281251) (by norm_num)
theorem B1500029 : Blo 996598 1500029 := bbase (se 3 (by rfl) ⟨281255, by rfl⟩ : syracuseStep 1500029 = 562511) (by norm_num)
theorem B3597205 : Blo 996598 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B1500053 : Blo 996598 1500053 := bbase (se 6 (by rfl) ⟨35157, by rfl⟩ : syracuseStep 1500053 = 70315) (by norm_num)
theorem B1500077 : Blo 996598 1500077 := bbase (se 3 (by rfl) ⟨281264, by rfl⟩ : syracuseStep 1500077 = 562529) (by norm_num)
theorem B1500101 : Blo 996598 1500101 := bbase (se 4 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 1500101 = 281269) (by norm_num)
theorem B1500125 : Blo 996598 1500125 := bbase (se 3 (by rfl) ⟨281273, by rfl⟩ : syracuseStep 1500125 = 562547) (by norm_num)
theorem B1139689 : Blo 996598 1139689 := bbase (se 2 (by rfl) ⟨427383, by rfl⟩ : syracuseStep 1139689 = 854767) (by norm_num)
theorem B1893365 : Blo 996598 1893365 := bbase (se 5 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 1893365 = 177503) (by norm_num)
theorem B3367925 : Blo 996598 3367925 := bbase (se 5 (by rfl) ⟨157871, by rfl⟩ : syracuseStep 3367925 = 315743) (by norm_num)
theorem B1500149 : Blo 996598 1500149 := bbase (se 5 (by rfl) ⟨70319, by rfl⟩ : syracuseStep 1500149 = 140639) (by norm_num)
theorem B1500173 : Blo 996598 1500173 := bbase (se 3 (by rfl) ⟨281282, by rfl⟩ : syracuseStep 1500173 = 562565) (by norm_num)
theorem B1139729 : Blo 996598 1139729 := bbase (se 2 (by rfl) ⟨427398, by rfl⟩ : syracuseStep 1139729 = 854797) (by norm_num)
theorem B1598501 : Blo 996598 1598501 := bbase (se 4 (by rfl) ⟨149859, by rfl⟩ : syracuseStep 1598501 = 299719) (by norm_num)
theorem B1500197 : Blo 996598 1500197 := bbase (se 4 (by rfl) ⟨140643, by rfl⟩ : syracuseStep 1500197 = 281287) (by norm_num)
theorem B3597365 : Blo 996598 3597365 := bbase (se 5 (by rfl) ⟨168626, by rfl⟩ : syracuseStep 3597365 = 337253) (by norm_num)
theorem B1500221 : Blo 996598 1500221 := bbase (se 3 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 1500221 = 562583) (by norm_num)
theorem B1500245 : Blo 996598 1500245 := bbase (se 8 (by rfl) ⟨8790, by rfl⟩ : syracuseStep 1500245 = 17581) (by norm_num)
theorem B1500269 : Blo 996598 1500269 := bbase (se 3 (by rfl) ⟨281300, by rfl⟩ : syracuseStep 1500269 = 562601) (by norm_num)
theorem B1500293 : Blo 996598 1500293 := bbase (se 4 (by rfl) ⟨140652, by rfl⟩ : syracuseStep 1500293 = 281305) (by norm_num)
theorem B1500317 : Blo 996598 1500317 := bbase (se 3 (by rfl) ⟨281309, by rfl⟩ : syracuseStep 1500317 = 562619) (by norm_num)
theorem B3597493 : Blo 996598 3597493 := bbase (se 5 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 3597493 = 337265) (by norm_num)
theorem B1500341 : Blo 996598 1500341 := bbase (se 5 (by rfl) ⟨70328, by rfl⟩ : syracuseStep 1500341 = 140657) (by norm_num)
theorem B1500365 : Blo 996598 1500365 := bbase (se 3 (by rfl) ⟨281318, by rfl⟩ : syracuseStep 1500365 = 562637) (by norm_num)
theorem B1500389 : Blo 996598 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B2024693 : Blo 996598 2024693 := bbase (se 5 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 2024693 = 189815) (by norm_num)
theorem B1500413 : Blo 996598 1500413 := bbase (se 3 (by rfl) ⟨281327, by rfl⟩ : syracuseStep 1500413 = 562655) (by norm_num)
theorem B1500437 : Blo 996598 1500437 := bbase (se 6 (by rfl) ⟨35166, by rfl⟩ : syracuseStep 1500437 = 70333) (by norm_num)
theorem B1500461 : Blo 996598 1500461 := bbase (se 3 (by rfl) ⟨281336, by rfl⟩ : syracuseStep 1500461 = 562673) (by norm_num)
theorem B1500485 : Blo 996598 1500485 := bbase (se 4 (by rfl) ⟨140670, by rfl⟩ : syracuseStep 1500485 = 281341) (by norm_num)
theorem B1500509 : Blo 996598 1500509 := bbase (se 3 (by rfl) ⟨281345, by rfl⟩ : syracuseStep 1500509 = 562691) (by norm_num)
theorem B1500533 : Blo 996598 1500533 := bbase (se 5 (by rfl) ⟨70337, by rfl⟩ : syracuseStep 1500533 = 140675) (by norm_num)
theorem B3794309 : Blo 996598 3794309 := bbase (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) (by norm_num)
theorem B1500557 : Blo 996598 1500557 := bbase (se 3 (by rfl) ⟨281354, by rfl⟩ : syracuseStep 1500557 = 562709) (by norm_num)
theorem B3368357 : Blo 996598 3368357 := bbase (se 4 (by rfl) ⟨315783, by rfl⟩ : syracuseStep 3368357 = 631567) (by norm_num)
theorem B1500581 : Blo 996598 1500581 := bbase (se 4 (by rfl) ⟨140679, by rfl⟩ : syracuseStep 1500581 = 281359) (by norm_num)
theorem B1500605 : Blo 996598 1500605 := bbase (se 3 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 1500605 = 562727) (by norm_num)
theorem B1500629 : Blo 996598 1500629 := bbase (se 7 (by rfl) ⟨17585, by rfl⟩ : syracuseStep 1500629 = 35171) (by norm_num)
theorem B1500653 : Blo 996598 1500653 := bbase (se 3 (by rfl) ⟨281372, by rfl⟩ : syracuseStep 1500653 = 562745) (by norm_num)
theorem B1500677 : Blo 996598 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B1500701 : Blo 996598 1500701 := bbase (se 3 (by rfl) ⟨281381, by rfl⟩ : syracuseStep 1500701 = 562763) (by norm_num)
theorem B1500725 : Blo 996598 1500725 := bbase (se 5 (by rfl) ⟨70346, by rfl⟩ : syracuseStep 1500725 = 140693) (by norm_num)
theorem B1500749 : Blo 996598 1500749 := bbase (se 3 (by rfl) ⟨281390, by rfl⟩ : syracuseStep 1500749 = 562781) (by norm_num)
theorem B1500773 : Blo 996598 1500773 := bbase (se 4 (by rfl) ⟨140697, by rfl⟩ : syracuseStep 1500773 = 281395) (by norm_num)
theorem B1500797 : Blo 996598 1500797 := bbase (se 3 (by rfl) ⟨281399, by rfl⟩ : syracuseStep 1500797 = 562799) (by norm_num)
theorem B19195541 : Blo 996598 19195541 := bbase (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) (by norm_num)
theorem B1500821 : Blo 996598 1500821 := bbase (se 6 (by rfl) ⟨35175, by rfl⟩ : syracuseStep 1500821 = 70351) (by norm_num)
theorem B3794597 : Blo 996598 3794597 := bbase (se 4 (by rfl) ⟨355743, by rfl⟩ : syracuseStep 3794597 = 711487) (by norm_num)
theorem B1500845 : Blo 996598 1500845 := bbase (se 3 (by rfl) ⟨281408, by rfl⟩ : syracuseStep 1500845 = 562817) (by norm_num)
theorem B1500869 : Blo 996598 1500869 := bbase (se 4 (by rfl) ⟨140706, by rfl⟩ : syracuseStep 1500869 = 281413) (by norm_num)
theorem B1500893 : Blo 996598 1500893 := bbase (se 3 (by rfl) ⟨281417, by rfl⟩ : syracuseStep 1500893 = 562835) (by norm_num)
theorem B1894117 : Blo 996598 1894117 := bbase (se 4 (by rfl) ⟨177573, by rfl⟩ : syracuseStep 1894117 = 355147) (by norm_num)
theorem B3368789 : Blo 996598 3368789 := bbase (se 9 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 3368789 = 19739) (by norm_num)
theorem B1894261 : Blo 996598 1894261 := bbase (se 5 (by rfl) ⟨88793, by rfl⟩ : syracuseStep 1894261 = 177587) (by norm_num)
theorem B1894421 : Blo 996598 1894421 := bbase (se 6 (by rfl) ⟨44400, by rfl⟩ : syracuseStep 1894421 = 88801) (by norm_num)
theorem B5695541 : Blo 996598 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B2844821 : Blo 996598 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B4548773 : Blo 996598 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B1894565 : Blo 996598 1894565 := bbase (se 4 (by rfl) ⟨177615, by rfl⟩ : syracuseStep 1894565 = 355231) (by norm_num)
theorem B3369221 : Blo 996598 3369221 := bbase (se 4 (by rfl) ⟨315864, by rfl⟩ : syracuseStep 3369221 = 631729) (by norm_num)
theorem B3467669 : Blo 996598 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B1894853 : Blo 996598 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B1600013 : Blo 996598 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B1895005 : Blo 996598 1895005 := bbase (se 3 (by rfl) ⟨355313, by rfl⟩ : syracuseStep 1895005 = 710627) (by norm_num)
theorem B3369653 : Blo 996598 3369653 := bbase (se 5 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 3369653 = 315905) (by norm_num)
theorem B19163861 : Blo 996598 19163861 := bbase (se 7 (by rfl) ⟨224576, by rfl⟩ : syracuseStep 19163861 = 449153) (by norm_num)
theorem B2845493 : Blo 996598 2845493 := bbase (se 5 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 2845493 = 266765) (by norm_num)
theorem B3795781 : Blo 996598 3795781 := bbase (se 4 (by rfl) ⟨355854, by rfl⟩ : syracuseStep 3795781 = 711709) (by norm_num)
theorem B1895309 : Blo 996598 1895309 := bbase (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) (by norm_num)
theorem B1600469 : Blo 996598 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B3075077 : Blo 996598 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B3370085 : Blo 996598 3370085 := bbase (se 4 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 3370085 = 631891) (by norm_num)
theorem B3796085 : Blo 996598 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B1141933 : Blo 996598 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B2845925 : Blo 996598 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1010981 : Blo 996598 1010981 := bbase (se 4 (by rfl) ⟨94779, by rfl⟩ : syracuseStep 1010981 = 189559) (by norm_num)
theorem B2026957 : Blo 996598 2026957 := bbase (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) (by norm_num)
theorem B3370517 : Blo 996598 3370517 := bbase (se 6 (by rfl) ⟨78996, by rfl⟩ : syracuseStep 3370517 = 157993) (by norm_num)
theorem B1797709 : Blo 996598 1797709 := bbase (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) (by norm_num)
theorem B2027125 : Blo 996598 2027125 := bbase (se 5 (by rfl) ⟨95021, by rfl⟩ : syracuseStep 2027125 = 190043) (by norm_num)
theorem B1896061 : Blo 996598 1896061 := bbase (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) (by norm_num)
theorem B1011349 : Blo 996598 1011349 := bbase (se 6 (by rfl) ⟨23703, by rfl⟩ : syracuseStep 1011349 = 47407) (by norm_num)
theorem B1896205 : Blo 996598 1896205 := bbase (se 3 (by rfl) ⟨355538, by rfl⟩ : syracuseStep 1896205 = 711077) (by norm_num)
theorem B9596693 : Blo 996598 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B6385493 : Blo 996598 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B1797997 : Blo 996598 1797997 := bbase (se 3 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 1797997 = 674249) (by norm_num)
theorem B1896365 : Blo 996598 1896365 := bbase (se 3 (by rfl) ⟨355568, by rfl⟩ : syracuseStep 1896365 = 711137) (by norm_num)
theorem B1601461 : Blo 996598 1601461 := bbase (se 5 (by rfl) ⟨75068, by rfl⟩ : syracuseStep 1601461 = 150137) (by norm_num)
theorem B3370949 : Blo 996598 3370949 := bbase (se 4 (by rfl) ⟨316026, by rfl⟩ : syracuseStep 3370949 = 632053) (by norm_num)
theorem B2846677 : Blo 996598 2846677 := bbase (se 7 (by rfl) ⟨33359, by rfl⟩ : syracuseStep 2846677 = 66719) (by norm_num)
theorem B1896509 : Blo 996598 1896509 := bbase (se 3 (by rfl) ⟨355595, by rfl⟩ : syracuseStep 1896509 = 711191) (by norm_num)
theorem B1896797 : Blo 996598 1896797 := bbase (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) (by norm_num)
theorem B3371381 : Blo 996598 3371381 := bbase (se 5 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 3371381 = 316067) (by norm_num)
theorem B1798573 : Blo 996598 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B1896949 : Blo 996598 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B1602109 : Blo 996598 1602109 := bbase (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) (by norm_num)
theorem B3371813 : Blo 996598 3371813 := bbase (se 4 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 3371813 = 632215) (by norm_num)
theorem B1897253 : Blo 996598 1897253 := bbase (se 4 (by rfl) ⟨177867, by rfl⟩ : syracuseStep 1897253 = 355735) (by norm_num)
theorem B3240805 : Blo 996598 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B1799093 : Blo 996598 1799093 := bbase (se 5 (by rfl) ⟨84332, by rfl⟩ : syracuseStep 1799093 = 168665) (by norm_num)
theorem B1438661 : Blo 996598 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B1537165 : Blo 996598 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B3798197 : Blo 996598 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B4256981 : Blo 996598 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B3372245 : Blo 996598 3372245 := bbase (se 7 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 3372245 = 79037) (by norm_num)
theorem B1799453 : Blo 996598 1799453 := bbase (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) (by norm_num)
theorem B1799605 : Blo 996598 1799605 := bbase (se 5 (by rfl) ⟨84356, by rfl⟩ : syracuseStep 1799605 = 168713) (by norm_num)
theorem B3798485 : Blo 996598 3798485 := bbase (se 7 (by rfl) ⟨44513, by rfl⟩ : syracuseStep 3798485 = 89027) (by norm_num)
theorem B4257269 : Blo 996598 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B1898005 : Blo 996598 1898005 := bbase (se 6 (by rfl) ⟨44484, by rfl⟩ : syracuseStep 1898005 = 88969) (by norm_num)
theorem B1078849 : Blo 996598 1078849 := bbase (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) (by norm_num)
theorem B8648309 : Blo 996598 8648309 := bbase (se 5 (by rfl) ⟨405389, by rfl⟩ : syracuseStep 8648309 = 810779) (by norm_num)
theorem B3372677 : Blo 996598 3372677 := bbase (se 4 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 3372677 = 632377) (by norm_num)
theorem B1898149 : Blo 996598 1898149 := bbase (se 4 (by rfl) ⟨177951, by rfl⟩ : syracuseStep 1898149 = 355903) (by norm_num)
theorem B1898309 : Blo 996598 1898309 := bbase (se 4 (by rfl) ⟨177966, by rfl⟩ : syracuseStep 1898309 = 355933) (by norm_num)
theorem B2160589 : Blo 996598 2160589 := bbase (se 3 (by rfl) ⟨405110, by rfl⟩ : syracuseStep 2160589 = 810221) (by norm_num)
theorem B1898453 : Blo 996598 1898453 := bbase (se 7 (by rfl) ⟨22247, by rfl⟩ : syracuseStep 1898453 = 44495) (by norm_num)
theorem B3373109 : Blo 996598 3373109 := bbase (se 5 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 3373109 = 316229) (by norm_num)
theorem B4258021 : Blo 996598 4258021 := bbase (se 4 (by rfl) ⟨399189, by rfl⟩ : syracuseStep 4258021 = 798379) (by norm_num)
theorem B8091893 : Blo 996598 8091893 := bbase (se 5 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 8091893 = 758615) (by norm_num)
theorem B1898741 : Blo 996598 1898741 := bbase (se 5 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 1898741 = 178007) (by norm_num)
theorem B1898893 : Blo 996598 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B3373541 : Blo 996598 3373541 := bbase (se 4 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 3373541 = 632539) (by norm_num)
theorem B1800701 : Blo 996598 1800701 := bbase (se 3 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 1800701 = 675263) (by norm_num)
theorem B8518229 : Blo 996598 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B1899197 : Blo 996598 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B3078869 : Blo 996598 3078869 := bbase (se 7 (by rfl) ⟨36080, by rfl⟩ : syracuseStep 3078869 = 72161) (by norm_num)
theorem B6388469 : Blo 996598 6388469 := bbase (se 5 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 6388469 = 598919) (by norm_num)
theorem B3373973 : Blo 996598 3373973 := bbase (se 6 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 3373973 = 158155) (by norm_num)
theorem B4258757 : Blo 996598 4258757 := bbase (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) (by norm_num)
theorem B7699637 : Blo 996598 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B3374405 : Blo 996598 3374405 := bbase (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) (by norm_num)
theorem B1539533 : Blo 996598 1539533 := bbase (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) (by norm_num)
theorem B4554245 : Blo 996598 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B5045813 : Blo 996598 5045813 := bbase (se 5 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 5045813 = 473045) (by norm_num)
theorem B13663829 : Blo 996598 13663829 := bbase (se 8 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 13663829 = 160123) (by norm_num)
theorem B2522765 : Blo 996598 2522765 := bbase (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) (by norm_num)
theorem B3374837 : Blo 996598 3374837 := bbase (se 5 (by rfl) ⟨158195, by rfl⟩ : syracuseStep 3374837 = 316391) (by norm_num)
theorem B2129789 : Blo 996598 2129789 := bbase (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) (by norm_num)
theorem B20742101 : Blo 996598 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B2523109 : Blo 996598 2523109 := bbase (se 4 (by rfl) ⟨236541, by rfl⟩ : syracuseStep 2523109 = 473083) (by norm_num)
theorem B3375107 : Blo 996598 3375107 := bstep (se 1 (by rfl) ⟨2531330, by rfl⟩ : syracuseStep 3375107 = 5062661) B5062661
theorem B13664483 : Blo 996598 13664483 := bstep (se 1 (by rfl) ⟨10248362, by rfl⟩ : syracuseStep 13664483 = 20496725) B20496725
theorem B3375377 : Blo 996598 3375377 := bstep (se 2 (by rfl) ⟨1265766, by rfl⟩ : syracuseStep 3375377 = 2531533) B2531533
theorem B8520005 : Blo 996598 8520005 := bstep (se 4 (by rfl) ⟨798750, by rfl⟩ : syracuseStep 8520005 = 1597501) B1597501
theorem B2130275 : Blo 996598 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B6062597 : Blo 996598 6062597 := bstep (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) B1136737
theorem B12812813 : Blo 996598 12812813 := bstep (se 3 (by rfl) ⟨2402402, by rfl⟩ : syracuseStep 12812813 = 4804805) B4804805
theorem B5046947 : Blo 996598 5046947 := bstep (se 1 (by rfl) ⟨3785210, by rfl⟩ : syracuseStep 5046947 = 7570421) B7570421
theorem B6062789 : Blo 996598 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B3605219 : Blo 996598 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B3375917 : Blo 996598 3375917 := bstep (se 3 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 3375917 = 1265969) B1265969
theorem B3375971 : Blo 996598 3375971 := bstep (se 1 (by rfl) ⟨2531978, by rfl⟩ : syracuseStep 3375971 = 5063957) B5063957
theorem B4260721 : Blo 996598 4260721 := bstep (se 2 (by rfl) ⟨1597770, by rfl⟩ : syracuseStep 4260721 = 3195541) B3195541
theorem B2524081 : Blo 996598 2524081 := bstep (se 2 (by rfl) ⟨946530, by rfl⟩ : syracuseStep 2524081 = 1893061) B1893061
theorem B3376241 : Blo 996598 3376241 := bstep (se 2 (by rfl) ⟨1266090, by rfl⟩ : syracuseStep 3376241 = 2532181) B2532181
theorem B2524355 : Blo 996598 2524355 := bstep (se 1 (by rfl) ⟨1893266, by rfl⟩ : syracuseStep 2524355 = 3786533) B3786533
theorem B27329845 : Blo 996598 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B2524547 : Blo 996598 2524547 := bstep (se 1 (by rfl) ⟨1893410, by rfl⟩ : syracuseStep 2524547 = 3786821) B3786821
theorem B5047757 : Blo 996598 5047757 := bstep (se 3 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 5047757 = 1892909) B1892909
theorem B3376781 : Blo 996598 3376781 := bstep (se 3 (by rfl) ⟨633146, by rfl⟩ : syracuseStep 3376781 = 1266293) B1266293
theorem B3376835 : Blo 996598 3376835 := bstep (se 1 (by rfl) ⟨2532626, by rfl⟩ : syracuseStep 3376835 = 5065253) B5065253
theorem B6391493 : Blo 996598 6391493 := bstep (se 4 (by rfl) ⟨599202, by rfl⟩ : syracuseStep 6391493 = 1198405) B1198405
theorem B12814133 : Blo 996598 12814133 := bstep (se 5 (by rfl) ⟨600662, by rfl⟩ : syracuseStep 12814133 = 1201325) B1201325
theorem B2525489 : Blo 996598 2525489 := bstep (se 2 (by rfl) ⟨947058, by rfl⟩ : syracuseStep 2525489 = 1894117) B1894117
theorem B2132291 : Blo 996598 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B2525539 : Blo 996598 2525539 := bstep (se 1 (by rfl) ⟨1894154, by rfl⟩ : syracuseStep 2525539 = 3788309) B3788309
theorem B6064517 : Blo 996598 6064517 := bstep (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) B1137097
theorem B46139789 : Blo 996598 46139789 := bstep (se 3 (by rfl) ⟨8651210, by rfl⟩ : syracuseStep 46139789 = 17302421) B17302421
theorem B2525681 : Blo 996598 2525681 := bstep (se 2 (by rfl) ⟨947130, by rfl⟩ : syracuseStep 2525681 = 1894261) B1894261
theorem B3836429 : Blo 996598 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B4262669 : Blo 996598 4262669 := bstep (se 3 (by rfl) ⟨799250, by rfl⟩ : syracuseStep 4262669 = 1598501) B1598501
theorem B12487493 : Blo 996598 12487493 := bstep (se 4 (by rfl) ⟨1170702, by rfl⟩ : syracuseStep 12487493 = 2341405) B2341405
theorem B7572365 : Blo 996598 7572365 := bstep (se 3 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 7572365 = 2839637) B2839637
theorem B2526673 : Blo 996598 2526673 := bstep (se 2 (by rfl) ⟨947502, by rfl⟩ : syracuseStep 2526673 = 1895005) B1895005
theorem B2526947 : Blo 996598 2526947 := bstep (se 1 (by rfl) ⟨1895210, by rfl⟩ : syracuseStep 2526947 = 3790421) B3790421
theorem B2527139 : Blo 996598 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B2134307 : Blo 996598 2134307 := bstep (se 1 (by rfl) ⟨1600730, by rfl⟩ : syracuseStep 2134307 = 3201461) B3201461
theorem B5050673 : Blo 996598 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2396483 : Blo 996598 2396483 := bstep (se 1 (by rfl) ⟨1797362, by rfl⟩ : syracuseStep 2396483 = 3594725) B3594725
theorem B2920835 : Blo 996598 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B1708499 : Blo 996598 1708499 := bstep (se 1 (by rfl) ⟨1281374, by rfl⟩ : syracuseStep 1708499 = 2562749) B2562749
theorem B2888173 : Blo 996598 2888173 := bstep (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) B1083065
theorem B2396675 : Blo 996598 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B4559537 : Blo 996598 4559537 := bstep (se 2 (by rfl) ⟨1709826, by rfl⟩ : syracuseStep 4559537 = 3419653) B3419653
theorem B2396945 : Blo 996598 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B2528081 : Blo 996598 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B2528131 : Blo 996598 2528131 := bstep (se 1 (by rfl) ⟨1896098, by rfl⟩ : syracuseStep 2528131 = 3792197) B3792197
theorem B11539381 : Blo 996598 11539381 := bstep (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) B1081817
theorem B2528273 : Blo 996598 2528273 := bstep (se 2 (by rfl) ⟨948102, by rfl⟩ : syracuseStep 2528273 = 1896205) B1896205
theorem B1709075 : Blo 996598 1709075 := bstep (se 1 (by rfl) ⟨1281806, by rfl⟩ : syracuseStep 1709075 = 2563613) B2563613
theorem B2397329 : Blo 996598 2397329 := bstep (se 2 (by rfl) ⟨898998, by rfl⟩ : syracuseStep 2397329 = 1797997) B1797997
theorem B2135555 : Blo 996598 2135555 := bstep (se 1 (by rfl) ⟨1601666, by rfl⟩ : syracuseStep 2135555 = 3203333) B3203333
theorem B5052131 : Blo 996598 5052131 := bstep (se 1 (by rfl) ⟨3789098, by rfl⟩ : syracuseStep 5052131 = 7578197) B7578197
theorem B7575281 : Blo 996598 7575281 := bstep (se 2 (by rfl) ⟨2840730, by rfl⟩ : syracuseStep 7575281 = 5681461) B5681461
theorem B1709923 : Blo 996598 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B2398097 : Blo 996598 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B2529265 : Blo 996598 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B2398243 : Blo 996598 2398243 := bstep (se 1 (by rfl) ⟨1798682, by rfl⟩ : syracuseStep 2398243 = 3597365) B3597365
theorem B8198213 : Blo 996598 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B2136145 : Blo 996598 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B1349795 : Blo 996598 1349795 := bstep (se 1 (by rfl) ⟨1012346, by rfl⟩ : syracuseStep 1349795 = 2024693) B2024693
theorem B2529539 : Blo 996598 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B9247117 : Blo 996598 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B2529731 : Blo 996598 2529731 := bstep (se 1 (by rfl) ⟨1897298, by rfl⟩ : syracuseStep 2529731 = 3794597) B3794597
theorem B5052941 : Blo 996598 5052941 := bstep (se 3 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 5052941 = 1894853) B1894853
theorem B4266701 : Blo 996598 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B1121251 : Blo 996598 1121251 := bstep (se 1 (by rfl) ⟨840938, by rfl⟩ : syracuseStep 1121251 = 1681877) B1681877
theorem B4267043 : Blo 996598 4267043 := bstep (se 1 (by rfl) ⟨3200282, by rfl⟩ : syracuseStep 4267043 = 6400565) B6400565
theorem B1645667 : Blo 996598 1645667 := bstep (se 1 (by rfl) ⟨1234250, by rfl⟩ : syracuseStep 1645667 = 2468501) B2468501
theorem B1121395 : Blo 996598 1121395 := bstep (se 1 (by rfl) ⟨841046, by rfl⟩ : syracuseStep 1121395 = 1682093) B1682093
theorem B2399473 : Blo 996598 2399473 := bstep (se 2 (by rfl) ⟨899802, by rfl⟩ : syracuseStep 2399473 = 1799605) B1799605
theorem B1121539 : Blo 996598 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B2530673 : Blo 996598 2530673 := bstep (se 2 (by rfl) ⟨949002, by rfl⟩ : syracuseStep 2530673 = 1898005) B1898005
theorem B1121683 : Blo 996598 1121683 := bstep (se 1 (by rfl) ⟨841262, by rfl⟩ : syracuseStep 1121683 = 1682525) B1682525
theorem B2530723 : Blo 996598 2530723 := bstep (se 1 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 2530723 = 3796085) B3796085
theorem B4267505 : Blo 996598 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B7183885 : Blo 996598 7183885 := bstep (se 3 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 7183885 = 2693957) B2693957
theorem B1121827 : Blo 996598 1121827 := bstep (se 1 (by rfl) ⟨841370, by rfl⟩ : syracuseStep 1121827 = 1682741) B1682741
theorem B2530865 : Blo 996598 2530865 := bstep (se 2 (by rfl) ⟨949074, by rfl⟩ : syracuseStep 2530865 = 1898149) B1898149
theorem B1121971 : Blo 996598 1121971 := bstep (se 1 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 1121971 = 1682957) B1682957
theorem B5119793 : Blo 996598 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B1122115 : Blo 996598 1122115 := bstep (se 1 (by rfl) ⟨841586, by rfl⟩ : syracuseStep 1122115 = 1683173) B1683173
theorem B6397795 : Blo 996598 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B1122259 : Blo 996598 1122259 := bstep (se 1 (by rfl) ⟨841694, by rfl⟩ : syracuseStep 1122259 = 1683389) B1683389
theorem B1122403 : Blo 996598 1122403 := bstep (se 1 (by rfl) ⟨841802, by rfl⟩ : syracuseStep 1122403 = 1683605) B1683605
theorem B5480561 : Blo 996598 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B6070477 : Blo 996598 6070477 := bstep (se 3 (by rfl) ⟨1138214, by rfl⟩ : syracuseStep 6070477 = 2276429) B2276429
theorem B1122547 : Blo 996598 1122547 := bstep (se 1 (by rfl) ⟨841910, by rfl⟩ : syracuseStep 1122547 = 1683821) B1683821
theorem B5677361 : Blo 996598 5677361 := bstep (se 2 (by rfl) ⟨2129010, by rfl⟩ : syracuseStep 5677361 = 4258021) B4258021
theorem B1122691 : Blo 996598 1122691 := bstep (se 1 (by rfl) ⟨842018, by rfl⟩ : syracuseStep 1122691 = 1684037) B1684037
theorem B2531857 : Blo 996598 2531857 := bstep (se 2 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 2531857 = 1898893) B1898893
theorem B1122835 : Blo 996598 1122835 := bstep (se 1 (by rfl) ⟨842126, by rfl⟩ : syracuseStep 1122835 = 1684253) B1684253
theorem B4563569 : Blo 996598 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B1122979 : Blo 996598 1122979 := bstep (se 1 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 1122979 = 1684469) B1684469
theorem B2368259 : Blo 996598 2368259 := bstep (se 1 (by rfl) ⟨1776194, by rfl⟩ : syracuseStep 2368259 = 3552389) B3552389
theorem B2695949 : Blo 996598 2695949 := bstep (se 3 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 2695949 = 1010981) B1010981
theorem B2532131 : Blo 996598 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B1123123 : Blo 996598 1123123 := bstep (se 1 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 1123123 = 1684685) B1684685
theorem B6824773 : Blo 996598 6824773 := bstep (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) B1279645
theorem B6398797 : Blo 996598 6398797 := bstep (se 3 (by rfl) ⟨1199774, by rfl⟩ : syracuseStep 6398797 = 2399549) B2399549
theorem B8528753 : Blo 996598 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B1123267 : Blo 996598 1123267 := bstep (se 1 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 1123267 = 1684901) B1684901
theorem B4858829 : Blo 996598 4858829 := bstep (se 3 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 4858829 = 1822061) B1822061
theorem B2532323 : Blo 996598 2532323 := bstep (se 1 (by rfl) ⟨1899242, by rfl⟩ : syracuseStep 2532323 = 3798485) B3798485
theorem B1123411 : Blo 996598 1123411 := bstep (se 1 (by rfl) ⟨842558, by rfl⟩ : syracuseStep 1123411 = 1685117) B1685117
theorem B4105421 : Blo 996598 4105421 := bstep (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) B1539533
theorem B1123555 : Blo 996598 1123555 := bstep (se 1 (by rfl) ⟨842666, by rfl⟩ : syracuseStep 1123555 = 1685333) B1685333
theorem B1516865 : Blo 996598 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B5055857 : Blo 996598 5055857 := bstep (se 2 (by rfl) ⟨1895946, by rfl⟩ : syracuseStep 5055857 = 3791893) B3791893
theorem B1123699 : Blo 996598 1123699 := bstep (se 1 (by rfl) ⟨842774, by rfl⟩ : syracuseStep 1123699 = 1685549) B1685549
theorem B1516963 : Blo 996598 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B1123843 : Blo 996598 1123843 := bstep (se 1 (by rfl) ⟨842882, by rfl⟩ : syracuseStep 1123843 = 1685765) B1685765
theorem B1123987 : Blo 996598 1123987 := bstep (se 1 (by rfl) ⟨842990, by rfl⟩ : syracuseStep 1123987 = 1685981) B1685981
theorem B5678819 : Blo 996598 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B1124131 : Blo 996598 1124131 := bstep (se 1 (by rfl) ⟨843098, by rfl⟩ : syracuseStep 1124131 = 1686197) B1686197
theorem B1124275 : Blo 996598 1124275 := bstep (se 1 (by rfl) ⟨843206, by rfl⟩ : syracuseStep 1124275 = 1686413) B1686413
theorem B9119729 : Blo 996598 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B1419329 : Blo 996598 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B1124419 : Blo 996598 1124419 := bstep (se 1 (by rfl) ⟨843314, by rfl⟩ : syracuseStep 1124419 = 1686629) B1686629
theorem B10791053 : Blo 996598 10791053 := bstep (se 3 (by rfl) ⟨2023322, by rfl⟩ : syracuseStep 10791053 = 4046645) B4046645
theorem B1124563 : Blo 996598 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B1124707 : Blo 996598 1124707 := bstep (se 1 (by rfl) ⟨843530, by rfl⟩ : syracuseStep 1124707 = 1687061) B1687061
theorem B1681843 : Blo 996598 1681843 := bstep (se 1 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 1681843 = 2522765) B2522765
theorem B1124851 : Blo 996598 1124851 := bstep (se 1 (by rfl) ⟨843638, by rfl⟩ : syracuseStep 1124851 = 1687277) B1687277
theorem B1681985 : Blo 996598 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B1419859 : Blo 996598 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B1124995 : Blo 996598 1124995 := bstep (se 1 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 1124995 = 1687493) B1687493
theorem B1682113 : Blo 996598 1682113 := bstep (se 2 (by rfl) ⟨630792, by rfl⟩ : syracuseStep 1682113 = 1261585) B1261585
theorem B5679821 : Blo 996598 5679821 := bstep (se 3 (by rfl) ⟨1064966, by rfl⟩ : syracuseStep 5679821 = 2129933) B2129933
theorem B1682147 : Blo 996598 1682147 := bstep (se 1 (by rfl) ⟨1261610, by rfl⟩ : syracuseStep 1682147 = 2523221) B2523221
theorem B1125139 : Blo 996598 1125139 := bstep (se 1 (by rfl) ⟨843854, by rfl⟩ : syracuseStep 1125139 = 1687709) B1687709
theorem B5057315 : Blo 996598 5057315 := bstep (se 1 (by rfl) ⟨3792986, by rfl⟩ : syracuseStep 5057315 = 7585973) B7585973
theorem B1682275 : Blo 996598 1682275 := bstep (se 1 (by rfl) ⟨1261706, by rfl⟩ : syracuseStep 1682275 = 2523413) B2523413
theorem B21900145 : Blo 996598 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B12790669 : Blo 996598 12790669 := bstep (se 3 (by rfl) ⟨2398250, by rfl⟩ : syracuseStep 12790669 = 4796501) B4796501
theorem B1420195 : Blo 996598 1420195 := bstep (se 1 (by rfl) ⟨1065146, by rfl⟩ : syracuseStep 1420195 = 2130293) B2130293
theorem B1125283 : Blo 996598 1125283 := bstep (se 1 (by rfl) ⟨843962, by rfl⟩ : syracuseStep 1125283 = 1687925) B1687925
theorem B4271075 : Blo 996598 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B1682417 : Blo 996598 1682417 := bstep (se 2 (by rfl) ⟨630906, by rfl⟩ : syracuseStep 1682417 = 1261813) B1261813
theorem B1125427 : Blo 996598 1125427 := bstep (se 1 (by rfl) ⟨844070, by rfl⟩ : syracuseStep 1125427 = 1688141) B1688141
theorem B2403395 : Blo 996598 2403395 := bstep (se 1 (by rfl) ⟨1802546, by rfl⟩ : syracuseStep 2403395 = 3605093) B3605093
theorem B1682545 : Blo 996598 1682545 := bstep (se 2 (by rfl) ⟨630954, by rfl⟩ : syracuseStep 1682545 = 1261909) B1261909
theorem B1682579 : Blo 996598 1682579 := bstep (se 1 (by rfl) ⟨1261934, by rfl⟩ : syracuseStep 1682579 = 2523869) B2523869
theorem B1125571 : Blo 996598 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B1682707 : Blo 996598 1682707 := bstep (se 1 (by rfl) ⟨1262030, by rfl⟩ : syracuseStep 1682707 = 2524061) B2524061
theorem B9612685 : Blo 996598 9612685 := bstep (se 3 (by rfl) ⟨1802378, by rfl⟩ : syracuseStep 9612685 = 3604757) B3604757
theorem B1682849 : Blo 996598 1682849 := bstep (se 2 (by rfl) ⟨631068, by rfl⟩ : syracuseStep 1682849 = 1262137) B1262137
theorem B4795811 : Blo 996598 4795811 := bstep (se 1 (by rfl) ⟨3596858, by rfl⟩ : syracuseStep 4795811 = 7193717) B7193717
theorem B1420753 : Blo 996598 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B1420787 : Blo 996598 1420787 := bstep (se 1 (by rfl) ⟨1065590, by rfl⟩ : syracuseStep 1420787 = 2131181) B2131181
theorem B1682977 : Blo 996598 1682977 := bstep (se 2 (by rfl) ⟨631116, by rfl⟩ : syracuseStep 1682977 = 1262233) B1262233
theorem B1683011 : Blo 996598 1683011 := bstep (se 1 (by rfl) ⟨1262258, by rfl⟩ : syracuseStep 1683011 = 2524517) B2524517
theorem B5058125 : Blo 996598 5058125 := bstep (se 3 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 5058125 = 1896797) B1896797
theorem B4796081 : Blo 996598 4796081 := bstep (se 2 (by rfl) ⟨1798530, by rfl⟩ : syracuseStep 4796081 = 3597061) B3597061
theorem B1683139 : Blo 996598 1683139 := bstep (se 1 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 1683139 = 2524709) B2524709
theorem B1683281 : Blo 996598 1683281 := bstep (se 2 (by rfl) ⟨631230, by rfl⟩ : syracuseStep 1683281 = 1262461) B1262461
theorem B4796273 : Blo 996598 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B1683409 : Blo 996598 1683409 := bstep (se 2 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 1683409 = 1262557) B1262557
theorem B1683443 : Blo 996598 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B1421345 : Blo 996598 1421345 := bstep (se 2 (by rfl) ⟨533004, by rfl⟩ : syracuseStep 1421345 = 1066009) B1066009
theorem B4042801 : Blo 996598 4042801 := bstep (se 2 (by rfl) ⟨1516050, by rfl⟩ : syracuseStep 4042801 = 3032101) B3032101
theorem B1421425 : Blo 996598 1421425 := bstep (se 2 (by rfl) ⟨533034, by rfl⟩ : syracuseStep 1421425 = 1066069) B1066069
theorem B1683571 : Blo 996598 1683571 := bstep (se 1 (by rfl) ⟨1262678, by rfl⟩ : syracuseStep 1683571 = 2525357) B2525357
theorem B12792005 : Blo 996598 12792005 := bstep (se 4 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 12792005 = 2398501) B2398501
theorem B4796657 : Blo 996598 4796657 := bstep (se 2 (by rfl) ⟨1798746, by rfl⟩ : syracuseStep 4796657 = 3597493) B3597493
theorem B1683713 : Blo 996598 1683713 := bstep (se 2 (by rfl) ⟨631392, by rfl⟩ : syracuseStep 1683713 = 1262785) B1262785
theorem B1683841 : Blo 996598 1683841 := bstep (se 2 (by rfl) ⟨631440, by rfl⟩ : syracuseStep 1683841 = 1262881) B1262881
theorem B1683875 : Blo 996598 1683875 := bstep (se 1 (by rfl) ⟨1262906, by rfl⟩ : syracuseStep 1683875 = 2525813) B2525813
theorem B1684003 : Blo 996598 1684003 := bstep (se 1 (by rfl) ⟨1263002, by rfl⟩ : syracuseStep 1684003 = 2526005) B2526005
theorem B1684145 : Blo 996598 1684145 := bstep (se 2 (by rfl) ⟨631554, by rfl⟩ : syracuseStep 1684145 = 1263109) B1263109
theorem B1684273 : Blo 996598 1684273 := bstep (se 2 (by rfl) ⟨631602, by rfl⟩ : syracuseStep 1684273 = 1263205) B1263205
theorem B1684307 : Blo 996598 1684307 := bstep (se 1 (by rfl) ⟨1263230, by rfl⟩ : syracuseStep 1684307 = 2526461) B2526461
theorem B1422211 : Blo 996598 1422211 := bstep (se 1 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 1422211 = 2133317) B2133317
theorem B1684435 : Blo 996598 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B1684577 : Blo 996598 1684577 := bstep (se 2 (by rfl) ⟨631716, by rfl⟩ : syracuseStep 1684577 = 1263433) B1263433
theorem B1684705 : Blo 996598 1684705 := bstep (se 2 (by rfl) ⟨631764, by rfl⟩ : syracuseStep 1684705 = 1263529) B1263529
theorem B996611 : Blo 996598 996611 := bstep (se 1 (by rfl) ⟨747458, by rfl⟩ : syracuseStep 996611 = 1494917) B1494917
theorem B1684739 : Blo 996598 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B996627 : Blo 996598 996627 := bstep (se 1 (by rfl) ⟨747470, by rfl⟩ : syracuseStep 996627 = 1494941) B1494941
theorem B996643 : Blo 996598 996643 := bstep (se 1 (by rfl) ⟨747482, by rfl⟩ : syracuseStep 996643 = 1494965) B1494965
theorem B996659 : Blo 996598 996659 := bstep (se 1 (by rfl) ⟨747494, by rfl⟩ : syracuseStep 996659 = 1494989) B1494989
theorem B996675 : Blo 996598 996675 := bstep (se 1 (by rfl) ⟨747506, by rfl⟩ : syracuseStep 996675 = 1495013) B1495013
theorem B996691 : Blo 996598 996691 := bstep (se 1 (by rfl) ⟨747518, by rfl⟩ : syracuseStep 996691 = 1495037) B1495037
theorem B1422689 : Blo 996598 1422689 := bstep (se 2 (by rfl) ⟨533508, by rfl⟩ : syracuseStep 1422689 = 1067017) B1067017
theorem B996707 : Blo 996598 996707 := bstep (se 1 (by rfl) ⟨747530, by rfl⟩ : syracuseStep 996707 = 1495061) B1495061
theorem B996723 : Blo 996598 996723 := bstep (se 1 (by rfl) ⟨747542, by rfl⟩ : syracuseStep 996723 = 1495085) B1495085
theorem B996739 : Blo 996598 996739 := bstep (se 1 (by rfl) ⟨747554, by rfl⟩ : syracuseStep 996739 = 1495109) B1495109
theorem B1684867 : Blo 996598 1684867 := bstep (se 1 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 1684867 = 2527301) B2527301
theorem B996755 : Blo 996598 996755 := bstep (se 1 (by rfl) ⟨747566, by rfl⟩ : syracuseStep 996755 = 1495133) B1495133
theorem B996771 : Blo 996598 996771 := bstep (se 1 (by rfl) ⟨747578, by rfl⟩ : syracuseStep 996771 = 1495157) B1495157
theorem B996787 : Blo 996598 996787 := bstep (se 1 (by rfl) ⟨747590, by rfl⟩ : syracuseStep 996787 = 1495181) B1495181
theorem B996803 : Blo 996598 996803 := bstep (se 1 (by rfl) ⟨747602, by rfl⟩ : syracuseStep 996803 = 1495205) B1495205
theorem B996819 : Blo 996598 996819 := bstep (se 1 (by rfl) ⟨747614, by rfl⟩ : syracuseStep 996819 = 1495229) B1495229
theorem B1422803 : Blo 996598 1422803 := bstep (se 1 (by rfl) ⟨1067102, by rfl⟩ : syracuseStep 1422803 = 2134205) B2134205
theorem B996835 : Blo 996598 996835 := bstep (se 1 (by rfl) ⟨747626, by rfl⟩ : syracuseStep 996835 = 1495253) B1495253
theorem B996851 : Blo 996598 996851 := bstep (se 1 (by rfl) ⟨747638, by rfl⟩ : syracuseStep 996851 = 1495277) B1495277
theorem B996867 : Blo 996598 996867 := bstep (se 1 (by rfl) ⟨747650, by rfl⟩ : syracuseStep 996867 = 1495301) B1495301
theorem B1685009 : Blo 996598 1685009 := bstep (se 2 (by rfl) ⟨631878, by rfl⟩ : syracuseStep 1685009 = 1263757) B1263757
theorem B996883 : Blo 996598 996883 := bstep (se 1 (by rfl) ⟨747662, by rfl⟩ : syracuseStep 996883 = 1495325) B1495325
theorem B996899 : Blo 996598 996899 := bstep (se 1 (by rfl) ⟨747674, by rfl⟩ : syracuseStep 996899 = 1495349) B1495349
theorem B1422883 : Blo 996598 1422883 := bstep (se 1 (by rfl) ⟨1067162, by rfl⟩ : syracuseStep 1422883 = 2134325) B2134325
theorem B5682737 : Blo 996598 5682737 := bstep (se 2 (by rfl) ⟨2131026, by rfl⟩ : syracuseStep 5682737 = 4262053) B4262053
theorem B996915 : Blo 996598 996915 := bstep (se 1 (by rfl) ⟨747686, by rfl⟩ : syracuseStep 996915 = 1495373) B1495373
theorem B996931 : Blo 996598 996931 := bstep (se 1 (by rfl) ⟨747698, by rfl⟩ : syracuseStep 996931 = 1495397) B1495397
theorem B996947 : Blo 996598 996947 := bstep (se 1 (by rfl) ⟨747710, by rfl⟩ : syracuseStep 996947 = 1495421) B1495421
theorem B996963 : Blo 996598 996963 := bstep (se 1 (by rfl) ⟨747722, by rfl⟩ : syracuseStep 996963 = 1495445) B1495445
theorem B996979 : Blo 996598 996979 := bstep (se 1 (by rfl) ⟨747734, by rfl⟩ : syracuseStep 996979 = 1495469) B1495469
theorem B996995 : Blo 996598 996995 := bstep (se 1 (by rfl) ⟨747746, by rfl⟩ : syracuseStep 996995 = 1495493) B1495493
theorem B1685137 : Blo 996598 1685137 := bstep (se 2 (by rfl) ⟨631926, by rfl⟩ : syracuseStep 1685137 = 1263853) B1263853
theorem B997011 : Blo 996598 997011 := bstep (se 1 (by rfl) ⟨747758, by rfl⟩ : syracuseStep 997011 = 1495517) B1495517
theorem B997027 : Blo 996598 997027 := bstep (se 1 (by rfl) ⟨747770, by rfl⟩ : syracuseStep 997027 = 1495541) B1495541
theorem B997043 : Blo 996598 997043 := bstep (se 1 (by rfl) ⟨747782, by rfl⟩ : syracuseStep 997043 = 1495565) B1495565
theorem B1685171 : Blo 996598 1685171 := bstep (se 1 (by rfl) ⟨1263878, by rfl⟩ : syracuseStep 1685171 = 2527757) B2527757
theorem B997059 : Blo 996598 997059 := bstep (se 1 (by rfl) ⟨747794, by rfl⟩ : syracuseStep 997059 = 1495589) B1495589
theorem B997075 : Blo 996598 997075 := bstep (se 1 (by rfl) ⟨747806, by rfl⟩ : syracuseStep 997075 = 1495613) B1495613
theorem B997091 : Blo 996598 997091 := bstep (se 1 (by rfl) ⟨747818, by rfl⟩ : syracuseStep 997091 = 1495637) B1495637
theorem B997107 : Blo 996598 997107 := bstep (se 1 (by rfl) ⟨747830, by rfl⟩ : syracuseStep 997107 = 1495661) B1495661
theorem B997123 : Blo 996598 997123 := bstep (se 1 (by rfl) ⟨747842, by rfl⟩ : syracuseStep 997123 = 1495685) B1495685
theorem B997139 : Blo 996598 997139 := bstep (se 1 (by rfl) ⟨747854, by rfl⟩ : syracuseStep 997139 = 1495709) B1495709
theorem B997155 : Blo 996598 997155 := bstep (se 1 (by rfl) ⟨747866, by rfl⟩ : syracuseStep 997155 = 1495733) B1495733
theorem B997171 : Blo 996598 997171 := bstep (se 1 (by rfl) ⟨747878, by rfl⟩ : syracuseStep 997171 = 1495757) B1495757
theorem B1685299 : Blo 996598 1685299 := bstep (se 1 (by rfl) ⟨1263974, by rfl⟩ : syracuseStep 1685299 = 2527949) B2527949
theorem B997187 : Blo 996598 997187 := bstep (se 1 (by rfl) ⟨747890, by rfl⟩ : syracuseStep 997187 = 1495781) B1495781
theorem B2242385 : Blo 996598 2242385 := bstep (se 2 (by rfl) ⟨840894, by rfl⟩ : syracuseStep 2242385 = 1681789) B1681789
theorem B997203 : Blo 996598 997203 := bstep (se 1 (by rfl) ⟨747902, by rfl⟩ : syracuseStep 997203 = 1495805) B1495805
theorem B2242403 : Blo 996598 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B997219 : Blo 996598 997219 := bstep (se 1 (by rfl) ⟨747914, by rfl⟩ : syracuseStep 997219 = 1495829) B1495829
theorem B997235 : Blo 996598 997235 := bstep (se 1 (by rfl) ⟨747926, by rfl⟩ : syracuseStep 997235 = 1495853) B1495853
theorem B997251 : Blo 996598 997251 := bstep (se 1 (by rfl) ⟨747938, by rfl⟩ : syracuseStep 997251 = 1495877) B1495877
theorem B997267 : Blo 996598 997267 := bstep (se 1 (by rfl) ⟨747950, by rfl⟩ : syracuseStep 997267 = 1495901) B1495901
theorem B997283 : Blo 996598 997283 := bstep (se 1 (by rfl) ⟨747962, by rfl⟩ : syracuseStep 997283 = 1495925) B1495925
theorem B997299 : Blo 996598 997299 := bstep (se 1 (by rfl) ⟨747974, by rfl⟩ : syracuseStep 997299 = 1495949) B1495949
theorem B1685441 : Blo 996598 1685441 := bstep (se 2 (by rfl) ⟨632040, by rfl⟩ : syracuseStep 1685441 = 1264081) B1264081
theorem B997315 : Blo 996598 997315 := bstep (se 1 (by rfl) ⟨747986, by rfl⟩ : syracuseStep 997315 = 1495973) B1495973
theorem B997331 : Blo 996598 997331 := bstep (se 1 (by rfl) ⟨747998, by rfl⟩ : syracuseStep 997331 = 1495997) B1495997
theorem B997347 : Blo 996598 997347 := bstep (se 1 (by rfl) ⟨748010, by rfl⟩ : syracuseStep 997347 = 1496021) B1496021
theorem B997363 : Blo 996598 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B997379 : Blo 996598 997379 := bstep (se 1 (by rfl) ⟨748034, by rfl⟩ : syracuseStep 997379 = 1496069) B1496069
theorem B997395 : Blo 996598 997395 := bstep (se 1 (by rfl) ⟨748046, by rfl⟩ : syracuseStep 997395 = 1496093) B1496093
theorem B997411 : Blo 996598 997411 := bstep (se 1 (by rfl) ⟨748058, by rfl⟩ : syracuseStep 997411 = 1496117) B1496117
theorem B997427 : Blo 996598 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B1685569 : Blo 996598 1685569 := bstep (se 2 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 1685569 = 1264177) B1264177
theorem B997443 : Blo 996598 997443 := bstep (se 1 (by rfl) ⟨748082, by rfl⟩ : syracuseStep 997443 = 1496165) B1496165
theorem B4798541 : Blo 996598 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B1423441 : Blo 996598 1423441 := bstep (se 2 (by rfl) ⟨533790, by rfl⟩ : syracuseStep 1423441 = 1067581) B1067581
theorem B997459 : Blo 996598 997459 := bstep (se 1 (by rfl) ⟨748094, by rfl⟩ : syracuseStep 997459 = 1496189) B1496189
theorem B997475 : Blo 996598 997475 := bstep (se 1 (by rfl) ⟨748106, by rfl⟩ : syracuseStep 997475 = 1496213) B1496213
theorem B1685603 : Blo 996598 1685603 := bstep (se 1 (by rfl) ⟨1264202, by rfl⟩ : syracuseStep 1685603 = 2528405) B2528405
theorem B2242673 : Blo 996598 2242673 := bstep (se 2 (by rfl) ⟨841002, by rfl⟩ : syracuseStep 2242673 = 1682005) B1682005
theorem B997491 : Blo 996598 997491 := bstep (se 1 (by rfl) ⟨748118, by rfl⟩ : syracuseStep 997491 = 1496237) B1496237
theorem B2242691 : Blo 996598 2242691 := bstep (se 1 (by rfl) ⟨1682018, by rfl⟩ : syracuseStep 2242691 = 3364037) B3364037
theorem B997507 : Blo 996598 997507 := bstep (se 1 (by rfl) ⟨748130, by rfl⟩ : syracuseStep 997507 = 1496261) B1496261
theorem B997523 : Blo 996598 997523 := bstep (se 1 (by rfl) ⟨748142, by rfl⟩ : syracuseStep 997523 = 1496285) B1496285
theorem B997539 : Blo 996598 997539 := bstep (se 1 (by rfl) ⟨748154, by rfl⟩ : syracuseStep 997539 = 1496309) B1496309
theorem B997555 : Blo 996598 997555 := bstep (se 1 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 997555 = 1496333) B1496333
theorem B997571 : Blo 996598 997571 := bstep (se 1 (by rfl) ⟨748178, by rfl⟩ : syracuseStep 997571 = 1496357) B1496357
theorem B997587 : Blo 996598 997587 := bstep (se 1 (by rfl) ⟨748190, by rfl⟩ : syracuseStep 997587 = 1496381) B1496381
theorem B997603 : Blo 996598 997603 := bstep (se 1 (by rfl) ⟨748202, by rfl⟩ : syracuseStep 997603 = 1496405) B1496405
theorem B1685731 : Blo 996598 1685731 := bstep (se 1 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 1685731 = 2528597) B2528597
theorem B997619 : Blo 996598 997619 := bstep (se 1 (by rfl) ⟨748214, by rfl⟩ : syracuseStep 997619 = 1496429) B1496429
theorem B997635 : Blo 996598 997635 := bstep (se 1 (by rfl) ⟨748226, by rfl⟩ : syracuseStep 997635 = 1496453) B1496453
theorem B997651 : Blo 996598 997651 := bstep (se 1 (by rfl) ⟨748238, by rfl⟩ : syracuseStep 997651 = 1496477) B1496477
theorem B997667 : Blo 996598 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B997683 : Blo 996598 997683 := bstep (se 1 (by rfl) ⟨748262, by rfl⟩ : syracuseStep 997683 = 1496525) B1496525
theorem B997699 : Blo 996598 997699 := bstep (se 1 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 997699 = 1496549) B1496549
theorem B997715 : Blo 996598 997715 := bstep (se 1 (by rfl) ⟨748286, by rfl⟩ : syracuseStep 997715 = 1496573) B1496573
theorem B997731 : Blo 996598 997731 := bstep (se 1 (by rfl) ⟨748298, by rfl⟩ : syracuseStep 997731 = 1496597) B1496597
theorem B2701667 : Blo 996598 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B1685873 : Blo 996598 1685873 := bstep (se 2 (by rfl) ⟨632202, by rfl⟩ : syracuseStep 1685873 = 1264405) B1264405
theorem B997747 : Blo 996598 997747 := bstep (se 1 (by rfl) ⟨748310, by rfl⟩ : syracuseStep 997747 = 1496621) B1496621
theorem B997763 : Blo 996598 997763 := bstep (se 1 (by rfl) ⟨748322, by rfl⟩ : syracuseStep 997763 = 1496645) B1496645
theorem B2242961 : Blo 996598 2242961 := bstep (se 2 (by rfl) ⟨841110, by rfl⟩ : syracuseStep 2242961 = 1682221) B1682221
theorem B997779 : Blo 996598 997779 := bstep (se 1 (by rfl) ⟨748334, by rfl⟩ : syracuseStep 997779 = 1496669) B1496669
theorem B2242979 : Blo 996598 2242979 := bstep (se 1 (by rfl) ⟨1682234, by rfl⟩ : syracuseStep 2242979 = 3364469) B3364469
theorem B997795 : Blo 996598 997795 := bstep (se 1 (by rfl) ⟨748346, by rfl⟩ : syracuseStep 997795 = 1496693) B1496693
theorem B5061041 : Blo 996598 5061041 := bstep (se 2 (by rfl) ⟨1897890, by rfl⟩ : syracuseStep 5061041 = 3795781) B3795781
theorem B997811 : Blo 996598 997811 := bstep (se 1 (by rfl) ⟨748358, by rfl⟩ : syracuseStep 997811 = 1496717) B1496717
theorem B997827 : Blo 996598 997827 := bstep (se 1 (by rfl) ⟨748370, by rfl⟩ : syracuseStep 997827 = 1496741) B1496741
theorem B997843 : Blo 996598 997843 := bstep (se 1 (by rfl) ⟨748382, by rfl⟩ : syracuseStep 997843 = 1496765) B1496765
theorem B997859 : Blo 996598 997859 := bstep (se 1 (by rfl) ⟨748394, by rfl⟩ : syracuseStep 997859 = 1496789) B1496789
theorem B1686001 : Blo 996598 1686001 := bstep (se 2 (by rfl) ⟨632250, by rfl⟩ : syracuseStep 1686001 = 1264501) B1264501
theorem B997875 : Blo 996598 997875 := bstep (se 1 (by rfl) ⟨748406, by rfl⟩ : syracuseStep 997875 = 1496813) B1496813
theorem B997891 : Blo 996598 997891 := bstep (se 1 (by rfl) ⟨748418, by rfl⟩ : syracuseStep 997891 = 1496837) B1496837
theorem B997907 : Blo 996598 997907 := bstep (se 1 (by rfl) ⟨748430, by rfl⟩ : syracuseStep 997907 = 1496861) B1496861
theorem B1686035 : Blo 996598 1686035 := bstep (se 1 (by rfl) ⟨1264526, by rfl⟩ : syracuseStep 1686035 = 2529053) B2529053
theorem B997923 : Blo 996598 997923 := bstep (se 1 (by rfl) ⟨748442, by rfl⟩ : syracuseStep 997923 = 1496885) B1496885
theorem B997939 : Blo 996598 997939 := bstep (se 1 (by rfl) ⟨748454, by rfl⟩ : syracuseStep 997939 = 1496909) B1496909
theorem B18233909 : Blo 996598 18233909 := bstep (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) B1709429
theorem B997955 : Blo 996598 997955 := bstep (se 1 (by rfl) ⟨748466, by rfl⟩ : syracuseStep 997955 = 1496933) B1496933
theorem B997971 : Blo 996598 997971 := bstep (se 1 (by rfl) ⟨748478, by rfl⟩ : syracuseStep 997971 = 1496957) B1496957
theorem B997987 : Blo 996598 997987 := bstep (se 1 (by rfl) ⟨748490, by rfl⟩ : syracuseStep 997987 = 1496981) B1496981
theorem B998003 : Blo 996598 998003 := bstep (se 1 (by rfl) ⟨748502, by rfl⟩ : syracuseStep 998003 = 1497005) B1497005
theorem B998019 : Blo 996598 998019 := bstep (se 1 (by rfl) ⟨748514, by rfl⟩ : syracuseStep 998019 = 1497029) B1497029
theorem B998035 : Blo 996598 998035 := bstep (se 1 (by rfl) ⟨748526, by rfl⟩ : syracuseStep 998035 = 1497053) B1497053
theorem B1686163 : Blo 996598 1686163 := bstep (se 1 (by rfl) ⟨1264622, by rfl⟩ : syracuseStep 1686163 = 2529245) B2529245
theorem B998051 : Blo 996598 998051 := bstep (se 1 (by rfl) ⟨748538, by rfl⟩ : syracuseStep 998051 = 1497077) B1497077
theorem B2243249 : Blo 996598 2243249 := bstep (se 2 (by rfl) ⟨841218, by rfl⟩ : syracuseStep 2243249 = 1682437) B1682437
theorem B998067 : Blo 996598 998067 := bstep (se 1 (by rfl) ⟨748550, by rfl⟩ : syracuseStep 998067 = 1497101) B1497101
theorem B2243267 : Blo 996598 2243267 := bstep (se 1 (by rfl) ⟨1682450, by rfl⟩ : syracuseStep 2243267 = 3364901) B3364901
theorem B998083 : Blo 996598 998083 := bstep (se 1 (by rfl) ⟨748562, by rfl⟩ : syracuseStep 998083 = 1497125) B1497125
theorem B998099 : Blo 996598 998099 := bstep (se 1 (by rfl) ⟨748574, by rfl⟩ : syracuseStep 998099 = 1497149) B1497149
theorem B998115 : Blo 996598 998115 := bstep (se 1 (by rfl) ⟨748586, by rfl⟩ : syracuseStep 998115 = 1497173) B1497173
theorem B998131 : Blo 996598 998131 := bstep (se 1 (by rfl) ⟨748598, by rfl⟩ : syracuseStep 998131 = 1497197) B1497197
theorem B998147 : Blo 996598 998147 := bstep (se 1 (by rfl) ⟨748610, by rfl⟩ : syracuseStep 998147 = 1497221) B1497221
theorem B998163 : Blo 996598 998163 := bstep (se 1 (by rfl) ⟨748622, by rfl⟩ : syracuseStep 998163 = 1497245) B1497245
theorem B1424147 : Blo 996598 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B1686305 : Blo 996598 1686305 := bstep (se 2 (by rfl) ⟨632364, by rfl⟩ : syracuseStep 1686305 = 1264729) B1264729
theorem B998179 : Blo 996598 998179 := bstep (se 1 (by rfl) ⟨748634, by rfl⟩ : syracuseStep 998179 = 1497269) B1497269
theorem B998195 : Blo 996598 998195 := bstep (se 1 (by rfl) ⟨748646, by rfl⟩ : syracuseStep 998195 = 1497293) B1497293
theorem B998211 : Blo 996598 998211 := bstep (se 1 (by rfl) ⟨748658, by rfl⟩ : syracuseStep 998211 = 1497317) B1497317
theorem B998227 : Blo 996598 998227 := bstep (se 1 (by rfl) ⟨748670, by rfl⟩ : syracuseStep 998227 = 1497341) B1497341
theorem B998243 : Blo 996598 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B998259 : Blo 996598 998259 := bstep (se 1 (by rfl) ⟨748694, by rfl⟩ : syracuseStep 998259 = 1497389) B1497389
theorem B998275 : Blo 996598 998275 := bstep (se 1 (by rfl) ⟨748706, by rfl⟩ : syracuseStep 998275 = 1497413) B1497413
theorem B1522577 : Blo 996598 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B998291 : Blo 996598 998291 := bstep (se 1 (by rfl) ⟨748718, by rfl⟩ : syracuseStep 998291 = 1497437) B1497437
theorem B1686433 : Blo 996598 1686433 := bstep (se 2 (by rfl) ⟨632412, by rfl⟩ : syracuseStep 1686433 = 1264825) B1264825
theorem B998307 : Blo 996598 998307 := bstep (se 1 (by rfl) ⟨748730, by rfl⟩ : syracuseStep 998307 = 1497461) B1497461
theorem B998323 : Blo 996598 998323 := bstep (se 1 (by rfl) ⟨748742, by rfl⟩ : syracuseStep 998323 = 1497485) B1497485
theorem B998339 : Blo 996598 998339 := bstep (se 1 (by rfl) ⟨748754, by rfl⟩ : syracuseStep 998339 = 1497509) B1497509
theorem B1686467 : Blo 996598 1686467 := bstep (se 1 (by rfl) ⟨1264850, by rfl⟩ : syracuseStep 1686467 = 2529701) B2529701
theorem B2243537 : Blo 996598 2243537 := bstep (se 2 (by rfl) ⟨841326, by rfl⟩ : syracuseStep 2243537 = 1682653) B1682653
theorem B998355 : Blo 996598 998355 := bstep (se 1 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 998355 = 1497533) B1497533
theorem B2243555 : Blo 996598 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B5684195 : Blo 996598 5684195 := bstep (se 1 (by rfl) ⟨4263146, by rfl⟩ : syracuseStep 5684195 = 8526293) B8526293
theorem B998371 : Blo 996598 998371 := bstep (se 1 (by rfl) ⟨748778, by rfl⟩ : syracuseStep 998371 = 1497557) B1497557
theorem B998387 : Blo 996598 998387 := bstep (se 1 (by rfl) ⟨748790, by rfl⟩ : syracuseStep 998387 = 1497581) B1497581
theorem B998403 : Blo 996598 998403 := bstep (se 1 (by rfl) ⟨748802, by rfl⟩ : syracuseStep 998403 = 1497605) B1497605
theorem B998419 : Blo 996598 998419 := bstep (se 1 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 998419 = 1497629) B1497629
theorem B6405155 : Blo 996598 6405155 := bstep (se 1 (by rfl) ⟨4803866, by rfl⟩ : syracuseStep 6405155 = 9607733) B9607733
theorem B998435 : Blo 996598 998435 := bstep (se 1 (by rfl) ⟨748826, by rfl⟩ : syracuseStep 998435 = 1497653) B1497653
theorem B3193901 : Blo 996598 3193901 := bstep (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) B1197713
theorem B998451 : Blo 996598 998451 := bstep (se 1 (by rfl) ⟨748838, by rfl⟩ : syracuseStep 998451 = 1497677) B1497677
theorem B998467 : Blo 996598 998467 := bstep (se 1 (by rfl) ⟨748850, by rfl⟩ : syracuseStep 998467 = 1497701) B1497701
theorem B1686595 : Blo 996598 1686595 := bstep (se 1 (by rfl) ⟨1264946, by rfl⟩ : syracuseStep 1686595 = 2529893) B2529893
theorem B998483 : Blo 996598 998483 := bstep (se 1 (by rfl) ⟨748862, by rfl⟩ : syracuseStep 998483 = 1497725) B1497725
theorem B998499 : Blo 996598 998499 := bstep (se 1 (by rfl) ⟨748874, by rfl⟩ : syracuseStep 998499 = 1497749) B1497749
theorem B998515 : Blo 996598 998515 := bstep (se 1 (by rfl) ⟨748886, by rfl⟩ : syracuseStep 998515 = 1497773) B1497773
theorem B998531 : Blo 996598 998531 := bstep (se 1 (by rfl) ⟨748898, by rfl⟩ : syracuseStep 998531 = 1497797) B1497797
theorem B998547 : Blo 996598 998547 := bstep (se 1 (by rfl) ⟨748910, by rfl⟩ : syracuseStep 998547 = 1497821) B1497821
theorem B998563 : Blo 996598 998563 := bstep (se 1 (by rfl) ⟨748922, by rfl⟩ : syracuseStep 998563 = 1497845) B1497845
theorem B998579 : Blo 996598 998579 := bstep (se 1 (by rfl) ⟨748934, by rfl⟩ : syracuseStep 998579 = 1497869) B1497869
theorem B998595 : Blo 996598 998595 := bstep (se 1 (by rfl) ⟨748946, by rfl⟩ : syracuseStep 998595 = 1497893) B1497893
theorem B1686737 : Blo 996598 1686737 := bstep (se 2 (by rfl) ⟨632526, by rfl⟩ : syracuseStep 1686737 = 1265053) B1265053
theorem B998611 : Blo 996598 998611 := bstep (se 1 (by rfl) ⟨748958, by rfl⟩ : syracuseStep 998611 = 1497917) B1497917
theorem B998627 : Blo 996598 998627 := bstep (se 1 (by rfl) ⟨748970, by rfl⟩ : syracuseStep 998627 = 1497941) B1497941
theorem B2243825 : Blo 996598 2243825 := bstep (se 2 (by rfl) ⟨841434, by rfl⟩ : syracuseStep 2243825 = 1682869) B1682869
theorem B998643 : Blo 996598 998643 := bstep (se 1 (by rfl) ⟨748982, by rfl⟩ : syracuseStep 998643 = 1497965) B1497965
theorem B2243843 : Blo 996598 2243843 := bstep (se 1 (by rfl) ⟨1682882, by rfl⟩ : syracuseStep 2243843 = 3365765) B3365765
theorem B998659 : Blo 996598 998659 := bstep (se 1 (by rfl) ⟨748994, by rfl⟩ : syracuseStep 998659 = 1497989) B1497989
theorem B2702609 : Blo 996598 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B998675 : Blo 996598 998675 := bstep (se 1 (by rfl) ⟨749006, by rfl⟩ : syracuseStep 998675 = 1498013) B1498013
theorem B998691 : Blo 996598 998691 := bstep (se 1 (by rfl) ⟨749018, by rfl⟩ : syracuseStep 998691 = 1498037) B1498037
theorem B998707 : Blo 996598 998707 := bstep (se 1 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 998707 = 1498061) B1498061
theorem B998723 : Blo 996598 998723 := bstep (se 1 (by rfl) ⟨749042, by rfl⟩ : syracuseStep 998723 = 1498085) B1498085
theorem B1686865 : Blo 996598 1686865 := bstep (se 2 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 1686865 = 1265149) B1265149
theorem B998739 : Blo 996598 998739 := bstep (se 1 (by rfl) ⟨749054, by rfl⟩ : syracuseStep 998739 = 1498109) B1498109
theorem B998755 : Blo 996598 998755 := bstep (se 1 (by rfl) ⟨749066, by rfl⟩ : syracuseStep 998755 = 1498133) B1498133
theorem B998771 : Blo 996598 998771 := bstep (se 1 (by rfl) ⟨749078, by rfl⟩ : syracuseStep 998771 = 1498157) B1498157
theorem B1686899 : Blo 996598 1686899 := bstep (se 1 (by rfl) ⟨1265174, by rfl⟩ : syracuseStep 1686899 = 2530349) B2530349
theorem B998787 : Blo 996598 998787 := bstep (se 1 (by rfl) ⟨749090, by rfl⟩ : syracuseStep 998787 = 1498181) B1498181
theorem B998803 : Blo 996598 998803 := bstep (se 1 (by rfl) ⟨749102, by rfl⟩ : syracuseStep 998803 = 1498205) B1498205
theorem B998819 : Blo 996598 998819 := bstep (se 1 (by rfl) ⟨749114, by rfl⟩ : syracuseStep 998819 = 1498229) B1498229
theorem B998835 : Blo 996598 998835 := bstep (se 1 (by rfl) ⟨749126, by rfl⟩ : syracuseStep 998835 = 1498253) B1498253
theorem B998851 : Blo 996598 998851 := bstep (se 1 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 998851 = 1498277) B1498277
theorem B998867 : Blo 996598 998867 := bstep (se 1 (by rfl) ⟨749150, by rfl⟩ : syracuseStep 998867 = 1498301) B1498301
theorem B998883 : Blo 996598 998883 := bstep (se 1 (by rfl) ⟨749162, by rfl⟩ : syracuseStep 998883 = 1498325) B1498325
theorem B998899 : Blo 996598 998899 := bstep (se 1 (by rfl) ⟨749174, by rfl⟩ : syracuseStep 998899 = 1498349) B1498349
theorem B1687027 : Blo 996598 1687027 := bstep (se 1 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 1687027 = 2530541) B2530541
theorem B998915 : Blo 996598 998915 := bstep (se 1 (by rfl) ⟨749186, by rfl⟩ : syracuseStep 998915 = 1498373) B1498373
theorem B2244113 : Blo 996598 2244113 := bstep (se 2 (by rfl) ⟨841542, by rfl⟩ : syracuseStep 2244113 = 1683085) B1683085
theorem B998931 : Blo 996598 998931 := bstep (se 1 (by rfl) ⟨749198, by rfl⟩ : syracuseStep 998931 = 1498397) B1498397
theorem B2244131 : Blo 996598 2244131 := bstep (se 1 (by rfl) ⟨1683098, by rfl⟩ : syracuseStep 2244131 = 3366197) B3366197
theorem B998947 : Blo 996598 998947 := bstep (se 1 (by rfl) ⟨749210, by rfl⟩ : syracuseStep 998947 = 1498421) B1498421
theorem B998963 : Blo 996598 998963 := bstep (se 1 (by rfl) ⟨749222, by rfl⟩ : syracuseStep 998963 = 1498445) B1498445
theorem B998979 : Blo 996598 998979 := bstep (se 1 (by rfl) ⟨749234, by rfl⟩ : syracuseStep 998979 = 1498469) B1498469
theorem B998995 : Blo 996598 998995 := bstep (se 1 (by rfl) ⟨749246, by rfl⟩ : syracuseStep 998995 = 1498493) B1498493
theorem B999011 : Blo 996598 999011 := bstep (se 1 (by rfl) ⟨749258, by rfl⟩ : syracuseStep 999011 = 1498517) B1498517
theorem B999027 : Blo 996598 999027 := bstep (se 1 (by rfl) ⟨749270, by rfl⟩ : syracuseStep 999027 = 1498541) B1498541
theorem B1687169 : Blo 996598 1687169 := bstep (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) B1265377
theorem B999043 : Blo 996598 999043 := bstep (se 1 (by rfl) ⟨749282, by rfl⟩ : syracuseStep 999043 = 1498565) B1498565
theorem B999059 : Blo 996598 999059 := bstep (se 1 (by rfl) ⟨749294, by rfl⟩ : syracuseStep 999059 = 1498589) B1498589
theorem B999075 : Blo 996598 999075 := bstep (se 1 (by rfl) ⟨749306, by rfl⟩ : syracuseStep 999075 = 1498613) B1498613
theorem B999091 : Blo 996598 999091 := bstep (se 1 (by rfl) ⟨749318, by rfl⟩ : syracuseStep 999091 = 1498637) B1498637
theorem B999107 : Blo 996598 999107 := bstep (se 1 (by rfl) ⟨749330, by rfl⟩ : syracuseStep 999107 = 1498661) B1498661
theorem B999123 : Blo 996598 999123 := bstep (se 1 (by rfl) ⟨749342, by rfl⟩ : syracuseStep 999123 = 1498685) B1498685
theorem B999139 : Blo 996598 999139 := bstep (se 1 (by rfl) ⟨749354, by rfl⟩ : syracuseStep 999139 = 1498709) B1498709
theorem B999155 : Blo 996598 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B1687297 : Blo 996598 1687297 := bstep (se 2 (by rfl) ⟨632736, by rfl⟩ : syracuseStep 1687297 = 1265473) B1265473
theorem B999171 : Blo 996598 999171 := bstep (se 1 (by rfl) ⟨749378, by rfl⟩ : syracuseStep 999171 = 1498757) B1498757
theorem B999187 : Blo 996598 999187 := bstep (se 1 (by rfl) ⟨749390, by rfl⟩ : syracuseStep 999187 = 1498781) B1498781
theorem B999203 : Blo 996598 999203 := bstep (se 1 (by rfl) ⟨749402, by rfl⟩ : syracuseStep 999203 = 1498805) B1498805
theorem B1687331 : Blo 996598 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B2244401 : Blo 996598 2244401 := bstep (se 2 (by rfl) ⟨841650, by rfl⟩ : syracuseStep 2244401 = 1683301) B1683301
theorem B999219 : Blo 996598 999219 := bstep (se 1 (by rfl) ⟨749414, by rfl⟩ : syracuseStep 999219 = 1498829) B1498829
theorem B2244419 : Blo 996598 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B999235 : Blo 996598 999235 := bstep (se 1 (by rfl) ⟨749426, by rfl⟩ : syracuseStep 999235 = 1498853) B1498853
theorem B999251 : Blo 996598 999251 := bstep (se 1 (by rfl) ⟨749438, by rfl⟩ : syracuseStep 999251 = 1498877) B1498877
theorem B999267 : Blo 996598 999267 := bstep (se 1 (by rfl) ⟨749450, by rfl⟩ : syracuseStep 999267 = 1498901) B1498901
theorem B5062499 : Blo 996598 5062499 := bstep (se 1 (by rfl) ⟨3796874, by rfl⟩ : syracuseStep 5062499 = 7593749) B7593749
theorem B999283 : Blo 996598 999283 := bstep (se 1 (by rfl) ⟨749462, by rfl⟩ : syracuseStep 999283 = 1498925) B1498925
theorem B999299 : Blo 996598 999299 := bstep (se 1 (by rfl) ⟨749474, by rfl⟩ : syracuseStep 999299 = 1498949) B1498949
theorem B6078341 : Blo 996598 6078341 := bstep (se 4 (by rfl) ⟨569844, by rfl⟩ : syracuseStep 6078341 = 1139689) B1139689
theorem B3784589 : Blo 996598 3784589 := bstep (se 3 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 3784589 = 1419221) B1419221
theorem B999315 : Blo 996598 999315 := bstep (se 1 (by rfl) ⟨749486, by rfl⟩ : syracuseStep 999315 = 1498973) B1498973
theorem B999331 : Blo 996598 999331 := bstep (se 1 (by rfl) ⟨749498, by rfl⟩ : syracuseStep 999331 = 1498997) B1498997
theorem B1687459 : Blo 996598 1687459 := bstep (se 1 (by rfl) ⟨1265594, by rfl⟩ : syracuseStep 1687459 = 2531189) B2531189
theorem B3194797 : Blo 996598 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B999347 : Blo 996598 999347 := bstep (se 1 (by rfl) ⟨749510, by rfl⟩ : syracuseStep 999347 = 1499021) B1499021
theorem B999363 : Blo 996598 999363 := bstep (se 1 (by rfl) ⟨749522, by rfl⟩ : syracuseStep 999363 = 1499045) B1499045
theorem B2703299 : Blo 996598 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B999379 : Blo 996598 999379 := bstep (se 1 (by rfl) ⟨749534, by rfl⟩ : syracuseStep 999379 = 1499069) B1499069
theorem B999395 : Blo 996598 999395 := bstep (se 1 (by rfl) ⟨749546, by rfl⟩ : syracuseStep 999395 = 1499093) B1499093
theorem B999411 : Blo 996598 999411 := bstep (se 1 (by rfl) ⟨749558, by rfl⟩ : syracuseStep 999411 = 1499117) B1499117
theorem B999427 : Blo 996598 999427 := bstep (se 1 (by rfl) ⟨749570, by rfl⟩ : syracuseStep 999427 = 1499141) B1499141
theorem B999443 : Blo 996598 999443 := bstep (se 1 (by rfl) ⟨749582, by rfl⟩ : syracuseStep 999443 = 1499165) B1499165
theorem B999459 : Blo 996598 999459 := bstep (se 1 (by rfl) ⟨749594, by rfl⟩ : syracuseStep 999459 = 1499189) B1499189
theorem B1687601 : Blo 996598 1687601 := bstep (se 2 (by rfl) ⟨632850, by rfl⟩ : syracuseStep 1687601 = 1265701) B1265701
theorem B999475 : Blo 996598 999475 := bstep (se 1 (by rfl) ⟨749606, by rfl⟩ : syracuseStep 999475 = 1499213) B1499213
theorem B999491 : Blo 996598 999491 := bstep (se 1 (by rfl) ⟨749618, by rfl⟩ : syracuseStep 999491 = 1499237) B1499237
theorem B2244689 : Blo 996598 2244689 := bstep (se 2 (by rfl) ⟨841758, by rfl⟩ : syracuseStep 2244689 = 1683517) B1683517
theorem B1261651 : Blo 996598 1261651 := bstep (se 1 (by rfl) ⟨946238, by rfl⟩ : syracuseStep 1261651 = 1892477) B1892477
theorem B999507 : Blo 996598 999507 := bstep (se 1 (by rfl) ⟨749630, by rfl⟩ : syracuseStep 999507 = 1499261) B1499261
theorem B2244707 : Blo 996598 2244707 := bstep (se 1 (by rfl) ⟨1683530, by rfl⟩ : syracuseStep 2244707 = 3367061) B3367061
theorem B999523 : Blo 996598 999523 := bstep (se 1 (by rfl) ⟨749642, by rfl⟩ : syracuseStep 999523 = 1499285) B1499285
theorem B11386979 : Blo 996598 11386979 := bstep (se 1 (by rfl) ⟨8540234, by rfl⟩ : syracuseStep 11386979 = 17080469) B17080469
theorem B999539 : Blo 996598 999539 := bstep (se 1 (by rfl) ⟨749654, by rfl⟩ : syracuseStep 999539 = 1499309) B1499309
theorem B999555 : Blo 996598 999555 := bstep (se 1 (by rfl) ⟨749666, by rfl⟩ : syracuseStep 999555 = 1499333) B1499333
theorem B999571 : Blo 996598 999571 := bstep (se 1 (by rfl) ⟨749678, by rfl⟩ : syracuseStep 999571 = 1499357) B1499357
theorem B999587 : Blo 996598 999587 := bstep (se 1 (by rfl) ⟨749690, by rfl⟩ : syracuseStep 999587 = 1499381) B1499381
theorem B1687729 : Blo 996598 1687729 := bstep (se 2 (by rfl) ⟨632898, by rfl⟩ : syracuseStep 1687729 = 1265797) B1265797
theorem B1261747 : Blo 996598 1261747 := bstep (se 1 (by rfl) ⟨946310, by rfl⟩ : syracuseStep 1261747 = 1892621) B1892621
theorem B999603 : Blo 996598 999603 := bstep (se 1 (by rfl) ⟨749702, by rfl⟩ : syracuseStep 999603 = 1499405) B1499405
theorem B999619 : Blo 996598 999619 := bstep (se 1 (by rfl) ⟨749714, by rfl⟩ : syracuseStep 999619 = 1499429) B1499429
theorem B999635 : Blo 996598 999635 := bstep (se 1 (by rfl) ⟨749726, by rfl⟩ : syracuseStep 999635 = 1499453) B1499453
theorem B1687763 : Blo 996598 1687763 := bstep (se 1 (by rfl) ⟨1265822, by rfl⟩ : syracuseStep 1687763 = 2531645) B2531645
theorem B999651 : Blo 996598 999651 := bstep (se 1 (by rfl) ⟨749738, by rfl⟩ : syracuseStep 999651 = 1499477) B1499477
theorem B999667 : Blo 996598 999667 := bstep (se 1 (by rfl) ⟨749750, by rfl⟩ : syracuseStep 999667 = 1499501) B1499501
theorem B999683 : Blo 996598 999683 := bstep (se 1 (by rfl) ⟨749762, by rfl⟩ : syracuseStep 999683 = 1499525) B1499525
theorem B999699 : Blo 996598 999699 := bstep (se 1 (by rfl) ⟨749774, by rfl⟩ : syracuseStep 999699 = 1499549) B1499549
theorem B999715 : Blo 996598 999715 := bstep (se 1 (by rfl) ⟨749786, by rfl⟩ : syracuseStep 999715 = 1499573) B1499573
theorem B999731 : Blo 996598 999731 := bstep (se 1 (by rfl) ⟨749798, by rfl⟩ : syracuseStep 999731 = 1499597) B1499597
theorem B999747 : Blo 996598 999747 := bstep (se 1 (by rfl) ⟨749810, by rfl⟩ : syracuseStep 999747 = 1499621) B1499621
theorem B999763 : Blo 996598 999763 := bstep (se 1 (by rfl) ⟨749822, by rfl⟩ : syracuseStep 999763 = 1499645) B1499645
theorem B1687891 : Blo 996598 1687891 := bstep (se 1 (by rfl) ⟨1265918, by rfl⟩ : syracuseStep 1687891 = 2531837) B2531837
theorem B999779 : Blo 996598 999779 := bstep (se 1 (by rfl) ⟨749834, by rfl⟩ : syracuseStep 999779 = 1499669) B1499669
theorem B2244977 : Blo 996598 2244977 := bstep (se 2 (by rfl) ⟨841866, by rfl⟩ : syracuseStep 2244977 = 1683733) B1683733
theorem B999795 : Blo 996598 999795 := bstep (se 1 (by rfl) ⟨749846, by rfl⟩ : syracuseStep 999795 = 1499693) B1499693
theorem B2244995 : Blo 996598 2244995 := bstep (se 1 (by rfl) ⟨1683746, by rfl⟩ : syracuseStep 2244995 = 3367493) B3367493
theorem B999811 : Blo 996598 999811 := bstep (se 1 (by rfl) ⟨749858, by rfl⟩ : syracuseStep 999811 = 1499717) B1499717
theorem B999827 : Blo 996598 999827 := bstep (se 1 (by rfl) ⟨749870, by rfl⟩ : syracuseStep 999827 = 1499741) B1499741
theorem B999843 : Blo 996598 999843 := bstep (se 1 (by rfl) ⟨749882, by rfl⟩ : syracuseStep 999843 = 1499765) B1499765
theorem B999859 : Blo 996598 999859 := bstep (se 1 (by rfl) ⟨749894, by rfl⟩ : syracuseStep 999859 = 1499789) B1499789
theorem B999875 : Blo 996598 999875 := bstep (se 1 (by rfl) ⟨749906, by rfl⟩ : syracuseStep 999875 = 1499813) B1499813
theorem B999891 : Blo 996598 999891 := bstep (se 1 (by rfl) ⟨749918, by rfl⟩ : syracuseStep 999891 = 1499837) B1499837
theorem B1688033 : Blo 996598 1688033 := bstep (se 2 (by rfl) ⟨633012, by rfl⟩ : syracuseStep 1688033 = 1266025) B1266025
theorem B999907 : Blo 996598 999907 := bstep (se 1 (by rfl) ⟨749930, by rfl⟩ : syracuseStep 999907 = 1499861) B1499861
theorem B999923 : Blo 996598 999923 := bstep (se 1 (by rfl) ⟨749942, by rfl⟩ : syracuseStep 999923 = 1499885) B1499885
theorem B999939 : Blo 996598 999939 := bstep (se 1 (by rfl) ⟨749954, by rfl⟩ : syracuseStep 999939 = 1499909) B1499909
theorem B999955 : Blo 996598 999955 := bstep (se 1 (by rfl) ⟨749966, by rfl⟩ : syracuseStep 999955 = 1499933) B1499933
theorem B999971 : Blo 996598 999971 := bstep (se 1 (by rfl) ⟨749978, by rfl⟩ : syracuseStep 999971 = 1499957) B1499957
theorem B3654179 : Blo 996598 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B999987 : Blo 996598 999987 := bstep (se 1 (by rfl) ⟨749990, by rfl⟩ : syracuseStep 999987 = 1499981) B1499981
theorem B1000003 : Blo 996598 1000003 := bstep (se 1 (by rfl) ⟨750002, by rfl⟩ : syracuseStep 1000003 = 1500005) B1500005
theorem B1000019 : Blo 996598 1000019 := bstep (se 1 (by rfl) ⟨750014, by rfl⟩ : syracuseStep 1000019 = 1500029) B1500029
theorem B1688161 : Blo 996598 1688161 := bstep (se 2 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 1688161 = 1266121) B1266121
theorem B1000035 : Blo 996598 1000035 := bstep (se 1 (by rfl) ⟨750026, by rfl⟩ : syracuseStep 1000035 = 1500053) B1500053
theorem B1000051 : Blo 996598 1000051 := bstep (se 1 (by rfl) ⟨750038, by rfl⟩ : syracuseStep 1000051 = 1500077) B1500077
theorem B1000067 : Blo 996598 1000067 := bstep (se 1 (by rfl) ⟨750050, by rfl⟩ : syracuseStep 1000067 = 1500101) B1500101
theorem B1688195 : Blo 996598 1688195 := bstep (se 1 (by rfl) ⟨1266146, by rfl⟩ : syracuseStep 1688195 = 2532293) B2532293
theorem B5063309 : Blo 996598 5063309 := bstep (se 3 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 5063309 = 1898741) B1898741
theorem B2245265 : Blo 996598 2245265 := bstep (se 2 (by rfl) ⟨841974, by rfl⟩ : syracuseStep 2245265 = 1683949) B1683949
theorem B1000083 : Blo 996598 1000083 := bstep (se 1 (by rfl) ⟨750062, by rfl⟩ : syracuseStep 1000083 = 1500125) B1500125
theorem B1262243 : Blo 996598 1262243 := bstep (se 1 (by rfl) ⟨946682, by rfl⟩ : syracuseStep 1262243 = 1893365) B1893365
theorem B2245283 : Blo 996598 2245283 := bstep (se 1 (by rfl) ⟨1683962, by rfl⟩ : syracuseStep 2245283 = 3367925) B3367925
theorem B1000099 : Blo 996598 1000099 := bstep (se 1 (by rfl) ⟨750074, by rfl⟩ : syracuseStep 1000099 = 1500149) B1500149
theorem B3785393 : Blo 996598 3785393 := bstep (se 2 (by rfl) ⟨1419522, by rfl⟩ : syracuseStep 3785393 = 2839045) B2839045
theorem B2933425 : Blo 996598 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B1000115 : Blo 996598 1000115 := bstep (se 1 (by rfl) ⟨750086, by rfl⟩ : syracuseStep 1000115 = 1500173) B1500173
theorem B1000131 : Blo 996598 1000131 := bstep (se 1 (by rfl) ⟨750098, by rfl⟩ : syracuseStep 1000131 = 1500197) B1500197
theorem B1000147 : Blo 996598 1000147 := bstep (se 1 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 1000147 = 1500221) B1500221
theorem B1000163 : Blo 996598 1000163 := bstep (se 1 (by rfl) ⟨750122, by rfl⟩ : syracuseStep 1000163 = 1500245) B1500245
theorem B1000179 : Blo 996598 1000179 := bstep (se 1 (by rfl) ⟨750134, by rfl⟩ : syracuseStep 1000179 = 1500269) B1500269
theorem B1000195 : Blo 996598 1000195 := bstep (se 1 (by rfl) ⟨750146, by rfl⟩ : syracuseStep 1000195 = 1500293) B1500293
theorem B1688323 : Blo 996598 1688323 := bstep (se 1 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 1688323 = 2532485) B2532485
theorem B1000211 : Blo 996598 1000211 := bstep (se 1 (by rfl) ⟨750158, by rfl⟩ : syracuseStep 1000211 = 1500317) B1500317
theorem B1000227 : Blo 996598 1000227 := bstep (se 1 (by rfl) ⟨750170, by rfl⟩ : syracuseStep 1000227 = 1500341) B1500341
theorem B1000243 : Blo 996598 1000243 := bstep (se 1 (by rfl) ⟨750182, by rfl⟩ : syracuseStep 1000243 = 1500365) B1500365
theorem B1000259 : Blo 996598 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B1000275 : Blo 996598 1000275 := bstep (se 1 (by rfl) ⟨750206, by rfl⟩ : syracuseStep 1000275 = 1500413) B1500413
theorem B1000291 : Blo 996598 1000291 := bstep (se 1 (by rfl) ⟨750218, by rfl⟩ : syracuseStep 1000291 = 1500437) B1500437
theorem B1622897 : Blo 996598 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B1000307 : Blo 996598 1000307 := bstep (se 1 (by rfl) ⟨750230, by rfl⟩ : syracuseStep 1000307 = 1500461) B1500461
theorem B1000323 : Blo 996598 1000323 := bstep (se 1 (by rfl) ⟨750242, by rfl⟩ : syracuseStep 1000323 = 1500485) B1500485
theorem B2737037 : Blo 996598 2737037 := bstep (se 3 (by rfl) ⟨513194, by rfl⟩ : syracuseStep 2737037 = 1026389) B1026389
theorem B1688465 : Blo 996598 1688465 := bstep (se 2 (by rfl) ⟨633174, by rfl⟩ : syracuseStep 1688465 = 1266349) B1266349
theorem B1000339 : Blo 996598 1000339 := bstep (se 1 (by rfl) ⟨750254, by rfl⟩ : syracuseStep 1000339 = 1500509) B1500509
theorem B1000355 : Blo 996598 1000355 := bstep (se 1 (by rfl) ⟨750266, by rfl⟩ : syracuseStep 1000355 = 1500533) B1500533
theorem B2245553 : Blo 996598 2245553 := bstep (se 2 (by rfl) ⟨842082, by rfl⟩ : syracuseStep 2245553 = 1684165) B1684165
theorem B1000371 : Blo 996598 1000371 := bstep (se 1 (by rfl) ⟨750278, by rfl⟩ : syracuseStep 1000371 = 1500557) B1500557
theorem B2245571 : Blo 996598 2245571 := bstep (se 1 (by rfl) ⟨1684178, by rfl⟩ : syracuseStep 2245571 = 3368357) B3368357
theorem B1000387 : Blo 996598 1000387 := bstep (se 1 (by rfl) ⟨750290, by rfl⟩ : syracuseStep 1000387 = 1500581) B1500581
theorem B1000403 : Blo 996598 1000403 := bstep (se 1 (by rfl) ⟨750302, by rfl⟩ : syracuseStep 1000403 = 1500605) B1500605
theorem B3195875 : Blo 996598 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B1000419 : Blo 996598 1000419 := bstep (se 1 (by rfl) ⟨750314, by rfl⟩ : syracuseStep 1000419 = 1500629) B1500629
theorem B1000435 : Blo 996598 1000435 := bstep (se 1 (by rfl) ⟨750326, by rfl⟩ : syracuseStep 1000435 = 1500653) B1500653
theorem B1000451 : Blo 996598 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B1000467 : Blo 996598 1000467 := bstep (se 1 (by rfl) ⟨750350, by rfl⟩ : syracuseStep 1000467 = 1500701) B1500701
theorem B1000483 : Blo 996598 1000483 := bstep (se 1 (by rfl) ⟨750362, by rfl⟩ : syracuseStep 1000483 = 1500725) B1500725
theorem B1000499 : Blo 996598 1000499 := bstep (se 1 (by rfl) ⟨750374, by rfl⟩ : syracuseStep 1000499 = 1500749) B1500749
theorem B1000515 : Blo 996598 1000515 := bstep (se 1 (by rfl) ⟨750386, by rfl⟩ : syracuseStep 1000515 = 1500773) B1500773
theorem B1000531 : Blo 996598 1000531 := bstep (se 1 (by rfl) ⟨750398, by rfl⟩ : syracuseStep 1000531 = 1500797) B1500797
theorem B12797027 : Blo 996598 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B1000547 : Blo 996598 1000547 := bstep (se 1 (by rfl) ⟨750410, by rfl⟩ : syracuseStep 1000547 = 1500821) B1500821
theorem B25937009 : Blo 996598 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B1000563 : Blo 996598 1000563 := bstep (se 1 (by rfl) ⟨750422, by rfl⟩ : syracuseStep 1000563 = 1500845) B1500845
theorem B1000579 : Blo 996598 1000579 := bstep (se 1 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 1000579 = 1500869) B1500869
theorem B15352973 : Blo 996598 15352973 := bstep (se 3 (by rfl) ⟨2878682, by rfl⟩ : syracuseStep 15352973 = 5757365) B5757365
theorem B1000595 : Blo 996598 1000595 := bstep (se 1 (by rfl) ⟨750446, by rfl⟩ : syracuseStep 1000595 = 1500893) B1500893
theorem B2245841 : Blo 996598 2245841 := bstep (se 2 (by rfl) ⟨842190, by rfl⟩ : syracuseStep 2245841 = 1684381) B1684381
theorem B2245859 : Blo 996598 2245859 := bstep (se 1 (by rfl) ⟨1684394, by rfl⟩ : syracuseStep 2245859 = 3368789) B3368789
theorem B54740245 : Blo 996598 54740245 := bstep (se 6 (by rfl) ⟨1282974, by rfl⟩ : syracuseStep 54740245 = 2565949) B2565949
theorem B1951025 : Blo 996598 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B2737475 : Blo 996598 2737475 := bstep (se 1 (by rfl) ⟨2053106, by rfl⟩ : syracuseStep 2737475 = 4106213) B4106213
theorem B2082115 : Blo 996598 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B3786061 : Blo 996598 3786061 := bstep (se 3 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 3786061 = 1419773) B1419773
theorem B1262947 : Blo 996598 1262947 := bstep (se 1 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 1262947 = 1894421) B1894421
theorem B3032515 : Blo 996598 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B1263043 : Blo 996598 1263043 := bstep (se 1 (by rfl) ⟨947282, by rfl⟩ : syracuseStep 1263043 = 1894565) B1894565
theorem B2278865 : Blo 996598 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B2246129 : Blo 996598 2246129 := bstep (se 2 (by rfl) ⟨842298, by rfl⟩ : syracuseStep 2246129 = 1684597) B1684597
theorem B2246147 : Blo 996598 2246147 := bstep (se 1 (by rfl) ⟨1684610, by rfl⟩ : syracuseStep 2246147 = 3369221) B3369221
theorem B3196529 : Blo 996598 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B2246417 : Blo 996598 2246417 := bstep (se 2 (by rfl) ⟨842406, by rfl⟩ : syracuseStep 2246417 = 1684813) B1684813
theorem B2737937 : Blo 996598 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B2246435 : Blo 996598 2246435 := bstep (se 1 (by rfl) ⟨1684826, by rfl⟩ : syracuseStep 2246435 = 3369653) B3369653
theorem B6080305 : Blo 996598 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B8210317 : Blo 996598 8210317 := bstep (se 3 (by rfl) ⟨1539434, by rfl⟩ : syracuseStep 8210317 = 3078869) B3078869
theorem B1263539 : Blo 996598 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1066979 : Blo 996598 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B2050051 : Blo 996598 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B2246705 : Blo 996598 2246705 := bstep (se 2 (by rfl) ⟨842514, by rfl⟩ : syracuseStep 2246705 = 1685029) B1685029
theorem B2246723 : Blo 996598 2246723 := bstep (se 1 (by rfl) ⟨1685042, by rfl⟩ : syracuseStep 2246723 = 3370085) B3370085
theorem B3786851 : Blo 996598 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B6408305 : Blo 996598 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B6473861 : Blo 996598 6473861 := bstep (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) B1213849
theorem B6408355 : Blo 996598 6408355 := bstep (se 1 (by rfl) ⟨4806266, by rfl⟩ : syracuseStep 6408355 = 9612533) B9612533
theorem B2246993 : Blo 996598 2246993 := bstep (se 2 (by rfl) ⟨842622, by rfl⟩ : syracuseStep 2246993 = 1685245) B1685245
theorem B2247011 : Blo 996598 2247011 := bstep (se 1 (by rfl) ⟨1685258, by rfl⟩ : syracuseStep 2247011 = 3370517) B3370517
theorem B2247281 : Blo 996598 2247281 := bstep (se 2 (by rfl) ⟨842730, by rfl⟩ : syracuseStep 2247281 = 1685461) B1685461
theorem B1264243 : Blo 996598 1264243 := bstep (se 1 (by rfl) ⟨948182, by rfl⟩ : syracuseStep 1264243 = 1896365) B1896365
theorem B2247299 : Blo 996598 2247299 := bstep (se 1 (by rfl) ⟨1685474, by rfl⟩ : syracuseStep 2247299 = 3370949) B3370949
theorem B1264339 : Blo 996598 1264339 := bstep (se 1 (by rfl) ⟨948254, by rfl⟩ : syracuseStep 1264339 = 1896509) B1896509
theorem B3787505 : Blo 996598 3787505 := bstep (se 2 (by rfl) ⟨1420314, by rfl⟩ : syracuseStep 3787505 = 2840629) B2840629
theorem B2247569 : Blo 996598 2247569 := bstep (se 2 (by rfl) ⟨842838, by rfl⟩ : syracuseStep 2247569 = 1685677) B1685677
theorem B2247587 : Blo 996598 2247587 := bstep (se 1 (by rfl) ⟨1685690, by rfl⟩ : syracuseStep 2247587 = 3371381) B3371381
theorem B3197873 : Blo 996598 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B5753861 : Blo 996598 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B2247857 : Blo 996598 2247857 := bstep (se 2 (by rfl) ⟨842946, by rfl⟩ : syracuseStep 2247857 = 1685893) B1685893
theorem B2247875 : Blo 996598 2247875 := bstep (se 1 (by rfl) ⟨1685906, by rfl⟩ : syracuseStep 2247875 = 3371813) B3371813
theorem B1264835 : Blo 996598 1264835 := bstep (se 1 (by rfl) ⟨948626, by rfl⟩ : syracuseStep 1264835 = 1897253) B1897253
theorem B1199395 : Blo 996598 1199395 := bstep (se 1 (by rfl) ⟨899546, by rfl⟩ : syracuseStep 1199395 = 1799093) B1799093
theorem B5393861 : Blo 996598 5393861 := bstep (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) B1011349
theorem B2248145 : Blo 996598 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B2837987 : Blo 996598 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B2248163 : Blo 996598 2248163 := bstep (se 1 (by rfl) ⟨1686122, by rfl⟩ : syracuseStep 2248163 = 3372245) B3372245
theorem B2838179 : Blo 996598 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B2248433 : Blo 996598 2248433 := bstep (se 2 (by rfl) ⟨843162, by rfl⟩ : syracuseStep 2248433 = 1686325) B1686325
theorem B2248451 : Blo 996598 2248451 := bstep (se 1 (by rfl) ⟨1686338, by rfl⟩ : syracuseStep 2248451 = 3372677) B3372677
theorem B1494899 : Blo 996598 1494899 := bstep (se 1 (by rfl) ⟨1121174, by rfl⟩ : syracuseStep 1494899 = 2242349) B2242349
theorem B1265539 : Blo 996598 1265539 := bstep (se 1 (by rfl) ⟨949154, by rfl⟩ : syracuseStep 1265539 = 1898309) B1898309
theorem B1494929 : Blo 996598 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B1494947 : Blo 996598 1494947 := bstep (se 1 (by rfl) ⟨1121210, by rfl⟩ : syracuseStep 1494947 = 2242421) B2242421
theorem B1494977 : Blo 996598 1494977 := bstep (se 2 (by rfl) ⟨560616, by rfl⟩ : syracuseStep 1494977 = 1121233) B1121233
theorem B1494995 : Blo 996598 1494995 := bstep (se 1 (by rfl) ⟨1121246, by rfl⟩ : syracuseStep 1494995 = 2242493) B2242493
theorem B1265635 : Blo 996598 1265635 := bstep (se 1 (by rfl) ⟨949226, by rfl⟩ : syracuseStep 1265635 = 1898453) B1898453
theorem B1495025 : Blo 996598 1495025 := bstep (se 2 (by rfl) ⟨560634, by rfl⟩ : syracuseStep 1495025 = 1121269) B1121269
theorem B1495043 : Blo 996598 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B12144653 : Blo 996598 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B3198989 : Blo 996598 3198989 := bstep (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) B1199621
theorem B2248721 : Blo 996598 2248721 := bstep (se 2 (by rfl) ⟨843270, by rfl⟩ : syracuseStep 2248721 = 1686541) B1686541
theorem B1495073 : Blo 996598 1495073 := bstep (se 2 (by rfl) ⟨560652, by rfl⟩ : syracuseStep 1495073 = 1121305) B1121305
theorem B2248739 : Blo 996598 2248739 := bstep (se 1 (by rfl) ⟨1686554, by rfl⟩ : syracuseStep 2248739 = 3373109) B3373109
theorem B1495091 : Blo 996598 1495091 := bstep (se 1 (by rfl) ⟨1121318, by rfl⟩ : syracuseStep 1495091 = 2242637) B2242637
theorem B5394509 : Blo 996598 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B1495121 : Blo 996598 1495121 := bstep (se 2 (by rfl) ⟨560670, by rfl⟩ : syracuseStep 1495121 = 1121341) B1121341
theorem B1495139 : Blo 996598 1495139 := bstep (se 1 (by rfl) ⟨1121354, by rfl⟩ : syracuseStep 1495139 = 2242709) B2242709
theorem B1495169 : Blo 996598 1495169 := bstep (se 2 (by rfl) ⟨560688, by rfl⟩ : syracuseStep 1495169 = 1121377) B1121377
theorem B1495187 : Blo 996598 1495187 := bstep (se 1 (by rfl) ⟨1121390, by rfl⟩ : syracuseStep 1495187 = 2242781) B2242781
theorem B5394595 : Blo 996598 5394595 := bstep (se 1 (by rfl) ⟨4045946, by rfl⟩ : syracuseStep 5394595 = 8091893) B8091893
theorem B3788963 : Blo 996598 3788963 := bstep (se 1 (by rfl) ⟨2841722, by rfl⟩ : syracuseStep 3788963 = 5683445) B5683445
theorem B1495217 : Blo 996598 1495217 := bstep (se 2 (by rfl) ⟨560706, by rfl⟩ : syracuseStep 1495217 = 1121413) B1121413
theorem B3788977 : Blo 996598 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B1495235 : Blo 996598 1495235 := bstep (se 1 (by rfl) ⟨1121426, by rfl⟩ : syracuseStep 1495235 = 2242853) B2242853
theorem B1495265 : Blo 996598 1495265 := bstep (se 2 (by rfl) ⟨560724, by rfl⟩ : syracuseStep 1495265 = 1121449) B1121449
theorem B1495283 : Blo 996598 1495283 := bstep (se 1 (by rfl) ⟨1121462, by rfl⟩ : syracuseStep 1495283 = 2242925) B2242925
theorem B1495313 : Blo 996598 1495313 := bstep (se 2 (by rfl) ⟨560742, by rfl⟩ : syracuseStep 1495313 = 1121485) B1121485
theorem B1495331 : Blo 996598 1495331 := bstep (se 1 (by rfl) ⟨1121498, by rfl⟩ : syracuseStep 1495331 = 2242997) B2242997
theorem B2249009 : Blo 996598 2249009 := bstep (se 2 (by rfl) ⟨843378, by rfl⟩ : syracuseStep 2249009 = 1686757) B1686757
theorem B1495361 : Blo 996598 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B2249027 : Blo 996598 2249027 := bstep (se 1 (by rfl) ⟨1686770, by rfl⟩ : syracuseStep 2249027 = 3373541) B3373541
theorem B1495379 : Blo 996598 1495379 := bstep (se 1 (by rfl) ⟨1121534, by rfl⟩ : syracuseStep 1495379 = 2243069) B2243069
theorem B1200467 : Blo 996598 1200467 := bstep (se 1 (by rfl) ⟨900350, by rfl⟩ : syracuseStep 1200467 = 1800701) B1800701
theorem B1495409 : Blo 996598 1495409 := bstep (se 2 (by rfl) ⟨560778, by rfl⟩ : syracuseStep 1495409 = 1121557) B1121557
theorem B1495427 : Blo 996598 1495427 := bstep (se 1 (by rfl) ⟨1121570, by rfl⟩ : syracuseStep 1495427 = 2243141) B2243141
theorem B1495457 : Blo 996598 1495457 := bstep (se 2 (by rfl) ⟨560796, by rfl⟩ : syracuseStep 1495457 = 1121593) B1121593
theorem B1495475 : Blo 996598 1495475 := bstep (se 1 (by rfl) ⟨1121606, by rfl⟩ : syracuseStep 1495475 = 2243213) B2243213
theorem B2838989 : Blo 996598 2838989 := bstep (se 3 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 2838989 = 1064621) B1064621
theorem B1495505 : Blo 996598 1495505 := bstep (se 2 (by rfl) ⟨560814, by rfl⟩ : syracuseStep 1495505 = 1121629) B1121629
theorem B1266131 : Blo 996598 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B1495523 : Blo 996598 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B1495553 : Blo 996598 1495553 := bstep (se 2 (by rfl) ⟨560832, by rfl⟩ : syracuseStep 1495553 = 1121665) B1121665
theorem B6410765 : Blo 996598 6410765 := bstep (se 3 (by rfl) ⟨1202018, by rfl⟩ : syracuseStep 6410765 = 2404037) B2404037
theorem B1495571 : Blo 996598 1495571 := bstep (se 1 (by rfl) ⟨1121678, by rfl⟩ : syracuseStep 1495571 = 2243357) B2243357
theorem B1495601 : Blo 996598 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B1495619 : Blo 996598 1495619 := bstep (se 1 (by rfl) ⟨1121714, by rfl⟩ : syracuseStep 1495619 = 2243429) B2243429
theorem B2249297 : Blo 996598 2249297 := bstep (se 2 (by rfl) ⟨843486, by rfl⟩ : syracuseStep 2249297 = 1686973) B1686973
theorem B1495649 : Blo 996598 1495649 := bstep (se 2 (by rfl) ⟨560868, by rfl⟩ : syracuseStep 1495649 = 1121737) B1121737
theorem B2249315 : Blo 996598 2249315 := bstep (se 1 (by rfl) ⟨1686986, by rfl⟩ : syracuseStep 2249315 = 3373973) B3373973
theorem B1495667 : Blo 996598 1495667 := bstep (se 1 (by rfl) ⟨1121750, by rfl⟩ : syracuseStep 1495667 = 2243501) B2243501
theorem B2839171 : Blo 996598 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B1495697 : Blo 996598 1495697 := bstep (se 2 (by rfl) ⟨560886, by rfl⟩ : syracuseStep 1495697 = 1121773) B1121773
theorem B1495715 : Blo 996598 1495715 := bstep (se 1 (by rfl) ⟨1121786, by rfl⟩ : syracuseStep 1495715 = 2243573) B2243573
theorem B1495745 : Blo 996598 1495745 := bstep (se 2 (by rfl) ⟨560904, by rfl⟩ : syracuseStep 1495745 = 1121809) B1121809
theorem B1495763 : Blo 996598 1495763 := bstep (se 1 (by rfl) ⟨1121822, by rfl⟩ : syracuseStep 1495763 = 2243645) B2243645
theorem B1495793 : Blo 996598 1495793 := bstep (se 2 (by rfl) ⟨560922, by rfl⟩ : syracuseStep 1495793 = 1121845) B1121845
theorem B1495811 : Blo 996598 1495811 := bstep (se 1 (by rfl) ⟨1121858, by rfl⟩ : syracuseStep 1495811 = 2243717) B2243717
theorem B1495841 : Blo 996598 1495841 := bstep (se 2 (by rfl) ⟨560940, by rfl⟩ : syracuseStep 1495841 = 1121881) B1121881
theorem B5133091 : Blo 996598 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B1495859 : Blo 996598 1495859 := bstep (se 1 (by rfl) ⟨1121894, by rfl⟩ : syracuseStep 1495859 = 2243789) B2243789
theorem B1495889 : Blo 996598 1495889 := bstep (se 2 (by rfl) ⟨560958, by rfl⟩ : syracuseStep 1495889 = 1121917) B1121917
theorem B1495907 : Blo 996598 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B2249585 : Blo 996598 2249585 := bstep (se 2 (by rfl) ⟨843594, by rfl⟩ : syracuseStep 2249585 = 1687189) B1687189
theorem B1495937 : Blo 996598 1495937 := bstep (se 2 (by rfl) ⟨560976, by rfl⟩ : syracuseStep 1495937 = 1121953) B1121953
theorem B2249603 : Blo 996598 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B17027981 : Blo 996598 17027981 := bstep (se 3 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 17027981 = 6385493) B6385493
theorem B1495955 : Blo 996598 1495955 := bstep (se 1 (by rfl) ⟨1121966, by rfl⟩ : syracuseStep 1495955 = 2243933) B2243933
theorem B1495985 : Blo 996598 1495985 := bstep (se 2 (by rfl) ⟨560994, by rfl⟩ : syracuseStep 1495985 = 1121989) B1121989
theorem B1496003 : Blo 996598 1496003 := bstep (se 1 (by rfl) ⟨1122002, by rfl⟩ : syracuseStep 1496003 = 2244005) B2244005
theorem B8541125 : Blo 996598 8541125 := bstep (se 4 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 8541125 = 1601461) B1601461
theorem B1496033 : Blo 996598 1496033 := bstep (se 2 (by rfl) ⟨561012, by rfl⟩ : syracuseStep 1496033 = 1122025) B1122025
theorem B3363821 : Blo 996598 3363821 := bstep (se 3 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 3363821 = 1261433) B1261433
theorem B1496051 : Blo 996598 1496051 := bstep (se 1 (by rfl) ⟨1122038, by rfl⟩ : syracuseStep 1496051 = 2244077) B2244077
theorem B1496081 : Blo 996598 1496081 := bstep (se 2 (by rfl) ⟨561030, by rfl⟩ : syracuseStep 1496081 = 1122061) B1122061
theorem B1496099 : Blo 996598 1496099 := bstep (se 1 (by rfl) ⟨1122074, by rfl⟩ : syracuseStep 1496099 = 2244149) B2244149
theorem B3363875 : Blo 996598 3363875 := bstep (se 1 (by rfl) ⟨2522906, by rfl⟩ : syracuseStep 3363875 = 5045813) B5045813
theorem B1496129 : Blo 996598 1496129 := bstep (se 2 (by rfl) ⟨561048, by rfl⟩ : syracuseStep 1496129 = 1122097) B1122097
theorem B3200077 : Blo 996598 3200077 := bstep (se 3 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 3200077 = 1200029) B1200029
theorem B1496147 : Blo 996598 1496147 := bstep (se 1 (by rfl) ⟨1122110, by rfl⟩ : syracuseStep 1496147 = 2244221) B2244221
theorem B2839661 : Blo 996598 2839661 := bstep (se 3 (by rfl) ⟨532436, by rfl⟩ : syracuseStep 2839661 = 1064873) B1064873
theorem B1496177 : Blo 996598 1496177 := bstep (se 2 (by rfl) ⟨561066, by rfl⟩ : syracuseStep 1496177 = 1122133) B1122133
theorem B1496195 : Blo 996598 1496195 := bstep (se 1 (by rfl) ⟨1122146, by rfl⟩ : syracuseStep 1496195 = 2244293) B2244293
theorem B2249873 : Blo 996598 2249873 := bstep (se 2 (by rfl) ⟨843702, by rfl⟩ : syracuseStep 2249873 = 1687405) B1687405
theorem B1496225 : Blo 996598 1496225 := bstep (se 2 (by rfl) ⟨561084, by rfl⟩ : syracuseStep 1496225 = 1122169) B1122169
theorem B2249891 : Blo 996598 2249891 := bstep (se 1 (by rfl) ⟨1687418, by rfl⟩ : syracuseStep 2249891 = 3374837) B3374837
theorem B2741411 : Blo 996598 2741411 := bstep (se 1 (by rfl) ⟨2056058, by rfl⟩ : syracuseStep 2741411 = 4112117) B4112117
theorem B1496243 : Blo 996598 1496243 := bstep (se 1 (by rfl) ⟨1122182, by rfl⟩ : syracuseStep 1496243 = 2244365) B2244365
theorem B1496273 : Blo 996598 1496273 := bstep (se 2 (by rfl) ⟨561102, by rfl⟩ : syracuseStep 1496273 = 1122205) B1122205
theorem B1496291 : Blo 996598 1496291 := bstep (se 1 (by rfl) ⟨1122218, by rfl⟩ : syracuseStep 1496291 = 2244437) B2244437
theorem B1496321 : Blo 996598 1496321 := bstep (se 2 (by rfl) ⟨561120, by rfl⟩ : syracuseStep 1496321 = 1122241) B1122241
theorem B1496339 : Blo 996598 1496339 := bstep (se 1 (by rfl) ⟨1122254, by rfl⟩ : syracuseStep 1496339 = 2244509) B2244509
theorem B3364145 : Blo 996598 3364145 := bstep (se 2 (by rfl) ⟨1261554, by rfl⟩ : syracuseStep 3364145 = 2523109) B2523109
theorem B1496369 : Blo 996598 1496369 := bstep (se 2 (by rfl) ⟨561138, by rfl⟩ : syracuseStep 1496369 = 1122277) B1122277
theorem B1496387 : Blo 996598 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B1496417 : Blo 996598 1496417 := bstep (se 2 (by rfl) ⟨561156, by rfl⟩ : syracuseStep 1496417 = 1122313) B1122313
theorem B1496435 : Blo 996598 1496435 := bstep (se 1 (by rfl) ⟨1122326, by rfl⟩ : syracuseStep 1496435 = 2244653) B2244653
theorem B5133709 : Blo 996598 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1496465 : Blo 996598 1496465 := bstep (se 2 (by rfl) ⟨561174, by rfl⟩ : syracuseStep 1496465 = 1122349) B1122349
theorem B1496483 : Blo 996598 1496483 := bstep (se 1 (by rfl) ⟨1122362, by rfl⟩ : syracuseStep 1496483 = 2244725) B2244725
theorem B2250161 : Blo 996598 2250161 := bstep (se 2 (by rfl) ⟨843810, by rfl⟩ : syracuseStep 2250161 = 1687621) B1687621
theorem B1496513 : Blo 996598 1496513 := bstep (se 2 (by rfl) ⟨561192, by rfl⟩ : syracuseStep 1496513 = 1122385) B1122385
theorem B2250179 : Blo 996598 2250179 := bstep (se 1 (by rfl) ⟨1687634, by rfl⟩ : syracuseStep 2250179 = 3375269) B3375269
theorem B1496531 : Blo 996598 1496531 := bstep (se 1 (by rfl) ⟨1122398, by rfl⟩ : syracuseStep 1496531 = 2244797) B2244797
theorem B1496561 : Blo 996598 1496561 := bstep (se 2 (by rfl) ⟨561210, by rfl⟩ : syracuseStep 1496561 = 1122421) B1122421
theorem B1496579 : Blo 996598 1496579 := bstep (se 1 (by rfl) ⟨1122434, by rfl⟩ : syracuseStep 1496579 = 2244869) B2244869
theorem B1496609 : Blo 996598 1496609 := bstep (se 2 (by rfl) ⟨561228, by rfl⟩ : syracuseStep 1496609 = 1122457) B1122457
theorem B1496627 : Blo 996598 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B1496657 : Blo 996598 1496657 := bstep (se 2 (by rfl) ⟨561246, by rfl⟩ : syracuseStep 1496657 = 1122493) B1122493
theorem B1496675 : Blo 996598 1496675 := bstep (se 1 (by rfl) ⟨1122506, by rfl⟩ : syracuseStep 1496675 = 2245013) B2245013
theorem B3790435 : Blo 996598 3790435 := bstep (se 1 (by rfl) ⟨2842826, by rfl⟩ : syracuseStep 3790435 = 5685653) B5685653
theorem B1496705 : Blo 996598 1496705 := bstep (se 2 (by rfl) ⟨561264, by rfl⟩ : syracuseStep 1496705 = 1122529) B1122529
theorem B1496723 : Blo 996598 1496723 := bstep (se 1 (by rfl) ⟨1122542, by rfl⟩ : syracuseStep 1496723 = 2245085) B2245085
theorem B1496753 : Blo 996598 1496753 := bstep (se 2 (by rfl) ⟨561282, by rfl⟩ : syracuseStep 1496753 = 1122565) B1122565
theorem B1496771 : Blo 996598 1496771 := bstep (se 1 (by rfl) ⟨1122578, by rfl⟩ : syracuseStep 1496771 = 2245157) B2245157
theorem B2250449 : Blo 996598 2250449 := bstep (se 2 (by rfl) ⟨843918, by rfl⟩ : syracuseStep 2250449 = 1687837) B1687837
theorem B1496801 : Blo 996598 1496801 := bstep (se 2 (by rfl) ⟨561300, by rfl⟩ : syracuseStep 1496801 = 1122601) B1122601
theorem B2250467 : Blo 996598 2250467 := bstep (se 1 (by rfl) ⟨1687850, by rfl⟩ : syracuseStep 2250467 = 3375701) B3375701
theorem B1496819 : Blo 996598 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B1496849 : Blo 996598 1496849 := bstep (se 2 (by rfl) ⟨561318, by rfl⟩ : syracuseStep 1496849 = 1122637) B1122637
theorem B1496867 : Blo 996598 1496867 := bstep (se 1 (by rfl) ⟨1122650, by rfl⟩ : syracuseStep 1496867 = 2245301) B2245301
theorem B1496897 : Blo 996598 1496897 := bstep (se 2 (by rfl) ⟨561336, by rfl⟩ : syracuseStep 1496897 = 1122673) B1122673
theorem B3364685 : Blo 996598 3364685 := bstep (se 3 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 3364685 = 1261757) B1261757
theorem B3594061 : Blo 996598 3594061 := bstep (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) B1347773
theorem B1496915 : Blo 996598 1496915 := bstep (se 1 (by rfl) ⟨1122686, by rfl⟩ : syracuseStep 1496915 = 2245373) B2245373
theorem B1496945 : Blo 996598 1496945 := bstep (se 2 (by rfl) ⟨561354, by rfl⟩ : syracuseStep 1496945 = 1122709) B1122709
theorem B3364739 : Blo 996598 3364739 := bstep (se 1 (by rfl) ⟨2523554, by rfl⟩ : syracuseStep 3364739 = 5047109) B5047109
theorem B1496963 : Blo 996598 1496963 := bstep (se 1 (by rfl) ⟨1122722, by rfl⟩ : syracuseStep 1496963 = 2245445) B2245445
theorem B1496993 : Blo 996598 1496993 := bstep (se 2 (by rfl) ⟨561372, by rfl⟩ : syracuseStep 1496993 = 1122745) B1122745
theorem B1497011 : Blo 996598 1497011 := bstep (se 1 (by rfl) ⟨1122758, by rfl⟩ : syracuseStep 1497011 = 2245517) B2245517
theorem B1497041 : Blo 996598 1497041 := bstep (se 2 (by rfl) ⟨561390, by rfl⟩ : syracuseStep 1497041 = 1122781) B1122781
theorem B1497059 : Blo 996598 1497059 := bstep (se 1 (by rfl) ⟨1122794, by rfl⟩ : syracuseStep 1497059 = 2245589) B2245589
theorem B2250737 : Blo 996598 2250737 := bstep (se 2 (by rfl) ⟨844026, by rfl⟩ : syracuseStep 2250737 = 1688053) B1688053
theorem B1497089 : Blo 996598 1497089 := bstep (se 2 (by rfl) ⟨561408, by rfl⟩ : syracuseStep 1497089 = 1122817) B1122817
theorem B2250755 : Blo 996598 2250755 := bstep (se 1 (by rfl) ⟨1688066, by rfl⟩ : syracuseStep 2250755 = 3376133) B3376133
theorem B1497107 : Blo 996598 1497107 := bstep (se 1 (by rfl) ⟨1122830, by rfl⟩ : syracuseStep 1497107 = 2245661) B2245661
theorem B1497137 : Blo 996598 1497137 := bstep (se 2 (by rfl) ⟨561426, by rfl⟩ : syracuseStep 1497137 = 1122853) B1122853
theorem B1497155 : Blo 996598 1497155 := bstep (se 1 (by rfl) ⟨1122866, by rfl⟩ : syracuseStep 1497155 = 2245733) B2245733
theorem B1497185 : Blo 996598 1497185 := bstep (se 2 (by rfl) ⟨561444, by rfl⟩ : syracuseStep 1497185 = 1122889) B1122889
theorem B1497203 : Blo 996598 1497203 := bstep (se 1 (by rfl) ⟨1122902, by rfl⟩ : syracuseStep 1497203 = 2245805) B2245805
theorem B1923203 : Blo 996598 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B5462149 : Blo 996598 5462149 := bstep (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) B1024153
theorem B3365009 : Blo 996598 3365009 := bstep (se 2 (by rfl) ⟨1261878, by rfl⟩ : syracuseStep 3365009 = 2523757) B2523757
theorem B1497233 : Blo 996598 1497233 := bstep (se 2 (by rfl) ⟨561462, by rfl⟩ : syracuseStep 1497233 = 1122925) B1122925
theorem B1497251 : Blo 996598 1497251 := bstep (se 1 (by rfl) ⟨1122938, by rfl⟩ : syracuseStep 1497251 = 2245877) B2245877
theorem B1497281 : Blo 996598 1497281 := bstep (se 2 (by rfl) ⟨561480, by rfl⟩ : syracuseStep 1497281 = 1122961) B1122961
theorem B1497299 : Blo 996598 1497299 := bstep (se 1 (by rfl) ⟨1122974, by rfl⟩ : syracuseStep 1497299 = 2245949) B2245949
theorem B1497329 : Blo 996598 1497329 := bstep (se 2 (by rfl) ⟨561498, by rfl⟩ : syracuseStep 1497329 = 1122997) B1122997
theorem B1497347 : Blo 996598 1497347 := bstep (se 1 (by rfl) ⟨1123010, by rfl⟩ : syracuseStep 1497347 = 2246021) B2246021
theorem B2840845 : Blo 996598 2840845 := bstep (se 3 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 2840845 = 1065317) B1065317
theorem B2251025 : Blo 996598 2251025 := bstep (se 2 (by rfl) ⟨844134, by rfl⟩ : syracuseStep 2251025 = 1688269) B1688269
theorem B1497377 : Blo 996598 1497377 := bstep (se 2 (by rfl) ⟨561516, by rfl⟩ : syracuseStep 1497377 = 1123033) B1123033
theorem B2251043 : Blo 996598 2251043 := bstep (se 1 (by rfl) ⟨1688282, by rfl⟩ : syracuseStep 2251043 = 3376565) B3376565
theorem B1497395 : Blo 996598 1497395 := bstep (se 1 (by rfl) ⟨1123046, by rfl⟩ : syracuseStep 1497395 = 2246093) B2246093
theorem B1497425 : Blo 996598 1497425 := bstep (se 2 (by rfl) ⟨561534, by rfl⟩ : syracuseStep 1497425 = 1123069) B1123069
theorem B1497443 : Blo 996598 1497443 := bstep (se 1 (by rfl) ⟨1123082, by rfl⟩ : syracuseStep 1497443 = 2246165) B2246165
theorem B7592291 : Blo 996598 7592291 := bstep (se 1 (by rfl) ⟨5694218, by rfl⟩ : syracuseStep 7592291 = 11388437) B11388437
theorem B1497473 : Blo 996598 1497473 := bstep (se 2 (by rfl) ⟨561552, by rfl⟩ : syracuseStep 1497473 = 1123105) B1123105
theorem B1497491 : Blo 996598 1497491 := bstep (se 1 (by rfl) ⟨1123118, by rfl⟩ : syracuseStep 1497491 = 2246237) B2246237
theorem B1497521 : Blo 996598 1497521 := bstep (se 2 (by rfl) ⟨561570, by rfl⟩ : syracuseStep 1497521 = 1123141) B1123141
theorem B1497539 : Blo 996598 1497539 := bstep (se 1 (by rfl) ⟨1123154, by rfl⟩ : syracuseStep 1497539 = 2246309) B2246309
theorem B1497569 : Blo 996598 1497569 := bstep (se 2 (by rfl) ⟨561588, by rfl⟩ : syracuseStep 1497569 = 1123177) B1123177
theorem B1497587 : Blo 996598 1497587 := bstep (se 1 (by rfl) ⟨1123190, by rfl⟩ : syracuseStep 1497587 = 2246381) B2246381
theorem B3037709 : Blo 996598 3037709 := bstep (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) B1139141
theorem B1497617 : Blo 996598 1497617 := bstep (se 2 (by rfl) ⟨561606, by rfl⟩ : syracuseStep 1497617 = 1123213) B1123213
theorem B1497635 : Blo 996598 1497635 := bstep (se 1 (by rfl) ⟨1123226, by rfl⟩ : syracuseStep 1497635 = 2246453) B2246453
theorem B2251313 : Blo 996598 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B1497665 : Blo 996598 1497665 := bstep (se 2 (by rfl) ⟨561624, by rfl⟩ : syracuseStep 1497665 = 1123249) B1123249
theorem B2251331 : Blo 996598 2251331 := bstep (se 1 (by rfl) ⟨1688498, by rfl⟩ : syracuseStep 2251331 = 3376997) B3376997
theorem B1497683 : Blo 996598 1497683 := bstep (se 1 (by rfl) ⟨1123262, by rfl⟩ : syracuseStep 1497683 = 2246525) B2246525
theorem B1497713 : Blo 996598 1497713 := bstep (se 2 (by rfl) ⟨561642, by rfl⟩ : syracuseStep 1497713 = 1123285) B1123285
theorem B1497731 : Blo 996598 1497731 := bstep (se 1 (by rfl) ⟨1123298, by rfl⟩ : syracuseStep 1497731 = 2246597) B2246597
theorem B1497761 : Blo 996598 1497761 := bstep (se 2 (by rfl) ⟨561660, by rfl⟩ : syracuseStep 1497761 = 1123321) B1123321
theorem B3365549 : Blo 996598 3365549 := bstep (se 3 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 3365549 = 1262081) B1262081
theorem B1497779 : Blo 996598 1497779 := bstep (se 1 (by rfl) ⟨1123334, by rfl⟩ : syracuseStep 1497779 = 2246669) B2246669
theorem B1497809 : Blo 996598 1497809 := bstep (se 2 (by rfl) ⟨561678, by rfl⟩ : syracuseStep 1497809 = 1123357) B1123357
theorem B3365603 : Blo 996598 3365603 := bstep (se 1 (by rfl) ⟨2524202, by rfl⟩ : syracuseStep 3365603 = 5048405) B5048405
theorem B1497827 : Blo 996598 1497827 := bstep (se 1 (by rfl) ⟨1123370, by rfl⟩ : syracuseStep 1497827 = 2246741) B2246741
theorem B1497857 : Blo 996598 1497857 := bstep (se 2 (by rfl) ⟨561696, by rfl⟩ : syracuseStep 1497857 = 1123393) B1123393
theorem B1497875 : Blo 996598 1497875 := bstep (se 1 (by rfl) ⟨1123406, by rfl⟩ : syracuseStep 1497875 = 2246813) B2246813
theorem B1497905 : Blo 996598 1497905 := bstep (se 2 (by rfl) ⟨561714, by rfl⟩ : syracuseStep 1497905 = 1123429) B1123429
theorem B1497923 : Blo 996598 1497923 := bstep (se 1 (by rfl) ⟨1123442, by rfl⟩ : syracuseStep 1497923 = 2246885) B2246885
theorem B3201859 : Blo 996598 3201859 := bstep (se 1 (by rfl) ⟨2401394, by rfl⟩ : syracuseStep 3201859 = 4802789) B4802789
theorem B1497953 : Blo 996598 1497953 := bstep (se 2 (by rfl) ⟨561732, by rfl⟩ : syracuseStep 1497953 = 1123465) B1123465
theorem B1497971 : Blo 996598 1497971 := bstep (se 1 (by rfl) ⟨1123478, by rfl⟩ : syracuseStep 1497971 = 2246957) B2246957
theorem B3201923 : Blo 996598 3201923 := bstep (se 1 (by rfl) ⟨2401442, by rfl⟩ : syracuseStep 3201923 = 4802885) B4802885
theorem B1137539 : Blo 996598 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B1498001 : Blo 996598 1498001 := bstep (se 2 (by rfl) ⟨561750, by rfl⟩ : syracuseStep 1498001 = 1123501) B1123501
theorem B1498019 : Blo 996598 1498019 := bstep (se 1 (by rfl) ⟨1123514, by rfl⟩ : syracuseStep 1498019 = 2247029) B2247029
theorem B1498049 : Blo 996598 1498049 := bstep (se 2 (by rfl) ⟨561768, by rfl⟩ : syracuseStep 1498049 = 1123537) B1123537
theorem B3202001 : Blo 996598 3202001 := bstep (se 2 (by rfl) ⟨1200750, by rfl⟩ : syracuseStep 3202001 = 2401501) B2401501
theorem B1498067 : Blo 996598 1498067 := bstep (se 1 (by rfl) ⟨1123550, by rfl⟩ : syracuseStep 1498067 = 2247101) B2247101
theorem B3365873 : Blo 996598 3365873 := bstep (se 2 (by rfl) ⟨1262202, by rfl⟩ : syracuseStep 3365873 = 2524405) B2524405
theorem B1498097 : Blo 996598 1498097 := bstep (se 2 (by rfl) ⟨561786, by rfl⟩ : syracuseStep 1498097 = 1123573) B1123573
theorem B1498115 : Blo 996598 1498115 := bstep (se 1 (by rfl) ⟨1123586, by rfl⟩ : syracuseStep 1498115 = 2247173) B2247173
theorem B1498145 : Blo 996598 1498145 := bstep (se 2 (by rfl) ⟨561804, by rfl⟩ : syracuseStep 1498145 = 1123609) B1123609
theorem B1596451 : Blo 996598 1596451 := bstep (se 1 (by rfl) ⟨1197338, by rfl⟩ : syracuseStep 1596451 = 2394677) B2394677
theorem B1498163 : Blo 996598 1498163 := bstep (se 1 (by rfl) ⟨1123622, by rfl⟩ : syracuseStep 1498163 = 2247245) B2247245
theorem B1498193 : Blo 996598 1498193 := bstep (se 2 (by rfl) ⟨561822, by rfl⟩ : syracuseStep 1498193 = 1123645) B1123645
theorem B1498211 : Blo 996598 1498211 := bstep (se 1 (by rfl) ⟨1123658, by rfl⟩ : syracuseStep 1498211 = 2247317) B2247317
theorem B1498241 : Blo 996598 1498241 := bstep (se 2 (by rfl) ⟨561840, by rfl⟩ : syracuseStep 1498241 = 1123681) B1123681
theorem B2022545 : Blo 996598 2022545 := bstep (se 2 (by rfl) ⟨758454, by rfl⟩ : syracuseStep 2022545 = 1516909) B1516909
theorem B1498259 : Blo 996598 1498259 := bstep (se 1 (by rfl) ⟨1123694, by rfl⟩ : syracuseStep 1498259 = 2247389) B2247389
theorem B1498289 : Blo 996598 1498289 := bstep (se 2 (by rfl) ⟨561858, by rfl⟩ : syracuseStep 1498289 = 1123717) B1123717
theorem B1498307 : Blo 996598 1498307 := bstep (se 1 (by rfl) ⟨1123730, by rfl⟩ : syracuseStep 1498307 = 2247461) B2247461
theorem B1498337 : Blo 996598 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B1498355 : Blo 996598 1498355 := bstep (se 1 (by rfl) ⟨1123766, by rfl⟩ : syracuseStep 1498355 = 2247533) B2247533
theorem B1498385 : Blo 996598 1498385 := bstep (se 2 (by rfl) ⟨561894, by rfl⟩ : syracuseStep 1498385 = 1123789) B1123789
theorem B1498403 : Blo 996598 1498403 := bstep (se 1 (by rfl) ⟨1123802, by rfl⟩ : syracuseStep 1498403 = 2247605) B2247605
theorem B2841905 : Blo 996598 2841905 := bstep (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) B2131429
theorem B1498433 : Blo 996598 1498433 := bstep (se 2 (by rfl) ⟨561912, by rfl⟩ : syracuseStep 1498433 = 1123825) B1123825
theorem B1498451 : Blo 996598 1498451 := bstep (se 1 (by rfl) ⟨1123838, by rfl⟩ : syracuseStep 1498451 = 2247677) B2247677
theorem B1498481 : Blo 996598 1498481 := bstep (se 2 (by rfl) ⟨561930, by rfl⟩ : syracuseStep 1498481 = 1123861) B1123861
theorem B1498499 : Blo 996598 1498499 := bstep (se 1 (by rfl) ⟨1123874, by rfl⟩ : syracuseStep 1498499 = 2247749) B2247749
theorem B1498529 : Blo 996598 1498529 := bstep (se 2 (by rfl) ⟨561948, by rfl⟩ : syracuseStep 1498529 = 1123897) B1123897
theorem B1596835 : Blo 996598 1596835 := bstep (se 1 (by rfl) ⟨1197626, by rfl⟩ : syracuseStep 1596835 = 2395253) B2395253
theorem B1498547 : Blo 996598 1498547 := bstep (se 1 (by rfl) ⟨1123910, by rfl⟩ : syracuseStep 1498547 = 2247821) B2247821
theorem B1498577 : Blo 996598 1498577 := bstep (se 2 (by rfl) ⟨561966, by rfl⟩ : syracuseStep 1498577 = 1123933) B1123933
theorem B1498595 : Blo 996598 1498595 := bstep (se 1 (by rfl) ⟨1123946, by rfl⟩ : syracuseStep 1498595 = 2247893) B2247893
theorem B1498625 : Blo 996598 1498625 := bstep (se 2 (by rfl) ⟨561984, by rfl⟩ : syracuseStep 1498625 = 1123969) B1123969
theorem B3366413 : Blo 996598 3366413 := bstep (se 3 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 3366413 = 1262405) B1262405
theorem B1498643 : Blo 996598 1498643 := bstep (se 1 (by rfl) ⟨1123982, by rfl⟩ : syracuseStep 1498643 = 2247965) B2247965
theorem B1498673 : Blo 996598 1498673 := bstep (se 2 (by rfl) ⟨562002, by rfl⟩ : syracuseStep 1498673 = 1124005) B1124005
theorem B3366467 : Blo 996598 3366467 := bstep (se 1 (by rfl) ⟨2524850, by rfl⟩ : syracuseStep 3366467 = 5049701) B5049701
theorem B1498691 : Blo 996598 1498691 := bstep (se 1 (by rfl) ⟨1124018, by rfl⟩ : syracuseStep 1498691 = 2248037) B2248037
theorem B1498721 : Blo 996598 1498721 := bstep (se 2 (by rfl) ⟨562020, by rfl⟩ : syracuseStep 1498721 = 1124041) B1124041
theorem B1498739 : Blo 996598 1498739 := bstep (se 1 (by rfl) ⟨1124054, by rfl⟩ : syracuseStep 1498739 = 2248109) B2248109
theorem B1498769 : Blo 996598 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B1597091 : Blo 996598 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B1498787 : Blo 996598 1498787 := bstep (se 1 (by rfl) ⟨1124090, by rfl⟩ : syracuseStep 1498787 = 2248181) B2248181
theorem B4054691 : Blo 996598 4054691 := bstep (se 1 (by rfl) ⟨3041018, by rfl⟩ : syracuseStep 4054691 = 6082037) B6082037
theorem B1498817 : Blo 996598 1498817 := bstep (se 2 (by rfl) ⟨562056, by rfl⟩ : syracuseStep 1498817 = 1124113) B1124113
theorem B5693125 : Blo 996598 5693125 := bstep (se 4 (by rfl) ⟨533730, by rfl⟩ : syracuseStep 5693125 = 1067461) B1067461
theorem B1498835 : Blo 996598 1498835 := bstep (se 1 (by rfl) ⟨1124126, by rfl⟩ : syracuseStep 1498835 = 2248253) B2248253
theorem B1498865 : Blo 996598 1498865 := bstep (se 2 (by rfl) ⟨562074, by rfl⟩ : syracuseStep 1498865 = 1124149) B1124149
theorem B1498883 : Blo 996598 1498883 := bstep (se 1 (by rfl) ⟨1124162, by rfl⟩ : syracuseStep 1498883 = 2248325) B2248325
theorem B3792653 : Blo 996598 3792653 := bstep (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) B1422245
theorem B1498913 : Blo 996598 1498913 := bstep (se 2 (by rfl) ⟨562092, by rfl⟩ : syracuseStep 1498913 = 1124185) B1124185
theorem B1498931 : Blo 996598 1498931 := bstep (se 1 (by rfl) ⟨1124198, by rfl⟩ : syracuseStep 1498931 = 2248397) B2248397
theorem B3366737 : Blo 996598 3366737 := bstep (se 2 (by rfl) ⟨1262526, by rfl⟩ : syracuseStep 3366737 = 2525053) B2525053
theorem B1498961 : Blo 996598 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1498979 : Blo 996598 1498979 := bstep (se 1 (by rfl) ⟨1124234, by rfl⟩ : syracuseStep 1498979 = 2248469) B2248469
theorem B1499009 : Blo 996598 1499009 := bstep (se 2 (by rfl) ⟨562128, by rfl⟩ : syracuseStep 1499009 = 1124257) B1124257
theorem B1499027 : Blo 996598 1499027 := bstep (se 1 (by rfl) ⟨1124270, by rfl⟩ : syracuseStep 1499027 = 2248541) B2248541
theorem B1499057 : Blo 996598 1499057 := bstep (se 2 (by rfl) ⟨562146, by rfl⟩ : syracuseStep 1499057 = 1124293) B1124293
theorem B1499075 : Blo 996598 1499075 := bstep (se 1 (by rfl) ⟨1124306, by rfl⟩ : syracuseStep 1499075 = 2248613) B2248613
theorem B2842577 : Blo 996598 2842577 := bstep (se 2 (by rfl) ⟨1065966, by rfl⟩ : syracuseStep 2842577 = 2131933) B2131933
theorem B1499105 : Blo 996598 1499105 := bstep (se 2 (by rfl) ⟨562164, by rfl⟩ : syracuseStep 1499105 = 1124329) B1124329
theorem B1499123 : Blo 996598 1499123 := bstep (se 1 (by rfl) ⟨1124342, by rfl⟩ : syracuseStep 1499123 = 2248685) B2248685
theorem B1499153 : Blo 996598 1499153 := bstep (se 2 (by rfl) ⟨562182, by rfl⟩ : syracuseStep 1499153 = 1124365) B1124365
theorem B1499171 : Blo 996598 1499171 := bstep (se 1 (by rfl) ⟨1124378, by rfl⟩ : syracuseStep 1499171 = 2248757) B2248757
theorem B3039277 : Blo 996598 3039277 := bstep (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) B1139729
theorem B18702389 : Blo 996598 18702389 := bstep (se 5 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 18702389 = 1753349) B1753349
theorem B1499201 : Blo 996598 1499201 := bstep (se 2 (by rfl) ⟨562200, by rfl⟩ : syracuseStep 1499201 = 1124401) B1124401
theorem B1925201 : Blo 996598 1925201 := bstep (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) B1443901
theorem B1499219 : Blo 996598 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B1597553 : Blo 996598 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B1499249 : Blo 996598 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B1499267 : Blo 996598 1499267 := bstep (se 1 (by rfl) ⟨1124450, by rfl⟩ : syracuseStep 1499267 = 2248901) B2248901
theorem B1499297 : Blo 996598 1499297 := bstep (se 2 (by rfl) ⟨562236, by rfl⟩ : syracuseStep 1499297 = 1124473) B1124473
theorem B1499315 : Blo 996598 1499315 := bstep (se 1 (by rfl) ⟨1124486, by rfl⟩ : syracuseStep 1499315 = 2248973) B2248973
theorem B1597649 : Blo 996598 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B1499345 : Blo 996598 1499345 := bstep (se 2 (by rfl) ⟨562254, by rfl⟩ : syracuseStep 1499345 = 1124509) B1124509
theorem B1499363 : Blo 996598 1499363 := bstep (se 1 (by rfl) ⟨1124522, by rfl⟩ : syracuseStep 1499363 = 2249045) B2249045
theorem B1597681 : Blo 996598 1597681 := bstep (se 2 (by rfl) ⟨599130, by rfl⟩ : syracuseStep 1597681 = 1198261) B1198261
theorem B1499393 : Blo 996598 1499393 := bstep (se 2 (by rfl) ⟨562272, by rfl⟩ : syracuseStep 1499393 = 1124545) B1124545
theorem B1499411 : Blo 996598 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B1499441 : Blo 996598 1499441 := bstep (se 2 (by rfl) ⟨562290, by rfl⟩ : syracuseStep 1499441 = 1124581) B1124581
theorem B1499459 : Blo 996598 1499459 := bstep (se 1 (by rfl) ⟨1124594, by rfl⟩ : syracuseStep 1499459 = 2249189) B2249189
theorem B1499489 : Blo 996598 1499489 := bstep (se 2 (by rfl) ⟨562308, by rfl⟩ : syracuseStep 1499489 = 1124617) B1124617
theorem B3367277 : Blo 996598 3367277 := bstep (se 3 (by rfl) ⟨631364, by rfl⟩ : syracuseStep 3367277 = 1262729) B1262729
theorem B1499507 : Blo 996598 1499507 := bstep (se 1 (by rfl) ⟨1124630, by rfl⟩ : syracuseStep 1499507 = 2249261) B2249261
theorem B1499537 : Blo 996598 1499537 := bstep (se 2 (by rfl) ⟨562326, by rfl⟩ : syracuseStep 1499537 = 1124653) B1124653
theorem B3367331 : Blo 996598 3367331 := bstep (se 1 (by rfl) ⟨2525498, by rfl⟩ : syracuseStep 3367331 = 5050997) B5050997
theorem B1499555 : Blo 996598 1499555 := bstep (se 1 (by rfl) ⟨1124666, by rfl⟩ : syracuseStep 1499555 = 2249333) B2249333
theorem B1499585 : Blo 996598 1499585 := bstep (se 2 (by rfl) ⟨562344, by rfl⟩ : syracuseStep 1499585 = 1124689) B1124689
theorem B1892803 : Blo 996598 1892803 := bstep (se 1 (by rfl) ⟨1419602, by rfl⟩ : syracuseStep 1892803 = 2839205) B2839205
theorem B1499603 : Blo 996598 1499603 := bstep (se 1 (by rfl) ⟨1124702, by rfl⟩ : syracuseStep 1499603 = 2249405) B2249405
theorem B1499633 : Blo 996598 1499633 := bstep (se 2 (by rfl) ⟨562362, by rfl⟩ : syracuseStep 1499633 = 1124725) B1124725
theorem B1499651 : Blo 996598 1499651 := bstep (se 1 (by rfl) ⟨1124738, by rfl⟩ : syracuseStep 1499651 = 2249477) B2249477
theorem B1499681 : Blo 996598 1499681 := bstep (se 2 (by rfl) ⟨562380, by rfl⟩ : syracuseStep 1499681 = 1124761) B1124761
theorem B1499699 : Blo 996598 1499699 := bstep (se 1 (by rfl) ⟨1124774, by rfl⟩ : syracuseStep 1499699 = 2249549) B2249549
theorem B1499729 : Blo 996598 1499729 := bstep (se 2 (by rfl) ⟨562398, by rfl⟩ : syracuseStep 1499729 = 1124797) B1124797
theorem B1892963 : Blo 996598 1892963 := bstep (se 1 (by rfl) ⟨1419722, by rfl⟩ : syracuseStep 1892963 = 2839445) B2839445
theorem B1499747 : Blo 996598 1499747 := bstep (se 1 (by rfl) ⟨1124810, by rfl⟩ : syracuseStep 1499747 = 2249621) B2249621
theorem B1499777 : Blo 996598 1499777 := bstep (se 2 (by rfl) ⟨562416, by rfl⟩ : syracuseStep 1499777 = 1124833) B1124833
theorem B1499795 : Blo 996598 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B3367601 : Blo 996598 3367601 := bstep (se 2 (by rfl) ⟨1262850, by rfl⟩ : syracuseStep 3367601 = 2525701) B2525701
theorem B1499825 : Blo 996598 1499825 := bstep (se 2 (by rfl) ⟨562434, by rfl⟩ : syracuseStep 1499825 = 1124869) B1124869
theorem B1499843 : Blo 996598 1499843 := bstep (se 1 (by rfl) ⟨1124882, by rfl⟩ : syracuseStep 1499843 = 2249765) B2249765
theorem B1499873 : Blo 996598 1499873 := bstep (se 2 (by rfl) ⟨562452, by rfl⟩ : syracuseStep 1499873 = 1124905) B1124905
theorem B2843363 : Blo 996598 2843363 := bstep (se 1 (by rfl) ⟨2132522, by rfl⟩ : syracuseStep 2843363 = 4265045) B4265045
theorem B1499891 : Blo 996598 1499891 := bstep (se 1 (by rfl) ⟨1124918, by rfl⟩ : syracuseStep 1499891 = 2249837) B2249837
theorem B1499921 : Blo 996598 1499921 := bstep (se 2 (by rfl) ⟨562470, by rfl⟩ : syracuseStep 1499921 = 1124941) B1124941
theorem B1499939 : Blo 996598 1499939 := bstep (se 1 (by rfl) ⟨1124954, by rfl⟩ : syracuseStep 1499939 = 2249909) B2249909
theorem B1499969 : Blo 996598 1499969 := bstep (se 2 (by rfl) ⟨562488, by rfl⟩ : syracuseStep 1499969 = 1124977) B1124977
theorem B3203921 : Blo 996598 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B1499987 : Blo 996598 1499987 := bstep (se 1 (by rfl) ⟨1124990, by rfl⟩ : syracuseStep 1499987 = 2249981) B2249981
theorem B1500017 : Blo 996598 1500017 := bstep (se 2 (by rfl) ⟨562506, by rfl⟩ : syracuseStep 1500017 = 1125013) B1125013
theorem B3466115 : Blo 996598 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B1500035 : Blo 996598 1500035 := bstep (se 1 (by rfl) ⟨1125026, by rfl⟩ : syracuseStep 1500035 = 2250053) B2250053
theorem B1500065 : Blo 996598 1500065 := bstep (se 2 (by rfl) ⟨562524, by rfl⟩ : syracuseStep 1500065 = 1125049) B1125049
theorem B1500083 : Blo 996598 1500083 := bstep (se 1 (by rfl) ⟨1125062, by rfl⟩ : syracuseStep 1500083 = 2250125) B2250125
theorem B1500113 : Blo 996598 1500113 := bstep (se 2 (by rfl) ⟨562542, by rfl⟩ : syracuseStep 1500113 = 1125085) B1125085
theorem B1500131 : Blo 996598 1500131 := bstep (se 1 (by rfl) ⟨1125098, by rfl⟩ : syracuseStep 1500131 = 2250197) B2250197
theorem B1500161 : Blo 996598 1500161 := bstep (se 2 (by rfl) ⟨562560, by rfl⟩ : syracuseStep 1500161 = 1125121) B1125121
theorem B1500179 : Blo 996598 1500179 := bstep (se 1 (by rfl) ⟨1125134, by rfl⟩ : syracuseStep 1500179 = 2250269) B2250269
theorem B6153251 : Blo 996598 6153251 := bstep (se 1 (by rfl) ⟨4614938, by rfl⟩ : syracuseStep 6153251 = 9229877) B9229877
theorem B2843693 : Blo 996598 2843693 := bstep (se 3 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 2843693 = 1066385) B1066385
theorem B1500209 : Blo 996598 1500209 := bstep (se 2 (by rfl) ⟨562578, by rfl⟩ : syracuseStep 1500209 = 1125157) B1125157
theorem B1500227 : Blo 996598 1500227 := bstep (se 1 (by rfl) ⟨1125170, by rfl⟩ : syracuseStep 1500227 = 2250341) B2250341
theorem B1500257 : Blo 996598 1500257 := bstep (se 2 (by rfl) ⟨562596, by rfl⟩ : syracuseStep 1500257 = 1125193) B1125193
theorem B2843761 : Blo 996598 2843761 := bstep (se 2 (by rfl) ⟨1066410, by rfl⟩ : syracuseStep 2843761 = 2132821) B2132821
theorem B1500275 : Blo 996598 1500275 := bstep (se 1 (by rfl) ⟨1125206, by rfl⟩ : syracuseStep 1500275 = 2250413) B2250413
theorem B1500305 : Blo 996598 1500305 := bstep (se 2 (by rfl) ⟨562614, by rfl⟩ : syracuseStep 1500305 = 1125229) B1125229
theorem B1500323 : Blo 996598 1500323 := bstep (se 1 (by rfl) ⟨1125242, by rfl⟩ : syracuseStep 1500323 = 2250485) B2250485
theorem B1500353 : Blo 996598 1500353 := bstep (se 2 (by rfl) ⟨562632, by rfl⟩ : syracuseStep 1500353 = 1125265) B1125265
theorem B3368141 : Blo 996598 3368141 := bstep (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) B1263053
theorem B1500371 : Blo 996598 1500371 := bstep (se 1 (by rfl) ⟨1125278, by rfl⟩ : syracuseStep 1500371 = 2250557) B2250557
theorem B1500401 : Blo 996598 1500401 := bstep (se 2 (by rfl) ⟨562650, by rfl⟩ : syracuseStep 1500401 = 1125301) B1125301
theorem B3368195 : Blo 996598 3368195 := bstep (se 1 (by rfl) ⟨2526146, by rfl⟩ : syracuseStep 3368195 = 5052293) B5052293
theorem B1500419 : Blo 996598 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B1500449 : Blo 996598 1500449 := bstep (se 2 (by rfl) ⟨562668, by rfl⟩ : syracuseStep 1500449 = 1125337) B1125337
theorem B1500467 : Blo 996598 1500467 := bstep (se 1 (by rfl) ⟨1125350, by rfl⟩ : syracuseStep 1500467 = 2250701) B2250701
theorem B1500497 : Blo 996598 1500497 := bstep (se 2 (by rfl) ⟨562686, by rfl⟩ : syracuseStep 1500497 = 1125373) B1125373
theorem B1140067 : Blo 996598 1140067 := bstep (se 1 (by rfl) ⟨855050, by rfl⟩ : syracuseStep 1140067 = 1710101) B1710101
theorem B1500515 : Blo 996598 1500515 := bstep (se 1 (by rfl) ⟨1125386, by rfl⟩ : syracuseStep 1500515 = 2250773) B2250773
theorem B3204461 : Blo 996598 3204461 := bstep (se 3 (by rfl) ⟨600836, by rfl⟩ : syracuseStep 3204461 = 1201673) B1201673
theorem B1500545 : Blo 996598 1500545 := bstep (se 2 (by rfl) ⟨562704, by rfl⟩ : syracuseStep 1500545 = 1125409) B1125409
theorem B2844035 : Blo 996598 2844035 := bstep (se 1 (by rfl) ⟨2133026, by rfl⟩ : syracuseStep 2844035 = 4266053) B4266053
theorem B1500563 : Blo 996598 1500563 := bstep (se 1 (by rfl) ⟨1125422, by rfl⟩ : syracuseStep 1500563 = 2250845) B2250845
theorem B1500593 : Blo 996598 1500593 := bstep (se 2 (by rfl) ⟨562722, by rfl⟩ : syracuseStep 1500593 = 1125445) B1125445
theorem B1500611 : Blo 996598 1500611 := bstep (se 1 (by rfl) ⟨1125458, by rfl⟩ : syracuseStep 1500611 = 2250917) B2250917
theorem B1500641 : Blo 996598 1500641 := bstep (se 2 (by rfl) ⟨562740, by rfl⟩ : syracuseStep 1500641 = 1125481) B1125481
theorem B1500659 : Blo 996598 1500659 := bstep (se 1 (by rfl) ⟨1125494, by rfl⟩ : syracuseStep 1500659 = 2250989) B2250989
theorem B3368465 : Blo 996598 3368465 := bstep (se 2 (by rfl) ⟨1263174, by rfl⟩ : syracuseStep 3368465 = 2526349) B2526349
theorem B1500689 : Blo 996598 1500689 := bstep (se 2 (by rfl) ⟨562758, by rfl⟩ : syracuseStep 1500689 = 1125517) B1125517
theorem B1500707 : Blo 996598 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B1500737 : Blo 996598 1500737 := bstep (se 2 (by rfl) ⟨562776, by rfl⟩ : syracuseStep 1500737 = 1125553) B1125553
theorem B1500755 : Blo 996598 1500755 := bstep (se 1 (by rfl) ⟨1125566, by rfl⟩ : syracuseStep 1500755 = 2251133) B2251133
theorem B1500785 : Blo 996598 1500785 := bstep (se 2 (by rfl) ⟨562794, by rfl⟩ : syracuseStep 1500785 = 1125589) B1125589
theorem B1500803 : Blo 996598 1500803 := bstep (se 1 (by rfl) ⟨1125602, by rfl⟩ : syracuseStep 1500803 = 2251205) B2251205
theorem B5695109 : Blo 996598 5695109 := bstep (se 4 (by rfl) ⟨533916, by rfl⟩ : syracuseStep 5695109 = 1067833) B1067833
theorem B23062157 : Blo 996598 23062157 := bstep (se 3 (by rfl) ⟨4324154, by rfl⟩ : syracuseStep 23062157 = 8648309) B8648309
theorem B1894033 : Blo 996598 1894033 := bstep (se 2 (by rfl) ⟨710262, by rfl⟩ : syracuseStep 1894033 = 1420525) B1420525
theorem B1500833 : Blo 996598 1500833 := bstep (se 2 (by rfl) ⟨562812, by rfl⟩ : syracuseStep 1500833 = 1125625) B1125625
theorem B1500851 : Blo 996598 1500851 := bstep (se 1 (by rfl) ⟨1125638, by rfl⟩ : syracuseStep 1500851 = 2251277) B2251277
theorem B1500881 : Blo 996598 1500881 := bstep (se 2 (by rfl) ⟨562830, by rfl⟩ : syracuseStep 1500881 = 1125661) B1125661
theorem B4384525 : Blo 996598 4384525 := bstep (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) B1644197
theorem B1599347 : Blo 996598 1599347 := bstep (se 1 (by rfl) ⟨1199510, by rfl⟩ : syracuseStep 1599347 = 2399021) B2399021
theorem B3369005 : Blo 996598 3369005 := bstep (se 3 (by rfl) ⟨631688, by rfl⟩ : syracuseStep 3369005 = 1263377) B1263377
theorem B1140787 : Blo 996598 1140787 := bstep (se 1 (by rfl) ⟨855590, by rfl⟩ : syracuseStep 1140787 = 1711181) B1711181
theorem B3369059 : Blo 996598 3369059 := bstep (se 1 (by rfl) ⟨2526794, by rfl⟩ : syracuseStep 3369059 = 5053589) B5053589
theorem B2844877 : Blo 996598 2844877 := bstep (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) B1066829
theorem B3467501 : Blo 996598 3467501 := bstep (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) B1300313
theorem B2845037 : Blo 996598 2845037 := bstep (se 3 (by rfl) ⟨533444, by rfl⟩ : syracuseStep 2845037 = 1066889) B1066889
theorem B3369329 : Blo 996598 3369329 := bstep (se 2 (by rfl) ⟨1263498, by rfl⟩ : syracuseStep 3369329 = 2526997) B2526997
theorem B1599859 : Blo 996598 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B1599905 : Blo 996598 1599905 := bstep (se 2 (by rfl) ⟨599964, by rfl⟩ : syracuseStep 1599905 = 1199929) B1199929
theorem B2845219 : Blo 996598 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B3795569 : Blo 996598 3795569 := bstep (se 2 (by rfl) ⟨1423338, by rfl⟩ : syracuseStep 3795569 = 2846677) B2846677
theorem B1895089 : Blo 996598 1895089 := bstep (se 2 (by rfl) ⟨710658, by rfl⟩ : syracuseStep 1895089 = 1421317) B1421317
theorem B2026307 : Blo 996598 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B3369869 : Blo 996598 3369869 := bstep (se 3 (by rfl) ⟨631850, by rfl⟩ : syracuseStep 3369869 = 1263701) B1263701
theorem B3369923 : Blo 996598 3369923 := bstep (se 1 (by rfl) ⟨2527442, by rfl⟩ : syracuseStep 3369923 = 5054885) B5054885
theorem B1600577 : Blo 996598 1600577 := bstep (se 2 (by rfl) ⟨600216, by rfl⟩ : syracuseStep 1600577 = 1200433) B1200433
theorem B1895491 : Blo 996598 1895491 := bstep (se 1 (by rfl) ⟨1421618, by rfl⟩ : syracuseStep 1895491 = 2843237) B2843237
theorem B1895537 : Blo 996598 1895537 := bstep (se 2 (by rfl) ⟨710826, by rfl⟩ : syracuseStep 1895537 = 1421653) B1421653
theorem B3370193 : Blo 996598 3370193 := bstep (se 2 (by rfl) ⟨1263822, by rfl⟩ : syracuseStep 3370193 = 2527645) B2527645
theorem B1895825 : Blo 996598 1895825 := bstep (se 2 (by rfl) ⟨710934, by rfl⟩ : syracuseStep 1895825 = 1421869) B1421869
theorem B1601089 : Blo 996598 1601089 := bstep (se 2 (by rfl) ⟨600408, by rfl⟩ : syracuseStep 1601089 = 1200817) B1200817
theorem B7597637 : Blo 996598 7597637 := bstep (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) B1424557
theorem B3370733 : Blo 996598 3370733 := bstep (se 3 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 3370733 = 1264025) B1264025
theorem B3370787 : Blo 996598 3370787 := bstep (se 1 (by rfl) ⟨2528090, by rfl⟩ : syracuseStep 3370787 = 5056181) B5056181
theorem B4321073 : Blo 996598 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B2846609 : Blo 996598 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B3797027 : Blo 996598 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B3371057 : Blo 996598 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B1896547 : Blo 996598 1896547 := bstep (se 1 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 1896547 = 2844821) B2844821
theorem B1012019 : Blo 996598 1012019 := bstep (se 1 (by rfl) ⟨759014, by rfl⟩ : syracuseStep 1012019 = 1518029) B1518029
theorem B1012051 : Blo 996598 1012051 := bstep (se 1 (by rfl) ⟨759038, by rfl⟩ : syracuseStep 1012051 = 1518077) B1518077
theorem B12775907 : Blo 996598 12775907 := bstep (se 1 (by rfl) ⟨9581930, by rfl⟩ : syracuseStep 12775907 = 19163861) B19163861
theorem B6386161 : Blo 996598 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B1896995 : Blo 996598 1896995 := bstep (se 1 (by rfl) ⟨1422746, by rfl⟩ : syracuseStep 1896995 = 2845493) B2845493
theorem B3371597 : Blo 996598 3371597 := bstep (se 3 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 3371597 = 1264349) B1264349
theorem B3371651 : Blo 996598 3371651 := bstep (se 1 (by rfl) ⟨2528738, by rfl⟩ : syracuseStep 3371651 = 5057477) B5057477
theorem B1012387 : Blo 996598 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B1897283 : Blo 996598 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B1602371 : Blo 996598 1602371 := bstep (se 1 (by rfl) ⟨1201778, by rfl⟩ : syracuseStep 1602371 = 2403557) B2403557
theorem B2847565 : Blo 996598 2847565 := bstep (se 3 (by rfl) ⟨533918, by rfl⟩ : syracuseStep 2847565 = 1067837) B1067837
theorem B3371921 : Blo 996598 3371921 := bstep (se 2 (by rfl) ⟨1264470, by rfl⟩ : syracuseStep 3371921 = 2528941) B2528941
theorem B1602499 : Blo 996598 1602499 := bstep (se 1 (by rfl) ⟨1201874, by rfl⟩ : syracuseStep 1602499 = 2403749) B2403749
theorem B9597923 : Blo 996598 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B3798029 : Blo 996598 3798029 := bstep (se 3 (by rfl) ⟨712130, by rfl⟩ : syracuseStep 3798029 = 1424261) B1424261
theorem B2847793 : Blo 996598 2847793 := bstep (se 2 (by rfl) ⟨1067922, by rfl⟩ : syracuseStep 2847793 = 2135845) B2135845
theorem B1602641 : Blo 996598 1602641 := bstep (se 2 (by rfl) ⟨600990, by rfl⟩ : syracuseStep 1602641 = 1201981) B1201981
theorem B19166321 : Blo 996598 19166321 := bstep (se 2 (by rfl) ⟨7187370, by rfl⟩ : syracuseStep 19166321 = 14374741) B14374741
theorem B7206029 : Blo 996598 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B2847953 : Blo 996598 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B2880785 : Blo 996598 2880785 := bstep (se 2 (by rfl) ⟨1080294, by rfl⟩ : syracuseStep 2880785 = 2160589) B2160589
theorem B2848067 : Blo 996598 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B3372461 : Blo 996598 3372461 := bstep (se 3 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 3372461 = 1264673) B1264673
theorem B3372515 : Blo 996598 3372515 := bstep (se 1 (by rfl) ⟨2529386, by rfl⟩ : syracuseStep 3372515 = 5058773) B5058773
theorem B3372785 : Blo 996598 3372785 := bstep (se 2 (by rfl) ⟨1264794, by rfl⟩ : syracuseStep 3372785 = 2529589) B2529589
theorem B1898225 : Blo 996598 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B10811333 : Blo 996598 10811333 := bstep (se 4 (by rfl) ⟨1013562, by rfl⟩ : syracuseStep 10811333 = 2027125) B2027125
theorem B3373325 : Blo 996598 3373325 := bstep (se 3 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 3373325 = 1264997) B1264997
theorem B2849069 : Blo 996598 2849069 := bstep (se 3 (by rfl) ⟨534200, by rfl⟩ : syracuseStep 2849069 = 1068401) B1068401
theorem B3373379 : Blo 996598 3373379 := bstep (se 1 (by rfl) ⟨2530034, by rfl⟩ : syracuseStep 3373379 = 5060069) B5060069
theorem B4553059 : Blo 996598 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B3242467 : Blo 996598 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B2849251 : Blo 996598 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B3373649 : Blo 996598 3373649 := bstep (se 2 (by rfl) ⟨1265118, by rfl⟩ : syracuseStep 3373649 = 2530237) B2530237
theorem B1899121 : Blo 996598 1899121 := bstep (se 2 (by rfl) ⟨712170, by rfl⟩ : syracuseStep 1899121 = 1424341) B1424341
theorem B1899281 : Blo 996598 1899281 := bstep (se 2 (by rfl) ⟨712230, by rfl⟩ : syracuseStep 1899281 = 1424461) B1424461
theorem B2128771 : Blo 996598 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B36436877 : Blo 996598 36436877 := bstep (se 3 (by rfl) ⟨6831914, by rfl⟩ : syracuseStep 36436877 = 13663829) B13663829
theorem B1801283 : Blo 996598 1801283 := bstep (se 1 (by rfl) ⟨1350962, by rfl⟩ : syracuseStep 1801283 = 2701925) B2701925
theorem B3374189 : Blo 996598 3374189 := bstep (se 3 (by rfl) ⟨632660, by rfl⟩ : syracuseStep 3374189 = 1265321) B1265321
theorem B4258979 : Blo 996598 4258979 := bstep (se 1 (by rfl) ⟨3194234, by rfl⟩ : syracuseStep 4258979 = 6388469) B6388469
theorem B3374243 : Blo 996598 3374243 := bstep (se 1 (by rfl) ⟨2530682, by rfl⟩ : syracuseStep 3374243 = 5061365) B5061365
theorem B2129105 : Blo 996598 2129105 := bstep (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) B1596829
theorem B5045489 : Blo 996598 5045489 := bstep (se 2 (by rfl) ⟨1892058, by rfl⟩ : syracuseStep 5045489 = 3784117) B3784117
theorem B3079565 : Blo 996598 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B3374513 : Blo 996598 3374513 := bstep (se 2 (by rfl) ⟨1265442, by rfl⟩ : syracuseStep 3374513 = 2530885) B2530885
theorem B1801745 : Blo 996598 1801745 := bstep (se 2 (by rfl) ⟨675654, by rfl⟩ : syracuseStep 1801745 = 1351309) B1351309
theorem B2522897 : Blo 996598 2522897 := bstep (se 2 (by rfl) ⟨946086, by rfl⟩ : syracuseStep 2522897 = 1892173) B1892173
theorem B2522947 : Blo 996598 2522947 := bstep (se 1 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 2522947 = 3784421) B3784421
theorem B3375053 : Blo 996598 3375053 := bstep (se 3 (by rfl) ⟨632822, by rfl⟩ : syracuseStep 3375053 = 1265645) B1265645
theorem B2523089 : Blo 996598 2523089 := bstep (se 2 (by rfl) ⟨946158, by rfl⟩ : syracuseStep 2523089 = 1892317) B1892317
theorem B13828067 : Blo 996598 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B9109655 : Blo 996598 9109655 := bstep (se 1 (by rfl) ⟨6832241, by rfl⟩ : syracuseStep 9109655 = 13664483) B13664483
theorem B8093969 : Blo 996598 8093969 := bstep (se 2 (by rfl) ⟨3035238, by rfl⟩ : syracuseStep 8093969 = 6070477) B6070477
theorem B2130241 : Blo 996598 2130241 := bstep (se 2 (by rfl) ⟨798840, by rfl⟩ : syracuseStep 2130241 = 1597681) B1597681
theorem B3375539 : Blo 996598 3375539 := bstep (se 1 (by rfl) ⟨2531654, by rfl⟩ : syracuseStep 3375539 = 5063309) B5063309
theorem B2523595 : Blo 996598 2523595 := bstep (se 1 (by rfl) ⟨1892696, by rfl⟩ : syracuseStep 2523595 = 3785393) B3785393
theorem B4260397 : Blo 996598 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B1081931 : Blo 996598 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B2523737 : Blo 996598 2523737 := bstep (se 2 (by rfl) ⟨946401, by rfl⟩ : syracuseStep 2523737 = 1892803) B1892803
theorem B2130583 : Blo 996598 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B3375809 : Blo 996598 3375809 := bstep (se 2 (by rfl) ⟨1265928, by rfl⟩ : syracuseStep 3375809 = 2531857) B2531857
theorem B2131019 : Blo 996598 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B4260995 : Blo 996598 4260995 := bstep (se 1 (by rfl) ⟨3195746, by rfl⟩ : syracuseStep 4260995 = 6391493) B6391493
theorem B4555997 : Blo 996598 4555997 := bstep (se 3 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 4555997 = 1708499) B1708499
theorem B3376349 : Blo 996598 3376349 := bstep (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) B1266131
theorem B6391133 : Blo 996598 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B2524567 : Blo 996598 2524567 := bstep (se 1 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 2524567 = 3786851) B3786851
theorem B2557619 : Blo 996598 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B36439793 : Blo 996598 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B5048081 : Blo 996598 5048081 := bstep (se 2 (by rfl) ⟨1893030, by rfl⟩ : syracuseStep 5048081 = 3786061) B3786061
theorem B2525003 : Blo 996598 2525003 := bstep (se 1 (by rfl) ⟨1893752, by rfl⟩ : syracuseStep 2525003 = 3787505) B3787505
theorem B8324995 : Blo 996598 8324995 := bstep (se 1 (by rfl) ⟨6243746, by rfl⟩ : syracuseStep 8324995 = 12487493) B12487493
theorem B5048243 : Blo 996598 5048243 := bstep (se 1 (by rfl) ⟨3786182, by rfl⟩ : syracuseStep 5048243 = 7572365) B7572365
theorem B2131915 : Blo 996598 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B3835907 : Blo 996598 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B2525377 : Blo 996598 2525377 := bstep (se 2 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 2525377 = 1894033) B1894033
theorem B10947089 : Blo 996598 10947089 := bstep (se 2 (by rfl) ⟨4105158, by rfl⟩ : syracuseStep 10947089 = 8210317) B8210317
theorem B8096435 : Blo 996598 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B2132659 : Blo 996598 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B2525975 : Blo 996598 2525975 := bstep (se 1 (by rfl) ⟨1894481, by rfl⟩ : syracuseStep 2525975 = 3788963) B3788963
theorem B7310429 : Blo 996598 7310429 := bstep (se 3 (by rfl) ⟨1370705, by rfl⟩ : syracuseStep 7310429 = 2741411) B2741411
theorem B2133145 : Blo 996598 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B2526785 : Blo 996598 2526785 := bstep (se 2 (by rfl) ⟨947544, by rfl⟩ : syracuseStep 2526785 = 1895089) B1895089
theorem B29200193 : Blo 996598 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B5050187 : Blo 996598 5050187 := bstep (se 1 (by rfl) ⟨3787640, by rfl⟩ : syracuseStep 5050187 = 7575281) B7575281
theorem B1282135 : Blo 996598 1282135 := bstep (se 1 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 1282135 = 1923203) B1923203
theorem B2527321 : Blo 996598 2527321 := bstep (se 2 (by rfl) ⟨947745, by rfl⟩ : syracuseStep 2527321 = 1895491) B1895491
theorem B12816913 : Blo 996598 12816913 := bstep (se 2 (by rfl) ⟨4806342, by rfl⟩ : syracuseStep 12816913 = 9612685) B9612685
theorem B2134615 : Blo 996598 2134615 := bstep (se 1 (by rfl) ⟨1600961, by rfl⟩ : syracuseStep 2134615 = 3201923) B3201923
theorem B2134667 : Blo 996598 2134667 := bstep (se 1 (by rfl) ⟨1601000, by rfl⟩ : syracuseStep 2134667 = 3202001) B3202001
theorem B1348363 : Blo 996598 1348363 := bstep (se 1 (by rfl) ⟨1011272, by rfl⟩ : syracuseStep 1348363 = 2022545) B2022545
theorem B6394925 : Blo 996598 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B2528435 : Blo 996598 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B3413195 : Blo 996598 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B48534997 : Blo 996598 48534997 := bstep (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) B1137539
theorem B2528729 : Blo 996598 2528729 := bstep (se 2 (by rfl) ⟨948273, by rfl⟩ : syracuseStep 2528729 = 1896547) B1896547
theorem B5051969 : Blo 996598 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B1349401 : Blo 996598 1349401 := bstep (se 2 (by rfl) ⟨506025, by rfl⟩ : syracuseStep 1349401 = 1012051) B1012051
theorem B1578839 : Blo 996598 1578839 := bstep (se 1 (by rfl) ⟨1184129, by rfl⟩ : syracuseStep 1578839 = 2368259) B2368259
theorem B1349849 : Blo 996598 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B2136307 : Blo 996598 2136307 := bstep (se 1 (by rfl) ⟨1602230, by rfl⟩ : syracuseStep 2136307 = 3204461) B3204461
theorem B15374771 : Blo 996598 15374771 := bstep (se 1 (by rfl) ⟨11531078, by rfl⟩ : syracuseStep 15374771 = 23062157) B23062157
theorem B2136665 : Blo 996598 2136665 := bstep (se 2 (by rfl) ⟨801249, by rfl⟩ : syracuseStep 2136665 = 1602499) B1602499
theorem B8100557 : Blo 996598 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B4266769 : Blo 996598 4266769 := bstep (se 2 (by rfl) ⟨1600038, by rfl⟩ : syracuseStep 4266769 = 3200077) B3200077
theorem B1121323 : Blo 996598 1121323 := bstep (se 1 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 1121323 = 1681985) B1681985
theorem B2530379 : Blo 996598 2530379 := bstep (se 1 (by rfl) ⟨1897784, by rfl⟩ : syracuseStep 2530379 = 3795569) B3795569
theorem B1121431 : Blo 996598 1121431 := bstep (se 1 (by rfl) ⟨841073, by rfl⟩ : syracuseStep 1121431 = 1682147) B1682147
theorem B1121611 : Blo 996598 1121611 := bstep (se 1 (by rfl) ⟨841208, by rfl⟩ : syracuseStep 1121611 = 1682417) B1682417
theorem B1121719 : Blo 996598 1121719 := bstep (se 1 (by rfl) ⟨841289, by rfl⟩ : syracuseStep 1121719 = 1682579) B1682579
theorem B5053913 : Blo 996598 5053913 := bstep (se 2 (by rfl) ⟨1895217, by rfl⟩ : syracuseStep 5053913 = 3790435) B3790435
theorem B1121899 : Blo 996598 1121899 := bstep (se 1 (by rfl) ⟨841424, by rfl⟩ : syracuseStep 1121899 = 1682849) B1682849
theorem B1122007 : Blo 996598 1122007 := bstep (se 1 (by rfl) ⟨841505, by rfl⟩ : syracuseStep 1122007 = 1683011) B1683011
theorem B1122187 : Blo 996598 1122187 := bstep (se 1 (by rfl) ⟨841640, by rfl⟩ : syracuseStep 1122187 = 1683281) B1683281
theorem B1122295 : Blo 996598 1122295 := bstep (se 1 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 1122295 = 1683443) B1683443
theorem B2531351 : Blo 996598 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B8528003 : Blo 996598 8528003 := bstep (se 1 (by rfl) ⟨6396002, by rfl⟩ : syracuseStep 8528003 = 12792005) B12792005
theorem B1122475 : Blo 996598 1122475 := bstep (se 1 (by rfl) ⟨841856, by rfl⟩ : syracuseStep 1122475 = 1683713) B1683713
theorem B7282865 : Blo 996598 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B1122583 : Blo 996598 1122583 := bstep (se 1 (by rfl) ⟨841937, by rfl⟩ : syracuseStep 1122583 = 1683875) B1683875
theorem B1122763 : Blo 996598 1122763 := bstep (se 1 (by rfl) ⟨842072, by rfl⟩ : syracuseStep 1122763 = 1684145) B1684145
theorem B6070745 : Blo 996598 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B12329489 : Blo 996598 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B5677613 : Blo 996598 5677613 := bstep (se 3 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 5677613 = 2129105) B2129105
theorem B1122871 : Blo 996598 1122871 := bstep (se 1 (by rfl) ⟨842153, by rfl⟩ : syracuseStep 1122871 = 1684307) B1684307
theorem B6398615 : Blo 996598 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B2532019 : Blo 996598 2532019 := bstep (se 1 (by rfl) ⟨1899014, by rfl⟩ : syracuseStep 2532019 = 3798029) B3798029
theorem B1123051 : Blo 996598 1123051 := bstep (se 1 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 1123051 = 1684577) B1684577
theorem B2532161 : Blo 996598 2532161 := bstep (se 2 (by rfl) ⟨949560, by rfl⟩ : syracuseStep 2532161 = 1899121) B1899121
theorem B1123159 : Blo 996598 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B1123339 : Blo 996598 1123339 := bstep (se 1 (by rfl) ⟨842504, by rfl⟩ : syracuseStep 1123339 = 1685009) B1685009
theorem B5055533 : Blo 996598 5055533 := bstep (se 3 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 5055533 = 1895825) B1895825
theorem B4269145 : Blo 996598 4269145 := bstep (se 2 (by rfl) ⟨1600929, by rfl⟩ : syracuseStep 4269145 = 3201859) B3201859
theorem B1123447 : Blo 996598 1123447 := bstep (se 1 (by rfl) ⟨842585, by rfl⟩ : syracuseStep 1123447 = 1685171) B1685171
theorem B1123627 : Blo 996598 1123627 := bstep (se 1 (by rfl) ⟨842720, by rfl⟩ : syracuseStep 1123627 = 1685441) B1685441
theorem B1123735 : Blo 996598 1123735 := bstep (se 1 (by rfl) ⟨842801, by rfl⟩ : syracuseStep 1123735 = 1685603) B1685603
theorem B1123915 : Blo 996598 1123915 := bstep (se 1 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 1123915 = 1685873) B1685873
theorem B1124023 : Blo 996598 1124023 := bstep (se 1 (by rfl) ⟨843017, by rfl⟩ : syracuseStep 1124023 = 1686035) B1686035
theorem B1124203 : Blo 996598 1124203 := bstep (se 1 (by rfl) ⟨843152, by rfl⟩ : syracuseStep 1124203 = 1686305) B1686305
theorem B24291251 : Blo 996598 24291251 := bstep (se 1 (by rfl) ⟨18218438, by rfl⟩ : syracuseStep 24291251 = 36436877) B36436877
theorem B1124311 : Blo 996598 1124311 := bstep (se 1 (by rfl) ⟨843233, by rfl⟩ : syracuseStep 1124311 = 1686467) B1686467
theorem B9578513 : Blo 996598 9578513 := bstep (se 2 (by rfl) ⟨3591942, by rfl⟩ : syracuseStep 9578513 = 7183885) B7183885
theorem B4270103 : Blo 996598 4270103 := bstep (se 1 (by rfl) ⟨3202577, by rfl⟩ : syracuseStep 4270103 = 6405155) B6405155
theorem B1124491 : Blo 996598 1124491 := bstep (se 1 (by rfl) ⟨843368, by rfl⟩ : syracuseStep 1124491 = 1686737) B1686737
theorem B1124599 : Blo 996598 1124599 := bstep (se 1 (by rfl) ⟨843449, by rfl⟩ : syracuseStep 1124599 = 1686899) B1686899
theorem B1124779 : Blo 996598 1124779 := bstep (se 1 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 1124779 = 1687169) B1687169
theorem B8530393 : Blo 996598 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B1681931 : Blo 996598 1681931 := bstep (se 1 (by rfl) ⟨1261448, by rfl⟩ : syracuseStep 1681931 = 2522897) B2522897
theorem B1124887 : Blo 996598 1124887 := bstep (se 1 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 1124887 = 1687331) B1687331
theorem B1682059 : Blo 996598 1682059 := bstep (se 1 (by rfl) ⟨1261544, by rfl⟩ : syracuseStep 1682059 = 2523089) B2523089
theorem B9218711 : Blo 996598 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B1125067 : Blo 996598 1125067 := bstep (se 1 (by rfl) ⟨843800, by rfl⟩ : syracuseStep 1125067 = 1687601) B1687601
theorem B1682201 : Blo 996598 1682201 := bstep (se 2 (by rfl) ⟨630825, by rfl⟩ : syracuseStep 1682201 = 1261651) B1261651
theorem B1125175 : Blo 996598 1125175 := bstep (se 1 (by rfl) ⟨843881, by rfl⟩ : syracuseStep 1125175 = 1687763) B1687763
theorem B5680003 : Blo 996598 5680003 := bstep (se 1 (by rfl) ⟨4260002, by rfl⟩ : syracuseStep 5680003 = 8520005) B8520005
theorem B1420183 : Blo 996598 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1682329 : Blo 996598 1682329 := bstep (se 2 (by rfl) ⟨630873, by rfl⟩ : syracuseStep 1682329 = 1261747) B1261747
theorem B1125355 : Blo 996598 1125355 := bstep (se 1 (by rfl) ⟨844016, by rfl⟩ : syracuseStep 1125355 = 1688033) B1688033
theorem B4041731 : Blo 996598 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B2436119 : Blo 996598 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B1125463 : Blo 996598 1125463 := bstep (se 1 (by rfl) ⟨844097, by rfl⟩ : syracuseStep 1125463 = 1688195) B1688195
theorem B4041859 : Blo 996598 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B2403479 : Blo 996598 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B1125643 : Blo 996598 1125643 := bstep (se 1 (by rfl) ⟨844232, by rfl⟩ : syracuseStep 1125643 = 1688465) B1688465
theorem B19213685 : Blo 996598 19213685 := bstep (se 5 (by rfl) ⟨900641, by rfl⟩ : syracuseStep 19213685 = 1801283) B1801283
theorem B8531351 : Blo 996598 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B10235315 : Blo 996598 10235315 := bstep (se 1 (by rfl) ⟨7676486, by rfl⟩ : syracuseStep 10235315 = 15352973) B15352973
theorem B1682903 : Blo 996598 1682903 := bstep (se 1 (by rfl) ⟨1262177, by rfl⟩ : syracuseStep 1682903 = 2524355) B2524355
theorem B2698717 : Blo 996598 2698717 := bstep (se 3 (by rfl) ⟨506009, by rfl⟩ : syracuseStep 2698717 = 1012019) B1012019
theorem B1683031 : Blo 996598 1683031 := bstep (se 1 (by rfl) ⟨1262273, by rfl⟩ : syracuseStep 1683031 = 2524547) B2524547
theorem B8531729 : Blo 996598 8531729 := bstep (se 2 (by rfl) ⟨3199398, by rfl⟩ : syracuseStep 8531729 = 6398797) B6398797
theorem B5680961 : Blo 996598 5680961 := bstep (se 2 (by rfl) ⟨2130360, by rfl⟩ : syracuseStep 5680961 = 4260721) B4260721
theorem B4272203 : Blo 996598 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B1683659 : Blo 996598 1683659 := bstep (se 1 (by rfl) ⟨1262744, by rfl⟩ : syracuseStep 1683659 = 2525489) B2525489
theorem B1683787 : Blo 996598 1683787 := bstep (se 1 (by rfl) ⟨1262840, by rfl⟩ : syracuseStep 1683787 = 2525681) B2525681
theorem B72986993 : Blo 996598 72986993 := bstep (se 2 (by rfl) ⟨27370122, by rfl⟩ : syracuseStep 72986993 = 54740245) B54740245
theorem B1683929 : Blo 996598 1683929 := bstep (se 2 (by rfl) ⟨631473, by rfl⟩ : syracuseStep 1683929 = 1262947) B1262947
theorem B1520089 : Blo 996598 1520089 := bstep (se 2 (by rfl) ⟨570033, by rfl⟩ : syracuseStep 1520089 = 1140067) B1140067
theorem B4043353 : Blo 996598 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B1684057 : Blo 996598 1684057 := bstep (se 2 (by rfl) ⟨631521, by rfl⟩ : syracuseStep 1684057 = 1263043) B1263043
theorem B5059421 : Blo 996598 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B5846033 : Blo 996598 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B8107073 : Blo 996598 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B1684631 : Blo 996598 1684631 := bstep (se 1 (by rfl) ⟨1263473, by rfl⟩ : syracuseStep 1684631 = 2526947) B2526947
theorem B996599 : Blo 996598 996599 := bstep (se 1 (by rfl) ⟨747449, by rfl⟩ : syracuseStep 996599 = 1494899) B1494899
theorem B996619 : Blo 996598 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B996631 : Blo 996598 996631 := bstep (se 1 (by rfl) ⟨747473, by rfl⟩ : syracuseStep 996631 = 1494947) B1494947
theorem B1684759 : Blo 996598 1684759 := bstep (se 1 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 1684759 = 2527139) B2527139
theorem B996651 : Blo 996598 996651 := bstep (se 1 (by rfl) ⟨747488, by rfl⟩ : syracuseStep 996651 = 1494977) B1494977
theorem B996663 : Blo 996598 996663 := bstep (se 1 (by rfl) ⟨747497, by rfl⟩ : syracuseStep 996663 = 1494995) B1494995
theorem B996683 : Blo 996598 996683 := bstep (se 1 (by rfl) ⟨747512, by rfl⟩ : syracuseStep 996683 = 1495025) B1495025
theorem B996695 : Blo 996598 996695 := bstep (se 1 (by rfl) ⟨747521, by rfl⟩ : syracuseStep 996695 = 1495043) B1495043
theorem B2733401 : Blo 996598 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B996715 : Blo 996598 996715 := bstep (se 1 (by rfl) ⟨747536, by rfl⟩ : syracuseStep 996715 = 1495073) B1495073
theorem B996727 : Blo 996598 996727 := bstep (se 1 (by rfl) ⟨747545, by rfl⟩ : syracuseStep 996727 = 1495091) B1495091
theorem B996747 : Blo 996598 996747 := bstep (se 1 (by rfl) ⟨747560, by rfl⟩ : syracuseStep 996747 = 1495121) B1495121
theorem B996759 : Blo 996598 996759 := bstep (se 1 (by rfl) ⟨747569, by rfl⟩ : syracuseStep 996759 = 1495139) B1495139
theorem B996779 : Blo 996598 996779 := bstep (se 1 (by rfl) ⟨747584, by rfl⟩ : syracuseStep 996779 = 1495169) B1495169
theorem B996791 : Blo 996598 996791 := bstep (se 1 (by rfl) ⟨747593, by rfl⟩ : syracuseStep 996791 = 1495187) B1495187
theorem B996811 : Blo 996598 996811 := bstep (se 1 (by rfl) ⟨747608, by rfl⟩ : syracuseStep 996811 = 1495217) B1495217
theorem B996823 : Blo 996598 996823 := bstep (se 1 (by rfl) ⟨747617, by rfl⟩ : syracuseStep 996823 = 1495235) B1495235
theorem B996843 : Blo 996598 996843 := bstep (se 1 (by rfl) ⟨747632, by rfl⟩ : syracuseStep 996843 = 1495265) B1495265
theorem B996855 : Blo 996598 996855 := bstep (se 1 (by rfl) ⟨747641, by rfl⟩ : syracuseStep 996855 = 1495283) B1495283
theorem B996875 : Blo 996598 996875 := bstep (se 1 (by rfl) ⟨747656, by rfl⟩ : syracuseStep 996875 = 1495313) B1495313
theorem B996887 : Blo 996598 996887 := bstep (se 1 (by rfl) ⟨747665, by rfl⟩ : syracuseStep 996887 = 1495331) B1495331
theorem B996907 : Blo 996598 996907 := bstep (se 1 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 996907 = 1495361) B1495361
theorem B996919 : Blo 996598 996919 := bstep (se 1 (by rfl) ⟨747689, by rfl⟩ : syracuseStep 996919 = 1495379) B1495379
theorem B996939 : Blo 996598 996939 := bstep (se 1 (by rfl) ⟨747704, by rfl⟩ : syracuseStep 996939 = 1495409) B1495409
theorem B996951 : Blo 996598 996951 := bstep (se 1 (by rfl) ⟨747713, by rfl⟩ : syracuseStep 996951 = 1495427) B1495427
theorem B1947223 : Blo 996598 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B996971 : Blo 996598 996971 := bstep (se 1 (by rfl) ⟨747728, by rfl⟩ : syracuseStep 996971 = 1495457) B1495457
theorem B996983 : Blo 996598 996983 := bstep (se 1 (by rfl) ⟨747737, by rfl⟩ : syracuseStep 996983 = 1495475) B1495475
theorem B997003 : Blo 996598 997003 := bstep (se 1 (by rfl) ⟨747752, by rfl⟩ : syracuseStep 997003 = 1495505) B1495505
theorem B997015 : Blo 996598 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B997035 : Blo 996598 997035 := bstep (se 1 (by rfl) ⟨747776, by rfl⟩ : syracuseStep 997035 = 1495553) B1495553
theorem B4273843 : Blo 996598 4273843 := bstep (se 1 (by rfl) ⟨3205382, by rfl⟩ : syracuseStep 4273843 = 6410765) B6410765
theorem B997047 : Blo 996598 997047 := bstep (se 1 (by rfl) ⟨747785, by rfl⟩ : syracuseStep 997047 = 1495571) B1495571
theorem B997067 : Blo 996598 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B997079 : Blo 996598 997079 := bstep (se 1 (by rfl) ⟨747809, by rfl⟩ : syracuseStep 997079 = 1495619) B1495619
theorem B997099 : Blo 996598 997099 := bstep (se 1 (by rfl) ⟨747824, by rfl⟩ : syracuseStep 997099 = 1495649) B1495649
theorem B997111 : Blo 996598 997111 := bstep (se 1 (by rfl) ⟨747833, by rfl⟩ : syracuseStep 997111 = 1495667) B1495667
theorem B997131 : Blo 996598 997131 := bstep (se 1 (by rfl) ⟨747848, by rfl⟩ : syracuseStep 997131 = 1495697) B1495697
theorem B997143 : Blo 996598 997143 := bstep (se 1 (by rfl) ⟨747857, by rfl⟩ : syracuseStep 997143 = 1495715) B1495715
theorem B997163 : Blo 996598 997163 := bstep (se 1 (by rfl) ⟨747872, by rfl⟩ : syracuseStep 997163 = 1495745) B1495745
theorem B997175 : Blo 996598 997175 := bstep (se 1 (by rfl) ⟨747881, by rfl⟩ : syracuseStep 997175 = 1495763) B1495763
theorem B997195 : Blo 996598 997195 := bstep (se 1 (by rfl) ⟨747896, by rfl⟩ : syracuseStep 997195 = 1495793) B1495793
theorem B997207 : Blo 996598 997207 := bstep (se 1 (by rfl) ⟨747905, by rfl⟩ : syracuseStep 997207 = 1495811) B1495811
theorem B997227 : Blo 996598 997227 := bstep (se 1 (by rfl) ⟨747920, by rfl⟩ : syracuseStep 997227 = 1495841) B1495841
theorem B997239 : Blo 996598 997239 := bstep (se 1 (by rfl) ⟨747929, by rfl⟩ : syracuseStep 997239 = 1495859) B1495859
theorem B997259 : Blo 996598 997259 := bstep (se 1 (by rfl) ⟨747944, by rfl⟩ : syracuseStep 997259 = 1495889) B1495889
theorem B1685387 : Blo 996598 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B997271 : Blo 996598 997271 := bstep (se 1 (by rfl) ⟨747953, by rfl⟩ : syracuseStep 997271 = 1495907) B1495907
theorem B2242457 : Blo 996598 2242457 := bstep (se 2 (by rfl) ⟨840921, by rfl⟩ : syracuseStep 2242457 = 1681843) B1681843
theorem B997291 : Blo 996598 997291 := bstep (se 1 (by rfl) ⟨747968, by rfl⟩ : syracuseStep 997291 = 1495937) B1495937
theorem B11351987 : Blo 996598 11351987 := bstep (se 1 (by rfl) ⟨8513990, by rfl⟩ : syracuseStep 11351987 = 17027981) B17027981
theorem B997303 : Blo 996598 997303 := bstep (se 1 (by rfl) ⟨747977, by rfl⟩ : syracuseStep 997303 = 1495955) B1495955
theorem B997323 : Blo 996598 997323 := bstep (se 1 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 997323 = 1495985) B1495985
theorem B997335 : Blo 996598 997335 := bstep (se 1 (by rfl) ⟨748001, by rfl⟩ : syracuseStep 997335 = 1496003) B1496003
theorem B997355 : Blo 996598 997355 := bstep (se 1 (by rfl) ⟨748016, by rfl⟩ : syracuseStep 997355 = 1496033) B1496033
theorem B2242547 : Blo 996598 2242547 := bstep (se 1 (by rfl) ⟨1681910, by rfl⟩ : syracuseStep 2242547 = 3363821) B3363821
theorem B997367 : Blo 996598 997367 := bstep (se 1 (by rfl) ⟨748025, by rfl⟩ : syracuseStep 997367 = 1496051) B1496051
theorem B997387 : Blo 996598 997387 := bstep (se 1 (by rfl) ⟨748040, by rfl⟩ : syracuseStep 997387 = 1496081) B1496081
theorem B1685515 : Blo 996598 1685515 := bstep (se 1 (by rfl) ⟨1264136, by rfl⟩ : syracuseStep 1685515 = 2528273) B2528273
theorem B2242583 : Blo 996598 2242583 := bstep (se 1 (by rfl) ⟨1681937, by rfl⟩ : syracuseStep 2242583 = 3363875) B3363875
theorem B997399 : Blo 996598 997399 := bstep (se 1 (by rfl) ⟨748049, by rfl⟩ : syracuseStep 997399 = 1496099) B1496099
theorem B997419 : Blo 996598 997419 := bstep (se 1 (by rfl) ⟨748064, by rfl⟩ : syracuseStep 997419 = 1496129) B1496129
theorem B997431 : Blo 996598 997431 := bstep (se 1 (by rfl) ⟨748073, by rfl⟩ : syracuseStep 997431 = 1496147) B1496147
theorem B997451 : Blo 996598 997451 := bstep (se 1 (by rfl) ⟨748088, by rfl⟩ : syracuseStep 997451 = 1496177) B1496177
theorem B997463 : Blo 996598 997463 := bstep (se 1 (by rfl) ⟨748097, by rfl⟩ : syracuseStep 997463 = 1496195) B1496195
theorem B997483 : Blo 996598 997483 := bstep (se 1 (by rfl) ⟨748112, by rfl⟩ : syracuseStep 997483 = 1496225) B1496225
theorem B997495 : Blo 996598 997495 := bstep (se 1 (by rfl) ⟨748121, by rfl⟩ : syracuseStep 997495 = 1496243) B1496243
theorem B997515 : Blo 996598 997515 := bstep (se 1 (by rfl) ⟨748136, by rfl⟩ : syracuseStep 997515 = 1496273) B1496273
theorem B997527 : Blo 996598 997527 := bstep (se 1 (by rfl) ⟨748145, by rfl⟩ : syracuseStep 997527 = 1496291) B1496291
theorem B1685657 : Blo 996598 1685657 := bstep (se 2 (by rfl) ⟨632121, by rfl⟩ : syracuseStep 1685657 = 1264243) B1264243
theorem B997547 : Blo 996598 997547 := bstep (se 1 (by rfl) ⟨748160, by rfl⟩ : syracuseStep 997547 = 1496321) B1496321
theorem B4044973 : Blo 996598 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B997559 : Blo 996598 997559 := bstep (se 1 (by rfl) ⟨748169, by rfl⟩ : syracuseStep 997559 = 1496339) B1496339
theorem B2242763 : Blo 996598 2242763 := bstep (se 1 (by rfl) ⟨1682072, by rfl⟩ : syracuseStep 2242763 = 3364145) B3364145
theorem B997579 : Blo 996598 997579 := bstep (se 1 (by rfl) ⟨748184, by rfl⟩ : syracuseStep 997579 = 1496369) B1496369
theorem B997591 : Blo 996598 997591 := bstep (se 1 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 997591 = 1496387) B1496387
theorem B997611 : Blo 996598 997611 := bstep (se 1 (by rfl) ⟨748208, by rfl⟩ : syracuseStep 997611 = 1496417) B1496417
theorem B997623 : Blo 996598 997623 := bstep (se 1 (by rfl) ⟨748217, by rfl⟩ : syracuseStep 997623 = 1496435) B1496435
theorem B2242817 : Blo 996598 2242817 := bstep (se 2 (by rfl) ⟨841056, by rfl⟩ : syracuseStep 2242817 = 1682113) B1682113
theorem B15644933 : Blo 996598 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B997643 : Blo 996598 997643 := bstep (se 1 (by rfl) ⟨748232, by rfl⟩ : syracuseStep 997643 = 1496465) B1496465
theorem B997655 : Blo 996598 997655 := bstep (se 1 (by rfl) ⟨748241, by rfl⟩ : syracuseStep 997655 = 1496483) B1496483
theorem B1685785 : Blo 996598 1685785 := bstep (se 2 (by rfl) ⟨632169, by rfl⟩ : syracuseStep 1685785 = 1264339) B1264339
theorem B997675 : Blo 996598 997675 := bstep (se 1 (by rfl) ⟨748256, by rfl⟩ : syracuseStep 997675 = 1496513) B1496513
theorem B997687 : Blo 996598 997687 := bstep (se 1 (by rfl) ⟨748265, by rfl⟩ : syracuseStep 997687 = 1496531) B1496531
theorem B997707 : Blo 996598 997707 := bstep (se 1 (by rfl) ⟨748280, by rfl⟩ : syracuseStep 997707 = 1496561) B1496561
theorem B997719 : Blo 996598 997719 := bstep (se 1 (by rfl) ⟨748289, by rfl⟩ : syracuseStep 997719 = 1496579) B1496579
theorem B1423703 : Blo 996598 1423703 := bstep (se 1 (by rfl) ⟨1067777, by rfl⟩ : syracuseStep 1423703 = 2135555) B2135555
theorem B997739 : Blo 996598 997739 := bstep (se 1 (by rfl) ⟨748304, by rfl⟩ : syracuseStep 997739 = 1496609) B1496609
theorem B997751 : Blo 996598 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B997771 : Blo 996598 997771 := bstep (se 1 (by rfl) ⟨748328, by rfl⟩ : syracuseStep 997771 = 1496657) B1496657
theorem B997783 : Blo 996598 997783 := bstep (se 1 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 997783 = 1496675) B1496675
theorem B997803 : Blo 996598 997803 := bstep (se 1 (by rfl) ⟨748352, by rfl⟩ : syracuseStep 997803 = 1496705) B1496705
theorem B997815 : Blo 996598 997815 := bstep (se 1 (by rfl) ⟨748361, by rfl⟩ : syracuseStep 997815 = 1496723) B1496723
theorem B997835 : Blo 996598 997835 := bstep (se 1 (by rfl) ⟨748376, by rfl⟩ : syracuseStep 997835 = 1496753) B1496753
theorem B997847 : Blo 996598 997847 := bstep (se 1 (by rfl) ⟨748385, by rfl⟩ : syracuseStep 997847 = 1496771) B1496771
theorem B2243033 : Blo 996598 2243033 := bstep (se 2 (by rfl) ⟨841137, by rfl⟩ : syracuseStep 2243033 = 1682275) B1682275
theorem B997867 : Blo 996598 997867 := bstep (se 1 (by rfl) ⟨748400, by rfl⟩ : syracuseStep 997867 = 1496801) B1496801
theorem B997879 : Blo 996598 997879 := bstep (se 1 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 997879 = 1496819) B1496819
theorem B997899 : Blo 996598 997899 := bstep (se 1 (by rfl) ⟨748424, by rfl⟩ : syracuseStep 997899 = 1496849) B1496849
theorem B17054225 : Blo 996598 17054225 := bstep (se 2 (by rfl) ⟨6395334, by rfl⟩ : syracuseStep 17054225 = 12790669) B12790669
theorem B997911 : Blo 996598 997911 := bstep (se 1 (by rfl) ⟨748433, by rfl⟩ : syracuseStep 997911 = 1496867) B1496867
theorem B997931 : Blo 996598 997931 := bstep (se 1 (by rfl) ⟨748448, by rfl⟩ : syracuseStep 997931 = 1496897) B1496897
theorem B6076973 : Blo 996598 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B2243123 : Blo 996598 2243123 := bstep (se 1 (by rfl) ⟨1682342, by rfl⟩ : syracuseStep 2243123 = 3364685) B3364685
theorem B997943 : Blo 996598 997943 := bstep (se 1 (by rfl) ⟨748457, by rfl⟩ : syracuseStep 997943 = 1496915) B1496915
theorem B997963 : Blo 996598 997963 := bstep (se 1 (by rfl) ⟨748472, by rfl⟩ : syracuseStep 997963 = 1496945) B1496945
theorem B2243159 : Blo 996598 2243159 := bstep (se 1 (by rfl) ⟨1682369, by rfl⟩ : syracuseStep 2243159 = 3364739) B3364739
theorem B997975 : Blo 996598 997975 := bstep (se 1 (by rfl) ⟨748481, by rfl⟩ : syracuseStep 997975 = 1496963) B1496963
theorem B997995 : Blo 996598 997995 := bstep (se 1 (by rfl) ⟨748496, by rfl⟩ : syracuseStep 997995 = 1496993) B1496993
theorem B998007 : Blo 996598 998007 := bstep (se 1 (by rfl) ⟨748505, by rfl⟩ : syracuseStep 998007 = 1497011) B1497011
theorem B998027 : Blo 996598 998027 := bstep (se 1 (by rfl) ⟨748520, by rfl⟩ : syracuseStep 998027 = 1497041) B1497041
theorem B998039 : Blo 996598 998039 := bstep (se 1 (by rfl) ⟨748529, by rfl⟩ : syracuseStep 998039 = 1497059) B1497059
theorem B998059 : Blo 996598 998059 := bstep (se 1 (by rfl) ⟨748544, by rfl⟩ : syracuseStep 998059 = 1497089) B1497089
theorem B998071 : Blo 996598 998071 := bstep (se 1 (by rfl) ⟨748553, by rfl⟩ : syracuseStep 998071 = 1497107) B1497107
theorem B998091 : Blo 996598 998091 := bstep (se 1 (by rfl) ⟨748568, by rfl⟩ : syracuseStep 998091 = 1497137) B1497137
theorem B998103 : Blo 996598 998103 := bstep (se 1 (by rfl) ⟨748577, by rfl⟩ : syracuseStep 998103 = 1497155) B1497155
theorem B998123 : Blo 996598 998123 := bstep (se 1 (by rfl) ⟨748592, by rfl⟩ : syracuseStep 998123 = 1497185) B1497185
theorem B998135 : Blo 996598 998135 := bstep (se 1 (by rfl) ⟨748601, by rfl⟩ : syracuseStep 998135 = 1497203) B1497203
theorem B2243339 : Blo 996598 2243339 := bstep (se 1 (by rfl) ⟨1682504, by rfl⟩ : syracuseStep 2243339 = 3365009) B3365009
theorem B998155 : Blo 996598 998155 := bstep (se 1 (by rfl) ⟨748616, by rfl⟩ : syracuseStep 998155 = 1497233) B1497233
theorem B998167 : Blo 996598 998167 := bstep (se 1 (by rfl) ⟨748625, by rfl⟩ : syracuseStep 998167 = 1497251) B1497251
theorem B998187 : Blo 996598 998187 := bstep (se 1 (by rfl) ⟨748640, by rfl⟩ : syracuseStep 998187 = 1497281) B1497281
theorem B998199 : Blo 996598 998199 := bstep (se 1 (by rfl) ⟨748649, by rfl⟩ : syracuseStep 998199 = 1497299) B1497299
theorem B2243393 : Blo 996598 2243393 := bstep (se 2 (by rfl) ⟨841272, by rfl⟩ : syracuseStep 2243393 = 1682545) B1682545
theorem B998219 : Blo 996598 998219 := bstep (se 1 (by rfl) ⟨748664, by rfl⟩ : syracuseStep 998219 = 1497329) B1497329
theorem B998231 : Blo 996598 998231 := bstep (se 1 (by rfl) ⟨748673, by rfl⟩ : syracuseStep 998231 = 1497347) B1497347
theorem B1686359 : Blo 996598 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B998251 : Blo 996598 998251 := bstep (se 1 (by rfl) ⟨748688, by rfl⟩ : syracuseStep 998251 = 1497377) B1497377
theorem B998263 : Blo 996598 998263 := bstep (se 1 (by rfl) ⟨748697, by rfl⟩ : syracuseStep 998263 = 1497395) B1497395
theorem B998283 : Blo 996598 998283 := bstep (se 1 (by rfl) ⟨748712, by rfl⟩ : syracuseStep 998283 = 1497425) B1497425
theorem B998295 : Blo 996598 998295 := bstep (se 1 (by rfl) ⟨748721, by rfl⟩ : syracuseStep 998295 = 1497443) B1497443
theorem B5061527 : Blo 996598 5061527 := bstep (se 1 (by rfl) ⟨3796145, by rfl⟩ : syracuseStep 5061527 = 7592291) B7592291
theorem B998315 : Blo 996598 998315 := bstep (se 1 (by rfl) ⟨748736, by rfl⟩ : syracuseStep 998315 = 1497473) B1497473
theorem B998327 : Blo 996598 998327 := bstep (se 1 (by rfl) ⟨748745, by rfl⟩ : syracuseStep 998327 = 1497491) B1497491
theorem B998347 : Blo 996598 998347 := bstep (se 1 (by rfl) ⟨748760, by rfl⟩ : syracuseStep 998347 = 1497521) B1497521
theorem B998359 : Blo 996598 998359 := bstep (se 1 (by rfl) ⟨748769, by rfl⟩ : syracuseStep 998359 = 1497539) B1497539
theorem B1686487 : Blo 996598 1686487 := bstep (se 1 (by rfl) ⟨1264865, by rfl⟩ : syracuseStep 1686487 = 2529731) B2529731
theorem B998379 : Blo 996598 998379 := bstep (se 1 (by rfl) ⟨748784, by rfl⟩ : syracuseStep 998379 = 1497569) B1497569
theorem B998391 : Blo 996598 998391 := bstep (se 1 (by rfl) ⟨748793, by rfl⟩ : syracuseStep 998391 = 1497587) B1497587
theorem B998411 : Blo 996598 998411 := bstep (se 1 (by rfl) ⟨748808, by rfl⟩ : syracuseStep 998411 = 1497617) B1497617
theorem B998423 : Blo 996598 998423 := bstep (se 1 (by rfl) ⟨748817, by rfl⟩ : syracuseStep 998423 = 1497635) B1497635
theorem B2243609 : Blo 996598 2243609 := bstep (se 2 (by rfl) ⟨841353, by rfl⟩ : syracuseStep 2243609 = 1682707) B1682707
theorem B998443 : Blo 996598 998443 := bstep (se 1 (by rfl) ⟨748832, by rfl⟩ : syracuseStep 998443 = 1497665) B1497665
theorem B998455 : Blo 996598 998455 := bstep (se 1 (by rfl) ⟨748841, by rfl⟩ : syracuseStep 998455 = 1497683) B1497683
theorem B998475 : Blo 996598 998475 := bstep (se 1 (by rfl) ⟨748856, by rfl⟩ : syracuseStep 998475 = 1497713) B1497713
theorem B998487 : Blo 996598 998487 := bstep (se 1 (by rfl) ⟨748865, by rfl⟩ : syracuseStep 998487 = 1497731) B1497731
theorem B998507 : Blo 996598 998507 := bstep (se 1 (by rfl) ⟨748880, by rfl⟩ : syracuseStep 998507 = 1497761) B1497761
theorem B2243699 : Blo 996598 2243699 := bstep (se 1 (by rfl) ⟨1682774, by rfl⟩ : syracuseStep 2243699 = 3365549) B3365549
theorem B998519 : Blo 996598 998519 := bstep (se 1 (by rfl) ⟨748889, by rfl⟩ : syracuseStep 998519 = 1497779) B1497779
theorem B998539 : Blo 996598 998539 := bstep (se 1 (by rfl) ⟨748904, by rfl⟩ : syracuseStep 998539 = 1497809) B1497809
theorem B2243735 : Blo 996598 2243735 := bstep (se 1 (by rfl) ⟨1682801, by rfl⟩ : syracuseStep 2243735 = 3365603) B3365603
theorem B998551 : Blo 996598 998551 := bstep (se 1 (by rfl) ⟨748913, by rfl⟩ : syracuseStep 998551 = 1497827) B1497827
theorem B998571 : Blo 996598 998571 := bstep (se 1 (by rfl) ⟨748928, by rfl⟩ : syracuseStep 998571 = 1497857) B1497857
theorem B998583 : Blo 996598 998583 := bstep (se 1 (by rfl) ⟨748937, by rfl⟩ : syracuseStep 998583 = 1497875) B1497875
theorem B998603 : Blo 996598 998603 := bstep (se 1 (by rfl) ⟨748952, by rfl⟩ : syracuseStep 998603 = 1497905) B1497905
theorem B998615 : Blo 996598 998615 := bstep (se 1 (by rfl) ⟨748961, by rfl⟩ : syracuseStep 998615 = 1497923) B1497923
theorem B998635 : Blo 996598 998635 := bstep (se 1 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 998635 = 1497953) B1497953
theorem B998647 : Blo 996598 998647 := bstep (se 1 (by rfl) ⟨748985, by rfl⟩ : syracuseStep 998647 = 1497971) B1497971
theorem B998667 : Blo 996598 998667 := bstep (se 1 (by rfl) ⟨749000, by rfl⟩ : syracuseStep 998667 = 1498001) B1498001
theorem B998679 : Blo 996598 998679 := bstep (se 1 (by rfl) ⟨749009, by rfl⟩ : syracuseStep 998679 = 1498019) B1498019
theorem B998699 : Blo 996598 998699 := bstep (se 1 (by rfl) ⟨749024, by rfl⟩ : syracuseStep 998699 = 1498049) B1498049
theorem B998711 : Blo 996598 998711 := bstep (se 1 (by rfl) ⟨749033, by rfl⟩ : syracuseStep 998711 = 1498067) B1498067
theorem B2243915 : Blo 996598 2243915 := bstep (se 1 (by rfl) ⟨1682936, by rfl⟩ : syracuseStep 2243915 = 3365873) B3365873
theorem B998731 : Blo 996598 998731 := bstep (se 1 (by rfl) ⟨749048, by rfl⟩ : syracuseStep 998731 = 1498097) B1498097
theorem B998743 : Blo 996598 998743 := bstep (se 1 (by rfl) ⟨749057, by rfl⟩ : syracuseStep 998743 = 1498115) B1498115
theorem B11353445 : Blo 996598 11353445 := bstep (se 4 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 11353445 = 2128771) B2128771
theorem B998763 : Blo 996598 998763 := bstep (se 1 (by rfl) ⟨749072, by rfl⟩ : syracuseStep 998763 = 1498145) B1498145
theorem B998775 : Blo 996598 998775 := bstep (se 1 (by rfl) ⟨749081, by rfl⟩ : syracuseStep 998775 = 1498163) B1498163
theorem B2243969 : Blo 996598 2243969 := bstep (se 2 (by rfl) ⟨841488, by rfl⟩ : syracuseStep 2243969 = 1682977) B1682977
theorem B998795 : Blo 996598 998795 := bstep (se 1 (by rfl) ⟨749096, by rfl⟩ : syracuseStep 998795 = 1498193) B1498193
theorem B1097111 : Blo 996598 1097111 := bstep (se 1 (by rfl) ⟨822833, by rfl⟩ : syracuseStep 1097111 = 1645667) B1645667
theorem B998807 : Blo 996598 998807 := bstep (se 1 (by rfl) ⟨749105, by rfl⟩ : syracuseStep 998807 = 1498211) B1498211
theorem B998827 : Blo 996598 998827 := bstep (se 1 (by rfl) ⟨749120, by rfl⟩ : syracuseStep 998827 = 1498241) B1498241
theorem B998839 : Blo 996598 998839 := bstep (se 1 (by rfl) ⟨749129, by rfl⟩ : syracuseStep 998839 = 1498259) B1498259
theorem B998859 : Blo 996598 998859 := bstep (se 1 (by rfl) ⟨749144, by rfl⟩ : syracuseStep 998859 = 1498289) B1498289
theorem B998871 : Blo 996598 998871 := bstep (se 1 (by rfl) ⟨749153, by rfl⟩ : syracuseStep 998871 = 1498307) B1498307
theorem B998891 : Blo 996598 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B998903 : Blo 996598 998903 := bstep (se 1 (by rfl) ⟨749177, by rfl⟩ : syracuseStep 998903 = 1498355) B1498355
theorem B998923 : Blo 996598 998923 := bstep (se 1 (by rfl) ⟨749192, by rfl⟩ : syracuseStep 998923 = 1498385) B1498385
theorem B998935 : Blo 996598 998935 := bstep (se 1 (by rfl) ⟨749201, by rfl⟩ : syracuseStep 998935 = 1498403) B1498403
theorem B998955 : Blo 996598 998955 := bstep (se 1 (by rfl) ⟨749216, by rfl⟩ : syracuseStep 998955 = 1498433) B1498433
theorem B998967 : Blo 996598 998967 := bstep (se 1 (by rfl) ⟨749225, by rfl⟩ : syracuseStep 998967 = 1498451) B1498451
theorem B998987 : Blo 996598 998987 := bstep (se 1 (by rfl) ⟨749240, by rfl⟩ : syracuseStep 998987 = 1498481) B1498481
theorem B1687115 : Blo 996598 1687115 := bstep (se 1 (by rfl) ⟨1265336, by rfl⟩ : syracuseStep 1687115 = 2530673) B2530673
theorem B998999 : Blo 996598 998999 := bstep (se 1 (by rfl) ⟨749249, by rfl⟩ : syracuseStep 998999 = 1498499) B1498499
theorem B2244185 : Blo 996598 2244185 := bstep (se 2 (by rfl) ⟨841569, by rfl⟩ : syracuseStep 2244185 = 1683139) B1683139
theorem B999019 : Blo 996598 999019 := bstep (se 1 (by rfl) ⟨749264, by rfl⟩ : syracuseStep 999019 = 1498529) B1498529
theorem B999031 : Blo 996598 999031 := bstep (se 1 (by rfl) ⟨749273, by rfl⟩ : syracuseStep 999031 = 1498547) B1498547
theorem B999051 : Blo 996598 999051 := bstep (se 1 (by rfl) ⟨749288, by rfl⟩ : syracuseStep 999051 = 1498577) B1498577
theorem B999063 : Blo 996598 999063 := bstep (se 1 (by rfl) ⟨749297, by rfl⟩ : syracuseStep 999063 = 1498595) B1498595
theorem B999083 : Blo 996598 999083 := bstep (se 1 (by rfl) ⟨749312, by rfl⟩ : syracuseStep 999083 = 1498625) B1498625
theorem B2244275 : Blo 996598 2244275 := bstep (se 1 (by rfl) ⟨1683206, by rfl⟩ : syracuseStep 2244275 = 3366413) B3366413
theorem B999095 : Blo 996598 999095 := bstep (se 1 (by rfl) ⟨749321, by rfl⟩ : syracuseStep 999095 = 1498643) B1498643
theorem B999115 : Blo 996598 999115 := bstep (se 1 (by rfl) ⟨749336, by rfl⟩ : syracuseStep 999115 = 1498673) B1498673
theorem B1687243 : Blo 996598 1687243 := bstep (se 1 (by rfl) ⟨1265432, by rfl⟩ : syracuseStep 1687243 = 2530865) B2530865
theorem B2244311 : Blo 996598 2244311 := bstep (se 1 (by rfl) ⟨1683233, by rfl⟩ : syracuseStep 2244311 = 3366467) B3366467
theorem B999127 : Blo 996598 999127 := bstep (se 1 (by rfl) ⟨749345, by rfl⟩ : syracuseStep 999127 = 1498691) B1498691
theorem B999147 : Blo 996598 999147 := bstep (se 1 (by rfl) ⟨749360, by rfl⟩ : syracuseStep 999147 = 1498721) B1498721
theorem B999159 : Blo 996598 999159 := bstep (se 1 (by rfl) ⟨749369, by rfl⟩ : syracuseStep 999159 = 1498739) B1498739
theorem B999179 : Blo 996598 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B999191 : Blo 996598 999191 := bstep (se 1 (by rfl) ⟨749393, by rfl⟩ : syracuseStep 999191 = 1498787) B1498787
theorem B2703127 : Blo 996598 2703127 := bstep (se 1 (by rfl) ⟨2027345, by rfl⟩ : syracuseStep 2703127 = 4054691) B4054691
theorem B999211 : Blo 996598 999211 := bstep (se 1 (by rfl) ⟨749408, by rfl⟩ : syracuseStep 999211 = 1498817) B1498817
theorem B999223 : Blo 996598 999223 := bstep (se 1 (by rfl) ⟨749417, by rfl⟩ : syracuseStep 999223 = 1498835) B1498835
theorem B999243 : Blo 996598 999243 := bstep (se 1 (by rfl) ⟨749432, by rfl⟩ : syracuseStep 999243 = 1498865) B1498865
theorem B999255 : Blo 996598 999255 := bstep (se 1 (by rfl) ⟨749441, by rfl⟩ : syracuseStep 999255 = 1498883) B1498883
theorem B1687385 : Blo 996598 1687385 := bstep (se 2 (by rfl) ⟨632769, by rfl⟩ : syracuseStep 1687385 = 1265539) B1265539
theorem B999275 : Blo 996598 999275 := bstep (se 1 (by rfl) ⟨749456, by rfl⟩ : syracuseStep 999275 = 1498913) B1498913
theorem B999287 : Blo 996598 999287 := bstep (se 1 (by rfl) ⟨749465, by rfl⟩ : syracuseStep 999287 = 1498931) B1498931
theorem B2244491 : Blo 996598 2244491 := bstep (se 1 (by rfl) ⟨1683368, by rfl⟩ : syracuseStep 2244491 = 3366737) B3366737
theorem B999307 : Blo 996598 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B999319 : Blo 996598 999319 := bstep (se 1 (by rfl) ⟨749489, by rfl⟩ : syracuseStep 999319 = 1498979) B1498979
theorem B999339 : Blo 996598 999339 := bstep (se 1 (by rfl) ⟨749504, by rfl⟩ : syracuseStep 999339 = 1499009) B1499009
theorem B999351 : Blo 996598 999351 := bstep (se 1 (by rfl) ⟨749513, by rfl⟩ : syracuseStep 999351 = 1499027) B1499027
theorem B2244545 : Blo 996598 2244545 := bstep (se 2 (by rfl) ⟨841704, by rfl⟩ : syracuseStep 2244545 = 1683409) B1683409
theorem B999371 : Blo 996598 999371 := bstep (se 1 (by rfl) ⟨749528, by rfl⟩ : syracuseStep 999371 = 1499057) B1499057
theorem B999383 : Blo 996598 999383 := bstep (se 1 (by rfl) ⟨749537, by rfl⟩ : syracuseStep 999383 = 1499075) B1499075
theorem B1687513 : Blo 996598 1687513 := bstep (se 2 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 1687513 = 1265635) B1265635
theorem B999403 : Blo 996598 999403 := bstep (se 1 (by rfl) ⟨749552, by rfl⟩ : syracuseStep 999403 = 1499105) B1499105
theorem B999415 : Blo 996598 999415 := bstep (se 1 (by rfl) ⟨749561, by rfl⟩ : syracuseStep 999415 = 1499123) B1499123
theorem B999435 : Blo 996598 999435 := bstep (se 1 (by rfl) ⟨749576, by rfl⟩ : syracuseStep 999435 = 1499153) B1499153
theorem B999447 : Blo 996598 999447 := bstep (se 1 (by rfl) ⟨749585, by rfl⟩ : syracuseStep 999447 = 1499171) B1499171
theorem B12468259 : Blo 996598 12468259 := bstep (se 1 (by rfl) ⟨9351194, by rfl⟩ : syracuseStep 12468259 = 18702389) B18702389
theorem B999467 : Blo 996598 999467 := bstep (se 1 (by rfl) ⟨749600, by rfl⟩ : syracuseStep 999467 = 1499201) B1499201
theorem B999479 : Blo 996598 999479 := bstep (se 1 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 999479 = 1499219) B1499219
theorem B5390401 : Blo 996598 5390401 := bstep (se 2 (by rfl) ⟨2021400, by rfl⟩ : syracuseStep 5390401 = 4042801) B4042801
theorem B1065035 : Blo 996598 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B999499 : Blo 996598 999499 := bstep (se 1 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 999499 = 1499249) B1499249
theorem B3653707 : Blo 996598 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B999511 : Blo 996598 999511 := bstep (se 1 (by rfl) ⟨749633, by rfl⟩ : syracuseStep 999511 = 1499267) B1499267
theorem B999531 : Blo 996598 999531 := bstep (se 1 (by rfl) ⟨749648, by rfl⟩ : syracuseStep 999531 = 1499297) B1499297
theorem B999543 : Blo 996598 999543 := bstep (se 1 (by rfl) ⟨749657, by rfl⟩ : syracuseStep 999543 = 1499315) B1499315
theorem B999563 : Blo 996598 999563 := bstep (se 1 (by rfl) ⟨749672, by rfl⟩ : syracuseStep 999563 = 1499345) B1499345
theorem B999575 : Blo 996598 999575 := bstep (se 1 (by rfl) ⟨749681, by rfl⟩ : syracuseStep 999575 = 1499363) B1499363
theorem B2244761 : Blo 996598 2244761 := bstep (se 2 (by rfl) ⟨841785, by rfl⟩ : syracuseStep 2244761 = 1683571) B1683571
theorem B999595 : Blo 996598 999595 := bstep (se 1 (by rfl) ⟨749696, by rfl⟩ : syracuseStep 999595 = 1499393) B1499393
theorem B3784877 : Blo 996598 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B999607 : Blo 996598 999607 := bstep (se 1 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 999607 = 1499411) B1499411
theorem B3784907 : Blo 996598 3784907 := bstep (se 1 (by rfl) ⟨2838680, by rfl⟩ : syracuseStep 3784907 = 5677361) B5677361
theorem B999627 : Blo 996598 999627 := bstep (se 1 (by rfl) ⟨749720, by rfl⟩ : syracuseStep 999627 = 1499441) B1499441
theorem B999639 : Blo 996598 999639 := bstep (se 1 (by rfl) ⟨749729, by rfl⟩ : syracuseStep 999639 = 1499459) B1499459
theorem B7192793 : Blo 996598 7192793 := bstep (se 2 (by rfl) ⟨2697297, by rfl⟩ : syracuseStep 7192793 = 5394595) B5394595
theorem B999659 : Blo 996598 999659 := bstep (se 1 (by rfl) ⟨749744, by rfl⟩ : syracuseStep 999659 = 1499489) B1499489
theorem B2244851 : Blo 996598 2244851 := bstep (se 1 (by rfl) ⟨1683638, by rfl⟩ : syracuseStep 2244851 = 3367277) B3367277
theorem B999671 : Blo 996598 999671 := bstep (se 1 (by rfl) ⟨749753, by rfl⟩ : syracuseStep 999671 = 1499507) B1499507
theorem B999691 : Blo 996598 999691 := bstep (se 1 (by rfl) ⟨749768, by rfl⟩ : syracuseStep 999691 = 1499537) B1499537
theorem B2244887 : Blo 996598 2244887 := bstep (se 1 (by rfl) ⟨1683665, by rfl⟩ : syracuseStep 2244887 = 3367331) B3367331
theorem B999703 : Blo 996598 999703 := bstep (se 1 (by rfl) ⟨749777, by rfl⟩ : syracuseStep 999703 = 1499555) B1499555
theorem B999723 : Blo 996598 999723 := bstep (se 1 (by rfl) ⟨749792, by rfl⟩ : syracuseStep 999723 = 1499585) B1499585
theorem B999735 : Blo 996598 999735 := bstep (se 1 (by rfl) ⟨749801, by rfl⟩ : syracuseStep 999735 = 1499603) B1499603
theorem B999755 : Blo 996598 999755 := bstep (se 1 (by rfl) ⟨749816, by rfl⟩ : syracuseStep 999755 = 1499633) B1499633
theorem B999767 : Blo 996598 999767 := bstep (se 1 (by rfl) ⟨749825, by rfl⟩ : syracuseStep 999767 = 1499651) B1499651
theorem B999787 : Blo 996598 999787 := bstep (se 1 (by rfl) ⟨749840, by rfl⟩ : syracuseStep 999787 = 1499681) B1499681
theorem B999799 : Blo 996598 999799 := bstep (se 1 (by rfl) ⟨749849, by rfl⟩ : syracuseStep 999799 = 1499699) B1499699
theorem B999819 : Blo 996598 999819 := bstep (se 1 (by rfl) ⟨749864, by rfl⟩ : syracuseStep 999819 = 1499729) B1499729
theorem B1261975 : Blo 996598 1261975 := bstep (se 1 (by rfl) ⟨946481, by rfl⟩ : syracuseStep 1261975 = 1892963) B1892963
theorem B999831 : Blo 996598 999831 := bstep (se 1 (by rfl) ⟨749873, by rfl⟩ : syracuseStep 999831 = 1499747) B1499747
theorem B999851 : Blo 996598 999851 := bstep (se 1 (by rfl) ⟨749888, by rfl⟩ : syracuseStep 999851 = 1499777) B1499777
theorem B999863 : Blo 996598 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B2245067 : Blo 996598 2245067 := bstep (se 1 (by rfl) ⟨1683800, by rfl⟩ : syracuseStep 2245067 = 3367601) B3367601
theorem B999883 : Blo 996598 999883 := bstep (se 1 (by rfl) ⟨749912, by rfl⟩ : syracuseStep 999883 = 1499825) B1499825
theorem B999895 : Blo 996598 999895 := bstep (se 1 (by rfl) ⟨749921, by rfl⟩ : syracuseStep 999895 = 1499843) B1499843
theorem B999915 : Blo 996598 999915 := bstep (se 1 (by rfl) ⟨749936, by rfl⟩ : syracuseStep 999915 = 1499873) B1499873
theorem B999927 : Blo 996598 999927 := bstep (se 1 (by rfl) ⟨749945, by rfl⟩ : syracuseStep 999927 = 1499891) B1499891
theorem B2245121 : Blo 996598 2245121 := bstep (se 2 (by rfl) ⟨841920, by rfl⟩ : syracuseStep 2245121 = 1683841) B1683841
theorem B999947 : Blo 996598 999947 := bstep (se 1 (by rfl) ⟨749960, by rfl⟩ : syracuseStep 999947 = 1499921) B1499921
theorem B999959 : Blo 996598 999959 := bstep (se 1 (by rfl) ⟨749969, by rfl⟩ : syracuseStep 999959 = 1499939) B1499939
theorem B1688087 : Blo 996598 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B999979 : Blo 996598 999979 := bstep (se 1 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 999979 = 1499969) B1499969
theorem B999991 : Blo 996598 999991 := bstep (se 1 (by rfl) ⟨749993, by rfl⟩ : syracuseStep 999991 = 1499987) B1499987
theorem B5685835 : Blo 996598 5685835 := bstep (se 1 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 5685835 = 8528753) B8528753
theorem B1000011 : Blo 996598 1000011 := bstep (se 1 (by rfl) ⟨750008, by rfl⟩ : syracuseStep 1000011 = 1500017) B1500017
theorem B2310743 : Blo 996598 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B1000023 : Blo 996598 1000023 := bstep (se 1 (by rfl) ⟨750017, by rfl⟩ : syracuseStep 1000023 = 1500035) B1500035
theorem B1000043 : Blo 996598 1000043 := bstep (se 1 (by rfl) ⟨750032, by rfl⟩ : syracuseStep 1000043 = 1500065) B1500065
theorem B1000055 : Blo 996598 1000055 := bstep (se 1 (by rfl) ⟨750041, by rfl⟩ : syracuseStep 1000055 = 1500083) B1500083
theorem B1000075 : Blo 996598 1000075 := bstep (se 1 (by rfl) ⟨750056, by rfl⟩ : syracuseStep 1000075 = 1500113) B1500113
theorem B3850897 : Blo 996598 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B1000087 : Blo 996598 1000087 := bstep (se 1 (by rfl) ⟨750065, by rfl⟩ : syracuseStep 1000087 = 1500131) B1500131
theorem B1688215 : Blo 996598 1688215 := bstep (se 1 (by rfl) ⟨1266161, by rfl⟩ : syracuseStep 1688215 = 2532323) B2532323
theorem B1000107 : Blo 996598 1000107 := bstep (se 1 (by rfl) ⟨750080, by rfl⟩ : syracuseStep 1000107 = 1500161) B1500161
theorem B1000119 : Blo 996598 1000119 := bstep (se 1 (by rfl) ⟨750089, by rfl⟩ : syracuseStep 1000119 = 1500179) B1500179
theorem B1000139 : Blo 996598 1000139 := bstep (se 1 (by rfl) ⟨750104, by rfl⟩ : syracuseStep 1000139 = 1500209) B1500209
theorem B1000151 : Blo 996598 1000151 := bstep (se 1 (by rfl) ⟨750113, by rfl⟩ : syracuseStep 1000151 = 1500227) B1500227
theorem B2245337 : Blo 996598 2245337 := bstep (se 2 (by rfl) ⟨842001, by rfl⟩ : syracuseStep 2245337 = 1684003) B1684003
theorem B1000171 : Blo 996598 1000171 := bstep (se 1 (by rfl) ⟨750128, by rfl⟩ : syracuseStep 1000171 = 1500257) B1500257
theorem B1000183 : Blo 996598 1000183 := bstep (se 1 (by rfl) ⟨750137, by rfl⟩ : syracuseStep 1000183 = 1500275) B1500275
theorem B1000203 : Blo 996598 1000203 := bstep (se 1 (by rfl) ⟨750152, by rfl⟩ : syracuseStep 1000203 = 1500305) B1500305
theorem B1000215 : Blo 996598 1000215 := bstep (se 1 (by rfl) ⟨750161, by rfl⟩ : syracuseStep 1000215 = 1500323) B1500323
theorem B1000235 : Blo 996598 1000235 := bstep (se 1 (by rfl) ⟨750176, by rfl⟩ : syracuseStep 1000235 = 1500353) B1500353
theorem B2245427 : Blo 996598 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B2736947 : Blo 996598 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B1000247 : Blo 996598 1000247 := bstep (se 1 (by rfl) ⟨750185, by rfl⟩ : syracuseStep 1000247 = 1500371) B1500371
theorem B1000267 : Blo 996598 1000267 := bstep (se 1 (by rfl) ⟨750200, by rfl⟩ : syracuseStep 1000267 = 1500401) B1500401
theorem B2245463 : Blo 996598 2245463 := bstep (se 1 (by rfl) ⟨1684097, by rfl⟩ : syracuseStep 2245463 = 3368195) B3368195
theorem B1000279 : Blo 996598 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B3785561 : Blo 996598 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B5686109 : Blo 996598 5686109 := bstep (se 3 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 5686109 = 2132291) B2132291
theorem B1000299 : Blo 996598 1000299 := bstep (se 1 (by rfl) ⟨750224, by rfl⟩ : syracuseStep 1000299 = 1500449) B1500449
theorem B1000311 : Blo 996598 1000311 := bstep (se 1 (by rfl) ⟨750233, by rfl⟩ : syracuseStep 1000311 = 1500467) B1500467
theorem B1000331 : Blo 996598 1000331 := bstep (se 1 (by rfl) ⟨750248, by rfl⟩ : syracuseStep 1000331 = 1500497) B1500497
theorem B1000343 : Blo 996598 1000343 := bstep (se 1 (by rfl) ⟨750257, by rfl⟩ : syracuseStep 1000343 = 1500515) B1500515
theorem B1000363 : Blo 996598 1000363 := bstep (se 1 (by rfl) ⟨750272, by rfl⟩ : syracuseStep 1000363 = 1500545) B1500545
theorem B1000375 : Blo 996598 1000375 := bstep (se 1 (by rfl) ⟨750281, by rfl⟩ : syracuseStep 1000375 = 1500563) B1500563
theorem B1000395 : Blo 996598 1000395 := bstep (se 1 (by rfl) ⟨750296, by rfl⟩ : syracuseStep 1000395 = 1500593) B1500593
theorem B1000407 : Blo 996598 1000407 := bstep (se 1 (by rfl) ⟨750305, by rfl⟩ : syracuseStep 1000407 = 1500611) B1500611
theorem B1000427 : Blo 996598 1000427 := bstep (se 1 (by rfl) ⟨750320, by rfl⟩ : syracuseStep 1000427 = 1500641) B1500641
theorem B1000439 : Blo 996598 1000439 := bstep (se 1 (by rfl) ⟨750329, by rfl⟩ : syracuseStep 1000439 = 1500659) B1500659
theorem B2245643 : Blo 996598 2245643 := bstep (se 1 (by rfl) ⟨1684232, by rfl⟩ : syracuseStep 2245643 = 3368465) B3368465
theorem B1000459 : Blo 996598 1000459 := bstep (se 1 (by rfl) ⟨750344, by rfl⟩ : syracuseStep 1000459 = 1500689) B1500689
theorem B16172045 : Blo 996598 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B1000471 : Blo 996598 1000471 := bstep (se 1 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 1000471 = 1500707) B1500707
theorem B1000491 : Blo 996598 1000491 := bstep (se 1 (by rfl) ⟨750368, by rfl⟩ : syracuseStep 1000491 = 1500737) B1500737
theorem B1000503 : Blo 996598 1000503 := bstep (se 1 (by rfl) ⟨750377, by rfl⟩ : syracuseStep 1000503 = 1500755) B1500755
theorem B2245697 : Blo 996598 2245697 := bstep (se 2 (by rfl) ⟨842136, by rfl⟩ : syracuseStep 2245697 = 1684273) B1684273
theorem B1000523 : Blo 996598 1000523 := bstep (se 1 (by rfl) ⟨750392, by rfl⟩ : syracuseStep 1000523 = 1500785) B1500785
theorem B1000535 : Blo 996598 1000535 := bstep (se 1 (by rfl) ⟨750401, by rfl⟩ : syracuseStep 1000535 = 1500803) B1500803
theorem B1000555 : Blo 996598 1000555 := bstep (se 1 (by rfl) ⟨750416, by rfl⟩ : syracuseStep 1000555 = 1500833) B1500833
theorem B1000567 : Blo 996598 1000567 := bstep (se 1 (by rfl) ⟨750425, by rfl⟩ : syracuseStep 1000567 = 1500851) B1500851
theorem B1000587 : Blo 996598 1000587 := bstep (se 1 (by rfl) ⟨750440, by rfl⟩ : syracuseStep 1000587 = 1500881) B1500881
theorem B3785879 : Blo 996598 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B15385841 : Blo 996598 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B1066231 : Blo 996598 1066231 := bstep (se 1 (by rfl) ⟨799673, by rfl⟩ : syracuseStep 1066231 = 1599347) B1599347
theorem B2245913 : Blo 996598 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B6079819 : Blo 996598 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B2246003 : Blo 996598 2246003 := bstep (se 1 (by rfl) ⟨1684502, by rfl⟩ : syracuseStep 2246003 = 3369005) B3369005
theorem B2246039 : Blo 996598 2246039 := bstep (se 1 (by rfl) ⟨1684529, by rfl⟩ : syracuseStep 2246039 = 3369059) B3369059
theorem B7194035 : Blo 996598 7194035 := bstep (se 1 (by rfl) ⟨5395526, by rfl⟩ : syracuseStep 7194035 = 10791053) B10791053
theorem B2311667 : Blo 996598 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B2246219 : Blo 996598 2246219 := bstep (se 1 (by rfl) ⟨1684664, by rfl⟩ : syracuseStep 2246219 = 3369329) B3369329
theorem B1066603 : Blo 996598 1066603 := bstep (se 1 (by rfl) ⟨799952, by rfl⟩ : syracuseStep 1066603 = 1599905) B1599905
theorem B2246273 : Blo 996598 2246273 := bstep (se 2 (by rfl) ⟨842352, by rfl⟩ : syracuseStep 2246273 = 1684705) B1684705
theorem B3786547 : Blo 996598 3786547 := bstep (se 1 (by rfl) ⟨2839910, by rfl⟩ : syracuseStep 3786547 = 5679821) B5679821
theorem B2246489 : Blo 996598 2246489 := bstep (se 2 (by rfl) ⟨842433, by rfl⟩ : syracuseStep 2246489 = 1684867) B1684867
theorem B2246579 : Blo 996598 2246579 := bstep (se 1 (by rfl) ⟨1684934, by rfl⟩ : syracuseStep 2246579 = 3369869) B3369869
theorem B2246615 : Blo 996598 2246615 := bstep (se 1 (by rfl) ⟨1684961, by rfl⟩ : syracuseStep 2246615 = 3369923) B3369923
theorem B1067051 : Blo 996598 1067051 := bstep (se 1 (by rfl) ⟨800288, by rfl⟩ : syracuseStep 1067051 = 1600577) B1600577
theorem B1263691 : Blo 996598 1263691 := bstep (se 1 (by rfl) ⟨947768, by rfl⟩ : syracuseStep 1263691 = 1895537) B1895537
theorem B2246795 : Blo 996598 2246795 := bstep (se 1 (by rfl) ⟨1685096, by rfl⟩ : syracuseStep 2246795 = 3370193) B3370193
theorem B2246849 : Blo 996598 2246849 := bstep (se 2 (by rfl) ⟨842568, by rfl⟩ : syracuseStep 2246849 = 1685137) B1685137
theorem B3197207 : Blo 996598 3197207 := bstep (se 1 (by rfl) ⟨2397905, by rfl⟩ : syracuseStep 3197207 = 4795811) B4795811
theorem B5065091 : Blo 996598 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B2247065 : Blo 996598 2247065 := bstep (se 2 (by rfl) ⟨842649, by rfl⟩ : syracuseStep 2247065 = 1685299) B1685299
theorem B3197387 : Blo 996598 3197387 := bstep (se 1 (by rfl) ⟨2398040, by rfl⟩ : syracuseStep 3197387 = 4796081) B4796081
theorem B2279897 : Blo 996598 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B2247155 : Blo 996598 2247155 := bstep (se 1 (by rfl) ⟨1685366, by rfl⟩ : syracuseStep 2247155 = 3370733) B3370733
theorem B2247191 : Blo 996598 2247191 := bstep (se 1 (by rfl) ⟨1685393, by rfl⟩ : syracuseStep 2247191 = 3370787) B3370787
theorem B3197515 : Blo 996598 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B2247371 : Blo 996598 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B3197657 : Blo 996598 3197657 := bstep (se 2 (by rfl) ⟨1199121, by rfl⟩ : syracuseStep 3197657 = 2398243) B2398243
theorem B2247425 : Blo 996598 2247425 := bstep (se 2 (by rfl) ⟨842784, by rfl⟩ : syracuseStep 2247425 = 1685569) B1685569
theorem B3197771 : Blo 996598 3197771 := bstep (se 1 (by rfl) ⟨2398328, by rfl⟩ : syracuseStep 3197771 = 4796657) B4796657
theorem B2247641 : Blo 996598 2247641 := bstep (se 2 (by rfl) ⟨842865, by rfl⟩ : syracuseStep 2247641 = 1685731) B1685731
theorem B8539141 : Blo 996598 8539141 := bstep (se 4 (by rfl) ⟨800544, by rfl⟩ : syracuseStep 8539141 = 1601089) B1601089
theorem B3787793 : Blo 996598 3787793 := bstep (se 2 (by rfl) ⟨1420422, by rfl⟩ : syracuseStep 3787793 = 2840845) B2840845
theorem B1264663 : Blo 996598 1264663 := bstep (se 1 (by rfl) ⟨948497, by rfl⟩ : syracuseStep 1264663 = 1896995) B1896995
theorem B2247731 : Blo 996598 2247731 := bstep (se 1 (by rfl) ⟨1685798, by rfl⟩ : syracuseStep 2247731 = 3371597) B3371597
theorem B2247767 : Blo 996598 2247767 := bstep (se 1 (by rfl) ⟨1685825, by rfl⟩ : syracuseStep 2247767 = 3371651) B3371651
theorem B1068247 : Blo 996598 1068247 := bstep (se 1 (by rfl) ⟨801185, by rfl⟩ : syracuseStep 1068247 = 1602371) B1602371
theorem B2247947 : Blo 996598 2247947 := bstep (se 1 (by rfl) ⟨1685960, by rfl⟩ : syracuseStep 2247947 = 3371921) B3371921
theorem B2248001 : Blo 996598 2248001 := bstep (se 2 (by rfl) ⟨843000, by rfl⟩ : syracuseStep 2248001 = 1686001) B1686001
theorem B1068427 : Blo 996598 1068427 := bstep (se 1 (by rfl) ⟨801320, by rfl⟩ : syracuseStep 1068427 = 1602641) B1602641
theorem B4804019 : Blo 996598 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B1920523 : Blo 996598 1920523 := bstep (se 1 (by rfl) ⟨1440392, by rfl⟩ : syracuseStep 1920523 = 2880785) B2880785
theorem B2248217 : Blo 996598 2248217 := bstep (se 2 (by rfl) ⟨843081, by rfl⟩ : syracuseStep 2248217 = 1686163) B1686163
theorem B2248307 : Blo 996598 2248307 := bstep (se 1 (by rfl) ⟨1686230, by rfl⟩ : syracuseStep 2248307 = 3372461) B3372461
theorem B2248343 : Blo 996598 2248343 := bstep (se 1 (by rfl) ⟨1686257, by rfl⟩ : syracuseStep 2248343 = 3372515) B3372515
theorem B3788491 : Blo 996598 3788491 := bstep (se 1 (by rfl) ⟨2841368, by rfl⟩ : syracuseStep 3788491 = 5682737) B5682737
theorem B2248523 : Blo 996598 2248523 := bstep (se 1 (by rfl) ⟨1686392, by rfl⟩ : syracuseStep 2248523 = 3372785) B3372785
theorem B1265483 : Blo 996598 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B2248577 : Blo 996598 2248577 := bstep (se 2 (by rfl) ⟨843216, by rfl⟩ : syracuseStep 2248577 = 1686433) B1686433
theorem B1494923 : Blo 996598 1494923 := bstep (se 1 (by rfl) ⟨1121192, by rfl⟩ : syracuseStep 1494923 = 2242385) B2242385
theorem B1494935 : Blo 996598 1494935 := bstep (se 1 (by rfl) ⟨1121201, by rfl⟩ : syracuseStep 1494935 = 2242403) B2242403
theorem B1495001 : Blo 996598 1495001 := bstep (se 2 (by rfl) ⟨560625, by rfl⟩ : syracuseStep 1495001 = 1121251) B1121251
theorem B3788765 : Blo 996598 3788765 := bstep (se 3 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 3788765 = 1420787) B1420787
theorem B3199027 : Blo 996598 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B1495115 : Blo 996598 1495115 := bstep (se 1 (by rfl) ⟨1121336, by rfl⟩ : syracuseStep 1495115 = 2242673) B2242673
theorem B1495127 : Blo 996598 1495127 := bstep (se 1 (by rfl) ⟨1121345, by rfl⟩ : syracuseStep 1495127 = 2242691) B2242691
theorem B2248793 : Blo 996598 2248793 := bstep (se 2 (by rfl) ⟨843297, by rfl⟩ : syracuseStep 2248793 = 1686595) B1686595
theorem B1495193 : Blo 996598 1495193 := bstep (se 2 (by rfl) ⟨560697, by rfl⟩ : syracuseStep 1495193 = 1121395) B1121395
theorem B2248883 : Blo 996598 2248883 := bstep (se 1 (by rfl) ⟨1686662, by rfl⟩ : syracuseStep 2248883 = 3373325) B3373325
theorem B2248919 : Blo 996598 2248919 := bstep (se 1 (by rfl) ⟨1686689, by rfl⟩ : syracuseStep 2248919 = 3373379) B3373379
theorem B1495307 : Blo 996598 1495307 := bstep (se 1 (by rfl) ⟨1121480, by rfl⟩ : syracuseStep 1495307 = 2242961) B2242961
theorem B1495319 : Blo 996598 1495319 := bstep (se 1 (by rfl) ⟨1121489, by rfl⟩ : syracuseStep 1495319 = 2242979) B2242979
theorem B3199297 : Blo 996598 3199297 := bstep (se 2 (by rfl) ⟨1199736, by rfl⟩ : syracuseStep 3199297 = 2399473) B2399473
theorem B1495385 : Blo 996598 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B2249099 : Blo 996598 2249099 := bstep (se 1 (by rfl) ⟨1686824, by rfl⟩ : syracuseStep 2249099 = 3373649) B3373649
theorem B2249153 : Blo 996598 2249153 := bstep (se 2 (by rfl) ⟨843432, by rfl⟩ : syracuseStep 2249153 = 1686865) B1686865
theorem B1495499 : Blo 996598 1495499 := bstep (se 1 (by rfl) ⟨1121624, by rfl⟩ : syracuseStep 1495499 = 2243249) B2243249
theorem B1495511 : Blo 996598 1495511 := bstep (se 1 (by rfl) ⟨1121633, by rfl⟩ : syracuseStep 1495511 = 2243267) B2243267
theorem B1266187 : Blo 996598 1266187 := bstep (se 1 (by rfl) ⟨949640, by rfl⟩ : syracuseStep 1266187 = 1899281) B1899281
theorem B1495577 : Blo 996598 1495577 := bstep (se 2 (by rfl) ⟨560841, by rfl⟩ : syracuseStep 1495577 = 1121683) B1121683
theorem B1495691 : Blo 996598 1495691 := bstep (se 1 (by rfl) ⟨1121768, by rfl⟩ : syracuseStep 1495691 = 2243537) B2243537
theorem B1495703 : Blo 996598 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B3789463 : Blo 996598 3789463 := bstep (se 1 (by rfl) ⟨2842097, by rfl⟩ : syracuseStep 3789463 = 5684195) B5684195
theorem B2249369 : Blo 996598 2249369 := bstep (se 2 (by rfl) ⟨843513, by rfl⟩ : syracuseStep 2249369 = 1687027) B1687027
theorem B1495769 : Blo 996598 1495769 := bstep (se 2 (by rfl) ⟨560913, by rfl⟩ : syracuseStep 1495769 = 1121827) B1121827
theorem B2249459 : Blo 996598 2249459 := bstep (se 1 (by rfl) ⟨1687094, by rfl⟩ : syracuseStep 2249459 = 3374189) B3374189
theorem B2839319 : Blo 996598 2839319 := bstep (se 1 (by rfl) ⟨2129489, by rfl⟩ : syracuseStep 2839319 = 4258979) B4258979
theorem B2249495 : Blo 996598 2249495 := bstep (se 1 (by rfl) ⟨1687121, by rfl⟩ : syracuseStep 2249495 = 3374243) B3374243
theorem B3363659 : Blo 996598 3363659 := bstep (se 1 (by rfl) ⟨2522744, by rfl⟩ : syracuseStep 3363659 = 5045489) B5045489
theorem B1495883 : Blo 996598 1495883 := bstep (se 1 (by rfl) ⟨1121912, by rfl⟩ : syracuseStep 1495883 = 2243825) B2243825
theorem B1495895 : Blo 996598 1495895 := bstep (se 1 (by rfl) ⟨1121921, by rfl⟩ : syracuseStep 1495895 = 2243843) B2243843
theorem B1495961 : Blo 996598 1495961 := bstep (se 2 (by rfl) ⟨560985, by rfl⟩ : syracuseStep 1495961 = 1121971) B1121971
theorem B7590833 : Blo 996598 7590833 := bstep (se 2 (by rfl) ⟨2846562, by rfl⟩ : syracuseStep 7590833 = 5693125) B5693125
theorem B2053043 : Blo 996598 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B2249675 : Blo 996598 2249675 := bstep (se 1 (by rfl) ⟨1687256, by rfl⟩ : syracuseStep 2249675 = 3374513) B3374513
theorem B2249729 : Blo 996598 2249729 := bstep (se 2 (by rfl) ⟨843648, by rfl⟩ : syracuseStep 2249729 = 1687297) B1687297
theorem B1496075 : Blo 996598 1496075 := bstep (se 1 (by rfl) ⟨1122056, by rfl⟩ : syracuseStep 1496075 = 2244113) B2244113
theorem B1201163 : Blo 996598 1201163 := bstep (se 1 (by rfl) ⟨900872, by rfl⟩ : syracuseStep 1201163 = 1801745) B1801745
theorem B1496087 : Blo 996598 1496087 := bstep (se 1 (by rfl) ⟨1122065, by rfl⟩ : syracuseStep 1496087 = 2244131) B2244131
theorem B3363929 : Blo 996598 3363929 := bstep (se 2 (by rfl) ⟨1261473, by rfl⟩ : syracuseStep 3363929 = 2522947) B2522947
theorem B1496153 : Blo 996598 1496153 := bstep (se 2 (by rfl) ⟨561057, by rfl⟩ : syracuseStep 1496153 = 1122115) B1122115
theorem B1496267 : Blo 996598 1496267 := bstep (se 1 (by rfl) ⟨1122200, by rfl⟩ : syracuseStep 1496267 = 2244401) B2244401
theorem B1496279 : Blo 996598 1496279 := bstep (se 1 (by rfl) ⟨1122209, by rfl⟩ : syracuseStep 1496279 = 2244419) B2244419
theorem B2249945 : Blo 996598 2249945 := bstep (se 2 (by rfl) ⟨843729, by rfl⟩ : syracuseStep 2249945 = 1687459) B1687459
theorem B4052227 : Blo 996598 4052227 := bstep (se 1 (by rfl) ⟨3039170, by rfl⟩ : syracuseStep 4052227 = 6078341) B6078341
theorem B1496345 : Blo 996598 1496345 := bstep (se 2 (by rfl) ⟨561129, by rfl⟩ : syracuseStep 1496345 = 1122259) B1122259
theorem B2250035 : Blo 996598 2250035 := bstep (se 1 (by rfl) ⟨1687526, by rfl⟩ : syracuseStep 2250035 = 3375053) B3375053
theorem B2250071 : Blo 996598 2250071 := bstep (se 1 (by rfl) ⟨1687553, by rfl⟩ : syracuseStep 2250071 = 3375107) B3375107
theorem B1496459 : Blo 996598 1496459 := bstep (se 1 (by rfl) ⟨1122344, by rfl⟩ : syracuseStep 1496459 = 2244689) B2244689
theorem B4052369 : Blo 996598 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B1496471 : Blo 996598 1496471 := bstep (se 1 (by rfl) ⟨1122353, by rfl⟩ : syracuseStep 1496471 = 2244707) B2244707
theorem B7591319 : Blo 996598 7591319 := bstep (se 1 (by rfl) ⟨5693489, by rfl⟩ : syracuseStep 7591319 = 11386979) B11386979
theorem B3790253 : Blo 996598 3790253 := bstep (se 3 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 3790253 = 1421345) B1421345
theorem B1496537 : Blo 996598 1496537 := bstep (se 2 (by rfl) ⟨561201, by rfl⟩ : syracuseStep 1496537 = 1122403) B1122403
theorem B2250251 : Blo 996598 2250251 := bstep (se 1 (by rfl) ⟨1687688, by rfl⟩ : syracuseStep 2250251 = 3375377) B3375377
theorem B5133869 : Blo 996598 5133869 := bstep (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) B1925201
theorem B2250305 : Blo 996598 2250305 := bstep (se 2 (by rfl) ⟨843864, by rfl⟩ : syracuseStep 2250305 = 1687729) B1687729
theorem B1496651 : Blo 996598 1496651 := bstep (se 1 (by rfl) ⟨1122488, by rfl⟩ : syracuseStep 1496651 = 2244977) B2244977
theorem B1496663 : Blo 996598 1496663 := bstep (se 1 (by rfl) ⟨1122497, by rfl⟩ : syracuseStep 1496663 = 2244995) B2244995
theorem B6084197 : Blo 996598 6084197 := bstep (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) B1140787
theorem B1496729 : Blo 996598 1496729 := bstep (se 2 (by rfl) ⟨561273, by rfl⟩ : syracuseStep 1496729 = 1122547) B1122547
theorem B8541875 : Blo 996598 8541875 := bstep (se 1 (by rfl) ⟨6406406, by rfl⟩ : syracuseStep 8541875 = 12812813) B12812813
theorem B1496843 : Blo 996598 1496843 := bstep (se 1 (by rfl) ⟨1122632, by rfl⟩ : syracuseStep 1496843 = 2245265) B2245265
theorem B3364631 : Blo 996598 3364631 := bstep (se 1 (by rfl) ⟨2523473, by rfl⟩ : syracuseStep 3364631 = 5046947) B5046947
theorem B1496855 : Blo 996598 1496855 := bstep (se 1 (by rfl) ⟨1122641, by rfl⟩ : syracuseStep 1496855 = 2245283) B2245283
theorem B2250521 : Blo 996598 2250521 := bstep (se 2 (by rfl) ⟨843945, by rfl⟩ : syracuseStep 2250521 = 1687891) B1687891
theorem B1496921 : Blo 996598 1496921 := bstep (se 2 (by rfl) ⟨561345, by rfl⟩ : syracuseStep 1496921 = 1122691) B1122691
theorem B2250611 : Blo 996598 2250611 := bstep (se 1 (by rfl) ⟨1687958, by rfl⟩ : syracuseStep 2250611 = 3375917) B3375917
theorem B2250647 : Blo 996598 2250647 := bstep (se 1 (by rfl) ⟨1687985, by rfl⟩ : syracuseStep 2250647 = 3375971) B3375971
theorem B1824691 : Blo 996598 1824691 := bstep (se 1 (by rfl) ⟨1368518, by rfl⟩ : syracuseStep 1824691 = 2737037) B2737037
theorem B1497035 : Blo 996598 1497035 := bstep (se 1 (by rfl) ⟨1122776, by rfl⟩ : syracuseStep 1497035 = 2245553) B2245553
theorem B1497047 : Blo 996598 1497047 := bstep (se 1 (by rfl) ⟨1122785, by rfl⟩ : syracuseStep 1497047 = 2245571) B2245571
theorem B1497113 : Blo 996598 1497113 := bstep (se 2 (by rfl) ⟨561417, by rfl⟩ : syracuseStep 1497113 = 1122835) B1122835
theorem B87447605 : Blo 996598 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B17291339 : Blo 996598 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B2250827 : Blo 996598 2250827 := bstep (se 1 (by rfl) ⟨1688120, by rfl⟩ : syracuseStep 2250827 = 3376241) B3376241
theorem B5691485 : Blo 996598 5691485 := bstep (se 3 (by rfl) ⟨1067153, by rfl⟩ : syracuseStep 5691485 = 2134307) B2134307
theorem B2250881 : Blo 996598 2250881 := bstep (se 2 (by rfl) ⟨844080, by rfl⟩ : syracuseStep 2250881 = 1688161) B1688161
theorem B1497227 : Blo 996598 1497227 := bstep (se 1 (by rfl) ⟨1122920, by rfl⟩ : syracuseStep 1497227 = 2245841) B2245841
theorem B1497239 : Blo 996598 1497239 := bstep (se 1 (by rfl) ⟨1122929, by rfl⟩ : syracuseStep 1497239 = 2245859) B2245859
theorem B1824983 : Blo 996598 1824983 := bstep (se 1 (by rfl) ⟨1368737, by rfl⟩ : syracuseStep 1824983 = 2737475) B2737475
theorem B1497305 : Blo 996598 1497305 := bstep (se 2 (by rfl) ⟨561489, by rfl⟩ : syracuseStep 1497305 = 1122979) B1122979
theorem B3201245 : Blo 996598 3201245 := bstep (se 3 (by rfl) ⟨600233, by rfl⟩ : syracuseStep 3201245 = 1200467) B1200467
theorem B3365171 : Blo 996598 3365171 := bstep (se 1 (by rfl) ⟨2523878, by rfl⟩ : syracuseStep 3365171 = 5047757) B5047757
theorem B1497419 : Blo 996598 1497419 := bstep (se 1 (by rfl) ⟨1123064, by rfl⟩ : syracuseStep 1497419 = 2246129) B2246129
theorem B1497431 : Blo 996598 1497431 := bstep (se 1 (by rfl) ⟨1123073, by rfl⟩ : syracuseStep 1497431 = 2246147) B2246147
theorem B2251097 : Blo 996598 2251097 := bstep (se 2 (by rfl) ⟨844161, by rfl⟩ : syracuseStep 2251097 = 1688323) B1688323
theorem B1497497 : Blo 996598 1497497 := bstep (se 2 (by rfl) ⟨561561, by rfl⟩ : syracuseStep 1497497 = 1123123) B1123123
theorem B9099697 : Blo 996598 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B2251187 : Blo 996598 2251187 := bstep (se 1 (by rfl) ⟨1688390, by rfl⟩ : syracuseStep 2251187 = 3376781) B3376781
theorem B2251223 : Blo 996598 2251223 := bstep (se 1 (by rfl) ⟨1688417, by rfl⟩ : syracuseStep 2251223 = 3376835) B3376835
theorem B1825291 : Blo 996598 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B1497611 : Blo 996598 1497611 := bstep (se 1 (by rfl) ⟨1123208, by rfl⟩ : syracuseStep 1497611 = 2246417) B2246417
theorem B1497623 : Blo 996598 1497623 := bstep (se 1 (by rfl) ⟨1123217, by rfl⟩ : syracuseStep 1497623 = 2246435) B2246435
theorem B3365441 : Blo 996598 3365441 := bstep (se 2 (by rfl) ⟨1262040, by rfl⟩ : syracuseStep 3365441 = 2524081) B2524081
theorem B1497689 : Blo 996598 1497689 := bstep (se 2 (by rfl) ⟨561633, by rfl⟩ : syracuseStep 1497689 = 1123267) B1123267
theorem B1497803 : Blo 996598 1497803 := bstep (se 1 (by rfl) ⟨1123352, by rfl⟩ : syracuseStep 1497803 = 2246705) B2246705
theorem B1497815 : Blo 996598 1497815 := bstep (se 1 (by rfl) ⟨1123361, by rfl⟩ : syracuseStep 1497815 = 2246723) B2246723
theorem B4315907 : Blo 996598 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B1497881 : Blo 996598 1497881 := bstep (se 2 (by rfl) ⟨561705, by rfl⟩ : syracuseStep 1497881 = 1123411) B1123411
theorem B3791681 : Blo 996598 3791681 := bstep (se 2 (by rfl) ⟨1421880, by rfl⟩ : syracuseStep 3791681 = 2843761) B2843761
theorem B1497995 : Blo 996598 1497995 := bstep (se 1 (by rfl) ⟨1123496, by rfl⟩ : syracuseStep 1497995 = 2246993) B2246993
theorem B1498007 : Blo 996598 1498007 := bstep (se 1 (by rfl) ⟨1123505, by rfl⟩ : syracuseStep 1498007 = 2247011) B2247011
theorem B30759859 : Blo 996598 30759859 := bstep (se 1 (by rfl) ⟨23069894, by rfl⟩ : syracuseStep 30759859 = 46139789) B46139789
theorem B1498073 : Blo 996598 1498073 := bstep (se 2 (by rfl) ⟨561777, by rfl⟩ : syracuseStep 1498073 = 1123555) B1123555
theorem B1498187 : Blo 996598 1498187 := bstep (se 1 (by rfl) ⟨1123640, by rfl⟩ : syracuseStep 1498187 = 2247281) B2247281
theorem B1498199 : Blo 996598 1498199 := bstep (se 1 (by rfl) ⟨1123649, by rfl⟩ : syracuseStep 1498199 = 2247299) B2247299
theorem B2776153 : Blo 996598 2776153 := bstep (se 2 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 2776153 = 2082115) B2082115
theorem B3365981 : Blo 996598 3365981 := bstep (se 3 (by rfl) ⟨631121, by rfl⟩ : syracuseStep 3365981 = 1262243) B1262243
theorem B1498265 : Blo 996598 1498265 := bstep (se 2 (by rfl) ⟨561849, by rfl⟩ : syracuseStep 1498265 = 1123699) B1123699
theorem B2841779 : Blo 996598 2841779 := bstep (se 1 (by rfl) ⟨2131334, by rfl⟩ : syracuseStep 2841779 = 4262669) B4262669
theorem B2022617 : Blo 996598 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B1498379 : Blo 996598 1498379 := bstep (se 1 (by rfl) ⟨1123784, by rfl⟩ : syracuseStep 1498379 = 2247569) B2247569
theorem B1498391 : Blo 996598 1498391 := bstep (se 1 (by rfl) ⟨1123793, by rfl⟩ : syracuseStep 1498391 = 2247587) B2247587
theorem B1498457 : Blo 996598 1498457 := bstep (se 2 (by rfl) ⟨561921, by rfl⟩ : syracuseStep 1498457 = 1123843) B1123843
theorem B1498571 : Blo 996598 1498571 := bstep (se 1 (by rfl) ⟨1123928, by rfl⟩ : syracuseStep 1498571 = 2247857) B2247857
theorem B1498583 : Blo 996598 1498583 := bstep (se 1 (by rfl) ⟨1123937, by rfl⟩ : syracuseStep 1498583 = 2247875) B2247875
theorem B1498649 : Blo 996598 1498649 := bstep (se 2 (by rfl) ⟨561993, by rfl⟩ : syracuseStep 1498649 = 1123987) B1123987
theorem B8543789 : Blo 996598 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B3595907 : Blo 996598 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B1498763 : Blo 996598 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B1891991 : Blo 996598 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B1498775 : Blo 996598 1498775 := bstep (se 1 (by rfl) ⟨1124081, by rfl⟩ : syracuseStep 1498775 = 2248163) B2248163
theorem B1498841 : Blo 996598 1498841 := bstep (se 2 (by rfl) ⟨562065, by rfl⟩ : syracuseStep 1498841 = 1124131) B1124131
theorem B1498955 : Blo 996598 1498955 := bstep (se 1 (by rfl) ⟨1124216, by rfl⟩ : syracuseStep 1498955 = 2248433) B2248433
theorem B1498967 : Blo 996598 1498967 := bstep (se 1 (by rfl) ⟨1124225, by rfl⟩ : syracuseStep 1498967 = 2248451) B2248451
theorem B1499033 : Blo 996598 1499033 := bstep (se 2 (by rfl) ⟨562137, by rfl⟩ : syracuseStep 1499033 = 1124275) B1124275
theorem B1499147 : Blo 996598 1499147 := bstep (se 1 (by rfl) ⟨1124360, by rfl⟩ : syracuseStep 1499147 = 2248721) B2248721
theorem B1499159 : Blo 996598 1499159 := bstep (se 1 (by rfl) ⟨1124369, by rfl⟩ : syracuseStep 1499159 = 2248739) B2248739
theorem B3596339 : Blo 996598 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B1499225 : Blo 996598 1499225 := bstep (se 2 (by rfl) ⟨562209, by rfl⟩ : syracuseStep 1499225 = 1124419) B1124419
theorem B16408669 : Blo 996598 16408669 := bstep (se 3 (by rfl) ⟨3076625, by rfl⟩ : syracuseStep 16408669 = 6153251) B6153251
theorem B3367115 : Blo 996598 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1499339 : Blo 996598 1499339 := bstep (se 1 (by rfl) ⟨1124504, by rfl⟩ : syracuseStep 1499339 = 2249009) B2249009
theorem B1597655 : Blo 996598 1597655 := bstep (se 1 (by rfl) ⟨1198241, by rfl⟩ : syracuseStep 1597655 = 2396483) B2396483
theorem B1499351 : Blo 996598 1499351 := bstep (se 1 (by rfl) ⟨1124513, by rfl⟩ : syracuseStep 1499351 = 2249027) B2249027
theorem B8544473 : Blo 996598 8544473 := bstep (se 2 (by rfl) ⟨3204177, by rfl⟩ : syracuseStep 8544473 = 6408355) B6408355
theorem B3793169 : Blo 996598 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B1499417 : Blo 996598 1499417 := bstep (se 2 (by rfl) ⟨562281, by rfl⟩ : syracuseStep 1499417 = 1124563) B1124563
theorem B1892659 : Blo 996598 1892659 := bstep (se 1 (by rfl) ⟨1419494, by rfl⟩ : syracuseStep 1892659 = 2838989) B2838989
theorem B1499531 : Blo 996598 1499531 := bstep (se 1 (by rfl) ⟨1124648, by rfl⟩ : syracuseStep 1499531 = 2249297) B2249297
theorem B1499543 : Blo 996598 1499543 := bstep (se 1 (by rfl) ⟨1124657, by rfl⟩ : syracuseStep 1499543 = 2249315) B2249315
theorem B3039691 : Blo 996598 3039691 := bstep (se 1 (by rfl) ⟨2279768, by rfl⟩ : syracuseStep 3039691 = 4559537) B4559537
theorem B3367385 : Blo 996598 3367385 := bstep (se 2 (by rfl) ⟨1262769, by rfl⟩ : syracuseStep 3367385 = 2525539) B2525539
theorem B1499609 : Blo 996598 1499609 := bstep (se 2 (by rfl) ⟨562353, by rfl⟩ : syracuseStep 1499609 = 1124707) B1124707
theorem B1597963 : Blo 996598 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B1499723 : Blo 996598 1499723 := bstep (se 1 (by rfl) ⟨1124792, by rfl⟩ : syracuseStep 1499723 = 2249585) B2249585
theorem B1499735 : Blo 996598 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B5694083 : Blo 996598 5694083 := bstep (se 1 (by rfl) ⟨4270562, by rfl⟩ : syracuseStep 5694083 = 8541125) B8541125
theorem B1499801 : Blo 996598 1499801 := bstep (se 2 (by rfl) ⟨562425, by rfl⟩ : syracuseStep 1499801 = 1124851) B1124851
theorem B1139383 : Blo 996598 1139383 := bstep (se 1 (by rfl) ⟨854537, by rfl⟩ : syracuseStep 1139383 = 1709075) B1709075
theorem B3793625 : Blo 996598 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B1893107 : Blo 996598 1893107 := bstep (se 1 (by rfl) ⟨1419830, by rfl⟩ : syracuseStep 1893107 = 2839661) B2839661
theorem B1598219 : Blo 996598 1598219 := bstep (se 1 (by rfl) ⟨1198664, by rfl⟩ : syracuseStep 1598219 = 2397329) B2397329
theorem B1499915 : Blo 996598 1499915 := bstep (se 1 (by rfl) ⟨1124936, by rfl⟩ : syracuseStep 1499915 = 2249873) B2249873
theorem B1499927 : Blo 996598 1499927 := bstep (se 1 (by rfl) ⟨1124945, by rfl⟩ : syracuseStep 1499927 = 2249891) B2249891
theorem B1893145 : Blo 996598 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B5202733 : Blo 996598 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B1499993 : Blo 996598 1499993 := bstep (se 2 (by rfl) ⟨562497, by rfl⟩ : syracuseStep 1499993 = 1124995) B1124995
theorem B3793837 : Blo 996598 3793837 := bstep (se 3 (by rfl) ⟨711344, by rfl⟩ : syracuseStep 3793837 = 1422689) B1422689
theorem B1500107 : Blo 996598 1500107 := bstep (se 1 (by rfl) ⟨1125080, by rfl⟩ : syracuseStep 1500107 = 2250161) B2250161
theorem B1500119 : Blo 996598 1500119 := bstep (se 1 (by rfl) ⟨1125089, by rfl⟩ : syracuseStep 1500119 = 2250179) B2250179
theorem B1500185 : Blo 996598 1500185 := bstep (se 2 (by rfl) ⟨562569, by rfl⟩ : syracuseStep 1500185 = 1125139) B1125139
theorem B1500299 : Blo 996598 1500299 := bstep (se 1 (by rfl) ⟨1125224, by rfl⟩ : syracuseStep 1500299 = 2250449) B2250449
theorem B3368087 : Blo 996598 3368087 := bstep (se 1 (by rfl) ⟨2526065, by rfl⟩ : syracuseStep 3368087 = 5052131) B5052131
theorem B1500311 : Blo 996598 1500311 := bstep (se 1 (by rfl) ⟨1125233, by rfl⟩ : syracuseStep 1500311 = 2250467) B2250467
theorem B1893593 : Blo 996598 1893593 := bstep (se 2 (by rfl) ⟨710097, by rfl⟩ : syracuseStep 1893593 = 1420195) B1420195
theorem B1500377 : Blo 996598 1500377 := bstep (se 2 (by rfl) ⟨562641, by rfl⟩ : syracuseStep 1500377 = 1125283) B1125283
theorem B3794141 : Blo 996598 3794141 := bstep (se 3 (by rfl) ⟨711401, by rfl⟩ : syracuseStep 3794141 = 1422803) B1422803
theorem B1500491 : Blo 996598 1500491 := bstep (se 1 (by rfl) ⟨1125368, by rfl⟩ : syracuseStep 1500491 = 2250737) B2250737
theorem B1500503 : Blo 996598 1500503 := bstep (se 1 (by rfl) ⟨1125377, by rfl⟩ : syracuseStep 1500503 = 2250755) B2250755
theorem B1500569 : Blo 996598 1500569 := bstep (se 2 (by rfl) ⟨562713, by rfl⟩ : syracuseStep 1500569 = 1125427) B1125427
theorem B1500683 : Blo 996598 1500683 := bstep (se 1 (by rfl) ⟨1125512, by rfl⟩ : syracuseStep 1500683 = 2251025) B2251025
theorem B1500695 : Blo 996598 1500695 := bstep (se 1 (by rfl) ⟨1125521, by rfl⟩ : syracuseStep 1500695 = 2251043) B2251043
theorem B1500761 : Blo 996598 1500761 := bstep (se 2 (by rfl) ⟨562785, by rfl⟩ : syracuseStep 1500761 = 1125571) B1125571
theorem B3368627 : Blo 996598 3368627 := bstep (se 1 (by rfl) ⟨2526470, by rfl⟩ : syracuseStep 3368627 = 5052941) B5052941
theorem B1500875 : Blo 996598 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B1500887 : Blo 996598 1500887 := bstep (se 1 (by rfl) ⟨1125665, by rfl⟩ : syracuseStep 1500887 = 2251331) B2251331
theorem B1599193 : Blo 996598 1599193 := bstep (se 2 (by rfl) ⟨599697, by rfl⟩ : syracuseStep 1599193 = 1199395) B1199395
theorem B2844467 : Blo 996598 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B1894337 : Blo 996598 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B3368897 : Blo 996598 3368897 := bstep (se 2 (by rfl) ⟨1263336, by rfl⟩ : syracuseStep 3368897 = 2526673) B2526673
theorem B2844695 : Blo 996598 2844695 := bstep (se 1 (by rfl) ⟨2133521, by rfl⟩ : syracuseStep 2844695 = 4267043) B4267043
theorem B34171021 : Blo 996598 34171021 := bstep (se 3 (by rfl) ⟨6407066, by rfl⟩ : syracuseStep 34171021 = 12814133) B12814133
theorem B1894603 : Blo 996598 1894603 := bstep (se 1 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 1894603 = 2841905) B2841905
theorem B2845003 : Blo 996598 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B3369437 : Blo 996598 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B2845277 : Blo 996598 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B1895051 : Blo 996598 1895051 := bstep (se 1 (by rfl) ⟨1421288, by rfl⟩ : syracuseStep 1895051 = 2842577) B2842577
theorem B1895233 : Blo 996598 1895233 := bstep (se 2 (by rfl) ⟨710712, by rfl⟩ : syracuseStep 1895233 = 1421425) B1421425
theorem B3042379 : Blo 996598 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B3599453 : Blo 996598 3599453 := bstep (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) B1349795
theorem B1895575 : Blo 996598 1895575 := bstep (se 1 (by rfl) ⟨1421681, by rfl⟩ : syracuseStep 1895575 = 2843363) B2843363
theorem B1797299 : Blo 996598 1797299 := bstep (se 1 (by rfl) ⟨1347974, by rfl⟩ : syracuseStep 1797299 = 2695949) B2695949
theorem B3239219 : Blo 996598 3239219 := bstep (se 1 (by rfl) ⟨2429414, by rfl⟩ : syracuseStep 3239219 = 4858829) B4858829
theorem B8514881 : Blo 996598 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B1895795 : Blo 996598 1895795 := bstep (se 1 (by rfl) ⟨1421846, by rfl⟩ : syracuseStep 1895795 = 2843693) B2843693
theorem B3370571 : Blo 996598 3370571 := bstep (se 1 (by rfl) ⟨2527928, by rfl⟩ : syracuseStep 3370571 = 5055857) B5055857
theorem B1896023 : Blo 996598 1896023 := bstep (se 1 (by rfl) ⟨1422017, by rfl⟩ : syracuseStep 1896023 = 2844035) B2844035
theorem B6844121 : Blo 996598 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B3796739 : Blo 996598 3796739 := bstep (se 1 (by rfl) ⟨2847554, by rfl⟩ : syracuseStep 3796739 = 5695109) B5695109
theorem B3796753 : Blo 996598 3796753 := bstep (se 2 (by rfl) ⟨1423782, by rfl⟩ : syracuseStep 3796753 = 2847565) B2847565
theorem B3370841 : Blo 996598 3370841 := bstep (se 2 (by rfl) ⟨1264065, by rfl⟩ : syracuseStep 3370841 = 2528131) B2528131
theorem B1896281 : Blo 996598 1896281 := bstep (se 2 (by rfl) ⟨711105, by rfl⟩ : syracuseStep 1896281 = 1422211) B1422211
theorem B3797057 : Blo 996598 3797057 := bstep (se 2 (by rfl) ⟨1423896, by rfl⟩ : syracuseStep 3797057 = 2847793) B2847793
theorem B1896691 : Blo 996598 1896691 := bstep (se 1 (by rfl) ⟨1422518, by rfl⟩ : syracuseStep 1896691 = 2845037) B2845037
theorem B6844945 : Blo 996598 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B3371543 : Blo 996598 3371543 := bstep (se 1 (by rfl) ⟨2528657, by rfl⟩ : syracuseStep 3371543 = 5057315) B5057315
theorem B2847383 : Blo 996598 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B1602263 : Blo 996598 1602263 := bstep (se 1 (by rfl) ⟨1201697, by rfl⟩ : syracuseStep 1602263 = 2403395) B2403395
theorem B1897177 : Blo 996598 1897177 := bstep (se 2 (by rfl) ⟨711441, by rfl⟩ : syracuseStep 1897177 = 1422883) B1422883
theorem B3797725 : Blo 996598 3797725 := bstep (se 3 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 3797725 = 1424147) B1424147
theorem B5403485 : Blo 996598 5403485 := bstep (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) B2026307
theorem B4060205 : Blo 996598 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B3372083 : Blo 996598 3372083 := bstep (se 1 (by rfl) ⟨2529062, by rfl⟩ : syracuseStep 3372083 = 5058125) B5058125
theorem B2880715 : Blo 996598 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B1897739 : Blo 996598 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B3372353 : Blo 996598 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B1897921 : Blo 996598 1897921 := bstep (se 2 (by rfl) ⟨711720, by rfl⟩ : syracuseStep 1897921 = 1423441) B1423441
theorem B2848193 : Blo 996598 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B8517271 : Blo 996598 8517271 := bstep (se 1 (by rfl) ⟨6387953, by rfl⟩ : syracuseStep 8517271 = 12775907) B12775907
theorem B3372893 : Blo 996598 3372893 := bstep (se 3 (by rfl) ⟨632417, by rfl⟩ : syracuseStep 3372893 = 1264835) B1264835
theorem B4323289 : Blo 996598 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B3799001 : Blo 996598 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B12777547 : Blo 996598 12777547 := bstep (se 1 (by rfl) ⟨9583160, by rfl⟩ : syracuseStep 12777547 = 19166321) B19166321
theorem B1898635 : Blo 996598 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B1898711 : Blo 996598 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B7207555 : Blo 996598 7207555 := bstep (se 1 (by rfl) ⟨5405666, by rfl⟩ : syracuseStep 7207555 = 10811333) B10811333
theorem B2128601 : Blo 996598 2128601 := bstep (se 2 (by rfl) ⟨798225, by rfl⟩ : syracuseStep 2128601 = 1596451) B1596451
theorem B1899379 : Blo 996598 1899379 := bstep (se 1 (by rfl) ⟨1424534, by rfl⟩ : syracuseStep 1899379 = 2849069) B2849069
theorem B1801111 : Blo 996598 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B3374027 : Blo 996598 3374027 := bstep (se 1 (by rfl) ⟨2530520, by rfl⟩ : syracuseStep 3374027 = 5061041) B5061041
theorem B12155939 : Blo 996598 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B19168325 : Blo 996598 19168325 := bstep (se 4 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 19168325 = 3594061) B3594061
theorem B7568477 : Blo 996598 7568477 := bstep (se 3 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 7568477 = 2838179) B2838179
theorem B4258909 : Blo 996598 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B2129113 : Blo 996598 2129113 := bstep (se 2 (by rfl) ⟨798417, by rfl⟩ : syracuseStep 2129113 = 1596835) B1596835
theorem B3374297 : Blo 996598 3374297 := bstep (se 2 (by rfl) ⟨1265361, by rfl⟩ : syracuseStep 3374297 = 2530723) B2530723
theorem B2129267 : Blo 996598 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B1801739 : Blo 996598 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B7208797 : Blo 996598 7208797 := bstep (se 3 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 7208797 = 2703299) B2703299
theorem B4259729 : Blo 996598 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B3374999 : Blo 996598 3374999 := bstep (se 1 (by rfl) ⟨2531249, by rfl⟩ : syracuseStep 3374999 = 5062499) B5062499
theorem B2523059 : Blo 996598 2523059 := bstep (se 1 (by rfl) ⟨1892294, by rfl⟩ : syracuseStep 2523059 = 3784589) B3784589
theorem B2523251 : Blo 996598 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B2523271 : Blo 996598 2523271 := bstep (se 1 (by rfl) ⟨1892453, by rfl⟩ : syracuseStep 2523271 = 3784907) B3784907
theorem B1540495 : Blo 996598 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B2523545 : Blo 996598 2523545 := bstep (se 2 (by rfl) ⟨946329, by rfl⟩ : syracuseStep 2523545 = 1892659) B1892659
theorem B932774453 : Blo 996598 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B2523707 : Blo 996598 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B4260413 : Blo 996598 4260413 := bstep (se 3 (by rfl) ⟨798827, by rfl⟩ : syracuseStep 4260413 = 1597655) B1597655
theorem B10781363 : Blo 996598 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B2130617 : Blo 996598 2130617 := bstep (se 2 (by rfl) ⟨798981, by rfl⟩ : syracuseStep 2130617 = 1597963) B1597963
theorem B2523919 : Blo 996598 2523919 := bstep (se 1 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 2523919 = 3785879) B3785879
theorem B10257227 : Blo 996598 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B4260755 : Blo 996598 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B3376025 : Blo 996598 3376025 := bstep (se 2 (by rfl) ⟨1266009, by rfl⟩ : syracuseStep 3376025 = 2532019) B2532019
theorem B1541111 : Blo 996598 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B2524193 : Blo 996598 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B1705079 : Blo 996598 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B16188653 : Blo 996598 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B2557271 : Blo 996598 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B2131471 : Blo 996598 2131471 := bstep (se 1 (by rfl) ⟨1598603, by rfl⟩ : syracuseStep 2131471 = 3197207) B3197207
theorem B2885149 : Blo 996598 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B3376727 : Blo 996598 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B2131591 : Blo 996598 2131591 := bstep (se 1 (by rfl) ⟨1598693, by rfl⟩ : syracuseStep 2131591 = 3197387) B3197387
theorem B2131771 : Blo 996598 2131771 := bstep (se 1 (by rfl) ⟨1598828, by rfl⟩ : syracuseStep 2131771 = 3197657) B3197657
theorem B2131847 : Blo 996598 2131847 := bstep (se 1 (by rfl) ⟨1598885, by rfl⟩ : syracuseStep 2131847 = 3197771) B3197771
theorem B2525195 : Blo 996598 2525195 := bstep (se 1 (by rfl) ⟨1893896, by rfl⟩ : syracuseStep 2525195 = 3787793) B3787793
theorem B2132257 : Blo 996598 2132257 := bstep (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) B1599193
theorem B5048729 : Blo 996598 5048729 := bstep (se 2 (by rfl) ⟨1893273, by rfl⟩ : syracuseStep 5048729 = 3786547) B3786547
theorem B19466795 : Blo 996598 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B2525843 : Blo 996598 2525843 := bstep (se 1 (by rfl) ⟨1894382, by rfl⟩ : syracuseStep 2525843 = 3788765) B3788765
theorem B2526137 : Blo 996598 2526137 := bstep (se 2 (by rfl) ⟨947301, by rfl⟩ : syracuseStep 2526137 = 1894603) B1894603
theorem B11373857 : Blo 996598 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B4263283 : Blo 996598 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B4263353 : Blo 996598 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B2526835 : Blo 996598 2526835 := bstep (se 1 (by rfl) ⟨1895126, by rfl⟩ : syracuseStep 2526835 = 3790253) B3790253
theorem B2526977 : Blo 996598 2526977 := bstep (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) B1895233
theorem B7573337 : Blo 996598 7573337 := bstep (se 2 (by rfl) ⟨2840001, by rfl⟩ : syracuseStep 7573337 = 5680003) B5680003
theorem B1216655 : Blo 996598 1216655 := bstep (se 1 (by rfl) ⟨912491, by rfl⟩ : syracuseStep 1216655 = 1824983) B1824983
theorem B2134163 : Blo 996598 2134163 := bstep (se 1 (by rfl) ⟨1600622, by rfl⟩ : syracuseStep 2134163 = 3201245) B3201245
theorem B2527433 : Blo 996598 2527433 := bstep (se 2 (by rfl) ⟨947787, by rfl⟩ : syracuseStep 2527433 = 1895575) B1895575
theorem B2527787 : Blo 996598 2527787 := bstep (se 1 (by rfl) ⟨1895840, by rfl⟩ : syracuseStep 2527787 = 3791681) B3791681
theorem B2560697 : Blo 996598 2560697 := bstep (se 2 (by rfl) ⟨960261, by rfl⟩ : syracuseStep 2560697 = 1920523) B1920523
theorem B7574309 : Blo 996598 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B1348411 : Blo 996598 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B5051321 : Blo 996598 5051321 := bstep (se 2 (by rfl) ⟨1894245, by rfl⟩ : syracuseStep 5051321 = 3788491) B3788491
theorem B2397271 : Blo 996598 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B4265369 : Blo 996598 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B1709513 : Blo 996598 1709513 := bstep (se 2 (by rfl) ⟨641067, by rfl⟩ : syracuseStep 1709513 = 1282135) B1282135
theorem B4855243 : Blo 996598 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B2528779 : Blo 996598 2528779 := bstep (se 1 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 2528779 = 3793169) B3793169
theorem B2528921 : Blo 996598 2528921 := bstep (se 2 (by rfl) ⟨948345, by rfl⟩ : syracuseStep 2528921 = 1896691) B1896691
theorem B16226021 : Blo 996598 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B4265729 : Blo 996598 4265729 := bstep (se 2 (by rfl) ⟨1599648, by rfl⟩ : syracuseStep 4265729 = 3199297) B3199297
theorem B2529083 : Blo 996598 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B11376773 : Blo 996598 11376773 := bstep (se 4 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 11376773 = 2133145) B2133145
theorem B2529427 : Blo 996598 2529427 := bstep (se 1 (by rfl) ⟨1897070, by rfl⟩ : syracuseStep 2529427 = 3794141) B3794141
theorem B5052617 : Blo 996598 5052617 := bstep (se 2 (by rfl) ⟨1894731, by rfl⟩ : syracuseStep 5052617 = 3789463) B3789463
theorem B2529569 : Blo 996598 2529569 := bstep (se 2 (by rfl) ⟨948588, by rfl⟩ : syracuseStep 2529569 = 1897177) B1897177
theorem B16194167 : Blo 996598 16194167 := bstep (se 1 (by rfl) ⟨12145625, by rfl⟩ : syracuseStep 16194167 = 24291251) B24291251
theorem B3840953 : Blo 996598 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B1121287 : Blo 996598 1121287 := bstep (se 1 (by rfl) ⟨840965, by rfl⟩ : syracuseStep 1121287 = 1681931) B1681931
theorem B1121467 : Blo 996598 1121467 := bstep (se 1 (by rfl) ⟨841100, by rfl⟩ : syracuseStep 1121467 = 1682201) B1682201
theorem B2530561 : Blo 996598 2530561 := bstep (se 2 (by rfl) ⟨948960, by rfl⟩ : syracuseStep 2530561 = 1897921) B1897921
theorem B2694487 : Blo 996598 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B11509085 : Blo 996598 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B2399635 : Blo 996598 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B5676587 : Blo 996598 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B6823543 : Blo 996598 6823543 := bstep (se 1 (by rfl) ⟨5117657, by rfl⟩ : syracuseStep 6823543 = 10235315) B10235315
theorem B1121935 : Blo 996598 1121935 := bstep (se 1 (by rfl) ⟨841451, by rfl⟩ : syracuseStep 1121935 = 1682903) B1682903
theorem B4562747 : Blo 996598 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B2531159 : Blo 996598 2531159 := bstep (se 1 (by rfl) ⟨1898369, by rfl⟩ : syracuseStep 2531159 = 3796739) B3796739
theorem B2432921 : Blo 996598 2432921 := bstep (se 2 (by rfl) ⟨912345, by rfl⟩ : syracuseStep 2432921 = 1824691) B1824691
theorem B2531371 : Blo 996598 2531371 := bstep (se 1 (by rfl) ⟨1898528, by rfl⟩ : syracuseStep 2531371 = 3797057) B3797057
theorem B1122439 : Blo 996598 1122439 := bstep (se 1 (by rfl) ⟨841829, by rfl⟩ : syracuseStep 1122439 = 1683659) B1683659
theorem B2531513 : Blo 996598 2531513 := bstep (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) B1898635
theorem B1122619 : Blo 996598 1122619 := bstep (se 1 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 1122619 = 1683929) B1683929
theorem B12132929 : Blo 996598 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B2433721 : Blo 996598 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B1123087 : Blo 996598 1123087 := bstep (se 1 (by rfl) ⟨842315, by rfl⟩ : syracuseStep 1123087 = 1684631) B1684631
theorem B9610073 : Blo 996598 9610073 := bstep (se 2 (by rfl) ⟨3603777, by rfl⟩ : syracuseStep 9610073 = 7207555) B7207555
theorem B5678045 : Blo 996598 5678045 := bstep (se 3 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 5678045 = 2129267) B2129267
theorem B2925629 : Blo 996598 2925629 := bstep (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) B1097111
theorem B2532505 : Blo 996598 2532505 := bstep (se 2 (by rfl) ⟨949689, by rfl⟩ : syracuseStep 2532505 = 1899379) B1899379
theorem B2401481 : Blo 996598 2401481 := bstep (se 2 (by rfl) ⟨900555, by rfl⟩ : syracuseStep 2401481 = 1801111) B1801111
theorem B1123591 : Blo 996598 1123591 := bstep (se 1 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 1123591 = 1685387) B1685387
theorem B2532667 : Blo 996598 2532667 := bstep (se 1 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 2532667 = 3799001) B3799001
theorem B1123771 : Blo 996598 1123771 := bstep (se 1 (by rfl) ⟨842828, by rfl⟩ : syracuseStep 1123771 = 1685657) B1685657
theorem B5678545 : Blo 996598 5678545 := bstep (se 2 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 5678545 = 4258909) B4258909
theorem B10429955 : Blo 996598 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B1419067 : Blo 996598 1419067 := bstep (se 1 (by rfl) ⟨1064300, by rfl⟩ : syracuseStep 1419067 = 2128601) B2128601
theorem B1124239 : Blo 996598 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B8103959 : Blo 996598 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B1124743 : Blo 996598 1124743 := bstep (se 1 (by rfl) ⟨843557, by rfl⟩ : syracuseStep 1124743 = 1687115) B1687115
theorem B9611729 : Blo 996598 9611729 := bstep (se 2 (by rfl) ⟨3604398, by rfl⟩ : syracuseStep 9611729 = 7208797) B7208797
theorem B1124923 : Blo 996598 1124923 := bstep (se 1 (by rfl) ⟨843692, by rfl⟩ : syracuseStep 1124923 = 1687385) B1687385
theorem B1682039 : Blo 996598 1682039 := bstep (se 1 (by rfl) ⟨1261529, by rfl⟩ : syracuseStep 1682039 = 2523059) B2523059
theorem B7187201 : Blo 996598 7187201 := bstep (se 2 (by rfl) ⟨2695200, by rfl⟩ : syracuseStep 7187201 = 5390401) B5390401
theorem B6073103 : Blo 996598 6073103 := bstep (se 1 (by rfl) ⟨4554827, by rfl⟩ : syracuseStep 6073103 = 9109655) B9109655
theorem B4795195 : Blo 996598 4795195 := bstep (se 1 (by rfl) ⟨3596396, by rfl⟩ : syracuseStep 4795195 = 7192793) B7192793
theorem B66497381 : Blo 996598 66497381 := bstep (se 4 (by rfl) ⟨6234129, by rfl⟩ : syracuseStep 66497381 = 12468259) B12468259
theorem B1125391 : Blo 996598 1125391 := bstep (se 1 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 1125391 = 1688087) B1688087
theorem B1682491 : Blo 996598 1682491 := bstep (se 1 (by rfl) ⟨1261868, by rfl⟩ : syracuseStep 1682491 = 2523737) B2523737
theorem B1682633 : Blo 996598 1682633 := bstep (se 2 (by rfl) ⟨630987, by rfl⟩ : syracuseStep 1682633 = 1261975) B1261975
theorem B1420679 : Blo 996598 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B5680529 : Blo 996598 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B7581113 : Blo 996598 7581113 := bstep (se 2 (by rfl) ⟨2842917, by rfl⟩ : syracuseStep 7581113 = 5685835) B5685835
theorem B1519177 : Blo 996598 1519177 := bstep (se 2 (by rfl) ⟨569691, by rfl⟩ : syracuseStep 1519177 = 1139383) B1139383
theorem B4796023 : Blo 996598 4796023 := bstep (se 1 (by rfl) ⟨3597017, by rfl⟩ : syracuseStep 4796023 = 7194035) B7194035
theorem B24293195 : Blo 996598 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B1683335 : Blo 996598 1683335 := bstep (se 1 (by rfl) ⟨1262501, by rfl⟩ : syracuseStep 1683335 = 2525003) B2525003
theorem B5058449 : Blo 996598 5058449 := bstep (se 2 (by rfl) ⟨1896918, by rfl⟩ : syracuseStep 5058449 = 3793837) B3793837
theorem B1519931 : Blo 996598 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B1421641 : Blo 996598 1421641 := bstep (se 2 (by rfl) ⟨533115, by rfl⟩ : syracuseStep 1421641 = 1066231) B1066231
theorem B8106425 : Blo 996598 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B1683983 : Blo 996598 1683983 := bstep (se 1 (by rfl) ⟨1262987, by rfl⟩ : syracuseStep 1683983 = 2525975) B2525975
theorem B1422137 : Blo 996598 1422137 := bstep (se 2 (by rfl) ⟨533301, by rfl⟩ : syracuseStep 1422137 = 1066603) B1066603
theorem B1684523 : Blo 996598 1684523 := bstep (se 1 (by rfl) ⟨1263392, by rfl⟩ : syracuseStep 1684523 = 2526785) B2526785
theorem B8107141 : Blo 996598 8107141 := bstep (se 4 (by rfl) ⟨760044, by rfl⟩ : syracuseStep 8107141 = 1520089) B1520089
theorem B996615 : Blo 996598 996615 := bstep (se 1 (by rfl) ⟨747461, by rfl⟩ : syracuseStep 996615 = 1494923) B1494923
theorem B996623 : Blo 996598 996623 := bstep (se 1 (by rfl) ⟨747467, by rfl⟩ : syracuseStep 996623 = 1494935) B1494935
theorem B996667 : Blo 996598 996667 := bstep (se 1 (by rfl) ⟨747500, by rfl⟩ : syracuseStep 996667 = 1495001) B1495001
theorem B996743 : Blo 996598 996743 := bstep (se 1 (by rfl) ⟨747557, by rfl⟩ : syracuseStep 996743 = 1495115) B1495115
theorem B996751 : Blo 996598 996751 := bstep (se 1 (by rfl) ⟨747563, by rfl⟩ : syracuseStep 996751 = 1495127) B1495127
theorem B1684921 : Blo 996598 1684921 := bstep (se 2 (by rfl) ⟨631845, by rfl⟩ : syracuseStep 1684921 = 1263691) B1263691
theorem B996795 : Blo 996598 996795 := bstep (se 1 (by rfl) ⟨747596, by rfl⟩ : syracuseStep 996795 = 1495193) B1495193
theorem B996871 : Blo 996598 996871 := bstep (se 1 (by rfl) ⟨747653, by rfl⟩ : syracuseStep 996871 = 1495307) B1495307
theorem B996879 : Blo 996598 996879 := bstep (se 1 (by rfl) ⟨747659, by rfl⟩ : syracuseStep 996879 = 1495319) B1495319
theorem B45561361 : Blo 996598 45561361 := bstep (se 2 (by rfl) ⟨17085510, by rfl⟩ : syracuseStep 45561361 = 34171021) B34171021
theorem B996923 : Blo 996598 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B996999 : Blo 996598 996999 := bstep (se 1 (by rfl) ⟨747749, by rfl⟩ : syracuseStep 996999 = 1495499) B1495499
theorem B997007 : Blo 996598 997007 := bstep (se 1 (by rfl) ⟨747755, by rfl⟩ : syracuseStep 997007 = 1495511) B1495511
theorem B997051 : Blo 996598 997051 := bstep (se 1 (by rfl) ⟨747788, by rfl⟩ : syracuseStep 997051 = 1495577) B1495577
theorem B997127 : Blo 996598 997127 := bstep (se 1 (by rfl) ⟨747845, by rfl⟩ : syracuseStep 997127 = 1495691) B1495691
theorem B1423111 : Blo 996598 1423111 := bstep (se 1 (by rfl) ⟨1067333, by rfl⟩ : syracuseStep 1423111 = 2134667) B2134667
theorem B997135 : Blo 996598 997135 := bstep (se 1 (by rfl) ⟨747851, by rfl⟩ : syracuseStep 997135 = 1495703) B1495703
theorem B997179 : Blo 996598 997179 := bstep (se 1 (by rfl) ⟨747884, by rfl⟩ : syracuseStep 997179 = 1495769) B1495769
theorem B2242439 : Blo 996598 2242439 := bstep (se 1 (by rfl) ⟨1681829, by rfl⟩ : syracuseStep 2242439 = 3363659) B3363659
theorem B997255 : Blo 996598 997255 := bstep (se 1 (by rfl) ⟨747941, by rfl⟩ : syracuseStep 997255 = 1495883) B1495883
theorem B997263 : Blo 996598 997263 := bstep (se 1 (by rfl) ⟨747947, by rfl⟩ : syracuseStep 997263 = 1495895) B1495895
theorem B997307 : Blo 996598 997307 := bstep (se 1 (by rfl) ⟨747980, by rfl⟩ : syracuseStep 997307 = 1495961) B1495961
theorem B5060555 : Blo 996598 5060555 := bstep (se 1 (by rfl) ⟨3795416, by rfl⟩ : syracuseStep 5060555 = 7590833) B7590833
theorem B997383 : Blo 996598 997383 := bstep (se 1 (by rfl) ⟨748037, by rfl⟩ : syracuseStep 997383 = 1496075) B1496075
theorem B997391 : Blo 996598 997391 := bstep (se 1 (by rfl) ⟨748043, by rfl⟩ : syracuseStep 997391 = 1496087) B1496087
theorem B2242619 : Blo 996598 2242619 := bstep (se 1 (by rfl) ⟨1681964, by rfl⟩ : syracuseStep 2242619 = 3363929) B3363929
theorem B997435 : Blo 996598 997435 := bstep (se 1 (by rfl) ⟨748076, by rfl⟩ : syracuseStep 997435 = 1496153) B1496153
theorem B1685623 : Blo 996598 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B997511 : Blo 996598 997511 := bstep (se 1 (by rfl) ⟨748133, by rfl⟩ : syracuseStep 997511 = 1496267) B1496267
theorem B2275463 : Blo 996598 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B997519 : Blo 996598 997519 := bstep (se 1 (by rfl) ⟨748139, by rfl⟩ : syracuseStep 997519 = 1496279) B1496279
theorem B2242745 : Blo 996598 2242745 := bstep (se 2 (by rfl) ⟨841029, by rfl⟩ : syracuseStep 2242745 = 1682059) B1682059
theorem B997563 : Blo 996598 997563 := bstep (se 1 (by rfl) ⟨748172, by rfl⟩ : syracuseStep 997563 = 1496345) B1496345
theorem B997639 : Blo 996598 997639 := bstep (se 1 (by rfl) ⟨748229, by rfl⟩ : syracuseStep 997639 = 1496459) B1496459
theorem B997647 : Blo 996598 997647 := bstep (se 1 (by rfl) ⟨748235, by rfl⟩ : syracuseStep 997647 = 1496471) B1496471
theorem B5060879 : Blo 996598 5060879 := bstep (se 1 (by rfl) ⟨3795659, by rfl⟩ : syracuseStep 5060879 = 7591319) B7591319
theorem B997691 : Blo 996598 997691 := bstep (se 1 (by rfl) ⟨748268, by rfl⟩ : syracuseStep 997691 = 1496537) B1496537
theorem B1685819 : Blo 996598 1685819 := bstep (se 1 (by rfl) ⟨1264364, by rfl⟩ : syracuseStep 1685819 = 2528729) B2528729
theorem B3422579 : Blo 996598 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B997767 : Blo 996598 997767 := bstep (se 1 (by rfl) ⟨748325, by rfl⟩ : syracuseStep 997767 = 1496651) B1496651
theorem B997775 : Blo 996598 997775 := bstep (se 1 (by rfl) ⟨748331, by rfl⟩ : syracuseStep 997775 = 1496663) B1496663
theorem B997819 : Blo 996598 997819 := bstep (se 1 (by rfl) ⟨748364, by rfl⟩ : syracuseStep 997819 = 1496729) B1496729
theorem B997895 : Blo 996598 997895 := bstep (se 1 (by rfl) ⟨748421, by rfl⟩ : syracuseStep 997895 = 1496843) B1496843
theorem B2243087 : Blo 996598 2243087 := bstep (se 1 (by rfl) ⟨1682315, by rfl⟩ : syracuseStep 2243087 = 3364631) B3364631
theorem B997903 : Blo 996598 997903 := bstep (se 1 (by rfl) ⟨748427, by rfl⟩ : syracuseStep 997903 = 1496855) B1496855
theorem B2243105 : Blo 996598 2243105 := bstep (se 2 (by rfl) ⟨841164, by rfl⟩ : syracuseStep 2243105 = 1682329) B1682329
theorem B997947 : Blo 996598 997947 := bstep (se 1 (by rfl) ⟨748460, by rfl⟩ : syracuseStep 997947 = 1496921) B1496921
theorem B998023 : Blo 996598 998023 := bstep (se 1 (by rfl) ⟨748517, by rfl⟩ : syracuseStep 998023 = 1497035) B1497035
theorem B998031 : Blo 996598 998031 := bstep (se 1 (by rfl) ⟨748523, by rfl⟩ : syracuseStep 998031 = 1497047) B1497047
theorem B11385521 : Blo 996598 11385521 := bstep (se 2 (by rfl) ⟨4269570, by rfl⟩ : syracuseStep 11385521 = 8539141) B8539141
theorem B998075 : Blo 996598 998075 := bstep (se 1 (by rfl) ⟨748556, by rfl⟩ : syracuseStep 998075 = 1497113) B1497113
theorem B1686217 : Blo 996598 1686217 := bstep (se 2 (by rfl) ⟨632331, by rfl⟩ : syracuseStep 1686217 = 1264663) B1264663
theorem B998151 : Blo 996598 998151 := bstep (se 1 (by rfl) ⟨748613, by rfl⟩ : syracuseStep 998151 = 1497227) B1497227
theorem B998159 : Blo 996598 998159 := bstep (se 1 (by rfl) ⟨748619, by rfl⟩ : syracuseStep 998159 = 1497239) B1497239
theorem B998203 : Blo 996598 998203 := bstep (se 1 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 998203 = 1497305) B1497305
theorem B5389145 : Blo 996598 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B2243447 : Blo 996598 2243447 := bstep (se 1 (by rfl) ⟨1682585, by rfl⟩ : syracuseStep 2243447 = 3365171) B3365171
theorem B998279 : Blo 996598 998279 := bstep (se 1 (by rfl) ⟨748709, by rfl⟩ : syracuseStep 998279 = 1497419) B1497419
theorem B998287 : Blo 996598 998287 := bstep (se 1 (by rfl) ⟨748715, by rfl⟩ : syracuseStep 998287 = 1497431) B1497431
theorem B998331 : Blo 996598 998331 := bstep (se 1 (by rfl) ⟨748748, by rfl⟩ : syracuseStep 998331 = 1497497) B1497497
theorem B998407 : Blo 996598 998407 := bstep (se 1 (by rfl) ⟨748805, by rfl⟩ : syracuseStep 998407 = 1497611) B1497611
theorem B998415 : Blo 996598 998415 := bstep (se 1 (by rfl) ⟨748811, by rfl⟩ : syracuseStep 998415 = 1497623) B1497623
theorem B2243627 : Blo 996598 2243627 := bstep (se 1 (by rfl) ⟨1682720, by rfl⟩ : syracuseStep 2243627 = 3365441) B3365441
theorem B998459 : Blo 996598 998459 := bstep (se 1 (by rfl) ⟨748844, by rfl⟩ : syracuseStep 998459 = 1497689) B1497689
theorem B998535 : Blo 996598 998535 := bstep (se 1 (by rfl) ⟨748901, by rfl⟩ : syracuseStep 998535 = 1497803) B1497803
theorem B998543 : Blo 996598 998543 := bstep (se 1 (by rfl) ⟨748907, by rfl⟩ : syracuseStep 998543 = 1497815) B1497815
theorem B1424569 : Blo 996598 1424569 := bstep (se 2 (by rfl) ⟨534213, by rfl⟩ : syracuseStep 1424569 = 1068427) B1068427
theorem B998587 : Blo 996598 998587 := bstep (se 1 (by rfl) ⟨748940, by rfl⟩ : syracuseStep 998587 = 1497881) B1497881
theorem B998663 : Blo 996598 998663 := bstep (se 1 (by rfl) ⟨748997, by rfl⟩ : syracuseStep 998663 = 1497995) B1497995
theorem B998671 : Blo 996598 998671 := bstep (se 1 (by rfl) ⟨749003, by rfl⟩ : syracuseStep 998671 = 1498007) B1498007
theorem B998715 : Blo 996598 998715 := bstep (se 1 (by rfl) ⟨749036, by rfl⟩ : syracuseStep 998715 = 1498073) B1498073
theorem B998791 : Blo 996598 998791 := bstep (se 1 (by rfl) ⟨749093, by rfl⟩ : syracuseStep 998791 = 1498187) B1498187
theorem B1686919 : Blo 996598 1686919 := bstep (se 1 (by rfl) ⟨1265189, by rfl⟩ : syracuseStep 1686919 = 2530379) B2530379
theorem B998799 : Blo 996598 998799 := bstep (se 1 (by rfl) ⟨749099, by rfl⟩ : syracuseStep 998799 = 1498199) B1498199
theorem B2243987 : Blo 996598 2243987 := bstep (se 1 (by rfl) ⟨1682990, by rfl⟩ : syracuseStep 2243987 = 3365981) B3365981
theorem B998843 : Blo 996598 998843 := bstep (se 1 (by rfl) ⟨749132, by rfl⟩ : syracuseStep 998843 = 1498265) B1498265
theorem B2244041 : Blo 996598 2244041 := bstep (se 2 (by rfl) ⟨841515, by rfl⟩ : syracuseStep 2244041 = 1683031) B1683031
theorem B998919 : Blo 996598 998919 := bstep (se 1 (by rfl) ⟨749189, by rfl⟩ : syracuseStep 998919 = 1498379) B1498379
theorem B998927 : Blo 996598 998927 := bstep (se 1 (by rfl) ⟨749195, by rfl⟩ : syracuseStep 998927 = 1498391) B1498391
theorem B998971 : Blo 996598 998971 := bstep (se 1 (by rfl) ⟨749228, by rfl⟩ : syracuseStep 998971 = 1498457) B1498457
theorem B4210237 : Blo 996598 4210237 := bstep (se 3 (by rfl) ⟨789419, by rfl⟩ : syracuseStep 4210237 = 1578839) B1578839
theorem B999047 : Blo 996598 999047 := bstep (se 1 (by rfl) ⟨749285, by rfl⟩ : syracuseStep 999047 = 1498571) B1498571
theorem B999055 : Blo 996598 999055 := bstep (se 1 (by rfl) ⟨749291, by rfl⟩ : syracuseStep 999055 = 1498583) B1498583
theorem B999099 : Blo 996598 999099 := bstep (se 1 (by rfl) ⟨749324, by rfl⟩ : syracuseStep 999099 = 1498649) B1498649
theorem B5062337 : Blo 996598 5062337 := bstep (se 2 (by rfl) ⟨1898376, by rfl⟩ : syracuseStep 5062337 = 3796753) B3796753
theorem B999175 : Blo 996598 999175 := bstep (se 1 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 999175 = 1498763) B1498763
theorem B1261327 : Blo 996598 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B999183 : Blo 996598 999183 := bstep (se 1 (by rfl) ⟨749387, by rfl⟩ : syracuseStep 999183 = 1498775) B1498775
theorem B999227 : Blo 996598 999227 := bstep (se 1 (by rfl) ⟨749420, by rfl⟩ : syracuseStep 999227 = 1498841) B1498841
theorem B999303 : Blo 996598 999303 := bstep (se 1 (by rfl) ⟨749477, by rfl⟩ : syracuseStep 999303 = 1498955) B1498955
theorem B999311 : Blo 996598 999311 := bstep (se 1 (by rfl) ⟨749483, by rfl⟩ : syracuseStep 999311 = 1498967) B1498967
theorem B999355 : Blo 996598 999355 := bstep (se 1 (by rfl) ⟨749516, by rfl⟩ : syracuseStep 999355 = 1499033) B1499033
theorem B999431 : Blo 996598 999431 := bstep (se 1 (by rfl) ⟨749573, by rfl⟩ : syracuseStep 999431 = 1499147) B1499147
theorem B999439 : Blo 996598 999439 := bstep (se 1 (by rfl) ⟨749579, by rfl⟩ : syracuseStep 999439 = 1499159) B1499159
theorem B1687567 : Blo 996598 1687567 := bstep (se 1 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 1687567 = 2531351) B2531351
theorem B999483 : Blo 996598 999483 := bstep (se 1 (by rfl) ⟨749612, by rfl⟩ : syracuseStep 999483 = 1499225) B1499225
theorem B5685335 : Blo 996598 5685335 := bstep (se 1 (by rfl) ⟨4264001, by rfl⟩ : syracuseStep 5685335 = 8528003) B8528003
theorem B2244743 : Blo 996598 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B999559 : Blo 996598 999559 := bstep (se 1 (by rfl) ⟨749669, by rfl⟩ : syracuseStep 999559 = 1499339) B1499339
theorem B999567 : Blo 996598 999567 := bstep (se 1 (by rfl) ⟨749675, by rfl⟩ : syracuseStep 999567 = 1499351) B1499351
theorem B999611 : Blo 996598 999611 := bstep (se 1 (by rfl) ⟨749708, by rfl⟩ : syracuseStep 999611 = 1499417) B1499417
theorem B999687 : Blo 996598 999687 := bstep (se 1 (by rfl) ⟨749765, by rfl⟩ : syracuseStep 999687 = 1499531) B1499531
theorem B999695 : Blo 996598 999695 := bstep (se 1 (by rfl) ⟨749771, by rfl⟩ : syracuseStep 999695 = 1499543) B1499543
theorem B2244923 : Blo 996598 2244923 := bstep (se 1 (by rfl) ⟨1683692, by rfl⟩ : syracuseStep 2244923 = 3367385) B3367385
theorem B999739 : Blo 996598 999739 := bstep (se 1 (by rfl) ⟨749804, by rfl⟩ : syracuseStep 999739 = 1499609) B1499609
theorem B3785075 : Blo 996598 3785075 := bstep (se 1 (by rfl) ⟨2838806, by rfl⟩ : syracuseStep 3785075 = 5677613) B5677613
theorem B999815 : Blo 996598 999815 := bstep (se 1 (by rfl) ⟨749861, by rfl⟩ : syracuseStep 999815 = 1499723) B1499723
theorem B999823 : Blo 996598 999823 := bstep (se 1 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 999823 = 1499735) B1499735
theorem B2245049 : Blo 996598 2245049 := bstep (se 2 (by rfl) ⟨841893, by rfl⟩ : syracuseStep 2245049 = 1683787) B1683787
theorem B999867 : Blo 996598 999867 := bstep (se 1 (by rfl) ⟨749900, by rfl⟩ : syracuseStep 999867 = 1499801) B1499801
theorem B1262071 : Blo 996598 1262071 := bstep (se 1 (by rfl) ⟨946553, by rfl⟩ : syracuseStep 1262071 = 1893107) B1893107
theorem B1065479 : Blo 996598 1065479 := bstep (se 1 (by rfl) ⟨799109, by rfl⟩ : syracuseStep 1065479 = 1598219) B1598219
theorem B999943 : Blo 996598 999943 := bstep (se 1 (by rfl) ⟨749957, by rfl⟩ : syracuseStep 999943 = 1499915) B1499915
theorem B999951 : Blo 996598 999951 := bstep (se 1 (by rfl) ⟨749963, by rfl⟩ : syracuseStep 999951 = 1499927) B1499927
theorem B1688107 : Blo 996598 1688107 := bstep (se 1 (by rfl) ⟨1266080, by rfl⟩ : syracuseStep 1688107 = 2532161) B2532161
theorem B999995 : Blo 996598 999995 := bstep (se 1 (by rfl) ⟨749996, by rfl⟩ : syracuseStep 999995 = 1499993) B1499993
theorem B1000071 : Blo 996598 1000071 := bstep (se 1 (by rfl) ⟨750053, by rfl⟩ : syracuseStep 1000071 = 1500107) B1500107
theorem B1000079 : Blo 996598 1000079 := bstep (se 1 (by rfl) ⟨750059, by rfl⟩ : syracuseStep 1000079 = 1500119) B1500119
theorem B1688249 : Blo 996598 1688249 := bstep (se 2 (by rfl) ⟨633093, by rfl⟩ : syracuseStep 1688249 = 1266187) B1266187
theorem B1000123 : Blo 996598 1000123 := bstep (se 1 (by rfl) ⟨750092, by rfl⟩ : syracuseStep 1000123 = 1500185) B1500185
theorem B17089217 : Blo 996598 17089217 := bstep (se 2 (by rfl) ⟨6408456, by rfl⟩ : syracuseStep 17089217 = 12816913) B12816913
theorem B9126593 : Blo 996598 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B1000199 : Blo 996598 1000199 := bstep (se 1 (by rfl) ⟨750149, by rfl⟩ : syracuseStep 1000199 = 1500299) B1500299
theorem B2245391 : Blo 996598 2245391 := bstep (se 1 (by rfl) ⟨1684043, by rfl⟩ : syracuseStep 2245391 = 3368087) B3368087
theorem B1000207 : Blo 996598 1000207 := bstep (se 1 (by rfl) ⟨750155, by rfl⟩ : syracuseStep 1000207 = 1500311) B1500311
theorem B5391137 : Blo 996598 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B2245409 : Blo 996598 2245409 := bstep (se 2 (by rfl) ⟨842028, by rfl⟩ : syracuseStep 2245409 = 1684057) B1684057
theorem B1262395 : Blo 996598 1262395 := bstep (se 1 (by rfl) ⟨946796, by rfl⟩ : syracuseStep 1262395 = 1893593) B1893593
theorem B1000251 : Blo 996598 1000251 := bstep (se 1 (by rfl) ⟨750188, by rfl⟩ : syracuseStep 1000251 = 1500377) B1500377
theorem B1000327 : Blo 996598 1000327 := bstep (se 1 (by rfl) ⟨750245, by rfl⟩ : syracuseStep 1000327 = 1500491) B1500491
theorem B1000335 : Blo 996598 1000335 := bstep (se 1 (by rfl) ⟨750251, by rfl⟩ : syracuseStep 1000335 = 1500503) B1500503
theorem B1000379 : Blo 996598 1000379 := bstep (se 1 (by rfl) ⟨750284, by rfl⟩ : syracuseStep 1000379 = 1500569) B1500569
theorem B5063633 : Blo 996598 5063633 := bstep (se 2 (by rfl) ⟨1898862, by rfl⟩ : syracuseStep 5063633 = 3797725) B3797725
theorem B1000455 : Blo 996598 1000455 := bstep (se 1 (by rfl) ⟨750341, by rfl⟩ : syracuseStep 1000455 = 1500683) B1500683
theorem B1000463 : Blo 996598 1000463 := bstep (se 1 (by rfl) ⟨750347, by rfl⟩ : syracuseStep 1000463 = 1500695) B1500695
theorem B1000507 : Blo 996598 1000507 := bstep (se 1 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 1000507 = 1500761) B1500761
theorem B2245751 : Blo 996598 2245751 := bstep (se 1 (by rfl) ⟨1684313, by rfl⟩ : syracuseStep 2245751 = 3368627) B3368627
theorem B1000583 : Blo 996598 1000583 := bstep (se 1 (by rfl) ⟨750437, by rfl⟩ : syracuseStep 1000583 = 1500875) B1500875
theorem B1000591 : Blo 996598 1000591 := bstep (se 1 (by rfl) ⟨750443, by rfl⟩ : syracuseStep 1000591 = 1500887) B1500887
theorem B1262891 : Blo 996598 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B2245931 : Blo 996598 2245931 := bstep (se 1 (by rfl) ⟨1684448, by rfl⟩ : syracuseStep 2245931 = 3368897) B3368897
theorem B2246291 : Blo 996598 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B2246345 : Blo 996598 2246345 := bstep (se 2 (by rfl) ⟨842379, by rfl⟩ : syracuseStep 2246345 = 1684759) B1684759
theorem B1263367 : Blo 996598 1263367 := bstep (se 1 (by rfl) ⟨947525, by rfl⟩ : syracuseStep 1263367 = 1895051) B1895051
theorem B6145807 : Blo 996598 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B1624079 : Blo 996598 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B1198199 : Blo 996598 1198199 := bstep (se 1 (by rfl) ⟨898649, by rfl⟩ : syracuseStep 1198199 = 1797299) B1797299
theorem B11356361 : Blo 996598 11356361 := bstep (se 2 (by rfl) ⟨4258635, by rfl⟩ : syracuseStep 11356361 = 8517271) B8517271
theorem B1263863 : Blo 996598 1263863 := bstep (se 1 (by rfl) ⟨947897, by rfl⟩ : syracuseStep 1263863 = 1895795) B1895795
theorem B5687567 : Blo 996598 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B2247047 : Blo 996598 2247047 := bstep (se 1 (by rfl) ⟨1685285, by rfl⟩ : syracuseStep 2247047 = 3370571) B3370571
theorem B1264015 : Blo 996598 1264015 := bstep (se 1 (by rfl) ⟨948011, by rfl⟩ : syracuseStep 1264015 = 1896023) B1896023
theorem B5687819 : Blo 996598 5687819 := bstep (se 1 (by rfl) ⟨4265864, by rfl⟩ : syracuseStep 5687819 = 8531729) B8531729
theorem B3787307 : Blo 996598 3787307 := bstep (se 1 (by rfl) ⟨2840480, by rfl⟩ : syracuseStep 3787307 = 5680961) B5680961
theorem B2247227 : Blo 996598 2247227 := bstep (se 1 (by rfl) ⟨1685420, by rfl⟩ : syracuseStep 2247227 = 3370841) B3370841
theorem B1264187 : Blo 996598 1264187 := bstep (se 1 (by rfl) ⟨948140, by rfl⟩ : syracuseStep 1264187 = 1896281) B1896281
theorem B2247353 : Blo 996598 2247353 := bstep (se 2 (by rfl) ⟨842757, by rfl⟩ : syracuseStep 2247353 = 1685515) B1685515
theorem B5393297 : Blo 996598 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B2247695 : Blo 996598 2247695 := bstep (se 1 (by rfl) ⟨1685771, by rfl⟩ : syracuseStep 2247695 = 3371543) B3371543
theorem B2247713 : Blo 996598 2247713 := bstep (se 2 (by rfl) ⟨842892, by rfl⟩ : syracuseStep 2247713 = 1685785) B1685785
theorem B6409277 : Blo 996598 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B1068175 : Blo 996598 1068175 := bstep (se 1 (by rfl) ⟨801131, by rfl⟩ : syracuseStep 1068175 = 1602263) B1602263
theorem B2706803 : Blo 996598 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B2248055 : Blo 996598 2248055 := bstep (se 1 (by rfl) ⟨1686041, by rfl⟩ : syracuseStep 2248055 = 3372083) B3372083
theorem B1265159 : Blo 996598 1265159 := bstep (se 1 (by rfl) ⟨948869, by rfl⟩ : syracuseStep 1265159 = 1897739) B1897739
theorem B2248235 : Blo 996598 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B1822267 : Blo 996598 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B5689025 : Blo 996598 5689025 := bstep (se 2 (by rfl) ⟨2133384, by rfl⟩ : syracuseStep 5689025 = 4266769) B4266769
theorem B2248595 : Blo 996598 2248595 := bstep (se 1 (by rfl) ⟨1686446, by rfl⟩ : syracuseStep 2248595 = 3372893) B3372893
theorem B41013145 : Blo 996598 41013145 := bstep (se 2 (by rfl) ⟨15379929, by rfl⟩ : syracuseStep 41013145 = 30759859) B30759859
theorem B1494971 : Blo 996598 1494971 := bstep (se 1 (by rfl) ⟨1121228, by rfl⟩ : syracuseStep 1494971 = 2242457) B2242457
theorem B2248649 : Blo 996598 2248649 := bstep (se 2 (by rfl) ⟨843243, by rfl⟩ : syracuseStep 2248649 = 1686487) B1686487
theorem B1495031 : Blo 996598 1495031 := bstep (se 1 (by rfl) ⟨1121273, by rfl⟩ : syracuseStep 1495031 = 2242547) B2242547
theorem B1495055 : Blo 996598 1495055 := bstep (se 1 (by rfl) ⟨1121291, by rfl⟩ : syracuseStep 1495055 = 2242583) B2242583
theorem B1495097 : Blo 996598 1495097 := bstep (se 2 (by rfl) ⟨560661, by rfl⟩ : syracuseStep 1495097 = 1121323) B1121323
theorem B1495175 : Blo 996598 1495175 := bstep (se 1 (by rfl) ⟨1121381, by rfl⟩ : syracuseStep 1495175 = 2242763) B2242763
theorem B1265807 : Blo 996598 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B1495211 : Blo 996598 1495211 := bstep (se 1 (by rfl) ⟨1121408, by rfl⟩ : syracuseStep 1495211 = 2242817) B2242817
theorem B1495241 : Blo 996598 1495241 := bstep (se 2 (by rfl) ⟨560715, by rfl⟩ : syracuseStep 1495241 = 1121431) B1121431
theorem B2838817 : Blo 996598 2838817 := bstep (se 2 (by rfl) ⟨1064556, by rfl⟩ : syracuseStep 2838817 = 2129113) B2129113
theorem B1495355 : Blo 996598 1495355 := bstep (se 1 (by rfl) ⟨1121516, by rfl⟩ : syracuseStep 1495355 = 2243033) B2243033
theorem B4051315 : Blo 996598 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B1495415 : Blo 996598 1495415 := bstep (se 1 (by rfl) ⟨1121561, by rfl⟩ : syracuseStep 1495415 = 2243123) B2243123
theorem B1495439 : Blo 996598 1495439 := bstep (se 1 (by rfl) ⟨1121579, by rfl⟩ : syracuseStep 1495439 = 2243159) B2243159
theorem B1495481 : Blo 996598 1495481 := bstep (se 2 (by rfl) ⟨560805, by rfl⟩ : syracuseStep 1495481 = 1121611) B1121611
theorem B1495559 : Blo 996598 1495559 := bstep (se 1 (by rfl) ⟨1121669, by rfl⟩ : syracuseStep 1495559 = 2243339) B2243339
theorem B1495595 : Blo 996598 1495595 := bstep (se 1 (by rfl) ⟨1121696, by rfl⟩ : syracuseStep 1495595 = 2243393) B2243393
theorem B1495625 : Blo 996598 1495625 := bstep (se 2 (by rfl) ⟨560859, by rfl⟩ : syracuseStep 1495625 = 1121719) B1121719
theorem B2249351 : Blo 996598 2249351 := bstep (se 1 (by rfl) ⟨1687013, by rfl⟩ : syracuseStep 2249351 = 3374027) B3374027
theorem B1495739 : Blo 996598 1495739 := bstep (se 1 (by rfl) ⟨1121804, by rfl⟩ : syracuseStep 1495739 = 2243609) B2243609
theorem B1495799 : Blo 996598 1495799 := bstep (se 1 (by rfl) ⟨1121849, by rfl⟩ : syracuseStep 1495799 = 2243699) B2243699
theorem B1495823 : Blo 996598 1495823 := bstep (se 1 (by rfl) ⟨1121867, by rfl⟩ : syracuseStep 1495823 = 2243735) B2243735
theorem B1495865 : Blo 996598 1495865 := bstep (se 2 (by rfl) ⟨560949, by rfl⟩ : syracuseStep 1495865 = 1121899) B1121899
theorem B2249531 : Blo 996598 2249531 := bstep (se 1 (by rfl) ⟨1687148, by rfl⟩ : syracuseStep 2249531 = 3374297) B3374297
theorem B1495943 : Blo 996598 1495943 := bstep (se 1 (by rfl) ⟨1121957, by rfl⟩ : syracuseStep 1495943 = 2243915) B2243915
theorem B1495979 : Blo 996598 1495979 := bstep (se 1 (by rfl) ⟨1121984, by rfl⟩ : syracuseStep 1495979 = 2243969) B2243969
theorem B2249657 : Blo 996598 2249657 := bstep (se 2 (by rfl) ⟨843621, by rfl⟩ : syracuseStep 2249657 = 1687243) B1687243
theorem B1496009 : Blo 996598 1496009 := bstep (se 2 (by rfl) ⟨561003, by rfl⟩ : syracuseStep 1496009 = 1122007) B1122007
theorem B1201159 : Blo 996598 1201159 := bstep (se 1 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 1201159 = 1801739) B1801739
theorem B11359277 : Blo 996598 11359277 := bstep (se 3 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 11359277 = 4259729) B4259729
theorem B1496123 : Blo 996598 1496123 := bstep (se 1 (by rfl) ⟨1122092, by rfl⟩ : syracuseStep 1496123 = 2244185) B2244185
theorem B1496183 : Blo 996598 1496183 := bstep (se 1 (by rfl) ⟨1122137, by rfl⟩ : syracuseStep 1496183 = 2244275) B2244275
theorem B1496207 : Blo 996598 1496207 := bstep (se 1 (by rfl) ⟨1122155, by rfl⟩ : syracuseStep 1496207 = 2244311) B2244311
theorem B1496249 : Blo 996598 1496249 := bstep (se 2 (by rfl) ⟨561093, by rfl⟩ : syracuseStep 1496249 = 1122187) B1122187
theorem B1496327 : Blo 996598 1496327 := bstep (se 1 (by rfl) ⟨1122245, by rfl⟩ : syracuseStep 1496327 = 2244491) B2244491
theorem B2249999 : Blo 996598 2249999 := bstep (se 1 (by rfl) ⟨1687499, by rfl⟩ : syracuseStep 2249999 = 3374999) B3374999
theorem B2250017 : Blo 996598 2250017 := bstep (se 2 (by rfl) ⟨843756, by rfl⟩ : syracuseStep 2250017 = 1687513) B1687513
theorem B1496363 : Blo 996598 1496363 := bstep (se 1 (by rfl) ⟨1122272, by rfl⟩ : syracuseStep 1496363 = 2244545) B2244545
theorem B1496393 : Blo 996598 1496393 := bstep (se 2 (by rfl) ⟨561147, by rfl⟩ : syracuseStep 1496393 = 1122295) B1122295
theorem B4871609 : Blo 996598 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B1496507 : Blo 996598 1496507 := bstep (se 1 (by rfl) ⟨1122380, by rfl⟩ : syracuseStep 1496507 = 2244761) B2244761
theorem B21878225 : Blo 996598 21878225 := bstep (se 2 (by rfl) ⟨8204334, by rfl⟩ : syracuseStep 21878225 = 16408669) B16408669
theorem B9590237 : Blo 996598 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B1496567 : Blo 996598 1496567 := bstep (se 1 (by rfl) ⟨1122425, by rfl⟩ : syracuseStep 1496567 = 2244851) B2244851
theorem B5395979 : Blo 996598 5395979 := bstep (se 1 (by rfl) ⟨4046984, by rfl⟩ : syracuseStep 5395979 = 8093969) B8093969
theorem B1496591 : Blo 996598 1496591 := bstep (se 1 (by rfl) ⟨1122443, by rfl⟩ : syracuseStep 1496591 = 2244887) B2244887
theorem B2840093 : Blo 996598 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B1496633 : Blo 996598 1496633 := bstep (se 2 (by rfl) ⟨561237, by rfl⟩ : syracuseStep 1496633 = 1122475) B1122475
theorem B2250359 : Blo 996598 2250359 := bstep (se 1 (by rfl) ⟨1687769, by rfl⟩ : syracuseStep 2250359 = 3375539) B3375539
theorem B1496711 : Blo 996598 1496711 := bstep (se 1 (by rfl) ⟨1122533, by rfl⟩ : syracuseStep 1496711 = 2245067) B2245067
theorem B1496747 : Blo 996598 1496747 := bstep (se 1 (by rfl) ⟨1122560, by rfl⟩ : syracuseStep 1496747 = 2245121) B2245121
theorem B1496777 : Blo 996598 1496777 := bstep (se 2 (by rfl) ⟨561291, by rfl⟩ : syracuseStep 1496777 = 1122583) B1122583
theorem B2840321 : Blo 996598 2840321 := bstep (se 2 (by rfl) ⟨1065120, by rfl⟩ : syracuseStep 2840321 = 2130241) B2130241
theorem B2250539 : Blo 996598 2250539 := bstep (se 1 (by rfl) ⟨1687904, by rfl⟩ : syracuseStep 2250539 = 3375809) B3375809
theorem B1496891 : Blo 996598 1496891 := bstep (se 1 (by rfl) ⟨1122668, by rfl⟩ : syracuseStep 1496891 = 2245337) B2245337
theorem B1496951 : Blo 996598 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B1824631 : Blo 996598 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B1496975 : Blo 996598 1496975 := bstep (se 1 (by rfl) ⟨1122731, by rfl⟩ : syracuseStep 1496975 = 2245463) B2245463
theorem B3790739 : Blo 996598 3790739 := bstep (se 1 (by rfl) ⟨2843054, by rfl⟩ : syracuseStep 3790739 = 5686109) B5686109
theorem B3364793 : Blo 996598 3364793 := bstep (se 2 (by rfl) ⟨1261797, by rfl⟩ : syracuseStep 3364793 = 2523595) B2523595
theorem B1497017 : Blo 996598 1497017 := bstep (se 2 (by rfl) ⟨561381, by rfl⟩ : syracuseStep 1497017 = 1122763) B1122763
theorem B4052921 : Blo 996598 4052921 := bstep (se 2 (by rfl) ⟨1519845, by rfl⟩ : syracuseStep 4052921 = 3039691) B3039691
theorem B1497095 : Blo 996598 1497095 := bstep (se 1 (by rfl) ⟨1122821, by rfl⟩ : syracuseStep 1497095 = 2245643) B2245643
theorem B1497131 : Blo 996598 1497131 := bstep (se 1 (by rfl) ⟨1122848, by rfl⟩ : syracuseStep 1497131 = 2245697) B2245697
theorem B1497161 : Blo 996598 1497161 := bstep (se 2 (by rfl) ⟨561435, by rfl⟩ : syracuseStep 1497161 = 1122871) B1122871
theorem B2840663 : Blo 996598 2840663 := bstep (se 1 (by rfl) ⟨2130497, by rfl⟩ : syracuseStep 2840663 = 4260995) B4260995
theorem B3037331 : Blo 996598 3037331 := bstep (se 1 (by rfl) ⟨2277998, by rfl⟩ : syracuseStep 3037331 = 4555997) B4555997
theorem B2250899 : Blo 996598 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B1497275 : Blo 996598 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B5134529 : Blo 996598 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B2840777 : Blo 996598 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B2250953 : Blo 996598 2250953 := bstep (se 2 (by rfl) ⟨844107, by rfl⟩ : syracuseStep 2250953 = 1688215) B1688215
theorem B1497335 : Blo 996598 1497335 := bstep (se 1 (by rfl) ⟨1123001, by rfl⟩ : syracuseStep 1497335 = 2246003) B2246003
theorem B1497359 : Blo 996598 1497359 := bstep (se 1 (by rfl) ⟨1123019, by rfl⟩ : syracuseStep 1497359 = 2246039) B2246039
theorem B1497401 : Blo 996598 1497401 := bstep (se 2 (by rfl) ⟨561525, by rfl⟩ : syracuseStep 1497401 = 1123051) B1123051
theorem B1497479 : Blo 996598 1497479 := bstep (se 1 (by rfl) ⟨1123109, by rfl⟩ : syracuseStep 1497479 = 2246219) B2246219
theorem B6936977 : Blo 996598 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B1497515 : Blo 996598 1497515 := bstep (se 1 (by rfl) ⟨1123136, by rfl⟩ : syracuseStep 1497515 = 2246273) B2246273
theorem B1497545 : Blo 996598 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B3365387 : Blo 996598 3365387 := bstep (se 1 (by rfl) ⟨2524040, by rfl⟩ : syracuseStep 3365387 = 5048081) B5048081
theorem B1497659 : Blo 996598 1497659 := bstep (se 1 (by rfl) ⟨1123244, by rfl⟩ : syracuseStep 1497659 = 2246489) B2246489
theorem B3365495 : Blo 996598 3365495 := bstep (se 1 (by rfl) ⟨2524121, by rfl⟩ : syracuseStep 3365495 = 5048243) B5048243
theorem B1497719 : Blo 996598 1497719 := bstep (se 1 (by rfl) ⟨1123289, by rfl⟩ : syracuseStep 1497719 = 2246579) B2246579
theorem B1497743 : Blo 996598 1497743 := bstep (se 1 (by rfl) ⟨1123307, by rfl⟩ : syracuseStep 1497743 = 2246615) B2246615
theorem B1497785 : Blo 996598 1497785 := bstep (se 2 (by rfl) ⟨561669, by rfl⟩ : syracuseStep 1497785 = 1123339) B1123339
theorem B1497863 : Blo 996598 1497863 := bstep (se 1 (by rfl) ⟨1123397, by rfl⟩ : syracuseStep 1497863 = 2246795) B2246795
theorem B5692193 : Blo 996598 5692193 := bstep (se 2 (by rfl) ⟨2134572, by rfl⟩ : syracuseStep 5692193 = 4269145) B4269145
theorem B1497899 : Blo 996598 1497899 := bstep (se 1 (by rfl) ⟨1123424, by rfl⟩ : syracuseStep 1497899 = 2246849) B2246849
theorem B1497929 : Blo 996598 1497929 := bstep (se 2 (by rfl) ⟨561723, by rfl⟩ : syracuseStep 1497929 = 1123447) B1123447
theorem B1498043 : Blo 996598 1498043 := bstep (se 1 (by rfl) ⟨1123532, by rfl⟩ : syracuseStep 1498043 = 2247065) B2247065
theorem B1498103 : Blo 996598 1498103 := bstep (se 1 (by rfl) ⟨1123577, by rfl⟩ : syracuseStep 1498103 = 2247155) B2247155
theorem B1498127 : Blo 996598 1498127 := bstep (se 1 (by rfl) ⟨1123595, by rfl⟩ : syracuseStep 1498127 = 2247191) B2247191
theorem B1498169 : Blo 996598 1498169 := bstep (se 2 (by rfl) ⟨561813, by rfl⟩ : syracuseStep 1498169 = 1123627) B1123627
theorem B17062973 : Blo 996598 17062973 := bstep (se 3 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 17062973 = 6398615) B6398615
theorem B5397623 : Blo 996598 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B1498247 : Blo 996598 1498247 := bstep (se 1 (by rfl) ⟨1123685, by rfl⟩ : syracuseStep 1498247 = 2247371) B2247371
theorem B1498283 : Blo 996598 1498283 := bstep (se 1 (by rfl) ⟨1123712, by rfl⟩ : syracuseStep 1498283 = 2247425) B2247425
theorem B3366089 : Blo 996598 3366089 := bstep (se 2 (by rfl) ⟨1262283, by rfl⟩ : syracuseStep 3366089 = 2524567) B2524567
theorem B1498313 : Blo 996598 1498313 := bstep (se 2 (by rfl) ⟨561867, by rfl⟩ : syracuseStep 1498313 = 1123735) B1123735
theorem B1498427 : Blo 996598 1498427 := bstep (se 1 (by rfl) ⟨1123820, by rfl⟩ : syracuseStep 1498427 = 2247641) B2247641
theorem B1498487 : Blo 996598 1498487 := bstep (se 1 (by rfl) ⟨1123865, by rfl⟩ : syracuseStep 1498487 = 2247731) B2247731
theorem B1498511 : Blo 996598 1498511 := bstep (se 1 (by rfl) ⟨1123883, by rfl⟩ : syracuseStep 1498511 = 2247767) B2247767
theorem B4873619 : Blo 996598 4873619 := bstep (se 1 (by rfl) ⟨3655214, by rfl⟩ : syracuseStep 4873619 = 7310429) B7310429
theorem B1498553 : Blo 996598 1498553 := bstep (se 2 (by rfl) ⟨561957, by rfl⟩ : syracuseStep 1498553 = 1123915) B1123915
theorem B1498631 : Blo 996598 1498631 := bstep (se 1 (by rfl) ⟨1123973, by rfl⟩ : syracuseStep 1498631 = 2247947) B2247947
theorem B1498667 : Blo 996598 1498667 := bstep (se 1 (by rfl) ⟨1124000, by rfl⟩ : syracuseStep 1498667 = 2248001) B2248001
theorem B1498697 : Blo 996598 1498697 := bstep (se 2 (by rfl) ⟨562011, by rfl⟩ : syracuseStep 1498697 = 1124023) B1124023
theorem B3202679 : Blo 996598 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1498811 : Blo 996598 1498811 := bstep (se 1 (by rfl) ⟨1124108, by rfl⟩ : syracuseStep 1498811 = 2248217) B2248217
theorem B1498871 : Blo 996598 1498871 := bstep (se 1 (by rfl) ⟨1124153, by rfl⟩ : syracuseStep 1498871 = 2248307) B2248307
theorem B1498895 : Blo 996598 1498895 := bstep (se 1 (by rfl) ⟨1124171, by rfl⟩ : syracuseStep 1498895 = 2248343) B2248343
theorem B1498937 : Blo 996598 1498937 := bstep (se 2 (by rfl) ⟨562101, by rfl⟩ : syracuseStep 1498937 = 1124203) B1124203
theorem B11099993 : Blo 996598 11099993 := bstep (se 2 (by rfl) ⟨4162497, by rfl⟩ : syracuseStep 11099993 = 8324995) B8324995
theorem B3366791 : Blo 996598 3366791 := bstep (se 1 (by rfl) ⟨2525093, by rfl⟩ : syracuseStep 3366791 = 5050187) B5050187
theorem B1499015 : Blo 996598 1499015 := bstep (se 1 (by rfl) ⟨1124261, by rfl⟩ : syracuseStep 1499015 = 2248523) B2248523
theorem B1499051 : Blo 996598 1499051 := bstep (se 1 (by rfl) ⟨1124288, by rfl⟩ : syracuseStep 1499051 = 2248577) B2248577
theorem B2842553 : Blo 996598 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B1499081 : Blo 996598 1499081 := bstep (se 2 (by rfl) ⟨562155, by rfl⟩ : syracuseStep 1499081 = 1124311) B1124311
theorem B3203101 : Blo 996598 3203101 := bstep (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) B1201163
theorem B1499195 : Blo 996598 1499195 := bstep (se 1 (by rfl) ⟨1124396, by rfl⟩ : syracuseStep 1499195 = 2248793) B2248793
theorem B1499255 : Blo 996598 1499255 := bstep (se 1 (by rfl) ⟨1124441, by rfl⟩ : syracuseStep 1499255 = 2248883) B2248883
theorem B1499279 : Blo 996598 1499279 := bstep (se 1 (by rfl) ⟨1124459, by rfl⟩ : syracuseStep 1499279 = 2248919) B2248919
theorem B1499321 : Blo 996598 1499321 := bstep (se 2 (by rfl) ⟨562245, by rfl⟩ : syracuseStep 1499321 = 1124491) B1124491
theorem B3367169 : Blo 996598 3367169 := bstep (se 2 (by rfl) ⟨1262688, by rfl⟩ : syracuseStep 3367169 = 2525377) B2525377
theorem B1499399 : Blo 996598 1499399 := bstep (se 1 (by rfl) ⟨1124549, by rfl⟩ : syracuseStep 1499399 = 2249099) B2249099
theorem B1499435 : Blo 996598 1499435 := bstep (se 1 (by rfl) ⟨1124576, by rfl⟩ : syracuseStep 1499435 = 2249153) B2249153
theorem B1499465 : Blo 996598 1499465 := bstep (se 2 (by rfl) ⟨562299, by rfl⟩ : syracuseStep 1499465 = 1124599) B1124599
theorem B3793337 : Blo 996598 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B1499579 : Blo 996598 1499579 := bstep (se 1 (by rfl) ⟨1124684, by rfl⟩ : syracuseStep 1499579 = 2249369) B2249369
theorem B1499639 : Blo 996598 1499639 := bstep (se 1 (by rfl) ⟨1124729, by rfl⟩ : syracuseStep 1499639 = 2249459) B2249459
theorem B1892879 : Blo 996598 1892879 := bstep (se 1 (by rfl) ⟨1419659, by rfl⟩ : syracuseStep 1892879 = 2839319) B2839319
theorem B1499663 : Blo 996598 1499663 := bstep (se 1 (by rfl) ⟨1124747, by rfl⟩ : syracuseStep 1499663 = 2249495) B2249495
theorem B1499705 : Blo 996598 1499705 := bstep (se 2 (by rfl) ⟨562389, by rfl⟩ : syracuseStep 1499705 = 1124779) B1124779
theorem B1368695 : Blo 996598 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1499783 : Blo 996598 1499783 := bstep (se 1 (by rfl) ⟨1124837, by rfl⟩ : syracuseStep 1499783 = 2249675) B2249675
theorem B1499819 : Blo 996598 1499819 := bstep (se 1 (by rfl) ⟨1124864, by rfl⟩ : syracuseStep 1499819 = 2249729) B2249729
theorem B1499849 : Blo 996598 1499849 := bstep (se 2 (by rfl) ⟨562443, by rfl⟩ : syracuseStep 1499849 = 1124887) B1124887
theorem B1499963 : Blo 996598 1499963 := bstep (se 1 (by rfl) ⟨1124972, by rfl⟩ : syracuseStep 1499963 = 2249945) B2249945
theorem B1500023 : Blo 996598 1500023 := bstep (se 1 (by rfl) ⟨1125017, by rfl⟩ : syracuseStep 1500023 = 2250035) B2250035
theorem B1500047 : Blo 996598 1500047 := bstep (se 1 (by rfl) ⟨1125035, by rfl⟩ : syracuseStep 1500047 = 2250071) B2250071
theorem B2843545 : Blo 996598 2843545 := bstep (se 2 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 2843545 = 2132659) B2132659
theorem B1500089 : Blo 996598 1500089 := bstep (se 2 (by rfl) ⟨562533, by rfl⟩ : syracuseStep 1500089 = 1125067) B1125067
theorem B1500167 : Blo 996598 1500167 := bstep (se 1 (by rfl) ⟨1125125, by rfl⟩ : syracuseStep 1500167 = 2250251) B2250251
theorem B3367979 : Blo 996598 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B10806317 : Blo 996598 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B1500203 : Blo 996598 1500203 := bstep (se 1 (by rfl) ⟨1125152, by rfl⟩ : syracuseStep 1500203 = 2250305) B2250305
theorem B4056131 : Blo 996598 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B1500233 : Blo 996598 1500233 := bstep (se 2 (by rfl) ⟨562587, by rfl⟩ : syracuseStep 1500233 = 1125175) B1125175
theorem B5694583 : Blo 996598 5694583 := bstep (se 1 (by rfl) ⟨4270937, by rfl⟩ : syracuseStep 5694583 = 8541875) B8541875
theorem B1500347 : Blo 996598 1500347 := bstep (se 1 (by rfl) ⟨1125260, by rfl⟩ : syracuseStep 1500347 = 2250521) B2250521
theorem B1500407 : Blo 996598 1500407 := bstep (se 1 (by rfl) ⟨1125305, by rfl⟩ : syracuseStep 1500407 = 2250611) B2250611
theorem B1500431 : Blo 996598 1500431 := bstep (se 1 (by rfl) ⟨1125323, by rfl⟩ : syracuseStep 1500431 = 2250647) B2250647
theorem B1500473 : Blo 996598 1500473 := bstep (se 2 (by rfl) ⟨562677, by rfl⟩ : syracuseStep 1500473 = 1125355) B1125355
theorem B11527559 : Blo 996598 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B1500551 : Blo 996598 1500551 := bstep (se 1 (by rfl) ⟨1125413, by rfl⟩ : syracuseStep 1500551 = 2250827) B2250827
theorem B3794323 : Blo 996598 3794323 := bstep (se 1 (by rfl) ⟨2845742, by rfl⟩ : syracuseStep 3794323 = 5691485) B5691485
theorem B1500587 : Blo 996598 1500587 := bstep (se 1 (by rfl) ⟨1125440, by rfl⟩ : syracuseStep 1500587 = 2250881) B2250881
theorem B1500617 : Blo 996598 1500617 := bstep (se 2 (by rfl) ⟨562731, by rfl⟩ : syracuseStep 1500617 = 1125463) B1125463
theorem B1500731 : Blo 996598 1500731 := bstep (se 1 (by rfl) ⟨1125548, by rfl⟩ : syracuseStep 1500731 = 2251097) B2251097
theorem B10249847 : Blo 996598 10249847 := bstep (se 1 (by rfl) ⟨7687385, by rfl⟩ : syracuseStep 10249847 = 15374771) B15374771
theorem B1500791 : Blo 996598 1500791 := bstep (se 1 (by rfl) ⟨1125593, by rfl⟩ : syracuseStep 1500791 = 2251187) B2251187
theorem B1500815 : Blo 996598 1500815 := bstep (se 1 (by rfl) ⟨1125611, by rfl⟩ : syracuseStep 1500815 = 2251223) B2251223
theorem B1500857 : Blo 996598 1500857 := bstep (se 2 (by rfl) ⟨562821, by rfl⟩ : syracuseStep 1500857 = 1125643) B1125643
theorem B5400371 : Blo 996598 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B3598289 : Blo 996598 3598289 := bstep (se 2 (by rfl) ⟨1349358, by rfl⟩ : syracuseStep 3598289 = 2698717) B2698717
theorem B1894519 : Blo 996598 1894519 := bstep (se 1 (by rfl) ⟨1420889, by rfl⟩ : syracuseStep 1894519 = 2841779) B2841779
theorem B3369275 : Blo 996598 3369275 := bstep (se 1 (by rfl) ⟨2526956, by rfl⟩ : syracuseStep 3369275 = 5053913) B5053913
theorem B5695859 : Blo 996598 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B2845469 : Blo 996598 2845469 := bstep (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) B1067051
theorem B3369761 : Blo 996598 3369761 := bstep (se 2 (by rfl) ⟨1263660, by rfl⟩ : syracuseStep 3369761 = 2527321) B2527321
theorem B5696315 : Blo 996598 5696315 := bstep (se 1 (by rfl) ⟨4272236, by rfl⟩ : syracuseStep 5696315 = 8544473) B8544473
theorem B8219659 : Blo 996598 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B3796055 : Blo 996598 3796055 := bstep (se 1 (by rfl) ⟨2847041, by rfl⟩ : syracuseStep 3796055 = 5694083) B5694083
theorem B3599597 : Blo 996598 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B3370355 : Blo 996598 3370355 := bstep (se 1 (by rfl) ⟨2527766, by rfl⟩ : syracuseStep 3370355 = 5055533) B5055533
theorem B2846153 : Blo 996598 2846153 := bstep (se 2 (by rfl) ⟨1067307, by rfl⟩ : syracuseStep 2846153 = 2134615) B2134615
theorem B3796541 : Blo 996598 3796541 := bstep (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) B1423703
theorem B1797817 : Blo 996598 1797817 := bstep (se 2 (by rfl) ⟨674181, by rfl⟩ : syracuseStep 1797817 = 1348363) B1348363
theorem B5697317 : Blo 996598 5697317 := bstep (se 4 (by rfl) ⟨534123, by rfl⟩ : syracuseStep 5697317 = 1068247) B1068247
theorem B1896311 : Blo 996598 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B6385675 : Blo 996598 6385675 := bstep (se 1 (by rfl) ⟨4789256, by rfl⟩ : syracuseStep 6385675 = 9578513) B9578513
theorem B1896463 : Blo 996598 1896463 := bstep (se 1 (by rfl) ⟨1422347, by rfl⟩ : syracuseStep 1896463 = 2844695) B2844695
theorem B2846735 : Blo 996598 2846735 := bstep (se 1 (by rfl) ⟨2135051, by rfl⟩ : syracuseStep 2846735 = 4270103) B4270103
theorem B29192237 : Blo 996598 29192237 := bstep (se 3 (by rfl) ⟨5473544, by rfl⟩ : syracuseStep 29192237 = 10947089) B10947089
theorem B5697773 : Blo 996598 5697773 := bstep (se 3 (by rfl) ⟨1068332, by rfl⟩ : syracuseStep 5697773 = 2136665) B2136665
theorem B5402969 : Blo 996598 5402969 := bstep (se 2 (by rfl) ⟨2026113, by rfl⟩ : syracuseStep 5402969 = 4052227) B4052227
theorem B1896851 : Blo 996598 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B64713329 : Blo 996598 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B2159479 : Blo 996598 2159479 := bstep (se 1 (by rfl) ⟨1619609, by rfl⟩ : syracuseStep 2159479 = 3239219) B3239219
theorem B5698457 : Blo 996598 5698457 := bstep (se 2 (by rfl) ⟨2136921, by rfl⟩ : syracuseStep 5698457 = 4273843) B4273843
theorem B12809123 : Blo 996598 12809123 := bstep (se 1 (by rfl) ⟨9606842, by rfl⟩ : syracuseStep 12809123 = 19213685) B19213685
theorem B1799201 : Blo 996598 1799201 := bstep (se 2 (by rfl) ⟨674700, by rfl⟩ : syracuseStep 1799201 = 1349401) B1349401
theorem B5764385 : Blo 996598 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B2848135 : Blo 996598 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B17036729 : Blo 996598 17036729 := bstep (se 2 (by rfl) ⟨6388773, by rfl⟩ : syracuseStep 17036729 = 12777547) B12777547
theorem B48657995 : Blo 996598 48657995 := bstep (se 1 (by rfl) ⟨36493496, by rfl⟩ : syracuseStep 48657995 = 72986993) B72986993
theorem B2848409 : Blo 996598 2848409 := bstep (se 2 (by rfl) ⟨1068153, by rfl⟩ : syracuseStep 2848409 = 2136307) B2136307
theorem B1898255 : Blo 996598 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B10385189 : Blo 996598 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B3372947 : Blo 996598 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B3602323 : Blo 996598 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B3897355 : Blo 996598 3897355 := bstep (se 1 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 3897355 = 5846033) B5846033
theorem B5404715 : Blo 996598 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B1898795 : Blo 996598 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B7567991 : Blo 996598 7567991 := bstep (se 1 (by rfl) ⟨5675993, by rfl⟩ : syracuseStep 7567991 = 11351987) B11351987
theorem B3701537 : Blo 996598 3701537 := bstep (se 2 (by rfl) ⟨1388076, by rfl⟩ : syracuseStep 3701537 = 2776153) B2776153
theorem B11369483 : Blo 996598 11369483 := bstep (se 1 (by rfl) ⟨8527112, by rfl⟩ : syracuseStep 11369483 = 17054225) B17054225
theorem B3374351 : Blo 996598 3374351 := bstep (se 1 (by rfl) ⟨2530763, by rfl⟩ : syracuseStep 3374351 = 5061527) B5061527
theorem B12778883 : Blo 996598 12778883 := bstep (se 1 (by rfl) ⟨9584162, by rfl⟩ : syracuseStep 12778883 = 19168325) B19168325
theorem B5045651 : Blo 996598 5045651 := bstep (se 1 (by rfl) ⟨3784238, by rfl⟩ : syracuseStep 5045651 = 7568477) B7568477
theorem B3374621 : Blo 996598 3374621 := bstep (se 3 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 3374621 = 1265483) B1265483
theorem B7568963 : Blo 996598 7568963 := bstep (se 1 (by rfl) ⟨5676722, by rfl⟩ : syracuseStep 7568963 = 11353445) B11353445
theorem B3604169 : Blo 996598 3604169 := bstep (se 2 (by rfl) ⟨1351563, by rfl⟩ : syracuseStep 3604169 = 2703127) B2703127
theorem B3375161 : Blo 996598 3375161 := bstep (se 2 (by rfl) ⟨1265685, by rfl⟩ : syracuseStep 3375161 = 2531371) B2531371
theorem B2523383 : Blo 996598 2523383 := bstep (se 1 (by rfl) ⟨1892537, by rfl⟩ : syracuseStep 2523383 = 3785075) B3785075
theorem B3375485 : Blo 996598 3375485 := bstep (se 3 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 3375485 = 1265807) B1265807
theorem B3375755 : Blo 996598 3375755 := bstep (se 1 (by rfl) ⟨2531816, by rfl⟩ : syracuseStep 3375755 = 5063633) B5063633
theorem B1704847 : Blo 996598 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B3244961 : Blo 996598 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B1082719 : Blo 996598 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B7570907 : Blo 996598 7570907 := bstep (se 1 (by rfl) ⟨5678180, by rfl⟩ : syracuseStep 7570907 = 11356361) B11356361
theorem B12977653 : Blo 996598 12977653 := bstep (se 5 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 12977653 = 1216655) B1216655
theorem B3376673 : Blo 996598 3376673 := bstep (se 2 (by rfl) ⟨1266252, by rfl⟩ : syracuseStep 3376673 = 2532505) B2532505
theorem B2524871 : Blo 996598 2524871 := bstep (se 1 (by rfl) ⟨1893653, by rfl⟩ : syracuseStep 2524871 = 3787307) B3787307
theorem B12977863 : Blo 996598 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B3376889 : Blo 996598 3376889 := bstep (se 2 (by rfl) ⟨1266333, by rfl⟩ : syracuseStep 3376889 = 2532667) B2532667
theorem B7571393 : Blo 996598 7571393 := bstep (se 2 (by rfl) ⟨2839272, by rfl⟩ : syracuseStep 7571393 = 5678545) B5678545
theorem B1804535 : Blo 996598 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B8194409 : Blo 996598 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B5048891 : Blo 996598 5048891 := bstep (se 1 (by rfl) ⟨3786668, by rfl⟩ : syracuseStep 5048891 = 7573337) B7573337
theorem B2526025 : Blo 996598 2526025 := bstep (se 2 (by rfl) ⟨947259, by rfl⟩ : syracuseStep 2526025 = 1894519) B1894519
theorem B1707131 : Blo 996598 1707131 := bstep (se 1 (by rfl) ⟨1280348, by rfl⟩ : syracuseStep 1707131 = 2560697) B2560697
theorem B5049539 : Blo 996598 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B7572851 : Blo 996598 7572851 := bstep (se 1 (by rfl) ⟨5679638, by rfl⟩ : syracuseStep 7572851 = 11359277) B11359277
theorem B15371693 : Blo 996598 15371693 := bstep (se 3 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 15371693 = 5764385) B5764385
theorem B3247739 : Blo 996598 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B14585483 : Blo 996598 14585483 := bstep (se 1 (by rfl) ⟨10939112, by rfl⟩ : syracuseStep 14585483 = 21878225) B21878225
theorem B6393491 : Blo 996598 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B6393593 : Blo 996598 6393593 := bstep (se 2 (by rfl) ⟨2397597, by rfl⟩ : syracuseStep 6393593 = 4795195) B4795195
theorem B10817347 : Blo 996598 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B36507509 : Blo 996598 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B2527159 : Blo 996598 2527159 := bstep (se 1 (by rfl) ⟨1895369, by rfl⟩ : syracuseStep 2527159 = 3790739) B3790739
theorem B4624651 : Blo 996598 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B11375315 : Blo 996598 11375315 := bstep (se 1 (by rfl) ⟨8531486, by rfl⟩ : syracuseStep 11375315 = 17062973) B17062973
theorem B2429689 : Blo 996598 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B6394697 : Blo 996598 6394697 := bstep (se 2 (by rfl) ⟨2398011, by rfl⟩ : syracuseStep 6394697 = 4796023) B4796023
theorem B2397089 : Blo 996598 2397089 := bstep (se 2 (by rfl) ⟨898908, by rfl⟩ : syracuseStep 2397089 = 1797817) B1797817
theorem B3249079 : Blo 996598 3249079 := bstep (se 1 (by rfl) ⟨2436809, by rfl⟩ : syracuseStep 3249079 = 4873619) B4873619
theorem B2528617 : Blo 996598 2528617 := bstep (se 2 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 2528617 = 1896463) B1896463
theorem B2528891 : Blo 996598 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B6953303 : Blo 996598 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B2398859 : Blo 996598 2398859 := bstep (se 1 (by rfl) ⟨1799144, by rfl⟩ : syracuseStep 2398859 = 3598289) B3598289
theorem B1121359 : Blo 996598 1121359 := bstep (se 1 (by rfl) ⟨841019, by rfl⟩ : syracuseStep 1121359 = 1682039) B1682039
theorem B4791467 : Blo 996598 4791467 := bstep (se 1 (by rfl) ⟨3593600, by rfl⟩ : syracuseStep 4791467 = 7187201) B7187201
theorem B16194941 : Blo 996598 16194941 := bstep (se 3 (by rfl) ⟨3036551, by rfl⟩ : syracuseStep 16194941 = 6073103) B6073103
theorem B2530703 : Blo 996598 2530703 := bstep (se 1 (by rfl) ⟨1898027, by rfl⟩ : syracuseStep 2530703 = 3796055) B3796055
theorem B1121755 : Blo 996598 1121755 := bstep (se 1 (by rfl) ⟨841316, by rfl⟩ : syracuseStep 1121755 = 1682633) B1682633
theorem B5054075 : Blo 996598 5054075 := bstep (se 1 (by rfl) ⟨3790556, by rfl⟩ : syracuseStep 5054075 = 7581113) B7581113
theorem B2531027 : Blo 996598 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B16195463 : Blo 996598 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B1122223 : Blo 996598 1122223 := bstep (se 1 (by rfl) ⟨841667, by rfl⟩ : syracuseStep 1122223 = 1683335) B1683335
theorem B22454597 : Blo 996598 22454597 := bstep (se 4 (by rfl) ⟨2105118, by rfl⟩ : syracuseStep 22454597 = 4210237) B4210237
theorem B1122655 : Blo 996598 1122655 := bstep (se 1 (by rfl) ⟨841991, by rfl⟩ : syracuseStep 1122655 = 1683983) B1683983
theorem B1123015 : Blo 996598 1123015 := bstep (se 1 (by rfl) ⟨842261, by rfl⟩ : syracuseStep 1123015 = 1684523) B1684523
theorem B6923459 : Blo 996598 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B1516975 : Blo 996598 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B1123879 : Blo 996598 1123879 := bstep (se 1 (by rfl) ⟨842909, by rfl⟩ : syracuseStep 1123879 = 1685819) B1685819
theorem B2467691 : Blo 996598 2467691 := bstep (se 1 (by rfl) ⟨1850768, by rfl⟩ : syracuseStep 2467691 = 3701537) B3701537
theorem B7579655 : Blo 996598 7579655 := bstep (se 1 (by rfl) ⟨5684741, by rfl⟩ : syracuseStep 7579655 = 11369483) B11369483
theorem B29599981 : Blo 996598 29599981 := bstep (se 3 (by rfl) ⟨5549996, by rfl⟩ : syracuseStep 29599981 = 11099993) B11099993
theorem B5056829 : Blo 996598 5056829 := bstep (se 3 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 5056829 = 1896311) B1896311
theorem B1681769 : Blo 996598 1681769 := bstep (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) B1261327
theorem B2402779 : Blo 996598 2402779 := bstep (se 1 (by rfl) ⟨1802084, by rfl⟩ : syracuseStep 2402779 = 3604169) B3604169
theorem B7580141 : Blo 996598 7580141 := bstep (se 3 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 7580141 = 2842553) B2842553
theorem B4270801 : Blo 996598 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B1682167 : Blo 996598 1682167 := bstep (se 1 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 1682167 = 2523251) B2523251
theorem B1682363 : Blo 996598 1682363 := bstep (se 1 (by rfl) ⟨1261772, by rfl⟩ : syracuseStep 1682363 = 2523545) B2523545
theorem B621849635 : Blo 996598 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1682471 : Blo 996598 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B1420411 : Blo 996598 1420411 := bstep (se 1 (by rfl) ⟨1065308, by rfl⟩ : syracuseStep 1420411 = 2130617) B2130617
theorem B1125499 : Blo 996598 1125499 := bstep (se 1 (by rfl) ⟨844124, by rfl⟩ : syracuseStep 1125499 = 1688249) B1688249
theorem B1682761 : Blo 996598 1682761 := bstep (se 2 (by rfl) ⟨631035, by rfl⟩ : syracuseStep 1682761 = 1262071) B1262071
theorem B1682795 : Blo 996598 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B10792435 : Blo 996598 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B1683193 : Blo 996598 1683193 := bstep (se 2 (by rfl) ⟨631197, by rfl⟩ : syracuseStep 1683193 = 1262395) B1262395
theorem B1421231 : Blo 996598 1421231 := bstep (se 1 (by rfl) ⟨1065923, by rfl⟩ : syracuseStep 1421231 = 2131847) B2131847
theorem B1683463 : Blo 996598 1683463 := bstep (se 1 (by rfl) ⟨1262597, by rfl⟩ : syracuseStep 1683463 = 2525195) B2525195
theorem B32354477 : Blo 996598 32354477 := bstep (se 3 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 32354477 = 12132929) B12132929
theorem B3649853 : Blo 996598 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B7582085 : Blo 996598 7582085 := bstep (se 4 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 7582085 = 1421641) B1421641
theorem B1683895 : Blo 996598 1683895 := bstep (se 1 (by rfl) ⟨1262921, by rfl⟩ : syracuseStep 1683895 = 2525843) B2525843
theorem B28750301 : Blo 996598 28750301 := bstep (se 3 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 28750301 = 10781363) B10781363
theorem B5059097 : Blo 996598 5059097 := bstep (se 2 (by rfl) ⟨1897161, by rfl⟩ : syracuseStep 5059097 = 3794323) B3794323
theorem B21607013 : Blo 996598 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B1684091 : Blo 996598 1684091 := bstep (se 1 (by rfl) ⟨1263068, by rfl⟩ : syracuseStep 1684091 = 2526137) B2526137
theorem B3846865 : Blo 996598 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B4272851 : Blo 996598 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B7582571 : Blo 996598 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B1684489 : Blo 996598 1684489 := bstep (se 2 (by rfl) ⟨631683, by rfl⟩ : syracuseStep 1684489 = 1263367) B1263367
theorem B1684651 : Blo 996598 1684651 := bstep (se 1 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 1684651 = 2526977) B2526977
theorem B996647 : Blo 996598 996647 := bstep (se 1 (by rfl) ⟨747485, by rfl⟩ : syracuseStep 996647 = 1494971) B1494971
theorem B4109629 : Blo 996598 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B996687 : Blo 996598 996687 := bstep (se 1 (by rfl) ⟨747515, by rfl⟩ : syracuseStep 996687 = 1495031) B1495031
theorem B996703 : Blo 996598 996703 := bstep (se 1 (by rfl) ⟨747527, by rfl⟩ : syracuseStep 996703 = 1495055) B1495055
theorem B996731 : Blo 996598 996731 := bstep (se 1 (by rfl) ⟨747548, by rfl⟩ : syracuseStep 996731 = 1495097) B1495097
theorem B996783 : Blo 996598 996783 := bstep (se 1 (by rfl) ⟨747587, by rfl⟩ : syracuseStep 996783 = 1495175) B1495175
theorem B1422775 : Blo 996598 1422775 := bstep (se 1 (by rfl) ⟨1067081, by rfl⟩ : syracuseStep 1422775 = 2134163) B2134163
theorem B996807 : Blo 996598 996807 := bstep (se 1 (by rfl) ⟨747605, by rfl⟩ : syracuseStep 996807 = 1495211) B1495211
theorem B996827 : Blo 996598 996827 := bstep (se 1 (by rfl) ⟨747620, by rfl⟩ : syracuseStep 996827 = 1495241) B1495241
theorem B1684955 : Blo 996598 1684955 := bstep (se 1 (by rfl) ⟨1263716, by rfl⟩ : syracuseStep 1684955 = 2527433) B2527433
theorem B996903 : Blo 996598 996903 := bstep (se 1 (by rfl) ⟨747677, by rfl⟩ : syracuseStep 996903 = 1495355) B1495355
theorem B996943 : Blo 996598 996943 := bstep (se 1 (by rfl) ⟨747707, by rfl⟩ : syracuseStep 996943 = 1495415) B1495415
theorem B996959 : Blo 996598 996959 := bstep (se 1 (by rfl) ⟨747719, by rfl⟩ : syracuseStep 996959 = 1495439) B1495439
theorem B996987 : Blo 996598 996987 := bstep (se 1 (by rfl) ⟨747740, by rfl⟩ : syracuseStep 996987 = 1495481) B1495481
theorem B997039 : Blo 996598 997039 := bstep (se 1 (by rfl) ⟨747779, by rfl⟩ : syracuseStep 997039 = 1495559) B1495559
theorem B997063 : Blo 996598 997063 := bstep (se 1 (by rfl) ⟨747797, by rfl⟩ : syracuseStep 997063 = 1495595) B1495595
theorem B1685191 : Blo 996598 1685191 := bstep (se 1 (by rfl) ⟨1263893, by rfl⟩ : syracuseStep 1685191 = 2527787) B2527787
theorem B997083 : Blo 996598 997083 := bstep (se 1 (by rfl) ⟨747812, by rfl⟩ : syracuseStep 997083 = 1495625) B1495625
theorem B997159 : Blo 996598 997159 := bstep (se 1 (by rfl) ⟨747869, by rfl⟩ : syracuseStep 997159 = 1495739) B1495739
theorem B997199 : Blo 996598 997199 := bstep (se 1 (by rfl) ⟨747899, by rfl⟩ : syracuseStep 997199 = 1495799) B1495799
theorem B997215 : Blo 996598 997215 := bstep (se 1 (by rfl) ⟨747911, by rfl⟩ : syracuseStep 997215 = 1495823) B1495823
theorem B1685353 : Blo 996598 1685353 := bstep (se 2 (by rfl) ⟨632007, by rfl⟩ : syracuseStep 1685353 = 1264015) B1264015
theorem B997243 : Blo 996598 997243 := bstep (se 1 (by rfl) ⟨747932, by rfl⟩ : syracuseStep 997243 = 1495865) B1495865
theorem B997295 : Blo 996598 997295 := bstep (se 1 (by rfl) ⟨747971, by rfl⟩ : syracuseStep 997295 = 1495943) B1495943
theorem B997319 : Blo 996598 997319 := bstep (se 1 (by rfl) ⟨747989, by rfl⟩ : syracuseStep 997319 = 1495979) B1495979
theorem B997339 : Blo 996598 997339 := bstep (se 1 (by rfl) ⟨748004, by rfl⟩ : syracuseStep 997339 = 1496009) B1496009
theorem B997415 : Blo 996598 997415 := bstep (se 1 (by rfl) ⟨748061, by rfl⟩ : syracuseStep 997415 = 1496123) B1496123
theorem B997455 : Blo 996598 997455 := bstep (se 1 (by rfl) ⟨748091, by rfl⟩ : syracuseStep 997455 = 1496183) B1496183
theorem B997471 : Blo 996598 997471 := bstep (se 1 (by rfl) ⟨748103, by rfl⟩ : syracuseStep 997471 = 1496207) B1496207
theorem B997499 : Blo 996598 997499 := bstep (se 1 (by rfl) ⟨748124, by rfl⟩ : syracuseStep 997499 = 1496249) B1496249
theorem B997551 : Blo 996598 997551 := bstep (se 1 (by rfl) ⟨748163, by rfl⟩ : syracuseStep 997551 = 1496327) B1496327
theorem B997575 : Blo 996598 997575 := bstep (se 1 (by rfl) ⟨748181, by rfl⟩ : syracuseStep 997575 = 1496363) B1496363
theorem B997595 : Blo 996598 997595 := bstep (se 1 (by rfl) ⟨748196, by rfl⟩ : syracuseStep 997595 = 1496393) B1496393
theorem B997671 : Blo 996598 997671 := bstep (se 1 (by rfl) ⟨748253, by rfl⟩ : syracuseStep 997671 = 1496507) B1496507
theorem B997711 : Blo 996598 997711 := bstep (se 1 (by rfl) ⟨748283, by rfl⟩ : syracuseStep 997711 = 1496567) B1496567
theorem B997727 : Blo 996598 997727 := bstep (se 1 (by rfl) ⟨748295, by rfl⟩ : syracuseStep 997727 = 1496591) B1496591
theorem B997755 : Blo 996598 997755 := bstep (se 1 (by rfl) ⟨748316, by rfl⟩ : syracuseStep 997755 = 1496633) B1496633
theorem B997807 : Blo 996598 997807 := bstep (se 1 (by rfl) ⟨748355, by rfl⟩ : syracuseStep 997807 = 1496711) B1496711
theorem B1685947 : Blo 996598 1685947 := bstep (se 1 (by rfl) ⟨1264460, by rfl⟩ : syracuseStep 1685947 = 2528921) B2528921
theorem B997831 : Blo 996598 997831 := bstep (se 1 (by rfl) ⟨748373, by rfl⟩ : syracuseStep 997831 = 1496747) B1496747
theorem B997851 : Blo 996598 997851 := bstep (se 1 (by rfl) ⟨748388, by rfl⟩ : syracuseStep 997851 = 1496777) B1496777
theorem B997927 : Blo 996598 997927 := bstep (se 1 (by rfl) ⟨748445, by rfl⟩ : syracuseStep 997927 = 1496891) B1496891
theorem B1686055 : Blo 996598 1686055 := bstep (se 1 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 1686055 = 2529083) B2529083
theorem B997967 : Blo 996598 997967 := bstep (se 1 (by rfl) ⟨748475, by rfl⟩ : syracuseStep 997967 = 1496951) B1496951
theorem B997983 : Blo 996598 997983 := bstep (se 1 (by rfl) ⟨748487, by rfl⟩ : syracuseStep 997983 = 1496975) B1496975
theorem B2243195 : Blo 996598 2243195 := bstep (se 1 (by rfl) ⟨1682396, by rfl⟩ : syracuseStep 2243195 = 3364793) B3364793
theorem B998011 : Blo 996598 998011 := bstep (se 1 (by rfl) ⟨748508, by rfl⟩ : syracuseStep 998011 = 1497017) B1497017
theorem B998063 : Blo 996598 998063 := bstep (se 1 (by rfl) ⟨748547, by rfl⟩ : syracuseStep 998063 = 1497095) B1497095
theorem B10959545 : Blo 996598 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B998087 : Blo 996598 998087 := bstep (se 1 (by rfl) ⟨748565, by rfl⟩ : syracuseStep 998087 = 1497131) B1497131
theorem B998107 : Blo 996598 998107 := bstep (se 1 (by rfl) ⟨748580, by rfl⟩ : syracuseStep 998107 = 1497161) B1497161
theorem B2243321 : Blo 996598 2243321 := bstep (se 2 (by rfl) ⟨841245, by rfl⟩ : syracuseStep 2243321 = 1682491) B1682491
theorem B7584515 : Blo 996598 7584515 := bstep (se 1 (by rfl) ⟨5688386, by rfl⟩ : syracuseStep 7584515 = 11376773) B11376773
theorem B998183 : Blo 996598 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B998223 : Blo 996598 998223 := bstep (se 1 (by rfl) ⟨748667, by rfl⟩ : syracuseStep 998223 = 1497335) B1497335
theorem B998239 : Blo 996598 998239 := bstep (se 1 (by rfl) ⟨748679, by rfl⟩ : syracuseStep 998239 = 1497359) B1497359
theorem B1424233 : Blo 996598 1424233 := bstep (se 2 (by rfl) ⟨534087, by rfl⟩ : syracuseStep 1424233 = 1068175) B1068175
theorem B1686379 : Blo 996598 1686379 := bstep (se 1 (by rfl) ⟨1264784, by rfl⟩ : syracuseStep 1686379 = 2529569) B2529569
theorem B998267 : Blo 996598 998267 := bstep (se 1 (by rfl) ⟨748700, by rfl⟩ : syracuseStep 998267 = 1497401) B1497401
theorem B998319 : Blo 996598 998319 := bstep (se 1 (by rfl) ⟨748739, by rfl⟩ : syracuseStep 998319 = 1497479) B1497479
theorem B998343 : Blo 996598 998343 := bstep (se 1 (by rfl) ⟨748757, by rfl⟩ : syracuseStep 998343 = 1497515) B1497515
theorem B998363 : Blo 996598 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B2243591 : Blo 996598 2243591 := bstep (se 1 (by rfl) ⟨1682693, by rfl⟩ : syracuseStep 2243591 = 3365387) B3365387
theorem B998439 : Blo 996598 998439 := bstep (se 1 (by rfl) ⟨748829, by rfl⟩ : syracuseStep 998439 = 1497659) B1497659
theorem B2243663 : Blo 996598 2243663 := bstep (se 1 (by rfl) ⟨1682747, by rfl⟩ : syracuseStep 2243663 = 3365495) B3365495
theorem B998479 : Blo 996598 998479 := bstep (se 1 (by rfl) ⟨748859, by rfl⟩ : syracuseStep 998479 = 1497719) B1497719
theorem B10796111 : Blo 996598 10796111 := bstep (se 1 (by rfl) ⟨8097083, by rfl⟩ : syracuseStep 10796111 = 16194167) B16194167
theorem B998495 : Blo 996598 998495 := bstep (se 1 (by rfl) ⟨748871, by rfl⟩ : syracuseStep 998495 = 1497743) B1497743
theorem B998523 : Blo 996598 998523 := bstep (se 1 (by rfl) ⟨748892, by rfl⟩ : syracuseStep 998523 = 1497785) B1497785
theorem B5684377 : Blo 996598 5684377 := bstep (se 2 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 5684377 = 4263283) B4263283
theorem B998575 : Blo 996598 998575 := bstep (se 1 (by rfl) ⟨748931, by rfl⟩ : syracuseStep 998575 = 1497863) B1497863
theorem B998599 : Blo 996598 998599 := bstep (se 1 (by rfl) ⟨748949, by rfl⟩ : syracuseStep 998599 = 1497899) B1497899
theorem B998619 : Blo 996598 998619 := bstep (se 1 (by rfl) ⟨748964, by rfl⟩ : syracuseStep 998619 = 1497929) B1497929
theorem B11517221 : Blo 996598 11517221 := bstep (se 4 (by rfl) ⟨1079739, by rfl⟩ : syracuseStep 11517221 = 2159479) B2159479
theorem B998695 : Blo 996598 998695 := bstep (se 1 (by rfl) ⟨749021, by rfl⟩ : syracuseStep 998695 = 1498043) B1498043
theorem B998735 : Blo 996598 998735 := bstep (se 1 (by rfl) ⟨749051, by rfl⟩ : syracuseStep 998735 = 1498103) B1498103
theorem B998751 : Blo 996598 998751 := bstep (se 1 (by rfl) ⟨749063, by rfl⟩ : syracuseStep 998751 = 1498127) B1498127
theorem B998779 : Blo 996598 998779 := bstep (se 1 (by rfl) ⟨749084, by rfl⟩ : syracuseStep 998779 = 1498169) B1498169
theorem B5062013 : Blo 996598 5062013 := bstep (se 3 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 5062013 = 1898255) B1898255
theorem B998831 : Blo 996598 998831 := bstep (se 1 (by rfl) ⟨749123, by rfl⟩ : syracuseStep 998831 = 1498247) B1498247
theorem B998855 : Blo 996598 998855 := bstep (se 1 (by rfl) ⟨749141, by rfl⟩ : syracuseStep 998855 = 1498283) B1498283
theorem B2244059 : Blo 996598 2244059 := bstep (se 1 (by rfl) ⟨1683044, by rfl⟩ : syracuseStep 2244059 = 3366089) B3366089
theorem B998875 : Blo 996598 998875 := bstep (se 1 (by rfl) ⟨749156, by rfl⟩ : syracuseStep 998875 = 1498313) B1498313
theorem B998951 : Blo 996598 998951 := bstep (se 1 (by rfl) ⟨749213, by rfl⟩ : syracuseStep 998951 = 1498427) B1498427
theorem B998991 : Blo 996598 998991 := bstep (se 1 (by rfl) ⟨749243, by rfl⟩ : syracuseStep 998991 = 1498487) B1498487
theorem B999007 : Blo 996598 999007 := bstep (se 1 (by rfl) ⟨749255, by rfl⟩ : syracuseStep 999007 = 1498511) B1498511
theorem B999035 : Blo 996598 999035 := bstep (se 1 (by rfl) ⟨749276, by rfl⟩ : syracuseStep 999035 = 1498553) B1498553
theorem B999087 : Blo 996598 999087 := bstep (se 1 (by rfl) ⟨749315, by rfl⟩ : syracuseStep 999087 = 1498631) B1498631
theorem B3784391 : Blo 996598 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B999111 : Blo 996598 999111 := bstep (se 1 (by rfl) ⟨749333, by rfl⟩ : syracuseStep 999111 = 1498667) B1498667
theorem B999131 : Blo 996598 999131 := bstep (se 1 (by rfl) ⟨749348, by rfl⟩ : syracuseStep 999131 = 1498697) B1498697
theorem B999207 : Blo 996598 999207 := bstep (se 1 (by rfl) ⟨749405, by rfl⟩ : syracuseStep 999207 = 1498811) B1498811
theorem B999247 : Blo 996598 999247 := bstep (se 1 (by rfl) ⟨749435, by rfl⟩ : syracuseStep 999247 = 1498871) B1498871
theorem B999263 : Blo 996598 999263 := bstep (se 1 (by rfl) ⟨749447, by rfl⟩ : syracuseStep 999263 = 1498895) B1498895
theorem B999291 : Blo 996598 999291 := bstep (se 1 (by rfl) ⟨749468, by rfl⟩ : syracuseStep 999291 = 1498937) B1498937
theorem B1687439 : Blo 996598 1687439 := bstep (se 1 (by rfl) ⟨1265579, by rfl⟩ : syracuseStep 1687439 = 2531159) B2531159
theorem B2244527 : Blo 996598 2244527 := bstep (se 1 (by rfl) ⟨1683395, by rfl⟩ : syracuseStep 2244527 = 3366791) B3366791
theorem B999343 : Blo 996598 999343 := bstep (se 1 (by rfl) ⟨749507, by rfl⟩ : syracuseStep 999343 = 1499015) B1499015
theorem B999367 : Blo 996598 999367 := bstep (se 1 (by rfl) ⟨749525, by rfl⟩ : syracuseStep 999367 = 1499051) B1499051
theorem B999387 : Blo 996598 999387 := bstep (se 1 (by rfl) ⟨749540, by rfl⟩ : syracuseStep 999387 = 1499081) B1499081
theorem B999463 : Blo 996598 999463 := bstep (se 1 (by rfl) ⟨749597, by rfl⟩ : syracuseStep 999463 = 1499195) B1499195
theorem B999503 : Blo 996598 999503 := bstep (se 1 (by rfl) ⟨749627, by rfl⟩ : syracuseStep 999503 = 1499255) B1499255
theorem B999519 : Blo 996598 999519 := bstep (se 1 (by rfl) ⟨749639, by rfl⟩ : syracuseStep 999519 = 1499279) B1499279
theorem B999547 : Blo 996598 999547 := bstep (se 1 (by rfl) ⟨749660, by rfl⟩ : syracuseStep 999547 = 1499321) B1499321
theorem B1687675 : Blo 996598 1687675 := bstep (se 1 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 1687675 = 2531513) B2531513
theorem B2244779 : Blo 996598 2244779 := bstep (se 1 (by rfl) ⟨1683584, by rfl⟩ : syracuseStep 2244779 = 3367169) B3367169
theorem B999599 : Blo 996598 999599 := bstep (se 1 (by rfl) ⟨749699, by rfl⟩ : syracuseStep 999599 = 1499399) B1499399
theorem B999623 : Blo 996598 999623 := bstep (se 1 (by rfl) ⟨749717, by rfl⟩ : syracuseStep 999623 = 1499435) B1499435
theorem B999643 : Blo 996598 999643 := bstep (se 1 (by rfl) ⟨749732, by rfl⟩ : syracuseStep 999643 = 1499465) B1499465
theorem B999719 : Blo 996598 999719 := bstep (se 1 (by rfl) ⟨749789, by rfl⟩ : syracuseStep 999719 = 1499579) B1499579
theorem B3195197 : Blo 996598 3195197 := bstep (se 3 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 3195197 = 1198199) B1198199
theorem B999759 : Blo 996598 999759 := bstep (se 1 (by rfl) ⟨749819, by rfl⟩ : syracuseStep 999759 = 1499639) B1499639
theorem B1261919 : Blo 996598 1261919 := bstep (se 1 (by rfl) ⟨946439, by rfl⟩ : syracuseStep 1261919 = 1892879) B1892879
theorem B999775 : Blo 996598 999775 := bstep (se 1 (by rfl) ⟨749831, by rfl⟩ : syracuseStep 999775 = 1499663) B1499663
theorem B999803 : Blo 996598 999803 := bstep (se 1 (by rfl) ⟨749852, by rfl⟩ : syracuseStep 999803 = 1499705) B1499705
theorem B3785089 : Blo 996598 3785089 := bstep (se 2 (by rfl) ⟨1419408, by rfl⟩ : syracuseStep 3785089 = 2838817) B2838817
theorem B999855 : Blo 996598 999855 := bstep (se 1 (by rfl) ⟨749891, by rfl⟩ : syracuseStep 999855 = 1499783) B1499783
theorem B999879 : Blo 996598 999879 := bstep (se 1 (by rfl) ⟨749909, by rfl⟩ : syracuseStep 999879 = 1499819) B1499819
theorem B999899 : Blo 996598 999899 := bstep (se 1 (by rfl) ⟨749924, by rfl⟩ : syracuseStep 999899 = 1499849) B1499849
theorem B999975 : Blo 996598 999975 := bstep (se 1 (by rfl) ⟨749981, by rfl⟩ : syracuseStep 999975 = 1499963) B1499963
theorem B6406715 : Blo 996598 6406715 := bstep (se 1 (by rfl) ⟨4805036, by rfl⟩ : syracuseStep 6406715 = 9610073) B9610073
theorem B1000015 : Blo 996598 1000015 := bstep (se 1 (by rfl) ⟨750011, by rfl⟩ : syracuseStep 1000015 = 1500023) B1500023
theorem B1000031 : Blo 996598 1000031 := bstep (se 1 (by rfl) ⟨750023, by rfl⟩ : syracuseStep 1000031 = 1500047) B1500047
theorem B1000059 : Blo 996598 1000059 := bstep (se 1 (by rfl) ⟨750044, by rfl⟩ : syracuseStep 1000059 = 1500089) B1500089
theorem B3785363 : Blo 996598 3785363 := bstep (se 1 (by rfl) ⟨2839022, by rfl⟩ : syracuseStep 3785363 = 5678045) B5678045
theorem B1000111 : Blo 996598 1000111 := bstep (se 1 (by rfl) ⟨750083, by rfl⟩ : syracuseStep 1000111 = 1500167) B1500167
theorem B2245319 : Blo 996598 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B1000135 : Blo 996598 1000135 := bstep (se 1 (by rfl) ⟨750101, by rfl⟩ : syracuseStep 1000135 = 1500203) B1500203
theorem B1950419 : Blo 996598 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B2704087 : Blo 996598 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B1000155 : Blo 996598 1000155 := bstep (se 1 (by rfl) ⟨750116, by rfl⟩ : syracuseStep 1000155 = 1500233) B1500233
theorem B1000231 : Blo 996598 1000231 := bstep (se 1 (by rfl) ⟨750173, by rfl⟩ : syracuseStep 1000231 = 1500347) B1500347
theorem B1000271 : Blo 996598 1000271 := bstep (se 1 (by rfl) ⟨750203, by rfl⟩ : syracuseStep 1000271 = 1500407) B1500407
theorem B1000287 : Blo 996598 1000287 := bstep (se 1 (by rfl) ⟨750215, by rfl⟩ : syracuseStep 1000287 = 1500431) B1500431
theorem B1000315 : Blo 996598 1000315 := bstep (se 1 (by rfl) ⟨750236, by rfl⟩ : syracuseStep 1000315 = 1500473) B1500473
theorem B7685039 : Blo 996598 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B1000367 : Blo 996598 1000367 := bstep (se 1 (by rfl) ⟨750275, by rfl⟩ : syracuseStep 1000367 = 1500551) B1500551
theorem B1000391 : Blo 996598 1000391 := bstep (se 1 (by rfl) ⟨750293, by rfl⟩ : syracuseStep 1000391 = 1500587) B1500587
theorem B1000411 : Blo 996598 1000411 := bstep (se 1 (by rfl) ⟨750308, by rfl⟩ : syracuseStep 1000411 = 1500617) B1500617
theorem B1000487 : Blo 996598 1000487 := bstep (se 1 (by rfl) ⟨750365, by rfl⟩ : syracuseStep 1000487 = 1500731) B1500731
theorem B6833231 : Blo 996598 6833231 := bstep (se 1 (by rfl) ⟨5124923, by rfl⟩ : syracuseStep 6833231 = 10249847) B10249847
theorem B1000527 : Blo 996598 1000527 := bstep (se 1 (by rfl) ⟨750395, by rfl⟩ : syracuseStep 1000527 = 1500791) B1500791
theorem B1000543 : Blo 996598 1000543 := bstep (se 1 (by rfl) ⟨750407, by rfl⟩ : syracuseStep 1000543 = 1500815) B1500815
theorem B1000571 : Blo 996598 1000571 := bstep (se 1 (by rfl) ⟨750428, by rfl⟩ : syracuseStep 1000571 = 1500857) B1500857
theorem B3196361 : Blo 996598 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B2246183 : Blo 996598 2246183 := bstep (se 1 (by rfl) ⟨1684637, by rfl⟩ : syracuseStep 2246183 = 3369275) B3369275
theorem B6407819 : Blo 996598 6407819 := bstep (se 1 (by rfl) ⟨4805864, by rfl⟩ : syracuseStep 6407819 = 9611729) B9611729
theorem B2246507 : Blo 996598 2246507 := bstep (se 1 (by rfl) ⟨1684880, by rfl⟩ : syracuseStep 2246507 = 3369761) B3369761
theorem B2246561 : Blo 996598 2246561 := bstep (se 2 (by rfl) ⟨842460, by rfl⟩ : syracuseStep 2246561 = 1684921) B1684921
theorem B6473657 : Blo 996598 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B7587917 : Blo 996598 7587917 := bstep (se 3 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 7587917 = 2845469) B2845469
theorem B2246903 : Blo 996598 2246903 := bstep (se 1 (by rfl) ⟨1685177, by rfl⟩ : syracuseStep 2246903 = 3370355) B3370355
theorem B3787019 : Blo 996598 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B10242541 : Blo 996598 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B4803097 : Blo 996598 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B5196473 : Blo 996598 5196473 := bstep (se 2 (by rfl) ⟨1948677, by rfl⟩ : syracuseStep 5196473 = 3897355) B3897355
theorem B2247497 : Blo 996598 2247497 := bstep (se 2 (by rfl) ⟨842811, by rfl⟩ : syracuseStep 2247497 = 1685623) B1685623
theorem B1264567 : Blo 996598 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B43142219 : Blo 996598 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B8539415 : Blo 996598 8539415 := bstep (se 1 (by rfl) ⟨6404561, by rfl⟩ : syracuseStep 8539415 = 12809123) B12809123
theorem B1199467 : Blo 996598 1199467 := bstep (se 1 (by rfl) ⟨899600, by rfl⟩ : syracuseStep 1199467 = 1799201) B1799201
theorem B30690893 : Blo 996598 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B2248289 : Blo 996598 2248289 := bstep (se 2 (by rfl) ⟨843108, by rfl⟩ : syracuseStep 2248289 = 1686217) B1686217
theorem B11357819 : Blo 996598 11357819 := bstep (se 1 (by rfl) ⟨8518364, by rfl⟩ : syracuseStep 11357819 = 17036729) B17036729
theorem B3788477 : Blo 996598 3788477 := bstep (se 3 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 3788477 = 1420679) B1420679
theorem B1494959 : Blo 996598 1494959 := bstep (se 1 (by rfl) ⟨1121219, by rfl⟩ : syracuseStep 1494959 = 2242439) B2242439
theorem B2248631 : Blo 996598 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B1495049 : Blo 996598 1495049 := bstep (se 2 (by rfl) ⟨560643, by rfl⟩ : syracuseStep 1495049 = 1121287) B1121287
theorem B1495079 : Blo 996598 1495079 := bstep (se 1 (by rfl) ⟨1121309, by rfl⟩ : syracuseStep 1495079 = 2242619) B2242619
theorem B1495163 : Blo 996598 1495163 := bstep (se 1 (by rfl) ⟨1121372, by rfl⟩ : syracuseStep 1495163 = 2242745) B2242745
theorem B1265863 : Blo 996598 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1495289 : Blo 996598 1495289 := bstep (se 2 (by rfl) ⟨560733, by rfl⟩ : syracuseStep 1495289 = 1121467) B1121467
theorem B8540477 : Blo 996598 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B1495391 : Blo 996598 1495391 := bstep (se 1 (by rfl) ⟨1121543, by rfl⟩ : syracuseStep 1495391 = 2243087) B2243087
theorem B1495403 : Blo 996598 1495403 := bstep (se 1 (by rfl) ⟨1121552, by rfl⟩ : syracuseStep 1495403 = 2243105) B2243105
theorem B3592649 : Blo 996598 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B7590347 : Blo 996598 7590347 := bstep (se 1 (by rfl) ⟨5692760, by rfl⟩ : syracuseStep 7590347 = 11385521) B11385521
theorem B2249225 : Blo 996598 2249225 := bstep (se 2 (by rfl) ⟨843459, by rfl⟩ : syracuseStep 2249225 = 1686919) B1686919
theorem B3199513 : Blo 996598 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B3592763 : Blo 996598 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B1495631 : Blo 996598 1495631 := bstep (se 1 (by rfl) ⟨1121723, by rfl⟩ : syracuseStep 1495631 = 2243447) B2243447
theorem B1495751 : Blo 996598 1495751 := bstep (se 1 (by rfl) ⟨1121813, by rfl⟩ : syracuseStep 1495751 = 2243627) B2243627
theorem B9098057 : Blo 996598 9098057 := bstep (se 2 (by rfl) ⟨3411771, by rfl⟩ : syracuseStep 9098057 = 6823543) B6823543
theorem B2249567 : Blo 996598 2249567 := bstep (se 1 (by rfl) ⟨1687175, by rfl⟩ : syracuseStep 2249567 = 3374351) B3374351
theorem B1495913 : Blo 996598 1495913 := bstep (se 2 (by rfl) ⟨560967, by rfl⟩ : syracuseStep 1495913 = 1121935) B1121935
theorem B3363767 : Blo 996598 3363767 := bstep (se 1 (by rfl) ⟨2522825, by rfl⟩ : syracuseStep 3363767 = 5045651) B5045651
theorem B1495991 : Blo 996598 1495991 := bstep (se 1 (by rfl) ⟨1121993, by rfl⟩ : syracuseStep 1495991 = 2243987) B2243987
theorem B1496027 : Blo 996598 1496027 := bstep (se 1 (by rfl) ⟨1122020, by rfl⟩ : syracuseStep 1496027 = 2244041) B2244041
theorem B2249747 : Blo 996598 2249747 := bstep (se 1 (by rfl) ⟨1687310, by rfl⟩ : syracuseStep 2249747 = 3374621) B3374621
theorem B2250089 : Blo 996598 2250089 := bstep (se 2 (by rfl) ⟨843783, by rfl⟩ : syracuseStep 2250089 = 1687567) B1687567
theorem B3790223 : Blo 996598 3790223 := bstep (se 1 (by rfl) ⟨2842667, by rfl⟩ : syracuseStep 3790223 = 5685335) B5685335
theorem B1496495 : Blo 996598 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B3364361 : Blo 996598 3364361 := bstep (se 2 (by rfl) ⟨1261635, by rfl⟩ : syracuseStep 3364361 = 2523271) B2523271
theorem B1496585 : Blo 996598 1496585 := bstep (se 2 (by rfl) ⟨561219, by rfl⟩ : syracuseStep 1496585 = 1122439) B1122439
theorem B1496615 : Blo 996598 1496615 := bstep (se 1 (by rfl) ⟨1122461, by rfl⟩ : syracuseStep 1496615 = 2244923) B2244923
theorem B1496699 : Blo 996598 1496699 := bstep (se 1 (by rfl) ⟨1122524, by rfl⟩ : syracuseStep 1496699 = 2245049) B2245049
theorem B2840275 : Blo 996598 2840275 := bstep (se 1 (by rfl) ⟨2130206, by rfl⟩ : syracuseStep 2840275 = 4260413) B4260413
theorem B1496825 : Blo 996598 1496825 := bstep (se 2 (by rfl) ⟨561309, by rfl⟩ : syracuseStep 1496825 = 1122619) B1122619
theorem B11392811 : Blo 996598 11392811 := bstep (se 1 (by rfl) ⟨8544608, by rfl⟩ : syracuseStep 11392811 = 17089217) B17089217
theorem B6084395 : Blo 996598 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B1496927 : Blo 996598 1496927 := bstep (se 1 (by rfl) ⟨1122695, by rfl⟩ : syracuseStep 1496927 = 2245391) B2245391
theorem B2053993 : Blo 996598 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B3594091 : Blo 996598 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B1496939 : Blo 996598 1496939 := bstep (se 1 (by rfl) ⟨1122704, by rfl⟩ : syracuseStep 1496939 = 2245409) B2245409
theorem B6838151 : Blo 996598 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B2840503 : Blo 996598 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B2250683 : Blo 996598 2250683 := bstep (se 1 (by rfl) ⟨1688012, by rfl⟩ : syracuseStep 2250683 = 3376025) B3376025
theorem B2250809 : Blo 996598 2250809 := bstep (se 2 (by rfl) ⟨844053, by rfl⟩ : syracuseStep 2250809 = 1688107) B1688107
theorem B1136719 : Blo 996598 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B1497167 : Blo 996598 1497167 := bstep (se 1 (by rfl) ⟨1122875, by rfl⟩ : syracuseStep 1497167 = 2245751) B2245751
theorem B4053149 : Blo 996598 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B1497287 : Blo 996598 1497287 := bstep (se 1 (by rfl) ⟨1122965, by rfl⟩ : syracuseStep 1497287 = 2245931) B2245931
theorem B3365225 : Blo 996598 3365225 := bstep (se 2 (by rfl) ⟨1261959, by rfl⟩ : syracuseStep 3365225 = 2523919) B2523919
theorem B1497449 : Blo 996598 1497449 := bstep (se 2 (by rfl) ⟨561543, by rfl⟩ : syracuseStep 1497449 = 1123087) B1123087
theorem B2251151 : Blo 996598 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B1497527 : Blo 996598 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B1497563 : Blo 996598 1497563 := bstep (se 1 (by rfl) ⟨1123172, by rfl⟩ : syracuseStep 1497563 = 2246345) B2246345
theorem B3791393 : Blo 996598 3791393 := bstep (se 2 (by rfl) ⟨1421772, by rfl⟩ : syracuseStep 3791393 = 2843545) B2843545
theorem B7592777 : Blo 996598 7592777 := bstep (se 2 (by rfl) ⟨2847291, by rfl⟩ : syracuseStep 7592777 = 5694583) B5694583
theorem B3791711 : Blo 996598 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B1498031 : Blo 996598 1498031 := bstep (se 1 (by rfl) ⟨1123523, by rfl⟩ : syracuseStep 1498031 = 2247047) B2247047
theorem B3365819 : Blo 996598 3365819 := bstep (se 1 (by rfl) ⟨2524364, by rfl⟩ : syracuseStep 3365819 = 5048729) B5048729
theorem B3791879 : Blo 996598 3791879 := bstep (se 1 (by rfl) ⟨2843909, by rfl⟩ : syracuseStep 3791879 = 5687819) B5687819
theorem B1498121 : Blo 996598 1498121 := bstep (se 2 (by rfl) ⟨561795, by rfl⟩ : syracuseStep 1498121 = 1123591) B1123591
theorem B1498151 : Blo 996598 1498151 := bstep (se 1 (by rfl) ⟨1123613, by rfl⟩ : syracuseStep 1498151 = 2247227) B2247227
theorem B1498235 : Blo 996598 1498235 := bstep (se 1 (by rfl) ⟨1123676, by rfl⟩ : syracuseStep 1498235 = 2247353) B2247353
theorem B1498361 : Blo 996598 1498361 := bstep (se 2 (by rfl) ⟨561885, by rfl⟩ : syracuseStep 1498361 = 1123771) B1123771
theorem B3595531 : Blo 996598 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B1498463 : Blo 996598 1498463 := bstep (se 1 (by rfl) ⟨1123847, by rfl⟩ : syracuseStep 1498463 = 2247695) B2247695
theorem B2841961 : Blo 996598 2841961 := bstep (se 2 (by rfl) ⟨1065735, by rfl⟩ : syracuseStep 2841961 = 2131471) B2131471
theorem B1498475 : Blo 996598 1498475 := bstep (se 1 (by rfl) ⟨1123856, by rfl⟩ : syracuseStep 1498475 = 2247713) B2247713
theorem B3792365 : Blo 996598 3792365 := bstep (se 3 (by rfl) ⟨711068, by rfl⟩ : syracuseStep 3792365 = 1422137) B1422137
theorem B2842121 : Blo 996598 2842121 := bstep (se 2 (by rfl) ⟨1065795, by rfl⟩ : syracuseStep 2842121 = 2131591) B2131591
theorem B1498703 : Blo 996598 1498703 := bstep (se 1 (by rfl) ⟨1124027, by rfl⟩ : syracuseStep 1498703 = 2248055) B2248055
theorem B2842235 : Blo 996598 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B1498823 : Blo 996598 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B1892089 : Blo 996598 1892089 := bstep (se 2 (by rfl) ⟨709533, by rfl⟩ : syracuseStep 1892089 = 1419067) B1419067
theorem B2842361 : Blo 996598 2842361 := bstep (se 2 (by rfl) ⟨1065885, by rfl⟩ : syracuseStep 2842361 = 2131771) B2131771
theorem B3792683 : Blo 996598 3792683 := bstep (se 1 (by rfl) ⟨2844512, by rfl⟩ : syracuseStep 3792683 = 5689025) B5689025
theorem B1498985 : Blo 996598 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B1499063 : Blo 996598 1499063 := bstep (se 1 (by rfl) ⟨1124297, by rfl⟩ : syracuseStep 1499063 = 2248595) B2248595
theorem B1499099 : Blo 996598 1499099 := bstep (se 1 (by rfl) ⟨1124324, by rfl⟩ : syracuseStep 1499099 = 2248649) B2248649
theorem B2843009 : Blo 996598 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B1499567 : Blo 996598 1499567 := bstep (se 1 (by rfl) ⟨1124675, by rfl⟩ : syracuseStep 1499567 = 2249351) B2249351
theorem B1499657 : Blo 996598 1499657 := bstep (se 2 (by rfl) ⟨562371, by rfl⟩ : syracuseStep 1499657 = 1124743) B1124743
theorem B1499687 : Blo 996598 1499687 := bstep (se 1 (by rfl) ⟨1124765, by rfl⟩ : syracuseStep 1499687 = 2249531) B2249531
theorem B3367547 : Blo 996598 3367547 := bstep (se 1 (by rfl) ⟨2525660, by rfl⟩ : syracuseStep 3367547 = 5051321) B5051321
theorem B1499771 : Blo 996598 1499771 := bstep (se 1 (by rfl) ⟨1124828, by rfl⟩ : syracuseStep 1499771 = 2249657) B2249657
theorem B1499897 : Blo 996598 1499897 := bstep (se 2 (by rfl) ⟨562461, by rfl⟩ : syracuseStep 1499897 = 1124923) B1124923
theorem B3367709 : Blo 996598 3367709 := bstep (se 3 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 3367709 = 1262891) B1262891
theorem B1499999 : Blo 996598 1499999 := bstep (se 1 (by rfl) ⟨1124999, by rfl⟩ : syracuseStep 1499999 = 2249999) B2249999
theorem B1500011 : Blo 996598 1500011 := bstep (se 1 (by rfl) ⟨1125008, by rfl⟩ : syracuseStep 1500011 = 2250017) B2250017
theorem B2843579 : Blo 996598 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1139675 : Blo 996598 1139675 := bstep (se 1 (by rfl) ⟨854756, by rfl⟩ : syracuseStep 1139675 = 1709513) B1709513
theorem B3597319 : Blo 996598 3597319 := bstep (se 1 (by rfl) ⟨2697989, by rfl⟩ : syracuseStep 3597319 = 5395979) B5395979
theorem B1893395 : Blo 996598 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B1500239 : Blo 996598 1500239 := bstep (se 1 (by rfl) ⟨1125179, by rfl⟩ : syracuseStep 1500239 = 2250359) B2250359
theorem B1893547 : Blo 996598 1893547 := bstep (se 1 (by rfl) ⟨1420160, by rfl⟩ : syracuseStep 1893547 = 2840321) B2840321
theorem B2843819 : Blo 996598 2843819 := bstep (se 1 (by rfl) ⟨2132864, by rfl⟩ : syracuseStep 2843819 = 4265729) B4265729
theorem B1500359 : Blo 996598 1500359 := bstep (se 1 (by rfl) ⟨1125269, by rfl⟩ : syracuseStep 1500359 = 2250539) B2250539
theorem B1500521 : Blo 996598 1500521 := bstep (se 2 (by rfl) ⟨562695, by rfl⟩ : syracuseStep 1500521 = 1125391) B1125391
theorem B1893775 : Blo 996598 1893775 := bstep (se 1 (by rfl) ⟨1420331, by rfl⟩ : syracuseStep 1893775 = 2840663) B2840663
theorem B2024887 : Blo 996598 2024887 := bstep (se 1 (by rfl) ⟨1518665, by rfl⟩ : syracuseStep 2024887 = 3037331) B3037331
theorem B1500599 : Blo 996598 1500599 := bstep (se 1 (by rfl) ⟨1125449, by rfl⟩ : syracuseStep 1500599 = 2250899) B2250899
theorem B1893851 : Blo 996598 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B3368411 : Blo 996598 3368411 := bstep (se 1 (by rfl) ⟨2526308, by rfl⟩ : syracuseStep 3368411 = 5052617) B5052617
theorem B1500635 : Blo 996598 1500635 := bstep (se 1 (by rfl) ⟨1125476, by rfl⟩ : syracuseStep 1500635 = 2250953) B2250953
theorem B3794795 : Blo 996598 3794795 := bstep (se 1 (by rfl) ⟨2846096, by rfl⟩ : syracuseStep 3794795 = 5692193) B5692193
theorem B3598415 : Blo 996598 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B2025569 : Blo 996598 2025569 := bstep (se 2 (by rfl) ⟨759588, by rfl⟩ : syracuseStep 2025569 = 1519177) B1519177
theorem B3369113 : Blo 996598 3369113 := bstep (se 2 (by rfl) ⟨1263417, by rfl⟩ : syracuseStep 3369113 = 2526835) B2526835
theorem B10807789 : Blo 996598 10807789 := bstep (se 3 (by rfl) ⟨2026460, by rfl⟩ : syracuseStep 10807789 = 4052921) B4052921
theorem B54684193 : Blo 996598 54684193 := bstep (se 2 (by rfl) ⟨20506572, by rfl⟩ : syracuseStep 54684193 = 41013145) B41013145
theorem B3041831 : Blo 996598 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B8514233 : Blo 996598 8514233 := bstep (se 2 (by rfl) ⟨3192837, by rfl⟩ : syracuseStep 8514233 = 6385675) B6385675
theorem B11365109 : Blo 996598 11365109 := bstep (se 5 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 11365109 = 1065479) B1065479
theorem B13692077 : Blo 996598 13692077 := bstep (se 3 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 13692077 = 5134529) B5134529
theorem B3370301 : Blo 996598 3370301 := bstep (se 3 (by rfl) ⟨631931, by rfl⟩ : syracuseStep 3370301 = 1263863) B1263863
theorem B7204211 : Blo 996598 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B1600987 : Blo 996598 1600987 := bstep (se 1 (by rfl) ⟨1200740, by rfl⟩ : syracuseStep 1600987 = 2401481) B2401481
theorem B1797881 : Blo 996598 1797881 := bstep (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) B1348411
theorem B3600247 : Blo 996598 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B1601545 : Blo 996598 1601545 := bstep (se 2 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 1601545 = 1201159) B1201159
theorem B5402639 : Blo 996598 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B3371165 : Blo 996598 3371165 := bstep (se 3 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 3371165 = 1264187) B1264187
theorem B10809521 : Blo 996598 10809521 := bstep (se 2 (by rfl) ⟨4053570, by rfl⟩ : syracuseStep 10809521 = 8107141) B8107141
theorem B3797239 : Blo 996598 3797239 := bstep (se 1 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 3797239 = 5695859) B5695859
theorem B3797513 : Blo 996598 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B3797543 : Blo 996598 3797543 := bstep (se 1 (by rfl) ⟨2848157, by rfl⟩ : syracuseStep 3797543 = 5696315) B5696315
theorem B44331587 : Blo 996598 44331587 := bstep (se 1 (by rfl) ⟨33248690, by rfl⟩ : syracuseStep 44331587 = 66497381) B66497381
theorem B3371705 : Blo 996598 3371705 := bstep (se 2 (by rfl) ⟨1264389, by rfl⟩ : syracuseStep 3371705 = 2528779) B2528779
theorem B60748481 : Blo 996598 60748481 := bstep (se 2 (by rfl) ⟨22780680, by rfl⟩ : syracuseStep 60748481 = 45561361) B45561361
theorem B1897435 : Blo 996598 1897435 := bstep (se 1 (by rfl) ⟨1423076, by rfl⟩ : syracuseStep 1897435 = 2846153) B2846153
theorem B1897481 : Blo 996598 1897481 := bstep (se 2 (by rfl) ⟨711555, by rfl⟩ : syracuseStep 1897481 = 1423111) B1423111
theorem B38925461 : Blo 996598 38925461 := bstep (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) B1824631
theorem B3798211 : Blo 996598 3798211 := bstep (se 1 (by rfl) ⟨2848658, by rfl⟩ : syracuseStep 3798211 = 5697317) B5697317
theorem B3372299 : Blo 996598 3372299 := bstep (se 1 (by rfl) ⟨2529224, by rfl⟩ : syracuseStep 3372299 = 5058449) B5058449
theorem B1897823 : Blo 996598 1897823 := bstep (se 1 (by rfl) ⟨1423367, by rfl⟩ : syracuseStep 1897823 = 2846735) B2846735
theorem B19461491 : Blo 996598 19461491 := bstep (se 1 (by rfl) ⟨14596118, by rfl⟩ : syracuseStep 19461491 = 29192237) B29192237
theorem B3798515 : Blo 996598 3798515 := bstep (se 1 (by rfl) ⟨2848886, by rfl⟩ : syracuseStep 3798515 = 5697773) B5697773
theorem B3372569 : Blo 996598 3372569 := bstep (se 2 (by rfl) ⟨1264713, by rfl⟩ : syracuseStep 3372569 = 2529427) B2529427
theorem B3601979 : Blo 996598 3601979 := bstep (se 1 (by rfl) ⟨2701484, by rfl⟩ : syracuseStep 3601979 = 5402969) B5402969
theorem B5404283 : Blo 996598 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B3798971 : Blo 996598 3798971 := bstep (se 1 (by rfl) ⟨2849228, by rfl⟩ : syracuseStep 3798971 = 5698457) B5698457
theorem B9598925 : Blo 996598 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B32438663 : Blo 996598 32438663 := bstep (se 1 (by rfl) ⟨24328997, by rfl⟩ : syracuseStep 32438663 = 48657995) B48657995
theorem B1898939 : Blo 996598 1898939 := bstep (se 1 (by rfl) ⟨1424204, by rfl⟩ : syracuseStep 1898939 = 2848409) B2848409
theorem B3373703 : Blo 996598 3373703 := bstep (se 1 (by rfl) ⟨2530277, by rfl⟩ : syracuseStep 3373703 = 5060555) B5060555
theorem B3373757 : Blo 996598 3373757 := bstep (se 3 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 3373757 = 1265159) B1265159
theorem B3603143 : Blo 996598 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B3373919 : Blo 996598 3373919 := bstep (se 1 (by rfl) ⟨2530439, by rfl⟩ : syracuseStep 3373919 = 5060879) B5060879
theorem B1899425 : Blo 996598 1899425 := bstep (se 2 (by rfl) ⟨712284, by rfl⟩ : syracuseStep 1899425 = 1424569) B1424569
theorem B3374081 : Blo 996598 3374081 := bstep (se 2 (by rfl) ⟨1265280, by rfl⟩ : syracuseStep 3374081 = 2530561) B2530561
theorem B5045327 : Blo 996598 5045327 := bstep (se 1 (by rfl) ⟨3783995, by rfl⟩ : syracuseStep 5045327 = 7567991) B7567991
theorem B8519255 : Blo 996598 8519255 := bstep (se 1 (by rfl) ⟨6389441, by rfl⟩ : syracuseStep 8519255 = 12778883) B12778883
theorem B5045975 : Blo 996598 5045975 := bstep (se 1 (by rfl) ⟨3784481, by rfl⟩ : syracuseStep 5045975 = 7568963) B7568963
theorem B6487789 : Blo 996598 6487789 := bstep (se 3 (by rfl) ⟨1216460, by rfl⟩ : syracuseStep 6487789 = 2432921) B2432921
theorem B3374891 : Blo 996598 3374891 := bstep (se 1 (by rfl) ⟨2531168, by rfl⟩ : syracuseStep 3374891 = 5062337) B5062337
theorem B2130131 : Blo 996598 2130131 := bstep (se 1 (by rfl) ⟨1597598, by rfl⟩ : syracuseStep 2130131 = 3195197) B3195197
theorem B6062501 : Blo 996598 6062501 := bstep (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) B1136719
theorem B2523575 : Blo 996598 2523575 := bstep (se 1 (by rfl) ⟨1892681, by rfl⟩ : syracuseStep 2523575 = 3785363) B3785363
theorem B5046785 : Blo 996598 5046785 := bstep (se 2 (by rfl) ⟨1892544, by rfl⟩ : syracuseStep 5046785 = 3785089) B3785089
theorem B4555487 : Blo 996598 4555487 := bstep (se 1 (by rfl) ⟨3416615, by rfl⟩ : syracuseStep 4555487 = 6833231) B6833231
theorem B5047271 : Blo 996598 5047271 := bstep (se 1 (by rfl) ⟨3785453, by rfl⟩ : syracuseStep 5047271 = 7570907) B7570907
theorem B5047595 : Blo 996598 5047595 := bstep (se 1 (by rfl) ⟨3785696, by rfl⟩ : syracuseStep 5047595 = 7571393) B7571393
theorem B2524679 : Blo 996598 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B2524729 : Blo 996598 2524729 := bstep (se 2 (by rfl) ⟨946773, by rfl⟩ : syracuseStep 2524729 = 1893547) B1893547
theorem B1443625 : Blo 996598 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B2525033 : Blo 996598 2525033 := bstep (se 2 (by rfl) ⟨946887, by rfl⟩ : syracuseStep 2525033 = 1893775) B1893775
theorem B17303537 : Blo 996598 17303537 := bstep (se 2 (by rfl) ⟨6488826, by rfl⟩ : syracuseStep 17303537 = 12977653) B12977653
theorem B5048567 : Blo 996598 5048567 := bstep (se 1 (by rfl) ⟨3786425, by rfl⟩ : syracuseStep 5048567 = 7572851) B7572851
theorem B7571879 : Blo 996598 7571879 := bstep (se 1 (by rfl) ⟨5678909, by rfl⟩ : syracuseStep 7571879 = 11357819) B11357819
theorem B2165159 : Blo 996598 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B8653229 : Blo 996598 8653229 := bstep (se 3 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 8653229 = 3244961) B3244961
theorem B4262327 : Blo 996598 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B2525651 : Blo 996598 2525651 := bstep (se 1 (by rfl) ⟨1894238, by rfl⟩ : syracuseStep 2525651 = 3788477) B3788477
theorem B4262395 : Blo 996598 4262395 := bstep (se 1 (by rfl) ⟨3196796, by rfl⟩ : syracuseStep 4262395 = 6393593) B6393593
theorem B5049053 : Blo 996598 5049053 := bstep (se 3 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 5049053 = 1893395) B1893395
theorem B2395099 : Blo 996598 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B2395175 : Blo 996598 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B6065371 : Blo 996598 6065371 := bstep (se 1 (by rfl) ⟨4549028, by rfl⟩ : syracuseStep 6065371 = 9098057) B9098057
theorem B4263131 : Blo 996598 4263131 := bstep (se 1 (by rfl) ⟨3197348, by rfl⟩ : syracuseStep 4263131 = 6394697) B6394697
theorem B72912257 : Blo 996598 72912257 := bstep (se 2 (by rfl) ⟨27342096, by rfl⟩ : syracuseStep 72912257 = 54684193) B54684193
theorem B2526815 : Blo 996598 2526815 := bstep (se 1 (by rfl) ⟨1895111, by rfl⟩ : syracuseStep 2526815 = 3790223) B3790223
theorem B14421797 : Blo 996598 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B8523629 : Blo 996598 8523629 := bstep (se 3 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 8523629 = 3196361) B3196361
theorem B2527595 : Blo 996598 2527595 := bstep (se 1 (by rfl) ⟨1895696, by rfl⟩ : syracuseStep 2527595 = 3791393) B3791393
theorem B2527807 : Blo 996598 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B2134649 : Blo 996598 2134649 := bstep (se 2 (by rfl) ⟨800493, by rfl⟩ : syracuseStep 2134649 = 1600987) B1600987
theorem B14389913 : Blo 996598 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B2527919 : Blo 996598 2527919 := bstep (se 1 (by rfl) ⟨1895939, by rfl⟩ : syracuseStep 2527919 = 3791879) B3791879
theorem B2528243 : Blo 996598 2528243 := bstep (se 1 (by rfl) ⟨1896182, by rfl⟩ : syracuseStep 2528243 = 3792365) B3792365
theorem B14423129 : Blo 996598 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B2528455 : Blo 996598 2528455 := bstep (se 1 (by rfl) ⟨1896341, by rfl⟩ : syracuseStep 2528455 = 3792683) B3792683
theorem B2135393 : Blo 996598 2135393 := bstep (se 2 (by rfl) ⟨800772, by rfl⟩ : syracuseStep 2135393 = 1601545) B1601545
theorem B6166201 : Blo 996598 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B4266017 : Blo 996598 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B2529863 : Blo 996598 2529863 := bstep (se 1 (by rfl) ⟨1897397, by rfl⟩ : syracuseStep 2529863 = 3794795) B3794795
theorem B1645127 : Blo 996598 1645127 := bstep (se 1 (by rfl) ⟨1233845, by rfl⟩ : syracuseStep 1645127 = 2467691) B2467691
theorem B2529913 : Blo 996598 2529913 := bstep (se 2 (by rfl) ⟨948717, by rfl⟩ : syracuseStep 2529913 = 1897435) B1897435
theorem B5053103 : Blo 996598 5053103 := bstep (se 1 (by rfl) ⟨3789827, by rfl⟩ : syracuseStep 5053103 = 7579655) B7579655
theorem B2398943 : Blo 996598 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B1350379 : Blo 996598 1350379 := bstep (se 1 (by rfl) ⟨1012784, by rfl⟩ : syracuseStep 1350379 = 2025569) B2025569
theorem B1121179 : Blo 996598 1121179 := bstep (se 1 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 1121179 = 1681769) B1681769
theorem B5053427 : Blo 996598 5053427 := bstep (se 1 (by rfl) ⟨3790070, by rfl⟩ : syracuseStep 5053427 = 7580141) B7580141
theorem B5479505 : Blo 996598 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B5676155 : Blo 996598 5676155 := bstep (se 1 (by rfl) ⟨4257116, by rfl⟩ : syracuseStep 5676155 = 8514233) B8514233
theorem B7576739 : Blo 996598 7576739 := bstep (se 1 (by rfl) ⟨5682554, by rfl⟩ : syracuseStep 7576739 = 11365109) B11365109
theorem B9608381 : Blo 996598 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B6397157 : Blo 996598 6397157 := bstep (se 4 (by rfl) ⟨599733, by rfl⟩ : syracuseStep 6397157 = 1199467) B1199467
theorem B1121575 : Blo 996598 1121575 := bstep (se 1 (by rfl) ⟨841181, by rfl⟩ : syracuseStep 1121575 = 1682363) B1682363
theorem B1121647 : Blo 996598 1121647 := bstep (se 1 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 1121647 = 1682471) B1682471
theorem B1121863 : Blo 996598 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B4792121 : Blo 996598 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B21569651 : Blo 996598 21569651 := bstep (se 1 (by rfl) ⟨16177238, by rfl⟩ : syracuseStep 21569651 = 32354477) B32354477
theorem B2433235 : Blo 996598 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B5054723 : Blo 996598 5054723 := bstep (se 1 (by rfl) ⟨3791042, by rfl⟩ : syracuseStep 5054723 = 7582085) B7582085
theorem B2531675 : Blo 996598 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B2531695 : Blo 996598 2531695 := bstep (se 1 (by rfl) ⟨1898771, by rfl⟩ : syracuseStep 2531695 = 3797543) B3797543
theorem B1122727 : Blo 996598 1122727 := bstep (se 1 (by rfl) ⟨842045, by rfl⟩ : syracuseStep 1122727 = 1684091) B1684091
theorem B5055047 : Blo 996598 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B1123303 : Blo 996598 1123303 := bstep (se 1 (by rfl) ⟨842477, by rfl⟩ : syracuseStep 1123303 = 1684955) B1684955
theorem B2532343 : Blo 996598 2532343 := bstep (se 1 (by rfl) ⟨1899257, by rfl⟩ : syracuseStep 2532343 = 3798515) B3798515
theorem B69215269 : Blo 996598 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B2401319 : Blo 996598 2401319 := bstep (se 1 (by rfl) ⟨1800989, by rfl⟩ : syracuseStep 2401319 = 3601979) B3601979
theorem B2532647 : Blo 996598 2532647 := bstep (se 1 (by rfl) ⟨1899485, by rfl⟩ : syracuseStep 2532647 = 3798971) B3798971
theorem B6399283 : Blo 996598 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B7579169 : Blo 996598 7579169 := bstep (se 2 (by rfl) ⟨2842188, by rfl⟩ : syracuseStep 7579169 = 5684377) B5684377
theorem B4794041 : Blo 996598 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B5056343 : Blo 996598 5056343 := bstep (se 1 (by rfl) ⟨3792257, by rfl⟩ : syracuseStep 5056343 = 7584515) B7584515
theorem B4794349 : Blo 996598 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B7678147 : Blo 996598 7678147 := bstep (se 1 (by rfl) ⟨5758610, by rfl⟩ : syracuseStep 7678147 = 11517221) B11517221
theorem B5679503 : Blo 996598 5679503 := bstep (se 1 (by rfl) ⟨4259627, by rfl⟩ : syracuseStep 5679503 = 8519255) B8519255
theorem B1124959 : Blo 996598 1124959 := bstep (se 1 (by rfl) ⟨843719, by rfl⟩ : syracuseStep 1124959 = 1687439) B1687439
theorem B1682255 : Blo 996598 1682255 := bstep (se 1 (by rfl) ⟨1261691, by rfl⟩ : syracuseStep 1682255 = 2523383) B2523383
theorem B4271143 : Blo 996598 4271143 := bstep (se 1 (by rfl) ⟨3203357, by rfl⟩ : syracuseStep 4271143 = 6406715) B6406715
theorem B5123359 : Blo 996598 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B4271879 : Blo 996598 4271879 := bstep (se 1 (by rfl) ⟨3203909, by rfl⟩ : syracuseStep 4271879 = 6407819) B6407819
theorem B1683247 : Blo 996598 1683247 := bstep (se 1 (by rfl) ⟨1262435, by rfl⟩ : syracuseStep 1683247 = 2524871) B2524871
theorem B2273129 : Blo 996598 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B4796425 : Blo 996598 4796425 := bstep (se 2 (by rfl) ⟨1798659, by rfl⟩ : syracuseStep 4796425 = 3597319) B3597319
theorem B5058611 : Blo 996598 5058611 := bstep (se 1 (by rfl) ⟨3793958, by rfl⟩ : syracuseStep 5058611 = 7587917) B7587917
theorem B2699849 : Blo 996598 2699849 := bstep (se 2 (by rfl) ⟨1012443, by rfl⟩ : syracuseStep 2699849 = 2024887) B2024887
theorem B20460595 : Blo 996598 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B996639 : Blo 996598 996639 := bstep (se 1 (by rfl) ⟨747479, by rfl⟩ : syracuseStep 996639 = 1494959) B1494959
theorem B996699 : Blo 996598 996699 := bstep (se 1 (by rfl) ⟨747524, by rfl⟩ : syracuseStep 996699 = 1495049) B1495049
theorem B996719 : Blo 996598 996719 := bstep (se 1 (by rfl) ⟨747539, by rfl⟩ : syracuseStep 996719 = 1495079) B1495079
theorem B996775 : Blo 996598 996775 := bstep (se 1 (by rfl) ⟨747581, by rfl⟩ : syracuseStep 996775 = 1495163) B1495163
theorem B996859 : Blo 996598 996859 := bstep (se 1 (by rfl) ⟨747644, by rfl⟩ : syracuseStep 996859 = 1495289) B1495289
theorem B996927 : Blo 996598 996927 := bstep (se 1 (by rfl) ⟨747695, by rfl⟩ : syracuseStep 996927 = 1495391) B1495391
theorem B996935 : Blo 996598 996935 := bstep (se 1 (by rfl) ⟨747701, by rfl⟩ : syracuseStep 996935 = 1495403) B1495403
theorem B5060231 : Blo 996598 5060231 := bstep (se 1 (by rfl) ⟨3795173, by rfl⟩ : syracuseStep 5060231 = 7590347) B7590347
theorem B997087 : Blo 996598 997087 := bstep (se 1 (by rfl) ⟨747815, by rfl⟩ : syracuseStep 997087 = 1495631) B1495631
theorem B997167 : Blo 996598 997167 := bstep (se 1 (by rfl) ⟨747875, by rfl⟩ : syracuseStep 997167 = 1495751) B1495751
theorem B7583543 : Blo 996598 7583543 := bstep (se 1 (by rfl) ⟨5687657, by rfl⟩ : syracuseStep 7583543 = 11375315) B11375315
theorem B997275 : Blo 996598 997275 := bstep (se 1 (by rfl) ⟨747956, by rfl⟩ : syracuseStep 997275 = 1495913) B1495913
theorem B2242511 : Blo 996598 2242511 := bstep (se 1 (by rfl) ⟨1681883, by rfl⟩ : syracuseStep 2242511 = 3363767) B3363767
theorem B997327 : Blo 996598 997327 := bstep (se 1 (by rfl) ⟨747995, by rfl⟩ : syracuseStep 997327 = 1495991) B1495991
theorem B997351 : Blo 996598 997351 := bstep (se 1 (by rfl) ⟨748013, by rfl⟩ : syracuseStep 997351 = 1496027) B1496027
theorem B6404129 : Blo 996598 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B997663 : Blo 996598 997663 := bstep (se 1 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 997663 = 1496495) B1496495
theorem B2242889 : Blo 996598 2242889 := bstep (se 2 (by rfl) ⟨841083, by rfl⟩ : syracuseStep 2242889 = 1682167) B1682167
theorem B2242907 : Blo 996598 2242907 := bstep (se 1 (by rfl) ⟨1682180, by rfl⟩ : syracuseStep 2242907 = 3364361) B3364361
theorem B997723 : Blo 996598 997723 := bstep (se 1 (by rfl) ⟨748292, by rfl⟩ : syracuseStep 997723 = 1496585) B1496585
theorem B997743 : Blo 996598 997743 := bstep (se 1 (by rfl) ⟨748307, by rfl⟩ : syracuseStep 997743 = 1496615) B1496615
theorem B997799 : Blo 996598 997799 := bstep (se 1 (by rfl) ⟨748349, by rfl⟩ : syracuseStep 997799 = 1496699) B1496699
theorem B1685927 : Blo 996598 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B997883 : Blo 996598 997883 := bstep (se 1 (by rfl) ⟨748412, by rfl⟩ : syracuseStep 997883 = 1496825) B1496825
theorem B997951 : Blo 996598 997951 := bstep (se 1 (by rfl) ⟨748463, by rfl⟩ : syracuseStep 997951 = 1496927) B1496927
theorem B997959 : Blo 996598 997959 := bstep (se 1 (by rfl) ⟨748469, by rfl⟩ : syracuseStep 997959 = 1496939) B1496939
theorem B1686089 : Blo 996598 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B998111 : Blo 996598 998111 := bstep (se 1 (by rfl) ⟨748583, by rfl⟩ : syracuseStep 998111 = 1497167) B1497167
theorem B2702099 : Blo 996598 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B998191 : Blo 996598 998191 := bstep (se 1 (by rfl) ⟨748643, by rfl⟩ : syracuseStep 998191 = 1497287) B1497287
theorem B4635535 : Blo 996598 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B2243483 : Blo 996598 2243483 := bstep (se 1 (by rfl) ⟨1682612, by rfl⟩ : syracuseStep 2243483 = 3365225) B3365225
theorem B998299 : Blo 996598 998299 := bstep (se 1 (by rfl) ⟨748724, by rfl⟩ : syracuseStep 998299 = 1497449) B1497449
theorem B998351 : Blo 996598 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B998375 : Blo 996598 998375 := bstep (se 1 (by rfl) ⟨748781, by rfl⟩ : syracuseStep 998375 = 1497563) B1497563
theorem B2243681 : Blo 996598 2243681 := bstep (se 2 (by rfl) ⟨841380, by rfl⟩ : syracuseStep 2243681 = 1682761) B1682761
theorem B5061851 : Blo 996598 5061851 := bstep (se 1 (by rfl) ⟨3796388, by rfl⟩ : syracuseStep 5061851 = 7592777) B7592777
theorem B998687 : Blo 996598 998687 := bstep (se 1 (by rfl) ⟨749015, by rfl⟩ : syracuseStep 998687 = 1498031) B1498031
theorem B2243879 : Blo 996598 2243879 := bstep (se 1 (by rfl) ⟨1682909, by rfl⟩ : syracuseStep 2243879 = 3365819) B3365819
theorem B998747 : Blo 996598 998747 := bstep (se 1 (by rfl) ⟨749060, by rfl⟩ : syracuseStep 998747 = 1498121) B1498121
theorem B998767 : Blo 996598 998767 := bstep (se 1 (by rfl) ⟨749075, by rfl⟩ : syracuseStep 998767 = 1498151) B1498151
theorem B998823 : Blo 996598 998823 := bstep (se 1 (by rfl) ⟨749117, by rfl⟩ : syracuseStep 998823 = 1498235) B1498235
theorem B3194311 : Blo 996598 3194311 := bstep (se 1 (by rfl) ⟨2395733, by rfl⟩ : syracuseStep 3194311 = 4791467) B4791467
theorem B998907 : Blo 996598 998907 := bstep (se 1 (by rfl) ⟨749180, by rfl⟩ : syracuseStep 998907 = 1498361) B1498361
theorem B998975 : Blo 996598 998975 := bstep (se 1 (by rfl) ⟨749231, by rfl⟩ : syracuseStep 998975 = 1498463) B1498463
theorem B998983 : Blo 996598 998983 := bstep (se 1 (by rfl) ⟨749237, by rfl⟩ : syracuseStep 998983 = 1498475) B1498475
theorem B10796627 : Blo 996598 10796627 := bstep (se 1 (by rfl) ⟨8097470, by rfl⟩ : syracuseStep 10796627 = 16194941) B16194941
theorem B1687135 : Blo 996598 1687135 := bstep (se 1 (by rfl) ⟨1265351, by rfl⟩ : syracuseStep 1687135 = 2530703) B2530703
theorem B2244257 : Blo 996598 2244257 := bstep (se 2 (by rfl) ⟨841596, by rfl⟩ : syracuseStep 2244257 = 1683193) B1683193
theorem B999135 : Blo 996598 999135 := bstep (se 1 (by rfl) ⟨749351, by rfl⟩ : syracuseStep 999135 = 1498703) B1498703
theorem B999215 : Blo 996598 999215 := bstep (se 1 (by rfl) ⟨749411, by rfl⟩ : syracuseStep 999215 = 1498823) B1498823
theorem B1687351 : Blo 996598 1687351 := bstep (se 1 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 1687351 = 2531027) B2531027
theorem B4800329 : Blo 996598 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B999323 : Blo 996598 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B10796975 : Blo 996598 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B999375 : Blo 996598 999375 := bstep (se 1 (by rfl) ⟨749531, by rfl⟩ : syracuseStep 999375 = 1499063) B1499063
theorem B999399 : Blo 996598 999399 := bstep (se 1 (by rfl) ⟨749549, by rfl⟩ : syracuseStep 999399 = 1499099) B1499099
theorem B2244617 : Blo 996598 2244617 := bstep (se 2 (by rfl) ⟨841731, by rfl⟩ : syracuseStep 2244617 = 1683463) B1683463
theorem B1687817 : Blo 996598 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B999711 : Blo 996598 999711 := bstep (se 1 (by rfl) ⟨749783, by rfl⟩ : syracuseStep 999711 = 1499567) B1499567
theorem B5062985 : Blo 996598 5062985 := bstep (se 2 (by rfl) ⟨1898619, by rfl⟩ : syracuseStep 5062985 = 3797239) B3797239
theorem B999771 : Blo 996598 999771 := bstep (se 1 (by rfl) ⟨749828, by rfl⟩ : syracuseStep 999771 = 1499657) B1499657
theorem B999791 : Blo 996598 999791 := bstep (se 1 (by rfl) ⟨749843, by rfl⟩ : syracuseStep 999791 = 1499687) B1499687
theorem B2245031 : Blo 996598 2245031 := bstep (se 1 (by rfl) ⟨1683773, by rfl⟩ : syracuseStep 2245031 = 3367547) B3367547
theorem B999847 : Blo 996598 999847 := bstep (se 1 (by rfl) ⟨749885, by rfl⟩ : syracuseStep 999847 = 1499771) B1499771
theorem B999931 : Blo 996598 999931 := bstep (se 1 (by rfl) ⟨749948, by rfl⟩ : syracuseStep 999931 = 1499897) B1499897
theorem B2245139 : Blo 996598 2245139 := bstep (se 1 (by rfl) ⟨1683854, by rfl⟩ : syracuseStep 2245139 = 3367709) B3367709
theorem B999999 : Blo 996598 999999 := bstep (se 1 (by rfl) ⟨749999, by rfl⟩ : syracuseStep 999999 = 1499999) B1499999
theorem B1000007 : Blo 996598 1000007 := bstep (se 1 (by rfl) ⟨750005, by rfl⟩ : syracuseStep 1000007 = 1500011) B1500011
theorem B2245193 : Blo 996598 2245193 := bstep (se 2 (by rfl) ⟨841947, by rfl⟩ : syracuseStep 2245193 = 1683895) B1683895
theorem B1000159 : Blo 996598 1000159 := bstep (se 1 (by rfl) ⟨750119, by rfl⟩ : syracuseStep 1000159 = 1500239) B1500239
theorem B1000239 : Blo 996598 1000239 := bstep (se 1 (by rfl) ⟨750179, by rfl⟩ : syracuseStep 1000239 = 1500359) B1500359
theorem B1000347 : Blo 996598 1000347 := bstep (se 1 (by rfl) ⟨750260, by rfl⟩ : syracuseStep 1000347 = 1500521) B1500521
theorem B5129153 : Blo 996598 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B1000399 : Blo 996598 1000399 := bstep (se 1 (by rfl) ⟨750299, by rfl⟩ : syracuseStep 1000399 = 1500599) B1500599
theorem B1262567 : Blo 996598 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B2245607 : Blo 996598 2245607 := bstep (se 1 (by rfl) ⟨1684205, by rfl⟩ : syracuseStep 2245607 = 3368411) B3368411
theorem B1000423 : Blo 996598 1000423 := bstep (se 1 (by rfl) ⟨750317, by rfl⟩ : syracuseStep 1000423 = 1500635) B1500635
theorem B2245985 : Blo 996598 2245985 := bstep (se 2 (by rfl) ⟨842244, by rfl⟩ : syracuseStep 2245985 = 1684489) B1684489
theorem B2246075 : Blo 996598 2246075 := bstep (se 1 (by rfl) ⟨1684556, by rfl⟩ : syracuseStep 2246075 = 3369113) B3369113
theorem B8111549 : Blo 996598 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B2246201 : Blo 996598 2246201 := bstep (se 2 (by rfl) ⟨842325, by rfl⟩ : syracuseStep 2246201 = 1684651) B1684651
theorem B5064281 : Blo 996598 5064281 := bstep (se 2 (by rfl) ⟨1899105, by rfl⟩ : syracuseStep 5064281 = 3798211) B3798211
theorem B414566423 : Blo 996598 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B9128051 : Blo 996598 9128051 := bstep (se 1 (by rfl) ⟨6846038, by rfl⟩ : syracuseStep 9128051 = 13692077) B13692077
theorem B2246867 : Blo 996598 2246867 := bstep (se 1 (by rfl) ⟨1685150, by rfl⟩ : syracuseStep 2246867 = 3370301) B3370301
theorem B4802807 : Blo 996598 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B2246921 : Blo 996598 2246921 := bstep (se 2 (by rfl) ⟨842595, by rfl⟩ : syracuseStep 2246921 = 1685191) B1685191
theorem B3787033 : Blo 996598 3787033 := bstep (se 2 (by rfl) ⟨1420137, by rfl⟩ : syracuseStep 3787033 = 2840275) B2840275
theorem B2247137 : Blo 996598 2247137 := bstep (se 2 (by rfl) ⟨842676, by rfl⟩ : syracuseStep 2247137 = 1685353) B1685353
theorem B2738657 : Blo 996598 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B3787337 : Blo 996598 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B2247443 : Blo 996598 2247443 := bstep (se 1 (by rfl) ⟨1685582, by rfl⟩ : syracuseStep 2247443 = 3371165) B3371165
theorem B14404675 : Blo 996598 14404675 := bstep (se 1 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 14404675 = 21607013) B21607013
theorem B2247803 : Blo 996598 2247803 := bstep (se 1 (by rfl) ⟨1685852, by rfl⟩ : syracuseStep 2247803 = 3371705) B3371705
theorem B2247929 : Blo 996598 2247929 := bstep (se 2 (by rfl) ⟨842973, by rfl⟩ : syracuseStep 2247929 = 1685947) B1685947
theorem B1264987 : Blo 996598 1264987 := bstep (se 1 (by rfl) ⟨948740, by rfl⟩ : syracuseStep 1264987 = 1897481) B1897481
theorem B2248073 : Blo 996598 2248073 := bstep (se 2 (by rfl) ⟨843027, by rfl⟩ : syracuseStep 2248073 = 1686055) B1686055
theorem B2248199 : Blo 996598 2248199 := bstep (se 1 (by rfl) ⟨1686149, by rfl⟩ : syracuseStep 2248199 = 3372299) B3372299
theorem B1265215 : Blo 996598 1265215 := bstep (se 1 (by rfl) ⟨948911, by rfl⟩ : syracuseStep 1265215 = 1897823) B1897823
theorem B2248379 : Blo 996598 2248379 := bstep (se 1 (by rfl) ⟨1686284, by rfl⟩ : syracuseStep 2248379 = 3372569) B3372569
theorem B2248505 : Blo 996598 2248505 := bstep (se 2 (by rfl) ⟨843189, by rfl⟩ : syracuseStep 2248505 = 1686379) B1686379
theorem B1495145 : Blo 996598 1495145 := bstep (se 2 (by rfl) ⟨560679, by rfl⟩ : syracuseStep 1495145 = 1121359) B1121359
theorem B1265959 : Blo 996598 1265959 := bstep (se 1 (by rfl) ⟨949469, by rfl⟩ : syracuseStep 1265959 = 1898939) B1898939
theorem B1495463 : Blo 996598 1495463 := bstep (se 1 (by rfl) ⟨1121597, by rfl⟩ : syracuseStep 1495463 = 2243195) B2243195
theorem B2249135 : Blo 996598 2249135 := bstep (se 1 (by rfl) ⟨1686851, by rfl⟩ : syracuseStep 2249135 = 3373703) B3373703
theorem B2249171 : Blo 996598 2249171 := bstep (se 1 (by rfl) ⟨1686878, by rfl⟩ : syracuseStep 2249171 = 3373757) B3373757
theorem B3789281 : Blo 996598 3789281 := bstep (se 2 (by rfl) ⟨1420980, by rfl⟩ : syracuseStep 3789281 = 2841961) B2841961
theorem B1495547 : Blo 996598 1495547 := bstep (se 1 (by rfl) ⟨1121660, by rfl⟩ : syracuseStep 1495547 = 2243321) B2243321
theorem B2249279 : Blo 996598 2249279 := bstep (se 1 (by rfl) ⟨1686959, by rfl⟩ : syracuseStep 2249279 = 3373919) B3373919
theorem B1266283 : Blo 996598 1266283 := bstep (se 1 (by rfl) ⟨949712, by rfl⟩ : syracuseStep 1266283 = 1899425) B1899425
theorem B1495673 : Blo 996598 1495673 := bstep (se 2 (by rfl) ⟨560877, by rfl⟩ : syracuseStep 1495673 = 1121755) B1121755
theorem B2249387 : Blo 996598 2249387 := bstep (se 1 (by rfl) ⟨1687040, by rfl⟩ : syracuseStep 2249387 = 3374081) B3374081
theorem B1495727 : Blo 996598 1495727 := bstep (se 1 (by rfl) ⟨1121795, by rfl⟩ : syracuseStep 1495727 = 2243591) B2243591
theorem B3363551 : Blo 996598 3363551 := bstep (se 1 (by rfl) ⟨2522663, by rfl⟩ : syracuseStep 3363551 = 5045327) B5045327
theorem B1495775 : Blo 996598 1495775 := bstep (se 1 (by rfl) ⟨1121831, by rfl⟩ : syracuseStep 1495775 = 2243663) B2243663
theorem B7197407 : Blo 996598 7197407 := bstep (se 1 (by rfl) ⟨5398055, by rfl⟩ : syracuseStep 7197407 = 10796111) B10796111
theorem B1496039 : Blo 996598 1496039 := bstep (se 1 (by rfl) ⟨1122029, by rfl⟩ : syracuseStep 1496039 = 2244059) B2244059
theorem B3789949 : Blo 996598 3789949 := bstep (se 3 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 3789949 = 1421231) B1421231
theorem B3363983 : Blo 996598 3363983 := bstep (se 1 (by rfl) ⟨2522987, by rfl⟩ : syracuseStep 3363983 = 5045975) B5045975
theorem B2249927 : Blo 996598 2249927 := bstep (se 1 (by rfl) ⟨1687445, by rfl⟩ : syracuseStep 2249927 = 3374891) B3374891
theorem B1496297 : Blo 996598 1496297 := bstep (se 2 (by rfl) ⟨561111, by rfl⟩ : syracuseStep 1496297 = 1122223) B1122223
theorem B1496351 : Blo 996598 1496351 := bstep (se 1 (by rfl) ⟨1122263, by rfl⟩ : syracuseStep 1496351 = 2244527) B2244527
theorem B2250107 : Blo 996598 2250107 := bstep (se 1 (by rfl) ⟨1687580, by rfl⟩ : syracuseStep 2250107 = 3375161) B3375161
theorem B1496519 : Blo 996598 1496519 := bstep (se 1 (by rfl) ⟨1122389, by rfl⟩ : syracuseStep 1496519 = 2244779) B2244779
theorem B2250233 : Blo 996598 2250233 := bstep (se 2 (by rfl) ⟨843837, by rfl⟩ : syracuseStep 2250233 = 1687675) B1687675
theorem B2250323 : Blo 996598 2250323 := bstep (se 1 (by rfl) ⟨1687742, by rfl⟩ : syracuseStep 2250323 = 3375485) B3375485
theorem B2250503 : Blo 996598 2250503 := bstep (se 1 (by rfl) ⟨1687877, by rfl⟩ : syracuseStep 2250503 = 3375755) B3375755
theorem B1496873 : Blo 996598 1496873 := bstep (se 2 (by rfl) ⟨561327, by rfl⟩ : syracuseStep 1496873 = 1122655) B1122655
theorem B1496879 : Blo 996598 1496879 := bstep (se 1 (by rfl) ⟨1122659, by rfl⟩ : syracuseStep 1496879 = 2245319) B2245319
theorem B3365117 : Blo 996598 3365117 := bstep (se 3 (by rfl) ⟨630959, by rfl⟩ : syracuseStep 3365117 = 1261919) B1261919
theorem B1497353 : Blo 996598 1497353 := bstep (se 2 (by rfl) ⟨561507, by rfl⟩ : syracuseStep 1497353 = 1123015) B1123015
theorem B2251115 : Blo 996598 2251115 := bstep (se 1 (by rfl) ⟨1688336, by rfl⟩ : syracuseStep 2251115 = 3376673) B3376673
theorem B1497455 : Blo 996598 1497455 := bstep (se 1 (by rfl) ⟨1123091, by rfl⟩ : syracuseStep 1497455 = 2246183) B2246183
theorem B2251259 : Blo 996598 2251259 := bstep (se 1 (by rfl) ⟨1688444, by rfl⟩ : syracuseStep 2251259 = 3376889) B3376889
theorem B157866565 : Blo 996598 157866565 := bstep (se 4 (by rfl) ⟨14799990, by rfl⟩ : syracuseStep 157866565 = 29599981) B29599981
theorem B1497671 : Blo 996598 1497671 := bstep (se 1 (by rfl) ⟨1123253, by rfl⟩ : syracuseStep 1497671 = 2246507) B2246507
theorem B1497707 : Blo 996598 1497707 := bstep (se 1 (by rfl) ⟨1123280, by rfl⟩ : syracuseStep 1497707 = 2246561) B2246561
theorem B4315771 : Blo 996598 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B1497935 : Blo 996598 1497935 := bstep (se 1 (by rfl) ⟨1123451, by rfl⟩ : syracuseStep 1497935 = 2246903) B2246903
theorem B1203023 : Blo 996598 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B5462939 : Blo 996598 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B3365927 : Blo 996598 3365927 := bstep (se 1 (by rfl) ⟨2524445, by rfl⟩ : syracuseStep 3365927 = 5048891) B5048891
theorem B3464315 : Blo 996598 3464315 := bstep (se 1 (by rfl) ⟨2598236, by rfl⟩ : syracuseStep 3464315 = 5196473) B5196473
theorem B1498331 : Blo 996598 1498331 := bstep (se 1 (by rfl) ⟨1123748, by rfl⟩ : syracuseStep 1498331 = 2247497) B2247497
theorem B5201117 : Blo 996598 5201117 := bstep (se 3 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 5201117 = 1950419) B1950419
theorem B11394269 : Blo 996598 11394269 := bstep (se 3 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 11394269 = 4272851) B4272851
theorem B28761479 : Blo 996598 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1498505 : Blo 996598 1498505 := bstep (se 2 (by rfl) ⟨561939, by rfl⟩ : syracuseStep 1498505 = 1123879) B1123879
theorem B1138087 : Blo 996598 1138087 := bstep (se 1 (by rfl) ⟨853565, by rfl⟩ : syracuseStep 1138087 = 1707131) B1707131
theorem B3366359 : Blo 996598 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B5692943 : Blo 996598 5692943 := bstep (se 1 (by rfl) ⟨4269707, by rfl⟩ : syracuseStep 5692943 = 8539415) B8539415
theorem B10247795 : Blo 996598 10247795 := bstep (se 1 (by rfl) ⟨7685846, by rfl⟩ : syracuseStep 10247795 = 15371693) B15371693
theorem B1498859 : Blo 996598 1498859 := bstep (se 1 (by rfl) ⟨1124144, by rfl⟩ : syracuseStep 1498859 = 2248289) B2248289
theorem B9723655 : Blo 996598 9723655 := bstep (se 1 (by rfl) ⟨7292741, by rfl⟩ : syracuseStep 9723655 = 14585483) B14585483
theorem B3039133 : Blo 996598 3039133 := bstep (se 3 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 3039133 = 1139675) B1139675
theorem B24338339 : Blo 996598 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B1499087 : Blo 996598 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B5693651 : Blo 996598 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1499483 : Blo 996598 1499483 := bstep (se 1 (by rfl) ⟨1124612, by rfl⟩ : syracuseStep 1499483 = 2249225) B2249225
theorem B1499711 : Blo 996598 1499711 := bstep (se 1 (by rfl) ⟨1124783, by rfl⟩ : syracuseStep 1499711 = 2249567) B2249567
theorem B1598059 : Blo 996598 1598059 := bstep (se 1 (by rfl) ⟨1198544, by rfl⟩ : syracuseStep 1598059 = 2397089) B2397089
theorem B3203705 : Blo 996598 3203705 := bstep (se 2 (by rfl) ⟨1201389, by rfl⟩ : syracuseStep 3203705 = 2402779) B2402779
theorem B13656721 : Blo 996598 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B14410385 : Blo 996598 14410385 := bstep (se 2 (by rfl) ⟨5403894, by rfl⟩ : syracuseStep 14410385 = 10807789) B10807789
theorem B1499831 : Blo 996598 1499831 := bstep (se 1 (by rfl) ⟨1124873, by rfl⟩ : syracuseStep 1499831 = 2249747) B2249747
theorem B1500059 : Blo 996598 1500059 := bstep (se 1 (by rfl) ⟨1125044, by rfl⟩ : syracuseStep 1500059 = 2250089) B2250089
theorem B5694401 : Blo 996598 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B3368033 : Blo 996598 3368033 := bstep (se 2 (by rfl) ⟨1263012, by rfl⟩ : syracuseStep 3368033 = 2526025) B2526025
theorem B7595207 : Blo 996598 7595207 := bstep (se 1 (by rfl) ⟨5696405, by rfl⟩ : syracuseStep 7595207 = 11392811) B11392811
theorem B4056263 : Blo 996598 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B1500455 : Blo 996598 1500455 := bstep (se 1 (by rfl) ⟨1125341, by rfl⟩ : syracuseStep 1500455 = 2250683) B2250683
theorem B1500539 : Blo 996598 1500539 := bstep (se 1 (by rfl) ⟨1125404, by rfl⟩ : syracuseStep 1500539 = 2250809) B2250809
theorem B1893881 : Blo 996598 1893881 := bstep (se 2 (by rfl) ⟨710205, by rfl⟩ : syracuseStep 1893881 = 1420411) B1420411
theorem B1500665 : Blo 996598 1500665 := bstep (se 2 (by rfl) ⟨562749, by rfl⟩ : syracuseStep 1500665 = 1125499) B1125499
theorem B1500767 : Blo 996598 1500767 := bstep (se 1 (by rfl) ⟨1125575, by rfl⟩ : syracuseStep 1500767 = 2251151) B2251151
theorem B1599239 : Blo 996598 1599239 := bstep (se 1 (by rfl) ⟨1199429, by rfl⟩ : syracuseStep 1599239 = 2398859) B2398859
theorem B17328421 : Blo 996598 17328421 := bstep (se 4 (by rfl) ⟨1624539, by rfl⟩ : syracuseStep 17328421 = 3249079) B3249079
theorem B1894747 : Blo 996598 1894747 := bstep (se 1 (by rfl) ⟨1421060, by rfl⟩ : syracuseStep 1894747 = 2842121) B2842121
theorem B1894823 : Blo 996598 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B3369383 : Blo 996598 3369383 := bstep (se 1 (by rfl) ⟨2527037, by rfl⟩ : syracuseStep 3369383 = 5054075) B5054075
theorem B1894907 : Blo 996598 1894907 := bstep (se 1 (by rfl) ⟨1421180, by rfl⟩ : syracuseStep 1894907 = 2842361) B2842361
theorem B3369545 : Blo 996598 3369545 := bstep (se 2 (by rfl) ⟨1263579, by rfl⟩ : syracuseStep 3369545 = 2527159) B2527159
theorem B14969731 : Blo 996598 14969731 := bstep (se 1 (by rfl) ⟨11227298, by rfl⟩ : syracuseStep 14969731 = 22454597) B22454597
theorem B1895339 : Blo 996598 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B1895719 : Blo 996598 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B1895879 : Blo 996598 1895879 := bstep (se 1 (by rfl) ⟨1421909, by rfl⟩ : syracuseStep 1895879 = 2843819) B2843819
theorem B4615639 : Blo 996598 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B3239585 : Blo 996598 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B3371219 : Blo 996598 3371219 := bstep (se 1 (by rfl) ⟨2528414, by rfl⟩ : syracuseStep 3371219 = 5056829) B5056829
theorem B3371489 : Blo 996598 3371489 := bstep (se 2 (by rfl) ⟨1264308, by rfl⟩ : syracuseStep 3371489 = 2528617) B2528617
theorem B1897033 : Blo 996598 1897033 := bstep (se 2 (by rfl) ⟨711387, by rfl⟩ : syracuseStep 1897033 = 1422775) B1422775
theorem B8090533 : Blo 996598 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B3601759 : Blo 996598 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B7206347 : Blo 996598 7206347 := bstep (se 1 (by rfl) ⟨5404760, by rfl⟩ : syracuseStep 7206347 = 10809521) B10809521
theorem B19166867 : Blo 996598 19166867 := bstep (se 1 (by rfl) ⟨14375150, by rfl⟩ : syracuseStep 19166867 = 28750301) B28750301
theorem B3372731 : Blo 996598 3372731 := bstep (se 1 (by rfl) ⟨2529548, by rfl⟩ : syracuseStep 3372731 = 5059097) B5059097
theorem B29554391 : Blo 996598 29554391 := bstep (se 1 (by rfl) ⟨22165793, by rfl⟩ : syracuseStep 29554391 = 44331587) B44331587
theorem B40498987 : Blo 996598 40498987 := bstep (se 1 (by rfl) ⟨30374240, by rfl⟩ : syracuseStep 40498987 = 60748481) B60748481
theorem B25950307 : Blo 996598 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B12974327 : Blo 996598 12974327 := bstep (se 1 (by rfl) ⟨9730745, by rfl⟩ : syracuseStep 12974327 = 19461491) B19461491
theorem B3602855 : Blo 996598 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B1898977 : Blo 996598 1898977 := bstep (se 2 (by rfl) ⟨712116, by rfl⟩ : syracuseStep 1898977 = 1424233) B1424233
theorem B72940277 : Blo 996598 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B21625775 : Blo 996598 21625775 := bstep (se 1 (by rfl) ⟨16219331, by rfl⟩ : syracuseStep 21625775 = 32438663) B32438663
theorem B7306363 : Blo 996598 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B3374675 : Blo 996598 3374675 := bstep (se 1 (by rfl) ⟨2531006, by rfl⟩ : syracuseStep 3374675 = 5062013) B5062013
theorem B8650385 : Blo 996598 8650385 := bstep (se 2 (by rfl) ⟨3243894, by rfl⟩ : syracuseStep 8650385 = 6487789) B6487789
theorem B2522785 : Blo 996598 2522785 := bstep (se 2 (by rfl) ⟨946044, by rfl⟩ : syracuseStep 2522785 = 1892089) B1892089
theorem B2522927 : Blo 996598 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B3375323 : Blo 996598 3375323 := bstep (se 1 (by rfl) ⟨2531492, by rfl⟩ : syracuseStep 3375323 = 5062985) B5062985
theorem B3244313 : Blo 996598 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B3375593 : Blo 996598 3375593 := bstep (se 2 (by rfl) ⟨1265847, by rfl⟩ : syracuseStep 3375593 = 2531695) B2531695
theorem B3376187 : Blo 996598 3376187 := bstep (se 1 (by rfl) ⟨2532140, by rfl⟩ : syracuseStep 3376187 = 5064281) B5064281
theorem B3376457 : Blo 996598 3376457 := bstep (se 2 (by rfl) ⟨1266171, by rfl⟩ : syracuseStep 3376457 = 2532343) B2532343
theorem B11535691 : Blo 996598 11535691 := bstep (se 1 (by rfl) ⟨8651768, by rfl⟩ : syracuseStep 11535691 = 17303537) B17303537
theorem B5047919 : Blo 996598 5047919 := bstep (se 1 (by rfl) ⟨3785939, by rfl⟩ : syracuseStep 5047919 = 7571879) B7571879
theorem B1443439 : Blo 996598 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B5768819 : Blo 996598 5768819 := bstep (se 1 (by rfl) ⟨4326614, by rfl⟩ : syracuseStep 5768819 = 8653229) B8653229
theorem B2524891 : Blo 996598 2524891 := bstep (se 1 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 2524891 = 3787337) B3787337
theorem B6392465 : Blo 996598 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B2526187 : Blo 996598 2526187 := bstep (se 1 (by rfl) ⟨1894640, by rfl⟩ : syracuseStep 2526187 = 3789281) B3789281
theorem B5049377 : Blo 996598 5049377 := bstep (se 2 (by rfl) ⟨1893516, by rfl⟩ : syracuseStep 5049377 = 3787033) B3787033
theorem B23104561 : Blo 996598 23104561 := bstep (se 2 (by rfl) ⟨8664210, by rfl⟩ : syracuseStep 23104561 = 17328421) B17328421
theorem B2526329 : Blo 996598 2526329 := bstep (se 2 (by rfl) ⟨947373, by rfl⟩ : syracuseStep 2526329 = 1894747) B1894747
theorem B8522981 : Blo 996598 8522981 := bstep (se 4 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 8522981 = 1598059) B1598059
theorem B21630797 : Blo 996598 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B19959641 : Blo 996598 19959641 := bstep (se 2 (by rfl) ⟨7484865, by rfl⟩ : syracuseStep 19959641 = 14969731) B14969731
theorem B5050349 : Blo 996598 5050349 := bstep (se 3 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 5050349 = 1893881) B1893881
theorem B19206233 : Blo 996598 19206233 := bstep (se 2 (by rfl) ⟨7202337, by rfl⟩ : syracuseStep 19206233 = 14404675) B14404675
theorem B2527625 : Blo 996598 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B3641959 : Blo 996598 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B5051159 : Blo 996598 5051159 := bstep (se 1 (by rfl) ⟨3788369, by rfl⟩ : syracuseStep 5051159 = 7576739) B7576739
theorem B4264771 : Blo 996598 4264771 := bstep (se 1 (by rfl) ⟨3198578, by rfl⟩ : syracuseStep 4264771 = 6397157) B6397157
theorem B19174319 : Blo 996598 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B16225559 : Blo 996598 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B6395233 : Blo 996598 6395233 := bstep (se 2 (by rfl) ⟨2398212, by rfl⟩ : syracuseStep 6395233 = 4796425) B4796425
theorem B2135803 : Blo 996598 2135803 := bstep (se 1 (by rfl) ⟨1601852, by rfl⟩ : syracuseStep 2135803 = 3203705) B3203705
theorem B9606923 : Blo 996598 9606923 := bstep (se 1 (by rfl) ⟨7205192, by rfl⟩ : syracuseStep 9606923 = 14410385) B14410385
theorem B2529377 : Blo 996598 2529377 := bstep (se 2 (by rfl) ⟨948516, by rfl⟩ : syracuseStep 2529377 = 1897033) B1897033
theorem B5052779 : Blo 996598 5052779 := bstep (se 1 (by rfl) ⟨3789584, by rfl⟩ : syracuseStep 5052779 = 7579169) B7579169
theorem B10787377 : Blo 996598 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B5053265 : Blo 996598 5053265 := bstep (se 2 (by rfl) ⟨1894974, by rfl⟩ : syracuseStep 5053265 = 3789949) B3789949
theorem B1121503 : Blo 996598 1121503 := bstep (se 1 (by rfl) ⟨841127, by rfl⟩ : syracuseStep 1121503 = 1682255) B1682255
theorem B6397181 : Blo 996598 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B5054237 : Blo 996598 5054237 := bstep (se 3 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 5054237 = 1895339) B1895339
theorem B1515419 : Blo 996598 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B2531969 : Blo 996598 2531969 := bstep (se 2 (by rfl) ⟨949488, by rfl⟩ : syracuseStep 2531969 = 1898977) B1898977
theorem B19702927 : Blo 996598 19702927 := bstep (se 1 (by rfl) ⟨14777195, by rfl⟩ : syracuseStep 19702927 = 29554391) B29554391
theorem B5055695 : Blo 996598 5055695 := bstep (se 1 (by rfl) ⟨3791771, by rfl⟩ : syracuseStep 5055695 = 7583543) B7583543
theorem B4269419 : Blo 996598 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B9741817 : Blo 996598 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B1123951 : Blo 996598 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B2401903 : Blo 996598 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B1124059 : Blo 996598 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B1517449 : Blo 996598 1517449 := bstep (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) B1138087
theorem B1681951 : Blo 996598 1681951 := bstep (se 1 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 1681951 = 2522927) B2522927
theorem B1420087 : Blo 996598 1420087 := bstep (se 1 (by rfl) ⟨1065065, by rfl⟩ : syracuseStep 1420087 = 2130131) B2130131
theorem B1125211 : Blo 996598 1125211 := bstep (se 1 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 1125211 = 1687817) B1687817
theorem B4041667 : Blo 996598 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B1682383 : Blo 996598 1682383 := bstep (se 1 (by rfl) ⟨1261787, by rfl⟩ : syracuseStep 1682383 = 2523575) B2523575
theorem B3419435 : Blo 996598 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B1683119 : Blo 996598 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B1683355 : Blo 996598 1683355 := bstep (se 1 (by rfl) ⟨1262516, by rfl⟩ : syracuseStep 1683355 = 2525033) B2525033
theorem B276377615 : Blo 996598 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B92287025 : Blo 996598 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B1683767 : Blo 996598 1683767 := bstep (se 1 (by rfl) ⟨1262825, by rfl⟩ : syracuseStep 1683767 = 2525651) B2525651
theorem B8532377 : Blo 996598 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B48608171 : Blo 996598 48608171 := bstep (se 1 (by rfl) ⟨36456128, by rfl⟩ : syracuseStep 48608171 = 72912257) B72912257
theorem B1684543 : Blo 996598 1684543 := bstep (se 1 (by rfl) ⟨1263407, by rfl⟩ : syracuseStep 1684543 = 2526815) B2526815
theorem B9614531 : Blo 996598 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B5682419 : Blo 996598 5682419 := bstep (se 1 (by rfl) ⟨4261814, by rfl⟩ : syracuseStep 5682419 = 8523629) B8523629
theorem B996763 : Blo 996598 996763 := bstep (se 1 (by rfl) ⟨747572, by rfl⟩ : syracuseStep 996763 = 1495145) B1495145
theorem B1685063 : Blo 996598 1685063 := bstep (se 1 (by rfl) ⟨1263797, by rfl⟩ : syracuseStep 1685063 = 2527595) B2527595
theorem B10237529 : Blo 996598 10237529 := bstep (se 2 (by rfl) ⟨3839073, by rfl⟩ : syracuseStep 10237529 = 7678147) B7678147
theorem B996975 : Blo 996598 996975 := bstep (se 1 (by rfl) ⟨747731, by rfl⟩ : syracuseStep 996975 = 1495463) B1495463
theorem B997031 : Blo 996598 997031 := bstep (se 1 (by rfl) ⟨747773, by rfl⟩ : syracuseStep 997031 = 1495547) B1495547
theorem B997115 : Blo 996598 997115 := bstep (se 1 (by rfl) ⟨747836, by rfl⟩ : syracuseStep 997115 = 1495673) B1495673
theorem B1423099 : Blo 996598 1423099 := bstep (se 1 (by rfl) ⟨1067324, by rfl⟩ : syracuseStep 1423099 = 2134649) B2134649
theorem B997151 : Blo 996598 997151 := bstep (se 1 (by rfl) ⟨747863, by rfl⟩ : syracuseStep 997151 = 1495727) B1495727
theorem B1685279 : Blo 996598 1685279 := bstep (se 1 (by rfl) ⟨1263959, by rfl⟩ : syracuseStep 1685279 = 2527919) B2527919
theorem B2242367 : Blo 996598 2242367 := bstep (se 1 (by rfl) ⟨1681775, by rfl⟩ : syracuseStep 2242367 = 3363551) B3363551
theorem B997183 : Blo 996598 997183 := bstep (se 1 (by rfl) ⟨747887, by rfl⟩ : syracuseStep 997183 = 1495775) B1495775
theorem B4798271 : Blo 996598 4798271 := bstep (se 1 (by rfl) ⟨3598703, by rfl⟩ : syracuseStep 4798271 = 7197407) B7197407
theorem B23017445 : Blo 996598 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B997359 : Blo 996598 997359 := bstep (se 1 (by rfl) ⟨748019, by rfl⟩ : syracuseStep 997359 = 1496039) B1496039
theorem B1685495 : Blo 996598 1685495 := bstep (se 1 (by rfl) ⟨1264121, by rfl⟩ : syracuseStep 1685495 = 2528243) B2528243
theorem B5683193 : Blo 996598 5683193 := bstep (se 2 (by rfl) ⟨2131197, by rfl⟩ : syracuseStep 5683193 = 4262395) B4262395
theorem B9615419 : Blo 996598 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B2242655 : Blo 996598 2242655 := bstep (se 1 (by rfl) ⟨1681991, by rfl⟩ : syracuseStep 2242655 = 3363983) B3363983
theorem B997531 : Blo 996598 997531 := bstep (se 1 (by rfl) ⟨748148, by rfl⟩ : syracuseStep 997531 = 1496297) B1496297
theorem B997567 : Blo 996598 997567 := bstep (se 1 (by rfl) ⟨748175, by rfl⟩ : syracuseStep 997567 = 1496351) B1496351
theorem B1423595 : Blo 996598 1423595 := bstep (se 1 (by rfl) ⟨1067696, by rfl⟩ : syracuseStep 1423595 = 2135393) B2135393
theorem B997679 : Blo 996598 997679 := bstep (se 1 (by rfl) ⟨748259, by rfl⟩ : syracuseStep 997679 = 1496519) B1496519
theorem B997915 : Blo 996598 997915 := bstep (se 1 (by rfl) ⟨748436, by rfl⟩ : syracuseStep 997915 = 1496873) B1496873
theorem B997919 : Blo 996598 997919 := bstep (se 1 (by rfl) ⟨748439, by rfl⟩ : syracuseStep 997919 = 1496879) B1496879
theorem B3193465 : Blo 996598 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B2243411 : Blo 996598 2243411 := bstep (se 1 (by rfl) ⟨1682558, by rfl⟩ : syracuseStep 2243411 = 3365117) B3365117
theorem B998235 : Blo 996598 998235 := bstep (se 1 (by rfl) ⟨748676, by rfl⟩ : syracuseStep 998235 = 1497353) B1497353
theorem B998303 : Blo 996598 998303 := bstep (se 1 (by rfl) ⟨748727, by rfl⟩ : syracuseStep 998303 = 1497455) B1497455
theorem B6831145 : Blo 996598 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B998447 : Blo 996598 998447 := bstep (se 1 (by rfl) ⟨748835, by rfl⟩ : syracuseStep 998447 = 1497671) B1497671
theorem B1686575 : Blo 996598 1686575 := bstep (se 1 (by rfl) ⟨1264931, by rfl⟩ : syracuseStep 1686575 = 2529863) B2529863
theorem B1096751 : Blo 996598 1096751 := bstep (se 1 (by rfl) ⟨822563, by rfl⟩ : syracuseStep 1096751 = 1645127) B1645127
theorem B998471 : Blo 996598 998471 := bstep (se 1 (by rfl) ⟨748853, by rfl⟩ : syracuseStep 998471 = 1497707) B1497707
theorem B1686649 : Blo 996598 1686649 := bstep (se 2 (by rfl) ⟨632493, by rfl⟩ : syracuseStep 1686649 = 1264987) B1264987
theorem B998623 : Blo 996598 998623 := bstep (se 1 (by rfl) ⟨748967, by rfl⟩ : syracuseStep 998623 = 1497935) B1497935
theorem B2243951 : Blo 996598 2243951 := bstep (se 1 (by rfl) ⟨1682963, by rfl⟩ : syracuseStep 2243951 = 3365927) B3365927
theorem B3653003 : Blo 996598 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B3784103 : Blo 996598 3784103 := bstep (se 1 (by rfl) ⟨2838077, by rfl⟩ : syracuseStep 3784103 = 5676155) B5676155
theorem B2309543 : Blo 996598 2309543 := bstep (se 1 (by rfl) ⟨1732157, by rfl⟩ : syracuseStep 2309543 = 3464315) B3464315
theorem B1686953 : Blo 996598 1686953 := bstep (se 2 (by rfl) ⟨632607, by rfl⟩ : syracuseStep 1686953 = 1265215) B1265215
theorem B6405587 : Blo 996598 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B998887 : Blo 996598 998887 := bstep (se 1 (by rfl) ⟨749165, by rfl⟩ : syracuseStep 998887 = 1498331) B1498331
theorem B999003 : Blo 996598 999003 := bstep (se 1 (by rfl) ⟨749252, by rfl⟩ : syracuseStep 999003 = 1498505) B1498505
theorem B2244239 : Blo 996598 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B2244329 : Blo 996598 2244329 := bstep (se 2 (by rfl) ⟨841623, by rfl⟩ : syracuseStep 2244329 = 1683247) B1683247
theorem B6831863 : Blo 996598 6831863 := bstep (se 1 (by rfl) ⟨5123897, by rfl⟩ : syracuseStep 6831863 = 10247795) B10247795
theorem B999239 : Blo 996598 999239 := bstep (se 1 (by rfl) ⟨749429, by rfl⟩ : syracuseStep 999239 = 1498859) B1498859
theorem B3194747 : Blo 996598 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B999391 : Blo 996598 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B999655 : Blo 996598 999655 := bstep (se 1 (by rfl) ⟨749741, by rfl⟩ : syracuseStep 999655 = 1499483) B1499483
theorem B1687783 : Blo 996598 1687783 := bstep (se 1 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 1687783 = 2531675) B2531675
theorem B999807 : Blo 996598 999807 := bstep (se 1 (by rfl) ⟨749855, by rfl⟩ : syracuseStep 999807 = 1499711) B1499711
theorem B1687945 : Blo 996598 1687945 := bstep (se 2 (by rfl) ⟨632979, by rfl⟩ : syracuseStep 1687945 = 1265959) B1265959
theorem B999887 : Blo 996598 999887 := bstep (se 1 (by rfl) ⟨749915, by rfl⟩ : syracuseStep 999887 = 1499831) B1499831
theorem B1000039 : Blo 996598 1000039 := bstep (se 1 (by rfl) ⟨750029, by rfl⟩ : syracuseStep 1000039 = 1500059) B1500059
theorem B2245355 : Blo 996598 2245355 := bstep (se 1 (by rfl) ⟨1684016, by rfl⟩ : syracuseStep 2245355 = 3368033) B3368033
theorem B5063471 : Blo 996598 5063471 := bstep (se 1 (by rfl) ⟨3797603, by rfl⟩ : syracuseStep 5063471 = 7595207) B7595207
theorem B2704175 : Blo 996598 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1688377 : Blo 996598 1688377 := bstep (se 2 (by rfl) ⟨633141, by rfl⟩ : syracuseStep 1688377 = 1266283) B1266283
theorem B1000303 : Blo 996598 1000303 := bstep (se 1 (by rfl) ⟨750227, by rfl⟩ : syracuseStep 1000303 = 1500455) B1500455
theorem B1688431 : Blo 996598 1688431 := bstep (se 1 (by rfl) ⟨1266323, by rfl⟩ : syracuseStep 1688431 = 2532647) B2532647
theorem B1000359 : Blo 996598 1000359 := bstep (se 1 (by rfl) ⟨750269, by rfl⟩ : syracuseStep 1000359 = 1500539) B1500539
theorem B1000443 : Blo 996598 1000443 := bstep (se 1 (by rfl) ⟨750332, by rfl⟩ : syracuseStep 1000443 = 1500665) B1500665
theorem B1000511 : Blo 996598 1000511 := bstep (se 1 (by rfl) ⟨750383, by rfl⟩ : syracuseStep 1000511 = 1500767) B1500767
theorem B3196027 : Blo 996598 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B1066159 : Blo 996598 1066159 := bstep (se 1 (by rfl) ⟨799619, by rfl⟩ : syracuseStep 1066159 = 1599239) B1599239
theorem B27280793 : Blo 996598 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B3786335 : Blo 996598 3786335 := bstep (se 1 (by rfl) ⟨2839751, by rfl⟩ : syracuseStep 3786335 = 5679503) B5679503
theorem B1263215 : Blo 996598 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B2246255 : Blo 996598 2246255 := bstep (se 1 (by rfl) ⟨1684691, by rfl⟩ : syracuseStep 2246255 = 3369383) B3369383
theorem B1263271 : Blo 996598 1263271 := bstep (se 1 (by rfl) ⟨947453, by rfl⟩ : syracuseStep 1263271 = 1894907) B1894907
theorem B2246363 : Blo 996598 2246363 := bstep (se 1 (by rfl) ⟨1684772, by rfl⟩ : syracuseStep 2246363 = 3369545) B3369545
theorem B4802345 : Blo 996598 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B1263919 : Blo 996598 1263919 := bstep (se 1 (by rfl) ⟨947939, by rfl⟩ : syracuseStep 1263919 = 1895879) B1895879
theorem B2247479 : Blo 996598 2247479 := bstep (se 1 (by rfl) ⟨1685609, by rfl⟩ : syracuseStep 2247479 = 3371219) B3371219
theorem B2247659 : Blo 996598 2247659 := bstep (se 1 (by rfl) ⟨1685744, by rfl⟩ : syracuseStep 2247659 = 3371489) B3371489
theorem B210488753 : Blo 996598 210488753 := bstep (se 2 (by rfl) ⟨78933282, by rfl⟩ : syracuseStep 210488753 = 157866565) B157866565
theorem B4804231 : Blo 996598 4804231 := bstep (se 1 (by rfl) ⟨3603173, by rfl⟩ : syracuseStep 4804231 = 7206347) B7206347
theorem B2248487 : Blo 996598 2248487 := bstep (se 1 (by rfl) ⟨1686365, by rfl⟩ : syracuseStep 2248487 = 3372731) B3372731
theorem B6180713 : Blo 996598 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B1494905 : Blo 996598 1494905 := bstep (se 2 (by rfl) ⟨560589, by rfl⟩ : syracuseStep 1494905 = 1121179) B1121179
theorem B1495007 : Blo 996598 1495007 := bstep (se 1 (by rfl) ⟨1121255, by rfl⟩ : syracuseStep 1495007 = 2242511) B2242511
theorem B1495259 : Blo 996598 1495259 := bstep (se 1 (by rfl) ⟨1121444, by rfl⟩ : syracuseStep 1495259 = 2242889) B2242889
theorem B1495271 : Blo 996598 1495271 := bstep (se 1 (by rfl) ⟨1121453, by rfl⟩ : syracuseStep 1495271 = 2242907) B2242907
theorem B1495433 : Blo 996598 1495433 := bstep (se 2 (by rfl) ⟨560787, by rfl⟩ : syracuseStep 1495433 = 1121575) B1121575
theorem B1495529 : Blo 996598 1495529 := bstep (se 2 (by rfl) ⟨560823, by rfl⟩ : syracuseStep 1495529 = 1121647) B1121647
theorem B1495655 : Blo 996598 1495655 := bstep (se 1 (by rfl) ⟨1121741, by rfl⟩ : syracuseStep 1495655 = 2243483) B2243483
theorem B1495787 : Blo 996598 1495787 := bstep (se 1 (by rfl) ⟨1121840, by rfl⟩ : syracuseStep 1495787 = 2243681) B2243681
theorem B1495817 : Blo 996598 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B2249513 : Blo 996598 2249513 := bstep (se 2 (by rfl) ⟨843567, by rfl⟩ : syracuseStep 2249513 = 1687135) B1687135
theorem B1495919 : Blo 996598 1495919 := bstep (se 1 (by rfl) ⟨1121939, by rfl⟩ : syracuseStep 1495919 = 2243879) B2243879
theorem B3363713 : Blo 996598 3363713 := bstep (se 2 (by rfl) ⟨1261392, by rfl⟩ : syracuseStep 3363713 = 2522785) B2522785
theorem B12964873 : Blo 996598 12964873 := bstep (se 2 (by rfl) ⟨4861827, by rfl⟩ : syracuseStep 12964873 = 9723655) B9723655
theorem B7197751 : Blo 996598 7197751 := bstep (se 1 (by rfl) ⟨5398313, by rfl⟩ : syracuseStep 7197751 = 10796627) B10796627
theorem B2249783 : Blo 996598 2249783 := bstep (se 1 (by rfl) ⟨1687337, by rfl⟩ : syracuseStep 2249783 = 3374675) B3374675
theorem B2249801 : Blo 996598 2249801 := bstep (se 2 (by rfl) ⟨843675, by rfl⟩ : syracuseStep 2249801 = 1687351) B1687351
theorem B1496171 : Blo 996598 1496171 := bstep (se 1 (by rfl) ⟨1122128, by rfl⟩ : syracuseStep 1496171 = 2244257) B2244257
theorem B4052177 : Blo 996598 4052177 := bstep (se 2 (by rfl) ⟨1519566, by rfl⟩ : syracuseStep 4052177 = 3039133) B3039133
theorem B3200219 : Blo 996598 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B7197983 : Blo 996598 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B1496411 : Blo 996598 1496411 := bstep (se 1 (by rfl) ⟨1122308, by rfl⟩ : syracuseStep 1496411 = 2244617) B2244617
theorem B1496687 : Blo 996598 1496687 := bstep (se 1 (by rfl) ⟨1122515, by rfl⟩ : syracuseStep 1496687 = 2245031) B2245031
theorem B3364523 : Blo 996598 3364523 := bstep (se 1 (by rfl) ⟨2523392, by rfl⟩ : syracuseStep 3364523 = 5046785) B5046785
theorem B1496759 : Blo 996598 1496759 := bstep (se 1 (by rfl) ⟨1122569, by rfl⟩ : syracuseStep 1496759 = 2245139) B2245139
theorem B1496795 : Blo 996598 1496795 := bstep (se 1 (by rfl) ⟨1122596, by rfl⟩ : syracuseStep 1496795 = 2245193) B2245193
theorem B25548533 : Blo 996598 25548533 := bstep (se 5 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 25548533 = 2395175) B2395175
theorem B1496969 : Blo 996598 1496969 := bstep (se 2 (by rfl) ⟨561363, by rfl⟩ : syracuseStep 1496969 = 1122727) B1122727
theorem B3364847 : Blo 996598 3364847 := bstep (se 1 (by rfl) ⟨2523635, by rfl⟩ : syracuseStep 3364847 = 5047271) B5047271
theorem B1497071 : Blo 996598 1497071 := bstep (se 1 (by rfl) ⟨1122803, by rfl⟩ : syracuseStep 1497071 = 2245607) B2245607
theorem B18208961 : Blo 996598 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B3365063 : Blo 996598 3365063 := bstep (se 1 (by rfl) ⟨2523797, by rfl⟩ : syracuseStep 3365063 = 5047595) B5047595
theorem B1497323 : Blo 996598 1497323 := bstep (se 1 (by rfl) ⟨1122992, by rfl⟩ : syracuseStep 1497323 = 2245985) B2245985
theorem B1497383 : Blo 996598 1497383 := bstep (se 1 (by rfl) ⟨1123037, by rfl⟩ : syracuseStep 1497383 = 2246075) B2246075
theorem B1497467 : Blo 996598 1497467 := bstep (se 1 (by rfl) ⟨1123100, by rfl⟩ : syracuseStep 1497467 = 2246201) B2246201
theorem B1497737 : Blo 996598 1497737 := bstep (se 2 (by rfl) ⟨561651, by rfl⟩ : syracuseStep 1497737 = 1123303) B1123303
theorem B6085367 : Blo 996598 6085367 := bstep (se 1 (by rfl) ⟨4564025, by rfl⟩ : syracuseStep 6085367 = 9128051) B9128051
theorem B1497911 : Blo 996598 1497911 := bstep (se 1 (by rfl) ⟨1123433, by rfl⟩ : syracuseStep 1497911 = 2246867) B2246867
theorem B3201871 : Blo 996598 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B3365711 : Blo 996598 3365711 := bstep (se 1 (by rfl) ⟨2524283, by rfl⟩ : syracuseStep 3365711 = 5048567) B5048567
theorem B1497947 : Blo 996598 1497947 := bstep (se 1 (by rfl) ⟨1123460, by rfl⟩ : syracuseStep 1497947 = 2246921) B2246921
theorem B7199597 : Blo 996598 7199597 := bstep (se 3 (by rfl) ⟨1349924, by rfl⟩ : syracuseStep 7199597 = 2699849) B2699849
theorem B2841551 : Blo 996598 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B1498091 : Blo 996598 1498091 := bstep (se 1 (by rfl) ⟨1123568, by rfl⟩ : syracuseStep 1498091 = 2247137) B2247137
theorem B3366035 : Blo 996598 3366035 := bstep (se 1 (by rfl) ⟨2524526, by rfl⟩ : syracuseStep 3366035 = 5049053) B5049053
theorem B1498295 : Blo 996598 1498295 := bstep (se 1 (by rfl) ⟨1123721, by rfl⟩ : syracuseStep 1498295 = 2247443) B2247443
theorem B12147965 : Blo 996598 12147965 := bstep (se 3 (by rfl) ⟨2277743, by rfl⟩ : syracuseStep 12147965 = 4555487) B4555487
theorem B3366305 : Blo 996598 3366305 := bstep (se 2 (by rfl) ⟨1262364, by rfl⟩ : syracuseStep 3366305 = 2524729) B2524729
theorem B1498535 : Blo 996598 1498535 := bstep (se 1 (by rfl) ⟨1123901, by rfl⟩ : syracuseStep 1498535 = 2247803) B2247803
theorem B2842087 : Blo 996598 2842087 := bstep (se 1 (by rfl) ⟨2131565, by rfl⟩ : syracuseStep 2842087 = 4263131) B4263131
theorem B1498619 : Blo 996598 1498619 := bstep (se 1 (by rfl) ⟨1123964, by rfl⟩ : syracuseStep 1498619 = 2247929) B2247929
theorem B1498715 : Blo 996598 1498715 := bstep (se 1 (by rfl) ⟨1124036, by rfl⟩ : syracuseStep 1498715 = 2248073) B2248073
theorem B1498799 : Blo 996598 1498799 := bstep (se 1 (by rfl) ⟨1124099, by rfl⟩ : syracuseStep 1498799 = 2248199) B2248199
theorem B1498919 : Blo 996598 1498919 := bstep (se 1 (by rfl) ⟨1124189, by rfl⟩ : syracuseStep 1498919 = 2248379) B2248379
theorem B1499003 : Blo 996598 1499003 := bstep (se 1 (by rfl) ⟨1124252, by rfl⟩ : syracuseStep 1499003 = 2248505) B2248505
theorem B3366845 : Blo 996598 3366845 := bstep (se 3 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 3366845 = 1262567) B1262567
theorem B1499423 : Blo 996598 1499423 := bstep (se 1 (by rfl) ⟨1124567, by rfl⟩ : syracuseStep 1499423 = 2249135) B2249135
theorem B1499447 : Blo 996598 1499447 := bstep (se 1 (by rfl) ⟨1124585, by rfl⟩ : syracuseStep 1499447 = 2249171) B2249171
theorem B1499519 : Blo 996598 1499519 := bstep (se 1 (by rfl) ⟨1124639, by rfl⟩ : syracuseStep 1499519 = 2249279) B2249279
theorem B9593275 : Blo 996598 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B1499591 : Blo 996598 1499591 := bstep (se 1 (by rfl) ⟨1124693, by rfl⟩ : syracuseStep 1499591 = 2249387) B2249387
theorem B1499945 : Blo 996598 1499945 := bstep (se 2 (by rfl) ⟨562479, by rfl⟩ : syracuseStep 1499945 = 1124959) B1124959
theorem B1499951 : Blo 996598 1499951 := bstep (se 1 (by rfl) ⟨1124963, by rfl⟩ : syracuseStep 1499951 = 2249927) B2249927
theorem B1500071 : Blo 996598 1500071 := bstep (se 1 (by rfl) ⟨1125053, by rfl⟩ : syracuseStep 1500071 = 2250107) B2250107
theorem B1500155 : Blo 996598 1500155 := bstep (se 1 (by rfl) ⟨1125116, by rfl⟩ : syracuseStep 1500155 = 2250233) B2250233
theorem B1500215 : Blo 996598 1500215 := bstep (se 1 (by rfl) ⟨1125161, by rfl⟩ : syracuseStep 1500215 = 2250323) B2250323
theorem B1500335 : Blo 996598 1500335 := bstep (se 1 (by rfl) ⟨1125251, by rfl⟩ : syracuseStep 1500335 = 2250503) B2250503
theorem B2844011 : Blo 996598 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B5694857 : Blo 996598 5694857 := bstep (se 2 (by rfl) ⟨2135571, by rfl⟩ : syracuseStep 5694857 = 4271143) B4271143
theorem B1500743 : Blo 996598 1500743 := bstep (se 1 (by rfl) ⟨1125557, by rfl⟩ : syracuseStep 1500743 = 2251115) B2251115
theorem B8087161 : Blo 996598 8087161 := bstep (se 2 (by rfl) ⟨3032685, by rfl⟩ : syracuseStep 8087161 = 6065371) B6065371
theorem B1500839 : Blo 996598 1500839 := bstep (se 1 (by rfl) ⟨1125629, by rfl⟩ : syracuseStep 1500839 = 2251259) B2251259
theorem B3368735 : Blo 996598 3368735 := bstep (se 1 (by rfl) ⟨2526551, by rfl⟩ : syracuseStep 3368735 = 5053103) B5053103
theorem B3368951 : Blo 996598 3368951 := bstep (se 1 (by rfl) ⟨2526713, by rfl⟩ : syracuseStep 3368951 = 5053427) B5053427
theorem B3467411 : Blo 996598 3467411 := bstep (se 1 (by rfl) ⟨2600558, by rfl⟩ : syracuseStep 3467411 = 5201117) B5201117
theorem B7596179 : Blo 996598 7596179 := bstep (se 1 (by rfl) ⟨5697134, by rfl⟩ : syracuseStep 7596179 = 11394269) B11394269
theorem B3795295 : Blo 996598 3795295 := bstep (se 1 (by rfl) ⟨2846471, by rfl⟩ : syracuseStep 3795295 = 5692943) B5692943
theorem B14379767 : Blo 996598 14379767 := bstep (se 1 (by rfl) ⟨10784825, by rfl⟩ : syracuseStep 14379767 = 21569651) B21569651
theorem B3795767 : Blo 996598 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B3369815 : Blo 996598 3369815 := bstep (se 1 (by rfl) ⟨2527361, by rfl⟩ : syracuseStep 3369815 = 5054723) B5054723
theorem B3370031 : Blo 996598 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B3796267 : Blo 996598 3796267 := bstep (se 1 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 3796267 = 5694401) B5694401
theorem B1600879 : Blo 996598 1600879 := bstep (se 1 (by rfl) ⟨1200659, by rfl⟩ : syracuseStep 1600879 = 2401319) B2401319
theorem B3370409 : Blo 996598 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B30797333 : Blo 996598 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B3370895 : Blo 996598 3370895 := bstep (se 1 (by rfl) ⟨2528171, by rfl⟩ : syracuseStep 3370895 = 5056343) B5056343
theorem B7303085 : Blo 996598 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B3371273 : Blo 996598 3371273 := bstep (se 2 (by rfl) ⟨1264227, by rfl⟩ : syracuseStep 3371273 = 2528455) B2528455
theorem B194507405 : Blo 996598 194507405 := bstep (se 3 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 194507405 = 72940277) B72940277
theorem B7205597 : Blo 996598 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B3208061 : Blo 996598 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B8221601 : Blo 996598 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B53998649 : Blo 996598 53998649 := bstep (se 2 (by rfl) ⟨20249493, by rfl⟩ : syracuseStep 53998649 = 40498987) B40498987
theorem B2159723 : Blo 996598 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B2847919 : Blo 996598 2847919 := bstep (se 1 (by rfl) ⟨2135939, by rfl⟩ : syracuseStep 2847919 = 4271879) B4271879
theorem B3372407 : Blo 996598 3372407 := bstep (se 1 (by rfl) ⟨2529305, by rfl⟩ : syracuseStep 3372407 = 5058611) B5058611
theorem B34600409 : Blo 996598 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B3373217 : Blo 996598 3373217 := bstep (se 2 (by rfl) ⟨1264956, by rfl⟩ : syracuseStep 3373217 = 2529913) B2529913
theorem B1800505 : Blo 996598 1800505 := bstep (se 2 (by rfl) ⟨675189, by rfl⟩ : syracuseStep 1800505 = 1350379) B1350379
theorem B3373487 : Blo 996598 3373487 := bstep (se 1 (by rfl) ⟨2530115, by rfl⟩ : syracuseStep 3373487 = 5060231) B5060231
theorem B12777911 : Blo 996598 12777911 := bstep (se 1 (by rfl) ⟨9583433, by rfl⟩ : syracuseStep 12777911 = 19166867) B19166867
theorem B8649551 : Blo 996598 8649551 := bstep (se 1 (by rfl) ⟨6487163, by rfl⟩ : syracuseStep 8649551 = 12974327) B12974327
theorem B98466965 : Blo 996598 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B4259081 : Blo 996598 4259081 := bstep (se 2 (by rfl) ⟨1597155, by rfl⟩ : syracuseStep 4259081 = 3194311) B3194311
theorem B14417183 : Blo 996598 14417183 := bstep (se 1 (by rfl) ⟨10812887, by rfl⟩ : syracuseStep 14417183 = 21625775) B21625775
theorem B3374567 : Blo 996598 3374567 := bstep (se 1 (by rfl) ⟨2530925, by rfl⟩ : syracuseStep 3374567 = 5061851) B5061851
theorem B5766923 : Blo 996598 5766923 := bstep (se 1 (by rfl) ⟨4325192, by rfl⟩ : syracuseStep 5766923 = 8650385) B8650385
theorem B2162875 : Blo 996598 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B3375647 : Blo 996598 3375647 := bstep (se 1 (by rfl) ⟨2531735, by rfl⟩ : syracuseStep 3375647 = 5063471) B5063471
theorem B1802783 : Blo 996598 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B18187195 : Blo 996598 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B2524223 : Blo 996598 2524223 := bstep (se 1 (by rfl) ⟨1893167, by rfl⟩ : syracuseStep 2524223 = 3786335) B3786335
theorem B4261643 : Blo 996598 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B10782881 : Blo 996598 10782881 := bstep (se 2 (by rfl) ⟨4043580, by rfl⟩ : syracuseStep 10782881 = 8087161) B8087161
theorem B14420531 : Blo 996598 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B13306427 : Blo 996598 13306427 := bstep (se 1 (by rfl) ⟨9979820, by rfl⟩ : syracuseStep 13306427 = 19959641) B19959641
theorem B12782879 : Blo 996598 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B2133479 : Blo 996598 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B10817039 : Blo 996598 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B30806081 : Blo 996598 30806081 := bstep (se 2 (by rfl) ⟨11552280, by rfl⟩ : syracuseStep 30806081 = 23104561) B23104561
theorem B2134505 : Blo 996598 2134505 := bstep (se 2 (by rfl) ⟨800439, by rfl⟩ : syracuseStep 2134505 = 1600879) B1600879
theorem B4264787 : Blo 996598 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B8098643 : Blo 996598 8098643 := bstep (se 1 (by rfl) ⟨6073982, by rfl⟩ : syracuseStep 8098643 = 12147965) B12147965
theorem B17045477 : Blo 996598 17045477 := bstep (se 4 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 17045477 = 3196027) B3196027
theorem B4855945 : Blo 996598 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B8526977 : Blo 996598 8526977 := bstep (se 2 (by rfl) ⟨3197616, by rfl⟩ : syracuseStep 8526977 = 6395233) B6395233
theorem B2530511 : Blo 996598 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B1122079 : Blo 996598 1122079 := bstep (se 1 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 1122079 = 1683119) B1683119
theorem B2924669 : Blo 996598 2924669 := bstep (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) B1096751
theorem B1122511 : Blo 996598 1122511 := bstep (se 1 (by rfl) ⟨841883, by rfl⟩ : syracuseStep 1122511 = 1683767) B1683767
theorem B2400673 : Blo 996598 2400673 := bstep (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) B1800505
theorem B129671603 : Blo 996598 129671603 := bstep (se 1 (by rfl) ⟨97253702, by rfl⟩ : syracuseStep 129671603 = 194507405) B194507405
theorem B2138707 : Blo 996598 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B5481067 : Blo 996598 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B9118493 : Blo 996598 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B9741341 : Blo 996598 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B1123375 : Blo 996598 1123375 := bstep (se 1 (by rfl) ⟨842531, by rfl⟩ : syracuseStep 1123375 = 1685063) B1685063
theorem B6825019 : Blo 996598 6825019 := bstep (se 1 (by rfl) ⟨5118764, by rfl⟩ : syracuseStep 6825019 = 10237529) B10237529
theorem B4269161 : Blo 996598 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B1123519 : Blo 996598 1123519 := bstep (se 1 (by rfl) ⟨842639, by rfl⟩ : syracuseStep 1123519 = 1685279) B1685279
theorem B15344963 : Blo 996598 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B1123663 : Blo 996598 1123663 := bstep (se 1 (by rfl) ⟨842747, by rfl⟩ : syracuseStep 1123663 = 1685495) B1685495
theorem B77899573 : Blo 996598 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B15378461 : Blo 996598 15378461 := bstep (se 3 (by rfl) ⟨2883461, by rfl⟩ : syracuseStep 15378461 = 5766923) B5766923
theorem B1124383 : Blo 996598 1124383 := bstep (se 1 (by rfl) ⟨843287, by rfl⟩ : syracuseStep 1124383 = 1686575) B1686575
theorem B65644643 : Blo 996598 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B9611455 : Blo 996598 9611455 := bstep (se 1 (by rfl) ⟨7208591, by rfl⟩ : syracuseStep 9611455 = 14417183) B14417183
theorem B1124635 : Blo 996598 1124635 := bstep (se 1 (by rfl) ⟨843476, by rfl⟩ : syracuseStep 1124635 = 1686953) B1686953
theorem B4270391 : Blo 996598 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B12791033 : Blo 996598 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B3845879 : Blo 996598 3845879 := bstep (se 1 (by rfl) ⟨2884409, by rfl⟩ : syracuseStep 3845879 = 5768819) B5768819
theorem B1421545 : Blo 996598 1421545 := bstep (se 2 (by rfl) ⟨533079, by rfl⟩ : syracuseStep 1421545 = 1066159) B1066159
theorem B15380921 : Blo 996598 15380921 := bstep (se 2 (by rfl) ⟨5767845, by rfl⟩ : syracuseStep 15380921 = 11535691) B11535691
theorem B12989089 : Blo 996598 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B1684219 : Blo 996598 1684219 := bstep (se 1 (by rfl) ⟨1263164, by rfl⟩ : syracuseStep 1684219 = 2526329) B2526329
theorem B5681987 : Blo 996598 5681987 := bstep (se 1 (by rfl) ⟨4261490, by rfl⟩ : syracuseStep 5681987 = 8522981) B8522981
theorem B1684361 : Blo 996598 1684361 := bstep (se 2 (by rfl) ⟨631635, by rfl⟩ : syracuseStep 1684361 = 1263271) B1263271
theorem B996603 : Blo 996598 996603 := bstep (se 1 (by rfl) ⟨747452, by rfl⟩ : syracuseStep 996603 = 1494905) B1494905
theorem B996671 : Blo 996598 996671 := bstep (se 1 (by rfl) ⟨747503, by rfl⟩ : syracuseStep 996671 = 1495007) B1495007
theorem B996839 : Blo 996598 996839 := bstep (se 1 (by rfl) ⟨747629, by rfl⟩ : syracuseStep 996839 = 1495259) B1495259
theorem B996847 : Blo 996598 996847 := bstep (se 1 (by rfl) ⟨747635, by rfl⟩ : syracuseStep 996847 = 1495271) B1495271
theorem B996955 : Blo 996598 996955 := bstep (se 1 (by rfl) ⟨747716, by rfl⟩ : syracuseStep 996955 = 1495433) B1495433
theorem B1685083 : Blo 996598 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B997019 : Blo 996598 997019 := bstep (se 1 (by rfl) ⟨747764, by rfl⟩ : syracuseStep 997019 = 1495529) B1495529
theorem B1685225 : Blo 996598 1685225 := bstep (se 2 (by rfl) ⟨631959, by rfl⟩ : syracuseStep 1685225 = 1263919) B1263919
theorem B997103 : Blo 996598 997103 := bstep (se 1 (by rfl) ⟨747827, by rfl⟩ : syracuseStep 997103 = 1495655) B1495655
theorem B5060393 : Blo 996598 5060393 := bstep (se 2 (by rfl) ⟨1897647, by rfl⟩ : syracuseStep 5060393 = 3795295) B3795295
theorem B997191 : Blo 996598 997191 := bstep (se 1 (by rfl) ⟨747893, by rfl⟩ : syracuseStep 997191 = 1495787) B1495787
theorem B997211 : Blo 996598 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B997279 : Blo 996598 997279 := bstep (se 1 (by rfl) ⟨747959, by rfl⟩ : syracuseStep 997279 = 1495919) B1495919
theorem B2242475 : Blo 996598 2242475 := bstep (se 1 (by rfl) ⟨1681856, by rfl⟩ : syracuseStep 2242475 = 3363713) B3363713
theorem B2242601 : Blo 996598 2242601 := bstep (se 2 (by rfl) ⟨840975, by rfl⟩ : syracuseStep 2242601 = 1681951) B1681951
theorem B997447 : Blo 996598 997447 := bstep (se 1 (by rfl) ⟨748085, by rfl⟩ : syracuseStep 997447 = 1496171) B1496171
theorem B2701451 : Blo 996598 2701451 := bstep (se 1 (by rfl) ⟨2026088, by rfl⟩ : syracuseStep 2701451 = 4052177) B4052177
theorem B4798655 : Blo 996598 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B997607 : Blo 996598 997607 := bstep (se 1 (by rfl) ⟨748205, by rfl⟩ : syracuseStep 997607 = 1496411) B1496411
theorem B7584029 : Blo 996598 7584029 := bstep (se 3 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 7584029 = 2844011) B2844011
theorem B997791 : Blo 996598 997791 := bstep (se 1 (by rfl) ⟨748343, by rfl⟩ : syracuseStep 997791 = 1496687) B1496687
theorem B2243015 : Blo 996598 2243015 := bstep (se 1 (by rfl) ⟨1682261, by rfl⟩ : syracuseStep 2243015 = 3364523) B3364523
theorem B997839 : Blo 996598 997839 := bstep (se 1 (by rfl) ⟨748379, by rfl⟩ : syracuseStep 997839 = 1496759) B1496759
theorem B997863 : Blo 996598 997863 := bstep (se 1 (by rfl) ⟨748397, by rfl⟩ : syracuseStep 997863 = 1496795) B1496795
theorem B6404615 : Blo 996598 6404615 := bstep (se 1 (by rfl) ⟨4803461, by rfl⟩ : syracuseStep 6404615 = 9606923) B9606923
theorem B5388889 : Blo 996598 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B997979 : Blo 996598 997979 := bstep (se 1 (by rfl) ⟨748484, by rfl⟩ : syracuseStep 997979 = 1496969) B1496969
theorem B2243177 : Blo 996598 2243177 := bstep (se 2 (by rfl) ⟨841191, by rfl⟩ : syracuseStep 2243177 = 1682383) B1682383
theorem B2243231 : Blo 996598 2243231 := bstep (se 1 (by rfl) ⟨1682423, by rfl⟩ : syracuseStep 2243231 = 3364847) B3364847
theorem B998047 : Blo 996598 998047 := bstep (se 1 (by rfl) ⟨748535, by rfl⟩ : syracuseStep 998047 = 1497071) B1497071
theorem B1686251 : Blo 996598 1686251 := bstep (se 1 (by rfl) ⟨1264688, by rfl⟩ : syracuseStep 1686251 = 2529377) B2529377
theorem B12139307 : Blo 996598 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B2243375 : Blo 996598 2243375 := bstep (se 1 (by rfl) ⟨1682531, by rfl⟩ : syracuseStep 2243375 = 3365063) B3365063
theorem B998215 : Blo 996598 998215 := bstep (se 1 (by rfl) ⟨748661, by rfl⟩ : syracuseStep 998215 = 1497323) B1497323
theorem B998255 : Blo 996598 998255 := bstep (se 1 (by rfl) ⟨748691, by rfl⟩ : syracuseStep 998255 = 1497383) B1497383
theorem B998311 : Blo 996598 998311 := bstep (se 1 (by rfl) ⟨748733, by rfl⟩ : syracuseStep 998311 = 1497467) B1497467
theorem B5061689 : Blo 996598 5061689 := bstep (se 2 (by rfl) ⟨1898133, by rfl⟩ : syracuseStep 5061689 = 3796267) B3796267
theorem B998491 : Blo 996598 998491 := bstep (se 1 (by rfl) ⟨748868, by rfl⟩ : syracuseStep 998491 = 1497737) B1497737
theorem B998607 : Blo 996598 998607 := bstep (se 1 (by rfl) ⟨748955, by rfl⟩ : syracuseStep 998607 = 1497911) B1497911
theorem B2243807 : Blo 996598 2243807 := bstep (se 1 (by rfl) ⟨1682855, by rfl⟩ : syracuseStep 2243807 = 3365711) B3365711
theorem B998631 : Blo 996598 998631 := bstep (se 1 (by rfl) ⟨748973, by rfl⟩ : syracuseStep 998631 = 1497947) B1497947
theorem B4799731 : Blo 996598 4799731 := bstep (se 1 (by rfl) ⟨3599798, by rfl⟩ : syracuseStep 4799731 = 7199597) B7199597
theorem B998727 : Blo 996598 998727 := bstep (se 1 (by rfl) ⟨749045, by rfl⟩ : syracuseStep 998727 = 1498091) B1498091
theorem B2244023 : Blo 996598 2244023 := bstep (se 1 (by rfl) ⟨1683017, by rfl⟩ : syracuseStep 2244023 = 3366035) B3366035
theorem B998863 : Blo 996598 998863 := bstep (se 1 (by rfl) ⟨749147, by rfl⟩ : syracuseStep 998863 = 1498295) B1498295
theorem B6405641 : Blo 996598 6405641 := bstep (se 2 (by rfl) ⟨2402115, by rfl⟩ : syracuseStep 6405641 = 4804231) B4804231
theorem B2244203 : Blo 996598 2244203 := bstep (se 1 (by rfl) ⟨1683152, by rfl⟩ : syracuseStep 2244203 = 3366305) B3366305
theorem B999023 : Blo 996598 999023 := bstep (se 1 (by rfl) ⟨749267, by rfl⟩ : syracuseStep 999023 = 1498535) B1498535
theorem B999079 : Blo 996598 999079 := bstep (se 1 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 999079 = 1498619) B1498619
theorem B999143 : Blo 996598 999143 := bstep (se 1 (by rfl) ⟨749357, by rfl⟩ : syracuseStep 999143 = 1498715) B1498715
theorem B999199 : Blo 996598 999199 := bstep (se 1 (by rfl) ⟨749399, by rfl⟩ : syracuseStep 999199 = 1498799) B1498799
theorem B999279 : Blo 996598 999279 := bstep (se 1 (by rfl) ⟨749459, by rfl⟩ : syracuseStep 999279 = 1498919) B1498919
theorem B2244473 : Blo 996598 2244473 := bstep (se 2 (by rfl) ⟨841677, by rfl⟩ : syracuseStep 2244473 = 1683355) B1683355
theorem B999335 : Blo 996598 999335 := bstep (se 1 (by rfl) ⟨749501, by rfl⟩ : syracuseStep 999335 = 1499003) B1499003
theorem B2244563 : Blo 996598 2244563 := bstep (se 1 (by rfl) ⟨1683422, by rfl⟩ : syracuseStep 2244563 = 3366845) B3366845
theorem B999615 : Blo 996598 999615 := bstep (se 1 (by rfl) ⟨749711, by rfl⟩ : syracuseStep 999615 = 1499423) B1499423
theorem B999631 : Blo 996598 999631 := bstep (se 1 (by rfl) ⟨749723, by rfl⟩ : syracuseStep 999631 = 1499447) B1499447
theorem B999679 : Blo 996598 999679 := bstep (se 1 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 999679 = 1499519) B1499519
theorem B999727 : Blo 996598 999727 := bstep (se 1 (by rfl) ⟨749795, by rfl⟩ : syracuseStep 999727 = 1499591) B1499591
theorem B1687979 : Blo 996598 1687979 := bstep (se 1 (by rfl) ⟨1265984, by rfl⟩ : syracuseStep 1687979 = 2531969) B2531969
theorem B999963 : Blo 996598 999963 := bstep (se 1 (by rfl) ⟨749972, by rfl⟩ : syracuseStep 999963 = 1499945) B1499945
theorem B999967 : Blo 996598 999967 := bstep (se 1 (by rfl) ⟨749975, by rfl⟩ : syracuseStep 999967 = 1499951) B1499951
theorem B1000047 : Blo 996598 1000047 := bstep (se 1 (by rfl) ⟨750035, by rfl⟩ : syracuseStep 1000047 = 1500071) B1500071
theorem B1000103 : Blo 996598 1000103 := bstep (se 1 (by rfl) ⟨750077, by rfl⟩ : syracuseStep 1000103 = 1500155) B1500155
theorem B1000143 : Blo 996598 1000143 := bstep (se 1 (by rfl) ⟨750107, by rfl⟩ : syracuseStep 1000143 = 1500215) B1500215
theorem B1000223 : Blo 996598 1000223 := bstep (se 1 (by rfl) ⟨750167, by rfl⟩ : syracuseStep 1000223 = 1500335) B1500335
theorem B1000495 : Blo 996598 1000495 := bstep (se 1 (by rfl) ⟨750371, by rfl⟩ : syracuseStep 1000495 = 1500743) B1500743
theorem B5686361 : Blo 996598 5686361 := bstep (se 2 (by rfl) ⟨2132385, by rfl⟩ : syracuseStep 5686361 = 4264771) B4264771
theorem B1000559 : Blo 996598 1000559 := bstep (se 1 (by rfl) ⟨750419, by rfl⟩ : syracuseStep 1000559 = 1500839) B1500839
theorem B2245823 : Blo 996598 2245823 := bstep (se 1 (by rfl) ⟨1684367, by rfl⟩ : syracuseStep 2245823 = 3368735) B3368735
theorem B2245967 : Blo 996598 2245967 := bstep (se 1 (by rfl) ⟨1684475, by rfl⟩ : syracuseStep 2245967 = 3368951) B3368951
theorem B17286497 : Blo 996598 17286497 := bstep (se 2 (by rfl) ⟨6482436, by rfl⟩ : syracuseStep 17286497 = 12964873) B12964873
theorem B2246057 : Blo 996598 2246057 := bstep (se 2 (by rfl) ⟨842271, by rfl⟩ : syracuseStep 2246057 = 1684543) B1684543
theorem B2311607 : Blo 996598 2311607 := bstep (se 1 (by rfl) ⟨1733705, by rfl⟩ : syracuseStep 2311607 = 3467411) B3467411
theorem B5064119 : Blo 996598 5064119 := bstep (se 1 (by rfl) ⟨3798089, by rfl⟩ : syracuseStep 5064119 = 7596179) B7596179
theorem B9586511 : Blo 996598 9586511 := bstep (se 1 (by rfl) ⟨7189883, by rfl⟩ : syracuseStep 9586511 = 14379767) B14379767
theorem B2246543 : Blo 996598 2246543 := bstep (se 1 (by rfl) ⟨1684907, by rfl⟩ : syracuseStep 2246543 = 3369815) B3369815
theorem B2246687 : Blo 996598 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B2246939 : Blo 996598 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B20531555 : Blo 996598 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B2247263 : Blo 996598 2247263 := bstep (se 1 (by rfl) ⟨1685447, by rfl⟩ : syracuseStep 2247263 = 3370895) B3370895
theorem B61524683 : Blo 996598 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B2247515 : Blo 996598 2247515 := bstep (se 1 (by rfl) ⟨1685636, by rfl⟩ : syracuseStep 2247515 = 3371273) B3371273
theorem B5688251 : Blo 996598 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B4803731 : Blo 996598 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B35999099 : Blo 996598 35999099 := bstep (se 1 (by rfl) ⟨26999324, by rfl⟩ : syracuseStep 35999099 = 53998649) B53998649
theorem B6409687 : Blo 996598 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B3788279 : Blo 996598 3788279 := bstep (se 1 (by rfl) ⟨2841209, by rfl⟩ : syracuseStep 3788279 = 5682419) B5682419
theorem B2248271 : Blo 996598 2248271 := bstep (se 1 (by rfl) ⟨1686203, by rfl⟩ : syracuseStep 2248271 = 3372407) B3372407
theorem B561303341 : Blo 996598 561303341 := bstep (se 3 (by rfl) ⟨105244376, by rfl⟩ : syracuseStep 561303341 = 210488753) B210488753
theorem B1494911 : Blo 996598 1494911 := bstep (se 1 (by rfl) ⟨1121183, by rfl⟩ : syracuseStep 1494911 = 2242367) B2242367
theorem B3198847 : Blo 996598 3198847 := bstep (se 1 (by rfl) ⟨2399135, by rfl⟩ : syracuseStep 3198847 = 4798271) B4798271
theorem B7589861 : Blo 996598 7589861 := bstep (se 4 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 7589861 = 1423099) B1423099
theorem B3788795 : Blo 996598 3788795 := bstep (se 1 (by rfl) ⟨2841596, by rfl⟩ : syracuseStep 3788795 = 5683193) B5683193
theorem B6410279 : Blo 996598 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B1495103 : Blo 996598 1495103 := bstep (se 1 (by rfl) ⟨1121327, by rfl⟩ : syracuseStep 1495103 = 2242655) B2242655
theorem B2248811 : Blo 996598 2248811 := bstep (se 1 (by rfl) ⟨1686608, by rfl⟩ : syracuseStep 2248811 = 3373217) B3373217
theorem B2248865 : Blo 996598 2248865 := bstep (se 2 (by rfl) ⟨843324, by rfl⟩ : syracuseStep 2248865 = 1686649) B1686649
theorem B2248991 : Blo 996598 2248991 := bstep (se 1 (by rfl) ⟨1686743, by rfl⟩ : syracuseStep 2248991 = 3373487) B3373487
theorem B1495337 : Blo 996598 1495337 := bstep (se 2 (by rfl) ⟨560751, by rfl⟩ : syracuseStep 1495337 = 1121503) B1121503
theorem B1495607 : Blo 996598 1495607 := bstep (se 1 (by rfl) ⟨1121705, by rfl⟩ : syracuseStep 1495607 = 2243411) B2243411
theorem B3789449 : Blo 996598 3789449 := bstep (se 2 (by rfl) ⟨1421043, by rfl⟩ : syracuseStep 3789449 = 2842087) B2842087
theorem B2839387 : Blo 996598 2839387 := bstep (se 1 (by rfl) ⟨2129540, by rfl⟩ : syracuseStep 2839387 = 4259081) B4259081
theorem B1495967 : Blo 996598 1495967 := bstep (se 1 (by rfl) ⟨1121975, by rfl⟩ : syracuseStep 1495967 = 2243951) B2243951
theorem B2249711 : Blo 996598 2249711 := bstep (se 1 (by rfl) ⟨1687283, by rfl⟩ : syracuseStep 2249711 = 3374567) B3374567
theorem B1496159 : Blo 996598 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B1496219 : Blo 996598 1496219 := bstep (se 1 (by rfl) ⟨1122164, by rfl⟩ : syracuseStep 1496219 = 2244329) B2244329
theorem B2250215 : Blo 996598 2250215 := bstep (se 1 (by rfl) ⟨1687661, by rfl⟩ : syracuseStep 2250215 = 3375323) B3375323
theorem B2250377 : Blo 996598 2250377 := bstep (se 2 (by rfl) ⟨843891, by rfl⟩ : syracuseStep 2250377 = 1687783) B1687783
theorem B2250395 : Blo 996598 2250395 := bstep (se 1 (by rfl) ⟨1687796, by rfl⟩ : syracuseStep 2250395 = 3375593) B3375593
theorem B1496903 : Blo 996598 1496903 := bstep (se 1 (by rfl) ⟨1122677, by rfl⟩ : syracuseStep 1496903 = 2245355) B2245355
theorem B2250593 : Blo 996598 2250593 := bstep (se 2 (by rfl) ⟨843972, by rfl⟩ : syracuseStep 2250593 = 1687945) B1687945
theorem B2250791 : Blo 996598 2250791 := bstep (se 1 (by rfl) ⟨1688093, by rfl⟩ : syracuseStep 2250791 = 3376187) B3376187
theorem B2250971 : Blo 996598 2250971 := bstep (se 1 (by rfl) ⟨1688228, by rfl⟩ : syracuseStep 2250971 = 3376457) B3376457
theorem B3365279 : Blo 996598 3365279 := bstep (se 1 (by rfl) ⟨2523959, by rfl⟩ : syracuseStep 3365279 = 5047919) B5047919
theorem B1497503 : Blo 996598 1497503 := bstep (se 1 (by rfl) ⟨1123127, by rfl⟩ : syracuseStep 1497503 = 2246255) B2246255
theorem B2251169 : Blo 996598 2251169 := bstep (se 2 (by rfl) ⟨844188, by rfl⟩ : syracuseStep 2251169 = 1688377) B1688377
theorem B1497575 : Blo 996598 1497575 := bstep (se 1 (by rfl) ⟨1123181, by rfl⟩ : syracuseStep 1497575 = 2246363) B2246363
theorem B2251241 : Blo 996598 2251241 := bstep (se 2 (by rfl) ⟨844215, by rfl⟩ : syracuseStep 2251241 = 1688431) B1688431
theorem B3201563 : Blo 996598 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B26270569 : Blo 996598 26270569 := bstep (se 2 (by rfl) ⟨9851463, by rfl⟩ : syracuseStep 26270569 = 19702927) B19702927
theorem B1498319 : Blo 996598 1498319 := bstep (se 1 (by rfl) ⟨1123739, by rfl⟩ : syracuseStep 1498319 = 2247479) B2247479
theorem B1498439 : Blo 996598 1498439 := bstep (se 1 (by rfl) ⟨1123829, by rfl⟩ : syracuseStep 1498439 = 2247659) B2247659
theorem B3366251 : Blo 996598 3366251 := bstep (se 1 (by rfl) ⟨2524688, by rfl⟩ : syracuseStep 3366251 = 5049377) B5049377
theorem B1498601 : Blo 996598 1498601 := bstep (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) B1123951
theorem B3366521 : Blo 996598 3366521 := bstep (se 2 (by rfl) ⟨1262445, by rfl⟩ : syracuseStep 3366521 = 2524891) B2524891
theorem B1498745 : Blo 996598 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B2023265 : Blo 996598 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B1498991 : Blo 996598 1498991 := bstep (se 1 (by rfl) ⟨1124243, by rfl⟩ : syracuseStep 1498991 = 2248487) B2248487
theorem B4120475 : Blo 996598 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B3366899 : Blo 996598 3366899 := bstep (se 1 (by rfl) ⟨2525174, by rfl⟩ : syracuseStep 3366899 = 5050349) B5050349
theorem B12804155 : Blo 996598 12804155 := bstep (se 1 (by rfl) ⟨9603116, by rfl⟩ : syracuseStep 12804155 = 19206233) B19206233
theorem B5759261 : Blo 996598 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B3367439 : Blo 996598 3367439 := bstep (se 1 (by rfl) ⟨2525579, by rfl⟩ : syracuseStep 3367439 = 5051159) B5051159
theorem B1499675 : Blo 996598 1499675 := bstep (se 1 (by rfl) ⟨1124756, by rfl⟩ : syracuseStep 1499675 = 2249513) B2249513
theorem B1499855 : Blo 996598 1499855 := bstep (se 1 (by rfl) ⟨1124891, by rfl⟩ : syracuseStep 1499855 = 2249783) B2249783
theorem B1499867 : Blo 996598 1499867 := bstep (se 1 (by rfl) ⟨1124900, by rfl⟩ : syracuseStep 1499867 = 2249801) B2249801
theorem B1893449 : Blo 996598 1893449 := bstep (se 2 (by rfl) ⟨710043, by rfl⟩ : syracuseStep 1893449 = 1420087) B1420087
theorem B1500281 : Blo 996598 1500281 := bstep (se 2 (by rfl) ⟨562605, by rfl⟩ : syracuseStep 1500281 = 1125211) B1125211
theorem B17032355 : Blo 996598 17032355 := bstep (se 1 (by rfl) ⟨12774266, by rfl⟩ : syracuseStep 17032355 = 25548533) B25548533
theorem B3368249 : Blo 996598 3368249 := bstep (se 2 (by rfl) ⟨1263093, by rfl⟩ : syracuseStep 3368249 = 2526187) B2526187
theorem B3368519 : Blo 996598 3368519 := bstep (se 1 (by rfl) ⟨2526389, by rfl⟩ : syracuseStep 3368519 = 5052779) B5052779
theorem B3368573 : Blo 996598 3368573 := bstep (se 3 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 3368573 = 1263215) B1263215
theorem B4056911 : Blo 996598 4056911 := bstep (se 1 (by rfl) ⟨3042683, by rfl⟩ : syracuseStep 4056911 = 6085367) B6085367
theorem B3368843 : Blo 996598 3368843 := bstep (se 1 (by rfl) ⟨2526632, by rfl⟩ : syracuseStep 3368843 = 5053265) B5053265
theorem B1894367 : Blo 996598 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B3369491 : Blo 996598 3369491 := bstep (se 1 (by rfl) ⟨2527118, by rfl⟩ : syracuseStep 3369491 = 5054237) B5054237
theorem B1010279 : Blo 996598 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B36432773 : Blo 996598 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B3796253 : Blo 996598 3796253 := bstep (se 3 (by rfl) ⟨711797, by rfl⟩ : syracuseStep 3796253 = 1423595) B1423595
theorem B3370463 : Blo 996598 3370463 := bstep (se 1 (by rfl) ⟨2527847, by rfl⟩ : syracuseStep 3370463 = 5055695) B5055695
theorem B2846279 : Blo 996598 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B3796571 : Blo 996598 3796571 := bstep (se 1 (by rfl) ⟨2847428, by rfl⟩ : syracuseStep 3796571 = 5694857) B5694857
theorem B9597001 : Blo 996598 9597001 := bstep (se 2 (by rfl) ⟨3598875, by rfl⟩ : syracuseStep 9597001 = 7197751) B7197751
theorem B3797225 : Blo 996598 3797225 := bstep (se 2 (by rfl) ⟨1423959, by rfl⟩ : syracuseStep 3797225 = 2847919) B2847919
theorem B23065469 : Blo 996598 23065469 := bstep (se 3 (by rfl) ⟨4324775, by rfl⟩ : syracuseStep 23065469 = 8649551) B8649551
theorem B2847737 : Blo 996598 2847737 := bstep (se 2 (by rfl) ⟨1067901, by rfl⟩ : syracuseStep 2847737 = 2135803) B2135803
theorem B184251743 : Blo 996598 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B12810149 : Blo 996598 12810149 := bstep (se 4 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 12810149 = 2401903) B2401903
theorem B7698341 : Blo 996598 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B32405447 : Blo 996598 32405447 := bstep (se 1 (by rfl) ⟨24304085, by rfl⟩ : syracuseStep 32405447 = 48608171) B48608171
theorem B14383169 : Blo 996598 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B4257953 : Blo 996598 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B23066939 : Blo 996598 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B8518607 : Blo 996598 8518607 := bstep (se 1 (by rfl) ⟨6388955, by rfl⟩ : syracuseStep 8518607 = 12777911) B12777911
theorem B2522735 : Blo 996598 2522735 := bstep (se 1 (by rfl) ⟨1892051, by rfl⟩ : syracuseStep 2522735 = 3784103) B3784103
theorem B1539695 : Blo 996598 1539695 := bstep (se 1 (by rfl) ⟨1154771, by rfl⟩ : syracuseStep 1539695 = 2309543) B2309543
theorem B4554575 : Blo 996598 4554575 := bstep (se 1 (by rfl) ⟨3415931, by rfl⟩ : syracuseStep 4554575 = 6831863) B6831863
theorem B2129831 : Blo 996598 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B2883833 : Blo 996598 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B2851609 : Blo 996598 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B7308089 : Blo 996598 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B1541071 : Blo 996598 1541071 := bstep (se 1 (by rfl) ⟨1155803, by rfl⟩ : syracuseStep 1541071 = 2311607) B2311607
theorem B3376079 : Blo 996598 3376079 := bstep (se 1 (by rfl) ⟨2532059, by rfl⟩ : syracuseStep 3376079 = 5064119) B5064119
theorem B6391007 : Blo 996598 6391007 := bstep (se 1 (by rfl) ⟨4793255, by rfl⟩ : syracuseStep 6391007 = 9586511) B9586511
theorem B24249593 : Blo 996598 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B8521919 : Blo 996598 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B2525519 : Blo 996598 2525519 := bstep (se 1 (by rfl) ⟨1894139, by rfl⟩ : syracuseStep 2525519 = 3788279) B3788279
theorem B7211359 : Blo 996598 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B2525863 : Blo 996598 2525863 := bstep (se 1 (by rfl) ⟨1894397, by rfl⟩ : syracuseStep 2525863 = 3788795) B3788795
theorem B12815273 : Blo 996598 12815273 := bstep (se 2 (by rfl) ⟨4805727, by rfl⟩ : syracuseStep 12815273 = 9611455) B9611455
theorem B2526299 : Blo 996598 2526299 := bstep (se 1 (by rfl) ⟨1894724, by rfl⟩ : syracuseStep 2526299 = 3789449) B3789449
theorem B4265129 : Blo 996598 4265129 := bstep (se 2 (by rfl) ⟨1599423, by rfl⟩ : syracuseStep 4265129 = 3198847) B3198847
theorem B5051645 : Blo 996598 5051645 := bstep (se 3 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 5051645 = 1894367) B1894367
theorem B3839507 : Blo 996598 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B86447735 : Blo 996598 86447735 := bstep (se 1 (by rfl) ⟨64835801, by rfl⟩ : syracuseStep 86447735 = 129671603) B129671603
theorem B10229975 : Blo 996598 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B2694077 : Blo 996598 2694077 := bstep (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) B1010279
theorem B24288515 : Blo 996598 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B8527355 : Blo 996598 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B2530835 : Blo 996598 2530835 := bstep (se 1 (by rfl) ⟨1898126, by rfl⟩ : syracuseStep 2530835 = 3796253) B3796253
theorem B2531047 : Blo 996598 2531047 := bstep (se 1 (by rfl) ⟨1898285, by rfl⟩ : syracuseStep 2531047 = 3796571) B3796571
theorem B2563919 : Blo 996598 2563919 := bstep (se 1 (by rfl) ⟨1922939, by rfl⟩ : syracuseStep 2563919 = 3845879) B3845879
theorem B2531483 : Blo 996598 2531483 := bstep (se 1 (by rfl) ⟨1898612, by rfl⟩ : syracuseStep 2531483 = 3797225) B3797225
theorem B15376979 : Blo 996598 15376979 := bstep (se 1 (by rfl) ⟨11532734, by rfl⟩ : syracuseStep 15376979 = 23065469) B23065469
theorem B1122907 : Blo 996598 1122907 := bstep (se 1 (by rfl) ⟨842180, by rfl⟩ : syracuseStep 1122907 = 1684361) B1684361
theorem B7185185 : Blo 996598 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B1123483 : Blo 996598 1123483 := bstep (se 1 (by rfl) ⟨842612, by rfl⟩ : syracuseStep 1123483 = 1685225) B1685225
theorem B21603631 : Blo 996598 21603631 := bstep (se 1 (by rfl) ⟨16202723, by rfl⟩ : syracuseStep 21603631 = 32405447) B32405447
theorem B5056019 : Blo 996598 5056019 := bstep (se 1 (by rfl) ⟨3792014, by rfl⟩ : syracuseStep 5056019 = 7584029) B7584029
theorem B15377959 : Blo 996598 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B6399641 : Blo 996598 6399641 := bstep (se 2 (by rfl) ⟨2399865, by rfl⟩ : syracuseStep 6399641 = 4799731) B4799731
theorem B4269743 : Blo 996598 4269743 := bstep (se 1 (by rfl) ⟨3202307, by rfl⟩ : syracuseStep 4269743 = 6404615) B6404615
theorem B1124167 : Blo 996598 1124167 := bstep (se 1 (by rfl) ⟨843125, by rfl⟩ : syracuseStep 1124167 = 1686251) B1686251
theorem B5679071 : Blo 996598 5679071 := bstep (se 1 (by rfl) ⟨4259303, by rfl⟩ : syracuseStep 5679071 = 8518607) B8518607
theorem B4270427 : Blo 996598 4270427 := bstep (se 1 (by rfl) ⟨3202820, by rfl⟩ : syracuseStep 4270427 = 6405641) B6405641
theorem B10987933 : Blo 996598 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B1681823 : Blo 996598 1681823 := bstep (se 1 (by rfl) ⟨1261367, by rfl⟩ : syracuseStep 1681823 = 2522735) B2522735
theorem B1026463 : Blo 996598 1026463 := bstep (se 1 (by rfl) ⟨769847, by rfl⟩ : syracuseStep 1026463 = 1539695) B1539695
theorem B1419887 : Blo 996598 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B1125319 : Blo 996598 1125319 := bstep (se 1 (by rfl) ⟨843989, by rfl⟩ : syracuseStep 1125319 = 1687979) B1687979
theorem B1682815 : Blo 996598 1682815 := bstep (se 1 (by rfl) ⟨1262111, by rfl⟩ : syracuseStep 1682815 = 2524223) B2524223
theorem B7188587 : Blo 996598 7188587 := bstep (se 1 (by rfl) ⟨5391440, by rfl⟩ : syracuseStep 7188587 = 10782881) B10782881
theorem B9613687 : Blo 996598 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B23999399 : Blo 996598 23999399 := bstep (se 1 (by rfl) ⟨17999549, by rfl⟩ : syracuseStep 23999399 = 35999099) B35999099
theorem B996607 : Blo 996598 996607 := bstep (se 1 (by rfl) ⟨747455, by rfl⟩ : syracuseStep 996607 = 1494911) B1494911
theorem B5059907 : Blo 996598 5059907 := bstep (se 1 (by rfl) ⟨3794930, by rfl⟩ : syracuseStep 5059907 = 7589861) B7589861
theorem B4273519 : Blo 996598 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B996735 : Blo 996598 996735 := bstep (se 1 (by rfl) ⟨747551, by rfl⟩ : syracuseStep 996735 = 1495103) B1495103
theorem B996891 : Blo 996598 996891 := bstep (se 1 (by rfl) ⟨747668, by rfl⟩ : syracuseStep 996891 = 1495337) B1495337
theorem B1423003 : Blo 996598 1423003 := bstep (se 1 (by rfl) ⟨1067252, by rfl⟩ : syracuseStep 1423003 = 2134505) B2134505
theorem B997071 : Blo 996598 997071 := bstep (se 1 (by rfl) ⟨747803, by rfl⟩ : syracuseStep 997071 = 1495607) B1495607
theorem B997311 : Blo 996598 997311 := bstep (se 1 (by rfl) ⟨747983, by rfl⟩ : syracuseStep 997311 = 1495967) B1495967
theorem B997439 : Blo 996598 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B997479 : Blo 996598 997479 := bstep (se 1 (by rfl) ⟨748109, by rfl⟩ : syracuseStep 997479 = 1496219) B1496219
theorem B997935 : Blo 996598 997935 := bstep (se 1 (by rfl) ⟨748451, by rfl⟩ : syracuseStep 997935 = 1496903) B1496903
theorem B2243519 : Blo 996598 2243519 := bstep (se 1 (by rfl) ⟨1682639, by rfl⟩ : syracuseStep 2243519 = 3365279) B3365279
theorem B998335 : Blo 996598 998335 := bstep (se 1 (by rfl) ⟨748751, by rfl⟩ : syracuseStep 998335 = 1497503) B1497503
theorem B998383 : Blo 996598 998383 := bstep (se 1 (by rfl) ⟨748787, by rfl⟩ : syracuseStep 998383 = 1497575) B1497575
theorem B5684651 : Blo 996598 5684651 := bstep (se 1 (by rfl) ⟨4263488, by rfl⟩ : syracuseStep 5684651 = 8526977) B8526977
theorem B998879 : Blo 996598 998879 := bstep (se 1 (by rfl) ⟨749159, by rfl⟩ : syracuseStep 998879 = 1498319) B1498319
theorem B1687007 : Blo 996598 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B998959 : Blo 996598 998959 := bstep (se 1 (by rfl) ⟨749219, by rfl⟩ : syracuseStep 998959 = 1498439) B1498439
theorem B2244167 : Blo 996598 2244167 := bstep (se 1 (by rfl) ⟨1683125, by rfl⟩ : syracuseStep 2244167 = 3366251) B3366251
theorem B999067 : Blo 996598 999067 := bstep (se 1 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 999067 = 1498601) B1498601
theorem B2244347 : Blo 996598 2244347 := bstep (se 1 (by rfl) ⟨1683260, by rfl⟩ : syracuseStep 2244347 = 3366521) B3366521
theorem B999163 : Blo 996598 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B20528909 : Blo 996598 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B999327 : Blo 996598 999327 := bstep (se 1 (by rfl) ⟨749495, by rfl⟩ : syracuseStep 999327 = 1498991) B1498991
theorem B2244599 : Blo 996598 2244599 := bstep (se 1 (by rfl) ⟨1683449, by rfl⟩ : syracuseStep 2244599 = 3366899) B3366899
theorem B8536103 : Blo 996598 8536103 := bstep (se 1 (by rfl) ⟨6402077, by rfl⟩ : syracuseStep 8536103 = 12804155) B12804155
theorem B1949779 : Blo 996598 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B12796001 : Blo 996598 12796001 := bstep (se 2 (by rfl) ⟨4798500, by rfl⟩ : syracuseStep 12796001 = 9597001) B9597001
theorem B2244959 : Blo 996598 2244959 := bstep (se 1 (by rfl) ⟨1683719, by rfl⟩ : syracuseStep 2244959 = 3367439) B3367439
theorem B999783 : Blo 996598 999783 := bstep (se 1 (by rfl) ⟨749837, by rfl⟩ : syracuseStep 999783 = 1499675) B1499675
theorem B999903 : Blo 996598 999903 := bstep (se 1 (by rfl) ⟨749927, by rfl⟩ : syracuseStep 999903 = 1499855) B1499855
theorem B999911 : Blo 996598 999911 := bstep (se 1 (by rfl) ⟨749933, by rfl⟩ : syracuseStep 999911 = 1499867) B1499867
theorem B6078995 : Blo 996598 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B1262299 : Blo 996598 1262299 := bstep (se 1 (by rfl) ⟨946724, by rfl⟩ : syracuseStep 1262299 = 1893449) B1893449
theorem B1000187 : Blo 996598 1000187 := bstep (se 1 (by rfl) ⟨750140, by rfl⟩ : syracuseStep 1000187 = 1500281) B1500281
theorem B11354903 : Blo 996598 11354903 := bstep (se 1 (by rfl) ⟨8516177, by rfl⟩ : syracuseStep 11354903 = 17032355) B17032355
theorem B2245499 : Blo 996598 2245499 := bstep (se 1 (by rfl) ⟨1684124, by rfl⟩ : syracuseStep 2245499 = 3368249) B3368249
theorem B17318785 : Blo 996598 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B2245625 : Blo 996598 2245625 := bstep (se 2 (by rfl) ⟨842109, by rfl⟩ : syracuseStep 2245625 = 1684219) B1684219
theorem B2245679 : Blo 996598 2245679 := bstep (se 1 (by rfl) ⟨1684259, by rfl⟩ : syracuseStep 2245679 = 3368519) B3368519
theorem B2245715 : Blo 996598 2245715 := bstep (se 1 (by rfl) ⟨1684286, by rfl⟩ : syracuseStep 2245715 = 3368573) B3368573
theorem B3785849 : Blo 996598 3785849 := bstep (se 2 (by rfl) ⟨1419693, by rfl⟩ : syracuseStep 3785849 = 2839387) B2839387
theorem B2704607 : Blo 996598 2704607 := bstep (se 1 (by rfl) ⟨2028455, by rfl⟩ : syracuseStep 2704607 = 4056911) B4056911
theorem B2245895 : Blo 996598 2245895 := bstep (se 1 (by rfl) ⟨1684421, by rfl⟩ : syracuseStep 2245895 = 3368843) B3368843
theorem B43763095 : Blo 996598 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B8537501 : Blo 996598 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B2246327 : Blo 996598 2246327 := bstep (se 1 (by rfl) ⟨1684745, by rfl⟩ : syracuseStep 2246327 = 3369491) B3369491
theorem B2246777 : Blo 996598 2246777 := bstep (se 2 (by rfl) ⟨842541, by rfl⟩ : syracuseStep 2246777 = 1685083) B1685083
theorem B2246975 : Blo 996598 2246975 := bstep (se 1 (by rfl) ⟨1685231, by rfl⟩ : syracuseStep 2246975 = 3370463) B3370463
theorem B6474593 : Blo 996598 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B3787991 : Blo 996598 3787991 := bstep (se 1 (by rfl) ⟨2840993, by rfl⟩ : syracuseStep 3787991 = 5681987) B5681987
theorem B122834495 : Blo 996598 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B5689277 : Blo 996598 5689277 := bstep (se 3 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 5689277 = 2133479) B2133479
theorem B8540099 : Blo 996598 8540099 := bstep (se 1 (by rfl) ⟨6405074, by rfl⟩ : syracuseStep 8540099 = 12810149) B12810149
theorem B1494983 : Blo 996598 1494983 := bstep (se 1 (by rfl) ⟨1121237, by rfl⟩ : syracuseStep 1494983 = 2242475) B2242475
theorem B1495067 : Blo 996598 1495067 := bstep (se 1 (by rfl) ⟨1121300, by rfl⟩ : syracuseStep 1495067 = 2242601) B2242601
theorem B9588779 : Blo 996598 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B2838635 : Blo 996598 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B3199103 : Blo 996598 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B1495343 : Blo 996598 1495343 := bstep (se 1 (by rfl) ⟨1121507, by rfl⟩ : syracuseStep 1495343 = 2243015) B2243015
theorem B1495451 : Blo 996598 1495451 := bstep (se 1 (by rfl) ⟨1121588, by rfl⟩ : syracuseStep 1495451 = 2243177) B2243177
theorem B1495487 : Blo 996598 1495487 := bstep (se 1 (by rfl) ⟨1121615, by rfl⟩ : syracuseStep 1495487 = 2243231) B2243231
theorem B1495583 : Blo 996598 1495583 := bstep (se 1 (by rfl) ⟨1121687, by rfl⟩ : syracuseStep 1495583 = 2243375) B2243375
theorem B1495871 : Blo 996598 1495871 := bstep (se 1 (by rfl) ⟨1121903, by rfl⟩ : syracuseStep 1495871 = 2243807) B2243807
theorem B5395373 : Blo 996598 5395373 := bstep (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) B2023265
theorem B1496015 : Blo 996598 1496015 := bstep (se 1 (by rfl) ⟨1122011, by rfl⟩ : syracuseStep 1496015 = 2244023) B2244023
theorem B1496105 : Blo 996598 1496105 := bstep (se 2 (by rfl) ⟨561039, by rfl⟩ : syracuseStep 1496105 = 1122079) B1122079
theorem B1496135 : Blo 996598 1496135 := bstep (se 1 (by rfl) ⟨1122101, by rfl⟩ : syracuseStep 1496135 = 2244203) B2244203
theorem B3036383 : Blo 996598 3036383 := bstep (se 1 (by rfl) ⟨2277287, by rfl⟩ : syracuseStep 3036383 = 4554575) B4554575
theorem B1496315 : Blo 996598 1496315 := bstep (se 1 (by rfl) ⟨1122236, by rfl⟩ : syracuseStep 1496315 = 2244473) B2244473
theorem B1496375 : Blo 996598 1496375 := bstep (se 1 (by rfl) ⟨1122281, by rfl⟩ : syracuseStep 1496375 = 2244563) B2244563
theorem B1496681 : Blo 996598 1496681 := bstep (se 2 (by rfl) ⟨561255, by rfl⟩ : syracuseStep 1496681 = 1122511) B1122511
theorem B2250431 : Blo 996598 2250431 := bstep (se 1 (by rfl) ⟨1687823, by rfl⟩ : syracuseStep 2250431 = 3375647) B3375647
theorem B3200897 : Blo 996598 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B3790907 : Blo 996598 3790907 := bstep (se 1 (by rfl) ⟨2843180, by rfl⟩ : syracuseStep 3790907 = 5686361) B5686361
theorem B1497215 : Blo 996598 1497215 := bstep (se 1 (by rfl) ⟨1122911, by rfl⟩ : syracuseStep 1497215 = 2245823) B2245823
theorem B1497311 : Blo 996598 1497311 := bstep (se 1 (by rfl) ⟨1122983, by rfl⟩ : syracuseStep 1497311 = 2245967) B2245967
theorem B11524331 : Blo 996598 11524331 := bstep (se 1 (by rfl) ⟨8643248, by rfl⟩ : syracuseStep 11524331 = 17286497) B17286497
theorem B1497371 : Blo 996598 1497371 := bstep (se 1 (by rfl) ⟨1123028, by rfl⟩ : syracuseStep 1497371 = 2246057) B2246057
theorem B2841095 : Blo 996598 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B1497695 : Blo 996598 1497695 := bstep (se 1 (by rfl) ⟨1123271, by rfl⟩ : syracuseStep 1497695 = 2246543) B2246543
theorem B1497791 : Blo 996598 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B1497833 : Blo 996598 1497833 := bstep (se 2 (by rfl) ⟨561687, by rfl⟩ : syracuseStep 1497833 = 1123375) B1123375
theorem B9100025 : Blo 996598 9100025 := bstep (se 2 (by rfl) ⟨3412509, by rfl⟩ : syracuseStep 9100025 = 6825019) B6825019
theorem B4807421 : Blo 996598 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B1497959 : Blo 996598 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B13687703 : Blo 996598 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B1498025 : Blo 996598 1498025 := bstep (se 2 (by rfl) ⟨561759, by rfl⟩ : syracuseStep 1498025 = 1123519) B1123519
theorem B8870951 : Blo 996598 8870951 := bstep (se 1 (by rfl) ⟨6653213, by rfl⟩ : syracuseStep 8870951 = 13306427) B13306427
theorem B1498175 : Blo 996598 1498175 := bstep (se 1 (by rfl) ⟨1123631, by rfl⟩ : syracuseStep 1498175 = 2247263) B2247263
theorem B1498217 : Blo 996598 1498217 := bstep (se 2 (by rfl) ⟨561831, by rfl⟩ : syracuseStep 1498217 = 1123663) B1123663
theorem B41016455 : Blo 996598 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B1498343 : Blo 996598 1498343 := bstep (se 1 (by rfl) ⟨1123757, by rfl⟩ : syracuseStep 1498343 = 2247515) B2247515
theorem B3792167 : Blo 996598 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B3202487 : Blo 996598 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B1498847 : Blo 996598 1498847 := bstep (se 1 (by rfl) ⟨1124135, by rfl⟩ : syracuseStep 1498847 = 2248271) B2248271
theorem B374202227 : Blo 996598 374202227 := bstep (se 1 (by rfl) ⟨280651670, by rfl⟩ : syracuseStep 374202227 = 561303341) B561303341
theorem B1499177 : Blo 996598 1499177 := bstep (se 2 (by rfl) ⟨562191, by rfl⟩ : syracuseStep 1499177 = 1124383) B1124383
theorem B20537387 : Blo 996598 20537387 := bstep (se 1 (by rfl) ⟨15403040, by rfl⟩ : syracuseStep 20537387 = 30806081) B30806081
theorem B1499207 : Blo 996598 1499207 := bstep (se 1 (by rfl) ⟨1124405, by rfl⟩ : syracuseStep 1499207 = 2248811) B2248811
theorem B25976909 : Blo 996598 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B1499243 : Blo 996598 1499243 := bstep (se 1 (by rfl) ⟨1124432, by rfl⟩ : syracuseStep 1499243 = 2248865) B2248865
theorem B1499327 : Blo 996598 1499327 := bstep (se 1 (by rfl) ⟨1124495, by rfl⟩ : syracuseStep 1499327 = 2248991) B2248991
theorem B1499513 : Blo 996598 1499513 := bstep (se 2 (by rfl) ⟨562317, by rfl⟩ : syracuseStep 1499513 = 1124635) B1124635
theorem B2843191 : Blo 996598 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B5399095 : Blo 996598 5399095 := bstep (se 1 (by rfl) ⟨4049321, by rfl⟩ : syracuseStep 5399095 = 8098643) B8098643
theorem B1499807 : Blo 996598 1499807 := bstep (se 1 (by rfl) ⟨1124855, by rfl⟩ : syracuseStep 1499807 = 2249711) B2249711
theorem B1500143 : Blo 996598 1500143 := bstep (se 1 (by rfl) ⟨1125107, by rfl⟩ : syracuseStep 1500143 = 2250215) B2250215
theorem B1500251 : Blo 996598 1500251 := bstep (se 1 (by rfl) ⟨1125188, by rfl⟩ : syracuseStep 1500251 = 2250377) B2250377
theorem B1500263 : Blo 996598 1500263 := bstep (se 1 (by rfl) ⟨1125197, by rfl⟩ : syracuseStep 1500263 = 2250395) B2250395
theorem B1500395 : Blo 996598 1500395 := bstep (se 1 (by rfl) ⟨1125296, by rfl⟩ : syracuseStep 1500395 = 2250593) B2250593
theorem B11363651 : Blo 996598 11363651 := bstep (se 1 (by rfl) ⟨8522738, by rfl⟩ : syracuseStep 11363651 = 17045477) B17045477
theorem B1500527 : Blo 996598 1500527 := bstep (se 1 (by rfl) ⟨1125395, by rfl⟩ : syracuseStep 1500527 = 2250791) B2250791
theorem B1500647 : Blo 996598 1500647 := bstep (se 1 (by rfl) ⟨1125485, by rfl⟩ : syracuseStep 1500647 = 2250971) B2250971
theorem B1500779 : Blo 996598 1500779 := bstep (se 1 (by rfl) ⟨1125584, by rfl⟩ : syracuseStep 1500779 = 2251169) B2251169
theorem B1500827 : Blo 996598 1500827 := bstep (se 1 (by rfl) ⟨1125620, by rfl⟩ : syracuseStep 1500827 = 2251241) B2251241
theorem B8546249 : Blo 996598 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B1895393 : Blo 996598 1895393 := bstep (se 2 (by rfl) ⟨710772, by rfl⟩ : syracuseStep 1895393 = 1421545) B1421545
theorem B2846107 : Blo 996598 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B10252307 : Blo 996598 10252307 := bstep (se 1 (by rfl) ⟨7689230, by rfl⟩ : syracuseStep 10252307 = 15378461) B15378461
theorem B2846927 : Blo 996598 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B1897519 : Blo 996598 1897519 := bstep (se 1 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 1897519 = 2846279) B2846279
theorem B10253947 : Blo 996598 10253947 := bstep (se 1 (by rfl) ⟨7690460, by rfl⟩ : syracuseStep 10253947 = 15380921) B15380921
theorem B1898491 : Blo 996598 1898491 := bstep (se 1 (by rfl) ⟨1423868, by rfl⟩ : syracuseStep 1898491 = 2847737) B2847737
theorem B35027425 : Blo 996598 35027425 := bstep (se 2 (by rfl) ⟨13135284, by rfl⟩ : syracuseStep 35027425 = 26270569) B26270569
theorem B3373595 : Blo 996598 3373595 := bstep (se 1 (by rfl) ⟨2530196, by rfl⟩ : syracuseStep 3373595 = 5060393) B5060393
theorem B1800967 : Blo 996598 1800967 := bstep (se 1 (by rfl) ⟨1350725, by rfl⟩ : syracuseStep 1800967 = 2701451) B2701451
theorem B415464389 : Blo 996598 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B8092871 : Blo 996598 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B3374459 : Blo 996598 3374459 := bstep (se 1 (by rfl) ⟨2530844, by rfl⟩ : syracuseStep 3374459 = 5061689) B5061689
theorem B69271757 : Blo 996598 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B7569935 : Blo 996598 7569935 := bstep (se 1 (by rfl) ⟨5677451, by rfl⟩ : syracuseStep 7569935 = 11354903) B11354903
theorem B2523899 : Blo 996598 2523899 := bstep (se 1 (by rfl) ⟨1892924, by rfl⟩ : syracuseStep 2523899 = 3785849) B3785849
theorem B4260671 : Blo 996598 4260671 := bstep (se 1 (by rfl) ⟨3195503, by rfl⟩ : syracuseStep 4260671 = 6391007) B6391007
theorem B1803071 : Blo 996598 1803071 := bstep (se 1 (by rfl) ⟨1352303, by rfl⟩ : syracuseStep 1803071 = 2704607) B2704607
theorem B3802145 : Blo 996598 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B28804841 : Blo 996598 28804841 := bstep (se 2 (by rfl) ⟨10801815, by rfl⟩ : syracuseStep 28804841 = 21603631) B21603631
theorem B2525327 : Blo 996598 2525327 := bstep (se 1 (by rfl) ⟨1893995, by rfl⟩ : syracuseStep 2525327 = 3787991) B3787991
theorem B81889663 : Blo 996598 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B6392519 : Blo 996598 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B2132735 : Blo 996598 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B14650577 : Blo 996598 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B2559671 : Blo 996598 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B2527271 : Blo 996598 2527271 := bstep (se 1 (by rfl) ⟨1895453, by rfl⟩ : syracuseStep 2527271 = 3790907) B3790907
theorem B6819983 : Blo 996598 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B6066683 : Blo 996598 6066683 := bstep (se 1 (by rfl) ⟨4550012, by rfl⟩ : syracuseStep 6066683 = 9100025) B9100025
theorem B16192343 : Blo 996598 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B2528111 : Blo 996598 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B2134991 : Blo 996598 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B1709279 : Blo 996598 1709279 := bstep (se 1 (by rfl) ⟨1281959, by rfl⟩ : syracuseStep 1709279 = 2563919) B2563919
theorem B12818249 : Blo 996598 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B4790123 : Blo 996598 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B7575767 : Blo 996598 7575767 := bstep (se 1 (by rfl) ⟨5681825, by rfl⟩ : syracuseStep 7575767 = 11363651) B11363651
theorem B4266427 : Blo 996598 4266427 := bstep (se 1 (by rfl) ⟨3199820, by rfl⟩ : syracuseStep 4266427 = 6399641) B6399641
theorem B7576253 : Blo 996598 7576253 := bstep (se 3 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 7576253 = 2841095) B2841095
theorem B2530025 : Blo 996598 2530025 := bstep (se 2 (by rfl) ⟨948759, by rfl⟩ : syracuseStep 2530025 = 1897519) B1897519
theorem B1121215 : Blo 996598 1121215 := bstep (se 1 (by rfl) ⟨840911, by rfl⟩ : syracuseStep 1121215 = 1681823) B1681823
theorem B13671929 : Blo 996598 13671929 := bstep (se 2 (by rfl) ⟨5126973, by rfl⟩ : syracuseStep 13671929 = 10253947) B10253947
theorem B2531321 : Blo 996598 2531321 := bstep (se 2 (by rfl) ⟨949245, by rfl⟩ : syracuseStep 2531321 = 1898491) B1898491
theorem B4792391 : Blo 996598 4792391 := bstep (se 1 (by rfl) ⟨3594293, by rfl⟩ : syracuseStep 4792391 = 7188587) B7188587
theorem B15999599 : Blo 996598 15999599 := bstep (se 1 (by rfl) ⟨11999699, by rfl⟩ : syracuseStep 15999599 = 23999399) B23999399
theorem B46703233 : Blo 996598 46703233 := bstep (se 2 (by rfl) ⟨17513712, by rfl⟩ : syracuseStep 46703233 = 35027425) B35027425
theorem B21897877 : Blo 996598 21897877 := bstep (se 6 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 21897877 = 1026463) B1026463
theorem B2401289 : Blo 996598 2401289 := bstep (se 2 (by rfl) ⟨900483, by rfl⟩ : syracuseStep 2401289 = 1800967) B1800967
theorem B1124671 : Blo 996598 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B8530667 : Blo 996598 8530667 := bstep (se 1 (by rfl) ⟨6398000, by rfl⟩ : syracuseStep 8530667 = 12796001) B12796001
theorem B2599705 : Blo 996598 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B16166395 : Blo 996598 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B1683065 : Blo 996598 1683065 := bstep (se 2 (by rfl) ⟨631149, by rfl⟩ : syracuseStep 1683065 = 1262299) B1262299
theorem B5681279 : Blo 996598 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B1683679 : Blo 996598 1683679 := bstep (se 1 (by rfl) ⟨1262759, by rfl⟩ : syracuseStep 1683679 = 2525519) B2525519
theorem B1684199 : Blo 996598 1684199 := bstep (se 1 (by rfl) ⟨1263149, by rfl⟩ : syracuseStep 1684199 = 2526299) B2526299
theorem B996655 : Blo 996598 996655 := bstep (se 1 (by rfl) ⟨747491, by rfl⟩ : syracuseStep 996655 = 1494983) B1494983
theorem B996711 : Blo 996598 996711 := bstep (se 1 (by rfl) ⟨747533, by rfl⟩ : syracuseStep 996711 = 1495067) B1495067
theorem B996895 : Blo 996598 996895 := bstep (se 1 (by rfl) ⟨747671, by rfl⟩ : syracuseStep 996895 = 1495343) B1495343
theorem B996967 : Blo 996598 996967 := bstep (se 1 (by rfl) ⟨747725, by rfl⟩ : syracuseStep 996967 = 1495451) B1495451
theorem B996991 : Blo 996598 996991 := bstep (se 1 (by rfl) ⟨747743, by rfl⟩ : syracuseStep 996991 = 1495487) B1495487
theorem B997055 : Blo 996598 997055 := bstep (se 1 (by rfl) ⟨747791, by rfl⟩ : syracuseStep 997055 = 1495583) B1495583
theorem B997247 : Blo 996598 997247 := bstep (se 1 (by rfl) ⟨747935, by rfl⟩ : syracuseStep 997247 = 1495871) B1495871
theorem B997343 : Blo 996598 997343 := bstep (se 1 (by rfl) ⟨748007, by rfl⟩ : syracuseStep 997343 = 1496015) B1496015
theorem B997403 : Blo 996598 997403 := bstep (se 1 (by rfl) ⟨748052, by rfl⟩ : syracuseStep 997403 = 1496105) B1496105
theorem B997423 : Blo 996598 997423 := bstep (se 1 (by rfl) ⟨748067, by rfl⟩ : syracuseStep 997423 = 1496135) B1496135
theorem B997543 : Blo 996598 997543 := bstep (se 1 (by rfl) ⟨748157, by rfl⟩ : syracuseStep 997543 = 1496315) B1496315
theorem B997583 : Blo 996598 997583 := bstep (se 1 (by rfl) ⟨748187, by rfl⟩ : syracuseStep 997583 = 1496375) B1496375
theorem B997787 : Blo 996598 997787 := bstep (se 1 (by rfl) ⟨748340, by rfl⟩ : syracuseStep 997787 = 1496681) B1496681
theorem B998143 : Blo 996598 998143 := bstep (se 1 (by rfl) ⟨748607, by rfl⟩ : syracuseStep 998143 = 1497215) B1497215
theorem B998207 : Blo 996598 998207 := bstep (se 1 (by rfl) ⟨748655, by rfl⟩ : syracuseStep 998207 = 1497311) B1497311
theorem B7682887 : Blo 996598 7682887 := bstep (se 1 (by rfl) ⟨5762165, by rfl⟩ : syracuseStep 7682887 = 11524331) B11524331
theorem B998247 : Blo 996598 998247 := bstep (se 1 (by rfl) ⟨748685, by rfl⟩ : syracuseStep 998247 = 1497371) B1497371
theorem B998463 : Blo 996598 998463 := bstep (se 1 (by rfl) ⟨748847, by rfl⟩ : syracuseStep 998463 = 1497695) B1497695
theorem B998527 : Blo 996598 998527 := bstep (se 1 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 998527 = 1497791) B1497791
theorem B998555 : Blo 996598 998555 := bstep (se 1 (by rfl) ⟨748916, by rfl⟩ : syracuseStep 998555 = 1497833) B1497833
theorem B2243753 : Blo 996598 2243753 := bstep (se 2 (by rfl) ⟨841407, by rfl⟩ : syracuseStep 2243753 = 1682815) B1682815
theorem B998639 : Blo 996598 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B9125135 : Blo 996598 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B998683 : Blo 996598 998683 := bstep (se 1 (by rfl) ⟨749012, by rfl⟩ : syracuseStep 998683 = 1498025) B1498025
theorem B5913967 : Blo 996598 5913967 := bstep (se 1 (by rfl) ⟨4435475, by rfl⟩ : syracuseStep 5913967 = 8870951) B8870951
theorem B998783 : Blo 996598 998783 := bstep (se 1 (by rfl) ⟨749087, by rfl⟩ : syracuseStep 998783 = 1498175) B1498175
theorem B998811 : Blo 996598 998811 := bstep (se 1 (by rfl) ⟨749108, by rfl⟩ : syracuseStep 998811 = 1498217) B1498217
theorem B27344303 : Blo 996598 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B998895 : Blo 996598 998895 := bstep (se 1 (by rfl) ⟨749171, by rfl⟩ : syracuseStep 998895 = 1498343) B1498343
theorem B5684903 : Blo 996598 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B8535725 : Blo 996598 8535725 := bstep (se 3 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 8535725 = 3200897) B3200897
theorem B1687223 : Blo 996598 1687223 := bstep (se 1 (by rfl) ⟨1265417, by rfl⟩ : syracuseStep 1687223 = 2530835) B2530835
theorem B999231 : Blo 996598 999231 := bstep (se 1 (by rfl) ⟨749423, by rfl⟩ : syracuseStep 999231 = 1498847) B1498847
theorem B999451 : Blo 996598 999451 := bstep (se 1 (by rfl) ⟨749588, by rfl⟩ : syracuseStep 999451 = 1499177) B1499177
theorem B999471 : Blo 996598 999471 := bstep (se 1 (by rfl) ⟨749603, by rfl⟩ : syracuseStep 999471 = 1499207) B1499207
theorem B999495 : Blo 996598 999495 := bstep (se 1 (by rfl) ⟨749621, by rfl⟩ : syracuseStep 999495 = 1499243) B1499243
theorem B1687655 : Blo 996598 1687655 := bstep (se 1 (by rfl) ⟨1265741, by rfl⟩ : syracuseStep 1687655 = 2531483) B2531483
theorem B999551 : Blo 996598 999551 := bstep (se 1 (by rfl) ⟨749663, by rfl⟩ : syracuseStep 999551 = 1499327) B1499327
theorem B999675 : Blo 996598 999675 := bstep (se 1 (by rfl) ⟨749756, by rfl⟩ : syracuseStep 999675 = 1499513) B1499513
theorem B999871 : Blo 996598 999871 := bstep (se 1 (by rfl) ⟨749903, by rfl⟩ : syracuseStep 999871 = 1499807) B1499807
theorem B1000095 : Blo 996598 1000095 := bstep (se 1 (by rfl) ⟨750071, by rfl⟩ : syracuseStep 1000095 = 1500143) B1500143
theorem B1000167 : Blo 996598 1000167 := bstep (se 1 (by rfl) ⟨750125, by rfl⟩ : syracuseStep 1000167 = 1500251) B1500251
theorem B1000175 : Blo 996598 1000175 := bstep (se 1 (by rfl) ⟨750131, by rfl⟩ : syracuseStep 1000175 = 1500263) B1500263
theorem B1000263 : Blo 996598 1000263 := bstep (se 1 (by rfl) ⟨750197, by rfl⟩ : syracuseStep 1000263 = 1500395) B1500395
theorem B1000351 : Blo 996598 1000351 := bstep (se 1 (by rfl) ⟨750263, by rfl⟩ : syracuseStep 1000351 = 1500527) B1500527
theorem B1000431 : Blo 996598 1000431 := bstep (se 1 (by rfl) ⟨750323, by rfl⟩ : syracuseStep 1000431 = 1500647) B1500647
theorem B1000519 : Blo 996598 1000519 := bstep (se 1 (by rfl) ⟨750389, by rfl⟩ : syracuseStep 1000519 = 1500779) B1500779
theorem B1000551 : Blo 996598 1000551 := bstep (se 1 (by rfl) ⟨750413, by rfl⟩ : syracuseStep 1000551 = 1500827) B1500827
theorem B3786047 : Blo 996598 3786047 := bstep (se 1 (by rfl) ⟨2839535, by rfl⟩ : syracuseStep 3786047 = 5679071) B5679071
theorem B3786365 : Blo 996598 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B1263595 : Blo 996598 1263595 := bstep (se 1 (by rfl) ⟨947696, by rfl⟩ : syracuseStep 1263595 = 1895393) B1895393
theorem B6834871 : Blo 996598 6834871 := bstep (se 1 (by rfl) ⟨5126153, by rfl⟩ : syracuseStep 6834871 = 10252307) B10252307
theorem B2249063 : Blo 996598 2249063 := bstep (se 1 (by rfl) ⟨1686797, by rfl⟩ : syracuseStep 2249063 = 3373595) B3373595
theorem B1495679 : Blo 996598 1495679 := bstep (se 1 (by rfl) ⟨1121759, by rfl⟩ : syracuseStep 1495679 = 2243519) B2243519
theorem B276976259 : Blo 996598 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B5395247 : Blo 996598 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B2249639 : Blo 996598 2249639 := bstep (se 1 (by rfl) ⟨1687229, by rfl⟩ : syracuseStep 2249639 = 3374459) B3374459
theorem B3789767 : Blo 996598 3789767 := bstep (se 1 (by rfl) ⟨2842325, by rfl⟩ : syracuseStep 3789767 = 5684651) B5684651
theorem B997872605 : Blo 996598 997872605 := bstep (se 3 (by rfl) ⟨187101113, by rfl⟩ : syracuseStep 997872605 = 374202227) B374202227
theorem B1496111 : Blo 996598 1496111 := bstep (se 1 (by rfl) ⟨1122083, by rfl⟩ : syracuseStep 1496111 = 2244167) B2244167
theorem B1496231 : Blo 996598 1496231 := bstep (se 1 (by rfl) ⟨1122173, by rfl⟩ : syracuseStep 1496231 = 2244347) B2244347
theorem B13685939 : Blo 996598 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B1496399 : Blo 996598 1496399 := bstep (se 1 (by rfl) ⟨1122299, by rfl⟩ : syracuseStep 1496399 = 2244599) B2244599
theorem B5690735 : Blo 996598 5690735 := bstep (se 1 (by rfl) ⟨4268051, by rfl⟩ : syracuseStep 5690735 = 8536103) B8536103
theorem B1922555 : Blo 996598 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1496639 : Blo 996598 1496639 := bstep (se 1 (by rfl) ⟨1122479, by rfl⟩ : syracuseStep 1496639 = 2244959) B2244959
theorem B4052663 : Blo 996598 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B4872059 : Blo 996598 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B7591805 : Blo 996598 7591805 := bstep (se 3 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 7591805 = 2846927) B2846927
theorem B1496999 : Blo 996598 1496999 := bstep (se 1 (by rfl) ⟨1122749, by rfl⟩ : syracuseStep 1496999 = 2245499) B2245499
theorem B2250719 : Blo 996598 2250719 := bstep (se 1 (by rfl) ⟨1688039, by rfl⟩ : syracuseStep 2250719 = 3376079) B3376079
theorem B1497083 : Blo 996598 1497083 := bstep (se 1 (by rfl) ⟨1122812, by rfl⟩ : syracuseStep 1497083 = 2245625) B2245625
theorem B1497119 : Blo 996598 1497119 := bstep (se 1 (by rfl) ⟨1122839, by rfl⟩ : syracuseStep 1497119 = 2245679) B2245679
theorem B1497143 : Blo 996598 1497143 := bstep (se 1 (by rfl) ⟨1122857, by rfl⟩ : syracuseStep 1497143 = 2245715) B2245715
theorem B7198793 : Blo 996598 7198793 := bstep (se 2 (by rfl) ⟨2699547, by rfl⟩ : syracuseStep 7198793 = 5399095) B5399095
theorem B3790921 : Blo 996598 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B1497209 : Blo 996598 1497209 := bstep (se 2 (by rfl) ⟨561453, by rfl⟩ : syracuseStep 1497209 = 1122907) B1122907
theorem B1497263 : Blo 996598 1497263 := bstep (se 1 (by rfl) ⟨1122947, by rfl⟩ : syracuseStep 1497263 = 2245895) B2245895
theorem B5691667 : Blo 996598 5691667 := bstep (se 1 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 5691667 = 8537501) B8537501
theorem B1497551 : Blo 996598 1497551 := bstep (se 1 (by rfl) ⟨1123163, by rfl⟩ : syracuseStep 1497551 = 2246327) B2246327
theorem B23091713 : Blo 996598 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B1497851 : Blo 996598 1497851 := bstep (se 1 (by rfl) ⟨1123388, by rfl⟩ : syracuseStep 1497851 = 2246777) B2246777
theorem B1497977 : Blo 996598 1497977 := bstep (se 2 (by rfl) ⟨561741, by rfl⟩ : syracuseStep 1497977 = 1123483) B1123483
theorem B1497983 : Blo 996598 1497983 := bstep (se 1 (by rfl) ⟨1123487, by rfl⟩ : syracuseStep 1497983 = 2246975) B2246975
theorem B38460581 : Blo 996598 38460581 := bstep (se 4 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 38460581 = 7211359) B7211359
theorem B58350793 : Blo 996598 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B8543515 : Blo 996598 8543515 := bstep (se 1 (by rfl) ⟨6407636, by rfl⟩ : syracuseStep 8543515 = 12815273) B12815273
theorem B20503945 : Blo 996598 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B1498889 : Blo 996598 1498889 := bstep (se 2 (by rfl) ⟨562083, by rfl⟩ : syracuseStep 1498889 = 1124167) B1124167
theorem B3792851 : Blo 996598 3792851 := bstep (se 1 (by rfl) ⟨2844638, by rfl⟩ : syracuseStep 3792851 = 5689277) B5689277
theorem B5693399 : Blo 996598 5693399 := bstep (se 1 (by rfl) ⟨4270049, by rfl⟩ : syracuseStep 5693399 = 8540099) B8540099
theorem B1892423 : Blo 996598 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B3596915 : Blo 996598 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B2843419 : Blo 996598 2843419 := bstep (se 1 (by rfl) ⟨2132564, by rfl⟩ : syracuseStep 2843419 = 4265129) B4265129
theorem B2024255 : Blo 996598 2024255 := bstep (se 1 (by rfl) ⟨1518191, by rfl⟩ : syracuseStep 2024255 = 3036383) B3036383
theorem B3367763 : Blo 996598 3367763 := bstep (se 1 (by rfl) ⟨2525822, by rfl⟩ : syracuseStep 3367763 = 5051645) B5051645
theorem B3367817 : Blo 996598 3367817 := bstep (se 2 (by rfl) ⟨1262931, by rfl⟩ : syracuseStep 3367817 = 2525863) B2525863
theorem B57631823 : Blo 996598 57631823 := bstep (se 1 (by rfl) ⟨43223867, by rfl⟩ : syracuseStep 57631823 = 86447735) B86447735
theorem B1500287 : Blo 996598 1500287 := bstep (se 1 (by rfl) ⟨1125215, by rfl⟩ : syracuseStep 1500287 = 2250431) B2250431
theorem B1500425 : Blo 996598 1500425 := bstep (se 2 (by rfl) ⟨562659, by rfl⟩ : syracuseStep 1500425 = 1125319) B1125319
theorem B3204947 : Blo 996598 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B3794809 : Blo 996598 3794809 := bstep (se 2 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 3794809 = 2846107) B2846107
theorem B1796051 : Blo 996598 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B8219045 : Blo 996598 8219045 := bstep (se 4 (by rfl) ⟨770535, by rfl⟩ : syracuseStep 8219045 = 1541071) B1541071
theorem B13691591 : Blo 996598 13691591 := bstep (se 1 (by rfl) ⟨10268693, by rfl⟩ : syracuseStep 13691591 = 20537387) B20537387
theorem B10251319 : Blo 996598 10251319 := bstep (se 1 (by rfl) ⟨7688489, by rfl⟩ : syracuseStep 10251319 = 15376979) B15376979
theorem B3370679 : Blo 996598 3370679 := bstep (se 1 (by rfl) ⟨2528009, by rfl⟩ : syracuseStep 3370679 = 5056019) B5056019
theorem B2846495 : Blo 996598 2846495 := bstep (se 1 (by rfl) ⟨2134871, by rfl⟩ : syracuseStep 2846495 = 4269743) B4269743
theorem B5697499 : Blo 996598 5697499 := bstep (se 1 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 5697499 = 8546249) B8546249
theorem B2846951 : Blo 996598 2846951 := bstep (se 1 (by rfl) ⟨2135213, by rfl⟩ : syracuseStep 2846951 = 4270427) B4270427
theorem B5698025 : Blo 996598 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B1897337 : Blo 996598 1897337 := bstep (se 2 (by rfl) ⟨711501, by rfl⟩ : syracuseStep 1897337 = 1423003) B1423003
theorem B17265581 : Blo 996598 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B3373271 : Blo 996598 3373271 := bstep (se 1 (by rfl) ⟨2529953, by rfl⟩ : syracuseStep 3373271 = 5059907) B5059907
theorem B3374729 : Blo 996598 3374729 := bstep (se 2 (by rfl) ⟨1265523, by rfl⟩ : syracuseStep 3374729 = 2531047) B2531047
theorem B5046461 : Blo 996598 5046461 := bstep (se 3 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 5046461 = 1892423) B1892423
theorem B5046623 : Blo 996598 5046623 := bstep (se 1 (by rfl) ⟨3784967, by rfl⟩ : syracuseStep 5046623 = 7569935) B7569935
theorem B29197169 : Blo 996598 29197169 := bstep (se 2 (by rfl) ⟨10948938, by rfl⟩ : syracuseStep 29197169 = 21897877) B21897877
theorem B2524031 : Blo 996598 2524031 := bstep (se 1 (by rfl) ⟨1893023, by rfl⟩ : syracuseStep 2524031 = 3786047) B3786047
theorem B2524243 : Blo 996598 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B19203227 : Blo 996598 19203227 := bstep (se 1 (by rfl) ⟨14402420, by rfl⟩ : syracuseStep 19203227 = 28804841) B28804841
theorem B4261679 : Blo 996598 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B9767051 : Blo 996598 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B1706447 : Blo 996598 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B184650839 : Blo 996598 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B109186217 : Blo 996598 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B2526511 : Blo 996598 2526511 := bstep (se 1 (by rfl) ⟨1894883, by rfl⟩ : syracuseStep 2526511 = 3789767) B3789767
theorem B9113161 : Blo 996598 9113161 := bstep (se 2 (by rfl) ⟨3417435, by rfl⟩ : syracuseStep 9113161 = 6834871) B6834871
theorem B3248039 : Blo 996598 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B13668425 : Blo 996598 13668425 := bstep (se 2 (by rfl) ⟨5125659, by rfl⟩ : syracuseStep 13668425 = 10251319) B10251319
theorem B5050511 : Blo 996598 5050511 := bstep (se 1 (by rfl) ⟨3787883, by rfl⟩ : syracuseStep 5050511 = 7575767) B7575767
theorem B5050835 : Blo 996598 5050835 := bstep (se 1 (by rfl) ⟨3788126, by rfl⟩ : syracuseStep 5050835 = 7576253) B7576253
theorem B9114619 : Blo 996598 9114619 := bstep (se 1 (by rfl) ⟨6835964, by rfl⟩ : syracuseStep 9114619 = 13671929) B13671929
theorem B4789469 : Blo 996598 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B2528567 : Blo 996598 2528567 := bstep (se 1 (by rfl) ⟨1896425, by rfl⟩ : syracuseStep 2528567 = 3792851) B3792851
theorem B2397943 : Blo 996598 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B1349503 : Blo 996598 1349503 := bstep (se 1 (by rfl) ⟨1012127, by rfl⟩ : syracuseStep 1349503 = 2024255) B2024255
theorem B2136631 : Blo 996598 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B5479363 : Blo 996598 5479363 := bstep (se 1 (by rfl) ⟨4109522, by rfl⟩ : syracuseStep 5479363 = 8219045) B8219045
theorem B109354373 : Blo 996598 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B1122043 : Blo 996598 1122043 := bstep (se 1 (by rfl) ⟨841532, by rfl⟩ : syracuseStep 1122043 = 1683065) B1683065
theorem B5054561 : Blo 996598 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B1122799 : Blo 996598 1122799 := bstep (se 1 (by rfl) ⟨842099, by rfl⟩ : syracuseStep 1122799 = 1684199) B1684199
theorem B11510387 : Blo 996598 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B77801057 : Blo 996598 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B18229535 : Blo 996598 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B1124815 : Blo 996598 1124815 := bstep (se 1 (by rfl) ⟨843611, by rfl⟩ : syracuseStep 1124815 = 1687223) B1687223
theorem B1125103 : Blo 996598 1125103 := bstep (se 1 (by rfl) ⟨843827, by rfl⟩ : syracuseStep 1125103 = 1687655) B1687655
theorem B46181171 : Blo 996598 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B1682599 : Blo 996598 1682599 := bstep (se 1 (by rfl) ⟨1261949, by rfl⟩ : syracuseStep 1682599 = 2523899) B2523899
theorem B1683551 : Blo 996598 1683551 := bstep (se 1 (by rfl) ⟨1262663, by rfl⟩ : syracuseStep 1683551 = 2525327) B2525327
theorem B5059745 : Blo 996598 5059745 := bstep (se 2 (by rfl) ⟨1897404, by rfl⟩ : syracuseStep 5059745 = 3794809) B3794809
theorem B1684793 : Blo 996598 1684793 := bstep (se 2 (by rfl) ⟨631797, by rfl⟩ : syracuseStep 1684793 = 1263595) B1263595
theorem B1684847 : Blo 996598 1684847 := bstep (se 1 (by rfl) ⟨1263635, by rfl⟩ : syracuseStep 1684847 = 2527271) B2527271
theorem B10139053 : Blo 996598 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B4044455 : Blo 996598 4044455 := bstep (se 1 (by rfl) ⟨3033341, by rfl⟩ : syracuseStep 4044455 = 6066683) B6066683
theorem B997119 : Blo 996598 997119 := bstep (se 1 (by rfl) ⟨747839, by rfl⟩ : syracuseStep 997119 = 1495679) B1495679
theorem B1685407 : Blo 996598 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B1423327 : Blo 996598 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B249083909 : Blo 996598 249083909 := bstep (se 4 (by rfl) ⟨23351616, by rfl⟩ : syracuseStep 249083909 = 46703233) B46703233
theorem B997407 : Blo 996598 997407 := bstep (se 1 (by rfl) ⟨748055, by rfl⟩ : syracuseStep 997407 = 1496111) B1496111
theorem B997487 : Blo 996598 997487 := bstep (se 1 (by rfl) ⟨748115, by rfl⟩ : syracuseStep 997487 = 1496231) B1496231
theorem B9123959 : Blo 996598 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B997599 : Blo 996598 997599 := bstep (se 1 (by rfl) ⟨748199, by rfl⟩ : syracuseStep 997599 = 1496399) B1496399
theorem B997759 : Blo 996598 997759 := bstep (se 1 (by rfl) ⟨748319, by rfl⟩ : syracuseStep 997759 = 1496639) B1496639
theorem B2701775 : Blo 996598 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B3193415 : Blo 996598 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B5061203 : Blo 996598 5061203 := bstep (se 1 (by rfl) ⟨3795902, by rfl⟩ : syracuseStep 5061203 = 7591805) B7591805
theorem B997999 : Blo 996598 997999 := bstep (se 1 (by rfl) ⟨748499, by rfl⟩ : syracuseStep 997999 = 1496999) B1496999
theorem B5126813 : Blo 996598 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B998055 : Blo 996598 998055 := bstep (se 1 (by rfl) ⟨748541, by rfl⟩ : syracuseStep 998055 = 1497083) B1497083
theorem B998079 : Blo 996598 998079 := bstep (se 1 (by rfl) ⟨748559, by rfl⟩ : syracuseStep 998079 = 1497119) B1497119
theorem B998095 : Blo 996598 998095 := bstep (se 1 (by rfl) ⟨748571, by rfl⟩ : syracuseStep 998095 = 1497143) B1497143
theorem B4799195 : Blo 996598 4799195 := bstep (se 1 (by rfl) ⟨3599396, by rfl⟩ : syracuseStep 4799195 = 7198793) B7198793
theorem B998139 : Blo 996598 998139 := bstep (se 1 (by rfl) ⟨748604, by rfl⟩ : syracuseStep 998139 = 1497209) B1497209
theorem B998175 : Blo 996598 998175 := bstep (se 1 (by rfl) ⟨748631, by rfl⟩ : syracuseStep 998175 = 1497263) B1497263
theorem B998367 : Blo 996598 998367 := bstep (se 1 (by rfl) ⟨748775, by rfl⟩ : syracuseStep 998367 = 1497551) B1497551
theorem B1686683 : Blo 996598 1686683 := bstep (se 1 (by rfl) ⟨1265012, by rfl⟩ : syracuseStep 1686683 = 2530025) B2530025
theorem B998567 : Blo 996598 998567 := bstep (se 1 (by rfl) ⟨748925, by rfl⟩ : syracuseStep 998567 = 1497851) B1497851
theorem B998651 : Blo 996598 998651 := bstep (se 1 (by rfl) ⟨748988, by rfl⟩ : syracuseStep 998651 = 1497977) B1497977
theorem B998655 : Blo 996598 998655 := bstep (se 1 (by rfl) ⟨748991, by rfl⟩ : syracuseStep 998655 = 1497983) B1497983
theorem B25640387 : Blo 996598 25640387 := bstep (se 1 (by rfl) ⟨19230290, by rfl⟩ : syracuseStep 25640387 = 38460581) B38460581
theorem B999259 : Blo 996598 999259 := bstep (se 1 (by rfl) ⟨749444, by rfl⟩ : syracuseStep 999259 = 1498889) B1498889
theorem B1687547 : Blo 996598 1687547 := bstep (se 1 (by rfl) ⟨1265660, by rfl⟩ : syracuseStep 1687547 = 2531321) B2531321
theorem B3194927 : Blo 996598 3194927 := bstep (se 1 (by rfl) ⟨2396195, by rfl⟩ : syracuseStep 3194927 = 4792391) B4792391
theorem B2244905 : Blo 996598 2244905 := bstep (se 2 (by rfl) ⟨841839, by rfl⟩ : syracuseStep 2244905 = 1683679) B1683679
theorem B10666399 : Blo 996598 10666399 := bstep (se 1 (by rfl) ⟨7999799, by rfl⟩ : syracuseStep 10666399 = 15999599) B15999599
theorem B2245175 : Blo 996598 2245175 := bstep (se 1 (by rfl) ⟨1683881, by rfl⟩ : syracuseStep 2245175 = 3367763) B3367763
theorem B2245211 : Blo 996598 2245211 := bstep (se 1 (by rfl) ⟨1683908, by rfl⟩ : syracuseStep 2245211 = 3367817) B3367817
theorem B38421215 : Blo 996598 38421215 := bstep (se 1 (by rfl) ⟨28815911, by rfl⟩ : syracuseStep 38421215 = 57631823) B57631823
theorem B1000191 : Blo 996598 1000191 := bstep (se 1 (by rfl) ⟨750143, by rfl⟩ : syracuseStep 1000191 = 1500287) B1500287
theorem B1000283 : Blo 996598 1000283 := bstep (se 1 (by rfl) ⟨750212, by rfl⟩ : syracuseStep 1000283 = 1500425) B1500425
theorem B9127727 : Blo 996598 9127727 := bstep (se 1 (by rfl) ⟨6845795, by rfl⟩ : syracuseStep 9127727 = 13691591) B13691591
theorem B5687111 : Blo 996598 5687111 := bstep (se 1 (by rfl) ⟨4265333, by rfl⟩ : syracuseStep 5687111 = 8530667) B8530667
theorem B5687293 : Blo 996598 5687293 := bstep (se 3 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 5687293 = 2132735) B2132735
theorem B2247119 : Blo 996598 2247119 := bstep (se 1 (by rfl) ⟨1685339, by rfl⟩ : syracuseStep 2247119 = 3370679) B3370679
theorem B3787519 : Blo 996598 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B7588889 : Blo 996598 7588889 := bstep (se 2 (by rfl) ⟨2845833, by rfl⟩ : syracuseStep 7588889 = 5691667) B5691667
theorem B5688569 : Blo 996598 5688569 := bstep (se 2 (by rfl) ⟨2133213, by rfl⟩ : syracuseStep 5688569 = 4266427) B4266427
theorem B1264891 : Blo 996598 1264891 := bstep (se 1 (by rfl) ⟨948668, by rfl⟩ : syracuseStep 1264891 = 1897337) B1897337
theorem B10243849 : Blo 996598 10243849 := bstep (se 2 (by rfl) ⟨3841443, by rfl⟩ : syracuseStep 10243849 = 7682887) B7682887
theorem B1494953 : Blo 996598 1494953 := bstep (se 2 (by rfl) ⟨560607, by rfl⟩ : syracuseStep 1494953 = 1121215) B1121215
theorem B2248847 : Blo 996598 2248847 := bstep (se 1 (by rfl) ⟨1686635, by rfl⟩ : syracuseStep 2248847 = 3373271) B3373271
theorem B11391353 : Blo 996598 11391353 := bstep (se 2 (by rfl) ⟨4271757, by rfl⟩ : syracuseStep 11391353 = 8543515) B8543515
theorem B7885289 : Blo 996598 7885289 := bstep (se 2 (by rfl) ⟨2956983, by rfl⟩ : syracuseStep 7885289 = 5913967) B5913967
theorem B1495835 : Blo 996598 1495835 := bstep (se 1 (by rfl) ⟨1121876, by rfl⟩ : syracuseStep 1495835 = 2243753) B2243753
theorem B6083423 : Blo 996598 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B2249819 : Blo 996598 2249819 := bstep (se 1 (by rfl) ⟨1687364, by rfl⟩ : syracuseStep 2249819 = 3374729) B3374729
theorem B3789935 : Blo 996598 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B5690483 : Blo 996598 5690483 := bstep (se 1 (by rfl) ⟨4267862, by rfl⟩ : syracuseStep 5690483 = 8535725) B8535725
theorem B2840447 : Blo 996598 2840447 := bstep (se 1 (by rfl) ⟨2130335, by rfl⟩ : syracuseStep 2840447 = 4260671) B4260671
theorem B1202047 : Blo 996598 1202047 := bstep (se 1 (by rfl) ⟨901535, by rfl⟩ : syracuseStep 1202047 = 1803071) B1803071
theorem B3791225 : Blo 996598 3791225 := bstep (se 2 (by rfl) ⟨1421709, by rfl⟩ : syracuseStep 3791225 = 2843419) B2843419
theorem B43179581 : Blo 996598 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B4546655 : Blo 996598 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B1499375 : Blo 996598 1499375 := bstep (se 1 (by rfl) ⟨1124531, by rfl⟩ : syracuseStep 1499375 = 2249063) B2249063
theorem B1499561 : Blo 996598 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B3596831 : Blo 996598 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B1499759 : Blo 996598 1499759 := bstep (se 1 (by rfl) ⟨1124819, by rfl⟩ : syracuseStep 1499759 = 2249639) B2249639
theorem B665248403 : Blo 996598 665248403 := bstep (se 1 (by rfl) ⟨498936302, by rfl⟩ : syracuseStep 665248403 = 997872605) B997872605
theorem B1139519 : Blo 996598 1139519 := bstep (se 1 (by rfl) ⟨854639, by rfl⟩ : syracuseStep 1139519 = 1709279) B1709279
theorem B3793823 : Blo 996598 3793823 := bstep (se 1 (by rfl) ⟨2845367, by rfl⟩ : syracuseStep 3793823 = 5690735) B5690735
theorem B3466273 : Blo 996598 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B8545499 : Blo 996598 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B1500479 : Blo 996598 1500479 := bstep (se 1 (by rfl) ⟨1125359, by rfl⟩ : syracuseStep 1500479 = 2250719) B2250719
theorem B15394475 : Blo 996598 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B21555193 : Blo 996598 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B7596665 : Blo 996598 7596665 := bstep (se 2 (by rfl) ⟨2848749, by rfl⟩ : syracuseStep 7596665 = 5697499) B5697499
theorem B3795599 : Blo 996598 3795599 := bstep (se 1 (by rfl) ⟨2846699, by rfl⟩ : syracuseStep 3795599 = 5693399) B5693399
theorem B1600859 : Blo 996598 1600859 := bstep (se 1 (by rfl) ⟨1200644, by rfl⟩ : syracuseStep 1600859 = 2401289) B2401289
theorem B1897663 : Blo 996598 1897663 := bstep (se 1 (by rfl) ⟨1423247, by rfl⟩ : syracuseStep 1897663 = 2846495) B2846495
theorem B1897967 : Blo 996598 1897967 := bstep (se 1 (by rfl) ⟨1423475, by rfl⟩ : syracuseStep 1897967 = 2846951) B2846951
theorem B3798683 : Blo 996598 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B2129951 : Blo 996598 2129951 := bstep (se 1 (by rfl) ⟨1597463, by rfl⟩ : syracuseStep 2129951 = 3194927) B3194927
theorem B14221865 : Blo 996598 14221865 := bstep (se 2 (by rfl) ⟨5333199, by rfl⟩ : syracuseStep 14221865 = 10666399) B10666399
theorem B19464779 : Blo 996598 19464779 := bstep (se 1 (by rfl) ⟨14598584, by rfl⟩ : syracuseStep 19464779 = 29197169) B29197169
theorem B4621697 : Blo 996598 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B28740257 : Blo 996598 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B9112283 : Blo 996598 9112283 := bstep (se 1 (by rfl) ⟨6834212, by rfl⟩ : syracuseStep 9112283 = 13668425) B13668425
theorem B2526623 : Blo 996598 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B5050025 : Blo 996598 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B2527483 : Blo 996598 2527483 := bstep (se 1 (by rfl) ⟨1895612, by rfl⟩ : syracuseStep 2527483 = 3791225) B3791225
theorem B2397887 : Blo 996598 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B7673591 : Blo 996598 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B2529215 : Blo 996598 2529215 := bstep (se 1 (by rfl) ⟨1896911, by rfl⟩ : syracuseStep 2529215 = 3793823) B3793823
theorem B10262983 : Blo 996598 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B2530217 : Blo 996598 2530217 := bstep (se 2 (by rfl) ⟨948831, by rfl⟩ : syracuseStep 2530217 = 1897663) B1897663
theorem B2530399 : Blo 996598 2530399 := bstep (se 1 (by rfl) ⟨1897799, by rfl⟩ : syracuseStep 2530399 = 3795599) B3795599
theorem B1122367 : Blo 996598 1122367 := bstep (se 1 (by rfl) ⟨841775, by rfl⟩ : syracuseStep 1122367 = 1683551) B1683551
theorem B1123195 : Blo 996598 1123195 := bstep (se 1 (by rfl) ⟨842396, by rfl⟩ : syracuseStep 1123195 = 1684793) B1684793
theorem B1123231 : Blo 996598 1123231 := bstep (se 1 (by rfl) ⟨842423, by rfl⟩ : syracuseStep 1123231 = 1684847) B1684847
theorem B2532455 : Blo 996598 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B2696303 : Blo 996598 2696303 := bstep (se 1 (by rfl) ⟨2022227, by rfl⟩ : syracuseStep 2696303 = 4044455) B4044455
theorem B12789029 : Blo 996598 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B3417875 : Blo 996598 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B1124455 : Blo 996598 1124455 := bstep (se 1 (by rfl) ⟨843341, by rfl⟩ : syracuseStep 1124455 = 1686683) B1686683
theorem B8661437 : Blo 996598 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B1125031 : Blo 996598 1125031 := bstep (se 1 (by rfl) ⟨843773, by rfl⟩ : syracuseStep 1125031 = 1687547) B1687547
theorem B1682687 : Blo 996598 1682687 := bstep (se 1 (by rfl) ⟨1262015, by rfl⟩ : syracuseStep 1682687 = 2524031) B2524031
theorem B5059259 : Blo 996598 5059259 := bstep (se 1 (by rfl) ⟨3794444, by rfl⟩ : syracuseStep 5059259 = 7588889) B7588889
theorem B72790811 : Blo 996598 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B996635 : Blo 996598 996635 := bstep (se 1 (by rfl) ⟨747476, by rfl⟩ : syracuseStep 996635 = 1494953) B1494953
theorem B7583057 : Blo 996598 7583057 := bstep (se 2 (by rfl) ⟨2843646, by rfl⟩ : syracuseStep 7583057 = 5687293) B5687293
theorem B997223 : Blo 996598 997223 := bstep (se 1 (by rfl) ⟨747917, by rfl⟩ : syracuseStep 997223 = 1495835) B1495835
theorem B3192979 : Blo 996598 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B1685711 : Blo 996598 1685711 := bstep (se 1 (by rfl) ⟨1264283, by rfl⟩ : syracuseStep 1685711 = 2528567) B2528567
theorem B2243465 : Blo 996598 2243465 := bstep (se 2 (by rfl) ⟨841299, by rfl⟩ : syracuseStep 2243465 = 1682599) B1682599
theorem B1686521 : Blo 996598 1686521 := bstep (se 2 (by rfl) ⟨632445, by rfl⟩ : syracuseStep 1686521 = 1264891) B1264891
theorem B28786387 : Blo 996598 28786387 := bstep (se 1 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 28786387 = 43179581) B43179581
theorem B3031103 : Blo 996598 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B999583 : Blo 996598 999583 := bstep (se 1 (by rfl) ⟨749687, by rfl⟩ : syracuseStep 999583 = 1499375) B1499375
theorem B999707 : Blo 996598 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B24330557 : Blo 996598 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B999839 : Blo 996598 999839 := bstep (se 1 (by rfl) ⟨749879, by rfl⟩ : syracuseStep 999839 = 1499759) B1499759
theorem B443498935 : Blo 996598 443498935 := bstep (se 1 (by rfl) ⟨332624201, by rfl⟩ : syracuseStep 443498935 = 665248403) B665248403
theorem B1000319 : Blo 996598 1000319 := bstep (se 1 (by rfl) ⟨750239, by rfl⟩ : syracuseStep 1000319 = 1500479) B1500479
theorem B5064443 : Blo 996598 5064443 := bstep (se 1 (by rfl) ⟨3798332, by rfl⟩ : syracuseStep 5064443 = 7596665) B7596665
theorem B30787447 : Blo 996598 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B13518737 : Blo 996598 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B1067239 : Blo 996598 1067239 := bstep (se 1 (by rfl) ⟨800429, by rfl⟩ : syracuseStep 1067239 = 1600859) B1600859
theorem B2247209 : Blo 996598 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B1265311 : Blo 996598 1265311 := bstep (se 1 (by rfl) ⟨948983, by rfl⟩ : syracuseStep 1265311 = 1897967) B1897967
theorem B166055939 : Blo 996598 166055939 := bstep (se 1 (by rfl) ⟨124541954, by rfl⟩ : syracuseStep 166055939 = 249083909) B249083909
theorem B3199463 : Blo 996598 3199463 := bstep (se 1 (by rfl) ⟨2399597, by rfl⟩ : syracuseStep 3199463 = 4799195) B4799195
theorem B7197349 : Blo 996598 7197349 := bstep (se 4 (by rfl) ⟨674751, by rfl⟩ : syracuseStep 7197349 = 1349503) B1349503
theorem B6410917 : Blo 996598 6410917 := bstep (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) B1202047
theorem B17093591 : Blo 996598 17093591 := bstep (se 1 (by rfl) ⟨12820193, by rfl⟩ : syracuseStep 17093591 = 25640387) B25640387
theorem B1496057 : Blo 996598 1496057 := bstep (se 2 (by rfl) ⟨561021, by rfl⟩ : syracuseStep 1496057 = 1122043) B1122043
theorem B3364307 : Blo 996598 3364307 := bstep (se 1 (by rfl) ⟨2523230, by rfl⟩ : syracuseStep 3364307 = 5046461) B5046461
theorem B1496603 : Blo 996598 1496603 := bstep (se 1 (by rfl) ⟨1122452, by rfl⟩ : syracuseStep 1496603 = 2244905) B2244905
theorem B3364415 : Blo 996598 3364415 := bstep (se 1 (by rfl) ⟨2523311, by rfl⟩ : syracuseStep 3364415 = 5046623) B5046623
theorem B1496783 : Blo 996598 1496783 := bstep (se 1 (by rfl) ⟨1122587, by rfl⟩ : syracuseStep 1496783 = 2245175) B2245175
theorem B1496807 : Blo 996598 1496807 := bstep (se 1 (by rfl) ⟨1122605, by rfl⟩ : syracuseStep 1496807 = 2245211) B2245211
theorem B25614143 : Blo 996598 25614143 := bstep (se 1 (by rfl) ⟨19210607, by rfl⟩ : syracuseStep 25614143 = 38421215) B38421215
theorem B1497065 : Blo 996598 1497065 := bstep (se 2 (by rfl) ⟨561399, by rfl⟩ : syracuseStep 1497065 = 1122799) B1122799
theorem B12802151 : Blo 996598 12802151 := bstep (se 1 (by rfl) ⟨9601613, by rfl⟩ : syracuseStep 12802151 = 19203227) B19203227
theorem B2841119 : Blo 996598 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B6085151 : Blo 996598 6085151 := bstep (se 1 (by rfl) ⟨4563863, by rfl⟩ : syracuseStep 6085151 = 9127727) B9127727
theorem B3791407 : Blo 996598 3791407 := bstep (se 1 (by rfl) ⟨2843555, by rfl⟩ : syracuseStep 3791407 = 5687111) B5687111
theorem B21027437 : Blo 996598 21027437 := bstep (se 3 (by rfl) ⟨3942644, by rfl⟩ : syracuseStep 21027437 = 7885289) B7885289
theorem B6511367 : Blo 996598 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B3365657 : Blo 996598 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B1137631 : Blo 996598 1137631 := bstep (se 1 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 1137631 = 1706447) B1706447
theorem B1498079 : Blo 996598 1498079 := bstep (se 1 (by rfl) ⟨1123559, by rfl⟩ : syracuseStep 1498079 = 2247119) B2247119
theorem B123100559 : Blo 996598 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B3792379 : Blo 996598 3792379 := bstep (se 1 (by rfl) ⟨2844284, by rfl⟩ : syracuseStep 3792379 = 5688569) B5688569
theorem B3038717 : Blo 996598 3038717 := bstep (se 3 (by rfl) ⟨569759, by rfl⟩ : syracuseStep 3038717 = 1139519) B1139519
theorem B3367007 : Blo 996598 3367007 := bstep (se 1 (by rfl) ⟨2525255, by rfl⟩ : syracuseStep 3367007 = 5050511) B5050511
theorem B1499231 : Blo 996598 1499231 := bstep (se 1 (by rfl) ⟨1124423, by rfl⟩ : syracuseStep 1499231 = 2248847) B2248847
theorem B7594235 : Blo 996598 7594235 := bstep (se 1 (by rfl) ⟨5695676, by rfl⟩ : syracuseStep 7594235 = 11391353) B11391353
theorem B3367223 : Blo 996598 3367223 := bstep (se 1 (by rfl) ⟨2525417, by rfl⟩ : syracuseStep 3367223 = 5050835) B5050835
theorem B4055615 : Blo 996598 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B1499753 : Blo 996598 1499753 := bstep (se 2 (by rfl) ⟨562407, by rfl⟩ : syracuseStep 1499753 = 1124815) B1124815
theorem B1499879 : Blo 996598 1499879 := bstep (se 1 (by rfl) ⟨1124909, by rfl⟩ : syracuseStep 1499879 = 2249819) B2249819
theorem B3793655 : Blo 996598 3793655 := bstep (se 1 (by rfl) ⟨2845241, by rfl⟩ : syracuseStep 3793655 = 5690483) B5690483
theorem B1500137 : Blo 996598 1500137 := bstep (se 2 (by rfl) ⟨562551, by rfl⟩ : syracuseStep 1500137 = 1125103) B1125103
theorem B1893631 : Blo 996598 1893631 := bstep (se 1 (by rfl) ⟨1420223, by rfl⟩ : syracuseStep 1893631 = 2840447) B2840447
theorem B3368681 : Blo 996598 3368681 := bstep (se 2 (by rfl) ⟨1263255, by rfl⟩ : syracuseStep 3368681 = 2526511) B2526511
theorem B12150881 : Blo 996598 12150881 := bstep (se 2 (by rfl) ⟨4556580, by rfl⟩ : syracuseStep 12150881 = 9113161) B9113161
theorem B72902915 : Blo 996598 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B13658465 : Blo 996598 13658465 := bstep (se 2 (by rfl) ⟨5121924, by rfl⟩ : syracuseStep 13658465 = 10243849) B10243849
theorem B3369707 : Blo 996598 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B5696999 : Blo 996598 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B51867371 : Blo 996598 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B12152825 : Blo 996598 12152825 := bstep (se 2 (by rfl) ⟨4557309, by rfl⟩ : syracuseStep 12152825 = 9114619) B9114619
theorem B12153023 : Blo 996598 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B1897769 : Blo 996598 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B2848841 : Blo 996598 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B3373163 : Blo 996598 3373163 := bstep (se 1 (by rfl) ⟨2529872, by rfl⟩ : syracuseStep 3373163 = 5059745) B5059745
theorem B7305817 : Blo 996598 7305817 := bstep (se 2 (by rfl) ⟨2739681, by rfl⟩ : syracuseStep 7305817 = 5479363) B5479363
theorem B1801183 : Blo 996598 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B2128943 : Blo 996598 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B3374135 : Blo 996598 3374135 := bstep (se 1 (by rfl) ⟨2530601, by rfl⟩ : syracuseStep 3374135 = 5061203) B5061203
theorem B16220371 : Blo 996598 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B12976519 : Blo 996598 12976519 := bstep (se 1 (by rfl) ⟨9732389, by rfl⟩ : syracuseStep 12976519 = 19464779) B19464779
theorem B591331913 : Blo 996598 591331913 := bstep (se 2 (by rfl) ⟨221749467, by rfl⟩ : syracuseStep 591331913 = 443498935) B443498935
theorem B3081131 : Blo 996598 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B3376295 : Blo 996598 3376295 := bstep (se 1 (by rfl) ⟨2532221, by rfl⟩ : syracuseStep 3376295 = 5064443) B5064443
theorem B9012491 : Blo 996598 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B2524841 : Blo 996598 2524841 := bstep (se 2 (by rfl) ⟨946815, by rfl⟩ : syracuseStep 2524841 = 1893631) B1893631
theorem B2132975 : Blo 996598 2132975 := bstep (se 1 (by rfl) ⟨1599731, by rfl⟩ : syracuseStep 2132975 = 3199463) B3199463
theorem B5115727 : Blo 996598 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B17076095 : Blo 996598 17076095 := bstep (se 1 (by rfl) ⟨12807071, by rfl⟩ : syracuseStep 17076095 = 25614143) B25614143
theorem B2529103 : Blo 996598 2529103 := bstep (se 1 (by rfl) ⟨1896827, by rfl⟩ : syracuseStep 2529103 = 3793655) B3793655
theorem B8526019 : Blo 996598 8526019 := bstep (se 1 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 8526019 = 12789029) B12789029
theorem B8100587 : Blo 996598 8100587 := bstep (se 1 (by rfl) ⟨6075440, by rfl⟩ : syracuseStep 8100587 = 12150881) B12150881
theorem B48601943 : Blo 996598 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B5774291 : Blo 996598 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B1121791 : Blo 996598 1121791 := bstep (se 1 (by rfl) ⟨841343, by rfl⟩ : syracuseStep 1121791 = 1682687) B1682687
theorem B34578247 : Blo 996598 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B8101883 : Blo 996598 8101883 := bstep (se 1 (by rfl) ⟨6076412, by rfl⟩ : syracuseStep 8101883 = 12152825) B12152825
theorem B8102015 : Blo 996598 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B5055209 : Blo 996598 5055209 := bstep (se 2 (by rfl) ⟨1895703, by rfl⟩ : syracuseStep 5055209 = 3791407) B3791407
theorem B9741089 : Blo 996598 9741089 := bstep (se 2 (by rfl) ⟨3652908, by rfl⟩ : syracuseStep 9741089 = 7305817) B7305817
theorem B5055371 : Blo 996598 5055371 := bstep (se 1 (by rfl) ⟨3791528, by rfl⟩ : syracuseStep 5055371 = 7583057) B7583057
theorem B1516841 : Blo 996598 1516841 := bstep (se 2 (by rfl) ⟨568815, by rfl⟩ : syracuseStep 1516841 = 1137631) B1137631
theorem B2401577 : Blo 996598 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B8103245 : Blo 996598 8103245 := bstep (se 3 (by rfl) ⟨1519358, by rfl⟩ : syracuseStep 8103245 = 3038717) B3038717
theorem B1123807 : Blo 996598 1123807 := bstep (se 1 (by rfl) ⟨842855, by rfl⟩ : syracuseStep 1123807 = 1685711) B1685711
theorem B5056505 : Blo 996598 5056505 := bstep (se 2 (by rfl) ⟨1896189, by rfl⟩ : syracuseStep 5056505 = 3792379) B3792379
theorem B1124347 : Blo 996598 1124347 := bstep (se 1 (by rfl) ⟨843260, by rfl⟩ : syracuseStep 1124347 = 1686521) B1686521
theorem B1419295 : Blo 996598 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B38381849 : Blo 996598 38381849 := bstep (se 2 (by rfl) ⟨14393193, by rfl⟩ : syracuseStep 38381849 = 28786387) B28786387
theorem B1419967 : Blo 996598 1419967 := bstep (se 1 (by rfl) ⟨1064975, by rfl⟩ : syracuseStep 1419967 = 2129951) B2129951
theorem B37924973 : Blo 996598 37924973 := bstep (se 3 (by rfl) ⟨7110932, by rfl⟩ : syracuseStep 37924973 = 14221865) B14221865
theorem B6074855 : Blo 996598 6074855 := bstep (se 1 (by rfl) ⟨4556141, by rfl⟩ : syracuseStep 6074855 = 9112283) B9112283
theorem B1684415 : Blo 996598 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B110703959 : Blo 996598 110703959 := bstep (se 1 (by rfl) ⟨83027969, by rfl⟩ : syracuseStep 110703959 = 166055939) B166055939
theorem B997371 : Blo 996598 997371 := bstep (se 1 (by rfl) ⟨748028, by rfl⟩ : syracuseStep 997371 = 1496057) B1496057
theorem B5060717 : Blo 996598 5060717 := bstep (se 3 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 5060717 = 1897769) B1897769
theorem B2242871 : Blo 996598 2242871 := bstep (se 1 (by rfl) ⟨1682153, by rfl⟩ : syracuseStep 2242871 = 3364307) B3364307
theorem B997735 : Blo 996598 997735 := bstep (se 1 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 997735 = 1496603) B1496603
theorem B2242943 : Blo 996598 2242943 := bstep (se 1 (by rfl) ⟨1682207, by rfl⟩ : syracuseStep 2242943 = 3364415) B3364415
theorem B997855 : Blo 996598 997855 := bstep (se 1 (by rfl) ⟨748391, by rfl⟩ : syracuseStep 997855 = 1496783) B1496783
theorem B997871 : Blo 996598 997871 := bstep (se 1 (by rfl) ⟨748403, by rfl⟩ : syracuseStep 997871 = 1496807) B1496807
theorem B1686143 : Blo 996598 1686143 := bstep (se 1 (by rfl) ⟨1264607, by rfl⟩ : syracuseStep 1686143 = 2529215) B2529215
theorem B998043 : Blo 996598 998043 := bstep (se 1 (by rfl) ⟨748532, by rfl⟩ : syracuseStep 998043 = 1497065) B1497065
theorem B8534767 : Blo 996598 8534767 := bstep (se 1 (by rfl) ⟨6401075, by rfl⟩ : syracuseStep 8534767 = 12802151) B12802151
theorem B4340911 : Blo 996598 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B2243771 : Blo 996598 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B1686811 : Blo 996598 1686811 := bstep (se 1 (by rfl) ⟨1265108, by rfl⟩ : syracuseStep 1686811 = 2530217) B2530217
theorem B998719 : Blo 996598 998719 := bstep (se 1 (by rfl) ⟨749039, by rfl⟩ : syracuseStep 998719 = 1498079) B1498079
theorem B1687081 : Blo 996598 1687081 := bstep (se 2 (by rfl) ⟨632655, by rfl⟩ : syracuseStep 1687081 = 1265311) B1265311
theorem B82067039 : Blo 996598 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B2244671 : Blo 996598 2244671 := bstep (se 1 (by rfl) ⟨1683503, by rfl⟩ : syracuseStep 2244671 = 3367007) B3367007
theorem B999487 : Blo 996598 999487 := bstep (se 1 (by rfl) ⟨749615, by rfl⟩ : syracuseStep 999487 = 1499231) B1499231
theorem B5062823 : Blo 996598 5062823 := bstep (se 1 (by rfl) ⟨3797117, by rfl⟩ : syracuseStep 5062823 = 7594235) B7594235
theorem B2244815 : Blo 996598 2244815 := bstep (se 1 (by rfl) ⟨1683611, by rfl⟩ : syracuseStep 2244815 = 3367223) B3367223
theorem B2703743 : Blo 996598 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B999835 : Blo 996598 999835 := bstep (se 1 (by rfl) ⟨749876, by rfl⟩ : syracuseStep 999835 = 1499753) B1499753
theorem B999919 : Blo 996598 999919 := bstep (se 1 (by rfl) ⟨749939, by rfl⟩ : syracuseStep 999919 = 1499879) B1499879
theorem B1000091 : Blo 996598 1000091 := bstep (se 1 (by rfl) ⟨750068, by rfl⟩ : syracuseStep 1000091 = 1500137) B1500137
theorem B1688303 : Blo 996598 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B2245787 : Blo 996598 2245787 := bstep (se 1 (by rfl) ⟨1684340, by rfl⟩ : syracuseStep 2245787 = 3368681) B3368681
theorem B2278583 : Blo 996598 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B2246471 : Blo 996598 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B13683977 : Blo 996598 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B2248775 : Blo 996598 2248775 := bstep (se 1 (by rfl) ⟨1686581, by rfl⟩ : syracuseStep 2248775 = 3373163) B3373163
theorem B1495643 : Blo 996598 1495643 := bstep (se 1 (by rfl) ⟨1121732, by rfl⟩ : syracuseStep 1495643 = 2243465) B2243465
theorem B2249423 : Blo 996598 2249423 := bstep (se 1 (by rfl) ⟨1687067, by rfl⟩ : syracuseStep 2249423 = 3374135) B3374135
theorem B2020735 : Blo 996598 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B1496489 : Blo 996598 1496489 := bstep (se 2 (by rfl) ⟨561183, by rfl⟩ : syracuseStep 1496489 = 1122367) B1122367
theorem B1497593 : Blo 996598 1497593 := bstep (se 2 (by rfl) ⟨561597, by rfl⟩ : syracuseStep 1497593 = 1123195) B1123195
theorem B5691941 : Blo 996598 5691941 := bstep (se 4 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 5691941 = 1067239) B1067239
theorem B1497641 : Blo 996598 1497641 := bstep (se 2 (by rfl) ⟨561615, by rfl⟩ : syracuseStep 1497641 = 1123231) B1123231
theorem B1498139 : Blo 996598 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B19160171 : Blo 996598 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B3366683 : Blo 996598 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B41049929 : Blo 996598 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B1499273 : Blo 996598 1499273 := bstep (se 2 (by rfl) ⟨562227, by rfl⟩ : syracuseStep 1499273 = 1124455) B1124455
theorem B11395727 : Blo 996598 11395727 := bstep (se 1 (by rfl) ⟨8546795, by rfl⟩ : syracuseStep 11395727 = 17093591) B17093591
theorem B1500041 : Blo 996598 1500041 := bstep (se 2 (by rfl) ⟨562515, by rfl⟩ : syracuseStep 1500041 = 1125031) B1125031
theorem B1598591 : Blo 996598 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B1894079 : Blo 996598 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B4056767 : Blo 996598 4056767 := bstep (se 1 (by rfl) ⟨3042575, by rfl⟩ : syracuseStep 4056767 = 6085151) B6085151
theorem B14018291 : Blo 996598 14018291 := bstep (se 1 (by rfl) ⟨10513718, by rfl⟩ : syracuseStep 14018291 = 21027437) B21027437
theorem B3369977 : Blo 996598 3369977 := bstep (se 2 (by rfl) ⟨1263741, by rfl⟩ : syracuseStep 3369977 = 2527483) B2527483
theorem B1797535 : Blo 996598 1797535 := bstep (se 1 (by rfl) ⟨1348151, by rfl⟩ : syracuseStep 1797535 = 2696303) B2696303
theorem B9596465 : Blo 996598 9596465 := bstep (se 2 (by rfl) ⟨3598674, by rfl⟩ : syracuseStep 9596465 = 7197349) B7197349
theorem B8547889 : Blo 996598 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B9105643 : Blo 996598 9105643 := bstep (se 1 (by rfl) ⟨6829232, by rfl⟩ : syracuseStep 9105643 = 13658465) B13658465
theorem B3797999 : Blo 996598 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B4257305 : Blo 996598 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B3372839 : Blo 996598 3372839 := bstep (se 1 (by rfl) ⟨2529629, by rfl⟩ : syracuseStep 3372839 = 5059259) B5059259
theorem B48527207 : Blo 996598 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B1899227 : Blo 996598 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B3373865 : Blo 996598 3373865 := bstep (se 2 (by rfl) ⟨1265199, by rfl⟩ : syracuseStep 3373865 = 2530399) B2530399
theorem B3375215 : Blo 996598 3375215 := bstep (se 1 (by rfl) ⟨2531411, by rfl⟩ : syracuseStep 3375215 = 5062823) B5062823
theorem B1802495 : Blo 996598 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B21627161 : Blo 996598 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B17302025 : Blo 996598 17302025 := bstep (se 2 (by rfl) ⟨6488259, by rfl⟩ : syracuseStep 17302025 = 12976519) B12976519
theorem B2396713 : Blo 996598 2396713 := bstep (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) B1797535
theorem B6820969 : Blo 996598 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B27366619 : Blo 996598 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B6494059 : Blo 996598 6494059 := bstep (se 1 (by rfl) ⟨4870544, by rfl⟩ : syracuseStep 6494059 = 9741089) B9741089
theorem B9345527 : Blo 996598 9345527 := bstep (se 1 (by rfl) ⟨7009145, by rfl⟩ : syracuseStep 9345527 = 14018291) B14018291
theorem B2694313 : Blo 996598 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B6397643 : Blo 996598 6397643 := bstep (se 1 (by rfl) ⟨4798232, by rfl⟩ : syracuseStep 6397643 = 9596465) B9596465
theorem B1122943 : Blo 996598 1122943 := bstep (se 1 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 1122943 = 1684415) B1684415
theorem B2531999 : Blo 996598 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B73802639 : Blo 996598 73802639 := bstep (se 1 (by rfl) ⟨55351979, by rfl⟩ : syracuseStep 73802639 = 110703959) B110703959
theorem B11379689 : Blo 996598 11379689 := bstep (se 2 (by rfl) ⟨4267383, by rfl⟩ : syracuseStep 11379689 = 8534767) B8534767
theorem B32351471 : Blo 996598 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B1124095 : Blo 996598 1124095 := bstep (se 1 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 1124095 = 1686143) B1686143
theorem B1125535 : Blo 996598 1125535 := bstep (se 1 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 1125535 = 1688303) B1688303
theorem B1519055 : Blo 996598 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B6008327 : Blo 996598 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B1683227 : Blo 996598 1683227 := bstep (se 1 (by rfl) ⟨1262420, by rfl⟩ : syracuseStep 1683227 = 2524841) B2524841
theorem B1421983 : Blo 996598 1421983 := bstep (se 1 (by rfl) ⟨1066487, by rfl⟩ : syracuseStep 1421983 = 2132975) B2132975
theorem B9122651 : Blo 996598 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B11384063 : Blo 996598 11384063 := bstep (se 1 (by rfl) ⟨8538047, by rfl⟩ : syracuseStep 11384063 = 17076095) B17076095
theorem B997095 : Blo 996598 997095 := bstep (se 1 (by rfl) ⟨747821, by rfl⟩ : syracuseStep 997095 = 1495643) B1495643
theorem B21608653 : Blo 996598 21608653 := bstep (se 3 (by rfl) ⟨4051622, by rfl⟩ : syracuseStep 21608653 = 8103245) B8103245
theorem B997659 : Blo 996598 997659 := bstep (se 1 (by rfl) ⟨748244, by rfl⟩ : syracuseStep 997659 = 1496489) B1496489
theorem B998395 : Blo 996598 998395 := bstep (se 1 (by rfl) ⟨748796, by rfl⟩ : syracuseStep 998395 = 1497593) B1497593
theorem B998427 : Blo 996598 998427 := bstep (se 1 (by rfl) ⟨748820, by rfl⟩ : syracuseStep 998427 = 1497641) B1497641
theorem B3849527 : Blo 996598 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B998759 : Blo 996598 998759 := bstep (se 1 (by rfl) ⟨749069, by rfl⟩ : syracuseStep 998759 = 1498139) B1498139
theorem B2244455 : Blo 996598 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B999515 : Blo 996598 999515 := bstep (se 1 (by rfl) ⟨749636, by rfl⟩ : syracuseStep 999515 = 1499273) B1499273
theorem B12140857 : Blo 996598 12140857 := bstep (se 2 (by rfl) ⟨4552821, by rfl⟩ : syracuseStep 12140857 = 9105643) B9105643
theorem B1000027 : Blo 996598 1000027 := bstep (se 1 (by rfl) ⟨750020, by rfl⟩ : syracuseStep 1000027 = 1500041) B1500041
theorem B1065727 : Blo 996598 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1262719 : Blo 996598 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B2704511 : Blo 996598 2704511 := bstep (se 1 (by rfl) ⟨2028383, by rfl⟩ : syracuseStep 2704511 = 4056767) B4056767
theorem B5064605 : Blo 996598 5064605 := bstep (se 3 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 5064605 = 1899227) B1899227
theorem B2246651 : Blo 996598 2246651 := bstep (se 1 (by rfl) ⟨1684988, by rfl⟩ : syracuseStep 2246651 = 3369977) B3369977
theorem B25283315 : Blo 996598 25283315 := bstep (se 1 (by rfl) ⟨18962486, by rfl⟩ : syracuseStep 25283315 = 37924973) B37924973
theorem B4049903 : Blo 996598 4049903 := bstep (se 1 (by rfl) ⟨3037427, by rfl⟩ : syracuseStep 4049903 = 6074855) B6074855
theorem B2838203 : Blo 996598 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B2248559 : Blo 996598 2248559 := bstep (se 1 (by rfl) ⟨1686419, by rfl⟩ : syracuseStep 2248559 = 3372839) B3372839
theorem B1495247 : Blo 996598 1495247 := bstep (se 1 (by rfl) ⟨1121435, by rfl⟩ : syracuseStep 1495247 = 2242871) B2242871
theorem B5787881 : Blo 996598 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B1495295 : Blo 996598 1495295 := bstep (se 1 (by rfl) ⟨1121471, by rfl⟩ : syracuseStep 1495295 = 2242943) B2242943
theorem B2249081 : Blo 996598 2249081 := bstep (se 2 (by rfl) ⟨843405, by rfl⟩ : syracuseStep 2249081 = 1686811) B1686811
theorem B2249243 : Blo 996598 2249243 := bstep (se 1 (by rfl) ⟨1686932, by rfl⟩ : syracuseStep 2249243 = 3373865) B3373865
theorem B1495721 : Blo 996598 1495721 := bstep (se 2 (by rfl) ⟨560895, by rfl⟩ : syracuseStep 1495721 = 1121791) B1121791
theorem B2249441 : Blo 996598 2249441 := bstep (se 2 (by rfl) ⟨843540, by rfl⟩ : syracuseStep 2249441 = 1687081) B1687081
theorem B1495847 : Blo 996598 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B54711359 : Blo 996598 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B1496447 : Blo 996598 1496447 := bstep (se 1 (by rfl) ⟨1122335, by rfl⟩ : syracuseStep 1496447 = 2244671) B2244671
theorem B1496543 : Blo 996598 1496543 := bstep (se 1 (by rfl) ⟨1122407, by rfl⟩ : syracuseStep 1496543 = 2244815) B2244815
theorem B394221275 : Blo 996598 394221275 := bstep (se 1 (by rfl) ⟨295665956, by rfl⟩ : syracuseStep 394221275 = 591331913) B591331913
theorem B2054087 : Blo 996598 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B1497191 : Blo 996598 1497191 := bstep (se 1 (by rfl) ⟨1122893, by rfl⟩ : syracuseStep 1497191 = 2245787) B2245787
theorem B2250863 : Blo 996598 2250863 := bstep (se 1 (by rfl) ⟨1688147, by rfl⟩ : syracuseStep 2250863 = 3376295) B3376295
theorem B1497647 : Blo 996598 1497647 := bstep (se 1 (by rfl) ⟨1123235, by rfl⟩ : syracuseStep 1497647 = 2246471) B2246471
theorem B1498409 : Blo 996598 1498409 := bstep (se 2 (by rfl) ⟨561903, by rfl⟩ : syracuseStep 1498409 = 1123807) B1123807
theorem B1499129 : Blo 996598 1499129 := bstep (se 2 (by rfl) ⟨562173, by rfl⟩ : syracuseStep 1499129 = 1124347) B1124347
theorem B1892393 : Blo 996598 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B1499183 : Blo 996598 1499183 := bstep (se 1 (by rfl) ⟨1124387, by rfl⟩ : syracuseStep 1499183 = 2248775) B2248775
theorem B1499615 : Blo 996598 1499615 := bstep (se 1 (by rfl) ⟨1124711, by rfl⟩ : syracuseStep 1499615 = 2249423) B2249423
theorem B1893289 : Blo 996598 1893289 := bstep (se 2 (by rfl) ⟨709983, by rfl⟩ : syracuseStep 1893289 = 1419967) B1419967
theorem B3794627 : Blo 996598 3794627 := bstep (se 1 (by rfl) ⟨2845970, by rfl⟩ : syracuseStep 3794627 = 5691941) B5691941
theorem B5400391 : Blo 996598 5400391 := bstep (se 1 (by rfl) ⟨4050293, by rfl⟩ : syracuseStep 5400391 = 8100587) B8100587
theorem B32401295 : Blo 996598 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B11397185 : Blo 996598 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B12773447 : Blo 996598 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B5401255 : Blo 996598 5401255 := bstep (se 1 (by rfl) ⟨4050941, by rfl⟩ : syracuseStep 5401255 = 8101883) B8101883
theorem B5401343 : Blo 996598 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B7597151 : Blo 996598 7597151 := bstep (se 1 (by rfl) ⟨5697863, by rfl⟩ : syracuseStep 7597151 = 11395727) B11395727
theorem B3370139 : Blo 996598 3370139 := bstep (se 1 (by rfl) ⟨2527604, by rfl⟩ : syracuseStep 3370139 = 5055209) B5055209
theorem B3370247 : Blo 996598 3370247 := bstep (se 1 (by rfl) ⟨2527685, by rfl⟩ : syracuseStep 3370247 = 5055371) B5055371
theorem B1011227 : Blo 996598 1011227 := bstep (se 1 (by rfl) ⟨758420, by rfl⟩ : syracuseStep 1011227 = 1516841) B1516841
theorem B1601051 : Blo 996598 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B3371003 : Blo 996598 3371003 := bstep (se 1 (by rfl) ⟨2528252, by rfl⟩ : syracuseStep 3371003 = 5056505) B5056505
theorem B25587899 : Blo 996598 25587899 := bstep (se 1 (by rfl) ⟨19190924, by rfl⟩ : syracuseStep 25587899 = 38381849) B38381849
theorem B3372137 : Blo 996598 3372137 := bstep (se 2 (by rfl) ⟨1264551, by rfl⟩ : syracuseStep 3372137 = 2529103) B2529103
theorem B11368025 : Blo 996598 11368025 := bstep (se 2 (by rfl) ⟨4263009, by rfl⟩ : syracuseStep 11368025 = 8526019) B8526019
theorem B3373811 : Blo 996598 3373811 := bstep (se 1 (by rfl) ⟨2530358, by rfl⟩ : syracuseStep 3373811 = 5060717) B5060717
theorem B46104329 : Blo 996598 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B14418107 : Blo 996598 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B11534683 : Blo 996598 11534683 := bstep (se 1 (by rfl) ⟨8651012, by rfl⟩ : syracuseStep 11534683 = 17302025) B17302025
theorem B16187809 : Blo 996598 16187809 := bstep (se 2 (by rfl) ⟨6070428, by rfl⟩ : syracuseStep 16187809 = 12140857) B12140857
theorem B1803007 : Blo 996598 1803007 := bstep (se 1 (by rfl) ⟨1352255, by rfl⟩ : syracuseStep 1803007 = 2704511) B2704511
theorem B2524385 : Blo 996598 2524385 := bstep (se 2 (by rfl) ⟨946644, by rfl⟩ : syracuseStep 2524385 = 1893289) B1893289
theorem B3376403 : Blo 996598 3376403 := bstep (se 1 (by rfl) ⟨2532302, by rfl⟩ : syracuseStep 3376403 = 5064605) B5064605
theorem B36474239 : Blo 996598 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B6230351 : Blo 996598 6230351 := bstep (se 1 (by rfl) ⟨4672763, by rfl⟩ : syracuseStep 6230351 = 9345527) B9345527
theorem B4265095 : Blo 996598 4265095 := bstep (se 1 (by rfl) ⟨3198821, by rfl⟩ : syracuseStep 4265095 = 6397643) B6397643
theorem B10786421 : Blo 996598 10786421 := bstep (se 5 (by rfl) ⟨505613, by rfl⟩ : syracuseStep 10786421 = 1011227) B1011227
theorem B21567647 : Blo 996598 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B2529751 : Blo 996598 2529751 := bstep (se 1 (by rfl) ⟨1897313, by rfl⟩ : syracuseStep 2529751 = 3794627) B3794627
theorem B21600863 : Blo 996598 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B4005551 : Blo 996598 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B1122151 : Blo 996598 1122151 := bstep (se 1 (by rfl) ⟨841613, by rfl⟩ : syracuseStep 1122151 = 1683227) B1683227
theorem B28811537 : Blo 996598 28811537 := bstep (se 2 (by rfl) ⟨10804326, by rfl⟩ : syracuseStep 28811537 = 21608653) B21608653
theorem B7578683 : Blo 996598 7578683 := bstep (se 1 (by rfl) ⟨5684012, by rfl⟩ : syracuseStep 7578683 = 11368025) B11368025
theorem B4269469 : Blo 996598 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B2566351 : Blo 996598 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B1683625 : Blo 996598 1683625 := bstep (se 2 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 1683625 = 1262719) B1262719
theorem B16855543 : Blo 996598 16855543 := bstep (se 1 (by rfl) ⟨12641657, by rfl⟩ : syracuseStep 16855543 = 25283315) B25283315
theorem B2699935 : Blo 996598 2699935 := bstep (se 1 (by rfl) ⟨2024951, by rfl⟩ : syracuseStep 2699935 = 4049903) B4049903
theorem B996831 : Blo 996598 996831 := bstep (se 1 (by rfl) ⟨747623, by rfl⟩ : syracuseStep 996831 = 1495247) B1495247
theorem B996863 : Blo 996598 996863 := bstep (se 1 (by rfl) ⟨747647, by rfl⟩ : syracuseStep 996863 = 1495295) B1495295
theorem B997147 : Blo 996598 997147 := bstep (se 1 (by rfl) ⟨747860, by rfl⟩ : syracuseStep 997147 = 1495721) B1495721
theorem B997231 : Blo 996598 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B997631 : Blo 996598 997631 := bstep (se 1 (by rfl) ⟨748223, by rfl⟩ : syracuseStep 997631 = 1496447) B1496447
theorem B997695 : Blo 996598 997695 := bstep (se 1 (by rfl) ⟨748271, by rfl⟩ : syracuseStep 997695 = 1496543) B1496543
theorem B262814183 : Blo 996598 262814183 := bstep (se 1 (by rfl) ⟨197110637, by rfl⟩ : syracuseStep 262814183 = 394221275) B394221275
theorem B5683877 : Blo 996598 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B998127 : Blo 996598 998127 := bstep (se 1 (by rfl) ⟨748595, by rfl⟩ : syracuseStep 998127 = 1497191) B1497191
theorem B998431 : Blo 996598 998431 := bstep (se 1 (by rfl) ⟨748823, by rfl⟩ : syracuseStep 998431 = 1497647) B1497647
theorem B998939 : Blo 996598 998939 := bstep (se 1 (by rfl) ⟨749204, by rfl⟩ : syracuseStep 998939 = 1498409) B1498409
theorem B999419 : Blo 996598 999419 := bstep (se 1 (by rfl) ⟨749564, by rfl⟩ : syracuseStep 999419 = 1499129) B1499129
theorem B1261595 : Blo 996598 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B999455 : Blo 996598 999455 := bstep (se 1 (by rfl) ⟨749591, by rfl⟩ : syracuseStep 999455 = 1499183) B1499183
theorem B999743 : Blo 996598 999743 := bstep (se 1 (by rfl) ⟨749807, by rfl⟩ : syracuseStep 999743 = 1499615) B1499615
theorem B1687999 : Blo 996598 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B49201759 : Blo 996598 49201759 := bstep (se 1 (by rfl) ⟨36901319, by rfl⟩ : syracuseStep 49201759 = 73802639) B73802639
theorem B7586459 : Blo 996598 7586459 := bstep (se 1 (by rfl) ⟨5689844, by rfl⟩ : syracuseStep 7586459 = 11379689) B11379689
theorem B3195617 : Blo 996598 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B14369669 : Blo 996598 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B9094625 : Blo 996598 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B36488825 : Blo 996598 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B14403581 : Blo 996598 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B5064767 : Blo 996598 5064767 := bstep (se 1 (by rfl) ⟨3798575, by rfl⟩ : syracuseStep 5064767 = 7597151) B7597151
theorem B2246759 : Blo 996598 2246759 := bstep (se 1 (by rfl) ⟨1685069, by rfl⟩ : syracuseStep 2246759 = 3370139) B3370139
theorem B2246831 : Blo 996598 2246831 := bstep (se 1 (by rfl) ⟨1685123, by rfl⟩ : syracuseStep 2246831 = 3370247) B3370247
theorem B2247335 : Blo 996598 2247335 := bstep (se 1 (by rfl) ⟨1685501, by rfl⟩ : syracuseStep 2247335 = 3371003) B3371003
theorem B17058599 : Blo 996598 17058599 := bstep (se 1 (by rfl) ⟨12793949, by rfl⟩ : syracuseStep 17058599 = 25587899) B25587899
theorem B6081767 : Blo 996598 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B2248091 : Blo 996598 2248091 := bstep (se 1 (by rfl) ⟨1686068, by rfl⟩ : syracuseStep 2248091 = 3372137) B3372137
theorem B7589375 : Blo 996598 7589375 := bstep (se 1 (by rfl) ⟨5692031, by rfl⟩ : syracuseStep 7589375 = 11384063) B11384063
theorem B2249207 : Blo 996598 2249207 := bstep (se 1 (by rfl) ⟨1686905, by rfl⟩ : syracuseStep 2249207 = 3373811) B3373811
theorem B1496303 : Blo 996598 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B2250143 : Blo 996598 2250143 := bstep (se 1 (by rfl) ⟨1687607, by rfl⟩ : syracuseStep 2250143 = 3375215) B3375215
theorem B1201663 : Blo 996598 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B1497257 : Blo 996598 1497257 := bstep (se 2 (by rfl) ⟨561471, by rfl⟩ : syracuseStep 1497257 = 1122943) B1122943
theorem B1497767 : Blo 996598 1497767 := bstep (se 1 (by rfl) ⟨1123325, by rfl⟩ : syracuseStep 1497767 = 2246651) B2246651
theorem B1498793 : Blo 996598 1498793 := bstep (se 2 (by rfl) ⟨562047, by rfl⟩ : syracuseStep 1498793 = 1124095) B1124095
theorem B7200521 : Blo 996598 7200521 := bstep (se 2 (by rfl) ⟨2700195, by rfl⟩ : syracuseStep 7200521 = 5400391) B5400391
theorem B1892135 : Blo 996598 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B1499039 : Blo 996598 1499039 := bstep (se 1 (by rfl) ⟨1124279, by rfl⟩ : syracuseStep 1499039 = 2248559) B2248559
theorem B3858587 : Blo 996598 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B1499387 : Blo 996598 1499387 := bstep (se 1 (by rfl) ⟨1124540, by rfl⟩ : syracuseStep 1499387 = 2249081) B2249081
theorem B1499495 : Blo 996598 1499495 := bstep (se 1 (by rfl) ⟨1124621, by rfl⟩ : syracuseStep 1499495 = 2249243) B2249243
theorem B1499627 : Blo 996598 1499627 := bstep (se 1 (by rfl) ⟨1124720, by rfl⟩ : syracuseStep 1499627 = 2249441) B2249441
theorem B7201673 : Blo 996598 7201673 := bstep (se 2 (by rfl) ⟨2700627, by rfl⟩ : syracuseStep 7201673 = 5401255) B5401255
theorem B1369391 : Blo 996598 1369391 := bstep (se 1 (by rfl) ⟨1027043, by rfl⟩ : syracuseStep 1369391 = 2054087) B2054087
theorem B1500575 : Blo 996598 1500575 := bstep (se 1 (by rfl) ⟨1125431, by rfl⟩ : syracuseStep 1500575 = 2250863) B2250863
theorem B1500713 : Blo 996598 1500713 := bstep (se 2 (by rfl) ⟨562767, by rfl⟩ : syracuseStep 1500713 = 1125535) B1125535
theorem B1895977 : Blo 996598 1895977 := bstep (se 2 (by rfl) ⟨710991, by rfl⟩ : syracuseStep 1895977 = 1421983) B1421983
theorem B7598123 : Blo 996598 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B8515631 : Blo 996598 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B1012703 : Blo 996598 1012703 := bstep (se 1 (by rfl) ⟨759527, by rfl⟩ : syracuseStep 1012703 = 1519055) B1519055
theorem B34634981 : Blo 996598 34634981 := bstep (se 4 (by rfl) ⟨3247029, by rfl⟩ : syracuseStep 34634981 = 6494059) B6494059
theorem B30736219 : Blo 996598 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B6063083 : Blo 996598 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B9602387 : Blo 996598 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B3376511 : Blo 996598 3376511 := bstep (se 1 (by rfl) ⟨2532383, by rfl⟩ : syracuseStep 3376511 = 5064767) B5064767
theorem B11372399 : Blo 996598 11372399 := bstep (se 1 (by rfl) ⟨8529299, by rfl⟩ : syracuseStep 11372399 = 17058599) B17058599
theorem B8521645 : Blo 996598 8521645 := bstep (se 3 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 8521645 = 3195617) B3195617
theorem B24316159 : Blo 996598 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B262409381 : Blo 996598 262409381 := bstep (se 4 (by rfl) ⟨24600879, by rfl⟩ : syracuseStep 262409381 = 49201759) B49201759
theorem B2527969 : Blo 996598 2527969 := bstep (se 2 (by rfl) ⟨947988, by rfl⟩ : syracuseStep 2527969 = 1895977) B1895977
theorem B19207691 : Blo 996598 19207691 := bstep (se 1 (by rfl) ⟨14405768, by rfl⟩ : syracuseStep 19207691 = 28811537) B28811537
theorem B57513725 : Blo 996598 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B5052455 : Blo 996598 5052455 := bstep (se 1 (by rfl) ⟨3789341, by rfl⟩ : syracuseStep 5052455 = 7578683) B7578683
theorem B5677087 : Blo 996598 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B9612071 : Blo 996598 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B5057639 : Blo 996598 5057639 := bstep (se 1 (by rfl) ⟨3793229, by rfl⟩ : syracuseStep 5057639 = 7586459) B7586459
theorem B15379577 : Blo 996598 15379577 := bstep (se 2 (by rfl) ⟨5767341, by rfl⟩ : syracuseStep 15379577 = 11534683) B11534683
theorem B9579779 : Blo 996598 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B1682923 : Blo 996598 1682923 := bstep (se 1 (by rfl) ⟨1262192, by rfl⟩ : syracuseStep 1682923 = 2524385) B2524385
theorem B2404009 : Blo 996598 2404009 := bstep (se 2 (by rfl) ⟨901503, by rfl⟩ : syracuseStep 2404009 = 1803007) B1803007
theorem B24325883 : Blo 996598 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B5059583 : Blo 996598 5059583 := bstep (se 1 (by rfl) ⟨3794687, by rfl⟩ : syracuseStep 5059583 = 7589375) B7589375
theorem B2700541 : Blo 996598 2700541 := bstep (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) B1012703
theorem B3421801 : Blo 996598 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B997535 : Blo 996598 997535 := bstep (se 1 (by rfl) ⟨748151, by rfl⟩ : syracuseStep 997535 = 1496303) B1496303
theorem B14399653 : Blo 996598 14399653 := bstep (se 4 (by rfl) ⟨1349967, by rfl⟩ : syracuseStep 14399653 = 2699935) B2699935
theorem B7190947 : Blo 996598 7190947 := bstep (se 1 (by rfl) ⟨5393210, by rfl⟩ : syracuseStep 7190947 = 10786421) B10786421
theorem B998171 : Blo 996598 998171 := bstep (se 1 (by rfl) ⟨748628, by rfl⟩ : syracuseStep 998171 = 1497257) B1497257
theorem B14400575 : Blo 996598 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B998511 : Blo 996598 998511 := bstep (se 1 (by rfl) ⟨748883, by rfl⟩ : syracuseStep 998511 = 1497767) B1497767
theorem B999195 : Blo 996598 999195 := bstep (se 1 (by rfl) ⟨749396, by rfl⟩ : syracuseStep 999195 = 1498793) B1498793
theorem B4800347 : Blo 996598 4800347 := bstep (se 1 (by rfl) ⟨3600260, by rfl⟩ : syracuseStep 4800347 = 7200521) B7200521
theorem B1261423 : Blo 996598 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B999359 : Blo 996598 999359 := bstep (se 1 (by rfl) ⟨749519, by rfl⟩ : syracuseStep 999359 = 1499039) B1499039
theorem B2572391 : Blo 996598 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B999591 : Blo 996598 999591 := bstep (se 1 (by rfl) ⟨749693, by rfl⟩ : syracuseStep 999591 = 1499387) B1499387
theorem B2244833 : Blo 996598 2244833 := bstep (se 2 (by rfl) ⟨841812, by rfl⟩ : syracuseStep 2244833 = 1683625) B1683625
theorem B999663 : Blo 996598 999663 := bstep (se 1 (by rfl) ⟨749747, by rfl⟩ : syracuseStep 999663 = 1499495) B1499495
theorem B999751 : Blo 996598 999751 := bstep (se 1 (by rfl) ⟨749813, by rfl⟩ : syracuseStep 999751 = 1499627) B1499627
theorem B4801115 : Blo 996598 4801115 := bstep (se 1 (by rfl) ⟨3600836, by rfl⟩ : syracuseStep 4801115 = 7201673) B7201673
theorem B1000383 : Blo 996598 1000383 := bstep (se 1 (by rfl) ⟨750287, by rfl⟩ : syracuseStep 1000383 = 1500575) B1500575
theorem B1000475 : Blo 996598 1000475 := bstep (se 1 (by rfl) ⟨750356, by rfl⟩ : syracuseStep 1000475 = 1500713) B1500713
theorem B5686793 : Blo 996598 5686793 := bstep (se 2 (by rfl) ⟨2132547, by rfl⟩ : syracuseStep 5686793 = 4265095) B4265095
theorem B5065415 : Blo 996598 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B3789251 : Blo 996598 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B23089987 : Blo 996598 23089987 := bstep (se 1 (by rfl) ⟨17317490, by rfl⟩ : syracuseStep 23089987 = 34634981) B34634981
theorem B40981625 : Blo 996598 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B1496201 : Blo 996598 1496201 := bstep (se 2 (by rfl) ⟨561075, by rfl⟩ : syracuseStep 1496201 = 1122151) B1122151
theorem B3364253 : Blo 996598 3364253 := bstep (se 3 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 3364253 = 1261595) B1261595
theorem B21583745 : Blo 996598 21583745 := bstep (se 2 (by rfl) ⟨8093904, by rfl⟩ : syracuseStep 21583745 = 16187809) B16187809
theorem B2250665 : Blo 996598 2250665 := bstep (se 2 (by rfl) ⟨843999, by rfl⟩ : syracuseStep 2250665 = 1687999) B1687999
theorem B2250935 : Blo 996598 2250935 := bstep (se 1 (by rfl) ⟨1688201, by rfl⟩ : syracuseStep 2250935 = 3376403) B3376403
theorem B1497839 : Blo 996598 1497839 := bstep (se 1 (by rfl) ⟨1123379, by rfl⟩ : syracuseStep 1497839 = 2246759) B2246759
theorem B1497887 : Blo 996598 1497887 := bstep (se 1 (by rfl) ⟨1123415, by rfl⟩ : syracuseStep 1497887 = 2246831) B2246831
theorem B1498223 : Blo 996598 1498223 := bstep (se 1 (by rfl) ⟨1123667, by rfl⟩ : syracuseStep 1498223 = 2247335) B2247335
theorem B5692625 : Blo 996598 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B4054511 : Blo 996598 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B1498727 : Blo 996598 1498727 := bstep (se 1 (by rfl) ⟨1124045, by rfl⟩ : syracuseStep 1498727 = 2248091) B2248091
theorem B4153567 : Blo 996598 4153567 := bstep (se 1 (by rfl) ⟨3115175, by rfl⟩ : syracuseStep 4153567 = 6230351) B6230351
theorem B1499471 : Blo 996598 1499471 := bstep (se 1 (by rfl) ⟨1124603, by rfl⟩ : syracuseStep 1499471 = 2249207) B2249207
theorem B14606837 : Blo 996598 14606837 := bstep (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) B1369391
theorem B1500095 : Blo 996598 1500095 := bstep (se 1 (by rfl) ⟨1125071, by rfl⟩ : syracuseStep 1500095 = 2250143) B2250143
theorem B22474057 : Blo 996598 22474057 := bstep (se 2 (by rfl) ⟨8427771, by rfl⟩ : syracuseStep 22474057 = 16855543) B16855543
theorem B1602217 : Blo 996598 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B3373001 : Blo 996598 3373001 := bstep (se 2 (by rfl) ⟨1264875, by rfl⟩ : syracuseStep 3373001 = 2529751) B2529751
theorem B175209455 : Blo 996598 175209455 := bstep (se 1 (by rfl) ⟨131407091, by rfl⟩ : syracuseStep 175209455 = 262814183) B262814183
theorem B10681469 : Blo 996598 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B7569449 : Blo 996598 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B5538089 : Blo 996598 5538089 := bstep (se 2 (by rfl) ⟨2076783, by rfl⟩ : syracuseStep 5538089 = 4153567) B4153567
theorem B3376943 : Blo 996598 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B2526167 : Blo 996598 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B38342483 : Blo 996598 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B14389163 : Blo 996598 14389163 := bstep (se 1 (by rfl) ⟨10791872, by rfl⟩ : syracuseStep 14389163 = 21583745) B21583745
theorem B9737891 : Blo 996598 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B2136289 : Blo 996598 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B4562401 : Blo 996598 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B7120979 : Blo 996598 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B1681897 : Blo 996598 1681897 := bstep (se 2 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 1681897 = 1261423) B1261423
theorem B1714927 : Blo 996598 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B4042055 : Blo 996598 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B6401591 : Blo 996598 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B7581599 : Blo 996598 7581599 := bstep (se 1 (by rfl) ⟨5686199, by rfl⟩ : syracuseStep 7581599 = 11372399) B11372399
theorem B32421545 : Blo 996598 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B997467 : Blo 996598 997467 := bstep (se 1 (by rfl) ⟨748100, by rfl⟩ : syracuseStep 997467 = 1496201) B1496201
theorem B2242835 : Blo 996598 2242835 := bstep (se 1 (by rfl) ⟨1682126, by rfl⟩ : syracuseStep 2242835 = 3364253) B3364253
theorem B29965409 : Blo 996598 29965409 := bstep (se 2 (by rfl) ⟨11237028, by rfl⟩ : syracuseStep 29965409 = 22474057) B22474057
theorem B998559 : Blo 996598 998559 := bstep (se 1 (by rfl) ⟨748919, by rfl⟩ : syracuseStep 998559 = 1497839) B1497839
theorem B998591 : Blo 996598 998591 := bstep (se 1 (by rfl) ⟨748943, by rfl⟩ : syracuseStep 998591 = 1497887) B1497887
theorem B2243897 : Blo 996598 2243897 := bstep (se 2 (by rfl) ⟨841461, by rfl⟩ : syracuseStep 2243897 = 1682923) B1682923
theorem B998815 : Blo 996598 998815 := bstep (se 1 (by rfl) ⟨749111, by rfl⟩ : syracuseStep 998815 = 1498223) B1498223
theorem B2703007 : Blo 996598 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B999151 : Blo 996598 999151 := bstep (se 1 (by rfl) ⟨749363, by rfl⟩ : syracuseStep 999151 = 1498727) B1498727
theorem B999647 : Blo 996598 999647 := bstep (se 1 (by rfl) ⟨749735, by rfl⟩ : syracuseStep 999647 = 1499471) B1499471
theorem B1000063 : Blo 996598 1000063 := bstep (se 1 (by rfl) ⟨750047, by rfl⟩ : syracuseStep 1000063 = 1500095) B1500095
theorem B30786649 : Blo 996598 30786649 := bstep (se 2 (by rfl) ⟨11544993, by rfl⟩ : syracuseStep 30786649 = 23089987) B23089987
theorem B6408047 : Blo 996598 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B9587929 : Blo 996598 9587929 := bstep (se 2 (by rfl) ⟨3595473, by rfl⟩ : syracuseStep 9587929 = 7190947) B7190947
theorem B2248667 : Blo 996598 2248667 := bstep (se 1 (by rfl) ⟨1686500, by rfl⟩ : syracuseStep 2248667 = 3373001) B3373001
theorem B116806303 : Blo 996598 116806303 := bstep (se 1 (by rfl) ⟨87604727, by rfl⟩ : syracuseStep 116806303 = 175209455) B175209455
theorem B3200231 : Blo 996598 3200231 := bstep (se 1 (by rfl) ⟨2400173, by rfl⟩ : syracuseStep 3200231 = 4800347) B4800347
theorem B1496555 : Blo 996598 1496555 := bstep (se 1 (by rfl) ⟨1122416, by rfl⟩ : syracuseStep 1496555 = 2244833) B2244833
theorem B3200743 : Blo 996598 3200743 := bstep (se 1 (by rfl) ⟨2400557, by rfl⟩ : syracuseStep 3200743 = 4801115) B4801115
theorem B2251007 : Blo 996598 2251007 := bstep (se 1 (by rfl) ⟨1688255, by rfl⟩ : syracuseStep 2251007 = 3376511) B3376511
theorem B3791195 : Blo 996598 3791195 := bstep (se 1 (by rfl) ⟨2843396, by rfl⟩ : syracuseStep 3791195 = 5686793) B5686793
theorem B174939587 : Blo 996598 174939587 := bstep (se 1 (by rfl) ⟨131204690, by rfl⟩ : syracuseStep 174939587 = 262409381) B262409381
theorem B11362193 : Blo 996598 11362193 := bstep (se 2 (by rfl) ⟨4260822, by rfl⟩ : syracuseStep 11362193 = 8521645) B8521645
theorem B27321083 : Blo 996598 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B12805127 : Blo 996598 12805127 := bstep (se 1 (by rfl) ⟨9603845, by rfl⟩ : syracuseStep 12805127 = 19207691) B19207691
theorem B1500443 : Blo 996598 1500443 := bstep (se 1 (by rfl) ⟨1125332, by rfl⟩ : syracuseStep 1500443 = 2250665) B2250665
theorem B3368303 : Blo 996598 3368303 := bstep (se 1 (by rfl) ⟨2526227, by rfl⟩ : syracuseStep 3368303 = 5052455) B5052455
theorem B1500623 : Blo 996598 1500623 := bstep (se 1 (by rfl) ⟨1125467, by rfl⟩ : syracuseStep 1500623 = 2250935) B2250935
theorem B3795083 : Blo 996598 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B3205345 : Blo 996598 3205345 := bstep (se 2 (by rfl) ⟨1202004, by rfl⟩ : syracuseStep 3205345 = 2404009) B2404009
theorem B3370625 : Blo 996598 3370625 := bstep (se 2 (by rfl) ⟨1263984, by rfl⟩ : syracuseStep 3370625 = 2527969) B2527969
theorem B3600721 : Blo 996598 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B3371759 : Blo 996598 3371759 := bstep (se 1 (by rfl) ⟨2528819, by rfl⟩ : syracuseStep 3371759 = 5057639) B5057639
theorem B10253051 : Blo 996598 10253051 := bstep (se 1 (by rfl) ⟨7689788, by rfl⟩ : syracuseStep 10253051 = 15379577) B15379577
theorem B6386519 : Blo 996598 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B16217255 : Blo 996598 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B19199537 : Blo 996598 19199537 := bstep (se 2 (by rfl) ⟨7199826, by rfl⟩ : syracuseStep 19199537 = 14399653) B14399653
theorem B3373055 : Blo 996598 3373055 := bstep (se 1 (by rfl) ⟨2529791, by rfl⟩ : syracuseStep 3373055 = 5059583) B5059583
theorem B9600383 : Blo 996598 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B5046299 : Blo 996598 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B25561655 : Blo 996598 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B2133487 : Blo 996598 2133487 := bstep (se 1 (by rfl) ⟨1600115, by rfl⟩ : syracuseStep 2133487 = 3200231) B3200231
theorem B6491927 : Blo 996598 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B2527463 : Blo 996598 2527463 := bstep (se 1 (by rfl) ⟨1895597, by rfl⟩ : syracuseStep 2527463 = 3791195) B3791195
theorem B12783905 : Blo 996598 12783905 := bstep (se 2 (by rfl) ⟨4793964, by rfl⟩ : syracuseStep 12783905 = 9587929) B9587929
theorem B116626391 : Blo 996598 116626391 := bstep (se 1 (by rfl) ⟨87469793, by rfl⟩ : syracuseStep 116626391 = 174939587) B174939587
theorem B7574795 : Blo 996598 7574795 := bstep (se 1 (by rfl) ⟨5681096, by rfl⟩ : syracuseStep 7574795 = 11362193) B11362193
theorem B2530055 : Blo 996598 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B2694703 : Blo 996598 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B4267657 : Blo 996598 4267657 := bstep (se 2 (by rfl) ⟨1600371, by rfl⟩ : syracuseStep 4267657 = 3200743) B3200743
theorem B4267727 : Blo 996598 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B5054399 : Blo 996598 5054399 := bstep (se 1 (by rfl) ⟨3790799, by rfl⟩ : syracuseStep 5054399 = 7581599) B7581599
theorem B25601021 : Blo 996598 25601021 := bstep (se 3 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 25601021 = 9600383) B9600383
theorem B4272031 : Blo 996598 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B1684111 : Blo 996598 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B4273793 : Blo 996598 4273793 := bstep (se 2 (by rfl) ⟨1602672, by rfl⟩ : syracuseStep 4273793 = 3205345) B3205345
theorem B2242529 : Blo 996598 2242529 := bstep (se 2 (by rfl) ⟨840948, by rfl⟩ : syracuseStep 2242529 = 1681897) B1681897
theorem B622966949 : Blo 996598 622966949 := bstep (se 4 (by rfl) ⟨58403151, by rfl⟩ : syracuseStep 622966949 = 116806303) B116806303
theorem B997703 : Blo 996598 997703 := bstep (se 1 (by rfl) ⟨748277, by rfl⟩ : syracuseStep 997703 = 1496555) B1496555
theorem B4800961 : Blo 996598 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B8536751 : Blo 996598 8536751 := bstep (se 1 (by rfl) ⟨6402563, by rfl⟩ : syracuseStep 8536751 = 12805127) B12805127
theorem B1000295 : Blo 996598 1000295 := bstep (se 1 (by rfl) ⟨750221, by rfl⟩ : syracuseStep 1000295 = 1500443) B1500443
theorem B2245535 : Blo 996598 2245535 := bstep (se 1 (by rfl) ⟨1684151, by rfl⟩ : syracuseStep 2245535 = 3368303) B3368303
theorem B1000415 : Blo 996598 1000415 := bstep (se 1 (by rfl) ⟨750311, by rfl⟩ : syracuseStep 1000415 = 1500623) B1500623
theorem B2247083 : Blo 996598 2247083 := bstep (se 1 (by rfl) ⟨1685312, by rfl⟩ : syracuseStep 2247083 = 3370625) B3370625
theorem B2247839 : Blo 996598 2247839 := bstep (se 1 (by rfl) ⟨1685879, by rfl⟩ : syracuseStep 2247839 = 3371759) B3371759
theorem B6835367 : Blo 996598 6835367 := bstep (se 1 (by rfl) ⟨5126525, by rfl⟩ : syracuseStep 6835367 = 10253051) B10253051
theorem B12799691 : Blo 996598 12799691 := bstep (se 1 (by rfl) ⟨9599768, by rfl⟩ : syracuseStep 12799691 = 19199537) B19199537
theorem B21614363 : Blo 996598 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B2248703 : Blo 996598 2248703 := bstep (se 1 (by rfl) ⟨1686527, by rfl⟩ : syracuseStep 2248703 = 3373055) B3373055
theorem B1495223 : Blo 996598 1495223 := bstep (se 1 (by rfl) ⟨1121417, by rfl⟩ : syracuseStep 1495223 = 2242835) B2242835
theorem B6083201 : Blo 996598 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B19976939 : Blo 996598 19976939 := bstep (se 1 (by rfl) ⟨14982704, by rfl⟩ : syracuseStep 19976939 = 29965409) B29965409
theorem B1495931 : Blo 996598 1495931 := bstep (se 1 (by rfl) ⟨1121948, by rfl⟩ : syracuseStep 1495931 = 2243897) B2243897
theorem B14768237 : Blo 996598 14768237 := bstep (se 3 (by rfl) ⟨2769044, by rfl⟩ : syracuseStep 14768237 = 5538089) B5538089
theorem B2251295 : Blo 996598 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B9592775 : Blo 996598 9592775 := bstep (se 1 (by rfl) ⟨7194581, by rfl⟩ : syracuseStep 9592775 = 14389163) B14389163
theorem B1499111 : Blo 996598 1499111 := bstep (se 1 (by rfl) ⟨1124333, by rfl⟩ : syracuseStep 1499111 = 2248667) B2248667
theorem B2286569 : Blo 996598 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B1500671 : Blo 996598 1500671 := bstep (se 1 (by rfl) ⟨1125503, by rfl⟩ : syracuseStep 1500671 = 2251007) B2251007
theorem B164195461 : Blo 996598 164195461 := bstep (se 4 (by rfl) ⟨15393324, by rfl⟩ : syracuseStep 164195461 = 30786649) B30786649
theorem B18214055 : Blo 996598 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B4747319 : Blo 996598 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B2848385 : Blo 996598 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B4257679 : Blo 996598 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B10811503 : Blo 996598 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B3604009 : Blo 996598 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B16221869 : Blo 996598 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B17041103 : Blo 996598 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B4556911 : Blo 996598 4556911 := bstep (se 1 (by rfl) ⟨3417683, by rfl⟩ : syracuseStep 4556911 = 6835367) B6835367
theorem B4327951 : Blo 996598 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B6097517 : Blo 996598 6097517 := bstep (se 3 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 6097517 = 2286569) B2286569
theorem B8522603 : Blo 996598 8522603 := bstep (se 1 (by rfl) ⟨6391952, by rfl⟩ : syracuseStep 8522603 = 12783905) B12783905
theorem B5049863 : Blo 996598 5049863 := bstep (se 1 (by rfl) ⟨3787397, by rfl⟩ : syracuseStep 5049863 = 7574795) B7574795
theorem B218927281 : Blo 996598 218927281 := bstep (se 2 (by rfl) ⟨82097730, by rfl⟩ : syracuseStep 218927281 = 164195461) B164195461
theorem B6395183 : Blo 996598 6395183 := bstep (se 1 (by rfl) ⟨4796387, by rfl⟩ : syracuseStep 6395183 = 9592775) B9592775
theorem B5676905 : Blo 996598 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B415311299 : Blo 996598 415311299 := bstep (se 1 (by rfl) ⟨311483474, by rfl⟩ : syracuseStep 415311299 = 622966949) B622966949
theorem B6401281 : Blo 996598 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B8533127 : Blo 996598 8533127 := bstep (se 1 (by rfl) ⟨6399845, by rfl⟩ : syracuseStep 8533127 = 12799691) B12799691
theorem B996815 : Blo 996598 996815 := bstep (se 1 (by rfl) ⟨747611, by rfl⟩ : syracuseStep 996815 = 1495223) B1495223
theorem B1684975 : Blo 996598 1684975 := bstep (se 1 (by rfl) ⟨1263731, by rfl⟩ : syracuseStep 1684975 = 2527463) B2527463
theorem B13317959 : Blo 996598 13317959 := bstep (se 1 (by rfl) ⟨9988469, by rfl⟩ : syracuseStep 13317959 = 19976939) B19976939
theorem B997287 : Blo 996598 997287 := bstep (se 1 (by rfl) ⟨747965, by rfl⟩ : syracuseStep 997287 = 1495931) B1495931
theorem B9845491 : Blo 996598 9845491 := bstep (se 1 (by rfl) ⟨7384118, by rfl⟩ : syracuseStep 9845491 = 14768237) B14768237
theorem B1686703 : Blo 996598 1686703 := bstep (se 1 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 1686703 = 2530055) B2530055
theorem B999407 : Blo 996598 999407 := bstep (se 1 (by rfl) ⟨749555, by rfl⟩ : syracuseStep 999407 = 1499111) B1499111
theorem B2245481 : Blo 996598 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B1000447 : Blo 996598 1000447 := bstep (se 1 (by rfl) ⟨750335, by rfl⟩ : syracuseStep 1000447 = 1500671) B1500671
theorem B12142703 : Blo 996598 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B3164879 : Blo 996598 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B1495019 : Blo 996598 1495019 := bstep (se 1 (by rfl) ⟨1121264, by rfl⟩ : syracuseStep 1495019 = 2242529) B2242529
theorem B4805345 : Blo 996598 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B3592937 : Blo 996598 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B5690209 : Blo 996598 5690209 := bstep (se 2 (by rfl) ⟨2133828, by rfl⟩ : syracuseStep 5690209 = 4267657) B4267657
theorem B3364199 : Blo 996598 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B5691167 : Blo 996598 5691167 := bstep (se 1 (by rfl) ⟨4268375, by rfl⟩ : syracuseStep 5691167 = 8536751) B8536751
theorem B1497023 : Blo 996598 1497023 := bstep (se 1 (by rfl) ⟨1122767, by rfl⟩ : syracuseStep 1497023 = 2245535) B2245535
theorem B1498055 : Blo 996598 1498055 := bstep (se 1 (by rfl) ⟨1123541, by rfl⟩ : syracuseStep 1498055 = 2247083) B2247083
theorem B1498559 : Blo 996598 1498559 := bstep (se 1 (by rfl) ⟨1123919, by rfl⟩ : syracuseStep 1498559 = 2247839) B2247839
theorem B14409575 : Blo 996598 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B1499135 : Blo 996598 1499135 := bstep (se 1 (by rfl) ⟨1124351, by rfl⟩ : syracuseStep 1499135 = 2248703) B2248703
theorem B77750927 : Blo 996598 77750927 := bstep (se 1 (by rfl) ⟨58313195, by rfl⟩ : syracuseStep 77750927 = 116626391) B116626391
theorem B7595693 : Blo 996598 7595693 := bstep (se 3 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 7595693 = 2848385) B2848385
theorem B1500863 : Blo 996598 1500863 := bstep (se 1 (by rfl) ⟨1125647, by rfl⟩ : syracuseStep 1500863 = 2251295) B2251295
theorem B2844649 : Blo 996598 2844649 := bstep (se 2 (by rfl) ⟨1066743, by rfl⟩ : syracuseStep 2844649 = 2133487) B2133487
theorem B2845151 : Blo 996598 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B5696041 : Blo 996598 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B3369599 : Blo 996598 3369599 := bstep (se 1 (by rfl) ⟨2527199, by rfl⟩ : syracuseStep 3369599 = 5054399) B5054399
theorem B17067347 : Blo 996598 17067347 := bstep (se 1 (by rfl) ⟨12800510, by rfl⟩ : syracuseStep 17067347 = 25601021) B25601021
theorem B14415337 : Blo 996598 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B2849195 : Blo 996598 2849195 := bstep (se 1 (by rfl) ⟨2136896, by rfl⟩ : syracuseStep 2849195 = 4273793) B4273793
theorem B10814579 : Blo 996598 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B8095135 : Blo 996598 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B4065011 : Blo 996598 4065011 := bstep (se 1 (by rfl) ⟨3048758, by rfl⟩ : syracuseStep 4065011 = 6097517) B6097517
theorem B5770601 : Blo 996598 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B4263455 : Blo 996598 4263455 := bstep (se 1 (by rfl) ⟨3197591, by rfl⟩ : syracuseStep 4263455 = 6395183) B6395183
theorem B9606383 : Blo 996598 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B291903041 : Blo 996598 291903041 := bstep (se 2 (by rfl) ⟨109463640, by rfl⟩ : syracuseStep 291903041 = 218927281) B218927281
theorem B11378231 : Blo 996598 11378231 := bstep (se 1 (by rfl) ⟨8533673, by rfl⟩ : syracuseStep 11378231 = 17067347) B17067347
theorem B5681735 : Blo 996598 5681735 := bstep (se 1 (by rfl) ⟨4261301, by rfl⟩ : syracuseStep 5681735 = 8522603) B8522603
theorem B9581165 : Blo 996598 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B996679 : Blo 996598 996679 := bstep (se 1 (by rfl) ⟨747509, by rfl⟩ : syracuseStep 996679 = 1495019) B1495019
theorem B6075881 : Blo 996598 6075881 := bstep (se 2 (by rfl) ⟨2278455, by rfl⟩ : syracuseStep 6075881 = 4556911) B4556911
theorem B2242799 : Blo 996598 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B998015 : Blo 996598 998015 := bstep (se 1 (by rfl) ⟨748511, by rfl⟩ : syracuseStep 998015 = 1497023) B1497023
theorem B8535041 : Blo 996598 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B998703 : Blo 996598 998703 := bstep (se 1 (by rfl) ⟨749027, by rfl⟩ : syracuseStep 998703 = 1498055) B1498055
theorem B999039 : Blo 996598 999039 := bstep (se 1 (by rfl) ⟨749279, by rfl⟩ : syracuseStep 999039 = 1498559) B1498559
theorem B3784603 : Blo 996598 3784603 := bstep (se 1 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 3784603 = 5676905) B5676905
theorem B999423 : Blo 996598 999423 := bstep (se 1 (by rfl) ⟨749567, by rfl⟩ : syracuseStep 999423 = 1499135) B1499135
theorem B276874199 : Blo 996598 276874199 := bstep (se 1 (by rfl) ⟨207655649, by rfl⟩ : syracuseStep 276874199 = 415311299) B415311299
theorem B5063795 : Blo 996598 5063795 := bstep (se 1 (by rfl) ⟨3797846, by rfl⟩ : syracuseStep 5063795 = 7595693) B7595693
theorem B7586945 : Blo 996598 7586945 := bstep (se 2 (by rfl) ⟨2845104, by rfl⟩ : syracuseStep 7586945 = 5690209) B5690209
theorem B1000575 : Blo 996598 1000575 := bstep (se 1 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 1000575 = 1500863) B1500863
theorem B2246399 : Blo 996598 2246399 := bstep (se 1 (by rfl) ⟨1684799, by rfl⟩ : syracuseStep 2246399 = 3369599) B3369599
theorem B8439677 : Blo 996598 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B19220449 : Blo 996598 19220449 := bstep (se 2 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 19220449 = 14415337) B14415337
theorem B2246633 : Blo 996598 2246633 := bstep (se 2 (by rfl) ⟨842487, by rfl⟩ : syracuseStep 2246633 = 1684975) B1684975
theorem B5688751 : Blo 996598 5688751 := bstep (se 1 (by rfl) ⟨4266563, by rfl⟩ : syracuseStep 5688751 = 8533127) B8533127
theorem B13127321 : Blo 996598 13127321 := bstep (se 2 (by rfl) ⟨4922745, by rfl⟩ : syracuseStep 13127321 = 9845491) B9845491
theorem B2248937 : Blo 996598 2248937 := bstep (se 2 (by rfl) ⟨843351, by rfl⟩ : syracuseStep 2248937 = 1686703) B1686703
theorem B1496987 : Blo 996598 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B11360735 : Blo 996598 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B3366575 : Blo 996598 3366575 := bstep (se 1 (by rfl) ⟨2524931, by rfl⟩ : syracuseStep 3366575 = 5049863) B5049863
theorem B3792865 : Blo 996598 3792865 := bstep (se 2 (by rfl) ⟨1422324, by rfl⟩ : syracuseStep 3792865 = 2844649) B2844649
theorem B3203563 : Blo 996598 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B7594721 : Blo 996598 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B3794111 : Blo 996598 3794111 := bstep (se 1 (by rfl) ⟨2845583, by rfl⟩ : syracuseStep 3794111 = 5691167) B5691167
theorem B35514557 : Blo 996598 35514557 := bstep (se 3 (by rfl) ⟨6658979, by rfl⟩ : syracuseStep 35514557 = 13317959) B13317959
theorem B51833951 : Blo 996598 51833951 := bstep (se 1 (by rfl) ⟨38875463, by rfl⟩ : syracuseStep 51833951 = 77750927) B77750927
theorem B1896767 : Blo 996598 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B1899463 : Blo 996598 1899463 := bstep (se 1 (by rfl) ⟨1424597, by rfl⟩ : syracuseStep 1899463 = 2849195) B2849195
theorem B184582799 : Blo 996598 184582799 := bstep (se 1 (by rfl) ⟨138437099, by rfl⟩ : syracuseStep 184582799 = 276874199) B276874199
theorem B7209719 : Blo 996598 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B3375863 : Blo 996598 3375863 := bstep (se 1 (by rfl) ⟨2531897, by rfl⟩ : syracuseStep 3375863 = 5063795) B5063795
theorem B8751547 : Blo 996598 8751547 := bstep (se 1 (by rfl) ⟨6563660, by rfl⟩ : syracuseStep 8751547 = 13127321) B13127321
theorem B25627265 : Blo 996598 25627265 := bstep (se 2 (by rfl) ⟨9610224, by rfl⟩ : syracuseStep 25627265 = 19220449) B19220449
theorem B7573823 : Blo 996598 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B2529407 : Blo 996598 2529407 := bstep (se 1 (by rfl) ⟨1897055, by rfl⟩ : syracuseStep 2529407 = 3794111) B3794111
theorem B2532617 : Blo 996598 2532617 := bstep (se 2 (by rfl) ⟨949731, by rfl⟩ : syracuseStep 2532617 = 1899463) B1899463
theorem B5057153 : Blo 996598 5057153 := bstep (se 2 (by rfl) ⟨1896432, by rfl⟩ : syracuseStep 5057153 = 3792865) B3792865
theorem B4271417 : Blo 996598 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B5057963 : Blo 996598 5057963 := bstep (se 1 (by rfl) ⟨3793472, by rfl⟩ : syracuseStep 5057963 = 7586945) B7586945
theorem B10793513 : Blo 996598 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B3847067 : Blo 996598 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B6404255 : Blo 996598 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B997991 : Blo 996598 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B7585001 : Blo 996598 7585001 := bstep (se 2 (by rfl) ⟨2844375, by rfl⟩ : syracuseStep 7585001 = 5688751) B5688751
theorem B7585487 : Blo 996598 7585487 := bstep (se 1 (by rfl) ⟨5689115, by rfl⟩ : syracuseStep 7585487 = 11378231) B11378231
theorem B2244383 : Blo 996598 2244383 := bstep (se 1 (by rfl) ⟨1683287, by rfl⟩ : syracuseStep 2244383 = 3366575) B3366575
theorem B5063147 : Blo 996598 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B23676371 : Blo 996598 23676371 := bstep (se 1 (by rfl) ⟨17757278, by rfl⟩ : syracuseStep 23676371 = 35514557) B35514557
theorem B34555967 : Blo 996598 34555967 := bstep (se 1 (by rfl) ⟨25916975, by rfl⟩ : syracuseStep 34555967 = 51833951) B51833951
theorem B1264511 : Blo 996598 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B3787823 : Blo 996598 3787823 := bstep (se 1 (by rfl) ⟨2840867, by rfl⟩ : syracuseStep 3787823 = 5681735) B5681735
theorem B4050587 : Blo 996598 4050587 := bstep (se 1 (by rfl) ⟨3037940, by rfl⟩ : syracuseStep 4050587 = 6075881) B6075881
theorem B1495199 : Blo 996598 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B5690027 : Blo 996598 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B2710007 : Blo 996598 2710007 := bstep (se 1 (by rfl) ⟨2032505, by rfl⟩ : syracuseStep 2710007 = 4065011) B4065011
theorem B1497599 : Blo 996598 1497599 := bstep (se 1 (by rfl) ⟨1123199, by rfl⟩ : syracuseStep 1497599 = 2246399) B2246399
theorem B5626451 : Blo 996598 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B1497755 : Blo 996598 1497755 := bstep (se 1 (by rfl) ⟨1123316, by rfl⟩ : syracuseStep 1497755 = 2246633) B2246633
theorem B2842303 : Blo 996598 2842303 := bstep (se 1 (by rfl) ⟨2131727, by rfl⟩ : syracuseStep 2842303 = 4263455) B4263455
theorem B1499291 : Blo 996598 1499291 := bstep (se 1 (by rfl) ⟨1124468, by rfl⟩ : syracuseStep 1499291 = 2248937) B2248937
theorem B194602027 : Blo 996598 194602027 := bstep (se 1 (by rfl) ⟨145951520, by rfl⟩ : syracuseStep 194602027 = 291903041) B291903041
theorem B6387443 : Blo 996598 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B5046137 : Blo 996598 5046137 := bstep (se 2 (by rfl) ⟨1892301, by rfl⟩ : syracuseStep 5046137 = 3784603) B3784603
theorem B3375431 : Blo 996598 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B23037311 : Blo 996598 23037311 := bstep (se 1 (by rfl) ⟨17277983, by rfl⟩ : syracuseStep 23037311 = 34555967) B34555967
theorem B2525215 : Blo 996598 2525215 := bstep (se 1 (by rfl) ⟨1893911, by rfl⟩ : syracuseStep 2525215 = 3787823) B3787823
theorem B5049215 : Blo 996598 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B1806671 : Blo 996598 1806671 := bstep (se 1 (by rfl) ⟨1355003, by rfl⟩ : syracuseStep 1806671 = 2710007) B2710007
theorem B2564711 : Blo 996598 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B4269503 : Blo 996598 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B5056667 : Blo 996598 5056667 := bstep (se 1 (by rfl) ⟨3792500, by rfl⟩ : syracuseStep 5056667 = 7585001) B7585001
theorem B5056991 : Blo 996598 5056991 := bstep (se 1 (by rfl) ⟨3792743, by rfl⟩ : syracuseStep 5056991 = 7585487) B7585487
theorem B123055199 : Blo 996598 123055199 := bstep (se 1 (by rfl) ⟨92291399, by rfl⟩ : syracuseStep 123055199 = 184582799) B184582799
theorem B259469369 : Blo 996598 259469369 := bstep (se 2 (by rfl) ⟨97301013, by rfl⟩ : syracuseStep 259469369 = 194602027) B194602027
theorem B17084843 : Blo 996598 17084843 := bstep (se 1 (by rfl) ⟨12813632, by rfl⟩ : syracuseStep 17084843 = 25627265) B25627265
theorem B46674917 : Blo 996598 46674917 := bstep (se 4 (by rfl) ⟨4375773, by rfl⟩ : syracuseStep 46674917 = 8751547) B8751547
theorem B2700391 : Blo 996598 2700391 := bstep (se 1 (by rfl) ⟨2025293, by rfl⟩ : syracuseStep 2700391 = 4050587) B4050587
theorem B996799 : Blo 996598 996799 := bstep (se 1 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 996799 = 1495199) B1495199
theorem B1686271 : Blo 996598 1686271 := bstep (se 1 (by rfl) ⟨1264703, by rfl⟩ : syracuseStep 1686271 = 2529407) B2529407
theorem B998399 : Blo 996598 998399 := bstep (se 1 (by rfl) ⟨748799, by rfl⟩ : syracuseStep 998399 = 1497599) B1497599
theorem B3750967 : Blo 996598 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B998503 : Blo 996598 998503 := bstep (se 1 (by rfl) ⟨748877, by rfl⟩ : syracuseStep 998503 = 1497755) B1497755
theorem B999527 : Blo 996598 999527 := bstep (se 1 (by rfl) ⟨749645, by rfl⟩ : syracuseStep 999527 = 1499291) B1499291
theorem B1688411 : Blo 996598 1688411 := bstep (se 1 (by rfl) ⟨1266308, by rfl⟩ : syracuseStep 1688411 = 2532617) B2532617
theorem B7195675 : Blo 996598 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B3789737 : Blo 996598 3789737 := bstep (se 2 (by rfl) ⟨1421151, by rfl⟩ : syracuseStep 3789737 = 2842303) B2842303
theorem B1496255 : Blo 996598 1496255 := bstep (se 1 (by rfl) ⟨1122191, by rfl⟩ : syracuseStep 1496255 = 2244383) B2244383
theorem B3364091 : Blo 996598 3364091 := bstep (se 1 (by rfl) ⟨2523068, by rfl⟩ : syracuseStep 3364091 = 5046137) B5046137
theorem B4806479 : Blo 996598 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B2250575 : Blo 996598 2250575 := bstep (se 1 (by rfl) ⟨1687931, by rfl⟩ : syracuseStep 2250575 = 3375863) B3375863
theorem B15784247 : Blo 996598 15784247 := bstep (se 1 (by rfl) ⟨11838185, by rfl⟩ : syracuseStep 15784247 = 23676371) B23676371
theorem B3793351 : Blo 996598 3793351 := bstep (se 1 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 3793351 = 5690027) B5690027
theorem B3371435 : Blo 996598 3371435 := bstep (se 1 (by rfl) ⟨2528576, by rfl⟩ : syracuseStep 3371435 = 5057153) B5057153
theorem B2847611 : Blo 996598 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B3371975 : Blo 996598 3371975 := bstep (se 1 (by rfl) ⟨2528981, by rfl⟩ : syracuseStep 3371975 = 5057963) B5057963
theorem B3372029 : Blo 996598 3372029 := bstep (se 3 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 3372029 = 1264511) B1264511
theorem B4258295 : Blo 996598 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B4817789 : Blo 996598 4817789 := bstep (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) B1806671
theorem B2526491 : Blo 996598 2526491 := bstep (se 1 (by rfl) ⟨1894868, by rfl⟩ : syracuseStep 2526491 = 3789737) B3789737
theorem B10522831 : Blo 996598 10522831 := bstep (se 1 (by rfl) ⟨7892123, by rfl⟩ : syracuseStep 10522831 = 15784247) B15784247
theorem B12817277 : Blo 996598 12817277 := bstep (se 3 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 12817277 = 4806479) B4806479
theorem B1709807 : Blo 996598 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B1125607 : Blo 996598 1125607 := bstep (se 1 (by rfl) ⟨844205, by rfl⟩ : syracuseStep 1125607 = 1688411) B1688411
theorem B5057801 : Blo 996598 5057801 := bstep (se 2 (by rfl) ⟨1896675, by rfl⟩ : syracuseStep 5057801 = 3793351) B3793351
theorem B997503 : Blo 996598 997503 := bstep (se 1 (by rfl) ⟨748127, by rfl⟩ : syracuseStep 997503 = 1496255) B1496255
theorem B2242727 : Blo 996598 2242727 := bstep (se 1 (by rfl) ⟨1682045, by rfl⟩ : syracuseStep 2242727 = 3364091) B3364091
theorem B20005157 : Blo 996598 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B82036799 : Blo 996598 82036799 := bstep (se 1 (by rfl) ⟨61527599, by rfl⟩ : syracuseStep 82036799 = 123055199) B123055199
theorem B2247623 : Blo 996598 2247623 := bstep (se 1 (by rfl) ⟨1685717, by rfl⟩ : syracuseStep 2247623 = 3371435) B3371435
theorem B11389895 : Blo 996598 11389895 := bstep (se 1 (by rfl) ⟨8542421, by rfl⟩ : syracuseStep 11389895 = 17084843) B17084843
theorem B2247983 : Blo 996598 2247983 := bstep (se 1 (by rfl) ⟨1685987, by rfl⟩ : syracuseStep 2247983 = 3371975) B3371975
theorem B31116611 : Blo 996598 31116611 := bstep (se 1 (by rfl) ⟨23337458, by rfl⟩ : syracuseStep 31116611 = 46674917) B46674917
theorem B2248019 : Blo 996598 2248019 := bstep (se 1 (by rfl) ⟨1686014, by rfl⟩ : syracuseStep 2248019 = 3372029) B3372029
theorem B2248361 : Blo 996598 2248361 := bstep (se 2 (by rfl) ⟨843135, by rfl⟩ : syracuseStep 2248361 = 1686271) B1686271
theorem B2838863 : Blo 996598 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B2250287 : Blo 996598 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B3366143 : Blo 996598 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B3366953 : Blo 996598 3366953 := bstep (se 2 (by rfl) ⟨1262607, by rfl⟩ : syracuseStep 3366953 = 2525215) B2525215
theorem B61432829 : Blo 996598 61432829 := bstep (se 3 (by rfl) ⟨11518655, by rfl⟩ : syracuseStep 61432829 = 23037311) B23037311
theorem B1500383 : Blo 996598 1500383 := bstep (se 1 (by rfl) ⟨1125287, by rfl⟩ : syracuseStep 1500383 = 2250575) B2250575
theorem B9594233 : Blo 996598 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B2846335 : Blo 996598 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B3371111 : Blo 996598 3371111 := bstep (se 1 (by rfl) ⟨2528333, by rfl⟩ : syracuseStep 3371111 = 5056667) B5056667
theorem B3600521 : Blo 996598 3600521 := bstep (se 2 (by rfl) ⟨1350195, by rfl⟩ : syracuseStep 3600521 = 2700391) B2700391
theorem B3371327 : Blo 996598 3371327 := bstep (se 1 (by rfl) ⟨2528495, by rfl⟩ : syracuseStep 3371327 = 5056991) B5056991
theorem B172979579 : Blo 996598 172979579 := bstep (se 1 (by rfl) ⟨129734684, by rfl⟩ : syracuseStep 172979579 = 259469369) B259469369
theorem B1898407 : Blo 996598 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B13336771 : Blo 996598 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B3211859 : Blo 996598 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B54691199 : Blo 996598 54691199 := bstep (se 1 (by rfl) ⟨41018399, by rfl⟩ : syracuseStep 54691199 = 82036799) B82036799
theorem B20744407 : Blo 996598 20744407 := bstep (se 1 (by rfl) ⟨15558305, by rfl⟩ : syracuseStep 20744407 = 31116611) B31116611
theorem B4559485 : Blo 996598 4559485 := bstep (se 3 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 4559485 = 1709807) B1709807
theorem B14030441 : Blo 996598 14030441 := bstep (se 2 (by rfl) ⟨5261415, by rfl⟩ : syracuseStep 14030441 = 10522831) B10522831
theorem B6396155 : Blo 996598 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B2531209 : Blo 996598 2531209 := bstep (se 2 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 2531209 = 1898407) B1898407
theorem B2400347 : Blo 996598 2400347 := bstep (se 1 (by rfl) ⟨1800260, by rfl⟩ : syracuseStep 2400347 = 3600521) B3600521
theorem B115319719 : Blo 996598 115319719 := bstep (se 1 (by rfl) ⟨86489789, by rfl⟩ : syracuseStep 115319719 = 172979579) B172979579
theorem B1684327 : Blo 996598 1684327 := bstep (se 1 (by rfl) ⟨1263245, by rfl⟩ : syracuseStep 1684327 = 2526491) B2526491
theorem B2244095 : Blo 996598 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B2244635 : Blo 996598 2244635 := bstep (se 1 (by rfl) ⟨1683476, by rfl⟩ : syracuseStep 2244635 = 3366953) B3366953
theorem B1000255 : Blo 996598 1000255 := bstep (se 1 (by rfl) ⟨750191, by rfl⟩ : syracuseStep 1000255 = 1500383) B1500383
theorem B2247407 : Blo 996598 2247407 := bstep (se 1 (by rfl) ⟨1685555, by rfl⟩ : syracuseStep 2247407 = 3371111) B3371111
theorem B2247551 : Blo 996598 2247551 := bstep (se 1 (by rfl) ⟨1685663, by rfl⟩ : syracuseStep 2247551 = 3371327) B3371327
theorem B1495151 : Blo 996598 1495151 := bstep (se 1 (by rfl) ⟨1121363, by rfl⟩ : syracuseStep 1495151 = 2242727) B2242727
theorem B1498415 : Blo 996598 1498415 := bstep (se 1 (by rfl) ⟨1123811, by rfl⟩ : syracuseStep 1498415 = 2247623) B2247623
theorem B7593263 : Blo 996598 7593263 := bstep (se 1 (by rfl) ⟨5694947, by rfl⟩ : syracuseStep 7593263 = 11389895) B11389895
theorem B1498655 : Blo 996598 1498655 := bstep (se 1 (by rfl) ⟨1123991, by rfl⟩ : syracuseStep 1498655 = 2247983) B2247983
theorem B1498679 : Blo 996598 1498679 := bstep (se 1 (by rfl) ⟨1124009, by rfl⟩ : syracuseStep 1498679 = 2248019) B2248019
theorem B1498907 : Blo 996598 1498907 := bstep (se 1 (by rfl) ⟨1124180, by rfl⟩ : syracuseStep 1498907 = 2248361) B2248361
theorem B1892575 : Blo 996598 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B8544851 : Blo 996598 8544851 := bstep (se 1 (by rfl) ⟨6408638, by rfl⟩ : syracuseStep 8544851 = 12817277) B12817277
theorem B1500191 : Blo 996598 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B1500809 : Blo 996598 1500809 := bstep (se 2 (by rfl) ⟨562803, by rfl⟩ : syracuseStep 1500809 = 1125607) B1125607
theorem B3795113 : Blo 996598 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B40955219 : Blo 996598 40955219 := bstep (se 1 (by rfl) ⟨30716414, by rfl⟩ : syracuseStep 40955219 = 61432829) B61432829
theorem B3371867 : Blo 996598 3371867 := bstep (se 1 (by rfl) ⟨2528900, by rfl⟩ : syracuseStep 3371867 = 5057801) B5057801
theorem B2523433 : Blo 996598 2523433 := bstep (se 2 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 2523433 = 1892575) B1892575
theorem B27659209 : Blo 996598 27659209 := bstep (se 2 (by rfl) ⟨10372203, by rfl⟩ : syracuseStep 27659209 = 20744407) B20744407
theorem B4264103 : Blo 996598 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B2530075 : Blo 996598 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B27303479 : Blo 996598 27303479 := bstep (se 1 (by rfl) ⟨20477609, by rfl⟩ : syracuseStep 27303479 = 40955219) B40955219
theorem B153759625 : Blo 996598 153759625 := bstep (se 2 (by rfl) ⟨57659859, by rfl⟩ : syracuseStep 153759625 = 115319719) B115319719
theorem B8564957 : Blo 996598 8564957 := bstep (se 3 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 8564957 = 3211859) B3211859
theorem B996767 : Blo 996598 996767 := bstep (se 1 (by rfl) ⟨747575, by rfl⟩ : syracuseStep 996767 = 1495151) B1495151
theorem B9353627 : Blo 996598 9353627 := bstep (se 1 (by rfl) ⟨7015220, by rfl⟩ : syracuseStep 9353627 = 14030441) B14030441
theorem B998943 : Blo 996598 998943 := bstep (se 1 (by rfl) ⟨749207, by rfl⟩ : syracuseStep 998943 = 1498415) B1498415
theorem B5062175 : Blo 996598 5062175 := bstep (se 1 (by rfl) ⟨3796631, by rfl⟩ : syracuseStep 5062175 = 7593263) B7593263
theorem B999103 : Blo 996598 999103 := bstep (se 1 (by rfl) ⟨749327, by rfl⟩ : syracuseStep 999103 = 1498655) B1498655
theorem B999119 : Blo 996598 999119 := bstep (se 1 (by rfl) ⟨749339, by rfl⟩ : syracuseStep 999119 = 1498679) B1498679
theorem B999271 : Blo 996598 999271 := bstep (se 1 (by rfl) ⟨749453, by rfl⟩ : syracuseStep 999271 = 1498907) B1498907
theorem B1000127 : Blo 996598 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B6079313 : Blo 996598 6079313 := bstep (se 2 (by rfl) ⟨2279742, by rfl⟩ : syracuseStep 6079313 = 4559485) B4559485
theorem B1000539 : Blo 996598 1000539 := bstep (se 1 (by rfl) ⟨750404, by rfl⟩ : syracuseStep 1000539 = 1500809) B1500809
theorem B2245769 : Blo 996598 2245769 := bstep (se 2 (by rfl) ⟨842163, by rfl⟩ : syracuseStep 2245769 = 1684327) B1684327
theorem B2247911 : Blo 996598 2247911 := bstep (se 1 (by rfl) ⟨1685933, by rfl⟩ : syracuseStep 2247911 = 3371867) B3371867
theorem B1496063 : Blo 996598 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B1496423 : Blo 996598 1496423 := bstep (se 1 (by rfl) ⟨1122317, by rfl⟩ : syracuseStep 1496423 = 2244635) B2244635
theorem B17782361 : Blo 996598 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B36460799 : Blo 996598 36460799 := bstep (se 1 (by rfl) ⟨27345599, by rfl⟩ : syracuseStep 36460799 = 54691199) B54691199
theorem B1498271 : Blo 996598 1498271 := bstep (se 1 (by rfl) ⟨1123703, by rfl⟩ : syracuseStep 1498271 = 2247407) B2247407
theorem B1498367 : Blo 996598 1498367 := bstep (se 1 (by rfl) ⟨1123775, by rfl⟩ : syracuseStep 1498367 = 2247551) B2247551
theorem B1600231 : Blo 996598 1600231 := bstep (se 1 (by rfl) ⟨1200173, by rfl⟩ : syracuseStep 1600231 = 2400347) B2400347
theorem B5696567 : Blo 996598 5696567 := bstep (se 1 (by rfl) ⟨4272425, by rfl⟩ : syracuseStep 5696567 = 8544851) B8544851
theorem B3374945 : Blo 996598 3374945 := bstep (se 2 (by rfl) ⟨1265604, by rfl⟩ : syracuseStep 3374945 = 2531209) B2531209
theorem B11370941 : Blo 996598 11370941 := bstep (se 3 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 11370941 = 4264103) B4264103
theorem B2133641 : Blo 996598 2133641 := bstep (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) B1600231
theorem B5709971 : Blo 996598 5709971 := bstep (se 1 (by rfl) ⟨4282478, by rfl⟩ : syracuseStep 5709971 = 8564957) B8564957
theorem B590063125 : Blo 996598 590063125 := bstep (se 6 (by rfl) ⟨13829604, by rfl⟩ : syracuseStep 590063125 = 27659209) B27659209
theorem B6235751 : Blo 996598 6235751 := bstep (se 1 (by rfl) ⟨4676813, by rfl⟩ : syracuseStep 6235751 = 9353627) B9353627
theorem B997375 : Blo 996598 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B997615 : Blo 996598 997615 := bstep (se 1 (by rfl) ⟨748211, by rfl⟩ : syracuseStep 997615 = 1496423) B1496423
theorem B998847 : Blo 996598 998847 := bstep (se 1 (by rfl) ⟨749135, by rfl⟩ : syracuseStep 998847 = 1498271) B1498271
theorem B998911 : Blo 996598 998911 := bstep (se 1 (by rfl) ⟨749183, by rfl⟩ : syracuseStep 998911 = 1498367) B1498367
theorem B18202319 : Blo 996598 18202319 := bstep (se 1 (by rfl) ⟨13651739, by rfl⟩ : syracuseStep 18202319 = 27303479) B27303479
theorem B2249963 : Blo 996598 2249963 := bstep (se 1 (by rfl) ⟨1687472, by rfl⟩ : syracuseStep 2249963 = 3374945) B3374945
theorem B3364577 : Blo 996598 3364577 := bstep (se 2 (by rfl) ⟨1261716, by rfl⟩ : syracuseStep 3364577 = 2523433) B2523433
theorem B4052875 : Blo 996598 4052875 := bstep (se 1 (by rfl) ⟨3039656, by rfl⟩ : syracuseStep 4052875 = 6079313) B6079313
theorem B1497179 : Blo 996598 1497179 := bstep (se 1 (by rfl) ⟨1122884, by rfl⟩ : syracuseStep 1497179 = 2245769) B2245769
theorem B1498607 : Blo 996598 1498607 := bstep (se 1 (by rfl) ⟨1123955, by rfl⟩ : syracuseStep 1498607 = 2247911) B2247911
theorem B11854907 : Blo 996598 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B24307199 : Blo 996598 24307199 := bstep (se 1 (by rfl) ⟨18230399, by rfl⟩ : syracuseStep 24307199 = 36460799) B36460799
theorem B3797711 : Blo 996598 3797711 := bstep (se 1 (by rfl) ⟨2848283, by rfl⟩ : syracuseStep 3797711 = 5696567) B5696567
theorem B3373433 : Blo 996598 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B820051333 : Blo 996598 820051333 := bstep (se 4 (by rfl) ⟨76879812, by rfl⟩ : syracuseStep 820051333 = 153759625) B153759625
theorem B3374783 : Blo 996598 3374783 := bstep (se 1 (by rfl) ⟨2531087, by rfl⟩ : syracuseStep 3374783 = 5062175) B5062175
theorem B7903271 : Blo 996598 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B2531807 : Blo 996598 2531807 := bstep (se 1 (by rfl) ⟨1898855, by rfl⟩ : syracuseStep 2531807 = 3797711) B3797711
theorem B12134879 : Blo 996598 12134879 := bstep (se 1 (by rfl) ⟨9101159, by rfl⟩ : syracuseStep 12134879 = 18202319) B18202319
theorem B7580627 : Blo 996598 7580627 := bstep (se 1 (by rfl) ⟨5685470, by rfl⟩ : syracuseStep 7580627 = 11370941) B11370941
theorem B2243051 : Blo 996598 2243051 := bstep (se 1 (by rfl) ⟨1682288, by rfl⟩ : syracuseStep 2243051 = 3364577) B3364577
theorem B998119 : Blo 996598 998119 := bstep (se 1 (by rfl) ⟨748589, by rfl⟩ : syracuseStep 998119 = 1497179) B1497179
theorem B999071 : Blo 996598 999071 := bstep (se 1 (by rfl) ⟨749303, by rfl⟩ : syracuseStep 999071 = 1498607) B1498607
theorem B16204799 : Blo 996598 16204799 := bstep (se 1 (by rfl) ⟨12153599, by rfl⟩ : syracuseStep 16204799 = 24307199) B24307199
theorem B17494428437 : Blo 996598 17494428437 := bstep (se 6 (by rfl) ⟨410025666, by rfl⟩ : syracuseStep 17494428437 = 820051333) B820051333
theorem B2248955 : Blo 996598 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B5689709 : Blo 996598 5689709 := bstep (se 3 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 5689709 = 2133641) B2133641
theorem B2249855 : Blo 996598 2249855 := bstep (se 1 (by rfl) ⟨1687391, by rfl⟩ : syracuseStep 2249855 = 3374783) B3374783
theorem B15226589 : Blo 996598 15226589 := bstep (se 3 (by rfl) ⟨2854985, by rfl⟩ : syracuseStep 15226589 = 5709971) B5709971
theorem B786750833 : Blo 996598 786750833 := bstep (se 2 (by rfl) ⟨295031562, by rfl⟩ : syracuseStep 786750833 = 590063125) B590063125
theorem B1499975 : Blo 996598 1499975 := bstep (se 1 (by rfl) ⟨1124981, by rfl⟩ : syracuseStep 1499975 = 2249963) B2249963
theorem B4157167 : Blo 996598 4157167 := bstep (se 1 (by rfl) ⟨3117875, by rfl⟩ : syracuseStep 4157167 = 6235751) B6235751
theorem B5403833 : Blo 996598 5403833 := bstep (se 2 (by rfl) ⟨2026437, by rfl⟩ : syracuseStep 5403833 = 4052875) B4052875
theorem B11662952291 : Blo 996598 11662952291 := bstep (se 1 (by rfl) ⟨8747214218, by rfl⟩ : syracuseStep 11662952291 = 17494428437) B17494428437
theorem B40604237 : Blo 996598 40604237 := bstep (se 3 (by rfl) ⟨7613294, by rfl⟩ : syracuseStep 40604237 = 15226589) B15226589
theorem B5542889 : Blo 996598 5542889 := bstep (se 2 (by rfl) ⟨2078583, by rfl⟩ : syracuseStep 5542889 = 4157167) B4157167
theorem B5053751 : Blo 996598 5053751 := bstep (se 1 (by rfl) ⟨3790313, by rfl⟩ : syracuseStep 5053751 = 7580627) B7580627
theorem B524500555 : Blo 996598 524500555 := bstep (se 1 (by rfl) ⟨393375416, by rfl⟩ : syracuseStep 524500555 = 786750833) B786750833
theorem B1687871 : Blo 996598 1687871 := bstep (se 1 (by rfl) ⟨1265903, by rfl⟩ : syracuseStep 1687871 = 2531807) B2531807
theorem B999983 : Blo 996598 999983 := bstep (se 1 (by rfl) ⟨749987, by rfl⟩ : syracuseStep 999983 = 1499975) B1499975
theorem B1495367 : Blo 996598 1495367 := bstep (se 1 (by rfl) ⟨1121525, by rfl⟩ : syracuseStep 1495367 = 2243051) B2243051
theorem B43212797 : Blo 996598 43212797 := bstep (se 3 (by rfl) ⟨8102399, by rfl⟩ : syracuseStep 43212797 = 16204799) B16204799
theorem B1499303 : Blo 996598 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B3793139 : Blo 996598 3793139 := bstep (se 1 (by rfl) ⟨2844854, by rfl⟩ : syracuseStep 3793139 = 5689709) B5689709
theorem B1499903 : Blo 996598 1499903 := bstep (se 1 (by rfl) ⟨1124927, by rfl⟩ : syracuseStep 1499903 = 2249855) B2249855
theorem B5268847 : Blo 996598 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B8089919 : Blo 996598 8089919 := bstep (se 1 (by rfl) ⟨6067439, by rfl⟩ : syracuseStep 8089919 = 12134879) B12134879
theorem B3602555 : Blo 996598 3602555 := bstep (se 1 (by rfl) ⟨2701916, by rfl⟩ : syracuseStep 3602555 = 5403833) B5403833
theorem B14781037 : Blo 996598 14781037 := bstep (se 3 (by rfl) ⟨2771444, by rfl⟩ : syracuseStep 14781037 = 5542889) B5542889
theorem B27069491 : Blo 996598 27069491 := bstep (se 1 (by rfl) ⟨20302118, by rfl⟩ : syracuseStep 27069491 = 40604237) B40604237
theorem B28808531 : Blo 996598 28808531 := bstep (se 1 (by rfl) ⟨21606398, by rfl⟩ : syracuseStep 28808531 = 43212797) B43212797
theorem B2528759 : Blo 996598 2528759 := bstep (se 1 (by rfl) ⟨1896569, by rfl⟩ : syracuseStep 2528759 = 3793139) B3793139
theorem B2401703 : Blo 996598 2401703 := bstep (se 1 (by rfl) ⟨1801277, by rfl⟩ : syracuseStep 2401703 = 3602555) B3602555
theorem B1125247 : Blo 996598 1125247 := bstep (se 1 (by rfl) ⟨843935, by rfl⟩ : syracuseStep 1125247 = 1687871) B1687871
theorem B7775301527 : Blo 996598 7775301527 := bstep (se 1 (by rfl) ⟨5831476145, by rfl⟩ : syracuseStep 7775301527 = 11662952291) B11662952291
theorem B7025129 : Blo 996598 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B996911 : Blo 996598 996911 := bstep (se 1 (by rfl) ⟨747683, by rfl⟩ : syracuseStep 996911 = 1495367) B1495367
theorem B999535 : Blo 996598 999535 := bstep (se 1 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 999535 = 1499303) B1499303
theorem B999935 : Blo 996598 999935 := bstep (se 1 (by rfl) ⟨749951, by rfl⟩ : syracuseStep 999935 = 1499903) B1499903
theorem B5393279 : Blo 996598 5393279 := bstep (se 1 (by rfl) ⟨4044959, by rfl⟩ : syracuseStep 5393279 = 8089919) B8089919
theorem B3369167 : Blo 996598 3369167 := bstep (se 1 (by rfl) ⟨2526875, by rfl⟩ : syracuseStep 3369167 = 5053751) B5053751
theorem B699334073 : Blo 996598 699334073 := bstep (se 2 (by rfl) ⟨262250277, by rfl⟩ : syracuseStep 699334073 = 524500555) B524500555
theorem B19205687 : Blo 996598 19205687 := bstep (se 1 (by rfl) ⟨14404265, by rfl⟩ : syracuseStep 19205687 = 28808531) B28808531
theorem B19708049 : Blo 996598 19708049 := bstep (se 2 (by rfl) ⟨7390518, by rfl⟩ : syracuseStep 19708049 = 14781037) B14781037
theorem B1685839 : Blo 996598 1685839 := bstep (se 1 (by rfl) ⟨1264379, by rfl⟩ : syracuseStep 1685839 = 2528759) B2528759
theorem B2246111 : Blo 996598 2246111 := bstep (se 1 (by rfl) ⟨1684583, by rfl⟩ : syracuseStep 2246111 = 3369167) B3369167
theorem B3595519 : Blo 996598 3595519 := bstep (se 1 (by rfl) ⟨2696639, by rfl⟩ : syracuseStep 3595519 = 5393279) B5393279
theorem B18046327 : Blo 996598 18046327 := bstep (se 1 (by rfl) ⟨13534745, by rfl⟩ : syracuseStep 18046327 = 27069491) B27069491
theorem B1500329 : Blo 996598 1500329 := bstep (se 2 (by rfl) ⟨562623, by rfl⟩ : syracuseStep 1500329 = 1125247) B1125247
theorem B1601135 : Blo 996598 1601135 := bstep (se 1 (by rfl) ⟨1200851, by rfl⟩ : syracuseStep 1601135 = 2401703) B2401703
theorem B5183534351 : Blo 996598 5183534351 := bstep (se 1 (by rfl) ⟨3887650763, by rfl⟩ : syracuseStep 5183534351 = 7775301527) B7775301527
theorem B4683419 : Blo 996598 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B466222715 : Blo 996598 466222715 := bstep (se 1 (by rfl) ⟨349667036, by rfl⟩ : syracuseStep 466222715 = 699334073) B699334073
theorem B3455689567 : Blo 996598 3455689567 := bstep (se 1 (by rfl) ⟨2591767175, by rfl⟩ : syracuseStep 3455689567 = 5183534351) B5183534351
theorem B3122279 : Blo 996598 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B4794025 : Blo 996598 4794025 := bstep (se 2 (by rfl) ⟨1797759, by rfl⟩ : syracuseStep 4794025 = 3595519) B3595519
theorem B24061769 : Blo 996598 24061769 := bstep (se 2 (by rfl) ⟨9023163, by rfl⟩ : syracuseStep 24061769 = 18046327) B18046327
theorem B310815143 : Blo 996598 310815143 := bstep (se 1 (by rfl) ⟨233111357, by rfl⟩ : syracuseStep 310815143 = 466222715) B466222715
theorem B1000219 : Blo 996598 1000219 := bstep (se 1 (by rfl) ⟨750164, by rfl⟩ : syracuseStep 1000219 = 1500329) B1500329
theorem B1067423 : Blo 996598 1067423 := bstep (se 1 (by rfl) ⟨800567, by rfl⟩ : syracuseStep 1067423 = 1601135) B1601135
theorem B2247785 : Blo 996598 2247785 := bstep (se 2 (by rfl) ⟨842919, by rfl⟩ : syracuseStep 2247785 = 1685839) B1685839
theorem B1497407 : Blo 996598 1497407 := bstep (se 1 (by rfl) ⟨1123055, by rfl⟩ : syracuseStep 1497407 = 2246111) B2246111
theorem B12803791 : Blo 996598 12803791 := bstep (se 1 (by rfl) ⟨9602843, by rfl⟩ : syracuseStep 12803791 = 19205687) B19205687
theorem B13138699 : Blo 996598 13138699 := bstep (se 1 (by rfl) ⟨9854024, by rfl⟩ : syracuseStep 13138699 = 19708049) B19708049
theorem B6392033 : Blo 996598 6392033 := bstep (se 2 (by rfl) ⟨2397012, by rfl⟩ : syracuseStep 6392033 = 4794025) B4794025
theorem B4607586089 : Blo 996598 4607586089 := bstep (se 2 (by rfl) ⟨1727844783, by rfl⟩ : syracuseStep 4607586089 = 3455689567) B3455689567
theorem B998271 : Blo 996598 998271 := bstep (se 1 (by rfl) ⟨748703, by rfl⟩ : syracuseStep 998271 = 1497407) B1497407
theorem B2081519 : Blo 996598 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B16041179 : Blo 996598 16041179 := bstep (se 1 (by rfl) ⟨12030884, by rfl⟩ : syracuseStep 16041179 = 24061769) B24061769
theorem B207210095 : Blo 996598 207210095 := bstep (se 1 (by rfl) ⟨155407571, by rfl⟩ : syracuseStep 207210095 = 310815143) B310815143
theorem B17518265 : Blo 996598 17518265 := bstep (se 2 (by rfl) ⟨6569349, by rfl⟩ : syracuseStep 17518265 = 13138699) B13138699
theorem B1498523 : Blo 996598 1498523 := bstep (se 1 (by rfl) ⟨1123892, by rfl⟩ : syracuseStep 1498523 = 2247785) B2247785
theorem B2846461 : Blo 996598 2846461 := bstep (se 3 (by rfl) ⟨533711, by rfl⟩ : syracuseStep 2846461 = 1067423) B1067423
theorem B17071721 : Blo 996598 17071721 := bstep (se 2 (by rfl) ⟨6401895, by rfl⟩ : syracuseStep 17071721 = 12803791) B12803791
theorem B4261355 : Blo 996598 4261355 := bstep (se 1 (by rfl) ⟨3196016, by rfl⟩ : syracuseStep 4261355 = 6392033) B6392033
theorem B11381147 : Blo 996598 11381147 := bstep (se 1 (by rfl) ⟨8535860, by rfl⟩ : syracuseStep 11381147 = 17071721) B17071721
theorem B10694119 : Blo 996598 10694119 := bstep (se 1 (by rfl) ⟨8020589, by rfl⟩ : syracuseStep 10694119 = 16041179) B16041179
theorem B11678843 : Blo 996598 11678843 := bstep (se 1 (by rfl) ⟨8759132, by rfl⟩ : syracuseStep 11678843 = 17518265) B17518265
theorem B999015 : Blo 996598 999015 := bstep (se 1 (by rfl) ⟨749261, by rfl⟩ : syracuseStep 999015 = 1498523) B1498523
theorem B22202869 : Blo 996598 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B3071724059 : Blo 996598 3071724059 := bstep (se 1 (by rfl) ⟨2303793044, by rfl⟩ : syracuseStep 3071724059 = 4607586089) B4607586089
theorem B138140063 : Blo 996598 138140063 := bstep (se 1 (by rfl) ⟨103605047, by rfl⟩ : syracuseStep 138140063 = 207210095) B207210095
theorem B3795281 : Blo 996598 3795281 := bstep (se 2 (by rfl) ⟨1423230, by rfl⟩ : syracuseStep 3795281 = 2846461) B2846461
theorem B14258825 : Blo 996598 14258825 := bstep (se 2 (by rfl) ⟨5347059, by rfl⟩ : syracuseStep 14258825 = 10694119) B10694119
theorem B2530187 : Blo 996598 2530187 := bstep (se 1 (by rfl) ⟨1897640, by rfl⟩ : syracuseStep 2530187 = 3795281) B3795281
theorem B2047816039 : Blo 996598 2047816039 := bstep (se 1 (by rfl) ⟨1535862029, by rfl⟩ : syracuseStep 2047816039 = 3071724059) B3071724059
theorem B29603825 : Blo 996598 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B92093375 : Blo 996598 92093375 := bstep (se 1 (by rfl) ⟨69070031, by rfl⟩ : syracuseStep 92093375 = 138140063) B138140063
theorem B7587431 : Blo 996598 7587431 := bstep (se 1 (by rfl) ⟨5690573, by rfl⟩ : syracuseStep 7587431 = 11381147) B11381147
theorem B7785895 : Blo 996598 7785895 := bstep (se 1 (by rfl) ⟨5839421, by rfl⟩ : syracuseStep 7785895 = 11678843) B11678843
theorem B2840903 : Blo 996598 2840903 := bstep (se 1 (by rfl) ⟨2130677, by rfl⟩ : syracuseStep 2840903 = 4261355) B4261355
theorem B9505883 : Blo 996598 9505883 := bstep (se 1 (by rfl) ⟨7129412, by rfl⟩ : syracuseStep 9505883 = 14258825) B14258825
theorem B19735883 : Blo 996598 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B5058287 : Blo 996598 5058287 := bstep (se 1 (by rfl) ⟨3793715, by rfl⟩ : syracuseStep 5058287 = 7587431) B7587431
theorem B1686791 : Blo 996598 1686791 := bstep (se 1 (by rfl) ⟨1265093, by rfl⟩ : syracuseStep 1686791 = 2530187) B2530187
theorem B61395583 : Blo 996598 61395583 := bstep (se 1 (by rfl) ⟨46046687, by rfl⟩ : syracuseStep 61395583 = 92093375) B92093375
theorem B1893935 : Blo 996598 1893935 := bstep (se 1 (by rfl) ⟨1420451, by rfl⟩ : syracuseStep 1893935 = 2840903) B2840903
theorem B10381193 : Blo 996598 10381193 := bstep (se 2 (by rfl) ⟨3892947, by rfl⟩ : syracuseStep 10381193 = 7785895) B7785895
theorem B2730421385 : Blo 996598 2730421385 := bstep (se 2 (by rfl) ⟨1023908019, by rfl⟩ : syracuseStep 2730421385 = 2047816039) B2047816039
theorem B81860777 : Blo 996598 81860777 := bstep (se 2 (by rfl) ⟨30697791, by rfl⟩ : syracuseStep 81860777 = 61395583) B61395583
theorem B6920795 : Blo 996598 6920795 := bstep (se 1 (by rfl) ⟨5190596, by rfl⟩ : syracuseStep 6920795 = 10381193) B10381193
theorem B1124527 : Blo 996598 1124527 := bstep (se 1 (by rfl) ⟨843395, by rfl⟩ : syracuseStep 1124527 = 1686791) B1686791
theorem B13157255 : Blo 996598 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B1262623 : Blo 996598 1262623 := bstep (se 1 (by rfl) ⟨946967, by rfl⟩ : syracuseStep 1262623 = 1893935) B1893935
theorem B1820280923 : Blo 996598 1820280923 := bstep (se 1 (by rfl) ⟨1365210692, by rfl⟩ : syracuseStep 1820280923 = 2730421385) B2730421385
theorem B25349021 : Blo 996598 25349021 := bstep (se 3 (by rfl) ⟨4752941, by rfl⟩ : syracuseStep 25349021 = 9505883) B9505883
theorem B3372191 : Blo 996598 3372191 := bstep (se 1 (by rfl) ⟨2529143, by rfl⟩ : syracuseStep 3372191 = 5058287) B5058287
theorem B1683497 : Blo 996598 1683497 := bstep (se 2 (by rfl) ⟨631311, by rfl⟩ : syracuseStep 1683497 = 1262623) B1262623
theorem B54573851 : Blo 996598 54573851 := bstep (se 1 (by rfl) ⟨40930388, by rfl⟩ : syracuseStep 54573851 = 81860777) B81860777
theorem B2248127 : Blo 996598 2248127 := bstep (se 1 (by rfl) ⟨1686095, by rfl⟩ : syracuseStep 2248127 = 3372191) B3372191
theorem B8771503 : Blo 996598 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B1213520615 : Blo 996598 1213520615 := bstep (se 1 (by rfl) ⟨910140461, by rfl⟩ : syracuseStep 1213520615 = 1820280923) B1820280923
theorem B16899347 : Blo 996598 16899347 := bstep (se 1 (by rfl) ⟨12674510, by rfl⟩ : syracuseStep 16899347 = 25349021) B25349021
theorem B1499369 : Blo 996598 1499369 := bstep (se 2 (by rfl) ⟨562263, by rfl⟩ : syracuseStep 1499369 = 1124527) B1124527
theorem B4613863 : Blo 996598 4613863 := bstep (se 1 (by rfl) ⟨3460397, by rfl⟩ : syracuseStep 4613863 = 6920795) B6920795
theorem B809013743 : Blo 996598 809013743 := bstep (se 1 (by rfl) ⟨606760307, by rfl⟩ : syracuseStep 809013743 = 1213520615) B1213520615
theorem B1122331 : Blo 996598 1122331 := bstep (se 1 (by rfl) ⟨841748, by rfl⟩ : syracuseStep 1122331 = 1683497) B1683497
theorem B36382567 : Blo 996598 36382567 := bstep (se 1 (by rfl) ⟨27286925, by rfl⟩ : syracuseStep 36382567 = 54573851) B54573851
theorem B999579 : Blo 996598 999579 := bstep (se 1 (by rfl) ⟨749684, by rfl⟩ : syracuseStep 999579 = 1499369) B1499369
theorem B1498751 : Blo 996598 1498751 := bstep (se 1 (by rfl) ⟨1124063, by rfl⟩ : syracuseStep 1498751 = 2248127) B2248127
theorem B6151817 : Blo 996598 6151817 := bstep (se 2 (by rfl) ⟨2306931, by rfl⟩ : syracuseStep 6151817 = 4613863) B4613863
theorem B11266231 : Blo 996598 11266231 := bstep (se 1 (by rfl) ⟨8449673, by rfl⟩ : syracuseStep 11266231 = 16899347) B16899347
theorem B11695337 : Blo 996598 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B4101211 : Blo 996598 4101211 := bstep (se 1 (by rfl) ⟨3075908, by rfl⟩ : syracuseStep 4101211 = 6151817) B6151817
theorem B48510089 : Blo 996598 48510089 := bstep (se 2 (by rfl) ⟨18191283, by rfl⟩ : syracuseStep 48510089 = 36382567) B36382567
theorem B15021641 : Blo 996598 15021641 := bstep (se 2 (by rfl) ⟨5633115, by rfl⟩ : syracuseStep 15021641 = 11266231) B11266231
theorem B539342495 : Blo 996598 539342495 := bstep (se 1 (by rfl) ⟨404506871, by rfl⟩ : syracuseStep 539342495 = 809013743) B809013743
theorem B999167 : Blo 996598 999167 := bstep (se 1 (by rfl) ⟨749375, by rfl⟩ : syracuseStep 999167 = 1498751) B1498751
theorem B1496441 : Blo 996598 1496441 := bstep (se 2 (by rfl) ⟨561165, by rfl⟩ : syracuseStep 1496441 = 1122331) B1122331
theorem B7796891 : Blo 996598 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B997627 : Blo 996598 997627 := bstep (se 1 (by rfl) ⟨748220, by rfl⟩ : syracuseStep 997627 = 1496441) B1496441
theorem B21873125 : Blo 996598 21873125 := bstep (se 4 (by rfl) ⟨2050605, by rfl⟩ : syracuseStep 21873125 = 4101211) B4101211
theorem B10014427 : Blo 996598 10014427 := bstep (se 1 (by rfl) ⟨7510820, by rfl⟩ : syracuseStep 10014427 = 15021641) B15021641
theorem B5197927 : Blo 996598 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B32340059 : Blo 996598 32340059 := bstep (se 1 (by rfl) ⟨24255044, by rfl⟩ : syracuseStep 32340059 = 48510089) B48510089
theorem B359561663 : Blo 996598 359561663 := bstep (se 1 (by rfl) ⟨269671247, by rfl⟩ : syracuseStep 359561663 = 539342495) B539342495
theorem B58328333 : Blo 996598 58328333 := bstep (se 3 (by rfl) ⟨10936562, by rfl⟩ : syracuseStep 58328333 = 21873125) B21873125
theorem B239707775 : Blo 996598 239707775 := bstep (se 1 (by rfl) ⟨179780831, by rfl⟩ : syracuseStep 239707775 = 359561663) B359561663
theorem B13352569 : Blo 996598 13352569 := bstep (se 2 (by rfl) ⟨5007213, by rfl⟩ : syracuseStep 13352569 = 10014427) B10014427
theorem B6930569 : Blo 996598 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B21560039 : Blo 996598 21560039 := bstep (se 1 (by rfl) ⟨16170029, by rfl⟩ : syracuseStep 21560039 = 32340059) B32340059
theorem B18481517 : Blo 996598 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B284854805 : Blo 996598 284854805 := bstep (se 6 (by rfl) ⟨6676284, by rfl⟩ : syracuseStep 284854805 = 13352569) B13352569
theorem B639220733 : Blo 996598 639220733 := bstep (se 3 (by rfl) ⟨119853887, by rfl⟩ : syracuseStep 639220733 = 239707775) B239707775
theorem B14373359 : Blo 996598 14373359 := bstep (se 1 (by rfl) ⟨10780019, by rfl⟩ : syracuseStep 14373359 = 21560039) B21560039
theorem B38885555 : Blo 996598 38885555 := bstep (se 1 (by rfl) ⟨29164166, by rfl⟩ : syracuseStep 38885555 = 58328333) B58328333
theorem B12321011 : Blo 996598 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B189903203 : Blo 996598 189903203 := bstep (se 1 (by rfl) ⟨142427402, by rfl⟩ : syracuseStep 189903203 = 284854805) B284854805
theorem B9582239 : Blo 996598 9582239 := bstep (se 1 (by rfl) ⟨7186679, by rfl⟩ : syracuseStep 9582239 = 14373359) B14373359
theorem B103694813 : Blo 996598 103694813 := bstep (se 3 (by rfl) ⟨19442777, by rfl⟩ : syracuseStep 103694813 = 38885555) B38885555
theorem B426147155 : Blo 996598 426147155 := bstep (se 1 (by rfl) ⟨319610366, by rfl⟩ : syracuseStep 426147155 = 639220733) B639220733
theorem B126602135 : Blo 996598 126602135 := bstep (se 1 (by rfl) ⟨94951601, by rfl⟩ : syracuseStep 126602135 = 189903203) B189903203
theorem B8214007 : Blo 996598 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B69129875 : Blo 996598 69129875 := bstep (se 1 (by rfl) ⟨51847406, by rfl⟩ : syracuseStep 69129875 = 103694813) B103694813
theorem B6388159 : Blo 996598 6388159 := bstep (se 1 (by rfl) ⟨4791119, by rfl⟩ : syracuseStep 6388159 = 9582239) B9582239
theorem B284098103 : Blo 996598 284098103 := bstep (se 1 (by rfl) ⟨213073577, by rfl⟩ : syracuseStep 284098103 = 426147155) B426147155
theorem B10952009 : Blo 996598 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B46086583 : Blo 996598 46086583 := bstep (se 1 (by rfl) ⟨34564937, by rfl⟩ : syracuseStep 46086583 = 69129875) B69129875
theorem B84401423 : Blo 996598 84401423 := bstep (se 1 (by rfl) ⟨63301067, by rfl⟩ : syracuseStep 84401423 = 126602135) B126602135
theorem B8517545 : Blo 996598 8517545 := bstep (se 2 (by rfl) ⟨3194079, by rfl⟩ : syracuseStep 8517545 = 6388159) B6388159
theorem B189398735 : Blo 996598 189398735 := bstep (se 1 (by rfl) ⟨142049051, by rfl⟩ : syracuseStep 189398735 = 284098103) B284098103
theorem B56267615 : Blo 996598 56267615 := bstep (se 1 (by rfl) ⟨42200711, by rfl⟩ : syracuseStep 56267615 = 84401423) B84401423
theorem B61448777 : Blo 996598 61448777 := bstep (se 2 (by rfl) ⟨23043291, by rfl⟩ : syracuseStep 61448777 = 46086583) B46086583
theorem B5678363 : Blo 996598 5678363 := bstep (se 1 (by rfl) ⟨4258772, by rfl⟩ : syracuseStep 5678363 = 8517545) B8517545
theorem B126265823 : Blo 996598 126265823 := bstep (se 1 (by rfl) ⟨94699367, by rfl⟩ : syracuseStep 126265823 = 189398735) B189398735
theorem B7301339 : Blo 996598 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B40965851 : Blo 996598 40965851 := bstep (se 1 (by rfl) ⟨30724388, by rfl⟩ : syracuseStep 40965851 = 61448777) B61448777
theorem B3785575 : Blo 996598 3785575 := bstep (se 1 (by rfl) ⟨2839181, by rfl⟩ : syracuseStep 3785575 = 5678363) B5678363
theorem B4867559 : Blo 996598 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B37511743 : Blo 996598 37511743 := bstep (se 1 (by rfl) ⟨28133807, by rfl⟩ : syracuseStep 37511743 = 56267615) B56267615
theorem B84177215 : Blo 996598 84177215 := bstep (se 1 (by rfl) ⟨63132911, by rfl⟩ : syracuseStep 84177215 = 126265823) B126265823
theorem B3245039 : Blo 996598 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B5047433 : Blo 996598 5047433 := bstep (se 2 (by rfl) ⟨1892787, by rfl⟩ : syracuseStep 5047433 = 3785575) B3785575
theorem B50015657 : Blo 996598 50015657 := bstep (se 2 (by rfl) ⟨18755871, by rfl⟩ : syracuseStep 50015657 = 37511743) B37511743
theorem B56118143 : Blo 996598 56118143 := bstep (se 1 (by rfl) ⟨42088607, by rfl⟩ : syracuseStep 56118143 = 84177215) B84177215
theorem B109242269 : Blo 996598 109242269 := bstep (se 3 (by rfl) ⟨20482925, by rfl⟩ : syracuseStep 109242269 = 40965851) B40965851
theorem B2163359 : Blo 996598 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B133375085 : Blo 996598 133375085 := bstep (se 3 (by rfl) ⟨25007828, by rfl⟩ : syracuseStep 133375085 = 50015657) B50015657
theorem B72828179 : Blo 996598 72828179 := bstep (se 1 (by rfl) ⟨54621134, by rfl⟩ : syracuseStep 72828179 = 109242269) B109242269
theorem B3364955 : Blo 996598 3364955 := bstep (se 1 (by rfl) ⟨2523716, by rfl⟩ : syracuseStep 3364955 = 5047433) B5047433
theorem B149648381 : Blo 996598 149648381 := bstep (se 3 (by rfl) ⟨28059071, by rfl⟩ : syracuseStep 149648381 = 56118143) B56118143
theorem B5768957 : Blo 996598 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B2243303 : Blo 996598 2243303 := bstep (se 1 (by rfl) ⟨1682477, by rfl⟩ : syracuseStep 2243303 = 3364955) B3364955
theorem B88916723 : Blo 996598 88916723 := bstep (se 1 (by rfl) ⟨66687542, by rfl⟩ : syracuseStep 88916723 = 133375085) B133375085
theorem B99765587 : Blo 996598 99765587 := bstep (se 1 (by rfl) ⟨74824190, by rfl⟩ : syracuseStep 99765587 = 149648381) B149648381
theorem B48552119 : Blo 996598 48552119 := bstep (se 1 (by rfl) ⟨36414089, by rfl⟩ : syracuseStep 48552119 = 72828179) B72828179
theorem B59277815 : Blo 996598 59277815 := bstep (se 1 (by rfl) ⟨44458361, by rfl⟩ : syracuseStep 59277815 = 88916723) B88916723
theorem B3845971 : Blo 996598 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B1495535 : Blo 996598 1495535 := bstep (se 1 (by rfl) ⟨1121651, by rfl⟩ : syracuseStep 1495535 = 2243303) B2243303
theorem B66510391 : Blo 996598 66510391 := bstep (se 1 (by rfl) ⟨49882793, by rfl⟩ : syracuseStep 66510391 = 99765587) B99765587
theorem B32368079 : Blo 996598 32368079 := bstep (se 1 (by rfl) ⟨24276059, by rfl⟩ : syracuseStep 32368079 = 48552119) B48552119
theorem B39518543 : Blo 996598 39518543 := bstep (se 1 (by rfl) ⟨29638907, by rfl⟩ : syracuseStep 39518543 = 59277815) B59277815
theorem B88680521 : Blo 996598 88680521 := bstep (se 2 (by rfl) ⟨33255195, by rfl⟩ : syracuseStep 88680521 = 66510391) B66510391
theorem B997023 : Blo 996598 997023 := bstep (se 1 (by rfl) ⟨747767, by rfl⟩ : syracuseStep 997023 = 1495535) B1495535
theorem B5127961 : Blo 996598 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B21578719 : Blo 996598 21578719 := bstep (se 1 (by rfl) ⟨16184039, by rfl⟩ : syracuseStep 21578719 = 32368079) B32368079
theorem B26345695 : Blo 996598 26345695 := bstep (se 1 (by rfl) ⟨19759271, by rfl⟩ : syracuseStep 26345695 = 39518543) B39518543
theorem B28771625 : Blo 996598 28771625 := bstep (se 2 (by rfl) ⟨10789359, by rfl⟩ : syracuseStep 28771625 = 21578719) B21578719
theorem B6837281 : Blo 996598 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B236481389 : Blo 996598 236481389 := bstep (se 3 (by rfl) ⟨44340260, by rfl⟩ : syracuseStep 236481389 = 88680521) B88680521
theorem B35127593 : Blo 996598 35127593 := bstep (se 2 (by rfl) ⟨13172847, by rfl⟩ : syracuseStep 35127593 = 26345695) B26345695
theorem B4558187 : Blo 996598 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B157654259 : Blo 996598 157654259 := bstep (se 1 (by rfl) ⟨118240694, by rfl⟩ : syracuseStep 157654259 = 236481389) B236481389
theorem B19181083 : Blo 996598 19181083 := bstep (se 1 (by rfl) ⟨14385812, by rfl⟩ : syracuseStep 19181083 = 28771625) B28771625
theorem B25574777 : Blo 996598 25574777 := bstep (se 2 (by rfl) ⟨9590541, by rfl⟩ : syracuseStep 25574777 = 19181083) B19181083
theorem B105102839 : Blo 996598 105102839 := bstep (se 1 (by rfl) ⟨78827129, by rfl⟩ : syracuseStep 105102839 = 157654259) B157654259
theorem B23418395 : Blo 996598 23418395 := bstep (se 1 (by rfl) ⟨17563796, by rfl⟩ : syracuseStep 23418395 = 35127593) B35127593
theorem B3038791 : Blo 996598 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B17049851 : Blo 996598 17049851 := bstep (se 1 (by rfl) ⟨12787388, by rfl⟩ : syracuseStep 17049851 = 25574777) B25574777
theorem B70068559 : Blo 996598 70068559 := bstep (se 1 (by rfl) ⟨52551419, by rfl⟩ : syracuseStep 70068559 = 105102839) B105102839
theorem B15612263 : Blo 996598 15612263 := bstep (se 1 (by rfl) ⟨11709197, by rfl⟩ : syracuseStep 15612263 = 23418395) B23418395
theorem B4051721 : Blo 996598 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B93424745 : Blo 996598 93424745 := bstep (se 2 (by rfl) ⟨35034279, by rfl⟩ : syracuseStep 93424745 = 70068559) B70068559
theorem B2701147 : Blo 996598 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B10408175 : Blo 996598 10408175 := bstep (se 1 (by rfl) ⟨7806131, by rfl⟩ : syracuseStep 10408175 = 15612263) B15612263
theorem B11366567 : Blo 996598 11366567 := bstep (se 1 (by rfl) ⟨8524925, by rfl⟩ : syracuseStep 11366567 = 17049851) B17049851
theorem B7577711 : Blo 996598 7577711 := bstep (se 1 (by rfl) ⟨5683283, by rfl⟩ : syracuseStep 7577711 = 11366567) B11366567
theorem B62283163 : Blo 996598 62283163 := bstep (se 1 (by rfl) ⟨46712372, by rfl⟩ : syracuseStep 62283163 = 93424745) B93424745
theorem B6938783 : Blo 996598 6938783 := bstep (se 1 (by rfl) ⟨5204087, by rfl⟩ : syracuseStep 6938783 = 10408175) B10408175
theorem B3601529 : Blo 996598 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B5051807 : Blo 996598 5051807 := bstep (se 1 (by rfl) ⟨3788855, by rfl⟩ : syracuseStep 5051807 = 7577711) B7577711
theorem B4625855 : Blo 996598 4625855 := bstep (se 1 (by rfl) ⟨3469391, by rfl⟩ : syracuseStep 4625855 = 6938783) B6938783
theorem B2401019 : Blo 996598 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B83044217 : Blo 996598 83044217 := bstep (se 2 (by rfl) ⟨31141581, by rfl⟩ : syracuseStep 83044217 = 62283163) B62283163
theorem B3083903 : Blo 996598 3083903 := bstep (se 1 (by rfl) ⟨2312927, by rfl⟩ : syracuseStep 3083903 = 4625855) B4625855
theorem B55362811 : Blo 996598 55362811 := bstep (se 1 (by rfl) ⟨41522108, by rfl⟩ : syracuseStep 55362811 = 83044217) B83044217
theorem B3367871 : Blo 996598 3367871 := bstep (se 1 (by rfl) ⟨2525903, by rfl⟩ : syracuseStep 3367871 = 5051807) B5051807
theorem B1600679 : Blo 996598 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B4268477 : Blo 996598 4268477 := bstep (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) B1600679
theorem B2245247 : Blo 996598 2245247 := bstep (se 1 (by rfl) ⟨1683935, by rfl⟩ : syracuseStep 2245247 = 3367871) B3367871
theorem B73817081 : Blo 996598 73817081 := bstep (se 2 (by rfl) ⟨27681405, by rfl⟩ : syracuseStep 73817081 = 55362811) B55362811
theorem B2055935 : Blo 996598 2055935 := bstep (se 1 (by rfl) ⟨1541951, by rfl⟩ : syracuseStep 2055935 = 3083903) B3083903
theorem B11382605 : Blo 996598 11382605 := bstep (se 3 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 11382605 = 4268477) B4268477
theorem B1496831 : Blo 996598 1496831 := bstep (se 1 (by rfl) ⟨1122623, by rfl⟩ : syracuseStep 1496831 = 2245247) B2245247
theorem B49211387 : Blo 996598 49211387 := bstep (se 1 (by rfl) ⟨36908540, by rfl⟩ : syracuseStep 49211387 = 73817081) B73817081
theorem B1370623 : Blo 996598 1370623 := bstep (se 1 (by rfl) ⟨1027967, by rfl⟩ : syracuseStep 1370623 = 2055935) B2055935
theorem B32807591 : Blo 996598 32807591 := bstep (se 1 (by rfl) ⟨24605693, by rfl⟩ : syracuseStep 32807591 = 49211387) B49211387
theorem B997887 : Blo 996598 997887 := bstep (se 1 (by rfl) ⟨748415, by rfl⟩ : syracuseStep 997887 = 1496831) B1496831
theorem B7588403 : Blo 996598 7588403 := bstep (se 1 (by rfl) ⟨5691302, by rfl⟩ : syracuseStep 7588403 = 11382605) B11382605
theorem B1827497 : Blo 996598 1827497 := bstep (se 2 (by rfl) ⟨685311, by rfl⟩ : syracuseStep 1827497 = 1370623) B1370623
theorem B1218331 : Blo 996598 1218331 := bstep (se 1 (by rfl) ⟨913748, by rfl⟩ : syracuseStep 1218331 = 1827497) B1827497
theorem B5058935 : Blo 996598 5058935 := bstep (se 1 (by rfl) ⟨3794201, by rfl⟩ : syracuseStep 5058935 = 7588403) B7588403
theorem B21871727 : Blo 996598 21871727 := bstep (se 1 (by rfl) ⟨16403795, by rfl⟩ : syracuseStep 21871727 = 32807591) B32807591
theorem B6497765 : Blo 996598 6497765 := bstep (se 4 (by rfl) ⟨609165, by rfl⟩ : syracuseStep 6497765 = 1218331) B1218331
theorem B3372623 : Blo 996598 3372623 := bstep (se 1 (by rfl) ⟨2529467, by rfl⟩ : syracuseStep 3372623 = 5058935) B5058935
theorem B14581151 : Blo 996598 14581151 := bstep (se 1 (by rfl) ⟨10935863, by rfl⟩ : syracuseStep 14581151 = 21871727) B21871727
theorem B4331843 : Blo 996598 4331843 := bstep (se 1 (by rfl) ⟨3248882, by rfl⟩ : syracuseStep 4331843 = 6497765) B6497765
theorem B2248415 : Blo 996598 2248415 := bstep (se 1 (by rfl) ⟨1686311, by rfl⟩ : syracuseStep 2248415 = 3372623) B3372623
theorem B9720767 : Blo 996598 9720767 := bstep (se 1 (by rfl) ⟨7290575, by rfl⟩ : syracuseStep 9720767 = 14581151) B14581151
theorem B25922045 : Blo 996598 25922045 := bstep (se 3 (by rfl) ⟨4860383, by rfl⟩ : syracuseStep 25922045 = 9720767) B9720767
theorem B2887895 : Blo 996598 2887895 := bstep (se 1 (by rfl) ⟨2165921, by rfl⟩ : syracuseStep 2887895 = 4331843) B4331843
theorem B1498943 : Blo 996598 1498943 := bstep (se 1 (by rfl) ⟨1124207, by rfl⟩ : syracuseStep 1498943 = 2248415) B2248415
theorem B17281363 : Blo 996598 17281363 := bstep (se 1 (by rfl) ⟨12961022, by rfl⟩ : syracuseStep 17281363 = 25922045) B25922045
theorem B999295 : Blo 996598 999295 := bstep (se 1 (by rfl) ⟨749471, by rfl⟩ : syracuseStep 999295 = 1498943) B1498943
theorem B1925263 : Blo 996598 1925263 := bstep (se 1 (by rfl) ⟨1443947, by rfl⟩ : syracuseStep 1925263 = 2887895) B2887895
theorem B23041817 : Blo 996598 23041817 := bstep (se 2 (by rfl) ⟨8640681, by rfl⟩ : syracuseStep 23041817 = 17281363) B17281363
theorem B2567017 : Blo 996598 2567017 := bstep (se 2 (by rfl) ⟨962631, by rfl⟩ : syracuseStep 2567017 = 1925263) B1925263
theorem B15361211 : Blo 996598 15361211 := bstep (se 1 (by rfl) ⟨11520908, by rfl⟩ : syracuseStep 15361211 = 23041817) B23041817
theorem B13690757 : Blo 996598 13690757 := bstep (se 4 (by rfl) ⟨1283508, by rfl⟩ : syracuseStep 13690757 = 2567017) B2567017
theorem B40963229 : Blo 996598 40963229 := bstep (se 3 (by rfl) ⟨7680605, by rfl⟩ : syracuseStep 40963229 = 15361211) B15361211
theorem B9127171 : Blo 996598 9127171 := bstep (se 1 (by rfl) ⟨6845378, by rfl⟩ : syracuseStep 9127171 = 13690757) B13690757
theorem B27308819 : Blo 996598 27308819 := bstep (se 1 (by rfl) ⟨20481614, by rfl⟩ : syracuseStep 27308819 = 40963229) B40963229
theorem B48678245 : Blo 996598 48678245 := bstep (se 4 (by rfl) ⟨4563585, by rfl⟩ : syracuseStep 48678245 = 9127171) B9127171
theorem B32452163 : Blo 996598 32452163 := bstep (se 1 (by rfl) ⟨24339122, by rfl⟩ : syracuseStep 32452163 = 48678245) B48678245
theorem B18205879 : Blo 996598 18205879 := bstep (se 1 (by rfl) ⟨13654409, by rfl⟩ : syracuseStep 18205879 = 27308819) B27308819
theorem B21634775 : Blo 996598 21634775 := bstep (se 1 (by rfl) ⟨16226081, by rfl⟩ : syracuseStep 21634775 = 32452163) B32452163
theorem B24274505 : Blo 996598 24274505 := bstep (se 2 (by rfl) ⟨9102939, by rfl⟩ : syracuseStep 24274505 = 18205879) B18205879
theorem B14423183 : Blo 996598 14423183 := bstep (se 1 (by rfl) ⟨10817387, by rfl⟩ : syracuseStep 14423183 = 21634775) B21634775
theorem B16183003 : Blo 996598 16183003 := bstep (se 1 (by rfl) ⟨12137252, by rfl⟩ : syracuseStep 16183003 = 24274505) B24274505
theorem B9615455 : Blo 996598 9615455 := bstep (se 1 (by rfl) ⟨7211591, by rfl⟩ : syracuseStep 9615455 = 14423183) B14423183
theorem B21577337 : Blo 996598 21577337 := bstep (se 2 (by rfl) ⟨8091501, by rfl⟩ : syracuseStep 21577337 = 16183003) B16183003
theorem B6410303 : Blo 996598 6410303 := bstep (se 1 (by rfl) ⟨4807727, by rfl⟩ : syracuseStep 6410303 = 9615455) B9615455
theorem B14384891 : Blo 996598 14384891 := bstep (se 1 (by rfl) ⟨10788668, by rfl⟩ : syracuseStep 14384891 = 21577337) B21577337
theorem B4273535 : Blo 996598 4273535 := bstep (se 1 (by rfl) ⟨3205151, by rfl⟩ : syracuseStep 4273535 = 6410303) B6410303
theorem B9589927 : Blo 996598 9589927 := bstep (se 1 (by rfl) ⟨7192445, by rfl⟩ : syracuseStep 9589927 = 14384891) B14384891
theorem B12786569 : Blo 996598 12786569 := bstep (se 2 (by rfl) ⟨4794963, by rfl⟩ : syracuseStep 12786569 = 9589927) B9589927
theorem B2849023 : Blo 996598 2849023 := bstep (se 1 (by rfl) ⟨2136767, by rfl⟩ : syracuseStep 2849023 = 4273535) B4273535
theorem B8524379 : Blo 996598 8524379 := bstep (se 1 (by rfl) ⟨6393284, by rfl⟩ : syracuseStep 8524379 = 12786569) B12786569
theorem B3798697 : Blo 996598 3798697 := bstep (se 2 (by rfl) ⟨1424511, by rfl⟩ : syracuseStep 3798697 = 2849023) B2849023
theorem B5682919 : Blo 996598 5682919 := bstep (se 1 (by rfl) ⟨4262189, by rfl⟩ : syracuseStep 5682919 = 8524379) B8524379
theorem B5064929 : Blo 996598 5064929 := bstep (se 2 (by rfl) ⟨1899348, by rfl⟩ : syracuseStep 5064929 = 3798697) B3798697
theorem B3376619 : Blo 996598 3376619 := bstep (se 1 (by rfl) ⟨2532464, by rfl⟩ : syracuseStep 3376619 = 5064929) B5064929
theorem B7577225 : Blo 996598 7577225 := bstep (se 2 (by rfl) ⟨2841459, by rfl⟩ : syracuseStep 7577225 = 5682919) B5682919
theorem B5051483 : Blo 996598 5051483 := bstep (se 1 (by rfl) ⟨3788612, by rfl⟩ : syracuseStep 5051483 = 7577225) B7577225
theorem B2251079 : Blo 996598 2251079 := bstep (se 1 (by rfl) ⟨1688309, by rfl⟩ : syracuseStep 2251079 = 3376619) B3376619
theorem B3367655 : Blo 996598 3367655 := bstep (se 1 (by rfl) ⟨2525741, by rfl⟩ : syracuseStep 3367655 = 5051483) B5051483
theorem B1500719 : Blo 996598 1500719 := bstep (se 1 (by rfl) ⟨1125539, by rfl⟩ : syracuseStep 1500719 = 2251079) B2251079
theorem B2245103 : Blo 996598 2245103 := bstep (se 1 (by rfl) ⟨1683827, by rfl⟩ : syracuseStep 2245103 = 3367655) B3367655
theorem B1000479 : Blo 996598 1000479 := bstep (se 1 (by rfl) ⟨750359, by rfl⟩ : syracuseStep 1000479 = 1500719) B1500719
theorem B1496735 : Blo 996598 1496735 := bstep (se 1 (by rfl) ⟨1122551, by rfl⟩ : syracuseStep 1496735 = 2245103) B2245103
theorem B997823 : Blo 996598 997823 := bstep (se 1 (by rfl) ⟨748367, by rfl⟩ : syracuseStep 997823 = 1496735) B1496735

theorem C0 (j : ℕ) (h1 : 249149 ≤ j) (h2 : j ≤ 249848) : Blo 996598 (4 * j + 3) := by
  interval_cases j
  · exact B996599
  · exact B996603
  · exact B996607
  · exact B996611
  · exact B996615
  · exact B996619
  · exact B996623
  · exact B996627
  · exact B996631
  · exact B996635
  · exact B996639
  · exact B996643
  · exact B996647
  · exact B996651
  · exact B996655
  · exact B996659
  · exact B996663
  · exact B996667
  · exact B996671
  · exact B996675
  · exact B996679
  · exact B996683
  · exact B996687
  · exact B996691
  · exact B996695
  · exact B996699
  · exact B996703
  · exact B996707
  · exact B996711
  · exact B996715
  · exact B996719
  · exact B996723
  · exact B996727
  · exact B996731
  · exact B996735
  · exact B996739
  · exact B996743
  · exact B996747
  · exact B996751
  · exact B996755
  · exact B996759
  · exact B996763
  · exact B996767
  · exact B996771
  · exact B996775
  · exact B996779
  · exact B996783
  · exact B996787
  · exact B996791
  · exact B996795
  · exact B996799
  · exact B996803
  · exact B996807
  · exact B996811
  · exact B996815
  · exact B996819
  · exact B996823
  · exact B996827
  · exact B996831
  · exact B996835
  · exact B996839
  · exact B996843
  · exact B996847
  · exact B996851
  · exact B996855
  · exact B996859
  · exact B996863
  · exact B996867
  · exact B996871
  · exact B996875
  · exact B996879
  · exact B996883
  · exact B996887
  · exact B996891
  · exact B996895
  · exact B996899
  · exact B996903
  · exact B996907
  · exact B996911
  · exact B996915
  · exact B996919
  · exact B996923
  · exact B996927
  · exact B996931
  · exact B996935
  · exact B996939
  · exact B996943
  · exact B996947
  · exact B996951
  · exact B996955
  · exact B996959
  · exact B996963
  · exact B996967
  · exact B996971
  · exact B996975
  · exact B996979
  · exact B996983
  · exact B996987
  · exact B996991
  · exact B996995
  · exact B996999
  · exact B997003
  · exact B997007
  · exact B997011
  · exact B997015
  · exact B997019
  · exact B997023
  · exact B997027
  · exact B997031
  · exact B997035
  · exact B997039
  · exact B997043
  · exact B997047
  · exact B997051
  · exact B997055
  · exact B997059
  · exact B997063
  · exact B997067
  · exact B997071
  · exact B997075
  · exact B997079
  · exact B997083
  · exact B997087
  · exact B997091
  · exact B997095
  · exact B997099
  · exact B997103
  · exact B997107
  · exact B997111
  · exact B997115
  · exact B997119
  · exact B997123
  · exact B997127
  · exact B997131
  · exact B997135
  · exact B997139
  · exact B997143
  · exact B997147
  · exact B997151
  · exact B997155
  · exact B997159
  · exact B997163
  · exact B997167
  · exact B997171
  · exact B997175
  · exact B997179
  · exact B997183
  · exact B997187
  · exact B997191
  · exact B997195
  · exact B997199
  · exact B997203
  · exact B997207
  · exact B997211
  · exact B997215
  · exact B997219
  · exact B997223
  · exact B997227
  · exact B997231
  · exact B997235
  · exact B997239
  · exact B997243
  · exact B997247
  · exact B997251
  · exact B997255
  · exact B997259
  · exact B997263
  · exact B997267
  · exact B997271
  · exact B997275
  · exact B997279
  · exact B997283
  · exact B997287
  · exact B997291
  · exact B997295
  · exact B997299
  · exact B997303
  · exact B997307
  · exact B997311
  · exact B997315
  · exact B997319
  · exact B997323
  · exact B997327
  · exact B997331
  · exact B997335
  · exact B997339
  · exact B997343
  · exact B997347
  · exact B997351
  · exact B997355
  · exact B997359
  · exact B997363
  · exact B997367
  · exact B997371
  · exact B997375
  · exact B997379
  · exact B997383
  · exact B997387
  · exact B997391
  · exact B997395
  · exact B997399
  · exact B997403
  · exact B997407
  · exact B997411
  · exact B997415
  · exact B997419
  · exact B997423
  · exact B997427
  · exact B997431
  · exact B997435
  · exact B997439
  · exact B997443
  · exact B997447
  · exact B997451
  · exact B997455
  · exact B997459
  · exact B997463
  · exact B997467
  · exact B997471
  · exact B997475
  · exact B997479
  · exact B997483
  · exact B997487
  · exact B997491
  · exact B997495
  · exact B997499
  · exact B997503
  · exact B997507
  · exact B997511
  · exact B997515
  · exact B997519
  · exact B997523
  · exact B997527
  · exact B997531
  · exact B997535
  · exact B997539
  · exact B997543
  · exact B997547
  · exact B997551
  · exact B997555
  · exact B997559
  · exact B997563
  · exact B997567
  · exact B997571
  · exact B997575
  · exact B997579
  · exact B997583
  · exact B997587
  · exact B997591
  · exact B997595
  · exact B997599
  · exact B997603
  · exact B997607
  · exact B997611
  · exact B997615
  · exact B997619
  · exact B997623
  · exact B997627
  · exact B997631
  · exact B997635
  · exact B997639
  · exact B997643
  · exact B997647
  · exact B997651
  · exact B997655
  · exact B997659
  · exact B997663
  · exact B997667
  · exact B997671
  · exact B997675
  · exact B997679
  · exact B997683
  · exact B997687
  · exact B997691
  · exact B997695
  · exact B997699
  · exact B997703
  · exact B997707
  · exact B997711
  · exact B997715
  · exact B997719
  · exact B997723
  · exact B997727
  · exact B997731
  · exact B997735
  · exact B997739
  · exact B997743
  · exact B997747
  · exact B997751
  · exact B997755
  · exact B997759
  · exact B997763
  · exact B997767
  · exact B997771
  · exact B997775
  · exact B997779
  · exact B997783
  · exact B997787
  · exact B997791
  · exact B997795
  · exact B997799
  · exact B997803
  · exact B997807
  · exact B997811
  · exact B997815
  · exact B997819
  · exact B997823
  · exact B997827
  · exact B997831
  · exact B997835
  · exact B997839
  · exact B997843
  · exact B997847
  · exact B997851
  · exact B997855
  · exact B997859
  · exact B997863
  · exact B997867
  · exact B997871
  · exact B997875
  · exact B997879
  · exact B997883
  · exact B997887
  · exact B997891
  · exact B997895
  · exact B997899
  · exact B997903
  · exact B997907
  · exact B997911
  · exact B997915
  · exact B997919
  · exact B997923
  · exact B997927
  · exact B997931
  · exact B997935
  · exact B997939
  · exact B997943
  · exact B997947
  · exact B997951
  · exact B997955
  · exact B997959
  · exact B997963
  · exact B997967
  · exact B997971
  · exact B997975
  · exact B997979
  · exact B997983
  · exact B997987
  · exact B997991
  · exact B997995
  · exact B997999
  · exact B998003
  · exact B998007
  · exact B998011
  · exact B998015
  · exact B998019
  · exact B998023
  · exact B998027
  · exact B998031
  · exact B998035
  · exact B998039
  · exact B998043
  · exact B998047
  · exact B998051
  · exact B998055
  · exact B998059
  · exact B998063
  · exact B998067
  · exact B998071
  · exact B998075
  · exact B998079
  · exact B998083
  · exact B998087
  · exact B998091
  · exact B998095
  · exact B998099
  · exact B998103
  · exact B998107
  · exact B998111
  · exact B998115
  · exact B998119
  · exact B998123
  · exact B998127
  · exact B998131
  · exact B998135
  · exact B998139
  · exact B998143
  · exact B998147
  · exact B998151
  · exact B998155
  · exact B998159
  · exact B998163
  · exact B998167
  · exact B998171
  · exact B998175
  · exact B998179
  · exact B998183
  · exact B998187
  · exact B998191
  · exact B998195
  · exact B998199
  · exact B998203
  · exact B998207
  · exact B998211
  · exact B998215
  · exact B998219
  · exact B998223
  · exact B998227
  · exact B998231
  · exact B998235
  · exact B998239
  · exact B998243
  · exact B998247
  · exact B998251
  · exact B998255
  · exact B998259
  · exact B998263
  · exact B998267
  · exact B998271
  · exact B998275
  · exact B998279
  · exact B998283
  · exact B998287
  · exact B998291
  · exact B998295
  · exact B998299
  · exact B998303
  · exact B998307
  · exact B998311
  · exact B998315
  · exact B998319
  · exact B998323
  · exact B998327
  · exact B998331
  · exact B998335
  · exact B998339
  · exact B998343
  · exact B998347
  · exact B998351
  · exact B998355
  · exact B998359
  · exact B998363
  · exact B998367
  · exact B998371
  · exact B998375
  · exact B998379
  · exact B998383
  · exact B998387
  · exact B998391
  · exact B998395
  · exact B998399
  · exact B998403
  · exact B998407
  · exact B998411
  · exact B998415
  · exact B998419
  · exact B998423
  · exact B998427
  · exact B998431
  · exact B998435
  · exact B998439
  · exact B998443
  · exact B998447
  · exact B998451
  · exact B998455
  · exact B998459
  · exact B998463
  · exact B998467
  · exact B998471
  · exact B998475
  · exact B998479
  · exact B998483
  · exact B998487
  · exact B998491
  · exact B998495
  · exact B998499
  · exact B998503
  · exact B998507
  · exact B998511
  · exact B998515
  · exact B998519
  · exact B998523
  · exact B998527
  · exact B998531
  · exact B998535
  · exact B998539
  · exact B998543
  · exact B998547
  · exact B998551
  · exact B998555
  · exact B998559
  · exact B998563
  · exact B998567
  · exact B998571
  · exact B998575
  · exact B998579
  · exact B998583
  · exact B998587
  · exact B998591
  · exact B998595
  · exact B998599
  · exact B998603
  · exact B998607
  · exact B998611
  · exact B998615
  · exact B998619
  · exact B998623
  · exact B998627
  · exact B998631
  · exact B998635
  · exact B998639
  · exact B998643
  · exact B998647
  · exact B998651
  · exact B998655
  · exact B998659
  · exact B998663
  · exact B998667
  · exact B998671
  · exact B998675
  · exact B998679
  · exact B998683
  · exact B998687
  · exact B998691
  · exact B998695
  · exact B998699
  · exact B998703
  · exact B998707
  · exact B998711
  · exact B998715
  · exact B998719
  · exact B998723
  · exact B998727
  · exact B998731
  · exact B998735
  · exact B998739
  · exact B998743
  · exact B998747
  · exact B998751
  · exact B998755
  · exact B998759
  · exact B998763
  · exact B998767
  · exact B998771
  · exact B998775
  · exact B998779
  · exact B998783
  · exact B998787
  · exact B998791
  · exact B998795
  · exact B998799
  · exact B998803
  · exact B998807
  · exact B998811
  · exact B998815
  · exact B998819
  · exact B998823
  · exact B998827
  · exact B998831
  · exact B998835
  · exact B998839
  · exact B998843
  · exact B998847
  · exact B998851
  · exact B998855
  · exact B998859
  · exact B998863
  · exact B998867
  · exact B998871
  · exact B998875
  · exact B998879
  · exact B998883
  · exact B998887
  · exact B998891
  · exact B998895
  · exact B998899
  · exact B998903
  · exact B998907
  · exact B998911
  · exact B998915
  · exact B998919
  · exact B998923
  · exact B998927
  · exact B998931
  · exact B998935
  · exact B998939
  · exact B998943
  · exact B998947
  · exact B998951
  · exact B998955
  · exact B998959
  · exact B998963
  · exact B998967
  · exact B998971
  · exact B998975
  · exact B998979
  · exact B998983
  · exact B998987
  · exact B998991
  · exact B998995
  · exact B998999
  · exact B999003
  · exact B999007
  · exact B999011
  · exact B999015
  · exact B999019
  · exact B999023
  · exact B999027
  · exact B999031
  · exact B999035
  · exact B999039
  · exact B999043
  · exact B999047
  · exact B999051
  · exact B999055
  · exact B999059
  · exact B999063
  · exact B999067
  · exact B999071
  · exact B999075
  · exact B999079
  · exact B999083
  · exact B999087
  · exact B999091
  · exact B999095
  · exact B999099
  · exact B999103
  · exact B999107
  · exact B999111
  · exact B999115
  · exact B999119
  · exact B999123
  · exact B999127
  · exact B999131
  · exact B999135
  · exact B999139
  · exact B999143
  · exact B999147
  · exact B999151
  · exact B999155
  · exact B999159
  · exact B999163
  · exact B999167
  · exact B999171
  · exact B999175
  · exact B999179
  · exact B999183
  · exact B999187
  · exact B999191
  · exact B999195
  · exact B999199
  · exact B999203
  · exact B999207
  · exact B999211
  · exact B999215
  · exact B999219
  · exact B999223
  · exact B999227
  · exact B999231
  · exact B999235
  · exact B999239
  · exact B999243
  · exact B999247
  · exact B999251
  · exact B999255
  · exact B999259
  · exact B999263
  · exact B999267
  · exact B999271
  · exact B999275
  · exact B999279
  · exact B999283
  · exact B999287
  · exact B999291
  · exact B999295
  · exact B999299
  · exact B999303
  · exact B999307
  · exact B999311
  · exact B999315
  · exact B999319
  · exact B999323
  · exact B999327
  · exact B999331
  · exact B999335
  · exact B999339
  · exact B999343
  · exact B999347
  · exact B999351
  · exact B999355
  · exact B999359
  · exact B999363
  · exact B999367
  · exact B999371
  · exact B999375
  · exact B999379
  · exact B999383
  · exact B999387
  · exact B999391
  · exact B999395

theorem C1 (j : ℕ) (h1 : 249849 ≤ j) (h2 : j ≤ 250148) : Blo 996598 (4 * j + 3) := by
  interval_cases j
  · exact B999399
  · exact B999403
  · exact B999407
  · exact B999411
  · exact B999415
  · exact B999419
  · exact B999423
  · exact B999427
  · exact B999431
  · exact B999435
  · exact B999439
  · exact B999443
  · exact B999447
  · exact B999451
  · exact B999455
  · exact B999459
  · exact B999463
  · exact B999467
  · exact B999471
  · exact B999475
  · exact B999479
  · exact B999483
  · exact B999487
  · exact B999491
  · exact B999495
  · exact B999499
  · exact B999503
  · exact B999507
  · exact B999511
  · exact B999515
  · exact B999519
  · exact B999523
  · exact B999527
  · exact B999531
  · exact B999535
  · exact B999539
  · exact B999543
  · exact B999547
  · exact B999551
  · exact B999555
  · exact B999559
  · exact B999563
  · exact B999567
  · exact B999571
  · exact B999575
  · exact B999579
  · exact B999583
  · exact B999587
  · exact B999591
  · exact B999595
  · exact B999599
  · exact B999603
  · exact B999607
  · exact B999611
  · exact B999615
  · exact B999619
  · exact B999623
  · exact B999627
  · exact B999631
  · exact B999635
  · exact B999639
  · exact B999643
  · exact B999647
  · exact B999651
  · exact B999655
  · exact B999659
  · exact B999663
  · exact B999667
  · exact B999671
  · exact B999675
  · exact B999679
  · exact B999683
  · exact B999687
  · exact B999691
  · exact B999695
  · exact B999699
  · exact B999703
  · exact B999707
  · exact B999711
  · exact B999715
  · exact B999719
  · exact B999723
  · exact B999727
  · exact B999731
  · exact B999735
  · exact B999739
  · exact B999743
  · exact B999747
  · exact B999751
  · exact B999755
  · exact B999759
  · exact B999763
  · exact B999767
  · exact B999771
  · exact B999775
  · exact B999779
  · exact B999783
  · exact B999787
  · exact B999791
  · exact B999795
  · exact B999799
  · exact B999803
  · exact B999807
  · exact B999811
  · exact B999815
  · exact B999819
  · exact B999823
  · exact B999827
  · exact B999831
  · exact B999835
  · exact B999839
  · exact B999843
  · exact B999847
  · exact B999851
  · exact B999855
  · exact B999859
  · exact B999863
  · exact B999867
  · exact B999871
  · exact B999875
  · exact B999879
  · exact B999883
  · exact B999887
  · exact B999891
  · exact B999895
  · exact B999899
  · exact B999903
  · exact B999907
  · exact B999911
  · exact B999915
  · exact B999919
  · exact B999923
  · exact B999927
  · exact B999931
  · exact B999935
  · exact B999939
  · exact B999943
  · exact B999947
  · exact B999951
  · exact B999955
  · exact B999959
  · exact B999963
  · exact B999967
  · exact B999971
  · exact B999975
  · exact B999979
  · exact B999983
  · exact B999987
  · exact B999991
  · exact B999995
  · exact B999999
  · exact B1000003
  · exact B1000007
  · exact B1000011
  · exact B1000015
  · exact B1000019
  · exact B1000023
  · exact B1000027
  · exact B1000031
  · exact B1000035
  · exact B1000039
  · exact B1000043
  · exact B1000047
  · exact B1000051
  · exact B1000055
  · exact B1000059
  · exact B1000063
  · exact B1000067
  · exact B1000071
  · exact B1000075
  · exact B1000079
  · exact B1000083
  · exact B1000087
  · exact B1000091
  · exact B1000095
  · exact B1000099
  · exact B1000103
  · exact B1000107
  · exact B1000111
  · exact B1000115
  · exact B1000119
  · exact B1000123
  · exact B1000127
  · exact B1000131
  · exact B1000135
  · exact B1000139
  · exact B1000143
  · exact B1000147
  · exact B1000151
  · exact B1000155
  · exact B1000159
  · exact B1000163
  · exact B1000167
  · exact B1000171
  · exact B1000175
  · exact B1000179
  · exact B1000183
  · exact B1000187
  · exact B1000191
  · exact B1000195
  · exact B1000199
  · exact B1000203
  · exact B1000207
  · exact B1000211
  · exact B1000215
  · exact B1000219
  · exact B1000223
  · exact B1000227
  · exact B1000231
  · exact B1000235
  · exact B1000239
  · exact B1000243
  · exact B1000247
  · exact B1000251
  · exact B1000255
  · exact B1000259
  · exact B1000263
  · exact B1000267
  · exact B1000271
  · exact B1000275
  · exact B1000279
  · exact B1000283
  · exact B1000287
  · exact B1000291
  · exact B1000295
  · exact B1000299
  · exact B1000303
  · exact B1000307
  · exact B1000311
  · exact B1000315
  · exact B1000319
  · exact B1000323
  · exact B1000327
  · exact B1000331
  · exact B1000335
  · exact B1000339
  · exact B1000343
  · exact B1000347
  · exact B1000351
  · exact B1000355
  · exact B1000359
  · exact B1000363
  · exact B1000367
  · exact B1000371
  · exact B1000375
  · exact B1000379
  · exact B1000383
  · exact B1000387
  · exact B1000391
  · exact B1000395
  · exact B1000399
  · exact B1000403
  · exact B1000407
  · exact B1000411
  · exact B1000415
  · exact B1000419
  · exact B1000423
  · exact B1000427
  · exact B1000431
  · exact B1000435
  · exact B1000439
  · exact B1000443
  · exact B1000447
  · exact B1000451
  · exact B1000455
  · exact B1000459
  · exact B1000463
  · exact B1000467
  · exact B1000471
  · exact B1000475
  · exact B1000479
  · exact B1000483
  · exact B1000487
  · exact B1000491
  · exact B1000495
  · exact B1000499
  · exact B1000503
  · exact B1000507
  · exact B1000511
  · exact B1000515
  · exact B1000519
  · exact B1000523
  · exact B1000527
  · exact B1000531
  · exact B1000535
  · exact B1000539
  · exact B1000543
  · exact B1000547
  · exact B1000551
  · exact B1000555
  · exact B1000559
  · exact B1000563
  · exact B1000567
  · exact B1000571
  · exact B1000575
  · exact B1000579
  · exact B1000583
  · exact B1000587
  · exact B1000591
  · exact B1000595

theorem solution (m : ℕ) (hlo : 996598 ≤ m) (hhi : m ≤ 1000598) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 249149 ≤ j := by omega
    have hj2 : j ≤ 250148 := by omega
    have hb : Blo 996598 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 249849 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
