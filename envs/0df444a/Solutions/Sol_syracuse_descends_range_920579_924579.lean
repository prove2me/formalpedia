-- Prove2me | solution 1 for syracuse_descends_range_920579_924579
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:53.16721+00:00
-- url     : https://prove2.me/submissions/af5f7da7-8241-481b-8cc5-835624d30722

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


theorem B9469973 : Blo 920579 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B983125 : Blo 920579 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B3113045 : Blo 920579 3113045 := bbase (se 8 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 3113045 = 36481) (by norm_num)
theorem B1310845 : Blo 920579 1310845 := bbase (se 3 (by rfl) ⟨245783, by rfl⟩ : syracuseStep 1310845 = 491567) (by norm_num)
theorem B1474733 : Blo 920579 1474733 := bbase (se 3 (by rfl) ⟨276512, by rfl⟩ : syracuseStep 1474733 = 553025) (by norm_num)
theorem B2621621 : Blo 920579 2621621 := bbase (se 5 (by rfl) ⟨122888, by rfl⟩ : syracuseStep 2621621 = 245777) (by norm_num)
theorem B4423909 : Blo 920579 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B1311061 : Blo 920579 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B1474957 : Blo 920579 1474957 := bbase (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) (by norm_num)
theorem B3506597 : Blo 920579 3506597 := bbase (se 4 (by rfl) ⟨328743, by rfl⟩ : syracuseStep 3506597 = 657487) (by norm_num)
theorem B2130349 : Blo 920579 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B983497 : Blo 920579 983497 := bbase (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) (by norm_num)
theorem B23658965 : Blo 920579 23658965 := bbase (se 7 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 23658965 = 554507) (by norm_num)
theorem B3113477 : Blo 920579 3113477 := bbase (se 4 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 3113477 = 583777) (by norm_num)
theorem B7111253 : Blo 920579 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B3506885 : Blo 920579 3506885 := bbase (se 4 (by rfl) ⟨328770, by rfl⟩ : syracuseStep 3506885 = 657541) (by norm_num)
theorem B1311437 : Blo 920579 1311437 := bbase (se 3 (by rfl) ⟨245894, by rfl⟩ : syracuseStep 1311437 = 491789) (by norm_num)
theorem B983873 : Blo 920579 983873 := bbase (se 2 (by rfl) ⟨368952, by rfl⟩ : syracuseStep 983873 = 737905) (by norm_num)
theorem B1966933 : Blo 920579 1966933 := bbase (se 9 (by rfl) ⟨5762, by rfl⟩ : syracuseStep 1966933 = 11525) (by norm_num)
theorem B983945 : Blo 920579 983945 := bbase (se 2 (by rfl) ⟨368979, by rfl⟩ : syracuseStep 983945 = 737959) (by norm_num)
theorem B3113909 : Blo 920579 3113909 := bbase (se 5 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 3113909 = 291929) (by norm_num)
theorem B984133 : Blo 920579 984133 := bbase (se 4 (by rfl) ⟨92262, by rfl⟩ : syracuseStep 984133 = 184525) (by norm_num)
theorem B984317 : Blo 920579 984317 := bbase (se 3 (by rfl) ⟨184559, by rfl⟩ : syracuseStep 984317 = 369119) (by norm_num)
theorem B1967429 : Blo 920579 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B12617045 : Blo 920579 12617045 := bbase (se 12 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 12617045 = 9241) (by norm_num)
theorem B3114341 : Blo 920579 3114341 := bbase (se 4 (by rfl) ⟨291969, by rfl⟩ : syracuseStep 3114341 = 583939) (by norm_num)
theorem B2491813 : Blo 920579 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B1476085 : Blo 920579 1476085 := bbase (se 5 (by rfl) ⟨69191, by rfl⟩ : syracuseStep 1476085 = 138383) (by norm_num)
theorem B2623205 : Blo 920579 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B2950901 : Blo 920579 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B3114773 : Blo 920579 3114773 := bbase (se 6 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 3114773 = 146005) (by norm_num)
theorem B3508069 : Blo 920579 3508069 := bbase (se 4 (by rfl) ⟨328881, by rfl⟩ : syracuseStep 3508069 = 657763) (by norm_num)
theorem B1476533 : Blo 920579 1476533 := bbase (se 5 (by rfl) ⟨69212, by rfl⟩ : syracuseStep 1476533 = 138425) (by norm_num)
theorem B985069 : Blo 920579 985069 := bbase (se 3 (by rfl) ⟨184700, by rfl⟩ : syracuseStep 985069 = 369401) (by norm_num)
theorem B13273109 : Blo 920579 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B985141 : Blo 920579 985141 := bbase (se 5 (by rfl) ⟨46178, by rfl⟩ : syracuseStep 985141 = 92357) (by norm_num)
theorem B3934277 : Blo 920579 3934277 := bbase (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) (by norm_num)
theorem B1312861 : Blo 920579 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B1181821 : Blo 920579 1181821 := bbase (se 3 (by rfl) ⟨221591, by rfl⟩ : syracuseStep 1181821 = 443183) (by norm_num)
theorem B3508373 : Blo 920579 3508373 := bbase (se 6 (by rfl) ⟨82227, by rfl⟩ : syracuseStep 3508373 = 164455) (by norm_num)
theorem B1968293 : Blo 920579 1968293 := bbase (se 4 (by rfl) ⟨184527, by rfl⟩ : syracuseStep 1968293 = 369055) (by norm_num)
theorem B3115205 : Blo 920579 3115205 := bbase (se 4 (by rfl) ⟨292050, by rfl⟩ : syracuseStep 3115205 = 584101) (by norm_num)
theorem B985321 : Blo 920579 985321 := bbase (se 2 (by rfl) ⟨369495, by rfl⟩ : syracuseStep 985321 = 738991) (by norm_num)
theorem B1968437 : Blo 920579 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B4983125 : Blo 920579 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B2623877 : Blo 920579 2623877 := bbase (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) (by norm_num)
theorem B2099621 : Blo 920579 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B7473653 : Blo 920579 7473653 := bbase (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) (by norm_num)
theorem B3115637 : Blo 920579 3115637 := bbase (se 5 (by rfl) ⟨146045, by rfl⟩ : syracuseStep 3115637 = 292091) (by norm_num)
theorem B985765 : Blo 920579 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B1313453 : Blo 920579 1313453 := bbase (se 3 (by rfl) ⟨246272, by rfl⟩ : syracuseStep 1313453 = 492545) (by norm_num)
theorem B1051321 : Blo 920579 1051321 := bbase (se 2 (by rfl) ⟨394245, by rfl⟩ : syracuseStep 1051321 = 788491) (by norm_num)
theorem B1313533 : Blo 920579 1313533 := bbase (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) (by norm_num)
theorem B985889 : Blo 920579 985889 := bbase (se 2 (by rfl) ⟨369708, by rfl⟩ : syracuseStep 985889 = 739417) (by norm_num)
theorem B2624309 : Blo 920579 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B4000565 : Blo 920579 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B1313653 : Blo 920579 1313653 := bbase (se 5 (by rfl) ⟨61577, by rfl⟩ : syracuseStep 1313653 = 123155) (by norm_num)
theorem B1313749 : Blo 920579 1313749 := bbase (se 7 (by rfl) ⟨15395, by rfl⟩ : syracuseStep 1313749 = 30791) (by norm_num)
theorem B2100205 : Blo 920579 2100205 := bbase (se 3 (by rfl) ⟨393788, by rfl⟩ : syracuseStep 2100205 = 787577) (by norm_num)
theorem B1969181 : Blo 920579 1969181 := bbase (se 3 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 1969181 = 738443) (by norm_num)
theorem B986141 : Blo 920579 986141 := bbase (se 3 (by rfl) ⟨184901, by rfl⟩ : syracuseStep 986141 = 369803) (by norm_num)
theorem B3116069 : Blo 920579 3116069 := bbase (se 4 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 3116069 = 584263) (by norm_num)
theorem B2952245 : Blo 920579 2952245 := bbase (se 5 (by rfl) ⟨138386, by rfl⟩ : syracuseStep 2952245 = 276773) (by norm_num)
theorem B1248637 : Blo 920579 1248637 := bbase (se 3 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 1248637 = 468239) (by norm_num)
theorem B1052041 : Blo 920579 1052041 := bbase (se 2 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 1052041 = 789031) (by norm_num)
theorem B1478045 : Blo 920579 1478045 := bbase (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) (by norm_num)
theorem B1314245 : Blo 920579 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B1183177 : Blo 920579 1183177 := bbase (se 2 (by rfl) ⟨443691, by rfl⟩ : syracuseStep 1183177 = 887383) (by norm_num)
theorem B3116501 : Blo 920579 3116501 := bbase (se 7 (by rfl) ⟨36521, by rfl⟩ : syracuseStep 3116501 = 73043) (by norm_num)
theorem B986585 : Blo 920579 986585 := bbase (se 2 (by rfl) ⟨369969, by rfl⟩ : syracuseStep 986585 = 739939) (by norm_num)
theorem B2100725 : Blo 920579 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B1478173 : Blo 920579 1478173 := bbase (se 3 (by rfl) ⟨277157, by rfl⟩ : syracuseStep 1478173 = 554315) (by norm_num)
theorem B2625061 : Blo 920579 2625061 := bbase (se 4 (by rfl) ⟨246099, by rfl⟩ : syracuseStep 2625061 = 492199) (by norm_num)
theorem B1248853 : Blo 920579 1248853 := bbase (se 8 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 1248853 = 14635) (by norm_num)
theorem B2330309 : Blo 920579 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B986833 : Blo 920579 986833 := bbase (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) (by norm_num)
theorem B2526949 : Blo 920579 2526949 := bbase (se 4 (by rfl) ⟨236901, by rfl⟩ : syracuseStep 2526949 = 473803) (by norm_num)
theorem B1969933 : Blo 920579 1969933 := bbase (se 3 (by rfl) ⟨369362, by rfl⟩ : syracuseStep 1969933 = 738725) (by norm_num)
theorem B3936053 : Blo 920579 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B3116933 : Blo 920579 3116933 := bbase (se 4 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 3116933 = 584425) (by norm_num)
theorem B1970077 : Blo 920579 1970077 := bbase (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) (by norm_num)
theorem B1314797 : Blo 920579 1314797 := bbase (se 3 (by rfl) ⟨246524, by rfl⟩ : syracuseStep 1314797 = 493049) (by norm_num)
theorem B1249285 : Blo 920579 1249285 := bbase (se 4 (by rfl) ⟨117120, by rfl⟩ : syracuseStep 1249285 = 234241) (by norm_num)
theorem B1871885 : Blo 920579 1871885 := bbase (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) (by norm_num)
theorem B2330653 : Blo 920579 2330653 := bbase (se 3 (by rfl) ⟨436997, by rfl⟩ : syracuseStep 2330653 = 873995) (by norm_num)
theorem B2101373 : Blo 920579 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B2330765 : Blo 920579 2330765 := bbase (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) (by norm_num)
theorem B987277 : Blo 920579 987277 := bbase (se 3 (by rfl) ⟨185114, by rfl⟩ : syracuseStep 987277 = 370229) (by norm_num)
theorem B3510485 : Blo 920579 3510485 := bbase (se 7 (by rfl) ⟨41138, by rfl⟩ : syracuseStep 3510485 = 82277) (by norm_num)
theorem B3739925 : Blo 920579 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B1970453 : Blo 920579 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B5902645 : Blo 920579 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B3117365 : Blo 920579 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B2101565 : Blo 920579 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B1052989 : Blo 920579 1052989 := bbase (se 3 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 1052989 = 394871) (by norm_num)
theorem B2363717 : Blo 920579 2363717 := bbase (se 4 (by rfl) ⟨221598, by rfl⟩ : syracuseStep 2363717 = 443197) (by norm_num)
theorem B2330957 : Blo 920579 2330957 := bbase (se 3 (by rfl) ⟨437054, by rfl⟩ : syracuseStep 2330957 = 874109) (by norm_num)
theorem B1347925 : Blo 920579 1347925 := bbase (se 10 (by rfl) ⟨1974, by rfl⟩ : syracuseStep 1347925 = 3949) (by norm_num)
theorem B1773965 : Blo 920579 1773965 := bbase (se 3 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 1773965 = 665237) (by norm_num)
theorem B1380869 : Blo 920579 1380869 := bbase (se 4 (by rfl) ⟨129456, by rfl⟩ : syracuseStep 1380869 = 258913) (by norm_num)
theorem B1053209 : Blo 920579 1053209 := bbase (se 2 (by rfl) ⟨394953, by rfl⟩ : syracuseStep 1053209 = 789907) (by norm_num)
theorem B1380893 : Blo 920579 1380893 := bbase (se 3 (by rfl) ⟨258917, by rfl⟩ : syracuseStep 1380893 = 517835) (by norm_num)
theorem B1380917 : Blo 920579 1380917 := bbase (se 5 (by rfl) ⟨64730, by rfl⟩ : syracuseStep 1380917 = 129461) (by norm_num)
theorem B1380941 : Blo 920579 1380941 := bbase (se 3 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 1380941 = 517853) (by norm_num)
theorem B1053281 : Blo 920579 1053281 := bbase (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) (by norm_num)
theorem B1380965 : Blo 920579 1380965 := bbase (se 4 (by rfl) ⟨129465, by rfl⟩ : syracuseStep 1380965 = 258931) (by norm_num)
theorem B1380989 : Blo 920579 1380989 := bbase (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) (by norm_num)
theorem B1970821 : Blo 920579 1970821 := bbase (se 4 (by rfl) ⟨184764, by rfl⟩ : syracuseStep 1970821 = 369529) (by norm_num)
theorem B1381013 : Blo 920579 1381013 := bbase (se 6 (by rfl) ⟨32367, by rfl⟩ : syracuseStep 1381013 = 64735) (by norm_num)
theorem B2331301 : Blo 920579 2331301 := bbase (se 4 (by rfl) ⟨218559, by rfl⟩ : syracuseStep 2331301 = 437119) (by norm_num)
theorem B1381037 : Blo 920579 1381037 := bbase (se 3 (by rfl) ⟨258944, by rfl⟩ : syracuseStep 1381037 = 517889) (by norm_num)
theorem B1381061 : Blo 920579 1381061 := bbase (se 4 (by rfl) ⟨129474, by rfl⟩ : syracuseStep 1381061 = 258949) (by norm_num)
theorem B1381085 : Blo 920579 1381085 := bbase (se 3 (by rfl) ⟨258953, by rfl⟩ : syracuseStep 1381085 = 517907) (by norm_num)
theorem B1577693 : Blo 920579 1577693 := bbase (se 3 (by rfl) ⟨295817, by rfl⟩ : syracuseStep 1577693 = 591635) (by norm_num)
theorem B1315549 : Blo 920579 1315549 := bbase (se 3 (by rfl) ⟨246665, by rfl⟩ : syracuseStep 1315549 = 493331) (by norm_num)
theorem B3117797 : Blo 920579 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1381109 : Blo 920579 1381109 := bbase (se 5 (by rfl) ⟨64739, by rfl⟩ : syracuseStep 1381109 = 129479) (by norm_num)
theorem B1381133 : Blo 920579 1381133 := bbase (se 3 (by rfl) ⟨258962, by rfl⟩ : syracuseStep 1381133 = 517925) (by norm_num)
theorem B2331413 : Blo 920579 2331413 := bbase (se 6 (by rfl) ⟨54642, by rfl⟩ : syracuseStep 2331413 = 109285) (by norm_num)
theorem B3937045 : Blo 920579 3937045 := bbase (se 6 (by rfl) ⟨92274, by rfl⟩ : syracuseStep 3937045 = 184549) (by norm_num)
theorem B1381157 : Blo 920579 1381157 := bbase (se 4 (by rfl) ⟨129483, by rfl⟩ : syracuseStep 1381157 = 258967) (by norm_num)
theorem B1381181 : Blo 920579 1381181 := bbase (se 3 (by rfl) ⟨258971, by rfl⟩ : syracuseStep 1381181 = 517943) (by norm_num)
theorem B1381205 : Blo 920579 1381205 := bbase (se 9 (by rfl) ⟨4046, by rfl⟩ : syracuseStep 1381205 = 8093) (by norm_num)
theorem B1381229 : Blo 920579 1381229 := bbase (se 3 (by rfl) ⟨258980, by rfl⟩ : syracuseStep 1381229 = 517961) (by norm_num)
theorem B1381253 : Blo 920579 1381253 := bbase (se 4 (by rfl) ⟨129492, by rfl⟩ : syracuseStep 1381253 = 258985) (by norm_num)
theorem B1479557 : Blo 920579 1479557 := bbase (se 4 (by rfl) ⟨138708, by rfl⟩ : syracuseStep 1479557 = 277417) (by norm_num)
theorem B1381277 : Blo 920579 1381277 := bbase (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) (by norm_num)
theorem B1381301 : Blo 920579 1381301 := bbase (se 5 (by rfl) ⟨64748, by rfl⟩ : syracuseStep 1381301 = 129497) (by norm_num)
theorem B1381325 : Blo 920579 1381325 := bbase (se 3 (by rfl) ⟨258998, by rfl⟩ : syracuseStep 1381325 = 517997) (by norm_num)
theorem B2331605 : Blo 920579 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B1381349 : Blo 920579 1381349 := bbase (se 4 (by rfl) ⟨129501, by rfl⟩ : syracuseStep 1381349 = 259003) (by norm_num)
theorem B1381373 : Blo 920579 1381373 := bbase (se 3 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 1381373 = 518015) (by norm_num)
theorem B2954245 : Blo 920579 2954245 := bbase (se 4 (by rfl) ⟨276960, by rfl⟩ : syracuseStep 2954245 = 553921) (by norm_num)
theorem B1381397 : Blo 920579 1381397 := bbase (se 6 (by rfl) ⟨32376, by rfl⟩ : syracuseStep 1381397 = 64753) (by norm_num)
theorem B1381421 : Blo 920579 1381421 := bbase (se 3 (by rfl) ⟨259016, by rfl⟩ : syracuseStep 1381421 = 518033) (by norm_num)
theorem B1381445 : Blo 920579 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B1381469 : Blo 920579 1381469 := bbase (se 3 (by rfl) ⟨259025, by rfl⟩ : syracuseStep 1381469 = 518051) (by norm_num)
theorem B1381493 : Blo 920579 1381493 := bbase (se 5 (by rfl) ⟨64757, by rfl⟩ : syracuseStep 1381493 = 129515) (by norm_num)
theorem B1381517 : Blo 920579 1381517 := bbase (se 3 (by rfl) ⟨259034, by rfl⟩ : syracuseStep 1381517 = 518069) (by norm_num)
theorem B3118229 : Blo 920579 3118229 := bbase (se 6 (by rfl) ⟨73083, by rfl⟩ : syracuseStep 3118229 = 146167) (by norm_num)
theorem B1381541 : Blo 920579 1381541 := bbase (se 4 (by rfl) ⟨129519, by rfl⟩ : syracuseStep 1381541 = 259039) (by norm_num)
theorem B1053865 : Blo 920579 1053865 := bbase (se 2 (by rfl) ⟨395199, by rfl⟩ : syracuseStep 1053865 = 790399) (by norm_num)
theorem B1381565 : Blo 920579 1381565 := bbase (se 3 (by rfl) ⟨259043, by rfl⟩ : syracuseStep 1381565 = 518087) (by norm_num)
theorem B1381589 : Blo 920579 1381589 := bbase (se 7 (by rfl) ⟨16190, by rfl⟩ : syracuseStep 1381589 = 32381) (by norm_num)
theorem B1381613 : Blo 920579 1381613 := bbase (se 3 (by rfl) ⟨259052, by rfl⟩ : syracuseStep 1381613 = 518105) (by norm_num)
theorem B1381637 : Blo 920579 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B1381661 : Blo 920579 1381661 := bbase (se 3 (by rfl) ⟨259061, by rfl⟩ : syracuseStep 1381661 = 518123) (by norm_num)
theorem B2331949 : Blo 920579 2331949 := bbase (se 3 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 2331949 = 874481) (by norm_num)
theorem B1381685 : Blo 920579 1381685 := bbase (se 5 (by rfl) ⟨64766, by rfl⟩ : syracuseStep 1381685 = 129533) (by norm_num)
theorem B1381709 : Blo 920579 1381709 := bbase (se 3 (by rfl) ⟨259070, by rfl⟩ : syracuseStep 1381709 = 518141) (by norm_num)
theorem B1381733 : Blo 920579 1381733 := bbase (se 4 (by rfl) ⟨129537, by rfl⟩ : syracuseStep 1381733 = 259075) (by norm_num)
theorem B1381757 : Blo 920579 1381757 := bbase (se 3 (by rfl) ⟨259079, by rfl⟩ : syracuseStep 1381757 = 518159) (by norm_num)
theorem B1381781 : Blo 920579 1381781 := bbase (se 6 (by rfl) ⟨32385, by rfl⟩ : syracuseStep 1381781 = 64771) (by norm_num)
theorem B2332061 : Blo 920579 2332061 := bbase (se 3 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 2332061 = 874523) (by norm_num)
theorem B1381805 : Blo 920579 1381805 := bbase (se 3 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 1381805 = 518177) (by norm_num)
theorem B1381829 : Blo 920579 1381829 := bbase (se 4 (by rfl) ⟨129546, by rfl⟩ : syracuseStep 1381829 = 259093) (by norm_num)
theorem B16848341 : Blo 920579 16848341 := bbase (se 7 (by rfl) ⟨197441, by rfl⟩ : syracuseStep 16848341 = 394883) (by norm_num)
theorem B1381853 : Blo 920579 1381853 := bbase (se 3 (by rfl) ⟨259097, by rfl⟩ : syracuseStep 1381853 = 518195) (by norm_num)
theorem B1381877 : Blo 920579 1381877 := bbase (se 5 (by rfl) ⟨64775, by rfl⟩ : syracuseStep 1381877 = 129551) (by norm_num)
theorem B1316341 : Blo 920579 1316341 := bbase (se 5 (by rfl) ⟨61703, by rfl⟩ : syracuseStep 1316341 = 123407) (by norm_num)
theorem B1381901 : Blo 920579 1381901 := bbase (se 3 (by rfl) ⟨259106, by rfl⟩ : syracuseStep 1381901 = 518213) (by norm_num)
theorem B1381925 : Blo 920579 1381925 := bbase (se 4 (by rfl) ⟨129555, by rfl⟩ : syracuseStep 1381925 = 259111) (by norm_num)
theorem B1381949 : Blo 920579 1381949 := bbase (se 3 (by rfl) ⟨259115, by rfl⟩ : syracuseStep 1381949 = 518231) (by norm_num)
theorem B3118661 : Blo 920579 3118661 := bbase (se 4 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 3118661 = 584749) (by norm_num)
theorem B1381973 : Blo 920579 1381973 := bbase (se 8 (by rfl) ⟨8097, by rfl⟩ : syracuseStep 1381973 = 16195) (by norm_num)
theorem B1578581 : Blo 920579 1578581 := bbase (se 8 (by rfl) ⟨9249, by rfl⟩ : syracuseStep 1578581 = 18499) (by norm_num)
theorem B2332253 : Blo 920579 2332253 := bbase (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) (by norm_num)
theorem B1381997 : Blo 920579 1381997 := bbase (se 3 (by rfl) ⟨259124, by rfl⟩ : syracuseStep 1381997 = 518249) (by norm_num)
theorem B1382021 : Blo 920579 1382021 := bbase (se 4 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 1382021 = 259129) (by norm_num)
theorem B1382045 : Blo 920579 1382045 := bbase (se 3 (by rfl) ⟨259133, by rfl⟩ : syracuseStep 1382045 = 518267) (by norm_num)
theorem B1382069 : Blo 920579 1382069 := bbase (se 5 (by rfl) ⟨64784, by rfl⟩ : syracuseStep 1382069 = 129569) (by norm_num)
theorem B1382093 : Blo 920579 1382093 := bbase (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) (by norm_num)
theorem B1382117 : Blo 920579 1382117 := bbase (se 4 (by rfl) ⟨129573, by rfl⟩ : syracuseStep 1382117 = 259147) (by norm_num)
theorem B1382141 : Blo 920579 1382141 := bbase (se 3 (by rfl) ⟨259151, by rfl⟩ : syracuseStep 1382141 = 518303) (by norm_num)
theorem B1382165 : Blo 920579 1382165 := bbase (se 6 (by rfl) ⟨32394, by rfl⟩ : syracuseStep 1382165 = 64789) (by norm_num)
theorem B1382189 : Blo 920579 1382189 := bbase (se 3 (by rfl) ⟨259160, by rfl⟩ : syracuseStep 1382189 = 518321) (by norm_num)
theorem B1480493 : Blo 920579 1480493 := bbase (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) (by norm_num)
theorem B1382213 : Blo 920579 1382213 := bbase (se 4 (by rfl) ⟨129582, by rfl⟩ : syracuseStep 1382213 = 259165) (by norm_num)
theorem B7018325 : Blo 920579 7018325 := bbase (se 9 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 7018325 = 41123) (by norm_num)
theorem B1382237 : Blo 920579 1382237 := bbase (se 3 (by rfl) ⟨259169, by rfl⟩ : syracuseStep 1382237 = 518339) (by norm_num)
theorem B1382261 : Blo 920579 1382261 := bbase (se 5 (by rfl) ⟨64793, by rfl⟩ : syracuseStep 1382261 = 129587) (by norm_num)
theorem B1382285 : Blo 920579 1382285 := bbase (se 3 (by rfl) ⟨259178, by rfl⟩ : syracuseStep 1382285 = 518357) (by norm_num)
theorem B1382309 : Blo 920579 1382309 := bbase (se 4 (by rfl) ⟨129591, by rfl⟩ : syracuseStep 1382309 = 259183) (by norm_num)
theorem B2332597 : Blo 920579 2332597 := bbase (se 5 (by rfl) ⟨109340, by rfl⟩ : syracuseStep 2332597 = 218681) (by norm_num)
theorem B4986805 : Blo 920579 4986805 := bbase (se 5 (by rfl) ⟨233756, by rfl⟩ : syracuseStep 4986805 = 467513) (by norm_num)
theorem B1382333 : Blo 920579 1382333 := bbase (se 3 (by rfl) ⟨259187, by rfl⟩ : syracuseStep 1382333 = 518375) (by norm_num)
theorem B1382357 : Blo 920579 1382357 := bbase (se 7 (by rfl) ⟨16199, by rfl⟩ : syracuseStep 1382357 = 32399) (by norm_num)
theorem B1382381 : Blo 920579 1382381 := bbase (se 3 (by rfl) ⟨259196, by rfl⟩ : syracuseStep 1382381 = 518393) (by norm_num)
theorem B3119093 : Blo 920579 3119093 := bbase (se 5 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 3119093 = 292415) (by norm_num)
theorem B1382405 : Blo 920579 1382405 := bbase (se 4 (by rfl) ⟨129600, by rfl⟩ : syracuseStep 1382405 = 259201) (by norm_num)
theorem B4429829 : Blo 920579 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B2103317 : Blo 920579 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B1382429 : Blo 920579 1382429 := bbase (se 3 (by rfl) ⟨259205, by rfl⟩ : syracuseStep 1382429 = 518411) (by norm_num)
theorem B2332709 : Blo 920579 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B1382453 : Blo 920579 1382453 := bbase (se 5 (by rfl) ⟨64802, by rfl⟩ : syracuseStep 1382453 = 129605) (by norm_num)
theorem B1382477 : Blo 920579 1382477 := bbase (se 3 (by rfl) ⟨259214, by rfl⟩ : syracuseStep 1382477 = 518429) (by norm_num)
theorem B1382501 : Blo 920579 1382501 := bbase (se 4 (by rfl) ⟨129609, by rfl⟩ : syracuseStep 1382501 = 259219) (by norm_num)
theorem B1972325 : Blo 920579 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B1382525 : Blo 920579 1382525 := bbase (se 3 (by rfl) ⟨259223, by rfl⟩ : syracuseStep 1382525 = 518447) (by norm_num)
theorem B1382549 : Blo 920579 1382549 := bbase (se 6 (by rfl) ⟨32403, by rfl⟩ : syracuseStep 1382549 = 64807) (by norm_num)
theorem B1382573 : Blo 920579 1382573 := bbase (se 3 (by rfl) ⟨259232, by rfl⟩ : syracuseStep 1382573 = 518465) (by norm_num)
theorem B1382597 : Blo 920579 1382597 := bbase (se 4 (by rfl) ⟨129618, by rfl⟩ : syracuseStep 1382597 = 259237) (by norm_num)
theorem B1382621 : Blo 920579 1382621 := bbase (se 3 (by rfl) ⟨259241, by rfl⟩ : syracuseStep 1382621 = 518483) (by norm_num)
theorem B2332901 : Blo 920579 2332901 := bbase (se 4 (by rfl) ⟨218709, by rfl⟩ : syracuseStep 2332901 = 437419) (by norm_num)
theorem B1382645 : Blo 920579 1382645 := bbase (se 5 (by rfl) ⟨64811, by rfl⟩ : syracuseStep 1382645 = 129623) (by norm_num)
theorem B1972469 : Blo 920579 1972469 := bbase (se 5 (by rfl) ⟨92459, by rfl⟩ : syracuseStep 1972469 = 184919) (by norm_num)
theorem B1382669 : Blo 920579 1382669 := bbase (se 3 (by rfl) ⟨259250, by rfl⟩ : syracuseStep 1382669 = 518501) (by norm_num)
theorem B1382693 : Blo 920579 1382693 := bbase (se 4 (by rfl) ⟨129627, by rfl⟩ : syracuseStep 1382693 = 259255) (by norm_num)
theorem B1382717 : Blo 920579 1382717 := bbase (se 3 (by rfl) ⟨259259, by rfl⟩ : syracuseStep 1382717 = 518519) (by norm_num)
theorem B2627909 : Blo 920579 2627909 := bbase (se 4 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 2627909 = 492733) (by norm_num)
theorem B1382741 : Blo 920579 1382741 := bbase (se 10 (by rfl) ⟨2025, by rfl⟩ : syracuseStep 1382741 = 4051) (by norm_num)
theorem B1382765 : Blo 920579 1382765 := bbase (se 3 (by rfl) ⟨259268, by rfl⟩ : syracuseStep 1382765 = 518537) (by norm_num)
theorem B1382789 : Blo 920579 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B1382813 : Blo 920579 1382813 := bbase (se 3 (by rfl) ⟨259277, by rfl⟩ : syracuseStep 1382813 = 518555) (by norm_num)
theorem B2365861 : Blo 920579 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B3119525 : Blo 920579 3119525 := bbase (se 4 (by rfl) ⟨292455, by rfl⟩ : syracuseStep 3119525 = 584911) (by norm_num)
theorem B1382837 : Blo 920579 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B1382861 : Blo 920579 1382861 := bbase (se 3 (by rfl) ⟨259286, by rfl⟩ : syracuseStep 1382861 = 518573) (by norm_num)
theorem B2365901 : Blo 920579 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B1382885 : Blo 920579 1382885 := bbase (se 4 (by rfl) ⟨129645, by rfl⟩ : syracuseStep 1382885 = 259291) (by norm_num)
theorem B2497013 : Blo 920579 2497013 := bbase (se 5 (by rfl) ⟨117047, by rfl⟩ : syracuseStep 2497013 = 234095) (by norm_num)
theorem B1382909 : Blo 920579 1382909 := bbase (se 3 (by rfl) ⟨259295, by rfl⟩ : syracuseStep 1382909 = 518591) (by norm_num)
theorem B1382933 : Blo 920579 1382933 := bbase (se 6 (by rfl) ⟨32412, by rfl⟩ : syracuseStep 1382933 = 64825) (by norm_num)
theorem B1382957 : Blo 920579 1382957 := bbase (se 3 (by rfl) ⟨259304, by rfl⟩ : syracuseStep 1382957 = 518609) (by norm_num)
theorem B2333245 : Blo 920579 2333245 := bbase (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) (by norm_num)
theorem B4725317 : Blo 920579 4725317 := bbase (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) (by norm_num)
theorem B1382981 : Blo 920579 1382981 := bbase (se 4 (by rfl) ⟨129654, by rfl⟩ : syracuseStep 1382981 = 259309) (by norm_num)
theorem B1383005 : Blo 920579 1383005 := bbase (se 3 (by rfl) ⟨259313, by rfl⟩ : syracuseStep 1383005 = 518627) (by norm_num)
theorem B1972829 : Blo 920579 1972829 := bbase (se 3 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 1972829 = 739811) (by norm_num)
theorem B1383029 : Blo 920579 1383029 := bbase (se 5 (by rfl) ⟨64829, by rfl⟩ : syracuseStep 1383029 = 129659) (by norm_num)
theorem B1383053 : Blo 920579 1383053 := bbase (se 3 (by rfl) ⟨259322, by rfl⟩ : syracuseStep 1383053 = 518645) (by norm_num)
theorem B1383077 : Blo 920579 1383077 := bbase (se 4 (by rfl) ⟨129663, by rfl⟩ : syracuseStep 1383077 = 259327) (by norm_num)
theorem B2333357 : Blo 920579 2333357 := bbase (se 3 (by rfl) ⟨437504, by rfl⟩ : syracuseStep 2333357 = 875009) (by norm_num)
theorem B1383101 : Blo 920579 1383101 := bbase (se 3 (by rfl) ⟨259331, by rfl⟩ : syracuseStep 1383101 = 518663) (by norm_num)
theorem B1383125 : Blo 920579 1383125 := bbase (se 7 (by rfl) ⟨16208, by rfl⟩ : syracuseStep 1383125 = 32417) (by norm_num)
theorem B1383149 : Blo 920579 1383149 := bbase (se 3 (by rfl) ⟨259340, by rfl⟩ : syracuseStep 1383149 = 518681) (by norm_num)
theorem B1383173 : Blo 920579 1383173 := bbase (se 4 (by rfl) ⟨129672, by rfl⟩ : syracuseStep 1383173 = 259345) (by norm_num)
theorem B1383197 : Blo 920579 1383197 := bbase (se 3 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 1383197 = 518699) (by norm_num)
theorem B2071349 : Blo 920579 2071349 := bbase (se 5 (by rfl) ⟨97094, by rfl⟩ : syracuseStep 2071349 = 194189) (by norm_num)
theorem B1383221 : Blo 920579 1383221 := bbase (se 5 (by rfl) ⟨64838, by rfl⟩ : syracuseStep 1383221 = 129677) (by norm_num)
theorem B2497349 : Blo 920579 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B1383245 : Blo 920579 1383245 := bbase (se 3 (by rfl) ⟨259358, by rfl⟩ : syracuseStep 1383245 = 518717) (by norm_num)
theorem B3119957 : Blo 920579 3119957 := bbase (se 9 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 3119957 = 18281) (by norm_num)
theorem B3545957 : Blo 920579 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B1383269 : Blo 920579 1383269 := bbase (se 4 (by rfl) ⟨129681, by rfl⟩ : syracuseStep 1383269 = 259363) (by norm_num)
theorem B2333549 : Blo 920579 2333549 := bbase (se 3 (by rfl) ⟨437540, by rfl⟩ : syracuseStep 2333549 = 875081) (by norm_num)
theorem B2071421 : Blo 920579 2071421 := bbase (se 3 (by rfl) ⟨388391, by rfl⟩ : syracuseStep 2071421 = 776783) (by norm_num)
theorem B1383293 : Blo 920579 1383293 := bbase (se 3 (by rfl) ⟨259367, by rfl⟩ : syracuseStep 1383293 = 518735) (by norm_num)
theorem B1383317 : Blo 920579 1383317 := bbase (se 6 (by rfl) ⟨32421, by rfl⟩ : syracuseStep 1383317 = 64843) (by norm_num)
theorem B1383341 : Blo 920579 1383341 := bbase (se 3 (by rfl) ⟨259376, by rfl⟩ : syracuseStep 1383341 = 518753) (by norm_num)
theorem B2071493 : Blo 920579 2071493 := bbase (se 4 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 2071493 = 388405) (by norm_num)
theorem B3152837 : Blo 920579 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B1383365 : Blo 920579 1383365 := bbase (se 4 (by rfl) ⟨129690, by rfl⟩ : syracuseStep 1383365 = 259381) (by norm_num)
theorem B1383389 : Blo 920579 1383389 := bbase (se 3 (by rfl) ⟨259385, by rfl⟩ : syracuseStep 1383389 = 518771) (by norm_num)
theorem B1580005 : Blo 920579 1580005 := bbase (se 4 (by rfl) ⟨148125, by rfl⟩ : syracuseStep 1580005 = 296251) (by norm_num)
theorem B2104301 : Blo 920579 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B1383413 : Blo 920579 1383413 := bbase (se 5 (by rfl) ⟨64847, by rfl⟩ : syracuseStep 1383413 = 129695) (by norm_num)
theorem B1776629 : Blo 920579 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B2071565 : Blo 920579 2071565 := bbase (se 3 (by rfl) ⟨388418, by rfl⟩ : syracuseStep 2071565 = 776837) (by norm_num)
theorem B1383437 : Blo 920579 1383437 := bbase (se 3 (by rfl) ⟨259394, by rfl⟩ : syracuseStep 1383437 = 518789) (by norm_num)
theorem B1383461 : Blo 920579 1383461 := bbase (se 4 (by rfl) ⟨129699, by rfl⟩ : syracuseStep 1383461 = 259399) (by norm_num)
theorem B1383485 : Blo 920579 1383485 := bbase (se 3 (by rfl) ⟨259403, by rfl⟩ : syracuseStep 1383485 = 518807) (by norm_num)
theorem B2071637 : Blo 920579 2071637 := bbase (se 8 (by rfl) ⟨12138, by rfl⟩ : syracuseStep 2071637 = 24277) (by norm_num)
theorem B5905493 : Blo 920579 5905493 := bbase (se 8 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 5905493 = 69205) (by norm_num)
theorem B1383509 : Blo 920579 1383509 := bbase (se 8 (by rfl) ⟨8106, by rfl⟩ : syracuseStep 1383509 = 16213) (by norm_num)
theorem B1383533 : Blo 920579 1383533 := bbase (se 3 (by rfl) ⟨259412, by rfl⟩ : syracuseStep 1383533 = 518825) (by norm_num)
theorem B1383557 : Blo 920579 1383557 := bbase (se 4 (by rfl) ⟨129708, by rfl⟩ : syracuseStep 1383557 = 259417) (by norm_num)
theorem B2071709 : Blo 920579 2071709 := bbase (se 3 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 2071709 = 776891) (by norm_num)
theorem B1383581 : Blo 920579 1383581 := bbase (se 3 (by rfl) ⟨259421, by rfl⟩ : syracuseStep 1383581 = 518843) (by norm_num)
theorem B1383605 : Blo 920579 1383605 := bbase (se 5 (by rfl) ⟨64856, by rfl⟩ : syracuseStep 1383605 = 129713) (by norm_num)
theorem B2333893 : Blo 920579 2333893 := bbase (se 4 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 2333893 = 437605) (by norm_num)
theorem B1383629 : Blo 920579 1383629 := bbase (se 3 (by rfl) ⟨259430, by rfl⟩ : syracuseStep 1383629 = 518861) (by norm_num)
theorem B2071781 : Blo 920579 2071781 := bbase (se 4 (by rfl) ⟨194229, by rfl⟩ : syracuseStep 2071781 = 388459) (by norm_num)
theorem B1383653 : Blo 920579 1383653 := bbase (se 4 (by rfl) ⟨129717, by rfl⟩ : syracuseStep 1383653 = 259435) (by norm_num)
theorem B1383677 : Blo 920579 1383677 := bbase (se 3 (by rfl) ⟨259439, by rfl⟩ : syracuseStep 1383677 = 518879) (by norm_num)
theorem B3120389 : Blo 920579 3120389 := bbase (se 4 (by rfl) ⟨292536, by rfl⟩ : syracuseStep 3120389 = 585073) (by norm_num)
theorem B1383701 : Blo 920579 1383701 := bbase (se 6 (by rfl) ⟨32430, by rfl⟩ : syracuseStep 1383701 = 64861) (by norm_num)
theorem B2104613 : Blo 920579 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B2071853 : Blo 920579 2071853 := bbase (se 3 (by rfl) ⟨388472, by rfl⟩ : syracuseStep 2071853 = 776945) (by norm_num)
theorem B1383725 : Blo 920579 1383725 := bbase (se 3 (by rfl) ⟨259448, by rfl⟩ : syracuseStep 1383725 = 518897) (by norm_num)
theorem B2334005 : Blo 920579 2334005 := bbase (se 5 (by rfl) ⟨109406, by rfl⟩ : syracuseStep 2334005 = 218813) (by norm_num)
theorem B1383749 : Blo 920579 1383749 := bbase (se 4 (by rfl) ⟨129726, by rfl⟩ : syracuseStep 1383749 = 259453) (by norm_num)
theorem B23928149 : Blo 920579 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B1383773 : Blo 920579 1383773 := bbase (se 3 (by rfl) ⟨259457, by rfl⟩ : syracuseStep 1383773 = 518915) (by norm_num)
theorem B2071925 : Blo 920579 2071925 := bbase (se 5 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 2071925 = 194243) (by norm_num)
theorem B1383797 : Blo 920579 1383797 := bbase (se 5 (by rfl) ⟨64865, by rfl⟩ : syracuseStep 1383797 = 129731) (by norm_num)
theorem B1154425 : Blo 920579 1154425 := bbase (se 2 (by rfl) ⟨432909, by rfl⟩ : syracuseStep 1154425 = 865819) (by norm_num)
theorem B1383821 : Blo 920579 1383821 := bbase (se 3 (by rfl) ⟨259466, by rfl⟩ : syracuseStep 1383821 = 518933) (by norm_num)
theorem B2661781 : Blo 920579 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B1383845 : Blo 920579 1383845 := bbase (se 4 (by rfl) ⟨129735, by rfl⟩ : syracuseStep 1383845 = 259471) (by norm_num)
theorem B2071997 : Blo 920579 2071997 := bbase (se 3 (by rfl) ⟨388499, by rfl⟩ : syracuseStep 2071997 = 776999) (by norm_num)
theorem B1383869 : Blo 920579 1383869 := bbase (se 3 (by rfl) ⟨259475, by rfl⟩ : syracuseStep 1383869 = 518951) (by norm_num)
theorem B1383893 : Blo 920579 1383893 := bbase (se 7 (by rfl) ⟨16217, by rfl⟩ : syracuseStep 1383893 = 32435) (by norm_num)
theorem B1973717 : Blo 920579 1973717 := bbase (se 7 (by rfl) ⟨23129, by rfl⟩ : syracuseStep 1973717 = 46259) (by norm_num)
theorem B2629093 : Blo 920579 2629093 := bbase (se 4 (by rfl) ⟨246477, by rfl⟩ : syracuseStep 2629093 = 492955) (by norm_num)
theorem B1383917 : Blo 920579 1383917 := bbase (se 3 (by rfl) ⟨259484, by rfl⟩ : syracuseStep 1383917 = 518969) (by norm_num)
theorem B2334197 : Blo 920579 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B2072069 : Blo 920579 2072069 := bbase (se 4 (by rfl) ⟨194256, by rfl⟩ : syracuseStep 2072069 = 388513) (by norm_num)
theorem B1383941 : Blo 920579 1383941 := bbase (se 4 (by rfl) ⟨129744, by rfl⟩ : syracuseStep 1383941 = 259489) (by norm_num)
theorem B1383965 : Blo 920579 1383965 := bbase (se 3 (by rfl) ⟨259493, by rfl⟩ : syracuseStep 1383965 = 518987) (by norm_num)
theorem B1383989 : Blo 920579 1383989 := bbase (se 5 (by rfl) ⟨64874, by rfl⟩ : syracuseStep 1383989 = 129749) (by norm_num)
theorem B2072141 : Blo 920579 2072141 := bbase (se 3 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 2072141 = 777053) (by norm_num)
theorem B1384013 : Blo 920579 1384013 := bbase (se 3 (by rfl) ⟨259502, by rfl⟩ : syracuseStep 1384013 = 519005) (by norm_num)
theorem B1384037 : Blo 920579 1384037 := bbase (se 4 (by rfl) ⟨129753, by rfl⟩ : syracuseStep 1384037 = 259507) (by norm_num)
theorem B1384061 : Blo 920579 1384061 := bbase (se 3 (by rfl) ⟨259511, by rfl⟩ : syracuseStep 1384061 = 519023) (by norm_num)
theorem B2629253 : Blo 920579 2629253 := bbase (se 4 (by rfl) ⟨246492, by rfl⟩ : syracuseStep 2629253 = 492985) (by norm_num)
theorem B2072213 : Blo 920579 2072213 := bbase (se 6 (by rfl) ⟨48567, by rfl⟩ : syracuseStep 2072213 = 97135) (by norm_num)
theorem B1384085 : Blo 920579 1384085 := bbase (se 6 (by rfl) ⟨32439, by rfl⟩ : syracuseStep 1384085 = 64879) (by norm_num)
theorem B4660901 : Blo 920579 4660901 := bbase (se 4 (by rfl) ⟨436959, by rfl⟩ : syracuseStep 4660901 = 873919) (by norm_num)
theorem B1384109 : Blo 920579 1384109 := bbase (se 3 (by rfl) ⟨259520, by rfl⟩ : syracuseStep 1384109 = 519041) (by norm_num)
theorem B1384133 : Blo 920579 1384133 := bbase (se 4 (by rfl) ⟨129762, by rfl⟩ : syracuseStep 1384133 = 259525) (by norm_num)
theorem B1973965 : Blo 920579 1973965 := bbase (se 3 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 1973965 = 740237) (by norm_num)
theorem B2072285 : Blo 920579 2072285 := bbase (se 3 (by rfl) ⟨388553, by rfl⟩ : syracuseStep 2072285 = 777107) (by norm_num)
theorem B1384157 : Blo 920579 1384157 := bbase (se 3 (by rfl) ⟨259529, by rfl⟩ : syracuseStep 1384157 = 519059) (by norm_num)
theorem B1384181 : Blo 920579 1384181 := bbase (se 5 (by rfl) ⟨64883, by rfl⟩ : syracuseStep 1384181 = 129767) (by norm_num)
theorem B1384205 : Blo 920579 1384205 := bbase (se 3 (by rfl) ⟨259538, by rfl⟩ : syracuseStep 1384205 = 519077) (by norm_num)
theorem B2072357 : Blo 920579 2072357 := bbase (se 4 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 2072357 = 388567) (by norm_num)
theorem B1384229 : Blo 920579 1384229 := bbase (se 4 (by rfl) ⟨129771, by rfl⟩ : syracuseStep 1384229 = 259543) (by norm_num)
theorem B1384253 : Blo 920579 1384253 := bbase (se 3 (by rfl) ⟨259547, by rfl⟩ : syracuseStep 1384253 = 519095) (by norm_num)
theorem B2334541 : Blo 920579 2334541 := bbase (se 3 (by rfl) ⟨437726, by rfl⟩ : syracuseStep 2334541 = 875453) (by norm_num)
theorem B1384277 : Blo 920579 1384277 := bbase (se 9 (by rfl) ⟨4055, by rfl⟩ : syracuseStep 1384277 = 8111) (by norm_num)
theorem B2072429 : Blo 920579 2072429 := bbase (se 3 (by rfl) ⟨388580, by rfl⟩ : syracuseStep 2072429 = 777161) (by norm_num)
theorem B1384301 : Blo 920579 1384301 := bbase (se 3 (by rfl) ⟨259556, by rfl⟩ : syracuseStep 1384301 = 519113) (by norm_num)
theorem B2629493 : Blo 920579 2629493 := bbase (se 5 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 2629493 = 246515) (by norm_num)
theorem B1384325 : Blo 920579 1384325 := bbase (se 4 (by rfl) ⟨129780, by rfl⟩ : syracuseStep 1384325 = 259561) (by norm_num)
theorem B1384349 : Blo 920579 1384349 := bbase (se 3 (by rfl) ⟨259565, by rfl⟩ : syracuseStep 1384349 = 519131) (by norm_num)
theorem B2072501 : Blo 920579 2072501 := bbase (se 5 (by rfl) ⟨97148, by rfl⟩ : syracuseStep 2072501 = 194297) (by norm_num)
theorem B1384373 : Blo 920579 1384373 := bbase (se 5 (by rfl) ⟨64892, by rfl⟩ : syracuseStep 1384373 = 129785) (by norm_num)
theorem B2334653 : Blo 920579 2334653 := bbase (se 3 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 2334653 = 875495) (by norm_num)
theorem B1384397 : Blo 920579 1384397 := bbase (se 3 (by rfl) ⟨259574, by rfl⟩ : syracuseStep 1384397 = 519149) (by norm_num)
theorem B2957269 : Blo 920579 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B1384421 : Blo 920579 1384421 := bbase (se 4 (by rfl) ⟨129789, by rfl⟩ : syracuseStep 1384421 = 259579) (by norm_num)
theorem B1384445 : Blo 920579 1384445 := bbase (se 3 (by rfl) ⟨259583, by rfl⟩ : syracuseStep 1384445 = 519167) (by norm_num)
theorem B2072573 : Blo 920579 2072573 := bbase (se 3 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 2072573 = 777215) (by norm_num)
theorem B1384469 : Blo 920579 1384469 := bbase (se 6 (by rfl) ⟨32448, by rfl⟩ : syracuseStep 1384469 = 64897) (by norm_num)
theorem B1384493 : Blo 920579 1384493 := bbase (se 3 (by rfl) ⟨259592, by rfl⟩ : syracuseStep 1384493 = 519185) (by norm_num)
theorem B2629685 : Blo 920579 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B2072645 : Blo 920579 2072645 := bbase (se 4 (by rfl) ⟨194310, by rfl⟩ : syracuseStep 2072645 = 388621) (by norm_num)
theorem B1384517 : Blo 920579 1384517 := bbase (se 4 (by rfl) ⟨129798, by rfl⟩ : syracuseStep 1384517 = 259597) (by norm_num)
theorem B1384541 : Blo 920579 1384541 := bbase (se 3 (by rfl) ⟨259601, by rfl⟩ : syracuseStep 1384541 = 519203) (by norm_num)
theorem B1384565 : Blo 920579 1384565 := bbase (se 5 (by rfl) ⟨64901, by rfl⟩ : syracuseStep 1384565 = 129803) (by norm_num)
theorem B2334845 : Blo 920579 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B2072717 : Blo 920579 2072717 := bbase (se 3 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 2072717 = 777269) (by norm_num)
theorem B1384589 : Blo 920579 1384589 := bbase (se 3 (by rfl) ⟨259610, by rfl⟩ : syracuseStep 1384589 = 519221) (by norm_num)
theorem B1384613 : Blo 920579 1384613 := bbase (se 4 (by rfl) ⟨129807, by rfl⟩ : syracuseStep 1384613 = 259615) (by norm_num)
theorem B1384637 : Blo 920579 1384637 := bbase (se 3 (by rfl) ⟨259619, by rfl⟩ : syracuseStep 1384637 = 519239) (by norm_num)
theorem B1974469 : Blo 920579 1974469 := bbase (se 4 (by rfl) ⟨185106, by rfl⟩ : syracuseStep 1974469 = 370213) (by norm_num)
theorem B2072789 : Blo 920579 2072789 := bbase (se 7 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 2072789 = 48581) (by norm_num)
theorem B1384661 : Blo 920579 1384661 := bbase (se 7 (by rfl) ⟨16226, by rfl⟩ : syracuseStep 1384661 = 32453) (by norm_num)
theorem B1384685 : Blo 920579 1384685 := bbase (se 3 (by rfl) ⟨259628, by rfl⟩ : syracuseStep 1384685 = 519257) (by norm_num)
theorem B1384709 : Blo 920579 1384709 := bbase (se 4 (by rfl) ⟨129816, by rfl⟩ : syracuseStep 1384709 = 259633) (by norm_num)
theorem B2072861 : Blo 920579 2072861 := bbase (se 3 (by rfl) ⟨388661, by rfl⟩ : syracuseStep 2072861 = 777323) (by norm_num)
theorem B1384733 : Blo 920579 1384733 := bbase (se 3 (by rfl) ⟨259637, by rfl⟩ : syracuseStep 1384733 = 519275) (by norm_num)
theorem B1384757 : Blo 920579 1384757 := bbase (se 5 (by rfl) ⟨64910, by rfl⟩ : syracuseStep 1384757 = 129821) (by norm_num)
theorem B1384781 : Blo 920579 1384781 := bbase (se 3 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 1384781 = 519293) (by norm_num)
theorem B2072933 : Blo 920579 2072933 := bbase (se 4 (by rfl) ⟨194337, by rfl⟩ : syracuseStep 2072933 = 388675) (by norm_num)
theorem B1384805 : Blo 920579 1384805 := bbase (se 4 (by rfl) ⟨129825, by rfl⟩ : syracuseStep 1384805 = 259651) (by norm_num)
theorem B1122665 : Blo 920579 1122665 := bbase (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) (by norm_num)
theorem B1384829 : Blo 920579 1384829 := bbase (se 3 (by rfl) ⟨259655, by rfl⟩ : syracuseStep 1384829 = 519311) (by norm_num)
theorem B1384853 : Blo 920579 1384853 := bbase (se 6 (by rfl) ⟨32457, by rfl⟩ : syracuseStep 1384853 = 64915) (by norm_num)
theorem B2073005 : Blo 920579 2073005 := bbase (se 3 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 2073005 = 777377) (by norm_num)
theorem B1384877 : Blo 920579 1384877 := bbase (se 3 (by rfl) ⟨259664, by rfl⟩ : syracuseStep 1384877 = 519329) (by norm_num)
theorem B3154373 : Blo 920579 3154373 := bbase (se 4 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 3154373 = 591445) (by norm_num)
theorem B1384901 : Blo 920579 1384901 := bbase (se 4 (by rfl) ⟨129834, by rfl⟩ : syracuseStep 1384901 = 259669) (by norm_num)
theorem B2335189 : Blo 920579 2335189 := bbase (se 7 (by rfl) ⟨27365, by rfl⟩ : syracuseStep 2335189 = 54731) (by norm_num)
theorem B1384925 : Blo 920579 1384925 := bbase (se 3 (by rfl) ⟨259673, by rfl⟩ : syracuseStep 1384925 = 519347) (by norm_num)
theorem B2073077 : Blo 920579 2073077 := bbase (se 5 (by rfl) ⟨97175, by rfl⟩ : syracuseStep 2073077 = 194351) (by norm_num)
theorem B1384949 : Blo 920579 1384949 := bbase (se 5 (by rfl) ⟨64919, by rfl⟩ : syracuseStep 1384949 = 129839) (by norm_num)
theorem B1384973 : Blo 920579 1384973 := bbase (se 3 (by rfl) ⟨259682, by rfl⟩ : syracuseStep 1384973 = 519365) (by norm_num)
theorem B1384997 : Blo 920579 1384997 := bbase (se 4 (by rfl) ⟨129843, by rfl⟩ : syracuseStep 1384997 = 259687) (by norm_num)
theorem B2073149 : Blo 920579 2073149 := bbase (se 3 (by rfl) ⟨388715, by rfl⟩ : syracuseStep 2073149 = 777431) (by norm_num)
theorem B1385021 : Blo 920579 1385021 := bbase (se 3 (by rfl) ⟨259691, by rfl⟩ : syracuseStep 1385021 = 519383) (by norm_num)
theorem B2335301 : Blo 920579 2335301 := bbase (se 4 (by rfl) ⟨218934, by rfl⟩ : syracuseStep 2335301 = 437869) (by norm_num)
theorem B1385045 : Blo 920579 1385045 := bbase (se 8 (by rfl) ⟨8115, by rfl⟩ : syracuseStep 1385045 = 16231) (by norm_num)
theorem B1385069 : Blo 920579 1385069 := bbase (se 3 (by rfl) ⟨259700, by rfl⟩ : syracuseStep 1385069 = 519401) (by norm_num)
theorem B2073221 : Blo 920579 2073221 := bbase (se 4 (by rfl) ⟨194364, by rfl⟩ : syracuseStep 2073221 = 388729) (by norm_num)
theorem B1385093 : Blo 920579 1385093 := bbase (se 4 (by rfl) ⟨129852, by rfl⟩ : syracuseStep 1385093 = 259705) (by norm_num)
theorem B1385117 : Blo 920579 1385117 := bbase (se 3 (by rfl) ⟨259709, by rfl⟩ : syracuseStep 1385117 = 519419) (by norm_num)
theorem B1385141 : Blo 920579 1385141 := bbase (se 5 (by rfl) ⟨64928, by rfl⟩ : syracuseStep 1385141 = 129857) (by norm_num)
theorem B2073293 : Blo 920579 2073293 := bbase (se 3 (by rfl) ⟨388742, by rfl⟩ : syracuseStep 2073293 = 777485) (by norm_num)
theorem B1385165 : Blo 920579 1385165 := bbase (se 3 (by rfl) ⟨259718, by rfl⟩ : syracuseStep 1385165 = 519437) (by norm_num)
theorem B1385189 : Blo 920579 1385189 := bbase (se 4 (by rfl) ⟨129861, by rfl⟩ : syracuseStep 1385189 = 259723) (by norm_num)
theorem B1385213 : Blo 920579 1385213 := bbase (se 3 (by rfl) ⟨259727, by rfl⟩ : syracuseStep 1385213 = 519455) (by norm_num)
theorem B2335493 : Blo 920579 2335493 := bbase (se 4 (by rfl) ⟨218952, by rfl⟩ : syracuseStep 2335493 = 437905) (by norm_num)
theorem B2073365 : Blo 920579 2073365 := bbase (se 6 (by rfl) ⟨48594, by rfl⟩ : syracuseStep 2073365 = 97189) (by norm_num)
theorem B1385237 : Blo 920579 1385237 := bbase (se 6 (by rfl) ⟨32466, by rfl⟩ : syracuseStep 1385237 = 64933) (by norm_num)
theorem B1385261 : Blo 920579 1385261 := bbase (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) (by norm_num)
theorem B1385285 : Blo 920579 1385285 := bbase (se 4 (by rfl) ⟨129870, by rfl⟩ : syracuseStep 1385285 = 259741) (by norm_num)
theorem B2073437 : Blo 920579 2073437 := bbase (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) (by norm_num)
theorem B1385309 : Blo 920579 1385309 := bbase (se 3 (by rfl) ⟨259745, by rfl⟩ : syracuseStep 1385309 = 519491) (by norm_num)
theorem B1385333 : Blo 920579 1385333 := bbase (se 5 (by rfl) ⟨64937, by rfl⟩ : syracuseStep 1385333 = 129875) (by norm_num)
theorem B1385357 : Blo 920579 1385357 := bbase (se 3 (by rfl) ⟨259754, by rfl⟩ : syracuseStep 1385357 = 519509) (by norm_num)
theorem B2073509 : Blo 920579 2073509 := bbase (se 4 (by rfl) ⟨194391, by rfl⟩ : syracuseStep 2073509 = 388783) (by norm_num)
theorem B1385381 : Blo 920579 1385381 := bbase (se 4 (by rfl) ⟨129879, by rfl⟩ : syracuseStep 1385381 = 259759) (by norm_num)
theorem B4662197 : Blo 920579 4662197 := bbase (se 5 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 4662197 = 437081) (by norm_num)
theorem B1385405 : Blo 920579 1385405 := bbase (se 3 (by rfl) ⟨259763, by rfl⟩ : syracuseStep 1385405 = 519527) (by norm_num)
theorem B1385429 : Blo 920579 1385429 := bbase (se 7 (by rfl) ⟨16235, by rfl⟩ : syracuseStep 1385429 = 32471) (by norm_num)
theorem B2073581 : Blo 920579 2073581 := bbase (se 3 (by rfl) ⟨388796, by rfl⟩ : syracuseStep 2073581 = 777593) (by norm_num)
theorem B1385453 : Blo 920579 1385453 := bbase (se 3 (by rfl) ⟨259772, by rfl⟩ : syracuseStep 1385453 = 519545) (by norm_num)
theorem B1385477 : Blo 920579 1385477 := bbase (se 4 (by rfl) ⟨129888, by rfl⟩ : syracuseStep 1385477 = 259777) (by norm_num)
theorem B2630677 : Blo 920579 2630677 := bbase (se 6 (by rfl) ⟨61656, by rfl⟩ : syracuseStep 2630677 = 123313) (by norm_num)
theorem B1385501 : Blo 920579 1385501 := bbase (se 3 (by rfl) ⟨259781, by rfl⟩ : syracuseStep 1385501 = 519563) (by norm_num)
theorem B2073653 : Blo 920579 2073653 := bbase (se 5 (by rfl) ⟨97202, by rfl⟩ : syracuseStep 2073653 = 194405) (by norm_num)
theorem B1385525 : Blo 920579 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B1385549 : Blo 920579 1385549 := bbase (se 3 (by rfl) ⟨259790, by rfl⟩ : syracuseStep 1385549 = 519581) (by norm_num)
theorem B4432981 : Blo 920579 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B2335837 : Blo 920579 2335837 := bbase (se 3 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 2335837 = 875939) (by norm_num)
theorem B1385573 : Blo 920579 1385573 := bbase (se 4 (by rfl) ⟨129897, by rfl⟩ : syracuseStep 1385573 = 259795) (by norm_num)
theorem B6661237 : Blo 920579 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B2073725 : Blo 920579 2073725 := bbase (se 3 (by rfl) ⟨388823, by rfl⟩ : syracuseStep 2073725 = 777647) (by norm_num)
theorem B1385597 : Blo 920579 1385597 := bbase (se 3 (by rfl) ⟨259799, by rfl⟩ : syracuseStep 1385597 = 519599) (by norm_num)
theorem B1385621 : Blo 920579 1385621 := bbase (se 6 (by rfl) ⟨32475, by rfl⟩ : syracuseStep 1385621 = 64951) (by norm_num)
theorem B1385645 : Blo 920579 1385645 := bbase (se 3 (by rfl) ⟨259808, by rfl⟩ : syracuseStep 1385645 = 519617) (by norm_num)
theorem B1778861 : Blo 920579 1778861 := bbase (se 3 (by rfl) ⟨333536, by rfl⟩ : syracuseStep 1778861 = 667073) (by norm_num)
theorem B2368693 : Blo 920579 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B2106557 : Blo 920579 2106557 := bbase (se 3 (by rfl) ⟨394979, by rfl⟩ : syracuseStep 2106557 = 789959) (by norm_num)
theorem B2073797 : Blo 920579 2073797 := bbase (se 4 (by rfl) ⟨194418, by rfl⟩ : syracuseStep 2073797 = 388837) (by norm_num)
theorem B1385669 : Blo 920579 1385669 := bbase (se 4 (by rfl) ⟨129906, by rfl⟩ : syracuseStep 1385669 = 259813) (by norm_num)
theorem B2335949 : Blo 920579 2335949 := bbase (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) (by norm_num)
theorem B5252309 : Blo 920579 5252309 := bbase (se 7 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 5252309 = 123101) (by norm_num)
theorem B1385693 : Blo 920579 1385693 := bbase (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) (by norm_num)
theorem B1385717 : Blo 920579 1385717 := bbase (se 5 (by rfl) ⟨64955, by rfl⟩ : syracuseStep 1385717 = 129911) (by norm_num)
theorem B2073869 : Blo 920579 2073869 := bbase (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) (by norm_num)
theorem B1385741 : Blo 920579 1385741 := bbase (se 3 (by rfl) ⟨259826, by rfl⟩ : syracuseStep 1385741 = 519653) (by norm_num)
theorem B1385765 : Blo 920579 1385765 := bbase (se 4 (by rfl) ⟨129915, by rfl⟩ : syracuseStep 1385765 = 259831) (by norm_num)
theorem B1385789 : Blo 920579 1385789 := bbase (se 3 (by rfl) ⟨259835, by rfl⟩ : syracuseStep 1385789 = 519671) (by norm_num)
theorem B2073941 : Blo 920579 2073941 := bbase (se 12 (by rfl) ⟨759, by rfl⟩ : syracuseStep 2073941 = 1519) (by norm_num)
theorem B1385813 : Blo 920579 1385813 := bbase (se 12 (by rfl) ⟨507, by rfl⟩ : syracuseStep 1385813 = 1015) (by norm_num)
theorem B1385837 : Blo 920579 1385837 := bbase (se 3 (by rfl) ⟨259844, by rfl⟩ : syracuseStep 1385837 = 519689) (by norm_num)
theorem B1385861 : Blo 920579 1385861 := bbase (se 4 (by rfl) ⟨129924, by rfl⟩ : syracuseStep 1385861 = 259849) (by norm_num)
theorem B2336141 : Blo 920579 2336141 := bbase (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) (by norm_num)
theorem B2074013 : Blo 920579 2074013 := bbase (se 3 (by rfl) ⟨388877, by rfl⟩ : syracuseStep 2074013 = 777755) (by norm_num)
theorem B1385885 : Blo 920579 1385885 := bbase (se 3 (by rfl) ⟨259853, by rfl⟩ : syracuseStep 1385885 = 519707) (by norm_num)
theorem B1385909 : Blo 920579 1385909 := bbase (se 5 (by rfl) ⟨64964, by rfl⟩ : syracuseStep 1385909 = 129929) (by norm_num)
theorem B1385933 : Blo 920579 1385933 := bbase (se 3 (by rfl) ⟨259862, by rfl⟩ : syracuseStep 1385933 = 519725) (by norm_num)
theorem B2074085 : Blo 920579 2074085 := bbase (se 4 (by rfl) ⟨194445, by rfl⟩ : syracuseStep 2074085 = 388891) (by norm_num)
theorem B1385957 : Blo 920579 1385957 := bbase (se 4 (by rfl) ⟨129933, by rfl⟩ : syracuseStep 1385957 = 259867) (by norm_num)
theorem B1385981 : Blo 920579 1385981 := bbase (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) (by norm_num)
theorem B1386005 : Blo 920579 1386005 := bbase (se 6 (by rfl) ⟨32484, by rfl⟩ : syracuseStep 1386005 = 64969) (by norm_num)
theorem B2074157 : Blo 920579 2074157 := bbase (se 3 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 2074157 = 777809) (by norm_num)
theorem B1386029 : Blo 920579 1386029 := bbase (se 3 (by rfl) ⟨259880, by rfl⟩ : syracuseStep 1386029 = 519761) (by norm_num)
theorem B1386053 : Blo 920579 1386053 := bbase (se 4 (by rfl) ⟨129942, by rfl⟩ : syracuseStep 1386053 = 259885) (by norm_num)
theorem B1386077 : Blo 920579 1386077 := bbase (se 3 (by rfl) ⟨259889, by rfl⟩ : syracuseStep 1386077 = 519779) (by norm_num)
theorem B2074229 : Blo 920579 2074229 := bbase (se 5 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 2074229 = 194459) (by norm_num)
theorem B1386101 : Blo 920579 1386101 := bbase (se 5 (by rfl) ⟨64973, by rfl⟩ : syracuseStep 1386101 = 129947) (by norm_num)
theorem B1386125 : Blo 920579 1386125 := bbase (se 3 (by rfl) ⟨259898, by rfl⟩ : syracuseStep 1386125 = 519797) (by norm_num)
theorem B3942053 : Blo 920579 3942053 := bbase (se 4 (by rfl) ⟨369567, by rfl⟩ : syracuseStep 3942053 = 739135) (by norm_num)
theorem B1386149 : Blo 920579 1386149 := bbase (se 4 (by rfl) ⟨129951, by rfl⟩ : syracuseStep 1386149 = 259903) (by norm_num)
theorem B2074301 : Blo 920579 2074301 := bbase (se 3 (by rfl) ⟨388931, by rfl⟩ : syracuseStep 2074301 = 777863) (by norm_num)
theorem B1386173 : Blo 920579 1386173 := bbase (se 3 (by rfl) ⟨259907, by rfl⟩ : syracuseStep 1386173 = 519815) (by norm_num)
theorem B1386197 : Blo 920579 1386197 := bbase (se 7 (by rfl) ⟨16244, by rfl⟩ : syracuseStep 1386197 = 32489) (by norm_num)
theorem B2336485 : Blo 920579 2336485 := bbase (se 4 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 2336485 = 438091) (by norm_num)
theorem B1386221 : Blo 920579 1386221 := bbase (se 3 (by rfl) ⟨259916, by rfl⟩ : syracuseStep 1386221 = 519833) (by norm_num)
theorem B7874293 : Blo 920579 7874293 := bbase (se 5 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 7874293 = 738215) (by norm_num)
theorem B2074373 : Blo 920579 2074373 := bbase (se 4 (by rfl) ⟨194472, by rfl⟩ : syracuseStep 2074373 = 388945) (by norm_num)
theorem B1386245 : Blo 920579 1386245 := bbase (se 4 (by rfl) ⟨129960, by rfl⟩ : syracuseStep 1386245 = 259921) (by norm_num)
theorem B1386269 : Blo 920579 1386269 := bbase (se 3 (by rfl) ⟨259925, by rfl⟩ : syracuseStep 1386269 = 519851) (by norm_num)
theorem B1386293 : Blo 920579 1386293 := bbase (se 5 (by rfl) ⟨64982, by rfl⟩ : syracuseStep 1386293 = 129965) (by norm_num)
theorem B2074445 : Blo 920579 2074445 := bbase (se 3 (by rfl) ⟨388958, by rfl⟩ : syracuseStep 2074445 = 777917) (by norm_num)
theorem B1386317 : Blo 920579 1386317 := bbase (se 3 (by rfl) ⟨259934, by rfl⟩ : syracuseStep 1386317 = 519869) (by norm_num)
theorem B2336597 : Blo 920579 2336597 := bbase (se 9 (by rfl) ⟨6845, by rfl⟩ : syracuseStep 2336597 = 13691) (by norm_num)
theorem B1386341 : Blo 920579 1386341 := bbase (se 4 (by rfl) ⟨129969, by rfl⟩ : syracuseStep 1386341 = 259939) (by norm_num)
theorem B1386365 : Blo 920579 1386365 := bbase (se 3 (by rfl) ⟨259943, by rfl⟩ : syracuseStep 1386365 = 519887) (by norm_num)
theorem B2074517 : Blo 920579 2074517 := bbase (se 6 (by rfl) ⟨48621, by rfl⟩ : syracuseStep 2074517 = 97243) (by norm_num)
theorem B1386389 : Blo 920579 1386389 := bbase (se 6 (by rfl) ⟨32493, by rfl⟩ : syracuseStep 1386389 = 64987) (by norm_num)
theorem B1386413 : Blo 920579 1386413 := bbase (se 3 (by rfl) ⟨259952, by rfl⟩ : syracuseStep 1386413 = 519905) (by norm_num)
theorem B3942341 : Blo 920579 3942341 := bbase (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) (by norm_num)
theorem B1386437 : Blo 920579 1386437 := bbase (se 4 (by rfl) ⟨129978, by rfl⟩ : syracuseStep 1386437 = 259957) (by norm_num)
theorem B2074589 : Blo 920579 2074589 := bbase (se 3 (by rfl) ⟨388985, by rfl⟩ : syracuseStep 2074589 = 777971) (by norm_num)
theorem B1386461 : Blo 920579 1386461 := bbase (se 3 (by rfl) ⟨259961, by rfl⟩ : syracuseStep 1386461 = 519923) (by norm_num)
theorem B1386485 : Blo 920579 1386485 := bbase (se 5 (by rfl) ⟨64991, by rfl⟩ : syracuseStep 1386485 = 129983) (by norm_num)
theorem B1386509 : Blo 920579 1386509 := bbase (se 3 (by rfl) ⟨259970, by rfl⟩ : syracuseStep 1386509 = 519941) (by norm_num)
theorem B2336789 : Blo 920579 2336789 := bbase (se 6 (by rfl) ⟨54768, by rfl⟩ : syracuseStep 2336789 = 109537) (by norm_num)
theorem B2074661 : Blo 920579 2074661 := bbase (se 4 (by rfl) ⟨194499, by rfl⟩ : syracuseStep 2074661 = 388999) (by norm_num)
theorem B1386533 : Blo 920579 1386533 := bbase (se 4 (by rfl) ⟨129987, by rfl⟩ : syracuseStep 1386533 = 259975) (by norm_num)
theorem B1386557 : Blo 920579 1386557 := bbase (se 3 (by rfl) ⟨259979, by rfl⟩ : syracuseStep 1386557 = 519959) (by norm_num)
theorem B1386581 : Blo 920579 1386581 := bbase (se 8 (by rfl) ⟨8124, by rfl⟩ : syracuseStep 1386581 = 16249) (by norm_num)
theorem B2631781 : Blo 920579 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B2074733 : Blo 920579 2074733 := bbase (se 3 (by rfl) ⟨389012, by rfl⟩ : syracuseStep 2074733 = 778025) (by norm_num)
theorem B1386605 : Blo 920579 1386605 := bbase (se 3 (by rfl) ⟨259988, by rfl⟩ : syracuseStep 1386605 = 519977) (by norm_num)
theorem B1386629 : Blo 920579 1386629 := bbase (se 4 (by rfl) ⟨129996, by rfl⟩ : syracuseStep 1386629 = 259993) (by norm_num)
theorem B1386653 : Blo 920579 1386653 := bbase (se 3 (by rfl) ⟨259997, by rfl⟩ : syracuseStep 1386653 = 519995) (by norm_num)
theorem B2074805 : Blo 920579 2074805 := bbase (se 5 (by rfl) ⟨97256, by rfl⟩ : syracuseStep 2074805 = 194513) (by norm_num)
theorem B3745973 : Blo 920579 3745973 := bbase (se 5 (by rfl) ⟨175592, by rfl⟩ : syracuseStep 3745973 = 351185) (by norm_num)
theorem B1386677 : Blo 920579 1386677 := bbase (se 5 (by rfl) ⟨65000, by rfl⟩ : syracuseStep 1386677 = 130001) (by norm_num)
theorem B4663493 : Blo 920579 4663493 := bbase (se 4 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 4663493 = 874405) (by norm_num)
theorem B1386701 : Blo 920579 1386701 := bbase (se 3 (by rfl) ⟨260006, by rfl⟩ : syracuseStep 1386701 = 520013) (by norm_num)
theorem B1386725 : Blo 920579 1386725 := bbase (se 4 (by rfl) ⟨130005, by rfl⟩ : syracuseStep 1386725 = 260011) (by norm_num)
theorem B2074877 : Blo 920579 2074877 := bbase (se 3 (by rfl) ⟨389039, by rfl⟩ : syracuseStep 2074877 = 778079) (by norm_num)
theorem B1386749 : Blo 920579 1386749 := bbase (se 3 (by rfl) ⟨260015, by rfl⟩ : syracuseStep 1386749 = 520031) (by norm_num)
theorem B1386773 : Blo 920579 1386773 := bbase (se 6 (by rfl) ⟨32502, by rfl⟩ : syracuseStep 1386773 = 65005) (by norm_num)
theorem B1386797 : Blo 920579 1386797 := bbase (se 3 (by rfl) ⟨260024, by rfl⟩ : syracuseStep 1386797 = 520049) (by norm_num)
theorem B2074949 : Blo 920579 2074949 := bbase (se 4 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 2074949 = 389053) (by norm_num)
theorem B1386821 : Blo 920579 1386821 := bbase (se 4 (by rfl) ⟨130014, by rfl⟩ : syracuseStep 1386821 = 260029) (by norm_num)
theorem B1386845 : Blo 920579 1386845 := bbase (se 3 (by rfl) ⟨260033, by rfl⟩ : syracuseStep 1386845 = 520067) (by norm_num)
theorem B2337133 : Blo 920579 2337133 := bbase (se 3 (by rfl) ⟨438212, by rfl⟩ : syracuseStep 2337133 = 876425) (by norm_num)
theorem B1386869 : Blo 920579 1386869 := bbase (se 5 (by rfl) ⟨65009, by rfl⟩ : syracuseStep 1386869 = 130019) (by norm_num)
theorem B2075021 : Blo 920579 2075021 := bbase (se 3 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 2075021 = 778133) (by norm_num)
theorem B12954005 : Blo 920579 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B2075093 : Blo 920579 2075093 := bbase (se 7 (by rfl) ⟨24317, by rfl⟩ : syracuseStep 2075093 = 48635) (by norm_num)
theorem B2337245 : Blo 920579 2337245 := bbase (se 3 (by rfl) ⟨438233, by rfl⟩ : syracuseStep 2337245 = 876467) (by norm_num)
theorem B2075165 : Blo 920579 2075165 := bbase (se 3 (by rfl) ⟨389093, by rfl⟩ : syracuseStep 2075165 = 778187) (by norm_num)
theorem B1682005 : Blo 920579 1682005 := bbase (se 8 (by rfl) ⟨9855, by rfl⟩ : syracuseStep 1682005 = 19711) (by norm_num)
theorem B2075237 : Blo 920579 2075237 := bbase (se 4 (by rfl) ⟨194553, by rfl⟩ : syracuseStep 2075237 = 389107) (by norm_num)
theorem B2337437 : Blo 920579 2337437 := bbase (se 3 (by rfl) ⟨438269, by rfl⟩ : syracuseStep 2337437 = 876539) (by norm_num)
theorem B2075309 : Blo 920579 2075309 := bbase (se 3 (by rfl) ⟨389120, by rfl⟩ : syracuseStep 2075309 = 778241) (by norm_num)
theorem B3943093 : Blo 920579 3943093 := bbase (se 5 (by rfl) ⟨184832, by rfl⟩ : syracuseStep 3943093 = 369665) (by norm_num)
theorem B2075381 : Blo 920579 2075381 := bbase (se 5 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 2075381 = 194567) (by norm_num)
theorem B2960165 : Blo 920579 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B2075453 : Blo 920579 2075453 := bbase (se 3 (by rfl) ⟨389147, by rfl⟩ : syracuseStep 2075453 = 778295) (by norm_num)
theorem B2075525 : Blo 920579 2075525 := bbase (se 4 (by rfl) ⟨194580, by rfl⟩ : syracuseStep 2075525 = 389161) (by norm_num)
theorem B2075597 : Blo 920579 2075597 := bbase (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) (by norm_num)
theorem B2370541 : Blo 920579 2370541 := bbase (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) (by norm_num)
theorem B2337781 : Blo 920579 2337781 := bbase (se 5 (by rfl) ⟨109583, by rfl⟩ : syracuseStep 2337781 = 219167) (by norm_num)
theorem B2075669 : Blo 920579 2075669 := bbase (se 6 (by rfl) ⟨48648, by rfl⟩ : syracuseStep 2075669 = 97297) (by norm_num)
theorem B2075741 : Blo 920579 2075741 := bbase (se 3 (by rfl) ⟨389201, by rfl⟩ : syracuseStep 2075741 = 778403) (by norm_num)
theorem B2337893 : Blo 920579 2337893 := bbase (se 4 (by rfl) ⟨219177, by rfl⟩ : syracuseStep 2337893 = 438355) (by norm_num)
theorem B3124373 : Blo 920579 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B2075813 : Blo 920579 2075813 := bbase (se 4 (by rfl) ⟨194607, by rfl⟩ : syracuseStep 2075813 = 389215) (by norm_num)
theorem B2075885 : Blo 920579 2075885 := bbase (se 3 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 2075885 = 778457) (by norm_num)
theorem B2338085 : Blo 920579 2338085 := bbase (se 4 (by rfl) ⟨219195, by rfl⟩ : syracuseStep 2338085 = 438391) (by norm_num)
theorem B2075957 : Blo 920579 2075957 := bbase (se 5 (by rfl) ⟨97310, by rfl⟩ : syracuseStep 2075957 = 194621) (by norm_num)
theorem B1748317 : Blo 920579 1748317 := bbase (se 3 (by rfl) ⟨327809, by rfl⟩ : syracuseStep 1748317 = 655619) (by norm_num)
theorem B2076029 : Blo 920579 2076029 := bbase (se 3 (by rfl) ⟨389255, by rfl⟩ : syracuseStep 2076029 = 778511) (by norm_num)
theorem B3943829 : Blo 920579 3943829 := bbase (se 6 (by rfl) ⟨92433, by rfl⟩ : syracuseStep 3943829 = 184867) (by norm_num)
theorem B2076101 : Blo 920579 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B4664789 : Blo 920579 4664789 := bbase (se 7 (by rfl) ⟨54665, by rfl⟩ : syracuseStep 4664789 = 109331) (by norm_num)
theorem B1748461 : Blo 920579 1748461 := bbase (se 3 (by rfl) ⟨327836, by rfl⟩ : syracuseStep 1748461 = 655673) (by norm_num)
theorem B2076173 : Blo 920579 2076173 := bbase (se 3 (by rfl) ⟨389282, by rfl⟩ : syracuseStep 2076173 = 778565) (by norm_num)
theorem B2076245 : Blo 920579 2076245 := bbase (se 8 (by rfl) ⟨12165, by rfl⟩ : syracuseStep 2076245 = 24331) (by norm_num)
theorem B2338429 : Blo 920579 2338429 := bbase (se 3 (by rfl) ⟨438455, by rfl⟩ : syracuseStep 2338429 = 876911) (by norm_num)
theorem B1748621 : Blo 920579 1748621 := bbase (se 3 (by rfl) ⟨327866, by rfl⟩ : syracuseStep 1748621 = 655733) (by norm_num)
theorem B2076317 : Blo 920579 2076317 := bbase (se 3 (by rfl) ⟨389309, by rfl⟩ : syracuseStep 2076317 = 778619) (by norm_num)
theorem B7876277 : Blo 920579 7876277 := bbase (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) (by norm_num)
theorem B2076389 : Blo 920579 2076389 := bbase (se 4 (by rfl) ⟨194661, by rfl⟩ : syracuseStep 2076389 = 389323) (by norm_num)
theorem B2338541 : Blo 920579 2338541 := bbase (se 3 (by rfl) ⟨438476, by rfl⟩ : syracuseStep 2338541 = 876953) (by norm_num)
theorem B1748765 : Blo 920579 1748765 := bbase (se 3 (by rfl) ⟨327893, by rfl⟩ : syracuseStep 1748765 = 655787) (by norm_num)
theorem B2305837 : Blo 920579 2305837 := bbase (se 3 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 2305837 = 864689) (by norm_num)
theorem B2076461 : Blo 920579 2076461 := bbase (se 3 (by rfl) ⟨389336, by rfl⟩ : syracuseStep 2076461 = 778673) (by norm_num)
theorem B2076533 : Blo 920579 2076533 := bbase (se 5 (by rfl) ⟨97337, by rfl⟩ : syracuseStep 2076533 = 194675) (by norm_num)
theorem B4435829 : Blo 920579 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B2338733 : Blo 920579 2338733 := bbase (se 3 (by rfl) ⟨438512, by rfl⟩ : syracuseStep 2338733 = 877025) (by norm_num)
theorem B2076605 : Blo 920579 2076605 := bbase (se 3 (by rfl) ⟨389363, by rfl⟩ : syracuseStep 2076605 = 778727) (by norm_num)
theorem B2076677 : Blo 920579 2076677 := bbase (se 4 (by rfl) ⟨194688, by rfl⟩ : syracuseStep 2076677 = 389377) (by norm_num)
theorem B2961461 : Blo 920579 2961461 := bbase (se 5 (by rfl) ⟨138818, by rfl⟩ : syracuseStep 2961461 = 277637) (by norm_num)
theorem B1749053 : Blo 920579 1749053 := bbase (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) (by norm_num)
theorem B2076749 : Blo 920579 2076749 := bbase (se 3 (by rfl) ⟨389390, by rfl⟩ : syracuseStep 2076749 = 778781) (by norm_num)
theorem B2076821 : Blo 920579 2076821 := bbase (se 6 (by rfl) ⟨48675, by rfl⟩ : syracuseStep 2076821 = 97351) (by norm_num)
theorem B1749205 : Blo 920579 1749205 := bbase (se 7 (by rfl) ⟨20498, by rfl⟩ : syracuseStep 1749205 = 40997) (by norm_num)
theorem B2076893 : Blo 920579 2076893 := bbase (se 3 (by rfl) ⟨389417, by rfl⟩ : syracuseStep 2076893 = 778835) (by norm_num)
theorem B2339077 : Blo 920579 2339077 := bbase (se 4 (by rfl) ⟨219288, by rfl⟩ : syracuseStep 2339077 = 438577) (by norm_num)
theorem B2371853 : Blo 920579 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B2076965 : Blo 920579 2076965 := bbase (se 4 (by rfl) ⟨194715, by rfl⟩ : syracuseStep 2076965 = 389431) (by norm_num)
theorem B2077037 : Blo 920579 2077037 := bbase (se 3 (by rfl) ⟨389444, by rfl⟩ : syracuseStep 2077037 = 778889) (by norm_num)
theorem B2339189 : Blo 920579 2339189 := bbase (se 5 (by rfl) ⟨109649, by rfl⟩ : syracuseStep 2339189 = 219299) (by norm_num)
theorem B2077109 : Blo 920579 2077109 := bbase (se 5 (by rfl) ⟨97364, by rfl⟩ : syracuseStep 2077109 = 194729) (by norm_num)
theorem B2077181 : Blo 920579 2077181 := bbase (se 3 (by rfl) ⟨389471, by rfl⟩ : syracuseStep 2077181 = 778943) (by norm_num)
theorem B1749509 : Blo 920579 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B2339381 : Blo 920579 2339381 := bbase (se 5 (by rfl) ⟨109658, by rfl⟩ : syracuseStep 2339381 = 219317) (by norm_num)
theorem B2077253 : Blo 920579 2077253 := bbase (se 4 (by rfl) ⟨194742, by rfl⟩ : syracuseStep 2077253 = 389485) (by norm_num)
theorem B2077325 : Blo 920579 2077325 := bbase (se 3 (by rfl) ⟨389498, by rfl⟩ : syracuseStep 2077325 = 778997) (by norm_num)
theorem B4207285 : Blo 920579 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B2077397 : Blo 920579 2077397 := bbase (se 7 (by rfl) ⟨24344, by rfl⟩ : syracuseStep 2077397 = 48689) (by norm_num)
theorem B4666085 : Blo 920579 4666085 := bbase (se 4 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 4666085 = 874891) (by norm_num)
theorem B13316885 : Blo 920579 13316885 := bbase (se 6 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 13316885 = 624229) (by norm_num)
theorem B2077469 : Blo 920579 2077469 := bbase (se 3 (by rfl) ⟨389525, by rfl⟩ : syracuseStep 2077469 = 779051) (by norm_num)
theorem B2077541 : Blo 920579 2077541 := bbase (se 4 (by rfl) ⟨194769, by rfl⟩ : syracuseStep 2077541 = 389539) (by norm_num)
theorem B2339725 : Blo 920579 2339725 := bbase (se 3 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 2339725 = 877397) (by norm_num)
theorem B2077613 : Blo 920579 2077613 := bbase (se 3 (by rfl) ⟨389552, by rfl⟩ : syracuseStep 2077613 = 779105) (by norm_num)
theorem B2077685 : Blo 920579 2077685 := bbase (se 5 (by rfl) ⟨97391, by rfl⟩ : syracuseStep 2077685 = 194783) (by norm_num)
theorem B2339837 : Blo 920579 2339837 := bbase (se 3 (by rfl) ⟨438719, by rfl⟩ : syracuseStep 2339837 = 877439) (by norm_num)
theorem B2077757 : Blo 920579 2077757 := bbase (se 3 (by rfl) ⟨389579, by rfl⟩ : syracuseStep 2077757 = 779159) (by norm_num)
theorem B1553485 : Blo 920579 1553485 := bbase (se 3 (by rfl) ⟨291278, by rfl⟩ : syracuseStep 1553485 = 582557) (by norm_num)
theorem B3847253 : Blo 920579 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B2077829 : Blo 920579 2077829 := bbase (se 4 (by rfl) ⟨194796, by rfl⟩ : syracuseStep 2077829 = 389593) (by norm_num)
theorem B1553573 : Blo 920579 1553573 := bbase (se 4 (by rfl) ⟨145647, by rfl⟩ : syracuseStep 1553573 = 291295) (by norm_num)
theorem B4437173 : Blo 920579 4437173 := bbase (se 5 (by rfl) ⟨207992, by rfl⟩ : syracuseStep 4437173 = 415985) (by norm_num)
theorem B2340029 : Blo 920579 2340029 := bbase (se 3 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 2340029 = 877511) (by norm_num)
theorem B2077901 : Blo 920579 2077901 := bbase (se 3 (by rfl) ⟨389606, by rfl⟩ : syracuseStep 2077901 = 779213) (by norm_num)
theorem B1750261 : Blo 920579 1750261 := bbase (se 5 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 1750261 = 164087) (by norm_num)
theorem B2077973 : Blo 920579 2077973 := bbase (se 6 (by rfl) ⟨48702, by rfl⟩ : syracuseStep 2077973 = 97405) (by norm_num)
theorem B1553701 : Blo 920579 1553701 := bbase (se 4 (by rfl) ⟨145659, by rfl⟩ : syracuseStep 1553701 = 291319) (by norm_num)
theorem B2078045 : Blo 920579 2078045 := bbase (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) (by norm_num)
theorem B1553789 : Blo 920579 1553789 := bbase (se 3 (by rfl) ⟨291335, by rfl⟩ : syracuseStep 1553789 = 582671) (by norm_num)
theorem B1750405 : Blo 920579 1750405 := bbase (se 4 (by rfl) ⟨164100, by rfl⟩ : syracuseStep 1750405 = 328201) (by norm_num)
theorem B2078117 : Blo 920579 2078117 := bbase (se 4 (by rfl) ⟨194823, by rfl⟩ : syracuseStep 2078117 = 389647) (by norm_num)
theorem B2078189 : Blo 920579 2078189 := bbase (se 3 (by rfl) ⟨389660, by rfl⟩ : syracuseStep 2078189 = 779321) (by norm_num)
theorem B1553917 : Blo 920579 1553917 := bbase (se 3 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 1553917 = 582719) (by norm_num)
theorem B1750565 : Blo 920579 1750565 := bbase (se 4 (by rfl) ⟨164115, by rfl⟩ : syracuseStep 1750565 = 328231) (by norm_num)
theorem B2078261 : Blo 920579 2078261 := bbase (se 5 (by rfl) ⟨97418, by rfl⟩ : syracuseStep 2078261 = 194837) (by norm_num)
theorem B1554005 : Blo 920579 1554005 := bbase (se 8 (by rfl) ⟨9105, by rfl⟩ : syracuseStep 1554005 = 18211) (by norm_num)
theorem B2078333 : Blo 920579 2078333 := bbase (se 3 (by rfl) ⟨389687, by rfl⟩ : syracuseStep 2078333 = 779375) (by norm_num)
theorem B1750709 : Blo 920579 1750709 := bbase (se 5 (by rfl) ⟨82064, by rfl⟩ : syracuseStep 1750709 = 164129) (by norm_num)
theorem B2078405 : Blo 920579 2078405 := bbase (se 4 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 2078405 = 389701) (by norm_num)
theorem B1554133 : Blo 920579 1554133 := bbase (se 7 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 1554133 = 36425) (by norm_num)
theorem B2078477 : Blo 920579 2078477 := bbase (se 3 (by rfl) ⟨389714, by rfl⟩ : syracuseStep 2078477 = 779429) (by norm_num)
theorem B1554221 : Blo 920579 1554221 := bbase (se 3 (by rfl) ⟨291416, by rfl⟩ : syracuseStep 1554221 = 582833) (by norm_num)
theorem B4208453 : Blo 920579 4208453 := bbase (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) (by norm_num)
theorem B2078549 : Blo 920579 2078549 := bbase (se 9 (by rfl) ⟨6089, by rfl⟩ : syracuseStep 2078549 = 12179) (by norm_num)
theorem B2078621 : Blo 920579 2078621 := bbase (se 3 (by rfl) ⟨389741, by rfl⟩ : syracuseStep 2078621 = 779483) (by norm_num)
theorem B3323813 : Blo 920579 3323813 := bbase (se 4 (by rfl) ⟨311607, by rfl⟩ : syracuseStep 3323813 = 623215) (by norm_num)
theorem B1554349 : Blo 920579 1554349 := bbase (se 3 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 1554349 = 582881) (by norm_num)
theorem B1750997 : Blo 920579 1750997 := bbase (se 7 (by rfl) ⟨20519, by rfl⟩ : syracuseStep 1750997 = 41039) (by norm_num)
theorem B2078693 : Blo 920579 2078693 := bbase (se 4 (by rfl) ⟨194877, by rfl⟩ : syracuseStep 2078693 = 389755) (by norm_num)
theorem B4667381 : Blo 920579 4667381 := bbase (se 5 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 4667381 = 437567) (by norm_num)
theorem B1554437 : Blo 920579 1554437 := bbase (se 4 (by rfl) ⟨145728, by rfl⟩ : syracuseStep 1554437 = 291457) (by norm_num)
theorem B2078765 : Blo 920579 2078765 := bbase (se 3 (by rfl) ⟨389768, by rfl⟩ : syracuseStep 2078765 = 779537) (by norm_num)
theorem B1751149 : Blo 920579 1751149 := bbase (se 3 (by rfl) ⟨328340, by rfl⟩ : syracuseStep 1751149 = 656681) (by norm_num)
theorem B2078837 : Blo 920579 2078837 := bbase (se 5 (by rfl) ⟨97445, by rfl⟩ : syracuseStep 2078837 = 194891) (by norm_num)
theorem B1554565 : Blo 920579 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B4274309 : Blo 920579 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B16824469 : Blo 920579 16824469 := bbase (se 6 (by rfl) ⟨394323, by rfl⟩ : syracuseStep 16824469 = 788647) (by norm_num)
theorem B2078909 : Blo 920579 2078909 := bbase (se 3 (by rfl) ⟨389795, by rfl⟩ : syracuseStep 2078909 = 779591) (by norm_num)
theorem B1554653 : Blo 920579 1554653 := bbase (se 3 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 1554653 = 582995) (by norm_num)
theorem B2078981 : Blo 920579 2078981 := bbase (se 4 (by rfl) ⟨194904, by rfl⟩ : syracuseStep 2078981 = 389809) (by norm_num)
theorem B2079053 : Blo 920579 2079053 := bbase (se 3 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 2079053 = 779645) (by norm_num)
theorem B1554781 : Blo 920579 1554781 := bbase (se 3 (by rfl) ⟨291521, by rfl⟩ : syracuseStep 1554781 = 583043) (by norm_num)
theorem B3160421 : Blo 920579 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B2079125 : Blo 920579 2079125 := bbase (se 6 (by rfl) ⟨48729, by rfl⟩ : syracuseStep 2079125 = 97459) (by norm_num)
theorem B1751453 : Blo 920579 1751453 := bbase (se 3 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 1751453 = 656795) (by norm_num)
theorem B1554869 : Blo 920579 1554869 := bbase (se 5 (by rfl) ⟨72884, by rfl⟩ : syracuseStep 1554869 = 145769) (by norm_num)
theorem B2079197 : Blo 920579 2079197 := bbase (se 3 (by rfl) ⟨389849, by rfl⟩ : syracuseStep 2079197 = 779699) (by norm_num)
theorem B2079269 : Blo 920579 2079269 := bbase (se 4 (by rfl) ⟨194931, by rfl⟩ : syracuseStep 2079269 = 389863) (by norm_num)
theorem B1554997 : Blo 920579 1554997 := bbase (se 5 (by rfl) ⟨72890, by rfl⟩ : syracuseStep 1554997 = 145781) (by norm_num)
theorem B1686101 : Blo 920579 1686101 := bbase (se 8 (by rfl) ⟨9879, by rfl⟩ : syracuseStep 1686101 = 19759) (by norm_num)
theorem B2079341 : Blo 920579 2079341 := bbase (se 3 (by rfl) ⟨389876, by rfl⟩ : syracuseStep 2079341 = 779753) (by norm_num)
theorem B3947125 : Blo 920579 3947125 := bbase (se 5 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 3947125 = 370043) (by norm_num)
theorem B1555085 : Blo 920579 1555085 := bbase (se 3 (by rfl) ⟨291578, by rfl⟩ : syracuseStep 1555085 = 583157) (by norm_num)
theorem B11844245 : Blo 920579 11844245 := bbase (se 6 (by rfl) ⟨277599, by rfl⟩ : syracuseStep 11844245 = 555199) (by norm_num)
theorem B7977653 : Blo 920579 7977653 := bbase (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) (by norm_num)
theorem B2079413 : Blo 920579 2079413 := bbase (se 5 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 2079413 = 194945) (by norm_num)
theorem B2079485 : Blo 920579 2079485 := bbase (se 3 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 2079485 = 779807) (by norm_num)
theorem B1555213 : Blo 920579 1555213 := bbase (se 3 (by rfl) ⟨291602, by rfl⟩ : syracuseStep 1555213 = 583205) (by norm_num)
theorem B2079557 : Blo 920579 2079557 := bbase (se 4 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 2079557 = 389917) (by norm_num)
theorem B1555301 : Blo 920579 1555301 := bbase (se 4 (by rfl) ⟨145809, by rfl⟩ : syracuseStep 1555301 = 291619) (by norm_num)
theorem B2079629 : Blo 920579 2079629 := bbase (se 3 (by rfl) ⟨389930, by rfl⟩ : syracuseStep 2079629 = 779861) (by norm_num)
theorem B2079701 : Blo 920579 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B1555429 : Blo 920579 1555429 := bbase (se 4 (by rfl) ⟨145821, by rfl⟩ : syracuseStep 1555429 = 291643) (by norm_num)
theorem B2079773 : Blo 920579 2079773 := bbase (se 3 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 2079773 = 779915) (by norm_num)
theorem B6994997 : Blo 920579 6994997 := bbase (se 5 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 6994997 = 655781) (by norm_num)
theorem B1555517 : Blo 920579 1555517 := bbase (se 3 (by rfl) ⟨291659, by rfl⟩ : syracuseStep 1555517 = 583319) (by norm_num)
theorem B2079845 : Blo 920579 2079845 := bbase (se 4 (by rfl) ⟨194985, by rfl⟩ : syracuseStep 2079845 = 389971) (by norm_num)
theorem B1752205 : Blo 920579 1752205 := bbase (se 3 (by rfl) ⟨328538, by rfl⟩ : syracuseStep 1752205 = 657077) (by norm_num)
theorem B2079917 : Blo 920579 2079917 := bbase (se 3 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 2079917 = 779969) (by norm_num)
theorem B1555645 : Blo 920579 1555645 := bbase (se 3 (by rfl) ⟨291683, by rfl⟩ : syracuseStep 1555645 = 583367) (by norm_num)
theorem B2079989 : Blo 920579 2079989 := bbase (se 5 (by rfl) ⟨97499, by rfl⟩ : syracuseStep 2079989 = 194999) (by norm_num)
theorem B4668677 : Blo 920579 4668677 := bbase (se 4 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 4668677 = 875377) (by norm_num)
theorem B1555733 : Blo 920579 1555733 := bbase (se 6 (by rfl) ⟨36462, by rfl⟩ : syracuseStep 1555733 = 72925) (by norm_num)
theorem B1752349 : Blo 920579 1752349 := bbase (se 3 (by rfl) ⟨328565, by rfl⟩ : syracuseStep 1752349 = 657131) (by norm_num)
theorem B2080061 : Blo 920579 2080061 := bbase (se 3 (by rfl) ⟨390011, by rfl⟩ : syracuseStep 2080061 = 780023) (by norm_num)
theorem B2080133 : Blo 920579 2080133 := bbase (se 4 (by rfl) ⟨195012, by rfl⟩ : syracuseStep 2080133 = 390025) (by norm_num)
theorem B1555861 : Blo 920579 1555861 := bbase (se 6 (by rfl) ⟨36465, by rfl⟩ : syracuseStep 1555861 = 72931) (by norm_num)
theorem B1752509 : Blo 920579 1752509 := bbase (se 3 (by rfl) ⟨328595, by rfl⟩ : syracuseStep 1752509 = 657191) (by norm_num)
theorem B2080205 : Blo 920579 2080205 := bbase (se 3 (by rfl) ⟨390038, by rfl⟩ : syracuseStep 2080205 = 780077) (by norm_num)
theorem B1555949 : Blo 920579 1555949 := bbase (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) (by norm_num)
theorem B2080277 : Blo 920579 2080277 := bbase (se 6 (by rfl) ⟨48756, by rfl⟩ : syracuseStep 2080277 = 97513) (by norm_num)
theorem B933445 : Blo 920579 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B1752653 : Blo 920579 1752653 := bbase (se 3 (by rfl) ⟨328622, by rfl⟩ : syracuseStep 1752653 = 657245) (by norm_num)
theorem B1556077 : Blo 920579 1556077 := bbase (se 3 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 1556077 = 583529) (by norm_num)
theorem B3325573 : Blo 920579 3325573 := bbase (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) (by norm_num)
theorem B1556165 : Blo 920579 1556165 := bbase (se 4 (by rfl) ⟨145890, by rfl⟩ : syracuseStep 1556165 = 291781) (by norm_num)
theorem B1556293 : Blo 920579 1556293 := bbase (se 4 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 1556293 = 291805) (by norm_num)
theorem B10501973 : Blo 920579 10501973 := bbase (se 9 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 10501973 = 61535) (by norm_num)
theorem B1752941 : Blo 920579 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B1556381 : Blo 920579 1556381 := bbase (se 3 (by rfl) ⟨291821, by rfl⟩ : syracuseStep 1556381 = 583643) (by norm_num)
theorem B1753093 : Blo 920579 1753093 := bbase (se 4 (by rfl) ⟨164352, by rfl⟩ : syracuseStep 1753093 = 328705) (by norm_num)
theorem B1556509 : Blo 920579 1556509 := bbase (se 3 (by rfl) ⟨291845, by rfl⟩ : syracuseStep 1556509 = 583691) (by norm_num)
theorem B1556597 : Blo 920579 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B1556725 : Blo 920579 1556725 := bbase (se 5 (by rfl) ⟨72971, by rfl⟩ : syracuseStep 1556725 = 145943) (by norm_num)
theorem B1753397 : Blo 920579 1753397 := bbase (se 5 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 1753397 = 164381) (by norm_num)
theorem B1556813 : Blo 920579 1556813 := bbase (se 3 (by rfl) ⟨291902, by rfl⟩ : syracuseStep 1556813 = 583805) (by norm_num)
theorem B999761 : Blo 920579 999761 := bbase (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) (by norm_num)
theorem B8864117 : Blo 920579 8864117 := bbase (se 5 (by rfl) ⟨415505, by rfl⟩ : syracuseStep 8864117 = 831011) (by norm_num)
theorem B1556941 : Blo 920579 1556941 := bbase (se 3 (by rfl) ⟨291926, by rfl⟩ : syracuseStep 1556941 = 583853) (by norm_num)
theorem B10961365 : Blo 920579 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B4669973 : Blo 920579 4669973 := bbase (se 6 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 4669973 = 218905) (by norm_num)
theorem B1557029 : Blo 920579 1557029 := bbase (se 4 (by rfl) ⟨145971, by rfl⟩ : syracuseStep 1557029 = 291943) (by norm_num)
theorem B1557157 : Blo 920579 1557157 := bbase (se 4 (by rfl) ⟨145983, by rfl⟩ : syracuseStep 1557157 = 291967) (by norm_num)
theorem B1557245 : Blo 920579 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B4440901 : Blo 920579 4440901 := bbase (se 4 (by rfl) ⟨416334, by rfl⟩ : syracuseStep 4440901 = 832669) (by norm_num)
theorem B1557373 : Blo 920579 1557373 := bbase (se 3 (by rfl) ⟨292007, by rfl⟩ : syracuseStep 1557373 = 584015) (by norm_num)
theorem B1557461 : Blo 920579 1557461 := bbase (se 7 (by rfl) ⟨18251, by rfl⟩ : syracuseStep 1557461 = 36503) (by norm_num)
theorem B2212877 : Blo 920579 2212877 := bbase (se 3 (by rfl) ⟨414914, by rfl⟩ : syracuseStep 2212877 = 829829) (by norm_num)
theorem B1754149 : Blo 920579 1754149 := bbase (se 4 (by rfl) ⟨164451, by rfl⟩ : syracuseStep 1754149 = 328903) (by norm_num)
theorem B1557589 : Blo 920579 1557589 := bbase (se 8 (by rfl) ⟨9126, by rfl⟩ : syracuseStep 1557589 = 18253) (by norm_num)
theorem B5260373 : Blo 920579 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B1557677 : Blo 920579 1557677 := bbase (se 3 (by rfl) ⟨292064, by rfl⟩ : syracuseStep 1557677 = 584129) (by norm_num)
theorem B2999477 : Blo 920579 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B1754293 : Blo 920579 1754293 := bbase (se 5 (by rfl) ⟨82232, by rfl⟩ : syracuseStep 1754293 = 164465) (by norm_num)
theorem B1557805 : Blo 920579 1557805 := bbase (se 3 (by rfl) ⟨292088, by rfl⟩ : syracuseStep 1557805 = 584177) (by norm_num)
theorem B1754453 : Blo 920579 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B1557893 : Blo 920579 1557893 := bbase (se 4 (by rfl) ⟨146052, by rfl⟩ : syracuseStep 1557893 = 292105) (by norm_num)
theorem B2803157 : Blo 920579 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1754597 : Blo 920579 1754597 := bbase (se 4 (by rfl) ⟨164493, by rfl⟩ : syracuseStep 1754597 = 328987) (by norm_num)
theorem B1558021 : Blo 920579 1558021 := bbase (se 4 (by rfl) ⟨146064, by rfl⟩ : syracuseStep 1558021 = 292129) (by norm_num)
theorem B1558109 : Blo 920579 1558109 := bbase (se 3 (by rfl) ⟨292145, by rfl⟩ : syracuseStep 1558109 = 584291) (by norm_num)
theorem B1558237 : Blo 920579 1558237 := bbase (se 3 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 1558237 = 584339) (by norm_num)
theorem B1754885 : Blo 920579 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B4671269 : Blo 920579 4671269 := bbase (se 4 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 4671269 = 875863) (by norm_num)
theorem B1558325 : Blo 920579 1558325 := bbase (se 5 (by rfl) ⟨73046, by rfl⟩ : syracuseStep 1558325 = 146093) (by norm_num)
theorem B1165205 : Blo 920579 1165205 := bbase (se 6 (by rfl) ⟨27309, by rfl⟩ : syracuseStep 1165205 = 54619) (by norm_num)
theorem B1755037 : Blo 920579 1755037 := bbase (se 3 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 1755037 = 658139) (by norm_num)
theorem B1558453 : Blo 920579 1558453 := bbase (se 5 (by rfl) ⟨73052, by rfl⟩ : syracuseStep 1558453 = 146105) (by norm_num)
theorem B1165261 : Blo 920579 1165261 := bbase (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) (by norm_num)
theorem B935893 : Blo 920579 935893 := bbase (se 7 (by rfl) ⟨10967, by rfl⟩ : syracuseStep 935893 = 21935) (by norm_num)
theorem B1558541 : Blo 920579 1558541 := bbase (se 3 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 1558541 = 584453) (by norm_num)
theorem B1165357 : Blo 920579 1165357 := bbase (se 3 (by rfl) ⟨218504, by rfl⟩ : syracuseStep 1165357 = 437009) (by norm_num)
theorem B1558669 : Blo 920579 1558669 := bbase (se 3 (by rfl) ⟨292250, by rfl⟩ : syracuseStep 1558669 = 584501) (by norm_num)
theorem B1165529 : Blo 920579 1165529 := bbase (se 2 (by rfl) ⟨437073, by rfl⟩ : syracuseStep 1165529 = 874147) (by norm_num)
theorem B1558757 : Blo 920579 1558757 := bbase (se 4 (by rfl) ⟨146133, by rfl⟩ : syracuseStep 1558757 = 292267) (by norm_num)
theorem B5261557 : Blo 920579 5261557 := bbase (se 5 (by rfl) ⟨246635, by rfl⟩ : syracuseStep 5261557 = 493271) (by norm_num)
theorem B1165585 : Blo 920579 1165585 := bbase (se 2 (by rfl) ⟨437094, by rfl⟩ : syracuseStep 1165585 = 874189) (by norm_num)
theorem B1558885 : Blo 920579 1558885 := bbase (se 4 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 1558885 = 292291) (by norm_num)
theorem B1165681 : Blo 920579 1165681 := bbase (se 2 (by rfl) ⟨437130, by rfl⟩ : syracuseStep 1165681 = 874261) (by norm_num)
theorem B1558973 : Blo 920579 1558973 := bbase (se 3 (by rfl) ⟨292307, by rfl⟩ : syracuseStep 1558973 = 584615) (by norm_num)
theorem B1165853 : Blo 920579 1165853 := bbase (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) (by norm_num)
theorem B1559101 : Blo 920579 1559101 := bbase (se 3 (by rfl) ⟨292331, by rfl⟩ : syracuseStep 1559101 = 584663) (by norm_num)
theorem B1165909 : Blo 920579 1165909 := bbase (se 8 (by rfl) ⟨6831, by rfl⟩ : syracuseStep 1165909 = 13663) (by norm_num)
theorem B1559189 : Blo 920579 1559189 := bbase (se 6 (by rfl) ⟨36543, by rfl⟩ : syracuseStep 1559189 = 73087) (by norm_num)
theorem B1166005 : Blo 920579 1166005 := bbase (se 5 (by rfl) ⟨54656, by rfl⟩ : syracuseStep 1166005 = 109313) (by norm_num)
theorem B1559317 : Blo 920579 1559317 := bbase (se 6 (by rfl) ⟨36546, by rfl⟩ : syracuseStep 1559317 = 73093) (by norm_num)
theorem B5327669 : Blo 920579 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B1166177 : Blo 920579 1166177 := bbase (se 2 (by rfl) ⟨437316, by rfl⟩ : syracuseStep 1166177 = 874633) (by norm_num)
theorem B1559405 : Blo 920579 1559405 := bbase (se 3 (by rfl) ⟨292388, by rfl⟩ : syracuseStep 1559405 = 584777) (by norm_num)
theorem B1166233 : Blo 920579 1166233 := bbase (se 2 (by rfl) ⟨437337, by rfl⟩ : syracuseStep 1166233 = 874675) (by norm_num)
theorem B2214877 : Blo 920579 2214877 := bbase (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) (by norm_num)
theorem B1559533 : Blo 920579 1559533 := bbase (se 3 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 1559533 = 584825) (by norm_num)
theorem B1166329 : Blo 920579 1166329 := bbase (se 2 (by rfl) ⟨437373, by rfl⟩ : syracuseStep 1166329 = 874747) (by norm_num)
theorem B4672565 : Blo 920579 4672565 := bbase (se 5 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 4672565 = 438053) (by norm_num)
theorem B1559621 : Blo 920579 1559621 := bbase (se 4 (by rfl) ⟨146214, by rfl⟩ : syracuseStep 1559621 = 292429) (by norm_num)
theorem B2215021 : Blo 920579 2215021 := bbase (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) (by norm_num)
theorem B1166501 : Blo 920579 1166501 := bbase (se 4 (by rfl) ⟨109359, by rfl⟩ : syracuseStep 1166501 = 218719) (by norm_num)
theorem B1559749 : Blo 920579 1559749 := bbase (se 4 (by rfl) ⟨146226, by rfl⟩ : syracuseStep 1559749 = 292453) (by norm_num)
theorem B1166557 : Blo 920579 1166557 := bbase (se 3 (by rfl) ⟨218729, by rfl⟩ : syracuseStep 1166557 = 437459) (by norm_num)
theorem B1559837 : Blo 920579 1559837 := bbase (se 3 (by rfl) ⟨292469, by rfl⟩ : syracuseStep 1559837 = 584939) (by norm_num)
theorem B1166653 : Blo 920579 1166653 := bbase (se 3 (by rfl) ⟨218747, by rfl⟩ : syracuseStep 1166653 = 437495) (by norm_num)
theorem B1035661 : Blo 920579 1035661 := bbase (se 3 (by rfl) ⟨194186, by rfl⟩ : syracuseStep 1035661 = 388373) (by norm_num)
theorem B1559965 : Blo 920579 1559965 := bbase (se 3 (by rfl) ⟨292493, by rfl⟩ : syracuseStep 1559965 = 584987) (by norm_num)
theorem B1035697 : Blo 920579 1035697 := bbase (se 2 (by rfl) ⟨388386, by rfl⟩ : syracuseStep 1035697 = 776773) (by norm_num)
theorem B1068485 : Blo 920579 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B1035733 : Blo 920579 1035733 := bbase (se 7 (by rfl) ⟨12137, by rfl⟩ : syracuseStep 1035733 = 24275) (by norm_num)
theorem B1166825 : Blo 920579 1166825 := bbase (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) (by norm_num)
theorem B1560053 : Blo 920579 1560053 := bbase (se 5 (by rfl) ⟨73127, by rfl⟩ : syracuseStep 1560053 = 146255) (by norm_num)
theorem B1035769 : Blo 920579 1035769 := bbase (se 2 (by rfl) ⟨388413, by rfl⟩ : syracuseStep 1035769 = 776827) (by norm_num)
theorem B1035805 : Blo 920579 1035805 := bbase (se 3 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 1035805 = 388427) (by norm_num)
theorem B1166881 : Blo 920579 1166881 := bbase (se 2 (by rfl) ⟨437580, by rfl⟩ : syracuseStep 1166881 = 875161) (by norm_num)
theorem B1035841 : Blo 920579 1035841 := bbase (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) (by norm_num)
theorem B1035877 : Blo 920579 1035877 := bbase (se 4 (by rfl) ⟨97113, by rfl⟩ : syracuseStep 1035877 = 194227) (by norm_num)
theorem B1560181 : Blo 920579 1560181 := bbase (se 5 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 1560181 = 146267) (by norm_num)
theorem B1166977 : Blo 920579 1166977 := bbase (se 2 (by rfl) ⟨437616, by rfl⟩ : syracuseStep 1166977 = 875233) (by norm_num)
theorem B1035913 : Blo 920579 1035913 := bbase (se 2 (by rfl) ⟨388467, by rfl⟩ : syracuseStep 1035913 = 776935) (by norm_num)
theorem B1035949 : Blo 920579 1035949 := bbase (se 3 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 1035949 = 388481) (by norm_num)
theorem B1035985 : Blo 920579 1035985 := bbase (se 2 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 1035985 = 776989) (by norm_num)
theorem B19910357 : Blo 920579 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B2215637 : Blo 920579 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B1036021 : Blo 920579 1036021 := bbase (se 5 (by rfl) ⟨48563, by rfl⟩ : syracuseStep 1036021 = 97127) (by norm_num)
theorem B1036057 : Blo 920579 1036057 := bbase (se 2 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 1036057 = 777043) (by norm_num)
theorem B1167149 : Blo 920579 1167149 := bbase (se 3 (by rfl) ⟨218840, by rfl⟩ : syracuseStep 1167149 = 437681) (by norm_num)
theorem B1036093 : Blo 920579 1036093 := bbase (se 3 (by rfl) ⟨194267, by rfl⟩ : syracuseStep 1036093 = 388535) (by norm_num)
theorem B1036129 : Blo 920579 1036129 := bbase (se 2 (by rfl) ⟨388548, by rfl⟩ : syracuseStep 1036129 = 777097) (by norm_num)
theorem B1167205 : Blo 920579 1167205 := bbase (se 4 (by rfl) ⟨109425, by rfl⟩ : syracuseStep 1167205 = 218851) (by norm_num)
theorem B1036165 : Blo 920579 1036165 := bbase (se 4 (by rfl) ⟨97140, by rfl⟩ : syracuseStep 1036165 = 194281) (by norm_num)
theorem B1036201 : Blo 920579 1036201 := bbase (se 2 (by rfl) ⟨388575, by rfl⟩ : syracuseStep 1036201 = 777151) (by norm_num)
theorem B1167301 : Blo 920579 1167301 := bbase (se 4 (by rfl) ⟨109434, by rfl⟩ : syracuseStep 1167301 = 218869) (by norm_num)
theorem B1036237 : Blo 920579 1036237 := bbase (se 3 (by rfl) ⟨194294, by rfl⟩ : syracuseStep 1036237 = 388589) (by norm_num)
theorem B1036273 : Blo 920579 1036273 := bbase (se 2 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 1036273 = 777205) (by norm_num)
theorem B1036309 : Blo 920579 1036309 := bbase (se 6 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 1036309 = 48577) (by norm_num)
theorem B5918741 : Blo 920579 5918741 := bbase (se 6 (by rfl) ⟨138720, by rfl⟩ : syracuseStep 5918741 = 277441) (by norm_num)
theorem B2215973 : Blo 920579 2215973 := bbase (se 4 (by rfl) ⟨207747, by rfl⟩ : syracuseStep 2215973 = 415495) (by norm_num)
theorem B1036345 : Blo 920579 1036345 := bbase (se 2 (by rfl) ⟨388629, by rfl⟩ : syracuseStep 1036345 = 777259) (by norm_num)
theorem B1036381 : Blo 920579 1036381 := bbase (se 3 (by rfl) ⟨194321, by rfl⟩ : syracuseStep 1036381 = 388643) (by norm_num)
theorem B1167473 : Blo 920579 1167473 := bbase (se 2 (by rfl) ⟨437802, by rfl⟩ : syracuseStep 1167473 = 875605) (by norm_num)
theorem B1036417 : Blo 920579 1036417 := bbase (se 2 (by rfl) ⟨388656, by rfl⟩ : syracuseStep 1036417 = 777313) (by norm_num)
theorem B2216069 : Blo 920579 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B1036453 : Blo 920579 1036453 := bbase (se 4 (by rfl) ⟨97167, by rfl⟩ : syracuseStep 1036453 = 194335) (by norm_num)
theorem B1167529 : Blo 920579 1167529 := bbase (se 2 (by rfl) ⟨437823, by rfl⟩ : syracuseStep 1167529 = 875647) (by norm_num)
theorem B5263541 : Blo 920579 5263541 := bbase (se 5 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 5263541 = 493457) (by norm_num)
theorem B1036489 : Blo 920579 1036489 := bbase (se 2 (by rfl) ⟨388683, by rfl⟩ : syracuseStep 1036489 = 777367) (by norm_num)
theorem B1036525 : Blo 920579 1036525 := bbase (se 3 (by rfl) ⟨194348, by rfl⟩ : syracuseStep 1036525 = 388697) (by norm_num)
theorem B1167625 : Blo 920579 1167625 := bbase (se 2 (by rfl) ⟨437859, by rfl⟩ : syracuseStep 1167625 = 875719) (by norm_num)
theorem B1036561 : Blo 920579 1036561 := bbase (se 2 (by rfl) ⟨388710, by rfl⟩ : syracuseStep 1036561 = 777421) (by norm_num)
theorem B1036597 : Blo 920579 1036597 := bbase (se 5 (by rfl) ⟨48590, by rfl⟩ : syracuseStep 1036597 = 97181) (by norm_num)
theorem B2216261 : Blo 920579 2216261 := bbase (se 4 (by rfl) ⟨207774, by rfl⟩ : syracuseStep 2216261 = 415549) (by norm_num)
theorem B4673861 : Blo 920579 4673861 := bbase (se 4 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 4673861 = 876349) (by norm_num)
theorem B1036633 : Blo 920579 1036633 := bbase (se 2 (by rfl) ⟨388737, by rfl⟩ : syracuseStep 1036633 = 777475) (by norm_num)
theorem B1036669 : Blo 920579 1036669 := bbase (se 3 (by rfl) ⟨194375, by rfl⟩ : syracuseStep 1036669 = 388751) (by norm_num)
theorem B1036705 : Blo 920579 1036705 := bbase (se 2 (by rfl) ⟨388764, by rfl⟩ : syracuseStep 1036705 = 777529) (by norm_num)
theorem B1167797 : Blo 920579 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B1036741 : Blo 920579 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B1331653 : Blo 920579 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B1036777 : Blo 920579 1036777 := bbase (se 2 (by rfl) ⟨388791, by rfl⟩ : syracuseStep 1036777 = 777583) (by norm_num)
theorem B1167853 : Blo 920579 1167853 := bbase (se 3 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 1167853 = 437945) (by norm_num)
theorem B1036813 : Blo 920579 1036813 := bbase (se 3 (by rfl) ⟨194402, by rfl⟩ : syracuseStep 1036813 = 388805) (by norm_num)
theorem B1036849 : Blo 920579 1036849 := bbase (se 2 (by rfl) ⟨388818, by rfl⟩ : syracuseStep 1036849 = 777637) (by norm_num)
theorem B1167949 : Blo 920579 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B1036885 : Blo 920579 1036885 := bbase (se 8 (by rfl) ⟨6075, by rfl⟩ : syracuseStep 1036885 = 12151) (by norm_num)
theorem B1659485 : Blo 920579 1659485 := bbase (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) (by norm_num)
theorem B1331813 : Blo 920579 1331813 := bbase (se 4 (by rfl) ⟨124857, by rfl⟩ : syracuseStep 1331813 = 249715) (by norm_num)
theorem B1036921 : Blo 920579 1036921 := bbase (se 2 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 1036921 = 777691) (by norm_num)
theorem B1036957 : Blo 920579 1036957 := bbase (se 3 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 1036957 = 388859) (by norm_num)
theorem B1036993 : Blo 920579 1036993 := bbase (se 2 (by rfl) ⟨388872, by rfl⟩ : syracuseStep 1036993 = 777745) (by norm_num)
theorem B1037029 : Blo 920579 1037029 := bbase (se 4 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 1037029 = 194443) (by norm_num)
theorem B2806501 : Blo 920579 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B1168121 : Blo 920579 1168121 := bbase (se 2 (by rfl) ⟨438045, by rfl⟩ : syracuseStep 1168121 = 876091) (by norm_num)
theorem B1037065 : Blo 920579 1037065 := bbase (se 2 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 1037065 = 777799) (by norm_num)
theorem B1037101 : Blo 920579 1037101 := bbase (se 3 (by rfl) ⟨194456, by rfl⟩ : syracuseStep 1037101 = 388913) (by norm_num)
theorem B1168177 : Blo 920579 1168177 := bbase (se 2 (by rfl) ⟨438066, by rfl⟩ : syracuseStep 1168177 = 876133) (by norm_num)
theorem B1037137 : Blo 920579 1037137 := bbase (se 2 (by rfl) ⟨388926, by rfl⟩ : syracuseStep 1037137 = 777853) (by norm_num)
theorem B1037173 : Blo 920579 1037173 := bbase (se 5 (by rfl) ⟨48617, by rfl⟩ : syracuseStep 1037173 = 97235) (by norm_num)
theorem B1332101 : Blo 920579 1332101 := bbase (se 4 (by rfl) ⟨124884, by rfl⟩ : syracuseStep 1332101 = 249769) (by norm_num)
theorem B1168273 : Blo 920579 1168273 := bbase (se 2 (by rfl) ⟨438102, by rfl⟩ : syracuseStep 1168273 = 876205) (by norm_num)
theorem B1037209 : Blo 920579 1037209 := bbase (se 2 (by rfl) ⟨388953, by rfl⟩ : syracuseStep 1037209 = 777907) (by norm_num)
theorem B1037245 : Blo 920579 1037245 := bbase (se 3 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 1037245 = 388967) (by norm_num)
theorem B1037281 : Blo 920579 1037281 := bbase (se 2 (by rfl) ⟨388980, by rfl⟩ : syracuseStep 1037281 = 777961) (by norm_num)
theorem B1037317 : Blo 920579 1037317 := bbase (se 4 (by rfl) ⟨97248, by rfl⟩ : syracuseStep 1037317 = 194497) (by norm_num)
theorem B2806805 : Blo 920579 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B1037353 : Blo 920579 1037353 := bbase (se 2 (by rfl) ⟨389007, by rfl⟩ : syracuseStep 1037353 = 778015) (by norm_num)
theorem B1168445 : Blo 920579 1168445 := bbase (se 3 (by rfl) ⟨219083, by rfl⟩ : syracuseStep 1168445 = 438167) (by norm_num)
theorem B1037389 : Blo 920579 1037389 := bbase (se 3 (by rfl) ⟨194510, by rfl⟩ : syracuseStep 1037389 = 389021) (by norm_num)
theorem B1037425 : Blo 920579 1037425 := bbase (se 2 (by rfl) ⟨389034, by rfl⟩ : syracuseStep 1037425 = 778069) (by norm_num)
theorem B2806901 : Blo 920579 2806901 := bbase (se 5 (by rfl) ⟨131573, by rfl⟩ : syracuseStep 2806901 = 263147) (by norm_num)
theorem B1168501 : Blo 920579 1168501 := bbase (se 5 (by rfl) ⟨54773, by rfl⟩ : syracuseStep 1168501 = 109547) (by norm_num)
theorem B1037461 : Blo 920579 1037461 := bbase (se 6 (by rfl) ⟨24315, by rfl⟩ : syracuseStep 1037461 = 48631) (by norm_num)
theorem B1037497 : Blo 920579 1037497 := bbase (se 2 (by rfl) ⟨389061, by rfl⟩ : syracuseStep 1037497 = 778123) (by norm_num)
theorem B1168597 : Blo 920579 1168597 := bbase (se 7 (by rfl) ⟨13694, by rfl⟩ : syracuseStep 1168597 = 27389) (by norm_num)
theorem B1037533 : Blo 920579 1037533 := bbase (se 3 (by rfl) ⟨194537, by rfl⟩ : syracuseStep 1037533 = 389075) (by norm_num)
theorem B1037569 : Blo 920579 1037569 := bbase (se 2 (by rfl) ⟨389088, by rfl⟩ : syracuseStep 1037569 = 778177) (by norm_num)
theorem B1037605 : Blo 920579 1037605 := bbase (se 4 (by rfl) ⟨97275, by rfl⟩ : syracuseStep 1037605 = 194551) (by norm_num)
theorem B1037641 : Blo 920579 1037641 := bbase (se 2 (by rfl) ⟨389115, by rfl⟩ : syracuseStep 1037641 = 778231) (by norm_num)
theorem B1037677 : Blo 920579 1037677 := bbase (se 3 (by rfl) ⟨194564, by rfl⟩ : syracuseStep 1037677 = 389129) (by norm_num)
theorem B1168769 : Blo 920579 1168769 := bbase (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) (by norm_num)
theorem B1037713 : Blo 920579 1037713 := bbase (se 2 (by rfl) ⟨389142, by rfl⟩ : syracuseStep 1037713 = 778285) (by norm_num)
theorem B4216229 : Blo 920579 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B1037749 : Blo 920579 1037749 := bbase (se 5 (by rfl) ⟨48644, by rfl⟩ : syracuseStep 1037749 = 97289) (by norm_num)
theorem B1168825 : Blo 920579 1168825 := bbase (se 2 (by rfl) ⟨438309, by rfl⟩ : syracuseStep 1168825 = 876619) (by norm_num)
theorem B2217413 : Blo 920579 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B1037785 : Blo 920579 1037785 := bbase (se 2 (by rfl) ⟨389169, by rfl⟩ : syracuseStep 1037785 = 778339) (by norm_num)
theorem B1496549 : Blo 920579 1496549 := bbase (se 4 (by rfl) ⟨140301, by rfl⟩ : syracuseStep 1496549 = 280603) (by norm_num)
theorem B1037821 : Blo 920579 1037821 := bbase (se 3 (by rfl) ⟨194591, by rfl⟩ : syracuseStep 1037821 = 389183) (by norm_num)
theorem B1168921 : Blo 920579 1168921 := bbase (se 2 (by rfl) ⟨438345, by rfl⟩ : syracuseStep 1168921 = 876691) (by norm_num)
theorem B1037857 : Blo 920579 1037857 := bbase (se 2 (by rfl) ⟨389196, by rfl⟩ : syracuseStep 1037857 = 778393) (by norm_num)
theorem B1037893 : Blo 920579 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B4675157 : Blo 920579 4675157 := bbase (se 8 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 4675157 = 54787) (by norm_num)
theorem B1037929 : Blo 920579 1037929 := bbase (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) (by norm_num)
theorem B1037965 : Blo 920579 1037965 := bbase (se 3 (by rfl) ⟨194618, by rfl⟩ : syracuseStep 1037965 = 389237) (by norm_num)
theorem B1038001 : Blo 920579 1038001 := bbase (se 2 (by rfl) ⟨389250, by rfl⟩ : syracuseStep 1038001 = 778501) (by norm_num)
theorem B1169093 : Blo 920579 1169093 := bbase (se 4 (by rfl) ⟨109602, by rfl⟩ : syracuseStep 1169093 = 219205) (by norm_num)
theorem B1038037 : Blo 920579 1038037 := bbase (se 7 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 1038037 = 24329) (by norm_num)
theorem B1038073 : Blo 920579 1038073 := bbase (se 2 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 1038073 = 778555) (by norm_num)
theorem B1169149 : Blo 920579 1169149 := bbase (se 3 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 1169149 = 438431) (by norm_num)
theorem B1038109 : Blo 920579 1038109 := bbase (se 3 (by rfl) ⟨194645, by rfl⟩ : syracuseStep 1038109 = 389291) (by norm_num)
theorem B1038145 : Blo 920579 1038145 := bbase (se 2 (by rfl) ⟨389304, by rfl⟩ : syracuseStep 1038145 = 778609) (by norm_num)
theorem B1169245 : Blo 920579 1169245 := bbase (se 3 (by rfl) ⟨219233, by rfl⟩ : syracuseStep 1169245 = 438467) (by norm_num)
theorem B1038181 : Blo 920579 1038181 := bbase (se 4 (by rfl) ⟨97329, by rfl⟩ : syracuseStep 1038181 = 194659) (by norm_num)
theorem B1660805 : Blo 920579 1660805 := bbase (se 4 (by rfl) ⟨155700, by rfl⟩ : syracuseStep 1660805 = 311401) (by norm_num)
theorem B1038217 : Blo 920579 1038217 := bbase (se 2 (by rfl) ⟨389331, by rfl⟩ : syracuseStep 1038217 = 778663) (by norm_num)
theorem B1038253 : Blo 920579 1038253 := bbase (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) (by norm_num)
theorem B1038289 : Blo 920579 1038289 := bbase (se 2 (by rfl) ⟨389358, by rfl⟩ : syracuseStep 1038289 = 778717) (by norm_num)
theorem B1038325 : Blo 920579 1038325 := bbase (se 5 (by rfl) ⟨48671, by rfl⟩ : syracuseStep 1038325 = 97343) (by norm_num)
theorem B1169417 : Blo 920579 1169417 := bbase (se 2 (by rfl) ⟨438531, by rfl⟩ : syracuseStep 1169417 = 877063) (by norm_num)
theorem B3332117 : Blo 920579 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B1038361 : Blo 920579 1038361 := bbase (se 2 (by rfl) ⟨389385, by rfl⟩ : syracuseStep 1038361 = 778771) (by norm_num)
theorem B1038397 : Blo 920579 1038397 := bbase (se 3 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 1038397 = 389399) (by norm_num)
theorem B1169473 : Blo 920579 1169473 := bbase (se 2 (by rfl) ⟨438552, by rfl⟩ : syracuseStep 1169473 = 877105) (by norm_num)
theorem B1038433 : Blo 920579 1038433 := bbase (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) (by norm_num)
theorem B1038469 : Blo 920579 1038469 := bbase (se 4 (by rfl) ⟨97356, by rfl⟩ : syracuseStep 1038469 = 194713) (by norm_num)
theorem B1169569 : Blo 920579 1169569 := bbase (se 2 (by rfl) ⟨438588, by rfl⟩ : syracuseStep 1169569 = 877177) (by norm_num)
theorem B1038505 : Blo 920579 1038505 := bbase (se 2 (by rfl) ⟨389439, by rfl⟩ : syracuseStep 1038505 = 778879) (by norm_num)
theorem B1038541 : Blo 920579 1038541 := bbase (se 3 (by rfl) ⟨194726, by rfl⟩ : syracuseStep 1038541 = 389453) (by norm_num)
theorem B1038577 : Blo 920579 1038577 := bbase (se 2 (by rfl) ⟨389466, by rfl⟩ : syracuseStep 1038577 = 778933) (by norm_num)
theorem B1038613 : Blo 920579 1038613 := bbase (se 6 (by rfl) ⟨24342, by rfl⟩ : syracuseStep 1038613 = 48685) (by norm_num)
theorem B1038649 : Blo 920579 1038649 := bbase (se 2 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 1038649 = 778987) (by norm_num)
theorem B1169741 : Blo 920579 1169741 := bbase (se 3 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 1169741 = 438653) (by norm_num)
theorem B5265749 : Blo 920579 5265749 := bbase (se 10 (by rfl) ⟨7713, by rfl⟩ : syracuseStep 5265749 = 15427) (by norm_num)
theorem B1038685 : Blo 920579 1038685 := bbase (se 3 (by rfl) ⟨194753, by rfl⟩ : syracuseStep 1038685 = 389507) (by norm_num)
theorem B1038721 : Blo 920579 1038721 := bbase (se 2 (by rfl) ⟨389520, by rfl⟩ : syracuseStep 1038721 = 779041) (by norm_num)
theorem B1169797 : Blo 920579 1169797 := bbase (se 4 (by rfl) ⟨109668, by rfl⟩ : syracuseStep 1169797 = 219337) (by norm_num)
theorem B1038757 : Blo 920579 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B1038793 : Blo 920579 1038793 := bbase (se 2 (by rfl) ⟨389547, by rfl⟩ : syracuseStep 1038793 = 779095) (by norm_num)
theorem B3496405 : Blo 920579 3496405 := bbase (se 7 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 3496405 = 81947) (by norm_num)
theorem B1169893 : Blo 920579 1169893 := bbase (se 4 (by rfl) ⟨109677, by rfl⟩ : syracuseStep 1169893 = 219355) (by norm_num)
theorem B1038829 : Blo 920579 1038829 := bbase (se 3 (by rfl) ⟨194780, by rfl⟩ : syracuseStep 1038829 = 389561) (by norm_num)
theorem B1038865 : Blo 920579 1038865 := bbase (se 2 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 1038865 = 779149) (by norm_num)
theorem B1038901 : Blo 920579 1038901 := bbase (se 5 (by rfl) ⟨48698, by rfl⟩ : syracuseStep 1038901 = 97397) (by norm_num)
theorem B1038937 : Blo 920579 1038937 := bbase (se 2 (by rfl) ⟨389601, by rfl⟩ : syracuseStep 1038937 = 779203) (by norm_num)
theorem B1038973 : Blo 920579 1038973 := bbase (se 3 (by rfl) ⟨194807, by rfl⟩ : syracuseStep 1038973 = 389615) (by norm_num)
theorem B1170065 : Blo 920579 1170065 := bbase (se 2 (by rfl) ⟨438774, by rfl⟩ : syracuseStep 1170065 = 877549) (by norm_num)
theorem B7002773 : Blo 920579 7002773 := bbase (se 6 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 7002773 = 328255) (by norm_num)
theorem B1039009 : Blo 920579 1039009 := bbase (se 2 (by rfl) ⟨389628, by rfl⟩ : syracuseStep 1039009 = 779257) (by norm_num)
theorem B2808485 : Blo 920579 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B1039045 : Blo 920579 1039045 := bbase (se 4 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 1039045 = 194821) (by norm_num)
theorem B1170121 : Blo 920579 1170121 := bbase (se 2 (by rfl) ⟨438795, by rfl⟩ : syracuseStep 1170121 = 877591) (by norm_num)
theorem B2251477 : Blo 920579 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B1039081 : Blo 920579 1039081 := bbase (se 2 (by rfl) ⟨389655, by rfl⟩ : syracuseStep 1039081 = 779311) (by norm_num)
theorem B3496709 : Blo 920579 3496709 := bbase (se 4 (by rfl) ⟨327816, by rfl⟩ : syracuseStep 3496709 = 655633) (by norm_num)
theorem B1039117 : Blo 920579 1039117 := bbase (se 3 (by rfl) ⟨194834, by rfl⟩ : syracuseStep 1039117 = 389669) (by norm_num)
theorem B1039153 : Blo 920579 1039153 := bbase (se 2 (by rfl) ⟨389682, by rfl⟩ : syracuseStep 1039153 = 779365) (by norm_num)
theorem B1039189 : Blo 920579 1039189 := bbase (se 9 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 1039189 = 6089) (by norm_num)
theorem B4676453 : Blo 920579 4676453 := bbase (se 4 (by rfl) ⟨438417, by rfl⟩ : syracuseStep 4676453 = 876835) (by norm_num)
theorem B1039225 : Blo 920579 1039225 := bbase (se 2 (by rfl) ⟨389709, by rfl⟩ : syracuseStep 1039225 = 779419) (by norm_num)
theorem B1039261 : Blo 920579 1039261 := bbase (se 3 (by rfl) ⟨194861, by rfl⟩ : syracuseStep 1039261 = 389723) (by norm_num)
theorem B1039297 : Blo 920579 1039297 := bbase (se 2 (by rfl) ⟨389736, by rfl⟩ : syracuseStep 1039297 = 779473) (by norm_num)
theorem B1039333 : Blo 920579 1039333 := bbase (se 4 (by rfl) ⟨97437, by rfl⟩ : syracuseStep 1039333 = 194875) (by norm_num)
theorem B1039369 : Blo 920579 1039369 := bbase (se 2 (by rfl) ⟨389763, by rfl⟩ : syracuseStep 1039369 = 779527) (by norm_num)
theorem B8969237 : Blo 920579 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B1039405 : Blo 920579 1039405 := bbase (se 3 (by rfl) ⟨194888, by rfl⟩ : syracuseStep 1039405 = 389777) (by norm_num)
theorem B1039441 : Blo 920579 1039441 := bbase (se 2 (by rfl) ⟨389790, by rfl⟩ : syracuseStep 1039441 = 779581) (by norm_num)
theorem B1039477 : Blo 920579 1039477 := bbase (se 5 (by rfl) ⟨48725, by rfl⟩ : syracuseStep 1039477 = 97451) (by norm_num)
theorem B1039513 : Blo 920579 1039513 := bbase (se 2 (by rfl) ⟨389817, by rfl⟩ : syracuseStep 1039513 = 779635) (by norm_num)
theorem B1399997 : Blo 920579 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B1039549 : Blo 920579 1039549 := bbase (se 3 (by rfl) ⟨194915, by rfl⟩ : syracuseStep 1039549 = 389831) (by norm_num)
theorem B1039585 : Blo 920579 1039585 := bbase (se 2 (by rfl) ⟨389844, by rfl⟩ : syracuseStep 1039585 = 779689) (by norm_num)
theorem B1400069 : Blo 920579 1400069 := bbase (se 4 (by rfl) ⟨131256, by rfl⟩ : syracuseStep 1400069 = 262513) (by norm_num)
theorem B1039621 : Blo 920579 1039621 := bbase (se 4 (by rfl) ⟨97464, by rfl⟩ : syracuseStep 1039621 = 194929) (by norm_num)
theorem B1039657 : Blo 920579 1039657 := bbase (se 2 (by rfl) ⟨389871, by rfl⟩ : syracuseStep 1039657 = 779743) (by norm_num)
theorem B1039693 : Blo 920579 1039693 := bbase (se 3 (by rfl) ⟨194942, by rfl⟩ : syracuseStep 1039693 = 389885) (by norm_num)
theorem B1039729 : Blo 920579 1039729 := bbase (se 2 (by rfl) ⟨389898, by rfl⟩ : syracuseStep 1039729 = 779797) (by norm_num)
theorem B1662325 : Blo 920579 1662325 := bbase (se 5 (by rfl) ⟨77921, by rfl⟩ : syracuseStep 1662325 = 155843) (by norm_num)
theorem B2219413 : Blo 920579 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B1039765 : Blo 920579 1039765 := bbase (se 6 (by rfl) ⟨24369, by rfl⟩ : syracuseStep 1039765 = 48739) (by norm_num)
theorem B1039801 : Blo 920579 1039801 := bbase (se 2 (by rfl) ⟨389925, by rfl⟩ : syracuseStep 1039801 = 779851) (by norm_num)
theorem B1039837 : Blo 920579 1039837 := bbase (se 3 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 1039837 = 389939) (by norm_num)
theorem B7888373 : Blo 920579 7888373 := bbase (se 5 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 7888373 = 739535) (by norm_num)
theorem B2219509 : Blo 920579 2219509 := bbase (se 5 (by rfl) ⟨104039, by rfl⟩ : syracuseStep 2219509 = 208079) (by norm_num)
theorem B1039873 : Blo 920579 1039873 := bbase (se 2 (by rfl) ⟨389952, by rfl⟩ : syracuseStep 1039873 = 779905) (by norm_num)
theorem B3988997 : Blo 920579 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B1039909 : Blo 920579 1039909 := bbase (se 4 (by rfl) ⟨97491, by rfl⟩ : syracuseStep 1039909 = 194983) (by norm_num)
theorem B1039945 : Blo 920579 1039945 := bbase (se 2 (by rfl) ⟨389979, by rfl⟩ : syracuseStep 1039945 = 779959) (by norm_num)
theorem B1039981 : Blo 920579 1039981 := bbase (se 3 (by rfl) ⟨194996, by rfl⟩ : syracuseStep 1039981 = 389993) (by norm_num)
theorem B1040017 : Blo 920579 1040017 := bbase (se 2 (by rfl) ⟨390006, by rfl⟩ : syracuseStep 1040017 = 780013) (by norm_num)
theorem B1040053 : Blo 920579 1040053 := bbase (se 5 (by rfl) ⟨48752, by rfl⟩ : syracuseStep 1040053 = 97505) (by norm_num)
theorem B1040089 : Blo 920579 1040089 := bbase (se 2 (by rfl) ⟨390033, by rfl⟩ : syracuseStep 1040089 = 780067) (by norm_num)
theorem B1040125 : Blo 920579 1040125 := bbase (se 3 (by rfl) ⟨195023, by rfl⟩ : syracuseStep 1040125 = 390047) (by norm_num)
theorem B1924877 : Blo 920579 1924877 := bbase (se 3 (by rfl) ⟨360914, by rfl⟩ : syracuseStep 1924877 = 721829) (by norm_num)
theorem B1892165 : Blo 920579 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B4677749 : Blo 920579 4677749 := bbase (se 5 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 4677749 = 438539) (by norm_num)
theorem B1892477 : Blo 920579 1892477 := bbase (se 3 (by rfl) ⟨354839, by rfl⟩ : syracuseStep 1892477 = 709679) (by norm_num)
theorem B1401013 : Blo 920579 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B1106141 : Blo 920579 1106141 := bbase (se 3 (by rfl) ⟨207401, by rfl⟩ : syracuseStep 1106141 = 414803) (by norm_num)
theorem B14180629 : Blo 920579 14180629 := bbase (se 6 (by rfl) ⟨332358, by rfl⟩ : syracuseStep 14180629 = 664717) (by norm_num)
theorem B2220605 : Blo 920579 2220605 := bbase (se 3 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 2220605 = 832727) (by norm_num)
theorem B1106497 : Blo 920579 1106497 := bbase (se 2 (by rfl) ⟨414936, by rfl⟩ : syracuseStep 1106497 = 829873) (by norm_num)
theorem B1663573 : Blo 920579 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B2024029 : Blo 920579 2024029 := bbase (se 3 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 2024029 = 759011) (by norm_num)
theorem B1401517 : Blo 920579 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B1106689 : Blo 920579 1106689 := bbase (se 2 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 1106689 = 830017) (by norm_num)
theorem B3498821 : Blo 920579 3498821 := bbase (se 4 (by rfl) ⟨328014, by rfl⟩ : syracuseStep 3498821 = 656029) (by norm_num)
theorem B1401725 : Blo 920579 1401725 := bbase (se 3 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 1401725 = 525647) (by norm_num)
theorem B1106833 : Blo 920579 1106833 := bbase (se 2 (by rfl) ⟨415062, by rfl⟩ : syracuseStep 1106833 = 830125) (by norm_num)
theorem B3499109 : Blo 920579 3499109 := bbase (se 4 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 3499109 = 656083) (by norm_num)
theorem B1402181 : Blo 920579 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B4679045 : Blo 920579 4679045 := bbase (se 4 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 4679045 = 877321) (by norm_num)
theorem B1893989 : Blo 920579 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B1664957 : Blo 920579 1664957 := bbase (se 3 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 1664957 = 624359) (by norm_num)
theorem B3106997 : Blo 920579 3106997 := bbase (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) (by norm_num)
theorem B3500293 : Blo 920579 3500293 := bbase (se 4 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 3500293 = 656305) (by norm_num)
theorem B1108361 : Blo 920579 1108361 := bbase (se 2 (by rfl) ⟨415635, by rfl⟩ : syracuseStep 1108361 = 831271) (by norm_num)
theorem B3500597 : Blo 920579 3500597 := bbase (se 5 (by rfl) ⟨164090, by rfl⟩ : syracuseStep 3500597 = 328181) (by norm_num)
theorem B3107429 : Blo 920579 3107429 := bbase (se 4 (by rfl) ⟨291321, by rfl⟩ : syracuseStep 3107429 = 582643) (by norm_num)
theorem B4680341 : Blo 920579 4680341 := bbase (se 6 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 4680341 = 219391) (by norm_num)
theorem B1108669 : Blo 920579 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B1108765 : Blo 920579 1108765 := bbase (se 3 (by rfl) ⟨207893, by rfl⟩ : syracuseStep 1108765 = 415787) (by norm_num)
theorem B3107861 : Blo 920579 3107861 := bbase (se 6 (by rfl) ⟨72840, by rfl⟩ : syracuseStep 3107861 = 145681) (by norm_num)
theorem B1109053 : Blo 920579 1109053 := bbase (se 3 (by rfl) ⟨207947, by rfl⟩ : syracuseStep 1109053 = 415895) (by norm_num)
theorem B1109245 : Blo 920579 1109245 := bbase (se 3 (by rfl) ⟨207983, by rfl⟩ : syracuseStep 1109245 = 415967) (by norm_num)
theorem B1404157 : Blo 920579 1404157 := bbase (se 3 (by rfl) ⟨263279, by rfl⟩ : syracuseStep 1404157 = 526559) (by norm_num)
theorem B7466357 : Blo 920579 7466357 := bbase (se 5 (by rfl) ⟨349985, by rfl⟩ : syracuseStep 7466357 = 699971) (by norm_num)
theorem B3108293 : Blo 920579 3108293 := bbase (se 4 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 3108293 = 582805) (by norm_num)
theorem B5336533 : Blo 920579 5336533 := bbase (se 7 (by rfl) ⟨62537, by rfl⟩ : syracuseStep 5336533 = 125075) (by norm_num)
theorem B3108725 : Blo 920579 3108725 := bbase (se 5 (by rfl) ⟨145721, by rfl⟩ : syracuseStep 3108725 = 291443) (by norm_num)
theorem B1110125 : Blo 920579 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B3109157 : Blo 920579 3109157 := bbase (se 4 (by rfl) ⟨291483, by rfl⟩ : syracuseStep 3109157 = 582967) (by norm_num)
theorem B1405325 : Blo 920579 1405325 := bbase (se 3 (by rfl) ⟨263498, by rfl⟩ : syracuseStep 1405325 = 526997) (by norm_num)
theorem B1110629 : Blo 920579 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B3502709 : Blo 920579 3502709 := bbase (se 5 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 3502709 = 328379) (by norm_num)
theorem B1110677 : Blo 920579 1110677 := bbase (se 6 (by rfl) ⟨26031, by rfl⟩ : syracuseStep 1110677 = 52063) (by norm_num)
theorem B3109589 : Blo 920579 3109589 := bbase (se 7 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 3109589 = 72881) (by norm_num)
theorem B2028341 : Blo 920579 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B3502997 : Blo 920579 3502997 := bbase (se 6 (by rfl) ⟨82101, by rfl⟩ : syracuseStep 3502997 = 164203) (by norm_num)
theorem B3110021 : Blo 920579 3110021 := bbase (se 4 (by rfl) ⟨291564, by rfl⟩ : syracuseStep 3110021 = 583129) (by norm_num)
theorem B1996213 : Blo 920579 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B3110453 : Blo 920579 3110453 := bbase (se 5 (by rfl) ⟨145802, by rfl⟩ : syracuseStep 3110453 = 291605) (by norm_num)
theorem B3110885 : Blo 920579 3110885 := bbase (se 4 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 3110885 = 583291) (by norm_num)
theorem B3504181 : Blo 920579 3504181 := bbase (se 5 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 3504181 = 328517) (by norm_num)
theorem B1439837 : Blo 920579 1439837 := bbase (se 3 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 1439837 = 539939) (by norm_num)
theorem B7010549 : Blo 920579 7010549 := bbase (se 5 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 7010549 = 657239) (by norm_num)
theorem B3504485 : Blo 920579 3504485 := bbase (se 4 (by rfl) ⟨328545, by rfl⟩ : syracuseStep 3504485 = 657091) (by norm_num)
theorem B3733877 : Blo 920579 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B3111317 : Blo 920579 3111317 := bbase (se 6 (by rfl) ⟨72921, by rfl⟩ : syracuseStep 3111317 = 145843) (by norm_num)
theorem B948629 : Blo 920579 948629 := bbase (se 6 (by rfl) ⟨22233, by rfl⟩ : syracuseStep 948629 = 44467) (by norm_num)
theorem B948893 : Blo 920579 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B3111749 : Blo 920579 3111749 := bbase (se 4 (by rfl) ⟨291726, by rfl⟩ : syracuseStep 3111749 = 583453) (by norm_num)
theorem B1244333 : Blo 920579 1244333 := bbase (se 3 (by rfl) ⟨233312, by rfl⟩ : syracuseStep 1244333 = 466625) (by norm_num)
theorem B2489573 : Blo 920579 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B3112181 : Blo 920579 3112181 := bbase (se 5 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 3112181 = 291767) (by norm_num)
theorem B7896437 : Blo 920579 7896437 := bbase (se 5 (by rfl) ⟨370145, by rfl⟩ : syracuseStep 7896437 = 740291) (by norm_num)
theorem B6651317 : Blo 920579 6651317 := bbase (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) (by norm_num)
theorem B1539733 : Blo 920579 1539733 := bbase (se 6 (by rfl) ⟨36087, by rfl⟩ : syracuseStep 1539733 = 72175) (by norm_num)
theorem B3112613 : Blo 920579 3112613 := bbase (se 4 (by rfl) ⟨291807, by rfl⟩ : syracuseStep 3112613 = 583615) (by norm_num)
theorem B1244917 : Blo 920579 1244917 := bbase (se 5 (by rfl) ⟨58355, by rfl⟩ : syracuseStep 1244917 = 116711) (by norm_num)
theorem B1245133 : Blo 920579 1245133 := bbase (se 3 (by rfl) ⟨233462, by rfl⟩ : syracuseStep 1245133 = 466925) (by norm_num)
theorem B1310833 : Blo 920579 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B7012493 : Blo 920579 7012493 := bstep (se 3 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 7012493 = 2629685) B2629685
theorem B1868017 : Blo 920579 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B3113261 : Blo 920579 3113261 := bstep (se 3 (by rfl) ⟨583736, by rfl⟩ : syracuseStep 3113261 = 1167473) B1167473
theorem B5898545 : Blo 920579 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B3113315 : Blo 920579 3113315 := bstep (se 1 (by rfl) ⟨2334986, by rfl⟩ : syracuseStep 3113315 = 4669973) B4669973
theorem B18907505 : Blo 920579 18907505 := bstep (se 2 (by rfl) ⟨7090314, by rfl⟩ : syracuseStep 18907505 = 14180629) B14180629
theorem B3932621 : Blo 920579 3932621 := bstep (se 3 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 3932621 = 1474733) B1474733
theorem B1966609 : Blo 920579 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B2949709 : Blo 920579 2949709 := bstep (se 3 (by rfl) ⟨553070, by rfl⟩ : syracuseStep 2949709 = 1106141) B1106141
theorem B1311329 : Blo 920579 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B3113585 : Blo 920579 3113585 := bstep (se 2 (by rfl) ⟨1167594, by rfl⟩ : syracuseStep 3113585 = 2335189) B2335189
theorem B14615153 : Blo 920579 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B6324941 : Blo 920579 6324941 := bstep (se 3 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 6324941 = 2371853) B2371853
theorem B3506915 : Blo 920579 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B1475329 : Blo 920579 1475329 := bstep (se 2 (by rfl) ⟨553248, by rfl⟩ : syracuseStep 1475329 = 1106497) B1106497
theorem B1999651 : Blo 920579 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B5604173 : Blo 920579 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B1868689 : Blo 920579 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1868771 : Blo 920579 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1475585 : Blo 920579 1475585 := bstep (se 2 (by rfl) ⟨553344, by rfl⟩ : syracuseStep 1475585 = 1106689) B1106689
theorem B3114125 : Blo 920579 3114125 := bstep (se 3 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 3114125 = 1167797) B1167797
theorem B1967267 : Blo 920579 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B1475777 : Blo 920579 1475777 := bstep (se 2 (by rfl) ⟨553416, by rfl⟩ : syracuseStep 1475777 = 1106833) B1106833
theorem B3114179 : Blo 920579 3114179 := bstep (se 1 (by rfl) ⟨2335634, by rfl⟩ : syracuseStep 3114179 = 4671269) B4671269
theorem B984355 : Blo 920579 984355 := bstep (se 1 (by rfl) ⟨738266, by rfl⟩ : syracuseStep 984355 = 1476533) B1476533
theorem B8848739 : Blo 920579 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B3507569 : Blo 920579 3507569 := bstep (se 2 (by rfl) ⟨1315338, by rfl⟩ : syracuseStep 3507569 = 2630677) B2630677
theorem B2622851 : Blo 920579 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B1312195 : Blo 920579 1312195 := bstep (se 1 (by rfl) ⟨984146, by rfl⟩ : syracuseStep 1312195 = 1968293) B1968293
theorem B3114449 : Blo 920579 3114449 := bstep (se 2 (by rfl) ⟨1167918, by rfl⟩ : syracuseStep 3114449 = 2335837) B2335837
theorem B8881649 : Blo 920579 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B1312291 : Blo 920579 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B33326645 : Blo 920579 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B4425293 : Blo 920579 4425293 := bstep (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) B1659485
theorem B4982435 : Blo 920579 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B3114989 : Blo 920579 3114989 := bstep (se 3 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 3114989 = 1168121) B1168121
theorem B1968113 : Blo 920579 1968113 := bstep (se 2 (by rfl) ⟨738042, by rfl⟩ : syracuseStep 1968113 = 1476085) B1476085
theorem B1312787 : Blo 920579 1312787 := bstep (se 1 (by rfl) ⟨984590, by rfl⟩ : syracuseStep 1312787 = 1969181) B1969181
theorem B3115043 : Blo 920579 3115043 := bstep (se 1 (by rfl) ⟨2336282, by rfl⟩ : syracuseStep 3115043 = 4672565) B4672565
theorem B2623661 : Blo 920579 2623661 := bstep (se 3 (by rfl) ⟨491936, by rfl⟩ : syracuseStep 2623661 = 983873) B983873
theorem B3115313 : Blo 920579 3115313 := bstep (se 2 (by rfl) ⟨1168242, by rfl⟩ : syracuseStep 3115313 = 2336485) B2336485
theorem B3737933 : Blo 920579 3737933 := bstep (se 3 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 3737933 = 1401725) B1401725
theorem B2623853 : Blo 920579 2623853 := bstep (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) B983945
theorem B13273571 : Blo 920579 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B1477091 : Blo 920579 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B1313425 : Blo 920579 1313425 := bstep (se 2 (by rfl) ⟨492534, by rfl⟩ : syracuseStep 1313425 = 985069) B985069
theorem B1247923 : Blo 920579 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1477315 : Blo 920579 1477315 := bstep (se 1 (by rfl) ⟨1107986, by rfl⟩ : syracuseStep 1477315 = 2215973) B2215973
theorem B5901005 : Blo 920579 5901005 := bstep (se 3 (by rfl) ⟨1106438, by rfl⟩ : syracuseStep 5901005 = 2212877) B2212877
theorem B1477379 : Blo 920579 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B3509027 : Blo 920579 3509027 := bstep (se 1 (by rfl) ⟨2631770, by rfl⟩ : syracuseStep 3509027 = 5263541) B5263541
theorem B3509041 : Blo 920579 3509041 := bstep (se 2 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 3509041 = 2631781) B2631781
theorem B3115853 : Blo 920579 3115853 := bstep (se 3 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 3115853 = 1168445) B1168445
theorem B2493283 : Blo 920579 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B1575811 : Blo 920579 1575811 := bstep (se 1 (by rfl) ⟨1181858, by rfl⟩ : syracuseStep 1575811 = 2363717) B2363717
theorem B1477507 : Blo 920579 1477507 := bstep (se 1 (by rfl) ⟨1108130, by rfl⟩ : syracuseStep 1477507 = 2216261) B2216261
theorem B3115907 : Blo 920579 3115907 := bstep (se 1 (by rfl) ⟨2336930, by rfl⟩ : syracuseStep 3115907 = 4673861) B4673861
theorem B10259341 : Blo 920579 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B1182643 : Blo 920579 1182643 := bstep (se 1 (by rfl) ⟨886982, by rfl⟩ : syracuseStep 1182643 = 1773965) B1773965
theorem B1313761 : Blo 920579 1313761 := bstep (se 2 (by rfl) ⟨492660, by rfl⟩ : syracuseStep 1313761 = 985321) B985321
theorem B7015409 : Blo 920579 7015409 := bstep (se 2 (by rfl) ⟨2630778, by rfl⟩ : syracuseStep 7015409 = 5261557) B5261557
theorem B920579 : Blo 920579 920579 := bstep (se 1 (by rfl) ⟨690434, by rfl⟩ : syracuseStep 920579 = 1380869) B1380869
theorem B920595 : Blo 920579 920595 := bstep (se 1 (by rfl) ⟨690446, by rfl⟩ : syracuseStep 920595 = 1380893) B1380893
theorem B920611 : Blo 920579 920611 := bstep (se 1 (by rfl) ⟨690458, by rfl⟩ : syracuseStep 920611 = 1380917) B1380917
theorem B920627 : Blo 920579 920627 := bstep (se 1 (by rfl) ⟨690470, by rfl⟩ : syracuseStep 920627 = 1380941) B1380941
theorem B920643 : Blo 920579 920643 := bstep (se 1 (by rfl) ⟨690482, by rfl⟩ : syracuseStep 920643 = 1380965) B1380965
theorem B920659 : Blo 920579 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B920675 : Blo 920579 920675 := bstep (se 1 (by rfl) ⟨690506, by rfl⟩ : syracuseStep 920675 = 1381013) B1381013
theorem B920691 : Blo 920579 920691 := bstep (se 1 (by rfl) ⟨690518, by rfl⟩ : syracuseStep 920691 = 1381037) B1381037
theorem B920707 : Blo 920579 920707 := bstep (se 1 (by rfl) ⟨690530, by rfl⟩ : syracuseStep 920707 = 1381061) B1381061
theorem B3116177 : Blo 920579 3116177 := bstep (se 2 (by rfl) ⟨1168566, by rfl⟩ : syracuseStep 3116177 = 2337133) B2337133
theorem B920723 : Blo 920579 920723 := bstep (se 1 (by rfl) ⟨690542, by rfl⟩ : syracuseStep 920723 = 1381085) B1381085
theorem B1051795 : Blo 920579 1051795 := bstep (se 1 (by rfl) ⟨788846, by rfl⟩ : syracuseStep 1051795 = 1577693) B1577693
theorem B920739 : Blo 920579 920739 := bstep (se 1 (by rfl) ⟨690554, by rfl⟩ : syracuseStep 920739 = 1381109) B1381109
theorem B920755 : Blo 920579 920755 := bstep (se 1 (by rfl) ⟨690566, by rfl⟩ : syracuseStep 920755 = 1381133) B1381133
theorem B920771 : Blo 920579 920771 := bstep (se 1 (by rfl) ⟨690578, by rfl⟩ : syracuseStep 920771 = 1381157) B1381157
theorem B920787 : Blo 920579 920787 := bstep (se 1 (by rfl) ⟨690590, by rfl⟩ : syracuseStep 920787 = 1381181) B1381181
theorem B920803 : Blo 920579 920803 := bstep (se 1 (by rfl) ⟨690602, by rfl⟩ : syracuseStep 920803 = 1381205) B1381205
theorem B920819 : Blo 920579 920819 := bstep (se 1 (by rfl) ⟨690614, by rfl⟩ : syracuseStep 920819 = 1381229) B1381229
theorem B920835 : Blo 920579 920835 := bstep (se 1 (by rfl) ⟨690626, by rfl⟩ : syracuseStep 920835 = 1381253) B1381253
theorem B920851 : Blo 920579 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B920867 : Blo 920579 920867 := bstep (se 1 (by rfl) ⟨690650, by rfl⟩ : syracuseStep 920867 = 1381301) B1381301
theorem B920883 : Blo 920579 920883 := bstep (se 1 (by rfl) ⟨690662, by rfl⟩ : syracuseStep 920883 = 1381325) B1381325
theorem B920899 : Blo 920579 920899 := bstep (se 1 (by rfl) ⟨690674, by rfl⟩ : syracuseStep 920899 = 1381349) B1381349
theorem B2624845 : Blo 920579 2624845 := bstep (se 3 (by rfl) ⟨492158, by rfl⟩ : syracuseStep 2624845 = 984317) B984317
theorem B920915 : Blo 920579 920915 := bstep (se 1 (by rfl) ⟨690686, by rfl⟩ : syracuseStep 920915 = 1381373) B1381373
theorem B920931 : Blo 920579 920931 := bstep (se 1 (by rfl) ⟨690698, by rfl⟩ : syracuseStep 920931 = 1381397) B1381397
theorem B1871203 : Blo 920579 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B920947 : Blo 920579 920947 := bstep (se 1 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 920947 = 1381421) B1381421
theorem B920963 : Blo 920579 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B920979 : Blo 920579 920979 := bstep (se 1 (by rfl) ⟨690734, by rfl⟩ : syracuseStep 920979 = 1381469) B1381469
theorem B920995 : Blo 920579 920995 := bstep (se 1 (by rfl) ⟨690746, by rfl⟩ : syracuseStep 920995 = 1381493) B1381493
theorem B1871267 : Blo 920579 1871267 := bstep (se 1 (by rfl) ⟨1403450, by rfl⟩ : syracuseStep 1871267 = 2806901) B2806901
theorem B921011 : Blo 920579 921011 := bstep (se 1 (by rfl) ⟨690758, by rfl⟩ : syracuseStep 921011 = 1381517) B1381517
theorem B921027 : Blo 920579 921027 := bstep (se 1 (by rfl) ⟨690770, by rfl⟩ : syracuseStep 921027 = 1381541) B1381541
theorem B921043 : Blo 920579 921043 := bstep (se 1 (by rfl) ⟨690782, by rfl⟩ : syracuseStep 921043 = 1381565) B1381565
theorem B921059 : Blo 920579 921059 := bstep (se 1 (by rfl) ⟨690794, by rfl⟩ : syracuseStep 921059 = 1381589) B1381589
theorem B921075 : Blo 920579 921075 := bstep (se 1 (by rfl) ⟨690806, by rfl⟩ : syracuseStep 921075 = 1381613) B1381613
theorem B921091 : Blo 920579 921091 := bstep (se 1 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 921091 = 1381637) B1381637
theorem B5246477 : Blo 920579 5246477 := bstep (se 3 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 5246477 = 1967429) B1967429
theorem B921107 : Blo 920579 921107 := bstep (se 1 (by rfl) ⟨690830, by rfl⟩ : syracuseStep 921107 = 1381661) B1381661
theorem B921123 : Blo 920579 921123 := bstep (se 1 (by rfl) ⟨690842, by rfl⟩ : syracuseStep 921123 = 1381685) B1381685
theorem B1314353 : Blo 920579 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B921139 : Blo 920579 921139 := bstep (se 1 (by rfl) ⟨690854, by rfl⟩ : syracuseStep 921139 = 1381709) B1381709
theorem B921155 : Blo 920579 921155 := bstep (se 1 (by rfl) ⟨690866, by rfl⟩ : syracuseStep 921155 = 1381733) B1381733
theorem B1478225 : Blo 920579 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B921171 : Blo 920579 921171 := bstep (se 1 (by rfl) ⟨690878, by rfl⟩ : syracuseStep 921171 = 1381757) B1381757
theorem B921187 : Blo 920579 921187 := bstep (se 1 (by rfl) ⟨690890, by rfl⟩ : syracuseStep 921187 = 1381781) B1381781
theorem B921203 : Blo 920579 921203 := bstep (se 1 (by rfl) ⟨690902, by rfl⟩ : syracuseStep 921203 = 1381805) B1381805
theorem B921219 : Blo 920579 921219 := bstep (se 1 (by rfl) ⟨690914, by rfl⟩ : syracuseStep 921219 = 1381829) B1381829
theorem B921235 : Blo 920579 921235 := bstep (se 1 (by rfl) ⟨690926, by rfl⟩ : syracuseStep 921235 = 1381853) B1381853
theorem B921251 : Blo 920579 921251 := bstep (se 1 (by rfl) ⟨690938, by rfl⟩ : syracuseStep 921251 = 1381877) B1381877
theorem B3116717 : Blo 920579 3116717 := bstep (se 3 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 3116717 = 1168769) B1168769
theorem B921267 : Blo 920579 921267 := bstep (se 1 (by rfl) ⟨690950, by rfl⟩ : syracuseStep 921267 = 1381901) B1381901
theorem B921283 : Blo 920579 921283 := bstep (se 1 (by rfl) ⟨690962, by rfl⟩ : syracuseStep 921283 = 1381925) B1381925
theorem B1478353 : Blo 920579 1478353 := bstep (se 2 (by rfl) ⟨554382, by rfl⟩ : syracuseStep 1478353 = 1108765) B1108765
theorem B921299 : Blo 920579 921299 := bstep (se 1 (by rfl) ⟨690974, by rfl⟩ : syracuseStep 921299 = 1381949) B1381949
theorem B921315 : Blo 920579 921315 := bstep (se 1 (by rfl) ⟨690986, by rfl⟩ : syracuseStep 921315 = 1381973) B1381973
theorem B1052387 : Blo 920579 1052387 := bstep (se 1 (by rfl) ⟨789290, by rfl⟩ : syracuseStep 1052387 = 1578581) B1578581
theorem B3116771 : Blo 920579 3116771 := bstep (se 1 (by rfl) ⟨2337578, by rfl⟩ : syracuseStep 3116771 = 4675157) B4675157
theorem B921331 : Blo 920579 921331 := bstep (se 1 (by rfl) ⟨690998, by rfl⟩ : syracuseStep 921331 = 1381997) B1381997
theorem B921347 : Blo 920579 921347 := bstep (se 1 (by rfl) ⟨691010, by rfl⟩ : syracuseStep 921347 = 1382021) B1382021
theorem B921363 : Blo 920579 921363 := bstep (se 1 (by rfl) ⟨691022, by rfl⟩ : syracuseStep 921363 = 1382045) B1382045
theorem B921379 : Blo 920579 921379 := bstep (se 1 (by rfl) ⟨691034, by rfl⟩ : syracuseStep 921379 = 1382069) B1382069
theorem B921395 : Blo 920579 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B921411 : Blo 920579 921411 := bstep (se 1 (by rfl) ⟨691058, by rfl⟩ : syracuseStep 921411 = 1382117) B1382117
theorem B921427 : Blo 920579 921427 := bstep (se 1 (by rfl) ⟨691070, by rfl⟩ : syracuseStep 921427 = 1382141) B1382141
theorem B921443 : Blo 920579 921443 := bstep (se 1 (by rfl) ⟨691082, by rfl⟩ : syracuseStep 921443 = 1382165) B1382165
theorem B921459 : Blo 920579 921459 := bstep (se 1 (by rfl) ⟨691094, by rfl⟩ : syracuseStep 921459 = 1382189) B1382189
theorem B986995 : Blo 920579 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B921475 : Blo 920579 921475 := bstep (se 1 (by rfl) ⟨691106, by rfl⟩ : syracuseStep 921475 = 1382213) B1382213
theorem B921491 : Blo 920579 921491 := bstep (se 1 (by rfl) ⟨691118, by rfl⟩ : syracuseStep 921491 = 1382237) B1382237
theorem B921507 : Blo 920579 921507 := bstep (se 1 (by rfl) ⟨691130, by rfl⟩ : syracuseStep 921507 = 1382261) B1382261
theorem B921523 : Blo 920579 921523 := bstep (se 1 (by rfl) ⟨691142, by rfl⟩ : syracuseStep 921523 = 1382285) B1382285
theorem B921539 : Blo 920579 921539 := bstep (se 1 (by rfl) ⟨691154, by rfl⟩ : syracuseStep 921539 = 1382309) B1382309
theorem B2953169 : Blo 920579 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B921555 : Blo 920579 921555 := bstep (se 1 (by rfl) ⟨691166, by rfl⟩ : syracuseStep 921555 = 1382333) B1382333
theorem B921571 : Blo 920579 921571 := bstep (se 1 (by rfl) ⟨691178, by rfl⟩ : syracuseStep 921571 = 1382357) B1382357
theorem B3117041 : Blo 920579 3117041 := bstep (se 2 (by rfl) ⟨1168890, by rfl⟩ : syracuseStep 3117041 = 2337781) B2337781
theorem B921587 : Blo 920579 921587 := bstep (se 1 (by rfl) ⟨691190, by rfl⟩ : syracuseStep 921587 = 1382381) B1382381
theorem B921603 : Blo 920579 921603 := bstep (se 1 (by rfl) ⟨691202, by rfl⟩ : syracuseStep 921603 = 1382405) B1382405
theorem B921619 : Blo 920579 921619 := bstep (se 1 (by rfl) ⟨691214, by rfl⟩ : syracuseStep 921619 = 1382429) B1382429
theorem B921635 : Blo 920579 921635 := bstep (se 1 (by rfl) ⟨691226, by rfl⟩ : syracuseStep 921635 = 1382453) B1382453
theorem B921651 : Blo 920579 921651 := bstep (se 1 (by rfl) ⟨691238, by rfl⟩ : syracuseStep 921651 = 1382477) B1382477
theorem B921667 : Blo 920579 921667 := bstep (se 1 (by rfl) ⟨691250, by rfl⟩ : syracuseStep 921667 = 1382501) B1382501
theorem B1314883 : Blo 920579 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B1478737 : Blo 920579 1478737 := bstep (se 2 (by rfl) ⟨554526, by rfl⟩ : syracuseStep 1478737 = 1109053) B1109053
theorem B921683 : Blo 920579 921683 := bstep (se 1 (by rfl) ⟨691262, by rfl⟩ : syracuseStep 921683 = 1382525) B1382525
theorem B921699 : Blo 920579 921699 := bstep (se 1 (by rfl) ⟨691274, by rfl⟩ : syracuseStep 921699 = 1382549) B1382549
theorem B921715 : Blo 920579 921715 := bstep (se 1 (by rfl) ⟨691286, by rfl⟩ : syracuseStep 921715 = 1382573) B1382573
theorem B921731 : Blo 920579 921731 := bstep (se 1 (by rfl) ⟨691298, by rfl⟩ : syracuseStep 921731 = 1382597) B1382597
theorem B2953361 : Blo 920579 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B921747 : Blo 920579 921747 := bstep (se 1 (by rfl) ⟨691310, by rfl⟩ : syracuseStep 921747 = 1382621) B1382621
theorem B921763 : Blo 920579 921763 := bstep (se 1 (by rfl) ⟨691322, by rfl⟩ : syracuseStep 921763 = 1382645) B1382645
theorem B921779 : Blo 920579 921779 := bstep (se 1 (by rfl) ⟨691334, by rfl⟩ : syracuseStep 921779 = 1382669) B1382669
theorem B921795 : Blo 920579 921795 := bstep (se 1 (by rfl) ⟨691346, by rfl⟩ : syracuseStep 921795 = 1382693) B1382693
theorem B921811 : Blo 920579 921811 := bstep (se 1 (by rfl) ⟨691358, by rfl⟩ : syracuseStep 921811 = 1382717) B1382717
theorem B921827 : Blo 920579 921827 := bstep (se 1 (by rfl) ⟨691370, by rfl⟩ : syracuseStep 921827 = 1382741) B1382741
theorem B3510499 : Blo 920579 3510499 := bstep (se 1 (by rfl) ⟨2632874, by rfl⟩ : syracuseStep 3510499 = 5265749) B5265749
theorem B921843 : Blo 920579 921843 := bstep (se 1 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 921843 = 1382765) B1382765
theorem B921859 : Blo 920579 921859 := bstep (se 1 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 921859 = 1382789) B1382789
theorem B921875 : Blo 920579 921875 := bstep (se 1 (by rfl) ⟨691406, by rfl⟩ : syracuseStep 921875 = 1382813) B1382813
theorem B921891 : Blo 920579 921891 := bstep (se 1 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 921891 = 1382837) B1382837
theorem B921907 : Blo 920579 921907 := bstep (se 1 (by rfl) ⟨691430, by rfl⟩ : syracuseStep 921907 = 1382861) B1382861
theorem B1577267 : Blo 920579 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B921923 : Blo 920579 921923 := bstep (se 1 (by rfl) ⟨691442, by rfl⟩ : syracuseStep 921923 = 1382885) B1382885
theorem B1478993 : Blo 920579 1478993 := bstep (se 2 (by rfl) ⟨554622, by rfl⟩ : syracuseStep 1478993 = 1109245) B1109245
theorem B1872209 : Blo 920579 1872209 := bstep (se 2 (by rfl) ⟨702078, by rfl⟩ : syracuseStep 1872209 = 1404157) B1404157
theorem B921939 : Blo 920579 921939 := bstep (se 1 (by rfl) ⟨691454, by rfl⟩ : syracuseStep 921939 = 1382909) B1382909
theorem B921955 : Blo 920579 921955 := bstep (se 1 (by rfl) ⟨691466, by rfl⟩ : syracuseStep 921955 = 1382933) B1382933
theorem B921971 : Blo 920579 921971 := bstep (se 1 (by rfl) ⟨691478, by rfl⟩ : syracuseStep 921971 = 1382957) B1382957
theorem B3150211 : Blo 920579 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B921987 : Blo 920579 921987 := bstep (se 1 (by rfl) ⟨691490, by rfl⟩ : syracuseStep 921987 = 1382981) B1382981
theorem B922003 : Blo 920579 922003 := bstep (se 1 (by rfl) ⟨691502, by rfl⟩ : syracuseStep 922003 = 1383005) B1383005
theorem B1315219 : Blo 920579 1315219 := bstep (se 1 (by rfl) ⟨986414, by rfl⟩ : syracuseStep 1315219 = 1972829) B1972829
theorem B922019 : Blo 920579 922019 := bstep (se 1 (by rfl) ⟨691514, by rfl⟩ : syracuseStep 922019 = 1383029) B1383029
theorem B922035 : Blo 920579 922035 := bstep (se 1 (by rfl) ⟨691526, by rfl⟩ : syracuseStep 922035 = 1383053) B1383053
theorem B922051 : Blo 920579 922051 := bstep (se 1 (by rfl) ⟨691538, by rfl⟩ : syracuseStep 922051 = 1383077) B1383077
theorem B1872323 : Blo 920579 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B10490309 : Blo 920579 10490309 := bstep (se 4 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 10490309 = 1966933) B1966933
theorem B2331089 : Blo 920579 2331089 := bstep (se 2 (by rfl) ⟨874158, by rfl⟩ : syracuseStep 2331089 = 1748317) B1748317
theorem B922067 : Blo 920579 922067 := bstep (se 1 (by rfl) ⟨691550, by rfl⟩ : syracuseStep 922067 = 1383101) B1383101
theorem B922083 : Blo 920579 922083 := bstep (se 1 (by rfl) ⟨691562, by rfl⟩ : syracuseStep 922083 = 1383125) B1383125
theorem B922099 : Blo 920579 922099 := bstep (se 1 (by rfl) ⟨691574, by rfl⟩ : syracuseStep 922099 = 1383149) B1383149
theorem B2331139 : Blo 920579 2331139 := bstep (se 1 (by rfl) ⟨1748354, by rfl⟩ : syracuseStep 2331139 = 3496709) B3496709
theorem B922115 : Blo 920579 922115 := bstep (se 1 (by rfl) ⟨691586, by rfl⟩ : syracuseStep 922115 = 1383173) B1383173
theorem B3117581 : Blo 920579 3117581 := bstep (se 3 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 3117581 = 1169093) B1169093
theorem B1380881 : Blo 920579 1380881 := bstep (se 2 (by rfl) ⟨517830, by rfl⟩ : syracuseStep 1380881 = 1035661) B1035661
theorem B922131 : Blo 920579 922131 := bstep (se 1 (by rfl) ⟨691598, by rfl⟩ : syracuseStep 922131 = 1383197) B1383197
theorem B1380899 : Blo 920579 1380899 := bstep (se 1 (by rfl) ⟨1035674, by rfl⟩ : syracuseStep 1380899 = 2071349) B2071349
theorem B922147 : Blo 920579 922147 := bstep (se 1 (by rfl) ⟨691610, by rfl⟩ : syracuseStep 922147 = 1383221) B1383221
theorem B922163 : Blo 920579 922163 := bstep (se 1 (by rfl) ⟨691622, by rfl⟩ : syracuseStep 922163 = 1383245) B1383245
theorem B1380929 : Blo 920579 1380929 := bstep (se 2 (by rfl) ⟨517848, by rfl⟩ : syracuseStep 1380929 = 1035697) B1035697
theorem B2363971 : Blo 920579 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B922179 : Blo 920579 922179 := bstep (se 1 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 922179 = 1383269) B1383269
theorem B3117635 : Blo 920579 3117635 := bstep (se 1 (by rfl) ⟨2338226, by rfl⟩ : syracuseStep 3117635 = 4676453) B4676453
theorem B1380947 : Blo 920579 1380947 := bstep (se 1 (by rfl) ⟨1035710, by rfl⟩ : syracuseStep 1380947 = 2071421) B2071421
theorem B922195 : Blo 920579 922195 := bstep (se 1 (by rfl) ⟨691646, by rfl⟩ : syracuseStep 922195 = 1383293) B1383293
theorem B1577569 : Blo 920579 1577569 := bstep (se 2 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 1577569 = 1183177) B1183177
theorem B922211 : Blo 920579 922211 := bstep (se 1 (by rfl) ⟨691658, by rfl⟩ : syracuseStep 922211 = 1383317) B1383317
theorem B1380977 : Blo 920579 1380977 := bstep (se 2 (by rfl) ⟨517866, by rfl⟩ : syracuseStep 1380977 = 1035733) B1035733
theorem B7115377 : Blo 920579 7115377 := bstep (se 2 (by rfl) ⟨2668266, by rfl⟩ : syracuseStep 7115377 = 5336533) B5336533
theorem B922227 : Blo 920579 922227 := bstep (se 1 (by rfl) ⟨691670, by rfl⟩ : syracuseStep 922227 = 1383341) B1383341
theorem B1380995 : Blo 920579 1380995 := bstep (se 1 (by rfl) ⟨1035746, by rfl⟩ : syracuseStep 1380995 = 2071493) B2071493
theorem B2101891 : Blo 920579 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B922243 : Blo 920579 922243 := bstep (se 1 (by rfl) ⟨691682, by rfl⟩ : syracuseStep 922243 = 1383365) B1383365
theorem B2331281 : Blo 920579 2331281 := bstep (se 2 (by rfl) ⟨874230, by rfl⟩ : syracuseStep 2331281 = 1748461) B1748461
theorem B922259 : Blo 920579 922259 := bstep (se 1 (by rfl) ⟨691694, by rfl⟩ : syracuseStep 922259 = 1383389) B1383389
theorem B1381025 : Blo 920579 1381025 := bstep (se 2 (by rfl) ⟨517884, by rfl⟩ : syracuseStep 1381025 = 1035769) B1035769
theorem B922275 : Blo 920579 922275 := bstep (se 1 (by rfl) ⟨691706, by rfl⟩ : syracuseStep 922275 = 1383413) B1383413
theorem B1184419 : Blo 920579 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B1381043 : Blo 920579 1381043 := bstep (se 1 (by rfl) ⟨1035782, by rfl⟩ : syracuseStep 1381043 = 2071565) B2071565
theorem B922291 : Blo 920579 922291 := bstep (se 1 (by rfl) ⟨691718, by rfl⟩ : syracuseStep 922291 = 1383437) B1383437
theorem B922307 : Blo 920579 922307 := bstep (se 1 (by rfl) ⟨691730, by rfl⟩ : syracuseStep 922307 = 1383461) B1383461
theorem B1381073 : Blo 920579 1381073 := bstep (se 2 (by rfl) ⟨517902, by rfl⟩ : syracuseStep 1381073 = 1035805) B1035805
theorem B1970897 : Blo 920579 1970897 := bstep (se 2 (by rfl) ⟨739086, by rfl⟩ : syracuseStep 1970897 = 1478173) B1478173
theorem B922323 : Blo 920579 922323 := bstep (se 1 (by rfl) ⟨691742, by rfl⟩ : syracuseStep 922323 = 1383485) B1383485
theorem B1381091 : Blo 920579 1381091 := bstep (se 1 (by rfl) ⟨1035818, by rfl⟩ : syracuseStep 1381091 = 2071637) B2071637
theorem B3936995 : Blo 920579 3936995 := bstep (se 1 (by rfl) ⟨2952746, by rfl⟩ : syracuseStep 3936995 = 5905493) B5905493
theorem B922339 : Blo 920579 922339 := bstep (se 1 (by rfl) ⟨691754, by rfl⟩ : syracuseStep 922339 = 1383509) B1383509
theorem B922355 : Blo 920579 922355 := bstep (se 1 (by rfl) ⟨691766, by rfl⟩ : syracuseStep 922355 = 1383533) B1383533
theorem B1381121 : Blo 920579 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B922371 : Blo 920579 922371 := bstep (se 1 (by rfl) ⟨691778, by rfl⟩ : syracuseStep 922371 = 1383557) B1383557
theorem B1381139 : Blo 920579 1381139 := bstep (se 1 (by rfl) ⟨1035854, by rfl⟩ : syracuseStep 1381139 = 2071709) B2071709
theorem B922387 : Blo 920579 922387 := bstep (se 1 (by rfl) ⟨691790, by rfl⟩ : syracuseStep 922387 = 1383581) B1383581
theorem B922403 : Blo 920579 922403 := bstep (se 1 (by rfl) ⟨691802, by rfl⟩ : syracuseStep 922403 = 1383605) B1383605
theorem B1381169 : Blo 920579 1381169 := bstep (se 2 (by rfl) ⟨517938, by rfl⟩ : syracuseStep 1381169 = 1035877) B1035877
theorem B922419 : Blo 920579 922419 := bstep (se 1 (by rfl) ⟨691814, by rfl⟩ : syracuseStep 922419 = 1383629) B1383629
theorem B1381187 : Blo 920579 1381187 := bstep (se 1 (by rfl) ⟨1035890, by rfl⟩ : syracuseStep 1381187 = 2071781) B2071781
theorem B922435 : Blo 920579 922435 := bstep (se 1 (by rfl) ⟨691826, by rfl⟩ : syracuseStep 922435 = 1383653) B1383653
theorem B3117905 : Blo 920579 3117905 := bstep (se 2 (by rfl) ⟨1169214, by rfl⟩ : syracuseStep 3117905 = 2338429) B2338429
theorem B922451 : Blo 920579 922451 := bstep (se 1 (by rfl) ⟨691838, by rfl⟩ : syracuseStep 922451 = 1383677) B1383677
theorem B1381217 : Blo 920579 1381217 := bstep (se 2 (by rfl) ⟨517956, by rfl⟩ : syracuseStep 1381217 = 1035913) B1035913
theorem B922467 : Blo 920579 922467 := bstep (se 1 (by rfl) ⟨691850, by rfl⟩ : syracuseStep 922467 = 1383701) B1383701
theorem B1381235 : Blo 920579 1381235 := bstep (se 1 (by rfl) ⟨1035926, by rfl⟩ : syracuseStep 1381235 = 2071853) B2071853
theorem B922483 : Blo 920579 922483 := bstep (se 1 (by rfl) ⟨691862, by rfl⟩ : syracuseStep 922483 = 1383725) B1383725
theorem B922499 : Blo 920579 922499 := bstep (se 1 (by rfl) ⟨691874, by rfl⟩ : syracuseStep 922499 = 1383749) B1383749
theorem B1381265 : Blo 920579 1381265 := bstep (se 2 (by rfl) ⟨517974, by rfl⟩ : syracuseStep 1381265 = 1035949) B1035949
theorem B922515 : Blo 920579 922515 := bstep (se 1 (by rfl) ⟨691886, by rfl⟩ : syracuseStep 922515 = 1383773) B1383773
theorem B1381283 : Blo 920579 1381283 := bstep (se 1 (by rfl) ⟨1035962, by rfl⟩ : syracuseStep 1381283 = 2071925) B2071925
theorem B922531 : Blo 920579 922531 := bstep (se 1 (by rfl) ⟨691898, by rfl⟩ : syracuseStep 922531 = 1383797) B1383797
theorem B922547 : Blo 920579 922547 := bstep (se 1 (by rfl) ⟨691910, by rfl⟩ : syracuseStep 922547 = 1383821) B1383821
theorem B1381313 : Blo 920579 1381313 := bstep (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) B1035985
theorem B922563 : Blo 920579 922563 := bstep (se 1 (by rfl) ⟨691922, by rfl⟩ : syracuseStep 922563 = 1383845) B1383845
theorem B1315777 : Blo 920579 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B1381331 : Blo 920579 1381331 := bstep (se 1 (by rfl) ⟨1035998, by rfl⟩ : syracuseStep 1381331 = 2071997) B2071997
theorem B922579 : Blo 920579 922579 := bstep (se 1 (by rfl) ⟨691934, by rfl⟩ : syracuseStep 922579 = 1383869) B1383869
theorem B922595 : Blo 920579 922595 := bstep (se 1 (by rfl) ⟨691946, by rfl⟩ : syracuseStep 922595 = 1383893) B1383893
theorem B1315811 : Blo 920579 1315811 := bstep (se 1 (by rfl) ⟨986858, by rfl⟩ : syracuseStep 1315811 = 1973717) B1973717
theorem B1381361 : Blo 920579 1381361 := bstep (se 2 (by rfl) ⟨518010, by rfl⟩ : syracuseStep 1381361 = 1036021) B1036021
theorem B922611 : Blo 920579 922611 := bstep (se 1 (by rfl) ⟨691958, by rfl⟩ : syracuseStep 922611 = 1383917) B1383917
theorem B1381379 : Blo 920579 1381379 := bstep (se 1 (by rfl) ⟨1036034, by rfl⟩ : syracuseStep 1381379 = 2072069) B2072069
theorem B2659331 : Blo 920579 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B922627 : Blo 920579 922627 := bstep (se 1 (by rfl) ⟨691970, by rfl⟩ : syracuseStep 922627 = 1383941) B1383941
theorem B2626577 : Blo 920579 2626577 := bstep (se 2 (by rfl) ⟨984966, by rfl⟩ : syracuseStep 2626577 = 1969933) B1969933
theorem B922643 : Blo 920579 922643 := bstep (se 1 (by rfl) ⟨691982, by rfl⟩ : syracuseStep 922643 = 1383965) B1383965
theorem B1381409 : Blo 920579 1381409 := bstep (se 2 (by rfl) ⟨518028, by rfl⟩ : syracuseStep 1381409 = 1036057) B1036057
theorem B922659 : Blo 920579 922659 := bstep (se 1 (by rfl) ⟨691994, by rfl⟩ : syracuseStep 922659 = 1383989) B1383989
theorem B1381427 : Blo 920579 1381427 := bstep (se 1 (by rfl) ⟨1036070, by rfl⟩ : syracuseStep 1381427 = 2072141) B2072141
theorem B922675 : Blo 920579 922675 := bstep (se 1 (by rfl) ⟨692006, by rfl⟩ : syracuseStep 922675 = 1384013) B1384013
theorem B922691 : Blo 920579 922691 := bstep (se 1 (by rfl) ⟨692018, by rfl⟩ : syracuseStep 922691 = 1384037) B1384037
theorem B1381457 : Blo 920579 1381457 := bstep (se 2 (by rfl) ⟨518046, by rfl⟩ : syracuseStep 1381457 = 1036093) B1036093
theorem B922707 : Blo 920579 922707 := bstep (se 1 (by rfl) ⟨692030, by rfl⟩ : syracuseStep 922707 = 1384061) B1384061
theorem B1381475 : Blo 920579 1381475 := bstep (se 1 (by rfl) ⟨1036106, by rfl⟩ : syracuseStep 1381475 = 2072213) B2072213
theorem B922723 : Blo 920579 922723 := bstep (se 1 (by rfl) ⟨692042, by rfl⟩ : syracuseStep 922723 = 1384085) B1384085
theorem B922739 : Blo 920579 922739 := bstep (se 1 (by rfl) ⟨692054, by rfl⟩ : syracuseStep 922739 = 1384109) B1384109
theorem B1381505 : Blo 920579 1381505 := bstep (se 2 (by rfl) ⟨518064, by rfl⟩ : syracuseStep 1381505 = 1036129) B1036129
theorem B922755 : Blo 920579 922755 := bstep (se 1 (by rfl) ⟨692066, by rfl⟩ : syracuseStep 922755 = 1384133) B1384133
theorem B1381523 : Blo 920579 1381523 := bstep (se 1 (by rfl) ⟨1036142, by rfl⟩ : syracuseStep 1381523 = 2072285) B2072285
theorem B922771 : Blo 920579 922771 := bstep (se 1 (by rfl) ⟨692078, by rfl⟩ : syracuseStep 922771 = 1384157) B1384157
theorem B922787 : Blo 920579 922787 := bstep (se 1 (by rfl) ⟨692090, by rfl⟩ : syracuseStep 922787 = 1384181) B1384181
theorem B1381553 : Blo 920579 1381553 := bstep (se 2 (by rfl) ⟨518082, by rfl⟩ : syracuseStep 1381553 = 1036165) B1036165
theorem B922803 : Blo 920579 922803 := bstep (se 1 (by rfl) ⟨692102, by rfl⟩ : syracuseStep 922803 = 1384205) B1384205
theorem B1283251 : Blo 920579 1283251 := bstep (se 1 (by rfl) ⟨962438, by rfl⟩ : syracuseStep 1283251 = 1924877) B1924877
theorem B1381571 : Blo 920579 1381571 := bstep (se 1 (by rfl) ⟨1036178, by rfl⟩ : syracuseStep 1381571 = 2072357) B2072357
theorem B922819 : Blo 920579 922819 := bstep (se 1 (by rfl) ⟨692114, by rfl⟩ : syracuseStep 922819 = 1384229) B1384229
theorem B8426693 : Blo 920579 8426693 := bstep (se 4 (by rfl) ⟨790002, by rfl⟩ : syracuseStep 8426693 = 1580005) B1580005
theorem B2626769 : Blo 920579 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B922835 : Blo 920579 922835 := bstep (se 1 (by rfl) ⟨692126, by rfl⟩ : syracuseStep 922835 = 1384253) B1384253
theorem B1381601 : Blo 920579 1381601 := bstep (se 2 (by rfl) ⟨518100, by rfl⟩ : syracuseStep 1381601 = 1036201) B1036201
theorem B922851 : Blo 920579 922851 := bstep (se 1 (by rfl) ⟨692138, by rfl⟩ : syracuseStep 922851 = 1384277) B1384277
theorem B1381619 : Blo 920579 1381619 := bstep (se 1 (by rfl) ⟨1036214, by rfl⟩ : syracuseStep 1381619 = 2072429) B2072429
theorem B922867 : Blo 920579 922867 := bstep (se 1 (by rfl) ⟨692150, by rfl⟩ : syracuseStep 922867 = 1384301) B1384301
theorem B922883 : Blo 920579 922883 := bstep (se 1 (by rfl) ⟨692162, by rfl⟩ : syracuseStep 922883 = 1384325) B1384325
theorem B1381649 : Blo 920579 1381649 := bstep (se 2 (by rfl) ⟨518118, by rfl⟩ : syracuseStep 1381649 = 1036237) B1036237
theorem B922899 : Blo 920579 922899 := bstep (se 1 (by rfl) ⟨692174, by rfl⟩ : syracuseStep 922899 = 1384349) B1384349
theorem B1381667 : Blo 920579 1381667 := bstep (se 1 (by rfl) ⟨1036250, by rfl⟩ : syracuseStep 1381667 = 2072501) B2072501
theorem B922915 : Blo 920579 922915 := bstep (se 1 (by rfl) ⟨692186, by rfl⟩ : syracuseStep 922915 = 1384373) B1384373
theorem B922931 : Blo 920579 922931 := bstep (se 1 (by rfl) ⟨692198, by rfl⟩ : syracuseStep 922931 = 1384397) B1384397
theorem B1381697 : Blo 920579 1381697 := bstep (se 2 (by rfl) ⟨518136, by rfl⟩ : syracuseStep 1381697 = 1036273) B1036273
theorem B922947 : Blo 920579 922947 := bstep (se 1 (by rfl) ⟨692210, by rfl⟩ : syracuseStep 922947 = 1384421) B1384421
theorem B1381715 : Blo 920579 1381715 := bstep (se 1 (by rfl) ⟨1036286, by rfl⟩ : syracuseStep 1381715 = 2072573) B2072573
theorem B922963 : Blo 920579 922963 := bstep (se 1 (by rfl) ⟨692222, by rfl⟩ : syracuseStep 922963 = 1384445) B1384445
theorem B922979 : Blo 920579 922979 := bstep (se 1 (by rfl) ⟨692234, by rfl⟩ : syracuseStep 922979 = 1384469) B1384469
theorem B3118445 : Blo 920579 3118445 := bstep (se 3 (by rfl) ⟨584708, by rfl⟩ : syracuseStep 3118445 = 1169417) B1169417
theorem B1381745 : Blo 920579 1381745 := bstep (se 2 (by rfl) ⟨518154, by rfl⟩ : syracuseStep 1381745 = 1036309) B1036309
theorem B922995 : Blo 920579 922995 := bstep (se 1 (by rfl) ⟨692246, by rfl⟩ : syracuseStep 922995 = 1384493) B1384493
theorem B1381763 : Blo 920579 1381763 := bstep (se 1 (by rfl) ⟨1036322, by rfl⟩ : syracuseStep 1381763 = 2072645) B2072645
theorem B923011 : Blo 920579 923011 := bstep (se 1 (by rfl) ⟨692258, by rfl⟩ : syracuseStep 923011 = 1384517) B1384517
theorem B8885645 : Blo 920579 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B923027 : Blo 920579 923027 := bstep (se 1 (by rfl) ⟨692270, by rfl⟩ : syracuseStep 923027 = 1384541) B1384541
theorem B1381793 : Blo 920579 1381793 := bstep (se 2 (by rfl) ⟨518172, by rfl⟩ : syracuseStep 1381793 = 1036345) B1036345
theorem B923043 : Blo 920579 923043 := bstep (se 1 (by rfl) ⟨692282, by rfl⟩ : syracuseStep 923043 = 1384565) B1384565
theorem B3118499 : Blo 920579 3118499 := bstep (se 1 (by rfl) ⟨2338874, by rfl⟩ : syracuseStep 3118499 = 4677749) B4677749
theorem B1381811 : Blo 920579 1381811 := bstep (se 1 (by rfl) ⟨1036358, by rfl⟩ : syracuseStep 1381811 = 2072717) B2072717
theorem B923059 : Blo 920579 923059 := bstep (se 1 (by rfl) ⟨692294, by rfl⟩ : syracuseStep 923059 = 1384589) B1384589
theorem B923075 : Blo 920579 923075 := bstep (se 1 (by rfl) ⟨692306, by rfl⟩ : syracuseStep 923075 = 1384613) B1384613
theorem B1381841 : Blo 920579 1381841 := bstep (se 2 (by rfl) ⟨518190, by rfl⟩ : syracuseStep 1381841 = 1036381) B1036381
theorem B923091 : Blo 920579 923091 := bstep (se 1 (by rfl) ⟨692318, by rfl⟩ : syracuseStep 923091 = 1384637) B1384637
theorem B1381859 : Blo 920579 1381859 := bstep (se 1 (by rfl) ⟨1036394, by rfl⟩ : syracuseStep 1381859 = 2072789) B2072789
theorem B923107 : Blo 920579 923107 := bstep (se 1 (by rfl) ⟨692330, by rfl⟩ : syracuseStep 923107 = 1384661) B1384661
theorem B923123 : Blo 920579 923123 := bstep (se 1 (by rfl) ⟨692342, by rfl⟩ : syracuseStep 923123 = 1384685) B1384685
theorem B1381889 : Blo 920579 1381889 := bstep (se 2 (by rfl) ⟨518208, by rfl⟩ : syracuseStep 1381889 = 1036417) B1036417
theorem B923139 : Blo 920579 923139 := bstep (se 1 (by rfl) ⟨692354, by rfl⟩ : syracuseStep 923139 = 1384709) B1384709
theorem B1316369 : Blo 920579 1316369 := bstep (se 2 (by rfl) ⟨493638, by rfl⟩ : syracuseStep 1316369 = 987277) B987277
theorem B1381907 : Blo 920579 1381907 := bstep (se 1 (by rfl) ⟨1036430, by rfl⟩ : syracuseStep 1381907 = 2072861) B2072861
theorem B923155 : Blo 920579 923155 := bstep (se 1 (by rfl) ⟨692366, by rfl⟩ : syracuseStep 923155 = 1384733) B1384733
theorem B923171 : Blo 920579 923171 := bstep (se 1 (by rfl) ⟨692378, by rfl⟩ : syracuseStep 923171 = 1384757) B1384757
theorem B1381937 : Blo 920579 1381937 := bstep (se 2 (by rfl) ⟨518226, by rfl⟩ : syracuseStep 1381937 = 1036453) B1036453
theorem B923187 : Blo 920579 923187 := bstep (se 1 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 923187 = 1384781) B1384781
theorem B1381955 : Blo 920579 1381955 := bstep (se 1 (by rfl) ⟨1036466, by rfl⟩ : syracuseStep 1381955 = 2072933) B2072933
theorem B923203 : Blo 920579 923203 := bstep (se 1 (by rfl) ⟨692402, by rfl⟩ : syracuseStep 923203 = 1384805) B1384805
theorem B923219 : Blo 920579 923219 := bstep (se 1 (by rfl) ⟨692414, by rfl⟩ : syracuseStep 923219 = 1384829) B1384829
theorem B1381985 : Blo 920579 1381985 := bstep (se 2 (by rfl) ⟨518244, by rfl⟩ : syracuseStep 1381985 = 1036489) B1036489
theorem B923235 : Blo 920579 923235 := bstep (se 1 (by rfl) ⟨692426, by rfl⟩ : syracuseStep 923235 = 1384853) B1384853
theorem B2332273 : Blo 920579 2332273 := bstep (se 2 (by rfl) ⟨874602, by rfl⟩ : syracuseStep 2332273 = 1749205) B1749205
theorem B1382003 : Blo 920579 1382003 := bstep (se 1 (by rfl) ⟨1036502, by rfl⟩ : syracuseStep 1382003 = 2073005) B2073005
theorem B923251 : Blo 920579 923251 := bstep (se 1 (by rfl) ⟨692438, by rfl⟩ : syracuseStep 923251 = 1384877) B1384877
theorem B2102915 : Blo 920579 2102915 := bstep (se 1 (by rfl) ⟨1577186, by rfl⟩ : syracuseStep 2102915 = 3154373) B3154373
theorem B923267 : Blo 920579 923267 := bstep (se 1 (by rfl) ⟨692450, by rfl⟩ : syracuseStep 923267 = 1384901) B1384901
theorem B1382033 : Blo 920579 1382033 := bstep (se 2 (by rfl) ⟨518262, by rfl⟩ : syracuseStep 1382033 = 1036525) B1036525
theorem B923283 : Blo 920579 923283 := bstep (se 1 (by rfl) ⟨692462, by rfl⟩ : syracuseStep 923283 = 1384925) B1384925
theorem B1382051 : Blo 920579 1382051 := bstep (se 1 (by rfl) ⟨1036538, by rfl⟩ : syracuseStep 1382051 = 2073077) B2073077
theorem B923299 : Blo 920579 923299 := bstep (se 1 (by rfl) ⟨692474, by rfl⟩ : syracuseStep 923299 = 1384949) B1384949
theorem B3118769 : Blo 920579 3118769 := bstep (se 2 (by rfl) ⟨1169538, by rfl⟩ : syracuseStep 3118769 = 2339077) B2339077
theorem B923315 : Blo 920579 923315 := bstep (se 1 (by rfl) ⟨692486, by rfl⟩ : syracuseStep 923315 = 1384973) B1384973
theorem B1382081 : Blo 920579 1382081 := bstep (se 2 (by rfl) ⟨518280, by rfl⟩ : syracuseStep 1382081 = 1036561) B1036561
theorem B923331 : Blo 920579 923331 := bstep (se 1 (by rfl) ⟨692498, by rfl⟩ : syracuseStep 923331 = 1384997) B1384997
theorem B5248709 : Blo 920579 5248709 := bstep (se 4 (by rfl) ⟨492066, by rfl⟩ : syracuseStep 5248709 = 984133) B984133
theorem B1382099 : Blo 920579 1382099 := bstep (se 1 (by rfl) ⟨1036574, by rfl⟩ : syracuseStep 1382099 = 2073149) B2073149
theorem B923347 : Blo 920579 923347 := bstep (se 1 (by rfl) ⟨692510, by rfl⟩ : syracuseStep 923347 = 1385021) B1385021
theorem B1480403 : Blo 920579 1480403 := bstep (se 1 (by rfl) ⟨1110302, by rfl⟩ : syracuseStep 1480403 = 2220605) B2220605
theorem B923363 : Blo 920579 923363 := bstep (se 1 (by rfl) ⟨692522, by rfl⟩ : syracuseStep 923363 = 1385045) B1385045
theorem B7870193 : Blo 920579 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B1382129 : Blo 920579 1382129 := bstep (se 2 (by rfl) ⟨518298, by rfl⟩ : syracuseStep 1382129 = 1036597) B1036597
theorem B923379 : Blo 920579 923379 := bstep (se 1 (by rfl) ⟨692534, by rfl⟩ : syracuseStep 923379 = 1385069) B1385069
theorem B1382147 : Blo 920579 1382147 := bstep (se 1 (by rfl) ⟨1036610, by rfl⟩ : syracuseStep 1382147 = 2073221) B2073221
theorem B923395 : Blo 920579 923395 := bstep (se 1 (by rfl) ⟨692546, by rfl⟩ : syracuseStep 923395 = 1385093) B1385093
theorem B923411 : Blo 920579 923411 := bstep (se 1 (by rfl) ⟨692558, by rfl⟩ : syracuseStep 923411 = 1385117) B1385117
theorem B1382177 : Blo 920579 1382177 := bstep (se 2 (by rfl) ⟨518316, by rfl⟩ : syracuseStep 1382177 = 1036633) B1036633
theorem B923427 : Blo 920579 923427 := bstep (se 1 (by rfl) ⟨692570, by rfl⟩ : syracuseStep 923427 = 1385141) B1385141
theorem B1382195 : Blo 920579 1382195 := bstep (se 1 (by rfl) ⟨1036646, by rfl⟩ : syracuseStep 1382195 = 2073293) B2073293
theorem B923443 : Blo 920579 923443 := bstep (se 1 (by rfl) ⟨692582, by rfl⟩ : syracuseStep 923443 = 1385165) B1385165
theorem B923459 : Blo 920579 923459 := bstep (se 1 (by rfl) ⟨692594, by rfl⟩ : syracuseStep 923459 = 1385189) B1385189
theorem B1382225 : Blo 920579 1382225 := bstep (se 2 (by rfl) ⟨518334, by rfl⟩ : syracuseStep 1382225 = 1036669) B1036669
theorem B923475 : Blo 920579 923475 := bstep (se 1 (by rfl) ⟨692606, by rfl⟩ : syracuseStep 923475 = 1385213) B1385213
theorem B1382243 : Blo 920579 1382243 := bstep (se 1 (by rfl) ⟨1036682, by rfl⟩ : syracuseStep 1382243 = 2073365) B2073365
theorem B923491 : Blo 920579 923491 := bstep (se 1 (by rfl) ⟨692618, by rfl⟩ : syracuseStep 923491 = 1385237) B1385237
theorem B923507 : Blo 920579 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B1382273 : Blo 920579 1382273 := bstep (se 2 (by rfl) ⟨518352, by rfl⟩ : syracuseStep 1382273 = 1036705) B1036705
theorem B2332547 : Blo 920579 2332547 := bstep (se 1 (by rfl) ⟨1749410, by rfl⟩ : syracuseStep 2332547 = 3498821) B3498821
theorem B923523 : Blo 920579 923523 := bstep (se 1 (by rfl) ⟨692642, by rfl⟩ : syracuseStep 923523 = 1385285) B1385285
theorem B1382291 : Blo 920579 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B923539 : Blo 920579 923539 := bstep (se 1 (by rfl) ⟨692654, by rfl⟩ : syracuseStep 923539 = 1385309) B1385309
theorem B923555 : Blo 920579 923555 := bstep (se 1 (by rfl) ⟨692666, by rfl⟩ : syracuseStep 923555 = 1385333) B1385333
theorem B1382321 : Blo 920579 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B1775537 : Blo 920579 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B923571 : Blo 920579 923571 := bstep (se 1 (by rfl) ⟨692678, by rfl⟩ : syracuseStep 923571 = 1385357) B1385357
theorem B1382339 : Blo 920579 1382339 := bstep (se 1 (by rfl) ⟨1036754, by rfl⟩ : syracuseStep 1382339 = 2073509) B2073509
theorem B923587 : Blo 920579 923587 := bstep (se 1 (by rfl) ⟨692690, by rfl⟩ : syracuseStep 923587 = 1385381) B1385381
theorem B923603 : Blo 920579 923603 := bstep (se 1 (by rfl) ⟨692702, by rfl⟩ : syracuseStep 923603 = 1385405) B1385405
theorem B1382369 : Blo 920579 1382369 := bstep (se 2 (by rfl) ⟨518388, by rfl⟩ : syracuseStep 1382369 = 1036777) B1036777
theorem B923619 : Blo 920579 923619 := bstep (se 1 (by rfl) ⟨692714, by rfl⟩ : syracuseStep 923619 = 1385429) B1385429
theorem B1382387 : Blo 920579 1382387 := bstep (se 1 (by rfl) ⟨1036790, by rfl⟩ : syracuseStep 1382387 = 2073581) B2073581
theorem B923635 : Blo 920579 923635 := bstep (se 1 (by rfl) ⟨692726, by rfl⟩ : syracuseStep 923635 = 1385453) B1385453
theorem B923651 : Blo 920579 923651 := bstep (se 1 (by rfl) ⟨692738, by rfl⟩ : syracuseStep 923651 = 1385477) B1385477
theorem B1382417 : Blo 920579 1382417 := bstep (se 2 (by rfl) ⟨518406, by rfl⟩ : syracuseStep 1382417 = 1036813) B1036813
theorem B923667 : Blo 920579 923667 := bstep (se 1 (by rfl) ⟨692750, by rfl⟩ : syracuseStep 923667 = 1385501) B1385501
theorem B1382435 : Blo 920579 1382435 := bstep (se 1 (by rfl) ⟨1036826, by rfl⟩ : syracuseStep 1382435 = 2073653) B2073653
theorem B923683 : Blo 920579 923683 := bstep (se 1 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 923683 = 1385525) B1385525
theorem B923699 : Blo 920579 923699 := bstep (se 1 (by rfl) ⟨692774, by rfl⟩ : syracuseStep 923699 = 1385549) B1385549
theorem B1382465 : Blo 920579 1382465 := bstep (se 2 (by rfl) ⟨518424, by rfl⟩ : syracuseStep 1382465 = 1036849) B1036849
theorem B2332739 : Blo 920579 2332739 := bstep (se 1 (by rfl) ⟨1749554, by rfl⟩ : syracuseStep 2332739 = 3499109) B3499109
theorem B923715 : Blo 920579 923715 := bstep (se 1 (by rfl) ⟨692786, by rfl⟩ : syracuseStep 923715 = 1385573) B1385573
theorem B1382483 : Blo 920579 1382483 := bstep (se 1 (by rfl) ⟨1036862, by rfl⟩ : syracuseStep 1382483 = 2073725) B2073725
theorem B923731 : Blo 920579 923731 := bstep (se 1 (by rfl) ⟨692798, by rfl⟩ : syracuseStep 923731 = 1385597) B1385597
theorem B923747 : Blo 920579 923747 := bstep (se 1 (by rfl) ⟨692810, by rfl⟩ : syracuseStep 923747 = 1385621) B1385621
theorem B1382513 : Blo 920579 1382513 := bstep (se 2 (by rfl) ⟨518442, by rfl⟩ : syracuseStep 1382513 = 1036885) B1036885
theorem B923763 : Blo 920579 923763 := bstep (se 1 (by rfl) ⟨692822, by rfl⟩ : syracuseStep 923763 = 1385645) B1385645
theorem B1185907 : Blo 920579 1185907 := bstep (se 1 (by rfl) ⟨889430, by rfl⟩ : syracuseStep 1185907 = 1778861) B1778861
theorem B1382531 : Blo 920579 1382531 := bstep (se 1 (by rfl) ⟨1036898, by rfl⟩ : syracuseStep 1382531 = 2073797) B2073797
theorem B923779 : Blo 920579 923779 := bstep (se 1 (by rfl) ⟨692834, by rfl⟩ : syracuseStep 923779 = 1385669) B1385669
theorem B923795 : Blo 920579 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B1382561 : Blo 920579 1382561 := bstep (se 2 (by rfl) ⟨518460, by rfl⟩ : syracuseStep 1382561 = 1036921) B1036921
theorem B923811 : Blo 920579 923811 := bstep (se 1 (by rfl) ⟨692858, by rfl⟩ : syracuseStep 923811 = 1385717) B1385717
theorem B2627761 : Blo 920579 2627761 := bstep (se 2 (by rfl) ⟨985410, by rfl⟩ : syracuseStep 2627761 = 1970821) B1970821
theorem B1382579 : Blo 920579 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B923827 : Blo 920579 923827 := bstep (se 1 (by rfl) ⟨692870, by rfl⟩ : syracuseStep 923827 = 1385741) B1385741
theorem B923843 : Blo 920579 923843 := bstep (se 1 (by rfl) ⟨692882, by rfl⟩ : syracuseStep 923843 = 1385765) B1385765
theorem B3119309 : Blo 920579 3119309 := bstep (se 3 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 3119309 = 1169741) B1169741
theorem B1382609 : Blo 920579 1382609 := bstep (se 2 (by rfl) ⟨518478, by rfl⟩ : syracuseStep 1382609 = 1036957) B1036957
theorem B923859 : Blo 920579 923859 := bstep (se 1 (by rfl) ⟨692894, by rfl⟩ : syracuseStep 923859 = 1385789) B1385789
theorem B1382627 : Blo 920579 1382627 := bstep (se 1 (by rfl) ⟨1036970, by rfl⟩ : syracuseStep 1382627 = 2073941) B2073941
theorem B923875 : Blo 920579 923875 := bstep (se 1 (by rfl) ⟨692906, by rfl⟩ : syracuseStep 923875 = 1385813) B1385813
theorem B923891 : Blo 920579 923891 := bstep (se 1 (by rfl) ⟨692918, by rfl⟩ : syracuseStep 923891 = 1385837) B1385837
theorem B1382657 : Blo 920579 1382657 := bstep (se 2 (by rfl) ⟨518496, by rfl⟩ : syracuseStep 1382657 = 1036993) B1036993
theorem B923907 : Blo 920579 923907 := bstep (se 1 (by rfl) ⟨692930, by rfl⟩ : syracuseStep 923907 = 1385861) B1385861
theorem B3119363 : Blo 920579 3119363 := bstep (se 1 (by rfl) ⟨2339522, by rfl⟩ : syracuseStep 3119363 = 4679045) B4679045
theorem B1382675 : Blo 920579 1382675 := bstep (se 1 (by rfl) ⟨1037006, by rfl⟩ : syracuseStep 1382675 = 2074013) B2074013
theorem B923923 : Blo 920579 923923 := bstep (se 1 (by rfl) ⟨692942, by rfl⟩ : syracuseStep 923923 = 1385885) B1385885
theorem B923939 : Blo 920579 923939 := bstep (se 1 (by rfl) ⟨692954, by rfl⟩ : syracuseStep 923939 = 1385909) B1385909
theorem B1382705 : Blo 920579 1382705 := bstep (se 2 (by rfl) ⟨518514, by rfl⟩ : syracuseStep 1382705 = 1037029) B1037029
theorem B3742001 : Blo 920579 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B923955 : Blo 920579 923955 := bstep (se 1 (by rfl) ⟨692966, by rfl⟩ : syracuseStep 923955 = 1385933) B1385933
theorem B1382723 : Blo 920579 1382723 := bstep (se 1 (by rfl) ⟨1037042, by rfl⟩ : syracuseStep 1382723 = 2074085) B2074085
theorem B923971 : Blo 920579 923971 := bstep (se 1 (by rfl) ⟨692978, by rfl⟩ : syracuseStep 923971 = 1385957) B1385957
theorem B923987 : Blo 920579 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B1382753 : Blo 920579 1382753 := bstep (se 2 (by rfl) ⟨518532, by rfl⟩ : syracuseStep 1382753 = 1037065) B1037065
theorem B924003 : Blo 920579 924003 := bstep (se 1 (by rfl) ⟨693002, by rfl⟩ : syracuseStep 924003 = 1386005) B1386005
theorem B2955629 : Blo 920579 2955629 := bstep (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) B1108361
theorem B5249393 : Blo 920579 5249393 := bstep (se 2 (by rfl) ⟨1968522, by rfl⟩ : syracuseStep 5249393 = 3937045) B3937045
theorem B1382771 : Blo 920579 1382771 := bstep (se 1 (by rfl) ⟨1037078, by rfl⟩ : syracuseStep 1382771 = 2074157) B2074157
theorem B924019 : Blo 920579 924019 := bstep (se 1 (by rfl) ⟨693014, by rfl⟩ : syracuseStep 924019 = 1386029) B1386029
theorem B924035 : Blo 920579 924035 := bstep (se 1 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 924035 = 1386053) B1386053
theorem B2529677 : Blo 920579 2529677 := bstep (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) B948629
theorem B1382801 : Blo 920579 1382801 := bstep (se 2 (by rfl) ⟨518550, by rfl⟩ : syracuseStep 1382801 = 1037101) B1037101
theorem B924051 : Blo 920579 924051 := bstep (se 1 (by rfl) ⟨693038, by rfl⟩ : syracuseStep 924051 = 1386077) B1386077
theorem B1382819 : Blo 920579 1382819 := bstep (se 1 (by rfl) ⟨1037114, by rfl⟩ : syracuseStep 1382819 = 2074229) B2074229
theorem B924067 : Blo 920579 924067 := bstep (se 1 (by rfl) ⟨693050, by rfl⟩ : syracuseStep 924067 = 1386101) B1386101
theorem B924083 : Blo 920579 924083 := bstep (se 1 (by rfl) ⟨693062, by rfl⟩ : syracuseStep 924083 = 1386125) B1386125
theorem B1382849 : Blo 920579 1382849 := bstep (se 2 (by rfl) ⟨518568, by rfl⟩ : syracuseStep 1382849 = 1037137) B1037137
theorem B2628035 : Blo 920579 2628035 := bstep (se 1 (by rfl) ⟨1971026, by rfl⟩ : syracuseStep 2628035 = 3942053) B3942053
theorem B924099 : Blo 920579 924099 := bstep (se 1 (by rfl) ⟨693074, by rfl⟩ : syracuseStep 924099 = 1386149) B1386149
theorem B1382867 : Blo 920579 1382867 := bstep (se 1 (by rfl) ⟨1037150, by rfl⟩ : syracuseStep 1382867 = 2074301) B2074301
theorem B924115 : Blo 920579 924115 := bstep (se 1 (by rfl) ⟨693086, by rfl⟩ : syracuseStep 924115 = 1386173) B1386173
theorem B924131 : Blo 920579 924131 := bstep (se 1 (by rfl) ⟨693098, by rfl⟩ : syracuseStep 924131 = 1386197) B1386197
theorem B1382897 : Blo 920579 1382897 := bstep (se 2 (by rfl) ⟨518586, by rfl⟩ : syracuseStep 1382897 = 1037173) B1037173
theorem B924147 : Blo 920579 924147 := bstep (se 1 (by rfl) ⟨693110, by rfl⟩ : syracuseStep 924147 = 1386221) B1386221
theorem B1382915 : Blo 920579 1382915 := bstep (se 1 (by rfl) ⟨1037186, by rfl⟩ : syracuseStep 1382915 = 2074373) B2074373
theorem B924163 : Blo 920579 924163 := bstep (se 1 (by rfl) ⟨693122, by rfl⟩ : syracuseStep 924163 = 1386245) B1386245
theorem B3119633 : Blo 920579 3119633 := bstep (se 2 (by rfl) ⟨1169862, by rfl⟩ : syracuseStep 3119633 = 2339725) B2339725
theorem B924179 : Blo 920579 924179 := bstep (se 1 (by rfl) ⟨693134, by rfl⟩ : syracuseStep 924179 = 1386269) B1386269
theorem B1382945 : Blo 920579 1382945 := bstep (se 2 (by rfl) ⟨518604, by rfl⟩ : syracuseStep 1382945 = 1037209) B1037209
theorem B924195 : Blo 920579 924195 := bstep (se 1 (by rfl) ⟨693146, by rfl⟩ : syracuseStep 924195 = 1386293) B1386293
theorem B1382963 : Blo 920579 1382963 := bstep (se 1 (by rfl) ⟨1037222, by rfl⟩ : syracuseStep 1382963 = 2074445) B2074445
theorem B924211 : Blo 920579 924211 := bstep (se 1 (by rfl) ⟨693158, by rfl⟩ : syracuseStep 924211 = 1386317) B1386317
theorem B924227 : Blo 920579 924227 := bstep (se 1 (by rfl) ⟨693170, by rfl⟩ : syracuseStep 924227 = 1386341) B1386341
theorem B1382993 : Blo 920579 1382993 := bstep (se 2 (by rfl) ⟨518622, by rfl⟩ : syracuseStep 1382993 = 1037245) B1037245
theorem B924243 : Blo 920579 924243 := bstep (se 1 (by rfl) ⟨693182, by rfl⟩ : syracuseStep 924243 = 1386365) B1386365
theorem B1383011 : Blo 920579 1383011 := bstep (se 1 (by rfl) ⟨1037258, by rfl⟩ : syracuseStep 1383011 = 2074517) B2074517
theorem B924259 : Blo 920579 924259 := bstep (se 1 (by rfl) ⟨693194, by rfl⟩ : syracuseStep 924259 = 1386389) B1386389
theorem B924275 : Blo 920579 924275 := bstep (se 1 (by rfl) ⟨693206, by rfl⟩ : syracuseStep 924275 = 1386413) B1386413
theorem B1383041 : Blo 920579 1383041 := bstep (se 2 (by rfl) ⟨518640, by rfl⟩ : syracuseStep 1383041 = 1037281) B1037281
theorem B2628227 : Blo 920579 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B924291 : Blo 920579 924291 := bstep (se 1 (by rfl) ⟨693218, by rfl⟩ : syracuseStep 924291 = 1386437) B1386437
theorem B1383059 : Blo 920579 1383059 := bstep (se 1 (by rfl) ⟨1037294, by rfl⟩ : syracuseStep 1383059 = 2074589) B2074589
theorem B924307 : Blo 920579 924307 := bstep (se 1 (by rfl) ⟨693230, by rfl⟩ : syracuseStep 924307 = 1386461) B1386461
theorem B924323 : Blo 920579 924323 := bstep (se 1 (by rfl) ⟨693242, by rfl⟩ : syracuseStep 924323 = 1386485) B1386485
theorem B1383089 : Blo 920579 1383089 := bstep (se 2 (by rfl) ⟨518658, by rfl⟩ : syracuseStep 1383089 = 1037317) B1037317
theorem B3938993 : Blo 920579 3938993 := bstep (se 2 (by rfl) ⟨1477122, by rfl⟩ : syracuseStep 3938993 = 2954245) B2954245
theorem B924339 : Blo 920579 924339 := bstep (se 1 (by rfl) ⟨693254, by rfl⟩ : syracuseStep 924339 = 1386509) B1386509
theorem B1383107 : Blo 920579 1383107 := bstep (se 1 (by rfl) ⟨1037330, by rfl⟩ : syracuseStep 1383107 = 2074661) B2074661
theorem B924355 : Blo 920579 924355 := bstep (se 1 (by rfl) ⟨693266, by rfl⟩ : syracuseStep 924355 = 1386533) B1386533
theorem B924371 : Blo 920579 924371 := bstep (se 1 (by rfl) ⟨693278, by rfl⟩ : syracuseStep 924371 = 1386557) B1386557
theorem B1383137 : Blo 920579 1383137 := bstep (se 2 (by rfl) ⟨518676, by rfl⟩ : syracuseStep 1383137 = 1037353) B1037353
theorem B924387 : Blo 920579 924387 := bstep (se 1 (by rfl) ⟨693290, by rfl⟩ : syracuseStep 924387 = 1386581) B1386581
theorem B1383155 : Blo 920579 1383155 := bstep (se 1 (by rfl) ⟨1037366, by rfl⟩ : syracuseStep 1383155 = 2074733) B2074733
theorem B924403 : Blo 920579 924403 := bstep (se 1 (by rfl) ⟨693302, by rfl⟩ : syracuseStep 924403 = 1386605) B1386605
theorem B924419 : Blo 920579 924419 := bstep (se 1 (by rfl) ⟨693314, by rfl⟩ : syracuseStep 924419 = 1386629) B1386629
theorem B2071313 : Blo 920579 2071313 := bstep (se 2 (by rfl) ⟨776742, by rfl⟩ : syracuseStep 2071313 = 1553485) B1553485
theorem B1383185 : Blo 920579 1383185 := bstep (se 2 (by rfl) ⟨518694, by rfl⟩ : syracuseStep 1383185 = 1037389) B1037389
theorem B924435 : Blo 920579 924435 := bstep (se 1 (by rfl) ⟨693326, by rfl⟩ : syracuseStep 924435 = 1386653) B1386653
theorem B2071331 : Blo 920579 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B1383203 : Blo 920579 1383203 := bstep (se 1 (by rfl) ⟨1037402, by rfl⟩ : syracuseStep 1383203 = 2074805) B2074805
theorem B2497315 : Blo 920579 2497315 := bstep (se 1 (by rfl) ⟨1872986, by rfl⟩ : syracuseStep 2497315 = 3745973) B3745973
theorem B924451 : Blo 920579 924451 := bstep (se 1 (by rfl) ⟨693338, by rfl⟩ : syracuseStep 924451 = 1386677) B1386677
theorem B924467 : Blo 920579 924467 := bstep (se 1 (by rfl) ⟨693350, by rfl⟩ : syracuseStep 924467 = 1386701) B1386701
theorem B1383233 : Blo 920579 1383233 := bstep (se 2 (by rfl) ⟨518712, by rfl⟩ : syracuseStep 1383233 = 1037425) B1037425
theorem B924483 : Blo 920579 924483 := bstep (se 1 (by rfl) ⟨693362, by rfl⟩ : syracuseStep 924483 = 1386725) B1386725
theorem B1383251 : Blo 920579 1383251 := bstep (se 1 (by rfl) ⟨1037438, by rfl⟩ : syracuseStep 1383251 = 2074877) B2074877
theorem B924499 : Blo 920579 924499 := bstep (se 1 (by rfl) ⟨693374, by rfl⟩ : syracuseStep 924499 = 1386749) B1386749
theorem B924515 : Blo 920579 924515 := bstep (se 1 (by rfl) ⟨693386, by rfl⟩ : syracuseStep 924515 = 1386773) B1386773
theorem B1383281 : Blo 920579 1383281 := bstep (se 2 (by rfl) ⟨518730, by rfl⟩ : syracuseStep 1383281 = 1037461) B1037461
theorem B924531 : Blo 920579 924531 := bstep (se 1 (by rfl) ⟨693398, by rfl⟩ : syracuseStep 924531 = 1386797) B1386797
theorem B1383299 : Blo 920579 1383299 := bstep (se 1 (by rfl) ⟨1037474, by rfl⟩ : syracuseStep 1383299 = 2074949) B2074949
theorem B924547 : Blo 920579 924547 := bstep (se 1 (by rfl) ⟨693410, by rfl⟩ : syracuseStep 924547 = 1386821) B1386821
theorem B924563 : Blo 920579 924563 := bstep (se 1 (by rfl) ⟨693422, by rfl⟩ : syracuseStep 924563 = 1386845) B1386845
theorem B1383329 : Blo 920579 1383329 := bstep (se 2 (by rfl) ⟨518748, by rfl⟩ : syracuseStep 1383329 = 1037497) B1037497
theorem B924579 : Blo 920579 924579 := bstep (se 1 (by rfl) ⟨693434, by rfl⟩ : syracuseStep 924579 = 1386869) B1386869
theorem B1383347 : Blo 920579 1383347 := bstep (se 1 (by rfl) ⟨1037510, by rfl⟩ : syracuseStep 1383347 = 2075021) B2075021
theorem B1383377 : Blo 920579 1383377 := bstep (se 2 (by rfl) ⟨518766, by rfl⟩ : syracuseStep 1383377 = 1037533) B1037533
theorem B1383395 : Blo 920579 1383395 := bstep (se 1 (by rfl) ⟨1037546, by rfl⟩ : syracuseStep 1383395 = 2075093) B2075093
theorem B2333681 : Blo 920579 2333681 := bstep (se 2 (by rfl) ⟨875130, by rfl⟩ : syracuseStep 2333681 = 1750261) B1750261
theorem B1383425 : Blo 920579 1383425 := bstep (se 2 (by rfl) ⟨518784, by rfl⟩ : syracuseStep 1383425 = 1037569) B1037569
theorem B1383443 : Blo 920579 1383443 := bstep (se 1 (by rfl) ⟨1037582, by rfl⟩ : syracuseStep 1383443 = 2075165) B2075165
theorem B2333731 : Blo 920579 2333731 := bstep (se 1 (by rfl) ⟨1750298, by rfl⟩ : syracuseStep 2333731 = 3500597) B3500597
theorem B3120173 : Blo 920579 3120173 := bstep (se 3 (by rfl) ⟨585032, by rfl⟩ : syracuseStep 3120173 = 1170065) B1170065
theorem B2071601 : Blo 920579 2071601 := bstep (se 2 (by rfl) ⟨776850, by rfl⟩ : syracuseStep 2071601 = 1553701) B1553701
theorem B1383473 : Blo 920579 1383473 := bstep (se 2 (by rfl) ⟨518802, by rfl⟩ : syracuseStep 1383473 = 1037605) B1037605
theorem B2071619 : Blo 920579 2071619 := bstep (se 1 (by rfl) ⟨1553714, by rfl⟩ : syracuseStep 2071619 = 3107429) B3107429
theorem B1383491 : Blo 920579 1383491 := bstep (se 1 (by rfl) ⟨1037618, by rfl⟩ : syracuseStep 1383491 = 2075237) B2075237
theorem B2530381 : Blo 920579 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B1383521 : Blo 920579 1383521 := bstep (se 2 (by rfl) ⟨518820, by rfl⟩ : syracuseStep 1383521 = 1037641) B1037641
theorem B3120227 : Blo 920579 3120227 := bstep (se 1 (by rfl) ⟨2340170, by rfl⟩ : syracuseStep 3120227 = 4680341) B4680341
theorem B1383539 : Blo 920579 1383539 := bstep (se 1 (by rfl) ⟨1037654, by rfl⟩ : syracuseStep 1383539 = 2075309) B2075309
theorem B1383569 : Blo 920579 1383569 := bstep (se 2 (by rfl) ⟨518838, by rfl⟩ : syracuseStep 1383569 = 1037677) B1037677
theorem B1383587 : Blo 920579 1383587 := bstep (se 1 (by rfl) ⟨1037690, by rfl⟩ : syracuseStep 1383587 = 2075381) B2075381
theorem B2333873 : Blo 920579 2333873 := bstep (se 2 (by rfl) ⟨875202, by rfl⟩ : syracuseStep 2333873 = 1750405) B1750405
theorem B1383617 : Blo 920579 1383617 := bstep (se 2 (by rfl) ⟨518856, by rfl⟩ : syracuseStep 1383617 = 1037713) B1037713
theorem B1383635 : Blo 920579 1383635 := bstep (se 1 (by rfl) ⟨1037726, by rfl⟩ : syracuseStep 1383635 = 2075453) B2075453
theorem B2661617 : Blo 920579 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B1383665 : Blo 920579 1383665 := bstep (se 2 (by rfl) ⟨518874, by rfl⟩ : syracuseStep 1383665 = 1037749) B1037749
theorem B1383683 : Blo 920579 1383683 := bstep (se 1 (by rfl) ⟨1037762, by rfl⟩ : syracuseStep 1383683 = 2075525) B2075525
theorem B1383713 : Blo 920579 1383713 := bstep (se 2 (by rfl) ⟨518892, by rfl⟩ : syracuseStep 1383713 = 1037785) B1037785
theorem B1383731 : Blo 920579 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B2071889 : Blo 920579 2071889 := bstep (se 2 (by rfl) ⟨776958, by rfl⟩ : syracuseStep 2071889 = 1553917) B1553917
theorem B1383761 : Blo 920579 1383761 := bstep (se 2 (by rfl) ⟨518910, by rfl⟩ : syracuseStep 1383761 = 1037821) B1037821
theorem B2071907 : Blo 920579 2071907 := bstep (se 1 (by rfl) ⟨1553930, by rfl⟩ : syracuseStep 2071907 = 3107861) B3107861
theorem B1383779 : Blo 920579 1383779 := bstep (se 1 (by rfl) ⟨1037834, by rfl⟩ : syracuseStep 1383779 = 2075669) B2075669
theorem B1383809 : Blo 920579 1383809 := bstep (se 2 (by rfl) ⟨518928, by rfl⟩ : syracuseStep 1383809 = 1037857) B1037857
theorem B1383827 : Blo 920579 1383827 := bstep (se 1 (by rfl) ⟨1037870, by rfl⟩ : syracuseStep 1383827 = 2075741) B2075741
theorem B2629037 : Blo 920579 2629037 := bstep (se 3 (by rfl) ⟨492944, by rfl⟩ : syracuseStep 2629037 = 985889) B985889
theorem B1383857 : Blo 920579 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B1383875 : Blo 920579 1383875 := bstep (se 1 (by rfl) ⟨1037906, by rfl⟩ : syracuseStep 1383875 = 2075813) B2075813
theorem B1383905 : Blo 920579 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B1383923 : Blo 920579 1383923 := bstep (se 1 (by rfl) ⟨1037942, by rfl⟩ : syracuseStep 1383923 = 2075885) B2075885
theorem B6659597 : Blo 920579 6659597 := bstep (se 3 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 6659597 = 2497349) B2497349
theorem B1383953 : Blo 920579 1383953 := bstep (se 2 (by rfl) ⟨518982, by rfl⟩ : syracuseStep 1383953 = 1037965) B1037965
theorem B1383971 : Blo 920579 1383971 := bstep (se 1 (by rfl) ⟨1037978, by rfl⟩ : syracuseStep 1383971 = 2075957) B2075957
theorem B1384001 : Blo 920579 1384001 := bstep (se 2 (by rfl) ⟨519000, by rfl⟩ : syracuseStep 1384001 = 1038001) B1038001
theorem B1384019 : Blo 920579 1384019 := bstep (se 1 (by rfl) ⟨1038014, by rfl⟩ : syracuseStep 1384019 = 2076029) B2076029
theorem B2629219 : Blo 920579 2629219 := bstep (se 1 (by rfl) ⟨1971914, by rfl⟩ : syracuseStep 2629219 = 3943829) B3943829
theorem B2072177 : Blo 920579 2072177 := bstep (se 2 (by rfl) ⟨777066, by rfl⟩ : syracuseStep 2072177 = 1554133) B1554133
theorem B1384049 : Blo 920579 1384049 := bstep (se 2 (by rfl) ⟨519018, by rfl⟩ : syracuseStep 1384049 = 1038037) B1038037
theorem B2072195 : Blo 920579 2072195 := bstep (se 1 (by rfl) ⟨1554146, by rfl⟩ : syracuseStep 2072195 = 3108293) B3108293
theorem B1384067 : Blo 920579 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B1384097 : Blo 920579 1384097 := bstep (se 2 (by rfl) ⟨519036, by rfl⟩ : syracuseStep 1384097 = 1038073) B1038073
theorem B1384115 : Blo 920579 1384115 := bstep (se 1 (by rfl) ⟨1038086, by rfl⟩ : syracuseStep 1384115 = 2076173) B2076173
theorem B1384145 : Blo 920579 1384145 := bstep (se 2 (by rfl) ⟨519054, by rfl⟩ : syracuseStep 1384145 = 1038109) B1038109
theorem B1384163 : Blo 920579 1384163 := bstep (se 1 (by rfl) ⟨1038122, by rfl⟩ : syracuseStep 1384163 = 2076245) B2076245
theorem B1384193 : Blo 920579 1384193 := bstep (se 2 (by rfl) ⟨519072, by rfl⟩ : syracuseStep 1384193 = 1038145) B1038145
theorem B1384211 : Blo 920579 1384211 := bstep (se 1 (by rfl) ⟨1038158, by rfl⟩ : syracuseStep 1384211 = 2076317) B2076317
theorem B5250851 : Blo 920579 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B1384241 : Blo 920579 1384241 := bstep (se 2 (by rfl) ⟨519090, by rfl⟩ : syracuseStep 1384241 = 1038181) B1038181
theorem B1384259 : Blo 920579 1384259 := bstep (se 1 (by rfl) ⟨1038194, by rfl⟩ : syracuseStep 1384259 = 2076389) B2076389
theorem B1384289 : Blo 920579 1384289 := bstep (se 2 (by rfl) ⟨519108, by rfl⟩ : syracuseStep 1384289 = 1038217) B1038217
theorem B1384307 : Blo 920579 1384307 := bstep (se 1 (by rfl) ⟨1038230, by rfl⟩ : syracuseStep 1384307 = 2076461) B2076461
theorem B2072465 : Blo 920579 2072465 := bstep (se 2 (by rfl) ⟨777174, by rfl⟩ : syracuseStep 2072465 = 1554349) B1554349
theorem B1384337 : Blo 920579 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B2072483 : Blo 920579 2072483 := bstep (se 1 (by rfl) ⟨1554362, by rfl⟩ : syracuseStep 2072483 = 3108725) B3108725
theorem B1384355 : Blo 920579 1384355 := bstep (se 1 (by rfl) ⟨1038266, by rfl⟩ : syracuseStep 1384355 = 2076533) B2076533
theorem B2957219 : Blo 920579 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B1384385 : Blo 920579 1384385 := bstep (se 2 (by rfl) ⟨519144, by rfl⟩ : syracuseStep 1384385 = 1038289) B1038289
theorem B1384403 : Blo 920579 1384403 := bstep (se 1 (by rfl) ⟨1038302, by rfl⟩ : syracuseStep 1384403 = 2076605) B2076605
theorem B1384433 : Blo 920579 1384433 := bstep (se 2 (by rfl) ⟨519162, by rfl⟩ : syracuseStep 1384433 = 1038325) B1038325
theorem B1384451 : Blo 920579 1384451 := bstep (se 1 (by rfl) ⟨1038338, by rfl⟩ : syracuseStep 1384451 = 2076677) B2076677
theorem B1384481 : Blo 920579 1384481 := bstep (se 2 (by rfl) ⟨519180, by rfl⟩ : syracuseStep 1384481 = 1038361) B1038361
theorem B1974307 : Blo 920579 1974307 := bstep (se 1 (by rfl) ⟨1480730, by rfl⟩ : syracuseStep 1974307 = 2961461) B2961461
theorem B1384499 : Blo 920579 1384499 := bstep (se 1 (by rfl) ⟨1038374, by rfl⟩ : syracuseStep 1384499 = 2076749) B2076749
theorem B2629709 : Blo 920579 2629709 := bstep (se 3 (by rfl) ⟨493070, by rfl⟩ : syracuseStep 2629709 = 986141) B986141
theorem B1384529 : Blo 920579 1384529 := bstep (se 2 (by rfl) ⟨519198, by rfl⟩ : syracuseStep 1384529 = 1038397) B1038397
theorem B1384547 : Blo 920579 1384547 := bstep (se 1 (by rfl) ⟨1038410, by rfl⟩ : syracuseStep 1384547 = 2076821) B2076821
theorem B1384577 : Blo 920579 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B7872653 : Blo 920579 7872653 := bstep (se 3 (by rfl) ⟨1476122, by rfl⟩ : syracuseStep 7872653 = 2952245) B2952245
theorem B2334865 : Blo 920579 2334865 := bstep (se 2 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 2334865 = 1751149) B1751149
theorem B1384595 : Blo 920579 1384595 := bstep (se 1 (by rfl) ⟨1038446, by rfl⟩ : syracuseStep 1384595 = 2076893) B2076893
theorem B2072753 : Blo 920579 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B1384625 : Blo 920579 1384625 := bstep (se 2 (by rfl) ⟨519234, by rfl⟩ : syracuseStep 1384625 = 1038469) B1038469
theorem B2072771 : Blo 920579 2072771 := bstep (se 1 (by rfl) ⟨1554578, by rfl⟩ : syracuseStep 2072771 = 3109157) B3109157
theorem B1384643 : Blo 920579 1384643 := bstep (se 1 (by rfl) ⟨1038482, by rfl⟩ : syracuseStep 1384643 = 2076965) B2076965
theorem B1384673 : Blo 920579 1384673 := bstep (se 2 (by rfl) ⟨519252, by rfl⟩ : syracuseStep 1384673 = 1038505) B1038505
theorem B1384691 : Blo 920579 1384691 := bstep (se 1 (by rfl) ⟨1038518, by rfl⟩ : syracuseStep 1384691 = 2077037) B2077037
theorem B1384721 : Blo 920579 1384721 := bstep (se 2 (by rfl) ⟨519270, by rfl⟩ : syracuseStep 1384721 = 1038541) B1038541
theorem B1384739 : Blo 920579 1384739 := bstep (se 1 (by rfl) ⟨1038554, by rfl⟩ : syracuseStep 1384739 = 2077109) B2077109
theorem B1384769 : Blo 920579 1384769 := bstep (se 2 (by rfl) ⟨519288, by rfl⟩ : syracuseStep 1384769 = 1038577) B1038577
theorem B1384787 : Blo 920579 1384787 := bstep (se 1 (by rfl) ⟨1038590, by rfl⟩ : syracuseStep 1384787 = 2077181) B2077181
theorem B1384817 : Blo 920579 1384817 := bstep (se 2 (by rfl) ⟨519306, by rfl⟩ : syracuseStep 1384817 = 1038613) B1038613
theorem B1384835 : Blo 920579 1384835 := bstep (se 1 (by rfl) ⟨1038626, by rfl⟩ : syracuseStep 1384835 = 2077253) B2077253
theorem B1384865 : Blo 920579 1384865 := bstep (se 2 (by rfl) ⟨519324, by rfl⟩ : syracuseStep 1384865 = 1038649) B1038649
theorem B2335139 : Blo 920579 2335139 := bstep (se 1 (by rfl) ⟨1751354, by rfl⟩ : syracuseStep 2335139 = 3502709) B3502709
theorem B1384883 : Blo 920579 1384883 := bstep (se 1 (by rfl) ⟨1038662, by rfl⟩ : syracuseStep 1384883 = 2077325) B2077325
theorem B3318221 : Blo 920579 3318221 := bstep (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) B1244333
theorem B2073041 : Blo 920579 2073041 := bstep (se 2 (by rfl) ⟨777390, by rfl⟩ : syracuseStep 2073041 = 1554781) B1554781
theorem B1384913 : Blo 920579 1384913 := bstep (se 2 (by rfl) ⟨519342, by rfl⟩ : syracuseStep 1384913 = 1038685) B1038685
theorem B2073059 : Blo 920579 2073059 := bstep (se 1 (by rfl) ⟨1554794, by rfl⟩ : syracuseStep 2073059 = 3109589) B3109589
theorem B1384931 : Blo 920579 1384931 := bstep (se 1 (by rfl) ⟨1038698, by rfl⟩ : syracuseStep 1384931 = 2077397) B2077397
theorem B1384961 : Blo 920579 1384961 := bstep (se 2 (by rfl) ⟨519360, by rfl⟩ : syracuseStep 1384961 = 1038721) B1038721
theorem B1384979 : Blo 920579 1384979 := bstep (se 1 (by rfl) ⟨1038734, by rfl⟩ : syracuseStep 1384979 = 2077469) B2077469
theorem B1352227 : Blo 920579 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B3154481 : Blo 920579 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B1385009 : Blo 920579 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B1385027 : Blo 920579 1385027 := bstep (se 1 (by rfl) ⟨1038770, by rfl⟩ : syracuseStep 1385027 = 2077541) B2077541
theorem B1385057 : Blo 920579 1385057 := bstep (se 2 (by rfl) ⟨519396, by rfl⟩ : syracuseStep 1385057 = 1038793) B1038793
theorem B2335331 : Blo 920579 2335331 := bstep (se 1 (by rfl) ⟨1751498, by rfl⟩ : syracuseStep 2335331 = 3502997) B3502997
theorem B4661873 : Blo 920579 4661873 := bstep (se 2 (by rfl) ⟨1748202, by rfl⟩ : syracuseStep 4661873 = 3496405) B3496405
theorem B1385075 : Blo 920579 1385075 := bstep (se 1 (by rfl) ⟨1038806, by rfl⟩ : syracuseStep 1385075 = 2077613) B2077613
theorem B1385105 : Blo 920579 1385105 := bstep (se 2 (by rfl) ⟨519414, by rfl⟩ : syracuseStep 1385105 = 1038829) B1038829
theorem B1385123 : Blo 920579 1385123 := bstep (se 1 (by rfl) ⟨1038842, by rfl⟩ : syracuseStep 1385123 = 2077685) B2077685
theorem B1385153 : Blo 920579 1385153 := bstep (se 2 (by rfl) ⟨519432, by rfl⟩ : syracuseStep 1385153 = 1038865) B1038865
theorem B1385171 : Blo 920579 1385171 := bstep (se 1 (by rfl) ⟨1038878, by rfl⟩ : syracuseStep 1385171 = 2077757) B2077757
theorem B2073329 : Blo 920579 2073329 := bstep (se 2 (by rfl) ⟨777498, by rfl⟩ : syracuseStep 2073329 = 1554997) B1554997
theorem B1385201 : Blo 920579 1385201 := bstep (se 2 (by rfl) ⟨519450, by rfl⟩ : syracuseStep 1385201 = 1038901) B1038901
theorem B2073347 : Blo 920579 2073347 := bstep (se 1 (by rfl) ⟨1555010, by rfl⟩ : syracuseStep 2073347 = 3110021) B3110021
theorem B1385219 : Blo 920579 1385219 := bstep (se 1 (by rfl) ⟨1038914, by rfl⟩ : syracuseStep 1385219 = 2077829) B2077829
theorem B1385249 : Blo 920579 1385249 := bstep (se 2 (by rfl) ⟨519468, by rfl⟩ : syracuseStep 1385249 = 1038937) B1038937
theorem B2958115 : Blo 920579 2958115 := bstep (se 1 (by rfl) ⟨2218586, by rfl⟩ : syracuseStep 2958115 = 4437173) B4437173
theorem B1385267 : Blo 920579 1385267 := bstep (se 1 (by rfl) ⟨1038950, by rfl⟩ : syracuseStep 1385267 = 2077901) B2077901
theorem B1385297 : Blo 920579 1385297 := bstep (se 2 (by rfl) ⟨519486, by rfl⟩ : syracuseStep 1385297 = 1038973) B1038973
theorem B1385315 : Blo 920579 1385315 := bstep (se 1 (by rfl) ⟨1038986, by rfl⟩ : syracuseStep 1385315 = 2077973) B2077973
theorem B1385345 : Blo 920579 1385345 := bstep (se 2 (by rfl) ⟨519504, by rfl⟩ : syracuseStep 1385345 = 1039009) B1039009
theorem B1385363 : Blo 920579 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B1385393 : Blo 920579 1385393 := bstep (se 2 (by rfl) ⟨519522, by rfl⟩ : syracuseStep 1385393 = 1039045) B1039045
theorem B1385411 : Blo 920579 1385411 := bstep (se 1 (by rfl) ⟨1039058, by rfl⟩ : syracuseStep 1385411 = 2078117) B2078117
theorem B1385441 : Blo 920579 1385441 := bstep (se 2 (by rfl) ⟨519540, by rfl⟩ : syracuseStep 1385441 = 1039081) B1039081
theorem B1385459 : Blo 920579 1385459 := bstep (se 1 (by rfl) ⟨1039094, by rfl⟩ : syracuseStep 1385459 = 2078189) B2078189
theorem B2073617 : Blo 920579 2073617 := bstep (se 2 (by rfl) ⟨777606, by rfl⟩ : syracuseStep 2073617 = 1555213) B1555213
theorem B1385489 : Blo 920579 1385489 := bstep (se 2 (by rfl) ⟨519558, by rfl⟩ : syracuseStep 1385489 = 1039117) B1039117
theorem B2073635 : Blo 920579 2073635 := bstep (se 1 (by rfl) ⟨1555226, by rfl⟩ : syracuseStep 2073635 = 3110453) B3110453
theorem B1385507 : Blo 920579 1385507 := bstep (se 1 (by rfl) ⟨1039130, by rfl⟩ : syracuseStep 1385507 = 2078261) B2078261
theorem B1385537 : Blo 920579 1385537 := bstep (se 2 (by rfl) ⟨519576, by rfl⟩ : syracuseStep 1385537 = 1039153) B1039153
theorem B3941453 : Blo 920579 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B1385555 : Blo 920579 1385555 := bstep (se 1 (by rfl) ⟨1039166, by rfl⟩ : syracuseStep 1385555 = 2078333) B2078333
theorem B1385585 : Blo 920579 1385585 := bstep (se 2 (by rfl) ⟨519594, by rfl⟩ : syracuseStep 1385585 = 1039189) B1039189
theorem B1385603 : Blo 920579 1385603 := bstep (se 1 (by rfl) ⟨1039202, by rfl⟩ : syracuseStep 1385603 = 2078405) B2078405
theorem B1385633 : Blo 920579 1385633 := bstep (se 2 (by rfl) ⟨519612, by rfl⟩ : syracuseStep 1385633 = 1039225) B1039225
theorem B1385651 : Blo 920579 1385651 := bstep (se 1 (by rfl) ⟨1039238, by rfl⟩ : syracuseStep 1385651 = 2078477) B2078477
theorem B13477061 : Blo 920579 13477061 := bstep (se 4 (by rfl) ⟨1263474, by rfl⟩ : syracuseStep 13477061 = 2526949) B2526949
theorem B1385681 : Blo 920579 1385681 := bstep (se 2 (by rfl) ⟨519630, by rfl⟩ : syracuseStep 1385681 = 1039261) B1039261
theorem B1385699 : Blo 920579 1385699 := bstep (se 1 (by rfl) ⟨1039274, by rfl⟩ : syracuseStep 1385699 = 2078549) B2078549
theorem B2630893 : Blo 920579 2630893 := bstep (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) B986585
theorem B1385729 : Blo 920579 1385729 := bstep (se 2 (by rfl) ⟨519648, by rfl⟩ : syracuseStep 1385729 = 1039297) B1039297
theorem B1385747 : Blo 920579 1385747 := bstep (se 1 (by rfl) ⟨1039310, by rfl⟩ : syracuseStep 1385747 = 2078621) B2078621
theorem B2073905 : Blo 920579 2073905 := bstep (se 2 (by rfl) ⟨777714, by rfl⟩ : syracuseStep 2073905 = 1555429) B1555429
theorem B1385777 : Blo 920579 1385777 := bstep (se 2 (by rfl) ⟨519666, by rfl⟩ : syracuseStep 1385777 = 1039333) B1039333
theorem B2073923 : Blo 920579 2073923 := bstep (se 1 (by rfl) ⟨1555442, by rfl⟩ : syracuseStep 2073923 = 3110885) B3110885
theorem B1385795 : Blo 920579 1385795 := bstep (se 1 (by rfl) ⟨1039346, by rfl⟩ : syracuseStep 1385795 = 2078693) B2078693
theorem B1385825 : Blo 920579 1385825 := bstep (se 2 (by rfl) ⟨519684, by rfl⟩ : syracuseStep 1385825 = 1039369) B1039369
theorem B1385843 : Blo 920579 1385843 := bstep (se 1 (by rfl) ⟨1039382, by rfl⟩ : syracuseStep 1385843 = 2078765) B2078765
theorem B1385873 : Blo 920579 1385873 := bstep (se 2 (by rfl) ⟨519702, by rfl⟩ : syracuseStep 1385873 = 1039405) B1039405
theorem B959891 : Blo 920579 959891 := bstep (se 1 (by rfl) ⟨719918, by rfl⟩ : syracuseStep 959891 = 1439837) B1439837
theorem B1385891 : Blo 920579 1385891 := bstep (se 1 (by rfl) ⟨1039418, by rfl⟩ : syracuseStep 1385891 = 2078837) B2078837
theorem B1385921 : Blo 920579 1385921 := bstep (se 2 (by rfl) ⟨519720, by rfl⟩ : syracuseStep 1385921 = 1039441) B1039441
theorem B1385939 : Blo 920579 1385939 := bstep (se 1 (by rfl) ⟨1039454, by rfl⟩ : syracuseStep 1385939 = 2078909) B2078909
theorem B1385969 : Blo 920579 1385969 := bstep (se 2 (by rfl) ⟨519738, by rfl⟩ : syracuseStep 1385969 = 1039477) B1039477
theorem B1385987 : Blo 920579 1385987 := bstep (se 1 (by rfl) ⟨1039490, by rfl⟩ : syracuseStep 1385987 = 2078981) B2078981
theorem B2336273 : Blo 920579 2336273 := bstep (se 2 (by rfl) ⟨876102, by rfl⟩ : syracuseStep 2336273 = 1752205) B1752205
theorem B1386017 : Blo 920579 1386017 := bstep (se 2 (by rfl) ⟨519756, by rfl⟩ : syracuseStep 1386017 = 1039513) B1039513
theorem B1386035 : Blo 920579 1386035 := bstep (se 1 (by rfl) ⟨1039526, by rfl⟩ : syracuseStep 1386035 = 2079053) B2079053
theorem B2336323 : Blo 920579 2336323 := bstep (se 1 (by rfl) ⟨1752242, by rfl⟩ : syracuseStep 2336323 = 3504485) B3504485
theorem B2106947 : Blo 920579 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B2074193 : Blo 920579 2074193 := bstep (se 2 (by rfl) ⟨777822, by rfl⟩ : syracuseStep 2074193 = 1555645) B1555645
theorem B1386065 : Blo 920579 1386065 := bstep (se 2 (by rfl) ⟨519774, by rfl⟩ : syracuseStep 1386065 = 1039549) B1039549
theorem B2074211 : Blo 920579 2074211 := bstep (se 1 (by rfl) ⟨1555658, by rfl⟩ : syracuseStep 2074211 = 3111317) B3111317
theorem B1386083 : Blo 920579 1386083 := bstep (se 1 (by rfl) ⟨1039562, by rfl⟩ : syracuseStep 1386083 = 2079125) B2079125
theorem B1386113 : Blo 920579 1386113 := bstep (se 2 (by rfl) ⟨519792, by rfl⟩ : syracuseStep 1386113 = 1039585) B1039585
theorem B1386131 : Blo 920579 1386131 := bstep (se 1 (by rfl) ⟨1039598, by rfl⟩ : syracuseStep 1386131 = 2079197) B2079197
theorem B1386161 : Blo 920579 1386161 := bstep (se 2 (by rfl) ⟨519810, by rfl⟩ : syracuseStep 1386161 = 1039621) B1039621
theorem B1386179 : Blo 920579 1386179 := bstep (se 1 (by rfl) ⟨1039634, by rfl⟩ : syracuseStep 1386179 = 2079269) B2079269
theorem B2336465 : Blo 920579 2336465 := bstep (se 2 (by rfl) ⟨876174, by rfl⟩ : syracuseStep 2336465 = 1752349) B1752349
theorem B1386209 : Blo 920579 1386209 := bstep (se 2 (by rfl) ⟨519828, by rfl⟩ : syracuseStep 1386209 = 1039657) B1039657
theorem B1386227 : Blo 920579 1386227 := bstep (se 1 (by rfl) ⟨1039670, by rfl⟩ : syracuseStep 1386227 = 2079341) B2079341
theorem B1386257 : Blo 920579 1386257 := bstep (se 2 (by rfl) ⟨519846, by rfl⟩ : syracuseStep 1386257 = 1039693) B1039693
theorem B5318435 : Blo 920579 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B1386275 : Blo 920579 1386275 := bstep (se 1 (by rfl) ⟨1039706, by rfl⟩ : syracuseStep 1386275 = 2079413) B2079413
theorem B1386305 : Blo 920579 1386305 := bstep (se 2 (by rfl) ⟨519864, by rfl⟩ : syracuseStep 1386305 = 1039729) B1039729
theorem B1386323 : Blo 920579 1386323 := bstep (se 1 (by rfl) ⟨1039742, by rfl⟩ : syracuseStep 1386323 = 2079485) B2079485
theorem B2074481 : Blo 920579 2074481 := bstep (se 2 (by rfl) ⟨777930, by rfl⟩ : syracuseStep 2074481 = 1555861) B1555861
theorem B3549041 : Blo 920579 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B2959217 : Blo 920579 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B1386353 : Blo 920579 1386353 := bstep (se 2 (by rfl) ⟨519882, by rfl⟩ : syracuseStep 1386353 = 1039765) B1039765
theorem B2074499 : Blo 920579 2074499 := bstep (se 1 (by rfl) ⟨1555874, by rfl⟩ : syracuseStep 2074499 = 3111749) B3111749
theorem B1386371 : Blo 920579 1386371 := bstep (se 1 (by rfl) ⟨1039778, by rfl⟩ : syracuseStep 1386371 = 2079557) B2079557
theorem B1386401 : Blo 920579 1386401 := bstep (se 2 (by rfl) ⟨519900, by rfl⟩ : syracuseStep 1386401 = 1039801) B1039801
theorem B1386419 : Blo 920579 1386419 := bstep (se 1 (by rfl) ⟨1039814, by rfl⟩ : syracuseStep 1386419 = 2079629) B2079629
theorem B1386449 : Blo 920579 1386449 := bstep (se 2 (by rfl) ⟨519918, by rfl⟩ : syracuseStep 1386449 = 1039837) B1039837
theorem B1386467 : Blo 920579 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B2959345 : Blo 920579 2959345 := bstep (se 2 (by rfl) ⟨1109754, by rfl⟩ : syracuseStep 2959345 = 2219509) B2219509
theorem B1386497 : Blo 920579 1386497 := bstep (se 2 (by rfl) ⟨519936, by rfl⟩ : syracuseStep 1386497 = 1039873) B1039873
theorem B1386515 : Blo 920579 1386515 := bstep (se 1 (by rfl) ⟨1039886, by rfl⟩ : syracuseStep 1386515 = 2079773) B2079773
theorem B4663331 : Blo 920579 4663331 := bstep (se 1 (by rfl) ⟨3497498, by rfl⟩ : syracuseStep 4663331 = 6994997) B6994997
theorem B1386545 : Blo 920579 1386545 := bstep (se 2 (by rfl) ⟨519954, by rfl⟩ : syracuseStep 1386545 = 1039909) B1039909
theorem B1386563 : Blo 920579 1386563 := bstep (se 1 (by rfl) ⟨1039922, by rfl⟩ : syracuseStep 1386563 = 2079845) B2079845
theorem B1386593 : Blo 920579 1386593 := bstep (se 2 (by rfl) ⟨519972, by rfl⟩ : syracuseStep 1386593 = 1039945) B1039945
theorem B1386611 : Blo 920579 1386611 := bstep (se 1 (by rfl) ⟨1039958, by rfl⟩ : syracuseStep 1386611 = 2079917) B2079917
theorem B10496141 : Blo 920579 10496141 := bstep (se 3 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 10496141 = 3936053) B3936053
theorem B2074769 : Blo 920579 2074769 := bstep (se 2 (by rfl) ⟨778038, by rfl⟩ : syracuseStep 2074769 = 1556077) B1556077
theorem B1386641 : Blo 920579 1386641 := bstep (se 2 (by rfl) ⟨519990, by rfl⟩ : syracuseStep 1386641 = 1039981) B1039981
theorem B2074787 : Blo 920579 2074787 := bstep (se 1 (by rfl) ⟨1556090, by rfl⟩ : syracuseStep 2074787 = 3112181) B3112181
theorem B1386659 : Blo 920579 1386659 := bstep (se 1 (by rfl) ⟨1039994, by rfl⟩ : syracuseStep 1386659 = 2079989) B2079989
theorem B4434097 : Blo 920579 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B1386689 : Blo 920579 1386689 := bstep (se 2 (by rfl) ⟨520008, by rfl⟩ : syracuseStep 1386689 = 1040017) B1040017
theorem B1386707 : Blo 920579 1386707 := bstep (se 1 (by rfl) ⟨1040030, by rfl⟩ : syracuseStep 1386707 = 2080061) B2080061
theorem B1386737 : Blo 920579 1386737 := bstep (se 2 (by rfl) ⟨520026, by rfl⟩ : syracuseStep 1386737 = 1040053) B1040053
theorem B1386755 : Blo 920579 1386755 := bstep (se 1 (by rfl) ⟨1040066, by rfl⟩ : syracuseStep 1386755 = 2080133) B2080133
theorem B2631953 : Blo 920579 2631953 := bstep (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) B1973965
theorem B1386785 : Blo 920579 1386785 := bstep (se 2 (by rfl) ⟨520044, by rfl⟩ : syracuseStep 1386785 = 1040089) B1040089
theorem B4434211 : Blo 920579 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B1386803 : Blo 920579 1386803 := bstep (se 1 (by rfl) ⟨1040102, by rfl⟩ : syracuseStep 1386803 = 2080205) B2080205
theorem B1386833 : Blo 920579 1386833 := bstep (se 2 (by rfl) ⟨520062, by rfl⟩ : syracuseStep 1386833 = 1040125) B1040125
theorem B1386851 : Blo 920579 1386851 := bstep (se 1 (by rfl) ⟨1040138, by rfl⟩ : syracuseStep 1386851 = 2080277) B2080277
theorem B2075057 : Blo 920579 2075057 := bstep (se 2 (by rfl) ⟨778146, by rfl⟩ : syracuseStep 2075057 = 1556293) B1556293
theorem B2075075 : Blo 920579 2075075 := bstep (se 1 (by rfl) ⟨1556306, by rfl⟩ : syracuseStep 2075075 = 3112613) B3112613
theorem B4991429 : Blo 920579 4991429 := bstep (se 4 (by rfl) ⟨467946, by rfl⟩ : syracuseStep 4991429 = 935893) B935893
theorem B3943025 : Blo 920579 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B2337457 : Blo 920579 2337457 := bstep (se 2 (by rfl) ⟨876546, by rfl⟩ : syracuseStep 2337457 = 1753093) B1753093
theorem B2075345 : Blo 920579 2075345 := bstep (se 2 (by rfl) ⟨778254, by rfl⟩ : syracuseStep 2075345 = 1556509) B1556509
theorem B2075363 : Blo 920579 2075363 := bstep (se 1 (by rfl) ⟨1556522, by rfl⟩ : syracuseStep 2075363 = 3113045) B3113045
theorem B1747747 : Blo 920579 1747747 := bstep (se 1 (by rfl) ⟨1310810, by rfl⟩ : syracuseStep 1747747 = 2621621) B2621621
theorem B4664141 : Blo 920579 4664141 := bstep (se 3 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 4664141 = 1749053) B1749053
theorem B1747793 : Blo 920579 1747793 := bstep (se 2 (by rfl) ⟨655422, by rfl⟩ : syracuseStep 1747793 = 1310845) B1310845
theorem B5909411 : Blo 920579 5909411 := bstep (se 1 (by rfl) ⟨4432058, by rfl⟩ : syracuseStep 5909411 = 8864117) B8864117
theorem B2632625 : Blo 920579 2632625 := bstep (se 2 (by rfl) ⟨987234, by rfl⟩ : syracuseStep 2632625 = 1974469) B1974469
theorem B2337731 : Blo 920579 2337731 := bstep (se 1 (by rfl) ⟨1753298, by rfl⟩ : syracuseStep 2337731 = 3506597) B3506597
theorem B5254085 : Blo 920579 5254085 := bstep (se 4 (by rfl) ⟨492570, by rfl⟩ : syracuseStep 5254085 = 985141) B985141
theorem B2960333 : Blo 920579 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B15772643 : Blo 920579 15772643 := bstep (se 1 (by rfl) ⟨11829482, by rfl⟩ : syracuseStep 15772643 = 23658965) B23658965
theorem B2075633 : Blo 920579 2075633 := bstep (se 2 (by rfl) ⟨778362, by rfl⟩ : syracuseStep 2075633 = 1556725) B1556725
theorem B2075651 : Blo 920579 2075651 := bstep (se 1 (by rfl) ⟨1556738, by rfl⟩ : syracuseStep 2075651 = 3113477) B3113477
theorem B1748081 : Blo 920579 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B2337923 : Blo 920579 2337923 := bstep (se 1 (by rfl) ⟨1753442, by rfl⟩ : syracuseStep 2337923 = 3506885) B3506885
theorem B2075921 : Blo 920579 2075921 := bstep (se 2 (by rfl) ⟨778470, by rfl⟩ : syracuseStep 2075921 = 1556941) B1556941
theorem B2075939 : Blo 920579 2075939 := bstep (se 1 (by rfl) ⟨1556954, by rfl⟩ : syracuseStep 2075939 = 3113909) B3113909
theorem B5254541 : Blo 920579 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B2698705 : Blo 920579 2698705 := bstep (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) B2024029
theorem B2666029 : Blo 920579 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B2076209 : Blo 920579 2076209 := bstep (se 2 (by rfl) ⟨778578, by rfl⟩ : syracuseStep 2076209 = 1557157) B1557157
theorem B2076227 : Blo 920579 2076227 := bstep (se 1 (by rfl) ⟨1557170, by rfl⟩ : syracuseStep 2076227 = 3114341) B3114341
theorem B2993773 : Blo 920579 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B1748803 : Blo 920579 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B2076497 : Blo 920579 2076497 := bstep (se 2 (by rfl) ⟨778686, by rfl⟩ : syracuseStep 2076497 = 1557373) B1557373
theorem B2076515 : Blo 920579 2076515 := bstep (se 1 (by rfl) ⟨1557386, by rfl⟩ : syracuseStep 2076515 = 3114773) B3114773
theorem B2338865 : Blo 920579 2338865 := bstep (se 2 (by rfl) ⟨877074, by rfl⟩ : syracuseStep 2338865 = 1754149) B1754149
theorem B2338915 : Blo 920579 2338915 := bstep (se 1 (by rfl) ⟨1754186, by rfl⟩ : syracuseStep 2338915 = 3508373) B3508373
theorem B5910641 : Blo 920579 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B2076785 : Blo 920579 2076785 := bstep (se 2 (by rfl) ⟨778794, by rfl⟩ : syracuseStep 2076785 = 1557589) B1557589
theorem B2076803 : Blo 920579 2076803 := bstep (se 1 (by rfl) ⟨1557602, by rfl⟩ : syracuseStep 2076803 = 3115205) B3115205
theorem B2339057 : Blo 920579 2339057 := bstep (se 2 (by rfl) ⟨877146, by rfl⟩ : syracuseStep 2339057 = 1754293) B1754293
theorem B1749251 : Blo 920579 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B3551501 : Blo 920579 3551501 := bstep (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) B1331813
theorem B2961677 : Blo 920579 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B5615941 : Blo 920579 5615941 := bstep (se 4 (by rfl) ⟨526494, by rfl⟩ : syracuseStep 5615941 = 1052989) B1052989
theorem B2077073 : Blo 920579 2077073 := bstep (se 2 (by rfl) ⟨778902, by rfl⟩ : syracuseStep 2077073 = 1557805) B1557805
theorem B2077091 : Blo 920579 2077091 := bstep (se 1 (by rfl) ⟨1557818, by rfl⟩ : syracuseStep 2077091 = 3115637) B3115637
theorem B1749539 : Blo 920579 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B3551779 : Blo 920579 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B2667043 : Blo 920579 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B2077361 : Blo 920579 2077361 := bstep (se 2 (by rfl) ⟨779010, by rfl⟩ : syracuseStep 2077361 = 1558021) B1558021
theorem B2077379 : Blo 920579 2077379 := bstep (se 1 (by rfl) ⟨1558034, by rfl⟩ : syracuseStep 2077379 = 3116069) B3116069
theorem B2077649 : Blo 920579 2077649 := bstep (se 2 (by rfl) ⟨779118, by rfl⟩ : syracuseStep 2077649 = 1558237) B1558237
theorem B2077667 : Blo 920579 2077667 := bstep (se 1 (by rfl) ⟨1558250, by rfl⟩ : syracuseStep 2077667 = 3116501) B3116501
theorem B10499057 : Blo 920579 10499057 := bstep (se 2 (by rfl) ⟨3937146, by rfl⟩ : syracuseStep 10499057 = 7874293) B7874293
theorem B3552269 : Blo 920579 3552269 := bstep (se 3 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 3552269 = 1332101) B1332101
theorem B3945485 : Blo 920579 3945485 := bstep (se 3 (by rfl) ⟨739778, by rfl⟩ : syracuseStep 3945485 = 1479557) B1479557
theorem B1553539 : Blo 920579 1553539 := bstep (se 1 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 1553539 = 2330309) B2330309
theorem B2340049 : Blo 920579 2340049 := bstep (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) B1755037
theorem B2077937 : Blo 920579 2077937 := bstep (se 2 (by rfl) ⟨779226, by rfl⟩ : syracuseStep 2077937 = 1558453) B1558453
theorem B2077955 : Blo 920579 2077955 := bstep (se 1 (by rfl) ⟨1558466, by rfl⟩ : syracuseStep 2077955 = 3116933) B3116933
theorem B1553681 : Blo 920579 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B25212181 : Blo 920579 25212181 := bstep (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) B1181821
theorem B3945827 : Blo 920579 3945827 := bstep (se 1 (by rfl) ⟨2959370, by rfl⟩ : syracuseStep 3945827 = 5918741) B5918741
theorem B1553809 : Blo 920579 1553809 := bstep (se 2 (by rfl) ⟨582678, by rfl⟩ : syracuseStep 1553809 = 1165357) B1165357
theorem B1553843 : Blo 920579 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1750481 : Blo 920579 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B2340323 : Blo 920579 2340323 := bstep (se 1 (by rfl) ⟨1755242, by rfl⟩ : syracuseStep 2340323 = 3510485) B3510485
theorem B2078225 : Blo 920579 2078225 := bstep (se 2 (by rfl) ⟨779334, by rfl⟩ : syracuseStep 2078225 = 1558669) B1558669
theorem B2078243 : Blo 920579 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B1553971 : Blo 920579 1553971 := bstep (se 1 (by rfl) ⟨1165478, by rfl⟩ : syracuseStep 1553971 = 2330957) B2330957
theorem B4667057 : Blo 920579 4667057 := bstep (se 2 (by rfl) ⟨1750146, by rfl⟩ : syracuseStep 4667057 = 3500293) B3500293
theorem B1554113 : Blo 920579 1554113 := bstep (se 2 (by rfl) ⟨582792, by rfl⟩ : syracuseStep 1554113 = 1165585) B1165585
theorem B2078513 : Blo 920579 2078513 := bstep (se 2 (by rfl) ⟨779442, by rfl⟩ : syracuseStep 2078513 = 1558885) B1558885
theorem B1554241 : Blo 920579 1554241 := bstep (se 2 (by rfl) ⟨582840, by rfl⟩ : syracuseStep 1554241 = 1165681) B1165681
theorem B2078531 : Blo 920579 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1554275 : Blo 920579 1554275 := bstep (se 1 (by rfl) ⟨1165706, by rfl⟩ : syracuseStep 1554275 = 2331413) B2331413
theorem B1554403 : Blo 920579 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B2078801 : Blo 920579 2078801 := bstep (se 2 (by rfl) ⟨779550, by rfl⟩ : syracuseStep 2078801 = 1559101) B1559101
theorem B2078819 : Blo 920579 2078819 := bstep (se 1 (by rfl) ⟨1559114, by rfl⟩ : syracuseStep 2078819 = 3118229) B3118229
theorem B2242673 : Blo 920579 2242673 := bstep (se 2 (by rfl) ⟨841002, by rfl⟩ : syracuseStep 2242673 = 1682005) B1682005
theorem B1554545 : Blo 920579 1554545 := bstep (se 2 (by rfl) ⟨582954, by rfl⟩ : syracuseStep 1554545 = 1165909) B1165909
theorem B1554673 : Blo 920579 1554673 := bstep (se 2 (by rfl) ⟨583002, by rfl⟩ : syracuseStep 1554673 = 1166005) B1166005
theorem B5257457 : Blo 920579 5257457 := bstep (se 2 (by rfl) ⟨1971546, by rfl⟩ : syracuseStep 5257457 = 3943093) B3943093
theorem B1554707 : Blo 920579 1554707 := bstep (se 1 (by rfl) ⟨1166030, by rfl⟩ : syracuseStep 1554707 = 2332061) B2332061
theorem B1751377 : Blo 920579 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B2079089 : Blo 920579 2079089 := bstep (se 2 (by rfl) ⟨779658, by rfl⟩ : syracuseStep 2079089 = 1559317) B1559317
theorem B2079107 : Blo 920579 2079107 := bstep (se 1 (by rfl) ⟨1559330, by rfl⟩ : syracuseStep 2079107 = 3118661) B3118661
theorem B1554835 : Blo 920579 1554835 := bstep (se 1 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 1554835 = 2332253) B2332253
theorem B1751537 : Blo 920579 1751537 := bstep (se 2 (by rfl) ⟨656826, by rfl⟩ : syracuseStep 1751537 = 1313653) B1313653
theorem B5913101 : Blo 920579 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B1554977 : Blo 920579 1554977 := bstep (se 2 (by rfl) ⟨583116, by rfl⟩ : syracuseStep 1554977 = 1166233) B1166233
theorem B2800273 : Blo 920579 2800273 := bstep (se 2 (by rfl) ⟨1050102, by rfl⟩ : syracuseStep 2800273 = 2100205) B2100205
theorem B3160721 : Blo 920579 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B2079377 : Blo 920579 2079377 := bstep (se 2 (by rfl) ⟨779766, by rfl⟩ : syracuseStep 2079377 = 1559533) B1559533
theorem B1555105 : Blo 920579 1555105 := bstep (se 2 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 1555105 = 1166329) B1166329
theorem B2079395 : Blo 920579 2079395 := bstep (se 1 (by rfl) ⟨1559546, by rfl⟩ : syracuseStep 2079395 = 3119093) B3119093
theorem B1555139 : Blo 920579 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1555267 : Blo 920579 1555267 := bstep (se 1 (by rfl) ⟨1166450, by rfl⟩ : syracuseStep 1555267 = 2332901) B2332901
theorem B1751939 : Blo 920579 1751939 := bstep (se 1 (by rfl) ⟨1313954, by rfl⟩ : syracuseStep 1751939 = 2627909) B2627909
theorem B2079665 : Blo 920579 2079665 := bstep (se 2 (by rfl) ⟨779874, by rfl⟩ : syracuseStep 2079665 = 1559749) B1559749
theorem B2079683 : Blo 920579 2079683 := bstep (se 1 (by rfl) ⟨1559762, by rfl⟩ : syracuseStep 2079683 = 3119525) B3119525
theorem B1555409 : Blo 920579 1555409 := bstep (se 2 (by rfl) ⟨583278, by rfl⟩ : syracuseStep 1555409 = 1166557) B1166557
theorem B1555537 : Blo 920579 1555537 := bstep (se 2 (by rfl) ⟨583326, by rfl⟩ : syracuseStep 1555537 = 1166653) B1166653
theorem B4668515 : Blo 920579 4668515 := bstep (se 1 (by rfl) ⟨3501386, by rfl⟩ : syracuseStep 4668515 = 7002773) B7002773
theorem B1555571 : Blo 920579 1555571 := bstep (se 1 (by rfl) ⟨1166678, by rfl⟩ : syracuseStep 1555571 = 2333357) B2333357
theorem B2079953 : Blo 920579 2079953 := bstep (se 2 (by rfl) ⟨779982, by rfl⟩ : syracuseStep 2079953 = 1559965) B1559965
theorem B2079971 : Blo 920579 2079971 := bstep (se 1 (by rfl) ⟨1559978, by rfl⟩ : syracuseStep 2079971 = 3119957) B3119957
theorem B1555699 : Blo 920579 1555699 := bstep (se 1 (by rfl) ⟨1166774, by rfl⟩ : syracuseStep 1555699 = 2333549) B2333549
theorem B5979491 : Blo 920579 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B1555841 : Blo 920579 1555841 := bstep (se 2 (by rfl) ⟨583440, by rfl⟩ : syracuseStep 1555841 = 1166881) B1166881
theorem B933331 : Blo 920579 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B2080241 : Blo 920579 2080241 := bstep (se 2 (by rfl) ⟨780090, by rfl⟩ : syracuseStep 2080241 = 1560181) B1560181
theorem B1555969 : Blo 920579 1555969 := bstep (se 2 (by rfl) ⟨583488, by rfl⟩ : syracuseStep 1555969 = 1166977) B1166977
theorem B2080259 : Blo 920579 2080259 := bstep (se 1 (by rfl) ⟨1560194, by rfl⟩ : syracuseStep 2080259 = 3120389) B3120389
theorem B1556003 : Blo 920579 1556003 := bstep (se 1 (by rfl) ⟨1167002, by rfl⟩ : syracuseStep 1556003 = 2334005) B2334005
theorem B1556131 : Blo 920579 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B5258915 : Blo 920579 5258915 := bstep (se 1 (by rfl) ⟨3944186, by rfl⟩ : syracuseStep 5258915 = 7888373) B7888373
theorem B1752835 : Blo 920579 1752835 := bstep (se 1 (by rfl) ⟨1314626, by rfl⟩ : syracuseStep 1752835 = 2629253) B2629253
theorem B8863501 : Blo 920579 8863501 := bstep (se 3 (by rfl) ⟨1661906, by rfl⟩ : syracuseStep 8863501 = 3323813) B3323813
theorem B1556273 : Blo 920579 1556273 := bstep (se 2 (by rfl) ⟨583602, by rfl⟩ : syracuseStep 1556273 = 1167205) B1167205
theorem B4669325 : Blo 920579 4669325 := bstep (se 3 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 4669325 = 1750997) B1750997
theorem B1752995 : Blo 920579 1752995 := bstep (se 1 (by rfl) ⟨1314746, by rfl⟩ : syracuseStep 1752995 = 2629493) B2629493
theorem B1556401 : Blo 920579 1556401 := bstep (se 2 (by rfl) ⟨583650, by rfl⟩ : syracuseStep 1556401 = 1167301) B1167301
theorem B1556435 : Blo 920579 1556435 := bstep (se 1 (by rfl) ⟨1167326, by rfl⟩ : syracuseStep 1556435 = 2334653) B2334653
theorem B11812877 : Blo 920579 11812877 := bstep (se 3 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 11812877 = 4429829) B4429829
theorem B1261651 : Blo 920579 1261651 := bstep (se 1 (by rfl) ⟨946238, by rfl⟩ : syracuseStep 1261651 = 1892477) B1892477
theorem B1556563 : Blo 920579 1556563 := bstep (se 1 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 1556563 = 2334845) B2334845
theorem B1556705 : Blo 920579 1556705 := bstep (se 2 (by rfl) ⟨583764, by rfl⟩ : syracuseStep 1556705 = 1167529) B1167529
theorem B1556833 : Blo 920579 1556833 := bstep (se 2 (by rfl) ⟨583812, by rfl⟩ : syracuseStep 1556833 = 1167625) B1167625
theorem B1556867 : Blo 920579 1556867 := bstep (se 1 (by rfl) ⟨1167650, by rfl⟩ : syracuseStep 1556867 = 2335301) B2335301
theorem B1556995 : Blo 920579 1556995 := bstep (se 1 (by rfl) ⟨1167746, by rfl⟩ : syracuseStep 1556995 = 2335493) B2335493
theorem B5259917 : Blo 920579 5259917 := bstep (se 3 (by rfl) ⟨986234, by rfl⟩ : syracuseStep 5259917 = 1972469) B1972469
theorem B1557137 : Blo 920579 1557137 := bstep (se 2 (by rfl) ⟨583926, by rfl⟩ : syracuseStep 1557137 = 1167853) B1167853
theorem B1557265 : Blo 920579 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B1557299 : Blo 920579 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B934787 : Blo 920579 934787 := bstep (se 1 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 934787 = 1402181) B1402181
theorem B13288333 : Blo 920579 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B1557427 : Blo 920579 1557427 := bstep (se 1 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 1557427 = 2336141) B2336141
theorem B12633029 : Blo 920579 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B1754065 : Blo 920579 1754065 := bstep (se 2 (by rfl) ⟨657774, by rfl⟩ : syracuseStep 1754065 = 1315549) B1315549
theorem B1557569 : Blo 920579 1557569 := bstep (se 2 (by rfl) ⟨584088, by rfl⟩ : syracuseStep 1557569 = 1168177) B1168177
theorem B1262659 : Blo 920579 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B1557697 : Blo 920579 1557697 := bstep (se 2 (by rfl) ⟨584136, by rfl⟩ : syracuseStep 1557697 = 1168273) B1168273
theorem B1557731 : Blo 920579 1557731 := bstep (se 1 (by rfl) ⟨1168298, by rfl⟩ : syracuseStep 1557731 = 2336597) B2336597
theorem B1557859 : Blo 920579 1557859 := bstep (se 1 (by rfl) ⟨1168394, by rfl⟩ : syracuseStep 1557859 = 2336789) B2336789
theorem B1558001 : Blo 920579 1558001 := bstep (se 2 (by rfl) ⟨584250, by rfl⟩ : syracuseStep 1558001 = 1168501) B1168501
theorem B11847221 : Blo 920579 11847221 := bstep (se 5 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 11847221 = 1110677) B1110677
theorem B8636003 : Blo 920579 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B1558129 : Blo 920579 1558129 := bstep (se 2 (by rfl) ⟨584298, by rfl⟩ : syracuseStep 1558129 = 1168597) B1168597
theorem B1558163 : Blo 920579 1558163 := bstep (se 1 (by rfl) ⟨1168622, by rfl⟩ : syracuseStep 1558163 = 2337245) B2337245
theorem B1558291 : Blo 920579 1558291 := bstep (se 1 (by rfl) ⟨1168718, by rfl⟩ : syracuseStep 1558291 = 2337437) B2337437
theorem B1558433 : Blo 920579 1558433 := bstep (se 2 (by rfl) ⟨584412, by rfl⟩ : syracuseStep 1558433 = 1168825) B1168825
theorem B8865733 : Blo 920579 8865733 := bstep (se 4 (by rfl) ⟨831162, by rfl⟩ : syracuseStep 8865733 = 1662325) B1662325
theorem B1755121 : Blo 920579 1755121 := bstep (se 2 (by rfl) ⟨658170, by rfl⟩ : syracuseStep 1755121 = 1316341) B1316341
theorem B1558561 : Blo 920579 1558561 := bstep (se 2 (by rfl) ⟨584460, by rfl⟩ : syracuseStep 1558561 = 1168921) B1168921
theorem B1558595 : Blo 920579 1558595 := bstep (se 1 (by rfl) ⟨1168946, by rfl⟩ : syracuseStep 1558595 = 2337893) B2337893
theorem B1558723 : Blo 920579 1558723 := bstep (se 1 (by rfl) ⟨1169042, by rfl⟩ : syracuseStep 1558723 = 2338085) B2338085
theorem B13289669 : Blo 920579 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B1558865 : Blo 920579 1558865 := bstep (se 2 (by rfl) ⟨584574, by rfl⟩ : syracuseStep 1558865 = 1169149) B1169149
theorem B1165747 : Blo 920579 1165747 := bstep (se 1 (by rfl) ⟨874310, by rfl⟩ : syracuseStep 1165747 = 1748621) B1748621
theorem B1558993 : Blo 920579 1558993 := bstep (se 2 (by rfl) ⟨584622, by rfl⟩ : syracuseStep 1558993 = 1169245) B1169245
theorem B1559027 : Blo 920579 1559027 := bstep (se 1 (by rfl) ⟨1169270, by rfl⟩ : syracuseStep 1559027 = 2338541) B2338541
theorem B1165843 : Blo 920579 1165843 := bstep (se 1 (by rfl) ⟨874382, by rfl⟩ : syracuseStep 1165843 = 1748765) B1748765
theorem B1559155 : Blo 920579 1559155 := bstep (se 1 (by rfl) ⟨1169366, by rfl⟩ : syracuseStep 1559155 = 2338733) B2338733
theorem B4672241 : Blo 920579 4672241 := bstep (se 2 (by rfl) ⟨1752090, by rfl⟩ : syracuseStep 4672241 = 3504181) B3504181
theorem B1559297 : Blo 920579 1559297 := bstep (se 2 (by rfl) ⟨584736, by rfl⟩ : syracuseStep 1559297 = 1169473) B1169473
theorem B22432625 : Blo 920579 22432625 := bstep (se 2 (by rfl) ⟨8412234, by rfl⟩ : syracuseStep 22432625 = 16824469) B16824469
theorem B1559425 : Blo 920579 1559425 := bstep (se 2 (by rfl) ⟨584784, by rfl⟩ : syracuseStep 1559425 = 1169569) B1169569
theorem B1559459 : Blo 920579 1559459 := bstep (se 1 (by rfl) ⟨1169594, by rfl⟩ : syracuseStep 1559459 = 2339189) B2339189
theorem B936883 : Blo 920579 936883 := bstep (se 1 (by rfl) ⟨702662, by rfl⟩ : syracuseStep 936883 = 1405325) B1405325
theorem B1166339 : Blo 920579 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1559587 : Blo 920579 1559587 := bstep (se 1 (by rfl) ⟨1169690, by rfl⟩ : syracuseStep 1559587 = 2339381) B2339381
theorem B1559729 : Blo 920579 1559729 := bstep (se 2 (by rfl) ⟨584898, by rfl⟩ : syracuseStep 1559729 = 1169797) B1169797
theorem B6638861 : Blo 920579 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B1559857 : Blo 920579 1559857 := bstep (se 2 (by rfl) ⟨584946, by rfl⟩ : syracuseStep 1559857 = 1169893) B1169893
theorem B1559891 : Blo 920579 1559891 := bstep (se 1 (by rfl) ⟨1169918, by rfl⟩ : syracuseStep 1559891 = 2339837) B2339837
theorem B1035715 : Blo 920579 1035715 := bstep (se 1 (by rfl) ⟨776786, by rfl⟩ : syracuseStep 1035715 = 1553573) B1553573
theorem B1560019 : Blo 920579 1560019 := bstep (se 1 (by rfl) ⟨1170014, by rfl⟩ : syracuseStep 1560019 = 2340029) B2340029
theorem B5262833 : Blo 920579 5262833 := bstep (se 2 (by rfl) ⟨1973562, by rfl⟩ : syracuseStep 5262833 = 3947125) B3947125
theorem B1035859 : Blo 920579 1035859 := bstep (se 1 (by rfl) ⟨776894, by rfl⟩ : syracuseStep 1035859 = 1553789) B1553789
theorem B1560161 : Blo 920579 1560161 := bstep (se 2 (by rfl) ⟨585060, by rfl⟩ : syracuseStep 1560161 = 1170121) B1170121
theorem B3001969 : Blo 920579 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B1167043 : Blo 920579 1167043 := bstep (se 1 (by rfl) ⟨875282, by rfl⟩ : syracuseStep 1167043 = 1750565) B1750565
theorem B1036003 : Blo 920579 1036003 := bstep (se 1 (by rfl) ⟨777002, by rfl⟩ : syracuseStep 1036003 = 1554005) B1554005
theorem B1167139 : Blo 920579 1167139 := bstep (se 1 (by rfl) ⟨875354, by rfl⟩ : syracuseStep 1167139 = 1750709) B1750709
theorem B1036147 : Blo 920579 1036147 := bstep (se 1 (by rfl) ⟨777110, by rfl⟩ : syracuseStep 1036147 = 1554221) B1554221
theorem B2805635 : Blo 920579 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B1036291 : Blo 920579 1036291 := bstep (se 1 (by rfl) ⟨777218, by rfl⟩ : syracuseStep 1036291 = 1554437) B1554437
theorem B1036435 : Blo 920579 1036435 := bstep (se 1 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 1036435 = 1554653) B1554653
theorem B4673699 : Blo 920579 4673699 := bstep (se 1 (by rfl) ⟨3505274, by rfl⟩ : syracuseStep 4673699 = 7010549) B7010549
theorem B1167635 : Blo 920579 1167635 := bstep (se 1 (by rfl) ⟨875726, by rfl⟩ : syracuseStep 1167635 = 1751453) B1751453
theorem B1036579 : Blo 920579 1036579 := bstep (se 1 (by rfl) ⟨777434, by rfl⟩ : syracuseStep 1036579 = 1554869) B1554869
theorem B1036723 : Blo 920579 1036723 := bstep (se 1 (by rfl) ⟨777542, by rfl⟩ : syracuseStep 1036723 = 1555085) B1555085
theorem B1036867 : Blo 920579 1036867 := bstep (se 1 (by rfl) ⟨777650, by rfl⟩ : syracuseStep 1036867 = 1555301) B1555301
theorem B1037011 : Blo 920579 1037011 := bstep (se 1 (by rfl) ⟨777758, by rfl⟩ : syracuseStep 1037011 = 1555517) B1555517
theorem B1037155 : Blo 920579 1037155 := bstep (se 1 (by rfl) ⟨777866, by rfl⟩ : syracuseStep 1037155 = 1555733) B1555733
theorem B2052977 : Blo 920579 2052977 := bstep (se 2 (by rfl) ⟨769866, by rfl⟩ : syracuseStep 2052977 = 1539733) B1539733
theorem B5264291 : Blo 920579 5264291 := bstep (se 1 (by rfl) ⟨3948218, by rfl⟩ : syracuseStep 5264291 = 7896437) B7896437
theorem B4674509 : Blo 920579 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B1168339 : Blo 920579 1168339 := bstep (se 1 (by rfl) ⟨876254, by rfl⟩ : syracuseStep 1168339 = 1752509) B1752509
theorem B1659889 : Blo 920579 1659889 := bstep (se 2 (by rfl) ⟨622458, by rfl⟩ : syracuseStep 1659889 = 1244917) B1244917
theorem B1037299 : Blo 920579 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B1168435 : Blo 920579 1168435 := bstep (se 1 (by rfl) ⟨876326, by rfl⟩ : syracuseStep 1168435 = 1752653) B1752653
theorem B1037443 : Blo 920579 1037443 := bstep (se 1 (by rfl) ⟨778082, by rfl⟩ : syracuseStep 1037443 = 1556165) B1556165
theorem B7001315 : Blo 920579 7001315 := bstep (se 1 (by rfl) ⟨5250986, by rfl⟩ : syracuseStep 7001315 = 10501973) B10501973
theorem B1660177 : Blo 920579 1660177 := bstep (se 2 (by rfl) ⟨622566, by rfl⟩ : syracuseStep 1660177 = 1245133) B1245133
theorem B1037587 : Blo 920579 1037587 := bstep (se 1 (by rfl) ⟨778190, by rfl⟩ : syracuseStep 1037587 = 1556381) B1556381
theorem B6313315 : Blo 920579 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B1037731 : Blo 920579 1037731 := bstep (se 1 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 1037731 = 1556597) B1556597
theorem B1168931 : Blo 920579 1168931 := bstep (se 1 (by rfl) ⟨876698, by rfl⟩ : syracuseStep 1168931 = 1753397) B1753397
theorem B1037875 : Blo 920579 1037875 := bstep (se 1 (by rfl) ⟨778406, by rfl⟩ : syracuseStep 1037875 = 1556813) B1556813
theorem B1038019 : Blo 920579 1038019 := bstep (se 1 (by rfl) ⟨778514, by rfl⟩ : syracuseStep 1038019 = 1557029) B1557029
theorem B1038163 : Blo 920579 1038163 := bstep (se 1 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 1038163 = 1557245) B1557245
theorem B2840465 : Blo 920579 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1038307 : Blo 920579 1038307 := bstep (se 1 (by rfl) ⟨778730, by rfl⟩ : syracuseStep 1038307 = 1557461) B1557461
theorem B2218097 : Blo 920579 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B1038451 : Blo 920579 1038451 := bstep (se 1 (by rfl) ⟨778838, by rfl⟩ : syracuseStep 1038451 = 1557677) B1557677
theorem B8411363 : Blo 920579 8411363 := bstep (se 1 (by rfl) ⟨6308522, by rfl⟩ : syracuseStep 8411363 = 12617045) B12617045
theorem B1169635 : Blo 920579 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B1038595 : Blo 920579 1038595 := bstep (se 1 (by rfl) ⟨778946, by rfl⟩ : syracuseStep 1038595 = 1557893) B1557893
theorem B1169731 : Blo 920579 1169731 := bstep (se 1 (by rfl) ⟨877298, by rfl⟩ : syracuseStep 1169731 = 1754597) B1754597
theorem B1038739 : Blo 920579 1038739 := bstep (se 1 (by rfl) ⟨779054, by rfl⟩ : syracuseStep 1038739 = 1558109) B1558109
theorem B5921201 : Blo 920579 5921201 := bstep (se 2 (by rfl) ⟨2220450, by rfl⟩ : syracuseStep 5921201 = 4440901) B4440901
theorem B1038883 : Blo 920579 1038883 := bstep (se 1 (by rfl) ⟨779162, by rfl⟩ : syracuseStep 1038883 = 1558325) B1558325
theorem B1039027 : Blo 920579 1039027 := bstep (se 1 (by rfl) ⟨779270, by rfl⟩ : syracuseStep 1039027 = 1558541) B1558541
theorem B2808557 : Blo 920579 2808557 := bstep (se 3 (by rfl) ⟨526604, by rfl⟩ : syracuseStep 2808557 = 1053209) B1053209
theorem B1039171 : Blo 920579 1039171 := bstep (se 1 (by rfl) ⟨779378, by rfl⟩ : syracuseStep 1039171 = 1558757) B1558757
theorem B18963341 : Blo 920579 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B2808749 : Blo 920579 2808749 := bstep (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) B1053281
theorem B1039315 : Blo 920579 1039315 := bstep (se 1 (by rfl) ⟨779486, by rfl⟩ : syracuseStep 1039315 = 1558973) B1558973
theorem B1039459 : Blo 920579 1039459 := bstep (se 1 (by rfl) ⟨779594, by rfl⟩ : syracuseStep 1039459 = 1559189) B1559189
theorem B3497165 : Blo 920579 3497165 := bstep (se 3 (by rfl) ⟨655718, by rfl⟩ : syracuseStep 3497165 = 1311437) B1311437
theorem B1039603 : Blo 920579 1039603 := bstep (se 1 (by rfl) ⟨779702, by rfl⟩ : syracuseStep 1039603 = 1559405) B1559405
theorem B1039747 : Blo 920579 1039747 := bstep (se 1 (by rfl) ⟨779810, by rfl⟩ : syracuseStep 1039747 = 1559621) B1559621
theorem B1039891 : Blo 920579 1039891 := bstep (se 1 (by rfl) ⟨779918, by rfl⟩ : syracuseStep 1039891 = 1559837) B1559837
theorem B1400483 : Blo 920579 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B1040035 : Blo 920579 1040035 := bstep (se 1 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 1040035 = 1560053) B1560053
theorem B4677425 : Blo 920579 4677425 := bstep (se 2 (by rfl) ⟨1754034, by rfl⟩ : syracuseStep 4677425 = 3508069) B3508069
theorem B1400915 : Blo 920579 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1401761 : Blo 920579 1401761 := bstep (se 2 (by rfl) ⟨525660, by rfl⟩ : syracuseStep 1401761 = 1051321) B1051321
theorem B2810819 : Blo 920579 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B22438853 : Blo 920579 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B11232227 : Blo 920579 11232227 := bstep (se 1 (by rfl) ⟨8424170, by rfl⟩ : syracuseStep 11232227 = 16848341) B16848341
theorem B4678883 : Blo 920579 4678883 := bstep (se 1 (by rfl) ⟨3509162, by rfl⟩ : syracuseStep 4678883 = 7018325) B7018325
theorem B1107203 : Blo 920579 1107203 := bstep (se 1 (by rfl) ⟨830402, by rfl⟩ : syracuseStep 1107203 = 1660805) B1660805
theorem B3990797 : Blo 920579 3990797 := bstep (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) B1496549
theorem B1402211 : Blo 920579 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B1664675 : Blo 920579 1664675 := bstep (se 1 (by rfl) ⟨1248506, by rfl⟩ : syracuseStep 1664675 = 2497013) B2497013
theorem B1664849 : Blo 920579 1664849 := bstep (se 2 (by rfl) ⟨624318, by rfl⟩ : syracuseStep 1664849 = 1248637) B1248637
theorem B1402721 : Blo 920579 1402721 := bstep (se 2 (by rfl) ⟨526020, by rfl⟩ : syracuseStep 1402721 = 1052041) B1052041
theorem B1402867 : Blo 920579 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B4679693 : Blo 920579 4679693 := bstep (se 3 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 4679693 = 1754885) B1754885
theorem B3500081 : Blo 920579 3500081 := bstep (se 2 (by rfl) ⟨1312530, by rfl⟩ : syracuseStep 3500081 = 2625061) B2625061
theorem B1665137 : Blo 920579 1665137 := bstep (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) B1248853
theorem B1403075 : Blo 920579 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B15952099 : Blo 920579 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B3107213 : Blo 920579 3107213 := bstep (se 3 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 3107213 = 1165205) B1165205
theorem B3074449 : Blo 920579 3074449 := bstep (se 2 (by rfl) ⟨1152918, by rfl⟩ : syracuseStep 3074449 = 2305837) B2305837
theorem B3107267 : Blo 920579 3107267 := bstep (se 1 (by rfl) ⟨2330450, by rfl⟩ : syracuseStep 3107267 = 4660901) B4660901
theorem B7006661 : Blo 920579 7006661 := bstep (se 4 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 7006661 = 1313749) B1313749
theorem B1665713 : Blo 920579 1665713 := bstep (se 2 (by rfl) ⟨624642, by rfl⟩ : syracuseStep 1665713 = 1249285) B1249285
theorem B3107537 : Blo 920579 3107537 := bstep (se 2 (by rfl) ⟨1165326, by rfl⟩ : syracuseStep 3107537 = 2330653) B2330653
theorem B11398157 : Blo 920579 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B1797233 : Blo 920579 1797233 := bstep (se 2 (by rfl) ⟨673962, by rfl⟩ : syracuseStep 1797233 = 1347925) B1347925
theorem B3108077 : Blo 920579 3108077 := bstep (se 3 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 3108077 = 1165529) B1165529
theorem B3108131 : Blo 920579 3108131 := bstep (se 1 (by rfl) ⟨2331098, by rfl⟩ : syracuseStep 3108131 = 4662197) B4662197
theorem B1404371 : Blo 920579 1404371 := bstep (se 1 (by rfl) ⟨1053278, by rfl⟩ : syracuseStep 1404371 = 2106557) B2106557
theorem B3501539 : Blo 920579 3501539 := bstep (se 1 (by rfl) ⟨2626154, by rfl⟩ : syracuseStep 3501539 = 5252309) B5252309
theorem B3108401 : Blo 920579 3108401 := bstep (se 2 (by rfl) ⟨1165650, by rfl⟩ : syracuseStep 3108401 = 2331301) B2331301
theorem B17985077 : Blo 920579 17985077 := bstep (se 5 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 17985077 = 1686101) B1686101
theorem B5598989 : Blo 920579 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B1109971 : Blo 920579 1109971 := bstep (se 1 (by rfl) ⟨832478, by rfl⟩ : syracuseStep 1109971 = 1664957) B1664957
theorem B3108941 : Blo 920579 3108941 := bstep (se 3 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 3108941 = 1165853) B1165853
theorem B3108995 : Blo 920579 3108995 := bstep (se 1 (by rfl) ⟨2331746, by rfl⟩ : syracuseStep 3108995 = 4663493) B4663493
theorem B1405153 : Blo 920579 1405153 := bstep (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) B1053865
theorem B3109265 : Blo 920579 3109265 := bstep (se 2 (by rfl) ⟨1165974, by rfl⟩ : syracuseStep 3109265 = 2331949) B2331949
theorem B3502541 : Blo 920579 3502541 := bstep (se 3 (by rfl) ⟨656726, by rfl⟩ : syracuseStep 3502541 = 1313453) B1313453
theorem B7893773 : Blo 920579 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B4977571 : Blo 920579 4977571 := bstep (se 1 (by rfl) ⟨3733178, by rfl⟩ : syracuseStep 4977571 = 7466357) B7466357
theorem B3109805 : Blo 920579 3109805 := bstep (se 3 (by rfl) ⟨583088, by rfl⟩ : syracuseStep 3109805 = 1166177) B1166177
theorem B3109859 : Blo 920579 3109859 := bstep (se 1 (by rfl) ⟨2332394, by rfl⟩ : syracuseStep 3109859 = 4664789) B4664789
theorem B3110129 : Blo 920579 3110129 := bstep (se 2 (by rfl) ⟨1166298, by rfl⟩ : syracuseStep 3110129 = 2332597) B2332597
theorem B6649073 : Blo 920579 6649073 := bstep (se 2 (by rfl) ⟨2493402, by rfl⟩ : syracuseStep 6649073 = 4986805) B4986805
theorem B3110669 : Blo 920579 3110669 := bstep (se 3 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 3110669 = 1166501) B1166501
theorem B3110723 : Blo 920579 3110723 := bstep (se 1 (by rfl) ⟨2333042, by rfl⟩ : syracuseStep 3110723 = 4666085) B4666085
theorem B8877923 : Blo 920579 8877923 := bstep (se 1 (by rfl) ⟨6658442, by rfl⟩ : syracuseStep 8877923 = 13316885) B13316885
theorem B3733517 : Blo 920579 3733517 := bstep (se 3 (by rfl) ⟨700034, by rfl⟩ : syracuseStep 3733517 = 1400069) B1400069
theorem B20183093 : Blo 920579 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B3110993 : Blo 920579 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B3504653 : Blo 920579 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B2849293 : Blo 920579 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B3111533 : Blo 920579 3111533 := bstep (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) B1166825
theorem B3111587 : Blo 920579 3111587 := bstep (se 1 (by rfl) ⟨2333690, by rfl⟩ : syracuseStep 3111587 = 4667381) B4667381
theorem B2489251 : Blo 920579 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B3111857 : Blo 920579 3111857 := bstep (se 2 (by rfl) ⟨1166946, by rfl⟩ : syracuseStep 3111857 = 2333893) B2333893
theorem B7896163 : Blo 920579 7896163 := bstep (se 1 (by rfl) ⟨5922122, by rfl⟩ : syracuseStep 7896163 = 11844245) B11844245
theorem B1539233 : Blo 920579 1539233 := bstep (se 2 (by rfl) ⟨577212, by rfl⟩ : syracuseStep 1539233 = 1154425) B1154425
theorem B3505457 : Blo 920579 3505457 := bstep (se 2 (by rfl) ⟨1314546, by rfl⟩ : syracuseStep 3505457 = 2629093) B2629093
theorem B1244593 : Blo 920579 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B3112397 : Blo 920579 3112397 := bstep (se 3 (by rfl) ⟨583574, by rfl⟩ : syracuseStep 3112397 = 1167149) B1167149
theorem B3112451 : Blo 920579 3112451 := bstep (se 1 (by rfl) ⟨2334338, by rfl⟩ : syracuseStep 3112451 = 4668677) B4668677
theorem B3112721 : Blo 920579 3112721 := bstep (se 2 (by rfl) ⟨1167270, by rfl⟩ : syracuseStep 3112721 = 2334541) B2334541
theorem B3506125 : Blo 920579 3506125 := bstep (se 3 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 3506125 = 1314797) B1314797
theorem B3113153 : Blo 920579 3113153 := bstep (se 2 (by rfl) ⟨1167432, by rfl⟩ : syracuseStep 3113153 = 2334865) B2334865
theorem B3932363 : Blo 920579 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B3735773 : Blo 920579 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B2621747 : Blo 920579 2621747 := bstep (se 1 (by rfl) ⟨1966310, by rfl⟩ : syracuseStep 2621747 = 3932621) B3932621
theorem B2490689 : Blo 920579 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B3506611 : Blo 920579 3506611 := bstep (se 1 (by rfl) ⟨2629958, by rfl⟩ : syracuseStep 3506611 = 5259917) B5259917
theorem B3736115 : Blo 920579 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B8422019 : Blo 920579 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B983723 : Blo 920579 983723 := bstep (se 1 (by rfl) ⟨737792, by rfl⟩ : syracuseStep 983723 = 1475585) B1475585
theorem B2622145 : Blo 920579 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B1802969 : Blo 920579 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B3113693 : Blo 920579 3113693 := bstep (se 3 (by rfl) ⟨583817, by rfl⟩ : syracuseStep 3113693 = 1167635) B1167635
theorem B3932945 : Blo 920579 3932945 := bstep (se 2 (by rfl) ⟨1474854, by rfl⟩ : syracuseStep 3932945 = 2949709) B2949709
theorem B5899159 : Blo 920579 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B1967105 : Blo 920579 1967105 := bstep (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) B1475329
theorem B7898147 : Blo 920579 7898147 := bstep (se 1 (by rfl) ⟨5923610, by rfl⟩ : syracuseStep 7898147 = 11847221) B11847221
theorem B2950195 : Blo 920579 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B1312075 : Blo 920579 1312075 := bstep (se 1 (by rfl) ⟨984056, by rfl⟩ : syracuseStep 1312075 = 1968113) B1968113
theorem B26936725 : Blo 920579 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B2491955 : Blo 920579 2491955 := bstep (se 1 (by rfl) ⟨1868966, by rfl⟩ : syracuseStep 2491955 = 3737933) B3737933
theorem B3507857 : Blo 920579 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B8849047 : Blo 920579 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B984727 : Blo 920579 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B3934003 : Blo 920579 3934003 := bstep (se 1 (by rfl) ⟨2950502, by rfl⟩ : syracuseStep 3934003 = 5901005) B5901005
theorem B3114827 : Blo 920579 3114827 := bstep (se 1 (by rfl) ⟨2336120, by rfl⟩ : syracuseStep 3114827 = 4672241) B4672241
theorem B3115097 : Blo 920579 3115097 := bstep (se 2 (by rfl) ⟨1168161, by rfl⟩ : syracuseStep 3115097 = 2336323) B2336323
theorem B3508555 : Blo 920579 3508555 := bstep (se 1 (by rfl) ⟨2631416, by rfl⟩ : syracuseStep 3508555 = 5262833) B5262833
theorem B2492765 : Blo 920579 2492765 := bstep (se 3 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 2492765 = 934787) B934787
theorem B985483 : Blo 920579 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B4983389 : Blo 920579 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B29952605 : Blo 920579 29952605 := bstep (se 3 (by rfl) ⟨5616113, by rfl⟩ : syracuseStep 29952605 = 11232227) B11232227
theorem B3508829 : Blo 920579 3508829 := bstep (se 3 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 3508829 = 1315811) B1315811
theorem B1968779 : Blo 920579 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B1870489 : Blo 920579 1870489 := bstep (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) B1402867
theorem B9472717 : Blo 920579 9472717 := bstep (se 3 (by rfl) ⟨1776134, by rfl⟩ : syracuseStep 9472717 = 3552269) B3552269
theorem B3115799 : Blo 920579 3115799 := bstep (se 1 (by rfl) ⟨2336849, by rfl⟩ : syracuseStep 3115799 = 4673699) B4673699
theorem B1248139 : Blo 920579 1248139 := bstep (se 1 (by rfl) ⟨936104, by rfl⟩ : syracuseStep 1248139 = 1872209) B1872209
theorem B1248215 : Blo 920579 1248215 := bstep (se 1 (by rfl) ⟨936161, by rfl⟩ : syracuseStep 1248215 = 1872323) B1872323
theorem B21269465 : Blo 920579 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B920587 : Blo 920579 920587 := bstep (se 1 (by rfl) ⟨690440, by rfl⟩ : syracuseStep 920587 = 1380881) B1380881
theorem B920599 : Blo 920579 920599 := bstep (se 1 (by rfl) ⟨690449, by rfl⟩ : syracuseStep 920599 = 1380899) B1380899
theorem B920619 : Blo 920579 920619 := bstep (se 1 (by rfl) ⟨690464, by rfl⟩ : syracuseStep 920619 = 1380929) B1380929
theorem B920631 : Blo 920579 920631 := bstep (se 1 (by rfl) ⟨690473, by rfl⟩ : syracuseStep 920631 = 1380947) B1380947
theorem B920651 : Blo 920579 920651 := bstep (se 1 (by rfl) ⟨690488, by rfl⟩ : syracuseStep 920651 = 1380977) B1380977
theorem B920663 : Blo 920579 920663 := bstep (se 1 (by rfl) ⟨690497, by rfl⟩ : syracuseStep 920663 = 1380995) B1380995
theorem B5246045 : Blo 920579 5246045 := bstep (se 3 (by rfl) ⟨983633, by rfl⟩ : syracuseStep 5246045 = 1967267) B1967267
theorem B920683 : Blo 920579 920683 := bstep (se 1 (by rfl) ⟨690512, by rfl⟩ : syracuseStep 920683 = 1381025) B1381025
theorem B920695 : Blo 920579 920695 := bstep (se 1 (by rfl) ⟨690521, by rfl⟩ : syracuseStep 920695 = 1381043) B1381043
theorem B920715 : Blo 920579 920715 := bstep (se 1 (by rfl) ⟨690536, by rfl⟩ : syracuseStep 920715 = 1381073) B1381073
theorem B920727 : Blo 920579 920727 := bstep (se 1 (by rfl) ⟨690545, by rfl⟩ : syracuseStep 920727 = 1381091) B1381091
theorem B2624663 : Blo 920579 2624663 := bstep (se 1 (by rfl) ⟨1968497, by rfl⟩ : syracuseStep 2624663 = 3936995) B3936995
theorem B920747 : Blo 920579 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B3935405 : Blo 920579 3935405 := bstep (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) B1475777
theorem B920759 : Blo 920579 920759 := bstep (se 1 (by rfl) ⟨690569, by rfl⟩ : syracuseStep 920759 = 1381139) B1381139
theorem B4099265 : Blo 920579 4099265 := bstep (se 2 (by rfl) ⟨1537224, by rfl⟩ : syracuseStep 4099265 = 3074449) B3074449
theorem B920779 : Blo 920579 920779 := bstep (se 1 (by rfl) ⟨690584, by rfl⟩ : syracuseStep 920779 = 1381169) B1381169
theorem B920791 : Blo 920579 920791 := bstep (se 1 (by rfl) ⟨690593, by rfl⟩ : syracuseStep 920791 = 1381187) B1381187
theorem B920811 : Blo 920579 920811 := bstep (se 1 (by rfl) ⟨690608, by rfl⟩ : syracuseStep 920811 = 1381217) B1381217
theorem B920823 : Blo 920579 920823 := bstep (se 1 (by rfl) ⟨690617, by rfl⟩ : syracuseStep 920823 = 1381235) B1381235
theorem B920843 : Blo 920579 920843 := bstep (se 1 (by rfl) ⟨690632, by rfl⟩ : syracuseStep 920843 = 1381265) B1381265
theorem B920855 : Blo 920579 920855 := bstep (se 1 (by rfl) ⟨690641, by rfl⟩ : syracuseStep 920855 = 1381283) B1381283
theorem B3509527 : Blo 920579 3509527 := bstep (se 1 (by rfl) ⟨2632145, by rfl⟩ : syracuseStep 3509527 = 5264291) B5264291
theorem B920875 : Blo 920579 920875 := bstep (se 1 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 920875 = 1381313) B1381313
theorem B3116339 : Blo 920579 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B920887 : Blo 920579 920887 := bstep (se 1 (by rfl) ⟨690665, by rfl⟩ : syracuseStep 920887 = 1381331) B1381331
theorem B920907 : Blo 920579 920907 := bstep (se 1 (by rfl) ⟨690680, by rfl⟩ : syracuseStep 920907 = 1381361) B1381361
theorem B920919 : Blo 920579 920919 := bstep (se 1 (by rfl) ⟨690689, by rfl⟩ : syracuseStep 920919 = 1381379) B1381379
theorem B2952541 : Blo 920579 2952541 := bstep (se 3 (by rfl) ⟨553601, by rfl⟩ : syracuseStep 2952541 = 1107203) B1107203
theorem B920939 : Blo 920579 920939 := bstep (se 1 (by rfl) ⟨690704, by rfl⟩ : syracuseStep 920939 = 1381409) B1381409
theorem B920951 : Blo 920579 920951 := bstep (se 1 (by rfl) ⟨690713, by rfl⟩ : syracuseStep 920951 = 1381427) B1381427
theorem B920971 : Blo 920579 920971 := bstep (se 1 (by rfl) ⟨690728, by rfl⟩ : syracuseStep 920971 = 1381457) B1381457
theorem B920983 : Blo 920579 920983 := bstep (se 1 (by rfl) ⟨690737, by rfl⟩ : syracuseStep 920983 = 1381475) B1381475
theorem B921003 : Blo 920579 921003 := bstep (se 1 (by rfl) ⟨690752, by rfl⟩ : syracuseStep 921003 = 1381505) B1381505
theorem B921015 : Blo 920579 921015 := bstep (se 1 (by rfl) ⟨690761, by rfl⟩ : syracuseStep 921015 = 1381523) B1381523
theorem B921035 : Blo 920579 921035 := bstep (se 1 (by rfl) ⟨690776, by rfl⟩ : syracuseStep 921035 = 1381553) B1381553
theorem B921047 : Blo 920579 921047 := bstep (se 1 (by rfl) ⟨690785, by rfl⟩ : syracuseStep 921047 = 1381571) B1381571
theorem B921067 : Blo 920579 921067 := bstep (se 1 (by rfl) ⟨690800, by rfl⟩ : syracuseStep 921067 = 1381601) B1381601
theorem B921079 : Blo 920579 921079 := bstep (se 1 (by rfl) ⟨690809, by rfl⟩ : syracuseStep 921079 = 1381619) B1381619
theorem B921099 : Blo 920579 921099 := bstep (se 1 (by rfl) ⟨690824, by rfl⟩ : syracuseStep 921099 = 1381649) B1381649
theorem B921111 : Blo 920579 921111 := bstep (se 1 (by rfl) ⟨690833, by rfl⟩ : syracuseStep 921111 = 1381667) B1381667
theorem B921131 : Blo 920579 921131 := bstep (se 1 (by rfl) ⟨690848, by rfl⟩ : syracuseStep 921131 = 1381697) B1381697
theorem B921143 : Blo 920579 921143 := bstep (se 1 (by rfl) ⟨690857, by rfl⟩ : syracuseStep 921143 = 1381715) B1381715
theorem B3116609 : Blo 920579 3116609 := bstep (se 2 (by rfl) ⟨1168728, by rfl⟩ : syracuseStep 3116609 = 2337457) B2337457
theorem B921163 : Blo 920579 921163 := bstep (se 1 (by rfl) ⟨690872, by rfl⟩ : syracuseStep 921163 = 1381745) B1381745
theorem B921175 : Blo 920579 921175 := bstep (se 1 (by rfl) ⟨690881, by rfl⟩ : syracuseStep 921175 = 1381763) B1381763
theorem B1969753 : Blo 920579 1969753 := bstep (se 2 (by rfl) ⟨738657, by rfl⟩ : syracuseStep 1969753 = 1477315) B1477315
theorem B3739229 : Blo 920579 3739229 := bstep (se 3 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 3739229 = 1402211) B1402211
theorem B921195 : Blo 920579 921195 := bstep (se 1 (by rfl) ⟨690896, by rfl⟩ : syracuseStep 921195 = 1381793) B1381793
theorem B921207 : Blo 920579 921207 := bstep (se 1 (by rfl) ⟨690905, by rfl⟩ : syracuseStep 921207 = 1381811) B1381811
theorem B921227 : Blo 920579 921227 := bstep (se 1 (by rfl) ⟨690920, by rfl⟩ : syracuseStep 921227 = 1381841) B1381841
theorem B921239 : Blo 920579 921239 := bstep (se 1 (by rfl) ⟨690929, by rfl⟩ : syracuseStep 921239 = 1381859) B1381859
theorem B921259 : Blo 920579 921259 := bstep (se 1 (by rfl) ⟨690944, by rfl⟩ : syracuseStep 921259 = 1381889) B1381889
theorem B921271 : Blo 920579 921271 := bstep (se 1 (by rfl) ⟨690953, by rfl⟩ : syracuseStep 921271 = 1381907) B1381907
theorem B921291 : Blo 920579 921291 := bstep (se 1 (by rfl) ⟨690968, by rfl⟩ : syracuseStep 921291 = 1381937) B1381937
theorem B921303 : Blo 920579 921303 := bstep (se 1 (by rfl) ⟨690977, by rfl⟩ : syracuseStep 921303 = 1381955) B1381955
theorem B2330329 : Blo 920579 2330329 := bstep (se 2 (by rfl) ⟨873873, by rfl⟩ : syracuseStep 2330329 = 1747747) B1747747
theorem B2559709 : Blo 920579 2559709 := bstep (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) B959891
theorem B921323 : Blo 920579 921323 := bstep (se 1 (by rfl) ⟨690992, by rfl⟩ : syracuseStep 921323 = 1381985) B1381985
theorem B921335 : Blo 920579 921335 := bstep (se 1 (by rfl) ⟨691001, by rfl⟩ : syracuseStep 921335 = 1382003) B1382003
theorem B921355 : Blo 920579 921355 := bstep (se 1 (by rfl) ⟨691016, by rfl⟩ : syracuseStep 921355 = 1382033) B1382033
theorem B921367 : Blo 920579 921367 := bstep (se 1 (by rfl) ⟨691025, by rfl⟩ : syracuseStep 921367 = 1382051) B1382051
theorem B921387 : Blo 920579 921387 := bstep (se 1 (by rfl) ⟨691040, by rfl⟩ : syracuseStep 921387 = 1382081) B1382081
theorem B921399 : Blo 920579 921399 := bstep (se 1 (by rfl) ⟨691049, by rfl⟩ : syracuseStep 921399 = 1382099) B1382099
theorem B5246795 : Blo 920579 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B921419 : Blo 920579 921419 := bstep (se 1 (by rfl) ⟨691064, by rfl⟩ : syracuseStep 921419 = 1382129) B1382129
theorem B921431 : Blo 920579 921431 := bstep (se 1 (by rfl) ⟨691073, by rfl⟩ : syracuseStep 921431 = 1382147) B1382147
theorem B2101081 : Blo 920579 2101081 := bstep (se 2 (by rfl) ⟨787905, by rfl⟩ : syracuseStep 2101081 = 1575811) B1575811
theorem B1970009 : Blo 920579 1970009 := bstep (se 2 (by rfl) ⟨738753, by rfl⟩ : syracuseStep 1970009 = 1477507) B1477507
theorem B921451 : Blo 920579 921451 := bstep (se 1 (by rfl) ⟨691088, by rfl⟩ : syracuseStep 921451 = 1382177) B1382177
theorem B921463 : Blo 920579 921463 := bstep (se 1 (by rfl) ⟨691097, by rfl⟩ : syracuseStep 921463 = 1382195) B1382195
theorem B921483 : Blo 920579 921483 := bstep (se 1 (by rfl) ⟨691112, by rfl⟩ : syracuseStep 921483 = 1382225) B1382225
theorem B921495 : Blo 920579 921495 := bstep (se 1 (by rfl) ⟨691121, by rfl⟩ : syracuseStep 921495 = 1382243) B1382243
theorem B1249177 : Blo 920579 1249177 := bstep (se 2 (by rfl) ⟨468441, by rfl⟩ : syracuseStep 1249177 = 936883) B936883
theorem B921515 : Blo 920579 921515 := bstep (se 1 (by rfl) ⟨691136, by rfl⟩ : syracuseStep 921515 = 1382273) B1382273
theorem B921527 : Blo 920579 921527 := bstep (se 1 (by rfl) ⟨691145, by rfl⟩ : syracuseStep 921527 = 1382291) B1382291
theorem B921547 : Blo 920579 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B1183691 : Blo 920579 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B921559 : Blo 920579 921559 := bstep (se 1 (by rfl) ⟨691169, by rfl⟩ : syracuseStep 921559 = 1382339) B1382339
theorem B921579 : Blo 920579 921579 := bstep (se 1 (by rfl) ⟨691184, by rfl⟩ : syracuseStep 921579 = 1382369) B1382369
theorem B921591 : Blo 920579 921591 := bstep (se 1 (by rfl) ⟨691193, by rfl⟩ : syracuseStep 921591 = 1382387) B1382387
theorem B921611 : Blo 920579 921611 := bstep (se 1 (by rfl) ⟨691208, by rfl⟩ : syracuseStep 921611 = 1382417) B1382417
theorem B921623 : Blo 920579 921623 := bstep (se 1 (by rfl) ⟨691217, by rfl⟩ : syracuseStep 921623 = 1382435) B1382435
theorem B921643 : Blo 920579 921643 := bstep (se 1 (by rfl) ⟨691232, by rfl⟩ : syracuseStep 921643 = 1382465) B1382465
theorem B3510317 : Blo 920579 3510317 := bstep (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) B1316369
theorem B921655 : Blo 920579 921655 := bstep (se 1 (by rfl) ⟨691241, by rfl⟩ : syracuseStep 921655 = 1382483) B1382483
theorem B921675 : Blo 920579 921675 := bstep (se 1 (by rfl) ⟨691256, by rfl⟩ : syracuseStep 921675 = 1382513) B1382513
theorem B1478731 : Blo 920579 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B921687 : Blo 920579 921687 := bstep (se 1 (by rfl) ⟨691265, by rfl⟩ : syracuseStep 921687 = 1382531) B1382531
theorem B3117149 : Blo 920579 3117149 := bstep (se 3 (by rfl) ⟨584465, by rfl⟩ : syracuseStep 3117149 = 1168931) B1168931
theorem B921707 : Blo 920579 921707 := bstep (se 1 (by rfl) ⟨691280, by rfl⟩ : syracuseStep 921707 = 1382561) B1382561
theorem B921719 : Blo 920579 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B921739 : Blo 920579 921739 := bstep (se 1 (by rfl) ⟨691304, by rfl⟩ : syracuseStep 921739 = 1382609) B1382609
theorem B88871053 : Blo 920579 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B921751 : Blo 920579 921751 := bstep (se 1 (by rfl) ⟨691313, by rfl⟩ : syracuseStep 921751 = 1382627) B1382627
theorem B5607575 : Blo 920579 5607575 := bstep (se 1 (by rfl) ⟨4205681, by rfl⟩ : syracuseStep 5607575 = 8411363) B8411363
theorem B921771 : Blo 920579 921771 := bstep (se 1 (by rfl) ⟨691328, by rfl⟩ : syracuseStep 921771 = 1382657) B1382657
theorem B921783 : Blo 920579 921783 := bstep (se 1 (by rfl) ⟨691337, by rfl⟩ : syracuseStep 921783 = 1382675) B1382675
theorem B921803 : Blo 920579 921803 := bstep (se 1 (by rfl) ⟨691352, by rfl⟩ : syracuseStep 921803 = 1382705) B1382705
theorem B2494667 : Blo 920579 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B921815 : Blo 920579 921815 := bstep (se 1 (by rfl) ⟨691361, by rfl⟩ : syracuseStep 921815 = 1382723) B1382723
theorem B921835 : Blo 920579 921835 := bstep (se 1 (by rfl) ⟨691376, by rfl⟩ : syracuseStep 921835 = 1382753) B1382753
theorem B1970419 : Blo 920579 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B921847 : Blo 920579 921847 := bstep (se 1 (by rfl) ⟨691385, by rfl⟩ : syracuseStep 921847 = 1382771) B1382771
theorem B921867 : Blo 920579 921867 := bstep (se 1 (by rfl) ⟨691400, by rfl⟩ : syracuseStep 921867 = 1382801) B1382801
theorem B921879 : Blo 920579 921879 := bstep (se 1 (by rfl) ⟨691409, by rfl⟩ : syracuseStep 921879 = 1382819) B1382819
theorem B921899 : Blo 920579 921899 := bstep (se 1 (by rfl) ⟨691424, by rfl⟩ : syracuseStep 921899 = 1382849) B1382849
theorem B921911 : Blo 920579 921911 := bstep (se 1 (by rfl) ⟨691433, by rfl⟩ : syracuseStep 921911 = 1382867) B1382867
theorem B921931 : Blo 920579 921931 := bstep (se 1 (by rfl) ⟨691448, by rfl⟩ : syracuseStep 921931 = 1382897) B1382897
theorem B921943 : Blo 920579 921943 := bstep (se 1 (by rfl) ⟨691457, by rfl⟩ : syracuseStep 921943 = 1382915) B1382915
theorem B921963 : Blo 920579 921963 := bstep (se 1 (by rfl) ⟨691472, by rfl⟩ : syracuseStep 921963 = 1382945) B1382945
theorem B19960181 : Blo 920579 19960181 := bstep (se 5 (by rfl) ⟨935633, by rfl⟩ : syracuseStep 19960181 = 1871267) B1871267
theorem B921975 : Blo 920579 921975 := bstep (se 1 (by rfl) ⟨691481, by rfl⟩ : syracuseStep 921975 = 1382963) B1382963
theorem B921995 : Blo 920579 921995 := bstep (se 1 (by rfl) ⟨691496, by rfl⟩ : syracuseStep 921995 = 1382993) B1382993
theorem B922007 : Blo 920579 922007 := bstep (se 1 (by rfl) ⟨691505, by rfl⟩ : syracuseStep 922007 = 1383011) B1383011
theorem B922027 : Blo 920579 922027 := bstep (se 1 (by rfl) ⟨691520, by rfl⟩ : syracuseStep 922027 = 1383041) B1383041
theorem B922039 : Blo 920579 922039 := bstep (se 1 (by rfl) ⟨691529, by rfl⟩ : syracuseStep 922039 = 1383059) B1383059
theorem B922059 : Blo 920579 922059 := bstep (se 1 (by rfl) ⟨691544, by rfl⟩ : syracuseStep 922059 = 1383089) B1383089
theorem B2625995 : Blo 920579 2625995 := bstep (se 1 (by rfl) ⟨1969496, by rfl⟩ : syracuseStep 2625995 = 3938993) B3938993
theorem B922071 : Blo 920579 922071 := bstep (se 1 (by rfl) ⟨691553, by rfl⟩ : syracuseStep 922071 = 1383107) B1383107
theorem B2494937 : Blo 920579 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B922091 : Blo 920579 922091 := bstep (se 1 (by rfl) ⟨691568, by rfl⟩ : syracuseStep 922091 = 1383137) B1383137
theorem B1872371 : Blo 920579 1872371 := bstep (se 1 (by rfl) ⟨1404278, by rfl⟩ : syracuseStep 1872371 = 2808557) B2808557
theorem B922103 : Blo 920579 922103 := bstep (se 1 (by rfl) ⟨691577, by rfl⟩ : syracuseStep 922103 = 1383155) B1383155
theorem B1380875 : Blo 920579 1380875 := bstep (se 1 (by rfl) ⟨1035656, by rfl⟩ : syracuseStep 1380875 = 2071313) B2071313
theorem B922123 : Blo 920579 922123 := bstep (se 1 (by rfl) ⟨691592, by rfl⟩ : syracuseStep 922123 = 1383185) B1383185
theorem B1380887 : Blo 920579 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B922135 : Blo 920579 922135 := bstep (se 1 (by rfl) ⟨691601, by rfl⟩ : syracuseStep 922135 = 1383203) B1383203
theorem B922155 : Blo 920579 922155 := bstep (se 1 (by rfl) ⟨691616, by rfl⟩ : syracuseStep 922155 = 1383233) B1383233
theorem B922167 : Blo 920579 922167 := bstep (se 1 (by rfl) ⟨691625, by rfl⟩ : syracuseStep 922167 = 1383251) B1383251
theorem B922187 : Blo 920579 922187 := bstep (se 1 (by rfl) ⟨691640, by rfl⟩ : syracuseStep 922187 = 1383281) B1383281
theorem B922199 : Blo 920579 922199 := bstep (se 1 (by rfl) ⟨691649, by rfl⟩ : syracuseStep 922199 = 1383299) B1383299
theorem B1380953 : Blo 920579 1380953 := bstep (se 2 (by rfl) ⟨517857, by rfl⟩ : syracuseStep 1380953 = 1035715) B1035715
theorem B922219 : Blo 920579 922219 := bstep (se 1 (by rfl) ⟨691664, by rfl⟩ : syracuseStep 922219 = 1383329) B1383329
theorem B922231 : Blo 920579 922231 := bstep (se 1 (by rfl) ⟨691673, by rfl⟩ : syracuseStep 922231 = 1383347) B1383347
theorem B922251 : Blo 920579 922251 := bstep (se 1 (by rfl) ⟨691688, by rfl⟩ : syracuseStep 922251 = 1383377) B1383377
theorem B922263 : Blo 920579 922263 := bstep (se 1 (by rfl) ⟨691697, by rfl⟩ : syracuseStep 922263 = 1383395) B1383395
theorem B922283 : Blo 920579 922283 := bstep (se 1 (by rfl) ⟨691712, by rfl⟩ : syracuseStep 922283 = 1383425) B1383425
theorem B922295 : Blo 920579 922295 := bstep (se 1 (by rfl) ⟨691721, by rfl⟩ : syracuseStep 922295 = 1383443) B1383443
theorem B1381067 : Blo 920579 1381067 := bstep (se 1 (by rfl) ⟨1035800, by rfl⟩ : syracuseStep 1381067 = 2071601) B2071601
theorem B922315 : Blo 920579 922315 := bstep (se 1 (by rfl) ⟨691736, by rfl⟩ : syracuseStep 922315 = 1383473) B1383473
theorem B1381079 : Blo 920579 1381079 := bstep (se 1 (by rfl) ⟨1035809, by rfl⟩ : syracuseStep 1381079 = 2071619) B2071619
theorem B922327 : Blo 920579 922327 := bstep (se 1 (by rfl) ⟨691745, by rfl⟩ : syracuseStep 922327 = 1383491) B1383491
theorem B922347 : Blo 920579 922347 := bstep (se 1 (by rfl) ⟨691760, by rfl⟩ : syracuseStep 922347 = 1383521) B1383521
theorem B922359 : Blo 920579 922359 := bstep (se 1 (by rfl) ⟨691769, by rfl⟩ : syracuseStep 922359 = 1383539) B1383539
theorem B9966341 : Blo 920579 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B922379 : Blo 920579 922379 := bstep (se 1 (by rfl) ⟨691784, by rfl⟩ : syracuseStep 922379 = 1383569) B1383569
theorem B922391 : Blo 920579 922391 := bstep (se 1 (by rfl) ⟨691793, by rfl⟩ : syracuseStep 922391 = 1383587) B1383587
theorem B1381145 : Blo 920579 1381145 := bstep (se 2 (by rfl) ⟨517929, by rfl⟩ : syracuseStep 1381145 = 1035859) B1035859
theorem B922411 : Blo 920579 922411 := bstep (se 1 (by rfl) ⟨691808, by rfl⟩ : syracuseStep 922411 = 1383617) B1383617
theorem B2331443 : Blo 920579 2331443 := bstep (se 1 (by rfl) ⟨1748582, by rfl⟩ : syracuseStep 2331443 = 3497165) B3497165
theorem B922423 : Blo 920579 922423 := bstep (se 1 (by rfl) ⟨691817, by rfl⟩ : syracuseStep 922423 = 1383635) B1383635
theorem B4002625 : Blo 920579 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B922443 : Blo 920579 922443 := bstep (se 1 (by rfl) ⟨691832, by rfl⟩ : syracuseStep 922443 = 1383665) B1383665
theorem B922455 : Blo 920579 922455 := bstep (se 1 (by rfl) ⟨691841, by rfl⟩ : syracuseStep 922455 = 1383683) B1383683
theorem B922475 : Blo 920579 922475 := bstep (se 1 (by rfl) ⟨691856, by rfl⟩ : syracuseStep 922475 = 1383713) B1383713
theorem B922487 : Blo 920579 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B1381259 : Blo 920579 1381259 := bstep (se 1 (by rfl) ⟨1035944, by rfl⟩ : syracuseStep 1381259 = 2071889) B2071889
theorem B922507 : Blo 920579 922507 := bstep (se 1 (by rfl) ⟨691880, by rfl⟩ : syracuseStep 922507 = 1383761) B1383761
theorem B1381271 : Blo 920579 1381271 := bstep (se 1 (by rfl) ⟨1035953, by rfl⟩ : syracuseStep 1381271 = 2071907) B2071907
theorem B922519 : Blo 920579 922519 := bstep (se 1 (by rfl) ⟨691889, by rfl⟩ : syracuseStep 922519 = 1383779) B1383779
theorem B922539 : Blo 920579 922539 := bstep (se 1 (by rfl) ⟨691904, by rfl⟩ : syracuseStep 922539 = 1383809) B1383809
theorem B922551 : Blo 920579 922551 := bstep (se 1 (by rfl) ⟨691913, by rfl⟩ : syracuseStep 922551 = 1383827) B1383827
theorem B1971137 : Blo 920579 1971137 := bstep (se 2 (by rfl) ⟨739176, by rfl⟩ : syracuseStep 1971137 = 1478353) B1478353
theorem B922571 : Blo 920579 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B922583 : Blo 920579 922583 := bstep (se 1 (by rfl) ⟨691937, by rfl⟩ : syracuseStep 922583 = 1383875) B1383875
theorem B1381337 : Blo 920579 1381337 := bstep (se 2 (by rfl) ⟨518001, by rfl⟩ : syracuseStep 1381337 = 1036003) B1036003
theorem B922603 : Blo 920579 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B922615 : Blo 920579 922615 := bstep (se 1 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 922615 = 1383923) B1383923
theorem B922635 : Blo 920579 922635 := bstep (se 1 (by rfl) ⟨691976, by rfl⟩ : syracuseStep 922635 = 1383953) B1383953
theorem B922647 : Blo 920579 922647 := bstep (se 1 (by rfl) ⟨691985, by rfl⟩ : syracuseStep 922647 = 1383971) B1383971
theorem B922667 : Blo 920579 922667 := bstep (se 1 (by rfl) ⟨692000, by rfl⟩ : syracuseStep 922667 = 1384001) B1384001
theorem B7574573 : Blo 920579 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B922679 : Blo 920579 922679 := bstep (se 1 (by rfl) ⟨692009, by rfl⟩ : syracuseStep 922679 = 1384019) B1384019
theorem B1381451 : Blo 920579 1381451 := bstep (se 1 (by rfl) ⟨1036088, by rfl⟩ : syracuseStep 1381451 = 2072177) B2072177
theorem B922699 : Blo 920579 922699 := bstep (se 1 (by rfl) ⟨692024, by rfl⟩ : syracuseStep 922699 = 1384049) B1384049
theorem B1381463 : Blo 920579 1381463 := bstep (se 1 (by rfl) ⟨1036097, by rfl⟩ : syracuseStep 1381463 = 2072195) B2072195
theorem B922711 : Blo 920579 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B2331737 : Blo 920579 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B922731 : Blo 920579 922731 := bstep (se 1 (by rfl) ⟨692048, by rfl⟩ : syracuseStep 922731 = 1384097) B1384097
theorem B922743 : Blo 920579 922743 := bstep (se 1 (by rfl) ⟨692057, by rfl⟩ : syracuseStep 922743 = 1384115) B1384115
theorem B922763 : Blo 920579 922763 := bstep (se 1 (by rfl) ⟨692072, by rfl⟩ : syracuseStep 922763 = 1384145) B1384145
theorem B922775 : Blo 920579 922775 := bstep (se 1 (by rfl) ⟨692081, by rfl⟩ : syracuseStep 922775 = 1384163) B1384163
theorem B1381529 : Blo 920579 1381529 := bstep (se 2 (by rfl) ⟨518073, by rfl⟩ : syracuseStep 1381529 = 1036147) B1036147
theorem B922795 : Blo 920579 922795 := bstep (se 1 (by rfl) ⟨692096, by rfl⟩ : syracuseStep 922795 = 1384193) B1384193
theorem B922807 : Blo 920579 922807 := bstep (se 1 (by rfl) ⟨692105, by rfl⟩ : syracuseStep 922807 = 1384211) B1384211
theorem B3118283 : Blo 920579 3118283 := bstep (se 1 (by rfl) ⟨2338712, by rfl⟩ : syracuseStep 3118283 = 4677425) B4677425
theorem B922827 : Blo 920579 922827 := bstep (se 1 (by rfl) ⟨692120, by rfl⟩ : syracuseStep 922827 = 1384241) B1384241
theorem B922839 : Blo 920579 922839 := bstep (se 1 (by rfl) ⟨692129, by rfl⟩ : syracuseStep 922839 = 1384259) B1384259
theorem B922859 : Blo 920579 922859 := bstep (se 1 (by rfl) ⟨692144, by rfl⟩ : syracuseStep 922859 = 1384289) B1384289
theorem B922871 : Blo 920579 922871 := bstep (se 1 (by rfl) ⟨692153, by rfl⟩ : syracuseStep 922871 = 1384307) B1384307
theorem B1381643 : Blo 920579 1381643 := bstep (se 1 (by rfl) ⟨1036232, by rfl⟩ : syracuseStep 1381643 = 2072465) B2072465
theorem B922891 : Blo 920579 922891 := bstep (se 1 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 922891 = 1384337) B1384337
theorem B1381655 : Blo 920579 1381655 := bstep (se 1 (by rfl) ⟨1036241, by rfl⟩ : syracuseStep 1381655 = 2072483) B2072483
theorem B922903 : Blo 920579 922903 := bstep (se 1 (by rfl) ⟨692177, by rfl⟩ : syracuseStep 922903 = 1384355) B1384355
theorem B1971479 : Blo 920579 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B1479961 : Blo 920579 1479961 := bstep (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) B1109971
theorem B922923 : Blo 920579 922923 := bstep (se 1 (by rfl) ⟨692192, by rfl⟩ : syracuseStep 922923 = 1384385) B1384385
theorem B922935 : Blo 920579 922935 := bstep (se 1 (by rfl) ⟨692201, by rfl⟩ : syracuseStep 922935 = 1384403) B1384403
theorem B922955 : Blo 920579 922955 := bstep (se 1 (by rfl) ⟨692216, by rfl⟩ : syracuseStep 922955 = 1384433) B1384433
theorem B922967 : Blo 920579 922967 := bstep (se 1 (by rfl) ⟨692225, by rfl⟩ : syracuseStep 922967 = 1384451) B1384451
theorem B1381721 : Blo 920579 1381721 := bstep (se 2 (by rfl) ⟨518145, by rfl⟩ : syracuseStep 1381721 = 1036291) B1036291
theorem B922987 : Blo 920579 922987 := bstep (se 1 (by rfl) ⟨692240, by rfl⟩ : syracuseStep 922987 = 1384481) B1384481
theorem B922999 : Blo 920579 922999 := bstep (se 1 (by rfl) ⟨692249, by rfl⟩ : syracuseStep 922999 = 1384499) B1384499
theorem B923019 : Blo 920579 923019 := bstep (se 1 (by rfl) ⟨692264, by rfl⟩ : syracuseStep 923019 = 1384529) B1384529
theorem B923031 : Blo 920579 923031 := bstep (se 1 (by rfl) ⟨692273, by rfl⟩ : syracuseStep 923031 = 1384547) B1384547
theorem B923051 : Blo 920579 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B5248435 : Blo 920579 5248435 := bstep (se 1 (by rfl) ⟨3936326, by rfl⟩ : syracuseStep 5248435 = 7872653) B7872653
theorem B923063 : Blo 920579 923063 := bstep (se 1 (by rfl) ⟨692297, by rfl⟩ : syracuseStep 923063 = 1384595) B1384595
theorem B1971649 : Blo 920579 1971649 := bstep (se 2 (by rfl) ⟨739368, by rfl⟩ : syracuseStep 1971649 = 1478737) B1478737
theorem B1381835 : Blo 920579 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B923083 : Blo 920579 923083 := bstep (se 1 (by rfl) ⟨692312, by rfl⟩ : syracuseStep 923083 = 1384625) B1384625
theorem B1381847 : Blo 920579 1381847 := bstep (se 1 (by rfl) ⟨1036385, by rfl⟩ : syracuseStep 1381847 = 2072771) B2072771
theorem B923095 : Blo 920579 923095 := bstep (se 1 (by rfl) ⟨692321, by rfl⟩ : syracuseStep 923095 = 1384643) B1384643
theorem B3118553 : Blo 920579 3118553 := bstep (se 2 (by rfl) ⟨1169457, by rfl⟩ : syracuseStep 3118553 = 2338915) B2338915
theorem B923115 : Blo 920579 923115 := bstep (se 1 (by rfl) ⟨692336, by rfl⟩ : syracuseStep 923115 = 1384673) B1384673
theorem B923127 : Blo 920579 923127 := bstep (se 1 (by rfl) ⟨692345, by rfl⟩ : syracuseStep 923127 = 1384691) B1384691
theorem B923147 : Blo 920579 923147 := bstep (se 1 (by rfl) ⟨692360, by rfl⟩ : syracuseStep 923147 = 1384721) B1384721
theorem B923159 : Blo 920579 923159 := bstep (se 1 (by rfl) ⟨692369, by rfl⟩ : syracuseStep 923159 = 1384739) B1384739
theorem B1381913 : Blo 920579 1381913 := bstep (se 2 (by rfl) ⟨518217, by rfl⟩ : syracuseStep 1381913 = 1036435) B1036435
theorem B923179 : Blo 920579 923179 := bstep (se 1 (by rfl) ⟨692384, by rfl⟩ : syracuseStep 923179 = 1384769) B1384769
theorem B923191 : Blo 920579 923191 := bstep (se 1 (by rfl) ⟨692393, by rfl⟩ : syracuseStep 923191 = 1384787) B1384787
theorem B923211 : Blo 920579 923211 := bstep (se 1 (by rfl) ⟨692408, by rfl⟩ : syracuseStep 923211 = 1384817) B1384817
theorem B923223 : Blo 920579 923223 := bstep (se 1 (by rfl) ⟨692417, by rfl⟩ : syracuseStep 923223 = 1384835) B1384835
theorem B923243 : Blo 920579 923243 := bstep (se 1 (by rfl) ⟨692432, by rfl⟩ : syracuseStep 923243 = 1384865) B1384865
theorem B923255 : Blo 920579 923255 := bstep (se 1 (by rfl) ⟨692441, by rfl⟩ : syracuseStep 923255 = 1384883) B1384883
theorem B1382027 : Blo 920579 1382027 := bstep (se 1 (by rfl) ⟨1036520, by rfl⟩ : syracuseStep 1382027 = 2073041) B2073041
theorem B923275 : Blo 920579 923275 := bstep (se 1 (by rfl) ⟨692456, by rfl⟩ : syracuseStep 923275 = 1384913) B1384913
theorem B1382039 : Blo 920579 1382039 := bstep (se 1 (by rfl) ⟨1036529, by rfl⟩ : syracuseStep 1382039 = 2073059) B2073059
theorem B923287 : Blo 920579 923287 := bstep (se 1 (by rfl) ⟨692465, by rfl⟩ : syracuseStep 923287 = 1384931) B1384931
theorem B923307 : Blo 920579 923307 := bstep (se 1 (by rfl) ⟨692480, by rfl⟩ : syracuseStep 923307 = 1384961) B1384961
theorem B923319 : Blo 920579 923319 := bstep (se 1 (by rfl) ⟨692489, by rfl⟩ : syracuseStep 923319 = 1384979) B1384979
theorem B2102987 : Blo 920579 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B923339 : Blo 920579 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B923351 : Blo 920579 923351 := bstep (se 1 (by rfl) ⟨692513, by rfl⟩ : syracuseStep 923351 = 1385027) B1385027
theorem B1382105 : Blo 920579 1382105 := bstep (se 2 (by rfl) ⟨518289, by rfl⟩ : syracuseStep 1382105 = 1036579) B1036579
theorem B923371 : Blo 920579 923371 := bstep (se 1 (by rfl) ⟨692528, by rfl⟩ : syracuseStep 923371 = 1385057) B1385057
theorem B923383 : Blo 920579 923383 := bstep (se 1 (by rfl) ⟨692537, by rfl⟩ : syracuseStep 923383 = 1385075) B1385075
theorem B923403 : Blo 920579 923403 := bstep (se 1 (by rfl) ⟨692552, by rfl⟩ : syracuseStep 923403 = 1385105) B1385105
theorem B923415 : Blo 920579 923415 := bstep (se 1 (by rfl) ⟨692561, by rfl⟩ : syracuseStep 923415 = 1385123) B1385123
theorem B923435 : Blo 920579 923435 := bstep (se 1 (by rfl) ⟨692576, by rfl⟩ : syracuseStep 923435 = 1385153) B1385153
theorem B923447 : Blo 920579 923447 := bstep (se 1 (by rfl) ⟨692585, by rfl⟩ : syracuseStep 923447 = 1385171) B1385171
theorem B1382219 : Blo 920579 1382219 := bstep (se 1 (by rfl) ⟨1036664, by rfl⟩ : syracuseStep 1382219 = 2073329) B2073329
theorem B923467 : Blo 920579 923467 := bstep (se 1 (by rfl) ⟨692600, by rfl⟩ : syracuseStep 923467 = 1385201) B1385201
theorem B1382231 : Blo 920579 1382231 := bstep (se 1 (by rfl) ⟨1036673, by rfl⟩ : syracuseStep 1382231 = 2073347) B2073347
theorem B923479 : Blo 920579 923479 := bstep (se 1 (by rfl) ⟨692609, by rfl⟩ : syracuseStep 923479 = 1385219) B1385219
theorem B4200281 : Blo 920579 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B923499 : Blo 920579 923499 := bstep (se 1 (by rfl) ⟨692624, by rfl⟩ : syracuseStep 923499 = 1385249) B1385249
theorem B923511 : Blo 920579 923511 := bstep (se 1 (by rfl) ⟨692633, by rfl⟩ : syracuseStep 923511 = 1385267) B1385267
theorem B923531 : Blo 920579 923531 := bstep (se 1 (by rfl) ⟨692648, by rfl⟩ : syracuseStep 923531 = 1385297) B1385297
theorem B923543 : Blo 920579 923543 := bstep (se 1 (by rfl) ⟨692657, by rfl⟩ : syracuseStep 923543 = 1385315) B1385315
theorem B1382297 : Blo 920579 1382297 := bstep (se 2 (by rfl) ⟨518361, by rfl⟩ : syracuseStep 1382297 = 1036723) B1036723
theorem B923563 : Blo 920579 923563 := bstep (se 1 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 923563 = 1385345) B1385345
theorem B923575 : Blo 920579 923575 := bstep (se 1 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 923575 = 1385363) B1385363
theorem B923595 : Blo 920579 923595 := bstep (se 1 (by rfl) ⟨692696, by rfl⟩ : syracuseStep 923595 = 1385393) B1385393
theorem B923607 : Blo 920579 923607 := bstep (se 1 (by rfl) ⟨692705, by rfl⟩ : syracuseStep 923607 = 1385411) B1385411
theorem B923627 : Blo 920579 923627 := bstep (se 1 (by rfl) ⟨692720, by rfl⟩ : syracuseStep 923627 = 1385441) B1385441
theorem B923639 : Blo 920579 923639 := bstep (se 1 (by rfl) ⟨692729, by rfl⟩ : syracuseStep 923639 = 1385459) B1385459
theorem B1382411 : Blo 920579 1382411 := bstep (se 1 (by rfl) ⟨1036808, by rfl⟩ : syracuseStep 1382411 = 2073617) B2073617
theorem B923659 : Blo 920579 923659 := bstep (se 1 (by rfl) ⟨692744, by rfl⟩ : syracuseStep 923659 = 1385489) B1385489
theorem B1382423 : Blo 920579 1382423 := bstep (se 1 (by rfl) ⟨1036817, by rfl⟩ : syracuseStep 1382423 = 2073635) B2073635
theorem B923671 : Blo 920579 923671 := bstep (se 1 (by rfl) ⟨692753, by rfl⟩ : syracuseStep 923671 = 1385507) B1385507
theorem B923691 : Blo 920579 923691 := bstep (se 1 (by rfl) ⟨692768, by rfl⟩ : syracuseStep 923691 = 1385537) B1385537
theorem B2627635 : Blo 920579 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B923703 : Blo 920579 923703 := bstep (se 1 (by rfl) ⟨692777, by rfl⟩ : syracuseStep 923703 = 1385555) B1385555
theorem B923723 : Blo 920579 923723 := bstep (se 1 (by rfl) ⟨692792, by rfl⟩ : syracuseStep 923723 = 1385585) B1385585
theorem B923735 : Blo 920579 923735 := bstep (se 1 (by rfl) ⟨692801, by rfl⟩ : syracuseStep 923735 = 1385603) B1385603
theorem B3151961 : Blo 920579 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B1382489 : Blo 920579 1382489 := bstep (se 2 (by rfl) ⟨518433, by rfl⟩ : syracuseStep 1382489 = 1036867) B1036867
theorem B5609573 : Blo 920579 5609573 := bstep (se 4 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 5609573 = 1051795) B1051795
theorem B923755 : Blo 920579 923755 := bstep (se 1 (by rfl) ⟨692816, by rfl⟩ : syracuseStep 923755 = 1385633) B1385633
theorem B923767 : Blo 920579 923767 := bstep (se 1 (by rfl) ⟨692825, by rfl⟩ : syracuseStep 923767 = 1385651) B1385651
theorem B2103425 : Blo 920579 2103425 := bstep (se 2 (by rfl) ⟨788784, by rfl⟩ : syracuseStep 2103425 = 1577569) B1577569
theorem B923787 : Blo 920579 923787 := bstep (se 1 (by rfl) ⟨692840, by rfl⟩ : syracuseStep 923787 = 1385681) B1385681
theorem B923799 : Blo 920579 923799 := bstep (se 1 (by rfl) ⟨692849, by rfl⟩ : syracuseStep 923799 = 1385699) B1385699
theorem B3119255 : Blo 920579 3119255 := bstep (se 1 (by rfl) ⟨2339441, by rfl⟩ : syracuseStep 3119255 = 4678883) B4678883
theorem B923819 : Blo 920579 923819 := bstep (se 1 (by rfl) ⟨692864, by rfl⟩ : syracuseStep 923819 = 1385729) B1385729
theorem B2660531 : Blo 920579 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B923831 : Blo 920579 923831 := bstep (se 1 (by rfl) ⟨692873, by rfl⟩ : syracuseStep 923831 = 1385747) B1385747
theorem B1382603 : Blo 920579 1382603 := bstep (se 1 (by rfl) ⟨1036952, by rfl⟩ : syracuseStep 1382603 = 2073905) B2073905
theorem B923851 : Blo 920579 923851 := bstep (se 1 (by rfl) ⟨692888, by rfl⟩ : syracuseStep 923851 = 1385777) B1385777
theorem B1382615 : Blo 920579 1382615 := bstep (se 1 (by rfl) ⟨1036961, by rfl⟩ : syracuseStep 1382615 = 2073923) B2073923
theorem B923863 : Blo 920579 923863 := bstep (se 1 (by rfl) ⟨692897, by rfl⟩ : syracuseStep 923863 = 1385795) B1385795
theorem B1579225 : Blo 920579 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B923883 : Blo 920579 923883 := bstep (se 1 (by rfl) ⟨692912, by rfl⟩ : syracuseStep 923883 = 1385825) B1385825
theorem B923895 : Blo 920579 923895 := bstep (se 1 (by rfl) ⟨692921, by rfl⟩ : syracuseStep 923895 = 1385843) B1385843
theorem B923915 : Blo 920579 923915 := bstep (se 1 (by rfl) ⟨692936, by rfl⟩ : syracuseStep 923915 = 1385873) B1385873
theorem B923927 : Blo 920579 923927 := bstep (se 1 (by rfl) ⟨692945, by rfl⟩ : syracuseStep 923927 = 1385891) B1385891
theorem B1382681 : Blo 920579 1382681 := bstep (se 2 (by rfl) ⟨518505, by rfl⟩ : syracuseStep 1382681 = 1037011) B1037011
theorem B923947 : Blo 920579 923947 := bstep (se 1 (by rfl) ⟨692960, by rfl⟩ : syracuseStep 923947 = 1385921) B1385921
theorem B923959 : Blo 920579 923959 := bstep (se 1 (by rfl) ⟨692969, by rfl⟩ : syracuseStep 923959 = 1385939) B1385939
theorem B923979 : Blo 920579 923979 := bstep (se 1 (by rfl) ⟨692984, by rfl⟩ : syracuseStep 923979 = 1385969) B1385969
theorem B923991 : Blo 920579 923991 := bstep (se 1 (by rfl) ⟨692993, by rfl⟩ : syracuseStep 923991 = 1385987) B1385987
theorem B924011 : Blo 920579 924011 := bstep (se 1 (by rfl) ⟨693008, by rfl⟩ : syracuseStep 924011 = 1386017) B1386017
theorem B924023 : Blo 920579 924023 := bstep (se 1 (by rfl) ⟨693017, by rfl⟩ : syracuseStep 924023 = 1386035) B1386035
theorem B1382795 : Blo 920579 1382795 := bstep (se 1 (by rfl) ⟨1037096, by rfl⟩ : syracuseStep 1382795 = 2074193) B2074193
theorem B924043 : Blo 920579 924043 := bstep (se 1 (by rfl) ⟨693032, by rfl⟩ : syracuseStep 924043 = 1386065) B1386065
theorem B1382807 : Blo 920579 1382807 := bstep (se 1 (by rfl) ⟨1037105, by rfl⟩ : syracuseStep 1382807 = 2074211) B2074211
theorem B924055 : Blo 920579 924055 := bstep (se 1 (by rfl) ⟨693041, by rfl⟩ : syracuseStep 924055 = 1386083) B1386083
theorem B924075 : Blo 920579 924075 := bstep (se 1 (by rfl) ⟨693056, by rfl⟩ : syracuseStep 924075 = 1386113) B1386113
theorem B924087 : Blo 920579 924087 := bstep (se 1 (by rfl) ⟨693065, by rfl⟩ : syracuseStep 924087 = 1386131) B1386131
theorem B924107 : Blo 920579 924107 := bstep (se 1 (by rfl) ⟨693080, by rfl⟩ : syracuseStep 924107 = 1386161) B1386161
theorem B924119 : Blo 920579 924119 := bstep (se 1 (by rfl) ⟨693089, by rfl⟩ : syracuseStep 924119 = 1386179) B1386179
theorem B1382873 : Blo 920579 1382873 := bstep (se 2 (by rfl) ⟨518577, by rfl⟩ : syracuseStep 1382873 = 1037155) B1037155
theorem B924139 : Blo 920579 924139 := bstep (se 1 (by rfl) ⟨693104, by rfl⟩ : syracuseStep 924139 = 1386209) B1386209
theorem B924151 : Blo 920579 924151 := bstep (se 1 (by rfl) ⟨693113, by rfl⟩ : syracuseStep 924151 = 1386227) B1386227
theorem B924171 : Blo 920579 924171 := bstep (se 1 (by rfl) ⟨693128, by rfl⟩ : syracuseStep 924171 = 1386257) B1386257
theorem B13310477 : Blo 920579 13310477 := bstep (se 3 (by rfl) ⟨2495714, by rfl⟩ : syracuseStep 13310477 = 4991429) B4991429
theorem B3545623 : Blo 920579 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B924183 : Blo 920579 924183 := bstep (se 1 (by rfl) ⟨693137, by rfl⟩ : syracuseStep 924183 = 1386275) B1386275
theorem B924203 : Blo 920579 924203 := bstep (se 1 (by rfl) ⟨693152, by rfl⟩ : syracuseStep 924203 = 1386305) B1386305
theorem B924215 : Blo 920579 924215 := bstep (se 1 (by rfl) ⟨693161, by rfl⟩ : syracuseStep 924215 = 1386323) B1386323
theorem B1382987 : Blo 920579 1382987 := bstep (se 1 (by rfl) ⟨1037240, by rfl⟩ : syracuseStep 1382987 = 2074481) B2074481
theorem B2366027 : Blo 920579 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B1972811 : Blo 920579 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B924235 : Blo 920579 924235 := bstep (se 1 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 924235 = 1386353) B1386353
theorem B1382999 : Blo 920579 1382999 := bstep (se 1 (by rfl) ⟨1037249, by rfl⟩ : syracuseStep 1382999 = 2074499) B2074499
theorem B924247 : Blo 920579 924247 := bstep (se 1 (by rfl) ⟨693185, by rfl⟩ : syracuseStep 924247 = 1386371) B1386371
theorem B924267 : Blo 920579 924267 := bstep (se 1 (by rfl) ⟨693200, by rfl⟩ : syracuseStep 924267 = 1386401) B1386401
theorem B924279 : Blo 920579 924279 := bstep (se 1 (by rfl) ⟨693209, by rfl⟩ : syracuseStep 924279 = 1386419) B1386419
theorem B924299 : Blo 920579 924299 := bstep (se 1 (by rfl) ⟨693224, by rfl⟩ : syracuseStep 924299 = 1386449) B1386449
theorem B924311 : Blo 920579 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B1383065 : Blo 920579 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B924331 : Blo 920579 924331 := bstep (se 1 (by rfl) ⟨693248, by rfl⟩ : syracuseStep 924331 = 1386497) B1386497
theorem B3119795 : Blo 920579 3119795 := bstep (se 1 (by rfl) ⟨2339846, by rfl⟩ : syracuseStep 3119795 = 4679693) B4679693
theorem B924343 : Blo 920579 924343 := bstep (se 1 (by rfl) ⟨693257, by rfl⟩ : syracuseStep 924343 = 1386515) B1386515
theorem B2333387 : Blo 920579 2333387 := bstep (se 1 (by rfl) ⟨1750040, by rfl⟩ : syracuseStep 2333387 = 3500081) B3500081
theorem B924363 : Blo 920579 924363 := bstep (se 1 (by rfl) ⟨693272, by rfl⟩ : syracuseStep 924363 = 1386545) B1386545
theorem B15768269 : Blo 920579 15768269 := bstep (se 3 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 15768269 = 5913101) B5913101
theorem B924375 : Blo 920579 924375 := bstep (se 1 (by rfl) ⟨693281, by rfl⟩ : syracuseStep 924375 = 1386563) B1386563
theorem B924395 : Blo 920579 924395 := bstep (se 1 (by rfl) ⟨693296, by rfl⟩ : syracuseStep 924395 = 1386593) B1386593
theorem B924407 : Blo 920579 924407 := bstep (se 1 (by rfl) ⟨693305, by rfl⟩ : syracuseStep 924407 = 1386611) B1386611
theorem B1383179 : Blo 920579 1383179 := bstep (se 1 (by rfl) ⟨1037384, by rfl⟩ : syracuseStep 1383179 = 2074769) B2074769
theorem B924427 : Blo 920579 924427 := bstep (se 1 (by rfl) ⟨693320, by rfl⟩ : syracuseStep 924427 = 1386641) B1386641
theorem B1383191 : Blo 920579 1383191 := bstep (se 1 (by rfl) ⟨1037393, by rfl⟩ : syracuseStep 1383191 = 2074787) B2074787
theorem B924439 : Blo 920579 924439 := bstep (se 1 (by rfl) ⟨693329, by rfl⟩ : syracuseStep 924439 = 1386659) B1386659
theorem B924459 : Blo 920579 924459 := bstep (se 1 (by rfl) ⟨693344, by rfl⟩ : syracuseStep 924459 = 1386689) B1386689
theorem B924471 : Blo 920579 924471 := bstep (se 1 (by rfl) ⟨693353, by rfl⟩ : syracuseStep 924471 = 1386707) B1386707
theorem B924491 : Blo 920579 924491 := bstep (se 1 (by rfl) ⟨693368, by rfl⟩ : syracuseStep 924491 = 1386737) B1386737
theorem B924503 : Blo 920579 924503 := bstep (se 1 (by rfl) ⟨693377, by rfl⟩ : syracuseStep 924503 = 1386755) B1386755
theorem B2071385 : Blo 920579 2071385 := bstep (se 2 (by rfl) ⟨776769, by rfl⟩ : syracuseStep 2071385 = 1553539) B1553539
theorem B1383257 : Blo 920579 1383257 := bstep (se 2 (by rfl) ⟨518721, by rfl⟩ : syracuseStep 1383257 = 1037443) B1037443
theorem B5249893 : Blo 920579 5249893 := bstep (se 4 (by rfl) ⟨492177, by rfl⟩ : syracuseStep 5249893 = 984355) B984355
theorem B924523 : Blo 920579 924523 := bstep (se 1 (by rfl) ⟨693392, by rfl⟩ : syracuseStep 924523 = 1386785) B1386785
theorem B924535 : Blo 920579 924535 := bstep (se 1 (by rfl) ⟨693401, by rfl⟩ : syracuseStep 924535 = 1386803) B1386803
theorem B924555 : Blo 920579 924555 := bstep (se 1 (by rfl) ⟨693416, by rfl⟩ : syracuseStep 924555 = 1386833) B1386833
theorem B924567 : Blo 920579 924567 := bstep (se 1 (by rfl) ⟨693425, by rfl⟩ : syracuseStep 924567 = 1386851) B1386851
theorem B1711001 : Blo 920579 1711001 := bstep (se 2 (by rfl) ⟨641625, by rfl⟩ : syracuseStep 1711001 = 1283251) B1283251
theorem B2071475 : Blo 920579 2071475 := bstep (se 1 (by rfl) ⟨1553606, by rfl⟩ : syracuseStep 2071475 = 3107213) B3107213
theorem B3120065 : Blo 920579 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B1383371 : Blo 920579 1383371 := bstep (se 1 (by rfl) ⟨1037528, by rfl⟩ : syracuseStep 1383371 = 2075057) B2075057
theorem B2071511 : Blo 920579 2071511 := bstep (se 1 (by rfl) ⟨1553633, by rfl⟩ : syracuseStep 2071511 = 3107267) B3107267
theorem B1383383 : Blo 920579 1383383 := bstep (se 1 (by rfl) ⟨1037537, by rfl⟩ : syracuseStep 1383383 = 2075075) B2075075
theorem B1383449 : Blo 920579 1383449 := bstep (se 2 (by rfl) ⟨518793, by rfl⟩ : syracuseStep 1383449 = 1037587) B1037587
theorem B2628683 : Blo 920579 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B2071691 : Blo 920579 2071691 := bstep (se 1 (by rfl) ⟨1553768, by rfl⟩ : syracuseStep 2071691 = 3107537) B3107537
theorem B1383563 : Blo 920579 1383563 := bstep (se 1 (by rfl) ⟨1037672, by rfl⟩ : syracuseStep 1383563 = 2075345) B2075345
theorem B1383575 : Blo 920579 1383575 := bstep (se 1 (by rfl) ⟨1037681, by rfl⟩ : syracuseStep 1383575 = 2075363) B2075363
theorem B2071745 : Blo 920579 2071745 := bstep (se 2 (by rfl) ⟨776904, by rfl⟩ : syracuseStep 2071745 = 1553809) B1553809
theorem B1383641 : Blo 920579 1383641 := bstep (se 2 (by rfl) ⟨518865, by rfl⟩ : syracuseStep 1383641 = 1037731) B1037731
theorem B3939607 : Blo 920579 3939607 := bstep (se 1 (by rfl) ⟨2954705, by rfl⟩ : syracuseStep 3939607 = 5909411) B5909411
theorem B1973555 : Blo 920579 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B1383755 : Blo 920579 1383755 := bstep (se 1 (by rfl) ⟨1037816, by rfl⟩ : syracuseStep 1383755 = 2075633) B2075633
theorem B1383767 : Blo 920579 1383767 := bstep (se 1 (by rfl) ⟨1037825, by rfl⟩ : syracuseStep 1383767 = 2075651) B2075651
theorem B3939677 : Blo 920579 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B2071961 : Blo 920579 2071961 := bstep (se 2 (by rfl) ⟨776985, by rfl⟩ : syracuseStep 2071961 = 1553971) B1553971
theorem B1383833 : Blo 920579 1383833 := bstep (se 2 (by rfl) ⟨518937, by rfl⟩ : syracuseStep 1383833 = 1037875) B1037875
theorem B2072051 : Blo 920579 2072051 := bstep (se 1 (by rfl) ⟨1554038, by rfl⟩ : syracuseStep 2072051 = 3108077) B3108077
theorem B1383947 : Blo 920579 1383947 := bstep (se 1 (by rfl) ⟨1037960, by rfl⟩ : syracuseStep 1383947 = 2075921) B2075921
theorem B2072087 : Blo 920579 2072087 := bstep (se 1 (by rfl) ⟨1554065, by rfl⟩ : syracuseStep 2072087 = 3108131) B3108131
theorem B1383959 : Blo 920579 1383959 := bstep (se 1 (by rfl) ⟨1037969, by rfl⟩ : syracuseStep 1383959 = 2075939) B2075939
theorem B1384025 : Blo 920579 1384025 := bstep (se 2 (by rfl) ⟨519009, by rfl⟩ : syracuseStep 1384025 = 1038019) B1038019
theorem B2334359 : Blo 920579 2334359 := bstep (se 1 (by rfl) ⟨1750769, by rfl⟩ : syracuseStep 2334359 = 3501539) B3501539
theorem B2072267 : Blo 920579 2072267 := bstep (se 1 (by rfl) ⟨1554200, by rfl⟩ : syracuseStep 2072267 = 3108401) B3108401
theorem B1384139 : Blo 920579 1384139 := bstep (se 1 (by rfl) ⟨1038104, by rfl⟩ : syracuseStep 1384139 = 2076209) B2076209
theorem B1384151 : Blo 920579 1384151 := bstep (se 1 (by rfl) ⟨1038113, by rfl⟩ : syracuseStep 1384151 = 2076227) B2076227
theorem B2072321 : Blo 920579 2072321 := bstep (se 2 (by rfl) ⟨777120, by rfl⟩ : syracuseStep 2072321 = 1554241) B1554241
theorem B1384217 : Blo 920579 1384217 := bstep (se 2 (by rfl) ⟨519081, by rfl⟩ : syracuseStep 1384217 = 1038163) B1038163
theorem B1384331 : Blo 920579 1384331 := bstep (se 1 (by rfl) ⟨1038248, by rfl⟩ : syracuseStep 1384331 = 2076497) B2076497
theorem B1384343 : Blo 920579 1384343 := bstep (se 1 (by rfl) ⟨1038257, by rfl⟩ : syracuseStep 1384343 = 2076515) B2076515
theorem B2072537 : Blo 920579 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B1384409 : Blo 920579 1384409 := bstep (se 2 (by rfl) ⟨519153, by rfl⟩ : syracuseStep 1384409 = 1038307) B1038307
theorem B2072627 : Blo 920579 2072627 := bstep (se 1 (by rfl) ⟨1554470, by rfl⟩ : syracuseStep 2072627 = 3108941) B3108941
theorem B3940427 : Blo 920579 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1384523 : Blo 920579 1384523 := bstep (se 1 (by rfl) ⟨1038392, by rfl⟩ : syracuseStep 1384523 = 2076785) B2076785
theorem B2072663 : Blo 920579 2072663 := bstep (se 1 (by rfl) ⟨1554497, by rfl⟩ : syracuseStep 2072663 = 3108995) B3108995
theorem B1384535 : Blo 920579 1384535 := bstep (se 1 (by rfl) ⟨1038401, by rfl⟩ : syracuseStep 1384535 = 2076803) B2076803
theorem B1384601 : Blo 920579 1384601 := bstep (se 2 (by rfl) ⟨519225, by rfl⟩ : syracuseStep 1384601 = 1038451) B1038451
theorem B1581209 : Blo 920579 1581209 := bstep (se 2 (by rfl) ⟨592953, by rfl⟩ : syracuseStep 1581209 = 1185907) B1185907
theorem B2367667 : Blo 920579 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B1974451 : Blo 920579 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B2072843 : Blo 920579 2072843 := bstep (se 1 (by rfl) ⟨1554632, by rfl⟩ : syracuseStep 2072843 = 3109265) B3109265
theorem B1384715 : Blo 920579 1384715 := bstep (se 1 (by rfl) ⟨1038536, by rfl⟩ : syracuseStep 1384715 = 2077073) B2077073
theorem B1384727 : Blo 920579 1384727 := bstep (se 1 (by rfl) ⟨1038545, by rfl⟩ : syracuseStep 1384727 = 2077091) B2077091
theorem B4661549 : Blo 920579 4661549 := bstep (se 3 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 4661549 = 1748081) B1748081
theorem B4792621 : Blo 920579 4792621 := bstep (se 3 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 4792621 = 1797233) B1797233
theorem B2335027 : Blo 920579 2335027 := bstep (se 1 (by rfl) ⟨1751270, by rfl⟩ : syracuseStep 2335027 = 3502541) B3502541
theorem B2072897 : Blo 920579 2072897 := bstep (se 2 (by rfl) ⟨777336, by rfl⟩ : syracuseStep 2072897 = 1554673) B1554673
theorem B1384793 : Blo 920579 1384793 := bstep (se 2 (by rfl) ⟨519297, by rfl⟩ : syracuseStep 1384793 = 1038595) B1038595
theorem B2335169 : Blo 920579 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1384907 : Blo 920579 1384907 := bstep (se 1 (by rfl) ⟨1038680, by rfl⟩ : syracuseStep 1384907 = 2077361) B2077361
theorem B1384919 : Blo 920579 1384919 := bstep (se 1 (by rfl) ⟨1038689, by rfl⟩ : syracuseStep 1384919 = 2077379) B2077379
theorem B2073113 : Blo 920579 2073113 := bstep (se 2 (by rfl) ⟨777417, by rfl⟩ : syracuseStep 2073113 = 1554835) B1554835
theorem B1384985 : Blo 920579 1384985 := bstep (se 2 (by rfl) ⟨519369, by rfl⟩ : syracuseStep 1384985 = 1038739) B1038739
theorem B2073203 : Blo 920579 2073203 := bstep (se 1 (by rfl) ⟨1554902, by rfl⟩ : syracuseStep 2073203 = 3109805) B3109805
theorem B1385099 : Blo 920579 1385099 := bstep (se 1 (by rfl) ⟨1038824, by rfl⟩ : syracuseStep 1385099 = 2077649) B2077649
theorem B2073239 : Blo 920579 2073239 := bstep (se 1 (by rfl) ⟨1554929, by rfl⟩ : syracuseStep 2073239 = 3109859) B3109859
theorem B1385111 : Blo 920579 1385111 := bstep (se 1 (by rfl) ⟨1038833, by rfl⟩ : syracuseStep 1385111 = 2077667) B2077667
theorem B2630323 : Blo 920579 2630323 := bstep (se 1 (by rfl) ⟨1972742, by rfl⟩ : syracuseStep 2630323 = 3945485) B3945485
theorem B17703629 : Blo 920579 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B1385177 : Blo 920579 1385177 := bstep (se 2 (by rfl) ⟨519441, by rfl⟩ : syracuseStep 1385177 = 1038883) B1038883
theorem B2073419 : Blo 920579 2073419 := bstep (se 1 (by rfl) ⟨1555064, by rfl⟩ : syracuseStep 2073419 = 3110129) B3110129
theorem B4432715 : Blo 920579 4432715 := bstep (se 1 (by rfl) ⟨3324536, by rfl⟩ : syracuseStep 4432715 = 6649073) B6649073
theorem B1385291 : Blo 920579 1385291 := bstep (se 1 (by rfl) ⟨1038968, by rfl⟩ : syracuseStep 1385291 = 2077937) B2077937
theorem B1385303 : Blo 920579 1385303 := bstep (se 1 (by rfl) ⟨1038977, by rfl⟩ : syracuseStep 1385303 = 2077955) B2077955
theorem B2073473 : Blo 920579 2073473 := bstep (se 2 (by rfl) ⟨777552, by rfl⟩ : syracuseStep 2073473 = 1555105) B1555105
theorem B2630551 : Blo 920579 2630551 := bstep (se 1 (by rfl) ⟨1972913, by rfl⟩ : syracuseStep 2630551 = 3945827) B3945827
theorem B1385369 : Blo 920579 1385369 := bstep (se 2 (by rfl) ⟨519513, by rfl⟩ : syracuseStep 1385369 = 1039027) B1039027
theorem B1385483 : Blo 920579 1385483 := bstep (se 1 (by rfl) ⟨1039112, by rfl⟩ : syracuseStep 1385483 = 2078225) B2078225
theorem B1385495 : Blo 920579 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B2073689 : Blo 920579 2073689 := bstep (se 2 (by rfl) ⟨777633, by rfl⟩ : syracuseStep 2073689 = 1555267) B1555267
theorem B1385561 : Blo 920579 1385561 := bstep (se 2 (by rfl) ⟨519585, by rfl⟩ : syracuseStep 1385561 = 1039171) B1039171
theorem B2073779 : Blo 920579 2073779 := bstep (se 1 (by rfl) ⟨1555334, by rfl⟩ : syracuseStep 2073779 = 3110669) B3110669
theorem B21898421 : Blo 920579 21898421 := bstep (se 5 (by rfl) ⟨1026488, by rfl⟩ : syracuseStep 21898421 = 2052977) B2052977
theorem B1385675 : Blo 920579 1385675 := bstep (se 1 (by rfl) ⟨1039256, by rfl⟩ : syracuseStep 1385675 = 2078513) B2078513
theorem B2073815 : Blo 920579 2073815 := bstep (se 1 (by rfl) ⟨1555361, by rfl⟩ : syracuseStep 2073815 = 3110723) B3110723
theorem B3319001 : Blo 920579 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B1385687 : Blo 920579 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B1385753 : Blo 920579 1385753 := bstep (se 2 (by rfl) ⟨519657, by rfl⟩ : syracuseStep 1385753 = 1039315) B1039315
theorem B2073995 : Blo 920579 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B1385867 : Blo 920579 1385867 := bstep (se 1 (by rfl) ⟨1039400, by rfl⟩ : syracuseStep 1385867 = 2078801) B2078801
theorem B1385879 : Blo 920579 1385879 := bstep (se 1 (by rfl) ⟨1039409, by rfl⟩ : syracuseStep 1385879 = 2078819) B2078819
theorem B2074049 : Blo 920579 2074049 := bstep (se 2 (by rfl) ⟨777768, by rfl⟩ : syracuseStep 2074049 = 1555537) B1555537
theorem B1385945 : Blo 920579 1385945 := bstep (se 2 (by rfl) ⟨519729, by rfl⟩ : syracuseStep 1385945 = 1039459) B1039459
theorem B10528217 : Blo 920579 10528217 := bstep (se 2 (by rfl) ⟨3948081, by rfl⟩ : syracuseStep 10528217 = 7896163) B7896163
theorem B1386059 : Blo 920579 1386059 := bstep (se 1 (by rfl) ⟨1039544, by rfl⟩ : syracuseStep 1386059 = 2079089) B2079089
theorem B1386071 : Blo 920579 1386071 := bstep (se 1 (by rfl) ⟨1039553, by rfl⟩ : syracuseStep 1386071 = 2079107) B2079107
theorem B2074265 : Blo 920579 2074265 := bstep (se 2 (by rfl) ⟨777849, by rfl⟩ : syracuseStep 2074265 = 1555699) B1555699
theorem B1386137 : Blo 920579 1386137 := bstep (se 2 (by rfl) ⟨519801, by rfl⟩ : syracuseStep 1386137 = 1039603) B1039603
theorem B2336435 : Blo 920579 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B2074355 : Blo 920579 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B2107147 : Blo 920579 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B1386251 : Blo 920579 1386251 := bstep (se 1 (by rfl) ⟨1039688, by rfl⟩ : syracuseStep 1386251 = 2079377) B2079377
theorem B2074391 : Blo 920579 2074391 := bstep (se 1 (by rfl) ⟨1555793, by rfl⟩ : syracuseStep 2074391 = 3111587) B3111587
theorem B1386263 : Blo 920579 1386263 := bstep (se 1 (by rfl) ⟨1039697, by rfl⟩ : syracuseStep 1386263 = 2079395) B2079395
theorem B1386329 : Blo 920579 1386329 := bstep (se 2 (by rfl) ⟨519873, by rfl⟩ : syracuseStep 1386329 = 1039747) B1039747
theorem B2074571 : Blo 920579 2074571 := bstep (se 1 (by rfl) ⟨1555928, by rfl⟩ : syracuseStep 2074571 = 3111857) B3111857
theorem B1386443 : Blo 920579 1386443 := bstep (se 1 (by rfl) ⟨1039832, by rfl⟩ : syracuseStep 1386443 = 2079665) B2079665
theorem B1386455 : Blo 920579 1386455 := bstep (se 1 (by rfl) ⟨1039841, by rfl⟩ : syracuseStep 1386455 = 2079683) B2079683
theorem B2074625 : Blo 920579 2074625 := bstep (se 2 (by rfl) ⟨777984, by rfl⟩ : syracuseStep 2074625 = 1555969) B1555969
theorem B1386521 : Blo 920579 1386521 := bstep (se 2 (by rfl) ⟨519945, by rfl⟩ : syracuseStep 1386521 = 1039891) B1039891
theorem B1026155 : Blo 920579 1026155 := bstep (se 1 (by rfl) ⟨769616, by rfl⟩ : syracuseStep 1026155 = 1539233) B1539233
theorem B1386635 : Blo 920579 1386635 := bstep (se 1 (by rfl) ⟨1039976, by rfl⟩ : syracuseStep 1386635 = 2079953) B2079953
theorem B1386647 : Blo 920579 1386647 := bstep (se 1 (by rfl) ⟨1039985, by rfl⟩ : syracuseStep 1386647 = 2079971) B2079971
theorem B2336971 : Blo 920579 2336971 := bstep (se 1 (by rfl) ⟨1752728, by rfl⟩ : syracuseStep 2336971 = 3505457) B3505457
theorem B2074841 : Blo 920579 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B1386713 : Blo 920579 1386713 := bstep (se 2 (by rfl) ⟨520017, by rfl⟩ : syracuseStep 1386713 = 1040035) B1040035
theorem B2074931 : Blo 920579 2074931 := bstep (se 1 (by rfl) ⟨1556198, by rfl⟩ : syracuseStep 2074931 = 3112397) B3112397
theorem B1386827 : Blo 920579 1386827 := bstep (se 1 (by rfl) ⟨1040120, by rfl⟩ : syracuseStep 1386827 = 2080241) B2080241
theorem B2074967 : Blo 920579 2074967 := bstep (se 1 (by rfl) ⟨1556225, by rfl⟩ : syracuseStep 2074967 = 3112451) B3112451
theorem B1386839 : Blo 920579 1386839 := bstep (se 1 (by rfl) ⟨1040129, by rfl⟩ : syracuseStep 1386839 = 2080259) B2080259
theorem B2337113 : Blo 920579 2337113 := bstep (se 2 (by rfl) ⟨876417, by rfl⟩ : syracuseStep 2337113 = 1752835) B1752835
theorem B7481693 : Blo 920579 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B2075147 : Blo 920579 2075147 := bstep (se 1 (by rfl) ⟨1556360, by rfl⟩ : syracuseStep 2075147 = 3112721) B3112721
theorem B2075201 : Blo 920579 2075201 := bstep (se 2 (by rfl) ⟨778200, by rfl⟩ : syracuseStep 2075201 = 1556401) B1556401
theorem B7875251 : Blo 920579 7875251 := bstep (se 1 (by rfl) ⟨5906438, by rfl⟩ : syracuseStep 7875251 = 11812877) B11812877
theorem B2632409 : Blo 920579 2632409 := bstep (se 2 (by rfl) ⟨987153, by rfl⟩ : syracuseStep 2632409 = 1974307) B1974307
theorem B1682201 : Blo 920579 1682201 := bstep (se 2 (by rfl) ⟨630825, by rfl⟩ : syracuseStep 1682201 = 1261651) B1261651
theorem B2075417 : Blo 920579 2075417 := bstep (se 2 (by rfl) ⟨778281, by rfl⟩ : syracuseStep 2075417 = 1556563) B1556563
theorem B2075507 : Blo 920579 2075507 := bstep (se 1 (by rfl) ⟨1556630, by rfl⟩ : syracuseStep 2075507 = 3113261) B3113261
theorem B2075543 : Blo 920579 2075543 := bstep (se 1 (by rfl) ⟨1556657, by rfl⟩ : syracuseStep 2075543 = 3113315) B3113315
theorem B7875629 : Blo 920579 7875629 := bstep (se 3 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 7875629 = 2953361) B2953361
theorem B2075723 : Blo 920579 2075723 := bstep (se 1 (by rfl) ⟨1556792, by rfl⟩ : syracuseStep 2075723 = 3113585) B3113585
theorem B9743435 : Blo 920579 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B2075777 : Blo 920579 2075777 := bstep (se 2 (by rfl) ⟨778416, by rfl⟩ : syracuseStep 2075777 = 1556833) B1556833
theorem B2337943 : Blo 920579 2337943 := bstep (se 1 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 2337943 = 3506915) B3506915
theorem B6991109 : Blo 920579 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B2075993 : Blo 920579 2075993 := bstep (se 2 (by rfl) ⟨778497, by rfl⟩ : syracuseStep 2075993 = 1556995) B1556995
theorem B2076083 : Blo 920579 2076083 := bstep (se 1 (by rfl) ⟨1557062, by rfl⟩ : syracuseStep 2076083 = 3114125) B3114125
theorem B2076119 : Blo 920579 2076119 := bstep (se 1 (by rfl) ⟨1557089, by rfl⟩ : syracuseStep 2076119 = 3114179) B3114179
theorem B3943981 : Blo 920579 3943981 := bstep (se 3 (by rfl) ⟨739496, by rfl⟩ : syracuseStep 3943981 = 1478993) B1478993
theorem B2338379 : Blo 920579 2338379 := bstep (se 1 (by rfl) ⟨1753784, by rfl⟩ : syracuseStep 2338379 = 3507569) B3507569
theorem B1748567 : Blo 920579 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B2076299 : Blo 920579 2076299 := bstep (se 1 (by rfl) ⟨1557224, by rfl⟩ : syracuseStep 2076299 = 3114449) B3114449
theorem B2076353 : Blo 920579 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B3944153 : Blo 920579 3944153 := bstep (se 2 (by rfl) ⟨1479057, by rfl⟩ : syracuseStep 3944153 = 2958115) B2958115
theorem B2666201 : Blo 920579 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B3321623 : Blo 920579 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B2076569 : Blo 920579 2076569 := bstep (se 2 (by rfl) ⟨778713, by rfl⟩ : syracuseStep 2076569 = 1557427) B1557427
theorem B2338753 : Blo 920579 2338753 := bstep (se 2 (by rfl) ⟨877032, by rfl⟩ : syracuseStep 2338753 = 1754065) B1754065
theorem B2076659 : Blo 920579 2076659 := bstep (se 1 (by rfl) ⟨1557494, by rfl⟩ : syracuseStep 2076659 = 3114989) B3114989
theorem B2076695 : Blo 920579 2076695 := bstep (se 1 (by rfl) ⟨1557521, by rfl⟩ : syracuseStep 2076695 = 3115043) B3115043
theorem B4665437 : Blo 920579 4665437 := bstep (se 3 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 4665437 = 1749539) B1749539
theorem B1749107 : Blo 920579 1749107 := bstep (se 1 (by rfl) ⟨1311830, by rfl⟩ : syracuseStep 1749107 = 2623661) B2623661
theorem B8859779 : Blo 920579 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B2076875 : Blo 920579 2076875 := bstep (se 1 (by rfl) ⟨1557656, by rfl⟩ : syracuseStep 2076875 = 3115313) B3115313
theorem B2076929 : Blo 920579 2076929 := bstep (se 2 (by rfl) ⟨778848, by rfl⟩ : syracuseStep 2076929 = 1557697) B1557697
theorem B2077145 : Blo 920579 2077145 := bstep (se 2 (by rfl) ⟨778929, by rfl⟩ : syracuseStep 2077145 = 1557859) B1557859
theorem B2339351 : Blo 920579 2339351 := bstep (se 1 (by rfl) ⟨1754513, by rfl⟩ : syracuseStep 2339351 = 3509027) B3509027
theorem B5255725 : Blo 920579 5255725 := bstep (se 3 (by rfl) ⟨985448, by rfl⟩ : syracuseStep 5255725 = 1970897) B1970897
theorem B2077235 : Blo 920579 2077235 := bstep (se 1 (by rfl) ⟨1557926, by rfl⟩ : syracuseStep 2077235 = 3115853) B3115853
theorem B14955083 : Blo 920579 14955083 := bstep (se 1 (by rfl) ⟨11216312, by rfl⟩ : syracuseStep 14955083 = 22432625) B22432625
theorem B2077271 : Blo 920579 2077271 := bstep (se 1 (by rfl) ⟨1557953, by rfl⟩ : syracuseStep 2077271 = 3115907) B3115907
theorem B1749593 : Blo 920579 1749593 := bstep (se 2 (by rfl) ⟨656097, by rfl⟩ : syracuseStep 1749593 = 1312195) B1312195
theorem B2077451 : Blo 920579 2077451 := bstep (se 1 (by rfl) ⟨1558088, by rfl⟩ : syracuseStep 2077451 = 3116177) B3116177
theorem B2077505 : Blo 920579 2077505 := bstep (se 2 (by rfl) ⟨779064, by rfl⟩ : syracuseStep 2077505 = 1558129) B1558129
theorem B2077721 : Blo 920579 2077721 := bstep (se 2 (by rfl) ⟨779145, by rfl⟩ : syracuseStep 2077721 = 1558291) B1558291
theorem B2077811 : Blo 920579 2077811 := bstep (se 1 (by rfl) ⟨1558358, by rfl⟩ : syracuseStep 2077811 = 3116717) B3116717
theorem B2077847 : Blo 920579 2077847 := bstep (se 1 (by rfl) ⟨1558385, by rfl⟩ : syracuseStep 2077847 = 3116771) B3116771
theorem B3945793 : Blo 920579 3945793 := bstep (se 2 (by rfl) ⟨1479672, by rfl⟩ : syracuseStep 3945793 = 2959345) B2959345
theorem B2340161 : Blo 920579 2340161 := bstep (se 2 (by rfl) ⟨877560, by rfl⟩ : syracuseStep 2340161 = 1755121) B1755121
theorem B2078027 : Blo 920579 2078027 := bstep (se 1 (by rfl) ⟨1558520, by rfl⟩ : syracuseStep 2078027 = 3117041) B3117041
theorem B7091549 : Blo 920579 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B2078081 : Blo 920579 2078081 := bstep (se 2 (by rfl) ⟨779280, by rfl⟩ : syracuseStep 2078081 = 1558561) B1558561
theorem B5912129 : Blo 920579 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B2078297 : Blo 920579 2078297 := bstep (se 2 (by rfl) ⟨779361, by rfl⟩ : syracuseStep 2078297 = 1558723) B1558723
theorem B6993539 : Blo 920579 6993539 := bstep (se 1 (by rfl) ⟨5245154, by rfl⟩ : syracuseStep 6993539 = 10490309) B10490309
theorem B1554059 : Blo 920579 1554059 := bstep (se 1 (by rfl) ⟨1165544, by rfl⟩ : syracuseStep 1554059 = 2331089) B2331089
theorem B2078387 : Blo 920579 2078387 := bstep (se 1 (by rfl) ⟨1558790, by rfl⟩ : syracuseStep 2078387 = 3117581) B3117581
theorem B2078423 : Blo 920579 2078423 := bstep (se 1 (by rfl) ⟨1558817, by rfl⟩ : syracuseStep 2078423 = 3117635) B3117635
theorem B5912281 : Blo 920579 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B1554187 : Blo 920579 1554187 := bstep (se 1 (by rfl) ⟨1165640, by rfl⟩ : syracuseStep 1554187 = 2331281) B2331281
theorem B16824181 : Blo 920579 16824181 := bstep (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) B1577267
theorem B2078603 : Blo 920579 2078603 := bstep (se 1 (by rfl) ⟨1558952, by rfl⟩ : syracuseStep 2078603 = 3117905) B3117905
theorem B1554329 : Blo 920579 1554329 := bstep (se 2 (by rfl) ⟨582873, by rfl⟩ : syracuseStep 1554329 = 1165747) B1165747
theorem B2078657 : Blo 920579 2078657 := bstep (se 2 (by rfl) ⟨779496, by rfl⟩ : syracuseStep 2078657 = 1558993) B1558993
theorem B1751051 : Blo 920579 1751051 := bstep (se 1 (by rfl) ⟨1313288, by rfl⟩ : syracuseStep 1751051 = 2626577) B2626577
theorem B1554457 : Blo 920579 1554457 := bstep (se 2 (by rfl) ⟨582921, by rfl⟩ : syracuseStep 1554457 = 1165843) B1165843
theorem B5617795 : Blo 920579 5617795 := bstep (se 1 (by rfl) ⟨4213346, by rfl⟩ : syracuseStep 5617795 = 8426693) B8426693
theorem B4667543 : Blo 920579 4667543 := bstep (se 1 (by rfl) ⟨3500657, by rfl⟩ : syracuseStep 4667543 = 7001315) B7001315
theorem B2078873 : Blo 920579 2078873 := bstep (se 2 (by rfl) ⟨779577, by rfl⟩ : syracuseStep 2078873 = 1559155) B1559155
theorem B1751233 : Blo 920579 1751233 := bstep (se 2 (by rfl) ⟨656712, by rfl⟩ : syracuseStep 1751233 = 1313425) B1313425
theorem B2078963 : Blo 920579 2078963 := bstep (se 1 (by rfl) ⟨1559222, by rfl⟩ : syracuseStep 2078963 = 3118445) B3118445
theorem B2078999 : Blo 920579 2078999 := bstep (se 1 (by rfl) ⟨1559249, by rfl⟩ : syracuseStep 2078999 = 3118499) B3118499
theorem B2079179 : Blo 920579 2079179 := bstep (se 1 (by rfl) ⟨1559384, by rfl⟩ : syracuseStep 2079179 = 3118769) B3118769
theorem B3324377 : Blo 920579 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B2079233 : Blo 920579 2079233 := bstep (se 2 (by rfl) ⟨779712, by rfl⟩ : syracuseStep 2079233 = 1559425) B1559425
theorem B1555031 : Blo 920579 1555031 := bstep (se 1 (by rfl) ⟨1166273, by rfl⟩ : syracuseStep 1555031 = 2332547) B2332547
theorem B1751681 : Blo 920579 1751681 := bstep (se 2 (by rfl) ⟨656880, by rfl⟩ : syracuseStep 1751681 = 1313761) B1313761
theorem B1555159 : Blo 920579 1555159 := bstep (se 1 (by rfl) ⟨1166369, by rfl⟩ : syracuseStep 1555159 = 2332739) B2332739
theorem B2079449 : Blo 920579 2079449 := bstep (se 2 (by rfl) ⟨779793, by rfl⟩ : syracuseStep 2079449 = 1559587) B1559587
theorem B2079539 : Blo 920579 2079539 := bstep (se 1 (by rfl) ⟨1559654, by rfl⟩ : syracuseStep 2079539 = 3119309) B3119309
theorem B2079575 : Blo 920579 2079575 := bstep (se 1 (by rfl) ⟨1559681, by rfl⟩ : syracuseStep 2079575 = 3119363) B3119363
theorem B3947467 : Blo 920579 3947467 := bstep (se 1 (by rfl) ⟨2960600, by rfl⟩ : syracuseStep 3947467 = 5921201) B5921201
theorem B1752023 : Blo 920579 1752023 := bstep (se 1 (by rfl) ⟨1314017, by rfl⟩ : syracuseStep 1752023 = 2628035) B2628035
theorem B2079755 : Blo 920579 2079755 := bstep (se 1 (by rfl) ⟨1559816, by rfl⟩ : syracuseStep 2079755 = 3119633) B3119633
theorem B2079809 : Blo 920579 2079809 := bstep (se 2 (by rfl) ⟨779928, by rfl⟩ : syracuseStep 2079809 = 1559857) B1559857
theorem B3947741 : Blo 920579 3947741 := bstep (se 3 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 3947741 = 1480403) B1480403
theorem B2080025 : Blo 920579 2080025 := bstep (se 2 (by rfl) ⟨780009, by rfl⟩ : syracuseStep 2080025 = 1560019) B1560019
theorem B1555787 : Blo 920579 1555787 := bstep (se 1 (by rfl) ⟨1166840, by rfl⟩ : syracuseStep 1555787 = 2333681) B2333681
theorem B2080115 : Blo 920579 2080115 := bstep (se 1 (by rfl) ⟨1560086, by rfl⟩ : syracuseStep 2080115 = 3120173) B3120173
theorem B3554705 : Blo 920579 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B2080151 : Blo 920579 2080151 := bstep (se 1 (by rfl) ⟨1560113, by rfl⟩ : syracuseStep 2080151 = 3120227) B3120227
theorem B1555915 : Blo 920579 1555915 := bstep (se 1 (by rfl) ⟨1166936, by rfl⟩ : syracuseStep 1555915 = 2333873) B2333873
theorem B1556057 : Blo 920579 1556057 := bstep (se 2 (by rfl) ⟨583521, by rfl⟩ : syracuseStep 1556057 = 1167043) B1167043
theorem B6307429 : Blo 920579 6307429 := bstep (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) B1182643
theorem B1752691 : Blo 920579 1752691 := bstep (se 1 (by rfl) ⟨1314518, by rfl⟩ : syracuseStep 1752691 = 2629037) B2629037
theorem B4439731 : Blo 920579 4439731 := bstep (se 1 (by rfl) ⟨3329798, by rfl⟩ : syracuseStep 4439731 = 6659597) B6659597
theorem B1556185 : Blo 920579 1556185 := bstep (se 2 (by rfl) ⟨583569, by rfl⟩ : syracuseStep 1556185 = 1167139) B1167139
theorem B933655 : Blo 920579 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B1753139 : Blo 920579 1753139 := bstep (se 1 (by rfl) ⟨1314854, by rfl⟩ : syracuseStep 1753139 = 2629709) B2629709
theorem B1753177 : Blo 920579 1753177 := bstep (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) B1314883
theorem B1556759 : Blo 920579 1556759 := bstep (se 1 (by rfl) ⟨1167569, by rfl⟩ : syracuseStep 1556759 = 2335139) B2335139
theorem B2212147 : Blo 920579 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B1556887 : Blo 920579 1556887 := bstep (se 1 (by rfl) ⟨1167665, by rfl⟩ : syracuseStep 1556887 = 2335331) B2335331
theorem B7487921 : Blo 920579 7487921 := bstep (se 2 (by rfl) ⟨2807970, by rfl⟩ : syracuseStep 7487921 = 5615941) B5615941
theorem B1753625 : Blo 920579 1753625 := bstep (se 2 (by rfl) ⟨657609, by rfl⟩ : syracuseStep 1753625 = 1315219) B1315219
theorem B934507 : Blo 920579 934507 := bstep (se 1 (by rfl) ⟨700880, by rfl⟩ : syracuseStep 934507 = 1401761) B1401761
theorem B14959235 : Blo 920579 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B4735705 : Blo 920579 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B3556057 : Blo 920579 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B9487169 : Blo 920579 9487169 := bstep (se 2 (by rfl) ⟨3557688, by rfl⟩ : syracuseStep 9487169 = 7115377) B7115377
theorem B2802521 : Blo 920579 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B6996941 : Blo 920579 6996941 := bstep (se 3 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 6996941 = 2623853) B2623853
theorem B1557515 : Blo 920579 1557515 := bstep (se 1 (by rfl) ⟨1168136, by rfl⟩ : syracuseStep 1557515 = 2336273) B2336273
theorem B1557643 : Blo 920579 1557643 := bstep (se 1 (by rfl) ⟨1168232, by rfl⟩ : syracuseStep 1557643 = 2336465) B2336465
theorem B6636761 : Blo 920579 6636761 := bstep (se 2 (by rfl) ⟨2488785, by rfl⟩ : syracuseStep 6636761 = 4977571) B4977571
theorem B935147 : Blo 920579 935147 := bstep (se 1 (by rfl) ⟨701360, by rfl⟩ : syracuseStep 935147 = 1402721) B1402721
theorem B1754369 : Blo 920579 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B1557785 : Blo 920579 1557785 := bstep (se 2 (by rfl) ⟨584169, by rfl⟩ : syracuseStep 1557785 = 1168339) B1168339
theorem B2213185 : Blo 920579 2213185 := bstep (se 2 (by rfl) ⟨829944, by rfl⟩ : syracuseStep 2213185 = 1659889) B1659889
theorem B1557913 : Blo 920579 1557913 := bstep (se 2 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 1557913 = 1168435) B1168435
theorem B6997427 : Blo 920579 6997427 := bstep (se 1 (by rfl) ⟨5248070, by rfl⟩ : syracuseStep 6997427 = 10496141) B10496141
theorem B935383 : Blo 920579 935383 := bstep (se 1 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 935383 = 1403075) B1403075
theorem B1754635 : Blo 920579 1754635 := bstep (se 1 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 1754635 = 2631953) B2631953
theorem B4671107 : Blo 920579 4671107 := bstep (se 1 (by rfl) ⟨3503330, by rfl⟩ : syracuseStep 4671107 = 7006661) B7006661
theorem B2213569 : Blo 920579 2213569 := bstep (se 2 (by rfl) ⟨830088, by rfl⟩ : syracuseStep 2213569 = 1660177) B1660177
theorem B1165195 : Blo 920579 1165195 := bstep (se 1 (by rfl) ⟨873896, by rfl⟩ : syracuseStep 1165195 = 1747793) B1747793
theorem B1755083 : Blo 920579 1755083 := bstep (se 1 (by rfl) ⟨1316312, by rfl⟩ : syracuseStep 1755083 = 2632625) B2632625
theorem B1558487 : Blo 920579 1558487 := bstep (se 1 (by rfl) ⟨1168865, by rfl⟩ : syracuseStep 1558487 = 2337731) B2337731
theorem B1558615 : Blo 920579 1558615 := bstep (se 1 (by rfl) ⟨1168961, by rfl⟩ : syracuseStep 1558615 = 2337923) B2337923
theorem B936247 : Blo 920579 936247 := bstep (se 1 (by rfl) ⟨702185, by rfl⟩ : syracuseStep 936247 = 1404371) B1404371
theorem B11225461 : Blo 920579 11225461 := bstep (se 5 (by rfl) ⟨526193, by rfl⟩ : syracuseStep 11225461 = 1052387) B1052387
theorem B7489997 : Blo 920579 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B1559243 : Blo 920579 1559243 := bstep (se 1 (by rfl) ⟨1169432, by rfl⟩ : syracuseStep 1559243 = 2338865) B2338865
theorem B1559371 : Blo 920579 1559371 := bstep (se 1 (by rfl) ⟨1169528, by rfl⟩ : syracuseStep 1559371 = 2339057) B2339057
theorem B1166167 : Blo 920579 1166167 := bstep (se 1 (by rfl) ⟨874625, by rfl⟩ : syracuseStep 1166167 = 1749251) B1749251
theorem B6998885 : Blo 920579 6998885 := bstep (se 4 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 6998885 = 1312291) B1312291
theorem B1559513 : Blo 920579 1559513 := bstep (se 2 (by rfl) ⟨584817, by rfl⟩ : syracuseStep 1559513 = 1169635) B1169635
theorem B1559641 : Blo 920579 1559641 := bstep (se 2 (by rfl) ⟨584865, by rfl⟩ : syracuseStep 1559641 = 1169731) B1169731
theorem B5262515 : Blo 920579 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B7097645 : Blo 920579 7097645 := bstep (se 3 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 7097645 = 2661617) B2661617
theorem B6999371 : Blo 920579 6999371 := bstep (se 1 (by rfl) ⟨5249528, by rfl⟩ : syracuseStep 6999371 = 10499057) B10499057
theorem B1035787 : Blo 920579 1035787 := bstep (se 1 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 1035787 = 1553681) B1553681
theorem B1035895 : Blo 920579 1035895 := bstep (se 1 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 1035895 = 1553843) B1553843
theorem B1166987 : Blo 920579 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B1560215 : Blo 920579 1560215 := bstep (se 1 (by rfl) ⟨1170161, by rfl⟩ : syracuseStep 1560215 = 2340323) B2340323
theorem B3329753 : Blo 920579 3329753 := bstep (se 2 (by rfl) ⟨1248657, by rfl⟩ : syracuseStep 3329753 = 2497315) B2497315
theorem B1036075 : Blo 920579 1036075 := bstep (se 1 (by rfl) ⟨777056, by rfl⟩ : syracuseStep 1036075 = 1554113) B1554113
theorem B1036183 : Blo 920579 1036183 := bstep (se 1 (by rfl) ⟨777137, by rfl⟩ : syracuseStep 1036183 = 1554275) B1554275
theorem B5918615 : Blo 920579 5918615 := bstep (se 1 (by rfl) ⟨4438961, by rfl⟩ : syracuseStep 5918615 = 8877923) B8877923
theorem B13455395 : Blo 920579 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B1495115 : Blo 920579 1495115 := bstep (se 1 (by rfl) ⟨1121336, by rfl⟩ : syracuseStep 1495115 = 2242673) B2242673
theorem B1036363 : Blo 920579 1036363 := bstep (se 1 (by rfl) ⟨777272, by rfl⟩ : syracuseStep 1036363 = 1554545) B1554545
theorem B1036471 : Blo 920579 1036471 := bstep (se 1 (by rfl) ⟨777353, by rfl⟩ : syracuseStep 1036471 = 1554707) B1554707
theorem B1167691 : Blo 920579 1167691 := bstep (se 1 (by rfl) ⟨875768, by rfl⟩ : syracuseStep 1167691 = 1751537) B1751537
theorem B1036651 : Blo 920579 1036651 := bstep (se 1 (by rfl) ⟨777488, by rfl⟩ : syracuseStep 1036651 = 1554977) B1554977
theorem B1036759 : Blo 920579 1036759 := bstep (se 1 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 1036759 = 1555139) B1555139
theorem B1659457 : Blo 920579 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B1167959 : Blo 920579 1167959 := bstep (se 1 (by rfl) ⟨875969, by rfl⟩ : syracuseStep 1167959 = 1751939) B1751939
theorem B5263973 : Blo 920579 5263973 := bstep (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) B986995
theorem B1036939 : Blo 920579 1036939 := bstep (se 1 (by rfl) ⟨777704, by rfl⟩ : syracuseStep 1036939 = 1555409) B1555409
theorem B1037047 : Blo 920579 1037047 := bstep (se 1 (by rfl) ⟨777785, by rfl⟩ : syracuseStep 1037047 = 1555571) B1555571
theorem B3986327 : Blo 920579 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B1037227 : Blo 920579 1037227 := bstep (se 1 (by rfl) ⟨777920, by rfl⟩ : syracuseStep 1037227 = 1555841) B1555841
theorem B11818001 : Blo 920579 11818001 := bstep (se 2 (by rfl) ⟨4431750, by rfl⟩ : syracuseStep 11818001 = 8863501) B8863501
theorem B1037335 : Blo 920579 1037335 := bstep (se 1 (by rfl) ⟨778001, by rfl⟩ : syracuseStep 1037335 = 1556003) B1556003
theorem B1037515 : Blo 920579 1037515 := bstep (se 1 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 1037515 = 1556273) B1556273
theorem B4674833 : Blo 920579 4674833 := bstep (se 2 (by rfl) ⟨1753062, by rfl⟩ : syracuseStep 4674833 = 3506125) B3506125
theorem B1168663 : Blo 920579 1168663 := bstep (se 1 (by rfl) ⟨876497, by rfl⟩ : syracuseStep 1168663 = 1752995) B1752995
theorem B1037623 : Blo 920579 1037623 := bstep (se 1 (by rfl) ⟨778217, by rfl⟩ : syracuseStep 1037623 = 1556435) B1556435
theorem B4674995 : Blo 920579 4674995 := bstep (se 1 (by rfl) ⟨3506246, by rfl⟩ : syracuseStep 4674995 = 7012493) B7012493
theorem B1037803 : Blo 920579 1037803 := bstep (se 1 (by rfl) ⟨778352, by rfl⟩ : syracuseStep 1037803 = 1556705) B1556705
theorem B12605003 : Blo 920579 12605003 := bstep (se 1 (by rfl) ⟨9453752, by rfl⟩ : syracuseStep 12605003 = 18907505) B18907505
theorem B1037911 : Blo 920579 1037911 := bstep (se 1 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 1037911 = 1556867) B1556867
theorem B1038091 : Blo 920579 1038091 := bstep (se 1 (by rfl) ⟨778568, by rfl⟩ : syracuseStep 1038091 = 1557137) B1557137
theorem B4216627 : Blo 920579 4216627 := bstep (se 1 (by rfl) ⟨3162470, by rfl⟩ : syracuseStep 4216627 = 6324941) B6324941
theorem B1038199 : Blo 920579 1038199 := bstep (se 1 (by rfl) ⟨778649, by rfl⟩ : syracuseStep 1038199 = 1557299) B1557299
theorem B1038379 : Blo 920579 1038379 := bstep (se 1 (by rfl) ⟨778784, by rfl⟩ : syracuseStep 1038379 = 1557569) B1557569
theorem B1038487 : Blo 920579 1038487 := bstep (se 1 (by rfl) ⟨778865, by rfl⟩ : syracuseStep 1038487 = 1557731) B1557731
theorem B1038667 : Blo 920579 1038667 := bstep (se 1 (by rfl) ⟨779000, by rfl⟩ : syracuseStep 1038667 = 1558001) B1558001
theorem B5921099 : Blo 920579 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B5757335 : Blo 920579 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B1038775 : Blo 920579 1038775 := bstep (se 1 (by rfl) ⟨779081, by rfl⟩ : syracuseStep 1038775 = 1558163) B1558163
theorem B7494149 : Blo 920579 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B17717777 : Blo 920579 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B1038955 : Blo 920579 1038955 := bstep (se 1 (by rfl) ⟨779216, by rfl⟩ : syracuseStep 1038955 = 1558433) B1558433
theorem B1039063 : Blo 920579 1039063 := bstep (se 1 (by rfl) ⟨779297, by rfl⟩ : syracuseStep 1039063 = 1558595) B1558595
theorem B1039243 : Blo 920579 1039243 := bstep (se 1 (by rfl) ⟨779432, by rfl⟩ : syracuseStep 1039243 = 1558865) B1558865
theorem B3496877 : Blo 920579 3496877 := bstep (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) B1311329
theorem B1039351 : Blo 920579 1039351 := bstep (se 1 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 1039351 = 1559027) B1559027
theorem B1039531 : Blo 920579 1039531 := bstep (se 1 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 1039531 = 1559297) B1559297
theorem B1039639 : Blo 920579 1039639 := bstep (se 1 (by rfl) ⟨779729, by rfl⟩ : syracuseStep 1039639 = 1559459) B1559459
theorem B4676939 : Blo 920579 4676939 := bstep (se 1 (by rfl) ⟨3507704, by rfl⟩ : syracuseStep 4676939 = 7015409) B7015409
theorem B1039819 : Blo 920579 1039819 := bstep (se 1 (by rfl) ⟨779864, by rfl⟩ : syracuseStep 1039819 = 1559729) B1559729
theorem B1039927 : Blo 920579 1039927 := bstep (se 1 (by rfl) ⟨779945, by rfl⟩ : syracuseStep 1039927 = 1559891) B1559891
theorem B3497651 : Blo 920579 3497651 := bstep (se 1 (by rfl) ⟨2623238, by rfl⟩ : syracuseStep 3497651 = 5246477) B5246477
theorem B1040107 : Blo 920579 1040107 := bstep (se 1 (by rfl) ⟨780080, by rfl⟩ : syracuseStep 1040107 = 1560161) B1560161
theorem B7495517 : Blo 920579 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B11820977 : Blo 920579 11820977 := bstep (se 2 (by rfl) ⟨4432866, by rfl⟩ : syracuseStep 11820977 = 8865733) B8865733
theorem B35938829 : Blo 920579 35938829 := bstep (se 3 (by rfl) ⟨6738530, by rfl⟩ : syracuseStep 35938829 = 13477061) B13477061
theorem B7004717 : Blo 920579 7004717 := bstep (se 3 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 7004717 = 2626769) B2626769
theorem B1663897 : Blo 920579 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B5923763 : Blo 920579 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B4678721 : Blo 920579 4678721 := bstep (se 2 (by rfl) ⟨1754520, by rfl⟩ : syracuseStep 4678721 = 3509041) B3509041
theorem B1401943 : Blo 920579 1401943 := bstep (se 1 (by rfl) ⟨1051457, by rfl⟩ : syracuseStep 1401943 = 2102915) B2102915
theorem B3499139 : Blo 920579 3499139 := bstep (se 1 (by rfl) ⟨2624354, by rfl⟩ : syracuseStep 3499139 = 5248709) B5248709
theorem B3499595 : Blo 920579 3499595 := bstep (se 1 (by rfl) ⟨2624696, by rfl⟩ : syracuseStep 3499595 = 5249393) B5249393
theorem B3499793 : Blo 920579 3499793 := bstep (se 2 (by rfl) ⟨1312422, by rfl⟩ : syracuseStep 3499793 = 2624845) B2624845
theorem B12642227 : Blo 920579 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B3598273 : Blo 920579 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B54716485 : Blo 920579 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B3991697 : Blo 920579 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B3500567 : Blo 920579 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B3500765 : Blo 920579 3500765 := bstep (se 3 (by rfl) ⟨656393, by rfl⟩ : syracuseStep 3500765 = 1312787) B1312787
theorem B4680665 : Blo 920579 4680665 := bstep (se 2 (by rfl) ⟨1755249, by rfl⟩ : syracuseStep 4680665 = 3510499) B3510499
theorem B3107915 : Blo 920579 3107915 := bstep (se 1 (by rfl) ⟨2330936, by rfl⟩ : syracuseStep 3107915 = 4661873) B4661873
theorem B3108185 : Blo 920579 3108185 := bstep (se 2 (by rfl) ⟨1165569, by rfl⟩ : syracuseStep 3108185 = 2331139) B2331139
theorem B6745805 : Blo 920579 6745805 := bstep (se 3 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 6745805 = 2529677) B2529677
theorem B1404631 : Blo 920579 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B1109783 : Blo 920579 1109783 := bstep (se 1 (by rfl) ⟨832337, by rfl⟩ : syracuseStep 1109783 = 1664675) B1664675
theorem B1109899 : Blo 920579 1109899 := bstep (se 1 (by rfl) ⟨832424, by rfl⟩ : syracuseStep 1109899 = 1664849) B1664849
theorem B3108887 : Blo 920579 3108887 := bstep (se 1 (by rfl) ⟨2331665, by rfl⟩ : syracuseStep 3108887 = 4663331) B4663331
theorem B1110091 : Blo 920579 1110091 := bstep (se 1 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 1110091 = 1665137) B1665137
theorem B7008605 : Blo 920579 7008605 := bstep (se 3 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 7008605 = 2628227) B2628227
theorem B33616241 : Blo 920579 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B1110475 : Blo 920579 1110475 := bstep (se 1 (by rfl) ⟨832856, by rfl⟩ : syracuseStep 1110475 = 1665713) B1665713
theorem B8417753 : Blo 920579 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B3109427 : Blo 920579 3109427 := bstep (se 1 (by rfl) ⟨2332070, by rfl⟩ : syracuseStep 3109427 = 4664141) B4664141
theorem B3502723 : Blo 920579 3502723 := bstep (se 1 (by rfl) ⟨2627042, by rfl⟩ : syracuseStep 3502723 = 5254085) B5254085
theorem B10515095 : Blo 920579 10515095 := bstep (se 1 (by rfl) ⟨7886321, by rfl⟩ : syracuseStep 10515095 = 15772643) B15772643
theorem B7598771 : Blo 920579 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B3109697 : Blo 920579 3109697 := bstep (se 2 (by rfl) ⟨1166136, by rfl⟩ : syracuseStep 3109697 = 2332273) B2332273
theorem B3503027 : Blo 920579 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B11990051 : Blo 920579 11990051 := bstep (se 1 (by rfl) ⟨8992538, by rfl⟩ : syracuseStep 11990051 = 17985077) B17985077
theorem B3732659 : Blo 920579 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B3110237 : Blo 920579 3110237 := bstep (se 3 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 3110237 = 1166339) B1166339
theorem B3503681 : Blo 920579 3503681 := bstep (se 2 (by rfl) ⟨1313880, by rfl⟩ : syracuseStep 3503681 = 2627761) B2627761
theorem B3799057 : Blo 920579 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B3733697 : Blo 920579 3733697 := bstep (se 2 (by rfl) ⟨1400136, by rfl⟩ : syracuseStep 3733697 = 2800273) B2800273
theorem B3111371 : Blo 920579 3111371 := bstep (se 1 (by rfl) ⟨2333528, by rfl⟩ : syracuseStep 3111371 = 4667057) B4667057
theorem B2489011 : Blo 920579 2489011 := bstep (se 1 (by rfl) ⟨1866758, by rfl⟩ : syracuseStep 2489011 = 3733517) B3733517
theorem B3111641 : Blo 920579 3111641 := bstep (se 2 (by rfl) ⟨1166865, by rfl⟩ : syracuseStep 3111641 = 2333731) B2333731
theorem B3373841 : Blo 920579 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B3504941 : Blo 920579 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B3504971 : Blo 920579 3504971 := bstep (se 1 (by rfl) ⟨2628728, by rfl⟩ : syracuseStep 3504971 = 5257457) B5257457
theorem B1244441 : Blo 920579 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B3112343 : Blo 920579 3112343 := bstep (se 1 (by rfl) ⟨2334257, by rfl⟩ : syracuseStep 3112343 = 4668515) B4668515
theorem B3505625 : Blo 920579 3505625 := bstep (se 2 (by rfl) ⟨1314609, by rfl⟩ : syracuseStep 3505625 = 2629219) B2629219
theorem B3505943 : Blo 920579 3505943 := bstep (se 1 (by rfl) ⟨2629457, by rfl⟩ : syracuseStep 3505943 = 5258915) B5258915
theorem B3112883 : Blo 920579 3112883 := bstep (se 1 (by rfl) ⟨2334662, by rfl⟩ : syracuseStep 3112883 = 4669325) B4669325
theorem B2621575 : Blo 920579 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B2490515 : Blo 920579 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B2490743 : Blo 920579 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B6390161 : Blo 920579 6390161 := bstep (se 2 (by rfl) ⟨2396310, by rfl⟩ : syracuseStep 6390161 = 4792621) B4792621
theorem B2949529 : Blo 920579 2949529 := bstep (se 2 (by rfl) ⟨1106073, by rfl⟩ : syracuseStep 2949529 = 2212147) B2212147
theorem B3113369 : Blo 920579 3113369 := bstep (se 2 (by rfl) ⟨1167513, by rfl⟩ : syracuseStep 3113369 = 2335027) B2335027
theorem B2621963 : Blo 920579 2621963 := bstep (se 1 (by rfl) ⟨1966472, by rfl⟩ : syracuseStep 2621963 = 3932945) B3932945
theorem B6324779 : Blo 920579 6324779 := bstep (se 1 (by rfl) ⟨4743584, by rfl⟩ : syracuseStep 6324779 = 9487169) B9487169
theorem B1311403 : Blo 920579 1311403 := bstep (se 1 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 1311403 = 1967105) B1967105
theorem B4424507 : Blo 920579 4424507 := bstep (se 1 (by rfl) ⟨3318380, by rfl⟩ : syracuseStep 4424507 = 6636761) B6636761
theorem B3507097 : Blo 920579 3507097 := bstep (se 2 (by rfl) ⟨1315161, by rfl⟩ : syracuseStep 3507097 = 2630323) B2630323
theorem B3114071 : Blo 920579 3114071 := bstep (se 1 (by rfl) ⟨2335553, by rfl⟩ : syracuseStep 3114071 = 4671107) B4671107
theorem B7865545 : Blo 920579 7865545 := bstep (se 2 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 7865545 = 5899159) B5899159
theorem B3507401 : Blo 920579 3507401 := bstep (se 2 (by rfl) ⟨1315275, by rfl⟩ : syracuseStep 3507401 = 2630551) B2630551
theorem B3933593 : Blo 920579 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B1869257 : Blo 920579 1869257 := bstep (se 2 (by rfl) ⟨700971, by rfl⟩ : syracuseStep 1869257 = 1401943) B1401943
theorem B3114557 : Blo 920579 3114557 := bstep (se 3 (by rfl) ⟨583979, by rfl⟩ : syracuseStep 3114557 = 1167959) B1167959
theorem B2950913 : Blo 920579 2950913 := bstep (se 2 (by rfl) ⟨1106592, by rfl⟩ : syracuseStep 2950913 = 2213185) B2213185
theorem B1312519 : Blo 920579 1312519 := bstep (se 1 (by rfl) ⟨984389, by rfl⟩ : syracuseStep 1312519 = 1968779) B1968779
theorem B2623261 : Blo 920579 2623261 := bstep (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) B983723
theorem B35915633 : Blo 920579 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B1247177 : Blo 920579 1247177 := bstep (se 2 (by rfl) ⟨467691, by rfl⟩ : syracuseStep 1247177 = 935383) B935383
theorem B2623603 : Blo 920579 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B3508343 : Blo 920579 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B11798729 : Blo 920579 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B7473389 : Blo 920579 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B2951425 : Blo 920579 2951425 := bstep (se 2 (by rfl) ⟨1106784, by rfl⟩ : syracuseStep 2951425 = 2213569) B2213569
theorem B2492819 : Blo 920579 2492819 := bstep (se 1 (by rfl) ⟨1869614, by rfl⟩ : syracuseStep 2492819 = 3739229) B3739229
theorem B5245337 : Blo 920579 5245337 := bstep (se 2 (by rfl) ⟨1967001, by rfl⟩ : syracuseStep 5245337 = 3934003) B3934003
theorem B1313339 : Blo 920579 1313339 := bstep (se 1 (by rfl) ⟨985004, by rfl⟩ : syracuseStep 1313339 = 1970009) B1970009
theorem B3738383 : Blo 920579 3738383 := bstep (se 1 (by rfl) ⟨2803787, by rfl⟩ : syracuseStep 3738383 = 5607575) B5607575
theorem B13306787 : Blo 920579 13306787 := bstep (se 1 (by rfl) ⟨9980090, by rfl⟩ : syracuseStep 13306787 = 19960181) B19960181
theorem B3115961 : Blo 920579 3115961 := bstep (se 2 (by rfl) ⟨1168485, by rfl⟩ : syracuseStep 3115961 = 2336971) B2336971
theorem B1248247 : Blo 920579 1248247 := bstep (se 1 (by rfl) ⟨936185, by rfl⟩ : syracuseStep 1248247 = 1872371) B1872371
theorem B920583 : Blo 920579 920583 := bstep (se 1 (by rfl) ⟨690437, by rfl⟩ : syracuseStep 920583 = 1380875) B1380875
theorem B920591 : Blo 920579 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B920635 : Blo 920579 920635 := bstep (se 1 (by rfl) ⟨690476, by rfl⟩ : syracuseStep 920635 = 1380953) B1380953
theorem B3509315 : Blo 920579 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B1248329 : Blo 920579 1248329 := bstep (se 2 (by rfl) ⟨468123, by rfl⟩ : syracuseStep 1248329 = 936247) B936247
theorem B920711 : Blo 920579 920711 := bstep (se 1 (by rfl) ⟨690533, by rfl⟩ : syracuseStep 920711 = 1381067) B1381067
theorem B920719 : Blo 920579 920719 := bstep (se 1 (by rfl) ⟨690539, by rfl⟩ : syracuseStep 920719 = 1381079) B1381079
theorem B1313977 : Blo 920579 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B920763 : Blo 920579 920763 := bstep (se 1 (by rfl) ⟨690572, by rfl⟩ : syracuseStep 920763 = 1381145) B1381145
theorem B4984037 : Blo 920579 4984037 := bstep (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) B934507
theorem B920839 : Blo 920579 920839 := bstep (se 1 (by rfl) ⟨690629, by rfl⟩ : syracuseStep 920839 = 1381259) B1381259
theorem B2657551 : Blo 920579 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B920847 : Blo 920579 920847 := bstep (se 1 (by rfl) ⟨690635, by rfl⟩ : syracuseStep 920847 = 1381271) B1381271
theorem B2493725 : Blo 920579 2493725 := bstep (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) B935147
theorem B1314091 : Blo 920579 1314091 := bstep (se 1 (by rfl) ⟨985568, by rfl⟩ : syracuseStep 1314091 = 1971137) B1971137
theorem B920891 : Blo 920579 920891 := bstep (se 1 (by rfl) ⟨690668, by rfl⟩ : syracuseStep 920891 = 1381337) B1381337
theorem B5049715 : Blo 920579 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B920967 : Blo 920579 920967 := bstep (se 1 (by rfl) ⟨690725, by rfl⟩ : syracuseStep 920967 = 1381451) B1381451
theorem B920975 : Blo 920579 920975 := bstep (se 1 (by rfl) ⟨690731, by rfl⟩ : syracuseStep 920975 = 1381463) B1381463
theorem B921019 : Blo 920579 921019 := bstep (se 1 (by rfl) ⟨690764, by rfl⟩ : syracuseStep 921019 = 1381529) B1381529
theorem B921095 : Blo 920579 921095 := bstep (se 1 (by rfl) ⟨690821, by rfl⟩ : syracuseStep 921095 = 1381643) B1381643
theorem B3116555 : Blo 920579 3116555 := bstep (se 1 (by rfl) ⟨2337416, by rfl⟩ : syracuseStep 3116555 = 4674833) B4674833
theorem B921103 : Blo 920579 921103 := bstep (se 1 (by rfl) ⟨690827, by rfl⟩ : syracuseStep 921103 = 1381655) B1381655
theorem B1314319 : Blo 920579 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B2493985 : Blo 920579 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B921147 : Blo 920579 921147 := bstep (se 1 (by rfl) ⟨690860, by rfl⟩ : syracuseStep 921147 = 1381721) B1381721
theorem B13274725 : Blo 920579 13274725 := bstep (se 4 (by rfl) ⟨1244505, by rfl⟩ : syracuseStep 13274725 = 2489011) B2489011
theorem B3116663 : Blo 920579 3116663 := bstep (se 1 (by rfl) ⟨2337497, by rfl⟩ : syracuseStep 3116663 = 4674995) B4674995
theorem B921223 : Blo 920579 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B921231 : Blo 920579 921231 := bstep (se 1 (by rfl) ⟨690923, by rfl⟩ : syracuseStep 921231 = 1381847) B1381847
theorem B921275 : Blo 920579 921275 := bstep (se 1 (by rfl) ⟨690956, by rfl⟩ : syracuseStep 921275 = 1381913) B1381913
theorem B921351 : Blo 920579 921351 := bstep (se 1 (by rfl) ⟨691013, by rfl⟩ : syracuseStep 921351 = 1382027) B1382027
theorem B921359 : Blo 920579 921359 := bstep (se 1 (by rfl) ⟨691019, by rfl⟩ : syracuseStep 921359 = 1382039) B1382039
theorem B921403 : Blo 920579 921403 := bstep (se 1 (by rfl) ⟨691052, by rfl⟩ : syracuseStep 921403 = 1382105) B1382105
theorem B921479 : Blo 920579 921479 := bstep (se 1 (by rfl) ⟨691109, by rfl⟩ : syracuseStep 921479 = 1382219) B1382219
theorem B921487 : Blo 920579 921487 := bstep (se 1 (by rfl) ⟨691115, by rfl⟩ : syracuseStep 921487 = 1382231) B1382231
theorem B921531 : Blo 920579 921531 := bstep (se 1 (by rfl) ⟨691148, by rfl⟩ : syracuseStep 921531 = 1382297) B1382297
theorem B921607 : Blo 920579 921607 := bstep (se 1 (by rfl) ⟨691205, by rfl⟩ : syracuseStep 921607 = 1382411) B1382411
theorem B921615 : Blo 920579 921615 := bstep (se 1 (by rfl) ⟨691211, by rfl⟩ : syracuseStep 921615 = 1382423) B1382423
theorem B2101307 : Blo 920579 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B921659 : Blo 920579 921659 := bstep (se 1 (by rfl) ⟨691244, by rfl⟩ : syracuseStep 921659 = 1382489) B1382489
theorem B3739715 : Blo 920579 3739715 := bstep (se 1 (by rfl) ⟨2804786, by rfl⟩ : syracuseStep 3739715 = 5609573) B5609573
theorem B921735 : Blo 920579 921735 := bstep (se 1 (by rfl) ⟨691301, by rfl⟩ : syracuseStep 921735 = 1382603) B1382603
theorem B921743 : Blo 920579 921743 := bstep (se 1 (by rfl) ⟨691307, by rfl⟩ : syracuseStep 921743 = 1382615) B1382615
theorem B921787 : Blo 920579 921787 := bstep (se 1 (by rfl) ⟨691340, by rfl⟩ : syracuseStep 921787 = 1382681) B1382681
theorem B3117257 : Blo 920579 3117257 := bstep (se 2 (by rfl) ⟨1168971, by rfl⟩ : syracuseStep 3117257 = 2337943) B2337943
theorem B921863 : Blo 920579 921863 := bstep (se 1 (by rfl) ⟨691397, by rfl⟩ : syracuseStep 921863 = 1382795) B1382795
theorem B3838223 : Blo 920579 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B921871 : Blo 920579 921871 := bstep (se 1 (by rfl) ⟨691403, by rfl⟩ : syracuseStep 921871 = 1382807) B1382807
theorem B921915 : Blo 920579 921915 := bstep (se 1 (by rfl) ⟨691436, by rfl⟩ : syracuseStep 921915 = 1382873) B1382873
theorem B921991 : Blo 920579 921991 := bstep (se 1 (by rfl) ⟨691493, by rfl⟩ : syracuseStep 921991 = 1382987) B1382987
theorem B1577351 : Blo 920579 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B1315207 : Blo 920579 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B921999 : Blo 920579 921999 := bstep (se 1 (by rfl) ⟨691499, by rfl⟩ : syracuseStep 921999 = 1382999) B1382999
theorem B922043 : Blo 920579 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B3936721 : Blo 920579 3936721 := bstep (se 2 (by rfl) ⟨1476270, by rfl⟩ : syracuseStep 3936721 = 2952541) B2952541
theorem B922119 : Blo 920579 922119 := bstep (se 1 (by rfl) ⟨691589, by rfl⟩ : syracuseStep 922119 = 1383179) B1383179
theorem B922127 : Blo 920579 922127 := bstep (se 1 (by rfl) ⟨691595, by rfl⟩ : syracuseStep 922127 = 1383191) B1383191
theorem B1380923 : Blo 920579 1380923 := bstep (se 1 (by rfl) ⟨1035692, by rfl⟩ : syracuseStep 1380923 = 2071385) B2071385
theorem B922171 : Blo 920579 922171 := bstep (se 1 (by rfl) ⟨691628, by rfl⟩ : syracuseStep 922171 = 1383257) B1383257
theorem B2331251 : Blo 920579 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B1380983 : Blo 920579 1380983 := bstep (se 1 (by rfl) ⟨1035737, by rfl⟩ : syracuseStep 1380983 = 2071475) B2071475
theorem B922247 : Blo 920579 922247 := bstep (se 1 (by rfl) ⟨691685, by rfl⟩ : syracuseStep 922247 = 1383371) B1383371
theorem B1381007 : Blo 920579 1381007 := bstep (se 1 (by rfl) ⟨1035755, by rfl⟩ : syracuseStep 1381007 = 2071511) B2071511
theorem B922255 : Blo 920579 922255 := bstep (se 1 (by rfl) ⟨691691, by rfl⟩ : syracuseStep 922255 = 1383383) B1383383
theorem B1381049 : Blo 920579 1381049 := bstep (se 2 (by rfl) ⟨517893, by rfl⟩ : syracuseStep 1381049 = 1035787) B1035787
theorem B922299 : Blo 920579 922299 := bstep (se 1 (by rfl) ⟨691724, by rfl⟩ : syracuseStep 922299 = 1383449) B1383449
theorem B6656741 : Blo 920579 6656741 := bstep (se 4 (by rfl) ⟨624069, by rfl⟩ : syracuseStep 6656741 = 1248139) B1248139
theorem B1381127 : Blo 920579 1381127 := bstep (se 1 (by rfl) ⟨1035845, by rfl⟩ : syracuseStep 1381127 = 2071691) B2071691
theorem B922375 : Blo 920579 922375 := bstep (se 1 (by rfl) ⟨691781, by rfl⟩ : syracuseStep 922375 = 1383563) B1383563
theorem B922383 : Blo 920579 922383 := bstep (se 1 (by rfl) ⟨691787, by rfl⟩ : syracuseStep 922383 = 1383575) B1383575
theorem B2626337 : Blo 920579 2626337 := bstep (se 2 (by rfl) ⟨984876, by rfl⟩ : syracuseStep 2626337 = 1969753) B1969753
theorem B1381163 : Blo 920579 1381163 := bstep (se 1 (by rfl) ⟨1035872, by rfl⟩ : syracuseStep 1381163 = 2071745) B2071745
theorem B922427 : Blo 920579 922427 := bstep (se 1 (by rfl) ⟨691820, by rfl⟩ : syracuseStep 922427 = 1383641) B1383641
theorem B1381193 : Blo 920579 1381193 := bstep (se 2 (by rfl) ⟨517947, by rfl⟩ : syracuseStep 1381193 = 1035895) B1035895
theorem B1315703 : Blo 920579 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B922503 : Blo 920579 922503 := bstep (se 1 (by rfl) ⟨691877, by rfl⟩ : syracuseStep 922503 = 1383755) B1383755
theorem B3117959 : Blo 920579 3117959 := bstep (se 1 (by rfl) ⟨2338469, by rfl⟩ : syracuseStep 3117959 = 4676939) B4676939
theorem B922511 : Blo 920579 922511 := bstep (se 1 (by rfl) ⟨691883, by rfl⟩ : syracuseStep 922511 = 1383767) B1383767
theorem B2626451 : Blo 920579 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B1381307 : Blo 920579 1381307 := bstep (se 1 (by rfl) ⟨1035980, by rfl⟩ : syracuseStep 1381307 = 2071961) B2071961
theorem B922555 : Blo 920579 922555 := bstep (se 1 (by rfl) ⟨691916, by rfl⟩ : syracuseStep 922555 = 1383833) B1383833
theorem B3412945 : Blo 920579 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B1381367 : Blo 920579 1381367 := bstep (se 1 (by rfl) ⟨1036025, by rfl⟩ : syracuseStep 1381367 = 2072051) B2072051
theorem B922631 : Blo 920579 922631 := bstep (se 1 (by rfl) ⟨691973, by rfl⟩ : syracuseStep 922631 = 1383947) B1383947
theorem B1381391 : Blo 920579 1381391 := bstep (se 1 (by rfl) ⟨1036043, by rfl⟩ : syracuseStep 1381391 = 2072087) B2072087
theorem B922639 : Blo 920579 922639 := bstep (se 1 (by rfl) ⟨691979, by rfl⟩ : syracuseStep 922639 = 1383959) B1383959
theorem B1381433 : Blo 920579 1381433 := bstep (se 2 (by rfl) ⟨518037, by rfl⟩ : syracuseStep 1381433 = 1036075) B1036075
theorem B922683 : Blo 920579 922683 := bstep (se 1 (by rfl) ⟨692012, by rfl⟩ : syracuseStep 922683 = 1384025) B1384025
theorem B2331767 : Blo 920579 2331767 := bstep (se 1 (by rfl) ⟨1748825, by rfl⟩ : syracuseStep 2331767 = 3497651) B3497651
theorem B1381511 : Blo 920579 1381511 := bstep (se 1 (by rfl) ⟨1036133, by rfl⟩ : syracuseStep 1381511 = 2072267) B2072267
theorem B922759 : Blo 920579 922759 := bstep (se 1 (by rfl) ⟨692069, by rfl⟩ : syracuseStep 922759 = 1384139) B1384139
theorem B922767 : Blo 920579 922767 := bstep (se 1 (by rfl) ⟨692075, by rfl⟩ : syracuseStep 922767 = 1384151) B1384151
theorem B1381547 : Blo 920579 1381547 := bstep (se 1 (by rfl) ⟨1036160, by rfl⟩ : syracuseStep 1381547 = 2072321) B2072321
theorem B1479865 : Blo 920579 1479865 := bstep (se 2 (by rfl) ⟨554949, by rfl⟩ : syracuseStep 1479865 = 1109899) B1109899
theorem B922811 : Blo 920579 922811 := bstep (se 1 (by rfl) ⟨692108, by rfl⟩ : syracuseStep 922811 = 1384217) B1384217
theorem B1381577 : Blo 920579 1381577 := bstep (se 2 (by rfl) ⟨518091, by rfl⟩ : syracuseStep 1381577 = 1036183) B1036183
theorem B3118337 : Blo 920579 3118337 := bstep (se 2 (by rfl) ⟨1169376, by rfl⟩ : syracuseStep 3118337 = 2338753) B2338753
theorem B922887 : Blo 920579 922887 := bstep (se 1 (by rfl) ⟨692165, by rfl⟩ : syracuseStep 922887 = 1384331) B1384331
theorem B922895 : Blo 920579 922895 := bstep (se 1 (by rfl) ⟨692171, by rfl⟩ : syracuseStep 922895 = 1384343) B1384343
theorem B1381691 : Blo 920579 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B922939 : Blo 920579 922939 := bstep (se 1 (by rfl) ⟨692204, by rfl⟩ : syracuseStep 922939 = 1384409) B1384409
theorem B1381751 : Blo 920579 1381751 := bstep (se 1 (by rfl) ⟨1036313, by rfl⟩ : syracuseStep 1381751 = 2072627) B2072627
theorem B923015 : Blo 920579 923015 := bstep (se 1 (by rfl) ⟨692261, by rfl⟩ : syracuseStep 923015 = 1384523) B1384523
theorem B1381775 : Blo 920579 1381775 := bstep (se 1 (by rfl) ⟨1036331, by rfl⟩ : syracuseStep 1381775 = 2072663) B2072663
theorem B923023 : Blo 920579 923023 := bstep (se 1 (by rfl) ⟨692267, by rfl⟩ : syracuseStep 923023 = 1384535) B1384535
theorem B1381817 : Blo 920579 1381817 := bstep (se 2 (by rfl) ⟨518181, by rfl⟩ : syracuseStep 1381817 = 1036363) B1036363
theorem B1971641 : Blo 920579 1971641 := bstep (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) B1478731
theorem B923067 : Blo 920579 923067 := bstep (se 1 (by rfl) ⟨692300, by rfl⟩ : syracuseStep 923067 = 1384601) B1384601
theorem B1480121 : Blo 920579 1480121 := bstep (se 2 (by rfl) ⟨555045, by rfl⟩ : syracuseStep 1480121 = 1110091) B1110091
theorem B1054139 : Blo 920579 1054139 := bstep (se 1 (by rfl) ⟨790604, by rfl⟩ : syracuseStep 1054139 = 1581209) B1581209
theorem B1381895 : Blo 920579 1381895 := bstep (se 1 (by rfl) ⟨1036421, by rfl⟩ : syracuseStep 1381895 = 2072843) B2072843
theorem B923143 : Blo 920579 923143 := bstep (se 1 (by rfl) ⟨692357, by rfl⟩ : syracuseStep 923143 = 1384715) B1384715
theorem B923151 : Blo 920579 923151 := bstep (se 1 (by rfl) ⟨692363, by rfl⟩ : syracuseStep 923151 = 1384727) B1384727
theorem B118494737 : Blo 920579 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B1381931 : Blo 920579 1381931 := bstep (se 1 (by rfl) ⟨1036448, by rfl⟩ : syracuseStep 1381931 = 2072897) B2072897
theorem B923195 : Blo 920579 923195 := bstep (se 1 (by rfl) ⟨692396, by rfl⟩ : syracuseStep 923195 = 1384793) B1384793
theorem B1381961 : Blo 920579 1381961 := bstep (se 2 (by rfl) ⟨518235, by rfl⟩ : syracuseStep 1381961 = 1036471) B1036471
theorem B923271 : Blo 920579 923271 := bstep (se 1 (by rfl) ⟨692453, by rfl⟩ : syracuseStep 923271 = 1384907) B1384907
theorem B923279 : Blo 920579 923279 := bstep (se 1 (by rfl) ⟨692459, by rfl⟩ : syracuseStep 923279 = 1384919) B1384919
theorem B2627225 : Blo 920579 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B1382075 : Blo 920579 1382075 := bstep (se 1 (by rfl) ⟨1036556, by rfl⟩ : syracuseStep 1382075 = 2073113) B2073113
theorem B923323 : Blo 920579 923323 := bstep (se 1 (by rfl) ⟨692492, by rfl⟩ : syracuseStep 923323 = 1384985) B1384985
theorem B1382135 : Blo 920579 1382135 := bstep (se 1 (by rfl) ⟨1036601, by rfl⟩ : syracuseStep 1382135 = 2073203) B2073203
theorem B923399 : Blo 920579 923399 := bstep (se 1 (by rfl) ⟨692549, by rfl⟩ : syracuseStep 923399 = 1385099) B1385099
theorem B1382159 : Blo 920579 1382159 := bstep (se 1 (by rfl) ⟨1036619, by rfl⟩ : syracuseStep 1382159 = 2073239) B2073239
theorem B923407 : Blo 920579 923407 := bstep (se 1 (by rfl) ⟨692555, by rfl⟩ : syracuseStep 923407 = 1385111) B1385111
theorem B11802419 : Blo 920579 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B1382201 : Blo 920579 1382201 := bstep (se 2 (by rfl) ⟨518325, by rfl⟩ : syracuseStep 1382201 = 1036651) B1036651
theorem B923451 : Blo 920579 923451 := bstep (se 1 (by rfl) ⟨692588, by rfl⟩ : syracuseStep 923451 = 1385177) B1385177
theorem B1382279 : Blo 920579 1382279 := bstep (se 1 (by rfl) ⟨1036709, by rfl⟩ : syracuseStep 1382279 = 2073419) B2073419
theorem B2955143 : Blo 920579 2955143 := bstep (se 1 (by rfl) ⟨2216357, by rfl⟩ : syracuseStep 2955143 = 4432715) B4432715
theorem B923527 : Blo 920579 923527 := bstep (se 1 (by rfl) ⟨692645, by rfl⟩ : syracuseStep 923527 = 1385291) B1385291
theorem B923535 : Blo 920579 923535 := bstep (se 1 (by rfl) ⟨692651, by rfl⟩ : syracuseStep 923535 = 1385303) B1385303
theorem B1382315 : Blo 920579 1382315 := bstep (se 1 (by rfl) ⟨1036736, by rfl⟩ : syracuseStep 1382315 = 2073473) B2073473
theorem B923579 : Blo 920579 923579 := bstep (se 1 (by rfl) ⟨692684, by rfl⟩ : syracuseStep 923579 = 1385369) B1385369
theorem B1382345 : Blo 920579 1382345 := bstep (se 2 (by rfl) ⟨518379, by rfl⟩ : syracuseStep 1382345 = 1036759) B1036759
theorem B923655 : Blo 920579 923655 := bstep (se 1 (by rfl) ⟨692741, by rfl⟩ : syracuseStep 923655 = 1385483) B1385483
theorem B923663 : Blo 920579 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B3119147 : Blo 920579 3119147 := bstep (se 1 (by rfl) ⟨2339360, by rfl⟩ : syracuseStep 3119147 = 4678721) B4678721
theorem B1382459 : Blo 920579 1382459 := bstep (se 1 (by rfl) ⟨1036844, by rfl⟩ : syracuseStep 1382459 = 2073689) B2073689
theorem B923707 : Blo 920579 923707 := bstep (se 1 (by rfl) ⟨692780, by rfl⟩ : syracuseStep 923707 = 1385561) B1385561
theorem B2332759 : Blo 920579 2332759 := bstep (se 1 (by rfl) ⟨1749569, by rfl⟩ : syracuseStep 2332759 = 3499139) B3499139
theorem B1382519 : Blo 920579 1382519 := bstep (se 1 (by rfl) ⟨1036889, by rfl⟩ : syracuseStep 1382519 = 2073779) B2073779
theorem B923783 : Blo 920579 923783 := bstep (se 1 (by rfl) ⟨692837, by rfl⟩ : syracuseStep 923783 = 1385675) B1385675
theorem B1382543 : Blo 920579 1382543 := bstep (se 1 (by rfl) ⟨1036907, by rfl⟩ : syracuseStep 1382543 = 2073815) B2073815
theorem B923791 : Blo 920579 923791 := bstep (se 1 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 923791 = 1385687) B1385687
theorem B1382585 : Blo 920579 1382585 := bstep (se 2 (by rfl) ⟨518469, by rfl⟩ : syracuseStep 1382585 = 1036939) B1036939
theorem B923835 : Blo 920579 923835 := bstep (se 1 (by rfl) ⟨692876, by rfl⟩ : syracuseStep 923835 = 1385753) B1385753
theorem B1382663 : Blo 920579 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B923911 : Blo 920579 923911 := bstep (se 1 (by rfl) ⟨692933, by rfl⟩ : syracuseStep 923911 = 1385867) B1385867
theorem B923919 : Blo 920579 923919 := bstep (se 1 (by rfl) ⟨692939, by rfl⟩ : syracuseStep 923919 = 1385879) B1385879
theorem B1382699 : Blo 920579 1382699 := bstep (se 1 (by rfl) ⟨1037024, by rfl⟩ : syracuseStep 1382699 = 2074049) B2074049
theorem B923963 : Blo 920579 923963 := bstep (se 1 (by rfl) ⟨692972, by rfl⟩ : syracuseStep 923963 = 1385945) B1385945
theorem B7018811 : Blo 920579 7018811 := bstep (se 1 (by rfl) ⟨5264108, by rfl⟩ : syracuseStep 7018811 = 10528217) B10528217
theorem B1382729 : Blo 920579 1382729 := bstep (se 2 (by rfl) ⟨518523, by rfl⟩ : syracuseStep 1382729 = 1037047) B1037047
theorem B2333063 : Blo 920579 2333063 := bstep (se 1 (by rfl) ⟨1749797, by rfl⟩ : syracuseStep 2333063 = 3499595) B3499595
theorem B924039 : Blo 920579 924039 := bstep (se 1 (by rfl) ⟨693029, by rfl⟩ : syracuseStep 924039 = 1386059) B1386059
theorem B924047 : Blo 920579 924047 := bstep (se 1 (by rfl) ⟨693035, by rfl⟩ : syracuseStep 924047 = 1386071) B1386071
theorem B1382843 : Blo 920579 1382843 := bstep (se 1 (by rfl) ⟨1037132, by rfl⟩ : syracuseStep 1382843 = 2074265) B2074265
theorem B924091 : Blo 920579 924091 := bstep (se 1 (by rfl) ⟨693068, by rfl⟩ : syracuseStep 924091 = 1386137) B1386137
theorem B1382903 : Blo 920579 1382903 := bstep (se 1 (by rfl) ⟨1037177, by rfl⟩ : syracuseStep 1382903 = 2074355) B2074355
theorem B924167 : Blo 920579 924167 := bstep (se 1 (by rfl) ⟨693125, by rfl⟩ : syracuseStep 924167 = 1386251) B1386251
theorem B2333195 : Blo 920579 2333195 := bstep (se 1 (by rfl) ⟨1749896, by rfl⟩ : syracuseStep 2333195 = 3499793) B3499793
theorem B1382927 : Blo 920579 1382927 := bstep (se 1 (by rfl) ⟨1037195, by rfl⟩ : syracuseStep 1382927 = 2074391) B2074391
theorem B924175 : Blo 920579 924175 := bstep (se 1 (by rfl) ⟨693131, by rfl⟩ : syracuseStep 924175 = 1386263) B1386263
theorem B1382969 : Blo 920579 1382969 := bstep (se 2 (by rfl) ⟨518613, by rfl⟩ : syracuseStep 1382969 = 1037227) B1037227
theorem B924219 : Blo 920579 924219 := bstep (se 1 (by rfl) ⟨693164, by rfl⟩ : syracuseStep 924219 = 1386329) B1386329
theorem B8428151 : Blo 920579 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B1383047 : Blo 920579 1383047 := bstep (se 1 (by rfl) ⟨1037285, by rfl⟩ : syracuseStep 1383047 = 2074571) B2074571
theorem B924295 : Blo 920579 924295 := bstep (se 1 (by rfl) ⟨693221, by rfl⟩ : syracuseStep 924295 = 1386443) B1386443
theorem B924303 : Blo 920579 924303 := bstep (se 1 (by rfl) ⟨693227, by rfl⟩ : syracuseStep 924303 = 1386455) B1386455
theorem B1383083 : Blo 920579 1383083 := bstep (se 1 (by rfl) ⟨1037312, by rfl⟩ : syracuseStep 1383083 = 2074625) B2074625
theorem B924347 : Blo 920579 924347 := bstep (se 1 (by rfl) ⟨693260, by rfl⟩ : syracuseStep 924347 = 1386521) B1386521
theorem B1383113 : Blo 920579 1383113 := bstep (se 2 (by rfl) ⟨518667, by rfl⟩ : syracuseStep 1383113 = 1037335) B1037335
theorem B924423 : Blo 920579 924423 := bstep (se 1 (by rfl) ⟨693317, by rfl⟩ : syracuseStep 924423 = 1386635) B1386635
theorem B2661131 : Blo 920579 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B924431 : Blo 920579 924431 := bstep (se 1 (by rfl) ⟨693323, by rfl⟩ : syracuseStep 924431 = 1386647) B1386647
theorem B1383227 : Blo 920579 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B924475 : Blo 920579 924475 := bstep (se 1 (by rfl) ⟨693356, by rfl⟩ : syracuseStep 924475 = 1386713) B1386713
theorem B1383287 : Blo 920579 1383287 := bstep (se 1 (by rfl) ⟨1037465, by rfl⟩ : syracuseStep 1383287 = 2074931) B2074931
theorem B924551 : Blo 920579 924551 := bstep (se 1 (by rfl) ⟨693413, by rfl⟩ : syracuseStep 924551 = 1386827) B1386827
theorem B1383311 : Blo 920579 1383311 := bstep (se 1 (by rfl) ⟨1037483, by rfl⟩ : syracuseStep 1383311 = 2074967) B2074967
theorem B924559 : Blo 920579 924559 := bstep (se 1 (by rfl) ⟨693419, by rfl⟩ : syracuseStep 924559 = 1386839) B1386839
theorem B1383353 : Blo 920579 1383353 := bstep (se 2 (by rfl) ⟨518757, by rfl⟩ : syracuseStep 1383353 = 1037515) B1037515
theorem B1383431 : Blo 920579 1383431 := bstep (se 1 (by rfl) ⟨1037573, by rfl⟩ : syracuseStep 1383431 = 2075147) B2075147
theorem B2333711 : Blo 920579 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B1383467 : Blo 920579 1383467 := bstep (se 1 (by rfl) ⟨1037600, by rfl⟩ : syracuseStep 1383467 = 2075201) B2075201
theorem B1383497 : Blo 920579 1383497 := bstep (se 2 (by rfl) ⟨518811, by rfl⟩ : syracuseStep 1383497 = 1037623) B1037623
theorem B5250167 : Blo 920579 5250167 := bstep (se 1 (by rfl) ⟨3937625, by rfl⟩ : syracuseStep 5250167 = 7875251) B7875251
theorem B2333843 : Blo 920579 2333843 := bstep (se 1 (by rfl) ⟨1750382, by rfl⟩ : syracuseStep 2333843 = 3500765) B3500765
theorem B1121467 : Blo 920579 1121467 := bstep (se 1 (by rfl) ⟨841100, by rfl⟩ : syracuseStep 1121467 = 1682201) B1682201
theorem B1383611 : Blo 920579 1383611 := bstep (se 1 (by rfl) ⟨1037708, by rfl⟩ : syracuseStep 1383611 = 2075417) B2075417
theorem B1383671 : Blo 920579 1383671 := bstep (se 1 (by rfl) ⟨1037753, by rfl⟩ : syracuseStep 1383671 = 2075507) B2075507
theorem B2628865 : Blo 920579 2628865 := bstep (se 2 (by rfl) ⟨985824, by rfl⟩ : syracuseStep 2628865 = 1971649) B1971649
theorem B1383695 : Blo 920579 1383695 := bstep (se 1 (by rfl) ⟨1037771, by rfl⟩ : syracuseStep 1383695 = 2075543) B2075543
theorem B1383737 : Blo 920579 1383737 := bstep (se 2 (by rfl) ⟨518901, by rfl⟩ : syracuseStep 1383737 = 1037803) B1037803
theorem B3120443 : Blo 920579 3120443 := bstep (se 1 (by rfl) ⟨2340332, by rfl⟩ : syracuseStep 3120443 = 4680665) B4680665
theorem B5250419 : Blo 920579 5250419 := bstep (se 1 (by rfl) ⟨3937814, by rfl⟩ : syracuseStep 5250419 = 7875629) B7875629
theorem B2071943 : Blo 920579 2071943 := bstep (se 1 (by rfl) ⟨1553957, by rfl⟩ : syracuseStep 2071943 = 3107915) B3107915
theorem B1383815 : Blo 920579 1383815 := bstep (se 1 (by rfl) ⟨1037861, by rfl⟩ : syracuseStep 1383815 = 2075723) B2075723
theorem B6495623 : Blo 920579 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1383851 : Blo 920579 1383851 := bstep (se 1 (by rfl) ⟨1037888, by rfl⟩ : syracuseStep 1383851 = 2075777) B2075777
theorem B1383881 : Blo 920579 1383881 := bstep (se 2 (by rfl) ⟨518955, by rfl⟩ : syracuseStep 1383881 = 1037911) B1037911
theorem B4660739 : Blo 920579 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B2072123 : Blo 920579 2072123 := bstep (se 1 (by rfl) ⟨1554092, by rfl⟩ : syracuseStep 2072123 = 3108185) B3108185
theorem B1383995 : Blo 920579 1383995 := bstep (se 1 (by rfl) ⟨1037996, by rfl⟩ : syracuseStep 1383995 = 2075993) B2075993
theorem B1384055 : Blo 920579 1384055 := bstep (se 1 (by rfl) ⟨1038041, by rfl⟩ : syracuseStep 1384055 = 2076083) B2076083
theorem B1384079 : Blo 920579 1384079 := bstep (se 1 (by rfl) ⟨1038059, by rfl⟩ : syracuseStep 1384079 = 2076119) B2076119
theorem B2072249 : Blo 920579 2072249 := bstep (se 2 (by rfl) ⟨777093, by rfl⟩ : syracuseStep 2072249 = 1554187) B1554187
theorem B1384121 : Blo 920579 1384121 := bstep (se 2 (by rfl) ⟨519045, by rfl⟩ : syracuseStep 1384121 = 1038091) B1038091
theorem B4562669 : Blo 920579 4562669 := bstep (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) B1711001
theorem B1384199 : Blo 920579 1384199 := bstep (se 1 (by rfl) ⟨1038149, by rfl⟩ : syracuseStep 1384199 = 2076299) B2076299
theorem B1384235 : Blo 920579 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B4497203 : Blo 920579 4497203 := bstep (se 1 (by rfl) ⟨3372902, by rfl⟩ : syracuseStep 4497203 = 6745805) B6745805
theorem B2629435 : Blo 920579 2629435 := bstep (se 1 (by rfl) ⟨1972076, by rfl⟩ : syracuseStep 2629435 = 3944153) B3944153
theorem B1384265 : Blo 920579 1384265 := bstep (se 2 (by rfl) ⟨519099, by rfl⟩ : syracuseStep 1384265 = 1038199) B1038199
theorem B1384379 : Blo 920579 1384379 := bstep (se 1 (by rfl) ⟨1038284, by rfl⟩ : syracuseStep 1384379 = 2076569) B2076569
theorem B1384439 : Blo 920579 1384439 := bstep (se 1 (by rfl) ⟨1038329, by rfl⟩ : syracuseStep 1384439 = 2076659) B2076659
theorem B2072591 : Blo 920579 2072591 := bstep (se 1 (by rfl) ⟨1554443, by rfl⟩ : syracuseStep 2072591 = 3108887) B3108887
theorem B1384463 : Blo 920579 1384463 := bstep (se 1 (by rfl) ⟨1038347, by rfl⟩ : syracuseStep 1384463 = 2076695) B2076695
theorem B2072609 : Blo 920579 2072609 := bstep (se 2 (by rfl) ⟨777228, by rfl⟩ : syracuseStep 2072609 = 1554457) B1554457
theorem B1384505 : Blo 920579 1384505 := bstep (se 2 (by rfl) ⟨519189, by rfl⟩ : syracuseStep 1384505 = 1038379) B1038379
theorem B5906519 : Blo 920579 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B1384583 : Blo 920579 1384583 := bstep (se 1 (by rfl) ⟨1038437, by rfl⟩ : syracuseStep 1384583 = 2076875) B2076875
theorem B1384619 : Blo 920579 1384619 := bstep (se 1 (by rfl) ⟨1038464, by rfl⟩ : syracuseStep 1384619 = 2076929) B2076929
theorem B1384649 : Blo 920579 1384649 := bstep (se 2 (by rfl) ⟨519243, by rfl⟩ : syracuseStep 1384649 = 1038487) B1038487
theorem B2334977 : Blo 920579 2334977 := bstep (se 2 (by rfl) ⟨875616, by rfl⟩ : syracuseStep 2334977 = 1751233) B1751233
theorem B2105633 : Blo 920579 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B5611835 : Blo 920579 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B1384763 : Blo 920579 1384763 := bstep (se 1 (by rfl) ⟨1038572, by rfl⟩ : syracuseStep 1384763 = 2077145) B2077145
theorem B2072951 : Blo 920579 2072951 := bstep (se 1 (by rfl) ⟨1554713, by rfl⟩ : syracuseStep 2072951 = 3109427) B3109427
theorem B1384823 : Blo 920579 1384823 := bstep (se 1 (by rfl) ⟨1038617, by rfl⟩ : syracuseStep 1384823 = 2077235) B2077235
theorem B9970055 : Blo 920579 9970055 := bstep (se 1 (by rfl) ⟨7477541, by rfl⟩ : syracuseStep 9970055 = 14955083) B14955083
theorem B1384847 : Blo 920579 1384847 := bstep (se 1 (by rfl) ⟨1038635, by rfl⟩ : syracuseStep 1384847 = 2077271) B2077271
theorem B1384889 : Blo 920579 1384889 := bstep (se 2 (by rfl) ⟨519333, by rfl⟩ : syracuseStep 1384889 = 1038667) B1038667
theorem B1384967 : Blo 920579 1384967 := bstep (se 1 (by rfl) ⟨1038725, by rfl⟩ : syracuseStep 1384967 = 2077451) B2077451
theorem B2073131 : Blo 920579 2073131 := bstep (se 1 (by rfl) ⟨1554848, by rfl⟩ : syracuseStep 2073131 = 3109697) B3109697
theorem B1385003 : Blo 920579 1385003 := bstep (se 1 (by rfl) ⟨1038752, by rfl⟩ : syracuseStep 1385003 = 2077505) B2077505
theorem B1385033 : Blo 920579 1385033 := bstep (se 2 (by rfl) ⟨519387, by rfl⟩ : syracuseStep 1385033 = 1038775) B1038775
theorem B2335351 : Blo 920579 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B1385147 : Blo 920579 1385147 := bstep (se 1 (by rfl) ⟨1038860, by rfl⟩ : syracuseStep 1385147 = 2077721) B2077721
theorem B4727497 : Blo 920579 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B3318509 : Blo 920579 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B1385207 : Blo 920579 1385207 := bstep (se 1 (by rfl) ⟨1038905, by rfl⟩ : syracuseStep 1385207 = 2077811) B2077811
theorem B1385231 : Blo 920579 1385231 := bstep (se 1 (by rfl) ⟨1038923, by rfl⟩ : syracuseStep 1385231 = 2077847) B2077847
theorem B5251877 : Blo 920579 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B1385273 : Blo 920579 1385273 := bstep (se 2 (by rfl) ⟨519477, by rfl⟩ : syracuseStep 1385273 = 1038955) B1038955
theorem B1385351 : Blo 920579 1385351 := bstep (se 1 (by rfl) ⟨1039013, by rfl⟩ : syracuseStep 1385351 = 2078027) B2078027
theorem B4727699 : Blo 920579 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B2073491 : Blo 920579 2073491 := bstep (se 1 (by rfl) ⟨1555118, by rfl⟩ : syracuseStep 2073491 = 3110237) B3110237
theorem B1385387 : Blo 920579 1385387 := bstep (se 1 (by rfl) ⟨1039040, by rfl⟩ : syracuseStep 1385387 = 2078081) B2078081
theorem B2073545 : Blo 920579 2073545 := bstep (se 2 (by rfl) ⟨777579, by rfl⟩ : syracuseStep 2073545 = 1555159) B1555159
theorem B1385417 : Blo 920579 1385417 := bstep (se 2 (by rfl) ⟨519531, by rfl⟩ : syracuseStep 1385417 = 1039063) B1039063
theorem B3941419 : Blo 920579 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B2335787 : Blo 920579 2335787 := bstep (se 1 (by rfl) ⟨1751840, by rfl⟩ : syracuseStep 2335787 = 3503681) B3503681
theorem B1385531 : Blo 920579 1385531 := bstep (se 1 (by rfl) ⟨1039148, by rfl⟩ : syracuseStep 1385531 = 2078297) B2078297
theorem B4662359 : Blo 920579 4662359 := bstep (se 1 (by rfl) ⟨3496769, by rfl⟩ : syracuseStep 4662359 = 6993539) B6993539
theorem B1385591 : Blo 920579 1385591 := bstep (se 1 (by rfl) ⟨1039193, by rfl⟩ : syracuseStep 1385591 = 2078387) B2078387
theorem B1385615 : Blo 920579 1385615 := bstep (se 1 (by rfl) ⟨1039211, by rfl⟩ : syracuseStep 1385615 = 2078423) B2078423
theorem B1385657 : Blo 920579 1385657 := bstep (se 2 (by rfl) ⟨519621, by rfl⟩ : syracuseStep 1385657 = 1039243) B1039243
theorem B1385735 : Blo 920579 1385735 := bstep (se 1 (by rfl) ⟨1039301, by rfl⟩ : syracuseStep 1385735 = 2078603) B2078603
theorem B1385771 : Blo 920579 1385771 := bstep (se 1 (by rfl) ⟨1039328, by rfl⟩ : syracuseStep 1385771 = 2078657) B2078657
theorem B1385801 : Blo 920579 1385801 := bstep (se 2 (by rfl) ⟨519675, by rfl⟩ : syracuseStep 1385801 = 1039351) B1039351
theorem B1385915 : Blo 920579 1385915 := bstep (se 1 (by rfl) ⟨1039436, by rfl⟩ : syracuseStep 1385915 = 2078873) B2078873
theorem B1385975 : Blo 920579 1385975 := bstep (se 1 (by rfl) ⟨1039481, by rfl⟩ : syracuseStep 1385975 = 2078963) B2078963
theorem B1385999 : Blo 920579 1385999 := bstep (se 1 (by rfl) ⟨1039499, by rfl⟩ : syracuseStep 1385999 = 2078999) B2078999
theorem B1386041 : Blo 920579 1386041 := bstep (se 2 (by rfl) ⟨519765, by rfl⟩ : syracuseStep 1386041 = 1039531) B1039531
theorem B4662845 : Blo 920579 4662845 := bstep (se 3 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 4662845 = 1748567) B1748567
theorem B22488677 : Blo 920579 22488677 := bstep (se 4 (by rfl) ⟨2108313, by rfl⟩ : syracuseStep 22488677 = 4216627) B4216627
theorem B2074247 : Blo 920579 2074247 := bstep (se 1 (by rfl) ⟨1555685, by rfl⟩ : syracuseStep 2074247 = 3111371) B3111371
theorem B1386119 : Blo 920579 1386119 := bstep (se 1 (by rfl) ⟨1039589, by rfl⟩ : syracuseStep 1386119 = 2079179) B2079179
theorem B1386155 : Blo 920579 1386155 := bstep (se 1 (by rfl) ⟨1039616, by rfl⟩ : syracuseStep 1386155 = 2079233) B2079233
theorem B5252809 : Blo 920579 5252809 := bstep (se 2 (by rfl) ⟨1969803, by rfl⟩ : syracuseStep 5252809 = 3939607) B3939607
theorem B1386185 : Blo 920579 1386185 := bstep (se 2 (by rfl) ⟨519819, by rfl⟩ : syracuseStep 1386185 = 1039639) B1039639
theorem B2074427 : Blo 920579 2074427 := bstep (se 1 (by rfl) ⟨1555820, by rfl⟩ : syracuseStep 2074427 = 3111641) B3111641
theorem B1386299 : Blo 920579 1386299 := bstep (se 1 (by rfl) ⟨1039724, by rfl⟩ : syracuseStep 1386299 = 2079449) B2079449
theorem B2336627 : Blo 920579 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1386359 : Blo 920579 1386359 := bstep (se 1 (by rfl) ⟨1039769, by rfl⟩ : syracuseStep 1386359 = 2079539) B2079539
theorem B2336647 : Blo 920579 2336647 := bstep (se 1 (by rfl) ⟨1752485, by rfl⟩ : syracuseStep 2336647 = 3504971) B3504971
theorem B1386383 : Blo 920579 1386383 := bstep (se 1 (by rfl) ⟨1039787, by rfl⟩ : syracuseStep 1386383 = 2079575) B2079575
theorem B2074553 : Blo 920579 2074553 := bstep (se 2 (by rfl) ⟨777957, by rfl⟩ : syracuseStep 2074553 = 1555915) B1555915
theorem B1386425 : Blo 920579 1386425 := bstep (se 2 (by rfl) ⟨519909, by rfl⟩ : syracuseStep 1386425 = 1039819) B1039819
theorem B1386503 : Blo 920579 1386503 := bstep (se 1 (by rfl) ⟨1039877, by rfl⟩ : syracuseStep 1386503 = 2079755) B2079755
theorem B1386539 : Blo 920579 1386539 := bstep (se 1 (by rfl) ⟨1039904, by rfl⟩ : syracuseStep 1386539 = 2079809) B2079809
theorem B2959421 : Blo 920579 2959421 := bstep (se 3 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 2959421 = 1109783) B1109783
theorem B1386569 : Blo 920579 1386569 := bstep (se 2 (by rfl) ⟨519963, by rfl⟩ : syracuseStep 1386569 = 1039927) B1039927
theorem B2631827 : Blo 920579 2631827 := bstep (se 1 (by rfl) ⟨1973870, by rfl⟩ : syracuseStep 2631827 = 3947741) B3947741
theorem B2336921 : Blo 920579 2336921 := bstep (se 2 (by rfl) ⟨876345, by rfl⟩ : syracuseStep 2336921 = 1752691) B1752691
theorem B1386683 : Blo 920579 1386683 := bstep (se 1 (by rfl) ⟨1040012, by rfl⟩ : syracuseStep 1386683 = 2080025) B2080025
theorem B1386743 : Blo 920579 1386743 := bstep (se 1 (by rfl) ⟨1040057, by rfl⟩ : syracuseStep 1386743 = 2080115) B2080115
theorem B2369803 : Blo 920579 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B2074895 : Blo 920579 2074895 := bstep (se 1 (by rfl) ⟨1556171, by rfl⟩ : syracuseStep 2074895 = 3112343) B3112343
theorem B1386767 : Blo 920579 1386767 := bstep (se 1 (by rfl) ⟨1040075, by rfl⟩ : syracuseStep 1386767 = 2080151) B2080151
theorem B2074913 : Blo 920579 2074913 := bstep (se 2 (by rfl) ⟨778092, by rfl⟩ : syracuseStep 2074913 = 1556185) B1556185
theorem B1386809 : Blo 920579 1386809 := bstep (se 2 (by rfl) ⟨520053, by rfl⟩ : syracuseStep 1386809 = 1040107) B1040107
theorem B2337083 : Blo 920579 2337083 := bstep (se 1 (by rfl) ⟨1752812, by rfl⟩ : syracuseStep 2337083 = 3505625) B3505625
theorem B2337295 : Blo 920579 2337295 := bstep (se 1 (by rfl) ⟨1752971, by rfl⟩ : syracuseStep 2337295 = 3505943) B3505943
theorem B3156509 : Blo 920579 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B2075255 : Blo 920579 2075255 := bstep (se 1 (by rfl) ⟨1556441, by rfl⟩ : syracuseStep 2075255 = 3112883) B3112883
theorem B2337569 : Blo 920579 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B2075435 : Blo 920579 2075435 := bstep (se 1 (by rfl) ⟨1556576, by rfl⟩ : syracuseStep 2075435 = 3113153) B3113153
theorem B1747831 : Blo 920579 1747831 := bstep (se 1 (by rfl) ⟨1310873, by rfl⟩ : syracuseStep 1747831 = 2621747) B2621747
theorem B3156889 : Blo 920579 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B2632601 : Blo 920579 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B9972823 : Blo 920579 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B5614679 : Blo 920579 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B2075795 : Blo 920579 2075795 := bstep (se 1 (by rfl) ⟨1556846, by rfl⟩ : syracuseStep 2075795 = 3113693) B3113693
theorem B2075849 : Blo 920579 2075849 := bstep (se 2 (by rfl) ⟨778443, by rfl⟩ : syracuseStep 2075849 = 1556887) B1556887
theorem B4664627 : Blo 920579 4664627 := bstep (se 1 (by rfl) ⟨3498470, by rfl⟩ : syracuseStep 4664627 = 6996941) B6996941
theorem B4664951 : Blo 920579 4664951 := bstep (se 1 (by rfl) ⟨3498713, by rfl⟩ : syracuseStep 4664951 = 6997427) B6997427
theorem B2338571 : Blo 920579 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B19967789 : Blo 920579 19967789 := bstep (se 3 (by rfl) ⟨3743960, by rfl⟩ : syracuseStep 19967789 = 7487921) B7487921
theorem B2076551 : Blo 920579 2076551 := bstep (se 1 (by rfl) ⟨1557413, by rfl⟩ : syracuseStep 2076551 = 3114827) B3114827
theorem B2076731 : Blo 920579 2076731 := bstep (se 1 (by rfl) ⟨1557548, by rfl⟩ : syracuseStep 2076731 = 3115097) B3115097
theorem B2076857 : Blo 920579 2076857 := bstep (se 2 (by rfl) ⟨778821, by rfl⟩ : syracuseStep 2076857 = 1557643) B1557643
theorem B4993331 : Blo 920579 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B3322259 : Blo 920579 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B19968403 : Blo 920579 19968403 := bstep (se 1 (by rfl) ⟨14976302, by rfl⟩ : syracuseStep 19968403 = 29952605) B29952605
theorem B2339219 : Blo 920579 2339219 := bstep (se 1 (by rfl) ⟨1754414, by rfl⟩ : syracuseStep 2339219 = 3508829) B3508829
theorem B1749433 : Blo 920579 1749433 := bstep (se 2 (by rfl) ⟨656037, by rfl⟩ : syracuseStep 1749433 = 1312075) B1312075
theorem B2077199 : Blo 920579 2077199 := bstep (se 1 (by rfl) ⟨1557899, by rfl⟩ : syracuseStep 2077199 = 3115799) B3115799
theorem B2077217 : Blo 920579 2077217 := bstep (se 2 (by rfl) ⟨778956, by rfl⟩ : syracuseStep 2077217 = 1557913) B1557913
theorem B4665923 : Blo 920579 4665923 := bstep (se 1 (by rfl) ⟨3499442, by rfl⟩ : syracuseStep 4665923 = 6998885) B6998885
theorem B2339513 : Blo 920579 2339513 := bstep (se 2 (by rfl) ⟨877317, by rfl⟩ : syracuseStep 2339513 = 1754635) B1754635
theorem B1749775 : Blo 920579 1749775 := bstep (se 1 (by rfl) ⟨1312331, by rfl⟩ : syracuseStep 1749775 = 2624663) B2624663
theorem B2732843 : Blo 920579 2732843 := bstep (se 1 (by rfl) ⟨2049632, by rfl⟩ : syracuseStep 2732843 = 4099265) B4099265
theorem B4731763 : Blo 920579 4731763 := bstep (se 1 (by rfl) ⟨3548822, by rfl⟩ : syracuseStep 4731763 = 7097645) B7097645
theorem B2077559 : Blo 920579 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B4666247 : Blo 920579 4666247 := bstep (se 1 (by rfl) ⟨3499685, by rfl⟩ : syracuseStep 4666247 = 6999371) B6999371
theorem B2077739 : Blo 920579 2077739 := bstep (se 1 (by rfl) ⟨1558304, by rfl⟩ : syracuseStep 2077739 = 3116609) B3116609
theorem B1553593 : Blo 920579 1553593 := bstep (se 2 (by rfl) ⟨582597, by rfl⟩ : syracuseStep 1553593 = 1165195) B1165195
theorem B3945743 : Blo 920579 3945743 := bstep (se 1 (by rfl) ⟨2959307, by rfl⟩ : syracuseStep 3945743 = 5918615) B5918615
theorem B2340211 : Blo 920579 2340211 := bstep (se 1 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 2340211 = 3510317) B3510317
theorem B996743 : Blo 920579 996743 := bstep (se 1 (by rfl) ⟨747557, by rfl⟩ : syracuseStep 996743 = 1495115) B1495115
theorem B2078099 : Blo 920579 2078099 := bstep (se 1 (by rfl) ⟨1558574, by rfl⟩ : syracuseStep 2078099 = 3117149) B3117149
theorem B72955313 : Blo 920579 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B2078153 : Blo 920579 2078153 := bstep (se 2 (by rfl) ⟨779307, by rfl⟩ : syracuseStep 2078153 = 1558615) B1558615
theorem B1750663 : Blo 920579 1750663 := bstep (se 1 (by rfl) ⟨1312997, by rfl⟩ : syracuseStep 1750663 = 2625995) B2625995
theorem B1554295 : Blo 920579 1554295 := bstep (se 1 (by rfl) ⟨1165721, by rfl⟩ : syracuseStep 1554295 = 2331443) B2331443
theorem B7878667 : Blo 920579 7878667 := bstep (se 1 (by rfl) ⟨5909000, by rfl⟩ : syracuseStep 7878667 = 11818001) B11818001
theorem B1554491 : Blo 920579 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B2078855 : Blo 920579 2078855 := bstep (se 1 (by rfl) ⟨1559141, by rfl⟩ : syracuseStep 2078855 = 3118283) B3118283
theorem B2079035 : Blo 920579 2079035 := bstep (se 1 (by rfl) ⟨1559276, by rfl⟩ : syracuseStep 2079035 = 3118553) B3118553
theorem B8403335 : Blo 920579 8403335 := bstep (se 1 (by rfl) ⟨6302501, by rfl⟩ : syracuseStep 8403335 = 12605003) B12605003
theorem B2079161 : Blo 920579 2079161 := bstep (se 2 (by rfl) ⟨779685, by rfl⟩ : syracuseStep 2079161 = 1559371) B1559371
theorem B1554889 : Blo 920579 1554889 := bstep (se 2 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 1554889 = 1166167) B1166167
theorem B2800187 : Blo 920579 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B2079503 : Blo 920579 2079503 := bstep (se 1 (by rfl) ⟨1559627, by rfl⟩ : syracuseStep 2079503 = 3119255) B3119255
theorem B2079521 : Blo 920579 2079521 := bstep (se 2 (by rfl) ⟨779820, by rfl⟩ : syracuseStep 2079521 = 1559641) B1559641
theorem B3947399 : Blo 920579 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B4996099 : Blo 920579 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B11811851 : Blo 920579 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B2079863 : Blo 920579 2079863 := bstep (se 1 (by rfl) ⟨1559897, by rfl⟩ : syracuseStep 2079863 = 3119795) B3119795
theorem B1555591 : Blo 920579 1555591 := bstep (se 1 (by rfl) ⟨1166693, by rfl⟩ : syracuseStep 1555591 = 2333387) B2333387
theorem B2080043 : Blo 920579 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B1752455 : Blo 920579 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B5258641 : Blo 920579 5258641 := bstep (se 2 (by rfl) ⟨1971990, by rfl⟩ : syracuseStep 5258641 = 3943981) B3943981
theorem B1556239 : Blo 920579 1556239 := bstep (se 1 (by rfl) ⟨1167179, by rfl⟩ : syracuseStep 1556239 = 2334359) B2334359
theorem B2801441 : Blo 920579 2801441 := bstep (se 2 (by rfl) ⟨1050540, by rfl⟩ : syracuseStep 2801441 = 2101081) B2101081
theorem B4997011 : Blo 920579 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B7880651 : Blo 920579 7880651 := bstep (se 1 (by rfl) ⟨5910488, by rfl⟩ : syracuseStep 7880651 = 11820977) B11820977
theorem B2736413 : Blo 920579 2736413 := bstep (se 3 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 2736413 = 1026155) B1026155
theorem B1556779 : Blo 920579 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B4669811 : Blo 920579 4669811 := bstep (se 1 (by rfl) ⟨3502358, by rfl⟩ : syracuseStep 4669811 = 7004717) B7004717
theorem B1556921 : Blo 920579 1556921 := bstep (se 2 (by rfl) ⟨583845, by rfl⟩ : syracuseStep 1556921 = 1167691) B1167691
theorem B7094749 : Blo 920579 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B3949175 : Blo 920579 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B2212609 : Blo 920579 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B14598947 : Blo 920579 14598947 := bstep (se 1 (by rfl) ⟨10949210, by rfl⟩ : syracuseStep 14598947 = 21898421) B21898421
theorem B2212667 : Blo 920579 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B4670297 : Blo 920579 4670297 := bstep (se 2 (by rfl) ⟨1751361, by rfl⟩ : syracuseStep 4670297 = 3502723) B3502723
theorem B1557623 : Blo 920579 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B1558075 : Blo 920579 1558075 := bstep (se 1 (by rfl) ⟨1168556, by rfl⟩ : syracuseStep 1558075 = 2337113) B2337113
theorem B1558217 : Blo 920579 1558217 := bstep (se 2 (by rfl) ⟨584331, by rfl⟩ : syracuseStep 1558217 = 1168663) B1168663
theorem B5261057 : Blo 920579 5261057 := bstep (se 2 (by rfl) ⟨1972896, by rfl⟩ : syracuseStep 5261057 = 3945793) B3945793
theorem B1754939 : Blo 920579 1754939 := bstep (se 1 (by rfl) ⟨1316204, by rfl⟩ : syracuseStep 1754939 = 2632409) B2632409
theorem B6997913 : Blo 920579 6997913 := bstep (se 2 (by rfl) ⟨2624217, by rfl⟩ : syracuseStep 6997913 = 5248435) B5248435
theorem B7883041 : Blo 920579 7883041 := bstep (se 2 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 7883041 = 5912281) B5912281
theorem B1558919 : Blo 920579 1558919 := bstep (se 1 (by rfl) ⟨1169189, by rfl⟩ : syracuseStep 1558919 = 2338379) B2338379
theorem B22432241 : Blo 920579 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B2214415 : Blo 920579 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B3328573 : Blo 920579 3328573 := bstep (se 3 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 3328573 = 1248215) B1248215
theorem B5065409 : Blo 920579 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B1166071 : Blo 920579 1166071 := bstep (se 1 (by rfl) ⟨874553, by rfl⟩ : syracuseStep 1166071 = 1749107) B1749107
theorem B7490393 : Blo 920579 7490393 := bstep (se 2 (by rfl) ⟨2808897, by rfl⟩ : syracuseStep 7490393 = 5617795) B5617795
theorem B4672403 : Blo 920579 4672403 := bstep (se 1 (by rfl) ⟨3504302, by rfl⟩ : syracuseStep 4672403 = 7008605) B7008605
theorem B1559567 : Blo 920579 1559567 := bstep (se 1 (by rfl) ⟨1169675, by rfl⟩ : syracuseStep 1559567 = 2339351) B2339351
theorem B1166395 : Blo 920579 1166395 := bstep (se 1 (by rfl) ⟨874796, by rfl⟩ : syracuseStep 1166395 = 1749593) B1749593
theorem B5065847 : Blo 920579 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B1560107 : Blo 920579 1560107 := bstep (se 1 (by rfl) ⟨1170080, by rfl⟩ : syracuseStep 1560107 = 2340161) B2340161
theorem B1036039 : Blo 920579 1036039 := bstep (se 1 (by rfl) ⟨777029, by rfl⟩ : syracuseStep 1036039 = 1554059) B1554059
theorem B7491365 : Blo 920579 7491365 := bstep (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) B1404631
theorem B6999857 : Blo 920579 6999857 := bstep (se 2 (by rfl) ⟨2624946, by rfl⟩ : syracuseStep 6999857 = 5249893) B5249893
theorem B5263289 : Blo 920579 5263289 := bstep (se 2 (by rfl) ⟨1973733, by rfl⟩ : syracuseStep 5263289 = 3947467) B3947467
theorem B1036219 : Blo 920579 1036219 := bstep (se 1 (by rfl) ⟨777164, by rfl⟩ : syracuseStep 1036219 = 1554329) B1554329
theorem B1167367 : Blo 920579 1167367 := bstep (se 1 (by rfl) ⟨875525, by rfl⟩ : syracuseStep 1167367 = 1751051) B1751051
theorem B2216251 : Blo 920579 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B1036687 : Blo 920579 1036687 := bstep (se 1 (by rfl) ⟨777515, by rfl⟩ : syracuseStep 1036687 = 1555031) B1555031
theorem B1167787 : Blo 920579 1167787 := bstep (se 1 (by rfl) ⟨875840, by rfl⟩ : syracuseStep 1167787 = 1751681) B1751681
theorem B2249227 : Blo 920579 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1168015 : Blo 920579 1168015 := bstep (se 1 (by rfl) ⟨876011, by rfl⟩ : syracuseStep 1168015 = 1752023) B1752023
theorem B8409905 : Blo 920579 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B1037191 : Blo 920579 1037191 := bstep (se 1 (by rfl) ⟨777893, by rfl⟩ : syracuseStep 1037191 = 1555787) B1555787
theorem B5919641 : Blo 920579 5919641 := bstep (se 2 (by rfl) ⟨2219865, by rfl⟩ : syracuseStep 5919641 = 4439731) B4439731
theorem B19190789 : Blo 920579 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B1037371 : Blo 920579 1037371 := bstep (se 1 (by rfl) ⟨778028, by rfl⟩ : syracuseStep 1037371 = 1556057) B1556057
theorem B1168759 : Blo 920579 1168759 := bstep (se 1 (by rfl) ⟨876569, by rfl⟩ : syracuseStep 1168759 = 1753139) B1753139
theorem B1037839 : Blo 920579 1037839 := bstep (se 1 (by rfl) ⟨778379, by rfl⟩ : syracuseStep 1037839 = 1556759) B1556759
theorem B10507805 : Blo 920579 10507805 := bstep (se 3 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 10507805 = 3940427) B3940427
theorem B1169083 : Blo 920579 1169083 := bstep (se 1 (by rfl) ⟨876812, by rfl⟩ : syracuseStep 1169083 = 1753625) B1753625
theorem B1201979 : Blo 920579 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B4675481 : Blo 920579 4675481 := bstep (se 2 (by rfl) ⟨1753305, by rfl⟩ : syracuseStep 4675481 = 3506611) B3506611
theorem B1038343 : Blo 920579 1038343 := bstep (se 1 (by rfl) ⟨778757, by rfl⟩ : syracuseStep 1038343 = 1557515) B1557515
theorem B5265431 : Blo 920579 5265431 := bstep (se 1 (by rfl) ⟨3949073, by rfl⟩ : syracuseStep 5265431 = 7898147) B7898147
theorem B1169579 : Blo 920579 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B6641837 : Blo 920579 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B1038523 : Blo 920579 1038523 := bstep (se 1 (by rfl) ⟨778892, by rfl⟩ : syracuseStep 1038523 = 1557785) B1557785
theorem B3496193 : Blo 920579 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B6314273 : Blo 920579 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B4741409 : Blo 920579 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B1661303 : Blo 920579 1661303 := bstep (se 1 (by rfl) ⟨1245977, by rfl⟩ : syracuseStep 1661303 = 2491955) B2491955
theorem B2218529 : Blo 920579 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B1170055 : Blo 920579 1170055 := bstep (se 1 (by rfl) ⟨877541, by rfl⟩ : syracuseStep 1170055 = 1755083) B1755083
theorem B1038991 : Blo 920579 1038991 := bstep (se 1 (by rfl) ⟨779243, by rfl⟩ : syracuseStep 1038991 = 1558487) B1558487
theorem B95836877 : Blo 920579 95836877 := bstep (se 3 (by rfl) ⟨17969414, by rfl⟩ : syracuseStep 95836877 = 35938829) B35938829
theorem B1661843 : Blo 920579 1661843 := bstep (se 1 (by rfl) ⟨1246382, by rfl⟩ : syracuseStep 1661843 = 2492765) B2492765
theorem B1039495 : Blo 920579 1039495 := bstep (se 1 (by rfl) ⟨779621, by rfl⟩ : syracuseStep 1039495 = 1559243) B1559243
theorem B14179643 : Blo 920579 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B1039675 : Blo 920579 1039675 := bstep (se 1 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 1039675 = 1559513) B1559513
theorem B3497363 : Blo 920579 3497363 := bstep (se 1 (by rfl) ⟨2623022, by rfl⟩ : syracuseStep 3497363 = 5246045) B5246045
theorem B2809529 : Blo 920579 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B5922533 : Blo 920579 5922533 := bstep (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) B1110475
theorem B1040143 : Blo 920579 1040143 := bstep (se 1 (by rfl) ⟨780107, by rfl⟩ : syracuseStep 1040143 = 1560215) B1560215
theorem B3497863 : Blo 920579 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B8970263 : Blo 920579 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B1663111 : Blo 920579 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B1663291 : Blo 920579 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B4678073 : Blo 920579 4678073 := bstep (se 2 (by rfl) ⟨1754277, by rfl⟩ : syracuseStep 4678073 = 3508555) B3508555
theorem B14967281 : Blo 920579 14967281 := bstep (se 2 (by rfl) ⟨5612730, by rfl⟩ : syracuseStep 14967281 = 11225461) B11225461
theorem B6644227 : Blo 920579 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B50521157 : Blo 920579 50521157 := bstep (se 4 (by rfl) ⟨4736358, by rfl⟩ : syracuseStep 50521157 = 9472717) B9472717
theorem B1401991 : Blo 920579 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B1402283 : Blo 920579 1402283 := bstep (se 1 (by rfl) ⟨1051712, by rfl⟩ : syracuseStep 1402283 = 2103425) B2103425
theorem B8873651 : Blo 920579 8873651 := bstep (se 1 (by rfl) ⟨6655238, by rfl⟩ : syracuseStep 8873651 = 13310477) B13310477
theorem B4679369 : Blo 920579 4679369 := bstep (se 2 (by rfl) ⟨1754763, by rfl⟩ : syracuseStep 4679369 = 3509527) B3509527
theorem B10512179 : Blo 920579 10512179 := bstep (se 1 (by rfl) ⟨7884134, by rfl⟩ : syracuseStep 10512179 = 15768269) B15768269
theorem B3107105 : Blo 920579 3107105 := bstep (se 2 (by rfl) ⟨1165164, by rfl⟩ : syracuseStep 3107105 = 2330329) B2330329
theorem B1665569 : Blo 920579 1665569 := bstep (se 2 (by rfl) ⟨624588, by rfl⟩ : syracuseStep 1665569 = 1249177) B1249177
theorem B3107699 : Blo 920579 3107699 := bstep (se 1 (by rfl) ⟨2330774, by rfl⟩ : syracuseStep 3107699 = 4661549) B4661549
theorem B7007633 : Blo 920579 7007633 := bstep (se 2 (by rfl) ⟨2627862, by rfl⟩ : syracuseStep 7007633 = 5255725) B5255725
theorem B19951181 : Blo 920579 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B5336833 : Blo 920579 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B7893125 : Blo 920579 7893125 := bstep (se 4 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 7893125 = 1479961) B1479961
theorem B3110291 : Blo 920579 3110291 := bstep (se 1 (by rfl) ⟨2332718, by rfl⟩ : syracuseStep 3110291 = 4665437) B4665437
theorem B3503513 : Blo 920579 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B22410827 : Blo 920579 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B7010063 : Blo 920579 7010063 := bstep (se 1 (by rfl) ⟨5257547, by rfl⟩ : syracuseStep 7010063 = 10515095) B10515095
theorem B7993367 : Blo 920579 7993367 := bstep (se 1 (by rfl) ⟨5995025, by rfl⟩ : syracuseStep 7993367 = 11990051) B11990051
theorem B2488439 : Blo 920579 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B3111695 : Blo 920579 3111695 := bstep (se 1 (by rfl) ⟨2333771, by rfl⟩ : syracuseStep 3111695 = 4667543) B4667543
theorem B2489131 : Blo 920579 2489131 := bstep (se 1 (by rfl) ⟨1866848, by rfl⟩ : syracuseStep 2489131 = 3733697) B3733697
theorem B3111965 : Blo 920579 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B7109869 : Blo 920579 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B8879341 : Blo 920579 8879341 := bstep (se 3 (by rfl) ⟨1664876, by rfl⟩ : syracuseStep 8879341 = 3329753) B3329753
theorem B1244873 : Blo 920579 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B3113207 : Blo 920579 3113207 := bstep (se 1 (by rfl) ⟨2334905, by rfl⟩ : syracuseStep 3113207 = 4669811) B4669811
theorem B4260107 : Blo 920579 4260107 := bstep (se 1 (by rfl) ⟨3195080, by rfl⟩ : syracuseStep 4260107 = 6390161) B6390161
theorem B9732631 : Blo 920579 9732631 := bstep (se 1 (by rfl) ⟨7299473, by rfl⟩ : syracuseStep 9732631 = 14598947) B14598947
theorem B3932705 : Blo 920579 3932705 := bstep (se 2 (by rfl) ⟨1474764, by rfl⟩ : syracuseStep 3932705 = 2949529) B2949529
theorem B2949671 : Blo 920579 2949671 := bstep (se 1 (by rfl) ⟨2212253, by rfl⟩ : syracuseStep 2949671 = 4424507) B4424507
theorem B1475111 : Blo 920579 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B3113531 : Blo 920579 3113531 := bstep (se 1 (by rfl) ⟨2335148, by rfl⟩ : syracuseStep 3113531 = 4670297) B4670297
theorem B22413941 : Blo 920579 22413941 := bstep (se 5 (by rfl) ⟨1050653, by rfl⟩ : syracuseStep 22413941 = 2101307) B2101307
theorem B3113801 : Blo 920579 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B2622395 : Blo 920579 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B1246171 : Blo 920579 1246171 := bstep (se 1 (by rfl) ⟨934628, by rfl⟩ : syracuseStep 1246171 = 1869257) B1869257
theorem B2950145 : Blo 920579 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1967275 : Blo 920579 1967275 := bstep (se 1 (by rfl) ⟨1475456, by rfl⟩ : syracuseStep 1967275 = 2950913) B2950913
theorem B3507371 : Blo 920579 3507371 := bstep (se 1 (by rfl) ⟨2630528, by rfl⟩ : syracuseStep 3507371 = 5261057) B5261057
theorem B39912749 : Blo 920579 39912749 := bstep (se 3 (by rfl) ⟨7483640, by rfl⟩ : syracuseStep 39912749 = 14967281) B14967281
theorem B7865819 : Blo 920579 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B10487393 : Blo 920579 10487393 := bstep (se 2 (by rfl) ⟨3932772, by rfl⟩ : syracuseStep 10487393 = 7865545) B7865545
theorem B3376939 : Blo 920579 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B2492255 : Blo 920579 2492255 := bstep (se 1 (by rfl) ⟨1869191, by rfl⟩ : syracuseStep 2492255 = 3738383) B3738383
theorem B3114935 : Blo 920579 3114935 := bstep (se 1 (by rfl) ⟨2336201, by rfl⟩ : syracuseStep 3114935 = 4672403) B4672403
theorem B7014437 : Blo 920579 7014437 := bstep (se 4 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 7014437 = 1315207) B1315207
theorem B3377231 : Blo 920579 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B3508541 : Blo 920579 3508541 := bstep (se 3 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 3508541 = 1315703) B1315703
theorem B3115529 : Blo 920579 3115529 := bstep (se 2 (by rfl) ⟨1168323, by rfl⟩ : syracuseStep 3115529 = 2336647) B2336647
theorem B3508859 : Blo 920579 3508859 := bstep (se 1 (by rfl) ⟨2631644, by rfl⟩ : syracuseStep 3508859 = 5263289) B5263289
theorem B2493143 : Blo 920579 2493143 := bstep (se 1 (by rfl) ⟨1869857, by rfl⟩ : syracuseStep 2493143 = 3739715) B3739715
theorem B11995877 : Blo 920579 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B3935233 : Blo 920579 3935233 := bstep (se 2 (by rfl) ⟨1475712, by rfl⟩ : syracuseStep 3935233 = 2951425) B2951425
theorem B920615 : Blo 920579 920615 := bstep (se 1 (by rfl) ⟨690461, by rfl⟩ : syracuseStep 920615 = 1380923) B1380923
theorem B920655 : Blo 920579 920655 := bstep (se 1 (by rfl) ⟨690491, by rfl⟩ : syracuseStep 920655 = 1380983) B1380983
theorem B920671 : Blo 920579 920671 := bstep (se 1 (by rfl) ⟨690503, by rfl⟩ : syracuseStep 920671 = 1381007) B1381007
theorem B920699 : Blo 920579 920699 := bstep (se 1 (by rfl) ⟨690524, by rfl⟩ : syracuseStep 920699 = 1381049) B1381049
theorem B920751 : Blo 920579 920751 := bstep (se 1 (by rfl) ⟨690563, by rfl⟩ : syracuseStep 920751 = 1381127) B1381127
theorem B920775 : Blo 920579 920775 := bstep (se 1 (by rfl) ⟨690581, by rfl⟩ : syracuseStep 920775 = 1381163) B1381163
theorem B5606603 : Blo 920579 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B920795 : Blo 920579 920795 := bstep (se 1 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 920795 = 1381193) B1381193
theorem B920871 : Blo 920579 920871 := bstep (se 1 (by rfl) ⟨690653, by rfl⟩ : syracuseStep 920871 = 1381307) B1381307
theorem B920911 : Blo 920579 920911 := bstep (se 1 (by rfl) ⟨690683, by rfl⟩ : syracuseStep 920911 = 1381367) B1381367
theorem B920927 : Blo 920579 920927 := bstep (se 1 (by rfl) ⟨690695, by rfl⟩ : syracuseStep 920927 = 1381391) B1381391
theorem B2952553 : Blo 920579 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B3116393 : Blo 920579 3116393 := bstep (se 2 (by rfl) ⟨1168647, by rfl⟩ : syracuseStep 3116393 = 2337295) B2337295
theorem B920955 : Blo 920579 920955 := bstep (se 1 (by rfl) ⟨690716, by rfl⟩ : syracuseStep 920955 = 1381433) B1381433
theorem B921007 : Blo 920579 921007 := bstep (se 1 (by rfl) ⟨690755, by rfl⟩ : syracuseStep 921007 = 1381511) B1381511
theorem B921031 : Blo 920579 921031 := bstep (se 1 (by rfl) ⟨690773, by rfl⟩ : syracuseStep 921031 = 1381547) B1381547
theorem B921051 : Blo 920579 921051 := bstep (se 1 (by rfl) ⟨690788, by rfl⟩ : syracuseStep 921051 = 1381577) B1381577
theorem B921127 : Blo 920579 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B921167 : Blo 920579 921167 := bstep (se 1 (by rfl) ⟨690875, by rfl⟩ : syracuseStep 921167 = 1381751) B1381751
theorem B921183 : Blo 920579 921183 := bstep (se 1 (by rfl) ⟨690887, by rfl⟩ : syracuseStep 921183 = 1381775) B1381775
theorem B921211 : Blo 920579 921211 := bstep (se 1 (by rfl) ⟨690908, by rfl⟩ : syracuseStep 921211 = 1381817) B1381817
theorem B986747 : Blo 920579 986747 := bstep (se 1 (by rfl) ⟨740060, by rfl⟩ : syracuseStep 986747 = 1480121) B1480121
theorem B921263 : Blo 920579 921263 := bstep (se 1 (by rfl) ⟨690947, by rfl⟩ : syracuseStep 921263 = 1381895) B1381895
theorem B2657981 : Blo 920579 2657981 := bstep (se 3 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 2657981 = 996743) B996743
theorem B921287 : Blo 920579 921287 := bstep (se 1 (by rfl) ⟨690965, by rfl⟩ : syracuseStep 921287 = 1381931) B1381931
theorem B921307 : Blo 920579 921307 := bstep (se 1 (by rfl) ⟨690980, by rfl⟩ : syracuseStep 921307 = 1381961) B1381961
theorem B3739421 : Blo 920579 3739421 := bstep (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) B1402283
theorem B921383 : Blo 920579 921383 := bstep (se 1 (by rfl) ⟨691037, by rfl⟩ : syracuseStep 921383 = 1382075) B1382075
theorem B2330441 : Blo 920579 2330441 := bstep (se 2 (by rfl) ⟨873915, by rfl⟩ : syracuseStep 2330441 = 1747831) B1747831
theorem B921423 : Blo 920579 921423 := bstep (se 1 (by rfl) ⟨691067, by rfl⟩ : syracuseStep 921423 = 1382135) B1382135
theorem B921439 : Blo 920579 921439 := bstep (se 1 (by rfl) ⟨691079, by rfl⟩ : syracuseStep 921439 = 1382159) B1382159
theorem B7868279 : Blo 920579 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B921467 : Blo 920579 921467 := bstep (se 1 (by rfl) ⟨691100, by rfl⟩ : syracuseStep 921467 = 1382201) B1382201
theorem B921519 : Blo 920579 921519 := bstep (se 1 (by rfl) ⟨691139, by rfl⟩ : syracuseStep 921519 = 1382279) B1382279
theorem B1970095 : Blo 920579 1970095 := bstep (se 1 (by rfl) ⟨1477571, by rfl⟩ : syracuseStep 1970095 = 2955143) B2955143
theorem B3116987 : Blo 920579 3116987 := bstep (se 1 (by rfl) ⟨2337740, by rfl⟩ : syracuseStep 3116987 = 4675481) B4675481
theorem B921543 : Blo 920579 921543 := bstep (se 1 (by rfl) ⟨691157, by rfl⟩ : syracuseStep 921543 = 1382315) B1382315
theorem B921563 : Blo 920579 921563 := bstep (se 1 (by rfl) ⟨691172, by rfl⟩ : syracuseStep 921563 = 1382345) B1382345
theorem B3510287 : Blo 920579 3510287 := bstep (se 1 (by rfl) ⟨2632715, by rfl⟩ : syracuseStep 3510287 = 5265431) B5265431
theorem B921639 : Blo 920579 921639 := bstep (se 1 (by rfl) ⟨691229, by rfl⟩ : syracuseStep 921639 = 1382459) B1382459
theorem B921679 : Blo 920579 921679 := bstep (se 1 (by rfl) ⟨691259, by rfl⟩ : syracuseStep 921679 = 1382519) B1382519
theorem B921695 : Blo 920579 921695 := bstep (se 1 (by rfl) ⟨691271, by rfl⟩ : syracuseStep 921695 = 1382543) B1382543
theorem B4427891 : Blo 920579 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B921723 : Blo 920579 921723 := bstep (se 1 (by rfl) ⟨691292, by rfl⟩ : syracuseStep 921723 = 1382585) B1382585
theorem B2330795 : Blo 920579 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B921775 : Blo 920579 921775 := bstep (se 1 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 921775 = 1382663) B1382663
theorem B921799 : Blo 920579 921799 := bstep (se 1 (by rfl) ⟨691349, by rfl⟩ : syracuseStep 921799 = 1382699) B1382699
theorem B921819 : Blo 920579 921819 := bstep (se 1 (by rfl) ⟨691364, by rfl⟩ : syracuseStep 921819 = 1382729) B1382729
theorem B921895 : Blo 920579 921895 := bstep (se 1 (by rfl) ⟨691421, by rfl⟩ : syracuseStep 921895 = 1382843) B1382843
theorem B921935 : Blo 920579 921935 := bstep (se 1 (by rfl) ⟨691451, by rfl⟩ : syracuseStep 921935 = 1382903) B1382903
theorem B921951 : Blo 920579 921951 := bstep (se 1 (by rfl) ⟨691463, by rfl⟩ : syracuseStep 921951 = 1382927) B1382927
theorem B921979 : Blo 920579 921979 := bstep (se 1 (by rfl) ⟨691484, by rfl⟩ : syracuseStep 921979 = 1382969) B1382969
theorem B922031 : Blo 920579 922031 := bstep (se 1 (by rfl) ⟨691523, by rfl⟩ : syracuseStep 922031 = 1383047) B1383047
theorem B922055 : Blo 920579 922055 := bstep (se 1 (by rfl) ⟨691541, by rfl⟩ : syracuseStep 922055 = 1383083) B1383083
theorem B922075 : Blo 920579 922075 := bstep (se 1 (by rfl) ⟨691556, by rfl⟩ : syracuseStep 922075 = 1383113) B1383113
theorem B922151 : Blo 920579 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B922191 : Blo 920579 922191 := bstep (se 1 (by rfl) ⟨691643, by rfl⟩ : syracuseStep 922191 = 1383287) B1383287
theorem B922207 : Blo 920579 922207 := bstep (se 1 (by rfl) ⟨691655, by rfl⟩ : syracuseStep 922207 = 1383311) B1383311
theorem B922235 : Blo 920579 922235 := bstep (se 1 (by rfl) ⟨691676, by rfl⟩ : syracuseStep 922235 = 1383353) B1383353
theorem B922287 : Blo 920579 922287 := bstep (se 1 (by rfl) ⟨691715, by rfl⟩ : syracuseStep 922287 = 1383431) B1383431
theorem B922311 : Blo 920579 922311 := bstep (se 1 (by rfl) ⟨691733, by rfl⟩ : syracuseStep 922311 = 1383467) B1383467
theorem B922331 : Blo 920579 922331 := bstep (se 1 (by rfl) ⟨691748, by rfl⟩ : syracuseStep 922331 = 1383497) B1383497
theorem B922407 : Blo 920579 922407 := bstep (se 1 (by rfl) ⟨691805, by rfl⟩ : syracuseStep 922407 = 1383611) B1383611
theorem B17699633 : Blo 920579 17699633 := bstep (se 2 (by rfl) ⟨6637362, by rfl⟩ : syracuseStep 17699633 = 13274725) B13274725
theorem B922447 : Blo 920579 922447 := bstep (se 1 (by rfl) ⟨691835, by rfl⟩ : syracuseStep 922447 = 1383671) B1383671
theorem B922463 : Blo 920579 922463 := bstep (se 1 (by rfl) ⟨691847, by rfl⟩ : syracuseStep 922463 = 1383695) B1383695
theorem B922491 : Blo 920579 922491 := bstep (se 1 (by rfl) ⟨691868, by rfl⟩ : syracuseStep 922491 = 1383737) B1383737
theorem B1381295 : Blo 920579 1381295 := bstep (se 1 (by rfl) ⟨1035971, by rfl⟩ : syracuseStep 1381295 = 2071943) B2071943
theorem B922543 : Blo 920579 922543 := bstep (se 1 (by rfl) ⟨691907, by rfl⟩ : syracuseStep 922543 = 1383815) B1383815
theorem B4330415 : Blo 920579 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B2331575 : Blo 920579 2331575 := bstep (se 1 (by rfl) ⟨1748681, by rfl⟩ : syracuseStep 2331575 = 3497363) B3497363
theorem B922567 : Blo 920579 922567 := bstep (se 1 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 922567 = 1383851) B1383851
theorem B922587 : Blo 920579 922587 := bstep (se 1 (by rfl) ⟨691940, by rfl⟩ : syracuseStep 922587 = 1383881) B1383881
theorem B7115777 : Blo 920579 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B1381385 : Blo 920579 1381385 := bstep (se 2 (by rfl) ⟨518019, by rfl⟩ : syracuseStep 1381385 = 1036039) B1036039
theorem B1381415 : Blo 920579 1381415 := bstep (se 1 (by rfl) ⟨1036061, by rfl⟩ : syracuseStep 1381415 = 2072123) B2072123
theorem B922663 : Blo 920579 922663 := bstep (se 1 (by rfl) ⟨691997, by rfl⟩ : syracuseStep 922663 = 1383995) B1383995
theorem B922703 : Blo 920579 922703 := bstep (se 1 (by rfl) ⟨692027, by rfl⟩ : syracuseStep 922703 = 1384055) B1384055
theorem B922719 : Blo 920579 922719 := bstep (se 1 (by rfl) ⟨692039, by rfl⟩ : syracuseStep 922719 = 1384079) B1384079
theorem B1381499 : Blo 920579 1381499 := bstep (se 1 (by rfl) ⟨1036124, by rfl⟩ : syracuseStep 1381499 = 2072249) B2072249
theorem B922747 : Blo 920579 922747 := bstep (se 1 (by rfl) ⟨692060, by rfl⟩ : syracuseStep 922747 = 1384121) B1384121
theorem B1873019 : Blo 920579 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B922799 : Blo 920579 922799 := bstep (se 1 (by rfl) ⟨692099, by rfl⟩ : syracuseStep 922799 = 1384199) B1384199
theorem B922823 : Blo 920579 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B922843 : Blo 920579 922843 := bstep (se 1 (by rfl) ⟨692132, by rfl⟩ : syracuseStep 922843 = 1384265) B1384265
theorem B1381625 : Blo 920579 1381625 := bstep (se 2 (by rfl) ⟨518109, by rfl⟩ : syracuseStep 1381625 = 1036219) B1036219
theorem B922919 : Blo 920579 922919 := bstep (se 1 (by rfl) ⟨692189, by rfl⟩ : syracuseStep 922919 = 1384379) B1384379
theorem B922959 : Blo 920579 922959 := bstep (se 1 (by rfl) ⟨692219, by rfl⟩ : syracuseStep 922959 = 1384439) B1384439
theorem B1381727 : Blo 920579 1381727 := bstep (se 1 (by rfl) ⟨1036295, by rfl⟩ : syracuseStep 1381727 = 2072591) B2072591
theorem B922975 : Blo 920579 922975 := bstep (se 1 (by rfl) ⟨692231, by rfl⟩ : syracuseStep 922975 = 1384463) B1384463
theorem B26645861 : Blo 920579 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B1381739 : Blo 920579 1381739 := bstep (se 1 (by rfl) ⟨1036304, by rfl⟩ : syracuseStep 1381739 = 2072609) B2072609
theorem B923003 : Blo 920579 923003 := bstep (se 1 (by rfl) ⟨692252, by rfl⟩ : syracuseStep 923003 = 1384505) B1384505
theorem B3937679 : Blo 920579 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B923055 : Blo 920579 923055 := bstep (se 1 (by rfl) ⟨692291, by rfl⟩ : syracuseStep 923055 = 1384583) B1384583
theorem B923079 : Blo 920579 923079 := bstep (se 1 (by rfl) ⟨692309, by rfl⟩ : syracuseStep 923079 = 1384619) B1384619
theorem B923099 : Blo 920579 923099 := bstep (se 1 (by rfl) ⟨692324, by rfl⟩ : syracuseStep 923099 = 1384649) B1384649
theorem B3741223 : Blo 920579 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B923175 : Blo 920579 923175 := bstep (se 1 (by rfl) ⟨692381, by rfl⟩ : syracuseStep 923175 = 1384763) B1384763
theorem B1381967 : Blo 920579 1381967 := bstep (se 1 (by rfl) ⟨1036475, by rfl⟩ : syracuseStep 1381967 = 2072951) B2072951
theorem B923215 : Blo 920579 923215 := bstep (se 1 (by rfl) ⟨692411, by rfl⟩ : syracuseStep 923215 = 1384823) B1384823
theorem B923231 : Blo 920579 923231 := bstep (se 1 (by rfl) ⟨692423, by rfl⟩ : syracuseStep 923231 = 1384847) B1384847
theorem B923259 : Blo 920579 923259 := bstep (se 1 (by rfl) ⟨692444, by rfl⟩ : syracuseStep 923259 = 1384889) B1384889
theorem B3118715 : Blo 920579 3118715 := bstep (se 1 (by rfl) ⟨2339036, by rfl⟩ : syracuseStep 3118715 = 4678073) B4678073
theorem B56694421 : Blo 920579 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B923311 : Blo 920579 923311 := bstep (se 1 (by rfl) ⟨692483, by rfl⟩ : syracuseStep 923311 = 1384967) B1384967
theorem B1382087 : Blo 920579 1382087 := bstep (se 1 (by rfl) ⟨1036565, by rfl⟩ : syracuseStep 1382087 = 2073131) B2073131
theorem B923335 : Blo 920579 923335 := bstep (se 1 (by rfl) ⟨692501, by rfl⟩ : syracuseStep 923335 = 1385003) B1385003
theorem B923355 : Blo 920579 923355 := bstep (se 1 (by rfl) ⟨692516, by rfl⟩ : syracuseStep 923355 = 1385033) B1385033
theorem B3118877 : Blo 920579 3118877 := bstep (se 3 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 3118877 = 1169579) B1169579
theorem B923431 : Blo 920579 923431 := bstep (se 1 (by rfl) ⟨692573, by rfl⟩ : syracuseStep 923431 = 1385147) B1385147
theorem B923471 : Blo 920579 923471 := bstep (se 1 (by rfl) ⟨692603, by rfl⟩ : syracuseStep 923471 = 1385207) B1385207
theorem B923487 : Blo 920579 923487 := bstep (se 1 (by rfl) ⟨692615, by rfl⟩ : syracuseStep 923487 = 1385231) B1385231
theorem B1382249 : Blo 920579 1382249 := bstep (se 2 (by rfl) ⟨518343, by rfl⟩ : syracuseStep 1382249 = 1036687) B1036687
theorem B923515 : Blo 920579 923515 := bstep (se 1 (by rfl) ⟨692636, by rfl⟩ : syracuseStep 923515 = 1385273) B1385273
theorem B2332577 : Blo 920579 2332577 := bstep (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) B1749433
theorem B923567 : Blo 920579 923567 := bstep (se 1 (by rfl) ⟨692675, by rfl⟩ : syracuseStep 923567 = 1385351) B1385351
theorem B3151799 : Blo 920579 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B1382327 : Blo 920579 1382327 := bstep (se 1 (by rfl) ⟨1036745, by rfl⟩ : syracuseStep 1382327 = 2073491) B2073491
theorem B5248961 : Blo 920579 5248961 := bstep (se 2 (by rfl) ⟨1968360, by rfl⟩ : syracuseStep 5248961 = 3936721) B3936721
theorem B923591 : Blo 920579 923591 := bstep (se 1 (by rfl) ⟨692693, by rfl⟩ : syracuseStep 923591 = 1385387) B1385387
theorem B1382363 : Blo 920579 1382363 := bstep (se 1 (by rfl) ⟨1036772, by rfl⟩ : syracuseStep 1382363 = 2073545) B2073545
theorem B923611 : Blo 920579 923611 := bstep (se 1 (by rfl) ⟨692708, by rfl⟩ : syracuseStep 923611 = 1385417) B1385417
theorem B7477285 : Blo 920579 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B923687 : Blo 920579 923687 := bstep (se 1 (by rfl) ⟨692765, by rfl⟩ : syracuseStep 923687 = 1385531) B1385531
theorem B923727 : Blo 920579 923727 := bstep (se 1 (by rfl) ⟨692795, by rfl⟩ : syracuseStep 923727 = 1385591) B1385591
theorem B923743 : Blo 920579 923743 := bstep (se 1 (by rfl) ⟨692807, by rfl⟩ : syracuseStep 923743 = 1385615) B1385615
theorem B923771 : Blo 920579 923771 := bstep (se 1 (by rfl) ⟨692828, by rfl⟩ : syracuseStep 923771 = 1385657) B1385657
theorem B923823 : Blo 920579 923823 := bstep (se 1 (by rfl) ⟨692867, by rfl⟩ : syracuseStep 923823 = 1385735) B1385735
theorem B923847 : Blo 920579 923847 := bstep (se 1 (by rfl) ⟨692885, by rfl⟩ : syracuseStep 923847 = 1385771) B1385771
theorem B923867 : Blo 920579 923867 := bstep (se 1 (by rfl) ⟨692900, by rfl⟩ : syracuseStep 923867 = 1385801) B1385801
theorem B923943 : Blo 920579 923943 := bstep (se 1 (by rfl) ⟨692957, by rfl⟩ : syracuseStep 923943 = 1385915) B1385915
theorem B923983 : Blo 920579 923983 := bstep (se 1 (by rfl) ⟨692987, by rfl⟩ : syracuseStep 923983 = 1385975) B1385975
theorem B923999 : Blo 920579 923999 := bstep (se 1 (by rfl) ⟨692999, by rfl⟩ : syracuseStep 923999 = 1385999) B1385999
theorem B2333033 : Blo 920579 2333033 := bstep (se 2 (by rfl) ⟨874887, by rfl⟩ : syracuseStep 2333033 = 1749775) B1749775
theorem B924027 : Blo 920579 924027 := bstep (se 1 (by rfl) ⟨693020, by rfl⟩ : syracuseStep 924027 = 1386041) B1386041
theorem B1382831 : Blo 920579 1382831 := bstep (se 1 (by rfl) ⟨1037123, by rfl⟩ : syracuseStep 1382831 = 2074247) B2074247
theorem B924079 : Blo 920579 924079 := bstep (se 1 (by rfl) ⟨693059, by rfl⟩ : syracuseStep 924079 = 1386119) B1386119
theorem B924103 : Blo 920579 924103 := bstep (se 1 (by rfl) ⟨693077, by rfl⟩ : syracuseStep 924103 = 1386155) B1386155
theorem B924123 : Blo 920579 924123 := bstep (se 1 (by rfl) ⟨693092, by rfl⟩ : syracuseStep 924123 = 1386185) B1386185
theorem B3119579 : Blo 920579 3119579 := bstep (se 1 (by rfl) ⟨2339684, by rfl⟩ : syracuseStep 3119579 = 4679369) B4679369
theorem B1382921 : Blo 920579 1382921 := bstep (se 2 (by rfl) ⟨518595, by rfl⟩ : syracuseStep 1382921 = 1037191) B1037191
theorem B1382951 : Blo 920579 1382951 := bstep (se 1 (by rfl) ⟨1037213, by rfl⟩ : syracuseStep 1382951 = 2074427) B2074427
theorem B924199 : Blo 920579 924199 := bstep (se 1 (by rfl) ⟨693149, by rfl⟩ : syracuseStep 924199 = 1386299) B1386299
theorem B924239 : Blo 920579 924239 := bstep (se 1 (by rfl) ⟨693179, by rfl⟩ : syracuseStep 924239 = 1386359) B1386359
theorem B924255 : Blo 920579 924255 := bstep (se 1 (by rfl) ⟨693191, by rfl⟩ : syracuseStep 924255 = 1386383) B1386383
theorem B1383035 : Blo 920579 1383035 := bstep (se 1 (by rfl) ⟨1037276, by rfl⟩ : syracuseStep 1383035 = 2074553) B2074553
theorem B924283 : Blo 920579 924283 := bstep (se 1 (by rfl) ⟨693212, by rfl⟩ : syracuseStep 924283 = 1386425) B1386425
theorem B924335 : Blo 920579 924335 := bstep (se 1 (by rfl) ⟨693251, by rfl⟩ : syracuseStep 924335 = 1386503) B1386503
theorem B924359 : Blo 920579 924359 := bstep (se 1 (by rfl) ⟨693269, by rfl⟩ : syracuseStep 924359 = 1386539) B1386539
theorem B924379 : Blo 920579 924379 := bstep (se 1 (by rfl) ⟨693284, by rfl⟩ : syracuseStep 924379 = 1386569) B1386569
theorem B1383161 : Blo 920579 1383161 := bstep (se 2 (by rfl) ⟨518685, by rfl⟩ : syracuseStep 1383161 = 1037371) B1037371
theorem B924455 : Blo 920579 924455 := bstep (se 1 (by rfl) ⟨693341, by rfl⟩ : syracuseStep 924455 = 1386683) B1386683
theorem B924495 : Blo 920579 924495 := bstep (se 1 (by rfl) ⟨693371, by rfl⟩ : syracuseStep 924495 = 1386743) B1386743
theorem B1383263 : Blo 920579 1383263 := bstep (se 1 (by rfl) ⟨1037447, by rfl⟩ : syracuseStep 1383263 = 2074895) B2074895
theorem B924511 : Blo 920579 924511 := bstep (se 1 (by rfl) ⟨693383, by rfl⟩ : syracuseStep 924511 = 1386767) B1386767
theorem B2071403 : Blo 920579 2071403 := bstep (se 1 (by rfl) ⟨1553552, by rfl⟩ : syracuseStep 2071403 = 3107105) B3107105
theorem B1383275 : Blo 920579 1383275 := bstep (se 1 (by rfl) ⟨1037456, by rfl⟩ : syracuseStep 1383275 = 2074913) B2074913
theorem B924539 : Blo 920579 924539 := bstep (se 1 (by rfl) ⟨693404, by rfl⟩ : syracuseStep 924539 = 1386809) B1386809
theorem B2071457 : Blo 920579 2071457 := bstep (se 2 (by rfl) ⟨776796, by rfl⟩ : syracuseStep 2071457 = 1553593) B1553593
theorem B1973153 : Blo 920579 1973153 := bstep (se 2 (by rfl) ⟨739932, by rfl⟩ : syracuseStep 1973153 = 1479865) B1479865
theorem B2104339 : Blo 920579 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B1383503 : Blo 920579 1383503 := bstep (se 1 (by rfl) ⟨1037627, by rfl⟩ : syracuseStep 1383503 = 2075255) B2075255
theorem B3120281 : Blo 920579 3120281 := bstep (se 2 (by rfl) ⟨1170105, by rfl⟩ : syracuseStep 3120281 = 2340211) B2340211
theorem B1383623 : Blo 920579 1383623 := bstep (se 1 (by rfl) ⟨1037717, by rfl⟩ : syracuseStep 1383623 = 2075435) B2075435
theorem B2071799 : Blo 920579 2071799 := bstep (se 1 (by rfl) ⟨1553849, by rfl⟩ : syracuseStep 2071799 = 3107699) B3107699
theorem B1383785 : Blo 920579 1383785 := bstep (se 2 (by rfl) ⟨518919, by rfl⟩ : syracuseStep 1383785 = 1037839) B1037839
theorem B3743119 : Blo 920579 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B1383863 : Blo 920579 1383863 := bstep (se 1 (by rfl) ⟨1037897, by rfl⟩ : syracuseStep 1383863 = 2075795) B2075795
theorem B1383899 : Blo 920579 1383899 := bstep (se 1 (by rfl) ⟨1037924, by rfl⟩ : syracuseStep 1383899 = 2075849) B2075849
theorem B2334217 : Blo 920579 2334217 := bstep (se 2 (by rfl) ⟨875331, by rfl⟩ : syracuseStep 2334217 = 1750663) B1750663
theorem B4431581 : Blo 920579 4431581 := bstep (se 3 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 4431581 = 1661843) B1661843
theorem B7020269 : Blo 920579 7020269 := bstep (se 3 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 7020269 = 2632601) B2632601
theorem B2072393 : Blo 920579 2072393 := bstep (se 2 (by rfl) ⟨777147, by rfl⟩ : syracuseStep 2072393 = 1554295) B1554295
theorem B13311859 : Blo 920579 13311859 := bstep (se 1 (by rfl) ⟨9983894, by rfl⟩ : syracuseStep 13311859 = 19967789) B19967789
theorem B1384367 : Blo 920579 1384367 := bstep (se 1 (by rfl) ⟨1038275, by rfl⟩ : syracuseStep 1384367 = 2076551) B2076551
theorem B1384457 : Blo 920579 1384457 := bstep (se 2 (by rfl) ⟨519171, by rfl⟩ : syracuseStep 1384457 = 1038343) B1038343
theorem B1384487 : Blo 920579 1384487 := bstep (se 1 (by rfl) ⟨1038365, by rfl⟩ : syracuseStep 1384487 = 2076731) B2076731
theorem B1384571 : Blo 920579 1384571 := bstep (se 1 (by rfl) ⟨1038428, by rfl⟩ : syracuseStep 1384571 = 2076857) B2076857
theorem B1384697 : Blo 920579 1384697 := bstep (se 2 (by rfl) ⟨519261, by rfl⟩ : syracuseStep 1384697 = 1038523) B1038523
theorem B1384799 : Blo 920579 1384799 := bstep (se 1 (by rfl) ⟨1038599, by rfl⟩ : syracuseStep 1384799 = 2077199) B2077199
theorem B1384811 : Blo 920579 1384811 := bstep (se 1 (by rfl) ⟨1038608, by rfl⟩ : syracuseStep 1384811 = 2077217) B2077217
theorem B1385039 : Blo 920579 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B2073185 : Blo 920579 2073185 := bstep (se 2 (by rfl) ⟨777444, by rfl⟩ : syracuseStep 2073185 = 1554889) B1554889
theorem B1385159 : Blo 920579 1385159 := bstep (se 1 (by rfl) ⟨1038869, by rfl⟩ : syracuseStep 1385159 = 2077739) B2077739
theorem B2630495 : Blo 920579 2630495 := bstep (se 1 (by rfl) ⟨1972871, by rfl⟩ : syracuseStep 2630495 = 3945743) B3945743
theorem B1385321 : Blo 920579 1385321 := bstep (se 2 (by rfl) ⟨519495, by rfl⟩ : syracuseStep 1385321 = 1038991) B1038991
theorem B2073527 : Blo 920579 2073527 := bstep (se 1 (by rfl) ⟨1555145, by rfl⟩ : syracuseStep 2073527 = 3110291) B3110291
theorem B1385399 : Blo 920579 1385399 := bstep (se 1 (by rfl) ⟨1039049, by rfl⟩ : syracuseStep 1385399 = 2078099) B2078099
theorem B2335675 : Blo 920579 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B48636875 : Blo 920579 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B1385435 : Blo 920579 1385435 := bstep (se 1 (by rfl) ⟨1039076, by rfl⟩ : syracuseStep 1385435 = 2078153) B2078153
theorem B3318841 : Blo 920579 3318841 := bstep (se 2 (by rfl) ⟨1244565, by rfl⟩ : syracuseStep 3318841 = 2489131) B2489131
theorem B1385903 : Blo 920579 1385903 := bstep (se 1 (by rfl) ⟨1039427, by rfl⟩ : syracuseStep 1385903 = 2078855) B2078855
theorem B2074121 : Blo 920579 2074121 := bstep (se 2 (by rfl) ⟨777795, by rfl⟩ : syracuseStep 2074121 = 1555591) B1555591
theorem B1385993 : Blo 920579 1385993 := bstep (se 2 (by rfl) ⟨519747, by rfl⟩ : syracuseStep 1385993 = 1039495) B1039495
theorem B1386023 : Blo 920579 1386023 := bstep (se 1 (by rfl) ⟨1039517, by rfl⟩ : syracuseStep 1386023 = 2079035) B2079035
theorem B1386107 : Blo 920579 1386107 := bstep (se 1 (by rfl) ⟨1039580, by rfl⟩ : syracuseStep 1386107 = 2079161) B2079161
theorem B9479825 : Blo 920579 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B11839121 : Blo 920579 11839121 := bstep (se 2 (by rfl) ⟨4439670, by rfl⟩ : syracuseStep 11839121 = 8879341) B8879341
theorem B1386233 : Blo 920579 1386233 := bstep (se 2 (by rfl) ⟨519837, by rfl⟩ : syracuseStep 1386233 = 1039675) B1039675
theorem B2074463 : Blo 920579 2074463 := bstep (se 1 (by rfl) ⟨1555847, by rfl⟩ : syracuseStep 2074463 = 3111695) B3111695
theorem B1386335 : Blo 920579 1386335 := bstep (se 1 (by rfl) ⟨1039751, by rfl⟩ : syracuseStep 1386335 = 2079503) B2079503
theorem B1386347 : Blo 920579 1386347 := bstep (se 1 (by rfl) ⟨1039760, by rfl⟩ : syracuseStep 1386347 = 2079521) B2079521
theorem B3319661 : Blo 920579 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B2631599 : Blo 920579 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B12167117 : Blo 920579 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B7874567 : Blo 920579 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B2074643 : Blo 920579 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B1386575 : Blo 920579 1386575 := bstep (se 1 (by rfl) ⟨1039931, by rfl⟩ : syracuseStep 1386575 = 2079863) B2079863
theorem B1386695 : Blo 920579 1386695 := bstep (se 1 (by rfl) ⟨1040021, by rfl⟩ : syracuseStep 1386695 = 2080043) B2080043
theorem B2074985 : Blo 920579 2074985 := bstep (se 2 (by rfl) ⟨778119, by rfl⟩ : syracuseStep 2074985 = 1556239) B1556239
theorem B1386857 : Blo 920579 1386857 := bstep (se 2 (by rfl) ⟨520071, by rfl⟩ : syracuseStep 1386857 = 1040143) B1040143
theorem B4663817 : Blo 920579 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B6662681 : Blo 920579 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B5253767 : Blo 920579 5253767 := bstep (se 1 (by rfl) ⟨3940325, by rfl⟩ : syracuseStep 5253767 = 7880651) B7880651
theorem B2075579 : Blo 920579 2075579 := bstep (se 1 (by rfl) ⟨1556684, by rfl⟩ : syracuseStep 2075579 = 3113369) B3113369
theorem B1747975 : Blo 920579 1747975 := bstep (se 1 (by rfl) ⟨1310981, by rfl⟩ : syracuseStep 1747975 = 2621963) B2621963
theorem B2075705 : Blo 920579 2075705 := bstep (se 2 (by rfl) ⟨778389, by rfl⟩ : syracuseStep 2075705 = 1556779) B1556779
theorem B8858969 : Blo 920579 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B10235261 : Blo 920579 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B2076047 : Blo 920579 2076047 := bstep (se 1 (by rfl) ⟨1557035, by rfl⟩ : syracuseStep 2076047 = 3114071) B3114071
theorem B5615021 : Blo 920579 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B2338267 : Blo 920579 2338267 := bstep (se 1 (by rfl) ⟨1753700, by rfl⟩ : syracuseStep 2338267 = 3507401) B3507401
theorem B1748537 : Blo 920579 1748537 := bstep (se 2 (by rfl) ⟨655701, by rfl⟩ : syracuseStep 1748537 = 1311403) B1311403
theorem B6303329 : Blo 920579 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B4206269 : Blo 920579 4206269 := bstep (se 3 (by rfl) ⟨788675, by rfl⟩ : syracuseStep 4206269 = 1577351) B1577351
theorem B2076371 : Blo 920579 2076371 := bstep (se 1 (by rfl) ⟨1557278, by rfl⟩ : syracuseStep 2076371 = 3114557) B3114557
theorem B4665275 : Blo 920579 4665275 := bstep (se 1 (by rfl) ⟨3498956, by rfl⟩ : syracuseStep 4665275 = 6997913) B6997913
theorem B5255225 : Blo 920579 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B2338895 : Blo 920579 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B10531133 : Blo 920579 10531133 := bstep (se 3 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 10531133 = 3949175) B3949175
theorem B14954827 : Blo 920579 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B4993595 : Blo 920579 4993595 := bstep (se 1 (by rfl) ⟨3745196, by rfl⟩ : syracuseStep 4993595 = 7490393) B7490393
theorem B2077307 : Blo 920579 2077307 := bstep (se 1 (by rfl) ⟨1557980, by rfl⟩ : syracuseStep 2077307 = 3115961) B3115961
theorem B2339543 : Blo 920579 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B2077433 : Blo 920579 2077433 := bstep (se 2 (by rfl) ⟨779037, by rfl⟩ : syracuseStep 2077433 = 1558075) B1558075
theorem B3322691 : Blo 920579 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B2077703 : Blo 920579 2077703 := bstep (se 1 (by rfl) ⟨1558277, by rfl⟩ : syracuseStep 2077703 = 3116555) B3116555
theorem B1750025 : Blo 920579 1750025 := bstep (se 2 (by rfl) ⟨656259, by rfl⟩ : syracuseStep 1750025 = 1312519) B1312519
theorem B2077775 : Blo 920579 2077775 := bstep (se 1 (by rfl) ⟨1558331, by rfl⟩ : syracuseStep 2077775 = 3116663) B3116663
theorem B4994243 : Blo 920579 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B4666571 : Blo 920579 4666571 := bstep (se 1 (by rfl) ⟨3499928, by rfl⟩ : syracuseStep 4666571 = 6999857) B6999857
theorem B2078171 : Blo 920579 2078171 := bstep (se 1 (by rfl) ⟨1558628, by rfl⟩ : syracuseStep 2078171 = 3117257) B3117257
theorem B3159737 : Blo 920579 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1554167 : Blo 920579 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B4437827 : Blo 920579 4437827 := bstep (se 1 (by rfl) ⟨3328370, by rfl⟩ : syracuseStep 4437827 = 6656741) B6656741
theorem B1750891 : Blo 920579 1750891 := bstep (se 1 (by rfl) ⟨1313168, by rfl⟩ : syracuseStep 1750891 = 2626337) B2626337
theorem B53262197 : Blo 920579 53262197 := bstep (se 5 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 53262197 = 4993331) B4993331
theorem B2078639 : Blo 920579 2078639 := bstep (se 1 (by rfl) ⟨1558979, by rfl⟩ : syracuseStep 2078639 = 3117959) B3117959
theorem B1750967 : Blo 920579 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B3946427 : Blo 920579 3946427 := bstep (se 1 (by rfl) ⟨2959820, by rfl⟩ : syracuseStep 3946427 = 5919641) B5919641
theorem B12793859 : Blo 920579 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B1554511 : Blo 920579 1554511 := bstep (se 1 (by rfl) ⟨1165883, by rfl⟩ : syracuseStep 1554511 = 2331767) B2331767
theorem B4438097 : Blo 920579 4438097 := bstep (se 2 (by rfl) ⟨1664286, by rfl⟩ : syracuseStep 4438097 = 3328573) B3328573
theorem B2078891 : Blo 920579 2078891 := bstep (se 1 (by rfl) ⟨1559168, by rfl⟩ : syracuseStep 2078891 = 3118337) B3118337
theorem B1554761 : Blo 920579 1554761 := bstep (se 2 (by rfl) ⟨583035, by rfl⟩ : syracuseStep 1554761 = 1166071) B1166071
theorem B1751483 : Blo 920579 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B5257709 : Blo 920579 5257709 := bstep (se 3 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 5257709 = 1971641) B1971641
theorem B4209185 : Blo 920579 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B2079431 : Blo 920579 2079431 := bstep (se 1 (by rfl) ⟨1559573, by rfl⟩ : syracuseStep 2079431 = 3119147) B3119147
theorem B1555193 : Blo 920579 1555193 := bstep (se 2 (by rfl) ⟨583197, by rfl⟩ : syracuseStep 1555193 = 1166395) B1166395
theorem B4209515 : Blo 920579 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B3160939 : Blo 920579 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B1751969 : Blo 920579 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1555375 : Blo 920579 1555375 := bstep (se 1 (by rfl) ⟨1166531, by rfl⟩ : syracuseStep 1555375 = 2333063) B2333063
theorem B1555463 : Blo 920579 1555463 := bstep (se 1 (by rfl) ⟨1166597, by rfl⟩ : syracuseStep 1555463 = 2333195) B2333195
theorem B1752121 : Blo 920579 1752121 := bstep (se 2 (by rfl) ⟨657045, by rfl⟩ : syracuseStep 1752121 = 1314091) B1314091
theorem B6732953 : Blo 920579 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B1555807 : Blo 920579 1555807 := bstep (se 1 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 1555807 = 2333711) B2333711
theorem B1752425 : Blo 920579 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B3325313 : Blo 920579 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B1555895 : Blo 920579 1555895 := bstep (se 1 (by rfl) ⟨1166921, by rfl⟩ : syracuseStep 1555895 = 2333843) B2333843
theorem B9453095 : Blo 920579 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B2080295 : Blo 920579 2080295 := bstep (se 1 (by rfl) ⟨1560221, by rfl⟩ : syracuseStep 2080295 = 3120443) B3120443
theorem B3948355 : Blo 920579 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B3325805 : Blo 920579 3325805 := bstep (se 3 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 3325805 = 1247177) B1247177
theorem B1556489 : Blo 920579 1556489 := bstep (se 2 (by rfl) ⟨583683, by rfl⟩ : syracuseStep 1556489 = 1167367) B1167367
theorem B5980175 : Blo 920579 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1556651 : Blo 920579 1556651 := bstep (se 1 (by rfl) ⟨1167488, by rfl⟩ : syracuseStep 1556651 = 2334977) B2334977
theorem B6635837 : Blo 920579 6635837 := bstep (se 3 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 6635837 = 2488439) B2488439
theorem B2212339 : Blo 920579 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B26624537 : Blo 920579 26624537 := bstep (se 2 (by rfl) ⟨9984201, by rfl⟩ : syracuseStep 26624537 = 19968403) B19968403
theorem B1557049 : Blo 920579 1557049 := bstep (se 2 (by rfl) ⟨583893, by rfl⟩ : syracuseStep 1557049 = 1167787) B1167787
theorem B1557191 : Blo 920579 1557191 := bstep (se 1 (by rfl) ⟨1167893, by rfl⟩ : syracuseStep 1557191 = 2335787) B2335787
theorem B1557353 : Blo 920579 1557353 := bstep (se 2 (by rfl) ⟨584007, by rfl⟩ : syracuseStep 1557353 = 1168015) B1168015
theorem B14992451 : Blo 920579 14992451 := bstep (se 1 (by rfl) ⟨11244338, by rfl⟩ : syracuseStep 14992451 = 22488677) B22488677
theorem B5915767 : Blo 920579 5915767 := bstep (se 1 (by rfl) ⟨4436825, by rfl⟩ : syracuseStep 5915767 = 8873651) B8873651
theorem B6309017 : Blo 920579 6309017 := bstep (se 2 (by rfl) ⟨2365881, by rfl⟩ : syracuseStep 6309017 = 4731763) B4731763
theorem B1557751 : Blo 920579 1557751 := bstep (se 1 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 1557751 = 2336627) B2336627
theorem B5916077 : Blo 920579 5916077 := bstep (se 3 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 5916077 = 2218529) B2218529
theorem B4441517 : Blo 920579 4441517 := bstep (se 3 (by rfl) ⟨832784, by rfl⟩ : syracuseStep 4441517 = 1665569) B1665569
theorem B1754551 : Blo 920579 1754551 := bstep (se 1 (by rfl) ⟨1315913, by rfl⟩ : syracuseStep 1754551 = 2631827) B2631827
theorem B1557947 : Blo 920579 1557947 := bstep (se 1 (by rfl) ⟨1168460, by rfl⟩ : syracuseStep 1557947 = 2336921) B2336921
theorem B1558055 : Blo 920579 1558055 := bstep (se 1 (by rfl) ⟨1168541, by rfl⟩ : syracuseStep 1558055 = 2337083) B2337083
theorem B1558345 : Blo 920579 1558345 := bstep (se 2 (by rfl) ⟨584379, by rfl⟩ : syracuseStep 1558345 = 1168759) B1168759
theorem B1558379 : Blo 920579 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B7096349 : Blo 920579 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B1558777 : Blo 920579 1558777 := bstep (se 2 (by rfl) ⟨584541, by rfl⟩ : syracuseStep 1558777 = 1169083) B1169083
theorem B4671755 : Blo 920579 4671755 := bstep (se 1 (by rfl) ⟨3503816, by rfl⟩ : syracuseStep 4671755 = 7007633) B7007633
theorem B1559047 : Blo 920579 1559047 := bstep (se 1 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 1559047 = 2338571) B2338571
theorem B10504889 : Blo 920579 10504889 := bstep (se 2 (by rfl) ⟨3939333, by rfl⟩ : syracuseStep 10504889 = 7878667) B7878667
theorem B5262083 : Blo 920579 5262083 := bstep (se 1 (by rfl) ⟨3946562, by rfl⟩ : syracuseStep 5262083 = 7893125) B7893125
theorem B3328877 : Blo 920579 3328877 := bstep (se 3 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 3328877 = 1248329) B1248329
theorem B2214839 : Blo 920579 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B1559479 : Blo 920579 1559479 := bstep (se 1 (by rfl) ⟨1169609, by rfl⟩ : syracuseStep 1559479 = 2339219) B2339219
theorem B1559675 : Blo 920579 1559675 := bstep (se 1 (by rfl) ⟨1169756, by rfl⟩ : syracuseStep 1559675 = 2339513) B2339513
theorem B1821895 : Blo 920579 1821895 := bstep (se 1 (by rfl) ⟨1366421, by rfl⟩ : syracuseStep 1821895 = 2732843) B2732843
theorem B1560073 : Blo 920579 1560073 := bstep (se 2 (by rfl) ⟨585027, by rfl⟩ : syracuseStep 1560073 = 1170055) B1170055
theorem B4673213 : Blo 920579 4673213 := bstep (se 3 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 4673213 = 1752455) B1752455
theorem B4673375 : Blo 920579 4673375 := bstep (se 1 (by rfl) ⟨3505031, by rfl⟩ : syracuseStep 4673375 = 7010063) B7010063
theorem B5328911 : Blo 920579 5328911 := bstep (se 1 (by rfl) ⟨3996683, by rfl⟩ : syracuseStep 5328911 = 7993367) B7993367
theorem B1036327 : Blo 920579 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B1495289 : Blo 920579 1495289 := bstep (se 2 (by rfl) ⟨560733, by rfl⟩ : syracuseStep 1495289 = 1121467) B1121467
theorem B1660343 : Blo 920579 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B3495433 : Blo 920579 3495433 := bstep (se 2 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 3495433 = 2621575) B2621575
theorem B1824275 : Blo 920579 1824275 := bstep (se 1 (by rfl) ⟨1368206, by rfl⟩ : syracuseStep 1824275 = 2736413) B2736413
theorem B1660495 : Blo 920579 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B1037947 : Blo 920579 1037947 := bstep (se 1 (by rfl) ⟨778460, by rfl⟩ : syracuseStep 1037947 = 1556921) B1556921
theorem B4216519 : Blo 920579 4216519 := bstep (se 1 (by rfl) ⟨3162389, by rfl⟩ : syracuseStep 4216519 = 6324779) B6324779
theorem B2217721 : Blo 920579 2217721 := bstep (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) B1663291
theorem B9459665 : Blo 920579 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B8869925 : Blo 920579 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B1038415 : Blo 920579 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B1038811 : Blo 920579 1038811 := bstep (se 1 (by rfl) ⟨779108, by rfl⟩ : syracuseStep 1038811 = 1558217) B1558217
theorem B4676129 : Blo 920579 4676129 := bstep (se 2 (by rfl) ⟨1753548, by rfl⟩ : syracuseStep 4676129 = 3507097) B3507097
theorem B1169959 : Blo 920579 1169959 := bstep (se 1 (by rfl) ⟨877469, by rfl⟩ : syracuseStep 1169959 = 1754939) B1754939
theorem B23943755 : Blo 920579 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B1039279 : Blo 920579 1039279 := bstep (se 1 (by rfl) ⟨779459, by rfl⟩ : syracuseStep 1039279 = 1558919) B1558919
theorem B1661879 : Blo 920579 1661879 := bstep (se 1 (by rfl) ⟨1246409, by rfl⟩ : syracuseStep 1661879 = 2492819) B2492819
theorem B3496891 : Blo 920579 3496891 := bstep (se 1 (by rfl) ⟨2622668, by rfl⟩ : syracuseStep 3496891 = 5245337) B5245337
theorem B11820005 : Blo 920579 11820005 := bstep (se 4 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 11820005 = 2216251) B2216251
theorem B8871191 : Blo 920579 8871191 := bstep (se 1 (by rfl) ⟨6653393, by rfl⟩ : syracuseStep 8871191 = 13306787) B13306787
theorem B1039711 : Blo 920579 1039711 := bstep (se 1 (by rfl) ⟨779783, by rfl⟩ : syracuseStep 1039711 = 1559567) B1559567
theorem B7003745 : Blo 920579 7003745 := bstep (se 2 (by rfl) ⟨2626404, by rfl⟩ : syracuseStep 7003745 = 5252809) B5252809
theorem B1040071 : Blo 920579 1040071 := bstep (se 1 (by rfl) ⟨780053, by rfl⟩ : syracuseStep 1040071 = 1560107) B1560107
theorem B3497681 : Blo 920579 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B79716149 : Blo 920579 79716149 := bstep (se 5 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 79716149 = 7473389) B7473389
theorem B3498137 : Blo 920579 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B10510721 : Blo 920579 10510721 := bstep (se 2 (by rfl) ⟨3941520, by rfl⟩ : syracuseStep 10510721 = 7883041) B7883041
theorem B78996491 : Blo 920579 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B7005203 : Blo 920579 7005203 := bstep (se 1 (by rfl) ⟨5253902, by rfl⟩ : syracuseStep 7005203 = 10507805) B10507805
theorem B2811037 : Blo 920579 2811037 := bstep (se 3 (by rfl) ⟨527069, by rfl⟩ : syracuseStep 2811037 = 1054139) B1054139
theorem B1664329 : Blo 920579 1664329 := bstep (se 2 (by rfl) ⟨624123, by rfl⟩ : syracuseStep 1664329 = 1248247) B1248247
theorem B13297097 : Blo 920579 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B4679207 : Blo 920579 4679207 := bstep (se 1 (by rfl) ⟨3509405, by rfl⟩ : syracuseStep 4679207 = 7018811) B7018811
theorem B1107535 : Blo 920579 1107535 := bstep (se 1 (by rfl) ⟨830651, by rfl⟩ : syracuseStep 1107535 = 1661303) B1661303
theorem B63891251 : Blo 920579 63891251 := bstep (se 1 (by rfl) ⟨47918438, by rfl⟩ : syracuseStep 63891251 = 95836877) B95836877
theorem B3500111 : Blo 920579 3500111 := bstep (se 1 (by rfl) ⟨2625083, by rfl⟩ : syracuseStep 3500111 = 5250167) B5250167
theorem B3205277 : Blo 920579 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B3500279 : Blo 920579 3500279 := bstep (se 1 (by rfl) ⟨2625209, by rfl⟩ : syracuseStep 3500279 = 5250419) B5250419
theorem B3107159 : Blo 920579 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B7891789 : Blo 920579 7891789 := bstep (se 3 (by rfl) ⟨1479710, by rfl⟩ : syracuseStep 7891789 = 2959421) B2959421
theorem B6646703 : Blo 920579 6646703 := bstep (se 1 (by rfl) ⟨4985027, by rfl⟩ : syracuseStep 6646703 = 9970055) B9970055
theorem B3501251 : Blo 920579 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B33680771 : Blo 920579 33680771 := bstep (se 1 (by rfl) ⟨25260578, by rfl⟩ : syracuseStep 33680771 = 50521157) B50521157
theorem B3108239 : Blo 920579 3108239 := bstep (se 1 (by rfl) ⟨2331179, by rfl⟩ : syracuseStep 3108239 = 4662359) B4662359
theorem B3108563 : Blo 920579 3108563 := bstep (se 1 (by rfl) ⟨2331422, by rfl⟩ : syracuseStep 3108563 = 4662845) B4662845
theorem B7008119 : Blo 920579 7008119 := bstep (se 1 (by rfl) ⟨5256089, by rfl⟩ : syracuseStep 7008119 = 10512179) B10512179
theorem B4550593 : Blo 920579 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B3502237 : Blo 920579 3502237 := bstep (se 3 (by rfl) ⟨656669, by rfl⟩ : syracuseStep 3502237 = 1313339) B1313339
theorem B22475069 : Blo 920579 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B3109751 : Blo 920579 3109751 := bstep (se 1 (by rfl) ⟨2332313, by rfl⟩ : syracuseStep 3109751 = 4664627) B4664627
theorem B13300787 : Blo 920579 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B3109967 : Blo 920579 3109967 := bstep (se 1 (by rfl) ⟨2332475, by rfl⟩ : syracuseStep 3109967 = 4664951) B4664951
theorem B3110345 : Blo 920579 3110345 := bstep (se 2 (by rfl) ⟨1166379, by rfl⟩ : syracuseStep 3110345 = 2332759) B2332759
theorem B3110615 : Blo 920579 3110615 := bstep (se 1 (by rfl) ⟨2332961, by rfl⟩ : syracuseStep 3110615 = 4665923) B4665923
theorem B3110831 : Blo 920579 3110831 := bstep (se 1 (by rfl) ⟨2333123, by rfl⟩ : syracuseStep 3110831 = 4666247) B4666247
theorem B6649933 : Blo 920579 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B14940551 : Blo 920579 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B5602223 : Blo 920579 5602223 := bstep (se 1 (by rfl) ⟨4201667, by rfl⟩ : syracuseStep 5602223 = 8403335) B8403335
theorem B3505153 : Blo 920579 3505153 := bstep (se 2 (by rfl) ⟨1314432, by rfl⟩ : syracuseStep 3505153 = 2628865) B2628865
theorem B1866791 : Blo 920579 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B7011521 : Blo 920579 7011521 := bstep (se 2 (by rfl) ⟨2629320, by rfl⟩ : syracuseStep 7011521 = 5258641) B5258641
theorem B11992541 : Blo 920579 11992541 := bstep (se 3 (by rfl) ⟨2248601, by rfl⟩ : syracuseStep 11992541 = 4497203) B4497203
theorem B3505913 : Blo 920579 3505913 := bstep (se 2 (by rfl) ⟨1314717, by rfl⟩ : syracuseStep 3505913 = 2629435) B2629435
theorem B1867627 : Blo 920579 1867627 := bstep (se 1 (by rfl) ⟨1400720, by rfl⟩ : syracuseStep 1867627 = 2801441) B2801441
theorem B4423891 : Blo 920579 4423891 := bstep (se 1 (by rfl) ⟨3317918, by rfl⟩ : syracuseStep 4423891 = 6635837) B6635837
theorem B2621803 : Blo 920579 2621803 := bstep (se 1 (by rfl) ⟨1966352, by rfl⟩ : syracuseStep 2621803 = 3932705) B3932705
theorem B1966447 : Blo 920579 1966447 := bstep (se 1 (by rfl) ⟨1474835, by rfl⟩ : syracuseStep 1966447 = 2949671) B2949671
theorem B14942627 : Blo 920579 14942627 := bstep (se 1 (by rfl) ⟨11206970, by rfl⟩ : syracuseStep 14942627 = 22413941) B22413941
theorem B2949785 : Blo 920579 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1966763 : Blo 920579 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B12976841 : Blo 920579 12976841 := bstep (se 2 (by rfl) ⟨4866315, by rfl⟩ : syracuseStep 12976841 = 9732631) B9732631
theorem B9994967 : Blo 920579 9994967 := bstep (se 1 (by rfl) ⟨7496225, by rfl⟩ : syracuseStep 9994967 = 14992451) B14992451
theorem B26608499 : Blo 920579 26608499 := bstep (se 1 (by rfl) ⟨19956374, by rfl⟩ : syracuseStep 26608499 = 39912749) B39912749
theorem B5243879 : Blo 920579 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B3114233 : Blo 920579 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B4425121 : Blo 920579 4425121 := bstep (se 2 (by rfl) ⟨1659420, by rfl⟩ : syracuseStep 4425121 = 3318841) B3318841
theorem B3933629 : Blo 920579 3933629 := bstep (se 3 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 3933629 = 1475111) B1475111
theorem B3114503 : Blo 920579 3114503 := bstep (se 1 (by rfl) ⟨2335877, by rfl⟩ : syracuseStep 3114503 = 4671755) B4671755
theorem B2623033 : Blo 920579 2623033 := bstep (se 2 (by rfl) ⟨983637, by rfl⟩ : syracuseStep 2623033 = 1967275) B1967275
theorem B7997251 : Blo 920579 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B3508055 : Blo 920579 3508055 := bstep (se 1 (by rfl) ⟨2631041, by rfl⟩ : syracuseStep 3508055 = 5262083) B5262083
theorem B1476559 : Blo 920579 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B1476713 : Blo 920579 1476713 := bstep (se 2 (by rfl) ⟨553767, by rfl⟩ : syracuseStep 1476713 = 1107535) B1107535
theorem B3737735 : Blo 920579 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B3115475 : Blo 920579 3115475 := bstep (se 1 (by rfl) ⟨2336606, by rfl⟩ : syracuseStep 3115475 = 4673213) B4673213
theorem B2492947 : Blo 920579 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B3115583 : Blo 920579 3115583 := bstep (se 1 (by rfl) ⟨2336687, by rfl⟩ : syracuseStep 3115583 = 4673375) B4673375
theorem B5245519 : Blo 920579 5245519 := bstep (se 1 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 5245519 = 7868279) B7868279
theorem B2951927 : Blo 920579 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B11799755 : Blo 920579 11799755 := bstep (se 1 (by rfl) ⟨8849816, by rfl⟩ : syracuseStep 11799755 = 17699633) B17699633
theorem B920863 : Blo 920579 920863 := bstep (se 1 (by rfl) ⟨690647, by rfl⟩ : syracuseStep 920863 = 1381295) B1381295
theorem B2886943 : Blo 920579 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B920923 : Blo 920579 920923 := bstep (se 1 (by rfl) ⟨690692, by rfl⟩ : syracuseStep 920923 = 1381385) B1381385
theorem B920943 : Blo 920579 920943 := bstep (se 1 (by rfl) ⟨690707, by rfl⟩ : syracuseStep 920943 = 1381415) B1381415
theorem B920999 : Blo 920579 920999 := bstep (se 1 (by rfl) ⟨690749, by rfl⟩ : syracuseStep 920999 = 1381499) B1381499
theorem B1248679 : Blo 920579 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B921083 : Blo 920579 921083 := bstep (se 1 (by rfl) ⟨690812, by rfl⟩ : syracuseStep 921083 = 1381625) B1381625
theorem B921151 : Blo 920579 921151 := bstep (se 1 (by rfl) ⟨690863, by rfl⟩ : syracuseStep 921151 = 1381727) B1381727
theorem B17763907 : Blo 920579 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B921159 : Blo 920579 921159 := bstep (se 1 (by rfl) ⟨690869, by rfl⟩ : syracuseStep 921159 = 1381739) B1381739
theorem B2625119 : Blo 920579 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B1216183 : Blo 920579 1216183 := bstep (se 1 (by rfl) ⟨912137, by rfl⟩ : syracuseStep 1216183 = 1824275) B1824275
theorem B921311 : Blo 920579 921311 := bstep (se 1 (by rfl) ⟨690983, by rfl⟩ : syracuseStep 921311 = 1381967) B1381967
theorem B10522385 : Blo 920579 10522385 := bstep (se 2 (by rfl) ⟨3945894, by rfl⟩ : syracuseStep 10522385 = 7891789) B7891789
theorem B921391 : Blo 920579 921391 := bstep (se 1 (by rfl) ⟨691043, by rfl⟩ : syracuseStep 921391 = 1382087) B1382087
theorem B921499 : Blo 920579 921499 := bstep (se 1 (by rfl) ⟨691124, by rfl⟩ : syracuseStep 921499 = 1382249) B1382249
theorem B2101199 : Blo 920579 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B921551 : Blo 920579 921551 := bstep (se 1 (by rfl) ⟨691163, by rfl⟩ : syracuseStep 921551 = 1382327) B1382327
theorem B921575 : Blo 920579 921575 := bstep (se 1 (by rfl) ⟨691181, by rfl⟩ : syracuseStep 921575 = 1382363) B1382363
theorem B5246977 : Blo 920579 5246977 := bstep (se 2 (by rfl) ⟨1967616, by rfl⟩ : syracuseStep 5246977 = 3935233) B3935233
theorem B2330633 : Blo 920579 2330633 := bstep (se 2 (by rfl) ⟨873987, by rfl⟩ : syracuseStep 2330633 = 1747975) B1747975
theorem B921887 : Blo 920579 921887 := bstep (se 1 (by rfl) ⟨691415, by rfl⟩ : syracuseStep 921887 = 1382831) B1382831
theorem B921947 : Blo 920579 921947 := bstep (se 1 (by rfl) ⟨691460, by rfl⟩ : syracuseStep 921947 = 1382921) B1382921
theorem B3117419 : Blo 920579 3117419 := bstep (se 1 (by rfl) ⟨2338064, by rfl⟩ : syracuseStep 3117419 = 4676129) B4676129
theorem B921967 : Blo 920579 921967 := bstep (se 1 (by rfl) ⟨691475, by rfl⟩ : syracuseStep 921967 = 1382951) B1382951
theorem B15962503 : Blo 920579 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B922023 : Blo 920579 922023 := bstep (se 1 (by rfl) ⟨691517, by rfl⟩ : syracuseStep 922023 = 1383035) B1383035
theorem B3936737 : Blo 920579 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B922107 : Blo 920579 922107 := bstep (se 1 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 922107 = 1383161) B1383161
theorem B922175 : Blo 920579 922175 := bstep (se 1 (by rfl) ⟨691631, by rfl⟩ : syracuseStep 922175 = 1383263) B1383263
theorem B1380935 : Blo 920579 1380935 := bstep (se 1 (by rfl) ⟨1035701, by rfl⟩ : syracuseStep 1380935 = 2071403) B2071403
theorem B922183 : Blo 920579 922183 := bstep (se 1 (by rfl) ⟨691637, by rfl⟩ : syracuseStep 922183 = 1383275) B1383275
theorem B1380971 : Blo 920579 1380971 := bstep (se 1 (by rfl) ⟨1035728, by rfl⟩ : syracuseStep 1380971 = 2071457) B2071457
theorem B1315435 : Blo 920579 1315435 := bstep (se 1 (by rfl) ⟨986576, by rfl⟩ : syracuseStep 1315435 = 1973153) B1973153
theorem B3117689 : Blo 920579 3117689 := bstep (se 2 (by rfl) ⟨1169133, by rfl⟩ : syracuseStep 3117689 = 2338267) B2338267
theorem B922335 : Blo 920579 922335 := bstep (se 1 (by rfl) ⟨691751, by rfl⟩ : syracuseStep 922335 = 1383503) B1383503
theorem B922415 : Blo 920579 922415 := bstep (se 1 (by rfl) ⟨691811, by rfl⟩ : syracuseStep 922415 = 1383623) B1383623
theorem B1381199 : Blo 920579 1381199 := bstep (se 1 (by rfl) ⟨1035899, by rfl⟩ : syracuseStep 1381199 = 2071799) B2071799
theorem B922523 : Blo 920579 922523 := bstep (se 1 (by rfl) ⟨691892, by rfl⟩ : syracuseStep 922523 = 1383785) B1383785
theorem B8852429 : Blo 920579 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B922575 : Blo 920579 922575 := bstep (se 1 (by rfl) ⟨691931, by rfl⟩ : syracuseStep 922575 = 1383863) B1383863
theorem B922599 : Blo 920579 922599 := bstep (se 1 (by rfl) ⟨691949, by rfl⟩ : syracuseStep 922599 = 1383899) B1383899
theorem B2331787 : Blo 920579 2331787 := bstep (se 1 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 2331787 = 3497681) B3497681
theorem B2954387 : Blo 920579 2954387 := bstep (se 1 (by rfl) ⟨2215790, by rfl⟩ : syracuseStep 2954387 = 4431581) B4431581
theorem B1381595 : Blo 920579 1381595 := bstep (se 1 (by rfl) ⟨1036196, by rfl⟩ : syracuseStep 1381595 = 2072393) B2072393
theorem B2626793 : Blo 920579 2626793 := bstep (se 2 (by rfl) ⟨985047, by rfl⟩ : syracuseStep 2626793 = 1970095) B1970095
theorem B6067457 : Blo 920579 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B922911 : Blo 920579 922911 := bstep (se 1 (by rfl) ⟨692183, by rfl⟩ : syracuseStep 922911 = 1384367) B1384367
theorem B922971 : Blo 920579 922971 := bstep (se 1 (by rfl) ⟨692228, by rfl⟩ : syracuseStep 922971 = 1384457) B1384457
theorem B922991 : Blo 920579 922991 := bstep (se 1 (by rfl) ⟨692243, by rfl⟩ : syracuseStep 922991 = 1384487) B1384487
theorem B1381769 : Blo 920579 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B923047 : Blo 920579 923047 := bstep (se 1 (by rfl) ⟨692285, by rfl⟩ : syracuseStep 923047 = 1384571) B1384571
theorem B2332091 : Blo 920579 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B923131 : Blo 920579 923131 := bstep (se 1 (by rfl) ⟨692348, by rfl⟩ : syracuseStep 923131 = 1384697) B1384697
theorem B923199 : Blo 920579 923199 := bstep (se 1 (by rfl) ⟨692399, by rfl⟩ : syracuseStep 923199 = 1384799) B1384799
theorem B923207 : Blo 920579 923207 := bstep (se 1 (by rfl) ⟨692405, by rfl⟩ : syracuseStep 923207 = 1384811) B1384811
theorem B923359 : Blo 920579 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B1382123 : Blo 920579 1382123 := bstep (se 1 (by rfl) ⟨1036592, by rfl⟩ : syracuseStep 1382123 = 2073185) B2073185
theorem B923439 : Blo 920579 923439 := bstep (se 1 (by rfl) ⟨692579, by rfl⟩ : syracuseStep 923439 = 1385159) B1385159
theorem B923547 : Blo 920579 923547 := bstep (se 1 (by rfl) ⟨692660, by rfl⟩ : syracuseStep 923547 = 1385321) B1385321
theorem B1382351 : Blo 920579 1382351 := bstep (se 1 (by rfl) ⟨1036763, by rfl⟩ : syracuseStep 1382351 = 2073527) B2073527
theorem B923599 : Blo 920579 923599 := bstep (se 1 (by rfl) ⟨692699, by rfl⟩ : syracuseStep 923599 = 1385399) B1385399
theorem B923623 : Blo 920579 923623 := bstep (se 1 (by rfl) ⟨692717, by rfl⟩ : syracuseStep 923623 = 1385435) B1385435
theorem B52664327 : Blo 920579 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B923935 : Blo 920579 923935 := bstep (se 1 (by rfl) ⟨692951, by rfl⟩ : syracuseStep 923935 = 1385903) B1385903
theorem B1382747 : Blo 920579 1382747 := bstep (se 1 (by rfl) ⟨1037060, by rfl⟩ : syracuseStep 1382747 = 2074121) B2074121
theorem B923995 : Blo 920579 923995 := bstep (se 1 (by rfl) ⟨692996, by rfl⟩ : syracuseStep 923995 = 1385993) B1385993
theorem B924015 : Blo 920579 924015 := bstep (se 1 (by rfl) ⟨693011, by rfl⟩ : syracuseStep 924015 = 1386023) B1386023
theorem B3119471 : Blo 920579 3119471 := bstep (se 1 (by rfl) ⟨2339603, by rfl⟩ : syracuseStep 3119471 = 4679207) B4679207
theorem B924071 : Blo 920579 924071 := bstep (se 1 (by rfl) ⟨693053, by rfl⟩ : syracuseStep 924071 = 1386107) B1386107
theorem B924155 : Blo 920579 924155 := bstep (se 1 (by rfl) ⟨693116, by rfl⟩ : syracuseStep 924155 = 1386233) B1386233
theorem B1382975 : Blo 920579 1382975 := bstep (se 1 (by rfl) ⟨1037231, by rfl⟩ : syracuseStep 1382975 = 2074463) B2074463
theorem B924223 : Blo 920579 924223 := bstep (se 1 (by rfl) ⟨693167, by rfl⟩ : syracuseStep 924223 = 1386335) B1386335
theorem B924231 : Blo 920579 924231 := bstep (se 1 (by rfl) ⟨693173, by rfl⟩ : syracuseStep 924231 = 1386347) B1386347
theorem B10525301 : Blo 920579 10525301 := bstep (se 5 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 10525301 = 986747) B986747
theorem B5249711 : Blo 920579 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B1383095 : Blo 920579 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B2333407 : Blo 920579 2333407 := bstep (se 1 (by rfl) ⟨1750055, by rfl⟩ : syracuseStep 2333407 = 3500111) B3500111
theorem B924383 : Blo 920579 924383 := bstep (se 1 (by rfl) ⟨693287, by rfl⟩ : syracuseStep 924383 = 1386575) B1386575
theorem B2136851 : Blo 920579 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B924463 : Blo 920579 924463 := bstep (se 1 (by rfl) ⟨693347, by rfl⟩ : syracuseStep 924463 = 1386695) B1386695
theorem B2333519 : Blo 920579 2333519 := bstep (se 1 (by rfl) ⟨1750139, by rfl⟩ : syracuseStep 2333519 = 3500279) B3500279
theorem B2071439 : Blo 920579 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B1383323 : Blo 920579 1383323 := bstep (se 1 (by rfl) ⟨1037492, by rfl⟩ : syracuseStep 1383323 = 2074985) B2074985
theorem B924571 : Blo 920579 924571 := bstep (se 1 (by rfl) ⟨693428, by rfl⟩ : syracuseStep 924571 = 1386857) B1386857
theorem B1383719 : Blo 920579 1383719 := bstep (se 1 (by rfl) ⟨1037789, by rfl⟩ : syracuseStep 1383719 = 2075579) B2075579
theorem B4660577 : Blo 920579 4660577 := bstep (se 2 (by rfl) ⟨1747716, by rfl⟩ : syracuseStep 4660577 = 3495433) B3495433
theorem B1383803 : Blo 920579 1383803 := bstep (se 1 (by rfl) ⟨1037852, by rfl⟩ : syracuseStep 1383803 = 2075705) B2075705
theorem B4988297 : Blo 920579 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B2334167 : Blo 920579 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1383929 : Blo 920579 1383929 := bstep (se 2 (by rfl) ⟨518973, by rfl⟩ : syracuseStep 1383929 = 1037947) B1037947
theorem B5905979 : Blo 920579 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B6823507 : Blo 920579 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B22453847 : Blo 920579 22453847 := bstep (se 1 (by rfl) ⟨16840385, by rfl⟩ : syracuseStep 22453847 = 33680771) B33680771
theorem B2072159 : Blo 920579 2072159 := bstep (se 1 (by rfl) ⟨1554119, by rfl⟩ : syracuseStep 2072159 = 3108239) B3108239
theorem B1384031 : Blo 920579 1384031 := bstep (se 1 (by rfl) ⟨1038023, by rfl⟩ : syracuseStep 1384031 = 2076047) B2076047
theorem B3743347 : Blo 920579 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B2956961 : Blo 920579 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B4202219 : Blo 920579 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B2072375 : Blo 920579 2072375 := bstep (se 1 (by rfl) ⟨1554281, by rfl⟩ : syracuseStep 2072375 = 3108563) B3108563
theorem B1384247 : Blo 920579 1384247 := bstep (se 1 (by rfl) ⟨1038185, by rfl⟩ : syracuseStep 1384247 = 2076371) B2076371
theorem B2334521 : Blo 920579 2334521 := bstep (se 2 (by rfl) ⟨875445, by rfl⟩ : syracuseStep 2334521 = 1750891) B1750891
theorem B9969713 : Blo 920579 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B2072681 : Blo 920579 2072681 := bstep (se 2 (by rfl) ⟨777255, by rfl⟩ : syracuseStep 2072681 = 1554511) B1554511
theorem B1384553 : Blo 920579 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B14983379 : Blo 920579 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B7020755 : Blo 920579 7020755 := bstep (se 1 (by rfl) ⟨5265566, by rfl⟩ : syracuseStep 7020755 = 10531133) B10531133
theorem B1384871 : Blo 920579 1384871 := bstep (se 1 (by rfl) ⟨1038653, by rfl⟩ : syracuseStep 1384871 = 2077307) B2077307
theorem B1384955 : Blo 920579 1384955 := bstep (se 1 (by rfl) ⟨1038716, by rfl⟩ : syracuseStep 1384955 = 2077433) B2077433
theorem B2073167 : Blo 920579 2073167 := bstep (se 1 (by rfl) ⟨1554875, by rfl⟩ : syracuseStep 2073167 = 3109751) B3109751
theorem B1385081 : Blo 920579 1385081 := bstep (se 2 (by rfl) ⟨519405, by rfl⟩ : syracuseStep 1385081 = 1038811) B1038811
theorem B1385135 : Blo 920579 1385135 := bstep (se 1 (by rfl) ⟨1038851, by rfl⟩ : syracuseStep 1385135 = 2077703) B2077703
theorem B2073311 : Blo 920579 2073311 := bstep (se 1 (by rfl) ⟨1554983, by rfl⟩ : syracuseStep 2073311 = 3109967) B3109967
theorem B1385183 : Blo 920579 1385183 := bstep (se 1 (by rfl) ⟨1038887, by rfl⟩ : syracuseStep 1385183 = 2077775) B2077775
theorem B2073563 : Blo 920579 2073563 := bstep (se 1 (by rfl) ⟨1555172, by rfl⟩ : syracuseStep 2073563 = 3110345) B3110345
theorem B1385447 : Blo 920579 1385447 := bstep (se 1 (by rfl) ⟨1039085, by rfl⟩ : syracuseStep 1385447 = 2078171) B2078171
theorem B22488101 : Blo 920579 22488101 := bstep (se 4 (by rfl) ⟨2108259, by rfl⟩ : syracuseStep 22488101 = 4216519) B4216519
theorem B2106491 : Blo 920579 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B2073743 : Blo 920579 2073743 := bstep (se 1 (by rfl) ⟨1555307, by rfl⟩ : syracuseStep 2073743 = 3110615) B3110615
theorem B2958551 : Blo 920579 2958551 := bstep (se 1 (by rfl) ⟨2218913, by rfl⟩ : syracuseStep 2958551 = 4437827) B4437827
theorem B2073833 : Blo 920579 2073833 := bstep (se 2 (by rfl) ⟨777687, by rfl⟩ : syracuseStep 2073833 = 1555375) B1555375
theorem B1385705 : Blo 920579 1385705 := bstep (se 2 (by rfl) ⟨519639, by rfl⟩ : syracuseStep 1385705 = 1039279) B1039279
theorem B4662521 : Blo 920579 4662521 := bstep (se 2 (by rfl) ⟨1748445, by rfl⟩ : syracuseStep 4662521 = 3496891) B3496891
theorem B2073887 : Blo 920579 2073887 := bstep (se 1 (by rfl) ⟨1555415, by rfl⟩ : syracuseStep 2073887 = 3110831) B3110831
theorem B1385759 : Blo 920579 1385759 := bstep (se 1 (by rfl) ⟨1039319, by rfl⟩ : syracuseStep 1385759 = 2078639) B2078639
theorem B2630951 : Blo 920579 2630951 := bstep (se 1 (by rfl) ⟨1973213, by rfl⟩ : syracuseStep 2630951 = 3946427) B3946427
theorem B8529239 : Blo 920579 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B2958731 : Blo 920579 2958731 := bstep (se 1 (by rfl) ⟨2219048, by rfl⟩ : syracuseStep 2958731 = 4438097) B4438097
theorem B2336161 : Blo 920579 2336161 := bstep (se 2 (by rfl) ⟨876060, by rfl⟩ : syracuseStep 2336161 = 1752121) B1752121
theorem B1385927 : Blo 920579 1385927 := bstep (se 1 (by rfl) ⟨1039445, by rfl⟩ : syracuseStep 1385927 = 2078891) B2078891
theorem B2074409 : Blo 920579 2074409 := bstep (se 2 (by rfl) ⟨777903, by rfl⟩ : syracuseStep 2074409 = 1555807) B1555807
theorem B1386281 : Blo 920579 1386281 := bstep (se 2 (by rfl) ⟨519855, by rfl⟩ : syracuseStep 1386281 = 1039711) B1039711
theorem B1386287 : Blo 920579 1386287 := bstep (se 1 (by rfl) ⟨1039715, by rfl⟩ : syracuseStep 1386287 = 2079431) B2079431
theorem B7087949 : Blo 920579 7087949 := bstep (se 3 (by rfl) ⟨1328990, by rfl⟩ : syracuseStep 7087949 = 2657981) B2657981
theorem B4990825 : Blo 920579 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B1386761 : Blo 920579 1386761 := bstep (se 2 (by rfl) ⟨520035, by rfl⟩ : syracuseStep 1386761 = 1040071) B1040071
theorem B6302063 : Blo 920579 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B1386863 : Blo 920579 1386863 := bstep (se 1 (by rfl) ⟨1040147, by rfl⟩ : syracuseStep 1386863 = 2080295) B2080295
theorem B2337275 : Blo 920579 2337275 := bstep (se 1 (by rfl) ⟨1752956, by rfl⟩ : syracuseStep 2337275 = 3505913) B3505913
theorem B2075471 : Blo 920579 2075471 := bstep (se 1 (by rfl) ⟨1556603, by rfl⟩ : syracuseStep 2075471 = 3113207) B3113207
theorem B2075687 : Blo 920579 2075687 := bstep (se 1 (by rfl) ⟨1556765, by rfl⟩ : syracuseStep 2075687 = 3113531) B3113531
theorem B2075867 : Blo 920579 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B2076065 : Blo 920579 2076065 := bstep (se 2 (by rfl) ⟨778524, by rfl⟩ : syracuseStep 2076065 = 1557049) B1557049
theorem B4206011 : Blo 920579 4206011 := bstep (se 1 (by rfl) ⟨3154508, by rfl⟩ : syracuseStep 4206011 = 6309017) B6309017
theorem B2338247 : Blo 920579 2338247 := bstep (se 1 (by rfl) ⟨1753685, by rfl⟩ : syracuseStep 2338247 = 3507371) B3507371
theorem B3944051 : Blo 920579 3944051 := bstep (se 1 (by rfl) ⟨2958038, by rfl⟩ : syracuseStep 3944051 = 5916077) B5916077
theorem B2961011 : Blo 920579 2961011 := bstep (se 1 (by rfl) ⟨2220758, by rfl⟩ : syracuseStep 2961011 = 4441517) B4441517
theorem B6991595 : Blo 920579 6991595 := bstep (se 1 (by rfl) ⟨5243696, by rfl⟩ : syracuseStep 6991595 = 10487393) B10487393
theorem B2076623 : Blo 920579 2076623 := bstep (se 1 (by rfl) ⟨1557467, by rfl⟩ : syracuseStep 2076623 = 3114935) B3114935
theorem B4730899 : Blo 920579 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B2339027 : Blo 920579 2339027 := bstep (se 1 (by rfl) ⟨1754270, by rfl⟩ : syracuseStep 2339027 = 3508541) B3508541
theorem B3748049 : Blo 920579 3748049 := bstep (se 2 (by rfl) ⟨1405518, by rfl⟩ : syracuseStep 3748049 = 2811037) B2811037
theorem B2077001 : Blo 920579 2077001 := bstep (se 2 (by rfl) ⟨778875, by rfl⟩ : syracuseStep 2077001 = 1557751) B1557751
theorem B2077019 : Blo 920579 2077019 := bstep (se 1 (by rfl) ⟨1557764, by rfl⟩ : syracuseStep 2077019 = 3115529) B3115529
theorem B2339239 : Blo 920579 2339239 := bstep (se 1 (by rfl) ⟨1754429, by rfl⟩ : syracuseStep 2339239 = 3508859) B3508859
theorem B2339401 : Blo 920579 2339401 := bstep (se 2 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 2339401 = 1754551) B1754551
theorem B2077595 : Blo 920579 2077595 := bstep (se 1 (by rfl) ⟨1558196, by rfl⟩ : syracuseStep 2077595 = 3116393) B3116393
theorem B4502585 : Blo 920579 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B2077793 : Blo 920579 2077793 := bstep (se 2 (by rfl) ⟨779172, by rfl⟩ : syracuseStep 2077793 = 1558345) B1558345
theorem B6993053 : Blo 920579 6993053 := bstep (se 3 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 6993053 = 2622395) B2622395
theorem B1553627 : Blo 920579 1553627 := bstep (se 1 (by rfl) ⟨1165220, by rfl⟩ : syracuseStep 1553627 = 2330441) B2330441
theorem B2077991 : Blo 920579 2077991 := bstep (se 1 (by rfl) ⟨1558493, by rfl⟩ : syracuseStep 2077991 = 3116987) B3116987
theorem B3552607 : Blo 920579 3552607 := bstep (se 1 (by rfl) ⟨2664455, by rfl⟩ : syracuseStep 3552607 = 5328911) B5328911
theorem B2340191 : Blo 920579 2340191 := bstep (se 1 (by rfl) ⟨1755143, by rfl⟩ : syracuseStep 2340191 = 3510287) B3510287
theorem B4666733 : Blo 920579 4666733 := bstep (se 3 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 4666733 = 1750025) B1750025
theorem B1553863 : Blo 920579 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B35468765 : Blo 920579 35468765 := bstep (se 3 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 35468765 = 13300787) B13300787
theorem B996859 : Blo 920579 996859 := bstep (se 1 (by rfl) ⟨747644, by rfl⟩ : syracuseStep 996859 = 1495289) B1495289
theorem B2078369 : Blo 920579 2078369 := bstep (se 2 (by rfl) ⟨779388, by rfl⟩ : syracuseStep 2078369 = 1558777) B1558777
theorem B1554383 : Blo 920579 1554383 := bstep (se 1 (by rfl) ⟨1165787, by rfl⟩ : syracuseStep 1554383 = 2331575) B2331575
theorem B2078729 : Blo 920579 2078729 := bstep (se 2 (by rfl) ⟨779523, by rfl⟩ : syracuseStep 2078729 = 1559047) B1559047
theorem B2079143 : Blo 920579 2079143 := bstep (se 1 (by rfl) ⟨1559357, by rfl⟩ : syracuseStep 2079143 = 3118715) B3118715
theorem B2079251 : Blo 920579 2079251 := bstep (se 1 (by rfl) ⟨1559438, by rfl⟩ : syracuseStep 2079251 = 3118877) B3118877
theorem B2079305 : Blo 920579 2079305 := bstep (se 2 (by rfl) ⟨779739, by rfl⟩ : syracuseStep 2079305 = 1559479) B1559479
theorem B1555051 : Blo 920579 1555051 := bstep (se 1 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 1555051 = 2332577) B2332577
theorem B6306443 : Blo 920579 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B5913283 : Blo 920579 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B1555355 : Blo 920579 1555355 := bstep (se 1 (by rfl) ⟨1166516, by rfl⟩ : syracuseStep 1555355 = 2333033) B2333033
theorem B2079719 : Blo 920579 2079719 := bstep (se 1 (by rfl) ⟨1559789, by rfl⟩ : syracuseStep 2079719 = 3119579) B3119579
theorem B17710325 : Blo 920579 17710325 := bstep (se 5 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 17710325 = 1660343) B1660343
theorem B7880003 : Blo 920579 7880003 := bstep (se 1 (by rfl) ⟨5910002, by rfl⟩ : syracuseStep 7880003 = 11820005) B11820005
theorem B2080097 : Blo 920579 2080097 := bstep (se 2 (by rfl) ⟨780036, by rfl⟩ : syracuseStep 2080097 = 1560073) B1560073
theorem B2080187 : Blo 920579 2080187 := bstep (se 1 (by rfl) ⟨1560140, by rfl⟩ : syracuseStep 2080187 = 3120281) B3120281
theorem B5914127 : Blo 920579 5914127 := bstep (se 1 (by rfl) ⟨4435595, by rfl⟩ : syracuseStep 5914127 = 8871191) B8871191
theorem B4669163 : Blo 920579 4669163 := bstep (se 1 (by rfl) ⟨3501872, by rfl⟩ : syracuseStep 4669163 = 7003745) B7003745
theorem B4669649 : Blo 920579 4669649 := bstep (se 2 (by rfl) ⟨1751118, by rfl⟩ : syracuseStep 4669649 = 3502237) B3502237
theorem B19939769 : Blo 920579 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B1753663 : Blo 920579 1753663 := bstep (se 1 (by rfl) ⟨1315247, by rfl⟩ : syracuseStep 1753663 = 2630495) B2630495
theorem B32424583 : Blo 920579 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B4670135 : Blo 920579 4670135 := bstep (se 1 (by rfl) ⟨3502601, by rfl⟩ : syracuseStep 4670135 = 7005203) B7005203
theorem B8864731 : Blo 920579 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B9716773 : Blo 920579 9716773 := bstep (se 4 (by rfl) ⟨910947, by rfl⟩ : syracuseStep 9716773 = 1821895) B1821895
theorem B4670621 : Blo 920579 4670621 := bstep (se 3 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 4670621 = 1751483) B1751483
theorem B1754399 : Blo 920579 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B8111411 : Blo 920579 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B4441787 : Blo 920579 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B2213993 : Blo 920579 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B1165691 : Blo 920579 1165691 := bstep (se 1 (by rfl) ⟨874268, by rfl⟩ : syracuseStep 1165691 = 1748537) B1748537
theorem B4671917 : Blo 920579 4671917 := bstep (se 3 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 4671917 = 1751969) B1751969
theorem B2804179 : Blo 920579 2804179 := bstep (se 1 (by rfl) ⟨2103134, by rfl⟩ : syracuseStep 2804179 = 4206269) B4206269
theorem B4672079 : Blo 920579 4672079 := bstep (se 1 (by rfl) ⟨3504059, by rfl⟩ : syracuseStep 4672079 = 7008119) B7008119
theorem B1559263 : Blo 920579 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B8866577 : Blo 920579 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B3329063 : Blo 920579 3329063 := bstep (se 1 (by rfl) ⟨2496797, by rfl⟩ : syracuseStep 3329063 = 4993595) B4993595
theorem B1559695 : Blo 920579 1559695 := bstep (se 1 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 1559695 = 2339543) B2339543
theorem B2215127 : Blo 920579 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B1559945 : Blo 920579 1559945 := bstep (se 2 (by rfl) ⟨584979, by rfl⟩ : syracuseStep 1559945 = 1169959) B1169959
theorem B3329495 : Blo 920579 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B8867501 : Blo 920579 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B4214585 : Blo 920579 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B1036111 : Blo 920579 1036111 := bstep (se 1 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 1036111 = 1554167) B1554167
theorem B35508131 : Blo 920579 35508131 := bstep (se 1 (by rfl) ⟨26631098, by rfl⟩ : syracuseStep 35508131 = 53262197) B53262197
theorem B1167311 : Blo 920579 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B4673537 : Blo 920579 4673537 := bstep (se 2 (by rfl) ⟨1752576, by rfl⟩ : syracuseStep 4673537 = 3505153) B3505153
theorem B2805785 : Blo 920579 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B1036507 : Blo 920579 1036507 := bstep (se 1 (by rfl) ⟨777380, by rfl⟩ : syracuseStep 1036507 = 1554761) B1554761
theorem B2806123 : Blo 920579 2806123 := bstep (se 1 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 2806123 = 4209185) B4209185
theorem B1036795 : Blo 920579 1036795 := bstep (se 1 (by rfl) ⟨777596, by rfl⟩ : syracuseStep 1036795 = 1555193) B1555193
theorem B2806343 : Blo 920579 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1036975 : Blo 920579 1036975 := bstep (se 1 (by rfl) ⟨777731, by rfl⟩ : syracuseStep 1036975 = 1555463) B1555463
theorem B4674347 : Blo 920579 4674347 := bstep (se 1 (by rfl) ⟨3505760, by rfl⟩ : syracuseStep 4674347 = 7011521) B7011521
theorem B1168283 : Blo 920579 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B1037263 : Blo 920579 1037263 := bstep (se 1 (by rfl) ⟨777947, by rfl⟩ : syracuseStep 1037263 = 1555895) B1555895
theorem B5264473 : Blo 920579 5264473 := bstep (se 2 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 5264473 = 3948355) B3948355
theorem B17749145 : Blo 920579 17749145 := bstep (se 2 (by rfl) ⟨6655929, by rfl⟩ : syracuseStep 17749145 = 13311859) B13311859
theorem B2217203 : Blo 920579 2217203 := bstep (se 1 (by rfl) ⟨1662902, by rfl⟩ : syracuseStep 2217203 = 3325805) B3325805
theorem B1037659 : Blo 920579 1037659 := bstep (se 1 (by rfl) ⟨778244, by rfl⟩ : syracuseStep 1037659 = 1556489) B1556489
theorem B3986783 : Blo 920579 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B1037767 : Blo 920579 1037767 := bstep (se 1 (by rfl) ⟨778325, by rfl⟩ : syracuseStep 1037767 = 1556651) B1556651
theorem B2840071 : Blo 920579 2840071 := bstep (se 1 (by rfl) ⟨2130053, by rfl⟩ : syracuseStep 2840071 = 4260107) B4260107
theorem B17749691 : Blo 920579 17749691 := bstep (se 1 (by rfl) ⟨13312268, by rfl⟩ : syracuseStep 17749691 = 26624537) B26624537
theorem B1038127 : Blo 920579 1038127 := bstep (se 1 (by rfl) ⟨778595, by rfl⟩ : syracuseStep 1038127 = 1557191) B1557191
theorem B1038235 : Blo 920579 1038235 := bstep (se 1 (by rfl) ⟨778676, by rfl⟩ : syracuseStep 1038235 = 1557353) B1557353
theorem B1038631 : Blo 920579 1038631 := bstep (se 1 (by rfl) ⟨778973, by rfl⟩ : syracuseStep 1038631 = 1557947) B1557947
theorem B1038703 : Blo 920579 1038703 := bstep (se 1 (by rfl) ⟨779027, by rfl⟩ : syracuseStep 1038703 = 1558055) B1558055
theorem B1038919 : Blo 920579 1038919 := bstep (se 1 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 1038919 = 1558379) B1558379
theorem B1661561 : Blo 920579 1661561 := bstep (se 2 (by rfl) ⟨623085, by rfl⟩ : syracuseStep 1661561 = 1246171) B1246171
theorem B4676291 : Blo 920579 4676291 := bstep (se 1 (by rfl) ⟨3507218, by rfl⟩ : syracuseStep 4676291 = 7014437) B7014437
theorem B2251487 : Blo 920579 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B7887689 : Blo 920579 7887689 := bstep (se 2 (by rfl) ⟨2957883, by rfl⟩ : syracuseStep 7887689 = 5915767) B5915767
theorem B2219105 : Blo 920579 2219105 := bstep (se 2 (by rfl) ⟨832164, by rfl⟩ : syracuseStep 2219105 = 1664329) B1664329
theorem B7003259 : Blo 920579 7003259 := bstep (se 1 (by rfl) ⟨5252444, by rfl⟩ : syracuseStep 7003259 = 10504889) B10504889
theorem B1662095 : Blo 920579 1662095 := bstep (se 1 (by rfl) ⟨1246571, by rfl⟩ : syracuseStep 1662095 = 2493143) B2493143
theorem B2219251 : Blo 920579 2219251 := bstep (se 1 (by rfl) ⟨1664438, by rfl⟩ : syracuseStep 2219251 = 3328877) B3328877
theorem B1039783 : Blo 920579 1039783 := bstep (se 1 (by rfl) ⟨779837, by rfl⟩ : syracuseStep 1039783 = 1559675) B1559675
theorem B4743851 : Blo 920579 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B3499307 : Blo 920579 3499307 := bstep (se 1 (by rfl) ⟨2624480, by rfl⟩ : syracuseStep 3499307 = 5248961) B5248961
theorem B1107919 : Blo 920579 1107919 := bstep (se 1 (by rfl) ⟨830939, by rfl⟩ : syracuseStep 1107919 = 1661879) B1661879
theorem B6646013 : Blo 920579 6646013 := bstep (se 3 (by rfl) ⟨1246127, by rfl⟩ : syracuseStep 6646013 = 2492255) B2492255
theorem B4680179 : Blo 920579 4680179 := bstep (se 1 (by rfl) ⟨3510134, by rfl⟩ : syracuseStep 4680179 = 7020269) B7020269
theorem B53144099 : Blo 920579 53144099 := bstep (se 1 (by rfl) ⟨39858074, by rfl⟩ : syracuseStep 53144099 = 79716149) B79716149
theorem B7007147 : Blo 920579 7007147 := bstep (se 1 (by rfl) ⟨5255360, by rfl⟩ : syracuseStep 7007147 = 10510721) B10510721
theorem B39841469 : Blo 920579 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B6319883 : Blo 920579 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B7892747 : Blo 920579 7892747 := bstep (se 1 (by rfl) ⟨5919560, by rfl⟩ : syracuseStep 7892747 = 11839121) B11839121
theorem B42594167 : Blo 920579 42594167 := bstep (se 1 (by rfl) ⟨31945625, by rfl⟩ : syracuseStep 42594167 = 63891251) B63891251
theorem B3109211 : Blo 920579 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B3502511 : Blo 920579 3502511 := bstep (se 1 (by rfl) ⟨2626883, by rfl⟩ : syracuseStep 3502511 = 5253767) B5253767
theorem B75592561 : Blo 920579 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B14939261 : Blo 920579 14939261 := bstep (se 3 (by rfl) ⟨2801111, by rfl⟩ : syracuseStep 14939261 = 5602223) B5602223
theorem B17724541 : Blo 920579 17724541 := bstep (se 3 (by rfl) ⟨3323351, by rfl⟩ : syracuseStep 17724541 = 6646703) B6646703
theorem B3110183 : Blo 920579 3110183 := bstep (se 1 (by rfl) ⟨2332637, by rfl⟩ : syracuseStep 3110183 = 4665275) B4665275
theorem B3503483 : Blo 920579 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B3111047 : Blo 920579 3111047 := bstep (se 1 (by rfl) ⟨2333285, by rfl⟩ : syracuseStep 3111047 = 4666571) B4666571
theorem B31980109 : Blo 920579 31980109 := bstep (se 3 (by rfl) ⟨5996270, by rfl⟩ : syracuseStep 31980109 = 11992541) B11992541
theorem B3505139 : Blo 920579 3505139 := bstep (se 1 (by rfl) ⟨2628854, by rfl⟩ : syracuseStep 3505139 = 5257709) B5257709
theorem B9960677 : Blo 920579 9960677 := bstep (se 4 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 9960677 = 1867627) B1867627
theorem B3112289 : Blo 920579 3112289 := bstep (se 2 (by rfl) ⟨1167108, by rfl⟩ : syracuseStep 3112289 = 2334217) B2334217
theorem B1244527 : Blo 920579 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B4488635 : Blo 920579 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B3113099 : Blo 920579 3113099 := bstep (se 1 (by rfl) ⟨2334824, by rfl⟩ : syracuseStep 3113099 = 4669649) B4669649
theorem B9961751 : Blo 920579 9961751 := bstep (se 1 (by rfl) ⟨7471313, by rfl⟩ : syracuseStep 9961751 = 14942627) B14942627
theorem B5898521 : Blo 920579 5898521 := bstep (se 2 (by rfl) ⟨2211945, by rfl⟩ : syracuseStep 5898521 = 4423891) B4423891
theorem B1966523 : Blo 920579 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B1311175 : Blo 920579 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B3113423 : Blo 920579 3113423 := bstep (se 1 (by rfl) ⟨2335067, by rfl⟩ : syracuseStep 3113423 = 4670135) B4670135
theorem B8651227 : Blo 920579 8651227 := bstep (se 1 (by rfl) ⟨6488420, by rfl⟩ : syracuseStep 8651227 = 12976841) B12976841
theorem B2621929 : Blo 920579 2621929 := bstep (se 2 (by rfl) ⟨983223, by rfl⟩ : syracuseStep 2621929 = 1966447) B1966447
theorem B3113747 : Blo 920579 3113747 := bstep (se 1 (by rfl) ⟨2335310, by rfl⟩ : syracuseStep 3113747 = 4670621) B4670621
theorem B5407607 : Blo 920579 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B2622419 : Blo 920579 2622419 := bstep (se 1 (by rfl) ⟨1966814, by rfl⟩ : syracuseStep 2622419 = 3933629) B3933629
theorem B1475995 : Blo 920579 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B984475 : Blo 920579 984475 := bstep (se 1 (by rfl) ⟨738356, by rfl⟩ : syracuseStep 984475 = 1476713) B1476713
theorem B2491823 : Blo 920579 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B3114611 : Blo 920579 3114611 := bstep (se 1 (by rfl) ⟨2335958, by rfl⟩ : syracuseStep 3114611 = 4671917) B4671917
theorem B3114719 : Blo 920579 3114719 := bstep (se 1 (by rfl) ⟨2336039, by rfl⟩ : syracuseStep 3114719 = 4672079) B4672079
theorem B12650269 : Blo 920579 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B1967951 : Blo 920579 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B5900161 : Blo 920579 5900161 := bstep (se 2 (by rfl) ⟨2212560, by rfl⟩ : syracuseStep 5900161 = 4425121) B4425121
theorem B3114881 : Blo 920579 3114881 := bstep (se 2 (by rfl) ⟨1168080, by rfl⟩ : syracuseStep 3114881 = 2336161) B2336161
theorem B7866503 : Blo 920579 7866503 := bstep (se 1 (by rfl) ⟨5899877, by rfl⟩ : syracuseStep 7866503 = 11799755) B11799755
theorem B3115421 : Blo 920579 3115421 := bstep (se 3 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 3115421 = 1168283) B1168283
theorem B6654433 : Blo 920579 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B7014923 : Blo 920579 7014923 := bstep (se 1 (by rfl) ⟨5261192, by rfl⟩ : syracuseStep 7014923 = 10522385) B10522385
theorem B1968745 : Blo 920579 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B1477225 : Blo 920579 1477225 := bstep (se 2 (by rfl) ⟨553959, by rfl⟩ : syracuseStep 1477225 = 1107919) B1107919
theorem B3115691 : Blo 920579 3115691 := bstep (se 1 (by rfl) ⟨2336768, by rfl⟩ : syracuseStep 3115691 = 4673537) B4673537
theorem B1870523 : Blo 920579 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B2624491 : Blo 920579 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B920623 : Blo 920579 920623 := bstep (se 1 (by rfl) ⟨690467, by rfl⟩ : syracuseStep 920623 = 1380935) B1380935
theorem B1870895 : Blo 920579 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B920647 : Blo 920579 920647 := bstep (se 1 (by rfl) ⟨690485, by rfl⟩ : syracuseStep 920647 = 1380971) B1380971
theorem B3116231 : Blo 920579 3116231 := bstep (se 1 (by rfl) ⟨2337173, by rfl⟩ : syracuseStep 3116231 = 4674347) B4674347
theorem B920799 : Blo 920579 920799 := bstep (se 1 (by rfl) ⟨690599, by rfl⟩ : syracuseStep 920799 = 1381199) B1381199
theorem B3738905 : Blo 920579 3738905 := bstep (se 2 (by rfl) ⟨1402089, by rfl⟩ : syracuseStep 3738905 = 2804179) B2804179
theorem B1969591 : Blo 920579 1969591 := bstep (se 1 (by rfl) ⟨1477193, by rfl⟩ : syracuseStep 1969591 = 2954387) B2954387
theorem B11832763 : Blo 920579 11832763 := bstep (se 1 (by rfl) ⟨8874572, by rfl⟩ : syracuseStep 11832763 = 17749145) B17749145
theorem B921063 : Blo 920579 921063 := bstep (se 1 (by rfl) ⟨690797, by rfl⟩ : syracuseStep 921063 = 1381595) B1381595
theorem B1478135 : Blo 920579 1478135 := bstep (se 1 (by rfl) ⟨1108601, by rfl⟩ : syracuseStep 1478135 = 2217203) B2217203
theorem B2657855 : Blo 920579 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B921179 : Blo 920579 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B11833127 : Blo 920579 11833127 := bstep (se 1 (by rfl) ⟨8874845, by rfl⟩ : syracuseStep 11833127 = 17749691) B17749691
theorem B921415 : Blo 920579 921415 := bstep (se 1 (by rfl) ⟨691061, by rfl⟩ : syracuseStep 921415 = 1382123) B1382123
theorem B921567 : Blo 920579 921567 := bstep (se 1 (by rfl) ⟨691175, by rfl⟩ : syracuseStep 921567 = 1382351) B1382351
theorem B921831 : Blo 920579 921831 := bstep (se 1 (by rfl) ⟨691373, by rfl⟩ : syracuseStep 921831 = 1382747) B1382747
theorem B921983 : Blo 920579 921983 := bstep (se 1 (by rfl) ⟨691487, by rfl⟩ : syracuseStep 921983 = 1382975) B1382975
theorem B7016867 : Blo 920579 7016867 := bstep (se 1 (by rfl) ⟨5262650, by rfl⟩ : syracuseStep 7016867 = 10525301) B10525301
theorem B922063 : Blo 920579 922063 := bstep (se 1 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 922063 = 1383095) B1383095
theorem B3117527 : Blo 920579 3117527 := bstep (se 1 (by rfl) ⟨2338145, by rfl⟩ : syracuseStep 3117527 = 4676291) B4676291
theorem B1380959 : Blo 920579 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B922215 : Blo 920579 922215 := bstep (se 1 (by rfl) ⟨691661, by rfl⟩ : syracuseStep 922215 = 1383323) B1383323
theorem B1479403 : Blo 920579 1479403 := bstep (se 1 (by rfl) ⟨1109552, by rfl⟩ : syracuseStep 1479403 = 2219105) B2219105
theorem B922479 : Blo 920579 922479 := bstep (se 1 (by rfl) ⟨691859, by rfl⟩ : syracuseStep 922479 = 1383719) B1383719
theorem B922535 : Blo 920579 922535 := bstep (se 1 (by rfl) ⟨691901, by rfl⟩ : syracuseStep 922535 = 1383803) B1383803
theorem B922619 : Blo 920579 922619 := bstep (se 1 (by rfl) ⟨691964, by rfl⟩ : syracuseStep 922619 = 1383929) B1383929
theorem B3937319 : Blo 920579 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B1381439 : Blo 920579 1381439 := bstep (se 1 (by rfl) ⟨1036079, by rfl⟩ : syracuseStep 1381439 = 2072159) B2072159
theorem B922687 : Blo 920579 922687 := bstep (se 1 (by rfl) ⟨692015, by rfl⟩ : syracuseStep 922687 = 1384031) B1384031
theorem B1381481 : Blo 920579 1381481 := bstep (se 2 (by rfl) ⟨518055, by rfl⟩ : syracuseStep 1381481 = 1036111) B1036111
theorem B1971307 : Blo 920579 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B1381583 : Blo 920579 1381583 := bstep (se 1 (by rfl) ⟨1036187, by rfl⟩ : syracuseStep 1381583 = 2072375) B2072375
theorem B922831 : Blo 920579 922831 := bstep (se 1 (by rfl) ⟨692123, by rfl⟩ : syracuseStep 922831 = 1384247) B1384247
theorem B1381787 : Blo 920579 1381787 := bstep (se 1 (by rfl) ⟨1036340, by rfl⟩ : syracuseStep 1381787 = 2072681) B2072681
theorem B923035 : Blo 920579 923035 := bstep (se 1 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 923035 = 1384553) B1384553
theorem B923247 : Blo 920579 923247 := bstep (se 1 (by rfl) ⟨692435, by rfl⟩ : syracuseStep 923247 = 1384871) B1384871
theorem B1382009 : Blo 920579 1382009 := bstep (se 2 (by rfl) ⟨518253, by rfl⟩ : syracuseStep 1382009 = 1036507) B1036507
theorem B923303 : Blo 920579 923303 := bstep (se 1 (by rfl) ⟨692477, by rfl⟩ : syracuseStep 923303 = 1384955) B1384955
theorem B1382111 : Blo 920579 1382111 := bstep (se 1 (by rfl) ⟨1036583, by rfl⟩ : syracuseStep 1382111 = 2073167) B2073167
theorem B923387 : Blo 920579 923387 := bstep (se 1 (by rfl) ⟨692540, by rfl⟩ : syracuseStep 923387 = 1385081) B1385081
theorem B923423 : Blo 920579 923423 := bstep (se 1 (by rfl) ⟨692567, by rfl⟩ : syracuseStep 923423 = 1385135) B1385135
theorem B3741497 : Blo 920579 3741497 := bstep (se 2 (by rfl) ⟨1403061, by rfl⟩ : syracuseStep 3741497 = 2806123) B2806123
theorem B1382207 : Blo 920579 1382207 := bstep (se 1 (by rfl) ⟨1036655, by rfl⟩ : syracuseStep 1382207 = 2073311) B2073311
theorem B923455 : Blo 920579 923455 := bstep (se 1 (by rfl) ⟨692591, by rfl⟩ : syracuseStep 923455 = 1385183) B1385183
theorem B3118985 : Blo 920579 3118985 := bstep (se 2 (by rfl) ⟨1169619, by rfl⟩ : syracuseStep 3118985 = 2339239) B2339239
theorem B1382375 : Blo 920579 1382375 := bstep (se 1 (by rfl) ⟨1036781, by rfl⟩ : syracuseStep 1382375 = 2073563) B2073563
theorem B923631 : Blo 920579 923631 := bstep (se 1 (by rfl) ⟨692723, by rfl⟩ : syracuseStep 923631 = 1385447) B1385447
theorem B1382393 : Blo 920579 1382393 := bstep (se 2 (by rfl) ⟨518397, by rfl⟩ : syracuseStep 1382393 = 1036795) B1036795
theorem B1382495 : Blo 920579 1382495 := bstep (se 1 (by rfl) ⟨1036871, by rfl⟩ : syracuseStep 1382495 = 2073743) B2073743
theorem B3119201 : Blo 920579 3119201 := bstep (se 2 (by rfl) ⟨1169700, by rfl⟩ : syracuseStep 3119201 = 2339401) B2339401
theorem B1972367 : Blo 920579 1972367 := bstep (se 1 (by rfl) ⟨1479275, by rfl⟩ : syracuseStep 1972367 = 2958551) B2958551
theorem B1382555 : Blo 920579 1382555 := bstep (se 1 (by rfl) ⟨1036916, by rfl⟩ : syracuseStep 1382555 = 2073833) B2073833
theorem B923803 : Blo 920579 923803 := bstep (se 1 (by rfl) ⟨692852, by rfl⟩ : syracuseStep 923803 = 1385705) B1385705
theorem B1382591 : Blo 920579 1382591 := bstep (se 1 (by rfl) ⟨1036943, by rfl⟩ : syracuseStep 1382591 = 2073887) B2073887
theorem B923839 : Blo 920579 923839 := bstep (se 1 (by rfl) ⟨692879, by rfl⟩ : syracuseStep 923839 = 1385759) B1385759
theorem B2332871 : Blo 920579 2332871 := bstep (se 1 (by rfl) ⟨1749653, by rfl⟩ : syracuseStep 2332871 = 3499307) B3499307
theorem B1382633 : Blo 920579 1382633 := bstep (se 2 (by rfl) ⟨518487, by rfl⟩ : syracuseStep 1382633 = 1036975) B1036975
theorem B1972487 : Blo 920579 1972487 := bstep (se 1 (by rfl) ⟨1479365, by rfl⟩ : syracuseStep 1972487 = 2958731) B2958731
theorem B923951 : Blo 920579 923951 := bstep (se 1 (by rfl) ⟨692963, by rfl⟩ : syracuseStep 923951 = 1385927) B1385927
theorem B1382939 : Blo 920579 1382939 := bstep (se 1 (by rfl) ⟨1037204, by rfl⟩ : syracuseStep 1382939 = 2074409) B2074409
theorem B924187 : Blo 920579 924187 := bstep (se 1 (by rfl) ⟨693140, by rfl⟩ : syracuseStep 924187 = 1386281) B1386281
theorem B924191 : Blo 920579 924191 := bstep (se 1 (by rfl) ⟨693143, by rfl⟩ : syracuseStep 924191 = 1386287) B1386287
theorem B4725299 : Blo 920579 4725299 := bstep (se 1 (by rfl) ⟨3543974, by rfl⟩ : syracuseStep 4725299 = 7087949) B7087949
theorem B1383017 : Blo 920579 1383017 := bstep (se 2 (by rfl) ⟨518631, by rfl⟩ : syracuseStep 1383017 = 1037263) B1037263
theorem B7019297 : Blo 920579 7019297 := bstep (se 2 (by rfl) ⟨2632236, by rfl⟩ : syracuseStep 7019297 = 5264473) B5264473
theorem B23632721 : Blo 920579 23632721 := bstep (se 2 (by rfl) ⟨8862270, by rfl⟩ : syracuseStep 23632721 = 17724541) B17724541
theorem B4430675 : Blo 920579 4430675 := bstep (se 1 (by rfl) ⟨3323006, by rfl⟩ : syracuseStep 4430675 = 6646013) B6646013
theorem B924507 : Blo 920579 924507 := bstep (se 1 (by rfl) ⟨693380, by rfl⟩ : syracuseStep 924507 = 1386761) B1386761
theorem B924575 : Blo 920579 924575 := bstep (se 1 (by rfl) ⟨693431, by rfl⟩ : syracuseStep 924575 = 1386863) B1386863
theorem B3120119 : Blo 920579 3120119 := bstep (se 1 (by rfl) ⟨2340089, by rfl⟩ : syracuseStep 3120119 = 4680179) B4680179
theorem B35429399 : Blo 920579 35429399 := bstep (se 1 (by rfl) ⟨26572049, by rfl⟩ : syracuseStep 35429399 = 53144099) B53144099
theorem B1383545 : Blo 920579 1383545 := bstep (se 2 (by rfl) ⟨518829, by rfl⟩ : syracuseStep 1383545 = 1037659) B1037659
theorem B1383647 : Blo 920579 1383647 := bstep (se 1 (by rfl) ⟨1037735, by rfl⟩ : syracuseStep 1383647 = 2075471) B2075471
theorem B6003965 : Blo 920579 6003965 := bstep (se 3 (by rfl) ⟨1125743, by rfl⟩ : syracuseStep 6003965 = 2251487) B2251487
theorem B2071817 : Blo 920579 2071817 := bstep (se 2 (by rfl) ⟨776931, by rfl⟩ : syracuseStep 2071817 = 1553863) B1553863
theorem B1383689 : Blo 920579 1383689 := bstep (se 2 (by rfl) ⟨518883, by rfl⟩ : syracuseStep 1383689 = 1037767) B1037767
theorem B1383791 : Blo 920579 1383791 := bstep (se 1 (by rfl) ⟨1037843, by rfl⟩ : syracuseStep 1383791 = 2075687) B2075687
theorem B1383911 : Blo 920579 1383911 := bstep (se 1 (by rfl) ⟨1037933, by rfl⟩ : syracuseStep 1383911 = 2075867) B2075867
theorem B6659621 : Blo 920579 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B1384043 : Blo 920579 1384043 := bstep (se 1 (by rfl) ⟨1038032, by rfl⟩ : syracuseStep 1384043 = 2076065) B2076065
theorem B1384169 : Blo 920579 1384169 := bstep (se 2 (by rfl) ⟨519063, by rfl⟩ : syracuseStep 1384169 = 1038127) B1038127
theorem B2629367 : Blo 920579 2629367 := bstep (se 1 (by rfl) ⟨1972025, by rfl⟩ : syracuseStep 2629367 = 3944051) B3944051
theorem B1974007 : Blo 920579 1974007 := bstep (se 1 (by rfl) ⟨1480505, by rfl⟩ : syracuseStep 1974007 = 2961011) B2961011
theorem B4661063 : Blo 920579 4661063 := bstep (se 1 (by rfl) ⟨3495797, by rfl⟩ : syracuseStep 4661063 = 6991595) B6991595
theorem B1384313 : Blo 920579 1384313 := bstep (se 2 (by rfl) ⟨519117, by rfl⟩ : syracuseStep 1384313 = 1038235) B1038235
theorem B1384415 : Blo 920579 1384415 := bstep (se 1 (by rfl) ⟨1038311, by rfl⟩ : syracuseStep 1384415 = 2076623) B2076623
theorem B2498699 : Blo 920579 2498699 := bstep (se 1 (by rfl) ⟨1874024, by rfl⟩ : syracuseStep 2498699 = 3748049) B3748049
theorem B1384667 : Blo 920579 1384667 := bstep (se 1 (by rfl) ⟨1038500, by rfl⟩ : syracuseStep 1384667 = 2077001) B2077001
theorem B2072807 : Blo 920579 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B1384679 : Blo 920579 1384679 := bstep (se 1 (by rfl) ⟨1038509, by rfl⟩ : syracuseStep 1384679 = 2077019) B2077019
theorem B2335007 : Blo 920579 2335007 := bstep (se 1 (by rfl) ⟨1751255, by rfl⟩ : syracuseStep 2335007 = 3502511) B3502511
theorem B1384841 : Blo 920579 1384841 := bstep (se 2 (by rfl) ⟨519315, by rfl⟩ : syracuseStep 1384841 = 1038631) B1038631
theorem B1384937 : Blo 920579 1384937 := bstep (se 2 (by rfl) ⟨519351, by rfl⟩ : syracuseStep 1384937 = 1038703) B1038703
theorem B5907005 : Blo 920579 5907005 := bstep (se 3 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 5907005 = 2215127) B2215127
theorem B1385063 : Blo 920579 1385063 := bstep (se 1 (by rfl) ⟨1038797, by rfl⟩ : syracuseStep 1385063 = 2077595) B2077595
theorem B1385195 : Blo 920579 1385195 := bstep (se 1 (by rfl) ⟨1038896, by rfl⟩ : syracuseStep 1385195 = 2077793) B2077793
theorem B1385225 : Blo 920579 1385225 := bstep (se 2 (by rfl) ⟨519459, by rfl⟩ : syracuseStep 1385225 = 1038919) B1038919
theorem B42640145 : Blo 920579 42640145 := bstep (se 2 (by rfl) ⟨15990054, by rfl⟩ : syracuseStep 42640145 = 31980109) B31980109
theorem B4662035 : Blo 920579 4662035 := bstep (se 1 (by rfl) ⟨3496526, by rfl⟩ : syracuseStep 4662035 = 6993053) B6993053
theorem B2073401 : Blo 920579 2073401 := bstep (se 2 (by rfl) ⟨777525, by rfl⟩ : syracuseStep 2073401 = 1555051) B1555051
theorem B2073455 : Blo 920579 2073455 := bstep (se 1 (by rfl) ⟨1555091, by rfl⟩ : syracuseStep 2073455 = 3110183) B3110183
theorem B1385327 : Blo 920579 1385327 := bstep (se 1 (by rfl) ⟨1038995, by rfl⟩ : syracuseStep 1385327 = 2077991) B2077991
theorem B2335655 : Blo 920579 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B1385579 : Blo 920579 1385579 := bstep (se 1 (by rfl) ⟨1039184, by rfl⟩ : syracuseStep 1385579 = 2078369) B2078369
theorem B11969693 : Blo 920579 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B11216029 : Blo 920579 11216029 := bstep (se 3 (by rfl) ⟨2103005, by rfl⟩ : syracuseStep 11216029 = 4206011) B4206011
theorem B1385819 : Blo 920579 1385819 := bstep (se 1 (by rfl) ⟨1039364, by rfl⟩ : syracuseStep 1385819 = 2078729) B2078729
theorem B2074031 : Blo 920579 2074031 := bstep (se 1 (by rfl) ⟨1555523, by rfl⟩ : syracuseStep 2074031 = 3111047) B3111047
theorem B1386095 : Blo 920579 1386095 := bstep (se 1 (by rfl) ⟨1039571, by rfl⟩ : syracuseStep 1386095 = 2079143) B2079143
theorem B2959001 : Blo 920579 2959001 := bstep (se 2 (by rfl) ⟨1109625, by rfl⟩ : syracuseStep 2959001 = 2219251) B2219251
theorem B1386167 : Blo 920579 1386167 := bstep (se 1 (by rfl) ⟨1039625, by rfl⟩ : syracuseStep 1386167 = 2079251) B2079251
theorem B1386203 : Blo 920579 1386203 := bstep (se 1 (by rfl) ⟨1039652, by rfl⟩ : syracuseStep 1386203 = 2079305) B2079305
theorem B4204295 : Blo 920579 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B1386377 : Blo 920579 1386377 := bstep (se 2 (by rfl) ⟨519891, by rfl⟩ : syracuseStep 1386377 = 1039783) B1039783
theorem B1386479 : Blo 920579 1386479 := bstep (se 1 (by rfl) ⟨1039859, by rfl⟩ : syracuseStep 1386479 = 2079719) B2079719
theorem B2336759 : Blo 920579 2336759 := bstep (se 1 (by rfl) ⟨1752569, by rfl⟩ : syracuseStep 2336759 = 3505139) B3505139
theorem B16853021 : Blo 920579 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B4991129 : Blo 920579 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B11806883 : Blo 920579 11806883 := bstep (se 1 (by rfl) ⟨8855162, by rfl⟩ : syracuseStep 11806883 = 17710325) B17710325
theorem B5253335 : Blo 920579 5253335 := bstep (se 1 (by rfl) ⟨3940001, by rfl⟩ : syracuseStep 5253335 = 7880003) B7880003
theorem B2074859 : Blo 920579 2074859 := bstep (se 1 (by rfl) ⟨1556144, by rfl⟩ : syracuseStep 2074859 = 3112289) B3112289
theorem B1386731 : Blo 920579 1386731 := bstep (se 1 (by rfl) ⟨1040048, by rfl⟩ : syracuseStep 1386731 = 2080097) B2080097
theorem B1386791 : Blo 920579 1386791 := bstep (se 1 (by rfl) ⟨1040093, by rfl⟩ : syracuseStep 1386791 = 2080187) B2080187
theorem B3942751 : Blo 920579 3942751 := bstep (se 1 (by rfl) ⟨2957063, by rfl⟩ : syracuseStep 3942751 = 5914127) B5914127
theorem B6663311 : Blo 920579 6663311 := bstep (se 1 (by rfl) ⟨4997483, by rfl⟩ : syracuseStep 6663311 = 9994967) B9994967
theorem B17738999 : Blo 920579 17738999 := bstep (se 1 (by rfl) ⟨13304249, by rfl⟩ : syracuseStep 17738999 = 26608499) B26608499
theorem B2338217 : Blo 920579 2338217 := bstep (se 2 (by rfl) ⟨876831, by rfl⟩ : syracuseStep 2338217 = 1753663) B1753663
theorem B2076155 : Blo 920579 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B43232777 : Blo 920579 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B2076335 : Blo 920579 2076335 := bstep (se 1 (by rfl) ⟨1557251, by rfl⟩ : syracuseStep 2076335 = 3114503) B3114503
theorem B2961191 : Blo 920579 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B2338703 : Blo 920579 2338703 := bstep (se 1 (by rfl) ⟨1754027, by rfl⟩ : syracuseStep 2338703 = 3508055) B3508055
theorem B12955697 : Blo 920579 12955697 := bstep (se 2 (by rfl) ⟨4858386, by rfl⟩ : syracuseStep 12955697 = 9716773) B9716773
theorem B2076983 : Blo 920579 2076983 := bstep (se 1 (by rfl) ⟨1557737, by rfl⟩ : syracuseStep 2076983 = 3115475) B3115475
theorem B2077055 : Blo 920579 2077055 := bstep (se 1 (by rfl) ⟨1557791, by rfl⟩ : syracuseStep 2077055 = 3115583) B3115583
theorem B5911051 : Blo 920579 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B1750079 : Blo 920579 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B10663001 : Blo 920579 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B5911667 : Blo 920579 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B23606477 : Blo 920579 23606477 := bstep (se 3 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 23606477 = 8852429) B8852429
theorem B23672087 : Blo 920579 23672087 := bstep (se 1 (by rfl) ⟨17754065, by rfl⟩ : syracuseStep 23672087 = 35508131) B35508131
theorem B1553755 : Blo 920579 1553755 := bstep (se 1 (by rfl) ⟨1165316, by rfl⟩ : syracuseStep 1553755 = 2330633) B2330633
theorem B12006893 : Blo 920579 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B2078279 : Blo 920579 2078279 := bstep (se 1 (by rfl) ⟨1558709, by rfl⟩ : syracuseStep 2078279 = 3117419) B3117419
theorem B5617309 : Blo 920579 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B2078459 : Blo 920579 2078459 := bstep (se 1 (by rfl) ⟨1558844, by rfl⟩ : syracuseStep 2078459 = 3117689) B3117689
theorem B3323929 : Blo 920579 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B6994025 : Blo 920579 6994025 := bstep (se 2 (by rfl) ⟨2622759, by rfl⟩ : syracuseStep 6994025 = 5245519) B5245519
theorem B1751195 : Blo 920579 1751195 := bstep (se 1 (by rfl) ⟨1313396, by rfl⟩ : syracuseStep 1751195 = 2626793) B2626793
theorem B4044971 : Blo 920579 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B1554727 : Blo 920579 1554727 := bstep (se 1 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 1554727 = 2332091) B2332091
theorem B2079017 : Blo 920579 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B35109551 : Blo 920579 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B2079593 : Blo 920579 2079593 := bstep (se 2 (by rfl) ⟨779847, by rfl⟩ : syracuseStep 2079593 = 1559695) B1559695
theorem B2079647 : Blo 920579 2079647 := bstep (se 1 (by rfl) ⟨1559735, by rfl⟩ : syracuseStep 2079647 = 3119471) B3119471
theorem B3849257 : Blo 920579 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1424567 : Blo 920579 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B5258459 : Blo 920579 5258459 := bstep (se 1 (by rfl) ⟨3943844, by rfl⟩ : syracuseStep 5258459 = 7887689) B7887689
theorem B1555679 : Blo 920579 1555679 := bstep (se 1 (by rfl) ⟨1166759, by rfl⟩ : syracuseStep 1555679 = 2333519) B2333519
theorem B4668839 : Blo 920579 4668839 := bstep (se 1 (by rfl) ⟨3501629, by rfl⟩ : syracuseStep 4668839 = 7003259) B7003259
theorem B1621577 : Blo 920579 1621577 := bstep (se 2 (by rfl) ⟨608091, by rfl⟩ : syracuseStep 1621577 = 1216183) B1216183
theorem B3325531 : Blo 920579 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B1556111 : Blo 920579 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B2801479 : Blo 920579 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B1556347 : Blo 920579 1556347 := bstep (se 1 (by rfl) ⟨1167260, by rfl⟩ : syracuseStep 1556347 = 2334521) B2334521
theorem B6995969 : Blo 920579 6995969 := bstep (se 2 (by rfl) ⟨2623488, by rfl⟩ : syracuseStep 6995969 = 5246977) B5246977
theorem B6307865 : Blo 920579 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B21283337 : Blo 920579 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B14992067 : Blo 920579 14992067 := bstep (se 1 (by rfl) ⟨11244050, by rfl⟩ : syracuseStep 14992067 = 22488101) B22488101
theorem B1753913 : Blo 920579 1753913 := bstep (se 2 (by rfl) ⟨657717, by rfl⟩ : syracuseStep 1753913 = 1315435) B1315435
theorem B1753967 : Blo 920579 1753967 := bstep (se 1 (by rfl) ⟨1315475, by rfl⟩ : syracuseStep 1753967 = 2630951) B2630951
theorem B5686159 : Blo 920579 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B1558183 : Blo 920579 1558183 := bstep (se 1 (by rfl) ⟨1168637, by rfl⟩ : syracuseStep 1558183 = 2337275) B2337275
theorem B4736809 : Blo 920579 4736809 := bstep (se 2 (by rfl) ⟨1776303, by rfl⟩ : syracuseStep 4736809 = 3552607) B3552607
theorem B6637477 : Blo 920579 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B4671431 : Blo 920579 4671431 := bstep (se 1 (by rfl) ⟨3503573, by rfl⟩ : syracuseStep 4671431 = 7007147) B7007147
theorem B1329145 : Blo 920579 1329145 := bstep (se 2 (by rfl) ⟨498429, by rfl⟩ : syracuseStep 1329145 = 996859) B996859
theorem B3786761 : Blo 920579 3786761 := bstep (se 2 (by rfl) ⟨1420035, by rfl⟩ : syracuseStep 3786761 = 2840071) B2840071
theorem B1558831 : Blo 920579 1558831 := bstep (se 1 (by rfl) ⟨1169123, by rfl⟩ : syracuseStep 1558831 = 2338247) B2338247
theorem B26560979 : Blo 920579 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B5261831 : Blo 920579 5261831 := bstep (se 1 (by rfl) ⟨3946373, by rfl⟩ : syracuseStep 5261831 = 7892747) B7892747
theorem B28396111 : Blo 920579 28396111 := bstep (se 1 (by rfl) ⟨21297083, by rfl⟩ : syracuseStep 28396111 = 42594167) B42594167
theorem B1559351 : Blo 920579 1559351 := bstep (se 1 (by rfl) ⟨1169513, by rfl⟩ : syracuseStep 1559351 = 2339027) B2339027
theorem B1035751 : Blo 920579 1035751 := bstep (se 1 (by rfl) ⟨776813, by rfl⟩ : syracuseStep 1035751 = 1553627) B1553627
theorem B1560127 : Blo 920579 1560127 := bstep (se 1 (by rfl) ⟨1170095, by rfl⟩ : syracuseStep 1560127 = 2340191) B2340191
theorem B7884377 : Blo 920579 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B23645843 : Blo 920579 23645843 := bstep (se 1 (by rfl) ⟨17734382, by rfl⟩ : syracuseStep 23645843 = 35468765) B35468765
theorem B1036255 : Blo 920579 1036255 := bstep (se 1 (by rfl) ⟨777191, by rfl⟩ : syracuseStep 1036255 = 1554383) B1554383
theorem B1036903 : Blo 920579 1036903 := bstep (se 1 (by rfl) ⟨777677, by rfl⟩ : syracuseStep 1036903 = 1555355) B1555355
theorem B9098009 : Blo 920579 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B6640451 : Blo 920579 6640451 := bstep (se 1 (by rfl) ⟨4980338, by rfl⟩ : syracuseStep 6640451 = 9960677) B9960677
theorem B13293179 : Blo 920579 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B3495737 : Blo 920579 3495737 := bstep (se 2 (by rfl) ⟨1310901, by rfl⟩ : syracuseStep 3495737 = 2621803) B2621803
theorem B3495919 : Blo 920579 3495919 := bstep (se 1 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 3495919 = 5243879) B5243879
theorem B11819641 : Blo 920579 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B2219375 : Blo 920579 2219375 := bstep (se 1 (by rfl) ⟨1664531, by rfl⟩ : syracuseStep 2219375 = 3329063) B3329063
theorem B3497377 : Blo 920579 3497377 := bstep (se 2 (by rfl) ⟨1311516, by rfl⟩ : syracuseStep 3497377 = 2623033) B2623033
theorem B1039963 : Blo 920579 1039963 := bstep (se 1 (by rfl) ⟨779972, by rfl⟩ : syracuseStep 1039963 = 1559945) B1559945
theorem B2219663 : Blo 920579 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B2809723 : Blo 920579 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B4678397 : Blo 920579 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B1107707 : Blo 920579 1107707 := bstep (se 1 (by rfl) ⟨830780, by rfl⟩ : syracuseStep 1107707 = 1661561) B1661561
theorem B3499807 : Blo 920579 3499807 := bstep (se 1 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 3499807 = 5249711) B5249711
theorem B23685209 : Blo 920579 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B1108063 : Blo 920579 1108063 := bstep (se 1 (by rfl) ⟨831047, by rfl⟩ : syracuseStep 1108063 = 1662095) B1662095
theorem B3107051 : Blo 920579 3107051 := bstep (se 1 (by rfl) ⟨2330288, by rfl⟩ : syracuseStep 3107051 = 4660577) B4660577
theorem B14969231 : Blo 920579 14969231 := bstep (se 1 (by rfl) ⟨11226923, by rfl⟩ : syracuseStep 14969231 = 22453847) B22453847
theorem B6646475 : Blo 920579 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B9988919 : Blo 920579 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B4680503 : Blo 920579 4680503 := bstep (se 1 (by rfl) ⟨3510377, by rfl⟩ : syracuseStep 4680503 = 7020755) B7020755
theorem B3108347 : Blo 920579 3108347 := bstep (se 1 (by rfl) ⟨2331260, by rfl⟩ : syracuseStep 3108347 = 4662521) B4662521
theorem B16805501 : Blo 920579 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B3108509 : Blo 920579 3108509 := bstep (se 3 (by rfl) ⟨582845, by rfl⟩ : syracuseStep 3108509 = 1165691) B1165691
theorem B100790081 : Blo 920579 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B3109049 : Blo 920579 3109049 := bstep (se 2 (by rfl) ⟨1165893, by rfl⟩ : syracuseStep 3109049 = 2331787) B2331787
theorem B9959507 : Blo 920579 9959507 := bstep (se 1 (by rfl) ⟨7469630, by rfl⟩ : syracuseStep 9959507 = 14939261) B14939261
theorem B3111155 : Blo 920579 3111155 := bstep (se 1 (by rfl) ⟨2333366, by rfl⟩ : syracuseStep 3111155 = 4666733) B4666733
theorem B3111209 : Blo 920579 3111209 := bstep (se 2 (by rfl) ⟨1166703, by rfl⟩ : syracuseStep 3111209 = 2333407) B2333407
theorem B3112775 : Blo 920579 3112775 := bstep (se 1 (by rfl) ⟨2334581, by rfl⟩ : syracuseStep 3112775 = 4669163) B4669163
theorem B5603197 : Blo 920579 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B3112829 : Blo 920579 3112829 := bstep (se 3 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 3112829 = 1167311) B1167311
theorem B3932347 : Blo 920579 3932347 := bstep (se 1 (by rfl) ⟨2949260, by rfl⟩ : syracuseStep 3932347 = 5898521) B5898521
theorem B14188891 : Blo 920579 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B9994711 : Blo 920579 9994711 := bstep (se 1 (by rfl) ⟨7496033, by rfl⟩ : syracuseStep 9994711 = 14992067) B14992067
theorem B11534969 : Blo 920579 11534969 := bstep (se 2 (by rfl) ⟨4325613, by rfl⟩ : syracuseStep 11534969 = 8651227) B8651227
theorem B5244061 : Blo 920579 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B1311967 : Blo 920579 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B3114287 : Blo 920579 3114287 := bstep (se 1 (by rfl) ⟨2335715, by rfl⟩ : syracuseStep 3114287 = 4671431) B4671431
theorem B5244335 : Blo 920579 5244335 := bstep (se 1 (by rfl) ⟨3933251, by rfl⟩ : syracuseStep 5244335 = 7866503) B7866503
theorem B3507887 : Blo 920579 3507887 := bstep (se 1 (by rfl) ⟨2630915, by rfl⟩ : syracuseStep 3507887 = 5261831) B5261831
theorem B1247015 : Blo 920579 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B1967993 : Blo 920579 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B1312633 : Blo 920579 1312633 := bstep (se 2 (by rfl) ⟨492237, by rfl⟩ : syracuseStep 1312633 = 984475) B984475
theorem B2492603 : Blo 920579 2492603 := bstep (se 1 (by rfl) ⟨1869452, by rfl⟩ : syracuseStep 2492603 = 3738905) B3738905
theorem B14420285 : Blo 920579 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B1771903 : Blo 920579 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B15763895 : Blo 920579 15763895 := bstep (se 1 (by rfl) ⟨11822921, by rfl⟩ : syracuseStep 15763895 = 23645843) B23645843
theorem B7866881 : Blo 920579 7866881 := bstep (se 2 (by rfl) ⟨2950080, by rfl⟩ : syracuseStep 7866881 = 5900161) B5900161
theorem B8849969 : Blo 920579 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B920639 : Blo 920579 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B6065339 : Blo 920579 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B4426967 : Blo 920579 4426967 := bstep (se 1 (by rfl) ⟨3320225, by rfl⟩ : syracuseStep 4426967 = 6640451) B6640451
theorem B2624879 : Blo 920579 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B920959 : Blo 920579 920959 := bstep (se 1 (by rfl) ⟨690719, by rfl⟩ : syracuseStep 920959 = 1381439) B1381439
theorem B920987 : Blo 920579 920987 := bstep (se 1 (by rfl) ⟨690740, by rfl⟩ : syracuseStep 920987 = 1381481) B1381481
theorem B921055 : Blo 920579 921055 := bstep (se 1 (by rfl) ⟨690791, by rfl⟩ : syracuseStep 921055 = 1381583) B1381583
theorem B2624993 : Blo 920579 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B1969633 : Blo 920579 1969633 := bstep (se 2 (by rfl) ⟨738612, by rfl⟩ : syracuseStep 1969633 = 1477225) B1477225
theorem B921191 : Blo 920579 921191 := bstep (se 1 (by rfl) ⟨690893, by rfl⟩ : syracuseStep 921191 = 1381787) B1381787
theorem B921339 : Blo 920579 921339 := bstep (se 1 (by rfl) ⟨691004, by rfl⟩ : syracuseStep 921339 = 1382009) B1382009
theorem B921407 : Blo 920579 921407 := bstep (se 1 (by rfl) ⟨691055, by rfl⟩ : syracuseStep 921407 = 1382111) B1382111
theorem B2330491 : Blo 920579 2330491 := bstep (se 1 (by rfl) ⟨1747868, by rfl⟩ : syracuseStep 2330491 = 3495737) B3495737
theorem B2494331 : Blo 920579 2494331 := bstep (se 1 (by rfl) ⟨1870748, by rfl⟩ : syracuseStep 2494331 = 3741497) B3741497
theorem B921471 : Blo 920579 921471 := bstep (se 1 (by rfl) ⟨691103, by rfl⟩ : syracuseStep 921471 = 1382207) B1382207
theorem B921583 : Blo 920579 921583 := bstep (se 1 (by rfl) ⟨691187, by rfl⟩ : syracuseStep 921583 = 1382375) B1382375
theorem B921595 : Blo 920579 921595 := bstep (se 1 (by rfl) ⟨691196, by rfl⟩ : syracuseStep 921595 = 1382393) B1382393
theorem B921663 : Blo 920579 921663 := bstep (se 1 (by rfl) ⟨691247, by rfl⟩ : syracuseStep 921663 = 1382495) B1382495
theorem B1314911 : Blo 920579 1314911 := bstep (se 1 (by rfl) ⟨986183, by rfl⟩ : syracuseStep 1314911 = 1972367) B1972367
theorem B921703 : Blo 920579 921703 := bstep (se 1 (by rfl) ⟨691277, by rfl⟩ : syracuseStep 921703 = 1382555) B1382555
theorem B921727 : Blo 920579 921727 := bstep (se 1 (by rfl) ⟨691295, by rfl⟩ : syracuseStep 921727 = 1382591) B1382591
theorem B921755 : Blo 920579 921755 := bstep (se 1 (by rfl) ⟨691316, by rfl⟩ : syracuseStep 921755 = 1382633) B1382633
theorem B1314991 : Blo 920579 1314991 := bstep (se 1 (by rfl) ⟨986243, by rfl⟩ : syracuseStep 1314991 = 1972487) B1972487
theorem B921959 : Blo 920579 921959 := bstep (se 1 (by rfl) ⟨691469, by rfl⟩ : syracuseStep 921959 = 1382939) B1382939
theorem B3150199 : Blo 920579 3150199 := bstep (se 1 (by rfl) ⟨2362649, by rfl⟩ : syracuseStep 3150199 = 4725299) B4725299
theorem B922011 : Blo 920579 922011 := bstep (se 1 (by rfl) ⟨691508, by rfl⟩ : syracuseStep 922011 = 1383017) B1383017
theorem B2953783 : Blo 920579 2953783 := bstep (se 1 (by rfl) ⟨2215337, by rfl⟩ : syracuseStep 2953783 = 4430675) B4430675
theorem B2626121 : Blo 920579 2626121 := bstep (se 2 (by rfl) ⟨984795, by rfl⟩ : syracuseStep 2626121 = 1969591) B1969591
theorem B1381001 : Blo 920579 1381001 := bstep (se 2 (by rfl) ⟨517875, by rfl⟩ : syracuseStep 1381001 = 1035751) B1035751
theorem B922363 : Blo 920579 922363 := bstep (se 1 (by rfl) ⟨691772, by rfl⟩ : syracuseStep 922363 = 1383545) B1383545
theorem B922431 : Blo 920579 922431 := bstep (se 1 (by rfl) ⟨691823, by rfl⟩ : syracuseStep 922431 = 1383647) B1383647
theorem B4002643 : Blo 920579 4002643 := bstep (se 1 (by rfl) ⟨3001982, by rfl⟩ : syracuseStep 4002643 = 6003965) B6003965
theorem B1381211 : Blo 920579 1381211 := bstep (se 1 (by rfl) ⟨1035908, by rfl⟩ : syracuseStep 1381211 = 2071817) B2071817
theorem B922459 : Blo 920579 922459 := bstep (se 1 (by rfl) ⟨691844, by rfl⟩ : syracuseStep 922459 = 1383689) B1383689
theorem B922527 : Blo 920579 922527 := bstep (se 1 (by rfl) ⟨691895, by rfl⟩ : syracuseStep 922527 = 1383791) B1383791
theorem B1479583 : Blo 920579 1479583 := bstep (se 1 (by rfl) ⟨1109687, by rfl⟩ : syracuseStep 1479583 = 2219375) B2219375
theorem B922607 : Blo 920579 922607 := bstep (se 1 (by rfl) ⟨691955, by rfl⟩ : syracuseStep 922607 = 1383911) B1383911
theorem B922695 : Blo 920579 922695 := bstep (se 1 (by rfl) ⟨692021, by rfl⟩ : syracuseStep 922695 = 1384043) B1384043
theorem B922779 : Blo 920579 922779 := bstep (se 1 (by rfl) ⟨692084, by rfl⟩ : syracuseStep 922779 = 1384169) B1384169
theorem B922875 : Blo 920579 922875 := bstep (se 1 (by rfl) ⟨692156, by rfl⟩ : syracuseStep 922875 = 1384313) B1384313
theorem B1381673 : Blo 920579 1381673 := bstep (se 2 (by rfl) ⟨518127, by rfl⟩ : syracuseStep 1381673 = 1036255) B1036255
theorem B922943 : Blo 920579 922943 := bstep (se 1 (by rfl) ⟨692207, by rfl⟩ : syracuseStep 922943 = 1384415) B1384415
theorem B10098029 : Blo 920579 10098029 := bstep (se 3 (by rfl) ⟨1893380, by rfl⟩ : syracuseStep 10098029 = 3786761) B3786761
theorem B923111 : Blo 920579 923111 := bstep (se 1 (by rfl) ⟨692333, by rfl⟩ : syracuseStep 923111 = 1384667) B1384667
theorem B1381871 : Blo 920579 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B923119 : Blo 920579 923119 := bstep (se 1 (by rfl) ⟨692339, by rfl⟩ : syracuseStep 923119 = 1384679) B1384679
theorem B923227 : Blo 920579 923227 := bstep (se 1 (by rfl) ⟨692420, by rfl⟩ : syracuseStep 923227 = 1384841) B1384841
theorem B923291 : Blo 920579 923291 := bstep (se 1 (by rfl) ⟨692468, by rfl⟩ : syracuseStep 923291 = 1384937) B1384937
theorem B3938003 : Blo 920579 3938003 := bstep (se 1 (by rfl) ⟨2953502, by rfl⟩ : syracuseStep 3938003 = 5907005) B5907005
theorem B923375 : Blo 920579 923375 := bstep (se 1 (by rfl) ⟨692531, by rfl⟩ : syracuseStep 923375 = 1385063) B1385063
theorem B923463 : Blo 920579 923463 := bstep (se 1 (by rfl) ⟨692597, by rfl⟩ : syracuseStep 923463 = 1385195) B1385195
theorem B3118931 : Blo 920579 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B923483 : Blo 920579 923483 := bstep (se 1 (by rfl) ⟨692612, by rfl⟩ : syracuseStep 923483 = 1385225) B1385225
theorem B1382267 : Blo 920579 1382267 := bstep (se 1 (by rfl) ⟨1036700, by rfl⟩ : syracuseStep 1382267 = 2073401) B2073401
theorem B1382303 : Blo 920579 1382303 := bstep (se 1 (by rfl) ⟨1036727, by rfl⟩ : syracuseStep 1382303 = 2073455) B2073455
theorem B923551 : Blo 920579 923551 := bstep (se 1 (by rfl) ⟨692663, by rfl⟩ : syracuseStep 923551 = 1385327) B1385327
theorem B923719 : Blo 920579 923719 := bstep (se 1 (by rfl) ⟨692789, by rfl⟩ : syracuseStep 923719 = 1385579) B1385579
theorem B1382537 : Blo 920579 1382537 := bstep (se 2 (by rfl) ⟨518451, by rfl⟩ : syracuseStep 1382537 = 1036903) B1036903
theorem B923879 : Blo 920579 923879 := bstep (se 1 (by rfl) ⟨692909, by rfl⟩ : syracuseStep 923879 = 1385819) B1385819
theorem B1382687 : Blo 920579 1382687 := bstep (se 1 (by rfl) ⟨1037015, by rfl⟩ : syracuseStep 1382687 = 2074031) B2074031
theorem B924063 : Blo 920579 924063 := bstep (se 1 (by rfl) ⟨693047, by rfl⟩ : syracuseStep 924063 = 1386095) B1386095
theorem B1972667 : Blo 920579 1972667 := bstep (se 1 (by rfl) ⟨1479500, by rfl⟩ : syracuseStep 1972667 = 2959001) B2959001
theorem B924111 : Blo 920579 924111 := bstep (se 1 (by rfl) ⟨693083, by rfl⟩ : syracuseStep 924111 = 1386167) B1386167
theorem B924135 : Blo 920579 924135 := bstep (se 1 (by rfl) ⟨693101, by rfl⟩ : syracuseStep 924135 = 1386203) B1386203
theorem B924251 : Blo 920579 924251 := bstep (se 1 (by rfl) ⟨693188, by rfl⟩ : syracuseStep 924251 = 1386377) B1386377
theorem B924319 : Blo 920579 924319 := bstep (se 1 (by rfl) ⟨693239, by rfl⟩ : syracuseStep 924319 = 1386479) B1386479
theorem B7871255 : Blo 920579 7871255 := bstep (se 1 (by rfl) ⟨5903441, by rfl⟩ : syracuseStep 7871255 = 11806883) B11806883
theorem B2071367 : Blo 920579 2071367 := bstep (se 1 (by rfl) ⟨1553525, by rfl⟩ : syracuseStep 2071367 = 3107051) B3107051
theorem B1383239 : Blo 920579 1383239 := bstep (se 1 (by rfl) ⟨1037429, by rfl⟩ : syracuseStep 1383239 = 2074859) B2074859
theorem B924487 : Blo 920579 924487 := bstep (se 1 (by rfl) ⟨693365, by rfl⟩ : syracuseStep 924487 = 1386731) B1386731
theorem B924527 : Blo 920579 924527 := bstep (se 1 (by rfl) ⟨693395, by rfl⟩ : syracuseStep 924527 = 1386791) B1386791
theorem B2071673 : Blo 920579 2071673 := bstep (se 2 (by rfl) ⟨776877, by rfl⟩ : syracuseStep 2071673 = 1553755) B1553755
theorem B4430983 : Blo 920579 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B6659279 : Blo 920579 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B3120335 : Blo 920579 3120335 := bstep (se 1 (by rfl) ⟨2340251, by rfl⟩ : syracuseStep 3120335 = 4680503) B4680503
theorem B2072231 : Blo 920579 2072231 := bstep (se 1 (by rfl) ⟨1554173, by rfl⟩ : syracuseStep 2072231 = 3108347) B3108347
theorem B1384103 : Blo 920579 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B2072339 : Blo 920579 2072339 := bstep (se 1 (by rfl) ⟨1554254, by rfl⟩ : syracuseStep 2072339 = 3108509) B3108509
theorem B1384223 : Blo 920579 1384223 := bstep (se 1 (by rfl) ⟨1038167, by rfl⟩ : syracuseStep 1384223 = 2076335) B2076335
theorem B1974127 : Blo 920579 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B4661225 : Blo 920579 4661225 := bstep (se 2 (by rfl) ⟨1747959, by rfl⟩ : syracuseStep 4661225 = 3495919) B3495919
theorem B4431905 : Blo 920579 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B2072699 : Blo 920579 2072699 := bstep (se 1 (by rfl) ⟨1554524, by rfl⟩ : syracuseStep 2072699 = 3109049) B3109049
theorem B4989053 : Blo 920579 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1384655 : Blo 920579 1384655 := bstep (se 1 (by rfl) ⟨1038491, by rfl⟩ : syracuseStep 1384655 = 2076983) B2076983
theorem B1384703 : Blo 920579 1384703 := bstep (se 1 (by rfl) ⟨1038527, by rfl⟩ : syracuseStep 1384703 = 2077055) B2077055
theorem B2072969 : Blo 920579 2072969 := bstep (se 2 (by rfl) ⟨777363, by rfl⟩ : syracuseStep 2072969 = 1554727) B1554727
theorem B3941111 : Blo 920579 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B15737651 : Blo 920579 15737651 := bstep (se 1 (by rfl) ⟨11803238, by rfl⟩ : syracuseStep 15737651 = 23606477) B23606477
theorem B8004595 : Blo 920579 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B1385519 : Blo 920579 1385519 := bstep (se 1 (by rfl) ⟨1039139, by rfl⟩ : syracuseStep 1385519 = 2078279) B2078279
theorem B1385639 : Blo 920579 1385639 := bstep (se 1 (by rfl) ⟨1039229, by rfl⟩ : syracuseStep 1385639 = 2078459) B2078459
theorem B3941693 : Blo 920579 3941693 := bstep (se 3 (by rfl) ⟨739067, by rfl⟩ : syracuseStep 3941693 = 1478135) B1478135
theorem B4662683 : Blo 920579 4662683 := bstep (se 1 (by rfl) ⟨3497012, by rfl⟩ : syracuseStep 4662683 = 6994025) B6994025
theorem B2696647 : Blo 920579 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B2074103 : Blo 920579 2074103 := bstep (se 1 (by rfl) ⟨1555577, by rfl⟩ : syracuseStep 2074103 = 3111155) B3111155
theorem B2074139 : Blo 920579 2074139 := bstep (se 1 (by rfl) ⟨1555604, by rfl⟩ : syracuseStep 2074139 = 3111209) B3111209
theorem B1386011 : Blo 920579 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B23406367 : Blo 920579 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B4663169 : Blo 920579 4663169 := bstep (se 2 (by rfl) ⟨1748688, by rfl⟩ : syracuseStep 4663169 = 3497377) B3497377
theorem B1386395 : Blo 920579 1386395 := bstep (se 1 (by rfl) ⟨1039796, by rfl⟩ : syracuseStep 1386395 = 2079593) B2079593
theorem B1386431 : Blo 920579 1386431 := bstep (se 1 (by rfl) ⟨1039823, by rfl⟩ : syracuseStep 1386431 = 2079647) B2079647
theorem B2566171 : Blo 920579 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B4434041 : Blo 920579 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B1386617 : Blo 920579 1386617 := bstep (se 2 (by rfl) ⟨519981, by rfl⟩ : syracuseStep 1386617 = 1039963) B1039963
theorem B2632009 : Blo 920579 2632009 := bstep (se 2 (by rfl) ⟨987003, by rfl⟩ : syracuseStep 2632009 = 1974007) B1974007
theorem B2075129 : Blo 920579 2075129 := bstep (se 2 (by rfl) ⟨778173, by rfl⟩ : syracuseStep 2075129 = 1556347) B1556347
theorem B3746297 : Blo 920579 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B28355093 : Blo 920579 28355093 := bstep (se 6 (by rfl) ⟨664572, by rfl⟩ : syracuseStep 28355093 = 1329145) B1329145
theorem B2075183 : Blo 920579 2075183 := bstep (se 1 (by rfl) ⟨1556387, by rfl⟩ : syracuseStep 2075183 = 3112775) B3112775
theorem B2075219 : Blo 920579 2075219 := bstep (se 1 (by rfl) ⟨1556414, by rfl⟩ : syracuseStep 2075219 = 3112829) B3112829
theorem B4663979 : Blo 920579 4663979 := bstep (se 1 (by rfl) ⟨3497984, by rfl⟩ : syracuseStep 4663979 = 6995969) B6995969
theorem B4205243 : Blo 920579 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B2075399 : Blo 920579 2075399 := bstep (se 1 (by rfl) ⟨1556549, by rfl⟩ : syracuseStep 2075399 = 3113099) B3113099
theorem B2075615 : Blo 920579 2075615 := bstep (se 1 (by rfl) ⟨1556711, by rfl⟩ : syracuseStep 2075615 = 3113423) B3113423
theorem B6663197 : Blo 920579 6663197 := bstep (se 3 (by rfl) ⟨1249349, by rfl⟩ : syracuseStep 6663197 = 2498699) B2498699
theorem B5909669 : Blo 920579 5909669 := bstep (se 4 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 5909669 = 1108063) B1108063
theorem B2075831 : Blo 920579 2075831 := bstep (se 1 (by rfl) ⟨1556873, by rfl⟩ : syracuseStep 2075831 = 3113747) B3113747
theorem B1748233 : Blo 920579 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B1748279 : Blo 920579 1748279 := bstep (se 1 (by rfl) ⟨1311209, by rfl⟩ : syracuseStep 1748279 = 2622419) B2622419
theorem B2076407 : Blo 920579 2076407 := bstep (se 1 (by rfl) ⟨1557305, by rfl⟩ : syracuseStep 2076407 = 3114611) B3114611
theorem B2076479 : Blo 920579 2076479 := bstep (se 1 (by rfl) ⟨1557359, by rfl⟩ : syracuseStep 2076479 = 3114719) B3114719
theorem B7581545 : Blo 920579 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B2076587 : Blo 920579 2076587 := bstep (se 1 (by rfl) ⟨1557440, by rfl⟩ : syracuseStep 2076587 = 3114881) B3114881
theorem B14954705 : Blo 920579 14954705 := bstep (se 2 (by rfl) ⟨5608014, by rfl⟩ : syracuseStep 14954705 = 11216029) B11216029
theorem B2076947 : Blo 920579 2076947 := bstep (se 1 (by rfl) ⟨1557710, by rfl⟩ : syracuseStep 2076947 = 3115421) B3115421
theorem B17707319 : Blo 920579 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B2077127 : Blo 920579 2077127 := bstep (se 1 (by rfl) ⟨1557845, by rfl⟩ : syracuseStep 2077127 = 3115691) B3115691
theorem B2077487 : Blo 920579 2077487 := bstep (se 1 (by rfl) ⟨1558115, by rfl⟩ : syracuseStep 2077487 = 3116231) B3116231
theorem B2077577 : Blo 920579 2077577 := bstep (se 2 (by rfl) ⟨779091, by rfl⟩ : syracuseStep 2077577 = 1558183) B1558183
theorem B4666409 : Blo 920579 4666409 := bstep (se 2 (by rfl) ⟨1749903, by rfl⟩ : syracuseStep 4666409 = 3499807) B3499807
theorem B5256251 : Blo 920579 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B2078351 : Blo 920579 2078351 := bstep (se 1 (by rfl) ⟨1558763, by rfl⟩ : syracuseStep 2078351 = 3117527) B3117527
theorem B2078441 : Blo 920579 2078441 := bstep (se 2 (by rfl) ⟨779415, by rfl⟩ : syracuseStep 2078441 = 1558831) B1558831
theorem B5257001 : Blo 920579 5257001 := bstep (se 2 (by rfl) ⟨1971375, by rfl⟩ : syracuseStep 5257001 = 3942751) B3942751
theorem B37861481 : Blo 920579 37861481 := bstep (se 2 (by rfl) ⟨14198055, by rfl⟩ : syracuseStep 37861481 = 28396111) B28396111
theorem B8862119 : Blo 920579 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B2079323 : Blo 920579 2079323 := bstep (se 1 (by rfl) ⟨1559492, by rfl⟩ : syracuseStep 2079323 = 3118985) B3118985
theorem B2079467 : Blo 920579 2079467 := bstep (se 1 (by rfl) ⟨1559600, by rfl⟩ : syracuseStep 2079467 = 3119201) B3119201
theorem B1555247 : Blo 920579 1555247 := bstep (se 1 (by rfl) ⟨1166435, by rfl⟩ : syracuseStep 1555247 = 2332871) B2332871
theorem B15777017 : Blo 920579 15777017 := bstep (se 2 (by rfl) ⟨5916381, by rfl⟩ : syracuseStep 15777017 = 11832763) B11832763
theorem B2080079 : Blo 920579 2080079 := bstep (se 1 (by rfl) ⟨1560059, by rfl⟩ : syracuseStep 2080079 = 3120119) B3120119
theorem B2080169 : Blo 920579 2080169 := bstep (se 2 (by rfl) ⟨780063, by rfl⟩ : syracuseStep 2080169 = 1560127) B1560127
theorem B4439747 : Blo 920579 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B1752911 : Blo 920579 1752911 := bstep (se 1 (by rfl) ⟨1314683, by rfl⟩ : syracuseStep 1752911 = 2629367) B2629367
theorem B1556671 : Blo 920579 1556671 := bstep (se 1 (by rfl) ⟨1167503, by rfl⟩ : syracuseStep 1556671 = 2335007) B2335007
theorem B28426763 : Blo 920579 28426763 := bstep (se 1 (by rfl) ⟨21320072, by rfl⟩ : syracuseStep 28426763 = 42640145) B42640145
theorem B1557103 : Blo 920579 1557103 := bstep (se 1 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 1557103 = 2335655) B2335655
theorem B7881401 : Blo 920579 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B7979795 : Blo 920579 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B2802863 : Blo 920579 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B1557839 : Blo 920579 1557839 := bstep (se 1 (by rfl) ⟨1168379, by rfl⟩ : syracuseStep 1557839 = 2336759) B2336759
theorem B3327419 : Blo 920579 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B9979487 : Blo 920579 9979487 := bstep (se 1 (by rfl) ⟨7484615, by rfl⟩ : syracuseStep 9979487 = 14969231) B14969231
theorem B4442207 : Blo 920579 4442207 := bstep (se 1 (by rfl) ⟨3331655, by rfl⟩ : syracuseStep 4442207 = 6663311) B6663311
theorem B7489745 : Blo 920579 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B1558811 : Blo 920579 1558811 := bstep (se 1 (by rfl) ⟨1169108, by rfl⟩ : syracuseStep 1558811 = 2338217) B2338217
theorem B28821851 : Blo 920579 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B67193387 : Blo 920579 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B1559135 : Blo 920579 1559135 := bstep (se 1 (by rfl) ⟨1169351, by rfl⟩ : syracuseStep 1559135 = 2338703) B2338703
theorem B11815541 : Blo 920579 11815541 := bstep (se 5 (by rfl) ⟨553853, by rfl⟩ : syracuseStep 11815541 = 1107707) B1107707
theorem B8637131 : Blo 920579 8637131 := bstep (se 1 (by rfl) ⟨6477848, by rfl⟩ : syracuseStep 8637131 = 12955697) B12955697
theorem B1166719 : Blo 920579 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B15781391 : Blo 920579 15781391 := bstep (se 1 (by rfl) ⟨11836043, by rfl⟩ : syracuseStep 15781391 = 23672087) B23672087
theorem B6639671 : Blo 920579 6639671 := bstep (se 1 (by rfl) ⟨4979753, by rfl⟩ : syracuseStep 6639671 = 9959507) B9959507
theorem B1167463 : Blo 920579 1167463 := bstep (se 1 (by rfl) ⟨875597, by rfl⟩ : syracuseStep 1167463 = 1751195) B1751195
theorem B5919101 : Blo 920579 5919101 := bstep (se 3 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 5919101 = 2219663) B2219663
theorem B1037119 : Blo 920579 1037119 := bstep (se 1 (by rfl) ⟨777839, by rfl⟩ : syracuseStep 1037119 = 1555679) B1555679
theorem B1037407 : Blo 920579 1037407 := bstep (se 1 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 1037407 = 1556111) B1556111
theorem B1169311 : Blo 920579 1169311 := bstep (se 1 (by rfl) ⟨876983, by rfl⟩ : syracuseStep 1169311 = 1753967) B1753967
theorem B3495905 : Blo 920579 3495905 := bstep (se 2 (by rfl) ⟨1310964, by rfl⟩ : syracuseStep 3495905 = 2621929) B2621929
theorem B26564669 : Blo 920579 26564669 := bstep (se 3 (by rfl) ⟨4980875, by rfl⟩ : syracuseStep 26564669 = 9961751) B9961751
theorem B1661215 : Blo 920579 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B4676615 : Blo 920579 4676615 := bstep (se 1 (by rfl) ⟨3507461, by rfl⟩ : syracuseStep 4676615 = 7014923) B7014923
theorem B1039567 : Blo 920579 1039567 := bstep (se 1 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 1039567 = 1559351) B1559351
theorem B4677101 : Blo 920579 4677101 := bstep (se 3 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 4677101 = 1753913) B1753913
theorem B16867025 : Blo 920579 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B6315745 : Blo 920579 6315745 := bstep (se 2 (by rfl) ⟨2368404, by rfl⟩ : syracuseStep 6315745 = 4736809) B4736809
theorem B7888751 : Blo 920579 7888751 := bstep (se 1 (by rfl) ⟨5916563, by rfl⟩ : syracuseStep 7888751 = 11833127) B11833127
theorem B4677911 : Blo 920579 4677911 := bstep (se 1 (by rfl) ⟨3508433, by rfl⟩ : syracuseStep 4677911 = 7016867) B7016867
theorem B8872577 : Blo 920579 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B7890149 : Blo 920579 7890149 := bstep (se 4 (by rfl) ⟨739701, by rfl⟩ : syracuseStep 7890149 = 1479403) B1479403
theorem B3499321 : Blo 920579 3499321 := bstep (se 2 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 3499321 = 2624491) B2624491
theorem B4679531 : Blo 920579 4679531 := bstep (se 1 (by rfl) ⟨3509648, by rfl⟩ : syracuseStep 4679531 = 7019297) B7019297
theorem B15755147 : Blo 920579 15755147 := bstep (se 1 (by rfl) ⟨11816360, by rfl⟩ : syracuseStep 15755147 = 23632721) B23632721
theorem B23619599 : Blo 920579 23619599 := bstep (se 1 (by rfl) ⟨17714699, by rfl⟩ : syracuseStep 23619599 = 35429399) B35429399
theorem B3107375 : Blo 920579 3107375 := bstep (se 1 (by rfl) ⟨2330531, by rfl⟩ : syracuseStep 3107375 = 4661063) B4661063
theorem B3108023 : Blo 920579 3108023 := bstep (se 1 (by rfl) ⟨2331017, by rfl⟩ : syracuseStep 3108023 = 4662035) B4662035
theorem B10513637 : Blo 920579 10513637 := bstep (se 4 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 10513637 = 1971307) B1971307
theorem B11235347 : Blo 920579 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B15790139 : Blo 920579 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B3502223 : Blo 920579 3502223 := bstep (se 1 (by rfl) ⟨2626667, by rfl⟩ : syracuseStep 3502223 = 5253335) B5253335
theorem B11825999 : Blo 920579 11825999 := bstep (se 1 (by rfl) ⟨8869499, by rfl⟩ : syracuseStep 11825999 = 17738999) B17738999
theorem B11203667 : Blo 920579 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B3798845 : Blo 920579 3798845 := bstep (se 3 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 3798845 = 1424567) B1424567
theorem B7108667 : Blo 920579 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B15759521 : Blo 920579 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B4324205 : Blo 920579 4324205 := bstep (se 3 (by rfl) ⟨810788, by rfl⟩ : syracuseStep 4324205 = 1621577) B1621577
theorem B3505639 : Blo 920579 3505639 := bstep (se 1 (by rfl) ⟨2629229, by rfl⟩ : syracuseStep 3505639 = 5258459) B5258459
theorem B3112559 : Blo 920579 3112559 := bstep (se 1 (by rfl) ⟨2334419, by rfl⟩ : syracuseStep 3112559 = 4668839) B4668839
theorem B3735305 : Blo 920579 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B7470929 : Blo 920579 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B5243129 : Blo 920579 5243129 := bstep (se 2 (by rfl) ⟨1966173, by rfl⟩ : syracuseStep 5243129 = 3932347) B3932347
theorem B3506429 : Blo 920579 3506429 := bstep (se 3 (by rfl) ⟨657455, by rfl⟩ : syracuseStep 3506429 = 1314911) B1314911
theorem B6652991 : Blo 920579 6652991 := bstep (se 1 (by rfl) ⟨4989743, by rfl⟩ : syracuseStep 6652991 = 9979487) B9979487
theorem B1311995 : Blo 920579 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B5244587 : Blo 920579 5244587 := bstep (se 1 (by rfl) ⟨3933440, by rfl⟩ : syracuseStep 5244587 = 7866881) B7866881
theorem B44795591 : Blo 920579 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B5899979 : Blo 920579 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B2951311 : Blo 920579 2951311 := bstep (se 1 (by rfl) ⟨2213483, by rfl⟩ : syracuseStep 2951311 = 4426967) B4426967
theorem B10520927 : Blo 920579 10520927 := bstep (se 1 (by rfl) ⟨7890695, by rfl⟩ : syracuseStep 10520927 = 15781391) B15781391
theorem B4426447 : Blo 920579 4426447 := bstep (se 1 (by rfl) ⟨3319835, by rfl⟩ : syracuseStep 4426447 = 6639671) B6639671
theorem B920667 : Blo 920579 920667 := bstep (se 1 (by rfl) ⟨690500, by rfl⟩ : syracuseStep 920667 = 1381001) B1381001
theorem B3509345 : Blo 920579 3509345 := bstep (se 2 (by rfl) ⟨1316004, by rfl⟩ : syracuseStep 3509345 = 2632009) B2632009
theorem B7474301 : Blo 920579 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B2362537 : Blo 920579 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B920807 : Blo 920579 920807 := bstep (se 1 (by rfl) ⟨690605, by rfl⟩ : syracuseStep 920807 = 1381211) B1381211
theorem B921115 : Blo 920579 921115 := bstep (se 1 (by rfl) ⟨690836, by rfl⟩ : syracuseStep 921115 = 1381673) B1381673
theorem B921247 : Blo 920579 921247 := bstep (se 1 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 921247 = 1381871) B1381871
theorem B2625335 : Blo 920579 2625335 := bstep (se 1 (by rfl) ⟨1969001, by rfl⟩ : syracuseStep 2625335 = 3938003) B3938003
theorem B921511 : Blo 920579 921511 := bstep (se 1 (by rfl) ⟨691133, by rfl⟩ : syracuseStep 921511 = 1382267) B1382267
theorem B921535 : Blo 920579 921535 := bstep (se 1 (by rfl) ⟨691151, by rfl⟩ : syracuseStep 921535 = 1382303) B1382303
theorem B2330603 : Blo 920579 2330603 := bstep (se 1 (by rfl) ⟨1747952, by rfl⟩ : syracuseStep 2330603 = 3495905) B3495905
theorem B921691 : Blo 920579 921691 := bstep (se 1 (by rfl) ⟨691268, by rfl⟩ : syracuseStep 921691 = 1382537) B1382537
theorem B921791 : Blo 920579 921791 := bstep (se 1 (by rfl) ⟨691343, by rfl⟩ : syracuseStep 921791 = 1382687) B1382687
theorem B1315111 : Blo 920579 1315111 := bstep (se 1 (by rfl) ⟨986333, by rfl⟩ : syracuseStep 1315111 = 1972667) B1972667
theorem B2330977 : Blo 920579 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B5247503 : Blo 920579 5247503 := bstep (se 1 (by rfl) ⟨3935627, by rfl⟩ : syracuseStep 5247503 = 7871255) B7871255
theorem B1380911 : Blo 920579 1380911 := bstep (se 1 (by rfl) ⟨1035683, by rfl⟩ : syracuseStep 1380911 = 2071367) B2071367
theorem B922159 : Blo 920579 922159 := bstep (se 1 (by rfl) ⟨691619, by rfl⟩ : syracuseStep 922159 = 1383239) B1383239
theorem B2626177 : Blo 920579 2626177 := bstep (se 2 (by rfl) ⟨984816, by rfl⟩ : syracuseStep 2626177 = 1969633) B1969633
theorem B3117743 : Blo 920579 3117743 := bstep (se 1 (by rfl) ⟨2338307, by rfl⟩ : syracuseStep 3117743 = 4676615) B4676615
theorem B1381115 : Blo 920579 1381115 := bstep (se 1 (by rfl) ⟨1035836, by rfl⟩ : syracuseStep 1381115 = 2071673) B2071673
theorem B3118067 : Blo 920579 3118067 := bstep (se 1 (by rfl) ⟨2338550, by rfl⟩ : syracuseStep 3118067 = 4677101) B4677101
theorem B1381487 : Blo 920579 1381487 := bstep (se 1 (by rfl) ⟨1036115, by rfl⟩ : syracuseStep 1381487 = 2072231) B2072231
theorem B922735 : Blo 920579 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B11244683 : Blo 920579 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B1381559 : Blo 920579 1381559 := bstep (se 1 (by rfl) ⟨1036169, by rfl⟩ : syracuseStep 1381559 = 2072339) B2072339
theorem B922815 : Blo 920579 922815 := bstep (se 1 (by rfl) ⟨692111, by rfl⟩ : syracuseStep 922815 = 1384223) B1384223
theorem B2954603 : Blo 920579 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B1381799 : Blo 920579 1381799 := bstep (se 1 (by rfl) ⟨1036349, by rfl⟩ : syracuseStep 1381799 = 2072699) B2072699
theorem B923103 : Blo 920579 923103 := bstep (se 1 (by rfl) ⟨692327, by rfl⟩ : syracuseStep 923103 = 1384655) B1384655
theorem B923135 : Blo 920579 923135 := bstep (se 1 (by rfl) ⟨692351, by rfl⟩ : syracuseStep 923135 = 1384703) B1384703
theorem B3118607 : Blo 920579 3118607 := bstep (se 1 (by rfl) ⟨2338955, by rfl⟩ : syracuseStep 3118607 = 4677911) B4677911
theorem B1381979 : Blo 920579 1381979 := bstep (se 1 (by rfl) ⟨1036484, by rfl⟩ : syracuseStep 1381979 = 2072969) B2072969
theorem B4200265 : Blo 920579 4200265 := bstep (se 2 (by rfl) ⟨1575099, by rfl⟩ : syracuseStep 4200265 = 3150199) B3150199
theorem B2627407 : Blo 920579 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B10491767 : Blo 920579 10491767 := bstep (se 1 (by rfl) ⟨7868825, by rfl⟩ : syracuseStep 10491767 = 15737651) B15737651
theorem B923679 : Blo 920579 923679 := bstep (se 1 (by rfl) ⟨692759, by rfl⟩ : syracuseStep 923679 = 1385519) B1385519
theorem B3938377 : Blo 920579 3938377 := bstep (se 2 (by rfl) ⟨1476891, by rfl⟩ : syracuseStep 3938377 = 2953783) B2953783
theorem B923759 : Blo 920579 923759 := bstep (se 1 (by rfl) ⟨692819, by rfl⟩ : syracuseStep 923759 = 1385639) B1385639
theorem B2627795 : Blo 920579 2627795 := bstep (se 1 (by rfl) ⟨1970846, by rfl⟩ : syracuseStep 2627795 = 3941693) B3941693
theorem B1382735 : Blo 920579 1382735 := bstep (se 1 (by rfl) ⟨1037051, by rfl⟩ : syracuseStep 1382735 = 2074103) B2074103
theorem B1382759 : Blo 920579 1382759 := bstep (se 1 (by rfl) ⟨1037069, by rfl⟩ : syracuseStep 1382759 = 2074139) B2074139
theorem B924007 : Blo 920579 924007 := bstep (se 1 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 924007 = 1386011) B1386011
theorem B1382825 : Blo 920579 1382825 := bstep (se 2 (by rfl) ⟨518559, by rfl⟩ : syracuseStep 1382825 = 1037119) B1037119
theorem B1972777 : Blo 920579 1972777 := bstep (se 2 (by rfl) ⟨739791, by rfl⟩ : syracuseStep 1972777 = 1479583) B1479583
theorem B3119687 : Blo 920579 3119687 := bstep (se 1 (by rfl) ⟨2339765, by rfl⟩ : syracuseStep 3119687 = 4679531) B4679531
theorem B924263 : Blo 920579 924263 := bstep (se 1 (by rfl) ⟨693197, by rfl⟩ : syracuseStep 924263 = 1386395) B1386395
theorem B924287 : Blo 920579 924287 := bstep (se 1 (by rfl) ⟨693215, by rfl⟩ : syracuseStep 924287 = 1386431) B1386431
theorem B2956027 : Blo 920579 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B924411 : Blo 920579 924411 := bstep (se 1 (by rfl) ⟨693308, by rfl⟩ : syracuseStep 924411 = 1386617) B1386617
theorem B1383209 : Blo 920579 1383209 := bstep (se 2 (by rfl) ⟨518703, by rfl⟩ : syracuseStep 1383209 = 1037407) B1037407
theorem B1383419 : Blo 920579 1383419 := bstep (se 1 (by rfl) ⟨1037564, by rfl⟩ : syracuseStep 1383419 = 2075129) B2075129
theorem B2071583 : Blo 920579 2071583 := bstep (se 1 (by rfl) ⟨1553687, by rfl⟩ : syracuseStep 2071583 = 3107375) B3107375
theorem B1383455 : Blo 920579 1383455 := bstep (se 1 (by rfl) ⟨1037591, by rfl⟩ : syracuseStep 1383455 = 2075183) B2075183
theorem B1383479 : Blo 920579 1383479 := bstep (se 1 (by rfl) ⟨1037609, by rfl⟩ : syracuseStep 1383479 = 2075219) B2075219
theorem B1383599 : Blo 920579 1383599 := bstep (se 1 (by rfl) ⟨1037699, by rfl⟩ : syracuseStep 1383599 = 2075399) B2075399
theorem B1383743 : Blo 920579 1383743 := bstep (se 1 (by rfl) ⟨1037807, by rfl⟩ : syracuseStep 1383743 = 2075615) B2075615
theorem B3939779 : Blo 920579 3939779 := bstep (se 1 (by rfl) ⟨2954834, by rfl⟩ : syracuseStep 3939779 = 5909669) B5909669
theorem B2072015 : Blo 920579 2072015 := bstep (se 1 (by rfl) ⟨1554011, by rfl⟩ : syracuseStep 2072015 = 3108023) B3108023
theorem B1383887 : Blo 920579 1383887 := bstep (se 1 (by rfl) ⟨1037915, by rfl⟩ : syracuseStep 1383887 = 2075831) B2075831
theorem B1384271 : Blo 920579 1384271 := bstep (se 1 (by rfl) ⟨1038203, by rfl⟩ : syracuseStep 1384271 = 2076407) B2076407
theorem B1384319 : Blo 920579 1384319 := bstep (se 1 (by rfl) ⟨1038239, by rfl⟩ : syracuseStep 1384319 = 2076479) B2076479
theorem B5054363 : Blo 920579 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B1384391 : Blo 920579 1384391 := bstep (se 1 (by rfl) ⟨1038293, by rfl⟩ : syracuseStep 1384391 = 2076587) B2076587
theorem B10526759 : Blo 920579 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B2334815 : Blo 920579 2334815 := bstep (se 1 (by rfl) ⟨1751111, by rfl⟩ : syracuseStep 2334815 = 3502223) B3502223
theorem B9969803 : Blo 920579 9969803 := bstep (se 1 (by rfl) ⟨7477352, by rfl⟩ : syracuseStep 9969803 = 14954705) B14954705
theorem B1384631 : Blo 920579 1384631 := bstep (se 1 (by rfl) ⟨1038473, by rfl⟩ : syracuseStep 1384631 = 2076947) B2076947
theorem B11804879 : Blo 920579 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B1384751 : Blo 920579 1384751 := bstep (se 1 (by rfl) ⟨1038563, by rfl⟩ : syracuseStep 1384751 = 2077127) B2077127
theorem B1384991 : Blo 920579 1384991 := bstep (se 1 (by rfl) ⟨1038743, by rfl⟩ : syracuseStep 1384991 = 2077487) B2077487
theorem B1385051 : Blo 920579 1385051 := bstep (se 1 (by rfl) ⟨1038788, by rfl⟩ : syracuseStep 1385051 = 2077577) B2077577
theorem B1385567 : Blo 920579 1385567 := bstep (se 1 (by rfl) ⟨1039175, by rfl⟩ : syracuseStep 1385567 = 2078351) B2078351
theorem B1385627 : Blo 920579 1385627 := bstep (se 1 (by rfl) ⟨1039220, by rfl⟩ : syracuseStep 1385627 = 2078441) B2078441
theorem B2532563 : Blo 920579 2532563 := bstep (se 1 (by rfl) ⟨1899422, by rfl⟩ : syracuseStep 2532563 = 3798845) B3798845
theorem B25240987 : Blo 920579 25240987 := bstep (se 1 (by rfl) ⟨18930740, by rfl⟩ : syracuseStep 25240987 = 37861481) B37861481
theorem B5907977 : Blo 920579 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B1386089 : Blo 920579 1386089 := bstep (se 2 (by rfl) ⟨519783, by rfl⟩ : syracuseStep 1386089 = 1039567) B1039567
theorem B5908079 : Blo 920579 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B1386215 : Blo 920579 1386215 := bstep (se 1 (by rfl) ⟨1039661, by rfl⟩ : syracuseStep 1386215 = 2079323) B2079323
theorem B1386311 : Blo 920579 1386311 := bstep (se 1 (by rfl) ⟨1039733, by rfl⟩ : syracuseStep 1386311 = 2079467) B2079467
theorem B1386719 : Blo 920579 1386719 := bstep (se 1 (by rfl) ⟨1040039, by rfl⟩ : syracuseStep 1386719 = 2080079) B2080079
theorem B1386779 : Blo 920579 1386779 := bstep (se 1 (by rfl) ⟨1040084, by rfl⟩ : syracuseStep 1386779 = 2080169) B2080169
theorem B2075039 : Blo 920579 2075039 := bstep (se 1 (by rfl) ⟨1556279, by rfl⟩ : syracuseStep 2075039 = 3112559) B3112559
theorem B2959831 : Blo 920579 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B2632169 : Blo 920579 2632169 := bstep (se 2 (by rfl) ⟨987063, by rfl⟩ : syracuseStep 2632169 = 1974127) B1974127
theorem B2075561 : Blo 920579 2075561 := bstep (se 2 (by rfl) ⟨778335, by rfl⟩ : syracuseStep 2075561 = 1556671) B1556671
theorem B18951175 : Blo 920579 18951175 := bstep (se 1 (by rfl) ⟨14213381, by rfl⟩ : syracuseStep 18951175 = 28426763) B28426763
theorem B18918521 : Blo 920579 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B5254267 : Blo 920579 5254267 := bstep (se 1 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 5254267 = 7881401) B7881401
theorem B5319863 : Blo 920579 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B2076137 : Blo 920579 2076137 := bstep (se 2 (by rfl) ⟨778551, by rfl⟩ : syracuseStep 2076137 = 1557103) B1557103
theorem B2076191 : Blo 920579 2076191 := bstep (se 1 (by rfl) ⟨1557143, by rfl⟩ : syracuseStep 2076191 = 3114287) B3114287
theorem B2338591 : Blo 920579 2338591 := bstep (se 1 (by rfl) ⟨1753943, by rfl⟩ : syracuseStep 2338591 = 3507887) B3507887
theorem B4993163 : Blo 920579 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B6992081 : Blo 920579 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B9613523 : Blo 920579 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B19214567 : Blo 920579 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B1749289 : Blo 920579 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B4665761 : Blo 920579 4665761 := bstep (se 2 (by rfl) ⟨1749660, by rfl⟩ : syracuseStep 4665761 = 3499321) B3499321
theorem B7877027 : Blo 920579 7877027 := bstep (se 1 (by rfl) ⟨5907770, by rfl⟩ : syracuseStep 7877027 = 11815541) B11815541
theorem B1749919 : Blo 920579 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B1749995 : Blo 920579 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B31208489 : Blo 920579 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B1750177 : Blo 920579 1750177 := bstep (se 2 (by rfl) ⟨656316, by rfl⟩ : syracuseStep 1750177 = 1312633) B1312633
theorem B3946067 : Blo 920579 3946067 := bstep (se 1 (by rfl) ⟨2959550, by rfl⟩ : syracuseStep 3946067 = 5919101) B5919101
theorem B1750747 : Blo 920579 1750747 := bstep (se 1 (by rfl) ⟨1313060, by rfl⟩ : syracuseStep 1750747 = 2626121) B2626121
theorem B6732019 : Blo 920579 6732019 := bstep (se 1 (by rfl) ⟨5049014, by rfl⟩ : syracuseStep 6732019 = 10098029) B10098029
theorem B2079287 : Blo 920579 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B17709779 : Blo 920579 17709779 := bstep (se 1 (by rfl) ⟨13282334, by rfl⟩ : syracuseStep 17709779 = 26564669) B26564669
theorem B1555625 : Blo 920579 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B3325373 : Blo 920579 3325373 := bstep (se 3 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 3325373 = 1247015) B1247015
theorem B4439519 : Blo 920579 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B2080223 : Blo 920579 2080223 := bstep (se 1 (by rfl) ⟨1560167, by rfl⟩ : syracuseStep 2080223 = 3120335) B3120335
theorem B5259167 : Blo 920579 5259167 := bstep (se 1 (by rfl) ⟨3944375, by rfl⟩ : syracuseStep 5259167 = 7888751) B7888751
theorem B3326035 : Blo 920579 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B1556617 : Blo 920579 1556617 := bstep (se 2 (by rfl) ⟨583731, by rfl⟩ : syracuseStep 1556617 = 1167463) B1167463
theorem B1753321 : Blo 920579 1753321 := bstep (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) B1314991
theorem B11845885 : Blo 920579 11845885 := bstep (se 3 (by rfl) ⟨2221103, by rfl⟩ : syracuseStep 11845885 = 4442207) B4442207
theorem B5915051 : Blo 920579 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B5260099 : Blo 920579 5260099 := bstep (se 1 (by rfl) ⟨3945074, by rfl⟩ : syracuseStep 5260099 = 7890149) B7890149
theorem B10503431 : Blo 920579 10503431 := bstep (se 1 (by rfl) ⟨7877573, by rfl⟩ : syracuseStep 10503431 = 15755147) B15755147
theorem B15746399 : Blo 920579 15746399 := bstep (se 1 (by rfl) ⟨11809799, by rfl⟩ : syracuseStep 15746399 = 23619599) B23619599
theorem B2803495 : Blo 920579 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B4442131 : Blo 920579 4442131 := bstep (se 1 (by rfl) ⟨3331598, by rfl⟩ : syracuseStep 4442131 = 6663197) B6663197
theorem B1165519 : Blo 920579 1165519 := bstep (se 1 (by rfl) ⟨874139, by rfl⟩ : syracuseStep 1165519 = 1748279) B1748279
theorem B1559081 : Blo 920579 1559081 := bstep (se 2 (by rfl) ⟨584655, by rfl⟩ : syracuseStep 1559081 = 1169311) B1169311
theorem B7490231 : Blo 920579 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B2214953 : Blo 920579 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B16174237 : Blo 920579 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B7883999 : Blo 920579 7883999 := bstep (se 1 (by rfl) ⟨5912999, by rfl⟩ : syracuseStep 7883999 = 11825999) B11825999
theorem B4739111 : Blo 920579 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B10506347 : Blo 920579 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B1036831 : Blo 920579 1036831 := bstep (se 1 (by rfl) ⟨777623, by rfl⟩ : syracuseStep 1036831 = 1555247) B1555247
theorem B4674185 : Blo 920579 4674185 := bstep (se 2 (by rfl) ⟨1752819, by rfl⟩ : syracuseStep 4674185 = 3505639) B3505639
theorem B1168607 : Blo 920579 1168607 := bstep (se 1 (by rfl) ⟨876455, by rfl⟩ : syracuseStep 1168607 = 1752911) B1752911
theorem B13686245 : Blo 920579 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B7689979 : Blo 920579 7689979 := bstep (se 1 (by rfl) ⟨5767484, by rfl⟩ : syracuseStep 7689979 = 11534969) B11534969
theorem B13326281 : Blo 920579 13326281 := bstep (se 2 (by rfl) ⟨4997355, by rfl⟩ : syracuseStep 13326281 = 9994711) B9994711
theorem B1038559 : Blo 920579 1038559 := bstep (se 1 (by rfl) ⟨778919, by rfl⟩ : syracuseStep 1038559 = 1557839) B1557839
theorem B3496223 : Blo 920579 3496223 := bstep (se 1 (by rfl) ⟨2622167, by rfl⟩ : syracuseStep 3496223 = 5244335) B5244335
theorem B2218279 : Blo 920579 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B10672793 : Blo 920579 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B1661735 : Blo 920579 1661735 := bstep (se 1 (by rfl) ⟨1246301, by rfl⟩ : syracuseStep 1661735 = 2492603) B2492603
theorem B1039207 : Blo 920579 1039207 := bstep (se 1 (by rfl) ⟨779405, by rfl⟩ : syracuseStep 1039207 = 1558811) B1558811
theorem B10509263 : Blo 920579 10509263 := bstep (se 1 (by rfl) ⟨7881947, by rfl⟩ : syracuseStep 10509263 = 15763895) B15763895
theorem B1039423 : Blo 920579 1039423 := bstep (se 1 (by rfl) ⟨779567, by rfl⟩ : syracuseStep 1039423 = 1559135) B1559135
theorem B5758087 : Blo 920579 5758087 := bstep (se 1 (by rfl) ⟨4318565, by rfl⟩ : syracuseStep 5758087 = 8637131) B8637131
theorem B3595529 : Blo 920579 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B1662887 : Blo 920579 1662887 := bstep (se 1 (by rfl) ⟨1247165, by rfl⟩ : syracuseStep 1662887 = 2494331) B2494331
theorem B3107321 : Blo 920579 3107321 := bstep (se 2 (by rfl) ⟨1165245, by rfl⟩ : syracuseStep 3107321 = 2330491) B2330491
theorem B3107483 : Blo 920579 3107483 := bstep (se 1 (by rfl) ⟨2330612, by rfl⟩ : syracuseStep 3107483 = 4661225) B4661225
theorem B3108455 : Blo 920579 3108455 := bstep (se 1 (by rfl) ⟨2331341, by rfl⟩ : syracuseStep 3108455 = 4662683) B4662683
theorem B5336857 : Blo 920579 5336857 := bstep (se 2 (by rfl) ⟨2001321, by rfl⟩ : syracuseStep 5336857 = 4002643) B4002643
theorem B3108779 : Blo 920579 3108779 := bstep (se 1 (by rfl) ⟨2331584, by rfl⟩ : syracuseStep 3108779 = 4663169) B4663169
theorem B9990125 : Blo 920579 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B18903395 : Blo 920579 18903395 := bstep (se 1 (by rfl) ⟨14177546, by rfl⟩ : syracuseStep 18903395 = 28355093) B28355093
theorem B3109319 : Blo 920579 3109319 := bstep (se 1 (by rfl) ⟨2331989, by rfl⟩ : syracuseStep 3109319 = 4663979) B4663979
theorem B7009091 : Blo 920579 7009091 := bstep (se 1 (by rfl) ⟨5256818, by rfl⟩ : syracuseStep 7009091 = 10513637) B10513637
theorem B11531213 : Blo 920579 11531213 := bstep (se 3 (by rfl) ⟨2162102, by rfl⟩ : syracuseStep 11531213 = 4324205) B4324205
theorem B3110939 : Blo 920579 3110939 := bstep (se 1 (by rfl) ⟨2333204, by rfl⟩ : syracuseStep 3110939 = 4666409) B4666409
theorem B3504167 : Blo 920579 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B7469111 : Blo 920579 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B3504667 : Blo 920579 3504667 := bstep (se 1 (by rfl) ⟨2628500, by rfl⟩ : syracuseStep 3504667 = 5257001) B5257001
theorem B10518011 : Blo 920579 10518011 := bstep (se 1 (by rfl) ⟨7888508, by rfl⟩ : syracuseStep 10518011 = 15777017) B15777017
theorem B8420993 : Blo 920579 8420993 := bstep (se 2 (by rfl) ⟨3157872, by rfl⟩ : syracuseStep 8420993 = 6315745) B6315745
theorem B2490203 : Blo 920579 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B4980619 : Blo 920579 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B15794513 : Blo 920579 15794513 := bstep (se 2 (by rfl) ⟨5922942, by rfl⟩ : syracuseStep 15794513 = 11845885) B11845885
theorem B7013465 : Blo 920579 7013465 := bstep (se 2 (by rfl) ⟨2630049, by rfl⟩ : syracuseStep 7013465 = 5260099) B5260099
theorem B7013951 : Blo 920579 7013951 := bstep (se 1 (by rfl) ⟨5260463, by rfl⟩ : syracuseStep 7013951 = 10520927) B10520927
theorem B33654649 : Blo 920579 33654649 := bstep (se 2 (by rfl) ⟨12620493, by rfl⟩ : syracuseStep 33654649 = 25240987) B25240987
theorem B1476635 : Blo 920579 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B4982867 : Blo 920579 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B3737993 : Blo 920579 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B3935081 : Blo 920579 3935081 := bstep (se 2 (by rfl) ⟨1475655, by rfl⟩ : syracuseStep 3935081 = 2951311) B2951311
theorem B920607 : Blo 920579 920607 := bstep (se 1 (by rfl) ⟨690455, by rfl⟩ : syracuseStep 920607 = 1380911) B1380911
theorem B29985821 : Blo 920579 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B3116123 : Blo 920579 3116123 := bstep (se 1 (by rfl) ⟨2337092, by rfl⟩ : syracuseStep 3116123 = 4674185) B4674185
theorem B920743 : Blo 920579 920743 := bstep (se 1 (by rfl) ⟨690557, by rfl⟩ : syracuseStep 920743 = 1381115) B1381115
theorem B3116285 : Blo 920579 3116285 := bstep (se 3 (by rfl) ⟨584303, by rfl⟩ : syracuseStep 3116285 = 1168607) B1168607
theorem B920991 : Blo 920579 920991 := bstep (se 1 (by rfl) ⟨690743, by rfl⟩ : syracuseStep 920991 = 1381487) B1381487
theorem B921039 : Blo 920579 921039 := bstep (se 1 (by rfl) ⟨690779, by rfl⟩ : syracuseStep 921039 = 1381559) B1381559
theorem B5901929 : Blo 920579 5901929 := bstep (se 2 (by rfl) ⟨2213223, by rfl⟩ : syracuseStep 5901929 = 4426447) B4426447
theorem B921199 : Blo 920579 921199 := bstep (se 1 (by rfl) ⟨690899, by rfl⟩ : syracuseStep 921199 = 1381799) B1381799
theorem B921319 : Blo 920579 921319 := bstep (se 1 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 921319 = 1381979) B1381979
theorem B8884187 : Blo 920579 8884187 := bstep (se 1 (by rfl) ⟨6663140, by rfl⟩ : syracuseStep 8884187 = 13326281) B13326281
theorem B25268233 : Blo 920579 25268233 := bstep (se 2 (by rfl) ⟨9475587, by rfl⟩ : syracuseStep 25268233 = 18951175) B18951175
theorem B2330815 : Blo 920579 2330815 := bstep (se 1 (by rfl) ⟨1748111, by rfl⟩ : syracuseStep 2330815 = 3496223) B3496223
theorem B21565649 : Blo 920579 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B921823 : Blo 920579 921823 := bstep (se 1 (by rfl) ⟨691367, by rfl⟩ : syracuseStep 921823 = 1382735) B1382735
theorem B921839 : Blo 920579 921839 := bstep (se 1 (by rfl) ⟨691379, by rfl⟩ : syracuseStep 921839 = 1382759) B1382759
theorem B921883 : Blo 920579 921883 := bstep (se 1 (by rfl) ⟨691412, by rfl⟩ : syracuseStep 921883 = 1382825) B1382825
theorem B7115195 : Blo 920579 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B922139 : Blo 920579 922139 := bstep (se 1 (by rfl) ⟨691604, by rfl⟩ : syracuseStep 922139 = 1383209) B1383209
theorem B15733277 : Blo 920579 15733277 := bstep (se 3 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 15733277 = 5899979) B5899979
theorem B922279 : Blo 920579 922279 := bstep (se 1 (by rfl) ⟨691709, by rfl⟩ : syracuseStep 922279 = 1383419) B1383419
theorem B1381055 : Blo 920579 1381055 := bstep (se 1 (by rfl) ⟨1035791, by rfl⟩ : syracuseStep 1381055 = 2071583) B2071583
theorem B922303 : Blo 920579 922303 := bstep (se 1 (by rfl) ⟨691727, by rfl⟩ : syracuseStep 922303 = 1383455) B1383455
theorem B922319 : Blo 920579 922319 := bstep (se 1 (by rfl) ⟨691739, by rfl⟩ : syracuseStep 922319 = 1383479) B1383479
theorem B922399 : Blo 920579 922399 := bstep (se 1 (by rfl) ⟨691799, by rfl⟩ : syracuseStep 922399 = 1383599) B1383599
theorem B2397019 : Blo 920579 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B922495 : Blo 920579 922495 := bstep (se 1 (by rfl) ⟨691871, by rfl⟩ : syracuseStep 922495 = 1383743) B1383743
theorem B2626519 : Blo 920579 2626519 := bstep (se 1 (by rfl) ⟨1969889, by rfl⟩ : syracuseStep 2626519 = 3939779) B3939779
theorem B1381343 : Blo 920579 1381343 := bstep (se 1 (by rfl) ⟨1036007, by rfl⟩ : syracuseStep 1381343 = 2072015) B2072015
theorem B922591 : Blo 920579 922591 := bstep (se 1 (by rfl) ⟨691943, by rfl⟩ : syracuseStep 922591 = 1383887) B1383887
theorem B3118121 : Blo 920579 3118121 := bstep (se 2 (by rfl) ⟨1169295, by rfl⟩ : syracuseStep 3118121 = 2338591) B2338591
theorem B922847 : Blo 920579 922847 := bstep (se 1 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 922847 = 1384271) B1384271
theorem B922879 : Blo 920579 922879 := bstep (se 1 (by rfl) ⟨692159, by rfl⟩ : syracuseStep 922879 = 1384319) B1384319
theorem B922927 : Blo 920579 922927 := bstep (se 1 (by rfl) ⟨692195, by rfl⟩ : syracuseStep 922927 = 1384391) B1384391
theorem B7017839 : Blo 920579 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B923087 : Blo 920579 923087 := bstep (se 1 (by rfl) ⟨692315, by rfl⟩ : syracuseStep 923087 = 1384631) B1384631
theorem B7869919 : Blo 920579 7869919 := bstep (se 1 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 7869919 = 11804879) B11804879
theorem B923167 : Blo 920579 923167 := bstep (se 1 (by rfl) ⟨692375, by rfl⟩ : syracuseStep 923167 = 1384751) B1384751
theorem B923327 : Blo 920579 923327 := bstep (se 1 (by rfl) ⟨692495, by rfl⟩ : syracuseStep 923327 = 1384991) B1384991
theorem B2332385 : Blo 920579 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B923367 : Blo 920579 923367 := bstep (se 1 (by rfl) ⟨692525, by rfl⟩ : syracuseStep 923367 = 1385051) B1385051
theorem B1382441 : Blo 920579 1382441 := bstep (se 2 (by rfl) ⟨518415, by rfl⟩ : syracuseStep 1382441 = 1036831) B1036831
theorem B923711 : Blo 920579 923711 := bstep (se 1 (by rfl) ⟨692783, by rfl⟩ : syracuseStep 923711 = 1385567) B1385567
theorem B923751 : Blo 920579 923751 := bstep (se 1 (by rfl) ⟨692813, by rfl⟩ : syracuseStep 923751 = 1385627) B1385627
theorem B3938651 : Blo 920579 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B924059 : Blo 920579 924059 := bstep (se 1 (by rfl) ⟨693044, by rfl⟩ : syracuseStep 924059 = 1386089) B1386089
theorem B3938719 : Blo 920579 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B924143 : Blo 920579 924143 := bstep (se 1 (by rfl) ⟨693107, by rfl⟩ : syracuseStep 924143 = 1386215) B1386215
theorem B2333225 : Blo 920579 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B924207 : Blo 920579 924207 := bstep (se 1 (by rfl) ⟨693155, by rfl⟩ : syracuseStep 924207 = 1386311) B1386311
theorem B924479 : Blo 920579 924479 := bstep (se 1 (by rfl) ⟨693359, by rfl⟩ : syracuseStep 924479 = 1386719) B1386719
theorem B924519 : Blo 920579 924519 := bstep (se 1 (by rfl) ⟨693389, by rfl⟩ : syracuseStep 924519 = 1386779) B1386779
theorem B2333569 : Blo 920579 2333569 := bstep (se 2 (by rfl) ⟨875088, by rfl⟩ : syracuseStep 2333569 = 1750177) B1750177
theorem B1383359 : Blo 920579 1383359 := bstep (se 1 (by rfl) ⟨1037519, by rfl⟩ : syracuseStep 1383359 = 2075039) B2075039
theorem B2071547 : Blo 920579 2071547 := bstep (se 1 (by rfl) ⟨1553660, by rfl⟩ : syracuseStep 2071547 = 3107321) B3107321
theorem B2071655 : Blo 920579 2071655 := bstep (se 1 (by rfl) ⟨1553741, by rfl⟩ : syracuseStep 2071655 = 3107483) B3107483
theorem B1383707 : Blo 920579 1383707 := bstep (se 1 (by rfl) ⟨1037780, by rfl⟩ : syracuseStep 1383707 = 2075561) B2075561
theorem B3546575 : Blo 920579 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B2334329 : Blo 920579 2334329 := bstep (se 2 (by rfl) ⟨875373, by rfl⟩ : syracuseStep 2334329 = 1750747) B1750747
theorem B1384091 : Blo 920579 1384091 := bstep (se 1 (by rfl) ⟨1038068, by rfl⟩ : syracuseStep 1384091 = 2076137) B2076137
theorem B1384127 : Blo 920579 1384127 := bstep (se 1 (by rfl) ⟨1038095, by rfl⟩ : syracuseStep 1384127 = 2076191) B2076191
theorem B2072303 : Blo 920579 2072303 := bstep (se 1 (by rfl) ⟨1554227, by rfl⟩ : syracuseStep 2072303 = 3108455) B3108455
theorem B2072519 : Blo 920579 2072519 := bstep (se 1 (by rfl) ⟨1554389, by rfl⟩ : syracuseStep 2072519 = 3108779) B3108779
theorem B6660083 : Blo 920579 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B5251169 : Blo 920579 5251169 := bstep (se 2 (by rfl) ⟨1969188, by rfl⟩ : syracuseStep 5251169 = 3938377) B3938377
theorem B4661387 : Blo 920579 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B5251351 : Blo 920579 5251351 := bstep (se 1 (by rfl) ⟨3938513, by rfl⟩ : syracuseStep 5251351 = 7877027) B7877027
theorem B1384745 : Blo 920579 1384745 := bstep (se 2 (by rfl) ⟨519279, by rfl⟩ : syracuseStep 1384745 = 1038559) B1038559
theorem B2072879 : Blo 920579 2072879 := bstep (se 1 (by rfl) ⟨1554659, by rfl⟩ : syracuseStep 2072879 = 3109319) B3109319
theorem B2957705 : Blo 920579 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B2630369 : Blo 920579 2630369 := bstep (se 2 (by rfl) ⟨986388, by rfl⟩ : syracuseStep 2630369 = 1972777) B1972777
theorem B3941369 : Blo 920579 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B2630711 : Blo 920579 2630711 := bstep (se 1 (by rfl) ⟨1973033, by rfl⟩ : syracuseStep 2630711 = 3946067) B3946067
theorem B1385609 : Blo 920579 1385609 := bstep (se 2 (by rfl) ⟨519603, by rfl⟩ : syracuseStep 1385609 = 1039207) B1039207
theorem B2073959 : Blo 920579 2073959 := bstep (se 1 (by rfl) ⟨1555469, by rfl⟩ : syracuseStep 2073959 = 3110939) B3110939
theorem B2336111 : Blo 920579 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B1385897 : Blo 920579 1385897 := bstep (se 2 (by rfl) ⟨519711, by rfl⟩ : syracuseStep 1385897 = 1039423) B1039423
theorem B7677449 : Blo 920579 7677449 := bstep (se 2 (by rfl) ⟨2879043, by rfl⟩ : syracuseStep 7677449 = 5758087) B5758087
theorem B1386191 : Blo 920579 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B11806519 : Blo 920579 11806519 := bstep (se 1 (by rfl) ⟨8854889, by rfl⟩ : syracuseStep 11806519 = 17709779) B17709779
theorem B2959679 : Blo 920579 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B1386815 : Blo 920579 1386815 := bstep (se 1 (by rfl) ⟨1040111, by rfl⟩ : syracuseStep 1386815 = 2080223) B2080223
theorem B5613995 : Blo 920579 5613995 := bstep (se 1 (by rfl) ⟨4210496, by rfl⟩ : syracuseStep 5613995 = 8420993) B8420993
theorem B4434365 : Blo 920579 4434365 := bstep (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) B1662887
theorem B4434713 : Blo 920579 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B2337619 : Blo 920579 2337619 := bstep (se 1 (by rfl) ⟨1753214, by rfl⟩ : syracuseStep 2337619 = 3506429) B3506429
theorem B2075489 : Blo 920579 2075489 := bstep (se 2 (by rfl) ⟨778308, by rfl⟩ : syracuseStep 2075489 = 1556617) B1556617
theorem B3943367 : Blo 920579 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B2337761 : Blo 920579 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B25636061 : Blo 920579 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B4435327 : Blo 920579 4435327 := bstep (se 1 (by rfl) ⟨3326495, by rfl⟩ : syracuseStep 4435327 = 6652991) B6652991
theorem B10497599 : Blo 920579 10497599 := bstep (se 1 (by rfl) ⟨7873199, by rfl⟩ : syracuseStep 10497599 = 15746399) B15746399
theorem B50409053 : Blo 920579 50409053 := bstep (se 3 (by rfl) ⟨9451697, by rfl⟩ : syracuseStep 50409053 = 18903395) B18903395
theorem B29863727 : Blo 920579 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B4993487 : Blo 920579 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B2339563 : Blo 920579 2339563 := bstep (se 1 (by rfl) ⟨1754672, by rfl⟩ : syracuseStep 2339563 = 3509345) B3509345
theorem B5255999 : Blo 920579 5255999 := bstep (se 1 (by rfl) ⟨3941999, by rfl⟩ : syracuseStep 5255999 = 7883999) B7883999
theorem B1750223 : Blo 920579 1750223 := bstep (se 1 (by rfl) ⟨1312667, by rfl⟩ : syracuseStep 1750223 = 2625335) B2625335
theorem B1553735 : Blo 920579 1553735 := bstep (se 1 (by rfl) ⟨1165301, by rfl⟩ : syracuseStep 1553735 = 2330603) B2330603
theorem B3159407 : Blo 920579 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1554025 : Blo 920579 1554025 := bstep (se 2 (by rfl) ⟨582759, by rfl⟩ : syracuseStep 1554025 = 1165519) B1165519
theorem B2078495 : Blo 920579 2078495 := bstep (se 1 (by rfl) ⟨1558871, by rfl⟩ : syracuseStep 2078495 = 3117743) B3117743
theorem B2078711 : Blo 920579 2078711 := bstep (se 1 (by rfl) ⟨1559033, by rfl⟩ : syracuseStep 2078711 = 3118067) B3118067
theorem B7878941 : Blo 920579 7878941 := bstep (se 3 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 7878941 = 2954603) B2954603
theorem B9124163 : Blo 920579 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B2079071 : Blo 920579 2079071 := bstep (se 1 (by rfl) ⟨1559303, by rfl⟩ : syracuseStep 2079071 = 3118607) B3118607
theorem B6994511 : Blo 920579 6994511 := bstep (se 1 (by rfl) ⟨5245883, by rfl⟩ : syracuseStep 6994511 = 10491767) B10491767
theorem B1751863 : Blo 920579 1751863 := bstep (se 1 (by rfl) ⟨1313897, by rfl⟩ : syracuseStep 1751863 = 2627795) B2627795
theorem B2079791 : Blo 920579 2079791 := bstep (se 1 (by rfl) ⟨1559843, by rfl⟩ : syracuseStep 2079791 = 3119687) B3119687
theorem B1556543 : Blo 920579 1556543 := bstep (se 1 (by rfl) ⟨1167407, by rfl⟩ : syracuseStep 1556543 = 2334815) B2334815
theorem B1753481 : Blo 920579 1753481 := bstep (se 2 (by rfl) ⟨657555, by rfl⟩ : syracuseStep 1753481 = 1315111) B1315111
theorem B1688375 : Blo 920579 1688375 := bstep (se 1 (by rfl) ⟨1266281, by rfl⟩ : syracuseStep 1688375 = 2532563) B2532563
theorem B12600197 : Blo 920579 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B1754779 : Blo 920579 1754779 := bstep (se 1 (by rfl) ⟨1316084, by rfl⟩ : syracuseStep 1754779 = 2632169) B2632169
theorem B3328775 : Blo 920579 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B4672727 : Blo 920579 4672727 := bstep (se 1 (by rfl) ⟨3504545, by rfl⟩ : syracuseStep 4672727 = 7009091) B7009091
theorem B7687475 : Blo 920579 7687475 := bstep (se 1 (by rfl) ⟨5765606, by rfl⟩ : syracuseStep 7687475 = 11531213) B11531213
theorem B1166663 : Blo 920579 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B4672889 : Blo 920579 4672889 := bstep (se 2 (by rfl) ⟨1752333, by rfl⟩ : syracuseStep 4672889 = 3504667) B3504667
theorem B41013221 : Blo 920579 41013221 := bstep (se 4 (by rfl) ⟨3844989, by rfl⟩ : syracuseStep 41013221 = 7689979) B7689979
theorem B28463237 : Blo 920579 28463237 := bstep (se 4 (by rfl) ⟨2668428, by rfl⟩ : syracuseStep 28463237 = 5336857) B5336857
theorem B1037083 : Blo 920579 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B2216915 : Blo 920579 2216915 := bstep (se 1 (by rfl) ⟨1662686, by rfl⟩ : syracuseStep 2216915 = 3325373) B3325373
theorem B6640825 : Blo 920579 6640825 := bstep (se 2 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 6640825 = 4980619) B4980619
theorem B1660135 : Blo 920579 1660135 := bstep (se 1 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 1660135 = 2490203) B2490203
theorem B3495419 : Blo 920579 3495419 := bstep (se 1 (by rfl) ⟨2621564, by rfl⟩ : syracuseStep 3495419 = 5243129) B5243129
theorem B7002287 : Blo 920579 7002287 := bstep (se 1 (by rfl) ⟨5251715, by rfl⟩ : syracuseStep 7002287 = 10503431) B10503431
theorem B3496391 : Blo 920579 3496391 := bstep (se 1 (by rfl) ⟨2622293, by rfl⟩ : syracuseStep 3496391 = 5244587) B5244587
theorem B1039387 : Blo 920579 1039387 := bstep (se 1 (by rfl) ⟨779540, by rfl⟩ : syracuseStep 1039387 = 1559081) B1559081
theorem B15785765 : Blo 920579 15785765 := bstep (se 4 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 15785765 = 2959831) B2959831
theorem B5922841 : Blo 920579 5922841 := bstep (se 2 (by rfl) ⟨2221065, by rfl⟩ : syracuseStep 5922841 = 4442131) B4442131
theorem B7004231 : Blo 920579 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B3498335 : Blo 920579 3498335 := bstep (se 1 (by rfl) ⟨2623751, by rfl⟩ : syracuseStep 3498335 = 5247503) B5247503
theorem B3498653 : Blo 920579 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B7005689 : Blo 920579 7005689 := bstep (se 2 (by rfl) ⟨2627133, by rfl⟩ : syracuseStep 7005689 = 5254267) B5254267
theorem B1107823 : Blo 920579 1107823 := bstep (se 1 (by rfl) ⟨830867, by rfl⟩ : syracuseStep 1107823 = 1661735) B1661735
theorem B7006175 : Blo 920579 7006175 := bstep (se 1 (by rfl) ⟨5254631, by rfl⟩ : syracuseStep 7006175 = 10509263) B10509263
theorem B3369575 : Blo 920579 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B6646535 : Blo 920579 6646535 := bstep (se 1 (by rfl) ⟨4984901, by rfl⟩ : syracuseStep 6646535 = 9969803) B9969803
theorem B3107969 : Blo 920579 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B3501569 : Blo 920579 3501569 := bstep (se 2 (by rfl) ⟨1313088, by rfl⟩ : syracuseStep 3501569 = 2626177) B2626177
theorem B12612347 : Blo 920579 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B5600353 : Blo 920579 5600353 := bstep (se 2 (by rfl) ⟨2100132, by rfl⟩ : syracuseStep 5600353 = 4200265) B4200265
theorem B3503209 : Blo 920579 3503209 := bstep (se 2 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 3503209 = 2627407) B2627407
theorem B12809711 : Blo 920579 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B3110507 : Blo 920579 3110507 := bstep (se 1 (by rfl) ⟨2332880, by rfl⟩ : syracuseStep 3110507 = 4665761) B4665761
theorem B8976025 : Blo 920579 8976025 := bstep (se 2 (by rfl) ⟨3366009, by rfl⟩ : syracuseStep 8976025 = 6732019) B6732019
theorem B20805659 : Blo 920579 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B4979407 : Blo 920579 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B7012007 : Blo 920579 7012007 := bstep (se 1 (by rfl) ⟨5259005, by rfl⟩ : syracuseStep 7012007 = 10518011) B10518011
theorem B3506111 : Blo 920579 3506111 := bstep (se 1 (by rfl) ⟨2629583, by rfl⟩ : syracuseStep 3506111 = 5259167) B5259167
theorem B7897121 : Blo 920579 7897121 := bstep (se 2 (by rfl) ⟨2961420, by rfl⟩ : syracuseStep 7897121 = 5922841) B5922841
theorem B2623387 : Blo 920579 2623387 := bstep (se 1 (by rfl) ⟨1967540, by rfl⟩ : syracuseStep 2623387 = 3935081) B3935081
theorem B19990547 : Blo 920579 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B3115151 : Blo 920579 3115151 := bstep (se 1 (by rfl) ⟨2336363, by rfl⟩ : syracuseStep 3115151 = 4672727) B4672727
theorem B3115259 : Blo 920579 3115259 := bstep (se 1 (by rfl) ⟨2336444, by rfl⟩ : syracuseStep 3115259 = 4672889) B4672889
theorem B3934619 : Blo 920579 3934619 := bstep (se 1 (by rfl) ⟨2950964, by rfl⟩ : syracuseStep 3934619 = 5901929) B5901929
theorem B1477097 : Blo 920579 1477097 := bstep (se 2 (by rfl) ⟨553911, by rfl⟩ : syracuseStep 1477097 = 1107823) B1107823
theorem B18975491 : Blo 920579 18975491 := bstep (se 1 (by rfl) ⟨14231618, by rfl⟩ : syracuseStep 18975491 = 28463237) B28463237
theorem B10488851 : Blo 920579 10488851 := bstep (se 1 (by rfl) ⟨7866638, by rfl⟩ : syracuseStep 10488851 = 15733277) B15733277
theorem B920703 : Blo 920579 920703 := bstep (se 1 (by rfl) ⟨690527, by rfl⟩ : syracuseStep 920703 = 1381055) B1381055
theorem B1477943 : Blo 920579 1477943 := bstep (se 1 (by rfl) ⟨1108457, by rfl⟩ : syracuseStep 1477943 = 2216915) B2216915
theorem B920895 : Blo 920579 920895 := bstep (se 1 (by rfl) ⟨690671, by rfl⟩ : syracuseStep 920895 = 1381343) B1381343
theorem B2330279 : Blo 920579 2330279 := bstep (se 1 (by rfl) ⟨1747709, by rfl⟩ : syracuseStep 2330279 = 3495419) B3495419
theorem B3116825 : Blo 920579 3116825 := bstep (se 2 (by rfl) ⟨1168809, by rfl⟩ : syracuseStep 3116825 = 2337619) B2337619
theorem B921627 : Blo 920579 921627 := bstep (se 1 (by rfl) ⟨691220, by rfl⟩ : syracuseStep 921627 = 1382441) B1382441
theorem B2625767 : Blo 920579 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B2330927 : Blo 920579 2330927 := bstep (se 1 (by rfl) ⟨1748195, by rfl⟩ : syracuseStep 2330927 = 3496391) B3496391
theorem B922239 : Blo 920579 922239 := bstep (se 1 (by rfl) ⟨691679, by rfl⟩ : syracuseStep 922239 = 1383359) B1383359
theorem B1381031 : Blo 920579 1381031 := bstep (se 1 (by rfl) ⟨1035773, by rfl⟩ : syracuseStep 1381031 = 2071547) B2071547
theorem B1381103 : Blo 920579 1381103 := bstep (se 1 (by rfl) ⟨1035827, by rfl⟩ : syracuseStep 1381103 = 2071655) B2071655
theorem B922471 : Blo 920579 922471 := bstep (se 1 (by rfl) ⟨691853, by rfl⟩ : syracuseStep 922471 = 1383707) B1383707
theorem B2364383 : Blo 920579 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B922727 : Blo 920579 922727 := bstep (se 1 (by rfl) ⟨692045, by rfl⟩ : syracuseStep 922727 = 1384091) B1384091
theorem B922751 : Blo 920579 922751 := bstep (se 1 (by rfl) ⟨692063, by rfl⟩ : syracuseStep 922751 = 1384127) B1384127
theorem B1381535 : Blo 920579 1381535 := bstep (se 1 (by rfl) ⟨1036151, by rfl⟩ : syracuseStep 1381535 = 2072303) B2072303
theorem B10523843 : Blo 920579 10523843 := bstep (se 1 (by rfl) ⟨7892882, by rfl⟩ : syracuseStep 10523843 = 15785765) B15785765
theorem B1381679 : Blo 920579 1381679 := bstep (se 1 (by rfl) ⟨1036259, by rfl⟩ : syracuseStep 1381679 = 2072519) B2072519
theorem B33690977 : Blo 920579 33690977 := bstep (se 2 (by rfl) ⟨12634116, by rfl⟩ : syracuseStep 33690977 = 25268233) B25268233
theorem B923163 : Blo 920579 923163 := bstep (se 1 (by rfl) ⟨692372, by rfl⟩ : syracuseStep 923163 = 1384745) B1384745
theorem B1381919 : Blo 920579 1381919 := bstep (se 1 (by rfl) ⟨1036439, by rfl⟩ : syracuseStep 1381919 = 2072879) B2072879
theorem B2332223 : Blo 920579 2332223 := bstep (se 1 (by rfl) ⟨1749167, by rfl⟩ : syracuseStep 2332223 = 3498335) B3498335
theorem B1971803 : Blo 920579 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B2332435 : Blo 920579 2332435 := bstep (se 1 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 2332435 = 3498653) B3498653
theorem B2627579 : Blo 920579 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B923739 : Blo 920579 923739 := bstep (se 1 (by rfl) ⟨692804, by rfl⟩ : syracuseStep 923739 = 1385609) B1385609
theorem B1382639 : Blo 920579 1382639 := bstep (se 1 (by rfl) ⟨1036979, by rfl⟩ : syracuseStep 1382639 = 2073959) B2073959
theorem B923931 : Blo 920579 923931 := bstep (se 1 (by rfl) ⟨692948, by rfl⟩ : syracuseStep 923931 = 1385897) B1385897
theorem B3119417 : Blo 920579 3119417 := bstep (se 2 (by rfl) ⟨1169781, by rfl⟩ : syracuseStep 3119417 = 2339563) B2339563
theorem B5118299 : Blo 920579 5118299 := bstep (se 1 (by rfl) ⟨3838724, by rfl⟩ : syracuseStep 5118299 = 7677449) B7677449
theorem B9967981 : Blo 920579 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B1382777 : Blo 920579 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B924127 : Blo 920579 924127 := bstep (se 1 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 924127 = 1386191) B1386191
theorem B1973119 : Blo 920579 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B924543 : Blo 920579 924543 := bstep (se 1 (by rfl) ⟨693407, by rfl⟩ : syracuseStep 924543 = 1386815) B1386815
theorem B8854433 : Blo 920579 8854433 := bstep (se 2 (by rfl) ⟨3320412, by rfl⟩ : syracuseStep 8854433 = 6640825) B6640825
theorem B4431023 : Blo 920579 4431023 := bstep (se 1 (by rfl) ⟨3323267, by rfl⟩ : syracuseStep 4431023 = 6646535) B6646535
theorem B2956475 : Blo 920579 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1383659 : Blo 920579 1383659 := bstep (se 1 (by rfl) ⟨1037744, by rfl⟩ : syracuseStep 1383659 = 2075489) B2075489
theorem B10493225 : Blo 920579 10493225 := bstep (se 2 (by rfl) ⟨3934959, by rfl⟩ : syracuseStep 10493225 = 7869919) B7869919
theorem B2628911 : Blo 920579 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B2071979 : Blo 920579 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B2072033 : Blo 920579 2072033 := bstep (se 2 (by rfl) ⟨777012, by rfl⟩ : syracuseStep 2072033 = 1554025) B1554025
theorem B2334379 : Blo 920579 2334379 := bstep (se 1 (by rfl) ⟨1750784, by rfl⟩ : syracuseStep 2334379 = 3501569) B3501569
theorem B5251625 : Blo 920579 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B2106271 : Blo 920579 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B2073671 : Blo 920579 2073671 := bstep (se 1 (by rfl) ⟨1555253, by rfl⟩ : syracuseStep 2073671 = 3110507) B3110507
theorem B2335817 : Blo 920579 2335817 := bstep (se 2 (by rfl) ⟨875931, by rfl⟩ : syracuseStep 2335817 = 1751863) B1751863
theorem B1385663 : Blo 920579 1385663 := bstep (se 1 (by rfl) ⟨1039247, by rfl⟩ : syracuseStep 1385663 = 2078495) B2078495
theorem B1385807 : Blo 920579 1385807 := bstep (se 1 (by rfl) ⟨1039355, by rfl⟩ : syracuseStep 1385807 = 2078711) B2078711
theorem B13870439 : Blo 920579 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B1385849 : Blo 920579 1385849 := bstep (se 2 (by rfl) ⟨519693, by rfl⟩ : syracuseStep 1385849 = 1039387) B1039387
theorem B5252627 : Blo 920579 5252627 := bstep (se 1 (by rfl) ⟨3939470, by rfl⟩ : syracuseStep 5252627 = 7878941) B7878941
theorem B1386047 : Blo 920579 1386047 := bstep (se 1 (by rfl) ⟨1039535, by rfl⟩ : syracuseStep 1386047 = 2079071) B2079071
theorem B4663007 : Blo 920579 4663007 := bstep (se 1 (by rfl) ⟨3497255, by rfl⟩ : syracuseStep 4663007 = 6994511) B6994511
theorem B1386527 : Blo 920579 1386527 := bstep (se 1 (by rfl) ⟨1039895, by rfl⟩ : syracuseStep 1386527 = 2079791) B2079791
theorem B2337407 : Blo 920579 2337407 := bstep (se 1 (by rfl) ⟨1753055, by rfl⟩ : syracuseStep 2337407 = 3506111) B3506111
theorem B10529675 : Blo 920579 10529675 := bstep (se 1 (by rfl) ⟨7897256, by rfl⟩ : syracuseStep 10529675 = 15794513) B15794513
theorem B8400131 : Blo 920579 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B3321911 : Blo 920579 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B2077415 : Blo 920579 2077415 := bstep (se 1 (by rfl) ⟨1558061, by rfl⟩ : syracuseStep 2077415 = 3116123) B3116123
theorem B4502333 : Blo 920579 4502333 := bstep (se 3 (by rfl) ⟨844187, by rfl⟩ : syracuseStep 4502333 = 1688375) B1688375
theorem B2077523 : Blo 920579 2077523 := bstep (se 1 (by rfl) ⟨1558142, by rfl⟩ : syracuseStep 2077523 = 3116285) B3116285
theorem B5124983 : Blo 920579 5124983 := bstep (se 1 (by rfl) ⟨3843737, by rfl⟩ : syracuseStep 5124983 = 7687475) B7687475
theorem B2339705 : Blo 920579 2339705 := bstep (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) B1754779
theorem B15742025 : Blo 920579 15742025 := bstep (se 2 (by rfl) ⟨5903259, by rfl⟩ : syracuseStep 15742025 = 11806519) B11806519
theorem B44872865 : Blo 920579 44872865 := bstep (se 2 (by rfl) ⟨16827324, by rfl⟩ : syracuseStep 44872865 = 33654649) B33654649
theorem B2078747 : Blo 920579 2078747 := bstep (se 1 (by rfl) ⟨1559060, by rfl⟩ : syracuseStep 2078747 = 3118121) B3118121
theorem B1554923 : Blo 920579 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B34159229 : Blo 920579 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B4668191 : Blo 920579 4668191 := bstep (se 1 (by rfl) ⟨3501143, by rfl⟩ : syracuseStep 4668191 = 7002287) B7002287
theorem B1555483 : Blo 920579 1555483 := bstep (se 1 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 1555483 = 2333225) B2333225
theorem B5913769 : Blo 920579 5913769 := bstep (se 2 (by rfl) ⟨2217663, by rfl⟩ : syracuseStep 5913769 = 4435327) B4435327
theorem B1556219 : Blo 920579 1556219 := bstep (se 1 (by rfl) ⟨1167164, by rfl⟩ : syracuseStep 1556219 = 2334329) B2334329
theorem B4440055 : Blo 920579 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B4669487 : Blo 920579 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B1753579 : Blo 920579 1753579 := bstep (se 1 (by rfl) ⟨1315184, by rfl⟩ : syracuseStep 1753579 = 2630369) B2630369
theorem B1753807 : Blo 920579 1753807 := bstep (se 1 (by rfl) ⟨1315355, by rfl⟩ : syracuseStep 1753807 = 2630711) B2630711
theorem B1557407 : Blo 920579 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B4670459 : Blo 920579 4670459 := bstep (se 1 (by rfl) ⟨3502844, by rfl⟩ : syracuseStep 4670459 = 7005689) B7005689
theorem B3196025 : Blo 920579 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B4670783 : Blo 920579 4670783 := bstep (se 1 (by rfl) ⟨3503087, by rfl⟩ : syracuseStep 4670783 = 7006175) B7006175
theorem B4670945 : Blo 920579 4670945 := bstep (se 2 (by rfl) ⟨1751604, by rfl⟩ : syracuseStep 4670945 = 3503209) B3503209
theorem B2213513 : Blo 920579 2213513 := bstep (se 2 (by rfl) ⟨830067, by rfl⟩ : syracuseStep 2213513 = 1660135) B1660135
theorem B2246383 : Blo 920579 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B1558507 : Blo 920579 1558507 := bstep (se 1 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 1558507 = 2337761) B2337761
theorem B17090707 : Blo 920579 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B6998399 : Blo 920579 6998399 := bstep (se 1 (by rfl) ⟨5248799, by rfl⟩ : syracuseStep 6998399 = 10497599) B10497599
theorem B33606035 : Blo 920579 33606035 := bstep (se 1 (by rfl) ⟨25204526, by rfl⟩ : syracuseStep 33606035 = 50409053) B50409053
theorem B19909151 : Blo 920579 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B3328991 : Blo 920579 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B8408231 : Blo 920579 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B1166815 : Blo 920579 1166815 := bstep (se 1 (by rfl) ⟨875111, by rfl⟩ : syracuseStep 1166815 = 1750223) B1750223
theorem B1035823 : Blo 920579 1035823 := bstep (se 1 (by rfl) ⟨776867, by rfl⟩ : syracuseStep 1035823 = 1553735) B1553735
theorem B6639209 : Blo 920579 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B6082775 : Blo 920579 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B4674671 : Blo 920579 4674671 := bstep (se 1 (by rfl) ⟨3506003, by rfl⟩ : syracuseStep 4674671 = 7012007) B7012007
theorem B109368589 : Blo 920579 109368589 := bstep (se 3 (by rfl) ⟨20506610, by rfl⟩ : syracuseStep 109368589 = 41013221) B41013221
theorem B1037695 : Blo 920579 1037695 := bstep (se 1 (by rfl) ⟨778271, by rfl⟩ : syracuseStep 1037695 = 1556543) B1556543
theorem B1168987 : Blo 920579 1168987 := bstep (se 1 (by rfl) ⟨876740, by rfl⟩ : syracuseStep 1168987 = 1753481) B1753481
theorem B15750773 : Blo 920579 15750773 := bstep (se 5 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 15750773 = 1476635) B1476635
theorem B7001801 : Blo 920579 7001801 := bstep (se 2 (by rfl) ⟨2625675, by rfl⟩ : syracuseStep 7001801 = 5251351) B5251351
theorem B4675643 : Blo 920579 4675643 := bstep (se 1 (by rfl) ⟨3506732, by rfl⟩ : syracuseStep 4675643 = 7013465) B7013465
theorem B4675967 : Blo 920579 4675967 := bstep (se 1 (by rfl) ⟨3506975, by rfl⟩ : syracuseStep 4675967 = 7013951) B7013951
theorem B2219183 : Blo 920579 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B5922791 : Blo 920579 5922791 := bstep (se 1 (by rfl) ⟨4442093, by rfl⟩ : syracuseStep 5922791 = 8884187) B8884187
theorem B14377099 : Blo 920579 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B4743463 : Blo 920579 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B4678559 : Blo 920579 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B3500779 : Blo 920579 3500779 := bstep (se 1 (by rfl) ⟨2625584, by rfl⟩ : syracuseStep 3500779 = 5251169) B5251169
theorem B3107591 : Blo 920579 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B3107753 : Blo 920579 3107753 := bstep (se 2 (by rfl) ⟨1165407, by rfl⟩ : syracuseStep 3107753 = 2330815) B2330815
theorem B14970653 : Blo 920579 14970653 := bstep (se 3 (by rfl) ⟨2806997, by rfl⟩ : syracuseStep 14970653 = 5613995) B5613995
theorem B11824973 : Blo 920579 11824973 := bstep (se 3 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 11824973 = 4434365) B4434365
theorem B3502025 : Blo 920579 3502025 := bstep (se 2 (by rfl) ⟨1313259, by rfl⟩ : syracuseStep 3502025 = 2626519) B2626519
theorem B7467137 : Blo 920579 7467137 := bstep (se 2 (by rfl) ⟨2800176, by rfl⟩ : syracuseStep 7467137 = 5600353) B5600353
theorem B3503999 : Blo 920579 3503999 := bstep (se 1 (by rfl) ⟨2627999, by rfl⟩ : syracuseStep 3503999 = 5255999) B5255999
theorem B47872133 : Blo 920579 47872133 := bstep (se 4 (by rfl) ⟨4488012, by rfl⟩ : syracuseStep 47872133 = 8976025) B8976025
theorem B3111101 : Blo 920579 3111101 := bstep (se 3 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 3111101 = 1166663) B1166663
theorem B3111425 : Blo 920579 3111425 := bstep (se 2 (by rfl) ⟨1166784, by rfl⟩ : syracuseStep 3111425 = 2333569) B2333569
theorem B3112991 : Blo 920579 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B19169465 : Blo 920579 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B6324617 : Blo 920579 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B3113639 : Blo 920579 3113639 := bstep (se 1 (by rfl) ⟨2335229, by rfl⟩ : syracuseStep 3113639 = 4670459) B4670459
theorem B2130683 : Blo 920579 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B3113855 : Blo 920579 3113855 := bstep (se 1 (by rfl) ⟨2335391, by rfl⟩ : syracuseStep 3113855 = 4670783) B4670783
theorem B3113963 : Blo 920579 3113963 := bstep (se 1 (by rfl) ⟨2335472, by rfl⟩ : syracuseStep 3113963 = 4670945) B4670945
theorem B1475675 : Blo 920579 1475675 := bstep (se 1 (by rfl) ⟨1106756, by rfl⟩ : syracuseStep 1475675 = 2213513) B2213513
theorem B2623079 : Blo 920579 2623079 := bstep (se 1 (by rfl) ⟨1967309, by rfl⟩ : syracuseStep 2623079 = 3934619) B3934619
theorem B984731 : Blo 920579 984731 := bstep (se 1 (by rfl) ⟨738548, by rfl⟩ : syracuseStep 984731 = 1477097) B1477097
theorem B13272767 : Blo 920579 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B12650327 : Blo 920579 12650327 := bstep (se 1 (by rfl) ⟨9487745, by rfl⟩ : syracuseStep 12650327 = 18975491) B18975491
theorem B5605487 : Blo 920579 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B985295 : Blo 920579 985295 := bstep (se 1 (by rfl) ⟨738971, by rfl⟩ : syracuseStep 985295 = 1477943) B1477943
theorem B13666621 : Blo 920579 13666621 := bstep (se 3 (by rfl) ⟨2562491, by rfl⟩ : syracuseStep 13666621 = 5124983) B5124983
theorem B4426139 : Blo 920579 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B920687 : Blo 920579 920687 := bstep (se 1 (by rfl) ⟨690515, by rfl⟩ : syracuseStep 920687 = 1381031) B1381031
theorem B920735 : Blo 920579 920735 := bstep (se 1 (by rfl) ⟨690551, by rfl⟩ : syracuseStep 920735 = 1381103) B1381103
theorem B1576255 : Blo 920579 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B3116447 : Blo 920579 3116447 := bstep (se 1 (by rfl) ⟨2337335, by rfl⟩ : syracuseStep 3116447 = 4674671) B4674671
theorem B921023 : Blo 920579 921023 := bstep (se 1 (by rfl) ⟨690767, by rfl⟩ : syracuseStep 921023 = 1381535) B1381535
theorem B7015895 : Blo 920579 7015895 := bstep (se 1 (by rfl) ⟨5261921, by rfl⟩ : syracuseStep 7015895 = 10523843) B10523843
theorem B921119 : Blo 920579 921119 := bstep (se 1 (by rfl) ⟨690839, by rfl⟩ : syracuseStep 921119 = 1381679) B1381679
theorem B921279 : Blo 920579 921279 := bstep (se 1 (by rfl) ⟨690959, by rfl⟩ : syracuseStep 921279 = 1381919) B1381919
theorem B3117095 : Blo 920579 3117095 := bstep (se 1 (by rfl) ⟨2337821, by rfl⟩ : syracuseStep 3117095 = 4675643) B4675643
theorem B921759 : Blo 920579 921759 := bstep (se 1 (by rfl) ⟨691319, by rfl⟩ : syracuseStep 921759 = 1382639) B1382639
theorem B3412199 : Blo 920579 3412199 := bstep (se 1 (by rfl) ⟨2559149, by rfl⟩ : syracuseStep 3412199 = 5118299) B5118299
theorem B921851 : Blo 920579 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B3117311 : Blo 920579 3117311 := bstep (se 1 (by rfl) ⟨2337983, by rfl⟩ : syracuseStep 3117311 = 4675967) B4675967
theorem B5902955 : Blo 920579 5902955 := bstep (se 1 (by rfl) ⟨4427216, by rfl⟩ : syracuseStep 5902955 = 8854433) B8854433
theorem B1381097 : Blo 920579 1381097 := bstep (se 2 (by rfl) ⟨517911, by rfl⟩ : syracuseStep 1381097 = 1035823) B1035823
theorem B2954015 : Blo 920579 2954015 := bstep (se 1 (by rfl) ⟨2215511, by rfl⟩ : syracuseStep 2954015 = 4431023) B4431023
theorem B1479455 : Blo 920579 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B1970983 : Blo 920579 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B922439 : Blo 920579 922439 := bstep (se 1 (by rfl) ⟨691829, by rfl⟩ : syracuseStep 922439 = 1383659) B1383659
theorem B1381319 : Blo 920579 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B1381355 : Blo 920579 1381355 := bstep (se 1 (by rfl) ⟨1036016, by rfl⟩ : syracuseStep 1381355 = 2072033) B2072033
theorem B3119039 : Blo 920579 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B1382447 : Blo 920579 1382447 := bstep (se 1 (by rfl) ⟨1036835, by rfl⟩ : syracuseStep 1382447 = 2073671) B2073671
theorem B923775 : Blo 920579 923775 := bstep (se 1 (by rfl) ⟨692831, by rfl⟩ : syracuseStep 923775 = 1385663) B1385663
theorem B923871 : Blo 920579 923871 := bstep (se 1 (by rfl) ⟨692903, by rfl⟩ : syracuseStep 923871 = 1385807) B1385807
theorem B9246959 : Blo 920579 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B923899 : Blo 920579 923899 := bstep (se 1 (by rfl) ⟨692924, by rfl⟩ : syracuseStep 923899 = 1385849) B1385849
theorem B924031 : Blo 920579 924031 := bstep (se 1 (by rfl) ⟨693023, by rfl⟩ : syracuseStep 924031 = 1386047) B1386047
theorem B924351 : Blo 920579 924351 := bstep (se 1 (by rfl) ⟨693263, by rfl⟩ : syracuseStep 924351 = 1386527) B1386527
theorem B145824785 : Blo 920579 145824785 := bstep (se 2 (by rfl) ⟨54684294, by rfl⟩ : syracuseStep 145824785 = 109368589) B109368589
theorem B1383593 : Blo 920579 1383593 := bstep (se 2 (by rfl) ⟨518847, by rfl⟩ : syracuseStep 1383593 = 1037695) B1037695
theorem B2071727 : Blo 920579 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B7019783 : Blo 920579 7019783 := bstep (se 1 (by rfl) ⟨5264837, by rfl⟩ : syracuseStep 7019783 = 10529675) B10529675
theorem B2071835 : Blo 920579 2071835 := bstep (se 1 (by rfl) ⟨1553876, by rfl⟩ : syracuseStep 2071835 = 3107753) B3107753
theorem B2334683 : Blo 920579 2334683 := bstep (se 1 (by rfl) ⟨1751012, by rfl⟩ : syracuseStep 2334683 = 3502025) B3502025
theorem B1384943 : Blo 920579 1384943 := bstep (se 1 (by rfl) ⟨1038707, by rfl⟩ : syracuseStep 1384943 = 2077415) B2077415
theorem B1385015 : Blo 920579 1385015 := bstep (se 1 (by rfl) ⟨1038761, by rfl⟩ : syracuseStep 1385015 = 2077523) B2077523
theorem B10494683 : Blo 920579 10494683 := bstep (se 1 (by rfl) ⟨7871012, by rfl⟩ : syracuseStep 10494683 = 15742025) B15742025
theorem B2630825 : Blo 920579 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B2335999 : Blo 920579 2335999 := bstep (se 1 (by rfl) ⟨1751999, by rfl⟩ : syracuseStep 2335999 = 3503999) B3503999
theorem B1385831 : Blo 920579 1385831 := bstep (se 1 (by rfl) ⟨1039373, by rfl⟩ : syracuseStep 1385831 = 2078747) B2078747
theorem B2073977 : Blo 920579 2073977 := bstep (se 2 (by rfl) ⟨777741, by rfl⟩ : syracuseStep 2073977 = 1555483) B1555483
theorem B2074067 : Blo 920579 2074067 := bstep (se 1 (by rfl) ⟨1555550, by rfl⟩ : syracuseStep 2074067 = 3111101) B3111101
theorem B2074283 : Blo 920579 2074283 := bstep (se 1 (by rfl) ⟨1555712, by rfl⟩ : syracuseStep 2074283 = 3111425) B3111425
theorem B8858429 : Blo 920579 8858429 := bstep (se 3 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 8858429 = 3321911) B3321911
theorem B2338105 : Blo 920579 2338105 := bstep (se 2 (by rfl) ⟨876789, by rfl⟩ : syracuseStep 2338105 = 1753579) B1753579
theorem B2338409 : Blo 920579 2338409 := bstep (se 2 (by rfl) ⟨876903, by rfl⟩ : syracuseStep 2338409 = 1753807) B1753807
theorem B2076767 : Blo 920579 2076767 := bstep (se 1 (by rfl) ⟨1557575, by rfl⟩ : syracuseStep 2076767 = 3115151) B3115151
theorem B2076839 : Blo 920579 2076839 := bstep (se 1 (by rfl) ⟨1557629, by rfl⟩ : syracuseStep 2076839 = 3115259) B3115259
theorem B4665599 : Blo 920579 4665599 := bstep (se 1 (by rfl) ⟨3499199, by rfl⟩ : syracuseStep 4665599 = 6998399) B6998399
theorem B6992567 : Blo 920579 6992567 := bstep (se 1 (by rfl) ⟨5244425, by rfl⟩ : syracuseStep 6992567 = 10488851) B10488851
theorem B2995177 : Blo 920579 2995177 := bstep (se 2 (by rfl) ⟨1123191, by rfl⟩ : syracuseStep 2995177 = 2246383) B2246383
theorem B1553519 : Blo 920579 1553519 := bstep (se 1 (by rfl) ⟨1165139, by rfl⟩ : syracuseStep 1553519 = 2330279) B2330279
theorem B2077883 : Blo 920579 2077883 := bstep (se 1 (by rfl) ⟨1558412, by rfl⟩ : syracuseStep 2077883 = 3116825) B3116825
theorem B2078009 : Blo 920579 2078009 := bstep (se 2 (by rfl) ⟨779253, by rfl⟩ : syracuseStep 2078009 = 1558507) B1558507
theorem B1750511 : Blo 920579 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B22787609 : Blo 920579 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B1553951 : Blo 920579 1553951 := bstep (se 1 (by rfl) ⟨1165463, by rfl⟩ : syracuseStep 1553951 = 2330927) B2330927
theorem B22460651 : Blo 920579 22460651 := bstep (se 1 (by rfl) ⟨16845488, by rfl⟩ : syracuseStep 22460651 = 33690977) B33690977
theorem B4667705 : Blo 920579 4667705 := bstep (se 2 (by rfl) ⟨1750389, by rfl⟩ : syracuseStep 4667705 = 3500779) B3500779
theorem B1554815 : Blo 920579 1554815 := bstep (se 1 (by rfl) ⟨1166111, by rfl⟩ : syracuseStep 1554815 = 2332223) B2332223
theorem B10500515 : Blo 920579 10500515 := bstep (se 1 (by rfl) ⟨7875386, by rfl⟩ : syracuseStep 10500515 = 15750773) B15750773
theorem B4667867 : Blo 920579 4667867 := bstep (se 1 (by rfl) ⟨3500900, by rfl⟩ : syracuseStep 4667867 = 7001801) B7001801
theorem B1751719 : Blo 920579 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B2079611 : Blo 920579 2079611 := bstep (se 1 (by rfl) ⟨1559708, by rfl⟩ : syracuseStep 2079611 = 3119417) B3119417
theorem B5258141 : Blo 920579 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B1555753 : Blo 920579 1555753 := bstep (se 2 (by rfl) ⟨583407, by rfl⟩ : syracuseStep 1555753 = 1166815) B1166815
theorem B6995483 : Blo 920579 6995483 := bstep (se 1 (by rfl) ⟨5246612, by rfl⟩ : syracuseStep 6995483 = 10493225) B10493225
theorem B1752607 : Blo 920579 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B3948527 : Blo 920579 3948527 := bstep (se 1 (by rfl) ⟨2961395, by rfl⟩ : syracuseStep 3948527 = 5922791) B5922791
theorem B1557211 : Blo 920579 1557211 := bstep (se 1 (by rfl) ⟨1167908, by rfl⟩ : syracuseStep 1557211 = 2335817) B2335817
theorem B1558271 : Blo 920579 1558271 := bstep (se 1 (by rfl) ⟨1168703, by rfl⟩ : syracuseStep 1558271 = 2337407) B2337407
theorem B1558649 : Blo 920579 1558649 := bstep (se 2 (by rfl) ⟨584493, by rfl⟩ : syracuseStep 1558649 = 1168987) B1168987
theorem B9980435 : Blo 920579 9980435 := bstep (se 1 (by rfl) ⟨7485326, by rfl⟩ : syracuseStep 9980435 = 14970653) B14970653
theorem B7883315 : Blo 920579 7883315 := bstep (se 1 (by rfl) ⟨5912486, by rfl⟩ : syracuseStep 7883315 = 11824973) B11824973
theorem B13290641 : Blo 920579 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B3001555 : Blo 920579 3001555 := bstep (se 1 (by rfl) ⟨2251166, by rfl⟩ : syracuseStep 3001555 = 4502333) B4502333
theorem B1559803 : Blo 920579 1559803 := bstep (se 1 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 1559803 = 2339705) B2339705
theorem B7885025 : Blo 920579 7885025 := bstep (se 2 (by rfl) ⟨2956884, by rfl⟩ : syracuseStep 7885025 = 5913769) B5913769
theorem B1036615 : Blo 920579 1036615 := bstep (se 1 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 1036615 = 1554923) B1554923
theorem B1037479 : Blo 920579 1037479 := bstep (se 1 (by rfl) ⟨778109, by rfl⟩ : syracuseStep 1037479 = 1556219) B1556219
theorem B5920073 : Blo 920579 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B5264747 : Blo 920579 5264747 := bstep (se 1 (by rfl) ⟨3948560, by rfl⟩ : syracuseStep 5264747 = 7897121) B7897121
theorem B1038271 : Blo 920579 1038271 := bstep (se 1 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 1038271 = 1557407) B1557407
theorem B2808361 : Blo 920579 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B13327031 : Blo 920579 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B22404023 : Blo 920579 22404023 := bstep (se 1 (by rfl) ⟨16803017, by rfl⟩ : syracuseStep 22404023 = 33606035) B33606035
theorem B2219327 : Blo 920579 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B3497849 : Blo 920579 3497849 := bstep (se 2 (by rfl) ⟨1311693, by rfl⟩ : syracuseStep 3497849 = 2623387) B2623387
theorem B4055183 : Blo 920579 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B3501083 : Blo 920579 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B3501751 : Blo 920579 3501751 := bstep (se 1 (by rfl) ⟨2626313, by rfl⟩ : syracuseStep 3501751 = 5252627) B5252627
theorem B3108671 : Blo 920579 3108671 := bstep (se 1 (by rfl) ⟨2331503, by rfl⟩ : syracuseStep 3108671 = 4663007) B4663007
theorem B5600087 : Blo 920579 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B3109913 : Blo 920579 3109913 := bstep (se 2 (by rfl) ⟨1166217, by rfl⟩ : syracuseStep 3109913 = 2332435) B2332435
theorem B4978091 : Blo 920579 4978091 := bstep (se 1 (by rfl) ⟨3733568, by rfl⟩ : syracuseStep 4978091 = 7467137) B7467137
theorem B29915243 : Blo 920579 29915243 := bstep (se 1 (by rfl) ⟨22436432, by rfl⟩ : syracuseStep 29915243 = 44872865) B44872865
theorem B31914755 : Blo 920579 31914755 := bstep (se 1 (by rfl) ⟨23936066, by rfl⟩ : syracuseStep 31914755 = 47872133) B47872133
theorem B22772819 : Blo 920579 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B3112127 : Blo 920579 3112127 := bstep (se 1 (by rfl) ⟨2334095, by rfl⟩ : syracuseStep 3112127 = 4668191) B4668191
theorem B3112505 : Blo 920579 3112505 := bstep (se 2 (by rfl) ⟨1167189, by rfl⟩ : syracuseStep 3112505 = 2334379) B2334379
theorem B51118573 : Blo 920579 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B983783 : Blo 920579 983783 := bstep (se 1 (by rfl) ⟨737837, by rfl⟩ : syracuseStep 983783 = 1475675) B1475675
theorem B8848511 : Blo 920579 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B3736991 : Blo 920579 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B2950759 : Blo 920579 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B3114665 : Blo 920579 3114665 := bstep (se 2 (by rfl) ⟨1167999, by rfl⟩ : syracuseStep 3114665 = 2335999) B2335999
theorem B3935303 : Blo 920579 3935303 := bstep (se 1 (by rfl) ⟨2951477, by rfl⟩ : syracuseStep 3935303 = 5902955) B5902955
theorem B18222161 : Blo 920579 18222161 := bstep (se 2 (by rfl) ⟨6833310, by rfl⟩ : syracuseStep 18222161 = 13666621) B13666621
theorem B920731 : Blo 920579 920731 := bstep (se 1 (by rfl) ⟨690548, by rfl⟩ : syracuseStep 920731 = 1381097) B1381097
theorem B1969343 : Blo 920579 1969343 := bstep (se 1 (by rfl) ⟨1477007, by rfl⟩ : syracuseStep 1969343 = 2954015) B2954015
theorem B986303 : Blo 920579 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B920879 : Blo 920579 920879 := bstep (se 1 (by rfl) ⟨690659, by rfl⟩ : syracuseStep 920879 = 1381319) B1381319
theorem B920903 : Blo 920579 920903 := bstep (se 1 (by rfl) ⟨690677, by rfl⟩ : syracuseStep 920903 = 1381355) B1381355
theorem B3509831 : Blo 920579 3509831 := bstep (se 1 (by rfl) ⟨2632373, by rfl⟩ : syracuseStep 3509831 = 5264747) B5264747
theorem B921631 : Blo 920579 921631 := bstep (se 1 (by rfl) ⟨691223, by rfl⟩ : syracuseStep 921631 = 1382447) B1382447
theorem B6164639 : Blo 920579 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B2625949 : Blo 920579 2625949 := bstep (se 3 (by rfl) ⟨492365, by rfl⟩ : syracuseStep 2625949 = 984731) B984731
theorem B3117473 : Blo 920579 3117473 := bstep (se 2 (by rfl) ⟨1169052, by rfl⟩ : syracuseStep 3117473 = 2338105) B2338105
theorem B2101673 : Blo 920579 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B8884687 : Blo 920579 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B922395 : Blo 920579 922395 := bstep (se 1 (by rfl) ⟨691796, by rfl⟩ : syracuseStep 922395 = 1383593) B1383593
theorem B1381151 : Blo 920579 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B1381223 : Blo 920579 1381223 := bstep (se 1 (by rfl) ⟨1035917, by rfl⟩ : syracuseStep 1381223 = 2071835) B2071835
theorem B1479551 : Blo 920579 1479551 := bstep (se 1 (by rfl) ⟨1109663, by rfl⟩ : syracuseStep 1479551 = 2219327) B2219327
theorem B2331899 : Blo 920579 2331899 := bstep (se 1 (by rfl) ⟨1748924, by rfl⟩ : syracuseStep 2331899 = 3497849) B3497849
theorem B923295 : Blo 920579 923295 := bstep (se 1 (by rfl) ⟨692471, by rfl⟩ : syracuseStep 923295 = 1384943) B1384943
theorem B923343 : Blo 920579 923343 := bstep (se 1 (by rfl) ⟨692507, by rfl⟩ : syracuseStep 923343 = 1385015) B1385015
theorem B1382153 : Blo 920579 1382153 := bstep (se 2 (by rfl) ⟨518307, by rfl⟩ : syracuseStep 1382153 = 1036615) B1036615
theorem B2627453 : Blo 920579 2627453 := bstep (se 3 (by rfl) ⟨492647, by rfl⟩ : syracuseStep 2627453 = 985295) B985295
theorem B923887 : Blo 920579 923887 := bstep (se 1 (by rfl) ⟨692915, by rfl⟩ : syracuseStep 923887 = 1385831) B1385831
theorem B1382651 : Blo 920579 1382651 := bstep (se 1 (by rfl) ⟨1036988, by rfl⟩ : syracuseStep 1382651 = 2073977) B2073977
theorem B1382711 : Blo 920579 1382711 := bstep (se 1 (by rfl) ⟨1037033, by rfl⟩ : syracuseStep 1382711 = 2074067) B2074067
theorem B2627977 : Blo 920579 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B1382855 : Blo 920579 1382855 := bstep (se 1 (by rfl) ⟨1037141, by rfl⟩ : syracuseStep 1382855 = 2074283) B2074283
theorem B26614493 : Blo 920579 26614493 := bstep (se 3 (by rfl) ⟨4990217, by rfl⟩ : syracuseStep 26614493 = 9980435) B9980435
theorem B1383305 : Blo 920579 1383305 := bstep (se 2 (by rfl) ⟨518739, by rfl⟩ : syracuseStep 1383305 = 1037479) B1037479
theorem B5905619 : Blo 920579 5905619 := bstep (se 1 (by rfl) ⟨4429214, by rfl⟩ : syracuseStep 5905619 = 8858429) B8858429
theorem B2334055 : Blo 920579 2334055 := bstep (se 1 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 2334055 = 3501083) B3501083
theorem B2072447 : Blo 920579 2072447 := bstep (se 1 (by rfl) ⟨1554335, by rfl⟩ : syracuseStep 2072447 = 3108671) B3108671
theorem B1384361 : Blo 920579 1384361 := bstep (se 2 (by rfl) ⟨519135, by rfl⟩ : syracuseStep 1384361 = 1038271) B1038271
theorem B1384511 : Blo 920579 1384511 := bstep (se 1 (by rfl) ⟨1038383, by rfl⟩ : syracuseStep 1384511 = 2076767) B2076767
theorem B1384559 : Blo 920579 1384559 := bstep (se 1 (by rfl) ⟨1038419, by rfl⟩ : syracuseStep 1384559 = 2076839) B2076839
theorem B4661711 : Blo 920579 4661711 := bstep (se 1 (by rfl) ⟨3496283, by rfl⟩ : syracuseStep 4661711 = 6992567) B6992567
theorem B2073275 : Blo 920579 2073275 := bstep (se 1 (by rfl) ⟨1554956, by rfl⟩ : syracuseStep 2073275 = 3109913) B3109913
theorem B3744481 : Blo 920579 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B1385255 : Blo 920579 1385255 := bstep (se 1 (by rfl) ⟨1038941, by rfl⟩ : syracuseStep 1385255 = 2077883) B2077883
theorem B1385339 : Blo 920579 1385339 := bstep (se 1 (by rfl) ⟨1039004, by rfl⟩ : syracuseStep 1385339 = 2078009) B2078009
theorem B2335625 : Blo 920579 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B3318727 : Blo 920579 3318727 := bstep (se 1 (by rfl) ⟨2489045, by rfl⟩ : syracuseStep 3318727 = 4978091) B4978091
theorem B2074337 : Blo 920579 2074337 := bstep (se 2 (by rfl) ⟨777876, by rfl⟩ : syracuseStep 2074337 = 1555753) B1555753
theorem B21276503 : Blo 920579 21276503 := bstep (se 1 (by rfl) ⟨15957377, by rfl⟩ : syracuseStep 21276503 = 31914755) B31914755
theorem B1386407 : Blo 920579 1386407 := bstep (se 1 (by rfl) ⟨1039805, by rfl⟩ : syracuseStep 1386407 = 2079611) B2079611
theorem B2336809 : Blo 920579 2336809 := bstep (se 2 (by rfl) ⟨876303, by rfl⟩ : syracuseStep 2336809 = 1752607) B1752607
theorem B15181879 : Blo 920579 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B2074751 : Blo 920579 2074751 := bstep (se 1 (by rfl) ⟨1556063, by rfl⟩ : syracuseStep 2074751 = 3112127) B3112127
theorem B4663655 : Blo 920579 4663655 := bstep (se 1 (by rfl) ⟨3497741, by rfl⟩ : syracuseStep 4663655 = 6995483) B6995483
theorem B2075003 : Blo 920579 2075003 := bstep (se 1 (by rfl) ⟨1556252, by rfl⟩ : syracuseStep 2075003 = 3112505) B3112505
theorem B2632351 : Blo 920579 2632351 := bstep (se 1 (by rfl) ⟨1974263, by rfl⟩ : syracuseStep 2632351 = 3948527) B3948527
theorem B2075327 : Blo 920579 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B2075759 : Blo 920579 2075759 := bstep (se 1 (by rfl) ⟨1556819, by rfl⟩ : syracuseStep 2075759 = 3113639) B3113639
theorem B2075903 : Blo 920579 2075903 := bstep (se 1 (by rfl) ⟨1556927, by rfl⟩ : syracuseStep 2075903 = 3113855) B3113855
theorem B2075975 : Blo 920579 2075975 := bstep (se 1 (by rfl) ⟨1556981, by rfl⟩ : syracuseStep 2075975 = 3113963) B3113963
theorem B2076281 : Blo 920579 2076281 := bstep (se 2 (by rfl) ⟨778605, by rfl⟩ : syracuseStep 2076281 = 1557211) B1557211
theorem B1748719 : Blo 920579 1748719 := bstep (se 1 (by rfl) ⟨1311539, by rfl⟩ : syracuseStep 1748719 = 2623079) B2623079
theorem B8433551 : Blo 920579 8433551 := bstep (se 1 (by rfl) ⟨6325163, by rfl⟩ : syracuseStep 8433551 = 12650327) B12650327
theorem B5255543 : Blo 920579 5255543 := bstep (se 1 (by rfl) ⟨3941657, by rfl⟩ : syracuseStep 5255543 = 7883315) B7883315
theorem B5681821 : Blo 920579 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B8860427 : Blo 920579 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B2077631 : Blo 920579 2077631 := bstep (se 1 (by rfl) ⟨1558223, by rfl⟩ : syracuseStep 2077631 = 3116447) B3116447
theorem B2078063 : Blo 920579 2078063 := bstep (se 1 (by rfl) ⟨1558547, by rfl⟩ : syracuseStep 2078063 = 3117095) B3117095
theorem B5256683 : Blo 920579 5256683 := bstep (se 1 (by rfl) ⟨3942512, by rfl⟩ : syracuseStep 5256683 = 7885025) B7885025
theorem B2274799 : Blo 920579 2274799 := bstep (se 1 (by rfl) ⟨1706099, by rfl⟩ : syracuseStep 2274799 = 3412199) B3412199
theorem B2078207 : Blo 920579 2078207 := bstep (se 1 (by rfl) ⟨1558655, by rfl⟩ : syracuseStep 2078207 = 3117311) B3117311
theorem B3946715 : Blo 920579 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B4668029 : Blo 920579 4668029 := bstep (se 3 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 4668029 = 1750511) B1750511
theorem B2079359 : Blo 920579 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B60766957 : Blo 920579 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B2079737 : Blo 920579 2079737 := bstep (se 2 (by rfl) ⟨779901, by rfl⟩ : syracuseStep 2079737 = 1559803) B1559803
theorem B4669001 : Blo 920579 4669001 := bstep (se 2 (by rfl) ⟨1750875, by rfl⟩ : syracuseStep 4669001 = 3501751) B3501751
theorem B1556455 : Blo 920579 1556455 := bstep (se 1 (by rfl) ⟨1167341, by rfl⟩ : syracuseStep 1556455 = 2334683) B2334683
theorem B2703455 : Blo 920579 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B6996455 : Blo 920579 6996455 := bstep (se 1 (by rfl) ⟨5247341, by rfl⟩ : syracuseStep 6996455 = 10494683) B10494683
theorem B1753883 : Blo 920579 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B16008293 : Blo 920579 16008293 := bstep (se 4 (by rfl) ⟨1500777, by rfl⟩ : syracuseStep 16008293 = 3001555) B3001555
theorem B1558939 : Blo 920579 1558939 := bstep (se 1 (by rfl) ⟨1169204, by rfl⟩ : syracuseStep 1558939 = 2338409) B2338409
theorem B1035679 : Blo 920579 1035679 := bstep (se 1 (by rfl) ⟨776759, by rfl⟩ : syracuseStep 1035679 = 1553519) B1553519
theorem B1035967 : Blo 920579 1035967 := bstep (se 1 (by rfl) ⟨776975, by rfl⟩ : syracuseStep 1035967 = 1553951) B1553951
theorem B19943495 : Blo 920579 19943495 := bstep (se 1 (by rfl) ⟨14957621, by rfl⟩ : syracuseStep 19943495 = 29915243) B29915243
theorem B1036543 : Blo 920579 1036543 := bstep (se 1 (by rfl) ⟨777407, by rfl⟩ : syracuseStep 1036543 = 1554815) B1554815
theorem B7000343 : Blo 920579 7000343 := bstep (se 1 (by rfl) ⟨5250257, by rfl⟩ : syracuseStep 7000343 = 10500515) B10500515
theorem B4216411 : Blo 920579 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1038847 : Blo 920579 1038847 := bstep (se 1 (by rfl) ⟨779135, by rfl⟩ : syracuseStep 1038847 = 1558271) B1558271
theorem B1039099 : Blo 920579 1039099 := bstep (se 1 (by rfl) ⟨779324, by rfl⟩ : syracuseStep 1039099 = 1558649) B1558649
theorem B4677263 : Blo 920579 4677263 := bstep (se 1 (by rfl) ⟨3507947, by rfl⟩ : syracuseStep 4677263 = 7015895) B7015895
theorem B14936015 : Blo 920579 14936015 := bstep (se 1 (by rfl) ⟨11202011, by rfl⟩ : syracuseStep 14936015 = 22404023) B22404023
theorem B97216523 : Blo 920579 97216523 := bstep (se 1 (by rfl) ⟨72912392, by rfl⟩ : syracuseStep 97216523 = 145824785) B145824785
theorem B4679855 : Blo 920579 4679855 := bstep (se 1 (by rfl) ⟨3509891, by rfl⟩ : syracuseStep 4679855 = 7019783) B7019783
theorem B3993569 : Blo 920579 3993569 := bstep (se 2 (by rfl) ⟨1497588, by rfl⟩ : syracuseStep 3993569 = 2995177) B2995177
theorem B3110399 : Blo 920579 3110399 := bstep (se 1 (by rfl) ⟨2332799, by rfl⟩ : syracuseStep 3110399 = 4665599) B4665599
theorem B3733391 : Blo 920579 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B14973767 : Blo 920579 14973767 := bstep (se 1 (by rfl) ⟨11230325, by rfl⟩ : syracuseStep 14973767 = 22460651) B22460651
theorem B3111803 : Blo 920579 3111803 := bstep (se 1 (by rfl) ⟨2333852, by rfl⟩ : syracuseStep 3111803 = 4667705) B4667705
theorem B3111911 : Blo 920579 3111911 := bstep (se 1 (by rfl) ⟨2333933, by rfl⟩ : syracuseStep 3111911 = 4667867) B4667867
theorem B3505427 : Blo 920579 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B1802303 : Blo 920579 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B68158097 : Blo 920579 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B5899007 : Blo 920579 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B2491327 : Blo 920579 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B5604461 : Blo 920579 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B4424969 : Blo 920579 4424969 := bstep (se 2 (by rfl) ⟨1659363, by rfl⟩ : syracuseStep 4424969 = 3318727) B3318727
theorem B2623421 : Blo 920579 2623421 := bstep (se 3 (by rfl) ⟨491891, by rfl⟩ : syracuseStep 2623421 = 983783) B983783
theorem B2623535 : Blo 920579 2623535 := bstep (se 1 (by rfl) ⟨1967651, by rfl⟩ : syracuseStep 2623535 = 3935303) B3935303
theorem B1312895 : Blo 920579 1312895 := bstep (se 1 (by rfl) ⟨984671, by rfl⟩ : syracuseStep 1312895 = 1969343) B1969343
theorem B3934345 : Blo 920579 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B3115745 : Blo 920579 3115745 := bstep (se 2 (by rfl) ⟨1168404, by rfl⟩ : syracuseStep 3115745 = 2336809) B2336809
theorem B920767 : Blo 920579 920767 := bstep (se 1 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 920767 = 1381151) B1381151
theorem B920815 : Blo 920579 920815 := bstep (se 1 (by rfl) ⟨690611, by rfl⟩ : syracuseStep 920815 = 1381223) B1381223
theorem B3509801 : Blo 920579 3509801 := bstep (se 2 (by rfl) ⟨1316175, by rfl⟩ : syracuseStep 3509801 = 2632351) B2632351
theorem B921435 : Blo 920579 921435 := bstep (se 1 (by rfl) ⟨691076, by rfl⟩ : syracuseStep 921435 = 1382153) B1382153
theorem B921767 : Blo 920579 921767 := bstep (se 1 (by rfl) ⟨691325, by rfl⟩ : syracuseStep 921767 = 1382651) B1382651
theorem B921807 : Blo 920579 921807 := bstep (se 1 (by rfl) ⟨691355, by rfl⟩ : syracuseStep 921807 = 1382711) B1382711
theorem B921903 : Blo 920579 921903 := bstep (se 1 (by rfl) ⟨691427, by rfl⟩ : syracuseStep 921903 = 1382855) B1382855
theorem B1380905 : Blo 920579 1380905 := bstep (se 2 (by rfl) ⟨517839, by rfl⟩ : syracuseStep 1380905 = 1035679) B1035679
theorem B922203 : Blo 920579 922203 := bstep (se 1 (by rfl) ⟨691652, by rfl⟩ : syracuseStep 922203 = 1383305) B1383305
theorem B3937079 : Blo 920579 3937079 := bstep (se 1 (by rfl) ⟨2952809, by rfl⟩ : syracuseStep 3937079 = 5905619) B5905619
theorem B1381289 : Blo 920579 1381289 := bstep (se 2 (by rfl) ⟨517983, by rfl⟩ : syracuseStep 1381289 = 1035967) B1035967
theorem B2331625 : Blo 920579 2331625 := bstep (se 2 (by rfl) ⟨874359, by rfl⟩ : syracuseStep 2331625 = 1748719) B1748719
theorem B3118175 : Blo 920579 3118175 := bstep (se 1 (by rfl) ⟨2338631, by rfl⟩ : syracuseStep 3118175 = 4677263) B4677263
theorem B1381631 : Blo 920579 1381631 := bstep (se 1 (by rfl) ⟨1036223, by rfl⟩ : syracuseStep 1381631 = 2072447) B2072447
theorem B922907 : Blo 920579 922907 := bstep (se 1 (by rfl) ⟨692180, by rfl⟩ : syracuseStep 922907 = 1384361) B1384361
theorem B923007 : Blo 920579 923007 := bstep (se 1 (by rfl) ⟨692255, by rfl⟩ : syracuseStep 923007 = 1384511) B1384511
theorem B923039 : Blo 920579 923039 := bstep (se 1 (by rfl) ⟨692279, by rfl⟩ : syracuseStep 923039 = 1384559) B1384559
theorem B1382057 : Blo 920579 1382057 := bstep (se 2 (by rfl) ⟨518271, by rfl⟩ : syracuseStep 1382057 = 1036543) B1036543
theorem B1382183 : Blo 920579 1382183 := bstep (se 1 (by rfl) ⟨1036637, by rfl⟩ : syracuseStep 1382183 = 2073275) B2073275
theorem B923503 : Blo 920579 923503 := bstep (se 1 (by rfl) ⟨692627, by rfl⟩ : syracuseStep 923503 = 1385255) B1385255
theorem B923559 : Blo 920579 923559 := bstep (se 1 (by rfl) ⟨692669, by rfl⟩ : syracuseStep 923559 = 1385339) B1385339
theorem B7575761 : Blo 920579 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B1382891 : Blo 920579 1382891 := bstep (se 1 (by rfl) ⟨1037168, by rfl⟩ : syracuseStep 1382891 = 2074337) B2074337
theorem B924271 : Blo 920579 924271 := bstep (se 1 (by rfl) ⟨693203, by rfl⟩ : syracuseStep 924271 = 1386407) B1386407
theorem B1383167 : Blo 920579 1383167 := bstep (se 1 (by rfl) ⟨1037375, by rfl⟩ : syracuseStep 1383167 = 2074751) B2074751
theorem B3119903 : Blo 920579 3119903 := bstep (se 1 (by rfl) ⟨2339927, by rfl⟩ : syracuseStep 3119903 = 4679855) B4679855
theorem B1383335 : Blo 920579 1383335 := bstep (se 1 (by rfl) ⟨1037501, by rfl⟩ : syracuseStep 1383335 = 2075003) B2075003
theorem B1383551 : Blo 920579 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B1383839 : Blo 920579 1383839 := bstep (se 1 (by rfl) ⟨1037879, by rfl⟩ : syracuseStep 1383839 = 2075759) B2075759
theorem B1383935 : Blo 920579 1383935 := bstep (se 1 (by rfl) ⟨1037951, by rfl⟩ : syracuseStep 1383935 = 2075903) B2075903
theorem B1383983 : Blo 920579 1383983 := bstep (se 1 (by rfl) ⟨1037987, by rfl⟩ : syracuseStep 1383983 = 2075975) B2075975
theorem B1384187 : Blo 920579 1384187 := bstep (se 1 (by rfl) ⟨1038140, by rfl⟩ : syracuseStep 1384187 = 2076281) B2076281
theorem B2662379 : Blo 920579 2662379 := bstep (se 1 (by rfl) ⟨1996784, by rfl⟩ : syracuseStep 2662379 = 3993569) B3993569
theorem B2630141 : Blo 920579 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B5906951 : Blo 920579 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B1385087 : Blo 920579 1385087 := bstep (se 1 (by rfl) ⟨1038815, by rfl⟩ : syracuseStep 1385087 = 2077631) B2077631
theorem B1385129 : Blo 920579 1385129 := bstep (se 2 (by rfl) ⟨519423, by rfl⟩ : syracuseStep 1385129 = 1038847) B1038847
theorem B1385375 : Blo 920579 1385375 := bstep (se 1 (by rfl) ⟨1039031, by rfl⟩ : syracuseStep 1385375 = 2078063) B2078063
theorem B1385465 : Blo 920579 1385465 := bstep (se 2 (by rfl) ⟨519549, by rfl⟩ : syracuseStep 1385465 = 1039099) B1039099
theorem B2073599 : Blo 920579 2073599 := bstep (se 1 (by rfl) ⟨1555199, by rfl⟩ : syracuseStep 2073599 = 3110399) B3110399
theorem B1385471 : Blo 920579 1385471 := bstep (se 1 (by rfl) ⟨1039103, by rfl⟩ : syracuseStep 1385471 = 2078207) B2078207
theorem B2631143 : Blo 920579 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B1386239 : Blo 920579 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B2074535 : Blo 920579 2074535 := bstep (se 1 (by rfl) ⟨1555901, by rfl⟩ : syracuseStep 2074535 = 3111803) B3111803
theorem B2074607 : Blo 920579 2074607 := bstep (se 1 (by rfl) ⟨1555955, by rfl⟩ : syracuseStep 2074607 = 3111911) B3111911
theorem B1386491 : Blo 920579 1386491 := bstep (se 1 (by rfl) ⟨1039868, by rfl⟩ : syracuseStep 1386491 = 2079737) B2079737
theorem B2336951 : Blo 920579 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B2075273 : Blo 920579 2075273 := bstep (se 2 (by rfl) ⟨778227, by rfl⟩ : syracuseStep 2075273 = 1556455) B1556455
theorem B4664303 : Blo 920579 4664303 := bstep (se 1 (by rfl) ⟨3498227, by rfl⟩ : syracuseStep 4664303 = 6996455) B6996455
theorem B4992641 : Blo 920579 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B2076443 : Blo 920579 2076443 := bstep (se 1 (by rfl) ⟨1557332, by rfl⟩ : syracuseStep 2076443 = 3114665) B3114665
theorem B3945469 : Blo 920579 3945469 := bstep (se 3 (by rfl) ⟨739775, by rfl⟩ : syracuseStep 3945469 = 1479551) B1479551
theorem B2339887 : Blo 920579 2339887 := bstep (se 1 (by rfl) ⟨1754915, by rfl⟩ : syracuseStep 2339887 = 3509831) B3509831
theorem B4109759 : Blo 920579 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B4666895 : Blo 920579 4666895 := bstep (se 1 (by rfl) ⟨3500171, by rfl⟩ : syracuseStep 4666895 = 7000343) B7000343
theorem B2078315 : Blo 920579 2078315 := bstep (se 1 (by rfl) ⟨1558736, by rfl⟩ : syracuseStep 2078315 = 3117473) B3117473
theorem B2078585 : Blo 920579 2078585 := bstep (se 2 (by rfl) ⟨779469, by rfl⟩ : syracuseStep 2078585 = 1558939) B1558939
theorem B1554599 : Blo 920579 1554599 := bstep (se 1 (by rfl) ⟨1165949, by rfl⟩ : syracuseStep 1554599 = 2331899) B2331899
theorem B1751635 : Blo 920579 1751635 := bstep (se 1 (by rfl) ⟨1313726, by rfl⟩ : syracuseStep 1751635 = 2627453) B2627453
theorem B17742995 : Blo 920579 17742995 := bstep (se 1 (by rfl) ⟨13307246, by rfl⟩ : syracuseStep 17742995 = 26614493) B26614493
theorem B1557083 : Blo 920579 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B11846249 : Blo 920579 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B3033065 : Blo 920579 3033065 := bstep (se 2 (by rfl) ⟨1137399, by rfl⟩ : syracuseStep 3033065 = 2274799) B2274799
theorem B5621881 : Blo 920579 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B5622367 : Blo 920579 5622367 := bstep (se 1 (by rfl) ⟨4216775, by rfl⟩ : syracuseStep 5622367 = 8433551) B8433551
theorem B81022609 : Blo 920579 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B9982511 : Blo 920579 9982511 := bstep (se 1 (by rfl) ⟨7486883, by rfl⟩ : syracuseStep 9982511 = 14973767) B14973767
theorem B1169255 : Blo 920579 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B10672195 : Blo 920579 10672195 := bstep (se 1 (by rfl) ⟨8004146, by rfl⟩ : syracuseStep 10672195 = 16008293) B16008293
theorem B13295663 : Blo 920579 13295663 := bstep (se 1 (by rfl) ⟨9971747, by rfl⟩ : syracuseStep 13295663 = 19943495) B19943495
theorem B20242505 : Blo 920579 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B3107807 : Blo 920579 3107807 := bstep (se 1 (by rfl) ⟨2330855, by rfl⟩ : syracuseStep 3107807 = 4661711) B4661711
theorem B3501265 : Blo 920579 3501265 := bstep (se 2 (by rfl) ⟨1312974, by rfl⟩ : syracuseStep 3501265 = 2625949) B2625949
theorem B14184335 : Blo 920579 14184335 := bstep (se 1 (by rfl) ⟨10638251, by rfl⟩ : syracuseStep 14184335 = 21276503) B21276503
theorem B9957343 : Blo 920579 9957343 := bstep (se 1 (by rfl) ⟨7468007, by rfl⟩ : syracuseStep 9957343 = 14936015) B14936015
theorem B64811015 : Blo 920579 64811015 := bstep (se 1 (by rfl) ⟨48608261, by rfl⟩ : syracuseStep 64811015 = 97216523) B97216523
theorem B3109103 : Blo 920579 3109103 := bstep (se 1 (by rfl) ⟨2331827, by rfl⟩ : syracuseStep 3109103 = 4663655) B4663655
theorem B48592429 : Blo 920579 48592429 := bstep (se 3 (by rfl) ⟨9111080, by rfl⟩ : syracuseStep 48592429 = 18222161) B18222161
theorem B3503695 : Blo 920579 3503695 := bstep (se 1 (by rfl) ⟨2627771, by rfl⟩ : syracuseStep 3503695 = 5255543) B5255543
theorem B3503969 : Blo 920579 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B3504455 : Blo 920579 3504455 := bstep (se 1 (by rfl) ⟨2628341, by rfl⟩ : syracuseStep 3504455 = 5256683) B5256683
theorem B2488927 : Blo 920579 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B3112019 : Blo 920579 3112019 := bstep (se 1 (by rfl) ⟨2334014, by rfl⟩ : syracuseStep 3112019 = 4668029) B4668029
theorem B3112073 : Blo 920579 3112073 := bstep (se 2 (by rfl) ⟨1167027, by rfl⟩ : syracuseStep 3112073 = 2334055) B2334055
theorem B3112667 : Blo 920579 3112667 := bstep (se 1 (by rfl) ⟨2334500, by rfl⟩ : syracuseStep 3112667 = 4669001) B4669001
theorem B7897499 : Blo 920579 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B3932671 : Blo 920579 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B3736307 : Blo 920579 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B2949979 : Blo 920579 2949979 := bstep (se 1 (by rfl) ⟨2212484, by rfl⟩ : syracuseStep 2949979 = 4424969) B4424969
theorem B5245793 : Blo 920579 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B920603 : Blo 920579 920603 := bstep (se 1 (by rfl) ⟨690452, by rfl⟩ : syracuseStep 920603 = 1380905) B1380905
theorem B6655007 : Blo 920579 6655007 := bstep (se 1 (by rfl) ⟨4991255, by rfl⟩ : syracuseStep 6655007 = 9982511) B9982511
theorem B2624719 : Blo 920579 2624719 := bstep (se 1 (by rfl) ⟨1968539, by rfl⟩ : syracuseStep 2624719 = 3937079) B3937079
theorem B920859 : Blo 920579 920859 := bstep (se 1 (by rfl) ⟨690644, by rfl⟩ : syracuseStep 920859 = 1381289) B1381289
theorem B921087 : Blo 920579 921087 := bstep (se 1 (by rfl) ⟨690815, by rfl⟩ : syracuseStep 921087 = 1381631) B1381631
theorem B921371 : Blo 920579 921371 := bstep (se 1 (by rfl) ⟨691028, by rfl⟩ : syracuseStep 921371 = 1382057) B1382057
theorem B921455 : Blo 920579 921455 := bstep (se 1 (by rfl) ⟨691091, by rfl⟩ : syracuseStep 921455 = 1382183) B1382183
theorem B7016381 : Blo 920579 7016381 := bstep (se 3 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 7016381 = 2631143) B2631143
theorem B5050507 : Blo 920579 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B921927 : Blo 920579 921927 := bstep (se 1 (by rfl) ⟨691445, by rfl⟩ : syracuseStep 921927 = 1382891) B1382891
theorem B922111 : Blo 920579 922111 := bstep (se 1 (by rfl) ⟨691583, by rfl⟩ : syracuseStep 922111 = 1383167) B1383167
theorem B922223 : Blo 920579 922223 := bstep (se 1 (by rfl) ⟨691667, by rfl⟩ : syracuseStep 922223 = 1383335) B1383335
theorem B922367 : Blo 920579 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B3118013 : Blo 920579 3118013 := bstep (se 3 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 3118013 = 1169255) B1169255
theorem B922559 : Blo 920579 922559 := bstep (se 1 (by rfl) ⟨691919, by rfl⟩ : syracuseStep 922559 = 1383839) B1383839
theorem B922623 : Blo 920579 922623 := bstep (se 1 (by rfl) ⟨691967, by rfl⟩ : syracuseStep 922623 = 1383935) B1383935
theorem B922655 : Blo 920579 922655 := bstep (se 1 (by rfl) ⟨691991, by rfl⟩ : syracuseStep 922655 = 1383983) B1383983
theorem B922791 : Blo 920579 922791 := bstep (se 1 (by rfl) ⟨692093, by rfl⟩ : syracuseStep 922791 = 1384187) B1384187
theorem B13276457 : Blo 920579 13276457 := bstep (se 2 (by rfl) ⟨4978671, by rfl⟩ : syracuseStep 13276457 = 9957343) B9957343
theorem B1774919 : Blo 920579 1774919 := bstep (se 1 (by rfl) ⟨1331189, by rfl⟩ : syracuseStep 1774919 = 2662379) B2662379
theorem B3937967 : Blo 920579 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B923391 : Blo 920579 923391 := bstep (se 1 (by rfl) ⟨692543, by rfl⟩ : syracuseStep 923391 = 1385087) B1385087
theorem B923419 : Blo 920579 923419 := bstep (se 1 (by rfl) ⟨692564, by rfl⟩ : syracuseStep 923419 = 1385129) B1385129
theorem B923583 : Blo 920579 923583 := bstep (se 1 (by rfl) ⟨692687, by rfl⟩ : syracuseStep 923583 = 1385375) B1385375
theorem B923643 : Blo 920579 923643 := bstep (se 1 (by rfl) ⟨692732, by rfl⟩ : syracuseStep 923643 = 1385465) B1385465
theorem B1382399 : Blo 920579 1382399 := bstep (se 1 (by rfl) ⟨1036799, by rfl⟩ : syracuseStep 1382399 = 2073599) B2073599
theorem B923647 : Blo 920579 923647 := bstep (se 1 (by rfl) ⟨692735, by rfl⟩ : syracuseStep 923647 = 1385471) B1385471
theorem B924159 : Blo 920579 924159 := bstep (se 1 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 924159 = 1386239) B1386239
theorem B1383023 : Blo 920579 1383023 := bstep (se 1 (by rfl) ⟨1037267, by rfl⟩ : syracuseStep 1383023 = 2074535) B2074535
theorem B1383071 : Blo 920579 1383071 := bstep (se 1 (by rfl) ⟨1037303, by rfl⟩ : syracuseStep 1383071 = 2074607) B2074607
theorem B924327 : Blo 920579 924327 := bstep (se 1 (by rfl) ⟨693245, by rfl⟩ : syracuseStep 924327 = 1386491) B1386491
theorem B3119849 : Blo 920579 3119849 := bstep (se 2 (by rfl) ⟨1169943, by rfl⟩ : syracuseStep 3119849 = 2339887) B2339887
theorem B1383515 : Blo 920579 1383515 := bstep (se 1 (by rfl) ⟨1037636, by rfl⟩ : syracuseStep 1383515 = 2075273) B2075273
theorem B2071871 : Blo 920579 2071871 := bstep (se 1 (by rfl) ⟨1553903, by rfl⟩ : syracuseStep 2071871 = 3107807) B3107807
theorem B1384295 : Blo 920579 1384295 := bstep (se 1 (by rfl) ⟨1038221, by rfl⟩ : syracuseStep 1384295 = 2076443) B2076443
theorem B14229593 : Blo 920579 14229593 := bstep (se 2 (by rfl) ⟨5336097, by rfl⟩ : syracuseStep 14229593 = 10672195) B10672195
theorem B2072735 : Blo 920579 2072735 := bstep (se 1 (by rfl) ⟨1554551, by rfl⟩ : syracuseStep 2072735 = 3109103) B3109103
theorem B2335513 : Blo 920579 2335513 := bstep (se 2 (by rfl) ⟨875817, by rfl⟩ : syracuseStep 2335513 = 1751635) B1751635
theorem B3318569 : Blo 920579 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B1385543 : Blo 920579 1385543 := bstep (se 1 (by rfl) ⟨1039157, by rfl⟩ : syracuseStep 1385543 = 2078315) B2078315
theorem B2335979 : Blo 920579 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B1385723 : Blo 920579 1385723 := bstep (se 1 (by rfl) ⟨1039292, by rfl⟩ : syracuseStep 1385723 = 2078585) B2078585
theorem B2336303 : Blo 920579 2336303 := bstep (se 1 (by rfl) ⟨1752227, by rfl⟩ : syracuseStep 2336303 = 3504455) B3504455
theorem B2074679 : Blo 920579 2074679 := bstep (se 1 (by rfl) ⟨1556009, by rfl⟩ : syracuseStep 2074679 = 3112019) B3112019
theorem B2074715 : Blo 920579 2074715 := bstep (se 1 (by rfl) ⟨1556036, by rfl⟩ : syracuseStep 2074715 = 3112073) B3112073
theorem B2075111 : Blo 920579 2075111 := bstep (se 1 (by rfl) ⟨1556333, by rfl⟩ : syracuseStep 2075111 = 3112667) B3112667
theorem B53980013 : Blo 920579 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B3321769 : Blo 920579 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B1748947 : Blo 920579 1748947 := bstep (se 1 (by rfl) ⟨1311710, by rfl⟩ : syracuseStep 1748947 = 2623421) B2623421
theorem B1749023 : Blo 920579 1749023 := bstep (se 1 (by rfl) ⟨1311767, by rfl⟩ : syracuseStep 1749023 = 2623535) B2623535
theorem B2077163 : Blo 920579 2077163 := bstep (se 1 (by rfl) ⟨1557872, by rfl⟩ : syracuseStep 2077163 = 3115745) B3115745
theorem B2339867 : Blo 920579 2339867 := bstep (se 1 (by rfl) ⟨1754900, by rfl⟩ : syracuseStep 2339867 = 3509801) B3509801
theorem B2078783 : Blo 920579 2078783 := bstep (se 1 (by rfl) ⟨1559087, by rfl⟩ : syracuseStep 2078783 = 3118175) B3118175
theorem B4668353 : Blo 920579 4668353 := bstep (se 2 (by rfl) ⟨1750632, by rfl⟩ : syracuseStep 4668353 = 3501265) B3501265
theorem B2079935 : Blo 920579 2079935 := bstep (se 1 (by rfl) ⟨1559951, by rfl⟩ : syracuseStep 2079935 = 3119903) B3119903
theorem B8863775 : Blo 920579 8863775 := bstep (se 1 (by rfl) ⟨6647831, by rfl⟩ : syracuseStep 8863775 = 13295663) B13295663
theorem B1753427 : Blo 920579 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B5260625 : Blo 920579 5260625 := bstep (se 2 (by rfl) ⟨1972734, by rfl⟩ : syracuseStep 5260625 = 3945469) B3945469
theorem B1557967 : Blo 920579 1557967 := bstep (se 1 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 1557967 = 2336951) B2336951
theorem B4671593 : Blo 920579 4671593 := bstep (se 2 (by rfl) ⟨1751847, by rfl⟩ : syracuseStep 4671593 = 3503695) B3503695
theorem B3328427 : Blo 920579 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B9456223 : Blo 920579 9456223 := bstep (se 1 (by rfl) ⟨7092167, by rfl⟩ : syracuseStep 9456223 = 14184335) B14184335
theorem B43207343 : Blo 920579 43207343 := bstep (se 1 (by rfl) ⟨32405507, by rfl⟩ : syracuseStep 43207343 = 64811015) B64811015
theorem B2739839 : Blo 920579 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B1036399 : Blo 920579 1036399 := bstep (se 1 (by rfl) ⟨777299, by rfl⟩ : syracuseStep 1036399 = 1554599) B1554599
theorem B1201535 : Blo 920579 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1038055 : Blo 920579 1038055 := bstep (se 1 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 1038055 = 1557083) B1557083
theorem B45438731 : Blo 920579 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B7495841 : Blo 920579 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B7496489 : Blo 920579 7496489 := bstep (se 2 (by rfl) ⟨2811183, by rfl⟩ : syracuseStep 7496489 = 5622367) B5622367
theorem B108030145 : Blo 920579 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B8088173 : Blo 920579 8088173 := bstep (se 3 (by rfl) ⟨1516532, by rfl⟩ : syracuseStep 8088173 = 3033065) B3033065
theorem B3501053 : Blo 920579 3501053 := bstep (se 3 (by rfl) ⟨656447, by rfl⟩ : syracuseStep 3501053 = 1312895) B1312895
theorem B3108833 : Blo 920579 3108833 := bstep (se 2 (by rfl) ⟨1165812, by rfl⟩ : syracuseStep 3108833 = 2331625) B2331625
theorem B3109535 : Blo 920579 3109535 := bstep (se 1 (by rfl) ⟨2332151, by rfl⟩ : syracuseStep 3109535 = 4664303) B4664303
theorem B259159621 : Blo 920579 259159621 := bstep (se 4 (by rfl) ⟨24296214, by rfl⟩ : syracuseStep 259159621 = 48592429) B48592429
theorem B3111263 : Blo 920579 3111263 := bstep (se 1 (by rfl) ⟨2333447, by rfl⟩ : syracuseStep 3111263 = 4666895) B4666895
theorem B11828663 : Blo 920579 11828663 := bstep (se 1 (by rfl) ⟨8871497, by rfl⟩ : syracuseStep 11828663 = 17742995) B17742995
theorem B5243561 : Blo 920579 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B3507083 : Blo 920579 3507083 := bstep (se 1 (by rfl) ⟨2630312, by rfl⟩ : syracuseStep 3507083 = 5260625) B5260625
theorem B3114017 : Blo 920579 3114017 := bstep (se 2 (by rfl) ⟨1167756, by rfl⟩ : syracuseStep 3114017 = 2335513) B2335513
theorem B3933305 : Blo 920579 3933305 := bstep (se 2 (by rfl) ⟨1474989, by rfl⟩ : syracuseStep 3933305 = 2949979) B2949979
theorem B3114395 : Blo 920579 3114395 := bstep (se 1 (by rfl) ⟨2335796, by rfl⟩ : syracuseStep 3114395 = 4671593) B4671593
theorem B28804895 : Blo 920579 28804895 := bstep (se 1 (by rfl) ⟨21603671, by rfl⟩ : syracuseStep 28804895 = 43207343) B43207343
theorem B9963485 : Blo 920579 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B8850971 : Blo 920579 8850971 := bstep (se 1 (by rfl) ⟨6638228, by rfl⟩ : syracuseStep 8850971 = 13276457) B13276457
theorem B2625311 : Blo 920579 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B12816373 : Blo 920579 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B921599 : Blo 920579 921599 := bstep (se 1 (by rfl) ⟨691199, by rfl⟩ : syracuseStep 921599 = 1382399) B1382399
theorem B922015 : Blo 920579 922015 := bstep (se 1 (by rfl) ⟨691511, by rfl⟩ : syracuseStep 922015 = 1383023) B1383023
theorem B922047 : Blo 920579 922047 := bstep (se 1 (by rfl) ⟨691535, by rfl⟩ : syracuseStep 922047 = 1383071) B1383071
theorem B922343 : Blo 920579 922343 := bstep (se 1 (by rfl) ⟨691757, by rfl⟩ : syracuseStep 922343 = 1383515) B1383515
theorem B1381247 : Blo 920579 1381247 := bstep (se 1 (by rfl) ⟨1035935, by rfl⟩ : syracuseStep 1381247 = 2071871) B2071871
theorem B4429025 : Blo 920579 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B922863 : Blo 920579 922863 := bstep (se 1 (by rfl) ⟨692147, by rfl⟩ : syracuseStep 922863 = 1384295) B1384295
theorem B2331929 : Blo 920579 2331929 := bstep (se 2 (by rfl) ⟨874473, by rfl⟩ : syracuseStep 2331929 = 1748947) B1748947
theorem B1381823 : Blo 920579 1381823 := bstep (se 1 (by rfl) ⟨1036367, by rfl⟩ : syracuseStep 1381823 = 2072735) B2072735
theorem B1381865 : Blo 920579 1381865 := bstep (se 2 (by rfl) ⟨518199, by rfl⟩ : syracuseStep 1381865 = 1036399) B1036399
theorem B923695 : Blo 920579 923695 := bstep (se 1 (by rfl) ⟨692771, by rfl⟩ : syracuseStep 923695 = 1385543) B1385543
theorem B923815 : Blo 920579 923815 := bstep (se 1 (by rfl) ⟨692861, by rfl⟩ : syracuseStep 923815 = 1385723) B1385723
theorem B1383119 : Blo 920579 1383119 := bstep (se 1 (by rfl) ⟨1037339, by rfl⟩ : syracuseStep 1383119 = 2074679) B2074679
theorem B1383143 : Blo 920579 1383143 := bstep (se 1 (by rfl) ⟨1037357, by rfl⟩ : syracuseStep 1383143 = 2074715) B2074715
theorem B1383407 : Blo 920579 1383407 := bstep (se 1 (by rfl) ⟨1037555, by rfl⟩ : syracuseStep 1383407 = 2075111) B2075111
theorem B35986675 : Blo 920579 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B2334035 : Blo 920579 2334035 := bstep (se 1 (by rfl) ⟨1750526, by rfl⟩ : syracuseStep 2334035 = 3501053) B3501053
theorem B345546161 : Blo 920579 345546161 := bstep (se 2 (by rfl) ⟨129579810, by rfl⟩ : syracuseStep 345546161 = 259159621) B259159621
theorem B1384073 : Blo 920579 1384073 := bstep (se 2 (by rfl) ⟨519027, by rfl⟩ : syracuseStep 1384073 = 1038055) B1038055
theorem B2072555 : Blo 920579 2072555 := bstep (se 1 (by rfl) ⟨1554416, by rfl⟩ : syracuseStep 2072555 = 3108833) B3108833
theorem B1384775 : Blo 920579 1384775 := bstep (se 1 (by rfl) ⟨1038581, by rfl⟩ : syracuseStep 1384775 = 2077163) B2077163
theorem B2073023 : Blo 920579 2073023 := bstep (se 1 (by rfl) ⟨1554767, by rfl⟩ : syracuseStep 2073023 = 3109535) B3109535
theorem B1385855 : Blo 920579 1385855 := bstep (se 1 (by rfl) ⟨1039391, by rfl⟩ : syracuseStep 1385855 = 2078783) B2078783
theorem B2074175 : Blo 920579 2074175 := bstep (se 1 (by rfl) ⟨1555631, by rfl⟩ : syracuseStep 2074175 = 3111263) B3111263
theorem B1386623 : Blo 920579 1386623 := bstep (se 1 (by rfl) ⟨1039967, by rfl⟩ : syracuseStep 1386623 = 2079935) B2079935
theorem B5909183 : Blo 920579 5909183 := bstep (se 1 (by rfl) ⟨4431887, by rfl⟩ : syracuseStep 5909183 = 8863775) B8863775
theorem B2077289 : Blo 920579 2077289 := bstep (se 2 (by rfl) ⟨778983, by rfl⟩ : syracuseStep 2077289 = 1557967) B1557967
theorem B2078675 : Blo 920579 2078675 := bstep (se 1 (by rfl) ⟨1559006, by rfl⟩ : syracuseStep 2078675 = 3118013) B3118013
theorem B4733117 : Blo 920579 4733117 := bstep (se 3 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 4733117 = 1774919) B1774919
theorem B30292487 : Blo 920579 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B2079899 : Blo 920579 2079899 := bstep (se 1 (by rfl) ⟨1559924, by rfl⟩ : syracuseStep 2079899 = 3119849) B3119849
theorem B9486395 : Blo 920579 9486395 := bstep (se 1 (by rfl) ⟨7114796, by rfl⟩ : syracuseStep 9486395 = 14229593) B14229593
theorem B4997227 : Blo 920579 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B6734009 : Blo 920579 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B2212379 : Blo 920579 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B4997659 : Blo 920579 4997659 := bstep (se 1 (by rfl) ⟨3748244, by rfl⟩ : syracuseStep 4997659 = 7496489) B7496489
theorem B1557319 : Blo 920579 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1557535 : Blo 920579 1557535 := bstep (se 1 (by rfl) ⟨1168151, by rfl⟩ : syracuseStep 1557535 = 2336303) B2336303
theorem B5392115 : Blo 920579 5392115 := bstep (se 1 (by rfl) ⟨4044086, by rfl⟩ : syracuseStep 5392115 = 8088173) B8088173
theorem B1166015 : Blo 920579 1166015 := bstep (se 1 (by rfl) ⟨874511, by rfl⟩ : syracuseStep 1166015 = 1749023) B1749023
theorem B17746685 : Blo 920579 17746685 := bstep (se 3 (by rfl) ⟨3327503, by rfl⟩ : syracuseStep 17746685 = 6655007) B6655007
theorem B1559911 : Blo 920579 1559911 := bstep (se 1 (by rfl) ⟨1169933, by rfl⟩ : syracuseStep 1559911 = 2339867) B2339867
theorem B7885775 : Blo 920579 7885775 := bstep (se 1 (by rfl) ⟨5914331, by rfl⟩ : syracuseStep 7885775 = 11828663) B11828663
theorem B5264999 : Blo 920579 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B4675805 : Blo 920579 4675805 := bstep (se 3 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 4675805 = 1753427) B1753427
theorem B2218951 : Blo 920579 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B3497195 : Blo 920579 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B4677587 : Blo 920579 4677587 := bstep (se 1 (by rfl) ⟨3508190, by rfl⟩ : syracuseStep 4677587 = 7016381) B7016381
theorem B144040193 : Blo 920579 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B12608297 : Blo 920579 12608297 := bstep (se 2 (by rfl) ⟨4728111, by rfl⟩ : syracuseStep 12608297 = 9456223) B9456223
theorem B3499625 : Blo 920579 3499625 := bstep (se 2 (by rfl) ⟨1312359, by rfl⟩ : syracuseStep 3499625 = 2624719) B2624719
theorem B7306237 : Blo 920579 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B3112235 : Blo 920579 3112235 := bstep (se 1 (by rfl) ⟨2334176, by rfl⟩ : syracuseStep 3112235 = 4668353) B4668353
theorem B6324263 : Blo 920579 6324263 := bstep (se 1 (by rfl) ⟨4743197, by rfl⟩ : syracuseStep 6324263 = 9486395) B9486395
theorem B4489339 : Blo 920579 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B1474919 : Blo 920579 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B2622203 : Blo 920579 2622203 := bstep (se 1 (by rfl) ⟨1966652, by rfl⟩ : syracuseStep 2622203 = 3933305) B3933305
theorem B19203263 : Blo 920579 19203263 := bstep (se 1 (by rfl) ⟨14402447, by rfl⟩ : syracuseStep 19203263 = 28804895) B28804895
theorem B11831123 : Blo 920579 11831123 := bstep (se 1 (by rfl) ⟨8873342, by rfl⟩ : syracuseStep 11831123 = 17746685) B17746685
theorem B5900647 : Blo 920579 5900647 := bstep (se 1 (by rfl) ⟨4425485, by rfl⟩ : syracuseStep 5900647 = 8850971) B8850971
theorem B920831 : Blo 920579 920831 := bstep (se 1 (by rfl) ⟨690623, by rfl⟩ : syracuseStep 920831 = 1381247) B1381247
theorem B2952683 : Blo 920579 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B921215 : Blo 920579 921215 := bstep (se 1 (by rfl) ⟨690911, by rfl⟩ : syracuseStep 921215 = 1381823) B1381823
theorem B921243 : Blo 920579 921243 := bstep (se 1 (by rfl) ⟨690932, by rfl⟩ : syracuseStep 921243 = 1381865) B1381865
theorem B3509999 : Blo 920579 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B3117203 : Blo 920579 3117203 := bstep (se 1 (by rfl) ⟨2337902, by rfl⟩ : syracuseStep 3117203 = 4675805) B4675805
theorem B922079 : Blo 920579 922079 := bstep (se 1 (by rfl) ⟨691559, by rfl⟩ : syracuseStep 922079 = 1383119) B1383119
theorem B922095 : Blo 920579 922095 := bstep (se 1 (by rfl) ⟨691571, by rfl⟩ : syracuseStep 922095 = 1383143) B1383143
theorem B922271 : Blo 920579 922271 := bstep (se 1 (by rfl) ⟨691703, by rfl⟩ : syracuseStep 922271 = 1383407) B1383407
theorem B2331463 : Blo 920579 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B230364107 : Blo 920579 230364107 := bstep (se 1 (by rfl) ⟨172773080, by rfl⟩ : syracuseStep 230364107 = 345546161) B345546161
theorem B922715 : Blo 920579 922715 := bstep (se 1 (by rfl) ⟨692036, by rfl⟩ : syracuseStep 922715 = 1384073) B1384073
theorem B3118391 : Blo 920579 3118391 := bstep (se 1 (by rfl) ⟨2338793, by rfl⟩ : syracuseStep 3118391 = 4677587) B4677587
theorem B1381703 : Blo 920579 1381703 := bstep (se 1 (by rfl) ⟨1036277, by rfl⟩ : syracuseStep 1381703 = 2072555) B2072555
theorem B923183 : Blo 920579 923183 := bstep (se 1 (by rfl) ⟨692387, by rfl⟩ : syracuseStep 923183 = 1384775) B1384775
theorem B1382015 : Blo 920579 1382015 := bstep (se 1 (by rfl) ⟨1036511, by rfl⟩ : syracuseStep 1382015 = 2073023) B2073023
theorem B923903 : Blo 920579 923903 := bstep (se 1 (by rfl) ⟨692927, by rfl⟩ : syracuseStep 923903 = 1385855) B1385855
theorem B1382783 : Blo 920579 1382783 := bstep (se 1 (by rfl) ⟨1037087, by rfl⟩ : syracuseStep 1382783 = 2074175) B2074175
theorem B2333083 : Blo 920579 2333083 := bstep (se 1 (by rfl) ⟨1749812, by rfl⟩ : syracuseStep 2333083 = 3499625) B3499625
theorem B924415 : Blo 920579 924415 := bstep (se 1 (by rfl) ⟨693311, by rfl⟩ : syracuseStep 924415 = 1386623) B1386623
theorem B3939455 : Blo 920579 3939455 := bstep (se 1 (by rfl) ⟨2954591, by rfl⟩ : syracuseStep 3939455 = 5909183) B5909183
theorem B1384859 : Blo 920579 1384859 := bstep (se 1 (by rfl) ⟨1038644, by rfl⟩ : syracuseStep 1384859 = 2077289) B2077289
theorem B2958601 : Blo 920579 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B1385783 : Blo 920579 1385783 := bstep (se 1 (by rfl) ⟨1039337, by rfl⟩ : syracuseStep 1385783 = 2078675) B2078675
theorem B9741649 : Blo 920579 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B3155411 : Blo 920579 3155411 := bstep (se 1 (by rfl) ⟨2366558, by rfl⟩ : syracuseStep 3155411 = 4733117) B4733117
theorem B47982233 : Blo 920579 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B20194991 : Blo 920579 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B1386599 : Blo 920579 1386599 := bstep (se 1 (by rfl) ⟨1039949, by rfl⟩ : syracuseStep 1386599 = 2079899) B2079899
theorem B2074823 : Blo 920579 2074823 := bstep (se 1 (by rfl) ⟨1556117, by rfl⟩ : syracuseStep 2074823 = 3112235) B3112235
theorem B6662969 : Blo 920579 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B2338055 : Blo 920579 2338055 := bstep (se 1 (by rfl) ⟨1753541, by rfl⟩ : syracuseStep 2338055 = 3507083) B3507083
theorem B2076011 : Blo 920579 2076011 := bstep (se 1 (by rfl) ⟨1557008, by rfl⟩ : syracuseStep 2076011 = 3114017) B3114017
theorem B6663545 : Blo 920579 6663545 := bstep (se 2 (by rfl) ⟨2498829, by rfl⟩ : syracuseStep 6663545 = 4997659) B4997659
theorem B2076263 : Blo 920579 2076263 := bstep (se 1 (by rfl) ⟨1557197, by rfl⟩ : syracuseStep 2076263 = 3114395) B3114395
theorem B2076425 : Blo 920579 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B2076713 : Blo 920579 2076713 := bstep (se 2 (by rfl) ⟨778767, by rfl⟩ : syracuseStep 2076713 = 1557535) B1557535
theorem B5257183 : Blo 920579 5257183 := bstep (se 1 (by rfl) ⟨3942887, by rfl⟩ : syracuseStep 5257183 = 7885775) B7885775
theorem B1554619 : Blo 920579 1554619 := bstep (se 1 (by rfl) ⟨1165964, by rfl⟩ : syracuseStep 1554619 = 2331929) B2331929
theorem B2079881 : Blo 920579 2079881 := bstep (se 2 (by rfl) ⟨779955, by rfl⟩ : syracuseStep 2079881 = 1559911) B1559911
theorem B1556023 : Blo 920579 1556023 := bstep (se 1 (by rfl) ⟨1167017, by rfl⟩ : syracuseStep 1556023 = 2334035) B2334035
theorem B17088497 : Blo 920579 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B96026795 : Blo 920579 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B8405531 : Blo 920579 8405531 := bstep (se 1 (by rfl) ⟨6304148, by rfl⟩ : syracuseStep 8405531 = 12608297) B12608297
theorem B7000829 : Blo 920579 7000829 := bstep (se 3 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 7000829 = 2625311) B2625311
theorem B3495707 : Blo 920579 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B3594743 : Blo 920579 3594743 := bstep (se 1 (by rfl) ⟨2696057, by rfl⟩ : syracuseStep 3594743 = 5392115) B5392115
theorem B6642323 : Blo 920579 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B3109373 : Blo 920579 3109373 := bstep (se 3 (by rfl) ⟨583007, by rfl⟩ : syracuseStep 3109373 = 1166015) B1166015
theorem B983279 : Blo 920579 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B5603687 : Blo 920579 5603687 := bstep (se 1 (by rfl) ⟨4202765, by rfl⟩ : syracuseStep 5603687 = 8405531) B8405531
theorem B1968455 : Blo 920579 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B7867529 : Blo 920579 7867529 := bstep (se 2 (by rfl) ⟨2950323, by rfl⟩ : syracuseStep 7867529 = 5900647) B5900647
theorem B921135 : Blo 920579 921135 := bstep (se 1 (by rfl) ⟨690851, by rfl⟩ : syracuseStep 921135 = 1381703) B1381703
theorem B921343 : Blo 920579 921343 := bstep (se 1 (by rfl) ⟨691007, by rfl⟩ : syracuseStep 921343 = 1382015) B1382015
theorem B2330471 : Blo 920579 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B921855 : Blo 920579 921855 := bstep (se 1 (by rfl) ⟨691391, by rfl⟩ : syracuseStep 921855 = 1382783) B1382783
theorem B2396495 : Blo 920579 2396495 := bstep (se 1 (by rfl) ⟨1797371, by rfl⟩ : syracuseStep 2396495 = 3594743) B3594743
theorem B4428215 : Blo 920579 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B2626303 : Blo 920579 2626303 := bstep (se 1 (by rfl) ⟨1969727, by rfl⟩ : syracuseStep 2626303 = 3939455) B3939455
theorem B923239 : Blo 920579 923239 := bstep (se 1 (by rfl) ⟨692429, by rfl⟩ : syracuseStep 923239 = 1384859) B1384859
theorem B923855 : Blo 920579 923855 := bstep (se 1 (by rfl) ⟨692891, by rfl⟩ : syracuseStep 923855 = 1385783) B1385783
theorem B2103607 : Blo 920579 2103607 := bstep (se 1 (by rfl) ⟨1577705, by rfl⟩ : syracuseStep 2103607 = 3155411) B3155411
theorem B924399 : Blo 920579 924399 := bstep (se 1 (by rfl) ⟨693299, by rfl⟩ : syracuseStep 924399 = 1386599) B1386599
theorem B1383215 : Blo 920579 1383215 := bstep (se 1 (by rfl) ⟨1037411, by rfl⟩ : syracuseStep 1383215 = 2074823) B2074823
theorem B1384007 : Blo 920579 1384007 := bstep (se 1 (by rfl) ⟨1038005, by rfl⟩ : syracuseStep 1384007 = 2076011) B2076011
theorem B1384175 : Blo 920579 1384175 := bstep (se 1 (by rfl) ⟨1038131, by rfl⟩ : syracuseStep 1384175 = 2076263) B2076263
theorem B1384283 : Blo 920579 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B1384475 : Blo 920579 1384475 := bstep (se 1 (by rfl) ⟨1038356, by rfl⟩ : syracuseStep 1384475 = 2076713) B2076713
theorem B2072825 : Blo 920579 2072825 := bstep (se 2 (by rfl) ⟨777309, by rfl⟩ : syracuseStep 2072825 = 1554619) B1554619
theorem B2072915 : Blo 920579 2072915 := bstep (se 1 (by rfl) ⟨1554686, by rfl⟩ : syracuseStep 2072915 = 3109373) B3109373
theorem B2074697 : Blo 920579 2074697 := bstep (se 2 (by rfl) ⟨778011, by rfl⟩ : syracuseStep 2074697 = 1556023) B1556023
theorem B1386587 : Blo 920579 1386587 := bstep (se 1 (by rfl) ⟨1039940, by rfl⟩ : syracuseStep 1386587 = 2079881) B2079881
theorem B1748135 : Blo 920579 1748135 := bstep (se 1 (by rfl) ⟨1311101, by rfl⟩ : syracuseStep 1748135 = 2622203) B2622203
theorem B3944801 : Blo 920579 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B12988865 : Blo 920579 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B2339999 : Blo 920579 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B2078135 : Blo 920579 2078135 := bstep (se 1 (by rfl) ⟨1558601, by rfl⟩ : syracuseStep 2078135 = 3117203) B3117203
theorem B4667219 : Blo 920579 4667219 := bstep (se 1 (by rfl) ⟨3500414, by rfl⟩ : syracuseStep 4667219 = 7000829) B7000829
theorem B2078927 : Blo 920579 2078927 := bstep (se 1 (by rfl) ⟨1559195, by rfl⟩ : syracuseStep 2078927 = 3118391) B3118391
theorem B4441979 : Blo 920579 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1558703 : Blo 920579 1558703 := bstep (se 1 (by rfl) ⟨1169027, by rfl⟩ : syracuseStep 1558703 = 2338055) B2338055
theorem B4442363 : Blo 920579 4442363 := bstep (se 1 (by rfl) ⟨3331772, by rfl⟩ : syracuseStep 4442363 = 6663545) B6663545
theorem B11392331 : Blo 920579 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B4216175 : Blo 920579 4216175 := bstep (se 1 (by rfl) ⟨3162131, by rfl⟩ : syracuseStep 4216175 = 6324263) B6324263
theorem B64017863 : Blo 920579 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B5985785 : Blo 920579 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B12802175 : Blo 920579 12802175 := bstep (se 1 (by rfl) ⟨9601631, by rfl⟩ : syracuseStep 12802175 = 19203263) B19203263
theorem B7887415 : Blo 920579 7887415 := bstep (se 1 (by rfl) ⟨5915561, by rfl⟩ : syracuseStep 7887415 = 11831123) B11831123
theorem B153576071 : Blo 920579 153576071 := bstep (se 1 (by rfl) ⟨115182053, by rfl⟩ : syracuseStep 153576071 = 230364107) B230364107
theorem B127952621 : Blo 920579 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B3108617 : Blo 920579 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B13463327 : Blo 920579 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B7009577 : Blo 920579 7009577 := bstep (se 2 (by rfl) ⟨2628591, by rfl⟩ : syracuseStep 7009577 = 5257183) B5257183
theorem B3110777 : Blo 920579 3110777 := bstep (se 2 (by rfl) ⟨1166541, by rfl⟩ : syracuseStep 3110777 = 2333083) B2333083
theorem B3735791 : Blo 920579 3735791 := bstep (se 1 (by rfl) ⟨2801843, by rfl⟩ : syracuseStep 3735791 = 5603687) B5603687
theorem B2622077 : Blo 920579 2622077 := bstep (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) B983279
theorem B10519469 : Blo 920579 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B1312303 : Blo 920579 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B5245019 : Blo 920579 5245019 := bstep (se 1 (by rfl) ⟨3933764, by rfl⟩ : syracuseStep 5245019 = 7867529) B7867529
theorem B2952143 : Blo 920579 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B30379549 : Blo 920579 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B15962093 : Blo 920579 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B922143 : Blo 920579 922143 := bstep (se 1 (by rfl) ⟨691607, by rfl⟩ : syracuseStep 922143 = 1383215) B1383215
theorem B922671 : Blo 920579 922671 := bstep (se 1 (by rfl) ⟨692003, by rfl⟩ : syracuseStep 922671 = 1384007) B1384007
theorem B922783 : Blo 920579 922783 := bstep (se 1 (by rfl) ⟨692087, by rfl⟩ : syracuseStep 922783 = 1384175) B1384175
theorem B922855 : Blo 920579 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B922983 : Blo 920579 922983 := bstep (se 1 (by rfl) ⟨692237, by rfl⟩ : syracuseStep 922983 = 1384475) B1384475
theorem B1381883 : Blo 920579 1381883 := bstep (se 1 (by rfl) ⟨1036412, by rfl⟩ : syracuseStep 1381883 = 2072825) B2072825
theorem B1381943 : Blo 920579 1381943 := bstep (se 1 (by rfl) ⟨1036457, by rfl⟩ : syracuseStep 1381943 = 2072915) B2072915
theorem B85301747 : Blo 920579 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B1383131 : Blo 920579 1383131 := bstep (se 1 (by rfl) ⟨1037348, by rfl⟩ : syracuseStep 1383131 = 2074697) B2074697
theorem B924391 : Blo 920579 924391 := bstep (se 1 (by rfl) ⟨693293, by rfl⟩ : syracuseStep 924391 = 1386587) B1386587
theorem B2072411 : Blo 920579 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B8659243 : Blo 920579 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B1385423 : Blo 920579 1385423 := bstep (se 1 (by rfl) ⟨1039067, by rfl⟩ : syracuseStep 1385423 = 2078135) B2078135
theorem B2073851 : Blo 920579 2073851 := bstep (se 1 (by rfl) ⟨1555388, by rfl⟩ : syracuseStep 2073851 = 3110777) B3110777
theorem B1385951 : Blo 920579 1385951 := bstep (se 1 (by rfl) ⟨1039463, by rfl⟩ : syracuseStep 1385951 = 2078927) B2078927
theorem B2961319 : Blo 920579 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B2961575 : Blo 920579 2961575 := bstep (se 1 (by rfl) ⟨2221181, by rfl⟩ : syracuseStep 2961575 = 4442363) B4442363
theorem B1553647 : Blo 920579 1553647 := bstep (se 1 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 1553647 = 2330471) B2330471
theorem B42678575 : Blo 920579 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B8534783 : Blo 920579 8534783 := bstep (se 1 (by rfl) ⟨6401087, by rfl⟩ : syracuseStep 8534783 = 12802175) B12802175
theorem B102384047 : Blo 920579 102384047 := bstep (se 1 (by rfl) ⟨76788035, by rfl⟩ : syracuseStep 102384047 = 153576071) B153576071
theorem B1165423 : Blo 920579 1165423 := bstep (se 1 (by rfl) ⟨874067, by rfl⟩ : syracuseStep 1165423 = 1748135) B1748135
theorem B2804809 : Blo 920579 2804809 := bstep (se 2 (by rfl) ⟨1051803, by rfl⟩ : syracuseStep 2804809 = 2103607) B2103607
theorem B1559999 : Blo 920579 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B4673051 : Blo 920579 4673051 := bstep (se 1 (by rfl) ⟨3504788, by rfl⟩ : syracuseStep 4673051 = 7009577) B7009577
theorem B1039135 : Blo 920579 1039135 := bstep (se 1 (by rfl) ⟨779351, by rfl⟩ : syracuseStep 1039135 = 1558703) B1558703
theorem B1597663 : Blo 920579 1597663 := bstep (se 1 (by rfl) ⟨1198247, by rfl⟩ : syracuseStep 1597663 = 2396495) B2396495
theorem B2810783 : Blo 920579 2810783 := bstep (se 1 (by rfl) ⟨2108087, by rfl⟩ : syracuseStep 2810783 = 4216175) B4216175
theorem B3501737 : Blo 920579 3501737 := bstep (se 2 (by rfl) ⟨1313151, by rfl⟩ : syracuseStep 3501737 = 2626303) B2626303
theorem B8975551 : Blo 920579 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B10516553 : Blo 920579 10516553 := bstep (se 2 (by rfl) ⟨3943707, by rfl⟩ : syracuseStep 10516553 = 7887415) B7887415
theorem B3111479 : Blo 920579 3111479 := bstep (se 1 (by rfl) ⟨2333609, by rfl⟩ : syracuseStep 3111479 = 4667219) B4667219
theorem B2490527 : Blo 920579 2490527 := bstep (se 1 (by rfl) ⟨1867895, by rfl⟩ : syracuseStep 2490527 = 3735791) B3735791
theorem B68256031 : Blo 920579 68256031 := bstep (se 1 (by rfl) ⟨51192023, by rfl⟩ : syracuseStep 68256031 = 102384047) B102384047
theorem B7012979 : Blo 920579 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B8520869 : Blo 920579 8520869 := bstep (se 4 (by rfl) ⟨798831, by rfl⟩ : syracuseStep 8520869 = 1597663) B1597663
theorem B1968095 : Blo 920579 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B3115367 : Blo 920579 3115367 := bstep (se 1 (by rfl) ⟨2336525, by rfl⟩ : syracuseStep 3115367 = 4673051) B4673051
theorem B921255 : Blo 920579 921255 := bstep (se 1 (by rfl) ⟨690941, by rfl⟩ : syracuseStep 921255 = 1381883) B1381883
theorem B921295 : Blo 920579 921295 := bstep (se 1 (by rfl) ⟨690971, by rfl⟩ : syracuseStep 921295 = 1381943) B1381943
theorem B3739745 : Blo 920579 3739745 := bstep (se 2 (by rfl) ⟨1402404, by rfl⟩ : syracuseStep 3739745 = 2804809) B2804809
theorem B922087 : Blo 920579 922087 := bstep (se 1 (by rfl) ⟨691565, by rfl⟩ : syracuseStep 922087 = 1383131) B1383131
theorem B40506065 : Blo 920579 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B1381607 : Blo 920579 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B1873855 : Blo 920579 1873855 := bstep (se 1 (by rfl) ⟨1405391, by rfl⟩ : syracuseStep 1873855 = 2810783) B2810783
theorem B923615 : Blo 920579 923615 := bstep (se 1 (by rfl) ⟨692711, by rfl⟩ : syracuseStep 923615 = 1385423) B1385423
theorem B1382567 : Blo 920579 1382567 := bstep (se 1 (by rfl) ⟨1036925, by rfl⟩ : syracuseStep 1382567 = 2073851) B2073851
theorem B923967 : Blo 920579 923967 := bstep (se 1 (by rfl) ⟨692975, by rfl⟩ : syracuseStep 923967 = 1385951) B1385951
theorem B11967401 : Blo 920579 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B2071529 : Blo 920579 2071529 := bstep (se 2 (by rfl) ⟨776823, by rfl⟩ : syracuseStep 2071529 = 1553647) B1553647
theorem B2334491 : Blo 920579 2334491 := bstep (se 1 (by rfl) ⟨1750868, by rfl⟩ : syracuseStep 2334491 = 3501737) B3501737
theorem B1974383 : Blo 920579 1974383 := bstep (se 1 (by rfl) ⟨1480787, by rfl⟩ : syracuseStep 1974383 = 2961575) B2961575
theorem B1385513 : Blo 920579 1385513 := bstep (se 2 (by rfl) ⟨519567, by rfl⟩ : syracuseStep 1385513 = 1039135) B1039135
theorem B28452383 : Blo 920579 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B2074319 : Blo 920579 2074319 := bstep (se 1 (by rfl) ⟨1555739, by rfl⟩ : syracuseStep 2074319 = 3111479) B3111479
theorem B1748051 : Blo 920579 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B46182629 : Blo 920579 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B1749737 : Blo 920579 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B1553897 : Blo 920579 1553897 := bstep (se 2 (by rfl) ⟨582711, by rfl⟩ : syracuseStep 1553897 = 1165423) B1165423
theorem B56867831 : Blo 920579 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B3948425 : Blo 920579 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B5689855 : Blo 920579 5689855 := bstep (se 1 (by rfl) ⟨4267391, by rfl⟩ : syracuseStep 5689855 = 8534783) B8534783
theorem B3496679 : Blo 920579 3496679 := bstep (se 1 (by rfl) ⟨2622509, by rfl⟩ : syracuseStep 3496679 = 5245019) B5245019
theorem B1039999 : Blo 920579 1039999 := bstep (se 1 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 1039999 = 1559999) B1559999
theorem B10641395 : Blo 920579 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B7011035 : Blo 920579 7011035 := bstep (se 1 (by rfl) ⟨5258276, by rfl⟩ : syracuseStep 7011035 = 10516553) B10516553
theorem B2493163 : Blo 920579 2493163 := bstep (se 1 (by rfl) ⟨1869872, by rfl⟩ : syracuseStep 2493163 = 3739745) B3739745
theorem B27004043 : Blo 920579 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B921071 : Blo 920579 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B921711 : Blo 920579 921711 := bstep (se 1 (by rfl) ⟨691283, by rfl⟩ : syracuseStep 921711 = 1382567) B1382567
theorem B2331119 : Blo 920579 2331119 := bstep (se 1 (by rfl) ⟨1748339, by rfl⟩ : syracuseStep 2331119 = 3496679) B3496679
theorem B1381019 : Blo 920579 1381019 := bstep (se 1 (by rfl) ⟨1035764, by rfl⟩ : syracuseStep 1381019 = 2071529) B2071529
theorem B5248253 : Blo 920579 5248253 := bstep (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) B1968095
theorem B1316255 : Blo 920579 1316255 := bstep (se 1 (by rfl) ⟨987191, by rfl⟩ : syracuseStep 1316255 = 1974383) B1974383
theorem B923675 : Blo 920579 923675 := bstep (se 1 (by rfl) ⟨692756, by rfl⟩ : syracuseStep 923675 = 1385513) B1385513
theorem B1382879 : Blo 920579 1382879 := bstep (se 1 (by rfl) ⟨1037159, by rfl⟩ : syracuseStep 1382879 = 2074319) B2074319
theorem B2498473 : Blo 920579 2498473 := bstep (se 2 (by rfl) ⟨936927, by rfl⟩ : syracuseStep 2498473 = 1873855) B1873855
theorem B1386665 : Blo 920579 1386665 := bstep (se 2 (by rfl) ⟨519999, by rfl⟩ : syracuseStep 1386665 = 1039999) B1039999
theorem B2632283 : Blo 920579 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B91008041 : Blo 920579 91008041 := bstep (se 2 (by rfl) ⟨34128015, by rfl⟩ : syracuseStep 91008041 = 68256031) B68256031
theorem B5680579 : Blo 920579 5680579 := bstep (se 1 (by rfl) ⟨4260434, by rfl⟩ : syracuseStep 5680579 = 8520869) B8520869
theorem B2076911 : Blo 920579 2076911 := bstep (se 1 (by rfl) ⟨1557683, by rfl⟩ : syracuseStep 2076911 = 3115367) B3115367
theorem B7978267 : Blo 920579 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B1556327 : Blo 920579 1556327 := bstep (se 1 (by rfl) ⟨1167245, by rfl⟩ : syracuseStep 1556327 = 2334491) B2334491
theorem B7094263 : Blo 920579 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B7586473 : Blo 920579 7586473 := bstep (se 2 (by rfl) ⟨2844927, by rfl⟩ : syracuseStep 7586473 = 5689855) B5689855
theorem B1165367 : Blo 920579 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B30788419 : Blo 920579 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B1166491 : Blo 920579 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B1035931 : Blo 920579 1035931 := bstep (se 1 (by rfl) ⟨776948, by rfl⟩ : syracuseStep 1035931 = 1553897) B1553897
theorem B4674023 : Blo 920579 4674023 := bstep (se 1 (by rfl) ⟨3505517, by rfl⟩ : syracuseStep 4674023 = 7011035) B7011035
theorem B1660351 : Blo 920579 1660351 := bstep (se 1 (by rfl) ⟨1245263, by rfl⟩ : syracuseStep 1660351 = 2490527) B2490527
theorem B4675319 : Blo 920579 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B18968255 : Blo 920579 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B37911887 : Blo 920579 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B3116015 : Blo 920579 3116015 := bstep (se 1 (by rfl) ⟨2337011, by rfl⟩ : syracuseStep 3116015 = 4674023) B4674023
theorem B920679 : Blo 920579 920679 := bstep (se 1 (by rfl) ⟨690509, by rfl⟩ : syracuseStep 920679 = 1381019) B1381019
theorem B3510013 : Blo 920579 3510013 := bstep (se 3 (by rfl) ⟨658127, by rfl⟩ : syracuseStep 3510013 = 1316255) B1316255
theorem B3116879 : Blo 920579 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B921919 : Blo 920579 921919 := bstep (se 1 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 921919 = 1382879) B1382879
theorem B7574105 : Blo 920579 7574105 := bstep (se 2 (by rfl) ⟨2840289, by rfl⟩ : syracuseStep 7574105 = 5680579) B5680579
theorem B1381241 : Blo 920579 1381241 := bstep (se 2 (by rfl) ⟨517965, by rfl⟩ : syracuseStep 1381241 = 1035931) B1035931
theorem B924443 : Blo 920579 924443 := bstep (se 1 (by rfl) ⟨693332, by rfl⟩ : syracuseStep 924443 = 1386665) B1386665
theorem B242688109 : Blo 920579 242688109 := bstep (se 3 (by rfl) ⟨45504020, by rfl⟩ : syracuseStep 242688109 = 91008041) B91008041
theorem B1384607 : Blo 920579 1384607 := bstep (se 1 (by rfl) ⟨1038455, by rfl⟩ : syracuseStep 1384607 = 2076911) B2076911
theorem B25274591 : Blo 920579 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B1554079 : Blo 920579 1554079 := bstep (se 1 (by rfl) ⟨1165559, by rfl⟩ : syracuseStep 1554079 = 2331119) B2331119
theorem B1555321 : Blo 920579 1555321 := bstep (se 2 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 1555321 = 1166491) B1166491
theorem B1754855 : Blo 920579 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B2213801 : Blo 920579 2213801 := bstep (se 2 (by rfl) ⟨830175, by rfl⟩ : syracuseStep 2213801 = 1660351) B1660351
theorem B72010781 : Blo 920579 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B10637689 : Blo 920579 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B3331297 : Blo 920579 3331297 := bstep (se 2 (by rfl) ⟨1249236, by rfl⟩ : syracuseStep 3331297 = 2498473) B2498473
theorem B1037551 : Blo 920579 1037551 := bstep (se 1 (by rfl) ⟨778163, by rfl⟩ : syracuseStep 1037551 = 1556327) B1556327
theorem B9459017 : Blo 920579 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B10115297 : Blo 920579 10115297 := bstep (se 2 (by rfl) ⟨3793236, by rfl⟩ : syracuseStep 10115297 = 7586473) B7586473
theorem B3498835 : Blo 920579 3498835 := bstep (se 1 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 3498835 = 5248253) B5248253
theorem B41051225 : Blo 920579 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B13296869 : Blo 920579 13296869 := bstep (se 4 (by rfl) ⟨1246581, by rfl⟩ : syracuseStep 13296869 = 2493163) B2493163
theorem B3107645 : Blo 920579 3107645 := bstep (se 3 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 3107645 = 1165367) B1165367
theorem B12645503 : Blo 920579 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B323584145 : Blo 920579 323584145 := bstep (se 2 (by rfl) ⟨121344054, by rfl⟩ : syracuseStep 323584145 = 242688109) B242688109
theorem B1475867 : Blo 920579 1475867 := bstep (se 1 (by rfl) ⟨1106900, by rfl⟩ : syracuseStep 1475867 = 2213801) B2213801
theorem B48007187 : Blo 920579 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B920827 : Blo 920579 920827 := bstep (se 1 (by rfl) ⟨690620, by rfl⟩ : syracuseStep 920827 = 1381241) B1381241
theorem B923071 : Blo 920579 923071 := bstep (se 1 (by rfl) ⟨692303, by rfl⟩ : syracuseStep 923071 = 1384607) B1384607
theorem B27367483 : Blo 920579 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B16849727 : Blo 920579 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B1383401 : Blo 920579 1383401 := bstep (se 2 (by rfl) ⟨518775, by rfl⟩ : syracuseStep 1383401 = 1037551) B1037551
theorem B2071763 : Blo 920579 2071763 := bstep (se 1 (by rfl) ⟨1553822, by rfl⟩ : syracuseStep 2071763 = 3107645) B3107645
theorem B2072105 : Blo 920579 2072105 := bstep (se 2 (by rfl) ⟨777039, by rfl⟩ : syracuseStep 2072105 = 1554079) B1554079
theorem B8430335 : Blo 920579 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B2073761 : Blo 920579 2073761 := bstep (se 2 (by rfl) ⟨777660, by rfl⟩ : syracuseStep 2073761 = 1555321) B1555321
theorem B4665113 : Blo 920579 4665113 := bstep (se 2 (by rfl) ⟨1749417, by rfl⟩ : syracuseStep 4665113 = 3498835) B3498835
theorem B20197613 : Blo 920579 20197613 := bstep (se 3 (by rfl) ⟨3787052, by rfl⟩ : syracuseStep 20197613 = 7574105) B7574105
theorem B2077343 : Blo 920579 2077343 := bstep (se 1 (by rfl) ⟨1558007, by rfl⟩ : syracuseStep 2077343 = 3116015) B3116015
theorem B2077919 : Blo 920579 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B6306011 : Blo 920579 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B8864579 : Blo 920579 8864579 := bstep (se 1 (by rfl) ⟨6648434, by rfl⟩ : syracuseStep 8864579 = 13296869) B13296869
theorem B4441729 : Blo 920579 4441729 := bstep (se 2 (by rfl) ⟨1665648, by rfl⟩ : syracuseStep 4441729 = 3331297) B3331297
theorem B1169903 : Blo 920579 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B6743531 : Blo 920579 6743531 := bstep (se 1 (by rfl) ⟨5057648, by rfl⟩ : syracuseStep 6743531 = 10115297) B10115297
theorem B4680017 : Blo 920579 4680017 := bstep (se 2 (by rfl) ⟨1755006, by rfl⟩ : syracuseStep 4680017 = 3510013) B3510013
theorem B14183585 : Blo 920579 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B983911 : Blo 920579 983911 := bstep (se 1 (by rfl) ⟨737933, by rfl⟩ : syracuseStep 983911 = 1475867) B1475867
theorem B922267 : Blo 920579 922267 := bstep (se 1 (by rfl) ⟨691700, by rfl⟩ : syracuseStep 922267 = 1383401) B1383401
theorem B1381175 : Blo 920579 1381175 := bstep (se 1 (by rfl) ⟨1035881, by rfl⟩ : syracuseStep 1381175 = 2071763) B2071763
theorem B1381403 : Blo 920579 1381403 := bstep (se 1 (by rfl) ⟨1036052, by rfl⟩ : syracuseStep 1381403 = 2072105) B2072105
theorem B1382507 : Blo 920579 1382507 := bstep (se 1 (by rfl) ⟨1036880, by rfl⟩ : syracuseStep 1382507 = 2073761) B2073761
theorem B3119741 : Blo 920579 3119741 := bstep (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) B1169903
theorem B3120011 : Blo 920579 3120011 := bstep (se 1 (by rfl) ⟨2340008, by rfl⟩ : syracuseStep 3120011 = 4680017) B4680017
theorem B1384895 : Blo 920579 1384895 := bstep (se 1 (by rfl) ⟨1038671, by rfl⟩ : syracuseStep 1384895 = 2077343) B2077343
theorem B1385279 : Blo 920579 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B4204007 : Blo 920579 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B215722763 : Blo 920579 215722763 := bstep (se 1 (by rfl) ⟨161792072, by rfl⟩ : syracuseStep 215722763 = 323584145) B323584145
theorem B5909719 : Blo 920579 5909719 := bstep (se 1 (by rfl) ⟨4432289, by rfl⟩ : syracuseStep 5909719 = 8864579) B8864579
theorem B5620223 : Blo 920579 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B9455723 : Blo 920579 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B36489977 : Blo 920579 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B32004791 : Blo 920579 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B5922305 : Blo 920579 5922305 := bstep (se 2 (by rfl) ⟨2220864, by rfl⟩ : syracuseStep 5922305 = 4441729) B4441729
theorem B17982749 : Blo 920579 17982749 := bstep (se 3 (by rfl) ⟨3371765, by rfl⟩ : syracuseStep 17982749 = 6743531) B6743531
theorem B11233151 : Blo 920579 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B3110075 : Blo 920579 3110075 := bstep (se 1 (by rfl) ⟨2332556, by rfl⟩ : syracuseStep 3110075 = 4665113) B4665113
theorem B13465075 : Blo 920579 13465075 := bstep (se 1 (by rfl) ⟨10098806, by rfl⟩ : syracuseStep 13465075 = 20197613) B20197613
theorem B1311881 : Blo 920579 1311881 := bstep (se 2 (by rfl) ⟨491955, by rfl⟩ : syracuseStep 1311881 = 983911) B983911
theorem B920783 : Blo 920579 920783 := bstep (se 1 (by rfl) ⟨690587, by rfl⟩ : syracuseStep 920783 = 1381175) B1381175
theorem B920935 : Blo 920579 920935 := bstep (se 1 (by rfl) ⟨690701, by rfl⟩ : syracuseStep 920935 = 1381403) B1381403
theorem B921671 : Blo 920579 921671 := bstep (se 1 (by rfl) ⟨691253, by rfl⟩ : syracuseStep 921671 = 1382507) B1382507
theorem B21336527 : Blo 920579 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B923263 : Blo 920579 923263 := bstep (se 1 (by rfl) ⟨692447, by rfl⟩ : syracuseStep 923263 = 1384895) B1384895
theorem B923519 : Blo 920579 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B2073383 : Blo 920579 2073383 := bstep (se 1 (by rfl) ⟨1555037, by rfl⟩ : syracuseStep 2073383 = 3110075) B3110075
theorem B14987261 : Blo 920579 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B6303815 : Blo 920579 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B24326651 : Blo 920579 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B7879625 : Blo 920579 7879625 := bstep (se 2 (by rfl) ⟨2954859, by rfl⟩ : syracuseStep 7879625 = 5909719) B5909719
theorem B2079827 : Blo 920579 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B2080007 : Blo 920579 2080007 := bstep (se 1 (by rfl) ⟨1560005, by rfl⟩ : syracuseStep 2080007 = 3120011) B3120011
theorem B3948203 : Blo 920579 3948203 := bstep (se 1 (by rfl) ⟨2961152, by rfl⟩ : syracuseStep 3948203 = 5922305) B5922305
theorem B2802671 : Blo 920579 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B7488767 : Blo 920579 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B11988499 : Blo 920579 11988499 := bstep (se 1 (by rfl) ⟨8991374, by rfl⟩ : syracuseStep 11988499 = 17982749) B17982749
theorem B143815175 : Blo 920579 143815175 := bstep (se 1 (by rfl) ⟨107861381, by rfl⟩ : syracuseStep 143815175 = 215722763) B215722763
theorem B17953433 : Blo 920579 17953433 := bstep (se 2 (by rfl) ⟨6732537, by rfl⟩ : syracuseStep 17953433 = 13465075) B13465075
theorem B1868447 : Blo 920579 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B14224351 : Blo 920579 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B1382255 : Blo 920579 1382255 := bstep (se 1 (by rfl) ⟨1036691, by rfl⟩ : syracuseStep 1382255 = 2073383) B2073383
theorem B4202543 : Blo 920579 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B11968955 : Blo 920579 11968955 := bstep (se 1 (by rfl) ⟨8976716, by rfl⟩ : syracuseStep 11968955 = 17953433) B17953433
theorem B5253083 : Blo 920579 5253083 := bstep (se 1 (by rfl) ⟨3939812, by rfl⟩ : syracuseStep 5253083 = 7879625) B7879625
theorem B1386551 : Blo 920579 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B1386671 : Blo 920579 1386671 := bstep (se 1 (by rfl) ⟨1040003, by rfl⟩ : syracuseStep 1386671 = 2080007) B2080007
theorem B2632135 : Blo 920579 2632135 := bstep (se 1 (by rfl) ⟨1974101, by rfl⟩ : syracuseStep 2632135 = 3948203) B3948203
theorem B4992511 : Blo 920579 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B3498349 : Blo 920579 3498349 := bstep (se 3 (by rfl) ⟨655940, by rfl⟩ : syracuseStep 3498349 = 1311881) B1311881
theorem B15984665 : Blo 920579 15984665 := bstep (se 2 (by rfl) ⟨5994249, by rfl⟩ : syracuseStep 15984665 = 11988499) B11988499
theorem B9991507 : Blo 920579 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B16217767 : Blo 920579 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B95876783 : Blo 920579 95876783 := bstep (se 1 (by rfl) ⟨71907587, by rfl⟩ : syracuseStep 95876783 = 143815175) B143815175
theorem B11206781 : Blo 920579 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B1245631 : Blo 920579 1245631 := bstep (se 1 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 1245631 = 1868447) B1868447
theorem B3509513 : Blo 920579 3509513 := bstep (se 2 (by rfl) ⟨1316067, by rfl⟩ : syracuseStep 3509513 = 2632135) B2632135
theorem B921503 : Blo 920579 921503 := bstep (se 1 (by rfl) ⟨691127, by rfl⟩ : syracuseStep 921503 = 1382255) B1382255
theorem B6656681 : Blo 920579 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B10656443 : Blo 920579 10656443 := bstep (se 1 (by rfl) ⟨7992332, by rfl⟩ : syracuseStep 10656443 = 15984665) B15984665
theorem B924367 : Blo 920579 924367 := bstep (se 1 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 924367 = 1386551) B1386551
theorem B924447 : Blo 920579 924447 := bstep (se 1 (by rfl) ⟨693335, by rfl⟩ : syracuseStep 924447 = 1386671) B1386671
theorem B4664465 : Blo 920579 4664465 := bstep (se 2 (by rfl) ⟨1749174, by rfl⟩ : syracuseStep 4664465 = 3498349) B3498349
theorem B7979303 : Blo 920579 7979303 := bstep (se 1 (by rfl) ⟨5984477, by rfl⟩ : syracuseStep 7979303 = 11968955) B11968955
theorem B13322009 : Blo 920579 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B63917855 : Blo 920579 63917855 := bstep (se 1 (by rfl) ⟨47938391, by rfl⟩ : syracuseStep 63917855 = 95876783) B95876783
theorem B18965801 : Blo 920579 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B3502055 : Blo 920579 3502055 := bstep (se 1 (by rfl) ⟨2626541, by rfl⟩ : syracuseStep 3502055 = 5253083) B5253083
theorem B21623689 : Blo 920579 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B7471187 : Blo 920579 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B8881339 : Blo 920579 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B2334703 : Blo 920579 2334703 := bstep (se 1 (by rfl) ⟨1751027, by rfl⟩ : syracuseStep 2334703 = 3502055) B3502055
theorem B21278141 : Blo 920579 21278141 := bstep (se 3 (by rfl) ⟨3989651, by rfl⟩ : syracuseStep 21278141 = 7979303) B7979303
theorem B2339675 : Blo 920579 2339675 := bstep (se 1 (by rfl) ⟨1754756, by rfl⟩ : syracuseStep 2339675 = 3509513) B3509513
theorem B42611903 : Blo 920579 42611903 := bstep (se 1 (by rfl) ⟨31958927, by rfl⟩ : syracuseStep 42611903 = 63917855) B63917855
theorem B115326341 : Blo 920579 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B1660841 : Blo 920579 1660841 := bstep (se 2 (by rfl) ⟨622815, by rfl⟩ : syracuseStep 1660841 = 1245631) B1245631
theorem B17751149 : Blo 920579 17751149 := bstep (se 3 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 17751149 = 6656681) B6656681
theorem B7104295 : Blo 920579 7104295 := bstep (se 1 (by rfl) ⟨5328221, by rfl⟩ : syracuseStep 7104295 = 10656443) B10656443
theorem B12643867 : Blo 920579 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B3109643 : Blo 920579 3109643 := bstep (se 1 (by rfl) ⟨2332232, by rfl⟩ : syracuseStep 3109643 = 4664465) B4664465
theorem B4980791 : Blo 920579 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B9472393 : Blo 920579 9472393 := bstep (se 2 (by rfl) ⟨3552147, by rfl⟩ : syracuseStep 9472393 = 7104295) B7104295
theorem B11834099 : Blo 920579 11834099 := bstep (se 1 (by rfl) ⟨8875574, by rfl⟩ : syracuseStep 11834099 = 17751149) B17751149
theorem B2073095 : Blo 920579 2073095 := bstep (se 1 (by rfl) ⟨1554821, by rfl⟩ : syracuseStep 2073095 = 3109643) B3109643
theorem B76884227 : Blo 920579 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B11841785 : Blo 920579 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B1559783 : Blo 920579 1559783 := bstep (se 1 (by rfl) ⟨1169837, by rfl⟩ : syracuseStep 1559783 = 2339675) B2339675
theorem B1107227 : Blo 920579 1107227 := bstep (se 1 (by rfl) ⟨830420, by rfl⟩ : syracuseStep 1107227 = 1660841) B1660841
theorem B14185427 : Blo 920579 14185427 := bstep (se 1 (by rfl) ⟨10639070, by rfl⟩ : syracuseStep 14185427 = 21278141) B21278141
theorem B67433957 : Blo 920579 67433957 := bstep (se 4 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 67433957 = 12643867) B12643867
theorem B28407935 : Blo 920579 28407935 := bstep (se 1 (by rfl) ⟨21305951, by rfl⟩ : syracuseStep 28407935 = 42611903) B42611903
theorem B3112937 : Blo 920579 3112937 := bstep (se 2 (by rfl) ⟨1167351, by rfl⟩ : syracuseStep 3112937 = 2334703) B2334703
theorem B2952605 : Blo 920579 2952605 := bstep (se 3 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 2952605 = 1107227) B1107227
theorem B1382063 : Blo 920579 1382063 := bstep (se 1 (by rfl) ⟨1036547, by rfl⟩ : syracuseStep 1382063 = 2073095) B2073095
theorem B51256151 : Blo 920579 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B2075291 : Blo 920579 2075291 := bstep (se 1 (by rfl) ⟨1556468, by rfl⟩ : syracuseStep 2075291 = 3112937) B3112937
theorem B3320527 : Blo 920579 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B37827805 : Blo 920579 37827805 := bstep (se 3 (by rfl) ⟨7092713, by rfl⟩ : syracuseStep 37827805 = 14185427) B14185427
theorem B12629857 : Blo 920579 12629857 := bstep (se 2 (by rfl) ⟨4736196, by rfl⟩ : syracuseStep 12629857 = 9472393) B9472393
theorem B1039855 : Blo 920579 1039855 := bstep (se 1 (by rfl) ⟨779891, by rfl⟩ : syracuseStep 1039855 = 1559783) B1559783
theorem B7889399 : Blo 920579 7889399 := bstep (se 1 (by rfl) ⟨5917049, by rfl⟩ : syracuseStep 7889399 = 11834099) B11834099
theorem B7894523 : Blo 920579 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B44955971 : Blo 920579 44955971 := bstep (se 1 (by rfl) ⟨33716978, by rfl⟩ : syracuseStep 44955971 = 67433957) B67433957
theorem B18938623 : Blo 920579 18938623 := bstep (se 1 (by rfl) ⟨14203967, by rfl⟩ : syracuseStep 18938623 = 28407935) B28407935
theorem B1968403 : Blo 920579 1968403 := bstep (se 1 (by rfl) ⟨1476302, by rfl⟩ : syracuseStep 1968403 = 2952605) B2952605
theorem B4427369 : Blo 920579 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B921375 : Blo 920579 921375 := bstep (se 1 (by rfl) ⟨691031, by rfl⟩ : syracuseStep 921375 = 1382063) B1382063
theorem B50437073 : Blo 920579 50437073 := bstep (se 2 (by rfl) ⟨18913902, by rfl⟩ : syracuseStep 50437073 = 37827805) B37827805
theorem B1383527 : Blo 920579 1383527 := bstep (se 1 (by rfl) ⟨1037645, by rfl⟩ : syracuseStep 1383527 = 2075291) B2075291
theorem B1386473 : Blo 920579 1386473 := bstep (se 2 (by rfl) ⟨519927, by rfl⟩ : syracuseStep 1386473 = 1039855) B1039855
theorem B5259599 : Blo 920579 5259599 := bstep (se 1 (by rfl) ⟨3944699, by rfl⟩ : syracuseStep 5259599 = 7889399) B7889399
theorem B5263015 : Blo 920579 5263015 := bstep (se 1 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 5263015 = 7894523) B7894523
theorem B25251497 : Blo 920579 25251497 := bstep (se 2 (by rfl) ⟨9469311, by rfl⟩ : syracuseStep 25251497 = 18938623) B18938623
theorem B29970647 : Blo 920579 29970647 := bstep (se 1 (by rfl) ⟨22477985, by rfl⟩ : syracuseStep 29970647 = 44955971) B44955971
theorem B34170767 : Blo 920579 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B16839809 : Blo 920579 16839809 := bstep (se 2 (by rfl) ⟨6314928, by rfl⟩ : syracuseStep 16839809 = 12629857) B12629857
theorem B3506399 : Blo 920579 3506399 := bstep (se 1 (by rfl) ⟨2629799, by rfl⟩ : syracuseStep 3506399 = 5259599) B5259599
theorem B2951579 : Blo 920579 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B2624537 : Blo 920579 2624537 := bstep (se 2 (by rfl) ⟨984201, by rfl⟩ : syracuseStep 2624537 = 1968403) B1968403
theorem B33624715 : Blo 920579 33624715 := bstep (se 1 (by rfl) ⟨25218536, by rfl⟩ : syracuseStep 33624715 = 50437073) B50437073
theorem B922351 : Blo 920579 922351 := bstep (se 1 (by rfl) ⟨691763, by rfl⟩ : syracuseStep 922351 = 1383527) B1383527
theorem B7017353 : Blo 920579 7017353 := bstep (se 2 (by rfl) ⟨2631507, by rfl⟩ : syracuseStep 7017353 = 5263015) B5263015
theorem B22780511 : Blo 920579 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B924315 : Blo 920579 924315 := bstep (se 1 (by rfl) ⟨693236, by rfl⟩ : syracuseStep 924315 = 1386473) B1386473
theorem B11226539 : Blo 920579 11226539 := bstep (se 1 (by rfl) ⟨8419904, by rfl⟩ : syracuseStep 11226539 = 16839809) B16839809
theorem B16834331 : Blo 920579 16834331 := bstep (se 1 (by rfl) ⟨12625748, by rfl⟩ : syracuseStep 16834331 = 25251497) B25251497
theorem B19980431 : Blo 920579 19980431 := bstep (se 1 (by rfl) ⟨14985323, by rfl⟩ : syracuseStep 19980431 = 29970647) B29970647
theorem B44832953 : Blo 920579 44832953 := bstep (se 2 (by rfl) ⟨16812357, by rfl⟩ : syracuseStep 44832953 = 33624715) B33624715
theorem B7870877 : Blo 920579 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B2337599 : Blo 920579 2337599 := bstep (se 1 (by rfl) ⟨1753199, by rfl⟩ : syracuseStep 2337599 = 3506399) B3506399
theorem B1749691 : Blo 920579 1749691 := bstep (se 1 (by rfl) ⟨1312268, by rfl⟩ : syracuseStep 1749691 = 2624537) B2624537
theorem B7484359 : Blo 920579 7484359 := bstep (se 1 (by rfl) ⟨5613269, by rfl⟩ : syracuseStep 7484359 = 11226539) B11226539
theorem B15187007 : Blo 920579 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B11222887 : Blo 920579 11222887 := bstep (se 1 (by rfl) ⟨8417165, by rfl⟩ : syracuseStep 11222887 = 16834331) B16834331
theorem B13320287 : Blo 920579 13320287 := bstep (se 1 (by rfl) ⟨9990215, by rfl⟩ : syracuseStep 13320287 = 19980431) B19980431
theorem B4678235 : Blo 920579 4678235 := bstep (se 1 (by rfl) ⟨3508676, by rfl⟩ : syracuseStep 4678235 = 7017353) B7017353
theorem B8880191 : Blo 920579 8880191 := bstep (se 1 (by rfl) ⟨6660143, by rfl⟩ : syracuseStep 8880191 = 13320287) B13320287
theorem B29888635 : Blo 920579 29888635 := bstep (se 1 (by rfl) ⟨22416476, by rfl⟩ : syracuseStep 29888635 = 44832953) B44832953
theorem B5247251 : Blo 920579 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B3118823 : Blo 920579 3118823 := bstep (se 1 (by rfl) ⟨2339117, by rfl⟩ : syracuseStep 3118823 = 4678235) B4678235
theorem B2332921 : Blo 920579 2332921 := bstep (se 2 (by rfl) ⟨874845, by rfl⟩ : syracuseStep 2332921 = 1749691) B1749691
theorem B9979145 : Blo 920579 9979145 := bstep (se 2 (by rfl) ⟨3742179, by rfl⟩ : syracuseStep 9979145 = 7484359) B7484359
theorem B1558399 : Blo 920579 1558399 := bstep (se 1 (by rfl) ⟨1168799, by rfl⟩ : syracuseStep 1558399 = 2337599) B2337599
theorem B14963849 : Blo 920579 14963849 := bstep (se 2 (by rfl) ⟨5611443, by rfl⟩ : syracuseStep 14963849 = 11222887) B11222887
theorem B10124671 : Blo 920579 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B6652763 : Blo 920579 6652763 := bstep (se 1 (by rfl) ⟨4989572, by rfl⟩ : syracuseStep 6652763 = 9979145) B9979145
theorem B39851513 : Blo 920579 39851513 := bstep (se 2 (by rfl) ⟨14944317, by rfl⟩ : syracuseStep 39851513 = 29888635) B29888635
theorem B2077865 : Blo 920579 2077865 := bstep (se 2 (by rfl) ⟨779199, by rfl⟩ : syracuseStep 2077865 = 1558399) B1558399
theorem B9975899 : Blo 920579 9975899 := bstep (se 1 (by rfl) ⟨7481924, by rfl⟩ : syracuseStep 9975899 = 14963849) B14963849
theorem B2079215 : Blo 920579 2079215 := bstep (se 1 (by rfl) ⟨1559411, by rfl⟩ : syracuseStep 2079215 = 3118823) B3118823
theorem B5920127 : Blo 920579 5920127 := bstep (se 1 (by rfl) ⟨4440095, by rfl⟩ : syracuseStep 5920127 = 8880191) B8880191
theorem B3498167 : Blo 920579 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B3110561 : Blo 920579 3110561 := bstep (se 2 (by rfl) ⟨1166460, by rfl⟩ : syracuseStep 3110561 = 2332921) B2332921
theorem B13499561 : Blo 920579 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B2332111 : Blo 920579 2332111 := bstep (se 1 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 2332111 = 3498167) B3498167
theorem B1385243 : Blo 920579 1385243 := bstep (se 1 (by rfl) ⟨1038932, by rfl⟩ : syracuseStep 1385243 = 2077865) B2077865
theorem B2073707 : Blo 920579 2073707 := bstep (se 1 (by rfl) ⟨1555280, by rfl⟩ : syracuseStep 2073707 = 3110561) B3110561
theorem B1386143 : Blo 920579 1386143 := bstep (se 1 (by rfl) ⟨1039607, by rfl⟩ : syracuseStep 1386143 = 2079215) B2079215
theorem B4435175 : Blo 920579 4435175 := bstep (se 1 (by rfl) ⟨3326381, by rfl⟩ : syracuseStep 4435175 = 6652763) B6652763
theorem B3946751 : Blo 920579 3946751 := bstep (se 1 (by rfl) ⟨2960063, by rfl⟩ : syracuseStep 3946751 = 5920127) B5920127
theorem B8999707 : Blo 920579 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B26567675 : Blo 920579 26567675 := bstep (se 1 (by rfl) ⟨19925756, by rfl⟩ : syracuseStep 26567675 = 39851513) B39851513
theorem B6650599 : Blo 920579 6650599 := bstep (se 1 (by rfl) ⟨4987949, by rfl⟩ : syracuseStep 6650599 = 9975899) B9975899
theorem B923495 : Blo 920579 923495 := bstep (se 1 (by rfl) ⟨692621, by rfl⟩ : syracuseStep 923495 = 1385243) B1385243
theorem B1382471 : Blo 920579 1382471 := bstep (se 1 (by rfl) ⟨1036853, by rfl⟩ : syracuseStep 1382471 = 2073707) B2073707
theorem B11999609 : Blo 920579 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B924095 : Blo 920579 924095 := bstep (se 1 (by rfl) ⟨693071, by rfl⟩ : syracuseStep 924095 = 1386143) B1386143
theorem B2956783 : Blo 920579 2956783 := bstep (se 1 (by rfl) ⟨2217587, by rfl⟩ : syracuseStep 2956783 = 4435175) B4435175
theorem B2631167 : Blo 920579 2631167 := bstep (se 1 (by rfl) ⟨1973375, by rfl⟩ : syracuseStep 2631167 = 3946751) B3946751
theorem B17711783 : Blo 920579 17711783 := bstep (se 1 (by rfl) ⟨13283837, by rfl⟩ : syracuseStep 17711783 = 26567675) B26567675
theorem B8867465 : Blo 920579 8867465 := bstep (se 2 (by rfl) ⟨3325299, by rfl⟩ : syracuseStep 8867465 = 6650599) B6650599
theorem B3109481 : Blo 920579 3109481 := bstep (se 2 (by rfl) ⟨1166055, by rfl⟩ : syracuseStep 3109481 = 2332111) B2332111
theorem B921647 : Blo 920579 921647 := bstep (se 1 (by rfl) ⟨691235, by rfl⟩ : syracuseStep 921647 = 1382471) B1382471
theorem B7999739 : Blo 920579 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B2072987 : Blo 920579 2072987 := bstep (se 1 (by rfl) ⟨1554740, by rfl⟩ : syracuseStep 2072987 = 3109481) B3109481
theorem B3942377 : Blo 920579 3942377 := bstep (se 2 (by rfl) ⟨1478391, by rfl⟩ : syracuseStep 3942377 = 2956783) B2956783
theorem B11807855 : Blo 920579 11807855 := bstep (se 1 (by rfl) ⟨8855891, by rfl⟩ : syracuseStep 11807855 = 17711783) B17711783
theorem B5911643 : Blo 920579 5911643 := bstep (se 1 (by rfl) ⟨4433732, by rfl⟩ : syracuseStep 5911643 = 8867465) B8867465
theorem B1754111 : Blo 920579 1754111 := bstep (se 1 (by rfl) ⟨1315583, by rfl⟩ : syracuseStep 1754111 = 2631167) B2631167
theorem B1381991 : Blo 920579 1381991 := bstep (se 1 (by rfl) ⟨1036493, by rfl⟩ : syracuseStep 1381991 = 2072987) B2072987
theorem B2628251 : Blo 920579 2628251 := bstep (se 1 (by rfl) ⟨1971188, by rfl⟩ : syracuseStep 2628251 = 3942377) B3942377
theorem B7871903 : Blo 920579 7871903 := bstep (se 1 (by rfl) ⟨5903927, by rfl⟩ : syracuseStep 7871903 = 11807855) B11807855
theorem B3941095 : Blo 920579 3941095 := bstep (se 1 (by rfl) ⟨2955821, by rfl⟩ : syracuseStep 3941095 = 5911643) B5911643
theorem B1169407 : Blo 920579 1169407 := bstep (se 1 (by rfl) ⟨877055, by rfl⟩ : syracuseStep 1169407 = 1754111) B1754111
theorem B5333159 : Blo 920579 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B14221757 : Blo 920579 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B921327 : Blo 920579 921327 := bstep (se 1 (by rfl) ⟨690995, by rfl⟩ : syracuseStep 921327 = 1381991) B1381991
theorem B5247935 : Blo 920579 5247935 := bstep (se 1 (by rfl) ⟨3935951, by rfl⟩ : syracuseStep 5247935 = 7871903) B7871903
theorem B5254793 : Blo 920579 5254793 := bstep (se 2 (by rfl) ⟨1970547, by rfl⟩ : syracuseStep 5254793 = 3941095) B3941095
theorem B1752167 : Blo 920579 1752167 := bstep (se 1 (by rfl) ⟨1314125, by rfl⟩ : syracuseStep 1752167 = 2628251) B2628251
theorem B1559209 : Blo 920579 1559209 := bstep (se 2 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 1559209 = 1169407) B1169407
theorem B37924685 : Blo 920579 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B2078945 : Blo 920579 2078945 := bstep (se 2 (by rfl) ⟨779604, by rfl⟩ : syracuseStep 2078945 = 1559209) B1559209
theorem B1168111 : Blo 920579 1168111 := bstep (se 1 (by rfl) ⟨876083, by rfl⟩ : syracuseStep 1168111 = 1752167) B1752167
theorem B3498623 : Blo 920579 3498623 := bstep (se 1 (by rfl) ⟨2623967, by rfl⟩ : syracuseStep 3498623 = 5247935) B5247935
theorem B3503195 : Blo 920579 3503195 := bstep (se 1 (by rfl) ⟨2627396, by rfl⟩ : syracuseStep 3503195 = 5254793) B5254793
theorem B2332415 : Blo 920579 2332415 := bstep (se 1 (by rfl) ⟨1749311, by rfl⟩ : syracuseStep 2332415 = 3498623) B3498623
theorem B2335463 : Blo 920579 2335463 := bstep (se 1 (by rfl) ⟨1751597, by rfl⟩ : syracuseStep 2335463 = 3503195) B3503195
theorem B1385963 : Blo 920579 1385963 := bstep (se 1 (by rfl) ⟨1039472, by rfl⟩ : syracuseStep 1385963 = 2078945) B2078945
theorem B1557481 : Blo 920579 1557481 := bstep (se 2 (by rfl) ⟨584055, by rfl⟩ : syracuseStep 1557481 = 1168111) B1168111
theorem B25283123 : Blo 920579 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B923975 : Blo 920579 923975 := bstep (se 1 (by rfl) ⟨692981, by rfl⟩ : syracuseStep 923975 = 1385963) B1385963
theorem B2076641 : Blo 920579 2076641 := bstep (se 2 (by rfl) ⟨778740, by rfl⟩ : syracuseStep 2076641 = 1557481) B1557481
theorem B16855415 : Blo 920579 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B1554943 : Blo 920579 1554943 := bstep (se 1 (by rfl) ⟨1166207, by rfl⟩ : syracuseStep 1554943 = 2332415) B2332415
theorem B1556975 : Blo 920579 1556975 := bstep (se 1 (by rfl) ⟨1167731, by rfl⟩ : syracuseStep 1556975 = 2335463) B2335463
theorem B1384427 : Blo 920579 1384427 := bstep (se 1 (by rfl) ⟨1038320, by rfl⟩ : syracuseStep 1384427 = 2076641) B2076641
theorem B2073257 : Blo 920579 2073257 := bstep (se 2 (by rfl) ⟨777471, by rfl⟩ : syracuseStep 2073257 = 1554943) B1554943
theorem B1037983 : Blo 920579 1037983 := bstep (se 1 (by rfl) ⟨778487, by rfl⟩ : syracuseStep 1037983 = 1556975) B1556975
theorem B11236943 : Blo 920579 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B922951 : Blo 920579 922951 := bstep (se 1 (by rfl) ⟨692213, by rfl⟩ : syracuseStep 922951 = 1384427) B1384427
theorem B1382171 : Blo 920579 1382171 := bstep (se 1 (by rfl) ⟨1036628, by rfl⟩ : syracuseStep 1382171 = 2073257) B2073257
theorem B1383977 : Blo 920579 1383977 := bstep (se 2 (by rfl) ⟨518991, by rfl⟩ : syracuseStep 1383977 = 1037983) B1037983
theorem B7491295 : Blo 920579 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B921447 : Blo 920579 921447 := bstep (se 1 (by rfl) ⟨691085, by rfl⟩ : syracuseStep 921447 = 1382171) B1382171
theorem B922651 : Blo 920579 922651 := bstep (se 1 (by rfl) ⟨691988, by rfl⟩ : syracuseStep 922651 = 1383977) B1383977
theorem B39953573 : Blo 920579 39953573 := bstep (se 4 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 39953573 = 7491295) B7491295
theorem B26635715 : Blo 920579 26635715 := bstep (se 1 (by rfl) ⟨19976786, by rfl⟩ : syracuseStep 26635715 = 39953573) B39953573
theorem B17757143 : Blo 920579 17757143 := bstep (se 1 (by rfl) ⟨13317857, by rfl⟩ : syracuseStep 17757143 = 26635715) B26635715
theorem B11838095 : Blo 920579 11838095 := bstep (se 1 (by rfl) ⟨8878571, by rfl⟩ : syracuseStep 11838095 = 17757143) B17757143
theorem B7892063 : Blo 920579 7892063 := bstep (se 1 (by rfl) ⟨5919047, by rfl⟩ : syracuseStep 7892063 = 11838095) B11838095
theorem B5261375 : Blo 920579 5261375 := bstep (se 1 (by rfl) ⟨3946031, by rfl⟩ : syracuseStep 5261375 = 7892063) B7892063
theorem B3507583 : Blo 920579 3507583 := bstep (se 1 (by rfl) ⟨2630687, by rfl⟩ : syracuseStep 3507583 = 5261375) B5261375
theorem B4676777 : Blo 920579 4676777 := bstep (se 2 (by rfl) ⟨1753791, by rfl⟩ : syracuseStep 4676777 = 3507583) B3507583
theorem B3117851 : Blo 920579 3117851 := bstep (se 1 (by rfl) ⟨2338388, by rfl⟩ : syracuseStep 3117851 = 4676777) B4676777
theorem B2078567 : Blo 920579 2078567 := bstep (se 1 (by rfl) ⟨1558925, by rfl⟩ : syracuseStep 2078567 = 3117851) B3117851
theorem B1385711 : Blo 920579 1385711 := bstep (se 1 (by rfl) ⟨1039283, by rfl⟩ : syracuseStep 1385711 = 2078567) B2078567
theorem B923807 : Blo 920579 923807 := bstep (se 1 (by rfl) ⟨692855, by rfl⟩ : syracuseStep 923807 = 1385711) B1385711

theorem C0 (j : ℕ) (h1 : 230144 ≤ j) (h2 : j ≤ 230843) : Blo 920579 (4 * j + 3) := by
  interval_cases j
  · exact B920579
  · exact B920583
  · exact B920587
  · exact B920591
  · exact B920595
  · exact B920599
  · exact B920603
  · exact B920607
  · exact B920611
  · exact B920615
  · exact B920619
  · exact B920623
  · exact B920627
  · exact B920631
  · exact B920635
  · exact B920639
  · exact B920643
  · exact B920647
  · exact B920651
  · exact B920655
  · exact B920659
  · exact B920663
  · exact B920667
  · exact B920671
  · exact B920675
  · exact B920679
  · exact B920683
  · exact B920687
  · exact B920691
  · exact B920695
  · exact B920699
  · exact B920703
  · exact B920707
  · exact B920711
  · exact B920715
  · exact B920719
  · exact B920723
  · exact B920727
  · exact B920731
  · exact B920735
  · exact B920739
  · exact B920743
  · exact B920747
  · exact B920751
  · exact B920755
  · exact B920759
  · exact B920763
  · exact B920767
  · exact B920771
  · exact B920775
  · exact B920779
  · exact B920783
  · exact B920787
  · exact B920791
  · exact B920795
  · exact B920799
  · exact B920803
  · exact B920807
  · exact B920811
  · exact B920815
  · exact B920819
  · exact B920823
  · exact B920827
  · exact B920831
  · exact B920835
  · exact B920839
  · exact B920843
  · exact B920847
  · exact B920851
  · exact B920855
  · exact B920859
  · exact B920863
  · exact B920867
  · exact B920871
  · exact B920875
  · exact B920879
  · exact B920883
  · exact B920887
  · exact B920891
  · exact B920895
  · exact B920899
  · exact B920903
  · exact B920907
  · exact B920911
  · exact B920915
  · exact B920919
  · exact B920923
  · exact B920927
  · exact B920931
  · exact B920935
  · exact B920939
  · exact B920943
  · exact B920947
  · exact B920951
  · exact B920955
  · exact B920959
  · exact B920963
  · exact B920967
  · exact B920971
  · exact B920975
  · exact B920979
  · exact B920983
  · exact B920987
  · exact B920991
  · exact B920995
  · exact B920999
  · exact B921003
  · exact B921007
  · exact B921011
  · exact B921015
  · exact B921019
  · exact B921023
  · exact B921027
  · exact B921031
  · exact B921035
  · exact B921039
  · exact B921043
  · exact B921047
  · exact B921051
  · exact B921055
  · exact B921059
  · exact B921063
  · exact B921067
  · exact B921071
  · exact B921075
  · exact B921079
  · exact B921083
  · exact B921087
  · exact B921091
  · exact B921095
  · exact B921099
  · exact B921103
  · exact B921107
  · exact B921111
  · exact B921115
  · exact B921119
  · exact B921123
  · exact B921127
  · exact B921131
  · exact B921135
  · exact B921139
  · exact B921143
  · exact B921147
  · exact B921151
  · exact B921155
  · exact B921159
  · exact B921163
  · exact B921167
  · exact B921171
  · exact B921175
  · exact B921179
  · exact B921183
  · exact B921187
  · exact B921191
  · exact B921195
  · exact B921199
  · exact B921203
  · exact B921207
  · exact B921211
  · exact B921215
  · exact B921219
  · exact B921223
  · exact B921227
  · exact B921231
  · exact B921235
  · exact B921239
  · exact B921243
  · exact B921247
  · exact B921251
  · exact B921255
  · exact B921259
  · exact B921263
  · exact B921267
  · exact B921271
  · exact B921275
  · exact B921279
  · exact B921283
  · exact B921287
  · exact B921291
  · exact B921295
  · exact B921299
  · exact B921303
  · exact B921307
  · exact B921311
  · exact B921315
  · exact B921319
  · exact B921323
  · exact B921327
  · exact B921331
  · exact B921335
  · exact B921339
  · exact B921343
  · exact B921347
  · exact B921351
  · exact B921355
  · exact B921359
  · exact B921363
  · exact B921367
  · exact B921371
  · exact B921375
  · exact B921379
  · exact B921383
  · exact B921387
  · exact B921391
  · exact B921395
  · exact B921399
  · exact B921403
  · exact B921407
  · exact B921411
  · exact B921415
  · exact B921419
  · exact B921423
  · exact B921427
  · exact B921431
  · exact B921435
  · exact B921439
  · exact B921443
  · exact B921447
  · exact B921451
  · exact B921455
  · exact B921459
  · exact B921463
  · exact B921467
  · exact B921471
  · exact B921475
  · exact B921479
  · exact B921483
  · exact B921487
  · exact B921491
  · exact B921495
  · exact B921499
  · exact B921503
  · exact B921507
  · exact B921511
  · exact B921515
  · exact B921519
  · exact B921523
  · exact B921527
  · exact B921531
  · exact B921535
  · exact B921539
  · exact B921543
  · exact B921547
  · exact B921551
  · exact B921555
  · exact B921559
  · exact B921563
  · exact B921567
  · exact B921571
  · exact B921575
  · exact B921579
  · exact B921583
  · exact B921587
  · exact B921591
  · exact B921595
  · exact B921599
  · exact B921603
  · exact B921607
  · exact B921611
  · exact B921615
  · exact B921619
  · exact B921623
  · exact B921627
  · exact B921631
  · exact B921635
  · exact B921639
  · exact B921643
  · exact B921647
  · exact B921651
  · exact B921655
  · exact B921659
  · exact B921663
  · exact B921667
  · exact B921671
  · exact B921675
  · exact B921679
  · exact B921683
  · exact B921687
  · exact B921691
  · exact B921695
  · exact B921699
  · exact B921703
  · exact B921707
  · exact B921711
  · exact B921715
  · exact B921719
  · exact B921723
  · exact B921727
  · exact B921731
  · exact B921735
  · exact B921739
  · exact B921743
  · exact B921747
  · exact B921751
  · exact B921755
  · exact B921759
  · exact B921763
  · exact B921767
  · exact B921771
  · exact B921775
  · exact B921779
  · exact B921783
  · exact B921787
  · exact B921791
  · exact B921795
  · exact B921799
  · exact B921803
  · exact B921807
  · exact B921811
  · exact B921815
  · exact B921819
  · exact B921823
  · exact B921827
  · exact B921831
  · exact B921835
  · exact B921839
  · exact B921843
  · exact B921847
  · exact B921851
  · exact B921855
  · exact B921859
  · exact B921863
  · exact B921867
  · exact B921871
  · exact B921875
  · exact B921879
  · exact B921883
  · exact B921887
  · exact B921891
  · exact B921895
  · exact B921899
  · exact B921903
  · exact B921907
  · exact B921911
  · exact B921915
  · exact B921919
  · exact B921923
  · exact B921927
  · exact B921931
  · exact B921935
  · exact B921939
  · exact B921943
  · exact B921947
  · exact B921951
  · exact B921955
  · exact B921959
  · exact B921963
  · exact B921967
  · exact B921971
  · exact B921975
  · exact B921979
  · exact B921983
  · exact B921987
  · exact B921991
  · exact B921995
  · exact B921999
  · exact B922003
  · exact B922007
  · exact B922011
  · exact B922015
  · exact B922019
  · exact B922023
  · exact B922027
  · exact B922031
  · exact B922035
  · exact B922039
  · exact B922043
  · exact B922047
  · exact B922051
  · exact B922055
  · exact B922059
  · exact B922063
  · exact B922067
  · exact B922071
  · exact B922075
  · exact B922079
  · exact B922083
  · exact B922087
  · exact B922091
  · exact B922095
  · exact B922099
  · exact B922103
  · exact B922107
  · exact B922111
  · exact B922115
  · exact B922119
  · exact B922123
  · exact B922127
  · exact B922131
  · exact B922135
  · exact B922139
  · exact B922143
  · exact B922147
  · exact B922151
  · exact B922155
  · exact B922159
  · exact B922163
  · exact B922167
  · exact B922171
  · exact B922175
  · exact B922179
  · exact B922183
  · exact B922187
  · exact B922191
  · exact B922195
  · exact B922199
  · exact B922203
  · exact B922207
  · exact B922211
  · exact B922215
  · exact B922219
  · exact B922223
  · exact B922227
  · exact B922231
  · exact B922235
  · exact B922239
  · exact B922243
  · exact B922247
  · exact B922251
  · exact B922255
  · exact B922259
  · exact B922263
  · exact B922267
  · exact B922271
  · exact B922275
  · exact B922279
  · exact B922283
  · exact B922287
  · exact B922291
  · exact B922295
  · exact B922299
  · exact B922303
  · exact B922307
  · exact B922311
  · exact B922315
  · exact B922319
  · exact B922323
  · exact B922327
  · exact B922331
  · exact B922335
  · exact B922339
  · exact B922343
  · exact B922347
  · exact B922351
  · exact B922355
  · exact B922359
  · exact B922363
  · exact B922367
  · exact B922371
  · exact B922375
  · exact B922379
  · exact B922383
  · exact B922387
  · exact B922391
  · exact B922395
  · exact B922399
  · exact B922403
  · exact B922407
  · exact B922411
  · exact B922415
  · exact B922419
  · exact B922423
  · exact B922427
  · exact B922431
  · exact B922435
  · exact B922439
  · exact B922443
  · exact B922447
  · exact B922451
  · exact B922455
  · exact B922459
  · exact B922463
  · exact B922467
  · exact B922471
  · exact B922475
  · exact B922479
  · exact B922483
  · exact B922487
  · exact B922491
  · exact B922495
  · exact B922499
  · exact B922503
  · exact B922507
  · exact B922511
  · exact B922515
  · exact B922519
  · exact B922523
  · exact B922527
  · exact B922531
  · exact B922535
  · exact B922539
  · exact B922543
  · exact B922547
  · exact B922551
  · exact B922555
  · exact B922559
  · exact B922563
  · exact B922567
  · exact B922571
  · exact B922575
  · exact B922579
  · exact B922583
  · exact B922587
  · exact B922591
  · exact B922595
  · exact B922599
  · exact B922603
  · exact B922607
  · exact B922611
  · exact B922615
  · exact B922619
  · exact B922623
  · exact B922627
  · exact B922631
  · exact B922635
  · exact B922639
  · exact B922643
  · exact B922647
  · exact B922651
  · exact B922655
  · exact B922659
  · exact B922663
  · exact B922667
  · exact B922671
  · exact B922675
  · exact B922679
  · exact B922683
  · exact B922687
  · exact B922691
  · exact B922695
  · exact B922699
  · exact B922703
  · exact B922707
  · exact B922711
  · exact B922715
  · exact B922719
  · exact B922723
  · exact B922727
  · exact B922731
  · exact B922735
  · exact B922739
  · exact B922743
  · exact B922747
  · exact B922751
  · exact B922755
  · exact B922759
  · exact B922763
  · exact B922767
  · exact B922771
  · exact B922775
  · exact B922779
  · exact B922783
  · exact B922787
  · exact B922791
  · exact B922795
  · exact B922799
  · exact B922803
  · exact B922807
  · exact B922811
  · exact B922815
  · exact B922819
  · exact B922823
  · exact B922827
  · exact B922831
  · exact B922835
  · exact B922839
  · exact B922843
  · exact B922847
  · exact B922851
  · exact B922855
  · exact B922859
  · exact B922863
  · exact B922867
  · exact B922871
  · exact B922875
  · exact B922879
  · exact B922883
  · exact B922887
  · exact B922891
  · exact B922895
  · exact B922899
  · exact B922903
  · exact B922907
  · exact B922911
  · exact B922915
  · exact B922919
  · exact B922923
  · exact B922927
  · exact B922931
  · exact B922935
  · exact B922939
  · exact B922943
  · exact B922947
  · exact B922951
  · exact B922955
  · exact B922959
  · exact B922963
  · exact B922967
  · exact B922971
  · exact B922975
  · exact B922979
  · exact B922983
  · exact B922987
  · exact B922991
  · exact B922995
  · exact B922999
  · exact B923003
  · exact B923007
  · exact B923011
  · exact B923015
  · exact B923019
  · exact B923023
  · exact B923027
  · exact B923031
  · exact B923035
  · exact B923039
  · exact B923043
  · exact B923047
  · exact B923051
  · exact B923055
  · exact B923059
  · exact B923063
  · exact B923067
  · exact B923071
  · exact B923075
  · exact B923079
  · exact B923083
  · exact B923087
  · exact B923091
  · exact B923095
  · exact B923099
  · exact B923103
  · exact B923107
  · exact B923111
  · exact B923115
  · exact B923119
  · exact B923123
  · exact B923127
  · exact B923131
  · exact B923135
  · exact B923139
  · exact B923143
  · exact B923147
  · exact B923151
  · exact B923155
  · exact B923159
  · exact B923163
  · exact B923167
  · exact B923171
  · exact B923175
  · exact B923179
  · exact B923183
  · exact B923187
  · exact B923191
  · exact B923195
  · exact B923199
  · exact B923203
  · exact B923207
  · exact B923211
  · exact B923215
  · exact B923219
  · exact B923223
  · exact B923227
  · exact B923231
  · exact B923235
  · exact B923239
  · exact B923243
  · exact B923247
  · exact B923251
  · exact B923255
  · exact B923259
  · exact B923263
  · exact B923267
  · exact B923271
  · exact B923275
  · exact B923279
  · exact B923283
  · exact B923287
  · exact B923291
  · exact B923295
  · exact B923299
  · exact B923303
  · exact B923307
  · exact B923311
  · exact B923315
  · exact B923319
  · exact B923323
  · exact B923327
  · exact B923331
  · exact B923335
  · exact B923339
  · exact B923343
  · exact B923347
  · exact B923351
  · exact B923355
  · exact B923359
  · exact B923363
  · exact B923367
  · exact B923371
  · exact B923375

theorem C1 (j : ℕ) (h1 : 230844 ≤ j) (h2 : j ≤ 231144) : Blo 920579 (4 * j + 3) := by
  interval_cases j
  · exact B923379
  · exact B923383
  · exact B923387
  · exact B923391
  · exact B923395
  · exact B923399
  · exact B923403
  · exact B923407
  · exact B923411
  · exact B923415
  · exact B923419
  · exact B923423
  · exact B923427
  · exact B923431
  · exact B923435
  · exact B923439
  · exact B923443
  · exact B923447
  · exact B923451
  · exact B923455
  · exact B923459
  · exact B923463
  · exact B923467
  · exact B923471
  · exact B923475
  · exact B923479
  · exact B923483
  · exact B923487
  · exact B923491
  · exact B923495
  · exact B923499
  · exact B923503
  · exact B923507
  · exact B923511
  · exact B923515
  · exact B923519
  · exact B923523
  · exact B923527
  · exact B923531
  · exact B923535
  · exact B923539
  · exact B923543
  · exact B923547
  · exact B923551
  · exact B923555
  · exact B923559
  · exact B923563
  · exact B923567
  · exact B923571
  · exact B923575
  · exact B923579
  · exact B923583
  · exact B923587
  · exact B923591
  · exact B923595
  · exact B923599
  · exact B923603
  · exact B923607
  · exact B923611
  · exact B923615
  · exact B923619
  · exact B923623
  · exact B923627
  · exact B923631
  · exact B923635
  · exact B923639
  · exact B923643
  · exact B923647
  · exact B923651
  · exact B923655
  · exact B923659
  · exact B923663
  · exact B923667
  · exact B923671
  · exact B923675
  · exact B923679
  · exact B923683
  · exact B923687
  · exact B923691
  · exact B923695
  · exact B923699
  · exact B923703
  · exact B923707
  · exact B923711
  · exact B923715
  · exact B923719
  · exact B923723
  · exact B923727
  · exact B923731
  · exact B923735
  · exact B923739
  · exact B923743
  · exact B923747
  · exact B923751
  · exact B923755
  · exact B923759
  · exact B923763
  · exact B923767
  · exact B923771
  · exact B923775
  · exact B923779
  · exact B923783
  · exact B923787
  · exact B923791
  · exact B923795
  · exact B923799
  · exact B923803
  · exact B923807
  · exact B923811
  · exact B923815
  · exact B923819
  · exact B923823
  · exact B923827
  · exact B923831
  · exact B923835
  · exact B923839
  · exact B923843
  · exact B923847
  · exact B923851
  · exact B923855
  · exact B923859
  · exact B923863
  · exact B923867
  · exact B923871
  · exact B923875
  · exact B923879
  · exact B923883
  · exact B923887
  · exact B923891
  · exact B923895
  · exact B923899
  · exact B923903
  · exact B923907
  · exact B923911
  · exact B923915
  · exact B923919
  · exact B923923
  · exact B923927
  · exact B923931
  · exact B923935
  · exact B923939
  · exact B923943
  · exact B923947
  · exact B923951
  · exact B923955
  · exact B923959
  · exact B923963
  · exact B923967
  · exact B923971
  · exact B923975
  · exact B923979
  · exact B923983
  · exact B923987
  · exact B923991
  · exact B923995
  · exact B923999
  · exact B924003
  · exact B924007
  · exact B924011
  · exact B924015
  · exact B924019
  · exact B924023
  · exact B924027
  · exact B924031
  · exact B924035
  · exact B924039
  · exact B924043
  · exact B924047
  · exact B924051
  · exact B924055
  · exact B924059
  · exact B924063
  · exact B924067
  · exact B924071
  · exact B924075
  · exact B924079
  · exact B924083
  · exact B924087
  · exact B924091
  · exact B924095
  · exact B924099
  · exact B924103
  · exact B924107
  · exact B924111
  · exact B924115
  · exact B924119
  · exact B924123
  · exact B924127
  · exact B924131
  · exact B924135
  · exact B924139
  · exact B924143
  · exact B924147
  · exact B924151
  · exact B924155
  · exact B924159
  · exact B924163
  · exact B924167
  · exact B924171
  · exact B924175
  · exact B924179
  · exact B924183
  · exact B924187
  · exact B924191
  · exact B924195
  · exact B924199
  · exact B924203
  · exact B924207
  · exact B924211
  · exact B924215
  · exact B924219
  · exact B924223
  · exact B924227
  · exact B924231
  · exact B924235
  · exact B924239
  · exact B924243
  · exact B924247
  · exact B924251
  · exact B924255
  · exact B924259
  · exact B924263
  · exact B924267
  · exact B924271
  · exact B924275
  · exact B924279
  · exact B924283
  · exact B924287
  · exact B924291
  · exact B924295
  · exact B924299
  · exact B924303
  · exact B924307
  · exact B924311
  · exact B924315
  · exact B924319
  · exact B924323
  · exact B924327
  · exact B924331
  · exact B924335
  · exact B924339
  · exact B924343
  · exact B924347
  · exact B924351
  · exact B924355
  · exact B924359
  · exact B924363
  · exact B924367
  · exact B924371
  · exact B924375
  · exact B924379
  · exact B924383
  · exact B924387
  · exact B924391
  · exact B924395
  · exact B924399
  · exact B924403
  · exact B924407
  · exact B924411
  · exact B924415
  · exact B924419
  · exact B924423
  · exact B924427
  · exact B924431
  · exact B924435
  · exact B924439
  · exact B924443
  · exact B924447
  · exact B924451
  · exact B924455
  · exact B924459
  · exact B924463
  · exact B924467
  · exact B924471
  · exact B924475
  · exact B924479
  · exact B924483
  · exact B924487
  · exact B924491
  · exact B924495
  · exact B924499
  · exact B924503
  · exact B924507
  · exact B924511
  · exact B924515
  · exact B924519
  · exact B924523
  · exact B924527
  · exact B924531
  · exact B924535
  · exact B924539
  · exact B924543
  · exact B924547
  · exact B924551
  · exact B924555
  · exact B924559
  · exact B924563
  · exact B924567
  · exact B924571
  · exact B924575
  · exact B924579

theorem solution (m : ℕ) (hlo : 920579 ≤ m) (hhi : m ≤ 924579) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 230144 ≤ j := by omega
    have hj2 : j ≤ 231144 := by omega
    have hb : Blo 920579 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 230844 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
