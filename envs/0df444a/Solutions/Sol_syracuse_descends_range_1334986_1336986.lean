-- Prove2me | solution 1 for syracuse_descends_range_1334986_1336986
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:42.580738+00:00
-- url     : https://prove2.me/submissions/61689f38-7e08-4877-9f52-e6168fedce08

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


theorem B3383309 : Blo 1334986 3383309 := bbase (se 3 (by rfl) ⟨634370, by rfl⟩ : syracuseStep 3383309 = 1268741) (by norm_num)
theorem B3006485 : Blo 1334986 3006485 := bbase (se 6 (by rfl) ⟨70464, by rfl⟩ : syracuseStep 3006485 = 140929) (by norm_num)
theorem B16482325 : Blo 1334986 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B2252893 : Blo 1334986 2252893 := bbase (se 3 (by rfl) ⟨422417, by rfl⟩ : syracuseStep 2252893 = 844835) (by norm_num)
theorem B3006557 : Blo 1334986 3006557 := bbase (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) (by norm_num)
theorem B3211397 : Blo 1334986 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B3006629 : Blo 1334986 3006629 := bbase (se 4 (by rfl) ⟨281871, by rfl⟩ : syracuseStep 3006629 = 563743) (by norm_num)
theorem B2252981 : Blo 1334986 2252981 := bbase (se 5 (by rfl) ⟨105608, by rfl⟩ : syracuseStep 2252981 = 211217) (by norm_num)
theorem B5071045 : Blo 1334986 5071045 := bbase (se 4 (by rfl) ⟨475410, by rfl⟩ : syracuseStep 5071045 = 950821) (by norm_num)
theorem B4505813 : Blo 1334986 4505813 := bbase (se 7 (by rfl) ⟨52802, by rfl⟩ : syracuseStep 4505813 = 105605) (by norm_num)
theorem B3006701 : Blo 1334986 3006701 := bbase (se 3 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 3006701 = 1127513) (by norm_num)
theorem B2031877 : Blo 1334986 2031877 := bbase (se 4 (by rfl) ⟨190488, by rfl⟩ : syracuseStep 2031877 = 380977) (by norm_num)
theorem B1425685 : Blo 1334986 1425685 := bbase (se 6 (by rfl) ⟨33414, by rfl⟩ : syracuseStep 1425685 = 66829) (by norm_num)
theorem B2253109 : Blo 1334986 2253109 := bbase (se 5 (by rfl) ⟨105614, by rfl⟩ : syracuseStep 2253109 = 211229) (by norm_num)
theorem B3006773 : Blo 1334986 3006773 := bbase (se 5 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 3006773 = 281885) (by norm_num)
theorem B6766901 : Blo 1334986 6766901 := bbase (se 5 (by rfl) ⟨317198, by rfl⟩ : syracuseStep 6766901 = 634397) (by norm_num)
theorem B1605953 : Blo 1334986 1605953 := bbase (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) (by norm_num)
theorem B3383653 : Blo 1334986 3383653 := bbase (se 4 (by rfl) ⟨317217, by rfl⟩ : syracuseStep 3383653 = 634435) (by norm_num)
theorem B3006845 : Blo 1334986 3006845 := bbase (se 3 (by rfl) ⟨563783, by rfl⟩ : syracuseStep 3006845 = 1127567) (by norm_num)
theorem B2253197 : Blo 1334986 2253197 := bbase (se 3 (by rfl) ⟨422474, by rfl⟩ : syracuseStep 2253197 = 844949) (by norm_num)
theorem B2892205 : Blo 1334986 2892205 := bbase (se 3 (by rfl) ⟨542288, by rfl⟩ : syracuseStep 2892205 = 1084577) (by norm_num)
theorem B1524145 : Blo 1334986 1524145 := bbase (se 2 (by rfl) ⟨571554, by rfl⟩ : syracuseStep 1524145 = 1143109) (by norm_num)
theorem B5489093 : Blo 1334986 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B3006917 : Blo 1334986 3006917 := bbase (se 4 (by rfl) ⟨281898, by rfl⟩ : syracuseStep 3006917 = 563797) (by norm_num)
theorem B3383765 : Blo 1334986 3383765 := bbase (se 7 (by rfl) ⟨39653, by rfl⟩ : syracuseStep 3383765 = 79307) (by norm_num)
theorem B5071349 : Blo 1334986 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B2253325 : Blo 1334986 2253325 := bbase (se 3 (by rfl) ⟨422498, by rfl⟩ : syracuseStep 2253325 = 844997) (by norm_num)
theorem B3006989 : Blo 1334986 3006989 := bbase (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) (by norm_num)
theorem B12182069 : Blo 1334986 12182069 := bbase (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) (by norm_num)
theorem B1712713 : Blo 1334986 1712713 := bbase (se 2 (by rfl) ⟨642267, by rfl⟩ : syracuseStep 1712713 = 1284535) (by norm_num)
theorem B51372629 : Blo 1334986 51372629 := bbase (se 8 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 51372629 = 602023) (by norm_num)
theorem B3007061 : Blo 1334986 3007061 := bbase (se 8 (by rfl) ⟨17619, by rfl⟩ : syracuseStep 3007061 = 35239) (by norm_num)
theorem B2253413 : Blo 1334986 2253413 := bbase (se 4 (by rfl) ⟨211257, by rfl⟩ : syracuseStep 2253413 = 422515) (by norm_num)
theorem B4506245 : Blo 1334986 4506245 := bbase (se 4 (by rfl) ⟨422460, by rfl⟩ : syracuseStep 4506245 = 844921) (by norm_num)
theorem B3383957 : Blo 1334986 3383957 := bbase (se 6 (by rfl) ⟨79311, by rfl⟩ : syracuseStep 3383957 = 158623) (by norm_num)
theorem B3007133 : Blo 1334986 3007133 := bbase (se 3 (by rfl) ⟨563837, by rfl⟩ : syracuseStep 3007133 = 1127675) (by norm_num)
theorem B4276901 : Blo 1334986 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B3048101 : Blo 1334986 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B2286245 : Blo 1334986 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B1426129 : Blo 1334986 1426129 := bbase (se 2 (by rfl) ⟨534798, by rfl⟩ : syracuseStep 1426129 = 1069597) (by norm_num)
theorem B6759125 : Blo 1334986 6759125 := bbase (se 7 (by rfl) ⟨79208, by rfl⟩ : syracuseStep 6759125 = 158417) (by norm_num)
theorem B2851541 : Blo 1334986 2851541 := bbase (se 7 (by rfl) ⟨33416, by rfl⟩ : syracuseStep 2851541 = 66833) (by norm_num)
theorem B2253541 : Blo 1334986 2253541 := bbase (se 4 (by rfl) ⟨211269, by rfl⟩ : syracuseStep 2253541 = 422539) (by norm_num)
theorem B3007205 : Blo 1334986 3007205 := bbase (se 4 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 3007205 = 563851) (by norm_num)
theorem B2138861 : Blo 1334986 2138861 := bbase (se 3 (by rfl) ⟨401036, by rfl⟩ : syracuseStep 2138861 = 802073) (by norm_num)
theorem B3007277 : Blo 1334986 3007277 := bbase (se 3 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 3007277 = 1127729) (by norm_num)
theorem B2253629 : Blo 1334986 2253629 := bbase (se 3 (by rfl) ⟨422555, by rfl⟩ : syracuseStep 2253629 = 845111) (by norm_num)
theorem B1426249 : Blo 1334986 1426249 := bbase (se 2 (by rfl) ⟨534843, by rfl⟩ : syracuseStep 1426249 = 1069687) (by norm_num)
theorem B2851661 : Blo 1334986 2851661 := bbase (se 3 (by rfl) ⟨534686, by rfl⟩ : syracuseStep 2851661 = 1069373) (by norm_num)
theorem B3801941 : Blo 1334986 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B5702501 : Blo 1334986 5702501 := bbase (se 4 (by rfl) ⟨534609, by rfl⟩ : syracuseStep 5702501 = 1069219) (by norm_num)
theorem B2138989 : Blo 1334986 2138989 := bbase (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) (by norm_num)
theorem B3007349 : Blo 1334986 3007349 := bbase (se 5 (by rfl) ⟨140969, by rfl⟩ : syracuseStep 3007349 = 281939) (by norm_num)
theorem B2139053 : Blo 1334986 2139053 := bbase (se 3 (by rfl) ⟨401072, by rfl⟩ : syracuseStep 2139053 = 802145) (by norm_num)
theorem B2253757 : Blo 1334986 2253757 := bbase (se 3 (by rfl) ⟨422579, by rfl⟩ : syracuseStep 2253757 = 845159) (by norm_num)
theorem B3007421 : Blo 1334986 3007421 := bbase (se 3 (by rfl) ⟨563891, by rfl⟩ : syracuseStep 3007421 = 1127783) (by norm_num)
theorem B3007493 : Blo 1334986 3007493 := bbase (se 4 (by rfl) ⟨281952, by rfl⟩ : syracuseStep 3007493 = 563905) (by norm_num)
theorem B2253845 : Blo 1334986 2253845 := bbase (se 6 (by rfl) ⟨52824, by rfl⟩ : syracuseStep 2253845 = 105649) (by norm_num)
theorem B14443541 : Blo 1334986 14443541 := bbase (se 6 (by rfl) ⟨338520, by rfl⟩ : syracuseStep 14443541 = 677041) (by norm_num)
theorem B4506677 : Blo 1334986 4506677 := bbase (se 5 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 4506677 = 422501) (by norm_num)
theorem B1426501 : Blo 1334986 1426501 := bbase (se 4 (by rfl) ⟨133734, by rfl⟩ : syracuseStep 1426501 = 267469) (by norm_num)
theorem B1426505 : Blo 1334986 1426505 := bbase (se 2 (by rfl) ⟨534939, by rfl⟩ : syracuseStep 1426505 = 1069879) (by norm_num)
theorem B3007565 : Blo 1334986 3007565 := bbase (se 3 (by rfl) ⟨563918, by rfl⟩ : syracuseStep 3007565 = 1127837) (by norm_num)
theorem B2253973 : Blo 1334986 2253973 := bbase (se 6 (by rfl) ⟨52827, by rfl⟩ : syracuseStep 2253973 = 105655) (by norm_num)
theorem B3007637 : Blo 1334986 3007637 := bbase (se 6 (by rfl) ⟨70491, by rfl⟩ : syracuseStep 3007637 = 140983) (by norm_num)
theorem B3007709 : Blo 1334986 3007709 := bbase (se 3 (by rfl) ⟨563945, by rfl⟩ : syracuseStep 3007709 = 1127891) (by norm_num)
theorem B2254061 : Blo 1334986 2254061 := bbase (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) (by norm_num)
theorem B3802373 : Blo 1334986 3802373 := bbase (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) (by norm_num)
theorem B3007781 : Blo 1334986 3007781 := bbase (se 4 (by rfl) ⟨281979, by rfl⟩ : syracuseStep 3007781 = 563959) (by norm_num)
theorem B1901893 : Blo 1334986 1901893 := bbase (se 4 (by rfl) ⟨178302, by rfl⟩ : syracuseStep 1901893 = 356605) (by norm_num)
theorem B38495573 : Blo 1334986 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B2254189 : Blo 1334986 2254189 := bbase (se 3 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 2254189 = 845321) (by norm_num)
theorem B3007853 : Blo 1334986 3007853 := bbase (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) (by norm_num)
theorem B3007925 : Blo 1334986 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B2852293 : Blo 1334986 2852293 := bbase (se 4 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 2852293 = 534805) (by norm_num)
theorem B2254277 : Blo 1334986 2254277 := bbase (se 4 (by rfl) ⟨211338, by rfl⟩ : syracuseStep 2254277 = 422677) (by norm_num)
theorem B4507109 : Blo 1334986 4507109 := bbase (se 4 (by rfl) ⟨422541, by rfl⟩ : syracuseStep 4507109 = 845083) (by norm_num)
theorem B3007997 : Blo 1334986 3007997 := bbase (se 3 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 3007997 = 1127999) (by norm_num)
theorem B2254405 : Blo 1334986 2254405 := bbase (se 4 (by rfl) ⟨211350, by rfl⟩ : syracuseStep 2254405 = 422701) (by norm_num)
theorem B3008069 : Blo 1334986 3008069 := bbase (se 4 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 3008069 = 564013) (by norm_num)
theorem B6768197 : Blo 1334986 6768197 := bbase (se 4 (by rfl) ⟨634518, by rfl⟩ : syracuseStep 6768197 = 1269037) (by norm_num)
theorem B1427069 : Blo 1334986 1427069 := bbase (se 3 (by rfl) ⟨267575, by rfl⟩ : syracuseStep 1427069 = 535151) (by norm_num)
theorem B1353349 : Blo 1334986 1353349 := bbase (se 4 (by rfl) ⟨126876, by rfl⟩ : syracuseStep 1353349 = 253753) (by norm_num)
theorem B3008141 : Blo 1334986 3008141 := bbase (se 3 (by rfl) ⟨564026, by rfl⟩ : syracuseStep 3008141 = 1128053) (by norm_num)
theorem B15214229 : Blo 1334986 15214229 := bbase (se 6 (by rfl) ⟨356583, by rfl⟩ : syracuseStep 15214229 = 713167) (by norm_num)
theorem B2254493 : Blo 1334986 2254493 := bbase (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) (by norm_num)
theorem B1353385 : Blo 1334986 1353385 := bbase (se 2 (by rfl) ⟨507519, by rfl⟩ : syracuseStep 1353385 = 1015039) (by norm_num)
theorem B3008213 : Blo 1334986 3008213 := bbase (se 7 (by rfl) ⟨35252, by rfl⟩ : syracuseStep 3008213 = 70505) (by norm_num)
theorem B4278005 : Blo 1334986 4278005 := bbase (se 5 (by rfl) ⟨200531, by rfl⟩ : syracuseStep 4278005 = 401063) (by norm_num)
theorem B2254621 : Blo 1334986 2254621 := bbase (se 3 (by rfl) ⟨422741, by rfl⟩ : syracuseStep 2254621 = 845483) (by norm_num)
theorem B1427257 : Blo 1334986 1427257 := bbase (se 2 (by rfl) ⟨535221, by rfl⟩ : syracuseStep 1427257 = 1070443) (by norm_num)
theorem B1713997 : Blo 1334986 1713997 := bbase (se 3 (by rfl) ⟨321374, by rfl⟩ : syracuseStep 1713997 = 642749) (by norm_num)
theorem B1738577 : Blo 1334986 1738577 := bbase (se 2 (by rfl) ⟨651966, by rfl⟩ : syracuseStep 1738577 = 1303933) (by norm_num)
theorem B2254709 : Blo 1334986 2254709 := bbase (se 5 (by rfl) ⟨105689, by rfl⟩ : syracuseStep 2254709 = 211379) (by norm_num)
theorem B4507541 : Blo 1334986 4507541 := bbase (se 6 (by rfl) ⟨105645, by rfl⟩ : syracuseStep 4507541 = 211291) (by norm_num)
theorem B1902485 : Blo 1334986 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B6760421 : Blo 1334986 6760421 := bbase (se 4 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 6760421 = 1267579) (by norm_num)
theorem B1902565 : Blo 1334986 1902565 := bbase (se 4 (by rfl) ⟨178365, by rfl⟩ : syracuseStep 1902565 = 356731) (by norm_num)
theorem B3803125 : Blo 1334986 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B2254837 : Blo 1334986 2254837 := bbase (se 5 (by rfl) ⟨105695, by rfl⟩ : syracuseStep 2254837 = 211391) (by norm_num)
theorem B23152661 : Blo 1334986 23152661 := bbase (se 6 (by rfl) ⟨542640, by rfl⟩ : syracuseStep 23152661 = 1085281) (by norm_num)
theorem B12847157 : Blo 1334986 12847157 := bbase (se 5 (by rfl) ⟨602210, by rfl⟩ : syracuseStep 12847157 = 1204421) (by norm_num)
theorem B2254925 : Blo 1334986 2254925 := bbase (se 3 (by rfl) ⟨422798, by rfl⟩ : syracuseStep 2254925 = 845597) (by norm_num)
theorem B8562773 : Blo 1334986 8562773 := bbase (se 8 (by rfl) ⟨50172, by rfl⟩ : syracuseStep 8562773 = 100345) (by norm_num)
theorem B1902685 : Blo 1334986 1902685 := bbase (se 3 (by rfl) ⟨356753, by rfl⟩ : syracuseStep 1902685 = 713507) (by norm_num)
theorem B10152053 : Blo 1334986 10152053 := bbase (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) (by norm_num)
theorem B1689761 : Blo 1334986 1689761 := bbase (se 2 (by rfl) ⟨633660, by rfl⟩ : syracuseStep 1689761 = 1267321) (by norm_num)
theorem B1902781 : Blo 1334986 1902781 := bbase (se 3 (by rfl) ⟨356771, by rfl⟩ : syracuseStep 1902781 = 713543) (by norm_num)
theorem B2255053 : Blo 1334986 2255053 := bbase (se 3 (by rfl) ⟨422822, by rfl⟩ : syracuseStep 2255053 = 845645) (by norm_num)
theorem B2140373 : Blo 1334986 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B1689817 : Blo 1334986 1689817 := bbase (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) (by norm_num)
theorem B1354001 : Blo 1334986 1354001 := bbase (se 2 (by rfl) ⟨507750, by rfl⟩ : syracuseStep 1354001 = 1015501) (by norm_num)
theorem B2255141 : Blo 1334986 2255141 := bbase (se 4 (by rfl) ⟨211419, by rfl⟩ : syracuseStep 2255141 = 422839) (by norm_num)
theorem B1689913 : Blo 1334986 1689913 := bbase (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) (by norm_num)
theorem B2853181 : Blo 1334986 2853181 := bbase (se 3 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 2853181 = 1069943) (by norm_num)
theorem B4507973 : Blo 1334986 4507973 := bbase (se 4 (by rfl) ⟨422622, by rfl⟩ : syracuseStep 4507973 = 845245) (by norm_num)
theorem B7317845 : Blo 1334986 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B2140501 : Blo 1334986 2140501 := bbase (se 10 (by rfl) ⟨3135, by rfl⟩ : syracuseStep 2140501 = 6271) (by norm_num)
theorem B2255269 : Blo 1334986 2255269 := bbase (se 4 (by rfl) ⟨211431, by rfl⟩ : syracuseStep 2255269 = 422863) (by norm_num)
theorem B2853301 : Blo 1334986 2853301 := bbase (se 5 (by rfl) ⟨133748, by rfl⟩ : syracuseStep 2853301 = 267497) (by norm_num)
theorem B1690085 : Blo 1334986 1690085 := bbase (se 4 (by rfl) ⟨158445, by rfl⟩ : syracuseStep 1690085 = 316891) (by norm_num)
theorem B4573685 : Blo 1334986 4573685 := bbase (se 5 (by rfl) ⟨214391, by rfl⟩ : syracuseStep 4573685 = 428783) (by norm_num)
theorem B2255357 : Blo 1334986 2255357 := bbase (se 3 (by rfl) ⟨422879, by rfl⟩ : syracuseStep 2255357 = 845759) (by norm_num)
theorem B10144277 : Blo 1334986 10144277 := bbase (se 6 (by rfl) ⟨237756, by rfl⟩ : syracuseStep 10144277 = 475513) (by norm_num)
theorem B1690141 : Blo 1334986 1690141 := bbase (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) (by norm_num)
theorem B5073461 : Blo 1334986 5073461 := bbase (se 5 (by rfl) ⟨237818, by rfl⟩ : syracuseStep 5073461 = 475637) (by norm_num)
theorem B1690237 : Blo 1334986 1690237 := bbase (se 3 (by rfl) ⟨316919, by rfl⟩ : syracuseStep 1690237 = 633839) (by norm_num)
theorem B2255485 : Blo 1334986 2255485 := bbase (se 3 (by rfl) ⟨422903, by rfl⟩ : syracuseStep 2255485 = 845807) (by norm_num)
theorem B10283669 : Blo 1334986 10283669 := bbase (se 6 (by rfl) ⟨241023, by rfl⟩ : syracuseStep 10283669 = 482047) (by norm_num)
theorem B1501861 : Blo 1334986 1501861 := bbase (se 4 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 1501861 = 281599) (by norm_num)
theorem B1903277 : Blo 1334986 1903277 := bbase (se 3 (by rfl) ⟨356864, by rfl⟩ : syracuseStep 1903277 = 713729) (by norm_num)
theorem B2853557 : Blo 1334986 2853557 := bbase (se 5 (by rfl) ⟨133760, by rfl⟩ : syracuseStep 2853557 = 267521) (by norm_num)
theorem B1501897 : Blo 1334986 1501897 := bbase (se 2 (by rfl) ⟨563211, by rfl⟩ : syracuseStep 1501897 = 1126423) (by norm_num)
theorem B2255573 : Blo 1334986 2255573 := bbase (se 7 (by rfl) ⟨26432, by rfl⟩ : syracuseStep 2255573 = 52865) (by norm_num)
theorem B1501933 : Blo 1334986 1501933 := bbase (se 3 (by rfl) ⟨281612, by rfl⟩ : syracuseStep 1501933 = 563225) (by norm_num)
theorem B4508405 : Blo 1334986 4508405 := bbase (se 5 (by rfl) ⟨211331, by rfl⟩ : syracuseStep 4508405 = 422663) (by norm_num)
theorem B1501969 : Blo 1334986 1501969 := bbase (se 2 (by rfl) ⟨563238, by rfl⟩ : syracuseStep 1501969 = 1126477) (by norm_num)
theorem B1690409 : Blo 1334986 1690409 := bbase (se 2 (by rfl) ⟨633903, by rfl⟩ : syracuseStep 1690409 = 1267807) (by norm_num)
theorem B1502005 : Blo 1334986 1502005 := bbase (se 5 (by rfl) ⟨70406, by rfl⟩ : syracuseStep 1502005 = 140813) (by norm_num)
theorem B5073749 : Blo 1334986 5073749 := bbase (se 9 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 5073749 = 29729) (by norm_num)
theorem B2255701 : Blo 1334986 2255701 := bbase (se 9 (by rfl) ⟨6608, by rfl⟩ : syracuseStep 2255701 = 13217) (by norm_num)
theorem B1502041 : Blo 1334986 1502041 := bbase (se 2 (by rfl) ⟨563265, by rfl⟩ : syracuseStep 1502041 = 1126531) (by norm_num)
theorem B1690465 : Blo 1334986 1690465 := bbase (se 2 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 1690465 = 1267849) (by norm_num)
theorem B1502077 : Blo 1334986 1502077 := bbase (se 3 (by rfl) ⟨281639, by rfl⟩ : syracuseStep 1502077 = 563279) (by norm_num)
theorem B1502113 : Blo 1334986 1502113 := bbase (se 2 (by rfl) ⟨563292, by rfl⟩ : syracuseStep 1502113 = 1126585) (by norm_num)
theorem B2255789 : Blo 1334986 2255789 := bbase (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) (by norm_num)
theorem B1690561 : Blo 1334986 1690561 := bbase (se 2 (by rfl) ⟨633960, by rfl⟩ : syracuseStep 1690561 = 1267921) (by norm_num)
theorem B1502149 : Blo 1334986 1502149 := bbase (se 4 (by rfl) ⟨140826, by rfl⟩ : syracuseStep 1502149 = 281653) (by norm_num)
theorem B1502185 : Blo 1334986 1502185 := bbase (se 2 (by rfl) ⟨563319, by rfl⟩ : syracuseStep 1502185 = 1126639) (by norm_num)
theorem B1502221 : Blo 1334986 1502221 := bbase (se 3 (by rfl) ⟨281666, by rfl⟩ : syracuseStep 1502221 = 563333) (by norm_num)
theorem B20859925 : Blo 1334986 20859925 := bbase (se 6 (by rfl) ⟨488904, by rfl⟩ : syracuseStep 20859925 = 977809) (by norm_num)
theorem B2534429 : Blo 1334986 2534429 := bbase (se 3 (by rfl) ⟨475205, by rfl⟩ : syracuseStep 2534429 = 950411) (by norm_num)
theorem B2255917 : Blo 1334986 2255917 := bbase (se 3 (by rfl) ⟨422984, by rfl⟩ : syracuseStep 2255917 = 845969) (by norm_num)
theorem B1502257 : Blo 1334986 1502257 := bbase (se 2 (by rfl) ⟨563346, by rfl⟩ : syracuseStep 1502257 = 1126693) (by norm_num)
theorem B3427397 : Blo 1334986 3427397 := bbase (se 4 (by rfl) ⟨321318, by rfl⟩ : syracuseStep 3427397 = 642637) (by norm_num)
theorem B1502293 : Blo 1334986 1502293 := bbase (se 8 (by rfl) ⟨8802, by rfl⟩ : syracuseStep 1502293 = 17605) (by norm_num)
theorem B19262549 : Blo 1334986 19262549 := bbase (se 8 (by rfl) ⟨112866, by rfl⟩ : syracuseStep 19262549 = 225733) (by norm_num)
theorem B1690733 : Blo 1334986 1690733 := bbase (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) (by norm_num)
theorem B1502329 : Blo 1334986 1502329 := bbase (se 2 (by rfl) ⟨563373, by rfl⟩ : syracuseStep 1502329 = 1126747) (by norm_num)
theorem B2141309 : Blo 1334986 2141309 := bbase (se 3 (by rfl) ⟨401495, by rfl⟩ : syracuseStep 2141309 = 802991) (by norm_num)
theorem B2256005 : Blo 1334986 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B1502365 : Blo 1334986 1502365 := bbase (se 3 (by rfl) ⟨281693, by rfl⟩ : syracuseStep 1502365 = 563387) (by norm_num)
theorem B1690789 : Blo 1334986 1690789 := bbase (se 4 (by rfl) ⟨158511, by rfl⟩ : syracuseStep 1690789 = 317023) (by norm_num)
theorem B4508837 : Blo 1334986 4508837 := bbase (se 4 (by rfl) ⟨422703, by rfl⟩ : syracuseStep 4508837 = 845407) (by norm_num)
theorem B2534581 : Blo 1334986 2534581 := bbase (se 5 (by rfl) ⟨118808, by rfl⟩ : syracuseStep 2534581 = 237617) (by norm_num)
theorem B1502401 : Blo 1334986 1502401 := bbase (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) (by norm_num)
theorem B1502437 : Blo 1334986 1502437 := bbase (se 4 (by rfl) ⟨140853, by rfl⟩ : syracuseStep 1502437 = 281707) (by norm_num)
theorem B6761717 : Blo 1334986 6761717 := bbase (se 5 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 6761717 = 633911) (by norm_num)
theorem B1690885 : Blo 1334986 1690885 := bbase (se 4 (by rfl) ⟨158520, by rfl⟩ : syracuseStep 1690885 = 317041) (by norm_num)
theorem B2256133 : Blo 1334986 2256133 := bbase (se 4 (by rfl) ⟨211512, by rfl⟩ : syracuseStep 2256133 = 423025) (by norm_num)
theorem B1502473 : Blo 1334986 1502473 := bbase (se 2 (by rfl) ⟨563427, by rfl⟩ : syracuseStep 1502473 = 1126855) (by norm_num)
theorem B1502509 : Blo 1334986 1502509 := bbase (se 3 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 1502509 = 563441) (by norm_num)
theorem B1502545 : Blo 1334986 1502545 := bbase (se 2 (by rfl) ⟨563454, by rfl⟩ : syracuseStep 1502545 = 1126909) (by norm_num)
theorem B4812149 : Blo 1334986 4812149 := bbase (se 5 (by rfl) ⟨225569, by rfl⟩ : syracuseStep 4812149 = 451139) (by norm_num)
theorem B1502581 : Blo 1334986 1502581 := bbase (se 5 (by rfl) ⟨70433, by rfl⟩ : syracuseStep 1502581 = 140867) (by norm_num)
theorem B10833301 : Blo 1334986 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B1502617 : Blo 1334986 1502617 := bbase (se 2 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 1502617 = 1126963) (by norm_num)
theorem B1355177 : Blo 1334986 1355177 := bbase (se 2 (by rfl) ⟨508191, by rfl⟩ : syracuseStep 1355177 = 1016383) (by norm_num)
theorem B1691057 : Blo 1334986 1691057 := bbase (se 2 (by rfl) ⟨634146, by rfl⟩ : syracuseStep 1691057 = 1268293) (by norm_num)
theorem B1502653 : Blo 1334986 1502653 := bbase (se 3 (by rfl) ⟨281747, by rfl⟩ : syracuseStep 1502653 = 563495) (by norm_num)
theorem B1502689 : Blo 1334986 1502689 := bbase (se 2 (by rfl) ⟨563508, by rfl⟩ : syracuseStep 1502689 = 1127017) (by norm_num)
theorem B2534885 : Blo 1334986 2534885 := bbase (se 4 (by rfl) ⟨237645, by rfl⟩ : syracuseStep 2534885 = 475291) (by norm_num)
theorem B1691113 : Blo 1334986 1691113 := bbase (se 2 (by rfl) ⟨634167, by rfl⟩ : syracuseStep 1691113 = 1268335) (by norm_num)
theorem B1502725 : Blo 1334986 1502725 := bbase (se 4 (by rfl) ⟨140880, by rfl⟩ : syracuseStep 1502725 = 281761) (by norm_num)
theorem B1502761 : Blo 1334986 1502761 := bbase (se 2 (by rfl) ⟨563535, by rfl⟩ : syracuseStep 1502761 = 1127071) (by norm_num)
theorem B2854445 : Blo 1334986 2854445 := bbase (se 3 (by rfl) ⟨535208, by rfl⟩ : syracuseStep 2854445 = 1070417) (by norm_num)
theorem B2002493 : Blo 1334986 2002493 := bbase (se 3 (by rfl) ⟨375467, by rfl⟩ : syracuseStep 2002493 = 750935) (by norm_num)
theorem B1691209 : Blo 1334986 1691209 := bbase (se 2 (by rfl) ⟨634203, by rfl⟩ : syracuseStep 1691209 = 1268407) (by norm_num)
theorem B1502797 : Blo 1334986 1502797 := bbase (se 3 (by rfl) ⟨281774, by rfl⟩ : syracuseStep 1502797 = 563549) (by norm_num)
theorem B2002517 : Blo 1334986 2002517 := bbase (se 8 (by rfl) ⟨11733, by rfl⟩ : syracuseStep 2002517 = 23467) (by norm_num)
theorem B4509269 : Blo 1334986 4509269 := bbase (se 8 (by rfl) ⟨26421, by rfl⟩ : syracuseStep 4509269 = 52843) (by norm_num)
theorem B2002541 : Blo 1334986 2002541 := bbase (se 3 (by rfl) ⟨375476, by rfl⟩ : syracuseStep 2002541 = 750953) (by norm_num)
theorem B1502833 : Blo 1334986 1502833 := bbase (se 2 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 1502833 = 1127125) (by norm_num)
theorem B4279925 : Blo 1334986 4279925 := bbase (se 5 (by rfl) ⟨200621, by rfl⟩ : syracuseStep 4279925 = 401243) (by norm_num)
theorem B2002565 : Blo 1334986 2002565 := bbase (se 4 (by rfl) ⟨187740, by rfl⟩ : syracuseStep 2002565 = 375481) (by norm_num)
theorem B1625737 : Blo 1334986 1625737 := bbase (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) (by norm_num)
theorem B1502869 : Blo 1334986 1502869 := bbase (se 6 (by rfl) ⟨35223, by rfl⟩ : syracuseStep 1502869 = 70447) (by norm_num)
theorem B2002589 : Blo 1334986 2002589 := bbase (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) (by norm_num)
theorem B2002613 : Blo 1334986 2002613 := bbase (se 5 (by rfl) ⟨93872, by rfl⟩ : syracuseStep 2002613 = 187745) (by norm_num)
theorem B1502905 : Blo 1334986 1502905 := bbase (se 2 (by rfl) ⟨563589, by rfl⟩ : syracuseStep 1502905 = 1127179) (by norm_num)
theorem B2002637 : Blo 1334986 2002637 := bbase (se 3 (by rfl) ⟨375494, by rfl⟩ : syracuseStep 2002637 = 750989) (by norm_num)
theorem B1543897 : Blo 1334986 1543897 := bbase (se 2 (by rfl) ⟨578961, by rfl⟩ : syracuseStep 1543897 = 1157923) (by norm_num)
theorem B1502941 : Blo 1334986 1502941 := bbase (se 3 (by rfl) ⟨281801, by rfl⟩ : syracuseStep 1502941 = 563603) (by norm_num)
theorem B2002661 : Blo 1334986 2002661 := bbase (se 4 (by rfl) ⟨187749, by rfl⟩ : syracuseStep 2002661 = 375499) (by norm_num)
theorem B1691381 : Blo 1334986 1691381 := bbase (se 5 (by rfl) ⟨79283, by rfl⟩ : syracuseStep 1691381 = 158567) (by norm_num)
theorem B2002685 : Blo 1334986 2002685 := bbase (se 3 (by rfl) ⟨375503, by rfl⟩ : syracuseStep 2002685 = 751007) (by norm_num)
theorem B1502977 : Blo 1334986 1502977 := bbase (se 2 (by rfl) ⟨563616, by rfl⟩ : syracuseStep 1502977 = 1127233) (by norm_num)
theorem B2002709 : Blo 1334986 2002709 := bbase (se 6 (by rfl) ⟨46938, by rfl⟩ : syracuseStep 2002709 = 93877) (by norm_num)
theorem B14634773 : Blo 1334986 14634773 := bbase (se 6 (by rfl) ⟨343002, by rfl⟩ : syracuseStep 14634773 = 686005) (by norm_num)
theorem B2854685 : Blo 1334986 2854685 := bbase (se 3 (by rfl) ⟨535253, by rfl⟩ : syracuseStep 2854685 = 1070507) (by norm_num)
theorem B1503013 : Blo 1334986 1503013 := bbase (se 4 (by rfl) ⟨140907, by rfl⟩ : syracuseStep 1503013 = 281815) (by norm_num)
theorem B2002733 : Blo 1334986 2002733 := bbase (se 3 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 2002733 = 751025) (by norm_num)
theorem B1691437 : Blo 1334986 1691437 := bbase (se 3 (by rfl) ⟨317144, by rfl⟩ : syracuseStep 1691437 = 634289) (by norm_num)
theorem B2002757 : Blo 1334986 2002757 := bbase (se 4 (by rfl) ⟨187758, by rfl⟩ : syracuseStep 2002757 = 375517) (by norm_num)
theorem B1503049 : Blo 1334986 1503049 := bbase (se 2 (by rfl) ⟨563643, by rfl⟩ : syracuseStep 1503049 = 1127287) (by norm_num)
theorem B2002781 : Blo 1334986 2002781 := bbase (se 3 (by rfl) ⟨375521, by rfl⟩ : syracuseStep 2002781 = 751043) (by norm_num)
theorem B1503085 : Blo 1334986 1503085 := bbase (se 3 (by rfl) ⟨281828, by rfl⟩ : syracuseStep 1503085 = 563657) (by norm_num)
theorem B2002805 : Blo 1334986 2002805 := bbase (se 5 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 2002805 = 187763) (by norm_num)
theorem B2002829 : Blo 1334986 2002829 := bbase (se 3 (by rfl) ⟨375530, by rfl⟩ : syracuseStep 2002829 = 751061) (by norm_num)
theorem B1691533 : Blo 1334986 1691533 := bbase (se 3 (by rfl) ⟨317162, by rfl⟩ : syracuseStep 1691533 = 634325) (by norm_num)
theorem B1503121 : Blo 1334986 1503121 := bbase (se 2 (by rfl) ⟨563670, by rfl⟩ : syracuseStep 1503121 = 1127341) (by norm_num)
theorem B2002853 : Blo 1334986 2002853 := bbase (se 4 (by rfl) ⟨187767, by rfl⟩ : syracuseStep 2002853 = 375535) (by norm_num)
theorem B1503157 : Blo 1334986 1503157 := bbase (se 5 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 1503157 = 140921) (by norm_num)
theorem B2002877 : Blo 1334986 2002877 := bbase (se 3 (by rfl) ⟨375539, by rfl⟩ : syracuseStep 2002877 = 751079) (by norm_num)
theorem B2002901 : Blo 1334986 2002901 := bbase (se 7 (by rfl) ⟨23471, by rfl⟩ : syracuseStep 2002901 = 46943) (by norm_num)
theorem B1503193 : Blo 1334986 1503193 := bbase (se 2 (by rfl) ⟨563697, by rfl⟩ : syracuseStep 1503193 = 1127395) (by norm_num)
theorem B2002925 : Blo 1334986 2002925 := bbase (se 3 (by rfl) ⟨375548, by rfl⟩ : syracuseStep 2002925 = 751097) (by norm_num)
theorem B5074933 : Blo 1334986 5074933 := bbase (se 5 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 5074933 = 475775) (by norm_num)
theorem B1929205 : Blo 1334986 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B1503229 : Blo 1334986 1503229 := bbase (se 3 (by rfl) ⟨281855, by rfl⟩ : syracuseStep 1503229 = 563711) (by norm_num)
theorem B2002949 : Blo 1334986 2002949 := bbase (se 4 (by rfl) ⟨187776, by rfl⟩ : syracuseStep 2002949 = 375553) (by norm_num)
theorem B4509701 : Blo 1334986 4509701 := bbase (se 4 (by rfl) ⟨422784, by rfl⟩ : syracuseStep 4509701 = 845569) (by norm_num)
theorem B3379229 : Blo 1334986 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B2002973 : Blo 1334986 2002973 := bbase (se 3 (by rfl) ⟨375557, by rfl⟩ : syracuseStep 2002973 = 751115) (by norm_num)
theorem B1503265 : Blo 1334986 1503265 := bbase (se 2 (by rfl) ⟨563724, by rfl⟩ : syracuseStep 1503265 = 1127449) (by norm_num)
theorem B2002997 : Blo 1334986 2002997 := bbase (se 5 (by rfl) ⟨93890, by rfl⟩ : syracuseStep 2002997 = 187781) (by norm_num)
theorem B1691705 : Blo 1334986 1691705 := bbase (se 2 (by rfl) ⟨634389, by rfl⟩ : syracuseStep 1691705 = 1268779) (by norm_num)
theorem B1503301 : Blo 1334986 1503301 := bbase (se 4 (by rfl) ⟨140934, by rfl⟩ : syracuseStep 1503301 = 281869) (by norm_num)
theorem B2003021 : Blo 1334986 2003021 := bbase (se 3 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 2003021 = 751133) (by norm_num)
theorem B2003045 : Blo 1334986 2003045 := bbase (se 4 (by rfl) ⟨187785, by rfl⟩ : syracuseStep 2003045 = 375571) (by norm_num)
theorem B1503337 : Blo 1334986 1503337 := bbase (se 2 (by rfl) ⟨563751, by rfl⟩ : syracuseStep 1503337 = 1127503) (by norm_num)
theorem B1691761 : Blo 1334986 1691761 := bbase (se 2 (by rfl) ⟨634410, by rfl⟩ : syracuseStep 1691761 = 1268821) (by norm_num)
theorem B2003069 : Blo 1334986 2003069 := bbase (se 3 (by rfl) ⟨375575, by rfl⟩ : syracuseStep 2003069 = 751151) (by norm_num)
theorem B1503373 : Blo 1334986 1503373 := bbase (se 3 (by rfl) ⟨281882, by rfl⟩ : syracuseStep 1503373 = 563765) (by norm_num)
theorem B2003093 : Blo 1334986 2003093 := bbase (se 6 (by rfl) ⟨46947, by rfl⟩ : syracuseStep 2003093 = 93895) (by norm_num)
theorem B2003117 : Blo 1334986 2003117 := bbase (se 3 (by rfl) ⟨375584, by rfl⟩ : syracuseStep 2003117 = 751169) (by norm_num)
theorem B1503409 : Blo 1334986 1503409 := bbase (se 2 (by rfl) ⟨563778, by rfl⟩ : syracuseStep 1503409 = 1127557) (by norm_num)
theorem B2003141 : Blo 1334986 2003141 := bbase (se 4 (by rfl) ⟨187794, by rfl⟩ : syracuseStep 2003141 = 375589) (by norm_num)
theorem B1691857 : Blo 1334986 1691857 := bbase (se 2 (by rfl) ⟨634446, by rfl⟩ : syracuseStep 1691857 = 1268893) (by norm_num)
theorem B1626325 : Blo 1334986 1626325 := bbase (se 7 (by rfl) ⟨19058, by rfl⟩ : syracuseStep 1626325 = 38117) (by norm_num)
theorem B2535637 : Blo 1334986 2535637 := bbase (se 7 (by rfl) ⟨29714, by rfl⟩ : syracuseStep 2535637 = 59429) (by norm_num)
theorem B1503445 : Blo 1334986 1503445 := bbase (se 7 (by rfl) ⟨17618, by rfl⟩ : syracuseStep 1503445 = 35237) (by norm_num)
theorem B3379421 : Blo 1334986 3379421 := bbase (se 3 (by rfl) ⟨633641, by rfl⟩ : syracuseStep 3379421 = 1267283) (by norm_num)
theorem B2003165 : Blo 1334986 2003165 := bbase (se 3 (by rfl) ⟨375593, by rfl⟩ : syracuseStep 2003165 = 751187) (by norm_num)
theorem B2003189 : Blo 1334986 2003189 := bbase (se 5 (by rfl) ⟨93899, by rfl⟩ : syracuseStep 2003189 = 187799) (by norm_num)
theorem B1503481 : Blo 1334986 1503481 := bbase (se 2 (by rfl) ⟨563805, by rfl⟩ : syracuseStep 1503481 = 1127611) (by norm_num)
theorem B2003213 : Blo 1334986 2003213 := bbase (se 3 (by rfl) ⟨375602, by rfl⟩ : syracuseStep 2003213 = 751205) (by norm_num)
theorem B2855189 : Blo 1334986 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B1503517 : Blo 1334986 1503517 := bbase (se 3 (by rfl) ⟨281909, by rfl⟩ : syracuseStep 1503517 = 563819) (by norm_num)
theorem B2855197 : Blo 1334986 2855197 := bbase (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) (by norm_num)
theorem B2003237 : Blo 1334986 2003237 := bbase (se 4 (by rfl) ⟨187803, by rfl⟩ : syracuseStep 2003237 = 375607) (by norm_num)
theorem B5075237 : Blo 1334986 5075237 := bbase (se 4 (by rfl) ⟨475803, by rfl⟩ : syracuseStep 5075237 = 951607) (by norm_num)
theorem B2003261 : Blo 1334986 2003261 := bbase (se 3 (by rfl) ⟨375611, by rfl⟩ : syracuseStep 2003261 = 751223) (by norm_num)
theorem B1503553 : Blo 1334986 1503553 := bbase (se 2 (by rfl) ⟨563832, by rfl⟩ : syracuseStep 1503553 = 1127665) (by norm_num)
theorem B2003285 : Blo 1334986 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B22819157 : Blo 1334986 22819157 := bbase (se 10 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 22819157 = 66853) (by norm_num)
theorem B2535781 : Blo 1334986 2535781 := bbase (se 4 (by rfl) ⟨237729, by rfl⟩ : syracuseStep 2535781 = 475459) (by norm_num)
theorem B1503589 : Blo 1334986 1503589 := bbase (se 4 (by rfl) ⟨140961, by rfl⟩ : syracuseStep 1503589 = 281923) (by norm_num)
theorem B2003309 : Blo 1334986 2003309 := bbase (se 3 (by rfl) ⟨375620, by rfl⟩ : syracuseStep 2003309 = 751241) (by norm_num)
theorem B1692029 : Blo 1334986 1692029 := bbase (se 3 (by rfl) ⟨317255, by rfl⟩ : syracuseStep 1692029 = 634511) (by norm_num)
theorem B2003333 : Blo 1334986 2003333 := bbase (se 4 (by rfl) ⟨187812, by rfl⟩ : syracuseStep 2003333 = 375625) (by norm_num)
theorem B1503625 : Blo 1334986 1503625 := bbase (se 2 (by rfl) ⟨563859, by rfl⟩ : syracuseStep 1503625 = 1127719) (by norm_num)
theorem B2003357 : Blo 1334986 2003357 := bbase (se 3 (by rfl) ⟨375629, by rfl⟩ : syracuseStep 2003357 = 751259) (by norm_num)
theorem B1503661 : Blo 1334986 1503661 := bbase (se 3 (by rfl) ⟨281936, by rfl⟩ : syracuseStep 1503661 = 563873) (by norm_num)
theorem B2003381 : Blo 1334986 2003381 := bbase (se 5 (by rfl) ⟨93908, by rfl⟩ : syracuseStep 2003381 = 187817) (by norm_num)
theorem B4510133 : Blo 1334986 4510133 := bbase (se 5 (by rfl) ⟨211412, by rfl⟩ : syracuseStep 4510133 = 422825) (by norm_num)
theorem B1692085 : Blo 1334986 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B2003405 : Blo 1334986 2003405 := bbase (se 3 (by rfl) ⟨375638, by rfl⟩ : syracuseStep 2003405 = 751277) (by norm_num)
theorem B1503697 : Blo 1334986 1503697 := bbase (se 2 (by rfl) ⟨563886, by rfl⟩ : syracuseStep 1503697 = 1127773) (by norm_num)
theorem B2003429 : Blo 1334986 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B1503733 : Blo 1334986 1503733 := bbase (se 5 (by rfl) ⟨70487, by rfl⟩ : syracuseStep 1503733 = 140975) (by norm_num)
theorem B2003453 : Blo 1334986 2003453 := bbase (se 3 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 2003453 = 751295) (by norm_num)
theorem B2535941 : Blo 1334986 2535941 := bbase (se 4 (by rfl) ⟨237744, by rfl⟩ : syracuseStep 2535941 = 475489) (by norm_num)
theorem B6763013 : Blo 1334986 6763013 := bbase (se 4 (by rfl) ⟨634032, by rfl⟩ : syracuseStep 6763013 = 1268065) (by norm_num)
theorem B2003477 : Blo 1334986 2003477 := bbase (se 6 (by rfl) ⟨46956, by rfl⟩ : syracuseStep 2003477 = 93913) (by norm_num)
theorem B5419541 : Blo 1334986 5419541 := bbase (se 6 (by rfl) ⟨127020, by rfl⟩ : syracuseStep 5419541 = 254041) (by norm_num)
theorem B1503769 : Blo 1334986 1503769 := bbase (se 2 (by rfl) ⟨563913, by rfl⟩ : syracuseStep 1503769 = 1127827) (by norm_num)
theorem B2003501 : Blo 1334986 2003501 := bbase (se 3 (by rfl) ⟨375656, by rfl⟩ : syracuseStep 2003501 = 751313) (by norm_num)
theorem B3379765 : Blo 1334986 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B1503805 : Blo 1334986 1503805 := bbase (se 3 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 1503805 = 563927) (by norm_num)
theorem B2003525 : Blo 1334986 2003525 := bbase (se 4 (by rfl) ⟨187830, by rfl⟩ : syracuseStep 2003525 = 375661) (by norm_num)
theorem B2003549 : Blo 1334986 2003549 := bbase (se 3 (by rfl) ⟨375665, by rfl⟩ : syracuseStep 2003549 = 751331) (by norm_num)
theorem B1503841 : Blo 1334986 1503841 := bbase (se 2 (by rfl) ⟨563940, by rfl⟩ : syracuseStep 1503841 = 1127881) (by norm_num)
theorem B2003573 : Blo 1334986 2003573 := bbase (se 5 (by rfl) ⟨93917, by rfl⟩ : syracuseStep 2003573 = 187835) (by norm_num)
theorem B1503877 : Blo 1334986 1503877 := bbase (se 4 (by rfl) ⟨140988, by rfl⟩ : syracuseStep 1503877 = 281977) (by norm_num)
theorem B2003597 : Blo 1334986 2003597 := bbase (se 3 (by rfl) ⟨375674, by rfl⟩ : syracuseStep 2003597 = 751349) (by norm_num)
theorem B2536085 : Blo 1334986 2536085 := bbase (se 6 (by rfl) ⟨59439, by rfl⟩ : syracuseStep 2536085 = 118879) (by norm_num)
theorem B5419669 : Blo 1334986 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B3379877 : Blo 1334986 3379877 := bbase (se 4 (by rfl) ⟨316863, by rfl⟩ : syracuseStep 3379877 = 633727) (by norm_num)
theorem B2003621 : Blo 1334986 2003621 := bbase (se 4 (by rfl) ⟨187839, by rfl⟩ : syracuseStep 2003621 = 375679) (by norm_num)
theorem B1503913 : Blo 1334986 1503913 := bbase (se 2 (by rfl) ⟨563967, by rfl⟩ : syracuseStep 1503913 = 1127935) (by norm_num)
theorem B3207869 : Blo 1334986 3207869 := bbase (se 3 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 3207869 = 1202951) (by norm_num)
theorem B2003645 : Blo 1334986 2003645 := bbase (se 3 (by rfl) ⟨375683, by rfl⟩ : syracuseStep 2003645 = 751367) (by norm_num)
theorem B1503949 : Blo 1334986 1503949 := bbase (se 3 (by rfl) ⟨281990, by rfl⟩ : syracuseStep 1503949 = 563981) (by norm_num)
theorem B2003669 : Blo 1334986 2003669 := bbase (se 7 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 2003669 = 46961) (by norm_num)
theorem B2003693 : Blo 1334986 2003693 := bbase (se 3 (by rfl) ⟨375692, by rfl⟩ : syracuseStep 2003693 = 751385) (by norm_num)
theorem B1503985 : Blo 1334986 1503985 := bbase (se 2 (by rfl) ⟨563994, by rfl⟩ : syracuseStep 1503985 = 1127989) (by norm_num)
theorem B2003717 : Blo 1334986 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B3805973 : Blo 1334986 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B1504021 : Blo 1334986 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B2003741 : Blo 1334986 2003741 := bbase (se 3 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 2003741 = 751403) (by norm_num)
theorem B2003765 : Blo 1334986 2003765 := bbase (se 5 (by rfl) ⟨93926, by rfl⟩ : syracuseStep 2003765 = 187853) (by norm_num)
theorem B1504057 : Blo 1334986 1504057 := bbase (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) (by norm_num)
theorem B2003789 : Blo 1334986 2003789 := bbase (se 3 (by rfl) ⟨375710, by rfl⟩ : syracuseStep 2003789 = 751421) (by norm_num)
theorem B1504093 : Blo 1334986 1504093 := bbase (se 3 (by rfl) ⟨282017, by rfl⟩ : syracuseStep 1504093 = 564035) (by norm_num)
theorem B3380069 : Blo 1334986 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B2003813 : Blo 1334986 2003813 := bbase (se 4 (by rfl) ⟨187857, by rfl⟩ : syracuseStep 2003813 = 375715) (by norm_num)
theorem B4510565 : Blo 1334986 4510565 := bbase (se 4 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 4510565 = 845731) (by norm_num)
theorem B2003837 : Blo 1334986 2003837 := bbase (se 3 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 2003837 = 751439) (by norm_num)
theorem B2003861 : Blo 1334986 2003861 := bbase (se 6 (by rfl) ⟨46965, by rfl⟩ : syracuseStep 2003861 = 93931) (by norm_num)
theorem B2003885 : Blo 1334986 2003885 := bbase (se 3 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 2003885 = 751457) (by norm_num)
theorem B6173621 : Blo 1334986 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B2536373 : Blo 1334986 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B2003909 : Blo 1334986 2003909 := bbase (se 4 (by rfl) ⟨187866, by rfl⟩ : syracuseStep 2003909 = 375733) (by norm_num)
theorem B2003933 : Blo 1334986 2003933 := bbase (se 3 (by rfl) ⟨375737, by rfl⟩ : syracuseStep 2003933 = 751475) (by norm_num)
theorem B2003957 : Blo 1334986 2003957 := bbase (se 5 (by rfl) ⟨93935, by rfl⟩ : syracuseStep 2003957 = 187871) (by norm_num)
theorem B4281349 : Blo 1334986 4281349 := bbase (se 4 (by rfl) ⟨401376, by rfl⟩ : syracuseStep 4281349 = 802753) (by norm_num)
theorem B2003981 : Blo 1334986 2003981 := bbase (se 3 (by rfl) ⟨375746, by rfl⟩ : syracuseStep 2003981 = 751493) (by norm_num)
theorem B5706773 : Blo 1334986 5706773 := bbase (se 6 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 5706773 = 267505) (by norm_num)
theorem B2004005 : Blo 1334986 2004005 := bbase (se 4 (by rfl) ⟨187875, by rfl⟩ : syracuseStep 2004005 = 375751) (by norm_num)
theorem B2004029 : Blo 1334986 2004029 := bbase (se 3 (by rfl) ⟨375755, by rfl⟩ : syracuseStep 2004029 = 751511) (by norm_num)
theorem B2536525 : Blo 1334986 2536525 := bbase (se 3 (by rfl) ⟨475598, by rfl⟩ : syracuseStep 2536525 = 951197) (by norm_num)
theorem B2004053 : Blo 1334986 2004053 := bbase (se 8 (by rfl) ⟨11742, by rfl⟩ : syracuseStep 2004053 = 23485) (by norm_num)
theorem B2004077 : Blo 1334986 2004077 := bbase (se 3 (by rfl) ⟨375764, by rfl⟩ : syracuseStep 2004077 = 751529) (by norm_num)
theorem B2004101 : Blo 1334986 2004101 := bbase (se 4 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 2004101 = 375769) (by norm_num)
theorem B2004125 : Blo 1334986 2004125 := bbase (se 3 (by rfl) ⟨375773, by rfl⟩ : syracuseStep 2004125 = 751547) (by norm_num)
theorem B3429533 : Blo 1334986 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B2004149 : Blo 1334986 2004149 := bbase (se 5 (by rfl) ⟨93944, by rfl⟩ : syracuseStep 2004149 = 187889) (by norm_num)
theorem B3380413 : Blo 1334986 3380413 := bbase (se 3 (by rfl) ⟨633827, by rfl⟩ : syracuseStep 3380413 = 1267655) (by norm_num)
theorem B1627333 : Blo 1334986 1627333 := bbase (se 4 (by rfl) ⟨152562, by rfl⟩ : syracuseStep 1627333 = 305125) (by norm_num)
theorem B2004173 : Blo 1334986 2004173 := bbase (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) (by norm_num)
theorem B2004197 : Blo 1334986 2004197 := bbase (se 4 (by rfl) ⟨187893, by rfl⟩ : syracuseStep 2004197 = 375787) (by norm_num)
theorem B2004221 : Blo 1334986 2004221 := bbase (se 3 (by rfl) ⟨375791, by rfl⟩ : syracuseStep 2004221 = 751583) (by norm_num)
theorem B3855637 : Blo 1334986 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B2004245 : Blo 1334986 2004245 := bbase (se 6 (by rfl) ⟨46974, by rfl⟩ : syracuseStep 2004245 = 93949) (by norm_num)
theorem B4510997 : Blo 1334986 4510997 := bbase (se 6 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 4510997 = 211453) (by norm_num)
theorem B3380525 : Blo 1334986 3380525 := bbase (se 3 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 3380525 = 1267697) (by norm_num)
theorem B2004269 : Blo 1334986 2004269 := bbase (se 3 (by rfl) ⟨375800, by rfl⟩ : syracuseStep 2004269 = 751601) (by norm_num)
theorem B2004293 : Blo 1334986 2004293 := bbase (se 4 (by rfl) ⟨187902, by rfl⟩ : syracuseStep 2004293 = 375805) (by norm_num)
theorem B2004317 : Blo 1334986 2004317 := bbase (se 3 (by rfl) ⟨375809, by rfl⟩ : syracuseStep 2004317 = 751619) (by norm_num)
theorem B3003749 : Blo 1334986 3003749 := bbase (se 4 (by rfl) ⟨281601, by rfl⟩ : syracuseStep 3003749 = 563203) (by norm_num)
theorem B2004341 : Blo 1334986 2004341 := bbase (se 5 (by rfl) ⟨93953, by rfl⟩ : syracuseStep 2004341 = 187907) (by norm_num)
theorem B2536829 : Blo 1334986 2536829 := bbase (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) (by norm_num)
theorem B2004365 : Blo 1334986 2004365 := bbase (se 3 (by rfl) ⟨375818, by rfl⟩ : syracuseStep 2004365 = 751637) (by norm_num)
theorem B2004389 : Blo 1334986 2004389 := bbase (se 4 (by rfl) ⟨187911, by rfl⟩ : syracuseStep 2004389 = 375823) (by norm_num)
theorem B3003821 : Blo 1334986 3003821 := bbase (se 3 (by rfl) ⟨563216, by rfl⟩ : syracuseStep 3003821 = 1126433) (by norm_num)
theorem B3208637 : Blo 1334986 3208637 := bbase (se 3 (by rfl) ⟨601619, by rfl⟩ : syracuseStep 3208637 = 1203239) (by norm_num)
theorem B2004413 : Blo 1334986 2004413 := bbase (se 3 (by rfl) ⟨375827, by rfl⟩ : syracuseStep 2004413 = 751655) (by norm_num)
theorem B4281797 : Blo 1334986 4281797 := bbase (se 4 (by rfl) ⟨401418, by rfl⟩ : syracuseStep 4281797 = 802837) (by norm_num)
theorem B2004437 : Blo 1334986 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B3380717 : Blo 1334986 3380717 := bbase (se 3 (by rfl) ⟨633884, by rfl⟩ : syracuseStep 3380717 = 1267769) (by norm_num)
theorem B2004461 : Blo 1334986 2004461 := bbase (se 3 (by rfl) ⟨375836, by rfl⟩ : syracuseStep 2004461 = 751673) (by norm_num)
theorem B3003893 : Blo 1334986 3003893 := bbase (se 5 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 3003893 = 281615) (by norm_num)
theorem B2004485 : Blo 1334986 2004485 := bbase (se 4 (by rfl) ⟨187920, by rfl⟩ : syracuseStep 2004485 = 375841) (by norm_num)
theorem B2004509 : Blo 1334986 2004509 := bbase (se 3 (by rfl) ⟨375845, by rfl⟩ : syracuseStep 2004509 = 751691) (by norm_num)
theorem B4339253 : Blo 1334986 4339253 := bbase (se 5 (by rfl) ⟨203402, by rfl⟩ : syracuseStep 4339253 = 406805) (by norm_num)
theorem B2004533 : Blo 1334986 2004533 := bbase (se 5 (by rfl) ⟨93962, by rfl⟩ : syracuseStep 2004533 = 187925) (by norm_num)
theorem B3003965 : Blo 1334986 3003965 := bbase (se 3 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 3003965 = 1126487) (by norm_num)
theorem B2004557 : Blo 1334986 2004557 := bbase (se 3 (by rfl) ⟨375854, by rfl⟩ : syracuseStep 2004557 = 751709) (by norm_num)
theorem B2004581 : Blo 1334986 2004581 := bbase (se 4 (by rfl) ⟨187929, by rfl⟩ : syracuseStep 2004581 = 375859) (by norm_num)
theorem B2004605 : Blo 1334986 2004605 := bbase (se 3 (by rfl) ⟨375863, by rfl⟩ : syracuseStep 2004605 = 751727) (by norm_num)
theorem B3004037 : Blo 1334986 3004037 := bbase (se 4 (by rfl) ⟨281628, by rfl⟩ : syracuseStep 3004037 = 563257) (by norm_num)
theorem B2004629 : Blo 1334986 2004629 := bbase (se 6 (by rfl) ⟨46983, by rfl⟩ : syracuseStep 2004629 = 93967) (by norm_num)
theorem B2004653 : Blo 1334986 2004653 := bbase (se 3 (by rfl) ⟨375872, by rfl⟩ : syracuseStep 2004653 = 751745) (by norm_num)
theorem B2004677 : Blo 1334986 2004677 := bbase (se 4 (by rfl) ⟨187938, by rfl⟩ : syracuseStep 2004677 = 375877) (by norm_num)
theorem B4511429 : Blo 1334986 4511429 := bbase (se 4 (by rfl) ⟨422946, by rfl⟩ : syracuseStep 4511429 = 845893) (by norm_num)
theorem B3004109 : Blo 1334986 3004109 := bbase (se 3 (by rfl) ⟨563270, by rfl⟩ : syracuseStep 3004109 = 1126541) (by norm_num)
theorem B2004701 : Blo 1334986 2004701 := bbase (se 3 (by rfl) ⟨375881, by rfl⟩ : syracuseStep 2004701 = 751763) (by norm_num)
theorem B2004725 : Blo 1334986 2004725 := bbase (se 5 (by rfl) ⟨93971, by rfl⟩ : syracuseStep 2004725 = 187943) (by norm_num)
theorem B2004749 : Blo 1334986 2004749 := bbase (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) (by norm_num)
theorem B3004181 : Blo 1334986 3004181 := bbase (se 6 (by rfl) ⟨70410, by rfl⟩ : syracuseStep 3004181 = 140821) (by norm_num)
theorem B6764309 : Blo 1334986 6764309 := bbase (se 6 (by rfl) ⟨158538, by rfl⟩ : syracuseStep 6764309 = 317077) (by norm_num)
theorem B2004773 : Blo 1334986 2004773 := bbase (se 4 (by rfl) ⟨187947, by rfl⟩ : syracuseStep 2004773 = 375895) (by norm_num)
theorem B2004797 : Blo 1334986 2004797 := bbase (se 3 (by rfl) ⟨375899, by rfl⟩ : syracuseStep 2004797 = 751799) (by norm_num)
theorem B3381061 : Blo 1334986 3381061 := bbase (se 4 (by rfl) ⟨316974, by rfl⟩ : syracuseStep 3381061 = 633949) (by norm_num)
theorem B2004821 : Blo 1334986 2004821 := bbase (se 9 (by rfl) ⟨5873, by rfl⟩ : syracuseStep 2004821 = 11747) (by norm_num)
theorem B3004253 : Blo 1334986 3004253 := bbase (se 3 (by rfl) ⟨563297, by rfl⟩ : syracuseStep 3004253 = 1126595) (by norm_num)
theorem B4061029 : Blo 1334986 4061029 := bbase (se 4 (by rfl) ⟨380721, by rfl⟩ : syracuseStep 4061029 = 761443) (by norm_num)
theorem B2004845 : Blo 1334986 2004845 := bbase (se 3 (by rfl) ⟨375908, by rfl⟩ : syracuseStep 2004845 = 751817) (by norm_num)
theorem B2004869 : Blo 1334986 2004869 := bbase (se 4 (by rfl) ⟨187956, by rfl⟩ : syracuseStep 2004869 = 375913) (by norm_num)
theorem B2004893 : Blo 1334986 2004893 := bbase (se 3 (by rfl) ⟨375917, by rfl⟩ : syracuseStep 2004893 = 751835) (by norm_num)
theorem B3004325 : Blo 1334986 3004325 := bbase (se 4 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 3004325 = 563311) (by norm_num)
theorem B3381173 : Blo 1334986 3381173 := bbase (se 5 (by rfl) ⟨158492, by rfl⟩ : syracuseStep 3381173 = 316985) (by norm_num)
theorem B2004917 : Blo 1334986 2004917 := bbase (se 5 (by rfl) ⟨93980, by rfl⟩ : syracuseStep 2004917 = 187961) (by norm_num)
theorem B3807157 : Blo 1334986 3807157 := bbase (se 5 (by rfl) ⟨178460, by rfl⟩ : syracuseStep 3807157 = 356921) (by norm_num)
theorem B2004941 : Blo 1334986 2004941 := bbase (se 3 (by rfl) ⟨375926, by rfl⟩ : syracuseStep 2004941 = 751853) (by norm_num)
theorem B2004965 : Blo 1334986 2004965 := bbase (se 4 (by rfl) ⟨187965, by rfl⟩ : syracuseStep 2004965 = 375931) (by norm_num)
theorem B3004397 : Blo 1334986 3004397 := bbase (se 3 (by rfl) ⟨563324, by rfl⟩ : syracuseStep 3004397 = 1126649) (by norm_num)
theorem B2316269 : Blo 1334986 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B6510581 : Blo 1334986 6510581 := bbase (se 5 (by rfl) ⟨305183, by rfl⟩ : syracuseStep 6510581 = 610367) (by norm_num)
theorem B2004989 : Blo 1334986 2004989 := bbase (se 3 (by rfl) ⟨375935, by rfl⟩ : syracuseStep 2004989 = 751871) (by norm_num)
theorem B6420485 : Blo 1334986 6420485 := bbase (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) (by norm_num)
theorem B2005013 : Blo 1334986 2005013 := bbase (se 6 (by rfl) ⟨46992, by rfl⟩ : syracuseStep 2005013 = 93985) (by norm_num)
theorem B2005037 : Blo 1334986 2005037 := bbase (se 3 (by rfl) ⟨375944, by rfl⟩ : syracuseStep 2005037 = 751889) (by norm_num)
theorem B3004469 : Blo 1334986 3004469 := bbase (se 5 (by rfl) ⟨140834, by rfl⟩ : syracuseStep 3004469 = 281669) (by norm_num)
theorem B2005061 : Blo 1334986 2005061 := bbase (se 4 (by rfl) ⟨187974, by rfl⟩ : syracuseStep 2005061 = 375949) (by norm_num)
theorem B1980493 : Blo 1334986 1980493 := bbase (se 3 (by rfl) ⟨371342, by rfl⟩ : syracuseStep 1980493 = 742685) (by norm_num)
theorem B2005085 : Blo 1334986 2005085 := bbase (se 3 (by rfl) ⟨375953, by rfl⟩ : syracuseStep 2005085 = 751907) (by norm_num)
theorem B2537581 : Blo 1334986 2537581 := bbase (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) (by norm_num)
theorem B3381365 : Blo 1334986 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B7608437 : Blo 1334986 7608437 := bbase (se 5 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 7608437 = 713291) (by norm_num)
theorem B2005109 : Blo 1334986 2005109 := bbase (se 5 (by rfl) ⟨93989, by rfl⟩ : syracuseStep 2005109 = 187979) (by norm_num)
theorem B4511861 : Blo 1334986 4511861 := bbase (se 5 (by rfl) ⟨211493, by rfl⟩ : syracuseStep 4511861 = 422987) (by norm_num)
theorem B3004541 : Blo 1334986 3004541 := bbase (se 3 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 3004541 = 1126703) (by norm_num)
theorem B2005133 : Blo 1334986 2005133 := bbase (se 3 (by rfl) ⟨375962, by rfl⟩ : syracuseStep 2005133 = 751925) (by norm_num)
theorem B2005157 : Blo 1334986 2005157 := bbase (se 4 (by rfl) ⟨187983, by rfl⟩ : syracuseStep 2005157 = 375967) (by norm_num)
theorem B3659957 : Blo 1334986 3659957 := bbase (se 5 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 3659957 = 343121) (by norm_num)
theorem B2005181 : Blo 1334986 2005181 := bbase (se 3 (by rfl) ⟨375971, by rfl⟩ : syracuseStep 2005181 = 751943) (by norm_num)
theorem B3004613 : Blo 1334986 3004613 := bbase (se 4 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 3004613 = 563365) (by norm_num)
theorem B2005205 : Blo 1334986 2005205 := bbase (se 7 (by rfl) ⟨23498, by rfl⟩ : syracuseStep 2005205 = 46997) (by norm_num)
theorem B2005229 : Blo 1334986 2005229 := bbase (se 3 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 2005229 = 751961) (by norm_num)
theorem B2537725 : Blo 1334986 2537725 := bbase (se 3 (by rfl) ⟨475823, by rfl⟩ : syracuseStep 2537725 = 951647) (by norm_num)
theorem B2005253 : Blo 1334986 2005253 := bbase (se 4 (by rfl) ⟨187992, by rfl⟩ : syracuseStep 2005253 = 375985) (by norm_num)
theorem B3004685 : Blo 1334986 3004685 := bbase (se 3 (by rfl) ⟨563378, by rfl⟩ : syracuseStep 3004685 = 1126757) (by norm_num)
theorem B2005277 : Blo 1334986 2005277 := bbase (se 3 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 2005277 = 751979) (by norm_num)
theorem B7706933 : Blo 1334986 7706933 := bbase (se 5 (by rfl) ⟨361262, by rfl⟩ : syracuseStep 7706933 = 722525) (by norm_num)
theorem B2005301 : Blo 1334986 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B2005325 : Blo 1334986 2005325 := bbase (se 3 (by rfl) ⟨375998, by rfl⟩ : syracuseStep 2005325 = 751997) (by norm_num)
theorem B3004757 : Blo 1334986 3004757 := bbase (se 10 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 3004757 = 8803) (by norm_num)
theorem B2029925 : Blo 1334986 2029925 := bbase (se 4 (by rfl) ⟨190305, by rfl⟩ : syracuseStep 2029925 = 380611) (by norm_num)
theorem B2005349 : Blo 1334986 2005349 := bbase (se 4 (by rfl) ⟨188001, by rfl⟩ : syracuseStep 2005349 = 376003) (by norm_num)
theorem B2005373 : Blo 1334986 2005373 := bbase (se 3 (by rfl) ⟨376007, by rfl⟩ : syracuseStep 2005373 = 752015) (by norm_num)
theorem B2005397 : Blo 1334986 2005397 := bbase (se 6 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 2005397 = 94003) (by norm_num)
theorem B3004829 : Blo 1334986 3004829 := bbase (se 3 (by rfl) ⟨563405, by rfl⟩ : syracuseStep 3004829 = 1126811) (by norm_num)
theorem B2537885 : Blo 1334986 2537885 := bbase (se 3 (by rfl) ⟨475853, by rfl⟩ : syracuseStep 2537885 = 951707) (by norm_num)
theorem B2005421 : Blo 1334986 2005421 := bbase (se 3 (by rfl) ⟨376016, by rfl⟩ : syracuseStep 2005421 = 752033) (by norm_num)
theorem B2005445 : Blo 1334986 2005445 := bbase (se 4 (by rfl) ⟨188010, by rfl⟩ : syracuseStep 2005445 = 376021) (by norm_num)
theorem B3381709 : Blo 1334986 3381709 := bbase (se 3 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 3381709 = 1268141) (by norm_num)
theorem B2005469 : Blo 1334986 2005469 := bbase (se 3 (by rfl) ⟨376025, by rfl⟩ : syracuseStep 2005469 = 752051) (by norm_num)
theorem B3004901 : Blo 1334986 3004901 := bbase (se 4 (by rfl) ⟨281709, by rfl⟩ : syracuseStep 3004901 = 563419) (by norm_num)
theorem B2169317 : Blo 1334986 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B2439661 : Blo 1334986 2439661 := bbase (se 3 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 2439661 = 914873) (by norm_num)
theorem B4512293 : Blo 1334986 4512293 := bbase (se 4 (by rfl) ⟨423027, by rfl⟩ : syracuseStep 4512293 = 846055) (by norm_num)
theorem B3004973 : Blo 1334986 3004973 := bbase (se 3 (by rfl) ⟨563432, by rfl⟩ : syracuseStep 3004973 = 1126865) (by norm_num)
theorem B2538029 : Blo 1334986 2538029 := bbase (se 3 (by rfl) ⟨475880, by rfl⟩ : syracuseStep 2538029 = 951761) (by norm_num)
theorem B3381821 : Blo 1334986 3381821 := bbase (se 3 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 3381821 = 1268183) (by norm_num)
theorem B1604161 : Blo 1334986 1604161 := bbase (se 2 (by rfl) ⟨601560, by rfl⟩ : syracuseStep 1604161 = 1203121) (by norm_num)
theorem B2406997 : Blo 1334986 2406997 := bbase (se 8 (by rfl) ⟨14103, by rfl⟩ : syracuseStep 2406997 = 28207) (by norm_num)
theorem B3086957 : Blo 1334986 3086957 := bbase (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) (by norm_num)
theorem B3005045 : Blo 1334986 3005045 := bbase (se 5 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 3005045 = 281723) (by norm_num)
theorem B3005117 : Blo 1334986 3005117 := bbase (se 3 (by rfl) ⟨563459, by rfl⟩ : syracuseStep 3005117 = 1126919) (by norm_num)
theorem B2407141 : Blo 1334986 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B3382013 : Blo 1334986 3382013 := bbase (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) (by norm_num)
theorem B1604353 : Blo 1334986 1604353 := bbase (se 2 (by rfl) ⟨601632, by rfl⟩ : syracuseStep 1604353 = 1203265) (by norm_num)
theorem B5069573 : Blo 1334986 5069573 := bbase (se 4 (by rfl) ⟨475272, by rfl⟩ : syracuseStep 5069573 = 950545) (by norm_num)
theorem B3005189 : Blo 1334986 3005189 := bbase (se 4 (by rfl) ⟨281736, by rfl⟩ : syracuseStep 3005189 = 563473) (by norm_num)
theorem B5708549 : Blo 1334986 5708549 := bbase (se 4 (by rfl) ⟨535176, by rfl⟩ : syracuseStep 5708549 = 1070353) (by norm_num)
theorem B3046157 : Blo 1334986 3046157 := bbase (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) (by norm_num)
theorem B3005261 : Blo 1334986 3005261 := bbase (se 3 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 3005261 = 1126973) (by norm_num)
theorem B1604453 : Blo 1334986 1604453 := bbase (se 4 (by rfl) ⟨150417, by rfl⟩ : syracuseStep 1604453 = 300835) (by norm_num)
theorem B3005333 : Blo 1334986 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B3046349 : Blo 1334986 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B3005405 : Blo 1334986 3005405 := bbase (se 3 (by rfl) ⟨563513, by rfl⟩ : syracuseStep 3005405 = 1127027) (by norm_num)
theorem B3611621 : Blo 1334986 3611621 := bbase (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) (by norm_num)
theorem B5708789 : Blo 1334986 5708789 := bbase (se 5 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 5708789 = 535199) (by norm_num)
theorem B5069861 : Blo 1334986 5069861 := bbase (se 4 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 5069861 = 950599) (by norm_num)
theorem B3005477 : Blo 1334986 3005477 := bbase (se 4 (by rfl) ⟨281763, by rfl⟩ : syracuseStep 3005477 = 563527) (by norm_num)
theorem B6765605 : Blo 1334986 6765605 := bbase (se 4 (by rfl) ⟨634275, by rfl⟩ : syracuseStep 6765605 = 1268551) (by norm_num)
theorem B1522741 : Blo 1334986 1522741 := bbase (se 5 (by rfl) ⟨71378, by rfl⟩ : syracuseStep 1522741 = 142757) (by norm_num)
theorem B3382357 : Blo 1334986 3382357 := bbase (se 8 (by rfl) ⟨19818, by rfl⟩ : syracuseStep 3382357 = 39637) (by norm_num)
theorem B3005549 : Blo 1334986 3005549 := bbase (se 3 (by rfl) ⟨563540, by rfl⟩ : syracuseStep 3005549 = 1127081) (by norm_num)
theorem B3210349 : Blo 1334986 3210349 := bbase (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) (by norm_num)
theorem B3005621 : Blo 1334986 3005621 := bbase (se 5 (by rfl) ⟨140888, by rfl⟩ : syracuseStep 3005621 = 281777) (by norm_num)
theorem B3382469 : Blo 1334986 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B3005693 : Blo 1334986 3005693 := bbase (se 3 (by rfl) ⟨563567, by rfl⟩ : syracuseStep 3005693 = 1127135) (by norm_num)
theorem B3005765 : Blo 1334986 3005765 := bbase (se 4 (by rfl) ⟨281790, by rfl⟩ : syracuseStep 3005765 = 563581) (by norm_num)
theorem B4341077 : Blo 1334986 4341077 := bbase (se 11 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 4341077 = 6359) (by norm_num)
theorem B3382661 : Blo 1334986 3382661 := bbase (se 4 (by rfl) ⟨317124, by rfl⟩ : syracuseStep 3382661 = 634249) (by norm_num)
theorem B3005837 : Blo 1334986 3005837 := bbase (se 3 (by rfl) ⟨563594, by rfl⟩ : syracuseStep 3005837 = 1127189) (by norm_num)
theorem B3612053 : Blo 1334986 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B2784701 : Blo 1334986 2784701 := bbase (se 3 (by rfl) ⟨522131, by rfl⟩ : syracuseStep 2784701 = 1044263) (by norm_num)
theorem B3005909 : Blo 1334986 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B3005981 : Blo 1334986 3005981 := bbase (se 3 (by rfl) ⟨563621, by rfl⟩ : syracuseStep 3005981 = 1127243) (by norm_num)
theorem B3006053 : Blo 1334986 3006053 := bbase (se 4 (by rfl) ⟨281817, by rfl⟩ : syracuseStep 3006053 = 563635) (by norm_num)
theorem B1605241 : Blo 1334986 1605241 := bbase (se 2 (by rfl) ⟨601965, by rfl⟩ : syracuseStep 1605241 = 1203931) (by norm_num)
theorem B4062869 : Blo 1334986 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B3006125 : Blo 1334986 3006125 := bbase (se 3 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 3006125 = 1127297) (by norm_num)
theorem B3210965 : Blo 1334986 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B3383005 : Blo 1334986 3383005 := bbase (se 3 (by rfl) ⟨634313, by rfl⟩ : syracuseStep 3383005 = 1268627) (by norm_num)
theorem B3006197 : Blo 1334986 3006197 := bbase (se 5 (by rfl) ⟨140915, by rfl⟩ : syracuseStep 3006197 = 281831) (by norm_num)
theorem B3006269 : Blo 1334986 3006269 := bbase (se 3 (by rfl) ⟨563675, by rfl⟩ : syracuseStep 3006269 = 1127351) (by norm_num)
theorem B3612485 : Blo 1334986 3612485 := bbase (se 4 (by rfl) ⟨338670, by rfl⟩ : syracuseStep 3612485 = 677341) (by norm_num)
theorem B3383117 : Blo 1334986 3383117 := bbase (se 3 (by rfl) ⟨634334, by rfl⟩ : syracuseStep 3383117 = 1268669) (by norm_num)
theorem B1523561 : Blo 1334986 1523561 := bbase (se 2 (by rfl) ⟨571335, by rfl⟩ : syracuseStep 1523561 = 1142671) (by norm_num)
theorem B3006341 : Blo 1334986 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B2408381 : Blo 1334986 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B3129293 : Blo 1334986 3129293 := bbase (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) (by norm_num)
theorem B3006413 : Blo 1334986 3006413 := bbase (se 3 (by rfl) ⟨563702, by rfl⟩ : syracuseStep 3006413 = 1127405) (by norm_num)
theorem B2031581 : Blo 1334986 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B2744309 : Blo 1334986 2744309 := bbase (se 5 (by rfl) ⟨128639, by rfl⟩ : syracuseStep 2744309 = 257279) (by norm_num)
theorem B1335299 : Blo 1334986 1335299 := bstep (se 1 (by rfl) ⟨1001474, by rfl⟩ : syracuseStep 1335299 = 2002949) B2002949
theorem B3006467 : Blo 1334986 3006467 := bstep (se 1 (by rfl) ⟨2254850, by rfl⟩ : syracuseStep 3006467 = 4509701) B4509701
theorem B17121293 : Blo 1334986 17121293 := bstep (se 3 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 17121293 = 6420485) B6420485
theorem B2252819 : Blo 1334986 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B1335315 : Blo 1334986 1335315 := bstep (se 1 (by rfl) ⟨1001486, by rfl⟩ : syracuseStep 1335315 = 2002973) B2002973
theorem B1335331 : Blo 1334986 1335331 := bstep (se 1 (by rfl) ⟨1001498, by rfl⟩ : syracuseStep 1335331 = 2002997) B2002997
theorem B1335347 : Blo 1334986 1335347 := bstep (se 1 (by rfl) ⟨1001510, by rfl⟩ : syracuseStep 1335347 = 2003021) B2003021
theorem B1335363 : Blo 1334986 1335363 := bstep (se 1 (by rfl) ⟨1001522, by rfl⟩ : syracuseStep 1335363 = 2003045) B2003045
theorem B6758477 : Blo 1334986 6758477 := bstep (se 3 (by rfl) ⟨1267214, by rfl⟩ : syracuseStep 6758477 = 2534429) B2534429
theorem B1335379 : Blo 1334986 1335379 := bstep (se 1 (by rfl) ⟨1001534, by rfl⟩ : syracuseStep 1335379 = 2003069) B2003069
theorem B1335395 : Blo 1334986 1335395 := bstep (se 1 (by rfl) ⟨1001546, by rfl⟩ : syracuseStep 1335395 = 2003093) B2003093
theorem B1335411 : Blo 1334986 1335411 := bstep (se 1 (by rfl) ⟨1001558, by rfl⟩ : syracuseStep 1335411 = 2003117) B2003117
theorem B1335427 : Blo 1334986 1335427 := bstep (se 1 (by rfl) ⟨1001570, by rfl⟩ : syracuseStep 1335427 = 2003141) B2003141
theorem B3383441 : Blo 1334986 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B2252947 : Blo 1334986 2252947 := bstep (se 1 (by rfl) ⟨1689710, by rfl⟩ : syracuseStep 2252947 = 3379421) B3379421
theorem B1335443 : Blo 1334986 1335443 := bstep (se 1 (by rfl) ⟨1001582, by rfl⟩ : syracuseStep 1335443 = 2003165) B2003165
theorem B1335459 : Blo 1334986 1335459 := bstep (se 1 (by rfl) ⟨1001594, by rfl⟩ : syracuseStep 1335459 = 2003189) B2003189
theorem B1335475 : Blo 1334986 1335475 := bstep (se 1 (by rfl) ⟨1001606, by rfl⟩ : syracuseStep 1335475 = 2003213) B2003213
theorem B1335491 : Blo 1334986 1335491 := bstep (se 1 (by rfl) ⟨1001618, by rfl⟩ : syracuseStep 1335491 = 2003237) B2003237
theorem B3383491 : Blo 1334986 3383491 := bstep (se 1 (by rfl) ⟨2537618, by rfl⟩ : syracuseStep 3383491 = 5075237) B5075237
theorem B1335507 : Blo 1334986 1335507 := bstep (se 1 (by rfl) ⟨1001630, by rfl⟩ : syracuseStep 1335507 = 2003261) B2003261
theorem B1335523 : Blo 1334986 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B15212771 : Blo 1334986 15212771 := bstep (se 1 (by rfl) ⟨11409578, by rfl⟩ : syracuseStep 15212771 = 22819157) B22819157
theorem B1335539 : Blo 1334986 1335539 := bstep (se 1 (by rfl) ⟨1001654, by rfl⟩ : syracuseStep 1335539 = 2003309) B2003309
theorem B1335555 : Blo 1334986 1335555 := bstep (se 1 (by rfl) ⟨1001666, by rfl⟩ : syracuseStep 1335555 = 2003333) B2003333
theorem B3006737 : Blo 1334986 3006737 := bstep (se 2 (by rfl) ⟨1127526, by rfl⟩ : syracuseStep 3006737 = 2255053) B2255053
theorem B1335571 : Blo 1334986 1335571 := bstep (se 1 (by rfl) ⟨1001678, by rfl⟩ : syracuseStep 1335571 = 2003357) B2003357
theorem B2253089 : Blo 1334986 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B1335587 : Blo 1334986 1335587 := bstep (se 1 (by rfl) ⟨1001690, by rfl⟩ : syracuseStep 1335587 = 2003381) B2003381
theorem B3006755 : Blo 1334986 3006755 := bstep (se 1 (by rfl) ⟨2255066, by rfl⟩ : syracuseStep 3006755 = 4510133) B4510133
theorem B1335603 : Blo 1334986 1335603 := bstep (se 1 (by rfl) ⟨1001702, by rfl⟩ : syracuseStep 1335603 = 2003405) B2003405
theorem B1335619 : Blo 1334986 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B3383633 : Blo 1334986 3383633 := bstep (se 2 (by rfl) ⟨1268862, by rfl⟩ : syracuseStep 3383633 = 2537725) B2537725
theorem B1335635 : Blo 1334986 1335635 := bstep (se 1 (by rfl) ⟨1001726, by rfl⟩ : syracuseStep 1335635 = 2003453) B2003453
theorem B1335651 : Blo 1334986 1335651 := bstep (se 1 (by rfl) ⟨1001738, by rfl⟩ : syracuseStep 1335651 = 2003477) B2003477
theorem B3613027 : Blo 1334986 3613027 := bstep (se 1 (by rfl) ⟨2709770, by rfl⟩ : syracuseStep 3613027 = 5419541) B5419541
theorem B1900913 : Blo 1334986 1900913 := bstep (se 2 (by rfl) ⟨712842, by rfl⟩ : syracuseStep 1900913 = 1425685) B1425685
theorem B1335667 : Blo 1334986 1335667 := bstep (se 1 (by rfl) ⟨1001750, by rfl⟩ : syracuseStep 1335667 = 2003501) B2003501
theorem B1335683 : Blo 1334986 1335683 := bstep (se 1 (by rfl) ⟨1001762, by rfl⟩ : syracuseStep 1335683 = 2003525) B2003525
theorem B1335699 : Blo 1334986 1335699 := bstep (se 1 (by rfl) ⟨1001774, by rfl⟩ : syracuseStep 1335699 = 2003549) B2003549
theorem B2253217 : Blo 1334986 2253217 := bstep (se 2 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 2253217 = 1689913) B1689913
theorem B1335715 : Blo 1334986 1335715 := bstep (se 1 (by rfl) ⟨1001786, by rfl⟩ : syracuseStep 1335715 = 2003573) B2003573
theorem B4506029 : Blo 1334986 4506029 := bstep (se 3 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 4506029 = 1689761) B1689761
theorem B1335731 : Blo 1334986 1335731 := bstep (se 1 (by rfl) ⟨1001798, by rfl⟩ : syracuseStep 1335731 = 2003597) B2003597
theorem B2253251 : Blo 1334986 2253251 := bstep (se 1 (by rfl) ⟨1689938, by rfl⟩ : syracuseStep 2253251 = 3379877) B3379877
theorem B1335747 : Blo 1334986 1335747 := bstep (se 1 (by rfl) ⟨1001810, by rfl⟩ : syracuseStep 1335747 = 2003621) B2003621
theorem B2032067 : Blo 1334986 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B2138579 : Blo 1334986 2138579 := bstep (se 1 (by rfl) ⟨1603934, by rfl⟩ : syracuseStep 2138579 = 3207869) B3207869
theorem B1335763 : Blo 1334986 1335763 := bstep (se 1 (by rfl) ⟨1001822, by rfl⟩ : syracuseStep 1335763 = 2003645) B2003645
theorem B4506083 : Blo 1334986 4506083 := bstep (se 1 (by rfl) ⟨3379562, by rfl⟩ : syracuseStep 4506083 = 6759125) B6759125
theorem B1901027 : Blo 1334986 1901027 := bstep (se 1 (by rfl) ⟨1425770, by rfl⟩ : syracuseStep 1901027 = 2851541) B2851541
theorem B1335779 : Blo 1334986 1335779 := bstep (se 1 (by rfl) ⟨1001834, by rfl⟩ : syracuseStep 1335779 = 2003669) B2003669
theorem B1425907 : Blo 1334986 1425907 := bstep (se 1 (by rfl) ⟨1069430, by rfl⟩ : syracuseStep 1425907 = 2138861) B2138861
theorem B1335795 : Blo 1334986 1335795 := bstep (se 1 (by rfl) ⟨1001846, by rfl⟩ : syracuseStep 1335795 = 2003693) B2003693
theorem B1335811 : Blo 1334986 1335811 := bstep (se 1 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 1335811 = 2003717) B2003717
theorem B1335827 : Blo 1334986 1335827 := bstep (se 1 (by rfl) ⟨1001870, by rfl⟩ : syracuseStep 1335827 = 2003741) B2003741
theorem B1335843 : Blo 1334986 1335843 := bstep (se 1 (by rfl) ⟨1001882, by rfl⟩ : syracuseStep 1335843 = 2003765) B2003765
theorem B3007025 : Blo 1334986 3007025 := bstep (se 2 (by rfl) ⟨1127634, by rfl⟩ : syracuseStep 3007025 = 2255269) B2255269
theorem B1901107 : Blo 1334986 1901107 := bstep (se 1 (by rfl) ⟨1425830, by rfl⟩ : syracuseStep 1901107 = 2851661) B2851661
theorem B1335859 : Blo 1334986 1335859 := bstep (se 1 (by rfl) ⟨1001894, by rfl⟩ : syracuseStep 1335859 = 2003789) B2003789
theorem B2032193 : Blo 1334986 2032193 := bstep (se 2 (by rfl) ⟨762072, by rfl⟩ : syracuseStep 2032193 = 1524145) B1524145
theorem B3801667 : Blo 1334986 3801667 := bstep (se 1 (by rfl) ⟨2851250, by rfl⟩ : syracuseStep 3801667 = 5702501) B5702501
theorem B2253379 : Blo 1334986 2253379 := bstep (se 1 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 2253379 = 3380069) B3380069
theorem B1335875 : Blo 1334986 1335875 := bstep (se 1 (by rfl) ⟨1001906, by rfl⟩ : syracuseStep 1335875 = 2003813) B2003813
theorem B3007043 : Blo 1334986 3007043 := bstep (se 1 (by rfl) ⟨2255282, by rfl⟩ : syracuseStep 3007043 = 4510565) B4510565
theorem B1335891 : Blo 1334986 1335891 := bstep (se 1 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 1335891 = 2003837) B2003837
theorem B1335907 : Blo 1334986 1335907 := bstep (se 1 (by rfl) ⟨1001930, by rfl⟩ : syracuseStep 1335907 = 2003861) B2003861
theorem B1335923 : Blo 1334986 1335923 := bstep (se 1 (by rfl) ⟨1001942, by rfl⟩ : syracuseStep 1335923 = 2003885) B2003885
theorem B1335939 : Blo 1334986 1335939 := bstep (se 1 (by rfl) ⟨1001954, by rfl⟩ : syracuseStep 1335939 = 2003909) B2003909
theorem B8561285 : Blo 1334986 8561285 := bstep (se 4 (by rfl) ⟨802620, by rfl⟩ : syracuseStep 8561285 = 1605241) B1605241
theorem B1335955 : Blo 1334986 1335955 := bstep (se 1 (by rfl) ⟨1001966, by rfl⟩ : syracuseStep 1335955 = 2003933) B2003933
theorem B1335971 : Blo 1334986 1335971 := bstep (se 1 (by rfl) ⟨1001978, by rfl⟩ : syracuseStep 1335971 = 2003957) B2003957
theorem B1335987 : Blo 1334986 1335987 := bstep (se 1 (by rfl) ⟨1001990, by rfl⟩ : syracuseStep 1335987 = 2003981) B2003981
theorem B1336003 : Blo 1334986 1336003 := bstep (se 1 (by rfl) ⟨1002002, by rfl⟩ : syracuseStep 1336003 = 2004005) B2004005
theorem B2253521 : Blo 1334986 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B1336019 : Blo 1334986 1336019 := bstep (se 1 (by rfl) ⟨1002014, by rfl⟩ : syracuseStep 1336019 = 2004029) B2004029
theorem B1336035 : Blo 1334986 1336035 := bstep (se 1 (by rfl) ⟨1002026, by rfl⟩ : syracuseStep 1336035 = 2004053) B2004053
theorem B4506353 : Blo 1334986 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B1336051 : Blo 1334986 1336051 := bstep (se 1 (by rfl) ⟨1002038, by rfl⟩ : syracuseStep 1336051 = 2004077) B2004077
theorem B2138881 : Blo 1334986 2138881 := bstep (se 2 (by rfl) ⟨802080, by rfl⟩ : syracuseStep 2138881 = 1604161) B1604161
theorem B1336067 : Blo 1334986 1336067 := bstep (se 1 (by rfl) ⟨1002050, by rfl⟩ : syracuseStep 1336067 = 2004101) B2004101
theorem B1336083 : Blo 1334986 1336083 := bstep (se 1 (by rfl) ⟨1002062, by rfl⟩ : syracuseStep 1336083 = 2004125) B2004125
theorem B2286355 : Blo 1334986 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B1336099 : Blo 1334986 1336099 := bstep (se 1 (by rfl) ⟨1002074, by rfl⟩ : syracuseStep 1336099 = 2004149) B2004149
theorem B1336115 : Blo 1334986 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B1336131 : Blo 1334986 1336131 := bstep (se 1 (by rfl) ⟨1002098, by rfl⟩ : syracuseStep 1336131 = 2004197) B2004197
theorem B2253649 : Blo 1334986 2253649 := bstep (se 2 (by rfl) ⟨845118, by rfl⟩ : syracuseStep 2253649 = 1690237) B1690237
theorem B3007313 : Blo 1334986 3007313 := bstep (se 2 (by rfl) ⟨1127742, by rfl⟩ : syracuseStep 3007313 = 2255485) B2255485
theorem B1336147 : Blo 1334986 1336147 := bstep (se 1 (by rfl) ⟨1002110, by rfl⟩ : syracuseStep 1336147 = 2004221) B2004221
theorem B1336163 : Blo 1334986 1336163 := bstep (se 1 (by rfl) ⟨1002122, by rfl⟩ : syracuseStep 1336163 = 2004245) B2004245
theorem B3007331 : Blo 1334986 3007331 := bstep (se 1 (by rfl) ⟨2255498, by rfl⟩ : syracuseStep 3007331 = 4510997) B4510997
theorem B7226225 : Blo 1334986 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B2253683 : Blo 1334986 2253683 := bstep (se 1 (by rfl) ⟨1690262, by rfl⟩ : syracuseStep 2253683 = 3380525) B3380525
theorem B1336179 : Blo 1334986 1336179 := bstep (se 1 (by rfl) ⟨1002134, by rfl⟩ : syracuseStep 1336179 = 2004269) B2004269
theorem B1336195 : Blo 1334986 1336195 := bstep (se 1 (by rfl) ⟨1002146, by rfl⟩ : syracuseStep 1336195 = 2004293) B2004293
theorem B1336211 : Blo 1334986 1336211 := bstep (se 1 (by rfl) ⟨1002158, by rfl⟩ : syracuseStep 1336211 = 2004317) B2004317
theorem B1336227 : Blo 1334986 1336227 := bstep (se 1 (by rfl) ⟨1002170, by rfl⟩ : syracuseStep 1336227 = 2004341) B2004341
theorem B1336243 : Blo 1334986 1336243 := bstep (se 1 (by rfl) ⟨1002182, by rfl⟩ : syracuseStep 1336243 = 2004365) B2004365
theorem B1336259 : Blo 1334986 1336259 := bstep (se 1 (by rfl) ⟨1002194, by rfl⟩ : syracuseStep 1336259 = 2004389) B2004389
theorem B2139091 : Blo 1334986 2139091 := bstep (se 1 (by rfl) ⟨1604318, by rfl⟩ : syracuseStep 2139091 = 3208637) B3208637
theorem B1336275 : Blo 1334986 1336275 := bstep (se 1 (by rfl) ⟨1002206, by rfl⟩ : syracuseStep 1336275 = 2004413) B2004413
theorem B1336291 : Blo 1334986 1336291 := bstep (se 1 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 1336291 = 2004437) B2004437
theorem B2253811 : Blo 1334986 2253811 := bstep (se 1 (by rfl) ⟨1690358, by rfl⟩ : syracuseStep 2253811 = 3380717) B3380717
theorem B1336307 : Blo 1334986 1336307 := bstep (se 1 (by rfl) ⟨1002230, by rfl⟩ : syracuseStep 1336307 = 2004461) B2004461
theorem B2139137 : Blo 1334986 2139137 := bstep (se 2 (by rfl) ⟨802176, by rfl⟩ : syracuseStep 2139137 = 1604353) B1604353
theorem B1336323 : Blo 1334986 1336323 := bstep (se 1 (by rfl) ⟨1002242, by rfl⟩ : syracuseStep 1336323 = 2004485) B2004485
theorem B1336339 : Blo 1334986 1336339 := bstep (se 1 (by rfl) ⟨1002254, by rfl⟩ : syracuseStep 1336339 = 2004509) B2004509
theorem B1336355 : Blo 1334986 1336355 := bstep (se 1 (by rfl) ⟨1002266, by rfl⟩ : syracuseStep 1336355 = 2004533) B2004533
theorem B1336371 : Blo 1334986 1336371 := bstep (se 1 (by rfl) ⟨1002278, by rfl⟩ : syracuseStep 1336371 = 2004557) B2004557
theorem B17114165 : Blo 1334986 17114165 := bstep (se 5 (by rfl) ⟨802226, by rfl⟩ : syracuseStep 17114165 = 1604453) B1604453
theorem B1336387 : Blo 1334986 1336387 := bstep (se 1 (by rfl) ⟨1002290, by rfl⟩ : syracuseStep 1336387 = 2004581) B2004581
theorem B1336403 : Blo 1334986 1336403 := bstep (se 1 (by rfl) ⟨1002302, by rfl⟩ : syracuseStep 1336403 = 2004605) B2004605
theorem B1901665 : Blo 1334986 1901665 := bstep (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) B1426249
theorem B10142819 : Blo 1334986 10142819 := bstep (se 1 (by rfl) ⟨7607114, by rfl⟩ : syracuseStep 10142819 = 15214229) B15214229
theorem B1336419 : Blo 1334986 1336419 := bstep (se 1 (by rfl) ⟨1002314, by rfl⟩ : syracuseStep 1336419 = 2004629) B2004629
theorem B3613805 : Blo 1334986 3613805 := bstep (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) B1355177
theorem B3007601 : Blo 1334986 3007601 := bstep (se 2 (by rfl) ⟨1127850, by rfl⟩ : syracuseStep 3007601 = 2255701) B2255701
theorem B1336435 : Blo 1334986 1336435 := bstep (se 1 (by rfl) ⟨1002326, by rfl⟩ : syracuseStep 1336435 = 2004653) B2004653
theorem B2253953 : Blo 1334986 2253953 := bstep (se 2 (by rfl) ⟨845232, by rfl⟩ : syracuseStep 2253953 = 1690465) B1690465
theorem B1336451 : Blo 1334986 1336451 := bstep (se 1 (by rfl) ⟨1002338, by rfl⟩ : syracuseStep 1336451 = 2004677) B2004677
theorem B3007619 : Blo 1334986 3007619 := bstep (se 1 (by rfl) ⟨2255714, by rfl⟩ : syracuseStep 3007619 = 4511429) B4511429
theorem B2851985 : Blo 1334986 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B1336467 : Blo 1334986 1336467 := bstep (se 1 (by rfl) ⟨1002350, by rfl⟩ : syracuseStep 1336467 = 2004701) B2004701
theorem B2852003 : Blo 1334986 2852003 := bstep (se 1 (by rfl) ⟨2139002, by rfl⟩ : syracuseStep 2852003 = 4278005) B4278005
theorem B1336483 : Blo 1334986 1336483 := bstep (se 1 (by rfl) ⟨1002362, by rfl⟩ : syracuseStep 1336483 = 2004725) B2004725
theorem B1336499 : Blo 1334986 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B1336515 : Blo 1334986 1336515 := bstep (se 1 (by rfl) ⟨1002386, by rfl⟩ : syracuseStep 1336515 = 2004773) B2004773
theorem B12838085 : Blo 1334986 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B1336531 : Blo 1334986 1336531 := bstep (se 1 (by rfl) ⟨1002398, by rfl⟩ : syracuseStep 1336531 = 2004797) B2004797
theorem B1336547 : Blo 1334986 1336547 := bstep (se 1 (by rfl) ⟨1002410, by rfl⟩ : syracuseStep 1336547 = 2004821) B2004821
theorem B1336563 : Blo 1334986 1336563 := bstep (se 1 (by rfl) ⟨1002422, by rfl⟩ : syracuseStep 1336563 = 2004845) B2004845
theorem B2254081 : Blo 1334986 2254081 := bstep (se 2 (by rfl) ⟨845280, by rfl⟩ : syracuseStep 2254081 = 1690561) B1690561
theorem B1336579 : Blo 1334986 1336579 := bstep (se 1 (by rfl) ⟨1002434, by rfl⟩ : syracuseStep 1336579 = 2004869) B2004869
theorem B4506893 : Blo 1334986 4506893 := bstep (se 3 (by rfl) ⟨845042, by rfl⟩ : syracuseStep 4506893 = 1690085) B1690085
theorem B1336595 : Blo 1334986 1336595 := bstep (se 1 (by rfl) ⟨1002446, by rfl⟩ : syracuseStep 1336595 = 2004893) B2004893
theorem B2254115 : Blo 1334986 2254115 := bstep (se 1 (by rfl) ⟨1690586, by rfl⟩ : syracuseStep 2254115 = 3381173) B3381173
theorem B1336611 : Blo 1334986 1336611 := bstep (se 1 (by rfl) ⟨1002458, by rfl⟩ : syracuseStep 1336611 = 2004917) B2004917
theorem B1336627 : Blo 1334986 1336627 := bstep (se 1 (by rfl) ⟨1002470, by rfl⟩ : syracuseStep 1336627 = 2004941) B2004941
theorem B4506947 : Blo 1334986 4506947 := bstep (se 1 (by rfl) ⟨3380210, by rfl⟩ : syracuseStep 4506947 = 6760421) B6760421
theorem B1336643 : Blo 1334986 1336643 := bstep (se 1 (by rfl) ⟨1002482, by rfl⟩ : syracuseStep 1336643 = 2004965) B2004965
theorem B1336659 : Blo 1334986 1336659 := bstep (se 1 (by rfl) ⟨1002494, by rfl⟩ : syracuseStep 1336659 = 2004989) B2004989
theorem B1336675 : Blo 1334986 1336675 := bstep (se 1 (by rfl) ⟨1002506, by rfl⟩ : syracuseStep 1336675 = 2005013) B2005013
theorem B15435107 : Blo 1334986 15435107 := bstep (se 1 (by rfl) ⟨11576330, by rfl⟩ : syracuseStep 15435107 = 23152661) B23152661
theorem B27813233 : Blo 1334986 27813233 := bstep (se 2 (by rfl) ⟨10429962, by rfl⟩ : syracuseStep 27813233 = 20859925) B20859925
theorem B1336691 : Blo 1334986 1336691 := bstep (se 1 (by rfl) ⟨1002518, by rfl⟩ : syracuseStep 1336691 = 2005037) B2005037
theorem B1336707 : Blo 1334986 1336707 := bstep (se 1 (by rfl) ⟨1002530, by rfl⟩ : syracuseStep 1336707 = 2005061) B2005061
theorem B3007889 : Blo 1334986 3007889 := bstep (se 2 (by rfl) ⟨1127958, by rfl⟩ : syracuseStep 3007889 = 2255917) B2255917
theorem B1336723 : Blo 1334986 1336723 := bstep (se 1 (by rfl) ⟨1002542, by rfl⟩ : syracuseStep 1336723 = 2005085) B2005085
theorem B2254243 : Blo 1334986 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B5072291 : Blo 1334986 5072291 := bstep (se 1 (by rfl) ⟨3804218, by rfl⟩ : syracuseStep 5072291 = 7608437) B7608437
theorem B1336739 : Blo 1334986 1336739 := bstep (se 1 (by rfl) ⟨1002554, by rfl⟩ : syracuseStep 1336739 = 2005109) B2005109
theorem B3007907 : Blo 1334986 3007907 := bstep (se 1 (by rfl) ⟨2255930, by rfl⟩ : syracuseStep 3007907 = 4511861) B4511861
theorem B6768035 : Blo 1334986 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B1336755 : Blo 1334986 1336755 := bstep (se 1 (by rfl) ⟨1002566, by rfl⟩ : syracuseStep 1336755 = 2005133) B2005133
theorem B1336771 : Blo 1334986 1336771 := bstep (se 1 (by rfl) ⟨1002578, by rfl⟩ : syracuseStep 1336771 = 2005157) B2005157
theorem B7611853 : Blo 1334986 7611853 := bstep (se 3 (by rfl) ⟨1427222, by rfl⟩ : syracuseStep 7611853 = 2854445) B2854445
theorem B1336787 : Blo 1334986 1336787 := bstep (se 1 (by rfl) ⟨1002590, by rfl⟩ : syracuseStep 1336787 = 2005181) B2005181
theorem B1426915 : Blo 1334986 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B1336803 : Blo 1334986 1336803 := bstep (se 1 (by rfl) ⟨1002602, by rfl⟩ : syracuseStep 1336803 = 2005205) B2005205
theorem B1336819 : Blo 1334986 1336819 := bstep (se 1 (by rfl) ⟨1002614, by rfl⟩ : syracuseStep 1336819 = 2005229) B2005229
theorem B1336835 : Blo 1334986 1336835 := bstep (se 1 (by rfl) ⟨1002626, by rfl⟩ : syracuseStep 1336835 = 2005253) B2005253
theorem B1336851 : Blo 1334986 1336851 := bstep (se 1 (by rfl) ⟨1002638, by rfl⟩ : syracuseStep 1336851 = 2005277) B2005277
theorem B5137955 : Blo 1334986 5137955 := bstep (se 1 (by rfl) ⟨3853466, by rfl⟩ : syracuseStep 5137955 = 7706933) B7706933
theorem B1336867 : Blo 1334986 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B2254385 : Blo 1334986 2254385 := bstep (se 2 (by rfl) ⟨845394, by rfl⟩ : syracuseStep 2254385 = 1690789) B1690789
theorem B1336883 : Blo 1334986 1336883 := bstep (se 1 (by rfl) ⟨1002662, by rfl⟩ : syracuseStep 1336883 = 2005325) B2005325
theorem B1336899 : Blo 1334986 1336899 := bstep (se 1 (by rfl) ⟨1002674, by rfl⟩ : syracuseStep 1336899 = 2005349) B2005349
theorem B4507217 : Blo 1334986 4507217 := bstep (se 2 (by rfl) ⟨1690206, by rfl⟩ : syracuseStep 4507217 = 3380413) B3380413
theorem B1336915 : Blo 1334986 1336915 := bstep (se 1 (by rfl) ⟨1002686, by rfl⟩ : syracuseStep 1336915 = 2005373) B2005373
theorem B1336931 : Blo 1334986 1336931 := bstep (se 1 (by rfl) ⟨1002698, by rfl⟩ : syracuseStep 1336931 = 2005397) B2005397
theorem B1336947 : Blo 1334986 1336947 := bstep (se 1 (by rfl) ⟨1002710, by rfl⟩ : syracuseStep 1336947 = 2005421) B2005421
theorem B1336963 : Blo 1334986 1336963 := bstep (se 1 (by rfl) ⟨1002722, by rfl⟩ : syracuseStep 1336963 = 2005445) B2005445
theorem B11413133 : Blo 1334986 11413133 := bstep (se 3 (by rfl) ⟨2139962, by rfl⟩ : syracuseStep 11413133 = 4279925) B4279925
theorem B1336979 : Blo 1334986 1336979 := bstep (se 1 (by rfl) ⟨1002734, by rfl⟩ : syracuseStep 1336979 = 2005469) B2005469
theorem B3049123 : Blo 1334986 3049123 := bstep (se 1 (by rfl) ⟨2286842, by rfl⟩ : syracuseStep 3049123 = 4573685) B4573685
theorem B2254513 : Blo 1334986 2254513 := bstep (se 2 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 2254513 = 1690885) B1690885
theorem B3008177 : Blo 1334986 3008177 := bstep (se 2 (by rfl) ⟨1128066, by rfl⟩ : syracuseStep 3008177 = 2256133) B2256133
theorem B3008195 : Blo 1334986 3008195 := bstep (se 1 (by rfl) ⟨2256146, by rfl⟩ : syracuseStep 3008195 = 4512293) B4512293
theorem B2254547 : Blo 1334986 2254547 := bstep (se 1 (by rfl) ⟨1690910, by rfl⟩ : syracuseStep 2254547 = 3381821) B3381821
theorem B2057971 : Blo 1334986 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B11405069 : Blo 1334986 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B6096653 : Blo 1334986 6096653 := bstep (se 3 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 6096653 = 2286245) B2286245
theorem B1902371 : Blo 1334986 1902371 := bstep (se 1 (by rfl) ⟨1426778, by rfl⟩ : syracuseStep 1902371 = 2853557) B2853557
theorem B2254675 : Blo 1334986 2254675 := bstep (se 1 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 2254675 = 3382013) B3382013
theorem B14444401 : Blo 1334986 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B3803057 : Blo 1334986 3803057 := bstep (se 2 (by rfl) ⟨1426146, by rfl⟩ : syracuseStep 3803057 = 2852293) B2852293
theorem B2254817 : Blo 1334986 2254817 := bstep (se 2 (by rfl) ⟨845556, by rfl⟩ : syracuseStep 2254817 = 1691113) B1691113
theorem B1427539 : Blo 1334986 1427539 := bstep (se 1 (by rfl) ⟨1070654, by rfl⟩ : syracuseStep 1427539 = 2141309) B2141309
theorem B2254945 : Blo 1334986 2254945 := bstep (se 2 (by rfl) ⟨845604, by rfl⟩ : syracuseStep 2254945 = 1691209) B1691209
theorem B4507757 : Blo 1334986 4507757 := bstep (se 3 (by rfl) ⟨845204, by rfl⟩ : syracuseStep 4507757 = 1690409) B1690409
theorem B2254979 : Blo 1334986 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B4507811 : Blo 1334986 4507811 := bstep (se 1 (by rfl) ⟨3380858, by rfl⟩ : syracuseStep 4507811 = 6761717) B6761717
theorem B1804465 : Blo 1334986 1804465 := bstep (se 2 (by rfl) ⟨676674, by rfl⟩ : syracuseStep 1804465 = 1353349) B1353349
theorem B1804513 : Blo 1334986 1804513 := bstep (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) B1353385
theorem B2894051 : Blo 1334986 2894051 := bstep (se 1 (by rfl) ⟨2170538, by rfl⟩ : syracuseStep 2894051 = 4341077) B4341077
theorem B2255107 : Blo 1334986 2255107 := bstep (se 1 (by rfl) ⟨1691330, by rfl⟩ : syracuseStep 2255107 = 3382661) B3382661
theorem B52046101 : Blo 1334986 52046101 := bstep (se 6 (by rfl) ⟨1219830, by rfl⟩ : syracuseStep 52046101 = 2439661) B2439661
theorem B2058529 : Blo 1334986 2058529 := bstep (se 2 (by rfl) ⟨771948, by rfl⟩ : syracuseStep 2058529 = 1543897) B1543897
theorem B1689923 : Blo 1334986 1689923 := bstep (se 1 (by rfl) ⟨1267442, by rfl⟩ : syracuseStep 1689923 = 2534885) B2534885
theorem B5073293 : Blo 1334986 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B2255249 : Blo 1334986 2255249 := bstep (se 2 (by rfl) ⟨845718, by rfl⟩ : syracuseStep 2255249 = 1691437) B1691437
theorem B1903009 : Blo 1334986 1903009 := bstep (se 2 (by rfl) ⟨713628, by rfl⟩ : syracuseStep 1903009 = 1427257) B1427257
theorem B4508081 : Blo 1334986 4508081 := bstep (se 2 (by rfl) ⟨1690530, by rfl⟩ : syracuseStep 4508081 = 3381061) B3381061
theorem B5704141 : Blo 1334986 5704141 := bstep (se 3 (by rfl) ⟨1069526, by rfl⟩ : syracuseStep 5704141 = 2139053) B2139053
theorem B2140643 : Blo 1334986 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B2255377 : Blo 1334986 2255377 := bstep (se 2 (by rfl) ⟨845766, by rfl⟩ : syracuseStep 2255377 = 1691533) B1691533
theorem B1903123 : Blo 1334986 1903123 := bstep (se 1 (by rfl) ⟨1427342, by rfl⟩ : syracuseStep 1903123 = 2854685) B2854685
theorem B2255411 : Blo 1334986 2255411 := bstep (se 1 (by rfl) ⟨1691558, by rfl⟩ : syracuseStep 2255411 = 3383117) B3383117
theorem B5417549 : Blo 1334986 5417549 := bstep (se 3 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 5417549 = 2031581) B2031581
theorem B1829539 : Blo 1334986 1829539 := bstep (se 1 (by rfl) ⟨1372154, by rfl⟩ : syracuseStep 1829539 = 2744309) B2744309
theorem B2255539 : Blo 1334986 2255539 := bstep (se 1 (by rfl) ⟨1691654, by rfl⟩ : syracuseStep 2255539 = 3383309) B3383309
theorem B2140931 : Blo 1334986 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B1501987 : Blo 1334986 1501987 := bstep (se 1 (by rfl) ⟨1126490, by rfl⟩ : syracuseStep 1501987 = 2252981) B2252981
theorem B2255681 : Blo 1334986 2255681 := bstep (se 2 (by rfl) ⟨845880, by rfl⟩ : syracuseStep 2255681 = 1691761) B1691761
theorem B3804013 : Blo 1334986 3804013 := bstep (se 3 (by rfl) ⟨713252, by rfl⟩ : syracuseStep 3804013 = 1426505) B1426505
theorem B6761393 : Blo 1334986 6761393 := bstep (se 2 (by rfl) ⟨2535522, by rfl⟩ : syracuseStep 6761393 = 5071045) B5071045
theorem B1502131 : Blo 1334986 1502131 := bstep (se 1 (by rfl) ⟨1126598, by rfl⟩ : syracuseStep 1502131 = 2253197) B2253197
theorem B2255809 : Blo 1334986 2255809 := bstep (se 2 (by rfl) ⟨845928, by rfl⟩ : syracuseStep 2255809 = 1691857) B1691857
theorem B4508621 : Blo 1334986 4508621 := bstep (se 3 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 4508621 = 1690733) B1690733
theorem B2255843 : Blo 1334986 2255843 := bstep (se 1 (by rfl) ⟨1691882, by rfl⟩ : syracuseStep 2255843 = 3383765) B3383765
theorem B1690627 : Blo 1334986 1690627 := bstep (se 1 (by rfl) ⟨1267970, by rfl⟩ : syracuseStep 1690627 = 2535941) B2535941
theorem B4508675 : Blo 1334986 4508675 := bstep (se 1 (by rfl) ⟨3381506, by rfl⟩ : syracuseStep 4508675 = 6763013) B6763013
theorem B8121379 : Blo 1334986 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B1502275 : Blo 1334986 1502275 := bstep (se 1 (by rfl) ⟨1126706, by rfl⟩ : syracuseStep 1502275 = 2253413) B2253413
theorem B3804241 : Blo 1334986 3804241 := bstep (se 2 (by rfl) ⟨1426590, by rfl⟩ : syracuseStep 3804241 = 2853181) B2853181
theorem B1690723 : Blo 1334986 1690723 := bstep (se 1 (by rfl) ⟨1268042, by rfl⟩ : syracuseStep 1690723 = 2536085) B2536085
theorem B2255971 : Blo 1334986 2255971 := bstep (se 1 (by rfl) ⟨1691978, by rfl⟩ : syracuseStep 2255971 = 3383957) B3383957
theorem B2854001 : Blo 1334986 2854001 := bstep (se 2 (by rfl) ⟨1070250, by rfl⟩ : syracuseStep 2854001 = 2140501) B2140501
theorem B1502419 : Blo 1334986 1502419 := bstep (se 1 (by rfl) ⟨1126814, by rfl⟩ : syracuseStep 1502419 = 2253629) B2253629
theorem B2534627 : Blo 1334986 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B3804401 : Blo 1334986 3804401 := bstep (se 2 (by rfl) ⟨1426650, by rfl⟩ : syracuseStep 3804401 = 2853301) B2853301
theorem B2256113 : Blo 1334986 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B4508945 : Blo 1334986 4508945 := bstep (se 2 (by rfl) ⟨1690854, by rfl⟩ : syracuseStep 4508945 = 3381709) B3381709
theorem B4115747 : Blo 1334986 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B1502563 : Blo 1334986 1502563 := bstep (se 1 (by rfl) ⟨1126922, by rfl⟩ : syracuseStep 1502563 = 2253845) B2253845
theorem B9629027 : Blo 1334986 9629027 := bstep (se 1 (by rfl) ⟨7221770, by rfl⟩ : syracuseStep 9629027 = 14443541) B14443541
theorem B3804515 : Blo 1334986 3804515 := bstep (se 1 (by rfl) ⟨2853386, by rfl⟩ : syracuseStep 3804515 = 5706773) B5706773
theorem B7613837 : Blo 1334986 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B1502707 : Blo 1334986 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B2534915 : Blo 1334986 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B2002481 : Blo 1334986 2002481 := bstep (se 2 (by rfl) ⟨750930, by rfl⟩ : syracuseStep 2002481 = 1501861) B1501861
theorem B2002499 : Blo 1334986 2002499 := bstep (se 1 (by rfl) ⟨1501874, by rfl⟩ : syracuseStep 2002499 = 3003749) B3003749
theorem B1691219 : Blo 1334986 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B2002529 : Blo 1334986 2002529 := bstep (se 2 (by rfl) ⟨750948, by rfl⟩ : syracuseStep 2002529 = 1501897) B1501897
theorem B2002547 : Blo 1334986 2002547 := bstep (se 1 (by rfl) ⟨1501910, by rfl⟩ : syracuseStep 2002547 = 3003821) B3003821
theorem B1502851 : Blo 1334986 1502851 := bstep (se 1 (by rfl) ⟨1127138, by rfl⟩ : syracuseStep 1502851 = 2254277) B2254277
theorem B2854531 : Blo 1334986 2854531 := bstep (se 1 (by rfl) ⟨2140898, by rfl⟩ : syracuseStep 2854531 = 4281797) B4281797
theorem B2002577 : Blo 1334986 2002577 := bstep (se 2 (by rfl) ⟨750966, by rfl⟩ : syracuseStep 2002577 = 1501933) B1501933
theorem B2002595 : Blo 1334986 2002595 := bstep (se 1 (by rfl) ⟨1501946, by rfl⟩ : syracuseStep 2002595 = 3003893) B3003893
theorem B2002625 : Blo 1334986 2002625 := bstep (se 2 (by rfl) ⟨750984, by rfl⟩ : syracuseStep 2002625 = 1501969) B1501969
theorem B8679109 : Blo 1334986 8679109 := bstep (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) B1627333
theorem B2002643 : Blo 1334986 2002643 := bstep (se 1 (by rfl) ⟨1501982, by rfl⟩ : syracuseStep 2002643 = 3003965) B3003965
theorem B2002673 : Blo 1334986 2002673 := bstep (se 2 (by rfl) ⟨751002, by rfl⟩ : syracuseStep 2002673 = 1502005) B1502005
theorem B2002691 : Blo 1334986 2002691 := bstep (se 1 (by rfl) ⟨1502018, by rfl⟩ : syracuseStep 2002691 = 3004037) B3004037
theorem B7606021 : Blo 1334986 7606021 := bstep (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) B1426129
theorem B1502995 : Blo 1334986 1502995 := bstep (se 1 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 1502995 = 2254493) B2254493
theorem B2002721 : Blo 1334986 2002721 := bstep (se 2 (by rfl) ⟨751020, by rfl⟩ : syracuseStep 2002721 = 1502041) B1502041
theorem B4509485 : Blo 1334986 4509485 := bstep (se 3 (by rfl) ⟨845528, by rfl⟩ : syracuseStep 4509485 = 1691057) B1691057
theorem B2002739 : Blo 1334986 2002739 := bstep (se 1 (by rfl) ⟨1502054, by rfl⟩ : syracuseStep 2002739 = 3004109) B3004109
theorem B2002769 : Blo 1334986 2002769 := bstep (se 2 (by rfl) ⟨751038, by rfl⟩ : syracuseStep 2002769 = 1502077) B1502077
theorem B2002787 : Blo 1334986 2002787 := bstep (se 1 (by rfl) ⟨1502090, by rfl⟩ : syracuseStep 2002787 = 3004181) B3004181
theorem B4509539 : Blo 1334986 4509539 := bstep (se 1 (by rfl) ⟨3382154, by rfl⟩ : syracuseStep 4509539 = 6764309) B6764309
theorem B2002817 : Blo 1334986 2002817 := bstep (se 2 (by rfl) ⟨751056, by rfl⟩ : syracuseStep 2002817 = 1502113) B1502113
theorem B2002835 : Blo 1334986 2002835 := bstep (se 1 (by rfl) ⟨1502126, by rfl⟩ : syracuseStep 2002835 = 3004253) B3004253
theorem B1503139 : Blo 1334986 1503139 := bstep (se 1 (by rfl) ⟨1127354, by rfl⟩ : syracuseStep 1503139 = 2254709) B2254709
theorem B2002865 : Blo 1334986 2002865 := bstep (se 2 (by rfl) ⟨751074, by rfl⟩ : syracuseStep 2002865 = 1502149) B1502149
theorem B2002883 : Blo 1334986 2002883 := bstep (se 1 (by rfl) ⟨1502162, by rfl⟩ : syracuseStep 2002883 = 3004325) B3004325
theorem B2002913 : Blo 1334986 2002913 := bstep (se 2 (by rfl) ⟨751092, by rfl⟩ : syracuseStep 2002913 = 1502185) B1502185
theorem B2002931 : Blo 1334986 2002931 := bstep (se 1 (by rfl) ⟨1502198, by rfl⟩ : syracuseStep 2002931 = 3004397) B3004397
theorem B1544179 : Blo 1334986 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B2002961 : Blo 1334986 2002961 := bstep (se 2 (by rfl) ⟨751110, by rfl⟩ : syracuseStep 2002961 = 1502221) B1502221
theorem B2002979 : Blo 1334986 2002979 := bstep (se 1 (by rfl) ⟨1502234, by rfl⟩ : syracuseStep 2002979 = 3004469) B3004469
theorem B8564771 : Blo 1334986 8564771 := bstep (se 1 (by rfl) ⟨6423578, by rfl⟩ : syracuseStep 8564771 = 12847157) B12847157
theorem B1503283 : Blo 1334986 1503283 := bstep (se 1 (by rfl) ⟨1127462, by rfl⟩ : syracuseStep 1503283 = 2254925) B2254925
theorem B2003009 : Blo 1334986 2003009 := bstep (se 2 (by rfl) ⟨751128, by rfl⟩ : syracuseStep 2003009 = 1502257) B1502257
theorem B2003027 : Blo 1334986 2003027 := bstep (se 1 (by rfl) ⟨1502270, by rfl⟩ : syracuseStep 2003027 = 3004541) B3004541
theorem B2003057 : Blo 1334986 2003057 := bstep (se 2 (by rfl) ⟨751146, by rfl⟩ : syracuseStep 2003057 = 1502293) B1502293
theorem B4509809 : Blo 1334986 4509809 := bstep (se 2 (by rfl) ⟨1691178, by rfl⟩ : syracuseStep 4509809 = 3382357) B3382357
theorem B2003075 : Blo 1334986 2003075 := bstep (se 1 (by rfl) ⟨1502306, by rfl⟩ : syracuseStep 2003075 = 3004613) B3004613
theorem B11571341 : Blo 1334986 11571341 := bstep (se 3 (by rfl) ⟨2169626, by rfl⟩ : syracuseStep 11571341 = 4339253) B4339253
theorem B4280465 : Blo 1334986 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B2003105 : Blo 1334986 2003105 := bstep (se 2 (by rfl) ⟨751164, by rfl⟩ : syracuseStep 2003105 = 1502329) B1502329
theorem B2003123 : Blo 1334986 2003123 := bstep (se 1 (by rfl) ⟨1502342, by rfl⟩ : syracuseStep 2003123 = 3004685) B3004685
theorem B1503427 : Blo 1334986 1503427 := bstep (se 1 (by rfl) ⟨1127570, by rfl⟩ : syracuseStep 1503427 = 2255141) B2255141
theorem B2003153 : Blo 1334986 2003153 := bstep (se 2 (by rfl) ⟨751182, by rfl⟩ : syracuseStep 2003153 = 1502365) B1502365
theorem B4878563 : Blo 1334986 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B2003171 : Blo 1334986 2003171 := bstep (se 1 (by rfl) ⟨1502378, by rfl⟩ : syracuseStep 2003171 = 3004757) B3004757
theorem B3379441 : Blo 1334986 3379441 := bstep (se 2 (by rfl) ⟨1267290, by rfl⟩ : syracuseStep 3379441 = 2534581) B2534581
theorem B2003201 : Blo 1334986 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B2003219 : Blo 1334986 2003219 := bstep (se 1 (by rfl) ⟨1502414, by rfl⟩ : syracuseStep 2003219 = 3004829) B3004829
theorem B42250517 : Blo 1334986 42250517 := bstep (se 6 (by rfl) ⟨990246, by rfl⟩ : syracuseStep 42250517 = 1980493) B1980493
theorem B1691923 : Blo 1334986 1691923 := bstep (se 1 (by rfl) ⟨1268942, by rfl⟩ : syracuseStep 1691923 = 2537885) B2537885
theorem B2003249 : Blo 1334986 2003249 := bstep (se 2 (by rfl) ⟨751218, by rfl⟩ : syracuseStep 2003249 = 1502437) B1502437
theorem B2003267 : Blo 1334986 2003267 := bstep (se 1 (by rfl) ⟨1502450, by rfl⟩ : syracuseStep 2003267 = 3004901) B3004901
theorem B1446211 : Blo 1334986 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B3805517 : Blo 1334986 3805517 := bstep (se 3 (by rfl) ⟨713534, by rfl⟩ : syracuseStep 3805517 = 1427069) B1427069
theorem B1503571 : Blo 1334986 1503571 := bstep (se 1 (by rfl) ⟨1127678, by rfl⟩ : syracuseStep 1503571 = 2255357) B2255357
theorem B2003297 : Blo 1334986 2003297 := bstep (se 2 (by rfl) ⟨751236, by rfl⟩ : syracuseStep 2003297 = 1502473) B1502473
theorem B6762851 : Blo 1334986 6762851 := bstep (se 1 (by rfl) ⟨5072138, by rfl⟩ : syracuseStep 6762851 = 10144277) B10144277
theorem B5140849 : Blo 1334986 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B2003315 : Blo 1334986 2003315 := bstep (se 1 (by rfl) ⟨1502486, by rfl⟩ : syracuseStep 2003315 = 3004973) B3004973
theorem B1692019 : Blo 1334986 1692019 := bstep (se 1 (by rfl) ⟨1269014, by rfl⟩ : syracuseStep 1692019 = 2538029) B2538029
theorem B2003345 : Blo 1334986 2003345 := bstep (se 2 (by rfl) ⟨751254, by rfl⟩ : syracuseStep 2003345 = 1502509) B1502509
theorem B2003363 : Blo 1334986 2003363 := bstep (se 1 (by rfl) ⟨1502522, by rfl⟩ : syracuseStep 2003363 = 3005045) B3005045
theorem B2535857 : Blo 1334986 2535857 := bstep (se 2 (by rfl) ⟨950946, by rfl⟩ : syracuseStep 2535857 = 1901893) B1901893
theorem B2003393 : Blo 1334986 2003393 := bstep (se 2 (by rfl) ⟨751272, by rfl⟩ : syracuseStep 2003393 = 1502545) B1502545
theorem B5075405 : Blo 1334986 5075405 := bstep (se 3 (by rfl) ⟨951638, by rfl⟩ : syracuseStep 5075405 = 1903277) B1903277
theorem B2003411 : Blo 1334986 2003411 := bstep (se 1 (by rfl) ⟨1502558, by rfl⟩ : syracuseStep 2003411 = 3005117) B3005117
theorem B1503715 : Blo 1334986 1503715 := bstep (se 1 (by rfl) ⟨1127786, by rfl⟩ : syracuseStep 1503715 = 2255573) B2255573
theorem B2003441 : Blo 1334986 2003441 := bstep (se 2 (by rfl) ⟨751290, by rfl⟩ : syracuseStep 2003441 = 1502581) B1502581
theorem B3379715 : Blo 1334986 3379715 := bstep (se 1 (by rfl) ⟨2534786, by rfl⟩ : syracuseStep 3379715 = 5069573) B5069573
theorem B2003459 : Blo 1334986 2003459 := bstep (se 1 (by rfl) ⟨1502594, by rfl⟩ : syracuseStep 2003459 = 3005189) B3005189
theorem B3805699 : Blo 1334986 3805699 := bstep (se 1 (by rfl) ⟨2854274, by rfl⟩ : syracuseStep 3805699 = 5708549) B5708549
theorem B2003489 : Blo 1334986 2003489 := bstep (se 2 (by rfl) ⟨751308, by rfl⟩ : syracuseStep 2003489 = 1502617) B1502617
theorem B2003507 : Blo 1334986 2003507 := bstep (se 1 (by rfl) ⟨1502630, by rfl⟩ : syracuseStep 2003507 = 3005261) B3005261
theorem B2003537 : Blo 1334986 2003537 := bstep (se 2 (by rfl) ⟨751326, by rfl⟩ : syracuseStep 2003537 = 1502653) B1502653
theorem B2003555 : Blo 1334986 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B1503859 : Blo 1334986 1503859 := bstep (se 1 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 1503859 = 2255789) B2255789
theorem B2003585 : Blo 1334986 2003585 := bstep (se 2 (by rfl) ⟨751344, by rfl⟩ : syracuseStep 2003585 = 1502689) B1502689
theorem B4510349 : Blo 1334986 4510349 := bstep (se 3 (by rfl) ⟨845690, by rfl⟩ : syracuseStep 4510349 = 1691381) B1691381
theorem B2003603 : Blo 1334986 2003603 := bstep (se 1 (by rfl) ⟨1502702, by rfl⟩ : syracuseStep 2003603 = 3005405) B3005405
theorem B3805859 : Blo 1334986 3805859 := bstep (se 1 (by rfl) ⟨2854394, by rfl⟩ : syracuseStep 3805859 = 5708789) B5708789
theorem B2003633 : Blo 1334986 2003633 := bstep (se 2 (by rfl) ⟨751362, by rfl⟩ : syracuseStep 2003633 = 1502725) B1502725
theorem B3379907 : Blo 1334986 3379907 := bstep (se 1 (by rfl) ⟨2534930, by rfl⟩ : syracuseStep 3379907 = 5069861) B5069861
theorem B2003651 : Blo 1334986 2003651 := bstep (se 1 (by rfl) ⟨1502738, by rfl⟩ : syracuseStep 2003651 = 3005477) B3005477
theorem B4510403 : Blo 1334986 4510403 := bstep (se 1 (by rfl) ⟨3382802, by rfl⟩ : syracuseStep 4510403 = 6765605) B6765605
theorem B2003681 : Blo 1334986 2003681 := bstep (se 2 (by rfl) ⟨751380, by rfl⟩ : syracuseStep 2003681 = 1502761) B1502761
theorem B12841699 : Blo 1334986 12841699 := bstep (se 1 (by rfl) ⟨9631274, by rfl⟩ : syracuseStep 12841699 = 19262549) B19262549
theorem B2003699 : Blo 1334986 2003699 := bstep (se 1 (by rfl) ⟨1502774, by rfl⟩ : syracuseStep 2003699 = 3005549) B3005549
theorem B1504003 : Blo 1334986 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B2003729 : Blo 1334986 2003729 := bstep (se 2 (by rfl) ⟨751398, by rfl⟩ : syracuseStep 2003729 = 1502797) B1502797
theorem B2003747 : Blo 1334986 2003747 := bstep (se 1 (by rfl) ⟨1502810, by rfl⟩ : syracuseStep 2003747 = 3005621) B3005621
theorem B2003777 : Blo 1334986 2003777 := bstep (se 2 (by rfl) ⟨751416, by rfl⟩ : syracuseStep 2003777 = 1502833) B1502833
theorem B2003795 : Blo 1334986 2003795 := bstep (se 1 (by rfl) ⟨1502846, by rfl⟩ : syracuseStep 2003795 = 3005693) B3005693
theorem B2167649 : Blo 1334986 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B2003825 : Blo 1334986 2003825 := bstep (se 2 (by rfl) ⟨751434, by rfl⟩ : syracuseStep 2003825 = 1502869) B1502869
theorem B2003843 : Blo 1334986 2003843 := bstep (se 1 (by rfl) ⟨1502882, by rfl⟩ : syracuseStep 2003843 = 3005765) B3005765
theorem B2003873 : Blo 1334986 2003873 := bstep (se 2 (by rfl) ⟨751452, by rfl⟩ : syracuseStep 2003873 = 1502905) B1502905
theorem B3208099 : Blo 1334986 3208099 := bstep (se 1 (by rfl) ⟨2406074, by rfl⟩ : syracuseStep 3208099 = 4812149) B4812149
theorem B2003891 : Blo 1334986 2003891 := bstep (se 1 (by rfl) ⟨1502918, by rfl⟩ : syracuseStep 2003891 = 3005837) B3005837
theorem B2003921 : Blo 1334986 2003921 := bstep (se 2 (by rfl) ⟨751470, by rfl⟩ : syracuseStep 2003921 = 1502941) B1502941
theorem B4510673 : Blo 1334986 4510673 := bstep (se 2 (by rfl) ⟨1691502, by rfl⟩ : syracuseStep 4510673 = 3383005) B3383005
theorem B1856467 : Blo 1334986 1856467 := bstep (se 1 (by rfl) ⟨1392350, by rfl⟩ : syracuseStep 1856467 = 2784701) B2784701
theorem B2003939 : Blo 1334986 2003939 := bstep (se 1 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 2003939 = 3005909) B3005909
theorem B2003969 : Blo 1334986 2003969 := bstep (se 2 (by rfl) ⟨751488, by rfl⟩ : syracuseStep 2003969 = 1502977) B1502977
theorem B2003987 : Blo 1334986 2003987 := bstep (se 1 (by rfl) ⟨1502990, by rfl⟩ : syracuseStep 2003987 = 3005981) B3005981
theorem B2004017 : Blo 1334986 2004017 := bstep (se 2 (by rfl) ⟨751506, by rfl⟩ : syracuseStep 2004017 = 1503013) B1503013
theorem B2004035 : Blo 1334986 2004035 := bstep (se 1 (by rfl) ⟨1503026, by rfl⟩ : syracuseStep 2004035 = 3006053) B3006053
theorem B2004065 : Blo 1334986 2004065 := bstep (se 2 (by rfl) ⟨751524, by rfl⟩ : syracuseStep 2004065 = 1503049) B1503049
theorem B2708579 : Blo 1334986 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B2004083 : Blo 1334986 2004083 := bstep (se 1 (by rfl) ⟨1503062, by rfl⟩ : syracuseStep 2004083 = 3006125) B3006125
theorem B6763661 : Blo 1334986 6763661 := bstep (se 3 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 6763661 = 2536373) B2536373
theorem B2004113 : Blo 1334986 2004113 := bstep (se 2 (by rfl) ⟨751542, by rfl⟩ : syracuseStep 2004113 = 1503085) B1503085
theorem B2004131 : Blo 1334986 2004131 := bstep (se 1 (by rfl) ⟨1503098, by rfl⟩ : syracuseStep 2004131 = 3006197) B3006197
theorem B2004161 : Blo 1334986 2004161 := bstep (se 2 (by rfl) ⟨751560, by rfl⟩ : syracuseStep 2004161 = 1503121) B1503121
theorem B8344781 : Blo 1334986 8344781 := bstep (se 3 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 8344781 = 3129293) B3129293
theorem B8123597 : Blo 1334986 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B2004179 : Blo 1334986 2004179 := bstep (se 1 (by rfl) ⟨1503134, by rfl⟩ : syracuseStep 2004179 = 3006269) B3006269
theorem B2004209 : Blo 1334986 2004209 := bstep (se 2 (by rfl) ⟨751578, by rfl⟩ : syracuseStep 2004209 = 1503157) B1503157
theorem B5076209 : Blo 1334986 5076209 := bstep (se 2 (by rfl) ⟨1903578, by rfl⟩ : syracuseStep 5076209 = 3807157) B3807157
theorem B2004227 : Blo 1334986 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B2004257 : Blo 1334986 2004257 := bstep (se 2 (by rfl) ⟨751596, by rfl⟩ : syracuseStep 2004257 = 1503193) B1503193
theorem B2536753 : Blo 1334986 2536753 := bstep (se 2 (by rfl) ⟨951282, by rfl⟩ : syracuseStep 2536753 = 1902565) B1902565
theorem B2004275 : Blo 1334986 2004275 := bstep (se 1 (by rfl) ⟨1503206, by rfl⟩ : syracuseStep 2004275 = 3006413) B3006413
theorem B2004305 : Blo 1334986 2004305 := bstep (se 2 (by rfl) ⟨751614, by rfl⟩ : syracuseStep 2004305 = 1503229) B1503229
theorem B2004323 : Blo 1334986 2004323 := bstep (se 1 (by rfl) ⟨1503242, by rfl⟩ : syracuseStep 2004323 = 3006485) B3006485
theorem B21976433 : Blo 1334986 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B2004353 : Blo 1334986 2004353 := bstep (se 2 (by rfl) ⟨751632, by rfl⟩ : syracuseStep 2004353 = 1503265) B1503265
theorem B2004371 : Blo 1334986 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B2004401 : Blo 1334986 2004401 := bstep (se 2 (by rfl) ⟨751650, by rfl⟩ : syracuseStep 2004401 = 1503301) B1503301
theorem B2004419 : Blo 1334986 2004419 := bstep (se 1 (by rfl) ⟨1503314, by rfl⟩ : syracuseStep 2004419 = 3006629) B3006629
theorem B3003857 : Blo 1334986 3003857 := bstep (se 2 (by rfl) ⟨1126446, by rfl⟩ : syracuseStep 3003857 = 2252893) B2252893
theorem B2536913 : Blo 1334986 2536913 := bstep (se 2 (by rfl) ⟨951342, by rfl⟩ : syracuseStep 2536913 = 1902685) B1902685
theorem B2004449 : Blo 1334986 2004449 := bstep (se 2 (by rfl) ⟨751668, by rfl⟩ : syracuseStep 2004449 = 1503337) B1503337
theorem B3003875 : Blo 1334986 3003875 := bstep (se 1 (by rfl) ⟨2252906, by rfl⟩ : syracuseStep 3003875 = 4505813) B4505813
theorem B4511213 : Blo 1334986 4511213 := bstep (se 3 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 4511213 = 1691705) B1691705
theorem B2004467 : Blo 1334986 2004467 := bstep (se 1 (by rfl) ⟨1503350, by rfl⟩ : syracuseStep 2004467 = 3006701) B3006701
theorem B2004497 : Blo 1334986 2004497 := bstep (se 2 (by rfl) ⟨751686, by rfl⟩ : syracuseStep 2004497 = 1503373) B1503373
theorem B2004515 : Blo 1334986 2004515 := bstep (se 1 (by rfl) ⟨1503386, by rfl⟩ : syracuseStep 2004515 = 3006773) B3006773
theorem B4511267 : Blo 1334986 4511267 := bstep (se 1 (by rfl) ⟨3383450, by rfl⟩ : syracuseStep 4511267 = 6766901) B6766901
theorem B2004545 : Blo 1334986 2004545 := bstep (se 2 (by rfl) ⟨751704, by rfl⟩ : syracuseStep 2004545 = 1503409) B1503409
theorem B2004563 : Blo 1334986 2004563 := bstep (se 1 (by rfl) ⟨1503422, by rfl⟩ : syracuseStep 2004563 = 3006845) B3006845
theorem B3380849 : Blo 1334986 3380849 := bstep (se 2 (by rfl) ⟨1267818, by rfl⟩ : syracuseStep 3380849 = 2535637) B2535637
theorem B2004593 : Blo 1334986 2004593 := bstep (se 2 (by rfl) ⟨751722, by rfl⟩ : syracuseStep 2004593 = 1503445) B1503445
theorem B2004611 : Blo 1334986 2004611 := bstep (se 1 (by rfl) ⟨1503458, by rfl⟩ : syracuseStep 2004611 = 3006917) B3006917
theorem B2004641 : Blo 1334986 2004641 := bstep (se 2 (by rfl) ⟨751740, by rfl⟩ : syracuseStep 2004641 = 1503481) B1503481
theorem B3380899 : Blo 1334986 3380899 := bstep (se 1 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 3380899 = 5071349) B5071349
theorem B2709169 : Blo 1334986 2709169 := bstep (se 2 (by rfl) ⟨1015938, by rfl⟩ : syracuseStep 2709169 = 2031877) B2031877
theorem B2004659 : Blo 1334986 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B7608005 : Blo 1334986 7608005 := bstep (se 4 (by rfl) ⟨713250, by rfl⟩ : syracuseStep 7608005 = 1426501) B1426501
theorem B2004689 : Blo 1334986 2004689 := bstep (se 2 (by rfl) ⟨751758, by rfl⟩ : syracuseStep 2004689 = 1503517) B1503517
theorem B3806929 : Blo 1334986 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B34248419 : Blo 1334986 34248419 := bstep (se 1 (by rfl) ⟨25686314, by rfl⟩ : syracuseStep 34248419 = 51372629) B51372629
theorem B2004707 : Blo 1334986 2004707 := bstep (se 1 (by rfl) ⟨1503530, by rfl⟩ : syracuseStep 2004707 = 3007061) B3007061
theorem B3004145 : Blo 1334986 3004145 := bstep (se 2 (by rfl) ⟨1126554, by rfl⟩ : syracuseStep 3004145 = 2253109) B2253109
theorem B2004737 : Blo 1334986 2004737 := bstep (se 2 (by rfl) ⟨751776, by rfl⟩ : syracuseStep 2004737 = 1503553) B1503553
theorem B3004163 : Blo 1334986 3004163 := bstep (se 1 (by rfl) ⟨2253122, by rfl⟩ : syracuseStep 3004163 = 4506245) B4506245
theorem B2004755 : Blo 1334986 2004755 := bstep (se 1 (by rfl) ⟨1503566, by rfl⟩ : syracuseStep 2004755 = 3007133) B3007133
theorem B3381041 : Blo 1334986 3381041 := bstep (se 2 (by rfl) ⟨1267890, by rfl⟩ : syracuseStep 3381041 = 2535781) B2535781
theorem B2004785 : Blo 1334986 2004785 := bstep (se 2 (by rfl) ⟨751794, by rfl⟩ : syracuseStep 2004785 = 1503589) B1503589
theorem B4511537 : Blo 1334986 4511537 := bstep (se 2 (by rfl) ⟨1691826, by rfl⟩ : syracuseStep 4511537 = 3383653) B3383653
theorem B2004803 : Blo 1334986 2004803 := bstep (se 1 (by rfl) ⟨1503602, by rfl⟩ : syracuseStep 2004803 = 3007205) B3007205
theorem B2004833 : Blo 1334986 2004833 := bstep (se 2 (by rfl) ⟨751812, by rfl⟩ : syracuseStep 2004833 = 1503625) B1503625
theorem B2537315 : Blo 1334986 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B2004851 : Blo 1334986 2004851 := bstep (se 1 (by rfl) ⟨1503638, by rfl⟩ : syracuseStep 2004851 = 3007277) B3007277
theorem B2004881 : Blo 1334986 2004881 := bstep (se 2 (by rfl) ⟨751830, by rfl⟩ : syracuseStep 2004881 = 1503661) B1503661
theorem B2004899 : Blo 1334986 2004899 := bstep (se 1 (by rfl) ⟨1503674, by rfl⟩ : syracuseStep 2004899 = 3007349) B3007349
theorem B2004929 : Blo 1334986 2004929 := bstep (se 2 (by rfl) ⟨751848, by rfl⟩ : syracuseStep 2004929 = 1503697) B1503697
theorem B2004947 : Blo 1334986 2004947 := bstep (se 1 (by rfl) ⟨1503710, by rfl⟩ : syracuseStep 2004947 = 3007421) B3007421
theorem B2004977 : Blo 1334986 2004977 := bstep (se 2 (by rfl) ⟨751866, by rfl⟩ : syracuseStep 2004977 = 1503733) B1503733
theorem B2004995 : Blo 1334986 2004995 := bstep (se 1 (by rfl) ⟨1503746, by rfl⟩ : syracuseStep 2004995 = 3007493) B3007493
theorem B3004433 : Blo 1334986 3004433 := bstep (se 2 (by rfl) ⟨1126662, by rfl⟩ : syracuseStep 3004433 = 2253325) B2253325
theorem B2005025 : Blo 1334986 2005025 := bstep (se 2 (by rfl) ⟨751884, by rfl⟩ : syracuseStep 2005025 = 1503769) B1503769
theorem B3004451 : Blo 1334986 3004451 := bstep (se 1 (by rfl) ⟨2253338, by rfl⟩ : syracuseStep 3004451 = 4506677) B4506677
theorem B3610669 : Blo 1334986 3610669 := bstep (se 3 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 3610669 = 1354001) B1354001
theorem B2005043 : Blo 1334986 2005043 := bstep (se 1 (by rfl) ⟨1503782, by rfl⟩ : syracuseStep 2005043 = 3007565) B3007565
theorem B2005073 : Blo 1334986 2005073 := bstep (se 2 (by rfl) ⟨751902, by rfl⟩ : syracuseStep 2005073 = 1503805) B1503805
theorem B2283617 : Blo 1334986 2283617 := bstep (se 2 (by rfl) ⟨856356, by rfl⟩ : syracuseStep 2283617 = 1712713) B1712713
theorem B2005091 : Blo 1334986 2005091 := bstep (se 1 (by rfl) ⟨1503818, by rfl⟩ : syracuseStep 2005091 = 3007637) B3007637
theorem B3209329 : Blo 1334986 3209329 := bstep (se 2 (by rfl) ⟨1203498, by rfl⟩ : syracuseStep 3209329 = 2406997) B2406997
theorem B2005121 : Blo 1334986 2005121 := bstep (se 2 (by rfl) ⟨751920, by rfl⟩ : syracuseStep 2005121 = 1503841) B1503841
theorem B2005139 : Blo 1334986 2005139 := bstep (se 1 (by rfl) ⟨1503854, by rfl⟩ : syracuseStep 2005139 = 3007709) B3007709
theorem B4282541 : Blo 1334986 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B2005169 : Blo 1334986 2005169 := bstep (se 2 (by rfl) ⟨751938, by rfl⟩ : syracuseStep 2005169 = 1503877) B1503877
theorem B2005187 : Blo 1334986 2005187 := bstep (se 1 (by rfl) ⟨1503890, by rfl⟩ : syracuseStep 2005187 = 3007781) B3007781
theorem B2005217 : Blo 1334986 2005217 := bstep (se 2 (by rfl) ⟨751956, by rfl⟩ : syracuseStep 2005217 = 1503913) B1503913
theorem B25663715 : Blo 1334986 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B2005235 : Blo 1334986 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B5413133 : Blo 1334986 5413133 := bstep (se 3 (by rfl) ⟨1014962, by rfl⟩ : syracuseStep 5413133 = 2029925) B2029925
theorem B2005265 : Blo 1334986 2005265 := bstep (se 2 (by rfl) ⟨751974, by rfl⟩ : syracuseStep 2005265 = 1503949) B1503949
theorem B2005283 : Blo 1334986 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B3004721 : Blo 1334986 3004721 := bstep (se 2 (by rfl) ⟨1126770, by rfl⟩ : syracuseStep 3004721 = 2253541) B2253541
theorem B2005313 : Blo 1334986 2005313 := bstep (se 2 (by rfl) ⟨751992, by rfl⟩ : syracuseStep 2005313 = 1503985) B1503985
theorem B3004739 : Blo 1334986 3004739 := bstep (se 1 (by rfl) ⟨2253554, by rfl⟩ : syracuseStep 3004739 = 4507109) B4507109
theorem B10148165 : Blo 1334986 10148165 := bstep (se 4 (by rfl) ⟨951390, by rfl⟩ : syracuseStep 10148165 = 1902781) B1902781
theorem B4512077 : Blo 1334986 4512077 := bstep (se 3 (by rfl) ⟨846014, by rfl⟩ : syracuseStep 4512077 = 1692029) B1692029
theorem B2005331 : Blo 1334986 2005331 := bstep (se 1 (by rfl) ⟨1503998, by rfl⟩ : syracuseStep 2005331 = 3007997) B3007997
theorem B2005361 : Blo 1334986 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B2005379 : Blo 1334986 2005379 := bstep (se 1 (by rfl) ⟨1504034, by rfl⟩ : syracuseStep 2005379 = 3008069) B3008069
theorem B4512131 : Blo 1334986 4512131 := bstep (se 1 (by rfl) ⟨3384098, by rfl⟩ : syracuseStep 4512131 = 6768197) B6768197
theorem B9632141 : Blo 1334986 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B2005409 : Blo 1334986 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B2005427 : Blo 1334986 2005427 := bstep (se 1 (by rfl) ⟨1504070, by rfl⟩ : syracuseStep 2005427 = 3008141) B3008141
theorem B16251317 : Blo 1334986 16251317 := bstep (se 5 (by rfl) ⟨761780, by rfl⟩ : syracuseStep 16251317 = 1523561) B1523561
theorem B8673733 : Blo 1334986 8673733 := bstep (se 4 (by rfl) ⟨813162, by rfl⟩ : syracuseStep 8673733 = 1626325) B1626325
theorem B2005457 : Blo 1334986 2005457 := bstep (se 2 (by rfl) ⟨752046, by rfl⟩ : syracuseStep 2005457 = 1504093) B1504093
theorem B2005475 : Blo 1334986 2005475 := bstep (se 1 (by rfl) ⟨1504106, by rfl⟩ : syracuseStep 2005475 = 3008213) B3008213
theorem B14637581 : Blo 1334986 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B3005009 : Blo 1334986 3005009 := bstep (se 2 (by rfl) ⟨1126878, by rfl⟩ : syracuseStep 3005009 = 2253757) B2253757
theorem B3005027 : Blo 1334986 3005027 := bstep (se 1 (by rfl) ⟨2253770, by rfl⟩ : syracuseStep 3005027 = 4507541) B4507541
theorem B4340387 : Blo 1334986 4340387 := bstep (se 1 (by rfl) ⟨3255290, by rfl⟩ : syracuseStep 4340387 = 6510581) B6510581
theorem B5708465 : Blo 1334986 5708465 := bstep (se 2 (by rfl) ⟨2140674, by rfl⟩ : syracuseStep 5708465 = 4281349) B4281349
theorem B5708515 : Blo 1334986 5708515 := bstep (se 1 (by rfl) ⟨4281386, by rfl⟩ : syracuseStep 5708515 = 8562773) B8562773
theorem B2030321 : Blo 1334986 2030321 := bstep (se 2 (by rfl) ⟨761370, by rfl⟩ : syracuseStep 2030321 = 1522741) B1522741
theorem B3382033 : Blo 1334986 3382033 := bstep (se 2 (by rfl) ⟨1268262, by rfl⟩ : syracuseStep 3382033 = 2536525) B2536525
theorem B2439971 : Blo 1334986 2439971 := bstep (se 1 (by rfl) ⟨1829978, by rfl⟩ : syracuseStep 2439971 = 3659957) B3659957
theorem B3005297 : Blo 1334986 3005297 := bstep (se 2 (by rfl) ⟨1126986, by rfl⟩ : syracuseStep 3005297 = 2253973) B2253973
theorem B3005315 : Blo 1334986 3005315 := bstep (se 1 (by rfl) ⟨2253986, by rfl⟩ : syracuseStep 3005315 = 4507973) B4507973
theorem B3382307 : Blo 1334986 3382307 := bstep (se 1 (by rfl) ⟨2536730, by rfl⟩ : syracuseStep 3382307 = 5073461) B5073461
theorem B6855779 : Blo 1334986 6855779 := bstep (se 1 (by rfl) ⟨5141834, by rfl⟩ : syracuseStep 6855779 = 10283669) B10283669
theorem B3005585 : Blo 1334986 3005585 := bstep (se 2 (by rfl) ⟨1127094, by rfl⟩ : syracuseStep 3005585 = 2254189) B2254189
theorem B3005603 : Blo 1334986 3005603 := bstep (se 1 (by rfl) ⟨2254202, by rfl⟩ : syracuseStep 3005603 = 4508405) B4508405
theorem B2030771 : Blo 1334986 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B3382499 : Blo 1334986 3382499 := bstep (se 1 (by rfl) ⟨2536874, by rfl⟩ : syracuseStep 3382499 = 5073749) B5073749
theorem B2407747 : Blo 1334986 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B2284931 : Blo 1334986 2284931 := bstep (se 1 (by rfl) ⟨1713698, by rfl⟩ : syracuseStep 2284931 = 3427397) B3427397
theorem B3005873 : Blo 1334986 3005873 := bstep (se 2 (by rfl) ⟨1127202, by rfl⟩ : syracuseStep 3005873 = 2254405) B2254405
theorem B3005891 : Blo 1334986 3005891 := bstep (se 1 (by rfl) ⟨2254418, by rfl⟩ : syracuseStep 3005891 = 4508837) B4508837
theorem B4636205 : Blo 1334986 4636205 := bstep (se 3 (by rfl) ⟨869288, by rfl⟩ : syracuseStep 4636205 = 1738577) B1738577
theorem B15425093 : Blo 1334986 15425093 := bstep (se 4 (by rfl) ⟨1446102, by rfl⟩ : syracuseStep 15425093 = 2892205) B2892205
theorem B3006161 : Blo 1334986 3006161 := bstep (se 2 (by rfl) ⟨1127310, by rfl⟩ : syracuseStep 3006161 = 2254621) B2254621
theorem B1334995 : Blo 1334986 1334995 := bstep (se 1 (by rfl) ⟨1001246, by rfl⟩ : syracuseStep 1334995 = 2002493) B2002493
theorem B1335011 : Blo 1334986 1335011 := bstep (se 1 (by rfl) ⟨1001258, by rfl⟩ : syracuseStep 1335011 = 2002517) B2002517
theorem B3006179 : Blo 1334986 3006179 := bstep (se 1 (by rfl) ⟨2254634, by rfl⟩ : syracuseStep 3006179 = 4509269) B4509269
theorem B1335027 : Blo 1334986 1335027 := bstep (se 1 (by rfl) ⟨1001270, by rfl⟩ : syracuseStep 1335027 = 2002541) B2002541
theorem B1335043 : Blo 1334986 1335043 := bstep (se 1 (by rfl) ⟨1001282, by rfl⟩ : syracuseStep 1335043 = 2002565) B2002565
theorem B2285329 : Blo 1334986 2285329 := bstep (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) B1713997
theorem B1335059 : Blo 1334986 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B1335075 : Blo 1334986 1335075 := bstep (se 1 (by rfl) ⟨1001306, by rfl⟩ : syracuseStep 1335075 = 2002613) B2002613
theorem B5414705 : Blo 1334986 5414705 := bstep (se 2 (by rfl) ⟨2030514, by rfl⟩ : syracuseStep 5414705 = 4061029) B4061029
theorem B1335091 : Blo 1334986 1335091 := bstep (se 1 (by rfl) ⟨1001318, by rfl⟩ : syracuseStep 1335091 = 2002637) B2002637
theorem B1335107 : Blo 1334986 1335107 := bstep (se 1 (by rfl) ⟨1001330, by rfl⟩ : syracuseStep 1335107 = 2002661) B2002661
theorem B1335123 : Blo 1334986 1335123 := bstep (se 1 (by rfl) ⟨1001342, by rfl⟩ : syracuseStep 1335123 = 2002685) B2002685
theorem B1335139 : Blo 1334986 1335139 := bstep (se 1 (by rfl) ⟨1001354, by rfl⟩ : syracuseStep 1335139 = 2002709) B2002709
theorem B9756515 : Blo 1334986 9756515 := bstep (se 1 (by rfl) ⟨7317386, by rfl⟩ : syracuseStep 9756515 = 14634773) B14634773
theorem B1335155 : Blo 1334986 1335155 := bstep (se 1 (by rfl) ⟨1001366, by rfl⟩ : syracuseStep 1335155 = 2002733) B2002733
theorem B1335171 : Blo 1334986 1335171 := bstep (se 1 (by rfl) ⟨1001378, by rfl⟩ : syracuseStep 1335171 = 2002757) B2002757
theorem B2408323 : Blo 1334986 2408323 := bstep (se 1 (by rfl) ⟨1806242, by rfl⟩ : syracuseStep 2408323 = 3612485) B3612485
theorem B1335187 : Blo 1334986 1335187 := bstep (se 1 (by rfl) ⟨1001390, by rfl⟩ : syracuseStep 1335187 = 2002781) B2002781
theorem B1335203 : Blo 1334986 1335203 := bstep (se 1 (by rfl) ⟨1001402, by rfl⟩ : syracuseStep 1335203 = 2002805) B2002805
theorem B1335219 : Blo 1334986 1335219 := bstep (se 1 (by rfl) ⟨1001414, by rfl⟩ : syracuseStep 1335219 = 2002829) B2002829
theorem B1335235 : Blo 1334986 1335235 := bstep (se 1 (by rfl) ⟨1001426, by rfl⟩ : syracuseStep 1335235 = 2002853) B2002853
theorem B1335251 : Blo 1334986 1335251 := bstep (se 1 (by rfl) ⟨1001438, by rfl⟩ : syracuseStep 1335251 = 2002877) B2002877
theorem B1605587 : Blo 1334986 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B1335267 : Blo 1334986 1335267 := bstep (se 1 (by rfl) ⟨1001450, by rfl⟩ : syracuseStep 1335267 = 2002901) B2002901
theorem B5070833 : Blo 1334986 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B3006449 : Blo 1334986 3006449 := bstep (se 2 (by rfl) ⟨1127418, by rfl⟩ : syracuseStep 3006449 = 2254837) B2254837
theorem B1335283 : Blo 1334986 1335283 := bstep (se 1 (by rfl) ⟨1001462, by rfl⟩ : syracuseStep 1335283 = 2002925) B2002925
theorem B6766577 : Blo 1334986 6766577 := bstep (se 2 (by rfl) ⟨2537466, by rfl⟩ : syracuseStep 6766577 = 5074933) B5074933
theorem B2572273 : Blo 1334986 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B1335307 : Blo 1334986 1335307 := bstep (se 1 (by rfl) ⟨1001480, by rfl⟩ : syracuseStep 1335307 = 2002961) B2002961
theorem B1335319 : Blo 1334986 1335319 := bstep (se 1 (by rfl) ⟨1001489, by rfl⟩ : syracuseStep 1335319 = 2002979) B2002979
theorem B5709847 : Blo 1334986 5709847 := bstep (se 1 (by rfl) ⟨4282385, by rfl⟩ : syracuseStep 5709847 = 8564771) B8564771
theorem B1335339 : Blo 1334986 1335339 := bstep (se 1 (by rfl) ⟨1001504, by rfl⟩ : syracuseStep 1335339 = 2003009) B2003009
theorem B4505651 : Blo 1334986 4505651 := bstep (se 1 (by rfl) ⟨3379238, by rfl⟩ : syracuseStep 4505651 = 6758477) B6758477
theorem B1335351 : Blo 1334986 1335351 := bstep (se 1 (by rfl) ⟨1001513, by rfl⟩ : syracuseStep 1335351 = 2003027) B2003027
theorem B1335371 : Blo 1334986 1335371 := bstep (se 1 (by rfl) ⟨1001528, by rfl⟩ : syracuseStep 1335371 = 2003057) B2003057
theorem B3006539 : Blo 1334986 3006539 := bstep (se 1 (by rfl) ⟨2254904, by rfl⟩ : syracuseStep 3006539 = 4509809) B4509809
theorem B1335383 : Blo 1334986 1335383 := bstep (se 1 (by rfl) ⟨1001537, by rfl⟩ : syracuseStep 1335383 = 2003075) B2003075
theorem B1335403 : Blo 1334986 1335403 := bstep (se 1 (by rfl) ⟨1001552, by rfl⟩ : syracuseStep 1335403 = 2003105) B2003105
theorem B1335415 : Blo 1334986 1335415 := bstep (se 1 (by rfl) ⟨1001561, by rfl⟩ : syracuseStep 1335415 = 2003123) B2003123
theorem B3006593 : Blo 1334986 3006593 := bstep (se 2 (by rfl) ⟨1127472, by rfl⟩ : syracuseStep 3006593 = 2254945) B2254945
theorem B1335435 : Blo 1334986 1335435 := bstep (se 1 (by rfl) ⟨1001576, by rfl⟩ : syracuseStep 1335435 = 2003153) B2003153
theorem B1335447 : Blo 1334986 1335447 := bstep (se 1 (by rfl) ⟨1001585, by rfl⟩ : syracuseStep 1335447 = 2003171) B2003171
theorem B10141847 : Blo 1334986 10141847 := bstep (se 1 (by rfl) ⟨7606385, by rfl⟩ : syracuseStep 10141847 = 15212771) B15212771
theorem B1335467 : Blo 1334986 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B1335479 : Blo 1334986 1335479 := bstep (se 1 (by rfl) ⟨1001609, by rfl⟩ : syracuseStep 1335479 = 2003219) B2003219
theorem B1335499 : Blo 1334986 1335499 := bstep (se 1 (by rfl) ⟨1001624, by rfl⟩ : syracuseStep 1335499 = 2003249) B2003249
theorem B1335511 : Blo 1334986 1335511 := bstep (se 1 (by rfl) ⟨1001633, by rfl⟩ : syracuseStep 1335511 = 2003267) B2003267
theorem B1335531 : Blo 1334986 1335531 := bstep (se 1 (by rfl) ⟨1001648, by rfl⟩ : syracuseStep 1335531 = 2003297) B2003297
theorem B1335543 : Blo 1334986 1335543 := bstep (se 1 (by rfl) ⟨1001657, by rfl⟩ : syracuseStep 1335543 = 2003315) B2003315
theorem B1335563 : Blo 1334986 1335563 := bstep (se 1 (by rfl) ⟨1001672, by rfl⟩ : syracuseStep 1335563 = 2003345) B2003345
theorem B1335575 : Blo 1334986 1335575 := bstep (se 1 (by rfl) ⟨1001681, by rfl⟩ : syracuseStep 1335575 = 2003363) B2003363
theorem B1335595 : Blo 1334986 1335595 := bstep (se 1 (by rfl) ⟨1001696, by rfl⟩ : syracuseStep 1335595 = 2003393) B2003393
theorem B7610669 : Blo 1334986 7610669 := bstep (se 3 (by rfl) ⟨1427000, by rfl⟩ : syracuseStep 7610669 = 2854001) B2854001
theorem B3383603 : Blo 1334986 3383603 := bstep (se 1 (by rfl) ⟨2537702, by rfl⟩ : syracuseStep 3383603 = 5075405) B5075405
theorem B1425719 : Blo 1334986 1425719 := bstep (se 1 (by rfl) ⟨1069289, by rfl⟩ : syracuseStep 1425719 = 2138579) B2138579
theorem B1335607 : Blo 1334986 1335607 := bstep (se 1 (by rfl) ⟨1001705, by rfl⟩ : syracuseStep 1335607 = 2003411) B2003411
theorem B4505921 : Blo 1334986 4505921 := bstep (se 2 (by rfl) ⟨1689720, by rfl⟩ : syracuseStep 4505921 = 3379441) B3379441
theorem B1335627 : Blo 1334986 1335627 := bstep (se 1 (by rfl) ⟨1001720, by rfl⟩ : syracuseStep 1335627 = 2003441) B2003441
theorem B2253143 : Blo 1334986 2253143 := bstep (se 1 (by rfl) ⟨1689857, by rfl⟩ : syracuseStep 2253143 = 3379715) B3379715
theorem B1335639 : Blo 1334986 1335639 := bstep (se 1 (by rfl) ⟨1001729, by rfl⟩ : syracuseStep 1335639 = 2003459) B2003459
theorem B3006809 : Blo 1334986 3006809 := bstep (se 2 (by rfl) ⟨1127553, by rfl⟩ : syracuseStep 3006809 = 2255107) B2255107
theorem B1335659 : Blo 1334986 1335659 := bstep (se 1 (by rfl) ⟨1001744, by rfl⟩ : syracuseStep 1335659 = 2003489) B2003489
theorem B69394801 : Blo 1334986 69394801 := bstep (se 2 (by rfl) ⟨26023050, by rfl⟩ : syracuseStep 69394801 = 52046101) B52046101
theorem B54804853 : Blo 1334986 54804853 := bstep (se 5 (by rfl) ⟨2568977, by rfl⟩ : syracuseStep 54804853 = 5137955) B5137955
theorem B1335671 : Blo 1334986 1335671 := bstep (se 1 (by rfl) ⟨1001753, by rfl⟩ : syracuseStep 1335671 = 2003507) B2003507
theorem B2744705 : Blo 1334986 2744705 := bstep (se 2 (by rfl) ⟨1029264, by rfl⟩ : syracuseStep 2744705 = 2058529) B2058529
theorem B1335691 : Blo 1334986 1335691 := bstep (se 1 (by rfl) ⟨1001768, by rfl⟩ : syracuseStep 1335691 = 2003537) B2003537
theorem B1335703 : Blo 1334986 1335703 := bstep (se 1 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 1335703 = 2003555) B2003555
theorem B1335723 : Blo 1334986 1335723 := bstep (se 1 (by rfl) ⟨1001792, by rfl⟩ : syracuseStep 1335723 = 2003585) B2003585
theorem B3006899 : Blo 1334986 3006899 := bstep (se 1 (by rfl) ⟨2255174, by rfl⟩ : syracuseStep 3006899 = 4510349) B4510349
theorem B1335735 : Blo 1334986 1335735 := bstep (se 1 (by rfl) ⟨1001801, by rfl⟩ : syracuseStep 1335735 = 2003603) B2003603
theorem B1335755 : Blo 1334986 1335755 := bstep (se 1 (by rfl) ⟨1001816, by rfl⟩ : syracuseStep 1335755 = 2003633) B2003633
theorem B2253271 : Blo 1334986 2253271 := bstep (se 1 (by rfl) ⟨1689953, by rfl⟩ : syracuseStep 2253271 = 3379907) B3379907
theorem B1335767 : Blo 1334986 1335767 := bstep (se 1 (by rfl) ⟨1001825, by rfl⟩ : syracuseStep 1335767 = 2003651) B2003651
theorem B3006935 : Blo 1334986 3006935 := bstep (se 1 (by rfl) ⟨2255201, by rfl⟩ : syracuseStep 3006935 = 4510403) B4510403
theorem B4817369 : Blo 1334986 4817369 := bstep (se 2 (by rfl) ⟨1806513, by rfl⟩ : syracuseStep 4817369 = 3613027) B3613027
theorem B5415389 : Blo 1334986 5415389 := bstep (se 3 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 5415389 = 2030771) B2030771
theorem B1335787 : Blo 1334986 1335787 := bstep (se 1 (by rfl) ⟨1001840, by rfl⟩ : syracuseStep 1335787 = 2003681) B2003681
theorem B1335799 : Blo 1334986 1335799 := bstep (se 1 (by rfl) ⟨1001849, by rfl⟩ : syracuseStep 1335799 = 2003699) B2003699
theorem B1335819 : Blo 1334986 1335819 := bstep (se 1 (by rfl) ⟨1001864, by rfl⟩ : syracuseStep 1335819 = 2003729) B2003729
theorem B1335831 : Blo 1334986 1335831 := bstep (se 1 (by rfl) ⟨1001873, by rfl⟩ : syracuseStep 1335831 = 2003747) B2003747
theorem B1335851 : Blo 1334986 1335851 := bstep (se 1 (by rfl) ⟨1001888, by rfl⟩ : syracuseStep 1335851 = 2003777) B2003777
theorem B1335863 : Blo 1334986 1335863 := bstep (se 1 (by rfl) ⟨1001897, by rfl⟩ : syracuseStep 1335863 = 2003795) B2003795
theorem B1335883 : Blo 1334986 1335883 := bstep (se 1 (by rfl) ⟨1001912, by rfl⟩ : syracuseStep 1335883 = 2003825) B2003825
theorem B4817483 : Blo 1334986 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B1335895 : Blo 1334986 1335895 := bstep (se 1 (by rfl) ⟨1001921, by rfl⟩ : syracuseStep 1335895 = 2003843) B2003843
theorem B13009501 : Blo 1334986 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B1335915 : Blo 1334986 1335915 := bstep (se 1 (by rfl) ⟨1001936, by rfl⟩ : syracuseStep 1335915 = 2003873) B2003873
theorem B1335927 : Blo 1334986 1335927 := bstep (se 1 (by rfl) ⟨1001945, by rfl⟩ : syracuseStep 1335927 = 2003891) B2003891
theorem B1335947 : Blo 1334986 1335947 := bstep (se 1 (by rfl) ⟨1001960, by rfl⟩ : syracuseStep 1335947 = 2003921) B2003921
theorem B3007115 : Blo 1334986 3007115 := bstep (se 1 (by rfl) ⟨2255336, by rfl⟩ : syracuseStep 3007115 = 4510673) B4510673
theorem B1335959 : Blo 1334986 1335959 := bstep (se 1 (by rfl) ⟨1001969, by rfl⟩ : syracuseStep 1335959 = 2003939) B2003939
theorem B1426091 : Blo 1334986 1426091 := bstep (se 1 (by rfl) ⟨1069568, by rfl⟩ : syracuseStep 1426091 = 2139137) B2139137
theorem B1335979 : Blo 1334986 1335979 := bstep (se 1 (by rfl) ⟨1001984, by rfl⟩ : syracuseStep 1335979 = 2003969) B2003969
theorem B1335991 : Blo 1334986 1335991 := bstep (se 1 (by rfl) ⟨1001993, by rfl⟩ : syracuseStep 1335991 = 2003987) B2003987
theorem B3007169 : Blo 1334986 3007169 := bstep (se 2 (by rfl) ⟨1127688, by rfl⟩ : syracuseStep 3007169 = 2255377) B2255377
theorem B1336011 : Blo 1334986 1336011 := bstep (se 1 (by rfl) ⟨1002008, by rfl⟩ : syracuseStep 1336011 = 2004017) B2004017
theorem B1336023 : Blo 1334986 1336023 := bstep (se 1 (by rfl) ⟨1002017, by rfl⟩ : syracuseStep 1336023 = 2004035) B2004035
theorem B1336043 : Blo 1334986 1336043 := bstep (se 1 (by rfl) ⟨1002032, by rfl⟩ : syracuseStep 1336043 = 2004065) B2004065
theorem B2409203 : Blo 1334986 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B1336055 : Blo 1334986 1336055 := bstep (se 1 (by rfl) ⟨1002041, by rfl⟩ : syracuseStep 1336055 = 2004083) B2004083
theorem B1901323 : Blo 1334986 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B1336075 : Blo 1334986 1336075 := bstep (se 1 (by rfl) ⟨1002056, by rfl⟩ : syracuseStep 1336075 = 2004113) B2004113
theorem B1901335 : Blo 1334986 1901335 := bstep (se 1 (by rfl) ⟨1426001, by rfl⟩ : syracuseStep 1901335 = 2852003) B2852003
theorem B1336087 : Blo 1334986 1336087 := bstep (se 1 (by rfl) ⟨1002065, by rfl⟩ : syracuseStep 1336087 = 2004131) B2004131
theorem B1336107 : Blo 1334986 1336107 := bstep (se 1 (by rfl) ⟨1002080, by rfl⟩ : syracuseStep 1336107 = 2004161) B2004161
theorem B5563187 : Blo 1334986 5563187 := bstep (se 1 (by rfl) ⟨4172390, by rfl⟩ : syracuseStep 5563187 = 8344781) B8344781
theorem B5415731 : Blo 1334986 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B1336119 : Blo 1334986 1336119 := bstep (se 1 (by rfl) ⟨1002089, by rfl⟩ : syracuseStep 1336119 = 2004179) B2004179
theorem B1336139 : Blo 1334986 1336139 := bstep (se 1 (by rfl) ⟨1002104, by rfl⟩ : syracuseStep 1336139 = 2004209) B2004209
theorem B3384139 : Blo 1334986 3384139 := bstep (se 1 (by rfl) ⟨2538104, by rfl⟩ : syracuseStep 3384139 = 5076209) B5076209
theorem B1336151 : Blo 1334986 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B4506461 : Blo 1334986 4506461 := bstep (se 3 (by rfl) ⟨844961, by rfl⟩ : syracuseStep 4506461 = 1689923) B1689923
theorem B1336171 : Blo 1334986 1336171 := bstep (se 1 (by rfl) ⟨1002128, by rfl⟩ : syracuseStep 1336171 = 2004257) B2004257
theorem B1336183 : Blo 1334986 1336183 := bstep (se 1 (by rfl) ⟨1002137, by rfl⟩ : syracuseStep 1336183 = 2004275) B2004275
theorem B1336203 : Blo 1334986 1336203 := bstep (se 1 (by rfl) ⟨1002152, by rfl⟩ : syracuseStep 1336203 = 2004305) B2004305
theorem B1336215 : Blo 1334986 1336215 := bstep (se 1 (by rfl) ⟨1002161, by rfl⟩ : syracuseStep 1336215 = 2004323) B2004323
theorem B10290071 : Blo 1334986 10290071 := bstep (se 1 (by rfl) ⟨7717553, by rfl⟩ : syracuseStep 10290071 = 15435107) B15435107
theorem B3007385 : Blo 1334986 3007385 := bstep (se 2 (by rfl) ⟨1127769, by rfl⟩ : syracuseStep 3007385 = 2255539) B2255539
theorem B1336235 : Blo 1334986 1336235 := bstep (se 1 (by rfl) ⟨1002176, by rfl⟩ : syracuseStep 1336235 = 2004353) B2004353
theorem B1336247 : Blo 1334986 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B1336267 : Blo 1334986 1336267 := bstep (se 1 (by rfl) ⟨1002200, by rfl⟩ : syracuseStep 1336267 = 2004401) B2004401
theorem B1336279 : Blo 1334986 1336279 := bstep (se 1 (by rfl) ⟨1002209, by rfl⟩ : syracuseStep 1336279 = 2004419) B2004419
theorem B17122265 : Blo 1334986 17122265 := bstep (se 2 (by rfl) ⟨6420849, by rfl⟩ : syracuseStep 17122265 = 12841699) B12841699
theorem B7611353 : Blo 1334986 7611353 := bstep (se 2 (by rfl) ⟨2854257, by rfl⟩ : syracuseStep 7611353 = 5708515) B5708515
theorem B1336299 : Blo 1334986 1336299 := bstep (se 1 (by rfl) ⟨1002224, by rfl⟩ : syracuseStep 1336299 = 2004449) B2004449
theorem B3007475 : Blo 1334986 3007475 := bstep (se 1 (by rfl) ⟨2255606, by rfl⟩ : syracuseStep 3007475 = 4511213) B4511213
theorem B1336311 : Blo 1334986 1336311 := bstep (se 1 (by rfl) ⟨1002233, by rfl⟩ : syracuseStep 1336311 = 2004467) B2004467
theorem B2851841 : Blo 1334986 2851841 := bstep (se 2 (by rfl) ⟨1069440, by rfl⟩ : syracuseStep 2851841 = 2138881) B2138881
theorem B1336331 : Blo 1334986 1336331 := bstep (se 1 (by rfl) ⟨1002248, by rfl⟩ : syracuseStep 1336331 = 2004497) B2004497
theorem B1336343 : Blo 1334986 1336343 := bstep (se 1 (by rfl) ⟨1002257, by rfl⟩ : syracuseStep 1336343 = 2004515) B2004515
theorem B3007511 : Blo 1334986 3007511 := bstep (se 1 (by rfl) ⟨2255633, by rfl⟩ : syracuseStep 3007511 = 4511267) B4511267
theorem B3048473 : Blo 1334986 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B1336363 : Blo 1334986 1336363 := bstep (se 1 (by rfl) ⟨1002272, by rfl⟩ : syracuseStep 1336363 = 2004545) B2004545
theorem B1336375 : Blo 1334986 1336375 := bstep (se 1 (by rfl) ⟨1002281, by rfl⟩ : syracuseStep 1336375 = 2004563) B2004563
theorem B2253899 : Blo 1334986 2253899 := bstep (se 1 (by rfl) ⟨1690424, by rfl⟩ : syracuseStep 2253899 = 3380849) B3380849
theorem B1336395 : Blo 1334986 1336395 := bstep (se 1 (by rfl) ⟨1002296, by rfl⟩ : syracuseStep 1336395 = 2004593) B2004593
theorem B1336407 : Blo 1334986 1336407 := bstep (se 1 (by rfl) ⟨1002305, by rfl⟩ : syracuseStep 1336407 = 2004611) B2004611
theorem B1336427 : Blo 1334986 1336427 := bstep (se 1 (by rfl) ⟨1002320, by rfl⟩ : syracuseStep 1336427 = 2004641) B2004641
theorem B1336439 : Blo 1334986 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B5072003 : Blo 1334986 5072003 := bstep (se 1 (by rfl) ⟨3804002, by rfl⟩ : syracuseStep 5072003 = 7608005) B7608005
theorem B1336459 : Blo 1334986 1336459 := bstep (se 1 (by rfl) ⟨1002344, by rfl⟩ : syracuseStep 1336459 = 2004689) B2004689
theorem B5072017 : Blo 1334986 5072017 := bstep (se 2 (by rfl) ⟨1902006, by rfl⟩ : syracuseStep 5072017 = 3804013) B3804013
theorem B22832279 : Blo 1334986 22832279 := bstep (se 1 (by rfl) ⟨17124209, by rfl⟩ : syracuseStep 22832279 = 34248419) B34248419
theorem B1336471 : Blo 1334986 1336471 := bstep (se 1 (by rfl) ⟨1002353, by rfl⟩ : syracuseStep 1336471 = 2004707) B2004707
theorem B1336491 : Blo 1334986 1336491 := bstep (se 1 (by rfl) ⟨1002368, by rfl⟩ : syracuseStep 1336491 = 2004737) B2004737
theorem B7603379 : Blo 1334986 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B4064435 : Blo 1334986 4064435 := bstep (se 1 (by rfl) ⟨3048326, by rfl⟩ : syracuseStep 4064435 = 6096653) B6096653
theorem B1336503 : Blo 1334986 1336503 := bstep (se 1 (by rfl) ⟨1002377, by rfl⟩ : syracuseStep 1336503 = 2004755) B2004755
theorem B2254027 : Blo 1334986 2254027 := bstep (se 1 (by rfl) ⟨1690520, by rfl⟩ : syracuseStep 2254027 = 3381041) B3381041
theorem B1336523 : Blo 1334986 1336523 := bstep (se 1 (by rfl) ⟨1002392, by rfl⟩ : syracuseStep 1336523 = 2004785) B2004785
theorem B3007691 : Blo 1334986 3007691 := bstep (se 1 (by rfl) ⟨2255768, by rfl⟩ : syracuseStep 3007691 = 4511537) B4511537
theorem B4277465 : Blo 1334986 4277465 := bstep (se 2 (by rfl) ⟨1604049, by rfl⟩ : syracuseStep 4277465 = 3208099) B3208099
theorem B1336535 : Blo 1334986 1336535 := bstep (se 1 (by rfl) ⟨1002401, by rfl⟩ : syracuseStep 1336535 = 2004803) B2004803
theorem B1336555 : Blo 1334986 1336555 := bstep (se 1 (by rfl) ⟨1002416, by rfl⟩ : syracuseStep 1336555 = 2004833) B2004833
theorem B1336567 : Blo 1334986 1336567 := bstep (se 1 (by rfl) ⟨1002425, by rfl⟩ : syracuseStep 1336567 = 2004851) B2004851
theorem B3007745 : Blo 1334986 3007745 := bstep (se 2 (by rfl) ⟨1127904, by rfl⟩ : syracuseStep 3007745 = 2255809) B2255809
theorem B1336587 : Blo 1334986 1336587 := bstep (se 1 (by rfl) ⟨1002440, by rfl⟩ : syracuseStep 1336587 = 2004881) B2004881
theorem B1336599 : Blo 1334986 1336599 := bstep (se 1 (by rfl) ⟨1002449, by rfl⟩ : syracuseStep 1336599 = 2004899) B2004899
theorem B2475289 : Blo 1334986 2475289 := bstep (se 2 (by rfl) ⟨928233, by rfl⟩ : syracuseStep 2475289 = 1856467) B1856467
theorem B1336619 : Blo 1334986 1336619 := bstep (se 1 (by rfl) ⟨1002464, by rfl⟩ : syracuseStep 1336619 = 2004929) B2004929
theorem B1336631 : Blo 1334986 1336631 := bstep (se 1 (by rfl) ⟨1002473, by rfl⟩ : syracuseStep 1336631 = 2004947) B2004947
theorem B1336651 : Blo 1334986 1336651 := bstep (se 1 (by rfl) ⟨1002488, by rfl⟩ : syracuseStep 1336651 = 2004977) B2004977
theorem B1336663 : Blo 1334986 1336663 := bstep (se 1 (by rfl) ⟨1002497, by rfl⟩ : syracuseStep 1336663 = 2004995) B2004995
theorem B2254169 : Blo 1334986 2254169 := bstep (se 2 (by rfl) ⟨845313, by rfl⟩ : syracuseStep 2254169 = 1690627) B1690627
theorem B6759773 : Blo 1334986 6759773 := bstep (se 3 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 6759773 = 2534915) B2534915
theorem B1336683 : Blo 1334986 1336683 := bstep (se 1 (by rfl) ⟨1002512, by rfl⟩ : syracuseStep 1336683 = 2005025) B2005025
theorem B1336695 : Blo 1334986 1336695 := bstep (se 1 (by rfl) ⟨1002521, by rfl⟩ : syracuseStep 1336695 = 2005043) B2005043
theorem B1336715 : Blo 1334986 1336715 := bstep (se 1 (by rfl) ⟨1002536, by rfl⟩ : syracuseStep 1336715 = 2005073) B2005073
theorem B1336727 : Blo 1334986 1336727 := bstep (se 1 (by rfl) ⟨1002545, by rfl⟩ : syracuseStep 1336727 = 2005091) B2005091
theorem B1336747 : Blo 1334986 1336747 := bstep (se 1 (by rfl) ⟨1002560, by rfl⟩ : syracuseStep 1336747 = 2005121) B2005121
theorem B1336759 : Blo 1334986 1336759 := bstep (se 1 (by rfl) ⟨1002569, by rfl⟩ : syracuseStep 1336759 = 2005139) B2005139
theorem B5072321 : Blo 1334986 5072321 := bstep (se 2 (by rfl) ⟨1902120, by rfl⟩ : syracuseStep 5072321 = 3804241) B3804241
theorem B1336779 : Blo 1334986 1336779 := bstep (se 1 (by rfl) ⟨1002584, by rfl⟩ : syracuseStep 1336779 = 2005169) B2005169
theorem B1336791 : Blo 1334986 1336791 := bstep (se 1 (by rfl) ⟨1002593, by rfl⟩ : syracuseStep 1336791 = 2005187) B2005187
theorem B2254297 : Blo 1334986 2254297 := bstep (se 2 (by rfl) ⟨845361, by rfl⟩ : syracuseStep 2254297 = 1690723) B1690723
theorem B3007961 : Blo 1334986 3007961 := bstep (se 2 (by rfl) ⟨1127985, by rfl⟩ : syracuseStep 3007961 = 2255971) B2255971
theorem B1336811 : Blo 1334986 1336811 := bstep (se 1 (by rfl) ⟨1002608, by rfl⟩ : syracuseStep 1336811 = 2005217) B2005217
theorem B1336823 : Blo 1334986 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B1336843 : Blo 1334986 1336843 := bstep (se 1 (by rfl) ⟨1002632, by rfl⟩ : syracuseStep 1336843 = 2005265) B2005265
theorem B1336855 : Blo 1334986 1336855 := bstep (se 1 (by rfl) ⟨1002641, by rfl⟩ : syracuseStep 1336855 = 2005283) B2005283
theorem B1336875 : Blo 1334986 1336875 := bstep (se 1 (by rfl) ⟨1002656, by rfl⟩ : syracuseStep 1336875 = 2005313) B2005313
theorem B3008051 : Blo 1334986 3008051 := bstep (se 1 (by rfl) ⟨2256038, by rfl⟩ : syracuseStep 3008051 = 4512077) B4512077
theorem B1336887 : Blo 1334986 1336887 := bstep (se 1 (by rfl) ⟨1002665, by rfl⟩ : syracuseStep 1336887 = 2005331) B2005331
theorem B1336907 : Blo 1334986 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B1336919 : Blo 1334986 1336919 := bstep (se 1 (by rfl) ⟨1002689, by rfl⟩ : syracuseStep 1336919 = 2005379) B2005379
theorem B3008087 : Blo 1334986 3008087 := bstep (se 1 (by rfl) ⟨2256065, by rfl⟩ : syracuseStep 3008087 = 4512131) B4512131
theorem B1336939 : Blo 1334986 1336939 := bstep (se 1 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 1336939 = 2005409) B2005409
theorem B1336951 : Blo 1334986 1336951 := bstep (se 1 (by rfl) ⟨1002713, by rfl⟩ : syracuseStep 1336951 = 2005427) B2005427
theorem B1336971 : Blo 1334986 1336971 := bstep (se 1 (by rfl) ⟨1002728, by rfl⟩ : syracuseStep 1336971 = 2005457) B2005457
theorem B1427095 : Blo 1334986 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B1336983 : Blo 1334986 1336983 := bstep (se 1 (by rfl) ⟨1002737, by rfl⟩ : syracuseStep 1336983 = 2005475) B2005475
theorem B9758387 : Blo 1334986 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B2893591 : Blo 1334986 2893591 := bstep (se 1 (by rfl) ⟨2170193, by rfl⟩ : syracuseStep 2893591 = 4340387) B4340387
theorem B1353547 : Blo 1334986 1353547 := bstep (se 1 (by rfl) ⟨1015160, by rfl⟩ : syracuseStep 1353547 = 2030321) B2030321
theorem B4507595 : Blo 1334986 4507595 := bstep (se 1 (by rfl) ⟨3380696, by rfl⟩ : syracuseStep 4507595 = 6761393) B6761393
theorem B2254871 : Blo 1334986 2254871 := bstep (se 1 (by rfl) ⟨1691153, by rfl⟩ : syracuseStep 2254871 = 3382307) B3382307
theorem B5072989 : Blo 1334986 5072989 := bstep (se 3 (by rfl) ⟨951185, by rfl⟩ : syracuseStep 5072989 = 1902371) B1902371
theorem B1689751 : Blo 1334986 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B2254999 : Blo 1334986 2254999 := bstep (se 1 (by rfl) ⟨1691249, by rfl⟩ : syracuseStep 2254999 = 3382499) B3382499
theorem B4507865 : Blo 1334986 4507865 := bstep (se 2 (by rfl) ⟨1690449, by rfl⟩ : syracuseStep 4507865 = 3380899) B3380899
theorem B4065497 : Blo 1334986 4065497 := bstep (se 2 (by rfl) ⟨1524561, by rfl⟩ : syracuseStep 4065497 = 3049123) B3049123
theorem B3090803 : Blo 1334986 3090803 := bstep (se 1 (by rfl) ⟨2318102, by rfl⟩ : syracuseStep 3090803 = 4636205) B4636205
theorem B10283395 : Blo 1334986 10283395 := bstep (se 1 (by rfl) ⟨7712546, by rfl⟩ : syracuseStep 10283395 = 15425093) B15425093
theorem B7604837 : Blo 1334986 7604837 := bstep (se 4 (by rfl) ⟨712953, by rfl⟩ : syracuseStep 7604837 = 1425907) B1425907
theorem B2058905 : Blo 1334986 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B11414195 : Blo 1334986 11414195 := bstep (se 1 (by rfl) ⟨8560646, by rfl⟩ : syracuseStep 11414195 = 17121293) B17121293
theorem B1501879 : Blo 1334986 1501879 := bstep (se 1 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 1501879 = 2252819) B2252819
theorem B2853643 : Blo 1334986 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B2255627 : Blo 1334986 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B1903385 : Blo 1334986 1903385 := bstep (se 2 (by rfl) ⟨713769, by rfl⟩ : syracuseStep 1903385 = 1427539) B1427539
theorem B4279105 : Blo 1334986 4279105 := bstep (se 2 (by rfl) ⟨1604664, by rfl⟩ : syracuseStep 4279105 = 3209329) B3209329
theorem B28167011 : Blo 1334986 28167011 := bstep (se 1 (by rfl) ⟨21125258, by rfl⟩ : syracuseStep 28167011 = 42250517) B42250517
theorem B1502059 : Blo 1334986 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B2255755 : Blo 1334986 2255755 := bstep (se 1 (by rfl) ⟨1691816, by rfl⟩ : syracuseStep 2255755 = 3383633) B3383633
theorem B4508567 : Blo 1334986 4508567 := bstep (se 1 (by rfl) ⟨3381425, by rfl⟩ : syracuseStep 4508567 = 6762851) B6762851
theorem B6089645 : Blo 1334986 6089645 := bstep (se 3 (by rfl) ⟨1141808, by rfl⟩ : syracuseStep 6089645 = 2283617) B2283617
theorem B1690571 : Blo 1334986 1690571 := bstep (se 1 (by rfl) ⟨1267928, by rfl⟩ : syracuseStep 1690571 = 2535857) B2535857
theorem B1502167 : Blo 1334986 1502167 := bstep (se 1 (by rfl) ⟨1126625, by rfl⟩ : syracuseStep 1502167 = 2253251) B2253251
theorem B2255897 : Blo 1334986 2255897 := bstep (se 2 (by rfl) ⟨845961, by rfl⟩ : syracuseStep 2255897 = 1691923) B1691923
theorem B1928281 : Blo 1334986 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B1502347 : Blo 1334986 1502347 := bstep (se 1 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 1502347 = 2253521) B2253521
theorem B2256025 : Blo 1334986 2256025 := bstep (se 2 (by rfl) ⟨846009, by rfl⟩ : syracuseStep 2256025 = 1692019) B1692019
theorem B1445099 : Blo 1334986 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B1502455 : Blo 1334986 1502455 := bstep (se 1 (by rfl) ⟨1126841, by rfl⟩ : syracuseStep 1502455 = 2253683) B2253683
theorem B7605521 : Blo 1334986 7605521 := bstep (se 2 (by rfl) ⟨2852070, by rfl⟩ : syracuseStep 7605521 = 5704141) B5704141
theorem B5074265 : Blo 1334986 5074265 := bstep (se 2 (by rfl) ⟨1902849, by rfl⟩ : syracuseStep 5074265 = 3805699) B3805699
theorem B6761879 : Blo 1334986 6761879 := bstep (se 1 (by rfl) ⟨5071409, by rfl⟩ : syracuseStep 6761879 = 10142819) B10142819
theorem B2534809 : Blo 1334986 2534809 := bstep (se 2 (by rfl) ⟨950553, by rfl⟩ : syracuseStep 2534809 = 1901107) B1901107
theorem B1502635 : Blo 1334986 1502635 := bstep (se 1 (by rfl) ⟨1126976, by rfl⟩ : syracuseStep 1502635 = 2253953) B2253953
theorem B4509107 : Blo 1334986 4509107 := bstep (se 1 (by rfl) ⟨3381830, by rfl⟩ : syracuseStep 4509107 = 6763661) B6763661
theorem B1502743 : Blo 1334986 1502743 := bstep (se 1 (by rfl) ⟨1127057, by rfl⟩ : syracuseStep 1502743 = 2254115) B2254115
theorem B14650955 : Blo 1334986 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B2002571 : Blo 1334986 2002571 := bstep (se 1 (by rfl) ⟨1501928, by rfl⟩ : syracuseStep 2002571 = 3003857) B3003857
theorem B1691275 : Blo 1334986 1691275 := bstep (se 1 (by rfl) ⟨1268456, by rfl⟩ : syracuseStep 1691275 = 2536913) B2536913
theorem B2002583 : Blo 1334986 2002583 := bstep (se 1 (by rfl) ⟨1501937, by rfl⟩ : syracuseStep 2002583 = 3003875) B3003875
theorem B4509377 : Blo 1334986 4509377 := bstep (se 2 (by rfl) ⟨1691016, by rfl⟩ : syracuseStep 4509377 = 3382033) B3382033
theorem B1502923 : Blo 1334986 1502923 := bstep (se 1 (by rfl) ⟨1127192, by rfl⟩ : syracuseStep 1502923 = 2254385) B2254385
theorem B2002649 : Blo 1334986 2002649 := bstep (se 2 (by rfl) ⟨750993, by rfl⟩ : syracuseStep 2002649 = 1501987) B1501987
theorem B1503031 : Blo 1334986 1503031 := bstep (se 1 (by rfl) ⟨1127273, by rfl⟩ : syracuseStep 1503031 = 2254547) B2254547
theorem B2002763 : Blo 1334986 2002763 := bstep (se 1 (by rfl) ⟨1502072, by rfl⟩ : syracuseStep 2002763 = 3004145) B3004145
theorem B2002775 : Blo 1334986 2002775 := bstep (se 1 (by rfl) ⟨1502081, by rfl⟩ : syracuseStep 2002775 = 3004163) B3004163
theorem B5418845 : Blo 1334986 5418845 := bstep (se 3 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 5418845 = 2032067) B2032067
theorem B1691543 : Blo 1334986 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B2002841 : Blo 1334986 2002841 := bstep (se 2 (by rfl) ⟨751065, by rfl⟩ : syracuseStep 2002841 = 1502131) B1502131
theorem B2535371 : Blo 1334986 2535371 := bstep (se 1 (by rfl) ⟨1901528, by rfl⟩ : syracuseStep 2535371 = 3803057) B3803057
theorem B1503211 : Blo 1334986 1503211 := bstep (se 1 (by rfl) ⟨1127408, by rfl⟩ : syracuseStep 1503211 = 2254817) B2254817
theorem B2002955 : Blo 1334986 2002955 := bstep (se 1 (by rfl) ⟨1502216, by rfl⟩ : syracuseStep 2002955 = 3004433) B3004433
theorem B2002967 : Blo 1334986 2002967 := bstep (se 1 (by rfl) ⟨1502225, by rfl⟩ : syracuseStep 2002967 = 3004451) B3004451
theorem B1503319 : Blo 1334986 1503319 := bstep (se 1 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 1503319 = 2254979) B2254979
theorem B2003033 : Blo 1334986 2003033 := bstep (se 2 (by rfl) ⟨751137, by rfl⟩ : syracuseStep 2003033 = 1502275) B1502275
theorem B2855027 : Blo 1334986 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B2535553 : Blo 1334986 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B17109143 : Blo 1334986 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B1929367 : Blo 1334986 1929367 := bstep (se 1 (by rfl) ⟨1447025, by rfl⟩ : syracuseStep 1929367 = 2894051) B2894051
theorem B5419181 : Blo 1334986 5419181 := bstep (se 3 (by rfl) ⟨1016096, by rfl⟩ : syracuseStep 5419181 = 2032193) B2032193
theorem B3608755 : Blo 1334986 3608755 := bstep (se 1 (by rfl) ⟨2706566, by rfl⟩ : syracuseStep 3608755 = 5413133) B5413133
theorem B2003147 : Blo 1334986 2003147 := bstep (se 1 (by rfl) ⟨1502360, by rfl⟩ : syracuseStep 2003147 = 3004721) B3004721
theorem B2003159 : Blo 1334986 2003159 := bstep (se 1 (by rfl) ⟨1502369, by rfl⟩ : syracuseStep 2003159 = 3004739) B3004739
theorem B4509917 : Blo 1334986 4509917 := bstep (se 3 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 4509917 = 1691219) B1691219
theorem B1503499 : Blo 1334986 1503499 := bstep (se 1 (by rfl) ⟨1127624, by rfl⟩ : syracuseStep 1503499 = 2255249) B2255249
theorem B2003225 : Blo 1334986 2003225 := bstep (se 2 (by rfl) ⟨751209, by rfl⟩ : syracuseStep 2003225 = 1502419) B1502419
theorem B10834211 : Blo 1334986 10834211 := bstep (se 1 (by rfl) ⟨8125658, by rfl⟩ : syracuseStep 10834211 = 16251317) B16251317
theorem B1503607 : Blo 1334986 1503607 := bstep (se 1 (by rfl) ⟨1127705, by rfl⟩ : syracuseStep 1503607 = 2255411) B2255411
theorem B2003339 : Blo 1334986 2003339 := bstep (se 1 (by rfl) ⟨1502504, by rfl⟩ : syracuseStep 2003339 = 3005009) B3005009
theorem B2003351 : Blo 1334986 2003351 := bstep (se 1 (by rfl) ⟨1502513, by rfl⟩ : syracuseStep 2003351 = 3005027) B3005027
theorem B3805643 : Blo 1334986 3805643 := bstep (se 1 (by rfl) ⟨2854232, by rfl⟩ : syracuseStep 3805643 = 5708465) B5708465
theorem B2003417 : Blo 1334986 2003417 := bstep (se 2 (by rfl) ⟨751281, by rfl⟩ : syracuseStep 2003417 = 1502563) B1502563
theorem B1626647 : Blo 1334986 1626647 := bstep (se 1 (by rfl) ⟨1219985, by rfl⟩ : syracuseStep 1626647 = 2439971) B2439971
theorem B1503787 : Blo 1334986 1503787 := bstep (se 1 (by rfl) ⟨1127840, by rfl⟩ : syracuseStep 1503787 = 2255681) B2255681
theorem B2003531 : Blo 1334986 2003531 := bstep (se 1 (by rfl) ⟨1502648, by rfl⟩ : syracuseStep 2003531 = 3005297) B3005297
theorem B2003543 : Blo 1334986 2003543 := bstep (se 1 (by rfl) ⟨1502657, by rfl⟩ : syracuseStep 2003543 = 3005315) B3005315
theorem B1503895 : Blo 1334986 1503895 := bstep (se 1 (by rfl) ⟨1127921, by rfl⟩ : syracuseStep 1503895 = 2255843) B2255843
theorem B2003609 : Blo 1334986 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B2003723 : Blo 1334986 2003723 := bstep (se 1 (by rfl) ⟨1502792, by rfl⟩ : syracuseStep 2003723 = 3005585) B3005585
theorem B2003735 : Blo 1334986 2003735 := bstep (se 1 (by rfl) ⟨1502801, by rfl⟩ : syracuseStep 2003735 = 3005603) B3005603
theorem B2536267 : Blo 1334986 2536267 := bstep (se 1 (by rfl) ⟨1902200, by rfl⟩ : syracuseStep 2536267 = 3804401) B3804401
theorem B1504075 : Blo 1334986 1504075 := bstep (se 1 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 1504075 = 2256113) B2256113
theorem B2003801 : Blo 1334986 2003801 := bstep (se 2 (by rfl) ⟨751425, by rfl⟩ : syracuseStep 2003801 = 1502851) B1502851
theorem B3806041 : Blo 1334986 3806041 := bstep (se 2 (by rfl) ⟨1427265, by rfl⟩ : syracuseStep 3806041 = 2854531) B2854531
theorem B17126261 : Blo 1334986 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B6419351 : Blo 1334986 6419351 := bstep (se 1 (by rfl) ⟨4814513, by rfl⟩ : syracuseStep 6419351 = 9629027) B9629027
theorem B2536343 : Blo 1334986 2536343 := bstep (se 1 (by rfl) ⟨1902257, by rfl⟩ : syracuseStep 2536343 = 3804515) B3804515
theorem B11572145 : Blo 1334986 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B5075891 : Blo 1334986 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B5075905 : Blo 1334986 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B2003915 : Blo 1334986 2003915 := bstep (se 1 (by rfl) ⟨1502936, by rfl⟩ : syracuseStep 2003915 = 3005873) B3005873
theorem B2003927 : Blo 1334986 2003927 := bstep (se 1 (by rfl) ⟨1502945, by rfl⟩ : syracuseStep 2003927 = 3005891) B3005891
theorem B2003993 : Blo 1334986 2003993 := bstep (se 2 (by rfl) ⟨751497, by rfl⟩ : syracuseStep 2003993 = 1502995) B1502995
theorem B11408485 : Blo 1334986 11408485 := bstep (se 4 (by rfl) ⟨1069545, by rfl⟩ : syracuseStep 11408485 = 2139091) B2139091
theorem B2004107 : Blo 1334986 2004107 := bstep (se 1 (by rfl) ⟨1503080, by rfl⟩ : syracuseStep 2004107 = 3006161) B3006161
theorem B2004119 : Blo 1334986 2004119 := bstep (se 1 (by rfl) ⟨1503089, by rfl⟩ : syracuseStep 2004119 = 3006179) B3006179
theorem B3609803 : Blo 1334986 3609803 := bstep (se 1 (by rfl) ⟨2707352, by rfl⟩ : syracuseStep 3609803 = 5414705) B5414705
theorem B2004185 : Blo 1334986 2004185 := bstep (se 2 (by rfl) ⟨751569, by rfl⟩ : syracuseStep 2004185 = 1503139) B1503139
theorem B3429697 : Blo 1334986 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B3380555 : Blo 1334986 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2004299 : Blo 1334986 2004299 := bstep (se 1 (by rfl) ⟨1503224, by rfl⟩ : syracuseStep 2004299 = 3006449) B3006449
theorem B4511051 : Blo 1334986 4511051 := bstep (se 1 (by rfl) ⟨3383288, by rfl⟩ : syracuseStep 4511051 = 6766577) B6766577
theorem B2004311 : Blo 1334986 2004311 := bstep (se 1 (by rfl) ⟨1503233, by rfl⟩ : syracuseStep 2004311 = 3006467) B3006467
theorem B4814225 : Blo 1334986 4814225 := bstep (se 2 (by rfl) ⟨1805334, by rfl⟩ : syracuseStep 4814225 = 3610669) B3610669
theorem B2004377 : Blo 1334986 2004377 := bstep (se 2 (by rfl) ⟨751641, by rfl⟩ : syracuseStep 2004377 = 1503283) B1503283
theorem B2004491 : Blo 1334986 2004491 := bstep (se 1 (by rfl) ⟨1503368, by rfl⟩ : syracuseStep 2004491 = 3006737) B3006737
theorem B2004503 : Blo 1334986 2004503 := bstep (se 1 (by rfl) ⟨1503377, by rfl⟩ : syracuseStep 2004503 = 3006755) B3006755
theorem B3003929 : Blo 1334986 3003929 := bstep (se 2 (by rfl) ⟨1126473, by rfl⟩ : syracuseStep 3003929 = 2252947) B2252947
theorem B2537011 : Blo 1334986 2537011 := bstep (se 1 (by rfl) ⟨1902758, by rfl⟩ : syracuseStep 2537011 = 3805517) B3805517
theorem B2405953 : Blo 1334986 2405953 := bstep (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) B1804465
theorem B2004569 : Blo 1334986 2004569 := bstep (se 2 (by rfl) ⟨751713, by rfl⟩ : syracuseStep 2004569 = 1503427) B1503427
theorem B4511321 : Blo 1334986 4511321 := bstep (se 2 (by rfl) ⟨1691745, by rfl⟩ : syracuseStep 4511321 = 3383491) B3383491
theorem B7222877 : Blo 1334986 7222877 := bstep (se 3 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 7222877 = 2708579) B2708579
theorem B3004019 : Blo 1334986 3004019 := bstep (se 1 (by rfl) ⟨2253014, by rfl⟩ : syracuseStep 3004019 = 4506029) B4506029
theorem B2406017 : Blo 1334986 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B3004055 : Blo 1334986 3004055 := bstep (se 1 (by rfl) ⟨2253041, by rfl⟩ : syracuseStep 3004055 = 4506083) B4506083
theorem B2004683 : Blo 1334986 2004683 := bstep (se 1 (by rfl) ⟨1503512, by rfl⟩ : syracuseStep 2004683 = 3007025) B3007025
theorem B2004695 : Blo 1334986 2004695 := bstep (se 1 (by rfl) ⟨1503521, by rfl⟩ : syracuseStep 2004695 = 3007043) B3007043
theorem B5707523 : Blo 1334986 5707523 := bstep (se 1 (by rfl) ⟨4280642, by rfl⟩ : syracuseStep 5707523 = 8561285) B8561285
theorem B2537239 : Blo 1334986 2537239 := bstep (se 1 (by rfl) ⟨1902929, by rfl⟩ : syracuseStep 2537239 = 3805859) B3805859
theorem B2004761 : Blo 1334986 2004761 := bstep (se 2 (by rfl) ⟨751785, by rfl⟩ : syracuseStep 2004761 = 1503571) B1503571
theorem B6854465 : Blo 1334986 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B3004235 : Blo 1334986 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B3004289 : Blo 1334986 3004289 := bstep (se 2 (by rfl) ⟨1126608, by rfl⟩ : syracuseStep 3004289 = 2253217) B2253217
theorem B2537345 : Blo 1334986 2537345 := bstep (se 2 (by rfl) ⟨951504, by rfl⟩ : syracuseStep 2537345 = 1903009) B1903009
theorem B2004875 : Blo 1334986 2004875 := bstep (se 1 (by rfl) ⟨1503656, by rfl⟩ : syracuseStep 2004875 = 3007313) B3007313
theorem B2004887 : Blo 1334986 2004887 := bstep (se 1 (by rfl) ⟨1503665, by rfl⟩ : syracuseStep 2004887 = 3007331) B3007331
theorem B11564977 : Blo 1334986 11564977 := bstep (se 2 (by rfl) ⟨4336866, by rfl⟩ : syracuseStep 11564977 = 8673733) B8673733
theorem B2004953 : Blo 1334986 2004953 := bstep (se 2 (by rfl) ⟨751857, by rfl⟩ : syracuseStep 2004953 = 1503715) B1503715
theorem B2537497 : Blo 1334986 2537497 := bstep (se 2 (by rfl) ⟨951561, by rfl⟩ : syracuseStep 2537497 = 1903123) B1903123
theorem B11409443 : Blo 1334986 11409443 := bstep (se 1 (by rfl) ⟨8557082, by rfl⟩ : syracuseStep 11409443 = 17114165) B17114165
theorem B2005067 : Blo 1334986 2005067 := bstep (se 1 (by rfl) ⟨1503800, by rfl⟩ : syracuseStep 2005067 = 3007601) B3007601
theorem B2005079 : Blo 1334986 2005079 := bstep (se 1 (by rfl) ⟨1503809, by rfl⟩ : syracuseStep 2005079 = 3007619) B3007619
theorem B5068889 : Blo 1334986 5068889 := bstep (se 2 (by rfl) ⟨1900833, by rfl⟩ : syracuseStep 5068889 = 3801667) B3801667
theorem B3004505 : Blo 1334986 3004505 := bstep (se 2 (by rfl) ⟨1126689, by rfl⟩ : syracuseStep 3004505 = 2253379) B2253379
theorem B8558723 : Blo 1334986 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B2005145 : Blo 1334986 2005145 := bstep (se 2 (by rfl) ⟨751929, by rfl⟩ : syracuseStep 2005145 = 1503859) B1503859
theorem B3004595 : Blo 1334986 3004595 := bstep (se 1 (by rfl) ⟨2253446, by rfl⟩ : syracuseStep 3004595 = 4506893) B4506893
theorem B3004631 : Blo 1334986 3004631 := bstep (se 1 (by rfl) ⟨2253473, by rfl⟩ : syracuseStep 3004631 = 4506947) B4506947
theorem B2439385 : Blo 1334986 2439385 := bstep (se 2 (by rfl) ⟨914769, by rfl⟩ : syracuseStep 2439385 = 1829539) B1829539
theorem B14448901 : Blo 1334986 14448901 := bstep (se 4 (by rfl) ⟨1354584, by rfl⟩ : syracuseStep 14448901 = 2709169) B2709169
theorem B2005259 : Blo 1334986 2005259 := bstep (se 1 (by rfl) ⟨1503944, by rfl⟩ : syracuseStep 2005259 = 3007889) B3007889
theorem B3381527 : Blo 1334986 3381527 := bstep (se 1 (by rfl) ⟨2536145, by rfl⟩ : syracuseStep 3381527 = 5072291) B5072291
theorem B2005271 : Blo 1334986 2005271 := bstep (se 1 (by rfl) ⟨1503953, by rfl⟩ : syracuseStep 2005271 = 3007907) B3007907
theorem B4512023 : Blo 1334986 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B5069101 : Blo 1334986 5069101 := bstep (se 3 (by rfl) ⟨950456, by rfl⟩ : syracuseStep 5069101 = 1900913) B1900913
theorem B74168621 : Blo 1334986 74168621 := bstep (se 3 (by rfl) ⟨13906616, by rfl⟩ : syracuseStep 74168621 = 27813233) B27813233
theorem B2005337 : Blo 1334986 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B3004811 : Blo 1334986 3004811 := bstep (se 1 (by rfl) ⟨2253608, by rfl⟩ : syracuseStep 3004811 = 4507217) B4507217
theorem B7608755 : Blo 1334986 7608755 := bstep (se 1 (by rfl) ⟨5706566, by rfl⟩ : syracuseStep 7608755 = 11413133) B11413133
theorem B3004865 : Blo 1334986 3004865 := bstep (se 2 (by rfl) ⟨1126824, by rfl⟩ : syracuseStep 3004865 = 2253649) B2253649
theorem B2005451 : Blo 1334986 2005451 := bstep (se 1 (by rfl) ⟨1504088, by rfl⟩ : syracuseStep 2005451 = 3008177) B3008177
theorem B2005463 : Blo 1334986 2005463 := bstep (se 1 (by rfl) ⟨1504097, by rfl⟩ : syracuseStep 2005463 = 3008195) B3008195
theorem B5069405 : Blo 1334986 5069405 := bstep (se 3 (by rfl) ⟨950513, by rfl⟩ : syracuseStep 5069405 = 1901027) B1901027
theorem B3005081 : Blo 1334986 3005081 := bstep (se 2 (by rfl) ⟨1126905, by rfl⟩ : syracuseStep 3005081 = 2253811) B2253811
theorem B10828505 : Blo 1334986 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B3005171 : Blo 1334986 3005171 := bstep (se 1 (by rfl) ⟨2253878, by rfl⟩ : syracuseStep 3005171 = 4507757) B4507757
theorem B3005207 : Blo 1334986 3005207 := bstep (se 1 (by rfl) ⟨2253905, by rfl⟩ : syracuseStep 3005207 = 4507811) B4507811
theorem B123427637 : Blo 1334986 123427637 := bstep (se 5 (by rfl) ⟨5785670, by rfl⟩ : syracuseStep 123427637 = 11571341) B11571341
theorem B6765443 : Blo 1334986 6765443 := bstep (se 1 (by rfl) ⟨5074082, by rfl⟩ : syracuseStep 6765443 = 10148165) B10148165
theorem B3382195 : Blo 1334986 3382195 := bstep (se 1 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 3382195 = 5073293) B5073293
theorem B6421427 : Blo 1334986 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B3005387 : Blo 1334986 3005387 := bstep (se 1 (by rfl) ⟨2254040, by rfl⟩ : syracuseStep 3005387 = 4508081) B4508081
theorem B3005441 : Blo 1334986 3005441 := bstep (se 2 (by rfl) ⟨1127040, by rfl⟩ : syracuseStep 3005441 = 2254081) B2254081
theorem B3611699 : Blo 1334986 3611699 := bstep (se 1 (by rfl) ⟨2708774, by rfl⟩ : syracuseStep 3611699 = 5417549) B5417549
theorem B3382337 : Blo 1334986 3382337 := bstep (se 2 (by rfl) ⟨1268376, by rfl⟩ : syracuseStep 3382337 = 2536753) B2536753
theorem B3210329 : Blo 1334986 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B3005657 : Blo 1334986 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B10149137 : Blo 1334986 10149137 := bstep (se 2 (by rfl) ⟨3805926, by rfl⟩ : syracuseStep 10149137 = 7611853) B7611853
theorem B3005747 : Blo 1334986 3005747 := bstep (se 1 (by rfl) ⟨2254310, by rfl⟩ : syracuseStep 3005747 = 4508621) B4508621
theorem B3005783 : Blo 1334986 3005783 := bstep (se 1 (by rfl) ⟨2254337, by rfl⟩ : syracuseStep 3005783 = 4508675) B4508675
theorem B5709149 : Blo 1334986 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B4570519 : Blo 1334986 4570519 := bstep (se 1 (by rfl) ⟨3427889, by rfl⟩ : syracuseStep 4570519 = 6855779) B6855779
theorem B3005963 : Blo 1334986 3005963 := bstep (se 1 (by rfl) ⟨2254472, by rfl⟩ : syracuseStep 3005963 = 4508945) B4508945
theorem B2743831 : Blo 1334986 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B3006017 : Blo 1334986 3006017 := bstep (se 2 (by rfl) ⟨1127256, by rfl⟩ : syracuseStep 3006017 = 2254513) B2254513
theorem B1523287 : Blo 1334986 1523287 := bstep (se 1 (by rfl) ⟨1142465, by rfl⟩ : syracuseStep 1523287 = 2284931) B2284931
theorem B2743961 : Blo 1334986 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B10141361 : Blo 1334986 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B3047105 : Blo 1334986 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B1334987 : Blo 1334986 1334987 := bstep (se 1 (by rfl) ⟨1001240, by rfl⟩ : syracuseStep 1334987 = 2002481) B2002481
theorem B1334999 : Blo 1334986 1334999 := bstep (se 1 (by rfl) ⟨1001249, by rfl⟩ : syracuseStep 1334999 = 2002499) B2002499
theorem B1335019 : Blo 1334986 1335019 := bstep (se 1 (by rfl) ⟨1001264, by rfl⟩ : syracuseStep 1335019 = 2002529) B2002529
theorem B1335031 : Blo 1334986 1335031 := bstep (se 1 (by rfl) ⟨1001273, by rfl⟩ : syracuseStep 1335031 = 2002547) B2002547
theorem B1335051 : Blo 1334986 1335051 := bstep (se 1 (by rfl) ⟨1001288, by rfl⟩ : syracuseStep 1335051 = 2002577) B2002577
theorem B1335063 : Blo 1334986 1335063 := bstep (se 1 (by rfl) ⟨1001297, by rfl⟩ : syracuseStep 1335063 = 2002595) B2002595
theorem B3006233 : Blo 1334986 3006233 := bstep (se 2 (by rfl) ⟨1127337, by rfl⟩ : syracuseStep 3006233 = 2254675) B2254675
theorem B1335083 : Blo 1334986 1335083 := bstep (se 1 (by rfl) ⟨1001312, by rfl⟩ : syracuseStep 1335083 = 2002625) B2002625
theorem B1335095 : Blo 1334986 1335095 := bstep (se 1 (by rfl) ⟨1001321, by rfl⟩ : syracuseStep 1335095 = 2002643) B2002643
theorem B19259201 : Blo 1334986 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B1335115 : Blo 1334986 1335115 := bstep (se 1 (by rfl) ⟨1001336, by rfl⟩ : syracuseStep 1335115 = 2002673) B2002673
theorem B1335127 : Blo 1334986 1335127 := bstep (se 1 (by rfl) ⟨1001345, by rfl⟩ : syracuseStep 1335127 = 2002691) B2002691
theorem B3211097 : Blo 1334986 3211097 := bstep (se 2 (by rfl) ⟨1204161, by rfl⟩ : syracuseStep 3211097 = 2408323) B2408323
theorem B7610213 : Blo 1334986 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B1335147 : Blo 1334986 1335147 := bstep (se 1 (by rfl) ⟨1001360, by rfl⟩ : syracuseStep 1335147 = 2002721) B2002721
theorem B3006323 : Blo 1334986 3006323 := bstep (se 1 (by rfl) ⟨2254742, by rfl⟩ : syracuseStep 3006323 = 4509485) B4509485
theorem B1335159 : Blo 1334986 1335159 := bstep (se 1 (by rfl) ⟨1001369, by rfl⟩ : syracuseStep 1335159 = 2002739) B2002739
theorem B1335179 : Blo 1334986 1335179 := bstep (se 1 (by rfl) ⟨1001384, by rfl⟩ : syracuseStep 1335179 = 2002769) B2002769
theorem B1335191 : Blo 1334986 1335191 := bstep (se 1 (by rfl) ⟨1001393, by rfl⟩ : syracuseStep 1335191 = 2002787) B2002787
theorem B6504343 : Blo 1334986 6504343 := bstep (se 1 (by rfl) ⟨4878257, by rfl⟩ : syracuseStep 6504343 = 9756515) B9756515
theorem B3006359 : Blo 1334986 3006359 := bstep (se 1 (by rfl) ⟨2254769, by rfl⟩ : syracuseStep 3006359 = 4509539) B4509539
theorem B1335211 : Blo 1334986 1335211 := bstep (se 1 (by rfl) ⟨1001408, by rfl⟩ : syracuseStep 1335211 = 2002817) B2002817
theorem B1335223 : Blo 1334986 1335223 := bstep (se 1 (by rfl) ⟨1001417, by rfl⟩ : syracuseStep 1335223 = 2002835) B2002835
theorem B1335243 : Blo 1334986 1335243 := bstep (se 1 (by rfl) ⟨1001432, by rfl⟩ : syracuseStep 1335243 = 2002865) B2002865
theorem B1335255 : Blo 1334986 1335255 := bstep (se 1 (by rfl) ⟨1001441, by rfl⟩ : syracuseStep 1335255 = 2002883) B2002883
theorem B1335275 : Blo 1334986 1335275 := bstep (se 1 (by rfl) ⟨1001456, by rfl⟩ : syracuseStep 1335275 = 2002913) B2002913
theorem B1335287 : Blo 1334986 1335287 := bstep (se 1 (by rfl) ⟨1001465, by rfl⟩ : syracuseStep 1335287 = 2002931) B2002931
theorem B1335303 : Blo 1334986 1335303 := bstep (se 1 (by rfl) ⟨1001477, by rfl⟩ : syracuseStep 1335303 = 2002955) B2002955
theorem B1335311 : Blo 1334986 1335311 := bstep (se 1 (by rfl) ⟨1001483, by rfl⟩ : syracuseStep 1335311 = 2002967) B2002967
theorem B3383329 : Blo 1334986 3383329 := bstep (se 2 (by rfl) ⟨1268748, by rfl⟩ : syracuseStep 3383329 = 2537497) B2537497
theorem B1335355 : Blo 1334986 1335355 := bstep (se 1 (by rfl) ⟨1001516, by rfl⟩ : syracuseStep 1335355 = 2003033) B2003033
theorem B1335431 : Blo 1334986 1335431 := bstep (se 1 (by rfl) ⟨1001573, by rfl⟩ : syracuseStep 1335431 = 2003147) B2003147
theorem B1335439 : Blo 1334986 1335439 := bstep (se 1 (by rfl) ⟨1001579, by rfl⟩ : syracuseStep 1335439 = 2003159) B2003159
theorem B3006611 : Blo 1334986 3006611 := bstep (se 1 (by rfl) ⟨2254958, by rfl⟩ : syracuseStep 3006611 = 4509917) B4509917
theorem B1335483 : Blo 1334986 1335483 := bstep (se 1 (by rfl) ⟨1001612, by rfl⟩ : syracuseStep 1335483 = 2003225) B2003225
theorem B2253001 : Blo 1334986 2253001 := bstep (se 2 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 2253001 = 1689751) B1689751
theorem B3006665 : Blo 1334986 3006665 := bstep (se 2 (by rfl) ⟨1127499, by rfl⟩ : syracuseStep 3006665 = 2254999) B2254999
theorem B2572489 : Blo 1334986 2572489 := bstep (se 2 (by rfl) ⟨964683, by rfl⟩ : syracuseStep 2572489 = 1929367) B1929367
theorem B1335559 : Blo 1334986 1335559 := bstep (se 1 (by rfl) ⟨1001669, by rfl⟩ : syracuseStep 1335559 = 2003339) B2003339
theorem B1335567 : Blo 1334986 1335567 := bstep (se 1 (by rfl) ⟨1001675, by rfl⟩ : syracuseStep 1335567 = 2003351) B2003351
theorem B1335611 : Blo 1334986 1335611 := bstep (se 1 (by rfl) ⟨1001708, by rfl⟩ : syracuseStep 1335611 = 2003417) B2003417
theorem B3211579 : Blo 1334986 3211579 := bstep (se 1 (by rfl) ⟨2408684, by rfl⟩ : syracuseStep 3211579 = 4817369) B4817369
theorem B1335687 : Blo 1334986 1335687 := bstep (se 1 (by rfl) ⟨1001765, by rfl⟩ : syracuseStep 1335687 = 2003531) B2003531
theorem B3211655 : Blo 1334986 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B1335695 : Blo 1334986 1335695 := bstep (se 1 (by rfl) ⟨1001771, by rfl⟩ : syracuseStep 1335695 = 2003543) B2003543
theorem B6758801 : Blo 1334986 6758801 := bstep (se 2 (by rfl) ⟨2534550, by rfl⟩ : syracuseStep 6758801 = 5069101) B5069101
theorem B1335739 : Blo 1334986 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B14451149 : Blo 1334986 14451149 := bstep (se 3 (by rfl) ⟨2709590, by rfl⟩ : syracuseStep 14451149 = 5419181) B5419181
theorem B73073137 : Blo 1334986 73073137 := bstep (se 2 (by rfl) ⟨27402426, by rfl⟩ : syracuseStep 73073137 = 54804853) B54804853
theorem B1335815 : Blo 1334986 1335815 := bstep (se 1 (by rfl) ⟨1001861, by rfl⟩ : syracuseStep 1335815 = 2003723) B2003723
theorem B1335823 : Blo 1334986 1335823 := bstep (se 1 (by rfl) ⟨1001867, by rfl⟩ : syracuseStep 1335823 = 2003735) B2003735
theorem B9626141 : Blo 1334986 9626141 := bstep (se 3 (by rfl) ⟨1804901, by rfl⟩ : syracuseStep 9626141 = 3609803) B3609803
theorem B1335867 : Blo 1334986 1335867 := bstep (se 1 (by rfl) ⟨1001900, by rfl⟩ : syracuseStep 1335867 = 2003801) B2003801
theorem B3383927 : Blo 1334986 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B1335943 : Blo 1334986 1335943 := bstep (se 1 (by rfl) ⟨1001957, by rfl⟩ : syracuseStep 1335943 = 2003915) B2003915
theorem B1335951 : Blo 1334986 1335951 := bstep (se 1 (by rfl) ⟨1001963, by rfl⟩ : syracuseStep 1335951 = 2003927) B2003927
theorem B1901227 : Blo 1334986 1901227 := bstep (se 1 (by rfl) ⟨1425920, by rfl⟩ : syracuseStep 1901227 = 2851841) B2851841
theorem B1335995 : Blo 1334986 1335995 := bstep (se 1 (by rfl) ⟨1001996, by rfl⟩ : syracuseStep 1335995 = 2003993) B2003993
theorem B1336071 : Blo 1334986 1336071 := bstep (se 1 (by rfl) ⟨1002053, by rfl⟩ : syracuseStep 1336071 = 2004107) B2004107
theorem B1336079 : Blo 1334986 1336079 := bstep (se 1 (by rfl) ⟨1002059, by rfl⟩ : syracuseStep 1336079 = 2004119) B2004119
theorem B15221519 : Blo 1334986 15221519 := bstep (se 1 (by rfl) ⟨11416139, by rfl⟩ : syracuseStep 15221519 = 22832279) B22832279
theorem B2851643 : Blo 1334986 2851643 := bstep (se 1 (by rfl) ⟨2138732, by rfl⟩ : syracuseStep 2851643 = 4277465) B4277465
theorem B1336123 : Blo 1334986 1336123 := bstep (se 1 (by rfl) ⟨1002092, by rfl⟩ : syracuseStep 1336123 = 2004185) B2004185
theorem B3801917 : Blo 1334986 3801917 := bstep (se 3 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 3801917 = 1425719) B1425719
theorem B2253703 : Blo 1334986 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B1336199 : Blo 1334986 1336199 := bstep (se 1 (by rfl) ⟨1002149, by rfl⟩ : syracuseStep 1336199 = 2004299) B2004299
theorem B3007367 : Blo 1334986 3007367 := bstep (se 1 (by rfl) ⟨2255525, by rfl⟩ : syracuseStep 3007367 = 4511051) B4511051
theorem B1336207 : Blo 1334986 1336207 := bstep (se 1 (by rfl) ⟨1002155, by rfl⟩ : syracuseStep 1336207 = 2004311) B2004311
theorem B4506515 : Blo 1334986 4506515 := bstep (se 1 (by rfl) ⟨3379886, by rfl⟩ : syracuseStep 4506515 = 6759773) B6759773
theorem B1336251 : Blo 1334986 1336251 := bstep (se 1 (by rfl) ⟨1002188, by rfl⟩ : syracuseStep 1336251 = 2004377) B2004377
theorem B1336327 : Blo 1334986 1336327 := bstep (se 1 (by rfl) ⟨1002245, by rfl⟩ : syracuseStep 1336327 = 2004491) B2004491
theorem B1336335 : Blo 1334986 1336335 := bstep (se 1 (by rfl) ⟨1002251, by rfl⟩ : syracuseStep 1336335 = 2004503) B2004503
theorem B1336379 : Blo 1334986 1336379 := bstep (se 1 (by rfl) ⟨1002284, by rfl⟩ : syracuseStep 1336379 = 2004569) B2004569
theorem B3007547 : Blo 1334986 3007547 := bstep (se 1 (by rfl) ⟨2255660, by rfl⟩ : syracuseStep 3007547 = 4511321) B4511321
theorem B6505591 : Blo 1334986 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B13010053 : Blo 1334986 13010053 := bstep (se 4 (by rfl) ⟨1219692, by rfl⟩ : syracuseStep 13010053 = 2439385) B2439385
theorem B1336455 : Blo 1334986 1336455 := bstep (se 1 (by rfl) ⟨1002341, by rfl⟩ : syracuseStep 1336455 = 2004683) B2004683
theorem B1336463 : Blo 1334986 1336463 := bstep (se 1 (by rfl) ⟨1002347, by rfl⟩ : syracuseStep 1336463 = 2004695) B2004695
theorem B3007673 : Blo 1334986 3007673 := bstep (se 2 (by rfl) ⟨1127877, by rfl⟩ : syracuseStep 3007673 = 2255755) B2255755
theorem B1336507 : Blo 1334986 1336507 := bstep (se 1 (by rfl) ⟨1002380, by rfl⟩ : syracuseStep 1336507 = 2004761) B2004761
theorem B6767873 : Blo 1334986 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B1336583 : Blo 1334986 1336583 := bstep (se 1 (by rfl) ⟨1002437, by rfl⟩ : syracuseStep 1336583 = 2004875) B2004875
theorem B1336591 : Blo 1334986 1336591 := bstep (se 1 (by rfl) ⟨1002443, by rfl⟩ : syracuseStep 1336591 = 2004887) B2004887
theorem B1336635 : Blo 1334986 1336635 := bstep (se 1 (by rfl) ⟨1002476, by rfl⟩ : syracuseStep 1336635 = 2004953) B2004953
theorem B1336711 : Blo 1334986 1336711 := bstep (se 1 (by rfl) ⟨1002533, by rfl⟩ : syracuseStep 1336711 = 2005067) B2005067
theorem B1336719 : Blo 1334986 1336719 := bstep (se 1 (by rfl) ⟨1002539, by rfl⟩ : syracuseStep 1336719 = 2005079) B2005079
theorem B1336763 : Blo 1334986 1336763 := bstep (se 1 (by rfl) ⟨1002572, by rfl⟩ : syracuseStep 1336763 = 2005145) B2005145
theorem B1336839 : Blo 1334986 1336839 := bstep (se 1 (by rfl) ⟨1002629, by rfl⟩ : syracuseStep 1336839 = 2005259) B2005259
theorem B2254351 : Blo 1334986 2254351 := bstep (se 1 (by rfl) ⟨1690763, by rfl⟩ : syracuseStep 2254351 = 3381527) B3381527
theorem B1336847 : Blo 1334986 1336847 := bstep (se 1 (by rfl) ⟨1002635, by rfl⟩ : syracuseStep 1336847 = 2005271) B2005271
theorem B3008015 : Blo 1334986 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B3008033 : Blo 1334986 3008033 := bstep (se 2 (by rfl) ⟨1128012, by rfl⟩ : syracuseStep 3008033 = 2256025) B2256025
theorem B1336891 : Blo 1334986 1336891 := bstep (se 1 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 1336891 = 2005337) B2005337
theorem B5072503 : Blo 1334986 5072503 := bstep (se 1 (by rfl) ⟨3804377, by rfl⟩ : syracuseStep 5072503 = 7608755) B7608755
theorem B1336967 : Blo 1334986 1336967 := bstep (se 1 (by rfl) ⟨1002725, by rfl⟩ : syracuseStep 1336967 = 2005451) B2005451
theorem B1336975 : Blo 1334986 1336975 := bstep (se 1 (by rfl) ⟨1002731, by rfl⟩ : syracuseStep 1336975 = 2005463) B2005463
theorem B7317229 : Blo 1334986 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B5490413 : Blo 1334986 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B4572929 : Blo 1334986 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B3802909 : Blo 1334986 3802909 := bstep (se 3 (by rfl) ⟨713045, by rfl⟩ : syracuseStep 3802909 = 1426091) B1426091
theorem B7219003 : Blo 1334986 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B18778007 : Blo 1334986 18778007 := bstep (se 1 (by rfl) ⟨14083505, by rfl⟩ : syracuseStep 18778007 = 28167011) B28167011
theorem B6424541 : Blo 1334986 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B2254891 : Blo 1334986 2254891 := bstep (se 1 (by rfl) ⟨1691168, by rfl⟩ : syracuseStep 2254891 = 3382337) B3382337
theorem B2140219 : Blo 1334986 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B2255033 : Blo 1334986 2255033 := bstep (se 2 (by rfl) ⟨845637, by rfl⟩ : syracuseStep 2255033 = 1691275) B1691275
theorem B1902793 : Blo 1334986 1902793 := bstep (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) B1427095
theorem B8562925 : Blo 1334986 8562925 := bstep (se 3 (by rfl) ⟨1605548, by rfl⟩ : syracuseStep 8562925 = 3211097) B3211097
theorem B4507919 : Blo 1334986 4507919 := bstep (se 1 (by rfl) ⟨3380939, by rfl⟩ : syracuseStep 4507919 = 6761879) B6761879
theorem B9767303 : Blo 1334986 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B1804729 : Blo 1334986 1804729 := bstep (se 2 (by rfl) ⟨676773, by rfl⟩ : syracuseStep 1804729 = 1353547) B1353547
theorem B6760907 : Blo 1334986 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B4508189 : Blo 1334986 4508189 := bstep (se 3 (by rfl) ⟨845285, by rfl⟩ : syracuseStep 4508189 = 1690571) B1690571
theorem B12839467 : Blo 1334986 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B15419969 : Blo 1334986 15419969 := bstep (se 2 (by rfl) ⟨5782488, by rfl⟩ : syracuseStep 15419969 = 11564977) B11564977
theorem B5073475 : Blo 1334986 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B1690247 : Blo 1334986 1690247 := bstep (se 1 (by rfl) ⟨1267685, by rfl⟩ : syracuseStep 1690247 = 2535371) B2535371
theorem B7613129 : Blo 1334986 7613129 := bstep (se 2 (by rfl) ⟨2854923, by rfl⟩ : syracuseStep 7613129 = 5709847) B5709847
theorem B8129261 : Blo 1334986 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B1903351 : Blo 1334986 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B11406095 : Blo 1334986 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B6761231 : Blo 1334986 6761231 := bstep (se 1 (by rfl) ⟨5070923, by rfl⟩ : syracuseStep 6761231 = 10141847) B10141847
theorem B5073779 : Blo 1334986 5073779 := bstep (se 1 (by rfl) ⟨3805334, by rfl⟩ : syracuseStep 5073779 = 7610669) B7610669
theorem B2255735 : Blo 1334986 2255735 := bstep (se 1 (by rfl) ⟨1691801, by rfl⟩ : syracuseStep 2255735 = 3383603) B3383603
theorem B1502095 : Blo 1334986 1502095 := bstep (se 1 (by rfl) ⟨1126571, by rfl⟩ : syracuseStep 1502095 = 2253143) B2253143
theorem B1829803 : Blo 1334986 1829803 := bstep (se 1 (by rfl) ⟨1372352, by rfl⟩ : syracuseStep 1829803 = 2744705) B2744705
theorem B4279567 : Blo 1334986 4279567 := bstep (se 1 (by rfl) ⟨3209675, by rfl⟩ : syracuseStep 4279567 = 6419351) B6419351
theorem B1690895 : Blo 1334986 1690895 := bstep (se 1 (by rfl) ⟨1268171, by rfl⟩ : syracuseStep 1690895 = 2536343) B2536343
theorem B6860047 : Blo 1334986 6860047 := bstep (se 1 (by rfl) ⟨5145035, by rfl⟩ : syracuseStep 6860047 = 10290071) B10290071
theorem B3853597 : Blo 1334986 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B11414843 : Blo 1334986 11414843 := bstep (se 1 (by rfl) ⟨8561132, by rfl⟩ : syracuseStep 11414843 = 17122265) B17122265
theorem B5074235 : Blo 1334986 5074235 := bstep (se 1 (by rfl) ⟨3805676, by rfl⟩ : syracuseStep 5074235 = 7611353) B7611353
theorem B1502599 : Blo 1334986 1502599 := bstep (se 1 (by rfl) ⟨1126949, by rfl⟩ : syracuseStep 1502599 = 2253899) B2253899
theorem B17346001 : Blo 1334986 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B1502779 : Blo 1334986 1502779 := bstep (se 1 (by rfl) ⟨1127084, by rfl⟩ : syracuseStep 1502779 = 2254169) B2254169
theorem B2002505 : Blo 1334986 2002505 := bstep (se 2 (by rfl) ⟨750939, by rfl⟩ : syracuseStep 2002505 = 1501879) B1501879
theorem B19246693 : Blo 1334986 19246693 := bstep (se 4 (by rfl) ⟨1804377, by rfl⟩ : syracuseStep 19246693 = 3608755) B3608755
theorem B3804857 : Blo 1334986 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B2002619 : Blo 1334986 2002619 := bstep (se 1 (by rfl) ⟨1501964, by rfl⟩ : syracuseStep 2002619 = 3003929) B3003929
theorem B2535113 : Blo 1334986 2535113 := bstep (se 2 (by rfl) ⟨950667, by rfl⟩ : syracuseStep 2535113 = 1901335) B1901335
theorem B2002679 : Blo 1334986 2002679 := bstep (se 1 (by rfl) ⟨1502009, by rfl⟩ : syracuseStep 2002679 = 3004019) B3004019
theorem B5705473 : Blo 1334986 5705473 := bstep (se 2 (by rfl) ⟨2139552, by rfl⟩ : syracuseStep 5705473 = 4279105) B4279105
theorem B2002703 : Blo 1334986 2002703 := bstep (se 1 (by rfl) ⟨1502027, by rfl⟩ : syracuseStep 2002703 = 3004055) B3004055
theorem B5074721 : Blo 1334986 5074721 := bstep (se 2 (by rfl) ⟨1903020, by rfl⟩ : syracuseStep 5074721 = 3806041) B3806041
theorem B2002745 : Blo 1334986 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B32968565 : Blo 1334986 32968565 := bstep (se 5 (by rfl) ⟨1545401, by rfl⟩ : syracuseStep 32968565 = 3090803) B3090803
theorem B2002823 : Blo 1334986 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B4509593 : Blo 1334986 4509593 := bstep (se 2 (by rfl) ⟨1691097, by rfl⟩ : syracuseStep 4509593 = 3382195) B3382195
theorem B2002859 : Blo 1334986 2002859 := bstep (se 1 (by rfl) ⟨1502144, by rfl⟩ : syracuseStep 2002859 = 3004289) B3004289
theorem B2002889 : Blo 1334986 2002889 := bstep (se 2 (by rfl) ⟨751083, by rfl⟩ : syracuseStep 2002889 = 1502167) B1502167
theorem B1503247 : Blo 1334986 1503247 := bstep (se 1 (by rfl) ⟨1127435, by rfl⟩ : syracuseStep 1503247 = 2254871) B2254871
theorem B7606295 : Blo 1334986 7606295 := bstep (se 1 (by rfl) ⟨5704721, by rfl⟩ : syracuseStep 7606295 = 11409443) B11409443
theorem B3379259 : Blo 1334986 3379259 := bstep (se 1 (by rfl) ⟨2534444, by rfl⟩ : syracuseStep 3379259 = 5068889) B5068889
theorem B2003003 : Blo 1334986 2003003 := bstep (se 1 (by rfl) ⟨1502252, by rfl⟩ : syracuseStep 2003003 = 3004505) B3004505
theorem B4337725 : Blo 1334986 4337725 := bstep (se 3 (by rfl) ⟨813323, by rfl⟩ : syracuseStep 4337725 = 1626647) B1626647
theorem B5705815 : Blo 1334986 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B2003063 : Blo 1334986 2003063 := bstep (se 1 (by rfl) ⟨1502297, by rfl⟩ : syracuseStep 2003063 = 3004595) B3004595
theorem B2003087 : Blo 1334986 2003087 := bstep (se 1 (by rfl) ⟨1502315, by rfl⟩ : syracuseStep 2003087 = 3004631) B3004631
theorem B2003129 : Blo 1334986 2003129 := bstep (se 2 (by rfl) ⟨751173, by rfl⟩ : syracuseStep 2003129 = 1502347) B1502347
theorem B6762689 : Blo 1334986 6762689 := bstep (se 2 (by rfl) ⟨2536008, by rfl⟩ : syracuseStep 6762689 = 5072017) B5072017
theorem B2003207 : Blo 1334986 2003207 := bstep (se 1 (by rfl) ⟨1502405, by rfl⟩ : syracuseStep 2003207 = 3004811) B3004811
theorem B2003243 : Blo 1334986 2003243 := bstep (se 1 (by rfl) ⟨1502432, by rfl⟩ : syracuseStep 2003243 = 3004865) B3004865
theorem B2003273 : Blo 1334986 2003273 := bstep (se 2 (by rfl) ⟨751227, by rfl⟩ : syracuseStep 2003273 = 1502455) B1502455
theorem B3379603 : Blo 1334986 3379603 := bstep (se 1 (by rfl) ⟨2534702, by rfl⟩ : syracuseStep 3379603 = 5069405) B5069405
theorem B2003387 : Blo 1334986 2003387 := bstep (se 1 (by rfl) ⟨1502540, by rfl⟩ : syracuseStep 2003387 = 3005081) B3005081
theorem B2003447 : Blo 1334986 2003447 := bstep (se 1 (by rfl) ⟨1502585, by rfl⟩ : syracuseStep 2003447 = 3005171) B3005171
theorem B1503751 : Blo 1334986 1503751 := bstep (se 1 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 1503751 = 2255627) B2255627
theorem B2003471 : Blo 1334986 2003471 := bstep (se 1 (by rfl) ⟨1502603, by rfl⟩ : syracuseStep 2003471 = 3005207) B3005207
theorem B3379745 : Blo 1334986 3379745 := bstep (se 2 (by rfl) ⟨1267404, by rfl⟩ : syracuseStep 3379745 = 2534809) B2534809
theorem B82285091 : Blo 1334986 82285091 := bstep (se 1 (by rfl) ⟨61713818, by rfl⟩ : syracuseStep 82285091 = 123427637) B123427637
theorem B2003513 : Blo 1334986 2003513 := bstep (se 2 (by rfl) ⟨751317, by rfl⟩ : syracuseStep 2003513 = 1502635) B1502635
theorem B4510295 : Blo 1334986 4510295 := bstep (se 1 (by rfl) ⟨3382721, by rfl⟩ : syracuseStep 4510295 = 6765443) B6765443
theorem B4059763 : Blo 1334986 4059763 := bstep (se 1 (by rfl) ⟨3044822, by rfl⟩ : syracuseStep 4059763 = 6089645) B6089645
theorem B4280951 : Blo 1334986 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B2003591 : Blo 1334986 2003591 := bstep (se 1 (by rfl) ⟨1502693, by rfl⟩ : syracuseStep 2003591 = 3005387) B3005387
theorem B2003627 : Blo 1334986 2003627 := bstep (se 1 (by rfl) ⟨1502720, by rfl⟩ : syracuseStep 2003627 = 3005441) B3005441
theorem B1503931 : Blo 1334986 1503931 := bstep (se 1 (by rfl) ⟨1127948, by rfl⟩ : syracuseStep 1503931 = 2255897) B2255897
theorem B3658441 : Blo 1334986 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B2003657 : Blo 1334986 2003657 := bstep (se 2 (by rfl) ⟨751371, by rfl⟩ : syracuseStep 2003657 = 1502743) B1502743
theorem B5075693 : Blo 1334986 5075693 := bstep (se 3 (by rfl) ⟨951692, by rfl⟩ : syracuseStep 5075693 = 1903385) B1903385
theorem B3207937 : Blo 1334986 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B34689829 : Blo 1334986 34689829 := bstep (se 4 (by rfl) ⟨3252171, by rfl⟩ : syracuseStep 34689829 = 6504343) B6504343
theorem B2003771 : Blo 1334986 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B2003831 : Blo 1334986 2003831 := bstep (se 1 (by rfl) ⟨1502873, by rfl⟩ : syracuseStep 2003831 = 3005747) B3005747
theorem B2003855 : Blo 1334986 2003855 := bstep (se 1 (by rfl) ⟨1502891, by rfl⟩ : syracuseStep 2003855 = 3005783) B3005783
theorem B3806099 : Blo 1334986 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B2003897 : Blo 1334986 2003897 := bstep (se 2 (by rfl) ⟨751461, by rfl⟩ : syracuseStep 2003897 = 1502923) B1502923
theorem B2003975 : Blo 1334986 2003975 := bstep (se 1 (by rfl) ⟨1502981, by rfl⟩ : syracuseStep 2003975 = 3005963) B3005963
theorem B2004011 : Blo 1334986 2004011 := bstep (se 1 (by rfl) ⟨1503008, by rfl⟩ : syracuseStep 2004011 = 3006017) B3006017
theorem B4510781 : Blo 1334986 4510781 := bstep (se 3 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 4510781 = 1691543) B1691543
theorem B2004041 : Blo 1334986 2004041 := bstep (se 2 (by rfl) ⟨751515, by rfl⟩ : syracuseStep 2004041 = 1503031) B1503031
theorem B2004155 : Blo 1334986 2004155 := bstep (se 1 (by rfl) ⟨1503116, by rfl⟩ : syracuseStep 2004155 = 3006233) B3006233
theorem B2004215 : Blo 1334986 2004215 := bstep (se 1 (by rfl) ⟨1503161, by rfl⟩ : syracuseStep 2004215 = 3006323) B3006323
theorem B2004239 : Blo 1334986 2004239 := bstep (se 1 (by rfl) ⟨1503179, by rfl⟩ : syracuseStep 2004239 = 3006359) B3006359
theorem B2004281 : Blo 1334986 2004281 := bstep (se 2 (by rfl) ⟨751605, by rfl⟩ : syracuseStep 2004281 = 1503211) B1503211
theorem B3003767 : Blo 1334986 3003767 := bstep (se 1 (by rfl) ⟨2252825, by rfl⟩ : syracuseStep 3003767 = 4505651) B4505651
theorem B2004359 : Blo 1334986 2004359 := bstep (se 1 (by rfl) ⟨1503269, by rfl⟩ : syracuseStep 2004359 = 3006539) B3006539
theorem B2004395 : Blo 1334986 2004395 := bstep (se 1 (by rfl) ⟨1503296, by rfl⟩ : syracuseStep 2004395 = 3006593) B3006593
theorem B2004425 : Blo 1334986 2004425 := bstep (se 2 (by rfl) ⟨751659, by rfl⟩ : syracuseStep 2004425 = 1503319) B1503319
theorem B6763985 : Blo 1334986 6763985 := bstep (se 2 (by rfl) ⟨2536494, by rfl⟩ : syracuseStep 6763985 = 5072989) B5072989
theorem B3380737 : Blo 1334986 3380737 := bstep (se 2 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 3380737 = 2535553) B2535553
theorem B7222807 : Blo 1334986 7222807 := bstep (se 1 (by rfl) ⟨5417105, by rfl⟩ : syracuseStep 7222807 = 10834211) B10834211
theorem B3003947 : Blo 1334986 3003947 := bstep (se 1 (by rfl) ⟨2252960, by rfl⟩ : syracuseStep 3003947 = 4505921) B4505921
theorem B2004539 : Blo 1334986 2004539 := bstep (se 1 (by rfl) ⟨1503404, by rfl⟩ : syracuseStep 2004539 = 3006809) B3006809
theorem B2004599 : Blo 1334986 2004599 := bstep (se 1 (by rfl) ⟨1503449, by rfl⟩ : syracuseStep 2004599 = 3006899) B3006899
theorem B2537095 : Blo 1334986 2537095 := bstep (se 1 (by rfl) ⟨1902821, by rfl⟩ : syracuseStep 2537095 = 3805643) B3805643
theorem B2004623 : Blo 1334986 2004623 := bstep (se 1 (by rfl) ⟨1503467, by rfl⟩ : syracuseStep 2004623 = 3006935) B3006935
theorem B3610259 : Blo 1334986 3610259 := bstep (se 1 (by rfl) ⟨2707694, by rfl⟩ : syracuseStep 3610259 = 5415389) B5415389
theorem B19265201 : Blo 1334986 19265201 := bstep (se 2 (by rfl) ⟨7224450, by rfl⟩ : syracuseStep 19265201 = 14448901) B14448901
theorem B2004665 : Blo 1334986 2004665 := bstep (se 2 (by rfl) ⟨751749, by rfl⟩ : syracuseStep 2004665 = 1503499) B1503499
theorem B2004743 : Blo 1334986 2004743 := bstep (se 1 (by rfl) ⟨1503557, by rfl⟩ : syracuseStep 2004743 = 3007115) B3007115
theorem B8124197 : Blo 1334986 8124197 := bstep (se 4 (by rfl) ⟨761643, by rfl⟩ : syracuseStep 8124197 = 1523287) B1523287
theorem B2004779 : Blo 1334986 2004779 := bstep (se 1 (by rfl) ⟨1503584, by rfl⟩ : syracuseStep 2004779 = 3007169) B3007169
theorem B92526401 : Blo 1334986 92526401 := bstep (se 2 (by rfl) ⟨34697400, by rfl⟩ : syracuseStep 92526401 = 69394801) B69394801
theorem B2004809 : Blo 1334986 2004809 := bstep (se 2 (by rfl) ⟨751803, by rfl⟩ : syracuseStep 2004809 = 1503607) B1503607
theorem B13711193 : Blo 1334986 13711193 := bstep (se 2 (by rfl) ⟨5141697, by rfl⟩ : syracuseStep 13711193 = 10283395) B10283395
theorem B3708791 : Blo 1334986 3708791 := bstep (se 1 (by rfl) ⟨2781593, by rfl⟩ : syracuseStep 3708791 = 5563187) B5563187
theorem B3610487 : Blo 1334986 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B3004307 : Blo 1334986 3004307 := bstep (se 1 (by rfl) ⟨2253230, by rfl⟩ : syracuseStep 3004307 = 4506461) B4506461
theorem B11417507 : Blo 1334986 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B2004923 : Blo 1334986 2004923 := bstep (se 1 (by rfl) ⟨1503692, by rfl⟩ : syracuseStep 2004923 = 3007385) B3007385
theorem B3004361 : Blo 1334986 3004361 := bstep (se 2 (by rfl) ⟨1126635, by rfl⟩ : syracuseStep 3004361 = 2253271) B2253271
theorem B7714763 : Blo 1334986 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B2004983 : Blo 1334986 2004983 := bstep (se 1 (by rfl) ⟨1503737, by rfl⟩ : syracuseStep 2004983 = 3007475) B3007475
theorem B2005007 : Blo 1334986 2005007 := bstep (se 1 (by rfl) ⟨1503755, by rfl⟩ : syracuseStep 2005007 = 3007511) B3007511
theorem B2005049 : Blo 1334986 2005049 := bstep (se 2 (by rfl) ⟨751893, by rfl⟩ : syracuseStep 2005049 = 1503787) B1503787
theorem B3381335 : Blo 1334986 3381335 := bstep (se 1 (by rfl) ⟨2536001, by rfl⟩ : syracuseStep 3381335 = 5072003) B5072003
theorem B5068919 : Blo 1334986 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B2709623 : Blo 1334986 2709623 := bstep (se 1 (by rfl) ⟨2032217, by rfl⟩ : syracuseStep 2709623 = 4064435) B4064435
theorem B2005127 : Blo 1334986 2005127 := bstep (se 1 (by rfl) ⟨1503845, by rfl⟩ : syracuseStep 2005127 = 3007691) B3007691
theorem B2005163 : Blo 1334986 2005163 := bstep (se 1 (by rfl) ⟨1503872, by rfl⟩ : syracuseStep 2005163 = 3007745) B3007745
theorem B2005193 : Blo 1334986 2005193 := bstep (se 2 (by rfl) ⟨751947, by rfl⟩ : syracuseStep 2005193 = 1503895) B1503895
theorem B3209483 : Blo 1334986 3209483 := bstep (se 1 (by rfl) ⟨2407112, by rfl⟩ : syracuseStep 3209483 = 4814225) B4814225
theorem B3381547 : Blo 1334986 3381547 := bstep (se 1 (by rfl) ⟨2536160, by rfl⟩ : syracuseStep 3381547 = 5072321) B5072321
theorem B2005307 : Blo 1334986 2005307 := bstep (se 1 (by rfl) ⟨1503980, by rfl⟩ : syracuseStep 2005307 = 3007961) B3007961
theorem B2005367 : Blo 1334986 2005367 := bstep (se 1 (by rfl) ⟨1504025, by rfl⟩ : syracuseStep 2005367 = 3008051) B3008051
theorem B2005391 : Blo 1334986 2005391 := bstep (se 1 (by rfl) ⟨1504043, by rfl⟩ : syracuseStep 2005391 = 3008087) B3008087
theorem B4815251 : Blo 1334986 4815251 := bstep (se 1 (by rfl) ⟨3611438, by rfl⟩ : syracuseStep 4815251 = 7222877) B7222877
theorem B1604011 : Blo 1334986 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B3381689 : Blo 1334986 3381689 := bstep (se 2 (by rfl) ⟨1268133, by rfl⟩ : syracuseStep 3381689 = 2536267) B2536267
theorem B4512185 : Blo 1334986 4512185 := bstep (se 2 (by rfl) ⟨1692069, by rfl⟩ : syracuseStep 4512185 = 3384139) B3384139
theorem B2005433 : Blo 1334986 2005433 := bstep (se 2 (by rfl) ⟨752037, by rfl⟩ : syracuseStep 2005433 = 1504075) B1504075
theorem B4569643 : Blo 1334986 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B3005063 : Blo 1334986 3005063 := bstep (se 1 (by rfl) ⟨2253797, by rfl⟩ : syracuseStep 3005063 = 4507595) B4507595
theorem B10140389 : Blo 1334986 10140389 := bstep (se 4 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 10140389 = 1901323) B1901323
theorem B2571041 : Blo 1334986 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B15211313 : Blo 1334986 15211313 := bstep (se 2 (by rfl) ⟨5704242, by rfl⟩ : syracuseStep 15211313 = 11408485) B11408485
theorem B3005243 : Blo 1334986 3005243 := bstep (se 1 (by rfl) ⟨2253932, by rfl⟩ : syracuseStep 3005243 = 4507865) B4507865
theorem B2710331 : Blo 1334986 2710331 := bstep (se 1 (by rfl) ⟨2032748, by rfl⟩ : syracuseStep 2710331 = 4065497) B4065497
theorem B49445747 : Blo 1334986 49445747 := bstep (se 1 (by rfl) ⟨37084310, by rfl⟩ : syracuseStep 49445747 = 74168621) B74168621
theorem B3005369 : Blo 1334986 3005369 := bstep (se 2 (by rfl) ⟨1127013, by rfl⟩ : syracuseStep 3005369 = 2254027) B2254027
theorem B3300385 : Blo 1334986 3300385 := bstep (se 2 (by rfl) ⟨1237644, by rfl⟩ : syracuseStep 3300385 = 2475289) B2475289
theorem B5069891 : Blo 1334986 5069891 := bstep (se 1 (by rfl) ⟨3802418, by rfl⟩ : syracuseStep 5069891 = 7604837) B7604837
theorem B7609463 : Blo 1334986 7609463 := bstep (se 1 (by rfl) ⟨5707097, by rfl⟩ : syracuseStep 7609463 = 11414195) B11414195
theorem B6094025 : Blo 1334986 6094025 := bstep (se 2 (by rfl) ⟨2285259, by rfl⟩ : syracuseStep 6094025 = 4570519) B4570519
theorem B3005711 : Blo 1334986 3005711 := bstep (se 1 (by rfl) ⟨2254283, by rfl⟩ : syracuseStep 3005711 = 4508567) B4508567
theorem B3005729 : Blo 1334986 3005729 := bstep (se 2 (by rfl) ⟨1127148, by rfl⟩ : syracuseStep 3005729 = 2254297) B2254297
theorem B15220061 : Blo 1334986 15220061 := bstep (se 3 (by rfl) ⟨2853761, by rfl⟩ : syracuseStep 15220061 = 5707523) B5707523
theorem B2407799 : Blo 1334986 2407799 := bstep (se 1 (by rfl) ⟨1805849, by rfl⟩ : syracuseStep 2407799 = 3611699) B3611699
theorem B3382681 : Blo 1334986 3382681 := bstep (se 2 (by rfl) ⟨1268505, by rfl⟩ : syracuseStep 3382681 = 2537011) B2537011
theorem B5070347 : Blo 1334986 5070347 := bstep (se 1 (by rfl) ⟨3802760, by rfl⟩ : syracuseStep 5070347 = 7605521) B7605521
theorem B6766091 : Blo 1334986 6766091 := bstep (se 1 (by rfl) ⟨5074568, by rfl⟩ : syracuseStep 6766091 = 10149137) B10149137
theorem B3382843 : Blo 1334986 3382843 := bstep (se 1 (by rfl) ⟨2537132, by rfl⟩ : syracuseStep 3382843 = 5074265) B5074265
theorem B3006071 : Blo 1334986 3006071 := bstep (se 1 (by rfl) ⟨2254553, by rfl⟩ : syracuseStep 3006071 = 4509107) B4509107
theorem B6766253 : Blo 1334986 6766253 := bstep (se 3 (by rfl) ⟨1268672, by rfl⟩ : syracuseStep 6766253 = 2537345) B2537345
theorem B3382985 : Blo 1334986 3382985 := bstep (se 2 (by rfl) ⟨1268619, by rfl⟩ : syracuseStep 3382985 = 2537239) B2537239
theorem B3858121 : Blo 1334986 3858121 := bstep (se 2 (by rfl) ⟨1446795, by rfl⟩ : syracuseStep 3858121 = 2893591) B2893591
theorem B1335047 : Blo 1334986 1335047 := bstep (se 1 (by rfl) ⟨1001285, by rfl⟩ : syracuseStep 1335047 = 2002571) B2002571
theorem B1335055 : Blo 1334986 1335055 := bstep (se 1 (by rfl) ⟨1001291, by rfl⟩ : syracuseStep 1335055 = 2002583) B2002583
theorem B2031403 : Blo 1334986 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B3006251 : Blo 1334986 3006251 := bstep (se 1 (by rfl) ⟨2254688, by rfl⟩ : syracuseStep 3006251 = 4509377) B4509377
theorem B1335099 : Blo 1334986 1335099 := bstep (se 1 (by rfl) ⟨1001324, by rfl⟩ : syracuseStep 1335099 = 2002649) B2002649
theorem B1335175 : Blo 1334986 1335175 := bstep (se 1 (by rfl) ⟨1001381, by rfl⟩ : syracuseStep 1335175 = 2002763) B2002763
theorem B1335183 : Blo 1334986 1335183 := bstep (se 1 (by rfl) ⟨1001387, by rfl⟩ : syracuseStep 1335183 = 2002775) B2002775
theorem B3612563 : Blo 1334986 3612563 := bstep (se 1 (by rfl) ⟨2709422, by rfl⟩ : syracuseStep 3612563 = 5418845) B5418845
theorem B1335227 : Blo 1334986 1335227 := bstep (se 1 (by rfl) ⟨1001420, by rfl⟩ : syracuseStep 1335227 = 2002841) B2002841
theorem B5070863 : Blo 1334986 5070863 := bstep (se 1 (by rfl) ⟨3803147, by rfl⟩ : syracuseStep 5070863 = 7606295) B7606295
theorem B2252839 : Blo 1334986 2252839 := bstep (se 1 (by rfl) ⟨1689629, by rfl⟩ : syracuseStep 2252839 = 3379259) B3379259
theorem B1335335 : Blo 1334986 1335335 := bstep (se 1 (by rfl) ⟨1001501, by rfl⟩ : syracuseStep 1335335 = 2003003) B2003003
theorem B3006521 : Blo 1334986 3006521 := bstep (se 2 (by rfl) ⟨1127445, by rfl⟩ : syracuseStep 3006521 = 2254891) B2254891
theorem B1335375 : Blo 1334986 1335375 := bstep (se 1 (by rfl) ⟨1001531, by rfl⟩ : syracuseStep 1335375 = 2003063) B2003063
theorem B5783633 : Blo 1334986 5783633 := bstep (se 2 (by rfl) ⟨2168862, by rfl⟩ : syracuseStep 5783633 = 4337725) B4337725
theorem B1335391 : Blo 1334986 1335391 := bstep (se 1 (by rfl) ⟨1001543, by rfl⟩ : syracuseStep 1335391 = 2003087) B2003087
theorem B1335419 : Blo 1334986 1335419 := bstep (se 1 (by rfl) ⟨1001564, by rfl⟩ : syracuseStep 1335419 = 2003129) B2003129
theorem B1335471 : Blo 1334986 1335471 := bstep (se 1 (by rfl) ⟨1001603, by rfl⟩ : syracuseStep 1335471 = 2003207) B2003207
theorem B1335495 : Blo 1334986 1335495 := bstep (se 1 (by rfl) ⟨1001621, by rfl⟩ : syracuseStep 1335495 = 2003243) B2003243
theorem B1335515 : Blo 1334986 1335515 := bstep (se 1 (by rfl) ⟨1001636, by rfl⟩ : syracuseStep 1335515 = 2003273) B2003273
theorem B4505867 : Blo 1334986 4505867 := bstep (se 1 (by rfl) ⟨3379400, by rfl⟩ : syracuseStep 4505867 = 6758801) B6758801
theorem B1335591 : Blo 1334986 1335591 := bstep (se 1 (by rfl) ⟨1001693, by rfl⟩ : syracuseStep 1335591 = 2003387) B2003387
theorem B7225661 : Blo 1334986 7225661 := bstep (se 3 (by rfl) ⟨1354811, by rfl⟩ : syracuseStep 7225661 = 2709623) B2709623
theorem B1335631 : Blo 1334986 1335631 := bstep (se 1 (by rfl) ⟨1001723, by rfl⟩ : syracuseStep 1335631 = 2003447) B2003447
theorem B1335647 : Blo 1334986 1335647 := bstep (se 1 (by rfl) ⟨1001735, by rfl⟩ : syracuseStep 1335647 = 2003471) B2003471
theorem B2253163 : Blo 1334986 2253163 := bstep (se 1 (by rfl) ⟨1689872, by rfl⟩ : syracuseStep 2253163 = 3379745) B3379745
theorem B1335675 : Blo 1334986 1335675 := bstep (se 1 (by rfl) ⟨1001756, by rfl⟩ : syracuseStep 1335675 = 2003513) B2003513
theorem B3006863 : Blo 1334986 3006863 := bstep (se 1 (by rfl) ⟨2255147, by rfl⟩ : syracuseStep 3006863 = 4510295) B4510295
theorem B1335727 : Blo 1334986 1335727 := bstep (se 1 (by rfl) ⟨1001795, by rfl⟩ : syracuseStep 1335727 = 2003591) B2003591
theorem B1335751 : Blo 1334986 1335751 := bstep (se 1 (by rfl) ⟨1001813, by rfl⟩ : syracuseStep 1335751 = 2003627) B2003627
theorem B1335771 : Blo 1334986 1335771 := bstep (se 1 (by rfl) ⟨1001828, by rfl⟩ : syracuseStep 1335771 = 2003657) B2003657
theorem B3383795 : Blo 1334986 3383795 := bstep (se 1 (by rfl) ⟨2537846, by rfl⟩ : syracuseStep 3383795 = 5075693) B5075693
theorem B4506137 : Blo 1334986 4506137 := bstep (se 2 (by rfl) ⟨1689801, by rfl⟩ : syracuseStep 4506137 = 3379603) B3379603
theorem B1335847 : Blo 1334986 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B2138681 : Blo 1334986 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B1335887 : Blo 1334986 1335887 := bstep (se 1 (by rfl) ⟨1001915, by rfl⟩ : syracuseStep 1335887 = 2003831) B2003831
theorem B1335903 : Blo 1334986 1335903 := bstep (se 1 (by rfl) ⟨1001927, by rfl⟩ : syracuseStep 1335903 = 2003855) B2003855
theorem B1335931 : Blo 1334986 1335931 := bstep (se 1 (by rfl) ⟨1001948, by rfl⟩ : syracuseStep 1335931 = 2003897) B2003897
theorem B1335983 : Blo 1334986 1335983 := bstep (se 1 (by rfl) ⟨1001987, by rfl⟩ : syracuseStep 1335983 = 2003975) B2003975
theorem B1336007 : Blo 1334986 1336007 := bstep (se 1 (by rfl) ⟨1002005, by rfl⟩ : syracuseStep 1336007 = 2004011) B2004011
theorem B3007187 : Blo 1334986 3007187 := bstep (se 1 (by rfl) ⟨2255390, by rfl⟩ : syracuseStep 3007187 = 4510781) B4510781
theorem B1336027 : Blo 1334986 1336027 := bstep (se 1 (by rfl) ⟨1002020, by rfl⟩ : syracuseStep 1336027 = 2004041) B2004041
theorem B1336103 : Blo 1334986 1336103 := bstep (se 1 (by rfl) ⟨1002077, by rfl⟩ : syracuseStep 1336103 = 2004155) B2004155
theorem B1336143 : Blo 1334986 1336143 := bstep (se 1 (by rfl) ⟨1002107, by rfl⟩ : syracuseStep 1336143 = 2004215) B2004215
theorem B1336159 : Blo 1334986 1336159 := bstep (se 1 (by rfl) ⟨1002119, by rfl⟩ : syracuseStep 1336159 = 2004239) B2004239
theorem B1336187 : Blo 1334986 1336187 := bstep (se 1 (by rfl) ⟨1002140, by rfl⟩ : syracuseStep 1336187 = 2004281) B2004281
theorem B1336239 : Blo 1334986 1336239 := bstep (se 1 (by rfl) ⟨1002179, by rfl⟩ : syracuseStep 1336239 = 2004359) B2004359
theorem B1336263 : Blo 1334986 1336263 := bstep (se 1 (by rfl) ⟨1002197, by rfl⟩ : syracuseStep 1336263 = 2004395) B2004395
theorem B1336283 : Blo 1334986 1336283 := bstep (se 1 (by rfl) ⟨1002212, by rfl⟩ : syracuseStep 1336283 = 2004425) B2004425
theorem B4277249 : Blo 1334986 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B1336359 : Blo 1334986 1336359 := bstep (se 1 (by rfl) ⟨1002269, by rfl⟩ : syracuseStep 1336359 = 2004539) B2004539
theorem B46253105 : Blo 1334986 46253105 := bstep (se 2 (by rfl) ⟨17344914, by rfl⟩ : syracuseStep 46253105 = 34689829) B34689829
theorem B1336399 : Blo 1334986 1336399 := bstep (se 1 (by rfl) ⟨1002299, by rfl⟩ : syracuseStep 1336399 = 2004599) B2004599
theorem B1336415 : Blo 1334986 1336415 := bstep (se 1 (by rfl) ⟨1002311, by rfl⟩ : syracuseStep 1336415 = 2004623) B2004623
theorem B1336443 : Blo 1334986 1336443 := bstep (se 1 (by rfl) ⟨1002332, by rfl⟩ : syracuseStep 1336443 = 2004665) B2004665
theorem B3048619 : Blo 1334986 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B1336495 : Blo 1334986 1336495 := bstep (se 1 (by rfl) ⟨1002371, by rfl⟩ : syracuseStep 1336495 = 2004743) B2004743
theorem B1336519 : Blo 1334986 1336519 := bstep (se 1 (by rfl) ⟨1002389, by rfl⟩ : syracuseStep 1336519 = 2004779) B2004779
theorem B38536397 : Blo 1334986 38536397 := bstep (se 3 (by rfl) ⟨7225574, by rfl⟩ : syracuseStep 38536397 = 14451149) B14451149
theorem B1336539 : Blo 1334986 1336539 := bstep (se 1 (by rfl) ⟨1002404, by rfl⟩ : syracuseStep 1336539 = 2004809) B2004809
theorem B12518671 : Blo 1334986 12518671 := bstep (se 1 (by rfl) ⟨9389003, by rfl⟩ : syracuseStep 12518671 = 18778007) B18778007
theorem B7611671 : Blo 1334986 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B1336615 : Blo 1334986 1336615 := bstep (se 1 (by rfl) ⟨1002461, by rfl⟩ : syracuseStep 1336615 = 2004923) B2004923
theorem B1336655 : Blo 1334986 1336655 := bstep (se 1 (by rfl) ⟨1002491, by rfl⟩ : syracuseStep 1336655 = 2004983) B2004983
theorem B1336671 : Blo 1334986 1336671 := bstep (se 1 (by rfl) ⟨1002503, by rfl⟩ : syracuseStep 1336671 = 2005007) B2005007
theorem B1336699 : Blo 1334986 1336699 := bstep (se 1 (by rfl) ⟨1002524, by rfl⟩ : syracuseStep 1336699 = 2005049) B2005049
theorem B4400513 : Blo 1334986 4400513 := bstep (se 2 (by rfl) ⟨1650192, by rfl⟩ : syracuseStep 4400513 = 3300385) B3300385
theorem B2254223 : Blo 1334986 2254223 := bstep (se 1 (by rfl) ⟨1690667, by rfl⟩ : syracuseStep 2254223 = 3381335) B3381335
theorem B1336751 : Blo 1334986 1336751 := bstep (se 1 (by rfl) ⟨1002563, by rfl⟩ : syracuseStep 1336751 = 2005127) B2005127
theorem B1336775 : Blo 1334986 1336775 := bstep (se 1 (by rfl) ⟨1002581, by rfl⟩ : syracuseStep 1336775 = 2005163) B2005163
theorem B1336795 : Blo 1334986 1336795 := bstep (se 1 (by rfl) ⟨1002596, by rfl⟩ : syracuseStep 1336795 = 2005193) B2005193
theorem B1336871 : Blo 1334986 1336871 := bstep (se 1 (by rfl) ⟨1002653, by rfl⟩ : syracuseStep 1336871 = 2005307) B2005307
theorem B1336911 : Blo 1334986 1336911 := bstep (se 1 (by rfl) ⟨1002683, by rfl⟩ : syracuseStep 1336911 = 2005367) B2005367
theorem B1336927 : Blo 1334986 1336927 := bstep (se 1 (by rfl) ⟨1002695, by rfl⟩ : syracuseStep 1336927 = 2005391) B2005391
theorem B2254459 : Blo 1334986 2254459 := bstep (se 1 (by rfl) ⟨1690844, by rfl⟩ : syracuseStep 2254459 = 3381689) B3381689
theorem B3008123 : Blo 1334986 3008123 := bstep (se 1 (by rfl) ⟨2256092, by rfl⟩ : syracuseStep 3008123 = 4512185) B4512185
theorem B1336955 : Blo 1334986 1336955 := bstep (se 1 (by rfl) ⟨1002716, by rfl⟩ : syracuseStep 1336955 = 2005433) B2005433
theorem B4507271 : Blo 1334986 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B4507325 : Blo 1334986 4507325 := bstep (se 3 (by rfl) ⟨845123, by rfl⟩ : syracuseStep 4507325 = 1690247) B1690247
theorem B5138129 : Blo 1334986 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B6760259 : Blo 1334986 6760259 := bstep (se 1 (by rfl) ⟨5070194, by rfl⟩ : syracuseStep 6760259 = 10140389) B10140389
theorem B7604063 : Blo 1334986 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B4507487 : Blo 1334986 4507487 := bstep (se 1 (by rfl) ⟨3380615, by rfl⟩ : syracuseStep 4507487 = 6761231) B6761231
theorem B1714027 : Blo 1334986 1714027 := bstep (se 1 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 1714027 = 2571041) B2571041
theorem B23128001 : Blo 1334986 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B4507649 : Blo 1334986 4507649 := bstep (se 2 (by rfl) ⟨1690368, by rfl⟩ : syracuseStep 4507649 = 3380737) B3380737
theorem B5072975 : Blo 1334986 5072975 := bstep (se 1 (by rfl) ⟨3804731, by rfl⟩ : syracuseStep 5072975 = 7609463) B7609463
theorem B7604381 : Blo 1334986 7604381 := bstep (se 3 (by rfl) ⟨1425821, by rfl⟩ : syracuseStep 7604381 = 2851643) B2851643
theorem B86608277 : Blo 1334986 86608277 := bstep (se 6 (by rfl) ⟨2029881, by rfl⟩ : syracuseStep 86608277 = 4059763) B4059763
theorem B1690075 : Blo 1334986 1690075 := bstep (se 1 (by rfl) ⟨1267556, by rfl⟩ : syracuseStep 1690075 = 2535113) B2535113
theorem B2255323 : Blo 1334986 2255323 := bstep (se 1 (by rfl) ⟨1691492, by rfl⟩ : syracuseStep 2255323 = 3382985) B3382985
theorem B2853625 : Blo 1334986 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B4508459 : Blo 1334986 4508459 := bstep (se 1 (by rfl) ⟨3381344, by rfl⟩ : syracuseStep 4508459 = 6762689) B6762689
theorem B54856727 : Blo 1334986 54856727 := bstep (se 1 (by rfl) ⟨41142545, by rfl⟩ : syracuseStep 54856727 = 82285091) B82285091
theorem B4508729 : Blo 1334986 4508729 := bstep (se 2 (by rfl) ⟨1690773, by rfl⟩ : syracuseStep 4508729 = 3381547) B3381547
theorem B2853967 : Blo 1334986 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B2255951 : Blo 1334986 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B97430849 : Blo 1334986 97430849 := bstep (se 2 (by rfl) ⟨36536568, by rfl⟩ : syracuseStep 97430849 = 73073137) B73073137
theorem B4509053 : Blo 1334986 4509053 := bstep (se 3 (by rfl) ⟨845447, by rfl⟩ : syracuseStep 4509053 = 1690895) B1690895
theorem B2534969 : Blo 1334986 2534969 := bstep (se 2 (by rfl) ⟨950613, by rfl⟩ : syracuseStep 2534969 = 1901227) B1901227
theorem B2002511 : Blo 1334986 2002511 := bstep (se 1 (by rfl) ⟨1501883, by rfl⟩ : syracuseStep 2002511 = 3003767) B3003767
theorem B4877921 : Blo 1334986 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B4509323 : Blo 1334986 4509323 := bstep (se 1 (by rfl) ⟨3381992, by rfl⟩ : syracuseStep 4509323 = 6763985) B6763985
theorem B8564413 : Blo 1334986 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B2002631 : Blo 1334986 2002631 := bstep (se 1 (by rfl) ⟨1501973, by rfl⟩ : syracuseStep 2002631 = 3003947) B3003947
theorem B2002793 : Blo 1334986 2002793 := bstep (se 2 (by rfl) ⟨751047, by rfl⟩ : syracuseStep 2002793 = 1502095) B1502095
theorem B2002871 : Blo 1334986 2002871 := bstep (se 1 (by rfl) ⟨1502153, by rfl⟩ : syracuseStep 2002871 = 3004307) B3004307
theorem B2002907 : Blo 1334986 2002907 := bstep (se 1 (by rfl) ⟨1502180, by rfl⟩ : syracuseStep 2002907 = 3004361) B3004361
theorem B25669709 : Blo 1334986 25669709 := bstep (se 3 (by rfl) ⟨4813070, by rfl⟩ : syracuseStep 25669709 = 9626141) B9626141
theorem B3379279 : Blo 1334986 3379279 := bstep (se 1 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 3379279 = 5068919) B5068919
theorem B1503355 : Blo 1334986 1503355 := bstep (se 1 (by rfl) ⟨1127516, by rfl⟩ : syracuseStep 1503355 = 2255033) B2255033
theorem B17346737 : Blo 1334986 17346737 := bstep (se 2 (by rfl) ⟨6505026, by rfl⟩ : syracuseStep 17346737 = 13010053) B13010053
theorem B5706089 : Blo 1334986 5706089 := bstep (se 2 (by rfl) ⟨2139783, by rfl⟩ : syracuseStep 5706089 = 4279567) B4279567
theorem B9146729 : Blo 1334986 9146729 := bstep (se 2 (by rfl) ⟨3430023, by rfl⟩ : syracuseStep 9146729 = 6860047) B6860047
theorem B2003375 : Blo 1334986 2003375 := bstep (se 1 (by rfl) ⟨1502531, by rfl⟩ : syracuseStep 2003375 = 3005063) B3005063
theorem B5075419 : Blo 1334986 5075419 := bstep (se 1 (by rfl) ⟨3806564, by rfl⟩ : syracuseStep 5075419 = 7613129) B7613129
theorem B5419507 : Blo 1334986 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B2003465 : Blo 1334986 2003465 := bstep (se 2 (by rfl) ⟨751299, by rfl⟩ : syracuseStep 2003465 = 1502599) B1502599
theorem B4510241 : Blo 1334986 4510241 := bstep (se 2 (by rfl) ⟨1691340, by rfl⟩ : syracuseStep 4510241 = 3382681) B3382681
theorem B2003495 : Blo 1334986 2003495 := bstep (se 1 (by rfl) ⟨1502621, by rfl⟩ : syracuseStep 2003495 = 3005243) B3005243
theorem B1806887 : Blo 1334986 1806887 := bstep (se 1 (by rfl) ⟨1355165, by rfl⟩ : syracuseStep 1806887 = 2710331) B2710331
theorem B1503823 : Blo 1334986 1503823 := bstep (se 1 (by rfl) ⟨1127867, by rfl⟩ : syracuseStep 1503823 = 2255735) B2255735
theorem B2003579 : Blo 1334986 2003579 := bstep (se 1 (by rfl) ⟨1502684, by rfl⟩ : syracuseStep 2003579 = 3005369) B3005369
theorem B9630409 : Blo 1334986 9630409 := bstep (se 2 (by rfl) ⟨3611403, by rfl⟩ : syracuseStep 9630409 = 7222807) B7222807
theorem B3379927 : Blo 1334986 3379927 := bstep (se 1 (by rfl) ⟨2534945, by rfl⟩ : syracuseStep 3379927 = 5069891) B5069891
theorem B2003705 : Blo 1334986 2003705 := bstep (se 2 (by rfl) ⟨751389, by rfl⟩ : syracuseStep 2003705 = 1502779) B1502779
theorem B4510457 : Blo 1334986 4510457 := bstep (se 2 (by rfl) ⟨1691421, by rfl⟩ : syracuseStep 4510457 = 3382843) B3382843
theorem B21664525 : Blo 1334986 21664525 := bstep (se 3 (by rfl) ⟨4062098, by rfl⟩ : syracuseStep 21664525 = 8124197) B8124197
theorem B25662257 : Blo 1334986 25662257 := bstep (se 2 (by rfl) ⟨9623346, by rfl⟩ : syracuseStep 25662257 = 19246693) B19246693
theorem B6763337 : Blo 1334986 6763337 := bstep (se 2 (by rfl) ⟨2536251, by rfl⟩ : syracuseStep 6763337 = 5072503) B5072503
theorem B10138445 : Blo 1334986 10138445 := bstep (se 3 (by rfl) ⟨1900958, by rfl⟩ : syracuseStep 10138445 = 3801917) B3801917
theorem B2003807 : Blo 1334986 2003807 := bstep (se 1 (by rfl) ⟨1502855, by rfl⟩ : syracuseStep 2003807 = 3005711) B3005711
theorem B2003819 : Blo 1334986 2003819 := bstep (se 1 (by rfl) ⟨1502864, by rfl⟩ : syracuseStep 2003819 = 3005729) B3005729
theorem B10146707 : Blo 1334986 10146707 := bstep (se 1 (by rfl) ⟨7610030, by rfl⟩ : syracuseStep 10146707 = 15220061) B15220061
theorem B7607297 : Blo 1334986 7607297 := bstep (se 2 (by rfl) ⟨2852736, by rfl⟩ : syracuseStep 7607297 = 5705473) B5705473
theorem B3380231 : Blo 1334986 3380231 := bstep (se 1 (by rfl) ⟨2535173, by rfl⟩ : syracuseStep 3380231 = 5070347) B5070347
theorem B4510727 : Blo 1334986 4510727 := bstep (se 1 (by rfl) ⟨3383045, by rfl⟩ : syracuseStep 4510727 = 6766091) B6766091
theorem B2708537 : Blo 1334986 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B2004047 : Blo 1334986 2004047 := bstep (se 1 (by rfl) ⟨1503035, by rfl⟩ : syracuseStep 2004047 = 3006071) B3006071
theorem B4510835 : Blo 1334986 4510835 := bstep (se 1 (by rfl) ⟨3383126, by rfl⟩ : syracuseStep 4510835 = 6766253) B6766253
theorem B2536571 : Blo 1334986 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B2004167 : Blo 1334986 2004167 := bstep (se 1 (by rfl) ⟨1503125, by rfl⟩ : syracuseStep 2004167 = 3006251) B3006251
theorem B2004329 : Blo 1334986 2004329 := bstep (se 2 (by rfl) ⟨751623, by rfl⟩ : syracuseStep 2004329 = 1503247) B1503247
theorem B4511105 : Blo 1334986 4511105 := bstep (se 2 (by rfl) ⟨1691664, by rfl⟩ : syracuseStep 4511105 = 3383329) B3383329
theorem B2004407 : Blo 1334986 2004407 := bstep (se 1 (by rfl) ⟨1503305, by rfl⟩ : syracuseStep 2004407 = 3006611) B3006611
theorem B7607753 : Blo 1334986 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B2004443 : Blo 1334986 2004443 := bstep (se 1 (by rfl) ⟨1503332, by rfl⟩ : syracuseStep 2004443 = 3006665) B3006665
theorem B3004001 : Blo 1334986 3004001 := bstep (se 2 (by rfl) ⟨1126500, by rfl⟩ : syracuseStep 3004001 = 2253001) B2253001
theorem B2537057 : Blo 1334986 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B11417233 : Blo 1334986 11417233 := bstep (se 2 (by rfl) ⟨4281462, by rfl⟩ : syracuseStep 11417233 = 8562925) B8562925
theorem B4282105 : Blo 1334986 4282105 := bstep (se 2 (by rfl) ⟨1605789, by rfl⟩ : syracuseStep 4282105 = 3211579) B3211579
theorem B10147679 : Blo 1334986 10147679 := bstep (se 1 (by rfl) ⟨7610759, by rfl⟩ : syracuseStep 10147679 = 15221519) B15221519
theorem B2406305 : Blo 1334986 2406305 := bstep (se 2 (by rfl) ⟨902364, by rfl⟩ : syracuseStep 2406305 = 1804729) B1804729
theorem B2004911 : Blo 1334986 2004911 := bstep (se 1 (by rfl) ⟨1503683, by rfl⟩ : syracuseStep 2004911 = 3007367) B3007367
theorem B3004343 : Blo 1334986 3004343 := bstep (se 1 (by rfl) ⟨2253257, by rfl⟩ : syracuseStep 3004343 = 4506515) B4506515
theorem B2537399 : Blo 1334986 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B2005001 : Blo 1334986 2005001 := bstep (se 2 (by rfl) ⟨751875, by rfl⟩ : syracuseStep 2005001 = 1503751) B1503751
theorem B8558621 : Blo 1334986 8558621 := bstep (se 3 (by rfl) ⟨1604741, by rfl⟩ : syracuseStep 8558621 = 3209483) B3209483
theorem B2005031 : Blo 1334986 2005031 := bstep (se 1 (by rfl) ⟨1503773, by rfl⟩ : syracuseStep 2005031 = 3007547) B3007547
theorem B6092857 : Blo 1334986 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B17119289 : Blo 1334986 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B6764633 : Blo 1334986 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B2005115 : Blo 1334986 2005115 := bstep (se 1 (by rfl) ⟨1503836, by rfl⟩ : syracuseStep 2005115 = 3007673) B3007673
theorem B4511915 : Blo 1334986 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B2005241 : Blo 1334986 2005241 := bstep (se 2 (by rfl) ⟨751965, by rfl⟩ : syracuseStep 2005241 = 1503931) B1503931
theorem B2537801 : Blo 1334986 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B2005343 : Blo 1334986 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B2005355 : Blo 1334986 2005355 := bstep (se 1 (by rfl) ⟨1504016, by rfl⟩ : syracuseStep 2005355 = 3008033) B3008033
theorem B13719941 : Blo 1334986 13719941 := bstep (se 4 (by rfl) ⟨1286244, by rfl⟩ : syracuseStep 13719941 = 2572489) B2572489
theorem B2406839 : Blo 1334986 2406839 := bstep (se 1 (by rfl) ⟨1805129, by rfl⟩ : syracuseStep 2406839 = 3610259) B3610259
theorem B12843467 : Blo 1334986 12843467 := bstep (se 1 (by rfl) ⟨9632600, by rfl⟩ : syracuseStep 12843467 = 19265201) B19265201
theorem B3660275 : Blo 1334986 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B3004937 : Blo 1334986 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B61684267 : Blo 1334986 61684267 := bstep (se 1 (by rfl) ⟨46263200, by rfl⟩ : syracuseStep 61684267 = 92526401) B92526401
theorem B2439737 : Blo 1334986 2439737 := bstep (se 2 (by rfl) ⟨914901, by rfl⟩ : syracuseStep 2439737 = 1829803) B1829803
theorem B9140795 : Blo 1334986 9140795 := bstep (se 1 (by rfl) ⟨6855596, by rfl⟩ : syracuseStep 9140795 = 13711193) B13711193
theorem B2472527 : Blo 1334986 2472527 := bstep (se 1 (by rfl) ⟨1854395, by rfl⟩ : syracuseStep 2472527 = 3708791) B3708791
theorem B2406991 : Blo 1334986 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B5143175 : Blo 1334986 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B4283027 : Blo 1334986 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B8674121 : Blo 1334986 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B3005279 : Blo 1334986 3005279 := bstep (se 1 (by rfl) ⟨2253959, by rfl⟩ : syracuseStep 3005279 = 4507919) B4507919
theorem B6511535 : Blo 1334986 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B3210167 : Blo 1334986 3210167 := bstep (se 1 (by rfl) ⟨2407625, by rfl⟩ : syracuseStep 3210167 = 4815251) B4815251
theorem B3005459 : Blo 1334986 3005459 := bstep (se 1 (by rfl) ⟨2254094, by rfl⟩ : syracuseStep 3005459 = 4508189) B4508189
theorem B10279979 : Blo 1334986 10279979 := bstep (se 1 (by rfl) ⟨7709984, by rfl⟩ : syracuseStep 10279979 = 15419969) B15419969
theorem B10140875 : Blo 1334986 10140875 := bstep (se 1 (by rfl) ⟨7605656, by rfl⟩ : syracuseStep 10140875 = 15211313) B15211313
theorem B3382519 : Blo 1334986 3382519 := bstep (se 1 (by rfl) ⟨2536889, by rfl⟩ : syracuseStep 3382519 = 5073779) B5073779
theorem B32963831 : Blo 1334986 32963831 := bstep (se 1 (by rfl) ⟨24722873, by rfl⟩ : syracuseStep 32963831 = 49445747) B49445747
theorem B3005801 : Blo 1334986 3005801 := bstep (se 2 (by rfl) ⟨1127175, by rfl⟩ : syracuseStep 3005801 = 2254351) B2254351
theorem B4062683 : Blo 1334986 4062683 := bstep (se 1 (by rfl) ⟨3047012, by rfl⟩ : syracuseStep 4062683 = 6094025) B6094025
theorem B3382793 : Blo 1334986 3382793 := bstep (se 2 (by rfl) ⟨1268547, by rfl⟩ : syracuseStep 3382793 = 2537095) B2537095
theorem B7609895 : Blo 1334986 7609895 := bstep (se 1 (by rfl) ⟨5707421, by rfl⟩ : syracuseStep 7609895 = 11414843) B11414843
theorem B3382823 : Blo 1334986 3382823 := bstep (se 1 (by rfl) ⟨2537117, by rfl⟩ : syracuseStep 3382823 = 5074235) B5074235
theorem B1605199 : Blo 1334986 1605199 := bstep (se 1 (by rfl) ⟨1203899, by rfl⟩ : syracuseStep 1605199 = 2407799) B2407799
theorem B5144161 : Blo 1334986 5144161 := bstep (se 2 (by rfl) ⟨1929060, by rfl⟩ : syracuseStep 5144161 = 3858121) B3858121
theorem B9756305 : Blo 1334986 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B5070545 : Blo 1334986 5070545 := bstep (se 2 (by rfl) ⟨1901454, by rfl⟩ : syracuseStep 5070545 = 3802909) B3802909
theorem B1335003 : Blo 1334986 1335003 := bstep (se 1 (by rfl) ⟨1001252, by rfl⟩ : syracuseStep 1335003 = 2002505) B2002505
theorem B9625337 : Blo 1334986 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B1335079 : Blo 1334986 1335079 := bstep (se 1 (by rfl) ⟨1001309, by rfl⟩ : syracuseStep 1335079 = 2002619) B2002619
theorem B1335119 : Blo 1334986 1335119 := bstep (se 1 (by rfl) ⟨1001339, by rfl⟩ : syracuseStep 1335119 = 2002679) B2002679
theorem B1335135 : Blo 1334986 1335135 := bstep (se 1 (by rfl) ⟨1001351, by rfl⟩ : syracuseStep 1335135 = 2002703) B2002703
theorem B3383147 : Blo 1334986 3383147 := bstep (se 1 (by rfl) ⟨2537360, by rfl⟩ : syracuseStep 3383147 = 5074721) B5074721
theorem B1335163 : Blo 1334986 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B21979043 : Blo 1334986 21979043 := bstep (se 1 (by rfl) ⟨16484282, by rfl⟩ : syracuseStep 21979043 = 32968565) B32968565
theorem B1335215 : Blo 1334986 1335215 := bstep (se 1 (by rfl) ⟨1001411, by rfl⟩ : syracuseStep 1335215 = 2002823) B2002823
theorem B2408375 : Blo 1334986 2408375 := bstep (se 1 (by rfl) ⟨1806281, by rfl⟩ : syracuseStep 2408375 = 3612563) B3612563
theorem B3006395 : Blo 1334986 3006395 := bstep (se 1 (by rfl) ⟨2254796, by rfl⟩ : syracuseStep 3006395 = 4509593) B4509593
theorem B1335239 : Blo 1334986 1335239 := bstep (se 1 (by rfl) ⟨1001429, by rfl⟩ : syracuseStep 1335239 = 2002859) B2002859
theorem B1335259 : Blo 1334986 1335259 := bstep (se 1 (by rfl) ⟨1001444, by rfl⟩ : syracuseStep 1335259 = 2002889) B2002889
theorem B17113139 : Blo 1334986 17113139 := bstep (se 1 (by rfl) ⟨12834854, by rfl⟩ : syracuseStep 17113139 = 25669709) B25669709
theorem B4505705 : Blo 1334986 4505705 := bstep (se 2 (by rfl) ⟨1689639, by rfl⟩ : syracuseStep 4505705 = 3379279) B3379279
theorem B4817107 : Blo 1334986 4817107 := bstep (se 1 (by rfl) ⟨3612830, by rfl⟩ : syracuseStep 4817107 = 7225661) B7225661
theorem B1335583 : Blo 1334986 1335583 := bstep (se 1 (by rfl) ⟨1001687, by rfl⟩ : syracuseStep 1335583 = 2003375) B2003375
theorem B1335643 : Blo 1334986 1335643 := bstep (se 1 (by rfl) ⟨1001732, by rfl⟩ : syracuseStep 1335643 = 2003465) B2003465
theorem B3006827 : Blo 1334986 3006827 := bstep (se 1 (by rfl) ⟨2255120, by rfl⟩ : syracuseStep 3006827 = 4510241) B4510241
theorem B1335663 : Blo 1334986 1335663 := bstep (se 1 (by rfl) ⟨1001747, by rfl⟩ : syracuseStep 1335663 = 2003495) B2003495
theorem B1335719 : Blo 1334986 1335719 := bstep (se 1 (by rfl) ⟨1001789, by rfl⟩ : syracuseStep 1335719 = 2003579) B2003579
theorem B1335803 : Blo 1334986 1335803 := bstep (se 1 (by rfl) ⟨1001852, by rfl⟩ : syracuseStep 1335803 = 2003705) B2003705
theorem B3006971 : Blo 1334986 3006971 := bstep (se 1 (by rfl) ⟨2255228, by rfl⟩ : syracuseStep 3006971 = 4510457) B4510457
theorem B6758963 : Blo 1334986 6758963 := bstep (se 1 (by rfl) ⟨5069222, by rfl⟩ : syracuseStep 6758963 = 10138445) B10138445
theorem B1335871 : Blo 1334986 1335871 := bstep (se 1 (by rfl) ⟨1001903, by rfl⟩ : syracuseStep 1335871 = 2003807) B2003807
theorem B1335879 : Blo 1334986 1335879 := bstep (se 1 (by rfl) ⟨1001909, by rfl⟩ : syracuseStep 1335879 = 2003819) B2003819
theorem B2253433 : Blo 1334986 2253433 := bstep (se 2 (by rfl) ⟨845037, by rfl⟩ : syracuseStep 2253433 = 1690075) B1690075
theorem B3007097 : Blo 1334986 3007097 := bstep (se 2 (by rfl) ⟨1127661, by rfl⟩ : syracuseStep 3007097 = 2255323) B2255323
theorem B6767225 : Blo 1334986 6767225 := bstep (se 2 (by rfl) ⟨2537709, by rfl⟩ : syracuseStep 6767225 = 5075419) B5075419
theorem B7226009 : Blo 1334986 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B2851499 : Blo 1334986 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B5071531 : Blo 1334986 5071531 := bstep (se 1 (by rfl) ⟨3803648, by rfl⟩ : syracuseStep 5071531 = 7607297) B7607297
theorem B2253487 : Blo 1334986 2253487 := bstep (se 1 (by rfl) ⟨1690115, by rfl⟩ : syracuseStep 2253487 = 3380231) B3380231
theorem B3007151 : Blo 1334986 3007151 := bstep (se 1 (by rfl) ⟨2255363, by rfl⟩ : syracuseStep 3007151 = 4510727) B4510727
theorem B30835403 : Blo 1334986 30835403 := bstep (se 1 (by rfl) ⟨23126552, by rfl⟩ : syracuseStep 30835403 = 46253105) B46253105
theorem B1336031 : Blo 1334986 1336031 := bstep (se 1 (by rfl) ⟨1002023, by rfl⟩ : syracuseStep 1336031 = 2004047) B2004047
theorem B3007223 : Blo 1334986 3007223 := bstep (se 1 (by rfl) ⟨2255417, by rfl⟩ : syracuseStep 3007223 = 4510835) B4510835
theorem B1336111 : Blo 1334986 1336111 := bstep (se 1 (by rfl) ⟨1002083, by rfl⟩ : syracuseStep 1336111 = 2004167) B2004167
theorem B25690931 : Blo 1334986 25690931 := bstep (se 1 (by rfl) ⟨19268198, by rfl⟩ : syracuseStep 25690931 = 38536397) B38536397
theorem B1336219 : Blo 1334986 1336219 := bstep (se 1 (by rfl) ⟨1002164, by rfl⟩ : syracuseStep 1336219 = 2004329) B2004329
theorem B3007403 : Blo 1334986 3007403 := bstep (se 1 (by rfl) ⟨2255552, by rfl⟩ : syracuseStep 3007403 = 4511105) B4511105
theorem B2933675 : Blo 1334986 2933675 := bstep (se 1 (by rfl) ⟨2200256, by rfl⟩ : syracuseStep 2933675 = 4400513) B4400513
theorem B4506569 : Blo 1334986 4506569 := bstep (se 2 (by rfl) ⟨1689963, by rfl⟩ : syracuseStep 4506569 = 3379927) B3379927
theorem B1336271 : Blo 1334986 1336271 := bstep (se 1 (by rfl) ⟨1002203, by rfl⟩ : syracuseStep 1336271 = 2004407) B2004407
theorem B5071835 : Blo 1334986 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B1336295 : Blo 1334986 1336295 := bstep (se 1 (by rfl) ⟨1002221, by rfl⟩ : syracuseStep 1336295 = 2004443) B2004443
theorem B28886033 : Blo 1334986 28886033 := bstep (se 2 (by rfl) ⟨10832262, by rfl⟩ : syracuseStep 28886033 = 21664525) B21664525
theorem B3425419 : Blo 1334986 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B4506839 : Blo 1334986 4506839 := bstep (se 1 (by rfl) ⟨3380129, by rfl⟩ : syracuseStep 4506839 = 6760259) B6760259
theorem B1336607 : Blo 1334986 1336607 := bstep (se 1 (by rfl) ⟨1002455, by rfl⟩ : syracuseStep 1336607 = 2004911) B2004911
theorem B15418667 : Blo 1334986 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B1336667 : Blo 1334986 1336667 := bstep (se 1 (by rfl) ⟨1002500, by rfl⟩ : syracuseStep 1336667 = 2005001) B2005001
theorem B1336687 : Blo 1334986 1336687 := bstep (se 1 (by rfl) ⟨1002515, by rfl⟩ : syracuseStep 1336687 = 2005031) B2005031
theorem B11412859 : Blo 1334986 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B1336743 : Blo 1334986 1336743 := bstep (se 1 (by rfl) ⟨1002557, by rfl⟩ : syracuseStep 1336743 = 2005115) B2005115
theorem B4818365 : Blo 1334986 4818365 := bstep (se 3 (by rfl) ⟨903443, by rfl⟩ : syracuseStep 4818365 = 1806887) B1806887
theorem B3007943 : Blo 1334986 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B5703149 : Blo 1334986 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B1336827 : Blo 1334986 1336827 := bstep (se 1 (by rfl) ⟨1002620, by rfl⟩ : syracuseStep 1336827 = 2005241) B2005241
theorem B4064825 : Blo 1334986 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B1336895 : Blo 1334986 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B1336903 : Blo 1334986 1336903 := bstep (se 1 (by rfl) ⟨1002677, by rfl⟩ : syracuseStep 1336903 = 2005355) B2005355
theorem B57738851 : Blo 1334986 57738851 := bstep (se 1 (by rfl) ⟨43304138, by rfl⟩ : syracuseStep 57738851 = 86608277) B86608277
theorem B8562311 : Blo 1334986 8562311 := bstep (se 1 (by rfl) ⟨6421733, by rfl⟩ : syracuseStep 8562311 = 12843467) B12843467
theorem B1648351 : Blo 1334986 1648351 := bstep (se 1 (by rfl) ⟨1236263, by rfl⟩ : syracuseStep 1648351 = 2472527) B2472527
theorem B2140111 : Blo 1334986 2140111 := bstep (se 1 (by rfl) ⟨1605083, by rfl⟩ : syracuseStep 2140111 = 3210167) B3210167
theorem B36571151 : Blo 1334986 36571151 := bstep (se 1 (by rfl) ⟨27428363, by rfl⟩ : syracuseStep 36571151 = 54856727) B54856727
theorem B2140265 : Blo 1334986 2140265 := bstep (se 2 (by rfl) ⟨802599, by rfl⟩ : syracuseStep 2140265 = 1605199) B1605199
theorem B6858881 : Blo 1334986 6858881 := bstep (se 2 (by rfl) ⟨2572080, by rfl⟩ : syracuseStep 6858881 = 5144161) B5144161
theorem B6760583 : Blo 1334986 6760583 := bstep (se 1 (by rfl) ⟨5070437, by rfl⟩ : syracuseStep 6760583 = 10140875) B10140875
theorem B15222977 : Blo 1334986 15222977 := bstep (se 2 (by rfl) ⟨5708616, by rfl⟩ : syracuseStep 15222977 = 11417233) B11417233
theorem B2255195 : Blo 1334986 2255195 := bstep (se 1 (by rfl) ⟨1691396, by rfl⟩ : syracuseStep 2255195 = 3382793) B3382793
theorem B5073263 : Blo 1334986 5073263 := bstep (se 1 (by rfl) ⟨3804947, by rfl⟩ : syracuseStep 5073263 = 7609895) B7609895
theorem B2255215 : Blo 1334986 2255215 := bstep (se 1 (by rfl) ⟨1691411, by rfl⟩ : syracuseStep 2255215 = 3382823) B3382823
theorem B1689979 : Blo 1334986 1689979 := bstep (se 1 (by rfl) ⟨1267484, by rfl⟩ : syracuseStep 1689979 = 2534969) B2534969
theorem B6416813 : Blo 1334986 6416813 := bstep (se 3 (by rfl) ⟨1203152, by rfl⟩ : syracuseStep 6416813 = 2406305) B2406305
theorem B6416891 : Blo 1334986 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B2255431 : Blo 1334986 2255431 := bstep (se 1 (by rfl) ⟨1691573, by rfl⟩ : syracuseStep 2255431 = 3383147) B3383147
theorem B3804059 : Blo 1334986 3804059 := bstep (se 1 (by rfl) ⟨2853044, by rfl⟩ : syracuseStep 3804059 = 5706089) B5706089
theorem B2255863 : Blo 1334986 2255863 := bstep (se 1 (by rfl) ⟨1691897, by rfl⟩ : syracuseStep 2255863 = 3383795) B3383795
theorem B17108171 : Blo 1334986 17108171 := bstep (se 1 (by rfl) ⟨12831128, by rfl⟩ : syracuseStep 17108171 = 25662257) B25662257
theorem B4508891 : Blo 1334986 4508891 := bstep (se 1 (by rfl) ⟨3381668, by rfl⟩ : syracuseStep 4508891 = 6763337) B6763337
theorem B1691047 : Blo 1334986 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B5074447 : Blo 1334986 5074447 := bstep (se 1 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 5074447 = 7611671) B7611671
theorem B1502815 : Blo 1334986 1502815 := bstep (se 1 (by rfl) ⟨1127111, by rfl⟩ : syracuseStep 1502815 = 2254223) B2254223
theorem B12840545 : Blo 1334986 12840545 := bstep (se 2 (by rfl) ⟨4815204, by rfl⟩ : syracuseStep 12840545 = 9630409) B9630409
theorem B24391277 : Blo 1334986 24391277 := bstep (se 3 (by rfl) ⟨4573364, by rfl⟩ : syracuseStep 24391277 = 9146729) B9146729
theorem B3804833 : Blo 1334986 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B2002667 : Blo 1334986 2002667 := bstep (se 1 (by rfl) ⟨1502000, by rfl⟩ : syracuseStep 2002667 = 3004001) B3004001
theorem B1691371 : Blo 1334986 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B6418237 : Blo 1334986 6418237 := bstep (se 3 (by rfl) ⟨1203419, by rfl⟩ : syracuseStep 6418237 = 2406839) B2406839
theorem B10833821 : Blo 1334986 10833821 := bstep (se 3 (by rfl) ⟨2031341, by rfl⟩ : syracuseStep 10833821 = 4062683) B4062683
theorem B2002895 : Blo 1334986 2002895 := bstep (se 1 (by rfl) ⟨1502171, by rfl⟩ : syracuseStep 2002895 = 3004343) B3004343
theorem B1691599 : Blo 1334986 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B9760733 : Blo 1334986 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B5705747 : Blo 1334986 5705747 := bstep (se 1 (by rfl) ⟨4279310, by rfl⟩ : syracuseStep 5705747 = 8558621) B8558621
theorem B4509755 : Blo 1334986 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B3805289 : Blo 1334986 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B1691867 : Blo 1334986 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B9146627 : Blo 1334986 9146627 := bstep (se 1 (by rfl) ⟨6859970, by rfl⟩ : syracuseStep 9146627 = 13719941) B13719941
theorem B4510025 : Blo 1334986 4510025 := bstep (se 2 (by rfl) ⟨1691259, by rfl⟩ : syracuseStep 4510025 = 3382519) B3382519
theorem B2003291 : Blo 1334986 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B16691561 : Blo 1334986 16691561 := bstep (se 2 (by rfl) ⟨6259335, by rfl⟩ : syracuseStep 16691561 = 12518671) B12518671
theorem B1626491 : Blo 1334986 1626491 := bstep (se 1 (by rfl) ⟨1219868, by rfl⟩ : syracuseStep 1626491 = 2439737) B2439737
theorem B3428783 : Blo 1334986 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B2855351 : Blo 1334986 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B2003519 : Blo 1334986 2003519 := bstep (se 1 (by rfl) ⟨1502639, by rfl⟩ : syracuseStep 2003519 = 3005279) B3005279
theorem B2003639 : Blo 1334986 2003639 := bstep (se 1 (by rfl) ⟨1502729, by rfl⟩ : syracuseStep 2003639 = 3005459) B3005459
theorem B6853319 : Blo 1334986 6853319 := bstep (se 1 (by rfl) ⟨5139989, by rfl⟩ : syracuseStep 6853319 = 10279979) B10279979
theorem B1503967 : Blo 1334986 1503967 := bstep (se 1 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 1503967 = 2255951) B2255951
theorem B21975887 : Blo 1334986 21975887 := bstep (se 1 (by rfl) ⟨16481915, by rfl⟩ : syracuseStep 21975887 = 32963831) B32963831
theorem B2003867 : Blo 1334986 2003867 := bstep (se 1 (by rfl) ⟨1502900, by rfl⟩ : syracuseStep 2003867 = 3005801) B3005801
theorem B3380363 : Blo 1334986 3380363 := bstep (se 1 (by rfl) ⟨2535272, by rfl⟩ : syracuseStep 3380363 = 5070545) B5070545
theorem B14652695 : Blo 1334986 14652695 := bstep (se 1 (by rfl) ⟨10989521, by rfl⟩ : syracuseStep 14652695 = 21979043) B21979043
theorem B2004263 : Blo 1334986 2004263 := bstep (se 1 (by rfl) ⟨1503197, by rfl⟩ : syracuseStep 2004263 = 3006395) B3006395
theorem B3380575 : Blo 1334986 3380575 := bstep (se 1 (by rfl) ⟨2535431, by rfl⟩ : syracuseStep 3380575 = 5070863) B5070863
theorem B2004347 : Blo 1334986 2004347 := bstep (se 1 (by rfl) ⟨1503260, by rfl⟩ : syracuseStep 2004347 = 3006521) B3006521
theorem B3003785 : Blo 1334986 3003785 := bstep (se 2 (by rfl) ⟨1126419, by rfl⟩ : syracuseStep 3003785 = 2252839) B2252839
theorem B3855755 : Blo 1334986 3855755 := bstep (se 1 (by rfl) ⟨2891816, by rfl⟩ : syracuseStep 3855755 = 5783633) B5783633
theorem B8123809 : Blo 1334986 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B11564491 : Blo 1334986 11564491 := bstep (se 1 (by rfl) ⟨8673368, by rfl⟩ : syracuseStep 11564491 = 17346737) B17346737
theorem B7222765 : Blo 1334986 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B2004473 : Blo 1334986 2004473 := bstep (se 2 (by rfl) ⟨751677, by rfl⟩ : syracuseStep 2004473 = 1503355) B1503355
theorem B3003911 : Blo 1334986 3003911 := bstep (se 1 (by rfl) ⟨2252933, by rfl⟩ : syracuseStep 3003911 = 4505867) B4505867
theorem B2004575 : Blo 1334986 2004575 := bstep (se 1 (by rfl) ⟨1503431, by rfl⟩ : syracuseStep 2004575 = 3006863) B3006863
theorem B3004091 : Blo 1334986 3004091 := bstep (se 1 (by rfl) ⟨2253068, by rfl⟩ : syracuseStep 3004091 = 4506137) B4506137
theorem B2004791 : Blo 1334986 2004791 := bstep (se 1 (by rfl) ⟨1503593, by rfl⟩ : syracuseStep 2004791 = 3007187) B3007187
theorem B3004217 : Blo 1334986 3004217 := bstep (se 2 (by rfl) ⟨1126581, by rfl⟩ : syracuseStep 3004217 = 2253163) B2253163
theorem B6764471 : Blo 1334986 6764471 := bstep (se 1 (by rfl) ⟨5073353, by rfl⟩ : syracuseStep 6764471 = 10146707) B10146707
theorem B82245689 : Blo 1334986 82245689 := bstep (se 2 (by rfl) ⟨30842133, by rfl⟩ : syracuseStep 82245689 = 61684267) B61684267
theorem B3209321 : Blo 1334986 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B2005097 : Blo 1334986 2005097 := bstep (se 2 (by rfl) ⟨751911, by rfl⟩ : syracuseStep 2005097 = 1503823) B1503823
theorem B2005415 : Blo 1334986 2005415 := bstep (se 1 (by rfl) ⟨1504061, by rfl⟩ : syracuseStep 2005415 = 3008123) B3008123
theorem B3004847 : Blo 1334986 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B3004883 : Blo 1334986 3004883 := bstep (se 1 (by rfl) ⟨2253662, by rfl⟩ : syracuseStep 3004883 = 4507325) B4507325
theorem B5069375 : Blo 1334986 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B3004991 : Blo 1334986 3004991 := bstep (se 1 (by rfl) ⟨2253743, by rfl⟩ : syracuseStep 3004991 = 4507487) B4507487
theorem B6765119 : Blo 1334986 6765119 := bstep (se 1 (by rfl) ⟨5073839, by rfl⟩ : syracuseStep 6765119 = 10147679) B10147679
theorem B3005099 : Blo 1334986 3005099 := bstep (se 1 (by rfl) ⟨2253824, by rfl⟩ : syracuseStep 3005099 = 4507649) B4507649
theorem B3381983 : Blo 1334986 3381983 := bstep (se 1 (by rfl) ⟨2536487, by rfl⟩ : syracuseStep 3381983 = 5072975) B5072975
theorem B5069587 : Blo 1334986 5069587 := bstep (se 1 (by rfl) ⟨3802190, by rfl⟩ : syracuseStep 5069587 = 7604381) B7604381
theorem B13007789 : Blo 1334986 13007789 := bstep (se 3 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 13007789 = 4877921) B4877921
theorem B6093863 : Blo 1334986 6093863 := bstep (se 1 (by rfl) ⟨4570397, by rfl⟩ : syracuseStep 6093863 = 9140795) B9140795
theorem B3005639 : Blo 1334986 3005639 := bstep (se 1 (by rfl) ⟨2254229, by rfl⟩ : syracuseStep 3005639 = 4508459) B4508459
theorem B5782747 : Blo 1334986 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B4341023 : Blo 1334986 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B3005819 : Blo 1334986 3005819 := bstep (se 1 (by rfl) ⟨2254364, by rfl⟩ : syracuseStep 3005819 = 4508729) B4508729
theorem B3005945 : Blo 1334986 3005945 := bstep (se 2 (by rfl) ⟨1127229, by rfl⟩ : syracuseStep 3005945 = 2254459) B2254459
theorem B64953899 : Blo 1334986 64953899 := bstep (se 1 (by rfl) ⟨48715424, by rfl⟩ : syracuseStep 64953899 = 97430849) B97430849
theorem B11419217 : Blo 1334986 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B3006035 : Blo 1334986 3006035 := bstep (se 1 (by rfl) ⟨2254526, by rfl⟩ : syracuseStep 3006035 = 4509053) B4509053
theorem B5709473 : Blo 1334986 5709473 := bstep (se 2 (by rfl) ⟨2141052, by rfl⟩ : syracuseStep 5709473 = 4282105) B4282105
theorem B1335007 : Blo 1334986 1335007 := bstep (se 1 (by rfl) ⟨1001255, by rfl⟩ : syracuseStep 1335007 = 2002511) B2002511
theorem B3006215 : Blo 1334986 3006215 := bstep (se 1 (by rfl) ⟨2254661, by rfl⟩ : syracuseStep 3006215 = 4509323) B4509323
theorem B6504203 : Blo 1334986 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B1335087 : Blo 1334986 1335087 := bstep (se 1 (by rfl) ⟨1001315, by rfl⟩ : syracuseStep 1335087 = 2002631) B2002631
theorem B2285369 : Blo 1334986 2285369 := bstep (se 2 (by rfl) ⟨857013, by rfl⟩ : syracuseStep 2285369 = 1714027) B1714027
theorem B1335195 : Blo 1334986 1335195 := bstep (se 1 (by rfl) ⟨1001396, by rfl⟩ : syracuseStep 1335195 = 2002793) B2002793
theorem B1335247 : Blo 1334986 1335247 := bstep (se 1 (by rfl) ⟨1001435, by rfl⟩ : syracuseStep 1335247 = 2002871) B2002871
theorem B1605583 : Blo 1334986 1605583 := bstep (se 1 (by rfl) ⟨1204187, by rfl⟩ : syracuseStep 1605583 = 2408375) B2408375
theorem B1335271 : Blo 1334986 1335271 := bstep (se 1 (by rfl) ⟨1001453, by rfl⟩ : syracuseStep 1335271 = 2002907) B2002907
theorem B3006503 : Blo 1334986 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B3006683 : Blo 1334986 3006683 := bstep (se 1 (by rfl) ⟨2255012, by rfl⟩ : syracuseStep 3006683 = 4510025) B4510025
theorem B1335527 : Blo 1334986 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B6422809 : Blo 1334986 6422809 := bstep (se 2 (by rfl) ⟨2408553, by rfl⟩ : syracuseStep 6422809 = 4817107) B4817107
theorem B2285855 : Blo 1334986 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B4505975 : Blo 1334986 4505975 := bstep (se 1 (by rfl) ⟨3379481, by rfl⟩ : syracuseStep 4505975 = 6758963) B6758963
theorem B1335679 : Blo 1334986 1335679 := bstep (se 1 (by rfl) ⟨1001759, by rfl⟩ : syracuseStep 1335679 = 2003519) B2003519
theorem B4817339 : Blo 1334986 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B1900999 : Blo 1334986 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B1335759 : Blo 1334986 1335759 := bstep (se 1 (by rfl) ⟨1001819, by rfl⟩ : syracuseStep 1335759 = 2003639) B2003639
theorem B3006953 : Blo 1334986 3006953 := bstep (se 2 (by rfl) ⟨1127607, by rfl⟩ : syracuseStep 3006953 = 2255215) B2255215
theorem B2253305 : Blo 1334986 2253305 := bstep (se 2 (by rfl) ⟨844989, by rfl⟩ : syracuseStep 2253305 = 1689979) B1689979
theorem B1335911 : Blo 1334986 1335911 := bstep (se 1 (by rfl) ⟨1001933, by rfl⟩ : syracuseStep 1335911 = 2003867) B2003867
theorem B18268901 : Blo 1334986 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B2253575 : Blo 1334986 2253575 := bstep (se 1 (by rfl) ⟨1690181, by rfl⟩ : syracuseStep 2253575 = 3380363) B3380363
theorem B3007241 : Blo 1334986 3007241 := bstep (se 2 (by rfl) ⟨1127715, by rfl⟩ : syracuseStep 3007241 = 2255431) B2255431
theorem B1336175 : Blo 1334986 1336175 := bstep (se 1 (by rfl) ⟨1002131, by rfl⟩ : syracuseStep 1336175 = 2004263) B2004263
theorem B1336231 : Blo 1334986 1336231 := bstep (se 1 (by rfl) ⟨1002173, by rfl⟩ : syracuseStep 1336231 = 2004347) B2004347
theorem B3212243 : Blo 1334986 3212243 := bstep (se 1 (by rfl) ⟨2409182, by rfl⟩ : syracuseStep 3212243 = 4818365) B4818365
theorem B1336315 : Blo 1334986 1336315 := bstep (se 1 (by rfl) ⟨1002236, by rfl⟩ : syracuseStep 1336315 = 2004473) B2004473
theorem B6759449 : Blo 1334986 6759449 := bstep (se 2 (by rfl) ⟨2534793, by rfl⟩ : syracuseStep 6759449 = 5069587) B5069587
theorem B1336383 : Blo 1334986 1336383 := bstep (se 1 (by rfl) ⟨1002287, by rfl⟩ : syracuseStep 1336383 = 2004575) B2004575
theorem B1336527 : Blo 1334986 1336527 := bstep (se 1 (by rfl) ⟨1002395, by rfl⟩ : syracuseStep 1336527 = 2004791) B2004791
theorem B3007817 : Blo 1334986 3007817 := bstep (se 2 (by rfl) ⟨1127931, by rfl⟩ : syracuseStep 3007817 = 2255863) B2255863
theorem B24380767 : Blo 1334986 24380767 := bstep (se 1 (by rfl) ⟨18285575, by rfl⟩ : syracuseStep 24380767 = 36571151) B36571151
theorem B54830459 : Blo 1334986 54830459 := bstep (se 1 (by rfl) ⟨41122844, by rfl⟩ : syracuseStep 54830459 = 82245689) B82245689
theorem B2139547 : Blo 1334986 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B1426843 : Blo 1334986 1426843 := bstep (se 1 (by rfl) ⟨1070132, by rfl⟩ : syracuseStep 1426843 = 2140265) B2140265
theorem B1336731 : Blo 1334986 1336731 := bstep (se 1 (by rfl) ⟨1002548, by rfl⟩ : syracuseStep 1336731 = 2005097) B2005097
theorem B4572587 : Blo 1334986 4572587 := bstep (se 1 (by rfl) ⟨3429440, by rfl⟩ : syracuseStep 4572587 = 6858881) B6858881
theorem B4507055 : Blo 1334986 4507055 := bstep (se 1 (by rfl) ⟨3380291, by rfl⟩ : syracuseStep 4507055 = 6760583) B6760583
theorem B1336943 : Blo 1334986 1336943 := bstep (se 1 (by rfl) ⟨1002707, by rfl⟩ : syracuseStep 1336943 = 2005415) B2005415
theorem B4277875 : Blo 1334986 4277875 := bstep (se 1 (by rfl) ⟨3208406, by rfl⟩ : syracuseStep 4277875 = 6416813) B6416813
theorem B7710329 : Blo 1334986 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B4277927 : Blo 1334986 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B4507433 : Blo 1334986 4507433 := bstep (se 2 (by rfl) ⟨1690287, by rfl⟩ : syracuseStep 4507433 = 3380575) B3380575
theorem B2254655 : Blo 1334986 2254655 := bstep (se 1 (by rfl) ⟨1690991, by rfl⟩ : syracuseStep 2254655 = 3381983) B3381983
theorem B10831745 : Blo 1334986 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B2254729 : Blo 1334986 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B15419321 : Blo 1334986 15419321 := bstep (se 2 (by rfl) ⟨5782245, by rfl⟩ : syracuseStep 15419321 = 11564491) B11564491
theorem B11405447 : Blo 1334986 11405447 := bstep (se 1 (by rfl) ⟨8554085, by rfl⟩ : syracuseStep 11405447 = 17108171) B17108171
theorem B2894015 : Blo 1334986 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B2197801 : Blo 1334986 2197801 := bstep (se 2 (by rfl) ⟨824175, by rfl⟩ : syracuseStep 2197801 = 1648351) B1648351
theorem B2255161 : Blo 1334986 2255161 := bstep (se 2 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 2255161 = 1691371) B1691371
theorem B7612811 : Blo 1334986 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B4336135 : Blo 1334986 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B2853481 : Blo 1334986 2853481 := bstep (se 2 (by rfl) ⟨1070055, by rfl⟩ : syracuseStep 2853481 = 2140111) B2140111
theorem B2140777 : Blo 1334986 2140777 := bstep (se 2 (by rfl) ⟨802791, by rfl⟩ : syracuseStep 2140777 = 1605583) B1605583
theorem B2255465 : Blo 1334986 2255465 := bstep (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) B1691599
theorem B6507155 : Blo 1334986 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B3803831 : Blo 1334986 3803831 := bstep (se 1 (by rfl) ⟨2852873, by rfl⟩ : syracuseStep 3803831 = 5705747) B5705747
theorem B6097751 : Blo 1334986 6097751 := bstep (se 1 (by rfl) ⟨4573313, by rfl⟩ : syracuseStep 6097751 = 9146627) B9146627
theorem B11127707 : Blo 1334986 11127707 := bstep (se 1 (by rfl) ⟨8345780, by rfl⟩ : syracuseStep 11127707 = 16691561) B16691561
theorem B20556935 : Blo 1334986 20556935 := bstep (se 1 (by rfl) ⟨15417701, by rfl⟩ : syracuseStep 20556935 = 30835403) B30835403
theorem B14650591 : Blo 1334986 14650591 := bstep (se 1 (by rfl) ⟨10987943, by rfl⟩ : syracuseStep 14650591 = 21975887) B21975887
theorem B6762041 : Blo 1334986 6762041 := bstep (se 2 (by rfl) ⟨2535765, by rfl⟩ : syracuseStep 6762041 = 5071531) B5071531
theorem B2002523 : Blo 1334986 2002523 := bstep (se 1 (by rfl) ⟨1501892, by rfl⟩ : syracuseStep 2002523 = 3003785) B3003785
theorem B4337309 : Blo 1334986 4337309 := bstep (se 3 (by rfl) ⟨813245, by rfl⟩ : syracuseStep 4337309 = 1626491) B1626491
theorem B2002607 : Blo 1334986 2002607 := bstep (se 1 (by rfl) ⟨1501955, by rfl⟩ : syracuseStep 2002607 = 3003911) B3003911
theorem B2002727 : Blo 1334986 2002727 := bstep (se 1 (by rfl) ⟨1502045, by rfl⟩ : syracuseStep 2002727 = 3004091) B3004091
theorem B7614269 : Blo 1334986 7614269 := bstep (se 3 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 7614269 = 2855351) B2855351
theorem B2002811 : Blo 1334986 2002811 := bstep (se 1 (by rfl) ⟨1502108, by rfl⟩ : syracuseStep 2002811 = 3004217) B3004217
theorem B15208397 : Blo 1334986 15208397 := bstep (se 3 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 15208397 = 5703149) B5703149
theorem B4509647 : Blo 1334986 4509647 := bstep (se 1 (by rfl) ⟨3382235, by rfl⟩ : syracuseStep 4509647 = 6764471) B6764471
theorem B1503463 : Blo 1334986 1503463 := bstep (se 1 (by rfl) ⟨1127597, by rfl⟩ : syracuseStep 1503463 = 2255195) B2255195
theorem B2003231 : Blo 1334986 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B2003255 : Blo 1334986 2003255 := bstep (se 1 (by rfl) ⟨1502441, by rfl⟩ : syracuseStep 2003255 = 3004883) B3004883
theorem B3379583 : Blo 1334986 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B2003327 : Blo 1334986 2003327 := bstep (se 1 (by rfl) ⟨1502495, by rfl⟩ : syracuseStep 2003327 = 3004991) B3004991
theorem B4510079 : Blo 1334986 4510079 := bstep (se 1 (by rfl) ⟨3382559, by rfl⟩ : syracuseStep 4510079 = 6765119) B6765119
theorem B10146221 : Blo 1334986 10146221 := bstep (se 3 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 10146221 = 3804833) B3804833
theorem B2003399 : Blo 1334986 2003399 := bstep (se 1 (by rfl) ⟨1502549, by rfl⟩ : syracuseStep 2003399 = 3005099) B3005099
theorem B15217145 : Blo 1334986 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B2536039 : Blo 1334986 2536039 := bstep (se 1 (by rfl) ⟨1902029, by rfl⟩ : syracuseStep 2536039 = 3804059) B3804059
theorem B8671859 : Blo 1334986 8671859 := bstep (se 1 (by rfl) ⟨6503894, by rfl⟩ : syracuseStep 8671859 = 13007789) B13007789
theorem B9630353 : Blo 1334986 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B2003753 : Blo 1334986 2003753 := bstep (se 2 (by rfl) ⟨751407, by rfl⟩ : syracuseStep 2003753 = 1502815) B1502815
theorem B2003759 : Blo 1334986 2003759 := bstep (se 1 (by rfl) ⟨1502819, by rfl⟩ : syracuseStep 2003759 = 3005639) B3005639
theorem B2003879 : Blo 1334986 2003879 := bstep (se 1 (by rfl) ⟨1502909, by rfl⟩ : syracuseStep 2003879 = 3005819) B3005819
theorem B2003963 : Blo 1334986 2003963 := bstep (se 1 (by rfl) ⟨1502972, by rfl⟩ : syracuseStep 2003963 = 3005945) B3005945
theorem B2004023 : Blo 1334986 2004023 := bstep (se 1 (by rfl) ⟨1503017, by rfl⟩ : syracuseStep 2004023 = 3006035) B3006035
theorem B8557649 : Blo 1334986 8557649 := bstep (se 2 (by rfl) ⟨3209118, by rfl⟩ : syracuseStep 8557649 = 6418237) B6418237
theorem B3806315 : Blo 1334986 3806315 := bstep (se 1 (by rfl) ⟨2854736, by rfl⟩ : syracuseStep 3806315 = 5709473) B5709473
theorem B2004143 : Blo 1334986 2004143 := bstep (se 1 (by rfl) ⟨1503107, by rfl⟩ : syracuseStep 2004143 = 3006215) B3006215
theorem B7222547 : Blo 1334986 7222547 := bstep (se 1 (by rfl) ⟨5416910, by rfl⟩ : syracuseStep 7222547 = 10833821) B10833821
theorem B11408759 : Blo 1334986 11408759 := bstep (se 1 (by rfl) ⟨8556569, by rfl⟩ : syracuseStep 11408759 = 17113139) B17113139
theorem B3003803 : Blo 1334986 3003803 := bstep (se 1 (by rfl) ⟨2252852, by rfl⟩ : syracuseStep 3003803 = 4505705) B4505705
theorem B2536859 : Blo 1334986 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B2004551 : Blo 1334986 2004551 := bstep (se 1 (by rfl) ⟨1503413, by rfl⟩ : syracuseStep 2004551 = 3006827) B3006827
theorem B2004647 : Blo 1334986 2004647 := bstep (se 1 (by rfl) ⟨1503485, by rfl⟩ : syracuseStep 2004647 = 3006971) B3006971
theorem B2004731 : Blo 1334986 2004731 := bstep (se 1 (by rfl) ⟨1503548, by rfl⟩ : syracuseStep 2004731 = 3007097) B3007097
theorem B4511483 : Blo 1334986 4511483 := bstep (se 1 (by rfl) ⟨3383612, by rfl⟩ : syracuseStep 4511483 = 6767225) B6767225
theorem B2004767 : Blo 1334986 2004767 := bstep (se 1 (by rfl) ⟨1503575, by rfl⟩ : syracuseStep 2004767 = 3007151) B3007151
theorem B4568879 : Blo 1334986 4568879 := bstep (se 1 (by rfl) ⟨3426659, by rfl⟩ : syracuseStep 4568879 = 6853319) B6853319
theorem B2004815 : Blo 1334986 2004815 := bstep (se 1 (by rfl) ⟨1503611, by rfl⟩ : syracuseStep 2004815 = 3007223) B3007223
theorem B17127287 : Blo 1334986 17127287 := bstep (se 1 (by rfl) ⟨12845465, by rfl⟩ : syracuseStep 17127287 = 25690931) B25690931
theorem B4511645 : Blo 1334986 4511645 := bstep (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) B1691867
theorem B2004935 : Blo 1334986 2004935 := bstep (se 1 (by rfl) ⟨1503701, by rfl⟩ : syracuseStep 2004935 = 3007403) B3007403
theorem B1955783 : Blo 1334986 1955783 := bstep (se 1 (by rfl) ⟨1466837, by rfl⟩ : syracuseStep 1955783 = 2933675) B2933675
theorem B3004379 : Blo 1334986 3004379 := bstep (se 1 (by rfl) ⟨2253284, by rfl⟩ : syracuseStep 3004379 = 4506569) B4506569
theorem B3381223 : Blo 1334986 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B19257355 : Blo 1334986 19257355 := bstep (se 1 (by rfl) ⟨14443016, by rfl⟩ : syracuseStep 19257355 = 28886033) B28886033
theorem B39073853 : Blo 1334986 39073853 := bstep (se 3 (by rfl) ⟨7326347, by rfl⟩ : syracuseStep 39073853 = 14652695) B14652695
theorem B3004559 : Blo 1334986 3004559 := bstep (se 1 (by rfl) ⟨2253419, by rfl⟩ : syracuseStep 3004559 = 4506839) B4506839
theorem B3004577 : Blo 1334986 3004577 := bstep (se 2 (by rfl) ⟨1126716, by rfl⟩ : syracuseStep 3004577 = 2253433) B2253433
theorem B10279111 : Blo 1334986 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B3004649 : Blo 1334986 3004649 := bstep (se 2 (by rfl) ⟨1126743, by rfl⟩ : syracuseStep 3004649 = 2253487) B2253487
theorem B2570503 : Blo 1334986 2570503 := bstep (se 1 (by rfl) ⟨1927877, by rfl⟩ : syracuseStep 2570503 = 3855755) B3855755
theorem B2005289 : Blo 1334986 2005289 := bstep (se 2 (by rfl) ⟨751983, by rfl⟩ : syracuseStep 2005289 = 1503967) B1503967
theorem B2005295 : Blo 1334986 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B2709883 : Blo 1334986 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B38492567 : Blo 1334986 38492567 := bstep (se 1 (by rfl) ⟨28869425, by rfl⟩ : syracuseStep 38492567 = 57738851) B57738851
theorem B5708207 : Blo 1334986 5708207 := bstep (se 1 (by rfl) ⟨4281155, by rfl⟩ : syracuseStep 5708207 = 8562311) B8562311
theorem B10148651 : Blo 1334986 10148651 := bstep (se 1 (by rfl) ⟨7611488, by rfl⟩ : syracuseStep 10148651 = 15222977) B15222977
theorem B3382175 : Blo 1334986 3382175 := bstep (se 1 (by rfl) ⟨2536631, by rfl⟩ : syracuseStep 3382175 = 5073263) B5073263
theorem B6765929 : Blo 1334986 6765929 := bstep (se 2 (by rfl) ⟨2537223, by rfl⟩ : syracuseStep 6765929 = 5074447) B5074447
theorem B4062575 : Blo 1334986 4062575 := bstep (se 1 (by rfl) ⟨3046931, by rfl⟩ : syracuseStep 4062575 = 6093863) B6093863
theorem B3005927 : Blo 1334986 3005927 := bstep (se 1 (by rfl) ⟨2254445, by rfl⟩ : syracuseStep 3005927 = 4508891) B4508891
theorem B43302599 : Blo 1334986 43302599 := bstep (se 1 (by rfl) ⟨32476949, by rfl⟩ : syracuseStep 43302599 = 64953899) B64953899
theorem B8560363 : Blo 1334986 8560363 := bstep (se 1 (by rfl) ⟨6420272, by rfl⟩ : syracuseStep 8560363 = 12840545) B12840545
theorem B16260851 : Blo 1334986 16260851 := bstep (se 1 (by rfl) ⟨12195638, by rfl⟩ : syracuseStep 16260851 = 24391277) B24391277
theorem B1335111 : Blo 1334986 1335111 := bstep (se 1 (by rfl) ⟨1001333, by rfl⟩ : syracuseStep 1335111 = 2002667) B2002667
theorem B1523579 : Blo 1334986 1523579 := bstep (se 1 (by rfl) ⟨1142684, by rfl⟩ : syracuseStep 1523579 = 2285369) B2285369
theorem B1335263 : Blo 1334986 1335263 := bstep (se 1 (by rfl) ⟨1001447, by rfl⟩ : syracuseStep 1335263 = 2002895) B2002895
theorem B92504213 : Blo 1334986 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B1335487 : Blo 1334986 1335487 := bstep (se 1 (by rfl) ⟨1001615, by rfl⟩ : syracuseStep 1335487 = 2003231) B2003231
theorem B1335503 : Blo 1334986 1335503 := bstep (se 1 (by rfl) ⟨1001627, by rfl⟩ : syracuseStep 1335503 = 2003255) B2003255
theorem B2253055 : Blo 1334986 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B1335551 : Blo 1334986 1335551 := bstep (se 1 (by rfl) ⟨1001663, by rfl⟩ : syracuseStep 1335551 = 2003327) B2003327
theorem B3006719 : Blo 1334986 3006719 := bstep (se 1 (by rfl) ⟨2255039, by rfl⟩ : syracuseStep 3006719 = 4510079) B4510079
theorem B13705481 : Blo 1334986 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B3211559 : Blo 1334986 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B1335599 : Blo 1334986 1335599 := bstep (se 1 (by rfl) ⟨1001699, by rfl⟩ : syracuseStep 1335599 = 2003399) B2003399
theorem B3006881 : Blo 1334986 3006881 := bstep (se 2 (by rfl) ⟨1127580, by rfl⟩ : syracuseStep 3006881 = 2255161) B2255161
theorem B3613177 : Blo 1334986 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B1335835 : Blo 1334986 1335835 := bstep (se 1 (by rfl) ⟨1001876, by rfl⟩ : syracuseStep 1335835 = 2003753) B2003753
theorem B1335839 : Blo 1334986 1335839 := bstep (se 1 (by rfl) ⟨1001879, by rfl⟩ : syracuseStep 1335839 = 2003759) B2003759
theorem B1335919 : Blo 1334986 1335919 := bstep (se 1 (by rfl) ⟨1001939, by rfl⟩ : syracuseStep 1335919 = 2003879) B2003879
theorem B1335975 : Blo 1334986 1335975 := bstep (se 1 (by rfl) ⟨1001981, by rfl⟩ : syracuseStep 1335975 = 2003963) B2003963
theorem B4506299 : Blo 1334986 4506299 := bstep (se 1 (by rfl) ⟨3379724, by rfl⟩ : syracuseStep 4506299 = 6759449) B6759449
theorem B1336015 : Blo 1334986 1336015 := bstep (se 1 (by rfl) ⟨1002011, by rfl⟩ : syracuseStep 1336015 = 2004023) B2004023
theorem B19260125 : Blo 1334986 19260125 := bstep (se 3 (by rfl) ⟨3611273, by rfl⟩ : syracuseStep 19260125 = 7222547) B7222547
theorem B1336095 : Blo 1334986 1336095 := bstep (se 1 (by rfl) ⟨1002071, by rfl⟩ : syracuseStep 1336095 = 2004143) B2004143
theorem B36553639 : Blo 1334986 36553639 := bstep (se 1 (by rfl) ⟨27415229, by rfl⟩ : syracuseStep 36553639 = 54830459) B54830459
theorem B3048391 : Blo 1334986 3048391 := bstep (se 1 (by rfl) ⟨2286293, by rfl⟩ : syracuseStep 3048391 = 4572587) B4572587
theorem B1336367 : Blo 1334986 1336367 := bstep (se 1 (by rfl) ⟨1002275, by rfl⟩ : syracuseStep 1336367 = 2004551) B2004551
theorem B2851951 : Blo 1334986 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B1336431 : Blo 1334986 1336431 := bstep (se 1 (by rfl) ⟨1002323, by rfl⟩ : syracuseStep 1336431 = 2004647) B2004647
theorem B1336487 : Blo 1334986 1336487 := bstep (se 1 (by rfl) ⟨1002365, by rfl⟩ : syracuseStep 1336487 = 2004731) B2004731
theorem B3007655 : Blo 1334986 3007655 := bstep (se 1 (by rfl) ⟨2255741, by rfl⟩ : syracuseStep 3007655 = 4511483) B4511483
theorem B1336511 : Blo 1334986 1336511 := bstep (se 1 (by rfl) ⟨1002383, by rfl⟩ : syracuseStep 1336511 = 2004767) B2004767
theorem B1336543 : Blo 1334986 1336543 := bstep (se 1 (by rfl) ⟨1002407, by rfl⟩ : syracuseStep 1336543 = 2004815) B2004815
theorem B3007763 : Blo 1334986 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B1336623 : Blo 1334986 1336623 := bstep (se 1 (by rfl) ⟨1002467, by rfl⟩ : syracuseStep 1336623 = 2004935) B2004935
theorem B7603631 : Blo 1334986 7603631 := bstep (se 1 (by rfl) ⟨5702723, by rfl⟩ : syracuseStep 7603631 = 11405447) B11405447
theorem B1336859 : Blo 1334986 1336859 := bstep (se 1 (by rfl) ⟨1002644, by rfl⟩ : syracuseStep 1336859 = 2005289) B2005289
theorem B1336863 : Blo 1334986 1336863 := bstep (se 1 (by rfl) ⟨1002647, by rfl⟩ : syracuseStep 1336863 = 2005295) B2005295
theorem B32507689 : Blo 1334986 32507689 := bstep (se 2 (by rfl) ⟨12190383, by rfl⟩ : syracuseStep 32507689 = 24380767) B24380767
theorem B2852729 : Blo 1334986 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B1902457 : Blo 1334986 1902457 := bstep (se 2 (by rfl) ⟨713421, by rfl⟩ : syracuseStep 1902457 = 1426843) B1426843
theorem B4065167 : Blo 1334986 4065167 := bstep (se 1 (by rfl) ⟨3048875, by rfl⟩ : syracuseStep 4065167 = 6097751) B6097751
theorem B2254783 : Blo 1334986 2254783 := bstep (se 1 (by rfl) ⟨1691087, by rfl⟩ : syracuseStep 2254783 = 3382175) B3382175
theorem B5703833 : Blo 1334986 5703833 := bstep (se 2 (by rfl) ⟨2138937, by rfl⟩ : syracuseStep 5703833 = 4277875) B4277875
theorem B11413817 : Blo 1334986 11413817 := bstep (se 2 (by rfl) ⟨4280181, by rfl⟩ : syracuseStep 11413817 = 8560363) B8560363
theorem B4508027 : Blo 1334986 4508027 := bstep (se 1 (by rfl) ⟨3381020, by rfl⟩ : syracuseStep 4508027 = 6762041) B6762041
theorem B10840567 : Blo 1334986 10840567 := bstep (se 1 (by rfl) ⟨8130425, by rfl⟩ : syracuseStep 10840567 = 16260851) B16260851
theorem B4508297 : Blo 1334986 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B25676473 : Blo 1334986 25676473 := bstep (se 2 (by rfl) ⟨9628677, by rfl⟩ : syracuseStep 25676473 = 19257355) B19257355
theorem B24382453 : Blo 1334986 24382453 := bstep (se 5 (by rfl) ⟨1142927, by rfl⟩ : syracuseStep 24382453 = 2285855) B2285855
theorem B1502203 : Blo 1334986 1502203 := bstep (se 1 (by rfl) ⟨1126652, by rfl⟩ : syracuseStep 1502203 = 2253305) B2253305
theorem B10144763 : Blo 1334986 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B3427337 : Blo 1334986 3427337 := bstep (se 2 (by rfl) ⟨1285251, by rfl⟩ : syracuseStep 3427337 = 2570503) B2570503
theorem B8563745 : Blo 1334986 8563745 := bstep (se 2 (by rfl) ⟨3211404, by rfl⟩ : syracuseStep 8563745 = 6422809) B6422809
theorem B1502383 : Blo 1334986 1502383 := bstep (se 1 (by rfl) ⟨1126787, by rfl⟩ : syracuseStep 1502383 = 2253575) B2253575
theorem B2534665 : Blo 1334986 2534665 := bstep (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) B1900999
theorem B2141495 : Blo 1334986 2141495 := bstep (se 1 (by rfl) ⟨1606121, by rfl⟩ : syracuseStep 2141495 = 3212243) B3212243
theorem B5705099 : Blo 1334986 5705099 := bstep (se 1 (by rfl) ⟨4278824, by rfl⟩ : syracuseStep 5705099 = 8557649) B8557649
theorem B3804641 : Blo 1334986 3804641 := bstep (se 2 (by rfl) ⟨1426740, by rfl⟩ : syracuseStep 3804641 = 2853481) B2853481
theorem B2854369 : Blo 1334986 2854369 := bstep (se 2 (by rfl) ⟨1070388, by rfl⟩ : syracuseStep 2854369 = 2140777) B2140777
theorem B7605839 : Blo 1334986 7605839 := bstep (se 1 (by rfl) ⟨5704379, by rfl⟩ : syracuseStep 7605839 = 11408759) B11408759
theorem B2002535 : Blo 1334986 2002535 := bstep (se 1 (by rfl) ⟨1501901, by rfl⟩ : syracuseStep 2002535 = 3003803) B3003803
theorem B10833533 : Blo 1334986 10833533 := bstep (se 3 (by rfl) ⟨2031287, by rfl⟩ : syracuseStep 10833533 = 4062575) B4062575
theorem B1503103 : Blo 1334986 1503103 := bstep (se 1 (by rfl) ⟨1127327, by rfl⟩ : syracuseStep 1503103 = 2254655) B2254655
theorem B7221163 : Blo 1334986 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B2002919 : Blo 1334986 2002919 := bstep (se 1 (by rfl) ⟨1502189, by rfl⟩ : syracuseStep 2002919 = 3004379) B3004379
theorem B2003039 : Blo 1334986 2003039 := bstep (se 1 (by rfl) ⟨1502279, by rfl⟩ : syracuseStep 2003039 = 3004559) B3004559
theorem B2003051 : Blo 1334986 2003051 := bstep (se 1 (by rfl) ⟨1502288, by rfl⟩ : syracuseStep 2003051 = 3004577) B3004577
theorem B1929343 : Blo 1334986 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B2003099 : Blo 1334986 2003099 := bstep (se 1 (by rfl) ⟨1502324, by rfl⟩ : syracuseStep 2003099 = 3004649) B3004649
theorem B5075207 : Blo 1334986 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B25661711 : Blo 1334986 25661711 := bstep (se 1 (by rfl) ⟨19246283, by rfl⟩ : syracuseStep 25661711 = 38492567) B38492567
theorem B3805471 : Blo 1334986 3805471 := bstep (se 1 (by rfl) ⟨2854103, by rfl⟩ : syracuseStep 3805471 = 5708207) B5708207
theorem B19534121 : Blo 1334986 19534121 := bstep (se 2 (by rfl) ⟨7325295, by rfl⟩ : syracuseStep 19534121 = 14650591) B14650591
theorem B1503643 : Blo 1334986 1503643 := bstep (se 1 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 1503643 = 2255465) B2255465
theorem B4338103 : Blo 1334986 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B2535887 : Blo 1334986 2535887 := bstep (se 1 (by rfl) ⟨1901915, by rfl⟩ : syracuseStep 2535887 = 3803831) B3803831
theorem B7418471 : Blo 1334986 7418471 := bstep (se 1 (by rfl) ⟨5563853, by rfl⟩ : syracuseStep 7418471 = 11127707) B11127707
theorem B4510619 : Blo 1334986 4510619 := bstep (se 1 (by rfl) ⟨3382964, by rfl⟩ : syracuseStep 4510619 = 6765929) B6765929
theorem B2003951 : Blo 1334986 2003951 := bstep (se 1 (by rfl) ⟨1502963, by rfl⟩ : syracuseStep 2003951 = 3005927) B3005927
theorem B5215421 : Blo 1334986 5215421 := bstep (se 3 (by rfl) ⟨977891, by rfl⟩ : syracuseStep 5215421 = 1955783) B1955783
theorem B5076179 : Blo 1334986 5076179 := bstep (se 1 (by rfl) ⟨3807134, by rfl⟩ : syracuseStep 5076179 = 7614269) B7614269
theorem B10138931 : Blo 1334986 10138931 := bstep (se 1 (by rfl) ⟨7604198, by rfl⟩ : syracuseStep 10138931 = 15208397) B15208397
theorem B2004335 : Blo 1334986 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B2004455 : Blo 1334986 2004455 := bstep (se 1 (by rfl) ⟨1503341, by rfl⟩ : syracuseStep 2004455 = 3006683) B3006683
theorem B3003983 : Blo 1334986 3003983 := bstep (se 1 (by rfl) ⟨2252987, by rfl⟩ : syracuseStep 3003983 = 4505975) B4505975
theorem B6764147 : Blo 1334986 6764147 := bstep (se 1 (by rfl) ⟨5073110, by rfl⟩ : syracuseStep 6764147 = 10146221) B10146221
theorem B2004617 : Blo 1334986 2004617 := bstep (se 2 (by rfl) ⟨751731, by rfl⟩ : syracuseStep 2004617 = 1503463) B1503463
theorem B2004635 : Blo 1334986 2004635 := bstep (se 1 (by rfl) ⟨1503476, by rfl⟩ : syracuseStep 2004635 = 3006953) B3006953
theorem B2930401 : Blo 1334986 2930401 := bstep (se 2 (by rfl) ⟨1098900, by rfl⟩ : syracuseStep 2930401 = 2197801) B2197801
theorem B5781239 : Blo 1334986 5781239 := bstep (se 1 (by rfl) ⟨4335929, by rfl⟩ : syracuseStep 5781239 = 8671859) B8671859
theorem B6420235 : Blo 1334986 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B12179267 : Blo 1334986 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B2004827 : Blo 1334986 2004827 := bstep (se 1 (by rfl) ⟨1503620, by rfl⟩ : syracuseStep 2004827 = 3007241) B3007241
theorem B2537543 : Blo 1334986 2537543 := bstep (se 1 (by rfl) ⟨1903157, by rfl⟩ : syracuseStep 2537543 = 3806315) B3806315
theorem B3381385 : Blo 1334986 3381385 := bstep (se 2 (by rfl) ⟨1268019, by rfl⟩ : syracuseStep 3381385 = 2536039) B2536039
theorem B2005211 : Blo 1334986 2005211 := bstep (se 1 (by rfl) ⟨1503908, by rfl⟩ : syracuseStep 2005211 = 3007817) B3007817
theorem B3004703 : Blo 1334986 3004703 := bstep (se 1 (by rfl) ⟨2253527, by rfl⟩ : syracuseStep 3004703 = 4507055) B4507055
theorem B6764957 : Blo 1334986 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B3004955 : Blo 1334986 3004955 := bstep (se 1 (by rfl) ⟨2253716, by rfl⟩ : syracuseStep 3004955 = 4507433) B4507433
theorem B3045919 : Blo 1334986 3045919 := bstep (se 1 (by rfl) ⟨2284439, by rfl⟩ : syracuseStep 3045919 = 4568879) B4568879
theorem B11418191 : Blo 1334986 11418191 := bstep (se 1 (by rfl) ⟨8563643, by rfl⟩ : syracuseStep 11418191 = 17127287) B17127287
theorem B16251509 : Blo 1334986 16251509 := bstep (se 5 (by rfl) ⟨761789, by rfl⟩ : syracuseStep 16251509 = 1523579) B1523579
theorem B10279547 : Blo 1334986 10279547 := bstep (se 1 (by rfl) ⟨7709660, by rfl⟩ : syracuseStep 10279547 = 15419321) B15419321
theorem B26049235 : Blo 1334986 26049235 := bstep (se 1 (by rfl) ⟨19536926, by rfl⟩ : syracuseStep 26049235 = 39073853) B39073853
theorem B20560877 : Blo 1334986 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B6765767 : Blo 1334986 6765767 := bstep (se 1 (by rfl) ⟨5074325, by rfl⟩ : syracuseStep 6765767 = 10148651) B10148651
theorem B13704623 : Blo 1334986 13704623 := bstep (se 1 (by rfl) ⟨10278467, by rfl⟩ : syracuseStep 13704623 = 20556935) B20556935
theorem B1335015 : Blo 1334986 1335015 := bstep (se 1 (by rfl) ⟨1001261, by rfl⟩ : syracuseStep 1335015 = 2002523) B2002523
theorem B2891539 : Blo 1334986 2891539 := bstep (se 1 (by rfl) ⟨2168654, by rfl⟩ : syracuseStep 2891539 = 4337309) B4337309
theorem B1335071 : Blo 1334986 1335071 := bstep (se 1 (by rfl) ⟨1001303, by rfl⟩ : syracuseStep 1335071 = 2002607) B2002607
theorem B28868399 : Blo 1334986 28868399 := bstep (se 1 (by rfl) ⟨21651299, by rfl⟩ : syracuseStep 28868399 = 43302599) B43302599
theorem B3006305 : Blo 1334986 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B1335151 : Blo 1334986 1335151 := bstep (se 1 (by rfl) ⟨1001363, by rfl⟩ : syracuseStep 1335151 = 2002727) B2002727
theorem B1335207 : Blo 1334986 1335207 := bstep (se 1 (by rfl) ⟨1001405, by rfl⟩ : syracuseStep 1335207 = 2002811) B2002811
theorem B3006431 : Blo 1334986 3006431 := bstep (se 1 (by rfl) ⟨2254823, by rfl⟩ : syracuseStep 3006431 = 4509647) B4509647
theorem B1335359 : Blo 1334986 1335359 := bstep (se 1 (by rfl) ⟨1001519, by rfl⟩ : syracuseStep 1335359 = 2003039) B2003039
theorem B1335367 : Blo 1334986 1335367 := bstep (se 1 (by rfl) ⟨1001525, by rfl⟩ : syracuseStep 1335367 = 2003051) B2003051
theorem B61669475 : Blo 1334986 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B1335399 : Blo 1334986 1335399 := bstep (se 1 (by rfl) ⟨1001549, by rfl⟩ : syracuseStep 1335399 = 2003099) B2003099
theorem B2572457 : Blo 1334986 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B3383471 : Blo 1334986 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B5784137 : Blo 1334986 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B3007079 : Blo 1334986 3007079 := bstep (se 1 (by rfl) ⟨2255309, by rfl⟩ : syracuseStep 3007079 = 4510619) B4510619
theorem B1335967 : Blo 1334986 1335967 := bstep (se 1 (by rfl) ⟨1001975, by rfl⟩ : syracuseStep 1335967 = 2003951) B2003951
theorem B4817569 : Blo 1334986 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B3384119 : Blo 1334986 3384119 := bstep (se 1 (by rfl) ⟨2538089, by rfl⟩ : syracuseStep 3384119 = 5076179) B5076179
theorem B6759287 : Blo 1334986 6759287 := bstep (se 1 (by rfl) ⟨5069465, by rfl⟩ : syracuseStep 6759287 = 10138931) B10138931
theorem B1336223 : Blo 1334986 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B34235297 : Blo 1334986 34235297 := bstep (se 2 (by rfl) ⟨12838236, by rfl⟩ : syracuseStep 34235297 = 25676473) B25676473
theorem B1336303 : Blo 1334986 1336303 := bstep (se 1 (by rfl) ⟨1002227, by rfl⟩ : syracuseStep 1336303 = 2004455) B2004455
theorem B1336411 : Blo 1334986 1336411 := bstep (se 1 (by rfl) ⟨1002308, by rfl⟩ : syracuseStep 1336411 = 2004617) B2004617
theorem B1336423 : Blo 1334986 1336423 := bstep (se 1 (by rfl) ⟨1002317, by rfl⟩ : syracuseStep 1336423 = 2004635) B2004635
theorem B8119511 : Blo 1334986 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B1336551 : Blo 1334986 1336551 := bstep (se 1 (by rfl) ⟨1002413, by rfl⟩ : syracuseStep 1336551 = 2004827) B2004827
theorem B1901819 : Blo 1334986 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B4064521 : Blo 1334986 4064521 := bstep (se 2 (by rfl) ⟨1524195, by rfl⟩ : syracuseStep 4064521 = 3048391) B3048391
theorem B3802555 : Blo 1334986 3802555 := bstep (se 1 (by rfl) ⟨2851916, by rfl⟩ : syracuseStep 3802555 = 5703833) B5703833
theorem B1336807 : Blo 1334986 1336807 := bstep (se 1 (by rfl) ⟨1002605, by rfl⟩ : syracuseStep 1336807 = 2005211) B2005211
theorem B3802601 : Blo 1334986 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B7612127 : Blo 1334986 7612127 := bstep (se 1 (by rfl) ⟨5709095, by rfl⟩ : syracuseStep 7612127 = 11418191) B11418191
theorem B13707251 : Blo 1334986 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B1427663 : Blo 1334986 1427663 := bstep (se 1 (by rfl) ⟨1070747, by rfl⟩ : syracuseStep 1427663 = 2141495) B2141495
theorem B3803399 : Blo 1334986 3803399 := bstep (se 1 (by rfl) ⟨2852549, by rfl⟩ : syracuseStep 3803399 = 5705099) B5705099
theorem B9136415 : Blo 1334986 9136415 := bstep (se 1 (by rfl) ⟨6852311, by rfl⟩ : syracuseStep 9136415 = 13704623) B13704623
theorem B19245599 : Blo 1334986 19245599 := bstep (se 1 (by rfl) ⟨14434199, by rfl⟩ : syracuseStep 19245599 = 28868399) B28868399
theorem B9628217 : Blo 1334986 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B17107807 : Blo 1334986 17107807 := bstep (se 1 (by rfl) ⟨12830855, by rfl⟩ : syracuseStep 17107807 = 25661711) B25661711
theorem B4508513 : Blo 1334986 4508513 := bstep (se 2 (by rfl) ⟨1690692, by rfl⟩ : syracuseStep 4508513 = 3381385) B3381385
theorem B2141039 : Blo 1334986 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B5073961 : Blo 1334986 5073961 := bstep (se 2 (by rfl) ⟨1902735, by rfl⟩ : syracuseStep 5073961 = 3805471) B3805471
theorem B12840083 : Blo 1334986 12840083 := bstep (se 1 (by rfl) ⟨9630062, by rfl⟩ : syracuseStep 12840083 = 19260125) B19260125
theorem B14454089 : Blo 1334986 14454089 := bstep (se 2 (by rfl) ⟨5420283, by rfl⟩ : syracuseStep 14454089 = 10840567) B10840567
theorem B36547949 : Blo 1334986 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B3476947 : Blo 1334986 3476947 := bstep (se 1 (by rfl) ⟨2607710, by rfl⟩ : syracuseStep 3476947 = 5215421) B5215421
theorem B2002655 : Blo 1334986 2002655 := bstep (se 1 (by rfl) ⟨1501991, by rfl⟩ : syracuseStep 2002655 = 3003983) B3003983
theorem B4509431 : Blo 1334986 4509431 := bstep (se 1 (by rfl) ⟨3382073, by rfl⟩ : syracuseStep 4509431 = 6764147) B6764147
theorem B3854159 : Blo 1334986 3854159 := bstep (se 1 (by rfl) ⟨2890619, by rfl⟩ : syracuseStep 3854159 = 5781239) B5781239
theorem B6762365 : Blo 1334986 6762365 := bstep (se 3 (by rfl) ⟨1267943, by rfl⟩ : syracuseStep 6762365 = 2535887) B2535887
theorem B48738185 : Blo 1334986 48738185 := bstep (se 2 (by rfl) ⟨18276819, by rfl⟩ : syracuseStep 48738185 = 36553639) B36553639
theorem B32509937 : Blo 1334986 32509937 := bstep (se 2 (by rfl) ⟨12191226, by rfl⟩ : syracuseStep 32509937 = 24382453) B24382453
theorem B2002937 : Blo 1334986 2002937 := bstep (se 2 (by rfl) ⟨751101, by rfl⟩ : syracuseStep 2002937 = 1502203) B1502203
theorem B1691695 : Blo 1334986 1691695 := bstep (se 1 (by rfl) ⟨1268771, by rfl⟩ : syracuseStep 1691695 = 2537543) B2537543
theorem B2003135 : Blo 1334986 2003135 := bstep (se 1 (by rfl) ⟨1502351, by rfl⟩ : syracuseStep 2003135 = 3004703) B3004703
theorem B2003177 : Blo 1334986 2003177 := bstep (se 2 (by rfl) ⟨751191, by rfl⟩ : syracuseStep 2003177 = 1502383) B1502383
theorem B4509971 : Blo 1334986 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B3379553 : Blo 1334986 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B2003303 : Blo 1334986 2003303 := bstep (se 1 (by rfl) ⟨1502477, by rfl⟩ : syracuseStep 2003303 = 3004955) B3004955
theorem B10834339 : Blo 1334986 10834339 := bstep (se 1 (by rfl) ⟨8125754, by rfl⟩ : syracuseStep 10834339 = 16251509) B16251509
theorem B6853031 : Blo 1334986 6853031 := bstep (se 1 (by rfl) ⟨5139773, by rfl⟩ : syracuseStep 6853031 = 10279547) B10279547
theorem B3805825 : Blo 1334986 3805825 := bstep (se 2 (by rfl) ⟨1427184, by rfl⟩ : syracuseStep 3805825 = 2854369) B2854369
theorem B6763175 : Blo 1334986 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B4510511 : Blo 1334986 4510511 := bstep (se 1 (by rfl) ⟨3382883, by rfl⟩ : syracuseStep 4510511 = 6765767) B6765767
theorem B2536427 : Blo 1334986 2536427 := bstep (se 1 (by rfl) ⟨1902320, by rfl⟩ : syracuseStep 2536427 = 3804641) B3804641
theorem B3855385 : Blo 1334986 3855385 := bstep (se 2 (by rfl) ⟨1445769, by rfl⟩ : syracuseStep 3855385 = 2891539) B2891539
theorem B7222355 : Blo 1334986 7222355 := bstep (se 1 (by rfl) ⟨5416766, by rfl⟩ : syracuseStep 7222355 = 10833533) B10833533
theorem B2536609 : Blo 1334986 2536609 := bstep (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) B1902457
theorem B2004137 : Blo 1334986 2004137 := bstep (se 2 (by rfl) ⟨751551, by rfl⟩ : syracuseStep 2004137 = 1503103) B1503103
theorem B2004203 : Blo 1334986 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B2004287 : Blo 1334986 2004287 := bstep (se 1 (by rfl) ⟨1503215, by rfl⟩ : syracuseStep 2004287 = 3006431) B3006431
theorem B22836653 : Blo 1334986 22836653 := bstep (se 3 (by rfl) ⟨4281872, by rfl⟩ : syracuseStep 22836653 = 8563745) B8563745
theorem B2004479 : Blo 1334986 2004479 := bstep (se 1 (by rfl) ⟨1503359, by rfl⟩ : syracuseStep 2004479 = 3006719) B3006719
theorem B13022747 : Blo 1334986 13022747 := bstep (se 1 (by rfl) ⟨9767060, by rfl⟩ : syracuseStep 13022747 = 19534121) B19534121
theorem B2004587 : Blo 1334986 2004587 := bstep (se 1 (by rfl) ⟨1503440, by rfl⟩ : syracuseStep 2004587 = 3006881) B3006881
theorem B3004073 : Blo 1334986 3004073 := bstep (se 2 (by rfl) ⟨1126527, by rfl⟩ : syracuseStep 3004073 = 2253055) B2253055
theorem B3004199 : Blo 1334986 3004199 := bstep (se 1 (by rfl) ⟨2253149, by rfl⟩ : syracuseStep 3004199 = 4506299) B4506299
theorem B2004857 : Blo 1334986 2004857 := bstep (se 2 (by rfl) ⟨751821, by rfl⟩ : syracuseStep 2004857 = 1503643) B1503643
theorem B4061225 : Blo 1334986 4061225 := bstep (se 2 (by rfl) ⟨1522959, by rfl⟩ : syracuseStep 4061225 = 3045919) B3045919
theorem B2005103 : Blo 1334986 2005103 := bstep (se 1 (by rfl) ⟨1503827, by rfl⟩ : syracuseStep 2005103 = 3007655) B3007655
theorem B2005175 : Blo 1334986 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B34732313 : Blo 1334986 34732313 := bstep (se 2 (by rfl) ⟨13024617, by rfl⟩ : syracuseStep 34732313 = 26049235) B26049235
theorem B5069087 : Blo 1334986 5069087 := bstep (se 1 (by rfl) ⟨3801815, by rfl⟩ : syracuseStep 5069087 = 7603631) B7603631
theorem B2710111 : Blo 1334986 2710111 := bstep (se 1 (by rfl) ⟨2032583, by rfl⟩ : syracuseStep 2710111 = 4065167) B4065167
theorem B7609211 : Blo 1334986 7609211 := bstep (se 1 (by rfl) ⟨5706908, by rfl⟩ : syracuseStep 7609211 = 11413817) B11413817
theorem B3005351 : Blo 1334986 3005351 := bstep (se 1 (by rfl) ⟨2254013, by rfl⟩ : syracuseStep 3005351 = 4508027) B4508027
theorem B19782589 : Blo 1334986 19782589 := bstep (se 3 (by rfl) ⟨3709235, by rfl⟩ : syracuseStep 19782589 = 7418471) B7418471
theorem B3005531 : Blo 1334986 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B2284891 : Blo 1334986 2284891 := bstep (se 1 (by rfl) ⟨1713668, by rfl⟩ : syracuseStep 2284891 = 3427337) B3427337
theorem B3907201 : Blo 1334986 3907201 := bstep (se 2 (by rfl) ⟨1465200, by rfl⟩ : syracuseStep 3907201 = 2930401) B2930401
theorem B8560313 : Blo 1334986 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B5070559 : Blo 1334986 5070559 := bstep (se 1 (by rfl) ⟨3802919, by rfl⟩ : syracuseStep 5070559 = 7605839) B7605839
theorem B43343585 : Blo 1334986 43343585 := bstep (se 2 (by rfl) ⟨16253844, by rfl⟩ : syracuseStep 43343585 = 32507689) B32507689
theorem B1335023 : Blo 1334986 1335023 := bstep (se 1 (by rfl) ⟨1001267, by rfl⟩ : syracuseStep 1335023 = 2002535) B2002535
theorem B3006377 : Blo 1334986 3006377 := bstep (se 2 (by rfl) ⟨1127391, by rfl⟩ : syracuseStep 3006377 = 2254783) B2254783
theorem B1335279 : Blo 1334986 1335279 := bstep (se 1 (by rfl) ⟨1001459, by rfl⟩ : syracuseStep 1335279 = 2002919) B2002919
theorem B10829933 : Blo 1334986 10829933 := bstep (se 3 (by rfl) ⟨2030612, by rfl⟩ : syracuseStep 10829933 = 4061225) B4061225
theorem B1335423 : Blo 1334986 1335423 := bstep (se 1 (by rfl) ⟨1001567, by rfl⟩ : syracuseStep 1335423 = 2003135) B2003135
theorem B1335451 : Blo 1334986 1335451 := bstep (se 1 (by rfl) ⟨1001588, by rfl⟩ : syracuseStep 1335451 = 2003177) B2003177
theorem B3006647 : Blo 1334986 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B2253035 : Blo 1334986 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B1335535 : Blo 1334986 1335535 := bstep (se 1 (by rfl) ⟨1001651, by rfl⟩ : syracuseStep 1335535 = 2003303) B2003303
theorem B3007007 : Blo 1334986 3007007 := bstep (se 1 (by rfl) ⟨2255255, by rfl⟩ : syracuseStep 3007007 = 4510511) B4510511
theorem B4506191 : Blo 1334986 4506191 := bstep (se 1 (by rfl) ⟨3379643, by rfl⟩ : syracuseStep 4506191 = 6759287) B6759287
theorem B22823531 : Blo 1334986 22823531 := bstep (se 1 (by rfl) ⟨17117648, by rfl⟩ : syracuseStep 22823531 = 34235297) B34235297
theorem B5071517 : Blo 1334986 5071517 := bstep (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) B1901819
theorem B24363773 : Blo 1334986 24363773 := bstep (se 3 (by rfl) ⟨4568207, by rfl⟩ : syracuseStep 24363773 = 9136415) B9136415
theorem B1336091 : Blo 1334986 1336091 := bstep (se 1 (by rfl) ⟨1002068, by rfl⟩ : syracuseStep 1336091 = 2004137) B2004137
theorem B3613481 : Blo 1334986 3613481 := bstep (se 2 (by rfl) ⟨1355055, by rfl⟩ : syracuseStep 3613481 = 2710111) B2710111
theorem B1336135 : Blo 1334986 1336135 := bstep (se 1 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 1336135 = 2004203) B2004203
theorem B1336191 : Blo 1334986 1336191 := bstep (se 1 (by rfl) ⟨1002143, by rfl⟩ : syracuseStep 1336191 = 2004287) B2004287
theorem B6423425 : Blo 1334986 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B1336319 : Blo 1334986 1336319 := bstep (se 1 (by rfl) ⟨1002239, by rfl⟩ : syracuseStep 1336319 = 2004479) B2004479
theorem B1336391 : Blo 1334986 1336391 := bstep (se 1 (by rfl) ⟨1002293, by rfl⟩ : syracuseStep 1336391 = 2004587) B2004587
theorem B1336571 : Blo 1334986 1336571 := bstep (se 1 (by rfl) ⟨1002428, by rfl⟩ : syracuseStep 1336571 = 2004857) B2004857
theorem B1336735 : Blo 1334986 1336735 := bstep (se 1 (by rfl) ⟨1002551, by rfl⟩ : syracuseStep 1336735 = 2005103) B2005103
theorem B1336783 : Blo 1334986 1336783 := bstep (se 1 (by rfl) ⟨1002587, by rfl⟩ : syracuseStep 1336783 = 2005175) B2005175
theorem B12830399 : Blo 1334986 12830399 := bstep (se 1 (by rfl) ⟨9622799, by rfl⟩ : syracuseStep 12830399 = 19245599) B19245599
theorem B5072807 : Blo 1334986 5072807 := bstep (se 1 (by rfl) ⟨3804605, by rfl⟩ : syracuseStep 5072807 = 7609211) B7609211
theorem B9636059 : Blo 1334986 9636059 := bstep (se 1 (by rfl) ⟨7227044, by rfl⟩ : syracuseStep 9636059 = 14454089) B14454089
theorem B24365299 : Blo 1334986 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B6760745 : Blo 1334986 6760745 := bstep (se 2 (by rfl) ⟨2535279, by rfl⟩ : syracuseStep 6760745 = 5070559) B5070559
theorem B28895723 : Blo 1334986 28895723 := bstep (se 1 (by rfl) ⟨21671792, by rfl⟩ : syracuseStep 28895723 = 43343585) B43343585
theorem B4508243 : Blo 1334986 4508243 := bstep (se 1 (by rfl) ⟨3381182, by rfl⟩ : syracuseStep 4508243 = 6762365) B6762365
theorem B32492123 : Blo 1334986 32492123 := bstep (se 1 (by rfl) ⟨24369092, by rfl⟩ : syracuseStep 32492123 = 48738185) B48738185
theorem B2255593 : Blo 1334986 2255593 := bstep (se 2 (by rfl) ⟨845847, by rfl⟩ : syracuseStep 2255593 = 1691695) B1691695
theorem B2255647 : Blo 1334986 2255647 := bstep (se 1 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 2255647 = 3383471) B3383471
theorem B6859885 : Blo 1334986 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B4508783 : Blo 1334986 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B2256079 : Blo 1334986 2256079 := bstep (se 1 (by rfl) ⟨1692059, by rfl⟩ : syracuseStep 2256079 = 3384119) B3384119
theorem B14445785 : Blo 1334986 14445785 := bstep (se 2 (by rfl) ⟨5417169, by rfl⟩ : syracuseStep 14445785 = 10834339) B10834339
theorem B1690951 : Blo 1334986 1690951 := bstep (se 1 (by rfl) ⟨1268213, by rfl⟩ : syracuseStep 1690951 = 2536427) B2536427
theorem B5074433 : Blo 1334986 5074433 := bstep (se 2 (by rfl) ⟨1902912, by rfl⟩ : syracuseStep 5074433 = 3805825) B3805825
theorem B15224435 : Blo 1334986 15224435 := bstep (se 1 (by rfl) ⟨11418326, by rfl⟩ : syracuseStep 15224435 = 22836653) B22836653
theorem B2535067 : Blo 1334986 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B2002715 : Blo 1334986 2002715 := bstep (se 1 (by rfl) ⟨1502036, by rfl⟩ : syracuseStep 2002715 = 3004073) B3004073
theorem B22810409 : Blo 1334986 22810409 := bstep (se 2 (by rfl) ⟨8553903, by rfl⟩ : syracuseStep 22810409 = 17107807) B17107807
theorem B5074751 : Blo 1334986 5074751 := bstep (se 1 (by rfl) ⟨3806063, by rfl⟩ : syracuseStep 5074751 = 7612127) B7612127
theorem B2002799 : Blo 1334986 2002799 := bstep (se 1 (by rfl) ⟨1502099, by rfl⟩ : syracuseStep 2002799 = 3004199) B3004199
theorem B9138167 : Blo 1334986 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B5140513 : Blo 1334986 5140513 := bstep (se 2 (by rfl) ⟨1927692, by rfl⟩ : syracuseStep 5140513 = 3855385) B3855385
theorem B2535599 : Blo 1334986 2535599 := bstep (se 1 (by rfl) ⟨1901699, by rfl⟩ : syracuseStep 2535599 = 3803399) B3803399
theorem B23154875 : Blo 1334986 23154875 := bstep (se 1 (by rfl) ⟨17366156, by rfl⟩ : syracuseStep 23154875 = 34732313) B34732313
theorem B3379391 : Blo 1334986 3379391 := bstep (se 1 (by rfl) ⟨2534543, by rfl⟩ : syracuseStep 3379391 = 5069087) B5069087
theorem B5419361 : Blo 1334986 5419361 := bstep (se 2 (by rfl) ⟨2032260, by rfl⟩ : syracuseStep 5419361 = 4064521) B4064521
theorem B6418811 : Blo 1334986 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B12186085 : Blo 1334986 12186085 := bstep (se 4 (by rfl) ⟨1142445, by rfl⟩ : syracuseStep 12186085 = 2284891) B2284891
theorem B2003567 : Blo 1334986 2003567 := bstep (se 1 (by rfl) ⟨1502675, by rfl⟩ : syracuseStep 2003567 = 3005351) B3005351
theorem B2003687 : Blo 1334986 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B5706875 : Blo 1334986 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B2569439 : Blo 1334986 2569439 := bstep (se 1 (by rfl) ⟨1927079, by rfl⟩ : syracuseStep 2569439 = 3854159) B3854159
theorem B2004251 : Blo 1334986 2004251 := bstep (se 1 (by rfl) ⟨1503188, by rfl⟩ : syracuseStep 2004251 = 3006377) B3006377
theorem B21673291 : Blo 1334986 21673291 := bstep (se 1 (by rfl) ⟨16254968, by rfl⟩ : syracuseStep 21673291 = 32509937) B32509937
theorem B41112983 : Blo 1334986 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B4568687 : Blo 1334986 4568687 := bstep (se 1 (by rfl) ⟨3426515, by rfl⟩ : syracuseStep 4568687 = 6853031) B6853031
theorem B3856091 : Blo 1334986 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B2004719 : Blo 1334986 2004719 := bstep (se 1 (by rfl) ⟨1503539, by rfl⟩ : syracuseStep 2004719 = 3007079) B3007079
theorem B3807101 : Blo 1334986 3807101 := bstep (se 3 (by rfl) ⟨713831, by rfl⟩ : syracuseStep 3807101 = 1427663) B1427663
theorem B4814903 : Blo 1334986 4814903 := bstep (se 1 (by rfl) ⟨3611177, by rfl⟩ : syracuseStep 4814903 = 7222355) B7222355
theorem B5413007 : Blo 1334986 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B8681831 : Blo 1334986 8681831 := bstep (se 1 (by rfl) ⟨6511373, by rfl⟩ : syracuseStep 8681831 = 13022747) B13022747
theorem B26376785 : Blo 1334986 26376785 := bstep (se 2 (by rfl) ⟨9891294, by rfl⟩ : syracuseStep 26376785 = 19782589) B19782589
theorem B6765281 : Blo 1334986 6765281 := bstep (se 2 (by rfl) ⟨2536980, by rfl⟩ : syracuseStep 6765281 = 5073961) B5073961
theorem B3382145 : Blo 1334986 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B3005675 : Blo 1334986 3005675 := bstep (se 1 (by rfl) ⟨2254256, by rfl⟩ : syracuseStep 3005675 = 4508513) B4508513
theorem B5070073 : Blo 1334986 5070073 := bstep (se 2 (by rfl) ⟨1901277, by rfl⟩ : syracuseStep 5070073 = 3802555) B3802555
theorem B4635929 : Blo 1334986 4635929 := bstep (se 2 (by rfl) ⟨1738473, by rfl⟩ : syracuseStep 4635929 = 3476947) B3476947
theorem B8560055 : Blo 1334986 8560055 := bstep (se 1 (by rfl) ⟨6420041, by rfl⟩ : syracuseStep 8560055 = 12840083) B12840083
theorem B5209601 : Blo 1334986 5209601 := bstep (se 2 (by rfl) ⟨1953600, by rfl⟩ : syracuseStep 5209601 = 3907201) B3907201
theorem B5709437 : Blo 1334986 5709437 := bstep (se 3 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 5709437 = 2141039) B2141039
theorem B1335103 : Blo 1334986 1335103 := bstep (se 1 (by rfl) ⟨1001327, by rfl⟩ : syracuseStep 1335103 = 2002655) B2002655
theorem B3006287 : Blo 1334986 3006287 := bstep (se 1 (by rfl) ⟨2254715, by rfl⟩ : syracuseStep 3006287 = 4509431) B4509431
theorem B1335291 : Blo 1334986 1335291 := bstep (se 1 (by rfl) ⟨1001468, by rfl⟩ : syracuseStep 1335291 = 2002937) B2002937
theorem B2252927 : Blo 1334986 2252927 := bstep (se 1 (by rfl) ⟨1689695, by rfl⟩ : syracuseStep 2252927 = 3379391) B3379391
theorem B3612907 : Blo 1334986 3612907 := bstep (se 1 (by rfl) ⟨2709680, by rfl⟩ : syracuseStep 3612907 = 5419361) B5419361
theorem B1335711 : Blo 1334986 1335711 := bstep (se 1 (by rfl) ⟨1001783, by rfl⟩ : syracuseStep 1335711 = 2003567) B2003567
theorem B1335791 : Blo 1334986 1335791 := bstep (se 1 (by rfl) ⟨1001843, by rfl⟩ : syracuseStep 1335791 = 2003687) B2003687
theorem B2408987 : Blo 1334986 2408987 := bstep (se 1 (by rfl) ⟨1806740, by rfl⟩ : syracuseStep 2408987 = 3613481) B3613481
theorem B1336167 : Blo 1334986 1336167 := bstep (se 1 (by rfl) ⟨1002125, by rfl⟩ : syracuseStep 1336167 = 2004251) B2004251
theorem B3007457 : Blo 1334986 3007457 := bstep (se 2 (by rfl) ⟨1127796, by rfl⟩ : syracuseStep 3007457 = 2255593) B2255593
theorem B3007529 : Blo 1334986 3007529 := bstep (se 2 (by rfl) ⟨1127823, by rfl⟩ : syracuseStep 3007529 = 2255647) B2255647
theorem B8553599 : Blo 1334986 8553599 := bstep (se 1 (by rfl) ⟨6415199, by rfl⟩ : syracuseStep 8553599 = 12830399) B12830399
theorem B1336479 : Blo 1334986 1336479 := bstep (se 1 (by rfl) ⟨1002359, by rfl⟩ : syracuseStep 1336479 = 2004719) B2004719
theorem B6424039 : Blo 1334986 6424039 := bstep (se 1 (by rfl) ⟨4818029, by rfl⟩ : syracuseStep 6424039 = 9636059) B9636059
theorem B4507163 : Blo 1334986 4507163 := bstep (se 1 (by rfl) ⟨3380372, by rfl⟩ : syracuseStep 4507163 = 6760745) B6760745
theorem B3008105 : Blo 1334986 3008105 := bstep (se 2 (by rfl) ⟨1128039, by rfl⟩ : syracuseStep 3008105 = 2256079) B2256079
theorem B6760097 : Blo 1334986 6760097 := bstep (se 2 (by rfl) ⟨2535036, by rfl⟩ : syracuseStep 6760097 = 5070073) B5070073
theorem B21661415 : Blo 1334986 21661415 := bstep (se 1 (by rfl) ⟨16246061, by rfl⟩ : syracuseStep 21661415 = 32492123) B32492123
theorem B2254601 : Blo 1334986 2254601 := bstep (se 2 (by rfl) ⟨845475, by rfl⟩ : syracuseStep 2254601 = 1690951) B1690951
theorem B10282909 : Blo 1334986 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B2254763 : Blo 1334986 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B3090619 : Blo 1334986 3090619 := bstep (se 1 (by rfl) ⟨2317964, by rfl⟩ : syracuseStep 3090619 = 4635929) B4635929
theorem B15206939 : Blo 1334986 15206939 := bstep (se 1 (by rfl) ⟨11405204, by rfl⟩ : syracuseStep 15206939 = 22810409) B22810409
theorem B7219955 : Blo 1334986 7219955 := bstep (se 1 (by rfl) ⟨5414966, by rfl⟩ : syracuseStep 7219955 = 10829933) B10829933
theorem B1690399 : Blo 1334986 1690399 := bstep (se 1 (by rfl) ⟨1267799, by rfl⟩ : syracuseStep 1690399 = 2535599) B2535599
theorem B15436583 : Blo 1334986 15436583 := bstep (se 1 (by rfl) ⟨11577437, by rfl⟩ : syracuseStep 15436583 = 23154875) B23154875
theorem B12839741 : Blo 1334986 12839741 := bstep (se 3 (by rfl) ⟨2407451, by rfl⟩ : syracuseStep 12839741 = 4814903) B4814903
theorem B1502023 : Blo 1334986 1502023 := bstep (se 1 (by rfl) ⟨1126517, by rfl⟩ : syracuseStep 1502023 = 2253035) B2253035
theorem B15215687 : Blo 1334986 15215687 := bstep (se 1 (by rfl) ⟨11411765, by rfl⟩ : syracuseStep 15215687 = 22823531) B22823531
theorem B6851837 : Blo 1334986 6851837 := bstep (se 3 (by rfl) ⟨1284719, by rfl⟩ : syracuseStep 6851837 = 2569439) B2569439
theorem B16248113 : Blo 1334986 16248113 := bstep (se 2 (by rfl) ⟨6093042, by rfl⟩ : syracuseStep 16248113 = 12186085) B12186085
theorem B3804583 : Blo 1334986 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B17116829 : Blo 1334986 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B3608671 : Blo 1334986 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B9146513 : Blo 1334986 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B5787887 : Blo 1334986 5787887 := bstep (se 1 (by rfl) ⟨4340915, by rfl⟩ : syracuseStep 5787887 = 8681831) B8681831
theorem B19263815 : Blo 1334986 19263815 := bstep (se 1 (by rfl) ⟨14447861, by rfl⟩ : syracuseStep 19263815 = 28895723) B28895723
theorem B17584523 : Blo 1334986 17584523 := bstep (se 1 (by rfl) ⟨13188392, by rfl⟩ : syracuseStep 17584523 = 26376785) B26376785
theorem B28897721 : Blo 1334986 28897721 := bstep (se 2 (by rfl) ⟨10836645, by rfl⟩ : syracuseStep 28897721 = 21673291) B21673291
theorem B4510187 : Blo 1334986 4510187 := bstep (se 1 (by rfl) ⟨3382640, by rfl⟩ : syracuseStep 4510187 = 6765281) B6765281
theorem B9630523 : Blo 1334986 9630523 := bstep (se 1 (by rfl) ⟨7222892, by rfl⟩ : syracuseStep 9630523 = 14445785) B14445785
theorem B2003783 : Blo 1334986 2003783 := bstep (se 1 (by rfl) ⟨1502837, by rfl⟩ : syracuseStep 2003783 = 3005675) B3005675
theorem B3380089 : Blo 1334986 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B5706703 : Blo 1334986 5706703 := bstep (se 1 (by rfl) ⟨4280027, by rfl⟩ : syracuseStep 5706703 = 8560055) B8560055
theorem B3806291 : Blo 1334986 3806291 := bstep (se 1 (by rfl) ⟨2854718, by rfl⟩ : syracuseStep 3806291 = 5709437) B5709437
theorem B2004191 : Blo 1334986 2004191 := bstep (se 1 (by rfl) ⟨1503143, by rfl⟩ : syracuseStep 2004191 = 3006287) B3006287
theorem B6092111 : Blo 1334986 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B6854017 : Blo 1334986 6854017 := bstep (se 2 (by rfl) ⟨2570256, by rfl⟩ : syracuseStep 6854017 = 5140513) B5140513
theorem B2004431 : Blo 1334986 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B32487065 : Blo 1334986 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B2004671 : Blo 1334986 2004671 := bstep (se 1 (by rfl) ⟨1503503, by rfl⟩ : syracuseStep 2004671 = 3007007) B3007007
theorem B3004127 : Blo 1334986 3004127 := bstep (se 1 (by rfl) ⟨2253095, by rfl⟩ : syracuseStep 3004127 = 4506191) B4506191
theorem B3381011 : Blo 1334986 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B16242515 : Blo 1334986 16242515 := bstep (se 1 (by rfl) ⟨12181886, by rfl⟩ : syracuseStep 16242515 = 24363773) B24363773
theorem B4282283 : Blo 1334986 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B27408655 : Blo 1334986 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B3045791 : Blo 1334986 3045791 := bstep (se 1 (by rfl) ⟨2284343, by rfl⟩ : syracuseStep 3045791 = 4568687) B4568687
theorem B2538067 : Blo 1334986 2538067 := bstep (se 1 (by rfl) ⟨1903550, by rfl⟩ : syracuseStep 2538067 = 3807101) B3807101
theorem B3381871 : Blo 1334986 3381871 := bstep (se 1 (by rfl) ⟨2536403, by rfl⟩ : syracuseStep 3381871 = 5072807) B5072807
theorem B13892269 : Blo 1334986 13892269 := bstep (se 3 (by rfl) ⟨2604800, by rfl⟩ : syracuseStep 13892269 = 5209601) B5209601
theorem B3005495 : Blo 1334986 3005495 := bstep (se 1 (by rfl) ⟨2254121, by rfl⟩ : syracuseStep 3005495 = 4508243) B4508243
theorem B3005855 : Blo 1334986 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B3382955 : Blo 1334986 3382955 := bstep (se 1 (by rfl) ⟨2537216, by rfl⟩ : syracuseStep 3382955 = 5074433) B5074433
theorem B10149623 : Blo 1334986 10149623 := bstep (se 1 (by rfl) ⟨7612217, by rfl⟩ : syracuseStep 10149623 = 15224435) B15224435
theorem B1335143 : Blo 1334986 1335143 := bstep (se 1 (by rfl) ⟨1001357, by rfl⟩ : syracuseStep 1335143 = 2002715) B2002715
theorem B3383167 : Blo 1334986 3383167 := bstep (se 1 (by rfl) ⟨2537375, by rfl⟩ : syracuseStep 3383167 = 5074751) B5074751
theorem B1335199 : Blo 1334986 1335199 := bstep (se 1 (by rfl) ⟨1001399, by rfl⟩ : syracuseStep 1335199 = 2002799) B2002799
theorem B10150109 : Blo 1334986 10150109 := bstep (se 3 (by rfl) ⟨1903145, by rfl⟩ : syracuseStep 10150109 = 3806291) B3806291
theorem B11723015 : Blo 1334986 11723015 := bstep (se 1 (by rfl) ⟨8792261, by rfl⟩ : syracuseStep 11723015 = 17584523) B17584523
theorem B3006791 : Blo 1334986 3006791 := bstep (se 1 (by rfl) ⟨2255093, by rfl⟩ : syracuseStep 3006791 = 4510187) B4510187
theorem B36544873 : Blo 1334986 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B1605991 : Blo 1334986 1605991 := bstep (se 1 (by rfl) ⟨1204493, by rfl⟩ : syracuseStep 1605991 = 2408987) B2408987
theorem B1335855 : Blo 1334986 1335855 := bstep (se 1 (by rfl) ⟨1001891, by rfl⟩ : syracuseStep 1335855 = 2003783) B2003783
theorem B5702399 : Blo 1334986 5702399 := bstep (se 1 (by rfl) ⟨4276799, by rfl⟩ : syracuseStep 5702399 = 8553599) B8553599
theorem B3384089 : Blo 1334986 3384089 := bstep (se 2 (by rfl) ⟨1269033, by rfl⟩ : syracuseStep 3384089 = 2538067) B2538067
theorem B1336127 : Blo 1334986 1336127 := bstep (se 1 (by rfl) ⟨1002095, by rfl⟩ : syracuseStep 1336127 = 2004191) B2004191
theorem B16245629 : Blo 1334986 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B18523025 : Blo 1334986 18523025 := bstep (se 2 (by rfl) ⟨6946134, by rfl⟩ : syracuseStep 18523025 = 13892269) B13892269
theorem B1336287 : Blo 1334986 1336287 := bstep (se 1 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 1336287 = 2004431) B2004431
theorem B16483301 : Blo 1334986 16483301 := bstep (se 4 (by rfl) ⟨1545309, by rfl⟩ : syracuseStep 16483301 = 3090619) B3090619
theorem B2253865 : Blo 1334986 2253865 := bstep (se 2 (by rfl) ⟨845199, by rfl⟩ : syracuseStep 2253865 = 1690399) B1690399
theorem B4506731 : Blo 1334986 4506731 := bstep (se 1 (by rfl) ⟨3380048, by rfl⟩ : syracuseStep 4506731 = 6760097) B6760097
theorem B1336447 : Blo 1334986 1336447 := bstep (se 1 (by rfl) ⟨1002335, by rfl⟩ : syracuseStep 1336447 = 2004671) B2004671
theorem B4506785 : Blo 1334986 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B2254007 : Blo 1334986 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B19268837 : Blo 1334986 19268837 := bstep (se 4 (by rfl) ⟨1806453, by rfl⟩ : syracuseStep 19268837 = 3612907) B3612907
theorem B10291055 : Blo 1334986 10291055 := bstep (se 1 (by rfl) ⟨7718291, by rfl⟩ : syracuseStep 10291055 = 15436583) B15436583
theorem B5072777 : Blo 1334986 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B10143791 : Blo 1334986 10143791 := bstep (se 1 (by rfl) ⟨7607843, by rfl⟩ : syracuseStep 10143791 = 15215687) B15215687
theorem B10832075 : Blo 1334986 10832075 := bstep (se 1 (by rfl) ⟨8124056, by rfl⟩ : syracuseStep 10832075 = 16248113) B16248113
theorem B2255303 : Blo 1334986 2255303 := bstep (se 1 (by rfl) ⟨1691477, by rfl⟩ : syracuseStep 2255303 = 3382955) B3382955
theorem B61737461 : Blo 1334986 61737461 := bstep (se 5 (by rfl) ⟨2893943, by rfl⟩ : syracuseStep 61737461 = 5787887) B5787887
theorem B34261541 : Blo 1334986 34261541 := bstep (se 4 (by rfl) ⟨3212019, by rfl⟩ : syracuseStep 34261541 = 6424039) B6424039
theorem B1501951 : Blo 1334986 1501951 := bstep (se 1 (by rfl) ⟨1126463, by rfl⟩ : syracuseStep 1501951 = 2252927) B2252927
theorem B6097675 : Blo 1334986 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B4811561 : Blo 1334986 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B18271565 : Blo 1334986 18271565 := bstep (se 3 (by rfl) ⟨3425918, by rfl⟩ : syracuseStep 18271565 = 6851837) B6851837
theorem B4509161 : Blo 1334986 4509161 := bstep (se 2 (by rfl) ⟨1690935, by rfl⟩ : syracuseStep 4509161 = 3381871) B3381871
theorem B12840697 : Blo 1334986 12840697 := bstep (se 2 (by rfl) ⟨4815261, by rfl⟩ : syracuseStep 12840697 = 9630523) B9630523
theorem B2002697 : Blo 1334986 2002697 := bstep (se 2 (by rfl) ⟨751011, by rfl⟩ : syracuseStep 2002697 = 1502023) B1502023
theorem B2002751 : Blo 1334986 2002751 := bstep (se 1 (by rfl) ⟨1502063, by rfl⟩ : syracuseStep 2002751 = 3004127) B3004127
theorem B1503067 : Blo 1334986 1503067 := bstep (se 1 (by rfl) ⟨1127300, by rfl⟩ : syracuseStep 1503067 = 2254601) B2254601
theorem B1503175 : Blo 1334986 1503175 := bstep (se 1 (by rfl) ⟨1127381, by rfl⟩ : syracuseStep 1503175 = 2254763) B2254763
theorem B2854855 : Blo 1334986 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B10137959 : Blo 1334986 10137959 := bstep (se 1 (by rfl) ⟨7603469, by rfl⟩ : syracuseStep 10137959 = 15206939) B15206939
theorem B4813303 : Blo 1334986 4813303 := bstep (se 1 (by rfl) ⟨3609977, by rfl⟩ : syracuseStep 4813303 = 7219955) B7219955
theorem B9138689 : Blo 1334986 9138689 := bstep (se 2 (by rfl) ⟨3427008, by rfl⟩ : syracuseStep 9138689 = 6854017) B6854017
theorem B2003663 : Blo 1334986 2003663 := bstep (se 1 (by rfl) ⟨1502747, by rfl⟩ : syracuseStep 2003663 = 3005495) B3005495
theorem B2003903 : Blo 1334986 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B4510889 : Blo 1334986 4510889 := bstep (se 2 (by rfl) ⟨1691583, by rfl⟩ : syracuseStep 4510889 = 3383167) B3383167
theorem B13710545 : Blo 1334986 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B12842543 : Blo 1334986 12842543 := bstep (se 1 (by rfl) ⟨9631907, by rfl⟩ : syracuseStep 12842543 = 19263815) B19263815
theorem B19265147 : Blo 1334986 19265147 := bstep (se 1 (by rfl) ⟨14448860, by rfl⟩ : syracuseStep 19265147 = 28897721) B28897721
theorem B2004971 : Blo 1334986 2004971 := bstep (se 1 (by rfl) ⟨1503728, by rfl⟩ : syracuseStep 2004971 = 3007457) B3007457
theorem B2005019 : Blo 1334986 2005019 := bstep (se 1 (by rfl) ⟨1503764, by rfl⟩ : syracuseStep 2005019 = 3007529) B3007529
theorem B3004775 : Blo 1334986 3004775 := bstep (se 1 (by rfl) ⟨2253581, by rfl⟩ : syracuseStep 3004775 = 4507163) B4507163
theorem B2005403 : Blo 1334986 2005403 := bstep (se 1 (by rfl) ⟨1504052, by rfl⟩ : syracuseStep 2005403 = 3008105) B3008105
theorem B21658043 : Blo 1334986 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B14440943 : Blo 1334986 14440943 := bstep (se 1 (by rfl) ⟨10830707, by rfl⟩ : syracuseStep 14440943 = 21661415) B21661415
theorem B10828343 : Blo 1334986 10828343 := bstep (se 1 (by rfl) ⟨8121257, by rfl⟩ : syracuseStep 10828343 = 16242515) B16242515
theorem B7608937 : Blo 1334986 7608937 := bstep (se 2 (by rfl) ⟨2853351, by rfl⟩ : syracuseStep 7608937 = 5706703) B5706703
theorem B2030527 : Blo 1334986 2030527 := bstep (se 1 (by rfl) ⟨1522895, by rfl⟩ : syracuseStep 2030527 = 3045791) B3045791
theorem B8559827 : Blo 1334986 8559827 := bstep (se 1 (by rfl) ⟨6419870, by rfl⟩ : syracuseStep 8559827 = 12839741) B12839741
theorem B11411219 : Blo 1334986 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B6766415 : Blo 1334986 6766415 := bstep (se 1 (by rfl) ⟨5074811, by rfl⟩ : syracuseStep 6766415 = 10149623) B10149623
theorem B6766739 : Blo 1334986 6766739 := bstep (se 1 (by rfl) ⟨5075054, by rfl⟩ : syracuseStep 6766739 = 10150109) B10150109
theorem B6758639 : Blo 1334986 6758639 := bstep (se 1 (by rfl) ⟨5068979, by rfl⟩ : syracuseStep 6758639 = 10137959) B10137959
theorem B1335775 : Blo 1334986 1335775 := bstep (se 1 (by rfl) ⟨1001831, by rfl⟩ : syracuseStep 1335775 = 2003663) B2003663
theorem B48726497 : Blo 1334986 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B3801599 : Blo 1334986 3801599 := bstep (se 1 (by rfl) ⟨2851199, by rfl⟩ : syracuseStep 3801599 = 5702399) B5702399
theorem B10830419 : Blo 1334986 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B1335935 : Blo 1334986 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B31261373 : Blo 1334986 31261373 := bstep (se 3 (by rfl) ⟨5861507, by rfl⟩ : syracuseStep 31261373 = 11723015) B11723015
theorem B3007259 : Blo 1334986 3007259 := bstep (se 1 (by rfl) ⟨2255444, by rfl⟩ : syracuseStep 3007259 = 4510889) B4510889
theorem B12845891 : Blo 1334986 12845891 := bstep (se 1 (by rfl) ⟨9634418, by rfl⟩ : syracuseStep 12845891 = 19268837) B19268837
theorem B8561695 : Blo 1334986 8561695 := bstep (se 1 (by rfl) ⟨6421271, by rfl⟩ : syracuseStep 8561695 = 12842543) B12842543
theorem B1336647 : Blo 1334986 1336647 := bstep (se 1 (by rfl) ⟨1002485, by rfl⟩ : syracuseStep 1336647 = 2004971) B2004971
theorem B1336679 : Blo 1334986 1336679 := bstep (se 1 (by rfl) ⟨1002509, by rfl⟩ : syracuseStep 1336679 = 2005019) B2005019
theorem B1336935 : Blo 1334986 1336935 := bstep (se 1 (by rfl) ⟨1002701, by rfl⟩ : syracuseStep 1336935 = 2005403) B2005403
theorem B9627295 : Blo 1334986 9627295 := bstep (se 1 (by rfl) ⟨7220471, by rfl⟩ : syracuseStep 9627295 = 14440943) B14440943
theorem B41158307 : Blo 1334986 41158307 := bstep (se 1 (by rfl) ⟨30868730, by rfl⟩ : syracuseStep 41158307 = 61737461) B61737461
theorem B22841027 : Blo 1334986 22841027 := bstep (se 1 (by rfl) ⟨17130770, by rfl⟩ : syracuseStep 22841027 = 34261541) B34261541
theorem B7218895 : Blo 1334986 7218895 := bstep (se 1 (by rfl) ⟨5414171, by rfl⟩ : syracuseStep 7218895 = 10828343) B10828343
theorem B2141321 : Blo 1334986 2141321 := bstep (se 2 (by rfl) ⟨802995, by rfl⟩ : syracuseStep 2141321 = 1605991) B1605991
theorem B2256059 : Blo 1334986 2256059 := bstep (se 1 (by rfl) ⟨1692044, by rfl⟩ : syracuseStep 2256059 = 3384089) B3384089
theorem B12348683 : Blo 1334986 12348683 := bstep (se 1 (by rfl) ⟨9261512, by rfl⟩ : syracuseStep 12348683 = 18523025) B18523025
theorem B10988867 : Blo 1334986 10988867 := bstep (se 1 (by rfl) ⟨8241650, by rfl⟩ : syracuseStep 10988867 = 16483301) B16483301
theorem B6417737 : Blo 1334986 6417737 := bstep (se 2 (by rfl) ⟨2406651, by rfl⟩ : syracuseStep 6417737 = 4813303) B4813303
theorem B1502671 : Blo 1334986 1502671 := bstep (se 1 (by rfl) ⟨1127003, by rfl⟩ : syracuseStep 1502671 = 2254007) B2254007
theorem B10145249 : Blo 1334986 10145249 := bstep (se 2 (by rfl) ⟨3804468, by rfl⟩ : syracuseStep 10145249 = 7608937) B7608937
theorem B2002601 : Blo 1334986 2002601 := bstep (se 2 (by rfl) ⟨750975, by rfl⟩ : syracuseStep 2002601 = 1501951) B1501951
theorem B8130233 : Blo 1334986 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B6762527 : Blo 1334986 6762527 := bstep (se 1 (by rfl) ⟨5071895, by rfl⟩ : syracuseStep 6762527 = 10143791) B10143791
theorem B7221383 : Blo 1334986 7221383 := bstep (se 1 (by rfl) ⟨5416037, by rfl⟩ : syracuseStep 7221383 = 10832075) B10832075
theorem B2003183 : Blo 1334986 2003183 := bstep (se 1 (by rfl) ⟨1502387, by rfl⟩ : syracuseStep 2003183 = 3004775) B3004775
theorem B14438695 : Blo 1334986 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B1503535 : Blo 1334986 1503535 := bstep (se 1 (by rfl) ⟨1127651, by rfl⟩ : syracuseStep 1503535 = 2255303) B2255303
theorem B3207707 : Blo 1334986 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B5706551 : Blo 1334986 5706551 := bstep (se 1 (by rfl) ⟨4279913, by rfl⟩ : syracuseStep 5706551 = 8559827) B8559827
theorem B15225893 : Blo 1334986 15225893 := bstep (se 4 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 15225893 = 2854855) B2854855
theorem B2004089 : Blo 1334986 2004089 := bstep (se 2 (by rfl) ⟨751533, by rfl⟩ : syracuseStep 2004089 = 1503067) B1503067
theorem B7607479 : Blo 1334986 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B4510943 : Blo 1334986 4510943 := bstep (se 1 (by rfl) ⟨3383207, by rfl⟩ : syracuseStep 4510943 = 6766415) B6766415
theorem B2004233 : Blo 1334986 2004233 := bstep (se 2 (by rfl) ⟨751587, by rfl⟩ : syracuseStep 2004233 = 1503175) B1503175
theorem B2004527 : Blo 1334986 2004527 := bstep (se 1 (by rfl) ⟨1503395, by rfl⟩ : syracuseStep 2004527 = 3006791) B3006791
theorem B6092459 : Blo 1334986 6092459 := bstep (se 1 (by rfl) ⟨4569344, by rfl⟩ : syracuseStep 6092459 = 9138689) B9138689
theorem B3004487 : Blo 1334986 3004487 := bstep (se 1 (by rfl) ⟨2253365, by rfl⟩ : syracuseStep 3004487 = 4506731) B4506731
theorem B3004523 : Blo 1334986 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B9140363 : Blo 1334986 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B12843431 : Blo 1334986 12843431 := bstep (se 1 (by rfl) ⟨9632573, by rfl⟩ : syracuseStep 12843431 = 19265147) B19265147
theorem B3381851 : Blo 1334986 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B3005153 : Blo 1334986 3005153 := bstep (se 2 (by rfl) ⟨1126932, by rfl⟩ : syracuseStep 3005153 = 2253865) B2253865
theorem B12181043 : Blo 1334986 12181043 := bstep (se 1 (by rfl) ⟨9135782, by rfl⟩ : syracuseStep 12181043 = 18271565) B18271565
theorem B27442813 : Blo 1334986 27442813 := bstep (se 3 (by rfl) ⟨5145527, by rfl⟩ : syracuseStep 27442813 = 10291055) B10291055
theorem B3006107 : Blo 1334986 3006107 := bstep (se 1 (by rfl) ⟨2254580, by rfl⟩ : syracuseStep 3006107 = 4509161) B4509161
theorem B17120929 : Blo 1334986 17120929 := bstep (se 2 (by rfl) ⟨6420348, by rfl⟩ : syracuseStep 17120929 = 12840697) B12840697
theorem B10829477 : Blo 1334986 10829477 := bstep (se 4 (by rfl) ⟨1015263, by rfl⟩ : syracuseStep 10829477 = 2030527) B2030527
theorem B1335131 : Blo 1334986 1335131 := bstep (se 1 (by rfl) ⟨1001348, by rfl⟩ : syracuseStep 1335131 = 2002697) B2002697
theorem B1335167 : Blo 1334986 1335167 := bstep (se 1 (by rfl) ⟨1001375, by rfl⟩ : syracuseStep 1335167 = 2002751) B2002751
theorem B4505759 : Blo 1334986 4505759 := bstep (se 1 (by rfl) ⟨3379319, by rfl⟩ : syracuseStep 4505759 = 6758639) B6758639
theorem B1335455 : Blo 1334986 1335455 := bstep (se 1 (by rfl) ⟨1001591, by rfl⟩ : syracuseStep 1335455 = 2003183) B2003183
theorem B2138471 : Blo 1334986 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B5710189 : Blo 1334986 5710189 := bstep (se 3 (by rfl) ⟨1070660, by rfl⟩ : syracuseStep 5710189 = 2141321) B2141321
theorem B19251593 : Blo 1334986 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B20840915 : Blo 1334986 20840915 := bstep (se 1 (by rfl) ⟨15630686, by rfl⟩ : syracuseStep 20840915 = 31261373) B31261373
theorem B10150595 : Blo 1334986 10150595 := bstep (se 1 (by rfl) ⟨7612946, by rfl⟩ : syracuseStep 10150595 = 15225893) B15225893
theorem B1336059 : Blo 1334986 1336059 := bstep (se 1 (by rfl) ⟨1002044, by rfl⟩ : syracuseStep 1336059 = 2004089) B2004089
theorem B3007295 : Blo 1334986 3007295 := bstep (se 1 (by rfl) ⟨2255471, by rfl⟩ : syracuseStep 3007295 = 4510943) B4510943
theorem B1336155 : Blo 1334986 1336155 := bstep (se 1 (by rfl) ⟨1002116, by rfl⟩ : syracuseStep 1336155 = 2004233) B2004233
theorem B1336351 : Blo 1334986 1336351 := bstep (se 1 (by rfl) ⟨1002263, by rfl⟩ : syracuseStep 1336351 = 2004527) B2004527
theorem B32482781 : Blo 1334986 32482781 := bstep (se 3 (by rfl) ⟨6090521, by rfl⟩ : syracuseStep 32482781 = 12181043) B12181043
theorem B10143305 : Blo 1334986 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B8562287 : Blo 1334986 8562287 := bstep (se 1 (by rfl) ⟨6421715, by rfl⟩ : syracuseStep 8562287 = 12843431) B12843431
theorem B2254567 : Blo 1334986 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B28878605 : Blo 1334986 28878605 := bstep (se 3 (by rfl) ⟨5414738, by rfl⟩ : syracuseStep 28878605 = 10829477) B10829477
theorem B7325911 : Blo 1334986 7325911 := bstep (se 1 (by rfl) ⟨5494433, by rfl⟩ : syracuseStep 7325911 = 10988867) B10988867
theorem B4278491 : Blo 1334986 4278491 := bstep (se 1 (by rfl) ⟨3208868, by rfl⟩ : syracuseStep 4278491 = 6417737) B6417737
theorem B4508351 : Blo 1334986 4508351 := bstep (se 1 (by rfl) ⟨3381263, by rfl⟩ : syracuseStep 4508351 = 6762527) B6762527
theorem B32484331 : Blo 1334986 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B2534399 : Blo 1334986 2534399 := bstep (se 1 (by rfl) ⟨1900799, by rfl⟩ : syracuseStep 2534399 = 3801599) B3801599
theorem B7220279 : Blo 1334986 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B3804367 : Blo 1334986 3804367 := bstep (se 1 (by rfl) ⟨2853275, by rfl⟩ : syracuseStep 3804367 = 5706551) B5706551
theorem B8563927 : Blo 1334986 8563927 := bstep (se 1 (by rfl) ⟨6422945, by rfl⟩ : syracuseStep 8563927 = 12845891) B12845891
theorem B11415593 : Blo 1334986 11415593 := bstep (se 2 (by rfl) ⟨4280847, by rfl⟩ : syracuseStep 11415593 = 8561695) B8561695
theorem B2002991 : Blo 1334986 2002991 := bstep (se 1 (by rfl) ⟨1502243, by rfl⟩ : syracuseStep 2002991 = 3004487) B3004487
theorem B2003015 : Blo 1334986 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B2003435 : Blo 1334986 2003435 := bstep (se 1 (by rfl) ⟨1502576, by rfl⟩ : syracuseStep 2003435 = 3005153) B3005153
theorem B21680621 : Blo 1334986 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B2003561 : Blo 1334986 2003561 := bstep (se 2 (by rfl) ⟨751335, by rfl⟩ : syracuseStep 2003561 = 1502671) B1502671
theorem B1504039 : Blo 1334986 1504039 := bstep (se 1 (by rfl) ⟨1128029, by rfl⟩ : syracuseStep 1504039 = 2256059) B2256059
theorem B36590417 : Blo 1334986 36590417 := bstep (se 2 (by rfl) ⟨13721406, by rfl⟩ : syracuseStep 36590417 = 27442813) B27442813
theorem B22827905 : Blo 1334986 22827905 := bstep (se 2 (by rfl) ⟨8560464, by rfl⟩ : syracuseStep 22827905 = 17120929) B17120929
theorem B6763499 : Blo 1334986 6763499 := bstep (se 1 (by rfl) ⟨5072624, by rfl⟩ : syracuseStep 6763499 = 10145249) B10145249
theorem B2004071 : Blo 1334986 2004071 := bstep (se 1 (by rfl) ⟨1503053, by rfl⟩ : syracuseStep 2004071 = 3006107) B3006107
theorem B4814255 : Blo 1334986 4814255 := bstep (se 1 (by rfl) ⟨3610691, by rfl⟩ : syracuseStep 4814255 = 7221383) B7221383
theorem B4511159 : Blo 1334986 4511159 := bstep (se 1 (by rfl) ⟨3383369, by rfl⟩ : syracuseStep 4511159 = 6766739) B6766739
theorem B2004713 : Blo 1334986 2004713 := bstep (se 2 (by rfl) ⟨751767, by rfl⟩ : syracuseStep 2004713 = 1503535) B1503535
theorem B2004839 : Blo 1334986 2004839 := bstep (se 1 (by rfl) ⟨1503629, by rfl⟩ : syracuseStep 2004839 = 3007259) B3007259
theorem B4061639 : Blo 1334986 4061639 := bstep (se 1 (by rfl) ⟨3046229, by rfl⟩ : syracuseStep 4061639 = 6092459) B6092459
theorem B15227351 : Blo 1334986 15227351 := bstep (se 1 (by rfl) ⟨11420513, by rfl⟩ : syracuseStep 15227351 = 22841027) B22841027
theorem B6093575 : Blo 1334986 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B109755485 : Blo 1334986 109755485 := bstep (se 3 (by rfl) ⟨20579153, by rfl⟩ : syracuseStep 109755485 = 41158307) B41158307
theorem B8232455 : Blo 1334986 8232455 := bstep (se 1 (by rfl) ⟨6174341, by rfl⟩ : syracuseStep 8232455 = 12348683) B12348683
theorem B12836393 : Blo 1334986 12836393 := bstep (se 2 (by rfl) ⟨4813647, by rfl⟩ : syracuseStep 12836393 = 9627295) B9627295
theorem B9625193 : Blo 1334986 9625193 := bstep (se 2 (by rfl) ⟨3609447, by rfl⟩ : syracuseStep 9625193 = 7218895) B7218895
theorem B1335067 : Blo 1334986 1335067 := bstep (se 1 (by rfl) ⟨1001300, by rfl⟩ : syracuseStep 1335067 = 2002601) B2002601
theorem B7610395 : Blo 1334986 7610395 := bstep (se 1 (by rfl) ⟨5707796, by rfl⟩ : syracuseStep 7610395 = 11415593) B11415593
theorem B1335327 : Blo 1334986 1335327 := bstep (se 1 (by rfl) ⟨1001495, by rfl⟩ : syracuseStep 1335327 = 2002991) B2002991
theorem B1335343 : Blo 1334986 1335343 := bstep (se 1 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 1335343 = 2003015) B2003015
theorem B1425647 : Blo 1334986 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B13893943 : Blo 1334986 13893943 := bstep (se 1 (by rfl) ⟨10420457, by rfl⟩ : syracuseStep 13893943 = 20840915) B20840915
theorem B1335623 : Blo 1334986 1335623 := bstep (se 1 (by rfl) ⟨1001717, by rfl⟩ : syracuseStep 1335623 = 2003435) B2003435
theorem B1335707 : Blo 1334986 1335707 := bstep (se 1 (by rfl) ⟨1001780, by rfl⟩ : syracuseStep 1335707 = 2003561) B2003561
theorem B6767063 : Blo 1334986 6767063 := bstep (se 1 (by rfl) ⟨5075297, by rfl⟩ : syracuseStep 6767063 = 10150595) B10150595
theorem B1336047 : Blo 1334986 1336047 := bstep (se 1 (by rfl) ⟨1002035, by rfl⟩ : syracuseStep 1336047 = 2004071) B2004071
theorem B3007439 : Blo 1334986 3007439 := bstep (se 1 (by rfl) ⟨2255579, by rfl⟩ : syracuseStep 3007439 = 4511159) B4511159
theorem B1336475 : Blo 1334986 1336475 := bstep (se 1 (by rfl) ⟨1002356, by rfl⟩ : syracuseStep 1336475 = 2004713) B2004713
theorem B19252403 : Blo 1334986 19252403 := bstep (se 1 (by rfl) ⟨14439302, by rfl⟩ : syracuseStep 19252403 = 28878605) B28878605
theorem B1336559 : Blo 1334986 1336559 := bstep (se 1 (by rfl) ⟨1002419, by rfl⟩ : syracuseStep 1336559 = 2004839) B2004839
theorem B2852327 : Blo 1334986 2852327 := bstep (se 1 (by rfl) ⟨2139245, by rfl⟩ : syracuseStep 2852327 = 4278491) B4278491
theorem B5072489 : Blo 1334986 5072489 := bstep (se 2 (by rfl) ⟨1902183, by rfl⟩ : syracuseStep 5072489 = 3804367) B3804367
theorem B10151567 : Blo 1334986 10151567 := bstep (se 1 (by rfl) ⟨7613675, by rfl⟩ : syracuseStep 10151567 = 15227351) B15227351
theorem B1689599 : Blo 1334986 1689599 := bstep (se 1 (by rfl) ⟨1267199, by rfl⟩ : syracuseStep 1689599 = 2534399) B2534399
theorem B6416795 : Blo 1334986 6416795 := bstep (se 1 (by rfl) ⟨4812596, by rfl⟩ : syracuseStep 6416795 = 9625193) B9625193
theorem B9767881 : Blo 1334986 9767881 := bstep (se 2 (by rfl) ⟨3662955, by rfl⟩ : syracuseStep 9767881 = 7325911) B7325911
theorem B14453747 : Blo 1334986 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B7613585 : Blo 1334986 7613585 := bstep (se 2 (by rfl) ⟨2855094, by rfl⟩ : syracuseStep 7613585 = 5710189) B5710189
theorem B4508999 : Blo 1334986 4508999 := bstep (se 1 (by rfl) ⟨3381749, by rfl⟩ : syracuseStep 4508999 = 6763499) B6763499
theorem B21655187 : Blo 1334986 21655187 := bstep (se 1 (by rfl) ⟨16241390, by rfl⟩ : syracuseStep 21655187 = 32482781) B32482781
theorem B6762203 : Blo 1334986 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B2707759 : Blo 1334986 2707759 := bstep (se 1 (by rfl) ⟨2030819, by rfl⟩ : syracuseStep 2707759 = 4061639) B4061639
theorem B4813519 : Blo 1334986 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B8557595 : Blo 1334986 8557595 := bstep (se 1 (by rfl) ⟨6418196, by rfl⟩ : syracuseStep 8557595 = 12836393) B12836393
theorem B173249765 : Blo 1334986 173249765 := bstep (se 4 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 173249765 = 32484331) B32484331
theorem B3003839 : Blo 1334986 3003839 := bstep (se 1 (by rfl) ⟨2252879, by rfl⟩ : syracuseStep 3003839 = 4505759) B4505759
theorem B12834395 : Blo 1334986 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B2004863 : Blo 1334986 2004863 := bstep (se 1 (by rfl) ⟨1503647, by rfl⟩ : syracuseStep 2004863 = 3007295) B3007295
theorem B24393611 : Blo 1334986 24393611 := bstep (se 1 (by rfl) ⟨18295208, by rfl⟩ : syracuseStep 24393611 = 36590417) B36590417
theorem B15218603 : Blo 1334986 15218603 := bstep (se 1 (by rfl) ⟨11413952, by rfl⟩ : syracuseStep 15218603 = 22827905) B22827905
theorem B3209503 : Blo 1334986 3209503 := bstep (se 1 (by rfl) ⟨2407127, by rfl⟩ : syracuseStep 3209503 = 4814255) B4814255
theorem B2005385 : Blo 1334986 2005385 := bstep (se 2 (by rfl) ⟨752019, by rfl⟩ : syracuseStep 2005385 = 1504039) B1504039
theorem B5708191 : Blo 1334986 5708191 := bstep (se 1 (by rfl) ⟨4281143, by rfl⟩ : syracuseStep 5708191 = 8562287) B8562287
theorem B21953213 : Blo 1334986 21953213 := bstep (se 3 (by rfl) ⟨4116227, by rfl⟩ : syracuseStep 21953213 = 8232455) B8232455
theorem B11418569 : Blo 1334986 11418569 := bstep (se 2 (by rfl) ⟨4281963, by rfl⟩ : syracuseStep 11418569 = 8563927) B8563927
theorem B3005567 : Blo 1334986 3005567 := bstep (se 1 (by rfl) ⟨2254175, by rfl⟩ : syracuseStep 3005567 = 4508351) B4508351
theorem B4062383 : Blo 1334986 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B73170323 : Blo 1334986 73170323 := bstep (se 1 (by rfl) ⟨54877742, by rfl⟩ : syracuseStep 73170323 = 109755485) B109755485
theorem B3006089 : Blo 1334986 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B7610921 : Blo 1334986 7610921 := bstep (se 2 (by rfl) ⟨2854095, by rfl⟩ : syracuseStep 7610921 = 5708191) B5708191
theorem B3801725 : Blo 1334986 3801725 := bstep (se 3 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 3801725 = 1425647) B1425647
theorem B115499843 : Blo 1334986 115499843 := bstep (se 1 (by rfl) ⟨86624882, by rfl⟩ : syracuseStep 115499843 = 173249765) B173249765
theorem B1901551 : Blo 1334986 1901551 := bstep (se 1 (by rfl) ⟨1426163, by rfl⟩ : syracuseStep 1901551 = 2852327) B2852327
theorem B6767711 : Blo 1334986 6767711 := bstep (se 1 (by rfl) ⟨5075783, by rfl⟩ : syracuseStep 6767711 = 10151567) B10151567
theorem B1336575 : Blo 1334986 1336575 := bstep (se 1 (by rfl) ⟨1002431, by rfl⟩ : syracuseStep 1336575 = 2004863) B2004863
theorem B16262407 : Blo 1334986 16262407 := bstep (se 1 (by rfl) ⟨12196805, by rfl⟩ : syracuseStep 16262407 = 24393611) B24393611
theorem B1336923 : Blo 1334986 1336923 := bstep (se 1 (by rfl) ⟨1002692, by rfl⟩ : syracuseStep 1336923 = 2005385) B2005385
theorem B4277863 : Blo 1334986 4277863 := bstep (se 1 (by rfl) ⟨3208397, by rfl⟩ : syracuseStep 4277863 = 6416795) B6416795
theorem B7612379 : Blo 1334986 7612379 := bstep (se 1 (by rfl) ⟨5709284, by rfl⟩ : syracuseStep 7612379 = 11418569) B11418569
theorem B9635831 : Blo 1334986 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B14436791 : Blo 1334986 14436791 := bstep (se 1 (by rfl) ⟨10827593, by rfl⟩ : syracuseStep 14436791 = 21655187) B21655187
theorem B4508135 : Blo 1334986 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B4279337 : Blo 1334986 4279337 := bstep (se 2 (by rfl) ⟨1604751, by rfl⟩ : syracuseStep 4279337 = 3209503) B3209503
theorem B18525257 : Blo 1334986 18525257 := bstep (se 2 (by rfl) ⟨6946971, by rfl⟩ : syracuseStep 18525257 = 13893943) B13893943
theorem B5705063 : Blo 1334986 5705063 := bstep (se 1 (by rfl) ⟨4278797, by rfl⟩ : syracuseStep 5705063 = 8557595) B8557595
theorem B6418025 : Blo 1334986 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B2002559 : Blo 1334986 2002559 := bstep (se 1 (by rfl) ⟨1501919, by rfl⟩ : syracuseStep 2002559 = 3003839) B3003839
theorem B8556263 : Blo 1334986 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B10145735 : Blo 1334986 10145735 := bstep (se 1 (by rfl) ⟨7609301, by rfl⟩ : syracuseStep 10145735 = 15218603) B15218603
theorem B14635475 : Blo 1334986 14635475 := bstep (se 1 (by rfl) ⟨10976606, by rfl⟩ : syracuseStep 14635475 = 21953213) B21953213
theorem B2003711 : Blo 1334986 2003711 := bstep (se 1 (by rfl) ⟨1502783, by rfl⟩ : syracuseStep 2003711 = 3005567) B3005567
theorem B5075723 : Blo 1334986 5075723 := bstep (se 1 (by rfl) ⟨3806792, by rfl⟩ : syracuseStep 5075723 = 7613585) B7613585
theorem B2708255 : Blo 1334986 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B48780215 : Blo 1334986 48780215 := bstep (se 1 (by rfl) ⟨36585161, by rfl⟩ : syracuseStep 48780215 = 73170323) B73170323
theorem B2004059 : Blo 1334986 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B10147193 : Blo 1334986 10147193 := bstep (se 2 (by rfl) ⟨3805197, by rfl⟩ : syracuseStep 10147193 = 7610395) B7610395
theorem B4511375 : Blo 1334986 4511375 := bstep (se 1 (by rfl) ⟨3383531, by rfl⟩ : syracuseStep 4511375 = 6767063) B6767063
theorem B3610345 : Blo 1334986 3610345 := bstep (se 2 (by rfl) ⟨1353879, by rfl⟩ : syracuseStep 3610345 = 2707759) B2707759
theorem B2004959 : Blo 1334986 2004959 := bstep (se 1 (by rfl) ⟨1503719, by rfl⟩ : syracuseStep 2004959 = 3007439) B3007439
theorem B12834935 : Blo 1334986 12834935 := bstep (se 1 (by rfl) ⟨9626201, by rfl⟩ : syracuseStep 12834935 = 19252403) B19252403
theorem B3381659 : Blo 1334986 3381659 := bstep (se 1 (by rfl) ⟨2536244, by rfl⟩ : syracuseStep 3381659 = 5072489) B5072489
theorem B13023841 : Blo 1334986 13023841 := bstep (se 2 (by rfl) ⟨4883940, by rfl⟩ : syracuseStep 13023841 = 9767881) B9767881
theorem B3005999 : Blo 1334986 3005999 := bstep (se 1 (by rfl) ⟨2254499, by rfl⟩ : syracuseStep 3005999 = 4508999) B4508999
theorem B4505597 : Blo 1334986 4505597 := bstep (se 3 (by rfl) ⟨844799, by rfl⟩ : syracuseStep 4505597 = 1689599) B1689599
theorem B9756983 : Blo 1334986 9756983 := bstep (se 1 (by rfl) ⟨7317737, by rfl⟩ : syracuseStep 9756983 = 14635475) B14635475
theorem B1335807 : Blo 1334986 1335807 := bstep (se 1 (by rfl) ⟨1001855, by rfl⟩ : syracuseStep 1335807 = 2003711) B2003711
theorem B3383815 : Blo 1334986 3383815 := bstep (se 1 (by rfl) ⟨2537861, by rfl⟩ : syracuseStep 3383815 = 5075723) B5075723
theorem B1336039 : Blo 1334986 1336039 := bstep (se 1 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 1336039 = 2004059) B2004059
theorem B3007583 : Blo 1334986 3007583 := bstep (se 1 (by rfl) ⟨2255687, by rfl⟩ : syracuseStep 3007583 = 4511375) B4511375
theorem B1336639 : Blo 1334986 1336639 := bstep (se 1 (by rfl) ⟨1002479, by rfl⟩ : syracuseStep 1336639 = 2004959) B2004959
theorem B6423887 : Blo 1334986 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B2254439 : Blo 1334986 2254439 := bstep (se 1 (by rfl) ⟨1690829, by rfl⟩ : syracuseStep 2254439 = 3381659) B3381659
theorem B2852891 : Blo 1334986 2852891 := bstep (se 1 (by rfl) ⟨2139668, by rfl⟩ : syracuseStep 2852891 = 4279337) B4279337
theorem B5703817 : Blo 1334986 5703817 := bstep (se 2 (by rfl) ⟨2138931, by rfl⟩ : syracuseStep 5703817 = 4277863) B4277863
theorem B3803375 : Blo 1334986 3803375 := bstep (se 1 (by rfl) ⟨2852531, by rfl⟩ : syracuseStep 3803375 = 5705063) B5705063
theorem B4278683 : Blo 1334986 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B5704175 : Blo 1334986 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B5073947 : Blo 1334986 5073947 := bstep (se 1 (by rfl) ⟨3805460, by rfl⟩ : syracuseStep 5073947 = 7610921) B7610921
theorem B2534483 : Blo 1334986 2534483 := bstep (se 1 (by rfl) ⟨1900862, by rfl⟩ : syracuseStep 2534483 = 3801725) B3801725
theorem B1805503 : Blo 1334986 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B76999895 : Blo 1334986 76999895 := bstep (se 1 (by rfl) ⟨57749921, by rfl⟩ : syracuseStep 76999895 = 115499843) B115499843
theorem B5074919 : Blo 1334986 5074919 := bstep (se 1 (by rfl) ⟨3806189, by rfl⟩ : syracuseStep 5074919 = 7612379) B7612379
theorem B2535401 : Blo 1334986 2535401 := bstep (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) B1901551
theorem B8556623 : Blo 1334986 8556623 := bstep (se 1 (by rfl) ⟨6417467, by rfl⟩ : syracuseStep 8556623 = 12834935) B12834935
theorem B12350171 : Blo 1334986 12350171 := bstep (se 1 (by rfl) ⟨9262628, by rfl⟩ : syracuseStep 12350171 = 18525257) B18525257
theorem B4813793 : Blo 1334986 4813793 := bstep (se 2 (by rfl) ⟨1805172, by rfl⟩ : syracuseStep 4813793 = 3610345) B3610345
theorem B2003999 : Blo 1334986 2003999 := bstep (se 1 (by rfl) ⟨1502999, by rfl⟩ : syracuseStep 2003999 = 3005999) B3005999
theorem B6763823 : Blo 1334986 6763823 := bstep (se 1 (by rfl) ⟨5072867, by rfl⟩ : syracuseStep 6763823 = 10145735) B10145735
theorem B3003731 : Blo 1334986 3003731 := bstep (se 1 (by rfl) ⟨2252798, by rfl⟩ : syracuseStep 3003731 = 4505597) B4505597
theorem B32520143 : Blo 1334986 32520143 := bstep (se 1 (by rfl) ⟨24390107, by rfl⟩ : syracuseStep 32520143 = 48780215) B48780215
theorem B4511807 : Blo 1334986 4511807 := bstep (se 1 (by rfl) ⟨3383855, by rfl⟩ : syracuseStep 4511807 = 6767711) B6767711
theorem B17365121 : Blo 1334986 17365121 := bstep (se 2 (by rfl) ⟨6511920, by rfl⟩ : syracuseStep 17365121 = 13023841) B13023841
theorem B6764795 : Blo 1334986 6764795 := bstep (se 1 (by rfl) ⟨5073596, by rfl⟩ : syracuseStep 6764795 = 10147193) B10147193
theorem B9624527 : Blo 1334986 9624527 := bstep (se 1 (by rfl) ⟨7218395, by rfl⟩ : syracuseStep 9624527 = 14436791) B14436791
theorem B3005423 : Blo 1334986 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B21683209 : Blo 1334986 21683209 := bstep (se 2 (by rfl) ⟨8131203, by rfl⟩ : syracuseStep 21683209 = 16262407) B16262407
theorem B1335039 : Blo 1334986 1335039 := bstep (se 1 (by rfl) ⟨1001279, by rfl⟩ : syracuseStep 1335039 = 2002559) B2002559
theorem B8233447 : Blo 1334986 8233447 := bstep (se 1 (by rfl) ⟨6175085, by rfl⟩ : syracuseStep 8233447 = 12350171) B12350171
theorem B10142333 : Blo 1334986 10142333 := bstep (se 3 (by rfl) ⟨1901687, by rfl⟩ : syracuseStep 10142333 = 3803375) B3803375
theorem B1335999 : Blo 1334986 1335999 := bstep (se 1 (by rfl) ⟨1001999, by rfl⟩ : syracuseStep 1335999 = 2003999) B2003999
theorem B26018621 : Blo 1334986 26018621 := bstep (se 3 (by rfl) ⟨4878491, by rfl⟩ : syracuseStep 26018621 = 9756983) B9756983
theorem B28910945 : Blo 1334986 28910945 := bstep (se 2 (by rfl) ⟨10841604, by rfl⟩ : syracuseStep 28910945 = 21683209) B21683209
theorem B1901927 : Blo 1334986 1901927 := bstep (se 1 (by rfl) ⟨1426445, by rfl⟩ : syracuseStep 1901927 = 2852891) B2852891
theorem B3007871 : Blo 1334986 3007871 := bstep (se 1 (by rfl) ⟨2255903, by rfl⟩ : syracuseStep 3007871 = 4511807) B4511807
theorem B11576747 : Blo 1334986 11576747 := bstep (se 1 (by rfl) ⟨8682560, by rfl⟩ : syracuseStep 11576747 = 17365121) B17365121
theorem B3802783 : Blo 1334986 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B6416351 : Blo 1334986 6416351 := bstep (se 1 (by rfl) ⟨4812263, by rfl⟩ : syracuseStep 6416351 = 9624527) B9624527
theorem B1689655 : Blo 1334986 1689655 := bstep (se 1 (by rfl) ⟨1267241, by rfl⟩ : syracuseStep 1689655 = 2534483) B2534483
theorem B51333263 : Blo 1334986 51333263 := bstep (se 1 (by rfl) ⟨38499947, by rfl⟩ : syracuseStep 51333263 = 76999895) B76999895
theorem B6761069 : Blo 1334986 6761069 := bstep (se 3 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 6761069 = 2535401) B2535401
theorem B5704415 : Blo 1334986 5704415 := bstep (se 1 (by rfl) ⟨4278311, by rfl⟩ : syracuseStep 5704415 = 8556623) B8556623
theorem B7605089 : Blo 1334986 7605089 := bstep (se 2 (by rfl) ⟨2851908, by rfl⟩ : syracuseStep 7605089 = 5703817) B5703817
theorem B4509215 : Blo 1334986 4509215 := bstep (se 1 (by rfl) ⟨3381911, by rfl⟩ : syracuseStep 4509215 = 6763823) B6763823
theorem B2002487 : Blo 1334986 2002487 := bstep (se 1 (by rfl) ⟨1501865, by rfl⟩ : syracuseStep 2002487 = 3003731) B3003731
theorem B1502959 : Blo 1334986 1502959 := bstep (se 1 (by rfl) ⟨1127219, by rfl⟩ : syracuseStep 1502959 = 2254439) B2254439
theorem B4509863 : Blo 1334986 4509863 := bstep (se 1 (by rfl) ⟨3382397, by rfl⟩ : syracuseStep 4509863 = 6764795) B6764795
theorem B2003615 : Blo 1334986 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B3209195 : Blo 1334986 3209195 := bstep (se 1 (by rfl) ⟨2406896, by rfl⟩ : syracuseStep 3209195 = 4813793) B4813793
theorem B4511753 : Blo 1334986 4511753 := bstep (se 2 (by rfl) ⟨1691907, by rfl⟩ : syracuseStep 4511753 = 3383815) B3383815
theorem B2005055 : Blo 1334986 2005055 := bstep (se 1 (by rfl) ⟨1503791, by rfl⟩ : syracuseStep 2005055 = 3007583) B3007583
theorem B4282591 : Blo 1334986 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B11409821 : Blo 1334986 11409821 := bstep (se 3 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 11409821 = 4278683) B4278683
theorem B2407337 : Blo 1334986 2407337 := bstep (se 2 (by rfl) ⟨902751, by rfl⟩ : syracuseStep 2407337 = 1805503) B1805503
theorem B3382631 : Blo 1334986 3382631 := bstep (se 1 (by rfl) ⟨2536973, by rfl⟩ : syracuseStep 3382631 = 5073947) B5073947
theorem B86720381 : Blo 1334986 86720381 := bstep (se 3 (by rfl) ⟨16260071, by rfl⟩ : syracuseStep 86720381 = 32520143) B32520143
theorem B3383279 : Blo 1334986 3383279 := bstep (se 1 (by rfl) ⟨2537459, by rfl⟩ : syracuseStep 3383279 = 5074919) B5074919
theorem B2252873 : Blo 1334986 2252873 := bstep (se 2 (by rfl) ⟨844827, by rfl⟩ : syracuseStep 2252873 = 1689655) B1689655
theorem B3006575 : Blo 1334986 3006575 := bstep (se 1 (by rfl) ⟨2254931, by rfl⟩ : syracuseStep 3006575 = 4509863) B4509863
theorem B5710121 : Blo 1334986 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B1335743 : Blo 1334986 1335743 := bstep (se 1 (by rfl) ⟨1001807, by rfl⟩ : syracuseStep 1335743 = 2003615) B2003615
theorem B10977929 : Blo 1334986 10977929 := bstep (se 2 (by rfl) ⟨4116723, by rfl⟩ : syracuseStep 10977929 = 8233447) B8233447
theorem B5071805 : Blo 1334986 5071805 := bstep (se 3 (by rfl) ⟨950963, by rfl⟩ : syracuseStep 5071805 = 1901927) B1901927
theorem B4277567 : Blo 1334986 4277567 := bstep (se 1 (by rfl) ⟨3208175, by rfl⟩ : syracuseStep 4277567 = 6416351) B6416351
theorem B2139463 : Blo 1334986 2139463 := bstep (se 1 (by rfl) ⟨1604597, by rfl⟩ : syracuseStep 2139463 = 3209195) B3209195
theorem B3007835 : Blo 1334986 3007835 := bstep (se 1 (by rfl) ⟨2255876, by rfl⟩ : syracuseStep 3007835 = 4511753) B4511753
theorem B1336703 : Blo 1334986 1336703 := bstep (se 1 (by rfl) ⟨1002527, by rfl⟩ : syracuseStep 1336703 = 2005055) B2005055
theorem B4507379 : Blo 1334986 4507379 := bstep (se 1 (by rfl) ⟨3380534, by rfl⟩ : syracuseStep 4507379 = 6761069) B6761069
theorem B3802943 : Blo 1334986 3802943 := bstep (se 1 (by rfl) ⟨2852207, by rfl⟩ : syracuseStep 3802943 = 5704415) B5704415
theorem B2255087 : Blo 1334986 2255087 := bstep (se 1 (by rfl) ⟨1691315, by rfl⟩ : syracuseStep 2255087 = 3382631) B3382631
theorem B57813587 : Blo 1334986 57813587 := bstep (se 1 (by rfl) ⟨43360190, by rfl⟩ : syracuseStep 57813587 = 86720381) B86720381
theorem B2255519 : Blo 1334986 2255519 := bstep (se 1 (by rfl) ⟨1691639, by rfl⟩ : syracuseStep 2255519 = 3383279) B3383279
theorem B6761555 : Blo 1334986 6761555 := bstep (se 1 (by rfl) ⟨5071166, by rfl⟩ : syracuseStep 6761555 = 10142333) B10142333
theorem B17345747 : Blo 1334986 17345747 := bstep (se 1 (by rfl) ⟨13009310, by rfl⟩ : syracuseStep 17345747 = 26018621) B26018621
theorem B30871325 : Blo 1334986 30871325 := bstep (se 3 (by rfl) ⟨5788373, by rfl⟩ : syracuseStep 30871325 = 11576747) B11576747
theorem B34222175 : Blo 1334986 34222175 := bstep (se 1 (by rfl) ⟨25666631, by rfl⟩ : syracuseStep 34222175 = 51333263) B51333263
theorem B7606547 : Blo 1334986 7606547 := bstep (se 1 (by rfl) ⟨5704910, by rfl⟩ : syracuseStep 7606547 = 11409821) B11409821
theorem B2003945 : Blo 1334986 2003945 := bstep (se 2 (by rfl) ⟨751479, by rfl⟩ : syracuseStep 2003945 = 1502959) B1502959
theorem B19273963 : Blo 1334986 19273963 := bstep (se 1 (by rfl) ⟨14455472, by rfl⟩ : syracuseStep 19273963 = 28910945) B28910945
theorem B2005247 : Blo 1334986 2005247 := bstep (se 1 (by rfl) ⟨1503935, by rfl⟩ : syracuseStep 2005247 = 3007871) B3007871
theorem B5070059 : Blo 1334986 5070059 := bstep (se 1 (by rfl) ⟨3802544, by rfl⟩ : syracuseStep 5070059 = 7605089) B7605089
theorem B1604891 : Blo 1334986 1604891 := bstep (se 1 (by rfl) ⟨1203668, by rfl⟩ : syracuseStep 1604891 = 2407337) B2407337
theorem B5070377 : Blo 1334986 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B3006143 : Blo 1334986 3006143 := bstep (se 1 (by rfl) ⟨2254607, by rfl⟩ : syracuseStep 3006143 = 4509215) B4509215
theorem B1334991 : Blo 1334986 1334991 := bstep (se 1 (by rfl) ⟨1001243, by rfl⟩ : syracuseStep 1334991 = 2002487) B2002487
theorem B22814783 : Blo 1334986 22814783 := bstep (se 1 (by rfl) ⟨17111087, by rfl⟩ : syracuseStep 22814783 = 34222175) B34222175
theorem B5071031 : Blo 1334986 5071031 := bstep (se 1 (by rfl) ⟨3803273, by rfl⟩ : syracuseStep 5071031 = 7606547) B7606547
theorem B1335963 : Blo 1334986 1335963 := bstep (se 1 (by rfl) ⟨1001972, by rfl⟩ : syracuseStep 1335963 = 2003945) B2003945
theorem B1336831 : Blo 1334986 1336831 := bstep (se 1 (by rfl) ⟨1002623, by rfl⟩ : syracuseStep 1336831 = 2005247) B2005247
theorem B25698617 : Blo 1334986 25698617 := bstep (se 2 (by rfl) ⟨9636981, by rfl⟩ : syracuseStep 25698617 = 19273963) B19273963
theorem B4507703 : Blo 1334986 4507703 := bstep (se 1 (by rfl) ⟨3380777, by rfl⟩ : syracuseStep 4507703 = 6761555) B6761555
theorem B82323533 : Blo 1334986 82323533 := bstep (se 3 (by rfl) ⟨15435662, by rfl⟩ : syracuseStep 82323533 = 30871325) B30871325
theorem B1501915 : Blo 1334986 1501915 := bstep (se 1 (by rfl) ⟨1126436, by rfl⟩ : syracuseStep 1501915 = 2252873) B2252873
theorem B7318619 : Blo 1334986 7318619 := bstep (se 1 (by rfl) ⟨5488964, by rfl⟩ : syracuseStep 7318619 = 10977929) B10977929
theorem B4279709 : Blo 1334986 4279709 := bstep (se 3 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 4279709 = 1604891) B1604891
theorem B11406845 : Blo 1334986 11406845 := bstep (se 3 (by rfl) ⟨2138783, by rfl⟩ : syracuseStep 11406845 = 4277567) B4277567
theorem B2535295 : Blo 1334986 2535295 := bstep (se 1 (by rfl) ⟨1901471, by rfl⟩ : syracuseStep 2535295 = 3802943) B3802943
theorem B1503391 : Blo 1334986 1503391 := bstep (se 1 (by rfl) ⟨1127543, by rfl⟩ : syracuseStep 1503391 = 2255087) B2255087
theorem B1503679 : Blo 1334986 1503679 := bstep (se 1 (by rfl) ⟨1127759, by rfl⟩ : syracuseStep 1503679 = 2255519) B2255519
theorem B11563831 : Blo 1334986 11563831 := bstep (se 1 (by rfl) ⟨8672873, by rfl⟩ : syracuseStep 11563831 = 17345747) B17345747
theorem B3380039 : Blo 1334986 3380039 := bstep (se 1 (by rfl) ⟨2535029, by rfl⟩ : syracuseStep 3380039 = 5070059) B5070059
theorem B3380251 : Blo 1334986 3380251 := bstep (se 1 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 3380251 = 5070377) B5070377
theorem B2004095 : Blo 1334986 2004095 := bstep (se 1 (by rfl) ⟨1503071, by rfl⟩ : syracuseStep 2004095 = 3006143) B3006143
theorem B2004383 : Blo 1334986 2004383 := bstep (se 1 (by rfl) ⟨1503287, by rfl⟩ : syracuseStep 2004383 = 3006575) B3006575
theorem B3806747 : Blo 1334986 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B3381203 : Blo 1334986 3381203 := bstep (se 1 (by rfl) ⟨2535902, by rfl⟩ : syracuseStep 3381203 = 5071805) B5071805
theorem B2005223 : Blo 1334986 2005223 := bstep (se 1 (by rfl) ⟨1503917, by rfl⟩ : syracuseStep 2005223 = 3007835) B3007835
theorem B3004919 : Blo 1334986 3004919 := bstep (se 1 (by rfl) ⟨2253689, by rfl⟩ : syracuseStep 3004919 = 4507379) B4507379
theorem B11410469 : Blo 1334986 11410469 := bstep (se 4 (by rfl) ⟨1069731, by rfl⟩ : syracuseStep 11410469 = 2139463) B2139463
theorem B38542391 : Blo 1334986 38542391 := bstep (se 1 (by rfl) ⟨28906793, by rfl⟩ : syracuseStep 38542391 = 57813587) B57813587
theorem B2253359 : Blo 1334986 2253359 := bstep (se 1 (by rfl) ⟨1690019, by rfl⟩ : syracuseStep 2253359 = 3380039) B3380039
theorem B1336063 : Blo 1334986 1336063 := bstep (se 1 (by rfl) ⟨1002047, by rfl⟩ : syracuseStep 1336063 = 2004095) B2004095
theorem B1336255 : Blo 1334986 1336255 := bstep (se 1 (by rfl) ⟨1002191, by rfl⟩ : syracuseStep 1336255 = 2004383) B2004383
theorem B15418441 : Blo 1334986 15418441 := bstep (se 2 (by rfl) ⟨5781915, by rfl⟩ : syracuseStep 15418441 = 11563831) B11563831
theorem B2254135 : Blo 1334986 2254135 := bstep (se 1 (by rfl) ⟨1690601, by rfl⟩ : syracuseStep 2254135 = 3381203) B3381203
theorem B4507001 : Blo 1334986 4507001 := bstep (se 2 (by rfl) ⟨1690125, by rfl⟩ : syracuseStep 4507001 = 3380251) B3380251
theorem B1336815 : Blo 1334986 1336815 := bstep (se 1 (by rfl) ⟨1002611, by rfl⟩ : syracuseStep 1336815 = 2005223) B2005223
theorem B2853139 : Blo 1334986 2853139 := bstep (se 1 (by rfl) ⟨2139854, by rfl⟩ : syracuseStep 2853139 = 4279709) B4279709
theorem B7604563 : Blo 1334986 7604563 := bstep (se 1 (by rfl) ⟨5703422, by rfl⟩ : syracuseStep 7604563 = 11406845) B11406845
theorem B17132411 : Blo 1334986 17132411 := bstep (se 1 (by rfl) ⟨12849308, by rfl⟩ : syracuseStep 17132411 = 25698617) B25698617
theorem B2002553 : Blo 1334986 2002553 := bstep (se 2 (by rfl) ⟨750957, by rfl⟩ : syracuseStep 2002553 = 1501915) B1501915
theorem B54882355 : Blo 1334986 54882355 := bstep (se 1 (by rfl) ⟨41161766, by rfl⟩ : syracuseStep 54882355 = 82323533) B82323533
theorem B2003279 : Blo 1334986 2003279 := bstep (se 1 (by rfl) ⟨1502459, by rfl⟩ : syracuseStep 2003279 = 3004919) B3004919
theorem B7606979 : Blo 1334986 7606979 := bstep (se 1 (by rfl) ⟨5705234, by rfl⟩ : syracuseStep 7606979 = 11410469) B11410469
theorem B25694927 : Blo 1334986 25694927 := bstep (se 1 (by rfl) ⟨19271195, by rfl⟩ : syracuseStep 25694927 = 38542391) B38542391
theorem B4879079 : Blo 1334986 4879079 := bstep (se 1 (by rfl) ⟨3659309, by rfl⟩ : syracuseStep 4879079 = 7318619) B7318619
theorem B3380393 : Blo 1334986 3380393 := bstep (se 2 (by rfl) ⟨1267647, by rfl⟩ : syracuseStep 3380393 = 2535295) B2535295
theorem B15209855 : Blo 1334986 15209855 := bstep (se 1 (by rfl) ⟨11407391, by rfl⟩ : syracuseStep 15209855 = 22814783) B22814783
theorem B3380687 : Blo 1334986 3380687 := bstep (se 1 (by rfl) ⟨2535515, by rfl⟩ : syracuseStep 3380687 = 5071031) B5071031
theorem B2004521 : Blo 1334986 2004521 := bstep (se 2 (by rfl) ⟨751695, by rfl⟩ : syracuseStep 2004521 = 1503391) B1503391
theorem B2004905 : Blo 1334986 2004905 := bstep (se 2 (by rfl) ⟨751839, by rfl⟩ : syracuseStep 2004905 = 1503679) B1503679
theorem B2537831 : Blo 1334986 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B3005135 : Blo 1334986 3005135 := bstep (se 1 (by rfl) ⟨2253851, by rfl⟩ : syracuseStep 3005135 = 4507703) B4507703
theorem B1335519 : Blo 1334986 1335519 := bstep (se 1 (by rfl) ⟨1001639, by rfl⟩ : syracuseStep 1335519 = 2003279) B2003279
theorem B5071319 : Blo 1334986 5071319 := bstep (se 1 (by rfl) ⟨3803489, by rfl⟩ : syracuseStep 5071319 = 7606979) B7606979
theorem B17129951 : Blo 1334986 17129951 := bstep (se 1 (by rfl) ⟨12847463, by rfl⟩ : syracuseStep 17129951 = 25694927) B25694927
theorem B3252719 : Blo 1334986 3252719 := bstep (se 1 (by rfl) ⟨2439539, by rfl⟩ : syracuseStep 3252719 = 4879079) B4879079
theorem B2253595 : Blo 1334986 2253595 := bstep (se 1 (by rfl) ⟨1690196, by rfl⟩ : syracuseStep 2253595 = 3380393) B3380393
theorem B6767549 : Blo 1334986 6767549 := bstep (se 3 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 6767549 = 2537831) B2537831
theorem B2253791 : Blo 1334986 2253791 := bstep (se 1 (by rfl) ⟨1690343, by rfl⟩ : syracuseStep 2253791 = 3380687) B3380687
theorem B1336347 : Blo 1334986 1336347 := bstep (se 1 (by rfl) ⟨1002260, by rfl⟩ : syracuseStep 1336347 = 2004521) B2004521
theorem B1336603 : Blo 1334986 1336603 := bstep (se 1 (by rfl) ⟨1002452, by rfl⟩ : syracuseStep 1336603 = 2004905) B2004905
theorem B11421607 : Blo 1334986 11421607 := bstep (se 1 (by rfl) ⟨8566205, by rfl⟩ : syracuseStep 11421607 = 17132411) B17132411
theorem B3804185 : Blo 1334986 3804185 := bstep (se 2 (by rfl) ⟨1426569, by rfl⟩ : syracuseStep 3804185 = 2853139) B2853139
theorem B1502239 : Blo 1334986 1502239 := bstep (se 1 (by rfl) ⟨1126679, by rfl⟩ : syracuseStep 1502239 = 2253359) B2253359
theorem B20557921 : Blo 1334986 20557921 := bstep (se 2 (by rfl) ⟨7709220, by rfl⟩ : syracuseStep 20557921 = 15418441) B15418441
theorem B2003423 : Blo 1334986 2003423 := bstep (se 1 (by rfl) ⟨1502567, by rfl⟩ : syracuseStep 2003423 = 3005135) B3005135
theorem B73176473 : Blo 1334986 73176473 := bstep (se 2 (by rfl) ⟨27441177, by rfl⟩ : syracuseStep 73176473 = 54882355) B54882355
theorem B10139417 : Blo 1334986 10139417 := bstep (se 2 (by rfl) ⟨3802281, by rfl⟩ : syracuseStep 10139417 = 7604563) B7604563
theorem B3004667 : Blo 1334986 3004667 := bstep (se 1 (by rfl) ⟨2253500, by rfl⟩ : syracuseStep 3004667 = 4507001) B4507001
theorem B10139903 : Blo 1334986 10139903 := bstep (se 1 (by rfl) ⟨7604927, by rfl⟩ : syracuseStep 10139903 = 15209855) B15209855
theorem B3005513 : Blo 1334986 3005513 := bstep (se 2 (by rfl) ⟨1127067, by rfl⟩ : syracuseStep 3005513 = 2254135) B2254135
theorem B1335035 : Blo 1334986 1335035 := bstep (se 1 (by rfl) ⟨1001276, by rfl⟩ : syracuseStep 1335035 = 2002553) B2002553
theorem B27410561 : Blo 1334986 27410561 := bstep (se 2 (by rfl) ⟨10278960, by rfl⟩ : syracuseStep 27410561 = 20557921) B20557921
theorem B1335615 : Blo 1334986 1335615 := bstep (se 1 (by rfl) ⟨1001711, by rfl⟩ : syracuseStep 1335615 = 2003423) B2003423
theorem B11419967 : Blo 1334986 11419967 := bstep (se 1 (by rfl) ⟨8564975, by rfl⟩ : syracuseStep 11419967 = 17129951) B17129951
theorem B48784315 : Blo 1334986 48784315 := bstep (se 1 (by rfl) ⟨36588236, by rfl⟩ : syracuseStep 48784315 = 73176473) B73176473
theorem B6759611 : Blo 1334986 6759611 := bstep (se 1 (by rfl) ⟨5069708, by rfl⟩ : syracuseStep 6759611 = 10139417) B10139417
theorem B6759935 : Blo 1334986 6759935 := bstep (se 1 (by rfl) ⟨5069951, by rfl⟩ : syracuseStep 6759935 = 10139903) B10139903
theorem B1502527 : Blo 1334986 1502527 := bstep (se 1 (by rfl) ⟨1126895, by rfl⟩ : syracuseStep 1502527 = 2253791) B2253791
theorem B2002985 : Blo 1334986 2002985 := bstep (se 2 (by rfl) ⟨751119, by rfl⟩ : syracuseStep 2002985 = 1502239) B1502239
theorem B2003111 : Blo 1334986 2003111 := bstep (se 1 (by rfl) ⟨1502333, by rfl⟩ : syracuseStep 2003111 = 3004667) B3004667
theorem B2536123 : Blo 1334986 2536123 := bstep (se 1 (by rfl) ⟨1902092, by rfl⟩ : syracuseStep 2536123 = 3804185) B3804185
theorem B2003675 : Blo 1334986 2003675 := bstep (se 1 (by rfl) ⟨1502756, by rfl⟩ : syracuseStep 2003675 = 3005513) B3005513
theorem B3380879 : Blo 1334986 3380879 := bstep (se 1 (by rfl) ⟨2535659, by rfl⟩ : syracuseStep 3380879 = 5071319) B5071319
theorem B2168479 : Blo 1334986 2168479 := bstep (se 1 (by rfl) ⟨1626359, by rfl⟩ : syracuseStep 2168479 = 3252719) B3252719
theorem B4511699 : Blo 1334986 4511699 := bstep (se 1 (by rfl) ⟨3383774, by rfl⟩ : syracuseStep 4511699 = 6767549) B6767549
theorem B3004793 : Blo 1334986 3004793 := bstep (se 2 (by rfl) ⟨1126797, by rfl⟩ : syracuseStep 3004793 = 2253595) B2253595
theorem B15228809 : Blo 1334986 15228809 := bstep (se 2 (by rfl) ⟨5710803, by rfl⟩ : syracuseStep 15228809 = 11421607) B11421607
theorem B1335323 : Blo 1334986 1335323 := bstep (se 1 (by rfl) ⟨1001492, by rfl⟩ : syracuseStep 1335323 = 2002985) B2002985
theorem B1335407 : Blo 1334986 1335407 := bstep (se 1 (by rfl) ⟨1001555, by rfl⟩ : syracuseStep 1335407 = 2003111) B2003111
theorem B1335783 : Blo 1334986 1335783 := bstep (se 1 (by rfl) ⟨1001837, by rfl⟩ : syracuseStep 1335783 = 2003675) B2003675
theorem B4506407 : Blo 1334986 4506407 := bstep (se 1 (by rfl) ⟨3379805, by rfl⟩ : syracuseStep 4506407 = 6759611) B6759611
theorem B4506623 : Blo 1334986 4506623 := bstep (se 1 (by rfl) ⟨3379967, by rfl⟩ : syracuseStep 4506623 = 6759935) B6759935
theorem B2253919 : Blo 1334986 2253919 := bstep (se 1 (by rfl) ⟨1690439, by rfl⟩ : syracuseStep 2253919 = 3380879) B3380879
theorem B65045753 : Blo 1334986 65045753 := bstep (se 2 (by rfl) ⟨24392157, by rfl⟩ : syracuseStep 65045753 = 48784315) B48784315
theorem B3007799 : Blo 1334986 3007799 := bstep (se 1 (by rfl) ⟨2255849, by rfl⟩ : syracuseStep 3007799 = 4511699) B4511699
theorem B10152539 : Blo 1334986 10152539 := bstep (se 1 (by rfl) ⟨7614404, by rfl⟩ : syracuseStep 10152539 = 15228809) B15228809
theorem B7613311 : Blo 1334986 7613311 := bstep (se 1 (by rfl) ⟨5709983, by rfl⟩ : syracuseStep 7613311 = 11419967) B11419967
theorem B2003195 : Blo 1334986 2003195 := bstep (se 1 (by rfl) ⟨1502396, by rfl⟩ : syracuseStep 2003195 = 3004793) B3004793
theorem B2003369 : Blo 1334986 2003369 := bstep (se 2 (by rfl) ⟨751263, by rfl⟩ : syracuseStep 2003369 = 1502527) B1502527
theorem B18273707 : Blo 1334986 18273707 := bstep (se 1 (by rfl) ⟨13705280, by rfl⟩ : syracuseStep 18273707 = 27410561) B27410561
theorem B3381497 : Blo 1334986 3381497 := bstep (se 2 (by rfl) ⟨1268061, by rfl⟩ : syracuseStep 3381497 = 2536123) B2536123
theorem B2891305 : Blo 1334986 2891305 := bstep (se 2 (by rfl) ⟨1084239, by rfl⟩ : syracuseStep 2891305 = 2168479) B2168479
theorem B1335463 : Blo 1334986 1335463 := bstep (se 1 (by rfl) ⟨1001597, by rfl⟩ : syracuseStep 1335463 = 2003195) B2003195
theorem B1335579 : Blo 1334986 1335579 := bstep (se 1 (by rfl) ⟨1001684, by rfl⟩ : syracuseStep 1335579 = 2003369) B2003369
theorem B12182471 : Blo 1334986 12182471 := bstep (se 1 (by rfl) ⟨9136853, by rfl⟩ : syracuseStep 12182471 = 18273707) B18273707
theorem B10151081 : Blo 1334986 10151081 := bstep (se 2 (by rfl) ⟨3806655, by rfl⟩ : syracuseStep 10151081 = 7613311) B7613311
theorem B2254331 : Blo 1334986 2254331 := bstep (se 1 (by rfl) ⟨1690748, by rfl⟩ : syracuseStep 2254331 = 3381497) B3381497
theorem B6768359 : Blo 1334986 6768359 := bstep (se 1 (by rfl) ⟨5076269, by rfl⟩ : syracuseStep 6768359 = 10152539) B10152539
theorem B15420293 : Blo 1334986 15420293 := bstep (se 4 (by rfl) ⟨1445652, by rfl⟩ : syracuseStep 15420293 = 2891305) B2891305
theorem B43363835 : Blo 1334986 43363835 := bstep (se 1 (by rfl) ⟨32522876, by rfl⟩ : syracuseStep 43363835 = 65045753) B65045753
theorem B3004271 : Blo 1334986 3004271 := bstep (se 1 (by rfl) ⟨2253203, by rfl⟩ : syracuseStep 3004271 = 4506407) B4506407
theorem B3004415 : Blo 1334986 3004415 := bstep (se 1 (by rfl) ⟨2253311, by rfl⟩ : syracuseStep 3004415 = 4506623) B4506623
theorem B2005199 : Blo 1334986 2005199 := bstep (se 1 (by rfl) ⟨1503899, by rfl⟩ : syracuseStep 2005199 = 3007799) B3007799
theorem B3005225 : Blo 1334986 3005225 := bstep (se 2 (by rfl) ⟨1126959, by rfl⟩ : syracuseStep 3005225 = 2253919) B2253919
theorem B6767387 : Blo 1334986 6767387 := bstep (se 1 (by rfl) ⟨5075540, by rfl⟩ : syracuseStep 6767387 = 10151081) B10151081
theorem B1336799 : Blo 1334986 1336799 := bstep (se 1 (by rfl) ⟨1002599, by rfl⟩ : syracuseStep 1336799 = 2005199) B2005199
theorem B8121647 : Blo 1334986 8121647 := bstep (se 1 (by rfl) ⟨6091235, by rfl⟩ : syracuseStep 8121647 = 12182471) B12182471
theorem B1502887 : Blo 1334986 1502887 := bstep (se 1 (by rfl) ⟨1127165, by rfl⟩ : syracuseStep 1502887 = 2254331) B2254331
theorem B2002847 : Blo 1334986 2002847 := bstep (se 1 (by rfl) ⟨1502135, by rfl⟩ : syracuseStep 2002847 = 3004271) B3004271
theorem B2002943 : Blo 1334986 2002943 := bstep (se 1 (by rfl) ⟨1502207, by rfl⟩ : syracuseStep 2002943 = 3004415) B3004415
theorem B2003483 : Blo 1334986 2003483 := bstep (se 1 (by rfl) ⟨1502612, by rfl⟩ : syracuseStep 2003483 = 3005225) B3005225
theorem B4512239 : Blo 1334986 4512239 := bstep (se 1 (by rfl) ⟨3384179, by rfl⟩ : syracuseStep 4512239 = 6768359) B6768359
theorem B10280195 : Blo 1334986 10280195 := bstep (se 1 (by rfl) ⟨7710146, by rfl⟩ : syracuseStep 10280195 = 15420293) B15420293
theorem B28909223 : Blo 1334986 28909223 := bstep (se 1 (by rfl) ⟨21681917, by rfl⟩ : syracuseStep 28909223 = 43363835) B43363835
theorem B1335655 : Blo 1334986 1335655 := bstep (se 1 (by rfl) ⟨1001741, by rfl⟩ : syracuseStep 1335655 = 2003483) B2003483
theorem B3008159 : Blo 1334986 3008159 := bstep (se 1 (by rfl) ⟨2256119, by rfl⟩ : syracuseStep 3008159 = 4512239) B4512239
theorem B6853463 : Blo 1334986 6853463 := bstep (se 1 (by rfl) ⟨5140097, by rfl⟩ : syracuseStep 6853463 = 10280195) B10280195
theorem B2003849 : Blo 1334986 2003849 := bstep (se 2 (by rfl) ⟨751443, by rfl⟩ : syracuseStep 2003849 = 1502887) B1502887
theorem B19272815 : Blo 1334986 19272815 := bstep (se 1 (by rfl) ⟨14454611, by rfl⟩ : syracuseStep 19272815 = 28909223) B28909223
theorem B4511591 : Blo 1334986 4511591 := bstep (se 1 (by rfl) ⟨3383693, by rfl⟩ : syracuseStep 4511591 = 6767387) B6767387
theorem B21657725 : Blo 1334986 21657725 := bstep (se 3 (by rfl) ⟨4060823, by rfl⟩ : syracuseStep 21657725 = 8121647) B8121647
theorem B1335231 : Blo 1334986 1335231 := bstep (se 1 (by rfl) ⟨1001423, by rfl⟩ : syracuseStep 1335231 = 2002847) B2002847
theorem B1335295 : Blo 1334986 1335295 := bstep (se 1 (by rfl) ⟨1001471, by rfl⟩ : syracuseStep 1335295 = 2002943) B2002943
theorem B1335899 : Blo 1334986 1335899 := bstep (se 1 (by rfl) ⟨1001924, by rfl⟩ : syracuseStep 1335899 = 2003849) B2003849
theorem B3007727 : Blo 1334986 3007727 := bstep (se 1 (by rfl) ⟨2255795, by rfl⟩ : syracuseStep 3007727 = 4511591) B4511591
theorem B12848543 : Blo 1334986 12848543 := bstep (se 1 (by rfl) ⟨9636407, by rfl⟩ : syracuseStep 12848543 = 19272815) B19272815
theorem B14438483 : Blo 1334986 14438483 := bstep (se 1 (by rfl) ⟨10828862, by rfl⟩ : syracuseStep 14438483 = 21657725) B21657725
theorem B4568975 : Blo 1334986 4568975 := bstep (se 1 (by rfl) ⟨3426731, by rfl⟩ : syracuseStep 4568975 = 6853463) B6853463
theorem B2005439 : Blo 1334986 2005439 := bstep (se 1 (by rfl) ⟨1504079, by rfl⟩ : syracuseStep 2005439 = 3008159) B3008159
theorem B9625655 : Blo 1334986 9625655 := bstep (se 1 (by rfl) ⟨7219241, by rfl⟩ : syracuseStep 9625655 = 14438483) B14438483
theorem B1336959 : Blo 1334986 1336959 := bstep (se 1 (by rfl) ⟨1002719, by rfl⟩ : syracuseStep 1336959 = 2005439) B2005439
theorem B8565695 : Blo 1334986 8565695 := bstep (se 1 (by rfl) ⟨6424271, by rfl⟩ : syracuseStep 8565695 = 12848543) B12848543
theorem B2005151 : Blo 1334986 2005151 := bstep (se 1 (by rfl) ⟨1503863, by rfl⟩ : syracuseStep 2005151 = 3007727) B3007727
theorem B3045983 : Blo 1334986 3045983 := bstep (se 1 (by rfl) ⟨2284487, by rfl⟩ : syracuseStep 3045983 = 4568975) B4568975
theorem B5710463 : Blo 1334986 5710463 := bstep (se 1 (by rfl) ⟨4282847, by rfl⟩ : syracuseStep 5710463 = 8565695) B8565695
theorem B1336767 : Blo 1334986 1336767 := bstep (se 1 (by rfl) ⟨1002575, by rfl⟩ : syracuseStep 1336767 = 2005151) B2005151
theorem B6417103 : Blo 1334986 6417103 := bstep (se 1 (by rfl) ⟨4812827, by rfl⟩ : syracuseStep 6417103 = 9625655) B9625655
theorem B8122621 : Blo 1334986 8122621 := bstep (se 3 (by rfl) ⟨1522991, by rfl⟩ : syracuseStep 8122621 = 3045983) B3045983
theorem B10830161 : Blo 1334986 10830161 := bstep (se 2 (by rfl) ⟨4061310, by rfl⟩ : syracuseStep 10830161 = 8122621) B8122621
theorem B8556137 : Blo 1334986 8556137 := bstep (se 2 (by rfl) ⟨3208551, by rfl⟩ : syracuseStep 8556137 = 6417103) B6417103
theorem B3806975 : Blo 1334986 3806975 := bstep (se 1 (by rfl) ⟨2855231, by rfl⟩ : syracuseStep 3806975 = 5710463) B5710463
theorem B5704091 : Blo 1334986 5704091 := bstep (se 1 (by rfl) ⟨4278068, by rfl⟩ : syracuseStep 5704091 = 8556137) B8556137
theorem B7220107 : Blo 1334986 7220107 := bstep (se 1 (by rfl) ⟨5415080, by rfl⟩ : syracuseStep 7220107 = 10830161) B10830161
theorem B2537983 : Blo 1334986 2537983 := bstep (se 1 (by rfl) ⟨1903487, by rfl⟩ : syracuseStep 2537983 = 3806975) B3806975
theorem B3383977 : Blo 1334986 3383977 := bstep (se 2 (by rfl) ⟨1268991, by rfl⟩ : syracuseStep 3383977 = 2537983) B2537983
theorem B9626809 : Blo 1334986 9626809 := bstep (se 2 (by rfl) ⟨3610053, by rfl⟩ : syracuseStep 9626809 = 7220107) B7220107
theorem B3802727 : Blo 1334986 3802727 := bstep (se 1 (by rfl) ⟨2852045, by rfl⟩ : syracuseStep 3802727 = 5704091) B5704091
theorem B2535151 : Blo 1334986 2535151 := bstep (se 1 (by rfl) ⟨1901363, by rfl⟩ : syracuseStep 2535151 = 3802727) B3802727
theorem B4511969 : Blo 1334986 4511969 := bstep (se 2 (by rfl) ⟨1691988, by rfl⟩ : syracuseStep 4511969 = 3383977) B3383977
theorem B12835745 : Blo 1334986 12835745 := bstep (se 2 (by rfl) ⟨4813404, by rfl⟩ : syracuseStep 12835745 = 9626809) B9626809
theorem B3007979 : Blo 1334986 3007979 := bstep (se 1 (by rfl) ⟨2255984, by rfl⟩ : syracuseStep 3007979 = 4511969) B4511969
theorem B8557163 : Blo 1334986 8557163 := bstep (se 1 (by rfl) ⟨6417872, by rfl⟩ : syracuseStep 8557163 = 12835745) B12835745
theorem B3380201 : Blo 1334986 3380201 := bstep (se 2 (by rfl) ⟨1267575, by rfl⟩ : syracuseStep 3380201 = 2535151) B2535151
theorem B2253467 : Blo 1334986 2253467 := bstep (se 1 (by rfl) ⟨1690100, by rfl⟩ : syracuseStep 2253467 = 3380201) B3380201
theorem B5704775 : Blo 1334986 5704775 := bstep (se 1 (by rfl) ⟨4278581, by rfl⟩ : syracuseStep 5704775 = 8557163) B8557163
theorem B2005319 : Blo 1334986 2005319 := bstep (se 1 (by rfl) ⟨1503989, by rfl⟩ : syracuseStep 2005319 = 3007979) B3007979
theorem B1336879 : Blo 1334986 1336879 := bstep (se 1 (by rfl) ⟨1002659, by rfl⟩ : syracuseStep 1336879 = 2005319) B2005319
theorem B3803183 : Blo 1334986 3803183 := bstep (se 1 (by rfl) ⟨2852387, by rfl⟩ : syracuseStep 3803183 = 5704775) B5704775
theorem B1502311 : Blo 1334986 1502311 := bstep (se 1 (by rfl) ⟨1126733, by rfl⟩ : syracuseStep 1502311 = 2253467) B2253467
theorem B2535455 : Blo 1334986 2535455 := bstep (se 1 (by rfl) ⟨1901591, by rfl⟩ : syracuseStep 2535455 = 3803183) B3803183
theorem B2003081 : Blo 1334986 2003081 := bstep (se 2 (by rfl) ⟨751155, by rfl⟩ : syracuseStep 2003081 = 1502311) B1502311
theorem B1335387 : Blo 1334986 1335387 := bstep (se 1 (by rfl) ⟨1001540, by rfl⟩ : syracuseStep 1335387 = 2003081) B2003081
theorem B1690303 : Blo 1334986 1690303 := bstep (se 1 (by rfl) ⟨1267727, by rfl⟩ : syracuseStep 1690303 = 2535455) B2535455
theorem B2253737 : Blo 1334986 2253737 := bstep (se 2 (by rfl) ⟨845151, by rfl⟩ : syracuseStep 2253737 = 1690303) B1690303
theorem B1502491 : Blo 1334986 1502491 := bstep (se 1 (by rfl) ⟨1126868, by rfl⟩ : syracuseStep 1502491 = 2253737) B2253737
theorem B2003321 : Blo 1334986 2003321 := bstep (se 2 (by rfl) ⟨751245, by rfl⟩ : syracuseStep 2003321 = 1502491) B1502491
theorem B1335547 : Blo 1334986 1335547 := bstep (se 1 (by rfl) ⟨1001660, by rfl⟩ : syracuseStep 1335547 = 2003321) B2003321

theorem C0 (j : ℕ) (h1 : 333746 ≤ j) (h2 : j ≤ 334245) : Blo 1334986 (4 * j + 3) := by
  interval_cases j
  · exact B1334987
  · exact B1334991
  · exact B1334995
  · exact B1334999
  · exact B1335003
  · exact B1335007
  · exact B1335011
  · exact B1335015
  · exact B1335019
  · exact B1335023
  · exact B1335027
  · exact B1335031
  · exact B1335035
  · exact B1335039
  · exact B1335043
  · exact B1335047
  · exact B1335051
  · exact B1335055
  · exact B1335059
  · exact B1335063
  · exact B1335067
  · exact B1335071
  · exact B1335075
  · exact B1335079
  · exact B1335083
  · exact B1335087
  · exact B1335091
  · exact B1335095
  · exact B1335099
  · exact B1335103
  · exact B1335107
  · exact B1335111
  · exact B1335115
  · exact B1335119
  · exact B1335123
  · exact B1335127
  · exact B1335131
  · exact B1335135
  · exact B1335139
  · exact B1335143
  · exact B1335147
  · exact B1335151
  · exact B1335155
  · exact B1335159
  · exact B1335163
  · exact B1335167
  · exact B1335171
  · exact B1335175
  · exact B1335179
  · exact B1335183
  · exact B1335187
  · exact B1335191
  · exact B1335195
  · exact B1335199
  · exact B1335203
  · exact B1335207
  · exact B1335211
  · exact B1335215
  · exact B1335219
  · exact B1335223
  · exact B1335227
  · exact B1335231
  · exact B1335235
  · exact B1335239
  · exact B1335243
  · exact B1335247
  · exact B1335251
  · exact B1335255
  · exact B1335259
  · exact B1335263
  · exact B1335267
  · exact B1335271
  · exact B1335275
  · exact B1335279
  · exact B1335283
  · exact B1335287
  · exact B1335291
  · exact B1335295
  · exact B1335299
  · exact B1335303
  · exact B1335307
  · exact B1335311
  · exact B1335315
  · exact B1335319
  · exact B1335323
  · exact B1335327
  · exact B1335331
  · exact B1335335
  · exact B1335339
  · exact B1335343
  · exact B1335347
  · exact B1335351
  · exact B1335355
  · exact B1335359
  · exact B1335363
  · exact B1335367
  · exact B1335371
  · exact B1335375
  · exact B1335379
  · exact B1335383
  · exact B1335387
  · exact B1335391
  · exact B1335395
  · exact B1335399
  · exact B1335403
  · exact B1335407
  · exact B1335411
  · exact B1335415
  · exact B1335419
  · exact B1335423
  · exact B1335427
  · exact B1335431
  · exact B1335435
  · exact B1335439
  · exact B1335443
  · exact B1335447
  · exact B1335451
  · exact B1335455
  · exact B1335459
  · exact B1335463
  · exact B1335467
  · exact B1335471
  · exact B1335475
  · exact B1335479
  · exact B1335483
  · exact B1335487
  · exact B1335491
  · exact B1335495
  · exact B1335499
  · exact B1335503
  · exact B1335507
  · exact B1335511
  · exact B1335515
  · exact B1335519
  · exact B1335523
  · exact B1335527
  · exact B1335531
  · exact B1335535
  · exact B1335539
  · exact B1335543
  · exact B1335547
  · exact B1335551
  · exact B1335555
  · exact B1335559
  · exact B1335563
  · exact B1335567
  · exact B1335571
  · exact B1335575
  · exact B1335579
  · exact B1335583
  · exact B1335587
  · exact B1335591
  · exact B1335595
  · exact B1335599
  · exact B1335603
  · exact B1335607
  · exact B1335611
  · exact B1335615
  · exact B1335619
  · exact B1335623
  · exact B1335627
  · exact B1335631
  · exact B1335635
  · exact B1335639
  · exact B1335643
  · exact B1335647
  · exact B1335651
  · exact B1335655
  · exact B1335659
  · exact B1335663
  · exact B1335667
  · exact B1335671
  · exact B1335675
  · exact B1335679
  · exact B1335683
  · exact B1335687
  · exact B1335691
  · exact B1335695
  · exact B1335699
  · exact B1335703
  · exact B1335707
  · exact B1335711
  · exact B1335715
  · exact B1335719
  · exact B1335723
  · exact B1335727
  · exact B1335731
  · exact B1335735
  · exact B1335739
  · exact B1335743
  · exact B1335747
  · exact B1335751
  · exact B1335755
  · exact B1335759
  · exact B1335763
  · exact B1335767
  · exact B1335771
  · exact B1335775
  · exact B1335779
  · exact B1335783
  · exact B1335787
  · exact B1335791
  · exact B1335795
  · exact B1335799
  · exact B1335803
  · exact B1335807
  · exact B1335811
  · exact B1335815
  · exact B1335819
  · exact B1335823
  · exact B1335827
  · exact B1335831
  · exact B1335835
  · exact B1335839
  · exact B1335843
  · exact B1335847
  · exact B1335851
  · exact B1335855
  · exact B1335859
  · exact B1335863
  · exact B1335867
  · exact B1335871
  · exact B1335875
  · exact B1335879
  · exact B1335883
  · exact B1335887
  · exact B1335891
  · exact B1335895
  · exact B1335899
  · exact B1335903
  · exact B1335907
  · exact B1335911
  · exact B1335915
  · exact B1335919
  · exact B1335923
  · exact B1335927
  · exact B1335931
  · exact B1335935
  · exact B1335939
  · exact B1335943
  · exact B1335947
  · exact B1335951
  · exact B1335955
  · exact B1335959
  · exact B1335963
  · exact B1335967
  · exact B1335971
  · exact B1335975
  · exact B1335979
  · exact B1335983
  · exact B1335987
  · exact B1335991
  · exact B1335995
  · exact B1335999
  · exact B1336003
  · exact B1336007
  · exact B1336011
  · exact B1336015
  · exact B1336019
  · exact B1336023
  · exact B1336027
  · exact B1336031
  · exact B1336035
  · exact B1336039
  · exact B1336043
  · exact B1336047
  · exact B1336051
  · exact B1336055
  · exact B1336059
  · exact B1336063
  · exact B1336067
  · exact B1336071
  · exact B1336075
  · exact B1336079
  · exact B1336083
  · exact B1336087
  · exact B1336091
  · exact B1336095
  · exact B1336099
  · exact B1336103
  · exact B1336107
  · exact B1336111
  · exact B1336115
  · exact B1336119
  · exact B1336123
  · exact B1336127
  · exact B1336131
  · exact B1336135
  · exact B1336139
  · exact B1336143
  · exact B1336147
  · exact B1336151
  · exact B1336155
  · exact B1336159
  · exact B1336163
  · exact B1336167
  · exact B1336171
  · exact B1336175
  · exact B1336179
  · exact B1336183
  · exact B1336187
  · exact B1336191
  · exact B1336195
  · exact B1336199
  · exact B1336203
  · exact B1336207
  · exact B1336211
  · exact B1336215
  · exact B1336219
  · exact B1336223
  · exact B1336227
  · exact B1336231
  · exact B1336235
  · exact B1336239
  · exact B1336243
  · exact B1336247
  · exact B1336251
  · exact B1336255
  · exact B1336259
  · exact B1336263
  · exact B1336267
  · exact B1336271
  · exact B1336275
  · exact B1336279
  · exact B1336283
  · exact B1336287
  · exact B1336291
  · exact B1336295
  · exact B1336299
  · exact B1336303
  · exact B1336307
  · exact B1336311
  · exact B1336315
  · exact B1336319
  · exact B1336323
  · exact B1336327
  · exact B1336331
  · exact B1336335
  · exact B1336339
  · exact B1336343
  · exact B1336347
  · exact B1336351
  · exact B1336355
  · exact B1336359
  · exact B1336363
  · exact B1336367
  · exact B1336371
  · exact B1336375
  · exact B1336379
  · exact B1336383
  · exact B1336387
  · exact B1336391
  · exact B1336395
  · exact B1336399
  · exact B1336403
  · exact B1336407
  · exact B1336411
  · exact B1336415
  · exact B1336419
  · exact B1336423
  · exact B1336427
  · exact B1336431
  · exact B1336435
  · exact B1336439
  · exact B1336443
  · exact B1336447
  · exact B1336451
  · exact B1336455
  · exact B1336459
  · exact B1336463
  · exact B1336467
  · exact B1336471
  · exact B1336475
  · exact B1336479
  · exact B1336483
  · exact B1336487
  · exact B1336491
  · exact B1336495
  · exact B1336499
  · exact B1336503
  · exact B1336507
  · exact B1336511
  · exact B1336515
  · exact B1336519
  · exact B1336523
  · exact B1336527
  · exact B1336531
  · exact B1336535
  · exact B1336539
  · exact B1336543
  · exact B1336547
  · exact B1336551
  · exact B1336555
  · exact B1336559
  · exact B1336563
  · exact B1336567
  · exact B1336571
  · exact B1336575
  · exact B1336579
  · exact B1336583
  · exact B1336587
  · exact B1336591
  · exact B1336595
  · exact B1336599
  · exact B1336603
  · exact B1336607
  · exact B1336611
  · exact B1336615
  · exact B1336619
  · exact B1336623
  · exact B1336627
  · exact B1336631
  · exact B1336635
  · exact B1336639
  · exact B1336643
  · exact B1336647
  · exact B1336651
  · exact B1336655
  · exact B1336659
  · exact B1336663
  · exact B1336667
  · exact B1336671
  · exact B1336675
  · exact B1336679
  · exact B1336683
  · exact B1336687
  · exact B1336691
  · exact B1336695
  · exact B1336699
  · exact B1336703
  · exact B1336707
  · exact B1336711
  · exact B1336715
  · exact B1336719
  · exact B1336723
  · exact B1336727
  · exact B1336731
  · exact B1336735
  · exact B1336739
  · exact B1336743
  · exact B1336747
  · exact B1336751
  · exact B1336755
  · exact B1336759
  · exact B1336763
  · exact B1336767
  · exact B1336771
  · exact B1336775
  · exact B1336779
  · exact B1336783
  · exact B1336787
  · exact B1336791
  · exact B1336795
  · exact B1336799
  · exact B1336803
  · exact B1336807
  · exact B1336811
  · exact B1336815
  · exact B1336819
  · exact B1336823
  · exact B1336827
  · exact B1336831
  · exact B1336835
  · exact B1336839
  · exact B1336843
  · exact B1336847
  · exact B1336851
  · exact B1336855
  · exact B1336859
  · exact B1336863
  · exact B1336867
  · exact B1336871
  · exact B1336875
  · exact B1336879
  · exact B1336883
  · exact B1336887
  · exact B1336891
  · exact B1336895
  · exact B1336899
  · exact B1336903
  · exact B1336907
  · exact B1336911
  · exact B1336915
  · exact B1336919
  · exact B1336923
  · exact B1336927
  · exact B1336931
  · exact B1336935
  · exact B1336939
  · exact B1336943
  · exact B1336947
  · exact B1336951
  · exact B1336955
  · exact B1336959
  · exact B1336963
  · exact B1336967
  · exact B1336971
  · exact B1336975
  · exact B1336979
  · exact B1336983

theorem solution (m : ℕ) (hlo : 1334986 ≤ m) (hhi : m ≤ 1336986) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 333746 ≤ j := by omega
    have hj2 : j ≤ 334245 := by omega
    have hb : Blo 1334986 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
