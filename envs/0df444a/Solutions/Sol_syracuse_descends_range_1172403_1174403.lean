-- Prove2me | solution 1 for syracuse_descends_range_1172403_1174403
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:23.068038+00:00
-- url     : https://prove2.me/submissions/82d704a1-95a2-4612-878f-52afae244f44

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


theorem B1761293 : Blo 1172403 1761293 := bbase (se 3 (by rfl) ⟨330242, by rfl⟩ : syracuseStep 1761293 = 660485) (by norm_num)
theorem B2506781 : Blo 1172403 2506781 := bbase (se 3 (by rfl) ⟨470021, by rfl⟩ : syracuseStep 2506781 = 940043) (by norm_num)
theorem B1761317 : Blo 1172403 1761317 := bbase (se 4 (by rfl) ⟨165123, by rfl⟩ : syracuseStep 1761317 = 330247) (by norm_num)
theorem B2113597 : Blo 1172403 2113597 := bbase (se 3 (by rfl) ⟨396299, by rfl⟩ : syracuseStep 2113597 = 792599) (by norm_num)
theorem B1761341 : Blo 1172403 1761341 := bbase (se 3 (by rfl) ⟨330251, by rfl⟩ : syracuseStep 1761341 = 660503) (by norm_num)
theorem B1318981 : Blo 1172403 1318981 := bbase (se 4 (by rfl) ⟨123654, by rfl⟩ : syracuseStep 1318981 = 247309) (by norm_num)
theorem B1761365 : Blo 1172403 1761365 := bbase (se 8 (by rfl) ⟨10320, by rfl⟩ : syracuseStep 1761365 = 20641) (by norm_num)
theorem B2637917 : Blo 1172403 2637917 := bbase (se 3 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 2637917 = 989219) (by norm_num)
theorem B1319017 : Blo 1172403 1319017 := bbase (se 2 (by rfl) ⟨494631, by rfl⟩ : syracuseStep 1319017 = 989263) (by norm_num)
theorem B1761389 : Blo 1172403 1761389 := bbase (se 3 (by rfl) ⟨330260, by rfl⟩ : syracuseStep 1761389 = 660521) (by norm_num)
theorem B1671301 : Blo 1172403 1671301 := bbase (se 4 (by rfl) ⟨156684, by rfl⟩ : syracuseStep 1671301 = 313369) (by norm_num)
theorem B1761413 : Blo 1172403 1761413 := bbase (se 4 (by rfl) ⟨165132, by rfl⟩ : syracuseStep 1761413 = 330265) (by norm_num)
theorem B1409161 : Blo 1172403 1409161 := bbase (se 2 (by rfl) ⟨528435, by rfl⟩ : syracuseStep 1409161 = 1056871) (by norm_num)
theorem B1319053 : Blo 1172403 1319053 := bbase (se 3 (by rfl) ⟨247322, by rfl⟩ : syracuseStep 1319053 = 494645) (by norm_num)
theorem B2113685 : Blo 1172403 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B1761437 : Blo 1172403 1761437 := bbase (se 3 (by rfl) ⟨330269, by rfl⟩ : syracuseStep 1761437 = 660539) (by norm_num)
theorem B2637989 : Blo 1172403 2637989 := bbase (se 4 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 2637989 = 494623) (by norm_num)
theorem B1319089 : Blo 1172403 1319089 := bbase (se 2 (by rfl) ⟨494658, by rfl⟩ : syracuseStep 1319089 = 989317) (by norm_num)
theorem B1761461 : Blo 1172403 1761461 := bbase (se 5 (by rfl) ⟨82568, by rfl⟩ : syracuseStep 1761461 = 165137) (by norm_num)
theorem B1253561 : Blo 1172403 1253561 := bbase (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) (by norm_num)
theorem B1761485 : Blo 1172403 1761485 := bbase (se 3 (by rfl) ⟨330278, by rfl⟩ : syracuseStep 1761485 = 660557) (by norm_num)
theorem B1319125 : Blo 1172403 1319125 := bbase (se 7 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 1319125 = 30917) (by norm_num)
theorem B2859229 : Blo 1172403 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B1761509 : Blo 1172403 1761509 := bbase (se 4 (by rfl) ⟨165141, by rfl⟩ : syracuseStep 1761509 = 330283) (by norm_num)
theorem B2638061 : Blo 1172403 2638061 := bbase (se 3 (by rfl) ⟨494636, by rfl⟩ : syracuseStep 2638061 = 989273) (by norm_num)
theorem B1319161 : Blo 1172403 1319161 := bbase (se 2 (by rfl) ⟨494685, by rfl⟩ : syracuseStep 1319161 = 989371) (by norm_num)
theorem B1761533 : Blo 1172403 1761533 := bbase (se 3 (by rfl) ⟨330287, by rfl⟩ : syracuseStep 1761533 = 660575) (by norm_num)
theorem B2228485 : Blo 1172403 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B1761557 : Blo 1172403 1761557 := bbase (se 6 (by rfl) ⟨41286, by rfl⟩ : syracuseStep 1761557 = 82573) (by norm_num)
theorem B1319197 : Blo 1172403 1319197 := bbase (se 3 (by rfl) ⟨247349, by rfl⟩ : syracuseStep 1319197 = 494699) (by norm_num)
theorem B4456741 : Blo 1172403 4456741 := bbase (se 4 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 4456741 = 835639) (by norm_num)
theorem B1761581 : Blo 1172403 1761581 := bbase (se 3 (by rfl) ⟨330296, by rfl⟩ : syracuseStep 1761581 = 660593) (by norm_num)
theorem B2638133 : Blo 1172403 2638133 := bbase (se 5 (by rfl) ⟨123662, by rfl⟩ : syracuseStep 2638133 = 247325) (by norm_num)
theorem B1319233 : Blo 1172403 1319233 := bbase (se 2 (by rfl) ⟨494712, by rfl⟩ : syracuseStep 1319233 = 989425) (by norm_num)
theorem B1270085 : Blo 1172403 1270085 := bbase (se 4 (by rfl) ⟨119070, by rfl⟩ : syracuseStep 1270085 = 238141) (by norm_num)
theorem B1761605 : Blo 1172403 1761605 := bbase (se 4 (by rfl) ⟨165150, by rfl⟩ : syracuseStep 1761605 = 330301) (by norm_num)
theorem B1319269 : Blo 1172403 1319269 := bbase (se 4 (by rfl) ⟨123681, by rfl⟩ : syracuseStep 1319269 = 247363) (by norm_num)
theorem B2638205 : Blo 1172403 2638205 := bbase (se 3 (by rfl) ⟨494663, by rfl⟩ : syracuseStep 2638205 = 989327) (by norm_num)
theorem B1319305 : Blo 1172403 1319305 := bbase (se 2 (by rfl) ⟨494739, by rfl⟩ : syracuseStep 1319305 = 989479) (by norm_num)
theorem B2228629 : Blo 1172403 2228629 := bbase (se 6 (by rfl) ⟨52233, by rfl⟩ : syracuseStep 2228629 = 104467) (by norm_num)
theorem B1319341 : Blo 1172403 1319341 := bbase (se 3 (by rfl) ⟨247376, by rfl⟩ : syracuseStep 1319341 = 494753) (by norm_num)
theorem B1253809 : Blo 1172403 1253809 := bbase (se 2 (by rfl) ⟨470178, by rfl⟩ : syracuseStep 1253809 = 940357) (by norm_num)
theorem B3957173 : Blo 1172403 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B2638277 : Blo 1172403 2638277 := bbase (se 4 (by rfl) ⟨247338, by rfl⟩ : syracuseStep 2638277 = 494677) (by norm_num)
theorem B1319377 : Blo 1172403 1319377 := bbase (se 2 (by rfl) ⟨494766, by rfl⟩ : syracuseStep 1319377 = 989533) (by norm_num)
theorem B8249813 : Blo 1172403 8249813 := bbase (se 7 (by rfl) ⟨96677, by rfl⟩ : syracuseStep 8249813 = 193355) (by norm_num)
theorem B1319413 : Blo 1172403 1319413 := bbase (se 5 (by rfl) ⟨61847, by rfl⟩ : syracuseStep 1319413 = 123695) (by norm_num)
theorem B2638349 : Blo 1172403 2638349 := bbase (se 3 (by rfl) ⟨494690, by rfl⟩ : syracuseStep 2638349 = 989381) (by norm_num)
theorem B1319449 : Blo 1172403 1319449 := bbase (se 2 (by rfl) ⟨494793, by rfl⟩ : syracuseStep 1319449 = 989587) (by norm_num)
theorem B2228789 : Blo 1172403 2228789 := bbase (se 5 (by rfl) ⟨104474, by rfl⟩ : syracuseStep 2228789 = 208949) (by norm_num)
theorem B1319485 : Blo 1172403 1319485 := bbase (se 3 (by rfl) ⟨247403, by rfl⟩ : syracuseStep 1319485 = 494807) (by norm_num)
theorem B2638421 : Blo 1172403 2638421 := bbase (se 8 (by rfl) ⟨15459, by rfl⟩ : syracuseStep 2638421 = 30919) (by norm_num)
theorem B4457045 : Blo 1172403 4457045 := bbase (se 8 (by rfl) ⟨26115, by rfl⟩ : syracuseStep 4457045 = 52231) (by norm_num)
theorem B1319521 : Blo 1172403 1319521 := bbase (se 2 (by rfl) ⟨494820, by rfl⟩ : syracuseStep 1319521 = 989641) (by norm_num)
theorem B10027637 : Blo 1172403 10027637 := bbase (se 5 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 10027637 = 940091) (by norm_num)
theorem B1319557 : Blo 1172403 1319557 := bbase (se 4 (by rfl) ⟨123708, by rfl⟩ : syracuseStep 1319557 = 247417) (by norm_num)
theorem B2114189 : Blo 1172403 2114189 := bbase (se 3 (by rfl) ⟨396410, by rfl⟩ : syracuseStep 2114189 = 792821) (by norm_num)
theorem B2638493 : Blo 1172403 2638493 := bbase (se 3 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 2638493 = 989435) (by norm_num)
theorem B1319593 : Blo 1172403 1319593 := bbase (se 2 (by rfl) ⟨494847, by rfl⟩ : syracuseStep 1319593 = 989695) (by norm_num)
theorem B2228933 : Blo 1172403 2228933 := bbase (se 4 (by rfl) ⟨208962, by rfl⟩ : syracuseStep 2228933 = 417925) (by norm_num)
theorem B1319629 : Blo 1172403 1319629 := bbase (se 3 (by rfl) ⟨247430, by rfl⟩ : syracuseStep 1319629 = 494861) (by norm_num)
theorem B2638565 : Blo 1172403 2638565 := bbase (se 4 (by rfl) ⟨247365, by rfl⟩ : syracuseStep 2638565 = 494731) (by norm_num)
theorem B1319665 : Blo 1172403 1319665 := bbase (se 2 (by rfl) ⟨494874, by rfl⟩ : syracuseStep 1319665 = 989749) (by norm_num)
theorem B1319701 : Blo 1172403 1319701 := bbase (se 6 (by rfl) ⟨30930, by rfl⟩ : syracuseStep 1319701 = 61861) (by norm_num)
theorem B2638637 : Blo 1172403 2638637 := bbase (se 3 (by rfl) ⟨494744, by rfl⟩ : syracuseStep 2638637 = 989489) (by norm_num)
theorem B1319737 : Blo 1172403 1319737 := bbase (se 2 (by rfl) ⟨494901, by rfl⟩ : syracuseStep 1319737 = 989803) (by norm_num)
theorem B5940053 : Blo 1172403 5940053 := bbase (se 9 (by rfl) ⟨17402, by rfl⟩ : syracuseStep 5940053 = 34805) (by norm_num)
theorem B1319773 : Blo 1172403 1319773 := bbase (se 3 (by rfl) ⟨247457, by rfl⟩ : syracuseStep 1319773 = 494915) (by norm_num)
theorem B3957605 : Blo 1172403 3957605 := bbase (se 4 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 3957605 = 742051) (by norm_num)
theorem B2638709 : Blo 1172403 2638709 := bbase (se 5 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 2638709 = 247379) (by norm_num)
theorem B1319809 : Blo 1172403 1319809 := bbase (se 2 (by rfl) ⟨494928, by rfl⟩ : syracuseStep 1319809 = 989857) (by norm_num)
theorem B1672093 : Blo 1172403 1672093 := bbase (se 3 (by rfl) ⟨313517, by rfl⟩ : syracuseStep 1672093 = 627035) (by norm_num)
theorem B1319845 : Blo 1172403 1319845 := bbase (se 4 (by rfl) ⟨123735, by rfl⟩ : syracuseStep 1319845 = 247471) (by norm_num)
theorem B7513013 : Blo 1172403 7513013 := bbase (se 5 (by rfl) ⟨352172, by rfl⟩ : syracuseStep 7513013 = 704345) (by norm_num)
theorem B3343285 : Blo 1172403 3343285 := bbase (se 5 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 3343285 = 313433) (by norm_num)
theorem B2638781 : Blo 1172403 2638781 := bbase (se 3 (by rfl) ⟨494771, by rfl⟩ : syracuseStep 2638781 = 989543) (by norm_num)
theorem B1319881 : Blo 1172403 1319881 := bbase (se 2 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 1319881 = 989911) (by norm_num)
theorem B12862421 : Blo 1172403 12862421 := bbase (se 7 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 12862421 = 301463) (by norm_num)
theorem B2229221 : Blo 1172403 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B1319917 : Blo 1172403 1319917 := bbase (se 3 (by rfl) ⟨247484, by rfl⟩ : syracuseStep 1319917 = 494969) (by norm_num)
theorem B2638853 : Blo 1172403 2638853 := bbase (se 4 (by rfl) ⟨247392, by rfl⟩ : syracuseStep 2638853 = 494785) (by norm_num)
theorem B1319953 : Blo 1172403 1319953 := bbase (se 2 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 1319953 = 989965) (by norm_num)
theorem B1319989 : Blo 1172403 1319989 := bbase (se 5 (by rfl) ⟨61874, by rfl⟩ : syracuseStep 1319989 = 123749) (by norm_num)
theorem B1483849 : Blo 1172403 1483849 := bbase (se 2 (by rfl) ⟨556443, by rfl⟩ : syracuseStep 1483849 = 1112887) (by norm_num)
theorem B2638925 : Blo 1172403 2638925 := bbase (se 3 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 2638925 = 989597) (by norm_num)
theorem B1320025 : Blo 1172403 1320025 := bbase (se 2 (by rfl) ⟨495009, by rfl⟩ : syracuseStep 1320025 = 990019) (by norm_num)
theorem B5637221 : Blo 1172403 5637221 := bbase (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) (by norm_num)
theorem B1320061 : Blo 1172403 1320061 := bbase (se 3 (by rfl) ⟨247511, by rfl⟩ : syracuseStep 1320061 = 495023) (by norm_num)
theorem B2229373 : Blo 1172403 2229373 := bbase (se 3 (by rfl) ⟨418007, by rfl⟩ : syracuseStep 2229373 = 836015) (by norm_num)
theorem B2638997 : Blo 1172403 2638997 := bbase (se 6 (by rfl) ⟨61851, by rfl⟩ : syracuseStep 2638997 = 123703) (by norm_num)
theorem B1320097 : Blo 1172403 1320097 := bbase (se 2 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 1320097 = 990073) (by norm_num)
theorem B2819245 : Blo 1172403 2819245 := bbase (se 3 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 2819245 = 1057217) (by norm_num)
theorem B6341813 : Blo 1172403 6341813 := bbase (se 5 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 6341813 = 594545) (by norm_num)
theorem B1320133 : Blo 1172403 1320133 := bbase (se 4 (by rfl) ⟨123762, by rfl⟩ : syracuseStep 1320133 = 247525) (by norm_num)
theorem B2639069 : Blo 1172403 2639069 := bbase (se 3 (by rfl) ⟨494825, by rfl⟩ : syracuseStep 2639069 = 989651) (by norm_num)
theorem B1320169 : Blo 1172403 1320169 := bbase (se 2 (by rfl) ⟨495063, by rfl⟩ : syracuseStep 1320169 = 990127) (by norm_num)
theorem B1484021 : Blo 1172403 1484021 := bbase (se 5 (by rfl) ⟨69563, by rfl⟩ : syracuseStep 1484021 = 139127) (by norm_num)
theorem B1320205 : Blo 1172403 1320205 := bbase (se 3 (by rfl) ⟨247538, by rfl⟩ : syracuseStep 1320205 = 495077) (by norm_num)
theorem B3958037 : Blo 1172403 3958037 := bbase (se 6 (by rfl) ⟨92766, by rfl⟩ : syracuseStep 3958037 = 185533) (by norm_num)
theorem B2639141 : Blo 1172403 2639141 := bbase (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) (by norm_num)
theorem B1484077 : Blo 1172403 1484077 := bbase (se 3 (by rfl) ⟨278264, by rfl⟩ : syracuseStep 1484077 = 556529) (by norm_num)
theorem B1320241 : Blo 1172403 1320241 := bbase (se 2 (by rfl) ⟨495090, by rfl⟩ : syracuseStep 1320241 = 990181) (by norm_num)
theorem B1320277 : Blo 1172403 1320277 := bbase (se 12 (by rfl) ⟨483, by rfl⟩ : syracuseStep 1320277 = 967) (by norm_num)
theorem B2639213 : Blo 1172403 2639213 := bbase (se 3 (by rfl) ⟨494852, by rfl⟩ : syracuseStep 2639213 = 989705) (by norm_num)
theorem B1320313 : Blo 1172403 1320313 := bbase (se 2 (by rfl) ⟨495117, by rfl⟩ : syracuseStep 1320313 = 990235) (by norm_num)
theorem B1484173 : Blo 1172403 1484173 := bbase (se 3 (by rfl) ⟨278282, by rfl⟩ : syracuseStep 1484173 = 556565) (by norm_num)
theorem B4760981 : Blo 1172403 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B1320349 : Blo 1172403 1320349 := bbase (se 3 (by rfl) ⟨247565, by rfl⟩ : syracuseStep 1320349 = 495131) (by norm_num)
theorem B2639285 : Blo 1172403 2639285 := bbase (se 5 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 2639285 = 247433) (by norm_num)
theorem B1320385 : Blo 1172403 1320385 := bbase (se 2 (by rfl) ⟨495144, by rfl⟩ : syracuseStep 1320385 = 990289) (by norm_num)
theorem B5014997 : Blo 1172403 5014997 := bbase (se 7 (by rfl) ⟨58769, by rfl⟩ : syracuseStep 5014997 = 117539) (by norm_num)
theorem B1320421 : Blo 1172403 1320421 := bbase (se 4 (by rfl) ⟨123789, by rfl⟩ : syracuseStep 1320421 = 247579) (by norm_num)
theorem B1410545 : Blo 1172403 1410545 := bbase (se 2 (by rfl) ⟨528954, by rfl⟩ : syracuseStep 1410545 = 1057909) (by norm_num)
theorem B2639357 : Blo 1172403 2639357 := bbase (se 3 (by rfl) ⟨494879, by rfl⟩ : syracuseStep 2639357 = 989759) (by norm_num)
theorem B1320457 : Blo 1172403 1320457 := bbase (se 2 (by rfl) ⟨495171, by rfl⟩ : syracuseStep 1320457 = 990343) (by norm_num)
theorem B1320493 : Blo 1172403 1320493 := bbase (se 3 (by rfl) ⟨247592, by rfl⟩ : syracuseStep 1320493 = 495185) (by norm_num)
theorem B1484345 : Blo 1172403 1484345 := bbase (se 2 (by rfl) ⟨556629, by rfl⟩ : syracuseStep 1484345 = 1113259) (by norm_num)
theorem B2639429 : Blo 1172403 2639429 := bbase (se 4 (by rfl) ⟨247446, by rfl⟩ : syracuseStep 2639429 = 494893) (by norm_num)
theorem B1320529 : Blo 1172403 1320529 := bbase (se 2 (by rfl) ⟨495198, by rfl⟩ : syracuseStep 1320529 = 990397) (by norm_num)
theorem B4761173 : Blo 1172403 4761173 := bbase (se 8 (by rfl) ⟨27897, by rfl⟩ : syracuseStep 4761173 = 55795) (by norm_num)
theorem B1484401 : Blo 1172403 1484401 := bbase (se 2 (by rfl) ⟨556650, by rfl⟩ : syracuseStep 1484401 = 1113301) (by norm_num)
theorem B1320565 : Blo 1172403 1320565 := bbase (se 5 (by rfl) ⟨61901, by rfl⟩ : syracuseStep 1320565 = 123803) (by norm_num)
theorem B2639501 : Blo 1172403 2639501 := bbase (se 3 (by rfl) ⟨494906, by rfl⟩ : syracuseStep 2639501 = 989813) (by norm_num)
theorem B1320601 : Blo 1172403 1320601 := bbase (se 2 (by rfl) ⟨495225, by rfl⟩ : syracuseStep 1320601 = 990451) (by norm_num)
theorem B2033333 : Blo 1172403 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B2819765 : Blo 1172403 2819765 := bbase (se 5 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 2819765 = 264353) (by norm_num)
theorem B1320637 : Blo 1172403 1320637 := bbase (se 3 (by rfl) ⟨247619, by rfl⟩ : syracuseStep 1320637 = 495239) (by norm_num)
theorem B3958469 : Blo 1172403 3958469 := bbase (se 4 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 3958469 = 742213) (by norm_num)
theorem B1484497 : Blo 1172403 1484497 := bbase (se 2 (by rfl) ⟨556686, by rfl⟩ : syracuseStep 1484497 = 1113373) (by norm_num)
theorem B2639573 : Blo 1172403 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B24094421 : Blo 1172403 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B2541277 : Blo 1172403 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B1320673 : Blo 1172403 1320673 := bbase (se 2 (by rfl) ⟨495252, by rfl⟩ : syracuseStep 1320673 = 990505) (by norm_num)
theorem B1410805 : Blo 1172403 1410805 := bbase (se 5 (by rfl) ⟨66131, by rfl⟩ : syracuseStep 1410805 = 132263) (by norm_num)
theorem B1320709 : Blo 1172403 1320709 := bbase (se 4 (by rfl) ⟨123816, by rfl⟩ : syracuseStep 1320709 = 247633) (by norm_num)
theorem B2639645 : Blo 1172403 2639645 := bbase (se 3 (by rfl) ⟨494933, by rfl⟩ : syracuseStep 2639645 = 989867) (by norm_num)
theorem B1410853 : Blo 1172403 1410853 := bbase (se 4 (by rfl) ⟨132267, by rfl⟩ : syracuseStep 1410853 = 264535) (by norm_num)
theorem B1320745 : Blo 1172403 1320745 := bbase (se 2 (by rfl) ⟨495279, by rfl⟩ : syracuseStep 1320745 = 990559) (by norm_num)
theorem B3008333 : Blo 1172403 3008333 := bbase (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) (by norm_num)
theorem B1320781 : Blo 1172403 1320781 := bbase (se 3 (by rfl) ⟨247646, by rfl⟩ : syracuseStep 1320781 = 495293) (by norm_num)
theorem B117253973 : Blo 1172403 117253973 := bbase (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) (by norm_num)
theorem B6686549 : Blo 1172403 6686549 := bbase (se 9 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 6686549 = 39179) (by norm_num)
theorem B2639717 : Blo 1172403 2639717 := bbase (se 4 (by rfl) ⟨247473, by rfl⟩ : syracuseStep 2639717 = 494947) (by norm_num)
theorem B1320817 : Blo 1172403 1320817 := bbase (se 2 (by rfl) ⟨495306, by rfl⟩ : syracuseStep 1320817 = 990613) (by norm_num)
theorem B3172213 : Blo 1172403 3172213 := bbase (se 5 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 3172213 = 297395) (by norm_num)
theorem B1484669 : Blo 1172403 1484669 := bbase (se 3 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 1484669 = 556751) (by norm_num)
theorem B3008405 : Blo 1172403 3008405 := bbase (se 6 (by rfl) ⟨70509, by rfl⟩ : syracuseStep 3008405 = 141019) (by norm_num)
theorem B1320853 : Blo 1172403 1320853 := bbase (se 6 (by rfl) ⟨30957, by rfl⟩ : syracuseStep 1320853 = 61915) (by norm_num)
theorem B2639789 : Blo 1172403 2639789 := bbase (se 3 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 2639789 = 989921) (by norm_num)
theorem B1484725 : Blo 1172403 1484725 := bbase (se 5 (by rfl) ⟨69596, by rfl⟩ : syracuseStep 1484725 = 139193) (by norm_num)
theorem B1320889 : Blo 1172403 1320889 := bbase (se 2 (by rfl) ⟨495333, by rfl⟩ : syracuseStep 1320889 = 990667) (by norm_num)
theorem B1320925 : Blo 1172403 1320925 := bbase (se 3 (by rfl) ⟨247673, by rfl⟩ : syracuseStep 1320925 = 495347) (by norm_num)
theorem B2639861 : Blo 1172403 2639861 := bbase (se 5 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 2639861 = 247487) (by norm_num)
theorem B1320961 : Blo 1172403 1320961 := bbase (se 2 (by rfl) ⟨495360, by rfl⟩ : syracuseStep 1320961 = 990721) (by norm_num)
theorem B1484821 : Blo 1172403 1484821 := bbase (se 6 (by rfl) ⟨34800, by rfl⟩ : syracuseStep 1484821 = 69601) (by norm_num)
theorem B1320997 : Blo 1172403 1320997 := bbase (se 4 (by rfl) ⟨123843, by rfl⟩ : syracuseStep 1320997 = 247687) (by norm_num)
theorem B1878061 : Blo 1172403 1878061 := bbase (se 3 (by rfl) ⟨352136, by rfl⟩ : syracuseStep 1878061 = 704273) (by norm_num)
theorem B1189933 : Blo 1172403 1189933 := bbase (se 3 (by rfl) ⟨223112, by rfl⟩ : syracuseStep 1189933 = 446225) (by norm_num)
theorem B1189937 : Blo 1172403 1189937 := bbase (se 2 (by rfl) ⟨446226, by rfl⟩ : syracuseStep 1189937 = 892453) (by norm_num)
theorem B2820149 : Blo 1172403 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B2639933 : Blo 1172403 2639933 := bbase (se 3 (by rfl) ⟨494987, by rfl⟩ : syracuseStep 2639933 = 989975) (by norm_num)
theorem B1321033 : Blo 1172403 1321033 := bbase (se 2 (by rfl) ⟨495387, by rfl⟩ : syracuseStep 1321033 = 990775) (by norm_num)
theorem B5941349 : Blo 1172403 5941349 := bbase (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) (by norm_num)
theorem B2820197 : Blo 1172403 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B2820205 : Blo 1172403 2820205 := bbase (se 3 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 2820205 = 1057577) (by norm_num)
theorem B1321069 : Blo 1172403 1321069 := bbase (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) (by norm_num)
theorem B3958901 : Blo 1172403 3958901 := bbase (se 5 (by rfl) ⟨185573, by rfl⟩ : syracuseStep 3958901 = 371147) (by norm_num)
theorem B2640005 : Blo 1172403 2640005 := bbase (se 4 (by rfl) ⟨247500, by rfl⟩ : syracuseStep 2640005 = 495001) (by norm_num)
theorem B1321105 : Blo 1172403 1321105 := bbase (se 2 (by rfl) ⟨495414, by rfl⟩ : syracuseStep 1321105 = 990829) (by norm_num)
theorem B1321141 : Blo 1172403 1321141 := bbase (se 5 (by rfl) ⟨61928, by rfl⟩ : syracuseStep 1321141 = 123857) (by norm_num)
theorem B1484993 : Blo 1172403 1484993 := bbase (se 2 (by rfl) ⟨556872, by rfl⟩ : syracuseStep 1484993 = 1113745) (by norm_num)
theorem B2967749 : Blo 1172403 2967749 := bbase (se 4 (by rfl) ⟨278226, by rfl⟩ : syracuseStep 2967749 = 556453) (by norm_num)
theorem B2640077 : Blo 1172403 2640077 := bbase (se 3 (by rfl) ⟨495014, by rfl⟩ : syracuseStep 2640077 = 990029) (by norm_num)
theorem B1321177 : Blo 1172403 1321177 := bbase (se 2 (by rfl) ⟨495441, by rfl⟩ : syracuseStep 1321177 = 990883) (by norm_num)
theorem B1485049 : Blo 1172403 1485049 := bbase (se 2 (by rfl) ⟨556893, by rfl⟩ : syracuseStep 1485049 = 1113787) (by norm_num)
theorem B2640149 : Blo 1172403 2640149 := bbase (se 6 (by rfl) ⟨61878, by rfl⟩ : syracuseStep 2640149 = 123757) (by norm_num)
theorem B1485145 : Blo 1172403 1485145 := bbase (se 2 (by rfl) ⟨556929, by rfl⟩ : syracuseStep 1485145 = 1113859) (by norm_num)
theorem B2640221 : Blo 1172403 2640221 := bbase (se 3 (by rfl) ⟨495041, by rfl⟩ : syracuseStep 2640221 = 990083) (by norm_num)
theorem B2967941 : Blo 1172403 2967941 := bbase (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) (by norm_num)
theorem B5638565 : Blo 1172403 5638565 := bbase (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) (by norm_num)
theorem B2640293 : Blo 1172403 2640293 := bbase (se 4 (by rfl) ⟨247527, by rfl⟩ : syracuseStep 2640293 = 495055) (by norm_num)
theorem B2640365 : Blo 1172403 2640365 := bbase (se 3 (by rfl) ⟨495068, by rfl⟩ : syracuseStep 2640365 = 990137) (by norm_num)
theorem B1485317 : Blo 1172403 1485317 := bbase (se 4 (by rfl) ⟨139248, by rfl⟩ : syracuseStep 1485317 = 278497) (by norm_num)
theorem B2411021 : Blo 1172403 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B1526293 : Blo 1172403 1526293 := bbase (se 6 (by rfl) ⟨35772, by rfl⟩ : syracuseStep 1526293 = 71545) (by norm_num)
theorem B3959333 : Blo 1172403 3959333 := bbase (se 4 (by rfl) ⟨371187, by rfl⟩ : syracuseStep 3959333 = 742375) (by norm_num)
theorem B2640437 : Blo 1172403 2640437 := bbase (se 5 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 2640437 = 247541) (by norm_num)
theorem B1485373 : Blo 1172403 1485373 := bbase (se 3 (by rfl) ⟨278507, by rfl⟩ : syracuseStep 1485373 = 557015) (by norm_num)
theorem B2640509 : Blo 1172403 2640509 := bbase (se 3 (by rfl) ⟨495095, by rfl⟩ : syracuseStep 2640509 = 990191) (by norm_num)
theorem B1485469 : Blo 1172403 1485469 := bbase (se 3 (by rfl) ⟨278525, by rfl⟩ : syracuseStep 1485469 = 557051) (by norm_num)
theorem B2640581 : Blo 1172403 2640581 := bbase (se 4 (by rfl) ⟨247554, by rfl⟩ : syracuseStep 2640581 = 495109) (by norm_num)
theorem B8915669 : Blo 1172403 8915669 := bbase (se 7 (by rfl) ⟨104480, by rfl⟩ : syracuseStep 8915669 = 208961) (by norm_num)
theorem B2968285 : Blo 1172403 2968285 := bbase (se 3 (by rfl) ⟨556553, by rfl⟩ : syracuseStep 2968285 = 1113107) (by norm_num)
theorem B2640653 : Blo 1172403 2640653 := bbase (se 3 (by rfl) ⟨495122, by rfl⟩ : syracuseStep 2640653 = 990245) (by norm_num)
theorem B3566405 : Blo 1172403 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B1485641 : Blo 1172403 1485641 := bbase (se 2 (by rfl) ⟨557115, by rfl⟩ : syracuseStep 1485641 = 1114231) (by norm_num)
theorem B2968397 : Blo 1172403 2968397 := bbase (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) (by norm_num)
theorem B1878869 : Blo 1172403 1878869 := bbase (se 9 (by rfl) ⟨5504, by rfl⟩ : syracuseStep 1878869 = 11009) (by norm_num)
theorem B2640725 : Blo 1172403 2640725 := bbase (se 9 (by rfl) ⟨7736, by rfl⟩ : syracuseStep 2640725 = 15473) (by norm_num)
theorem B7523189 : Blo 1172403 7523189 := bbase (se 5 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 7523189 = 705299) (by norm_num)
theorem B1485697 : Blo 1172403 1485697 := bbase (se 2 (by rfl) ⟨557136, by rfl⟩ : syracuseStep 1485697 = 1114273) (by norm_num)
theorem B2640797 : Blo 1172403 2640797 := bbase (se 3 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 2640797 = 990299) (by norm_num)
theorem B3959765 : Blo 1172403 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B1485793 : Blo 1172403 1485793 := bbase (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) (by norm_num)
theorem B2640869 : Blo 1172403 2640869 := bbase (se 4 (by rfl) ⟨247581, by rfl⟩ : syracuseStep 2640869 = 495163) (by norm_num)
theorem B3173381 : Blo 1172403 3173381 := bbase (se 4 (by rfl) ⟨297504, by rfl⟩ : syracuseStep 3173381 = 595009) (by norm_num)
theorem B2968589 : Blo 1172403 2968589 := bbase (se 3 (by rfl) ⟨556610, by rfl⟩ : syracuseStep 2968589 = 1113221) (by norm_num)
theorem B3009565 : Blo 1172403 3009565 := bbase (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) (by norm_num)
theorem B2640941 : Blo 1172403 2640941 := bbase (se 3 (by rfl) ⟨495176, by rfl⟩ : syracuseStep 2640941 = 990353) (by norm_num)
theorem B2821205 : Blo 1172403 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B8907893 : Blo 1172403 8907893 := bbase (se 5 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 8907893 = 835115) (by norm_num)
theorem B1879157 : Blo 1172403 1879157 := bbase (se 5 (by rfl) ⟨88085, by rfl⟩ : syracuseStep 1879157 = 176171) (by norm_num)
theorem B2641013 : Blo 1172403 2641013 := bbase (se 5 (by rfl) ⟨123797, by rfl⟩ : syracuseStep 2641013 = 247595) (by norm_num)
theorem B1485965 : Blo 1172403 1485965 := bbase (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) (by norm_num)
theorem B2641085 : Blo 1172403 2641085 := bbase (se 3 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 2641085 = 990407) (by norm_num)
theorem B1486021 : Blo 1172403 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B2641157 : Blo 1172403 2641157 := bbase (se 4 (by rfl) ⟨247608, by rfl⟩ : syracuseStep 2641157 = 495217) (by norm_num)
theorem B2821397 : Blo 1172403 2821397 := bbase (se 6 (by rfl) ⟨66126, by rfl⟩ : syracuseStep 2821397 = 132253) (by norm_num)
theorem B1486117 : Blo 1172403 1486117 := bbase (se 4 (by rfl) ⟨139323, by rfl⟩ : syracuseStep 1486117 = 278647) (by norm_num)
theorem B2714941 : Blo 1172403 2714941 := bbase (se 3 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 2714941 = 1018103) (by norm_num)
theorem B5008709 : Blo 1172403 5008709 := bbase (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) (by norm_num)
theorem B2641229 : Blo 1172403 2641229 := bbase (se 3 (by rfl) ⟨495230, by rfl⟩ : syracuseStep 2641229 = 990461) (by norm_num)
theorem B4451669 : Blo 1172403 4451669 := bbase (se 11 (by rfl) ⟨3260, by rfl⟩ : syracuseStep 4451669 = 6521) (by norm_num)
theorem B2968933 : Blo 1172403 2968933 := bbase (se 4 (by rfl) ⟨278337, by rfl⟩ : syracuseStep 2968933 = 556675) (by norm_num)
theorem B5942645 : Blo 1172403 5942645 := bbase (se 5 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 5942645 = 557123) (by norm_num)
theorem B3960197 : Blo 1172403 3960197 := bbase (se 4 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 3960197 = 742537) (by norm_num)
theorem B2641301 : Blo 1172403 2641301 := bbase (se 6 (by rfl) ⟨61905, by rfl⟩ : syracuseStep 2641301 = 123811) (by norm_num)
theorem B2035109 : Blo 1172403 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B1486289 : Blo 1172403 1486289 := bbase (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) (by norm_num)
theorem B2969045 : Blo 1172403 2969045 := bbase (se 7 (by rfl) ⟨34793, by rfl⟩ : syracuseStep 2969045 = 69587) (by norm_num)
theorem B2641373 : Blo 1172403 2641373 := bbase (se 3 (by rfl) ⟨495257, by rfl⟩ : syracuseStep 2641373 = 990515) (by norm_num)
theorem B4754933 : Blo 1172403 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B1486345 : Blo 1172403 1486345 := bbase (se 2 (by rfl) ⟨557379, by rfl⟩ : syracuseStep 1486345 = 1114759) (by norm_num)
theorem B1879573 : Blo 1172403 1879573 := bbase (se 6 (by rfl) ⟨44052, by rfl⟩ : syracuseStep 1879573 = 88105) (by norm_num)
theorem B2641445 : Blo 1172403 2641445 := bbase (se 4 (by rfl) ⟨247635, by rfl⟩ : syracuseStep 2641445 = 495271) (by norm_num)
theorem B5008949 : Blo 1172403 5008949 := bbase (se 5 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 5008949 = 469589) (by norm_num)
theorem B2641517 : Blo 1172403 2641517 := bbase (se 3 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 2641517 = 990569) (by norm_num)
theorem B2969237 : Blo 1172403 2969237 := bbase (se 6 (by rfl) ⟨69591, by rfl⟩ : syracuseStep 2969237 = 139183) (by norm_num)
theorem B2641589 : Blo 1172403 2641589 := bbase (se 5 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 2641589 = 247649) (by norm_num)
theorem B2641661 : Blo 1172403 2641661 := bbase (se 3 (by rfl) ⟨495311, by rfl⟩ : syracuseStep 2641661 = 990623) (by norm_num)
theorem B2748205 : Blo 1172403 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B3960629 : Blo 1172403 3960629 := bbase (se 5 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 3960629 = 371309) (by norm_num)
theorem B5639989 : Blo 1172403 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B2641733 : Blo 1172403 2641733 := bbase (se 4 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 2641733 = 495325) (by norm_num)
theorem B2641805 : Blo 1172403 2641805 := bbase (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) (by norm_num)
theorem B4231061 : Blo 1172403 4231061 := bbase (se 6 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 4231061 = 198331) (by norm_num)
theorem B5713861 : Blo 1172403 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B6770645 : Blo 1172403 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B2641877 : Blo 1172403 2641877 := bbase (se 7 (by rfl) ⟨30959, by rfl⟩ : syracuseStep 2641877 = 61919) (by norm_num)
theorem B2969581 : Blo 1172403 2969581 := bbase (se 3 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 2969581 = 1113593) (by norm_num)
theorem B2641949 : Blo 1172403 2641949 := bbase (se 3 (by rfl) ⟨495365, by rfl⟩ : syracuseStep 2641949 = 990731) (by norm_num)
theorem B1978445 : Blo 1172403 1978445 := bbase (se 3 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 1978445 = 741917) (by norm_num)
theorem B2969693 : Blo 1172403 2969693 := bbase (se 3 (by rfl) ⟨556817, by rfl⟩ : syracuseStep 2969693 = 1113635) (by norm_num)
theorem B2642021 : Blo 1172403 2642021 := bbase (se 4 (by rfl) ⟨247689, by rfl⟩ : syracuseStep 2642021 = 495379) (by norm_num)
theorem B2642093 : Blo 1172403 2642093 := bbase (se 3 (by rfl) ⟨495392, by rfl⟩ : syracuseStep 2642093 = 990785) (by norm_num)
theorem B1978573 : Blo 1172403 1978573 := bbase (se 3 (by rfl) ⟨370982, by rfl⟩ : syracuseStep 1978573 = 741965) (by norm_num)
theorem B3961061 : Blo 1172403 3961061 := bbase (se 4 (by rfl) ⟨371349, by rfl⟩ : syracuseStep 3961061 = 742699) (by norm_num)
theorem B2642165 : Blo 1172403 2642165 := bbase (se 5 (by rfl) ⟨123851, by rfl⟩ : syracuseStep 2642165 = 247703) (by norm_num)
theorem B2674949 : Blo 1172403 2674949 := bbase (se 4 (by rfl) ⟨250776, by rfl⟩ : syracuseStep 2674949 = 501553) (by norm_num)
theorem B2969885 : Blo 1172403 2969885 := bbase (se 3 (by rfl) ⟨556853, by rfl⟩ : syracuseStep 2969885 = 1113707) (by norm_num)
theorem B1978661 : Blo 1172403 1978661 := bbase (se 4 (by rfl) ⟨185499, by rfl⟩ : syracuseStep 1978661 = 370999) (by norm_num)
theorem B2642237 : Blo 1172403 2642237 := bbase (se 3 (by rfl) ⟨495419, by rfl⟩ : syracuseStep 2642237 = 990839) (by norm_num)
theorem B1356149 : Blo 1172403 1356149 := bbase (se 5 (by rfl) ⟨63569, by rfl⟩ : syracuseStep 1356149 = 127139) (by norm_num)
theorem B3567989 : Blo 1172403 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B2642309 : Blo 1172403 2642309 := bbase (se 4 (by rfl) ⟨247716, by rfl⟩ : syracuseStep 2642309 = 495433) (by norm_num)
theorem B1978789 : Blo 1172403 1978789 := bbase (se 4 (by rfl) ⟨185511, by rfl⟩ : syracuseStep 1978789 = 371023) (by norm_num)
theorem B3756469 : Blo 1172403 3756469 := bbase (se 5 (by rfl) ⟨176084, by rfl⟩ : syracuseStep 3756469 = 352169) (by norm_num)
theorem B12038581 : Blo 1172403 12038581 := bbase (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) (by norm_num)
theorem B1880509 : Blo 1172403 1880509 := bbase (se 3 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 1880509 = 705191) (by norm_num)
theorem B2642381 : Blo 1172403 2642381 := bbase (se 3 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 2642381 = 990893) (by norm_num)
theorem B5714405 : Blo 1172403 5714405 := bbase (se 4 (by rfl) ⟨535725, by rfl⟩ : syracuseStep 5714405 = 1071451) (by norm_num)
theorem B4452853 : Blo 1172403 4452853 := bbase (se 5 (by rfl) ⟨208727, by rfl⟩ : syracuseStep 4452853 = 417455) (by norm_num)
theorem B1978877 : Blo 1172403 1978877 := bbase (se 3 (by rfl) ⟨371039, by rfl⟩ : syracuseStep 1978877 = 742079) (by norm_num)
theorem B2413061 : Blo 1172403 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B2970229 : Blo 1172403 2970229 := bbase (se 5 (by rfl) ⟨139229, by rfl⟩ : syracuseStep 2970229 = 278459) (by norm_num)
theorem B1979005 : Blo 1172403 1979005 := bbase (se 3 (by rfl) ⟨371063, by rfl⟩ : syracuseStep 1979005 = 742127) (by norm_num)
theorem B5943941 : Blo 1172403 5943941 := bbase (se 4 (by rfl) ⟨557244, by rfl⟩ : syracuseStep 5943941 = 1114489) (by norm_num)
theorem B3961493 : Blo 1172403 3961493 := bbase (se 6 (by rfl) ⟨92847, by rfl⟩ : syracuseStep 3961493 = 185695) (by norm_num)
theorem B1979093 : Blo 1172403 1979093 := bbase (se 7 (by rfl) ⟨23192, by rfl⟩ : syracuseStep 1979093 = 46385) (by norm_num)
theorem B6869717 : Blo 1172403 6869717 := bbase (se 7 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 6869717 = 161009) (by norm_num)
theorem B2855645 : Blo 1172403 2855645 := bbase (se 3 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 2855645 = 1070867) (by norm_num)
theorem B2970341 : Blo 1172403 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B2577125 : Blo 1172403 2577125 := bbase (se 4 (by rfl) ⟨241605, by rfl⟩ : syracuseStep 2577125 = 483211) (by norm_num)
theorem B6026005 : Blo 1172403 6026005 := bbase (se 6 (by rfl) ⟨141234, by rfl⟩ : syracuseStep 6026005 = 282469) (by norm_num)
theorem B4453157 : Blo 1172403 4453157 := bbase (se 4 (by rfl) ⟨417483, by rfl⟩ : syracuseStep 4453157 = 834967) (by norm_num)
theorem B1979221 : Blo 1172403 1979221 := bbase (se 9 (by rfl) ⟨5798, by rfl⟩ : syracuseStep 1979221 = 11597) (by norm_num)
theorem B3756917 : Blo 1172403 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B2970533 : Blo 1172403 2970533 := bbase (se 4 (by rfl) ⟨278487, by rfl⟩ : syracuseStep 2970533 = 556975) (by norm_num)
theorem B1979309 : Blo 1172403 1979309 := bbase (se 3 (by rfl) ⟨371120, by rfl⟩ : syracuseStep 1979309 = 742241) (by norm_num)
theorem B1340345 : Blo 1172403 1340345 := bbase (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) (by norm_num)
theorem B14275541 : Blo 1172403 14275541 := bbase (se 7 (by rfl) ⟨167291, by rfl⟩ : syracuseStep 14275541 = 334583) (by norm_num)
theorem B9286613 : Blo 1172403 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B1504261 : Blo 1172403 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B2675717 : Blo 1172403 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B4756501 : Blo 1172403 4756501 := bbase (se 6 (by rfl) ⟨111480, by rfl⟩ : syracuseStep 4756501 = 222961) (by norm_num)
theorem B5936165 : Blo 1172403 5936165 := bbase (se 4 (by rfl) ⟨556515, by rfl⟩ : syracuseStep 5936165 = 1113031) (by norm_num)
theorem B1979437 : Blo 1172403 1979437 := bbase (se 3 (by rfl) ⟨371144, by rfl⟩ : syracuseStep 1979437 = 742289) (by norm_num)
theorem B3961925 : Blo 1172403 3961925 := bbase (se 4 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 3961925 = 742861) (by norm_num)
theorem B1979525 : Blo 1172403 1979525 := bbase (se 4 (by rfl) ⟨185580, by rfl⟩ : syracuseStep 1979525 = 371161) (by norm_num)
theorem B3339413 : Blo 1172403 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B4519061 : Blo 1172403 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B2970877 : Blo 1172403 2970877 := bbase (se 3 (by rfl) ⟨557039, by rfl⟩ : syracuseStep 2970877 = 1114079) (by norm_num)
theorem B1979653 : Blo 1172403 1979653 := bbase (se 4 (by rfl) ⟨185592, by rfl⟩ : syracuseStep 1979653 = 371185) (by norm_num)
theorem B10704149 : Blo 1172403 10704149 := bbase (se 6 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 10704149 = 501757) (by norm_num)
theorem B1979741 : Blo 1172403 1979741 := bbase (se 3 (by rfl) ⟨371201, by rfl⟩ : syracuseStep 1979741 = 742403) (by norm_num)
theorem B2970989 : Blo 1172403 2970989 := bbase (se 3 (by rfl) ⟨557060, by rfl⟩ : syracuseStep 2970989 = 1114121) (by norm_num)
theorem B1758605 : Blo 1172403 1758605 := bbase (se 3 (by rfl) ⟨329738, by rfl⟩ : syracuseStep 1758605 = 659477) (by norm_num)
theorem B1758629 : Blo 1172403 1758629 := bbase (se 4 (by rfl) ⟨164871, by rfl⟩ : syracuseStep 1758629 = 329743) (by norm_num)
theorem B1758653 : Blo 1172403 1758653 := bbase (se 3 (by rfl) ⟨329747, by rfl⟩ : syracuseStep 1758653 = 659495) (by norm_num)
theorem B8566229 : Blo 1172403 8566229 := bbase (se 7 (by rfl) ⟨100385, by rfl⟩ : syracuseStep 8566229 = 200771) (by norm_num)
theorem B1758677 : Blo 1172403 1758677 := bbase (se 7 (by rfl) ⟨20609, by rfl⟩ : syracuseStep 1758677 = 41219) (by norm_num)
theorem B1979869 : Blo 1172403 1979869 := bbase (se 3 (by rfl) ⟨371225, by rfl⟩ : syracuseStep 1979869 = 742451) (by norm_num)
theorem B1758701 : Blo 1172403 1758701 := bbase (se 3 (by rfl) ⟨329756, by rfl⟩ : syracuseStep 1758701 = 659513) (by norm_num)
theorem B3962357 : Blo 1172403 3962357 := bbase (se 5 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 3962357 = 371471) (by norm_num)
theorem B1758725 : Blo 1172403 1758725 := bbase (se 4 (by rfl) ⟨164880, by rfl⟩ : syracuseStep 1758725 = 329761) (by norm_num)
theorem B1758749 : Blo 1172403 1758749 := bbase (se 3 (by rfl) ⟨329765, by rfl⟩ : syracuseStep 1758749 = 659531) (by norm_num)
theorem B2971181 : Blo 1172403 2971181 := bbase (se 3 (by rfl) ⟨557096, by rfl⟩ : syracuseStep 2971181 = 1114193) (by norm_num)
theorem B1758773 : Blo 1172403 1758773 := bbase (se 5 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 1758773 = 164885) (by norm_num)
theorem B1979957 : Blo 1172403 1979957 := bbase (se 5 (by rfl) ⟨92810, by rfl⟩ : syracuseStep 1979957 = 185621) (by norm_num)
theorem B1758797 : Blo 1172403 1758797 := bbase (se 3 (by rfl) ⟨329774, by rfl⟩ : syracuseStep 1758797 = 659549) (by norm_num)
theorem B1758821 : Blo 1172403 1758821 := bbase (se 4 (by rfl) ⟨164889, by rfl⟩ : syracuseStep 1758821 = 329779) (by norm_num)
theorem B2225789 : Blo 1172403 2225789 := bbase (se 3 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 2225789 = 834671) (by norm_num)
theorem B1758845 : Blo 1172403 1758845 := bbase (se 3 (by rfl) ⟨329783, by rfl⟩ : syracuseStep 1758845 = 659567) (by norm_num)
theorem B1758869 : Blo 1172403 1758869 := bbase (se 6 (by rfl) ⟨41223, by rfl⟩ : syracuseStep 1758869 = 82447) (by norm_num)
theorem B1586837 : Blo 1172403 1586837 := bbase (se 6 (by rfl) ⟨37191, by rfl⟩ : syracuseStep 1586837 = 74383) (by norm_num)
theorem B1758893 : Blo 1172403 1758893 := bbase (se 3 (by rfl) ⟨329792, by rfl⟩ : syracuseStep 1758893 = 659585) (by norm_num)
theorem B1980085 : Blo 1172403 1980085 := bbase (se 5 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 1980085 = 185633) (by norm_num)
theorem B1758917 : Blo 1172403 1758917 := bbase (se 4 (by rfl) ⟨164898, by rfl⟩ : syracuseStep 1758917 = 329797) (by norm_num)
theorem B10024661 : Blo 1172403 10024661 := bbase (se 7 (by rfl) ⟨117476, by rfl⟩ : syracuseStep 10024661 = 234953) (by norm_num)
theorem B1758941 : Blo 1172403 1758941 := bbase (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) (by norm_num)
theorem B1758965 : Blo 1172403 1758965 := bbase (se 5 (by rfl) ⟨82451, by rfl⟩ : syracuseStep 1758965 = 164903) (by norm_num)
theorem B1758989 : Blo 1172403 1758989 := bbase (se 3 (by rfl) ⟨329810, by rfl⟩ : syracuseStep 1758989 = 659621) (by norm_num)
theorem B1980173 : Blo 1172403 1980173 := bbase (se 3 (by rfl) ⟨371282, by rfl⟩ : syracuseStep 1980173 = 742565) (by norm_num)
theorem B1759013 : Blo 1172403 1759013 := bbase (se 4 (by rfl) ⟨164907, by rfl⟩ : syracuseStep 1759013 = 329815) (by norm_num)
theorem B5011237 : Blo 1172403 5011237 := bbase (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) (by norm_num)
theorem B1759037 : Blo 1172403 1759037 := bbase (se 3 (by rfl) ⟨329819, by rfl⟩ : syracuseStep 1759037 = 659639) (by norm_num)
theorem B2504525 : Blo 1172403 2504525 := bbase (se 3 (by rfl) ⟨469598, by rfl⟩ : syracuseStep 2504525 = 939197) (by norm_num)
theorem B1759061 : Blo 1172403 1759061 := bbase (se 9 (by rfl) ⟨5153, by rfl⟩ : syracuseStep 1759061 = 10307) (by norm_num)
theorem B1759085 : Blo 1172403 1759085 := bbase (se 3 (by rfl) ⟨329828, by rfl⟩ : syracuseStep 1759085 = 659657) (by norm_num)
theorem B1759109 : Blo 1172403 1759109 := bbase (se 4 (by rfl) ⟨164916, by rfl⟩ : syracuseStep 1759109 = 329833) (by norm_num)
theorem B2971525 : Blo 1172403 2971525 := bbase (se 4 (by rfl) ⟨278580, by rfl⟩ : syracuseStep 2971525 = 557161) (by norm_num)
theorem B1980301 : Blo 1172403 1980301 := bbase (se 3 (by rfl) ⟨371306, by rfl⟩ : syracuseStep 1980301 = 742613) (by norm_num)
theorem B2258837 : Blo 1172403 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B5945237 : Blo 1172403 5945237 := bbase (se 6 (by rfl) ⟨139341, by rfl⟩ : syracuseStep 5945237 = 278683) (by norm_num)
theorem B1759133 : Blo 1172403 1759133 := bbase (se 3 (by rfl) ⟨329837, by rfl⟩ : syracuseStep 1759133 = 659675) (by norm_num)
theorem B3962789 : Blo 1172403 3962789 := bbase (se 4 (by rfl) ⟨371511, by rfl⟩ : syracuseStep 3962789 = 743023) (by norm_num)
theorem B1759157 : Blo 1172403 1759157 := bbase (se 5 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 1759157 = 164921) (by norm_num)
theorem B1759181 : Blo 1172403 1759181 := bbase (se 3 (by rfl) ⟨329846, by rfl⟩ : syracuseStep 1759181 = 659693) (by norm_num)
theorem B2676701 : Blo 1172403 2676701 := bbase (se 3 (by rfl) ⟨501881, by rfl⟩ : syracuseStep 2676701 = 1003763) (by norm_num)
theorem B1759205 : Blo 1172403 1759205 := bbase (se 4 (by rfl) ⟨164925, by rfl⟩ : syracuseStep 1759205 = 329851) (by norm_num)
theorem B1980389 : Blo 1172403 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B2971637 : Blo 1172403 2971637 := bbase (se 5 (by rfl) ⟨139295, by rfl⟩ : syracuseStep 2971637 = 278591) (by norm_num)
theorem B1759229 : Blo 1172403 1759229 := bbase (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) (by norm_num)
theorem B1759253 : Blo 1172403 1759253 := bbase (se 6 (by rfl) ⟨41232, by rfl⟩ : syracuseStep 1759253 = 82465) (by norm_num)
theorem B2676773 : Blo 1172403 2676773 := bbase (se 4 (by rfl) ⟨250947, by rfl⟩ : syracuseStep 2676773 = 501895) (by norm_num)
theorem B1759277 : Blo 1172403 1759277 := bbase (se 3 (by rfl) ⟨329864, by rfl⟩ : syracuseStep 1759277 = 659729) (by norm_num)
theorem B2504765 : Blo 1172403 2504765 := bbase (se 3 (by rfl) ⟨469643, by rfl⟩ : syracuseStep 2504765 = 939287) (by norm_num)
theorem B1759301 : Blo 1172403 1759301 := bbase (se 4 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 1759301 = 329869) (by norm_num)
theorem B1759325 : Blo 1172403 1759325 := bbase (se 3 (by rfl) ⟨329873, by rfl⟩ : syracuseStep 1759325 = 659747) (by norm_num)
theorem B1980517 : Blo 1172403 1980517 := bbase (se 4 (by rfl) ⟨185673, by rfl⟩ : syracuseStep 1980517 = 371347) (by norm_num)
theorem B1759349 : Blo 1172403 1759349 := bbase (se 5 (by rfl) ⟨82469, by rfl⟩ : syracuseStep 1759349 = 164939) (by norm_num)
theorem B1759373 : Blo 1172403 1759373 := bbase (se 3 (by rfl) ⟨329882, by rfl⟩ : syracuseStep 1759373 = 659765) (by norm_num)
theorem B1759397 : Blo 1172403 1759397 := bbase (se 4 (by rfl) ⟨164943, by rfl⟩ : syracuseStep 1759397 = 329887) (by norm_num)
theorem B2971829 : Blo 1172403 2971829 := bbase (se 5 (by rfl) ⟨139304, by rfl⟩ : syracuseStep 2971829 = 278609) (by norm_num)
theorem B1759421 : Blo 1172403 1759421 := bbase (se 3 (by rfl) ⟨329891, by rfl⟩ : syracuseStep 1759421 = 659783) (by norm_num)
theorem B1980605 : Blo 1172403 1980605 := bbase (se 3 (by rfl) ⟨371363, by rfl⟩ : syracuseStep 1980605 = 742727) (by norm_num)
theorem B1759445 : Blo 1172403 1759445 := bbase (se 7 (by rfl) ⟨20618, by rfl⟩ : syracuseStep 1759445 = 41237) (by norm_num)
theorem B1759469 : Blo 1172403 1759469 := bbase (se 3 (by rfl) ⟨329900, by rfl⟩ : syracuseStep 1759469 = 659801) (by norm_num)
theorem B1759493 : Blo 1172403 1759493 := bbase (se 4 (by rfl) ⟨164952, by rfl⟩ : syracuseStep 1759493 = 329905) (by norm_num)
theorem B3012869 : Blo 1172403 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B1669405 : Blo 1172403 1669405 := bbase (se 3 (by rfl) ⟨313013, by rfl⟩ : syracuseStep 1669405 = 626027) (by norm_num)
theorem B1759517 : Blo 1172403 1759517 := bbase (se 3 (by rfl) ⟨329909, by rfl⟩ : syracuseStep 1759517 = 659819) (by norm_num)
theorem B5937461 : Blo 1172403 5937461 := bbase (se 5 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 5937461 = 556637) (by norm_num)
theorem B1759541 : Blo 1172403 1759541 := bbase (se 5 (by rfl) ⟨82478, by rfl⟩ : syracuseStep 1759541 = 164957) (by norm_num)
theorem B3340597 : Blo 1172403 3340597 := bbase (se 5 (by rfl) ⟨156590, by rfl⟩ : syracuseStep 3340597 = 313181) (by norm_num)
theorem B1980733 : Blo 1172403 1980733 := bbase (se 3 (by rfl) ⟨371387, by rfl⟩ : syracuseStep 1980733 = 742775) (by norm_num)
theorem B1759565 : Blo 1172403 1759565 := bbase (se 3 (by rfl) ⟨329918, by rfl⟩ : syracuseStep 1759565 = 659837) (by norm_num)
theorem B3963221 : Blo 1172403 3963221 := bbase (se 10 (by rfl) ⟨5805, by rfl⟩ : syracuseStep 3963221 = 11611) (by norm_num)
theorem B1759589 : Blo 1172403 1759589 := bbase (se 4 (by rfl) ⟨164961, by rfl⟩ : syracuseStep 1759589 = 329923) (by norm_num)
theorem B2226541 : Blo 1172403 2226541 := bbase (se 3 (by rfl) ⟨417476, by rfl⟩ : syracuseStep 2226541 = 834953) (by norm_num)
theorem B1669501 : Blo 1172403 1669501 := bbase (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) (by norm_num)
theorem B1759613 : Blo 1172403 1759613 := bbase (se 3 (by rfl) ⟨329927, by rfl⟩ : syracuseStep 1759613 = 659855) (by norm_num)
theorem B2898317 : Blo 1172403 2898317 := bbase (se 3 (by rfl) ⟨543434, by rfl⟩ : syracuseStep 2898317 = 1086869) (by norm_num)
theorem B1759637 : Blo 1172403 1759637 := bbase (se 6 (by rfl) ⟨41241, by rfl⟩ : syracuseStep 1759637 = 82483) (by norm_num)
theorem B1980821 : Blo 1172403 1980821 := bbase (se 6 (by rfl) ⟨46425, by rfl⟩ : syracuseStep 1980821 = 92851) (by norm_num)
theorem B1759661 : Blo 1172403 1759661 := bbase (se 3 (by rfl) ⟨329936, by rfl⟩ : syracuseStep 1759661 = 659873) (by norm_num)
theorem B1759685 : Blo 1172403 1759685 := bbase (se 4 (by rfl) ⟨164970, by rfl⟩ : syracuseStep 1759685 = 329941) (by norm_num)
theorem B3340757 : Blo 1172403 3340757 := bbase (se 7 (by rfl) ⟨39149, by rfl⟩ : syracuseStep 3340757 = 78299) (by norm_num)
theorem B1759709 : Blo 1172403 1759709 := bbase (se 3 (by rfl) ⟨329945, by rfl⟩ : syracuseStep 1759709 = 659891) (by norm_num)
theorem B1759733 : Blo 1172403 1759733 := bbase (se 5 (by rfl) ⟨82487, by rfl⟩ : syracuseStep 1759733 = 164975) (by norm_num)
theorem B2005501 : Blo 1172403 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B2226685 : Blo 1172403 2226685 := bbase (se 3 (by rfl) ⟨417503, by rfl⟩ : syracuseStep 2226685 = 835007) (by norm_num)
theorem B1759757 : Blo 1172403 1759757 := bbase (se 3 (by rfl) ⟨329954, by rfl⟩ : syracuseStep 1759757 = 659909) (by norm_num)
theorem B2972173 : Blo 1172403 2972173 := bbase (se 3 (by rfl) ⟨557282, by rfl⟩ : syracuseStep 2972173 = 1114565) (by norm_num)
theorem B1980949 : Blo 1172403 1980949 := bbase (se 6 (by rfl) ⟨46428, by rfl⟩ : syracuseStep 1980949 = 92857) (by norm_num)
theorem B1759781 : Blo 1172403 1759781 := bbase (se 4 (by rfl) ⟨164979, by rfl⟩ : syracuseStep 1759781 = 329959) (by norm_num)
theorem B2505269 : Blo 1172403 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B2505277 : Blo 1172403 2505277 := bbase (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) (by norm_num)
theorem B1759805 : Blo 1172403 1759805 := bbase (se 3 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 1759805 = 659927) (by norm_num)
theorem B1759829 : Blo 1172403 1759829 := bbase (se 8 (by rfl) ⟨10311, by rfl⟩ : syracuseStep 1759829 = 20623) (by norm_num)
theorem B1784413 : Blo 1172403 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B1759853 : Blo 1172403 1759853 := bbase (se 3 (by rfl) ⟨329972, by rfl⟩ : syracuseStep 1759853 = 659945) (by norm_num)
theorem B1981037 : Blo 1172403 1981037 := bbase (se 3 (by rfl) ⟨371444, by rfl⟩ : syracuseStep 1981037 = 742889) (by norm_num)
theorem B2972285 : Blo 1172403 2972285 := bbase (se 3 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 2972285 = 1114607) (by norm_num)
theorem B1759877 : Blo 1172403 1759877 := bbase (se 4 (by rfl) ⟨164988, by rfl⟩ : syracuseStep 1759877 = 329977) (by norm_num)
theorem B2226845 : Blo 1172403 2226845 := bbase (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) (by norm_num)
theorem B1759901 : Blo 1172403 1759901 := bbase (se 3 (by rfl) ⟨329981, by rfl⟩ : syracuseStep 1759901 = 659963) (by norm_num)
theorem B1759925 : Blo 1172403 1759925 := bbase (se 5 (by rfl) ⟨82496, by rfl⟩ : syracuseStep 1759925 = 164993) (by norm_num)
theorem B3340997 : Blo 1172403 3340997 := bbase (se 4 (by rfl) ⟨313218, by rfl⟩ : syracuseStep 3340997 = 626437) (by norm_num)
theorem B1759949 : Blo 1172403 1759949 := bbase (se 3 (by rfl) ⟨329990, by rfl⟩ : syracuseStep 1759949 = 659981) (by norm_num)
theorem B1759973 : Blo 1172403 1759973 := bbase (se 4 (by rfl) ⟨164997, by rfl⟩ : syracuseStep 1759973 = 329995) (by norm_num)
theorem B1981165 : Blo 1172403 1981165 := bbase (se 3 (by rfl) ⟨371468, by rfl⟩ : syracuseStep 1981165 = 742937) (by norm_num)
theorem B6683381 : Blo 1172403 6683381 := bbase (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) (by norm_num)
theorem B1759997 : Blo 1172403 1759997 := bbase (se 3 (by rfl) ⟨329999, by rfl⟩ : syracuseStep 1759997 = 659999) (by norm_num)
theorem B1252109 : Blo 1172403 1252109 := bbase (se 3 (by rfl) ⟨234770, by rfl⟩ : syracuseStep 1252109 = 469541) (by norm_num)
theorem B1760021 : Blo 1172403 1760021 := bbase (se 6 (by rfl) ⟨41250, by rfl⟩ : syracuseStep 1760021 = 82501) (by norm_num)
theorem B2226989 : Blo 1172403 2226989 := bbase (se 3 (by rfl) ⟨417560, by rfl⟩ : syracuseStep 2226989 = 835121) (by norm_num)
theorem B1760045 : Blo 1172403 1760045 := bbase (se 3 (by rfl) ⟨330008, by rfl⟩ : syracuseStep 1760045 = 660017) (by norm_num)
theorem B2972477 : Blo 1172403 2972477 := bbase (se 3 (by rfl) ⟨557339, by rfl⟩ : syracuseStep 2972477 = 1114679) (by norm_num)
theorem B1760069 : Blo 1172403 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B1981253 : Blo 1172403 1981253 := bbase (se 4 (by rfl) ⟨185742, by rfl⟩ : syracuseStep 1981253 = 371485) (by norm_num)
theorem B1760093 : Blo 1172403 1760093 := bbase (se 3 (by rfl) ⟨330017, by rfl⟩ : syracuseStep 1760093 = 660035) (by norm_num)
theorem B4455269 : Blo 1172403 4455269 := bbase (se 4 (by rfl) ⟨417681, by rfl⟩ : syracuseStep 4455269 = 835363) (by norm_num)
theorem B1669997 : Blo 1172403 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B1760117 : Blo 1172403 1760117 := bbase (se 5 (by rfl) ⟨82505, by rfl⟩ : syracuseStep 1760117 = 165011) (by norm_num)
theorem B3341189 : Blo 1172403 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B1760141 : Blo 1172403 1760141 := bbase (se 3 (by rfl) ⟨330026, by rfl⟩ : syracuseStep 1760141 = 660053) (by norm_num)
theorem B1760165 : Blo 1172403 1760165 := bbase (se 4 (by rfl) ⟨165015, by rfl⟩ : syracuseStep 1760165 = 330031) (by norm_num)
theorem B5356469 : Blo 1172403 5356469 := bbase (se 5 (by rfl) ⟨251084, by rfl⟩ : syracuseStep 5356469 = 502169) (by norm_num)
theorem B1760189 : Blo 1172403 1760189 := bbase (se 3 (by rfl) ⟨330035, by rfl⟩ : syracuseStep 1760189 = 660071) (by norm_num)
theorem B1981381 : Blo 1172403 1981381 := bbase (se 4 (by rfl) ⟨185754, by rfl⟩ : syracuseStep 1981381 = 371509) (by norm_num)
theorem B1252297 : Blo 1172403 1252297 := bbase (se 2 (by rfl) ⟨469611, by rfl⟩ : syracuseStep 1252297 = 939223) (by norm_num)
theorem B1760213 : Blo 1172403 1760213 := bbase (se 7 (by rfl) ⟨20627, by rfl⟩ : syracuseStep 1760213 = 41255) (by norm_num)
theorem B1760237 : Blo 1172403 1760237 := bbase (se 3 (by rfl) ⟨330044, by rfl⟩ : syracuseStep 1760237 = 660089) (by norm_num)
theorem B1760261 : Blo 1172403 1760261 := bbase (se 4 (by rfl) ⟨165024, by rfl⟩ : syracuseStep 1760261 = 330049) (by norm_num)
theorem B1760285 : Blo 1172403 1760285 := bbase (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) (by norm_num)
theorem B1981469 : Blo 1172403 1981469 := bbase (se 3 (by rfl) ⟨371525, by rfl⟩ : syracuseStep 1981469 = 743051) (by norm_num)
theorem B1760309 : Blo 1172403 1760309 := bbase (se 5 (by rfl) ⟨82514, by rfl⟩ : syracuseStep 1760309 = 165029) (by norm_num)
theorem B3759173 : Blo 1172403 3759173 := bbase (se 4 (by rfl) ⟨352422, by rfl⟩ : syracuseStep 3759173 = 704845) (by norm_num)
theorem B2858053 : Blo 1172403 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B5356613 : Blo 1172403 5356613 := bbase (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) (by norm_num)
theorem B2227277 : Blo 1172403 2227277 := bbase (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) (by norm_num)
theorem B1760333 : Blo 1172403 1760333 := bbase (se 3 (by rfl) ⟨330062, by rfl⟩ : syracuseStep 1760333 = 660125) (by norm_num)
theorem B1760357 : Blo 1172403 1760357 := bbase (se 4 (by rfl) ⟨165033, by rfl⟩ : syracuseStep 1760357 = 330067) (by norm_num)
theorem B1760381 : Blo 1172403 1760381 := bbase (se 3 (by rfl) ⟨330071, by rfl⟩ : syracuseStep 1760381 = 660143) (by norm_num)
theorem B4455557 : Blo 1172403 4455557 := bbase (se 4 (by rfl) ⟨417708, by rfl⟩ : syracuseStep 4455557 = 835417) (by norm_num)
theorem B1760405 : Blo 1172403 1760405 := bbase (se 6 (by rfl) ⟨41259, by rfl⟩ : syracuseStep 1760405 = 82519) (by norm_num)
theorem B1981597 : Blo 1172403 1981597 := bbase (se 3 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 1981597 = 743099) (by norm_num)
theorem B1760429 : Blo 1172403 1760429 := bbase (se 3 (by rfl) ⟨330080, by rfl⟩ : syracuseStep 1760429 = 660161) (by norm_num)
theorem B1760453 : Blo 1172403 1760453 := bbase (se 4 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 1760453 = 330085) (by norm_num)
theorem B1760477 : Blo 1172403 1760477 := bbase (se 3 (by rfl) ⟨330089, by rfl⟩ : syracuseStep 1760477 = 660179) (by norm_num)
theorem B2227429 : Blo 1172403 2227429 := bbase (se 4 (by rfl) ⟨208821, by rfl⟩ : syracuseStep 2227429 = 417643) (by norm_num)
theorem B5012725 : Blo 1172403 5012725 := bbase (se 5 (by rfl) ⟨234971, by rfl⟩ : syracuseStep 5012725 = 469943) (by norm_num)
theorem B1760501 : Blo 1172403 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B1981685 : Blo 1172403 1981685 := bbase (se 5 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 1981685 = 185783) (by norm_num)
theorem B5012741 : Blo 1172403 5012741 := bbase (se 4 (by rfl) ⟨469944, by rfl⟩ : syracuseStep 5012741 = 939889) (by norm_num)
theorem B1760525 : Blo 1172403 1760525 := bbase (se 3 (by rfl) ⟨330098, by rfl⟩ : syracuseStep 1760525 = 660197) (by norm_num)
theorem B1760549 : Blo 1172403 1760549 := bbase (se 4 (by rfl) ⟨165051, by rfl⟩ : syracuseStep 1760549 = 330103) (by norm_num)
theorem B1760573 : Blo 1172403 1760573 := bbase (se 3 (by rfl) ⟨330107, by rfl⟩ : syracuseStep 1760573 = 660215) (by norm_num)
theorem B1760597 : Blo 1172403 1760597 := bbase (se 11 (by rfl) ⟨1289, by rfl⟩ : syracuseStep 1760597 = 2579) (by norm_num)
theorem B1760621 : Blo 1172403 1760621 := bbase (se 3 (by rfl) ⟨330116, by rfl⟩ : syracuseStep 1760621 = 660233) (by norm_num)
theorem B1760645 : Blo 1172403 1760645 := bbase (se 4 (by rfl) ⟨165060, by rfl⟩ : syracuseStep 1760645 = 330121) (by norm_num)
theorem B1670549 : Blo 1172403 1670549 := bbase (se 6 (by rfl) ⟨39153, by rfl⟩ : syracuseStep 1670549 = 78307) (by norm_num)
theorem B2817437 : Blo 1172403 2817437 := bbase (se 3 (by rfl) ⟨528269, by rfl⟩ : syracuseStep 2817437 = 1056539) (by norm_num)
theorem B1760669 : Blo 1172403 1760669 := bbase (se 3 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 1760669 = 660251) (by norm_num)
theorem B1785245 : Blo 1172403 1785245 := bbase (se 3 (by rfl) ⟨334733, by rfl⟩ : syracuseStep 1785245 = 669467) (by norm_num)
theorem B1760693 : Blo 1172403 1760693 := bbase (se 5 (by rfl) ⟨82532, by rfl⟩ : syracuseStep 1760693 = 165065) (by norm_num)
theorem B1760717 : Blo 1172403 1760717 := bbase (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) (by norm_num)
theorem B1760741 : Blo 1172403 1760741 := bbase (se 4 (by rfl) ⟨165069, by rfl⟩ : syracuseStep 1760741 = 330139) (by norm_num)
theorem B1760765 : Blo 1172403 1760765 := bbase (se 3 (by rfl) ⟨330143, by rfl⟩ : syracuseStep 1760765 = 660287) (by norm_num)
theorem B2227733 : Blo 1172403 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B1760789 : Blo 1172403 1760789 := bbase (se 6 (by rfl) ⟨41268, by rfl⟩ : syracuseStep 1760789 = 82537) (by norm_num)
theorem B1760813 : Blo 1172403 1760813 := bbase (se 3 (by rfl) ⟨330152, by rfl⟩ : syracuseStep 1760813 = 660305) (by norm_num)
theorem B5938757 : Blo 1172403 5938757 := bbase (se 4 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 5938757 = 1113517) (by norm_num)
theorem B1760837 : Blo 1172403 1760837 := bbase (se 4 (by rfl) ⟨165078, by rfl⟩ : syracuseStep 1760837 = 330157) (by norm_num)
theorem B1760861 : Blo 1172403 1760861 := bbase (se 3 (by rfl) ⟨330161, by rfl⟩ : syracuseStep 1760861 = 660323) (by norm_num)
theorem B1760885 : Blo 1172403 1760885 := bbase (se 5 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 1760885 = 165083) (by norm_num)
theorem B1760909 : Blo 1172403 1760909 := bbase (se 3 (by rfl) ⟨330170, by rfl⟩ : syracuseStep 1760909 = 660341) (by norm_num)
theorem B2506405 : Blo 1172403 2506405 := bbase (se 4 (by rfl) ⟨234975, by rfl⟩ : syracuseStep 2506405 = 469951) (by norm_num)
theorem B1760933 : Blo 1172403 1760933 := bbase (se 4 (by rfl) ⟨165087, by rfl⟩ : syracuseStep 1760933 = 330175) (by norm_num)
theorem B1760957 : Blo 1172403 1760957 := bbase (se 3 (by rfl) ⟨330179, by rfl⟩ : syracuseStep 1760957 = 660359) (by norm_num)
theorem B1760981 : Blo 1172403 1760981 := bbase (se 7 (by rfl) ⟨20636, by rfl⟩ : syracuseStep 1760981 = 41273) (by norm_num)
theorem B1761005 : Blo 1172403 1761005 := bbase (se 3 (by rfl) ⟨330188, by rfl⟩ : syracuseStep 1761005 = 660377) (by norm_num)
theorem B1408753 : Blo 1172403 1408753 := bbase (se 2 (by rfl) ⟨528282, by rfl⟩ : syracuseStep 1408753 = 1056565) (by norm_num)
theorem B1408757 : Blo 1172403 1408757 := bbase (se 5 (by rfl) ⟨66035, by rfl⟩ : syracuseStep 1408757 = 132071) (by norm_num)
theorem B1253117 : Blo 1172403 1253117 := bbase (se 3 (by rfl) ⟨234959, by rfl⟩ : syracuseStep 1253117 = 469919) (by norm_num)
theorem B1761029 : Blo 1172403 1761029 := bbase (se 4 (by rfl) ⟨165096, by rfl⟩ : syracuseStep 1761029 = 330193) (by norm_num)
theorem B1761053 : Blo 1172403 1761053 := bbase (se 3 (by rfl) ⟨330197, by rfl⟩ : syracuseStep 1761053 = 660395) (by norm_num)
theorem B1761077 : Blo 1172403 1761077 := bbase (se 5 (by rfl) ⟨82550, by rfl⟩ : syracuseStep 1761077 = 165101) (by norm_num)
theorem B1761101 : Blo 1172403 1761101 := bbase (se 3 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 1761101 = 660413) (by norm_num)
theorem B2006869 : Blo 1172403 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B3342181 : Blo 1172403 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B1761125 : Blo 1172403 1761125 := bbase (se 4 (by rfl) ⟨165105, by rfl⟩ : syracuseStep 1761125 = 330211) (by norm_num)
theorem B1761149 : Blo 1172403 1761149 := bbase (se 3 (by rfl) ⟨330215, by rfl⟩ : syracuseStep 1761149 = 660431) (by norm_num)
theorem B6684565 : Blo 1172403 6684565 := bbase (se 6 (by rfl) ⟨156669, by rfl⟩ : syracuseStep 6684565 = 313339) (by norm_num)
theorem B1761173 : Blo 1172403 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B1761197 : Blo 1172403 1761197 := bbase (se 3 (by rfl) ⟨330224, by rfl⟩ : syracuseStep 1761197 = 660449) (by norm_num)
theorem B3170245 : Blo 1172403 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B1761221 : Blo 1172403 1761221 := bbase (se 4 (by rfl) ⟨165114, by rfl⟩ : syracuseStep 1761221 = 330229) (by norm_num)
theorem B1761245 : Blo 1172403 1761245 := bbase (se 3 (by rfl) ⟨330233, by rfl⟩ : syracuseStep 1761245 = 660467) (by norm_num)
theorem B1761269 : Blo 1172403 1761269 := bbase (se 5 (by rfl) ⟨82559, by rfl⟩ : syracuseStep 1761269 = 165119) (by norm_num)
theorem B1761281 : Blo 1172403 1761281 := bstep (se 2 (by rfl) ⟨660480, by rfl⟩ : syracuseStep 1761281 = 1320961) B1320961
theorem B1671187 : Blo 1172403 1671187 := bstep (se 1 (by rfl) ⟨1253390, by rfl⟩ : syracuseStep 1671187 = 2506781) B2506781
theorem B1761299 : Blo 1172403 1761299 := bstep (se 1 (by rfl) ⟨1320974, by rfl⟩ : syracuseStep 1761299 = 2641949) B2641949
theorem B1761329 : Blo 1172403 1761329 := bstep (se 2 (by rfl) ⟨660498, by rfl⟩ : syracuseStep 1761329 = 1320997) B1320997
theorem B1318963 : Blo 1172403 1318963 := bstep (se 1 (by rfl) ⟨989222, by rfl⟩ : syracuseStep 1318963 = 1978445) B1978445
theorem B1761347 : Blo 1172403 1761347 := bstep (se 1 (by rfl) ⟨1321010, by rfl⟩ : syracuseStep 1761347 = 2642021) B2642021
theorem B1761377 : Blo 1172403 1761377 := bstep (se 2 (by rfl) ⟨660516, by rfl⟩ : syracuseStep 1761377 = 1321033) B1321033
theorem B1409123 : Blo 1172403 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B1761395 : Blo 1172403 1761395 := bstep (se 1 (by rfl) ⟨1321046, by rfl⟩ : syracuseStep 1761395 = 2642093) B2642093
theorem B3760273 : Blo 1172403 3760273 := bstep (se 2 (by rfl) ⟨1410102, by rfl⟩ : syracuseStep 3760273 = 2820205) B2820205
theorem B1761425 : Blo 1172403 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B1761443 : Blo 1172403 1761443 := bstep (se 1 (by rfl) ⟨1321082, by rfl⟩ : syracuseStep 1761443 = 2642165) B2642165
theorem B2228401 : Blo 1172403 2228401 := bstep (se 2 (by rfl) ⟨835650, by rfl⟩ : syracuseStep 2228401 = 1671301) B1671301
theorem B1761473 : Blo 1172403 1761473 := bstep (se 2 (by rfl) ⟨660552, by rfl⟩ : syracuseStep 1761473 = 1321105) B1321105
theorem B1319107 : Blo 1172403 1319107 := bstep (se 1 (by rfl) ⟨989330, by rfl⟩ : syracuseStep 1319107 = 1978661) B1978661
theorem B5939405 : Blo 1172403 5939405 := bstep (se 3 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 5939405 = 2227277) B2227277
theorem B1761491 : Blo 1172403 1761491 := bstep (se 1 (by rfl) ⟨1321118, by rfl⟩ : syracuseStep 1761491 = 2642237) B2642237
theorem B1761521 : Blo 1172403 1761521 := bstep (se 2 (by rfl) ⟨660570, by rfl⟩ : syracuseStep 1761521 = 1321141) B1321141
theorem B1761539 : Blo 1172403 1761539 := bstep (se 1 (by rfl) ⟨1321154, by rfl⟩ : syracuseStep 1761539 = 2642309) B2642309
theorem B7520525 : Blo 1172403 7520525 := bstep (se 3 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 7520525 = 2820197) B2820197
theorem B2638097 : Blo 1172403 2638097 := bstep (se 2 (by rfl) ⟨989286, by rfl⟩ : syracuseStep 2638097 = 1978573) B1978573
theorem B1761569 : Blo 1172403 1761569 := bstep (se 2 (by rfl) ⟨660588, by rfl⟩ : syracuseStep 1761569 = 1321177) B1321177
theorem B2638115 : Blo 1172403 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B1761587 : Blo 1172403 1761587 := bstep (se 1 (by rfl) ⟨1321190, by rfl⟩ : syracuseStep 1761587 = 2642381) B2642381
theorem B3809603 : Blo 1172403 3809603 := bstep (se 1 (by rfl) ⟨2857202, by rfl⟩ : syracuseStep 3809603 = 5714405) B5714405
theorem B11272517 : Blo 1172403 11272517 := bstep (se 4 (by rfl) ⟨1056798, by rfl⟩ : syracuseStep 11272517 = 2113597) B2113597
theorem B1319251 : Blo 1172403 1319251 := bstep (se 1 (by rfl) ⟨989438, by rfl⟩ : syracuseStep 1319251 = 1978877) B1978877
theorem B6685091 : Blo 1172403 6685091 := bstep (se 1 (by rfl) ⟨5013818, by rfl⟩ : syracuseStep 6685091 = 10027637) B10027637
theorem B1409459 : Blo 1172403 1409459 := bstep (se 1 (by rfl) ⟨1057094, by rfl⟩ : syracuseStep 1409459 = 2114189) B2114189
theorem B1319395 : Blo 1172403 1319395 := bstep (se 1 (by rfl) ⟨989546, by rfl⟩ : syracuseStep 1319395 = 1979093) B1979093
theorem B4579811 : Blo 1172403 4579811 := bstep (se 1 (by rfl) ⟨3434858, by rfl⟩ : syracuseStep 4579811 = 6869717) B6869717
theorem B2638385 : Blo 1172403 2638385 := bstep (se 2 (by rfl) ⟨989394, by rfl⟩ : syracuseStep 2638385 = 1978789) B1978789
theorem B2638403 : Blo 1172403 2638403 := bstep (se 1 (by rfl) ⟨1978802, by rfl⟩ : syracuseStep 2638403 = 3957605) B3957605
theorem B2507345 : Blo 1172403 2507345 := bstep (se 2 (by rfl) ⟨940254, by rfl⟩ : syracuseStep 2507345 = 1880509) B1880509
theorem B1319539 : Blo 1172403 1319539 := bstep (se 1 (by rfl) ⟨989654, by rfl⟩ : syracuseStep 1319539 = 1979309) B1979309
theorem B3957389 : Blo 1172403 3957389 := bstep (se 3 (by rfl) ⟨742010, by rfl⟩ : syracuseStep 3957389 = 1484021) B1484021
theorem B3957443 : Blo 1172403 3957443 := bstep (se 1 (by rfl) ⟨2968082, by rfl⟩ : syracuseStep 3957443 = 5936165) B5936165
theorem B1319683 : Blo 1172403 1319683 := bstep (se 1 (by rfl) ⟨989762, by rfl⟩ : syracuseStep 1319683 = 1979525) B1979525
theorem B4227875 : Blo 1172403 4227875 := bstep (se 1 (by rfl) ⟨3170906, by rfl⟩ : syracuseStep 4227875 = 6341813) B6341813
theorem B2638673 : Blo 1172403 2638673 := bstep (se 2 (by rfl) ⟨989502, by rfl⟩ : syracuseStep 2638673 = 1979005) B1979005
theorem B2638691 : Blo 1172403 2638691 := bstep (se 1 (by rfl) ⟨1979018, by rfl⟩ : syracuseStep 2638691 = 3958037) B3958037
theorem B7136099 : Blo 1172403 7136099 := bstep (se 1 (by rfl) ⟨5352074, by rfl⟩ : syracuseStep 7136099 = 10704149) B10704149
theorem B1319827 : Blo 1172403 1319827 := bstep (se 1 (by rfl) ⟨989870, by rfl⟩ : syracuseStep 1319827 = 1979741) B1979741
theorem B1172403 : Blo 1172403 1172403 := bstep (se 1 (by rfl) ⟨879302, by rfl⟩ : syracuseStep 1172403 = 1758605) B1758605
theorem B1172419 : Blo 1172403 1172419 := bstep (se 1 (by rfl) ⟨879314, by rfl⟩ : syracuseStep 1172419 = 1758629) B1758629
theorem B3957713 : Blo 1172403 3957713 := bstep (se 2 (by rfl) ⟨1484142, by rfl⟩ : syracuseStep 3957713 = 2968285) B2968285
theorem B1172435 : Blo 1172403 1172435 := bstep (se 1 (by rfl) ⟨879326, by rfl⟩ : syracuseStep 1172435 = 1758653) B1758653
theorem B5710819 : Blo 1172403 5710819 := bstep (se 1 (by rfl) ⟨4283114, by rfl⟩ : syracuseStep 5710819 = 8566229) B8566229
theorem B1172451 : Blo 1172403 1172451 := bstep (se 1 (by rfl) ⟨879338, by rfl⟩ : syracuseStep 1172451 = 1758677) B1758677
theorem B3343331 : Blo 1172403 3343331 := bstep (se 1 (by rfl) ⟨2507498, by rfl⟩ : syracuseStep 3343331 = 5014997) B5014997
theorem B1172467 : Blo 1172403 1172467 := bstep (se 1 (by rfl) ⟨879350, by rfl⟩ : syracuseStep 1172467 = 1758701) B1758701
theorem B1172483 : Blo 1172403 1172483 := bstep (se 1 (by rfl) ⟨879362, by rfl⟩ : syracuseStep 1172483 = 1758725) B1758725
theorem B1172499 : Blo 1172403 1172499 := bstep (se 1 (by rfl) ⟨879374, by rfl⟩ : syracuseStep 1172499 = 1758749) B1758749
theorem B1172515 : Blo 1172403 1172515 := bstep (se 1 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 1172515 = 1758773) B1758773
theorem B1319971 : Blo 1172403 1319971 := bstep (se 1 (by rfl) ⟨989978, by rfl⟩ : syracuseStep 1319971 = 1979957) B1979957
theorem B1172531 : Blo 1172403 1172531 := bstep (se 1 (by rfl) ⟨879398, by rfl⟩ : syracuseStep 1172531 = 1758797) B1758797
theorem B1172547 : Blo 1172403 1172547 := bstep (se 1 (by rfl) ⟨879410, by rfl⟩ : syracuseStep 1172547 = 1758821) B1758821
theorem B7513165 : Blo 1172403 7513165 := bstep (se 3 (by rfl) ⟨1408718, by rfl⟩ : syracuseStep 7513165 = 2817437) B2817437
theorem B1483859 : Blo 1172403 1483859 := bstep (se 1 (by rfl) ⟨1112894, by rfl⟩ : syracuseStep 1483859 = 2225789) B2225789
theorem B1172563 : Blo 1172403 1172563 := bstep (se 1 (by rfl) ⟨879422, by rfl⟩ : syracuseStep 1172563 = 1758845) B1758845
theorem B1172579 : Blo 1172403 1172579 := bstep (se 1 (by rfl) ⟨879434, by rfl⟩ : syracuseStep 1172579 = 1758869) B1758869
theorem B2638961 : Blo 1172403 2638961 := bstep (se 2 (by rfl) ⟨989610, by rfl⟩ : syracuseStep 2638961 = 1979221) B1979221
theorem B1172595 : Blo 1172403 1172595 := bstep (se 1 (by rfl) ⟨879446, by rfl⟩ : syracuseStep 1172595 = 1758893) B1758893
theorem B1172611 : Blo 1172403 1172611 := bstep (se 1 (by rfl) ⟨879458, by rfl⟩ : syracuseStep 1172611 = 1758917) B1758917
theorem B2638979 : Blo 1172403 2638979 := bstep (se 1 (by rfl) ⟨1979234, by rfl⟩ : syracuseStep 2638979 = 3958469) B3958469
theorem B1172627 : Blo 1172403 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B1172643 : Blo 1172403 1172643 := bstep (se 1 (by rfl) ⟨879482, by rfl⟩ : syracuseStep 1172643 = 1758965) B1758965
theorem B1172659 : Blo 1172403 1172659 := bstep (se 1 (by rfl) ⟨879494, by rfl⟩ : syracuseStep 1172659 = 1758989) B1758989
theorem B1320115 : Blo 1172403 1320115 := bstep (se 1 (by rfl) ⟨990086, by rfl⟩ : syracuseStep 1320115 = 1980173) B1980173
theorem B1172675 : Blo 1172403 1172675 := bstep (se 1 (by rfl) ⟨879506, by rfl⟩ : syracuseStep 1172675 = 1759013) B1759013
theorem B2229457 : Blo 1172403 2229457 := bstep (se 2 (by rfl) ⟨836046, by rfl⟩ : syracuseStep 2229457 = 1672093) B1672093
theorem B1172691 : Blo 1172403 1172691 := bstep (se 1 (by rfl) ⟨879518, by rfl⟩ : syracuseStep 1172691 = 1759037) B1759037
theorem B1172707 : Blo 1172403 1172707 := bstep (se 1 (by rfl) ⟨879530, by rfl⟩ : syracuseStep 1172707 = 1759061) B1759061
theorem B78169315 : Blo 1172403 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B4457699 : Blo 1172403 4457699 := bstep (se 1 (by rfl) ⟨3343274, by rfl⟩ : syracuseStep 4457699 = 6686549) B6686549
theorem B4457713 : Blo 1172403 4457713 := bstep (se 2 (by rfl) ⟨1671642, by rfl⟩ : syracuseStep 4457713 = 3343285) B3343285
theorem B1172723 : Blo 1172403 1172723 := bstep (se 1 (by rfl) ⟨879542, by rfl⟩ : syracuseStep 1172723 = 1759085) B1759085
theorem B1172739 : Blo 1172403 1172739 := bstep (se 1 (by rfl) ⟨879554, by rfl⟩ : syracuseStep 1172739 = 1759109) B1759109
theorem B1172755 : Blo 1172403 1172755 := bstep (se 1 (by rfl) ⟨879566, by rfl⟩ : syracuseStep 1172755 = 1759133) B1759133
theorem B1172771 : Blo 1172403 1172771 := bstep (se 1 (by rfl) ⟨879578, by rfl⟩ : syracuseStep 1172771 = 1759157) B1759157
theorem B3761453 : Blo 1172403 3761453 := bstep (se 3 (by rfl) ⟨705272, by rfl⟩ : syracuseStep 3761453 = 1410545) B1410545
theorem B1172787 : Blo 1172403 1172787 := bstep (se 1 (by rfl) ⟨879590, by rfl⟩ : syracuseStep 1172787 = 1759181) B1759181
theorem B1172803 : Blo 1172403 1172803 := bstep (se 1 (by rfl) ⟨879602, by rfl⟩ : syracuseStep 1172803 = 1759205) B1759205
theorem B1320259 : Blo 1172403 1320259 := bstep (se 1 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 1320259 = 1980389) B1980389
theorem B1172819 : Blo 1172403 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B1172835 : Blo 1172403 1172835 := bstep (se 1 (by rfl) ⟨879626, by rfl⟩ : syracuseStep 1172835 = 1759253) B1759253
theorem B1172851 : Blo 1172403 1172851 := bstep (se 1 (by rfl) ⟨879638, by rfl⟩ : syracuseStep 1172851 = 1759277) B1759277
theorem B1172867 : Blo 1172403 1172867 := bstep (se 1 (by rfl) ⟨879650, by rfl⟩ : syracuseStep 1172867 = 1759301) B1759301
theorem B2639249 : Blo 1172403 2639249 := bstep (se 2 (by rfl) ⟨989718, by rfl⟩ : syracuseStep 2639249 = 1979437) B1979437
theorem B1172883 : Blo 1172403 1172883 := bstep (se 1 (by rfl) ⟨879662, by rfl⟩ : syracuseStep 1172883 = 1759325) B1759325
theorem B1172899 : Blo 1172403 1172899 := bstep (se 1 (by rfl) ⟨879674, by rfl⟩ : syracuseStep 1172899 = 1759349) B1759349
theorem B2639267 : Blo 1172403 2639267 := bstep (se 1 (by rfl) ⟨1979450, by rfl⟩ : syracuseStep 2639267 = 3958901) B3958901
theorem B3810737 : Blo 1172403 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B1172915 : Blo 1172403 1172915 := bstep (se 1 (by rfl) ⟨879686, by rfl⟩ : syracuseStep 1172915 = 1759373) B1759373
theorem B1172931 : Blo 1172403 1172931 := bstep (se 1 (by rfl) ⟨879698, by rfl⟩ : syracuseStep 1172931 = 1759397) B1759397
theorem B32138693 : Blo 1172403 32138693 := bstep (se 4 (by rfl) ⟨3013002, by rfl⟩ : syracuseStep 32138693 = 6026005) B6026005
theorem B1172947 : Blo 1172403 1172947 := bstep (se 1 (by rfl) ⟨879710, by rfl⟩ : syracuseStep 1172947 = 1759421) B1759421
theorem B1320403 : Blo 1172403 1320403 := bstep (se 1 (by rfl) ⟨990302, by rfl⟩ : syracuseStep 1320403 = 1980605) B1980605
theorem B1172963 : Blo 1172403 1172963 := bstep (se 1 (by rfl) ⟨879722, by rfl⟩ : syracuseStep 1172963 = 1759445) B1759445
theorem B3958253 : Blo 1172403 3958253 := bstep (se 3 (by rfl) ⟨742172, by rfl⟩ : syracuseStep 3958253 = 1484345) B1484345
theorem B1172979 : Blo 1172403 1172979 := bstep (se 1 (by rfl) ⟨879734, by rfl⟩ : syracuseStep 1172979 = 1759469) B1759469
theorem B1172995 : Blo 1172403 1172995 := bstep (se 1 (by rfl) ⟨879746, by rfl⟩ : syracuseStep 1172995 = 1759493) B1759493
theorem B1173011 : Blo 1172403 1173011 := bstep (se 1 (by rfl) ⟨879758, by rfl⟩ : syracuseStep 1173011 = 1759517) B1759517
theorem B3958307 : Blo 1172403 3958307 := bstep (se 1 (by rfl) ⟨2968730, by rfl⟩ : syracuseStep 3958307 = 5937461) B5937461
theorem B1173027 : Blo 1172403 1173027 := bstep (se 1 (by rfl) ⟨879770, by rfl⟩ : syracuseStep 1173027 = 1759541) B1759541
theorem B1173043 : Blo 1172403 1173043 := bstep (se 1 (by rfl) ⟨879782, by rfl⟩ : syracuseStep 1173043 = 1759565) B1759565
theorem B1173059 : Blo 1172403 1173059 := bstep (se 1 (by rfl) ⟨879794, by rfl⟩ : syracuseStep 1173059 = 1759589) B1759589
theorem B1173075 : Blo 1172403 1173075 := bstep (se 1 (by rfl) ⟨879806, by rfl⟩ : syracuseStep 1173075 = 1759613) B1759613
theorem B1173091 : Blo 1172403 1173091 := bstep (se 1 (by rfl) ⟨879818, by rfl⟩ : syracuseStep 1173091 = 1759637) B1759637
theorem B1320547 : Blo 1172403 1320547 := bstep (se 1 (by rfl) ⟨990410, by rfl⟩ : syracuseStep 1320547 = 1980821) B1980821
theorem B1173107 : Blo 1172403 1173107 := bstep (se 1 (by rfl) ⟨879830, by rfl⟩ : syracuseStep 1173107 = 1759661) B1759661
theorem B1173123 : Blo 1172403 1173123 := bstep (se 1 (by rfl) ⟨879842, by rfl⟩ : syracuseStep 1173123 = 1759685) B1759685
theorem B1173139 : Blo 1172403 1173139 := bstep (se 1 (by rfl) ⟨879854, by rfl⟩ : syracuseStep 1173139 = 1759709) B1759709
theorem B1173155 : Blo 1172403 1173155 := bstep (se 1 (by rfl) ⟨879866, by rfl⟩ : syracuseStep 1173155 = 1759733) B1759733
theorem B2639537 : Blo 1172403 2639537 := bstep (se 2 (by rfl) ⟨989826, by rfl⟩ : syracuseStep 2639537 = 1979653) B1979653
theorem B1173171 : Blo 1172403 1173171 := bstep (se 1 (by rfl) ⟨879878, by rfl⟩ : syracuseStep 1173171 = 1759757) B1759757
theorem B1607347 : Blo 1172403 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B2639555 : Blo 1172403 2639555 := bstep (se 1 (by rfl) ⟨1979666, by rfl⟩ : syracuseStep 2639555 = 3959333) B3959333
theorem B1173187 : Blo 1172403 1173187 := bstep (se 1 (by rfl) ⟨879890, by rfl⟩ : syracuseStep 1173187 = 1759781) B1759781
theorem B1173203 : Blo 1172403 1173203 := bstep (se 1 (by rfl) ⟨879902, by rfl⟩ : syracuseStep 1173203 = 1759805) B1759805
theorem B1173219 : Blo 1172403 1173219 := bstep (se 1 (by rfl) ⟨879914, by rfl⟩ : syracuseStep 1173219 = 1759829) B1759829
theorem B1173235 : Blo 1172403 1173235 := bstep (se 1 (by rfl) ⟨879926, by rfl⟩ : syracuseStep 1173235 = 1759853) B1759853
theorem B1320691 : Blo 1172403 1320691 := bstep (se 1 (by rfl) ⟨990518, by rfl⟩ : syracuseStep 1320691 = 1981037) B1981037
theorem B1173251 : Blo 1172403 1173251 := bstep (se 1 (by rfl) ⟨879938, by rfl⟩ : syracuseStep 1173251 = 1759877) B1759877
theorem B1484563 : Blo 1172403 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B1173267 : Blo 1172403 1173267 := bstep (se 1 (by rfl) ⟨879950, by rfl⟩ : syracuseStep 1173267 = 1759901) B1759901
theorem B1173283 : Blo 1172403 1173283 := bstep (se 1 (by rfl) ⟨879962, by rfl⟩ : syracuseStep 1173283 = 1759925) B1759925
theorem B3958577 : Blo 1172403 3958577 := bstep (se 2 (by rfl) ⟨1484466, by rfl⟩ : syracuseStep 3958577 = 2968933) B2968933
theorem B1173299 : Blo 1172403 1173299 := bstep (se 1 (by rfl) ⟨879974, by rfl⟩ : syracuseStep 1173299 = 1759949) B1759949
theorem B1173315 : Blo 1172403 1173315 := bstep (se 1 (by rfl) ⟨879986, by rfl⟩ : syracuseStep 1173315 = 1759973) B1759973
theorem B1173331 : Blo 1172403 1173331 := bstep (se 1 (by rfl) ⟨879998, by rfl⟩ : syracuseStep 1173331 = 1759997) B1759997
theorem B1173347 : Blo 1172403 1173347 := bstep (se 1 (by rfl) ⟨880010, by rfl⟩ : syracuseStep 1173347 = 1760021) B1760021
theorem B1484659 : Blo 1172403 1484659 := bstep (se 1 (by rfl) ⟨1113494, by rfl⟩ : syracuseStep 1484659 = 2226989) B2226989
theorem B1173363 : Blo 1172403 1173363 := bstep (se 1 (by rfl) ⟨880022, by rfl⟩ : syracuseStep 1173363 = 1760045) B1760045
theorem B2377603 : Blo 1172403 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B1173379 : Blo 1172403 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B1320835 : Blo 1172403 1320835 := bstep (se 1 (by rfl) ⟨990626, by rfl⟩ : syracuseStep 1320835 = 1981253) B1981253
theorem B1173395 : Blo 1172403 1173395 := bstep (se 1 (by rfl) ⟨880046, by rfl⟩ : syracuseStep 1173395 = 1760093) B1760093
theorem B1173411 : Blo 1172403 1173411 := bstep (se 1 (by rfl) ⟨880058, by rfl⟩ : syracuseStep 1173411 = 1760117) B1760117
theorem B5015459 : Blo 1172403 5015459 := bstep (se 1 (by rfl) ⟨3761594, by rfl⟩ : syracuseStep 5015459 = 7523189) B7523189
theorem B1173427 : Blo 1172403 1173427 := bstep (se 1 (by rfl) ⟨880070, by rfl⟩ : syracuseStep 1173427 = 1760141) B1760141
theorem B13371317 : Blo 1172403 13371317 := bstep (se 5 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 13371317 = 1253561) B1253561
theorem B1173443 : Blo 1172403 1173443 := bstep (se 1 (by rfl) ⟨880082, by rfl⟩ : syracuseStep 1173443 = 1760165) B1760165
theorem B2639825 : Blo 1172403 2639825 := bstep (se 2 (by rfl) ⟨989934, by rfl⟩ : syracuseStep 2639825 = 1979869) B1979869
theorem B1173459 : Blo 1172403 1173459 := bstep (se 1 (by rfl) ⟨880094, by rfl⟩ : syracuseStep 1173459 = 1760189) B1760189
theorem B2639843 : Blo 1172403 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B1173475 : Blo 1172403 1173475 := bstep (se 1 (by rfl) ⟨880106, by rfl⟩ : syracuseStep 1173475 = 1760213) B1760213
theorem B1173491 : Blo 1172403 1173491 := bstep (se 1 (by rfl) ⟨880118, by rfl⟩ : syracuseStep 1173491 = 1760237) B1760237
theorem B1173507 : Blo 1172403 1173507 := bstep (se 1 (by rfl) ⟨880130, by rfl⟩ : syracuseStep 1173507 = 1760261) B1760261
theorem B2115587 : Blo 1172403 2115587 := bstep (se 1 (by rfl) ⟨1586690, by rfl⟩ : syracuseStep 2115587 = 3173381) B3173381
theorem B1173523 : Blo 1172403 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B1320979 : Blo 1172403 1320979 := bstep (se 1 (by rfl) ⟨990734, by rfl⟩ : syracuseStep 1320979 = 1981469) B1981469
theorem B1173539 : Blo 1172403 1173539 := bstep (se 1 (by rfl) ⟨880154, by rfl⟩ : syracuseStep 1173539 = 1760309) B1760309
theorem B1173555 : Blo 1172403 1173555 := bstep (se 1 (by rfl) ⟨880166, by rfl⟩ : syracuseStep 1173555 = 1760333) B1760333
theorem B1173571 : Blo 1172403 1173571 := bstep (se 1 (by rfl) ⟨880178, by rfl⟩ : syracuseStep 1173571 = 1760357) B1760357
theorem B1173587 : Blo 1172403 1173587 := bstep (se 1 (by rfl) ⟨880190, by rfl⟩ : syracuseStep 1173587 = 1760381) B1760381
theorem B1173603 : Blo 1172403 1173603 := bstep (se 1 (by rfl) ⟨880202, by rfl⟩ : syracuseStep 1173603 = 1760405) B1760405
theorem B1173619 : Blo 1172403 1173619 := bstep (se 1 (by rfl) ⟨880214, by rfl⟩ : syracuseStep 1173619 = 1760429) B1760429
theorem B1173635 : Blo 1172403 1173635 := bstep (se 1 (by rfl) ⟨880226, by rfl⟩ : syracuseStep 1173635 = 1760453) B1760453
theorem B1173651 : Blo 1172403 1173651 := bstep (se 1 (by rfl) ⟨880238, by rfl⟩ : syracuseStep 1173651 = 1760477) B1760477
theorem B1173667 : Blo 1172403 1173667 := bstep (se 1 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 1173667 = 1760501) B1760501
theorem B1321123 : Blo 1172403 1321123 := bstep (se 1 (by rfl) ⟨990842, by rfl⟩ : syracuseStep 1321123 = 1981685) B1981685
theorem B1173683 : Blo 1172403 1173683 := bstep (se 1 (by rfl) ⟨880262, by rfl⟩ : syracuseStep 1173683 = 1760525) B1760525
theorem B1173699 : Blo 1172403 1173699 := bstep (se 1 (by rfl) ⟨880274, by rfl⟩ : syracuseStep 1173699 = 1760549) B1760549
theorem B6678733 : Blo 1172403 6678733 := bstep (se 3 (by rfl) ⟨1252262, by rfl⟩ : syracuseStep 6678733 = 2504525) B2504525
theorem B1173715 : Blo 1172403 1173715 := bstep (se 1 (by rfl) ⟨880286, by rfl⟩ : syracuseStep 1173715 = 1760573) B1760573
theorem B2967779 : Blo 1172403 2967779 := bstep (se 1 (by rfl) ⟨2225834, by rfl⟩ : syracuseStep 2967779 = 4451669) B4451669
theorem B1173731 : Blo 1172403 1173731 := bstep (se 1 (by rfl) ⟨880298, by rfl⟩ : syracuseStep 1173731 = 1760597) B1760597
theorem B2640113 : Blo 1172403 2640113 := bstep (se 2 (by rfl) ⟨990042, by rfl⟩ : syracuseStep 2640113 = 1980085) B1980085
theorem B1173747 : Blo 1172403 1173747 := bstep (se 1 (by rfl) ⟨880310, by rfl⟩ : syracuseStep 1173747 = 1760621) B1760621
theorem B2640131 : Blo 1172403 2640131 := bstep (se 1 (by rfl) ⟨1980098, by rfl⟩ : syracuseStep 2640131 = 3960197) B3960197
theorem B1173763 : Blo 1172403 1173763 := bstep (se 1 (by rfl) ⟨880322, by rfl⟩ : syracuseStep 1173763 = 1760645) B1760645
theorem B6686981 : Blo 1172403 6686981 := bstep (se 4 (by rfl) ⟨626904, by rfl⟩ : syracuseStep 6686981 = 1253809) B1253809
theorem B1173779 : Blo 1172403 1173779 := bstep (se 1 (by rfl) ⟨880334, by rfl⟩ : syracuseStep 1173779 = 1760669) B1760669
theorem B1173795 : Blo 1172403 1173795 := bstep (se 1 (by rfl) ⟨880346, by rfl⟩ : syracuseStep 1173795 = 1760693) B1760693
theorem B1173811 : Blo 1172403 1173811 := bstep (se 1 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 1173811 = 1760717) B1760717
theorem B1878337 : Blo 1172403 1878337 := bstep (se 2 (by rfl) ⟨704376, by rfl⟩ : syracuseStep 1878337 = 1408753) B1408753
theorem B1173827 : Blo 1172403 1173827 := bstep (se 1 (by rfl) ⟨880370, by rfl⟩ : syracuseStep 1173827 = 1760741) B1760741
theorem B3959117 : Blo 1172403 3959117 := bstep (se 3 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 3959117 = 1484669) B1484669
theorem B1173843 : Blo 1172403 1173843 := bstep (se 1 (by rfl) ⟨880382, by rfl⟩ : syracuseStep 1173843 = 1760765) B1760765
theorem B1485155 : Blo 1172403 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B1173859 : Blo 1172403 1173859 := bstep (se 1 (by rfl) ⟨880394, by rfl⟩ : syracuseStep 1173859 = 1760789) B1760789
theorem B1173875 : Blo 1172403 1173875 := bstep (se 1 (by rfl) ⟨880406, by rfl⟩ : syracuseStep 1173875 = 1760813) B1760813
theorem B3959171 : Blo 1172403 3959171 := bstep (se 1 (by rfl) ⟨2969378, by rfl⟩ : syracuseStep 3959171 = 5938757) B5938757
theorem B1173891 : Blo 1172403 1173891 := bstep (se 1 (by rfl) ⟨880418, by rfl⟩ : syracuseStep 1173891 = 1760837) B1760837
theorem B3664273 : Blo 1172403 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B1173907 : Blo 1172403 1173907 := bstep (se 1 (by rfl) ⟨880430, by rfl⟩ : syracuseStep 1173907 = 1760861) B1760861
theorem B1173923 : Blo 1172403 1173923 := bstep (se 1 (by rfl) ⟨880442, by rfl⟩ : syracuseStep 1173923 = 1760885) B1760885
theorem B1173939 : Blo 1172403 1173939 := bstep (se 1 (by rfl) ⟨880454, by rfl⟩ : syracuseStep 1173939 = 1760909) B1760909
theorem B1173955 : Blo 1172403 1173955 := bstep (se 1 (by rfl) ⟨880466, by rfl⟩ : syracuseStep 1173955 = 1760933) B1760933
theorem B1173971 : Blo 1172403 1173971 := bstep (se 1 (by rfl) ⟨880478, by rfl⟩ : syracuseStep 1173971 = 1760957) B1760957
theorem B1173987 : Blo 1172403 1173987 := bstep (se 1 (by rfl) ⟨880490, by rfl⟩ : syracuseStep 1173987 = 1760981) B1760981
theorem B3574253 : Blo 1172403 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B4229617 : Blo 1172403 4229617 := bstep (se 2 (by rfl) ⟨1586106, by rfl⟩ : syracuseStep 4229617 = 3172213) B3172213
theorem B1174003 : Blo 1172403 1174003 := bstep (se 1 (by rfl) ⟨880502, by rfl⟩ : syracuseStep 1174003 = 1761005) B1761005
theorem B1174019 : Blo 1172403 1174019 := bstep (se 1 (by rfl) ⟨880514, by rfl⟩ : syracuseStep 1174019 = 1761029) B1761029
theorem B2640401 : Blo 1172403 2640401 := bstep (se 2 (by rfl) ⟨990150, by rfl⟩ : syracuseStep 2640401 = 1980301) B1980301
theorem B1174035 : Blo 1172403 1174035 := bstep (se 1 (by rfl) ⟨880526, by rfl⟩ : syracuseStep 1174035 = 1761053) B1761053
theorem B2640419 : Blo 1172403 2640419 := bstep (se 1 (by rfl) ⟨1980314, by rfl⟩ : syracuseStep 2640419 = 3960629) B3960629
theorem B1174051 : Blo 1172403 1174051 := bstep (se 1 (by rfl) ⟨880538, by rfl⟩ : syracuseStep 1174051 = 1761077) B1761077
theorem B1174067 : Blo 1172403 1174067 := bstep (se 1 (by rfl) ⟨880550, by rfl⟩ : syracuseStep 1174067 = 1761101) B1761101
theorem B15026741 : Blo 1172403 15026741 := bstep (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) B1408757
theorem B1174083 : Blo 1172403 1174083 := bstep (se 1 (by rfl) ⟨880562, by rfl⟩ : syracuseStep 1174083 = 1761125) B1761125
theorem B1174099 : Blo 1172403 1174099 := bstep (se 1 (by rfl) ⟨880574, by rfl⟩ : syracuseStep 1174099 = 1761149) B1761149
theorem B2820707 : Blo 1172403 2820707 := bstep (se 1 (by rfl) ⟨2115530, by rfl⟩ : syracuseStep 2820707 = 4231061) B4231061
theorem B1174115 : Blo 1172403 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B1174131 : Blo 1172403 1174131 := bstep (se 1 (by rfl) ⟨880598, by rfl⟩ : syracuseStep 1174131 = 1761197) B1761197
theorem B1174147 : Blo 1172403 1174147 := bstep (se 1 (by rfl) ⟨880610, by rfl⟩ : syracuseStep 1174147 = 1761221) B1761221
theorem B3959441 : Blo 1172403 3959441 := bstep (se 2 (by rfl) ⟨1484790, by rfl⟩ : syracuseStep 3959441 = 2969581) B2969581
theorem B1174163 : Blo 1172403 1174163 := bstep (se 1 (by rfl) ⟨880622, by rfl⟩ : syracuseStep 1174163 = 1761245) B1761245
theorem B1174179 : Blo 1172403 1174179 := bstep (se 1 (by rfl) ⟨880634, by rfl⟩ : syracuseStep 1174179 = 1761269) B1761269
theorem B1174195 : Blo 1172403 1174195 := bstep (se 1 (by rfl) ⟨880646, by rfl⟩ : syracuseStep 1174195 = 1761293) B1761293
theorem B1174211 : Blo 1172403 1174211 := bstep (se 1 (by rfl) ⟨880658, by rfl⟩ : syracuseStep 1174211 = 1761317) B1761317
theorem B1174227 : Blo 1172403 1174227 := bstep (se 1 (by rfl) ⟨880670, by rfl⟩ : syracuseStep 1174227 = 1761341) B1761341
theorem B1174243 : Blo 1172403 1174243 := bstep (se 1 (by rfl) ⟨880682, by rfl⟩ : syracuseStep 1174243 = 1761365) B1761365
theorem B1174259 : Blo 1172403 1174259 := bstep (se 1 (by rfl) ⟨880694, by rfl⟩ : syracuseStep 1174259 = 1761389) B1761389
theorem B1174275 : Blo 1172403 1174275 := bstep (se 1 (by rfl) ⟨880706, by rfl⟩ : syracuseStep 1174275 = 1761413) B1761413
theorem B7138061 : Blo 1172403 7138061 := bstep (se 3 (by rfl) ⟨1338386, by rfl⟩ : syracuseStep 7138061 = 2676773) B2676773
theorem B1174291 : Blo 1172403 1174291 := bstep (se 1 (by rfl) ⟨880718, by rfl⟩ : syracuseStep 1174291 = 1761437) B1761437
theorem B1174307 : Blo 1172403 1174307 := bstep (se 1 (by rfl) ⟨880730, by rfl⟩ : syracuseStep 1174307 = 1761461) B1761461
theorem B3173165 : Blo 1172403 3173165 := bstep (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) B1189937
theorem B2640689 : Blo 1172403 2640689 := bstep (se 2 (by rfl) ⟨990258, by rfl⟩ : syracuseStep 2640689 = 1980517) B1980517
theorem B1174323 : Blo 1172403 1174323 := bstep (se 1 (by rfl) ⟨880742, by rfl⟩ : syracuseStep 1174323 = 1761485) B1761485
theorem B2640707 : Blo 1172403 2640707 := bstep (se 1 (by rfl) ⟨1980530, by rfl⟩ : syracuseStep 2640707 = 3961061) B3961061
theorem B1174339 : Blo 1172403 1174339 := bstep (se 1 (by rfl) ⟨880754, by rfl⟩ : syracuseStep 1174339 = 1761509) B1761509
theorem B1174355 : Blo 1172403 1174355 := bstep (se 1 (by rfl) ⟨880766, by rfl⟩ : syracuseStep 1174355 = 1761533) B1761533
theorem B1878881 : Blo 1172403 1878881 := bstep (se 2 (by rfl) ⟨704580, by rfl⟩ : syracuseStep 1878881 = 1409161) B1409161
theorem B1174371 : Blo 1172403 1174371 := bstep (se 1 (by rfl) ⟨880778, by rfl⟩ : syracuseStep 1174371 = 1761557) B1761557
theorem B1174387 : Blo 1172403 1174387 := bstep (se 1 (by rfl) ⟨880790, by rfl⟩ : syracuseStep 1174387 = 1761581) B1761581
theorem B1174403 : Blo 1172403 1174403 := bstep (se 1 (by rfl) ⟨880802, by rfl⟩ : syracuseStep 1174403 = 1761605) B1761605
theorem B2378659 : Blo 1172403 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B5499875 : Blo 1172403 5499875 := bstep (se 1 (by rfl) ⟨4124906, by rfl⟩ : syracuseStep 5499875 = 8249813) B8249813
theorem B1608707 : Blo 1172403 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B1485859 : Blo 1172403 1485859 := bstep (se 1 (by rfl) ⟨1114394, by rfl⟩ : syracuseStep 1485859 = 2228789) B2228789
theorem B5942321 : Blo 1172403 5942321 := bstep (se 2 (by rfl) ⟨2228370, by rfl⟩ : syracuseStep 5942321 = 4456741) B4456741
theorem B2640977 : Blo 1172403 2640977 := bstep (se 2 (by rfl) ⟨990366, by rfl⟩ : syracuseStep 2640977 = 1980733) B1980733
theorem B2640995 : Blo 1172403 2640995 := bstep (se 1 (by rfl) ⟨1980746, by rfl⟩ : syracuseStep 2640995 = 3961493) B3961493
theorem B1485955 : Blo 1172403 1485955 := bstep (se 1 (by rfl) ⟨1114466, by rfl⟩ : syracuseStep 1485955 = 2228933) B2228933
theorem B2968721 : Blo 1172403 2968721 := bstep (se 2 (by rfl) ⟨1113270, by rfl⟩ : syracuseStep 2968721 = 2226541) B2226541
theorem B1903763 : Blo 1172403 1903763 := bstep (se 1 (by rfl) ⟨1427822, by rfl⟩ : syracuseStep 1903763 = 2855645) B2855645
theorem B3959981 : Blo 1172403 3959981 := bstep (se 3 (by rfl) ⟨742496, by rfl⟩ : syracuseStep 3959981 = 1484993) B1484993
theorem B2968771 : Blo 1172403 2968771 := bstep (se 1 (by rfl) ⟨2226578, by rfl⟩ : syracuseStep 2968771 = 4453157) B4453157
theorem B3960035 : Blo 1172403 3960035 := bstep (se 1 (by rfl) ⟨2970026, by rfl⟩ : syracuseStep 3960035 = 5940053) B5940053
theorem B5008625 : Blo 1172403 5008625 := bstep (se 2 (by rfl) ⟨1878234, by rfl⟩ : syracuseStep 5008625 = 3756469) B3756469
theorem B16051441 : Blo 1172403 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B5008675 : Blo 1172403 5008675 := bstep (se 1 (by rfl) ⟨3756506, by rfl⟩ : syracuseStep 5008675 = 7513013) B7513013
theorem B2674001 : Blo 1172403 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B2968913 : Blo 1172403 2968913 := bstep (se 2 (by rfl) ⟨1113342, by rfl⟩ : syracuseStep 2968913 = 2226685) B2226685
theorem B2035057 : Blo 1172403 2035057 := bstep (se 2 (by rfl) ⟨763146, by rfl⟩ : syracuseStep 2035057 = 1526293) B1526293
theorem B2641265 : Blo 1172403 2641265 := bstep (se 2 (by rfl) ⟨990474, by rfl⟩ : syracuseStep 2641265 = 1980949) B1980949
theorem B2641283 : Blo 1172403 2641283 := bstep (se 1 (by rfl) ⟨1980962, by rfl⟩ : syracuseStep 2641283 = 3961925) B3961925
theorem B7523725 : Blo 1172403 7523725 := bstep (se 3 (by rfl) ⟨1410698, by rfl⟩ : syracuseStep 7523725 = 2821397) B2821397
theorem B2379217 : Blo 1172403 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B3960305 : Blo 1172403 3960305 := bstep (se 2 (by rfl) ⟨1485114, by rfl⟩ : syracuseStep 3960305 = 2970229) B2970229
theorem B3386893 : Blo 1172403 3386893 := bstep (se 3 (by rfl) ⟨635042, by rfl⟩ : syracuseStep 3386893 = 1270085) B1270085
theorem B3173987 : Blo 1172403 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B3616397 : Blo 1172403 3616397 := bstep (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) B1356149
theorem B2641553 : Blo 1172403 2641553 := bstep (se 2 (by rfl) ⟨990582, by rfl⟩ : syracuseStep 2641553 = 1981165) B1981165
theorem B2641571 : Blo 1172403 2641571 := bstep (se 1 (by rfl) ⟨1981178, by rfl⟩ : syracuseStep 2641571 = 3962357) B3962357
theorem B3174115 : Blo 1172403 3174115 := bstep (se 1 (by rfl) ⟨2380586, by rfl⟩ : syracuseStep 3174115 = 4761173) B4761173
theorem B5426957 : Blo 1172403 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B1879843 : Blo 1172403 1879843 := bstep (se 1 (by rfl) ⟨1409882, by rfl⟩ : syracuseStep 1879843 = 2819765) B2819765
theorem B13553477 : Blo 1172403 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B15249221 : Blo 1172403 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2641841 : Blo 1172403 2641841 := bstep (se 2 (by rfl) ⟨990690, by rfl⟩ : syracuseStep 2641841 = 1981381) B1981381
theorem B2641859 : Blo 1172403 2641859 := bstep (se 1 (by rfl) ⟨1981394, by rfl⟩ : syracuseStep 2641859 = 3962789) B3962789
theorem B3960845 : Blo 1172403 3960845 := bstep (se 3 (by rfl) ⟨742658, by rfl⟩ : syracuseStep 3960845 = 1485317) B1485317
theorem B1880099 : Blo 1172403 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B3960899 : Blo 1172403 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B1978465 : Blo 1172403 1978465 := bstep (se 2 (by rfl) ⟨741924, by rfl⟩ : syracuseStep 1978465 = 1483849) B1483849
theorem B1978499 : Blo 1172403 1978499 := bstep (se 1 (by rfl) ⟨1483874, by rfl⟩ : syracuseStep 1978499 = 2967749) B2967749
theorem B6680717 : Blo 1172403 6680717 := bstep (se 3 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 6680717 = 2505269) B2505269
theorem B2642129 : Blo 1172403 2642129 := bstep (se 2 (by rfl) ⟨990798, by rfl⟩ : syracuseStep 2642129 = 1981597) B1981597
theorem B2642147 : Blo 1172403 2642147 := bstep (se 1 (by rfl) ⟨1981610, by rfl⟩ : syracuseStep 2642147 = 3963221) B3963221
theorem B1978627 : Blo 1172403 1978627 := bstep (se 1 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 1978627 = 2967941) B2967941
theorem B2969905 : Blo 1172403 2969905 := bstep (se 2 (by rfl) ⟨1113714, by rfl⟩ : syracuseStep 2969905 = 2227429) B2227429
theorem B19042613 : Blo 1172403 19042613 := bstep (se 5 (by rfl) ⟨892622, by rfl⟩ : syracuseStep 19042613 = 1785245) B1785245
theorem B3961169 : Blo 1172403 3961169 := bstep (se 2 (by rfl) ⟨1485438, by rfl⟩ : syracuseStep 3961169 = 2970877) B2970877
theorem B4231565 : Blo 1172403 4231565 := bstep (se 3 (by rfl) ⟨793418, by rfl⟩ : syracuseStep 4231565 = 1586837) B1586837
theorem B1978769 : Blo 1172403 1978769 := bstep (se 2 (by rfl) ⟨742038, by rfl⟩ : syracuseStep 1978769 = 1484077) B1484077
theorem B5943779 : Blo 1172403 5943779 := bstep (se 1 (by rfl) ⟨4457834, by rfl⟩ : syracuseStep 5943779 = 8915669) B8915669
theorem B1978897 : Blo 1172403 1978897 := bstep (se 2 (by rfl) ⟨742086, by rfl⟩ : syracuseStep 1978897 = 1484173) B1484173
theorem B1978931 : Blo 1172403 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B21688885 : Blo 1172403 21688885 := bstep (se 5 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 21688885 = 2033333) B2033333
theorem B2970179 : Blo 1172403 2970179 := bstep (se 1 (by rfl) ⟨2227634, by rfl⟩ : syracuseStep 2970179 = 4455269) B4455269
theorem B1979059 : Blo 1172403 1979059 := bstep (se 1 (by rfl) ⟨1484294, by rfl⟩ : syracuseStep 1979059 = 2968589) B2968589
theorem B3338957 : Blo 1172403 3338957 := bstep (se 3 (by rfl) ⟨626054, by rfl⟩ : syracuseStep 3338957 = 1252109) B1252109
theorem B1880803 : Blo 1172403 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B2970371 : Blo 1172403 2970371 := bstep (se 1 (by rfl) ⟨2227778, by rfl⟩ : syracuseStep 2970371 = 4455557) B4455557
theorem B1979201 : Blo 1172403 1979201 := bstep (se 2 (by rfl) ⟨742200, by rfl⟩ : syracuseStep 1979201 = 1484401) B1484401
theorem B3961709 : Blo 1172403 3961709 := bstep (se 3 (by rfl) ⟨742820, by rfl⟩ : syracuseStep 3961709 = 1485641) B1485641
theorem B3339139 : Blo 1172403 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B3961763 : Blo 1172403 3961763 := bstep (se 1 (by rfl) ⟨2971322, by rfl⟩ : syracuseStep 3961763 = 5942645) B5942645
theorem B1979329 : Blo 1172403 1979329 := bstep (se 2 (by rfl) ⟨742248, by rfl⟩ : syracuseStep 1979329 = 1484497) B1484497
theorem B4453325 : Blo 1172403 4453325 := bstep (se 3 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 4453325 = 1669997) B1669997
theorem B1979363 : Blo 1172403 1979363 := bstep (se 1 (by rfl) ⟨1484522, by rfl⟩ : syracuseStep 1979363 = 2969045) B2969045
theorem B1881073 : Blo 1172403 1881073 := bstep (se 2 (by rfl) ⟨705402, by rfl⟩ : syracuseStep 1881073 = 1410805) B1410805
theorem B8909837 : Blo 1172403 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B3339299 : Blo 1172403 3339299 := bstep (se 1 (by rfl) ⟨2504474, by rfl⟩ : syracuseStep 3339299 = 5008949) B5008949
theorem B6681649 : Blo 1172403 6681649 := bstep (se 2 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 6681649 = 5011237) B5011237
theorem B1881137 : Blo 1172403 1881137 := bstep (se 2 (by rfl) ⟨705426, by rfl⟩ : syracuseStep 1881137 = 1410853) B1410853
theorem B1979491 : Blo 1172403 1979491 := bstep (se 1 (by rfl) ⟨1484618, by rfl⟩ : syracuseStep 1979491 = 2969237) B2969237
theorem B2675825 : Blo 1172403 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B3962033 : Blo 1172403 3962033 := bstep (se 2 (by rfl) ⟨1485762, by rfl⟩ : syracuseStep 3962033 = 2971525) B2971525
theorem B1979633 : Blo 1172403 1979633 := bstep (se 2 (by rfl) ⟨742362, by rfl⟩ : syracuseStep 1979633 = 1484725) B1484725
theorem B5944589 : Blo 1172403 5944589 := bstep (se 3 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 5944589 = 2229221) B2229221
theorem B1979761 : Blo 1172403 1979761 := bstep (se 2 (by rfl) ⟨742410, by rfl⟩ : syracuseStep 1979761 = 1484821) B1484821
theorem B2504081 : Blo 1172403 2504081 := bstep (se 2 (by rfl) ⟨939030, by rfl⟩ : syracuseStep 2504081 = 1878061) B1878061
theorem B1758611 : Blo 1172403 1758611 := bstep (se 1 (by rfl) ⟨1318958, by rfl⟩ : syracuseStep 1758611 = 2637917) B2637917
theorem B1979795 : Blo 1172403 1979795 := bstep (se 1 (by rfl) ⟨1484846, by rfl⟩ : syracuseStep 1979795 = 2969693) B2969693
theorem B1758641 : Blo 1172403 1758641 := bstep (se 2 (by rfl) ⟨659490, by rfl⟩ : syracuseStep 1758641 = 1318981) B1318981
theorem B1758659 : Blo 1172403 1758659 := bstep (se 1 (by rfl) ⟨1318994, by rfl⟩ : syracuseStep 1758659 = 2637989) B2637989
theorem B25368005 : Blo 1172403 25368005 := bstep (se 4 (by rfl) ⟨2378250, by rfl⟩ : syracuseStep 25368005 = 4756501) B4756501
theorem B1758689 : Blo 1172403 1758689 := bstep (se 2 (by rfl) ⟨659508, by rfl⟩ : syracuseStep 1758689 = 1319017) B1319017
theorem B1758707 : Blo 1172403 1758707 := bstep (se 1 (by rfl) ⟨1319030, by rfl⟩ : syracuseStep 1758707 = 2638061) B2638061
theorem B1758737 : Blo 1172403 1758737 := bstep (se 2 (by rfl) ⟨659526, by rfl⟩ : syracuseStep 1758737 = 1319053) B1319053
theorem B1979923 : Blo 1172403 1979923 := bstep (se 1 (by rfl) ⟨1484942, by rfl⟩ : syracuseStep 1979923 = 2969885) B2969885
theorem B1758755 : Blo 1172403 1758755 := bstep (se 1 (by rfl) ⟨1319066, by rfl⟩ : syracuseStep 1758755 = 2638133) B2638133
theorem B1758785 : Blo 1172403 1758785 := bstep (se 2 (by rfl) ⟨659544, by rfl⟩ : syracuseStep 1758785 = 1319089) B1319089
theorem B6346309 : Blo 1172403 6346309 := bstep (se 4 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 6346309 = 1189933) B1189933
theorem B1758803 : Blo 1172403 1758803 := bstep (se 1 (by rfl) ⟨1319102, by rfl⟩ : syracuseStep 1758803 = 2638205) B2638205
theorem B1758833 : Blo 1172403 1758833 := bstep (se 2 (by rfl) ⟨659562, by rfl⟩ : syracuseStep 1758833 = 1319125) B1319125
theorem B1758851 : Blo 1172403 1758851 := bstep (se 1 (by rfl) ⟨1319138, by rfl⟩ : syracuseStep 1758851 = 2638277) B2638277
theorem B5011085 : Blo 1172403 5011085 := bstep (se 3 (by rfl) ⟨939578, by rfl⟩ : syracuseStep 5011085 = 1879157) B1879157
theorem B1758881 : Blo 1172403 1758881 := bstep (se 2 (by rfl) ⟨659580, by rfl⟩ : syracuseStep 1758881 = 1319161) B1319161
theorem B1980065 : Blo 1172403 1980065 := bstep (se 2 (by rfl) ⟨742524, by rfl⟩ : syracuseStep 1980065 = 1485049) B1485049
theorem B2971313 : Blo 1172403 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B1758899 : Blo 1172403 1758899 := bstep (se 1 (by rfl) ⟨1319174, by rfl⟩ : syracuseStep 1758899 = 2638349) B2638349
theorem B3962573 : Blo 1172403 3962573 := bstep (se 3 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 3962573 = 1485965) B1485965
theorem B2225873 : Blo 1172403 2225873 := bstep (se 2 (by rfl) ⟨834702, by rfl⟩ : syracuseStep 2225873 = 1669405) B1669405
theorem B1758929 : Blo 1172403 1758929 := bstep (se 2 (by rfl) ⟨659598, by rfl⟩ : syracuseStep 1758929 = 1319197) B1319197
theorem B1758947 : Blo 1172403 1758947 := bstep (se 1 (by rfl) ⟨1319210, by rfl⟩ : syracuseStep 1758947 = 2638421) B2638421
theorem B2971363 : Blo 1172403 2971363 := bstep (se 1 (by rfl) ⟨2228522, by rfl⟩ : syracuseStep 2971363 = 4457045) B4457045
theorem B4454129 : Blo 1172403 4454129 := bstep (se 2 (by rfl) ⟨1670298, by rfl⟩ : syracuseStep 4454129 = 3340597) B3340597
theorem B1758977 : Blo 1172403 1758977 := bstep (se 2 (by rfl) ⟨659616, by rfl⟩ : syracuseStep 1758977 = 1319233) B1319233
theorem B3962627 : Blo 1172403 3962627 := bstep (se 1 (by rfl) ⟨2971970, by rfl⟩ : syracuseStep 3962627 = 5943941) B5943941
theorem B1758995 : Blo 1172403 1758995 := bstep (se 1 (by rfl) ⟨1319246, by rfl⟩ : syracuseStep 1758995 = 2638493) B2638493
theorem B1980193 : Blo 1172403 1980193 := bstep (se 2 (by rfl) ⟨742572, by rfl⟩ : syracuseStep 1980193 = 1485145) B1485145
theorem B1759025 : Blo 1172403 1759025 := bstep (se 2 (by rfl) ⟨659634, by rfl⟩ : syracuseStep 1759025 = 1319269) B1319269
theorem B1759043 : Blo 1172403 1759043 := bstep (se 1 (by rfl) ⟨1319282, by rfl⟩ : syracuseStep 1759043 = 2638565) B2638565
theorem B1980227 : Blo 1172403 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B1718083 : Blo 1172403 1718083 := bstep (se 1 (by rfl) ⟨1288562, by rfl⟩ : syracuseStep 1718083 = 2577125) B2577125
theorem B1759073 : Blo 1172403 1759073 := bstep (se 2 (by rfl) ⟨659652, by rfl⟩ : syracuseStep 1759073 = 1319305) B1319305
theorem B2971505 : Blo 1172403 2971505 := bstep (se 2 (by rfl) ⟨1114314, by rfl⟩ : syracuseStep 2971505 = 2228629) B2228629
theorem B1759091 : Blo 1172403 1759091 := bstep (se 1 (by rfl) ⟨1319318, by rfl⟩ : syracuseStep 1759091 = 2638637) B2638637
theorem B1759121 : Blo 1172403 1759121 := bstep (se 2 (by rfl) ⟨659670, by rfl⟩ : syracuseStep 1759121 = 1319341) B1319341
theorem B2504611 : Blo 1172403 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B1759139 : Blo 1172403 1759139 := bstep (se 1 (by rfl) ⟨1319354, by rfl⟩ : syracuseStep 1759139 = 2638709) B2638709
theorem B1759169 : Blo 1172403 1759169 := bstep (se 2 (by rfl) ⟨659688, by rfl⟩ : syracuseStep 1759169 = 1319377) B1319377
theorem B1980355 : Blo 1172403 1980355 := bstep (se 1 (by rfl) ⟨1485266, by rfl⟩ : syracuseStep 1980355 = 2970533) B2970533
theorem B1759187 : Blo 1172403 1759187 := bstep (se 1 (by rfl) ⟨1319390, by rfl⟩ : syracuseStep 1759187 = 2638781) B2638781
theorem B8574947 : Blo 1172403 8574947 := bstep (se 1 (by rfl) ⟨6431210, by rfl⟩ : syracuseStep 8574947 = 12862421) B12862421
theorem B9517027 : Blo 1172403 9517027 := bstep (se 1 (by rfl) ⟨7137770, by rfl⟩ : syracuseStep 9517027 = 14275541) B14275541
theorem B6191075 : Blo 1172403 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B5937137 : Blo 1172403 5937137 := bstep (se 2 (by rfl) ⟨2226426, by rfl⟩ : syracuseStep 5937137 = 4452853) B4452853
theorem B1759217 : Blo 1172403 1759217 := bstep (se 2 (by rfl) ⟨659706, by rfl⟩ : syracuseStep 1759217 = 1319413) B1319413
theorem B1759235 : Blo 1172403 1759235 := bstep (se 1 (by rfl) ⟨1319426, by rfl⟩ : syracuseStep 1759235 = 2638853) B2638853
theorem B1783811 : Blo 1172403 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B7133197 : Blo 1172403 7133197 := bstep (se 3 (by rfl) ⟨1337474, by rfl⟩ : syracuseStep 7133197 = 2674949) B2674949
theorem B8034317 : Blo 1172403 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B3962897 : Blo 1172403 3962897 := bstep (se 2 (by rfl) ⟨1486086, by rfl⟩ : syracuseStep 3962897 = 2972173) B2972173
theorem B1759265 : Blo 1172403 1759265 := bstep (se 2 (by rfl) ⟨659724, by rfl⟩ : syracuseStep 1759265 = 1319449) B1319449
theorem B1759283 : Blo 1172403 1759283 := bstep (se 1 (by rfl) ⟨1319462, by rfl⟩ : syracuseStep 1759283 = 2638925) B2638925
theorem B3758147 : Blo 1172403 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1759313 : Blo 1172403 1759313 := bstep (se 2 (by rfl) ⟨659742, by rfl⟩ : syracuseStep 1759313 = 1319485) B1319485
theorem B3340369 : Blo 1172403 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B1980497 : Blo 1172403 1980497 := bstep (se 2 (by rfl) ⟨742686, by rfl⟩ : syracuseStep 1980497 = 1485373) B1485373
theorem B2226275 : Blo 1172403 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B1759331 : Blo 1172403 1759331 := bstep (se 1 (by rfl) ⟨1319498, by rfl⟩ : syracuseStep 1759331 = 2638997) B2638997
theorem B3012707 : Blo 1172403 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B1759361 : Blo 1172403 1759361 := bstep (se 2 (by rfl) ⟨659760, by rfl⟩ : syracuseStep 1759361 = 1319521) B1319521
theorem B1759379 : Blo 1172403 1759379 := bstep (se 1 (by rfl) ⟨1319534, by rfl⟩ : syracuseStep 1759379 = 2639069) B2639069
theorem B1759409 : Blo 1172403 1759409 := bstep (se 2 (by rfl) ⟨659778, by rfl⟩ : syracuseStep 1759409 = 1319557) B1319557
theorem B1759427 : Blo 1172403 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B1980625 : Blo 1172403 1980625 := bstep (se 2 (by rfl) ⟨742734, by rfl⟩ : syracuseStep 1980625 = 1485469) B1485469
theorem B1759457 : Blo 1172403 1759457 := bstep (se 2 (by rfl) ⟨659796, by rfl⟩ : syracuseStep 1759457 = 1319593) B1319593
theorem B1759475 : Blo 1172403 1759475 := bstep (se 1 (by rfl) ⟨1319606, by rfl⟩ : syracuseStep 1759475 = 2639213) B2639213
theorem B1980659 : Blo 1172403 1980659 := bstep (se 1 (by rfl) ⟨1485494, by rfl⟩ : syracuseStep 1980659 = 2970989) B2970989
theorem B1759505 : Blo 1172403 1759505 := bstep (se 2 (by rfl) ⟨659814, by rfl⟩ : syracuseStep 1759505 = 1319629) B1319629
theorem B1759523 : Blo 1172403 1759523 := bstep (se 1 (by rfl) ⟨1319642, by rfl⟩ : syracuseStep 1759523 = 2639285) B2639285
theorem B1759553 : Blo 1172403 1759553 := bstep (se 2 (by rfl) ⟨659832, by rfl⟩ : syracuseStep 1759553 = 1319665) B1319665
theorem B1759571 : Blo 1172403 1759571 := bstep (se 1 (by rfl) ⟨1319678, by rfl⟩ : syracuseStep 1759571 = 2639357) B2639357
theorem B1759601 : Blo 1172403 1759601 := bstep (se 2 (by rfl) ⟨659850, by rfl⟩ : syracuseStep 1759601 = 1319701) B1319701
theorem B1980787 : Blo 1172403 1980787 := bstep (se 1 (by rfl) ⟨1485590, by rfl⟩ : syracuseStep 1980787 = 2971181) B2971181
theorem B1759619 : Blo 1172403 1759619 := bstep (se 1 (by rfl) ⟨1319714, by rfl⟩ : syracuseStep 1759619 = 2639429) B2639429
theorem B4454797 : Blo 1172403 4454797 := bstep (se 3 (by rfl) ⟨835274, by rfl⟩ : syracuseStep 4454797 = 1670549) B1670549
theorem B1759649 : Blo 1172403 1759649 := bstep (se 2 (by rfl) ⟨659868, by rfl⟩ : syracuseStep 1759649 = 1319737) B1319737
theorem B1759667 : Blo 1172403 1759667 := bstep (se 1 (by rfl) ⟨1319750, by rfl⟩ : syracuseStep 1759667 = 2639501) B2639501
theorem B1759697 : Blo 1172403 1759697 := bstep (se 2 (by rfl) ⟨659886, by rfl⟩ : syracuseStep 1759697 = 1319773) B1319773
theorem B1759715 : Blo 1172403 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B6683107 : Blo 1172403 6683107 := bstep (se 1 (by rfl) ⟨5012330, by rfl⟩ : syracuseStep 6683107 = 10024661) B10024661
theorem B16062947 : Blo 1172403 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B1759745 : Blo 1172403 1759745 := bstep (se 2 (by rfl) ⟨659904, by rfl⟩ : syracuseStep 1759745 = 1319809) B1319809
theorem B1980929 : Blo 1172403 1980929 := bstep (se 2 (by rfl) ⟨742848, by rfl⟩ : syracuseStep 1980929 = 1485697) B1485697
theorem B1759763 : Blo 1172403 1759763 := bstep (se 1 (by rfl) ⟨1319822, by rfl⟩ : syracuseStep 1759763 = 2639645) B2639645
theorem B3963437 : Blo 1172403 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B1759793 : Blo 1172403 1759793 := bstep (se 2 (by rfl) ⟨659922, by rfl⟩ : syracuseStep 1759793 = 1319845) B1319845
theorem B2005555 : Blo 1172403 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B1759811 : Blo 1172403 1759811 := bstep (se 1 (by rfl) ⟨1319858, by rfl⟩ : syracuseStep 1759811 = 2639717) B2639717
theorem B1669729 : Blo 1172403 1669729 := bstep (se 2 (by rfl) ⟨626148, by rfl⟩ : syracuseStep 1669729 = 1252297) B1252297
theorem B1759841 : Blo 1172403 1759841 := bstep (se 2 (by rfl) ⟨659940, by rfl⟩ : syracuseStep 1759841 = 1319881) B1319881
theorem B2005603 : Blo 1172403 2005603 := bstep (se 1 (by rfl) ⟨1504202, by rfl⟩ : syracuseStep 2005603 = 3008405) B3008405
theorem B1505891 : Blo 1172403 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B3963491 : Blo 1172403 3963491 := bstep (se 1 (by rfl) ⟨2972618, by rfl⟩ : syracuseStep 3963491 = 5945237) B5945237
theorem B1759859 : Blo 1172403 1759859 := bstep (se 1 (by rfl) ⟨1319894, by rfl⟩ : syracuseStep 1759859 = 2639789) B2639789
theorem B1981057 : Blo 1172403 1981057 := bstep (se 2 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 1981057 = 1485793) B1485793
theorem B1759889 : Blo 1172403 1759889 := bstep (se 2 (by rfl) ⟨659958, by rfl⟩ : syracuseStep 1759889 = 1319917) B1319917
theorem B1784467 : Blo 1172403 1784467 := bstep (se 1 (by rfl) ⟨1338350, by rfl⟩ : syracuseStep 1784467 = 2676701) B2676701
theorem B1759907 : Blo 1172403 1759907 := bstep (se 1 (by rfl) ⟨1319930, by rfl⟩ : syracuseStep 1759907 = 2639861) B2639861
theorem B1981091 : Blo 1172403 1981091 := bstep (se 1 (by rfl) ⟨1485818, by rfl⟩ : syracuseStep 1981091 = 2971637) B2971637
theorem B2005681 : Blo 1172403 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B1759937 : Blo 1172403 1759937 := bstep (se 2 (by rfl) ⟨659976, by rfl⟩ : syracuseStep 1759937 = 1319953) B1319953
theorem B4012753 : Blo 1172403 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B1669843 : Blo 1172403 1669843 := bstep (se 1 (by rfl) ⟨1252382, by rfl⟩ : syracuseStep 1669843 = 2504765) B2504765
theorem B1759955 : Blo 1172403 1759955 := bstep (se 1 (by rfl) ⟨1319966, by rfl⟩ : syracuseStep 1759955 = 2639933) B2639933
theorem B1759985 : Blo 1172403 1759985 := bstep (se 2 (by rfl) ⟨659994, by rfl⟩ : syracuseStep 1759985 = 1319989) B1319989
theorem B1760003 : Blo 1172403 1760003 := bstep (se 1 (by rfl) ⟨1320002, by rfl⟩ : syracuseStep 1760003 = 2640005) B2640005
theorem B1760033 : Blo 1172403 1760033 := bstep (se 2 (by rfl) ⟨660012, by rfl⟩ : syracuseStep 1760033 = 1320025) B1320025
theorem B1981219 : Blo 1172403 1981219 := bstep (se 1 (by rfl) ⟨1485914, by rfl⟩ : syracuseStep 1981219 = 2971829) B2971829
theorem B1760051 : Blo 1172403 1760051 := bstep (se 1 (by rfl) ⟨1320038, by rfl⟩ : syracuseStep 1760051 = 2640077) B2640077
theorem B1760081 : Blo 1172403 1760081 := bstep (se 2 (by rfl) ⟨660030, by rfl⟩ : syracuseStep 1760081 = 1320061) B1320061
theorem B2972497 : Blo 1172403 2972497 := bstep (se 2 (by rfl) ⟨1114686, by rfl⟩ : syracuseStep 2972497 = 2229373) B2229373
theorem B1760099 : Blo 1172403 1760099 := bstep (se 1 (by rfl) ⟨1320074, by rfl⟩ : syracuseStep 1760099 = 2640149) B2640149
theorem B1760129 : Blo 1172403 1760129 := bstep (se 2 (by rfl) ⟨660048, by rfl⟩ : syracuseStep 1760129 = 1320097) B1320097
theorem B3758993 : Blo 1172403 3758993 := bstep (se 2 (by rfl) ⟨1409622, by rfl⟩ : syracuseStep 3758993 = 2819245) B2819245
theorem B1760147 : Blo 1172403 1760147 := bstep (se 1 (by rfl) ⟨1320110, by rfl⟩ : syracuseStep 1760147 = 2640221) B2640221
theorem B1760177 : Blo 1172403 1760177 := bstep (se 2 (by rfl) ⟨660066, by rfl⟩ : syracuseStep 1760177 = 1320133) B1320133
theorem B1981361 : Blo 1172403 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B1932211 : Blo 1172403 1932211 := bstep (se 1 (by rfl) ⟨1449158, by rfl⟩ : syracuseStep 1932211 = 2898317) B2898317
theorem B3759043 : Blo 1172403 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B1760195 : Blo 1172403 1760195 := bstep (se 1 (by rfl) ⟨1320146, by rfl⟩ : syracuseStep 1760195 = 2640293) B2640293
theorem B1760225 : Blo 1172403 1760225 := bstep (se 2 (by rfl) ⟨660084, by rfl⟩ : syracuseStep 1760225 = 1320169) B1320169
theorem B2227171 : Blo 1172403 2227171 := bstep (se 1 (by rfl) ⟨1670378, by rfl⟩ : syracuseStep 2227171 = 3340757) B3340757
theorem B6683633 : Blo 1172403 6683633 := bstep (se 2 (by rfl) ⟨2506362, by rfl⟩ : syracuseStep 6683633 = 5012725) B5012725
theorem B1760243 : Blo 1172403 1760243 := bstep (se 1 (by rfl) ⟨1320182, by rfl⟩ : syracuseStep 1760243 = 2640365) B2640365
theorem B1760273 : Blo 1172403 1760273 := bstep (se 2 (by rfl) ⟨660102, by rfl⟩ : syracuseStep 1760273 = 1320205) B1320205
theorem B1760291 : Blo 1172403 1760291 := bstep (se 1 (by rfl) ⟨1320218, by rfl⟩ : syracuseStep 1760291 = 2640437) B2640437
theorem B1981489 : Blo 1172403 1981489 := bstep (se 2 (by rfl) ⟨743058, by rfl⟩ : syracuseStep 1981489 = 1486117) B1486117
theorem B1760321 : Blo 1172403 1760321 := bstep (se 2 (by rfl) ⟨660120, by rfl⟩ : syracuseStep 1760321 = 1320241) B1320241
theorem B3619921 : Blo 1172403 3619921 := bstep (se 2 (by rfl) ⟨1357470, by rfl⟩ : syracuseStep 3619921 = 2714941) B2714941
theorem B1760339 : Blo 1172403 1760339 := bstep (se 1 (by rfl) ⟨1320254, by rfl⟩ : syracuseStep 1760339 = 2640509) B2640509
theorem B1981523 : Blo 1172403 1981523 := bstep (se 1 (by rfl) ⟨1486142, by rfl⟩ : syracuseStep 1981523 = 2972285) B2972285
theorem B1760369 : Blo 1172403 1760369 := bstep (se 2 (by rfl) ⟨660138, by rfl⟩ : syracuseStep 1760369 = 1320277) B1320277
theorem B2227331 : Blo 1172403 2227331 := bstep (se 1 (by rfl) ⟨1670498, by rfl⟩ : syracuseStep 2227331 = 3340997) B3340997
theorem B1760387 : Blo 1172403 1760387 := bstep (se 1 (by rfl) ⟨1320290, by rfl⟩ : syracuseStep 1760387 = 2640581) B2640581
theorem B1760417 : Blo 1172403 1760417 := bstep (se 2 (by rfl) ⟨660156, by rfl⟩ : syracuseStep 1760417 = 1320313) B1320313
theorem B4455587 : Blo 1172403 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B1760435 : Blo 1172403 1760435 := bstep (se 1 (by rfl) ⟨1320326, by rfl⟩ : syracuseStep 1760435 = 2640653) B2640653
theorem B1760465 : Blo 1172403 1760465 := bstep (se 2 (by rfl) ⟨660174, by rfl⟩ : syracuseStep 1760465 = 1320349) B1320349
theorem B1981651 : Blo 1172403 1981651 := bstep (se 1 (by rfl) ⟨1486238, by rfl⟩ : syracuseStep 1981651 = 2972477) B2972477
theorem B1252579 : Blo 1172403 1252579 := bstep (se 1 (by rfl) ⟨939434, by rfl⟩ : syracuseStep 1252579 = 1878869) B1878869
theorem B1760483 : Blo 1172403 1760483 := bstep (se 1 (by rfl) ⟨1320362, by rfl⟩ : syracuseStep 1760483 = 2640725) B2640725
theorem B1760513 : Blo 1172403 1760513 := bstep (se 2 (by rfl) ⟨660192, by rfl⟩ : syracuseStep 1760513 = 1320385) B1320385
theorem B1760531 : Blo 1172403 1760531 := bstep (se 1 (by rfl) ⟨1320398, by rfl⟩ : syracuseStep 1760531 = 2640797) B2640797
theorem B3570979 : Blo 1172403 3570979 := bstep (se 1 (by rfl) ⟨2678234, by rfl⟩ : syracuseStep 3570979 = 5356469) B5356469
theorem B1760561 : Blo 1172403 1760561 := bstep (se 2 (by rfl) ⟨660210, by rfl⟩ : syracuseStep 1760561 = 1320421) B1320421
theorem B1760579 : Blo 1172403 1760579 := bstep (se 1 (by rfl) ⟨1320434, by rfl⟩ : syracuseStep 1760579 = 2640869) B2640869
theorem B8904005 : Blo 1172403 8904005 := bstep (se 4 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 8904005 = 1669501) B1669501
theorem B3341645 : Blo 1172403 3341645 := bstep (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) B1253117
theorem B1760609 : Blo 1172403 1760609 := bstep (se 2 (by rfl) ⟨660228, by rfl⟩ : syracuseStep 1760609 = 1320457) B1320457
theorem B1981793 : Blo 1172403 1981793 := bstep (se 2 (by rfl) ⟨743172, by rfl⟩ : syracuseStep 1981793 = 1486345) B1486345
theorem B2506097 : Blo 1172403 2506097 := bstep (se 2 (by rfl) ⟨939786, by rfl⟩ : syracuseStep 2506097 = 1879573) B1879573
theorem B1760627 : Blo 1172403 1760627 := bstep (se 1 (by rfl) ⟨1320470, by rfl⟩ : syracuseStep 1760627 = 2640941) B2640941
theorem B2506115 : Blo 1172403 2506115 := bstep (se 1 (by rfl) ⟨1879586, by rfl⟩ : syracuseStep 2506115 = 3759173) B3759173
theorem B3571075 : Blo 1172403 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B1760657 : Blo 1172403 1760657 := bstep (se 2 (by rfl) ⟨660246, by rfl⟩ : syracuseStep 1760657 = 1320493) B1320493
theorem B5938595 : Blo 1172403 5938595 := bstep (se 1 (by rfl) ⟨4453946, by rfl⟩ : syracuseStep 5938595 = 8907893) B8907893
theorem B1760675 : Blo 1172403 1760675 := bstep (se 1 (by rfl) ⟨1320506, by rfl⟩ : syracuseStep 1760675 = 2641013) B2641013
theorem B1760705 : Blo 1172403 1760705 := bstep (se 2 (by rfl) ⟨660264, by rfl⟩ : syracuseStep 1760705 = 1320529) B1320529
theorem B1760723 : Blo 1172403 1760723 := bstep (se 1 (by rfl) ⟨1320542, by rfl⟩ : syracuseStep 1760723 = 2641085) B2641085
theorem B1760753 : Blo 1172403 1760753 := bstep (se 2 (by rfl) ⟨660282, by rfl⟩ : syracuseStep 1760753 = 1320565) B1320565
theorem B3341827 : Blo 1172403 3341827 := bstep (se 1 (by rfl) ⟨2506370, by rfl⟩ : syracuseStep 3341827 = 5012741) B5012741
theorem B1760771 : Blo 1172403 1760771 := bstep (se 1 (by rfl) ⟨1320578, by rfl⟩ : syracuseStep 1760771 = 2641157) B2641157
theorem B1760801 : Blo 1172403 1760801 := bstep (se 2 (by rfl) ⟨660300, by rfl⟩ : syracuseStep 1760801 = 1320601) B1320601
theorem B3341873 : Blo 1172403 3341873 := bstep (se 2 (by rfl) ⟨1253202, by rfl⟩ : syracuseStep 3341873 = 2506405) B2506405
theorem B1760819 : Blo 1172403 1760819 := bstep (se 1 (by rfl) ⟨1320614, by rfl⟩ : syracuseStep 1760819 = 2641229) B2641229
theorem B1760849 : Blo 1172403 1760849 := bstep (se 2 (by rfl) ⟨660318, by rfl⟩ : syracuseStep 1760849 = 1320637) B1320637
theorem B1760867 : Blo 1172403 1760867 := bstep (se 1 (by rfl) ⟨1320650, by rfl⟩ : syracuseStep 1760867 = 2641301) B2641301
theorem B1760897 : Blo 1172403 1760897 := bstep (se 2 (by rfl) ⟨660336, by rfl⟩ : syracuseStep 1760897 = 1320673) B1320673
theorem B1760915 : Blo 1172403 1760915 := bstep (se 1 (by rfl) ⟨1320686, by rfl⟩ : syracuseStep 1760915 = 2641373) B2641373
theorem B3169955 : Blo 1172403 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B1760945 : Blo 1172403 1760945 := bstep (se 2 (by rfl) ⟨660354, by rfl⟩ : syracuseStep 1760945 = 1320709) B1320709
theorem B1760963 : Blo 1172403 1760963 := bstep (se 1 (by rfl) ⟨1320722, by rfl⟩ : syracuseStep 1760963 = 2641445) B2641445
theorem B1760993 : Blo 1172403 1760993 := bstep (se 2 (by rfl) ⟨660372, by rfl⟩ : syracuseStep 1760993 = 1320745) B1320745
theorem B7519985 : Blo 1172403 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B1761011 : Blo 1172403 1761011 := bstep (se 1 (by rfl) ⟨1320758, by rfl⟩ : syracuseStep 1761011 = 2641517) B2641517
theorem B1761041 : Blo 1172403 1761041 := bstep (se 2 (by rfl) ⟨660390, by rfl⟩ : syracuseStep 1761041 = 1320781) B1320781
theorem B1761059 : Blo 1172403 1761059 := bstep (se 1 (by rfl) ⟨1320794, by rfl⟩ : syracuseStep 1761059 = 2641589) B2641589
theorem B4456241 : Blo 1172403 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B1761089 : Blo 1172403 1761089 := bstep (se 2 (by rfl) ⟨660408, by rfl⟩ : syracuseStep 1761089 = 1320817) B1320817
theorem B1761107 : Blo 1172403 1761107 := bstep (se 1 (by rfl) ⟨1320830, by rfl⟩ : syracuseStep 1761107 = 2641661) B2641661
theorem B8912753 : Blo 1172403 8912753 := bstep (se 2 (by rfl) ⟨3342282, by rfl⟩ : syracuseStep 8912753 = 6684565) B6684565
theorem B1761137 : Blo 1172403 1761137 := bstep (se 2 (by rfl) ⟨660426, by rfl⟩ : syracuseStep 1761137 = 1320853) B1320853
theorem B1761155 : Blo 1172403 1761155 := bstep (se 1 (by rfl) ⟨1320866, by rfl⟩ : syracuseStep 1761155 = 2641733) B2641733
theorem B1761185 : Blo 1172403 1761185 := bstep (se 2 (by rfl) ⟨660444, by rfl⟩ : syracuseStep 1761185 = 1320889) B1320889
theorem B4226993 : Blo 1172403 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B7618481 : Blo 1172403 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B1761203 : Blo 1172403 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B1761233 : Blo 1172403 1761233 := bstep (se 2 (by rfl) ⟨660462, by rfl⟩ : syracuseStep 1761233 = 1320925) B1320925
theorem B4513763 : Blo 1172403 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B1761251 : Blo 1172403 1761251 := bstep (se 1 (by rfl) ⟨1320938, by rfl⟩ : syracuseStep 1761251 = 2641877) B2641877
theorem B9510929 : Blo 1172403 9510929 := bstep (se 2 (by rfl) ⟨3566598, by rfl⟩ : syracuseStep 9510929 = 7133197) B7133197
theorem B1253399 : Blo 1172403 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B2228249 : Blo 1172403 2228249 := bstep (se 2 (by rfl) ⟨835593, by rfl⟩ : syracuseStep 2228249 = 1671187) B1671187
theorem B1761305 : Blo 1172403 1761305 := bstep (se 2 (by rfl) ⟨660489, by rfl⟩ : syracuseStep 1761305 = 1320979) B1320979
theorem B1318999 : Blo 1172403 1318999 := bstep (se 1 (by rfl) ⟨989249, by rfl⟩ : syracuseStep 1318999 = 1978499) B1978499
theorem B2637953 : Blo 1172403 2637953 := bstep (se 2 (by rfl) ⟨989232, by rfl⟩ : syracuseStep 2637953 = 1978465) B1978465
theorem B1761419 : Blo 1172403 1761419 := bstep (se 1 (by rfl) ⟨1321064, by rfl⟩ : syracuseStep 1761419 = 2642129) B2642129
theorem B1761431 : Blo 1172403 1761431 := bstep (se 1 (by rfl) ⟨1321073, by rfl⟩ : syracuseStep 1761431 = 2642147) B2642147
theorem B5013683 : Blo 1172403 5013683 := bstep (se 1 (by rfl) ⟨3760262, by rfl⟩ : syracuseStep 5013683 = 7520525) B7520525
theorem B2539735 : Blo 1172403 2539735 := bstep (se 1 (by rfl) ⟨1904801, by rfl⟩ : syracuseStep 2539735 = 3809603) B3809603
theorem B1761497 : Blo 1172403 1761497 := bstep (se 2 (by rfl) ⟨660561, by rfl⟩ : syracuseStep 1761497 = 1321123) B1321123
theorem B3956957 : Blo 1172403 3956957 := bstep (se 3 (by rfl) ⟨741929, by rfl⟩ : syracuseStep 3956957 = 1483859) B1483859
theorem B1319179 : Blo 1172403 1319179 := bstep (se 1 (by rfl) ⟨989384, by rfl⟩ : syracuseStep 1319179 = 1978769) B1978769
theorem B8904977 : Blo 1172403 8904977 := bstep (se 2 (by rfl) ⟨3339366, by rfl⟩ : syracuseStep 8904977 = 6678733) B6678733
theorem B4456727 : Blo 1172403 4456727 := bstep (se 1 (by rfl) ⟨3342545, by rfl⟩ : syracuseStep 4456727 = 6685091) B6685091
theorem B2638169 : Blo 1172403 2638169 := bstep (se 2 (by rfl) ⟨989313, by rfl⟩ : syracuseStep 2638169 = 1978627) B1978627
theorem B1319287 : Blo 1172403 1319287 := bstep (se 1 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 1319287 = 1978931) B1978931
theorem B1671563 : Blo 1172403 1671563 := bstep (se 1 (by rfl) ⟨1253672, by rfl⟩ : syracuseStep 1671563 = 2507345) B2507345
theorem B2638259 : Blo 1172403 2638259 := bstep (se 1 (by rfl) ⟨1978694, by rfl⟩ : syracuseStep 2638259 = 3957389) B3957389
theorem B2638295 : Blo 1172403 2638295 := bstep (se 1 (by rfl) ⟨1978721, by rfl⟩ : syracuseStep 2638295 = 3957443) B3957443
theorem B5939729 : Blo 1172403 5939729 := bstep (se 2 (by rfl) ⟨2227398, by rfl⟩ : syracuseStep 5939729 = 4454797) B4454797
theorem B2818583 : Blo 1172403 2818583 := bstep (se 1 (by rfl) ⟨2113937, by rfl⟩ : syracuseStep 2818583 = 4227875) B4227875
theorem B1319467 : Blo 1172403 1319467 := bstep (se 1 (by rfl) ⟨989600, by rfl⟩ : syracuseStep 1319467 = 1979201) B1979201
theorem B2638475 : Blo 1172403 2638475 := bstep (se 1 (by rfl) ⟨1978856, by rfl⟩ : syracuseStep 2638475 = 3957713) B3957713
theorem B1319575 : Blo 1172403 1319575 := bstep (se 1 (by rfl) ⟨989681, by rfl⟩ : syracuseStep 1319575 = 1979363) B1979363
theorem B2228887 : Blo 1172403 2228887 := bstep (se 1 (by rfl) ⟨1671665, by rfl⟩ : syracuseStep 2228887 = 3343331) B3343331
theorem B5939891 : Blo 1172403 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B2638529 : Blo 1172403 2638529 := bstep (se 2 (by rfl) ⟨989448, by rfl⟩ : syracuseStep 2638529 = 1978897) B1978897
theorem B1254091 : Blo 1172403 1254091 := bstep (se 1 (by rfl) ⟨940568, by rfl⟩ : syracuseStep 1254091 = 1881137) B1881137
theorem B28918513 : Blo 1172403 28918513 := bstep (se 2 (by rfl) ⟨10844442, by rfl⟩ : syracuseStep 28918513 = 21688885) B21688885
theorem B20054789 : Blo 1172403 20054789 := bstep (se 4 (by rfl) ⟨1880136, by rfl⟩ : syracuseStep 20054789 = 3760273) B3760273
theorem B1319755 : Blo 1172403 1319755 := bstep (se 1 (by rfl) ⟨989816, by rfl⟩ : syracuseStep 1319755 = 1979633) B1979633
theorem B2507635 : Blo 1172403 2507635 := bstep (se 1 (by rfl) ⟨1880726, by rfl⟩ : syracuseStep 2507635 = 3761453) B3761453
theorem B2638745 : Blo 1172403 2638745 := bstep (se 2 (by rfl) ⟨989529, by rfl⟩ : syracuseStep 2638745 = 1979059) B1979059
theorem B1172407 : Blo 1172403 1172407 := bstep (se 1 (by rfl) ⟨879305, by rfl⟩ : syracuseStep 1172407 = 1758611) B1758611
theorem B1319863 : Blo 1172403 1319863 := bstep (se 1 (by rfl) ⟨989897, by rfl⟩ : syracuseStep 1319863 = 1979795) B1979795
theorem B5350337 : Blo 1172403 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B1172427 : Blo 1172403 1172427 := bstep (se 1 (by rfl) ⟨879320, by rfl⟩ : syracuseStep 1172427 = 1758641) B1758641
theorem B2540491 : Blo 1172403 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B1172439 : Blo 1172403 1172439 := bstep (se 1 (by rfl) ⟨879329, by rfl⟩ : syracuseStep 1172439 = 1758659) B1758659
theorem B1172459 : Blo 1172403 1172459 := bstep (se 1 (by rfl) ⟨879344, by rfl⟩ : syracuseStep 1172459 = 1758689) B1758689
theorem B2638835 : Blo 1172403 2638835 := bstep (se 1 (by rfl) ⟨1979126, by rfl⟩ : syracuseStep 2638835 = 3958253) B3958253
theorem B1172471 : Blo 1172403 1172471 := bstep (se 1 (by rfl) ⟨879353, by rfl⟩ : syracuseStep 1172471 = 1758707) B1758707
theorem B1172491 : Blo 1172403 1172491 := bstep (se 1 (by rfl) ⟨879368, by rfl⟩ : syracuseStep 1172491 = 1758737) B1758737
theorem B1172503 : Blo 1172403 1172503 := bstep (se 1 (by rfl) ⟨879377, by rfl⟩ : syracuseStep 1172503 = 1758755) B1758755
theorem B2638871 : Blo 1172403 2638871 := bstep (se 1 (by rfl) ⟨1979153, by rfl⟩ : syracuseStep 2638871 = 3958307) B3958307
theorem B1172523 : Blo 1172403 1172523 := bstep (se 1 (by rfl) ⟨879392, by rfl⟩ : syracuseStep 1172523 = 1758785) B1758785
theorem B6677549 : Blo 1172403 6677549 := bstep (se 3 (by rfl) ⟨1252040, by rfl⟩ : syracuseStep 6677549 = 2504081) B2504081
theorem B1172535 : Blo 1172403 1172535 := bstep (se 1 (by rfl) ⟨879401, by rfl⟩ : syracuseStep 1172535 = 1758803) B1758803
theorem B1172555 : Blo 1172403 1172555 := bstep (se 1 (by rfl) ⟨879416, by rfl⟩ : syracuseStep 1172555 = 1758833) B1758833
theorem B1172567 : Blo 1172403 1172567 := bstep (se 1 (by rfl) ⟨879425, by rfl⟩ : syracuseStep 1172567 = 1758851) B1758851
theorem B1172587 : Blo 1172403 1172587 := bstep (se 1 (by rfl) ⟨879440, by rfl⟩ : syracuseStep 1172587 = 1758881) B1758881
theorem B1320043 : Blo 1172403 1320043 := bstep (se 1 (by rfl) ⟨990032, by rfl⟩ : syracuseStep 1320043 = 1980065) B1980065
theorem B1172599 : Blo 1172403 1172599 := bstep (se 1 (by rfl) ⟨879449, by rfl⟩ : syracuseStep 1172599 = 1758899) B1758899
theorem B1483915 : Blo 1172403 1483915 := bstep (se 1 (by rfl) ⟨1112936, by rfl⟩ : syracuseStep 1483915 = 2225873) B2225873
theorem B1172619 : Blo 1172403 1172619 := bstep (se 1 (by rfl) ⟨879464, by rfl⟩ : syracuseStep 1172619 = 1758929) B1758929
theorem B1172631 : Blo 1172403 1172631 := bstep (se 1 (by rfl) ⟨879473, by rfl⟩ : syracuseStep 1172631 = 1758947) B1758947
theorem B1172651 : Blo 1172403 1172651 := bstep (se 1 (by rfl) ⟨879488, by rfl⟩ : syracuseStep 1172651 = 1758977) B1758977
theorem B1172663 : Blo 1172403 1172663 := bstep (se 1 (by rfl) ⟨879497, by rfl⟩ : syracuseStep 1172663 = 1758995) B1758995
theorem B1172683 : Blo 1172403 1172683 := bstep (se 1 (by rfl) ⟨879512, by rfl⟩ : syracuseStep 1172683 = 1759025) B1759025
theorem B2639051 : Blo 1172403 2639051 := bstep (se 1 (by rfl) ⟨1979288, by rfl⟩ : syracuseStep 2639051 = 3958577) B3958577
theorem B1172695 : Blo 1172403 1172695 := bstep (se 1 (by rfl) ⟨879521, by rfl⟩ : syracuseStep 1172695 = 1759043) B1759043
theorem B1320151 : Blo 1172403 1320151 := bstep (se 1 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 1320151 = 1980227) B1980227
theorem B3171545 : Blo 1172403 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B1172715 : Blo 1172403 1172715 := bstep (se 1 (by rfl) ⟨879536, by rfl⟩ : syracuseStep 1172715 = 1759073) B1759073
theorem B1172727 : Blo 1172403 1172727 := bstep (se 1 (by rfl) ⟨879545, by rfl⟩ : syracuseStep 1172727 = 1759091) B1759091
theorem B2639105 : Blo 1172403 2639105 := bstep (se 2 (by rfl) ⟨989664, by rfl⟩ : syracuseStep 2639105 = 1979329) B1979329
theorem B1172747 : Blo 1172403 1172747 := bstep (se 1 (by rfl) ⟨879560, by rfl⟩ : syracuseStep 1172747 = 1759121) B1759121
theorem B1172759 : Blo 1172403 1172759 := bstep (se 1 (by rfl) ⟨879569, by rfl⟩ : syracuseStep 1172759 = 1759139) B1759139
theorem B3343639 : Blo 1172403 3343639 := bstep (se 1 (by rfl) ⟨2507729, by rfl⟩ : syracuseStep 3343639 = 5015459) B5015459
theorem B8914211 : Blo 1172403 8914211 := bstep (se 1 (by rfl) ⟨6685658, by rfl⟩ : syracuseStep 8914211 = 13371317) B13371317
theorem B1172779 : Blo 1172403 1172779 := bstep (se 1 (by rfl) ⟨879584, by rfl⟩ : syracuseStep 1172779 = 1759169) B1759169
theorem B1172791 : Blo 1172403 1172791 := bstep (se 1 (by rfl) ⟨879593, by rfl⟩ : syracuseStep 1172791 = 1759187) B1759187
theorem B2508097 : Blo 1172403 2508097 := bstep (se 2 (by rfl) ⟨940536, by rfl⟩ : syracuseStep 2508097 = 1881073) B1881073
theorem B3958091 : Blo 1172403 3958091 := bstep (se 1 (by rfl) ⟨2968568, by rfl⟩ : syracuseStep 3958091 = 5937137) B5937137
theorem B1172811 : Blo 1172403 1172811 := bstep (se 1 (by rfl) ⟨879608, by rfl⟩ : syracuseStep 1172811 = 1759217) B1759217
theorem B1172823 : Blo 1172403 1172823 := bstep (se 1 (by rfl) ⟨879617, by rfl⟩ : syracuseStep 1172823 = 1759235) B1759235
theorem B1189207 : Blo 1172403 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B1410391 : Blo 1172403 1410391 := bstep (se 1 (by rfl) ⟨1057793, by rfl⟩ : syracuseStep 1410391 = 2115587) B2115587
theorem B1172843 : Blo 1172403 1172843 := bstep (se 1 (by rfl) ⟨879632, by rfl⟩ : syracuseStep 1172843 = 1759265) B1759265
theorem B1172855 : Blo 1172403 1172855 := bstep (se 1 (by rfl) ⟨879641, by rfl⟩ : syracuseStep 1172855 = 1759283) B1759283
theorem B1172875 : Blo 1172403 1172875 := bstep (se 1 (by rfl) ⟨879656, by rfl⟩ : syracuseStep 1172875 = 1759313) B1759313
theorem B1320331 : Blo 1172403 1320331 := bstep (se 1 (by rfl) ⟨990248, by rfl⟩ : syracuseStep 1320331 = 1980497) B1980497
theorem B1484183 : Blo 1172403 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B1172887 : Blo 1172403 1172887 := bstep (se 1 (by rfl) ⟨879665, by rfl⟩ : syracuseStep 1172887 = 1759331) B1759331
theorem B2008471 : Blo 1172403 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B1172907 : Blo 1172403 1172907 := bstep (se 1 (by rfl) ⟨879680, by rfl⟩ : syracuseStep 1172907 = 1759361) B1759361
theorem B1172919 : Blo 1172403 1172919 := bstep (se 1 (by rfl) ⟨879689, by rfl⟩ : syracuseStep 1172919 = 1759379) B1759379
theorem B4826561 : Blo 1172403 4826561 := bstep (se 2 (by rfl) ⟨1809960, by rfl⟩ : syracuseStep 4826561 = 3619921) B3619921
theorem B1172939 : Blo 1172403 1172939 := bstep (se 1 (by rfl) ⟨879704, by rfl⟩ : syracuseStep 1172939 = 1759409) B1759409
theorem B1172951 : Blo 1172403 1172951 := bstep (se 1 (by rfl) ⟨879713, by rfl⟩ : syracuseStep 1172951 = 1759427) B1759427
theorem B2639321 : Blo 1172403 2639321 := bstep (se 2 (by rfl) ⟨989745, by rfl⟩ : syracuseStep 2639321 = 1979491) B1979491
theorem B1172971 : Blo 1172403 1172971 := bstep (se 1 (by rfl) ⟨879728, by rfl⟩ : syracuseStep 1172971 = 1759457) B1759457
theorem B1172983 : Blo 1172403 1172983 := bstep (se 1 (by rfl) ⟨879737, by rfl⟩ : syracuseStep 1172983 = 1759475) B1759475
theorem B1320439 : Blo 1172403 1320439 := bstep (se 1 (by rfl) ⟨990329, by rfl⟩ : syracuseStep 1320439 = 1980659) B1980659
theorem B4457987 : Blo 1172403 4457987 := bstep (se 1 (by rfl) ⟨3343490, by rfl⟩ : syracuseStep 4457987 = 6686981) B6686981
theorem B1173003 : Blo 1172403 1173003 := bstep (se 1 (by rfl) ⟨879752, by rfl⟩ : syracuseStep 1173003 = 1759505) B1759505
theorem B1173015 : Blo 1172403 1173015 := bstep (se 1 (by rfl) ⟨879761, by rfl⟩ : syracuseStep 1173015 = 1759523) B1759523
theorem B1173035 : Blo 1172403 1173035 := bstep (se 1 (by rfl) ⟨879776, by rfl⟩ : syracuseStep 1173035 = 1759553) B1759553
theorem B2639411 : Blo 1172403 2639411 := bstep (se 1 (by rfl) ⟨1979558, by rfl⟩ : syracuseStep 2639411 = 3959117) B3959117
theorem B1173047 : Blo 1172403 1173047 := bstep (se 1 (by rfl) ⟨879785, by rfl⟩ : syracuseStep 1173047 = 1759571) B1759571
theorem B1173067 : Blo 1172403 1173067 := bstep (se 1 (by rfl) ⟨879800, by rfl⟩ : syracuseStep 1173067 = 1759601) B1759601
theorem B1173079 : Blo 1172403 1173079 := bstep (se 1 (by rfl) ⟨879809, by rfl⟩ : syracuseStep 1173079 = 1759619) B1759619
theorem B2639447 : Blo 1172403 2639447 := bstep (se 1 (by rfl) ⟨1979585, by rfl⟩ : syracuseStep 2639447 = 3959171) B3959171
theorem B3958361 : Blo 1172403 3958361 := bstep (se 2 (by rfl) ⟨1484385, by rfl⟩ : syracuseStep 3958361 = 2968771) B2968771
theorem B4015709 : Blo 1172403 4015709 := bstep (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) B1505891
theorem B1173099 : Blo 1172403 1173099 := bstep (se 1 (by rfl) ⟨879824, by rfl⟩ : syracuseStep 1173099 = 1759649) B1759649
theorem B1173111 : Blo 1172403 1173111 := bstep (se 1 (by rfl) ⟨879833, by rfl⟩ : syracuseStep 1173111 = 1759667) B1759667
theorem B1173131 : Blo 1172403 1173131 := bstep (se 1 (by rfl) ⟨879848, by rfl⟩ : syracuseStep 1173131 = 1759697) B1759697
theorem B1173143 : Blo 1172403 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B10708631 : Blo 1172403 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B1173163 : Blo 1172403 1173163 := bstep (se 1 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 1173163 = 1759745) B1759745
theorem B1320619 : Blo 1172403 1320619 := bstep (se 1 (by rfl) ⟨990464, by rfl⟩ : syracuseStep 1320619 = 1980929) B1980929
theorem B1173175 : Blo 1172403 1173175 := bstep (se 1 (by rfl) ⟨879881, by rfl⟩ : syracuseStep 1173175 = 1759763) B1759763
theorem B1173195 : Blo 1172403 1173195 := bstep (se 1 (by rfl) ⟨879896, by rfl⟩ : syracuseStep 1173195 = 1759793) B1759793
theorem B1173207 : Blo 1172403 1173207 := bstep (se 1 (by rfl) ⟨879905, by rfl⟩ : syracuseStep 1173207 = 1759811) B1759811
theorem B6678233 : Blo 1172403 6678233 := bstep (se 2 (by rfl) ⟨2504337, by rfl⟩ : syracuseStep 6678233 = 5008675) B5008675
theorem B4761305 : Blo 1172403 4761305 := bstep (se 2 (by rfl) ⟨1785489, by rfl⟩ : syracuseStep 4761305 = 3570979) B3570979
theorem B1173227 : Blo 1172403 1173227 := bstep (se 1 (by rfl) ⟨879920, by rfl⟩ : syracuseStep 1173227 = 1759841) B1759841
theorem B1173239 : Blo 1172403 1173239 := bstep (se 1 (by rfl) ⟨879929, by rfl⟩ : syracuseStep 1173239 = 1759859) B1759859
theorem B2639627 : Blo 1172403 2639627 := bstep (se 1 (by rfl) ⟨1979720, by rfl⟩ : syracuseStep 2639627 = 3959441) B3959441
theorem B1173259 : Blo 1172403 1173259 := bstep (se 1 (by rfl) ⟨879944, by rfl⟩ : syracuseStep 1173259 = 1759889) B1759889
theorem B1173271 : Blo 1172403 1173271 := bstep (se 1 (by rfl) ⟨879953, by rfl⟩ : syracuseStep 1173271 = 1759907) B1759907
theorem B1320727 : Blo 1172403 1320727 := bstep (se 1 (by rfl) ⟨990545, by rfl⟩ : syracuseStep 1320727 = 1981091) B1981091
theorem B1173291 : Blo 1172403 1173291 := bstep (se 1 (by rfl) ⟨879968, by rfl⟩ : syracuseStep 1173291 = 1759937) B1759937
theorem B1173303 : Blo 1172403 1173303 := bstep (se 1 (by rfl) ⟨879977, by rfl⟩ : syracuseStep 1173303 = 1759955) B1759955
theorem B2639681 : Blo 1172403 2639681 := bstep (se 2 (by rfl) ⟨989880, by rfl⟩ : syracuseStep 2639681 = 1979761) B1979761
theorem B2713409 : Blo 1172403 2713409 := bstep (se 2 (by rfl) ⟨1017528, by rfl⟩ : syracuseStep 2713409 = 2035057) B2035057
theorem B1173323 : Blo 1172403 1173323 := bstep (se 1 (by rfl) ⟨879992, by rfl⟩ : syracuseStep 1173323 = 1759985) B1759985
theorem B1173335 : Blo 1172403 1173335 := bstep (se 1 (by rfl) ⟨880001, by rfl⟩ : syracuseStep 1173335 = 1760003) B1760003
theorem B4761433 : Blo 1172403 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B1173355 : Blo 1172403 1173355 := bstep (se 1 (by rfl) ⟨880016, by rfl⟩ : syracuseStep 1173355 = 1760033) B1760033
theorem B2115443 : Blo 1172403 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B1173367 : Blo 1172403 1173367 := bstep (se 1 (by rfl) ⟨880025, by rfl⟩ : syracuseStep 1173367 = 1760051) B1760051
theorem B1173387 : Blo 1172403 1173387 := bstep (se 1 (by rfl) ⟨880040, by rfl⟩ : syracuseStep 1173387 = 1760081) B1760081
theorem B1173399 : Blo 1172403 1173399 := bstep (se 1 (by rfl) ⟨880049, by rfl⟩ : syracuseStep 1173399 = 1760099) B1760099
theorem B1173419 : Blo 1172403 1173419 := bstep (se 1 (by rfl) ⟨880064, by rfl⟩ : syracuseStep 1173419 = 1760129) B1760129
theorem B1173431 : Blo 1172403 1173431 := bstep (se 1 (by rfl) ⟨880073, by rfl⟩ : syracuseStep 1173431 = 1760147) B1760147
theorem B3172289 : Blo 1172403 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B1173451 : Blo 1172403 1173451 := bstep (se 1 (by rfl) ⟨880088, by rfl⟩ : syracuseStep 1173451 = 1760177) B1760177
theorem B1320907 : Blo 1172403 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B1173463 : Blo 1172403 1173463 := bstep (se 1 (by rfl) ⟨880097, by rfl⟩ : syracuseStep 1173463 = 1760195) B1760195
theorem B1173483 : Blo 1172403 1173483 := bstep (se 1 (by rfl) ⟨880112, by rfl⟩ : syracuseStep 1173483 = 1760225) B1760225
theorem B1173495 : Blo 1172403 1173495 := bstep (se 1 (by rfl) ⟨880121, by rfl⟩ : syracuseStep 1173495 = 1760243) B1760243
theorem B1173515 : Blo 1172403 1173515 := bstep (se 1 (by rfl) ⟨880136, by rfl⟩ : syracuseStep 1173515 = 1760273) B1760273
theorem B4515857 : Blo 1172403 4515857 := bstep (se 2 (by rfl) ⟨1693446, by rfl⟩ : syracuseStep 4515857 = 3386893) B3386893
theorem B2639897 : Blo 1172403 2639897 := bstep (se 2 (by rfl) ⟨989961, by rfl⟩ : syracuseStep 2639897 = 1979923) B1979923
theorem B1173527 : Blo 1172403 1173527 := bstep (se 1 (by rfl) ⟨880145, by rfl⟩ : syracuseStep 1173527 = 1760291) B1760291
theorem B1173547 : Blo 1172403 1173547 := bstep (se 1 (by rfl) ⟨880160, by rfl⟩ : syracuseStep 1173547 = 1760321) B1760321
theorem B1173559 : Blo 1172403 1173559 := bstep (se 1 (by rfl) ⟨880169, by rfl⟩ : syracuseStep 1173559 = 1760339) B1760339
theorem B1321015 : Blo 1172403 1321015 := bstep (se 1 (by rfl) ⟨990761, by rfl⟩ : syracuseStep 1321015 = 1981523) B1981523
theorem B1173579 : Blo 1172403 1173579 := bstep (se 1 (by rfl) ⟨880184, by rfl⟩ : syracuseStep 1173579 = 1760369) B1760369
theorem B1484887 : Blo 1172403 1484887 := bstep (se 1 (by rfl) ⟨1113665, by rfl⟩ : syracuseStep 1484887 = 2227331) B2227331
theorem B1173591 : Blo 1172403 1173591 := bstep (se 1 (by rfl) ⟨880193, by rfl⟩ : syracuseStep 1173591 = 1760387) B1760387
theorem B1173611 : Blo 1172403 1173611 := bstep (se 1 (by rfl) ⟨880208, by rfl⟩ : syracuseStep 1173611 = 1760417) B1760417
theorem B2639987 : Blo 1172403 2639987 := bstep (se 1 (by rfl) ⟨1979990, by rfl⟩ : syracuseStep 2639987 = 3959981) B3959981
theorem B1173623 : Blo 1172403 1173623 := bstep (se 1 (by rfl) ⟨880217, by rfl⟩ : syracuseStep 1173623 = 1760435) B1760435
theorem B1173643 : Blo 1172403 1173643 := bstep (se 1 (by rfl) ⟨880232, by rfl⟩ : syracuseStep 1173643 = 1760465) B1760465
theorem B2640023 : Blo 1172403 2640023 := bstep (se 1 (by rfl) ⟨1980017, by rfl⟩ : syracuseStep 2640023 = 3960035) B3960035
theorem B1173655 : Blo 1172403 1173655 := bstep (se 1 (by rfl) ⟨880241, by rfl⟩ : syracuseStep 1173655 = 1760483) B1760483
theorem B1173675 : Blo 1172403 1173675 := bstep (se 1 (by rfl) ⟨880256, by rfl⟩ : syracuseStep 1173675 = 1760513) B1760513
theorem B1173687 : Blo 1172403 1173687 := bstep (se 1 (by rfl) ⟨880265, by rfl⟩ : syracuseStep 1173687 = 1760531) B1760531
theorem B1173707 : Blo 1172403 1173707 := bstep (se 1 (by rfl) ⟨880280, by rfl⟩ : syracuseStep 1173707 = 1760561) B1760561
theorem B1173719 : Blo 1172403 1173719 := bstep (se 1 (by rfl) ⟨880289, by rfl⟩ : syracuseStep 1173719 = 1760579) B1760579
theorem B1173739 : Blo 1172403 1173739 := bstep (se 1 (by rfl) ⟨880304, by rfl⟩ : syracuseStep 1173739 = 1760609) B1760609
theorem B1321195 : Blo 1172403 1321195 := bstep (se 1 (by rfl) ⟨990896, by rfl⟩ : syracuseStep 1321195 = 1981793) B1981793
theorem B1173751 : Blo 1172403 1173751 := bstep (se 1 (by rfl) ⟨880313, by rfl⟩ : syracuseStep 1173751 = 1760627) B1760627
theorem B1173771 : Blo 1172403 1173771 := bstep (se 1 (by rfl) ⟨880328, by rfl⟩ : syracuseStep 1173771 = 1760657) B1760657
theorem B3959063 : Blo 1172403 3959063 := bstep (se 1 (by rfl) ⟨2969297, by rfl⟩ : syracuseStep 3959063 = 5938595) B5938595
theorem B1173783 : Blo 1172403 1173783 := bstep (se 1 (by rfl) ⟨880337, by rfl⟩ : syracuseStep 1173783 = 1760675) B1760675
theorem B1173803 : Blo 1172403 1173803 := bstep (se 1 (by rfl) ⟨880352, by rfl⟩ : syracuseStep 1173803 = 1760705) B1760705
theorem B1173815 : Blo 1172403 1173815 := bstep (se 1 (by rfl) ⟨880361, by rfl⟩ : syracuseStep 1173815 = 1760723) B1760723
theorem B2640203 : Blo 1172403 2640203 := bstep (se 1 (by rfl) ⟨1980152, by rfl⟩ : syracuseStep 2640203 = 3960305) B3960305
theorem B1173835 : Blo 1172403 1173835 := bstep (se 1 (by rfl) ⟨880376, by rfl⟩ : syracuseStep 1173835 = 1760753) B1760753
theorem B1173847 : Blo 1172403 1173847 := bstep (se 1 (by rfl) ⟨880385, by rfl⟩ : syracuseStep 1173847 = 1760771) B1760771
theorem B1173867 : Blo 1172403 1173867 := bstep (se 1 (by rfl) ⟨880400, by rfl⟩ : syracuseStep 1173867 = 1760801) B1760801
theorem B1173879 : Blo 1172403 1173879 := bstep (se 1 (by rfl) ⟨880409, by rfl⟩ : syracuseStep 1173879 = 1760819) B1760819
theorem B2640257 : Blo 1172403 2640257 := bstep (se 2 (by rfl) ⟨990096, by rfl⟩ : syracuseStep 2640257 = 1980193) B1980193
theorem B1173899 : Blo 1172403 1173899 := bstep (se 1 (by rfl) ⟨880424, by rfl⟩ : syracuseStep 1173899 = 1760849) B1760849
theorem B1173911 : Blo 1172403 1173911 := bstep (se 1 (by rfl) ⟨880433, by rfl⟩ : syracuseStep 1173911 = 1760867) B1760867
theorem B2115991 : Blo 1172403 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B1173931 : Blo 1172403 1173931 := bstep (se 1 (by rfl) ⟨880448, by rfl⟩ : syracuseStep 1173931 = 1760897) B1760897
theorem B2410931 : Blo 1172403 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B1173943 : Blo 1172403 1173943 := bstep (se 1 (by rfl) ⟨880457, by rfl⟩ : syracuseStep 1173943 = 1760915) B1760915
theorem B1173963 : Blo 1172403 1173963 := bstep (se 1 (by rfl) ⟨880472, by rfl⟩ : syracuseStep 1173963 = 1760945) B1760945
theorem B1173975 : Blo 1172403 1173975 := bstep (se 1 (by rfl) ⟨880481, by rfl⟩ : syracuseStep 1173975 = 1760963) B1760963
theorem B1173995 : Blo 1172403 1173995 := bstep (se 1 (by rfl) ⟨880496, by rfl⟩ : syracuseStep 1173995 = 1760993) B1760993
theorem B1174007 : Blo 1172403 1174007 := bstep (se 1 (by rfl) ⟨880505, by rfl⟩ : syracuseStep 1174007 = 1761011) B1761011
theorem B1174027 : Blo 1172403 1174027 := bstep (se 1 (by rfl) ⟨880520, by rfl⟩ : syracuseStep 1174027 = 1761041) B1761041
theorem B1174039 : Blo 1172403 1174039 := bstep (se 1 (by rfl) ⟨880529, by rfl⟩ : syracuseStep 1174039 = 1761059) B1761059
theorem B1174059 : Blo 1172403 1174059 := bstep (se 1 (by rfl) ⟨880544, by rfl⟩ : syracuseStep 1174059 = 1761089) B1761089
theorem B1174071 : Blo 1172403 1174071 := bstep (se 1 (by rfl) ⟨880553, by rfl⟩ : syracuseStep 1174071 = 1761107) B1761107
theorem B5941835 : Blo 1172403 5941835 := bstep (se 1 (by rfl) ⟨4456376, by rfl⟩ : syracuseStep 5941835 = 8912753) B8912753
theorem B1174091 : Blo 1172403 1174091 := bstep (se 1 (by rfl) ⟨880568, by rfl⟩ : syracuseStep 1174091 = 1761137) B1761137
theorem B1174103 : Blo 1172403 1174103 := bstep (se 1 (by rfl) ⟨880577, by rfl⟩ : syracuseStep 1174103 = 1761155) B1761155
theorem B2640473 : Blo 1172403 2640473 := bstep (se 2 (by rfl) ⟨990177, by rfl⟩ : syracuseStep 2640473 = 1980355) B1980355
theorem B12036701 : Blo 1172403 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B1174123 : Blo 1172403 1174123 := bstep (se 1 (by rfl) ⟨880592, by rfl⟩ : syracuseStep 1174123 = 1761185) B1761185
theorem B1174135 : Blo 1172403 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B1174155 : Blo 1172403 1174155 := bstep (se 1 (by rfl) ⟨880616, by rfl⟩ : syracuseStep 1174155 = 1761233) B1761233
theorem B1174167 : Blo 1172403 1174167 := bstep (se 1 (by rfl) ⟨880625, by rfl⟩ : syracuseStep 1174167 = 1761251) B1761251
theorem B1174187 : Blo 1172403 1174187 := bstep (se 1 (by rfl) ⟨880640, by rfl⟩ : syracuseStep 1174187 = 1761281) B1761281
theorem B2640563 : Blo 1172403 2640563 := bstep (se 1 (by rfl) ⟨1980422, by rfl⟩ : syracuseStep 2640563 = 3960845) B3960845
theorem B1174199 : Blo 1172403 1174199 := bstep (se 1 (by rfl) ⟨880649, by rfl⟩ : syracuseStep 1174199 = 1761299) B1761299
theorem B1174219 : Blo 1172403 1174219 := bstep (se 1 (by rfl) ⟨880664, by rfl⟩ : syracuseStep 1174219 = 1761329) B1761329
theorem B2640599 : Blo 1172403 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B1174231 : Blo 1172403 1174231 := bstep (se 1 (by rfl) ⟨880673, by rfl⟩ : syracuseStep 1174231 = 1761347) B1761347
theorem B1174251 : Blo 1172403 1174251 := bstep (se 1 (by rfl) ⟨880688, by rfl⟩ : syracuseStep 1174251 = 1761377) B1761377
theorem B1174263 : Blo 1172403 1174263 := bstep (se 1 (by rfl) ⟨880697, by rfl⟩ : syracuseStep 1174263 = 1761395) B1761395
theorem B1174283 : Blo 1172403 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B1174295 : Blo 1172403 1174295 := bstep (se 1 (by rfl) ⟨880721, by rfl⟩ : syracuseStep 1174295 = 1761443) B1761443
theorem B1174315 : Blo 1172403 1174315 := bstep (se 1 (by rfl) ⟨880736, by rfl⟩ : syracuseStep 1174315 = 1761473) B1761473
theorem B3959603 : Blo 1172403 3959603 := bstep (se 1 (by rfl) ⟨2969702, by rfl⟩ : syracuseStep 3959603 = 5939405) B5939405
theorem B1174327 : Blo 1172403 1174327 := bstep (se 1 (by rfl) ⟨880745, by rfl⟩ : syracuseStep 1174327 = 1761491) B1761491
theorem B1174347 : Blo 1172403 1174347 := bstep (se 1 (by rfl) ⟨880760, by rfl⟩ : syracuseStep 1174347 = 1761521) B1761521
theorem B1174359 : Blo 1172403 1174359 := bstep (se 1 (by rfl) ⟨880769, by rfl⟩ : syracuseStep 1174359 = 1761539) B1761539
theorem B1174379 : Blo 1172403 1174379 := bstep (se 1 (by rfl) ⟨880784, by rfl⟩ : syracuseStep 1174379 = 1761569) B1761569
theorem B1174391 : Blo 1172403 1174391 := bstep (se 1 (by rfl) ⟨880793, by rfl⟩ : syracuseStep 1174391 = 1761587) B1761587
theorem B7515011 : Blo 1172403 7515011 := bstep (se 1 (by rfl) ⟨5636258, by rfl⟩ : syracuseStep 7515011 = 11272517) B11272517
theorem B2640779 : Blo 1172403 2640779 := bstep (se 1 (by rfl) ⟨1980584, by rfl⟩ : syracuseStep 2640779 = 3961169) B3961169
theorem B2821043 : Blo 1172403 2821043 := bstep (se 1 (by rfl) ⟨2115782, by rfl⟩ : syracuseStep 2821043 = 4231565) B4231565
theorem B2640833 : Blo 1172403 2640833 := bstep (se 2 (by rfl) ⟨990312, by rfl⟩ : syracuseStep 2640833 = 1980625) B1980625
theorem B3959873 : Blo 1172403 3959873 := bstep (se 2 (by rfl) ⟨1484952, by rfl⟩ : syracuseStep 3959873 = 2969905) B2969905
theorem B2641049 : Blo 1172403 2641049 := bstep (se 2 (by rfl) ⟨990393, by rfl⟩ : syracuseStep 2641049 = 1980787) B1980787
theorem B4885697 : Blo 1172403 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B2641139 : Blo 1172403 2641139 := bstep (se 1 (by rfl) ⟨1980854, by rfl⟩ : syracuseStep 2641139 = 3961709) B3961709
theorem B2641175 : Blo 1172403 2641175 := bstep (se 1 (by rfl) ⟨1980881, by rfl⟩ : syracuseStep 2641175 = 3961763) B3961763
theorem B2968883 : Blo 1172403 2968883 := bstep (se 1 (by rfl) ⟨2226662, by rfl⟩ : syracuseStep 2968883 = 4453325) B4453325
theorem B5639489 : Blo 1172403 5639489 := bstep (se 2 (by rfl) ⟨2114808, by rfl⟩ : syracuseStep 5639489 = 4229617) B4229617
theorem B2674073 : Blo 1172403 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B2641355 : Blo 1172403 2641355 := bstep (se 1 (by rfl) ⟨1981016, by rfl⟩ : syracuseStep 2641355 = 3962033) B3962033
theorem B2641409 : Blo 1172403 2641409 := bstep (se 2 (by rfl) ⟨990528, by rfl⟩ : syracuseStep 2641409 = 1981057) B1981057
theorem B2379289 : Blo 1172403 2379289 := bstep (se 2 (by rfl) ⟨892233, by rfl⟩ : syracuseStep 2379289 = 1784467) B1784467
theorem B2674241 : Blo 1172403 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B3960413 : Blo 1172403 3960413 := bstep (se 3 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 3960413 = 1485155) B1485155
theorem B8572517 : Blo 1172403 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B16912003 : Blo 1172403 16912003 := bstep (se 1 (by rfl) ⟨12684002, by rfl⟩ : syracuseStep 16912003 = 25368005) B25368005
theorem B21425795 : Blo 1172403 21425795 := bstep (se 1 (by rfl) ⟨16069346, by rfl⟩ : syracuseStep 21425795 = 32138693) B32138693
theorem B2641625 : Blo 1172403 2641625 := bstep (se 2 (by rfl) ⟨990609, by rfl⟩ : syracuseStep 2641625 = 1981219) B1981219
theorem B2641715 : Blo 1172403 2641715 := bstep (se 1 (by rfl) ⟨1981286, by rfl⟩ : syracuseStep 2641715 = 3962573) B3962573
theorem B2969419 : Blo 1172403 2969419 := bstep (se 1 (by rfl) ⟨2227064, by rfl⟩ : syracuseStep 2969419 = 4454129) B4454129
theorem B2641751 : Blo 1172403 2641751 := bstep (se 1 (by rfl) ⟨1981313, by rfl⟩ : syracuseStep 2641751 = 3962627) B3962627
theorem B4452185 : Blo 1172403 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B10030949 : Blo 1172403 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B2576281 : Blo 1172403 2576281 := bstep (se 2 (by rfl) ⟨966105, by rfl⟩ : syracuseStep 2576281 = 1932211) B1932211
theorem B9531341 : Blo 1172403 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B7614425 : Blo 1172403 7614425 := bstep (se 2 (by rfl) ⟨2855409, by rfl⟩ : syracuseStep 7614425 = 5710819) B5710819
theorem B2969561 : Blo 1172403 2969561 := bstep (se 2 (by rfl) ⟨1113585, by rfl⟩ : syracuseStep 2969561 = 2227171) B2227171
theorem B2641931 : Blo 1172403 2641931 := bstep (se 1 (by rfl) ⟨1981448, by rfl⟩ : syracuseStep 2641931 = 3962897) B3962897
theorem B8908865 : Blo 1172403 8908865 := bstep (se 2 (by rfl) ⟨3340824, by rfl⟩ : syracuseStep 8908865 = 6681649) B6681649
theorem B2641985 : Blo 1172403 2641985 := bstep (se 2 (by rfl) ⟨990744, by rfl⟩ : syracuseStep 2641985 = 1981489) B1981489
theorem B1978519 : Blo 1172403 1978519 := bstep (se 1 (by rfl) ⟨1483889, by rfl⟩ : syracuseStep 1978519 = 2967779) B2967779
theorem B2642201 : Blo 1172403 2642201 := bstep (se 2 (by rfl) ⟨990825, by rfl⟩ : syracuseStep 2642201 = 1981651) B1981651
theorem B21401921 : Blo 1172403 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B5943617 : Blo 1172403 5943617 := bstep (se 2 (by rfl) ⟨2228856, by rfl⟩ : syracuseStep 5943617 = 4457713) B4457713
theorem B9163109 : Blo 1172403 9163109 := bstep (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) B1718083
theorem B2642291 : Blo 1172403 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B1880471 : Blo 1172403 1880471 := bstep (se 1 (by rfl) ⟨1410353, by rfl⟩ : syracuseStep 1880471 = 2820707) B2820707
theorem B2642327 : Blo 1172403 2642327 := bstep (se 1 (by rfl) ⟨1981745, by rfl⟩ : syracuseStep 2642327 = 3963491) B3963491
theorem B10031633 : Blo 1172403 10031633 := bstep (se 2 (by rfl) ⟨3761862, by rfl⟩ : syracuseStep 10031633 = 7523725) B7523725
theorem B3666583 : Blo 1172403 3666583 := bstep (se 1 (by rfl) ⟨2749937, by rfl⟩ : syracuseStep 3666583 = 5499875) B5499875
theorem B3961547 : Blo 1172403 3961547 := bstep (se 1 (by rfl) ⟨2971160, by rfl⟩ : syracuseStep 3961547 = 5942321) B5942321
theorem B14471885 : Blo 1172403 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B1979147 : Blo 1172403 1979147 := bstep (se 1 (by rfl) ⟨1484360, by rfl⟩ : syracuseStep 1979147 = 2968721) B2968721
theorem B2970391 : Blo 1172403 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B3339083 : Blo 1172403 3339083 := bstep (se 1 (by rfl) ⟨2504312, by rfl⟩ : syracuseStep 3339083 = 5008625) B5008625
theorem B5936003 : Blo 1172403 5936003 := bstep (se 1 (by rfl) ⟨4452002, by rfl⟩ : syracuseStep 5936003 = 8904005) B8904005
theorem B1782667 : Blo 1172403 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B1979275 : Blo 1172403 1979275 := bstep (se 1 (by rfl) ⟨1484456, by rfl⟩ : syracuseStep 1979275 = 2968913) B2968913
theorem B5010349 : Blo 1172403 5010349 := bstep (se 3 (by rfl) ⟨939440, by rfl⟩ : syracuseStep 5010349 = 1878881) B1878881
theorem B3961817 : Blo 1172403 3961817 := bstep (se 2 (by rfl) ⟨1485681, by rfl⟩ : syracuseStep 3961817 = 2971363) B2971363
theorem B4232153 : Blo 1172403 4232153 := bstep (se 2 (by rfl) ⟨1587057, by rfl⟩ : syracuseStep 4232153 = 3174115) B3174115
theorem B1979417 : Blo 1172403 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B1979545 : Blo 1172403 1979545 := bstep (se 2 (by rfl) ⟨742329, by rfl⟩ : syracuseStep 1979545 = 1484659) B1484659
theorem B2970827 : Blo 1172403 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B3339481 : Blo 1172403 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B4289885 : Blo 1172403 4289885 := bstep (se 3 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 4289885 = 1608707) B1608707
theorem B1758617 : Blo 1172403 1758617 := bstep (se 2 (by rfl) ⟨659481, by rfl⟩ : syracuseStep 1758617 = 1318963) B1318963
theorem B4453811 : Blo 1172403 4453811 := bstep (se 1 (by rfl) ⟨3340358, by rfl⟩ : syracuseStep 4453811 = 6680717) B6680717
theorem B4453825 : Blo 1172403 4453825 := bstep (se 2 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 4453825 = 3340369) B3340369
theorem B1758731 : Blo 1172403 1758731 := bstep (se 1 (by rfl) ⟨1319048, by rfl⟩ : syracuseStep 1758731 = 2638097) B2638097
theorem B1758743 : Blo 1172403 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B12695075 : Blo 1172403 12695075 := bstep (se 1 (by rfl) ⟨9521306, by rfl⟩ : syracuseStep 12695075 = 19042613) B19042613
theorem B2971201 : Blo 1172403 2971201 := bstep (se 2 (by rfl) ⟨1114200, by rfl⟩ : syracuseStep 2971201 = 2228401) B2228401
theorem B1758809 : Blo 1172403 1758809 := bstep (se 2 (by rfl) ⟨659553, by rfl⟩ : syracuseStep 1758809 = 1319107) B1319107
theorem B3757661 : Blo 1172403 3757661 := bstep (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) B1409123
theorem B3053207 : Blo 1172403 3053207 := bstep (se 1 (by rfl) ⟨2289905, by rfl⟩ : syracuseStep 3053207 = 4579811) B4579811
theorem B3962519 : Blo 1172403 3962519 := bstep (se 1 (by rfl) ⟨2971889, by rfl⟩ : syracuseStep 3962519 = 5943779) B5943779
theorem B1758923 : Blo 1172403 1758923 := bstep (se 1 (by rfl) ⟨1319192, by rfl⟩ : syracuseStep 1758923 = 2638385) B2638385
theorem B1758935 : Blo 1172403 1758935 := bstep (se 1 (by rfl) ⟨1319201, by rfl⟩ : syracuseStep 1758935 = 2638403) B2638403
theorem B1980119 : Blo 1172403 1980119 := bstep (se 1 (by rfl) ⟨1485089, by rfl⟩ : syracuseStep 1980119 = 2970179) B2970179
theorem B2504449 : Blo 1172403 2504449 := bstep (se 2 (by rfl) ⟨939168, by rfl⟩ : syracuseStep 2504449 = 1878337) B1878337
theorem B1759001 : Blo 1172403 1759001 := bstep (se 2 (by rfl) ⟨659625, by rfl⟩ : syracuseStep 1759001 = 1319251) B1319251
theorem B2225971 : Blo 1172403 2225971 := bstep (se 1 (by rfl) ⟨1669478, by rfl⟩ : syracuseStep 2225971 = 3338957) B3338957
theorem B1980247 : Blo 1172403 1980247 := bstep (se 1 (by rfl) ⟨1485185, by rfl⟩ : syracuseStep 1980247 = 2970371) B2970371
theorem B10696549 : Blo 1172403 10696549 := bstep (se 4 (by rfl) ⟨1002801, by rfl⟩ : syracuseStep 10696549 = 2005603) B2005603
theorem B1759115 : Blo 1172403 1759115 := bstep (se 1 (by rfl) ⟨1319336, by rfl⟩ : syracuseStep 1759115 = 2638673) B2638673
theorem B1759127 : Blo 1172403 1759127 := bstep (se 1 (by rfl) ⟨1319345, by rfl⟩ : syracuseStep 1759127 = 2638691) B2638691
theorem B4757399 : Blo 1172403 4757399 := bstep (se 1 (by rfl) ⟨3568049, by rfl⟩ : syracuseStep 4757399 = 7136099) B7136099
theorem B1759193 : Blo 1172403 1759193 := bstep (se 2 (by rfl) ⟨659697, by rfl⟩ : syracuseStep 1759193 = 1319395) B1319395
theorem B8910809 : Blo 1172403 8910809 := bstep (se 2 (by rfl) ⟨3341553, by rfl⟩ : syracuseStep 8910809 = 6683107) B6683107
theorem B2226199 : Blo 1172403 2226199 := bstep (se 1 (by rfl) ⟨1669649, by rfl⟩ : syracuseStep 2226199 = 3339299) B3339299
theorem B1759307 : Blo 1172403 1759307 := bstep (se 1 (by rfl) ⟨1319480, by rfl⟩ : syracuseStep 1759307 = 2638961) B2638961
theorem B1783883 : Blo 1172403 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B1759319 : Blo 1172403 1759319 := bstep (se 1 (by rfl) ⟨1319489, by rfl⟩ : syracuseStep 1759319 = 2638979) B2638979
theorem B2226305 : Blo 1172403 2226305 := bstep (se 2 (by rfl) ⟨834864, by rfl⟩ : syracuseStep 2226305 = 1669729) B1669729
theorem B2971799 : Blo 1172403 2971799 := bstep (se 1 (by rfl) ⟨2228849, by rfl⟩ : syracuseStep 2971799 = 4457699) B4457699
theorem B1759385 : Blo 1172403 1759385 := bstep (se 2 (by rfl) ⟨659769, by rfl⟩ : syracuseStep 1759385 = 1319539) B1319539
theorem B3963059 : Blo 1172403 3963059 := bstep (se 1 (by rfl) ⟨2972294, by rfl⟩ : syracuseStep 3963059 = 5944589) B5944589
theorem B1759499 : Blo 1172403 1759499 := bstep (se 1 (by rfl) ⟨1319624, by rfl⟩ : syracuseStep 1759499 = 2639249) B2639249
theorem B1759511 : Blo 1172403 1759511 := bstep (se 1 (by rfl) ⟨1319633, by rfl⟩ : syracuseStep 1759511 = 2639267) B2639267
theorem B2226457 : Blo 1172403 2226457 := bstep (se 2 (by rfl) ⟨834921, by rfl⟩ : syracuseStep 2226457 = 1669843) B1669843
theorem B6682925 : Blo 1172403 6682925 := bstep (se 3 (by rfl) ⟨1253048, by rfl⟩ : syracuseStep 6682925 = 2506097) B2506097
theorem B1759577 : Blo 1172403 1759577 := bstep (se 2 (by rfl) ⟨659841, by rfl⟩ : syracuseStep 1759577 = 1319683) B1319683
theorem B3340723 : Blo 1172403 3340723 := bstep (se 1 (by rfl) ⟨2505542, by rfl⟩ : syracuseStep 3340723 = 5011085) B5011085
theorem B3963329 : Blo 1172403 3963329 := bstep (se 2 (by rfl) ⟨1486248, by rfl⟩ : syracuseStep 3963329 = 2972497) B2972497
theorem B1759691 : Blo 1172403 1759691 := bstep (se 1 (by rfl) ⟨1319768, by rfl⟩ : syracuseStep 1759691 = 2639537) B2639537
theorem B1980875 : Blo 1172403 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B1759703 : Blo 1172403 1759703 := bstep (se 1 (by rfl) ⟨1319777, by rfl⟩ : syracuseStep 1759703 = 2639555) B2639555
theorem B3758557 : Blo 1172403 3758557 := bstep (se 3 (by rfl) ⟨704729, by rfl⟩ : syracuseStep 3758557 = 1409459) B1409459
theorem B1759769 : Blo 1172403 1759769 := bstep (se 2 (by rfl) ⟨659913, by rfl⟩ : syracuseStep 1759769 = 1319827) B1319827
theorem B1981003 : Blo 1172403 1981003 := bstep (se 1 (by rfl) ⟨1485752, by rfl⟩ : syracuseStep 1981003 = 2971505) B2971505
theorem B5012057 : Blo 1172403 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B1759883 : Blo 1172403 1759883 := bstep (se 1 (by rfl) ⟨1319912, by rfl⟩ : syracuseStep 1759883 = 2639825) B2639825
theorem B1759895 : Blo 1172403 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B5716631 : Blo 1172403 5716631 := bstep (se 1 (by rfl) ⟨4287473, by rfl⟩ : syracuseStep 5716631 = 8574947) B8574947
theorem B4127383 : Blo 1172403 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B5356211 : Blo 1172403 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B2505431 : Blo 1172403 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B1759961 : Blo 1172403 1759961 := bstep (se 2 (by rfl) ⟨659985, by rfl⟩ : syracuseStep 1759961 = 1319971) B1319971
theorem B1981145 : Blo 1172403 1981145 := bstep (se 2 (by rfl) ⟨742929, by rfl⟩ : syracuseStep 1981145 = 1485859) B1485859
theorem B10017553 : Blo 1172403 10017553 := bstep (se 2 (by rfl) ⟨3756582, by rfl⟩ : syracuseStep 10017553 = 7513165) B7513165
theorem B1760075 : Blo 1172403 1760075 := bstep (se 1 (by rfl) ⟨1320056, by rfl⟩ : syracuseStep 1760075 = 2640113) B2640113
theorem B1760087 : Blo 1172403 1760087 := bstep (se 1 (by rfl) ⟨1320065, by rfl⟩ : syracuseStep 1760087 = 2640131) B2640131
theorem B1981273 : Blo 1172403 1981273 := bstep (se 2 (by rfl) ⟨742977, by rfl⟩ : syracuseStep 1981273 = 1485955) B1485955
theorem B1760153 : Blo 1172403 1760153 := bstep (se 2 (by rfl) ⟨660057, by rfl⟩ : syracuseStep 1760153 = 1320115) B1320115
theorem B2972609 : Blo 1172403 2972609 := bstep (se 2 (by rfl) ⟨1114728, by rfl⟩ : syracuseStep 2972609 = 2229457) B2229457
theorem B104225753 : Blo 1172403 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B1670105 : Blo 1172403 1670105 := bstep (se 2 (by rfl) ⟨626289, by rfl⟩ : syracuseStep 1670105 = 1252579) B1252579
theorem B1760267 : Blo 1172403 1760267 := bstep (se 1 (by rfl) ⟨1320200, by rfl⟩ : syracuseStep 1760267 = 2640401) B2640401
theorem B1760279 : Blo 1172403 1760279 := bstep (se 1 (by rfl) ⟨1320209, by rfl⟩ : syracuseStep 1760279 = 2640419) B2640419
theorem B10017827 : Blo 1172403 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B1760345 : Blo 1172403 1760345 := bstep (se 2 (by rfl) ⟨660129, by rfl⟩ : syracuseStep 1760345 = 1320259) B1320259
theorem B4758707 : Blo 1172403 4758707 := bstep (se 1 (by rfl) ⟨3569030, by rfl⟩ : syracuseStep 4758707 = 7138061) B7138061
theorem B1760459 : Blo 1172403 1760459 := bstep (se 1 (by rfl) ⟨1320344, by rfl⟩ : syracuseStep 1760459 = 2640689) B2640689
theorem B1760471 : Blo 1172403 1760471 := bstep (se 1 (by rfl) ⟨1320353, by rfl⟩ : syracuseStep 1760471 = 2640707) B2640707
theorem B2505995 : Blo 1172403 2505995 := bstep (se 1 (by rfl) ⟨1879496, by rfl⟩ : syracuseStep 2505995 = 3758993) B3758993
theorem B1760537 : Blo 1172403 1760537 := bstep (se 2 (by rfl) ⟨660201, by rfl⟩ : syracuseStep 1760537 = 1320403) B1320403
theorem B4455755 : Blo 1172403 4455755 := bstep (se 1 (by rfl) ⟨3341816, by rfl⟩ : syracuseStep 4455755 = 6683633) B6683633
theorem B4455769 : Blo 1172403 4455769 := bstep (se 2 (by rfl) ⟨1670913, by rfl⟩ : syracuseStep 4455769 = 3341827) B3341827
theorem B1760651 : Blo 1172403 1760651 := bstep (se 1 (by rfl) ⟨1320488, by rfl⟩ : syracuseStep 1760651 = 2640977) B2640977
theorem B1760663 : Blo 1172403 1760663 := bstep (se 1 (by rfl) ⟨1320497, by rfl⟩ : syracuseStep 1760663 = 2640995) B2640995
theorem B8461745 : Blo 1172403 8461745 := bstep (se 2 (by rfl) ⟨3173154, by rfl⟩ : syracuseStep 8461745 = 6346309) B6346309
theorem B1269175 : Blo 1172403 1269175 := bstep (se 1 (by rfl) ⟨951881, by rfl⟩ : syracuseStep 1269175 = 1903763) B1903763
theorem B1760729 : Blo 1172403 1760729 := bstep (se 2 (by rfl) ⟨660273, by rfl⟩ : syracuseStep 1760729 = 1320547) B1320547
theorem B2227763 : Blo 1172403 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B1760843 : Blo 1172403 1760843 := bstep (se 1 (by rfl) ⟨1320632, by rfl⟩ : syracuseStep 1760843 = 2641265) B2641265
theorem B1670743 : Blo 1172403 1670743 := bstep (se 1 (by rfl) ⟨1253057, by rfl⟩ : syracuseStep 1670743 = 2506115) B2506115
theorem B1760855 : Blo 1172403 1760855 := bstep (se 1 (by rfl) ⟨1320641, by rfl⟩ : syracuseStep 1760855 = 2641283) B2641283
theorem B1760921 : Blo 1172403 1760921 := bstep (se 2 (by rfl) ⟨660345, by rfl⟩ : syracuseStep 1760921 = 1320691) B1320691
theorem B2227915 : Blo 1172403 2227915 := bstep (se 1 (by rfl) ⟨1670936, by rfl⟩ : syracuseStep 2227915 = 3341873) B3341873
theorem B2506457 : Blo 1172403 2506457 := bstep (se 2 (by rfl) ⟨939921, by rfl⟩ : syracuseStep 2506457 = 1879843) B1879843
theorem B1761035 : Blo 1172403 1761035 := bstep (se 1 (by rfl) ⟨1320776, by rfl⟩ : syracuseStep 1761035 = 2641553) B2641553
theorem B2113303 : Blo 1172403 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B1761047 : Blo 1172403 1761047 := bstep (se 1 (by rfl) ⟨1320785, by rfl⟩ : syracuseStep 1761047 = 2641571) B2641571
theorem B5013323 : Blo 1172403 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B3170137 : Blo 1172403 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B1761113 : Blo 1172403 1761113 := bstep (se 2 (by rfl) ⟨660417, by rfl⟩ : syracuseStep 1761113 = 1320835) B1320835
theorem B9035651 : Blo 1172403 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B10166147 : Blo 1172403 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B2817995 : Blo 1172403 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B5078987 : Blo 1172403 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B1761227 : Blo 1172403 1761227 := bstep (se 1 (by rfl) ⟨1320920, by rfl⟩ : syracuseStep 1761227 = 2641841) B2641841
theorem B1761239 : Blo 1172403 1761239 := bstep (se 1 (by rfl) ⟨1320929, by rfl⟩ : syracuseStep 1761239 = 2641859) B2641859
theorem B12689369 : Blo 1172403 12689369 := bstep (se 2 (by rfl) ⟨4758513, by rfl⟩ : syracuseStep 12689369 = 9517027) B9517027
theorem B1761287 : Blo 1172403 1761287 := bstep (se 1 (by rfl) ⟨1320965, by rfl⟩ : syracuseStep 1761287 = 2641931) B2641931
theorem B6340619 : Blo 1172403 6340619 := bstep (se 1 (by rfl) ⟨4755464, by rfl⟩ : syracuseStep 6340619 = 9510929) B9510929
theorem B5939243 : Blo 1172403 5939243 := bstep (se 1 (by rfl) ⟨4454432, by rfl⟩ : syracuseStep 5939243 = 8908865) B8908865
theorem B1761323 : Blo 1172403 1761323 := bstep (se 1 (by rfl) ⟨1320992, by rfl⟩ : syracuseStep 1761323 = 2641985) B2641985
theorem B3342397 : Blo 1172403 3342397 := bstep (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) B1253399
theorem B1761353 : Blo 1172403 1761353 := bstep (se 2 (by rfl) ⟨660507, by rfl⟩ : syracuseStep 1761353 = 1321015) B1321015
theorem B3342455 : Blo 1172403 3342455 := bstep (se 1 (by rfl) ⟨2506841, by rfl⟩ : syracuseStep 3342455 = 5013683) B5013683
theorem B2637971 : Blo 1172403 2637971 := bstep (se 1 (by rfl) ⟨1978478, by rfl⟩ : syracuseStep 2637971 = 3956957) B3956957
theorem B1761467 : Blo 1172403 1761467 := bstep (se 1 (by rfl) ⟨1321100, by rfl⟩ : syracuseStep 1761467 = 2642201) B2642201
theorem B2638025 : Blo 1172403 2638025 := bstep (se 2 (by rfl) ⟨989259, by rfl⟩ : syracuseStep 2638025 = 1978519) B1978519
theorem B1761527 : Blo 1172403 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B1253647 : Blo 1172403 1253647 := bstep (se 1 (by rfl) ⟨940235, by rfl⟩ : syracuseStep 1253647 = 1880471) B1880471
theorem B1761551 : Blo 1172403 1761551 := bstep (se 1 (by rfl) ⟨1321163, by rfl⟩ : syracuseStep 1761551 = 2642327) B2642327
theorem B1761593 : Blo 1172403 1761593 := bstep (se 2 (by rfl) ⟨660597, by rfl⟩ : syracuseStep 1761593 = 1321195) B1321195
theorem B12689885 : Blo 1172403 12689885 := bstep (se 3 (by rfl) ⟨2379353, by rfl⟩ : syracuseStep 12689885 = 4758707) B4758707
theorem B13369859 : Blo 1172403 13369859 := bstep (se 1 (by rfl) ⟨10027394, by rfl⟩ : syracuseStep 13369859 = 20054789) B20054789
theorem B1319431 : Blo 1172403 1319431 := bstep (se 1 (by rfl) ⟨989573, by rfl⟩ : syracuseStep 1319431 = 1979147) B1979147
theorem B3957335 : Blo 1172403 3957335 := bstep (se 1 (by rfl) ⟨2968001, by rfl⟩ : syracuseStep 3957335 = 5936003) B5936003
theorem B1319611 : Blo 1172403 1319611 := bstep (se 1 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 1319611 = 1979417) B1979417
theorem B2114363 : Blo 1172403 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B2638727 : Blo 1172403 2638727 := bstep (se 1 (by rfl) ⟨1979045, by rfl⟩ : syracuseStep 2638727 = 3958091) B3958091
theorem B2859923 : Blo 1172403 2859923 := bstep (se 1 (by rfl) ⟨2144942, by rfl⟩ : syracuseStep 2859923 = 4289885) B4289885
theorem B1672121 : Blo 1172403 1672121 := bstep (se 2 (by rfl) ⟨627045, by rfl⟩ : syracuseStep 1672121 = 1254091) B1254091
theorem B1172411 : Blo 1172403 1172411 := bstep (se 1 (by rfl) ⟨879308, by rfl⟩ : syracuseStep 1172411 = 1758617) B1758617
theorem B1172487 : Blo 1172403 1172487 := bstep (se 1 (by rfl) ⟨879365, by rfl⟩ : syracuseStep 1172487 = 1758731) B1758731
theorem B1172495 : Blo 1172403 1172495 := bstep (se 1 (by rfl) ⟨879371, by rfl⟩ : syracuseStep 1172495 = 1758743) B1758743
theorem B8463383 : Blo 1172403 8463383 := bstep (se 1 (by rfl) ⟨6347537, by rfl⟩ : syracuseStep 8463383 = 12695075) B12695075
theorem B4457501 : Blo 1172403 4457501 := bstep (se 3 (by rfl) ⟨835781, by rfl⟩ : syracuseStep 4457501 = 1671563) B1671563
theorem B1172539 : Blo 1172403 1172539 := bstep (se 1 (by rfl) ⟨879404, by rfl⟩ : syracuseStep 1172539 = 1758809) B1758809
theorem B2638907 : Blo 1172403 2638907 := bstep (se 1 (by rfl) ⟨1979180, by rfl⟩ : syracuseStep 2638907 = 3958361) B3958361
theorem B3957821 : Blo 1172403 3957821 := bstep (se 3 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 3957821 = 1484183) B1484183
theorem B1172615 : Blo 1172403 1172615 := bstep (se 1 (by rfl) ⟨879461, by rfl⟩ : syracuseStep 1172615 = 1758923) B1758923
theorem B1172623 : Blo 1172403 1172623 := bstep (se 1 (by rfl) ⟨879467, by rfl⟩ : syracuseStep 1172623 = 1758935) B1758935
theorem B1320079 : Blo 1172403 1320079 := bstep (se 1 (by rfl) ⟨990059, by rfl⟩ : syracuseStep 1320079 = 1980119) B1980119
theorem B3343513 : Blo 1172403 3343513 := bstep (se 2 (by rfl) ⟨1253817, by rfl⟩ : syracuseStep 3343513 = 2507635) B2507635
theorem B12870829 : Blo 1172403 12870829 := bstep (se 3 (by rfl) ⟨2413280, by rfl⟩ : syracuseStep 12870829 = 4826561) B4826561
theorem B2639033 : Blo 1172403 2639033 := bstep (se 2 (by rfl) ⟨989637, by rfl⟩ : syracuseStep 2639033 = 1979275) B1979275
theorem B1172667 : Blo 1172403 1172667 := bstep (se 1 (by rfl) ⟨879500, by rfl⟩ : syracuseStep 1172667 = 1759001) B1759001
theorem B1410295 : Blo 1172403 1410295 := bstep (se 1 (by rfl) ⟨1057721, by rfl⟩ : syracuseStep 1410295 = 2115443) B2115443
theorem B1172743 : Blo 1172403 1172743 := bstep (se 1 (by rfl) ⟨879557, by rfl⟩ : syracuseStep 1172743 = 1759115) B1759115
theorem B1172751 : Blo 1172403 1172751 := bstep (se 1 (by rfl) ⟨879563, by rfl⟩ : syracuseStep 1172751 = 1759127) B1759127
theorem B3171599 : Blo 1172403 3171599 := bstep (se 1 (by rfl) ⟨2378699, by rfl⟩ : syracuseStep 3171599 = 4757399) B4757399
theorem B1172795 : Blo 1172403 1172795 := bstep (se 1 (by rfl) ⟨879596, by rfl⟩ : syracuseStep 1172795 = 1759193) B1759193
theorem B5940539 : Blo 1172403 5940539 := bstep (se 1 (by rfl) ⟨4455404, by rfl⟩ : syracuseStep 5940539 = 8910809) B8910809
theorem B1172871 : Blo 1172403 1172871 := bstep (se 1 (by rfl) ⟨879653, by rfl⟩ : syracuseStep 1172871 = 1759307) B1759307
theorem B1172879 : Blo 1172403 1172879 := bstep (se 1 (by rfl) ⟨879659, by rfl⟩ : syracuseStep 1172879 = 1759319) B1759319
theorem B1172923 : Blo 1172403 1172923 := bstep (se 1 (by rfl) ⟨879692, by rfl⟩ : syracuseStep 1172923 = 1759385) B1759385
theorem B5940701 : Blo 1172403 5940701 := bstep (se 3 (by rfl) ⟨1113881, by rfl⟩ : syracuseStep 5940701 = 2227763) B2227763
theorem B1172999 : Blo 1172403 1172999 := bstep (se 1 (by rfl) ⟨879749, by rfl⟩ : syracuseStep 1172999 = 1759499) B1759499
theorem B1173007 : Blo 1172403 1173007 := bstep (se 1 (by rfl) ⟨879755, by rfl⟩ : syracuseStep 1173007 = 1759511) B1759511
theorem B2639375 : Blo 1172403 2639375 := bstep (se 1 (by rfl) ⟨1979531, by rfl⟩ : syracuseStep 2639375 = 3959063) B3959063
theorem B2639393 : Blo 1172403 2639393 := bstep (se 2 (by rfl) ⟨989772, by rfl⟩ : syracuseStep 2639393 = 1979545) B1979545
theorem B1173051 : Blo 1172403 1173051 := bstep (se 1 (by rfl) ⟨879788, by rfl⟩ : syracuseStep 1173051 = 1759577) B1759577
theorem B32097869 : Blo 1172403 32097869 := bstep (se 3 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 32097869 = 12036701) B12036701
theorem B1173127 : Blo 1172403 1173127 := bstep (se 1 (by rfl) ⟨879845, by rfl⟩ : syracuseStep 1173127 = 1759691) B1759691
theorem B1320583 : Blo 1172403 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B1173135 : Blo 1172403 1173135 := bstep (se 1 (by rfl) ⟨879851, by rfl⟩ : syracuseStep 1173135 = 1759703) B1759703
theorem B1173179 : Blo 1172403 1173179 := bstep (se 1 (by rfl) ⟨879884, by rfl⟩ : syracuseStep 1173179 = 1759769) B1759769
theorem B4458185 : Blo 1172403 4458185 := bstep (se 2 (by rfl) ⟨1671819, by rfl⟩ : syracuseStep 4458185 = 3343639) B3343639
theorem B3344129 : Blo 1172403 3344129 := bstep (se 2 (by rfl) ⟨1254048, by rfl⟩ : syracuseStep 3344129 = 2508097) B2508097
theorem B1173255 : Blo 1172403 1173255 := bstep (se 1 (by rfl) ⟨879941, by rfl⟩ : syracuseStep 1173255 = 1759883) B1759883
theorem B1173263 : Blo 1172403 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B3811087 : Blo 1172403 3811087 := bstep (se 1 (by rfl) ⟨2858315, by rfl⟩ : syracuseStep 3811087 = 5716631) B5716631
theorem B5941025 : Blo 1172403 5941025 := bstep (se 2 (by rfl) ⟨2227884, by rfl⟩ : syracuseStep 5941025 = 4455769) B4455769
theorem B6342437 : Blo 1172403 6342437 := bstep (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) B1189207
theorem B7522085 : Blo 1172403 7522085 := bstep (se 4 (by rfl) ⟨705195, by rfl⟩ : syracuseStep 7522085 = 1410391) B1410391
theorem B1173307 : Blo 1172403 1173307 := bstep (se 1 (by rfl) ⟨879980, by rfl⟩ : syracuseStep 1173307 = 1759961) B1759961
theorem B1320763 : Blo 1172403 1320763 := bstep (se 1 (by rfl) ⟨990572, by rfl⟩ : syracuseStep 1320763 = 1981145) B1981145
theorem B2639735 : Blo 1172403 2639735 := bstep (se 1 (by rfl) ⟨1979801, by rfl⟩ : syracuseStep 2639735 = 3959603) B3959603
theorem B1173383 : Blo 1172403 1173383 := bstep (se 1 (by rfl) ⟨880037, by rfl⟩ : syracuseStep 1173383 = 1760075) B1760075
theorem B1173391 : Blo 1172403 1173391 := bstep (se 1 (by rfl) ⟨880043, by rfl⟩ : syracuseStep 1173391 = 1760087) B1760087
theorem B1173435 : Blo 1172403 1173435 := bstep (se 1 (by rfl) ⟨880076, by rfl⟩ : syracuseStep 1173435 = 1760153) B1760153
theorem B1173511 : Blo 1172403 1173511 := bstep (se 1 (by rfl) ⟨880133, by rfl⟩ : syracuseStep 1173511 = 1760267) B1760267
theorem B1173519 : Blo 1172403 1173519 := bstep (se 1 (by rfl) ⟨880139, by rfl⟩ : syracuseStep 1173519 = 1760279) B1760279
theorem B6678551 : Blo 1172403 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B3172385 : Blo 1172403 3172385 := bstep (se 2 (by rfl) ⟨1189644, by rfl⟩ : syracuseStep 3172385 = 2379289) B2379289
theorem B2639915 : Blo 1172403 2639915 := bstep (se 1 (by rfl) ⟨1979936, by rfl⟩ : syracuseStep 2639915 = 3959873) B3959873
theorem B1173563 : Blo 1172403 1173563 := bstep (se 1 (by rfl) ⟨880172, by rfl⟩ : syracuseStep 1173563 = 1760345) B1760345
theorem B1173639 : Blo 1172403 1173639 := bstep (se 1 (by rfl) ⟨880229, by rfl⟩ : syracuseStep 1173639 = 1760459) B1760459
theorem B1173647 : Blo 1172403 1173647 := bstep (se 1 (by rfl) ⟨880235, by rfl⟩ : syracuseStep 1173647 = 1760471) B1760471
theorem B1173691 : Blo 1172403 1173691 := bstep (se 1 (by rfl) ⟨880268, by rfl⟩ : syracuseStep 1173691 = 1760537) B1760537
theorem B1173767 : Blo 1172403 1173767 := bstep (se 1 (by rfl) ⟨880325, by rfl⟩ : syracuseStep 1173767 = 1760651) B1760651
theorem B1173775 : Blo 1172403 1173775 := bstep (se 1 (by rfl) ⟨880331, by rfl⟩ : syracuseStep 1173775 = 1760663) B1760663
theorem B1173819 : Blo 1172403 1173819 := bstep (se 1 (by rfl) ⟨880364, by rfl⟩ : syracuseStep 1173819 = 1760729) B1760729
theorem B24095069 : Blo 1172403 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B1173895 : Blo 1172403 1173895 := bstep (se 1 (by rfl) ⟨880421, by rfl⟩ : syracuseStep 1173895 = 1760843) B1760843
theorem B1173903 : Blo 1172403 1173903 := bstep (se 1 (by rfl) ⟨880427, by rfl⟩ : syracuseStep 1173903 = 1760855) B1760855
theorem B2640275 : Blo 1172403 2640275 := bstep (se 1 (by rfl) ⟨1980206, by rfl⟩ : syracuseStep 2640275 = 3960413) B3960413
theorem B2967961 : Blo 1172403 2967961 := bstep (se 2 (by rfl) ⟨1112985, by rfl⟩ : syracuseStep 2967961 = 2225971) B2225971
theorem B3959225 : Blo 1172403 3959225 := bstep (se 2 (by rfl) ⟨1484709, by rfl⟩ : syracuseStep 3959225 = 2969419) B2969419
theorem B1173947 : Blo 1172403 1173947 := bstep (se 1 (by rfl) ⟨880460, by rfl⟩ : syracuseStep 1173947 = 1760921) B1760921
theorem B2640329 : Blo 1172403 2640329 := bstep (se 2 (by rfl) ⟨990123, by rfl⟩ : syracuseStep 2640329 = 1980247) B1980247
theorem B1174023 : Blo 1172403 1174023 := bstep (se 1 (by rfl) ⟨880517, by rfl⟩ : syracuseStep 1174023 = 1761035) B1761035
theorem B1174031 : Blo 1172403 1174031 := bstep (se 1 (by rfl) ⟨880523, by rfl⟩ : syracuseStep 1174031 = 1761047) B1761047
theorem B7514653 : Blo 1172403 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B3435041 : Blo 1172403 3435041 := bstep (se 2 (by rfl) ⟨1288140, by rfl⟩ : syracuseStep 3435041 = 2576281) B2576281
theorem B2968123 : Blo 1172403 2968123 := bstep (se 1 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 2968123 = 4452185) B4452185
theorem B1174075 : Blo 1172403 1174075 := bstep (se 1 (by rfl) ⟨880556, by rfl⟩ : syracuseStep 1174075 = 1761113) B1761113
theorem B6687299 : Blo 1172403 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B6777431 : Blo 1172403 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B3385991 : Blo 1172403 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B1174151 : Blo 1172403 1174151 := bstep (se 1 (by rfl) ⟨880613, by rfl⟩ : syracuseStep 1174151 = 1761227) B1761227
theorem B1174159 : Blo 1172403 1174159 := bstep (se 1 (by rfl) ⟨880619, by rfl⟩ : syracuseStep 1174159 = 1761239) B1761239
theorem B1174203 : Blo 1172403 1174203 := bstep (se 1 (by rfl) ⟨880652, by rfl⟩ : syracuseStep 1174203 = 1761305) B1761305
theorem B2968265 : Blo 1172403 2968265 := bstep (se 2 (by rfl) ⟨1113099, by rfl⟩ : syracuseStep 2968265 = 2226199) B2226199
theorem B5941997 : Blo 1172403 5941997 := bstep (se 3 (by rfl) ⟨1114124, by rfl⟩ : syracuseStep 5941997 = 2228249) B2228249
theorem B1174279 : Blo 1172403 1174279 := bstep (se 1 (by rfl) ⟨880709, by rfl⟩ : syracuseStep 1174279 = 1761419) B1761419
theorem B1174287 : Blo 1172403 1174287 := bstep (se 1 (by rfl) ⟨880715, by rfl⟩ : syracuseStep 1174287 = 1761431) B1761431
theorem B1174331 : Blo 1172403 1174331 := bstep (se 1 (by rfl) ⟨880748, by rfl⟩ : syracuseStep 1174331 = 1761497) B1761497
theorem B3959819 : Blo 1172403 3959819 := bstep (se 1 (by rfl) ⟨2969864, by rfl⟩ : syracuseStep 3959819 = 5939729) B5939729
theorem B6687755 : Blo 1172403 6687755 := bstep (se 1 (by rfl) ⟨5015816, by rfl⟩ : syracuseStep 6687755 = 10031633) B10031633
theorem B1879055 : Blo 1172403 1879055 := bstep (se 1 (by rfl) ⟨1409291, by rfl⟩ : syracuseStep 1879055 = 2818583) B2818583
theorem B2968609 : Blo 1172403 2968609 := bstep (se 2 (by rfl) ⟨1113228, by rfl⟩ : syracuseStep 2968609 = 2226457) B2226457
theorem B3959927 : Blo 1172403 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B2641031 : Blo 1172403 2641031 := bstep (se 1 (by rfl) ⟨1980773, by rfl⟩ : syracuseStep 2641031 = 3961547) B3961547
theorem B13028525 : Blo 1172403 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B2821321 : Blo 1172403 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B3566891 : Blo 1172403 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B2641211 : Blo 1172403 2641211 := bstep (se 1 (by rfl) ⟨1980908, by rfl⟩ : syracuseStep 2641211 = 3961817) B3961817
theorem B2821435 : Blo 1172403 2821435 := bstep (se 1 (by rfl) ⟨2116076, by rfl⟩ : syracuseStep 2821435 = 4232153) B4232153
theorem B4451699 : Blo 1172403 4451699 := bstep (se 1 (by rfl) ⟨3338774, by rfl⟩ : syracuseStep 4451699 = 6677549) B6677549
theorem B2641337 : Blo 1172403 2641337 := bstep (se 2 (by rfl) ⟨990501, by rfl⟩ : syracuseStep 2641337 = 1981003) B1981003
theorem B5942807 : Blo 1172403 5942807 := bstep (se 1 (by rfl) ⟨4457105, by rfl⟩ : syracuseStep 5942807 = 8914211) B8914211
theorem B2969207 : Blo 1172403 2969207 := bstep (se 1 (by rfl) ⟨2226905, by rfl⟩ : syracuseStep 2969207 = 4453811) B4453811
theorem B13356737 : Blo 1172403 13356737 := bstep (se 2 (by rfl) ⟨5008776, by rfl⟩ : syracuseStep 13356737 = 10017553) B10017553
theorem B3960521 : Blo 1172403 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B7130861 : Blo 1172403 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B7139087 : Blo 1172403 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B2035471 : Blo 1172403 2035471 := bstep (se 1 (by rfl) ⟨1526603, by rfl⟩ : syracuseStep 2035471 = 3053207) B3053207
theorem B2641679 : Blo 1172403 2641679 := bstep (se 1 (by rfl) ⟨1981259, by rfl⟩ : syracuseStep 2641679 = 3962519) B3962519
theorem B2641697 : Blo 1172403 2641697 := bstep (se 2 (by rfl) ⟨990636, by rfl⟩ : syracuseStep 2641697 = 1981273) B1981273
theorem B13545253 : Blo 1172403 13545253 := bstep (se 4 (by rfl) ⟨1269867, by rfl⟩ : syracuseStep 13545253 = 2539735) B2539735
theorem B4452155 : Blo 1172403 4452155 := bstep (se 1 (by rfl) ⟨3339116, by rfl⟩ : syracuseStep 4452155 = 6678233) B6678233
theorem B3174203 : Blo 1172403 3174203 := bstep (se 1 (by rfl) ⟨2380652, by rfl⟩ : syracuseStep 3174203 = 4761305) B4761305
theorem B6680465 : Blo 1172403 6680465 := bstep (se 2 (by rfl) ⟨2505174, by rfl⟩ : syracuseStep 6680465 = 5010349) B5010349
theorem B3010571 : Blo 1172403 3010571 := bstep (se 1 (by rfl) ⟨2257928, by rfl⟩ : syracuseStep 3010571 = 4515857) B4515857
theorem B2642039 : Blo 1172403 2642039 := bstep (se 1 (by rfl) ⟨1981529, by rfl⟩ : syracuseStep 2642039 = 3963059) B3963059
theorem B1978553 : Blo 1172403 1978553 := bstep (se 2 (by rfl) ⟨741957, by rfl⟩ : syracuseStep 1978553 = 1483915) B1483915
theorem B13365485 : Blo 1172403 13365485 := bstep (se 3 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 13365485 = 5012057) B5012057
theorem B4452641 : Blo 1172403 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B2642219 : Blo 1172403 2642219 := bstep (se 1 (by rfl) ⟨1981664, by rfl⟩ : syracuseStep 2642219 = 3963329) B3963329
theorem B3961223 : Blo 1172403 3961223 := bstep (se 1 (by rfl) ⟨2970917, by rfl⟩ : syracuseStep 3961223 = 5941835) B5941835
theorem B14283229 : Blo 1172403 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B6681149 : Blo 1172403 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B1692233 : Blo 1172403 1692233 := bstep (se 2 (by rfl) ⟨634587, by rfl⟩ : syracuseStep 1692233 = 1269175) B1269175
theorem B5010007 : Blo 1172403 5010007 := bstep (se 1 (by rfl) ⟨3757505, by rfl⟩ : syracuseStep 5010007 = 7515011) B7515011
theorem B1880695 : Blo 1172403 1880695 := bstep (se 1 (by rfl) ⟨1410521, by rfl⟩ : syracuseStep 1880695 = 2821043) B2821043
theorem B9507557 : Blo 1172403 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B3961601 : Blo 1172403 3961601 := bstep (se 2 (by rfl) ⟨1485600, by rfl⟩ : syracuseStep 3961601 = 2971201) B2971201
theorem B22549337 : Blo 1172403 22549337 := bstep (se 2 (by rfl) ⟨8456001, by rfl⟩ : syracuseStep 22549337 = 16912003) B16912003
theorem B1979255 : Blo 1172403 1979255 := bstep (se 1 (by rfl) ⟨1484441, by rfl⟩ : syracuseStep 1979255 = 2968883) B2968883
theorem B2970503 : Blo 1172403 2970503 := bstep (se 1 (by rfl) ⟨2227877, by rfl⟩ : syracuseStep 2970503 = 4455755) B4455755
theorem B2970553 : Blo 1172403 2970553 := bstep (se 2 (by rfl) ⟨1113957, by rfl⟩ : syracuseStep 2970553 = 2227915) B2227915
theorem B5641163 : Blo 1172403 5641163 := bstep (se 1 (by rfl) ⟨4230872, by rfl⟩ : syracuseStep 5641163 = 8461745) B8461745
theorem B3339265 : Blo 1172403 3339265 := bstep (se 2 (by rfl) ⟨1252224, by rfl⟩ : syracuseStep 3339265 = 2504449) B2504449
theorem B1782827 : Blo 1172403 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B5715011 : Blo 1172403 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B14283863 : Blo 1172403 14283863 := bstep (se 1 (by rfl) ⟨10712897, by rfl⟩ : syracuseStep 14283863 = 21425795) B21425795
theorem B8459437 : Blo 1172403 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B4453613 : Blo 1172403 4453613 := bstep (se 3 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 4453613 = 1670105) B1670105
theorem B6354227 : Blo 1172403 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B5076283 : Blo 1172403 5076283 := bstep (se 1 (by rfl) ⟨3807212, by rfl⟩ : syracuseStep 5076283 = 7614425) B7614425
theorem B1979707 : Blo 1172403 1979707 := bstep (se 1 (by rfl) ⟨1484780, by rfl⟩ : syracuseStep 1979707 = 2969561) B2969561
theorem B8459579 : Blo 1172403 8459579 := bstep (se 1 (by rfl) ⟨6344684, by rfl⟩ : syracuseStep 8459579 = 12689369) B12689369
theorem B1758635 : Blo 1172403 1758635 := bstep (se 1 (by rfl) ⟨1318976, by rfl⟩ : syracuseStep 1758635 = 2637953) B2637953
theorem B1758665 : Blo 1172403 1758665 := bstep (se 2 (by rfl) ⟨659499, by rfl⟩ : syracuseStep 1758665 = 1318999) B1318999
theorem B1979849 : Blo 1172403 1979849 := bstep (se 2 (by rfl) ⟨742443, by rfl⟩ : syracuseStep 1979849 = 1484887) B1484887
theorem B5936651 : Blo 1172403 5936651 := bstep (se 1 (by rfl) ⟨4452488, by rfl⟩ : syracuseStep 5936651 = 8904977) B8904977
theorem B2971151 : Blo 1172403 2971151 := bstep (se 1 (by rfl) ⟨2228363, by rfl⟩ : syracuseStep 2971151 = 4456727) B4456727
theorem B4757021 : Blo 1172403 4757021 := bstep (se 3 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 4757021 = 1783883) B1783883
theorem B14267947 : Blo 1172403 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B3962411 : Blo 1172403 3962411 := bstep (se 1 (by rfl) ⟨2971808, by rfl⟩ : syracuseStep 3962411 = 5943617) B5943617
theorem B1758779 : Blo 1172403 1758779 := bstep (se 1 (by rfl) ⟨1319084, by rfl⟩ : syracuseStep 1758779 = 2638169) B2638169
theorem B6108739 : Blo 1172403 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B1758839 : Blo 1172403 1758839 := bstep (se 1 (by rfl) ⟨1319129, by rfl⟩ : syracuseStep 1758839 = 2638259) B2638259
theorem B1758863 : Blo 1172403 1758863 := bstep (se 1 (by rfl) ⟨1319147, by rfl⟩ : syracuseStep 1758863 = 2638295) B2638295
theorem B5936813 : Blo 1172403 5936813 := bstep (se 3 (by rfl) ⟨1113152, by rfl⟩ : syracuseStep 5936813 = 2226305) B2226305
theorem B1758905 : Blo 1172403 1758905 := bstep (se 2 (by rfl) ⟨659589, by rfl⟩ : syracuseStep 1758905 = 1319179) B1319179
theorem B1758983 : Blo 1172403 1758983 := bstep (se 1 (by rfl) ⟨1319237, by rfl⟩ : syracuseStep 1758983 = 2638475) B2638475
theorem B1759019 : Blo 1172403 1759019 := bstep (se 1 (by rfl) ⟨1319264, by rfl⟩ : syracuseStep 1759019 = 2638529) B2638529
theorem B9647923 : Blo 1172403 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B1759049 : Blo 1172403 1759049 := bstep (se 2 (by rfl) ⟨659643, by rfl⟩ : syracuseStep 1759049 = 1319287) B1319287
theorem B2226055 : Blo 1172403 2226055 := bstep (se 1 (by rfl) ⟨1669541, by rfl⟩ : syracuseStep 2226055 = 3339083) B3339083
theorem B4454297 : Blo 1172403 4454297 := bstep (se 2 (by rfl) ⟨1670361, by rfl⟩ : syracuseStep 4454297 = 3340723) B3340723
theorem B1759163 : Blo 1172403 1759163 := bstep (se 1 (by rfl) ⟨1319372, by rfl⟩ : syracuseStep 1759163 = 2638745) B2638745
theorem B5011409 : Blo 1172403 5011409 := bstep (se 2 (by rfl) ⟨1879278, by rfl⟩ : syracuseStep 5011409 = 3758557) B3758557
theorem B1759223 : Blo 1172403 1759223 := bstep (se 1 (by rfl) ⟨1319417, by rfl⟩ : syracuseStep 1759223 = 2638835) B2638835
theorem B1759247 : Blo 1172403 1759247 := bstep (se 1 (by rfl) ⟨1319435, by rfl⟩ : syracuseStep 1759247 = 2638871) B2638871
theorem B1759289 : Blo 1172403 1759289 := bstep (se 2 (by rfl) ⟨659733, by rfl⟩ : syracuseStep 1759289 = 1319467) B1319467
theorem B1759367 : Blo 1172403 1759367 := bstep (se 1 (by rfl) ⟨1319525, by rfl⟩ : syracuseStep 1759367 = 2639051) B2639051
theorem B1980551 : Blo 1172403 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B1759403 : Blo 1172403 1759403 := bstep (se 1 (by rfl) ⟨1319552, by rfl⟩ : syracuseStep 1759403 = 2639105) B2639105
theorem B1759433 : Blo 1172403 1759433 := bstep (se 2 (by rfl) ⟨659787, by rfl⟩ : syracuseStep 1759433 = 1319575) B1319575
theorem B4888777 : Blo 1172403 4888777 := bstep (se 2 (by rfl) ⟨1833291, by rfl⟩ : syracuseStep 4888777 = 3666583) B3666583
theorem B2971849 : Blo 1172403 2971849 := bstep (se 2 (by rfl) ⟨1114443, by rfl⟩ : syracuseStep 2971849 = 2228887) B2228887
theorem B5503177 : Blo 1172403 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B1759547 : Blo 1172403 1759547 := bstep (se 1 (by rfl) ⟨1319660, by rfl⟩ : syracuseStep 1759547 = 2639321) B2639321
theorem B38558017 : Blo 1172403 38558017 := bstep (se 2 (by rfl) ⟨14459256, by rfl⟩ : syracuseStep 38558017 = 28918513) B28918513
theorem B2971991 : Blo 1172403 2971991 := bstep (se 1 (by rfl) ⟨2228993, by rfl⟩ : syracuseStep 2971991 = 4457987) B4457987
theorem B1759607 : Blo 1172403 1759607 := bstep (se 1 (by rfl) ⟨1319705, by rfl⟩ : syracuseStep 1759607 = 2639411) B2639411
theorem B1759631 : Blo 1172403 1759631 := bstep (se 1 (by rfl) ⟨1319723, by rfl⟩ : syracuseStep 1759631 = 2639447) B2639447
theorem B2505107 : Blo 1172403 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B2677139 : Blo 1172403 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B1759673 : Blo 1172403 1759673 := bstep (se 2 (by rfl) ⟨659877, by rfl⟩ : syracuseStep 1759673 = 1319755) B1319755
theorem B6429149 : Blo 1172403 6429149 := bstep (se 3 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 6429149 = 2410931) B2410931
theorem B1759751 : Blo 1172403 1759751 := bstep (se 1 (by rfl) ⟨1319813, by rfl⟩ : syracuseStep 1759751 = 2639627) B2639627
theorem B1759787 : Blo 1172403 1759787 := bstep (se 1 (by rfl) ⟨1319840, by rfl⟩ : syracuseStep 1759787 = 2639681) B2639681
theorem B1808939 : Blo 1172403 1808939 := bstep (se 1 (by rfl) ⟨1356704, by rfl⟩ : syracuseStep 1808939 = 2713409) B2713409
theorem B1759817 : Blo 1172403 1759817 := bstep (se 2 (by rfl) ⟨659931, by rfl⟩ : syracuseStep 1759817 = 1319863) B1319863
theorem B1759931 : Blo 1172403 1759931 := bstep (se 1 (by rfl) ⟨1319948, by rfl⟩ : syracuseStep 1759931 = 2639897) B2639897
theorem B1759991 : Blo 1172403 1759991 := bstep (se 1 (by rfl) ⟨1319993, by rfl⟩ : syracuseStep 1759991 = 2639987) B2639987
theorem B1760015 : Blo 1172403 1760015 := bstep (se 1 (by rfl) ⟨1320011, by rfl⟩ : syracuseStep 1760015 = 2640023) B2640023
theorem B1981199 : Blo 1172403 1981199 := bstep (se 1 (by rfl) ⟨1485899, by rfl⟩ : syracuseStep 1981199 = 2971799) B2971799
theorem B1760057 : Blo 1172403 1760057 := bstep (se 2 (by rfl) ⟨660021, by rfl⟩ : syracuseStep 1760057 = 1320043) B1320043
theorem B4455283 : Blo 1172403 4455283 := bstep (se 1 (by rfl) ⟨3341462, by rfl⟩ : syracuseStep 4455283 = 6682925) B6682925
theorem B1760135 : Blo 1172403 1760135 := bstep (se 1 (by rfl) ⟨1320101, by rfl⟩ : syracuseStep 1760135 = 2640203) B2640203
theorem B1760171 : Blo 1172403 1760171 := bstep (se 1 (by rfl) ⟨1320128, by rfl⟩ : syracuseStep 1760171 = 2640257) B2640257
theorem B1760201 : Blo 1172403 1760201 := bstep (se 2 (by rfl) ⟨660075, by rfl⟩ : syracuseStep 1760201 = 1320151) B1320151
theorem B1760315 : Blo 1172403 1760315 := bstep (se 1 (by rfl) ⟨1320236, by rfl⟩ : syracuseStep 1760315 = 2640473) B2640473
theorem B1760375 : Blo 1172403 1760375 := bstep (se 1 (by rfl) ⟨1320281, by rfl⟩ : syracuseStep 1760375 = 2640563) B2640563
theorem B1760399 : Blo 1172403 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B1760441 : Blo 1172403 1760441 := bstep (se 2 (by rfl) ⟨660165, by rfl⟩ : syracuseStep 1760441 = 1320331) B1320331
theorem B2677961 : Blo 1172403 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B5938433 : Blo 1172403 5938433 := bstep (se 2 (by rfl) ⟨2226912, by rfl⟩ : syracuseStep 5938433 = 4453825) B4453825
theorem B1760519 : Blo 1172403 1760519 := bstep (se 1 (by rfl) ⟨1320389, by rfl⟩ : syracuseStep 1760519 = 2640779) B2640779
theorem B1760555 : Blo 1172403 1760555 := bstep (se 1 (by rfl) ⟨1320416, by rfl⟩ : syracuseStep 1760555 = 2640833) B2640833
theorem B1981739 : Blo 1172403 1981739 := bstep (se 1 (by rfl) ⟨1486304, by rfl⟩ : syracuseStep 1981739 = 2972609) B2972609
theorem B69483835 : Blo 1172403 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B1760585 : Blo 1172403 1760585 := bstep (se 2 (by rfl) ⟨660219, by rfl⟩ : syracuseStep 1760585 = 1320439) B1320439
theorem B1760699 : Blo 1172403 1760699 := bstep (se 1 (by rfl) ⟨1320524, by rfl⟩ : syracuseStep 1760699 = 2641049) B2641049
theorem B2227657 : Blo 1172403 2227657 := bstep (se 2 (by rfl) ⟨835371, by rfl⟩ : syracuseStep 2227657 = 1670743) B1670743
theorem B1760759 : Blo 1172403 1760759 := bstep (se 1 (by rfl) ⟨1320569, by rfl⟩ : syracuseStep 1760759 = 2641139) B2641139
theorem B1670663 : Blo 1172403 1670663 := bstep (se 1 (by rfl) ⟨1252997, by rfl⟩ : syracuseStep 1670663 = 2505995) B2505995
theorem B1760783 : Blo 1172403 1760783 := bstep (se 1 (by rfl) ⟨1320587, by rfl⟩ : syracuseStep 1760783 = 2641175) B2641175
theorem B3759659 : Blo 1172403 3759659 := bstep (se 1 (by rfl) ⟨2819744, by rfl⟩ : syracuseStep 3759659 = 5639489) B5639489
theorem B1760825 : Blo 1172403 1760825 := bstep (se 2 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 1760825 = 1320619) B1320619
theorem B1760903 : Blo 1172403 1760903 := bstep (se 1 (by rfl) ⟨1320677, by rfl⟩ : syracuseStep 1760903 = 2641355) B2641355
theorem B1760939 : Blo 1172403 1760939 := bstep (se 1 (by rfl) ⟨1320704, by rfl⟩ : syracuseStep 1760939 = 2641409) B2641409
theorem B2817737 : Blo 1172403 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B1760969 : Blo 1172403 1760969 := bstep (se 2 (by rfl) ⟨660363, by rfl⟩ : syracuseStep 1760969 = 1320727) B1320727
theorem B13549285 : Blo 1172403 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B4226849 : Blo 1172403 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B6348577 : Blo 1172403 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B14262065 : Blo 1172403 14262065 := bstep (se 2 (by rfl) ⟨5348274, by rfl⟩ : syracuseStep 14262065 = 10696549) B10696549
theorem B1670971 : Blo 1172403 1670971 := bstep (se 1 (by rfl) ⟨1253228, by rfl⟩ : syracuseStep 1670971 = 2506457) B2506457
theorem B1761083 : Blo 1172403 1761083 := bstep (se 1 (by rfl) ⟨1320812, by rfl⟩ : syracuseStep 1761083 = 2641625) B2641625
theorem B1761143 : Blo 1172403 1761143 := bstep (se 1 (by rfl) ⟨1320857, by rfl⟩ : syracuseStep 1761143 = 2641715) B2641715
theorem B3342215 : Blo 1172403 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B1761167 : Blo 1172403 1761167 := bstep (se 1 (by rfl) ⟨1320875, by rfl⟩ : syracuseStep 1761167 = 2641751) B2641751
theorem B1761209 : Blo 1172403 1761209 := bstep (se 2 (by rfl) ⟨660453, by rfl⟩ : syracuseStep 1761209 = 1320907) B1320907
theorem B4227079 : Blo 1172403 4227079 := bstep (se 1 (by rfl) ⟨3170309, by rfl⟩ : syracuseStep 4227079 = 6340619) B6340619
theorem B2007047 : Blo 1172403 2007047 := bstep (se 1 (by rfl) ⟨1505285, by rfl⟩ : syracuseStep 2007047 = 3010571) B3010571
theorem B2228303 : Blo 1172403 2228303 := bstep (se 1 (by rfl) ⟨1671227, by rfl⟩ : syracuseStep 2228303 = 3342455) B3342455
theorem B1761359 : Blo 1172403 1761359 := bstep (se 1 (by rfl) ⟨1321019, by rfl⟩ : syracuseStep 1761359 = 2642039) B2642039
theorem B4456529 : Blo 1172403 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B1319035 : Blo 1172403 1319035 := bstep (se 1 (by rfl) ⟨989276, by rfl⟩ : syracuseStep 1319035 = 1978553) B1978553
theorem B1761479 : Blo 1172403 1761479 := bstep (se 1 (by rfl) ⟨1321109, by rfl⟩ : syracuseStep 1761479 = 2642219) B2642219
theorem B8913239 : Blo 1172403 8913239 := bstep (se 1 (by rfl) ⟨6684929, by rfl⟩ : syracuseStep 8913239 = 13369859) B13369859
theorem B32579941 : Blo 1172403 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B1671529 : Blo 1172403 1671529 := bstep (se 2 (by rfl) ⟨626823, by rfl⟩ : syracuseStep 1671529 = 1253647) B1253647
theorem B2638223 : Blo 1172403 2638223 := bstep (se 1 (by rfl) ⟨1978667, by rfl⟩ : syracuseStep 2638223 = 3957335) B3957335
theorem B3957281 : Blo 1172403 3957281 := bstep (se 2 (by rfl) ⟨1483980, by rfl⟩ : syracuseStep 3957281 = 2967961) B2967961
theorem B1409575 : Blo 1172403 1409575 := bstep (se 1 (by rfl) ⟨1057181, by rfl⟩ : syracuseStep 1409575 = 2114363) B2114363
theorem B15032891 : Blo 1172403 15032891 := bstep (se 1 (by rfl) ⟨11274668, by rfl⟩ : syracuseStep 15032891 = 22549337) B22549337
theorem B1319503 : Blo 1172403 1319503 := bstep (se 1 (by rfl) ⟨989627, by rfl⟩ : syracuseStep 1319503 = 1979255) B1979255
theorem B3760775 : Blo 1172403 3760775 := bstep (se 1 (by rfl) ⟨2820581, by rfl⟩ : syracuseStep 3760775 = 5641163) B5641163
theorem B1188551 : Blo 1172403 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B10019537 : Blo 1172403 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B2638547 : Blo 1172403 2638547 := bstep (se 1 (by rfl) ⟨1978910, by rfl⟩ : syracuseStep 2638547 = 3957821) B3957821
theorem B3810007 : Blo 1172403 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B3957497 : Blo 1172403 3957497 := bstep (se 2 (by rfl) ⟨1484061, by rfl⟩ : syracuseStep 3957497 = 2968123) B2968123
theorem B2507593 : Blo 1172403 2507593 := bstep (se 2 (by rfl) ⟨940347, by rfl⟩ : syracuseStep 2507593 = 1880695) B1880695
theorem B2114399 : Blo 1172403 2114399 := bstep (se 1 (by rfl) ⟨1585799, by rfl⟩ : syracuseStep 2114399 = 3171599) B3171599
theorem B4236151 : Blo 1172403 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1172423 : Blo 1172403 1172423 := bstep (se 1 (by rfl) ⟨879317, by rfl⟩ : syracuseStep 1172423 = 1758635) B1758635
theorem B1172443 : Blo 1172403 1172443 := bstep (se 1 (by rfl) ⟨879332, by rfl⟩ : syracuseStep 1172443 = 1758665) B1758665
theorem B1319899 : Blo 1172403 1319899 := bstep (se 1 (by rfl) ⟨989924, by rfl⟩ : syracuseStep 1319899 = 1979849) B1979849
theorem B3957767 : Blo 1172403 3957767 := bstep (se 1 (by rfl) ⟨2968325, by rfl⟩ : syracuseStep 3957767 = 5936651) B5936651
theorem B3171347 : Blo 1172403 3171347 := bstep (se 1 (by rfl) ⟨2378510, by rfl⟩ : syracuseStep 3171347 = 4757021) B4757021
theorem B1172519 : Blo 1172403 1172519 := bstep (se 1 (by rfl) ⟨879389, by rfl⟩ : syracuseStep 1172519 = 1758779) B1758779
theorem B21398579 : Blo 1172403 21398579 := bstep (se 1 (by rfl) ⟨16048934, by rfl⟩ : syracuseStep 21398579 = 32097869) B32097869
theorem B1172559 : Blo 1172403 1172559 := bstep (se 1 (by rfl) ⟨879419, by rfl⟩ : syracuseStep 1172559 = 1758839) B1758839
theorem B1172575 : Blo 1172403 1172575 := bstep (se 1 (by rfl) ⟨879431, by rfl⟩ : syracuseStep 1172575 = 1758863) B1758863
theorem B3957875 : Blo 1172403 3957875 := bstep (se 1 (by rfl) ⟨2968406, by rfl⟩ : syracuseStep 3957875 = 5936813) B5936813
theorem B1172603 : Blo 1172403 1172603 := bstep (se 1 (by rfl) ⟨879452, by rfl⟩ : syracuseStep 1172603 = 1758905) B1758905
theorem B5940377 : Blo 1172403 5940377 := bstep (se 2 (by rfl) ⟨2227641, by rfl⟩ : syracuseStep 5940377 = 4455283) B4455283
theorem B2229419 : Blo 1172403 2229419 := bstep (se 1 (by rfl) ⟨1672064, by rfl⟩ : syracuseStep 2229419 = 3344129) B3344129
theorem B1172655 : Blo 1172403 1172655 := bstep (se 1 (by rfl) ⟨879491, by rfl⟩ : syracuseStep 1172655 = 1758983) B1758983
theorem B4228291 : Blo 1172403 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B5014723 : Blo 1172403 5014723 := bstep (se 1 (by rfl) ⟨3761042, by rfl⟩ : syracuseStep 5014723 = 7522085) B7522085
theorem B1172679 : Blo 1172403 1172679 := bstep (se 1 (by rfl) ⟨879509, by rfl⟩ : syracuseStep 1172679 = 1759019) B1759019
theorem B1172699 : Blo 1172403 1172699 := bstep (se 1 (by rfl) ⟨879524, by rfl⟩ : syracuseStep 1172699 = 1759049) B1759049
theorem B1172775 : Blo 1172403 1172775 := bstep (se 1 (by rfl) ⟨879581, by rfl⟩ : syracuseStep 1172775 = 1759163) B1759163
theorem B1172815 : Blo 1172403 1172815 := bstep (se 1 (by rfl) ⟨879611, by rfl⟩ : syracuseStep 1172815 = 1759223) B1759223
theorem B1172831 : Blo 1172403 1172831 := bstep (se 1 (by rfl) ⟨879623, by rfl⟩ : syracuseStep 1172831 = 1759247) B1759247
theorem B1172859 : Blo 1172403 1172859 := bstep (se 1 (by rfl) ⟨879644, by rfl⟩ : syracuseStep 1172859 = 1759289) B1759289
theorem B3958145 : Blo 1172403 3958145 := bstep (se 2 (by rfl) ⟨1484304, by rfl⟩ : syracuseStep 3958145 = 2968609) B2968609
theorem B9160109 : Blo 1172403 9160109 := bstep (se 3 (by rfl) ⟨1717520, by rfl⟩ : syracuseStep 9160109 = 3435041) B3435041
theorem B1172911 : Blo 1172403 1172911 := bstep (se 1 (by rfl) ⟨879683, by rfl⟩ : syracuseStep 1172911 = 1759367) B1759367
theorem B1320367 : Blo 1172403 1320367 := bstep (se 1 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 1320367 = 1980551) B1980551
theorem B1172935 : Blo 1172403 1172935 := bstep (se 1 (by rfl) ⟨879701, by rfl⟩ : syracuseStep 1172935 = 1759403) B1759403
theorem B1172955 : Blo 1172403 1172955 := bstep (se 1 (by rfl) ⟨879716, by rfl⟩ : syracuseStep 1172955 = 1759433) B1759433
theorem B4458017 : Blo 1172403 4458017 := bstep (se 2 (by rfl) ⟨1671756, by rfl⟩ : syracuseStep 4458017 = 3343513) B3343513
theorem B1173031 : Blo 1172403 1173031 := bstep (se 1 (by rfl) ⟨879773, by rfl⟩ : syracuseStep 1173031 = 1759547) B1759547
theorem B1173071 : Blo 1172403 1173071 := bstep (se 1 (by rfl) ⟨879803, by rfl⟩ : syracuseStep 1173071 = 1759607) B1759607
theorem B1173087 : Blo 1172403 1173087 := bstep (se 1 (by rfl) ⟨879815, by rfl⟩ : syracuseStep 1173087 = 1759631) B1759631
theorem B3761761 : Blo 1172403 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B2639483 : Blo 1172403 2639483 := bstep (se 1 (by rfl) ⟨1979612, by rfl⟩ : syracuseStep 2639483 = 3959225) B3959225
theorem B1173115 : Blo 1172403 1173115 := bstep (se 1 (by rfl) ⟨879836, by rfl⟩ : syracuseStep 1173115 = 1759673) B1759673
theorem B4286099 : Blo 1172403 4286099 := bstep (se 1 (by rfl) ⟨3214574, by rfl⟩ : syracuseStep 4286099 = 6429149) B6429149
theorem B1173167 : Blo 1172403 1173167 := bstep (se 1 (by rfl) ⟨879875, by rfl⟩ : syracuseStep 1173167 = 1759751) B1759751
theorem B1173191 : Blo 1172403 1173191 := bstep (se 1 (by rfl) ⟨879893, by rfl⟩ : syracuseStep 1173191 = 1759787) B1759787
theorem B1205959 : Blo 1172403 1205959 := bstep (se 1 (by rfl) ⟨904469, by rfl⟩ : syracuseStep 1205959 = 1808939) B1808939
theorem B4458199 : Blo 1172403 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B1173211 : Blo 1172403 1173211 := bstep (se 1 (by rfl) ⟨879908, by rfl⟩ : syracuseStep 1173211 = 1759817) B1759817
theorem B6768377 : Blo 1172403 6768377 := bstep (se 2 (by rfl) ⟨2538141, by rfl⟩ : syracuseStep 6768377 = 5076283) B5076283
theorem B2639609 : Blo 1172403 2639609 := bstep (se 2 (by rfl) ⟨989853, by rfl⟩ : syracuseStep 2639609 = 1979707) B1979707
theorem B1173287 : Blo 1172403 1173287 := bstep (se 1 (by rfl) ⟨879965, by rfl⟩ : syracuseStep 1173287 = 1759931) B1759931
theorem B1173327 : Blo 1172403 1173327 := bstep (se 1 (by rfl) ⟨879995, by rfl⟩ : syracuseStep 1173327 = 1759991) B1759991
theorem B1173343 : Blo 1172403 1173343 := bstep (se 1 (by rfl) ⟨880007, by rfl⟩ : syracuseStep 1173343 = 1760015) B1760015
theorem B1320799 : Blo 1172403 1320799 := bstep (se 1 (by rfl) ⟨990599, by rfl⟩ : syracuseStep 1320799 = 1981199) B1981199
theorem B1173371 : Blo 1172403 1173371 := bstep (se 1 (by rfl) ⟨880028, by rfl⟩ : syracuseStep 1173371 = 1760057) B1760057
theorem B1173423 : Blo 1172403 1173423 := bstep (se 1 (by rfl) ⟨880067, by rfl⟩ : syracuseStep 1173423 = 1760135) B1760135
theorem B1173447 : Blo 1172403 1173447 := bstep (se 1 (by rfl) ⟨880085, by rfl⟩ : syracuseStep 1173447 = 1760171) B1760171
theorem B1173467 : Blo 1172403 1173467 := bstep (se 1 (by rfl) ⟨880100, by rfl⟩ : syracuseStep 1173467 = 1760201) B1760201
theorem B2639879 : Blo 1172403 2639879 := bstep (se 1 (by rfl) ⟨1979909, by rfl⟩ : syracuseStep 2639879 = 3959819) B3959819
theorem B4458503 : Blo 1172403 4458503 := bstep (se 1 (by rfl) ⟨3343877, by rfl⟩ : syracuseStep 4458503 = 6687755) B6687755
theorem B1173543 : Blo 1172403 1173543 := bstep (se 1 (by rfl) ⟨880157, by rfl⟩ : syracuseStep 1173543 = 1760315) B1760315
theorem B19023929 : Blo 1172403 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B2639951 : Blo 1172403 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B1173583 : Blo 1172403 1173583 := bstep (se 1 (by rfl) ⟨880187, by rfl⟩ : syracuseStep 1173583 = 1760375) B1760375
theorem B1173599 : Blo 1172403 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B8685683 : Blo 1172403 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B1173627 : Blo 1172403 1173627 := bstep (se 1 (by rfl) ⟨880220, by rfl⟩ : syracuseStep 1173627 = 1760441) B1760441
theorem B3958955 : Blo 1172403 3958955 := bstep (se 1 (by rfl) ⟨2969216, by rfl⟩ : syracuseStep 3958955 = 5938433) B5938433
theorem B1173679 : Blo 1172403 1173679 := bstep (se 1 (by rfl) ⟨880259, by rfl⟩ : syracuseStep 1173679 = 1760519) B1760519
theorem B2377927 : Blo 1172403 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B1173703 : Blo 1172403 1173703 := bstep (se 1 (by rfl) ⟨880277, by rfl⟩ : syracuseStep 1173703 = 1760555) B1760555
theorem B1321159 : Blo 1172403 1321159 := bstep (se 1 (by rfl) ⟨990869, by rfl⟩ : syracuseStep 1321159 = 1981739) B1981739
theorem B1173723 : Blo 1172403 1173723 := bstep (se 1 (by rfl) ⟨880292, by rfl⟩ : syracuseStep 1173723 = 1760585) B1760585
theorem B2967799 : Blo 1172403 2967799 := bstep (se 1 (by rfl) ⟨2225849, by rfl⟩ : syracuseStep 2967799 = 4451699) B4451699
theorem B1173799 : Blo 1172403 1173799 := bstep (se 1 (by rfl) ⟨880349, by rfl⟩ : syracuseStep 1173799 = 1760699) B1760699
theorem B18065713 : Blo 1172403 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B1173839 : Blo 1172403 1173839 := bstep (se 1 (by rfl) ⟨880379, by rfl⟩ : syracuseStep 1173839 = 1760759) B1760759
theorem B1173855 : Blo 1172403 1173855 := bstep (se 1 (by rfl) ⟨880391, by rfl⟩ : syracuseStep 1173855 = 1760783) B1760783
theorem B5081449 : Blo 1172403 5081449 := bstep (se 2 (by rfl) ⟨1905543, by rfl⟩ : syracuseStep 5081449 = 3811087) B3811087
theorem B2713961 : Blo 1172403 2713961 := bstep (se 2 (by rfl) ⟨1017735, by rfl⟩ : syracuseStep 2713961 = 2035471) B2035471
theorem B1173883 : Blo 1172403 1173883 := bstep (se 1 (by rfl) ⟨880412, by rfl⟩ : syracuseStep 1173883 = 1760825) B1760825
theorem B8464769 : Blo 1172403 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B12863897 : Blo 1172403 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B1173935 : Blo 1172403 1173935 := bstep (se 1 (by rfl) ⟨880451, by rfl⟩ : syracuseStep 1173935 = 1760903) B1760903
theorem B1173959 : Blo 1172403 1173959 := bstep (se 1 (by rfl) ⟨880469, by rfl⟩ : syracuseStep 1173959 = 1760939) B1760939
theorem B1878491 : Blo 1172403 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B2640347 : Blo 1172403 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B1173979 : Blo 1172403 1173979 := bstep (se 1 (by rfl) ⟨880484, by rfl⟩ : syracuseStep 1173979 = 1760969) B1760969
theorem B4458989 : Blo 1172403 4458989 := bstep (se 3 (by rfl) ⟨836060, by rfl⟩ : syracuseStep 4458989 = 1672121) B1672121
theorem B4753907 : Blo 1172403 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B2968073 : Blo 1172403 2968073 := bstep (se 2 (by rfl) ⟨1113027, by rfl⟩ : syracuseStep 2968073 = 2226055) B2226055
theorem B2968103 : Blo 1172403 2968103 := bstep (se 1 (by rfl) ⟨2226077, by rfl⟩ : syracuseStep 2968103 = 4452155) B4452155
theorem B1174055 : Blo 1172403 1174055 := bstep (se 1 (by rfl) ⟨880541, by rfl⟩ : syracuseStep 1174055 = 1761083) B1761083
theorem B2116135 : Blo 1172403 2116135 := bstep (se 1 (by rfl) ⟨1587101, by rfl⟩ : syracuseStep 2116135 = 3174203) B3174203
theorem B1174095 : Blo 1172403 1174095 := bstep (se 1 (by rfl) ⟨880571, by rfl⟩ : syracuseStep 1174095 = 1761143) B1761143
theorem B1174111 : Blo 1172403 1174111 := bstep (se 1 (by rfl) ⟨880583, by rfl⟩ : syracuseStep 1174111 = 1761167) B1761167
theorem B1174139 : Blo 1172403 1174139 := bstep (se 1 (by rfl) ⟨880604, by rfl⟩ : syracuseStep 1174139 = 1761209) B1761209
theorem B1174191 : Blo 1172403 1174191 := bstep (se 1 (by rfl) ⟨880643, by rfl⟩ : syracuseStep 1174191 = 1761287) B1761287
theorem B3959495 : Blo 1172403 3959495 := bstep (se 1 (by rfl) ⟨2969621, by rfl⟩ : syracuseStep 3959495 = 5939243) B5939243
theorem B1174215 : Blo 1172403 1174215 := bstep (se 1 (by rfl) ⟨880661, by rfl⟩ : syracuseStep 1174215 = 1761323) B1761323
theorem B1174235 : Blo 1172403 1174235 := bstep (se 1 (by rfl) ⟨880676, by rfl⟩ : syracuseStep 1174235 = 1761353) B1761353
theorem B1174311 : Blo 1172403 1174311 := bstep (se 1 (by rfl) ⟨880733, by rfl⟩ : syracuseStep 1174311 = 1761467) B1761467
theorem B1174351 : Blo 1172403 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1174367 : Blo 1172403 1174367 := bstep (se 1 (by rfl) ⟨880775, by rfl⟩ : syracuseStep 1174367 = 1761551) B1761551
theorem B2968427 : Blo 1172403 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B1174395 : Blo 1172403 1174395 := bstep (se 1 (by rfl) ⟨880796, by rfl⟩ : syracuseStep 1174395 = 1761593) B1761593
theorem B2640815 : Blo 1172403 2640815 := bstep (se 1 (by rfl) ⟨1980611, by rfl⟩ : syracuseStep 2640815 = 3961223) B3961223
theorem B2641067 : Blo 1172403 2641067 := bstep (se 1 (by rfl) ⟨1980800, by rfl⟩ : syracuseStep 2641067 = 3961601) B3961601
theorem B9522575 : Blo 1172403 9522575 := bstep (se 1 (by rfl) ⟨7141931, by rfl⟩ : syracuseStep 9522575 = 14283863) B14283863
theorem B18050485 : Blo 1172403 18050485 := bstep (se 5 (by rfl) ⟨846116, by rfl⟩ : syracuseStep 18050485 = 1692233) B1692233
theorem B6680009 : Blo 1172403 6680009 := bstep (se 2 (by rfl) ⟨2505003, by rfl⟩ : syracuseStep 6680009 = 5010007) B5010007
theorem B2969075 : Blo 1172403 2969075 := bstep (se 1 (by rfl) ⟨2226806, by rfl⟩ : syracuseStep 2969075 = 4453613) B4453613
theorem B3960359 : Blo 1172403 3960359 := bstep (se 1 (by rfl) ⟨2970269, by rfl⟩ : syracuseStep 3960359 = 5940539) B5940539
theorem B5639719 : Blo 1172403 5639719 := bstep (se 1 (by rfl) ⟨4229789, by rfl⟩ : syracuseStep 5639719 = 8459579) B8459579
theorem B3960467 : Blo 1172403 3960467 := bstep (se 1 (by rfl) ⟨2970350, by rfl⟩ : syracuseStep 3960467 = 5940701) B5940701
theorem B2641607 : Blo 1172403 2641607 := bstep (se 1 (by rfl) ⟨1981205, by rfl⟩ : syracuseStep 2641607 = 3962411) B3962411
theorem B3960683 : Blo 1172403 3960683 := bstep (se 1 (by rfl) ⟨2970512, by rfl⟩ : syracuseStep 3960683 = 5941025) B5941025
theorem B3960737 : Blo 1172403 3960737 := bstep (se 2 (by rfl) ⟨1485276, by rfl⟩ : syracuseStep 3960737 = 2970553) B2970553
theorem B2969531 : Blo 1172403 2969531 := bstep (se 1 (by rfl) ⟨2227148, by rfl⟩ : syracuseStep 2969531 = 4454297) B4454297
theorem B4452353 : Blo 1172403 4452353 := bstep (se 2 (by rfl) ⟨1669632, by rfl⟩ : syracuseStep 4452353 = 3339265) B3339265
theorem B4452367 : Blo 1172403 4452367 := bstep (se 1 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 4452367 = 6678551) B6678551
theorem B1880393 : Blo 1172403 1880393 := bstep (se 2 (by rfl) ⟨705147, by rfl⟩ : syracuseStep 1880393 = 1410295) B1410295
theorem B4518287 : Blo 1172403 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2257327 : Blo 1172403 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B1978843 : Blo 1172403 1978843 := bstep (se 1 (by rfl) ⟨1484132, by rfl⟩ : syracuseStep 1978843 = 2968265) B2968265
theorem B3961331 : Blo 1172403 3961331 := bstep (se 1 (by rfl) ⟨2970998, by rfl⟩ : syracuseStep 3961331 = 5941997) B5941997
theorem B2970209 : Blo 1172403 2970209 := bstep (se 2 (by rfl) ⟨1113828, by rfl⟩ : syracuseStep 2970209 = 2227657) B2227657
theorem B3961871 : Blo 1172403 3961871 := bstep (se 1 (by rfl) ⟨2971403, by rfl⟩ : syracuseStep 3961871 = 5942807) B5942807
theorem B18060337 : Blo 1172403 18060337 := bstep (se 2 (by rfl) ⟨6772626, by rfl⟩ : syracuseStep 18060337 = 13545253) B13545253
theorem B1979471 : Blo 1172403 1979471 := bstep (se 1 (by rfl) ⟨1484603, by rfl⟩ : syracuseStep 1979471 = 2969207) B2969207
theorem B9508043 : Blo 1172403 9508043 := bstep (se 1 (by rfl) ⟨7131032, by rfl⟩ : syracuseStep 9508043 = 14262065) B14262065
theorem B4453643 : Blo 1172403 4453643 := bstep (se 1 (by rfl) ⟨3340232, by rfl⟩ : syracuseStep 4453643 = 6680465) B6680465
theorem B8459693 : Blo 1172403 8459693 := bstep (se 3 (by rfl) ⟨1586192, by rfl⟩ : syracuseStep 8459693 = 3172385) B3172385
theorem B1758647 : Blo 1172403 1758647 := bstep (se 1 (by rfl) ⟨1318985, by rfl⟩ : syracuseStep 1758647 = 2637971) B2637971
theorem B1758683 : Blo 1172403 1758683 := bstep (se 1 (by rfl) ⟨1319012, by rfl⟩ : syracuseStep 1758683 = 2638025) B2638025
theorem B8910323 : Blo 1172403 8910323 := bstep (se 1 (by rfl) ⟨6682742, by rfl⟩ : syracuseStep 8910323 = 13365485) B13365485
theorem B6518369 : Blo 1172403 6518369 := bstep (se 2 (by rfl) ⟨2444388, by rfl⟩ : syracuseStep 6518369 = 4888777) B4888777
theorem B3962465 : Blo 1172403 3962465 := bstep (se 2 (by rfl) ⟨1485924, by rfl⟩ : syracuseStep 3962465 = 2971849) B2971849
theorem B4454099 : Blo 1172403 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B51410689 : Blo 1172403 51410689 := bstep (se 2 (by rfl) ⟨19279008, by rfl⟩ : syracuseStep 51410689 = 38558017) B38558017
theorem B6338371 : Blo 1172403 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B7141229 : Blo 1172403 7141229 := bstep (se 3 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 7141229 = 2677961) B2677961
theorem B1759151 : Blo 1172403 1759151 := bstep (se 1 (by rfl) ⟨1319363, by rfl⟩ : syracuseStep 1759151 = 2638727) B2638727
theorem B1980335 : Blo 1172403 1980335 := bstep (se 1 (by rfl) ⟨1485251, by rfl⟩ : syracuseStep 1980335 = 2970503) B2970503
theorem B1906615 : Blo 1172403 1906615 := bstep (se 1 (by rfl) ⟨1429961, by rfl⟩ : syracuseStep 1906615 = 2859923) B2859923
theorem B19044305 : Blo 1172403 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B1759241 : Blo 1172403 1759241 := bstep (se 2 (by rfl) ⟨659715, by rfl⟩ : syracuseStep 1759241 = 1319431) B1319431
theorem B5642255 : Blo 1172403 5642255 := bstep (se 1 (by rfl) ⟨4231691, by rfl⟩ : syracuseStep 5642255 = 8463383) B8463383
theorem B2971667 : Blo 1172403 2971667 := bstep (se 1 (by rfl) ⟨2228750, by rfl⟩ : syracuseStep 2971667 = 4457501) B4457501
theorem B1759271 : Blo 1172403 1759271 := bstep (se 1 (by rfl) ⟨1319453, by rfl⟩ : syracuseStep 1759271 = 2638907) B2638907
theorem B1759355 : Blo 1172403 1759355 := bstep (se 1 (by rfl) ⟨1319516, by rfl⟩ : syracuseStep 1759355 = 2639033) B2639033
theorem B1759481 : Blo 1172403 1759481 := bstep (se 2 (by rfl) ⟨659805, by rfl⟩ : syracuseStep 1759481 = 1319611) B1319611
theorem B1759583 : Blo 1172403 1759583 := bstep (se 1 (by rfl) ⟨1319687, by rfl⟩ : syracuseStep 1759583 = 2639375) B2639375
theorem B1980767 : Blo 1172403 1980767 := bstep (se 1 (by rfl) ⟨1485575, by rfl⟩ : syracuseStep 1980767 = 2971151) B2971151
theorem B1759595 : Blo 1172403 1759595 := bstep (se 1 (by rfl) ⟨1319696, by rfl⟩ : syracuseStep 1759595 = 2639393) B2639393
theorem B29350277 : Blo 1172403 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B2972123 : Blo 1172403 2972123 := bstep (se 1 (by rfl) ⟨2229092, by rfl⟩ : syracuseStep 2972123 = 4458185) B4458185
theorem B33839693 : Blo 1172403 33839693 := bstep (se 3 (by rfl) ⟨6344942, by rfl⟩ : syracuseStep 33839693 = 12689885) B12689885
theorem B1759823 : Blo 1172403 1759823 := bstep (se 1 (by rfl) ⟨1319867, by rfl⟩ : syracuseStep 1759823 = 2639735) B2639735
theorem B3340939 : Blo 1172403 3340939 := bstep (se 1 (by rfl) ⟨2505704, by rfl⟩ : syracuseStep 3340939 = 5011409) B5011409
theorem B4455101 : Blo 1172403 4455101 := bstep (se 3 (by rfl) ⟨835331, by rfl⟩ : syracuseStep 4455101 = 1670663) B1670663
theorem B1759943 : Blo 1172403 1759943 := bstep (se 1 (by rfl) ⟨1319957, by rfl⟩ : syracuseStep 1759943 = 2639915) B2639915
theorem B1760105 : Blo 1172403 1760105 := bstep (se 2 (by rfl) ⟨660039, by rfl⟩ : syracuseStep 1760105 = 1320079) B1320079
theorem B1981327 : Blo 1172403 1981327 := bstep (se 1 (by rfl) ⟨1485995, by rfl⟩ : syracuseStep 1981327 = 2971991) B2971991
theorem B11279249 : Blo 1172403 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B16063379 : Blo 1172403 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B17161105 : Blo 1172403 17161105 := bstep (se 2 (by rfl) ⟨6435414, by rfl⟩ : syracuseStep 17161105 = 12870829) B12870829
theorem B1670071 : Blo 1172403 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B1760183 : Blo 1172403 1760183 := bstep (se 1 (by rfl) ⟨1320137, by rfl⟩ : syracuseStep 1760183 = 2640275) B2640275
theorem B1784759 : Blo 1172403 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B1760219 : Blo 1172403 1760219 := bstep (se 1 (by rfl) ⟨1320164, by rfl⟩ : syracuseStep 1760219 = 2640329) B2640329
theorem B370580453 : Blo 1172403 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B15047653 : Blo 1172403 15047653 := bstep (se 4 (by rfl) ⟨1410717, by rfl⟩ : syracuseStep 15047653 = 2821435) B2821435
theorem B1252703 : Blo 1172403 1252703 := bstep (se 1 (by rfl) ⟨939527, by rfl⟩ : syracuseStep 1252703 = 1879055) B1879055
theorem B1760687 : Blo 1172403 1760687 := bstep (se 1 (by rfl) ⟨1320515, by rfl⟩ : syracuseStep 1760687 = 2641031) B2641031
theorem B1760777 : Blo 1172403 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B1760807 : Blo 1172403 1760807 := bstep (se 1 (by rfl) ⟨1320605, by rfl⟩ : syracuseStep 1760807 = 2641211) B2641211
theorem B1760891 : Blo 1172403 1760891 := bstep (se 1 (by rfl) ⟨1320668, by rfl⟩ : syracuseStep 1760891 = 2641337) B2641337
theorem B2506439 : Blo 1172403 2506439 := bstep (se 1 (by rfl) ⟨1879829, by rfl⟩ : syracuseStep 2506439 = 3759659) B3759659
theorem B2227961 : Blo 1172403 2227961 := bstep (se 2 (by rfl) ⟨835485, by rfl⟩ : syracuseStep 2227961 = 1670971) B1670971
theorem B1761017 : Blo 1172403 1761017 := bstep (se 2 (by rfl) ⟨660381, by rfl⟩ : syracuseStep 1761017 = 1320763) B1320763
theorem B8904491 : Blo 1172403 8904491 := bstep (se 1 (by rfl) ⟨6678368, by rfl⟩ : syracuseStep 8904491 = 13356737) B13356737
theorem B4759391 : Blo 1172403 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B1761119 : Blo 1172403 1761119 := bstep (se 1 (by rfl) ⟨1320839, by rfl⟩ : syracuseStep 1761119 = 2641679) B2641679
theorem B2817899 : Blo 1172403 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B1761131 : Blo 1172403 1761131 := bstep (se 1 (by rfl) ⟨1320848, by rfl⟩ : syracuseStep 1761131 = 2641697) B2641697
theorem B2228143 : Blo 1172403 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B5636105 : Blo 1172403 5636105 := bstep (se 2 (by rfl) ⟨2113539, by rfl⟩ : syracuseStep 5636105 = 4227079) B4227079
theorem B1761545 : Blo 1172403 1761545 := bstep (se 2 (by rfl) ⟨660579, by rfl⟩ : syracuseStep 1761545 = 1321159) B1321159
theorem B3957065 : Blo 1172403 3957065 := bstep (se 2 (by rfl) ⟨1483899, by rfl⟩ : syracuseStep 3957065 = 2967799) B2967799
theorem B2638187 : Blo 1172403 2638187 := bstep (se 1 (by rfl) ⟨1978640, by rfl⟩ : syracuseStep 2638187 = 3957281) B3957281
theorem B2507183 : Blo 1172403 2507183 := bstep (se 1 (by rfl) ⟨1880387, by rfl⟩ : syracuseStep 2507183 = 3760775) B3760775
theorem B6775265 : Blo 1172403 6775265 := bstep (se 2 (by rfl) ⟨2540724, by rfl⟩ : syracuseStep 6775265 = 5081449) B5081449
theorem B2228705 : Blo 1172403 2228705 := bstep (se 2 (by rfl) ⟨835764, by rfl⟩ : syracuseStep 2228705 = 1671529) B1671529
theorem B2638331 : Blo 1172403 2638331 := bstep (se 1 (by rfl) ⟨1978748, by rfl⟩ : syracuseStep 2638331 = 3957497) B3957497
theorem B25354781 : Blo 1172403 25354781 := bstep (se 3 (by rfl) ⟨4754021, by rfl⟩ : syracuseStep 25354781 = 9508043) B9508043
theorem B1409599 : Blo 1172403 1409599 := bstep (se 1 (by rfl) ⟨1057199, by rfl⟩ : syracuseStep 1409599 = 2114399) B2114399
theorem B2638457 : Blo 1172403 2638457 := bstep (se 2 (by rfl) ⟨989421, by rfl⟩ : syracuseStep 2638457 = 1978843) B1978843
theorem B2638511 : Blo 1172403 2638511 := bstep (se 1 (by rfl) ⟨1978883, by rfl⟩ : syracuseStep 2638511 = 3957767) B3957767
theorem B2114231 : Blo 1172403 2114231 := bstep (se 1 (by rfl) ⟨1585673, by rfl⟩ : syracuseStep 2114231 = 3171347) B3171347
theorem B1319647 : Blo 1172403 1319647 := bstep (se 1 (by rfl) ⟨989735, by rfl⟩ : syracuseStep 1319647 = 1979471) B1979471
theorem B2638583 : Blo 1172403 2638583 := bstep (se 1 (by rfl) ⟨1978937, by rfl⟩ : syracuseStep 2638583 = 3957875) B3957875
theorem B5014381 : Blo 1172403 5014381 := bstep (se 3 (by rfl) ⟨940196, by rfl⟩ : syracuseStep 5014381 = 1880393) B1880393
theorem B2638763 : Blo 1172403 2638763 := bstep (se 1 (by rfl) ⟨1979072, by rfl⟩ : syracuseStep 2638763 = 3958145) B3958145
theorem B5080009 : Blo 1172403 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B1172431 : Blo 1172403 1172431 := bstep (se 1 (by rfl) ⟨879323, by rfl⟩ : syracuseStep 1172431 = 1758647) B1758647
theorem B1172455 : Blo 1172403 1172455 := bstep (se 1 (by rfl) ⟨879341, by rfl⟩ : syracuseStep 1172455 = 1758683) B1758683
theorem B5940215 : Blo 1172403 5940215 := bstep (se 1 (by rfl) ⟨4455161, by rfl⟩ : syracuseStep 5940215 = 8910323) B8910323
theorem B12682277 : Blo 1172403 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B3343457 : Blo 1172403 3343457 := bstep (se 2 (by rfl) ⟨1253796, by rfl⟩ : syracuseStep 3343457 = 2507593) B2507593
theorem B22881473 : Blo 1172403 22881473 := bstep (se 2 (by rfl) ⟨8580552, by rfl⟩ : syracuseStep 22881473 = 17161105) B17161105
theorem B4760819 : Blo 1172403 4760819 := bstep (se 1 (by rfl) ⟨3570614, by rfl⟩ : syracuseStep 4760819 = 7141229) B7141229
theorem B1172767 : Blo 1172403 1172767 := bstep (se 1 (by rfl) ⟨879575, by rfl⟩ : syracuseStep 1172767 = 1759151) B1759151
theorem B1320223 : Blo 1172403 1320223 := bstep (se 1 (by rfl) ⟨990167, by rfl⟩ : syracuseStep 1320223 = 1980335) B1980335
theorem B20063537 : Blo 1172403 20063537 := bstep (se 2 (by rfl) ⟨7523826, by rfl⟩ : syracuseStep 20063537 = 15047653) B15047653
theorem B1172827 : Blo 1172403 1172827 := bstep (se 1 (by rfl) ⟨879620, by rfl⟩ : syracuseStep 1172827 = 1759241) B1759241
theorem B1172847 : Blo 1172403 1172847 := bstep (se 1 (by rfl) ⟨879635, by rfl⟩ : syracuseStep 1172847 = 1759271) B1759271
theorem B12682619 : Blo 1172403 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B1172903 : Blo 1172403 1172903 := bstep (se 1 (by rfl) ⟨879677, by rfl⟩ : syracuseStep 1172903 = 1759355) B1759355
theorem B2639303 : Blo 1172403 2639303 := bstep (se 1 (by rfl) ⟨1979477, by rfl⟩ : syracuseStep 2639303 = 3958955) B3958955
theorem B1172987 : Blo 1172403 1172987 := bstep (se 1 (by rfl) ⟨879740, by rfl⟩ : syracuseStep 1172987 = 1759481) B1759481
theorem B1173055 : Blo 1172403 1173055 := bstep (se 1 (by rfl) ⟨879791, by rfl⟩ : syracuseStep 1173055 = 1759583) B1759583
theorem B1320511 : Blo 1172403 1320511 := bstep (se 1 (by rfl) ⟨990383, by rfl⟩ : syracuseStep 1320511 = 1980767) B1980767
theorem B1173063 : Blo 1172403 1173063 := bstep (se 1 (by rfl) ⟨879797, by rfl⟩ : syracuseStep 1173063 = 1759595) B1759595
theorem B5637721 : Blo 1172403 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B6686297 : Blo 1172403 6686297 := bstep (se 2 (by rfl) ⟨2507361, by rfl⟩ : syracuseStep 6686297 = 5014723) B5014723
theorem B1173215 : Blo 1172403 1173215 := bstep (se 1 (by rfl) ⟨879911, by rfl⟩ : syracuseStep 1173215 = 1759823) B1759823
theorem B2639663 : Blo 1172403 2639663 := bstep (se 1 (by rfl) ⟨1979747, by rfl⟩ : syracuseStep 2639663 = 3959495) B3959495
theorem B1173295 : Blo 1172403 1173295 := bstep (se 1 (by rfl) ⟨879971, by rfl⟩ : syracuseStep 1173295 = 1759943) B1759943
theorem B1173403 : Blo 1172403 1173403 := bstep (se 1 (by rfl) ⟨880052, by rfl⟩ : syracuseStep 1173403 = 1760105) B1760105
theorem B10708919 : Blo 1172403 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B1173455 : Blo 1172403 1173455 := bstep (se 1 (by rfl) ⟨880091, by rfl⟩ : syracuseStep 1173455 = 1760183) B1760183
theorem B1173479 : Blo 1172403 1173479 := bstep (se 1 (by rfl) ⟨880109, by rfl⟩ : syracuseStep 1173479 = 1760219) B1760219
theorem B5015681 : Blo 1172403 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B1607945 : Blo 1172403 1607945 := bstep (se 2 (by rfl) ⟨602979, by rfl⟩ : syracuseStep 1607945 = 1205959) B1205959
theorem B1173791 : Blo 1172403 1173791 := bstep (se 1 (by rfl) ⟨880343, by rfl⟩ : syracuseStep 1173791 = 1760687) B1760687
theorem B1173851 : Blo 1172403 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B2640239 : Blo 1172403 2640239 := bstep (se 1 (by rfl) ⟨1980179, by rfl⟩ : syracuseStep 2640239 = 3960359) B3960359
theorem B1173871 : Blo 1172403 1173871 := bstep (se 1 (by rfl) ⟨880403, by rfl⟩ : syracuseStep 1173871 = 1760807) B1760807
theorem B1173927 : Blo 1172403 1173927 := bstep (se 1 (by rfl) ⟨880445, by rfl⟩ : syracuseStep 1173927 = 1760891) B1760891
theorem B2640311 : Blo 1172403 2640311 := bstep (se 1 (by rfl) ⟨1980233, by rfl⟩ : syracuseStep 2640311 = 3960467) B3960467
theorem B1485307 : Blo 1172403 1485307 := bstep (se 1 (by rfl) ⟨1113980, by rfl⟩ : syracuseStep 1485307 = 2227961) B2227961
theorem B1174011 : Blo 1172403 1174011 := bstep (se 1 (by rfl) ⟨880508, by rfl⟩ : syracuseStep 1174011 = 1761017) B1761017
theorem B3172927 : Blo 1172403 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B1174079 : Blo 1172403 1174079 := bstep (se 1 (by rfl) ⟨880559, by rfl⟩ : syracuseStep 1174079 = 1761119) B1761119
theorem B1878599 : Blo 1172403 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B2640455 : Blo 1172403 2640455 := bstep (se 1 (by rfl) ⟨1980341, by rfl⟩ : syracuseStep 2640455 = 3960683) B3960683
theorem B1174087 : Blo 1172403 1174087 := bstep (se 1 (by rfl) ⟨880565, by rfl⟩ : syracuseStep 1174087 = 1761131) B1761131
theorem B2542153 : Blo 1172403 2542153 := bstep (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) B1906615
theorem B2640491 : Blo 1172403 2640491 := bstep (se 1 (by rfl) ⟨1980368, by rfl⟩ : syracuseStep 2640491 = 3960737) B3960737
theorem B2968235 : Blo 1172403 2968235 := bstep (se 1 (by rfl) ⟨2226176, by rfl⟩ : syracuseStep 2968235 = 4452353) B4452353
theorem B1338031 : Blo 1172403 1338031 := bstep (se 1 (by rfl) ⟨1003523, by rfl⟩ : syracuseStep 1338031 = 2007047) B2007047
theorem B1485535 : Blo 1172403 1485535 := bstep (se 1 (by rfl) ⟨1114151, by rfl⟩ : syracuseStep 1485535 = 2228303) B2228303
theorem B1174239 : Blo 1172403 1174239 := bstep (se 1 (by rfl) ⟨880679, by rfl⟩ : syracuseStep 1174239 = 1761359) B1761359
theorem B1174319 : Blo 1172403 1174319 := bstep (se 1 (by rfl) ⟨880739, by rfl⟩ : syracuseStep 1174319 = 1761479) B1761479
theorem B5942159 : Blo 1172403 5942159 := bstep (se 1 (by rfl) ⟨4456619, by rfl⟩ : syracuseStep 5942159 = 8913239) B8913239
theorem B2640887 : Blo 1172403 2640887 := bstep (se 1 (by rfl) ⟨1980665, by rfl⟩ : syracuseStep 2640887 = 3961331) B3961331
theorem B10021927 : Blo 1172403 10021927 := bstep (se 1 (by rfl) ⟨7516445, by rfl⟩ : syracuseStep 10021927 = 15032891) B15032891
theorem B24087617 : Blo 1172403 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B6679691 : Blo 1172403 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B2641247 : Blo 1172403 2641247 := bstep (se 1 (by rfl) ⟨1980935, by rfl⟩ : syracuseStep 2641247 = 3961871) B3961871
theorem B14265719 : Blo 1172403 14265719 := bstep (se 1 (by rfl) ⟨10699289, by rfl⟩ : syracuseStep 14265719 = 21398579) B21398579
theorem B1879433 : Blo 1172403 1879433 := bstep (se 2 (by rfl) ⟨704787, by rfl⟩ : syracuseStep 1879433 = 1409575) B1409575
theorem B2821513 : Blo 1172403 2821513 := bstep (se 2 (by rfl) ⟨1058067, by rfl⟩ : syracuseStep 2821513 = 2116135) B2116135
theorem B3960251 : Blo 1172403 3960251 := bstep (se 1 (by rfl) ⟨2970188, by rfl⟩ : syracuseStep 3960251 = 5940377) B5940377
theorem B1486279 : Blo 1172403 1486279 := bstep (se 1 (by rfl) ⟨1114709, by rfl⟩ : syracuseStep 1486279 = 2229419) B2229419
theorem B2969095 : Blo 1172403 2969095 := bstep (se 1 (by rfl) ⟨2226821, by rfl⟩ : syracuseStep 2969095 = 4453643) B4453643
theorem B5639795 : Blo 1172403 5639795 := bstep (se 1 (by rfl) ⟨4229846, by rfl⟩ : syracuseStep 5639795 = 8459693) B8459693
theorem B6106739 : Blo 1172403 6106739 := bstep (se 1 (by rfl) ⟨4580054, by rfl⟩ : syracuseStep 6106739 = 9160109) B9160109
theorem B4345579 : Blo 1172403 4345579 := bstep (se 1 (by rfl) ⟨3259184, by rfl⟩ : syracuseStep 4345579 = 6518369) B6518369
theorem B2641643 : Blo 1172403 2641643 := bstep (se 1 (by rfl) ⟨1981232, by rfl⟩ : syracuseStep 2641643 = 3962465) B3962465
theorem B2969399 : Blo 1172403 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B5648201 : Blo 1172403 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B2641769 : Blo 1172403 2641769 := bstep (se 2 (by rfl) ⟨990663, by rfl⟩ : syracuseStep 2641769 = 1981327) B1981327
theorem B5009309 : Blo 1172403 5009309 := bstep (se 3 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 5009309 = 1878491) B1878491
theorem B274190341 : Blo 1172403 274190341 := bstep (se 4 (by rfl) ⟨25705344, by rfl⟩ : syracuseStep 274190341 = 51410689) B51410689
theorem B24080449 : Blo 1172403 24080449 := bstep (se 2 (by rfl) ⟨9030168, by rfl⟩ : syracuseStep 24080449 = 18060337) B18060337
theorem B19566851 : Blo 1172403 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B1978715 : Blo 1172403 1978715 := bstep (se 1 (by rfl) ⟨1484036, by rfl⟩ : syracuseStep 1978715 = 2968073) B2968073
theorem B1978735 : Blo 1172403 1978735 := bstep (se 1 (by rfl) ⟨1484051, by rfl⟩ : syracuseStep 1978735 = 2968103) B2968103
theorem B2970067 : Blo 1172403 2970067 := bstep (se 1 (by rfl) ⟨2227550, by rfl⟩ : syracuseStep 2970067 = 4455101) B4455101
theorem B1978951 : Blo 1172403 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B12039077 : Blo 1172403 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B5944265 : Blo 1172403 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B4453339 : Blo 1172403 4453339 := bstep (se 1 (by rfl) ⟨3340004, by rfl⟩ : syracuseStep 4453339 = 6680009) B6680009
theorem B1979383 : Blo 1172403 1979383 := bstep (se 1 (by rfl) ⟨1484537, by rfl⟩ : syracuseStep 1979383 = 2969075) B2969075
theorem B8451161 : Blo 1172403 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B5936327 : Blo 1172403 5936327 := bstep (se 1 (by rfl) ⟨4452245, by rfl⟩ : syracuseStep 5936327 = 8904491) B8904491
theorem B2970857 : Blo 1172403 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B1979687 : Blo 1172403 1979687 := bstep (se 1 (by rfl) ⟨1484765, by rfl⟩ : syracuseStep 1979687 = 2969531) B2969531
theorem B5936489 : Blo 1172403 5936489 := bstep (se 2 (by rfl) ⟨2226183, by rfl⟩ : syracuseStep 5936489 = 4452367) B4452367
theorem B15046013 : Blo 1172403 15046013 := bstep (se 3 (by rfl) ⟨2821127, by rfl⟩ : syracuseStep 15046013 = 5642255) B5642255
theorem B2971019 : Blo 1172403 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B1758713 : Blo 1172403 1758713 := bstep (se 2 (by rfl) ⟨659517, by rfl⟩ : syracuseStep 1758713 = 1319035) B1319035
theorem B1758815 : Blo 1172403 1758815 := bstep (se 1 (by rfl) ⟨1319111, by rfl⟩ : syracuseStep 1758815 = 2638223) B2638223
theorem B3012191 : Blo 1172403 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B1980139 : Blo 1172403 1980139 := bstep (se 1 (by rfl) ⟨1485104, by rfl⟩ : syracuseStep 1980139 = 2970209) B2970209
theorem B43439921 : Blo 1172403 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B1759031 : Blo 1172403 1759031 := bstep (se 1 (by rfl) ⟨1319273, by rfl⟩ : syracuseStep 1759031 = 2638547) B2638547
theorem B1759337 : Blo 1172403 1759337 := bstep (se 2 (by rfl) ⟨659751, by rfl⟩ : syracuseStep 1759337 = 1319503) B1319503
theorem B4454585 : Blo 1172403 4454585 := bstep (se 2 (by rfl) ⟨1670469, by rfl⟩ : syracuseStep 4454585 = 3340939) B3340939
theorem B3340541 : Blo 1172403 3340541 := bstep (se 3 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 3340541 = 1252703) B1252703
theorem B2972011 : Blo 1172403 2972011 := bstep (se 1 (by rfl) ⟨2229008, by rfl⟩ : syracuseStep 2972011 = 4458017) B4458017
theorem B1759655 : Blo 1172403 1759655 := bstep (se 1 (by rfl) ⟨1319741, by rfl⟩ : syracuseStep 1759655 = 2639483) B2639483
theorem B2857399 : Blo 1172403 2857399 := bstep (se 1 (by rfl) ⟨2143049, by rfl⟩ : syracuseStep 2857399 = 4286099) B4286099
theorem B4512251 : Blo 1172403 4512251 := bstep (se 1 (by rfl) ⟨3384188, by rfl⟩ : syracuseStep 4512251 = 6768377) B6768377
theorem B1759739 : Blo 1172403 1759739 := bstep (se 1 (by rfl) ⟨1319804, by rfl⟩ : syracuseStep 1759739 = 2639609) B2639609
theorem B2226761 : Blo 1172403 2226761 := bstep (se 2 (by rfl) ⟨835035, by rfl⟩ : syracuseStep 2226761 = 1670071) B1670071
theorem B1759865 : Blo 1172403 1759865 := bstep (se 2 (by rfl) ⟨659949, by rfl⟩ : syracuseStep 1759865 = 1319899) B1319899
theorem B12696203 : Blo 1172403 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B1759919 : Blo 1172403 1759919 := bstep (se 1 (by rfl) ⟨1319939, by rfl⟩ : syracuseStep 1759919 = 2639879) B2639879
theorem B2972335 : Blo 1172403 2972335 := bstep (se 1 (by rfl) ⟨2229251, by rfl⟩ : syracuseStep 2972335 = 4458503) B4458503
theorem B1981111 : Blo 1172403 1981111 := bstep (se 1 (by rfl) ⟨1485833, by rfl⟩ : syracuseStep 1981111 = 2971667) B2971667
theorem B1759967 : Blo 1172403 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B5790455 : Blo 1172403 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B1809307 : Blo 1172403 1809307 := bstep (se 1 (by rfl) ⟨1356980, by rfl⟩ : syracuseStep 1809307 = 2713961) B2713961
theorem B5643179 : Blo 1172403 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B8575931 : Blo 1172403 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B1760231 : Blo 1172403 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B1981415 : Blo 1172403 1981415 := bstep (se 1 (by rfl) ⟨1486061, by rfl⟩ : syracuseStep 1981415 = 2972123) B2972123
theorem B2972659 : Blo 1172403 2972659 := bstep (se 1 (by rfl) ⟨2229494, by rfl⟩ : syracuseStep 2972659 = 4458989) B4458989
theorem B3169271 : Blo 1172403 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B22559795 : Blo 1172403 22559795 := bstep (se 1 (by rfl) ⟨16919846, by rfl⟩ : syracuseStep 22559795 = 33839693) B33839693
theorem B3169469 : Blo 1172403 3169469 := bstep (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) B1188551
theorem B1760489 : Blo 1172403 1760489 := bstep (se 2 (by rfl) ⟨660183, by rfl⟩ : syracuseStep 1760489 = 1320367) B1320367
theorem B24067313 : Blo 1172403 24067313 := bstep (se 2 (by rfl) ⟨9025242, by rfl⟩ : syracuseStep 24067313 = 18050485) B18050485
theorem B7519499 : Blo 1172403 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B1760543 : Blo 1172403 1760543 := bstep (se 1 (by rfl) ⟨1320407, by rfl⟩ : syracuseStep 1760543 = 2640815) B2640815
theorem B247053635 : Blo 1172403 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B7519625 : Blo 1172403 7519625 := bstep (se 2 (by rfl) ⟨2819859, by rfl⟩ : syracuseStep 7519625 = 5639719) B5639719
theorem B1760711 : Blo 1172403 1760711 := bstep (se 1 (by rfl) ⟨1320533, by rfl⟩ : syracuseStep 1760711 = 2641067) B2641067
theorem B6348383 : Blo 1172403 6348383 := bstep (se 1 (by rfl) ⟨4761287, by rfl⟩ : syracuseStep 6348383 = 9522575) B9522575
theorem B1761065 : Blo 1172403 1761065 := bstep (se 2 (by rfl) ⟨660399, by rfl⟩ : syracuseStep 1761065 = 1320799) B1320799
theorem B1670959 : Blo 1172403 1670959 := bstep (se 1 (by rfl) ⟨1253219, by rfl⟩ : syracuseStep 1670959 = 2506439) B2506439
theorem B1761071 : Blo 1172403 1761071 := bstep (se 1 (by rfl) ⟨1320803, by rfl⟩ : syracuseStep 1761071 = 2641607) B2641607
theorem B4759357 : Blo 1172403 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B2638043 : Blo 1172403 2638043 := bstep (se 1 (by rfl) ⟨1978532, by rfl⟩ : syracuseStep 2638043 = 3957065) B3957065
theorem B1319143 : Blo 1172403 1319143 := bstep (se 1 (by rfl) ⟨989357, by rfl⟩ : syracuseStep 1319143 = 1978715) B1978715
theorem B1671455 : Blo 1172403 1671455 := bstep (se 1 (by rfl) ⟨1253591, by rfl⟩ : syracuseStep 1671455 = 2507183) B2507183
theorem B2638313 : Blo 1172403 2638313 := bstep (se 2 (by rfl) ⟨989367, by rfl⟩ : syracuseStep 2638313 = 1978735) B1978735
theorem B8454851 : Blo 1172403 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B2228971 : Blo 1172403 2228971 := bstep (se 1 (by rfl) ⟨1671728, by rfl⟩ : syracuseStep 2228971 = 3343457) B3343457
theorem B2638601 : Blo 1172403 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B15254315 : Blo 1172403 15254315 := bstep (se 1 (by rfl) ⟨11440736, by rfl⟩ : syracuseStep 15254315 = 22881473) B22881473
theorem B3957551 : Blo 1172403 3957551 := bstep (se 1 (by rfl) ⟨2968163, by rfl⟩ : syracuseStep 3957551 = 5936327) B5936327
theorem B1319791 : Blo 1172403 1319791 := bstep (se 1 (by rfl) ⟨989843, by rfl⟩ : syracuseStep 1319791 = 1979687) B1979687
theorem B3957659 : Blo 1172403 3957659 := bstep (se 1 (by rfl) ⟨2968244, by rfl⟩ : syracuseStep 3957659 = 5936489) B5936489
theorem B8455079 : Blo 1172403 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B32130037 : Blo 1172403 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B1172475 : Blo 1172403 1172475 := bstep (se 1 (by rfl) ⟨879356, by rfl⟩ : syracuseStep 1172475 = 1758713) B1758713
theorem B4457531 : Blo 1172403 4457531 := bstep (se 1 (by rfl) ⟨3343148, by rfl⟩ : syracuseStep 4457531 = 6686297) B6686297
theorem B1172543 : Blo 1172403 1172543 := bstep (se 1 (by rfl) ⟨879407, by rfl⟩ : syracuseStep 1172543 = 1758815) B1758815
theorem B6685841 : Blo 1172403 6685841 := bstep (se 2 (by rfl) ⟨2507190, by rfl⟩ : syracuseStep 6685841 = 5014381) B5014381
theorem B28959947 : Blo 1172403 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B1172687 : Blo 1172403 1172687 := bstep (se 1 (by rfl) ⟨879515, by rfl⟩ : syracuseStep 1172687 = 1759031) B1759031
theorem B2639177 : Blo 1172403 2639177 := bstep (se 2 (by rfl) ⟨989691, by rfl⟩ : syracuseStep 2639177 = 1979383) B1979383
theorem B13362569 : Blo 1172403 13362569 := bstep (se 2 (by rfl) ⟨5010963, by rfl⟩ : syracuseStep 13362569 = 10021927) B10021927
theorem B1172891 : Blo 1172403 1172891 := bstep (se 1 (by rfl) ⟨879668, by rfl⟩ : syracuseStep 1172891 = 1759337) B1759337
theorem B3343787 : Blo 1172403 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B1173103 : Blo 1172403 1173103 := bstep (se 1 (by rfl) ⟨879827, by rfl⟩ : syracuseStep 1173103 = 1759655) B1759655
theorem B1173159 : Blo 1172403 1173159 := bstep (se 1 (by rfl) ⟨879869, by rfl⟩ : syracuseStep 1173159 = 1759739) B1759739
theorem B1484507 : Blo 1172403 1484507 := bstep (se 1 (by rfl) ⟨1113380, by rfl⟩ : syracuseStep 1484507 = 2226761) B2226761
theorem B1173243 : Blo 1172403 1173243 := bstep (se 1 (by rfl) ⟨879932, by rfl⟩ : syracuseStep 1173243 = 1759865) B1759865
theorem B8464135 : Blo 1172403 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B1173279 : Blo 1172403 1173279 := bstep (se 1 (by rfl) ⟨879959, by rfl⟩ : syracuseStep 1173279 = 1759919) B1759919
theorem B1173311 : Blo 1172403 1173311 := bstep (se 1 (by rfl) ⟨879983, by rfl⟩ : syracuseStep 1173311 = 1759967) B1759967
theorem B3860303 : Blo 1172403 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B3762017 : Blo 1172403 3762017 := bstep (se 2 (by rfl) ⟨1410756, by rfl⟩ : syracuseStep 3762017 = 2821513) B2821513
theorem B3762119 : Blo 1172403 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B1173487 : Blo 1172403 1173487 := bstep (se 1 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 1173487 = 1760231) B1760231
theorem B1320943 : Blo 1172403 1320943 := bstep (se 1 (by rfl) ⟨990707, by rfl⟩ : syracuseStep 1320943 = 1981415) B1981415
theorem B3958793 : Blo 1172403 3958793 := bstep (se 2 (by rfl) ⟨1484547, by rfl⟩ : syracuseStep 3958793 = 2969095) B2969095
theorem B16058411 : Blo 1172403 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B1173659 : Blo 1172403 1173659 := bstep (se 1 (by rfl) ⟨880244, by rfl⟩ : syracuseStep 1173659 = 1760489) B1760489
theorem B1173695 : Blo 1172403 1173695 := bstep (se 1 (by rfl) ⟨880271, by rfl⟩ : syracuseStep 1173695 = 1760543) B1760543
theorem B164702423 : Blo 1172403 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B15239461 : Blo 1172403 15239461 := bstep (se 4 (by rfl) ⟨1428699, by rfl⟩ : syracuseStep 15239461 = 2857399) B2857399
theorem B2640167 : Blo 1172403 2640167 := bstep (se 1 (by rfl) ⟨1980125, by rfl⟩ : syracuseStep 2640167 = 3960251) B3960251
theorem B1173807 : Blo 1172403 1173807 := bstep (se 1 (by rfl) ⟨880355, by rfl⟩ : syracuseStep 1173807 = 1760711) B1760711
theorem B2640185 : Blo 1172403 2640185 := bstep (se 2 (by rfl) ⟨990069, by rfl⟩ : syracuseStep 2640185 = 1980139) B1980139
theorem B5794105 : Blo 1172403 5794105 := bstep (se 2 (by rfl) ⟨2172789, by rfl⟩ : syracuseStep 5794105 = 4345579) B4345579
theorem B1174043 : Blo 1172403 1174043 := bstep (se 1 (by rfl) ⟨880532, by rfl⟩ : syracuseStep 1174043 = 1761065) B1761065
theorem B1174047 : Blo 1172403 1174047 := bstep (se 1 (by rfl) ⟨880535, by rfl⟩ : syracuseStep 1174047 = 1761071) B1761071
theorem B365587121 : Blo 1172403 365587121 := bstep (se 2 (by rfl) ⟨137095170, by rfl⟩ : syracuseStep 365587121 = 274190341) B274190341
theorem B32107265 : Blo 1172403 32107265 := bstep (se 2 (by rfl) ⟨12040224, by rfl⟩ : syracuseStep 32107265 = 24080449) B24080449
theorem B1174363 : Blo 1172403 1174363 := bstep (se 1 (by rfl) ⟨880772, by rfl⟩ : syracuseStep 1174363 = 1761545) B1761545
theorem B4516843 : Blo 1172403 4516843 := bstep (se 1 (by rfl) ⟨3387632, by rfl⟩ : syracuseStep 4516843 = 6775265) B6775265
theorem B1485803 : Blo 1172403 1485803 := bstep (se 1 (by rfl) ⟨1114352, by rfl⟩ : syracuseStep 1485803 = 2228705) B2228705
theorem B16903187 : Blo 1172403 16903187 := bstep (se 1 (by rfl) ⟨12677390, by rfl⟩ : syracuseStep 16903187 = 25354781) B25354781
theorem B3960089 : Blo 1172403 3960089 := bstep (se 2 (by rfl) ⟨1485033, by rfl⟩ : syracuseStep 3960089 = 2970067) B2970067
theorem B3960143 : Blo 1172403 3960143 := bstep (se 1 (by rfl) ⟨2970107, by rfl⟩ : syracuseStep 3960143 = 5940215) B5940215
theorem B52178269 : Blo 1172403 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B4287853 : Blo 1172403 4287853 := bstep (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) B1607945
theorem B1879465 : Blo 1172403 1879465 := bstep (se 2 (by rfl) ⟨704799, by rfl⟩ : syracuseStep 1879465 = 1409599) B1409599
theorem B4230569 : Blo 1172403 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B3173879 : Blo 1172403 3173879 := bstep (se 1 (by rfl) ⟨2380409, by rfl⟩ : syracuseStep 3173879 = 4760819) B4760819
theorem B2641481 : Blo 1172403 2641481 := bstep (se 2 (by rfl) ⟨990555, by rfl⟩ : syracuseStep 2641481 = 1981111) B1981111
theorem B10030675 : Blo 1172403 10030675 := bstep (se 1 (by rfl) ⟨7523006, by rfl⟩ : syracuseStep 10030675 = 15046013) B15046013
theorem B7139279 : Blo 1172403 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B2969723 : Blo 1172403 2969723 := bstep (se 1 (by rfl) ⟨2227292, by rfl⟩ : syracuseStep 2969723 = 4454585) B4454585
theorem B5009597 : Blo 1172403 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B1978823 : Blo 1172403 1978823 := bstep (se 1 (by rfl) ⟨1484117, by rfl⟩ : syracuseStep 1978823 = 2968235) B2968235
theorem B3961439 : Blo 1172403 3961439 := bstep (se 1 (by rfl) ⟨2971079, by rfl⟩ : syracuseStep 3961439 = 5942159) B5942159
theorem B4453127 : Blo 1172403 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B7516961 : Blo 1172403 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B16044875 : Blo 1172403 16044875 := bstep (se 1 (by rfl) ⟨12033656, by rfl⟩ : syracuseStep 16044875 = 24067313) B24067313
theorem B4232255 : Blo 1172403 4232255 := bstep (se 1 (by rfl) ⟨3174191, by rfl⟩ : syracuseStep 4232255 = 6348383) B6348383
theorem B6345809 : Blo 1172403 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B1979599 : Blo 1172403 1979599 := bstep (se 1 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 1979599 = 2969399) B2969399
theorem B3765467 : Blo 1172403 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B3339539 : Blo 1172403 3339539 := bstep (se 1 (by rfl) ⟨2504654, by rfl⟩ : syracuseStep 3339539 = 5009309) B5009309
theorem B3757403 : Blo 1172403 3757403 := bstep (se 1 (by rfl) ⟨2818052, by rfl⟩ : syracuseStep 3757403 = 5636105) B5636105
theorem B1758791 : Blo 1172403 1758791 := bstep (se 1 (by rfl) ⟨1319093, by rfl⟩ : syracuseStep 1758791 = 2638187) B2638187
theorem B1758887 : Blo 1172403 1758887 := bstep (se 1 (by rfl) ⟨1319165, by rfl⟩ : syracuseStep 1758887 = 2638331) B2638331
theorem B1758971 : Blo 1172403 1758971 := bstep (se 1 (by rfl) ⟨1319228, by rfl⟩ : syracuseStep 1758971 = 2638457) B2638457
theorem B1759007 : Blo 1172403 1759007 := bstep (se 1 (by rfl) ⟨1319255, by rfl⟩ : syracuseStep 1759007 = 2638511) B2638511
theorem B3962681 : Blo 1172403 3962681 := bstep (se 2 (by rfl) ⟨1486005, by rfl⟩ : syracuseStep 3962681 = 2972011) B2972011
theorem B1759055 : Blo 1172403 1759055 := bstep (se 1 (by rfl) ⟨1319291, by rfl⟩ : syracuseStep 1759055 = 2638583) B2638583
theorem B8026051 : Blo 1172403 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B1759175 : Blo 1172403 1759175 := bstep (se 1 (by rfl) ⟨1319381, by rfl⟩ : syracuseStep 1759175 = 2638763) B2638763
theorem B3962843 : Blo 1172403 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B1980409 : Blo 1172403 1980409 := bstep (se 2 (by rfl) ⟨742653, by rfl⟩ : syracuseStep 1980409 = 1485307) B1485307
theorem B5634107 : Blo 1172403 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B3389537 : Blo 1172403 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B1980571 : Blo 1172403 1980571 := bstep (se 1 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 1980571 = 2970857) B2970857
theorem B13375691 : Blo 1172403 13375691 := bstep (se 1 (by rfl) ⟨10031768, by rfl⟩ : syracuseStep 13375691 = 20063537) B20063537
theorem B1784041 : Blo 1172403 1784041 := bstep (se 2 (by rfl) ⟨669015, by rfl⟩ : syracuseStep 1784041 = 1338031) B1338031
theorem B3963113 : Blo 1172403 3963113 := bstep (se 2 (by rfl) ⟨1486167, by rfl⟩ : syracuseStep 3963113 = 2972335) B2972335
theorem B1980679 : Blo 1172403 1980679 := bstep (se 1 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 1980679 = 2971019) B2971019
theorem B1759529 : Blo 1172403 1759529 := bstep (se 2 (by rfl) ⟨659823, by rfl⟩ : syracuseStep 1759529 = 1319647) B1319647
theorem B1980713 : Blo 1172403 1980713 := bstep (se 2 (by rfl) ⟨742767, by rfl⟩ : syracuseStep 1980713 = 1485535) B1485535
theorem B1759535 : Blo 1172403 1759535 := bstep (se 1 (by rfl) ⟨1319651, by rfl⟩ : syracuseStep 1759535 = 2639303) B2639303
theorem B1759775 : Blo 1172403 1759775 := bstep (se 1 (by rfl) ⟨1319831, by rfl⟩ : syracuseStep 1759775 = 2639663) B2639663
theorem B6773345 : Blo 1172403 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B5937785 : Blo 1172403 5937785 := bstep (se 2 (by rfl) ⟨2226669, by rfl⟩ : syracuseStep 5937785 = 4453339) B4453339
theorem B3963545 : Blo 1172403 3963545 := bstep (se 2 (by rfl) ⟨1486329, by rfl⟩ : syracuseStep 3963545 = 2972659) B2972659
theorem B12032669 : Blo 1172403 12032669 := bstep (se 3 (by rfl) ⟨2256125, by rfl⟩ : syracuseStep 12032669 = 4512251) B4512251
theorem B2227027 : Blo 1172403 2227027 := bstep (se 1 (by rfl) ⟨1670270, by rfl⟩ : syracuseStep 2227027 = 3340541) B3340541
theorem B1760159 : Blo 1172403 1760159 := bstep (se 1 (by rfl) ⟨1320119, by rfl⟩ : syracuseStep 1760159 = 2640239) B2640239
theorem B8911781 : Blo 1172403 8911781 := bstep (se 4 (by rfl) ⟨835479, by rfl⟩ : syracuseStep 8911781 = 1670959) B1670959
theorem B1760207 : Blo 1172403 1760207 := bstep (se 1 (by rfl) ⟨1320155, by rfl⟩ : syracuseStep 1760207 = 2640311) B2640311
theorem B16284637 : Blo 1172403 16284637 := bstep (se 3 (by rfl) ⟨3053369, by rfl⟩ : syracuseStep 16284637 = 6106739) B6106739
theorem B1760297 : Blo 1172403 1760297 := bstep (se 2 (by rfl) ⟨660111, by rfl⟩ : syracuseStep 1760297 = 1320223) B1320223
theorem B1760303 : Blo 1172403 1760303 := bstep (se 1 (by rfl) ⟨1320227, by rfl⟩ : syracuseStep 1760303 = 2640455) B2640455
theorem B1760327 : Blo 1172403 1760327 := bstep (se 1 (by rfl) ⟨1320245, by rfl⟩ : syracuseStep 1760327 = 2640491) B2640491
theorem B22551797 : Blo 1172403 22551797 := bstep (se 5 (by rfl) ⟨1057115, by rfl⟩ : syracuseStep 22551797 = 2114231) B2114231
theorem B1981705 : Blo 1172403 1981705 := bstep (se 2 (by rfl) ⟨743139, by rfl⟩ : syracuseStep 1981705 = 1486279) B1486279
theorem B5717287 : Blo 1172403 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B2112847 : Blo 1172403 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B1760591 : Blo 1172403 1760591 := bstep (se 1 (by rfl) ⟨1320443, by rfl⟩ : syracuseStep 1760591 = 2640887) B2640887
theorem B15039863 : Blo 1172403 15039863 := bstep (se 1 (by rfl) ⟨11279897, by rfl⟩ : syracuseStep 15039863 = 22559795) B22559795
theorem B1760681 : Blo 1172403 1760681 := bstep (se 2 (by rfl) ⟨660255, by rfl⟩ : syracuseStep 1760681 = 1320511) B1320511
theorem B2112979 : Blo 1172403 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B9649637 : Blo 1172403 9649637 := bstep (se 4 (by rfl) ⟨904653, by rfl⟩ : syracuseStep 9649637 = 1809307) B1809307
theorem B5012999 : Blo 1172403 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B1760831 : Blo 1172403 1760831 := bstep (se 1 (by rfl) ⟨1320623, by rfl⟩ : syracuseStep 1760831 = 2641247) B2641247
theorem B9510479 : Blo 1172403 9510479 := bstep (se 1 (by rfl) ⟨7132859, by rfl⟩ : syracuseStep 9510479 = 14265719) B14265719
theorem B1252955 : Blo 1172403 1252955 := bstep (se 1 (by rfl) ⟨939716, by rfl⟩ : syracuseStep 1252955 = 1879433) B1879433
theorem B5013083 : Blo 1172403 5013083 := bstep (se 1 (by rfl) ⟨3759812, by rfl⟩ : syracuseStep 5013083 = 7519625) B7519625
theorem B3759863 : Blo 1172403 3759863 := bstep (se 1 (by rfl) ⟨2819897, by rfl⟩ : syracuseStep 3759863 = 5639795) B5639795
theorem B1761095 : Blo 1172403 1761095 := bstep (se 1 (by rfl) ⟨1320821, by rfl⟩ : syracuseStep 1761095 = 2641643) B2641643
theorem B1761179 : Blo 1172403 1761179 := bstep (se 1 (by rfl) ⟨1320884, by rfl⟩ : syracuseStep 1761179 = 2641769) B2641769
theorem B1319215 : Blo 1172403 1319215 := bstep (se 1 (by rfl) ⟨989411, by rfl⟩ : syracuseStep 1319215 = 1978823) B1978823
theorem B7725473 : Blo 1172403 7725473 := bstep (se 2 (by rfl) ⟨2897052, by rfl⟩ : syracuseStep 7725473 = 5794105) B5794105
theorem B5636567 : Blo 1172403 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B2638367 : Blo 1172403 2638367 := bstep (se 1 (by rfl) ⟨1978775, by rfl⟩ : syracuseStep 2638367 = 3957551) B3957551
theorem B2638439 : Blo 1172403 2638439 := bstep (se 1 (by rfl) ⟨1978829, by rfl⟩ : syracuseStep 2638439 = 3957659) B3957659
theorem B5636719 : Blo 1172403 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B4457213 : Blo 1172403 4457213 := bstep (se 3 (by rfl) ⟨835727, by rfl⟩ : syracuseStep 4457213 = 1671455) B1671455
theorem B4457227 : Blo 1172403 4457227 := bstep (se 1 (by rfl) ⟨3342920, by rfl⟩ : syracuseStep 4457227 = 6685841) B6685841
theorem B2229191 : Blo 1172403 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B1172527 : Blo 1172403 1172527 := bstep (se 1 (by rfl) ⟨879395, by rfl⟩ : syracuseStep 1172527 = 1758791) B1758791
theorem B11281517 : Blo 1172403 11281517 := bstep (se 3 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 11281517 = 4230569) B4230569
theorem B1172591 : Blo 1172403 1172591 := bstep (se 1 (by rfl) ⟨879443, by rfl⟩ : syracuseStep 1172591 = 1758887) B1758887
theorem B1172647 : Blo 1172403 1172647 := bstep (se 1 (by rfl) ⟨879485, by rfl⟩ : syracuseStep 1172647 = 1758971) B1758971
theorem B1172671 : Blo 1172403 1172671 := bstep (se 1 (by rfl) ⟨879503, by rfl⟩ : syracuseStep 1172671 = 1759007) B1759007
theorem B1172703 : Blo 1172403 1172703 := bstep (se 1 (by rfl) ⟨879527, by rfl⟩ : syracuseStep 1172703 = 1759055) B1759055
theorem B2508011 : Blo 1172403 2508011 := bstep (se 1 (by rfl) ⟨1881008, by rfl⟩ : syracuseStep 2508011 = 3762017) B3762017
theorem B1172783 : Blo 1172403 1172783 := bstep (se 1 (by rfl) ⟨879587, by rfl⟩ : syracuseStep 1172783 = 1759175) B1759175
theorem B2508079 : Blo 1172403 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B6022457 : Blo 1172403 6022457 := bstep (se 2 (by rfl) ⟨2258421, by rfl⟩ : syracuseStep 6022457 = 4516843) B4516843
theorem B2639195 : Blo 1172403 2639195 := bstep (se 1 (by rfl) ⟨1979396, by rfl⟩ : syracuseStep 2639195 = 3958793) B3958793
theorem B1173019 : Blo 1172403 1173019 := bstep (se 1 (by rfl) ⟨879764, by rfl⟩ : syracuseStep 1173019 = 1759529) B1759529
theorem B1320475 : Blo 1172403 1320475 := bstep (se 1 (by rfl) ⟨990356, by rfl⟩ : syracuseStep 1320475 = 1980713) B1980713
theorem B1173023 : Blo 1172403 1173023 := bstep (se 1 (by rfl) ⟨879767, by rfl⟩ : syracuseStep 1173023 = 1759535) B1759535
theorem B30492197 : Blo 1172403 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B2639465 : Blo 1172403 2639465 := bstep (se 2 (by rfl) ⟨989799, by rfl⟩ : syracuseStep 2639465 = 1979599) B1979599
theorem B45074069 : Blo 1172403 45074069 := bstep (se 6 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 45074069 = 2112847) B2112847
theorem B1173183 : Blo 1172403 1173183 := bstep (se 1 (by rfl) ⟨879887, by rfl⟩ : syracuseStep 1173183 = 1759775) B1759775
theorem B4515563 : Blo 1172403 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B3958523 : Blo 1172403 3958523 := bstep (se 1 (by rfl) ⟨2968892, by rfl⟩ : syracuseStep 3958523 = 5937785) B5937785
theorem B3958685 : Blo 1172403 3958685 := bstep (se 3 (by rfl) ⟨742253, by rfl⟩ : syracuseStep 3958685 = 1484507) B1484507
theorem B1173439 : Blo 1172403 1173439 := bstep (se 1 (by rfl) ⟨880079, by rfl⟩ : syracuseStep 1173439 = 1760159) B1760159
theorem B5941187 : Blo 1172403 5941187 := bstep (se 1 (by rfl) ⟨4455890, by rfl⟩ : syracuseStep 5941187 = 8911781) B8911781
theorem B1173471 : Blo 1172403 1173471 := bstep (se 1 (by rfl) ⟨880103, by rfl⟩ : syracuseStep 1173471 = 1760207) B1760207
theorem B1173531 : Blo 1172403 1173531 := bstep (se 1 (by rfl) ⟨880148, by rfl⟩ : syracuseStep 1173531 = 1760297) B1760297
theorem B1173535 : Blo 1172403 1173535 := bstep (se 1 (by rfl) ⟨880151, by rfl⟩ : syracuseStep 1173535 = 1760303) B1760303
theorem B1173551 : Blo 1172403 1173551 := bstep (se 1 (by rfl) ⟨880163, by rfl⟩ : syracuseStep 1173551 = 1760327) B1760327
theorem B15034531 : Blo 1172403 15034531 := bstep (se 1 (by rfl) ⟨11275898, by rfl⟩ : syracuseStep 15034531 = 22551797) B22551797
theorem B2640059 : Blo 1172403 2640059 := bstep (se 1 (by rfl) ⟨1980044, by rfl⟩ : syracuseStep 2640059 = 3960089) B3960089
theorem B2640095 : Blo 1172403 2640095 := bstep (se 1 (by rfl) ⟨1980071, by rfl⟩ : syracuseStep 2640095 = 3960143) B3960143
theorem B1173727 : Blo 1172403 1173727 := bstep (se 1 (by rfl) ⟨880295, by rfl⟩ : syracuseStep 1173727 = 1760591) B1760591
theorem B1173787 : Blo 1172403 1173787 := bstep (se 1 (by rfl) ⟨880340, by rfl⟩ : syracuseStep 1173787 = 1760681) B1760681
theorem B6433091 : Blo 1172403 6433091 := bstep (se 1 (by rfl) ⟨4824818, by rfl⟩ : syracuseStep 6433091 = 9649637) B9649637
theorem B2115919 : Blo 1172403 2115919 := bstep (se 1 (by rfl) ⟨1586939, by rfl⟩ : syracuseStep 2115919 = 3173879) B3173879
theorem B1173887 : Blo 1172403 1173887 := bstep (se 1 (by rfl) ⟨880415, by rfl⟩ : syracuseStep 1173887 = 1760831) B1760831
theorem B1174063 : Blo 1172403 1174063 := bstep (se 1 (by rfl) ⟨880547, by rfl⟩ : syracuseStep 1174063 = 1761095) B1761095
theorem B10701401 : Blo 1172403 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B1174119 : Blo 1172403 1174119 := bstep (se 1 (by rfl) ⟨880589, by rfl⟩ : syracuseStep 1174119 = 1761179) B1761179
theorem B2640545 : Blo 1172403 2640545 := bstep (se 2 (by rfl) ⟨990204, by rfl⟩ : syracuseStep 2640545 = 1980409) B1980409
theorem B2640761 : Blo 1172403 2640761 := bstep (se 2 (by rfl) ⟨990285, by rfl⟩ : syracuseStep 2640761 = 1980571) B1980571
theorem B9038765 : Blo 1172403 9038765 := bstep (se 3 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 9038765 = 3389537) B3389537
theorem B2640905 : Blo 1172403 2640905 := bstep (se 2 (by rfl) ⟨990339, by rfl⟩ : syracuseStep 2640905 = 1980679) B1980679
theorem B20319281 : Blo 1172403 20319281 := bstep (se 2 (by rfl) ⟨7619730, by rfl⟩ : syracuseStep 20319281 = 15239461) B15239461
theorem B2640959 : Blo 1172403 2640959 := bstep (se 1 (by rfl) ⟨1980719, by rfl⟩ : syracuseStep 2640959 = 3961439) B3961439
theorem B2968751 : Blo 1172403 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B10169543 : Blo 1172403 10169543 := bstep (se 1 (by rfl) ⟨7627157, by rfl⟩ : syracuseStep 10169543 = 15254315) B15254315
theorem B4230539 : Blo 1172403 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B8908379 : Blo 1172403 8908379 := bstep (se 1 (by rfl) ⟨6681284, by rfl⟩ : syracuseStep 8908379 = 13362569) B13362569
theorem B2969369 : Blo 1172403 2969369 := bstep (se 2 (by rfl) ⟨1113513, by rfl⟩ : syracuseStep 2969369 = 2227027) B2227027
theorem B2641787 : Blo 1172403 2641787 := bstep (se 1 (by rfl) ⟨1981340, by rfl⟩ : syracuseStep 2641787 = 3962681) B3962681
theorem B2641895 : Blo 1172403 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B42840049 : Blo 1172403 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B3756071 : Blo 1172403 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B8917127 : Blo 1172403 8917127 := bstep (se 1 (by rfl) ⟨6687845, by rfl⟩ : syracuseStep 8917127 = 13375691) B13375691
theorem B109801615 : Blo 1172403 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B2642075 : Blo 1172403 2642075 := bstep (se 1 (by rfl) ⟨1981556, by rfl⟩ : syracuseStep 2642075 = 3963113) B3963113
theorem B2642273 : Blo 1172403 2642273 := bstep (se 2 (by rfl) ⟨990852, by rfl⟩ : syracuseStep 2642273 = 1981705) B1981705
theorem B2642363 : Blo 1172403 2642363 := bstep (se 1 (by rfl) ⟨1981772, by rfl⟩ : syracuseStep 2642363 = 3963545) B3963545
theorem B243724747 : Blo 1172403 243724747 := bstep (se 1 (by rfl) ⟨182793560, by rfl⟩ : syracuseStep 243724747 = 365587121) B365587121
theorem B69571025 : Blo 1172403 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B11268791 : Blo 1172403 11268791 := bstep (se 1 (by rfl) ⟨8451593, by rfl⟩ : syracuseStep 11268791 = 16903187) B16903187
theorem B13374233 : Blo 1172403 13374233 := bstep (se 2 (by rfl) ⟨5015337, by rfl⟩ : syracuseStep 13374233 = 10030675) B10030675
theorem B10294141 : Blo 1172403 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B11285513 : Blo 1172403 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B3962141 : Blo 1172403 3962141 := bstep (se 3 (by rfl) ⟨742901, by rfl⟩ : syracuseStep 3962141 = 1485803) B1485803
theorem B1979815 : Blo 1172403 1979815 := bstep (se 1 (by rfl) ⟨1484861, by rfl⟩ : syracuseStep 1979815 = 2969723) B2969723
theorem B3339731 : Blo 1172403 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B1758695 : Blo 1172403 1758695 := bstep (se 1 (by rfl) ⟨1319021, by rfl⟩ : syracuseStep 1758695 = 2638043) B2638043
theorem B11286013 : Blo 1172403 11286013 := bstep (se 3 (by rfl) ⟨2116127, by rfl⟩ : syracuseStep 11286013 = 4232255) B4232255
theorem B1758857 : Blo 1172403 1758857 := bstep (se 2 (by rfl) ⟨659571, by rfl⟩ : syracuseStep 1758857 = 1319143) B1319143
theorem B1758875 : Blo 1172403 1758875 := bstep (se 1 (by rfl) ⟨1319156, by rfl⟩ : syracuseStep 1758875 = 2638313) B2638313
theorem B1759067 : Blo 1172403 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B5011307 : Blo 1172403 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B10696583 : Blo 1172403 10696583 := bstep (se 1 (by rfl) ⟨8022437, by rfl⟩ : syracuseStep 10696583 = 16044875) B16044875
theorem B10041245 : Blo 1172403 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B2971687 : Blo 1172403 2971687 := bstep (se 1 (by rfl) ⟨2228765, by rfl⟩ : syracuseStep 2971687 = 4457531) B4457531
theorem B19306631 : Blo 1172403 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B2226359 : Blo 1172403 2226359 := bstep (se 1 (by rfl) ⟨1669769, by rfl⟩ : syracuseStep 2226359 = 3339539) B3339539
theorem B1759451 : Blo 1172403 1759451 := bstep (se 1 (by rfl) ⟨1319588, by rfl⟩ : syracuseStep 1759451 = 2639177) B2639177
theorem B2504935 : Blo 1172403 2504935 := bstep (se 1 (by rfl) ⟨1878701, by rfl⟩ : syracuseStep 2504935 = 3757403) B3757403
theorem B2971961 : Blo 1172403 2971961 := bstep (se 2 (by rfl) ⟨1114485, by rfl⟩ : syracuseStep 2971961 = 2228971) B2228971
theorem B1759721 : Blo 1172403 1759721 := bstep (se 2 (by rfl) ⟨659895, by rfl⟩ : syracuseStep 1759721 = 1319791) B1319791
theorem B10705607 : Blo 1172403 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B1760111 : Blo 1172403 1760111 := bstep (se 1 (by rfl) ⟨1320083, by rfl⟩ : syracuseStep 1760111 = 2640167) B2640167
theorem B1760123 : Blo 1172403 1760123 := bstep (se 1 (by rfl) ⟨1320092, by rfl⟩ : syracuseStep 1760123 = 2640185) B2640185
theorem B3341213 : Blo 1172403 3341213 := bstep (se 3 (by rfl) ⟨626477, by rfl⟩ : syracuseStep 3341213 = 1252955) B1252955
theorem B32087117 : Blo 1172403 32087117 := bstep (se 3 (by rfl) ⟨6016334, by rfl⟩ : syracuseStep 32087117 = 12032669) B12032669
theorem B5717137 : Blo 1172403 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B21404843 : Blo 1172403 21404843 := bstep (se 1 (by rfl) ⟨16053632, by rfl⟩ : syracuseStep 21404843 = 32107265) B32107265
theorem B2505953 : Blo 1172403 2505953 := bstep (se 2 (by rfl) ⟨939732, by rfl⟩ : syracuseStep 2505953 = 1879465) B1879465
theorem B2817305 : Blo 1172403 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B10026301 : Blo 1172403 10026301 := bstep (se 3 (by rfl) ⟨1879931, by rfl⟩ : syracuseStep 10026301 = 3759863) B3759863
theorem B38059541 : Blo 1172403 38059541 := bstep (se 6 (by rfl) ⟨892020, by rfl⟩ : syracuseStep 38059541 = 1784041) B1784041
theorem B10026575 : Blo 1172403 10026575 := bstep (se 1 (by rfl) ⟨7519931, by rfl⟩ : syracuseStep 10026575 = 15039863) B15039863
theorem B3341999 : Blo 1172403 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B1760987 : Blo 1172403 1760987 := bstep (se 1 (by rfl) ⟨1320740, by rfl⟩ : syracuseStep 1760987 = 2641481) B2641481
theorem B6340319 : Blo 1172403 6340319 := bstep (se 1 (by rfl) ⟨4755239, by rfl⟩ : syracuseStep 6340319 = 9510479) B9510479
theorem B3342055 : Blo 1172403 3342055 := bstep (se 1 (by rfl) ⟨2506541, by rfl⟩ : syracuseStep 3342055 = 5013083) B5013083
theorem B86851397 : Blo 1172403 86851397 := bstep (se 4 (by rfl) ⟨8142318, by rfl⟩ : syracuseStep 86851397 = 16284637) B16284637
theorem B19038077 : Blo 1172403 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B1761257 : Blo 1172403 1761257 := bstep (se 2 (by rfl) ⟨660471, by rfl⟩ : syracuseStep 1761257 = 1320943) B1320943
theorem B1761383 : Blo 1172403 1761383 := bstep (se 1 (by rfl) ⟨1321037, by rfl⟩ : syracuseStep 1761383 = 2642075) B2642075
theorem B85565645 : Blo 1172403 85565645 := bstep (se 3 (by rfl) ⟨16043558, by rfl⟩ : syracuseStep 85565645 = 32087117) B32087117
theorem B20046041 : Blo 1172403 20046041 := bstep (se 2 (by rfl) ⟨7517265, by rfl⟩ : syracuseStep 20046041 = 15034531) B15034531
theorem B1761515 : Blo 1172403 1761515 := bstep (se 1 (by rfl) ⟨1321136, by rfl⟩ : syracuseStep 1761515 = 2642273) B2642273
theorem B1761575 : Blo 1172403 1761575 := bstep (se 1 (by rfl) ⟨1321181, by rfl⟩ : syracuseStep 1761575 = 2642363) B2642363
theorem B7512527 : Blo 1172403 7512527 := bstep (se 1 (by rfl) ⟨5634395, by rfl⟩ : syracuseStep 7512527 = 11268791) B11268791
theorem B7521011 : Blo 1172403 7521011 := bstep (se 1 (by rfl) ⟨5640758, by rfl⟩ : syracuseStep 7521011 = 11281517) B11281517
theorem B1672007 : Blo 1172403 1672007 := bstep (se 1 (by rfl) ⟨1254005, by rfl⟩ : syracuseStep 1672007 = 2508011) B2508011
theorem B4014971 : Blo 1172403 4014971 := bstep (se 1 (by rfl) ⟨3011228, by rfl⟩ : syracuseStep 4014971 = 6022457) B6022457
theorem B1172463 : Blo 1172403 1172463 := bstep (se 1 (by rfl) ⟨879347, by rfl⟩ : syracuseStep 1172463 = 1758695) B1758695
theorem B1172571 : Blo 1172403 1172571 := bstep (se 1 (by rfl) ⟨879428, by rfl⟩ : syracuseStep 1172571 = 1758857) B1758857
theorem B30049379 : Blo 1172403 30049379 := bstep (se 1 (by rfl) ⟨22537034, by rfl⟩ : syracuseStep 30049379 = 45074069) B45074069
theorem B1172583 : Blo 1172403 1172583 := bstep (se 1 (by rfl) ⟨879437, by rfl⟩ : syracuseStep 1172583 = 1758875) B1758875
theorem B2639015 : Blo 1172403 2639015 := bstep (se 1 (by rfl) ⟨1979261, by rfl⟩ : syracuseStep 2639015 = 3958523) B3958523
theorem B8905949 : Blo 1172403 8905949 := bstep (se 3 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 8905949 = 3339731) B3339731
theorem B1172711 : Blo 1172403 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B6694163 : Blo 1172403 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B2639123 : Blo 1172403 2639123 := bstep (se 1 (by rfl) ⟨1979342, by rfl⟩ : syracuseStep 2639123 = 3958685) B3958685
theorem B1484239 : Blo 1172403 1484239 := bstep (se 1 (by rfl) ⟨1113179, by rfl⟩ : syracuseStep 1484239 = 2226359) B2226359
theorem B1172967 : Blo 1172403 1172967 := bstep (se 1 (by rfl) ⟨879725, by rfl⟩ : syracuseStep 1172967 = 1759451) B1759451
theorem B1173147 : Blo 1172403 1173147 := bstep (se 1 (by rfl) ⟨879860, by rfl⟩ : syracuseStep 1173147 = 1759721) B1759721
theorem B3344105 : Blo 1172403 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B7137071 : Blo 1172403 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B2639753 : Blo 1172403 2639753 := bstep (se 2 (by rfl) ⟨989907, by rfl⟩ : syracuseStep 2639753 = 1979815) B1979815
theorem B1173407 : Blo 1172403 1173407 := bstep (se 1 (by rfl) ⟨880055, by rfl⟩ : syracuseStep 1173407 = 1760111) B1760111
theorem B1173415 : Blo 1172403 1173415 := bstep (se 1 (by rfl) ⟨880061, by rfl⟩ : syracuseStep 1173415 = 1760123) B1760123
theorem B1878203 : Blo 1172403 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B2820359 : Blo 1172403 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B25373027 : Blo 1172403 25373027 := bstep (se 1 (by rfl) ⟨19029770, by rfl⟩ : syracuseStep 25373027 = 38059541) B38059541
theorem B1173991 : Blo 1172403 1173991 := bstep (se 1 (by rfl) ⟨880493, by rfl⟩ : syracuseStep 1173991 = 1760987) B1760987
theorem B12692051 : Blo 1172403 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B1174171 : Blo 1172403 1174171 := bstep (se 1 (by rfl) ⟨880628, by rfl⟩ : syracuseStep 1174171 = 1761257) B1761257
theorem B146402153 : Blo 1172403 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B2821225 : Blo 1172403 2821225 := bstep (se 2 (by rfl) ⟨1057959, by rfl⟩ : syracuseStep 2821225 = 2115919) B2115919
theorem B8916155 : Blo 1172403 8916155 := bstep (se 1 (by rfl) ⟨6687116, by rfl⟩ : syracuseStep 8916155 = 13374233) B13374233
theorem B1486127 : Blo 1172403 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B7523675 : Blo 1172403 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B2641427 : Blo 1172403 2641427 := bstep (se 1 (by rfl) ⟨1981070, by rfl⟩ : syracuseStep 2641427 = 3962141) B3962141
theorem B5942969 : Blo 1172403 5942969 := bstep (se 2 (by rfl) ⟨2228613, by rfl⟩ : syracuseStep 5942969 = 4457227) B4457227
theorem B20328131 : Blo 1172403 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B3010375 : Blo 1172403 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B13725521 : Blo 1172403 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B3960791 : Blo 1172403 3960791 := bstep (se 1 (by rfl) ⟨2970593, by rfl⟩ : syracuseStep 3960791 = 5941187) B5941187
theorem B7622849 : Blo 1172403 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B4288727 : Blo 1172403 4288727 := bstep (se 1 (by rfl) ⟨3216545, by rfl⟩ : syracuseStep 4288727 = 6433091) B6433091
theorem B28537069 : Blo 1172403 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B6025843 : Blo 1172403 6025843 := bstep (se 1 (by rfl) ⟨4519382, by rfl⟩ : syracuseStep 6025843 = 9038765) B9038765
theorem B13546187 : Blo 1172403 13546187 := bstep (se 1 (by rfl) ⟨10159640, by rfl⟩ : syracuseStep 13546187 = 20319281) B20319281
theorem B1979167 : Blo 1172403 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B6779695 : Blo 1172403 6779695 := bstep (se 1 (by rfl) ⟨5084771, by rfl⟩ : syracuseStep 6779695 = 10169543) B10169543
theorem B1979579 : Blo 1172403 1979579 := bstep (se 1 (by rfl) ⟨1484684, by rfl⟩ : syracuseStep 1979579 = 2969369) B2969369
theorem B57120065 : Blo 1172403 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B2504047 : Blo 1172403 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B3962249 : Blo 1172403 3962249 := bstep (se 2 (by rfl) ⟨1485843, by rfl⟩ : syracuseStep 3962249 = 2971687) B2971687
theorem B5944751 : Blo 1172403 5944751 := bstep (se 1 (by rfl) ⟨4458563, by rfl⟩ : syracuseStep 5944751 = 8917127) B8917127
theorem B5150315 : Blo 1172403 5150315 := bstep (se 1 (by rfl) ⟨3862736, by rfl⟩ : syracuseStep 5150315 = 7725473) B7725473
theorem B46380683 : Blo 1172403 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B3757711 : Blo 1172403 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B51484349 : Blo 1172403 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B1758911 : Blo 1172403 1758911 := bstep (se 1 (by rfl) ⟨1319183, by rfl⟩ : syracuseStep 1758911 = 2638367) B2638367
theorem B1758953 : Blo 1172403 1758953 := bstep (se 2 (by rfl) ⟨659607, by rfl⟩ : syracuseStep 1758953 = 1319215) B1319215
theorem B1758959 : Blo 1172403 1758959 := bstep (se 1 (by rfl) ⟨1319219, by rfl⟩ : syracuseStep 1758959 = 2638439) B2638439
theorem B2971475 : Blo 1172403 2971475 := bstep (se 1 (by rfl) ⟨2228606, by rfl⟩ : syracuseStep 2971475 = 4457213) B4457213
theorem B30062501 : Blo 1172403 30062501 := bstep (se 4 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 30062501 = 5636719) B5636719
theorem B324966329 : Blo 1172403 324966329 := bstep (se 2 (by rfl) ⟨121862373, by rfl⟩ : syracuseStep 324966329 = 243724747) B243724747
theorem B1759463 : Blo 1172403 1759463 := bstep (se 1 (by rfl) ⟨1319597, by rfl⟩ : syracuseStep 1759463 = 2639195) B2639195
theorem B1759643 : Blo 1172403 1759643 := bstep (se 1 (by rfl) ⟨1319732, by rfl⟩ : syracuseStep 1759643 = 2639465) B2639465
theorem B13359653 : Blo 1172403 13359653 := bstep (se 4 (by rfl) ⟨1252467, by rfl⟩ : syracuseStep 13359653 = 2504935) B2504935
theorem B3340871 : Blo 1172403 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B1760039 : Blo 1172403 1760039 := bstep (se 1 (by rfl) ⟨1320029, by rfl⟩ : syracuseStep 1760039 = 2640059) B2640059
theorem B1760063 : Blo 1172403 1760063 := bstep (se 1 (by rfl) ⟨1320047, by rfl⟩ : syracuseStep 1760063 = 2640095) B2640095
theorem B1981307 : Blo 1172403 1981307 := bstep (se 1 (by rfl) ⟨1485980, by rfl⟩ : syracuseStep 1981307 = 2971961) B2971961
theorem B13368401 : Blo 1172403 13368401 := bstep (se 2 (by rfl) ⟨5013150, by rfl⟩ : syracuseStep 13368401 = 10026301) B10026301
theorem B1760363 : Blo 1172403 1760363 := bstep (se 1 (by rfl) ⟨1320272, by rfl⟩ : syracuseStep 1760363 = 2640545) B2640545
theorem B1760507 : Blo 1172403 1760507 := bstep (se 1 (by rfl) ⟨1320380, by rfl⟩ : syracuseStep 1760507 = 2640761) B2640761
theorem B2227475 : Blo 1172403 2227475 := bstep (se 1 (by rfl) ⟨1670606, by rfl⟩ : syracuseStep 2227475 = 3341213) B3341213
theorem B15048017 : Blo 1172403 15048017 := bstep (se 2 (by rfl) ⟨5643006, by rfl⟩ : syracuseStep 15048017 = 11286013) B11286013
theorem B1760603 : Blo 1172403 1760603 := bstep (se 1 (by rfl) ⟨1320452, by rfl⟩ : syracuseStep 1760603 = 2640905) B2640905
theorem B1760633 : Blo 1172403 1760633 := bstep (se 2 (by rfl) ⟨660237, by rfl⟩ : syracuseStep 1760633 = 1320475) B1320475
theorem B1760639 : Blo 1172403 1760639 := bstep (se 1 (by rfl) ⟨1320479, by rfl⟩ : syracuseStep 1760639 = 2640959) B2640959
theorem B14269895 : Blo 1172403 14269895 := bstep (se 1 (by rfl) ⟨10702421, by rfl⟩ : syracuseStep 14269895 = 21404843) B21404843
theorem B1670635 : Blo 1172403 1670635 := bstep (se 1 (by rfl) ⟨1252976, by rfl⟩ : syracuseStep 1670635 = 2505953) B2505953
theorem B231603725 : Blo 1172403 231603725 := bstep (se 3 (by rfl) ⟨43425698, by rfl⟩ : syracuseStep 231603725 = 86851397) B86851397
theorem B4456073 : Blo 1172403 4456073 := bstep (se 2 (by rfl) ⟨1671027, by rfl⟩ : syracuseStep 4456073 = 3342055) B3342055
theorem B28524221 : Blo 1172403 28524221 := bstep (se 3 (by rfl) ⟨5348291, by rfl⟩ : syracuseStep 28524221 = 10696583) B10696583
theorem B6684383 : Blo 1172403 6684383 := bstep (se 1 (by rfl) ⟨5013287, by rfl⟩ : syracuseStep 6684383 = 10026575) B10026575
theorem B5938919 : Blo 1172403 5938919 := bstep (se 1 (by rfl) ⟨4454189, by rfl⟩ : syracuseStep 5938919 = 8908379) B8908379
theorem B2227999 : Blo 1172403 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B4226879 : Blo 1172403 4226879 := bstep (se 1 (by rfl) ⟨3170159, by rfl⟩ : syracuseStep 4226879 = 6340319) B6340319
theorem B1761191 : Blo 1172403 1761191 := bstep (se 1 (by rfl) ⟨1320893, by rfl⟩ : syracuseStep 1761191 = 2641787) B2641787
theorem B1761263 : Blo 1172403 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B2859151 : Blo 1172403 2859151 := bstep (se 1 (by rfl) ⟨2144363, by rfl⟩ : syracuseStep 2859151 = 4288727) B4288727
theorem B5014007 : Blo 1172403 5014007 := bstep (se 1 (by rfl) ⟨3760505, by rfl⟩ : syracuseStep 5014007 = 7521011) B7521011
theorem B32137829 : Blo 1172403 32137829 := bstep (se 4 (by rfl) ⟨3012921, by rfl⟩ : syracuseStep 32137829 = 6025843) B6025843
theorem B7520957 : Blo 1172403 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B1319719 : Blo 1172403 1319719 := bstep (se 1 (by rfl) ⟨989789, by rfl⟩ : syracuseStep 1319719 = 1979579) B1979579
theorem B2638889 : Blo 1172403 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B1172607 : Blo 1172403 1172607 := bstep (se 1 (by rfl) ⟨879455, by rfl⟩ : syracuseStep 1172607 = 1758911) B1758911
theorem B1172635 : Blo 1172403 1172635 := bstep (se 1 (by rfl) ⟨879476, by rfl⟩ : syracuseStep 1172635 = 1758953) B1758953
theorem B1172639 : Blo 1172403 1172639 := bstep (se 1 (by rfl) ⟨879479, by rfl⟩ : syracuseStep 1172639 = 1758959) B1758959
theorem B3761633 : Blo 1172403 3761633 := bstep (se 2 (by rfl) ⟨1410612, by rfl⟩ : syracuseStep 3761633 = 2821225) B2821225
theorem B1172975 : Blo 1172403 1172975 := bstep (se 1 (by rfl) ⟨879731, by rfl⟩ : syracuseStep 1172975 = 1759463) B1759463
theorem B1173095 : Blo 1172403 1173095 := bstep (se 1 (by rfl) ⟨879821, by rfl⟩ : syracuseStep 1173095 = 1759643) B1759643
theorem B8906435 : Blo 1172403 8906435 := bstep (se 1 (by rfl) ⟨6679826, by rfl⟩ : syracuseStep 8906435 = 13359653) B13359653
theorem B54208349 : Blo 1172403 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B1173359 : Blo 1172403 1173359 := bstep (se 1 (by rfl) ⟨880019, by rfl⟩ : syracuseStep 1173359 = 1760039) B1760039
theorem B1173375 : Blo 1172403 1173375 := bstep (se 1 (by rfl) ⟨880031, by rfl⟩ : syracuseStep 1173375 = 1760063) B1760063
theorem B97601435 : Blo 1172403 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B1320871 : Blo 1172403 1320871 := bstep (se 1 (by rfl) ⟨990653, by rfl⟩ : syracuseStep 1320871 = 1981307) B1981307
theorem B1173575 : Blo 1172403 1173575 := bstep (se 1 (by rfl) ⟨880181, by rfl⟩ : syracuseStep 1173575 = 1760363) B1760363
theorem B1173671 : Blo 1172403 1173671 := bstep (se 1 (by rfl) ⟨880253, by rfl⟩ : syracuseStep 1173671 = 1760507) B1760507
theorem B1484983 : Blo 1172403 1484983 := bstep (se 1 (by rfl) ⟨1113737, by rfl⟩ : syracuseStep 1484983 = 2227475) B2227475
theorem B4458685 : Blo 1172403 4458685 := bstep (se 3 (by rfl) ⟨836003, by rfl⟩ : syracuseStep 4458685 = 1672007) B1672007
theorem B1173735 : Blo 1172403 1173735 := bstep (se 1 (by rfl) ⟨880301, by rfl⟩ : syracuseStep 1173735 = 1760603) B1760603
theorem B5015783 : Blo 1172403 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B1173755 : Blo 1172403 1173755 := bstep (se 1 (by rfl) ⟨880316, by rfl⟩ : syracuseStep 1173755 = 1760633) B1760633
theorem B1173759 : Blo 1172403 1173759 := bstep (se 1 (by rfl) ⟨880319, by rfl⟩ : syracuseStep 1173759 = 1760639) B1760639
theorem B9513263 : Blo 1172403 9513263 := bstep (se 1 (by rfl) ⟨7134947, by rfl⟩ : syracuseStep 9513263 = 14269895) B14269895
theorem B19016147 : Blo 1172403 19016147 := bstep (se 1 (by rfl) ⟨14262110, by rfl⟩ : syracuseStep 19016147 = 28524221) B28524221
theorem B3959279 : Blo 1172403 3959279 := bstep (se 1 (by rfl) ⟨2969459, by rfl⟩ : syracuseStep 3959279 = 5938919) B5938919
theorem B1174127 : Blo 1172403 1174127 := bstep (se 1 (by rfl) ⟨880595, by rfl⟩ : syracuseStep 1174127 = 1761191) B1761191
theorem B2640527 : Blo 1172403 2640527 := bstep (se 1 (by rfl) ⟨1980395, by rfl⟩ : syracuseStep 2640527 = 3960791) B3960791
theorem B1174175 : Blo 1172403 1174175 := bstep (se 1 (by rfl) ⟨880631, by rfl⟩ : syracuseStep 1174175 = 1761263) B1761263
theorem B1174255 : Blo 1172403 1174255 := bstep (se 1 (by rfl) ⟨880691, by rfl⟩ : syracuseStep 1174255 = 1761383) B1761383
theorem B57043763 : Blo 1172403 57043763 := bstep (se 1 (by rfl) ⟨42782822, by rfl⟩ : syracuseStep 57043763 = 85565645) B85565645
theorem B13364027 : Blo 1172403 13364027 := bstep (se 1 (by rfl) ⟨10023020, by rfl⟩ : syracuseStep 13364027 = 20046041) B20046041
theorem B1174343 : Blo 1172403 1174343 := bstep (se 1 (by rfl) ⟨880757, by rfl⟩ : syracuseStep 1174343 = 1761515) B1761515
theorem B1174383 : Blo 1172403 1174383 := bstep (se 1 (by rfl) ⟨880787, by rfl⟩ : syracuseStep 1174383 = 1761575) B1761575
theorem B5008351 : Blo 1172403 5008351 := bstep (se 1 (by rfl) ⟨3756263, by rfl⟩ : syracuseStep 5008351 = 7512527) B7512527
theorem B9030791 : Blo 1172403 9030791 := bstep (se 1 (by rfl) ⟨6773093, by rfl⟩ : syracuseStep 9030791 = 13546187) B13546187
theorem B20327597 : Blo 1172403 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B20032919 : Blo 1172403 20032919 := bstep (se 1 (by rfl) ⟨15024689, by rfl⟩ : syracuseStep 20032919 = 30049379) B30049379
theorem B38080043 : Blo 1172403 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B2641499 : Blo 1172403 2641499 := bstep (se 1 (by rfl) ⟨1981124, by rfl⟩ : syracuseStep 2641499 = 3962249) B3962249
theorem B9039593 : Blo 1172403 9039593 := bstep (se 2 (by rfl) ⟨3389847, by rfl⟩ : syracuseStep 9039593 = 6779695) B6779695
theorem B20041667 : Blo 1172403 20041667 := bstep (se 1 (by rfl) ⟨15031250, by rfl⟩ : syracuseStep 20041667 = 30062501) B30062501
theorem B13734173 : Blo 1172403 13734173 := bstep (se 3 (by rfl) ⟨2575157, by rfl⟩ : syracuseStep 13734173 = 5150315) B5150315
theorem B3338729 : Blo 1172403 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B1978985 : Blo 1172403 1978985 := bstep (se 2 (by rfl) ⟨742119, by rfl⟩ : syracuseStep 1978985 = 1484239) B1484239
theorem B8917613 : Blo 1172403 8917613 := bstep (se 3 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 8917613 = 3344105) B3344105
theorem B5944103 : Blo 1172403 5944103 := bstep (se 1 (by rfl) ⟨4458077, by rfl⟩ : syracuseStep 5944103 = 8916155) B8916155
theorem B5010281 : Blo 1172403 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B10032011 : Blo 1172403 10032011 := bstep (se 1 (by rfl) ⟨7524008, by rfl⟩ : syracuseStep 10032011 = 15048017) B15048017
theorem B2970665 : Blo 1172403 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B2970715 : Blo 1172403 2970715 := bstep (se 1 (by rfl) ⟨2228036, by rfl⟩ : syracuseStep 2970715 = 4456073) B4456073
theorem B3961979 : Blo 1172403 3961979 := bstep (se 1 (by rfl) ⟨2971484, by rfl⟩ : syracuseStep 3961979 = 5942969) B5942969
theorem B38049425 : Blo 1172403 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B2676647 : Blo 1172403 2676647 := bstep (se 1 (by rfl) ⟨2007485, by rfl⟩ : syracuseStep 2676647 = 4014971) B4014971
theorem B1759343 : Blo 1172403 1759343 := bstep (se 1 (by rfl) ⟨1319507, by rfl⟩ : syracuseStep 1759343 = 2639015) B2639015
theorem B3963005 : Blo 1172403 3963005 := bstep (se 3 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 3963005 = 1486127) B1486127
theorem B5937299 : Blo 1172403 5937299 := bstep (se 1 (by rfl) ⟨4452974, by rfl⟩ : syracuseStep 5937299 = 8905949) B8905949
theorem B4462775 : Blo 1172403 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B1759415 : Blo 1172403 1759415 := bstep (se 1 (by rfl) ⟨1319561, by rfl⟩ : syracuseStep 1759415 = 2639123) B2639123
theorem B3963167 : Blo 1172403 3963167 := bstep (se 1 (by rfl) ⟨2972375, by rfl⟩ : syracuseStep 3963167 = 5944751) B5944751
theorem B34322899 : Blo 1172403 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B4758047 : Blo 1172403 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B1980983 : Blo 1172403 1980983 := bstep (se 1 (by rfl) ⟨1485737, by rfl⟩ : syracuseStep 1980983 = 2971475) B2971475
theorem B1759835 : Blo 1172403 1759835 := bstep (se 1 (by rfl) ⟨1319876, by rfl⟩ : syracuseStep 1759835 = 2639753) B2639753
theorem B216644219 : Blo 1172403 216644219 := bstep (se 1 (by rfl) ⟨162483164, by rfl⟩ : syracuseStep 216644219 = 324966329) B324966329
theorem B1252135 : Blo 1172403 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B16915351 : Blo 1172403 16915351 := bstep (se 1 (by rfl) ⟨12686513, by rfl⟩ : syracuseStep 16915351 = 25373027) B25373027
theorem B123681821 : Blo 1172403 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B16055333 : Blo 1172403 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B2227247 : Blo 1172403 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B8461367 : Blo 1172403 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B2227513 : Blo 1172403 2227513 := bstep (se 2 (by rfl) ⟨835317, by rfl⟩ : syracuseStep 2227513 = 1670635) B1670635
theorem B8912267 : Blo 1172403 8912267 := bstep (se 1 (by rfl) ⟨6684200, by rfl⟩ : syracuseStep 8912267 = 13368401) B13368401
theorem B154402483 : Blo 1172403 154402483 := bstep (se 1 (by rfl) ⟨115801862, by rfl⟩ : syracuseStep 154402483 = 231603725) B231603725
theorem B1760951 : Blo 1172403 1760951 := bstep (se 1 (by rfl) ⟨1320713, by rfl⟩ : syracuseStep 1760951 = 2641427) B2641427
theorem B4456255 : Blo 1172403 4456255 := bstep (se 1 (by rfl) ⟨3342191, by rfl⟩ : syracuseStep 4456255 = 6684383) B6684383
theorem B2817919 : Blo 1172403 2817919 := bstep (se 1 (by rfl) ⟨2113439, by rfl⟩ : syracuseStep 2817919 = 4226879) B4226879
theorem B9150347 : Blo 1172403 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B329818189 : Blo 1172403 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B3342671 : Blo 1172403 3342671 := bstep (se 1 (by rfl) ⟨2507003, by rfl⟩ : syracuseStep 3342671 = 5014007) B5014007
theorem B1319323 : Blo 1172403 1319323 := bstep (se 1 (by rfl) ⟨989492, by rfl⟩ : syracuseStep 1319323 = 1978985) B1978985
theorem B5013971 : Blo 1172403 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B2507755 : Blo 1172403 2507755 := bstep (se 1 (by rfl) ⟨1880816, by rfl⟩ : syracuseStep 2507755 = 3761633) B3761633
theorem B22553801 : Blo 1172403 22553801 := bstep (se 2 (by rfl) ⟨8457675, by rfl⟩ : syracuseStep 22553801 = 16915351) B16915351
theorem B6677801 : Blo 1172403 6677801 := bstep (se 2 (by rfl) ⟨2504175, by rfl⟩ : syracuseStep 6677801 = 5008351) B5008351
theorem B1172895 : Blo 1172403 1172895 := bstep (se 1 (by rfl) ⟨879671, by rfl⟩ : syracuseStep 1172895 = 1759343) B1759343
theorem B3958199 : Blo 1172403 3958199 := bstep (se 1 (by rfl) ⟨2968649, by rfl⟩ : syracuseStep 3958199 = 5937299) B5937299
theorem B2975183 : Blo 1172403 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B1172943 : Blo 1172403 1172943 := bstep (se 1 (by rfl) ⟨879707, by rfl⟩ : syracuseStep 1172943 = 1759415) B1759415
theorem B3343855 : Blo 1172403 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B6342175 : Blo 1172403 6342175 := bstep (se 1 (by rfl) ⟨4756631, by rfl⟩ : syracuseStep 6342175 = 9513263) B9513263
theorem B2639519 : Blo 1172403 2639519 := bstep (se 1 (by rfl) ⟨1979639, by rfl⟩ : syracuseStep 2639519 = 3959279) B3959279
theorem B3172031 : Blo 1172403 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B1320655 : Blo 1172403 1320655 := bstep (se 1 (by rfl) ⟨990491, by rfl⟩ : syracuseStep 1320655 = 1980983) B1980983
theorem B1173223 : Blo 1172403 1173223 := bstep (se 1 (by rfl) ⟨879917, by rfl⟩ : syracuseStep 1173223 = 1759835) B1759835
theorem B38029175 : Blo 1172403 38029175 := bstep (se 1 (by rfl) ⟨28521881, by rfl⟩ : syracuseStep 38029175 = 57043763) B57043763
theorem B1484831 : Blo 1172403 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B13551731 : Blo 1172403 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B5941511 : Blo 1172403 5941511 := bstep (se 1 (by rfl) ⟨4456133, by rfl⟩ : syracuseStep 5941511 = 8912267) B8912267
theorem B13355279 : Blo 1172403 13355279 := bstep (se 1 (by rfl) ⟨10016459, by rfl⟩ : syracuseStep 13355279 = 20032919) B20032919
theorem B5941673 : Blo 1172403 5941673 := bstep (se 2 (by rfl) ⟨2228127, by rfl⟩ : syracuseStep 5941673 = 4456255) B4456255
theorem B1173967 : Blo 1172403 1173967 := bstep (se 1 (by rfl) ⟨880475, by rfl⟩ : syracuseStep 1173967 = 1760951) B1760951
theorem B3812201 : Blo 1172403 3812201 := bstep (se 2 (by rfl) ⟨1429575, by rfl⟩ : syracuseStep 3812201 = 2859151) B2859151
theorem B21425219 : Blo 1172403 21425219 := bstep (se 1 (by rfl) ⟨16068914, by rfl⟩ : syracuseStep 21425219 = 32137829) B32137829
theorem B6688007 : Blo 1172403 6688007 := bstep (se 1 (by rfl) ⟨5016005, by rfl⟩ : syracuseStep 6688007 = 10032011) B10032011
theorem B45763865 : Blo 1172403 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B2641319 : Blo 1172403 2641319 := bstep (se 1 (by rfl) ⟨1980989, by rfl⟩ : syracuseStep 2641319 = 3961979) B3961979
theorem B25366283 : Blo 1172403 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B36138899 : Blo 1172403 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B2642003 : Blo 1172403 2642003 := bstep (se 1 (by rfl) ⟨1981502, by rfl⟩ : syracuseStep 2642003 = 3963005) B3963005
theorem B3960953 : Blo 1172403 3960953 := bstep (se 2 (by rfl) ⟨1485357, by rfl⟩ : syracuseStep 3960953 = 2970715) B2970715
theorem B2642111 : Blo 1172403 2642111 := bstep (se 1 (by rfl) ⟨1981583, by rfl⟩ : syracuseStep 2642111 = 3963167) B3963167
theorem B12677431 : Blo 1172403 12677431 := bstep (se 1 (by rfl) ⟨9508073, by rfl⟩ : syracuseStep 12677431 = 19016147) B19016147
theorem B2970017 : Blo 1172403 2970017 := bstep (se 2 (by rfl) ⟨1113756, by rfl⟩ : syracuseStep 2970017 = 2227513) B2227513
theorem B144429479 : Blo 1172403 144429479 := bstep (se 1 (by rfl) ⟨108322109, by rfl⟩ : syracuseStep 144429479 = 216644219) B216644219
theorem B8909351 : Blo 1172403 8909351 := bstep (se 1 (by rfl) ⟨6682013, by rfl⟩ : syracuseStep 8909351 = 13364027) B13364027
theorem B10703555 : Blo 1172403 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B5640911 : Blo 1172403 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B205869977 : Blo 1172403 205869977 := bstep (se 2 (by rfl) ⟨77201241, by rfl⟩ : syracuseStep 205869977 = 154402483) B154402483
theorem B24400925 : Blo 1172403 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B6026395 : Blo 1172403 6026395 := bstep (se 1 (by rfl) ⟨4519796, by rfl⟩ : syracuseStep 6026395 = 9039593) B9039593
theorem B3757225 : Blo 1172403 3757225 := bstep (se 2 (by rfl) ⟨1408959, by rfl⟩ : syracuseStep 3757225 = 2817919) B2817919
theorem B9156115 : Blo 1172403 9156115 := bstep (se 1 (by rfl) ⟨6867086, by rfl⟩ : syracuseStep 9156115 = 13734173) B13734173
theorem B1979977 : Blo 1172403 1979977 := bstep (se 2 (by rfl) ⟨742491, by rfl⟩ : syracuseStep 1979977 = 1484983) B1484983
theorem B5944913 : Blo 1172403 5944913 := bstep (se 2 (by rfl) ⟨2229342, by rfl⟩ : syracuseStep 5944913 = 4458685) B4458685
theorem B2225819 : Blo 1172403 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B5945075 : Blo 1172403 5945075 := bstep (se 1 (by rfl) ⟨4458806, by rfl⟩ : syracuseStep 5945075 = 8917613) B8917613
theorem B3962735 : Blo 1172403 3962735 := bstep (se 1 (by rfl) ⟨2972051, by rfl⟩ : syracuseStep 3962735 = 5944103) B5944103
theorem B3340187 : Blo 1172403 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B1759259 : Blo 1172403 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B1980443 : Blo 1172403 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B1669513 : Blo 1172403 1669513 := bstep (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) B1252135
theorem B1759625 : Blo 1172403 1759625 := bstep (se 2 (by rfl) ⟨659859, by rfl⟩ : syracuseStep 1759625 = 1319719) B1319719
theorem B5937623 : Blo 1172403 5937623 := bstep (se 1 (by rfl) ⟨4453217, by rfl⟩ : syracuseStep 5937623 = 8906435) B8906435
theorem B65067623 : Blo 1172403 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B1784431 : Blo 1172403 1784431 := bstep (se 1 (by rfl) ⟨1338323, by rfl⟩ : syracuseStep 1784431 = 2676647) B2676647
theorem B1760351 : Blo 1172403 1760351 := bstep (se 1 (by rfl) ⟨1320263, by rfl⟩ : syracuseStep 1760351 = 2640527) B2640527
theorem B6020527 : Blo 1172403 6020527 := bstep (se 1 (by rfl) ⟨4515395, by rfl⟩ : syracuseStep 6020527 = 9030791) B9030791
theorem B25386695 : Blo 1172403 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B1760999 : Blo 1172403 1760999 := bstep (se 1 (by rfl) ⟨1320749, by rfl⟩ : syracuseStep 1760999 = 2641499) B2641499
theorem B1761161 : Blo 1172403 1761161 := bstep (se 2 (by rfl) ⟨660435, by rfl⟩ : syracuseStep 1761161 = 1320871) B1320871
theorem B13361111 : Blo 1172403 13361111 := bstep (se 1 (by rfl) ⟨10020833, by rfl⟩ : syracuseStep 13361111 = 20041667) B20041667
theorem B1761335 : Blo 1172403 1761335 := bstep (se 1 (by rfl) ⟨1321001, by rfl⟩ : syracuseStep 1761335 = 2642003) B2642003
theorem B1761407 : Blo 1172403 1761407 := bstep (se 1 (by rfl) ⟨1321055, by rfl⟩ : syracuseStep 1761407 = 2642111) B2642111
theorem B2228447 : Blo 1172403 2228447 := bstep (se 1 (by rfl) ⟨1671335, by rfl⟩ : syracuseStep 2228447 = 3342671) B3342671
theorem B3342647 : Blo 1172403 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B5939567 : Blo 1172403 5939567 := bstep (se 1 (by rfl) ⟨4454675, by rfl⟩ : syracuseStep 5939567 = 8909351) B8909351
theorem B7135703 : Blo 1172403 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B3760607 : Blo 1172403 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B2638799 : Blo 1172403 2638799 := bstep (se 1 (by rfl) ⟨1979099, by rfl⟩ : syracuseStep 2638799 = 3958199) B3958199
theorem B1983455 : Blo 1172403 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B2114687 : Blo 1172403 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B3343673 : Blo 1172403 3343673 := bstep (se 2 (by rfl) ⟨1253877, by rfl⟩ : syracuseStep 3343673 = 2507755) B2507755
theorem B1172839 : Blo 1172403 1172839 := bstep (se 1 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 1172839 = 1759259) B1759259
theorem B1320295 : Blo 1172403 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B1173083 : Blo 1172403 1173083 := bstep (se 1 (by rfl) ⟨879812, by rfl⟩ : syracuseStep 1173083 = 1759625) B1759625
theorem B3958415 : Blo 1172403 3958415 := bstep (se 1 (by rfl) ⟨2968811, by rfl⟩ : syracuseStep 3958415 = 5937623) B5937623
theorem B43378415 : Blo 1172403 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B2541467 : Blo 1172403 2541467 := bstep (se 1 (by rfl) ⟨1906100, by rfl⟩ : syracuseStep 2541467 = 3812201) B3812201
theorem B4458473 : Blo 1172403 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B12208153 : Blo 1172403 12208153 := bstep (se 2 (by rfl) ⟨4578057, by rfl⟩ : syracuseStep 12208153 = 9156115) B9156115
theorem B8456233 : Blo 1172403 8456233 := bstep (se 2 (by rfl) ⟨3171087, by rfl⟩ : syracuseStep 8456233 = 6342175) B6342175
theorem B1173567 : Blo 1172403 1173567 := bstep (se 1 (by rfl) ⟨880175, by rfl⟩ : syracuseStep 1173567 = 1760351) B1760351
theorem B2639969 : Blo 1172403 2639969 := bstep (se 2 (by rfl) ⟨989988, by rfl⟩ : syracuseStep 2639969 = 1979977) B1979977
theorem B4458671 : Blo 1172403 4458671 := bstep (se 1 (by rfl) ⟨3344003, by rfl⟩ : syracuseStep 4458671 = 6688007) B6688007
theorem B30509243 : Blo 1172403 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B1173999 : Blo 1172403 1173999 := bstep (se 1 (by rfl) ⟨880499, by rfl⟩ : syracuseStep 1173999 = 1760999) B1760999
theorem B16910855 : Blo 1172403 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B1174107 : Blo 1172403 1174107 := bstep (se 1 (by rfl) ⟨880580, by rfl⟩ : syracuseStep 1174107 = 1761161) B1761161
theorem B8907407 : Blo 1172403 8907407 := bstep (se 1 (by rfl) ⟨6680555, by rfl⟩ : syracuseStep 8907407 = 13361111) B13361111
theorem B2640635 : Blo 1172403 2640635 := bstep (se 1 (by rfl) ⟨1980476, by rfl⟩ : syracuseStep 2640635 = 3960953) B3960953
theorem B3959549 : Blo 1172403 3959549 := bstep (se 3 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 3959549 = 1484831) B1484831
theorem B439757585 : Blo 1172403 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B16903241 : Blo 1172403 16903241 := bstep (se 2 (by rfl) ⟨6338715, by rfl⟩ : syracuseStep 16903241 = 12677431) B12677431
theorem B15035867 : Blo 1172403 15035867 := bstep (se 1 (by rfl) ⟨11276900, by rfl⟩ : syracuseStep 15035867 = 22553801) B22553801
theorem B2379241 : Blo 1172403 2379241 := bstep (se 2 (by rfl) ⟨892215, by rfl⟩ : syracuseStep 2379241 = 1784431) B1784431
theorem B4451867 : Blo 1172403 4451867 := bstep (se 1 (by rfl) ⟨3338900, by rfl⟩ : syracuseStep 4451867 = 6677801) B6677801
theorem B2641823 : Blo 1172403 2641823 := bstep (se 1 (by rfl) ⟨1981367, by rfl⟩ : syracuseStep 2641823 = 3962735) B3962735
theorem B3961007 : Blo 1172403 3961007 := bstep (se 1 (by rfl) ⟨2970755, by rfl⟩ : syracuseStep 3961007 = 5941511) B5941511
theorem B5009633 : Blo 1172403 5009633 := bstep (se 2 (by rfl) ⟨1878612, by rfl⟩ : syracuseStep 5009633 = 3757225) B3757225
theorem B3961115 : Blo 1172403 3961115 := bstep (se 1 (by rfl) ⟨2970836, by rfl⟩ : syracuseStep 3961115 = 5941673) B5941673
theorem B5935517 : Blo 1172403 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B14283479 : Blo 1172403 14283479 := bstep (se 1 (by rfl) ⟨10712609, by rfl⟩ : syracuseStep 14283479 = 21425219) B21425219
theorem B1980011 : Blo 1172403 1980011 := bstep (se 1 (by rfl) ⟨1485008, by rfl⟩ : syracuseStep 1980011 = 2970017) B2970017
theorem B96286319 : Blo 1172403 96286319 := bstep (se 1 (by rfl) ⟨72214739, by rfl⟩ : syracuseStep 96286319 = 144429479) B144429479
theorem B2226017 : Blo 1172403 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B1759097 : Blo 1172403 1759097 := bstep (se 2 (by rfl) ⟨659661, by rfl⟩ : syracuseStep 1759097 = 1319323) B1319323
theorem B137246651 : Blo 1172403 137246651 := bstep (se 1 (by rfl) ⟨102934988, by rfl⟩ : syracuseStep 137246651 = 205869977) B205869977
theorem B16267283 : Blo 1172403 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B3963275 : Blo 1172403 3963275 := bstep (se 1 (by rfl) ⟨2972456, by rfl⟩ : syracuseStep 3963275 = 5944913) B5944913
theorem B1759679 : Blo 1172403 1759679 := bstep (se 1 (by rfl) ⟨1319759, by rfl⟩ : syracuseStep 1759679 = 2639519) B2639519
theorem B3963383 : Blo 1172403 3963383 := bstep (se 1 (by rfl) ⟨2972537, by rfl⟩ : syracuseStep 3963383 = 5945075) B5945075
theorem B25352783 : Blo 1172403 25352783 := bstep (se 1 (by rfl) ⟨19014587, by rfl⟩ : syracuseStep 25352783 = 38029175) B38029175
theorem B2226791 : Blo 1172403 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B9034487 : Blo 1172403 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B8903519 : Blo 1172403 8903519 := bstep (se 1 (by rfl) ⟨6677639, by rfl⟩ : syracuseStep 8903519 = 13355279) B13355279
theorem B8035193 : Blo 1172403 8035193 := bstep (se 2 (by rfl) ⟨3013197, by rfl⟩ : syracuseStep 8035193 = 6026395) B6026395
theorem B8027369 : Blo 1172403 8027369 := bstep (se 2 (by rfl) ⟨3010263, by rfl⟩ : syracuseStep 8027369 = 6020527) B6020527
theorem B1760873 : Blo 1172403 1760873 := bstep (se 2 (by rfl) ⟨660327, by rfl⟩ : syracuseStep 1760873 = 1320655) B1320655
theorem B1760879 : Blo 1172403 1760879 := bstep (se 1 (by rfl) ⟨1320659, by rfl⟩ : syracuseStep 1760879 = 2641319) B2641319
theorem B96370397 : Blo 1172403 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B16924463 : Blo 1172403 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B16277537 : Blo 1172403 16277537 := bstep (se 2 (by rfl) ⟨6104076, by rfl⟩ : syracuseStep 16277537 = 12208153) B12208153
theorem B3957011 : Blo 1172403 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B8913725 : Blo 1172403 8913725 := bstep (se 3 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 8913725 = 3342647) B3342647
theorem B2229115 : Blo 1172403 2229115 := bstep (se 1 (by rfl) ⟨1671836, by rfl⟩ : syracuseStep 2229115 = 3343673) B3343673
theorem B1320007 : Blo 1172403 1320007 := bstep (se 1 (by rfl) ⟨990005, by rfl⟩ : syracuseStep 1320007 = 1980011) B1980011
theorem B2638943 : Blo 1172403 2638943 := bstep (se 1 (by rfl) ⟨1979207, by rfl⟩ : syracuseStep 2638943 = 3958415) B3958415
theorem B28918943 : Blo 1172403 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B1484011 : Blo 1172403 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B1172731 : Blo 1172403 1172731 := bstep (se 1 (by rfl) ⟨879548, by rfl⟩ : syracuseStep 1172731 = 1759097) B1759097
theorem B10028285 : Blo 1172403 10028285 := bstep (se 3 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 10028285 = 3760607) B3760607
theorem B91497767 : Blo 1172403 91497767 := bstep (se 1 (by rfl) ⟨68623325, by rfl⟩ : syracuseStep 91497767 = 137246651) B137246651
theorem B1173119 : Blo 1172403 1173119 := bstep (se 1 (by rfl) ⟨879839, by rfl⟩ : syracuseStep 1173119 = 1759679) B1759679
theorem B11273903 : Blo 1172403 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B16901855 : Blo 1172403 16901855 := bstep (se 1 (by rfl) ⟨12676391, by rfl⟩ : syracuseStep 16901855 = 25352783) B25352783
theorem B6022991 : Blo 1172403 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B2639699 : Blo 1172403 2639699 := bstep (se 1 (by rfl) ⟨1979774, by rfl⟩ : syracuseStep 2639699 = 3959549) B3959549
theorem B3172321 : Blo 1172403 3172321 := bstep (se 2 (by rfl) ⟨1189620, by rfl⟩ : syracuseStep 3172321 = 2379241) B2379241
theorem B5351579 : Blo 1172403 5351579 := bstep (se 1 (by rfl) ⟨4013684, by rfl⟩ : syracuseStep 5351579 = 8027369) B8027369
theorem B2967911 : Blo 1172403 2967911 := bstep (se 1 (by rfl) ⟨2225933, by rfl⟩ : syracuseStep 2967911 = 4451867) B4451867
theorem B1173915 : Blo 1172403 1173915 := bstep (se 1 (by rfl) ⟨880436, by rfl⟩ : syracuseStep 1173915 = 1760873) B1760873
theorem B6777245 : Blo 1172403 6777245 := bstep (se 3 (by rfl) ⟨1270733, by rfl⟩ : syracuseStep 6777245 = 2541467) B2541467
theorem B1173919 : Blo 1172403 1173919 := bstep (se 1 (by rfl) ⟨880439, by rfl⟩ : syracuseStep 1173919 = 1760879) B1760879
theorem B11282975 : Blo 1172403 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B1174223 : Blo 1172403 1174223 := bstep (se 1 (by rfl) ⟨880667, by rfl⟩ : syracuseStep 1174223 = 1761335) B1761335
theorem B11274977 : Blo 1172403 11274977 := bstep (se 2 (by rfl) ⟨4228116, by rfl⟩ : syracuseStep 11274977 = 8456233) B8456233
theorem B1174271 : Blo 1172403 1174271 := bstep (se 1 (by rfl) ⟨880703, by rfl⟩ : syracuseStep 1174271 = 1761407) B1761407
theorem B2640671 : Blo 1172403 2640671 := bstep (se 1 (by rfl) ⟨1980503, by rfl⟩ : syracuseStep 2640671 = 3961007) B3961007
theorem B1485631 : Blo 1172403 1485631 := bstep (se 1 (by rfl) ⟨1114223, by rfl⟩ : syracuseStep 1485631 = 2228447) B2228447
theorem B2640743 : Blo 1172403 2640743 := bstep (se 1 (by rfl) ⟨1980557, by rfl⟩ : syracuseStep 2640743 = 3961115) B3961115
theorem B3959711 : Blo 1172403 3959711 := bstep (se 1 (by rfl) ⟨2969783, by rfl⟩ : syracuseStep 3959711 = 5939567) B5939567
theorem B5639165 : Blo 1172403 5639165 := bstep (se 3 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 5639165 = 2114687) B2114687
theorem B9522319 : Blo 1172403 9522319 := bstep (se 1 (by rfl) ⟨7141739, by rfl⟩ : syracuseStep 9522319 = 14283479) B14283479
theorem B1322303 : Blo 1172403 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B2642183 : Blo 1172403 2642183 := bstep (se 1 (by rfl) ⟨1981637, by rfl⟩ : syracuseStep 2642183 = 3963275) B3963275
theorem B2642255 : Blo 1172403 2642255 := bstep (se 1 (by rfl) ⟨1981691, by rfl⟩ : syracuseStep 2642255 = 3963383) B3963383
theorem B293171723 : Blo 1172403 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B5935679 : Blo 1172403 5935679 := bstep (se 1 (by rfl) ⟨4451759, by rfl⟩ : syracuseStep 5935679 = 8903519) B8903519
theorem B11268827 : Blo 1172403 11268827 := bstep (se 1 (by rfl) ⟨8451620, by rfl⟩ : syracuseStep 11268827 = 16903241) B16903241
theorem B10023911 : Blo 1172403 10023911 := bstep (se 1 (by rfl) ⟨7517933, by rfl⟩ : syracuseStep 10023911 = 15035867) B15035867
theorem B64246931 : Blo 1172403 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B3339755 : Blo 1172403 3339755 := bstep (se 1 (by rfl) ⟨2504816, by rfl⟩ : syracuseStep 3339755 = 5009633) B5009633
theorem B4757135 : Blo 1172403 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B1759199 : Blo 1172403 1759199 := bstep (se 1 (by rfl) ⟨1319399, by rfl⟩ : syracuseStep 1759199 = 2638799) B2638799
theorem B64190879 : Blo 1172403 64190879 := bstep (se 1 (by rfl) ⟨48143159, by rfl⟩ : syracuseStep 64190879 = 96286319) B96286319
theorem B2972315 : Blo 1172403 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B10844855 : Blo 1172403 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B1759979 : Blo 1172403 1759979 := bstep (se 1 (by rfl) ⟨1319984, by rfl⟩ : syracuseStep 1759979 = 2639969) B2639969
theorem B2972447 : Blo 1172403 2972447 := bstep (se 1 (by rfl) ⟨2229335, by rfl⟩ : syracuseStep 2972447 = 4458671) B4458671
theorem B20339495 : Blo 1172403 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B5938109 : Blo 1172403 5938109 := bstep (se 3 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 5938109 = 2226791) B2226791
theorem B5938271 : Blo 1172403 5938271 := bstep (se 1 (by rfl) ⟨4453703, by rfl⟩ : syracuseStep 5938271 = 8907407) B8907407
theorem B1760393 : Blo 1172403 1760393 := bstep (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) B1320295
theorem B1760423 : Blo 1172403 1760423 := bstep (se 1 (by rfl) ⟨1320317, by rfl⟩ : syracuseStep 1760423 = 2640635) B2640635
theorem B5356795 : Blo 1172403 5356795 := bstep (se 1 (by rfl) ⟨4017596, by rfl⟩ : syracuseStep 5356795 = 8035193) B8035193
theorem B1761215 : Blo 1172403 1761215 := bstep (se 1 (by rfl) ⟨1320911, by rfl⟩ : syracuseStep 1761215 = 2641823) B2641823
theorem B1761455 : Blo 1172403 1761455 := bstep (se 1 (by rfl) ⟨1321091, by rfl⟩ : syracuseStep 1761455 = 2642183) B2642183
theorem B2638007 : Blo 1172403 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B1761503 : Blo 1172403 1761503 := bstep (se 1 (by rfl) ⟨1321127, by rfl⟩ : syracuseStep 1761503 = 2642255) B2642255
theorem B3957119 : Blo 1172403 3957119 := bstep (se 1 (by rfl) ⟨2967839, by rfl⟩ : syracuseStep 3957119 = 5935679) B5935679
theorem B7512551 : Blo 1172403 7512551 := bstep (se 1 (by rfl) ⟨5634413, by rfl⟩ : syracuseStep 7512551 = 11268827) B11268827
theorem B6685523 : Blo 1172403 6685523 := bstep (se 1 (by rfl) ⟨5014142, by rfl⟩ : syracuseStep 6685523 = 10028285) B10028285
theorem B4015327 : Blo 1172403 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B1172799 : Blo 1172403 1172799 := bstep (se 1 (by rfl) ⟨879599, by rfl⟩ : syracuseStep 1172799 = 1759199) B1759199
theorem B50742773 : Blo 1172403 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B7521983 : Blo 1172403 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B1173319 : Blo 1172403 1173319 := bstep (se 1 (by rfl) ⟨879989, by rfl⟩ : syracuseStep 1173319 = 1759979) B1759979
theorem B13559663 : Blo 1172403 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B2639807 : Blo 1172403 2639807 := bstep (se 1 (by rfl) ⟨1979855, by rfl⟩ : syracuseStep 2639807 = 3959711) B3959711
theorem B3958739 : Blo 1172403 3958739 := bstep (se 1 (by rfl) ⟨2969054, by rfl⟩ : syracuseStep 3958739 = 5938109) B5938109
theorem B3958847 : Blo 1172403 3958847 := bstep (se 1 (by rfl) ⟨2969135, by rfl⟩ : syracuseStep 3958847 = 5938271) B5938271
theorem B1173595 : Blo 1172403 1173595 := bstep (se 1 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 1173595 = 1760393) B1760393
theorem B1173615 : Blo 1172403 1173615 := bstep (se 1 (by rfl) ⟨880211, by rfl⟩ : syracuseStep 1173615 = 1760423) B1760423
theorem B1174143 : Blo 1172403 1174143 := bstep (se 1 (by rfl) ⟨880607, by rfl⟩ : syracuseStep 1174143 = 1761215) B1761215
theorem B4229761 : Blo 1172403 4229761 := bstep (se 2 (by rfl) ⟨1586160, by rfl⟩ : syracuseStep 4229761 = 3172321) B3172321
theorem B195447815 : Blo 1172403 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B5942483 : Blo 1172403 5942483 := bstep (se 1 (by rfl) ⟨4456862, by rfl⟩ : syracuseStep 5942483 = 8913725) B8913725
theorem B42831287 : Blo 1172403 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B243994045 : Blo 1172403 243994045 := bstep (se 3 (by rfl) ⟨45748883, by rfl⟩ : syracuseStep 243994045 = 91497767) B91497767
theorem B19279295 : Blo 1172403 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B3526141 : Blo 1172403 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B7515935 : Blo 1172403 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B11267903 : Blo 1172403 11267903 := bstep (se 1 (by rfl) ⟨8450927, by rfl⟩ : syracuseStep 11267903 = 16901855) B16901855
theorem B3567719 : Blo 1172403 3567719 := bstep (se 1 (by rfl) ⟨2675789, by rfl⟩ : syracuseStep 3567719 = 5351579) B5351579
theorem B1978607 : Blo 1172403 1978607 := bstep (se 1 (by rfl) ⟨1483955, by rfl⟩ : syracuseStep 1978607 = 2967911) B2967911
theorem B4518163 : Blo 1172403 4518163 := bstep (se 1 (by rfl) ⟨3388622, by rfl⟩ : syracuseStep 4518163 = 6777245) B6777245
theorem B1978681 : Blo 1172403 1978681 := bstep (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) B1484011
theorem B7229903 : Blo 1172403 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B7516651 : Blo 1172403 7516651 := bstep (se 1 (by rfl) ⟨5637488, by rfl⟩ : syracuseStep 7516651 = 11274977) B11274977
theorem B10851691 : Blo 1172403 10851691 := bstep (se 1 (by rfl) ⟨8138768, by rfl⟩ : syracuseStep 10851691 = 16277537) B16277537
theorem B6682607 : Blo 1172403 6682607 := bstep (se 1 (by rfl) ⟨5011955, by rfl⟩ : syracuseStep 6682607 = 10023911) B10023911
theorem B1759295 : Blo 1172403 1759295 := bstep (se 1 (by rfl) ⟨1319471, by rfl⟩ : syracuseStep 1759295 = 2638943) B2638943
theorem B2226503 : Blo 1172403 2226503 := bstep (se 1 (by rfl) ⟨1669877, by rfl⟩ : syracuseStep 2226503 = 3339755) B3339755
theorem B1980841 : Blo 1172403 1980841 := bstep (se 2 (by rfl) ⟨742815, by rfl⟩ : syracuseStep 1980841 = 1485631) B1485631
theorem B2972153 : Blo 1172403 2972153 := bstep (se 2 (by rfl) ⟨1114557, by rfl⟩ : syracuseStep 2972153 = 2229115) B2229115
theorem B1759799 : Blo 1172403 1759799 := bstep (se 1 (by rfl) ⟨1319849, by rfl⟩ : syracuseStep 1759799 = 2639699) B2639699
theorem B1760009 : Blo 1172403 1760009 := bstep (se 2 (by rfl) ⟨660003, by rfl⟩ : syracuseStep 1760009 = 1320007) B1320007
theorem B12696425 : Blo 1172403 12696425 := bstep (se 2 (by rfl) ⟨4761159, by rfl⟩ : syracuseStep 12696425 = 9522319) B9522319
theorem B42793919 : Blo 1172403 42793919 := bstep (se 1 (by rfl) ⟨32095439, by rfl⟩ : syracuseStep 42793919 = 64190879) B64190879
theorem B7142393 : Blo 1172403 7142393 := bstep (se 2 (by rfl) ⟨2678397, by rfl⟩ : syracuseStep 7142393 = 5356795) B5356795
theorem B1981543 : Blo 1172403 1981543 := bstep (se 1 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 1981543 = 2972315) B2972315
theorem B1760447 : Blo 1172403 1760447 := bstep (se 1 (by rfl) ⟨1320335, by rfl⟩ : syracuseStep 1760447 = 2640671) B2640671
theorem B1981631 : Blo 1172403 1981631 := bstep (se 1 (by rfl) ⟨1486223, by rfl⟩ : syracuseStep 1981631 = 2972447) B2972447
theorem B1760495 : Blo 1172403 1760495 := bstep (se 1 (by rfl) ⟨1320371, by rfl⟩ : syracuseStep 1760495 = 2640743) B2640743
theorem B3759443 : Blo 1172403 3759443 := bstep (se 1 (by rfl) ⟨2819582, by rfl⟩ : syracuseStep 3759443 = 5639165) B5639165
theorem B1319071 : Blo 1172403 1319071 := bstep (se 1 (by rfl) ⟨989303, by rfl⟩ : syracuseStep 1319071 = 1978607) B1978607
theorem B2638079 : Blo 1172403 2638079 := bstep (se 1 (by rfl) ⟨1978559, by rfl⟩ : syracuseStep 2638079 = 3957119) B3957119
theorem B2638241 : Blo 1172403 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B4457015 : Blo 1172403 4457015 := bstep (se 1 (by rfl) ⟨3342761, by rfl⟩ : syracuseStep 4457015 = 6685523) B6685523
theorem B5014655 : Blo 1172403 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B2639159 : Blo 1172403 2639159 := bstep (se 1 (by rfl) ⟨1979369, by rfl⟩ : syracuseStep 2639159 = 3958739) B3958739
theorem B1172863 : Blo 1172403 1172863 := bstep (se 1 (by rfl) ⟨879647, by rfl⟩ : syracuseStep 1172863 = 1759295) B1759295
theorem B2639231 : Blo 1172403 2639231 := bstep (se 1 (by rfl) ⟨1979423, by rfl⟩ : syracuseStep 2639231 = 3958847) B3958847
theorem B1484335 : Blo 1172403 1484335 := bstep (se 1 (by rfl) ⟨1113251, by rfl⟩ : syracuseStep 1484335 = 2226503) B2226503
theorem B1173199 : Blo 1172403 1173199 := bstep (se 1 (by rfl) ⟨879899, by rfl⟩ : syracuseStep 1173199 = 1759799) B1759799
theorem B14468921 : Blo 1172403 14468921 := bstep (se 2 (by rfl) ⟨5425845, by rfl⟩ : syracuseStep 14468921 = 10851691) B10851691
theorem B1173339 : Blo 1172403 1173339 := bstep (se 1 (by rfl) ⟨880004, by rfl⟩ : syracuseStep 1173339 = 1760009) B1760009
theorem B8464283 : Blo 1172403 8464283 := bstep (se 1 (by rfl) ⟨6348212, by rfl⟩ : syracuseStep 8464283 = 12696425) B12696425
theorem B4761595 : Blo 1172403 4761595 := bstep (se 1 (by rfl) ⟨3571196, by rfl⟩ : syracuseStep 4761595 = 7142393) B7142393
theorem B1173631 : Blo 1172403 1173631 := bstep (se 1 (by rfl) ⟨880223, by rfl⟩ : syracuseStep 1173631 = 1760447) B1760447
theorem B1321087 : Blo 1172403 1321087 := bstep (se 1 (by rfl) ⟨990815, by rfl⟩ : syracuseStep 1321087 = 1981631) B1981631
theorem B1173663 : Blo 1172403 1173663 := bstep (se 1 (by rfl) ⟨880247, by rfl⟩ : syracuseStep 1173663 = 1760495) B1760495
theorem B2378479 : Blo 1172403 2378479 := bstep (se 1 (by rfl) ⟨1783859, by rfl⟩ : syracuseStep 2378479 = 3567719) B3567719
theorem B1174303 : Blo 1172403 1174303 := bstep (se 1 (by rfl) ⟨880727, by rfl⟩ : syracuseStep 1174303 = 1761455) B1761455
theorem B1174335 : Blo 1172403 1174335 := bstep (se 1 (by rfl) ⟨880751, by rfl⟩ : syracuseStep 1174335 = 1761503) B1761503
theorem B5008367 : Blo 1172403 5008367 := bstep (se 1 (by rfl) ⟨3756275, by rfl⟩ : syracuseStep 5008367 = 7512551) B7512551
theorem B6024217 : Blo 1172403 6024217 := bstep (se 2 (by rfl) ⟨2259081, by rfl⟩ : syracuseStep 6024217 = 4518163) B4518163
theorem B2641121 : Blo 1172403 2641121 := bstep (se 2 (by rfl) ⟨990420, by rfl⟩ : syracuseStep 2641121 = 1980841) B1980841
theorem B10022201 : Blo 1172403 10022201 := bstep (se 2 (by rfl) ⟨3758325, by rfl⟩ : syracuseStep 10022201 = 7516651) B7516651
theorem B5639681 : Blo 1172403 5639681 := bstep (se 2 (by rfl) ⟨2114880, by rfl⟩ : syracuseStep 5639681 = 4229761) B4229761
theorem B33828515 : Blo 1172403 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B19279741 : Blo 1172403 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B9039775 : Blo 1172403 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B2642057 : Blo 1172403 2642057 := bstep (se 2 (by rfl) ⟨990771, by rfl⟩ : syracuseStep 2642057 = 1981543) B1981543
theorem B5353769 : Blo 1172403 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B325325393 : Blo 1172403 325325393 := bstep (se 2 (by rfl) ⟨121997022, by rfl⟩ : syracuseStep 325325393 = 243994045) B243994045
theorem B28529279 : Blo 1172403 28529279 := bstep (se 1 (by rfl) ⟨21396959, by rfl⟩ : syracuseStep 28529279 = 42793919) B42793919
theorem B130298543 : Blo 1172403 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B3961655 : Blo 1172403 3961655 := bstep (se 1 (by rfl) ⟨2971241, by rfl⟩ : syracuseStep 3961655 = 5942483) B5942483
theorem B28554191 : Blo 1172403 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B5010623 : Blo 1172403 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B1758671 : Blo 1172403 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B1759871 : Blo 1172403 1759871 := bstep (se 1 (by rfl) ⟨1319903, by rfl⟩ : syracuseStep 1759871 = 2639807) B2639807
theorem B4455071 : Blo 1172403 4455071 := bstep (se 1 (by rfl) ⟨3341303, by rfl⟩ : syracuseStep 4455071 = 6682607) B6682607
theorem B1981435 : Blo 1172403 1981435 := bstep (se 1 (by rfl) ⟨1486076, by rfl⟩ : syracuseStep 1981435 = 2972153) B2972153
theorem B4701521 : Blo 1172403 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B2506295 : Blo 1172403 2506295 := bstep (se 1 (by rfl) ⟨1879721, by rfl⟩ : syracuseStep 2506295 = 3759443) B3759443
theorem B12852863 : Blo 1172403 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B7511935 : Blo 1172403 7511935 := bstep (se 1 (by rfl) ⟨5633951, by rfl⟩ : syracuseStep 7511935 = 11267903) B11267903
theorem B1761371 : Blo 1172403 1761371 := bstep (se 1 (by rfl) ⟨1321028, by rfl⟩ : syracuseStep 1761371 = 2642057) B2642057
theorem B1761449 : Blo 1172403 1761449 := bstep (se 2 (by rfl) ⟨660543, by rfl⟩ : syracuseStep 1761449 = 1321087) B1321087
theorem B216883595 : Blo 1172403 216883595 := bstep (se 1 (by rfl) ⟨162662696, by rfl⟩ : syracuseStep 216883595 = 325325393) B325325393
theorem B3343103 : Blo 1172403 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B1172447 : Blo 1172403 1172447 := bstep (se 1 (by rfl) ⟨879335, by rfl⟩ : syracuseStep 1172447 = 1758671) B1758671
theorem B3171305 : Blo 1172403 3171305 := bstep (se 2 (by rfl) ⟨1189239, by rfl⟩ : syracuseStep 3171305 = 2378479) B2378479
theorem B6348793 : Blo 1172403 6348793 := bstep (se 2 (by rfl) ⟨2380797, by rfl⟩ : syracuseStep 6348793 = 4761595) B4761595
theorem B1173247 : Blo 1172403 1173247 := bstep (se 1 (by rfl) ⟨879935, by rfl⟩ : syracuseStep 1173247 = 1759871) B1759871
theorem B12053033 : Blo 1172403 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B2641103 : Blo 1172403 2641103 := bstep (se 1 (by rfl) ⟨1980827, by rfl⟩ : syracuseStep 2641103 = 3961655) B3961655
theorem B12537389 : Blo 1172403 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B9645947 : Blo 1172403 9645947 := bstep (se 1 (by rfl) ⟨7234460, by rfl⟩ : syracuseStep 9645947 = 14468921) B14468921
theorem B2641913 : Blo 1172403 2641913 := bstep (se 2 (by rfl) ⟨990717, by rfl⟩ : syracuseStep 2641913 = 1981435) B1981435
theorem B8032289 : Blo 1172403 8032289 := bstep (se 2 (by rfl) ⟨3012108, by rfl⟩ : syracuseStep 8032289 = 6024217) B6024217
theorem B2970047 : Blo 1172403 2970047 := bstep (se 1 (by rfl) ⟨2227535, by rfl⟩ : syracuseStep 2970047 = 4455071) B4455071
theorem B3338911 : Blo 1172403 3338911 := bstep (se 1 (by rfl) ⟨2504183, by rfl⟩ : syracuseStep 3338911 = 5008367) B5008367
theorem B1979113 : Blo 1172403 1979113 := bstep (se 2 (by rfl) ⟨742167, by rfl⟩ : syracuseStep 1979113 = 1484335) B1484335
theorem B6681467 : Blo 1172403 6681467 := bstep (se 1 (by rfl) ⟨5011100, by rfl⟩ : syracuseStep 6681467 = 10022201) B10022201
theorem B10015913 : Blo 1172403 10015913 := bstep (se 2 (by rfl) ⟨3755967, by rfl⟩ : syracuseStep 10015913 = 7511935) B7511935
theorem B1758719 : Blo 1172403 1758719 := bstep (se 1 (by rfl) ⟨1319039, by rfl⟩ : syracuseStep 1758719 = 2638079) B2638079
theorem B3569179 : Blo 1172403 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B1758761 : Blo 1172403 1758761 := bstep (se 2 (by rfl) ⟨659535, by rfl⟩ : syracuseStep 1758761 = 1319071) B1319071
theorem B1758827 : Blo 1172403 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B2971343 : Blo 1172403 2971343 := bstep (se 1 (by rfl) ⟨2228507, by rfl⟩ : syracuseStep 2971343 = 4457015) B4457015
theorem B19019519 : Blo 1172403 19019519 := bstep (se 1 (by rfl) ⟨14264639, by rfl⟩ : syracuseStep 19019519 = 28529279) B28529279
theorem B86865695 : Blo 1172403 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B19036127 : Blo 1172403 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B3340415 : Blo 1172403 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B1759439 : Blo 1172403 1759439 := bstep (se 1 (by rfl) ⟨1319579, by rfl⟩ : syracuseStep 1759439 = 2639159) B2639159
theorem B1759487 : Blo 1172403 1759487 := bstep (se 1 (by rfl) ⟨1319615, by rfl⟩ : syracuseStep 1759487 = 2639231) B2639231
theorem B5642855 : Blo 1172403 5642855 := bstep (se 1 (by rfl) ⟨4232141, by rfl⟩ : syracuseStep 5642855 = 8464283) B8464283
theorem B1760747 : Blo 1172403 1760747 := bstep (se 1 (by rfl) ⟨1320560, by rfl⟩ : syracuseStep 1760747 = 2641121) B2641121
theorem B3759787 : Blo 1172403 3759787 := bstep (se 1 (by rfl) ⟨2819840, by rfl⟩ : syracuseStep 3759787 = 5639681) B5639681
theorem B1670863 : Blo 1172403 1670863 := bstep (se 1 (by rfl) ⟨1253147, by rfl⟩ : syracuseStep 1670863 = 2506295) B2506295
theorem B8568575 : Blo 1172403 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B22552343 : Blo 1172403 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B25706321 : Blo 1172403 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B144589063 : Blo 1172403 144589063 := bstep (se 1 (by rfl) ⟨108441797, by rfl⟩ : syracuseStep 144589063 = 216883595) B216883595
theorem B2228735 : Blo 1172403 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B2114203 : Blo 1172403 2114203 := bstep (se 1 (by rfl) ⟨1585652, by rfl⟩ : syracuseStep 2114203 = 3171305) B3171305
theorem B6677275 : Blo 1172403 6677275 := bstep (se 1 (by rfl) ⟨5007956, by rfl⟩ : syracuseStep 6677275 = 10015913) B10015913
theorem B2638817 : Blo 1172403 2638817 := bstep (se 2 (by rfl) ⟨989556, by rfl⟩ : syracuseStep 2638817 = 1979113) B1979113
theorem B1172479 : Blo 1172403 1172479 := bstep (se 1 (by rfl) ⟨879359, by rfl⟩ : syracuseStep 1172479 = 1758719) B1758719
theorem B1172507 : Blo 1172403 1172507 := bstep (se 1 (by rfl) ⟨879380, by rfl⟩ : syracuseStep 1172507 = 1758761) B1758761
theorem B1172551 : Blo 1172403 1172551 := bstep (se 1 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 1172551 = 1758827) B1758827
theorem B57910463 : Blo 1172403 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B12690751 : Blo 1172403 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B33433037 : Blo 1172403 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B1172959 : Blo 1172403 1172959 := bstep (se 1 (by rfl) ⟨879719, by rfl⟩ : syracuseStep 1172959 = 1759439) B1759439
theorem B1172991 : Blo 1172403 1172991 := bstep (se 1 (by rfl) ⟨879743, by rfl⟩ : syracuseStep 1172991 = 1759487) B1759487
theorem B3761903 : Blo 1172403 3761903 := bstep (se 1 (by rfl) ⟨2821427, by rfl⟩ : syracuseStep 3761903 = 5642855) B5642855
theorem B1173831 : Blo 1172403 1173831 := bstep (se 1 (by rfl) ⟨880373, by rfl⟩ : syracuseStep 1173831 = 1760747) B1760747
theorem B5712383 : Blo 1172403 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B15034895 : Blo 1172403 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B8465057 : Blo 1172403 8465057 := bstep (se 2 (by rfl) ⟨3174396, by rfl⟩ : syracuseStep 8465057 = 6348793) B6348793
theorem B1174247 : Blo 1172403 1174247 := bstep (se 1 (by rfl) ⟨880685, by rfl⟩ : syracuseStep 1174247 = 1761371) B1761371
theorem B1174299 : Blo 1172403 1174299 := bstep (se 1 (by rfl) ⟨880724, by rfl⟩ : syracuseStep 1174299 = 1761449) B1761449
theorem B4451881 : Blo 1172403 4451881 := bstep (se 2 (by rfl) ⟨1669455, by rfl⟩ : syracuseStep 4451881 = 3338911) B3338911
theorem B21419437 : Blo 1172403 21419437 := bstep (se 3 (by rfl) ⟨4016144, by rfl⟩ : syracuseStep 21419437 = 8032289) B8032289
theorem B1980031 : Blo 1172403 1980031 := bstep (se 1 (by rfl) ⟨1485023, by rfl⟩ : syracuseStep 1980031 = 2970047) B2970047
theorem B1761275 : Blo 1172403 1761275 := bstep (se 1 (by rfl) ⟨1320956, by rfl⟩ : syracuseStep 1761275 = 2641913) B2641913
theorem B4454311 : Blo 1172403 4454311 := bstep (se 1 (by rfl) ⟨3340733, by rfl⟩ : syracuseStep 4454311 = 6681467) B6681467
theorem B1980895 : Blo 1172403 1980895 := bstep (se 1 (by rfl) ⟨1485671, by rfl⟩ : syracuseStep 1980895 = 2971343) B2971343
theorem B12679679 : Blo 1172403 12679679 := bstep (se 1 (by rfl) ⟨9509759, by rfl⟩ : syracuseStep 12679679 = 19019519) B19019519
theorem B2226943 : Blo 1172403 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B8035355 : Blo 1172403 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B4758905 : Blo 1172403 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B1760735 : Blo 1172403 1760735 := bstep (se 1 (by rfl) ⟨1320551, by rfl⟩ : syracuseStep 1760735 = 2641103) B2641103
theorem B5013049 : Blo 1172403 5013049 := bstep (se 2 (by rfl) ⟨1879893, by rfl⟩ : syracuseStep 5013049 = 3759787) B3759787
theorem B2227817 : Blo 1172403 2227817 := bstep (se 2 (by rfl) ⟨835431, by rfl⟩ : syracuseStep 2227817 = 1670863) B1670863
theorem B17137547 : Blo 1172403 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B6430631 : Blo 1172403 6430631 := bstep (se 1 (by rfl) ⟨4822973, by rfl⟩ : syracuseStep 6430631 = 9645947) B9645947
theorem B2818937 : Blo 1172403 2818937 := bstep (se 2 (by rfl) ⟨1057101, by rfl⟩ : syracuseStep 2818937 = 2114203) B2114203
theorem B2507935 : Blo 1172403 2507935 := bstep (se 1 (by rfl) ⟨1880951, by rfl⟩ : syracuseStep 2507935 = 3761903) B3761903
theorem B68593397 : Blo 1172403 68593397 := bstep (se 5 (by rfl) ⟨3215315, by rfl⟩ : syracuseStep 68593397 = 6430631) B6430631
theorem B28559249 : Blo 1172403 28559249 := bstep (se 2 (by rfl) ⟨10709718, by rfl⟩ : syracuseStep 28559249 = 21419437) B21419437
theorem B2640041 : Blo 1172403 2640041 := bstep (se 2 (by rfl) ⟨990015, by rfl⟩ : syracuseStep 2640041 = 1980031) B1980031
theorem B3172603 : Blo 1172403 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B1173823 : Blo 1172403 1173823 := bstep (se 1 (by rfl) ⟨880367, by rfl⟩ : syracuseStep 1173823 = 1760735) B1760735
theorem B1485211 : Blo 1172403 1485211 := bstep (se 1 (by rfl) ⟨1113908, by rfl⟩ : syracuseStep 1485211 = 2227817) B2227817
theorem B1174183 : Blo 1172403 1174183 := bstep (se 1 (by rfl) ⟨880637, by rfl⟩ : syracuseStep 1174183 = 1761275) B1761275
theorem B192785417 : Blo 1172403 192785417 := bstep (se 2 (by rfl) ⟨72294531, by rfl⟩ : syracuseStep 192785417 = 144589063) B144589063
theorem B2641193 : Blo 1172403 2641193 := bstep (se 2 (by rfl) ⟨990447, by rfl⟩ : syracuseStep 2641193 = 1980895) B1980895
theorem B2969257 : Blo 1172403 2969257 := bstep (se 2 (by rfl) ⟨1113471, by rfl⟩ : syracuseStep 2969257 = 2226943) B2226943
theorem B33812477 : Blo 1172403 33812477 := bstep (se 3 (by rfl) ⟨6339839, by rfl⟩ : syracuseStep 33812477 = 12679679) B12679679
theorem B5943293 : Blo 1172403 5943293 := bstep (se 3 (by rfl) ⟨1114367, by rfl⟩ : syracuseStep 5943293 = 2228735) B2228735
theorem B10023263 : Blo 1172403 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B16921001 : Blo 1172403 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B5935841 : Blo 1172403 5935841 := bstep (se 2 (by rfl) ⟨2225940, by rfl⟩ : syracuseStep 5935841 = 4451881) B4451881
theorem B11425031 : Blo 1172403 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B1759211 : Blo 1172403 1759211 := bstep (se 1 (by rfl) ⟨1319408, by rfl⟩ : syracuseStep 1759211 = 2638817) B2638817
theorem B38606975 : Blo 1172403 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B22288691 : Blo 1172403 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B8903033 : Blo 1172403 8903033 := bstep (se 2 (by rfl) ⟨3338637, by rfl⟩ : syracuseStep 8903033 = 6677275) B6677275
theorem B3808255 : Blo 1172403 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B5643371 : Blo 1172403 5643371 := bstep (se 1 (by rfl) ⟨4232528, by rfl⟩ : syracuseStep 5643371 = 8465057) B8465057
theorem B5356903 : Blo 1172403 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B6684065 : Blo 1172403 6684065 := bstep (se 2 (by rfl) ⟨2506524, by rfl⟩ : syracuseStep 6684065 = 5013049) B5013049
theorem B5939081 : Blo 1172403 5939081 := bstep (se 2 (by rfl) ⟨2227155, by rfl⟩ : syracuseStep 5939081 = 4454311) B4454311
theorem B11280667 : Blo 1172403 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B15048989 : Blo 1172403 15048989 := bstep (se 3 (by rfl) ⟨2821685, by rfl⟩ : syracuseStep 15048989 = 5643371) B5643371
theorem B3957227 : Blo 1172403 3957227 := bstep (se 1 (by rfl) ⟨2967920, by rfl⟩ : syracuseStep 3957227 = 5935841) B5935841
theorem B19039499 : Blo 1172403 19039499 := bstep (se 1 (by rfl) ⟨14279624, by rfl⟩ : syracuseStep 19039499 = 28559249) B28559249
theorem B1172807 : Blo 1172403 1172807 := bstep (se 1 (by rfl) ⟨879605, by rfl⟩ : syracuseStep 1172807 = 1759211) B1759211
theorem B3343913 : Blo 1172403 3343913 := bstep (se 2 (by rfl) ⟨1253967, by rfl⟩ : syracuseStep 3343913 = 2507935) B2507935
theorem B3959009 : Blo 1172403 3959009 := bstep (se 2 (by rfl) ⟨1484628, by rfl⟩ : syracuseStep 3959009 = 2969257) B2969257
theorem B731662901 : Blo 1172403 731662901 := bstep (se 5 (by rfl) ⟨34296698, by rfl⟩ : syracuseStep 731662901 = 68593397) B68593397
theorem B3959387 : Blo 1172403 3959387 := bstep (se 1 (by rfl) ⟨2969540, by rfl⟩ : syracuseStep 3959387 = 5939081) B5939081
theorem B4230137 : Blo 1172403 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B1879291 : Blo 1172403 1879291 := bstep (se 1 (by rfl) ⟨1409468, by rfl⟩ : syracuseStep 1879291 = 2818937) B2818937
theorem B59436509 : Blo 1172403 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B5935355 : Blo 1172403 5935355 := bstep (se 1 (by rfl) ⟨4451516, by rfl⟩ : syracuseStep 5935355 = 8903033) B8903033
theorem B22541651 : Blo 1172403 22541651 := bstep (se 1 (by rfl) ⟨16906238, by rfl⟩ : syracuseStep 22541651 = 33812477) B33812477
theorem B3962195 : Blo 1172403 3962195 := bstep (se 1 (by rfl) ⟨2971646, by rfl⟩ : syracuseStep 3962195 = 5943293) B5943293
theorem B6682175 : Blo 1172403 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B1980281 : Blo 1172403 1980281 := bstep (se 2 (by rfl) ⟨742605, by rfl⟩ : syracuseStep 1980281 = 1485211) B1485211
theorem B7616687 : Blo 1172403 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B5077673 : Blo 1172403 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B25737983 : Blo 1172403 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B1760027 : Blo 1172403 1760027 := bstep (se 1 (by rfl) ⟨1320020, by rfl⟩ : syracuseStep 1760027 = 2640041) B2640041
theorem B7142537 : Blo 1172403 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B128523611 : Blo 1172403 128523611 := bstep (se 1 (by rfl) ⟨96392708, by rfl⟩ : syracuseStep 128523611 = 192785417) B192785417
theorem B1760795 : Blo 1172403 1760795 := bstep (se 1 (by rfl) ⟨1320596, by rfl⟩ : syracuseStep 1760795 = 2641193) B2641193
theorem B4456043 : Blo 1172403 4456043 := bstep (se 1 (by rfl) ⟨3342032, by rfl⟩ : syracuseStep 4456043 = 6684065) B6684065
theorem B3956903 : Blo 1172403 3956903 := bstep (se 1 (by rfl) ⟨2967677, by rfl⟩ : syracuseStep 3956903 = 5935355) B5935355
theorem B2638151 : Blo 1172403 2638151 := bstep (se 1 (by rfl) ⟨1978613, by rfl⟩ : syracuseStep 2638151 = 3957227) B3957227
theorem B19046765 : Blo 1172403 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B15040889 : Blo 1172403 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B2229275 : Blo 1172403 2229275 := bstep (se 1 (by rfl) ⟨1671956, by rfl⟩ : syracuseStep 2229275 = 3343913) B3343913
theorem B1320187 : Blo 1172403 1320187 := bstep (se 1 (by rfl) ⟨990140, by rfl⟩ : syracuseStep 1320187 = 1980281) B1980281
theorem B2639339 : Blo 1172403 2639339 := bstep (se 1 (by rfl) ⟨1979504, by rfl⟩ : syracuseStep 2639339 = 3959009) B3959009
theorem B2639591 : Blo 1172403 2639591 := bstep (se 1 (by rfl) ⟨1979693, by rfl⟩ : syracuseStep 2639591 = 3959387) B3959387
theorem B3385115 : Blo 1172403 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B1173351 : Blo 1172403 1173351 := bstep (se 1 (by rfl) ⟨880013, by rfl⟩ : syracuseStep 1173351 = 1760027) B1760027
theorem B2820091 : Blo 1172403 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B85682407 : Blo 1172403 85682407 := bstep (se 1 (by rfl) ⟨64261805, by rfl⟩ : syracuseStep 85682407 = 128523611) B128523611
theorem B1173863 : Blo 1172403 1173863 := bstep (se 1 (by rfl) ⟨880397, by rfl⟩ : syracuseStep 1173863 = 1760795) B1760795
theorem B20311165 : Blo 1172403 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B12692999 : Blo 1172403 12692999 := bstep (se 1 (by rfl) ⟨9519749, by rfl⟩ : syracuseStep 12692999 = 19039499) B19039499
theorem B15027767 : Blo 1172403 15027767 := bstep (se 1 (by rfl) ⟨11270825, by rfl⟩ : syracuseStep 15027767 = 22541651) B22541651
theorem B2641463 : Blo 1172403 2641463 := bstep (se 1 (by rfl) ⟨1981097, by rfl⟩ : syracuseStep 2641463 = 3962195) B3962195
theorem B10022885 : Blo 1172403 10022885 := bstep (se 4 (by rfl) ⟨939645, by rfl⟩ : syracuseStep 10022885 = 1879291) B1879291
theorem B17158655 : Blo 1172403 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B2970695 : Blo 1172403 2970695 := bstep (se 1 (by rfl) ⟨2228021, by rfl⟩ : syracuseStep 2970695 = 4456043) B4456043
theorem B10032659 : Blo 1172403 10032659 := bstep (se 1 (by rfl) ⟨7524494, by rfl⟩ : syracuseStep 10032659 = 15048989) B15048989
theorem B4454783 : Blo 1172403 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B158497357 : Blo 1172403 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B487775267 : Blo 1172403 487775267 := bstep (se 1 (by rfl) ⟨365831450, by rfl⟩ : syracuseStep 487775267 = 731662901) B731662901
theorem B2637935 : Blo 1172403 2637935 := bstep (se 1 (by rfl) ⟨1978451, by rfl⟩ : syracuseStep 2637935 = 3956903) B3956903
theorem B12697843 : Blo 1172403 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B10027259 : Blo 1172403 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B211329809 : Blo 1172403 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B325183511 : Blo 1172403 325183511 := bstep (se 1 (by rfl) ⟨243887633, by rfl⟩ : syracuseStep 325183511 = 487775267) B487775267
theorem B3760121 : Blo 1172403 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B1486183 : Blo 1172403 1486183 := bstep (se 1 (by rfl) ⟨1114637, by rfl⟩ : syracuseStep 1486183 = 2229275) B2229275
theorem B6688439 : Blo 1172403 6688439 := bstep (se 1 (by rfl) ⟨5016329, by rfl⟩ : syracuseStep 6688439 = 10032659) B10032659
theorem B2256743 : Blo 1172403 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B45756413 : Blo 1172403 45756413 := bstep (se 3 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 45756413 = 17158655) B17158655
theorem B2969855 : Blo 1172403 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B6681923 : Blo 1172403 6681923 := bstep (se 1 (by rfl) ⟨5011442, by rfl⟩ : syracuseStep 6681923 = 10022885) B10022885
theorem B1758767 : Blo 1172403 1758767 := bstep (se 1 (by rfl) ⟨1319075, by rfl⟩ : syracuseStep 1758767 = 2638151) B2638151
theorem B114243209 : Blo 1172403 114243209 := bstep (se 2 (by rfl) ⟨42841203, by rfl⟩ : syracuseStep 114243209 = 85682407) B85682407
theorem B1980463 : Blo 1172403 1980463 := bstep (se 1 (by rfl) ⟨1485347, by rfl⟩ : syracuseStep 1980463 = 2970695) B2970695
theorem B1759559 : Blo 1172403 1759559 := bstep (se 1 (by rfl) ⟨1319669, by rfl⟩ : syracuseStep 1759559 = 2639339) B2639339
theorem B1759727 : Blo 1172403 1759727 := bstep (se 1 (by rfl) ⟨1319795, by rfl⟩ : syracuseStep 1759727 = 2639591) B2639591
theorem B27081553 : Blo 1172403 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B1760249 : Blo 1172403 1760249 := bstep (se 2 (by rfl) ⟨660093, by rfl⟩ : syracuseStep 1760249 = 1320187) B1320187
theorem B8461999 : Blo 1172403 8461999 := bstep (se 1 (by rfl) ⟨6346499, by rfl⟩ : syracuseStep 8461999 = 12692999) B12692999
theorem B10018511 : Blo 1172403 10018511 := bstep (se 1 (by rfl) ⟨7513883, by rfl⟩ : syracuseStep 10018511 = 15027767) B15027767
theorem B1760975 : Blo 1172403 1760975 := bstep (se 1 (by rfl) ⟨1320731, by rfl⟩ : syracuseStep 1760975 = 2641463) B2641463
theorem B6684839 : Blo 1172403 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B140886539 : Blo 1172403 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B1172511 : Blo 1172403 1172511 := bstep (se 1 (by rfl) ⟨879383, by rfl⟩ : syracuseStep 1172511 = 1758767) B1758767
theorem B76162139 : Blo 1172403 76162139 := bstep (se 1 (by rfl) ⟨57121604, by rfl⟩ : syracuseStep 76162139 = 114243209) B114243209
theorem B1173039 : Blo 1172403 1173039 := bstep (se 1 (by rfl) ⟨879779, by rfl⟩ : syracuseStep 1173039 = 1759559) B1759559
theorem B1173151 : Blo 1172403 1173151 := bstep (se 1 (by rfl) ⟨879863, by rfl⟩ : syracuseStep 1173151 = 1759727) B1759727
theorem B1173499 : Blo 1172403 1173499 := bstep (se 1 (by rfl) ⟨880124, by rfl⟩ : syracuseStep 1173499 = 1760249) B1760249
theorem B11282665 : Blo 1172403 11282665 := bstep (se 2 (by rfl) ⟨4230999, by rfl⟩ : syracuseStep 11282665 = 8461999) B8461999
theorem B4458959 : Blo 1172403 4458959 := bstep (se 1 (by rfl) ⟨3344219, by rfl⟩ : syracuseStep 4458959 = 6688439) B6688439
theorem B6679007 : Blo 1172403 6679007 := bstep (se 1 (by rfl) ⟨5009255, by rfl⟩ : syracuseStep 6679007 = 10018511) B10018511
theorem B1173983 : Blo 1172403 1173983 := bstep (se 1 (by rfl) ⟨880487, by rfl⟩ : syracuseStep 1173983 = 1760975) B1760975
theorem B2640617 : Blo 1172403 2640617 := bstep (se 2 (by rfl) ⟨990231, by rfl⟩ : syracuseStep 2640617 = 1980463) B1980463
theorem B216789007 : Blo 1172403 216789007 := bstep (se 1 (by rfl) ⟨162591755, by rfl⟩ : syracuseStep 216789007 = 325183511) B325183511
theorem B2506747 : Blo 1172403 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B1504495 : Blo 1172403 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B30504275 : Blo 1172403 30504275 := bstep (se 1 (by rfl) ⟨22878206, by rfl⟩ : syracuseStep 30504275 = 45756413) B45756413
theorem B1758623 : Blo 1172403 1758623 := bstep (se 1 (by rfl) ⟨1318967, by rfl⟩ : syracuseStep 1758623 = 2637935) B2637935
theorem B1979903 : Blo 1172403 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B16930457 : Blo 1172403 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B4454615 : Blo 1172403 4454615 := bstep (se 1 (by rfl) ⟨3340961, by rfl⟩ : syracuseStep 4454615 = 6681923) B6681923
theorem B36108737 : Blo 1172403 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B1981577 : Blo 1172403 1981577 := bstep (se 2 (by rfl) ⟨743091, by rfl⟩ : syracuseStep 1981577 = 1486183) B1486183
theorem B4456559 : Blo 1172403 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B50774759 : Blo 1172403 50774759 := bstep (se 1 (by rfl) ⟨38081069, by rfl⟩ : syracuseStep 50774759 = 76162139) B76162139
theorem B1172415 : Blo 1172403 1172415 := bstep (se 1 (by rfl) ⟨879311, by rfl⟩ : syracuseStep 1172415 = 1758623) B1758623
theorem B1319935 : Blo 1172403 1319935 := bstep (se 1 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 1319935 = 1979903) B1979903
theorem B1321051 : Blo 1172403 1321051 := bstep (se 1 (by rfl) ⟨990788, by rfl⟩ : syracuseStep 1321051 = 1981577) B1981577
theorem B15043553 : Blo 1172403 15043553 := bstep (se 2 (by rfl) ⟨5641332, by rfl⟩ : syracuseStep 15043553 = 11282665) B11282665
theorem B93924359 : Blo 1172403 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B20336183 : Blo 1172403 20336183 := bstep (se 1 (by rfl) ⟨15252137, by rfl⟩ : syracuseStep 20336183 = 30504275) B30504275
theorem B2969743 : Blo 1172403 2969743 := bstep (se 1 (by rfl) ⟨2227307, by rfl⟩ : syracuseStep 2969743 = 4454615) B4454615
theorem B24072491 : Blo 1172403 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B4452671 : Blo 1172403 4452671 := bstep (se 1 (by rfl) ⟨3339503, by rfl⟩ : syracuseStep 4452671 = 6679007) B6679007
theorem B289052009 : Blo 1172403 289052009 := bstep (se 2 (by rfl) ⟨108394503, by rfl⟩ : syracuseStep 289052009 = 216789007) B216789007
theorem B11286971 : Blo 1172403 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B2972639 : Blo 1172403 2972639 := bstep (se 1 (by rfl) ⟨2229479, by rfl⟩ : syracuseStep 2972639 = 4458959) B4458959
theorem B2005993 : Blo 1172403 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B1760411 : Blo 1172403 1760411 := bstep (se 1 (by rfl) ⟨1320308, by rfl⟩ : syracuseStep 1760411 = 2640617) B2640617
theorem B3342329 : Blo 1172403 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B1761401 : Blo 1172403 1761401 := bstep (se 2 (by rfl) ⟨660525, by rfl⟩ : syracuseStep 1761401 = 1321051) B1321051
theorem B16048327 : Blo 1172403 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B33849839 : Blo 1172403 33849839 := bstep (se 1 (by rfl) ⟨25387379, by rfl⟩ : syracuseStep 33849839 = 50774759) B50774759
theorem B192701339 : Blo 1172403 192701339 := bstep (se 1 (by rfl) ⟨144526004, by rfl⟩ : syracuseStep 192701339 = 289052009) B289052009
theorem B10029035 : Blo 1172403 10029035 := bstep (se 1 (by rfl) ⟨7521776, by rfl⟩ : syracuseStep 10029035 = 15043553) B15043553
theorem B1173607 : Blo 1172403 1173607 := bstep (se 1 (by rfl) ⟨880205, by rfl⟩ : syracuseStep 1173607 = 1760411) B1760411
theorem B3959657 : Blo 1172403 3959657 := bstep (se 2 (by rfl) ⟨1484871, by rfl⟩ : syracuseStep 3959657 = 2969743) B2969743
theorem B2968447 : Blo 1172403 2968447 := bstep (se 1 (by rfl) ⟨2226335, by rfl⟩ : syracuseStep 2968447 = 4452671) B4452671
theorem B2674657 : Blo 1172403 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B7524647 : Blo 1172403 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B62616239 : Blo 1172403 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B2971039 : Blo 1172403 2971039 := bstep (se 1 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 2971039 = 4456559) B4456559
theorem B1759913 : Blo 1172403 1759913 := bstep (se 2 (by rfl) ⟨659967, by rfl⟩ : syracuseStep 1759913 = 1319935) B1319935
theorem B1981759 : Blo 1172403 1981759 := bstep (se 1 (by rfl) ⟨1486319, by rfl⟩ : syracuseStep 1981759 = 2972639) B2972639
theorem B13557455 : Blo 1172403 13557455 := bstep (se 1 (by rfl) ⟨10168091, by rfl⟩ : syracuseStep 13557455 = 20336183) B20336183
theorem B2228219 : Blo 1172403 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B21397769 : Blo 1172403 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B128467559 : Blo 1172403 128467559 := bstep (se 1 (by rfl) ⟨96350669, by rfl⟩ : syracuseStep 128467559 = 192701339) B192701339
theorem B3957929 : Blo 1172403 3957929 := bstep (se 2 (by rfl) ⟨1484223, by rfl⟩ : syracuseStep 3957929 = 2968447) B2968447
theorem B6686023 : Blo 1172403 6686023 := bstep (se 1 (by rfl) ⟨5014517, by rfl⟩ : syracuseStep 6686023 = 10029035) B10029035
theorem B1173275 : Blo 1172403 1173275 := bstep (se 1 (by rfl) ⟨879956, by rfl⟩ : syracuseStep 1173275 = 1759913) B1759913
theorem B2639771 : Blo 1172403 2639771 := bstep (se 1 (by rfl) ⟨1979828, by rfl⟩ : syracuseStep 2639771 = 3959657) B3959657
theorem B9038303 : Blo 1172403 9038303 := bstep (se 1 (by rfl) ⟨6778727, by rfl⟩ : syracuseStep 9038303 = 13557455) B13557455
theorem B3566209 : Blo 1172403 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B1485479 : Blo 1172403 1485479 := bstep (se 1 (by rfl) ⟨1114109, by rfl⟩ : syracuseStep 1485479 = 2228219) B2228219
theorem B1174267 : Blo 1172403 1174267 := bstep (se 1 (by rfl) ⟨880700, by rfl⟩ : syracuseStep 1174267 = 1761401) B1761401
theorem B5016431 : Blo 1172403 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B2642345 : Blo 1172403 2642345 := bstep (se 2 (by rfl) ⟨990879, by rfl⟩ : syracuseStep 2642345 = 1981759) B1981759
theorem B3961385 : Blo 1172403 3961385 := bstep (se 2 (by rfl) ⟨1485519, by rfl⟩ : syracuseStep 3961385 = 2971039) B2971039
theorem B22566559 : Blo 1172403 22566559 := bstep (se 1 (by rfl) ⟨16924919, by rfl⟩ : syracuseStep 22566559 = 33849839) B33849839
theorem B41744159 : Blo 1172403 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B1761563 : Blo 1172403 1761563 := bstep (se 1 (by rfl) ⟨1321172, by rfl⟩ : syracuseStep 1761563 = 2642345) B2642345
theorem B2638619 : Blo 1172403 2638619 := bstep (se 1 (by rfl) ⟨1978964, by rfl⟩ : syracuseStep 2638619 = 3957929) B3957929
theorem B27829439 : Blo 1172403 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B8914697 : Blo 1172403 8914697 := bstep (se 2 (by rfl) ⟨3343011, by rfl⟩ : syracuseStep 8914697 = 6686023) B6686023
theorem B14265179 : Blo 1172403 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B2640923 : Blo 1172403 2640923 := bstep (se 1 (by rfl) ⟨1980692, by rfl⟩ : syracuseStep 2640923 = 3961385) B3961385
theorem B4754945 : Blo 1172403 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B6025535 : Blo 1172403 6025535 := bstep (se 1 (by rfl) ⟨4519151, by rfl⟩ : syracuseStep 6025535 = 9038303) B9038303
theorem B3961277 : Blo 1172403 3961277 := bstep (se 3 (by rfl) ⟨742739, by rfl⟩ : syracuseStep 3961277 = 1485479) B1485479
theorem B85645039 : Blo 1172403 85645039 := bstep (se 1 (by rfl) ⟨64233779, by rfl⟩ : syracuseStep 85645039 = 128467559) B128467559
theorem B1759847 : Blo 1172403 1759847 := bstep (se 1 (by rfl) ⟨1319885, by rfl⟩ : syracuseStep 1759847 = 2639771) B2639771
theorem B30088745 : Blo 1172403 30088745 := bstep (se 2 (by rfl) ⟨11283279, by rfl⟩ : syracuseStep 30088745 = 22566559) B22566559
theorem B13377149 : Blo 1172403 13377149 := bstep (se 3 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 13377149 = 5016431) B5016431
theorem B1173231 : Blo 1172403 1173231 := bstep (se 1 (by rfl) ⟨879923, by rfl⟩ : syracuseStep 1173231 = 1759847) B1759847
theorem B1174375 : Blo 1172403 1174375 := bstep (se 1 (by rfl) ⟨880781, by rfl⟩ : syracuseStep 1174375 = 1761563) B1761563
theorem B4017023 : Blo 1172403 4017023 := bstep (se 1 (by rfl) ⟨3012767, by rfl⟩ : syracuseStep 4017023 = 6025535) B6025535
theorem B2640851 : Blo 1172403 2640851 := bstep (se 1 (by rfl) ⟨1980638, by rfl⟩ : syracuseStep 2640851 = 3961277) B3961277
theorem B5943131 : Blo 1172403 5943131 := bstep (se 1 (by rfl) ⟨4457348, by rfl⟩ : syracuseStep 5943131 = 8914697) B8914697
theorem B114193385 : Blo 1172403 114193385 := bstep (se 2 (by rfl) ⟨42822519, by rfl⟩ : syracuseStep 114193385 = 85645039) B85645039
theorem B20059163 : Blo 1172403 20059163 := bstep (se 1 (by rfl) ⟨15044372, by rfl⟩ : syracuseStep 20059163 = 30088745) B30088745
theorem B8918099 : Blo 1172403 8918099 := bstep (se 1 (by rfl) ⟨6688574, by rfl⟩ : syracuseStep 8918099 = 13377149) B13377149
theorem B1759079 : Blo 1172403 1759079 := bstep (se 1 (by rfl) ⟨1319309, by rfl⟩ : syracuseStep 1759079 = 2638619) B2638619
theorem B18552959 : Blo 1172403 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B9510119 : Blo 1172403 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B1760615 : Blo 1172403 1760615 := bstep (se 1 (by rfl) ⟨1320461, by rfl⟩ : syracuseStep 1760615 = 2640923) B2640923
theorem B3169963 : Blo 1172403 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B76128923 : Blo 1172403 76128923 := bstep (se 1 (by rfl) ⟨57096692, by rfl⟩ : syracuseStep 76128923 = 114193385) B114193385
theorem B1172719 : Blo 1172403 1172719 := bstep (se 1 (by rfl) ⟨879539, by rfl⟩ : syracuseStep 1172719 = 1759079) B1759079
theorem B1173743 : Blo 1172403 1173743 := bstep (se 1 (by rfl) ⟨880307, by rfl⟩ : syracuseStep 1173743 = 1760615) B1760615
theorem B13372775 : Blo 1172403 13372775 := bstep (se 1 (by rfl) ⟨10029581, by rfl⟩ : syracuseStep 13372775 = 20059163) B20059163
theorem B3962087 : Blo 1172403 3962087 := bstep (se 1 (by rfl) ⟨2971565, by rfl⟩ : syracuseStep 3962087 = 5943131) B5943131
theorem B5945399 : Blo 1172403 5945399 := bstep (se 1 (by rfl) ⟨4459049, by rfl⟩ : syracuseStep 5945399 = 8918099) B8918099
theorem B12368639 : Blo 1172403 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B2678015 : Blo 1172403 2678015 := bstep (se 1 (by rfl) ⟨2008511, by rfl⟩ : syracuseStep 2678015 = 4017023) B4017023
theorem B1760567 : Blo 1172403 1760567 := bstep (se 1 (by rfl) ⟨1320425, by rfl⟩ : syracuseStep 1760567 = 2640851) B2640851
theorem B6340079 : Blo 1172403 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B4226617 : Blo 1172403 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B32983037 : Blo 1172403 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B1173711 : Blo 1172403 1173711 := bstep (se 1 (by rfl) ⟨880283, by rfl⟩ : syracuseStep 1173711 = 1760567) B1760567
theorem B8915183 : Blo 1172403 8915183 := bstep (se 1 (by rfl) ⟨6686387, by rfl⟩ : syracuseStep 8915183 = 13372775) B13372775
theorem B50752615 : Blo 1172403 50752615 := bstep (se 1 (by rfl) ⟨38064461, by rfl⟩ : syracuseStep 50752615 = 76128923) B76128923
theorem B2641391 : Blo 1172403 2641391 := bstep (se 1 (by rfl) ⟨1981043, by rfl⟩ : syracuseStep 2641391 = 3962087) B3962087
theorem B16906877 : Blo 1172403 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B3963599 : Blo 1172403 3963599 := bstep (se 1 (by rfl) ⟨2972699, by rfl⟩ : syracuseStep 3963599 = 5945399) B5945399
theorem B5635489 : Blo 1172403 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B1785343 : Blo 1172403 1785343 := bstep (se 1 (by rfl) ⟨1339007, by rfl⟩ : syracuseStep 1785343 = 2678015) B2678015
theorem B21988691 : Blo 1172403 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B7513985 : Blo 1172403 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B67670153 : Blo 1172403 67670153 := bstep (se 2 (by rfl) ⟨25376307, by rfl⟩ : syracuseStep 67670153 = 50752615) B50752615
theorem B5943455 : Blo 1172403 5943455 := bstep (se 1 (by rfl) ⟨4457591, by rfl⟩ : syracuseStep 5943455 = 8915183) B8915183
theorem B2642399 : Blo 1172403 2642399 := bstep (se 1 (by rfl) ⟨1981799, by rfl⟩ : syracuseStep 2642399 = 3963599) B3963599
theorem B2380457 : Blo 1172403 2380457 := bstep (se 2 (by rfl) ⟨892671, by rfl⟩ : syracuseStep 2380457 = 1785343) B1785343
theorem B11271251 : Blo 1172403 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B1760927 : Blo 1172403 1760927 := bstep (se 1 (by rfl) ⟨1320695, by rfl⟩ : syracuseStep 1760927 = 2641391) B2641391
theorem B45113435 : Blo 1172403 45113435 := bstep (se 1 (by rfl) ⟨33835076, by rfl⟩ : syracuseStep 45113435 = 67670153) B67670153
theorem B1761599 : Blo 1172403 1761599 := bstep (se 1 (by rfl) ⟨1321199, by rfl⟩ : syracuseStep 1761599 = 2642399) B2642399
theorem B7514167 : Blo 1172403 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B1173951 : Blo 1172403 1173951 := bstep (se 1 (by rfl) ⟨880463, by rfl⟩ : syracuseStep 1173951 = 1760927) B1760927
theorem B14659127 : Blo 1172403 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B3962303 : Blo 1172403 3962303 := bstep (se 1 (by rfl) ⟨2971727, by rfl⟩ : syracuseStep 3962303 = 5943455) B5943455
theorem B1586971 : Blo 1172403 1586971 := bstep (se 1 (by rfl) ⟨1190228, by rfl⟩ : syracuseStep 1586971 = 2380457) B2380457
theorem B20037293 : Blo 1172403 20037293 := bstep (se 3 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 20037293 = 7513985) B7513985
theorem B10018889 : Blo 1172403 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B8463845 : Blo 1172403 8463845 := bstep (se 4 (by rfl) ⟨793485, by rfl⟩ : syracuseStep 8463845 = 1586971) B1586971
theorem B30075623 : Blo 1172403 30075623 := bstep (se 1 (by rfl) ⟨22556717, by rfl⟩ : syracuseStep 30075623 = 45113435) B45113435
theorem B1174399 : Blo 1172403 1174399 := bstep (se 1 (by rfl) ⟨880799, by rfl⟩ : syracuseStep 1174399 = 1761599) B1761599
theorem B2641535 : Blo 1172403 2641535 := bstep (se 1 (by rfl) ⟨1981151, by rfl⟩ : syracuseStep 2641535 = 3962303) B3962303
theorem B13358195 : Blo 1172403 13358195 := bstep (se 1 (by rfl) ⟨10018646, by rfl⟩ : syracuseStep 13358195 = 20037293) B20037293
theorem B9772751 : Blo 1172403 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B8905463 : Blo 1172403 8905463 := bstep (se 1 (by rfl) ⟨6679097, by rfl⟩ : syracuseStep 8905463 = 13358195) B13358195
theorem B26060669 : Blo 1172403 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B6679259 : Blo 1172403 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B20050415 : Blo 1172403 20050415 := bstep (se 1 (by rfl) ⟨15037811, by rfl⟩ : syracuseStep 20050415 = 30075623) B30075623
theorem B5642563 : Blo 1172403 5642563 := bstep (se 1 (by rfl) ⟨4231922, by rfl⟩ : syracuseStep 5642563 = 8463845) B8463845
theorem B1761023 : Blo 1172403 1761023 := bstep (se 1 (by rfl) ⟨1320767, by rfl⟩ : syracuseStep 1761023 = 2641535) B2641535
theorem B1174015 : Blo 1172403 1174015 := bstep (se 1 (by rfl) ⟨880511, by rfl⟩ : syracuseStep 1174015 = 1761023) B1761023
theorem B7523417 : Blo 1172403 7523417 := bstep (se 2 (by rfl) ⟨2821281, by rfl⟩ : syracuseStep 7523417 = 5642563) B5642563
theorem B4452839 : Blo 1172403 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B13366943 : Blo 1172403 13366943 := bstep (se 1 (by rfl) ⟨10025207, by rfl⟩ : syracuseStep 13366943 = 20050415) B20050415
theorem B5936975 : Blo 1172403 5936975 := bstep (se 1 (by rfl) ⟨4452731, by rfl⟩ : syracuseStep 5936975 = 8905463) B8905463
theorem B17373779 : Blo 1172403 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B3957983 : Blo 1172403 3957983 := bstep (se 1 (by rfl) ⟨2968487, by rfl⟩ : syracuseStep 3957983 = 5936975) B5936975
theorem B5015611 : Blo 1172403 5015611 := bstep (se 1 (by rfl) ⟨3761708, by rfl⟩ : syracuseStep 5015611 = 7523417) B7523417
theorem B2968559 : Blo 1172403 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B8911295 : Blo 1172403 8911295 := bstep (se 1 (by rfl) ⟨6683471, by rfl⟩ : syracuseStep 8911295 = 13366943) B13366943
theorem B11582519 : Blo 1172403 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B2638655 : Blo 1172403 2638655 := bstep (se 1 (by rfl) ⟨1978991, by rfl⟩ : syracuseStep 2638655 = 3957983) B3957983
theorem B5940863 : Blo 1172403 5940863 := bstep (se 1 (by rfl) ⟨4455647, by rfl⟩ : syracuseStep 5940863 = 8911295) B8911295
theorem B6687481 : Blo 1172403 6687481 := bstep (se 2 (by rfl) ⟨2507805, by rfl⟩ : syracuseStep 6687481 = 5015611) B5015611
theorem B123546869 : Blo 1172403 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B1979039 : Blo 1172403 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B1319359 : Blo 1172403 1319359 := bstep (se 1 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 1319359 = 1979039) B1979039
theorem B82364579 : Blo 1172403 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B8916641 : Blo 1172403 8916641 := bstep (se 2 (by rfl) ⟨3343740, by rfl⟩ : syracuseStep 8916641 = 6687481) B6687481
theorem B3960575 : Blo 1172403 3960575 := bstep (se 1 (by rfl) ⟨2970431, by rfl⟩ : syracuseStep 3960575 = 5940863) B5940863
theorem B1759103 : Blo 1172403 1759103 := bstep (se 1 (by rfl) ⟨1319327, by rfl⟩ : syracuseStep 1759103 = 2638655) B2638655
theorem B1172735 : Blo 1172403 1172735 := bstep (se 1 (by rfl) ⟨879551, by rfl⟩ : syracuseStep 1172735 = 1759103) B1759103
theorem B2640383 : Blo 1172403 2640383 := bstep (se 1 (by rfl) ⟨1980287, by rfl⟩ : syracuseStep 2640383 = 3960575) B3960575
theorem B5944427 : Blo 1172403 5944427 := bstep (se 1 (by rfl) ⟨4458320, by rfl⟩ : syracuseStep 5944427 = 8916641) B8916641
theorem B1759145 : Blo 1172403 1759145 := bstep (se 2 (by rfl) ⟨659679, by rfl⟩ : syracuseStep 1759145 = 1319359) B1319359
theorem B54909719 : Blo 1172403 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B1172763 : Blo 1172403 1172763 := bstep (se 1 (by rfl) ⟨879572, by rfl⟩ : syracuseStep 1172763 = 1759145) B1759145
theorem B36606479 : Blo 1172403 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B3962951 : Blo 1172403 3962951 := bstep (se 1 (by rfl) ⟨2972213, by rfl⟩ : syracuseStep 3962951 = 5944427) B5944427
theorem B1760255 : Blo 1172403 1760255 := bstep (se 1 (by rfl) ⟨1320191, by rfl⟩ : syracuseStep 1760255 = 2640383) B2640383
theorem B97617277 : Blo 1172403 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B1173503 : Blo 1172403 1173503 := bstep (se 1 (by rfl) ⟨880127, by rfl⟩ : syracuseStep 1173503 = 1760255) B1760255
theorem B2641967 : Blo 1172403 2641967 := bstep (se 1 (by rfl) ⟨1981475, by rfl⟩ : syracuseStep 2641967 = 3962951) B3962951
theorem B1761311 : Blo 1172403 1761311 := bstep (se 1 (by rfl) ⟨1320983, by rfl⟩ : syracuseStep 1761311 = 2641967) B2641967
theorem B520625477 : Blo 1172403 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B1174207 : Blo 1172403 1174207 := bstep (se 1 (by rfl) ⟨880655, by rfl⟩ : syracuseStep 1174207 = 1761311) B1761311
theorem B347083651 : Blo 1172403 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B462778201 : Blo 1172403 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B617037601 : Blo 1172403 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B822716801 : Blo 1172403 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B548477867 : Blo 1172403 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B365651911 : Blo 1172403 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B487535881 : Blo 1172403 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B650047841 : Blo 1172403 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 1172403 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B288910151 : Blo 1172403 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B192606767 : Blo 1172403 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B128404511 : Blo 1172403 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B85603007 : Blo 1172403 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B57068671 : Blo 1172403 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B76091561 : Blo 1172403 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B50727707 : Blo 1172403 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B33818471 : Blo 1172403 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B22545647 : Blo 1172403 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B15030431 : Blo 1172403 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B10020287 : Blo 1172403 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B6680191 : Blo 1172403 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B8906921 : Blo 1172403 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 1172403 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B3958631 : Blo 1172403 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 1172403 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B1759391 : Blo 1172403 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B1172927 : Blo 1172403 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391

theorem C0 (j : ℕ) (h1 : 293100 ≤ j) (h2 : j ≤ 293600) : Blo 1172403 (4 * j + 3) := by
  interval_cases j
  · exact B1172403
  · exact B1172407
  · exact B1172411
  · exact B1172415
  · exact B1172419
  · exact B1172423
  · exact B1172427
  · exact B1172431
  · exact B1172435
  · exact B1172439
  · exact B1172443
  · exact B1172447
  · exact B1172451
  · exact B1172455
  · exact B1172459
  · exact B1172463
  · exact B1172467
  · exact B1172471
  · exact B1172475
  · exact B1172479
  · exact B1172483
  · exact B1172487
  · exact B1172491
  · exact B1172495
  · exact B1172499
  · exact B1172503
  · exact B1172507
  · exact B1172511
  · exact B1172515
  · exact B1172519
  · exact B1172523
  · exact B1172527
  · exact B1172531
  · exact B1172535
  · exact B1172539
  · exact B1172543
  · exact B1172547
  · exact B1172551
  · exact B1172555
  · exact B1172559
  · exact B1172563
  · exact B1172567
  · exact B1172571
  · exact B1172575
  · exact B1172579
  · exact B1172583
  · exact B1172587
  · exact B1172591
  · exact B1172595
  · exact B1172599
  · exact B1172603
  · exact B1172607
  · exact B1172611
  · exact B1172615
  · exact B1172619
  · exact B1172623
  · exact B1172627
  · exact B1172631
  · exact B1172635
  · exact B1172639
  · exact B1172643
  · exact B1172647
  · exact B1172651
  · exact B1172655
  · exact B1172659
  · exact B1172663
  · exact B1172667
  · exact B1172671
  · exact B1172675
  · exact B1172679
  · exact B1172683
  · exact B1172687
  · exact B1172691
  · exact B1172695
  · exact B1172699
  · exact B1172703
  · exact B1172707
  · exact B1172711
  · exact B1172715
  · exact B1172719
  · exact B1172723
  · exact B1172727
  · exact B1172731
  · exact B1172735
  · exact B1172739
  · exact B1172743
  · exact B1172747
  · exact B1172751
  · exact B1172755
  · exact B1172759
  · exact B1172763
  · exact B1172767
  · exact B1172771
  · exact B1172775
  · exact B1172779
  · exact B1172783
  · exact B1172787
  · exact B1172791
  · exact B1172795
  · exact B1172799
  · exact B1172803
  · exact B1172807
  · exact B1172811
  · exact B1172815
  · exact B1172819
  · exact B1172823
  · exact B1172827
  · exact B1172831
  · exact B1172835
  · exact B1172839
  · exact B1172843
  · exact B1172847
  · exact B1172851
  · exact B1172855
  · exact B1172859
  · exact B1172863
  · exact B1172867
  · exact B1172871
  · exact B1172875
  · exact B1172879
  · exact B1172883
  · exact B1172887
  · exact B1172891
  · exact B1172895
  · exact B1172899
  · exact B1172903
  · exact B1172907
  · exact B1172911
  · exact B1172915
  · exact B1172919
  · exact B1172923
  · exact B1172927
  · exact B1172931
  · exact B1172935
  · exact B1172939
  · exact B1172943
  · exact B1172947
  · exact B1172951
  · exact B1172955
  · exact B1172959
  · exact B1172963
  · exact B1172967
  · exact B1172971
  · exact B1172975
  · exact B1172979
  · exact B1172983
  · exact B1172987
  · exact B1172991
  · exact B1172995
  · exact B1172999
  · exact B1173003
  · exact B1173007
  · exact B1173011
  · exact B1173015
  · exact B1173019
  · exact B1173023
  · exact B1173027
  · exact B1173031
  · exact B1173035
  · exact B1173039
  · exact B1173043
  · exact B1173047
  · exact B1173051
  · exact B1173055
  · exact B1173059
  · exact B1173063
  · exact B1173067
  · exact B1173071
  · exact B1173075
  · exact B1173079
  · exact B1173083
  · exact B1173087
  · exact B1173091
  · exact B1173095
  · exact B1173099
  · exact B1173103
  · exact B1173107
  · exact B1173111
  · exact B1173115
  · exact B1173119
  · exact B1173123
  · exact B1173127
  · exact B1173131
  · exact B1173135
  · exact B1173139
  · exact B1173143
  · exact B1173147
  · exact B1173151
  · exact B1173155
  · exact B1173159
  · exact B1173163
  · exact B1173167
  · exact B1173171
  · exact B1173175
  · exact B1173179
  · exact B1173183
  · exact B1173187
  · exact B1173191
  · exact B1173195
  · exact B1173199
  · exact B1173203
  · exact B1173207
  · exact B1173211
  · exact B1173215
  · exact B1173219
  · exact B1173223
  · exact B1173227
  · exact B1173231
  · exact B1173235
  · exact B1173239
  · exact B1173243
  · exact B1173247
  · exact B1173251
  · exact B1173255
  · exact B1173259
  · exact B1173263
  · exact B1173267
  · exact B1173271
  · exact B1173275
  · exact B1173279
  · exact B1173283
  · exact B1173287
  · exact B1173291
  · exact B1173295
  · exact B1173299
  · exact B1173303
  · exact B1173307
  · exact B1173311
  · exact B1173315
  · exact B1173319
  · exact B1173323
  · exact B1173327
  · exact B1173331
  · exact B1173335
  · exact B1173339
  · exact B1173343
  · exact B1173347
  · exact B1173351
  · exact B1173355
  · exact B1173359
  · exact B1173363
  · exact B1173367
  · exact B1173371
  · exact B1173375
  · exact B1173379
  · exact B1173383
  · exact B1173387
  · exact B1173391
  · exact B1173395
  · exact B1173399
  · exact B1173403
  · exact B1173407
  · exact B1173411
  · exact B1173415
  · exact B1173419
  · exact B1173423
  · exact B1173427
  · exact B1173431
  · exact B1173435
  · exact B1173439
  · exact B1173443
  · exact B1173447
  · exact B1173451
  · exact B1173455
  · exact B1173459
  · exact B1173463
  · exact B1173467
  · exact B1173471
  · exact B1173475
  · exact B1173479
  · exact B1173483
  · exact B1173487
  · exact B1173491
  · exact B1173495
  · exact B1173499
  · exact B1173503
  · exact B1173507
  · exact B1173511
  · exact B1173515
  · exact B1173519
  · exact B1173523
  · exact B1173527
  · exact B1173531
  · exact B1173535
  · exact B1173539
  · exact B1173543
  · exact B1173547
  · exact B1173551
  · exact B1173555
  · exact B1173559
  · exact B1173563
  · exact B1173567
  · exact B1173571
  · exact B1173575
  · exact B1173579
  · exact B1173583
  · exact B1173587
  · exact B1173591
  · exact B1173595
  · exact B1173599
  · exact B1173603
  · exact B1173607
  · exact B1173611
  · exact B1173615
  · exact B1173619
  · exact B1173623
  · exact B1173627
  · exact B1173631
  · exact B1173635
  · exact B1173639
  · exact B1173643
  · exact B1173647
  · exact B1173651
  · exact B1173655
  · exact B1173659
  · exact B1173663
  · exact B1173667
  · exact B1173671
  · exact B1173675
  · exact B1173679
  · exact B1173683
  · exact B1173687
  · exact B1173691
  · exact B1173695
  · exact B1173699
  · exact B1173703
  · exact B1173707
  · exact B1173711
  · exact B1173715
  · exact B1173719
  · exact B1173723
  · exact B1173727
  · exact B1173731
  · exact B1173735
  · exact B1173739
  · exact B1173743
  · exact B1173747
  · exact B1173751
  · exact B1173755
  · exact B1173759
  · exact B1173763
  · exact B1173767
  · exact B1173771
  · exact B1173775
  · exact B1173779
  · exact B1173783
  · exact B1173787
  · exact B1173791
  · exact B1173795
  · exact B1173799
  · exact B1173803
  · exact B1173807
  · exact B1173811
  · exact B1173815
  · exact B1173819
  · exact B1173823
  · exact B1173827
  · exact B1173831
  · exact B1173835
  · exact B1173839
  · exact B1173843
  · exact B1173847
  · exact B1173851
  · exact B1173855
  · exact B1173859
  · exact B1173863
  · exact B1173867
  · exact B1173871
  · exact B1173875
  · exact B1173879
  · exact B1173883
  · exact B1173887
  · exact B1173891
  · exact B1173895
  · exact B1173899
  · exact B1173903
  · exact B1173907
  · exact B1173911
  · exact B1173915
  · exact B1173919
  · exact B1173923
  · exact B1173927
  · exact B1173931
  · exact B1173935
  · exact B1173939
  · exact B1173943
  · exact B1173947
  · exact B1173951
  · exact B1173955
  · exact B1173959
  · exact B1173963
  · exact B1173967
  · exact B1173971
  · exact B1173975
  · exact B1173979
  · exact B1173983
  · exact B1173987
  · exact B1173991
  · exact B1173995
  · exact B1173999
  · exact B1174003
  · exact B1174007
  · exact B1174011
  · exact B1174015
  · exact B1174019
  · exact B1174023
  · exact B1174027
  · exact B1174031
  · exact B1174035
  · exact B1174039
  · exact B1174043
  · exact B1174047
  · exact B1174051
  · exact B1174055
  · exact B1174059
  · exact B1174063
  · exact B1174067
  · exact B1174071
  · exact B1174075
  · exact B1174079
  · exact B1174083
  · exact B1174087
  · exact B1174091
  · exact B1174095
  · exact B1174099
  · exact B1174103
  · exact B1174107
  · exact B1174111
  · exact B1174115
  · exact B1174119
  · exact B1174123
  · exact B1174127
  · exact B1174131
  · exact B1174135
  · exact B1174139
  · exact B1174143
  · exact B1174147
  · exact B1174151
  · exact B1174155
  · exact B1174159
  · exact B1174163
  · exact B1174167
  · exact B1174171
  · exact B1174175
  · exact B1174179
  · exact B1174183
  · exact B1174187
  · exact B1174191
  · exact B1174195
  · exact B1174199
  · exact B1174203
  · exact B1174207
  · exact B1174211
  · exact B1174215
  · exact B1174219
  · exact B1174223
  · exact B1174227
  · exact B1174231
  · exact B1174235
  · exact B1174239
  · exact B1174243
  · exact B1174247
  · exact B1174251
  · exact B1174255
  · exact B1174259
  · exact B1174263
  · exact B1174267
  · exact B1174271
  · exact B1174275
  · exact B1174279
  · exact B1174283
  · exact B1174287
  · exact B1174291
  · exact B1174295
  · exact B1174299
  · exact B1174303
  · exact B1174307
  · exact B1174311
  · exact B1174315
  · exact B1174319
  · exact B1174323
  · exact B1174327
  · exact B1174331
  · exact B1174335
  · exact B1174339
  · exact B1174343
  · exact B1174347
  · exact B1174351
  · exact B1174355
  · exact B1174359
  · exact B1174363
  · exact B1174367
  · exact B1174371
  · exact B1174375
  · exact B1174379
  · exact B1174383
  · exact B1174387
  · exact B1174391
  · exact B1174395
  · exact B1174399
  · exact B1174403

theorem solution (m : ℕ) (hlo : 1172403 ≤ m) (hhi : m ≤ 1174403) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 293100 ≤ j := by omega
    have hj2 : j ≤ 293600 := by omega
    have hb : Blo 1172403 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
