-- Prove2me | solution 1 for syracuse_descends_range_2055435_2057435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:31.902399+00:00
-- url     : https://prove2.me/submissions/e1038c4f-b0ef-4cf7-8946-bf8e6d3648f1

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

theorem B2312365 : Blo 2055435 2312365 := bbase (se 3 (by rfl) ⟨433568, by rfl⟩ : syracuseStep 2312365 = 867137) (by norm_num)
theorem B3083153 : Blo 2055435 3083153 := bstep (se 2 (by rfl) ⟨1156182, by rfl⟩ : syracuseStep 3083153 = 2312365) B2312365
theorem B2055435 : Blo 2055435 2055435 := bstep (se 1 (by rfl) ⟨1541576, by rfl⟩ : syracuseStep 2055435 = 3083153) B3083153
theorem B6937109 : Blo 2055435 6937109 := bbase (se 6 (by rfl) ⟨162588, by rfl⟩ : syracuseStep 6937109 = 325177) (by norm_num)
theorem B4624739 : Blo 2055435 4624739 := bstep (se 1 (by rfl) ⟨3468554, by rfl⟩ : syracuseStep 4624739 = 6937109) B6937109
theorem B3083159 : Blo 2055435 3083159 := bstep (se 1 (by rfl) ⟨2312369, by rfl⟩ : syracuseStep 3083159 = 4624739) B4624739
theorem B2055439 : Blo 2055435 2055439 := bstep (se 1 (by rfl) ⟨1541579, by rfl⟩ : syracuseStep 2055439 = 3083159) B3083159
theorem B3083165 : Blo 2055435 3083165 := bbase (se 3 (by rfl) ⟨578093, by rfl⟩ : syracuseStep 3083165 = 1156187) (by norm_num)
theorem B2055443 : Blo 2055435 2055443 := bstep (se 1 (by rfl) ⟨1541582, by rfl⟩ : syracuseStep 2055443 = 3083165) B3083165
theorem B4624757 : Blo 2055435 4624757 := bbase (se 5 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 4624757 = 433571) (by norm_num)
theorem B3083171 : Blo 2055435 3083171 := bstep (se 1 (by rfl) ⟨2312378, by rfl⟩ : syracuseStep 3083171 = 4624757) B4624757
theorem B2055447 : Blo 2055435 2055447 := bstep (se 1 (by rfl) ⟨1541585, by rfl⟩ : syracuseStep 2055447 = 3083171) B3083171
theorem B13169749 : Blo 2055435 13169749 := bbase (se 8 (by rfl) ⟨77166, by rfl⟩ : syracuseStep 13169749 = 154333) (by norm_num)
theorem B17559665 : Blo 2055435 17559665 := bstep (se 2 (by rfl) ⟨6584874, by rfl⟩ : syracuseStep 17559665 = 13169749) B13169749
theorem B11706443 : Blo 2055435 11706443 := bstep (se 1 (by rfl) ⟨8779832, by rfl⟩ : syracuseStep 11706443 = 17559665) B17559665
theorem B7804295 : Blo 2055435 7804295 := bstep (se 1 (by rfl) ⟨5853221, by rfl⟩ : syracuseStep 7804295 = 11706443) B11706443
theorem B5202863 : Blo 2055435 5202863 := bstep (se 1 (by rfl) ⟨3902147, by rfl⟩ : syracuseStep 5202863 = 7804295) B7804295
theorem B3468575 : Blo 2055435 3468575 := bstep (se 1 (by rfl) ⟨2601431, by rfl⟩ : syracuseStep 3468575 = 5202863) B5202863
theorem B2312383 : Blo 2055435 2312383 := bstep (se 1 (by rfl) ⟨1734287, by rfl⟩ : syracuseStep 2312383 = 3468575) B3468575
theorem B3083177 : Blo 2055435 3083177 := bstep (se 2 (by rfl) ⟨1156191, by rfl⟩ : syracuseStep 3083177 = 2312383) B2312383
theorem B2055451 : Blo 2055435 2055451 := bstep (se 1 (by rfl) ⟨1541588, by rfl⟩ : syracuseStep 2055451 = 3083177) B3083177
theorem B7804309 : Blo 2055435 7804309 := bbase (se 6 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 7804309 = 365827) (by norm_num)
theorem B10405745 : Blo 2055435 10405745 := bstep (se 2 (by rfl) ⟨3902154, by rfl⟩ : syracuseStep 10405745 = 7804309) B7804309
theorem B6937163 : Blo 2055435 6937163 := bstep (se 1 (by rfl) ⟨5202872, by rfl⟩ : syracuseStep 6937163 = 10405745) B10405745
theorem B4624775 : Blo 2055435 4624775 := bstep (se 1 (by rfl) ⟨3468581, by rfl⟩ : syracuseStep 4624775 = 6937163) B6937163
theorem B3083183 : Blo 2055435 3083183 := bstep (se 1 (by rfl) ⟨2312387, by rfl⟩ : syracuseStep 3083183 = 4624775) B4624775
theorem B2055455 : Blo 2055435 2055455 := bstep (se 1 (by rfl) ⟨1541591, by rfl⟩ : syracuseStep 2055455 = 3083183) B3083183
theorem B3083189 : Blo 2055435 3083189 := bbase (se 5 (by rfl) ⟨144524, by rfl⟩ : syracuseStep 3083189 = 289049) (by norm_num)
theorem B2055459 : Blo 2055435 2055459 := bstep (se 1 (by rfl) ⟨1541594, by rfl⟩ : syracuseStep 2055459 = 3083189) B3083189
theorem B5202893 : Blo 2055435 5202893 := bbase (se 3 (by rfl) ⟨975542, by rfl⟩ : syracuseStep 5202893 = 1951085) (by norm_num)
theorem B3468595 : Blo 2055435 3468595 := bstep (se 1 (by rfl) ⟨2601446, by rfl⟩ : syracuseStep 3468595 = 5202893) B5202893
theorem B4624793 : Blo 2055435 4624793 := bstep (se 2 (by rfl) ⟨1734297, by rfl⟩ : syracuseStep 4624793 = 3468595) B3468595
theorem B3083195 : Blo 2055435 3083195 := bstep (se 1 (by rfl) ⟨2312396, by rfl⟩ : syracuseStep 3083195 = 4624793) B4624793
theorem B2055463 : Blo 2055435 2055463 := bstep (se 1 (by rfl) ⟨1541597, by rfl⟩ : syracuseStep 2055463 = 3083195) B3083195
theorem B2312401 : Blo 2055435 2312401 := bbase (se 2 (by rfl) ⟨867150, by rfl⟩ : syracuseStep 2312401 = 1734301) (by norm_num)
theorem B3083201 : Blo 2055435 3083201 := bstep (se 2 (by rfl) ⟨1156200, by rfl⟩ : syracuseStep 3083201 = 2312401) B2312401
theorem B2055467 : Blo 2055435 2055467 := bstep (se 1 (by rfl) ⟨1541600, by rfl⟩ : syracuseStep 2055467 = 3083201) B3083201
theorem B6250549 : Blo 2055435 6250549 := bbase (se 5 (by rfl) ⟨292994, by rfl⟩ : syracuseStep 6250549 = 585989) (by norm_num)
theorem B8334065 : Blo 2055435 8334065 := bstep (se 2 (by rfl) ⟨3125274, by rfl⟩ : syracuseStep 8334065 = 6250549) B6250549
theorem B5556043 : Blo 2055435 5556043 := bstep (se 1 (by rfl) ⟨4167032, by rfl⟩ : syracuseStep 5556043 = 8334065) B8334065
theorem B7408057 : Blo 2055435 7408057 := bstep (se 2 (by rfl) ⟨2778021, by rfl⟩ : syracuseStep 7408057 = 5556043) B5556043
theorem B9877409 : Blo 2055435 9877409 := bstep (se 2 (by rfl) ⟨3704028, by rfl⟩ : syracuseStep 9877409 = 7408057) B7408057
theorem B6584939 : Blo 2055435 6584939 := bstep (se 1 (by rfl) ⟨4938704, by rfl⟩ : syracuseStep 6584939 = 9877409) B9877409
theorem B4389959 : Blo 2055435 4389959 := bstep (se 1 (by rfl) ⟨3292469, by rfl⟩ : syracuseStep 4389959 = 6584939) B6584939
theorem B2926639 : Blo 2055435 2926639 := bstep (se 1 (by rfl) ⟨2194979, by rfl⟩ : syracuseStep 2926639 = 4389959) B4389959
theorem B3902185 : Blo 2055435 3902185 := bstep (se 2 (by rfl) ⟨1463319, by rfl⟩ : syracuseStep 3902185 = 2926639) B2926639
theorem B5202913 : Blo 2055435 5202913 := bstep (se 2 (by rfl) ⟨1951092, by rfl⟩ : syracuseStep 5202913 = 3902185) B3902185
theorem B6937217 : Blo 2055435 6937217 := bstep (se 2 (by rfl) ⟨2601456, by rfl⟩ : syracuseStep 6937217 = 5202913) B5202913
theorem B4624811 : Blo 2055435 4624811 := bstep (se 1 (by rfl) ⟨3468608, by rfl⟩ : syracuseStep 4624811 = 6937217) B6937217
theorem B3083207 : Blo 2055435 3083207 := bstep (se 1 (by rfl) ⟨2312405, by rfl⟩ : syracuseStep 3083207 = 4624811) B4624811
theorem B2055471 : Blo 2055435 2055471 := bstep (se 1 (by rfl) ⟨1541603, by rfl⟩ : syracuseStep 2055471 = 3083207) B3083207
theorem B3083213 : Blo 2055435 3083213 := bbase (se 3 (by rfl) ⟨578102, by rfl⟩ : syracuseStep 3083213 = 1156205) (by norm_num)
theorem B2055475 : Blo 2055435 2055475 := bstep (se 1 (by rfl) ⟨1541606, by rfl⟩ : syracuseStep 2055475 = 3083213) B3083213
theorem B4624829 : Blo 2055435 4624829 := bbase (se 3 (by rfl) ⟨867155, by rfl⟩ : syracuseStep 4624829 = 1734311) (by norm_num)
theorem B3083219 : Blo 2055435 3083219 := bstep (se 1 (by rfl) ⟨2312414, by rfl⟩ : syracuseStep 3083219 = 4624829) B4624829
theorem B2055479 : Blo 2055435 2055479 := bstep (se 1 (by rfl) ⟨1541609, by rfl⟩ : syracuseStep 2055479 = 3083219) B3083219
theorem B3468629 : Blo 2055435 3468629 := bbase (se 11 (by rfl) ⟨2540, by rfl⟩ : syracuseStep 3468629 = 5081) (by norm_num)
theorem B2312419 : Blo 2055435 2312419 := bstep (se 1 (by rfl) ⟨1734314, by rfl⟩ : syracuseStep 2312419 = 3468629) B3468629
theorem B3083225 : Blo 2055435 3083225 := bstep (se 2 (by rfl) ⟨1156209, by rfl⟩ : syracuseStep 3083225 = 2312419) B2312419
theorem B2055483 : Blo 2055435 2055483 := bstep (se 1 (by rfl) ⟨1541612, by rfl⟩ : syracuseStep 2055483 = 3083225) B3083225
theorem B4687949 : Blo 2055435 4687949 := bbase (se 3 (by rfl) ⟨878990, by rfl⟩ : syracuseStep 4687949 = 1757981) (by norm_num)
theorem B3125299 : Blo 2055435 3125299 := bstep (se 1 (by rfl) ⟨2343974, by rfl⟩ : syracuseStep 3125299 = 4687949) B4687949
theorem B4167065 : Blo 2055435 4167065 := bstep (se 2 (by rfl) ⟨1562649, by rfl⟩ : syracuseStep 4167065 = 3125299) B3125299
theorem B2778043 : Blo 2055435 2778043 := bstep (se 1 (by rfl) ⟨2083532, by rfl⟩ : syracuseStep 2778043 = 4167065) B4167065
theorem B3704057 : Blo 2055435 3704057 := bstep (se 2 (by rfl) ⟨1389021, by rfl⟩ : syracuseStep 3704057 = 2778043) B2778043
theorem B2469371 : Blo 2055435 2469371 := bstep (se 1 (by rfl) ⟨1852028, by rfl⟩ : syracuseStep 2469371 = 3704057) B3704057
theorem B6584989 : Blo 2055435 6584989 := bstep (se 3 (by rfl) ⟨1234685, by rfl⟩ : syracuseStep 6584989 = 2469371) B2469371
theorem B8779985 : Blo 2055435 8779985 := bstep (se 2 (by rfl) ⟨3292494, by rfl⟩ : syracuseStep 8779985 = 6584989) B6584989
theorem B5853323 : Blo 2055435 5853323 := bstep (se 1 (by rfl) ⟨4389992, by rfl⟩ : syracuseStep 5853323 = 8779985) B8779985
theorem B15608861 : Blo 2055435 15608861 := bstep (se 3 (by rfl) ⟨2926661, by rfl⟩ : syracuseStep 15608861 = 5853323) B5853323
theorem B10405907 : Blo 2055435 10405907 := bstep (se 1 (by rfl) ⟨7804430, by rfl⟩ : syracuseStep 10405907 = 15608861) B15608861
theorem B6937271 : Blo 2055435 6937271 := bstep (se 1 (by rfl) ⟨5202953, by rfl⟩ : syracuseStep 6937271 = 10405907) B10405907
theorem B4624847 : Blo 2055435 4624847 := bstep (se 1 (by rfl) ⟨3468635, by rfl⟩ : syracuseStep 4624847 = 6937271) B6937271
theorem B3083231 : Blo 2055435 3083231 := bstep (se 1 (by rfl) ⟨2312423, by rfl⟩ : syracuseStep 3083231 = 4624847) B4624847
theorem B2055487 : Blo 2055435 2055487 := bstep (se 1 (by rfl) ⟨1541615, by rfl⟩ : syracuseStep 2055487 = 3083231) B3083231
theorem B3083237 : Blo 2055435 3083237 := bbase (se 4 (by rfl) ⟨289053, by rfl⟩ : syracuseStep 3083237 = 578107) (by norm_num)
theorem B2055491 : Blo 2055435 2055491 := bstep (se 1 (by rfl) ⟨1541618, by rfl⟩ : syracuseStep 2055491 = 3083237) B3083237
theorem B8780021 : Blo 2055435 8780021 := bbase (se 5 (by rfl) ⟨411563, by rfl⟩ : syracuseStep 8780021 = 823127) (by norm_num)
theorem B5853347 : Blo 2055435 5853347 := bstep (se 1 (by rfl) ⟨4390010, by rfl⟩ : syracuseStep 5853347 = 8780021) B8780021
theorem B3902231 : Blo 2055435 3902231 := bstep (se 1 (by rfl) ⟨2926673, by rfl⟩ : syracuseStep 3902231 = 5853347) B5853347
theorem B2601487 : Blo 2055435 2601487 := bstep (se 1 (by rfl) ⟨1951115, by rfl⟩ : syracuseStep 2601487 = 3902231) B3902231
theorem B3468649 : Blo 2055435 3468649 := bstep (se 2 (by rfl) ⟨1300743, by rfl⟩ : syracuseStep 3468649 = 2601487) B2601487
theorem B4624865 : Blo 2055435 4624865 := bstep (se 2 (by rfl) ⟨1734324, by rfl⟩ : syracuseStep 4624865 = 3468649) B3468649
theorem B3083243 : Blo 2055435 3083243 := bstep (se 1 (by rfl) ⟨2312432, by rfl⟩ : syracuseStep 3083243 = 4624865) B4624865
theorem B2055495 : Blo 2055435 2055495 := bstep (se 1 (by rfl) ⟨1541621, by rfl⟩ : syracuseStep 2055495 = 3083243) B3083243
theorem B2312437 : Blo 2055435 2312437 := bbase (se 5 (by rfl) ⟨108395, by rfl⟩ : syracuseStep 2312437 = 216791) (by norm_num)
theorem B3083249 : Blo 2055435 3083249 := bstep (se 2 (by rfl) ⟨1156218, by rfl⟩ : syracuseStep 3083249 = 2312437) B2312437
theorem B2055499 : Blo 2055435 2055499 := bstep (se 1 (by rfl) ⟨1541624, by rfl⟩ : syracuseStep 2055499 = 3083249) B3083249
theorem B2601497 : Blo 2055435 2601497 := bbase (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) (by norm_num)
theorem B6937325 : Blo 2055435 6937325 := bstep (se 3 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 6937325 = 2601497) B2601497
theorem B4624883 : Blo 2055435 4624883 := bstep (se 1 (by rfl) ⟨3468662, by rfl⟩ : syracuseStep 4624883 = 6937325) B6937325
theorem B3083255 : Blo 2055435 3083255 := bstep (se 1 (by rfl) ⟨2312441, by rfl⟩ : syracuseStep 3083255 = 4624883) B4624883
theorem B2055503 : Blo 2055435 2055503 := bstep (se 1 (by rfl) ⟨1541627, by rfl⟩ : syracuseStep 2055503 = 3083255) B3083255
theorem B3083261 : Blo 2055435 3083261 := bbase (se 3 (by rfl) ⟨578111, by rfl⟩ : syracuseStep 3083261 = 1156223) (by norm_num)
theorem B2055507 : Blo 2055435 2055507 := bstep (se 1 (by rfl) ⟨1541630, by rfl⟩ : syracuseStep 2055507 = 3083261) B3083261
theorem B4624901 : Blo 2055435 4624901 := bbase (se 4 (by rfl) ⟨433584, by rfl⟩ : syracuseStep 4624901 = 867169) (by norm_num)
theorem B3083267 : Blo 2055435 3083267 := bstep (se 1 (by rfl) ⟨2312450, by rfl⟩ : syracuseStep 3083267 = 4624901) B4624901
theorem B2055511 : Blo 2055435 2055511 := bstep (se 1 (by rfl) ⟨1541633, by rfl⟩ : syracuseStep 2055511 = 3083267) B3083267
theorem B3902269 : Blo 2055435 3902269 := bbase (se 3 (by rfl) ⟨731675, by rfl⟩ : syracuseStep 3902269 = 1463351) (by norm_num)
theorem B5203025 : Blo 2055435 5203025 := bstep (se 2 (by rfl) ⟨1951134, by rfl⟩ : syracuseStep 5203025 = 3902269) B3902269
theorem B3468683 : Blo 2055435 3468683 := bstep (se 1 (by rfl) ⟨2601512, by rfl⟩ : syracuseStep 3468683 = 5203025) B5203025
theorem B2312455 : Blo 2055435 2312455 := bstep (se 1 (by rfl) ⟨1734341, by rfl⟩ : syracuseStep 2312455 = 3468683) B3468683
theorem B3083273 : Blo 2055435 3083273 := bstep (se 2 (by rfl) ⟨1156227, by rfl⟩ : syracuseStep 3083273 = 2312455) B2312455
theorem B2055515 : Blo 2055435 2055515 := bstep (se 1 (by rfl) ⟨1541636, by rfl⟩ : syracuseStep 2055515 = 3083273) B3083273
theorem B10406069 : Blo 2055435 10406069 := bbase (se 5 (by rfl) ⟨487784, by rfl⟩ : syracuseStep 10406069 = 975569) (by norm_num)
theorem B6937379 : Blo 2055435 6937379 := bstep (se 1 (by rfl) ⟨5203034, by rfl⟩ : syracuseStep 6937379 = 10406069) B10406069
theorem B4624919 : Blo 2055435 4624919 := bstep (se 1 (by rfl) ⟨3468689, by rfl⟩ : syracuseStep 4624919 = 6937379) B6937379
theorem B3083279 : Blo 2055435 3083279 := bstep (se 1 (by rfl) ⟨2312459, by rfl⟩ : syracuseStep 3083279 = 4624919) B4624919
theorem B2055519 : Blo 2055435 2055519 := bstep (se 1 (by rfl) ⟨1541639, by rfl⟩ : syracuseStep 2055519 = 3083279) B3083279
theorem B3083285 : Blo 2055435 3083285 := bbase (se 6 (by rfl) ⟨72264, by rfl⟩ : syracuseStep 3083285 = 144529) (by norm_num)
theorem B2055523 : Blo 2055435 2055523 := bstep (se 1 (by rfl) ⟨1541642, by rfl⟩ : syracuseStep 2055523 = 3083285) B3083285
theorem B2673001 : Blo 2055435 2673001 := bbase (se 2 (by rfl) ⟨1002375, by rfl⟩ : syracuseStep 2673001 = 2004751) (by norm_num)
theorem B3564001 : Blo 2055435 3564001 := bstep (se 2 (by rfl) ⟨1336500, by rfl⟩ : syracuseStep 3564001 = 2673001) B2673001
theorem B4752001 : Blo 2055435 4752001 := bstep (se 2 (by rfl) ⟨1782000, by rfl⟩ : syracuseStep 4752001 = 3564001) B3564001
theorem B6336001 : Blo 2055435 6336001 := bstep (se 2 (by rfl) ⟨2376000, by rfl⟩ : syracuseStep 6336001 = 4752001) B4752001
theorem B33792005 : Blo 2055435 33792005 := bstep (se 4 (by rfl) ⟨3168000, by rfl⟩ : syracuseStep 33792005 = 6336001) B6336001
theorem B22528003 : Blo 2055435 22528003 := bstep (se 1 (by rfl) ⟨16896002, by rfl⟩ : syracuseStep 22528003 = 33792005) B33792005
theorem B30037337 : Blo 2055435 30037337 := bstep (se 2 (by rfl) ⟨11264001, by rfl⟩ : syracuseStep 30037337 = 22528003) B22528003
theorem B20024891 : Blo 2055435 20024891 := bstep (se 1 (by rfl) ⟨15018668, by rfl⟩ : syracuseStep 20024891 = 30037337) B30037337
theorem B13349927 : Blo 2055435 13349927 := bstep (se 1 (by rfl) ⟨10012445, by rfl⟩ : syracuseStep 13349927 = 20024891) B20024891
theorem B8899951 : Blo 2055435 8899951 := bstep (se 1 (by rfl) ⟨6674963, by rfl⟩ : syracuseStep 8899951 = 13349927) B13349927
theorem B11866601 : Blo 2055435 11866601 := bstep (se 2 (by rfl) ⟨4449975, by rfl⟩ : syracuseStep 11866601 = 8899951) B8899951
theorem B7911067 : Blo 2055435 7911067 := bstep (se 1 (by rfl) ⟨5933300, by rfl⟩ : syracuseStep 7911067 = 11866601) B11866601
theorem B10548089 : Blo 2055435 10548089 := bstep (se 2 (by rfl) ⟨3955533, by rfl⟩ : syracuseStep 10548089 = 7911067) B7911067
theorem B7032059 : Blo 2055435 7032059 := bstep (se 1 (by rfl) ⟨5274044, by rfl⟩ : syracuseStep 7032059 = 10548089) B10548089
theorem B4688039 : Blo 2055435 4688039 := bstep (se 1 (by rfl) ⟨3516029, by rfl⟩ : syracuseStep 4688039 = 7032059) B7032059
theorem B3125359 : Blo 2055435 3125359 := bstep (se 1 (by rfl) ⟨2344019, by rfl⟩ : syracuseStep 3125359 = 4688039) B4688039
theorem B4167145 : Blo 2055435 4167145 := bstep (se 2 (by rfl) ⟨1562679, by rfl⟩ : syracuseStep 4167145 = 3125359) B3125359
theorem B22224773 : Blo 2055435 22224773 := bstep (se 4 (by rfl) ⟨2083572, by rfl⟩ : syracuseStep 22224773 = 4167145) B4167145
theorem B14816515 : Blo 2055435 14816515 := bstep (se 1 (by rfl) ⟨11112386, by rfl⟩ : syracuseStep 14816515 = 22224773) B22224773
theorem B19755353 : Blo 2055435 19755353 := bstep (se 2 (by rfl) ⟨7408257, by rfl⟩ : syracuseStep 19755353 = 14816515) B14816515
theorem B13170235 : Blo 2055435 13170235 := bstep (se 1 (by rfl) ⟨9877676, by rfl⟩ : syracuseStep 13170235 = 19755353) B19755353
theorem B17560313 : Blo 2055435 17560313 := bstep (se 2 (by rfl) ⟨6585117, by rfl⟩ : syracuseStep 17560313 = 13170235) B13170235
theorem B11706875 : Blo 2055435 11706875 := bstep (se 1 (by rfl) ⟨8780156, by rfl⟩ : syracuseStep 11706875 = 17560313) B17560313
theorem B7804583 : Blo 2055435 7804583 := bstep (se 1 (by rfl) ⟨5853437, by rfl⟩ : syracuseStep 7804583 = 11706875) B11706875
theorem B5203055 : Blo 2055435 5203055 := bstep (se 1 (by rfl) ⟨3902291, by rfl⟩ : syracuseStep 5203055 = 7804583) B7804583
theorem B3468703 : Blo 2055435 3468703 := bstep (se 1 (by rfl) ⟨2601527, by rfl⟩ : syracuseStep 3468703 = 5203055) B5203055
theorem B4624937 : Blo 2055435 4624937 := bstep (se 2 (by rfl) ⟨1734351, by rfl⟩ : syracuseStep 4624937 = 3468703) B3468703
theorem B3083291 : Blo 2055435 3083291 := bstep (se 1 (by rfl) ⟨2312468, by rfl⟩ : syracuseStep 3083291 = 4624937) B4624937
theorem B2055527 : Blo 2055435 2055527 := bstep (se 1 (by rfl) ⟨1541645, by rfl⟩ : syracuseStep 2055527 = 3083291) B3083291
theorem B2312473 : Blo 2055435 2312473 := bbase (se 2 (by rfl) ⟨867177, by rfl⟩ : syracuseStep 2312473 = 1734355) (by norm_num)
theorem B3083297 : Blo 2055435 3083297 := bstep (se 2 (by rfl) ⟨1156236, by rfl⟩ : syracuseStep 3083297 = 2312473) B2312473
theorem B2055531 : Blo 2055435 2055531 := bstep (se 1 (by rfl) ⟨1541648, by rfl⟩ : syracuseStep 2055531 = 3083297) B3083297
theorem B7804613 : Blo 2055435 7804613 := bbase (se 4 (by rfl) ⟨731682, by rfl⟩ : syracuseStep 7804613 = 1463365) (by norm_num)
theorem B5203075 : Blo 2055435 5203075 := bstep (se 1 (by rfl) ⟨3902306, by rfl⟩ : syracuseStep 5203075 = 7804613) B7804613
theorem B6937433 : Blo 2055435 6937433 := bstep (se 2 (by rfl) ⟨2601537, by rfl⟩ : syracuseStep 6937433 = 5203075) B5203075
theorem B4624955 : Blo 2055435 4624955 := bstep (se 1 (by rfl) ⟨3468716, by rfl⟩ : syracuseStep 4624955 = 6937433) B6937433
theorem B3083303 : Blo 2055435 3083303 := bstep (se 1 (by rfl) ⟨2312477, by rfl⟩ : syracuseStep 3083303 = 4624955) B4624955
theorem B2055535 : Blo 2055435 2055535 := bstep (se 1 (by rfl) ⟨1541651, by rfl⟩ : syracuseStep 2055535 = 3083303) B3083303
theorem B3083309 : Blo 2055435 3083309 := bbase (se 3 (by rfl) ⟨578120, by rfl⟩ : syracuseStep 3083309 = 1156241) (by norm_num)
theorem B2055539 : Blo 2055435 2055539 := bstep (se 1 (by rfl) ⟨1541654, by rfl⟩ : syracuseStep 2055539 = 3083309) B3083309
theorem B4624973 : Blo 2055435 4624973 := bbase (se 3 (by rfl) ⟨867182, by rfl⟩ : syracuseStep 4624973 = 1734365) (by norm_num)
theorem B3083315 : Blo 2055435 3083315 := bstep (se 1 (by rfl) ⟨2312486, by rfl⟩ : syracuseStep 3083315 = 4624973) B4624973
theorem B2055543 : Blo 2055435 2055543 := bstep (se 1 (by rfl) ⟨1541657, by rfl⟩ : syracuseStep 2055543 = 3083315) B3083315
theorem B2601553 : Blo 2055435 2601553 := bbase (se 2 (by rfl) ⟨975582, by rfl⟩ : syracuseStep 2601553 = 1951165) (by norm_num)
theorem B3468737 : Blo 2055435 3468737 := bstep (se 2 (by rfl) ⟨1300776, by rfl⟩ : syracuseStep 3468737 = 2601553) B2601553
theorem B2312491 : Blo 2055435 2312491 := bstep (se 1 (by rfl) ⟨1734368, by rfl⟩ : syracuseStep 2312491 = 3468737) B3468737
theorem B3083321 : Blo 2055435 3083321 := bstep (se 2 (by rfl) ⟨1156245, by rfl⟩ : syracuseStep 3083321 = 2312491) B2312491
theorem B2055547 : Blo 2055435 2055547 := bstep (se 1 (by rfl) ⟨1541660, by rfl⟩ : syracuseStep 2055547 = 3083321) B3083321
theorem B3292597 : Blo 2055435 3292597 := bbase (se 5 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 3292597 = 308681) (by norm_num)
theorem B4390129 : Blo 2055435 4390129 := bstep (se 2 (by rfl) ⟨1646298, by rfl⟩ : syracuseStep 4390129 = 3292597) B3292597
theorem B23414021 : Blo 2055435 23414021 := bstep (se 4 (by rfl) ⟨2195064, by rfl⟩ : syracuseStep 23414021 = 4390129) B4390129
theorem B15609347 : Blo 2055435 15609347 := bstep (se 1 (by rfl) ⟨11707010, by rfl⟩ : syracuseStep 15609347 = 23414021) B23414021
theorem B10406231 : Blo 2055435 10406231 := bstep (se 1 (by rfl) ⟨7804673, by rfl⟩ : syracuseStep 10406231 = 15609347) B15609347
theorem B6937487 : Blo 2055435 6937487 := bstep (se 1 (by rfl) ⟨5203115, by rfl⟩ : syracuseStep 6937487 = 10406231) B10406231
theorem B4624991 : Blo 2055435 4624991 := bstep (se 1 (by rfl) ⟨3468743, by rfl⟩ : syracuseStep 4624991 = 6937487) B6937487
theorem B3083327 : Blo 2055435 3083327 := bstep (se 1 (by rfl) ⟨2312495, by rfl⟩ : syracuseStep 3083327 = 4624991) B4624991
theorem B2055551 : Blo 2055435 2055551 := bstep (se 1 (by rfl) ⟨1541663, by rfl⟩ : syracuseStep 2055551 = 3083327) B3083327
theorem B3083333 : Blo 2055435 3083333 := bbase (se 4 (by rfl) ⟨289062, by rfl⟩ : syracuseStep 3083333 = 578125) (by norm_num)
theorem B2055555 : Blo 2055435 2055555 := bstep (se 1 (by rfl) ⟨1541666, by rfl⟩ : syracuseStep 2055555 = 3083333) B3083333
theorem B3468757 : Blo 2055435 3468757 := bbase (se 7 (by rfl) ⟨40649, by rfl⟩ : syracuseStep 3468757 = 81299) (by norm_num)
theorem B4625009 : Blo 2055435 4625009 := bstep (se 2 (by rfl) ⟨1734378, by rfl⟩ : syracuseStep 4625009 = 3468757) B3468757
theorem B3083339 : Blo 2055435 3083339 := bstep (se 1 (by rfl) ⟨2312504, by rfl⟩ : syracuseStep 3083339 = 4625009) B4625009
theorem B2055559 : Blo 2055435 2055559 := bstep (se 1 (by rfl) ⟨1541669, by rfl⟩ : syracuseStep 2055559 = 3083339) B3083339
theorem B2312509 : Blo 2055435 2312509 := bbase (se 3 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 2312509 = 867191) (by norm_num)
theorem B3083345 : Blo 2055435 3083345 := bstep (se 2 (by rfl) ⟨1156254, by rfl⟩ : syracuseStep 3083345 = 2312509) B2312509
theorem B2055563 : Blo 2055435 2055563 := bstep (se 1 (by rfl) ⟨1541672, by rfl⟩ : syracuseStep 2055563 = 3083345) B3083345
theorem B6937541 : Blo 2055435 6937541 := bbase (se 4 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 6937541 = 1300789) (by norm_num)
theorem B4625027 : Blo 2055435 4625027 := bstep (se 1 (by rfl) ⟨3468770, by rfl⟩ : syracuseStep 4625027 = 6937541) B6937541
theorem B3083351 : Blo 2055435 3083351 := bstep (se 1 (by rfl) ⟨2312513, by rfl⟩ : syracuseStep 3083351 = 4625027) B4625027
theorem B2055567 : Blo 2055435 2055567 := bstep (se 1 (by rfl) ⟨1541675, by rfl⟩ : syracuseStep 2055567 = 3083351) B3083351
theorem B3083357 : Blo 2055435 3083357 := bbase (se 3 (by rfl) ⟨578129, by rfl⟩ : syracuseStep 3083357 = 1156259) (by norm_num)
theorem B2055571 : Blo 2055435 2055571 := bstep (se 1 (by rfl) ⟨1541678, by rfl⟩ : syracuseStep 2055571 = 3083357) B3083357
theorem B4625045 : Blo 2055435 4625045 := bbase (se 6 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 4625045 = 216799) (by norm_num)
theorem B3083363 : Blo 2055435 3083363 := bstep (se 1 (by rfl) ⟨2312522, by rfl⟩ : syracuseStep 3083363 = 4625045) B4625045
theorem B2055575 : Blo 2055435 2055575 := bstep (se 1 (by rfl) ⟨1541681, by rfl⟩ : syracuseStep 2055575 = 3083363) B3083363
theorem B4938965 : Blo 2055435 4938965 := bbase (se 7 (by rfl) ⟨57878, by rfl⟩ : syracuseStep 4938965 = 115757) (by norm_num)
theorem B3292643 : Blo 2055435 3292643 := bstep (se 1 (by rfl) ⟨2469482, by rfl⟩ : syracuseStep 3292643 = 4938965) B4938965
theorem B2195095 : Blo 2055435 2195095 := bstep (se 1 (by rfl) ⟨1646321, by rfl⟩ : syracuseStep 2195095 = 3292643) B3292643
theorem B2926793 : Blo 2055435 2926793 := bstep (se 2 (by rfl) ⟨1097547, by rfl⟩ : syracuseStep 2926793 = 2195095) B2195095
theorem B7804781 : Blo 2055435 7804781 := bstep (se 3 (by rfl) ⟨1463396, by rfl⟩ : syracuseStep 7804781 = 2926793) B2926793
theorem B5203187 : Blo 2055435 5203187 := bstep (se 1 (by rfl) ⟨3902390, by rfl⟩ : syracuseStep 5203187 = 7804781) B7804781
theorem B3468791 : Blo 2055435 3468791 := bstep (se 1 (by rfl) ⟨2601593, by rfl⟩ : syracuseStep 3468791 = 5203187) B5203187
theorem B2312527 : Blo 2055435 2312527 := bstep (se 1 (by rfl) ⟨1734395, by rfl⟩ : syracuseStep 2312527 = 3468791) B3468791
theorem B3083369 : Blo 2055435 3083369 := bstep (se 2 (by rfl) ⟨1156263, by rfl⟩ : syracuseStep 3083369 = 2312527) B2312527
theorem B2055579 : Blo 2055435 2055579 := bstep (se 1 (by rfl) ⟨1541684, by rfl⟩ : syracuseStep 2055579 = 3083369) B3083369
theorem B8334517 : Blo 2055435 8334517 := bbase (se 5 (by rfl) ⟨390680, by rfl⟩ : syracuseStep 8334517 = 781361) (by norm_num)
theorem B11112689 : Blo 2055435 11112689 := bstep (se 2 (by rfl) ⟨4167258, by rfl⟩ : syracuseStep 11112689 = 8334517) B8334517
theorem B7408459 : Blo 2055435 7408459 := bstep (se 1 (by rfl) ⟨5556344, by rfl⟩ : syracuseStep 7408459 = 11112689) B11112689
theorem B9877945 : Blo 2055435 9877945 := bstep (se 2 (by rfl) ⟨3704229, by rfl⟩ : syracuseStep 9877945 = 7408459) B7408459
theorem B13170593 : Blo 2055435 13170593 := bstep (se 2 (by rfl) ⟨4938972, by rfl⟩ : syracuseStep 13170593 = 9877945) B9877945
theorem B8780395 : Blo 2055435 8780395 := bstep (se 1 (by rfl) ⟨6585296, by rfl⟩ : syracuseStep 8780395 = 13170593) B13170593
theorem B11707193 : Blo 2055435 11707193 := bstep (se 2 (by rfl) ⟨4390197, by rfl⟩ : syracuseStep 11707193 = 8780395) B8780395
theorem B7804795 : Blo 2055435 7804795 := bstep (se 1 (by rfl) ⟨5853596, by rfl⟩ : syracuseStep 7804795 = 11707193) B11707193
theorem B10406393 : Blo 2055435 10406393 := bstep (se 2 (by rfl) ⟨3902397, by rfl⟩ : syracuseStep 10406393 = 7804795) B7804795
theorem B6937595 : Blo 2055435 6937595 := bstep (se 1 (by rfl) ⟨5203196, by rfl⟩ : syracuseStep 6937595 = 10406393) B10406393
theorem B4625063 : Blo 2055435 4625063 := bstep (se 1 (by rfl) ⟨3468797, by rfl⟩ : syracuseStep 4625063 = 6937595) B6937595
theorem B3083375 : Blo 2055435 3083375 := bstep (se 1 (by rfl) ⟨2312531, by rfl⟩ : syracuseStep 3083375 = 4625063) B4625063
theorem B2055583 : Blo 2055435 2055583 := bstep (se 1 (by rfl) ⟨1541687, by rfl⟩ : syracuseStep 2055583 = 3083375) B3083375
theorem B3083381 : Blo 2055435 3083381 := bbase (se 5 (by rfl) ⟨144533, by rfl⟩ : syracuseStep 3083381 = 289067) (by norm_num)
theorem B2055587 : Blo 2055435 2055587 := bstep (se 1 (by rfl) ⟨1541690, by rfl⟩ : syracuseStep 2055587 = 3083381) B3083381
theorem B3902413 : Blo 2055435 3902413 := bbase (se 3 (by rfl) ⟨731702, by rfl⟩ : syracuseStep 3902413 = 1463405) (by norm_num)
theorem B5203217 : Blo 2055435 5203217 := bstep (se 2 (by rfl) ⟨1951206, by rfl⟩ : syracuseStep 5203217 = 3902413) B3902413
theorem B3468811 : Blo 2055435 3468811 := bstep (se 1 (by rfl) ⟨2601608, by rfl⟩ : syracuseStep 3468811 = 5203217) B5203217
theorem B4625081 : Blo 2055435 4625081 := bstep (se 2 (by rfl) ⟨1734405, by rfl⟩ : syracuseStep 4625081 = 3468811) B3468811
theorem B3083387 : Blo 2055435 3083387 := bstep (se 1 (by rfl) ⟨2312540, by rfl⟩ : syracuseStep 3083387 = 4625081) B4625081
theorem B2055591 : Blo 2055435 2055591 := bstep (se 1 (by rfl) ⟨1541693, by rfl⟩ : syracuseStep 2055591 = 3083387) B3083387
theorem B2312545 : Blo 2055435 2312545 := bbase (se 2 (by rfl) ⟨867204, by rfl⟩ : syracuseStep 2312545 = 1734409) (by norm_num)
theorem B3083393 : Blo 2055435 3083393 := bstep (se 2 (by rfl) ⟨1156272, by rfl⟩ : syracuseStep 3083393 = 2312545) B2312545
theorem B2055595 : Blo 2055435 2055595 := bstep (se 1 (by rfl) ⟨1541696, by rfl⟩ : syracuseStep 2055595 = 3083393) B3083393
theorem B5203237 : Blo 2055435 5203237 := bbase (se 4 (by rfl) ⟨487803, by rfl⟩ : syracuseStep 5203237 = 975607) (by norm_num)
theorem B6937649 : Blo 2055435 6937649 := bstep (se 2 (by rfl) ⟨2601618, by rfl⟩ : syracuseStep 6937649 = 5203237) B5203237
theorem B4625099 : Blo 2055435 4625099 := bstep (se 1 (by rfl) ⟨3468824, by rfl⟩ : syracuseStep 4625099 = 6937649) B6937649
theorem B3083399 : Blo 2055435 3083399 := bstep (se 1 (by rfl) ⟨2312549, by rfl⟩ : syracuseStep 3083399 = 4625099) B4625099
theorem B2055599 : Blo 2055435 2055599 := bstep (se 1 (by rfl) ⟨1541699, by rfl⟩ : syracuseStep 2055599 = 3083399) B3083399
theorem B3083405 : Blo 2055435 3083405 := bbase (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) (by norm_num)
theorem B2055603 : Blo 2055435 2055603 := bstep (se 1 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 2055603 = 3083405) B3083405
theorem B4625117 : Blo 2055435 4625117 := bbase (se 3 (by rfl) ⟨867209, by rfl⟩ : syracuseStep 4625117 = 1734419) (by norm_num)
theorem B3083411 : Blo 2055435 3083411 := bstep (se 1 (by rfl) ⟨2312558, by rfl⟩ : syracuseStep 3083411 = 4625117) B4625117
theorem B2055607 : Blo 2055435 2055607 := bstep (se 1 (by rfl) ⟨1541705, by rfl⟩ : syracuseStep 2055607 = 3083411) B3083411
theorem B3468845 : Blo 2055435 3468845 := bbase (se 3 (by rfl) ⟨650408, by rfl⟩ : syracuseStep 3468845 = 1300817) (by norm_num)
theorem B2312563 : Blo 2055435 2312563 := bstep (se 1 (by rfl) ⟨1734422, by rfl⟩ : syracuseStep 2312563 = 3468845) B3468845
theorem B3083417 : Blo 2055435 3083417 := bstep (se 2 (by rfl) ⟨1156281, by rfl⟩ : syracuseStep 3083417 = 2312563) B2312563
theorem B2055611 : Blo 2055435 2055611 := bstep (se 1 (by rfl) ⟨1541708, by rfl⟩ : syracuseStep 2055611 = 3083417) B3083417
theorem B15822805 : Blo 2055435 15822805 := bbase (se 7 (by rfl) ⟨185423, by rfl⟩ : syracuseStep 15822805 = 370847) (by norm_num)
theorem B21097073 : Blo 2055435 21097073 := bstep (se 2 (by rfl) ⟨7911402, by rfl⟩ : syracuseStep 21097073 = 15822805) B15822805
theorem B14064715 : Blo 2055435 14064715 := bstep (se 1 (by rfl) ⟨10548536, by rfl⟩ : syracuseStep 14064715 = 21097073) B21097073
theorem B18752953 : Blo 2055435 18752953 := bstep (se 2 (by rfl) ⟨7032357, by rfl⟩ : syracuseStep 18752953 = 14064715) B14064715
theorem B25003937 : Blo 2055435 25003937 := bstep (se 2 (by rfl) ⟨9376476, by rfl⟩ : syracuseStep 25003937 = 18752953) B18752953
theorem B66677165 : Blo 2055435 66677165 := bstep (se 3 (by rfl) ⟨12501968, by rfl⟩ : syracuseStep 66677165 = 25003937) B25003937
theorem B44451443 : Blo 2055435 44451443 := bstep (se 1 (by rfl) ⟨33338582, by rfl⟩ : syracuseStep 44451443 = 66677165) B66677165
theorem B29634295 : Blo 2055435 29634295 := bstep (se 1 (by rfl) ⟨22225721, by rfl⟩ : syracuseStep 29634295 = 44451443) B44451443
theorem B39512393 : Blo 2055435 39512393 := bstep (se 2 (by rfl) ⟨14817147, by rfl⟩ : syracuseStep 39512393 = 29634295) B29634295
theorem B26341595 : Blo 2055435 26341595 := bstep (se 1 (by rfl) ⟨19756196, by rfl⟩ : syracuseStep 26341595 = 39512393) B39512393
theorem B17561063 : Blo 2055435 17561063 := bstep (se 1 (by rfl) ⟨13170797, by rfl⟩ : syracuseStep 17561063 = 26341595) B26341595
theorem B11707375 : Blo 2055435 11707375 := bstep (se 1 (by rfl) ⟨8780531, by rfl⟩ : syracuseStep 11707375 = 17561063) B17561063
theorem B15609833 : Blo 2055435 15609833 := bstep (se 2 (by rfl) ⟨5853687, by rfl⟩ : syracuseStep 15609833 = 11707375) B11707375
theorem B10406555 : Blo 2055435 10406555 := bstep (se 1 (by rfl) ⟨7804916, by rfl⟩ : syracuseStep 10406555 = 15609833) B15609833
theorem B6937703 : Blo 2055435 6937703 := bstep (se 1 (by rfl) ⟨5203277, by rfl⟩ : syracuseStep 6937703 = 10406555) B10406555
theorem B4625135 : Blo 2055435 4625135 := bstep (se 1 (by rfl) ⟨3468851, by rfl⟩ : syracuseStep 4625135 = 6937703) B6937703
theorem B3083423 : Blo 2055435 3083423 := bstep (se 1 (by rfl) ⟨2312567, by rfl⟩ : syracuseStep 3083423 = 4625135) B4625135
theorem B2055615 : Blo 2055435 2055615 := bstep (se 1 (by rfl) ⟨1541711, by rfl⟩ : syracuseStep 2055615 = 3083423) B3083423
theorem B3083429 : Blo 2055435 3083429 := bbase (se 4 (by rfl) ⟨289071, by rfl⟩ : syracuseStep 3083429 = 578143) (by norm_num)
theorem B2055619 : Blo 2055435 2055619 := bstep (se 1 (by rfl) ⟨1541714, by rfl⟩ : syracuseStep 2055619 = 3083429) B3083429
theorem B2601649 : Blo 2055435 2601649 := bbase (se 2 (by rfl) ⟨975618, by rfl⟩ : syracuseStep 2601649 = 1951237) (by norm_num)
theorem B3468865 : Blo 2055435 3468865 := bstep (se 2 (by rfl) ⟨1300824, by rfl⟩ : syracuseStep 3468865 = 2601649) B2601649
theorem B4625153 : Blo 2055435 4625153 := bstep (se 2 (by rfl) ⟨1734432, by rfl⟩ : syracuseStep 4625153 = 3468865) B3468865
theorem B3083435 : Blo 2055435 3083435 := bstep (se 1 (by rfl) ⟨2312576, by rfl⟩ : syracuseStep 3083435 = 4625153) B4625153
theorem B2055623 : Blo 2055435 2055623 := bstep (se 1 (by rfl) ⟨1541717, by rfl⟩ : syracuseStep 2055623 = 3083435) B3083435
theorem B2312581 : Blo 2055435 2312581 := bbase (se 4 (by rfl) ⟨216804, by rfl⟩ : syracuseStep 2312581 = 433609) (by norm_num)
theorem B3083441 : Blo 2055435 3083441 := bstep (se 2 (by rfl) ⟨1156290, by rfl⟩ : syracuseStep 3083441 = 2312581) B2312581
theorem B2055627 : Blo 2055435 2055627 := bstep (se 1 (by rfl) ⟨1541720, by rfl⟩ : syracuseStep 2055627 = 3083441) B3083441
theorem B4390301 : Blo 2055435 4390301 := bbase (se 3 (by rfl) ⟨823181, by rfl⟩ : syracuseStep 4390301 = 1646363) (by norm_num)
theorem B2926867 : Blo 2055435 2926867 := bstep (se 1 (by rfl) ⟨2195150, by rfl⟩ : syracuseStep 2926867 = 4390301) B4390301
theorem B3902489 : Blo 2055435 3902489 := bstep (se 2 (by rfl) ⟨1463433, by rfl⟩ : syracuseStep 3902489 = 2926867) B2926867
theorem B2601659 : Blo 2055435 2601659 := bstep (se 1 (by rfl) ⟨1951244, by rfl⟩ : syracuseStep 2601659 = 3902489) B3902489
theorem B6937757 : Blo 2055435 6937757 := bstep (se 3 (by rfl) ⟨1300829, by rfl⟩ : syracuseStep 6937757 = 2601659) B2601659
theorem B4625171 : Blo 2055435 4625171 := bstep (se 1 (by rfl) ⟨3468878, by rfl⟩ : syracuseStep 4625171 = 6937757) B6937757
theorem B3083447 : Blo 2055435 3083447 := bstep (se 1 (by rfl) ⟨2312585, by rfl⟩ : syracuseStep 3083447 = 4625171) B4625171
theorem B2055631 : Blo 2055435 2055631 := bstep (se 1 (by rfl) ⟨1541723, by rfl⟩ : syracuseStep 2055631 = 3083447) B3083447
theorem B3083453 : Blo 2055435 3083453 := bbase (se 3 (by rfl) ⟨578147, by rfl⟩ : syracuseStep 3083453 = 1156295) (by norm_num)
theorem B2055635 : Blo 2055435 2055635 := bstep (se 1 (by rfl) ⟨1541726, by rfl⟩ : syracuseStep 2055635 = 3083453) B3083453
theorem B4625189 : Blo 2055435 4625189 := bbase (se 4 (by rfl) ⟨433611, by rfl⟩ : syracuseStep 4625189 = 867223) (by norm_num)
theorem B3083459 : Blo 2055435 3083459 := bstep (se 1 (by rfl) ⟨2312594, by rfl⟩ : syracuseStep 3083459 = 4625189) B4625189
theorem B2055639 : Blo 2055435 2055639 := bstep (se 1 (by rfl) ⟨1541729, by rfl⟩ : syracuseStep 2055639 = 3083459) B3083459
theorem B5203349 : Blo 2055435 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B3468899 : Blo 2055435 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B2312599 : Blo 2055435 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B3083465 : Blo 2055435 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B2055643 : Blo 2055435 2055643 := bstep (se 1 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 2055643 = 3083465) B3083465
theorem B4167389 : Blo 2055435 4167389 := bbase (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) (by norm_num)
theorem B11113037 : Blo 2055435 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B7408691 : Blo 2055435 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B4939127 : Blo 2055435 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B3292751 : Blo 2055435 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B8780669 : Blo 2055435 8780669 := bstep (se 3 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 8780669 = 3292751) B3292751
theorem B5853779 : Blo 2055435 5853779 := bstep (se 1 (by rfl) ⟨4390334, by rfl⟩ : syracuseStep 5853779 = 8780669) B8780669
theorem B3902519 : Blo 2055435 3902519 := bstep (se 1 (by rfl) ⟨2926889, by rfl⟩ : syracuseStep 3902519 = 5853779) B5853779
theorem B10406717 : Blo 2055435 10406717 := bstep (se 3 (by rfl) ⟨1951259, by rfl⟩ : syracuseStep 10406717 = 3902519) B3902519
theorem B6937811 : Blo 2055435 6937811 := bstep (se 1 (by rfl) ⟨5203358, by rfl⟩ : syracuseStep 6937811 = 10406717) B10406717
theorem B4625207 : Blo 2055435 4625207 := bstep (se 1 (by rfl) ⟨3468905, by rfl⟩ : syracuseStep 4625207 = 6937811) B6937811
theorem B3083471 : Blo 2055435 3083471 := bstep (se 1 (by rfl) ⟨2312603, by rfl⟩ : syracuseStep 3083471 = 4625207) B4625207
theorem B2055647 : Blo 2055435 2055647 := bstep (se 1 (by rfl) ⟨1541735, by rfl⟩ : syracuseStep 2055647 = 3083471) B3083471
theorem B3083477 : Blo 2055435 3083477 := bbase (se 7 (by rfl) ⟨36134, by rfl⟩ : syracuseStep 3083477 = 72269) (by norm_num)
theorem B2055651 : Blo 2055435 2055651 := bstep (se 1 (by rfl) ⟨1541738, by rfl⟩ : syracuseStep 2055651 = 3083477) B3083477
theorem B2926901 : Blo 2055435 2926901 := bbase (se 5 (by rfl) ⟨137198, by rfl⟩ : syracuseStep 2926901 = 274397) (by norm_num)
theorem B7805069 : Blo 2055435 7805069 := bstep (se 3 (by rfl) ⟨1463450, by rfl⟩ : syracuseStep 7805069 = 2926901) B2926901
theorem B5203379 : Blo 2055435 5203379 := bstep (se 1 (by rfl) ⟨3902534, by rfl⟩ : syracuseStep 5203379 = 7805069) B7805069
theorem B3468919 : Blo 2055435 3468919 := bstep (se 1 (by rfl) ⟨2601689, by rfl⟩ : syracuseStep 3468919 = 5203379) B5203379
theorem B4625225 : Blo 2055435 4625225 := bstep (se 2 (by rfl) ⟨1734459, by rfl⟩ : syracuseStep 4625225 = 3468919) B3468919
theorem B3083483 : Blo 2055435 3083483 := bstep (se 1 (by rfl) ⟨2312612, by rfl⟩ : syracuseStep 3083483 = 4625225) B4625225
theorem B2055655 : Blo 2055435 2055655 := bstep (se 1 (by rfl) ⟨1541741, by rfl⟩ : syracuseStep 2055655 = 3083483) B3083483
theorem B2312617 : Blo 2055435 2312617 := bbase (se 2 (by rfl) ⟨867231, by rfl⟩ : syracuseStep 2312617 = 1734463) (by norm_num)
theorem B3083489 : Blo 2055435 3083489 := bstep (se 2 (by rfl) ⟨1156308, by rfl⟩ : syracuseStep 3083489 = 2312617) B2312617
theorem B2055659 : Blo 2055435 2055659 := bstep (se 1 (by rfl) ⟨1541744, by rfl⟩ : syracuseStep 2055659 = 3083489) B3083489
theorem B4939165 : Blo 2055435 4939165 := bbase (se 3 (by rfl) ⟨926093, by rfl⟩ : syracuseStep 4939165 = 1852187) (by norm_num)
theorem B6585553 : Blo 2055435 6585553 := bstep (se 2 (by rfl) ⟨2469582, by rfl⟩ : syracuseStep 6585553 = 4939165) B4939165
theorem B8780737 : Blo 2055435 8780737 := bstep (se 2 (by rfl) ⟨3292776, by rfl⟩ : syracuseStep 8780737 = 6585553) B6585553
theorem B11707649 : Blo 2055435 11707649 := bstep (se 2 (by rfl) ⟨4390368, by rfl⟩ : syracuseStep 11707649 = 8780737) B8780737
theorem B7805099 : Blo 2055435 7805099 := bstep (se 1 (by rfl) ⟨5853824, by rfl⟩ : syracuseStep 7805099 = 11707649) B11707649
theorem B5203399 : Blo 2055435 5203399 := bstep (se 1 (by rfl) ⟨3902549, by rfl⟩ : syracuseStep 5203399 = 7805099) B7805099
theorem B6937865 : Blo 2055435 6937865 := bstep (se 2 (by rfl) ⟨2601699, by rfl⟩ : syracuseStep 6937865 = 5203399) B5203399
theorem B4625243 : Blo 2055435 4625243 := bstep (se 1 (by rfl) ⟨3468932, by rfl⟩ : syracuseStep 4625243 = 6937865) B6937865
theorem B3083495 : Blo 2055435 3083495 := bstep (se 1 (by rfl) ⟨2312621, by rfl⟩ : syracuseStep 3083495 = 4625243) B4625243
theorem B2055663 : Blo 2055435 2055663 := bstep (se 1 (by rfl) ⟨1541747, by rfl⟩ : syracuseStep 2055663 = 3083495) B3083495
theorem B3083501 : Blo 2055435 3083501 := bbase (se 3 (by rfl) ⟨578156, by rfl⟩ : syracuseStep 3083501 = 1156313) (by norm_num)
theorem B2055667 : Blo 2055435 2055667 := bstep (se 1 (by rfl) ⟨1541750, by rfl⟩ : syracuseStep 2055667 = 3083501) B3083501
theorem B4625261 : Blo 2055435 4625261 := bbase (se 3 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 4625261 = 1734473) (by norm_num)
theorem B3083507 : Blo 2055435 3083507 := bstep (se 1 (by rfl) ⟨2312630, by rfl⟩ : syracuseStep 3083507 = 4625261) B4625261
theorem B2055671 : Blo 2055435 2055671 := bstep (se 1 (by rfl) ⟨1541753, by rfl⟩ : syracuseStep 2055671 = 3083507) B3083507
theorem B3902573 : Blo 2055435 3902573 := bbase (se 3 (by rfl) ⟨731732, by rfl⟩ : syracuseStep 3902573 = 1463465) (by norm_num)
theorem B2601715 : Blo 2055435 2601715 := bstep (se 1 (by rfl) ⟨1951286, by rfl⟩ : syracuseStep 2601715 = 3902573) B3902573
theorem B3468953 : Blo 2055435 3468953 := bstep (se 2 (by rfl) ⟨1300857, by rfl⟩ : syracuseStep 3468953 = 2601715) B2601715
theorem B2312635 : Blo 2055435 2312635 := bstep (se 1 (by rfl) ⟨1734476, by rfl⟩ : syracuseStep 2312635 = 3468953) B3468953
theorem B3083513 : Blo 2055435 3083513 := bstep (se 2 (by rfl) ⟨1156317, by rfl⟩ : syracuseStep 3083513 = 2312635) B2312635
theorem B2055675 : Blo 2055435 2055675 := bstep (se 1 (by rfl) ⟨1541756, by rfl⟩ : syracuseStep 2055675 = 3083513) B3083513
theorem B2966869 : Blo 2055435 2966869 := bbase (se 12 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 2966869 = 2173) (by norm_num)
theorem B3955825 : Blo 2055435 3955825 := bstep (se 2 (by rfl) ⟨1483434, by rfl⟩ : syracuseStep 3955825 = 2966869) B2966869
theorem B5274433 : Blo 2055435 5274433 := bstep (se 2 (by rfl) ⟨1977912, by rfl⟩ : syracuseStep 5274433 = 3955825) B3955825
theorem B7032577 : Blo 2055435 7032577 := bstep (se 2 (by rfl) ⟨2637216, by rfl⟩ : syracuseStep 7032577 = 5274433) B5274433
theorem B9376769 : Blo 2055435 9376769 := bstep (se 2 (by rfl) ⟨3516288, by rfl⟩ : syracuseStep 9376769 = 7032577) B7032577
theorem B6251179 : Blo 2055435 6251179 := bstep (se 1 (by rfl) ⟨4688384, by rfl⟩ : syracuseStep 6251179 = 9376769) B9376769
theorem B8334905 : Blo 2055435 8334905 := bstep (se 2 (by rfl) ⟨3125589, by rfl⟩ : syracuseStep 8334905 = 6251179) B6251179
theorem B22226413 : Blo 2055435 22226413 := bstep (se 3 (by rfl) ⟨4167452, by rfl⟩ : syracuseStep 22226413 = 8334905) B8334905
theorem B29635217 : Blo 2055435 29635217 := bstep (se 2 (by rfl) ⟨11113206, by rfl⟩ : syracuseStep 29635217 = 22226413) B22226413
theorem B19756811 : Blo 2055435 19756811 := bstep (se 1 (by rfl) ⟨14817608, by rfl⟩ : syracuseStep 19756811 = 29635217) B29635217
theorem B52684829 : Blo 2055435 52684829 := bstep (se 3 (by rfl) ⟨9878405, by rfl⟩ : syracuseStep 52684829 = 19756811) B19756811
theorem B35123219 : Blo 2055435 35123219 := bstep (se 1 (by rfl) ⟨26342414, by rfl⟩ : syracuseStep 35123219 = 52684829) B52684829
theorem B23415479 : Blo 2055435 23415479 := bstep (se 1 (by rfl) ⟨17561609, by rfl⟩ : syracuseStep 23415479 = 35123219) B35123219
theorem B15610319 : Blo 2055435 15610319 := bstep (se 1 (by rfl) ⟨11707739, by rfl⟩ : syracuseStep 15610319 = 23415479) B23415479
theorem B10406879 : Blo 2055435 10406879 := bstep (se 1 (by rfl) ⟨7805159, by rfl⟩ : syracuseStep 10406879 = 15610319) B15610319
theorem B6937919 : Blo 2055435 6937919 := bstep (se 1 (by rfl) ⟨5203439, by rfl⟩ : syracuseStep 6937919 = 10406879) B10406879
theorem B4625279 : Blo 2055435 4625279 := bstep (se 1 (by rfl) ⟨3468959, by rfl⟩ : syracuseStep 4625279 = 6937919) B6937919
theorem B3083519 : Blo 2055435 3083519 := bstep (se 1 (by rfl) ⟨2312639, by rfl⟩ : syracuseStep 3083519 = 4625279) B4625279
theorem B2055679 : Blo 2055435 2055679 := bstep (se 1 (by rfl) ⟨1541759, by rfl⟩ : syracuseStep 2055679 = 3083519) B3083519
theorem B3083525 : Blo 2055435 3083525 := bbase (se 4 (by rfl) ⟨289080, by rfl⟩ : syracuseStep 3083525 = 578161) (by norm_num)
theorem B2055683 : Blo 2055435 2055683 := bstep (se 1 (by rfl) ⟨1541762, by rfl⟩ : syracuseStep 2055683 = 3083525) B3083525
theorem B3468973 : Blo 2055435 3468973 := bbase (se 3 (by rfl) ⟨650432, by rfl⟩ : syracuseStep 3468973 = 1300865) (by norm_num)
theorem B4625297 : Blo 2055435 4625297 := bstep (se 2 (by rfl) ⟨1734486, by rfl⟩ : syracuseStep 4625297 = 3468973) B3468973
theorem B3083531 : Blo 2055435 3083531 := bstep (se 1 (by rfl) ⟨2312648, by rfl⟩ : syracuseStep 3083531 = 4625297) B4625297
theorem B2055687 : Blo 2055435 2055687 := bstep (se 1 (by rfl) ⟨1541765, by rfl⟩ : syracuseStep 2055687 = 3083531) B3083531
theorem B2312653 : Blo 2055435 2312653 := bbase (se 3 (by rfl) ⟨433622, by rfl⟩ : syracuseStep 2312653 = 867245) (by norm_num)
theorem B3083537 : Blo 2055435 3083537 := bstep (se 2 (by rfl) ⟨1156326, by rfl⟩ : syracuseStep 3083537 = 2312653) B2312653
theorem B2055691 : Blo 2055435 2055691 := bstep (se 1 (by rfl) ⟨1541768, by rfl⟩ : syracuseStep 2055691 = 3083537) B3083537
theorem B6937973 : Blo 2055435 6937973 := bbase (se 5 (by rfl) ⟨325217, by rfl⟩ : syracuseStep 6937973 = 650435) (by norm_num)
theorem B4625315 : Blo 2055435 4625315 := bstep (se 1 (by rfl) ⟨3468986, by rfl⟩ : syracuseStep 4625315 = 6937973) B6937973
theorem B3083543 : Blo 2055435 3083543 := bstep (se 1 (by rfl) ⟨2312657, by rfl⟩ : syracuseStep 3083543 = 4625315) B4625315
theorem B2055695 : Blo 2055435 2055695 := bstep (se 1 (by rfl) ⟨1541771, by rfl⟩ : syracuseStep 2055695 = 3083543) B3083543
theorem B3083549 : Blo 2055435 3083549 := bbase (se 3 (by rfl) ⟨578165, by rfl⟩ : syracuseStep 3083549 = 1156331) (by norm_num)
theorem B2055699 : Blo 2055435 2055699 := bstep (se 1 (by rfl) ⟨1541774, by rfl⟩ : syracuseStep 2055699 = 3083549) B3083549
theorem B4625333 : Blo 2055435 4625333 := bbase (se 5 (by rfl) ⟨216812, by rfl⟩ : syracuseStep 4625333 = 433625) (by norm_num)
theorem B3083555 : Blo 2055435 3083555 := bstep (se 1 (by rfl) ⟨2312666, by rfl⟩ : syracuseStep 3083555 = 4625333) B4625333
theorem B2055703 : Blo 2055435 2055703 := bstep (se 1 (by rfl) ⟨1541777, by rfl⟩ : syracuseStep 2055703 = 3083555) B3083555
theorem B2344225 : Blo 2055435 2344225 := bbase (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) (by norm_num)
theorem B3125633 : Blo 2055435 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B33340085 : Blo 2055435 33340085 := bstep (se 5 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 33340085 = 3125633) B3125633
theorem B22226723 : Blo 2055435 22226723 := bstep (se 1 (by rfl) ⟨16670042, by rfl⟩ : syracuseStep 22226723 = 33340085) B33340085
theorem B14817815 : Blo 2055435 14817815 := bstep (se 1 (by rfl) ⟨11113361, by rfl⟩ : syracuseStep 14817815 = 22226723) B22226723
theorem B9878543 : Blo 2055435 9878543 := bstep (se 1 (by rfl) ⟨7408907, by rfl⟩ : syracuseStep 9878543 = 14817815) B14817815
theorem B6585695 : Blo 2055435 6585695 := bstep (se 1 (by rfl) ⟨4939271, by rfl⟩ : syracuseStep 6585695 = 9878543) B9878543
theorem B4390463 : Blo 2055435 4390463 := bstep (se 1 (by rfl) ⟨3292847, by rfl⟩ : syracuseStep 4390463 = 6585695) B6585695
theorem B11707901 : Blo 2055435 11707901 := bstep (se 3 (by rfl) ⟨2195231, by rfl⟩ : syracuseStep 11707901 = 4390463) B4390463
theorem B7805267 : Blo 2055435 7805267 := bstep (se 1 (by rfl) ⟨5853950, by rfl⟩ : syracuseStep 7805267 = 11707901) B11707901
theorem B5203511 : Blo 2055435 5203511 := bstep (se 1 (by rfl) ⟨3902633, by rfl⟩ : syracuseStep 5203511 = 7805267) B7805267
theorem B3469007 : Blo 2055435 3469007 := bstep (se 1 (by rfl) ⟨2601755, by rfl⟩ : syracuseStep 3469007 = 5203511) B5203511
theorem B2312671 : Blo 2055435 2312671 := bstep (se 1 (by rfl) ⟨1734503, by rfl⟩ : syracuseStep 2312671 = 3469007) B3469007
theorem B3083561 : Blo 2055435 3083561 := bstep (se 2 (by rfl) ⟨1156335, by rfl⟩ : syracuseStep 3083561 = 2312671) B2312671
theorem B2055707 : Blo 2055435 2055707 := bstep (se 1 (by rfl) ⟨1541780, by rfl⟩ : syracuseStep 2055707 = 3083561) B3083561
theorem B5274517 : Blo 2055435 5274517 := bbase (se 6 (by rfl) ⟨123621, by rfl⟩ : syracuseStep 5274517 = 247243) (by norm_num)
theorem B7032689 : Blo 2055435 7032689 := bstep (se 2 (by rfl) ⟨2637258, by rfl⟩ : syracuseStep 7032689 = 5274517) B5274517
theorem B4688459 : Blo 2055435 4688459 := bstep (se 1 (by rfl) ⟨3516344, by rfl⟩ : syracuseStep 4688459 = 7032689) B7032689
theorem B3125639 : Blo 2055435 3125639 := bstep (se 1 (by rfl) ⟨2344229, by rfl⟩ : syracuseStep 3125639 = 4688459) B4688459
theorem B8335037 : Blo 2055435 8335037 := bstep (se 3 (by rfl) ⟨1562819, by rfl⟩ : syracuseStep 8335037 = 3125639) B3125639
theorem B5556691 : Blo 2055435 5556691 := bstep (se 1 (by rfl) ⟨4167518, by rfl⟩ : syracuseStep 5556691 = 8335037) B8335037
theorem B7408921 : Blo 2055435 7408921 := bstep (se 2 (by rfl) ⟨2778345, by rfl⟩ : syracuseStep 7408921 = 5556691) B5556691
theorem B9878561 : Blo 2055435 9878561 := bstep (se 2 (by rfl) ⟨3704460, by rfl⟩ : syracuseStep 9878561 = 7408921) B7408921
theorem B6585707 : Blo 2055435 6585707 := bstep (se 1 (by rfl) ⟨4939280, by rfl⟩ : syracuseStep 6585707 = 9878561) B9878561
theorem B4390471 : Blo 2055435 4390471 := bstep (se 1 (by rfl) ⟨3292853, by rfl⟩ : syracuseStep 4390471 = 6585707) B6585707
theorem B5853961 : Blo 2055435 5853961 := bstep (se 2 (by rfl) ⟨2195235, by rfl⟩ : syracuseStep 5853961 = 4390471) B4390471
theorem B7805281 : Blo 2055435 7805281 := bstep (se 2 (by rfl) ⟨2926980, by rfl⟩ : syracuseStep 7805281 = 5853961) B5853961
theorem B10407041 : Blo 2055435 10407041 := bstep (se 2 (by rfl) ⟨3902640, by rfl⟩ : syracuseStep 10407041 = 7805281) B7805281
theorem B6938027 : Blo 2055435 6938027 := bstep (se 1 (by rfl) ⟨5203520, by rfl⟩ : syracuseStep 6938027 = 10407041) B10407041
theorem B4625351 : Blo 2055435 4625351 := bstep (se 1 (by rfl) ⟨3469013, by rfl⟩ : syracuseStep 4625351 = 6938027) B6938027
theorem B3083567 : Blo 2055435 3083567 := bstep (se 1 (by rfl) ⟨2312675, by rfl⟩ : syracuseStep 3083567 = 4625351) B4625351
theorem B2055711 : Blo 2055435 2055711 := bstep (se 1 (by rfl) ⟨1541783, by rfl⟩ : syracuseStep 2055711 = 3083567) B3083567
theorem B3083573 : Blo 2055435 3083573 := bbase (se 5 (by rfl) ⟨144542, by rfl⟩ : syracuseStep 3083573 = 289085) (by norm_num)
theorem B2055715 : Blo 2055435 2055715 := bstep (se 1 (by rfl) ⟨1541786, by rfl⟩ : syracuseStep 2055715 = 3083573) B3083573
theorem B5203541 : Blo 2055435 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B3469027 : Blo 2055435 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B4625369 : Blo 2055435 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B3083579 : Blo 2055435 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B2055719 : Blo 2055435 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B2312689 : Blo 2055435 2312689 := bbase (se 2 (by rfl) ⟨867258, by rfl⟩ : syracuseStep 2312689 = 1734517) (by norm_num)
theorem B3083585 : Blo 2055435 3083585 := bstep (se 2 (by rfl) ⟨1156344, by rfl⟩ : syracuseStep 3083585 = 2312689) B2312689
theorem B2055723 : Blo 2055435 2055723 := bstep (se 1 (by rfl) ⟨1541792, by rfl⟩ : syracuseStep 2055723 = 3083585) B3083585
theorem B6014837 : Blo 2055435 6014837 := bbase (se 5 (by rfl) ⟨281945, by rfl⟩ : syracuseStep 6014837 = 563891) (by norm_num)
theorem B16039565 : Blo 2055435 16039565 := bstep (se 3 (by rfl) ⟨3007418, by rfl⟩ : syracuseStep 16039565 = 6014837) B6014837
theorem B10693043 : Blo 2055435 10693043 := bstep (se 1 (by rfl) ⟨8019782, by rfl⟩ : syracuseStep 10693043 = 16039565) B16039565
theorem B7128695 : Blo 2055435 7128695 := bstep (se 1 (by rfl) ⟨5346521, by rfl⟩ : syracuseStep 7128695 = 10693043) B10693043
theorem B19009853 : Blo 2055435 19009853 := bstep (se 3 (by rfl) ⟨3564347, by rfl⟩ : syracuseStep 19009853 = 7128695) B7128695
theorem B12673235 : Blo 2055435 12673235 := bstep (se 1 (by rfl) ⟨9504926, by rfl⟩ : syracuseStep 12673235 = 19009853) B19009853
theorem B8448823 : Blo 2055435 8448823 := bstep (se 1 (by rfl) ⟨6336617, by rfl⟩ : syracuseStep 8448823 = 12673235) B12673235
theorem B11265097 : Blo 2055435 11265097 := bstep (se 2 (by rfl) ⟨4224411, by rfl⟩ : syracuseStep 11265097 = 8448823) B8448823
theorem B15020129 : Blo 2055435 15020129 := bstep (se 2 (by rfl) ⟨5632548, by rfl⟩ : syracuseStep 15020129 = 11265097) B11265097
theorem B10013419 : Blo 2055435 10013419 := bstep (se 1 (by rfl) ⟨7510064, by rfl⟩ : syracuseStep 10013419 = 15020129) B15020129
theorem B13351225 : Blo 2055435 13351225 := bstep (se 2 (by rfl) ⟨5006709, by rfl⟩ : syracuseStep 13351225 = 10013419) B10013419
theorem B17801633 : Blo 2055435 17801633 := bstep (se 2 (by rfl) ⟨6675612, by rfl⟩ : syracuseStep 17801633 = 13351225) B13351225
theorem B47471021 : Blo 2055435 47471021 := bstep (se 3 (by rfl) ⟨8900816, by rfl⟩ : syracuseStep 47471021 = 17801633) B17801633
theorem B31647347 : Blo 2055435 31647347 := bstep (se 1 (by rfl) ⟨23735510, by rfl⟩ : syracuseStep 31647347 = 47471021) B47471021
theorem B21098231 : Blo 2055435 21098231 := bstep (se 1 (by rfl) ⟨15823673, by rfl⟩ : syracuseStep 21098231 = 31647347) B31647347
theorem B14065487 : Blo 2055435 14065487 := bstep (se 1 (by rfl) ⟨10549115, by rfl⟩ : syracuseStep 14065487 = 21098231) B21098231
theorem B9376991 : Blo 2055435 9376991 := bstep (se 1 (by rfl) ⟨7032743, by rfl⟩ : syracuseStep 9376991 = 14065487) B14065487
theorem B6251327 : Blo 2055435 6251327 := bstep (se 1 (by rfl) ⟨4688495, by rfl⟩ : syracuseStep 6251327 = 9376991) B9376991
theorem B4167551 : Blo 2055435 4167551 := bstep (se 1 (by rfl) ⟨3125663, by rfl⟩ : syracuseStep 4167551 = 6251327) B6251327
theorem B11113469 : Blo 2055435 11113469 := bstep (se 3 (by rfl) ⟨2083775, by rfl⟩ : syracuseStep 11113469 = 4167551) B4167551
theorem B7408979 : Blo 2055435 7408979 := bstep (se 1 (by rfl) ⟨5556734, by rfl⟩ : syracuseStep 7408979 = 11113469) B11113469
theorem B4939319 : Blo 2055435 4939319 := bstep (se 1 (by rfl) ⟨3704489, by rfl⟩ : syracuseStep 4939319 = 7408979) B7408979
theorem B13171517 : Blo 2055435 13171517 := bstep (se 3 (by rfl) ⟨2469659, by rfl⟩ : syracuseStep 13171517 = 4939319) B4939319
theorem B8781011 : Blo 2055435 8781011 := bstep (se 1 (by rfl) ⟨6585758, by rfl⟩ : syracuseStep 8781011 = 13171517) B13171517
theorem B5854007 : Blo 2055435 5854007 := bstep (se 1 (by rfl) ⟨4390505, by rfl⟩ : syracuseStep 5854007 = 8781011) B8781011
theorem B3902671 : Blo 2055435 3902671 := bstep (se 1 (by rfl) ⟨2927003, by rfl⟩ : syracuseStep 3902671 = 5854007) B5854007
theorem B5203561 : Blo 2055435 5203561 := bstep (se 2 (by rfl) ⟨1951335, by rfl⟩ : syracuseStep 5203561 = 3902671) B3902671
theorem B6938081 : Blo 2055435 6938081 := bstep (se 2 (by rfl) ⟨2601780, by rfl⟩ : syracuseStep 6938081 = 5203561) B5203561
theorem B4625387 : Blo 2055435 4625387 := bstep (se 1 (by rfl) ⟨3469040, by rfl⟩ : syracuseStep 4625387 = 6938081) B6938081
theorem B3083591 : Blo 2055435 3083591 := bstep (se 1 (by rfl) ⟨2312693, by rfl⟩ : syracuseStep 3083591 = 4625387) B4625387
theorem B2055727 : Blo 2055435 2055727 := bstep (se 1 (by rfl) ⟨1541795, by rfl⟩ : syracuseStep 2055727 = 3083591) B3083591
theorem B3083597 : Blo 2055435 3083597 := bbase (se 3 (by rfl) ⟨578174, by rfl⟩ : syracuseStep 3083597 = 1156349) (by norm_num)
theorem B2055731 : Blo 2055435 2055731 := bstep (se 1 (by rfl) ⟨1541798, by rfl⟩ : syracuseStep 2055731 = 3083597) B3083597
theorem B4625405 : Blo 2055435 4625405 := bbase (se 3 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 4625405 = 1734527) (by norm_num)
theorem B3083603 : Blo 2055435 3083603 := bstep (se 1 (by rfl) ⟨2312702, by rfl⟩ : syracuseStep 3083603 = 4625405) B4625405
theorem B2055735 : Blo 2055435 2055735 := bstep (se 1 (by rfl) ⟨1541801, by rfl⟩ : syracuseStep 2055735 = 3083603) B3083603
theorem B3469061 : Blo 2055435 3469061 := bbase (se 4 (by rfl) ⟨325224, by rfl⟩ : syracuseStep 3469061 = 650449) (by norm_num)
theorem B2312707 : Blo 2055435 2312707 := bstep (se 1 (by rfl) ⟨1734530, by rfl⟩ : syracuseStep 2312707 = 3469061) B3469061
theorem B3083609 : Blo 2055435 3083609 := bstep (se 2 (by rfl) ⟨1156353, by rfl⟩ : syracuseStep 3083609 = 2312707) B2312707
theorem B2055739 : Blo 2055435 2055739 := bstep (se 1 (by rfl) ⟨1541804, by rfl⟩ : syracuseStep 2055739 = 3083609) B3083609
theorem B15610805 : Blo 2055435 15610805 := bbase (se 5 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 15610805 = 1463513) (by norm_num)
theorem B10407203 : Blo 2055435 10407203 := bstep (se 1 (by rfl) ⟨7805402, by rfl⟩ : syracuseStep 10407203 = 15610805) B15610805
theorem B6938135 : Blo 2055435 6938135 := bstep (se 1 (by rfl) ⟨5203601, by rfl⟩ : syracuseStep 6938135 = 10407203) B10407203
theorem B4625423 : Blo 2055435 4625423 := bstep (se 1 (by rfl) ⟨3469067, by rfl⟩ : syracuseStep 4625423 = 6938135) B6938135
theorem B3083615 : Blo 2055435 3083615 := bstep (se 1 (by rfl) ⟨2312711, by rfl⟩ : syracuseStep 3083615 = 4625423) B4625423
theorem B2055743 : Blo 2055435 2055743 := bstep (se 1 (by rfl) ⟨1541807, by rfl⟩ : syracuseStep 2055743 = 3083615) B3083615
theorem B3083621 : Blo 2055435 3083621 := bbase (se 4 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 3083621 = 578179) (by norm_num)
theorem B2055747 : Blo 2055435 2055747 := bstep (se 1 (by rfl) ⟨1541810, by rfl⟩ : syracuseStep 2055747 = 3083621) B3083621
theorem B3902717 : Blo 2055435 3902717 := bbase (se 3 (by rfl) ⟨731759, by rfl⟩ : syracuseStep 3902717 = 1463519) (by norm_num)
theorem B2601811 : Blo 2055435 2601811 := bstep (se 1 (by rfl) ⟨1951358, by rfl⟩ : syracuseStep 2601811 = 3902717) B3902717
theorem B3469081 : Blo 2055435 3469081 := bstep (se 2 (by rfl) ⟨1300905, by rfl⟩ : syracuseStep 3469081 = 2601811) B2601811
theorem B4625441 : Blo 2055435 4625441 := bstep (se 2 (by rfl) ⟨1734540, by rfl⟩ : syracuseStep 4625441 = 3469081) B3469081
theorem B3083627 : Blo 2055435 3083627 := bstep (se 1 (by rfl) ⟨2312720, by rfl⟩ : syracuseStep 3083627 = 4625441) B4625441
theorem B2055751 : Blo 2055435 2055751 := bstep (se 1 (by rfl) ⟨1541813, by rfl⟩ : syracuseStep 2055751 = 3083627) B3083627
theorem B2312725 : Blo 2055435 2312725 := bbase (se 6 (by rfl) ⟨54204, by rfl⟩ : syracuseStep 2312725 = 108409) (by norm_num)
theorem B3083633 : Blo 2055435 3083633 := bstep (se 2 (by rfl) ⟨1156362, by rfl⟩ : syracuseStep 3083633 = 2312725) B2312725
theorem B2055755 : Blo 2055435 2055755 := bstep (se 1 (by rfl) ⟨1541816, by rfl⟩ : syracuseStep 2055755 = 3083633) B3083633
theorem B2601821 : Blo 2055435 2601821 := bbase (se 3 (by rfl) ⟨487841, by rfl⟩ : syracuseStep 2601821 = 975683) (by norm_num)
theorem B6938189 : Blo 2055435 6938189 := bstep (se 3 (by rfl) ⟨1300910, by rfl⟩ : syracuseStep 6938189 = 2601821) B2601821
theorem B4625459 : Blo 2055435 4625459 := bstep (se 1 (by rfl) ⟨3469094, by rfl⟩ : syracuseStep 4625459 = 6938189) B6938189
theorem B3083639 : Blo 2055435 3083639 := bstep (se 1 (by rfl) ⟨2312729, by rfl⟩ : syracuseStep 3083639 = 4625459) B4625459
theorem B2055759 : Blo 2055435 2055759 := bstep (se 1 (by rfl) ⟨1541819, by rfl⟩ : syracuseStep 2055759 = 3083639) B3083639
theorem B3083645 : Blo 2055435 3083645 := bbase (se 3 (by rfl) ⟨578183, by rfl⟩ : syracuseStep 3083645 = 1156367) (by norm_num)
theorem B2055763 : Blo 2055435 2055763 := bstep (se 1 (by rfl) ⟨1541822, by rfl⟩ : syracuseStep 2055763 = 3083645) B3083645
theorem B4625477 : Blo 2055435 4625477 := bbase (se 4 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 4625477 = 867277) (by norm_num)
theorem B3083651 : Blo 2055435 3083651 := bstep (se 1 (by rfl) ⟨2312738, by rfl⟩ : syracuseStep 3083651 = 4625477) B4625477
theorem B2055767 : Blo 2055435 2055767 := bstep (se 1 (by rfl) ⟨1541825, by rfl⟩ : syracuseStep 2055767 = 3083651) B3083651
theorem B5854133 : Blo 2055435 5854133 := bbase (se 5 (by rfl) ⟨274412, by rfl⟩ : syracuseStep 5854133 = 548825) (by norm_num)
theorem B3902755 : Blo 2055435 3902755 := bstep (se 1 (by rfl) ⟨2927066, by rfl⟩ : syracuseStep 3902755 = 5854133) B5854133
theorem B5203673 : Blo 2055435 5203673 := bstep (se 2 (by rfl) ⟨1951377, by rfl⟩ : syracuseStep 5203673 = 3902755) B3902755
theorem B3469115 : Blo 2055435 3469115 := bstep (se 1 (by rfl) ⟨2601836, by rfl⟩ : syracuseStep 3469115 = 5203673) B5203673
theorem B2312743 : Blo 2055435 2312743 := bstep (se 1 (by rfl) ⟨1734557, by rfl⟩ : syracuseStep 2312743 = 3469115) B3469115
theorem B3083657 : Blo 2055435 3083657 := bstep (se 2 (by rfl) ⟨1156371, by rfl⟩ : syracuseStep 3083657 = 2312743) B2312743
theorem B2055771 : Blo 2055435 2055771 := bstep (se 1 (by rfl) ⟨1541828, by rfl⟩ : syracuseStep 2055771 = 3083657) B3083657
theorem B10407365 : Blo 2055435 10407365 := bbase (se 4 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 10407365 = 1951381) (by norm_num)
theorem B6938243 : Blo 2055435 6938243 := bstep (se 1 (by rfl) ⟨5203682, by rfl⟩ : syracuseStep 6938243 = 10407365) B10407365
theorem B4625495 : Blo 2055435 4625495 := bstep (se 1 (by rfl) ⟨3469121, by rfl⟩ : syracuseStep 4625495 = 6938243) B6938243
theorem B3083663 : Blo 2055435 3083663 := bstep (se 1 (by rfl) ⟨2312747, by rfl⟩ : syracuseStep 3083663 = 4625495) B4625495
theorem B2055775 : Blo 2055435 2055775 := bstep (se 1 (by rfl) ⟨1541831, by rfl⟩ : syracuseStep 2055775 = 3083663) B3083663
theorem B3083669 : Blo 2055435 3083669 := bbase (se 6 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 3083669 = 144547) (by norm_num)
theorem B2055779 : Blo 2055435 2055779 := bstep (se 1 (by rfl) ⟨1541834, by rfl⟩ : syracuseStep 2055779 = 3083669) B3083669
theorem B12502997 : Blo 2055435 12502997 := bbase (se 7 (by rfl) ⟨146519, by rfl⟩ : syracuseStep 12502997 = 293039) (by norm_num)
theorem B8335331 : Blo 2055435 8335331 := bstep (se 1 (by rfl) ⟨6251498, by rfl⟩ : syracuseStep 8335331 = 12502997) B12502997
theorem B5556887 : Blo 2055435 5556887 := bstep (se 1 (by rfl) ⟨4167665, by rfl⟩ : syracuseStep 5556887 = 8335331) B8335331
theorem B3704591 : Blo 2055435 3704591 := bstep (se 1 (by rfl) ⟨2778443, by rfl⟩ : syracuseStep 3704591 = 5556887) B5556887
theorem B2469727 : Blo 2055435 2469727 := bstep (se 1 (by rfl) ⟨1852295, by rfl⟩ : syracuseStep 2469727 = 3704591) B3704591
theorem B3292969 : Blo 2055435 3292969 := bstep (se 2 (by rfl) ⟨1234863, by rfl⟩ : syracuseStep 3292969 = 2469727) B2469727
theorem B4390625 : Blo 2055435 4390625 := bstep (se 2 (by rfl) ⟨1646484, by rfl⟩ : syracuseStep 4390625 = 3292969) B3292969
theorem B11708333 : Blo 2055435 11708333 := bstep (se 3 (by rfl) ⟨2195312, by rfl⟩ : syracuseStep 11708333 = 4390625) B4390625
theorem B7805555 : Blo 2055435 7805555 := bstep (se 1 (by rfl) ⟨5854166, by rfl⟩ : syracuseStep 7805555 = 11708333) B11708333
theorem B5203703 : Blo 2055435 5203703 := bstep (se 1 (by rfl) ⟨3902777, by rfl⟩ : syracuseStep 5203703 = 7805555) B7805555
theorem B3469135 : Blo 2055435 3469135 := bstep (se 1 (by rfl) ⟨2601851, by rfl⟩ : syracuseStep 3469135 = 5203703) B5203703
theorem B4625513 : Blo 2055435 4625513 := bstep (se 2 (by rfl) ⟨1734567, by rfl⟩ : syracuseStep 4625513 = 3469135) B3469135
theorem B3083675 : Blo 2055435 3083675 := bstep (se 1 (by rfl) ⟨2312756, by rfl⟩ : syracuseStep 3083675 = 4625513) B4625513
theorem B2055783 : Blo 2055435 2055783 := bstep (se 1 (by rfl) ⟨1541837, by rfl⟩ : syracuseStep 2055783 = 3083675) B3083675
theorem B2312761 : Blo 2055435 2312761 := bbase (se 2 (by rfl) ⟨867285, by rfl⟩ : syracuseStep 2312761 = 1734571) (by norm_num)
theorem B3083681 : Blo 2055435 3083681 := bstep (se 2 (by rfl) ⟨1156380, by rfl⟩ : syracuseStep 3083681 = 2312761) B2312761
theorem B2055787 : Blo 2055435 2055787 := bstep (se 1 (by rfl) ⟨1541840, by rfl⟩ : syracuseStep 2055787 = 3083681) B3083681
theorem B2195321 : Blo 2055435 2195321 := bbase (se 2 (by rfl) ⟨823245, by rfl⟩ : syracuseStep 2195321 = 1646491) (by norm_num)
theorem B5854189 : Blo 2055435 5854189 := bstep (se 3 (by rfl) ⟨1097660, by rfl⟩ : syracuseStep 5854189 = 2195321) B2195321
theorem B7805585 : Blo 2055435 7805585 := bstep (se 2 (by rfl) ⟨2927094, by rfl⟩ : syracuseStep 7805585 = 5854189) B5854189
theorem B5203723 : Blo 2055435 5203723 := bstep (se 1 (by rfl) ⟨3902792, by rfl⟩ : syracuseStep 5203723 = 7805585) B7805585
theorem B6938297 : Blo 2055435 6938297 := bstep (se 2 (by rfl) ⟨2601861, by rfl⟩ : syracuseStep 6938297 = 5203723) B5203723
theorem B4625531 : Blo 2055435 4625531 := bstep (se 1 (by rfl) ⟨3469148, by rfl⟩ : syracuseStep 4625531 = 6938297) B6938297
theorem B3083687 : Blo 2055435 3083687 := bstep (se 1 (by rfl) ⟨2312765, by rfl⟩ : syracuseStep 3083687 = 4625531) B4625531
theorem B2055791 : Blo 2055435 2055791 := bstep (se 1 (by rfl) ⟨1541843, by rfl⟩ : syracuseStep 2055791 = 3083687) B3083687
theorem B3083693 : Blo 2055435 3083693 := bbase (se 3 (by rfl) ⟨578192, by rfl⟩ : syracuseStep 3083693 = 1156385) (by norm_num)
theorem B2055795 : Blo 2055435 2055795 := bstep (se 1 (by rfl) ⟨1541846, by rfl⟩ : syracuseStep 2055795 = 3083693) B3083693
theorem B4625549 : Blo 2055435 4625549 := bbase (se 3 (by rfl) ⟨867290, by rfl⟩ : syracuseStep 4625549 = 1734581) (by norm_num)
theorem B3083699 : Blo 2055435 3083699 := bstep (se 1 (by rfl) ⟨2312774, by rfl⟩ : syracuseStep 3083699 = 4625549) B4625549
theorem B2055799 : Blo 2055435 2055799 := bstep (se 1 (by rfl) ⟨1541849, by rfl⟩ : syracuseStep 2055799 = 3083699) B3083699
theorem B2601877 : Blo 2055435 2601877 := bbase (se 6 (by rfl) ⟨60981, by rfl⟩ : syracuseStep 2601877 = 121963) (by norm_num)
theorem B3469169 : Blo 2055435 3469169 := bstep (se 2 (by rfl) ⟨1300938, by rfl⟩ : syracuseStep 3469169 = 2601877) B2601877
theorem B2312779 : Blo 2055435 2312779 := bstep (se 1 (by rfl) ⟨1734584, by rfl⟩ : syracuseStep 2312779 = 3469169) B3469169
theorem B3083705 : Blo 2055435 3083705 := bstep (se 2 (by rfl) ⟨1156389, by rfl⟩ : syracuseStep 3083705 = 2312779) B2312779
theorem B2055803 : Blo 2055435 2055803 := bstep (se 1 (by rfl) ⟨1541852, by rfl⟩ : syracuseStep 2055803 = 3083705) B3083705
theorem B22227797 : Blo 2055435 22227797 := bbase (se 9 (by rfl) ⟨65120, by rfl⟩ : syracuseStep 22227797 = 130241) (by norm_num)
theorem B59274125 : Blo 2055435 59274125 := bstep (se 3 (by rfl) ⟨11113898, by rfl⟩ : syracuseStep 59274125 = 22227797) B22227797
theorem B39516083 : Blo 2055435 39516083 := bstep (se 1 (by rfl) ⟨29637062, by rfl⟩ : syracuseStep 39516083 = 59274125) B59274125
theorem B26344055 : Blo 2055435 26344055 := bstep (se 1 (by rfl) ⟨19758041, by rfl⟩ : syracuseStep 26344055 = 39516083) B39516083
theorem B17562703 : Blo 2055435 17562703 := bstep (se 1 (by rfl) ⟨13172027, by rfl⟩ : syracuseStep 17562703 = 26344055) B26344055
theorem B23416937 : Blo 2055435 23416937 := bstep (se 2 (by rfl) ⟨8781351, by rfl⟩ : syracuseStep 23416937 = 17562703) B17562703
theorem B15611291 : Blo 2055435 15611291 := bstep (se 1 (by rfl) ⟨11708468, by rfl⟩ : syracuseStep 15611291 = 23416937) B23416937
theorem B10407527 : Blo 2055435 10407527 := bstep (se 1 (by rfl) ⟨7805645, by rfl⟩ : syracuseStep 10407527 = 15611291) B15611291
theorem B6938351 : Blo 2055435 6938351 := bstep (se 1 (by rfl) ⟨5203763, by rfl⟩ : syracuseStep 6938351 = 10407527) B10407527
theorem B4625567 : Blo 2055435 4625567 := bstep (se 1 (by rfl) ⟨3469175, by rfl⟩ : syracuseStep 4625567 = 6938351) B6938351
theorem B3083711 : Blo 2055435 3083711 := bstep (se 1 (by rfl) ⟨2312783, by rfl⟩ : syracuseStep 3083711 = 4625567) B4625567
theorem B2055807 : Blo 2055435 2055807 := bstep (se 1 (by rfl) ⟨1541855, by rfl⟩ : syracuseStep 2055807 = 3083711) B3083711
theorem B3083717 : Blo 2055435 3083717 := bbase (se 4 (by rfl) ⟨289098, by rfl⟩ : syracuseStep 3083717 = 578197) (by norm_num)
theorem B2055811 : Blo 2055435 2055811 := bstep (se 1 (by rfl) ⟨1541858, by rfl⟩ : syracuseStep 2055811 = 3083717) B3083717
theorem B3469189 : Blo 2055435 3469189 := bbase (se 4 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 3469189 = 650473) (by norm_num)
theorem B4625585 : Blo 2055435 4625585 := bstep (se 2 (by rfl) ⟨1734594, by rfl⟩ : syracuseStep 4625585 = 3469189) B3469189
theorem B3083723 : Blo 2055435 3083723 := bstep (se 1 (by rfl) ⟨2312792, by rfl⟩ : syracuseStep 3083723 = 4625585) B4625585
theorem B2055815 : Blo 2055435 2055815 := bstep (se 1 (by rfl) ⟨1541861, by rfl⟩ : syracuseStep 2055815 = 3083723) B3083723
theorem B2312797 : Blo 2055435 2312797 := bbase (se 3 (by rfl) ⟨433649, by rfl⟩ : syracuseStep 2312797 = 867299) (by norm_num)
theorem B3083729 : Blo 2055435 3083729 := bstep (se 2 (by rfl) ⟨1156398, by rfl⟩ : syracuseStep 3083729 = 2312797) B2312797
theorem B2055819 : Blo 2055435 2055819 := bstep (se 1 (by rfl) ⟨1541864, by rfl⟩ : syracuseStep 2055819 = 3083729) B3083729
theorem B6938405 : Blo 2055435 6938405 := bbase (se 4 (by rfl) ⟨650475, by rfl⟩ : syracuseStep 6938405 = 1300951) (by norm_num)
theorem B4625603 : Blo 2055435 4625603 := bstep (se 1 (by rfl) ⟨3469202, by rfl⟩ : syracuseStep 4625603 = 6938405) B6938405
theorem B3083735 : Blo 2055435 3083735 := bstep (se 1 (by rfl) ⟨2312801, by rfl⟩ : syracuseStep 3083735 = 4625603) B4625603
theorem B2055823 : Blo 2055435 2055823 := bstep (se 1 (by rfl) ⟨1541867, by rfl⟩ : syracuseStep 2055823 = 3083735) B3083735
theorem B3083741 : Blo 2055435 3083741 := bbase (se 3 (by rfl) ⟨578201, by rfl⟩ : syracuseStep 3083741 = 1156403) (by norm_num)
theorem B2055827 : Blo 2055435 2055827 := bstep (se 1 (by rfl) ⟨1541870, by rfl⟩ : syracuseStep 2055827 = 3083741) B3083741
theorem B4625621 : Blo 2055435 4625621 := bbase (se 7 (by rfl) ⟨54206, by rfl⟩ : syracuseStep 4625621 = 108413) (by norm_num)
theorem B3083747 : Blo 2055435 3083747 := bstep (se 1 (by rfl) ⟨2312810, by rfl⟩ : syracuseStep 3083747 = 4625621) B4625621
theorem B2055831 : Blo 2055435 2055831 := bstep (se 1 (by rfl) ⟨1541873, by rfl⟩ : syracuseStep 2055831 = 3083747) B3083747
theorem B8335541 : Blo 2055435 8335541 := bbase (se 5 (by rfl) ⟨390728, by rfl⟩ : syracuseStep 8335541 = 781457) (by norm_num)
theorem B5557027 : Blo 2055435 5557027 := bstep (se 1 (by rfl) ⟨4167770, by rfl⟩ : syracuseStep 5557027 = 8335541) B8335541
theorem B7409369 : Blo 2055435 7409369 := bstep (se 2 (by rfl) ⟨2778513, by rfl⟩ : syracuseStep 7409369 = 5557027) B5557027
theorem B4939579 : Blo 2055435 4939579 := bstep (se 1 (by rfl) ⟨3704684, by rfl⟩ : syracuseStep 4939579 = 7409369) B7409369
theorem B6586105 : Blo 2055435 6586105 := bstep (se 2 (by rfl) ⟨2469789, by rfl⟩ : syracuseStep 6586105 = 4939579) B4939579
theorem B8781473 : Blo 2055435 8781473 := bstep (se 2 (by rfl) ⟨3293052, by rfl⟩ : syracuseStep 8781473 = 6586105) B6586105
theorem B5854315 : Blo 2055435 5854315 := bstep (se 1 (by rfl) ⟨4390736, by rfl⟩ : syracuseStep 5854315 = 8781473) B8781473
theorem B7805753 : Blo 2055435 7805753 := bstep (se 2 (by rfl) ⟨2927157, by rfl⟩ : syracuseStep 7805753 = 5854315) B5854315
theorem B5203835 : Blo 2055435 5203835 := bstep (se 1 (by rfl) ⟨3902876, by rfl⟩ : syracuseStep 5203835 = 7805753) B7805753
theorem B3469223 : Blo 2055435 3469223 := bstep (se 1 (by rfl) ⟨2601917, by rfl⟩ : syracuseStep 3469223 = 5203835) B5203835
theorem B2312815 : Blo 2055435 2312815 := bstep (se 1 (by rfl) ⟨1734611, by rfl⟩ : syracuseStep 2312815 = 3469223) B3469223
theorem B3083753 : Blo 2055435 3083753 := bstep (se 2 (by rfl) ⟨1156407, by rfl⟩ : syracuseStep 3083753 = 2312815) B2312815
theorem B2055835 : Blo 2055435 2055835 := bstep (se 1 (by rfl) ⟨1541876, by rfl⟩ : syracuseStep 2055835 = 3083753) B3083753
theorem B5274845 : Blo 2055435 5274845 := bbase (se 3 (by rfl) ⟨989033, by rfl⟩ : syracuseStep 5274845 = 1978067) (by norm_num)
theorem B3516563 : Blo 2055435 3516563 := bstep (se 1 (by rfl) ⟨2637422, by rfl⟩ : syracuseStep 3516563 = 5274845) B5274845
theorem B2344375 : Blo 2055435 2344375 := bstep (se 1 (by rfl) ⟨1758281, by rfl⟩ : syracuseStep 2344375 = 3516563) B3516563
theorem B3125833 : Blo 2055435 3125833 := bstep (se 2 (by rfl) ⟨1172187, by rfl⟩ : syracuseStep 3125833 = 2344375) B2344375
theorem B16671109 : Blo 2055435 16671109 := bstep (se 4 (by rfl) ⟨1562916, by rfl⟩ : syracuseStep 16671109 = 3125833) B3125833
theorem B22228145 : Blo 2055435 22228145 := bstep (se 2 (by rfl) ⟨8335554, by rfl⟩ : syracuseStep 22228145 = 16671109) B16671109
theorem B14818763 : Blo 2055435 14818763 := bstep (se 1 (by rfl) ⟨11114072, by rfl⟩ : syracuseStep 14818763 = 22228145) B22228145
theorem B9879175 : Blo 2055435 9879175 := bstep (se 1 (by rfl) ⟨7409381, by rfl⟩ : syracuseStep 9879175 = 14818763) B14818763
theorem B13172233 : Blo 2055435 13172233 := bstep (se 2 (by rfl) ⟨4939587, by rfl⟩ : syracuseStep 13172233 = 9879175) B9879175
theorem B17562977 : Blo 2055435 17562977 := bstep (se 2 (by rfl) ⟨6586116, by rfl⟩ : syracuseStep 17562977 = 13172233) B13172233
theorem B11708651 : Blo 2055435 11708651 := bstep (se 1 (by rfl) ⟨8781488, by rfl⟩ : syracuseStep 11708651 = 17562977) B17562977
theorem B7805767 : Blo 2055435 7805767 := bstep (se 1 (by rfl) ⟨5854325, by rfl⟩ : syracuseStep 7805767 = 11708651) B11708651
theorem B10407689 : Blo 2055435 10407689 := bstep (se 2 (by rfl) ⟨3902883, by rfl⟩ : syracuseStep 10407689 = 7805767) B7805767
theorem B6938459 : Blo 2055435 6938459 := bstep (se 1 (by rfl) ⟨5203844, by rfl⟩ : syracuseStep 6938459 = 10407689) B10407689
theorem B4625639 : Blo 2055435 4625639 := bstep (se 1 (by rfl) ⟨3469229, by rfl⟩ : syracuseStep 4625639 = 6938459) B6938459
theorem B3083759 : Blo 2055435 3083759 := bstep (se 1 (by rfl) ⟨2312819, by rfl⟩ : syracuseStep 3083759 = 4625639) B4625639
theorem B2055839 : Blo 2055435 2055839 := bstep (se 1 (by rfl) ⟨1541879, by rfl⟩ : syracuseStep 2055839 = 3083759) B3083759
theorem B3083765 : Blo 2055435 3083765 := bbase (se 5 (by rfl) ⟨144551, by rfl⟩ : syracuseStep 3083765 = 289103) (by norm_num)
theorem B2055843 : Blo 2055435 2055843 := bstep (se 1 (by rfl) ⟨1541882, by rfl⟩ : syracuseStep 2055843 = 3083765) B3083765
theorem B2195381 : Blo 2055435 2195381 := bbase (se 5 (by rfl) ⟨102908, by rfl⟩ : syracuseStep 2195381 = 205817) (by norm_num)
theorem B5854349 : Blo 2055435 5854349 := bstep (se 3 (by rfl) ⟨1097690, by rfl⟩ : syracuseStep 5854349 = 2195381) B2195381
theorem B3902899 : Blo 2055435 3902899 := bstep (se 1 (by rfl) ⟨2927174, by rfl⟩ : syracuseStep 3902899 = 5854349) B5854349
theorem B5203865 : Blo 2055435 5203865 := bstep (se 2 (by rfl) ⟨1951449, by rfl⟩ : syracuseStep 5203865 = 3902899) B3902899
theorem B3469243 : Blo 2055435 3469243 := bstep (se 1 (by rfl) ⟨2601932, by rfl⟩ : syracuseStep 3469243 = 5203865) B5203865
theorem B4625657 : Blo 2055435 4625657 := bstep (se 2 (by rfl) ⟨1734621, by rfl⟩ : syracuseStep 4625657 = 3469243) B3469243
theorem B3083771 : Blo 2055435 3083771 := bstep (se 1 (by rfl) ⟨2312828, by rfl⟩ : syracuseStep 3083771 = 4625657) B4625657
theorem B2055847 : Blo 2055435 2055847 := bstep (se 1 (by rfl) ⟨1541885, by rfl⟩ : syracuseStep 2055847 = 3083771) B3083771
theorem B2312833 : Blo 2055435 2312833 := bbase (se 2 (by rfl) ⟨867312, by rfl⟩ : syracuseStep 2312833 = 1734625) (by norm_num)
theorem B3083777 : Blo 2055435 3083777 := bstep (se 2 (by rfl) ⟨1156416, by rfl⟩ : syracuseStep 3083777 = 2312833) B2312833
theorem B2055851 : Blo 2055435 2055851 := bstep (se 1 (by rfl) ⟨1541888, by rfl⟩ : syracuseStep 2055851 = 3083777) B3083777
theorem B5203885 : Blo 2055435 5203885 := bbase (se 3 (by rfl) ⟨975728, by rfl⟩ : syracuseStep 5203885 = 1951457) (by norm_num)
theorem B6938513 : Blo 2055435 6938513 := bstep (se 2 (by rfl) ⟨2601942, by rfl⟩ : syracuseStep 6938513 = 5203885) B5203885
theorem B4625675 : Blo 2055435 4625675 := bstep (se 1 (by rfl) ⟨3469256, by rfl⟩ : syracuseStep 4625675 = 6938513) B6938513
theorem B3083783 : Blo 2055435 3083783 := bstep (se 1 (by rfl) ⟨2312837, by rfl⟩ : syracuseStep 3083783 = 4625675) B4625675
theorem B2055855 : Blo 2055435 2055855 := bstep (se 1 (by rfl) ⟨1541891, by rfl⟩ : syracuseStep 2055855 = 3083783) B3083783
theorem B3083789 : Blo 2055435 3083789 := bbase (se 3 (by rfl) ⟨578210, by rfl⟩ : syracuseStep 3083789 = 1156421) (by norm_num)
theorem B2055859 : Blo 2055435 2055859 := bstep (se 1 (by rfl) ⟨1541894, by rfl⟩ : syracuseStep 2055859 = 3083789) B3083789
theorem B4625693 : Blo 2055435 4625693 := bbase (se 3 (by rfl) ⟨867317, by rfl⟩ : syracuseStep 4625693 = 1734635) (by norm_num)
theorem B3083795 : Blo 2055435 3083795 := bstep (se 1 (by rfl) ⟨2312846, by rfl⟩ : syracuseStep 3083795 = 4625693) B4625693
theorem B2055863 : Blo 2055435 2055863 := bstep (se 1 (by rfl) ⟨1541897, by rfl⟩ : syracuseStep 2055863 = 3083795) B3083795
theorem B3469277 : Blo 2055435 3469277 := bbase (se 3 (by rfl) ⟨650489, by rfl⟩ : syracuseStep 3469277 = 1300979) (by norm_num)
theorem B2312851 : Blo 2055435 2312851 := bstep (se 1 (by rfl) ⟨1734638, by rfl⟩ : syracuseStep 2312851 = 3469277) B3469277
theorem B3083801 : Blo 2055435 3083801 := bstep (se 2 (by rfl) ⟨1156425, by rfl⟩ : syracuseStep 3083801 = 2312851) B2312851
theorem B2055867 : Blo 2055435 2055867 := bstep (se 1 (by rfl) ⟨1541900, by rfl⟩ : syracuseStep 2055867 = 3083801) B3083801
theorem B8335685 : Blo 2055435 8335685 := bbase (se 4 (by rfl) ⟨781470, by rfl⟩ : syracuseStep 8335685 = 1562941) (by norm_num)
theorem B5557123 : Blo 2055435 5557123 := bstep (se 1 (by rfl) ⟨4167842, by rfl⟩ : syracuseStep 5557123 = 8335685) B8335685
theorem B7409497 : Blo 2055435 7409497 := bstep (se 2 (by rfl) ⟨2778561, by rfl⟩ : syracuseStep 7409497 = 5557123) B5557123
theorem B9879329 : Blo 2055435 9879329 := bstep (se 2 (by rfl) ⟨3704748, by rfl⟩ : syracuseStep 9879329 = 7409497) B7409497
theorem B6586219 : Blo 2055435 6586219 := bstep (se 1 (by rfl) ⟨4939664, by rfl⟩ : syracuseStep 6586219 = 9879329) B9879329
theorem B8781625 : Blo 2055435 8781625 := bstep (se 2 (by rfl) ⟨3293109, by rfl⟩ : syracuseStep 8781625 = 6586219) B6586219
theorem B11708833 : Blo 2055435 11708833 := bstep (se 2 (by rfl) ⟨4390812, by rfl⟩ : syracuseStep 11708833 = 8781625) B8781625
theorem B15611777 : Blo 2055435 15611777 := bstep (se 2 (by rfl) ⟨5854416, by rfl⟩ : syracuseStep 15611777 = 11708833) B11708833
theorem B10407851 : Blo 2055435 10407851 := bstep (se 1 (by rfl) ⟨7805888, by rfl⟩ : syracuseStep 10407851 = 15611777) B15611777
theorem B6938567 : Blo 2055435 6938567 := bstep (se 1 (by rfl) ⟨5203925, by rfl⟩ : syracuseStep 6938567 = 10407851) B10407851
theorem B4625711 : Blo 2055435 4625711 := bstep (se 1 (by rfl) ⟨3469283, by rfl⟩ : syracuseStep 4625711 = 6938567) B6938567
theorem B3083807 : Blo 2055435 3083807 := bstep (se 1 (by rfl) ⟨2312855, by rfl⟩ : syracuseStep 3083807 = 4625711) B4625711
theorem B2055871 : Blo 2055435 2055871 := bstep (se 1 (by rfl) ⟨1541903, by rfl⟩ : syracuseStep 2055871 = 3083807) B3083807
theorem B3083813 : Blo 2055435 3083813 := bbase (se 4 (by rfl) ⟨289107, by rfl⟩ : syracuseStep 3083813 = 578215) (by norm_num)
theorem B2055875 : Blo 2055435 2055875 := bstep (se 1 (by rfl) ⟨1541906, by rfl⟩ : syracuseStep 2055875 = 3083813) B3083813
theorem B2601973 : Blo 2055435 2601973 := bbase (se 5 (by rfl) ⟨121967, by rfl⟩ : syracuseStep 2601973 = 243935) (by norm_num)
theorem B3469297 : Blo 2055435 3469297 := bstep (se 2 (by rfl) ⟨1300986, by rfl⟩ : syracuseStep 3469297 = 2601973) B2601973
theorem B4625729 : Blo 2055435 4625729 := bstep (se 2 (by rfl) ⟨1734648, by rfl⟩ : syracuseStep 4625729 = 3469297) B3469297
theorem B3083819 : Blo 2055435 3083819 := bstep (se 1 (by rfl) ⟨2312864, by rfl⟩ : syracuseStep 3083819 = 4625729) B4625729
theorem B2055879 : Blo 2055435 2055879 := bstep (se 1 (by rfl) ⟨1541909, by rfl⟩ : syracuseStep 2055879 = 3083819) B3083819
theorem B2312869 : Blo 2055435 2312869 := bbase (se 4 (by rfl) ⟨216831, by rfl⟩ : syracuseStep 2312869 = 433663) (by norm_num)
theorem B3083825 : Blo 2055435 3083825 := bstep (se 2 (by rfl) ⟨1156434, by rfl⟩ : syracuseStep 3083825 = 2312869) B2312869
theorem B2055883 : Blo 2055435 2055883 := bstep (se 1 (by rfl) ⟨1541912, by rfl⟩ : syracuseStep 2055883 = 3083825) B3083825
theorem B2225377 : Blo 2055435 2225377 := bbase (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) (by norm_num)
theorem B11868677 : Blo 2055435 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B7912451 : Blo 2055435 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B21099869 : Blo 2055435 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B14066579 : Blo 2055435 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B37510877 : Blo 2055435 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B100029005 : Blo 2055435 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B66686003 : Blo 2055435 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B44457335 : Blo 2055435 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B29638223 : Blo 2055435 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B19758815 : Blo 2055435 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B13172543 : Blo 2055435 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B8781695 : Blo 2055435 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B5854463 : Blo 2055435 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B3902975 : Blo 2055435 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B2601983 : Blo 2055435 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B6938621 : Blo 2055435 6938621 := bstep (se 3 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 6938621 = 2601983) B2601983
theorem B4625747 : Blo 2055435 4625747 := bstep (se 1 (by rfl) ⟨3469310, by rfl⟩ : syracuseStep 4625747 = 6938621) B6938621
theorem B3083831 : Blo 2055435 3083831 := bstep (se 1 (by rfl) ⟨2312873, by rfl⟩ : syracuseStep 3083831 = 4625747) B4625747
theorem B2055887 : Blo 2055435 2055887 := bstep (se 1 (by rfl) ⟨1541915, by rfl⟩ : syracuseStep 2055887 = 3083831) B3083831
theorem B3083837 : Blo 2055435 3083837 := bbase (se 3 (by rfl) ⟨578219, by rfl⟩ : syracuseStep 3083837 = 1156439) (by norm_num)
theorem B2055891 : Blo 2055435 2055891 := bstep (se 1 (by rfl) ⟨1541918, by rfl⟩ : syracuseStep 2055891 = 3083837) B3083837
theorem B4625765 : Blo 2055435 4625765 := bbase (se 4 (by rfl) ⟨433665, by rfl⟩ : syracuseStep 4625765 = 867331) (by norm_num)
theorem B3083843 : Blo 2055435 3083843 := bstep (se 1 (by rfl) ⟨2312882, by rfl⟩ : syracuseStep 3083843 = 4625765) B4625765
theorem B2055895 : Blo 2055435 2055895 := bstep (se 1 (by rfl) ⟨1541921, by rfl⟩ : syracuseStep 2055895 = 3083843) B3083843
theorem B5203997 : Blo 2055435 5203997 := bbase (se 3 (by rfl) ⟨975749, by rfl⟩ : syracuseStep 5203997 = 1951499) (by norm_num)
theorem B3469331 : Blo 2055435 3469331 := bstep (se 1 (by rfl) ⟨2601998, by rfl⟩ : syracuseStep 3469331 = 5203997) B5203997
theorem B2312887 : Blo 2055435 2312887 := bstep (se 1 (by rfl) ⟨1734665, by rfl⟩ : syracuseStep 2312887 = 3469331) B3469331
theorem B3083849 : Blo 2055435 3083849 := bstep (se 2 (by rfl) ⟨1156443, by rfl⟩ : syracuseStep 3083849 = 2312887) B2312887
theorem B2055899 : Blo 2055435 2055899 := bstep (se 1 (by rfl) ⟨1541924, by rfl⟩ : syracuseStep 2055899 = 3083849) B3083849
theorem B3903005 : Blo 2055435 3903005 := bbase (se 3 (by rfl) ⟨731813, by rfl⟩ : syracuseStep 3903005 = 1463627) (by norm_num)
theorem B10408013 : Blo 2055435 10408013 := bstep (se 3 (by rfl) ⟨1951502, by rfl⟩ : syracuseStep 10408013 = 3903005) B3903005
theorem B6938675 : Blo 2055435 6938675 := bstep (se 1 (by rfl) ⟨5204006, by rfl⟩ : syracuseStep 6938675 = 10408013) B10408013
theorem B4625783 : Blo 2055435 4625783 := bstep (se 1 (by rfl) ⟨3469337, by rfl⟩ : syracuseStep 4625783 = 6938675) B6938675
theorem B3083855 : Blo 2055435 3083855 := bstep (se 1 (by rfl) ⟨2312891, by rfl⟩ : syracuseStep 3083855 = 4625783) B4625783
theorem B2055903 : Blo 2055435 2055903 := bstep (se 1 (by rfl) ⟨1541927, by rfl⟩ : syracuseStep 2055903 = 3083855) B3083855
theorem B3083861 : Blo 2055435 3083861 := bbase (se 8 (by rfl) ⟨18069, by rfl⟩ : syracuseStep 3083861 = 36139) (by norm_num)
theorem B2055907 : Blo 2055435 2055907 := bstep (se 1 (by rfl) ⟨1541930, by rfl⟩ : syracuseStep 2055907 = 3083861) B3083861
theorem B8781797 : Blo 2055435 8781797 := bbase (se 4 (by rfl) ⟨823293, by rfl⟩ : syracuseStep 8781797 = 1646587) (by norm_num)
theorem B5854531 : Blo 2055435 5854531 := bstep (se 1 (by rfl) ⟨4390898, by rfl⟩ : syracuseStep 5854531 = 8781797) B8781797
theorem B7806041 : Blo 2055435 7806041 := bstep (se 2 (by rfl) ⟨2927265, by rfl⟩ : syracuseStep 7806041 = 5854531) B5854531
theorem B5204027 : Blo 2055435 5204027 := bstep (se 1 (by rfl) ⟨3903020, by rfl⟩ : syracuseStep 5204027 = 7806041) B7806041
theorem B3469351 : Blo 2055435 3469351 := bstep (se 1 (by rfl) ⟨2602013, by rfl⟩ : syracuseStep 3469351 = 5204027) B5204027
theorem B4625801 : Blo 2055435 4625801 := bstep (se 2 (by rfl) ⟨1734675, by rfl⟩ : syracuseStep 4625801 = 3469351) B3469351
theorem B3083867 : Blo 2055435 3083867 := bstep (se 1 (by rfl) ⟨2312900, by rfl⟩ : syracuseStep 3083867 = 4625801) B4625801
theorem B2055911 : Blo 2055435 2055911 := bstep (se 1 (by rfl) ⟨1541933, by rfl⟩ : syracuseStep 2055911 = 3083867) B3083867
theorem B2312905 : Blo 2055435 2312905 := bbase (se 2 (by rfl) ⟨867339, by rfl⟩ : syracuseStep 2312905 = 1734679) (by norm_num)
theorem B3083873 : Blo 2055435 3083873 := bstep (se 2 (by rfl) ⟨1156452, by rfl⟩ : syracuseStep 3083873 = 2312905) B2312905
theorem B2055915 : Blo 2055435 2055915 := bstep (se 1 (by rfl) ⟨1541936, by rfl⟩ : syracuseStep 2055915 = 3083873) B3083873
theorem B6586373 : Blo 2055435 6586373 := bbase (se 4 (by rfl) ⟨617472, by rfl⟩ : syracuseStep 6586373 = 1234945) (by norm_num)
theorem B17563661 : Blo 2055435 17563661 := bstep (se 3 (by rfl) ⟨3293186, by rfl⟩ : syracuseStep 17563661 = 6586373) B6586373
theorem B11709107 : Blo 2055435 11709107 := bstep (se 1 (by rfl) ⟨8781830, by rfl⟩ : syracuseStep 11709107 = 17563661) B17563661
theorem B7806071 : Blo 2055435 7806071 := bstep (se 1 (by rfl) ⟨5854553, by rfl⟩ : syracuseStep 7806071 = 11709107) B11709107
theorem B5204047 : Blo 2055435 5204047 := bstep (se 1 (by rfl) ⟨3903035, by rfl⟩ : syracuseStep 5204047 = 7806071) B7806071
theorem B6938729 : Blo 2055435 6938729 := bstep (se 2 (by rfl) ⟨2602023, by rfl⟩ : syracuseStep 6938729 = 5204047) B5204047
theorem B4625819 : Blo 2055435 4625819 := bstep (se 1 (by rfl) ⟨3469364, by rfl⟩ : syracuseStep 4625819 = 6938729) B6938729
theorem B3083879 : Blo 2055435 3083879 := bstep (se 1 (by rfl) ⟨2312909, by rfl⟩ : syracuseStep 3083879 = 4625819) B4625819
theorem B2055919 : Blo 2055435 2055919 := bstep (se 1 (by rfl) ⟨1541939, by rfl⟩ : syracuseStep 2055919 = 3083879) B3083879
theorem B3083885 : Blo 2055435 3083885 := bbase (se 3 (by rfl) ⟨578228, by rfl⟩ : syracuseStep 3083885 = 1156457) (by norm_num)
theorem B2055923 : Blo 2055435 2055923 := bstep (se 1 (by rfl) ⟨1541942, by rfl⟩ : syracuseStep 2055923 = 3083885) B3083885
theorem B4625837 : Blo 2055435 4625837 := bbase (se 3 (by rfl) ⟨867344, by rfl⟩ : syracuseStep 4625837 = 1734689) (by norm_num)
theorem B3083891 : Blo 2055435 3083891 := bstep (se 1 (by rfl) ⟨2312918, by rfl⟩ : syracuseStep 3083891 = 4625837) B4625837
theorem B2055927 : Blo 2055435 2055927 := bstep (se 1 (by rfl) ⟨1541945, by rfl⟩ : syracuseStep 2055927 = 3083891) B3083891
theorem B7409717 : Blo 2055435 7409717 := bbase (se 5 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 7409717 = 694661) (by norm_num)
theorem B4939811 : Blo 2055435 4939811 := bstep (se 1 (by rfl) ⟨3704858, by rfl⟩ : syracuseStep 4939811 = 7409717) B7409717
theorem B3293207 : Blo 2055435 3293207 := bstep (se 1 (by rfl) ⟨2469905, by rfl⟩ : syracuseStep 3293207 = 4939811) B4939811
theorem B2195471 : Blo 2055435 2195471 := bstep (se 1 (by rfl) ⟨1646603, by rfl⟩ : syracuseStep 2195471 = 3293207) B3293207
theorem B5854589 : Blo 2055435 5854589 := bstep (se 3 (by rfl) ⟨1097735, by rfl⟩ : syracuseStep 5854589 = 2195471) B2195471
theorem B3903059 : Blo 2055435 3903059 := bstep (se 1 (by rfl) ⟨2927294, by rfl⟩ : syracuseStep 3903059 = 5854589) B5854589
theorem B2602039 : Blo 2055435 2602039 := bstep (se 1 (by rfl) ⟨1951529, by rfl⟩ : syracuseStep 2602039 = 3903059) B3903059
theorem B3469385 : Blo 2055435 3469385 := bstep (se 2 (by rfl) ⟨1301019, by rfl⟩ : syracuseStep 3469385 = 2602039) B2602039
theorem B2312923 : Blo 2055435 2312923 := bstep (se 1 (by rfl) ⟨1734692, by rfl⟩ : syracuseStep 2312923 = 3469385) B3469385
theorem B3083897 : Blo 2055435 3083897 := bstep (se 2 (by rfl) ⟨1156461, by rfl⟩ : syracuseStep 3083897 = 2312923) B2312923
theorem B2055931 : Blo 2055435 2055931 := bstep (se 1 (by rfl) ⟨1541948, by rfl⟩ : syracuseStep 2055931 = 3083897) B3083897
theorem B4817789 : Blo 2055435 4817789 := bbase (se 3 (by rfl) ⟨903335, by rfl⟩ : syracuseStep 4817789 = 1806671) (by norm_num)
theorem B3211859 : Blo 2055435 3211859 := bstep (se 1 (by rfl) ⟨2408894, by rfl⟩ : syracuseStep 3211859 = 4817789) B4817789
theorem B8564957 : Blo 2055435 8564957 := bstep (se 3 (by rfl) ⟨1605929, by rfl⟩ : syracuseStep 8564957 = 3211859) B3211859
theorem B5709971 : Blo 2055435 5709971 := bstep (se 1 (by rfl) ⟨4282478, by rfl⟩ : syracuseStep 5709971 = 8564957) B8564957
theorem B15226589 : Blo 2055435 15226589 := bstep (se 3 (by rfl) ⟨2854985, by rfl⟩ : syracuseStep 15226589 = 5709971) B5709971
theorem B40604237 : Blo 2055435 40604237 := bstep (se 3 (by rfl) ⟨7613294, by rfl⟩ : syracuseStep 40604237 = 15226589) B15226589
theorem B27069491 : Blo 2055435 27069491 := bstep (se 1 (by rfl) ⟨20302118, by rfl⟩ : syracuseStep 27069491 = 40604237) B40604237
theorem B18046327 : Blo 2055435 18046327 := bstep (se 1 (by rfl) ⟨13534745, by rfl⟩ : syracuseStep 18046327 = 27069491) B27069491
theorem B24061769 : Blo 2055435 24061769 := bstep (se 2 (by rfl) ⟨9023163, by rfl⟩ : syracuseStep 24061769 = 18046327) B18046327
theorem B16041179 : Blo 2055435 16041179 := bstep (se 1 (by rfl) ⟨12030884, by rfl⟩ : syracuseStep 16041179 = 24061769) B24061769
theorem B10694119 : Blo 2055435 10694119 := bstep (se 1 (by rfl) ⟨8020589, by rfl⟩ : syracuseStep 10694119 = 16041179) B16041179
theorem B14258825 : Blo 2055435 14258825 := bstep (se 2 (by rfl) ⟨5347059, by rfl⟩ : syracuseStep 14258825 = 10694119) B10694119
theorem B9505883 : Blo 2055435 9505883 := bstep (se 1 (by rfl) ⟨7129412, by rfl⟩ : syracuseStep 9505883 = 14258825) B14258825
theorem B25349021 : Blo 2055435 25349021 := bstep (se 3 (by rfl) ⟨4752941, by rfl⟩ : syracuseStep 25349021 = 9505883) B9505883
theorem B16899347 : Blo 2055435 16899347 := bstep (se 1 (by rfl) ⟨12674510, by rfl⟩ : syracuseStep 16899347 = 25349021) B25349021
theorem B11266231 : Blo 2055435 11266231 := bstep (se 1 (by rfl) ⟨8449673, by rfl⟩ : syracuseStep 11266231 = 16899347) B16899347
theorem B15021641 : Blo 2055435 15021641 := bstep (se 2 (by rfl) ⟨5633115, by rfl⟩ : syracuseStep 15021641 = 11266231) B11266231
theorem B10014427 : Blo 2055435 10014427 := bstep (se 1 (by rfl) ⟨7510820, by rfl⟩ : syracuseStep 10014427 = 15021641) B15021641
theorem B13352569 : Blo 2055435 13352569 := bstep (se 2 (by rfl) ⟨5007213, by rfl⟩ : syracuseStep 13352569 = 10014427) B10014427
theorem B284854805 : Blo 2055435 284854805 := bstep (se 6 (by rfl) ⟨6676284, by rfl⟩ : syracuseStep 284854805 = 13352569) B13352569
theorem B189903203 : Blo 2055435 189903203 := bstep (se 1 (by rfl) ⟨142427402, by rfl⟩ : syracuseStep 189903203 = 284854805) B284854805
theorem B126602135 : Blo 2055435 126602135 := bstep (se 1 (by rfl) ⟨94951601, by rfl⟩ : syracuseStep 126602135 = 189903203) B189903203
theorem B84401423 : Blo 2055435 84401423 := bstep (se 1 (by rfl) ⟨63301067, by rfl⟩ : syracuseStep 84401423 = 126602135) B126602135
theorem B56267615 : Blo 2055435 56267615 := bstep (se 1 (by rfl) ⟨42200711, by rfl⟩ : syracuseStep 56267615 = 84401423) B84401423
theorem B37511743 : Blo 2055435 37511743 := bstep (se 1 (by rfl) ⟨28133807, by rfl⟩ : syracuseStep 37511743 = 56267615) B56267615
theorem B50015657 : Blo 2055435 50015657 := bstep (se 2 (by rfl) ⟨18755871, by rfl⟩ : syracuseStep 50015657 = 37511743) B37511743
theorem B133375085 : Blo 2055435 133375085 := bstep (se 3 (by rfl) ⟨25007828, by rfl⟩ : syracuseStep 133375085 = 50015657) B50015657
theorem B88916723 : Blo 2055435 88916723 := bstep (se 1 (by rfl) ⟨66687542, by rfl⟩ : syracuseStep 88916723 = 133375085) B133375085
theorem B59277815 : Blo 2055435 59277815 := bstep (se 1 (by rfl) ⟨44458361, by rfl⟩ : syracuseStep 59277815 = 88916723) B88916723
theorem B39518543 : Blo 2055435 39518543 := bstep (se 1 (by rfl) ⟨29638907, by rfl⟩ : syracuseStep 39518543 = 59277815) B59277815
theorem B26345695 : Blo 2055435 26345695 := bstep (se 1 (by rfl) ⟨19759271, by rfl⟩ : syracuseStep 26345695 = 39518543) B39518543
theorem B35127593 : Blo 2055435 35127593 := bstep (se 2 (by rfl) ⟨13172847, by rfl⟩ : syracuseStep 35127593 = 26345695) B26345695
theorem B23418395 : Blo 2055435 23418395 := bstep (se 1 (by rfl) ⟨17563796, by rfl⟩ : syracuseStep 23418395 = 35127593) B35127593
theorem B15612263 : Blo 2055435 15612263 := bstep (se 1 (by rfl) ⟨11709197, by rfl⟩ : syracuseStep 15612263 = 23418395) B23418395
theorem B10408175 : Blo 2055435 10408175 := bstep (se 1 (by rfl) ⟨7806131, by rfl⟩ : syracuseStep 10408175 = 15612263) B15612263
theorem B6938783 : Blo 2055435 6938783 := bstep (se 1 (by rfl) ⟨5204087, by rfl⟩ : syracuseStep 6938783 = 10408175) B10408175
theorem B4625855 : Blo 2055435 4625855 := bstep (se 1 (by rfl) ⟨3469391, by rfl⟩ : syracuseStep 4625855 = 6938783) B6938783
theorem B3083903 : Blo 2055435 3083903 := bstep (se 1 (by rfl) ⟨2312927, by rfl⟩ : syracuseStep 3083903 = 4625855) B4625855
theorem B2055935 : Blo 2055435 2055935 := bstep (se 1 (by rfl) ⟨1541951, by rfl⟩ : syracuseStep 2055935 = 3083903) B3083903
theorem B3083909 : Blo 2055435 3083909 := bbase (se 4 (by rfl) ⟨289116, by rfl⟩ : syracuseStep 3083909 = 578233) (by norm_num)
theorem B2055939 : Blo 2055435 2055939 := bstep (se 1 (by rfl) ⟨1541954, by rfl⟩ : syracuseStep 2055939 = 3083909) B3083909
theorem B3469405 : Blo 2055435 3469405 := bbase (se 3 (by rfl) ⟨650513, by rfl⟩ : syracuseStep 3469405 = 1301027) (by norm_num)
theorem B4625873 : Blo 2055435 4625873 := bstep (se 2 (by rfl) ⟨1734702, by rfl⟩ : syracuseStep 4625873 = 3469405) B3469405
theorem B3083915 : Blo 2055435 3083915 := bstep (se 1 (by rfl) ⟨2312936, by rfl⟩ : syracuseStep 3083915 = 4625873) B4625873
theorem B2055943 : Blo 2055435 2055943 := bstep (se 1 (by rfl) ⟨1541957, by rfl⟩ : syracuseStep 2055943 = 3083915) B3083915
theorem B2312941 : Blo 2055435 2312941 := bbase (se 3 (by rfl) ⟨433676, by rfl⟩ : syracuseStep 2312941 = 867353) (by norm_num)
theorem B3083921 : Blo 2055435 3083921 := bstep (se 2 (by rfl) ⟨1156470, by rfl⟩ : syracuseStep 3083921 = 2312941) B2312941
theorem B2055947 : Blo 2055435 2055947 := bstep (se 1 (by rfl) ⟨1541960, by rfl⟩ : syracuseStep 2055947 = 3083921) B3083921
theorem B6938837 : Blo 2055435 6938837 := bbase (se 7 (by rfl) ⟨81314, by rfl⟩ : syracuseStep 6938837 = 162629) (by norm_num)
theorem B4625891 : Blo 2055435 4625891 := bstep (se 1 (by rfl) ⟨3469418, by rfl⟩ : syracuseStep 4625891 = 6938837) B6938837
theorem B3083927 : Blo 2055435 3083927 := bstep (se 1 (by rfl) ⟨2312945, by rfl⟩ : syracuseStep 3083927 = 4625891) B4625891
theorem B2055951 : Blo 2055435 2055951 := bstep (se 1 (by rfl) ⟨1541963, by rfl⟩ : syracuseStep 2055951 = 3083927) B3083927
theorem B3083933 : Blo 2055435 3083933 := bbase (se 3 (by rfl) ⟨578237, by rfl⟩ : syracuseStep 3083933 = 1156475) (by norm_num)
theorem B2055955 : Blo 2055435 2055955 := bstep (se 1 (by rfl) ⟨1541966, by rfl⟩ : syracuseStep 2055955 = 3083933) B3083933
theorem B4625909 : Blo 2055435 4625909 := bbase (se 5 (by rfl) ⟨216839, by rfl⟩ : syracuseStep 4625909 = 433679) (by norm_num)
theorem B3083939 : Blo 2055435 3083939 := bstep (se 1 (by rfl) ⟨2312954, by rfl⟩ : syracuseStep 3083939 = 4625909) B4625909
theorem B2055959 : Blo 2055435 2055959 := bstep (se 1 (by rfl) ⟨1541969, by rfl⟩ : syracuseStep 2055959 = 3083939) B3083939
theorem B29639317 : Blo 2055435 29639317 := bbase (se 6 (by rfl) ⟨694671, by rfl⟩ : syracuseStep 29639317 = 1389343) (by norm_num)
theorem B39519089 : Blo 2055435 39519089 := bstep (se 2 (by rfl) ⟨14819658, by rfl⟩ : syracuseStep 39519089 = 29639317) B29639317
theorem B26346059 : Blo 2055435 26346059 := bstep (se 1 (by rfl) ⟨19759544, by rfl⟩ : syracuseStep 26346059 = 39519089) B39519089
theorem B17564039 : Blo 2055435 17564039 := bstep (se 1 (by rfl) ⟨13173029, by rfl⟩ : syracuseStep 17564039 = 26346059) B26346059
theorem B11709359 : Blo 2055435 11709359 := bstep (se 1 (by rfl) ⟨8782019, by rfl⟩ : syracuseStep 11709359 = 17564039) B17564039
theorem B7806239 : Blo 2055435 7806239 := bstep (se 1 (by rfl) ⟨5854679, by rfl⟩ : syracuseStep 7806239 = 11709359) B11709359
theorem B5204159 : Blo 2055435 5204159 := bstep (se 1 (by rfl) ⟨3903119, by rfl⟩ : syracuseStep 5204159 = 7806239) B7806239
theorem B3469439 : Blo 2055435 3469439 := bstep (se 1 (by rfl) ⟨2602079, by rfl⟩ : syracuseStep 3469439 = 5204159) B5204159
theorem B2312959 : Blo 2055435 2312959 := bstep (se 1 (by rfl) ⟨1734719, by rfl⟩ : syracuseStep 2312959 = 3469439) B3469439
theorem B3083945 : Blo 2055435 3083945 := bstep (se 2 (by rfl) ⟨1156479, by rfl⟩ : syracuseStep 3083945 = 2312959) B2312959
theorem B2055963 : Blo 2055435 2055963 := bstep (se 1 (by rfl) ⟨1541972, by rfl⟩ : syracuseStep 2055963 = 3083945) B3083945
theorem B2195509 : Blo 2055435 2195509 := bbase (se 5 (by rfl) ⟨102914, by rfl⟩ : syracuseStep 2195509 = 205829) (by norm_num)
theorem B2927345 : Blo 2055435 2927345 := bstep (se 2 (by rfl) ⟨1097754, by rfl⟩ : syracuseStep 2927345 = 2195509) B2195509
theorem B7806253 : Blo 2055435 7806253 := bstep (se 3 (by rfl) ⟨1463672, by rfl⟩ : syracuseStep 7806253 = 2927345) B2927345
theorem B10408337 : Blo 2055435 10408337 := bstep (se 2 (by rfl) ⟨3903126, by rfl⟩ : syracuseStep 10408337 = 7806253) B7806253
theorem B6938891 : Blo 2055435 6938891 := bstep (se 1 (by rfl) ⟨5204168, by rfl⟩ : syracuseStep 6938891 = 10408337) B10408337
theorem B4625927 : Blo 2055435 4625927 := bstep (se 1 (by rfl) ⟨3469445, by rfl⟩ : syracuseStep 4625927 = 6938891) B6938891
theorem B3083951 : Blo 2055435 3083951 := bstep (se 1 (by rfl) ⟨2312963, by rfl⟩ : syracuseStep 3083951 = 4625927) B4625927
theorem B2055967 : Blo 2055435 2055967 := bstep (se 1 (by rfl) ⟨1541975, by rfl⟩ : syracuseStep 2055967 = 3083951) B3083951
theorem B3083957 : Blo 2055435 3083957 := bbase (se 5 (by rfl) ⟨144560, by rfl⟩ : syracuseStep 3083957 = 289121) (by norm_num)
theorem B2055971 : Blo 2055435 2055971 := bstep (se 1 (by rfl) ⟨1541978, by rfl⟩ : syracuseStep 2055971 = 3083957) B3083957
theorem B5204189 : Blo 2055435 5204189 := bbase (se 3 (by rfl) ⟨975785, by rfl⟩ : syracuseStep 5204189 = 1951571) (by norm_num)
theorem B3469459 : Blo 2055435 3469459 := bstep (se 1 (by rfl) ⟨2602094, by rfl⟩ : syracuseStep 3469459 = 5204189) B5204189
theorem B4625945 : Blo 2055435 4625945 := bstep (se 2 (by rfl) ⟨1734729, by rfl⟩ : syracuseStep 4625945 = 3469459) B3469459
theorem B3083963 : Blo 2055435 3083963 := bstep (se 1 (by rfl) ⟨2312972, by rfl⟩ : syracuseStep 3083963 = 4625945) B4625945
theorem B2055975 : Blo 2055435 2055975 := bstep (se 1 (by rfl) ⟨1541981, by rfl⟩ : syracuseStep 2055975 = 3083963) B3083963
theorem B2312977 : Blo 2055435 2312977 := bbase (se 2 (by rfl) ⟨867366, by rfl⟩ : syracuseStep 2312977 = 1734733) (by norm_num)
theorem B3083969 : Blo 2055435 3083969 := bstep (se 2 (by rfl) ⟨1156488, by rfl⟩ : syracuseStep 3083969 = 2312977) B2312977
theorem B2055979 : Blo 2055435 2055979 := bstep (se 1 (by rfl) ⟨1541984, by rfl⟩ : syracuseStep 2055979 = 3083969) B3083969
theorem B3903157 : Blo 2055435 3903157 := bbase (se 5 (by rfl) ⟨182960, by rfl⟩ : syracuseStep 3903157 = 365921) (by norm_num)
theorem B5204209 : Blo 2055435 5204209 := bstep (se 2 (by rfl) ⟨1951578, by rfl⟩ : syracuseStep 5204209 = 3903157) B3903157
theorem B6938945 : Blo 2055435 6938945 := bstep (se 2 (by rfl) ⟨2602104, by rfl⟩ : syracuseStep 6938945 = 5204209) B5204209
theorem B4625963 : Blo 2055435 4625963 := bstep (se 1 (by rfl) ⟨3469472, by rfl⟩ : syracuseStep 4625963 = 6938945) B6938945
theorem B3083975 : Blo 2055435 3083975 := bstep (se 1 (by rfl) ⟨2312981, by rfl⟩ : syracuseStep 3083975 = 4625963) B4625963
theorem B2055983 : Blo 2055435 2055983 := bstep (se 1 (by rfl) ⟨1541987, by rfl⟩ : syracuseStep 2055983 = 3083975) B3083975
theorem B3083981 : Blo 2055435 3083981 := bbase (se 3 (by rfl) ⟨578246, by rfl⟩ : syracuseStep 3083981 = 1156493) (by norm_num)
theorem B2055987 : Blo 2055435 2055987 := bstep (se 1 (by rfl) ⟨1541990, by rfl⟩ : syracuseStep 2055987 = 3083981) B3083981
theorem B4625981 : Blo 2055435 4625981 := bbase (se 3 (by rfl) ⟨867371, by rfl⟩ : syracuseStep 4625981 = 1734743) (by norm_num)
theorem B3083987 : Blo 2055435 3083987 := bstep (se 1 (by rfl) ⟨2312990, by rfl⟩ : syracuseStep 3083987 = 4625981) B4625981
theorem B2055991 : Blo 2055435 2055991 := bstep (se 1 (by rfl) ⟨1541993, by rfl⟩ : syracuseStep 2055991 = 3083987) B3083987
theorem B3469493 : Blo 2055435 3469493 := bbase (se 5 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 3469493 = 325265) (by norm_num)
theorem B2312995 : Blo 2055435 2312995 := bstep (se 1 (by rfl) ⟨1734746, by rfl⟩ : syracuseStep 2312995 = 3469493) B3469493
theorem B3083993 : Blo 2055435 3083993 := bstep (se 2 (by rfl) ⟨1156497, by rfl⟩ : syracuseStep 3083993 = 2312995) B2312995
theorem B2055995 : Blo 2055435 2055995 := bstep (se 1 (by rfl) ⟨1541996, by rfl⟩ : syracuseStep 2055995 = 3083993) B3083993
theorem B4939973 : Blo 2055435 4939973 := bbase (se 4 (by rfl) ⟨463122, by rfl⟩ : syracuseStep 4939973 = 926245) (by norm_num)
theorem B3293315 : Blo 2055435 3293315 := bstep (se 1 (by rfl) ⟨2469986, by rfl⟩ : syracuseStep 3293315 = 4939973) B4939973
theorem B2195543 : Blo 2055435 2195543 := bstep (se 1 (by rfl) ⟨1646657, by rfl⟩ : syracuseStep 2195543 = 3293315) B3293315
theorem B5854781 : Blo 2055435 5854781 := bstep (se 3 (by rfl) ⟨1097771, by rfl⟩ : syracuseStep 5854781 = 2195543) B2195543
theorem B15612749 : Blo 2055435 15612749 := bstep (se 3 (by rfl) ⟨2927390, by rfl⟩ : syracuseStep 15612749 = 5854781) B5854781
theorem B10408499 : Blo 2055435 10408499 := bstep (se 1 (by rfl) ⟨7806374, by rfl⟩ : syracuseStep 10408499 = 15612749) B15612749
theorem B6938999 : Blo 2055435 6938999 := bstep (se 1 (by rfl) ⟨5204249, by rfl⟩ : syracuseStep 6938999 = 10408499) B10408499
theorem B4625999 : Blo 2055435 4625999 := bstep (se 1 (by rfl) ⟨3469499, by rfl⟩ : syracuseStep 4625999 = 6938999) B6938999
theorem B3083999 : Blo 2055435 3083999 := bstep (se 1 (by rfl) ⟨2312999, by rfl⟩ : syracuseStep 3083999 = 4625999) B4625999
theorem B2055999 : Blo 2055435 2055999 := bstep (se 1 (by rfl) ⟨1541999, by rfl⟩ : syracuseStep 2055999 = 3083999) B3083999
theorem B3084005 : Blo 2055435 3084005 := bbase (se 4 (by rfl) ⟨289125, by rfl⟩ : syracuseStep 3084005 = 578251) (by norm_num)
theorem B2056003 : Blo 2055435 2056003 := bstep (se 1 (by rfl) ⟨1542002, by rfl⟩ : syracuseStep 2056003 = 3084005) B3084005
theorem B5854805 : Blo 2055435 5854805 := bbase (se 8 (by rfl) ⟨34305, by rfl⟩ : syracuseStep 5854805 = 68611) (by norm_num)
theorem B3903203 : Blo 2055435 3903203 := bstep (se 1 (by rfl) ⟨2927402, by rfl⟩ : syracuseStep 3903203 = 5854805) B5854805
theorem B2602135 : Blo 2055435 2602135 := bstep (se 1 (by rfl) ⟨1951601, by rfl⟩ : syracuseStep 2602135 = 3903203) B3903203
theorem B3469513 : Blo 2055435 3469513 := bstep (se 2 (by rfl) ⟨1301067, by rfl⟩ : syracuseStep 3469513 = 2602135) B2602135
theorem B4626017 : Blo 2055435 4626017 := bstep (se 2 (by rfl) ⟨1734756, by rfl⟩ : syracuseStep 4626017 = 3469513) B3469513
theorem B3084011 : Blo 2055435 3084011 := bstep (se 1 (by rfl) ⟨2313008, by rfl⟩ : syracuseStep 3084011 = 4626017) B4626017
theorem B2056007 : Blo 2055435 2056007 := bstep (se 1 (by rfl) ⟨1542005, by rfl⟩ : syracuseStep 2056007 = 3084011) B3084011
theorem B2313013 : Blo 2055435 2313013 := bbase (se 5 (by rfl) ⟨108422, by rfl⟩ : syracuseStep 2313013 = 216845) (by norm_num)
theorem B3084017 : Blo 2055435 3084017 := bstep (se 2 (by rfl) ⟨1156506, by rfl⟩ : syracuseStep 3084017 = 2313013) B2313013
theorem B2056011 : Blo 2055435 2056011 := bstep (se 1 (by rfl) ⟨1542008, by rfl⟩ : syracuseStep 2056011 = 3084017) B3084017
theorem B2602145 : Blo 2055435 2602145 := bbase (se 2 (by rfl) ⟨975804, by rfl⟩ : syracuseStep 2602145 = 1951609) (by norm_num)
theorem B6939053 : Blo 2055435 6939053 := bstep (se 3 (by rfl) ⟨1301072, by rfl⟩ : syracuseStep 6939053 = 2602145) B2602145
theorem B4626035 : Blo 2055435 4626035 := bstep (se 1 (by rfl) ⟨3469526, by rfl⟩ : syracuseStep 4626035 = 6939053) B6939053
theorem B3084023 : Blo 2055435 3084023 := bstep (se 1 (by rfl) ⟨2313017, by rfl⟩ : syracuseStep 3084023 = 4626035) B4626035
theorem B2056015 : Blo 2055435 2056015 := bstep (se 1 (by rfl) ⟨1542011, by rfl⟩ : syracuseStep 2056015 = 3084023) B3084023
theorem B3084029 : Blo 2055435 3084029 := bbase (se 3 (by rfl) ⟨578255, by rfl⟩ : syracuseStep 3084029 = 1156511) (by norm_num)
theorem B2056019 : Blo 2055435 2056019 := bstep (se 1 (by rfl) ⟨1542014, by rfl⟩ : syracuseStep 2056019 = 3084029) B3084029
theorem B4626053 : Blo 2055435 4626053 := bbase (se 4 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 4626053 = 867385) (by norm_num)
theorem B3084035 : Blo 2055435 3084035 := bstep (se 1 (by rfl) ⟨2313026, by rfl⟩ : syracuseStep 3084035 = 4626053) B4626053
theorem B2056023 : Blo 2055435 2056023 := bstep (se 1 (by rfl) ⟨1542017, by rfl⟩ : syracuseStep 2056023 = 3084035) B3084035
theorem B4689181 : Blo 2055435 4689181 := bbase (se 3 (by rfl) ⟨879221, by rfl⟩ : syracuseStep 4689181 = 1758443) (by norm_num)
theorem B6252241 : Blo 2055435 6252241 := bstep (se 2 (by rfl) ⟨2344590, by rfl⟩ : syracuseStep 6252241 = 4689181) B4689181
theorem B8336321 : Blo 2055435 8336321 := bstep (se 2 (by rfl) ⟨3126120, by rfl⟩ : syracuseStep 8336321 = 6252241) B6252241
theorem B5557547 : Blo 2055435 5557547 := bstep (se 1 (by rfl) ⟨4168160, by rfl⟩ : syracuseStep 5557547 = 8336321) B8336321
theorem B3705031 : Blo 2055435 3705031 := bstep (se 1 (by rfl) ⟨2778773, by rfl⟩ : syracuseStep 3705031 = 5557547) B5557547
theorem B4940041 : Blo 2055435 4940041 := bstep (se 2 (by rfl) ⟨1852515, by rfl⟩ : syracuseStep 4940041 = 3705031) B3705031
theorem B6586721 : Blo 2055435 6586721 := bstep (se 2 (by rfl) ⟨2470020, by rfl⟩ : syracuseStep 6586721 = 4940041) B4940041
theorem B4391147 : Blo 2055435 4391147 := bstep (se 1 (by rfl) ⟨3293360, by rfl⟩ : syracuseStep 4391147 = 6586721) B6586721
theorem B2927431 : Blo 2055435 2927431 := bstep (se 1 (by rfl) ⟨2195573, by rfl⟩ : syracuseStep 2927431 = 4391147) B4391147
theorem B3903241 : Blo 2055435 3903241 := bstep (se 2 (by rfl) ⟨1463715, by rfl⟩ : syracuseStep 3903241 = 2927431) B2927431
theorem B5204321 : Blo 2055435 5204321 := bstep (se 2 (by rfl) ⟨1951620, by rfl⟩ : syracuseStep 5204321 = 3903241) B3903241
theorem B3469547 : Blo 2055435 3469547 := bstep (se 1 (by rfl) ⟨2602160, by rfl⟩ : syracuseStep 3469547 = 5204321) B5204321
theorem B2313031 : Blo 2055435 2313031 := bstep (se 1 (by rfl) ⟨1734773, by rfl⟩ : syracuseStep 2313031 = 3469547) B3469547
theorem B3084041 : Blo 2055435 3084041 := bstep (se 2 (by rfl) ⟨1156515, by rfl⟩ : syracuseStep 3084041 = 2313031) B2313031
theorem B2056027 : Blo 2055435 2056027 := bstep (se 1 (by rfl) ⟨1542020, by rfl⟩ : syracuseStep 2056027 = 3084041) B3084041
theorem B10408661 : Blo 2055435 10408661 := bbase (se 7 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 10408661 = 243953) (by norm_num)
theorem B6939107 : Blo 2055435 6939107 := bstep (se 1 (by rfl) ⟨5204330, by rfl⟩ : syracuseStep 6939107 = 10408661) B10408661
theorem B4626071 : Blo 2055435 4626071 := bstep (se 1 (by rfl) ⟨3469553, by rfl⟩ : syracuseStep 4626071 = 6939107) B6939107
theorem B3084047 : Blo 2055435 3084047 := bstep (se 1 (by rfl) ⟨2313035, by rfl⟩ : syracuseStep 3084047 = 4626071) B4626071
theorem B2056031 : Blo 2055435 2056031 := bstep (se 1 (by rfl) ⟨1542023, by rfl⟩ : syracuseStep 2056031 = 3084047) B3084047
theorem B3084053 : Blo 2055435 3084053 := bbase (se 6 (by rfl) ⟨72282, by rfl⟩ : syracuseStep 3084053 = 144565) (by norm_num)
theorem B2056035 : Blo 2055435 2056035 := bstep (se 1 (by rfl) ⟨1542026, by rfl⟩ : syracuseStep 2056035 = 3084053) B3084053
theorem B7129781 : Blo 2055435 7129781 := bbase (se 5 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 7129781 = 668417) (by norm_num)
theorem B4753187 : Blo 2055435 4753187 := bstep (se 1 (by rfl) ⟨3564890, by rfl⟩ : syracuseStep 4753187 = 7129781) B7129781
theorem B3168791 : Blo 2055435 3168791 := bstep (se 1 (by rfl) ⟨2376593, by rfl⟩ : syracuseStep 3168791 = 4753187) B4753187
theorem B2112527 : Blo 2055435 2112527 := bstep (se 1 (by rfl) ⟨1584395, by rfl⟩ : syracuseStep 2112527 = 3168791) B3168791
theorem B5633405 : Blo 2055435 5633405 := bstep (se 3 (by rfl) ⟨1056263, by rfl⟩ : syracuseStep 5633405 = 2112527) B2112527
theorem B3755603 : Blo 2055435 3755603 := bstep (se 1 (by rfl) ⟨2816702, by rfl⟩ : syracuseStep 3755603 = 5633405) B5633405
theorem B10014941 : Blo 2055435 10014941 := bstep (se 3 (by rfl) ⟨1877801, by rfl⟩ : syracuseStep 10014941 = 3755603) B3755603
theorem B6676627 : Blo 2055435 6676627 := bstep (se 1 (by rfl) ⟨5007470, by rfl⟩ : syracuseStep 6676627 = 10014941) B10014941
theorem B8902169 : Blo 2055435 8902169 := bstep (se 2 (by rfl) ⟨3338313, by rfl⟩ : syracuseStep 8902169 = 6676627) B6676627
theorem B5934779 : Blo 2055435 5934779 := bstep (se 1 (by rfl) ⟨4451084, by rfl⟩ : syracuseStep 5934779 = 8902169) B8902169
theorem B3956519 : Blo 2055435 3956519 := bstep (se 1 (by rfl) ⟨2967389, by rfl⟩ : syracuseStep 3956519 = 5934779) B5934779
theorem B2637679 : Blo 2055435 2637679 := bstep (se 1 (by rfl) ⟨1978259, by rfl⟩ : syracuseStep 2637679 = 3956519) B3956519
theorem B3516905 : Blo 2055435 3516905 := bstep (se 2 (by rfl) ⟨1318839, by rfl⟩ : syracuseStep 3516905 = 2637679) B2637679
theorem B9378413 : Blo 2055435 9378413 := bstep (se 3 (by rfl) ⟨1758452, by rfl⟩ : syracuseStep 9378413 = 3516905) B3516905
theorem B6252275 : Blo 2055435 6252275 := bstep (se 1 (by rfl) ⟨4689206, by rfl⟩ : syracuseStep 6252275 = 9378413) B9378413
theorem B4168183 : Blo 2055435 4168183 := bstep (se 1 (by rfl) ⟨3126137, by rfl⟩ : syracuseStep 4168183 = 6252275) B6252275
theorem B5557577 : Blo 2055435 5557577 := bstep (se 2 (by rfl) ⟨2084091, by rfl⟩ : syracuseStep 5557577 = 4168183) B4168183
theorem B59280821 : Blo 2055435 59280821 := bstep (se 5 (by rfl) ⟨2778788, by rfl⟩ : syracuseStep 59280821 = 5557577) B5557577
theorem B39520547 : Blo 2055435 39520547 := bstep (se 1 (by rfl) ⟨29640410, by rfl⟩ : syracuseStep 39520547 = 59280821) B59280821
theorem B26347031 : Blo 2055435 26347031 := bstep (se 1 (by rfl) ⟨19760273, by rfl⟩ : syracuseStep 26347031 = 39520547) B39520547
theorem B17564687 : Blo 2055435 17564687 := bstep (se 1 (by rfl) ⟨13173515, by rfl⟩ : syracuseStep 17564687 = 26347031) B26347031
theorem B11709791 : Blo 2055435 11709791 := bstep (se 1 (by rfl) ⟨8782343, by rfl⟩ : syracuseStep 11709791 = 17564687) B17564687
theorem B7806527 : Blo 2055435 7806527 := bstep (se 1 (by rfl) ⟨5854895, by rfl⟩ : syracuseStep 7806527 = 11709791) B11709791
theorem B5204351 : Blo 2055435 5204351 := bstep (se 1 (by rfl) ⟨3903263, by rfl⟩ : syracuseStep 5204351 = 7806527) B7806527
theorem B3469567 : Blo 2055435 3469567 := bstep (se 1 (by rfl) ⟨2602175, by rfl⟩ : syracuseStep 3469567 = 5204351) B5204351
theorem B4626089 : Blo 2055435 4626089 := bstep (se 2 (by rfl) ⟨1734783, by rfl⟩ : syracuseStep 4626089 = 3469567) B3469567
theorem B3084059 : Blo 2055435 3084059 := bstep (se 1 (by rfl) ⟨2313044, by rfl⟩ : syracuseStep 3084059 = 4626089) B4626089
theorem B2056039 : Blo 2055435 2056039 := bstep (se 1 (by rfl) ⟨1542029, by rfl⟩ : syracuseStep 2056039 = 3084059) B3084059
theorem B2313049 : Blo 2055435 2313049 := bbase (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) (by norm_num)
theorem B3084065 : Blo 2055435 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B2056043 : Blo 2055435 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B4391189 : Blo 2055435 4391189 := bbase (se 6 (by rfl) ⟨102918, by rfl⟩ : syracuseStep 4391189 = 205837) (by norm_num)
theorem B2927459 : Blo 2055435 2927459 := bstep (se 1 (by rfl) ⟨2195594, by rfl⟩ : syracuseStep 2927459 = 4391189) B4391189
theorem B7806557 : Blo 2055435 7806557 := bstep (se 3 (by rfl) ⟨1463729, by rfl⟩ : syracuseStep 7806557 = 2927459) B2927459
theorem B5204371 : Blo 2055435 5204371 := bstep (se 1 (by rfl) ⟨3903278, by rfl⟩ : syracuseStep 5204371 = 7806557) B7806557
theorem B6939161 : Blo 2055435 6939161 := bstep (se 2 (by rfl) ⟨2602185, by rfl⟩ : syracuseStep 6939161 = 5204371) B5204371
theorem B4626107 : Blo 2055435 4626107 := bstep (se 1 (by rfl) ⟨3469580, by rfl⟩ : syracuseStep 4626107 = 6939161) B6939161
theorem B3084071 : Blo 2055435 3084071 := bstep (se 1 (by rfl) ⟨2313053, by rfl⟩ : syracuseStep 3084071 = 4626107) B4626107
theorem B2056047 : Blo 2055435 2056047 := bstep (se 1 (by rfl) ⟨1542035, by rfl⟩ : syracuseStep 2056047 = 3084071) B3084071
theorem B3084077 : Blo 2055435 3084077 := bbase (se 3 (by rfl) ⟨578264, by rfl⟩ : syracuseStep 3084077 = 1156529) (by norm_num)
theorem B2056051 : Blo 2055435 2056051 := bstep (se 1 (by rfl) ⟨1542038, by rfl⟩ : syracuseStep 2056051 = 3084077) B3084077
theorem B4626125 : Blo 2055435 4626125 := bbase (se 3 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 4626125 = 1734797) (by norm_num)
theorem B3084083 : Blo 2055435 3084083 := bstep (se 1 (by rfl) ⟨2313062, by rfl⟩ : syracuseStep 3084083 = 4626125) B4626125
theorem B2056055 : Blo 2055435 2056055 := bstep (se 1 (by rfl) ⟨1542041, by rfl⟩ : syracuseStep 2056055 = 3084083) B3084083
theorem B2602201 : Blo 2055435 2602201 := bbase (se 2 (by rfl) ⟨975825, by rfl⟩ : syracuseStep 2602201 = 1951651) (by norm_num)
theorem B3469601 : Blo 2055435 3469601 := bstep (se 2 (by rfl) ⟨1301100, by rfl⟩ : syracuseStep 3469601 = 2602201) B2602201
theorem B2313067 : Blo 2055435 2313067 := bstep (se 1 (by rfl) ⟨1734800, by rfl⟩ : syracuseStep 2313067 = 3469601) B3469601
theorem B3084089 : Blo 2055435 3084089 := bstep (se 2 (by rfl) ⟨1156533, by rfl⟩ : syracuseStep 3084089 = 2313067) B2313067
theorem B2056059 : Blo 2055435 2056059 := bstep (se 1 (by rfl) ⟨1542044, by rfl⟩ : syracuseStep 2056059 = 3084089) B3084089
theorem B5275421 : Blo 2055435 5275421 := bbase (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) (by norm_num)
theorem B3516947 : Blo 2055435 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B2344631 : Blo 2055435 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B6252349 : Blo 2055435 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B8336465 : Blo 2055435 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B5557643 : Blo 2055435 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B3705095 : Blo 2055435 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B2470063 : Blo 2055435 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B3293417 : Blo 2055435 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B8782445 : Blo 2055435 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B23419853 : Blo 2055435 23419853 := bstep (se 3 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 23419853 = 8782445) B8782445
theorem B15613235 : Blo 2055435 15613235 := bstep (se 1 (by rfl) ⟨11709926, by rfl⟩ : syracuseStep 15613235 = 23419853) B23419853
theorem B10408823 : Blo 2055435 10408823 := bstep (se 1 (by rfl) ⟨7806617, by rfl⟩ : syracuseStep 10408823 = 15613235) B15613235
theorem B6939215 : Blo 2055435 6939215 := bstep (se 1 (by rfl) ⟨5204411, by rfl⟩ : syracuseStep 6939215 = 10408823) B10408823
theorem B4626143 : Blo 2055435 4626143 := bstep (se 1 (by rfl) ⟨3469607, by rfl⟩ : syracuseStep 4626143 = 6939215) B6939215
theorem B3084095 : Blo 2055435 3084095 := bstep (se 1 (by rfl) ⟨2313071, by rfl⟩ : syracuseStep 3084095 = 4626143) B4626143
theorem B2056063 : Blo 2055435 2056063 := bstep (se 1 (by rfl) ⟨1542047, by rfl⟩ : syracuseStep 2056063 = 3084095) B3084095
theorem B3084101 : Blo 2055435 3084101 := bbase (se 4 (by rfl) ⟨289134, by rfl⟩ : syracuseStep 3084101 = 578269) (by norm_num)
theorem B2056067 : Blo 2055435 2056067 := bstep (se 1 (by rfl) ⟨1542050, by rfl⟩ : syracuseStep 2056067 = 3084101) B3084101
theorem B3469621 : Blo 2055435 3469621 := bbase (se 5 (by rfl) ⟨162638, by rfl⟩ : syracuseStep 3469621 = 325277) (by norm_num)
theorem B4626161 : Blo 2055435 4626161 := bstep (se 2 (by rfl) ⟨1734810, by rfl⟩ : syracuseStep 4626161 = 3469621) B3469621
theorem B3084107 : Blo 2055435 3084107 := bstep (se 1 (by rfl) ⟨2313080, by rfl⟩ : syracuseStep 3084107 = 4626161) B4626161
theorem B2056071 : Blo 2055435 2056071 := bstep (se 1 (by rfl) ⟨1542053, by rfl⟩ : syracuseStep 2056071 = 3084107) B3084107
theorem B2313085 : Blo 2055435 2313085 := bbase (se 3 (by rfl) ⟨433703, by rfl⟩ : syracuseStep 2313085 = 867407) (by norm_num)
theorem B3084113 : Blo 2055435 3084113 := bstep (se 2 (by rfl) ⟨1156542, by rfl⟩ : syracuseStep 3084113 = 2313085) B2313085
theorem B2056075 : Blo 2055435 2056075 := bstep (se 1 (by rfl) ⟨1542056, by rfl⟩ : syracuseStep 2056075 = 3084113) B3084113
theorem B6939269 : Blo 2055435 6939269 := bbase (se 4 (by rfl) ⟨650556, by rfl⟩ : syracuseStep 6939269 = 1301113) (by norm_num)
theorem B4626179 : Blo 2055435 4626179 := bstep (se 1 (by rfl) ⟨3469634, by rfl⟩ : syracuseStep 4626179 = 6939269) B6939269
theorem B3084119 : Blo 2055435 3084119 := bstep (se 1 (by rfl) ⟨2313089, by rfl⟩ : syracuseStep 3084119 = 4626179) B4626179
theorem B2056079 : Blo 2055435 2056079 := bstep (se 1 (by rfl) ⟨1542059, by rfl⟩ : syracuseStep 2056079 = 3084119) B3084119
theorem B3084125 : Blo 2055435 3084125 := bbase (se 3 (by rfl) ⟨578273, by rfl⟩ : syracuseStep 3084125 = 1156547) (by norm_num)
theorem B2056083 : Blo 2055435 2056083 := bstep (se 1 (by rfl) ⟨1542062, by rfl⟩ : syracuseStep 2056083 = 3084125) B3084125
theorem B4626197 : Blo 2055435 4626197 := bbase (se 6 (by rfl) ⟨108426, by rfl⟩ : syracuseStep 4626197 = 216853) (by norm_num)
theorem B3084131 : Blo 2055435 3084131 := bstep (se 1 (by rfl) ⟨2313098, by rfl⟩ : syracuseStep 3084131 = 4626197) B4626197
theorem B2056087 : Blo 2055435 2056087 := bstep (se 1 (by rfl) ⟨1542065, by rfl⟩ : syracuseStep 2056087 = 3084131) B3084131
theorem B7806725 : Blo 2055435 7806725 := bbase (se 4 (by rfl) ⟨731880, by rfl⟩ : syracuseStep 7806725 = 1463761) (by norm_num)
theorem B5204483 : Blo 2055435 5204483 := bstep (se 1 (by rfl) ⟨3903362, by rfl⟩ : syracuseStep 5204483 = 7806725) B7806725
theorem B3469655 : Blo 2055435 3469655 := bstep (se 1 (by rfl) ⟨2602241, by rfl⟩ : syracuseStep 3469655 = 5204483) B5204483
theorem B2313103 : Blo 2055435 2313103 := bstep (se 1 (by rfl) ⟨1734827, by rfl⟩ : syracuseStep 2313103 = 3469655) B3469655
theorem B3084137 : Blo 2055435 3084137 := bstep (se 2 (by rfl) ⟨1156551, by rfl⟩ : syracuseStep 3084137 = 2313103) B2313103
theorem B2056091 : Blo 2055435 2056091 := bstep (se 1 (by rfl) ⟨1542068, by rfl⟩ : syracuseStep 2056091 = 3084137) B3084137
theorem B3338405 : Blo 2055435 3338405 := bbase (se 4 (by rfl) ⟨312975, by rfl⟩ : syracuseStep 3338405 = 625951) (by norm_num)
theorem B2225603 : Blo 2055435 2225603 := bstep (se 1 (by rfl) ⟨1669202, by rfl⟩ : syracuseStep 2225603 = 3338405) B3338405
theorem B5934941 : Blo 2055435 5934941 := bstep (se 3 (by rfl) ⟨1112801, by rfl⟩ : syracuseStep 5934941 = 2225603) B2225603
theorem B3956627 : Blo 2055435 3956627 := bstep (se 1 (by rfl) ⟨2967470, by rfl⟩ : syracuseStep 3956627 = 5934941) B5934941
theorem B10551005 : Blo 2055435 10551005 := bstep (se 3 (by rfl) ⟨1978313, by rfl⟩ : syracuseStep 10551005 = 3956627) B3956627
theorem B7034003 : Blo 2055435 7034003 := bstep (se 1 (by rfl) ⟨5275502, by rfl⟩ : syracuseStep 7034003 = 10551005) B10551005
theorem B4689335 : Blo 2055435 4689335 := bstep (se 1 (by rfl) ⟨3517001, by rfl⟩ : syracuseStep 4689335 = 7034003) B7034003
theorem B3126223 : Blo 2055435 3126223 := bstep (se 1 (by rfl) ⟨2344667, by rfl⟩ : syracuseStep 3126223 = 4689335) B4689335
theorem B4168297 : Blo 2055435 4168297 := bstep (se 2 (by rfl) ⟨1563111, by rfl⟩ : syracuseStep 4168297 = 3126223) B3126223
theorem B5557729 : Blo 2055435 5557729 := bstep (se 2 (by rfl) ⟨2084148, by rfl⟩ : syracuseStep 5557729 = 4168297) B4168297
theorem B7410305 : Blo 2055435 7410305 := bstep (se 2 (by rfl) ⟨2778864, by rfl⟩ : syracuseStep 7410305 = 5557729) B5557729
theorem B4940203 : Blo 2055435 4940203 := bstep (se 1 (by rfl) ⟨3705152, by rfl⟩ : syracuseStep 4940203 = 7410305) B7410305
theorem B6586937 : Blo 2055435 6586937 := bstep (se 2 (by rfl) ⟨2470101, by rfl⟩ : syracuseStep 6586937 = 4940203) B4940203
theorem B4391291 : Blo 2055435 4391291 := bstep (se 1 (by rfl) ⟨3293468, by rfl⟩ : syracuseStep 4391291 = 6586937) B6586937
theorem B11710109 : Blo 2055435 11710109 := bstep (se 3 (by rfl) ⟨2195645, by rfl⟩ : syracuseStep 11710109 = 4391291) B4391291
theorem B7806739 : Blo 2055435 7806739 := bstep (se 1 (by rfl) ⟨5855054, by rfl⟩ : syracuseStep 7806739 = 11710109) B11710109
theorem B10408985 : Blo 2055435 10408985 := bstep (se 2 (by rfl) ⟨3903369, by rfl⟩ : syracuseStep 10408985 = 7806739) B7806739
theorem B6939323 : Blo 2055435 6939323 := bstep (se 1 (by rfl) ⟨5204492, by rfl⟩ : syracuseStep 6939323 = 10408985) B10408985
theorem B4626215 : Blo 2055435 4626215 := bstep (se 1 (by rfl) ⟨3469661, by rfl⟩ : syracuseStep 4626215 = 6939323) B6939323
theorem B3084143 : Blo 2055435 3084143 := bstep (se 1 (by rfl) ⟨2313107, by rfl⟩ : syracuseStep 3084143 = 4626215) B4626215
theorem B2056095 : Blo 2055435 2056095 := bstep (se 1 (by rfl) ⟨1542071, by rfl⟩ : syracuseStep 2056095 = 3084143) B3084143
theorem B3084149 : Blo 2055435 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B2056099 : Blo 2055435 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B4391309 : Blo 2055435 4391309 := bbase (se 3 (by rfl) ⟨823370, by rfl⟩ : syracuseStep 4391309 = 1646741) (by norm_num)
theorem B2927539 : Blo 2055435 2927539 := bstep (se 1 (by rfl) ⟨2195654, by rfl⟩ : syracuseStep 2927539 = 4391309) B4391309
theorem B3903385 : Blo 2055435 3903385 := bstep (se 2 (by rfl) ⟨1463769, by rfl⟩ : syracuseStep 3903385 = 2927539) B2927539
theorem B5204513 : Blo 2055435 5204513 := bstep (se 2 (by rfl) ⟨1951692, by rfl⟩ : syracuseStep 5204513 = 3903385) B3903385
theorem B3469675 : Blo 2055435 3469675 := bstep (se 1 (by rfl) ⟨2602256, by rfl⟩ : syracuseStep 3469675 = 5204513) B5204513
theorem B4626233 : Blo 2055435 4626233 := bstep (se 2 (by rfl) ⟨1734837, by rfl⟩ : syracuseStep 4626233 = 3469675) B3469675
theorem B3084155 : Blo 2055435 3084155 := bstep (se 1 (by rfl) ⟨2313116, by rfl⟩ : syracuseStep 3084155 = 4626233) B4626233
theorem B2056103 : Blo 2055435 2056103 := bstep (se 1 (by rfl) ⟨1542077, by rfl⟩ : syracuseStep 2056103 = 3084155) B3084155
theorem B2313121 : Blo 2055435 2313121 := bbase (se 2 (by rfl) ⟨867420, by rfl⟩ : syracuseStep 2313121 = 1734841) (by norm_num)
theorem B3084161 : Blo 2055435 3084161 := bstep (se 2 (by rfl) ⟨1156560, by rfl⟩ : syracuseStep 3084161 = 2313121) B2313121
theorem B2056107 : Blo 2055435 2056107 := bstep (se 1 (by rfl) ⟨1542080, by rfl⟩ : syracuseStep 2056107 = 3084161) B3084161
theorem B5204533 : Blo 2055435 5204533 := bbase (se 5 (by rfl) ⟨243962, by rfl⟩ : syracuseStep 5204533 = 487925) (by norm_num)
theorem B6939377 : Blo 2055435 6939377 := bstep (se 2 (by rfl) ⟨2602266, by rfl⟩ : syracuseStep 6939377 = 5204533) B5204533
theorem B4626251 : Blo 2055435 4626251 := bstep (se 1 (by rfl) ⟨3469688, by rfl⟩ : syracuseStep 4626251 = 6939377) B6939377
theorem B3084167 : Blo 2055435 3084167 := bstep (se 1 (by rfl) ⟨2313125, by rfl⟩ : syracuseStep 3084167 = 4626251) B4626251
theorem B2056111 : Blo 2055435 2056111 := bstep (se 1 (by rfl) ⟨1542083, by rfl⟩ : syracuseStep 2056111 = 3084167) B3084167
theorem B3084173 : Blo 2055435 3084173 := bbase (se 3 (by rfl) ⟨578282, by rfl⟩ : syracuseStep 3084173 = 1156565) (by norm_num)
theorem B2056115 : Blo 2055435 2056115 := bstep (se 1 (by rfl) ⟨1542086, by rfl⟩ : syracuseStep 2056115 = 3084173) B3084173
theorem B4626269 : Blo 2055435 4626269 := bbase (se 3 (by rfl) ⟨867425, by rfl⟩ : syracuseStep 4626269 = 1734851) (by norm_num)
theorem B3084179 : Blo 2055435 3084179 := bstep (se 1 (by rfl) ⟨2313134, by rfl⟩ : syracuseStep 3084179 = 4626269) B4626269
theorem B2056119 : Blo 2055435 2056119 := bstep (se 1 (by rfl) ⟨1542089, by rfl⟩ : syracuseStep 2056119 = 3084179) B3084179
theorem B3469709 : Blo 2055435 3469709 := bbase (se 3 (by rfl) ⟨650570, by rfl⟩ : syracuseStep 3469709 = 1301141) (by norm_num)
theorem B2313139 : Blo 2055435 2313139 := bstep (se 1 (by rfl) ⟨1734854, by rfl⟩ : syracuseStep 2313139 = 3469709) B3469709
theorem B3084185 : Blo 2055435 3084185 := bstep (se 2 (by rfl) ⟨1156569, by rfl⟩ : syracuseStep 3084185 = 2313139) B2313139
theorem B2056123 : Blo 2055435 2056123 := bstep (se 1 (by rfl) ⟨1542092, by rfl⟩ : syracuseStep 2056123 = 3084185) B3084185
theorem B2503841 : Blo 2055435 2503841 := bbase (se 2 (by rfl) ⟨938940, by rfl⟩ : syracuseStep 2503841 = 1877881) (by norm_num)
theorem B26707637 : Blo 2055435 26707637 := bstep (se 5 (by rfl) ⟨1251920, by rfl⟩ : syracuseStep 26707637 = 2503841) B2503841
theorem B17805091 : Blo 2055435 17805091 := bstep (se 1 (by rfl) ⟨13353818, by rfl⟩ : syracuseStep 17805091 = 26707637) B26707637
theorem B23740121 : Blo 2055435 23740121 := bstep (se 2 (by rfl) ⟨8902545, by rfl⟩ : syracuseStep 23740121 = 17805091) B17805091
theorem B15826747 : Blo 2055435 15826747 := bstep (se 1 (by rfl) ⟨11870060, by rfl⟩ : syracuseStep 15826747 = 23740121) B23740121
theorem B21102329 : Blo 2055435 21102329 := bstep (se 2 (by rfl) ⟨7913373, by rfl⟩ : syracuseStep 21102329 = 15826747) B15826747
theorem B56272877 : Blo 2055435 56272877 := bstep (se 3 (by rfl) ⟨10551164, by rfl⟩ : syracuseStep 56272877 = 21102329) B21102329
theorem B37515251 : Blo 2055435 37515251 := bstep (se 1 (by rfl) ⟨28136438, by rfl⟩ : syracuseStep 37515251 = 56272877) B56272877
theorem B25010167 : Blo 2055435 25010167 := bstep (se 1 (by rfl) ⟨18757625, by rfl⟩ : syracuseStep 25010167 = 37515251) B37515251
theorem B33346889 : Blo 2055435 33346889 := bstep (se 2 (by rfl) ⟨12505083, by rfl⟩ : syracuseStep 33346889 = 25010167) B25010167
theorem B22231259 : Blo 2055435 22231259 := bstep (se 1 (by rfl) ⟨16673444, by rfl⟩ : syracuseStep 22231259 = 33346889) B33346889
theorem B14820839 : Blo 2055435 14820839 := bstep (se 1 (by rfl) ⟨11115629, by rfl⟩ : syracuseStep 14820839 = 22231259) B22231259
theorem B9880559 : Blo 2055435 9880559 := bstep (se 1 (by rfl) ⟨7410419, by rfl⟩ : syracuseStep 9880559 = 14820839) B14820839
theorem B6587039 : Blo 2055435 6587039 := bstep (se 1 (by rfl) ⟨4940279, by rfl⟩ : syracuseStep 6587039 = 9880559) B9880559
theorem B17565437 : Blo 2055435 17565437 := bstep (se 3 (by rfl) ⟨3293519, by rfl⟩ : syracuseStep 17565437 = 6587039) B6587039
theorem B11710291 : Blo 2055435 11710291 := bstep (se 1 (by rfl) ⟨8782718, by rfl⟩ : syracuseStep 11710291 = 17565437) B17565437
theorem B15613721 : Blo 2055435 15613721 := bstep (se 2 (by rfl) ⟨5855145, by rfl⟩ : syracuseStep 15613721 = 11710291) B11710291
theorem B10409147 : Blo 2055435 10409147 := bstep (se 1 (by rfl) ⟨7806860, by rfl⟩ : syracuseStep 10409147 = 15613721) B15613721
theorem B6939431 : Blo 2055435 6939431 := bstep (se 1 (by rfl) ⟨5204573, by rfl⟩ : syracuseStep 6939431 = 10409147) B10409147
theorem B4626287 : Blo 2055435 4626287 := bstep (se 1 (by rfl) ⟨3469715, by rfl⟩ : syracuseStep 4626287 = 6939431) B6939431
theorem B3084191 : Blo 2055435 3084191 := bstep (se 1 (by rfl) ⟨2313143, by rfl⟩ : syracuseStep 3084191 = 4626287) B4626287
theorem B2056127 : Blo 2055435 2056127 := bstep (se 1 (by rfl) ⟨1542095, by rfl⟩ : syracuseStep 2056127 = 3084191) B3084191
theorem B3084197 : Blo 2055435 3084197 := bbase (se 4 (by rfl) ⟨289143, by rfl⟩ : syracuseStep 3084197 = 578287) (by norm_num)
theorem B2056131 : Blo 2055435 2056131 := bstep (se 1 (by rfl) ⟨1542098, by rfl⟩ : syracuseStep 2056131 = 3084197) B3084197
theorem B2602297 : Blo 2055435 2602297 := bbase (se 2 (by rfl) ⟨975861, by rfl⟩ : syracuseStep 2602297 = 1951723) (by norm_num)
theorem B3469729 : Blo 2055435 3469729 := bstep (se 2 (by rfl) ⟨1301148, by rfl⟩ : syracuseStep 3469729 = 2602297) B2602297
theorem B4626305 : Blo 2055435 4626305 := bstep (se 2 (by rfl) ⟨1734864, by rfl⟩ : syracuseStep 4626305 = 3469729) B3469729
theorem B3084203 : Blo 2055435 3084203 := bstep (se 1 (by rfl) ⟨2313152, by rfl⟩ : syracuseStep 3084203 = 4626305) B4626305
theorem B2056135 : Blo 2055435 2056135 := bstep (se 1 (by rfl) ⟨1542101, by rfl⟩ : syracuseStep 2056135 = 3084203) B3084203
theorem B2313157 : Blo 2055435 2313157 := bbase (se 4 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 2313157 = 433717) (by norm_num)
theorem B3084209 : Blo 2055435 3084209 := bstep (se 2 (by rfl) ⟨1156578, by rfl⟩ : syracuseStep 3084209 = 2313157) B2313157
theorem B2056139 : Blo 2055435 2056139 := bstep (se 1 (by rfl) ⟨1542104, by rfl⟩ : syracuseStep 2056139 = 3084209) B3084209
theorem B3903461 : Blo 2055435 3903461 := bbase (se 4 (by rfl) ⟨365949, by rfl⟩ : syracuseStep 3903461 = 731899) (by norm_num)
theorem B2602307 : Blo 2055435 2602307 := bstep (se 1 (by rfl) ⟨1951730, by rfl⟩ : syracuseStep 2602307 = 3903461) B3903461
theorem B6939485 : Blo 2055435 6939485 := bstep (se 3 (by rfl) ⟨1301153, by rfl⟩ : syracuseStep 6939485 = 2602307) B2602307
theorem B4626323 : Blo 2055435 4626323 := bstep (se 1 (by rfl) ⟨3469742, by rfl⟩ : syracuseStep 4626323 = 6939485) B6939485
theorem B3084215 : Blo 2055435 3084215 := bstep (se 1 (by rfl) ⟨2313161, by rfl⟩ : syracuseStep 3084215 = 4626323) B4626323
theorem B2056143 : Blo 2055435 2056143 := bstep (se 1 (by rfl) ⟨1542107, by rfl⟩ : syracuseStep 2056143 = 3084215) B3084215
theorem B3084221 : Blo 2055435 3084221 := bbase (se 3 (by rfl) ⟨578291, by rfl⟩ : syracuseStep 3084221 = 1156583) (by norm_num)
theorem B2056147 : Blo 2055435 2056147 := bstep (se 1 (by rfl) ⟨1542110, by rfl⟩ : syracuseStep 2056147 = 3084221) B3084221
theorem B4626341 : Blo 2055435 4626341 := bbase (se 4 (by rfl) ⟨433719, by rfl⟩ : syracuseStep 4626341 = 867439) (by norm_num)
theorem B3084227 : Blo 2055435 3084227 := bstep (se 1 (by rfl) ⟨2313170, by rfl⟩ : syracuseStep 3084227 = 4626341) B4626341
theorem B2056151 : Blo 2055435 2056151 := bstep (se 1 (by rfl) ⟨1542113, by rfl⟩ : syracuseStep 2056151 = 3084227) B3084227
theorem B5204645 : Blo 2055435 5204645 := bbase (se 4 (by rfl) ⟨487935, by rfl⟩ : syracuseStep 5204645 = 975871) (by norm_num)
theorem B3469763 : Blo 2055435 3469763 := bstep (se 1 (by rfl) ⟨2602322, by rfl⟩ : syracuseStep 3469763 = 5204645) B5204645
theorem B2313175 : Blo 2055435 2313175 := bstep (se 1 (by rfl) ⟨1734881, by rfl⟩ : syracuseStep 2313175 = 3469763) B3469763
theorem B3084233 : Blo 2055435 3084233 := bstep (se 2 (by rfl) ⟨1156587, by rfl⟩ : syracuseStep 3084233 = 2313175) B2313175
theorem B2056155 : Blo 2055435 2056155 := bstep (se 1 (by rfl) ⟨1542116, by rfl⟩ : syracuseStep 2056155 = 3084233) B3084233
theorem B5855237 : Blo 2055435 5855237 := bbase (se 4 (by rfl) ⟨548928, by rfl⟩ : syracuseStep 5855237 = 1097857) (by norm_num)
theorem B3903491 : Blo 2055435 3903491 := bstep (se 1 (by rfl) ⟨2927618, by rfl⟩ : syracuseStep 3903491 = 5855237) B5855237
theorem B10409309 : Blo 2055435 10409309 := bstep (se 3 (by rfl) ⟨1951745, by rfl⟩ : syracuseStep 10409309 = 3903491) B3903491
theorem B6939539 : Blo 2055435 6939539 := bstep (se 1 (by rfl) ⟨5204654, by rfl⟩ : syracuseStep 6939539 = 10409309) B10409309
theorem B4626359 : Blo 2055435 4626359 := bstep (se 1 (by rfl) ⟨3469769, by rfl⟩ : syracuseStep 4626359 = 6939539) B6939539
theorem B3084239 : Blo 2055435 3084239 := bstep (se 1 (by rfl) ⟨2313179, by rfl⟩ : syracuseStep 3084239 = 4626359) B4626359
theorem B2056159 : Blo 2055435 2056159 := bstep (se 1 (by rfl) ⟨1542119, by rfl⟩ : syracuseStep 2056159 = 3084239) B3084239
theorem B3084245 : Blo 2055435 3084245 := bbase (se 7 (by rfl) ⟨36143, by rfl⟩ : syracuseStep 3084245 = 72287) (by norm_num)
theorem B2056163 : Blo 2055435 2056163 := bstep (se 1 (by rfl) ⟨1542122, by rfl⟩ : syracuseStep 2056163 = 3084245) B3084245
theorem B7807013 : Blo 2055435 7807013 := bbase (se 4 (by rfl) ⟨731907, by rfl⟩ : syracuseStep 7807013 = 1463815) (by norm_num)
theorem B5204675 : Blo 2055435 5204675 := bstep (se 1 (by rfl) ⟨3903506, by rfl⟩ : syracuseStep 5204675 = 7807013) B7807013
theorem B3469783 : Blo 2055435 3469783 := bstep (se 1 (by rfl) ⟨2602337, by rfl⟩ : syracuseStep 3469783 = 5204675) B5204675
theorem B4626377 : Blo 2055435 4626377 := bstep (se 2 (by rfl) ⟨1734891, by rfl⟩ : syracuseStep 4626377 = 3469783) B3469783
theorem B3084251 : Blo 2055435 3084251 := bstep (se 1 (by rfl) ⟨2313188, by rfl⟩ : syracuseStep 3084251 = 4626377) B4626377
theorem B2056167 : Blo 2055435 2056167 := bstep (se 1 (by rfl) ⟨1542125, by rfl⟩ : syracuseStep 2056167 = 3084251) B3084251
theorem B2313193 : Blo 2055435 2313193 := bbase (se 2 (by rfl) ⟨867447, by rfl⟩ : syracuseStep 2313193 = 1734895) (by norm_num)
theorem B3084257 : Blo 2055435 3084257 := bstep (se 2 (by rfl) ⟨1156596, by rfl⟩ : syracuseStep 3084257 = 2313193) B2313193
theorem B2056171 : Blo 2055435 2056171 := bstep (se 1 (by rfl) ⟨1542128, by rfl⟩ : syracuseStep 2056171 = 3084257) B3084257
theorem B3293597 : Blo 2055435 3293597 := bbase (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) (by norm_num)
theorem B2195731 : Blo 2055435 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B11710565 : Blo 2055435 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B7807043 : Blo 2055435 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B5204695 : Blo 2055435 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B6939593 : Blo 2055435 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B4626395 : Blo 2055435 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B3084263 : Blo 2055435 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B2056175 : Blo 2055435 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B3084269 : Blo 2055435 3084269 := bbase (se 3 (by rfl) ⟨578300, by rfl⟩ : syracuseStep 3084269 = 1156601) (by norm_num)
theorem B2056179 : Blo 2055435 2056179 := bstep (se 1 (by rfl) ⟨1542134, by rfl⟩ : syracuseStep 2056179 = 3084269) B3084269
theorem B4626413 : Blo 2055435 4626413 := bbase (se 3 (by rfl) ⟨867452, by rfl⟩ : syracuseStep 4626413 = 1734905) (by norm_num)
theorem B3084275 : Blo 2055435 3084275 := bstep (se 1 (by rfl) ⟨2313206, by rfl⟩ : syracuseStep 3084275 = 4626413) B4626413
theorem B2056183 : Blo 2055435 2056183 := bstep (se 1 (by rfl) ⟨1542137, by rfl⟩ : syracuseStep 2056183 = 3084275) B3084275
theorem B2470213 : Blo 2055435 2470213 := bbase (se 4 (by rfl) ⟨231582, by rfl⟩ : syracuseStep 2470213 = 463165) (by norm_num)
theorem B3293617 : Blo 2055435 3293617 := bstep (se 2 (by rfl) ⟨1235106, by rfl⟩ : syracuseStep 3293617 = 2470213) B2470213
theorem B4391489 : Blo 2055435 4391489 := bstep (se 2 (by rfl) ⟨1646808, by rfl⟩ : syracuseStep 4391489 = 3293617) B3293617
theorem B2927659 : Blo 2055435 2927659 := bstep (se 1 (by rfl) ⟨2195744, by rfl⟩ : syracuseStep 2927659 = 4391489) B4391489
theorem B3903545 : Blo 2055435 3903545 := bstep (se 2 (by rfl) ⟨1463829, by rfl⟩ : syracuseStep 3903545 = 2927659) B2927659
theorem B2602363 : Blo 2055435 2602363 := bstep (se 1 (by rfl) ⟨1951772, by rfl⟩ : syracuseStep 2602363 = 3903545) B3903545
theorem B3469817 : Blo 2055435 3469817 := bstep (se 2 (by rfl) ⟨1301181, by rfl⟩ : syracuseStep 3469817 = 2602363) B2602363
theorem B2313211 : Blo 2055435 2313211 := bstep (se 1 (by rfl) ⟨1734908, by rfl⟩ : syracuseStep 2313211 = 3469817) B3469817
theorem B3084281 : Blo 2055435 3084281 := bstep (se 2 (by rfl) ⟨1156605, by rfl⟩ : syracuseStep 3084281 = 2313211) B2313211
theorem B2056187 : Blo 2055435 2056187 := bstep (se 1 (by rfl) ⟨1542140, by rfl⟩ : syracuseStep 2056187 = 3084281) B3084281
theorem B142445141 : Blo 2055435 142445141 := bbase (se 8 (by rfl) ⟨834639, by rfl⟩ : syracuseStep 142445141 = 1669279) (by norm_num)
theorem B94963427 : Blo 2055435 94963427 := bstep (se 1 (by rfl) ⟨71222570, by rfl⟩ : syracuseStep 94963427 = 142445141) B142445141
theorem B63308951 : Blo 2055435 63308951 := bstep (se 1 (by rfl) ⟨47481713, by rfl⟩ : syracuseStep 63308951 = 94963427) B94963427
theorem B42205967 : Blo 2055435 42205967 := bstep (se 1 (by rfl) ⟨31654475, by rfl⟩ : syracuseStep 42205967 = 63308951) B63308951
theorem B28137311 : Blo 2055435 28137311 := bstep (se 1 (by rfl) ⟨21102983, by rfl⟩ : syracuseStep 28137311 = 42205967) B42205967
theorem B18758207 : Blo 2055435 18758207 := bstep (se 1 (by rfl) ⟨14068655, by rfl⟩ : syracuseStep 18758207 = 28137311) B28137311
theorem B12505471 : Blo 2055435 12505471 := bstep (se 1 (by rfl) ⟨9379103, by rfl⟩ : syracuseStep 12505471 = 18758207) B18758207
theorem B266783381 : Blo 2055435 266783381 := bstep (se 6 (by rfl) ⟨6252735, by rfl⟩ : syracuseStep 266783381 = 12505471) B12505471
theorem B177855587 : Blo 2055435 177855587 := bstep (se 1 (by rfl) ⟨133391690, by rfl⟩ : syracuseStep 177855587 = 266783381) B266783381
theorem B118570391 : Blo 2055435 118570391 := bstep (se 1 (by rfl) ⟨88927793, by rfl⟩ : syracuseStep 118570391 = 177855587) B177855587
theorem B79046927 : Blo 2055435 79046927 := bstep (se 1 (by rfl) ⟨59285195, by rfl⟩ : syracuseStep 79046927 = 118570391) B118570391
theorem B52697951 : Blo 2055435 52697951 := bstep (se 1 (by rfl) ⟨39523463, by rfl⟩ : syracuseStep 52697951 = 79046927) B79046927
theorem B35131967 : Blo 2055435 35131967 := bstep (se 1 (by rfl) ⟨26348975, by rfl⟩ : syracuseStep 35131967 = 52697951) B52697951
theorem B23421311 : Blo 2055435 23421311 := bstep (se 1 (by rfl) ⟨17565983, by rfl⟩ : syracuseStep 23421311 = 35131967) B35131967
theorem B15614207 : Blo 2055435 15614207 := bstep (se 1 (by rfl) ⟨11710655, by rfl⟩ : syracuseStep 15614207 = 23421311) B23421311
theorem B10409471 : Blo 2055435 10409471 := bstep (se 1 (by rfl) ⟨7807103, by rfl⟩ : syracuseStep 10409471 = 15614207) B15614207
theorem B6939647 : Blo 2055435 6939647 := bstep (se 1 (by rfl) ⟨5204735, by rfl⟩ : syracuseStep 6939647 = 10409471) B10409471
theorem B4626431 : Blo 2055435 4626431 := bstep (se 1 (by rfl) ⟨3469823, by rfl⟩ : syracuseStep 4626431 = 6939647) B6939647
theorem B3084287 : Blo 2055435 3084287 := bstep (se 1 (by rfl) ⟨2313215, by rfl⟩ : syracuseStep 3084287 = 4626431) B4626431
theorem B2056191 : Blo 2055435 2056191 := bstep (se 1 (by rfl) ⟨1542143, by rfl⟩ : syracuseStep 2056191 = 3084287) B3084287
theorem B3084293 : Blo 2055435 3084293 := bbase (se 4 (by rfl) ⟨289152, by rfl⟩ : syracuseStep 3084293 = 578305) (by norm_num)
theorem B2056195 : Blo 2055435 2056195 := bstep (se 1 (by rfl) ⟨1542146, by rfl⟩ : syracuseStep 2056195 = 3084293) B3084293
theorem B3469837 : Blo 2055435 3469837 := bbase (se 3 (by rfl) ⟨650594, by rfl⟩ : syracuseStep 3469837 = 1301189) (by norm_num)
theorem B4626449 : Blo 2055435 4626449 := bstep (se 2 (by rfl) ⟨1734918, by rfl⟩ : syracuseStep 4626449 = 3469837) B3469837
theorem B3084299 : Blo 2055435 3084299 := bstep (se 1 (by rfl) ⟨2313224, by rfl⟩ : syracuseStep 3084299 = 4626449) B4626449
theorem B2056199 : Blo 2055435 2056199 := bstep (se 1 (by rfl) ⟨1542149, by rfl⟩ : syracuseStep 2056199 = 3084299) B3084299
theorem B2313229 : Blo 2055435 2313229 := bbase (se 3 (by rfl) ⟨433730, by rfl⟩ : syracuseStep 2313229 = 867461) (by norm_num)
theorem B3084305 : Blo 2055435 3084305 := bstep (se 2 (by rfl) ⟨1156614, by rfl⟩ : syracuseStep 3084305 = 2313229) B2313229
theorem B2056203 : Blo 2055435 2056203 := bstep (se 1 (by rfl) ⟨1542152, by rfl⟩ : syracuseStep 2056203 = 3084305) B3084305
theorem B6939701 : Blo 2055435 6939701 := bbase (se 5 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 6939701 = 650597) (by norm_num)
theorem B4626467 : Blo 2055435 4626467 := bstep (se 1 (by rfl) ⟨3469850, by rfl⟩ : syracuseStep 4626467 = 6939701) B6939701
theorem B3084311 : Blo 2055435 3084311 := bstep (se 1 (by rfl) ⟨2313233, by rfl⟩ : syracuseStep 3084311 = 4626467) B4626467
theorem B2056207 : Blo 2055435 2056207 := bstep (se 1 (by rfl) ⟨1542155, by rfl⟩ : syracuseStep 2056207 = 3084311) B3084311
theorem B3084317 : Blo 2055435 3084317 := bbase (se 3 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 3084317 = 1156619) (by norm_num)
theorem B2056211 : Blo 2055435 2056211 := bstep (se 1 (by rfl) ⟨1542158, by rfl⟩ : syracuseStep 2056211 = 3084317) B3084317
theorem B4626485 : Blo 2055435 4626485 := bbase (se 5 (by rfl) ⟨216866, by rfl⟩ : syracuseStep 4626485 = 433733) (by norm_num)
theorem B3084323 : Blo 2055435 3084323 := bstep (se 1 (by rfl) ⟨2313242, by rfl⟩ : syracuseStep 3084323 = 4626485) B4626485
theorem B2056215 : Blo 2055435 2056215 := bstep (se 1 (by rfl) ⟨1542161, by rfl⟩ : syracuseStep 2056215 = 3084323) B3084323
theorem B14068853 : Blo 2055435 14068853 := bbase (se 5 (by rfl) ⟨659477, by rfl⟩ : syracuseStep 14068853 = 1318955) (by norm_num)
theorem B9379235 : Blo 2055435 9379235 := bstep (se 1 (by rfl) ⟨7034426, by rfl⟩ : syracuseStep 9379235 = 14068853) B14068853
theorem B6252823 : Blo 2055435 6252823 := bstep (se 1 (by rfl) ⟨4689617, by rfl⟩ : syracuseStep 6252823 = 9379235) B9379235
theorem B8337097 : Blo 2055435 8337097 := bstep (se 2 (by rfl) ⟨3126411, by rfl⟩ : syracuseStep 8337097 = 6252823) B6252823
theorem B11116129 : Blo 2055435 11116129 := bstep (se 2 (by rfl) ⟨4168548, by rfl⟩ : syracuseStep 11116129 = 8337097) B8337097
theorem B14821505 : Blo 2055435 14821505 := bstep (se 2 (by rfl) ⟨5558064, by rfl⟩ : syracuseStep 14821505 = 11116129) B11116129
theorem B9881003 : Blo 2055435 9881003 := bstep (se 1 (by rfl) ⟨7410752, by rfl⟩ : syracuseStep 9881003 = 14821505) B14821505
theorem B6587335 : Blo 2055435 6587335 := bstep (se 1 (by rfl) ⟨4940501, by rfl⟩ : syracuseStep 6587335 = 9881003) B9881003
theorem B8783113 : Blo 2055435 8783113 := bstep (se 2 (by rfl) ⟨3293667, by rfl⟩ : syracuseStep 8783113 = 6587335) B6587335
theorem B11710817 : Blo 2055435 11710817 := bstep (se 2 (by rfl) ⟨4391556, by rfl⟩ : syracuseStep 11710817 = 8783113) B8783113
theorem B7807211 : Blo 2055435 7807211 := bstep (se 1 (by rfl) ⟨5855408, by rfl⟩ : syracuseStep 7807211 = 11710817) B11710817
theorem B5204807 : Blo 2055435 5204807 := bstep (se 1 (by rfl) ⟨3903605, by rfl⟩ : syracuseStep 5204807 = 7807211) B7807211
theorem B3469871 : Blo 2055435 3469871 := bstep (se 1 (by rfl) ⟨2602403, by rfl⟩ : syracuseStep 3469871 = 5204807) B5204807
theorem B2313247 : Blo 2055435 2313247 := bstep (se 1 (by rfl) ⟨1734935, by rfl⟩ : syracuseStep 2313247 = 3469871) B3469871
theorem B3084329 : Blo 2055435 3084329 := bstep (se 2 (by rfl) ⟨1156623, by rfl⟩ : syracuseStep 3084329 = 2313247) B2313247
theorem B2056219 : Blo 2055435 2056219 := bstep (se 1 (by rfl) ⟨1542164, by rfl⟩ : syracuseStep 2056219 = 3084329) B3084329
theorem B9379253 : Blo 2055435 9379253 := bbase (se 5 (by rfl) ⟨439652, by rfl⟩ : syracuseStep 9379253 = 879305) (by norm_num)
theorem B6252835 : Blo 2055435 6252835 := bstep (se 1 (by rfl) ⟨4689626, by rfl⟩ : syracuseStep 6252835 = 9379253) B9379253
theorem B8337113 : Blo 2055435 8337113 := bstep (se 2 (by rfl) ⟨3126417, by rfl⟩ : syracuseStep 8337113 = 6252835) B6252835
theorem B5558075 : Blo 2055435 5558075 := bstep (se 1 (by rfl) ⟨4168556, by rfl⟩ : syracuseStep 5558075 = 8337113) B8337113
theorem B3705383 : Blo 2055435 3705383 := bstep (se 1 (by rfl) ⟨2779037, by rfl⟩ : syracuseStep 3705383 = 5558075) B5558075
theorem B9881021 : Blo 2055435 9881021 := bstep (se 3 (by rfl) ⟨1852691, by rfl⟩ : syracuseStep 9881021 = 3705383) B3705383
theorem B6587347 : Blo 2055435 6587347 := bstep (se 1 (by rfl) ⟨4940510, by rfl⟩ : syracuseStep 6587347 = 9881021) B9881021
theorem B8783129 : Blo 2055435 8783129 := bstep (se 2 (by rfl) ⟨3293673, by rfl⟩ : syracuseStep 8783129 = 6587347) B6587347
theorem B5855419 : Blo 2055435 5855419 := bstep (se 1 (by rfl) ⟨4391564, by rfl⟩ : syracuseStep 5855419 = 8783129) B8783129
theorem B7807225 : Blo 2055435 7807225 := bstep (se 2 (by rfl) ⟨2927709, by rfl⟩ : syracuseStep 7807225 = 5855419) B5855419
theorem B10409633 : Blo 2055435 10409633 := bstep (se 2 (by rfl) ⟨3903612, by rfl⟩ : syracuseStep 10409633 = 7807225) B7807225
theorem B6939755 : Blo 2055435 6939755 := bstep (se 1 (by rfl) ⟨5204816, by rfl⟩ : syracuseStep 6939755 = 10409633) B10409633
theorem B4626503 : Blo 2055435 4626503 := bstep (se 1 (by rfl) ⟨3469877, by rfl⟩ : syracuseStep 4626503 = 6939755) B6939755
theorem B3084335 : Blo 2055435 3084335 := bstep (se 1 (by rfl) ⟨2313251, by rfl⟩ : syracuseStep 3084335 = 4626503) B4626503
theorem B2056223 : Blo 2055435 2056223 := bstep (se 1 (by rfl) ⟨1542167, by rfl⟩ : syracuseStep 2056223 = 3084335) B3084335
theorem B3084341 : Blo 2055435 3084341 := bbase (se 5 (by rfl) ⟨144578, by rfl⟩ : syracuseStep 3084341 = 289157) (by norm_num)
theorem B2056227 : Blo 2055435 2056227 := bstep (se 1 (by rfl) ⟨1542170, by rfl⟩ : syracuseStep 2056227 = 3084341) B3084341
theorem B5204837 : Blo 2055435 5204837 := bbase (se 4 (by rfl) ⟨487953, by rfl⟩ : syracuseStep 5204837 = 975907) (by norm_num)
theorem B3469891 : Blo 2055435 3469891 := bstep (se 1 (by rfl) ⟨2602418, by rfl⟩ : syracuseStep 3469891 = 5204837) B5204837
theorem B4626521 : Blo 2055435 4626521 := bstep (se 2 (by rfl) ⟨1734945, by rfl⟩ : syracuseStep 4626521 = 3469891) B3469891
theorem B3084347 : Blo 2055435 3084347 := bstep (se 1 (by rfl) ⟨2313260, by rfl⟩ : syracuseStep 3084347 = 4626521) B4626521
theorem B2056231 : Blo 2055435 2056231 := bstep (se 1 (by rfl) ⟨1542173, by rfl⟩ : syracuseStep 2056231 = 3084347) B3084347
theorem B2313265 : Blo 2055435 2313265 := bbase (se 2 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 2313265 = 1734949) (by norm_num)
theorem B3084353 : Blo 2055435 3084353 := bstep (se 2 (by rfl) ⟨1156632, by rfl⟩ : syracuseStep 3084353 = 2313265) B2313265
theorem B2056235 : Blo 2055435 2056235 := bstep (se 1 (by rfl) ⟨1542176, by rfl⟩ : syracuseStep 2056235 = 3084353) B3084353
theorem B4168589 : Blo 2055435 4168589 := bbase (se 3 (by rfl) ⟨781610, by rfl⟩ : syracuseStep 4168589 = 1563221) (by norm_num)
theorem B11116237 : Blo 2055435 11116237 := bstep (se 3 (by rfl) ⟨2084294, by rfl⟩ : syracuseStep 11116237 = 4168589) B4168589
theorem B14821649 : Blo 2055435 14821649 := bstep (se 2 (by rfl) ⟨5558118, by rfl⟩ : syracuseStep 14821649 = 11116237) B11116237
theorem B9881099 : Blo 2055435 9881099 := bstep (se 1 (by rfl) ⟨7410824, by rfl⟩ : syracuseStep 9881099 = 14821649) B14821649
theorem B6587399 : Blo 2055435 6587399 := bstep (se 1 (by rfl) ⟨4940549, by rfl⟩ : syracuseStep 6587399 = 9881099) B9881099
theorem B4391599 : Blo 2055435 4391599 := bstep (se 1 (by rfl) ⟨3293699, by rfl⟩ : syracuseStep 4391599 = 6587399) B6587399
theorem B5855465 : Blo 2055435 5855465 := bstep (se 2 (by rfl) ⟨2195799, by rfl⟩ : syracuseStep 5855465 = 4391599) B4391599
theorem B3903643 : Blo 2055435 3903643 := bstep (se 1 (by rfl) ⟨2927732, by rfl⟩ : syracuseStep 3903643 = 5855465) B5855465
theorem B5204857 : Blo 2055435 5204857 := bstep (se 2 (by rfl) ⟨1951821, by rfl⟩ : syracuseStep 5204857 = 3903643) B3903643
theorem B6939809 : Blo 2055435 6939809 := bstep (se 2 (by rfl) ⟨2602428, by rfl⟩ : syracuseStep 6939809 = 5204857) B5204857
theorem B4626539 : Blo 2055435 4626539 := bstep (se 1 (by rfl) ⟨3469904, by rfl⟩ : syracuseStep 4626539 = 6939809) B6939809
theorem B3084359 : Blo 2055435 3084359 := bstep (se 1 (by rfl) ⟨2313269, by rfl⟩ : syracuseStep 3084359 = 4626539) B4626539
theorem B2056239 : Blo 2055435 2056239 := bstep (se 1 (by rfl) ⟨1542179, by rfl⟩ : syracuseStep 2056239 = 3084359) B3084359
theorem B3084365 : Blo 2055435 3084365 := bbase (se 3 (by rfl) ⟨578318, by rfl⟩ : syracuseStep 3084365 = 1156637) (by norm_num)
theorem B2056243 : Blo 2055435 2056243 := bstep (se 1 (by rfl) ⟨1542182, by rfl⟩ : syracuseStep 2056243 = 3084365) B3084365
theorem B4626557 : Blo 2055435 4626557 := bbase (se 3 (by rfl) ⟨867479, by rfl⟩ : syracuseStep 4626557 = 1734959) (by norm_num)
theorem B3084371 : Blo 2055435 3084371 := bstep (se 1 (by rfl) ⟨2313278, by rfl⟩ : syracuseStep 3084371 = 4626557) B4626557
theorem B2056247 : Blo 2055435 2056247 := bstep (se 1 (by rfl) ⟨1542185, by rfl⟩ : syracuseStep 2056247 = 3084371) B3084371
theorem B3469925 : Blo 2055435 3469925 := bbase (se 4 (by rfl) ⟨325305, by rfl⟩ : syracuseStep 3469925 = 650611) (by norm_num)
theorem B2313283 : Blo 2055435 2313283 := bstep (se 1 (by rfl) ⟨1734962, by rfl⟩ : syracuseStep 2313283 = 3469925) B3469925
theorem B3084377 : Blo 2055435 3084377 := bstep (se 2 (by rfl) ⟨1156641, by rfl⟩ : syracuseStep 3084377 = 2313283) B2313283
theorem B2056251 : Blo 2055435 2056251 := bstep (se 1 (by rfl) ⟨1542188, by rfl⟩ : syracuseStep 2056251 = 3084377) B3084377
theorem B3293725 : Blo 2055435 3293725 := bbase (se 3 (by rfl) ⟨617573, by rfl⟩ : syracuseStep 3293725 = 1235147) (by norm_num)
theorem B4391633 : Blo 2055435 4391633 := bstep (se 2 (by rfl) ⟨1646862, by rfl⟩ : syracuseStep 4391633 = 3293725) B3293725
theorem B2927755 : Blo 2055435 2927755 := bstep (se 1 (by rfl) ⟨2195816, by rfl⟩ : syracuseStep 2927755 = 4391633) B4391633
theorem B15614693 : Blo 2055435 15614693 := bstep (se 4 (by rfl) ⟨1463877, by rfl⟩ : syracuseStep 15614693 = 2927755) B2927755
theorem B10409795 : Blo 2055435 10409795 := bstep (se 1 (by rfl) ⟨7807346, by rfl⟩ : syracuseStep 10409795 = 15614693) B15614693
theorem B6939863 : Blo 2055435 6939863 := bstep (se 1 (by rfl) ⟨5204897, by rfl⟩ : syracuseStep 6939863 = 10409795) B10409795
theorem B4626575 : Blo 2055435 4626575 := bstep (se 1 (by rfl) ⟨3469931, by rfl⟩ : syracuseStep 4626575 = 6939863) B6939863
theorem B3084383 : Blo 2055435 3084383 := bstep (se 1 (by rfl) ⟨2313287, by rfl⟩ : syracuseStep 3084383 = 4626575) B4626575
theorem B2056255 : Blo 2055435 2056255 := bstep (se 1 (by rfl) ⟨1542191, by rfl⟩ : syracuseStep 2056255 = 3084383) B3084383
theorem B3084389 : Blo 2055435 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B2056259 : Blo 2055435 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B6587477 : Blo 2055435 6587477 := bbase (se 8 (by rfl) ⟨38598, by rfl⟩ : syracuseStep 6587477 = 77197) (by norm_num)
theorem B4391651 : Blo 2055435 4391651 := bstep (se 1 (by rfl) ⟨3293738, by rfl⟩ : syracuseStep 4391651 = 6587477) B6587477
theorem B2927767 : Blo 2055435 2927767 := bstep (se 1 (by rfl) ⟨2195825, by rfl⟩ : syracuseStep 2927767 = 4391651) B4391651
theorem B3903689 : Blo 2055435 3903689 := bstep (se 2 (by rfl) ⟨1463883, by rfl⟩ : syracuseStep 3903689 = 2927767) B2927767
theorem B2602459 : Blo 2055435 2602459 := bstep (se 1 (by rfl) ⟨1951844, by rfl⟩ : syracuseStep 2602459 = 3903689) B3903689
theorem B3469945 : Blo 2055435 3469945 := bstep (se 2 (by rfl) ⟨1301229, by rfl⟩ : syracuseStep 3469945 = 2602459) B2602459
theorem B4626593 : Blo 2055435 4626593 := bstep (se 2 (by rfl) ⟨1734972, by rfl⟩ : syracuseStep 4626593 = 3469945) B3469945
theorem B3084395 : Blo 2055435 3084395 := bstep (se 1 (by rfl) ⟨2313296, by rfl⟩ : syracuseStep 3084395 = 4626593) B4626593
theorem B2056263 : Blo 2055435 2056263 := bstep (se 1 (by rfl) ⟨1542197, by rfl⟩ : syracuseStep 2056263 = 3084395) B3084395
theorem B2313301 : Blo 2055435 2313301 := bbase (se 8 (by rfl) ⟨13554, by rfl⟩ : syracuseStep 2313301 = 27109) (by norm_num)
theorem B3084401 : Blo 2055435 3084401 := bstep (se 2 (by rfl) ⟨1156650, by rfl⟩ : syracuseStep 3084401 = 2313301) B2313301
theorem B2056267 : Blo 2055435 2056267 := bstep (se 1 (by rfl) ⟨1542200, by rfl⟩ : syracuseStep 2056267 = 3084401) B3084401
theorem B2602469 : Blo 2055435 2602469 := bbase (se 4 (by rfl) ⟨243981, by rfl⟩ : syracuseStep 2602469 = 487963) (by norm_num)
theorem B6939917 : Blo 2055435 6939917 := bstep (se 3 (by rfl) ⟨1301234, by rfl⟩ : syracuseStep 6939917 = 2602469) B2602469
theorem B4626611 : Blo 2055435 4626611 := bstep (se 1 (by rfl) ⟨3469958, by rfl⟩ : syracuseStep 4626611 = 6939917) B6939917
theorem B3084407 : Blo 2055435 3084407 := bstep (se 1 (by rfl) ⟨2313305, by rfl⟩ : syracuseStep 3084407 = 4626611) B4626611
theorem B2056271 : Blo 2055435 2056271 := bstep (se 1 (by rfl) ⟨1542203, by rfl⟩ : syracuseStep 2056271 = 3084407) B3084407
theorem B3084413 : Blo 2055435 3084413 := bbase (se 3 (by rfl) ⟨578327, by rfl⟩ : syracuseStep 3084413 = 1156655) (by norm_num)
theorem B2056275 : Blo 2055435 2056275 := bstep (se 1 (by rfl) ⟨1542206, by rfl⟩ : syracuseStep 2056275 = 3084413) B3084413
theorem B4626629 : Blo 2055435 4626629 := bbase (se 4 (by rfl) ⟨433746, by rfl⟩ : syracuseStep 4626629 = 867493) (by norm_num)
theorem B3084419 : Blo 2055435 3084419 := bstep (se 1 (by rfl) ⟨2313314, by rfl⟩ : syracuseStep 3084419 = 4626629) B4626629
theorem B2056279 : Blo 2055435 2056279 := bstep (se 1 (by rfl) ⟨1542209, by rfl⟩ : syracuseStep 2056279 = 3084419) B3084419
theorem B7034645 : Blo 2055435 7034645 := bbase (se 6 (by rfl) ⟨164874, by rfl⟩ : syracuseStep 7034645 = 329749) (by norm_num)
theorem B18759053 : Blo 2055435 18759053 := bstep (se 3 (by rfl) ⟨3517322, by rfl⟩ : syracuseStep 18759053 = 7034645) B7034645
theorem B50024141 : Blo 2055435 50024141 := bstep (se 3 (by rfl) ⟨9379526, by rfl⟩ : syracuseStep 50024141 = 18759053) B18759053
theorem B33349427 : Blo 2055435 33349427 := bstep (se 1 (by rfl) ⟨25012070, by rfl⟩ : syracuseStep 33349427 = 50024141) B50024141
theorem B22232951 : Blo 2055435 22232951 := bstep (se 1 (by rfl) ⟨16674713, by rfl⟩ : syracuseStep 22232951 = 33349427) B33349427
theorem B14821967 : Blo 2055435 14821967 := bstep (se 1 (by rfl) ⟨11116475, by rfl⟩ : syracuseStep 14821967 = 22232951) B22232951
theorem B9881311 : Blo 2055435 9881311 := bstep (se 1 (by rfl) ⟨7410983, by rfl⟩ : syracuseStep 9881311 = 14821967) B14821967
theorem B13175081 : Blo 2055435 13175081 := bstep (se 2 (by rfl) ⟨4940655, by rfl⟩ : syracuseStep 13175081 = 9881311) B9881311
theorem B8783387 : Blo 2055435 8783387 := bstep (se 1 (by rfl) ⟨6587540, by rfl⟩ : syracuseStep 8783387 = 13175081) B13175081
theorem B5855591 : Blo 2055435 5855591 := bstep (se 1 (by rfl) ⟨4391693, by rfl⟩ : syracuseStep 5855591 = 8783387) B8783387
theorem B3903727 : Blo 2055435 3903727 := bstep (se 1 (by rfl) ⟨2927795, by rfl⟩ : syracuseStep 3903727 = 5855591) B5855591
theorem B5204969 : Blo 2055435 5204969 := bstep (se 2 (by rfl) ⟨1951863, by rfl⟩ : syracuseStep 5204969 = 3903727) B3903727
theorem B3469979 : Blo 2055435 3469979 := bstep (se 1 (by rfl) ⟨2602484, by rfl⟩ : syracuseStep 3469979 = 5204969) B5204969
theorem B2313319 : Blo 2055435 2313319 := bstep (se 1 (by rfl) ⟨1734989, by rfl⟩ : syracuseStep 2313319 = 3469979) B3469979
theorem B3084425 : Blo 2055435 3084425 := bstep (se 2 (by rfl) ⟨1156659, by rfl⟩ : syracuseStep 3084425 = 2313319) B2313319
theorem B2056283 : Blo 2055435 2056283 := bstep (se 1 (by rfl) ⟨1542212, by rfl⟩ : syracuseStep 2056283 = 3084425) B3084425
theorem B10409957 : Blo 2055435 10409957 := bbase (se 4 (by rfl) ⟨975933, by rfl⟩ : syracuseStep 10409957 = 1951867) (by norm_num)
theorem B6939971 : Blo 2055435 6939971 := bstep (se 1 (by rfl) ⟨5204978, by rfl⟩ : syracuseStep 6939971 = 10409957) B10409957
theorem B4626647 : Blo 2055435 4626647 := bstep (se 1 (by rfl) ⟨3469985, by rfl⟩ : syracuseStep 4626647 = 6939971) B6939971
theorem B3084431 : Blo 2055435 3084431 := bstep (se 1 (by rfl) ⟨2313323, by rfl⟩ : syracuseStep 3084431 = 4626647) B4626647
theorem B2056287 : Blo 2055435 2056287 := bstep (se 1 (by rfl) ⟨1542215, by rfl⟩ : syracuseStep 2056287 = 3084431) B3084431
theorem B3084437 : Blo 2055435 3084437 := bbase (se 6 (by rfl) ⟨72291, by rfl⟩ : syracuseStep 3084437 = 144583) (by norm_num)
theorem B2056291 : Blo 2055435 2056291 := bstep (se 1 (by rfl) ⟨1542218, by rfl⟩ : syracuseStep 2056291 = 3084437) B3084437
theorem B3293789 : Blo 2055435 3293789 := bbase (se 3 (by rfl) ⟨617585, by rfl⟩ : syracuseStep 3293789 = 1235171) (by norm_num)
theorem B8783437 : Blo 2055435 8783437 := bstep (se 3 (by rfl) ⟨1646894, by rfl⟩ : syracuseStep 8783437 = 3293789) B3293789
theorem B11711249 : Blo 2055435 11711249 := bstep (se 2 (by rfl) ⟨4391718, by rfl⟩ : syracuseStep 11711249 = 8783437) B8783437
theorem B7807499 : Blo 2055435 7807499 := bstep (se 1 (by rfl) ⟨5855624, by rfl⟩ : syracuseStep 7807499 = 11711249) B11711249
theorem B5204999 : Blo 2055435 5204999 := bstep (se 1 (by rfl) ⟨3903749, by rfl⟩ : syracuseStep 5204999 = 7807499) B7807499
theorem B3469999 : Blo 2055435 3469999 := bstep (se 1 (by rfl) ⟨2602499, by rfl⟩ : syracuseStep 3469999 = 5204999) B5204999
theorem B4626665 : Blo 2055435 4626665 := bstep (se 2 (by rfl) ⟨1734999, by rfl⟩ : syracuseStep 4626665 = 3469999) B3469999
theorem B3084443 : Blo 2055435 3084443 := bstep (se 1 (by rfl) ⟨2313332, by rfl⟩ : syracuseStep 3084443 = 4626665) B4626665
theorem B2056295 : Blo 2055435 2056295 := bstep (se 1 (by rfl) ⟨1542221, by rfl⟩ : syracuseStep 2056295 = 3084443) B3084443
theorem B2313337 : Blo 2055435 2313337 := bbase (se 2 (by rfl) ⟨867501, by rfl⟩ : syracuseStep 2313337 = 1735003) (by norm_num)
theorem B3084449 : Blo 2055435 3084449 := bstep (se 2 (by rfl) ⟨1156668, by rfl⟩ : syracuseStep 3084449 = 2313337) B2313337
theorem B2056299 : Blo 2055435 2056299 := bstep (se 1 (by rfl) ⟨1542224, by rfl⟩ : syracuseStep 2056299 = 3084449) B3084449
theorem B25012309 : Blo 2055435 25012309 := bbase (se 8 (by rfl) ⟨146556, by rfl⟩ : syracuseStep 25012309 = 293113) (by norm_num)
theorem B33349745 : Blo 2055435 33349745 := bstep (se 2 (by rfl) ⟨12506154, by rfl⟩ : syracuseStep 33349745 = 25012309) B25012309
theorem B22233163 : Blo 2055435 22233163 := bstep (se 1 (by rfl) ⟨16674872, by rfl⟩ : syracuseStep 22233163 = 33349745) B33349745
theorem B29644217 : Blo 2055435 29644217 := bstep (se 2 (by rfl) ⟨11116581, by rfl⟩ : syracuseStep 29644217 = 22233163) B22233163
theorem B19762811 : Blo 2055435 19762811 := bstep (se 1 (by rfl) ⟨14822108, by rfl⟩ : syracuseStep 19762811 = 29644217) B29644217
theorem B13175207 : Blo 2055435 13175207 := bstep (se 1 (by rfl) ⟨9881405, by rfl⟩ : syracuseStep 13175207 = 19762811) B19762811
theorem B8783471 : Blo 2055435 8783471 := bstep (se 1 (by rfl) ⟨6587603, by rfl⟩ : syracuseStep 8783471 = 13175207) B13175207
theorem B5855647 : Blo 2055435 5855647 := bstep (se 1 (by rfl) ⟨4391735, by rfl⟩ : syracuseStep 5855647 = 8783471) B8783471
theorem B7807529 : Blo 2055435 7807529 := bstep (se 2 (by rfl) ⟨2927823, by rfl⟩ : syracuseStep 7807529 = 5855647) B5855647
theorem B5205019 : Blo 2055435 5205019 := bstep (se 1 (by rfl) ⟨3903764, by rfl⟩ : syracuseStep 5205019 = 7807529) B7807529
theorem B6940025 : Blo 2055435 6940025 := bstep (se 2 (by rfl) ⟨2602509, by rfl⟩ : syracuseStep 6940025 = 5205019) B5205019
theorem B4626683 : Blo 2055435 4626683 := bstep (se 1 (by rfl) ⟨3470012, by rfl⟩ : syracuseStep 4626683 = 6940025) B6940025
theorem B3084455 : Blo 2055435 3084455 := bstep (se 1 (by rfl) ⟨2313341, by rfl⟩ : syracuseStep 3084455 = 4626683) B4626683
theorem B2056303 : Blo 2055435 2056303 := bstep (se 1 (by rfl) ⟨1542227, by rfl⟩ : syracuseStep 2056303 = 3084455) B3084455
theorem B3084461 : Blo 2055435 3084461 := bbase (se 3 (by rfl) ⟨578336, by rfl⟩ : syracuseStep 3084461 = 1156673) (by norm_num)
theorem B2056307 : Blo 2055435 2056307 := bstep (se 1 (by rfl) ⟨1542230, by rfl⟩ : syracuseStep 2056307 = 3084461) B3084461
theorem B4626701 : Blo 2055435 4626701 := bbase (se 3 (by rfl) ⟨867506, by rfl⟩ : syracuseStep 4626701 = 1735013) (by norm_num)
theorem B3084467 : Blo 2055435 3084467 := bstep (se 1 (by rfl) ⟨2313350, by rfl⟩ : syracuseStep 3084467 = 4626701) B4626701
theorem B2056311 : Blo 2055435 2056311 := bstep (se 1 (by rfl) ⟨1542233, by rfl⟩ : syracuseStep 2056311 = 3084467) B3084467
theorem B2602525 : Blo 2055435 2602525 := bbase (se 3 (by rfl) ⟨487973, by rfl⟩ : syracuseStep 2602525 = 975947) (by norm_num)
theorem B3470033 : Blo 2055435 3470033 := bstep (se 2 (by rfl) ⟨1301262, by rfl⟩ : syracuseStep 3470033 = 2602525) B2602525
theorem B2313355 : Blo 2055435 2313355 := bstep (se 1 (by rfl) ⟨1735016, by rfl⟩ : syracuseStep 2313355 = 3470033) B3470033
theorem B3084473 : Blo 2055435 3084473 := bstep (se 2 (by rfl) ⟨1156677, by rfl⟩ : syracuseStep 3084473 = 2313355) B2313355
theorem B2056315 : Blo 2055435 2056315 := bstep (se 1 (by rfl) ⟨1542236, by rfl⟩ : syracuseStep 2056315 = 3084473) B3084473
theorem B4940741 : Blo 2055435 4940741 := bbase (se 4 (by rfl) ⟨463194, by rfl⟩ : syracuseStep 4940741 = 926389) (by norm_num)
theorem B3293827 : Blo 2055435 3293827 := bstep (se 1 (by rfl) ⟨2470370, by rfl⟩ : syracuseStep 3293827 = 4940741) B4940741
theorem B17567077 : Blo 2055435 17567077 := bstep (se 4 (by rfl) ⟨1646913, by rfl⟩ : syracuseStep 17567077 = 3293827) B3293827
theorem B23422769 : Blo 2055435 23422769 := bstep (se 2 (by rfl) ⟨8783538, by rfl⟩ : syracuseStep 23422769 = 17567077) B17567077
theorem B15615179 : Blo 2055435 15615179 := bstep (se 1 (by rfl) ⟨11711384, by rfl⟩ : syracuseStep 15615179 = 23422769) B23422769
theorem B10410119 : Blo 2055435 10410119 := bstep (se 1 (by rfl) ⟨7807589, by rfl⟩ : syracuseStep 10410119 = 15615179) B15615179
theorem B6940079 : Blo 2055435 6940079 := bstep (se 1 (by rfl) ⟨5205059, by rfl⟩ : syracuseStep 6940079 = 10410119) B10410119
theorem B4626719 : Blo 2055435 4626719 := bstep (se 1 (by rfl) ⟨3470039, by rfl⟩ : syracuseStep 4626719 = 6940079) B6940079
theorem B3084479 : Blo 2055435 3084479 := bstep (se 1 (by rfl) ⟨2313359, by rfl⟩ : syracuseStep 3084479 = 4626719) B4626719
theorem B2056319 : Blo 2055435 2056319 := bstep (se 1 (by rfl) ⟨1542239, by rfl⟩ : syracuseStep 2056319 = 3084479) B3084479
theorem B3084485 : Blo 2055435 3084485 := bbase (se 4 (by rfl) ⟨289170, by rfl⟩ : syracuseStep 3084485 = 578341) (by norm_num)
theorem B2056323 : Blo 2055435 2056323 := bstep (se 1 (by rfl) ⟨1542242, by rfl⟩ : syracuseStep 2056323 = 3084485) B3084485
theorem B3470053 : Blo 2055435 3470053 := bbase (se 4 (by rfl) ⟨325317, by rfl⟩ : syracuseStep 3470053 = 650635) (by norm_num)
theorem B4626737 : Blo 2055435 4626737 := bstep (se 2 (by rfl) ⟨1735026, by rfl⟩ : syracuseStep 4626737 = 3470053) B3470053
theorem B3084491 : Blo 2055435 3084491 := bstep (se 1 (by rfl) ⟨2313368, by rfl⟩ : syracuseStep 3084491 = 4626737) B4626737
theorem B2056327 : Blo 2055435 2056327 := bstep (se 1 (by rfl) ⟨1542245, by rfl⟩ : syracuseStep 2056327 = 3084491) B3084491
theorem B2313373 : Blo 2055435 2313373 := bbase (se 3 (by rfl) ⟨433757, by rfl⟩ : syracuseStep 2313373 = 867515) (by norm_num)
theorem B3084497 : Blo 2055435 3084497 := bstep (se 2 (by rfl) ⟨1156686, by rfl⟩ : syracuseStep 3084497 = 2313373) B2313373
theorem B2056331 : Blo 2055435 2056331 := bstep (se 1 (by rfl) ⟨1542248, by rfl⟩ : syracuseStep 2056331 = 3084497) B3084497
theorem B6940133 : Blo 2055435 6940133 := bbase (se 4 (by rfl) ⟨650637, by rfl⟩ : syracuseStep 6940133 = 1301275) (by norm_num)
theorem B4626755 : Blo 2055435 4626755 := bstep (se 1 (by rfl) ⟨3470066, by rfl⟩ : syracuseStep 4626755 = 6940133) B6940133
theorem B3084503 : Blo 2055435 3084503 := bstep (se 1 (by rfl) ⟨2313377, by rfl⟩ : syracuseStep 3084503 = 4626755) B4626755
theorem B2056335 : Blo 2055435 2056335 := bstep (se 1 (by rfl) ⟨1542251, by rfl⟩ : syracuseStep 2056335 = 3084503) B3084503
theorem B3084509 : Blo 2055435 3084509 := bbase (se 3 (by rfl) ⟨578345, by rfl⟩ : syracuseStep 3084509 = 1156691) (by norm_num)
theorem B2056339 : Blo 2055435 2056339 := bstep (se 1 (by rfl) ⟨1542254, by rfl⟩ : syracuseStep 2056339 = 3084509) B3084509
theorem B4626773 : Blo 2055435 4626773 := bbase (se 10 (by rfl) ⟨6777, by rfl⟩ : syracuseStep 4626773 = 13555) (by norm_num)
theorem B3084515 : Blo 2055435 3084515 := bstep (se 1 (by rfl) ⟨2313386, by rfl⟩ : syracuseStep 3084515 = 4626773) B4626773
theorem B2056343 : Blo 2055435 2056343 := bstep (se 1 (by rfl) ⟨1542257, by rfl⟩ : syracuseStep 2056343 = 3084515) B3084515
theorem B2470405 : Blo 2055435 2470405 := bbase (se 4 (by rfl) ⟨231600, by rfl⟩ : syracuseStep 2470405 = 463201) (by norm_num)
theorem B3293873 : Blo 2055435 3293873 := bstep (se 2 (by rfl) ⟨1235202, by rfl⟩ : syracuseStep 3293873 = 2470405) B2470405
theorem B2195915 : Blo 2055435 2195915 := bstep (se 1 (by rfl) ⟨1646936, by rfl⟩ : syracuseStep 2195915 = 3293873) B3293873
theorem B5855773 : Blo 2055435 5855773 := bstep (se 3 (by rfl) ⟨1097957, by rfl⟩ : syracuseStep 5855773 = 2195915) B2195915
theorem B7807697 : Blo 2055435 7807697 := bstep (se 2 (by rfl) ⟨2927886, by rfl⟩ : syracuseStep 7807697 = 5855773) B5855773
theorem B5205131 : Blo 2055435 5205131 := bstep (se 1 (by rfl) ⟨3903848, by rfl⟩ : syracuseStep 5205131 = 7807697) B7807697
theorem B3470087 : Blo 2055435 3470087 := bstep (se 1 (by rfl) ⟨2602565, by rfl⟩ : syracuseStep 3470087 = 5205131) B5205131
theorem B2313391 : Blo 2055435 2313391 := bstep (se 1 (by rfl) ⟨1735043, by rfl⟩ : syracuseStep 2313391 = 3470087) B3470087
theorem B3084521 : Blo 2055435 3084521 := bstep (se 2 (by rfl) ⟨1156695, by rfl⟩ : syracuseStep 3084521 = 2313391) B2313391
theorem B2056347 : Blo 2055435 2056347 := bstep (se 1 (by rfl) ⟨1542260, by rfl⟩ : syracuseStep 2056347 = 3084521) B3084521
theorem B14822453 : Blo 2055435 14822453 := bbase (se 5 (by rfl) ⟨694802, by rfl⟩ : syracuseStep 14822453 = 1389605) (by norm_num)
theorem B39526541 : Blo 2055435 39526541 := bstep (se 3 (by rfl) ⟨7411226, by rfl⟩ : syracuseStep 39526541 = 14822453) B14822453
theorem B26351027 : Blo 2055435 26351027 := bstep (se 1 (by rfl) ⟨19763270, by rfl⟩ : syracuseStep 26351027 = 39526541) B39526541
theorem B17567351 : Blo 2055435 17567351 := bstep (se 1 (by rfl) ⟨13175513, by rfl⟩ : syracuseStep 17567351 = 26351027) B26351027
theorem B11711567 : Blo 2055435 11711567 := bstep (se 1 (by rfl) ⟨8783675, by rfl⟩ : syracuseStep 11711567 = 17567351) B17567351
theorem B7807711 : Blo 2055435 7807711 := bstep (se 1 (by rfl) ⟨5855783, by rfl⟩ : syracuseStep 7807711 = 11711567) B11711567
theorem B10410281 : Blo 2055435 10410281 := bstep (se 2 (by rfl) ⟨3903855, by rfl⟩ : syracuseStep 10410281 = 7807711) B7807711
theorem B6940187 : Blo 2055435 6940187 := bstep (se 1 (by rfl) ⟨5205140, by rfl⟩ : syracuseStep 6940187 = 10410281) B10410281
theorem B4626791 : Blo 2055435 4626791 := bstep (se 1 (by rfl) ⟨3470093, by rfl⟩ : syracuseStep 4626791 = 6940187) B6940187
theorem B3084527 : Blo 2055435 3084527 := bstep (se 1 (by rfl) ⟨2313395, by rfl⟩ : syracuseStep 3084527 = 4626791) B4626791
theorem B2056351 : Blo 2055435 2056351 := bstep (se 1 (by rfl) ⟨1542263, by rfl⟩ : syracuseStep 2056351 = 3084527) B3084527
theorem B3084533 : Blo 2055435 3084533 := bbase (se 5 (by rfl) ⟨144587, by rfl⟩ : syracuseStep 3084533 = 289175) (by norm_num)
theorem B2056355 : Blo 2055435 2056355 := bstep (se 1 (by rfl) ⟨1542266, by rfl⟩ : syracuseStep 2056355 = 3084533) B3084533
theorem B44467541 : Blo 2055435 44467541 := bbase (se 12 (by rfl) ⟨16284, by rfl⟩ : syracuseStep 44467541 = 32569) (by norm_num)
theorem B29645027 : Blo 2055435 29645027 := bstep (se 1 (by rfl) ⟨22233770, by rfl⟩ : syracuseStep 29645027 = 44467541) B44467541
theorem B19763351 : Blo 2055435 19763351 := bstep (se 1 (by rfl) ⟨14822513, by rfl⟩ : syracuseStep 19763351 = 29645027) B29645027
theorem B13175567 : Blo 2055435 13175567 := bstep (se 1 (by rfl) ⟨9881675, by rfl⟩ : syracuseStep 13175567 = 19763351) B19763351
theorem B8783711 : Blo 2055435 8783711 := bstep (se 1 (by rfl) ⟨6587783, by rfl⟩ : syracuseStep 8783711 = 13175567) B13175567
theorem B5855807 : Blo 2055435 5855807 := bstep (se 1 (by rfl) ⟨4391855, by rfl⟩ : syracuseStep 5855807 = 8783711) B8783711
theorem B3903871 : Blo 2055435 3903871 := bstep (se 1 (by rfl) ⟨2927903, by rfl⟩ : syracuseStep 3903871 = 5855807) B5855807
theorem B5205161 : Blo 2055435 5205161 := bstep (se 2 (by rfl) ⟨1951935, by rfl⟩ : syracuseStep 5205161 = 3903871) B3903871
theorem B3470107 : Blo 2055435 3470107 := bstep (se 1 (by rfl) ⟨2602580, by rfl⟩ : syracuseStep 3470107 = 5205161) B5205161
theorem B4626809 : Blo 2055435 4626809 := bstep (se 2 (by rfl) ⟨1735053, by rfl⟩ : syracuseStep 4626809 = 3470107) B3470107
theorem B3084539 : Blo 2055435 3084539 := bstep (se 1 (by rfl) ⟨2313404, by rfl⟩ : syracuseStep 3084539 = 4626809) B4626809
theorem B2056359 : Blo 2055435 2056359 := bstep (se 1 (by rfl) ⟨1542269, by rfl⟩ : syracuseStep 2056359 = 3084539) B3084539
theorem B2313409 : Blo 2055435 2313409 := bbase (se 2 (by rfl) ⟨867528, by rfl⟩ : syracuseStep 2313409 = 1735057) (by norm_num)
theorem B3084545 : Blo 2055435 3084545 := bstep (se 2 (by rfl) ⟨1156704, by rfl⟩ : syracuseStep 3084545 = 2313409) B2313409
theorem B2056363 : Blo 2055435 2056363 := bstep (se 1 (by rfl) ⟨1542272, by rfl⟩ : syracuseStep 2056363 = 3084545) B3084545
theorem B5205181 : Blo 2055435 5205181 := bbase (se 3 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 5205181 = 1951943) (by norm_num)
theorem B6940241 : Blo 2055435 6940241 := bstep (se 2 (by rfl) ⟨2602590, by rfl⟩ : syracuseStep 6940241 = 5205181) B5205181
theorem B4626827 : Blo 2055435 4626827 := bstep (se 1 (by rfl) ⟨3470120, by rfl⟩ : syracuseStep 4626827 = 6940241) B6940241
theorem B3084551 : Blo 2055435 3084551 := bstep (se 1 (by rfl) ⟨2313413, by rfl⟩ : syracuseStep 3084551 = 4626827) B4626827
theorem B2056367 : Blo 2055435 2056367 := bstep (se 1 (by rfl) ⟨1542275, by rfl⟩ : syracuseStep 2056367 = 3084551) B3084551
theorem B3084557 : Blo 2055435 3084557 := bbase (se 3 (by rfl) ⟨578354, by rfl⟩ : syracuseStep 3084557 = 1156709) (by norm_num)
theorem B2056371 : Blo 2055435 2056371 := bstep (se 1 (by rfl) ⟨1542278, by rfl⟩ : syracuseStep 2056371 = 3084557) B3084557
theorem B4626845 : Blo 2055435 4626845 := bbase (se 3 (by rfl) ⟨867533, by rfl⟩ : syracuseStep 4626845 = 1735067) (by norm_num)
theorem B3084563 : Blo 2055435 3084563 := bstep (se 1 (by rfl) ⟨2313422, by rfl⟩ : syracuseStep 3084563 = 4626845) B4626845
theorem B2056375 : Blo 2055435 2056375 := bstep (se 1 (by rfl) ⟨1542281, by rfl⟩ : syracuseStep 2056375 = 3084563) B3084563
theorem B3470141 : Blo 2055435 3470141 := bbase (se 3 (by rfl) ⟨650651, by rfl⟩ : syracuseStep 3470141 = 1301303) (by norm_num)
theorem B2313427 : Blo 2055435 2313427 := bstep (se 1 (by rfl) ⟨1735070, by rfl⟩ : syracuseStep 2313427 = 3470141) B3470141
theorem B3084569 : Blo 2055435 3084569 := bstep (se 2 (by rfl) ⟨1156713, by rfl⟩ : syracuseStep 3084569 = 2313427) B2313427
theorem B2056379 : Blo 2055435 2056379 := bstep (se 1 (by rfl) ⟨1542284, by rfl⟩ : syracuseStep 2056379 = 3084569) B3084569
theorem B2195953 : Blo 2055435 2195953 := bbase (se 2 (by rfl) ⟨823482, by rfl⟩ : syracuseStep 2195953 = 1646965) (by norm_num)
theorem B11711749 : Blo 2055435 11711749 := bstep (se 4 (by rfl) ⟨1097976, by rfl⟩ : syracuseStep 11711749 = 2195953) B2195953
theorem B15615665 : Blo 2055435 15615665 := bstep (se 2 (by rfl) ⟨5855874, by rfl⟩ : syracuseStep 15615665 = 11711749) B11711749
theorem B10410443 : Blo 2055435 10410443 := bstep (se 1 (by rfl) ⟨7807832, by rfl⟩ : syracuseStep 10410443 = 15615665) B15615665
theorem B6940295 : Blo 2055435 6940295 := bstep (se 1 (by rfl) ⟨5205221, by rfl⟩ : syracuseStep 6940295 = 10410443) B10410443
theorem B4626863 : Blo 2055435 4626863 := bstep (se 1 (by rfl) ⟨3470147, by rfl⟩ : syracuseStep 4626863 = 6940295) B6940295
theorem B3084575 : Blo 2055435 3084575 := bstep (se 1 (by rfl) ⟨2313431, by rfl⟩ : syracuseStep 3084575 = 4626863) B4626863
theorem B2056383 : Blo 2055435 2056383 := bstep (se 1 (by rfl) ⟨1542287, by rfl⟩ : syracuseStep 2056383 = 3084575) B3084575
theorem B3084581 : Blo 2055435 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B2056387 : Blo 2055435 2056387 := bstep (se 1 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 2056387 = 3084581) B3084581
theorem B2602621 : Blo 2055435 2602621 := bbase (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) (by norm_num)
theorem B3470161 : Blo 2055435 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B4626881 : Blo 2055435 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B3084587 : Blo 2055435 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B2056391 : Blo 2055435 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B2313445 : Blo 2055435 2313445 := bbase (se 4 (by rfl) ⟨216885, by rfl⟩ : syracuseStep 2313445 = 433771) (by norm_num)
theorem B3084593 : Blo 2055435 3084593 := bstep (se 2 (by rfl) ⟨1156722, by rfl⟩ : syracuseStep 3084593 = 2313445) B2313445
theorem B2056395 : Blo 2055435 2056395 := bstep (se 1 (by rfl) ⟨1542296, by rfl⟩ : syracuseStep 2056395 = 3084593) B3084593
theorem B4391941 : Blo 2055435 4391941 := bbase (se 4 (by rfl) ⟨411744, by rfl⟩ : syracuseStep 4391941 = 823489) (by norm_num)
theorem B5855921 : Blo 2055435 5855921 := bstep (se 2 (by rfl) ⟨2195970, by rfl⟩ : syracuseStep 5855921 = 4391941) B4391941
theorem B3903947 : Blo 2055435 3903947 := bstep (se 1 (by rfl) ⟨2927960, by rfl⟩ : syracuseStep 3903947 = 5855921) B5855921
theorem B2602631 : Blo 2055435 2602631 := bstep (se 1 (by rfl) ⟨1951973, by rfl⟩ : syracuseStep 2602631 = 3903947) B3903947
theorem B6940349 : Blo 2055435 6940349 := bstep (se 3 (by rfl) ⟨1301315, by rfl⟩ : syracuseStep 6940349 = 2602631) B2602631
theorem B4626899 : Blo 2055435 4626899 := bstep (se 1 (by rfl) ⟨3470174, by rfl⟩ : syracuseStep 4626899 = 6940349) B6940349
theorem B3084599 : Blo 2055435 3084599 := bstep (se 1 (by rfl) ⟨2313449, by rfl⟩ : syracuseStep 3084599 = 4626899) B4626899
theorem B2056399 : Blo 2055435 2056399 := bstep (se 1 (by rfl) ⟨1542299, by rfl⟩ : syracuseStep 2056399 = 3084599) B3084599
theorem B3084605 : Blo 2055435 3084605 := bbase (se 3 (by rfl) ⟨578363, by rfl⟩ : syracuseStep 3084605 = 1156727) (by norm_num)
theorem B2056403 : Blo 2055435 2056403 := bstep (se 1 (by rfl) ⟨1542302, by rfl⟩ : syracuseStep 2056403 = 3084605) B3084605
theorem B4626917 : Blo 2055435 4626917 := bbase (se 4 (by rfl) ⟨433773, by rfl⟩ : syracuseStep 4626917 = 867547) (by norm_num)
theorem B3084611 : Blo 2055435 3084611 := bstep (se 1 (by rfl) ⟨2313458, by rfl⟩ : syracuseStep 3084611 = 4626917) B4626917
theorem B2056407 : Blo 2055435 2056407 := bstep (se 1 (by rfl) ⟨1542305, by rfl⟩ : syracuseStep 2056407 = 3084611) B3084611
theorem B5205293 : Blo 2055435 5205293 := bbase (se 3 (by rfl) ⟨975992, by rfl⟩ : syracuseStep 5205293 = 1951985) (by norm_num)
theorem B3470195 : Blo 2055435 3470195 := bstep (se 1 (by rfl) ⟨2602646, by rfl⟩ : syracuseStep 3470195 = 5205293) B5205293
theorem B2313463 : Blo 2055435 2313463 := bstep (se 1 (by rfl) ⟨1735097, by rfl⟩ : syracuseStep 2313463 = 3470195) B3470195
theorem B3084617 : Blo 2055435 3084617 := bstep (se 2 (by rfl) ⟨1156731, by rfl⟩ : syracuseStep 3084617 = 2313463) B2313463
theorem B2056411 : Blo 2055435 2056411 := bstep (se 1 (by rfl) ⟨1542308, by rfl⟩ : syracuseStep 2056411 = 3084617) B3084617
theorem B2084473 : Blo 2055435 2084473 := bbase (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) (by norm_num)
theorem B11117189 : Blo 2055435 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B7411459 : Blo 2055435 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B9881945 : Blo 2055435 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B6587963 : Blo 2055435 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B4391975 : Blo 2055435 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B2927983 : Blo 2055435 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B3903977 : Blo 2055435 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B10410605 : Blo 2055435 10410605 := bstep (se 3 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 10410605 = 3903977) B3903977
theorem B6940403 : Blo 2055435 6940403 := bstep (se 1 (by rfl) ⟨5205302, by rfl⟩ : syracuseStep 6940403 = 10410605) B10410605
theorem B4626935 : Blo 2055435 4626935 := bstep (se 1 (by rfl) ⟨3470201, by rfl⟩ : syracuseStep 4626935 = 6940403) B6940403
theorem B3084623 : Blo 2055435 3084623 := bstep (se 1 (by rfl) ⟨2313467, by rfl⟩ : syracuseStep 3084623 = 4626935) B4626935
theorem B2056415 : Blo 2055435 2056415 := bstep (se 1 (by rfl) ⟨1542311, by rfl⟩ : syracuseStep 2056415 = 3084623) B3084623
theorem B3084629 : Blo 2055435 3084629 := bbase (se 10 (by rfl) ⟨4518, by rfl⟩ : syracuseStep 3084629 = 9037) (by norm_num)
theorem B2056419 : Blo 2055435 2056419 := bstep (se 1 (by rfl) ⟨1542314, by rfl⟩ : syracuseStep 2056419 = 3084629) B3084629
theorem B5855989 : Blo 2055435 5855989 := bbase (se 5 (by rfl) ⟨274499, by rfl⟩ : syracuseStep 5855989 = 548999) (by norm_num)
theorem B7807985 : Blo 2055435 7807985 := bstep (se 2 (by rfl) ⟨2927994, by rfl⟩ : syracuseStep 7807985 = 5855989) B5855989
theorem B5205323 : Blo 2055435 5205323 := bstep (se 1 (by rfl) ⟨3903992, by rfl⟩ : syracuseStep 5205323 = 7807985) B7807985
theorem B3470215 : Blo 2055435 3470215 := bstep (se 1 (by rfl) ⟨2602661, by rfl⟩ : syracuseStep 3470215 = 5205323) B5205323
theorem B4626953 : Blo 2055435 4626953 := bstep (se 2 (by rfl) ⟨1735107, by rfl⟩ : syracuseStep 4626953 = 3470215) B3470215
theorem B3084635 : Blo 2055435 3084635 := bstep (se 1 (by rfl) ⟨2313476, by rfl⟩ : syracuseStep 3084635 = 4626953) B4626953
theorem B2056423 : Blo 2055435 2056423 := bstep (se 1 (by rfl) ⟨1542317, by rfl⟩ : syracuseStep 2056423 = 3084635) B3084635
theorem B2313481 : Blo 2055435 2313481 := bbase (se 2 (by rfl) ⟨867555, by rfl⟩ : syracuseStep 2313481 = 1735111) (by norm_num)
theorem B3084641 : Blo 2055435 3084641 := bstep (se 2 (by rfl) ⟨1156740, by rfl⟩ : syracuseStep 3084641 = 2313481) B2313481
theorem B2056427 : Blo 2055435 2056427 := bstep (se 1 (by rfl) ⟨1542320, by rfl⟩ : syracuseStep 2056427 = 3084641) B3084641
theorem B2470505 : Blo 2055435 2470505 := bbase (se 2 (by rfl) ⟨926439, by rfl⟩ : syracuseStep 2470505 = 1852879) (by norm_num)
theorem B26352053 : Blo 2055435 26352053 := bstep (se 5 (by rfl) ⟨1235252, by rfl⟩ : syracuseStep 26352053 = 2470505) B2470505
theorem B17568035 : Blo 2055435 17568035 := bstep (se 1 (by rfl) ⟨13176026, by rfl⟩ : syracuseStep 17568035 = 26352053) B26352053
theorem B11712023 : Blo 2055435 11712023 := bstep (se 1 (by rfl) ⟨8784017, by rfl⟩ : syracuseStep 11712023 = 17568035) B17568035
theorem B7808015 : Blo 2055435 7808015 := bstep (se 1 (by rfl) ⟨5856011, by rfl⟩ : syracuseStep 7808015 = 11712023) B11712023
theorem B5205343 : Blo 2055435 5205343 := bstep (se 1 (by rfl) ⟨3904007, by rfl⟩ : syracuseStep 5205343 = 7808015) B7808015
theorem B6940457 : Blo 2055435 6940457 := bstep (se 2 (by rfl) ⟨2602671, by rfl⟩ : syracuseStep 6940457 = 5205343) B5205343
theorem B4626971 : Blo 2055435 4626971 := bstep (se 1 (by rfl) ⟨3470228, by rfl⟩ : syracuseStep 4626971 = 6940457) B6940457
theorem B3084647 : Blo 2055435 3084647 := bstep (se 1 (by rfl) ⟨2313485, by rfl⟩ : syracuseStep 3084647 = 4626971) B4626971
theorem B2056431 : Blo 2055435 2056431 := bstep (se 1 (by rfl) ⟨1542323, by rfl⟩ : syracuseStep 2056431 = 3084647) B3084647
theorem B3084653 : Blo 2055435 3084653 := bbase (se 3 (by rfl) ⟨578372, by rfl⟩ : syracuseStep 3084653 = 1156745) (by norm_num)
theorem B2056435 : Blo 2055435 2056435 := bstep (se 1 (by rfl) ⟨1542326, by rfl⟩ : syracuseStep 2056435 = 3084653) B3084653
theorem B4626989 : Blo 2055435 4626989 := bbase (se 3 (by rfl) ⟨867560, by rfl⟩ : syracuseStep 4626989 = 1735121) (by norm_num)
theorem B3084659 : Blo 2055435 3084659 := bstep (se 1 (by rfl) ⟨2313494, by rfl⟩ : syracuseStep 3084659 = 4626989) B4626989
theorem B2056439 : Blo 2055435 2056439 := bstep (se 1 (by rfl) ⟨1542329, by rfl⟩ : syracuseStep 2056439 = 3084659) B3084659
theorem B3517597 : Blo 2055435 3517597 := bbase (se 3 (by rfl) ⟨659549, by rfl⟩ : syracuseStep 3517597 = 1319099) (by norm_num)
theorem B4690129 : Blo 2055435 4690129 := bstep (se 2 (by rfl) ⟨1758798, by rfl⟩ : syracuseStep 4690129 = 3517597) B3517597
theorem B6253505 : Blo 2055435 6253505 := bstep (se 2 (by rfl) ⟨2345064, by rfl⟩ : syracuseStep 6253505 = 4690129) B4690129
theorem B4169003 : Blo 2055435 4169003 := bstep (se 1 (by rfl) ⟨3126752, by rfl⟩ : syracuseStep 4169003 = 6253505) B6253505
theorem B11117341 : Blo 2055435 11117341 := bstep (se 3 (by rfl) ⟨2084501, by rfl⟩ : syracuseStep 11117341 = 4169003) B4169003
theorem B14823121 : Blo 2055435 14823121 := bstep (se 2 (by rfl) ⟨5558670, by rfl⟩ : syracuseStep 14823121 = 11117341) B11117341
theorem B19764161 : Blo 2055435 19764161 := bstep (se 2 (by rfl) ⟨7411560, by rfl⟩ : syracuseStep 19764161 = 14823121) B14823121
theorem B13176107 : Blo 2055435 13176107 := bstep (se 1 (by rfl) ⟨9882080, by rfl⟩ : syracuseStep 13176107 = 19764161) B19764161
theorem B8784071 : Blo 2055435 8784071 := bstep (se 1 (by rfl) ⟨6588053, by rfl⟩ : syracuseStep 8784071 = 13176107) B13176107
theorem B5856047 : Blo 2055435 5856047 := bstep (se 1 (by rfl) ⟨4392035, by rfl⟩ : syracuseStep 5856047 = 8784071) B8784071
theorem B3904031 : Blo 2055435 3904031 := bstep (se 1 (by rfl) ⟨2928023, by rfl⟩ : syracuseStep 3904031 = 5856047) B5856047
theorem B2602687 : Blo 2055435 2602687 := bstep (se 1 (by rfl) ⟨1952015, by rfl⟩ : syracuseStep 2602687 = 3904031) B3904031
theorem B3470249 : Blo 2055435 3470249 := bstep (se 2 (by rfl) ⟨1301343, by rfl⟩ : syracuseStep 3470249 = 2602687) B2602687
theorem B2313499 : Blo 2055435 2313499 := bstep (se 1 (by rfl) ⟨1735124, by rfl⟩ : syracuseStep 2313499 = 3470249) B3470249
theorem B3084665 : Blo 2055435 3084665 := bstep (se 2 (by rfl) ⟨1156749, by rfl⟩ : syracuseStep 3084665 = 2313499) B2313499
theorem B2056443 : Blo 2055435 2056443 := bstep (se 1 (by rfl) ⟨1542332, by rfl⟩ : syracuseStep 2056443 = 3084665) B3084665
theorem B35136341 : Blo 2055435 35136341 := bbase (se 9 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 35136341 = 205877) (by norm_num)
theorem B23424227 : Blo 2055435 23424227 := bstep (se 1 (by rfl) ⟨17568170, by rfl⟩ : syracuseStep 23424227 = 35136341) B35136341
theorem B15616151 : Blo 2055435 15616151 := bstep (se 1 (by rfl) ⟨11712113, by rfl⟩ : syracuseStep 15616151 = 23424227) B23424227
theorem B10410767 : Blo 2055435 10410767 := bstep (se 1 (by rfl) ⟨7808075, by rfl⟩ : syracuseStep 10410767 = 15616151) B15616151
theorem B6940511 : Blo 2055435 6940511 := bstep (se 1 (by rfl) ⟨5205383, by rfl⟩ : syracuseStep 6940511 = 10410767) B10410767
theorem B4627007 : Blo 2055435 4627007 := bstep (se 1 (by rfl) ⟨3470255, by rfl⟩ : syracuseStep 4627007 = 6940511) B6940511
theorem B3084671 : Blo 2055435 3084671 := bstep (se 1 (by rfl) ⟨2313503, by rfl⟩ : syracuseStep 3084671 = 4627007) B4627007
theorem B2056447 : Blo 2055435 2056447 := bstep (se 1 (by rfl) ⟨1542335, by rfl⟩ : syracuseStep 2056447 = 3084671) B3084671
theorem B3084677 : Blo 2055435 3084677 := bbase (se 4 (by rfl) ⟨289188, by rfl⟩ : syracuseStep 3084677 = 578377) (by norm_num)
theorem B2056451 : Blo 2055435 2056451 := bstep (se 1 (by rfl) ⟨1542338, by rfl⟩ : syracuseStep 2056451 = 3084677) B3084677
theorem B3470269 : Blo 2055435 3470269 := bbase (se 3 (by rfl) ⟨650675, by rfl⟩ : syracuseStep 3470269 = 1301351) (by norm_num)
theorem B4627025 : Blo 2055435 4627025 := bstep (se 2 (by rfl) ⟨1735134, by rfl⟩ : syracuseStep 4627025 = 3470269) B3470269
theorem B3084683 : Blo 2055435 3084683 := bstep (se 1 (by rfl) ⟨2313512, by rfl⟩ : syracuseStep 3084683 = 4627025) B4627025
theorem B2056455 : Blo 2055435 2056455 := bstep (se 1 (by rfl) ⟨1542341, by rfl⟩ : syracuseStep 2056455 = 3084683) B3084683
theorem B2313517 : Blo 2055435 2313517 := bbase (se 3 (by rfl) ⟨433784, by rfl⟩ : syracuseStep 2313517 = 867569) (by norm_num)
theorem B3084689 : Blo 2055435 3084689 := bstep (se 2 (by rfl) ⟨1156758, by rfl⟩ : syracuseStep 3084689 = 2313517) B2313517
theorem B2056459 : Blo 2055435 2056459 := bstep (se 1 (by rfl) ⟨1542344, by rfl⟩ : syracuseStep 2056459 = 3084689) B3084689
theorem B6940565 : Blo 2055435 6940565 := bbase (se 6 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 6940565 = 325339) (by norm_num)
theorem B4627043 : Blo 2055435 4627043 := bstep (se 1 (by rfl) ⟨3470282, by rfl⟩ : syracuseStep 4627043 = 6940565) B6940565
theorem B3084695 : Blo 2055435 3084695 := bstep (se 1 (by rfl) ⟨2313521, by rfl⟩ : syracuseStep 3084695 = 4627043) B4627043
theorem B2056463 : Blo 2055435 2056463 := bstep (se 1 (by rfl) ⟨1542347, by rfl⟩ : syracuseStep 2056463 = 3084695) B3084695
theorem B3084701 : Blo 2055435 3084701 := bbase (se 3 (by rfl) ⟨578381, by rfl⟩ : syracuseStep 3084701 = 1156763) (by norm_num)
theorem B2056467 : Blo 2055435 2056467 := bstep (se 1 (by rfl) ⟨1542350, by rfl⟩ : syracuseStep 2056467 = 3084701) B3084701
theorem B4627061 : Blo 2055435 4627061 := bbase (se 5 (by rfl) ⟨216893, by rfl⟩ : syracuseStep 4627061 = 433787) (by norm_num)
theorem B3084707 : Blo 2055435 3084707 := bstep (se 1 (by rfl) ⟨2313530, by rfl⟩ : syracuseStep 3084707 = 4627061) B4627061
theorem B2056471 : Blo 2055435 2056471 := bstep (se 1 (by rfl) ⟨1542353, by rfl⟩ : syracuseStep 2056471 = 3084707) B3084707
theorem B5276477 : Blo 2055435 5276477 := bbase (se 3 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 5276477 = 1978679) (by norm_num)
theorem B3517651 : Blo 2055435 3517651 := bstep (se 1 (by rfl) ⟨2638238, by rfl⟩ : syracuseStep 3517651 = 5276477) B5276477
theorem B18760805 : Blo 2055435 18760805 := bstep (se 4 (by rfl) ⟨1758825, by rfl⟩ : syracuseStep 18760805 = 3517651) B3517651
theorem B12507203 : Blo 2055435 12507203 := bstep (se 1 (by rfl) ⟨9380402, by rfl⟩ : syracuseStep 12507203 = 18760805) B18760805
theorem B8338135 : Blo 2055435 8338135 := bstep (se 1 (by rfl) ⟨6253601, by rfl⟩ : syracuseStep 8338135 = 12507203) B12507203
theorem B11117513 : Blo 2055435 11117513 := bstep (se 2 (by rfl) ⟨4169067, by rfl⟩ : syracuseStep 11117513 = 8338135) B8338135
theorem B7411675 : Blo 2055435 7411675 := bstep (se 1 (by rfl) ⟨5558756, by rfl⟩ : syracuseStep 7411675 = 11117513) B11117513
theorem B9882233 : Blo 2055435 9882233 := bstep (se 2 (by rfl) ⟨3705837, by rfl⟩ : syracuseStep 9882233 = 7411675) B7411675
theorem B6588155 : Blo 2055435 6588155 := bstep (se 1 (by rfl) ⟨4941116, by rfl⟩ : syracuseStep 6588155 = 9882233) B9882233
theorem B17568413 : Blo 2055435 17568413 := bstep (se 3 (by rfl) ⟨3294077, by rfl⟩ : syracuseStep 17568413 = 6588155) B6588155
theorem B11712275 : Blo 2055435 11712275 := bstep (se 1 (by rfl) ⟨8784206, by rfl⟩ : syracuseStep 11712275 = 17568413) B17568413
theorem B7808183 : Blo 2055435 7808183 := bstep (se 1 (by rfl) ⟨5856137, by rfl⟩ : syracuseStep 7808183 = 11712275) B11712275
theorem B5205455 : Blo 2055435 5205455 := bstep (se 1 (by rfl) ⟨3904091, by rfl⟩ : syracuseStep 5205455 = 7808183) B7808183
theorem B3470303 : Blo 2055435 3470303 := bstep (se 1 (by rfl) ⟨2602727, by rfl⟩ : syracuseStep 3470303 = 5205455) B5205455
theorem B2313535 : Blo 2055435 2313535 := bstep (se 1 (by rfl) ⟨1735151, by rfl⟩ : syracuseStep 2313535 = 3470303) B3470303
theorem B3084713 : Blo 2055435 3084713 := bstep (se 2 (by rfl) ⟨1156767, by rfl⟩ : syracuseStep 3084713 = 2313535) B2313535
theorem B2056475 : Blo 2055435 2056475 := bstep (se 1 (by rfl) ⟨1542356, by rfl⟩ : syracuseStep 2056475 = 3084713) B3084713
theorem B7808197 : Blo 2055435 7808197 := bbase (se 4 (by rfl) ⟨732018, by rfl⟩ : syracuseStep 7808197 = 1464037) (by norm_num)
theorem B10410929 : Blo 2055435 10410929 := bstep (se 2 (by rfl) ⟨3904098, by rfl⟩ : syracuseStep 10410929 = 7808197) B7808197
theorem B6940619 : Blo 2055435 6940619 := bstep (se 1 (by rfl) ⟨5205464, by rfl⟩ : syracuseStep 6940619 = 10410929) B10410929
theorem B4627079 : Blo 2055435 4627079 := bstep (se 1 (by rfl) ⟨3470309, by rfl⟩ : syracuseStep 4627079 = 6940619) B6940619
theorem B3084719 : Blo 2055435 3084719 := bstep (se 1 (by rfl) ⟨2313539, by rfl⟩ : syracuseStep 3084719 = 4627079) B4627079
theorem B2056479 : Blo 2055435 2056479 := bstep (se 1 (by rfl) ⟨1542359, by rfl⟩ : syracuseStep 2056479 = 3084719) B3084719
theorem B3084725 : Blo 2055435 3084725 := bbase (se 5 (by rfl) ⟨144596, by rfl⟩ : syracuseStep 3084725 = 289193) (by norm_num)
theorem B2056483 : Blo 2055435 2056483 := bstep (se 1 (by rfl) ⟨1542362, by rfl⟩ : syracuseStep 2056483 = 3084725) B3084725
theorem B5205485 : Blo 2055435 5205485 := bbase (se 3 (by rfl) ⟨976028, by rfl⟩ : syracuseStep 5205485 = 1952057) (by norm_num)
theorem B3470323 : Blo 2055435 3470323 := bstep (se 1 (by rfl) ⟨2602742, by rfl⟩ : syracuseStep 3470323 = 5205485) B5205485
theorem B4627097 : Blo 2055435 4627097 := bstep (se 2 (by rfl) ⟨1735161, by rfl⟩ : syracuseStep 4627097 = 3470323) B3470323
theorem B3084731 : Blo 2055435 3084731 := bstep (se 1 (by rfl) ⟨2313548, by rfl⟩ : syracuseStep 3084731 = 4627097) B4627097
theorem B2056487 : Blo 2055435 2056487 := bstep (se 1 (by rfl) ⟨1542365, by rfl⟩ : syracuseStep 2056487 = 3084731) B3084731
theorem B2313553 : Blo 2055435 2313553 := bbase (se 2 (by rfl) ⟨867582, by rfl⟩ : syracuseStep 2313553 = 1735165) (by norm_num)
theorem B3084737 : Blo 2055435 3084737 := bstep (se 2 (by rfl) ⟨1156776, by rfl⟩ : syracuseStep 3084737 = 2313553) B2313553
theorem B2056491 : Blo 2055435 2056491 := bstep (se 1 (by rfl) ⟨1542368, by rfl⟩ : syracuseStep 2056491 = 3084737) B3084737
theorem B2196073 : Blo 2055435 2196073 := bbase (se 2 (by rfl) ⟨823527, by rfl⟩ : syracuseStep 2196073 = 1647055) (by norm_num)
theorem B2928097 : Blo 2055435 2928097 := bstep (se 2 (by rfl) ⟨1098036, by rfl⟩ : syracuseStep 2928097 = 2196073) B2196073
theorem B3904129 : Blo 2055435 3904129 := bstep (se 2 (by rfl) ⟨1464048, by rfl⟩ : syracuseStep 3904129 = 2928097) B2928097
theorem B5205505 : Blo 2055435 5205505 := bstep (se 2 (by rfl) ⟨1952064, by rfl⟩ : syracuseStep 5205505 = 3904129) B3904129
theorem B6940673 : Blo 2055435 6940673 := bstep (se 2 (by rfl) ⟨2602752, by rfl⟩ : syracuseStep 6940673 = 5205505) B5205505
theorem B4627115 : Blo 2055435 4627115 := bstep (se 1 (by rfl) ⟨3470336, by rfl⟩ : syracuseStep 4627115 = 6940673) B6940673
theorem B3084743 : Blo 2055435 3084743 := bstep (se 1 (by rfl) ⟨2313557, by rfl⟩ : syracuseStep 3084743 = 4627115) B4627115
theorem B2056495 : Blo 2055435 2056495 := bstep (se 1 (by rfl) ⟨1542371, by rfl⟩ : syracuseStep 2056495 = 3084743) B3084743
theorem B3084749 : Blo 2055435 3084749 := bbase (se 3 (by rfl) ⟨578390, by rfl⟩ : syracuseStep 3084749 = 1156781) (by norm_num)
theorem B2056499 : Blo 2055435 2056499 := bstep (se 1 (by rfl) ⟨1542374, by rfl⟩ : syracuseStep 2056499 = 3084749) B3084749
theorem B4627133 : Blo 2055435 4627133 := bbase (se 3 (by rfl) ⟨867587, by rfl⟩ : syracuseStep 4627133 = 1735175) (by norm_num)
theorem B3084755 : Blo 2055435 3084755 := bstep (se 1 (by rfl) ⟨2313566, by rfl⟩ : syracuseStep 3084755 = 4627133) B4627133
theorem B2056503 : Blo 2055435 2056503 := bstep (se 1 (by rfl) ⟨1542377, by rfl⟩ : syracuseStep 2056503 = 3084755) B3084755
theorem B3470357 : Blo 2055435 3470357 := bbase (se 6 (by rfl) ⟨81336, by rfl⟩ : syracuseStep 3470357 = 162673) (by norm_num)
theorem B2313571 : Blo 2055435 2313571 := bstep (se 1 (by rfl) ⟨1735178, by rfl⟩ : syracuseStep 2313571 = 3470357) B3470357
theorem B3084761 : Blo 2055435 3084761 := bstep (se 2 (by rfl) ⟨1156785, by rfl⟩ : syracuseStep 3084761 = 2313571) B2313571
theorem B2056507 : Blo 2055435 2056507 := bstep (se 1 (by rfl) ⟨1542380, by rfl⟩ : syracuseStep 2056507 = 3084761) B3084761
theorem B9508549 : Blo 2055435 9508549 := bbase (se 4 (by rfl) ⟨891426, by rfl⟩ : syracuseStep 9508549 = 1782853) (by norm_num)
theorem B12678065 : Blo 2055435 12678065 := bstep (se 2 (by rfl) ⟨4754274, by rfl⟩ : syracuseStep 12678065 = 9508549) B9508549
theorem B8452043 : Blo 2055435 8452043 := bstep (se 1 (by rfl) ⟨6339032, by rfl⟩ : syracuseStep 8452043 = 12678065) B12678065
theorem B5634695 : Blo 2055435 5634695 := bstep (se 1 (by rfl) ⟨4226021, by rfl⟩ : syracuseStep 5634695 = 8452043) B8452043
theorem B3756463 : Blo 2055435 3756463 := bstep (se 1 (by rfl) ⟨2817347, by rfl⟩ : syracuseStep 3756463 = 5634695) B5634695
theorem B20034469 : Blo 2055435 20034469 := bstep (se 4 (by rfl) ⟨1878231, by rfl⟩ : syracuseStep 20034469 = 3756463) B3756463
theorem B106850501 : Blo 2055435 106850501 := bstep (se 4 (by rfl) ⟨10017234, by rfl⟩ : syracuseStep 106850501 = 20034469) B20034469
theorem B71233667 : Blo 2055435 71233667 := bstep (se 1 (by rfl) ⟨53425250, by rfl⟩ : syracuseStep 71233667 = 106850501) B106850501
theorem B47489111 : Blo 2055435 47489111 := bstep (se 1 (by rfl) ⟨35616833, by rfl⟩ : syracuseStep 47489111 = 71233667) B71233667
theorem B31659407 : Blo 2055435 31659407 := bstep (se 1 (by rfl) ⟨23744555, by rfl⟩ : syracuseStep 31659407 = 47489111) B47489111
theorem B21106271 : Blo 2055435 21106271 := bstep (se 1 (by rfl) ⟨15829703, by rfl⟩ : syracuseStep 21106271 = 31659407) B31659407
theorem B14070847 : Blo 2055435 14070847 := bstep (se 1 (by rfl) ⟨10553135, by rfl⟩ : syracuseStep 14070847 = 21106271) B21106271
theorem B18761129 : Blo 2055435 18761129 := bstep (se 2 (by rfl) ⟨7035423, by rfl⟩ : syracuseStep 18761129 = 14070847) B14070847
theorem B12507419 : Blo 2055435 12507419 := bstep (se 1 (by rfl) ⟨9380564, by rfl⟩ : syracuseStep 12507419 = 18761129) B18761129
theorem B33353117 : Blo 2055435 33353117 := bstep (se 3 (by rfl) ⟨6253709, by rfl⟩ : syracuseStep 33353117 = 12507419) B12507419
theorem B22235411 : Blo 2055435 22235411 := bstep (se 1 (by rfl) ⟨16676558, by rfl⟩ : syracuseStep 22235411 = 33353117) B33353117
theorem B14823607 : Blo 2055435 14823607 := bstep (se 1 (by rfl) ⟨11117705, by rfl⟩ : syracuseStep 14823607 = 22235411) B22235411
theorem B19764809 : Blo 2055435 19764809 := bstep (se 2 (by rfl) ⟨7411803, by rfl⟩ : syracuseStep 19764809 = 14823607) B14823607
theorem B13176539 : Blo 2055435 13176539 := bstep (se 1 (by rfl) ⟨9882404, by rfl⟩ : syracuseStep 13176539 = 19764809) B19764809
theorem B8784359 : Blo 2055435 8784359 := bstep (se 1 (by rfl) ⟨6588269, by rfl⟩ : syracuseStep 8784359 = 13176539) B13176539
theorem B5856239 : Blo 2055435 5856239 := bstep (se 1 (by rfl) ⟨4392179, by rfl⟩ : syracuseStep 5856239 = 8784359) B8784359
theorem B15616637 : Blo 2055435 15616637 := bstep (se 3 (by rfl) ⟨2928119, by rfl⟩ : syracuseStep 15616637 = 5856239) B5856239
theorem B10411091 : Blo 2055435 10411091 := bstep (se 1 (by rfl) ⟨7808318, by rfl⟩ : syracuseStep 10411091 = 15616637) B15616637
theorem B6940727 : Blo 2055435 6940727 := bstep (se 1 (by rfl) ⟨5205545, by rfl⟩ : syracuseStep 6940727 = 10411091) B10411091
theorem B4627151 : Blo 2055435 4627151 := bstep (se 1 (by rfl) ⟨3470363, by rfl⟩ : syracuseStep 4627151 = 6940727) B6940727
theorem B3084767 : Blo 2055435 3084767 := bstep (se 1 (by rfl) ⟨2313575, by rfl⟩ : syracuseStep 3084767 = 4627151) B4627151
theorem B2056511 : Blo 2055435 2056511 := bstep (se 1 (by rfl) ⟨1542383, by rfl⟩ : syracuseStep 2056511 = 3084767) B3084767
theorem B3084773 : Blo 2055435 3084773 := bbase (se 4 (by rfl) ⟨289197, by rfl⟩ : syracuseStep 3084773 = 578395) (by norm_num)
theorem B2056515 : Blo 2055435 2056515 := bstep (se 1 (by rfl) ⟨1542386, by rfl⟩ : syracuseStep 2056515 = 3084773) B3084773
theorem B3705917 : Blo 2055435 3705917 := bbase (se 3 (by rfl) ⟨694859, by rfl⟩ : syracuseStep 3705917 = 1389719) (by norm_num)
theorem B9882445 : Blo 2055435 9882445 := bstep (se 3 (by rfl) ⟨1852958, by rfl⟩ : syracuseStep 9882445 = 3705917) B3705917
theorem B13176593 : Blo 2055435 13176593 := bstep (se 2 (by rfl) ⟨4941222, by rfl⟩ : syracuseStep 13176593 = 9882445) B9882445
theorem B8784395 : Blo 2055435 8784395 := bstep (se 1 (by rfl) ⟨6588296, by rfl⟩ : syracuseStep 8784395 = 13176593) B13176593
theorem B5856263 : Blo 2055435 5856263 := bstep (se 1 (by rfl) ⟨4392197, by rfl⟩ : syracuseStep 5856263 = 8784395) B8784395
theorem B3904175 : Blo 2055435 3904175 := bstep (se 1 (by rfl) ⟨2928131, by rfl⟩ : syracuseStep 3904175 = 5856263) B5856263
theorem B2602783 : Blo 2055435 2602783 := bstep (se 1 (by rfl) ⟨1952087, by rfl⟩ : syracuseStep 2602783 = 3904175) B3904175
theorem B3470377 : Blo 2055435 3470377 := bstep (se 2 (by rfl) ⟨1301391, by rfl⟩ : syracuseStep 3470377 = 2602783) B2602783
theorem B4627169 : Blo 2055435 4627169 := bstep (se 2 (by rfl) ⟨1735188, by rfl⟩ : syracuseStep 4627169 = 3470377) B3470377
theorem B3084779 : Blo 2055435 3084779 := bstep (se 1 (by rfl) ⟨2313584, by rfl⟩ : syracuseStep 3084779 = 4627169) B4627169
theorem B2056519 : Blo 2055435 2056519 := bstep (se 1 (by rfl) ⟨1542389, by rfl⟩ : syracuseStep 2056519 = 3084779) B3084779
theorem B2313589 : Blo 2055435 2313589 := bbase (se 5 (by rfl) ⟨108449, by rfl⟩ : syracuseStep 2313589 = 216899) (by norm_num)
theorem B3084785 : Blo 2055435 3084785 := bstep (se 2 (by rfl) ⟨1156794, by rfl⟩ : syracuseStep 3084785 = 2313589) B2313589
theorem B2056523 : Blo 2055435 2056523 := bstep (se 1 (by rfl) ⟨1542392, by rfl⟩ : syracuseStep 2056523 = 3084785) B3084785
theorem B2602793 : Blo 2055435 2602793 := bbase (se 2 (by rfl) ⟨976047, by rfl⟩ : syracuseStep 2602793 = 1952095) (by norm_num)
theorem B6940781 : Blo 2055435 6940781 := bstep (se 3 (by rfl) ⟨1301396, by rfl⟩ : syracuseStep 6940781 = 2602793) B2602793
theorem B4627187 : Blo 2055435 4627187 := bstep (se 1 (by rfl) ⟨3470390, by rfl⟩ : syracuseStep 4627187 = 6940781) B6940781
theorem B3084791 : Blo 2055435 3084791 := bstep (se 1 (by rfl) ⟨2313593, by rfl⟩ : syracuseStep 3084791 = 4627187) B4627187
theorem B2056527 : Blo 2055435 2056527 := bstep (se 1 (by rfl) ⟨1542395, by rfl⟩ : syracuseStep 2056527 = 3084791) B3084791
theorem B3084797 : Blo 2055435 3084797 := bbase (se 3 (by rfl) ⟨578399, by rfl⟩ : syracuseStep 3084797 = 1156799) (by norm_num)
theorem B2056531 : Blo 2055435 2056531 := bstep (se 1 (by rfl) ⟨1542398, by rfl⟩ : syracuseStep 2056531 = 3084797) B3084797
theorem B4627205 : Blo 2055435 4627205 := bbase (se 4 (by rfl) ⟨433800, by rfl⟩ : syracuseStep 4627205 = 867601) (by norm_num)
theorem B3084803 : Blo 2055435 3084803 := bstep (se 1 (by rfl) ⟨2313602, by rfl⟩ : syracuseStep 3084803 = 4627205) B4627205
theorem B2056535 : Blo 2055435 2056535 := bstep (se 1 (by rfl) ⟨1542401, by rfl⟩ : syracuseStep 2056535 = 3084803) B3084803
theorem B3904213 : Blo 2055435 3904213 := bbase (se 7 (by rfl) ⟨45752, by rfl⟩ : syracuseStep 3904213 = 91505) (by norm_num)
theorem B5205617 : Blo 2055435 5205617 := bstep (se 2 (by rfl) ⟨1952106, by rfl⟩ : syracuseStep 5205617 = 3904213) B3904213
theorem B3470411 : Blo 2055435 3470411 := bstep (se 1 (by rfl) ⟨2602808, by rfl⟩ : syracuseStep 3470411 = 5205617) B5205617
theorem B2313607 : Blo 2055435 2313607 := bstep (se 1 (by rfl) ⟨1735205, by rfl⟩ : syracuseStep 2313607 = 3470411) B3470411
theorem B3084809 : Blo 2055435 3084809 := bstep (se 2 (by rfl) ⟨1156803, by rfl⟩ : syracuseStep 3084809 = 2313607) B2313607
theorem B2056539 : Blo 2055435 2056539 := bstep (se 1 (by rfl) ⟨1542404, by rfl⟩ : syracuseStep 2056539 = 3084809) B3084809
theorem B10411253 : Blo 2055435 10411253 := bbase (se 5 (by rfl) ⟨488027, by rfl⟩ : syracuseStep 10411253 = 976055) (by norm_num)
theorem B6940835 : Blo 2055435 6940835 := bstep (se 1 (by rfl) ⟨5205626, by rfl⟩ : syracuseStep 6940835 = 10411253) B10411253
theorem B4627223 : Blo 2055435 4627223 := bstep (se 1 (by rfl) ⟨3470417, by rfl⟩ : syracuseStep 4627223 = 6940835) B6940835
theorem B3084815 : Blo 2055435 3084815 := bstep (se 1 (by rfl) ⟨2313611, by rfl⟩ : syracuseStep 3084815 = 4627223) B4627223
theorem B2056543 : Blo 2055435 2056543 := bstep (se 1 (by rfl) ⟨1542407, by rfl⟩ : syracuseStep 2056543 = 3084815) B3084815
theorem B3084821 : Blo 2055435 3084821 := bbase (se 6 (by rfl) ⟨72300, by rfl⟩ : syracuseStep 3084821 = 144601) (by norm_num)
theorem B2056547 : Blo 2055435 2056547 := bstep (se 1 (by rfl) ⟨1542410, by rfl⟩ : syracuseStep 2056547 = 3084821) B3084821
theorem B3126917 : Blo 2055435 3126917 := bbase (se 4 (by rfl) ⟨293148, by rfl⟩ : syracuseStep 3126917 = 586297) (by norm_num)
theorem B2084611 : Blo 2055435 2084611 := bstep (se 1 (by rfl) ⟨1563458, by rfl⟩ : syracuseStep 2084611 = 3126917) B3126917
theorem B2779481 : Blo 2055435 2779481 := bstep (se 2 (by rfl) ⟨1042305, by rfl⟩ : syracuseStep 2779481 = 2084611) B2084611
theorem B7411949 : Blo 2055435 7411949 := bstep (se 3 (by rfl) ⟨1389740, by rfl⟩ : syracuseStep 7411949 = 2779481) B2779481
theorem B4941299 : Blo 2055435 4941299 := bstep (se 1 (by rfl) ⟨3705974, by rfl⟩ : syracuseStep 4941299 = 7411949) B7411949
theorem B3294199 : Blo 2055435 3294199 := bstep (se 1 (by rfl) ⟨2470649, by rfl⟩ : syracuseStep 3294199 = 4941299) B4941299
theorem B17569061 : Blo 2055435 17569061 := bstep (se 4 (by rfl) ⟨1647099, by rfl⟩ : syracuseStep 17569061 = 3294199) B3294199
theorem B11712707 : Blo 2055435 11712707 := bstep (se 1 (by rfl) ⟨8784530, by rfl⟩ : syracuseStep 11712707 = 17569061) B17569061
theorem B7808471 : Blo 2055435 7808471 := bstep (se 1 (by rfl) ⟨5856353, by rfl⟩ : syracuseStep 7808471 = 11712707) B11712707
theorem B5205647 : Blo 2055435 5205647 := bstep (se 1 (by rfl) ⟨3904235, by rfl⟩ : syracuseStep 5205647 = 7808471) B7808471
theorem B3470431 : Blo 2055435 3470431 := bstep (se 1 (by rfl) ⟨2602823, by rfl⟩ : syracuseStep 3470431 = 5205647) B5205647
theorem B4627241 : Blo 2055435 4627241 := bstep (se 2 (by rfl) ⟨1735215, by rfl⟩ : syracuseStep 4627241 = 3470431) B3470431
theorem B3084827 : Blo 2055435 3084827 := bstep (se 1 (by rfl) ⟨2313620, by rfl⟩ : syracuseStep 3084827 = 4627241) B4627241
theorem B2056551 : Blo 2055435 2056551 := bstep (se 1 (by rfl) ⟨1542413, by rfl⟩ : syracuseStep 2056551 = 3084827) B3084827
theorem B2313625 : Blo 2055435 2313625 := bbase (se 2 (by rfl) ⟨867609, by rfl⟩ : syracuseStep 2313625 = 1735219) (by norm_num)
theorem B3084833 : Blo 2055435 3084833 := bstep (se 2 (by rfl) ⟨1156812, by rfl⟩ : syracuseStep 3084833 = 2313625) B2313625
theorem B2056555 : Blo 2055435 2056555 := bstep (se 1 (by rfl) ⟨1542416, by rfl⟩ : syracuseStep 2056555 = 3084833) B3084833
theorem B7808501 : Blo 2055435 7808501 := bbase (se 5 (by rfl) ⟨366023, by rfl⟩ : syracuseStep 7808501 = 732047) (by norm_num)
theorem B5205667 : Blo 2055435 5205667 := bstep (se 1 (by rfl) ⟨3904250, by rfl⟩ : syracuseStep 5205667 = 7808501) B7808501
theorem B6940889 : Blo 2055435 6940889 := bstep (se 2 (by rfl) ⟨2602833, by rfl⟩ : syracuseStep 6940889 = 5205667) B5205667
theorem B4627259 : Blo 2055435 4627259 := bstep (se 1 (by rfl) ⟨3470444, by rfl⟩ : syracuseStep 4627259 = 6940889) B6940889
theorem B3084839 : Blo 2055435 3084839 := bstep (se 1 (by rfl) ⟨2313629, by rfl⟩ : syracuseStep 3084839 = 4627259) B4627259
theorem B2056559 : Blo 2055435 2056559 := bstep (se 1 (by rfl) ⟨1542419, by rfl⟩ : syracuseStep 2056559 = 3084839) B3084839
theorem B3084845 : Blo 2055435 3084845 := bbase (se 3 (by rfl) ⟨578408, by rfl⟩ : syracuseStep 3084845 = 1156817) (by norm_num)
theorem B2056563 : Blo 2055435 2056563 := bstep (se 1 (by rfl) ⟨1542422, by rfl⟩ : syracuseStep 2056563 = 3084845) B3084845
theorem B4627277 : Blo 2055435 4627277 := bbase (se 3 (by rfl) ⟨867614, by rfl⟩ : syracuseStep 4627277 = 1735229) (by norm_num)
theorem B3084851 : Blo 2055435 3084851 := bstep (se 1 (by rfl) ⟨2313638, by rfl⟩ : syracuseStep 3084851 = 4627277) B4627277
theorem B2056567 : Blo 2055435 2056567 := bstep (se 1 (by rfl) ⟨1542425, by rfl⟩ : syracuseStep 2056567 = 3084851) B3084851
theorem B2602849 : Blo 2055435 2602849 := bbase (se 2 (by rfl) ⟨976068, by rfl⟩ : syracuseStep 2602849 = 1952137) (by norm_num)
theorem B3470465 : Blo 2055435 3470465 := bstep (se 2 (by rfl) ⟨1301424, by rfl⟩ : syracuseStep 3470465 = 2602849) B2602849
theorem B2313643 : Blo 2055435 2313643 := bstep (se 1 (by rfl) ⟨1735232, by rfl⟩ : syracuseStep 2313643 = 3470465) B3470465
theorem B3084857 : Blo 2055435 3084857 := bstep (se 2 (by rfl) ⟨1156821, by rfl⟩ : syracuseStep 3084857 = 2313643) B2313643
theorem B2056571 : Blo 2055435 2056571 := bstep (se 1 (by rfl) ⟨1542428, by rfl⟩ : syracuseStep 2056571 = 3084857) B3084857
theorem B23425685 : Blo 2055435 23425685 := bbase (se 6 (by rfl) ⟨549039, by rfl⟩ : syracuseStep 23425685 = 1098079) (by norm_num)
theorem B15617123 : Blo 2055435 15617123 := bstep (se 1 (by rfl) ⟨11712842, by rfl⟩ : syracuseStep 15617123 = 23425685) B23425685
theorem B10411415 : Blo 2055435 10411415 := bstep (se 1 (by rfl) ⟨7808561, by rfl⟩ : syracuseStep 10411415 = 15617123) B15617123
theorem B6940943 : Blo 2055435 6940943 := bstep (se 1 (by rfl) ⟨5205707, by rfl⟩ : syracuseStep 6940943 = 10411415) B10411415
theorem B4627295 : Blo 2055435 4627295 := bstep (se 1 (by rfl) ⟨3470471, by rfl⟩ : syracuseStep 4627295 = 6940943) B6940943
theorem B3084863 : Blo 2055435 3084863 := bstep (se 1 (by rfl) ⟨2313647, by rfl⟩ : syracuseStep 3084863 = 4627295) B4627295
theorem B2056575 : Blo 2055435 2056575 := bstep (se 1 (by rfl) ⟨1542431, by rfl⟩ : syracuseStep 2056575 = 3084863) B3084863
theorem B3084869 : Blo 2055435 3084869 := bbase (se 4 (by rfl) ⟨289206, by rfl⟩ : syracuseStep 3084869 = 578413) (by norm_num)
theorem B2056579 : Blo 2055435 2056579 := bstep (se 1 (by rfl) ⟨1542434, by rfl⟩ : syracuseStep 2056579 = 3084869) B3084869
theorem B3470485 : Blo 2055435 3470485 := bbase (se 6 (by rfl) ⟨81339, by rfl⟩ : syracuseStep 3470485 = 162679) (by norm_num)
theorem B4627313 : Blo 2055435 4627313 := bstep (se 2 (by rfl) ⟨1735242, by rfl⟩ : syracuseStep 4627313 = 3470485) B3470485
theorem B3084875 : Blo 2055435 3084875 := bstep (se 1 (by rfl) ⟨2313656, by rfl⟩ : syracuseStep 3084875 = 4627313) B4627313
theorem B2056583 : Blo 2055435 2056583 := bstep (se 1 (by rfl) ⟨1542437, by rfl⟩ : syracuseStep 2056583 = 3084875) B3084875
theorem B2313661 : Blo 2055435 2313661 := bbase (se 3 (by rfl) ⟨433811, by rfl⟩ : syracuseStep 2313661 = 867623) (by norm_num)
theorem B3084881 : Blo 2055435 3084881 := bstep (se 2 (by rfl) ⟨1156830, by rfl⟩ : syracuseStep 3084881 = 2313661) B2313661
theorem B2056587 : Blo 2055435 2056587 := bstep (se 1 (by rfl) ⟨1542440, by rfl⟩ : syracuseStep 2056587 = 3084881) B3084881
theorem B6940997 : Blo 2055435 6940997 := bbase (se 4 (by rfl) ⟨650718, by rfl⟩ : syracuseStep 6940997 = 1301437) (by norm_num)
theorem B4627331 : Blo 2055435 4627331 := bstep (se 1 (by rfl) ⟨3470498, by rfl⟩ : syracuseStep 4627331 = 6940997) B6940997
theorem B3084887 : Blo 2055435 3084887 := bstep (se 1 (by rfl) ⟨2313665, by rfl⟩ : syracuseStep 3084887 = 4627331) B4627331
theorem B2056591 : Blo 2055435 2056591 := bstep (se 1 (by rfl) ⟨1542443, by rfl⟩ : syracuseStep 2056591 = 3084887) B3084887
theorem B3084893 : Blo 2055435 3084893 := bbase (se 3 (by rfl) ⟨578417, by rfl⟩ : syracuseStep 3084893 = 1156835) (by norm_num)
theorem B2056595 : Blo 2055435 2056595 := bstep (se 1 (by rfl) ⟨1542446, by rfl⟩ : syracuseStep 2056595 = 3084893) B3084893
theorem B4627349 : Blo 2055435 4627349 := bbase (se 6 (by rfl) ⟨108453, by rfl⟩ : syracuseStep 4627349 = 216907) (by norm_num)
theorem B3084899 : Blo 2055435 3084899 := bstep (se 1 (by rfl) ⟨2313674, by rfl⟩ : syracuseStep 3084899 = 4627349) B4627349
theorem B2056599 : Blo 2055435 2056599 := bstep (se 1 (by rfl) ⟨1542449, by rfl⟩ : syracuseStep 2056599 = 3084899) B3084899
theorem B3706069 : Blo 2055435 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B4941425 : Blo 2055435 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B3294283 : Blo 2055435 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B4392377 : Blo 2055435 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B2928251 : Blo 2055435 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B7808669 : Blo 2055435 7808669 := bstep (se 3 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 7808669 = 2928251) B2928251
theorem B5205779 : Blo 2055435 5205779 := bstep (se 1 (by rfl) ⟨3904334, by rfl⟩ : syracuseStep 5205779 = 7808669) B7808669
theorem B3470519 : Blo 2055435 3470519 := bstep (se 1 (by rfl) ⟨2602889, by rfl⟩ : syracuseStep 3470519 = 5205779) B5205779
theorem B2313679 : Blo 2055435 2313679 := bstep (se 1 (by rfl) ⟨1735259, by rfl⟩ : syracuseStep 2313679 = 3470519) B3470519
theorem B3084905 : Blo 2055435 3084905 := bstep (se 2 (by rfl) ⟨1156839, by rfl⟩ : syracuseStep 3084905 = 2313679) B2313679
theorem B2056603 : Blo 2055435 2056603 := bstep (se 1 (by rfl) ⟨1542452, by rfl⟩ : syracuseStep 2056603 = 3084905) B3084905
theorem B3517877 : Blo 2055435 3517877 := bbase (se 5 (by rfl) ⟨164900, by rfl⟩ : syracuseStep 3517877 = 329801) (by norm_num)
theorem B9381005 : Blo 2055435 9381005 := bstep (se 3 (by rfl) ⟨1758938, by rfl⟩ : syracuseStep 9381005 = 3517877) B3517877
theorem B6254003 : Blo 2055435 6254003 := bstep (se 1 (by rfl) ⟨4690502, by rfl⟩ : syracuseStep 6254003 = 9381005) B9381005
theorem B4169335 : Blo 2055435 4169335 := bstep (se 1 (by rfl) ⟨3127001, by rfl⟩ : syracuseStep 4169335 = 6254003) B6254003
theorem B5559113 : Blo 2055435 5559113 := bstep (se 2 (by rfl) ⟨2084667, by rfl⟩ : syracuseStep 5559113 = 4169335) B4169335
theorem B3706075 : Blo 2055435 3706075 := bstep (se 1 (by rfl) ⟨2779556, by rfl⟩ : syracuseStep 3706075 = 5559113) B5559113
theorem B4941433 : Blo 2055435 4941433 := bstep (se 2 (by rfl) ⟨1853037, by rfl⟩ : syracuseStep 4941433 = 3706075) B3706075
theorem B6588577 : Blo 2055435 6588577 := bstep (se 2 (by rfl) ⟨2470716, by rfl⟩ : syracuseStep 6588577 = 4941433) B4941433
theorem B8784769 : Blo 2055435 8784769 := bstep (se 2 (by rfl) ⟨3294288, by rfl⟩ : syracuseStep 8784769 = 6588577) B6588577
theorem B11713025 : Blo 2055435 11713025 := bstep (se 2 (by rfl) ⟨4392384, by rfl⟩ : syracuseStep 11713025 = 8784769) B8784769
theorem B7808683 : Blo 2055435 7808683 := bstep (se 1 (by rfl) ⟨5856512, by rfl⟩ : syracuseStep 7808683 = 11713025) B11713025
theorem B10411577 : Blo 2055435 10411577 := bstep (se 2 (by rfl) ⟨3904341, by rfl⟩ : syracuseStep 10411577 = 7808683) B7808683
theorem B6941051 : Blo 2055435 6941051 := bstep (se 1 (by rfl) ⟨5205788, by rfl⟩ : syracuseStep 6941051 = 10411577) B10411577
theorem B4627367 : Blo 2055435 4627367 := bstep (se 1 (by rfl) ⟨3470525, by rfl⟩ : syracuseStep 4627367 = 6941051) B6941051
theorem B3084911 : Blo 2055435 3084911 := bstep (se 1 (by rfl) ⟨2313683, by rfl⟩ : syracuseStep 3084911 = 4627367) B4627367
theorem B2056607 : Blo 2055435 2056607 := bstep (se 1 (by rfl) ⟨1542455, by rfl⟩ : syracuseStep 2056607 = 3084911) B3084911
theorem B3084917 : Blo 2055435 3084917 := bbase (se 5 (by rfl) ⟨144605, by rfl⟩ : syracuseStep 3084917 = 289211) (by norm_num)
theorem B2056611 : Blo 2055435 2056611 := bstep (se 1 (by rfl) ⟨1542458, by rfl⟩ : syracuseStep 2056611 = 3084917) B3084917
theorem B3904357 : Blo 2055435 3904357 := bbase (se 4 (by rfl) ⟨366033, by rfl⟩ : syracuseStep 3904357 = 732067) (by norm_num)
theorem B5205809 : Blo 2055435 5205809 := bstep (se 2 (by rfl) ⟨1952178, by rfl⟩ : syracuseStep 5205809 = 3904357) B3904357
theorem B3470539 : Blo 2055435 3470539 := bstep (se 1 (by rfl) ⟨2602904, by rfl⟩ : syracuseStep 3470539 = 5205809) B5205809
theorem B4627385 : Blo 2055435 4627385 := bstep (se 2 (by rfl) ⟨1735269, by rfl⟩ : syracuseStep 4627385 = 3470539) B3470539
theorem B3084923 : Blo 2055435 3084923 := bstep (se 1 (by rfl) ⟨2313692, by rfl⟩ : syracuseStep 3084923 = 4627385) B4627385
theorem B2056615 : Blo 2055435 2056615 := bstep (se 1 (by rfl) ⟨1542461, by rfl⟩ : syracuseStep 2056615 = 3084923) B3084923
theorem B2313697 : Blo 2055435 2313697 := bbase (se 2 (by rfl) ⟨867636, by rfl⟩ : syracuseStep 2313697 = 1735273) (by norm_num)
theorem B3084929 : Blo 2055435 3084929 := bstep (se 2 (by rfl) ⟨1156848, by rfl⟩ : syracuseStep 3084929 = 2313697) B2313697
theorem B2056619 : Blo 2055435 2056619 := bstep (se 1 (by rfl) ⟨1542464, by rfl⟩ : syracuseStep 2056619 = 3084929) B3084929
theorem B5205829 : Blo 2055435 5205829 := bbase (se 4 (by rfl) ⟨488046, by rfl⟩ : syracuseStep 5205829 = 976093) (by norm_num)
theorem B6941105 : Blo 2055435 6941105 := bstep (se 2 (by rfl) ⟨2602914, by rfl⟩ : syracuseStep 6941105 = 5205829) B5205829
theorem B4627403 : Blo 2055435 4627403 := bstep (se 1 (by rfl) ⟨3470552, by rfl⟩ : syracuseStep 4627403 = 6941105) B6941105
theorem B3084935 : Blo 2055435 3084935 := bstep (se 1 (by rfl) ⟨2313701, by rfl⟩ : syracuseStep 3084935 = 4627403) B4627403
theorem B2056623 : Blo 2055435 2056623 := bstep (se 1 (by rfl) ⟨1542467, by rfl⟩ : syracuseStep 2056623 = 3084935) B3084935
theorem B3084941 : Blo 2055435 3084941 := bbase (se 3 (by rfl) ⟨578426, by rfl⟩ : syracuseStep 3084941 = 1156853) (by norm_num)
theorem B2056627 : Blo 2055435 2056627 := bstep (se 1 (by rfl) ⟨1542470, by rfl⟩ : syracuseStep 2056627 = 3084941) B3084941
theorem B4627421 : Blo 2055435 4627421 := bbase (se 3 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 4627421 = 1735283) (by norm_num)
theorem B3084947 : Blo 2055435 3084947 := bstep (se 1 (by rfl) ⟨2313710, by rfl⟩ : syracuseStep 3084947 = 4627421) B4627421
theorem B2056631 : Blo 2055435 2056631 := bstep (se 1 (by rfl) ⟨1542473, by rfl⟩ : syracuseStep 2056631 = 3084947) B3084947
theorem B3470573 : Blo 2055435 3470573 := bbase (se 3 (by rfl) ⟨650732, by rfl⟩ : syracuseStep 3470573 = 1301465) (by norm_num)
theorem B2313715 : Blo 2055435 2313715 := bstep (se 1 (by rfl) ⟨1735286, by rfl⟩ : syracuseStep 2313715 = 3470573) B3470573
theorem B3084953 : Blo 2055435 3084953 := bstep (se 2 (by rfl) ⟨1156857, by rfl⟩ : syracuseStep 3084953 = 2313715) B2313715
theorem B2056635 : Blo 2055435 2056635 := bstep (se 1 (by rfl) ⟨1542476, by rfl⟩ : syracuseStep 2056635 = 3084953) B3084953
theorem B9026261 : Blo 2055435 9026261 := bbase (se 7 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 9026261 = 211553) (by norm_num)
theorem B6017507 : Blo 2055435 6017507 := bstep (se 1 (by rfl) ⟨4513130, by rfl⟩ : syracuseStep 6017507 = 9026261) B9026261
theorem B4011671 : Blo 2055435 4011671 := bstep (se 1 (by rfl) ⟨3008753, by rfl⟩ : syracuseStep 4011671 = 6017507) B6017507
theorem B2674447 : Blo 2055435 2674447 := bstep (se 1 (by rfl) ⟨2005835, by rfl⟩ : syracuseStep 2674447 = 4011671) B4011671
theorem B14263717 : Blo 2055435 14263717 := bstep (se 4 (by rfl) ⟨1337223, by rfl⟩ : syracuseStep 14263717 = 2674447) B2674447
theorem B19018289 : Blo 2055435 19018289 := bstep (se 2 (by rfl) ⟨7131858, by rfl⟩ : syracuseStep 19018289 = 14263717) B14263717
theorem B12678859 : Blo 2055435 12678859 := bstep (se 1 (by rfl) ⟨9509144, by rfl⟩ : syracuseStep 12678859 = 19018289) B19018289
theorem B16905145 : Blo 2055435 16905145 := bstep (se 2 (by rfl) ⟨6339429, by rfl⟩ : syracuseStep 16905145 = 12678859) B12678859
theorem B22540193 : Blo 2055435 22540193 := bstep (se 2 (by rfl) ⟨8452572, by rfl⟩ : syracuseStep 22540193 = 16905145) B16905145
theorem B15026795 : Blo 2055435 15026795 := bstep (se 1 (by rfl) ⟨11270096, by rfl⟩ : syracuseStep 15026795 = 22540193) B22540193
theorem B10017863 : Blo 2055435 10017863 := bstep (se 1 (by rfl) ⟨7513397, by rfl⟩ : syracuseStep 10017863 = 15026795) B15026795
theorem B6678575 : Blo 2055435 6678575 := bstep (se 1 (by rfl) ⟨5008931, by rfl⟩ : syracuseStep 6678575 = 10017863) B10017863
theorem B4452383 : Blo 2055435 4452383 := bstep (se 1 (by rfl) ⟨3339287, by rfl⟩ : syracuseStep 4452383 = 6678575) B6678575
theorem B2968255 : Blo 2055435 2968255 := bstep (se 1 (by rfl) ⟨2226191, by rfl⟩ : syracuseStep 2968255 = 4452383) B4452383
theorem B3957673 : Blo 2055435 3957673 := bstep (se 2 (by rfl) ⟨1484127, by rfl⟩ : syracuseStep 3957673 = 2968255) B2968255
theorem B5276897 : Blo 2055435 5276897 := bstep (se 2 (by rfl) ⟨1978836, by rfl⟩ : syracuseStep 5276897 = 3957673) B3957673
theorem B3517931 : Blo 2055435 3517931 := bstep (se 1 (by rfl) ⟨2638448, by rfl⟩ : syracuseStep 3517931 = 5276897) B5276897
theorem B9381149 : Blo 2055435 9381149 := bstep (se 3 (by rfl) ⟨1758965, by rfl⟩ : syracuseStep 9381149 = 3517931) B3517931
theorem B6254099 : Blo 2055435 6254099 := bstep (se 1 (by rfl) ⟨4690574, by rfl⟩ : syracuseStep 6254099 = 9381149) B9381149
theorem B4169399 : Blo 2055435 4169399 := bstep (se 1 (by rfl) ⟨3127049, by rfl⟩ : syracuseStep 4169399 = 6254099) B6254099
theorem B11118397 : Blo 2055435 11118397 := bstep (se 3 (by rfl) ⟨2084699, by rfl⟩ : syracuseStep 11118397 = 4169399) B4169399
theorem B14824529 : Blo 2055435 14824529 := bstep (se 2 (by rfl) ⟨5559198, by rfl⟩ : syracuseStep 14824529 = 11118397) B11118397
theorem B9883019 : Blo 2055435 9883019 := bstep (se 1 (by rfl) ⟨7412264, by rfl⟩ : syracuseStep 9883019 = 14824529) B14824529
theorem B26354717 : Blo 2055435 26354717 := bstep (se 3 (by rfl) ⟨4941509, by rfl⟩ : syracuseStep 26354717 = 9883019) B9883019
theorem B17569811 : Blo 2055435 17569811 := bstep (se 1 (by rfl) ⟨13177358, by rfl⟩ : syracuseStep 17569811 = 26354717) B26354717
theorem B11713207 : Blo 2055435 11713207 := bstep (se 1 (by rfl) ⟨8784905, by rfl⟩ : syracuseStep 11713207 = 17569811) B17569811
theorem B15617609 : Blo 2055435 15617609 := bstep (se 2 (by rfl) ⟨5856603, by rfl⟩ : syracuseStep 15617609 = 11713207) B11713207
theorem B10411739 : Blo 2055435 10411739 := bstep (se 1 (by rfl) ⟨7808804, by rfl⟩ : syracuseStep 10411739 = 15617609) B15617609
theorem B6941159 : Blo 2055435 6941159 := bstep (se 1 (by rfl) ⟨5205869, by rfl⟩ : syracuseStep 6941159 = 10411739) B10411739
theorem B4627439 : Blo 2055435 4627439 := bstep (se 1 (by rfl) ⟨3470579, by rfl⟩ : syracuseStep 4627439 = 6941159) B6941159
theorem B3084959 : Blo 2055435 3084959 := bstep (se 1 (by rfl) ⟨2313719, by rfl⟩ : syracuseStep 3084959 = 4627439) B4627439
theorem B2056639 : Blo 2055435 2056639 := bstep (se 1 (by rfl) ⟨1542479, by rfl⟩ : syracuseStep 2056639 = 3084959) B3084959
theorem B3084965 : Blo 2055435 3084965 := bbase (se 4 (by rfl) ⟨289215, by rfl⟩ : syracuseStep 3084965 = 578431) (by norm_num)
theorem B2056643 : Blo 2055435 2056643 := bstep (se 1 (by rfl) ⟨1542482, by rfl⟩ : syracuseStep 2056643 = 3084965) B3084965
theorem B2602945 : Blo 2055435 2602945 := bbase (se 2 (by rfl) ⟨976104, by rfl⟩ : syracuseStep 2602945 = 1952209) (by norm_num)
theorem B3470593 : Blo 2055435 3470593 := bstep (se 2 (by rfl) ⟨1301472, by rfl⟩ : syracuseStep 3470593 = 2602945) B2602945
theorem B4627457 : Blo 2055435 4627457 := bstep (se 2 (by rfl) ⟨1735296, by rfl⟩ : syracuseStep 4627457 = 3470593) B3470593
theorem B3084971 : Blo 2055435 3084971 := bstep (se 1 (by rfl) ⟨2313728, by rfl⟩ : syracuseStep 3084971 = 4627457) B4627457
theorem B2056647 : Blo 2055435 2056647 := bstep (se 1 (by rfl) ⟨1542485, by rfl⟩ : syracuseStep 2056647 = 3084971) B3084971
theorem B2313733 : Blo 2055435 2313733 := bbase (se 4 (by rfl) ⟨216912, by rfl⟩ : syracuseStep 2313733 = 433825) (by norm_num)
theorem B3084977 : Blo 2055435 3084977 := bstep (se 2 (by rfl) ⟨1156866, by rfl⟩ : syracuseStep 3084977 = 2313733) B2313733
theorem B2056651 : Blo 2055435 2056651 := bstep (se 1 (by rfl) ⟨1542488, by rfl⟩ : syracuseStep 2056651 = 3084977) B3084977
theorem B2928325 : Blo 2055435 2928325 := bbase (se 4 (by rfl) ⟨274530, by rfl⟩ : syracuseStep 2928325 = 549061) (by norm_num)
theorem B3904433 : Blo 2055435 3904433 := bstep (se 2 (by rfl) ⟨1464162, by rfl⟩ : syracuseStep 3904433 = 2928325) B2928325
theorem B2602955 : Blo 2055435 2602955 := bstep (se 1 (by rfl) ⟨1952216, by rfl⟩ : syracuseStep 2602955 = 3904433) B3904433
theorem B6941213 : Blo 2055435 6941213 := bstep (se 3 (by rfl) ⟨1301477, by rfl⟩ : syracuseStep 6941213 = 2602955) B2602955
theorem B4627475 : Blo 2055435 4627475 := bstep (se 1 (by rfl) ⟨3470606, by rfl⟩ : syracuseStep 4627475 = 6941213) B6941213
theorem B3084983 : Blo 2055435 3084983 := bstep (se 1 (by rfl) ⟨2313737, by rfl⟩ : syracuseStep 3084983 = 4627475) B4627475
theorem B2056655 : Blo 2055435 2056655 := bstep (se 1 (by rfl) ⟨1542491, by rfl⟩ : syracuseStep 2056655 = 3084983) B3084983
theorem B3084989 : Blo 2055435 3084989 := bbase (se 3 (by rfl) ⟨578435, by rfl⟩ : syracuseStep 3084989 = 1156871) (by norm_num)
theorem B2056659 : Blo 2055435 2056659 := bstep (se 1 (by rfl) ⟨1542494, by rfl⟩ : syracuseStep 2056659 = 3084989) B3084989
theorem B4627493 : Blo 2055435 4627493 := bbase (se 4 (by rfl) ⟨433827, by rfl⟩ : syracuseStep 4627493 = 867655) (by norm_num)
theorem B3084995 : Blo 2055435 3084995 := bstep (se 1 (by rfl) ⟨2313746, by rfl⟩ : syracuseStep 3084995 = 4627493) B4627493
theorem B2056663 : Blo 2055435 2056663 := bstep (se 1 (by rfl) ⟨1542497, by rfl⟩ : syracuseStep 2056663 = 3084995) B3084995
theorem B5205941 : Blo 2055435 5205941 := bbase (se 5 (by rfl) ⟨244028, by rfl⟩ : syracuseStep 5205941 = 488057) (by norm_num)
theorem B3470627 : Blo 2055435 3470627 := bstep (se 1 (by rfl) ⟨2602970, by rfl⟩ : syracuseStep 3470627 = 5205941) B5205941
theorem B2313751 : Blo 2055435 2313751 := bstep (se 1 (by rfl) ⟨1735313, by rfl⟩ : syracuseStep 2313751 = 3470627) B3470627
theorem B3085001 : Blo 2055435 3085001 := bstep (se 2 (by rfl) ⟨1156875, by rfl⟩ : syracuseStep 3085001 = 2313751) B2313751
theorem B2056667 : Blo 2055435 2056667 := bstep (se 1 (by rfl) ⟨1542500, by rfl⟩ : syracuseStep 2056667 = 3085001) B3085001
theorem B5276981 : Blo 2055435 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B3517987 : Blo 2055435 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B4690649 : Blo 2055435 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B3127099 : Blo 2055435 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B4169465 : Blo 2055435 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B2779643 : Blo 2055435 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B7412381 : Blo 2055435 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B4941587 : Blo 2055435 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B13177565 : Blo 2055435 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B8785043 : Blo 2055435 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B5856695 : Blo 2055435 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B3904463 : Blo 2055435 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B10411901 : Blo 2055435 10411901 := bstep (se 3 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 10411901 = 3904463) B3904463
theorem B6941267 : Blo 2055435 6941267 := bstep (se 1 (by rfl) ⟨5205950, by rfl⟩ : syracuseStep 6941267 = 10411901) B10411901
theorem B4627511 : Blo 2055435 4627511 := bstep (se 1 (by rfl) ⟨3470633, by rfl⟩ : syracuseStep 4627511 = 6941267) B6941267
theorem B3085007 : Blo 2055435 3085007 := bstep (se 1 (by rfl) ⟨2313755, by rfl⟩ : syracuseStep 3085007 = 4627511) B4627511
theorem B2056671 : Blo 2055435 2056671 := bstep (se 1 (by rfl) ⟨1542503, by rfl⟩ : syracuseStep 2056671 = 3085007) B3085007
theorem B3085013 : Blo 2055435 3085013 := bbase (se 7 (by rfl) ⟨36152, by rfl⟩ : syracuseStep 3085013 = 72305) (by norm_num)
theorem B2056675 : Blo 2055435 2056675 := bstep (se 1 (by rfl) ⟨1542506, by rfl⟩ : syracuseStep 2056675 = 3085013) B3085013
theorem B3756773 : Blo 2055435 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B2504515 : Blo 2055435 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B3339353 : Blo 2055435 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B8904941 : Blo 2055435 8904941 := bstep (se 3 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 8904941 = 3339353) B3339353
theorem B5936627 : Blo 2055435 5936627 := bstep (se 1 (by rfl) ⟨4452470, by rfl⟩ : syracuseStep 5936627 = 8904941) B8904941
theorem B3957751 : Blo 2055435 3957751 := bstep (se 1 (by rfl) ⟨2968313, by rfl⟩ : syracuseStep 3957751 = 5936627) B5936627
theorem B5277001 : Blo 2055435 5277001 := bstep (se 2 (by rfl) ⟨1978875, by rfl⟩ : syracuseStep 5277001 = 3957751) B3957751
theorem B7036001 : Blo 2055435 7036001 := bstep (se 2 (by rfl) ⟨2638500, by rfl⟩ : syracuseStep 7036001 = 5277001) B5277001
theorem B4690667 : Blo 2055435 4690667 := bstep (se 1 (by rfl) ⟨3518000, by rfl⟩ : syracuseStep 4690667 = 7036001) B7036001
theorem B12508445 : Blo 2055435 12508445 := bstep (se 3 (by rfl) ⟨2345333, by rfl⟩ : syracuseStep 12508445 = 4690667) B4690667
theorem B8338963 : Blo 2055435 8338963 := bstep (se 1 (by rfl) ⟨6254222, by rfl⟩ : syracuseStep 8338963 = 12508445) B12508445
theorem B11118617 : Blo 2055435 11118617 := bstep (se 2 (by rfl) ⟨4169481, by rfl⟩ : syracuseStep 11118617 = 8338963) B8338963
theorem B7412411 : Blo 2055435 7412411 := bstep (se 1 (by rfl) ⟨5559308, by rfl⟩ : syracuseStep 7412411 = 11118617) B11118617
theorem B4941607 : Blo 2055435 4941607 := bstep (se 1 (by rfl) ⟨3706205, by rfl⟩ : syracuseStep 4941607 = 7412411) B7412411
theorem B6588809 : Blo 2055435 6588809 := bstep (se 2 (by rfl) ⟨2470803, by rfl⟩ : syracuseStep 6588809 = 4941607) B4941607
theorem B4392539 : Blo 2055435 4392539 := bstep (se 1 (by rfl) ⟨3294404, by rfl⟩ : syracuseStep 4392539 = 6588809) B6588809
theorem B2928359 : Blo 2055435 2928359 := bstep (se 1 (by rfl) ⟨2196269, by rfl⟩ : syracuseStep 2928359 = 4392539) B4392539
theorem B7808957 : Blo 2055435 7808957 := bstep (se 3 (by rfl) ⟨1464179, by rfl⟩ : syracuseStep 7808957 = 2928359) B2928359
theorem B5205971 : Blo 2055435 5205971 := bstep (se 1 (by rfl) ⟨3904478, by rfl⟩ : syracuseStep 5205971 = 7808957) B7808957
theorem B3470647 : Blo 2055435 3470647 := bstep (se 1 (by rfl) ⟨2602985, by rfl⟩ : syracuseStep 3470647 = 5205971) B5205971
theorem B4627529 : Blo 2055435 4627529 := bstep (se 2 (by rfl) ⟨1735323, by rfl⟩ : syracuseStep 4627529 = 3470647) B3470647
theorem B3085019 : Blo 2055435 3085019 := bstep (se 1 (by rfl) ⟨2313764, by rfl⟩ : syracuseStep 3085019 = 4627529) B4627529
theorem B2056679 : Blo 2055435 2056679 := bstep (se 1 (by rfl) ⟨1542509, by rfl⟩ : syracuseStep 2056679 = 3085019) B3085019
theorem B2313769 : Blo 2055435 2313769 := bbase (se 2 (by rfl) ⟨867663, by rfl⟩ : syracuseStep 2313769 = 1735327) (by norm_num)
theorem B3085025 : Blo 2055435 3085025 := bstep (se 2 (by rfl) ⟨1156884, by rfl⟩ : syracuseStep 3085025 = 2313769) B2313769
theorem B2056683 : Blo 2055435 2056683 := bstep (se 1 (by rfl) ⟨1542512, by rfl⟩ : syracuseStep 2056683 = 3085025) B3085025
theorem B4690685 : Blo 2055435 4690685 := bbase (se 3 (by rfl) ⟨879503, by rfl⟩ : syracuseStep 4690685 = 1759007) (by norm_num)
theorem B3127123 : Blo 2055435 3127123 := bstep (se 1 (by rfl) ⟨2345342, by rfl⟩ : syracuseStep 3127123 = 4690685) B4690685
theorem B4169497 : Blo 2055435 4169497 := bstep (se 2 (by rfl) ⟨1563561, by rfl⟩ : syracuseStep 4169497 = 3127123) B3127123
theorem B5559329 : Blo 2055435 5559329 := bstep (se 2 (by rfl) ⟨2084748, by rfl⟩ : syracuseStep 5559329 = 4169497) B4169497
theorem B3706219 : Blo 2055435 3706219 := bstep (se 1 (by rfl) ⟨2779664, by rfl⟩ : syracuseStep 3706219 = 5559329) B5559329
theorem B19766501 : Blo 2055435 19766501 := bstep (se 4 (by rfl) ⟨1853109, by rfl⟩ : syracuseStep 19766501 = 3706219) B3706219
theorem B13177667 : Blo 2055435 13177667 := bstep (se 1 (by rfl) ⟨9883250, by rfl⟩ : syracuseStep 13177667 = 19766501) B19766501
theorem B8785111 : Blo 2055435 8785111 := bstep (se 1 (by rfl) ⟨6588833, by rfl⟩ : syracuseStep 8785111 = 13177667) B13177667
theorem B11713481 : Blo 2055435 11713481 := bstep (se 2 (by rfl) ⟨4392555, by rfl⟩ : syracuseStep 11713481 = 8785111) B8785111
theorem B7808987 : Blo 2055435 7808987 := bstep (se 1 (by rfl) ⟨5856740, by rfl⟩ : syracuseStep 7808987 = 11713481) B11713481
theorem B5205991 : Blo 2055435 5205991 := bstep (se 1 (by rfl) ⟨3904493, by rfl⟩ : syracuseStep 5205991 = 7808987) B7808987
theorem B6941321 : Blo 2055435 6941321 := bstep (se 2 (by rfl) ⟨2602995, by rfl⟩ : syracuseStep 6941321 = 5205991) B5205991
theorem B4627547 : Blo 2055435 4627547 := bstep (se 1 (by rfl) ⟨3470660, by rfl⟩ : syracuseStep 4627547 = 6941321) B6941321
theorem B3085031 : Blo 2055435 3085031 := bstep (se 1 (by rfl) ⟨2313773, by rfl⟩ : syracuseStep 3085031 = 4627547) B4627547
theorem B2056687 : Blo 2055435 2056687 := bstep (se 1 (by rfl) ⟨1542515, by rfl⟩ : syracuseStep 2056687 = 3085031) B3085031
theorem B3085037 : Blo 2055435 3085037 := bbase (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) (by norm_num)
theorem B2056691 : Blo 2055435 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B4627565 : Blo 2055435 4627565 := bbase (se 3 (by rfl) ⟨867668, by rfl⟩ : syracuseStep 4627565 = 1735337) (by norm_num)
theorem B3085043 : Blo 2055435 3085043 := bstep (se 1 (by rfl) ⟨2313782, by rfl⟩ : syracuseStep 3085043 = 4627565) B4627565
theorem B2056695 : Blo 2055435 2056695 := bstep (se 1 (by rfl) ⟨1542521, by rfl⟩ : syracuseStep 2056695 = 3085043) B3085043
theorem B3904517 : Blo 2055435 3904517 := bbase (se 4 (by rfl) ⟨366048, by rfl⟩ : syracuseStep 3904517 = 732097) (by norm_num)
theorem B2603011 : Blo 2055435 2603011 := bstep (se 1 (by rfl) ⟨1952258, by rfl⟩ : syracuseStep 2603011 = 3904517) B3904517
theorem B3470681 : Blo 2055435 3470681 := bstep (se 2 (by rfl) ⟨1301505, by rfl⟩ : syracuseStep 3470681 = 2603011) B2603011
theorem B2313787 : Blo 2055435 2313787 := bstep (se 1 (by rfl) ⟨1735340, by rfl⟩ : syracuseStep 2313787 = 3470681) B3470681
theorem B3085049 : Blo 2055435 3085049 := bstep (se 2 (by rfl) ⟨1156893, by rfl⟩ : syracuseStep 3085049 = 2313787) B2313787
theorem B2056699 : Blo 2055435 2056699 := bstep (se 1 (by rfl) ⟨1542524, by rfl⟩ : syracuseStep 2056699 = 3085049) B3085049
theorem B3008845 : Blo 2055435 3008845 := bbase (se 3 (by rfl) ⟨564158, by rfl⟩ : syracuseStep 3008845 = 1128317) (by norm_num)
theorem B16047173 : Blo 2055435 16047173 := bstep (se 4 (by rfl) ⟨1504422, by rfl⟩ : syracuseStep 16047173 = 3008845) B3008845
theorem B42792461 : Blo 2055435 42792461 := bstep (se 3 (by rfl) ⟨8023586, by rfl⟩ : syracuseStep 42792461 = 16047173) B16047173
theorem B28528307 : Blo 2055435 28528307 := bstep (se 1 (by rfl) ⟨21396230, by rfl⟩ : syracuseStep 28528307 = 42792461) B42792461
theorem B19018871 : Blo 2055435 19018871 := bstep (se 1 (by rfl) ⟨14264153, by rfl⟩ : syracuseStep 19018871 = 28528307) B28528307
theorem B12679247 : Blo 2055435 12679247 := bstep (se 1 (by rfl) ⟨9509435, by rfl⟩ : syracuseStep 12679247 = 19018871) B19018871
theorem B8452831 : Blo 2055435 8452831 := bstep (se 1 (by rfl) ⟨6339623, by rfl⟩ : syracuseStep 8452831 = 12679247) B12679247
theorem B11270441 : Blo 2055435 11270441 := bstep (se 2 (by rfl) ⟨4226415, by rfl⟩ : syracuseStep 11270441 = 8452831) B8452831
theorem B7513627 : Blo 2055435 7513627 := bstep (se 1 (by rfl) ⟨5635220, by rfl⟩ : syracuseStep 7513627 = 11270441) B11270441
theorem B10018169 : Blo 2055435 10018169 := bstep (se 2 (by rfl) ⟨3756813, by rfl⟩ : syracuseStep 10018169 = 7513627) B7513627
theorem B6678779 : Blo 2055435 6678779 := bstep (se 1 (by rfl) ⟨5009084, by rfl⟩ : syracuseStep 6678779 = 10018169) B10018169
theorem B71240309 : Blo 2055435 71240309 := bstep (se 5 (by rfl) ⟨3339389, by rfl⟩ : syracuseStep 71240309 = 6678779) B6678779
theorem B47493539 : Blo 2055435 47493539 := bstep (se 1 (by rfl) ⟨35620154, by rfl⟩ : syracuseStep 47493539 = 71240309) B71240309
theorem B31662359 : Blo 2055435 31662359 := bstep (se 1 (by rfl) ⟨23746769, by rfl⟩ : syracuseStep 31662359 = 47493539) B47493539
theorem B21108239 : Blo 2055435 21108239 := bstep (se 1 (by rfl) ⟨15831179, by rfl⟩ : syracuseStep 21108239 = 31662359) B31662359
theorem B14072159 : Blo 2055435 14072159 := bstep (se 1 (by rfl) ⟨10554119, by rfl⟩ : syracuseStep 14072159 = 21108239) B21108239
theorem B9381439 : Blo 2055435 9381439 := bstep (se 1 (by rfl) ⟨7036079, by rfl⟩ : syracuseStep 9381439 = 14072159) B14072159
theorem B50034341 : Blo 2055435 50034341 := bstep (se 4 (by rfl) ⟨4690719, by rfl⟩ : syracuseStep 50034341 = 9381439) B9381439
theorem B33356227 : Blo 2055435 33356227 := bstep (se 1 (by rfl) ⟨25017170, by rfl⟩ : syracuseStep 33356227 = 50034341) B50034341
theorem B44474969 : Blo 2055435 44474969 := bstep (se 2 (by rfl) ⟨16678113, by rfl⟩ : syracuseStep 44474969 = 33356227) B33356227
theorem B29649979 : Blo 2055435 29649979 := bstep (se 1 (by rfl) ⟨22237484, by rfl⟩ : syracuseStep 29649979 = 44474969) B44474969
theorem B39533305 : Blo 2055435 39533305 := bstep (se 2 (by rfl) ⟨14824989, by rfl⟩ : syracuseStep 39533305 = 29649979) B29649979
theorem B52711073 : Blo 2055435 52711073 := bstep (se 2 (by rfl) ⟨19766652, by rfl⟩ : syracuseStep 52711073 = 39533305) B39533305
theorem B35140715 : Blo 2055435 35140715 := bstep (se 1 (by rfl) ⟨26355536, by rfl⟩ : syracuseStep 35140715 = 52711073) B52711073
theorem B23427143 : Blo 2055435 23427143 := bstep (se 1 (by rfl) ⟨17570357, by rfl⟩ : syracuseStep 23427143 = 35140715) B35140715
theorem B15618095 : Blo 2055435 15618095 := bstep (se 1 (by rfl) ⟨11713571, by rfl⟩ : syracuseStep 15618095 = 23427143) B23427143
theorem B10412063 : Blo 2055435 10412063 := bstep (se 1 (by rfl) ⟨7809047, by rfl⟩ : syracuseStep 10412063 = 15618095) B15618095
theorem B6941375 : Blo 2055435 6941375 := bstep (se 1 (by rfl) ⟨5206031, by rfl⟩ : syracuseStep 6941375 = 10412063) B10412063
theorem B4627583 : Blo 2055435 4627583 := bstep (se 1 (by rfl) ⟨3470687, by rfl⟩ : syracuseStep 4627583 = 6941375) B6941375
theorem B3085055 : Blo 2055435 3085055 := bstep (se 1 (by rfl) ⟨2313791, by rfl⟩ : syracuseStep 3085055 = 4627583) B4627583
theorem B2056703 : Blo 2055435 2056703 := bstep (se 1 (by rfl) ⟨1542527, by rfl⟩ : syracuseStep 2056703 = 3085055) B3085055
theorem B3085061 : Blo 2055435 3085061 := bbase (se 4 (by rfl) ⟨289224, by rfl⟩ : syracuseStep 3085061 = 578449) (by norm_num)
theorem B2056707 : Blo 2055435 2056707 := bstep (se 1 (by rfl) ⟨1542530, by rfl⟩ : syracuseStep 2056707 = 3085061) B3085061
theorem B3470701 : Blo 2055435 3470701 := bbase (se 3 (by rfl) ⟨650756, by rfl⟩ : syracuseStep 3470701 = 1301513) (by norm_num)
theorem B4627601 : Blo 2055435 4627601 := bstep (se 2 (by rfl) ⟨1735350, by rfl⟩ : syracuseStep 4627601 = 3470701) B3470701
theorem B3085067 : Blo 2055435 3085067 := bstep (se 1 (by rfl) ⟨2313800, by rfl⟩ : syracuseStep 3085067 = 4627601) B4627601
theorem B2056711 : Blo 2055435 2056711 := bstep (se 1 (by rfl) ⟨1542533, by rfl⟩ : syracuseStep 2056711 = 3085067) B3085067
theorem B2313805 : Blo 2055435 2313805 := bbase (se 3 (by rfl) ⟨433838, by rfl⟩ : syracuseStep 2313805 = 867677) (by norm_num)
theorem B3085073 : Blo 2055435 3085073 := bstep (se 2 (by rfl) ⟨1156902, by rfl⟩ : syracuseStep 3085073 = 2313805) B2313805
theorem B2056715 : Blo 2055435 2056715 := bstep (se 1 (by rfl) ⟨1542536, by rfl⟩ : syracuseStep 2056715 = 3085073) B3085073
theorem B6941429 : Blo 2055435 6941429 := bbase (se 5 (by rfl) ⟨325379, by rfl⟩ : syracuseStep 6941429 = 650759) (by norm_num)
theorem B4627619 : Blo 2055435 4627619 := bstep (se 1 (by rfl) ⟨3470714, by rfl⟩ : syracuseStep 4627619 = 6941429) B6941429
theorem B3085079 : Blo 2055435 3085079 := bstep (se 1 (by rfl) ⟨2313809, by rfl⟩ : syracuseStep 3085079 = 4627619) B4627619
theorem B2056719 : Blo 2055435 2056719 := bstep (se 1 (by rfl) ⟨1542539, by rfl⟩ : syracuseStep 2056719 = 3085079) B3085079
theorem B3085085 : Blo 2055435 3085085 := bbase (se 3 (by rfl) ⟨578453, by rfl⟩ : syracuseStep 3085085 = 1156907) (by norm_num)
theorem B2056723 : Blo 2055435 2056723 := bstep (se 1 (by rfl) ⟨1542542, by rfl⟩ : syracuseStep 2056723 = 3085085) B3085085
theorem B4627637 : Blo 2055435 4627637 := bbase (se 5 (by rfl) ⟨216920, by rfl⟩ : syracuseStep 4627637 = 433841) (by norm_num)
theorem B3085091 : Blo 2055435 3085091 := bstep (se 1 (by rfl) ⟨2313818, by rfl⟩ : syracuseStep 3085091 = 4627637) B4627637
theorem B2056727 : Blo 2055435 2056727 := bstep (se 1 (by rfl) ⟨1542545, by rfl⟩ : syracuseStep 2056727 = 3085091) B3085091
theorem B2196325 : Blo 2055435 2196325 := bbase (se 4 (by rfl) ⟨205905, by rfl⟩ : syracuseStep 2196325 = 411811) (by norm_num)
theorem B11713733 : Blo 2055435 11713733 := bstep (se 4 (by rfl) ⟨1098162, by rfl⟩ : syracuseStep 11713733 = 2196325) B2196325
theorem B7809155 : Blo 2055435 7809155 := bstep (se 1 (by rfl) ⟨5856866, by rfl⟩ : syracuseStep 7809155 = 11713733) B11713733
theorem B5206103 : Blo 2055435 5206103 := bstep (se 1 (by rfl) ⟨3904577, by rfl⟩ : syracuseStep 5206103 = 7809155) B7809155
theorem B3470735 : Blo 2055435 3470735 := bstep (se 1 (by rfl) ⟨2603051, by rfl⟩ : syracuseStep 3470735 = 5206103) B5206103
theorem B2313823 : Blo 2055435 2313823 := bstep (se 1 (by rfl) ⟨1735367, by rfl⟩ : syracuseStep 2313823 = 3470735) B3470735
theorem B3085097 : Blo 2055435 3085097 := bstep (se 2 (by rfl) ⟨1156911, by rfl⟩ : syracuseStep 3085097 = 2313823) B2313823
theorem B2056731 : Blo 2055435 2056731 := bstep (se 1 (by rfl) ⟨1542548, by rfl⟩ : syracuseStep 2056731 = 3085097) B3085097
theorem B2196329 : Blo 2055435 2196329 := bbase (se 2 (by rfl) ⟨823623, by rfl⟩ : syracuseStep 2196329 = 1647247) (by norm_num)
theorem B5856877 : Blo 2055435 5856877 := bstep (se 3 (by rfl) ⟨1098164, by rfl⟩ : syracuseStep 5856877 = 2196329) B2196329
theorem B7809169 : Blo 2055435 7809169 := bstep (se 2 (by rfl) ⟨2928438, by rfl⟩ : syracuseStep 7809169 = 5856877) B5856877
theorem B10412225 : Blo 2055435 10412225 := bstep (se 2 (by rfl) ⟨3904584, by rfl⟩ : syracuseStep 10412225 = 7809169) B7809169
theorem B6941483 : Blo 2055435 6941483 := bstep (se 1 (by rfl) ⟨5206112, by rfl⟩ : syracuseStep 6941483 = 10412225) B10412225
theorem B4627655 : Blo 2055435 4627655 := bstep (se 1 (by rfl) ⟨3470741, by rfl⟩ : syracuseStep 4627655 = 6941483) B6941483
theorem B3085103 : Blo 2055435 3085103 := bstep (se 1 (by rfl) ⟨2313827, by rfl⟩ : syracuseStep 3085103 = 4627655) B4627655
theorem B2056735 : Blo 2055435 2056735 := bstep (se 1 (by rfl) ⟨1542551, by rfl⟩ : syracuseStep 2056735 = 3085103) B3085103
theorem B3085109 : Blo 2055435 3085109 := bbase (se 5 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 3085109 = 289229) (by norm_num)
theorem B2056739 : Blo 2055435 2056739 := bstep (se 1 (by rfl) ⟨1542554, by rfl⟩ : syracuseStep 2056739 = 3085109) B3085109
theorem B5206133 : Blo 2055435 5206133 := bbase (se 5 (by rfl) ⟨244037, by rfl⟩ : syracuseStep 5206133 = 488075) (by norm_num)
theorem B3470755 : Blo 2055435 3470755 := bstep (se 1 (by rfl) ⟨2603066, by rfl⟩ : syracuseStep 3470755 = 5206133) B5206133
theorem B4627673 : Blo 2055435 4627673 := bstep (se 2 (by rfl) ⟨1735377, by rfl⟩ : syracuseStep 4627673 = 3470755) B3470755
theorem B3085115 : Blo 2055435 3085115 := bstep (se 1 (by rfl) ⟨2313836, by rfl⟩ : syracuseStep 3085115 = 4627673) B4627673
theorem B2056743 : Blo 2055435 2056743 := bstep (se 1 (by rfl) ⟨1542557, by rfl⟩ : syracuseStep 2056743 = 3085115) B3085115
theorem B2313841 : Blo 2055435 2313841 := bbase (se 2 (by rfl) ⟨867690, by rfl⟩ : syracuseStep 2313841 = 1735381) (by norm_num)
theorem B3085121 : Blo 2055435 3085121 := bstep (se 2 (by rfl) ⟨1156920, by rfl⟩ : syracuseStep 3085121 = 2313841) B2313841
theorem B2056747 : Blo 2055435 2056747 := bstep (se 1 (by rfl) ⟨1542560, by rfl⟩ : syracuseStep 2056747 = 3085121) B3085121
theorem B2817677 : Blo 2055435 2817677 := bbase (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) (by norm_num)
theorem B7513805 : Blo 2055435 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B5009203 : Blo 2055435 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B6678937 : Blo 2055435 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B8905249 : Blo 2055435 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B11873665 : Blo 2055435 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B15831553 : Blo 2055435 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B21108737 : Blo 2055435 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B14072491 : Blo 2055435 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B18763321 : Blo 2055435 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B25017761 : Blo 2055435 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B16678507 : Blo 2055435 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B22238009 : Blo 2055435 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B14825339 : Blo 2055435 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B9883559 : Blo 2055435 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B6589039 : Blo 2055435 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B8785385 : Blo 2055435 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B5856923 : Blo 2055435 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B3904615 : Blo 2055435 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B5206153 : Blo 2055435 5206153 := bstep (se 2 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 5206153 = 3904615) B3904615
theorem B6941537 : Blo 2055435 6941537 := bstep (se 2 (by rfl) ⟨2603076, by rfl⟩ : syracuseStep 6941537 = 5206153) B5206153
theorem B4627691 : Blo 2055435 4627691 := bstep (se 1 (by rfl) ⟨3470768, by rfl⟩ : syracuseStep 4627691 = 6941537) B6941537
theorem B3085127 : Blo 2055435 3085127 := bstep (se 1 (by rfl) ⟨2313845, by rfl⟩ : syracuseStep 3085127 = 4627691) B4627691
theorem B2056751 : Blo 2055435 2056751 := bstep (se 1 (by rfl) ⟨1542563, by rfl⟩ : syracuseStep 2056751 = 3085127) B3085127
theorem B3085133 : Blo 2055435 3085133 := bbase (se 3 (by rfl) ⟨578462, by rfl⟩ : syracuseStep 3085133 = 1156925) (by norm_num)
theorem B2056755 : Blo 2055435 2056755 := bstep (se 1 (by rfl) ⟨1542566, by rfl⟩ : syracuseStep 2056755 = 3085133) B3085133
theorem B4627709 : Blo 2055435 4627709 := bbase (se 3 (by rfl) ⟨867695, by rfl⟩ : syracuseStep 4627709 = 1735391) (by norm_num)
theorem B3085139 : Blo 2055435 3085139 := bstep (se 1 (by rfl) ⟨2313854, by rfl⟩ : syracuseStep 3085139 = 4627709) B4627709
theorem B2056759 : Blo 2055435 2056759 := bstep (se 1 (by rfl) ⟨1542569, by rfl⟩ : syracuseStep 2056759 = 3085139) B3085139
theorem B3470789 : Blo 2055435 3470789 := bbase (se 4 (by rfl) ⟨325386, by rfl⟩ : syracuseStep 3470789 = 650773) (by norm_num)
theorem B2313859 : Blo 2055435 2313859 := bstep (se 1 (by rfl) ⟨1735394, by rfl⟩ : syracuseStep 2313859 = 3470789) B3470789
theorem B3085145 : Blo 2055435 3085145 := bstep (se 2 (by rfl) ⟨1156929, by rfl⟩ : syracuseStep 3085145 = 2313859) B2313859
theorem B2056763 : Blo 2055435 2056763 := bstep (se 1 (by rfl) ⟨1542572, by rfl⟩ : syracuseStep 2056763 = 3085145) B3085145
theorem B15618581 : Blo 2055435 15618581 := bbase (se 6 (by rfl) ⟨366060, by rfl⟩ : syracuseStep 15618581 = 732121) (by norm_num)
theorem B10412387 : Blo 2055435 10412387 := bstep (se 1 (by rfl) ⟨7809290, by rfl⟩ : syracuseStep 10412387 = 15618581) B15618581
theorem B6941591 : Blo 2055435 6941591 := bstep (se 1 (by rfl) ⟨5206193, by rfl⟩ : syracuseStep 6941591 = 10412387) B10412387
theorem B4627727 : Blo 2055435 4627727 := bstep (se 1 (by rfl) ⟨3470795, by rfl⟩ : syracuseStep 4627727 = 6941591) B6941591
theorem B3085151 : Blo 2055435 3085151 := bstep (se 1 (by rfl) ⟨2313863, by rfl⟩ : syracuseStep 3085151 = 4627727) B4627727
theorem B2056767 : Blo 2055435 2056767 := bstep (se 1 (by rfl) ⟨1542575, by rfl⟩ : syracuseStep 2056767 = 3085151) B3085151
theorem B3085157 : Blo 2055435 3085157 := bbase (se 4 (by rfl) ⟨289233, by rfl⟩ : syracuseStep 3085157 = 578467) (by norm_num)
theorem B2056771 : Blo 2055435 2056771 := bstep (se 1 (by rfl) ⟨1542578, by rfl⟩ : syracuseStep 2056771 = 3085157) B3085157
theorem B3904661 : Blo 2055435 3904661 := bbase (se 6 (by rfl) ⟨91515, by rfl⟩ : syracuseStep 3904661 = 183031) (by norm_num)
theorem B2603107 : Blo 2055435 2603107 := bstep (se 1 (by rfl) ⟨1952330, by rfl⟩ : syracuseStep 2603107 = 3904661) B3904661
theorem B3470809 : Blo 2055435 3470809 := bstep (se 2 (by rfl) ⟨1301553, by rfl⟩ : syracuseStep 3470809 = 2603107) B2603107
theorem B4627745 : Blo 2055435 4627745 := bstep (se 2 (by rfl) ⟨1735404, by rfl⟩ : syracuseStep 4627745 = 3470809) B3470809
theorem B3085163 : Blo 2055435 3085163 := bstep (se 1 (by rfl) ⟨2313872, by rfl⟩ : syracuseStep 3085163 = 4627745) B4627745
theorem B2056775 : Blo 2055435 2056775 := bstep (se 1 (by rfl) ⟨1542581, by rfl⟩ : syracuseStep 2056775 = 3085163) B3085163
theorem B2313877 : Blo 2055435 2313877 := bbase (se 6 (by rfl) ⟨54231, by rfl⟩ : syracuseStep 2313877 = 108463) (by norm_num)
theorem B3085169 : Blo 2055435 3085169 := bstep (se 2 (by rfl) ⟨1156938, by rfl⟩ : syracuseStep 3085169 = 2313877) B2313877
theorem B2056779 : Blo 2055435 2056779 := bstep (se 1 (by rfl) ⟨1542584, by rfl⟩ : syracuseStep 2056779 = 3085169) B3085169
theorem B2603117 : Blo 2055435 2603117 := bbase (se 3 (by rfl) ⟨488084, by rfl⟩ : syracuseStep 2603117 = 976169) (by norm_num)
theorem B6941645 : Blo 2055435 6941645 := bstep (se 3 (by rfl) ⟨1301558, by rfl⟩ : syracuseStep 6941645 = 2603117) B2603117
theorem B4627763 : Blo 2055435 4627763 := bstep (se 1 (by rfl) ⟨3470822, by rfl⟩ : syracuseStep 4627763 = 6941645) B6941645
theorem B3085175 : Blo 2055435 3085175 := bstep (se 1 (by rfl) ⟨2313881, by rfl⟩ : syracuseStep 3085175 = 4627763) B4627763
theorem B2056783 : Blo 2055435 2056783 := bstep (se 1 (by rfl) ⟨1542587, by rfl⟩ : syracuseStep 2056783 = 3085175) B3085175
theorem B3085181 : Blo 2055435 3085181 := bbase (se 3 (by rfl) ⟨578471, by rfl⟩ : syracuseStep 3085181 = 1156943) (by norm_num)
theorem B2056787 : Blo 2055435 2056787 := bstep (se 1 (by rfl) ⟨1542590, by rfl⟩ : syracuseStep 2056787 = 3085181) B3085181
theorem B4627781 : Blo 2055435 4627781 := bbase (se 4 (by rfl) ⟨433854, by rfl⟩ : syracuseStep 4627781 = 867709) (by norm_num)
theorem B3085187 : Blo 2055435 3085187 := bstep (se 1 (by rfl) ⟨2313890, by rfl⟩ : syracuseStep 3085187 = 4627781) B4627781
theorem B2056791 : Blo 2055435 2056791 := bstep (se 1 (by rfl) ⟨1542593, by rfl⟩ : syracuseStep 2056791 = 3085187) B3085187
theorem B2142137 : Blo 2055435 2142137 := bbase (se 2 (by rfl) ⟨803301, by rfl⟩ : syracuseStep 2142137 = 1606603) (by norm_num)
theorem B5712365 : Blo 2055435 5712365 := bstep (se 3 (by rfl) ⟨1071068, by rfl⟩ : syracuseStep 5712365 = 2142137) B2142137
theorem B3808243 : Blo 2055435 3808243 := bstep (se 1 (by rfl) ⟨2856182, by rfl⟩ : syracuseStep 3808243 = 5712365) B5712365
theorem B5077657 : Blo 2055435 5077657 := bstep (se 2 (by rfl) ⟨1904121, by rfl⟩ : syracuseStep 5077657 = 3808243) B3808243
theorem B27080837 : Blo 2055435 27080837 := bstep (se 4 (by rfl) ⟨2538828, by rfl⟩ : syracuseStep 27080837 = 5077657) B5077657
theorem B18053891 : Blo 2055435 18053891 := bstep (se 1 (by rfl) ⟨13540418, by rfl⟩ : syracuseStep 18053891 = 27080837) B27080837
theorem B12035927 : Blo 2055435 12035927 := bstep (se 1 (by rfl) ⟨9026945, by rfl⟩ : syracuseStep 12035927 = 18053891) B18053891
theorem B8023951 : Blo 2055435 8023951 := bstep (se 1 (by rfl) ⟨6017963, by rfl⟩ : syracuseStep 8023951 = 12035927) B12035927
theorem B10698601 : Blo 2055435 10698601 := bstep (se 2 (by rfl) ⟨4011975, by rfl⟩ : syracuseStep 10698601 = 8023951) B8023951
theorem B14264801 : Blo 2055435 14264801 := bstep (se 2 (by rfl) ⟨5349300, by rfl⟩ : syracuseStep 14264801 = 10698601) B10698601
theorem B9509867 : Blo 2055435 9509867 := bstep (se 1 (by rfl) ⟨7132400, by rfl⟩ : syracuseStep 9509867 = 14264801) B14264801
theorem B6339911 : Blo 2055435 6339911 := bstep (se 1 (by rfl) ⟨4754933, by rfl⟩ : syracuseStep 6339911 = 9509867) B9509867
theorem B16906429 : Blo 2055435 16906429 := bstep (se 3 (by rfl) ⟨3169955, by rfl⟩ : syracuseStep 16906429 = 6339911) B6339911
theorem B22541905 : Blo 2055435 22541905 := bstep (se 2 (by rfl) ⟨8453214, by rfl⟩ : syracuseStep 22541905 = 16906429) B16906429
theorem B30055873 : Blo 2055435 30055873 := bstep (se 2 (by rfl) ⟨11270952, by rfl⟩ : syracuseStep 30055873 = 22541905) B22541905
theorem B40074497 : Blo 2055435 40074497 := bstep (se 2 (by rfl) ⟨15027936, by rfl⟩ : syracuseStep 40074497 = 30055873) B30055873
theorem B26716331 : Blo 2055435 26716331 := bstep (se 1 (by rfl) ⟨20037248, by rfl⟩ : syracuseStep 26716331 = 40074497) B40074497
theorem B17810887 : Blo 2055435 17810887 := bstep (se 1 (by rfl) ⟨13358165, by rfl⟩ : syracuseStep 17810887 = 26716331) B26716331
theorem B23747849 : Blo 2055435 23747849 := bstep (se 2 (by rfl) ⟨8905443, by rfl⟩ : syracuseStep 23747849 = 17810887) B17810887
theorem B15831899 : Blo 2055435 15831899 := bstep (se 1 (by rfl) ⟨11873924, by rfl⟩ : syracuseStep 15831899 = 23747849) B23747849
theorem B10554599 : Blo 2055435 10554599 := bstep (se 1 (by rfl) ⟨7915949, by rfl⟩ : syracuseStep 10554599 = 15831899) B15831899
theorem B7036399 : Blo 2055435 7036399 := bstep (se 1 (by rfl) ⟨5277299, by rfl⟩ : syracuseStep 7036399 = 10554599) B10554599
theorem B9381865 : Blo 2055435 9381865 := bstep (se 2 (by rfl) ⟨3518199, by rfl⟩ : syracuseStep 9381865 = 7036399) B7036399
theorem B12509153 : Blo 2055435 12509153 := bstep (se 2 (by rfl) ⟨4690932, by rfl⟩ : syracuseStep 12509153 = 9381865) B9381865
theorem B8339435 : Blo 2055435 8339435 := bstep (se 1 (by rfl) ⟨6254576, by rfl⟩ : syracuseStep 8339435 = 12509153) B12509153
theorem B5559623 : Blo 2055435 5559623 := bstep (se 1 (by rfl) ⟨4169717, by rfl⟩ : syracuseStep 5559623 = 8339435) B8339435
theorem B3706415 : Blo 2055435 3706415 := bstep (se 1 (by rfl) ⟨2779811, by rfl⟩ : syracuseStep 3706415 = 5559623) B5559623
theorem B2470943 : Blo 2055435 2470943 := bstep (se 1 (by rfl) ⟨1853207, by rfl⟩ : syracuseStep 2470943 = 3706415) B3706415
theorem B6589181 : Blo 2055435 6589181 := bstep (se 3 (by rfl) ⟨1235471, by rfl⟩ : syracuseStep 6589181 = 2470943) B2470943
theorem B4392787 : Blo 2055435 4392787 := bstep (se 1 (by rfl) ⟨3294590, by rfl⟩ : syracuseStep 4392787 = 6589181) B6589181
theorem B5857049 : Blo 2055435 5857049 := bstep (se 2 (by rfl) ⟨2196393, by rfl⟩ : syracuseStep 5857049 = 4392787) B4392787
theorem B3904699 : Blo 2055435 3904699 := bstep (se 1 (by rfl) ⟨2928524, by rfl⟩ : syracuseStep 3904699 = 5857049) B5857049
theorem B5206265 : Blo 2055435 5206265 := bstep (se 2 (by rfl) ⟨1952349, by rfl⟩ : syracuseStep 5206265 = 3904699) B3904699
theorem B3470843 : Blo 2055435 3470843 := bstep (se 1 (by rfl) ⟨2603132, by rfl⟩ : syracuseStep 3470843 = 5206265) B5206265
theorem B2313895 : Blo 2055435 2313895 := bstep (se 1 (by rfl) ⟨1735421, by rfl⟩ : syracuseStep 2313895 = 3470843) B3470843
theorem B3085193 : Blo 2055435 3085193 := bstep (se 2 (by rfl) ⟨1156947, by rfl⟩ : syracuseStep 3085193 = 2313895) B2313895
theorem B2056795 : Blo 2055435 2056795 := bstep (se 1 (by rfl) ⟨1542596, by rfl⟩ : syracuseStep 2056795 = 3085193) B3085193
theorem B10412549 : Blo 2055435 10412549 := bbase (se 4 (by rfl) ⟨976176, by rfl⟩ : syracuseStep 10412549 = 1952353) (by norm_num)
theorem B6941699 : Blo 2055435 6941699 := bstep (se 1 (by rfl) ⟨5206274, by rfl⟩ : syracuseStep 6941699 = 10412549) B10412549
theorem B4627799 : Blo 2055435 4627799 := bstep (se 1 (by rfl) ⟨3470849, by rfl⟩ : syracuseStep 4627799 = 6941699) B6941699
theorem B3085199 : Blo 2055435 3085199 := bstep (se 1 (by rfl) ⟨2313899, by rfl⟩ : syracuseStep 3085199 = 4627799) B4627799
theorem B2056799 : Blo 2055435 2056799 := bstep (se 1 (by rfl) ⟨1542599, by rfl⟩ : syracuseStep 2056799 = 3085199) B3085199
theorem B3085205 : Blo 2055435 3085205 := bbase (se 6 (by rfl) ⟨72309, by rfl⟩ : syracuseStep 3085205 = 144619) (by norm_num)
theorem B2056803 : Blo 2055435 2056803 := bstep (se 1 (by rfl) ⟨1542602, by rfl⟩ : syracuseStep 2056803 = 3085205) B3085205
theorem B11714165 : Blo 2055435 11714165 := bbase (se 5 (by rfl) ⟨549101, by rfl⟩ : syracuseStep 11714165 = 1098203) (by norm_num)
theorem B7809443 : Blo 2055435 7809443 := bstep (se 1 (by rfl) ⟨5857082, by rfl⟩ : syracuseStep 7809443 = 11714165) B11714165
theorem B5206295 : Blo 2055435 5206295 := bstep (se 1 (by rfl) ⟨3904721, by rfl⟩ : syracuseStep 5206295 = 7809443) B7809443
theorem B3470863 : Blo 2055435 3470863 := bstep (se 1 (by rfl) ⟨2603147, by rfl⟩ : syracuseStep 3470863 = 5206295) B5206295
theorem B4627817 : Blo 2055435 4627817 := bstep (se 2 (by rfl) ⟨1735431, by rfl⟩ : syracuseStep 4627817 = 3470863) B3470863
theorem B3085211 : Blo 2055435 3085211 := bstep (se 1 (by rfl) ⟨2313908, by rfl⟩ : syracuseStep 3085211 = 4627817) B4627817
theorem B2056807 : Blo 2055435 2056807 := bstep (se 1 (by rfl) ⟨1542605, by rfl⟩ : syracuseStep 2056807 = 3085211) B3085211
theorem B2313913 : Blo 2055435 2313913 := bbase (se 2 (by rfl) ⟨867717, by rfl⟩ : syracuseStep 2313913 = 1735435) (by norm_num)
theorem B3085217 : Blo 2055435 3085217 := bstep (se 2 (by rfl) ⟨1156956, by rfl⟩ : syracuseStep 3085217 = 2313913) B2313913
theorem B2056811 : Blo 2055435 2056811 := bstep (se 1 (by rfl) ⟨1542608, by rfl⟩ : syracuseStep 2056811 = 3085217) B3085217
theorem B4392829 : Blo 2055435 4392829 := bbase (se 3 (by rfl) ⟨823655, by rfl⟩ : syracuseStep 4392829 = 1647311) (by norm_num)
theorem B5857105 : Blo 2055435 5857105 := bstep (se 2 (by rfl) ⟨2196414, by rfl⟩ : syracuseStep 5857105 = 4392829) B4392829
theorem B7809473 : Blo 2055435 7809473 := bstep (se 2 (by rfl) ⟨2928552, by rfl⟩ : syracuseStep 7809473 = 5857105) B5857105
theorem B5206315 : Blo 2055435 5206315 := bstep (se 1 (by rfl) ⟨3904736, by rfl⟩ : syracuseStep 5206315 = 7809473) B7809473
theorem B6941753 : Blo 2055435 6941753 := bstep (se 2 (by rfl) ⟨2603157, by rfl⟩ : syracuseStep 6941753 = 5206315) B5206315
theorem B4627835 : Blo 2055435 4627835 := bstep (se 1 (by rfl) ⟨3470876, by rfl⟩ : syracuseStep 4627835 = 6941753) B6941753
theorem B3085223 : Blo 2055435 3085223 := bstep (se 1 (by rfl) ⟨2313917, by rfl⟩ : syracuseStep 3085223 = 4627835) B4627835
theorem B2056815 : Blo 2055435 2056815 := bstep (se 1 (by rfl) ⟨1542611, by rfl⟩ : syracuseStep 2056815 = 3085223) B3085223
theorem B3085229 : Blo 2055435 3085229 := bbase (se 3 (by rfl) ⟨578480, by rfl⟩ : syracuseStep 3085229 = 1156961) (by norm_num)
theorem B2056819 : Blo 2055435 2056819 := bstep (se 1 (by rfl) ⟨1542614, by rfl⟩ : syracuseStep 2056819 = 3085229) B3085229
theorem B4627853 : Blo 2055435 4627853 := bbase (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) (by norm_num)
theorem B3085235 : Blo 2055435 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B2056823 : Blo 2055435 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B2603173 : Blo 2055435 2603173 := bbase (se 4 (by rfl) ⟨244047, by rfl⟩ : syracuseStep 2603173 = 488095) (by norm_num)
theorem B3470897 : Blo 2055435 3470897 := bstep (se 2 (by rfl) ⟨1301586, by rfl⟩ : syracuseStep 3470897 = 2603173) B2603173
theorem B2313931 : Blo 2055435 2313931 := bstep (se 1 (by rfl) ⟨1735448, by rfl⟩ : syracuseStep 2313931 = 3470897) B3470897
theorem B3085241 : Blo 2055435 3085241 := bstep (se 2 (by rfl) ⟨1156965, by rfl⟩ : syracuseStep 3085241 = 2313931) B2313931
theorem B2056827 : Blo 2055435 2056827 := bstep (se 1 (by rfl) ⟨1542620, by rfl⟩ : syracuseStep 2056827 = 3085241) B3085241
theorem B22238869 : Blo 2055435 22238869 := bbase (se 6 (by rfl) ⟨521223, by rfl⟩ : syracuseStep 22238869 = 1042447) (by norm_num)
theorem B29651825 : Blo 2055435 29651825 := bstep (se 2 (by rfl) ⟨11119434, by rfl⟩ : syracuseStep 29651825 = 22238869) B22238869
theorem B19767883 : Blo 2055435 19767883 := bstep (se 1 (by rfl) ⟨14825912, by rfl⟩ : syracuseStep 19767883 = 29651825) B29651825
theorem B26357177 : Blo 2055435 26357177 := bstep (se 2 (by rfl) ⟨9883941, by rfl⟩ : syracuseStep 26357177 = 19767883) B19767883
theorem B17571451 : Blo 2055435 17571451 := bstep (se 1 (by rfl) ⟨13178588, by rfl⟩ : syracuseStep 17571451 = 26357177) B26357177
theorem B23428601 : Blo 2055435 23428601 := bstep (se 2 (by rfl) ⟨8785725, by rfl⟩ : syracuseStep 23428601 = 17571451) B17571451
theorem B15619067 : Blo 2055435 15619067 := bstep (se 1 (by rfl) ⟨11714300, by rfl⟩ : syracuseStep 15619067 = 23428601) B23428601
theorem B10412711 : Blo 2055435 10412711 := bstep (se 1 (by rfl) ⟨7809533, by rfl⟩ : syracuseStep 10412711 = 15619067) B15619067
theorem B6941807 : Blo 2055435 6941807 := bstep (se 1 (by rfl) ⟨5206355, by rfl⟩ : syracuseStep 6941807 = 10412711) B10412711
theorem B4627871 : Blo 2055435 4627871 := bstep (se 1 (by rfl) ⟨3470903, by rfl⟩ : syracuseStep 4627871 = 6941807) B6941807
theorem B3085247 : Blo 2055435 3085247 := bstep (se 1 (by rfl) ⟨2313935, by rfl⟩ : syracuseStep 3085247 = 4627871) B4627871
theorem B2056831 : Blo 2055435 2056831 := bstep (se 1 (by rfl) ⟨1542623, by rfl⟩ : syracuseStep 2056831 = 3085247) B3085247
theorem B3085253 : Blo 2055435 3085253 := bbase (se 4 (by rfl) ⟨289242, by rfl⟩ : syracuseStep 3085253 = 578485) (by norm_num)
theorem B2056835 : Blo 2055435 2056835 := bstep (se 1 (by rfl) ⟨1542626, by rfl⟩ : syracuseStep 2056835 = 3085253) B3085253
theorem B3470917 : Blo 2055435 3470917 := bbase (se 4 (by rfl) ⟨325398, by rfl⟩ : syracuseStep 3470917 = 650797) (by norm_num)
theorem B4627889 : Blo 2055435 4627889 := bstep (se 2 (by rfl) ⟨1735458, by rfl⟩ : syracuseStep 4627889 = 3470917) B3470917
theorem B3085259 : Blo 2055435 3085259 := bstep (se 1 (by rfl) ⟨2313944, by rfl⟩ : syracuseStep 3085259 = 4627889) B4627889
theorem B2056839 : Blo 2055435 2056839 := bstep (se 1 (by rfl) ⟨1542629, by rfl⟩ : syracuseStep 2056839 = 3085259) B3085259
theorem B2313949 : Blo 2055435 2313949 := bbase (se 3 (by rfl) ⟨433865, by rfl⟩ : syracuseStep 2313949 = 867731) (by norm_num)
theorem B3085265 : Blo 2055435 3085265 := bstep (se 2 (by rfl) ⟨1156974, by rfl⟩ : syracuseStep 3085265 = 2313949) B2313949
theorem B2056843 : Blo 2055435 2056843 := bstep (se 1 (by rfl) ⟨1542632, by rfl⟩ : syracuseStep 2056843 = 3085265) B3085265
theorem B6941861 : Blo 2055435 6941861 := bbase (se 4 (by rfl) ⟨650799, by rfl⟩ : syracuseStep 6941861 = 1301599) (by norm_num)
theorem B4627907 : Blo 2055435 4627907 := bstep (se 1 (by rfl) ⟨3470930, by rfl⟩ : syracuseStep 4627907 = 6941861) B6941861
theorem B3085271 : Blo 2055435 3085271 := bstep (se 1 (by rfl) ⟨2313953, by rfl⟩ : syracuseStep 3085271 = 4627907) B4627907
theorem B2056847 : Blo 2055435 2056847 := bstep (se 1 (by rfl) ⟨1542635, by rfl⟩ : syracuseStep 2056847 = 3085271) B3085271
theorem B3085277 : Blo 2055435 3085277 := bbase (se 3 (by rfl) ⟨578489, by rfl⟩ : syracuseStep 3085277 = 1156979) (by norm_num)
theorem B2056851 : Blo 2055435 2056851 := bstep (se 1 (by rfl) ⟨1542638, by rfl⟩ : syracuseStep 2056851 = 3085277) B3085277
theorem B4627925 : Blo 2055435 4627925 := bbase (se 7 (by rfl) ⟨54233, by rfl⟩ : syracuseStep 4627925 = 108467) (by norm_num)
theorem B3085283 : Blo 2055435 3085283 := bstep (se 1 (by rfl) ⟨2313962, by rfl⟩ : syracuseStep 3085283 = 4627925) B4627925
theorem B2056855 : Blo 2055435 2056855 := bstep (se 1 (by rfl) ⟨1542641, by rfl⟩ : syracuseStep 2056855 = 3085283) B3085283
theorem B3518309 : Blo 2055435 3518309 := bbase (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) (by norm_num)
theorem B2345539 : Blo 2055435 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B3127385 : Blo 2055435 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B2084923 : Blo 2055435 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B11119589 : Blo 2055435 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B7413059 : Blo 2055435 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B19768157 : Blo 2055435 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B13178771 : Blo 2055435 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B8785847 : Blo 2055435 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B5857231 : Blo 2055435 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B7809641 : Blo 2055435 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B5206427 : Blo 2055435 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B3470951 : Blo 2055435 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B2313967 : Blo 2055435 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B3085289 : Blo 2055435 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B2056859 : Blo 2055435 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B6589397 : Blo 2055435 6589397 := bbase (se 7 (by rfl) ⟨77219, by rfl⟩ : syracuseStep 6589397 = 154439) (by norm_num)
theorem B17571725 : Blo 2055435 17571725 := bstep (se 3 (by rfl) ⟨3294698, by rfl⟩ : syracuseStep 17571725 = 6589397) B6589397
theorem B11714483 : Blo 2055435 11714483 := bstep (se 1 (by rfl) ⟨8785862, by rfl⟩ : syracuseStep 11714483 = 17571725) B17571725
theorem B7809655 : Blo 2055435 7809655 := bstep (se 1 (by rfl) ⟨5857241, by rfl⟩ : syracuseStep 7809655 = 11714483) B11714483
theorem B10412873 : Blo 2055435 10412873 := bstep (se 2 (by rfl) ⟨3904827, by rfl⟩ : syracuseStep 10412873 = 7809655) B7809655
theorem B6941915 : Blo 2055435 6941915 := bstep (se 1 (by rfl) ⟨5206436, by rfl⟩ : syracuseStep 6941915 = 10412873) B10412873
theorem B4627943 : Blo 2055435 4627943 := bstep (se 1 (by rfl) ⟨3470957, by rfl⟩ : syracuseStep 4627943 = 6941915) B6941915
theorem B3085295 : Blo 2055435 3085295 := bstep (se 1 (by rfl) ⟨2313971, by rfl⟩ : syracuseStep 3085295 = 4627943) B4627943
theorem B2056863 : Blo 2055435 2056863 := bstep (se 1 (by rfl) ⟨1542647, by rfl⟩ : syracuseStep 2056863 = 3085295) B3085295
theorem B3085301 : Blo 2055435 3085301 := bbase (se 5 (by rfl) ⟨144623, by rfl⟩ : syracuseStep 3085301 = 289247) (by norm_num)
theorem B2056867 : Blo 2055435 2056867 := bstep (se 1 (by rfl) ⟨1542650, by rfl⟩ : syracuseStep 2056867 = 3085301) B3085301
theorem B4392949 : Blo 2055435 4392949 := bbase (se 5 (by rfl) ⟨205919, by rfl⟩ : syracuseStep 4392949 = 411839) (by norm_num)
theorem B5857265 : Blo 2055435 5857265 := bstep (se 2 (by rfl) ⟨2196474, by rfl⟩ : syracuseStep 5857265 = 4392949) B4392949
theorem B3904843 : Blo 2055435 3904843 := bstep (se 1 (by rfl) ⟨2928632, by rfl⟩ : syracuseStep 3904843 = 5857265) B5857265
theorem B5206457 : Blo 2055435 5206457 := bstep (se 2 (by rfl) ⟨1952421, by rfl⟩ : syracuseStep 5206457 = 3904843) B3904843
theorem B3470971 : Blo 2055435 3470971 := bstep (se 1 (by rfl) ⟨2603228, by rfl⟩ : syracuseStep 3470971 = 5206457) B5206457
theorem B4627961 : Blo 2055435 4627961 := bstep (se 2 (by rfl) ⟨1735485, by rfl⟩ : syracuseStep 4627961 = 3470971) B3470971
theorem B3085307 : Blo 2055435 3085307 := bstep (se 1 (by rfl) ⟨2313980, by rfl⟩ : syracuseStep 3085307 = 4627961) B4627961
theorem B2056871 : Blo 2055435 2056871 := bstep (se 1 (by rfl) ⟨1542653, by rfl⟩ : syracuseStep 2056871 = 3085307) B3085307
theorem B2313985 : Blo 2055435 2313985 := bbase (se 2 (by rfl) ⟨867744, by rfl⟩ : syracuseStep 2313985 = 1735489) (by norm_num)
theorem B3085313 : Blo 2055435 3085313 := bstep (se 2 (by rfl) ⟨1156992, by rfl⟩ : syracuseStep 3085313 = 2313985) B2313985
theorem B2056875 : Blo 2055435 2056875 := bstep (se 1 (by rfl) ⟨1542656, by rfl⟩ : syracuseStep 2056875 = 3085313) B3085313
theorem B5206477 : Blo 2055435 5206477 := bbase (se 3 (by rfl) ⟨976214, by rfl⟩ : syracuseStep 5206477 = 1952429) (by norm_num)
theorem B6941969 : Blo 2055435 6941969 := bstep (se 2 (by rfl) ⟨2603238, by rfl⟩ : syracuseStep 6941969 = 5206477) B5206477
theorem B4627979 : Blo 2055435 4627979 := bstep (se 1 (by rfl) ⟨3470984, by rfl⟩ : syracuseStep 4627979 = 6941969) B6941969
theorem B3085319 : Blo 2055435 3085319 := bstep (se 1 (by rfl) ⟨2313989, by rfl⟩ : syracuseStep 3085319 = 4627979) B4627979
theorem B2056879 : Blo 2055435 2056879 := bstep (se 1 (by rfl) ⟨1542659, by rfl⟩ : syracuseStep 2056879 = 3085319) B3085319
theorem B3085325 : Blo 2055435 3085325 := bbase (se 3 (by rfl) ⟨578498, by rfl⟩ : syracuseStep 3085325 = 1156997) (by norm_num)
theorem B2056883 : Blo 2055435 2056883 := bstep (se 1 (by rfl) ⟨1542662, by rfl⟩ : syracuseStep 2056883 = 3085325) B3085325
theorem B4627997 : Blo 2055435 4627997 := bbase (se 3 (by rfl) ⟨867749, by rfl⟩ : syracuseStep 4627997 = 1735499) (by norm_num)
theorem B3085331 : Blo 2055435 3085331 := bstep (se 1 (by rfl) ⟨2313998, by rfl⟩ : syracuseStep 3085331 = 4627997) B4627997
theorem B2056887 : Blo 2055435 2056887 := bstep (se 1 (by rfl) ⟨1542665, by rfl⟩ : syracuseStep 2056887 = 3085331) B3085331
theorem B3471005 : Blo 2055435 3471005 := bbase (se 3 (by rfl) ⟨650813, by rfl⟩ : syracuseStep 3471005 = 1301627) (by norm_num)
theorem B2314003 : Blo 2055435 2314003 := bstep (se 1 (by rfl) ⟨1735502, by rfl⟩ : syracuseStep 2314003 = 3471005) B3471005
theorem B3085337 : Blo 2055435 3085337 := bstep (se 2 (by rfl) ⟨1157001, by rfl⟩ : syracuseStep 3085337 = 2314003) B2314003
theorem B2056891 : Blo 2055435 2056891 := bstep (se 1 (by rfl) ⟨1542668, by rfl⟩ : syracuseStep 2056891 = 3085337) B3085337
theorem B10555109 : Blo 2055435 10555109 := bbase (se 4 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 10555109 = 1979083) (by norm_num)
theorem B7036739 : Blo 2055435 7036739 := bstep (se 1 (by rfl) ⟨5277554, by rfl⟩ : syracuseStep 7036739 = 10555109) B10555109
theorem B4691159 : Blo 2055435 4691159 := bstep (se 1 (by rfl) ⟨3518369, by rfl⟩ : syracuseStep 4691159 = 7036739) B7036739
theorem B3127439 : Blo 2055435 3127439 := bstep (se 1 (by rfl) ⟨2345579, by rfl⟩ : syracuseStep 3127439 = 4691159) B4691159
theorem B2084959 : Blo 2055435 2084959 := bstep (se 1 (by rfl) ⟨1563719, by rfl⟩ : syracuseStep 2084959 = 3127439) B3127439
theorem B11119781 : Blo 2055435 11119781 := bstep (se 4 (by rfl) ⟨1042479, by rfl⟩ : syracuseStep 11119781 = 2084959) B2084959
theorem B29652749 : Blo 2055435 29652749 := bstep (se 3 (by rfl) ⟨5559890, by rfl⟩ : syracuseStep 29652749 = 11119781) B11119781
theorem B19768499 : Blo 2055435 19768499 := bstep (se 1 (by rfl) ⟨14826374, by rfl⟩ : syracuseStep 19768499 = 29652749) B29652749
theorem B13178999 : Blo 2055435 13178999 := bstep (se 1 (by rfl) ⟨9884249, by rfl⟩ : syracuseStep 13178999 = 19768499) B19768499
theorem B8785999 : Blo 2055435 8785999 := bstep (se 1 (by rfl) ⟨6589499, by rfl⟩ : syracuseStep 8785999 = 13178999) B13178999
theorem B11714665 : Blo 2055435 11714665 := bstep (se 2 (by rfl) ⟨4392999, by rfl⟩ : syracuseStep 11714665 = 8785999) B8785999
theorem B15619553 : Blo 2055435 15619553 := bstep (se 2 (by rfl) ⟨5857332, by rfl⟩ : syracuseStep 15619553 = 11714665) B11714665
theorem B10413035 : Blo 2055435 10413035 := bstep (se 1 (by rfl) ⟨7809776, by rfl⟩ : syracuseStep 10413035 = 15619553) B15619553
theorem B6942023 : Blo 2055435 6942023 := bstep (se 1 (by rfl) ⟨5206517, by rfl⟩ : syracuseStep 6942023 = 10413035) B10413035
theorem B4628015 : Blo 2055435 4628015 := bstep (se 1 (by rfl) ⟨3471011, by rfl⟩ : syracuseStep 4628015 = 6942023) B6942023
theorem B3085343 : Blo 2055435 3085343 := bstep (se 1 (by rfl) ⟨2314007, by rfl⟩ : syracuseStep 3085343 = 4628015) B4628015
theorem B2056895 : Blo 2055435 2056895 := bstep (se 1 (by rfl) ⟨1542671, by rfl⟩ : syracuseStep 2056895 = 3085343) B3085343
theorem B3085349 : Blo 2055435 3085349 := bbase (se 4 (by rfl) ⟨289251, by rfl⟩ : syracuseStep 3085349 = 578503) (by norm_num)
theorem B2056899 : Blo 2055435 2056899 := bstep (se 1 (by rfl) ⟨1542674, by rfl⟩ : syracuseStep 2056899 = 3085349) B3085349
theorem B2603269 : Blo 2055435 2603269 := bbase (se 4 (by rfl) ⟨244056, by rfl⟩ : syracuseStep 2603269 = 488113) (by norm_num)
theorem B3471025 : Blo 2055435 3471025 := bstep (se 2 (by rfl) ⟨1301634, by rfl⟩ : syracuseStep 3471025 = 2603269) B2603269
theorem B4628033 : Blo 2055435 4628033 := bstep (se 2 (by rfl) ⟨1735512, by rfl⟩ : syracuseStep 4628033 = 3471025) B3471025
theorem B3085355 : Blo 2055435 3085355 := bstep (se 1 (by rfl) ⟨2314016, by rfl⟩ : syracuseStep 3085355 = 4628033) B4628033
theorem B2056903 : Blo 2055435 2056903 := bstep (se 1 (by rfl) ⟨1542677, by rfl⟩ : syracuseStep 2056903 = 3085355) B3085355
theorem B2314021 : Blo 2055435 2314021 := bbase (se 4 (by rfl) ⟨216939, by rfl⟩ : syracuseStep 2314021 = 433879) (by norm_num)
theorem B3085361 : Blo 2055435 3085361 := bstep (se 2 (by rfl) ⟨1157010, by rfl⟩ : syracuseStep 3085361 = 2314021) B2314021
theorem B2056907 : Blo 2055435 2056907 := bstep (se 1 (by rfl) ⟨1542680, by rfl⟩ : syracuseStep 2056907 = 3085361) B3085361
theorem B8786069 : Blo 2055435 8786069 := bbase (se 6 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 8786069 = 411847) (by norm_num)
theorem B5857379 : Blo 2055435 5857379 := bstep (se 1 (by rfl) ⟨4393034, by rfl⟩ : syracuseStep 5857379 = 8786069) B8786069
theorem B3904919 : Blo 2055435 3904919 := bstep (se 1 (by rfl) ⟨2928689, by rfl⟩ : syracuseStep 3904919 = 5857379) B5857379
theorem B2603279 : Blo 2055435 2603279 := bstep (se 1 (by rfl) ⟨1952459, by rfl⟩ : syracuseStep 2603279 = 3904919) B3904919
theorem B6942077 : Blo 2055435 6942077 := bstep (se 3 (by rfl) ⟨1301639, by rfl⟩ : syracuseStep 6942077 = 2603279) B2603279
theorem B4628051 : Blo 2055435 4628051 := bstep (se 1 (by rfl) ⟨3471038, by rfl⟩ : syracuseStep 4628051 = 6942077) B6942077
theorem B3085367 : Blo 2055435 3085367 := bstep (se 1 (by rfl) ⟨2314025, by rfl⟩ : syracuseStep 3085367 = 4628051) B4628051
theorem B2056911 : Blo 2055435 2056911 := bstep (se 1 (by rfl) ⟨1542683, by rfl⟩ : syracuseStep 2056911 = 3085367) B3085367
theorem B3085373 : Blo 2055435 3085373 := bbase (se 3 (by rfl) ⟨578507, by rfl⟩ : syracuseStep 3085373 = 1157015) (by norm_num)
theorem B2056915 : Blo 2055435 2056915 := bstep (se 1 (by rfl) ⟨1542686, by rfl⟩ : syracuseStep 2056915 = 3085373) B3085373
theorem B4628069 : Blo 2055435 4628069 := bbase (se 4 (by rfl) ⟨433881, by rfl⟩ : syracuseStep 4628069 = 867763) (by norm_num)
theorem B3085379 : Blo 2055435 3085379 := bstep (se 1 (by rfl) ⟨2314034, by rfl⟩ : syracuseStep 3085379 = 4628069) B4628069
theorem B2056919 : Blo 2055435 2056919 := bstep (se 1 (by rfl) ⟨1542689, by rfl⟩ : syracuseStep 2056919 = 3085379) B3085379
theorem B5206589 : Blo 2055435 5206589 := bbase (se 3 (by rfl) ⟨976235, by rfl⟩ : syracuseStep 5206589 = 1952471) (by norm_num)
theorem B3471059 : Blo 2055435 3471059 := bstep (se 1 (by rfl) ⟨2603294, by rfl⟩ : syracuseStep 3471059 = 5206589) B5206589
theorem B2314039 : Blo 2055435 2314039 := bstep (se 1 (by rfl) ⟨1735529, by rfl⟩ : syracuseStep 2314039 = 3471059) B3471059
theorem B3085385 : Blo 2055435 3085385 := bstep (se 2 (by rfl) ⟨1157019, by rfl⟩ : syracuseStep 3085385 = 2314039) B2314039
theorem B2056923 : Blo 2055435 2056923 := bstep (se 1 (by rfl) ⟨1542692, by rfl⟩ : syracuseStep 2056923 = 3085385) B3085385
theorem B3904949 : Blo 2055435 3904949 := bbase (se 5 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 3904949 = 366089) (by norm_num)
theorem B10413197 : Blo 2055435 10413197 := bstep (se 3 (by rfl) ⟨1952474, by rfl⟩ : syracuseStep 10413197 = 3904949) B3904949
theorem B6942131 : Blo 2055435 6942131 := bstep (se 1 (by rfl) ⟨5206598, by rfl⟩ : syracuseStep 6942131 = 10413197) B10413197
theorem B4628087 : Blo 2055435 4628087 := bstep (se 1 (by rfl) ⟨3471065, by rfl⟩ : syracuseStep 4628087 = 6942131) B6942131
theorem B3085391 : Blo 2055435 3085391 := bstep (se 1 (by rfl) ⟨2314043, by rfl⟩ : syracuseStep 3085391 = 4628087) B4628087
theorem B2056927 : Blo 2055435 2056927 := bstep (se 1 (by rfl) ⟨1542695, by rfl⟩ : syracuseStep 2056927 = 3085391) B3085391
theorem B3085397 : Blo 2055435 3085397 := bbase (se 8 (by rfl) ⟨18078, by rfl⟩ : syracuseStep 3085397 = 36157) (by norm_num)
theorem B2056931 : Blo 2055435 2056931 := bstep (se 1 (by rfl) ⟨1542698, by rfl⟩ : syracuseStep 2056931 = 3085397) B3085397
theorem B4513781 : Blo 2055435 4513781 := bbase (se 5 (by rfl) ⟨211583, by rfl⟩ : syracuseStep 4513781 = 423167) (by norm_num)
theorem B3009187 : Blo 2055435 3009187 := bstep (se 1 (by rfl) ⟨2256890, by rfl⟩ : syracuseStep 3009187 = 4513781) B4513781
theorem B4012249 : Blo 2055435 4012249 := bstep (se 2 (by rfl) ⟨1504593, by rfl⟩ : syracuseStep 4012249 = 3009187) B3009187
theorem B5349665 : Blo 2055435 5349665 := bstep (se 2 (by rfl) ⟨2006124, by rfl⟩ : syracuseStep 5349665 = 4012249) B4012249
theorem B3566443 : Blo 2055435 3566443 := bstep (se 1 (by rfl) ⟨2674832, by rfl⟩ : syracuseStep 3566443 = 5349665) B5349665
theorem B4755257 : Blo 2055435 4755257 := bstep (se 2 (by rfl) ⟨1783221, by rfl⟩ : syracuseStep 4755257 = 3566443) B3566443
theorem B3170171 : Blo 2055435 3170171 := bstep (se 1 (by rfl) ⟨2377628, by rfl⟩ : syracuseStep 3170171 = 4755257) B4755257
theorem B2113447 : Blo 2055435 2113447 := bstep (se 1 (by rfl) ⟨1585085, by rfl⟩ : syracuseStep 2113447 = 3170171) B3170171
theorem B2817929 : Blo 2055435 2817929 := bstep (se 2 (by rfl) ⟨1056723, by rfl⟩ : syracuseStep 2817929 = 2113447) B2113447
theorem B7514477 : Blo 2055435 7514477 := bstep (se 3 (by rfl) ⟨1408964, by rfl⟩ : syracuseStep 7514477 = 2817929) B2817929
theorem B5009651 : Blo 2055435 5009651 := bstep (se 1 (by rfl) ⟨3757238, by rfl⟩ : syracuseStep 5009651 = 7514477) B7514477
theorem B3339767 : Blo 2055435 3339767 := bstep (se 1 (by rfl) ⟨2504825, by rfl⟩ : syracuseStep 3339767 = 5009651) B5009651
theorem B8906045 : Blo 2055435 8906045 := bstep (se 3 (by rfl) ⟨1669883, by rfl⟩ : syracuseStep 8906045 = 3339767) B3339767
theorem B23749453 : Blo 2055435 23749453 := bstep (se 3 (by rfl) ⟨4453022, by rfl⟩ : syracuseStep 23749453 = 8906045) B8906045
theorem B126663749 : Blo 2055435 126663749 := bstep (se 4 (by rfl) ⟨11874726, by rfl⟩ : syracuseStep 126663749 = 23749453) B23749453
theorem B84442499 : Blo 2055435 84442499 := bstep (se 1 (by rfl) ⟨63331874, by rfl⟩ : syracuseStep 84442499 = 126663749) B126663749
theorem B56294999 : Blo 2055435 56294999 := bstep (se 1 (by rfl) ⟨42221249, by rfl⟩ : syracuseStep 56294999 = 84442499) B84442499
theorem B37529999 : Blo 2055435 37529999 := bstep (se 1 (by rfl) ⟨28147499, by rfl⟩ : syracuseStep 37529999 = 56294999) B56294999
theorem B25019999 : Blo 2055435 25019999 := bstep (se 1 (by rfl) ⟨18764999, by rfl⟩ : syracuseStep 25019999 = 37529999) B37529999
theorem B16679999 : Blo 2055435 16679999 := bstep (se 1 (by rfl) ⟨12509999, by rfl⟩ : syracuseStep 16679999 = 25019999) B25019999
theorem B11119999 : Blo 2055435 11119999 := bstep (se 1 (by rfl) ⟨8339999, by rfl⟩ : syracuseStep 11119999 = 16679999) B16679999
theorem B14826665 : Blo 2055435 14826665 := bstep (se 2 (by rfl) ⟨5559999, by rfl⟩ : syracuseStep 14826665 = 11119999) B11119999
theorem B9884443 : Blo 2055435 9884443 := bstep (se 1 (by rfl) ⟨7413332, by rfl⟩ : syracuseStep 9884443 = 14826665) B14826665
theorem B13179257 : Blo 2055435 13179257 := bstep (se 2 (by rfl) ⟨4942221, by rfl⟩ : syracuseStep 13179257 = 9884443) B9884443
theorem B8786171 : Blo 2055435 8786171 := bstep (se 1 (by rfl) ⟨6589628, by rfl⟩ : syracuseStep 8786171 = 13179257) B13179257
theorem B5857447 : Blo 2055435 5857447 := bstep (se 1 (by rfl) ⟨4393085, by rfl⟩ : syracuseStep 5857447 = 8786171) B8786171
theorem B7809929 : Blo 2055435 7809929 := bstep (se 2 (by rfl) ⟨2928723, by rfl⟩ : syracuseStep 7809929 = 5857447) B5857447
theorem B5206619 : Blo 2055435 5206619 := bstep (se 1 (by rfl) ⟨3904964, by rfl⟩ : syracuseStep 5206619 = 7809929) B7809929
theorem B3471079 : Blo 2055435 3471079 := bstep (se 1 (by rfl) ⟨2603309, by rfl⟩ : syracuseStep 3471079 = 5206619) B5206619
theorem B4628105 : Blo 2055435 4628105 := bstep (se 2 (by rfl) ⟨1735539, by rfl⟩ : syracuseStep 4628105 = 3471079) B3471079
theorem B3085403 : Blo 2055435 3085403 := bstep (se 1 (by rfl) ⟨2314052, by rfl⟩ : syracuseStep 3085403 = 4628105) B4628105
theorem B2056935 : Blo 2055435 2056935 := bstep (se 1 (by rfl) ⟨1542701, by rfl⟩ : syracuseStep 2056935 = 3085403) B3085403
theorem B2314057 : Blo 2055435 2314057 := bbase (se 2 (by rfl) ⟨867771, by rfl⟩ : syracuseStep 2314057 = 1735543) (by norm_num)
theorem B3085409 : Blo 2055435 3085409 := bstep (se 2 (by rfl) ⟨1157028, by rfl⟩ : syracuseStep 3085409 = 2314057) B2314057
theorem B2056939 : Blo 2055435 2056939 := bstep (se 1 (by rfl) ⟨1542704, by rfl⟩ : syracuseStep 2056939 = 3085409) B3085409
theorem B2968693 : Blo 2055435 2968693 := bbase (se 5 (by rfl) ⟨139157, by rfl⟩ : syracuseStep 2968693 = 278315) (by norm_num)
theorem B63332117 : Blo 2055435 63332117 := bstep (se 6 (by rfl) ⟨1484346, by rfl⟩ : syracuseStep 63332117 = 2968693) B2968693
theorem B42221411 : Blo 2055435 42221411 := bstep (se 1 (by rfl) ⟨31666058, by rfl⟩ : syracuseStep 42221411 = 63332117) B63332117
theorem B28147607 : Blo 2055435 28147607 := bstep (se 1 (by rfl) ⟨21110705, by rfl⟩ : syracuseStep 28147607 = 42221411) B42221411
theorem B18765071 : Blo 2055435 18765071 := bstep (se 1 (by rfl) ⟨14073803, by rfl⟩ : syracuseStep 18765071 = 28147607) B28147607
theorem B12510047 : Blo 2055435 12510047 := bstep (se 1 (by rfl) ⟨9382535, by rfl⟩ : syracuseStep 12510047 = 18765071) B18765071
theorem B8340031 : Blo 2055435 8340031 := bstep (se 1 (by rfl) ⟨6255023, by rfl⟩ : syracuseStep 8340031 = 12510047) B12510047
theorem B11120041 : Blo 2055435 11120041 := bstep (se 2 (by rfl) ⟨4170015, by rfl⟩ : syracuseStep 11120041 = 8340031) B8340031
theorem B14826721 : Blo 2055435 14826721 := bstep (se 2 (by rfl) ⟨5560020, by rfl⟩ : syracuseStep 14826721 = 11120041) B11120041
theorem B19768961 : Blo 2055435 19768961 := bstep (se 2 (by rfl) ⟨7413360, by rfl⟩ : syracuseStep 19768961 = 14826721) B14826721
theorem B13179307 : Blo 2055435 13179307 := bstep (se 1 (by rfl) ⟨9884480, by rfl⟩ : syracuseStep 13179307 = 19768961) B19768961
theorem B17572409 : Blo 2055435 17572409 := bstep (se 2 (by rfl) ⟨6589653, by rfl⟩ : syracuseStep 17572409 = 13179307) B13179307
theorem B11714939 : Blo 2055435 11714939 := bstep (se 1 (by rfl) ⟨8786204, by rfl⟩ : syracuseStep 11714939 = 17572409) B17572409
theorem B7809959 : Blo 2055435 7809959 := bstep (se 1 (by rfl) ⟨5857469, by rfl⟩ : syracuseStep 7809959 = 11714939) B11714939
theorem B5206639 : Blo 2055435 5206639 := bstep (se 1 (by rfl) ⟨3904979, by rfl⟩ : syracuseStep 5206639 = 7809959) B7809959
theorem B6942185 : Blo 2055435 6942185 := bstep (se 2 (by rfl) ⟨2603319, by rfl⟩ : syracuseStep 6942185 = 5206639) B5206639
theorem B4628123 : Blo 2055435 4628123 := bstep (se 1 (by rfl) ⟨3471092, by rfl⟩ : syracuseStep 4628123 = 6942185) B6942185
theorem B3085415 : Blo 2055435 3085415 := bstep (se 1 (by rfl) ⟨2314061, by rfl⟩ : syracuseStep 3085415 = 4628123) B4628123
theorem B2056943 : Blo 2055435 2056943 := bstep (se 1 (by rfl) ⟨1542707, by rfl⟩ : syracuseStep 2056943 = 3085415) B3085415
theorem B3085421 : Blo 2055435 3085421 := bbase (se 3 (by rfl) ⟨578516, by rfl⟩ : syracuseStep 3085421 = 1157033) (by norm_num)
theorem B2056947 : Blo 2055435 2056947 := bstep (se 1 (by rfl) ⟨1542710, by rfl⟩ : syracuseStep 2056947 = 3085421) B3085421
theorem B4628141 : Blo 2055435 4628141 := bbase (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) (by norm_num)
theorem B3085427 : Blo 2055435 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B2056951 : Blo 2055435 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B4067029 : Blo 2055435 4067029 := bbase (se 7 (by rfl) ⟨47660, by rfl⟩ : syracuseStep 4067029 = 95321) (by norm_num)
theorem B21690821 : Blo 2055435 21690821 := bstep (se 4 (by rfl) ⟨2033514, by rfl⟩ : syracuseStep 21690821 = 4067029) B4067029
theorem B14460547 : Blo 2055435 14460547 := bstep (se 1 (by rfl) ⟨10845410, by rfl⟩ : syracuseStep 14460547 = 21690821) B21690821
theorem B19280729 : Blo 2055435 19280729 := bstep (se 2 (by rfl) ⟨7230273, by rfl⟩ : syracuseStep 19280729 = 14460547) B14460547
theorem B12853819 : Blo 2055435 12853819 := bstep (se 1 (by rfl) ⟨9640364, by rfl⟩ : syracuseStep 12853819 = 19280729) B19280729
theorem B17138425 : Blo 2055435 17138425 := bstep (se 2 (by rfl) ⟨6426909, by rfl⟩ : syracuseStep 17138425 = 12853819) B12853819
theorem B22851233 : Blo 2055435 22851233 := bstep (se 2 (by rfl) ⟨8569212, by rfl⟩ : syracuseStep 22851233 = 17138425) B17138425
theorem B15234155 : Blo 2055435 15234155 := bstep (se 1 (by rfl) ⟨11425616, by rfl⟩ : syracuseStep 15234155 = 22851233) B22851233
theorem B10156103 : Blo 2055435 10156103 := bstep (se 1 (by rfl) ⟨7617077, by rfl⟩ : syracuseStep 10156103 = 15234155) B15234155
theorem B6770735 : Blo 2055435 6770735 := bstep (se 1 (by rfl) ⟨5078051, by rfl⟩ : syracuseStep 6770735 = 10156103) B10156103
theorem B4513823 : Blo 2055435 4513823 := bstep (se 1 (by rfl) ⟨3385367, by rfl⟩ : syracuseStep 4513823 = 6770735) B6770735
theorem B3009215 : Blo 2055435 3009215 := bstep (se 1 (by rfl) ⟨2256911, by rfl⟩ : syracuseStep 3009215 = 4513823) B4513823
theorem B8024573 : Blo 2055435 8024573 := bstep (se 3 (by rfl) ⟨1504607, by rfl⟩ : syracuseStep 8024573 = 3009215) B3009215
theorem B5349715 : Blo 2055435 5349715 := bstep (se 1 (by rfl) ⟨4012286, by rfl⟩ : syracuseStep 5349715 = 8024573) B8024573
theorem B28531813 : Blo 2055435 28531813 := bstep (se 4 (by rfl) ⟨2674857, by rfl⟩ : syracuseStep 28531813 = 5349715) B5349715
theorem B38042417 : Blo 2055435 38042417 := bstep (se 2 (by rfl) ⟨14265906, by rfl⟩ : syracuseStep 38042417 = 28531813) B28531813
theorem B101446445 : Blo 2055435 101446445 := bstep (se 3 (by rfl) ⟨19021208, by rfl⟩ : syracuseStep 101446445 = 38042417) B38042417
theorem B67630963 : Blo 2055435 67630963 := bstep (se 1 (by rfl) ⟨50723222, by rfl⟩ : syracuseStep 67630963 = 101446445) B101446445
theorem B90174617 : Blo 2055435 90174617 := bstep (se 2 (by rfl) ⟨33815481, by rfl⟩ : syracuseStep 90174617 = 67630963) B67630963
theorem B60116411 : Blo 2055435 60116411 := bstep (se 1 (by rfl) ⟨45087308, by rfl⟩ : syracuseStep 60116411 = 90174617) B90174617
theorem B40077607 : Blo 2055435 40077607 := bstep (se 1 (by rfl) ⟨30058205, by rfl⟩ : syracuseStep 40077607 = 60116411) B60116411
theorem B53436809 : Blo 2055435 53436809 := bstep (se 2 (by rfl) ⟨20038803, by rfl⟩ : syracuseStep 53436809 = 40077607) B40077607
theorem B35624539 : Blo 2055435 35624539 := bstep (se 1 (by rfl) ⟨26718404, by rfl⟩ : syracuseStep 35624539 = 53436809) B53436809
theorem B47499385 : Blo 2055435 47499385 := bstep (se 2 (by rfl) ⟨17812269, by rfl⟩ : syracuseStep 47499385 = 35624539) B35624539
theorem B63332513 : Blo 2055435 63332513 := bstep (se 2 (by rfl) ⟨23749692, by rfl⟩ : syracuseStep 63332513 = 47499385) B47499385
theorem B42221675 : Blo 2055435 42221675 := bstep (se 1 (by rfl) ⟨31666256, by rfl⟩ : syracuseStep 42221675 = 63332513) B63332513
theorem B28147783 : Blo 2055435 28147783 := bstep (se 1 (by rfl) ⟨21110837, by rfl⟩ : syracuseStep 28147783 = 42221675) B42221675
theorem B37530377 : Blo 2055435 37530377 := bstep (se 2 (by rfl) ⟨14073891, by rfl⟩ : syracuseStep 37530377 = 28147783) B28147783
theorem B25020251 : Blo 2055435 25020251 := bstep (se 1 (by rfl) ⟨18765188, by rfl⟩ : syracuseStep 25020251 = 37530377) B37530377
theorem B16680167 : Blo 2055435 16680167 := bstep (se 1 (by rfl) ⟨12510125, by rfl⟩ : syracuseStep 16680167 = 25020251) B25020251
theorem B11120111 : Blo 2055435 11120111 := bstep (se 1 (by rfl) ⟨8340083, by rfl⟩ : syracuseStep 11120111 = 16680167) B16680167
theorem B7413407 : Blo 2055435 7413407 := bstep (se 1 (by rfl) ⟨5560055, by rfl⟩ : syracuseStep 7413407 = 11120111) B11120111
theorem B4942271 : Blo 2055435 4942271 := bstep (se 1 (by rfl) ⟨3706703, by rfl⟩ : syracuseStep 4942271 = 7413407) B7413407
theorem B3294847 : Blo 2055435 3294847 := bstep (se 1 (by rfl) ⟨2471135, by rfl⟩ : syracuseStep 3294847 = 4942271) B4942271
theorem B4393129 : Blo 2055435 4393129 := bstep (se 2 (by rfl) ⟨1647423, by rfl⟩ : syracuseStep 4393129 = 3294847) B3294847
theorem B5857505 : Blo 2055435 5857505 := bstep (se 2 (by rfl) ⟨2196564, by rfl⟩ : syracuseStep 5857505 = 4393129) B4393129
theorem B3905003 : Blo 2055435 3905003 := bstep (se 1 (by rfl) ⟨2928752, by rfl⟩ : syracuseStep 3905003 = 5857505) B5857505
theorem B2603335 : Blo 2055435 2603335 := bstep (se 1 (by rfl) ⟨1952501, by rfl⟩ : syracuseStep 2603335 = 3905003) B3905003
theorem B3471113 : Blo 2055435 3471113 := bstep (se 2 (by rfl) ⟨1301667, by rfl⟩ : syracuseStep 3471113 = 2603335) B2603335
theorem B2314075 : Blo 2055435 2314075 := bstep (se 1 (by rfl) ⟨1735556, by rfl⟩ : syracuseStep 2314075 = 3471113) B3471113
theorem B3085433 : Blo 2055435 3085433 := bstep (se 2 (by rfl) ⟨1157037, by rfl⟩ : syracuseStep 3085433 = 2314075) B2314075
theorem B2056955 : Blo 2055435 2056955 := bstep (se 1 (by rfl) ⟨1542716, by rfl⟩ : syracuseStep 2056955 = 3085433) B3085433
theorem B14460565 : Blo 2055435 14460565 := bbase (se 6 (by rfl) ⟨338919, by rfl⟩ : syracuseStep 14460565 = 677839) (by norm_num)
theorem B19280753 : Blo 2055435 19280753 := bstep (se 2 (by rfl) ⟨7230282, by rfl⟩ : syracuseStep 19280753 = 14460565) B14460565
theorem B12853835 : Blo 2055435 12853835 := bstep (se 1 (by rfl) ⟨9640376, by rfl⟩ : syracuseStep 12853835 = 19280753) B19280753
theorem B8569223 : Blo 2055435 8569223 := bstep (se 1 (by rfl) ⟨6426917, by rfl⟩ : syracuseStep 8569223 = 12853835) B12853835
theorem B5712815 : Blo 2055435 5712815 := bstep (se 1 (by rfl) ⟨4284611, by rfl⟩ : syracuseStep 5712815 = 8569223) B8569223
theorem B3808543 : Blo 2055435 3808543 := bstep (se 1 (by rfl) ⟨2856407, by rfl⟩ : syracuseStep 3808543 = 5712815) B5712815
theorem B5078057 : Blo 2055435 5078057 := bstep (se 2 (by rfl) ⟨1904271, by rfl⟩ : syracuseStep 5078057 = 3808543) B3808543
theorem B13541485 : Blo 2055435 13541485 := bstep (se 3 (by rfl) ⟨2539028, by rfl⟩ : syracuseStep 13541485 = 5078057) B5078057
theorem B18055313 : Blo 2055435 18055313 := bstep (se 2 (by rfl) ⟨6770742, by rfl⟩ : syracuseStep 18055313 = 13541485) B13541485
theorem B770360021 : Blo 2055435 770360021 := bstep (se 7 (by rfl) ⟨9027656, by rfl⟩ : syracuseStep 770360021 = 18055313) B18055313
theorem B513573347 : Blo 2055435 513573347 := bstep (se 1 (by rfl) ⟨385180010, by rfl⟩ : syracuseStep 513573347 = 770360021) B770360021
theorem B342382231 : Blo 2055435 342382231 := bstep (se 1 (by rfl) ⟨256786673, by rfl⟩ : syracuseStep 342382231 = 513573347) B513573347
theorem B456509641 : Blo 2055435 456509641 := bstep (se 2 (by rfl) ⟨171191115, by rfl⟩ : syracuseStep 456509641 = 342382231) B342382231
theorem B608679521 : Blo 2055435 608679521 := bstep (se 2 (by rfl) ⟨228254820, by rfl⟩ : syracuseStep 608679521 = 456509641) B456509641
theorem B405786347 : Blo 2055435 405786347 := bstep (se 1 (by rfl) ⟨304339760, by rfl⟩ : syracuseStep 405786347 = 608679521) B608679521
theorem B270524231 : Blo 2055435 270524231 := bstep (se 1 (by rfl) ⟨202893173, by rfl⟩ : syracuseStep 270524231 = 405786347) B405786347
theorem B180349487 : Blo 2055435 180349487 := bstep (se 1 (by rfl) ⟨135262115, by rfl⟩ : syracuseStep 180349487 = 270524231) B270524231
theorem B120232991 : Blo 2055435 120232991 := bstep (se 1 (by rfl) ⟨90174743, by rfl⟩ : syracuseStep 120232991 = 180349487) B180349487
theorem B80155327 : Blo 2055435 80155327 := bstep (se 1 (by rfl) ⟨60116495, by rfl⟩ : syracuseStep 80155327 = 120232991) B120232991
theorem B106873769 : Blo 2055435 106873769 := bstep (se 2 (by rfl) ⟨40077663, by rfl⟩ : syracuseStep 106873769 = 80155327) B80155327
theorem B71249179 : Blo 2055435 71249179 := bstep (se 1 (by rfl) ⟨53436884, by rfl⟩ : syracuseStep 71249179 = 106873769) B106873769
theorem B94998905 : Blo 2055435 94998905 := bstep (se 2 (by rfl) ⟨35624589, by rfl⟩ : syracuseStep 94998905 = 71249179) B71249179
theorem B63332603 : Blo 2055435 63332603 := bstep (se 1 (by rfl) ⟨47499452, by rfl⟩ : syracuseStep 63332603 = 94998905) B94998905
theorem B42221735 : Blo 2055435 42221735 := bstep (se 1 (by rfl) ⟨31666301, by rfl⟩ : syracuseStep 42221735 = 63332603) B63332603
theorem B28147823 : Blo 2055435 28147823 := bstep (se 1 (by rfl) ⟨21110867, by rfl⟩ : syracuseStep 28147823 = 42221735) B42221735
theorem B18765215 : Blo 2055435 18765215 := bstep (se 1 (by rfl) ⟨14073911, by rfl⟩ : syracuseStep 18765215 = 28147823) B28147823
theorem B12510143 : Blo 2055435 12510143 := bstep (se 1 (by rfl) ⟨9382607, by rfl⟩ : syracuseStep 12510143 = 18765215) B18765215
theorem B8340095 : Blo 2055435 8340095 := bstep (se 1 (by rfl) ⟨6255071, by rfl⟩ : syracuseStep 8340095 = 12510143) B12510143
theorem B22240253 : Blo 2055435 22240253 := bstep (se 3 (by rfl) ⟨4170047, by rfl⟩ : syracuseStep 22240253 = 8340095) B8340095
theorem B14826835 : Blo 2055435 14826835 := bstep (se 1 (by rfl) ⟨11120126, by rfl⟩ : syracuseStep 14826835 = 22240253) B22240253
theorem B19769113 : Blo 2055435 19769113 := bstep (se 2 (by rfl) ⟨7413417, by rfl⟩ : syracuseStep 19769113 = 14826835) B14826835
theorem B26358817 : Blo 2055435 26358817 := bstep (se 2 (by rfl) ⟨9884556, by rfl⟩ : syracuseStep 26358817 = 19769113) B19769113
theorem B35145089 : Blo 2055435 35145089 := bstep (se 2 (by rfl) ⟨13179408, by rfl⟩ : syracuseStep 35145089 = 26358817) B26358817
theorem B23430059 : Blo 2055435 23430059 := bstep (se 1 (by rfl) ⟨17572544, by rfl⟩ : syracuseStep 23430059 = 35145089) B35145089
theorem B15620039 : Blo 2055435 15620039 := bstep (se 1 (by rfl) ⟨11715029, by rfl⟩ : syracuseStep 15620039 = 23430059) B23430059
theorem B10413359 : Blo 2055435 10413359 := bstep (se 1 (by rfl) ⟨7810019, by rfl⟩ : syracuseStep 10413359 = 15620039) B15620039
theorem B6942239 : Blo 2055435 6942239 := bstep (se 1 (by rfl) ⟨5206679, by rfl⟩ : syracuseStep 6942239 = 10413359) B10413359
theorem B4628159 : Blo 2055435 4628159 := bstep (se 1 (by rfl) ⟨3471119, by rfl⟩ : syracuseStep 4628159 = 6942239) B6942239
theorem B3085439 : Blo 2055435 3085439 := bstep (se 1 (by rfl) ⟨2314079, by rfl⟩ : syracuseStep 3085439 = 4628159) B4628159
theorem B2056959 : Blo 2055435 2056959 := bstep (se 1 (by rfl) ⟨1542719, by rfl⟩ : syracuseStep 2056959 = 3085439) B3085439
theorem B3085445 : Blo 2055435 3085445 := bbase (se 4 (by rfl) ⟨289260, by rfl⟩ : syracuseStep 3085445 = 578521) (by norm_num)
theorem B2056963 : Blo 2055435 2056963 := bstep (se 1 (by rfl) ⟨1542722, by rfl⟩ : syracuseStep 2056963 = 3085445) B3085445
theorem B3471133 : Blo 2055435 3471133 := bbase (se 3 (by rfl) ⟨650837, by rfl⟩ : syracuseStep 3471133 = 1301675) (by norm_num)
theorem B4628177 : Blo 2055435 4628177 := bstep (se 2 (by rfl) ⟨1735566, by rfl⟩ : syracuseStep 4628177 = 3471133) B3471133
theorem B3085451 : Blo 2055435 3085451 := bstep (se 1 (by rfl) ⟨2314088, by rfl⟩ : syracuseStep 3085451 = 4628177) B4628177
theorem B2056967 : Blo 2055435 2056967 := bstep (se 1 (by rfl) ⟨1542725, by rfl⟩ : syracuseStep 2056967 = 3085451) B3085451
theorem B2314093 : Blo 2055435 2314093 := bbase (se 3 (by rfl) ⟨433892, by rfl⟩ : syracuseStep 2314093 = 867785) (by norm_num)
theorem B3085457 : Blo 2055435 3085457 := bstep (se 2 (by rfl) ⟨1157046, by rfl⟩ : syracuseStep 3085457 = 2314093) B2314093
theorem B2056971 : Blo 2055435 2056971 := bstep (se 1 (by rfl) ⟨1542728, by rfl⟩ : syracuseStep 2056971 = 3085457) B3085457
theorem B6942293 : Blo 2055435 6942293 := bbase (se 8 (by rfl) ⟨40677, by rfl⟩ : syracuseStep 6942293 = 81355) (by norm_num)
theorem B4628195 : Blo 2055435 4628195 := bstep (se 1 (by rfl) ⟨3471146, by rfl⟩ : syracuseStep 4628195 = 6942293) B6942293
theorem B3085463 : Blo 2055435 3085463 := bstep (se 1 (by rfl) ⟨2314097, by rfl⟩ : syracuseStep 3085463 = 4628195) B4628195
theorem B2056975 : Blo 2055435 2056975 := bstep (se 1 (by rfl) ⟨1542731, by rfl⟩ : syracuseStep 2056975 = 3085463) B3085463
theorem B3085469 : Blo 2055435 3085469 := bbase (se 3 (by rfl) ⟨578525, by rfl⟩ : syracuseStep 3085469 = 1157051) (by norm_num)
theorem B2056979 : Blo 2055435 2056979 := bstep (se 1 (by rfl) ⟨1542734, by rfl⟩ : syracuseStep 2056979 = 3085469) B3085469
theorem B4628213 : Blo 2055435 4628213 := bbase (se 5 (by rfl) ⟨216947, by rfl⟩ : syracuseStep 4628213 = 433895) (by norm_num)
theorem B3085475 : Blo 2055435 3085475 := bstep (se 1 (by rfl) ⟨2314106, by rfl⟩ : syracuseStep 3085475 = 4628213) B4628213
theorem B2056983 : Blo 2055435 2056983 := bstep (se 1 (by rfl) ⟨1542737, by rfl⟩ : syracuseStep 2056983 = 3085475) B3085475
theorem B9884693 : Blo 2055435 9884693 := bbase (se 6 (by rfl) ⟨231672, by rfl⟩ : syracuseStep 9884693 = 463345) (by norm_num)
theorem B26359181 : Blo 2055435 26359181 := bstep (se 3 (by rfl) ⟨4942346, by rfl⟩ : syracuseStep 26359181 = 9884693) B9884693
theorem B17572787 : Blo 2055435 17572787 := bstep (se 1 (by rfl) ⟨13179590, by rfl⟩ : syracuseStep 17572787 = 26359181) B26359181
theorem B11715191 : Blo 2055435 11715191 := bstep (se 1 (by rfl) ⟨8786393, by rfl⟩ : syracuseStep 11715191 = 17572787) B17572787
theorem B7810127 : Blo 2055435 7810127 := bstep (se 1 (by rfl) ⟨5857595, by rfl⟩ : syracuseStep 7810127 = 11715191) B11715191
theorem B5206751 : Blo 2055435 5206751 := bstep (se 1 (by rfl) ⟨3905063, by rfl⟩ : syracuseStep 5206751 = 7810127) B7810127
theorem B3471167 : Blo 2055435 3471167 := bstep (se 1 (by rfl) ⟨2603375, by rfl⟩ : syracuseStep 3471167 = 5206751) B5206751
theorem B2314111 : Blo 2055435 2314111 := bstep (se 1 (by rfl) ⟨1735583, by rfl⟩ : syracuseStep 2314111 = 3471167) B3471167
theorem B3085481 : Blo 2055435 3085481 := bstep (se 2 (by rfl) ⟨1157055, by rfl⟩ : syracuseStep 3085481 = 2314111) B2314111
theorem B2056987 : Blo 2055435 2056987 := bstep (se 1 (by rfl) ⟨1542740, by rfl⟩ : syracuseStep 2056987 = 3085481) B3085481
theorem B4393205 : Blo 2055435 4393205 := bbase (se 5 (by rfl) ⟨205931, by rfl⟩ : syracuseStep 4393205 = 411863) (by norm_num)
theorem B2928803 : Blo 2055435 2928803 := bstep (se 1 (by rfl) ⟨2196602, by rfl⟩ : syracuseStep 2928803 = 4393205) B4393205
theorem B7810141 : Blo 2055435 7810141 := bstep (se 3 (by rfl) ⟨1464401, by rfl⟩ : syracuseStep 7810141 = 2928803) B2928803
theorem B10413521 : Blo 2055435 10413521 := bstep (se 2 (by rfl) ⟨3905070, by rfl⟩ : syracuseStep 10413521 = 7810141) B7810141
theorem B6942347 : Blo 2055435 6942347 := bstep (se 1 (by rfl) ⟨5206760, by rfl⟩ : syracuseStep 6942347 = 10413521) B10413521
theorem B4628231 : Blo 2055435 4628231 := bstep (se 1 (by rfl) ⟨3471173, by rfl⟩ : syracuseStep 4628231 = 6942347) B6942347
theorem B3085487 : Blo 2055435 3085487 := bstep (se 1 (by rfl) ⟨2314115, by rfl⟩ : syracuseStep 3085487 = 4628231) B4628231
theorem B2056991 : Blo 2055435 2056991 := bstep (se 1 (by rfl) ⟨1542743, by rfl⟩ : syracuseStep 2056991 = 3085487) B3085487
theorem B3085493 : Blo 2055435 3085493 := bbase (se 5 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 3085493 = 289265) (by norm_num)
theorem B2056995 : Blo 2055435 2056995 := bstep (se 1 (by rfl) ⟨1542746, by rfl⟩ : syracuseStep 2056995 = 3085493) B3085493
theorem B5206781 : Blo 2055435 5206781 := bbase (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) (by norm_num)
theorem B3471187 : Blo 2055435 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B4628249 : Blo 2055435 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B3085499 : Blo 2055435 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B2056999 : Blo 2055435 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B2314129 : Blo 2055435 2314129 := bbase (se 2 (by rfl) ⟨867798, by rfl⟩ : syracuseStep 2314129 = 1735597) (by norm_num)
theorem B3085505 : Blo 2055435 3085505 := bstep (se 2 (by rfl) ⟨1157064, by rfl⟩ : syracuseStep 3085505 = 2314129) B2314129
theorem B2057003 : Blo 2055435 2057003 := bstep (se 1 (by rfl) ⟨1542752, by rfl⟩ : syracuseStep 2057003 = 3085505) B3085505
theorem B3905101 : Blo 2055435 3905101 := bbase (se 3 (by rfl) ⟨732206, by rfl⟩ : syracuseStep 3905101 = 1464413) (by norm_num)
theorem B5206801 : Blo 2055435 5206801 := bstep (se 2 (by rfl) ⟨1952550, by rfl⟩ : syracuseStep 5206801 = 3905101) B3905101
theorem B6942401 : Blo 2055435 6942401 := bstep (se 2 (by rfl) ⟨2603400, by rfl⟩ : syracuseStep 6942401 = 5206801) B5206801
theorem B4628267 : Blo 2055435 4628267 := bstep (se 1 (by rfl) ⟨3471200, by rfl⟩ : syracuseStep 4628267 = 6942401) B6942401
theorem B3085511 : Blo 2055435 3085511 := bstep (se 1 (by rfl) ⟨2314133, by rfl⟩ : syracuseStep 3085511 = 4628267) B4628267
theorem B2057007 : Blo 2055435 2057007 := bstep (se 1 (by rfl) ⟨1542755, by rfl⟩ : syracuseStep 2057007 = 3085511) B3085511
theorem B3085517 : Blo 2055435 3085517 := bbase (se 3 (by rfl) ⟨578534, by rfl⟩ : syracuseStep 3085517 = 1157069) (by norm_num)
theorem B2057011 : Blo 2055435 2057011 := bstep (se 1 (by rfl) ⟨1542758, by rfl⟩ : syracuseStep 2057011 = 3085517) B3085517
theorem B4628285 : Blo 2055435 4628285 := bbase (se 3 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 4628285 = 1735607) (by norm_num)
theorem B3085523 : Blo 2055435 3085523 := bstep (se 1 (by rfl) ⟨2314142, by rfl⟩ : syracuseStep 3085523 = 4628285) B4628285
theorem B2057015 : Blo 2055435 2057015 := bstep (se 1 (by rfl) ⟨1542761, by rfl⟩ : syracuseStep 2057015 = 3085523) B3085523
theorem B3471221 : Blo 2055435 3471221 := bbase (se 5 (by rfl) ⟨162713, by rfl⟩ : syracuseStep 3471221 = 325427) (by norm_num)
theorem B2314147 : Blo 2055435 2314147 := bstep (se 1 (by rfl) ⟨1735610, by rfl⟩ : syracuseStep 2314147 = 3471221) B3471221
theorem B3085529 : Blo 2055435 3085529 := bstep (se 2 (by rfl) ⟨1157073, by rfl⟩ : syracuseStep 3085529 = 2314147) B2314147
theorem B2057019 : Blo 2055435 2057019 := bstep (se 1 (by rfl) ⟨1542764, by rfl⟩ : syracuseStep 2057019 = 3085529) B3085529
theorem B6255269 : Blo 2055435 6255269 := bbase (se 4 (by rfl) ⟨586431, by rfl⟩ : syracuseStep 6255269 = 1172863) (by norm_num)
theorem B4170179 : Blo 2055435 4170179 := bstep (se 1 (by rfl) ⟨3127634, by rfl⟩ : syracuseStep 4170179 = 6255269) B6255269
theorem B2780119 : Blo 2055435 2780119 := bstep (se 1 (by rfl) ⟨2085089, by rfl⟩ : syracuseStep 2780119 = 4170179) B4170179
theorem B3706825 : Blo 2055435 3706825 := bstep (se 2 (by rfl) ⟨1390059, by rfl⟩ : syracuseStep 3706825 = 2780119) B2780119
theorem B4942433 : Blo 2055435 4942433 := bstep (se 2 (by rfl) ⟨1853412, by rfl⟩ : syracuseStep 4942433 = 3706825) B3706825
theorem B3294955 : Blo 2055435 3294955 := bstep (se 1 (by rfl) ⟨2471216, by rfl⟩ : syracuseStep 3294955 = 4942433) B4942433
theorem B4393273 : Blo 2055435 4393273 := bstep (se 2 (by rfl) ⟨1647477, by rfl⟩ : syracuseStep 4393273 = 3294955) B3294955
theorem B5857697 : Blo 2055435 5857697 := bstep (se 2 (by rfl) ⟨2196636, by rfl⟩ : syracuseStep 5857697 = 4393273) B4393273
theorem B15620525 : Blo 2055435 15620525 := bstep (se 3 (by rfl) ⟨2928848, by rfl⟩ : syracuseStep 15620525 = 5857697) B5857697
theorem B10413683 : Blo 2055435 10413683 := bstep (se 1 (by rfl) ⟨7810262, by rfl⟩ : syracuseStep 10413683 = 15620525) B15620525
theorem B6942455 : Blo 2055435 6942455 := bstep (se 1 (by rfl) ⟨5206841, by rfl⟩ : syracuseStep 6942455 = 10413683) B10413683
theorem B4628303 : Blo 2055435 4628303 := bstep (se 1 (by rfl) ⟨3471227, by rfl⟩ : syracuseStep 4628303 = 6942455) B6942455
theorem B3085535 : Blo 2055435 3085535 := bstep (se 1 (by rfl) ⟨2314151, by rfl⟩ : syracuseStep 3085535 = 4628303) B4628303
theorem B2057023 : Blo 2055435 2057023 := bstep (se 1 (by rfl) ⟨1542767, by rfl⟩ : syracuseStep 2057023 = 3085535) B3085535
theorem B3085541 : Blo 2055435 3085541 := bbase (se 4 (by rfl) ⟨289269, by rfl⟩ : syracuseStep 3085541 = 578539) (by norm_num)
theorem B2057027 : Blo 2055435 2057027 := bstep (se 1 (by rfl) ⟨1542770, by rfl⟩ : syracuseStep 2057027 = 3085541) B3085541
theorem B4942453 : Blo 2055435 4942453 := bbase (se 5 (by rfl) ⟨231677, by rfl⟩ : syracuseStep 4942453 = 463355) (by norm_num)
theorem B6589937 : Blo 2055435 6589937 := bstep (se 2 (by rfl) ⟨2471226, by rfl⟩ : syracuseStep 6589937 = 4942453) B4942453
theorem B4393291 : Blo 2055435 4393291 := bstep (se 1 (by rfl) ⟨3294968, by rfl⟩ : syracuseStep 4393291 = 6589937) B6589937
theorem B5857721 : Blo 2055435 5857721 := bstep (se 2 (by rfl) ⟨2196645, by rfl⟩ : syracuseStep 5857721 = 4393291) B4393291
theorem B3905147 : Blo 2055435 3905147 := bstep (se 1 (by rfl) ⟨2928860, by rfl⟩ : syracuseStep 3905147 = 5857721) B5857721
theorem B2603431 : Blo 2055435 2603431 := bstep (se 1 (by rfl) ⟨1952573, by rfl⟩ : syracuseStep 2603431 = 3905147) B3905147
theorem B3471241 : Blo 2055435 3471241 := bstep (se 2 (by rfl) ⟨1301715, by rfl⟩ : syracuseStep 3471241 = 2603431) B2603431
theorem B4628321 : Blo 2055435 4628321 := bstep (se 2 (by rfl) ⟨1735620, by rfl⟩ : syracuseStep 4628321 = 3471241) B3471241
theorem B3085547 : Blo 2055435 3085547 := bstep (se 1 (by rfl) ⟨2314160, by rfl⟩ : syracuseStep 3085547 = 4628321) B4628321
theorem B2057031 : Blo 2055435 2057031 := bstep (se 1 (by rfl) ⟨1542773, by rfl⟩ : syracuseStep 2057031 = 3085547) B3085547
theorem B2314165 : Blo 2055435 2314165 := bbase (se 5 (by rfl) ⟨108476, by rfl⟩ : syracuseStep 2314165 = 216953) (by norm_num)
theorem B3085553 : Blo 2055435 3085553 := bstep (se 2 (by rfl) ⟨1157082, by rfl⟩ : syracuseStep 3085553 = 2314165) B2314165
theorem B2057035 : Blo 2055435 2057035 := bstep (se 1 (by rfl) ⟨1542776, by rfl⟩ : syracuseStep 2057035 = 3085553) B3085553
theorem B2603441 : Blo 2055435 2603441 := bbase (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) (by norm_num)
theorem B6942509 : Blo 2055435 6942509 := bstep (se 3 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 6942509 = 2603441) B2603441
theorem B4628339 : Blo 2055435 4628339 := bstep (se 1 (by rfl) ⟨3471254, by rfl⟩ : syracuseStep 4628339 = 6942509) B6942509
theorem B3085559 : Blo 2055435 3085559 := bstep (se 1 (by rfl) ⟨2314169, by rfl⟩ : syracuseStep 3085559 = 4628339) B4628339
theorem B2057039 : Blo 2055435 2057039 := bstep (se 1 (by rfl) ⟨1542779, by rfl⟩ : syracuseStep 2057039 = 3085559) B3085559
theorem B3085565 : Blo 2055435 3085565 := bbase (se 3 (by rfl) ⟨578543, by rfl⟩ : syracuseStep 3085565 = 1157087) (by norm_num)
theorem B2057043 : Blo 2055435 2057043 := bstep (se 1 (by rfl) ⟨1542782, by rfl⟩ : syracuseStep 2057043 = 3085565) B3085565
theorem B4628357 : Blo 2055435 4628357 := bbase (se 4 (by rfl) ⟨433908, by rfl⟩ : syracuseStep 4628357 = 867817) (by norm_num)
theorem B3085571 : Blo 2055435 3085571 := bstep (se 1 (by rfl) ⟨2314178, by rfl⟩ : syracuseStep 3085571 = 4628357) B4628357
theorem B2057047 : Blo 2055435 2057047 := bstep (se 1 (by rfl) ⟨1542785, by rfl⟩ : syracuseStep 2057047 = 3085571) B3085571
theorem B3706877 : Blo 2055435 3706877 := bbase (se 3 (by rfl) ⟨695039, by rfl⟩ : syracuseStep 3706877 = 1390079) (by norm_num)
theorem B2471251 : Blo 2055435 2471251 := bstep (se 1 (by rfl) ⟨1853438, by rfl⟩ : syracuseStep 2471251 = 3706877) B3706877
theorem B3295001 : Blo 2055435 3295001 := bstep (se 2 (by rfl) ⟨1235625, by rfl⟩ : syracuseStep 3295001 = 2471251) B2471251
theorem B2196667 : Blo 2055435 2196667 := bstep (se 1 (by rfl) ⟨1647500, by rfl⟩ : syracuseStep 2196667 = 3295001) B3295001
theorem B2928889 : Blo 2055435 2928889 := bstep (se 2 (by rfl) ⟨1098333, by rfl⟩ : syracuseStep 2928889 = 2196667) B2196667
theorem B3905185 : Blo 2055435 3905185 := bstep (se 2 (by rfl) ⟨1464444, by rfl⟩ : syracuseStep 3905185 = 2928889) B2928889
theorem B5206913 : Blo 2055435 5206913 := bstep (se 2 (by rfl) ⟨1952592, by rfl⟩ : syracuseStep 5206913 = 3905185) B3905185
theorem B3471275 : Blo 2055435 3471275 := bstep (se 1 (by rfl) ⟨2603456, by rfl⟩ : syracuseStep 3471275 = 5206913) B5206913
theorem B2314183 : Blo 2055435 2314183 := bstep (se 1 (by rfl) ⟨1735637, by rfl⟩ : syracuseStep 2314183 = 3471275) B3471275
theorem B3085577 : Blo 2055435 3085577 := bstep (se 2 (by rfl) ⟨1157091, by rfl⟩ : syracuseStep 3085577 = 2314183) B2314183
theorem B2057051 : Blo 2055435 2057051 := bstep (se 1 (by rfl) ⟨1542788, by rfl⟩ : syracuseStep 2057051 = 3085577) B3085577
theorem B10413845 : Blo 2055435 10413845 := bbase (se 6 (by rfl) ⟨244074, by rfl⟩ : syracuseStep 10413845 = 488149) (by norm_num)
theorem B6942563 : Blo 2055435 6942563 := bstep (se 1 (by rfl) ⟨5206922, by rfl⟩ : syracuseStep 6942563 = 10413845) B10413845
theorem B4628375 : Blo 2055435 4628375 := bstep (se 1 (by rfl) ⟨3471281, by rfl⟩ : syracuseStep 4628375 = 6942563) B6942563
theorem B3085583 : Blo 2055435 3085583 := bstep (se 1 (by rfl) ⟨2314187, by rfl⟩ : syracuseStep 3085583 = 4628375) B4628375
theorem B2057055 : Blo 2055435 2057055 := bstep (se 1 (by rfl) ⟨1542791, by rfl⟩ : syracuseStep 2057055 = 3085583) B3085583
theorem B3085589 : Blo 2055435 3085589 := bbase (se 6 (by rfl) ⟨72318, by rfl⟩ : syracuseStep 3085589 = 144637) (by norm_num)
theorem B2057059 : Blo 2055435 2057059 := bstep (se 1 (by rfl) ⟨1542794, by rfl⟩ : syracuseStep 2057059 = 3085589) B3085589
theorem B2638993 : Blo 2055435 2638993 := bbase (se 2 (by rfl) ⟨989622, by rfl⟩ : syracuseStep 2638993 = 1979245) (by norm_num)
theorem B3518657 : Blo 2055435 3518657 := bstep (se 2 (by rfl) ⟨1319496, by rfl⟩ : syracuseStep 3518657 = 2638993) B2638993
theorem B2345771 : Blo 2055435 2345771 := bstep (se 1 (by rfl) ⟨1759328, by rfl⟩ : syracuseStep 2345771 = 3518657) B3518657
theorem B6255389 : Blo 2055435 6255389 := bstep (se 3 (by rfl) ⟨1172885, by rfl⟩ : syracuseStep 6255389 = 2345771) B2345771
theorem B4170259 : Blo 2055435 4170259 := bstep (se 1 (by rfl) ⟨3127694, by rfl⟩ : syracuseStep 4170259 = 6255389) B6255389
theorem B5560345 : Blo 2055435 5560345 := bstep (se 2 (by rfl) ⟨2085129, by rfl⟩ : syracuseStep 5560345 = 4170259) B4170259
theorem B29655173 : Blo 2055435 29655173 := bstep (se 4 (by rfl) ⟨2780172, by rfl⟩ : syracuseStep 29655173 = 5560345) B5560345
theorem B19770115 : Blo 2055435 19770115 := bstep (se 1 (by rfl) ⟨14827586, by rfl⟩ : syracuseStep 19770115 = 29655173) B29655173
theorem B26360153 : Blo 2055435 26360153 := bstep (se 2 (by rfl) ⟨9885057, by rfl⟩ : syracuseStep 26360153 = 19770115) B19770115
theorem B17573435 : Blo 2055435 17573435 := bstep (se 1 (by rfl) ⟨13180076, by rfl⟩ : syracuseStep 17573435 = 26360153) B26360153
theorem B11715623 : Blo 2055435 11715623 := bstep (se 1 (by rfl) ⟨8786717, by rfl⟩ : syracuseStep 11715623 = 17573435) B17573435
theorem B7810415 : Blo 2055435 7810415 := bstep (se 1 (by rfl) ⟨5857811, by rfl⟩ : syracuseStep 7810415 = 11715623) B11715623
theorem B5206943 : Blo 2055435 5206943 := bstep (se 1 (by rfl) ⟨3905207, by rfl⟩ : syracuseStep 5206943 = 7810415) B7810415
theorem B3471295 : Blo 2055435 3471295 := bstep (se 1 (by rfl) ⟨2603471, by rfl⟩ : syracuseStep 3471295 = 5206943) B5206943
theorem B4628393 : Blo 2055435 4628393 := bstep (se 2 (by rfl) ⟨1735647, by rfl⟩ : syracuseStep 4628393 = 3471295) B3471295
theorem B3085595 : Blo 2055435 3085595 := bstep (se 1 (by rfl) ⟨2314196, by rfl⟩ : syracuseStep 3085595 = 4628393) B4628393
theorem B2057063 : Blo 2055435 2057063 := bstep (se 1 (by rfl) ⟨1542797, by rfl⟩ : syracuseStep 2057063 = 3085595) B3085595
theorem B2314201 : Blo 2055435 2314201 := bbase (se 2 (by rfl) ⟨867825, by rfl⟩ : syracuseStep 2314201 = 1735651) (by norm_num)
theorem B3085601 : Blo 2055435 3085601 := bstep (se 2 (by rfl) ⟨1157100, by rfl⟩ : syracuseStep 3085601 = 2314201) B2314201
theorem B2057067 : Blo 2055435 2057067 := bstep (se 1 (by rfl) ⟨1542800, by rfl⟩ : syracuseStep 2057067 = 3085601) B3085601
theorem B2928917 : Blo 2055435 2928917 := bbase (se 6 (by rfl) ⟨68646, by rfl⟩ : syracuseStep 2928917 = 137293) (by norm_num)
theorem B7810445 : Blo 2055435 7810445 := bstep (se 3 (by rfl) ⟨1464458, by rfl⟩ : syracuseStep 7810445 = 2928917) B2928917
theorem B5206963 : Blo 2055435 5206963 := bstep (se 1 (by rfl) ⟨3905222, by rfl⟩ : syracuseStep 5206963 = 7810445) B7810445
theorem B6942617 : Blo 2055435 6942617 := bstep (se 2 (by rfl) ⟨2603481, by rfl⟩ : syracuseStep 6942617 = 5206963) B5206963
theorem B4628411 : Blo 2055435 4628411 := bstep (se 1 (by rfl) ⟨3471308, by rfl⟩ : syracuseStep 4628411 = 6942617) B6942617
theorem B3085607 : Blo 2055435 3085607 := bstep (se 1 (by rfl) ⟨2314205, by rfl⟩ : syracuseStep 3085607 = 4628411) B4628411
theorem B2057071 : Blo 2055435 2057071 := bstep (se 1 (by rfl) ⟨1542803, by rfl⟩ : syracuseStep 2057071 = 3085607) B3085607
theorem B3085613 : Blo 2055435 3085613 := bbase (se 3 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 3085613 = 1157105) (by norm_num)
theorem B2057075 : Blo 2055435 2057075 := bstep (se 1 (by rfl) ⟨1542806, by rfl⟩ : syracuseStep 2057075 = 3085613) B3085613
theorem B4628429 : Blo 2055435 4628429 := bbase (se 3 (by rfl) ⟨867830, by rfl⟩ : syracuseStep 4628429 = 1735661) (by norm_num)
theorem B3085619 : Blo 2055435 3085619 := bstep (se 1 (by rfl) ⟨2314214, by rfl⟩ : syracuseStep 3085619 = 4628429) B4628429
theorem B2057079 : Blo 2055435 2057079 := bstep (se 1 (by rfl) ⟨1542809, by rfl⟩ : syracuseStep 2057079 = 3085619) B3085619
theorem B2603497 : Blo 2055435 2603497 := bbase (se 2 (by rfl) ⟨976311, by rfl⟩ : syracuseStep 2603497 = 1952623) (by norm_num)
theorem B3471329 : Blo 2055435 3471329 := bstep (se 2 (by rfl) ⟨1301748, by rfl⟩ : syracuseStep 3471329 = 2603497) B2603497
theorem B2314219 : Blo 2055435 2314219 := bstep (se 1 (by rfl) ⟨1735664, by rfl⟩ : syracuseStep 2314219 = 3471329) B3471329
theorem B3085625 : Blo 2055435 3085625 := bstep (se 2 (by rfl) ⟨1157109, by rfl⟩ : syracuseStep 3085625 = 2314219) B2314219
theorem B2057083 : Blo 2055435 2057083 := bstep (se 1 (by rfl) ⟨1542812, by rfl⟩ : syracuseStep 2057083 = 3085625) B3085625
theorem B2471293 : Blo 2055435 2471293 := bbase (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) (by norm_num)
theorem B13180229 : Blo 2055435 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B8786819 : Blo 2055435 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B23431517 : Blo 2055435 23431517 := bstep (se 3 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 23431517 = 8786819) B8786819
theorem B15621011 : Blo 2055435 15621011 := bstep (se 1 (by rfl) ⟨11715758, by rfl⟩ : syracuseStep 15621011 = 23431517) B23431517
theorem B10414007 : Blo 2055435 10414007 := bstep (se 1 (by rfl) ⟨7810505, by rfl⟩ : syracuseStep 10414007 = 15621011) B15621011
theorem B6942671 : Blo 2055435 6942671 := bstep (se 1 (by rfl) ⟨5207003, by rfl⟩ : syracuseStep 6942671 = 10414007) B10414007
theorem B4628447 : Blo 2055435 4628447 := bstep (se 1 (by rfl) ⟨3471335, by rfl⟩ : syracuseStep 4628447 = 6942671) B6942671
theorem B3085631 : Blo 2055435 3085631 := bstep (se 1 (by rfl) ⟨2314223, by rfl⟩ : syracuseStep 3085631 = 4628447) B4628447
theorem B2057087 : Blo 2055435 2057087 := bstep (se 1 (by rfl) ⟨1542815, by rfl⟩ : syracuseStep 2057087 = 3085631) B3085631
theorem B3085637 : Blo 2055435 3085637 := bbase (se 4 (by rfl) ⟨289278, by rfl⟩ : syracuseStep 3085637 = 578557) (by norm_num)
theorem B2057091 : Blo 2055435 2057091 := bstep (se 1 (by rfl) ⟨1542818, by rfl⟩ : syracuseStep 2057091 = 3085637) B3085637
theorem B3471349 : Blo 2055435 3471349 := bbase (se 5 (by rfl) ⟨162719, by rfl⟩ : syracuseStep 3471349 = 325439) (by norm_num)
theorem B4628465 : Blo 2055435 4628465 := bstep (se 2 (by rfl) ⟨1735674, by rfl⟩ : syracuseStep 4628465 = 3471349) B3471349
theorem B3085643 : Blo 2055435 3085643 := bstep (se 1 (by rfl) ⟨2314232, by rfl⟩ : syracuseStep 3085643 = 4628465) B4628465
theorem B2057095 : Blo 2055435 2057095 := bstep (se 1 (by rfl) ⟨1542821, by rfl⟩ : syracuseStep 2057095 = 3085643) B3085643
theorem B2314237 : Blo 2055435 2314237 := bbase (se 3 (by rfl) ⟨433919, by rfl⟩ : syracuseStep 2314237 = 867839) (by norm_num)
theorem B3085649 : Blo 2055435 3085649 := bstep (se 2 (by rfl) ⟨1157118, by rfl⟩ : syracuseStep 3085649 = 2314237) B2314237
theorem B2057099 : Blo 2055435 2057099 := bstep (se 1 (by rfl) ⟨1542824, by rfl⟩ : syracuseStep 2057099 = 3085649) B3085649
theorem B6942725 : Blo 2055435 6942725 := bbase (se 4 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 6942725 = 1301761) (by norm_num)
theorem B4628483 : Blo 2055435 4628483 := bstep (se 1 (by rfl) ⟨3471362, by rfl⟩ : syracuseStep 4628483 = 6942725) B6942725
theorem B3085655 : Blo 2055435 3085655 := bstep (se 1 (by rfl) ⟨2314241, by rfl⟩ : syracuseStep 3085655 = 4628483) B4628483
theorem B2057103 : Blo 2055435 2057103 := bstep (se 1 (by rfl) ⟨1542827, by rfl⟩ : syracuseStep 2057103 = 3085655) B3085655
theorem B3085661 : Blo 2055435 3085661 := bbase (se 3 (by rfl) ⟨578561, by rfl⟩ : syracuseStep 3085661 = 1157123) (by norm_num)
theorem B2057107 : Blo 2055435 2057107 := bstep (se 1 (by rfl) ⟨1542830, by rfl⟩ : syracuseStep 2057107 = 3085661) B3085661
theorem B4628501 : Blo 2055435 4628501 := bbase (se 6 (by rfl) ⟨108480, by rfl⟩ : syracuseStep 4628501 = 216961) (by norm_num)
theorem B3085667 : Blo 2055435 3085667 := bstep (se 1 (by rfl) ⟨2314250, by rfl⟩ : syracuseStep 3085667 = 4628501) B4628501
theorem B2057111 : Blo 2055435 2057111 := bstep (se 1 (by rfl) ⟨1542833, by rfl⟩ : syracuseStep 2057111 = 3085667) B3085667
theorem B7810613 : Blo 2055435 7810613 := bbase (se 5 (by rfl) ⟨366122, by rfl⟩ : syracuseStep 7810613 = 732245) (by norm_num)
theorem B5207075 : Blo 2055435 5207075 := bstep (se 1 (by rfl) ⟨3905306, by rfl⟩ : syracuseStep 5207075 = 7810613) B7810613
theorem B3471383 : Blo 2055435 3471383 := bstep (se 1 (by rfl) ⟨2603537, by rfl⟩ : syracuseStep 3471383 = 5207075) B5207075
theorem B2314255 : Blo 2055435 2314255 := bstep (se 1 (by rfl) ⟨1735691, by rfl⟩ : syracuseStep 2314255 = 3471383) B3471383
theorem B3085673 : Blo 2055435 3085673 := bstep (se 2 (by rfl) ⟨1157127, by rfl⟩ : syracuseStep 3085673 = 2314255) B2314255
theorem B2057115 : Blo 2055435 2057115 := bstep (se 1 (by rfl) ⟨1542836, by rfl⟩ : syracuseStep 2057115 = 3085673) B3085673
theorem B3295109 : Blo 2055435 3295109 := bbase (se 4 (by rfl) ⟨308916, by rfl⟩ : syracuseStep 3295109 = 617833) (by norm_num)
theorem B2196739 : Blo 2055435 2196739 := bstep (se 1 (by rfl) ⟨1647554, by rfl⟩ : syracuseStep 2196739 = 3295109) B3295109
theorem B11715941 : Blo 2055435 11715941 := bstep (se 4 (by rfl) ⟨1098369, by rfl⟩ : syracuseStep 11715941 = 2196739) B2196739
theorem B7810627 : Blo 2055435 7810627 := bstep (se 1 (by rfl) ⟨5857970, by rfl⟩ : syracuseStep 7810627 = 11715941) B11715941
theorem B10414169 : Blo 2055435 10414169 := bstep (se 2 (by rfl) ⟨3905313, by rfl⟩ : syracuseStep 10414169 = 7810627) B7810627
theorem B6942779 : Blo 2055435 6942779 := bstep (se 1 (by rfl) ⟨5207084, by rfl⟩ : syracuseStep 6942779 = 10414169) B10414169
theorem B4628519 : Blo 2055435 4628519 := bstep (se 1 (by rfl) ⟨3471389, by rfl⟩ : syracuseStep 4628519 = 6942779) B6942779
theorem B3085679 : Blo 2055435 3085679 := bstep (se 1 (by rfl) ⟨2314259, by rfl⟩ : syracuseStep 3085679 = 4628519) B4628519
theorem B2057119 : Blo 2055435 2057119 := bstep (se 1 (by rfl) ⟨1542839, by rfl⟩ : syracuseStep 2057119 = 3085679) B3085679
theorem B3085685 : Blo 2055435 3085685 := bbase (se 5 (by rfl) ⟨144641, by rfl⟩ : syracuseStep 3085685 = 289283) (by norm_num)
theorem B2057123 : Blo 2055435 2057123 := bstep (se 1 (by rfl) ⟨1542842, by rfl⟩ : syracuseStep 2057123 = 3085685) B3085685
theorem B2928997 : Blo 2055435 2928997 := bbase (se 4 (by rfl) ⟨274593, by rfl⟩ : syracuseStep 2928997 = 549187) (by norm_num)
theorem B3905329 : Blo 2055435 3905329 := bstep (se 2 (by rfl) ⟨1464498, by rfl⟩ : syracuseStep 3905329 = 2928997) B2928997
theorem B5207105 : Blo 2055435 5207105 := bstep (se 2 (by rfl) ⟨1952664, by rfl⟩ : syracuseStep 5207105 = 3905329) B3905329
theorem B3471403 : Blo 2055435 3471403 := bstep (se 1 (by rfl) ⟨2603552, by rfl⟩ : syracuseStep 3471403 = 5207105) B5207105
theorem B4628537 : Blo 2055435 4628537 := bstep (se 2 (by rfl) ⟨1735701, by rfl⟩ : syracuseStep 4628537 = 3471403) B3471403
theorem B3085691 : Blo 2055435 3085691 := bstep (se 1 (by rfl) ⟨2314268, by rfl⟩ : syracuseStep 3085691 = 4628537) B4628537
theorem B2057127 : Blo 2055435 2057127 := bstep (se 1 (by rfl) ⟨1542845, by rfl⟩ : syracuseStep 2057127 = 3085691) B3085691
theorem B2314273 : Blo 2055435 2314273 := bbase (se 2 (by rfl) ⟨867852, by rfl⟩ : syracuseStep 2314273 = 1735705) (by norm_num)
theorem B3085697 : Blo 2055435 3085697 := bstep (se 2 (by rfl) ⟨1157136, by rfl⟩ : syracuseStep 3085697 = 2314273) B2314273
theorem B2057131 : Blo 2055435 2057131 := bstep (se 1 (by rfl) ⟨1542848, by rfl⟩ : syracuseStep 2057131 = 3085697) B3085697
theorem B5207125 : Blo 2055435 5207125 := bbase (se 8 (by rfl) ⟨30510, by rfl⟩ : syracuseStep 5207125 = 61021) (by norm_num)
theorem B6942833 : Blo 2055435 6942833 := bstep (se 2 (by rfl) ⟨2603562, by rfl⟩ : syracuseStep 6942833 = 5207125) B5207125
theorem B4628555 : Blo 2055435 4628555 := bstep (se 1 (by rfl) ⟨3471416, by rfl⟩ : syracuseStep 4628555 = 6942833) B6942833
theorem B3085703 : Blo 2055435 3085703 := bstep (se 1 (by rfl) ⟨2314277, by rfl⟩ : syracuseStep 3085703 = 4628555) B4628555
theorem B2057135 : Blo 2055435 2057135 := bstep (se 1 (by rfl) ⟨1542851, by rfl⟩ : syracuseStep 2057135 = 3085703) B3085703
theorem B3085709 : Blo 2055435 3085709 := bbase (se 3 (by rfl) ⟨578570, by rfl⟩ : syracuseStep 3085709 = 1157141) (by norm_num)
theorem B2057139 : Blo 2055435 2057139 := bstep (se 1 (by rfl) ⟨1542854, by rfl⟩ : syracuseStep 2057139 = 3085709) B3085709
theorem B4628573 : Blo 2055435 4628573 := bbase (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) (by norm_num)
theorem B3085715 : Blo 2055435 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B2057143 : Blo 2055435 2057143 := bstep (se 1 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 2057143 = 3085715) B3085715
theorem B3471437 : Blo 2055435 3471437 := bbase (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) (by norm_num)
theorem B2314291 : Blo 2055435 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B3085721 : Blo 2055435 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B2057147 : Blo 2055435 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B2226745 : Blo 2055435 2226745 := bbase (se 2 (by rfl) ⟨835029, by rfl⟩ : syracuseStep 2226745 = 1670059) (by norm_num)
theorem B2968993 : Blo 2055435 2968993 := bstep (se 2 (by rfl) ⟨1113372, by rfl⟩ : syracuseStep 2968993 = 2226745) B2226745
theorem B15834629 : Blo 2055435 15834629 := bstep (se 4 (by rfl) ⟨1484496, by rfl⟩ : syracuseStep 15834629 = 2968993) B2968993
theorem B10556419 : Blo 2055435 10556419 := bstep (se 1 (by rfl) ⟨7917314, by rfl⟩ : syracuseStep 10556419 = 15834629) B15834629
theorem B14075225 : Blo 2055435 14075225 := bstep (se 2 (by rfl) ⟨5278209, by rfl⟩ : syracuseStep 14075225 = 10556419) B10556419
theorem B9383483 : Blo 2055435 9383483 := bstep (se 1 (by rfl) ⟨7037612, by rfl⟩ : syracuseStep 9383483 = 14075225) B14075225
theorem B25022621 : Blo 2055435 25022621 := bstep (se 3 (by rfl) ⟨4691741, by rfl⟩ : syracuseStep 25022621 = 9383483) B9383483
theorem B66726989 : Blo 2055435 66726989 := bstep (se 3 (by rfl) ⟨12511310, by rfl⟩ : syracuseStep 66726989 = 25022621) B25022621
theorem B44484659 : Blo 2055435 44484659 := bstep (se 1 (by rfl) ⟨33363494, by rfl⟩ : syracuseStep 44484659 = 66726989) B66726989
theorem B29656439 : Blo 2055435 29656439 := bstep (se 1 (by rfl) ⟨22242329, by rfl⟩ : syracuseStep 29656439 = 44484659) B44484659
theorem B19770959 : Blo 2055435 19770959 := bstep (se 1 (by rfl) ⟨14828219, by rfl⟩ : syracuseStep 19770959 = 29656439) B29656439
theorem B13180639 : Blo 2055435 13180639 := bstep (se 1 (by rfl) ⟨9885479, by rfl⟩ : syracuseStep 13180639 = 19770959) B19770959
theorem B17574185 : Blo 2055435 17574185 := bstep (se 2 (by rfl) ⟨6590319, by rfl⟩ : syracuseStep 17574185 = 13180639) B13180639
theorem B11716123 : Blo 2055435 11716123 := bstep (se 1 (by rfl) ⟨8787092, by rfl⟩ : syracuseStep 11716123 = 17574185) B17574185
theorem B15621497 : Blo 2055435 15621497 := bstep (se 2 (by rfl) ⟨5858061, by rfl⟩ : syracuseStep 15621497 = 11716123) B11716123
theorem B10414331 : Blo 2055435 10414331 := bstep (se 1 (by rfl) ⟨7810748, by rfl⟩ : syracuseStep 10414331 = 15621497) B15621497
theorem B6942887 : Blo 2055435 6942887 := bstep (se 1 (by rfl) ⟨5207165, by rfl⟩ : syracuseStep 6942887 = 10414331) B10414331
theorem B4628591 : Blo 2055435 4628591 := bstep (se 1 (by rfl) ⟨3471443, by rfl⟩ : syracuseStep 4628591 = 6942887) B6942887
theorem B3085727 : Blo 2055435 3085727 := bstep (se 1 (by rfl) ⟨2314295, by rfl⟩ : syracuseStep 3085727 = 4628591) B4628591
theorem B2057151 : Blo 2055435 2057151 := bstep (se 1 (by rfl) ⟨1542863, by rfl⟩ : syracuseStep 2057151 = 3085727) B3085727
theorem B3085733 : Blo 2055435 3085733 := bbase (se 4 (by rfl) ⟨289287, by rfl⟩ : syracuseStep 3085733 = 578575) (by norm_num)
theorem B2057155 : Blo 2055435 2057155 := bstep (se 1 (by rfl) ⟨1542866, by rfl⟩ : syracuseStep 2057155 = 3085733) B3085733
theorem B2603593 : Blo 2055435 2603593 := bbase (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) (by norm_num)
theorem B3471457 : Blo 2055435 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B4628609 : Blo 2055435 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B3085739 : Blo 2055435 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B2057159 : Blo 2055435 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B2314309 : Blo 2055435 2314309 := bbase (se 4 (by rfl) ⟨216966, by rfl⟩ : syracuseStep 2314309 = 433933) (by norm_num)
theorem B3085745 : Blo 2055435 3085745 := bstep (se 2 (by rfl) ⟨1157154, by rfl⟩ : syracuseStep 3085745 = 2314309) B2314309
theorem B2057163 : Blo 2055435 2057163 := bstep (se 1 (by rfl) ⟨1542872, by rfl⟩ : syracuseStep 2057163 = 3085745) B3085745
theorem B3905405 : Blo 2055435 3905405 := bbase (se 3 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 3905405 = 1464527) (by norm_num)
theorem B2603603 : Blo 2055435 2603603 := bstep (se 1 (by rfl) ⟨1952702, by rfl⟩ : syracuseStep 2603603 = 3905405) B3905405
theorem B6942941 : Blo 2055435 6942941 := bstep (se 3 (by rfl) ⟨1301801, by rfl⟩ : syracuseStep 6942941 = 2603603) B2603603
theorem B4628627 : Blo 2055435 4628627 := bstep (se 1 (by rfl) ⟨3471470, by rfl⟩ : syracuseStep 4628627 = 6942941) B6942941
theorem B3085751 : Blo 2055435 3085751 := bstep (se 1 (by rfl) ⟨2314313, by rfl⟩ : syracuseStep 3085751 = 4628627) B4628627
theorem B2057167 : Blo 2055435 2057167 := bstep (se 1 (by rfl) ⟨1542875, by rfl⟩ : syracuseStep 2057167 = 3085751) B3085751
theorem B3085757 : Blo 2055435 3085757 := bbase (se 3 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 3085757 = 1157159) (by norm_num)
theorem B2057171 : Blo 2055435 2057171 := bstep (se 1 (by rfl) ⟨1542878, by rfl⟩ : syracuseStep 2057171 = 3085757) B3085757
theorem B4628645 : Blo 2055435 4628645 := bbase (se 4 (by rfl) ⟨433935, by rfl⟩ : syracuseStep 4628645 = 867871) (by norm_num)
theorem B3085763 : Blo 2055435 3085763 := bstep (se 1 (by rfl) ⟨2314322, by rfl⟩ : syracuseStep 3085763 = 4628645) B4628645
theorem B2057175 : Blo 2055435 2057175 := bstep (se 1 (by rfl) ⟨1542881, by rfl⟩ : syracuseStep 2057175 = 3085763) B3085763
theorem B5207237 : Blo 2055435 5207237 := bbase (se 4 (by rfl) ⟨488178, by rfl⟩ : syracuseStep 5207237 = 976357) (by norm_num)
theorem B3471491 : Blo 2055435 3471491 := bstep (se 1 (by rfl) ⟨2603618, by rfl⟩ : syracuseStep 3471491 = 5207237) B5207237
theorem B2314327 : Blo 2055435 2314327 := bstep (se 1 (by rfl) ⟨1735745, by rfl⟩ : syracuseStep 2314327 = 3471491) B3471491
theorem B3085769 : Blo 2055435 3085769 := bstep (se 2 (by rfl) ⟨1157163, by rfl⟩ : syracuseStep 3085769 = 2314327) B2314327
theorem B2057179 : Blo 2055435 2057179 := bstep (se 1 (by rfl) ⟨1542884, by rfl⟩ : syracuseStep 2057179 = 3085769) B3085769
theorem B2226781 : Blo 2055435 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B2969041 : Blo 2055435 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B3958721 : Blo 2055435 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B2639147 : Blo 2055435 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B7037725 : Blo 2055435 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B9383633 : Blo 2055435 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B6255755 : Blo 2055435 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B4170503 : Blo 2055435 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B2780335 : Blo 2055435 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B14828453 : Blo 2055435 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B9885635 : Blo 2055435 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B6590423 : Blo 2055435 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B4393615 : Blo 2055435 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B5858153 : Blo 2055435 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B3905435 : Blo 2055435 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B10414493 : Blo 2055435 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B6942995 : Blo 2055435 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B4628663 : Blo 2055435 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B3085775 : Blo 2055435 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B2057183 : Blo 2055435 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B3085781 : Blo 2055435 3085781 := bbase (se 7 (by rfl) ⟨36161, by rfl⟩ : syracuseStep 3085781 = 72323) (by norm_num)
theorem B2057187 : Blo 2055435 2057187 := bstep (se 1 (by rfl) ⟨1542890, by rfl⟩ : syracuseStep 2057187 = 3085781) B3085781
theorem B7810901 : Blo 2055435 7810901 := bbase (se 9 (by rfl) ⟨22883, by rfl⟩ : syracuseStep 7810901 = 45767) (by norm_num)
theorem B5207267 : Blo 2055435 5207267 := bstep (se 1 (by rfl) ⟨3905450, by rfl⟩ : syracuseStep 5207267 = 7810901) B7810901
theorem B3471511 : Blo 2055435 3471511 := bstep (se 1 (by rfl) ⟨2603633, by rfl⟩ : syracuseStep 3471511 = 5207267) B5207267
theorem B4628681 : Blo 2055435 4628681 := bstep (se 2 (by rfl) ⟨1735755, by rfl⟩ : syracuseStep 4628681 = 3471511) B3471511
theorem B3085787 : Blo 2055435 3085787 := bstep (se 1 (by rfl) ⟨2314340, by rfl⟩ : syracuseStep 3085787 = 4628681) B4628681
theorem B2057191 : Blo 2055435 2057191 := bstep (se 1 (by rfl) ⟨1542893, by rfl⟩ : syracuseStep 2057191 = 3085787) B3085787
theorem B2314345 : Blo 2055435 2314345 := bbase (se 2 (by rfl) ⟨867879, by rfl⟩ : syracuseStep 2314345 = 1735759) (by norm_num)
theorem B3085793 : Blo 2055435 3085793 := bstep (se 2 (by rfl) ⟨1157172, by rfl⟩ : syracuseStep 3085793 = 2314345) B2314345
theorem B2057195 : Blo 2055435 2057195 := bstep (se 1 (by rfl) ⟨1542896, by rfl⟩ : syracuseStep 2057195 = 3085793) B3085793
theorem B3295237 : Blo 2055435 3295237 := bbase (se 4 (by rfl) ⟨308928, by rfl⟩ : syracuseStep 3295237 = 617857) (by norm_num)
theorem B4393649 : Blo 2055435 4393649 := bstep (se 2 (by rfl) ⟨1647618, by rfl⟩ : syracuseStep 4393649 = 3295237) B3295237
theorem B11716397 : Blo 2055435 11716397 := bstep (se 3 (by rfl) ⟨2196824, by rfl⟩ : syracuseStep 11716397 = 4393649) B4393649
theorem B7810931 : Blo 2055435 7810931 := bstep (se 1 (by rfl) ⟨5858198, by rfl⟩ : syracuseStep 7810931 = 11716397) B11716397
theorem B5207287 : Blo 2055435 5207287 := bstep (se 1 (by rfl) ⟨3905465, by rfl⟩ : syracuseStep 5207287 = 7810931) B7810931
theorem B6943049 : Blo 2055435 6943049 := bstep (se 2 (by rfl) ⟨2603643, by rfl⟩ : syracuseStep 6943049 = 5207287) B5207287
theorem B4628699 : Blo 2055435 4628699 := bstep (se 1 (by rfl) ⟨3471524, by rfl⟩ : syracuseStep 4628699 = 6943049) B6943049
theorem B3085799 : Blo 2055435 3085799 := bstep (se 1 (by rfl) ⟨2314349, by rfl⟩ : syracuseStep 3085799 = 4628699) B4628699
theorem B2057199 : Blo 2055435 2057199 := bstep (se 1 (by rfl) ⟨1542899, by rfl⟩ : syracuseStep 2057199 = 3085799) B3085799
theorem B3085805 : Blo 2055435 3085805 := bbase (se 3 (by rfl) ⟨578588, by rfl⟩ : syracuseStep 3085805 = 1157177) (by norm_num)
theorem B2057203 : Blo 2055435 2057203 := bstep (se 1 (by rfl) ⟨1542902, by rfl⟩ : syracuseStep 2057203 = 3085805) B3085805
theorem B4628717 : Blo 2055435 4628717 := bbase (se 3 (by rfl) ⟨867884, by rfl⟩ : syracuseStep 4628717 = 1735769) (by norm_num)
theorem B3085811 : Blo 2055435 3085811 := bstep (se 1 (by rfl) ⟨2314358, by rfl⟩ : syracuseStep 3085811 = 4628717) B4628717
theorem B2057207 : Blo 2055435 2057207 := bstep (se 1 (by rfl) ⟨1542905, by rfl⟩ : syracuseStep 2057207 = 3085811) B3085811
theorem B2929117 : Blo 2055435 2929117 := bbase (se 3 (by rfl) ⟨549209, by rfl⟩ : syracuseStep 2929117 = 1098419) (by norm_num)
theorem B3905489 : Blo 2055435 3905489 := bstep (se 2 (by rfl) ⟨1464558, by rfl⟩ : syracuseStep 3905489 = 2929117) B2929117
theorem B2603659 : Blo 2055435 2603659 := bstep (se 1 (by rfl) ⟨1952744, by rfl⟩ : syracuseStep 2603659 = 3905489) B3905489
theorem B3471545 : Blo 2055435 3471545 := bstep (se 2 (by rfl) ⟨1301829, by rfl⟩ : syracuseStep 3471545 = 2603659) B2603659
theorem B2314363 : Blo 2055435 2314363 := bstep (se 1 (by rfl) ⟨1735772, by rfl⟩ : syracuseStep 2314363 = 3471545) B3471545
theorem B3085817 : Blo 2055435 3085817 := bstep (se 2 (by rfl) ⟨1157181, by rfl⟩ : syracuseStep 3085817 = 2314363) B2314363
theorem B2057211 : Blo 2055435 2057211 := bstep (se 1 (by rfl) ⟨1542908, by rfl⟩ : syracuseStep 2057211 = 3085817) B3085817
theorem B79086293 : Blo 2055435 79086293 := bbase (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) (by norm_num)
theorem B52724195 : Blo 2055435 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B35149463 : Blo 2055435 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B23432975 : Blo 2055435 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B15621983 : Blo 2055435 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B10414655 : Blo 2055435 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B6943103 : Blo 2055435 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B4628735 : Blo 2055435 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B3085823 : Blo 2055435 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B2057215 : Blo 2055435 2057215 := bstep (se 1 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 2057215 = 3085823) B3085823
theorem B3085829 : Blo 2055435 3085829 := bbase (se 4 (by rfl) ⟨289296, by rfl⟩ : syracuseStep 3085829 = 578593) (by norm_num)
theorem B2057219 : Blo 2055435 2057219 := bstep (se 1 (by rfl) ⟨1542914, by rfl⟩ : syracuseStep 2057219 = 3085829) B3085829
theorem B3471565 : Blo 2055435 3471565 := bbase (se 3 (by rfl) ⟨650918, by rfl⟩ : syracuseStep 3471565 = 1301837) (by norm_num)
theorem B4628753 : Blo 2055435 4628753 := bstep (se 2 (by rfl) ⟨1735782, by rfl⟩ : syracuseStep 4628753 = 3471565) B3471565
theorem B3085835 : Blo 2055435 3085835 := bstep (se 1 (by rfl) ⟨2314376, by rfl⟩ : syracuseStep 3085835 = 4628753) B4628753
theorem B2057223 : Blo 2055435 2057223 := bstep (se 1 (by rfl) ⟨1542917, by rfl⟩ : syracuseStep 2057223 = 3085835) B3085835
theorem B2314381 : Blo 2055435 2314381 := bbase (se 3 (by rfl) ⟨433946, by rfl⟩ : syracuseStep 2314381 = 867893) (by norm_num)
theorem B3085841 : Blo 2055435 3085841 := bstep (se 2 (by rfl) ⟨1157190, by rfl⟩ : syracuseStep 3085841 = 2314381) B2314381
theorem B2057227 : Blo 2055435 2057227 := bstep (se 1 (by rfl) ⟨1542920, by rfl⟩ : syracuseStep 2057227 = 3085841) B3085841
theorem B6943157 : Blo 2055435 6943157 := bbase (se 5 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 6943157 = 650921) (by norm_num)
theorem B4628771 : Blo 2055435 4628771 := bstep (se 1 (by rfl) ⟨3471578, by rfl⟩ : syracuseStep 4628771 = 6943157) B6943157
theorem B3085847 : Blo 2055435 3085847 := bstep (se 1 (by rfl) ⟨2314385, by rfl⟩ : syracuseStep 3085847 = 4628771) B4628771
theorem B2057231 : Blo 2055435 2057231 := bstep (se 1 (by rfl) ⟨1542923, by rfl⟩ : syracuseStep 2057231 = 3085847) B3085847
theorem B3085853 : Blo 2055435 3085853 := bbase (se 3 (by rfl) ⟨578597, by rfl⟩ : syracuseStep 3085853 = 1157195) (by norm_num)
theorem B2057235 : Blo 2055435 2057235 := bstep (se 1 (by rfl) ⟨1542926, by rfl⟩ : syracuseStep 2057235 = 3085853) B3085853
theorem B4628789 : Blo 2055435 4628789 := bbase (se 5 (by rfl) ⟨216974, by rfl⟩ : syracuseStep 4628789 = 433949) (by norm_num)
theorem B3085859 : Blo 2055435 3085859 := bstep (se 1 (by rfl) ⟨2314394, by rfl⟩ : syracuseStep 3085859 = 4628789) B4628789
theorem B2057239 : Blo 2055435 2057239 := bstep (se 1 (by rfl) ⟨1542929, by rfl⟩ : syracuseStep 2057239 = 3085859) B3085859
theorem B2226845 : Blo 2055435 2226845 := bbase (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) (by norm_num)
theorem B5938253 : Blo 2055435 5938253 := bstep (se 3 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 5938253 = 2226845) B2226845
theorem B3958835 : Blo 2055435 3958835 := bstep (se 1 (by rfl) ⟨2969126, by rfl⟩ : syracuseStep 3958835 = 5938253) B5938253
theorem B10556893 : Blo 2055435 10556893 := bstep (se 3 (by rfl) ⟨1979417, by rfl⟩ : syracuseStep 10556893 = 3958835) B3958835
theorem B14075857 : Blo 2055435 14075857 := bstep (se 2 (by rfl) ⟨5278446, by rfl⟩ : syracuseStep 14075857 = 10556893) B10556893
theorem B18767809 : Blo 2055435 18767809 := bstep (se 2 (by rfl) ⟨7037928, by rfl⟩ : syracuseStep 18767809 = 14075857) B14075857
theorem B25023745 : Blo 2055435 25023745 := bstep (se 2 (by rfl) ⟨9383904, by rfl⟩ : syracuseStep 25023745 = 18767809) B18767809
theorem B33364993 : Blo 2055435 33364993 := bstep (se 2 (by rfl) ⟨12511872, by rfl⟩ : syracuseStep 33364993 = 25023745) B25023745
theorem B44486657 : Blo 2055435 44486657 := bstep (se 2 (by rfl) ⟨16682496, by rfl⟩ : syracuseStep 44486657 = 33364993) B33364993
theorem B29657771 : Blo 2055435 29657771 := bstep (se 1 (by rfl) ⟨22243328, by rfl⟩ : syracuseStep 29657771 = 44486657) B44486657
theorem B19771847 : Blo 2055435 19771847 := bstep (se 1 (by rfl) ⟨14828885, by rfl⟩ : syracuseStep 19771847 = 29657771) B29657771
theorem B13181231 : Blo 2055435 13181231 := bstep (se 1 (by rfl) ⟨9885923, by rfl⟩ : syracuseStep 13181231 = 19771847) B19771847
theorem B8787487 : Blo 2055435 8787487 := bstep (se 1 (by rfl) ⟨6590615, by rfl⟩ : syracuseStep 8787487 = 13181231) B13181231
theorem B11716649 : Blo 2055435 11716649 := bstep (se 2 (by rfl) ⟨4393743, by rfl⟩ : syracuseStep 11716649 = 8787487) B8787487
theorem B7811099 : Blo 2055435 7811099 := bstep (se 1 (by rfl) ⟨5858324, by rfl⟩ : syracuseStep 7811099 = 11716649) B11716649
theorem B5207399 : Blo 2055435 5207399 := bstep (se 1 (by rfl) ⟨3905549, by rfl⟩ : syracuseStep 5207399 = 7811099) B7811099
theorem B3471599 : Blo 2055435 3471599 := bstep (se 1 (by rfl) ⟨2603699, by rfl⟩ : syracuseStep 3471599 = 5207399) B5207399
theorem B2314399 : Blo 2055435 2314399 := bstep (se 1 (by rfl) ⟨1735799, by rfl⟩ : syracuseStep 2314399 = 3471599) B3471599
theorem B3085865 : Blo 2055435 3085865 := bstep (se 2 (by rfl) ⟨1157199, by rfl⟩ : syracuseStep 3085865 = 2314399) B2314399
theorem B2057243 : Blo 2055435 2057243 := bstep (se 1 (by rfl) ⟨1542932, by rfl⟩ : syracuseStep 2057243 = 3085865) B3085865
theorem B7231301 : Blo 2055435 7231301 := bbase (se 4 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 7231301 = 1355869) (by norm_num)
theorem B4820867 : Blo 2055435 4820867 := bstep (se 1 (by rfl) ⟨3615650, by rfl⟩ : syracuseStep 4820867 = 7231301) B7231301
theorem B3213911 : Blo 2055435 3213911 := bstep (se 1 (by rfl) ⟨2410433, by rfl⟩ : syracuseStep 3213911 = 4820867) B4820867
theorem B2142607 : Blo 2055435 2142607 := bstep (se 1 (by rfl) ⟨1606955, by rfl⟩ : syracuseStep 2142607 = 3213911) B3213911
theorem B2856809 : Blo 2055435 2856809 := bstep (se 2 (by rfl) ⟨1071303, by rfl⟩ : syracuseStep 2856809 = 2142607) B2142607
theorem B7618157 : Blo 2055435 7618157 := bstep (se 3 (by rfl) ⟨1428404, by rfl⟩ : syracuseStep 7618157 = 2856809) B2856809
theorem B5078771 : Blo 2055435 5078771 := bstep (se 1 (by rfl) ⟨3809078, by rfl⟩ : syracuseStep 5078771 = 7618157) B7618157
theorem B3385847 : Blo 2055435 3385847 := bstep (se 1 (by rfl) ⟨2539385, by rfl⟩ : syracuseStep 3385847 = 5078771) B5078771
theorem B2257231 : Blo 2055435 2257231 := bstep (se 1 (by rfl) ⟨1692923, by rfl⟩ : syracuseStep 2257231 = 3385847) B3385847
theorem B3009641 : Blo 2055435 3009641 := bstep (se 2 (by rfl) ⟨1128615, by rfl⟩ : syracuseStep 3009641 = 2257231) B2257231
theorem B32102837 : Blo 2055435 32102837 := bstep (se 5 (by rfl) ⟨1504820, by rfl⟩ : syracuseStep 32102837 = 3009641) B3009641
theorem B21401891 : Blo 2055435 21401891 := bstep (se 1 (by rfl) ⟨16051418, by rfl⟩ : syracuseStep 21401891 = 32102837) B32102837
theorem B14267927 : Blo 2055435 14267927 := bstep (se 1 (by rfl) ⟨10700945, by rfl⟩ : syracuseStep 14267927 = 21401891) B21401891
theorem B9511951 : Blo 2055435 9511951 := bstep (se 1 (by rfl) ⟨7133963, by rfl⟩ : syracuseStep 9511951 = 14267927) B14267927
theorem B12682601 : Blo 2055435 12682601 := bstep (se 2 (by rfl) ⟨4755975, by rfl⟩ : syracuseStep 12682601 = 9511951) B9511951
theorem B8455067 : Blo 2055435 8455067 := bstep (se 1 (by rfl) ⟨6341300, by rfl⟩ : syracuseStep 8455067 = 12682601) B12682601
theorem B5636711 : Blo 2055435 5636711 := bstep (se 1 (by rfl) ⟨4227533, by rfl⟩ : syracuseStep 5636711 = 8455067) B8455067
theorem B15031229 : Blo 2055435 15031229 := bstep (se 3 (by rfl) ⟨2818355, by rfl⟩ : syracuseStep 15031229 = 5636711) B5636711
theorem B40083277 : Blo 2055435 40083277 := bstep (se 3 (by rfl) ⟨7515614, by rfl⟩ : syracuseStep 40083277 = 15031229) B15031229
theorem B53444369 : Blo 2055435 53444369 := bstep (se 2 (by rfl) ⟨20041638, by rfl⟩ : syracuseStep 53444369 = 40083277) B40083277
theorem B35629579 : Blo 2055435 35629579 := bstep (se 1 (by rfl) ⟨26722184, by rfl⟩ : syracuseStep 35629579 = 53444369) B53444369
theorem B47506105 : Blo 2055435 47506105 := bstep (se 2 (by rfl) ⟨17814789, by rfl⟩ : syracuseStep 47506105 = 35629579) B35629579
theorem B63341473 : Blo 2055435 63341473 := bstep (se 2 (by rfl) ⟨23753052, by rfl⟩ : syracuseStep 63341473 = 47506105) B47506105
theorem B84455297 : Blo 2055435 84455297 := bstep (se 2 (by rfl) ⟨31670736, by rfl⟩ : syracuseStep 84455297 = 63341473) B63341473
theorem B56303531 : Blo 2055435 56303531 := bstep (se 1 (by rfl) ⟨42227648, by rfl⟩ : syracuseStep 56303531 = 84455297) B84455297
theorem B37535687 : Blo 2055435 37535687 := bstep (se 1 (by rfl) ⟨28151765, by rfl⟩ : syracuseStep 37535687 = 56303531) B56303531
theorem B25023791 : Blo 2055435 25023791 := bstep (se 1 (by rfl) ⟨18767843, by rfl⟩ : syracuseStep 25023791 = 37535687) B37535687
theorem B16682527 : Blo 2055435 16682527 := bstep (se 1 (by rfl) ⟨12511895, by rfl⟩ : syracuseStep 16682527 = 25023791) B25023791
theorem B22243369 : Blo 2055435 22243369 := bstep (se 2 (by rfl) ⟨8341263, by rfl⟩ : syracuseStep 22243369 = 16682527) B16682527
theorem B29657825 : Blo 2055435 29657825 := bstep (se 2 (by rfl) ⟨11121684, by rfl⟩ : syracuseStep 29657825 = 22243369) B22243369
theorem B19771883 : Blo 2055435 19771883 := bstep (se 1 (by rfl) ⟨14828912, by rfl⟩ : syracuseStep 19771883 = 29657825) B29657825
theorem B13181255 : Blo 2055435 13181255 := bstep (se 1 (by rfl) ⟨9885941, by rfl⟩ : syracuseStep 13181255 = 19771883) B19771883
theorem B8787503 : Blo 2055435 8787503 := bstep (se 1 (by rfl) ⟨6590627, by rfl⟩ : syracuseStep 8787503 = 13181255) B13181255
theorem B5858335 : Blo 2055435 5858335 := bstep (se 1 (by rfl) ⟨4393751, by rfl⟩ : syracuseStep 5858335 = 8787503) B8787503
theorem B7811113 : Blo 2055435 7811113 := bstep (se 2 (by rfl) ⟨2929167, by rfl⟩ : syracuseStep 7811113 = 5858335) B5858335
theorem B10414817 : Blo 2055435 10414817 := bstep (se 2 (by rfl) ⟨3905556, by rfl⟩ : syracuseStep 10414817 = 7811113) B7811113
theorem B6943211 : Blo 2055435 6943211 := bstep (se 1 (by rfl) ⟨5207408, by rfl⟩ : syracuseStep 6943211 = 10414817) B10414817
theorem B4628807 : Blo 2055435 4628807 := bstep (se 1 (by rfl) ⟨3471605, by rfl⟩ : syracuseStep 4628807 = 6943211) B6943211
theorem B3085871 : Blo 2055435 3085871 := bstep (se 1 (by rfl) ⟨2314403, by rfl⟩ : syracuseStep 3085871 = 4628807) B4628807
theorem B2057247 : Blo 2055435 2057247 := bstep (se 1 (by rfl) ⟨1542935, by rfl⟩ : syracuseStep 2057247 = 3085871) B3085871
theorem B3085877 : Blo 2055435 3085877 := bbase (se 5 (by rfl) ⟨144650, by rfl⟩ : syracuseStep 3085877 = 289301) (by norm_num)
theorem B2057251 : Blo 2055435 2057251 := bstep (se 1 (by rfl) ⟨1542938, by rfl⟩ : syracuseStep 2057251 = 3085877) B3085877
theorem B5207429 : Blo 2055435 5207429 := bbase (se 4 (by rfl) ⟨488196, by rfl⟩ : syracuseStep 5207429 = 976393) (by norm_num)
theorem B3471619 : Blo 2055435 3471619 := bstep (se 1 (by rfl) ⟨2603714, by rfl⟩ : syracuseStep 3471619 = 5207429) B5207429
theorem B4628825 : Blo 2055435 4628825 := bstep (se 2 (by rfl) ⟨1735809, by rfl⟩ : syracuseStep 4628825 = 3471619) B3471619
theorem B3085883 : Blo 2055435 3085883 := bstep (se 1 (by rfl) ⟨2314412, by rfl⟩ : syracuseStep 3085883 = 4628825) B4628825
theorem B2057255 : Blo 2055435 2057255 := bstep (se 1 (by rfl) ⟨1542941, by rfl⟩ : syracuseStep 2057255 = 3085883) B3085883
theorem B2314417 : Blo 2055435 2314417 := bbase (se 2 (by rfl) ⟨867906, by rfl⟩ : syracuseStep 2314417 = 1735813) (by norm_num)
theorem B3085889 : Blo 2055435 3085889 := bstep (se 2 (by rfl) ⟨1157208, by rfl⟩ : syracuseStep 3085889 = 2314417) B2314417
theorem B2057259 : Blo 2055435 2057259 := bstep (se 1 (by rfl) ⟨1542944, by rfl⟩ : syracuseStep 2057259 = 3085889) B3085889
theorem B2196893 : Blo 2055435 2196893 := bbase (se 3 (by rfl) ⟨411917, by rfl⟩ : syracuseStep 2196893 = 823835) (by norm_num)
theorem B5858381 : Blo 2055435 5858381 := bstep (se 3 (by rfl) ⟨1098446, by rfl⟩ : syracuseStep 5858381 = 2196893) B2196893
theorem B3905587 : Blo 2055435 3905587 := bstep (se 1 (by rfl) ⟨2929190, by rfl⟩ : syracuseStep 3905587 = 5858381) B5858381
theorem B5207449 : Blo 2055435 5207449 := bstep (se 2 (by rfl) ⟨1952793, by rfl⟩ : syracuseStep 5207449 = 3905587) B3905587
theorem B6943265 : Blo 2055435 6943265 := bstep (se 2 (by rfl) ⟨2603724, by rfl⟩ : syracuseStep 6943265 = 5207449) B5207449
theorem B4628843 : Blo 2055435 4628843 := bstep (se 1 (by rfl) ⟨3471632, by rfl⟩ : syracuseStep 4628843 = 6943265) B6943265
theorem B3085895 : Blo 2055435 3085895 := bstep (se 1 (by rfl) ⟨2314421, by rfl⟩ : syracuseStep 3085895 = 4628843) B4628843
theorem B2057263 : Blo 2055435 2057263 := bstep (se 1 (by rfl) ⟨1542947, by rfl⟩ : syracuseStep 2057263 = 3085895) B3085895
theorem B3085901 : Blo 2055435 3085901 := bbase (se 3 (by rfl) ⟨578606, by rfl⟩ : syracuseStep 3085901 = 1157213) (by norm_num)
theorem B2057267 : Blo 2055435 2057267 := bstep (se 1 (by rfl) ⟨1542950, by rfl⟩ : syracuseStep 2057267 = 3085901) B3085901
theorem B4628861 : Blo 2055435 4628861 := bbase (se 3 (by rfl) ⟨867911, by rfl⟩ : syracuseStep 4628861 = 1735823) (by norm_num)
theorem B3085907 : Blo 2055435 3085907 := bstep (se 1 (by rfl) ⟨2314430, by rfl⟩ : syracuseStep 3085907 = 4628861) B4628861
theorem B2057271 : Blo 2055435 2057271 := bstep (se 1 (by rfl) ⟨1542953, by rfl⟩ : syracuseStep 2057271 = 3085907) B3085907
theorem B3471653 : Blo 2055435 3471653 := bbase (se 4 (by rfl) ⟨325467, by rfl⟩ : syracuseStep 3471653 = 650935) (by norm_num)
theorem B2314435 : Blo 2055435 2314435 := bstep (se 1 (by rfl) ⟨1735826, by rfl⟩ : syracuseStep 2314435 = 3471653) B3471653
theorem B3085913 : Blo 2055435 3085913 := bstep (se 2 (by rfl) ⟨1157217, by rfl⟩ : syracuseStep 3085913 = 2314435) B2314435
theorem B2057275 : Blo 2055435 2057275 := bstep (se 1 (by rfl) ⟨1542956, by rfl⟩ : syracuseStep 2057275 = 3085913) B3085913
theorem B2929213 : Blo 2055435 2929213 := bbase (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) (by norm_num)
theorem B15622469 : Blo 2055435 15622469 := bstep (se 4 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 15622469 = 2929213) B2929213
theorem B10414979 : Blo 2055435 10414979 := bstep (se 1 (by rfl) ⟨7811234, by rfl⟩ : syracuseStep 10414979 = 15622469) B15622469
theorem B6943319 : Blo 2055435 6943319 := bstep (se 1 (by rfl) ⟨5207489, by rfl⟩ : syracuseStep 6943319 = 10414979) B10414979
theorem B4628879 : Blo 2055435 4628879 := bstep (se 1 (by rfl) ⟨3471659, by rfl⟩ : syracuseStep 4628879 = 6943319) B6943319
theorem B3085919 : Blo 2055435 3085919 := bstep (se 1 (by rfl) ⟨2314439, by rfl⟩ : syracuseStep 3085919 = 4628879) B4628879
theorem B2057279 : Blo 2055435 2057279 := bstep (se 1 (by rfl) ⟨1542959, by rfl⟩ : syracuseStep 2057279 = 3085919) B3085919
theorem B3085925 : Blo 2055435 3085925 := bbase (se 4 (by rfl) ⟨289305, by rfl⟩ : syracuseStep 3085925 = 578611) (by norm_num)
theorem B2057283 : Blo 2055435 2057283 := bstep (se 1 (by rfl) ⟨1542962, by rfl⟩ : syracuseStep 2057283 = 3085925) B3085925
theorem B4943069 : Blo 2055435 4943069 := bbase (se 3 (by rfl) ⟨926825, by rfl⟩ : syracuseStep 4943069 = 1853651) (by norm_num)
theorem B3295379 : Blo 2055435 3295379 := bstep (se 1 (by rfl) ⟨2471534, by rfl⟩ : syracuseStep 3295379 = 4943069) B4943069
theorem B2196919 : Blo 2055435 2196919 := bstep (se 1 (by rfl) ⟨1647689, by rfl⟩ : syracuseStep 2196919 = 3295379) B3295379
theorem B2929225 : Blo 2055435 2929225 := bstep (se 2 (by rfl) ⟨1098459, by rfl⟩ : syracuseStep 2929225 = 2196919) B2196919
theorem B3905633 : Blo 2055435 3905633 := bstep (se 2 (by rfl) ⟨1464612, by rfl⟩ : syracuseStep 3905633 = 2929225) B2929225
theorem B2603755 : Blo 2055435 2603755 := bstep (se 1 (by rfl) ⟨1952816, by rfl⟩ : syracuseStep 2603755 = 3905633) B3905633
theorem B3471673 : Blo 2055435 3471673 := bstep (se 2 (by rfl) ⟨1301877, by rfl⟩ : syracuseStep 3471673 = 2603755) B2603755
theorem B4628897 : Blo 2055435 4628897 := bstep (se 2 (by rfl) ⟨1735836, by rfl⟩ : syracuseStep 4628897 = 3471673) B3471673
theorem B3085931 : Blo 2055435 3085931 := bstep (se 1 (by rfl) ⟨2314448, by rfl⟩ : syracuseStep 3085931 = 4628897) B4628897
theorem B2057287 : Blo 2055435 2057287 := bstep (se 1 (by rfl) ⟨1542965, by rfl⟩ : syracuseStep 2057287 = 3085931) B3085931
theorem B2314453 : Blo 2055435 2314453 := bbase (se 7 (by rfl) ⟨27122, by rfl⟩ : syracuseStep 2314453 = 54245) (by norm_num)
theorem B3085937 : Blo 2055435 3085937 := bstep (se 2 (by rfl) ⟨1157226, by rfl⟩ : syracuseStep 3085937 = 2314453) B2314453
theorem B2057291 : Blo 2055435 2057291 := bstep (se 1 (by rfl) ⟨1542968, by rfl⟩ : syracuseStep 2057291 = 3085937) B3085937
theorem B2603765 : Blo 2055435 2603765 := bbase (se 5 (by rfl) ⟨122051, by rfl⟩ : syracuseStep 2603765 = 244103) (by norm_num)
theorem B6943373 : Blo 2055435 6943373 := bstep (se 3 (by rfl) ⟨1301882, by rfl⟩ : syracuseStep 6943373 = 2603765) B2603765
theorem B4628915 : Blo 2055435 4628915 := bstep (se 1 (by rfl) ⟨3471686, by rfl⟩ : syracuseStep 4628915 = 6943373) B6943373
theorem B3085943 : Blo 2055435 3085943 := bstep (se 1 (by rfl) ⟨2314457, by rfl⟩ : syracuseStep 3085943 = 4628915) B4628915
theorem B2057295 : Blo 2055435 2057295 := bstep (se 1 (by rfl) ⟨1542971, by rfl⟩ : syracuseStep 2057295 = 3085943) B3085943
theorem B3085949 : Blo 2055435 3085949 := bbase (se 3 (by rfl) ⟨578615, by rfl⟩ : syracuseStep 3085949 = 1157231) (by norm_num)
theorem B2057299 : Blo 2055435 2057299 := bstep (se 1 (by rfl) ⟨1542974, by rfl⟩ : syracuseStep 2057299 = 3085949) B3085949
theorem B4628933 : Blo 2055435 4628933 := bbase (se 4 (by rfl) ⟨433962, by rfl⟩ : syracuseStep 4628933 = 867925) (by norm_num)
theorem B3085955 : Blo 2055435 3085955 := bstep (se 1 (by rfl) ⟨2314466, by rfl⟩ : syracuseStep 3085955 = 4628933) B4628933
theorem B2057303 : Blo 2055435 2057303 := bstep (se 1 (by rfl) ⟨1542977, by rfl⟩ : syracuseStep 2057303 = 3085955) B3085955
theorem B6590821 : Blo 2055435 6590821 := bbase (se 4 (by rfl) ⟨617889, by rfl⟩ : syracuseStep 6590821 = 1235779) (by norm_num)
theorem B8787761 : Blo 2055435 8787761 := bstep (se 2 (by rfl) ⟨3295410, by rfl⟩ : syracuseStep 8787761 = 6590821) B6590821
theorem B5858507 : Blo 2055435 5858507 := bstep (se 1 (by rfl) ⟨4393880, by rfl⟩ : syracuseStep 5858507 = 8787761) B8787761
theorem B3905671 : Blo 2055435 3905671 := bstep (se 1 (by rfl) ⟨2929253, by rfl⟩ : syracuseStep 3905671 = 5858507) B5858507
theorem B5207561 : Blo 2055435 5207561 := bstep (se 2 (by rfl) ⟨1952835, by rfl⟩ : syracuseStep 5207561 = 3905671) B3905671
theorem B3471707 : Blo 2055435 3471707 := bstep (se 1 (by rfl) ⟨2603780, by rfl⟩ : syracuseStep 3471707 = 5207561) B5207561
theorem B2314471 : Blo 2055435 2314471 := bstep (se 1 (by rfl) ⟨1735853, by rfl⟩ : syracuseStep 2314471 = 3471707) B3471707
theorem B3085961 : Blo 2055435 3085961 := bstep (se 2 (by rfl) ⟨1157235, by rfl⟩ : syracuseStep 3085961 = 2314471) B2314471
theorem B2057307 : Blo 2055435 2057307 := bstep (se 1 (by rfl) ⟨1542980, by rfl⟩ : syracuseStep 2057307 = 3085961) B3085961
theorem B10415141 : Blo 2055435 10415141 := bbase (se 4 (by rfl) ⟨976419, by rfl⟩ : syracuseStep 10415141 = 1952839) (by norm_num)
theorem B6943427 : Blo 2055435 6943427 := bstep (se 1 (by rfl) ⟨5207570, by rfl⟩ : syracuseStep 6943427 = 10415141) B10415141
theorem B4628951 : Blo 2055435 4628951 := bstep (se 1 (by rfl) ⟨3471713, by rfl⟩ : syracuseStep 4628951 = 6943427) B6943427
theorem B3085967 : Blo 2055435 3085967 := bstep (se 1 (by rfl) ⟨2314475, by rfl⟩ : syracuseStep 3085967 = 4628951) B4628951
theorem B2057311 : Blo 2055435 2057311 := bstep (se 1 (by rfl) ⟨1542983, by rfl⟩ : syracuseStep 2057311 = 3085967) B3085967
theorem B3085973 : Blo 2055435 3085973 := bbase (se 6 (by rfl) ⟨72327, by rfl⟩ : syracuseStep 3085973 = 144655) (by norm_num)
theorem B2057315 : Blo 2055435 2057315 := bstep (se 1 (by rfl) ⟨1542986, by rfl⟩ : syracuseStep 2057315 = 3085973) B3085973
theorem B13181717 : Blo 2055435 13181717 := bbase (se 6 (by rfl) ⟨308946, by rfl⟩ : syracuseStep 13181717 = 617893) (by norm_num)
theorem B8787811 : Blo 2055435 8787811 := bstep (se 1 (by rfl) ⟨6590858, by rfl⟩ : syracuseStep 8787811 = 13181717) B13181717
theorem B11717081 : Blo 2055435 11717081 := bstep (se 2 (by rfl) ⟨4393905, by rfl⟩ : syracuseStep 11717081 = 8787811) B8787811
theorem B7811387 : Blo 2055435 7811387 := bstep (se 1 (by rfl) ⟨5858540, by rfl⟩ : syracuseStep 7811387 = 11717081) B11717081
theorem B5207591 : Blo 2055435 5207591 := bstep (se 1 (by rfl) ⟨3905693, by rfl⟩ : syracuseStep 5207591 = 7811387) B7811387
theorem B3471727 : Blo 2055435 3471727 := bstep (se 1 (by rfl) ⟨2603795, by rfl⟩ : syracuseStep 3471727 = 5207591) B5207591
theorem B4628969 : Blo 2055435 4628969 := bstep (se 2 (by rfl) ⟨1735863, by rfl⟩ : syracuseStep 4628969 = 3471727) B3471727
theorem B3085979 : Blo 2055435 3085979 := bstep (se 1 (by rfl) ⟨2314484, by rfl⟩ : syracuseStep 3085979 = 4628969) B4628969
theorem B2057319 : Blo 2055435 2057319 := bstep (se 1 (by rfl) ⟨1542989, by rfl⟩ : syracuseStep 2057319 = 3085979) B3085979
theorem B2314489 : Blo 2055435 2314489 := bbase (se 2 (by rfl) ⟨867933, by rfl⟩ : syracuseStep 2314489 = 1735867) (by norm_num)
theorem B3085985 : Blo 2055435 3085985 := bstep (se 2 (by rfl) ⟨1157244, by rfl⟩ : syracuseStep 3085985 = 2314489) B2314489
theorem B2057323 : Blo 2055435 2057323 := bstep (se 1 (by rfl) ⟨1542992, by rfl⟩ : syracuseStep 2057323 = 3085985) B3085985
theorem B8787845 : Blo 2055435 8787845 := bbase (se 4 (by rfl) ⟨823860, by rfl⟩ : syracuseStep 8787845 = 1647721) (by norm_num)
theorem B5858563 : Blo 2055435 5858563 := bstep (se 1 (by rfl) ⟨4393922, by rfl⟩ : syracuseStep 5858563 = 8787845) B8787845
theorem B7811417 : Blo 2055435 7811417 := bstep (se 2 (by rfl) ⟨2929281, by rfl⟩ : syracuseStep 7811417 = 5858563) B5858563
theorem B5207611 : Blo 2055435 5207611 := bstep (se 1 (by rfl) ⟨3905708, by rfl⟩ : syracuseStep 5207611 = 7811417) B7811417
theorem B6943481 : Blo 2055435 6943481 := bstep (se 2 (by rfl) ⟨2603805, by rfl⟩ : syracuseStep 6943481 = 5207611) B5207611
theorem B4628987 : Blo 2055435 4628987 := bstep (se 1 (by rfl) ⟨3471740, by rfl⟩ : syracuseStep 4628987 = 6943481) B6943481
theorem B3085991 : Blo 2055435 3085991 := bstep (se 1 (by rfl) ⟨2314493, by rfl⟩ : syracuseStep 3085991 = 4628987) B4628987
theorem B2057327 : Blo 2055435 2057327 := bstep (se 1 (by rfl) ⟨1542995, by rfl⟩ : syracuseStep 2057327 = 3085991) B3085991
theorem B3085997 : Blo 2055435 3085997 := bbase (se 3 (by rfl) ⟨578624, by rfl⟩ : syracuseStep 3085997 = 1157249) (by norm_num)
theorem B2057331 : Blo 2055435 2057331 := bstep (se 1 (by rfl) ⟨1542998, by rfl⟩ : syracuseStep 2057331 = 3085997) B3085997
theorem B4629005 : Blo 2055435 4629005 := bbase (se 3 (by rfl) ⟨867938, by rfl⟩ : syracuseStep 4629005 = 1735877) (by norm_num)
theorem B3086003 : Blo 2055435 3086003 := bstep (se 1 (by rfl) ⟨2314502, by rfl⟩ : syracuseStep 3086003 = 4629005) B4629005
theorem B2057335 : Blo 2055435 2057335 := bstep (se 1 (by rfl) ⟨1543001, by rfl⟩ : syracuseStep 2057335 = 3086003) B3086003
theorem B2603821 : Blo 2055435 2603821 := bbase (se 3 (by rfl) ⟨488216, by rfl⟩ : syracuseStep 2603821 = 976433) (by norm_num)
theorem B3471761 : Blo 2055435 3471761 := bstep (se 2 (by rfl) ⟨1301910, by rfl⟩ : syracuseStep 3471761 = 2603821) B2603821
theorem B2314507 : Blo 2055435 2314507 := bstep (se 1 (by rfl) ⟨1735880, by rfl⟩ : syracuseStep 2314507 = 3471761) B3471761
theorem B3086009 : Blo 2055435 3086009 := bstep (se 2 (by rfl) ⟨1157253, by rfl⟩ : syracuseStep 3086009 = 2314507) B2314507
theorem B2057339 : Blo 2055435 2057339 := bstep (se 1 (by rfl) ⟨1543004, by rfl⟩ : syracuseStep 2057339 = 3086009) B3086009
theorem B4692181 : Blo 2055435 4692181 := bbase (se 7 (by rfl) ⟨54986, by rfl⟩ : syracuseStep 4692181 = 109973) (by norm_num)
theorem B6256241 : Blo 2055435 6256241 := bstep (se 2 (by rfl) ⟨2346090, by rfl⟩ : syracuseStep 6256241 = 4692181) B4692181
theorem B4170827 : Blo 2055435 4170827 := bstep (se 1 (by rfl) ⟨3128120, by rfl⟩ : syracuseStep 4170827 = 6256241) B6256241
theorem B2780551 : Blo 2055435 2780551 := bstep (se 1 (by rfl) ⟨2085413, by rfl⟩ : syracuseStep 2780551 = 4170827) B4170827
theorem B3707401 : Blo 2055435 3707401 := bstep (se 2 (by rfl) ⟨1390275, by rfl⟩ : syracuseStep 3707401 = 2780551) B2780551
theorem B4943201 : Blo 2055435 4943201 := bstep (se 2 (by rfl) ⟨1853700, by rfl⟩ : syracuseStep 4943201 = 3707401) B3707401
theorem B13181869 : Blo 2055435 13181869 := bstep (se 3 (by rfl) ⟨2471600, by rfl⟩ : syracuseStep 13181869 = 4943201) B4943201
theorem B17575825 : Blo 2055435 17575825 := bstep (se 2 (by rfl) ⟨6590934, by rfl⟩ : syracuseStep 17575825 = 13181869) B13181869
theorem B23434433 : Blo 2055435 23434433 := bstep (se 2 (by rfl) ⟨8787912, by rfl⟩ : syracuseStep 23434433 = 17575825) B17575825
theorem B15622955 : Blo 2055435 15622955 := bstep (se 1 (by rfl) ⟨11717216, by rfl⟩ : syracuseStep 15622955 = 23434433) B23434433
theorem B10415303 : Blo 2055435 10415303 := bstep (se 1 (by rfl) ⟨7811477, by rfl⟩ : syracuseStep 10415303 = 15622955) B15622955
theorem B6943535 : Blo 2055435 6943535 := bstep (se 1 (by rfl) ⟨5207651, by rfl⟩ : syracuseStep 6943535 = 10415303) B10415303
theorem B4629023 : Blo 2055435 4629023 := bstep (se 1 (by rfl) ⟨3471767, by rfl⟩ : syracuseStep 4629023 = 6943535) B6943535
theorem B3086015 : Blo 2055435 3086015 := bstep (se 1 (by rfl) ⟨2314511, by rfl⟩ : syracuseStep 3086015 = 4629023) B4629023
theorem B2057343 : Blo 2055435 2057343 := bstep (se 1 (by rfl) ⟨1543007, by rfl⟩ : syracuseStep 2057343 = 3086015) B3086015
theorem B3086021 : Blo 2055435 3086021 := bbase (se 4 (by rfl) ⟨289314, by rfl⟩ : syracuseStep 3086021 = 578629) (by norm_num)
theorem B2057347 : Blo 2055435 2057347 := bstep (se 1 (by rfl) ⟨1543010, by rfl⟩ : syracuseStep 2057347 = 3086021) B3086021
theorem B3471781 : Blo 2055435 3471781 := bbase (se 4 (by rfl) ⟨325479, by rfl⟩ : syracuseStep 3471781 = 650959) (by norm_num)
theorem B4629041 : Blo 2055435 4629041 := bstep (se 2 (by rfl) ⟨1735890, by rfl⟩ : syracuseStep 4629041 = 3471781) B3471781
theorem B3086027 : Blo 2055435 3086027 := bstep (se 1 (by rfl) ⟨2314520, by rfl⟩ : syracuseStep 3086027 = 4629041) B4629041
theorem B2057351 : Blo 2055435 2057351 := bstep (se 1 (by rfl) ⟨1543013, by rfl⟩ : syracuseStep 2057351 = 3086027) B3086027
theorem B2314525 : Blo 2055435 2314525 := bbase (se 3 (by rfl) ⟨433973, by rfl⟩ : syracuseStep 2314525 = 867947) (by norm_num)
theorem B3086033 : Blo 2055435 3086033 := bstep (se 2 (by rfl) ⟨1157262, by rfl⟩ : syracuseStep 3086033 = 2314525) B2314525
theorem B2057355 : Blo 2055435 2057355 := bstep (se 1 (by rfl) ⟨1543016, by rfl⟩ : syracuseStep 2057355 = 3086033) B3086033
theorem B6943589 : Blo 2055435 6943589 := bbase (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) (by norm_num)
theorem B4629059 : Blo 2055435 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B3086039 : Blo 2055435 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B2057359 : Blo 2055435 2057359 := bstep (se 1 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 2057359 = 3086039) B3086039
theorem B3086045 : Blo 2055435 3086045 := bbase (se 3 (by rfl) ⟨578633, by rfl⟩ : syracuseStep 3086045 = 1157267) (by norm_num)
theorem B2057363 : Blo 2055435 2057363 := bstep (se 1 (by rfl) ⟨1543022, by rfl⟩ : syracuseStep 2057363 = 3086045) B3086045
theorem B4629077 : Blo 2055435 4629077 := bbase (se 8 (by rfl) ⟨27123, by rfl⟩ : syracuseStep 4629077 = 54247) (by norm_num)
theorem B3086051 : Blo 2055435 3086051 := bstep (se 1 (by rfl) ⟨2314538, by rfl⟩ : syracuseStep 3086051 = 4629077) B4629077
theorem B2057367 : Blo 2055435 2057367 := bstep (se 1 (by rfl) ⟨1543025, by rfl⟩ : syracuseStep 2057367 = 3086051) B3086051
theorem B3707453 : Blo 2055435 3707453 := bbase (se 3 (by rfl) ⟨695147, by rfl⟩ : syracuseStep 3707453 = 1390295) (by norm_num)
theorem B2471635 : Blo 2055435 2471635 := bstep (se 1 (by rfl) ⟨1853726, by rfl⟩ : syracuseStep 2471635 = 3707453) B3707453
theorem B3295513 : Blo 2055435 3295513 := bstep (se 2 (by rfl) ⟨1235817, by rfl⟩ : syracuseStep 3295513 = 2471635) B2471635
theorem B4394017 : Blo 2055435 4394017 := bstep (se 2 (by rfl) ⟨1647756, by rfl⟩ : syracuseStep 4394017 = 3295513) B3295513
theorem B5858689 : Blo 2055435 5858689 := bstep (se 2 (by rfl) ⟨2197008, by rfl⟩ : syracuseStep 5858689 = 4394017) B4394017
theorem B7811585 : Blo 2055435 7811585 := bstep (se 2 (by rfl) ⟨2929344, by rfl⟩ : syracuseStep 7811585 = 5858689) B5858689
theorem B5207723 : Blo 2055435 5207723 := bstep (se 1 (by rfl) ⟨3905792, by rfl⟩ : syracuseStep 5207723 = 7811585) B7811585
theorem B3471815 : Blo 2055435 3471815 := bstep (se 1 (by rfl) ⟨2603861, by rfl⟩ : syracuseStep 3471815 = 5207723) B5207723
theorem B2314543 : Blo 2055435 2314543 := bstep (se 1 (by rfl) ⟨1735907, by rfl⟩ : syracuseStep 2314543 = 3471815) B3471815
theorem B3086057 : Blo 2055435 3086057 := bstep (se 2 (by rfl) ⟨1157271, by rfl⟩ : syracuseStep 3086057 = 2314543) B2314543
theorem B2057371 : Blo 2055435 2057371 := bstep (se 1 (by rfl) ⟨1543028, by rfl⟩ : syracuseStep 2057371 = 3086057) B3086057
theorem B5561189 : Blo 2055435 5561189 := bbase (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) (by norm_num)
theorem B3707459 : Blo 2055435 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B2471639 : Blo 2055435 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B26364149 : Blo 2055435 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B17576099 : Blo 2055435 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B11717399 : Blo 2055435 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B7811599 : Blo 2055435 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B10415465 : Blo 2055435 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B6943643 : Blo 2055435 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B4629095 : Blo 2055435 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B3086063 : Blo 2055435 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B2057375 : Blo 2055435 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B3086069 : Blo 2055435 3086069 := bbase (se 5 (by rfl) ⟨144659, by rfl⟩ : syracuseStep 3086069 = 289319) (by norm_num)
theorem B2057379 : Blo 2055435 2057379 := bstep (se 1 (by rfl) ⟨1543034, by rfl⟩ : syracuseStep 2057379 = 3086069) B3086069
theorem B8788085 : Blo 2055435 8788085 := bbase (se 5 (by rfl) ⟨411941, by rfl⟩ : syracuseStep 8788085 = 823883) (by norm_num)
theorem B5858723 : Blo 2055435 5858723 := bstep (se 1 (by rfl) ⟨4394042, by rfl⟩ : syracuseStep 5858723 = 8788085) B8788085
theorem B3905815 : Blo 2055435 3905815 := bstep (se 1 (by rfl) ⟨2929361, by rfl⟩ : syracuseStep 3905815 = 5858723) B5858723
theorem B5207753 : Blo 2055435 5207753 := bstep (se 2 (by rfl) ⟨1952907, by rfl⟩ : syracuseStep 5207753 = 3905815) B3905815
theorem B3471835 : Blo 2055435 3471835 := bstep (se 1 (by rfl) ⟨2603876, by rfl⟩ : syracuseStep 3471835 = 5207753) B5207753
theorem B4629113 : Blo 2055435 4629113 := bstep (se 2 (by rfl) ⟨1735917, by rfl⟩ : syracuseStep 4629113 = 3471835) B3471835
theorem B3086075 : Blo 2055435 3086075 := bstep (se 1 (by rfl) ⟨2314556, by rfl⟩ : syracuseStep 3086075 = 4629113) B4629113
theorem B2057383 : Blo 2055435 2057383 := bstep (se 1 (by rfl) ⟨1543037, by rfl⟩ : syracuseStep 2057383 = 3086075) B3086075
theorem B2314561 : Blo 2055435 2314561 := bbase (se 2 (by rfl) ⟨867960, by rfl⟩ : syracuseStep 2314561 = 1735921) (by norm_num)
theorem B3086081 : Blo 2055435 3086081 := bstep (se 2 (by rfl) ⟨1157280, by rfl⟩ : syracuseStep 3086081 = 2314561) B2314561
theorem B2057387 : Blo 2055435 2057387 := bstep (se 1 (by rfl) ⟨1543040, by rfl⟩ : syracuseStep 2057387 = 3086081) B3086081
theorem B5207773 : Blo 2055435 5207773 := bbase (se 3 (by rfl) ⟨976457, by rfl⟩ : syracuseStep 5207773 = 1952915) (by norm_num)
theorem B6943697 : Blo 2055435 6943697 := bstep (se 2 (by rfl) ⟨2603886, by rfl⟩ : syracuseStep 6943697 = 5207773) B5207773
theorem B4629131 : Blo 2055435 4629131 := bstep (se 1 (by rfl) ⟨3471848, by rfl⟩ : syracuseStep 4629131 = 6943697) B6943697
theorem B3086087 : Blo 2055435 3086087 := bstep (se 1 (by rfl) ⟨2314565, by rfl⟩ : syracuseStep 3086087 = 4629131) B4629131
theorem B2057391 : Blo 2055435 2057391 := bstep (se 1 (by rfl) ⟨1543043, by rfl⟩ : syracuseStep 2057391 = 3086087) B3086087
theorem B3086093 : Blo 2055435 3086093 := bbase (se 3 (by rfl) ⟨578642, by rfl⟩ : syracuseStep 3086093 = 1157285) (by norm_num)
theorem B2057395 : Blo 2055435 2057395 := bstep (se 1 (by rfl) ⟨1543046, by rfl⟩ : syracuseStep 2057395 = 3086093) B3086093
theorem B4629149 : Blo 2055435 4629149 := bbase (se 3 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 4629149 = 1735931) (by norm_num)
theorem B3086099 : Blo 2055435 3086099 := bstep (se 1 (by rfl) ⟨2314574, by rfl⟩ : syracuseStep 3086099 = 4629149) B4629149
theorem B2057399 : Blo 2055435 2057399 := bstep (se 1 (by rfl) ⟨1543049, by rfl⟩ : syracuseStep 2057399 = 3086099) B3086099
theorem B3471869 : Blo 2055435 3471869 := bbase (se 3 (by rfl) ⟨650975, by rfl⟩ : syracuseStep 3471869 = 1301951) (by norm_num)
theorem B2314579 : Blo 2055435 2314579 := bstep (se 1 (by rfl) ⟨1735934, by rfl⟩ : syracuseStep 2314579 = 3471869) B3471869
theorem B3086105 : Blo 2055435 3086105 := bstep (se 2 (by rfl) ⟨1157289, by rfl⟩ : syracuseStep 3086105 = 2314579) B2314579
theorem B2057403 : Blo 2055435 2057403 := bstep (se 1 (by rfl) ⟨1543052, by rfl⟩ : syracuseStep 2057403 = 3086105) B3086105
theorem B4394093 : Blo 2055435 4394093 := bbase (se 3 (by rfl) ⟨823892, by rfl⟩ : syracuseStep 4394093 = 1647785) (by norm_num)
theorem B11717581 : Blo 2055435 11717581 := bstep (se 3 (by rfl) ⟨2197046, by rfl⟩ : syracuseStep 11717581 = 4394093) B4394093
theorem B15623441 : Blo 2055435 15623441 := bstep (se 2 (by rfl) ⟨5858790, by rfl⟩ : syracuseStep 15623441 = 11717581) B11717581
theorem B10415627 : Blo 2055435 10415627 := bstep (se 1 (by rfl) ⟨7811720, by rfl⟩ : syracuseStep 10415627 = 15623441) B15623441
theorem B6943751 : Blo 2055435 6943751 := bstep (se 1 (by rfl) ⟨5207813, by rfl⟩ : syracuseStep 6943751 = 10415627) B10415627
theorem B4629167 : Blo 2055435 4629167 := bstep (se 1 (by rfl) ⟨3471875, by rfl⟩ : syracuseStep 4629167 = 6943751) B6943751
theorem B3086111 : Blo 2055435 3086111 := bstep (se 1 (by rfl) ⟨2314583, by rfl⟩ : syracuseStep 3086111 = 4629167) B4629167
theorem B2057407 : Blo 2055435 2057407 := bstep (se 1 (by rfl) ⟨1543055, by rfl⟩ : syracuseStep 2057407 = 3086111) B3086111
theorem B3086117 : Blo 2055435 3086117 := bbase (se 4 (by rfl) ⟨289323, by rfl⟩ : syracuseStep 3086117 = 578647) (by norm_num)
theorem B2057411 : Blo 2055435 2057411 := bstep (se 1 (by rfl) ⟨1543058, by rfl⟩ : syracuseStep 2057411 = 3086117) B3086117
theorem B2603917 : Blo 2055435 2603917 := bbase (se 3 (by rfl) ⟨488234, by rfl⟩ : syracuseStep 2603917 = 976469) (by norm_num)
theorem B3471889 : Blo 2055435 3471889 := bstep (se 2 (by rfl) ⟨1301958, by rfl⟩ : syracuseStep 3471889 = 2603917) B2603917
theorem B4629185 : Blo 2055435 4629185 := bstep (se 2 (by rfl) ⟨1735944, by rfl⟩ : syracuseStep 4629185 = 3471889) B3471889
theorem B3086123 : Blo 2055435 3086123 := bstep (se 1 (by rfl) ⟨2314592, by rfl⟩ : syracuseStep 3086123 = 4629185) B4629185
theorem B2057415 : Blo 2055435 2057415 := bstep (se 1 (by rfl) ⟨1543061, by rfl⟩ : syracuseStep 2057415 = 3086123) B3086123
theorem B2314597 : Blo 2055435 2314597 := bbase (se 4 (by rfl) ⟨216993, by rfl⟩ : syracuseStep 2314597 = 433987) (by norm_num)
theorem B3086129 : Blo 2055435 3086129 := bstep (se 2 (by rfl) ⟨1157298, by rfl⟩ : syracuseStep 3086129 = 2314597) B2314597
theorem B2057419 : Blo 2055435 2057419 := bstep (se 1 (by rfl) ⟨1543064, by rfl⟩ : syracuseStep 2057419 = 3086129) B3086129
theorem B5858837 : Blo 2055435 5858837 := bbase (se 6 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 5858837 = 274633) (by norm_num)
theorem B3905891 : Blo 2055435 3905891 := bstep (se 1 (by rfl) ⟨2929418, by rfl⟩ : syracuseStep 3905891 = 5858837) B5858837
theorem B2603927 : Blo 2055435 2603927 := bstep (se 1 (by rfl) ⟨1952945, by rfl⟩ : syracuseStep 2603927 = 3905891) B3905891
theorem B6943805 : Blo 2055435 6943805 := bstep (se 3 (by rfl) ⟨1301963, by rfl⟩ : syracuseStep 6943805 = 2603927) B2603927
theorem B4629203 : Blo 2055435 4629203 := bstep (se 1 (by rfl) ⟨3471902, by rfl⟩ : syracuseStep 4629203 = 6943805) B6943805
theorem B3086135 : Blo 2055435 3086135 := bstep (se 1 (by rfl) ⟨2314601, by rfl⟩ : syracuseStep 3086135 = 4629203) B4629203
theorem B2057423 : Blo 2055435 2057423 := bstep (se 1 (by rfl) ⟨1543067, by rfl⟩ : syracuseStep 2057423 = 3086135) B3086135
theorem B3086141 : Blo 2055435 3086141 := bbase (se 3 (by rfl) ⟨578651, by rfl⟩ : syracuseStep 3086141 = 1157303) (by norm_num)
theorem B2057427 : Blo 2055435 2057427 := bstep (se 1 (by rfl) ⟨1543070, by rfl⟩ : syracuseStep 2057427 = 3086141) B3086141
theorem B4629221 : Blo 2055435 4629221 := bbase (se 4 (by rfl) ⟨433989, by rfl⟩ : syracuseStep 4629221 = 867979) (by norm_num)
theorem B3086147 : Blo 2055435 3086147 := bstep (se 1 (by rfl) ⟨2314610, by rfl⟩ : syracuseStep 3086147 = 4629221) B4629221
theorem B2057431 : Blo 2055435 2057431 := bstep (se 1 (by rfl) ⟨1543073, by rfl⟩ : syracuseStep 2057431 = 3086147) B3086147
theorem B5207885 : Blo 2055435 5207885 := bbase (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) (by norm_num)
theorem B3471923 : Blo 2055435 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B2314615 : Blo 2055435 2314615 := bstep (se 1 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 2314615 = 3471923) B3471923
theorem B3086153 : Blo 2055435 3086153 := bstep (se 2 (by rfl) ⟨1157307, by rfl⟩ : syracuseStep 3086153 = 2314615) B2314615
theorem B2057435 : Blo 2055435 2057435 := bstep (se 1 (by rfl) ⟨1543076, by rfl⟩ : syracuseStep 2057435 = 3086153) B3086153
theorem C0 (j : ℕ) (h1 : 513858 ≤ j) (h2 : j ≤ 514358) : Blo 2055435 (4 * j + 3) := by
  interval_cases j
  · exact B2055435
  · exact B2055439
  · exact B2055443
  · exact B2055447
  · exact B2055451
  · exact B2055455
  · exact B2055459
  · exact B2055463
  · exact B2055467
  · exact B2055471
  · exact B2055475
  · exact B2055479
  · exact B2055483
  · exact B2055487
  · exact B2055491
  · exact B2055495
  · exact B2055499
  · exact B2055503
  · exact B2055507
  · exact B2055511
  · exact B2055515
  · exact B2055519
  · exact B2055523
  · exact B2055527
  · exact B2055531
  · exact B2055535
  · exact B2055539
  · exact B2055543
  · exact B2055547
  · exact B2055551
  · exact B2055555
  · exact B2055559
  · exact B2055563
  · exact B2055567
  · exact B2055571
  · exact B2055575
  · exact B2055579
  · exact B2055583
  · exact B2055587
  · exact B2055591
  · exact B2055595
  · exact B2055599
  · exact B2055603
  · exact B2055607
  · exact B2055611
  · exact B2055615
  · exact B2055619
  · exact B2055623
  · exact B2055627
  · exact B2055631
  · exact B2055635
  · exact B2055639
  · exact B2055643
  · exact B2055647
  · exact B2055651
  · exact B2055655
  · exact B2055659
  · exact B2055663
  · exact B2055667
  · exact B2055671
  · exact B2055675
  · exact B2055679
  · exact B2055683
  · exact B2055687
  · exact B2055691
  · exact B2055695
  · exact B2055699
  · exact B2055703
  · exact B2055707
  · exact B2055711
  · exact B2055715
  · exact B2055719
  · exact B2055723
  · exact B2055727
  · exact B2055731
  · exact B2055735
  · exact B2055739
  · exact B2055743
  · exact B2055747
  · exact B2055751
  · exact B2055755
  · exact B2055759
  · exact B2055763
  · exact B2055767
  · exact B2055771
  · exact B2055775
  · exact B2055779
  · exact B2055783
  · exact B2055787
  · exact B2055791
  · exact B2055795
  · exact B2055799
  · exact B2055803
  · exact B2055807
  · exact B2055811
  · exact B2055815
  · exact B2055819
  · exact B2055823
  · exact B2055827
  · exact B2055831
  · exact B2055835
  · exact B2055839
  · exact B2055843
  · exact B2055847
  · exact B2055851
  · exact B2055855
  · exact B2055859
  · exact B2055863
  · exact B2055867
  · exact B2055871
  · exact B2055875
  · exact B2055879
  · exact B2055883
  · exact B2055887
  · exact B2055891
  · exact B2055895
  · exact B2055899
  · exact B2055903
  · exact B2055907
  · exact B2055911
  · exact B2055915
  · exact B2055919
  · exact B2055923
  · exact B2055927
  · exact B2055931
  · exact B2055935
  · exact B2055939
  · exact B2055943
  · exact B2055947
  · exact B2055951
  · exact B2055955
  · exact B2055959
  · exact B2055963
  · exact B2055967
  · exact B2055971
  · exact B2055975
  · exact B2055979
  · exact B2055983
  · exact B2055987
  · exact B2055991
  · exact B2055995
  · exact B2055999
  · exact B2056003
  · exact B2056007
  · exact B2056011
  · exact B2056015
  · exact B2056019
  · exact B2056023
  · exact B2056027
  · exact B2056031
  · exact B2056035
  · exact B2056039
  · exact B2056043
  · exact B2056047
  · exact B2056051
  · exact B2056055
  · exact B2056059
  · exact B2056063
  · exact B2056067
  · exact B2056071
  · exact B2056075
  · exact B2056079
  · exact B2056083
  · exact B2056087
  · exact B2056091
  · exact B2056095
  · exact B2056099
  · exact B2056103
  · exact B2056107
  · exact B2056111
  · exact B2056115
  · exact B2056119
  · exact B2056123
  · exact B2056127
  · exact B2056131
  · exact B2056135
  · exact B2056139
  · exact B2056143
  · exact B2056147
  · exact B2056151
  · exact B2056155
  · exact B2056159
  · exact B2056163
  · exact B2056167
  · exact B2056171
  · exact B2056175
  · exact B2056179
  · exact B2056183
  · exact B2056187
  · exact B2056191
  · exact B2056195
  · exact B2056199
  · exact B2056203
  · exact B2056207
  · exact B2056211
  · exact B2056215
  · exact B2056219
  · exact B2056223
  · exact B2056227
  · exact B2056231
  · exact B2056235
  · exact B2056239
  · exact B2056243
  · exact B2056247
  · exact B2056251
  · exact B2056255
  · exact B2056259
  · exact B2056263
  · exact B2056267
  · exact B2056271
  · exact B2056275
  · exact B2056279
  · exact B2056283
  · exact B2056287
  · exact B2056291
  · exact B2056295
  · exact B2056299
  · exact B2056303
  · exact B2056307
  · exact B2056311
  · exact B2056315
  · exact B2056319
  · exact B2056323
  · exact B2056327
  · exact B2056331
  · exact B2056335
  · exact B2056339
  · exact B2056343
  · exact B2056347
  · exact B2056351
  · exact B2056355
  · exact B2056359
  · exact B2056363
  · exact B2056367
  · exact B2056371
  · exact B2056375
  · exact B2056379
  · exact B2056383
  · exact B2056387
  · exact B2056391
  · exact B2056395
  · exact B2056399
  · exact B2056403
  · exact B2056407
  · exact B2056411
  · exact B2056415
  · exact B2056419
  · exact B2056423
  · exact B2056427
  · exact B2056431
  · exact B2056435
  · exact B2056439
  · exact B2056443
  · exact B2056447
  · exact B2056451
  · exact B2056455
  · exact B2056459
  · exact B2056463
  · exact B2056467
  · exact B2056471
  · exact B2056475
  · exact B2056479
  · exact B2056483
  · exact B2056487
  · exact B2056491
  · exact B2056495
  · exact B2056499
  · exact B2056503
  · exact B2056507
  · exact B2056511
  · exact B2056515
  · exact B2056519
  · exact B2056523
  · exact B2056527
  · exact B2056531
  · exact B2056535
  · exact B2056539
  · exact B2056543
  · exact B2056547
  · exact B2056551
  · exact B2056555
  · exact B2056559
  · exact B2056563
  · exact B2056567
  · exact B2056571
  · exact B2056575
  · exact B2056579
  · exact B2056583
  · exact B2056587
  · exact B2056591
  · exact B2056595
  · exact B2056599
  · exact B2056603
  · exact B2056607
  · exact B2056611
  · exact B2056615
  · exact B2056619
  · exact B2056623
  · exact B2056627
  · exact B2056631
  · exact B2056635
  · exact B2056639
  · exact B2056643
  · exact B2056647
  · exact B2056651
  · exact B2056655
  · exact B2056659
  · exact B2056663
  · exact B2056667
  · exact B2056671
  · exact B2056675
  · exact B2056679
  · exact B2056683
  · exact B2056687
  · exact B2056691
  · exact B2056695
  · exact B2056699
  · exact B2056703
  · exact B2056707
  · exact B2056711
  · exact B2056715
  · exact B2056719
  · exact B2056723
  · exact B2056727
  · exact B2056731
  · exact B2056735
  · exact B2056739
  · exact B2056743
  · exact B2056747
  · exact B2056751
  · exact B2056755
  · exact B2056759
  · exact B2056763
  · exact B2056767
  · exact B2056771
  · exact B2056775
  · exact B2056779
  · exact B2056783
  · exact B2056787
  · exact B2056791
  · exact B2056795
  · exact B2056799
  · exact B2056803
  · exact B2056807
  · exact B2056811
  · exact B2056815
  · exact B2056819
  · exact B2056823
  · exact B2056827
  · exact B2056831
  · exact B2056835
  · exact B2056839
  · exact B2056843
  · exact B2056847
  · exact B2056851
  · exact B2056855
  · exact B2056859
  · exact B2056863
  · exact B2056867
  · exact B2056871
  · exact B2056875
  · exact B2056879
  · exact B2056883
  · exact B2056887
  · exact B2056891
  · exact B2056895
  · exact B2056899
  · exact B2056903
  · exact B2056907
  · exact B2056911
  · exact B2056915
  · exact B2056919
  · exact B2056923
  · exact B2056927
  · exact B2056931
  · exact B2056935
  · exact B2056939
  · exact B2056943
  · exact B2056947
  · exact B2056951
  · exact B2056955
  · exact B2056959
  · exact B2056963
  · exact B2056967
  · exact B2056971
  · exact B2056975
  · exact B2056979
  · exact B2056983
  · exact B2056987
  · exact B2056991
  · exact B2056995
  · exact B2056999
  · exact B2057003
  · exact B2057007
  · exact B2057011
  · exact B2057015
  · exact B2057019
  · exact B2057023
  · exact B2057027
  · exact B2057031
  · exact B2057035
  · exact B2057039
  · exact B2057043
  · exact B2057047
  · exact B2057051
  · exact B2057055
  · exact B2057059
  · exact B2057063
  · exact B2057067
  · exact B2057071
  · exact B2057075
  · exact B2057079
  · exact B2057083
  · exact B2057087
  · exact B2057091
  · exact B2057095
  · exact B2057099
  · exact B2057103
  · exact B2057107
  · exact B2057111
  · exact B2057115
  · exact B2057119
  · exact B2057123
  · exact B2057127
  · exact B2057131
  · exact B2057135
  · exact B2057139
  · exact B2057143
  · exact B2057147
  · exact B2057151
  · exact B2057155
  · exact B2057159
  · exact B2057163
  · exact B2057167
  · exact B2057171
  · exact B2057175
  · exact B2057179
  · exact B2057183
  · exact B2057187
  · exact B2057191
  · exact B2057195
  · exact B2057199
  · exact B2057203
  · exact B2057207
  · exact B2057211
  · exact B2057215
  · exact B2057219
  · exact B2057223
  · exact B2057227
  · exact B2057231
  · exact B2057235
  · exact B2057239
  · exact B2057243
  · exact B2057247
  · exact B2057251
  · exact B2057255
  · exact B2057259
  · exact B2057263
  · exact B2057267
  · exact B2057271
  · exact B2057275
  · exact B2057279
  · exact B2057283
  · exact B2057287
  · exact B2057291
  · exact B2057295
  · exact B2057299
  · exact B2057303
  · exact B2057307
  · exact B2057311
  · exact B2057315
  · exact B2057319
  · exact B2057323
  · exact B2057327
  · exact B2057331
  · exact B2057335
  · exact B2057339
  · exact B2057343
  · exact B2057347
  · exact B2057351
  · exact B2057355
  · exact B2057359
  · exact B2057363
  · exact B2057367
  · exact B2057371
  · exact B2057375
  · exact B2057379
  · exact B2057383
  · exact B2057387
  · exact B2057391
  · exact B2057395
  · exact B2057399
  · exact B2057403
  · exact B2057407
  · exact B2057411
  · exact B2057415
  · exact B2057419
  · exact B2057423
  · exact B2057427
  · exact B2057431
  · exact B2057435
theorem solution (m : ℕ) (hlo : 2055435 ≤ m) (hhi : m ≤ 2057435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 513858 ≤ j := by omega
    have hj2 : j ≤ 514358 := by omega
    have hb : Blo 2055435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
