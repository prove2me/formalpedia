-- Prove2me | solution 1 for syracuse_descends_range_1674037_1676037
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:21:24.922131+00:00
-- url     : https://prove2.me/submissions/efcd281e-f794-4c6a-ba57-135e98513d2b

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


theorem B2826245 : Blo 1674037 2826245 := bbase (se 4 (by rfl) ⟨264960, by rfl⟩ : syracuseStep 2826245 = 529921) (by norm_num)
theorem B1884181 : Blo 1674037 1884181 := bbase (se 6 (by rfl) ⟨44160, by rfl⟩ : syracuseStep 1884181 = 88321) (by norm_num)
theorem B10731541 : Blo 1674037 10731541 := bbase (se 6 (by rfl) ⟨251520, by rfl⟩ : syracuseStep 10731541 = 503041) (by norm_num)
theorem B4767797 : Blo 1674037 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B2039861 : Blo 1674037 2039861 := bbase (se 5 (by rfl) ⟨95618, by rfl⟩ : syracuseStep 2039861 = 191237) (by norm_num)
theorem B1884217 : Blo 1674037 1884217 := bbase (se 2 (by rfl) ⟨706581, by rfl⟩ : syracuseStep 1884217 = 1413163) (by norm_num)
theorem B2383933 : Blo 1674037 2383933 := bbase (se 3 (by rfl) ⟨446987, by rfl⟩ : syracuseStep 2383933 = 893975) (by norm_num)
theorem B3768389 : Blo 1674037 3768389 := bbase (se 4 (by rfl) ⟨353286, by rfl⟩ : syracuseStep 3768389 = 706573) (by norm_num)
theorem B1884253 : Blo 1674037 1884253 := bbase (se 3 (by rfl) ⟨353297, by rfl⟩ : syracuseStep 1884253 = 706595) (by norm_num)
theorem B1884289 : Blo 1674037 1884289 := bbase (se 2 (by rfl) ⟨706608, by rfl⟩ : syracuseStep 1884289 = 1413217) (by norm_num)
theorem B2826373 : Blo 1674037 2826373 := bbase (se 4 (by rfl) ⟨264972, by rfl⟩ : syracuseStep 2826373 = 529945) (by norm_num)
theorem B3768461 : Blo 1674037 3768461 := bbase (se 3 (by rfl) ⟨706586, by rfl⟩ : syracuseStep 3768461 = 1413173) (by norm_num)
theorem B1884325 : Blo 1674037 1884325 := bbase (se 4 (by rfl) ⟨176655, by rfl⟩ : syracuseStep 1884325 = 353311) (by norm_num)
theorem B8478917 : Blo 1674037 8478917 := bbase (se 4 (by rfl) ⟨794898, by rfl⟩ : syracuseStep 8478917 = 1589797) (by norm_num)
theorem B1884361 : Blo 1674037 1884361 := bbase (se 2 (by rfl) ⟨706635, by rfl⟩ : syracuseStep 1884361 = 1413271) (by norm_num)
theorem B3768533 : Blo 1674037 3768533 := bbase (se 7 (by rfl) ⟨44162, by rfl⟩ : syracuseStep 3768533 = 88325) (by norm_num)
theorem B2826461 : Blo 1674037 2826461 := bbase (se 3 (by rfl) ⟨529961, by rfl⟩ : syracuseStep 2826461 = 1059923) (by norm_num)
theorem B1884397 : Blo 1674037 1884397 := bbase (se 3 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 1884397 = 706649) (by norm_num)
theorem B1884433 : Blo 1674037 1884433 := bbase (se 2 (by rfl) ⟨706662, by rfl⟩ : syracuseStep 1884433 = 1413325) (by norm_num)
theorem B2384149 : Blo 1674037 2384149 := bbase (se 6 (by rfl) ⟨55878, by rfl⟩ : syracuseStep 2384149 = 111757) (by norm_num)
theorem B3768605 : Blo 1674037 3768605 := bbase (se 3 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 3768605 = 1413227) (by norm_num)
theorem B5652773 : Blo 1674037 5652773 := bbase (se 4 (by rfl) ⟨529947, by rfl⟩ : syracuseStep 5652773 = 1059895) (by norm_num)
theorem B1909045 : Blo 1674037 1909045 := bbase (se 5 (by rfl) ⟨89486, by rfl⟩ : syracuseStep 1909045 = 178973) (by norm_num)
theorem B1884469 : Blo 1674037 1884469 := bbase (se 5 (by rfl) ⟨88334, by rfl⟩ : syracuseStep 1884469 = 176669) (by norm_num)
theorem B1884505 : Blo 1674037 1884505 := bbase (se 2 (by rfl) ⟨706689, by rfl⟩ : syracuseStep 1884505 = 1413379) (by norm_num)
theorem B2826589 : Blo 1674037 2826589 := bbase (se 3 (by rfl) ⟨529985, by rfl⟩ : syracuseStep 2826589 = 1059971) (by norm_num)
theorem B3768677 : Blo 1674037 3768677 := bbase (se 4 (by rfl) ⟨353313, by rfl⟩ : syracuseStep 3768677 = 706627) (by norm_num)
theorem B6037877 : Blo 1674037 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B1884541 : Blo 1674037 1884541 := bbase (se 3 (by rfl) ⟨353351, by rfl⟩ : syracuseStep 1884541 = 706703) (by norm_num)
theorem B10191253 : Blo 1674037 10191253 := bbase (se 6 (by rfl) ⟨238857, by rfl⟩ : syracuseStep 10191253 = 477715) (by norm_num)
theorem B1884577 : Blo 1674037 1884577 := bbase (se 2 (by rfl) ⟨706716, by rfl⟩ : syracuseStep 1884577 = 1413433) (by norm_num)
theorem B3768749 : Blo 1674037 3768749 := bbase (se 3 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 3768749 = 1413281) (by norm_num)
theorem B2826677 : Blo 1674037 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B1884613 : Blo 1674037 1884613 := bbase (se 4 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 1884613 = 353365) (by norm_num)
theorem B8159717 : Blo 1674037 8159717 := bbase (se 4 (by rfl) ⟨764973, by rfl⟩ : syracuseStep 8159717 = 1529947) (by norm_num)
theorem B1884649 : Blo 1674037 1884649 := bbase (se 2 (by rfl) ⟨706743, by rfl⟩ : syracuseStep 1884649 = 1413487) (by norm_num)
theorem B3768821 : Blo 1674037 3768821 := bbase (se 5 (by rfl) ⟨176663, by rfl⟩ : syracuseStep 3768821 = 353327) (by norm_num)
theorem B8053253 : Blo 1674037 8053253 := bbase (se 4 (by rfl) ⟨754992, by rfl⟩ : syracuseStep 8053253 = 1509985) (by norm_num)
theorem B1884685 : Blo 1674037 1884685 := bbase (se 3 (by rfl) ⟨353378, by rfl⟩ : syracuseStep 1884685 = 706757) (by norm_num)
theorem B13591061 : Blo 1674037 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B1884721 : Blo 1674037 1884721 := bbase (se 2 (by rfl) ⟨706770, by rfl⟩ : syracuseStep 1884721 = 1413541) (by norm_num)
theorem B2826805 : Blo 1674037 2826805 := bbase (se 5 (by rfl) ⟨132506, by rfl⟩ : syracuseStep 2826805 = 265013) (by norm_num)
theorem B2548277 : Blo 1674037 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B3768893 : Blo 1674037 3768893 := bbase (se 3 (by rfl) ⟨706667, by rfl⟩ : syracuseStep 3768893 = 1413335) (by norm_num)
theorem B1884757 : Blo 1674037 1884757 := bbase (se 8 (by rfl) ⟨11043, by rfl⟩ : syracuseStep 1884757 = 22087) (by norm_num)
theorem B3179101 : Blo 1674037 3179101 := bbase (se 3 (by rfl) ⟨596081, by rfl⟩ : syracuseStep 3179101 = 1192163) (by norm_num)
theorem B1884793 : Blo 1674037 1884793 := bbase (se 2 (by rfl) ⟨706797, by rfl⟩ : syracuseStep 1884793 = 1413595) (by norm_num)
theorem B3768965 : Blo 1674037 3768965 := bbase (se 4 (by rfl) ⟨353340, by rfl⟩ : syracuseStep 3768965 = 706681) (by norm_num)
theorem B2384525 : Blo 1674037 2384525 := bbase (se 3 (by rfl) ⟨447098, by rfl⟩ : syracuseStep 2384525 = 894197) (by norm_num)
theorem B2826893 : Blo 1674037 2826893 := bbase (se 3 (by rfl) ⟨530042, by rfl⟩ : syracuseStep 2826893 = 1060085) (by norm_num)
theorem B6038165 : Blo 1674037 6038165 := bbase (se 6 (by rfl) ⟨141519, by rfl⟩ : syracuseStep 6038165 = 283039) (by norm_num)
theorem B13591189 : Blo 1674037 13591189 := bbase (se 6 (by rfl) ⟨318543, by rfl⟩ : syracuseStep 13591189 = 637087) (by norm_num)
theorem B1884829 : Blo 1674037 1884829 := bbase (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) (by norm_num)
theorem B1884865 : Blo 1674037 1884865 := bbase (se 2 (by rfl) ⟨706824, by rfl⟩ : syracuseStep 1884865 = 1413649) (by norm_num)
theorem B3769037 : Blo 1674037 3769037 := bbase (se 3 (by rfl) ⟨706694, by rfl⟩ : syracuseStep 3769037 = 1413389) (by norm_num)
theorem B5653205 : Blo 1674037 5653205 := bbase (se 7 (by rfl) ⟨66248, by rfl⟩ : syracuseStep 5653205 = 132497) (by norm_num)
theorem B1884901 : Blo 1674037 1884901 := bbase (se 4 (by rfl) ⟨176709, by rfl⟩ : syracuseStep 1884901 = 353419) (by norm_num)
theorem B3179245 : Blo 1674037 3179245 := bbase (se 3 (by rfl) ⟨596108, by rfl⟩ : syracuseStep 3179245 = 1192217) (by norm_num)
theorem B1884937 : Blo 1674037 1884937 := bbase (se 2 (by rfl) ⟨706851, by rfl⟩ : syracuseStep 1884937 = 1413703) (by norm_num)
theorem B2827021 : Blo 1674037 2827021 := bbase (se 3 (by rfl) ⟨530066, by rfl⟩ : syracuseStep 2827021 = 1060133) (by norm_num)
theorem B3769109 : Blo 1674037 3769109 := bbase (se 6 (by rfl) ⟨88338, by rfl⟩ : syracuseStep 3769109 = 176677) (by norm_num)
theorem B1884973 : Blo 1674037 1884973 := bbase (se 3 (by rfl) ⟨353432, by rfl⟩ : syracuseStep 1884973 = 706865) (by norm_num)
theorem B1885009 : Blo 1674037 1885009 := bbase (se 2 (by rfl) ⟨706878, by rfl⟩ : syracuseStep 1885009 = 1413757) (by norm_num)
theorem B3769181 : Blo 1674037 3769181 := bbase (se 3 (by rfl) ⟨706721, by rfl⟩ : syracuseStep 3769181 = 1413443) (by norm_num)
theorem B2827109 : Blo 1674037 2827109 := bbase (se 4 (by rfl) ⟨265041, by rfl⟩ : syracuseStep 2827109 = 530083) (by norm_num)
theorem B1885045 : Blo 1674037 1885045 := bbase (se 5 (by rfl) ⟨88361, by rfl⟩ : syracuseStep 1885045 = 176723) (by norm_num)
theorem B3179405 : Blo 1674037 3179405 := bbase (se 3 (by rfl) ⟨596138, by rfl⟩ : syracuseStep 3179405 = 1192277) (by norm_num)
theorem B1885081 : Blo 1674037 1885081 := bbase (se 2 (by rfl) ⟨706905, by rfl⟩ : syracuseStep 1885081 = 1413811) (by norm_num)
theorem B5366693 : Blo 1674037 5366693 := bbase (se 4 (by rfl) ⟨503127, by rfl⟩ : syracuseStep 5366693 = 1006255) (by norm_num)
theorem B3769253 : Blo 1674037 3769253 := bbase (se 4 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 3769253 = 706735) (by norm_num)
theorem B1909693 : Blo 1674037 1909693 := bbase (se 3 (by rfl) ⟨358067, by rfl⟩ : syracuseStep 1909693 = 716135) (by norm_num)
theorem B1885117 : Blo 1674037 1885117 := bbase (se 3 (by rfl) ⟨353459, by rfl⟩ : syracuseStep 1885117 = 706919) (by norm_num)
theorem B6357973 : Blo 1674037 6357973 := bbase (se 7 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 6357973 = 149015) (by norm_num)
theorem B9544661 : Blo 1674037 9544661 := bbase (se 7 (by rfl) ⟨111851, by rfl⟩ : syracuseStep 9544661 = 223703) (by norm_num)
theorem B5096405 : Blo 1674037 5096405 := bbase (se 7 (by rfl) ⟨59723, by rfl⟩ : syracuseStep 5096405 = 119447) (by norm_num)
theorem B1885153 : Blo 1674037 1885153 := bbase (se 2 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 1885153 = 1413865) (by norm_num)
theorem B2827237 : Blo 1674037 2827237 := bbase (se 4 (by rfl) ⟨265053, by rfl⟩ : syracuseStep 2827237 = 530107) (by norm_num)
theorem B3769325 : Blo 1674037 3769325 := bbase (se 3 (by rfl) ⟨706748, by rfl⟩ : syracuseStep 3769325 = 1413497) (by norm_num)
theorem B1885189 : Blo 1674037 1885189 := bbase (se 4 (by rfl) ⟨176736, by rfl⟩ : syracuseStep 1885189 = 353473) (by norm_num)
theorem B3179549 : Blo 1674037 3179549 := bbase (se 3 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 3179549 = 1192331) (by norm_num)
theorem B1885225 : Blo 1674037 1885225 := bbase (se 2 (by rfl) ⟨706959, by rfl⟩ : syracuseStep 1885225 = 1413919) (by norm_num)
theorem B3769397 : Blo 1674037 3769397 := bbase (se 5 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 3769397 = 353381) (by norm_num)
theorem B2827325 : Blo 1674037 2827325 := bbase (se 3 (by rfl) ⟨530123, by rfl⟩ : syracuseStep 2827325 = 1060247) (by norm_num)
theorem B1885261 : Blo 1674037 1885261 := bbase (se 3 (by rfl) ⟨353486, by rfl⟩ : syracuseStep 1885261 = 706973) (by norm_num)
theorem B10183765 : Blo 1674037 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B1885297 : Blo 1674037 1885297 := bbase (se 2 (by rfl) ⟨706986, by rfl⟩ : syracuseStep 1885297 = 1413973) (by norm_num)
theorem B3769469 : Blo 1674037 3769469 := bbase (se 3 (by rfl) ⟨706775, by rfl⟩ : syracuseStep 3769469 = 1413551) (by norm_num)
theorem B1696897 : Blo 1674037 1696897 := bbase (se 2 (by rfl) ⟨636336, by rfl⟩ : syracuseStep 1696897 = 1272673) (by norm_num)
theorem B5653637 : Blo 1674037 5653637 := bbase (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) (by norm_num)
theorem B4023445 : Blo 1674037 4023445 := bbase (se 6 (by rfl) ⟨94299, by rfl⟩ : syracuseStep 4023445 = 188599) (by norm_num)
theorem B1885333 : Blo 1674037 1885333 := bbase (se 6 (by rfl) ⟨44187, by rfl⟩ : syracuseStep 1885333 = 88375) (by norm_num)
theorem B1885369 : Blo 1674037 1885369 := bbase (se 2 (by rfl) ⟨707013, by rfl⟩ : syracuseStep 1885369 = 1414027) (by norm_num)
theorem B2827453 : Blo 1674037 2827453 := bbase (se 3 (by rfl) ⟨530147, by rfl⟩ : syracuseStep 2827453 = 1060295) (by norm_num)
theorem B3769541 : Blo 1674037 3769541 := bbase (se 4 (by rfl) ⟨353394, by rfl⟩ : syracuseStep 3769541 = 706789) (by norm_num)
theorem B1885405 : Blo 1674037 1885405 := bbase (se 3 (by rfl) ⟨353513, by rfl⟩ : syracuseStep 1885405 = 707027) (by norm_num)
theorem B1885441 : Blo 1674037 1885441 := bbase (se 2 (by rfl) ⟨707040, by rfl⟩ : syracuseStep 1885441 = 1414081) (by norm_num)
theorem B6358277 : Blo 1674037 6358277 := bbase (se 4 (by rfl) ⟨596088, by rfl⟩ : syracuseStep 6358277 = 1192177) (by norm_num)
theorem B3769613 : Blo 1674037 3769613 := bbase (se 3 (by rfl) ⟨706802, by rfl⟩ : syracuseStep 3769613 = 1413605) (by norm_num)
theorem B2827541 : Blo 1674037 2827541 := bbase (se 6 (by rfl) ⟨66270, by rfl⟩ : syracuseStep 2827541 = 132541) (by norm_num)
theorem B1885477 : Blo 1674037 1885477 := bbase (se 4 (by rfl) ⟨176763, by rfl⟩ : syracuseStep 1885477 = 353527) (by norm_num)
theorem B3179837 : Blo 1674037 3179837 := bbase (se 3 (by rfl) ⟨596219, by rfl⟩ : syracuseStep 3179837 = 1192439) (by norm_num)
theorem B3818821 : Blo 1674037 3818821 := bbase (se 4 (by rfl) ⟨358014, by rfl⟩ : syracuseStep 3818821 = 716029) (by norm_num)
theorem B1885513 : Blo 1674037 1885513 := bbase (se 2 (by rfl) ⟨707067, by rfl⟩ : syracuseStep 1885513 = 1414135) (by norm_num)
theorem B3769685 : Blo 1674037 3769685 := bbase (se 12 (by rfl) ⟨1380, by rfl⟩ : syracuseStep 3769685 = 2761) (by norm_num)
theorem B14312821 : Blo 1674037 14312821 := bbase (se 5 (by rfl) ⟨670913, by rfl⟩ : syracuseStep 14312821 = 1341827) (by norm_num)
theorem B2827669 : Blo 1674037 2827669 := bbase (se 6 (by rfl) ⟨66273, by rfl⟩ : syracuseStep 2827669 = 132547) (by norm_num)
theorem B3769757 : Blo 1674037 3769757 := bbase (se 3 (by rfl) ⟨706829, by rfl⟩ : syracuseStep 3769757 = 1413659) (by norm_num)
theorem B5727653 : Blo 1674037 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B3179989 : Blo 1674037 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B8480213 : Blo 1674037 8480213 := bbase (se 7 (by rfl) ⟨99377, by rfl⟩ : syracuseStep 8480213 = 198755) (by norm_num)
theorem B3769829 : Blo 1674037 3769829 := bbase (se 4 (by rfl) ⟨353421, by rfl⟩ : syracuseStep 3769829 = 706843) (by norm_num)
theorem B2827757 : Blo 1674037 2827757 := bbase (se 3 (by rfl) ⟨530204, by rfl⟩ : syracuseStep 2827757 = 1060409) (by norm_num)
theorem B3769901 : Blo 1674037 3769901 := bbase (se 3 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 3769901 = 1413713) (by norm_num)
theorem B5654069 : Blo 1674037 5654069 := bbase (se 5 (by rfl) ⟨265034, by rfl⟩ : syracuseStep 5654069 = 530069) (by norm_num)
theorem B4769381 : Blo 1674037 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B2827885 : Blo 1674037 2827885 := bbase (se 3 (by rfl) ⟨530228, by rfl⟩ : syracuseStep 2827885 = 1060457) (by norm_num)
theorem B3769973 : Blo 1674037 3769973 := bbase (se 5 (by rfl) ⟨176717, by rfl⟩ : syracuseStep 3769973 = 353435) (by norm_num)
theorem B3770045 : Blo 1674037 3770045 := bbase (se 3 (by rfl) ⟨706883, by rfl⟩ : syracuseStep 3770045 = 1413767) (by norm_num)
theorem B2827973 : Blo 1674037 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B4024021 : Blo 1674037 4024021 := bbase (se 7 (by rfl) ⟨47156, by rfl⟩ : syracuseStep 4024021 = 94313) (by norm_num)
theorem B3180293 : Blo 1674037 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B3770117 : Blo 1674037 3770117 := bbase (se 4 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 3770117 = 706897) (by norm_num)
theorem B2828101 : Blo 1674037 2828101 := bbase (se 4 (by rfl) ⟨265134, by rfl⟩ : syracuseStep 2828101 = 530269) (by norm_num)
theorem B3770189 : Blo 1674037 3770189 := bbase (se 3 (by rfl) ⟨706910, by rfl⟩ : syracuseStep 3770189 = 1413821) (by norm_num)
theorem B7153541 : Blo 1674037 7153541 := bbase (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) (by norm_num)
theorem B3770261 : Blo 1674037 3770261 := bbase (se 6 (by rfl) ⟨88365, by rfl⟩ : syracuseStep 3770261 = 176731) (by norm_num)
theorem B2828189 : Blo 1674037 2828189 := bbase (se 3 (by rfl) ⟨530285, by rfl⟩ : syracuseStep 2828189 = 1060571) (by norm_num)
theorem B1787869 : Blo 1674037 1787869 := bbase (se 3 (by rfl) ⟨335225, by rfl⟩ : syracuseStep 1787869 = 670451) (by norm_num)
theorem B3770333 : Blo 1674037 3770333 := bbase (se 3 (by rfl) ⟨706937, by rfl⟩ : syracuseStep 3770333 = 1413875) (by norm_num)
theorem B5654501 : Blo 1674037 5654501 := bbase (se 4 (by rfl) ⟨530109, by rfl⟩ : syracuseStep 5654501 = 1060219) (by norm_num)
theorem B4024349 : Blo 1674037 4024349 := bbase (se 3 (by rfl) ⟨754565, by rfl⟩ : syracuseStep 4024349 = 1509131) (by norm_num)
theorem B2385949 : Blo 1674037 2385949 := bbase (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) (by norm_num)
theorem B1787941 : Blo 1674037 1787941 := bbase (se 4 (by rfl) ⟨167619, by rfl⟩ : syracuseStep 1787941 = 335239) (by norm_num)
theorem B3770405 : Blo 1674037 3770405 := bbase (se 4 (by rfl) ⟨353475, by rfl⟩ : syracuseStep 3770405 = 706951) (by norm_num)
theorem B1697845 : Blo 1674037 1697845 := bbase (se 5 (by rfl) ⟨79586, by rfl⟩ : syracuseStep 1697845 = 159173) (by norm_num)
theorem B4024405 : Blo 1674037 4024405 := bbase (se 8 (by rfl) ⟨23580, by rfl⟩ : syracuseStep 4024405 = 47161) (by norm_num)
theorem B2148445 : Blo 1674037 2148445 := bbase (se 3 (by rfl) ⟨402833, by rfl⟩ : syracuseStep 2148445 = 805667) (by norm_num)
theorem B3770477 : Blo 1674037 3770477 := bbase (se 3 (by rfl) ⟨706964, by rfl⟩ : syracuseStep 3770477 = 1413929) (by norm_num)
theorem B1910933 : Blo 1674037 1910933 := bbase (se 6 (by rfl) ⟨44787, by rfl⟩ : syracuseStep 1910933 = 89575) (by norm_num)
theorem B3770549 : Blo 1674037 3770549 := bbase (se 5 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 3770549 = 353489) (by norm_num)
theorem B2148589 : Blo 1674037 2148589 := bbase (se 3 (by rfl) ⟨402860, by rfl⟩ : syracuseStep 2148589 = 805721) (by norm_num)
theorem B3770621 : Blo 1674037 3770621 := bbase (se 3 (by rfl) ⟨706991, by rfl⟩ : syracuseStep 3770621 = 1413983) (by norm_num)
theorem B4770053 : Blo 1674037 4770053 := bbase (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) (by norm_num)
theorem B4024637 : Blo 1674037 4024637 := bbase (se 3 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 4024637 = 1509239) (by norm_num)
theorem B3770693 : Blo 1674037 3770693 := bbase (se 4 (by rfl) ⟨353502, by rfl⟩ : syracuseStep 3770693 = 707005) (by norm_num)
theorem B2263405 : Blo 1674037 2263405 := bbase (se 3 (by rfl) ⟨424388, by rfl⟩ : syracuseStep 2263405 = 848777) (by norm_num)
theorem B8046965 : Blo 1674037 8046965 := bbase (se 5 (by rfl) ⟨377201, by rfl⟩ : syracuseStep 8046965 = 754403) (by norm_num)
theorem B3017093 : Blo 1674037 3017093 := bbase (se 4 (by rfl) ⟨282852, by rfl⟩ : syracuseStep 3017093 = 565705) (by norm_num)
theorem B3770765 : Blo 1674037 3770765 := bbase (se 3 (by rfl) ⟨707018, by rfl⟩ : syracuseStep 3770765 = 1414037) (by norm_num)
theorem B4237717 : Blo 1674037 4237717 := bbase (se 6 (by rfl) ⟨99321, by rfl⟩ : syracuseStep 4237717 = 198643) (by norm_num)
theorem B12069269 : Blo 1674037 12069269 := bbase (se 6 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 12069269 = 565747) (by norm_num)
theorem B32197013 : Blo 1674037 32197013 := bbase (se 6 (by rfl) ⟨754617, by rfl⟩ : syracuseStep 32197013 = 1509235) (by norm_num)
theorem B1788313 : Blo 1674037 1788313 := bbase (se 2 (by rfl) ⟨670617, by rfl⟩ : syracuseStep 1788313 = 1341235) (by norm_num)
theorem B5654933 : Blo 1674037 5654933 := bbase (se 6 (by rfl) ⟨132537, by rfl⟩ : syracuseStep 5654933 = 265075) (by norm_num)
theorem B6121925 : Blo 1674037 6121925 := bbase (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) (by norm_num)
theorem B22915541 : Blo 1674037 22915541 := bbase (se 7 (by rfl) ⟨268541, by rfl⟩ : syracuseStep 22915541 = 537083) (by norm_num)
theorem B3770837 : Blo 1674037 3770837 := bbase (se 7 (by rfl) ⟨44189, by rfl⟩ : syracuseStep 3770837 = 88379) (by norm_num)
theorem B3181045 : Blo 1674037 3181045 := bbase (se 5 (by rfl) ⟨149111, by rfl⟩ : syracuseStep 3181045 = 298223) (by norm_num)
theorem B4024829 : Blo 1674037 4024829 := bbase (se 3 (by rfl) ⟨754655, by rfl⟩ : syracuseStep 4024829 = 1509311) (by norm_num)
theorem B4237829 : Blo 1674037 4237829 := bbase (se 4 (by rfl) ⟨397296, by rfl⟩ : syracuseStep 4237829 = 794593) (by norm_num)
theorem B3770909 : Blo 1674037 3770909 := bbase (se 3 (by rfl) ⟨707045, by rfl⟩ : syracuseStep 3770909 = 1414091) (by norm_num)
theorem B2263621 : Blo 1674037 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B3770981 : Blo 1674037 3770981 := bbase (se 4 (by rfl) ⟨353529, by rfl⟩ : syracuseStep 3770981 = 707059) (by norm_num)
theorem B1698409 : Blo 1674037 1698409 := bbase (se 2 (by rfl) ⟨636903, by rfl⟩ : syracuseStep 1698409 = 1273807) (by norm_num)
theorem B3181189 : Blo 1674037 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B3771053 : Blo 1674037 3771053 := bbase (se 3 (by rfl) ⟨707072, by rfl⟩ : syracuseStep 3771053 = 1414145) (by norm_num)
theorem B4770485 : Blo 1674037 4770485 := bbase (se 5 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 4770485 = 447233) (by norm_num)
theorem B4238021 : Blo 1674037 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B8481509 : Blo 1674037 8481509 := bbase (se 4 (by rfl) ⟨795141, by rfl⟩ : syracuseStep 8481509 = 1590283) (by norm_num)
theorem B1788689 : Blo 1674037 1788689 := bbase (se 2 (by rfl) ⟨670758, by rfl⟩ : syracuseStep 1788689 = 1341517) (by norm_num)
theorem B3181349 : Blo 1674037 3181349 := bbase (se 4 (by rfl) ⟨298251, by rfl⟩ : syracuseStep 3181349 = 596503) (by norm_num)
theorem B10734389 : Blo 1674037 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B4836149 : Blo 1674037 4836149 := bbase (se 5 (by rfl) ⟨226694, by rfl⟩ : syracuseStep 4836149 = 453389) (by norm_num)
theorem B2681669 : Blo 1674037 2681669 := bbase (se 4 (by rfl) ⟨251406, by rfl⟩ : syracuseStep 2681669 = 502813) (by norm_num)
theorem B5655365 : Blo 1674037 5655365 := bbase (se 4 (by rfl) ⟨530190, by rfl⟩ : syracuseStep 5655365 = 1060381) (by norm_num)
theorem B1788761 : Blo 1674037 1788761 := bbase (se 2 (by rfl) ⟨670785, by rfl⟩ : syracuseStep 1788761 = 1341571) (by norm_num)
theorem B5368693 : Blo 1674037 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B3181493 : Blo 1674037 3181493 := bbase (se 5 (by rfl) ⟨149132, by rfl⟩ : syracuseStep 3181493 = 298265) (by norm_num)
theorem B1698769 : Blo 1674037 1698769 := bbase (se 2 (by rfl) ⟨637038, by rfl⟩ : syracuseStep 1698769 = 1274077) (by norm_num)
theorem B1788949 : Blo 1674037 1788949 := bbase (se 6 (by rfl) ⟨41928, by rfl⟩ : syracuseStep 1788949 = 83857) (by norm_num)
theorem B4238365 : Blo 1674037 4238365 := bbase (se 3 (by rfl) ⟨794693, by rfl⟩ : syracuseStep 4238365 = 1589387) (by norm_num)
theorem B2681957 : Blo 1674037 2681957 := bbase (se 4 (by rfl) ⟨251433, by rfl⟩ : syracuseStep 2681957 = 502867) (by norm_num)
theorem B4295813 : Blo 1674037 4295813 := bbase (se 4 (by rfl) ⟨402732, by rfl⟩ : syracuseStep 4295813 = 805465) (by norm_num)
theorem B4238477 : Blo 1674037 4238477 := bbase (se 3 (by rfl) ⟨794714, by rfl⟩ : syracuseStep 4238477 = 1589429) (by norm_num)
theorem B1789133 : Blo 1674037 1789133 := bbase (se 3 (by rfl) ⟨335462, by rfl⟩ : syracuseStep 1789133 = 670925) (by norm_num)
theorem B3181781 : Blo 1674037 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B5655797 : Blo 1674037 5655797 := bbase (se 5 (by rfl) ⟨265115, by rfl⟩ : syracuseStep 5655797 = 530231) (by norm_num)
theorem B14314805 : Blo 1674037 14314805 := bbase (se 5 (by rfl) ⟨671006, by rfl⟩ : syracuseStep 14314805 = 1342013) (by norm_num)
theorem B2682181 : Blo 1674037 2682181 := bbase (se 4 (by rfl) ⟨251454, by rfl⟩ : syracuseStep 2682181 = 502909) (by norm_num)
theorem B6360389 : Blo 1674037 6360389 := bbase (se 4 (by rfl) ⟨596286, by rfl⟩ : syracuseStep 6360389 = 1192573) (by norm_num)
theorem B4238669 : Blo 1674037 4238669 := bbase (se 3 (by rfl) ⟨794750, by rfl⟩ : syracuseStep 4238669 = 1589501) (by norm_num)
theorem B4771237 : Blo 1674037 4771237 := bbase (se 4 (by rfl) ⟨447303, by rfl⟩ : syracuseStep 4771237 = 894607) (by norm_num)
theorem B2264485 : Blo 1674037 2264485 := bbase (se 4 (by rfl) ⟨212295, by rfl⟩ : syracuseStep 2264485 = 424591) (by norm_num)
theorem B4025789 : Blo 1674037 4025789 := bbase (se 3 (by rfl) ⟨754835, by rfl⟩ : syracuseStep 4025789 = 1509671) (by norm_num)
theorem B2207197 : Blo 1674037 2207197 := bbase (se 3 (by rfl) ⟨413849, by rfl⟩ : syracuseStep 2207197 = 827699) (by norm_num)
theorem B3223037 : Blo 1674037 3223037 := bbase (se 3 (by rfl) ⟨604319, by rfl⟩ : syracuseStep 3223037 = 1208639) (by norm_num)
theorem B6360677 : Blo 1674037 6360677 := bbase (se 4 (by rfl) ⟨596313, by rfl⟩ : syracuseStep 6360677 = 1192627) (by norm_num)
theorem B7155317 : Blo 1674037 7155317 := bbase (se 5 (by rfl) ⟨335405, by rfl⟩ : syracuseStep 7155317 = 670811) (by norm_num)
theorem B12725909 : Blo 1674037 12725909 := bbase (se 6 (by rfl) ⟨298263, by rfl⟩ : syracuseStep 12725909 = 596527) (by norm_num)
theorem B2150041 : Blo 1674037 2150041 := bbase (se 2 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 2150041 = 1612531) (by norm_num)
theorem B4239013 : Blo 1674037 4239013 := bbase (se 4 (by rfl) ⟨397407, by rfl⟩ : syracuseStep 4239013 = 794815) (by norm_num)
theorem B5656229 : Blo 1674037 5656229 := bbase (se 4 (by rfl) ⟨530271, by rfl⟩ : syracuseStep 5656229 = 1060543) (by norm_num)
theorem B9178805 : Blo 1674037 9178805 := bbase (se 5 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 9178805 = 860513) (by norm_num)
theorem B4296397 : Blo 1674037 4296397 := bbase (se 3 (by rfl) ⟨805574, by rfl⟩ : syracuseStep 4296397 = 1611149) (by norm_num)
theorem B32640725 : Blo 1674037 32640725 := bbase (se 7 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 32640725 = 765017) (by norm_num)
theorem B4239125 : Blo 1674037 4239125 := bbase (se 6 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 4239125 = 198709) (by norm_num)
theorem B4837141 : Blo 1674037 4837141 := bbase (se 6 (by rfl) ⟨113370, by rfl⟩ : syracuseStep 4837141 = 226741) (by norm_num)
theorem B7253813 : Blo 1674037 7253813 := bbase (se 5 (by rfl) ⟨340022, by rfl⟩ : syracuseStep 7253813 = 680045) (by norm_num)
theorem B3575677 : Blo 1674037 3575677 := bbase (se 3 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 3575677 = 1340879) (by norm_num)
theorem B3624877 : Blo 1674037 3624877 := bbase (se 3 (by rfl) ⟨679664, by rfl⟩ : syracuseStep 3624877 = 1359329) (by norm_num)
theorem B4239317 : Blo 1674037 4239317 := bbase (se 7 (by rfl) ⟨49679, by rfl⟩ : syracuseStep 4239317 = 99359) (by norm_num)
theorem B8482805 : Blo 1674037 8482805 := bbase (se 5 (by rfl) ⟨397631, by rfl⟩ : syracuseStep 8482805 = 795263) (by norm_num)
theorem B12718133 : Blo 1674037 12718133 := bbase (se 5 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 12718133 = 1192325) (by norm_num)
theorem B1863745 : Blo 1674037 1863745 := bbase (se 2 (by rfl) ⟨698904, by rfl⟩ : syracuseStep 1863745 = 1397809) (by norm_num)
theorem B2511077 : Blo 1674037 2511077 := bbase (se 4 (by rfl) ⟨235413, by rfl⟩ : syracuseStep 2511077 = 470827) (by norm_num)
theorem B2511101 : Blo 1674037 2511101 := bbase (se 3 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 2511101 = 941663) (by norm_num)
theorem B5091589 : Blo 1674037 5091589 := bbase (se 4 (by rfl) ⟨477336, by rfl⟩ : syracuseStep 5091589 = 954673) (by norm_num)
theorem B2511125 : Blo 1674037 2511125 := bbase (se 6 (by rfl) ⟨58854, by rfl⟩ : syracuseStep 2511125 = 117709) (by norm_num)
theorem B2511149 : Blo 1674037 2511149 := bbase (se 3 (by rfl) ⟨470840, by rfl⟩ : syracuseStep 2511149 = 941681) (by norm_num)
theorem B4239661 : Blo 1674037 4239661 := bbase (se 3 (by rfl) ⟨794936, by rfl⟩ : syracuseStep 4239661 = 1589873) (by norm_num)
theorem B2617661 : Blo 1674037 2617661 := bbase (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) (by norm_num)
theorem B2511173 : Blo 1674037 2511173 := bbase (se 4 (by rfl) ⟨235422, by rfl⟩ : syracuseStep 2511173 = 470845) (by norm_num)
theorem B2511197 : Blo 1674037 2511197 := bbase (se 3 (by rfl) ⟨470849, by rfl⟩ : syracuseStep 2511197 = 941699) (by norm_num)
theorem B2511221 : Blo 1674037 2511221 := bbase (se 5 (by rfl) ⟨117713, by rfl⟩ : syracuseStep 2511221 = 235427) (by norm_num)
theorem B2511245 : Blo 1674037 2511245 := bbase (se 3 (by rfl) ⟨470858, by rfl⟩ : syracuseStep 2511245 = 941717) (by norm_num)
theorem B8475029 : Blo 1674037 8475029 := bbase (se 6 (by rfl) ⟨198633, by rfl⟩ : syracuseStep 8475029 = 397267) (by norm_num)
theorem B4239773 : Blo 1674037 4239773 := bbase (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) (by norm_num)
theorem B2511269 : Blo 1674037 2511269 := bbase (se 4 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 2511269 = 470863) (by norm_num)
theorem B2683309 : Blo 1674037 2683309 := bbase (se 3 (by rfl) ⟨503120, by rfl⟩ : syracuseStep 2683309 = 1006241) (by norm_num)
theorem B3822005 : Blo 1674037 3822005 := bbase (se 5 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 3822005 = 358313) (by norm_num)
theorem B2511293 : Blo 1674037 2511293 := bbase (se 3 (by rfl) ⟨470867, by rfl⟩ : syracuseStep 2511293 = 941735) (by norm_num)
theorem B2511317 : Blo 1674037 2511317 := bbase (se 7 (by rfl) ⟨29429, by rfl⟩ : syracuseStep 2511317 = 58859) (by norm_num)
theorem B2511341 : Blo 1674037 2511341 := bbase (se 3 (by rfl) ⟨470876, by rfl⟩ : syracuseStep 2511341 = 941753) (by norm_num)
theorem B2511365 : Blo 1674037 2511365 := bbase (se 4 (by rfl) ⟨235440, by rfl⟩ : syracuseStep 2511365 = 470881) (by norm_num)
theorem B3019285 : Blo 1674037 3019285 := bbase (se 6 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 3019285 = 141529) (by norm_num)
theorem B2511389 : Blo 1674037 2511389 := bbase (se 3 (by rfl) ⟨470885, by rfl⟩ : syracuseStep 2511389 = 941771) (by norm_num)
theorem B2511413 : Blo 1674037 2511413 := bbase (se 5 (by rfl) ⟨117722, by rfl⟩ : syracuseStep 2511413 = 235445) (by norm_num)
theorem B2511437 : Blo 1674037 2511437 := bbase (se 3 (by rfl) ⟨470894, by rfl⟩ : syracuseStep 2511437 = 941789) (by norm_num)
theorem B7156309 : Blo 1674037 7156309 := bbase (se 8 (by rfl) ⟨41931, by rfl⟩ : syracuseStep 7156309 = 83863) (by norm_num)
theorem B4239965 : Blo 1674037 4239965 := bbase (se 3 (by rfl) ⟨794993, by rfl⟩ : syracuseStep 4239965 = 1589987) (by norm_num)
theorem B2863717 : Blo 1674037 2863717 := bbase (se 4 (by rfl) ⟨268473, by rfl⟩ : syracuseStep 2863717 = 536947) (by norm_num)
theorem B2511461 : Blo 1674037 2511461 := bbase (se 4 (by rfl) ⟨235449, by rfl⟩ : syracuseStep 2511461 = 470899) (by norm_num)
theorem B2511485 : Blo 1674037 2511485 := bbase (se 3 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 2511485 = 941807) (by norm_num)
theorem B2511509 : Blo 1674037 2511509 := bbase (se 6 (by rfl) ⟨58863, by rfl⟩ : syracuseStep 2511509 = 117727) (by norm_num)
theorem B2511533 : Blo 1674037 2511533 := bbase (se 3 (by rfl) ⟨470912, by rfl⟩ : syracuseStep 2511533 = 941825) (by norm_num)
theorem B2511557 : Blo 1674037 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B13578965 : Blo 1674037 13578965 := bbase (se 7 (by rfl) ⟨159128, by rfl⟩ : syracuseStep 13578965 = 318257) (by norm_num)
theorem B2511581 : Blo 1674037 2511581 := bbase (se 3 (by rfl) ⟨470921, by rfl⟩ : syracuseStep 2511581 = 941843) (by norm_num)
theorem B2511605 : Blo 1674037 2511605 := bbase (se 5 (by rfl) ⟨117731, by rfl⟩ : syracuseStep 2511605 = 235463) (by norm_num)
theorem B3576565 : Blo 1674037 3576565 := bbase (se 5 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 3576565 = 335303) (by norm_num)
theorem B6361861 : Blo 1674037 6361861 := bbase (se 4 (by rfl) ⟨596424, by rfl⟩ : syracuseStep 6361861 = 1192849) (by norm_num)
theorem B2511629 : Blo 1674037 2511629 := bbase (se 3 (by rfl) ⟨470930, by rfl⟩ : syracuseStep 2511629 = 941861) (by norm_num)
theorem B2511653 : Blo 1674037 2511653 := bbase (se 4 (by rfl) ⟨235467, by rfl⟩ : syracuseStep 2511653 = 470935) (by norm_num)
theorem B2511677 : Blo 1674037 2511677 := bbase (se 3 (by rfl) ⟨470939, by rfl⟩ : syracuseStep 2511677 = 941879) (by norm_num)
theorem B2511701 : Blo 1674037 2511701 := bbase (se 9 (by rfl) ⟨7358, by rfl⟩ : syracuseStep 2511701 = 14717) (by norm_num)
theorem B2511725 : Blo 1674037 2511725 := bbase (se 3 (by rfl) ⟨470948, by rfl⟩ : syracuseStep 2511725 = 941897) (by norm_num)
theorem B2683757 : Blo 1674037 2683757 := bbase (se 3 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 2683757 = 1006409) (by norm_num)
theorem B2511749 : Blo 1674037 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B2511773 : Blo 1674037 2511773 := bbase (se 3 (by rfl) ⟨470957, by rfl⟩ : syracuseStep 2511773 = 941915) (by norm_num)
theorem B2511797 : Blo 1674037 2511797 := bbase (se 5 (by rfl) ⟨117740, by rfl⟩ : syracuseStep 2511797 = 235481) (by norm_num)
theorem B4240309 : Blo 1674037 4240309 := bbase (se 5 (by rfl) ⟨198764, by rfl⟩ : syracuseStep 4240309 = 397529) (by norm_num)
theorem B2511821 : Blo 1674037 2511821 := bbase (se 3 (by rfl) ⟨470966, by rfl⟩ : syracuseStep 2511821 = 941933) (by norm_num)
theorem B3396565 : Blo 1674037 3396565 := bbase (se 7 (by rfl) ⟨39803, by rfl⟩ : syracuseStep 3396565 = 79607) (by norm_num)
theorem B2511845 : Blo 1674037 2511845 := bbase (se 4 (by rfl) ⟨235485, by rfl⟩ : syracuseStep 2511845 = 470971) (by norm_num)
theorem B2511869 : Blo 1674037 2511869 := bbase (se 3 (by rfl) ⟨470975, by rfl⟩ : syracuseStep 2511869 = 941951) (by norm_num)
theorem B11457557 : Blo 1674037 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B2511893 : Blo 1674037 2511893 := bbase (se 6 (by rfl) ⟨58872, by rfl⟩ : syracuseStep 2511893 = 117745) (by norm_num)
theorem B4240421 : Blo 1674037 4240421 := bbase (se 4 (by rfl) ⟨397539, by rfl⟩ : syracuseStep 4240421 = 795079) (by norm_num)
theorem B2511917 : Blo 1674037 2511917 := bbase (se 3 (by rfl) ⟨470984, by rfl⟩ : syracuseStep 2511917 = 941969) (by norm_num)
theorem B6362165 : Blo 1674037 6362165 := bbase (se 5 (by rfl) ⟨298226, by rfl⟩ : syracuseStep 6362165 = 596453) (by norm_num)
theorem B2511941 : Blo 1674037 2511941 := bbase (se 4 (by rfl) ⟨235494, by rfl⟩ : syracuseStep 2511941 = 470989) (by norm_num)
theorem B2118737 : Blo 1674037 2118737 := bbase (se 2 (by rfl) ⟨794526, by rfl⟩ : syracuseStep 2118737 = 1589053) (by norm_num)
theorem B2511965 : Blo 1674037 2511965 := bbase (se 3 (by rfl) ⟨470993, by rfl⟩ : syracuseStep 2511965 = 941987) (by norm_num)
theorem B2511989 : Blo 1674037 2511989 := bbase (se 5 (by rfl) ⟨117749, by rfl⟩ : syracuseStep 2511989 = 235499) (by norm_num)
theorem B2118793 : Blo 1674037 2118793 := bbase (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) (by norm_num)
theorem B2512013 : Blo 1674037 2512013 := bbase (se 3 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 2512013 = 942005) (by norm_num)
theorem B2512037 : Blo 1674037 2512037 := bbase (se 4 (by rfl) ⟨235503, by rfl⟩ : syracuseStep 2512037 = 471007) (by norm_num)
theorem B2512061 : Blo 1674037 2512061 := bbase (se 3 (by rfl) ⟨471011, by rfl⟩ : syracuseStep 2512061 = 942023) (by norm_num)
theorem B3265733 : Blo 1674037 3265733 := bbase (se 4 (by rfl) ⟨306162, by rfl⟩ : syracuseStep 3265733 = 612325) (by norm_num)
theorem B2512085 : Blo 1674037 2512085 := bbase (se 7 (by rfl) ⟨29438, by rfl⟩ : syracuseStep 2512085 = 58877) (by norm_num)
theorem B4297949 : Blo 1674037 4297949 := bbase (se 3 (by rfl) ⟨805865, by rfl⟩ : syracuseStep 4297949 = 1611731) (by norm_num)
theorem B3577061 : Blo 1674037 3577061 := bbase (se 4 (by rfl) ⟨335349, by rfl⟩ : syracuseStep 3577061 = 670699) (by norm_num)
theorem B4240613 : Blo 1674037 4240613 := bbase (se 4 (by rfl) ⟨397557, by rfl⟩ : syracuseStep 4240613 = 795115) (by norm_num)
theorem B2118889 : Blo 1674037 2118889 := bbase (se 2 (by rfl) ⟨794583, by rfl⟩ : syracuseStep 2118889 = 1589167) (by norm_num)
theorem B2512109 : Blo 1674037 2512109 := bbase (se 3 (by rfl) ⟨471020, by rfl⟩ : syracuseStep 2512109 = 942041) (by norm_num)
theorem B2512133 : Blo 1674037 2512133 := bbase (se 4 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 2512133 = 471025) (by norm_num)
theorem B8484101 : Blo 1674037 8484101 := bbase (se 4 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 8484101 = 1590769) (by norm_num)
theorem B2512157 : Blo 1674037 2512157 := bbase (se 3 (by rfl) ⟨471029, by rfl⟩ : syracuseStep 2512157 = 942059) (by norm_num)
theorem B2512181 : Blo 1674037 2512181 := bbase (se 5 (by rfl) ⟨117758, by rfl⟩ : syracuseStep 2512181 = 235517) (by norm_num)
theorem B2512205 : Blo 1674037 2512205 := bbase (se 3 (by rfl) ⟨471038, by rfl⟩ : syracuseStep 2512205 = 942077) (by norm_num)
theorem B2512229 : Blo 1674037 2512229 := bbase (se 4 (by rfl) ⟨235521, by rfl⟩ : syracuseStep 2512229 = 471043) (by norm_num)
theorem B3020149 : Blo 1674037 3020149 := bbase (se 5 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 3020149 = 283139) (by norm_num)
theorem B2512253 : Blo 1674037 2512253 := bbase (se 3 (by rfl) ⟨471047, by rfl⟩ : syracuseStep 2512253 = 942095) (by norm_num)
theorem B2119061 : Blo 1674037 2119061 := bbase (se 6 (by rfl) ⟨49665, by rfl⟩ : syracuseStep 2119061 = 99331) (by norm_num)
theorem B5092757 : Blo 1674037 5092757 := bbase (se 6 (by rfl) ⟨119361, by rfl⟩ : syracuseStep 5092757 = 238723) (by norm_num)
theorem B2512277 : Blo 1674037 2512277 := bbase (se 6 (by rfl) ⟨58881, by rfl⟩ : syracuseStep 2512277 = 117763) (by norm_num)
theorem B2512301 : Blo 1674037 2512301 := bbase (se 3 (by rfl) ⟨471056, by rfl⟩ : syracuseStep 2512301 = 942113) (by norm_num)
theorem B2512325 : Blo 1674037 2512325 := bbase (se 4 (by rfl) ⟨235530, by rfl⟩ : syracuseStep 2512325 = 471061) (by norm_num)
theorem B2119117 : Blo 1674037 2119117 := bbase (se 3 (by rfl) ⟨397334, by rfl⟩ : syracuseStep 2119117 = 794669) (by norm_num)
theorem B2012621 : Blo 1674037 2012621 := bbase (se 3 (by rfl) ⟨377366, by rfl⟩ : syracuseStep 2012621 = 754733) (by norm_num)
theorem B2512349 : Blo 1674037 2512349 := bbase (se 3 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 2512349 = 942131) (by norm_num)
theorem B2012645 : Blo 1674037 2012645 := bbase (se 4 (by rfl) ⟨188685, by rfl⟩ : syracuseStep 2012645 = 377371) (by norm_num)
theorem B2512373 : Blo 1674037 2512373 := bbase (se 5 (by rfl) ⟨117767, by rfl⟩ : syracuseStep 2512373 = 235535) (by norm_num)
theorem B2512397 : Blo 1674037 2512397 := bbase (se 3 (by rfl) ⟨471074, by rfl⟩ : syracuseStep 2512397 = 942149) (by norm_num)
theorem B6034981 : Blo 1674037 6034981 := bbase (se 4 (by rfl) ⟨565779, by rfl⟩ : syracuseStep 6034981 = 1131559) (by norm_num)
theorem B2512421 : Blo 1674037 2512421 := bbase (se 4 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 2512421 = 471079) (by norm_num)
theorem B2119213 : Blo 1674037 2119213 := bbase (se 3 (by rfl) ⟨397352, by rfl⟩ : syracuseStep 2119213 = 794705) (by norm_num)
theorem B2512445 : Blo 1674037 2512445 := bbase (se 3 (by rfl) ⟨471083, by rfl⟩ : syracuseStep 2512445 = 942167) (by norm_num)
theorem B4240957 : Blo 1674037 4240957 := bbase (se 3 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 4240957 = 1590359) (by norm_num)
theorem B2512469 : Blo 1674037 2512469 := bbase (se 8 (by rfl) ⟨14721, by rfl⟩ : syracuseStep 2512469 = 29443) (by norm_num)
theorem B2512493 : Blo 1674037 2512493 := bbase (se 3 (by rfl) ⟨471092, by rfl⟩ : syracuseStep 2512493 = 942185) (by norm_num)
theorem B2512517 : Blo 1674037 2512517 := bbase (se 4 (by rfl) ⟨235548, by rfl⟩ : syracuseStep 2512517 = 471097) (by norm_num)
theorem B2512541 : Blo 1674037 2512541 := bbase (se 3 (by rfl) ⟨471101, by rfl⟩ : syracuseStep 2512541 = 942203) (by norm_num)
theorem B8476325 : Blo 1674037 8476325 := bbase (se 4 (by rfl) ⟨794655, by rfl⟩ : syracuseStep 8476325 = 1589311) (by norm_num)
theorem B4241069 : Blo 1674037 4241069 := bbase (se 3 (by rfl) ⟨795200, by rfl⟩ : syracuseStep 4241069 = 1590401) (by norm_num)
theorem B2512565 : Blo 1674037 2512565 := bbase (se 5 (by rfl) ⟨117776, by rfl⟩ : syracuseStep 2512565 = 235553) (by norm_num)
theorem B5732021 : Blo 1674037 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B2512589 : Blo 1674037 2512589 := bbase (se 3 (by rfl) ⟨471110, by rfl⟩ : syracuseStep 2512589 = 942221) (by norm_num)
theorem B2119385 : Blo 1674037 2119385 := bbase (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) (by norm_num)
theorem B2512613 : Blo 1674037 2512613 := bbase (se 4 (by rfl) ⟨235557, by rfl⟩ : syracuseStep 2512613 = 471115) (by norm_num)
theorem B2512637 : Blo 1674037 2512637 := bbase (se 3 (by rfl) ⟨471119, by rfl⟩ : syracuseStep 2512637 = 942239) (by norm_num)
theorem B5650181 : Blo 1674037 5650181 := bbase (se 4 (by rfl) ⟨529704, by rfl⟩ : syracuseStep 5650181 = 1059409) (by norm_num)
theorem B2119441 : Blo 1674037 2119441 := bbase (se 2 (by rfl) ⟨794790, by rfl⟩ : syracuseStep 2119441 = 1589581) (by norm_num)
theorem B2545429 : Blo 1674037 2545429 := bbase (se 6 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 2545429 = 119317) (by norm_num)
theorem B2512661 : Blo 1674037 2512661 := bbase (se 6 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 2512661 = 117781) (by norm_num)
theorem B2012953 : Blo 1674037 2012953 := bbase (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) (by norm_num)
theorem B2512685 : Blo 1674037 2512685 := bbase (se 3 (by rfl) ⟨471128, by rfl⟩ : syracuseStep 2512685 = 942257) (by norm_num)
theorem B2512709 : Blo 1674037 2512709 := bbase (se 4 (by rfl) ⟨235566, by rfl⟩ : syracuseStep 2512709 = 471133) (by norm_num)
theorem B2512733 : Blo 1674037 2512733 := bbase (se 3 (by rfl) ⟨471137, by rfl⟩ : syracuseStep 2512733 = 942275) (by norm_num)
theorem B4241261 : Blo 1674037 4241261 := bbase (se 3 (by rfl) ⟨795236, by rfl⟩ : syracuseStep 4241261 = 1590473) (by norm_num)
theorem B2119537 : Blo 1674037 2119537 := bbase (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) (by norm_num)
theorem B2512757 : Blo 1674037 2512757 := bbase (se 5 (by rfl) ⟨117785, by rfl⟩ : syracuseStep 2512757 = 235571) (by norm_num)
theorem B2512781 : Blo 1674037 2512781 := bbase (se 3 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 2512781 = 942293) (by norm_num)
theorem B2512805 : Blo 1674037 2512805 := bbase (se 4 (by rfl) ⟨235575, by rfl⟩ : syracuseStep 2512805 = 471151) (by norm_num)
theorem B2512829 : Blo 1674037 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B2013125 : Blo 1674037 2013125 := bbase (se 4 (by rfl) ⟨188730, by rfl⟩ : syracuseStep 2013125 = 377461) (by norm_num)
theorem B9050069 : Blo 1674037 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B2512853 : Blo 1674037 2512853 := bbase (se 7 (by rfl) ⟨29447, by rfl⟩ : syracuseStep 2512853 = 58895) (by norm_num)
theorem B2512877 : Blo 1674037 2512877 := bbase (se 3 (by rfl) ⟨471164, by rfl⟩ : syracuseStep 2512877 = 942329) (by norm_num)
theorem B6789109 : Blo 1674037 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B3397621 : Blo 1674037 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B2512901 : Blo 1674037 2512901 := bbase (se 4 (by rfl) ⟨235584, by rfl⟩ : syracuseStep 2512901 = 471169) (by norm_num)
theorem B2119709 : Blo 1674037 2119709 := bbase (se 3 (by rfl) ⟨397445, by rfl⟩ : syracuseStep 2119709 = 794891) (by norm_num)
theorem B2512925 : Blo 1674037 2512925 := bbase (se 3 (by rfl) ⟨471173, by rfl⟩ : syracuseStep 2512925 = 942347) (by norm_num)
theorem B2512949 : Blo 1674037 2512949 := bbase (se 5 (by rfl) ⟨117794, by rfl⟩ : syracuseStep 2512949 = 235589) (by norm_num)
theorem B2013241 : Blo 1674037 2013241 := bbase (se 2 (by rfl) ⟨754965, by rfl⟩ : syracuseStep 2013241 = 1509931) (by norm_num)
theorem B3577925 : Blo 1674037 3577925 := bbase (se 4 (by rfl) ⟨335430, by rfl⟩ : syracuseStep 3577925 = 670861) (by norm_num)
theorem B2512973 : Blo 1674037 2512973 := bbase (se 3 (by rfl) ⟨471182, by rfl⟩ : syracuseStep 2512973 = 942365) (by norm_num)
theorem B2119765 : Blo 1674037 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B2512997 : Blo 1674037 2512997 := bbase (se 4 (by rfl) ⟨235593, by rfl⟩ : syracuseStep 2512997 = 471187) (by norm_num)
theorem B2513021 : Blo 1674037 2513021 := bbase (se 3 (by rfl) ⟨471191, by rfl⟩ : syracuseStep 2513021 = 942383) (by norm_num)
theorem B2513045 : Blo 1674037 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B2013337 : Blo 1674037 2013337 := bbase (se 2 (by rfl) ⟨755001, by rfl⟩ : syracuseStep 2013337 = 1510003) (by norm_num)
theorem B2513069 : Blo 1674037 2513069 := bbase (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) (by norm_num)
theorem B5650613 : Blo 1674037 5650613 := bbase (se 5 (by rfl) ⟨264872, by rfl⟩ : syracuseStep 5650613 = 529745) (by norm_num)
theorem B2119861 : Blo 1674037 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B2513093 : Blo 1674037 2513093 := bbase (se 4 (by rfl) ⟨235602, by rfl⟩ : syracuseStep 2513093 = 471205) (by norm_num)
theorem B4241605 : Blo 1674037 4241605 := bbase (se 4 (by rfl) ⟨397650, by rfl⟩ : syracuseStep 4241605 = 795301) (by norm_num)
theorem B13760725 : Blo 1674037 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B3578069 : Blo 1674037 3578069 := bbase (se 7 (by rfl) ⟨41930, by rfl⟩ : syracuseStep 3578069 = 83861) (by norm_num)
theorem B2513117 : Blo 1674037 2513117 := bbase (se 3 (by rfl) ⟨471209, by rfl⟩ : syracuseStep 2513117 = 942419) (by norm_num)
theorem B2513141 : Blo 1674037 2513141 := bbase (se 5 (by rfl) ⟨117803, by rfl⟩ : syracuseStep 2513141 = 235607) (by norm_num)
theorem B2513165 : Blo 1674037 2513165 := bbase (se 3 (by rfl) ⟨471218, by rfl⟩ : syracuseStep 2513165 = 942437) (by norm_num)
theorem B2513189 : Blo 1674037 2513189 := bbase (se 4 (by rfl) ⟨235611, by rfl⟩ : syracuseStep 2513189 = 471223) (by norm_num)
theorem B2013481 : Blo 1674037 2013481 := bbase (se 2 (by rfl) ⟨755055, by rfl⟩ : syracuseStep 2013481 = 1510111) (by norm_num)
theorem B4241717 : Blo 1674037 4241717 := bbase (se 5 (by rfl) ⟨198830, by rfl⟩ : syracuseStep 4241717 = 397661) (by norm_num)
theorem B3766589 : Blo 1674037 3766589 := bbase (se 3 (by rfl) ⟨706235, by rfl⟩ : syracuseStep 3766589 = 1412471) (by norm_num)
theorem B2513213 : Blo 1674037 2513213 := bbase (se 3 (by rfl) ⟨471227, by rfl⟩ : syracuseStep 2513213 = 942455) (by norm_num)
theorem B2513237 : Blo 1674037 2513237 := bbase (se 10 (by rfl) ⟨3681, by rfl⟩ : syracuseStep 2513237 = 7363) (by norm_num)
theorem B2120033 : Blo 1674037 2120033 := bbase (se 2 (by rfl) ⟨795012, by rfl⟩ : syracuseStep 2120033 = 1590025) (by norm_num)
theorem B2513261 : Blo 1674037 2513261 := bbase (se 3 (by rfl) ⟨471236, by rfl⟩ : syracuseStep 2513261 = 942473) (by norm_num)
theorem B12073333 : Blo 1674037 12073333 := bbase (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) (by norm_num)
theorem B3766661 : Blo 1674037 3766661 := bbase (se 4 (by rfl) ⟨353124, by rfl⟩ : syracuseStep 3766661 = 706249) (by norm_num)
theorem B2513285 : Blo 1674037 2513285 := bbase (se 4 (by rfl) ⟨235620, by rfl⟩ : syracuseStep 2513285 = 471241) (by norm_num)
theorem B2120089 : Blo 1674037 2120089 := bbase (se 2 (by rfl) ⟨795033, by rfl⟩ : syracuseStep 2120089 = 1590067) (by norm_num)
theorem B2513309 : Blo 1674037 2513309 := bbase (se 3 (by rfl) ⟨471245, by rfl⟩ : syracuseStep 2513309 = 942491) (by norm_num)
theorem B2513333 : Blo 1674037 2513333 := bbase (se 5 (by rfl) ⟨117812, by rfl⟩ : syracuseStep 2513333 = 235625) (by norm_num)
theorem B3766733 : Blo 1674037 3766733 := bbase (se 3 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 3766733 = 1412525) (by norm_num)
theorem B2513357 : Blo 1674037 2513357 := bbase (se 3 (by rfl) ⟨471254, by rfl⟩ : syracuseStep 2513357 = 942509) (by norm_num)
theorem B2513381 : Blo 1674037 2513381 := bbase (se 4 (by rfl) ⟨235629, by rfl⟩ : syracuseStep 2513381 = 471259) (by norm_num)
theorem B4241909 : Blo 1674037 4241909 := bbase (se 5 (by rfl) ⟨198839, by rfl⟩ : syracuseStep 4241909 = 397679) (by norm_num)
theorem B2120185 : Blo 1674037 2120185 := bbase (se 2 (by rfl) ⟨795069, by rfl⟩ : syracuseStep 2120185 = 1590139) (by norm_num)
theorem B2513405 : Blo 1674037 2513405 := bbase (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) (by norm_num)
theorem B3766805 : Blo 1674037 3766805 := bbase (se 6 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 3766805 = 176569) (by norm_num)
theorem B2513429 : Blo 1674037 2513429 := bbase (se 6 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 2513429 = 117817) (by norm_num)
theorem B2513453 : Blo 1674037 2513453 := bbase (se 3 (by rfl) ⟨471272, by rfl⟩ : syracuseStep 2513453 = 942545) (by norm_num)
theorem B2513477 : Blo 1674037 2513477 := bbase (se 4 (by rfl) ⟨235638, by rfl⟩ : syracuseStep 2513477 = 471277) (by norm_num)
theorem B3766877 : Blo 1674037 3766877 := bbase (se 3 (by rfl) ⟨706289, by rfl⟩ : syracuseStep 3766877 = 1412579) (by norm_num)
theorem B2513501 : Blo 1674037 2513501 := bbase (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) (by norm_num)
theorem B5651045 : Blo 1674037 5651045 := bbase (se 4 (by rfl) ⟨529785, by rfl⟩ : syracuseStep 5651045 = 1059571) (by norm_num)
theorem B2513525 : Blo 1674037 2513525 := bbase (se 5 (by rfl) ⟨117821, by rfl⟩ : syracuseStep 2513525 = 235643) (by norm_num)
theorem B2513549 : Blo 1674037 2513549 := bbase (se 3 (by rfl) ⟨471290, by rfl⟩ : syracuseStep 2513549 = 942581) (by norm_num)
theorem B3766949 : Blo 1674037 3766949 := bbase (se 4 (by rfl) ⟨353151, by rfl⟩ : syracuseStep 3766949 = 706303) (by norm_num)
theorem B2120357 : Blo 1674037 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2513573 : Blo 1674037 2513573 := bbase (se 4 (by rfl) ⟨235647, by rfl⟩ : syracuseStep 2513573 = 471295) (by norm_num)
theorem B2513597 : Blo 1674037 2513597 := bbase (se 3 (by rfl) ⟨471299, by rfl⟩ : syracuseStep 2513597 = 942599) (by norm_num)
theorem B2513621 : Blo 1674037 2513621 := bbase (se 7 (by rfl) ⟨29456, by rfl⟩ : syracuseStep 2513621 = 58913) (by norm_num)
theorem B2120413 : Blo 1674037 2120413 := bbase (se 3 (by rfl) ⟨397577, by rfl⟩ : syracuseStep 2120413 = 795155) (by norm_num)
theorem B3767021 : Blo 1674037 3767021 := bbase (se 3 (by rfl) ⟨706316, by rfl⟩ : syracuseStep 3767021 = 1412633) (by norm_num)
theorem B2513645 : Blo 1674037 2513645 := bbase (se 3 (by rfl) ⟨471308, by rfl⟩ : syracuseStep 2513645 = 942617) (by norm_num)
theorem B2824949 : Blo 1674037 2824949 := bbase (se 5 (by rfl) ⟨132419, by rfl⟩ : syracuseStep 2824949 = 264839) (by norm_num)
theorem B4528885 : Blo 1674037 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B2513669 : Blo 1674037 2513669 := bbase (se 4 (by rfl) ⟨235656, by rfl⟩ : syracuseStep 2513669 = 471313) (by norm_num)
theorem B2513693 : Blo 1674037 2513693 := bbase (se 3 (by rfl) ⟨471317, by rfl⟩ : syracuseStep 2513693 = 942635) (by norm_num)
theorem B3767093 : Blo 1674037 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B2513717 : Blo 1674037 2513717 := bbase (se 5 (by rfl) ⟨117830, by rfl⟩ : syracuseStep 2513717 = 235661) (by norm_num)
theorem B2120509 : Blo 1674037 2120509 := bbase (se 3 (by rfl) ⟨397595, by rfl⟩ : syracuseStep 2120509 = 795191) (by norm_num)
theorem B2513741 : Blo 1674037 2513741 := bbase (se 3 (by rfl) ⟨471326, by rfl⟩ : syracuseStep 2513741 = 942653) (by norm_num)
theorem B4242253 : Blo 1674037 4242253 := bbase (se 3 (by rfl) ⟨795422, by rfl⟩ : syracuseStep 4242253 = 1590845) (by norm_num)
theorem B2513765 : Blo 1674037 2513765 := bbase (se 4 (by rfl) ⟨235665, by rfl⟩ : syracuseStep 2513765 = 471331) (by norm_num)
theorem B2825077 : Blo 1674037 2825077 := bbase (se 5 (by rfl) ⟨132425, by rfl⟩ : syracuseStep 2825077 = 264851) (by norm_num)
theorem B3767165 : Blo 1674037 3767165 := bbase (se 3 (by rfl) ⟨706343, by rfl⟩ : syracuseStep 3767165 = 1412687) (by norm_num)
theorem B2513789 : Blo 1674037 2513789 := bbase (se 3 (by rfl) ⟨471335, by rfl⟩ : syracuseStep 2513789 = 942671) (by norm_num)
theorem B2513813 : Blo 1674037 2513813 := bbase (se 6 (by rfl) ⟨58917, by rfl⟩ : syracuseStep 2513813 = 117835) (by norm_num)
theorem B2513837 : Blo 1674037 2513837 := bbase (se 3 (by rfl) ⟨471344, by rfl⟩ : syracuseStep 2513837 = 942689) (by norm_num)
theorem B8477621 : Blo 1674037 8477621 := bbase (se 5 (by rfl) ⟨397388, by rfl⟩ : syracuseStep 8477621 = 794777) (by norm_num)
theorem B3578813 : Blo 1674037 3578813 := bbase (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) (by norm_num)
theorem B4242365 : Blo 1674037 4242365 := bbase (se 3 (by rfl) ⟨795443, by rfl⟩ : syracuseStep 4242365 = 1590887) (by norm_num)
theorem B3767237 : Blo 1674037 3767237 := bbase (se 4 (by rfl) ⟨353178, by rfl⟩ : syracuseStep 3767237 = 706357) (by norm_num)
theorem B2513861 : Blo 1674037 2513861 := bbase (se 4 (by rfl) ⟨235674, by rfl⟩ : syracuseStep 2513861 = 471349) (by norm_num)
theorem B2825165 : Blo 1674037 2825165 := bbase (se 3 (by rfl) ⟨529718, by rfl⟩ : syracuseStep 2825165 = 1059437) (by norm_num)
theorem B2866141 : Blo 1674037 2866141 := bbase (se 3 (by rfl) ⟨537401, by rfl⟩ : syracuseStep 2866141 = 1074803) (by norm_num)
theorem B2513885 : Blo 1674037 2513885 := bbase (se 3 (by rfl) ⟨471353, by rfl⟩ : syracuseStep 2513885 = 942707) (by norm_num)
theorem B2120681 : Blo 1674037 2120681 := bbase (se 2 (by rfl) ⟨795255, by rfl⟩ : syracuseStep 2120681 = 1590511) (by norm_num)
theorem B2513909 : Blo 1674037 2513909 := bbase (se 5 (by rfl) ⟨117839, by rfl⟩ : syracuseStep 2513909 = 235679) (by norm_num)
theorem B3767309 : Blo 1674037 3767309 := bbase (se 3 (by rfl) ⟨706370, by rfl⟩ : syracuseStep 3767309 = 1412741) (by norm_num)
theorem B2513933 : Blo 1674037 2513933 := bbase (se 3 (by rfl) ⟨471362, by rfl⟩ : syracuseStep 2513933 = 942725) (by norm_num)
theorem B5651477 : Blo 1674037 5651477 := bbase (se 6 (by rfl) ⟨132456, by rfl⟩ : syracuseStep 5651477 = 264913) (by norm_num)
theorem B2120737 : Blo 1674037 2120737 := bbase (se 2 (by rfl) ⟨795276, by rfl⟩ : syracuseStep 2120737 = 1590553) (by norm_num)
theorem B2513957 : Blo 1674037 2513957 := bbase (se 4 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 2513957 = 471367) (by norm_num)
theorem B2513981 : Blo 1674037 2513981 := bbase (se 3 (by rfl) ⟨471371, by rfl⟩ : syracuseStep 2513981 = 942743) (by norm_num)
theorem B2825293 : Blo 1674037 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B3767381 : Blo 1674037 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B2514005 : Blo 1674037 2514005 := bbase (se 8 (by rfl) ⟨14730, by rfl⟩ : syracuseStep 2514005 = 29461) (by norm_num)
theorem B2514029 : Blo 1674037 2514029 := bbase (se 3 (by rfl) ⟨471380, by rfl⟩ : syracuseStep 2514029 = 942761) (by norm_num)
theorem B2120833 : Blo 1674037 2120833 := bbase (se 2 (by rfl) ⟨795312, by rfl⟩ : syracuseStep 2120833 = 1590625) (by norm_num)
theorem B2514053 : Blo 1674037 2514053 := bbase (se 4 (by rfl) ⟨235692, by rfl⟩ : syracuseStep 2514053 = 471385) (by norm_num)
theorem B3767453 : Blo 1674037 3767453 := bbase (se 3 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 3767453 = 1412795) (by norm_num)
theorem B2825381 : Blo 1674037 2825381 := bbase (se 4 (by rfl) ⟨264879, by rfl⟩ : syracuseStep 2825381 = 529759) (by norm_num)
theorem B1883317 : Blo 1674037 1883317 := bbase (se 5 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 1883317 = 176561) (by norm_num)
theorem B12573877 : Blo 1674037 12573877 := bbase (se 5 (by rfl) ⟨589400, by rfl⟩ : syracuseStep 12573877 = 1178801) (by norm_num)
theorem B1883353 : Blo 1674037 1883353 := bbase (se 2 (by rfl) ⟨706257, by rfl⟩ : syracuseStep 1883353 = 1412515) (by norm_num)
theorem B3767525 : Blo 1674037 3767525 := bbase (se 4 (by rfl) ⟨353205, by rfl⟩ : syracuseStep 3767525 = 706411) (by norm_num)
theorem B1883389 : Blo 1674037 1883389 := bbase (se 3 (by rfl) ⟨353135, by rfl⟩ : syracuseStep 1883389 = 706271) (by norm_num)
theorem B6790405 : Blo 1674037 6790405 := bbase (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) (by norm_num)
theorem B1883425 : Blo 1674037 1883425 := bbase (se 2 (by rfl) ⟨706284, by rfl⟩ : syracuseStep 1883425 = 1412569) (by norm_num)
theorem B2825509 : Blo 1674037 2825509 := bbase (se 4 (by rfl) ⟨264891, by rfl⟩ : syracuseStep 2825509 = 529783) (by norm_num)
theorem B3767597 : Blo 1674037 3767597 := bbase (se 3 (by rfl) ⟨706424, by rfl⟩ : syracuseStep 3767597 = 1412849) (by norm_num)
theorem B2121005 : Blo 1674037 2121005 := bbase (se 3 (by rfl) ⟨397688, by rfl⟩ : syracuseStep 2121005 = 795377) (by norm_num)
theorem B9534773 : Blo 1674037 9534773 := bbase (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) (by norm_num)
theorem B1883461 : Blo 1674037 1883461 := bbase (se 4 (by rfl) ⟨176574, by rfl⟩ : syracuseStep 1883461 = 353149) (by norm_num)
theorem B19086677 : Blo 1674037 19086677 := bbase (se 11 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 19086677 = 27959) (by norm_num)
theorem B2121061 : Blo 1674037 2121061 := bbase (se 4 (by rfl) ⟨198849, by rfl⟩ : syracuseStep 2121061 = 397699) (by norm_num)
theorem B1883497 : Blo 1674037 1883497 := bbase (se 2 (by rfl) ⟨706311, by rfl⟩ : syracuseStep 1883497 = 1412623) (by norm_num)
theorem B3767669 : Blo 1674037 3767669 := bbase (se 5 (by rfl) ⟨176609, by rfl⟩ : syracuseStep 3767669 = 353219) (by norm_num)
theorem B2825597 : Blo 1674037 2825597 := bbase (se 3 (by rfl) ⟨529799, by rfl⟩ : syracuseStep 2825597 = 1059599) (by norm_num)
theorem B1883533 : Blo 1674037 1883533 := bbase (se 3 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 1883533 = 706325) (by norm_num)
theorem B1883569 : Blo 1674037 1883569 := bbase (se 2 (by rfl) ⟨706338, by rfl⟩ : syracuseStep 1883569 = 1412677) (by norm_num)
theorem B3767741 : Blo 1674037 3767741 := bbase (se 3 (by rfl) ⟨706451, by rfl⟩ : syracuseStep 3767741 = 1412903) (by norm_num)
theorem B5651909 : Blo 1674037 5651909 := bbase (se 4 (by rfl) ⟨529866, by rfl⟩ : syracuseStep 5651909 = 1059733) (by norm_num)
theorem B2121157 : Blo 1674037 2121157 := bbase (se 4 (by rfl) ⟨198858, by rfl⟩ : syracuseStep 2121157 = 397717) (by norm_num)
theorem B1883605 : Blo 1674037 1883605 := bbase (se 7 (by rfl) ⟨22073, by rfl⟩ : syracuseStep 1883605 = 44147) (by norm_num)
theorem B1883641 : Blo 1674037 1883641 := bbase (se 2 (by rfl) ⟨706365, by rfl⟩ : syracuseStep 1883641 = 1412731) (by norm_num)
theorem B2825725 : Blo 1674037 2825725 := bbase (se 3 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 2825725 = 1059647) (by norm_num)
theorem B3767813 : Blo 1674037 3767813 := bbase (se 4 (by rfl) ⟨353232, by rfl⟩ : syracuseStep 3767813 = 706465) (by norm_num)
theorem B6356501 : Blo 1674037 6356501 := bbase (se 6 (by rfl) ⟨148980, by rfl⟩ : syracuseStep 6356501 = 297961) (by norm_num)
theorem B1883677 : Blo 1674037 1883677 := bbase (se 3 (by rfl) ⟨353189, by rfl⟩ : syracuseStep 1883677 = 706379) (by norm_num)
theorem B1883713 : Blo 1674037 1883713 := bbase (se 2 (by rfl) ⟨706392, by rfl⟩ : syracuseStep 1883713 = 1412785) (by norm_num)
theorem B3767885 : Blo 1674037 3767885 := bbase (se 3 (by rfl) ⟨706478, by rfl⟩ : syracuseStep 3767885 = 1412957) (by norm_num)
theorem B2825813 : Blo 1674037 2825813 := bbase (se 8 (by rfl) ⟨16557, by rfl⟩ : syracuseStep 2825813 = 33115) (by norm_num)
theorem B1883749 : Blo 1674037 1883749 := bbase (se 4 (by rfl) ⟨176601, by rfl⟩ : syracuseStep 1883749 = 353203) (by norm_num)
theorem B5365349 : Blo 1674037 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B1883785 : Blo 1674037 1883785 := bbase (se 2 (by rfl) ⟨706419, by rfl⟩ : syracuseStep 1883785 = 1412839) (by norm_num)
theorem B9051797 : Blo 1674037 9051797 := bbase (se 6 (by rfl) ⟨212151, by rfl⟩ : syracuseStep 9051797 = 424303) (by norm_num)
theorem B3767957 : Blo 1674037 3767957 := bbase (se 6 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 3767957 = 176623) (by norm_num)
theorem B1883821 : Blo 1674037 1883821 := bbase (se 3 (by rfl) ⟨353216, by rfl⟩ : syracuseStep 1883821 = 706433) (by norm_num)
theorem B3579565 : Blo 1674037 3579565 := bbase (se 3 (by rfl) ⟨671168, by rfl⟩ : syracuseStep 3579565 = 1342337) (by norm_num)
theorem B1883857 : Blo 1674037 1883857 := bbase (se 2 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 1883857 = 1412893) (by norm_num)
theorem B2825941 : Blo 1674037 2825941 := bbase (se 7 (by rfl) ⟨33116, by rfl⟩ : syracuseStep 2825941 = 66233) (by norm_num)
theorem B3768029 : Blo 1674037 3768029 := bbase (se 3 (by rfl) ⟨706505, by rfl⟩ : syracuseStep 3768029 = 1413011) (by norm_num)
theorem B2383597 : Blo 1674037 2383597 := bbase (se 3 (by rfl) ⟨446924, by rfl⟩ : syracuseStep 2383597 = 893849) (by norm_num)
theorem B1883893 : Blo 1674037 1883893 := bbase (se 5 (by rfl) ⟨88307, by rfl⟩ : syracuseStep 1883893 = 176615) (by norm_num)
theorem B1883929 : Blo 1674037 1883929 := bbase (se 2 (by rfl) ⟨706473, by rfl⟩ : syracuseStep 1883929 = 1412947) (by norm_num)
theorem B3768101 : Blo 1674037 3768101 := bbase (se 4 (by rfl) ⟨353259, by rfl⟩ : syracuseStep 3768101 = 706519) (by norm_num)
theorem B2826029 : Blo 1674037 2826029 := bbase (se 3 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 2826029 = 1059761) (by norm_num)
theorem B6356789 : Blo 1674037 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B4079413 : Blo 1674037 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B1883965 : Blo 1674037 1883965 := bbase (se 3 (by rfl) ⟨353243, by rfl⟩ : syracuseStep 1883965 = 706487) (by norm_num)
theorem B51552085 : Blo 1674037 51552085 := bbase (se 9 (by rfl) ⟨151031, by rfl⟩ : syracuseStep 51552085 = 302063) (by norm_num)
theorem B1884001 : Blo 1674037 1884001 := bbase (se 2 (by rfl) ⟨706500, by rfl⟩ : syracuseStep 1884001 = 1413001) (by norm_num)
theorem B3178349 : Blo 1674037 3178349 := bbase (se 3 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 3178349 = 1191881) (by norm_num)
theorem B3768173 : Blo 1674037 3768173 := bbase (se 3 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 3768173 = 1413065) (by norm_num)
theorem B5652341 : Blo 1674037 5652341 := bbase (se 5 (by rfl) ⟨264953, by rfl⟩ : syracuseStep 5652341 = 529907) (by norm_num)
theorem B1884037 : Blo 1674037 1884037 := bbase (se 4 (by rfl) ⟨176628, by rfl⟩ : syracuseStep 1884037 = 353257) (by norm_num)
theorem B1884073 : Blo 1674037 1884073 := bbase (se 2 (by rfl) ⟨706527, by rfl⟩ : syracuseStep 1884073 = 1413055) (by norm_num)
theorem B2826157 : Blo 1674037 2826157 := bbase (se 3 (by rfl) ⟨529904, by rfl⟩ : syracuseStep 2826157 = 1059809) (by norm_num)
theorem B3768245 : Blo 1674037 3768245 := bbase (se 5 (by rfl) ⟨176636, by rfl⟩ : syracuseStep 3768245 = 353273) (by norm_num)
theorem B1884109 : Blo 1674037 1884109 := bbase (se 3 (by rfl) ⟨353270, by rfl⟩ : syracuseStep 1884109 = 706541) (by norm_num)
theorem B1884145 : Blo 1674037 1884145 := bbase (se 2 (by rfl) ⟨706554, by rfl⟩ : syracuseStep 1884145 = 1413109) (by norm_num)
theorem B3768317 : Blo 1674037 3768317 := bbase (se 3 (by rfl) ⟨706559, by rfl⟩ : syracuseStep 3768317 = 1413119) (by norm_num)
theorem B1884163 : Blo 1674037 1884163 := bstep (se 1 (by rfl) ⟨1413122, by rfl⟩ : syracuseStep 1884163 = 2826245) B2826245
theorem B3178531 : Blo 1674037 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B8478755 : Blo 1674037 8478755 := bstep (se 1 (by rfl) ⟨6359066, by rfl⟩ : syracuseStep 8478755 = 12718133) B12718133
theorem B2383921 : Blo 1674037 2383921 := bstep (se 2 (by rfl) ⟨893970, by rfl⟩ : syracuseStep 2383921 = 1787941) B1787941
theorem B5652557 : Blo 1674037 5652557 := bstep (se 3 (by rfl) ⟨1059854, by rfl⟩ : syracuseStep 5652557 = 2119709) B2119709
theorem B3178577 : Blo 1674037 3178577 := bstep (se 2 (by rfl) ⟨1191966, by rfl⟩ : syracuseStep 3178577 = 2383933) B2383933
theorem B2826353 : Blo 1674037 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B5365873 : Blo 1674037 5365873 := bstep (se 2 (by rfl) ⟨2012202, by rfl⟩ : syracuseStep 5365873 = 4024405) B4024405
theorem B5652611 : Blo 1674037 5652611 := bstep (se 1 (by rfl) ⟨4239458, by rfl⟩ : syracuseStep 5652611 = 8478917) B8478917
theorem B5439629 : Blo 1674037 5439629 := bstep (se 3 (by rfl) ⟨1019930, by rfl⟩ : syracuseStep 5439629 = 2039861) B2039861
theorem B1884307 : Blo 1674037 1884307 := bstep (se 1 (by rfl) ⟨1413230, by rfl⟩ : syracuseStep 1884307 = 2826461) B2826461
theorem B3768497 : Blo 1674037 3768497 := bstep (se 2 (by rfl) ⟨1413186, by rfl⟩ : syracuseStep 3768497 = 2826373) B2826373
theorem B3768515 : Blo 1674037 3768515 := bstep (se 1 (by rfl) ⟨2826386, by rfl⟩ : syracuseStep 3768515 = 5652773) B5652773
theorem B1745107 : Blo 1674037 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B2826481 : Blo 1674037 2826481 := bstep (se 2 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 2826481 = 2119861) B2119861
theorem B7151885 : Blo 1674037 7151885 := bstep (se 3 (by rfl) ⟨1340978, by rfl⟩ : syracuseStep 7151885 = 2681957) B2681957
theorem B2826515 : Blo 1674037 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B1884451 : Blo 1674037 1884451 := bstep (se 1 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 1884451 = 2826677) B2826677
theorem B5439811 : Blo 1674037 5439811 := bstep (se 1 (by rfl) ⟨4079858, by rfl⟩ : syracuseStep 5439811 = 8159717) B8159717
theorem B9060707 : Blo 1674037 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B3178865 : Blo 1674037 3178865 := bstep (se 2 (by rfl) ⟨1192074, by rfl⟩ : syracuseStep 3178865 = 2384149) B2384149
theorem B5652881 : Blo 1674037 5652881 := bstep (se 2 (by rfl) ⟨2119830, by rfl⟩ : syracuseStep 5652881 = 4239661) B4239661
theorem B2826643 : Blo 1674037 2826643 := bstep (se 1 (by rfl) ⟨2119982, by rfl⟩ : syracuseStep 2826643 = 4239965) B4239965
theorem B1884595 : Blo 1674037 1884595 := bstep (se 1 (by rfl) ⟨1413446, by rfl⟩ : syracuseStep 1884595 = 2826893) B2826893
theorem B3768785 : Blo 1674037 3768785 := bstep (se 2 (by rfl) ⟨1413294, by rfl⟩ : syracuseStep 3768785 = 2826589) B2826589
theorem B9052643 : Blo 1674037 9052643 := bstep (se 1 (by rfl) ⟨6789482, by rfl⟩ : syracuseStep 9052643 = 13578965) B13578965
theorem B3768803 : Blo 1674037 3768803 := bstep (se 1 (by rfl) ⟨2826602, by rfl⟩ : syracuseStep 3768803 = 5653205) B5653205
theorem B16097777 : Blo 1674037 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B45867541 : Blo 1674037 45867541 := bstep (se 6 (by rfl) ⟨1075020, by rfl⟩ : syracuseStep 45867541 = 2150041) B2150041
theorem B2384417 : Blo 1674037 2384417 := bstep (se 2 (by rfl) ⟨894156, by rfl⟩ : syracuseStep 2384417 = 1788313) B1788313
theorem B2826785 : Blo 1674037 2826785 := bstep (se 2 (by rfl) ⟨1060044, by rfl⟩ : syracuseStep 2826785 = 2120089) B2120089
theorem B51585589 : Blo 1674037 51585589 := bstep (se 5 (by rfl) ⟨2418074, by rfl⟩ : syracuseStep 51585589 = 4836149) B4836149
theorem B1884739 : Blo 1674037 1884739 := bstep (se 1 (by rfl) ⟨1413554, by rfl⟩ : syracuseStep 1884739 = 2827109) B2827109
theorem B2826913 : Blo 1674037 2826913 := bstep (se 2 (by rfl) ⟨1060092, by rfl⟩ : syracuseStep 2826913 = 2120185) B2120185
theorem B2826947 : Blo 1674037 2826947 := bstep (se 1 (by rfl) ⟨2120210, by rfl⟩ : syracuseStep 2826947 = 4240421) B4240421
theorem B1884883 : Blo 1674037 1884883 := bstep (se 1 (by rfl) ⟨1413662, by rfl⟩ : syracuseStep 1884883 = 2827325) B2827325
theorem B3769073 : Blo 1674037 3769073 := bstep (se 2 (by rfl) ⟨1413402, by rfl⟩ : syracuseStep 3769073 = 2826805) B2826805
theorem B3769091 : Blo 1674037 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B2827075 : Blo 1674037 2827075 := bstep (se 1 (by rfl) ⟨2120306, by rfl⟩ : syracuseStep 2827075 = 4240613) B4240613
theorem B8479565 : Blo 1674037 8479565 := bstep (se 3 (by rfl) ⟨1589918, by rfl⟩ : syracuseStep 8479565 = 3179837) B3179837
theorem B1885027 : Blo 1674037 1885027 := bstep (se 1 (by rfl) ⟨1413770, by rfl⟩ : syracuseStep 1885027 = 2827541) B2827541
theorem B18121585 : Blo 1674037 18121585 := bstep (se 2 (by rfl) ⟨6795594, by rfl⟩ : syracuseStep 18121585 = 13591189) B13591189
theorem B5653421 : Blo 1674037 5653421 := bstep (se 3 (by rfl) ⟨1060016, by rfl⟩ : syracuseStep 5653421 = 2120033) B2120033
theorem B3818435 : Blo 1674037 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B2827217 : Blo 1674037 2827217 := bstep (se 2 (by rfl) ⟨1060206, by rfl⟩ : syracuseStep 2827217 = 2120413) B2120413
theorem B5653475 : Blo 1674037 5653475 := bstep (se 1 (by rfl) ⟨4240106, by rfl⟩ : syracuseStep 5653475 = 8480213) B8480213
theorem B6038513 : Blo 1674037 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B1885171 : Blo 1674037 1885171 := bstep (se 1 (by rfl) ⟨1413878, by rfl⟩ : syracuseStep 1885171 = 2827757) B2827757
theorem B8045581 : Blo 1674037 8045581 := bstep (se 3 (by rfl) ⟨1508546, by rfl⟩ : syracuseStep 8045581 = 3017093) B3017093
theorem B3769361 : Blo 1674037 3769361 := bstep (se 2 (by rfl) ⟨1413510, by rfl⟩ : syracuseStep 3769361 = 2827021) B2827021
theorem B3769379 : Blo 1674037 3769379 := bstep (se 1 (by rfl) ⟨2827034, by rfl⟩ : syracuseStep 3769379 = 5654069) B5654069
theorem B3179587 : Blo 1674037 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B2827345 : Blo 1674037 2827345 := bstep (se 2 (by rfl) ⟨1060254, by rfl⟩ : syracuseStep 2827345 = 2120509) B2120509
theorem B2827379 : Blo 1674037 2827379 := bstep (se 1 (by rfl) ⟨2120534, by rfl⟩ : syracuseStep 2827379 = 4241069) B4241069
theorem B1885315 : Blo 1674037 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B10192013 : Blo 1674037 10192013 := bstep (se 3 (by rfl) ⟨1911002, by rfl⟩ : syracuseStep 10192013 = 3822005) B3822005
theorem B5366989 : Blo 1674037 5366989 := bstep (se 3 (by rfl) ⟨1006310, by rfl⟩ : syracuseStep 5366989 = 2012621) B2012621
theorem B5653745 : Blo 1674037 5653745 := bstep (se 2 (by rfl) ⟨2120154, by rfl⟩ : syracuseStep 5653745 = 4240309) B4240309
theorem B2827507 : Blo 1674037 2827507 := bstep (se 1 (by rfl) ⟨2120630, by rfl⟩ : syracuseStep 2827507 = 4241261) B4241261
theorem B4769027 : Blo 1674037 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B5367053 : Blo 1674037 5367053 := bstep (se 3 (by rfl) ⟨1006322, by rfl⟩ : syracuseStep 5367053 = 2012645) B2012645
theorem B1885459 : Blo 1674037 1885459 := bstep (se 1 (by rfl) ⟨1414094, by rfl⟩ : syracuseStep 1885459 = 2828189) B2828189
theorem B3769649 : Blo 1674037 3769649 := bstep (se 2 (by rfl) ⟨1413618, by rfl⟩ : syracuseStep 3769649 = 2827237) B2827237
theorem B3769667 : Blo 1674037 3769667 := bstep (se 1 (by rfl) ⟨2827250, by rfl⟩ : syracuseStep 3769667 = 5654501) B5654501
theorem B2827649 : Blo 1674037 2827649 := bstep (se 2 (by rfl) ⟨1060368, by rfl⟩ : syracuseStep 2827649 = 2120737) B2120737
theorem B2385283 : Blo 1674037 2385283 := bstep (se 1 (by rfl) ⟨1788962, by rfl⟩ : syracuseStep 2385283 = 3577925) B3577925
theorem B25798085 : Blo 1674037 25798085 := bstep (se 4 (by rfl) ⟨2418570, by rfl⟩ : syracuseStep 25798085 = 4837141) B4837141
theorem B2385379 : Blo 1674037 2385379 := bstep (se 1 (by rfl) ⟨1789034, by rfl⟩ : syracuseStep 2385379 = 3578069) B3578069
theorem B2262529 : Blo 1674037 2262529 := bstep (se 2 (by rfl) ⟨848448, by rfl⟩ : syracuseStep 2262529 = 1696897) B1696897
theorem B2827777 : Blo 1674037 2827777 := bstep (se 2 (by rfl) ⟨1060416, by rfl⟩ : syracuseStep 2827777 = 2120833) B2120833
theorem B3180035 : Blo 1674037 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B2827811 : Blo 1674037 2827811 := bstep (se 1 (by rfl) ⟨2120858, by rfl⟩ : syracuseStep 2827811 = 4241717) B4241717
theorem B20383285 : Blo 1674037 20383285 := bstep (se 5 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 20383285 = 1910933) B1910933
theorem B3769937 : Blo 1674037 3769937 := bstep (se 2 (by rfl) ⟨1413726, by rfl⟩ : syracuseStep 3769937 = 2827453) B2827453
theorem B8046179 : Blo 1674037 8046179 := bstep (se 1 (by rfl) ⟨6034634, by rfl⟩ : syracuseStep 8046179 = 12069269) B12069269
theorem B21464675 : Blo 1674037 21464675 := bstep (se 1 (by rfl) ⟨16098506, by rfl⟩ : syracuseStep 21464675 = 32197013) B32197013
theorem B3769955 : Blo 1674037 3769955 := bstep (se 1 (by rfl) ⟨2827466, by rfl⟩ : syracuseStep 3769955 = 5654933) B5654933
theorem B4081283 : Blo 1674037 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B19080845 : Blo 1674037 19080845 := bstep (se 3 (by rfl) ⟨3577658, by rfl⟩ : syracuseStep 19080845 = 7155317) B7155317
theorem B2827939 : Blo 1674037 2827939 := bstep (se 1 (by rfl) ⟨2120954, by rfl⟩ : syracuseStep 2827939 = 4241909) B4241909
theorem B9053873 : Blo 1674037 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B6358733 : Blo 1674037 6358733 := bstep (se 3 (by rfl) ⟨1192262, by rfl⟩ : syracuseStep 6358733 = 2384525) B2384525
theorem B5654285 : Blo 1674037 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B3180323 : Blo 1674037 3180323 := bstep (se 1 (by rfl) ⟨2385242, by rfl⟩ : syracuseStep 3180323 = 4770485) B4770485
theorem B2828081 : Blo 1674037 2828081 := bstep (se 2 (by rfl) ⟨1060530, by rfl⟩ : syracuseStep 2828081 = 2121061) B2121061
theorem B5654339 : Blo 1674037 5654339 := bstep (se 1 (by rfl) ⟨4240754, by rfl⟩ : syracuseStep 5654339 = 8481509) B8481509
theorem B3770225 : Blo 1674037 3770225 := bstep (se 2 (by rfl) ⟨1413834, by rfl⟩ : syracuseStep 3770225 = 2827669) B2827669
theorem B1787779 : Blo 1674037 1787779 := bstep (se 1 (by rfl) ⟨1340834, by rfl⟩ : syracuseStep 1787779 = 2681669) B2681669
theorem B3770243 : Blo 1674037 3770243 := bstep (se 1 (by rfl) ⟨2827682, by rfl⟩ : syracuseStep 3770243 = 5655365) B5655365
theorem B2828209 : Blo 1674037 2828209 := bstep (se 2 (by rfl) ⟨1060578, by rfl⟩ : syracuseStep 2828209 = 2121157) B2121157
theorem B16107461 : Blo 1674037 16107461 := bstep (se 4 (by rfl) ⟨1510074, by rfl⟩ : syracuseStep 16107461 = 3020149) B3020149
theorem B2942929 : Blo 1674037 2942929 := bstep (se 2 (by rfl) ⟨1103598, by rfl⟩ : syracuseStep 2942929 = 2207197) B2207197
theorem B2385875 : Blo 1674037 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B2828243 : Blo 1674037 2828243 := bstep (se 1 (by rfl) ⟨2121182, by rfl⟩ : syracuseStep 2828243 = 4242365) B4242365
theorem B4769837 : Blo 1674037 4769837 := bstep (se 3 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 4769837 = 1788689) B1788689
theorem B8046641 : Blo 1674037 8046641 := bstep (se 2 (by rfl) ⟨3017490, by rfl⟩ : syracuseStep 8046641 = 6034981) B6034981
theorem B21473333 : Blo 1674037 21473333 := bstep (se 5 (by rfl) ⟨1006562, by rfl⟩ : syracuseStep 21473333 = 2013125) B2013125
theorem B5654609 : Blo 1674037 5654609 := bstep (se 2 (by rfl) ⟨2120478, by rfl⟩ : syracuseStep 5654609 = 4240957) B4240957
theorem B3770513 : Blo 1674037 3770513 := bstep (se 2 (by rfl) ⟨1413942, by rfl⟩ : syracuseStep 3770513 = 2827885) B2827885
theorem B3770531 : Blo 1674037 3770531 := bstep (se 1 (by rfl) ⟨2827898, by rfl⟩ : syracuseStep 3770531 = 5655797) B5655797
theorem B12724451 : Blo 1674037 12724451 := bstep (se 1 (by rfl) ⟨9543338, by rfl⟩ : syracuseStep 12724451 = 19086677) B19086677
theorem B4770029 : Blo 1674037 4770029 := bstep (se 3 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 4770029 = 1788761) B1788761
theorem B5728529 : Blo 1674037 5728529 := bstep (se 2 (by rfl) ⟨2148198, by rfl⟩ : syracuseStep 5728529 = 4296397) B4296397
theorem B2148691 : Blo 1674037 2148691 := bstep (se 1 (by rfl) ⟨1611518, by rfl⟩ : syracuseStep 2148691 = 3223037) B3223037
theorem B4237667 : Blo 1674037 4237667 := bstep (se 1 (by rfl) ⟨3178250, by rfl⟩ : syracuseStep 4237667 = 6356501) B6356501
theorem B3393905 : Blo 1674037 3393905 := bstep (se 2 (by rfl) ⟨1272714, by rfl⟩ : syracuseStep 3393905 = 2545429) B2545429
theorem B3770801 : Blo 1674037 3770801 := bstep (se 2 (by rfl) ⟨1414050, by rfl⟩ : syracuseStep 3770801 = 2828101) B2828101
theorem B3770819 : Blo 1674037 3770819 := bstep (se 1 (by rfl) ⟨2828114, by rfl⟩ : syracuseStep 3770819 = 5656229) B5656229
theorem B21760483 : Blo 1674037 21760483 := bstep (se 1 (by rfl) ⟨16320362, by rfl⟩ : syracuseStep 21760483 = 32640725) B32640725
theorem B4237859 : Blo 1674037 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B4835875 : Blo 1674037 4835875 := bstep (se 1 (by rfl) ⟨3626906, by rfl⟩ : syracuseStep 4835875 = 7253813) B7253813
theorem B5655149 : Blo 1674037 5655149 := bstep (se 3 (by rfl) ⟨1060340, by rfl⟩ : syracuseStep 5655149 = 2120681) B2120681
theorem B5655203 : Blo 1674037 5655203 := bstep (se 1 (by rfl) ⟨4241402, by rfl⟩ : syracuseStep 5655203 = 8482805) B8482805
theorem B3181265 : Blo 1674037 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B2263793 : Blo 1674037 2263793 := bstep (se 2 (by rfl) ⟨848922, by rfl⟩ : syracuseStep 2263793 = 1697845) B1697845
theorem B1674051 : Blo 1674037 1674051 := bstep (se 1 (by rfl) ⟨1255538, by rfl⟩ : syracuseStep 1674051 = 2511077) B2511077
theorem B1674067 : Blo 1674037 1674067 := bstep (se 1 (by rfl) ⟨1255550, by rfl⟩ : syracuseStep 1674067 = 2511101) B2511101
theorem B1674083 : Blo 1674037 1674083 := bstep (se 1 (by rfl) ⟨1255562, by rfl⟩ : syracuseStep 1674083 = 2511125) B2511125
theorem B1674099 : Blo 1674037 1674099 := bstep (se 1 (by rfl) ⟨1255574, by rfl⟩ : syracuseStep 1674099 = 2511149) B2511149
theorem B1674115 : Blo 1674037 1674115 := bstep (se 1 (by rfl) ⟨1255586, by rfl⟩ : syracuseStep 1674115 = 2511173) B2511173
theorem B1674131 : Blo 1674037 1674131 := bstep (se 1 (by rfl) ⟨1255598, by rfl⟩ : syracuseStep 1674131 = 2511197) B2511197
theorem B1674147 : Blo 1674037 1674147 := bstep (se 1 (by rfl) ⟨1255610, by rfl⟩ : syracuseStep 1674147 = 2511221) B2511221
theorem B4025251 : Blo 1674037 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B5655473 : Blo 1674037 5655473 := bstep (se 2 (by rfl) ⟨2120802, by rfl⟩ : syracuseStep 5655473 = 4241605) B4241605
theorem B1674163 : Blo 1674037 1674163 := bstep (se 1 (by rfl) ⟨1255622, by rfl⟩ : syracuseStep 1674163 = 2511245) B2511245
theorem B1674179 : Blo 1674037 1674179 := bstep (se 1 (by rfl) ⟨1255634, by rfl⟩ : syracuseStep 1674179 = 2511269) B2511269
theorem B1674195 : Blo 1674037 1674195 := bstep (se 1 (by rfl) ⟨1255646, by rfl⟩ : syracuseStep 1674195 = 2511293) B2511293
theorem B1674211 : Blo 1674037 1674211 := bstep (se 1 (by rfl) ⟨1255658, by rfl⟩ : syracuseStep 1674211 = 2511317) B2511317
theorem B1674227 : Blo 1674037 1674227 := bstep (se 1 (by rfl) ⟨1255670, by rfl⟩ : syracuseStep 1674227 = 2511341) B2511341
theorem B1674243 : Blo 1674037 1674243 := bstep (se 1 (by rfl) ⟨1255682, by rfl⟩ : syracuseStep 1674243 = 2511365) B2511365
theorem B5368835 : Blo 1674037 5368835 := bstep (se 1 (by rfl) ⟨4026626, by rfl⟩ : syracuseStep 5368835 = 8053253) B8053253
theorem B11455501 : Blo 1674037 11455501 := bstep (se 3 (by rfl) ⟨2147906, by rfl⟩ : syracuseStep 11455501 = 4295813) B4295813
theorem B1674259 : Blo 1674037 1674259 := bstep (se 1 (by rfl) ⟨1255694, by rfl⟩ : syracuseStep 1674259 = 2511389) B2511389
theorem B1674275 : Blo 1674037 1674275 := bstep (se 1 (by rfl) ⟨1255706, by rfl⟩ : syracuseStep 1674275 = 2511413) B2511413
theorem B1698851 : Blo 1674037 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B1674291 : Blo 1674037 1674291 := bstep (se 1 (by rfl) ⟨1255718, by rfl⟩ : syracuseStep 1674291 = 2511437) B2511437
theorem B1674307 : Blo 1674037 1674307 := bstep (se 1 (by rfl) ⟨1255730, by rfl⟩ : syracuseStep 1674307 = 2511461) B2511461
theorem B1674323 : Blo 1674037 1674323 := bstep (se 1 (by rfl) ⟨1255742, by rfl⟩ : syracuseStep 1674323 = 2511485) B2511485
theorem B1674339 : Blo 1674037 1674339 := bstep (se 1 (by rfl) ⟨1255754, by rfl⟩ : syracuseStep 1674339 = 2511509) B2511509
theorem B1674355 : Blo 1674037 1674355 := bstep (se 1 (by rfl) ⟨1255766, by rfl⟩ : syracuseStep 1674355 = 2511533) B2511533
theorem B1674371 : Blo 1674037 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B3017873 : Blo 1674037 3017873 := bstep (se 2 (by rfl) ⟨1131702, by rfl⟩ : syracuseStep 3017873 = 2263405) B2263405
theorem B1674387 : Blo 1674037 1674387 := bstep (se 1 (by rfl) ⟨1255790, by rfl⟩ : syracuseStep 1674387 = 2511581) B2511581
theorem B1674403 : Blo 1674037 1674403 := bstep (se 1 (by rfl) ⟨1255802, by rfl⟩ : syracuseStep 1674403 = 2511605) B2511605
theorem B1674419 : Blo 1674037 1674419 := bstep (se 1 (by rfl) ⟨1255814, by rfl⟩ : syracuseStep 1674419 = 2511629) B2511629
theorem B1674435 : Blo 1674037 1674435 := bstep (se 1 (by rfl) ⟨1255826, by rfl⟩ : syracuseStep 1674435 = 2511653) B2511653
theorem B4771021 : Blo 1674037 4771021 := bstep (se 3 (by rfl) ⟨894566, by rfl⟩ : syracuseStep 4771021 = 1789133) B1789133
theorem B1674451 : Blo 1674037 1674451 := bstep (se 1 (by rfl) ⟨1255838, by rfl⟩ : syracuseStep 1674451 = 2511677) B2511677
theorem B1674467 : Blo 1674037 1674467 := bstep (se 1 (by rfl) ⟨1255850, by rfl⟩ : syracuseStep 1674467 = 2511701) B2511701
theorem B1674483 : Blo 1674037 1674483 := bstep (se 1 (by rfl) ⟨1255862, by rfl⟩ : syracuseStep 1674483 = 2511725) B2511725
theorem B1789171 : Blo 1674037 1789171 := bstep (se 1 (by rfl) ⟨1341878, by rfl⟩ : syracuseStep 1789171 = 2683757) B2683757
theorem B1674499 : Blo 1674037 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B9538829 : Blo 1674037 9538829 := bstep (se 3 (by rfl) ⟨1788530, by rfl⟩ : syracuseStep 9538829 = 3577061) B3577061
theorem B1674515 : Blo 1674037 1674515 := bstep (se 1 (by rfl) ⟨1255886, by rfl⟩ : syracuseStep 1674515 = 2511773) B2511773
theorem B1674531 : Blo 1674037 1674531 := bstep (se 1 (by rfl) ⟨1255898, by rfl⟩ : syracuseStep 1674531 = 2511797) B2511797
theorem B1674547 : Blo 1674037 1674547 := bstep (se 1 (by rfl) ⟨1255910, by rfl⟩ : syracuseStep 1674547 = 2511821) B2511821
theorem B1674563 : Blo 1674037 1674563 := bstep (se 1 (by rfl) ⟨1255922, by rfl⟩ : syracuseStep 1674563 = 2511845) B2511845
theorem B1674579 : Blo 1674037 1674579 := bstep (se 1 (by rfl) ⟨1255934, by rfl⟩ : syracuseStep 1674579 = 2511869) B2511869
theorem B7638371 : Blo 1674037 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B1674595 : Blo 1674037 1674595 := bstep (se 1 (by rfl) ⟨1255946, by rfl⟩ : syracuseStep 1674595 = 2511893) B2511893
theorem B4025713 : Blo 1674037 4025713 := bstep (se 2 (by rfl) ⟨1509642, by rfl⟩ : syracuseStep 4025713 = 3019285) B3019285
theorem B1674611 : Blo 1674037 1674611 := bstep (se 1 (by rfl) ⟨1255958, by rfl⟩ : syracuseStep 1674611 = 2511917) B2511917
theorem B1674627 : Blo 1674037 1674627 := bstep (se 1 (by rfl) ⟨1255970, by rfl⟩ : syracuseStep 1674627 = 2511941) B2511941
theorem B1674643 : Blo 1674037 1674643 := bstep (se 1 (by rfl) ⟨1255982, by rfl⟩ : syracuseStep 1674643 = 2511965) B2511965
theorem B1674659 : Blo 1674037 1674659 := bstep (se 1 (by rfl) ⟨1255994, by rfl⟩ : syracuseStep 1674659 = 2511989) B2511989
theorem B3018161 : Blo 1674037 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B1674675 : Blo 1674037 1674675 := bstep (se 1 (by rfl) ⟨1256006, by rfl⟩ : syracuseStep 1674675 = 2512013) B2512013
theorem B1674691 : Blo 1674037 1674691 := bstep (se 1 (by rfl) ⟨1256018, by rfl⟩ : syracuseStep 1674691 = 2512037) B2512037
theorem B5656013 : Blo 1674037 5656013 := bstep (se 3 (by rfl) ⟨1060502, by rfl⟩ : syracuseStep 5656013 = 2121005) B2121005
theorem B4238801 : Blo 1674037 4238801 := bstep (se 2 (by rfl) ⟨1589550, by rfl⟩ : syracuseStep 4238801 = 3179101) B3179101
theorem B1674707 : Blo 1674037 1674707 := bstep (se 1 (by rfl) ⟨1256030, by rfl⟩ : syracuseStep 1674707 = 2512061) B2512061
theorem B2264545 : Blo 1674037 2264545 := bstep (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) B1698409
theorem B1674723 : Blo 1674037 1674723 := bstep (se 1 (by rfl) ⟨1256042, by rfl⟩ : syracuseStep 1674723 = 2512085) B2512085
theorem B1674739 : Blo 1674037 1674739 := bstep (se 1 (by rfl) ⟨1256054, by rfl⟩ : syracuseStep 1674739 = 2512109) B2512109
theorem B4238851 : Blo 1674037 4238851 := bstep (se 1 (by rfl) ⟨3179138, by rfl⟩ : syracuseStep 4238851 = 6358277) B6358277
theorem B1674755 : Blo 1674037 1674755 := bstep (se 1 (by rfl) ⟨1256066, by rfl⟩ : syracuseStep 1674755 = 2512133) B2512133
theorem B5656067 : Blo 1674037 5656067 := bstep (se 1 (by rfl) ⟨4242050, by rfl⟩ : syracuseStep 5656067 = 8484101) B8484101
theorem B1674771 : Blo 1674037 1674771 := bstep (se 1 (by rfl) ⟨1256078, by rfl⟩ : syracuseStep 1674771 = 2512157) B2512157
theorem B1674787 : Blo 1674037 1674787 := bstep (se 1 (by rfl) ⟨1256090, by rfl⟩ : syracuseStep 1674787 = 2512181) B2512181
theorem B1674803 : Blo 1674037 1674803 := bstep (se 1 (by rfl) ⟨1256102, by rfl⟩ : syracuseStep 1674803 = 2512205) B2512205
theorem B1674819 : Blo 1674037 1674819 := bstep (se 1 (by rfl) ⟨1256114, by rfl⟩ : syracuseStep 1674819 = 2512229) B2512229
theorem B1674835 : Blo 1674037 1674835 := bstep (se 1 (by rfl) ⟨1256126, by rfl⟩ : syracuseStep 1674835 = 2512253) B2512253
theorem B3395171 : Blo 1674037 3395171 := bstep (se 1 (by rfl) ⟨2546378, by rfl⟩ : syracuseStep 3395171 = 5092757) B5092757
theorem B1674851 : Blo 1674037 1674851 := bstep (se 1 (by rfl) ⟨1256138, by rfl⟩ : syracuseStep 1674851 = 2512277) B2512277
theorem B1674867 : Blo 1674037 1674867 := bstep (se 1 (by rfl) ⟨1256150, by rfl⟩ : syracuseStep 1674867 = 2512301) B2512301
theorem B1674883 : Blo 1674037 1674883 := bstep (se 1 (by rfl) ⟨1256162, by rfl⟩ : syracuseStep 1674883 = 2512325) B2512325
theorem B4238993 : Blo 1674037 4238993 := bstep (se 2 (by rfl) ⟨1589622, by rfl⟩ : syracuseStep 4238993 = 3179245) B3179245
theorem B1674899 : Blo 1674037 1674899 := bstep (se 1 (by rfl) ⟨1256174, by rfl⟩ : syracuseStep 1674899 = 2512349) B2512349
theorem B1674915 : Blo 1674037 1674915 := bstep (se 1 (by rfl) ⟨1256186, by rfl⟩ : syracuseStep 1674915 = 2512373) B2512373
theorem B8482481 : Blo 1674037 8482481 := bstep (se 2 (by rfl) ⟨3180930, by rfl⟩ : syracuseStep 8482481 = 6361861) B6361861
theorem B1674931 : Blo 1674037 1674931 := bstep (se 1 (by rfl) ⟨1256198, by rfl⟩ : syracuseStep 1674931 = 2512397) B2512397
theorem B1674947 : Blo 1674037 1674947 := bstep (se 1 (by rfl) ⟨1256210, by rfl⟩ : syracuseStep 1674947 = 2512421) B2512421
theorem B1674963 : Blo 1674037 1674963 := bstep (se 1 (by rfl) ⟨1256222, by rfl⟩ : syracuseStep 1674963 = 2512445) B2512445
theorem B1674979 : Blo 1674037 1674979 := bstep (se 1 (by rfl) ⟨1256234, by rfl⟩ : syracuseStep 1674979 = 2512469) B2512469
theorem B1674995 : Blo 1674037 1674995 := bstep (se 1 (by rfl) ⟨1256246, by rfl⟩ : syracuseStep 1674995 = 2512493) B2512493
theorem B1675011 : Blo 1674037 1675011 := bstep (se 1 (by rfl) ⟨1256258, by rfl⟩ : syracuseStep 1675011 = 2512517) B2512517
theorem B5656337 : Blo 1674037 5656337 := bstep (se 2 (by rfl) ⟨2121126, by rfl⟩ : syracuseStep 5656337 = 4242253) B4242253
theorem B1675027 : Blo 1674037 1675027 := bstep (se 1 (by rfl) ⟨1256270, by rfl⟩ : syracuseStep 1675027 = 2512541) B2512541
theorem B1675043 : Blo 1674037 1675043 := bstep (se 1 (by rfl) ⟨1256282, by rfl⟩ : syracuseStep 1675043 = 2512565) B2512565
theorem B3821347 : Blo 1674037 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B1675059 : Blo 1674037 1675059 := bstep (se 1 (by rfl) ⟨1256294, by rfl⟩ : syracuseStep 1675059 = 2512589) B2512589
theorem B1675075 : Blo 1674037 1675075 := bstep (se 1 (by rfl) ⟨1256306, by rfl⟩ : syracuseStep 1675075 = 2512613) B2512613
theorem B1675091 : Blo 1674037 1675091 := bstep (se 1 (by rfl) ⟨1256318, by rfl⟩ : syracuseStep 1675091 = 2512637) B2512637
theorem B1675107 : Blo 1674037 1675107 := bstep (se 1 (by rfl) ⟨1256330, by rfl⟩ : syracuseStep 1675107 = 2512661) B2512661
theorem B1675123 : Blo 1674037 1675123 := bstep (se 1 (by rfl) ⟨1256342, by rfl⟩ : syracuseStep 1675123 = 2512685) B2512685
theorem B1675139 : Blo 1674037 1675139 := bstep (se 1 (by rfl) ⟨1256354, by rfl⟩ : syracuseStep 1675139 = 2512709) B2512709
theorem B1675155 : Blo 1674037 1675155 := bstep (se 1 (by rfl) ⟨1256366, by rfl⟩ : syracuseStep 1675155 = 2512733) B2512733
theorem B1675171 : Blo 1674037 1675171 := bstep (se 1 (by rfl) ⟨1256378, by rfl⟩ : syracuseStep 1675171 = 2512757) B2512757
theorem B1675187 : Blo 1674037 1675187 := bstep (se 1 (by rfl) ⟨1256390, by rfl⟩ : syracuseStep 1675187 = 2512781) B2512781
theorem B1675203 : Blo 1674037 1675203 := bstep (se 1 (by rfl) ⟨1256402, by rfl⟩ : syracuseStep 1675203 = 2512805) B2512805
theorem B19075013 : Blo 1674037 19075013 := bstep (se 4 (by rfl) ⟨1788282, by rfl⟩ : syracuseStep 19075013 = 3576565) B3576565
theorem B3821521 : Blo 1674037 3821521 := bstep (se 2 (by rfl) ⟨1433070, by rfl⟩ : syracuseStep 3821521 = 2866141) B2866141
theorem B1675219 : Blo 1674037 1675219 := bstep (se 1 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 1675219 = 2512829) B2512829
theorem B6033379 : Blo 1674037 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B1675235 : Blo 1674037 1675235 := bstep (se 1 (by rfl) ⟨1256426, by rfl⟩ : syracuseStep 1675235 = 2512853) B2512853
theorem B1675251 : Blo 1674037 1675251 := bstep (se 1 (by rfl) ⟨1256438, by rfl⟩ : syracuseStep 1675251 = 2512877) B2512877
theorem B1675267 : Blo 1674037 1675267 := bstep (se 1 (by rfl) ⟨1256450, by rfl⟩ : syracuseStep 1675267 = 2512901) B2512901
theorem B2682899 : Blo 1674037 2682899 := bstep (se 1 (by rfl) ⟨2012174, by rfl⟩ : syracuseStep 2682899 = 4024349) B4024349
theorem B1675283 : Blo 1674037 1675283 := bstep (se 1 (by rfl) ⟨1256462, by rfl⟩ : syracuseStep 1675283 = 2512925) B2512925
theorem B39759893 : Blo 1674037 39759893 := bstep (se 6 (by rfl) ⟨931872, by rfl⟩ : syracuseStep 39759893 = 1863745) B1863745
theorem B1675299 : Blo 1674037 1675299 := bstep (se 1 (by rfl) ⟨1256474, by rfl⟩ : syracuseStep 1675299 = 2512949) B2512949
theorem B1675315 : Blo 1674037 1675315 := bstep (se 1 (by rfl) ⟨1256486, by rfl⟩ : syracuseStep 1675315 = 2512973) B2512973
theorem B1675331 : Blo 1674037 1675331 := bstep (se 1 (by rfl) ⟨1256498, by rfl⟩ : syracuseStep 1675331 = 2512997) B2512997
theorem B1675347 : Blo 1674037 1675347 := bstep (se 1 (by rfl) ⟨1256510, by rfl⟩ : syracuseStep 1675347 = 2513021) B2513021
theorem B1675363 : Blo 1674037 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B13578353 : Blo 1674037 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B1675379 : Blo 1674037 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B1675395 : Blo 1674037 1675395 := bstep (se 1 (by rfl) ⟨1256546, by rfl⟩ : syracuseStep 1675395 = 2513093) B2513093
theorem B1675411 : Blo 1674037 1675411 := bstep (se 1 (by rfl) ⟨1256558, by rfl⟩ : syracuseStep 1675411 = 2513117) B2513117
theorem B1675427 : Blo 1674037 1675427 := bstep (se 1 (by rfl) ⟨1256570, by rfl⟩ : syracuseStep 1675427 = 2513141) B2513141
theorem B1675443 : Blo 1674037 1675443 := bstep (se 1 (by rfl) ⟨1256582, by rfl⟩ : syracuseStep 1675443 = 2513165) B2513165
theorem B1675459 : Blo 1674037 1675459 := bstep (se 1 (by rfl) ⟨1256594, by rfl⟩ : syracuseStep 1675459 = 2513189) B2513189
theorem B2511059 : Blo 1674037 2511059 := bstep (se 1 (by rfl) ⟨1883294, by rfl⟩ : syracuseStep 2511059 = 3766589) B3766589
theorem B2683091 : Blo 1674037 2683091 := bstep (se 1 (by rfl) ⟨2012318, by rfl⟩ : syracuseStep 2683091 = 4024637) B4024637
theorem B1675475 : Blo 1674037 1675475 := bstep (se 1 (by rfl) ⟨1256606, by rfl⟩ : syracuseStep 1675475 = 2513213) B2513213
theorem B1675491 : Blo 1674037 1675491 := bstep (se 1 (by rfl) ⟨1256618, by rfl⟩ : syracuseStep 1675491 = 2513237) B2513237
theorem B2511089 : Blo 1674037 2511089 := bstep (se 2 (by rfl) ⟨941658, by rfl⟩ : syracuseStep 2511089 = 1883317) B1883317
theorem B16765169 : Blo 1674037 16765169 := bstep (se 2 (by rfl) ⟨6286938, by rfl⟩ : syracuseStep 16765169 = 12573877) B12573877
theorem B1675507 : Blo 1674037 1675507 := bstep (se 1 (by rfl) ⟨1256630, by rfl⟩ : syracuseStep 1675507 = 2513261) B2513261
theorem B2511107 : Blo 1674037 2511107 := bstep (se 1 (by rfl) ⟨1883330, by rfl⟩ : syracuseStep 2511107 = 3766661) B3766661
theorem B1675523 : Blo 1674037 1675523 := bstep (se 1 (by rfl) ⟨1256642, by rfl⟩ : syracuseStep 1675523 = 2513285) B2513285
theorem B1675539 : Blo 1674037 1675539 := bstep (se 1 (by rfl) ⟨1256654, by rfl⟩ : syracuseStep 1675539 = 2513309) B2513309
theorem B2511137 : Blo 1674037 2511137 := bstep (se 2 (by rfl) ⟨941676, by rfl⟩ : syracuseStep 2511137 = 1883353) B1883353
theorem B1675555 : Blo 1674037 1675555 := bstep (se 1 (by rfl) ⟨1256666, by rfl⟩ : syracuseStep 1675555 = 2513333) B2513333
theorem B2511155 : Blo 1674037 2511155 := bstep (se 1 (by rfl) ⟨1883366, by rfl⟩ : syracuseStep 2511155 = 3766733) B3766733
theorem B1675571 : Blo 1674037 1675571 := bstep (se 1 (by rfl) ⟨1256678, by rfl⟩ : syracuseStep 1675571 = 2513357) B2513357
theorem B1675587 : Blo 1674037 1675587 := bstep (se 1 (by rfl) ⟨1256690, by rfl⟩ : syracuseStep 1675587 = 2513381) B2513381
theorem B2511185 : Blo 1674037 2511185 := bstep (se 2 (by rfl) ⟨941694, by rfl⟩ : syracuseStep 2511185 = 1883389) B1883389
theorem B2683219 : Blo 1674037 2683219 := bstep (se 1 (by rfl) ⟨2012414, by rfl⟩ : syracuseStep 2683219 = 4024829) B4024829
theorem B1675603 : Blo 1674037 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B2511203 : Blo 1674037 2511203 := bstep (se 1 (by rfl) ⟨1883402, by rfl⟩ : syracuseStep 2511203 = 3766805) B3766805
theorem B1675619 : Blo 1674037 1675619 := bstep (se 1 (by rfl) ⟨1256714, by rfl⟩ : syracuseStep 1675619 = 2513429) B2513429
theorem B1675635 : Blo 1674037 1675635 := bstep (se 1 (by rfl) ⟨1256726, by rfl⟩ : syracuseStep 1675635 = 2513453) B2513453
theorem B2511233 : Blo 1674037 2511233 := bstep (se 2 (by rfl) ⟨941712, by rfl⟩ : syracuseStep 2511233 = 1883425) B1883425
theorem B1675651 : Blo 1674037 1675651 := bstep (se 1 (by rfl) ⟨1256738, by rfl⟩ : syracuseStep 1675651 = 2513477) B2513477
theorem B24138125 : Blo 1674037 24138125 := bstep (se 3 (by rfl) ⟨4525898, by rfl⟩ : syracuseStep 24138125 = 9051797) B9051797
theorem B16101773 : Blo 1674037 16101773 := bstep (se 3 (by rfl) ⟨3019082, by rfl⟩ : syracuseStep 16101773 = 6038165) B6038165
theorem B2511251 : Blo 1674037 2511251 := bstep (se 1 (by rfl) ⟨1883438, by rfl⟩ : syracuseStep 2511251 = 3766877) B3766877
theorem B1675667 : Blo 1674037 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B1675683 : Blo 1674037 1675683 := bstep (se 1 (by rfl) ⟨1256762, by rfl⟩ : syracuseStep 1675683 = 2513525) B2513525
theorem B2511281 : Blo 1674037 2511281 := bstep (se 2 (by rfl) ⟨941730, by rfl⟩ : syracuseStep 2511281 = 1883461) B1883461
theorem B5091761 : Blo 1674037 5091761 := bstep (se 2 (by rfl) ⟨1909410, by rfl⟩ : syracuseStep 5091761 = 3818821) B3818821
theorem B3576241 : Blo 1674037 3576241 := bstep (se 2 (by rfl) ⟨1341090, by rfl⟩ : syracuseStep 3576241 = 2682181) B2682181
theorem B1675699 : Blo 1674037 1675699 := bstep (se 1 (by rfl) ⟨1256774, by rfl⟩ : syracuseStep 1675699 = 2513549) B2513549
theorem B2511299 : Blo 1674037 2511299 := bstep (se 1 (by rfl) ⟨1883474, by rfl⟩ : syracuseStep 2511299 = 3766949) B3766949
theorem B1675715 : Blo 1674037 1675715 := bstep (se 1 (by rfl) ⟨1256786, by rfl⟩ : syracuseStep 1675715 = 2513573) B2513573
theorem B1675731 : Blo 1674037 1675731 := bstep (se 1 (by rfl) ⟨1256798, by rfl⟩ : syracuseStep 1675731 = 2513597) B2513597
theorem B2511329 : Blo 1674037 2511329 := bstep (se 2 (by rfl) ⟨941748, by rfl⟩ : syracuseStep 2511329 = 1883497) B1883497
theorem B1675747 : Blo 1674037 1675747 := bstep (se 1 (by rfl) ⟨1256810, by rfl⟩ : syracuseStep 1675747 = 2513621) B2513621
theorem B19083761 : Blo 1674037 19083761 := bstep (se 2 (by rfl) ⟨7156410, by rfl⟩ : syracuseStep 19083761 = 14312821) B14312821
theorem B2511347 : Blo 1674037 2511347 := bstep (se 1 (by rfl) ⟨1883510, by rfl⟩ : syracuseStep 2511347 = 3767021) B3767021
theorem B1675763 : Blo 1674037 1675763 := bstep (se 1 (by rfl) ⟨1256822, by rfl⟩ : syracuseStep 1675763 = 2513645) B2513645
theorem B1675779 : Blo 1674037 1675779 := bstep (se 1 (by rfl) ⟨1256834, by rfl⟩ : syracuseStep 1675779 = 2513669) B2513669
theorem B2511377 : Blo 1674037 2511377 := bstep (se 2 (by rfl) ⟨941766, by rfl⟩ : syracuseStep 2511377 = 1883533) B1883533
theorem B1675795 : Blo 1674037 1675795 := bstep (se 1 (by rfl) ⟨1256846, by rfl⟩ : syracuseStep 1675795 = 2513693) B2513693
theorem B2511395 : Blo 1674037 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B7156259 : Blo 1674037 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B1675811 : Blo 1674037 1675811 := bstep (se 1 (by rfl) ⟨1256858, by rfl⟩ : syracuseStep 1675811 = 2513717) B2513717
theorem B6361649 : Blo 1674037 6361649 := bstep (se 2 (by rfl) ⟨2385618, by rfl⟩ : syracuseStep 6361649 = 4771237) B4771237
theorem B3019313 : Blo 1674037 3019313 := bstep (se 2 (by rfl) ⟨1132242, by rfl⟩ : syracuseStep 3019313 = 2264485) B2264485
theorem B1675827 : Blo 1674037 1675827 := bstep (se 1 (by rfl) ⟨1256870, by rfl⟩ : syracuseStep 1675827 = 2513741) B2513741
theorem B2511425 : Blo 1674037 2511425 := bstep (se 2 (by rfl) ⟨941784, by rfl⟩ : syracuseStep 2511425 = 1883569) B1883569
theorem B1675843 : Blo 1674037 1675843 := bstep (se 1 (by rfl) ⟨1256882, by rfl⟩ : syracuseStep 1675843 = 2513765) B2513765
theorem B2511443 : Blo 1674037 2511443 := bstep (se 1 (by rfl) ⟨1883582, by rfl⟩ : syracuseStep 2511443 = 3767165) B3767165
theorem B1675859 : Blo 1674037 1675859 := bstep (se 1 (by rfl) ⟨1256894, by rfl⟩ : syracuseStep 1675859 = 2513789) B2513789
theorem B1675875 : Blo 1674037 1675875 := bstep (se 1 (by rfl) ⟨1256906, by rfl⟩ : syracuseStep 1675875 = 2513813) B2513813
theorem B2511473 : Blo 1674037 2511473 := bstep (se 2 (by rfl) ⟨941802, by rfl⟩ : syracuseStep 2511473 = 1883605) B1883605
theorem B4239985 : Blo 1674037 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B1675891 : Blo 1674037 1675891 := bstep (se 1 (by rfl) ⟨1256918, by rfl⟩ : syracuseStep 1675891 = 2513837) B2513837
theorem B2511491 : Blo 1674037 2511491 := bstep (se 1 (by rfl) ⟨1883618, by rfl⟩ : syracuseStep 2511491 = 3767237) B3767237
theorem B1675907 : Blo 1674037 1675907 := bstep (se 1 (by rfl) ⟨1256930, by rfl⟩ : syracuseStep 1675907 = 2513861) B2513861
theorem B1675923 : Blo 1674037 1675923 := bstep (se 1 (by rfl) ⟨1256942, by rfl⟩ : syracuseStep 1675923 = 2513885) B2513885
theorem B2511521 : Blo 1674037 2511521 := bstep (se 2 (by rfl) ⟨941820, by rfl⟩ : syracuseStep 2511521 = 1883641) B1883641
theorem B1675939 : Blo 1674037 1675939 := bstep (se 1 (by rfl) ⟨1256954, by rfl⟩ : syracuseStep 1675939 = 2513909) B2513909
theorem B2511539 : Blo 1674037 2511539 := bstep (se 1 (by rfl) ⟨1883654, by rfl⟩ : syracuseStep 2511539 = 3767309) B3767309
theorem B1675955 : Blo 1674037 1675955 := bstep (se 1 (by rfl) ⟨1256966, by rfl⟩ : syracuseStep 1675955 = 2513933) B2513933
theorem B1675971 : Blo 1674037 1675971 := bstep (se 1 (by rfl) ⟨1256978, by rfl⟩ : syracuseStep 1675971 = 2513957) B2513957
theorem B2511569 : Blo 1674037 2511569 := bstep (se 2 (by rfl) ⟨941838, by rfl⟩ : syracuseStep 2511569 = 1883677) B1883677
theorem B1675987 : Blo 1674037 1675987 := bstep (se 1 (by rfl) ⟨1256990, by rfl⟩ : syracuseStep 1675987 = 2513981) B2513981
theorem B2511587 : Blo 1674037 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B1676003 : Blo 1674037 1676003 := bstep (se 1 (by rfl) ⟨1257002, by rfl⟩ : syracuseStep 1676003 = 2514005) B2514005
theorem B1676019 : Blo 1674037 1676019 := bstep (se 1 (by rfl) ⟨1257014, by rfl⟩ : syracuseStep 1676019 = 2514029) B2514029
theorem B2511617 : Blo 1674037 2511617 := bstep (se 2 (by rfl) ⟨941856, by rfl⟩ : syracuseStep 2511617 = 1883713) B1883713
theorem B1676035 : Blo 1674037 1676035 := bstep (se 1 (by rfl) ⟨1257026, by rfl⟩ : syracuseStep 1676035 = 2514053) B2514053
theorem B2511635 : Blo 1674037 2511635 := bstep (se 1 (by rfl) ⟨1883726, by rfl⟩ : syracuseStep 2511635 = 3767453) B3767453
theorem B61092629 : Blo 1674037 61092629 := bstep (se 6 (by rfl) ⟨1431858, by rfl⟩ : syracuseStep 61092629 = 2863717) B2863717
theorem B2511665 : Blo 1674037 2511665 := bstep (se 2 (by rfl) ⟨941874, by rfl⟩ : syracuseStep 2511665 = 1883749) B1883749
theorem B2511683 : Blo 1674037 2511683 := bstep (se 1 (by rfl) ⟨1883762, by rfl⟩ : syracuseStep 2511683 = 3767525) B3767525
theorem B2511713 : Blo 1674037 2511713 := bstep (se 2 (by rfl) ⟨941892, by rfl⟩ : syracuseStep 2511713 = 1883785) B1883785
theorem B2511731 : Blo 1674037 2511731 := bstep (se 1 (by rfl) ⟨1883798, by rfl⟩ : syracuseStep 2511731 = 3767597) B3767597
theorem B4240259 : Blo 1674037 4240259 := bstep (se 1 (by rfl) ⟨3180194, by rfl⟩ : syracuseStep 4240259 = 6360389) B6360389
theorem B2511761 : Blo 1674037 2511761 := bstep (se 2 (by rfl) ⟨941910, by rfl⟩ : syracuseStep 2511761 = 1883821) B1883821
theorem B4772753 : Blo 1674037 4772753 := bstep (se 2 (by rfl) ⟨1789782, by rfl⟩ : syracuseStep 4772753 = 3579565) B3579565
theorem B2511779 : Blo 1674037 2511779 := bstep (se 1 (by rfl) ⟨1883834, by rfl⟩ : syracuseStep 2511779 = 3767669) B3767669
theorem B2511809 : Blo 1674037 2511809 := bstep (se 2 (by rfl) ⟨941928, by rfl⟩ : syracuseStep 2511809 = 1883857) B1883857
theorem B2511827 : Blo 1674037 2511827 := bstep (se 1 (by rfl) ⟨1883870, by rfl⟩ : syracuseStep 2511827 = 3767741) B3767741
theorem B2683859 : Blo 1674037 2683859 := bstep (se 1 (by rfl) ⟨2012894, by rfl⟩ : syracuseStep 2683859 = 4025789) B4025789
theorem B2511857 : Blo 1674037 2511857 := bstep (se 2 (by rfl) ⟨941946, by rfl⟩ : syracuseStep 2511857 = 1883893) B1883893
theorem B2511875 : Blo 1674037 2511875 := bstep (se 1 (by rfl) ⟨1883906, by rfl⟩ : syracuseStep 2511875 = 3767813) B3767813
theorem B2511905 : Blo 1674037 2511905 := bstep (se 2 (by rfl) ⟨941964, by rfl⟩ : syracuseStep 2511905 = 1883929) B1883929
theorem B2683937 : Blo 1674037 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B2511923 : Blo 1674037 2511923 := bstep (se 1 (by rfl) ⟨1883942, by rfl⟩ : syracuseStep 2511923 = 3767885) B3767885
theorem B3576899 : Blo 1674037 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B4240451 : Blo 1674037 4240451 := bstep (se 1 (by rfl) ⟨3180338, by rfl⟩ : syracuseStep 4240451 = 6360677) B6360677
theorem B2511953 : Blo 1674037 2511953 := bstep (se 2 (by rfl) ⟨941982, by rfl⟩ : syracuseStep 2511953 = 1883965) B1883965
theorem B2511971 : Blo 1674037 2511971 := bstep (se 1 (by rfl) ⟨1883978, by rfl⟩ : syracuseStep 2511971 = 3767957) B3767957
theorem B8483939 : Blo 1674037 8483939 := bstep (se 1 (by rfl) ⟨6362954, by rfl⟩ : syracuseStep 8483939 = 12725909) B12725909
theorem B68736113 : Blo 1674037 68736113 := bstep (se 2 (by rfl) ⟨25776042, by rfl⟩ : syracuseStep 68736113 = 51552085) B51552085
theorem B2512001 : Blo 1674037 2512001 := bstep (se 2 (by rfl) ⟨942000, by rfl⟩ : syracuseStep 2512001 = 1884001) B1884001
theorem B2512019 : Blo 1674037 2512019 := bstep (se 1 (by rfl) ⟨1884014, by rfl⟩ : syracuseStep 2512019 = 3768029) B3768029
theorem B2512049 : Blo 1674037 2512049 := bstep (se 2 (by rfl) ⟨942018, by rfl⟩ : syracuseStep 2512049 = 1884037) B1884037
theorem B2512067 : Blo 1674037 2512067 := bstep (se 1 (by rfl) ⟨1884050, by rfl⟩ : syracuseStep 2512067 = 3768101) B3768101
theorem B2512097 : Blo 1674037 2512097 := bstep (se 2 (by rfl) ⟨942036, by rfl⟩ : syracuseStep 2512097 = 1884073) B1884073
theorem B2118899 : Blo 1674037 2118899 := bstep (se 1 (by rfl) ⟨1589174, by rfl⟩ : syracuseStep 2118899 = 3178349) B3178349
theorem B2512115 : Blo 1674037 2512115 := bstep (se 1 (by rfl) ⟨1884086, by rfl⟩ : syracuseStep 2512115 = 3768173) B3768173
theorem B2512145 : Blo 1674037 2512145 := bstep (se 2 (by rfl) ⟨942054, by rfl⟩ : syracuseStep 2512145 = 1884109) B1884109
theorem B2512163 : Blo 1674037 2512163 := bstep (se 1 (by rfl) ⟨1884122, by rfl⟩ : syracuseStep 2512163 = 3768245) B3768245
theorem B2512193 : Blo 1674037 2512193 := bstep (se 2 (by rfl) ⟨942072, by rfl⟩ : syracuseStep 2512193 = 1884145) B1884145
theorem B2512211 : Blo 1674037 2512211 := bstep (se 1 (by rfl) ⟨1884158, by rfl⟩ : syracuseStep 2512211 = 3768317) B3768317
theorem B2512241 : Blo 1674037 2512241 := bstep (se 2 (by rfl) ⟨942090, by rfl⟩ : syracuseStep 2512241 = 1884181) B1884181
theorem B14308721 : Blo 1674037 14308721 := bstep (se 2 (by rfl) ⟨5365770, by rfl⟩ : syracuseStep 14308721 = 10731541) B10731541
theorem B2512259 : Blo 1674037 2512259 := bstep (se 1 (by rfl) ⟨1884194, by rfl⟩ : syracuseStep 2512259 = 3768389) B3768389
theorem B2512289 : Blo 1674037 2512289 := bstep (se 2 (by rfl) ⟨942108, by rfl⟩ : syracuseStep 2512289 = 1884217) B1884217
theorem B2684321 : Blo 1674037 2684321 := bstep (se 2 (by rfl) ⟨1006620, by rfl⟩ : syracuseStep 2684321 = 2013241) B2013241
theorem B2512307 : Blo 1674037 2512307 := bstep (se 1 (by rfl) ⟨1884230, by rfl⟩ : syracuseStep 2512307 = 3768461) B3768461
theorem B9541061 : Blo 1674037 9541061 := bstep (se 4 (by rfl) ⟨894474, by rfl⟩ : syracuseStep 9541061 = 1788949) B1788949
theorem B2864593 : Blo 1674037 2864593 := bstep (se 2 (by rfl) ⟨1074222, by rfl⟩ : syracuseStep 2864593 = 2148445) B2148445
theorem B2512337 : Blo 1674037 2512337 := bstep (se 2 (by rfl) ⟨942126, by rfl⟩ : syracuseStep 2512337 = 1884253) B1884253
theorem B2512355 : Blo 1674037 2512355 := bstep (se 1 (by rfl) ⟨1884266, by rfl⟩ : syracuseStep 2512355 = 3768533) B3768533
theorem B2512385 : Blo 1674037 2512385 := bstep (se 2 (by rfl) ⟨942144, by rfl⟩ : syracuseStep 2512385 = 1884289) B1884289
theorem B2512403 : Blo 1674037 2512403 := bstep (se 1 (by rfl) ⟨1884302, by rfl⟩ : syracuseStep 2512403 = 3768605) B3768605
theorem B2684449 : Blo 1674037 2684449 := bstep (se 2 (by rfl) ⟨1006668, by rfl⟩ : syracuseStep 2684449 = 2013337) B2013337
theorem B5649965 : Blo 1674037 5649965 := bstep (se 3 (by rfl) ⟨1059368, by rfl⟩ : syracuseStep 5649965 = 2118737) B2118737
theorem B2512433 : Blo 1674037 2512433 := bstep (se 2 (by rfl) ⟨942162, by rfl⟩ : syracuseStep 2512433 = 1884325) B1884325
theorem B2512451 : Blo 1674037 2512451 := bstep (se 1 (by rfl) ⟨1884338, by rfl⟩ : syracuseStep 2512451 = 3768677) B3768677
theorem B2512481 : Blo 1674037 2512481 := bstep (se 2 (by rfl) ⟨942180, by rfl⟩ : syracuseStep 2512481 = 1884361) B1884361
theorem B5650019 : Blo 1674037 5650019 := bstep (se 1 (by rfl) ⟨4237514, by rfl⟩ : syracuseStep 5650019 = 8475029) B8475029
theorem B18347633 : Blo 1674037 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B2512499 : Blo 1674037 2512499 := bstep (se 1 (by rfl) ⟨1884374, by rfl⟩ : syracuseStep 2512499 = 3768749) B3768749
theorem B2512529 : Blo 1674037 2512529 := bstep (se 2 (by rfl) ⟨942198, by rfl⟩ : syracuseStep 2512529 = 1884397) B1884397
theorem B2512547 : Blo 1674037 2512547 := bstep (se 1 (by rfl) ⟨1884410, by rfl⟩ : syracuseStep 2512547 = 3768821) B3768821
theorem B6788785 : Blo 1674037 6788785 := bstep (se 2 (by rfl) ⟨2545794, by rfl⟩ : syracuseStep 6788785 = 5091589) B5091589
theorem B2512577 : Blo 1674037 2512577 := bstep (se 2 (by rfl) ⟨942216, by rfl⟩ : syracuseStep 2512577 = 1884433) B1884433
theorem B2512595 : Blo 1674037 2512595 := bstep (se 1 (by rfl) ⟨1884446, by rfl⟩ : syracuseStep 2512595 = 3768893) B3768893
theorem B2545393 : Blo 1674037 2545393 := bstep (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) B1909045
theorem B2512625 : Blo 1674037 2512625 := bstep (se 2 (by rfl) ⟨942234, by rfl⟩ : syracuseStep 2512625 = 1884469) B1884469
theorem B2512643 : Blo 1674037 2512643 := bstep (se 1 (by rfl) ⟨1884482, by rfl⟩ : syracuseStep 2512643 = 3768965) B3768965
theorem B2512673 : Blo 1674037 2512673 := bstep (se 2 (by rfl) ⟨942252, by rfl⟩ : syracuseStep 2512673 = 1884505) B1884505
theorem B2512691 : Blo 1674037 2512691 := bstep (se 1 (by rfl) ⟨1884518, by rfl⟩ : syracuseStep 2512691 = 3769037) B3769037
theorem B2512721 : Blo 1674037 2512721 := bstep (se 2 (by rfl) ⟨942270, by rfl⟩ : syracuseStep 2512721 = 1884541) B1884541
theorem B2512739 : Blo 1674037 2512739 := bstep (se 1 (by rfl) ⟨1884554, by rfl⟩ : syracuseStep 2512739 = 3769109) B3769109
theorem B5650289 : Blo 1674037 5650289 := bstep (se 2 (by rfl) ⟨2118858, by rfl⟩ : syracuseStep 5650289 = 4237717) B4237717
theorem B13588337 : Blo 1674037 13588337 := bstep (se 2 (by rfl) ⟨5095626, by rfl⟩ : syracuseStep 13588337 = 10191253) B10191253
theorem B2512769 : Blo 1674037 2512769 := bstep (se 2 (by rfl) ⟨942288, by rfl⟩ : syracuseStep 2512769 = 1884577) B1884577
theorem B8484749 : Blo 1674037 8484749 := bstep (se 3 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 8484749 = 3181781) B3181781
theorem B3577745 : Blo 1674037 3577745 := bstep (se 2 (by rfl) ⟨1341654, by rfl⟩ : syracuseStep 3577745 = 2683309) B2683309
theorem B2512787 : Blo 1674037 2512787 := bstep (se 1 (by rfl) ⟨1884590, by rfl⟩ : syracuseStep 2512787 = 3769181) B3769181
theorem B2512817 : Blo 1674037 2512817 := bstep (se 2 (by rfl) ⟨942306, by rfl⟩ : syracuseStep 2512817 = 1884613) B1884613
theorem B2119603 : Blo 1674037 2119603 := bstep (se 1 (by rfl) ⟨1589702, by rfl⟩ : syracuseStep 2119603 = 3179405) B3179405
theorem B2512835 : Blo 1674037 2512835 := bstep (se 1 (by rfl) ⟨1884626, by rfl⟩ : syracuseStep 2512835 = 3769253) B3769253
theorem B2512865 : Blo 1674037 2512865 := bstep (se 2 (by rfl) ⟨942324, by rfl⟩ : syracuseStep 2512865 = 1884649) B1884649
theorem B6363107 : Blo 1674037 6363107 := bstep (se 1 (by rfl) ⟨4772330, by rfl⟩ : syracuseStep 6363107 = 9544661) B9544661
theorem B4241393 : Blo 1674037 4241393 := bstep (se 2 (by rfl) ⟨1590522, by rfl⟩ : syracuseStep 4241393 = 3181045) B3181045
theorem B2512883 : Blo 1674037 2512883 := bstep (se 1 (by rfl) ⟨1884662, by rfl⟩ : syracuseStep 2512883 = 3769325) B3769325
theorem B2512913 : Blo 1674037 2512913 := bstep (se 2 (by rfl) ⟨942342, by rfl⟩ : syracuseStep 2512913 = 1884685) B1884685
theorem B2119699 : Blo 1674037 2119699 := bstep (se 1 (by rfl) ⟨1589774, by rfl⟩ : syracuseStep 2119699 = 3179549) B3179549
theorem B2512931 : Blo 1674037 2512931 := bstep (se 1 (by rfl) ⟨1884698, by rfl⟩ : syracuseStep 2512931 = 3769397) B3769397
theorem B4241443 : Blo 1674037 4241443 := bstep (se 1 (by rfl) ⟨3181082, by rfl⟩ : syracuseStep 4241443 = 6362165) B6362165
theorem B2512961 : Blo 1674037 2512961 := bstep (se 2 (by rfl) ⟨942360, by rfl⟩ : syracuseStep 2512961 = 1884721) B1884721
theorem B2512979 : Blo 1674037 2512979 := bstep (se 1 (by rfl) ⟨1884734, by rfl⟩ : syracuseStep 2512979 = 3769469) B3769469
theorem B2513009 : Blo 1674037 2513009 := bstep (se 2 (by rfl) ⟨942378, by rfl⟩ : syracuseStep 2513009 = 1884757) B1884757
theorem B9541745 : Blo 1674037 9541745 := bstep (se 2 (by rfl) ⟨3578154, by rfl⟩ : syracuseStep 9541745 = 7156309) B7156309
theorem B2177155 : Blo 1674037 2177155 := bstep (se 1 (by rfl) ⟨1632866, by rfl⟩ : syracuseStep 2177155 = 3265733) B3265733
theorem B2513027 : Blo 1674037 2513027 := bstep (se 1 (by rfl) ⟨1884770, by rfl⟩ : syracuseStep 2513027 = 3769541) B3769541
theorem B2865299 : Blo 1674037 2865299 := bstep (se 1 (by rfl) ⟨2148974, by rfl⟩ : syracuseStep 2865299 = 4297949) B4297949
theorem B2513057 : Blo 1674037 2513057 := bstep (se 2 (by rfl) ⟨942396, by rfl⟩ : syracuseStep 2513057 = 1884793) B1884793
theorem B4241585 : Blo 1674037 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B2513075 : Blo 1674037 2513075 := bstep (se 1 (by rfl) ⟨1884806, by rfl⟩ : syracuseStep 2513075 = 3769613) B3769613
theorem B2513105 : Blo 1674037 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B2513123 : Blo 1674037 2513123 := bstep (se 1 (by rfl) ⟨1884842, by rfl⟩ : syracuseStep 2513123 = 3769685) B3769685
theorem B2513153 : Blo 1674037 2513153 := bstep (se 2 (by rfl) ⟨942432, by rfl⟩ : syracuseStep 2513153 = 1884865) B1884865
theorem B2513171 : Blo 1674037 2513171 := bstep (se 1 (by rfl) ⟨1884878, by rfl⟩ : syracuseStep 2513171 = 3769757) B3769757
theorem B2513201 : Blo 1674037 2513201 := bstep (se 2 (by rfl) ⟨942450, by rfl⟩ : syracuseStep 2513201 = 1884901) B1884901
theorem B2513219 : Blo 1674037 2513219 := bstep (se 1 (by rfl) ⟨1884914, by rfl⟩ : syracuseStep 2513219 = 3769829) B3769829
theorem B2513249 : Blo 1674037 2513249 := bstep (se 2 (by rfl) ⟨942468, by rfl⟩ : syracuseStep 2513249 = 1884937) B1884937
theorem B2513267 : Blo 1674037 2513267 := bstep (se 1 (by rfl) ⟨1884950, by rfl⟩ : syracuseStep 2513267 = 3769901) B3769901
theorem B5650829 : Blo 1674037 5650829 := bstep (se 3 (by rfl) ⟨1059530, by rfl⟩ : syracuseStep 5650829 = 2119061) B2119061
theorem B2513297 : Blo 1674037 2513297 := bstep (se 2 (by rfl) ⟨942486, by rfl⟩ : syracuseStep 2513297 = 1884973) B1884973
theorem B2513315 : Blo 1674037 2513315 := bstep (se 1 (by rfl) ⟨1884986, by rfl⟩ : syracuseStep 2513315 = 3769973) B3769973
theorem B2513345 : Blo 1674037 2513345 := bstep (se 2 (by rfl) ⟨942504, by rfl⟩ : syracuseStep 2513345 = 1885009) B1885009
theorem B5650883 : Blo 1674037 5650883 := bstep (se 1 (by rfl) ⟨4238162, by rfl⟩ : syracuseStep 5650883 = 8476325) B8476325
theorem B2513363 : Blo 1674037 2513363 := bstep (se 1 (by rfl) ⟨1885022, by rfl⟩ : syracuseStep 2513363 = 3770045) B3770045
theorem B3766769 : Blo 1674037 3766769 := bstep (se 2 (by rfl) ⟨1412538, by rfl⟩ : syracuseStep 3766769 = 2825077) B2825077
theorem B2513393 : Blo 1674037 2513393 := bstep (se 2 (by rfl) ⟨942522, by rfl⟩ : syracuseStep 2513393 = 1885045) B1885045
theorem B7158257 : Blo 1674037 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B3766787 : Blo 1674037 3766787 := bstep (se 1 (by rfl) ⟨2825090, by rfl⟩ : syracuseStep 3766787 = 5650181) B5650181
theorem B2120195 : Blo 1674037 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B2513411 : Blo 1674037 2513411 := bstep (se 1 (by rfl) ⟨1885058, by rfl⟩ : syracuseStep 2513411 = 3770117) B3770117
theorem B2513441 : Blo 1674037 2513441 := bstep (se 2 (by rfl) ⟨942540, by rfl⟩ : syracuseStep 2513441 = 1885081) B1885081
theorem B2513459 : Blo 1674037 2513459 := bstep (se 1 (by rfl) ⟨1885094, by rfl⟩ : syracuseStep 2513459 = 3770189) B3770189
theorem B11459141 : Blo 1674037 11459141 := bstep (se 4 (by rfl) ⟨1074294, by rfl⟩ : syracuseStep 11459141 = 2148589) B2148589
theorem B2546257 : Blo 1674037 2546257 := bstep (se 2 (by rfl) ⟨954846, by rfl⟩ : syracuseStep 2546257 = 1909693) B1909693
theorem B2513489 : Blo 1674037 2513489 := bstep (se 2 (by rfl) ⟨942558, by rfl⟩ : syracuseStep 2513489 = 1885117) B1885117
theorem B2513507 : Blo 1674037 2513507 := bstep (se 1 (by rfl) ⟨1885130, by rfl⟩ : syracuseStep 2513507 = 3770261) B3770261
theorem B8477297 : Blo 1674037 8477297 := bstep (se 2 (by rfl) ⟨3178986, by rfl⟩ : syracuseStep 8477297 = 6357973) B6357973
theorem B4528753 : Blo 1674037 4528753 := bstep (se 2 (by rfl) ⟨1698282, by rfl⟩ : syracuseStep 4528753 = 3396565) B3396565
theorem B2513537 : Blo 1674037 2513537 := bstep (se 2 (by rfl) ⟨942576, by rfl⟩ : syracuseStep 2513537 = 1885153) B1885153
theorem B2513555 : Blo 1674037 2513555 := bstep (se 1 (by rfl) ⟨1885166, by rfl⟩ : syracuseStep 2513555 = 3770333) B3770333
theorem B2513585 : Blo 1674037 2513585 := bstep (se 2 (by rfl) ⟨942594, by rfl⟩ : syracuseStep 2513585 = 1885189) B1885189
theorem B2513603 : Blo 1674037 2513603 := bstep (se 1 (by rfl) ⟨1885202, by rfl⟩ : syracuseStep 2513603 = 3770405) B3770405
theorem B5651153 : Blo 1674037 5651153 := bstep (se 2 (by rfl) ⟨2119182, by rfl⟩ : syracuseStep 5651153 = 4238365) B4238365
theorem B2513633 : Blo 1674037 2513633 := bstep (se 2 (by rfl) ⟨942612, by rfl⟩ : syracuseStep 2513633 = 1885225) B1885225
theorem B2513651 : Blo 1674037 2513651 := bstep (se 1 (by rfl) ⟨1885238, by rfl⟩ : syracuseStep 2513651 = 3770477) B3770477
theorem B3767057 : Blo 1674037 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2513681 : Blo 1674037 2513681 := bstep (se 2 (by rfl) ⟨942630, by rfl⟩ : syracuseStep 2513681 = 1885261) B1885261
theorem B3767075 : Blo 1674037 3767075 := bstep (se 1 (by rfl) ⟨2825306, by rfl⟩ : syracuseStep 3767075 = 5650613) B5650613
theorem B2513699 : Blo 1674037 2513699 := bstep (se 1 (by rfl) ⟨1885274, by rfl⟩ : syracuseStep 2513699 = 3770549) B3770549
theorem B2513729 : Blo 1674037 2513729 := bstep (se 2 (by rfl) ⟨942648, by rfl⟩ : syracuseStep 2513729 = 1885297) B1885297
theorem B2513747 : Blo 1674037 2513747 := bstep (se 1 (by rfl) ⟨1885310, by rfl⟩ : syracuseStep 2513747 = 3770621) B3770621
theorem B2825057 : Blo 1674037 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B5364593 : Blo 1674037 5364593 := bstep (se 2 (by rfl) ⟨2011722, by rfl⟩ : syracuseStep 5364593 = 4023445) B4023445
theorem B2513777 : Blo 1674037 2513777 := bstep (se 2 (by rfl) ⟨942666, by rfl⟩ : syracuseStep 2513777 = 1885333) B1885333
theorem B2513795 : Blo 1674037 2513795 := bstep (se 1 (by rfl) ⟨1885346, by rfl⟩ : syracuseStep 2513795 = 3770693) B3770693
theorem B10738565 : Blo 1674037 10738565 := bstep (se 4 (by rfl) ⟨1006740, by rfl⟩ : syracuseStep 10738565 = 2013481) B2013481
theorem B2513825 : Blo 1674037 2513825 := bstep (se 2 (by rfl) ⟨942684, by rfl⟩ : syracuseStep 2513825 = 1885369) B1885369
theorem B5364643 : Blo 1674037 5364643 := bstep (se 1 (by rfl) ⟨4023482, by rfl⟩ : syracuseStep 5364643 = 8046965) B8046965
theorem B2513843 : Blo 1674037 2513843 := bstep (se 1 (by rfl) ⟨1885382, by rfl⟩ : syracuseStep 2513843 = 3770765) B3770765
theorem B21756869 : Blo 1674037 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B2513873 : Blo 1674037 2513873 := bstep (se 2 (by rfl) ⟨942702, by rfl⟩ : syracuseStep 2513873 = 1885405) B1885405
theorem B2825185 : Blo 1674037 2825185 := bstep (se 2 (by rfl) ⟨1059444, by rfl⟩ : syracuseStep 2825185 = 2118889) B2118889
theorem B15277027 : Blo 1674037 15277027 := bstep (se 1 (by rfl) ⟨11457770, by rfl⟩ : syracuseStep 15277027 = 22915541) B22915541
theorem B2513891 : Blo 1674037 2513891 := bstep (se 1 (by rfl) ⟨1885418, by rfl⟩ : syracuseStep 2513891 = 3770837) B3770837
theorem B2513921 : Blo 1674037 2513921 := bstep (se 2 (by rfl) ⟨942720, by rfl⟩ : syracuseStep 2513921 = 1885441) B1885441
theorem B2825219 : Blo 1674037 2825219 := bstep (se 1 (by rfl) ⟨2118914, by rfl⟩ : syracuseStep 2825219 = 4237829) B4237829
theorem B2513939 : Blo 1674037 2513939 := bstep (se 1 (by rfl) ⟨1885454, by rfl⟩ : syracuseStep 2513939 = 3770909) B3770909
theorem B3767345 : Blo 1674037 3767345 := bstep (se 2 (by rfl) ⟨1412754, by rfl⟩ : syracuseStep 3767345 = 2825509) B2825509
theorem B2513969 : Blo 1674037 2513969 := bstep (se 2 (by rfl) ⟨942738, by rfl⟩ : syracuseStep 2513969 = 1885477) B1885477
theorem B3767363 : Blo 1674037 3767363 := bstep (se 1 (by rfl) ⟨2825522, by rfl⟩ : syracuseStep 3767363 = 5651045) B5651045
theorem B2513987 : Blo 1674037 2513987 := bstep (se 1 (by rfl) ⟨1885490, by rfl⟩ : syracuseStep 2513987 = 3770981) B3770981
theorem B2514017 : Blo 1674037 2514017 := bstep (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) B1885513
theorem B2514035 : Blo 1674037 2514035 := bstep (se 1 (by rfl) ⟨1885526, by rfl⟩ : syracuseStep 2514035 = 3771053) B3771053
theorem B2825347 : Blo 1674037 2825347 := bstep (se 1 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 2825347 = 4238021) B4238021
theorem B24476813 : Blo 1674037 24476813 := bstep (se 3 (by rfl) ⟨4589402, by rfl⟩ : syracuseStep 24476813 = 9178805) B9178805
theorem B1883299 : Blo 1674037 1883299 := bstep (se 1 (by rfl) ⟨1412474, by rfl⟩ : syracuseStep 1883299 = 2824949) B2824949
theorem B2120899 : Blo 1674037 2120899 := bstep (se 1 (by rfl) ⟨1590674, by rfl⟩ : syracuseStep 2120899 = 3181349) B3181349
theorem B5651693 : Blo 1674037 5651693 := bstep (se 3 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 5651693 = 2119385) B2119385
theorem B2825489 : Blo 1674037 2825489 := bstep (se 2 (by rfl) ⟨1059558, by rfl⟩ : syracuseStep 2825489 = 2119117) B2119117
theorem B5651747 : Blo 1674037 5651747 := bstep (se 1 (by rfl) ⟨4238810, by rfl⟩ : syracuseStep 5651747 = 8477621) B8477621
theorem B2120995 : Blo 1674037 2120995 := bstep (se 1 (by rfl) ⟨1590746, by rfl⟩ : syracuseStep 2120995 = 3181493) B3181493
theorem B1883443 : Blo 1674037 1883443 := bstep (se 1 (by rfl) ⟨1412582, by rfl⟩ : syracuseStep 1883443 = 2825165) B2825165
theorem B3767633 : Blo 1674037 3767633 := bstep (se 2 (by rfl) ⟨1412862, by rfl⟩ : syracuseStep 3767633 = 2825725) B2825725
theorem B3767651 : Blo 1674037 3767651 := bstep (se 1 (by rfl) ⟨2825738, by rfl⟩ : syracuseStep 3767651 = 5651477) B5651477
theorem B2825617 : Blo 1674037 2825617 := bstep (se 2 (by rfl) ⟨1059606, by rfl⟩ : syracuseStep 2825617 = 2119213) B2119213
theorem B2825651 : Blo 1674037 2825651 := bstep (se 1 (by rfl) ⟨2119238, by rfl⟩ : syracuseStep 2825651 = 4238477) B4238477
theorem B1883587 : Blo 1674037 1883587 := bstep (se 1 (by rfl) ⟨1412690, by rfl⟩ : syracuseStep 1883587 = 2825381) B2825381
theorem B6356515 : Blo 1674037 6356515 := bstep (se 1 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 6356515 = 9534773) B9534773
theorem B9543203 : Blo 1674037 9543203 := bstep (se 1 (by rfl) ⟨7157402, by rfl⟩ : syracuseStep 9543203 = 14314805) B14314805
theorem B5652017 : Blo 1674037 5652017 := bstep (se 2 (by rfl) ⟨2119506, by rfl⟩ : syracuseStep 5652017 = 4239013) B4239013
theorem B2825779 : Blo 1674037 2825779 := bstep (se 1 (by rfl) ⟨2119334, by rfl⟩ : syracuseStep 2825779 = 4238669) B4238669
theorem B1883731 : Blo 1674037 1883731 := bstep (se 1 (by rfl) ⟨1412798, by rfl⟩ : syracuseStep 1883731 = 2825597) B2825597
theorem B3767921 : Blo 1674037 3767921 := bstep (se 2 (by rfl) ⟨1412970, by rfl⟩ : syracuseStep 3767921 = 2825941) B2825941
theorem B5365361 : Blo 1674037 5365361 := bstep (se 2 (by rfl) ⟨2012010, by rfl⟩ : syracuseStep 5365361 = 4024021) B4024021
theorem B3767939 : Blo 1674037 3767939 := bstep (se 1 (by rfl) ⟨2825954, by rfl⟩ : syracuseStep 3767939 = 5651909) B5651909
theorem B3178129 : Blo 1674037 3178129 := bstep (se 2 (by rfl) ⟨1191798, by rfl⟩ : syracuseStep 3178129 = 2383597) B2383597
theorem B2825921 : Blo 1674037 2825921 := bstep (se 2 (by rfl) ⟨1059720, by rfl⟩ : syracuseStep 2825921 = 2119441) B2119441
theorem B1883875 : Blo 1674037 1883875 := bstep (se 1 (by rfl) ⟨1412906, by rfl⟩ : syracuseStep 1883875 = 2825813) B2825813
theorem B9060101 : Blo 1674037 9060101 := bstep (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) B1698769
theorem B14311181 : Blo 1674037 14311181 := bstep (se 3 (by rfl) ⟨2683346, by rfl⟩ : syracuseStep 14311181 = 5366693) B5366693
theorem B2826049 : Blo 1674037 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B4767569 : Blo 1674037 4767569 := bstep (se 2 (by rfl) ⟨1787838, by rfl⟩ : syracuseStep 4767569 = 3575677) B3575677
theorem B2826083 : Blo 1674037 2826083 := bstep (se 1 (by rfl) ⟨2119562, by rfl⟩ : syracuseStep 2826083 = 4239125) B4239125
theorem B1884019 : Blo 1674037 1884019 := bstep (se 1 (by rfl) ⟨1413014, by rfl⟩ : syracuseStep 1884019 = 2826029) B2826029
theorem B13590413 : Blo 1674037 13590413 := bstep (se 3 (by rfl) ⟨2548202, by rfl⟩ : syracuseStep 13590413 = 5096405) B5096405
theorem B4833169 : Blo 1674037 4833169 := bstep (se 2 (by rfl) ⟨1812438, by rfl⟩ : syracuseStep 4833169 = 3624877) B3624877
theorem B3768209 : Blo 1674037 3768209 := bstep (se 2 (by rfl) ⟨1413078, by rfl⟩ : syracuseStep 3768209 = 2826157) B2826157
theorem B3768227 : Blo 1674037 3768227 := bstep (se 1 (by rfl) ⟨2826170, by rfl⟩ : syracuseStep 3768227 = 5652341) B5652341
theorem B2383825 : Blo 1674037 2383825 := bstep (se 2 (by rfl) ⟨893934, by rfl⟩ : syracuseStep 2383825 = 1787869) B1787869
theorem B2826211 : Blo 1674037 2826211 := bstep (se 1 (by rfl) ⟨2119658, by rfl⟩ : syracuseStep 2826211 = 4239317) B4239317
theorem B9052145 : Blo 1674037 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B4530161 : Blo 1674037 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B5652503 : Blo 1674037 5652503 := bstep (se 1 (by rfl) ⟨4239377, by rfl⟩ : syracuseStep 5652503 = 8478755) B8478755
theorem B2826265 : Blo 1674037 2826265 := bstep (se 2 (by rfl) ⟨1059849, by rfl⟩ : syracuseStep 2826265 = 2119699) B2119699
theorem B3768371 : Blo 1674037 3768371 := bstep (se 1 (by rfl) ⟨2826278, by rfl⟩ : syracuseStep 3768371 = 5652557) B5652557
theorem B9052235 : Blo 1674037 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B1884235 : Blo 1674037 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B3768407 : Blo 1674037 3768407 := bstep (se 1 (by rfl) ⟨2826305, by rfl⟩ : syracuseStep 3768407 = 5652611) B5652611
theorem B4530269 : Blo 1674037 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B4767923 : Blo 1674037 4767923 := bstep (se 1 (by rfl) ⟨3575942, by rfl⟩ : syracuseStep 4767923 = 7151885) B7151885
theorem B1884343 : Blo 1674037 1884343 := bstep (se 1 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 1884343 = 2826515) B2826515
theorem B12714245 : Blo 1674037 12714245 := bstep (se 4 (by rfl) ⟨1191960, by rfl⟩ : syracuseStep 12714245 = 2383921) B2383921
theorem B3768587 : Blo 1674037 3768587 := bstep (se 1 (by rfl) ⟨2826440, by rfl⟩ : syracuseStep 3768587 = 5652881) B5652881
theorem B3768641 : Blo 1674037 3768641 := bstep (se 2 (by rfl) ⟨1413240, by rfl⟩ : syracuseStep 3768641 = 2826481) B2826481
theorem B10731851 : Blo 1674037 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B12722507 : Blo 1674037 12722507 := bstep (se 1 (by rfl) ⟨9541880, by rfl⟩ : syracuseStep 12722507 = 19083761) B19083761
theorem B1884523 : Blo 1674037 1884523 := bstep (se 1 (by rfl) ⟨1413392, by rfl⟩ : syracuseStep 1884523 = 2826785) B2826785
theorem B1884631 : Blo 1674037 1884631 := bstep (se 1 (by rfl) ⟨1413473, by rfl⟩ : syracuseStep 1884631 = 2826947) B2826947
theorem B3768857 : Blo 1674037 3768857 := bstep (se 2 (by rfl) ⟨1413321, by rfl⟩ : syracuseStep 3768857 = 2826643) B2826643
theorem B5653043 : Blo 1674037 5653043 := bstep (se 1 (by rfl) ⟨4239782, by rfl⟩ : syracuseStep 5653043 = 8479565) B8479565
theorem B4768321 : Blo 1674037 4768321 := bstep (se 2 (by rfl) ⟨1788120, by rfl⟩ : syracuseStep 4768321 = 3576241) B3576241
theorem B2826839 : Blo 1674037 2826839 := bstep (se 1 (by rfl) ⟨2120129, by rfl⟩ : syracuseStep 2826839 = 4240259) B4240259
theorem B3768947 : Blo 1674037 3768947 := bstep (se 1 (by rfl) ⟨2826710, by rfl⟩ : syracuseStep 3768947 = 5653421) B5653421
theorem B1884811 : Blo 1674037 1884811 := bstep (se 1 (by rfl) ⟨1413608, by rfl⟩ : syracuseStep 1884811 = 2827217) B2827217
theorem B3768983 : Blo 1674037 3768983 := bstep (se 1 (by rfl) ⟨2826737, by rfl⟩ : syracuseStep 3768983 = 5653475) B5653475
theorem B2826967 : Blo 1674037 2826967 := bstep (se 1 (by rfl) ⟨2120225, by rfl⟩ : syracuseStep 2826967 = 4240451) B4240451
theorem B6447833 : Blo 1674037 6447833 := bstep (se 2 (by rfl) ⟨2417937, by rfl⟩ : syracuseStep 6447833 = 4835875) B4835875
theorem B68780785 : Blo 1674037 68780785 := bstep (se 2 (by rfl) ⟨25792794, by rfl⟩ : syracuseStep 68780785 = 51585589) B51585589
theorem B1884919 : Blo 1674037 1884919 := bstep (se 1 (by rfl) ⟨1413689, by rfl⟩ : syracuseStep 1884919 = 2827379) B2827379
theorem B5653313 : Blo 1674037 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B3769163 : Blo 1674037 3769163 := bstep (se 1 (by rfl) ⟨2826872, by rfl⟩ : syracuseStep 3769163 = 5653745) B5653745
theorem B3179351 : Blo 1674037 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B3769217 : Blo 1674037 3769217 := bstep (se 2 (by rfl) ⟨1413456, by rfl⟩ : syracuseStep 3769217 = 2826913) B2826913
theorem B1885099 : Blo 1674037 1885099 := bstep (se 1 (by rfl) ⟨1413824, by rfl⟩ : syracuseStep 1885099 = 2827649) B2827649
theorem B1885207 : Blo 1674037 1885207 := bstep (se 1 (by rfl) ⟨1413905, by rfl⟩ : syracuseStep 1885207 = 2827811) B2827811
theorem B12231755 : Blo 1674037 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B2720855 : Blo 1674037 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B3769433 : Blo 1674037 3769433 := bstep (se 2 (by rfl) ⟨1413537, by rfl⟩ : syracuseStep 3769433 = 2827075) B2827075
theorem B9307237 : Blo 1674037 9307237 := bstep (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) B1745107
theorem B3769523 : Blo 1674037 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B36201653 : Blo 1674037 36201653 := bstep (se 5 (by rfl) ⟨1696952, by rfl⟩ : syracuseStep 36201653 = 3393905) B3393905
theorem B1885387 : Blo 1674037 1885387 := bstep (se 1 (by rfl) ⟨1414040, by rfl⟩ : syracuseStep 1885387 = 2828081) B2828081
theorem B3769559 : Blo 1674037 3769559 := bstep (se 1 (by rfl) ⟨2827169, by rfl⟩ : syracuseStep 3769559 = 5654339) B5654339
theorem B7152857 : Blo 1674037 7152857 := bstep (se 2 (by rfl) ⟨2682321, by rfl⟩ : syracuseStep 7152857 = 5364643) B5364643
theorem B5367001 : Blo 1674037 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B2385163 : Blo 1674037 2385163 := bstep (se 1 (by rfl) ⟨1788872, by rfl⟩ : syracuseStep 2385163 = 3577745) B3577745
theorem B1885495 : Blo 1674037 1885495 := bstep (se 1 (by rfl) ⟨1414121, by rfl⟩ : syracuseStep 1885495 = 2828243) B2828243
theorem B2827595 : Blo 1674037 2827595 := bstep (se 1 (by rfl) ⟨2120696, by rfl⟩ : syracuseStep 2827595 = 4241393) B4241393
theorem B5653853 : Blo 1674037 5653853 := bstep (se 3 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 5653853 = 2120195) B2120195
theorem B3179891 : Blo 1674037 3179891 := bstep (se 1 (by rfl) ⟨2384918, by rfl⟩ : syracuseStep 3179891 = 4769837) B4769837
theorem B3769739 : Blo 1674037 3769739 := bstep (se 1 (by rfl) ⟨2827304, by rfl⟩ : syracuseStep 3769739 = 5654609) B5654609
theorem B6358445 : Blo 1674037 6358445 := bstep (se 3 (by rfl) ⟨1192208, by rfl⟩ : syracuseStep 6358445 = 2384417) B2384417
theorem B3769793 : Blo 1674037 3769793 := bstep (se 2 (by rfl) ⟨1413672, by rfl⟩ : syracuseStep 3769793 = 2827345) B2827345
theorem B2827723 : Blo 1674037 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B2827865 : Blo 1674037 2827865 := bstep (se 2 (by rfl) ⟨1060449, by rfl⟩ : syracuseStep 2827865 = 2120899) B2120899
theorem B3770009 : Blo 1674037 3770009 := bstep (se 2 (by rfl) ⟨1413753, by rfl⟩ : syracuseStep 3770009 = 2827507) B2827507
theorem B2827993 : Blo 1674037 2827993 := bstep (se 2 (by rfl) ⟨1060497, by rfl⟩ : syracuseStep 2827993 = 2120995) B2120995
theorem B3770099 : Blo 1674037 3770099 := bstep (se 1 (by rfl) ⟨2827574, by rfl⟩ : syracuseStep 3770099 = 5655149) B5655149
theorem B3770135 : Blo 1674037 3770135 := bstep (se 1 (by rfl) ⟨2827601, by rfl⟩ : syracuseStep 3770135 = 5655203) B5655203
theorem B5367617 : Blo 1674037 5367617 := bstep (se 2 (by rfl) ⟨2012856, by rfl⟩ : syracuseStep 5367617 = 4025713) B4025713
theorem B3180377 : Blo 1674037 3180377 := bstep (se 2 (by rfl) ⟨1192641, by rfl⟩ : syracuseStep 3180377 = 2385283) B2385283
theorem B3819457 : Blo 1674037 3819457 := bstep (se 2 (by rfl) ⟨1432296, by rfl⟩ : syracuseStep 3819457 = 2864593) B2864593
theorem B3770315 : Blo 1674037 3770315 := bstep (se 1 (by rfl) ⟨2827736, by rfl⟩ : syracuseStep 3770315 = 5655473) B5655473
theorem B3016705 : Blo 1674037 3016705 := bstep (se 2 (by rfl) ⟨1131264, by rfl⟩ : syracuseStep 3016705 = 2262529) B2262529
theorem B3770369 : Blo 1674037 3770369 := bstep (se 2 (by rfl) ⟨1413888, by rfl⟩ : syracuseStep 3770369 = 2827777) B2827777
theorem B8480861 : Blo 1674037 8480861 := bstep (se 3 (by rfl) ⟨1590161, by rfl⟩ : syracuseStep 8480861 = 3180323) B3180323
theorem B6359219 : Blo 1674037 6359219 := bstep (se 1 (by rfl) ⟨4769414, by rfl⟩ : syracuseStep 6359219 = 9538829) B9538829
theorem B4237505 : Blo 1674037 4237505 := bstep (se 2 (by rfl) ⟨1589064, by rfl⟩ : syracuseStep 4237505 = 3178129) B3178129
theorem B3770585 : Blo 1674037 3770585 := bstep (se 2 (by rfl) ⟨1413969, by rfl⟩ : syracuseStep 3770585 = 2827939) B2827939
theorem B3770675 : Blo 1674037 3770675 := bstep (se 1 (by rfl) ⟨2828006, by rfl⟩ : syracuseStep 3770675 = 5656013) B5656013
theorem B3393857 : Blo 1674037 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B3770711 : Blo 1674037 3770711 := bstep (se 1 (by rfl) ⟨2828033, by rfl⟩ : syracuseStep 3770711 = 5656067) B5656067
theorem B2263447 : Blo 1674037 2263447 := bstep (se 1 (by rfl) ⟨1697585, by rfl⟩ : syracuseStep 2263447 = 3395171) B3395171
theorem B5654987 : Blo 1674037 5654987 := bstep (se 1 (by rfl) ⟨4241240, by rfl⟩ : syracuseStep 5654987 = 8482481) B8482481
theorem B6040067 : Blo 1674037 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B3770891 : Blo 1674037 3770891 := bstep (se 1 (by rfl) ⟨2828168, by rfl⟩ : syracuseStep 3770891 = 5656337) B5656337
theorem B3770945 : Blo 1674037 3770945 := bstep (se 2 (by rfl) ⟨1414104, by rfl⟩ : syracuseStep 3770945 = 2828209) B2828209
theorem B12716675 : Blo 1674037 12716675 := bstep (se 1 (by rfl) ⟨9537506, by rfl⟩ : syracuseStep 12716675 = 19075013) B19075013
theorem B1788599 : Blo 1674037 1788599 := bstep (se 1 (by rfl) ⟨1341449, by rfl⟩ : syracuseStep 1788599 = 2682899) B2682899
theorem B4238041 : Blo 1674037 4238041 := bstep (se 2 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 4238041 = 3178531) B3178531
theorem B5655257 : Blo 1674037 5655257 := bstep (se 2 (by rfl) ⟨2120721, by rfl⟩ : syracuseStep 5655257 = 4241443) B4241443
theorem B1674039 : Blo 1674037 1674039 := bstep (se 1 (by rfl) ⟨1255529, by rfl⟩ : syracuseStep 1674039 = 2511059) B2511059
theorem B1788727 : Blo 1674037 1788727 := bstep (se 1 (by rfl) ⟨1341545, by rfl⟩ : syracuseStep 1788727 = 2683091) B2683091
theorem B7154497 : Blo 1674037 7154497 := bstep (se 2 (by rfl) ⟨2682936, by rfl⟩ : syracuseStep 7154497 = 5365873) B5365873
theorem B1674059 : Blo 1674037 1674059 := bstep (se 1 (by rfl) ⟨1255544, by rfl⟩ : syracuseStep 1674059 = 2511089) B2511089
theorem B1674071 : Blo 1674037 1674071 := bstep (se 1 (by rfl) ⟨1255553, by rfl⟩ : syracuseStep 1674071 = 2511107) B2511107
theorem B2902873 : Blo 1674037 2902873 := bstep (se 2 (by rfl) ⟨1088577, by rfl⟩ : syracuseStep 2902873 = 2177155) B2177155
theorem B9538397 : Blo 1674037 9538397 := bstep (se 3 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 9538397 = 3576899) B3576899
theorem B1674091 : Blo 1674037 1674091 := bstep (se 1 (by rfl) ⟨1255568, by rfl⟩ : syracuseStep 1674091 = 2511137) B2511137
theorem B1674103 : Blo 1674037 1674103 := bstep (se 1 (by rfl) ⟨1255577, by rfl⟩ : syracuseStep 1674103 = 2511155) B2511155
theorem B1674123 : Blo 1674037 1674123 := bstep (se 1 (by rfl) ⟨1255592, by rfl⟩ : syracuseStep 1674123 = 2511185) B2511185
theorem B1674135 : Blo 1674037 1674135 := bstep (se 1 (by rfl) ⟨1255601, by rfl⟩ : syracuseStep 1674135 = 2511203) B2511203
theorem B1674155 : Blo 1674037 1674155 := bstep (se 1 (by rfl) ⟨1255616, by rfl⟩ : syracuseStep 1674155 = 2511233) B2511233
theorem B16092083 : Blo 1674037 16092083 := bstep (se 1 (by rfl) ⟨12069062, by rfl⟩ : syracuseStep 16092083 = 24138125) B24138125
theorem B10734515 : Blo 1674037 10734515 := bstep (se 1 (by rfl) ⟨8050886, by rfl⟩ : syracuseStep 10734515 = 16101773) B16101773
theorem B1674167 : Blo 1674037 1674167 := bstep (se 1 (by rfl) ⟨1255625, by rfl⟩ : syracuseStep 1674167 = 2511251) B2511251
theorem B1674187 : Blo 1674037 1674187 := bstep (se 1 (by rfl) ⟨1255640, by rfl⟩ : syracuseStep 1674187 = 2511281) B2511281
theorem B3394507 : Blo 1674037 3394507 := bstep (se 1 (by rfl) ⟨2545880, by rfl⟩ : syracuseStep 3394507 = 5091761) B5091761
theorem B1674199 : Blo 1674037 1674199 := bstep (se 1 (by rfl) ⟨1255649, by rfl⟩ : syracuseStep 1674199 = 2511299) B2511299
theorem B1674219 : Blo 1674037 1674219 := bstep (se 1 (by rfl) ⟨1255664, by rfl⟩ : syracuseStep 1674219 = 2511329) B2511329
theorem B1674231 : Blo 1674037 1674231 := bstep (se 1 (by rfl) ⟨1255673, by rfl⟩ : syracuseStep 1674231 = 2511347) B2511347
theorem B1674251 : Blo 1674037 1674251 := bstep (se 1 (by rfl) ⟨1255688, by rfl⟩ : syracuseStep 1674251 = 2511377) B2511377
theorem B1674263 : Blo 1674037 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B4770839 : Blo 1674037 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B1674283 : Blo 1674037 1674283 := bstep (se 1 (by rfl) ⟨1255712, by rfl⟩ : syracuseStep 1674283 = 2511425) B2511425
theorem B1674295 : Blo 1674037 1674295 := bstep (se 1 (by rfl) ⟨1255721, by rfl⟩ : syracuseStep 1674295 = 2511443) B2511443
theorem B1674315 : Blo 1674037 1674315 := bstep (se 1 (by rfl) ⟨1255736, by rfl⟩ : syracuseStep 1674315 = 2511473) B2511473
theorem B1674327 : Blo 1674037 1674327 := bstep (se 1 (by rfl) ⟨1255745, by rfl⟩ : syracuseStep 1674327 = 2511491) B2511491
theorem B7253081 : Blo 1674037 7253081 := bstep (se 2 (by rfl) ⟨2719905, by rfl⟩ : syracuseStep 7253081 = 5439811) B5439811
theorem B1674347 : Blo 1674037 1674347 := bstep (se 1 (by rfl) ⟨1255760, by rfl⟩ : syracuseStep 1674347 = 2511521) B2511521
theorem B1674359 : Blo 1674037 1674359 := bstep (se 1 (by rfl) ⟨1255769, by rfl⟩ : syracuseStep 1674359 = 2511539) B2511539
theorem B1674379 : Blo 1674037 1674379 := bstep (se 1 (by rfl) ⟨1255784, by rfl⟩ : syracuseStep 1674379 = 2511569) B2511569
theorem B1674391 : Blo 1674037 1674391 := bstep (se 1 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 1674391 = 2511587) B2511587
theorem B1674411 : Blo 1674037 1674411 := bstep (se 1 (by rfl) ⟨1255808, by rfl⟩ : syracuseStep 1674411 = 2511617) B2511617
theorem B1674423 : Blo 1674037 1674423 := bstep (se 1 (by rfl) ⟨1255817, by rfl⟩ : syracuseStep 1674423 = 2511635) B2511635
theorem B1674443 : Blo 1674037 1674443 := bstep (se 1 (by rfl) ⟨1255832, by rfl⟩ : syracuseStep 1674443 = 2511665) B2511665
theorem B1674455 : Blo 1674037 1674455 := bstep (se 1 (by rfl) ⟨1255841, by rfl⟩ : syracuseStep 1674455 = 2511683) B2511683
theorem B1674475 : Blo 1674037 1674475 := bstep (se 1 (by rfl) ⟨1255856, by rfl⟩ : syracuseStep 1674475 = 2511713) B2511713
theorem B1674487 : Blo 1674037 1674487 := bstep (se 1 (by rfl) ⟨1255865, by rfl⟩ : syracuseStep 1674487 = 2511731) B2511731
theorem B24153349 : Blo 1674037 24153349 := bstep (se 4 (by rfl) ⟨2264376, by rfl⟩ : syracuseStep 24153349 = 4528753) B4528753
theorem B1674507 : Blo 1674037 1674507 := bstep (se 1 (by rfl) ⟨1255880, by rfl⟩ : syracuseStep 1674507 = 2511761) B2511761
theorem B3181835 : Blo 1674037 3181835 := bstep (se 1 (by rfl) ⟨2386376, by rfl⟩ : syracuseStep 3181835 = 4772753) B4772753
theorem B1674519 : Blo 1674037 1674519 := bstep (se 1 (by rfl) ⟨1255889, by rfl⟩ : syracuseStep 1674519 = 2511779) B2511779
theorem B1674539 : Blo 1674037 1674539 := bstep (se 1 (by rfl) ⟨1255904, by rfl⟩ : syracuseStep 1674539 = 2511809) B2511809
theorem B1674551 : Blo 1674037 1674551 := bstep (se 1 (by rfl) ⟨1255913, by rfl⟩ : syracuseStep 1674551 = 2511827) B2511827
theorem B1674571 : Blo 1674037 1674571 := bstep (se 1 (by rfl) ⟨1255928, by rfl⟩ : syracuseStep 1674571 = 2511857) B2511857
theorem B4025675 : Blo 1674037 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B1674583 : Blo 1674037 1674583 := bstep (se 1 (by rfl) ⟨1255937, by rfl⟩ : syracuseStep 1674583 = 2511875) B2511875
theorem B1674603 : Blo 1674037 1674603 := bstep (se 1 (by rfl) ⟨1255952, by rfl⟩ : syracuseStep 1674603 = 2511905) B2511905
theorem B1789291 : Blo 1674037 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B61156721 : Blo 1674037 61156721 := bstep (se 2 (by rfl) ⟨22933770, by rfl⟩ : syracuseStep 61156721 = 45867541) B45867541
theorem B1674615 : Blo 1674037 1674615 := bstep (se 1 (by rfl) ⟨1255961, by rfl⟩ : syracuseStep 1674615 = 2511923) B2511923
theorem B1674635 : Blo 1674037 1674635 := bstep (se 1 (by rfl) ⟨1255976, by rfl⟩ : syracuseStep 1674635 = 2511953) B2511953
theorem B1674647 : Blo 1674037 1674647 := bstep (se 1 (by rfl) ⟨1255985, by rfl⟩ : syracuseStep 1674647 = 2511971) B2511971
theorem B5655959 : Blo 1674037 5655959 := bstep (se 1 (by rfl) ⟨4241969, by rfl⟩ : syracuseStep 5655959 = 8483939) B8483939
theorem B1674667 : Blo 1674037 1674667 := bstep (se 1 (by rfl) ⟨1256000, by rfl⟩ : syracuseStep 1674667 = 2512001) B2512001
theorem B6794675 : Blo 1674037 6794675 := bstep (se 1 (by rfl) ⟨5096006, by rfl⟩ : syracuseStep 6794675 = 10192013) B10192013
theorem B1674679 : Blo 1674037 1674679 := bstep (se 1 (by rfl) ⟨1256009, by rfl⟩ : syracuseStep 1674679 = 2512019) B2512019
theorem B3395009 : Blo 1674037 3395009 := bstep (se 2 (by rfl) ⟨1273128, by rfl⟩ : syracuseStep 3395009 = 2546257) B2546257
theorem B1674699 : Blo 1674037 1674699 := bstep (se 1 (by rfl) ⟨1256024, by rfl⟩ : syracuseStep 1674699 = 2512049) B2512049
theorem B1674711 : Blo 1674037 1674711 := bstep (se 1 (by rfl) ⟨1256033, by rfl⟩ : syracuseStep 1674711 = 2512067) B2512067
theorem B1674731 : Blo 1674037 1674731 := bstep (se 1 (by rfl) ⟨1256048, by rfl⟩ : syracuseStep 1674731 = 2512097) B2512097
theorem B1674743 : Blo 1674037 1674743 := bstep (se 1 (by rfl) ⟨1256057, by rfl⟩ : syracuseStep 1674743 = 2512115) B2512115
theorem B1674763 : Blo 1674037 1674763 := bstep (se 1 (by rfl) ⟨1256072, by rfl⟩ : syracuseStep 1674763 = 2512145) B2512145
theorem B1674775 : Blo 1674037 1674775 := bstep (se 1 (by rfl) ⟨1256081, by rfl⟩ : syracuseStep 1674775 = 2512163) B2512163
theorem B1674795 : Blo 1674037 1674795 := bstep (se 1 (by rfl) ⟨1256096, by rfl⟩ : syracuseStep 1674795 = 2512193) B2512193
theorem B1674807 : Blo 1674037 1674807 := bstep (se 1 (by rfl) ⟨1256105, by rfl⟩ : syracuseStep 1674807 = 2512211) B2512211
theorem B1674827 : Blo 1674037 1674827 := bstep (se 1 (by rfl) ⟨1256120, by rfl⟩ : syracuseStep 1674827 = 2512241) B2512241
theorem B9539147 : Blo 1674037 9539147 := bstep (se 1 (by rfl) ⟨7154360, by rfl⟩ : syracuseStep 9539147 = 14308721) B14308721
theorem B1674839 : Blo 1674037 1674839 := bstep (se 1 (by rfl) ⟨1256129, by rfl⟩ : syracuseStep 1674839 = 2512259) B2512259
theorem B24161885 : Blo 1674037 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B1674859 : Blo 1674037 1674859 := bstep (se 1 (by rfl) ⟨1256144, by rfl⟩ : syracuseStep 1674859 = 2512289) B2512289
theorem B1789547 : Blo 1674037 1789547 := bstep (se 1 (by rfl) ⟨1342160, by rfl⟩ : syracuseStep 1789547 = 2684321) B2684321
theorem B1674871 : Blo 1674037 1674871 := bstep (se 1 (by rfl) ⟨1256153, by rfl⟩ : syracuseStep 1674871 = 2512307) B2512307
theorem B6360707 : Blo 1674037 6360707 := bstep (se 1 (by rfl) ⟨4770530, by rfl⟩ : syracuseStep 6360707 = 9541061) B9541061
theorem B17198723 : Blo 1674037 17198723 := bstep (se 1 (by rfl) ⟨12899042, by rfl⟩ : syracuseStep 17198723 = 25798085) B25798085
theorem B1674891 : Blo 1674037 1674891 := bstep (se 1 (by rfl) ⟨1256168, by rfl⟩ : syracuseStep 1674891 = 2512337) B2512337
theorem B1674903 : Blo 1674037 1674903 := bstep (se 1 (by rfl) ⟨1256177, by rfl⟩ : syracuseStep 1674903 = 2512355) B2512355
theorem B1674923 : Blo 1674037 1674923 := bstep (se 1 (by rfl) ⟨1256192, by rfl⟩ : syracuseStep 1674923 = 2512385) B2512385
theorem B1674935 : Blo 1674037 1674935 := bstep (se 1 (by rfl) ⟨1256201, by rfl⟩ : syracuseStep 1674935 = 2512403) B2512403
theorem B1674955 : Blo 1674037 1674955 := bstep (se 1 (by rfl) ⟨1256216, by rfl⟩ : syracuseStep 1674955 = 2512433) B2512433
theorem B1674967 : Blo 1674037 1674967 := bstep (se 1 (by rfl) ⟨1256225, by rfl⟩ : syracuseStep 1674967 = 2512451) B2512451
theorem B1674987 : Blo 1674037 1674987 := bstep (se 1 (by rfl) ⟨1256240, by rfl⟩ : syracuseStep 1674987 = 2512481) B2512481
theorem B1674999 : Blo 1674037 1674999 := bstep (se 1 (by rfl) ⟨1256249, by rfl⟩ : syracuseStep 1674999 = 2512499) B2512499
theorem B1675019 : Blo 1674037 1675019 := bstep (se 1 (by rfl) ⟨1256264, by rfl⟩ : syracuseStep 1675019 = 2512529) B2512529
theorem B1675031 : Blo 1674037 1675031 := bstep (se 1 (by rfl) ⟨1256273, by rfl⟩ : syracuseStep 1675031 = 2512547) B2512547
theorem B1675051 : Blo 1674037 1675051 := bstep (se 1 (by rfl) ⟨1256288, by rfl⟩ : syracuseStep 1675051 = 2512577) B2512577
theorem B4239155 : Blo 1674037 4239155 := bstep (se 1 (by rfl) ⟨3179366, by rfl⟩ : syracuseStep 4239155 = 6358733) B6358733
theorem B1675063 : Blo 1674037 1675063 := bstep (se 1 (by rfl) ⟨1256297, by rfl⟩ : syracuseStep 1675063 = 2512595) B2512595
theorem B24162113 : Blo 1674037 24162113 := bstep (se 2 (by rfl) ⟨9060792, by rfl⟩ : syracuseStep 24162113 = 18121585) B18121585
theorem B1675083 : Blo 1674037 1675083 := bstep (se 1 (by rfl) ⟨1256312, by rfl⟩ : syracuseStep 1675083 = 2512625) B2512625
theorem B1675095 : Blo 1674037 1675095 := bstep (se 1 (by rfl) ⟨1256321, by rfl⟩ : syracuseStep 1675095 = 2512643) B2512643
theorem B1675115 : Blo 1674037 1675115 := bstep (se 1 (by rfl) ⟨1256336, by rfl⟩ : syracuseStep 1675115 = 2512673) B2512673
theorem B1675127 : Blo 1674037 1675127 := bstep (se 1 (by rfl) ⟨1256345, by rfl⟩ : syracuseStep 1675127 = 2512691) B2512691
theorem B1675147 : Blo 1674037 1675147 := bstep (se 1 (by rfl) ⟨1256360, by rfl⟩ : syracuseStep 1675147 = 2512721) B2512721
theorem B1675159 : Blo 1674037 1675159 := bstep (se 1 (by rfl) ⟨1256369, by rfl⟩ : syracuseStep 1675159 = 2512739) B2512739
theorem B1675179 : Blo 1674037 1675179 := bstep (se 1 (by rfl) ⟨1256384, by rfl⟩ : syracuseStep 1675179 = 2512769) B2512769
theorem B5656499 : Blo 1674037 5656499 := bstep (se 1 (by rfl) ⟨4242374, by rfl⟩ : syracuseStep 5656499 = 8484749) B8484749
theorem B1675191 : Blo 1674037 1675191 := bstep (se 1 (by rfl) ⟨1256393, by rfl⟩ : syracuseStep 1675191 = 2512787) B2512787
theorem B1675211 : Blo 1674037 1675211 := bstep (se 1 (by rfl) ⟨1256408, by rfl⟩ : syracuseStep 1675211 = 2512817) B2512817
theorem B1675223 : Blo 1674037 1675223 := bstep (se 1 (by rfl) ⟨1256417, by rfl⟩ : syracuseStep 1675223 = 2512835) B2512835
theorem B20369369 : Blo 1674037 20369369 := bstep (se 2 (by rfl) ⟨7638513, by rfl⟩ : syracuseStep 20369369 = 15277027) B15277027
theorem B1675243 : Blo 1674037 1675243 := bstep (se 1 (by rfl) ⟨1256432, by rfl⟩ : syracuseStep 1675243 = 2512865) B2512865
theorem B1675255 : Blo 1674037 1675255 := bstep (se 1 (by rfl) ⟨1256441, by rfl⟩ : syracuseStep 1675255 = 2512883) B2512883
theorem B1675275 : Blo 1674037 1675275 := bstep (se 1 (by rfl) ⟨1256456, by rfl⟩ : syracuseStep 1675275 = 2512913) B2512913
theorem B15274001 : Blo 1674037 15274001 := bstep (se 2 (by rfl) ⟨5727750, by rfl⟩ : syracuseStep 15274001 = 11455501) B11455501
theorem B10727441 : Blo 1674037 10727441 := bstep (se 2 (by rfl) ⟨4022790, by rfl⟩ : syracuseStep 10727441 = 8045581) B8045581
theorem B1675287 : Blo 1674037 1675287 := bstep (se 1 (by rfl) ⟨1256465, by rfl⟩ : syracuseStep 1675287 = 2512931) B2512931
theorem B14315555 : Blo 1674037 14315555 := bstep (se 1 (by rfl) ⟨10736666, by rfl⟩ : syracuseStep 14315555 = 21473333) B21473333
theorem B1675307 : Blo 1674037 1675307 := bstep (se 1 (by rfl) ⟨1256480, by rfl⟩ : syracuseStep 1675307 = 2512961) B2512961
theorem B1675319 : Blo 1674037 1675319 := bstep (se 1 (by rfl) ⟨1256489, by rfl⟩ : syracuseStep 1675319 = 2512979) B2512979
theorem B1675339 : Blo 1674037 1675339 := bstep (se 1 (by rfl) ⟨1256504, by rfl⟩ : syracuseStep 1675339 = 2513009) B2513009
theorem B6361163 : Blo 1674037 6361163 := bstep (se 1 (by rfl) ⟨4770872, by rfl⟩ : syracuseStep 6361163 = 9541745) B9541745
theorem B1675351 : Blo 1674037 1675351 := bstep (se 1 (by rfl) ⟨1256513, by rfl⟩ : syracuseStep 1675351 = 2513027) B2513027
theorem B4239449 : Blo 1674037 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B1675371 : Blo 1674037 1675371 := bstep (se 1 (by rfl) ⟨1256528, by rfl⟩ : syracuseStep 1675371 = 2513057) B2513057
theorem B1675383 : Blo 1674037 1675383 := bstep (se 1 (by rfl) ⟨1256537, by rfl⟩ : syracuseStep 1675383 = 2513075) B2513075
theorem B1675403 : Blo 1674037 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B1675415 : Blo 1674037 1675415 := bstep (se 1 (by rfl) ⟨1256561, by rfl⟩ : syracuseStep 1675415 = 2513123) B2513123
theorem B8482967 : Blo 1674037 8482967 := bstep (se 1 (by rfl) ⟨6362225, by rfl⟩ : syracuseStep 8482967 = 12724451) B12724451
theorem B1675435 : Blo 1674037 1675435 := bstep (se 1 (by rfl) ⟨1256576, by rfl⟩ : syracuseStep 1675435 = 2513153) B2513153
theorem B1675447 : Blo 1674037 1675447 := bstep (se 1 (by rfl) ⟨1256585, by rfl⟩ : syracuseStep 1675447 = 2513171) B2513171
theorem B1675467 : Blo 1674037 1675467 := bstep (se 1 (by rfl) ⟨1256600, by rfl⟩ : syracuseStep 1675467 = 2513201) B2513201
theorem B1675479 : Blo 1674037 1675479 := bstep (se 1 (by rfl) ⟨1256609, by rfl⟩ : syracuseStep 1675479 = 2513219) B2513219
theorem B2511065 : Blo 1674037 2511065 := bstep (se 2 (by rfl) ⟨941649, by rfl⟩ : syracuseStep 2511065 = 1883299) B1883299
theorem B1675499 : Blo 1674037 1675499 := bstep (se 1 (by rfl) ⟨1256624, by rfl⟩ : syracuseStep 1675499 = 2513249) B2513249
theorem B1675511 : Blo 1674037 1675511 := bstep (se 1 (by rfl) ⟨1256633, by rfl⟩ : syracuseStep 1675511 = 2513267) B2513267
theorem B1675531 : Blo 1674037 1675531 := bstep (se 1 (by rfl) ⟨1256648, by rfl⟩ : syracuseStep 1675531 = 2513297) B2513297
theorem B7155985 : Blo 1674037 7155985 := bstep (se 2 (by rfl) ⟨2683494, by rfl⟩ : syracuseStep 7155985 = 5366989) B5366989
theorem B6361361 : Blo 1674037 6361361 := bstep (se 2 (by rfl) ⟨2385510, by rfl⟩ : syracuseStep 6361361 = 4771021) B4771021
theorem B1675543 : Blo 1674037 1675543 := bstep (se 1 (by rfl) ⟨1256657, by rfl⟩ : syracuseStep 1675543 = 2513315) B2513315
theorem B1675563 : Blo 1674037 1675563 := bstep (se 1 (by rfl) ⟨1256672, by rfl⟩ : syracuseStep 1675563 = 2513345) B2513345
theorem B1675575 : Blo 1674037 1675575 := bstep (se 1 (by rfl) ⟨1256681, by rfl⟩ : syracuseStep 1675575 = 2513363) B2513363
theorem B2511179 : Blo 1674037 2511179 := bstep (se 1 (by rfl) ⟨1883384, by rfl⟩ : syracuseStep 2511179 = 3766769) B3766769
theorem B1675595 : Blo 1674037 1675595 := bstep (se 1 (by rfl) ⟨1256696, by rfl⟩ : syracuseStep 1675595 = 2513393) B2513393
theorem B4772171 : Blo 1674037 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B2511191 : Blo 1674037 2511191 := bstep (se 1 (by rfl) ⟨1883393, by rfl⟩ : syracuseStep 2511191 = 3766787) B3766787
theorem B1675607 : Blo 1674037 1675607 := bstep (se 1 (by rfl) ⟨1256705, by rfl⟩ : syracuseStep 1675607 = 2513411) B2513411
theorem B1675627 : Blo 1674037 1675627 := bstep (se 1 (by rfl) ⟨1256720, by rfl⟩ : syracuseStep 1675627 = 2513441) B2513441
theorem B1675639 : Blo 1674037 1675639 := bstep (se 1 (by rfl) ⟨1256729, by rfl⟩ : syracuseStep 1675639 = 2513459) B2513459
theorem B7639427 : Blo 1674037 7639427 := bstep (se 1 (by rfl) ⟨5729570, by rfl⟩ : syracuseStep 7639427 = 11459141) B11459141
theorem B1675659 : Blo 1674037 1675659 := bstep (se 1 (by rfl) ⟨1256744, by rfl⟩ : syracuseStep 1675659 = 2513489) B2513489
theorem B1675671 : Blo 1674037 1675671 := bstep (se 1 (by rfl) ⟨1256753, by rfl⟩ : syracuseStep 1675671 = 2513507) B2513507
theorem B2511257 : Blo 1674037 2511257 := bstep (se 2 (by rfl) ⟨941721, by rfl⟩ : syracuseStep 2511257 = 1883443) B1883443
theorem B1675691 : Blo 1674037 1675691 := bstep (se 1 (by rfl) ⟨1256768, by rfl⟩ : syracuseStep 1675691 = 2513537) B2513537
theorem B1675703 : Blo 1674037 1675703 := bstep (se 1 (by rfl) ⟨1256777, by rfl⟩ : syracuseStep 1675703 = 2513555) B2513555
theorem B1675723 : Blo 1674037 1675723 := bstep (se 1 (by rfl) ⟨1256792, by rfl⟩ : syracuseStep 1675723 = 2513585) B2513585
theorem B1675735 : Blo 1674037 1675735 := bstep (se 1 (by rfl) ⟨1256801, by rfl⟩ : syracuseStep 1675735 = 2513603) B2513603
theorem B1675755 : Blo 1674037 1675755 := bstep (se 1 (by rfl) ⟨1256816, by rfl⟩ : syracuseStep 1675755 = 2513633) B2513633
theorem B1675767 : Blo 1674037 1675767 := bstep (se 1 (by rfl) ⟨1256825, by rfl⟩ : syracuseStep 1675767 = 2513651) B2513651
theorem B2511371 : Blo 1674037 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B1675787 : Blo 1674037 1675787 := bstep (se 1 (by rfl) ⟨1256840, by rfl⟩ : syracuseStep 1675787 = 2513681) B2513681
theorem B2511383 : Blo 1674037 2511383 := bstep (se 1 (by rfl) ⟨1883537, by rfl⟩ : syracuseStep 2511383 = 3767075) B3767075
theorem B1675799 : Blo 1674037 1675799 := bstep (se 1 (by rfl) ⟨1256849, by rfl⟩ : syracuseStep 1675799 = 2513699) B2513699
theorem B1675819 : Blo 1674037 1675819 := bstep (se 1 (by rfl) ⟨1256864, by rfl⟩ : syracuseStep 1675819 = 2513729) B2513729
theorem B1675831 : Blo 1674037 1675831 := bstep (se 1 (by rfl) ⟨1256873, by rfl⟩ : syracuseStep 1675831 = 2513747) B2513747
theorem B3576395 : Blo 1674037 3576395 := bstep (se 1 (by rfl) ⟨2682296, by rfl⟩ : syracuseStep 3576395 = 5364593) B5364593
theorem B1675851 : Blo 1674037 1675851 := bstep (se 1 (by rfl) ⟨1256888, by rfl⟩ : syracuseStep 1675851 = 2513777) B2513777
theorem B1675863 : Blo 1674037 1675863 := bstep (se 1 (by rfl) ⟨1256897, by rfl⟩ : syracuseStep 1675863 = 2513795) B2513795
theorem B2511449 : Blo 1674037 2511449 := bstep (se 2 (by rfl) ⟨941793, by rfl⟩ : syracuseStep 2511449 = 1883587) B1883587
theorem B1675883 : Blo 1674037 1675883 := bstep (se 1 (by rfl) ⟨1256912, by rfl⟩ : syracuseStep 1675883 = 2513825) B2513825
theorem B1675895 : Blo 1674037 1675895 := bstep (se 1 (by rfl) ⟨1256921, by rfl⟩ : syracuseStep 1675895 = 2513843) B2513843
theorem B3019393 : Blo 1674037 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B14504579 : Blo 1674037 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B1675915 : Blo 1674037 1675915 := bstep (se 1 (by rfl) ⟨1256936, by rfl⟩ : syracuseStep 1675915 = 2513873) B2513873
theorem B1675927 : Blo 1674037 1675927 := bstep (se 1 (by rfl) ⟨1256945, by rfl⟩ : syracuseStep 1675927 = 2513891) B2513891
theorem B1675947 : Blo 1674037 1675947 := bstep (se 1 (by rfl) ⟨1256960, by rfl⟩ : syracuseStep 1675947 = 2513921) B2513921
theorem B1675959 : Blo 1674037 1675959 := bstep (se 1 (by rfl) ⟨1256969, by rfl⟩ : syracuseStep 1675959 = 2513939) B2513939
theorem B2511563 : Blo 1674037 2511563 := bstep (se 1 (by rfl) ⟨1883672, by rfl⟩ : syracuseStep 2511563 = 3767345) B3767345
theorem B1675979 : Blo 1674037 1675979 := bstep (se 1 (by rfl) ⟨1256984, by rfl⟩ : syracuseStep 1675979 = 2513969) B2513969
theorem B2511575 : Blo 1674037 2511575 := bstep (se 1 (by rfl) ⟨1883681, by rfl⟩ : syracuseStep 2511575 = 3767363) B3767363
theorem B1675991 : Blo 1674037 1675991 := bstep (se 1 (by rfl) ⟨1256993, by rfl⟩ : syracuseStep 1675991 = 2513987) B2513987
theorem B8475353 : Blo 1674037 8475353 := bstep (se 2 (by rfl) ⟨3178257, by rfl⟩ : syracuseStep 8475353 = 6356515) B6356515
theorem B1676011 : Blo 1674037 1676011 := bstep (se 1 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 1676011 = 2514017) B2514017
theorem B27177713 : Blo 1674037 27177713 := bstep (se 2 (by rfl) ⟨10191642, by rfl⟩ : syracuseStep 27177713 = 20383285) B20383285
theorem B1676023 : Blo 1674037 1676023 := bstep (se 1 (by rfl) ⟨1257017, by rfl⟩ : syracuseStep 1676023 = 2514035) B2514035
theorem B25776901 : Blo 1674037 25776901 := bstep (se 4 (by rfl) ⟨2416584, by rfl⟩ : syracuseStep 25776901 = 4833169) B4833169
theorem B2011915 : Blo 1674037 2011915 := bstep (se 1 (by rfl) ⟨1508936, by rfl⟩ : syracuseStep 2011915 = 3017873) B3017873
theorem B2511641 : Blo 1674037 2511641 := bstep (se 2 (by rfl) ⟨941865, by rfl⟩ : syracuseStep 2511641 = 1883731) B1883731
theorem B28627829 : Blo 1674037 28627829 := bstep (se 5 (by rfl) ⟨1341929, by rfl⟩ : syracuseStep 28627829 = 2683859) B2683859
theorem B2511755 : Blo 1674037 2511755 := bstep (se 1 (by rfl) ⟨1883816, by rfl⟩ : syracuseStep 2511755 = 3767633) B3767633
theorem B2511767 : Blo 1674037 2511767 := bstep (se 1 (by rfl) ⟨1883825, by rfl⟩ : syracuseStep 2511767 = 3767651) B3767651
theorem B5092247 : Blo 1674037 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B2012107 : Blo 1674037 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B2511833 : Blo 1674037 2511833 := bstep (se 2 (by rfl) ⟨941937, by rfl⟩ : syracuseStep 2511833 = 1883875) B1883875
theorem B6362135 : Blo 1674037 6362135 := bstep (se 1 (by rfl) ⟨4771601, by rfl⟩ : syracuseStep 6362135 = 9543203) B9543203
theorem B2511947 : Blo 1674037 2511947 := bstep (se 1 (by rfl) ⟨1883960, by rfl⟩ : syracuseStep 2511947 = 3767921) B3767921
theorem B3576907 : Blo 1674037 3576907 := bstep (se 1 (by rfl) ⟨2682680, by rfl⟩ : syracuseStep 3576907 = 5365361) B5365361
theorem B2511959 : Blo 1674037 2511959 := bstep (se 1 (by rfl) ⟨1883969, by rfl⟩ : syracuseStep 2511959 = 3767939) B3767939
theorem B2512025 : Blo 1674037 2512025 := bstep (se 2 (by rfl) ⟨942009, by rfl⟩ : syracuseStep 2512025 = 1884019) B1884019
theorem B9540787 : Blo 1674037 9540787 := bstep (se 1 (by rfl) ⟨7155590, by rfl⟩ : syracuseStep 9540787 = 14311181) B14311181
theorem B178828469 : Blo 1674037 178828469 := bstep (se 5 (by rfl) ⟨8382584, by rfl⟩ : syracuseStep 178828469 = 16765169) B16765169
theorem B6362333 : Blo 1674037 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B2512139 : Blo 1674037 2512139 := bstep (se 1 (by rfl) ⟨1884104, by rfl⟩ : syracuseStep 2512139 = 3768209) B3768209
theorem B2512151 : Blo 1674037 2512151 := bstep (se 1 (by rfl) ⟨1884113, by rfl⟩ : syracuseStep 2512151 = 3768227) B3768227
theorem B6034763 : Blo 1674037 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B3020107 : Blo 1674037 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B2512217 : Blo 1674037 2512217 := bstep (se 2 (by rfl) ⟨942081, by rfl⟩ : syracuseStep 2512217 = 1884163) B1884163
theorem B26506595 : Blo 1674037 26506595 := bstep (se 1 (by rfl) ⟨19879946, by rfl⟩ : syracuseStep 26506595 = 39759893) B39759893
theorem B2119051 : Blo 1674037 2119051 := bstep (se 1 (by rfl) ⟨1589288, by rfl⟩ : syracuseStep 2119051 = 3178577) B3178577
theorem B3626419 : Blo 1674037 3626419 := bstep (se 1 (by rfl) ⟨2719814, by rfl⟩ : syracuseStep 3626419 = 5439629) B5439629
theorem B2512331 : Blo 1674037 2512331 := bstep (se 1 (by rfl) ⟨1884248, by rfl⟩ : syracuseStep 2512331 = 3768497) B3768497
theorem B2512343 : Blo 1674037 2512343 := bstep (se 1 (by rfl) ⟨1884257, by rfl⟩ : syracuseStep 2512343 = 3768515) B3768515
theorem B2512409 : Blo 1674037 2512409 := bstep (se 2 (by rfl) ⟨942153, by rfl⟩ : syracuseStep 2512409 = 1884307) B1884307
theorem B2512523 : Blo 1674037 2512523 := bstep (se 1 (by rfl) ⟨1884392, by rfl⟩ : syracuseStep 2512523 = 3768785) B3768785
theorem B6035095 : Blo 1674037 6035095 := bstep (se 1 (by rfl) ⟨4526321, by rfl⟩ : syracuseStep 6035095 = 9052643) B9052643
theorem B2512535 : Blo 1674037 2512535 := bstep (se 1 (by rfl) ⟨1884401, by rfl⟩ : syracuseStep 2512535 = 3768803) B3768803
theorem B4241099 : Blo 1674037 4241099 := bstep (se 1 (by rfl) ⟨3180824, by rfl⟩ : syracuseStep 4241099 = 6361649) B6361649
theorem B2512601 : Blo 1674037 2512601 := bstep (se 2 (by rfl) ⟨942225, by rfl⟩ : syracuseStep 2512601 = 1884451) B1884451
theorem B2864921 : Blo 1674037 2864921 := bstep (se 2 (by rfl) ⟨1074345, by rfl⟩ : syracuseStep 2864921 = 2148691) B2148691
theorem B3577625 : Blo 1674037 3577625 := bstep (se 2 (by rfl) ⟨1341609, by rfl⟩ : syracuseStep 3577625 = 2683219) B2683219
theorem B2512715 : Blo 1674037 2512715 := bstep (se 1 (by rfl) ⟨1884536, by rfl⟩ : syracuseStep 2512715 = 3769073) B3769073
theorem B2512727 : Blo 1674037 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B40728419 : Blo 1674037 40728419 := bstep (se 1 (by rfl) ⟨30546314, by rfl⟩ : syracuseStep 40728419 = 61092629) B61092629
theorem B2512793 : Blo 1674037 2512793 := bstep (se 2 (by rfl) ⟨942297, by rfl⟩ : syracuseStep 2512793 = 1884595) B1884595
theorem B12720077 : Blo 1674037 12720077 := bstep (se 3 (by rfl) ⟨2385014, by rfl⟩ : syracuseStep 12720077 = 4770029) B4770029
theorem B29013977 : Blo 1674037 29013977 := bstep (se 2 (by rfl) ⟨10880241, by rfl⟩ : syracuseStep 29013977 = 21760483) B21760483
theorem B5650397 : Blo 1674037 5650397 := bstep (se 3 (by rfl) ⟨1059449, by rfl⟩ : syracuseStep 5650397 = 2118899) B2118899
theorem B2512907 : Blo 1674037 2512907 := bstep (se 1 (by rfl) ⟨1884680, by rfl⟩ : syracuseStep 2512907 = 3769361) B3769361
theorem B2512919 : Blo 1674037 2512919 := bstep (se 1 (by rfl) ⟨1884689, by rfl⟩ : syracuseStep 2512919 = 3769379) B3769379
theorem B15276077 : Blo 1674037 15276077 := bstep (se 3 (by rfl) ⟨2864264, by rfl⟩ : syracuseStep 15276077 = 5728529) B5728529
theorem B45824075 : Blo 1674037 45824075 := bstep (se 1 (by rfl) ⟨34368056, by rfl⟩ : syracuseStep 45824075 = 68736113) B68736113
theorem B2512985 : Blo 1674037 2512985 := bstep (se 2 (by rfl) ⟨942369, by rfl⟩ : syracuseStep 2512985 = 1884739) B1884739
theorem B3578035 : Blo 1674037 3578035 := bstep (se 1 (by rfl) ⟨2683526, by rfl⟩ : syracuseStep 3578035 = 5367053) B5367053
theorem B2513099 : Blo 1674037 2513099 := bstep (se 1 (by rfl) ⟨1884824, by rfl⟩ : syracuseStep 2513099 = 3769649) B3769649
theorem B2513111 : Blo 1674037 2513111 := bstep (se 1 (by rfl) ⟨1884833, by rfl⟩ : syracuseStep 2513111 = 3769667) B3769667
theorem B2513177 : Blo 1674037 2513177 := bstep (se 2 (by rfl) ⟨942441, by rfl⟩ : syracuseStep 2513177 = 1884883) B1884883
theorem B8476973 : Blo 1674037 8476973 := bstep (se 3 (by rfl) ⟨1589432, by rfl⟩ : syracuseStep 8476973 = 3178865) B3178865
theorem B2120023 : Blo 1674037 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B3766643 : Blo 1674037 3766643 := bstep (se 1 (by rfl) ⟨2824982, by rfl⟩ : syracuseStep 3766643 = 5649965) B5649965
theorem B2513291 : Blo 1674037 2513291 := bstep (se 1 (by rfl) ⟨1884968, by rfl⟩ : syracuseStep 2513291 = 3769937) B3769937
theorem B3766679 : Blo 1674037 3766679 := bstep (se 1 (by rfl) ⟨2825009, by rfl⟩ : syracuseStep 3766679 = 5650019) B5650019
theorem B5364119 : Blo 1674037 5364119 := bstep (se 1 (by rfl) ⟨4023089, by rfl⟩ : syracuseStep 5364119 = 8046179) B8046179
theorem B14309783 : Blo 1674037 14309783 := bstep (se 1 (by rfl) ⟨10732337, by rfl⟩ : syracuseStep 14309783 = 21464675) B21464675
theorem B2513303 : Blo 1674037 2513303 := bstep (se 1 (by rfl) ⟨1884977, by rfl⟩ : syracuseStep 2513303 = 3769955) B3769955
theorem B12720563 : Blo 1674037 12720563 := bstep (se 1 (by rfl) ⟨9540422, by rfl⟩ : syracuseStep 12720563 = 19080845) B19080845
theorem B6035915 : Blo 1674037 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B2513369 : Blo 1674037 2513369 := bstep (se 2 (by rfl) ⟨942513, by rfl⟩ : syracuseStep 2513369 = 1885027) B1885027
theorem B3766859 : Blo 1674037 3766859 := bstep (se 1 (by rfl) ⟨2825144, by rfl⟩ : syracuseStep 3766859 = 5650289) B5650289
theorem B2513483 : Blo 1674037 2513483 := bstep (se 1 (by rfl) ⟨1885112, by rfl⟩ : syracuseStep 2513483 = 3770225) B3770225
theorem B9058891 : Blo 1674037 9058891 := bstep (se 1 (by rfl) ⟨6794168, by rfl⟩ : syracuseStep 9058891 = 13588337) B13588337
theorem B2513495 : Blo 1674037 2513495 := bstep (se 1 (by rfl) ⟨1885121, by rfl⟩ : syracuseStep 2513495 = 3770243) B3770243
theorem B9542245 : Blo 1674037 9542245 := bstep (se 4 (by rfl) ⟨894585, by rfl⟩ : syracuseStep 9542245 = 1789171) B1789171
theorem B3766913 : Blo 1674037 3766913 := bstep (se 2 (by rfl) ⟨1412592, by rfl⟩ : syracuseStep 3766913 = 2825185) B2825185
theorem B10738307 : Blo 1674037 10738307 := bstep (se 1 (by rfl) ⟨8053730, by rfl⟩ : syracuseStep 10738307 = 16107461) B16107461
theorem B4242071 : Blo 1674037 4242071 := bstep (se 1 (by rfl) ⟨3181553, by rfl⟩ : syracuseStep 4242071 = 6363107) B6363107
theorem B2513561 : Blo 1674037 2513561 := bstep (se 2 (by rfl) ⟨942585, by rfl⟩ : syracuseStep 2513561 = 1885171) B1885171
theorem B5364427 : Blo 1674037 5364427 := bstep (se 1 (by rfl) ⟨4023320, by rfl⟩ : syracuseStep 5364427 = 8046641) B8046641
theorem B2513675 : Blo 1674037 2513675 := bstep (se 1 (by rfl) ⟨1885256, by rfl⟩ : syracuseStep 2513675 = 3770513) B3770513
theorem B2513687 : Blo 1674037 2513687 := bstep (se 1 (by rfl) ⟨1885265, by rfl⟩ : syracuseStep 2513687 = 3770531) B3770531
theorem B8051501 : Blo 1674037 8051501 := bstep (se 3 (by rfl) ⟨1509656, by rfl⟩ : syracuseStep 8051501 = 3019313) B3019313
theorem B3767129 : Blo 1674037 3767129 := bstep (se 2 (by rfl) ⟨1412673, by rfl⟩ : syracuseStep 3767129 = 2825347) B2825347
theorem B2513753 : Blo 1674037 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B20380517 : Blo 1674037 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B30563189 : Blo 1674037 30563189 := bstep (se 5 (by rfl) ⟨1432649, by rfl⟩ : syracuseStep 30563189 = 2865299) B2865299
theorem B2825111 : Blo 1674037 2825111 := bstep (se 1 (by rfl) ⟨2118833, by rfl⟩ : syracuseStep 2825111 = 4237667) B4237667
theorem B3767219 : Blo 1674037 3767219 := bstep (se 1 (by rfl) ⟨2825414, by rfl⟩ : syracuseStep 3767219 = 5650829) B5650829
theorem B2513867 : Blo 1674037 2513867 := bstep (se 1 (by rfl) ⟨1885400, by rfl⟩ : syracuseStep 2513867 = 3770801) B3770801
theorem B3767255 : Blo 1674037 3767255 := bstep (se 1 (by rfl) ⟨2825441, by rfl⟩ : syracuseStep 3767255 = 5650883) B5650883
theorem B2513879 : Blo 1674037 2513879 := bstep (se 1 (by rfl) ⟨1885409, by rfl⟩ : syracuseStep 2513879 = 3770819) B3770819
theorem B2825239 : Blo 1674037 2825239 := bstep (se 1 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 2825239 = 4237859) B4237859
theorem B2513945 : Blo 1674037 2513945 := bstep (se 2 (by rfl) ⟨942729, by rfl⟩ : syracuseStep 2513945 = 1885459) B1885459
theorem B5651531 : Blo 1674037 5651531 := bstep (se 1 (by rfl) ⟨4238648, by rfl⟩ : syracuseStep 5651531 = 8477297) B8477297
theorem B3767435 : Blo 1674037 3767435 := bstep (se 1 (by rfl) ⟨2825576, by rfl⟩ : syracuseStep 3767435 = 5651153) B5651153
theorem B2120843 : Blo 1674037 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B3767489 : Blo 1674037 3767489 := bstep (se 2 (by rfl) ⟨1412808, by rfl⟩ : syracuseStep 3767489 = 2825617) B2825617
theorem B1883371 : Blo 1674037 1883371 := bstep (se 1 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 1883371 = 2825057) B2825057
theorem B7159043 : Blo 1674037 7159043 := bstep (se 1 (by rfl) ⟨5369282, by rfl⟩ : syracuseStep 7159043 = 10738565) B10738565
theorem B6036781 : Blo 1674037 6036781 := bstep (se 3 (by rfl) ⟨1131896, by rfl⟩ : syracuseStep 6036781 = 2263793) B2263793
theorem B1883479 : Blo 1674037 1883479 := bstep (se 1 (by rfl) ⟨1412609, by rfl⟩ : syracuseStep 1883479 = 2825219) B2825219
theorem B3579223 : Blo 1674037 3579223 := bstep (se 1 (by rfl) ⟨2684417, by rfl⟩ : syracuseStep 3579223 = 5368835) B5368835
theorem B5651801 : Blo 1674037 5651801 := bstep (se 2 (by rfl) ⟨2119425, by rfl⟩ : syracuseStep 5651801 = 4238851) B4238851
theorem B3579265 : Blo 1674037 3579265 := bstep (se 2 (by rfl) ⟨1342224, by rfl⟩ : syracuseStep 3579265 = 2684449) B2684449
theorem B3767705 : Blo 1674037 3767705 := bstep (se 2 (by rfl) ⟨1412889, by rfl⟩ : syracuseStep 3767705 = 2825779) B2825779
theorem B16317875 : Blo 1674037 16317875 := bstep (se 1 (by rfl) ⟨12238406, by rfl⟩ : syracuseStep 16317875 = 24476813) B24476813
theorem B3767795 : Blo 1674037 3767795 := bstep (se 1 (by rfl) ⟨2825846, by rfl⟩ : syracuseStep 3767795 = 5651693) B5651693
theorem B1883659 : Blo 1674037 1883659 := bstep (se 1 (by rfl) ⟨1412744, by rfl⟩ : syracuseStep 1883659 = 2825489) B2825489
theorem B3767831 : Blo 1674037 3767831 := bstep (se 1 (by rfl) ⟨2825873, by rfl⟩ : syracuseStep 3767831 = 5651747) B5651747
theorem B9051713 : Blo 1674037 9051713 := bstep (se 2 (by rfl) ⟨3394392, by rfl⟩ : syracuseStep 9051713 = 6788785) B6788785
theorem B1883767 : Blo 1674037 1883767 := bstep (se 1 (by rfl) ⟨1412825, by rfl⟩ : syracuseStep 1883767 = 2825651) B2825651
theorem B2825867 : Blo 1674037 2825867 := bstep (se 1 (by rfl) ⟨2119400, by rfl⟩ : syracuseStep 2825867 = 4238801) B4238801
theorem B3768011 : Blo 1674037 3768011 := bstep (se 1 (by rfl) ⟨2826008, by rfl⟩ : syracuseStep 3768011 = 5652017) B5652017
theorem B3768065 : Blo 1674037 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B2825995 : Blo 1674037 2825995 := bstep (se 1 (by rfl) ⟨2119496, by rfl⟩ : syracuseStep 2825995 = 4238993) B4238993
theorem B1883947 : Blo 1674037 1883947 := bstep (se 1 (by rfl) ⟨1412960, by rfl⟩ : syracuseStep 1883947 = 2825921) B2825921
theorem B2383705 : Blo 1674037 2383705 := bstep (se 2 (by rfl) ⟨893889, by rfl⟩ : syracuseStep 2383705 = 1787779) B1787779
theorem B10182493 : Blo 1674037 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B12722021 : Blo 1674037 12722021 := bstep (se 4 (by rfl) ⟨1192689, by rfl⟩ : syracuseStep 12722021 = 2385379) B2385379
theorem B3178379 : Blo 1674037 3178379 := bstep (se 1 (by rfl) ⟨2383784, by rfl⟩ : syracuseStep 3178379 = 4767569) B4767569
theorem B1884055 : Blo 1674037 1884055 := bstep (se 1 (by rfl) ⟨1413041, by rfl⟩ : syracuseStep 1884055 = 2826083) B2826083
theorem B2826137 : Blo 1674037 2826137 := bstep (se 2 (by rfl) ⟨1059801, by rfl⟩ : syracuseStep 2826137 = 2119603) B2119603
theorem B9060275 : Blo 1674037 9060275 := bstep (se 1 (by rfl) ⟨6795206, by rfl⟩ : syracuseStep 9060275 = 13590413) B13590413
theorem B3178433 : Blo 1674037 3178433 := bstep (se 2 (by rfl) ⟨1191912, by rfl⟩ : syracuseStep 3178433 = 2383825) B2383825
theorem B3923905 : Blo 1674037 3923905 := bstep (se 2 (by rfl) ⟨1471464, by rfl⟩ : syracuseStep 3923905 = 2942929) B2942929
theorem B5095361 : Blo 1674037 5095361 := bstep (se 2 (by rfl) ⟨1910760, by rfl⟩ : syracuseStep 5095361 = 3821521) B3821521
theorem B8044505 : Blo 1674037 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B3768281 : Blo 1674037 3768281 := bstep (se 2 (by rfl) ⟨1413105, by rfl⟩ : syracuseStep 3768281 = 2826211) B2826211
theorem B4022273 : Blo 1674037 4022273 := bstep (se 2 (by rfl) ⟨1508352, by rfl⟩ : syracuseStep 4022273 = 3016705) B3016705
theorem B10182667 : Blo 1674037 10182667 := bstep (se 1 (by rfl) ⟨7637000, by rfl⟩ : syracuseStep 10182667 = 15274001) B15274001
theorem B7151627 : Blo 1674037 7151627 := bstep (se 1 (by rfl) ⟨5363720, by rfl⟩ : syracuseStep 7151627 = 10727441) B10727441
theorem B3768335 : Blo 1674037 3768335 := bstep (se 1 (by rfl) ⟨2826251, by rfl⟩ : syracuseStep 3768335 = 5652503) B5652503
theorem B9543703 : Blo 1674037 9543703 := bstep (se 1 (by rfl) ⟨7157777, by rfl⟩ : syracuseStep 9543703 = 14315555) B14315555
theorem B3768353 : Blo 1674037 3768353 := bstep (se 2 (by rfl) ⟨1413132, by rfl⟩ : syracuseStep 3768353 = 2826265) B2826265
theorem B2826299 : Blo 1674037 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B3178615 : Blo 1674037 3178615 := bstep (se 1 (by rfl) ⟨2383961, by rfl⟩ : syracuseStep 3178615 = 4767923) B4767923
theorem B3768695 : Blo 1674037 3768695 := bstep (se 1 (by rfl) ⟨2826521, by rfl⟩ : syracuseStep 3768695 = 5653043) B5653043
theorem B2384263 : Blo 1674037 2384263 := bstep (se 1 (by rfl) ⟨1788197, by rfl⟩ : syracuseStep 2384263 = 3576395) B3576395
theorem B1884559 : Blo 1674037 1884559 := bstep (se 1 (by rfl) ⟨1413419, by rfl⟩ : syracuseStep 1884559 = 2826839) B2826839
theorem B2826697 : Blo 1674037 2826697 := bstep (se 2 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 2826697 = 2120023) B2120023
theorem B3768875 : Blo 1674037 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B6357761 : Blo 1674037 6357761 := bstep (se 2 (by rfl) ⟨2384160, by rfl⟩ : syracuseStep 6357761 = 4768321) B4768321
theorem B24134435 : Blo 1674037 24134435 := bstep (se 1 (by rfl) ⟨18100826, by rfl⟩ : syracuseStep 24134435 = 36201653) B36201653
theorem B119218979 : Blo 1674037 119218979 := bstep (se 1 (by rfl) ⟨89414234, by rfl⟩ : syracuseStep 119218979 = 178828469) B178828469
theorem B12722993 : Blo 1674037 12722993 := bstep (se 2 (by rfl) ⟨4771122, by rfl⟩ : syracuseStep 12722993 = 9542245) B9542245
theorem B4768571 : Blo 1674037 4768571 := bstep (se 1 (by rfl) ⟨3576428, by rfl⟩ : syracuseStep 4768571 = 7152857) B7152857
theorem B4023175 : Blo 1674037 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B1885063 : Blo 1674037 1885063 := bstep (se 1 (by rfl) ⟨1413797, by rfl⟩ : syracuseStep 1885063 = 2827595) B2827595
theorem B3769235 : Blo 1674037 3769235 := bstep (se 1 (by rfl) ⟨2826926, by rfl⟩ : syracuseStep 3769235 = 5653853) B5653853
theorem B17671063 : Blo 1674037 17671063 := bstep (se 1 (by rfl) ⟨13253297, by rfl⟩ : syracuseStep 17671063 = 26506595) B26506595
theorem B7152569 : Blo 1674037 7152569 := bstep (se 2 (by rfl) ⟨2682213, by rfl⟩ : syracuseStep 7152569 = 5364427) B5364427
theorem B3769289 : Blo 1674037 3769289 := bstep (se 2 (by rfl) ⟨1413483, by rfl⟩ : syracuseStep 3769289 = 2826967) B2826967
theorem B1885243 : Blo 1674037 1885243 := bstep (se 1 (by rfl) ⟨1413932, by rfl⟩ : syracuseStep 1885243 = 2827865) B2827865
theorem B2384969 : Blo 1674037 2384969 := bstep (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) B1788727
theorem B2827399 : Blo 1674037 2827399 := bstep (se 1 (by rfl) ⟨2120549, by rfl⟩ : syracuseStep 2827399 = 4241099) B4241099
theorem B2385083 : Blo 1674037 2385083 := bstep (se 1 (by rfl) ⟨1788812, by rfl⟩ : syracuseStep 2385083 = 3577625) B3577625
theorem B8480051 : Blo 1674037 8480051 := bstep (se 1 (by rfl) ⟨6360038, by rfl⟩ : syracuseStep 8480051 = 12720077) B12720077
theorem B19342651 : Blo 1674037 19342651 := bstep (se 1 (by rfl) ⟨14506988, by rfl⟩ : syracuseStep 19342651 = 29013977) B29013977
theorem B16106845 : Blo 1674037 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B10184051 : Blo 1674037 10184051 := bstep (se 1 (by rfl) ⟨7638038, by rfl⟩ : syracuseStep 10184051 = 15276077) B15276077
theorem B30549383 : Blo 1674037 30549383 := bstep (se 1 (by rfl) ⟨22912037, by rfl⟩ : syracuseStep 30549383 = 45824075) B45824075
theorem B5653907 : Blo 1674037 5653907 := bstep (se 1 (by rfl) ⟨4240430, by rfl⟩ : syracuseStep 5653907 = 8480861) B8480861
theorem B4769209 : Blo 1674037 4769209 := bstep (se 2 (by rfl) ⟨1788453, by rfl⟩ : syracuseStep 4769209 = 3576907) B3576907
theorem B8480375 : Blo 1674037 8480375 := bstep (se 1 (by rfl) ⟨6360281, by rfl⟩ : syracuseStep 8480375 = 12720563) B12720563
theorem B3769991 : Blo 1674037 3769991 := bstep (se 1 (by rfl) ⟨2827493, by rfl⟩ : syracuseStep 3769991 = 5654987) B5654987
theorem B32204465 : Blo 1674037 32204465 := bstep (se 2 (by rfl) ⟨12076674, by rfl⟩ : syracuseStep 32204465 = 24153349) B24153349
theorem B3180217 : Blo 1674037 3180217 := bstep (se 2 (by rfl) ⟨1192581, by rfl⟩ : syracuseStep 3180217 = 2385163) B2385163
theorem B2828047 : Blo 1674037 2828047 := bstep (se 1 (by rfl) ⟨2121035, by rfl⟩ : syracuseStep 2828047 = 4242071) B4242071
theorem B2385721 : Blo 1674037 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B3770171 : Blo 1674037 3770171 := bstep (se 1 (by rfl) ⟨2827628, by rfl⟩ : syracuseStep 3770171 = 5655257) B5655257
theorem B4769597 : Blo 1674037 4769597 := bstep (se 3 (by rfl) ⟨894299, by rfl⟩ : syracuseStep 4769597 = 1788599) B1788599
theorem B6358931 : Blo 1674037 6358931 := bstep (se 1 (by rfl) ⟨4769198, by rfl⟩ : syracuseStep 6358931 = 9538397) B9538397
theorem B4835225 : Blo 1674037 4835225 := bstep (se 2 (by rfl) ⟨1813209, by rfl⟩ : syracuseStep 4835225 = 3626419) B3626419
theorem B20375459 : Blo 1674037 20375459 := bstep (se 1 (by rfl) ⟨15281594, by rfl⟩ : syracuseStep 20375459 = 30563189) B30563189
theorem B3770297 : Blo 1674037 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B3180559 : Blo 1674037 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B4835387 : Blo 1674037 4835387 := bstep (se 1 (by rfl) ⟨3626540, by rfl⟩ : syracuseStep 4835387 = 7253081) B7253081
theorem B8046793 : Blo 1674037 8046793 := bstep (se 2 (by rfl) ⟨3017547, by rfl⟩ : syracuseStep 8046793 = 6035095) B6035095
theorem B3770639 : Blo 1674037 3770639 := bstep (se 1 (by rfl) ⟨2827979, by rfl⟩ : syracuseStep 3770639 = 5655959) B5655959
theorem B3770657 : Blo 1674037 3770657 := bstep (se 2 (by rfl) ⟨1413996, by rfl⟩ : syracuseStep 3770657 = 2827993) B2827993
theorem B2263339 : Blo 1674037 2263339 := bstep (se 1 (by rfl) ⟨1697504, by rfl⟩ : syracuseStep 2263339 = 3395009) B3395009
theorem B6359431 : Blo 1674037 6359431 := bstep (se 1 (by rfl) ⟨4769573, by rfl⟩ : syracuseStep 6359431 = 9539147) B9539147
theorem B16107923 : Blo 1674037 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B13576657 : Blo 1674037 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B16108075 : Blo 1674037 16108075 := bstep (se 1 (by rfl) ⟨12081056, by rfl⟩ : syracuseStep 16108075 = 24162113) B24162113
theorem B8481347 : Blo 1674037 8481347 := bstep (se 1 (by rfl) ⟨6361010, by rfl⟩ : syracuseStep 8481347 = 12722021) B12722021
theorem B6040183 : Blo 1674037 6040183 := bstep (se 1 (by rfl) ⟨4530137, by rfl⟩ : syracuseStep 6040183 = 9060275) B9060275
theorem B3770999 : Blo 1674037 3770999 := bstep (se 1 (by rfl) ⟨2828249, by rfl⟩ : syracuseStep 3770999 = 5656499) B5656499
theorem B5655311 : Blo 1674037 5655311 := bstep (se 1 (by rfl) ⟨4241483, by rfl⟩ : syracuseStep 5655311 = 8482967) B8482967
theorem B1674043 : Blo 1674037 1674043 := bstep (se 1 (by rfl) ⟨1255532, by rfl⟩ : syracuseStep 1674043 = 2511065) B2511065
theorem B1674119 : Blo 1674037 1674119 := bstep (se 1 (by rfl) ⟨1255589, by rfl⟩ : syracuseStep 1674119 = 2511179) B2511179
theorem B7154567 : Blo 1674037 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B8481671 : Blo 1674037 8481671 := bstep (se 1 (by rfl) ⟨6361253, by rfl⟩ : syracuseStep 8481671 = 12722507) B12722507
theorem B3181447 : Blo 1674037 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B1674127 : Blo 1674037 1674127 := bstep (se 1 (by rfl) ⟨1255595, by rfl⟩ : syracuseStep 1674127 = 2511191) B2511191
theorem B4770713 : Blo 1674037 4770713 := bstep (se 2 (by rfl) ⟨1789017, by rfl⟩ : syracuseStep 4770713 = 3578035) B3578035
theorem B30559157 : Blo 1674037 30559157 := bstep (se 5 (by rfl) ⟨1432460, by rfl⟩ : syracuseStep 30559157 = 2864921) B2864921
theorem B1674171 : Blo 1674037 1674171 := bstep (se 1 (by rfl) ⟨1255628, by rfl⟩ : syracuseStep 1674171 = 2511257) B2511257
theorem B1674247 : Blo 1674037 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B1674255 : Blo 1674037 1674255 := bstep (se 1 (by rfl) ⟨1255691, by rfl⟩ : syracuseStep 1674255 = 2511383) B2511383
theorem B5655581 : Blo 1674037 5655581 := bstep (se 3 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 5655581 = 2120843) B2120843
theorem B1674299 : Blo 1674037 1674299 := bstep (se 1 (by rfl) ⟨1255724, by rfl⟩ : syracuseStep 1674299 = 2511449) B2511449
theorem B9669719 : Blo 1674037 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B1674375 : Blo 1674037 1674375 := bstep (se 1 (by rfl) ⟨1255781, by rfl⟩ : syracuseStep 1674375 = 2511563) B2511563
theorem B1674383 : Blo 1674037 1674383 := bstep (se 1 (by rfl) ⟨1255787, by rfl⟩ : syracuseStep 1674383 = 2511575) B2511575
theorem B1674427 : Blo 1674037 1674427 := bstep (se 1 (by rfl) ⟨1255820, by rfl⟩ : syracuseStep 1674427 = 2511641) B2511641
theorem B1674503 : Blo 1674037 1674503 := bstep (se 1 (by rfl) ⟨1255877, by rfl⟩ : syracuseStep 1674503 = 2511755) B2511755
theorem B1674511 : Blo 1674037 1674511 := bstep (se 1 (by rfl) ⟨1255883, by rfl⟩ : syracuseStep 1674511 = 2511767) B2511767
theorem B1674555 : Blo 1674037 1674555 := bstep (se 1 (by rfl) ⟨1255916, by rfl⟩ : syracuseStep 1674555 = 2511833) B2511833
theorem B8154503 : Blo 1674037 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B1674631 : Blo 1674037 1674631 := bstep (se 1 (by rfl) ⟨1255973, by rfl⟩ : syracuseStep 1674631 = 2511947) B2511947
theorem B1674639 : Blo 1674037 1674639 := bstep (se 1 (by rfl) ⟨1255979, by rfl⟩ : syracuseStep 1674639 = 2511959) B2511959
theorem B1813903 : Blo 1674037 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B12078521 : Blo 1674037 12078521 := bstep (se 2 (by rfl) ⟨4529445, by rfl⟩ : syracuseStep 12078521 = 9058891) B9058891
theorem B1674683 : Blo 1674037 1674683 := bstep (se 1 (by rfl) ⟨1256012, by rfl⟩ : syracuseStep 1674683 = 2512025) B2512025
theorem B4025857 : Blo 1674037 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B1674759 : Blo 1674037 1674759 := bstep (se 1 (by rfl) ⟨1256069, by rfl⟩ : syracuseStep 1674759 = 2512139) B2512139
theorem B1674767 : Blo 1674037 1674767 := bstep (se 1 (by rfl) ⟨1256075, by rfl⟩ : syracuseStep 1674767 = 2512151) B2512151
theorem B1674811 : Blo 1674037 1674811 := bstep (se 1 (by rfl) ⟨1256108, by rfl⟩ : syracuseStep 1674811 = 2512217) B2512217
theorem B4238963 : Blo 1674037 4238963 := bstep (se 1 (by rfl) ⟨3179222, by rfl⟩ : syracuseStep 4238963 = 6358445) B6358445
theorem B1674887 : Blo 1674037 1674887 := bstep (se 1 (by rfl) ⟨1256165, by rfl⟩ : syracuseStep 1674887 = 2512331) B2512331
theorem B1674895 : Blo 1674037 1674895 := bstep (se 1 (by rfl) ⟨1256171, by rfl⟩ : syracuseStep 1674895 = 2512343) B2512343
theorem B34369201 : Blo 1674037 34369201 := bstep (se 2 (by rfl) ⟨12888450, by rfl⟩ : syracuseStep 34369201 = 25776901) B25776901
theorem B2682553 : Blo 1674037 2682553 := bstep (se 2 (by rfl) ⟨1005957, by rfl⟩ : syracuseStep 2682553 = 2011915) B2011915
theorem B1674939 : Blo 1674037 1674939 := bstep (se 1 (by rfl) ⟨1256204, by rfl⟩ : syracuseStep 1674939 = 2512409) B2512409
theorem B9539329 : Blo 1674037 9539329 := bstep (se 2 (by rfl) ⟨3577248, by rfl⟩ : syracuseStep 9539329 = 7154497) B7154497
theorem B1675015 : Blo 1674037 1675015 := bstep (se 1 (by rfl) ⟨1256261, by rfl⟩ : syracuseStep 1675015 = 2512523) B2512523
theorem B1675023 : Blo 1674037 1675023 := bstep (se 1 (by rfl) ⟨1256267, by rfl⟩ : syracuseStep 1675023 = 2512535) B2512535
theorem B3870497 : Blo 1674037 3870497 := bstep (se 2 (by rfl) ⟨1451436, by rfl⟩ : syracuseStep 3870497 = 2902873) B2902873
theorem B1675067 : Blo 1674037 1675067 := bstep (se 1 (by rfl) ⟨1256300, by rfl⟩ : syracuseStep 1675067 = 2512601) B2512601
theorem B1675143 : Blo 1674037 1675143 := bstep (se 1 (by rfl) ⟨1256357, by rfl⟩ : syracuseStep 1675143 = 2512715) B2512715
theorem B1675151 : Blo 1674037 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B27152279 : Blo 1674037 27152279 := bstep (se 1 (by rfl) ⟨20364209, by rfl⟩ : syracuseStep 27152279 = 40728419) B40728419
theorem B4526009 : Blo 1674037 4526009 := bstep (se 2 (by rfl) ⟨1697253, by rfl⟩ : syracuseStep 4526009 = 3394507) B3394507
theorem B2682809 : Blo 1674037 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B1675195 : Blo 1674037 1675195 := bstep (se 1 (by rfl) ⟨1256396, by rfl⟩ : syracuseStep 1675195 = 2512793) B2512793
theorem B1675271 : Blo 1674037 1675271 := bstep (se 1 (by rfl) ⟨1256453, by rfl⟩ : syracuseStep 1675271 = 2512907) B2512907
theorem B1675279 : Blo 1674037 1675279 := bstep (se 1 (by rfl) ⟨1256459, by rfl⟩ : syracuseStep 1675279 = 2512919) B2512919
theorem B1675323 : Blo 1674037 1675323 := bstep (se 1 (by rfl) ⟨1256492, by rfl⟩ : syracuseStep 1675323 = 2512985) B2512985
theorem B4239479 : Blo 1674037 4239479 := bstep (se 1 (by rfl) ⟨3179609, by rfl⟩ : syracuseStep 4239479 = 6359219) B6359219
theorem B1675399 : Blo 1674037 1675399 := bstep (se 1 (by rfl) ⟨1256549, by rfl⟩ : syracuseStep 1675399 = 2513099) B2513099
theorem B1675407 : Blo 1674037 1675407 := bstep (se 1 (by rfl) ⟨1256555, by rfl⟩ : syracuseStep 1675407 = 2513111) B2513111
theorem B1675451 : Blo 1674037 1675451 := bstep (se 1 (by rfl) ⟨1256588, by rfl⟩ : syracuseStep 1675451 = 2513177) B2513177
theorem B2511095 : Blo 1674037 2511095 := bstep (se 1 (by rfl) ⟨1883321, by rfl⟩ : syracuseStep 2511095 = 3766643) B3766643
theorem B1675527 : Blo 1674037 1675527 := bstep (se 1 (by rfl) ⟨1256645, by rfl⟩ : syracuseStep 1675527 = 2513291) B2513291
theorem B2511119 : Blo 1674037 2511119 := bstep (se 1 (by rfl) ⟨1883339, by rfl⟩ : syracuseStep 2511119 = 3766679) B3766679
theorem B3576079 : Blo 1674037 3576079 := bstep (se 1 (by rfl) ⟨2682059, by rfl⟩ : syracuseStep 3576079 = 5364119) B5364119
theorem B9539855 : Blo 1674037 9539855 := bstep (se 1 (by rfl) ⟨7154891, by rfl⟩ : syracuseStep 9539855 = 14309783) B14309783
theorem B1675535 : Blo 1674037 1675535 := bstep (se 1 (by rfl) ⟨1256651, by rfl⟩ : syracuseStep 1675535 = 2513303) B2513303
theorem B4772125 : Blo 1674037 4772125 := bstep (se 3 (by rfl) ⟨894773, by rfl⟩ : syracuseStep 4772125 = 1789547) B1789547
theorem B7156001 : Blo 1674037 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B2511161 : Blo 1674037 2511161 := bstep (se 2 (by rfl) ⟨941685, by rfl⟩ : syracuseStep 2511161 = 1883371) B1883371
theorem B1675579 : Blo 1674037 1675579 := bstep (se 1 (by rfl) ⟨1256684, by rfl⟩ : syracuseStep 1675579 = 2513369) B2513369
theorem B2511239 : Blo 1674037 2511239 := bstep (se 1 (by rfl) ⟨1883429, by rfl⟩ : syracuseStep 2511239 = 3766859) B3766859
theorem B1675655 : Blo 1674037 1675655 := bstep (se 1 (by rfl) ⟨1256741, by rfl⟩ : syracuseStep 1675655 = 2513483) B2513483
theorem B1675663 : Blo 1674037 1675663 := bstep (se 1 (by rfl) ⟨1256747, by rfl⟩ : syracuseStep 1675663 = 2513495) B2513495
theorem B8049041 : Blo 1674037 8049041 := bstep (se 2 (by rfl) ⟨3018390, by rfl⟩ : syracuseStep 8049041 = 6036781) B6036781
theorem B2511275 : Blo 1674037 2511275 := bstep (se 1 (by rfl) ⟨1883456, by rfl⟩ : syracuseStep 2511275 = 3766913) B3766913
theorem B4026809 : Blo 1674037 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B1675707 : Blo 1674037 1675707 := bstep (se 1 (by rfl) ⟨1256780, by rfl⟩ : syracuseStep 1675707 = 2513561) B2513561
theorem B2511305 : Blo 1674037 2511305 := bstep (se 2 (by rfl) ⟨941739, by rfl⟩ : syracuseStep 2511305 = 1883479) B1883479
theorem B4772297 : Blo 1674037 4772297 := bstep (se 2 (by rfl) ⟨1789611, by rfl⟩ : syracuseStep 4772297 = 3579223) B3579223
theorem B4772353 : Blo 1674037 4772353 := bstep (se 2 (by rfl) ⟨1789632, by rfl⟩ : syracuseStep 4772353 = 3579265) B3579265
theorem B1675783 : Blo 1674037 1675783 := bstep (se 1 (by rfl) ⟨1256837, by rfl⟩ : syracuseStep 1675783 = 2513675) B2513675
theorem B1675791 : Blo 1674037 1675791 := bstep (se 1 (by rfl) ⟨1256843, by rfl⟩ : syracuseStep 1675791 = 2513687) B2513687
theorem B2511419 : Blo 1674037 2511419 := bstep (se 1 (by rfl) ⟨1883564, by rfl⟩ : syracuseStep 2511419 = 3767129) B3767129
theorem B1675835 : Blo 1674037 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B13587011 : Blo 1674037 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B2511479 : Blo 1674037 2511479 := bstep (se 1 (by rfl) ⟨1883609, by rfl⟩ : syracuseStep 2511479 = 3767219) B3767219
theorem B10728055 : Blo 1674037 10728055 := bstep (se 1 (by rfl) ⟨8046041, by rfl⟩ : syracuseStep 10728055 = 16092083) B16092083
theorem B7156343 : Blo 1674037 7156343 := bstep (se 1 (by rfl) ⟨5367257, by rfl⟩ : syracuseStep 7156343 = 10734515) B10734515
theorem B1675911 : Blo 1674037 1675911 := bstep (se 1 (by rfl) ⟨1256933, by rfl⟩ : syracuseStep 1675911 = 2513867) B2513867
theorem B2511503 : Blo 1674037 2511503 := bstep (se 1 (by rfl) ⟨1883627, by rfl⟩ : syracuseStep 2511503 = 3767255) B3767255
theorem B1675919 : Blo 1674037 1675919 := bstep (se 1 (by rfl) ⟨1256939, by rfl⟩ : syracuseStep 1675919 = 2513879) B2513879
theorem B2511545 : Blo 1674037 2511545 := bstep (se 2 (by rfl) ⟨941829, by rfl⟩ : syracuseStep 2511545 = 1883659) B1883659
theorem B1675963 : Blo 1674037 1675963 := bstep (se 1 (by rfl) ⟨1256972, by rfl⟩ : syracuseStep 1675963 = 2513945) B2513945
theorem B2511623 : Blo 1674037 2511623 := bstep (se 1 (by rfl) ⟨1883717, by rfl⟩ : syracuseStep 2511623 = 3767435) B3767435
theorem B12071717 : Blo 1674037 12071717 := bstep (se 4 (by rfl) ⟨1131723, by rfl⟩ : syracuseStep 12071717 = 2263447) B2263447
theorem B2511659 : Blo 1674037 2511659 := bstep (se 1 (by rfl) ⟨1883744, by rfl⟩ : syracuseStep 2511659 = 3767489) B3767489
theorem B2511689 : Blo 1674037 2511689 := bstep (se 2 (by rfl) ⟨941883, by rfl⟩ : syracuseStep 2511689 = 1883767) B1883767
theorem B4772695 : Blo 1674037 4772695 := bstep (se 1 (by rfl) ⟨3579521, by rfl⟩ : syracuseStep 4772695 = 7159043) B7159043
theorem B2683783 : Blo 1674037 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B2511803 : Blo 1674037 2511803 := bstep (se 1 (by rfl) ⟨1883852, by rfl⟩ : syracuseStep 2511803 = 3767705) B3767705
theorem B2511863 : Blo 1674037 2511863 := bstep (se 1 (by rfl) ⟨1883897, by rfl⟩ : syracuseStep 2511863 = 3767795) B3767795
theorem B20370437 : Blo 1674037 20370437 := bstep (se 4 (by rfl) ⟨1909728, by rfl⟩ : syracuseStep 20370437 = 3819457) B3819457
theorem B2511887 : Blo 1674037 2511887 := bstep (se 1 (by rfl) ⟨1883915, by rfl⟩ : syracuseStep 2511887 = 3767831) B3767831
theorem B8475677 : Blo 1674037 8475677 := bstep (se 3 (by rfl) ⟨1589189, by rfl⟩ : syracuseStep 8475677 = 3178379) B3178379
theorem B6034475 : Blo 1674037 6034475 := bstep (se 1 (by rfl) ⟨4525856, by rfl⟩ : syracuseStep 6034475 = 9051713) B9051713
theorem B2511929 : Blo 1674037 2511929 := bstep (se 2 (by rfl) ⟨941973, by rfl⟩ : syracuseStep 2511929 = 1883947) B1883947
theorem B13579325 : Blo 1674037 13579325 := bstep (se 3 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 13579325 = 5092247) B5092247
theorem B4240471 : Blo 1674037 4240471 := bstep (se 1 (by rfl) ⟨3180353, by rfl⟩ : syracuseStep 4240471 = 6360707) B6360707
theorem B11465815 : Blo 1674037 11465815 := bstep (se 1 (by rfl) ⟨8599361, by rfl⟩ : syracuseStep 11465815 = 17198723) B17198723
theorem B2512007 : Blo 1674037 2512007 := bstep (se 1 (by rfl) ⟨1884005, by rfl⟩ : syracuseStep 2512007 = 3768011) B3768011
theorem B2512043 : Blo 1674037 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B2512073 : Blo 1674037 2512073 := bstep (se 2 (by rfl) ⟨942027, by rfl⟩ : syracuseStep 2512073 = 1884055) B1884055
theorem B5231873 : Blo 1674037 5231873 := bstep (se 2 (by rfl) ⟨1961952, by rfl⟩ : syracuseStep 5231873 = 3923905) B3923905
theorem B2118955 : Blo 1674037 2118955 := bstep (se 1 (by rfl) ⟨1589216, by rfl⟩ : syracuseStep 2118955 = 3178433) B3178433
theorem B3396907 : Blo 1674037 3396907 := bstep (se 1 (by rfl) ⟨2547680, by rfl⟩ : syracuseStep 3396907 = 5095361) B5095361
theorem B5363003 : Blo 1674037 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B13579579 : Blo 1674037 13579579 := bstep (se 1 (by rfl) ⟨10184684, by rfl⟩ : syracuseStep 13579579 = 20369369) B20369369
theorem B2512187 : Blo 1674037 2512187 := bstep (se 1 (by rfl) ⟨1884140, by rfl⟩ : syracuseStep 2512187 = 3768281) B3768281
theorem B2512247 : Blo 1674037 2512247 := bstep (se 1 (by rfl) ⟨1884185, by rfl⟩ : syracuseStep 2512247 = 3768371) B3768371
theorem B6034823 : Blo 1674037 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B4240775 : Blo 1674037 4240775 := bstep (se 1 (by rfl) ⟨3180581, by rfl⟩ : syracuseStep 4240775 = 6361163) B6361163
theorem B2512271 : Blo 1674037 2512271 := bstep (se 1 (by rfl) ⟨1884203, by rfl⟩ : syracuseStep 2512271 = 3768407) B3768407
theorem B3020179 : Blo 1674037 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B2512313 : Blo 1674037 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B8476163 : Blo 1674037 8476163 := bstep (se 1 (by rfl) ⟨6357122, by rfl⟩ : syracuseStep 8476163 = 12714245) B12714245
theorem B2512391 : Blo 1674037 2512391 := bstep (se 1 (by rfl) ⟨1884293, by rfl⟩ : syracuseStep 2512391 = 3768587) B3768587
theorem B4240907 : Blo 1674037 4240907 := bstep (se 1 (by rfl) ⟨3180680, by rfl⟩ : syracuseStep 4240907 = 6361361) B6361361
theorem B2512427 : Blo 1674037 2512427 := bstep (se 1 (by rfl) ⟨1884320, by rfl⟩ : syracuseStep 2512427 = 3768641) B3768641
theorem B2512457 : Blo 1674037 2512457 := bstep (se 2 (by rfl) ⟨942171, by rfl⟩ : syracuseStep 2512457 = 1884343) B1884343
theorem B5092951 : Blo 1674037 5092951 := bstep (se 1 (by rfl) ⟨3819713, by rfl⟩ : syracuseStep 5092951 = 7639427) B7639427
theorem B2512571 : Blo 1674037 2512571 := bstep (se 1 (by rfl) ⟨1884428, by rfl⟩ : syracuseStep 2512571 = 3768857) B3768857
theorem B9541313 : Blo 1674037 9541313 := bstep (se 2 (by rfl) ⟨3577992, by rfl⟩ : syracuseStep 9541313 = 7155985) B7155985
theorem B2512631 : Blo 1674037 2512631 := bstep (se 1 (by rfl) ⟨1884473, by rfl⟩ : syracuseStep 2512631 = 3768947) B3768947
theorem B2512655 : Blo 1674037 2512655 := bstep (se 1 (by rfl) ⟨1884491, by rfl⟩ : syracuseStep 2512655 = 3768983) B3768983
theorem B2512697 : Blo 1674037 2512697 := bstep (se 2 (by rfl) ⟨942261, by rfl⟩ : syracuseStep 2512697 = 1884523) B1884523
theorem B5650235 : Blo 1674037 5650235 := bstep (se 1 (by rfl) ⟨4237676, by rfl⟩ : syracuseStep 5650235 = 8475353) B8475353
theorem B4298555 : Blo 1674037 4298555 := bstep (se 1 (by rfl) ⟨3223916, by rfl⟩ : syracuseStep 4298555 = 6447833) B6447833
theorem B18118475 : Blo 1674037 18118475 := bstep (se 1 (by rfl) ⟨13588856, by rfl⟩ : syracuseStep 18118475 = 27177713) B27177713
theorem B2512775 : Blo 1674037 2512775 := bstep (se 1 (by rfl) ⟨1884581, by rfl⟩ : syracuseStep 2512775 = 3769163) B3769163
theorem B19085219 : Blo 1674037 19085219 := bstep (se 1 (by rfl) ⟨14313914, by rfl⟩ : syracuseStep 19085219 = 28627829) B28627829
theorem B2512811 : Blo 1674037 2512811 := bstep (se 1 (by rfl) ⟨1884608, by rfl⟩ : syracuseStep 2512811 = 3769217) B3769217
theorem B2512841 : Blo 1674037 2512841 := bstep (se 2 (by rfl) ⟨942315, by rfl⟩ : syracuseStep 2512841 = 1884631) B1884631
theorem B4241423 : Blo 1674037 4241423 := bstep (se 1 (by rfl) ⟨3181067, by rfl⟩ : syracuseStep 4241423 = 6362135) B6362135
theorem B2512955 : Blo 1674037 2512955 := bstep (se 1 (by rfl) ⟨1884716, by rfl⟩ : syracuseStep 2512955 = 3769433) B3769433
theorem B2513015 : Blo 1674037 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B2513039 : Blo 1674037 2513039 := bstep (se 1 (by rfl) ⟨1884779, by rfl⟩ : syracuseStep 2513039 = 3769559) B3769559
theorem B4241555 : Blo 1674037 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B9050285 : Blo 1674037 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B2513081 : Blo 1674037 2513081 := bstep (se 2 (by rfl) ⟨942405, by rfl⟩ : syracuseStep 2513081 = 1884811) B1884811
theorem B2119927 : Blo 1674037 2119927 := bstep (se 1 (by rfl) ⟨1589945, by rfl⟩ : syracuseStep 2119927 = 3179891) B3179891
theorem B2513159 : Blo 1674037 2513159 := bstep (se 1 (by rfl) ⟨1884869, by rfl⟩ : syracuseStep 2513159 = 3769739) B3769739
theorem B5650721 : Blo 1674037 5650721 := bstep (se 2 (by rfl) ⟨2119020, by rfl⟩ : syracuseStep 5650721 = 4238041) B4238041
theorem B2513195 : Blo 1674037 2513195 := bstep (se 1 (by rfl) ⟨1884896, by rfl⟩ : syracuseStep 2513195 = 3769793) B3769793
theorem B91707713 : Blo 1674037 91707713 := bstep (se 2 (by rfl) ⟨34390392, by rfl⟩ : syracuseStep 91707713 = 68780785) B68780785
theorem B2513225 : Blo 1674037 2513225 := bstep (se 2 (by rfl) ⟨942459, by rfl⟩ : syracuseStep 2513225 = 1884919) B1884919
theorem B2513339 : Blo 1674037 2513339 := bstep (se 1 (by rfl) ⟨1885004, by rfl⟩ : syracuseStep 2513339 = 3770009) B3770009
theorem B2513399 : Blo 1674037 2513399 := bstep (se 1 (by rfl) ⟨1885049, by rfl⟩ : syracuseStep 2513399 = 3770099) B3770099
theorem B2513423 : Blo 1674037 2513423 := bstep (se 1 (by rfl) ⟨1885067, by rfl⟩ : syracuseStep 2513423 = 3770135) B3770135
theorem B16095773 : Blo 1674037 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B3578411 : Blo 1674037 3578411 := bstep (se 1 (by rfl) ⟨2683808, by rfl⟩ : syracuseStep 3578411 = 5367617) B5367617
theorem B2513465 : Blo 1674037 2513465 := bstep (se 2 (by rfl) ⟨942549, by rfl⟩ : syracuseStep 2513465 = 1885099) B1885099
theorem B2120251 : Blo 1674037 2120251 := bstep (se 1 (by rfl) ⟨1590188, by rfl⟩ : syracuseStep 2120251 = 3180377) B3180377
theorem B2513543 : Blo 1674037 2513543 := bstep (se 1 (by rfl) ⟨1885157, by rfl⟩ : syracuseStep 2513543 = 3770315) B3770315
theorem B3766931 : Blo 1674037 3766931 := bstep (se 1 (by rfl) ⟨2825198, by rfl⟩ : syracuseStep 3766931 = 5650397) B5650397
theorem B2513579 : Blo 1674037 2513579 := bstep (se 1 (by rfl) ⟨1885184, by rfl⟩ : syracuseStep 2513579 = 3770369) B3770369
theorem B3766985 : Blo 1674037 3766985 := bstep (se 2 (by rfl) ⟨1412619, by rfl⟩ : syracuseStep 3766985 = 2825239) B2825239
theorem B2513609 : Blo 1674037 2513609 := bstep (se 2 (by rfl) ⟨942603, by rfl⟩ : syracuseStep 2513609 = 1885207) B1885207
theorem B2825003 : Blo 1674037 2825003 := bstep (se 1 (by rfl) ⟨2118752, by rfl⟩ : syracuseStep 2825003 = 4237505) B4237505
theorem B12409649 : Blo 1674037 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B2513723 : Blo 1674037 2513723 := bstep (se 1 (by rfl) ⟨1885292, by rfl⟩ : syracuseStep 2513723 = 3770585) B3770585
theorem B5651315 : Blo 1674037 5651315 := bstep (se 1 (by rfl) ⟨4238486, by rfl⟩ : syracuseStep 5651315 = 8476973) B8476973
theorem B2513783 : Blo 1674037 2513783 := bstep (se 1 (by rfl) ⟨1885337, by rfl⟩ : syracuseStep 2513783 = 3770675) B3770675
theorem B2513807 : Blo 1674037 2513807 := bstep (se 1 (by rfl) ⟨1885355, by rfl⟩ : syracuseStep 2513807 = 3770711) B3770711
theorem B12721049 : Blo 1674037 12721049 := bstep (se 2 (by rfl) ⟨4770393, by rfl⟩ : syracuseStep 12721049 = 9540787) B9540787
theorem B2513849 : Blo 1674037 2513849 := bstep (se 2 (by rfl) ⟨942693, by rfl⟩ : syracuseStep 2513849 = 1885387) B1885387
theorem B2513927 : Blo 1674037 2513927 := bstep (se 1 (by rfl) ⟨1885445, by rfl⟩ : syracuseStep 2513927 = 3770891) B3770891
theorem B2513963 : Blo 1674037 2513963 := bstep (se 1 (by rfl) ⟨1885472, by rfl⟩ : syracuseStep 2513963 = 3770945) B3770945
theorem B2513993 : Blo 1674037 2513993 := bstep (se 2 (by rfl) ⟨942747, by rfl⟩ : syracuseStep 2513993 = 1885495) B1885495
theorem B8477783 : Blo 1674037 8477783 := bstep (se 1 (by rfl) ⟨6358337, by rfl⟩ : syracuseStep 8477783 = 12716675) B12716675
theorem B7158871 : Blo 1674037 7158871 := bstep (se 1 (by rfl) ⟨5369153, by rfl⟩ : syracuseStep 7158871 = 10738307) B10738307
theorem B2825401 : Blo 1674037 2825401 := bstep (se 2 (by rfl) ⟨1059525, by rfl⟩ : syracuseStep 2825401 = 2119051) B2119051
theorem B1883407 : Blo 1674037 1883407 := bstep (se 1 (by rfl) ⟨1412555, by rfl⟩ : syracuseStep 1883407 = 2825111) B2825111
theorem B3767687 : Blo 1674037 3767687 := bstep (se 1 (by rfl) ⟨2825765, by rfl⟩ : syracuseStep 3767687 = 5651531) B5651531
theorem B21470669 : Blo 1674037 21470669 := bstep (se 3 (by rfl) ⟨4025750, by rfl⟩ : syracuseStep 21470669 = 8051501) B8051501
theorem B2121223 : Blo 1674037 2121223 := bstep (se 1 (by rfl) ⟨1590917, by rfl⟩ : syracuseStep 2121223 = 3181835) B3181835
theorem B3767867 : Blo 1674037 3767867 := bstep (se 1 (by rfl) ⟨2825900, by rfl⟩ : syracuseStep 3767867 = 5651801) B5651801
theorem B8478269 : Blo 1674037 8478269 := bstep (se 3 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 8478269 = 3179351) B3179351
theorem B40771147 : Blo 1674037 40771147 := bstep (se 1 (by rfl) ⟨30578360, by rfl⟩ : syracuseStep 40771147 = 61156721) B61156721
theorem B10878583 : Blo 1674037 10878583 := bstep (se 1 (by rfl) ⟨8158937, by rfl⟩ : syracuseStep 10878583 = 16317875) B16317875
theorem B4529783 : Blo 1674037 4529783 := bstep (se 1 (by rfl) ⟨3397337, by rfl⟩ : syracuseStep 4529783 = 6794675) B6794675
theorem B3767993 : Blo 1674037 3767993 := bstep (se 2 (by rfl) ⟨1412997, by rfl⟩ : syracuseStep 3767993 = 2825995) B2825995
theorem B1883911 : Blo 1674037 1883911 := bstep (se 1 (by rfl) ⟨1412933, by rfl⟩ : syracuseStep 1883911 = 2825867) B2825867
theorem B3178273 : Blo 1674037 3178273 := bstep (se 2 (by rfl) ⟨1191852, by rfl⟩ : syracuseStep 3178273 = 2383705) B2383705
theorem B2826103 : Blo 1674037 2826103 := bstep (se 1 (by rfl) ⟨2119577, by rfl⟩ : syracuseStep 2826103 = 4239155) B4239155
theorem B1884091 : Blo 1674037 1884091 := bstep (se 1 (by rfl) ⟨1413068, by rfl⟩ : syracuseStep 1884091 = 2826137) B2826137
theorem B4767751 : Blo 1674037 4767751 := bstep (se 1 (by rfl) ⟨3575813, by rfl⟩ : syracuseStep 4767751 = 7151627) B7151627
theorem B1884199 : Blo 1674037 1884199 := bstep (se 1 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 1884199 = 2826299) B2826299
theorem B2826319 : Blo 1674037 2826319 := bstep (se 1 (by rfl) ⟨2119739, by rfl⟩ : syracuseStep 2826319 = 4239479) B4239479
theorem B12894365 : Blo 1674037 12894365 := bstep (se 3 (by rfl) ⟨2417693, by rfl⟩ : syracuseStep 12894365 = 4835387) B4835387
theorem B5366027 : Blo 1674037 5366027 := bstep (se 1 (by rfl) ⟨4024520, by rfl⟩ : syracuseStep 5366027 = 8049041) B8049041
theorem B2826569 : Blo 1674037 2826569 := bstep (se 2 (by rfl) ⟨1059963, by rfl⟩ : syracuseStep 2826569 = 2119927) B2119927
theorem B4768105 : Blo 1674037 4768105 := bstep (se 2 (by rfl) ⟨1788039, by rfl⟩ : syracuseStep 4768105 = 3576079) B3576079
theorem B3179017 : Blo 1674037 3179017 := bstep (se 2 (by rfl) ⟨1192131, by rfl⟩ : syracuseStep 3179017 = 2384263) B2384263
theorem B8479241 : Blo 1674037 8479241 := bstep (se 2 (by rfl) ⟨3179715, by rfl⟩ : syracuseStep 8479241 = 6359431) B6359431
theorem B16089623 : Blo 1674037 16089623 := bstep (se 1 (by rfl) ⟨12067217, by rfl⟩ : syracuseStep 16089623 = 24134435) B24134435
theorem B79479319 : Blo 1674037 79479319 := bstep (se 1 (by rfl) ⟨59609489, by rfl⟩ : syracuseStep 79479319 = 119218979) B119218979
theorem B3768929 : Blo 1674037 3768929 := bstep (se 2 (by rfl) ⟨1413348, by rfl⟩ : syracuseStep 3768929 = 2826697) B2826697
theorem B4768379 : Blo 1674037 4768379 := bstep (se 1 (by rfl) ⟨3576284, by rfl⟩ : syracuseStep 4768379 = 7152569) B7152569
theorem B4022983 : Blo 1674037 4022983 := bstep (se 1 (by rfl) ⟨3017237, by rfl⟩ : syracuseStep 4022983 = 6034475) B6034475
theorem B9052883 : Blo 1674037 9052883 := bstep (se 1 (by rfl) ⟨6789662, by rfl⟩ : syracuseStep 9052883 = 13579325) B13579325
theorem B2827001 : Blo 1674037 2827001 := bstep (se 2 (by rfl) ⟨1060125, by rfl⟩ : syracuseStep 2827001 = 2120251) B2120251
theorem B14304073 : Blo 1674037 14304073 := bstep (se 2 (by rfl) ⟨5364027, by rfl⟩ : syracuseStep 14304073 = 10728055) B10728055
theorem B8053577 : Blo 1674037 8053577 := bstep (se 2 (by rfl) ⟨3020091, by rfl⟩ : syracuseStep 8053577 = 6040183) B6040183
theorem B5653367 : Blo 1674037 5653367 := bstep (se 1 (by rfl) ⟨4240025, by rfl⟩ : syracuseStep 5653367 = 8480051) B8480051
theorem B20366255 : Blo 1674037 20366255 := bstep (se 1 (by rfl) ⟨15274691, by rfl⟩ : syracuseStep 20366255 = 30549383) B30549383
theorem B4023215 : Blo 1674037 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B2827183 : Blo 1674037 2827183 := bstep (se 1 (by rfl) ⟨2120387, by rfl⟩ : syracuseStep 2827183 = 4240775) B4240775
theorem B3769271 : Blo 1674037 3769271 := bstep (se 1 (by rfl) ⟨2826953, by rfl⟩ : syracuseStep 3769271 = 5653907) B5653907
theorem B2827271 : Blo 1674037 2827271 := bstep (se 1 (by rfl) ⟨2120453, by rfl⟩ : syracuseStep 2827271 = 4240907) B4240907
theorem B5653583 : Blo 1674037 5653583 := bstep (se 1 (by rfl) ⟨4240187, by rfl⟩ : syracuseStep 5653583 = 8480375) B8480375
theorem B23561417 : Blo 1674037 23561417 := bstep (se 2 (by rfl) ⟨8835531, by rfl⟩ : syracuseStep 23561417 = 17671063) B17671063
theorem B3179731 : Blo 1674037 3179731 := bstep (se 1 (by rfl) ⟨2384798, by rfl⟩ : syracuseStep 3179731 = 4769597) B4769597
theorem B13583639 : Blo 1674037 13583639 := bstep (se 1 (by rfl) ⟨10187729, by rfl⟩ : syracuseStep 13583639 = 20375459) B20375459
theorem B12723479 : Blo 1674037 12723479 := bstep (se 1 (by rfl) ⟨9542609, by rfl⟩ : syracuseStep 12723479 = 19085219) B19085219
theorem B2827615 : Blo 1674037 2827615 := bstep (se 1 (by rfl) ⟨2120711, by rfl⟩ : syracuseStep 2827615 = 4241423) B4241423
theorem B2827703 : Blo 1674037 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B5653961 : Blo 1674037 5653961 := bstep (se 2 (by rfl) ⟨2120235, by rfl⟩ : syracuseStep 5653961 = 4240471) B4240471
theorem B15287753 : Blo 1674037 15287753 := bstep (se 2 (by rfl) ⟨5732907, by rfl⟩ : syracuseStep 15287753 = 11465815) B11465815
theorem B9545161 : Blo 1674037 9545161 := bstep (se 2 (by rfl) ⟨3579435, by rfl⟩ : syracuseStep 9545161 = 7158871) B7158871
theorem B3769865 : Blo 1674037 3769865 := bstep (se 2 (by rfl) ⟨1413699, by rfl⟩ : syracuseStep 3769865 = 2827399) B2827399
theorem B61138475 : Blo 1674037 61138475 := bstep (se 1 (by rfl) ⟨45853856, by rfl⟩ : syracuseStep 61138475 = 91707713) B91707713
theorem B2385607 : Blo 1674037 2385607 := bstep (se 1 (by rfl) ⟨1789205, by rfl⟩ : syracuseStep 2385607 = 3578411) B3578411
theorem B5654231 : Blo 1674037 5654231 := bstep (se 1 (by rfl) ⟨4240673, by rfl⟩ : syracuseStep 5654231 = 8481347) B8481347
theorem B18106105 : Blo 1674037 18106105 := bstep (se 2 (by rfl) ⟨6789789, by rfl⟩ : syracuseStep 18106105 = 13579579) B13579579
theorem B25790201 : Blo 1674037 25790201 := bstep (se 2 (by rfl) ⟨9671325, by rfl⟩ : syracuseStep 25790201 = 19342651) B19342651
theorem B3770207 : Blo 1674037 3770207 := bstep (se 1 (by rfl) ⟨2827655, by rfl⟩ : syracuseStep 3770207 = 5655311) B5655311
theorem B6358945 : Blo 1674037 6358945 := bstep (se 2 (by rfl) ⟨2384604, by rfl⟩ : syracuseStep 6358945 = 4769209) B4769209
theorem B4769711 : Blo 1674037 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B5654447 : Blo 1674037 5654447 := bstep (se 1 (by rfl) ⟨4240835, by rfl⟩ : syracuseStep 5654447 = 8481671) B8481671
theorem B8480699 : Blo 1674037 8480699 := bstep (se 1 (by rfl) ⟨6360524, by rfl⟩ : syracuseStep 8480699 = 12721049) B12721049
theorem B3180475 : Blo 1674037 3180475 := bstep (se 1 (by rfl) ⟨2385356, by rfl⟩ : syracuseStep 3180475 = 4770713) B4770713
theorem B5367809 : Blo 1674037 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B2828297 : Blo 1674037 2828297 := bstep (se 2 (by rfl) ⟨1060611, by rfl⟩ : syracuseStep 2828297 = 2121223) B2121223
theorem B3770387 : Blo 1674037 3770387 := bstep (se 1 (by rfl) ⟨2827790, by rfl⟩ : syracuseStep 3770387 = 5655581) B5655581
theorem B12716189 : Blo 1674037 12716189 := bstep (se 3 (by rfl) ⟨2384285, by rfl⟩ : syracuseStep 12716189 = 4768571) B4768571
theorem B14313779 : Blo 1674037 14313779 := bstep (se 1 (by rfl) ⟨10735334, by rfl⟩ : syracuseStep 14313779 = 21470669) B21470669
theorem B3770729 : Blo 1674037 3770729 := bstep (se 2 (by rfl) ⟨1414023, by rfl⟩ : syracuseStep 3770729 = 2828047) B2828047
theorem B4237697 : Blo 1674037 4237697 := bstep (se 2 (by rfl) ⟨1589136, by rfl⟩ : syracuseStep 4237697 = 3178273) B3178273
theorem B3180961 : Blo 1674037 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B3017339 : Blo 1674037 3017339 := bstep (se 1 (by rfl) ⟨2263004, by rfl⟩ : syracuseStep 3017339 = 4526009) B4526009
theorem B1788539 : Blo 1674037 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B2681515 : Blo 1674037 2681515 := bstep (se 1 (by rfl) ⟨2011136, by rfl⟩ : syracuseStep 2681515 = 4022273) B4022273
theorem B13576889 : Blo 1674037 13576889 := bstep (se 2 (by rfl) ⟨5091333, by rfl⟩ : syracuseStep 13576889 = 10182667) B10182667
theorem B12724937 : Blo 1674037 12724937 := bstep (se 2 (by rfl) ⟨4771851, by rfl⟩ : syracuseStep 12724937 = 9543703) B9543703
theorem B4238153 : Blo 1674037 4238153 := bstep (se 2 (by rfl) ⟨1589307, by rfl⟩ : syracuseStep 4238153 = 3178615) B3178615
theorem B1674063 : Blo 1674037 1674063 := bstep (se 1 (by rfl) ⟨1255547, by rfl⟩ : syracuseStep 1674063 = 2511095) B2511095
theorem B1674079 : Blo 1674037 1674079 := bstep (se 1 (by rfl) ⟨1255559, by rfl⟩ : syracuseStep 1674079 = 2511119) B2511119
theorem B6359903 : Blo 1674037 6359903 := bstep (se 1 (by rfl) ⟨4769927, by rfl⟩ : syracuseStep 6359903 = 9539855) B9539855
theorem B4770667 : Blo 1674037 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B6359917 : Blo 1674037 6359917 := bstep (se 3 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 6359917 = 2384969) B2384969
theorem B1674107 : Blo 1674037 1674107 := bstep (se 1 (by rfl) ⟨1255580, by rfl⟩ : syracuseStep 1674107 = 2511161) B2511161
theorem B1674159 : Blo 1674037 1674159 := bstep (se 1 (by rfl) ⟨1255619, by rfl⟩ : syracuseStep 1674159 = 2511239) B2511239
theorem B1674183 : Blo 1674037 1674183 := bstep (se 1 (by rfl) ⟨1255637, by rfl⟩ : syracuseStep 1674183 = 2511275) B2511275
theorem B1674203 : Blo 1674037 1674203 := bstep (se 1 (by rfl) ⟨1255652, by rfl⟩ : syracuseStep 1674203 = 2511305) B2511305
theorem B3181531 : Blo 1674037 3181531 := bstep (se 1 (by rfl) ⟨2386148, by rfl⟩ : syracuseStep 3181531 = 4772297) B4772297
theorem B1674279 : Blo 1674037 1674279 := bstep (se 1 (by rfl) ⟨1255709, by rfl⟩ : syracuseStep 1674279 = 2511419) B2511419
theorem B3017785 : Blo 1674037 3017785 := bstep (se 2 (by rfl) ⟨1131669, by rfl⟩ : syracuseStep 3017785 = 2263339) B2263339
theorem B1674319 : Blo 1674037 1674319 := bstep (se 1 (by rfl) ⟨1255739, by rfl⟩ : syracuseStep 1674319 = 2511479) B2511479
theorem B4770895 : Blo 1674037 4770895 := bstep (se 1 (by rfl) ⟨3578171, by rfl⟩ : syracuseStep 4770895 = 7156343) B7156343
theorem B1674335 : Blo 1674037 1674335 := bstep (se 1 (by rfl) ⟨1255751, by rfl⟩ : syracuseStep 1674335 = 2511503) B2511503
theorem B1674363 : Blo 1674037 1674363 := bstep (se 1 (by rfl) ⟨1255772, by rfl⟩ : syracuseStep 1674363 = 2511545) B2511545
theorem B6360221 : Blo 1674037 6360221 := bstep (se 3 (by rfl) ⟨1192541, by rfl⟩ : syracuseStep 6360221 = 2385083) B2385083
theorem B4238507 : Blo 1674037 4238507 := bstep (se 1 (by rfl) ⟨3178880, by rfl⟩ : syracuseStep 4238507 = 6357761) B6357761
theorem B1674415 : Blo 1674037 1674415 := bstep (se 1 (by rfl) ⟨1255811, by rfl⟩ : syracuseStep 1674415 = 2511623) B2511623
theorem B8047811 : Blo 1674037 8047811 := bstep (se 1 (by rfl) ⟨6035858, by rfl⟩ : syracuseStep 8047811 = 12071717) B12071717
theorem B1674439 : Blo 1674037 1674439 := bstep (se 1 (by rfl) ⟨1255829, by rfl⟩ : syracuseStep 1674439 = 2511659) B2511659
theorem B8481995 : Blo 1674037 8481995 := bstep (se 1 (by rfl) ⟨6361496, by rfl⟩ : syracuseStep 8481995 = 12722993) B12722993
theorem B1674459 : Blo 1674037 1674459 := bstep (se 1 (by rfl) ⟨1255844, by rfl⟩ : syracuseStep 1674459 = 2511689) B2511689
theorem B1674535 : Blo 1674037 1674535 := bstep (se 1 (by rfl) ⟨1255901, by rfl⟩ : syracuseStep 1674535 = 2511803) B2511803
theorem B1674575 : Blo 1674037 1674575 := bstep (se 1 (by rfl) ⟨1255931, by rfl⟩ : syracuseStep 1674575 = 2511863) B2511863
theorem B1674591 : Blo 1674037 1674591 := bstep (se 1 (by rfl) ⟨1255943, by rfl⟩ : syracuseStep 1674591 = 2511887) B2511887
theorem B1674619 : Blo 1674037 1674619 := bstep (se 1 (by rfl) ⟨1255964, by rfl⟩ : syracuseStep 1674619 = 2511929) B2511929
theorem B1674671 : Blo 1674037 1674671 := bstep (se 1 (by rfl) ⟨1256003, by rfl⟩ : syracuseStep 1674671 = 2512007) B2512007
theorem B1674695 : Blo 1674037 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B1674715 : Blo 1674037 1674715 := bstep (se 1 (by rfl) ⟨1256036, by rfl⟩ : syracuseStep 1674715 = 2512073) B2512073
theorem B3575335 : Blo 1674037 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1674791 : Blo 1674037 1674791 := bstep (se 1 (by rfl) ⟨1256093, by rfl⟩ : syracuseStep 1674791 = 2512187) B2512187
theorem B1674831 : Blo 1674037 1674831 := bstep (se 1 (by rfl) ⟨1256123, by rfl⟩ : syracuseStep 1674831 = 2512247) B2512247
theorem B1674847 : Blo 1674037 1674847 := bstep (se 1 (by rfl) ⟨1256135, by rfl⟩ : syracuseStep 1674847 = 2512271) B2512271
theorem B1674875 : Blo 1674037 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B1674927 : Blo 1674037 1674927 := bstep (se 1 (by rfl) ⟨1256195, by rfl⟩ : syracuseStep 1674927 = 2512391) B2512391
theorem B1674951 : Blo 1674037 1674951 := bstep (se 1 (by rfl) ⟨1256213, by rfl⟩ : syracuseStep 1674951 = 2512427) B2512427
theorem B1674971 : Blo 1674037 1674971 := bstep (se 1 (by rfl) ⟨1256228, by rfl⟩ : syracuseStep 1674971 = 2512457) B2512457
theorem B1675047 : Blo 1674037 1675047 := bstep (se 1 (by rfl) ⟨1256285, by rfl⟩ : syracuseStep 1675047 = 2512571) B2512571
theorem B6360875 : Blo 1674037 6360875 := bstep (se 1 (by rfl) ⟨4770656, by rfl⟩ : syracuseStep 6360875 = 9541313) B9541313
theorem B1675087 : Blo 1674037 1675087 := bstep (se 1 (by rfl) ⟨1256315, by rfl⟩ : syracuseStep 1675087 = 2512631) B2512631
theorem B1675103 : Blo 1674037 1675103 := bstep (se 1 (by rfl) ⟨1256327, by rfl⟩ : syracuseStep 1675103 = 2512655) B2512655
theorem B1675131 : Blo 1674037 1675131 := bstep (se 1 (by rfl) ⟨1256348, by rfl⟩ : syracuseStep 1675131 = 2512697) B2512697
theorem B12078983 : Blo 1674037 12078983 := bstep (se 1 (by rfl) ⟨9059237, by rfl⟩ : syracuseStep 12078983 = 18118475) B18118475
theorem B1675183 : Blo 1674037 1675183 := bstep (se 1 (by rfl) ⟨1256387, by rfl⟩ : syracuseStep 1675183 = 2512775) B2512775
theorem B4239287 : Blo 1674037 4239287 := bstep (se 1 (by rfl) ⟨3179465, by rfl⟩ : syracuseStep 4239287 = 6358931) B6358931
theorem B3223483 : Blo 1674037 3223483 := bstep (se 1 (by rfl) ⟨2417612, by rfl⟩ : syracuseStep 3223483 = 4835225) B4835225
theorem B1675207 : Blo 1674037 1675207 := bstep (se 1 (by rfl) ⟨1256405, by rfl⟩ : syracuseStep 1675207 = 2512811) B2512811
theorem B1675227 : Blo 1674037 1675227 := bstep (se 1 (by rfl) ⟨1256420, by rfl⟩ : syracuseStep 1675227 = 2512841) B2512841
theorem B1675303 : Blo 1674037 1675303 := bstep (se 1 (by rfl) ⟨1256477, by rfl⟩ : syracuseStep 1675303 = 2512955) B2512955
theorem B42922061 : Blo 1674037 42922061 := bstep (se 3 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 42922061 = 16095773) B16095773
theorem B1675343 : Blo 1674037 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1675359 : Blo 1674037 1675359 := bstep (se 1 (by rfl) ⟨1256519, by rfl⟩ : syracuseStep 1675359 = 2513039) B2513039
theorem B6033523 : Blo 1674037 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B1675387 : Blo 1674037 1675387 := bstep (se 1 (by rfl) ⟨1256540, by rfl⟩ : syracuseStep 1675387 = 2513081) B2513081
theorem B1675439 : Blo 1674037 1675439 := bstep (se 1 (by rfl) ⟨1256579, by rfl⟩ : syracuseStep 1675439 = 2513159) B2513159
theorem B1675463 : Blo 1674037 1675463 := bstep (se 1 (by rfl) ⟨1256597, by rfl⟩ : syracuseStep 1675463 = 2513195) B2513195
theorem B1675483 : Blo 1674037 1675483 := bstep (se 1 (by rfl) ⟨1256612, by rfl⟩ : syracuseStep 1675483 = 2513225) B2513225
theorem B1675559 : Blo 1674037 1675559 := bstep (se 1 (by rfl) ⟨1256669, by rfl⟩ : syracuseStep 1675559 = 2513339) B2513339
theorem B1675599 : Blo 1674037 1675599 := bstep (se 1 (by rfl) ⟨1256699, by rfl⟩ : syracuseStep 1675599 = 2513399) B2513399
theorem B1675615 : Blo 1674037 1675615 := bstep (se 1 (by rfl) ⟨1256711, by rfl⟩ : syracuseStep 1675615 = 2513423) B2513423
theorem B2511209 : Blo 1674037 2511209 := bstep (se 2 (by rfl) ⟨941703, by rfl⟩ : syracuseStep 2511209 = 1883407) B1883407
theorem B1675643 : Blo 1674037 1675643 := bstep (se 1 (by rfl) ⟨1256732, by rfl⟩ : syracuseStep 1675643 = 2513465) B2513465
theorem B1675695 : Blo 1674037 1675695 := bstep (se 1 (by rfl) ⟨1256771, by rfl⟩ : syracuseStep 1675695 = 2513543) B2513543
theorem B2511287 : Blo 1674037 2511287 := bstep (se 1 (by rfl) ⟨1883465, by rfl⟩ : syracuseStep 2511287 = 3766931) B3766931
theorem B1675719 : Blo 1674037 1675719 := bstep (se 1 (by rfl) ⟨1256789, by rfl⟩ : syracuseStep 1675719 = 2513579) B2513579
theorem B21475793 : Blo 1674037 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B2511323 : Blo 1674037 2511323 := bstep (se 1 (by rfl) ⟨1883492, by rfl⟩ : syracuseStep 2511323 = 3766985) B3766985
theorem B1675739 : Blo 1674037 1675739 := bstep (se 1 (by rfl) ⟨1256804, by rfl⟩ : syracuseStep 1675739 = 2513609) B2513609
theorem B4026905 : Blo 1674037 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B1675815 : Blo 1674037 1675815 := bstep (se 1 (by rfl) ⟨1256861, by rfl⟩ : syracuseStep 1675815 = 2513723) B2513723
theorem B1675855 : Blo 1674037 1675855 := bstep (se 1 (by rfl) ⟨1256891, by rfl⟩ : syracuseStep 1675855 = 2513783) B2513783
theorem B1675871 : Blo 1674037 1675871 := bstep (se 1 (by rfl) ⟨1256903, by rfl⟩ : syracuseStep 1675871 = 2513807) B2513807
theorem B1675899 : Blo 1674037 1675899 := bstep (se 1 (by rfl) ⟨1256924, by rfl⟩ : syracuseStep 1675899 = 2513849) B2513849
theorem B1675951 : Blo 1674037 1675951 := bstep (se 1 (by rfl) ⟨1256963, by rfl⟩ : syracuseStep 1675951 = 2513927) B2513927
theorem B1675975 : Blo 1674037 1675975 := bstep (se 1 (by rfl) ⟨1256981, by rfl⟩ : syracuseStep 1675975 = 2513963) B2513963
theorem B1675995 : Blo 1674037 1675995 := bstep (se 1 (by rfl) ⟨1256996, by rfl⟩ : syracuseStep 1675995 = 2513993) B2513993
theorem B14504777 : Blo 1674037 14504777 := bstep (se 2 (by rfl) ⟨5439291, by rfl⟩ : syracuseStep 14504777 = 10878583) B10878583
theorem B3576737 : Blo 1674037 3576737 := bstep (se 2 (by rfl) ⟨1341276, by rfl⟩ : syracuseStep 3576737 = 2682553) B2682553
theorem B4240289 : Blo 1674037 4240289 := bstep (se 2 (by rfl) ⟨1590108, by rfl⟩ : syracuseStep 4240289 = 3180217) B3180217
theorem B5436335 : Blo 1674037 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B2511791 : Blo 1674037 2511791 := bstep (se 1 (by rfl) ⟨1883843, by rfl⟩ : syracuseStep 2511791 = 3767687) B3767687
theorem B12719105 : Blo 1674037 12719105 := bstep (se 2 (by rfl) ⟨4769664, by rfl⟩ : syracuseStep 12719105 = 9539329) B9539329
theorem B2511881 : Blo 1674037 2511881 := bstep (se 2 (by rfl) ⟨941955, by rfl⟩ : syracuseStep 2511881 = 1883911) B1883911
theorem B2511911 : Blo 1674037 2511911 := bstep (se 1 (by rfl) ⟨1883933, by rfl⟩ : syracuseStep 2511911 = 3767867) B3767867
theorem B3019855 : Blo 1674037 3019855 := bstep (se 1 (by rfl) ⟨2264891, by rfl⟩ : syracuseStep 3019855 = 4529783) B4529783
theorem B2511995 : Blo 1674037 2511995 := bstep (se 1 (by rfl) ⟨1883996, by rfl⟩ : syracuseStep 2511995 = 3767993) B3767993
theorem B2512121 : Blo 1674037 2512121 := bstep (se 2 (by rfl) ⟨942045, by rfl⟩ : syracuseStep 2512121 = 1884091) B1884091
theorem B18101519 : Blo 1674037 18101519 := bstep (se 1 (by rfl) ⟨13576139, by rfl⟩ : syracuseStep 18101519 = 27152279) B27152279
theorem B2512223 : Blo 1674037 2512223 := bstep (se 1 (by rfl) ⟨1884167, by rfl⟩ : syracuseStep 2512223 = 3768335) B3768335
theorem B4240745 : Blo 1674037 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B2512235 : Blo 1674037 2512235 := bstep (se 1 (by rfl) ⟨1884176, by rfl⟩ : syracuseStep 2512235 = 3768353) B3768353
theorem B2512463 : Blo 1674037 2512463 := bstep (se 1 (by rfl) ⟨1884347, by rfl⟩ : syracuseStep 2512463 = 3768695) B3768695
theorem B10729057 : Blo 1674037 10729057 := bstep (se 2 (by rfl) ⟨4023396, by rfl⟩ : syracuseStep 10729057 = 8046793) B8046793
theorem B2684539 : Blo 1674037 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B2512583 : Blo 1674037 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B6362833 : Blo 1674037 6362833 := bstep (se 2 (by rfl) ⟨2386062, by rfl⟩ : syracuseStep 6362833 = 4772125) B4772125
theorem B9058007 : Blo 1674037 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B2512745 : Blo 1674037 2512745 := bstep (se 2 (by rfl) ⟨942279, by rfl⟩ : syracuseStep 2512745 = 1884559) B1884559
theorem B2512823 : Blo 1674037 2512823 := bstep (se 1 (by rfl) ⟨1884617, by rfl⟩ : syracuseStep 2512823 = 3769235) B3769235
theorem B18102209 : Blo 1674037 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B2512859 : Blo 1674037 2512859 := bstep (se 1 (by rfl) ⟨1884644, by rfl⟩ : syracuseStep 2512859 = 3769289) B3769289
theorem B6363137 : Blo 1674037 6363137 := bstep (se 2 (by rfl) ⟨2386176, by rfl⟩ : syracuseStep 6363137 = 4772353) B4772353
theorem B13580291 : Blo 1674037 13580291 := bstep (se 1 (by rfl) ⟨10185218, by rfl⟩ : syracuseStep 13580291 = 20370437) B20370437
theorem B5650451 : Blo 1674037 5650451 := bstep (se 1 (by rfl) ⟨4237838, by rfl⟩ : syracuseStep 5650451 = 8475677) B8475677
theorem B21477433 : Blo 1674037 21477433 := bstep (se 2 (by rfl) ⟨8054037, by rfl⟩ : syracuseStep 21477433 = 16108075) B16108075
theorem B3487915 : Blo 1674037 3487915 := bstep (se 1 (by rfl) ⟨2615936, by rfl⟩ : syracuseStep 3487915 = 5231873) B5231873
theorem B6789367 : Blo 1674037 6789367 := bstep (se 1 (by rfl) ⟨5092025, by rfl⟩ : syracuseStep 6789367 = 10184051) B10184051
theorem B5650775 : Blo 1674037 5650775 := bstep (se 1 (by rfl) ⟨4238081, by rfl⟩ : syracuseStep 5650775 = 8476163) B8476163
theorem B2513327 : Blo 1674037 2513327 := bstep (se 1 (by rfl) ⟨1884995, by rfl⟩ : syracuseStep 2513327 = 3769991) B3769991
theorem B6363593 : Blo 1674037 6363593 := bstep (se 2 (by rfl) ⟨2386347, by rfl⟩ : syracuseStep 6363593 = 4772695) B4772695
theorem B21469643 : Blo 1674037 21469643 := bstep (se 1 (by rfl) ⟨16102232, by rfl⟩ : syracuseStep 21469643 = 32204465) B32204465
theorem B5364233 : Blo 1674037 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B3578377 : Blo 1674037 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B2513417 : Blo 1674037 2513417 := bstep (se 2 (by rfl) ⟨942531, by rfl⟩ : syracuseStep 2513417 = 1885063) B1885063
theorem B4241929 : Blo 1674037 4241929 := bstep (se 2 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 4241929 = 3181447) B3181447
theorem B3766823 : Blo 1674037 3766823 := bstep (se 1 (by rfl) ⟨2825117, by rfl⟩ : syracuseStep 3766823 = 5650235) B5650235
theorem B2865703 : Blo 1674037 2865703 := bstep (se 1 (by rfl) ⟨2149277, by rfl⟩ : syracuseStep 2865703 = 4298555) B4298555
theorem B2513447 : Blo 1674037 2513447 := bstep (se 1 (by rfl) ⟨1885085, by rfl⟩ : syracuseStep 2513447 = 3770171) B3770171
theorem B2513531 : Blo 1674037 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B2513657 : Blo 1674037 2513657 := bstep (se 2 (by rfl) ⟨942621, by rfl⟩ : syracuseStep 2513657 = 1885243) B1885243
theorem B2513759 : Blo 1674037 2513759 := bstep (se 1 (by rfl) ⟨1885319, by rfl⟩ : syracuseStep 2513759 = 3770639) B3770639
theorem B3767147 : Blo 1674037 3767147 := bstep (se 1 (by rfl) ⟨2825360, by rfl⟩ : syracuseStep 3767147 = 5650721) B5650721
theorem B2513771 : Blo 1674037 2513771 := bstep (se 1 (by rfl) ⟨1885328, by rfl⟩ : syracuseStep 2513771 = 3770657) B3770657
theorem B3767201 : Blo 1674037 3767201 := bstep (se 2 (by rfl) ⟨1412700, by rfl⟩ : syracuseStep 3767201 = 2825401) B2825401
theorem B10738615 : Blo 1674037 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B2825273 : Blo 1674037 2825273 := bstep (se 2 (by rfl) ⟨1059477, by rfl⟩ : syracuseStep 2825273 = 2118955) B2118955
theorem B4529209 : Blo 1674037 4529209 := bstep (se 2 (by rfl) ⟨1698453, by rfl⟩ : syracuseStep 4529209 = 3396907) B3396907
theorem B2513999 : Blo 1674037 2513999 := bstep (se 1 (by rfl) ⟨1885499, by rfl⟩ : syracuseStep 2513999 = 3770999) B3770999
theorem B1883335 : Blo 1674037 1883335 := bstep (se 1 (by rfl) ⟨1412501, by rfl⟩ : syracuseStep 1883335 = 2825003) B2825003
theorem B8273099 : Blo 1674037 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B3767543 : Blo 1674037 3767543 := bstep (se 1 (by rfl) ⟨2825657, by rfl⟩ : syracuseStep 3767543 = 5651315) B5651315
theorem B20372771 : Blo 1674037 20372771 := bstep (se 1 (by rfl) ⟨15279578, by rfl⟩ : syracuseStep 20372771 = 30559157) B30559157
theorem B5651855 : Blo 1674037 5651855 := bstep (se 1 (by rfl) ⟨4238891, by rfl⟩ : syracuseStep 5651855 = 8477783) B8477783
theorem B6446479 : Blo 1674037 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B9674149 : Blo 1674037 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B54361529 : Blo 1674037 54361529 := bstep (se 2 (by rfl) ⟨20385573, by rfl⟩ : syracuseStep 54361529 = 40771147) B40771147
theorem B6790601 : Blo 1674037 6790601 := bstep (se 2 (by rfl) ⟨2546475, by rfl⟩ : syracuseStep 6790601 = 5092951) B5092951
theorem B45825601 : Blo 1674037 45825601 := bstep (se 2 (by rfl) ⟨17184600, by rfl⟩ : syracuseStep 45825601 = 34369201) B34369201
theorem B8052347 : Blo 1674037 8052347 := bstep (se 1 (by rfl) ⟨6039260, by rfl⟩ : syracuseStep 8052347 = 12078521) B12078521
theorem B5652179 : Blo 1674037 5652179 := bstep (se 1 (by rfl) ⟨4239134, by rfl⟩ : syracuseStep 5652179 = 8478269) B8478269
theorem B2825975 : Blo 1674037 2825975 := bstep (se 1 (by rfl) ⟨2119481, by rfl⟩ : syracuseStep 2825975 = 4238963) B4238963
theorem B3768137 : Blo 1674037 3768137 := bstep (se 2 (by rfl) ⟨1413051, by rfl⟩ : syracuseStep 3768137 = 2826103) B2826103
theorem B2580331 : Blo 1674037 2580331 := bstep (se 1 (by rfl) ⟨1935248, by rfl⟩ : syracuseStep 2580331 = 3870497) B3870497
theorem B6357001 : Blo 1674037 6357001 := bstep (se 2 (by rfl) ⟨2383875, by rfl⟩ : syracuseStep 6357001 = 4767751) B4767751
theorem B28614707 : Blo 1674037 28614707 := bstep (se 1 (by rfl) ⟨21461030, by rfl⟩ : syracuseStep 28614707 = 42922061) B42922061
theorem B3768425 : Blo 1674037 3768425 := bstep (se 2 (by rfl) ⟨1413159, by rfl⟩ : syracuseStep 3768425 = 2826319) B2826319
theorem B8044697 : Blo 1674037 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B1884379 : Blo 1674037 1884379 := bstep (se 1 (by rfl) ⟨1413284, by rfl⟩ : syracuseStep 1884379 = 2826569) B2826569
theorem B9052489 : Blo 1674037 9052489 := bstep (se 2 (by rfl) ⟨3394683, by rfl⟩ : syracuseStep 9052489 = 6789367) B6789367
theorem B5652827 : Blo 1674037 5652827 := bstep (se 1 (by rfl) ⟨4239620, by rfl⟩ : syracuseStep 5652827 = 8479241) B8479241
theorem B3178919 : Blo 1674037 3178919 := bstep (se 1 (by rfl) ⟨2384189, by rfl⟩ : syracuseStep 3178919 = 4768379) B4768379
theorem B6357473 : Blo 1674037 6357473 := bstep (se 2 (by rfl) ⟨2384052, by rfl⟩ : syracuseStep 6357473 = 4768105) B4768105
theorem B1884667 : Blo 1674037 1884667 := bstep (se 1 (by rfl) ⟨1413500, by rfl⟩ : syracuseStep 1884667 = 2827001) B2827001
theorem B3768911 : Blo 1674037 3768911 := bstep (se 1 (by rfl) ⟨2826683, by rfl⟩ : syracuseStep 3768911 = 5653367) B5653367
theorem B2384491 : Blo 1674037 2384491 := bstep (se 1 (by rfl) ⟨1788368, by rfl⟩ : syracuseStep 2384491 = 3576737) B3576737
theorem B2826859 : Blo 1674037 2826859 := bstep (se 1 (by rfl) ⟨2120144, by rfl⟩ : syracuseStep 2826859 = 4240289) B4240289
theorem B8479403 : Blo 1674037 8479403 := bstep (se 1 (by rfl) ⟨6359552, by rfl⟩ : syracuseStep 8479403 = 12719105) B12719105
theorem B1884847 : Blo 1674037 1884847 := bstep (se 1 (by rfl) ⟨1413635, by rfl⟩ : syracuseStep 1884847 = 2827271) B2827271
theorem B105972425 : Blo 1674037 105972425 := bstep (se 2 (by rfl) ⟨39739659, by rfl⟩ : syracuseStep 105972425 = 79479319) B79479319
theorem B3769055 : Blo 1674037 3769055 := bstep (se 1 (by rfl) ⟨2826791, by rfl⟩ : syracuseStep 3769055 = 5653583) B5653583
theorem B12067679 : Blo 1674037 12067679 := bstep (se 1 (by rfl) ⟨9050759, by rfl⟩ : syracuseStep 12067679 = 18101519) B18101519
theorem B2827163 : Blo 1674037 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B1885135 : Blo 1674037 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B3769307 : Blo 1674037 3769307 := bstep (se 1 (by rfl) ⟨2826980, by rfl⟩ : syracuseStep 3769307 = 5653961) B5653961
theorem B10191835 : Blo 1674037 10191835 := bstep (se 1 (by rfl) ⟨7643876, by rfl⟩ : syracuseStep 10191835 = 15287753) B15287753
theorem B19072097 : Blo 1674037 19072097 := bstep (se 2 (by rfl) ⟨7152036, by rfl⟩ : syracuseStep 19072097 = 14304073) B14304073
theorem B3769487 : Blo 1674037 3769487 := bstep (se 1 (by rfl) ⟨2827115, by rfl⟩ : syracuseStep 3769487 = 5654231) B5654231
theorem B8479889 : Blo 1674037 8479889 := bstep (se 2 (by rfl) ⟨3179958, by rfl⟩ : syracuseStep 8479889 = 6359917) B6359917
theorem B3769577 : Blo 1674037 3769577 := bstep (se 2 (by rfl) ⟨1413591, by rfl⟩ : syracuseStep 3769577 = 2827183) B2827183
theorem B3179807 : Blo 1674037 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B3769631 : Blo 1674037 3769631 := bstep (se 1 (by rfl) ⟨2827223, by rfl⟩ : syracuseStep 3769631 = 5654447) B5654447
theorem B5653799 : Blo 1674037 5653799 := bstep (se 1 (by rfl) ⟨4240349, by rfl⟩ : syracuseStep 5653799 = 8480699) B8480699
theorem B9053527 : Blo 1674037 9053527 := bstep (se 1 (by rfl) ⟨6790145, by rfl⟩ : syracuseStep 9053527 = 13580291) B13580291
theorem B1885531 : Blo 1674037 1885531 := bstep (se 1 (by rfl) ⟨1414148, by rfl⟩ : syracuseStep 1885531 = 2828297) B2828297
theorem B4023713 : Blo 1674037 4023713 := bstep (se 2 (by rfl) ⟨1508892, by rfl⟩ : syracuseStep 4023713 = 3017785) B3017785
theorem B6038945 : Blo 1674037 6038945 := bstep (se 2 (by rfl) ⟨2264604, by rfl⟩ : syracuseStep 6038945 = 4529209) B4529209
theorem B14313095 : Blo 1674037 14313095 := bstep (se 1 (by rfl) ⟨10734821, by rfl⟩ : syracuseStep 14313095 = 21469643) B21469643
theorem B4769437 : Blo 1674037 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B3770153 : Blo 1674037 3770153 := bstep (se 2 (by rfl) ⟨1413807, by rfl⟩ : syracuseStep 3770153 = 2827615) B2827615
theorem B8595305 : Blo 1674037 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B14305409 : Blo 1674037 14305409 := bstep (se 2 (by rfl) ⟨5364528, by rfl⟩ : syracuseStep 14305409 = 10729057) B10729057
theorem B5654663 : Blo 1674037 5654663 := bstep (se 1 (by rfl) ⟨4240997, by rfl⟩ : syracuseStep 5654663 = 8481995) B8481995
theorem B5515399 : Blo 1674037 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B3180809 : Blo 1674037 3180809 := bstep (se 2 (by rfl) ⟨1192803, by rfl⟩ : syracuseStep 3180809 = 2385607) B2385607
theorem B5368231 : Blo 1674037 5368231 := bstep (se 1 (by rfl) ⟨4026173, by rfl⟩ : syracuseStep 5368231 = 8052347) B8052347
theorem B14314157 : Blo 1674037 14314157 := bstep (se 3 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 14314157 = 5367809) B5367809
theorem B8596243 : Blo 1674037 8596243 := bstep (se 1 (by rfl) ⟨6447182, by rfl⟩ : syracuseStep 8596243 = 12894365) B12894365
theorem B1674139 : Blo 1674037 1674139 := bstep (se 1 (by rfl) ⟨1255604, by rfl⟩ : syracuseStep 1674139 = 2511209) B2511209
theorem B1674191 : Blo 1674037 1674191 := bstep (se 1 (by rfl) ⟨1255643, by rfl⟩ : syracuseStep 1674191 = 2511287) B2511287
theorem B1674215 : Blo 1674037 1674215 := bstep (se 1 (by rfl) ⟨1255661, by rfl⟩ : syracuseStep 1674215 = 2511323) B2511323
theorem B10726415 : Blo 1674037 10726415 := bstep (se 1 (by rfl) ⟨8044811, by rfl⟩ : syracuseStep 10726415 = 16089623) B16089623
theorem B9669851 : Blo 1674037 9669851 := bstep (se 1 (by rfl) ⟨7252388, by rfl⟩ : syracuseStep 9669851 = 14504777) B14504777
theorem B5369051 : Blo 1674037 5369051 := bstep (se 1 (by rfl) ⟨4026788, by rfl⟩ : syracuseStep 5369051 = 8053577) B8053577
theorem B2682143 : Blo 1674037 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B1674527 : Blo 1674037 1674527 := bstep (se 1 (by rfl) ⟨1255895, by rfl⟩ : syracuseStep 1674527 = 2511791) B2511791
theorem B1674587 : Blo 1674037 1674587 := bstep (se 1 (by rfl) ⟨1255940, by rfl⟩ : syracuseStep 1674587 = 2511881) B2511881
theorem B4238689 : Blo 1674037 4238689 := bstep (se 2 (by rfl) ⟨1589508, by rfl⟩ : syracuseStep 4238689 = 3179017) B3179017
theorem B4771169 : Blo 1674037 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B5655905 : Blo 1674037 5655905 := bstep (se 2 (by rfl) ⟨2120964, by rfl⟩ : syracuseStep 5655905 = 4241929) B4241929
theorem B1674607 : Blo 1674037 1674607 := bstep (se 1 (by rfl) ⟨1255955, by rfl⟩ : syracuseStep 1674607 = 2511911) B2511911
theorem B3820937 : Blo 1674037 3820937 := bstep (se 2 (by rfl) ⟨1432851, by rfl⟩ : syracuseStep 3820937 = 2865703) B2865703
theorem B1674663 : Blo 1674037 1674663 := bstep (se 1 (by rfl) ⟨1255997, by rfl⟩ : syracuseStep 1674663 = 2511995) B2511995
theorem B15707611 : Blo 1674037 15707611 := bstep (se 1 (by rfl) ⟨11780708, by rfl⟩ : syracuseStep 15707611 = 23561417) B23561417
theorem B1674747 : Blo 1674037 1674747 := bstep (se 1 (by rfl) ⟨1256060, by rfl⟩ : syracuseStep 1674747 = 2512121) B2512121
theorem B9055759 : Blo 1674037 9055759 := bstep (se 1 (by rfl) ⟨6791819, by rfl⟩ : syracuseStep 9055759 = 13583639) B13583639
theorem B8482319 : Blo 1674037 8482319 := bstep (se 1 (by rfl) ⟨6361739, by rfl⟩ : syracuseStep 8482319 = 12723479) B12723479
theorem B3575353 : Blo 1674037 3575353 := bstep (se 2 (by rfl) ⟨1340757, by rfl⟩ : syracuseStep 3575353 = 2681515) B2681515
theorem B1674815 : Blo 1674037 1674815 := bstep (se 1 (by rfl) ⟨1256111, by rfl⟩ : syracuseStep 1674815 = 2512223) B2512223
theorem B1674823 : Blo 1674037 1674823 := bstep (se 1 (by rfl) ⟨1256117, by rfl⟩ : syracuseStep 1674823 = 2512235) B2512235
theorem B40758983 : Blo 1674037 40758983 := bstep (se 1 (by rfl) ⟨30569237, by rfl⟩ : syracuseStep 40758983 = 61138475) B61138475
theorem B1674975 : Blo 1674037 1674975 := bstep (se 1 (by rfl) ⟨1256231, by rfl⟩ : syracuseStep 1674975 = 2512463) B2512463
theorem B1675055 : Blo 1674037 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B6360889 : Blo 1674037 6360889 := bstep (se 2 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 6360889 = 4770667) B4770667
theorem B18108269 : Blo 1674037 18108269 := bstep (se 3 (by rfl) ⟨3395300, by rfl⟩ : syracuseStep 18108269 = 6790601) B6790601
theorem B1675163 : Blo 1674037 1675163 := bstep (se 1 (by rfl) ⟨1256372, by rfl⟩ : syracuseStep 1675163 = 2512745) B2512745
theorem B1675215 : Blo 1674037 1675215 := bstep (se 1 (by rfl) ⟨1256411, by rfl⟩ : syracuseStep 1675215 = 2512823) B2512823
theorem B1675239 : Blo 1674037 1675239 := bstep (se 1 (by rfl) ⟨1256429, by rfl⟩ : syracuseStep 1675239 = 2512859) B2512859
theorem B6361193 : Blo 1674037 6361193 := bstep (se 2 (by rfl) ⟨2385447, by rfl⟩ : syracuseStep 6361193 = 4770895) B4770895
theorem B4026473 : Blo 1674037 4026473 := bstep (se 2 (by rfl) ⟨1509927, by rfl⟩ : syracuseStep 4026473 = 3019855) B3019855
theorem B2511113 : Blo 1674037 2511113 := bstep (se 2 (by rfl) ⟨941667, by rfl⟩ : syracuseStep 2511113 = 1883335) B1883335
theorem B4239641 : Blo 1674037 4239641 := bstep (se 2 (by rfl) ⟨1589865, by rfl⟩ : syracuseStep 4239641 = 3179731) B3179731
theorem B1675551 : Blo 1674037 1675551 := bstep (se 1 (by rfl) ⟨1256663, by rfl⟩ : syracuseStep 1675551 = 2513327) B2513327
theorem B3576155 : Blo 1674037 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B1675611 : Blo 1674037 1675611 := bstep (se 1 (by rfl) ⟨1256708, by rfl⟩ : syracuseStep 1675611 = 2513417) B2513417
theorem B2511215 : Blo 1674037 2511215 := bstep (se 1 (by rfl) ⟨1883411, by rfl⟩ : syracuseStep 2511215 = 3766823) B3766823
theorem B1675631 : Blo 1674037 1675631 := bstep (se 1 (by rfl) ⟨1256723, by rfl⟩ : syracuseStep 1675631 = 2513447) B2513447
theorem B2011559 : Blo 1674037 2011559 := bstep (se 1 (by rfl) ⟨1508669, by rfl⟩ : syracuseStep 2011559 = 3017339) B3017339
theorem B1675687 : Blo 1674037 1675687 := bstep (se 1 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 1675687 = 2513531) B2513531
theorem B8483291 : Blo 1674037 8483291 := bstep (se 1 (by rfl) ⟨6362468, by rfl⟩ : syracuseStep 8483291 = 12724937) B12724937
theorem B1675771 : Blo 1674037 1675771 := bstep (se 1 (by rfl) ⟨1256828, by rfl⟩ : syracuseStep 1675771 = 2513657) B2513657
theorem B12898865 : Blo 1674037 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B24154685 : Blo 1674037 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B4239935 : Blo 1674037 4239935 := bstep (se 1 (by rfl) ⟨3179951, by rfl⟩ : syracuseStep 4239935 = 6359903) B6359903
theorem B1675839 : Blo 1674037 1675839 := bstep (se 1 (by rfl) ⟨1256879, by rfl⟩ : syracuseStep 1675839 = 2513759) B2513759
theorem B2511431 : Blo 1674037 2511431 := bstep (se 1 (by rfl) ⟨1883573, by rfl⟩ : syracuseStep 2511431 = 3767147) B3767147
theorem B1675847 : Blo 1674037 1675847 := bstep (se 1 (by rfl) ⟨1256885, by rfl⟩ : syracuseStep 1675847 = 2513771) B2513771
theorem B12726881 : Blo 1674037 12726881 := bstep (se 2 (by rfl) ⟨4772580, by rfl⟩ : syracuseStep 12726881 = 9545161) B9545161
theorem B2511467 : Blo 1674037 2511467 := bstep (se 1 (by rfl) ⟨1883600, by rfl⟩ : syracuseStep 2511467 = 3767201) B3767201
theorem B1675999 : Blo 1674037 1675999 := bstep (se 1 (by rfl) ⟨1256999, by rfl⟩ : syracuseStep 1675999 = 2513999) B2513999
theorem B61100801 : Blo 1674037 61100801 := bstep (se 2 (by rfl) ⟨22912800, by rfl⟩ : syracuseStep 61100801 = 45825601) B45825601
theorem B4240147 : Blo 1674037 4240147 := bstep (se 1 (by rfl) ⟨3180110, by rfl⟩ : syracuseStep 4240147 = 6360221) B6360221
theorem B2511695 : Blo 1674037 2511695 := bstep (se 1 (by rfl) ⟨1883771, by rfl⟩ : syracuseStep 2511695 = 3767543) B3767543
theorem B8483777 : Blo 1674037 8483777 := bstep (se 2 (by rfl) ⟨3181416, by rfl⟩ : syracuseStep 8483777 = 6362833) B6362833
theorem B17191909 : Blo 1674037 17191909 := bstep (se 4 (by rfl) ⟨1611741, by rfl⟩ : syracuseStep 17191909 = 3223483) B3223483
theorem B14496893 : Blo 1674037 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B54310013 : Blo 1674037 54310013 := bstep (se 3 (by rfl) ⟨10183127, by rfl⟩ : syracuseStep 54310013 = 20366255) B20366255
theorem B48272557 : Blo 1674037 48272557 := bstep (se 3 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 48272557 = 18102209) B18102209
theorem B4240583 : Blo 1674037 4240583 := bstep (se 1 (by rfl) ⟨3180437, by rfl⟩ : syracuseStep 4240583 = 6360875) B6360875
theorem B2512091 : Blo 1674037 2512091 := bstep (se 1 (by rfl) ⟨1884068, by rfl⟩ : syracuseStep 2512091 = 3768137) B3768137
theorem B4240633 : Blo 1674037 4240633 := bstep (se 2 (by rfl) ⟨1590237, by rfl⟩ : syracuseStep 4240633 = 3180475) B3180475
theorem B2512265 : Blo 1674037 2512265 := bstep (se 2 (by rfl) ⟨942099, by rfl⟩ : syracuseStep 2512265 = 1884199) B1884199
theorem B28636577 : Blo 1674037 28636577 := bstep (se 2 (by rfl) ⟨10738716, by rfl⟩ : syracuseStep 28636577 = 21477433) B21477433
theorem B4650553 : Blo 1674037 4650553 := bstep (se 2 (by rfl) ⟨1743957, by rfl⟩ : syracuseStep 4650553 = 3487915) B3487915
theorem B14317195 : Blo 1674037 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B2684603 : Blo 1674037 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B2512619 : Blo 1674037 2512619 := bstep (se 1 (by rfl) ⟨1884464, by rfl⟩ : syracuseStep 2512619 = 3768929) B3768929
theorem B6035255 : Blo 1674037 6035255 := bstep (se 1 (by rfl) ⟨4526441, by rfl⟩ : syracuseStep 6035255 = 9052883) B9052883
theorem B4241281 : Blo 1674037 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B2512847 : Blo 1674037 2512847 := bstep (se 1 (by rfl) ⟨1884635, by rfl⟩ : syracuseStep 2512847 = 3769271) B3769271
theorem B14309405 : Blo 1674037 14309405 := bstep (se 3 (by rfl) ⟨2683013, by rfl⟩ : syracuseStep 14309405 = 5366027) B5366027
theorem B5363977 : Blo 1674037 5363977 := bstep (se 2 (by rfl) ⟨2011491, by rfl⟩ : syracuseStep 5363977 = 4022983) B4022983
theorem B2513243 : Blo 1674037 2513243 := bstep (se 1 (by rfl) ⟨1884932, by rfl⟩ : syracuseStep 2513243 = 3769865) B3769865
theorem B17193467 : Blo 1674037 17193467 := bstep (se 1 (by rfl) ⟨12895100, by rfl⟩ : syracuseStep 17193467 = 25790201) B25790201
theorem B2513471 : Blo 1674037 2513471 := bstep (se 1 (by rfl) ⟨1885103, by rfl⟩ : syracuseStep 2513471 = 3770207) B3770207
theorem B14318153 : Blo 1674037 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B4242041 : Blo 1674037 4242041 := bstep (se 2 (by rfl) ⟨1590765, by rfl⟩ : syracuseStep 4242041 = 3181531) B3181531
theorem B4242091 : Blo 1674037 4242091 := bstep (se 1 (by rfl) ⟨3181568, by rfl⟩ : syracuseStep 4242091 = 6363137) B6363137
theorem B3766967 : Blo 1674037 3766967 := bstep (se 1 (by rfl) ⟨2825225, by rfl⟩ : syracuseStep 3766967 = 5650451) B5650451
theorem B2513591 : Blo 1674037 2513591 := bstep (se 1 (by rfl) ⟨1885193, by rfl⟩ : syracuseStep 2513591 = 3770387) B3770387
theorem B8477459 : Blo 1674037 8477459 := bstep (se 1 (by rfl) ⟨6358094, by rfl⟩ : syracuseStep 8477459 = 12716189) B12716189
theorem B9542519 : Blo 1674037 9542519 := bstep (se 1 (by rfl) ⟨7156889, by rfl⟩ : syracuseStep 9542519 = 14313779) B14313779
theorem B3767183 : Blo 1674037 3767183 := bstep (se 1 (by rfl) ⟨2825387, by rfl⟩ : syracuseStep 3767183 = 5650775) B5650775
theorem B2513819 : Blo 1674037 2513819 := bstep (se 1 (by rfl) ⟨1885364, by rfl⟩ : syracuseStep 2513819 = 3770729) B3770729
theorem B2825131 : Blo 1674037 2825131 := bstep (se 1 (by rfl) ⟨2118848, by rfl⟩ : syracuseStep 2825131 = 4237697) B4237697
theorem B4242395 : Blo 1674037 4242395 := bstep (se 1 (by rfl) ⟨3181796, by rfl⟩ : syracuseStep 4242395 = 6363593) B6363593
theorem B9051259 : Blo 1674037 9051259 := bstep (se 1 (by rfl) ⟨6788444, by rfl⟩ : syracuseStep 9051259 = 13576889) B13576889
theorem B2825435 : Blo 1674037 2825435 := bstep (se 1 (by rfl) ⟨2119076, by rfl⟩ : syracuseStep 2825435 = 4238153) B4238153
theorem B1883515 : Blo 1674037 1883515 := bstep (se 1 (by rfl) ⟨1412636, by rfl⟩ : syracuseStep 1883515 = 2825273) B2825273
theorem B4767113 : Blo 1674037 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B2825671 : Blo 1674037 2825671 := bstep (se 1 (by rfl) ⟨2119253, by rfl⟩ : syracuseStep 2825671 = 4238507) B4238507
theorem B5365207 : Blo 1674037 5365207 := bstep (se 1 (by rfl) ⟨4023905, by rfl⟩ : syracuseStep 5365207 = 8047811) B8047811
theorem B3579385 : Blo 1674037 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B13581847 : Blo 1674037 13581847 := bstep (se 1 (by rfl) ⟨10186385, by rfl⟩ : syracuseStep 13581847 = 20372771) B20372771
theorem B3767903 : Blo 1674037 3767903 := bstep (se 1 (by rfl) ⟨2825927, by rfl⟩ : syracuseStep 3767903 = 5651855) B5651855
theorem B36241019 : Blo 1674037 36241019 := bstep (se 1 (by rfl) ⟨27180764, by rfl⟩ : syracuseStep 36241019 = 54361529) B54361529
theorem B24141473 : Blo 1674037 24141473 := bstep (se 2 (by rfl) ⟨9053052, by rfl⟩ : syracuseStep 24141473 = 18106105) B18106105
theorem B3768119 : Blo 1674037 3768119 := bstep (se 1 (by rfl) ⟨2826089, by rfl⟩ : syracuseStep 3768119 = 5652179) B5652179
theorem B3440441 : Blo 1674037 3440441 := bstep (se 2 (by rfl) ⟨1290165, by rfl⟩ : syracuseStep 3440441 = 2580331) B2580331
theorem B1883983 : Blo 1674037 1883983 := bstep (se 1 (by rfl) ⟨1412987, by rfl⟩ : syracuseStep 1883983 = 2825975) B2825975
theorem B8478593 : Blo 1674037 8478593 := bstep (se 2 (by rfl) ⟨3179472, by rfl⟩ : syracuseStep 8478593 = 6358945) B6358945
theorem B8052655 : Blo 1674037 8052655 := bstep (se 1 (by rfl) ⟨6039491, by rfl⟩ : syracuseStep 8052655 = 12078983) B12078983
theorem B2826191 : Blo 1674037 2826191 := bstep (se 1 (by rfl) ⟨2119643, by rfl⟩ : syracuseStep 2826191 = 4239287) B4239287
theorem B2826427 : Blo 1674037 2826427 := bstep (se 1 (by rfl) ⟨2119820, by rfl⟩ : syracuseStep 2826427 = 4239641) B4239641
theorem B3768551 : Blo 1674037 3768551 := bstep (se 1 (by rfl) ⟨2826413, by rfl⟩ : syracuseStep 3768551 = 5652827) B5652827
theorem B7151969 : Blo 1674037 7151969 := bstep (se 2 (by rfl) ⟨2681988, by rfl⟩ : syracuseStep 7151969 = 5363977) B5363977
theorem B2826623 : Blo 1674037 2826623 := bstep (se 1 (by rfl) ⟨2119967, by rfl⟩ : syracuseStep 2826623 = 4239935) B4239935
theorem B5652935 : Blo 1674037 5652935 := bstep (se 1 (by rfl) ⟨4239701, by rfl⟩ : syracuseStep 5652935 = 8479403) B8479403
theorem B70648283 : Blo 1674037 70648283 := bstep (se 1 (by rfl) ⟨52986212, by rfl⟩ : syracuseStep 70648283 = 105972425) B105972425
theorem B8045119 : Blo 1674037 8045119 := bstep (se 1 (by rfl) ⟨6033839, by rfl⟩ : syracuseStep 8045119 = 12067679) B12067679
theorem B1884775 : Blo 1674037 1884775 := bstep (se 1 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 1884775 = 2827163) B2827163
theorem B12714731 : Blo 1674037 12714731 := bstep (se 1 (by rfl) ⟨9536048, by rfl⟩ : syracuseStep 12714731 = 19072097) B19072097
theorem B5653259 : Blo 1674037 5653259 := bstep (se 1 (by rfl) ⟨4239944, by rfl⟩ : syracuseStep 5653259 = 8479889) B8479889
theorem B2827055 : Blo 1674037 2827055 := bstep (se 1 (by rfl) ⟨2120291, by rfl⟩ : syracuseStep 2827055 = 4240583) B4240583
theorem B3179321 : Blo 1674037 3179321 := bstep (se 2 (by rfl) ⟨1192245, by rfl⟩ : syracuseStep 3179321 = 2384491) B2384491
theorem B3769145 : Blo 1674037 3769145 := bstep (se 2 (by rfl) ⟨1413429, by rfl⟩ : syracuseStep 3769145 = 2826859) B2826859
theorem B3769199 : Blo 1674037 3769199 := bstep (se 1 (by rfl) ⟨2826899, by rfl⟩ : syracuseStep 3769199 = 5653799) B5653799
theorem B9536413 : Blo 1674037 9536413 := bstep (se 3 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 9536413 = 3576155) B3576155
theorem B5653529 : Blo 1674037 5653529 := bstep (se 2 (by rfl) ⟨2120073, by rfl⟩ : syracuseStep 5653529 = 4240147) B4240147
theorem B11461657 : Blo 1674037 11461657 := bstep (se 2 (by rfl) ⟨4298121, by rfl⟩ : syracuseStep 11461657 = 8596243) B8596243
theorem B4023503 : Blo 1674037 4023503 := bstep (se 1 (by rfl) ⟨3017627, by rfl⟩ : syracuseStep 4023503 = 6035255) B6035255
theorem B9536939 : Blo 1674037 9536939 := bstep (se 1 (by rfl) ⟨7152704, by rfl⟩ : syracuseStep 9536939 = 14305409) B14305409
theorem B3769775 : Blo 1674037 3769775 := bstep (se 1 (by rfl) ⟨2827331, by rfl⟩ : syracuseStep 3769775 = 5654663) B5654663
theorem B12068345 : Blo 1674037 12068345 := bstep (se 2 (by rfl) ⟨4525629, by rfl⟩ : syracuseStep 12068345 = 9051259) B9051259
theorem B5654177 : Blo 1674037 5654177 := bstep (se 2 (by rfl) ⟨2120316, by rfl⟩ : syracuseStep 5654177 = 4240633) B4240633
theorem B11462311 : Blo 1674037 11462311 := bstep (se 1 (by rfl) ⟨8596733, by rfl⟩ : syracuseStep 11462311 = 17193467) B17193467
theorem B9545435 : Blo 1674037 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B2828027 : Blo 1674037 2828027 := bstep (se 1 (by rfl) ⟨2121020, by rfl⟩ : syracuseStep 2828027 = 4242041) B4242041
theorem B7153609 : Blo 1674037 7153609 := bstep (se 2 (by rfl) ⟨2682603, by rfl⟩ : syracuseStep 7153609 = 5365207) B5365207
theorem B2828263 : Blo 1674037 2828263 := bstep (se 1 (by rfl) ⟨2121197, by rfl⟩ : syracuseStep 2828263 = 4242395) B4242395
theorem B19089593 : Blo 1674037 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B1788095 : Blo 1674037 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B6359249 : Blo 1674037 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B3180779 : Blo 1674037 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B3770603 : Blo 1674037 3770603 := bstep (se 1 (by rfl) ⟨2827952, by rfl⟩ : syracuseStep 3770603 = 5655905) B5655905
theorem B5654879 : Blo 1674037 5654879 := bstep (se 1 (by rfl) ⟨4241159, by rfl⟩ : syracuseStep 5654879 = 8482319) B8482319
theorem B8481185 : Blo 1674037 8481185 := bstep (se 2 (by rfl) ⟨3180444, by rfl⟩ : syracuseStep 8481185 = 6360889) B6360889
theorem B24160679 : Blo 1674037 24160679 := bstep (se 1 (by rfl) ⟨18120509, by rfl⟩ : syracuseStep 24160679 = 36241019) B36241019
theorem B83773925 : Blo 1674037 83773925 := bstep (se 4 (by rfl) ⟨7853805, by rfl⟩ : syracuseStep 83773925 = 15707611) B15707611
theorem B5655041 : Blo 1674037 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B72436517 : Blo 1674037 72436517 := bstep (se 4 (by rfl) ⟨6790923, by rfl⟩ : syracuseStep 72436517 = 13581847) B13581847
theorem B1674075 : Blo 1674037 1674075 := bstep (se 1 (by rfl) ⟨1255556, by rfl⟩ : syracuseStep 1674075 = 2511113) B2511113
theorem B1674143 : Blo 1674037 1674143 := bstep (se 1 (by rfl) ⟨1255607, by rfl⟩ : syracuseStep 1674143 = 2511215) B2511215
theorem B5655527 : Blo 1674037 5655527 := bstep (se 1 (by rfl) ⟨4241645, by rfl⟩ : syracuseStep 5655527 = 8483291) B8483291
theorem B4238315 : Blo 1674037 4238315 := bstep (se 1 (by rfl) ⟨3178736, by rfl⟩ : syracuseStep 4238315 = 6357473) B6357473
theorem B1674287 : Blo 1674037 1674287 := bstep (se 1 (by rfl) ⟨1255715, by rfl⟩ : syracuseStep 1674287 = 2511431) B2511431
theorem B1674311 : Blo 1674037 1674311 := bstep (se 1 (by rfl) ⟨1255733, by rfl⟩ : syracuseStep 1674311 = 2511467) B2511467
theorem B12069985 : Blo 1674037 12069985 := bstep (se 2 (by rfl) ⟨4526244, by rfl⟩ : syracuseStep 12069985 = 9052489) B9052489
theorem B40733867 : Blo 1674037 40733867 := bstep (se 1 (by rfl) ⟨30550400, by rfl⟩ : syracuseStep 40733867 = 61100801) B61100801
theorem B1674463 : Blo 1674037 1674463 := bstep (se 1 (by rfl) ⟨1255847, by rfl⟩ : syracuseStep 1674463 = 2511695) B2511695
theorem B5655851 : Blo 1674037 5655851 := bstep (se 1 (by rfl) ⟨4241888, by rfl⟩ : syracuseStep 5655851 = 8483777) B8483777
theorem B8482157 : Blo 1674037 8482157 := bstep (se 3 (by rfl) ⟨1590404, by rfl⟩ : syracuseStep 8482157 = 3180809) B3180809
theorem B1674727 : Blo 1674037 1674727 := bstep (se 1 (by rfl) ⟨1256045, by rfl⟩ : syracuseStep 1674727 = 2512091) B2512091
theorem B5656121 : Blo 1674037 5656121 := bstep (se 2 (by rfl) ⟨2121045, by rfl⟩ : syracuseStep 5656121 = 4242091) B4242091
theorem B1674843 : Blo 1674037 1674843 := bstep (se 1 (by rfl) ⟨1256132, by rfl⟩ : syracuseStep 1674843 = 2512265) B2512265
theorem B4025963 : Blo 1674037 4025963 := bstep (se 1 (by rfl) ⟨3019472, by rfl⟩ : syracuseStep 4025963 = 6038945) B6038945
theorem B19091051 : Blo 1674037 19091051 := bstep (se 1 (by rfl) ⟨14318288, by rfl⟩ : syracuseStep 19091051 = 28636577) B28636577
theorem B1675079 : Blo 1674037 1675079 := bstep (se 1 (by rfl) ⟨1256309, by rfl⟩ : syracuseStep 1675079 = 2512619) B2512619
theorem B5730203 : Blo 1674037 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B1675231 : Blo 1674037 1675231 := bstep (se 1 (by rfl) ⟨1256423, by rfl⟩ : syracuseStep 1675231 = 2512847) B2512847
theorem B9539603 : Blo 1674037 9539603 := bstep (se 1 (by rfl) ⟨7154702, by rfl⟩ : syracuseStep 9539603 = 14309405) B14309405
theorem B1675495 : Blo 1674037 1675495 := bstep (se 1 (by rfl) ⟨1256621, by rfl⟩ : syracuseStep 1675495 = 2513243) B2513243
theorem B1675647 : Blo 1674037 1675647 := bstep (se 1 (by rfl) ⟨1256735, by rfl⟩ : syracuseStep 1675647 = 2513471) B2513471
theorem B12071369 : Blo 1674037 12071369 := bstep (se 2 (by rfl) ⟨4526763, by rfl⟩ : syracuseStep 12071369 = 9053527) B9053527
theorem B2511311 : Blo 1674037 2511311 := bstep (se 1 (by rfl) ⟨1883483, by rfl⟩ : syracuseStep 2511311 = 3766967) B3766967
theorem B1675727 : Blo 1674037 1675727 := bstep (se 1 (by rfl) ⟨1256795, by rfl⟩ : syracuseStep 1675727 = 2513591) B2513591
theorem B2511353 : Blo 1674037 2511353 := bstep (se 2 (by rfl) ⟨941757, by rfl⟩ : syracuseStep 2511353 = 1883515) B1883515
theorem B6361679 : Blo 1674037 6361679 := bstep (se 1 (by rfl) ⟨4771259, by rfl⟩ : syracuseStep 6361679 = 9542519) B9542519
theorem B2511455 : Blo 1674037 2511455 := bstep (se 1 (by rfl) ⟨1883591, by rfl⟩ : syracuseStep 2511455 = 3767183) B3767183
theorem B1675879 : Blo 1674037 1675879 := bstep (se 1 (by rfl) ⟨1256909, by rfl⟩ : syracuseStep 1675879 = 2513819) B2513819
theorem B4772513 : Blo 1674037 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B2511935 : Blo 1674037 2511935 := bstep (se 1 (by rfl) ⟨1883951, by rfl⟩ : syracuseStep 2511935 = 3767903) B3767903
theorem B2511977 : Blo 1674037 2511977 := bstep (se 2 (by rfl) ⟨941991, by rfl⟩ : syracuseStep 2511977 = 1883983) B1883983
theorem B16094315 : Blo 1674037 16094315 := bstep (se 1 (by rfl) ⟨12070736, by rfl⟩ : syracuseStep 16094315 = 24141473) B24141473
theorem B91690181 : Blo 1674037 91690181 := bstep (se 4 (by rfl) ⟨8595954, by rfl⟩ : syracuseStep 91690181 = 17191909) B17191909
theorem B2512079 : Blo 1674037 2512079 := bstep (se 1 (by rfl) ⟨1884059, by rfl⟩ : syracuseStep 2512079 = 3768119) B3768119
theorem B10736873 : Blo 1674037 10736873 := bstep (se 2 (by rfl) ⟨4026327, by rfl⟩ : syracuseStep 10736873 = 8052655) B8052655
theorem B12072179 : Blo 1674037 12072179 := bstep (se 1 (by rfl) ⟨9054134, by rfl⟩ : syracuseStep 12072179 = 18108269) B18108269
theorem B8476001 : Blo 1674037 8476001 := bstep (se 2 (by rfl) ⟨3178500, by rfl⟩ : syracuseStep 8476001 = 6357001) B6357001
theorem B19076471 : Blo 1674037 19076471 := bstep (se 1 (by rfl) ⟨14307353, by rfl⟩ : syracuseStep 19076471 = 28614707) B28614707
theorem B2512283 : Blo 1674037 2512283 := bstep (se 1 (by rfl) ⟨1884212, by rfl⟩ : syracuseStep 2512283 = 3768425) B3768425
theorem B4240795 : Blo 1674037 4240795 := bstep (se 1 (by rfl) ⟨3180596, by rfl⟩ : syracuseStep 4240795 = 6361193) B6361193
theorem B2684315 : Blo 1674037 2684315 := bstep (se 1 (by rfl) ⟨2013236, by rfl⟩ : syracuseStep 2684315 = 4026473) B4026473
theorem B7353865 : Blo 1674037 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B2119279 : Blo 1674037 2119279 := bstep (se 1 (by rfl) ⟨1589459, by rfl⟩ : syracuseStep 2119279 = 3178919) B3178919
theorem B2512505 : Blo 1674037 2512505 := bstep (se 2 (by rfl) ⟨942189, by rfl⟩ : syracuseStep 2512505 = 1884379) B1884379
theorem B24802949 : Blo 1674037 24802949 := bstep (se 4 (by rfl) ⟨2325276, by rfl⟩ : syracuseStep 24802949 = 4650553) B4650553
theorem B8599243 : Blo 1674037 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B16103123 : Blo 1674037 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B2512607 : Blo 1674037 2512607 := bstep (se 1 (by rfl) ⟨1884455, by rfl⟩ : syracuseStep 2512607 = 3768911) B3768911
theorem B21452525 : Blo 1674037 21452525 := bstep (se 3 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 21452525 = 8044697) B8044697
theorem B8484587 : Blo 1674037 8484587 := bstep (se 1 (by rfl) ⟨6363440, by rfl⟩ : syracuseStep 8484587 = 12726881) B12726881
theorem B2512703 : Blo 1674037 2512703 := bstep (se 1 (by rfl) ⟨1884527, by rfl⟩ : syracuseStep 2512703 = 3769055) B3769055
theorem B7157641 : Blo 1674037 7157641 := bstep (se 2 (by rfl) ⟨2684115, by rfl⟩ : syracuseStep 7157641 = 5368231) B5368231
theorem B14317469 : Blo 1674037 14317469 := bstep (se 3 (by rfl) ⟨2684525, by rfl⟩ : syracuseStep 14317469 = 5369051) B5369051
theorem B2512871 : Blo 1674037 2512871 := bstep (se 1 (by rfl) ⟨1884653, by rfl⟩ : syracuseStep 2512871 = 3769307) B3769307
theorem B2512889 : Blo 1674037 2512889 := bstep (se 2 (by rfl) ⟨942333, by rfl⟩ : syracuseStep 2512889 = 1884667) B1884667
theorem B9664595 : Blo 1674037 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B36206675 : Blo 1674037 36206675 := bstep (se 1 (by rfl) ⟨27155006, by rfl⟩ : syracuseStep 36206675 = 54310013) B54310013
theorem B2512991 : Blo 1674037 2512991 := bstep (se 1 (by rfl) ⟨1884743, by rfl⟩ : syracuseStep 2512991 = 3769487) B3769487
theorem B2513051 : Blo 1674037 2513051 := bstep (se 1 (by rfl) ⟨1884788, by rfl⟩ : syracuseStep 2513051 = 3769577) B3769577
theorem B2119871 : Blo 1674037 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B2513087 : Blo 1674037 2513087 := bstep (se 1 (by rfl) ⟨1884815, by rfl⟩ : syracuseStep 2513087 = 3769631) B3769631
theorem B2513129 : Blo 1674037 2513129 := bstep (se 2 (by rfl) ⟨942423, by rfl⟩ : syracuseStep 2513129 = 1884847) B1884847
theorem B12712301 : Blo 1674037 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B10189165 : Blo 1674037 10189165 := bstep (se 3 (by rfl) ⟨1910468, by rfl⟩ : syracuseStep 10189165 = 3820937) B3820937
theorem B10729901 : Blo 1674037 10729901 := bstep (se 3 (by rfl) ⟨2011856, by rfl⟩ : syracuseStep 10729901 = 4023713) B4023713
theorem B9542063 : Blo 1674037 9542063 := bstep (se 1 (by rfl) ⟨7156547, by rfl⟩ : syracuseStep 9542063 = 14313095) B14313095
theorem B5364157 : Blo 1674037 5364157 := bstep (se 3 (by rfl) ⟨1005779, by rfl⟩ : syracuseStep 5364157 = 2011559) B2011559
theorem B2513435 : Blo 1674037 2513435 := bstep (se 1 (by rfl) ⟨1885076, by rfl⟩ : syracuseStep 2513435 = 3770153) B3770153
theorem B3766841 : Blo 1674037 3766841 := bstep (se 2 (by rfl) ⟨1412565, by rfl⟩ : syracuseStep 3766841 = 2825131) B2825131
theorem B2513513 : Blo 1674037 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B13589113 : Blo 1674037 13589113 := bstep (se 2 (by rfl) ⟨5095917, by rfl⟩ : syracuseStep 13589113 = 10191835) B10191835
theorem B64363409 : Blo 1674037 64363409 := bstep (se 2 (by rfl) ⟨24136278, by rfl⟩ : syracuseStep 64363409 = 48272557) B48272557
theorem B9542771 : Blo 1674037 9542771 := bstep (se 1 (by rfl) ⟨7157078, by rfl⟩ : syracuseStep 9542771 = 14314157) B14314157
theorem B2514041 : Blo 1674037 2514041 := bstep (se 2 (by rfl) ⟨942765, by rfl⟩ : syracuseStep 2514041 = 1885531) B1885531
theorem B5651585 : Blo 1674037 5651585 := bstep (se 2 (by rfl) ⟨2119344, by rfl⟩ : syracuseStep 5651585 = 4238689) B4238689
theorem B7158941 : Blo 1674037 7158941 := bstep (se 3 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 7158941 = 2684603) B2684603
theorem B5651639 : Blo 1674037 5651639 := bstep (se 1 (by rfl) ⟨4238729, by rfl⟩ : syracuseStep 5651639 = 8477459) B8477459
theorem B3767561 : Blo 1674037 3767561 := bstep (se 2 (by rfl) ⟨1412835, by rfl⟩ : syracuseStep 3767561 = 2825671) B2825671
theorem B7150943 : Blo 1674037 7150943 := bstep (se 1 (by rfl) ⟨5363207, by rfl⟩ : syracuseStep 7150943 = 10726415) B10726415
theorem B12074345 : Blo 1674037 12074345 := bstep (se 2 (by rfl) ⟨4527879, by rfl⟩ : syracuseStep 12074345 = 9055759) B9055759
theorem B4767137 : Blo 1674037 4767137 := bstep (se 2 (by rfl) ⟨1787676, by rfl⟩ : syracuseStep 4767137 = 3575353) B3575353
theorem B1883623 : Blo 1674037 1883623 := bstep (se 1 (by rfl) ⟨1412717, by rfl⟩ : syracuseStep 1883623 = 2825435) B2825435
theorem B6446567 : Blo 1674037 6446567 := bstep (se 1 (by rfl) ⟨4834925, by rfl⟩ : syracuseStep 6446567 = 9669851) B9669851
theorem B9174509 : Blo 1674037 9174509 := bstep (se 3 (by rfl) ⟨1720220, by rfl⟩ : syracuseStep 9174509 = 3440441) B3440441
theorem B27172655 : Blo 1674037 27172655 := bstep (se 1 (by rfl) ⟨20379491, by rfl⟩ : syracuseStep 27172655 = 40758983) B40758983
theorem B5652395 : Blo 1674037 5652395 := bstep (se 1 (by rfl) ⟨4239296, by rfl⟩ : syracuseStep 5652395 = 8478593) B8478593
theorem B1884127 : Blo 1674037 1884127 := bstep (se 1 (by rfl) ⟨1413095, by rfl⟩ : syracuseStep 1884127 = 2826191) B2826191
theorem B4767979 : Blo 1674037 4767979 := bstep (se 1 (by rfl) ⟨3575984, by rfl⟩ : syracuseStep 4767979 = 7151969) B7151969
theorem B3768569 : Blo 1674037 3768569 := bstep (se 2 (by rfl) ⟨1413213, by rfl⟩ : syracuseStep 3768569 = 2826427) B2826427
theorem B1884415 : Blo 1674037 1884415 := bstep (se 1 (by rfl) ⟨1413311, by rfl⟩ : syracuseStep 1884415 = 2826623) B2826623
theorem B3768623 : Blo 1674037 3768623 := bstep (se 1 (by rfl) ⟨2826467, by rfl⟩ : syracuseStep 3768623 = 5652935) B5652935
theorem B4768253 : Blo 1674037 4768253 := bstep (se 3 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 4768253 = 1788095) B1788095
theorem B5652989 : Blo 1674037 5652989 := bstep (se 3 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 5652989 = 2119871) B2119871
theorem B3768839 : Blo 1674037 3768839 := bstep (se 1 (by rfl) ⟨2826629, by rfl⟩ : syracuseStep 3768839 = 5653259) B5653259
theorem B1884703 : Blo 1674037 1884703 := bstep (se 1 (by rfl) ⟨1413527, by rfl⟩ : syracuseStep 1884703 = 2827055) B2827055
theorem B7152209 : Blo 1674037 7152209 := bstep (se 2 (by rfl) ⟨2682078, by rfl⟩ : syracuseStep 7152209 = 5364157) B5364157
theorem B3769019 : Blo 1674037 3769019 := bstep (se 1 (by rfl) ⟨2826764, by rfl⟩ : syracuseStep 3769019 = 5653529) B5653529
theorem B6357959 : Blo 1674037 6357959 := bstep (se 1 (by rfl) ⟨4768469, by rfl⟩ : syracuseStep 6357959 = 9536939) B9536939
theorem B8045563 : Blo 1674037 8045563 := bstep (se 1 (by rfl) ⟨6034172, by rfl⟩ : syracuseStep 8045563 = 12068345) B12068345
theorem B3769451 : Blo 1674037 3769451 := bstep (se 1 (by rfl) ⟨2827088, by rfl⟩ : syracuseStep 3769451 = 5654177) B5654177
theorem B1885351 : Blo 1674037 1885351 := bstep (se 1 (by rfl) ⟨1414013, by rfl⟩ : syracuseStep 1885351 = 2828027) B2828027
theorem B12715217 : Blo 1674037 12715217 := bstep (se 2 (by rfl) ⟨4768206, by rfl⟩ : syracuseStep 12715217 = 9536413) B9536413
theorem B9544979 : Blo 1674037 9544979 := bstep (se 1 (by rfl) ⟨7158734, by rfl⟩ : syracuseStep 9544979 = 14317469) B14317469
theorem B3769919 : Blo 1674037 3769919 := bstep (se 1 (by rfl) ⟨2827439, by rfl⟩ : syracuseStep 3769919 = 5654879) B5654879
theorem B5654123 : Blo 1674037 5654123 := bstep (se 1 (by rfl) ⟨4240592, by rfl⟩ : syracuseStep 5654123 = 8481185) B8481185
theorem B16107119 : Blo 1674037 16107119 := bstep (se 1 (by rfl) ⟨12080339, by rfl⟩ : syracuseStep 16107119 = 24160679) B24160679
theorem B7153267 : Blo 1674037 7153267 := bstep (se 1 (by rfl) ⟨5364950, by rfl⟩ : syracuseStep 7153267 = 10729901) B10729901
theorem B3770027 : Blo 1674037 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B5654393 : Blo 1674037 5654393 := bstep (se 2 (by rfl) ⟨2120397, by rfl⟩ : syracuseStep 5654393 = 4240795) B4240795
theorem B3770351 : Blo 1674037 3770351 := bstep (se 1 (by rfl) ⟨2827763, by rfl⟩ : syracuseStep 3770351 = 5655527) B5655527
theorem B3770567 : Blo 1674037 3770567 := bstep (se 1 (by rfl) ⟨2827925, by rfl⟩ : syracuseStep 3770567 = 5655851) B5655851
theorem B5654771 : Blo 1674037 5654771 := bstep (se 1 (by rfl) ⟨4241078, by rfl⟩ : syracuseStep 5654771 = 8482157) B8482157
theorem B3770747 : Blo 1674037 3770747 := bstep (se 1 (by rfl) ⟨2828060, by rfl⟩ : syracuseStep 3770747 = 5656121) B5656121
theorem B18115103 : Blo 1674037 18115103 := bstep (se 1 (by rfl) ⟨13586327, by rfl⟩ : syracuseStep 18115103 = 27172655) B27172655
theorem B9538145 : Blo 1674037 9538145 := bstep (se 2 (by rfl) ⟨3576804, by rfl⟩ : syracuseStep 9538145 = 7153609) B7153609
theorem B3820135 : Blo 1674037 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B3771017 : Blo 1674037 3771017 := bstep (se 2 (by rfl) ⟨1414131, by rfl⟩ : syracuseStep 3771017 = 2828263) B2828263
theorem B6359735 : Blo 1674037 6359735 := bstep (se 1 (by rfl) ⟨4769801, by rfl⟩ : syracuseStep 6359735 = 9539603) B9539603
theorem B1674207 : Blo 1674037 1674207 := bstep (se 1 (by rfl) ⟨1255655, by rfl⟩ : syracuseStep 1674207 = 2511311) B2511311
theorem B47098855 : Blo 1674037 47098855 := bstep (se 1 (by rfl) ⟨35324141, by rfl⟩ : syracuseStep 47098855 = 70648283) B70648283
theorem B1674235 : Blo 1674037 1674235 := bstep (se 1 (by rfl) ⟨1255676, by rfl⟩ : syracuseStep 1674235 = 2511353) B2511353
theorem B1674303 : Blo 1674037 1674303 := bstep (se 1 (by rfl) ⟨1255727, by rfl⟩ : syracuseStep 1674303 = 2511455) B2511455
theorem B3181675 : Blo 1674037 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B13585553 : Blo 1674037 13585553 := bstep (se 2 (by rfl) ⟨5094582, by rfl⟩ : syracuseStep 13585553 = 10189165) B10189165
theorem B1674623 : Blo 1674037 1674623 := bstep (se 1 (by rfl) ⟨1255967, by rfl⟩ : syracuseStep 1674623 = 2511935) B2511935
theorem B1674651 : Blo 1674037 1674651 := bstep (se 1 (by rfl) ⟨1255988, by rfl⟩ : syracuseStep 1674651 = 2511977) B2511977
theorem B10726825 : Blo 1674037 10726825 := bstep (se 2 (by rfl) ⟨4022559, by rfl⟩ : syracuseStep 10726825 = 8045119) B8045119
theorem B2682335 : Blo 1674037 2682335 := bstep (se 1 (by rfl) ⟨2011751, by rfl⟩ : syracuseStep 2682335 = 4023503) B4023503
theorem B1674719 : Blo 1674037 1674719 := bstep (se 1 (by rfl) ⟨1256039, by rfl⟩ : syracuseStep 1674719 = 2512079) B2512079
theorem B8048119 : Blo 1674037 8048119 := bstep (se 1 (by rfl) ⟨6036089, by rfl⟩ : syracuseStep 8048119 = 12072179) B12072179
theorem B12717647 : Blo 1674037 12717647 := bstep (se 1 (by rfl) ⟨9538235, by rfl⟩ : syracuseStep 12717647 = 19076471) B19076471
theorem B1674855 : Blo 1674037 1674855 := bstep (se 1 (by rfl) ⟨1256141, by rfl⟩ : syracuseStep 1674855 = 2512283) B2512283
theorem B1789543 : Blo 1674037 1789543 := bstep (se 1 (by rfl) ⟨1342157, by rfl⟩ : syracuseStep 1789543 = 2684315) B2684315
theorem B1675003 : Blo 1674037 1675003 := bstep (se 1 (by rfl) ⟨1256252, by rfl⟩ : syracuseStep 1675003 = 2512505) B2512505
theorem B16535299 : Blo 1674037 16535299 := bstep (se 1 (by rfl) ⟨12401474, by rfl⟩ : syracuseStep 16535299 = 24802949) B24802949
theorem B10735415 : Blo 1674037 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B1675071 : Blo 1674037 1675071 := bstep (se 1 (by rfl) ⟨1256303, by rfl⟩ : syracuseStep 1675071 = 2512607) B2512607
theorem B5656391 : Blo 1674037 5656391 := bstep (se 1 (by rfl) ⟨4242293, by rfl⟩ : syracuseStep 5656391 = 8484587) B8484587
theorem B32190317 : Blo 1674037 32190317 := bstep (se 3 (by rfl) ⟨6035684, by rfl⟩ : syracuseStep 32190317 = 12071369) B12071369
theorem B1675135 : Blo 1674037 1675135 := bstep (se 1 (by rfl) ⟨1256351, by rfl⟩ : syracuseStep 1675135 = 2512703) B2512703
theorem B1675247 : Blo 1674037 1675247 := bstep (se 1 (by rfl) ⟨1256435, by rfl⟩ : syracuseStep 1675247 = 2512871) B2512871
theorem B1675259 : Blo 1674037 1675259 := bstep (se 1 (by rfl) ⟨1256444, by rfl⟩ : syracuseStep 1675259 = 2512889) B2512889
theorem B15282209 : Blo 1674037 15282209 := bstep (se 2 (by rfl) ⟨5730828, by rfl⟩ : syracuseStep 15282209 = 11461657) B11461657
theorem B6443063 : Blo 1674037 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B24137783 : Blo 1674037 24137783 := bstep (se 1 (by rfl) ⟨18103337, by rfl⟩ : syracuseStep 24137783 = 36206675) B36206675
theorem B1675327 : Blo 1674037 1675327 := bstep (se 1 (by rfl) ⟨1256495, by rfl⟩ : syracuseStep 1675327 = 2512991) B2512991
theorem B1675367 : Blo 1674037 1675367 := bstep (se 1 (by rfl) ⟨1256525, by rfl⟩ : syracuseStep 1675367 = 2513051) B2513051
theorem B12726395 : Blo 1674037 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B1675391 : Blo 1674037 1675391 := bstep (se 1 (by rfl) ⟨1256543, by rfl⟩ : syracuseStep 1675391 = 2513087) B2513087
theorem B16093313 : Blo 1674037 16093313 := bstep (se 2 (by rfl) ⟨6034992, by rfl⟩ : syracuseStep 16093313 = 12069985) B12069985
theorem B4239499 : Blo 1674037 4239499 := bstep (se 1 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 4239499 = 6359249) B6359249
theorem B1675419 : Blo 1674037 1675419 := bstep (se 1 (by rfl) ⟨1256564, by rfl⟩ : syracuseStep 1675419 = 2513129) B2513129
theorem B8474867 : Blo 1674037 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B10735901 : Blo 1674037 10735901 := bstep (se 3 (by rfl) ⟨2012981, by rfl⟩ : syracuseStep 10735901 = 4025963) B4025963
theorem B6361375 : Blo 1674037 6361375 := bstep (se 1 (by rfl) ⟨4771031, by rfl⟩ : syracuseStep 6361375 = 9542063) B9542063
theorem B55849283 : Blo 1674037 55849283 := bstep (se 1 (by rfl) ⟨41886962, by rfl⟩ : syracuseStep 55849283 = 83773925) B83773925
theorem B1675623 : Blo 1674037 1675623 := bstep (se 1 (by rfl) ⟨1256717, by rfl⟩ : syracuseStep 1675623 = 2513435) B2513435
theorem B2511227 : Blo 1674037 2511227 := bstep (se 1 (by rfl) ⟨1883420, by rfl⟩ : syracuseStep 2511227 = 3766841) B3766841
theorem B1675675 : Blo 1674037 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B2511497 : Blo 1674037 2511497 := bstep (se 2 (by rfl) ⟨941811, by rfl⟩ : syracuseStep 2511497 = 1883623) B1883623
theorem B6361847 : Blo 1674037 6361847 := bstep (se 1 (by rfl) ⟨4771385, by rfl⟩ : syracuseStep 6361847 = 9542771) B9542771
theorem B1676027 : Blo 1674037 1676027 := bstep (se 1 (by rfl) ⟨1257020, by rfl⟩ : syracuseStep 1676027 = 2514041) B2514041
theorem B4772627 : Blo 1674037 4772627 := bstep (se 1 (by rfl) ⟨3579470, by rfl⟩ : syracuseStep 4772627 = 7158941) B7158941
theorem B2511707 : Blo 1674037 2511707 := bstep (se 1 (by rfl) ⟨1883780, by rfl⟩ : syracuseStep 2511707 = 3767561) B3767561
theorem B15283081 : Blo 1674037 15283081 := bstep (se 2 (by rfl) ⟨5731155, by rfl⟩ : syracuseStep 15283081 = 11462311) B11462311
theorem B8049563 : Blo 1674037 8049563 := bstep (se 1 (by rfl) ⟨6037172, by rfl⟩ : syracuseStep 8049563 = 12074345) B12074345
theorem B11465657 : Blo 1674037 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B4297711 : Blo 1674037 4297711 := bstep (se 1 (by rfl) ⟨3223283, by rfl⟩ : syracuseStep 4297711 = 6446567) B6446567
theorem B6116339 : Blo 1674037 6116339 := bstep (se 1 (by rfl) ⟨4587254, by rfl⟩ : syracuseStep 6116339 = 9174509) B9174509
theorem B12727367 : Blo 1674037 12727367 := bstep (se 1 (by rfl) ⟨9545525, by rfl⟩ : syracuseStep 12727367 = 19091051) B19091051
theorem B2512169 : Blo 1674037 2512169 := bstep (se 2 (by rfl) ⟨942063, by rfl⟩ : syracuseStep 2512169 = 1884127) B1884127
theorem B2512367 : Blo 1674037 2512367 := bstep (se 1 (by rfl) ⟨1884275, by rfl⟩ : syracuseStep 2512367 = 3768551) B3768551
theorem B4241119 : Blo 1674037 4241119 := bstep (se 1 (by rfl) ⟨3180839, by rfl⟩ : syracuseStep 4241119 = 6361679) B6361679
theorem B8476487 : Blo 1674037 8476487 := bstep (se 1 (by rfl) ⟨6357365, by rfl⟩ : syracuseStep 8476487 = 12714731) B12714731
theorem B2119547 : Blo 1674037 2119547 := bstep (se 1 (by rfl) ⟨1589660, by rfl⟩ : syracuseStep 2119547 = 3179321) B3179321
theorem B2512763 : Blo 1674037 2512763 := bstep (se 1 (by rfl) ⟨1884572, by rfl⟩ : syracuseStep 2512763 = 3769145) B3769145
theorem B2512799 : Blo 1674037 2512799 := bstep (se 1 (by rfl) ⟨1884599, by rfl⟩ : syracuseStep 2512799 = 3769199) B3769199
theorem B10729543 : Blo 1674037 10729543 := bstep (se 1 (by rfl) ⟨8047157, by rfl⟩ : syracuseStep 10729543 = 16094315) B16094315
theorem B61126787 : Blo 1674037 61126787 := bstep (se 1 (by rfl) ⟨45845090, by rfl⟩ : syracuseStep 61126787 = 91690181) B91690181
theorem B2513033 : Blo 1674037 2513033 := bstep (se 2 (by rfl) ⟨942387, by rfl⟩ : syracuseStep 2513033 = 1884775) B1884775
theorem B7157915 : Blo 1674037 7157915 := bstep (se 1 (by rfl) ⟨5368436, by rfl⟩ : syracuseStep 7157915 = 10736873) B10736873
theorem B18118817 : Blo 1674037 18118817 := bstep (se 2 (by rfl) ⟨6794556, by rfl⟩ : syracuseStep 18118817 = 13589113) B13589113
theorem B5650667 : Blo 1674037 5650667 := bstep (se 1 (by rfl) ⟨4238000, by rfl⟩ : syracuseStep 5650667 = 8476001) B8476001
theorem B19069181 : Blo 1674037 19069181 := bstep (se 3 (by rfl) ⟨3575471, by rfl⟩ : syracuseStep 19069181 = 7150943) B7150943
theorem B2513183 : Blo 1674037 2513183 := bstep (se 1 (by rfl) ⟨1884887, by rfl⟩ : syracuseStep 2513183 = 3769775) B3769775
theorem B6363623 : Blo 1674037 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B14301683 : Blo 1674037 14301683 := bstep (se 1 (by rfl) ⟨10726262, by rfl⟩ : syracuseStep 14301683 = 21452525) B21452525
theorem B2120519 : Blo 1674037 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B2513735 : Blo 1674037 2513735 := bstep (se 1 (by rfl) ⟨1885301, by rfl⟩ : syracuseStep 2513735 = 3770603) B3770603
theorem B48291011 : Blo 1674037 48291011 := bstep (se 1 (by rfl) ⟨36218258, by rfl⟩ : syracuseStep 48291011 = 72436517) B72436517
theorem B42908939 : Blo 1674037 42908939 := bstep (se 1 (by rfl) ⟨32181704, by rfl⟩ : syracuseStep 42908939 = 64363409) B64363409
theorem B2825543 : Blo 1674037 2825543 := bstep (se 1 (by rfl) ⟨2119157, by rfl⟩ : syracuseStep 2825543 = 4238315) B4238315
theorem B9805153 : Blo 1674037 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B3767723 : Blo 1674037 3767723 := bstep (se 1 (by rfl) ⟨2825792, by rfl⟩ : syracuseStep 3767723 = 5651585) B5651585
theorem B27155911 : Blo 1674037 27155911 := bstep (se 1 (by rfl) ⟨20366933, by rfl⟩ : syracuseStep 27155911 = 40733867) B40733867
theorem B3767759 : Blo 1674037 3767759 := bstep (se 1 (by rfl) ⟨2825819, by rfl⟩ : syracuseStep 3767759 = 5651639) B5651639
theorem B2825705 : Blo 1674037 2825705 := bstep (se 2 (by rfl) ⟨1059639, by rfl⟩ : syracuseStep 2825705 = 2119279) B2119279
theorem B3178091 : Blo 1674037 3178091 := bstep (se 1 (by rfl) ⟨2383568, by rfl⟩ : syracuseStep 3178091 = 4767137) B4767137
theorem B9543521 : Blo 1674037 9543521 := bstep (se 2 (by rfl) ⟨3578820, by rfl⟩ : syracuseStep 9543521 = 7157641) B7157641
theorem B3768263 : Blo 1674037 3768263 := bstep (se 1 (by rfl) ⟨2826197, by rfl⟩ : syracuseStep 3768263 = 5652395) B5652395
theorem B5652665 : Blo 1674037 5652665 := bstep (se 2 (by rfl) ⟨2119749, by rfl⟩ : syracuseStep 5652665 = 4239499) B4239499
theorem B37232855 : Blo 1674037 37232855 := bstep (se 1 (by rfl) ⟨27924641, by rfl⟩ : syracuseStep 37232855 = 55849283) B55849283
theorem B6357305 : Blo 1674037 6357305 := bstep (se 2 (by rfl) ⟨2383989, by rfl⟩ : syracuseStep 6357305 = 4767979) B4767979
theorem B3178835 : Blo 1674037 3178835 := bstep (se 1 (by rfl) ⟨2384126, by rfl⟩ : syracuseStep 3178835 = 4768253) B4768253
theorem B3768659 : Blo 1674037 3768659 := bstep (se 1 (by rfl) ⟨2826494, by rfl⟩ : syracuseStep 3768659 = 5652989) B5652989
theorem B4768139 : Blo 1674037 4768139 := bstep (se 1 (by rfl) ⟨3576104, by rfl⟩ : syracuseStep 4768139 = 7152209) B7152209
theorem B9544229 : Blo 1674037 9544229 := bstep (se 4 (by rfl) ⟨894771, by rfl⟩ : syracuseStep 9544229 = 1789543) B1789543
theorem B5366375 : Blo 1674037 5366375 := bstep (se 1 (by rfl) ⟨4024781, by rfl⟩ : syracuseStep 5366375 = 8049563) B8049563
theorem B7643771 : Blo 1674037 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B3769415 : Blo 1674037 3769415 := bstep (se 1 (by rfl) ⟨2827061, by rfl⟩ : syracuseStep 3769415 = 5654123) B5654123
theorem B3769595 : Blo 1674037 3769595 := bstep (se 1 (by rfl) ⟨2827196, by rfl⟩ : syracuseStep 3769595 = 5654393) B5654393
theorem B7152893 : Blo 1674037 7152893 := bstep (se 3 (by rfl) ⟨1341167, by rfl⟩ : syracuseStep 7152893 = 2682335) B2682335
theorem B3769847 : Blo 1674037 3769847 := bstep (se 1 (by rfl) ⟨2827385, by rfl⟩ : syracuseStep 3769847 = 5654771) B5654771
theorem B12076735 : Blo 1674037 12076735 := bstep (se 1 (by rfl) ⟨9057551, by rfl⟩ : syracuseStep 12076735 = 18115103) B18115103
theorem B6358763 : Blo 1674037 6358763 := bstep (se 1 (by rfl) ⟨4769072, by rfl⟩ : syracuseStep 6358763 = 9538145) B9538145
theorem B9537689 : Blo 1674037 9537689 := bstep (se 2 (by rfl) ⟨3576633, by rfl⟩ : syracuseStep 9537689 = 7153267) B7153267
theorem B5654717 : Blo 1674037 5654717 := bstep (se 3 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 5654717 = 2120519) B2120519
theorem B5654825 : Blo 1674037 5654825 := bstep (se 2 (by rfl) ⟨2120559, by rfl⟩ : syracuseStep 5654825 = 4241119) B4241119
theorem B22047065 : Blo 1674037 22047065 := bstep (se 2 (by rfl) ⟨8267649, by rfl⟩ : syracuseStep 22047065 = 16535299) B16535299
theorem B3770927 : Blo 1674037 3770927 := bstep (se 1 (by rfl) ⟨2828195, by rfl⟩ : syracuseStep 3770927 = 5656391) B5656391
theorem B4295375 : Blo 1674037 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B16091855 : Blo 1674037 16091855 := bstep (se 1 (by rfl) ⟨12068891, by rfl⟩ : syracuseStep 16091855 = 24137783) B24137783
theorem B14306057 : Blo 1674037 14306057 := bstep (se 2 (by rfl) ⟨5364771, by rfl⟩ : syracuseStep 14306057 = 10729543) B10729543
theorem B1674151 : Blo 1674037 1674151 := bstep (se 1 (by rfl) ⟨1255613, by rfl⟩ : syracuseStep 1674151 = 2511227) B2511227
theorem B8481833 : Blo 1674037 8481833 := bstep (se 2 (by rfl) ⟨3180687, by rfl⟩ : syracuseStep 8481833 = 6361375) B6361375
theorem B1674331 : Blo 1674037 1674331 := bstep (se 1 (by rfl) ⟨1255748, by rfl⟩ : syracuseStep 1674331 = 2511497) B2511497
theorem B3181751 : Blo 1674037 3181751 := bstep (se 1 (by rfl) ⟨2386313, by rfl⟩ : syracuseStep 3181751 = 4772627) B4772627
theorem B1674471 : Blo 1674037 1674471 := bstep (se 1 (by rfl) ⟨1255853, by rfl⟩ : syracuseStep 1674471 = 2511707) B2511707
theorem B4238639 : Blo 1674037 4238639 := bstep (se 1 (by rfl) ⟨3178979, by rfl⟩ : syracuseStep 4238639 = 6357959) B6357959
theorem B1674779 : Blo 1674037 1674779 := bstep (se 1 (by rfl) ⟨1256084, by rfl⟩ : syracuseStep 1674779 = 2512169) B2512169
theorem B1674911 : Blo 1674037 1674911 := bstep (se 1 (by rfl) ⟨1256183, by rfl⟩ : syracuseStep 1674911 = 2512367) B2512367
theorem B20377441 : Blo 1674037 20377441 := bstep (se 2 (by rfl) ⟨7641540, by rfl⟩ : syracuseStep 20377441 = 15283081) B15283081
theorem B1675175 : Blo 1674037 1675175 := bstep (se 1 (by rfl) ⟨1256381, by rfl⟩ : syracuseStep 1675175 = 2512763) B2512763
theorem B1675199 : Blo 1674037 1675199 := bstep (se 1 (by rfl) ⟨1256399, by rfl⟩ : syracuseStep 1675199 = 2512799) B2512799
theorem B5730281 : Blo 1674037 5730281 := bstep (se 2 (by rfl) ⟨2148855, by rfl⟩ : syracuseStep 5730281 = 4297711) B4297711
theorem B10727417 : Blo 1674037 10727417 := bstep (se 2 (by rfl) ⟨4022781, by rfl⟩ : syracuseStep 10727417 = 8045563) B8045563
theorem B40751191 : Blo 1674037 40751191 := bstep (se 1 (by rfl) ⟨30563393, by rfl⟩ : syracuseStep 40751191 = 61126787) B61126787
theorem B1675355 : Blo 1674037 1675355 := bstep (se 1 (by rfl) ⟨1256516, by rfl⟩ : syracuseStep 1675355 = 2513033) B2513033
theorem B4771943 : Blo 1674037 4771943 := bstep (se 1 (by rfl) ⟨3578957, by rfl⟩ : syracuseStep 4771943 = 7157915) B7157915
theorem B12079211 : Blo 1674037 12079211 := bstep (se 1 (by rfl) ⟨9059408, by rfl⟩ : syracuseStep 12079211 = 18118817) B18118817
theorem B1675455 : Blo 1674037 1675455 := bstep (se 1 (by rfl) ⟨1256591, by rfl⟩ : syracuseStep 1675455 = 2513183) B2513183
theorem B4239823 : Blo 1674037 4239823 := bstep (se 1 (by rfl) ⟨3179867, by rfl⟩ : syracuseStep 4239823 = 6359735) B6359735
theorem B1675823 : Blo 1674037 1675823 := bstep (se 1 (by rfl) ⟨1256867, by rfl⟩ : syracuseStep 1675823 = 2513735) B2513735
theorem B9057035 : Blo 1674037 9057035 := bstep (se 1 (by rfl) ⟨6792776, by rfl⟩ : syracuseStep 9057035 = 13585553) B13585553
theorem B2511815 : Blo 1674037 2511815 := bstep (se 1 (by rfl) ⟨1883861, by rfl⟩ : syracuseStep 2511815 = 3767723) B3767723
theorem B2511839 : Blo 1674037 2511839 := bstep (se 1 (by rfl) ⟨1883879, by rfl⟩ : syracuseStep 2511839 = 3767759) B3767759
theorem B2118727 : Blo 1674037 2118727 := bstep (se 1 (by rfl) ⟨1589045, by rfl⟩ : syracuseStep 2118727 = 3178091) B3178091
theorem B7156943 : Blo 1674037 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B6362347 : Blo 1674037 6362347 := bstep (se 1 (by rfl) ⟨4771760, by rfl⟩ : syracuseStep 6362347 = 9543521) B9543521
theorem B21460211 : Blo 1674037 21460211 := bstep (se 1 (by rfl) ⟨16095158, by rfl⟩ : syracuseStep 21460211 = 32190317) B32190317
theorem B2512175 : Blo 1674037 2512175 := bstep (se 1 (by rfl) ⟨1884131, by rfl⟩ : syracuseStep 2512175 = 3768263) B3768263
theorem B8484263 : Blo 1674037 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B10728875 : Blo 1674037 10728875 := bstep (se 1 (by rfl) ⟨8046656, by rfl⟩ : syracuseStep 10728875 = 16093313) B16093313
theorem B40752557 : Blo 1674037 40752557 := bstep (se 3 (by rfl) ⟨7641104, by rfl⟩ : syracuseStep 40752557 = 15282209) B15282209
theorem B5649911 : Blo 1674037 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B2512379 : Blo 1674037 2512379 := bstep (se 1 (by rfl) ⟨1884284, by rfl⟩ : syracuseStep 2512379 = 3768569) B3768569
theorem B7157267 : Blo 1674037 7157267 := bstep (se 1 (by rfl) ⟨5367950, by rfl⟩ : syracuseStep 7157267 = 10735901) B10735901
theorem B2512415 : Blo 1674037 2512415 := bstep (se 1 (by rfl) ⟨1884311, by rfl⟩ : syracuseStep 2512415 = 3768623) B3768623
theorem B2512553 : Blo 1674037 2512553 := bstep (se 2 (by rfl) ⟨942207, by rfl⟩ : syracuseStep 2512553 = 1884415) B1884415
theorem B2512559 : Blo 1674037 2512559 := bstep (se 1 (by rfl) ⟨1884419, by rfl⟩ : syracuseStep 2512559 = 3768839) B3768839
theorem B2512679 : Blo 1674037 2512679 := bstep (se 1 (by rfl) ⟨1884509, by rfl⟩ : syracuseStep 2512679 = 3769019) B3769019
theorem B4241231 : Blo 1674037 4241231 := bstep (se 1 (by rfl) ⟨3180923, by rfl⟩ : syracuseStep 4241231 = 6361847) B6361847
theorem B4077559 : Blo 1674037 4077559 := bstep (se 1 (by rfl) ⟨3058169, by rfl⟩ : syracuseStep 4077559 = 6116339) B6116339
theorem B2512937 : Blo 1674037 2512937 := bstep (se 2 (by rfl) ⟨942351, by rfl⟩ : syracuseStep 2512937 = 1884703) B1884703
theorem B8484911 : Blo 1674037 8484911 := bstep (se 1 (by rfl) ⟨6363683, by rfl⟩ : syracuseStep 8484911 = 12727367) B12727367
theorem B2512967 : Blo 1674037 2512967 := bstep (se 1 (by rfl) ⟨1884725, by rfl⟩ : syracuseStep 2512967 = 3769451) B3769451
theorem B5093513 : Blo 1674037 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B8476811 : Blo 1674037 8476811 := bstep (se 1 (by rfl) ⟨6357608, by rfl⟩ : syracuseStep 8476811 = 12715217) B12715217
theorem B6363319 : Blo 1674037 6363319 := bstep (se 1 (by rfl) ⟨4772489, by rfl⟩ : syracuseStep 6363319 = 9544979) B9544979
theorem B2513279 : Blo 1674037 2513279 := bstep (se 1 (by rfl) ⟨1884959, by rfl⟩ : syracuseStep 2513279 = 3769919) B3769919
theorem B10738079 : Blo 1674037 10738079 := bstep (se 1 (by rfl) ⟨8053559, by rfl⟩ : syracuseStep 10738079 = 16107119) B16107119
theorem B2513351 : Blo 1674037 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B5650991 : Blo 1674037 5650991 := bstep (se 1 (by rfl) ⟨4238243, by rfl⟩ : syracuseStep 5650991 = 8476487) B8476487
theorem B62798473 : Blo 1674037 62798473 := bstep (se 2 (by rfl) ⟨23549427, by rfl⟩ : syracuseStep 62798473 = 47098855) B47098855
theorem B2513567 : Blo 1674037 2513567 := bstep (se 1 (by rfl) ⟨1885175, by rfl⟩ : syracuseStep 2513567 = 3770351) B3770351
theorem B2513711 : Blo 1674037 2513711 := bstep (se 1 (by rfl) ⟨1885283, by rfl⟩ : syracuseStep 2513711 = 3770567) B3770567
theorem B4242233 : Blo 1674037 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B3767111 : Blo 1674037 3767111 := bstep (se 1 (by rfl) ⟨2825333, by rfl⟩ : syracuseStep 3767111 = 5650667) B5650667
theorem B12712787 : Blo 1674037 12712787 := bstep (se 1 (by rfl) ⟨9534590, by rfl⟩ : syracuseStep 12712787 = 19069181) B19069181
theorem B2513801 : Blo 1674037 2513801 := bstep (se 2 (by rfl) ⟨942675, by rfl⟩ : syracuseStep 2513801 = 1885351) B1885351
theorem B2513831 : Blo 1674037 2513831 := bstep (se 1 (by rfl) ⟨1885373, by rfl⟩ : syracuseStep 2513831 = 3770747) B3770747
theorem B4242415 : Blo 1674037 4242415 := bstep (se 1 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 4242415 = 6363623) B6363623
theorem B9534455 : Blo 1674037 9534455 := bstep (se 1 (by rfl) ⟨7150841, by rfl⟩ : syracuseStep 9534455 = 14301683) B14301683
theorem B2514011 : Blo 1674037 2514011 := bstep (se 1 (by rfl) ⟨1885508, by rfl⟩ : syracuseStep 2514011 = 3771017) B3771017
theorem B13073537 : Blo 1674037 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B14302433 : Blo 1674037 14302433 := bstep (se 2 (by rfl) ⟨5363412, by rfl⟩ : syracuseStep 14302433 = 10726825) B10726825
theorem B36207881 : Blo 1674037 36207881 := bstep (se 2 (by rfl) ⟨13577955, by rfl⟩ : syracuseStep 36207881 = 27155911) B27155911
theorem B10730825 : Blo 1674037 10730825 := bstep (se 2 (by rfl) ⟨4024059, by rfl⟩ : syracuseStep 10730825 = 8048119) B8048119
theorem B32194007 : Blo 1674037 32194007 := bstep (se 1 (by rfl) ⟨24145505, by rfl⟩ : syracuseStep 32194007 = 48291011) B48291011
theorem B28605959 : Blo 1674037 28605959 := bstep (se 1 (by rfl) ⟨21454469, by rfl⟩ : syracuseStep 28605959 = 42908939) B42908939
theorem B1883695 : Blo 1674037 1883695 := bstep (se 1 (by rfl) ⟨1412771, by rfl⟩ : syracuseStep 1883695 = 2825543) B2825543
theorem B1883803 : Blo 1674037 1883803 := bstep (se 1 (by rfl) ⟨1412852, by rfl⟩ : syracuseStep 1883803 = 2825705) B2825705
theorem B5652125 : Blo 1674037 5652125 := bstep (se 3 (by rfl) ⟨1059773, by rfl⟩ : syracuseStep 5652125 = 2119547) B2119547
theorem B8478431 : Blo 1674037 8478431 := bstep (se 1 (by rfl) ⟨6358823, by rfl⟩ : syracuseStep 8478431 = 12717647) B12717647
theorem B3768443 : Blo 1674037 3768443 := bstep (se 1 (by rfl) ⟨2826332, by rfl⟩ : syracuseStep 3768443 = 5652665) B5652665
theorem B24821903 : Blo 1674037 24821903 := bstep (se 1 (by rfl) ⟨18616427, by rfl⟩ : syracuseStep 24821903 = 37232855) B37232855
theorem B3178759 : Blo 1674037 3178759 := bstep (se 1 (by rfl) ⟨2384069, by rfl⟩ : syracuseStep 3178759 = 4768139) B4768139
theorem B32211229 : Blo 1674037 32211229 := bstep (se 3 (by rfl) ⟨6039605, by rfl⟩ : syracuseStep 32211229 = 12079211) B12079211
theorem B5095847 : Blo 1674037 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B6038023 : Blo 1674037 6038023 := bstep (se 1 (by rfl) ⟨4528517, by rfl⟩ : syracuseStep 6038023 = 9057035) B9057035
theorem B5653097 : Blo 1674037 5653097 := bstep (se 2 (by rfl) ⟨2119911, by rfl⟩ : syracuseStep 5653097 = 4239823) B4239823
theorem B4768595 : Blo 1674037 4768595 := bstep (se 1 (by rfl) ⟨3576446, by rfl⟩ : syracuseStep 4768595 = 7152893) B7152893
theorem B2827487 : Blo 1674037 2827487 := bstep (se 1 (by rfl) ⟨2120615, by rfl⟩ : syracuseStep 2827487 = 4241231) B4241231
theorem B6358459 : Blo 1674037 6358459 := bstep (se 1 (by rfl) ⟨4768844, by rfl⟩ : syracuseStep 6358459 = 9537689) B9537689
theorem B3769811 : Blo 1674037 3769811 := bstep (se 1 (by rfl) ⟨2827358, by rfl⟩ : syracuseStep 3769811 = 5654717) B5654717
theorem B3769883 : Blo 1674037 3769883 := bstep (se 1 (by rfl) ⟨2827412, by rfl⟩ : syracuseStep 3769883 = 5654825) B5654825
theorem B14698043 : Blo 1674037 14698043 := bstep (se 1 (by rfl) ⟨11023532, by rfl⟩ : syracuseStep 14698043 = 22047065) B22047065
theorem B9537371 : Blo 1674037 9537371 := bstep (se 1 (by rfl) ⟨7153028, by rfl⟩ : syracuseStep 9537371 = 14306057) B14306057
theorem B2828155 : Blo 1674037 2828155 := bstep (se 1 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 2828155 = 4242233) B4242233
theorem B5654555 : Blo 1674037 5654555 := bstep (se 1 (by rfl) ⟨4240916, by rfl⟩ : syracuseStep 5654555 = 8481833) B8481833
theorem B7153883 : Blo 1674037 7153883 := bstep (se 1 (by rfl) ⟨5365412, by rfl⟩ : syracuseStep 7153883 = 10730825) B10730825
theorem B3820187 : Blo 1674037 3820187 := bstep (se 1 (by rfl) ⟨2865140, by rfl⟩ : syracuseStep 3820187 = 5730281) B5730281
theorem B3181295 : Blo 1674037 3181295 := bstep (se 1 (by rfl) ⟨2385971, by rfl⟩ : syracuseStep 3181295 = 4771943) B4771943
theorem B4238203 : Blo 1674037 4238203 := bstep (se 1 (by rfl) ⟨3178652, by rfl⟩ : syracuseStep 4238203 = 6357305) B6357305
theorem B1674543 : Blo 1674037 1674543 := bstep (se 1 (by rfl) ⟨1255907, by rfl⟩ : syracuseStep 1674543 = 2511815) B2511815
theorem B1674559 : Blo 1674037 1674559 := bstep (se 1 (by rfl) ⟨1255919, by rfl⟩ : syracuseStep 1674559 = 2511839) B2511839
theorem B334925189 : Blo 1674037 334925189 := bstep (se 4 (by rfl) ⟨31399236, by rfl⟩ : syracuseStep 334925189 = 62798473) B62798473
theorem B4771295 : Blo 1674037 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B14306807 : Blo 1674037 14306807 := bstep (se 1 (by rfl) ⟨10730105, by rfl⟩ : syracuseStep 14306807 = 21460211) B21460211
theorem B1674783 : Blo 1674037 1674783 := bstep (se 1 (by rfl) ⟨1256087, by rfl⟩ : syracuseStep 1674783 = 2512175) B2512175
theorem B5656175 : Blo 1674037 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B27168371 : Blo 1674037 27168371 := bstep (se 1 (by rfl) ⟨20376278, by rfl⟩ : syracuseStep 27168371 = 40752557) B40752557
theorem B1674919 : Blo 1674037 1674919 := bstep (se 1 (by rfl) ⟨1256189, by rfl⟩ : syracuseStep 1674919 = 2512379) B2512379
theorem B4771511 : Blo 1674037 4771511 := bstep (se 1 (by rfl) ⟨3578633, by rfl⟩ : syracuseStep 4771511 = 7157267) B7157267
theorem B1674943 : Blo 1674037 1674943 := bstep (se 1 (by rfl) ⟨1256207, by rfl⟩ : syracuseStep 1674943 = 2512415) B2512415
theorem B1675035 : Blo 1674037 1675035 := bstep (se 1 (by rfl) ⟨1256276, by rfl⟩ : syracuseStep 1675035 = 2512553) B2512553
theorem B28610333 : Blo 1674037 28610333 := bstep (se 3 (by rfl) ⟨5364437, by rfl⟩ : syracuseStep 28610333 = 10728875) B10728875
theorem B1675039 : Blo 1674037 1675039 := bstep (se 1 (by rfl) ⟨1256279, by rfl⟩ : syracuseStep 1675039 = 2512559) B2512559
theorem B4239175 : Blo 1674037 4239175 := bstep (se 1 (by rfl) ⟨3179381, by rfl⟩ : syracuseStep 4239175 = 6358763) B6358763
theorem B1675119 : Blo 1674037 1675119 := bstep (se 1 (by rfl) ⟨1256339, by rfl⟩ : syracuseStep 1675119 = 2512679) B2512679
theorem B5656553 : Blo 1674037 5656553 := bstep (se 2 (by rfl) ⟨2121207, by rfl⟩ : syracuseStep 5656553 = 4242415) B4242415
theorem B1675291 : Blo 1674037 1675291 := bstep (se 1 (by rfl) ⟨1256468, by rfl⟩ : syracuseStep 1675291 = 2512937) B2512937
theorem B5656607 : Blo 1674037 5656607 := bstep (se 1 (by rfl) ⟨4242455, by rfl⟩ : syracuseStep 5656607 = 8484911) B8484911
theorem B1675311 : Blo 1674037 1675311 := bstep (se 1 (by rfl) ⟨1256483, by rfl⟩ : syracuseStep 1675311 = 2512967) B2512967
theorem B3395675 : Blo 1674037 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B1675519 : Blo 1674037 1675519 := bstep (se 1 (by rfl) ⟨1256639, by rfl⟩ : syracuseStep 1675519 = 2513279) B2513279
theorem B1675567 : Blo 1674037 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B8483129 : Blo 1674037 8483129 := bstep (se 2 (by rfl) ⟨3181173, by rfl⟩ : syracuseStep 8483129 = 6362347) B6362347
theorem B1675711 : Blo 1674037 1675711 := bstep (se 1 (by rfl) ⟨1256783, by rfl⟩ : syracuseStep 1675711 = 2513567) B2513567
theorem B2863583 : Blo 1674037 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B10727903 : Blo 1674037 10727903 := bstep (se 1 (by rfl) ⟨8045927, by rfl⟩ : syracuseStep 10727903 = 16091855) B16091855
theorem B1675807 : Blo 1674037 1675807 := bstep (se 1 (by rfl) ⟨1256855, by rfl⟩ : syracuseStep 1675807 = 2513711) B2513711
theorem B2511407 : Blo 1674037 2511407 := bstep (se 1 (by rfl) ⟨1883555, by rfl⟩ : syracuseStep 2511407 = 3767111) B3767111
theorem B8475191 : Blo 1674037 8475191 := bstep (se 1 (by rfl) ⟨6356393, by rfl⟩ : syracuseStep 8475191 = 12712787) B12712787
theorem B1675867 : Blo 1674037 1675867 := bstep (se 1 (by rfl) ⟨1256900, by rfl⟩ : syracuseStep 1675867 = 2513801) B2513801
theorem B1675887 : Blo 1674037 1675887 := bstep (se 1 (by rfl) ⟨1256915, by rfl⟩ : syracuseStep 1675887 = 2513831) B2513831
theorem B1676007 : Blo 1674037 1676007 := bstep (se 1 (by rfl) ⟨1257005, by rfl⟩ : syracuseStep 1676007 = 2514011) B2514011
theorem B2511593 : Blo 1674037 2511593 := bstep (se 2 (by rfl) ⟨941847, by rfl⟩ : syracuseStep 2511593 = 1883695) B1883695
theorem B24138587 : Blo 1674037 24138587 := bstep (se 1 (by rfl) ⟨18103940, by rfl⟩ : syracuseStep 24138587 = 36207881) B36207881
theorem B2511737 : Blo 1674037 2511737 := bstep (se 2 (by rfl) ⟨941901, by rfl⟩ : syracuseStep 2511737 = 1883803) B1883803
theorem B16102313 : Blo 1674037 16102313 := bstep (se 2 (by rfl) ⟨6038367, by rfl⟩ : syracuseStep 16102313 = 12076735) B12076735
theorem B27169921 : Blo 1674037 27169921 := bstep (se 2 (by rfl) ⟨10188720, by rfl⟩ : syracuseStep 27169921 = 20377441) B20377441
theorem B21746981 : Blo 1674037 21746981 := bstep (se 4 (by rfl) ⟨2038779, by rfl⟩ : syracuseStep 21746981 = 4077559) B4077559
theorem B54334921 : Blo 1674037 54334921 := bstep (se 2 (by rfl) ⟨20375595, by rfl⟩ : syracuseStep 54334921 = 40751191) B40751191
theorem B2119223 : Blo 1674037 2119223 := bstep (se 1 (by rfl) ⟨1589417, by rfl⟩ : syracuseStep 2119223 = 3178835) B3178835
theorem B2512439 : Blo 1674037 2512439 := bstep (se 1 (by rfl) ⟨1884329, by rfl⟩ : syracuseStep 2512439 = 3768659) B3768659
theorem B8484425 : Blo 1674037 8484425 := bstep (se 2 (by rfl) ⟨3181659, by rfl⟩ : syracuseStep 8484425 = 6363319) B6363319
theorem B6362819 : Blo 1674037 6362819 := bstep (se 1 (by rfl) ⟨4772114, by rfl⟩ : syracuseStep 6362819 = 9544229) B9544229
theorem B3577583 : Blo 1674037 3577583 := bstep (se 1 (by rfl) ⟨2683187, by rfl⟩ : syracuseStep 3577583 = 5366375) B5366375
theorem B2512943 : Blo 1674037 2512943 := bstep (se 1 (by rfl) ⟨1884707, by rfl⟩ : syracuseStep 2512943 = 3769415) B3769415
theorem B2513063 : Blo 1674037 2513063 := bstep (se 1 (by rfl) ⟨1884797, by rfl⟩ : syracuseStep 2513063 = 3769595) B3769595
theorem B3766607 : Blo 1674037 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B2513231 : Blo 1674037 2513231 := bstep (se 1 (by rfl) ⟨1884923, by rfl⟩ : syracuseStep 2513231 = 3769847) B3769847
theorem B5651207 : Blo 1674037 5651207 := bstep (se 1 (by rfl) ⟨4238405, by rfl⟩ : syracuseStep 5651207 = 8476811) B8476811
theorem B2824969 : Blo 1674037 2824969 := bstep (se 2 (by rfl) ⟨1059363, by rfl⟩ : syracuseStep 2824969 = 2118727) B2118727
theorem B7158719 : Blo 1674037 7158719 := bstep (se 1 (by rfl) ⟨5369039, by rfl⟩ : syracuseStep 7158719 = 10738079) B10738079
theorem B3767327 : Blo 1674037 3767327 := bstep (se 1 (by rfl) ⟨2825495, by rfl⟩ : syracuseStep 3767327 = 5650991) B5650991
theorem B2513951 : Blo 1674037 2513951 := bstep (se 1 (by rfl) ⟨1885463, by rfl⟩ : syracuseStep 2513951 = 3770927) B3770927
theorem B6356303 : Blo 1674037 6356303 := bstep (se 1 (by rfl) ⟨4767227, by rfl⟩ : syracuseStep 6356303 = 9534455) B9534455
theorem B8715691 : Blo 1674037 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B2121167 : Blo 1674037 2121167 := bstep (se 1 (by rfl) ⟨1590875, by rfl⟩ : syracuseStep 2121167 = 3181751) B3181751
theorem B9534955 : Blo 1674037 9534955 := bstep (se 1 (by rfl) ⟨7151216, by rfl⟩ : syracuseStep 9534955 = 14302433) B14302433
theorem B2825759 : Blo 1674037 2825759 := bstep (se 1 (by rfl) ⟨2119319, by rfl⟩ : syracuseStep 2825759 = 4238639) B4238639
theorem B21462671 : Blo 1674037 21462671 := bstep (se 1 (by rfl) ⟨16097003, by rfl⟩ : syracuseStep 21462671 = 32194007) B32194007
theorem B19070639 : Blo 1674037 19070639 := bstep (se 1 (by rfl) ⟨14302979, by rfl⟩ : syracuseStep 19070639 = 28605959) B28605959
theorem B3768083 : Blo 1674037 3768083 := bstep (se 1 (by rfl) ⟨2826062, by rfl⟩ : syracuseStep 3768083 = 5652125) B5652125
theorem B5652287 : Blo 1674037 5652287 := bstep (se 1 (by rfl) ⟨4239215, by rfl⟩ : syracuseStep 5652287 = 8478431) B8478431
theorem B7151611 : Blo 1674037 7151611 := bstep (se 1 (by rfl) ⟨5363708, by rfl⟩ : syracuseStep 7151611 = 10727417) B10727417
theorem B16547935 : Blo 1674037 16547935 := bstep (se 1 (by rfl) ⟨12410951, by rfl⟩ : syracuseStep 16547935 = 24821903) B24821903
theorem B1909055 : Blo 1674037 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B7151935 : Blo 1674037 7151935 := bstep (se 1 (by rfl) ⟨5363951, by rfl⟩ : syracuseStep 7151935 = 10727903) B10727903
theorem B3768731 : Blo 1674037 3768731 := bstep (se 1 (by rfl) ⟨2826548, by rfl⟩ : syracuseStep 3768731 = 5653097) B5653097
theorem B3179063 : Blo 1674037 3179063 := bstep (se 1 (by rfl) ⟨2384297, by rfl⟩ : syracuseStep 3179063 = 4768595) B4768595
theorem B57991949 : Blo 1674037 57991949 := bstep (se 3 (by rfl) ⟨10873490, by rfl⟩ : syracuseStep 57991949 = 21746981) B21746981
theorem B1884991 : Blo 1674037 1884991 := bstep (se 1 (by rfl) ⟨1413743, by rfl⟩ : syracuseStep 1884991 = 2827487) B2827487
theorem B9798695 : Blo 1674037 9798695 := bstep (se 1 (by rfl) ⟨7349021, by rfl⟩ : syracuseStep 9798695 = 14698043) B14698043
theorem B2385055 : Blo 1674037 2385055 := bstep (se 1 (by rfl) ⟨1788791, by rfl⟩ : syracuseStep 2385055 = 3577583) B3577583
theorem B6358247 : Blo 1674037 6358247 := bstep (se 1 (by rfl) ⟨4768685, by rfl⟩ : syracuseStep 6358247 = 9537371) B9537371
theorem B3769703 : Blo 1674037 3769703 := bstep (se 1 (by rfl) ⟨2827277, by rfl⟩ : syracuseStep 3769703 = 5654555) B5654555
theorem B4769255 : Blo 1674037 4769255 := bstep (se 1 (by rfl) ⟨3576941, by rfl⟩ : syracuseStep 4769255 = 7153883) B7153883
theorem B4237535 : Blo 1674037 4237535 := bstep (se 1 (by rfl) ⟨3178151, by rfl⟩ : syracuseStep 4237535 = 6356303) B6356303
theorem B223283459 : Blo 1674037 223283459 := bstep (se 1 (by rfl) ⟨167462594, by rfl⟩ : syracuseStep 223283459 = 334925189) B334925189
theorem B3180863 : Blo 1674037 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B9537871 : Blo 1674037 9537871 := bstep (se 1 (by rfl) ⟨7153403, by rfl⟩ : syracuseStep 9537871 = 14306807) B14306807
theorem B3770783 : Blo 1674037 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B3181007 : Blo 1674037 3181007 := bstep (se 1 (by rfl) ⟨2385755, by rfl⟩ : syracuseStep 3181007 = 4771511) B4771511
theorem B3770873 : Blo 1674037 3770873 := bstep (se 2 (by rfl) ⟨1414077, by rfl⟩ : syracuseStep 3770873 = 2828155) B2828155
theorem B19073555 : Blo 1674037 19073555 := bstep (se 1 (by rfl) ⟨14305166, by rfl⟩ : syracuseStep 19073555 = 28610333) B28610333
theorem B3771035 : Blo 1674037 3771035 := bstep (se 1 (by rfl) ⟨2828276, by rfl⟩ : syracuseStep 3771035 = 5656553) B5656553
theorem B3771071 : Blo 1674037 3771071 := bstep (se 1 (by rfl) ⟨2828303, by rfl⟩ : syracuseStep 3771071 = 5656607) B5656607
theorem B2263783 : Blo 1674037 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B5655419 : Blo 1674037 5655419 := bstep (se 1 (by rfl) ⟨4241564, by rfl⟩ : syracuseStep 5655419 = 8483129) B8483129
theorem B4238345 : Blo 1674037 4238345 := bstep (se 2 (by rfl) ⟨1589379, by rfl⟩ : syracuseStep 4238345 = 3178759) B3178759
theorem B1674271 : Blo 1674037 1674271 := bstep (se 1 (by rfl) ⟨1255703, by rfl⟩ : syracuseStep 1674271 = 2511407) B2511407
theorem B1674395 : Blo 1674037 1674395 := bstep (se 1 (by rfl) ⟨1255796, by rfl⟩ : syracuseStep 1674395 = 2511593) B2511593
theorem B16092391 : Blo 1674037 16092391 := bstep (se 1 (by rfl) ⟨12069293, by rfl⟩ : syracuseStep 16092391 = 24138587) B24138587
theorem B1674491 : Blo 1674037 1674491 := bstep (se 1 (by rfl) ⟨1255868, by rfl⟩ : syracuseStep 1674491 = 2511737) B2511737
theorem B10734875 : Blo 1674037 10734875 := bstep (se 1 (by rfl) ⟨8051156, by rfl⟩ : syracuseStep 10734875 = 16102313) B16102313
theorem B1674959 : Blo 1674037 1674959 := bstep (se 1 (by rfl) ⟨1256219, by rfl⟩ : syracuseStep 1674959 = 2512439) B2512439
theorem B5656283 : Blo 1674037 5656283 := bstep (se 1 (by rfl) ⟨4242212, by rfl⟩ : syracuseStep 5656283 = 8484425) B8484425
theorem B5656445 : Blo 1674037 5656445 := bstep (se 3 (by rfl) ⟨1060583, by rfl⟩ : syracuseStep 5656445 = 2121167) B2121167
theorem B1675295 : Blo 1674037 1675295 := bstep (se 1 (by rfl) ⟨1256471, by rfl⟩ : syracuseStep 1675295 = 2512943) B2512943
theorem B1675375 : Blo 1674037 1675375 := bstep (se 1 (by rfl) ⟨1256531, by rfl⟩ : syracuseStep 1675375 = 2513063) B2513063
theorem B2511071 : Blo 1674037 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B1675487 : Blo 1674037 1675487 := bstep (se 1 (by rfl) ⟨1256615, by rfl⟩ : syracuseStep 1675487 = 2513231) B2513231
theorem B11620921 : Blo 1674037 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B72446561 : Blo 1674037 72446561 := bstep (se 2 (by rfl) ⟨27167460, by rfl⟩ : syracuseStep 72446561 = 54334921) B54334921
theorem B8483453 : Blo 1674037 8483453 := bstep (se 3 (by rfl) ⟨1590647, by rfl⟩ : syracuseStep 8483453 = 3181295) B3181295
theorem B4772479 : Blo 1674037 4772479 := bstep (se 1 (by rfl) ⟨3579359, by rfl⟩ : syracuseStep 4772479 = 7158719) B7158719
theorem B2511551 : Blo 1674037 2511551 := bstep (se 1 (by rfl) ⟨1883663, by rfl⟩ : syracuseStep 2511551 = 3767327) B3767327
theorem B1675967 : Blo 1674037 1675967 := bstep (se 1 (by rfl) ⟨1256975, by rfl⟩ : syracuseStep 1675967 = 2513951) B2513951
theorem B14308447 : Blo 1674037 14308447 := bstep (se 1 (by rfl) ⟨10731335, by rfl⟩ : syracuseStep 14308447 = 21462671) B21462671
theorem B2512055 : Blo 1674037 2512055 := bstep (se 1 (by rfl) ⟨1884041, by rfl⟩ : syracuseStep 2512055 = 3768083) B3768083
theorem B2512295 : Blo 1674037 2512295 := bstep (se 1 (by rfl) ⟨1884221, by rfl⟩ : syracuseStep 2512295 = 3768443) B3768443
theorem B3397231 : Blo 1674037 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B5650127 : Blo 1674037 5650127 := bstep (se 1 (by rfl) ⟨4237595, by rfl⟩ : syracuseStep 5650127 = 8475191) B8475191
theorem B42948305 : Blo 1674037 42948305 := bstep (se 2 (by rfl) ⟨16105614, by rfl⟩ : syracuseStep 42948305 = 32211229) B32211229
theorem B144906245 : Blo 1674037 144906245 := bstep (se 4 (by rfl) ⟨13584960, by rfl⟩ : syracuseStep 144906245 = 27169921) B27169921
theorem B8050697 : Blo 1674037 8050697 := bstep (se 2 (by rfl) ⟨3019011, by rfl⟩ : syracuseStep 8050697 = 6038023) B6038023
theorem B2513207 : Blo 1674037 2513207 := bstep (se 1 (by rfl) ⟨1884905, by rfl⟩ : syracuseStep 2513207 = 3769811) B3769811
theorem B3766625 : Blo 1674037 3766625 := bstep (se 2 (by rfl) ⟨1412484, by rfl⟩ : syracuseStep 3766625 = 2824969) B2824969
theorem B2513255 : Blo 1674037 2513255 := bstep (se 1 (by rfl) ⟨1884941, by rfl⟩ : syracuseStep 2513255 = 3769883) B3769883
theorem B4241879 : Blo 1674037 4241879 := bstep (se 1 (by rfl) ⟨3181409, by rfl⟩ : syracuseStep 4241879 = 6362819) B6362819
theorem B5650937 : Blo 1674037 5650937 := bstep (se 2 (by rfl) ⟨2119101, by rfl⟩ : syracuseStep 5650937 = 4238203) B4238203
theorem B5651261 : Blo 1674037 5651261 := bstep (se 3 (by rfl) ⟨1059611, by rfl⟩ : syracuseStep 5651261 = 2119223) B2119223
theorem B2546791 : Blo 1674037 2546791 := bstep (se 1 (by rfl) ⟨1910093, by rfl⟩ : syracuseStep 2546791 = 3820187) B3820187
theorem B3767471 : Blo 1674037 3767471 := bstep (se 1 (by rfl) ⟨2825603, by rfl⟩ : syracuseStep 3767471 = 5651207) B5651207
theorem B8477945 : Blo 1674037 8477945 := bstep (se 2 (by rfl) ⟨3179229, by rfl⟩ : syracuseStep 8477945 = 6358459) B6358459
theorem B12713273 : Blo 1674037 12713273 := bstep (se 2 (by rfl) ⟨4767477, by rfl⟩ : syracuseStep 12713273 = 9534955) B9534955
theorem B1883839 : Blo 1674037 1883839 := bstep (se 1 (by rfl) ⟨1412879, by rfl⟩ : syracuseStep 1883839 = 2825759) B2825759
theorem B18112247 : Blo 1674037 18112247 := bstep (se 1 (by rfl) ⟨13584185, by rfl⟩ : syracuseStep 18112247 = 27168371) B27168371
theorem B5652233 : Blo 1674037 5652233 := bstep (se 2 (by rfl) ⟨2119587, by rfl⟩ : syracuseStep 5652233 = 4239175) B4239175
theorem B12713759 : Blo 1674037 12713759 := bstep (se 1 (by rfl) ⟨9535319, by rfl⟩ : syracuseStep 12713759 = 19070639) B19070639
theorem B3768191 : Blo 1674037 3768191 := bstep (se 1 (by rfl) ⟨2826143, by rfl⟩ : syracuseStep 3768191 = 5652287) B5652287
theorem B9535481 : Blo 1674037 9535481 := bstep (se 2 (by rfl) ⟨3575805, by rfl⟩ : syracuseStep 9535481 = 7151611) B7151611
theorem B9535913 : Blo 1674037 9535913 := bstep (se 2 (by rfl) ⟨3575967, by rfl⟩ : syracuseStep 9535913 = 7151935) B7151935
theorem B13582885 : Blo 1674037 13582885 := bstep (se 4 (by rfl) ⟨1273395, by rfl⟩ : syracuseStep 13582885 = 2546791) B2546791
theorem B3179503 : Blo 1674037 3179503 := bstep (se 1 (by rfl) ⟨2384627, by rfl⟩ : syracuseStep 3179503 = 4769255) B4769255
theorem B28632203 : Blo 1674037 28632203 := bstep (se 1 (by rfl) ⟨21474152, by rfl⟩ : syracuseStep 28632203 = 42948305) B42948305
theorem B5367131 : Blo 1674037 5367131 := bstep (se 1 (by rfl) ⟨4025348, by rfl⟩ : syracuseStep 5367131 = 8050697) B8050697
theorem B3180073 : Blo 1674037 3180073 := bstep (se 2 (by rfl) ⟨1192527, by rfl⟩ : syracuseStep 3180073 = 2385055) B2385055
theorem B21456521 : Blo 1674037 21456521 := bstep (se 2 (by rfl) ⟨8046195, by rfl⟩ : syracuseStep 21456521 = 16092391) B16092391
theorem B2827919 : Blo 1674037 2827919 := bstep (se 1 (by rfl) ⟨2120939, by rfl⟩ : syracuseStep 2827919 = 4241879) B4241879
theorem B12715703 : Blo 1674037 12715703 := bstep (se 1 (by rfl) ⟨9536777, by rfl⟩ : syracuseStep 12715703 = 19073555) B19073555
theorem B3770279 : Blo 1674037 3770279 := bstep (se 1 (by rfl) ⟨2827709, by rfl⟩ : syracuseStep 3770279 = 5655419) B5655419
theorem B6356987 : Blo 1674037 6356987 := bstep (se 1 (by rfl) ⟨4767740, by rfl⟩ : syracuseStep 6356987 = 9535481) B9535481
theorem B3770855 : Blo 1674037 3770855 := bstep (se 1 (by rfl) ⟨2828141, by rfl⟩ : syracuseStep 3770855 = 5656283) B5656283
theorem B3770963 : Blo 1674037 3770963 := bstep (se 1 (by rfl) ⟨2828222, by rfl⟩ : syracuseStep 3770963 = 5656445) B5656445
theorem B22063913 : Blo 1674037 22063913 := bstep (se 2 (by rfl) ⟨8273967, by rfl⟩ : syracuseStep 22063913 = 16547935) B16547935
theorem B1674047 : Blo 1674037 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B5655635 : Blo 1674037 5655635 := bstep (se 1 (by rfl) ⟨4241726, by rfl⟩ : syracuseStep 5655635 = 8483453) B8483453
theorem B12717161 : Blo 1674037 12717161 := bstep (se 2 (by rfl) ⟨4768935, by rfl⟩ : syracuseStep 12717161 = 9537871) B9537871
theorem B1674367 : Blo 1674037 1674367 := bstep (se 1 (by rfl) ⟨1255775, by rfl⟩ : syracuseStep 1674367 = 2511551) B2511551
theorem B38661299 : Blo 1674037 38661299 := bstep (se 1 (by rfl) ⟨28995974, by rfl⟩ : syracuseStep 38661299 = 57991949) B57991949
theorem B6532463 : Blo 1674037 6532463 := bstep (se 1 (by rfl) ⟨4899347, by rfl⟩ : syracuseStep 6532463 = 9798695) B9798695
theorem B15494561 : Blo 1674037 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B1674703 : Blo 1674037 1674703 := bstep (se 1 (by rfl) ⟨1256027, by rfl⟩ : syracuseStep 1674703 = 2512055) B2512055
theorem B4238831 : Blo 1674037 4238831 := bstep (se 1 (by rfl) ⟨3179123, by rfl⟩ : syracuseStep 4238831 = 6358247) B6358247
theorem B5090813 : Blo 1674037 5090813 := bstep (se 3 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 5090813 = 1909055) B1909055
theorem B1674863 : Blo 1674037 1674863 := bstep (se 1 (by rfl) ⟨1256147, by rfl⟩ : syracuseStep 1674863 = 2512295) B2512295
theorem B3018377 : Blo 1674037 3018377 := bstep (se 2 (by rfl) ⟨1131891, by rfl⟩ : syracuseStep 3018377 = 2263783) B2263783
theorem B96604163 : Blo 1674037 96604163 := bstep (se 1 (by rfl) ⟨72453122, by rfl⟩ : syracuseStep 96604163 = 144906245) B144906245
theorem B1675471 : Blo 1674037 1675471 := bstep (se 1 (by rfl) ⟨1256603, by rfl⟩ : syracuseStep 1675471 = 2513207) B2513207
theorem B2511083 : Blo 1674037 2511083 := bstep (se 1 (by rfl) ⟨1883312, by rfl⟩ : syracuseStep 2511083 = 3766625) B3766625
theorem B1675503 : Blo 1674037 1675503 := bstep (se 1 (by rfl) ⟨1256627, by rfl⟩ : syracuseStep 1675503 = 2513255) B2513255
theorem B2511647 : Blo 1674037 2511647 := bstep (se 1 (by rfl) ⟨1883735, by rfl⟩ : syracuseStep 2511647 = 3767471) B3767471
theorem B7156583 : Blo 1674037 7156583 := bstep (se 1 (by rfl) ⟨5367437, by rfl⟩ : syracuseStep 7156583 = 10734875) B10734875
theorem B8475515 : Blo 1674037 8475515 := bstep (se 1 (by rfl) ⟨6356636, by rfl⟩ : syracuseStep 8475515 = 12713273) B12713273
theorem B2511785 : Blo 1674037 2511785 := bstep (se 2 (by rfl) ⟨941919, by rfl⟩ : syracuseStep 2511785 = 1883839) B1883839
theorem B8475839 : Blo 1674037 8475839 := bstep (se 1 (by rfl) ⟨6356879, by rfl⟩ : syracuseStep 8475839 = 12713759) B12713759
theorem B2512127 : Blo 1674037 2512127 := bstep (se 1 (by rfl) ⟨1884095, by rfl⟩ : syracuseStep 2512127 = 3768191) B3768191
theorem B2512487 : Blo 1674037 2512487 := bstep (se 1 (by rfl) ⟨1884365, by rfl⟩ : syracuseStep 2512487 = 3768731) B3768731
theorem B2119375 : Blo 1674037 2119375 := bstep (se 1 (by rfl) ⟨1589531, by rfl⟩ : syracuseStep 2119375 = 3179063) B3179063
theorem B48297707 : Blo 1674037 48297707 := bstep (se 1 (by rfl) ⟨36223280, by rfl⟩ : syracuseStep 48297707 = 72446561) B72446561
theorem B18118565 : Blo 1674037 18118565 := bstep (se 4 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 18118565 = 3397231) B3397231
theorem B6363305 : Blo 1674037 6363305 := bstep (se 2 (by rfl) ⟨2386239, by rfl⟩ : syracuseStep 6363305 = 4772479) B4772479
theorem B2513135 : Blo 1674037 2513135 := bstep (se 1 (by rfl) ⟨1884851, by rfl⟩ : syracuseStep 2513135 = 3769703) B3769703
theorem B2513321 : Blo 1674037 2513321 := bstep (se 2 (by rfl) ⟨942495, by rfl⟩ : syracuseStep 2513321 = 1884991) B1884991
theorem B3766751 : Blo 1674037 3766751 := bstep (se 1 (by rfl) ⟨2825063, by rfl⟩ : syracuseStep 3766751 = 5650127) B5650127
theorem B19077929 : Blo 1674037 19077929 := bstep (se 2 (by rfl) ⟨7154223, by rfl⟩ : syracuseStep 19077929 = 14308447) B14308447
theorem B2825023 : Blo 1674037 2825023 := bstep (se 1 (by rfl) ⟨2118767, by rfl⟩ : syracuseStep 2825023 = 4237535) B4237535
theorem B148855639 : Blo 1674037 148855639 := bstep (se 1 (by rfl) ⟨111641729, by rfl⟩ : syracuseStep 148855639 = 223283459) B223283459
theorem B2120575 : Blo 1674037 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B2513855 : Blo 1674037 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B2120671 : Blo 1674037 2120671 := bstep (se 1 (by rfl) ⟨1590503, by rfl⟩ : syracuseStep 2120671 = 3181007) B3181007
theorem B3767291 : Blo 1674037 3767291 := bstep (se 1 (by rfl) ⟨2825468, by rfl⟩ : syracuseStep 3767291 = 5650937) B5650937
theorem B2513915 : Blo 1674037 2513915 := bstep (se 1 (by rfl) ⟨1885436, by rfl⟩ : syracuseStep 2513915 = 3770873) B3770873
theorem B2514023 : Blo 1674037 2514023 := bstep (se 1 (by rfl) ⟨1885517, by rfl⟩ : syracuseStep 2514023 = 3771035) B3771035
theorem B2514047 : Blo 1674037 2514047 := bstep (se 1 (by rfl) ⟨1885535, by rfl⟩ : syracuseStep 2514047 = 3771071) B3771071
theorem B3767507 : Blo 1674037 3767507 := bstep (se 1 (by rfl) ⟨2825630, by rfl⟩ : syracuseStep 3767507 = 5651261) B5651261
theorem B2825563 : Blo 1674037 2825563 := bstep (se 1 (by rfl) ⟨2119172, by rfl⟩ : syracuseStep 2825563 = 4238345) B4238345
theorem B5651963 : Blo 1674037 5651963 := bstep (se 1 (by rfl) ⟨4238972, by rfl⟩ : syracuseStep 5651963 = 8477945) B8477945
theorem B12074831 : Blo 1674037 12074831 := bstep (se 1 (by rfl) ⟨9056123, by rfl⟩ : syracuseStep 12074831 = 18112247) B18112247
theorem B3768155 : Blo 1674037 3768155 := bstep (se 1 (by rfl) ⟨2826116, by rfl⟩ : syracuseStep 3768155 = 5652233) B5652233
theorem B6357275 : Blo 1674037 6357275 := bstep (se 1 (by rfl) ⟨4767956, by rfl⟩ : syracuseStep 6357275 = 9535913) B9535913
theorem B19088135 : Blo 1674037 19088135 := bstep (se 1 (by rfl) ⟨14316101, by rfl⟩ : syracuseStep 19088135 = 28632203) B28632203
theorem B14304347 : Blo 1674037 14304347 := bstep (se 1 (by rfl) ⟨10728260, by rfl⟩ : syracuseStep 14304347 = 21456521) B21456521
theorem B1885279 : Blo 1674037 1885279 := bstep (se 1 (by rfl) ⟨1413959, by rfl⟩ : syracuseStep 1885279 = 2827919) B2827919
theorem B2827433 : Blo 1674037 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B2827561 : Blo 1674037 2827561 := bstep (se 2 (by rfl) ⟨1060335, by rfl⟩ : syracuseStep 2827561 = 2120671) B2120671
theorem B3770423 : Blo 1674037 3770423 := bstep (se 1 (by rfl) ⟨2827817, by rfl⟩ : syracuseStep 3770423 = 5655635) B5655635
theorem B25774199 : Blo 1674037 25774199 := bstep (se 1 (by rfl) ⟨19330649, by rfl⟩ : syracuseStep 25774199 = 38661299) B38661299
theorem B3393875 : Blo 1674037 3393875 := bstep (se 1 (by rfl) ⟨2545406, by rfl⟩ : syracuseStep 3393875 = 5090813) B5090813
theorem B4237991 : Blo 1674037 4237991 := bstep (se 1 (by rfl) ⟨3178493, by rfl⟩ : syracuseStep 4237991 = 6356987) B6356987
theorem B1674055 : Blo 1674037 1674055 := bstep (se 1 (by rfl) ⟨1255541, by rfl⟩ : syracuseStep 1674055 = 2511083) B2511083
theorem B1674431 : Blo 1674037 1674431 := bstep (se 1 (by rfl) ⟨1255823, by rfl⟩ : syracuseStep 1674431 = 2511647) B2511647
theorem B4771055 : Blo 1674037 4771055 := bstep (se 1 (by rfl) ⟨3578291, by rfl⟩ : syracuseStep 4771055 = 7156583) B7156583
theorem B1674523 : Blo 1674037 1674523 := bstep (se 1 (by rfl) ⟨1255892, by rfl⟩ : syracuseStep 1674523 = 2511785) B2511785
theorem B1674751 : Blo 1674037 1674751 := bstep (se 1 (by rfl) ⟨1256063, by rfl⟩ : syracuseStep 1674751 = 2512127) B2512127
theorem B1674991 : Blo 1674037 1674991 := bstep (se 1 (by rfl) ⟨1256243, by rfl⟩ : syracuseStep 1674991 = 2512487) B2512487
theorem B32198471 : Blo 1674037 32198471 := bstep (se 1 (by rfl) ⟨24148853, by rfl⟩ : syracuseStep 32198471 = 48297707) B48297707
theorem B12079043 : Blo 1674037 12079043 := bstep (se 1 (by rfl) ⟨9059282, by rfl⟩ : syracuseStep 12079043 = 18118565) B18118565
theorem B4239337 : Blo 1674037 4239337 := bstep (se 2 (by rfl) ⟨1589751, by rfl⟩ : syracuseStep 4239337 = 3179503) B3179503
theorem B1675423 : Blo 1674037 1675423 := bstep (se 1 (by rfl) ⟨1256567, by rfl⟩ : syracuseStep 1675423 = 2513135) B2513135
theorem B1675547 : Blo 1674037 1675547 := bstep (se 1 (by rfl) ⟨1256660, by rfl⟩ : syracuseStep 1675547 = 2513321) B2513321
theorem B2511167 : Blo 1674037 2511167 := bstep (se 1 (by rfl) ⟨1883375, by rfl⟩ : syracuseStep 2511167 = 3766751) B3766751
theorem B12718619 : Blo 1674037 12718619 := bstep (se 1 (by rfl) ⟨9538964, by rfl⟩ : syracuseStep 12718619 = 19077929) B19077929
theorem B14709275 : Blo 1674037 14709275 := bstep (se 1 (by rfl) ⟨11031956, by rfl⟩ : syracuseStep 14709275 = 22063913) B22063913
theorem B1675903 : Blo 1674037 1675903 := bstep (se 1 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 1675903 = 2513855) B2513855
theorem B2511527 : Blo 1674037 2511527 := bstep (se 1 (by rfl) ⟨1883645, by rfl⟩ : syracuseStep 2511527 = 3767291) B3767291
theorem B1675943 : Blo 1674037 1675943 := bstep (se 1 (by rfl) ⟨1256957, by rfl⟩ : syracuseStep 1675943 = 2513915) B2513915
theorem B4240097 : Blo 1674037 4240097 := bstep (se 2 (by rfl) ⟨1590036, by rfl⟩ : syracuseStep 4240097 = 3180073) B3180073
theorem B1676015 : Blo 1674037 1676015 := bstep (se 1 (by rfl) ⟨1257011, by rfl⟩ : syracuseStep 1676015 = 2514023) B2514023
theorem B1676031 : Blo 1674037 1676031 := bstep (se 1 (by rfl) ⟨1257023, by rfl⟩ : syracuseStep 1676031 = 2514047) B2514047
theorem B2511671 : Blo 1674037 2511671 := bstep (se 1 (by rfl) ⟨1883753, by rfl⟩ : syracuseStep 2511671 = 3767507) B3767507
theorem B4354975 : Blo 1674037 4354975 := bstep (se 1 (by rfl) ⟨3266231, by rfl⟩ : syracuseStep 4354975 = 6532463) B6532463
theorem B2012251 : Blo 1674037 2012251 := bstep (se 1 (by rfl) ⟨1509188, by rfl⟩ : syracuseStep 2012251 = 3018377) B3018377
theorem B8049887 : Blo 1674037 8049887 := bstep (se 1 (by rfl) ⟨6037415, by rfl⟩ : syracuseStep 8049887 = 12074831) B12074831
theorem B2512103 : Blo 1674037 2512103 := bstep (se 1 (by rfl) ⟨1884077, by rfl⟩ : syracuseStep 2512103 = 3768155) B3768155
theorem B64402775 : Blo 1674037 64402775 := bstep (se 1 (by rfl) ⟨48302081, by rfl⟩ : syracuseStep 64402775 = 96604163) B96604163
theorem B5650343 : Blo 1674037 5650343 := bstep (se 1 (by rfl) ⟨4237757, by rfl⟩ : syracuseStep 5650343 = 8475515) B8475515
theorem B18110513 : Blo 1674037 18110513 := bstep (se 2 (by rfl) ⟨6791442, by rfl⟩ : syracuseStep 18110513 = 13582885) B13582885
theorem B5650559 : Blo 1674037 5650559 := bstep (se 1 (by rfl) ⟨4237919, by rfl⟩ : syracuseStep 5650559 = 8475839) B8475839
theorem B3578087 : Blo 1674037 3578087 := bstep (se 1 (by rfl) ⟨2683565, by rfl⟩ : syracuseStep 3578087 = 5367131) B5367131
theorem B3766697 : Blo 1674037 3766697 := bstep (se 2 (by rfl) ⟨1412511, by rfl⟩ : syracuseStep 3766697 = 2825023) B2825023
theorem B198474185 : Blo 1674037 198474185 := bstep (se 2 (by rfl) ⟨74427819, by rfl⟩ : syracuseStep 198474185 = 148855639) B148855639
theorem B8477135 : Blo 1674037 8477135 := bstep (se 1 (by rfl) ⟨6357851, by rfl⟩ : syracuseStep 8477135 = 12715703) B12715703
theorem B2513519 : Blo 1674037 2513519 := bstep (se 1 (by rfl) ⟨1885139, by rfl⟩ : syracuseStep 2513519 = 3770279) B3770279
theorem B4242203 : Blo 1674037 4242203 := bstep (se 1 (by rfl) ⟨3181652, by rfl⟩ : syracuseStep 4242203 = 6363305) B6363305
theorem B2513903 : Blo 1674037 2513903 := bstep (se 1 (by rfl) ⟨1885427, by rfl⟩ : syracuseStep 2513903 = 3770855) B3770855
theorem B2513975 : Blo 1674037 2513975 := bstep (se 1 (by rfl) ⟨1885481, by rfl⟩ : syracuseStep 2513975 = 3770963) B3770963
theorem B3767417 : Blo 1674037 3767417 := bstep (se 2 (by rfl) ⟨1412781, by rfl⟩ : syracuseStep 3767417 = 2825563) B2825563
theorem B8478107 : Blo 1674037 8478107 := bstep (se 1 (by rfl) ⟨6358580, by rfl⟩ : syracuseStep 8478107 = 12717161) B12717161
theorem B2825833 : Blo 1674037 2825833 := bstep (se 2 (by rfl) ⟨1059687, by rfl⟩ : syracuseStep 2825833 = 2119375) B2119375
theorem B10329707 : Blo 1674037 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B2825887 : Blo 1674037 2825887 := bstep (se 1 (by rfl) ⟨2119415, by rfl⟩ : syracuseStep 2825887 = 4238831) B4238831
theorem B3767975 : Blo 1674037 3767975 := bstep (se 1 (by rfl) ⟨2825981, by rfl⟩ : syracuseStep 3767975 = 5651963) B5651963
theorem B8479079 : Blo 1674037 8479079 := bstep (se 1 (by rfl) ⟨6359309, by rfl⟩ : syracuseStep 8479079 = 12718619) B12718619
theorem B9806183 : Blo 1674037 9806183 := bstep (se 1 (by rfl) ⟨7354637, by rfl⟩ : syracuseStep 9806183 = 14709275) B14709275
theorem B2826731 : Blo 1674037 2826731 := bstep (se 1 (by rfl) ⟨2120048, by rfl⟩ : syracuseStep 2826731 = 4240097) B4240097
theorem B9536231 : Blo 1674037 9536231 := bstep (se 1 (by rfl) ⟨7152173, by rfl⟩ : syracuseStep 9536231 = 14304347) B14304347
theorem B1884955 : Blo 1674037 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B5366591 : Blo 1674037 5366591 := bstep (se 1 (by rfl) ⟨4024943, by rfl⟩ : syracuseStep 5366591 = 8049887) B8049887
theorem B42935183 : Blo 1674037 42935183 := bstep (se 1 (by rfl) ⟨32201387, by rfl⟩ : syracuseStep 42935183 = 64402775) B64402775
theorem B2385391 : Blo 1674037 2385391 := bstep (se 1 (by rfl) ⟨1789043, by rfl⟩ : syracuseStep 2385391 = 3578087) B3578087
theorem B2262583 : Blo 1674037 2262583 := bstep (se 1 (by rfl) ⟨1696937, by rfl⟩ : syracuseStep 2262583 = 3393875) B3393875
theorem B3770081 : Blo 1674037 3770081 := bstep (se 2 (by rfl) ⟨1413780, by rfl⟩ : syracuseStep 3770081 = 2827561) B2827561
theorem B2828135 : Blo 1674037 2828135 := bstep (se 1 (by rfl) ⟨2121101, by rfl⟩ : syracuseStep 2828135 = 4242203) B4242203
theorem B3180703 : Blo 1674037 3180703 := bstep (se 1 (by rfl) ⟨2385527, by rfl⟩ : syracuseStep 3180703 = 4771055) B4771055
theorem B23226533 : Blo 1674037 23226533 := bstep (se 4 (by rfl) ⟨2177487, by rfl⟩ : syracuseStep 23226533 = 4354975) B4354975
theorem B21465647 : Blo 1674037 21465647 := bstep (se 1 (by rfl) ⟨16099235, by rfl⟩ : syracuseStep 21465647 = 32198471) B32198471
theorem B48294701 : Blo 1674037 48294701 := bstep (se 3 (by rfl) ⟨9055256, by rfl⟩ : syracuseStep 48294701 = 18110513) B18110513
theorem B4238183 : Blo 1674037 4238183 := bstep (se 1 (by rfl) ⟨3178637, by rfl⟩ : syracuseStep 4238183 = 6357275) B6357275
theorem B1674111 : Blo 1674037 1674111 := bstep (se 1 (by rfl) ⟨1255583, by rfl⟩ : syracuseStep 1674111 = 2511167) B2511167
theorem B1674351 : Blo 1674037 1674351 := bstep (se 1 (by rfl) ⟨1255763, by rfl⟩ : syracuseStep 1674351 = 2511527) B2511527
theorem B12725423 : Blo 1674037 12725423 := bstep (se 1 (by rfl) ⟨9544067, by rfl⟩ : syracuseStep 12725423 = 19088135) B19088135
theorem B1674447 : Blo 1674037 1674447 := bstep (se 1 (by rfl) ⟨1255835, by rfl⟩ : syracuseStep 1674447 = 2511671) B2511671
theorem B1674735 : Blo 1674037 1674735 := bstep (se 1 (by rfl) ⟨1256051, by rfl⟩ : syracuseStep 1674735 = 2512103) B2512103
theorem B17182799 : Blo 1674037 17182799 := bstep (se 1 (by rfl) ⟨12887099, by rfl⟩ : syracuseStep 17182799 = 25774199) B25774199
theorem B2683001 : Blo 1674037 2683001 := bstep (se 2 (by rfl) ⟨1006125, by rfl⟩ : syracuseStep 2683001 = 2012251) B2012251
theorem B2511131 : Blo 1674037 2511131 := bstep (se 1 (by rfl) ⟨1883348, by rfl⟩ : syracuseStep 2511131 = 3766697) B3766697
theorem B1675679 : Blo 1674037 1675679 := bstep (se 1 (by rfl) ⟨1256759, by rfl⟩ : syracuseStep 1675679 = 2513519) B2513519
theorem B1675935 : Blo 1674037 1675935 := bstep (se 1 (by rfl) ⟨1256951, by rfl⟩ : syracuseStep 1675935 = 2513903) B2513903
theorem B1675983 : Blo 1674037 1675983 := bstep (se 1 (by rfl) ⟨1256987, by rfl⟩ : syracuseStep 1675983 = 2513975) B2513975
theorem B2511611 : Blo 1674037 2511611 := bstep (se 1 (by rfl) ⟨1883708, by rfl⟩ : syracuseStep 2511611 = 3767417) B3767417
theorem B6886471 : Blo 1674037 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B2511983 : Blo 1674037 2511983 := bstep (se 1 (by rfl) ⟨1883987, by rfl⟩ : syracuseStep 2511983 = 3767975) B3767975
theorem B3766895 : Blo 1674037 3766895 := bstep (se 1 (by rfl) ⟨2825171, by rfl⟩ : syracuseStep 3766895 = 5650343) B5650343
theorem B2513615 : Blo 1674037 2513615 := bstep (se 1 (by rfl) ⟨1885211, by rfl⟩ : syracuseStep 2513615 = 3770423) B3770423
theorem B3767039 : Blo 1674037 3767039 := bstep (se 1 (by rfl) ⟨2825279, by rfl⟩ : syracuseStep 3767039 = 5650559) B5650559
theorem B2513705 : Blo 1674037 2513705 := bstep (se 2 (by rfl) ⟨942639, by rfl⟩ : syracuseStep 2513705 = 1885279) B1885279
theorem B132316123 : Blo 1674037 132316123 := bstep (se 1 (by rfl) ⟨99237092, by rfl⟩ : syracuseStep 132316123 = 198474185) B198474185
theorem B5651423 : Blo 1674037 5651423 := bstep (se 1 (by rfl) ⟨4238567, by rfl⟩ : syracuseStep 5651423 = 8477135) B8477135
theorem B2825327 : Blo 1674037 2825327 := bstep (se 1 (by rfl) ⟨2118995, by rfl⟩ : syracuseStep 2825327 = 4237991) B4237991
theorem B3767777 : Blo 1674037 3767777 := bstep (se 2 (by rfl) ⟨1412916, by rfl⟩ : syracuseStep 3767777 = 2825833) B2825833
theorem B3767849 : Blo 1674037 3767849 := bstep (se 2 (by rfl) ⟨1412943, by rfl⟩ : syracuseStep 3767849 = 2825887) B2825887
theorem B5652071 : Blo 1674037 5652071 := bstep (se 1 (by rfl) ⟨4239053, by rfl⟩ : syracuseStep 5652071 = 8478107) B8478107
theorem B8052695 : Blo 1674037 8052695 := bstep (se 1 (by rfl) ⟨6039521, by rfl⟩ : syracuseStep 8052695 = 12079043) B12079043
theorem B5652449 : Blo 1674037 5652449 := bstep (se 2 (by rfl) ⟨2119668, by rfl⟩ : syracuseStep 5652449 = 4239337) B4239337
theorem B5652719 : Blo 1674037 5652719 := bstep (se 1 (by rfl) ⟨4239539, by rfl⟩ : syracuseStep 5652719 = 8479079) B8479079
theorem B6537455 : Blo 1674037 6537455 := bstep (se 1 (by rfl) ⟨4903091, by rfl⟩ : syracuseStep 6537455 = 9806183) B9806183
theorem B1884487 : Blo 1674037 1884487 := bstep (se 1 (by rfl) ⟨1413365, by rfl⟩ : syracuseStep 1884487 = 2826731) B2826731
theorem B6357487 : Blo 1674037 6357487 := bstep (se 1 (by rfl) ⟨4768115, by rfl⟩ : syracuseStep 6357487 = 9536231) B9536231
theorem B28623455 : Blo 1674037 28623455 := bstep (se 1 (by rfl) ⟨21467591, by rfl⟩ : syracuseStep 28623455 = 42935183) B42935183
theorem B1885423 : Blo 1674037 1885423 := bstep (se 1 (by rfl) ⟨1414067, by rfl⟩ : syracuseStep 1885423 = 2828135) B2828135
theorem B15484355 : Blo 1674037 15484355 := bstep (se 1 (by rfl) ⟨11613266, by rfl⟩ : syracuseStep 15484355 = 23226533) B23226533
theorem B32196467 : Blo 1674037 32196467 := bstep (se 1 (by rfl) ⟨24147350, by rfl⟩ : syracuseStep 32196467 = 48294701) B48294701
theorem B3180521 : Blo 1674037 3180521 := bstep (se 2 (by rfl) ⟨1192695, by rfl⟩ : syracuseStep 3180521 = 2385391) B2385391
theorem B3016777 : Blo 1674037 3016777 := bstep (se 2 (by rfl) ⟨1131291, by rfl⟩ : syracuseStep 3016777 = 2262583) B2262583
theorem B5368463 : Blo 1674037 5368463 := bstep (se 1 (by rfl) ⟨4026347, by rfl⟩ : syracuseStep 5368463 = 8052695) B8052695
theorem B11455199 : Blo 1674037 11455199 := bstep (se 1 (by rfl) ⟨8591399, by rfl⟩ : syracuseStep 11455199 = 17182799) B17182799
theorem B1674087 : Blo 1674037 1674087 := bstep (se 1 (by rfl) ⟨1255565, by rfl⟩ : syracuseStep 1674087 = 2511131) B2511131
theorem B7154669 : Blo 1674037 7154669 := bstep (se 3 (by rfl) ⟨1341500, by rfl⟩ : syracuseStep 7154669 = 2683001) B2683001
theorem B1674407 : Blo 1674037 1674407 := bstep (se 1 (by rfl) ⟨1255805, by rfl⟩ : syracuseStep 1674407 = 2511611) B2511611
theorem B1674655 : Blo 1674037 1674655 := bstep (se 1 (by rfl) ⟨1255991, by rfl⟩ : syracuseStep 1674655 = 2511983) B2511983
theorem B2511263 : Blo 1674037 2511263 := bstep (se 1 (by rfl) ⟨1883447, by rfl⟩ : syracuseStep 2511263 = 3766895) B3766895
theorem B1675743 : Blo 1674037 1675743 := bstep (se 1 (by rfl) ⟨1256807, by rfl⟩ : syracuseStep 1675743 = 2513615) B2513615
theorem B2511359 : Blo 1674037 2511359 := bstep (se 1 (by rfl) ⟨1883519, by rfl⟩ : syracuseStep 2511359 = 3767039) B3767039
theorem B1675803 : Blo 1674037 1675803 := bstep (se 1 (by rfl) ⟨1256852, by rfl⟩ : syracuseStep 1675803 = 2513705) B2513705
theorem B8483615 : Blo 1674037 8483615 := bstep (se 1 (by rfl) ⟨6362711, by rfl⟩ : syracuseStep 8483615 = 12725423) B12725423
theorem B2511851 : Blo 1674037 2511851 := bstep (se 1 (by rfl) ⟨1883888, by rfl⟩ : syracuseStep 2511851 = 3767777) B3767777
theorem B2511899 : Blo 1674037 2511899 := bstep (se 1 (by rfl) ⟨1883924, by rfl⟩ : syracuseStep 2511899 = 3767849) B3767849
theorem B4240937 : Blo 1674037 4240937 := bstep (se 2 (by rfl) ⟨1590351, by rfl⟩ : syracuseStep 4240937 = 3180703) B3180703
theorem B3577727 : Blo 1674037 3577727 := bstep (se 1 (by rfl) ⟨2683295, by rfl⟩ : syracuseStep 3577727 = 5366591) B5366591
theorem B2513273 : Blo 1674037 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B2513387 : Blo 1674037 2513387 := bstep (se 1 (by rfl) ⟨1885040, by rfl⟩ : syracuseStep 2513387 = 3770081) B3770081
theorem B176421497 : Blo 1674037 176421497 := bstep (se 2 (by rfl) ⟨66158061, by rfl⟩ : syracuseStep 176421497 = 132316123) B132316123
theorem B9181961 : Blo 1674037 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B14310431 : Blo 1674037 14310431 := bstep (se 1 (by rfl) ⟨10732823, by rfl⟩ : syracuseStep 14310431 = 21465647) B21465647
theorem B2825455 : Blo 1674037 2825455 := bstep (se 1 (by rfl) ⟨2119091, by rfl⟩ : syracuseStep 2825455 = 4238183) B4238183
theorem B3767615 : Blo 1674037 3767615 := bstep (se 1 (by rfl) ⟨2825711, by rfl⟩ : syracuseStep 3767615 = 5651423) B5651423
theorem B1883551 : Blo 1674037 1883551 := bstep (se 1 (by rfl) ⟨1412663, by rfl⟩ : syracuseStep 1883551 = 2825327) B2825327
theorem B3768047 : Blo 1674037 3768047 := bstep (se 1 (by rfl) ⟨2826035, by rfl⟩ : syracuseStep 3768047 = 5652071) B5652071
theorem B3768299 : Blo 1674037 3768299 := bstep (se 1 (by rfl) ⟨2826224, by rfl⟩ : syracuseStep 3768299 = 5652449) B5652449
theorem B4022369 : Blo 1674037 4022369 := bstep (se 2 (by rfl) ⟨1508388, by rfl⟩ : syracuseStep 4022369 = 3016777) B3016777
theorem B3768479 : Blo 1674037 3768479 := bstep (se 1 (by rfl) ⟨2826359, by rfl⟩ : syracuseStep 3768479 = 5652719) B5652719
theorem B4358303 : Blo 1674037 4358303 := bstep (se 1 (by rfl) ⟨3268727, by rfl⟩ : syracuseStep 4358303 = 6537455) B6537455
theorem B10322903 : Blo 1674037 10322903 := bstep (se 1 (by rfl) ⟨7742177, by rfl⟩ : syracuseStep 10322903 = 15484355) B15484355
theorem B2827291 : Blo 1674037 2827291 := bstep (se 1 (by rfl) ⟨2120468, by rfl⟩ : syracuseStep 2827291 = 4240937) B4240937
theorem B21464311 : Blo 1674037 21464311 := bstep (se 1 (by rfl) ⟨16098233, by rfl⟩ : syracuseStep 21464311 = 32196467) B32196467
theorem B7636799 : Blo 1674037 7636799 := bstep (se 1 (by rfl) ⟨5727599, by rfl⟩ : syracuseStep 7636799 = 11455199) B11455199
theorem B6121307 : Blo 1674037 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B4769779 : Blo 1674037 4769779 := bstep (se 1 (by rfl) ⟨3577334, by rfl⟩ : syracuseStep 4769779 = 7154669) B7154669
theorem B1674175 : Blo 1674037 1674175 := bstep (se 1 (by rfl) ⟨1255631, by rfl⟩ : syracuseStep 1674175 = 2511263) B2511263
theorem B1674239 : Blo 1674037 1674239 := bstep (se 1 (by rfl) ⟨1255679, by rfl⟩ : syracuseStep 1674239 = 2511359) B2511359
theorem B19082303 : Blo 1674037 19082303 := bstep (se 1 (by rfl) ⟨14311727, by rfl⟩ : syracuseStep 19082303 = 28623455) B28623455
theorem B5655743 : Blo 1674037 5655743 := bstep (se 1 (by rfl) ⟨4241807, by rfl⟩ : syracuseStep 5655743 = 8483615) B8483615
theorem B1674567 : Blo 1674037 1674567 := bstep (se 1 (by rfl) ⟨1255925, by rfl⟩ : syracuseStep 1674567 = 2511851) B2511851
theorem B1674599 : Blo 1674037 1674599 := bstep (se 1 (by rfl) ⟨1255949, by rfl⟩ : syracuseStep 1674599 = 2511899) B2511899
theorem B1675515 : Blo 1674037 1675515 := bstep (se 1 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 1675515 = 2513273) B2513273
theorem B1675591 : Blo 1674037 1675591 := bstep (se 1 (by rfl) ⟨1256693, by rfl⟩ : syracuseStep 1675591 = 2513387) B2513387
theorem B2511401 : Blo 1674037 2511401 := bstep (se 2 (by rfl) ⟨941775, by rfl⟩ : syracuseStep 2511401 = 1883551) B1883551
theorem B9540287 : Blo 1674037 9540287 := bstep (se 1 (by rfl) ⟨7155215, by rfl⟩ : syracuseStep 9540287 = 14310431) B14310431
theorem B2511743 : Blo 1674037 2511743 := bstep (se 1 (by rfl) ⟨1883807, by rfl⟩ : syracuseStep 2511743 = 3767615) B3767615
theorem B9540605 : Blo 1674037 9540605 := bstep (se 3 (by rfl) ⟨1788863, by rfl⟩ : syracuseStep 9540605 = 3577727) B3577727
theorem B2512031 : Blo 1674037 2512031 := bstep (se 1 (by rfl) ⟨1884023, by rfl⟩ : syracuseStep 2512031 = 3768047) B3768047
theorem B2512199 : Blo 1674037 2512199 := bstep (se 1 (by rfl) ⟨1884149, by rfl⟩ : syracuseStep 2512199 = 3768299) B3768299
theorem B2512649 : Blo 1674037 2512649 := bstep (se 2 (by rfl) ⟨942243, by rfl⟩ : syracuseStep 2512649 = 1884487) B1884487
theorem B8476649 : Blo 1674037 8476649 := bstep (se 2 (by rfl) ⟨3178743, by rfl⟩ : syracuseStep 8476649 = 6357487) B6357487
theorem B2120347 : Blo 1674037 2120347 := bstep (se 1 (by rfl) ⟨1590260, by rfl⟩ : syracuseStep 2120347 = 3180521) B3180521
theorem B3767273 : Blo 1674037 3767273 := bstep (se 2 (by rfl) ⟨1412727, by rfl⟩ : syracuseStep 3767273 = 2825455) B2825455
theorem B2513897 : Blo 1674037 2513897 := bstep (se 2 (by rfl) ⟨942711, by rfl⟩ : syracuseStep 2513897 = 1885423) B1885423
theorem B470457325 : Blo 1674037 470457325 := bstep (se 3 (by rfl) ⟨88210748, by rfl⟩ : syracuseStep 470457325 = 176421497) B176421497
theorem B3578975 : Blo 1674037 3578975 := bstep (se 1 (by rfl) ⟨2684231, by rfl⟩ : syracuseStep 3578975 = 5368463) B5368463
theorem B6881935 : Blo 1674037 6881935 := bstep (se 1 (by rfl) ⟨5161451, by rfl⟩ : syracuseStep 6881935 = 10322903) B10322903
theorem B2827129 : Blo 1674037 2827129 := bstep (se 2 (by rfl) ⟨1060173, by rfl⟩ : syracuseStep 2827129 = 2120347) B2120347
theorem B4080871 : Blo 1674037 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B3769721 : Blo 1674037 3769721 := bstep (se 2 (by rfl) ⟨1413645, by rfl⟩ : syracuseStep 3769721 = 2827291) B2827291
theorem B2385983 : Blo 1674037 2385983 := bstep (se 1 (by rfl) ⟨1789487, by rfl⟩ : syracuseStep 2385983 = 3578975) B3578975
theorem B3770495 : Blo 1674037 3770495 := bstep (se 1 (by rfl) ⟨2827871, by rfl⟩ : syracuseStep 3770495 = 5655743) B5655743
theorem B2509105733 : Blo 1674037 2509105733 := bstep (se 4 (by rfl) ⟨235228662, by rfl⟩ : syracuseStep 2509105733 = 470457325) B470457325
theorem B6359705 : Blo 1674037 6359705 := bstep (se 2 (by rfl) ⟨2384889, by rfl⟩ : syracuseStep 6359705 = 4769779) B4769779
theorem B2681579 : Blo 1674037 2681579 := bstep (se 1 (by rfl) ⟨2011184, by rfl⟩ : syracuseStep 2681579 = 4022369) B4022369
theorem B1674267 : Blo 1674037 1674267 := bstep (se 1 (by rfl) ⟨1255700, by rfl⟩ : syracuseStep 1674267 = 2511401) B2511401
theorem B6360191 : Blo 1674037 6360191 := bstep (se 1 (by rfl) ⟨4770143, by rfl⟩ : syracuseStep 6360191 = 9540287) B9540287
theorem B1674495 : Blo 1674037 1674495 := bstep (se 1 (by rfl) ⟨1255871, by rfl⟩ : syracuseStep 1674495 = 2511743) B2511743
theorem B6360403 : Blo 1674037 6360403 := bstep (se 1 (by rfl) ⟨4770302, by rfl⟩ : syracuseStep 6360403 = 9540605) B9540605
theorem B1674687 : Blo 1674037 1674687 := bstep (se 1 (by rfl) ⟨1256015, by rfl⟩ : syracuseStep 1674687 = 2512031) B2512031
theorem B1674799 : Blo 1674037 1674799 := bstep (se 1 (by rfl) ⟨1256099, by rfl⟩ : syracuseStep 1674799 = 2512199) B2512199
theorem B1675099 : Blo 1674037 1675099 := bstep (se 1 (by rfl) ⟨1256324, by rfl⟩ : syracuseStep 1675099 = 2512649) B2512649
theorem B28619081 : Blo 1674037 28619081 := bstep (se 2 (by rfl) ⟨10732155, by rfl⟩ : syracuseStep 28619081 = 21464311) B21464311
theorem B2511515 : Blo 1674037 2511515 := bstep (se 1 (by rfl) ⟨1883636, by rfl⟩ : syracuseStep 2511515 = 3767273) B3767273
theorem B1675931 : Blo 1674037 1675931 := bstep (se 1 (by rfl) ⟨1256948, by rfl⟩ : syracuseStep 1675931 = 2513897) B2513897
theorem B2512319 : Blo 1674037 2512319 := bstep (se 1 (by rfl) ⟨1884239, by rfl⟩ : syracuseStep 2512319 = 3768479) B3768479
theorem B2905535 : Blo 1674037 2905535 := bstep (se 1 (by rfl) ⟨2179151, by rfl⟩ : syracuseStep 2905535 = 4358303) B4358303
theorem B5651099 : Blo 1674037 5651099 := bstep (se 1 (by rfl) ⟨4238324, by rfl⟩ : syracuseStep 5651099 = 8476649) B8476649
theorem B12721535 : Blo 1674037 12721535 := bstep (se 1 (by rfl) ⟨9541151, by rfl⟩ : syracuseStep 12721535 = 19082303) B19082303
theorem B20364797 : Blo 1674037 20364797 := bstep (se 3 (by rfl) ⟨3818399, by rfl⟩ : syracuseStep 20364797 = 7636799) B7636799
theorem B19079387 : Blo 1674037 19079387 := bstep (se 1 (by rfl) ⟨14309540, by rfl⟩ : syracuseStep 19079387 = 28619081) B28619081
theorem B9175913 : Blo 1674037 9175913 := bstep (se 2 (by rfl) ⟨3440967, by rfl⟩ : syracuseStep 9175913 = 6881935) B6881935
theorem B3769505 : Blo 1674037 3769505 := bstep (se 2 (by rfl) ⟨1413564, by rfl⟩ : syracuseStep 3769505 = 2827129) B2827129
theorem B8480537 : Blo 1674037 8480537 := bstep (se 2 (by rfl) ⟨3180201, by rfl⟩ : syracuseStep 8480537 = 6360403) B6360403
theorem B1787719 : Blo 1674037 1787719 := bstep (se 1 (by rfl) ⟨1340789, by rfl⟩ : syracuseStep 1787719 = 2681579) B2681579
theorem B8481023 : Blo 1674037 8481023 := bstep (se 1 (by rfl) ⟨6360767, by rfl⟩ : syracuseStep 8481023 = 12721535) B12721535
theorem B13576531 : Blo 1674037 13576531 := bstep (se 1 (by rfl) ⟨10182398, by rfl⟩ : syracuseStep 13576531 = 20364797) B20364797
theorem B1674343 : Blo 1674037 1674343 := bstep (se 1 (by rfl) ⟨1255757, by rfl⟩ : syracuseStep 1674343 = 2511515) B2511515
theorem B1674879 : Blo 1674037 1674879 := bstep (se 1 (by rfl) ⟨1256159, by rfl⟩ : syracuseStep 1674879 = 2512319) B2512319
theorem B1672737155 : Blo 1674037 1672737155 := bstep (se 1 (by rfl) ⟨1254552866, by rfl⟩ : syracuseStep 1672737155 = 2509105733) B2509105733
theorem B4239803 : Blo 1674037 4239803 := bstep (se 1 (by rfl) ⟨3179852, by rfl⟩ : syracuseStep 4239803 = 6359705) B6359705
theorem B4240127 : Blo 1674037 4240127 := bstep (se 1 (by rfl) ⟨3180095, by rfl⟩ : syracuseStep 4240127 = 6360191) B6360191
theorem B6362621 : Blo 1674037 6362621 := bstep (se 3 (by rfl) ⟨1192991, by rfl⟩ : syracuseStep 6362621 = 2385983) B2385983
theorem B2513147 : Blo 1674037 2513147 := bstep (se 1 (by rfl) ⟨1884860, by rfl⟩ : syracuseStep 2513147 = 3769721) B3769721
theorem B7748093 : Blo 1674037 7748093 := bstep (se 3 (by rfl) ⟨1452767, by rfl⟩ : syracuseStep 7748093 = 2905535) B2905535
theorem B21764645 : Blo 1674037 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B2513663 : Blo 1674037 2513663 := bstep (se 1 (by rfl) ⟨1885247, by rfl⟩ : syracuseStep 2513663 = 3770495) B3770495
theorem B3767399 : Blo 1674037 3767399 := bstep (se 1 (by rfl) ⟨2825549, by rfl⟩ : syracuseStep 3767399 = 5651099) B5651099
theorem B2826535 : Blo 1674037 2826535 := bstep (se 1 (by rfl) ⟨2119901, by rfl⟩ : syracuseStep 2826535 = 4239803) B4239803
theorem B2826751 : Blo 1674037 2826751 := bstep (se 1 (by rfl) ⟨2120063, by rfl⟩ : syracuseStep 2826751 = 4240127) B4240127
theorem B5653691 : Blo 1674037 5653691 := bstep (se 1 (by rfl) ⟨4240268, by rfl⟩ : syracuseStep 5653691 = 8480537) B8480537
theorem B20661581 : Blo 1674037 20661581 := bstep (se 3 (by rfl) ⟨3874046, by rfl⟩ : syracuseStep 20661581 = 7748093) B7748093
theorem B5654015 : Blo 1674037 5654015 := bstep (se 1 (by rfl) ⟨4240511, by rfl⟩ : syracuseStep 5654015 = 8481023) B8481023
theorem B14509763 : Blo 1674037 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B1675431 : Blo 1674037 1675431 := bstep (se 1 (by rfl) ⟨1256573, by rfl⟩ : syracuseStep 1675431 = 2513147) B2513147
theorem B1675775 : Blo 1674037 1675775 := bstep (se 1 (by rfl) ⟨1256831, by rfl⟩ : syracuseStep 1675775 = 2513663) B2513663
theorem B2511599 : Blo 1674037 2511599 := bstep (se 1 (by rfl) ⟨1883699, by rfl⟩ : syracuseStep 2511599 = 3767399) B3767399
theorem B12719591 : Blo 1674037 12719591 := bstep (se 1 (by rfl) ⟨9539693, by rfl⟩ : syracuseStep 12719591 = 19079387) B19079387
theorem B1115158103 : Blo 1674037 1115158103 := bstep (se 1 (by rfl) ⟨836368577, by rfl⟩ : syracuseStep 1115158103 = 1672737155) B1672737155
theorem B18102041 : Blo 1674037 18102041 := bstep (se 2 (by rfl) ⟨6788265, by rfl⟩ : syracuseStep 18102041 = 13576531) B13576531
theorem B6117275 : Blo 1674037 6117275 := bstep (se 1 (by rfl) ⟨4587956, by rfl⟩ : syracuseStep 6117275 = 9175913) B9175913
theorem B2513003 : Blo 1674037 2513003 := bstep (se 1 (by rfl) ⟨1884752, by rfl⟩ : syracuseStep 2513003 = 3769505) B3769505
theorem B4241747 : Blo 1674037 4241747 := bstep (se 1 (by rfl) ⟨3181310, by rfl⟩ : syracuseStep 4241747 = 6362621) B6362621
theorem B2383625 : Blo 1674037 2383625 := bstep (se 2 (by rfl) ⟨893859, by rfl⟩ : syracuseStep 2383625 = 1787719) B1787719
theorem B3768713 : Blo 1674037 3768713 := bstep (se 2 (by rfl) ⟨1413267, by rfl⟩ : syracuseStep 3768713 = 2826535) B2826535
theorem B3769001 : Blo 1674037 3769001 := bstep (se 2 (by rfl) ⟨1413375, by rfl⟩ : syracuseStep 3769001 = 2826751) B2826751
theorem B3769127 : Blo 1674037 3769127 := bstep (se 1 (by rfl) ⟨2826845, by rfl⟩ : syracuseStep 3769127 = 5653691) B5653691
theorem B8479727 : Blo 1674037 8479727 := bstep (se 1 (by rfl) ⟨6359795, by rfl⟩ : syracuseStep 8479727 = 12719591) B12719591
theorem B3769343 : Blo 1674037 3769343 := bstep (se 1 (by rfl) ⟨2827007, by rfl⟩ : syracuseStep 3769343 = 5654015) B5654015
theorem B12068027 : Blo 1674037 12068027 := bstep (se 1 (by rfl) ⟨9051020, by rfl⟩ : syracuseStep 12068027 = 18102041) B18102041
theorem B2827831 : Blo 1674037 2827831 := bstep (se 1 (by rfl) ⟨2120873, by rfl⟩ : syracuseStep 2827831 = 4241747) B4241747
theorem B1674399 : Blo 1674037 1674399 := bstep (se 1 (by rfl) ⟨1255799, by rfl⟩ : syracuseStep 1674399 = 2511599) B2511599
theorem B13774387 : Blo 1674037 13774387 := bstep (se 1 (by rfl) ⟨10330790, by rfl⟩ : syracuseStep 13774387 = 20661581) B20661581
theorem B1675335 : Blo 1674037 1675335 := bstep (se 1 (by rfl) ⟨1256501, by rfl⟩ : syracuseStep 1675335 = 2513003) B2513003
theorem B743438735 : Blo 1674037 743438735 := bstep (se 1 (by rfl) ⟨557579051, by rfl⟩ : syracuseStep 743438735 = 1115158103) B1115158103
theorem B9673175 : Blo 1674037 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B4078183 : Blo 1674037 4078183 := bstep (se 1 (by rfl) ⟨3058637, by rfl⟩ : syracuseStep 4078183 = 6117275) B6117275
theorem B6356333 : Blo 1674037 6356333 := bstep (se 3 (by rfl) ⟨1191812, by rfl⟩ : syracuseStep 6356333 = 2383625) B2383625
theorem B5653151 : Blo 1674037 5653151 := bstep (se 1 (by rfl) ⟨4239863, by rfl⟩ : syracuseStep 5653151 = 8479727) B8479727
theorem B8045351 : Blo 1674037 8045351 := bstep (se 1 (by rfl) ⟨6034013, by rfl⟩ : syracuseStep 8045351 = 12068027) B12068027
theorem B495625823 : Blo 1674037 495625823 := bstep (se 1 (by rfl) ⟨371719367, by rfl⟩ : syracuseStep 495625823 = 743438735) B743438735
theorem B6448783 : Blo 1674037 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B3770441 : Blo 1674037 3770441 := bstep (se 2 (by rfl) ⟨1413915, by rfl⟩ : syracuseStep 3770441 = 2827831) B2827831
theorem B4237555 : Blo 1674037 4237555 := bstep (se 1 (by rfl) ⟨3178166, by rfl⟩ : syracuseStep 4237555 = 6356333) B6356333
theorem B2512475 : Blo 1674037 2512475 := bstep (se 1 (by rfl) ⟨1884356, by rfl⟩ : syracuseStep 2512475 = 3768713) B3768713
theorem B2512667 : Blo 1674037 2512667 := bstep (se 1 (by rfl) ⟨1884500, by rfl⟩ : syracuseStep 2512667 = 3769001) B3769001
theorem B2512751 : Blo 1674037 2512751 := bstep (se 1 (by rfl) ⟨1884563, by rfl⟩ : syracuseStep 2512751 = 3769127) B3769127
theorem B2512895 : Blo 1674037 2512895 := bstep (se 1 (by rfl) ⟨1884671, by rfl⟩ : syracuseStep 2512895 = 3769343) B3769343
theorem B5437577 : Blo 1674037 5437577 := bstep (se 2 (by rfl) ⟨2039091, by rfl⟩ : syracuseStep 5437577 = 4078183) B4078183
theorem B18365849 : Blo 1674037 18365849 := bstep (se 2 (by rfl) ⟨6887193, by rfl⟩ : syracuseStep 18365849 = 13774387) B13774387
theorem B14500205 : Blo 1674037 14500205 := bstep (se 3 (by rfl) ⟨2718788, by rfl⟩ : syracuseStep 14500205 = 5437577) B5437577
theorem B3768767 : Blo 1674037 3768767 := bstep (se 1 (by rfl) ⟨2826575, by rfl⟩ : syracuseStep 3768767 = 5653151) B5653151
theorem B330417215 : Blo 1674037 330417215 := bstep (se 1 (by rfl) ⟨247812911, by rfl⟩ : syracuseStep 330417215 = 495625823) B495625823
theorem B1674983 : Blo 1674037 1674983 := bstep (se 1 (by rfl) ⟨1256237, by rfl⟩ : syracuseStep 1674983 = 2512475) B2512475
theorem B1675111 : Blo 1674037 1675111 := bstep (se 1 (by rfl) ⟨1256333, by rfl⟩ : syracuseStep 1675111 = 2512667) B2512667
theorem B1675167 : Blo 1674037 1675167 := bstep (se 1 (by rfl) ⟨1256375, by rfl⟩ : syracuseStep 1675167 = 2512751) B2512751
theorem B1675263 : Blo 1674037 1675263 := bstep (se 1 (by rfl) ⟨1256447, by rfl⟩ : syracuseStep 1675263 = 2512895) B2512895
theorem B8598377 : Blo 1674037 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B12243899 : Blo 1674037 12243899 := bstep (se 1 (by rfl) ⟨9182924, by rfl⟩ : syracuseStep 12243899 = 18365849) B18365849
theorem B5650073 : Blo 1674037 5650073 := bstep (se 2 (by rfl) ⟨2118777, by rfl⟩ : syracuseStep 5650073 = 4237555) B4237555
theorem B5363567 : Blo 1674037 5363567 := bstep (se 1 (by rfl) ⟨4022675, by rfl⟩ : syracuseStep 5363567 = 8045351) B8045351
theorem B2513627 : Blo 1674037 2513627 := bstep (se 1 (by rfl) ⟨1885220, by rfl⟩ : syracuseStep 2513627 = 3770441) B3770441
theorem B9666803 : Blo 1674037 9666803 := bstep (se 1 (by rfl) ⟨7250102, by rfl⟩ : syracuseStep 9666803 = 14500205) B14500205
theorem B220278143 : Blo 1674037 220278143 := bstep (se 1 (by rfl) ⟨165208607, by rfl⟩ : syracuseStep 220278143 = 330417215) B330417215
theorem B3575711 : Blo 1674037 3575711 := bstep (se 1 (by rfl) ⟨2681783, by rfl⟩ : syracuseStep 3575711 = 5363567) B5363567
theorem B1675751 : Blo 1674037 1675751 := bstep (se 1 (by rfl) ⟨1256813, by rfl⟩ : syracuseStep 1675751 = 2513627) B2513627
theorem B32650397 : Blo 1674037 32650397 := bstep (se 3 (by rfl) ⟨6121949, by rfl⟩ : syracuseStep 32650397 = 12243899) B12243899
theorem B2512511 : Blo 1674037 2512511 := bstep (se 1 (by rfl) ⟨1884383, by rfl⟩ : syracuseStep 2512511 = 3768767) B3768767
theorem B5732251 : Blo 1674037 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B3766715 : Blo 1674037 3766715 := bstep (se 1 (by rfl) ⟨2825036, by rfl⟩ : syracuseStep 3766715 = 5650073) B5650073
theorem B21766931 : Blo 1674037 21766931 := bstep (se 1 (by rfl) ⟨16325198, by rfl⟩ : syracuseStep 21766931 = 32650397) B32650397
theorem B587408381 : Blo 1674037 587408381 := bstep (se 3 (by rfl) ⟨110139071, by rfl⟩ : syracuseStep 587408381 = 220278143) B220278143
theorem B1675007 : Blo 1674037 1675007 := bstep (se 1 (by rfl) ⟨1256255, by rfl⟩ : syracuseStep 1675007 = 2512511) B2512511
theorem B2511143 : Blo 1674037 2511143 := bstep (se 1 (by rfl) ⟨1883357, by rfl⟩ : syracuseStep 2511143 = 3766715) B3766715
theorem B6444535 : Blo 1674037 6444535 := bstep (se 1 (by rfl) ⟨4833401, by rfl⟩ : syracuseStep 6444535 = 9666803) B9666803
theorem B30572005 : Blo 1674037 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B9535229 : Blo 1674037 9535229 := bstep (se 3 (by rfl) ⟨1787855, by rfl⟩ : syracuseStep 9535229 = 3575711) B3575711
theorem B1674095 : Blo 1674037 1674095 := bstep (se 1 (by rfl) ⟨1255571, by rfl⟩ : syracuseStep 1674095 = 2511143) B2511143
theorem B14511287 : Blo 1674037 14511287 := bstep (se 1 (by rfl) ⟨10883465, by rfl⟩ : syracuseStep 14511287 = 21766931) B21766931
theorem B391605587 : Blo 1674037 391605587 := bstep (se 1 (by rfl) ⟨293704190, by rfl⟩ : syracuseStep 391605587 = 587408381) B587408381
theorem B40762673 : Blo 1674037 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B8592713 : Blo 1674037 8592713 := bstep (se 2 (by rfl) ⟨3222267, by rfl⟩ : syracuseStep 8592713 = 6444535) B6444535
theorem B6356819 : Blo 1674037 6356819 := bstep (se 1 (by rfl) ⟨4767614, by rfl⟩ : syracuseStep 6356819 = 9535229) B9535229
theorem B27175115 : Blo 1674037 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B5728475 : Blo 1674037 5728475 := bstep (se 1 (by rfl) ⟨4296356, by rfl⟩ : syracuseStep 5728475 = 8592713) B8592713
theorem B4237879 : Blo 1674037 4237879 := bstep (se 1 (by rfl) ⟨3178409, by rfl⟩ : syracuseStep 4237879 = 6356819) B6356819
theorem B9674191 : Blo 1674037 9674191 := bstep (se 1 (by rfl) ⟨7255643, by rfl⟩ : syracuseStep 9674191 = 14511287) B14511287
theorem B261070391 : Blo 1674037 261070391 := bstep (se 1 (by rfl) ⟨195802793, by rfl⟩ : syracuseStep 261070391 = 391605587) B391605587
theorem B3818983 : Blo 1674037 3818983 := bstep (se 1 (by rfl) ⟨2864237, by rfl⟩ : syracuseStep 3818983 = 5728475) B5728475
theorem B18116743 : Blo 1674037 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B12898921 : Blo 1674037 12898921 := bstep (se 2 (by rfl) ⟨4837095, by rfl⟩ : syracuseStep 12898921 = 9674191) B9674191
theorem B5650505 : Blo 1674037 5650505 := bstep (se 2 (by rfl) ⟨2118939, by rfl⟩ : syracuseStep 5650505 = 4237879) B4237879
theorem B696187709 : Blo 1674037 696187709 := bstep (se 3 (by rfl) ⟨130535195, by rfl⟩ : syracuseStep 696187709 = 261070391) B261070391
theorem B17198561 : Blo 1674037 17198561 := bstep (se 2 (by rfl) ⟨6449460, by rfl⟩ : syracuseStep 17198561 = 12898921) B12898921
theorem B5091977 : Blo 1674037 5091977 := bstep (se 2 (by rfl) ⟨1909491, by rfl⟩ : syracuseStep 5091977 = 3818983) B3818983
theorem B24155657 : Blo 1674037 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B3767003 : Blo 1674037 3767003 := bstep (se 1 (by rfl) ⟨2825252, by rfl⟩ : syracuseStep 3767003 = 5650505) B5650505
theorem B464125139 : Blo 1674037 464125139 := bstep (se 1 (by rfl) ⟨348093854, by rfl⟩ : syracuseStep 464125139 = 696187709) B696187709
theorem B13578605 : Blo 1674037 13578605 := bstep (se 3 (by rfl) ⟨2545988, by rfl⟩ : syracuseStep 13578605 = 5091977) B5091977
theorem B2511335 : Blo 1674037 2511335 := bstep (se 1 (by rfl) ⟨1883501, by rfl⟩ : syracuseStep 2511335 = 3767003) B3767003
theorem B309416759 : Blo 1674037 309416759 := bstep (se 1 (by rfl) ⟨232062569, by rfl⟩ : syracuseStep 309416759 = 464125139) B464125139
theorem B11465707 : Blo 1674037 11465707 := bstep (se 1 (by rfl) ⟨8599280, by rfl⟩ : syracuseStep 11465707 = 17198561) B17198561
theorem B16103771 : Blo 1674037 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B9052403 : Blo 1674037 9052403 := bstep (se 1 (by rfl) ⟨6789302, by rfl⟩ : syracuseStep 9052403 = 13578605) B13578605
theorem B15287609 : Blo 1674037 15287609 := bstep (se 2 (by rfl) ⟨5732853, by rfl⟩ : syracuseStep 15287609 = 11465707) B11465707
theorem B1674223 : Blo 1674037 1674223 := bstep (se 1 (by rfl) ⟨1255667, by rfl⟩ : syracuseStep 1674223 = 2511335) B2511335
theorem B206277839 : Blo 1674037 206277839 := bstep (se 1 (by rfl) ⟨154708379, by rfl⟩ : syracuseStep 206277839 = 309416759) B309416759
theorem B10735847 : Blo 1674037 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B10191739 : Blo 1674037 10191739 := bstep (se 1 (by rfl) ⟨7643804, by rfl⟩ : syracuseStep 10191739 = 15287609) B15287609
theorem B7157231 : Blo 1674037 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B24139741 : Blo 1674037 24139741 := bstep (se 3 (by rfl) ⟨4526201, by rfl⟩ : syracuseStep 24139741 = 9052403) B9052403
theorem B137518559 : Blo 1674037 137518559 := bstep (se 1 (by rfl) ⟨103138919, by rfl⟩ : syracuseStep 137518559 = 206277839) B206277839
theorem B91679039 : Blo 1674037 91679039 := bstep (se 1 (by rfl) ⟨68759279, by rfl⟩ : syracuseStep 91679039 = 137518559) B137518559
theorem B4771487 : Blo 1674037 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B13588985 : Blo 1674037 13588985 := bstep (se 2 (by rfl) ⟨5095869, by rfl⟩ : syracuseStep 13588985 = 10191739) B10191739
theorem B32186321 : Blo 1674037 32186321 := bstep (se 2 (by rfl) ⟨12069870, by rfl⟩ : syracuseStep 32186321 = 24139741) B24139741
theorem B12723965 : Blo 1674037 12723965 := bstep (se 3 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 12723965 = 4771487) B4771487
theorem B21457547 : Blo 1674037 21457547 := bstep (se 1 (by rfl) ⟨16093160, by rfl⟩ : syracuseStep 21457547 = 32186321) B32186321
theorem B36237293 : Blo 1674037 36237293 := bstep (se 3 (by rfl) ⟨6794492, by rfl⟩ : syracuseStep 36237293 = 13588985) B13588985
theorem B61119359 : Blo 1674037 61119359 := bstep (se 1 (by rfl) ⟨45839519, by rfl⟩ : syracuseStep 61119359 = 91679039) B91679039
theorem B14305031 : Blo 1674037 14305031 := bstep (se 1 (by rfl) ⟨10728773, by rfl⟩ : syracuseStep 14305031 = 21457547) B21457547
theorem B8482643 : Blo 1674037 8482643 := bstep (se 1 (by rfl) ⟨6361982, by rfl⟩ : syracuseStep 8482643 = 12723965) B12723965
theorem B40746239 : Blo 1674037 40746239 := bstep (se 1 (by rfl) ⟨30559679, by rfl⟩ : syracuseStep 40746239 = 61119359) B61119359
theorem B24158195 : Blo 1674037 24158195 := bstep (se 1 (by rfl) ⟨18118646, by rfl⟩ : syracuseStep 24158195 = 36237293) B36237293
theorem B9536687 : Blo 1674037 9536687 := bstep (se 1 (by rfl) ⟨7152515, by rfl⟩ : syracuseStep 9536687 = 14305031) B14305031
theorem B5655095 : Blo 1674037 5655095 := bstep (se 1 (by rfl) ⟨4241321, by rfl⟩ : syracuseStep 5655095 = 8482643) B8482643
theorem B27164159 : Blo 1674037 27164159 := bstep (se 1 (by rfl) ⟨20373119, by rfl⟩ : syracuseStep 27164159 = 40746239) B40746239
theorem B16105463 : Blo 1674037 16105463 := bstep (se 1 (by rfl) ⟨12079097, by rfl⟩ : syracuseStep 16105463 = 24158195) B24158195
theorem B6357791 : Blo 1674037 6357791 := bstep (se 1 (by rfl) ⟨4768343, by rfl⟩ : syracuseStep 6357791 = 9536687) B9536687
theorem B3770063 : Blo 1674037 3770063 := bstep (se 1 (by rfl) ⟨2827547, by rfl⟩ : syracuseStep 3770063 = 5655095) B5655095
theorem B18109439 : Blo 1674037 18109439 := bstep (se 1 (by rfl) ⟨13582079, by rfl⟩ : syracuseStep 18109439 = 27164159) B27164159
theorem B10736975 : Blo 1674037 10736975 := bstep (se 1 (by rfl) ⟨8052731, by rfl⟩ : syracuseStep 10736975 = 16105463) B16105463
theorem B4238527 : Blo 1674037 4238527 := bstep (se 1 (by rfl) ⟨3178895, by rfl⟩ : syracuseStep 4238527 = 6357791) B6357791
theorem B12072959 : Blo 1674037 12072959 := bstep (se 1 (by rfl) ⟨9054719, by rfl⟩ : syracuseStep 12072959 = 18109439) B18109439
theorem B7157983 : Blo 1674037 7157983 := bstep (se 1 (by rfl) ⟨5368487, by rfl⟩ : syracuseStep 7157983 = 10736975) B10736975
theorem B2513375 : Blo 1674037 2513375 := bstep (se 1 (by rfl) ⟨1885031, by rfl⟩ : syracuseStep 2513375 = 3770063) B3770063
theorem B9543977 : Blo 1674037 9543977 := bstep (se 2 (by rfl) ⟨3578991, by rfl⟩ : syracuseStep 9543977 = 7157983) B7157983
theorem B8048639 : Blo 1674037 8048639 := bstep (se 1 (by rfl) ⟨6036479, by rfl⟩ : syracuseStep 8048639 = 12072959) B12072959
theorem B1675583 : Blo 1674037 1675583 := bstep (se 1 (by rfl) ⟨1256687, by rfl⟩ : syracuseStep 1675583 = 2513375) B2513375
theorem B5651369 : Blo 1674037 5651369 := bstep (se 2 (by rfl) ⟨2119263, by rfl⟩ : syracuseStep 5651369 = 4238527) B4238527
theorem B6362651 : Blo 1674037 6362651 := bstep (se 1 (by rfl) ⟨4771988, by rfl⟩ : syracuseStep 6362651 = 9543977) B9543977
theorem B3767579 : Blo 1674037 3767579 := bstep (se 1 (by rfl) ⟨2825684, by rfl⟩ : syracuseStep 3767579 = 5651369) B5651369
theorem B5365759 : Blo 1674037 5365759 := bstep (se 1 (by rfl) ⟨4024319, by rfl⟩ : syracuseStep 5365759 = 8048639) B8048639
theorem B7154345 : Blo 1674037 7154345 := bstep (se 2 (by rfl) ⟨2682879, by rfl⟩ : syracuseStep 7154345 = 5365759) B5365759
theorem B2511719 : Blo 1674037 2511719 := bstep (se 1 (by rfl) ⟨1883789, by rfl⟩ : syracuseStep 2511719 = 3767579) B3767579
theorem B4241767 : Blo 1674037 4241767 := bstep (se 1 (by rfl) ⟨3181325, by rfl⟩ : syracuseStep 4241767 = 6362651) B6362651
theorem B4769563 : Blo 1674037 4769563 := bstep (se 1 (by rfl) ⟨3577172, by rfl⟩ : syracuseStep 4769563 = 7154345) B7154345
theorem B5655689 : Blo 1674037 5655689 := bstep (se 2 (by rfl) ⟨2120883, by rfl⟩ : syracuseStep 5655689 = 4241767) B4241767
theorem B1674479 : Blo 1674037 1674479 := bstep (se 1 (by rfl) ⟨1255859, by rfl⟩ : syracuseStep 1674479 = 2511719) B2511719
theorem B3770459 : Blo 1674037 3770459 := bstep (se 1 (by rfl) ⟨2827844, by rfl⟩ : syracuseStep 3770459 = 5655689) B5655689
theorem B6359417 : Blo 1674037 6359417 := bstep (se 2 (by rfl) ⟨2384781, by rfl⟩ : syracuseStep 6359417 = 4769563) B4769563
theorem B4239611 : Blo 1674037 4239611 := bstep (se 1 (by rfl) ⟨3179708, by rfl⟩ : syracuseStep 4239611 = 6359417) B6359417
theorem B2513639 : Blo 1674037 2513639 := bstep (se 1 (by rfl) ⟨1885229, by rfl⟩ : syracuseStep 2513639 = 3770459) B3770459
theorem B2826407 : Blo 1674037 2826407 := bstep (se 1 (by rfl) ⟨2119805, by rfl⟩ : syracuseStep 2826407 = 4239611) B4239611
theorem B1675759 : Blo 1674037 1675759 := bstep (se 1 (by rfl) ⟨1256819, by rfl⟩ : syracuseStep 1675759 = 2513639) B2513639
theorem B1884271 : Blo 1674037 1884271 := bstep (se 1 (by rfl) ⟨1413203, by rfl⟩ : syracuseStep 1884271 = 2826407) B2826407
theorem B2512361 : Blo 1674037 2512361 := bstep (se 2 (by rfl) ⟨942135, by rfl⟩ : syracuseStep 2512361 = 1884271) B1884271
theorem B1674907 : Blo 1674037 1674907 := bstep (se 1 (by rfl) ⟨1256180, by rfl⟩ : syracuseStep 1674907 = 2512361) B2512361

theorem C0 (j : ℕ) (h1 : 418509 ≤ j) (h2 : j ≤ 419008) : Blo 1674037 (4 * j + 3) := by
  interval_cases j
  · exact B1674039
  · exact B1674043
  · exact B1674047
  · exact B1674051
  · exact B1674055
  · exact B1674059
  · exact B1674063
  · exact B1674067
  · exact B1674071
  · exact B1674075
  · exact B1674079
  · exact B1674083
  · exact B1674087
  · exact B1674091
  · exact B1674095
  · exact B1674099
  · exact B1674103
  · exact B1674107
  · exact B1674111
  · exact B1674115
  · exact B1674119
  · exact B1674123
  · exact B1674127
  · exact B1674131
  · exact B1674135
  · exact B1674139
  · exact B1674143
  · exact B1674147
  · exact B1674151
  · exact B1674155
  · exact B1674159
  · exact B1674163
  · exact B1674167
  · exact B1674171
  · exact B1674175
  · exact B1674179
  · exact B1674183
  · exact B1674187
  · exact B1674191
  · exact B1674195
  · exact B1674199
  · exact B1674203
  · exact B1674207
  · exact B1674211
  · exact B1674215
  · exact B1674219
  · exact B1674223
  · exact B1674227
  · exact B1674231
  · exact B1674235
  · exact B1674239
  · exact B1674243
  · exact B1674247
  · exact B1674251
  · exact B1674255
  · exact B1674259
  · exact B1674263
  · exact B1674267
  · exact B1674271
  · exact B1674275
  · exact B1674279
  · exact B1674283
  · exact B1674287
  · exact B1674291
  · exact B1674295
  · exact B1674299
  · exact B1674303
  · exact B1674307
  · exact B1674311
  · exact B1674315
  · exact B1674319
  · exact B1674323
  · exact B1674327
  · exact B1674331
  · exact B1674335
  · exact B1674339
  · exact B1674343
  · exact B1674347
  · exact B1674351
  · exact B1674355
  · exact B1674359
  · exact B1674363
  · exact B1674367
  · exact B1674371
  · exact B1674375
  · exact B1674379
  · exact B1674383
  · exact B1674387
  · exact B1674391
  · exact B1674395
  · exact B1674399
  · exact B1674403
  · exact B1674407
  · exact B1674411
  · exact B1674415
  · exact B1674419
  · exact B1674423
  · exact B1674427
  · exact B1674431
  · exact B1674435
  · exact B1674439
  · exact B1674443
  · exact B1674447
  · exact B1674451
  · exact B1674455
  · exact B1674459
  · exact B1674463
  · exact B1674467
  · exact B1674471
  · exact B1674475
  · exact B1674479
  · exact B1674483
  · exact B1674487
  · exact B1674491
  · exact B1674495
  · exact B1674499
  · exact B1674503
  · exact B1674507
  · exact B1674511
  · exact B1674515
  · exact B1674519
  · exact B1674523
  · exact B1674527
  · exact B1674531
  · exact B1674535
  · exact B1674539
  · exact B1674543
  · exact B1674547
  · exact B1674551
  · exact B1674555
  · exact B1674559
  · exact B1674563
  · exact B1674567
  · exact B1674571
  · exact B1674575
  · exact B1674579
  · exact B1674583
  · exact B1674587
  · exact B1674591
  · exact B1674595
  · exact B1674599
  · exact B1674603
  · exact B1674607
  · exact B1674611
  · exact B1674615
  · exact B1674619
  · exact B1674623
  · exact B1674627
  · exact B1674631
  · exact B1674635
  · exact B1674639
  · exact B1674643
  · exact B1674647
  · exact B1674651
  · exact B1674655
  · exact B1674659
  · exact B1674663
  · exact B1674667
  · exact B1674671
  · exact B1674675
  · exact B1674679
  · exact B1674683
  · exact B1674687
  · exact B1674691
  · exact B1674695
  · exact B1674699
  · exact B1674703
  · exact B1674707
  · exact B1674711
  · exact B1674715
  · exact B1674719
  · exact B1674723
  · exact B1674727
  · exact B1674731
  · exact B1674735
  · exact B1674739
  · exact B1674743
  · exact B1674747
  · exact B1674751
  · exact B1674755
  · exact B1674759
  · exact B1674763
  · exact B1674767
  · exact B1674771
  · exact B1674775
  · exact B1674779
  · exact B1674783
  · exact B1674787
  · exact B1674791
  · exact B1674795
  · exact B1674799
  · exact B1674803
  · exact B1674807
  · exact B1674811
  · exact B1674815
  · exact B1674819
  · exact B1674823
  · exact B1674827
  · exact B1674831
  · exact B1674835
  · exact B1674839
  · exact B1674843
  · exact B1674847
  · exact B1674851
  · exact B1674855
  · exact B1674859
  · exact B1674863
  · exact B1674867
  · exact B1674871
  · exact B1674875
  · exact B1674879
  · exact B1674883
  · exact B1674887
  · exact B1674891
  · exact B1674895
  · exact B1674899
  · exact B1674903
  · exact B1674907
  · exact B1674911
  · exact B1674915
  · exact B1674919
  · exact B1674923
  · exact B1674927
  · exact B1674931
  · exact B1674935
  · exact B1674939
  · exact B1674943
  · exact B1674947
  · exact B1674951
  · exact B1674955
  · exact B1674959
  · exact B1674963
  · exact B1674967
  · exact B1674971
  · exact B1674975
  · exact B1674979
  · exact B1674983
  · exact B1674987
  · exact B1674991
  · exact B1674995
  · exact B1674999
  · exact B1675003
  · exact B1675007
  · exact B1675011
  · exact B1675015
  · exact B1675019
  · exact B1675023
  · exact B1675027
  · exact B1675031
  · exact B1675035
  · exact B1675039
  · exact B1675043
  · exact B1675047
  · exact B1675051
  · exact B1675055
  · exact B1675059
  · exact B1675063
  · exact B1675067
  · exact B1675071
  · exact B1675075
  · exact B1675079
  · exact B1675083
  · exact B1675087
  · exact B1675091
  · exact B1675095
  · exact B1675099
  · exact B1675103
  · exact B1675107
  · exact B1675111
  · exact B1675115
  · exact B1675119
  · exact B1675123
  · exact B1675127
  · exact B1675131
  · exact B1675135
  · exact B1675139
  · exact B1675143
  · exact B1675147
  · exact B1675151
  · exact B1675155
  · exact B1675159
  · exact B1675163
  · exact B1675167
  · exact B1675171
  · exact B1675175
  · exact B1675179
  · exact B1675183
  · exact B1675187
  · exact B1675191
  · exact B1675195
  · exact B1675199
  · exact B1675203
  · exact B1675207
  · exact B1675211
  · exact B1675215
  · exact B1675219
  · exact B1675223
  · exact B1675227
  · exact B1675231
  · exact B1675235
  · exact B1675239
  · exact B1675243
  · exact B1675247
  · exact B1675251
  · exact B1675255
  · exact B1675259
  · exact B1675263
  · exact B1675267
  · exact B1675271
  · exact B1675275
  · exact B1675279
  · exact B1675283
  · exact B1675287
  · exact B1675291
  · exact B1675295
  · exact B1675299
  · exact B1675303
  · exact B1675307
  · exact B1675311
  · exact B1675315
  · exact B1675319
  · exact B1675323
  · exact B1675327
  · exact B1675331
  · exact B1675335
  · exact B1675339
  · exact B1675343
  · exact B1675347
  · exact B1675351
  · exact B1675355
  · exact B1675359
  · exact B1675363
  · exact B1675367
  · exact B1675371
  · exact B1675375
  · exact B1675379
  · exact B1675383
  · exact B1675387
  · exact B1675391
  · exact B1675395
  · exact B1675399
  · exact B1675403
  · exact B1675407
  · exact B1675411
  · exact B1675415
  · exact B1675419
  · exact B1675423
  · exact B1675427
  · exact B1675431
  · exact B1675435
  · exact B1675439
  · exact B1675443
  · exact B1675447
  · exact B1675451
  · exact B1675455
  · exact B1675459
  · exact B1675463
  · exact B1675467
  · exact B1675471
  · exact B1675475
  · exact B1675479
  · exact B1675483
  · exact B1675487
  · exact B1675491
  · exact B1675495
  · exact B1675499
  · exact B1675503
  · exact B1675507
  · exact B1675511
  · exact B1675515
  · exact B1675519
  · exact B1675523
  · exact B1675527
  · exact B1675531
  · exact B1675535
  · exact B1675539
  · exact B1675543
  · exact B1675547
  · exact B1675551
  · exact B1675555
  · exact B1675559
  · exact B1675563
  · exact B1675567
  · exact B1675571
  · exact B1675575
  · exact B1675579
  · exact B1675583
  · exact B1675587
  · exact B1675591
  · exact B1675595
  · exact B1675599
  · exact B1675603
  · exact B1675607
  · exact B1675611
  · exact B1675615
  · exact B1675619
  · exact B1675623
  · exact B1675627
  · exact B1675631
  · exact B1675635
  · exact B1675639
  · exact B1675643
  · exact B1675647
  · exact B1675651
  · exact B1675655
  · exact B1675659
  · exact B1675663
  · exact B1675667
  · exact B1675671
  · exact B1675675
  · exact B1675679
  · exact B1675683
  · exact B1675687
  · exact B1675691
  · exact B1675695
  · exact B1675699
  · exact B1675703
  · exact B1675707
  · exact B1675711
  · exact B1675715
  · exact B1675719
  · exact B1675723
  · exact B1675727
  · exact B1675731
  · exact B1675735
  · exact B1675739
  · exact B1675743
  · exact B1675747
  · exact B1675751
  · exact B1675755
  · exact B1675759
  · exact B1675763
  · exact B1675767
  · exact B1675771
  · exact B1675775
  · exact B1675779
  · exact B1675783
  · exact B1675787
  · exact B1675791
  · exact B1675795
  · exact B1675799
  · exact B1675803
  · exact B1675807
  · exact B1675811
  · exact B1675815
  · exact B1675819
  · exact B1675823
  · exact B1675827
  · exact B1675831
  · exact B1675835
  · exact B1675839
  · exact B1675843
  · exact B1675847
  · exact B1675851
  · exact B1675855
  · exact B1675859
  · exact B1675863
  · exact B1675867
  · exact B1675871
  · exact B1675875
  · exact B1675879
  · exact B1675883
  · exact B1675887
  · exact B1675891
  · exact B1675895
  · exact B1675899
  · exact B1675903
  · exact B1675907
  · exact B1675911
  · exact B1675915
  · exact B1675919
  · exact B1675923
  · exact B1675927
  · exact B1675931
  · exact B1675935
  · exact B1675939
  · exact B1675943
  · exact B1675947
  · exact B1675951
  · exact B1675955
  · exact B1675959
  · exact B1675963
  · exact B1675967
  · exact B1675971
  · exact B1675975
  · exact B1675979
  · exact B1675983
  · exact B1675987
  · exact B1675991
  · exact B1675995
  · exact B1675999
  · exact B1676003
  · exact B1676007
  · exact B1676011
  · exact B1676015
  · exact B1676019
  · exact B1676023
  · exact B1676027
  · exact B1676031
  · exact B1676035

theorem solution (m : ℕ) (hlo : 1674037 ≤ m) (hhi : m ≤ 1676037) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 418509 ≤ j := by omega
    have hj2 : j ≤ 419008 := by omega
    have hb : Blo 1674037 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
