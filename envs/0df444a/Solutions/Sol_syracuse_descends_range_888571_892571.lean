-- Prove2me | solution 1 for syracuse_descends_range_888571_892571
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:46.335555+00:00
-- url     : https://prove2.me/submissions/4396cf59-1ef0-43f9-9244-650b59b135ad

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


theorem B16482325 : Blo 888571 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B950329 : Blo 888571 950329 := bbase (se 2 (by rfl) ⟨356373, by rfl⟩ : syracuseStep 950329 = 712747) (by norm_num)
theorem B5079125 : Blo 888571 5079125 := bbase (se 8 (by rfl) ⟨29760, by rfl⟩ : syracuseStep 5079125 = 59521) (by norm_num)
theorem B1802341 : Blo 888571 1802341 := bbase (se 4 (by rfl) ⟨168969, by rfl⟩ : syracuseStep 1802341 = 337939) (by norm_num)
theorem B3211397 : Blo 888571 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B1802405 : Blo 888571 1802405 := bbase (se 4 (by rfl) ⟨168975, by rfl⟩ : syracuseStep 1802405 = 337951) (by norm_num)
theorem B1900837 : Blo 888571 1900837 := bbase (se 4 (by rfl) ⟨178203, by rfl⟩ : syracuseStep 1900837 = 356407) (by norm_num)
theorem B32440661 : Blo 888571 32440661 := bbase (se 10 (by rfl) ⟨47520, by rfl⟩ : syracuseStep 32440661 = 95041) (by norm_num)
theorem B1999349 : Blo 888571 1999349 := bbase (se 5 (by rfl) ⟨93719, by rfl⟩ : syracuseStep 1999349 = 187439) (by norm_num)
theorem B950773 : Blo 888571 950773 := bbase (se 5 (by rfl) ⟨44567, by rfl⟩ : syracuseStep 950773 = 89135) (by norm_num)
theorem B1999421 : Blo 888571 1999421 := bbase (se 3 (by rfl) ⟨374891, by rfl⟩ : syracuseStep 1999421 = 749783) (by norm_num)
theorem B1016425 : Blo 888571 1016425 := bbase (se 2 (by rfl) ⟨381159, by rfl⟩ : syracuseStep 1016425 = 762319) (by norm_num)
theorem B950897 : Blo 888571 950897 := bbase (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) (by norm_num)
theorem B1999493 : Blo 888571 1999493 := bbase (se 4 (by rfl) ⟨187452, by rfl⟩ : syracuseStep 1999493 = 374905) (by norm_num)
theorem B3048101 : Blo 888571 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B1999565 : Blo 888571 1999565 := bbase (se 3 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 1999565 = 749837) (by norm_num)
theorem B3375877 : Blo 888571 3375877 := bbase (se 4 (by rfl) ⟨316488, by rfl⟩ : syracuseStep 3375877 = 632977) (by norm_num)
theorem B1606405 : Blo 888571 1606405 := bbase (se 4 (by rfl) ⟨150600, by rfl⟩ : syracuseStep 1606405 = 301201) (by norm_num)
theorem B1999637 : Blo 888571 1999637 := bbase (se 6 (by rfl) ⟨46866, by rfl⟩ : syracuseStep 1999637 = 93733) (by norm_num)
theorem B1999709 : Blo 888571 1999709 := bbase (se 3 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 1999709 = 749891) (by norm_num)
theorem B951149 : Blo 888571 951149 := bbase (se 3 (by rfl) ⟨178340, by rfl⟩ : syracuseStep 951149 = 356681) (by norm_num)
theorem B1999781 : Blo 888571 1999781 := bbase (se 4 (by rfl) ⟨187479, by rfl⟩ : syracuseStep 1999781 = 374959) (by norm_num)
theorem B3802085 : Blo 888571 3802085 := bbase (se 4 (by rfl) ⟨356445, by rfl⟩ : syracuseStep 3802085 = 712891) (by norm_num)
theorem B1999853 : Blo 888571 1999853 := bbase (se 3 (by rfl) ⟨374972, by rfl⟩ : syracuseStep 1999853 = 749945) (by norm_num)
theorem B1999925 : Blo 888571 1999925 := bbase (se 5 (by rfl) ⟨93746, by rfl⟩ : syracuseStep 1999925 = 187493) (by norm_num)
theorem B3376181 : Blo 888571 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B1999997 : Blo 888571 1999997 := bbase (se 3 (by rfl) ⟨374999, by rfl⟩ : syracuseStep 1999997 = 749999) (by norm_num)
theorem B2000069 : Blo 888571 2000069 := bbase (se 4 (by rfl) ⟨187506, by rfl⟩ : syracuseStep 2000069 = 375013) (by norm_num)
theorem B3802373 : Blo 888571 3802373 := bbase (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) (by norm_num)
theorem B2000141 : Blo 888571 2000141 := bbase (se 3 (by rfl) ⟨375026, by rfl⟩ : syracuseStep 2000141 = 750053) (by norm_num)
theorem B1803541 : Blo 888571 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B951593 : Blo 888571 951593 := bbase (se 2 (by rfl) ⟨356847, by rfl⟩ : syracuseStep 951593 = 713695) (by norm_num)
theorem B2000213 : Blo 888571 2000213 := bbase (se 12 (by rfl) ⟨732, by rfl⟩ : syracuseStep 2000213 = 1465) (by norm_num)
theorem B2000285 : Blo 888571 2000285 := bbase (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) (by norm_num)
theorem B1017265 : Blo 888571 1017265 := bbase (se 2 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 1017265 = 762949) (by norm_num)
theorem B2852293 : Blo 888571 2852293 := bbase (se 4 (by rfl) ⟨267402, by rfl⟩ : syracuseStep 2852293 = 534805) (by norm_num)
theorem B1607125 : Blo 888571 1607125 := bbase (se 7 (by rfl) ⟨18833, by rfl⟩ : syracuseStep 1607125 = 37667) (by norm_num)
theorem B2000357 : Blo 888571 2000357 := bbase (se 4 (by rfl) ⟨187533, by rfl⟩ : syracuseStep 2000357 = 375067) (by norm_num)
theorem B951841 : Blo 888571 951841 := bbase (se 2 (by rfl) ⟨356940, by rfl⟩ : syracuseStep 951841 = 713881) (by norm_num)
theorem B2000429 : Blo 888571 2000429 := bbase (se 3 (by rfl) ⟨375080, by rfl⟩ : syracuseStep 2000429 = 750161) (by norm_num)
theorem B2000501 : Blo 888571 2000501 := bbase (se 5 (by rfl) ⟨93773, by rfl⟩ : syracuseStep 2000501 = 187547) (by norm_num)
theorem B2000573 : Blo 888571 2000573 := bbase (se 3 (by rfl) ⟨375107, by rfl⟩ : syracuseStep 2000573 = 750215) (by norm_num)
theorem B1607357 : Blo 888571 1607357 := bbase (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) (by norm_num)
theorem B3049157 : Blo 888571 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B2000645 : Blo 888571 2000645 := bbase (se 4 (by rfl) ⟨187560, by rfl⟩ : syracuseStep 2000645 = 375121) (by norm_num)
theorem B1902341 : Blo 888571 1902341 := bbase (se 4 (by rfl) ⟨178344, by rfl⟩ : syracuseStep 1902341 = 356689) (by norm_num)
theorem B2000717 : Blo 888571 2000717 := bbase (se 3 (by rfl) ⟨375134, by rfl⟩ : syracuseStep 2000717 = 750269) (by norm_num)
theorem B2000789 : Blo 888571 2000789 := bbase (se 6 (by rfl) ⟨46893, by rfl⟩ : syracuseStep 2000789 = 93787) (by norm_num)
theorem B1902485 : Blo 888571 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B1804205 : Blo 888571 1804205 := bbase (se 3 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 1804205 = 676577) (by norm_num)
theorem B2000861 : Blo 888571 2000861 := bbase (se 3 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 2000861 = 750323) (by norm_num)
theorem B1804253 : Blo 888571 1804253 := bbase (se 3 (by rfl) ⟨338297, by rfl⟩ : syracuseStep 1804253 = 676595) (by norm_num)
theorem B952285 : Blo 888571 952285 := bbase (se 3 (by rfl) ⟨178553, by rfl⟩ : syracuseStep 952285 = 357107) (by norm_num)
theorem B3803125 : Blo 888571 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B952345 : Blo 888571 952345 := bbase (se 2 (by rfl) ⟨357129, by rfl⟩ : syracuseStep 952345 = 714259) (by norm_num)
theorem B2000933 : Blo 888571 2000933 := bbase (se 4 (by rfl) ⟨187587, by rfl⟩ : syracuseStep 2000933 = 375175) (by norm_num)
theorem B2001005 : Blo 888571 2001005 := bbase (se 3 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 2001005 = 750377) (by norm_num)
theorem B1607789 : Blo 888571 1607789 := bbase (se 3 (by rfl) ⟨301460, by rfl⟩ : syracuseStep 1607789 = 602921) (by norm_num)
theorem B1083541 : Blo 888571 1083541 := bbase (se 6 (by rfl) ⟨25395, by rfl⟩ : syracuseStep 1083541 = 50791) (by norm_num)
theorem B2001077 : Blo 888571 2001077 := bbase (se 5 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 2001077 = 187601) (by norm_num)
theorem B2001149 : Blo 888571 2001149 := bbase (se 3 (by rfl) ⟨375215, by rfl⟩ : syracuseStep 2001149 = 750431) (by norm_num)
theorem B1902845 : Blo 888571 1902845 := bbase (se 3 (by rfl) ⟨356783, by rfl⟩ : syracuseStep 1902845 = 713567) (by norm_num)
theorem B1607933 : Blo 888571 1607933 := bbase (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) (by norm_num)
theorem B2001221 : Blo 888571 2001221 := bbase (se 4 (by rfl) ⟨187614, by rfl⟩ : syracuseStep 2001221 = 375229) (by norm_num)
theorem B952661 : Blo 888571 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B2001293 : Blo 888571 2001293 := bbase (se 3 (by rfl) ⟨375242, by rfl⟩ : syracuseStep 2001293 = 750485) (by norm_num)
theorem B1739213 : Blo 888571 1739213 := bbase (se 3 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 1739213 = 652205) (by norm_num)
theorem B2001365 : Blo 888571 2001365 := bbase (se 7 (by rfl) ⟨23453, by rfl⟩ : syracuseStep 2001365 = 46907) (by norm_num)
theorem B8554997 : Blo 888571 8554997 := bbase (se 5 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 8554997 = 802031) (by norm_num)
theorem B2001437 : Blo 888571 2001437 := bbase (se 3 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 2001437 = 750539) (by norm_num)
theorem B1608221 : Blo 888571 1608221 := bbase (se 3 (by rfl) ⟨301541, by rfl⟩ : syracuseStep 1608221 = 603083) (by norm_num)
theorem B2034229 : Blo 888571 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2001509 : Blo 888571 2001509 := bbase (se 4 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 2001509 = 375283) (by norm_num)
theorem B2001581 : Blo 888571 2001581 := bbase (se 3 (by rfl) ⟨375296, by rfl⟩ : syracuseStep 2001581 = 750593) (by norm_num)
theorem B3803861 : Blo 888571 3803861 := bbase (se 7 (by rfl) ⟨44576, by rfl⟩ : syracuseStep 3803861 = 89153) (by norm_num)
theorem B2001653 : Blo 888571 2001653 := bbase (se 5 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 2001653 = 187655) (by norm_num)
theorem B1608445 : Blo 888571 1608445 := bbase (se 3 (by rfl) ⟨301583, by rfl⟩ : syracuseStep 1608445 = 603167) (by norm_num)
theorem B953105 : Blo 888571 953105 := bbase (se 2 (by rfl) ⟨357414, by rfl⟩ : syracuseStep 953105 = 714829) (by norm_num)
theorem B2001725 : Blo 888571 2001725 := bbase (se 3 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 2001725 = 750647) (by norm_num)
theorem B2001797 : Blo 888571 2001797 := bbase (se 4 (by rfl) ⟨187668, by rfl⟩ : syracuseStep 2001797 = 375337) (by norm_num)
theorem B2001869 : Blo 888571 2001869 := bbase (se 3 (by rfl) ⟨375350, by rfl⟩ : syracuseStep 2001869 = 750701) (by norm_num)
theorem B2001941 : Blo 888571 2001941 := bbase (se 6 (by rfl) ⟨46920, by rfl⟩ : syracuseStep 2001941 = 93841) (by norm_num)
theorem B2002013 : Blo 888571 2002013 := bbase (se 3 (by rfl) ⟨375377, by rfl⟩ : syracuseStep 2002013 = 750755) (by norm_num)
theorem B3378293 : Blo 888571 3378293 := bbase (se 5 (by rfl) ⟨158357, by rfl⟩ : syracuseStep 3378293 = 316715) (by norm_num)
theorem B1903733 : Blo 888571 1903733 := bbase (se 5 (by rfl) ⟨89237, by rfl⟩ : syracuseStep 1903733 = 178475) (by norm_num)
theorem B2002085 : Blo 888571 2002085 := bbase (se 4 (by rfl) ⟨187695, by rfl⟩ : syracuseStep 2002085 = 375391) (by norm_num)
theorem B2002157 : Blo 888571 2002157 := bbase (se 3 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 2002157 = 750809) (by norm_num)
theorem B2002229 : Blo 888571 2002229 := bbase (se 5 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 2002229 = 187709) (by norm_num)
theorem B10128725 : Blo 888571 10128725 := bbase (se 11 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 10128725 = 14837) (by norm_num)
theorem B1903981 : Blo 888571 1903981 := bbase (se 3 (by rfl) ⟨356996, by rfl⟩ : syracuseStep 1903981 = 713993) (by norm_num)
theorem B2002301 : Blo 888571 2002301 := bbase (se 3 (by rfl) ⟨375431, by rfl⟩ : syracuseStep 2002301 = 750863) (by norm_num)
theorem B3378581 : Blo 888571 3378581 := bbase (se 6 (by rfl) ⟨79185, by rfl⟩ : syracuseStep 3378581 = 158371) (by norm_num)
theorem B2002373 : Blo 888571 2002373 := bbase (se 4 (by rfl) ⟨187722, by rfl⟩ : syracuseStep 2002373 = 375445) (by norm_num)
theorem B2002445 : Blo 888571 2002445 := bbase (se 3 (by rfl) ⟨375458, by rfl⟩ : syracuseStep 2002445 = 750917) (by norm_num)
theorem B3214885 : Blo 888571 3214885 := bbase (se 4 (by rfl) ⟨301395, by rfl⟩ : syracuseStep 3214885 = 602791) (by norm_num)
theorem B2002517 : Blo 888571 2002517 := bbase (se 8 (by rfl) ⟨11733, by rfl⟩ : syracuseStep 2002517 = 23467) (by norm_num)
theorem B6753941 : Blo 888571 6753941 := bbase (se 6 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 6753941 = 316591) (by norm_num)
theorem B2002589 : Blo 888571 2002589 := bbase (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) (by norm_num)
theorem B3215045 : Blo 888571 3215045 := bbase (se 4 (by rfl) ⟨301410, by rfl⟩ : syracuseStep 3215045 = 602821) (by norm_num)
theorem B2035397 : Blo 888571 2035397 := bbase (se 4 (by rfl) ⟨190818, by rfl⟩ : syracuseStep 2035397 = 381637) (by norm_num)
theorem B2002661 : Blo 888571 2002661 := bbase (se 4 (by rfl) ⟨187749, by rfl⟩ : syracuseStep 2002661 = 375499) (by norm_num)
theorem B2002733 : Blo 888571 2002733 := bbase (se 3 (by rfl) ⟨375512, by rfl⟩ : syracuseStep 2002733 = 751025) (by norm_num)
theorem B3215173 : Blo 888571 3215173 := bbase (se 4 (by rfl) ⟨301422, by rfl⟩ : syracuseStep 3215173 = 602845) (by norm_num)
theorem B1904485 : Blo 888571 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B2002805 : Blo 888571 2002805 := bbase (se 5 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 2002805 = 187763) (by norm_num)
theorem B6426485 : Blo 888571 6426485 := bbase (se 5 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 6426485 = 602483) (by norm_num)
theorem B2002877 : Blo 888571 2002877 := bbase (se 3 (by rfl) ⟨375539, by rfl⟩ : syracuseStep 2002877 = 751079) (by norm_num)
theorem B2002949 : Blo 888571 2002949 := bbase (se 4 (by rfl) ⟨187776, by rfl⟩ : syracuseStep 2002949 = 375553) (by norm_num)
theorem B2003021 : Blo 888571 2003021 := bbase (se 3 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 2003021 = 751133) (by norm_num)
theorem B2003093 : Blo 888571 2003093 := bbase (se 6 (by rfl) ⟨46947, by rfl⟩ : syracuseStep 2003093 = 93895) (by norm_num)
theorem B6426773 : Blo 888571 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B2003165 : Blo 888571 2003165 := bbase (se 3 (by rfl) ⟨375593, by rfl⟩ : syracuseStep 2003165 = 751187) (by norm_num)
theorem B2855189 : Blo 888571 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B2003237 : Blo 888571 2003237 := bbase (se 4 (by rfl) ⟨187803, by rfl⟩ : syracuseStep 2003237 = 375607) (by norm_num)
theorem B2003309 : Blo 888571 2003309 := bbase (se 3 (by rfl) ⟨375620, by rfl⟩ : syracuseStep 2003309 = 751241) (by norm_num)
theorem B2003381 : Blo 888571 2003381 := bbase (se 5 (by rfl) ⟨93908, by rfl⟩ : syracuseStep 2003381 = 187817) (by norm_num)
theorem B1085929 : Blo 888571 1085929 := bbase (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) (by norm_num)
theorem B2003453 : Blo 888571 2003453 := bbase (se 3 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 2003453 = 751295) (by norm_num)
theorem B3379765 : Blo 888571 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B2003525 : Blo 888571 2003525 := bbase (se 4 (by rfl) ⟨187830, by rfl⟩ : syracuseStep 2003525 = 375661) (by norm_num)
theorem B2003597 : Blo 888571 2003597 := bbase (se 3 (by rfl) ⟨375674, by rfl⟩ : syracuseStep 2003597 = 751349) (by norm_num)
theorem B2888405 : Blo 888571 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B2003669 : Blo 888571 2003669 := bbase (se 7 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 2003669 = 46961) (by norm_num)
theorem B6427349 : Blo 888571 6427349 := bbase (se 7 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 6427349 = 150641) (by norm_num)
theorem B1905373 : Blo 888571 1905373 := bbase (se 3 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 1905373 = 714515) (by norm_num)
theorem B2003741 : Blo 888571 2003741 := bbase (se 3 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 2003741 = 751403) (by norm_num)
theorem B3380069 : Blo 888571 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B2003813 : Blo 888571 2003813 := bbase (se 4 (by rfl) ⟨187857, by rfl⟩ : syracuseStep 2003813 = 375715) (by norm_num)
theorem B2003885 : Blo 888571 2003885 := bbase (se 3 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 2003885 = 751457) (by norm_num)
theorem B2003957 : Blo 888571 2003957 := bbase (se 5 (by rfl) ⟨93935, by rfl⟩ : syracuseStep 2003957 = 187871) (by norm_num)
theorem B2135069 : Blo 888571 2135069 := bbase (se 3 (by rfl) ⟨400325, by rfl⟩ : syracuseStep 2135069 = 800651) (by norm_num)
theorem B2004029 : Blo 888571 2004029 := bbase (se 3 (by rfl) ⟨375755, by rfl⟩ : syracuseStep 2004029 = 751511) (by norm_num)
theorem B2004101 : Blo 888571 2004101 := bbase (se 4 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 2004101 = 375769) (by norm_num)
theorem B2004173 : Blo 888571 2004173 := bbase (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) (by norm_num)
theorem B1905869 : Blo 888571 1905869 := bbase (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) (by norm_num)
theorem B2135261 : Blo 888571 2135261 := bbase (se 3 (by rfl) ⟨400361, by rfl⟩ : syracuseStep 2135261 = 800723) (by norm_num)
theorem B2004245 : Blo 888571 2004245 := bbase (se 6 (by rfl) ⟨46974, by rfl⟩ : syracuseStep 2004245 = 93949) (by norm_num)
theorem B2004317 : Blo 888571 2004317 := bbase (se 3 (by rfl) ⟨375809, by rfl⟩ : syracuseStep 2004317 = 751619) (by norm_num)
theorem B2004389 : Blo 888571 2004389 := bbase (se 4 (by rfl) ⟨187911, by rfl⟩ : syracuseStep 2004389 = 375823) (by norm_num)
theorem B2004461 : Blo 888571 2004461 := bbase (se 3 (by rfl) ⟨375836, by rfl⟩ : syracuseStep 2004461 = 751673) (by norm_num)
theorem B2856485 : Blo 888571 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B2004533 : Blo 888571 2004533 := bbase (se 5 (by rfl) ⟨93962, by rfl⟩ : syracuseStep 2004533 = 187925) (by norm_num)
theorem B2004605 : Blo 888571 2004605 := bbase (se 3 (by rfl) ⟨375863, by rfl⟩ : syracuseStep 2004605 = 751727) (by norm_num)
theorem B2004677 : Blo 888571 2004677 := bbase (se 4 (by rfl) ⟨187938, by rfl⟩ : syracuseStep 2004677 = 375877) (by norm_num)
theorem B2004749 : Blo 888571 2004749 := bbase (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) (by norm_num)
theorem B2004821 : Blo 888571 2004821 := bbase (se 9 (by rfl) ⟨5873, by rfl⟩ : syracuseStep 2004821 = 11747) (by norm_num)
theorem B2004893 : Blo 888571 2004893 := bbase (se 3 (by rfl) ⟨375917, by rfl⟩ : syracuseStep 2004893 = 751835) (by norm_num)
theorem B3807157 : Blo 888571 3807157 := bbase (se 5 (by rfl) ⟨178460, by rfl⟩ : syracuseStep 3807157 = 356921) (by norm_num)
theorem B2004965 : Blo 888571 2004965 := bbase (se 4 (by rfl) ⟨187965, by rfl⟩ : syracuseStep 2004965 = 375931) (by norm_num)
theorem B1710101 : Blo 888571 1710101 := bbase (se 6 (by rfl) ⟨40080, by rfl⟩ : syracuseStep 1710101 = 80161) (by norm_num)
theorem B2005037 : Blo 888571 2005037 := bbase (se 3 (by rfl) ⟨375944, by rfl⟩ : syracuseStep 2005037 = 751889) (by norm_num)
theorem B7608437 : Blo 888571 7608437 := bbase (se 5 (by rfl) ⟨356645, by rfl⟩ : syracuseStep 7608437 = 713291) (by norm_num)
theorem B2005109 : Blo 888571 2005109 := bbase (se 5 (by rfl) ⟨93989, by rfl⟩ : syracuseStep 2005109 = 187979) (by norm_num)
theorem B2136221 : Blo 888571 2136221 := bbase (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) (by norm_num)
theorem B2005181 : Blo 888571 2005181 := bbase (se 3 (by rfl) ⟨375971, by rfl⟩ : syracuseStep 2005181 = 751943) (by norm_num)
theorem B2005253 : Blo 888571 2005253 := bbase (se 4 (by rfl) ⟨187992, by rfl⟩ : syracuseStep 2005253 = 375985) (by norm_num)
theorem B2201861 : Blo 888571 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B2005325 : Blo 888571 2005325 := bbase (se 3 (by rfl) ⟨375998, by rfl⟩ : syracuseStep 2005325 = 751997) (by norm_num)
theorem B2005397 : Blo 888571 2005397 := bbase (se 6 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 2005397 = 94003) (by norm_num)
theorem B2005469 : Blo 888571 2005469 := bbase (se 3 (by rfl) ⟨376025, by rfl⟩ : syracuseStep 2005469 = 752051) (by norm_num)
theorem B2005541 : Blo 888571 2005541 := bbase (se 4 (by rfl) ⟨188019, by rfl⟩ : syracuseStep 2005541 = 376039) (by norm_num)
theorem B2005613 : Blo 888571 2005613 := bbase (se 3 (by rfl) ⟨376052, by rfl⟩ : syracuseStep 2005613 = 752105) (by norm_num)
theorem B989869 : Blo 888571 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B2005685 : Blo 888571 2005685 := bbase (se 5 (by rfl) ⟨94016, by rfl⟩ : syracuseStep 2005685 = 188033) (by norm_num)
theorem B2005757 : Blo 888571 2005757 := bbase (se 3 (by rfl) ⟨376079, by rfl⟩ : syracuseStep 2005757 = 752159) (by norm_num)
theorem B2005829 : Blo 888571 2005829 := bbase (se 4 (by rfl) ⟨188046, by rfl⟩ : syracuseStep 2005829 = 376093) (by norm_num)
theorem B4070213 : Blo 888571 4070213 := bbase (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) (by norm_num)
theorem B2005901 : Blo 888571 2005901 := bbase (se 3 (by rfl) ⟨376106, by rfl⟩ : syracuseStep 2005901 = 752213) (by norm_num)
theorem B3611557 : Blo 888571 3611557 := bbase (se 4 (by rfl) ⟨338583, by rfl⟩ : syracuseStep 3611557 = 677167) (by norm_num)
theorem B3382181 : Blo 888571 3382181 := bbase (se 4 (by rfl) ⟨317079, by rfl⟩ : syracuseStep 3382181 = 634159) (by norm_num)
theorem B2005973 : Blo 888571 2005973 := bbase (se 7 (by rfl) ⟨23507, by rfl⟩ : syracuseStep 2005973 = 47015) (by norm_num)
theorem B3611621 : Blo 888571 3611621 := bbase (se 4 (by rfl) ⟨338589, by rfl⟩ : syracuseStep 3611621 = 677179) (by norm_num)
theorem B5708789 : Blo 888571 5708789 := bbase (se 5 (by rfl) ⟨267599, by rfl⟩ : syracuseStep 5708789 = 535199) (by norm_num)
theorem B2006045 : Blo 888571 2006045 := bbase (se 3 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 2006045 = 752267) (by norm_num)
theorem B2006117 : Blo 888571 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B2006189 : Blo 888571 2006189 := bbase (se 3 (by rfl) ⟨376160, by rfl⟩ : syracuseStep 2006189 = 752321) (by norm_num)
theorem B3382469 : Blo 888571 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B2006261 : Blo 888571 2006261 := bbase (se 5 (by rfl) ⟨94043, by rfl⟩ : syracuseStep 2006261 = 188087) (by norm_num)
theorem B2530565 : Blo 888571 2530565 := bbase (se 4 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 2530565 = 474481) (by norm_num)
theorem B2006333 : Blo 888571 2006333 := bbase (se 3 (by rfl) ⟨376187, by rfl⟩ : syracuseStep 2006333 = 752375) (by norm_num)
theorem B2858341 : Blo 888571 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B2006405 : Blo 888571 2006405 := bbase (se 4 (by rfl) ⟨188100, by rfl⟩ : syracuseStep 2006405 = 376201) (by norm_num)
theorem B2006477 : Blo 888571 2006477 := bbase (se 3 (by rfl) ⟨376214, by rfl⟩ : syracuseStep 2006477 = 752429) (by norm_num)
theorem B2006549 : Blo 888571 2006549 := bbase (se 6 (by rfl) ⟨47028, by rfl⟩ : syracuseStep 2006549 = 94057) (by norm_num)
theorem B2006621 : Blo 888571 2006621 := bbase (se 3 (by rfl) ⟨376241, by rfl⟩ : syracuseStep 2006621 = 752483) (by norm_num)
theorem B2006693 : Blo 888571 2006693 := bbase (se 4 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 2006693 = 376255) (by norm_num)
theorem B2530997 : Blo 888571 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B2006765 : Blo 888571 2006765 := bbase (se 3 (by rfl) ⟨376268, by rfl⟩ : syracuseStep 2006765 = 752537) (by norm_num)
theorem B2006837 : Blo 888571 2006837 := bbase (se 5 (by rfl) ⟨94070, by rfl⟩ : syracuseStep 2006837 = 188141) (by norm_num)
theorem B925553 : Blo 888571 925553 := bbase (se 2 (by rfl) ⟨347082, by rfl⟩ : syracuseStep 925553 = 694165) (by norm_num)
theorem B1351549 : Blo 888571 1351549 := bbase (se 3 (by rfl) ⟨253415, by rfl⟩ : syracuseStep 1351549 = 506831) (by norm_num)
theorem B2006909 : Blo 888571 2006909 := bbase (se 3 (by rfl) ⟨376295, by rfl⟩ : syracuseStep 2006909 = 752591) (by norm_num)
theorem B2006981 : Blo 888571 2006981 := bbase (se 4 (by rfl) ⟨188154, by rfl⟩ : syracuseStep 2006981 = 376309) (by norm_num)
theorem B2007053 : Blo 888571 2007053 := bbase (se 3 (by rfl) ⟨376322, by rfl⟩ : syracuseStep 2007053 = 752645) (by norm_num)
theorem B3711013 : Blo 888571 3711013 := bbase (se 4 (by rfl) ⟨347907, by rfl⟩ : syracuseStep 3711013 = 695815) (by norm_num)
theorem B2007125 : Blo 888571 2007125 := bbase (se 8 (by rfl) ⟨11760, by rfl⟩ : syracuseStep 2007125 = 23521) (by norm_num)
theorem B17080469 : Blo 888571 17080469 := bbase (se 6 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 17080469 = 800647) (by norm_num)
theorem B2007197 : Blo 888571 2007197 := bbase (se 3 (by rfl) ⟨376349, by rfl⟩ : syracuseStep 2007197 = 752699) (by norm_num)
theorem B2007269 : Blo 888571 2007269 := bbase (se 4 (by rfl) ⟨188181, by rfl⟩ : syracuseStep 2007269 = 376363) (by norm_num)
theorem B2007341 : Blo 888571 2007341 := bbase (se 3 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 2007341 = 752753) (by norm_num)
theorem B3383653 : Blo 888571 3383653 := bbase (se 4 (by rfl) ⟨317217, by rfl⟩ : syracuseStep 3383653 = 634435) (by norm_num)
theorem B2007413 : Blo 888571 2007413 := bbase (se 5 (by rfl) ⟨94097, by rfl⟩ : syracuseStep 2007413 = 188195) (by norm_num)
theorem B2531749 : Blo 888571 2531749 := bbase (se 4 (by rfl) ⟨237351, by rfl⟩ : syracuseStep 2531749 = 474703) (by norm_num)
theorem B2007485 : Blo 888571 2007485 := bbase (se 3 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 2007485 = 752807) (by norm_num)
theorem B2007557 : Blo 888571 2007557 := bbase (se 4 (by rfl) ⟨188208, by rfl⟩ : syracuseStep 2007557 = 376417) (by norm_num)
theorem B1352261 : Blo 888571 1352261 := bbase (se 4 (by rfl) ⟨126774, by rfl⟩ : syracuseStep 1352261 = 253549) (by norm_num)
theorem B2007629 : Blo 888571 2007629 := bbase (se 3 (by rfl) ⟨376430, by rfl⟩ : syracuseStep 2007629 = 752861) (by norm_num)
theorem B3383957 : Blo 888571 3383957 := bbase (se 6 (by rfl) ⟨79311, by rfl⟩ : syracuseStep 3383957 = 158623) (by norm_num)
theorem B2007701 : Blo 888571 2007701 := bbase (se 6 (by rfl) ⟨47055, by rfl⟩ : syracuseStep 2007701 = 94111) (by norm_num)
theorem B2007773 : Blo 888571 2007773 := bbase (se 3 (by rfl) ⟨376457, by rfl⟩ : syracuseStep 2007773 = 752915) (by norm_num)
theorem B2007845 : Blo 888571 2007845 := bbase (se 4 (by rfl) ⟨188235, by rfl⟩ : syracuseStep 2007845 = 376471) (by norm_num)
theorem B5481269 : Blo 888571 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B3810149 : Blo 888571 3810149 := bbase (se 4 (by rfl) ⟨357201, by rfl⟩ : syracuseStep 3810149 = 714403) (by norm_num)
theorem B2138989 : Blo 888571 2138989 := bbase (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) (by norm_num)
theorem B2007917 : Blo 888571 2007917 := bbase (se 3 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 2007917 = 752969) (by norm_num)
theorem B2007989 : Blo 888571 2007989 := bbase (se 5 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 2007989 = 188249) (by norm_num)
theorem B2008061 : Blo 888571 2008061 := bbase (se 3 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 2008061 = 753023) (by norm_num)
theorem B1352717 : Blo 888571 1352717 := bbase (se 3 (by rfl) ⟨253634, by rfl⟩ : syracuseStep 1352717 = 507269) (by norm_num)
theorem B2008133 : Blo 888571 2008133 := bbase (se 4 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 2008133 = 376525) (by norm_num)
theorem B2008205 : Blo 888571 2008205 := bbase (se 3 (by rfl) ⟨376538, by rfl⟩ : syracuseStep 2008205 = 753077) (by norm_num)
theorem B2008277 : Blo 888571 2008277 := bbase (se 7 (by rfl) ⟨23534, by rfl⟩ : syracuseStep 2008277 = 47069) (by norm_num)
theorem B2139365 : Blo 888571 2139365 := bbase (se 4 (by rfl) ⟨200565, by rfl⟩ : syracuseStep 2139365 = 401131) (by norm_num)
theorem B2172149 : Blo 888571 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B4498901 : Blo 888571 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B3253765 : Blo 888571 3253765 := bbase (se 4 (by rfl) ⟨305040, by rfl⟩ : syracuseStep 3253765 = 610081) (by norm_num)
theorem B1353349 : Blo 888571 1353349 := bbase (se 4 (by rfl) ⟨126876, by rfl⟩ : syracuseStep 1353349 = 253753) (by norm_num)
theorem B2139797 : Blo 888571 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B3811157 : Blo 888571 3811157 := bbase (se 9 (by rfl) ⟨11165, by rfl⟩ : syracuseStep 3811157 = 22331) (by norm_num)
theorem B4565045 : Blo 888571 4565045 := bbase (se 5 (by rfl) ⟨213986, by rfl⟩ : syracuseStep 4565045 = 427973) (by norm_num)
theorem B2140373 : Blo 888571 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B7317845 : Blo 888571 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B1124705 : Blo 888571 1124705 := bbase (se 2 (by rfl) ⟨421764, by rfl⟩ : syracuseStep 1124705 = 843529) (by norm_num)
theorem B1124761 : Blo 888571 1124761 := bbase (se 2 (by rfl) ⟨421785, by rfl⟩ : syracuseStep 1124761 = 843571) (by norm_num)
theorem B1124857 : Blo 888571 1124857 := bbase (se 2 (by rfl) ⟨421821, by rfl⟩ : syracuseStep 1124857 = 843643) (by norm_num)
theorem B1125029 : Blo 888571 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B25701077 : Blo 888571 25701077 := bbase (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) (by norm_num)
theorem B3386069 : Blo 888571 3386069 := bbase (se 7 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 3386069 = 79361) (by norm_num)
theorem B1125085 : Blo 888571 1125085 := bbase (se 3 (by rfl) ⟨210953, by rfl⟩ : syracuseStep 1125085 = 421907) (by norm_num)
theorem B4500197 : Blo 888571 4500197 := bbase (se 4 (by rfl) ⟨421893, by rfl⟩ : syracuseStep 4500197 = 843787) (by norm_num)
theorem B1125181 : Blo 888571 1125181 := bbase (se 3 (by rfl) ⟨210971, by rfl⟩ : syracuseStep 1125181 = 421943) (by norm_num)
theorem B1354693 : Blo 888571 1354693 := bbase (se 4 (by rfl) ⟨127002, by rfl⟩ : syracuseStep 1354693 = 254005) (by norm_num)
theorem B1125353 : Blo 888571 1125353 := bbase (se 2 (by rfl) ⟨422007, by rfl⟩ : syracuseStep 1125353 = 844015) (by norm_num)
theorem B3386357 : Blo 888571 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B1125409 : Blo 888571 1125409 := bbase (se 2 (by rfl) ⟨422028, by rfl⟩ : syracuseStep 1125409 = 844057) (by norm_num)
theorem B2403445 : Blo 888571 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B1125505 : Blo 888571 1125505 := bbase (se 2 (by rfl) ⟨422064, by rfl⟩ : syracuseStep 1125505 = 844129) (by norm_num)
theorem B2534597 : Blo 888571 2534597 := bbase (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) (by norm_num)
theorem B6761717 : Blo 888571 6761717 := bbase (se 5 (by rfl) ⟨316955, by rfl⟩ : syracuseStep 6761717 = 633911) (by norm_num)
theorem B1125677 : Blo 888571 1125677 := bbase (se 3 (by rfl) ⟨211064, by rfl⟩ : syracuseStep 1125677 = 422129) (by norm_num)
theorem B1125733 : Blo 888571 1125733 := bbase (se 4 (by rfl) ⟨105537, by rfl⟩ : syracuseStep 1125733 = 211075) (by norm_num)
theorem B1125829 : Blo 888571 1125829 := bbase (se 4 (by rfl) ⟨105546, by rfl⟩ : syracuseStep 1125829 = 211093) (by norm_num)
theorem B1126001 : Blo 888571 1126001 := bbase (se 2 (by rfl) ⟨422250, by rfl⟩ : syracuseStep 1126001 = 844501) (by norm_num)
theorem B1126057 : Blo 888571 1126057 := bbase (se 2 (by rfl) ⟨422271, by rfl⟩ : syracuseStep 1126057 = 844543) (by norm_num)
theorem B3092213 : Blo 888571 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B1126153 : Blo 888571 1126153 := bbase (se 2 (by rfl) ⟨422307, by rfl⟩ : syracuseStep 1126153 = 844615) (by norm_num)
theorem B1126325 : Blo 888571 1126325 := bbase (se 5 (by rfl) ⟨52796, by rfl⟩ : syracuseStep 1126325 = 105593) (by norm_num)
theorem B9646037 : Blo 888571 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B1126381 : Blo 888571 1126381 := bbase (se 3 (by rfl) ⟨211196, by rfl⟩ : syracuseStep 1126381 = 422393) (by norm_num)
theorem B4501493 : Blo 888571 4501493 := bbase (se 5 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 4501493 = 422015) (by norm_num)
theorem B1126477 : Blo 888571 1126477 := bbase (se 3 (by rfl) ⟨211214, by rfl⟩ : syracuseStep 1126477 = 422429) (by norm_num)
theorem B3387541 : Blo 888571 3387541 := bbase (se 6 (by rfl) ⟨79395, by rfl⟩ : syracuseStep 3387541 = 158791) (by norm_num)
theorem B1126649 : Blo 888571 1126649 := bbase (se 2 (by rfl) ⟨422493, by rfl⟩ : syracuseStep 1126649 = 844987) (by norm_num)
theorem B1126705 : Blo 888571 1126705 := bbase (se 2 (by rfl) ⟨422514, by rfl⟩ : syracuseStep 1126705 = 845029) (by norm_num)
theorem B8106293 : Blo 888571 8106293 := bbase (se 5 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 8106293 = 759965) (by norm_num)
theorem B22819157 : Blo 888571 22819157 := bbase (se 10 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 22819157 = 66853) (by norm_num)
theorem B2535781 : Blo 888571 2535781 := bbase (se 4 (by rfl) ⟨237729, by rfl⟩ : syracuseStep 2535781 = 475459) (by norm_num)
theorem B1126801 : Blo 888571 1126801 := bbase (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) (by norm_num)
theorem B3387845 : Blo 888571 3387845 := bbase (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) (by norm_num)
theorem B5419477 : Blo 888571 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B2535941 : Blo 888571 2535941 := bbase (se 4 (by rfl) ⟨237744, by rfl⟩ : syracuseStep 2535941 = 475489) (by norm_num)
theorem B1126973 : Blo 888571 1126973 := bbase (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) (by norm_num)
theorem B1127029 : Blo 888571 1127029 := bbase (se 5 (by rfl) ⟨52829, by rfl⟩ : syracuseStep 1127029 = 105659) (by norm_num)
theorem B5419669 : Blo 888571 5419669 := bbase (se 6 (by rfl) ⟨127023, by rfl⟩ : syracuseStep 5419669 = 254047) (by norm_num)
theorem B1127125 : Blo 888571 1127125 := bbase (se 7 (by rfl) ⟨13208, by rfl⟩ : syracuseStep 1127125 = 26417) (by norm_num)
theorem B2142949 : Blo 888571 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B2536181 : Blo 888571 2536181 := bbase (se 5 (by rfl) ⟨118883, by rfl⟩ : syracuseStep 2536181 = 237767) (by norm_num)
theorem B1127297 : Blo 888571 1127297 := bbase (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) (by norm_num)
theorem B5714837 : Blo 888571 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B2536373 : Blo 888571 2536373 := bbase (se 5 (by rfl) ⟨118892, by rfl⟩ : syracuseStep 2536373 = 237785) (by norm_num)
theorem B1127353 : Blo 888571 1127353 := bbase (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) (by norm_num)
theorem B3093461 : Blo 888571 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B1127449 : Blo 888571 1127449 := bbase (se 2 (by rfl) ⟨422793, by rfl⟩ : syracuseStep 1127449 = 845587) (by norm_num)
theorem B1127621 : Blo 888571 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B1127677 : Blo 888571 1127677 := bbase (se 3 (by rfl) ⟨211439, by rfl⟩ : syracuseStep 1127677 = 422879) (by norm_num)
theorem B4502789 : Blo 888571 4502789 := bbase (se 4 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 4502789 = 844273) (by norm_num)
theorem B1127773 : Blo 888571 1127773 := bbase (se 3 (by rfl) ⟨211457, by rfl⟩ : syracuseStep 1127773 = 422915) (by norm_num)
theorem B1127945 : Blo 888571 1127945 := bbase (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) (by norm_num)
theorem B1128001 : Blo 888571 1128001 := bbase (se 2 (by rfl) ⟨423000, by rfl⟩ : syracuseStep 1128001 = 846001) (by norm_num)
theorem B1128097 : Blo 888571 1128097 := bbase (se 2 (by rfl) ⟨423036, by rfl⟩ : syracuseStep 1128097 = 846073) (by norm_num)
theorem B2406149 : Blo 888571 2406149 := bbase (se 4 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 2406149 = 451153) (by norm_num)
theorem B1128269 : Blo 888571 1128269 := bbase (se 3 (by rfl) ⟨211550, by rfl⟩ : syracuseStep 1128269 = 423101) (by norm_num)
theorem B1128325 : Blo 888571 1128325 := bbase (se 4 (by rfl) ⟨105780, by rfl⟩ : syracuseStep 1128325 = 211561) (by norm_num)
theorem B2144141 : Blo 888571 2144141 := bbase (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) (by norm_num)
theorem B2537365 : Blo 888571 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B4274117 : Blo 888571 4274117 := bbase (se 4 (by rfl) ⟨400698, by rfl⟩ : syracuseStep 4274117 = 801397) (by norm_num)
theorem B1128421 : Blo 888571 1128421 := bbase (se 4 (by rfl) ⟨105789, by rfl⟩ : syracuseStep 1128421 = 211579) (by norm_num)
theorem B7616501 : Blo 888571 7616501 := bbase (se 5 (by rfl) ⟨357023, by rfl⟩ : syracuseStep 7616501 = 714047) (by norm_num)
theorem B2144333 : Blo 888571 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B1128593 : Blo 888571 1128593 := bbase (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) (by norm_num)
theorem B9615509 : Blo 888571 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B2406581 : Blo 888571 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B1128649 : Blo 888571 1128649 := bbase (se 2 (by rfl) ⟨423243, by rfl⟩ : syracuseStep 1128649 = 846487) (by norm_num)
theorem B1423597 : Blo 888571 1423597 := bbase (se 3 (by rfl) ⟨266924, by rfl⟩ : syracuseStep 1423597 = 533849) (by norm_num)
theorem B1128745 : Blo 888571 1128745 := bbase (se 2 (by rfl) ⟨423279, by rfl⟩ : syracuseStep 1128745 = 846559) (by norm_num)
theorem B3422677 : Blo 888571 3422677 := bbase (se 7 (by rfl) ⟨40109, by rfl⟩ : syracuseStep 3422677 = 80219) (by norm_num)
theorem B1128917 : Blo 888571 1128917 := bbase (se 7 (by rfl) ⟨13229, by rfl⟩ : syracuseStep 1128917 = 26459) (by norm_num)
theorem B1128973 : Blo 888571 1128973 := bbase (se 3 (by rfl) ⟨211682, by rfl⟩ : syracuseStep 1128973 = 423365) (by norm_num)
theorem B4504085 : Blo 888571 4504085 := bbase (se 6 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 4504085 = 211129) (by norm_num)
theorem B1129069 : Blo 888571 1129069 := bbase (se 3 (by rfl) ⟨211700, by rfl⟩ : syracuseStep 1129069 = 423401) (by norm_num)
theorem B1424045 : Blo 888571 1424045 := bbase (se 3 (by rfl) ⟨267008, by rfl⟩ : syracuseStep 1424045 = 534017) (by norm_num)
theorem B2407141 : Blo 888571 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B1129241 : Blo 888571 1129241 := bbase (se 2 (by rfl) ⟨423465, by rfl⟩ : syracuseStep 1129241 = 846931) (by norm_num)
theorem B1129297 : Blo 888571 1129297 := bbase (se 2 (by rfl) ⟨423486, by rfl⟩ : syracuseStep 1129297 = 846973) (by norm_num)
theorem B1129393 : Blo 888571 1129393 := bbase (se 2 (by rfl) ⟨423522, by rfl⟩ : syracuseStep 1129393 = 847045) (by norm_num)
theorem B2538469 : Blo 888571 2538469 := bbase (se 4 (by rfl) ⟨237981, by rfl⟩ : syracuseStep 2538469 = 475963) (by norm_num)
theorem B3652613 : Blo 888571 3652613 := bbase (se 4 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 3652613 = 684865) (by norm_num)
theorem B1129565 : Blo 888571 1129565 := bbase (se 3 (by rfl) ⟨211793, by rfl⟩ : syracuseStep 1129565 = 423587) (by norm_num)
theorem B1129621 : Blo 888571 1129621 := bbase (se 6 (by rfl) ⟨26475, by rfl⟩ : syracuseStep 1129621 = 52951) (by norm_num)
theorem B1686997 : Blo 888571 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B1687301 : Blo 888571 1687301 := bbase (se 4 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 1687301 = 316369) (by norm_num)
theorem B4505381 : Blo 888571 4505381 := bbase (se 4 (by rfl) ⟨422379, by rfl⟩ : syracuseStep 4505381 = 844759) (by norm_num)
theorem B901121 : Blo 888571 901121 := bbase (se 2 (by rfl) ⟨337920, by rfl⟩ : syracuseStep 901121 = 675841) (by norm_num)
theorem B1425557 : Blo 888571 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B999661 : Blo 888571 999661 := bbase (se 3 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 999661 = 374873) (by norm_num)
theorem B999697 : Blo 888571 999697 := bbase (se 2 (by rfl) ⟨374886, by rfl⟩ : syracuseStep 999697 = 749773) (by norm_num)
theorem B1425685 : Blo 888571 1425685 := bbase (se 6 (by rfl) ⟨33414, by rfl⟩ : syracuseStep 1425685 = 66829) (by norm_num)
theorem B999733 : Blo 888571 999733 := bbase (se 5 (by rfl) ⟨46862, by rfl⟩ : syracuseStep 999733 = 93725) (by norm_num)
theorem B999769 : Blo 888571 999769 := bbase (se 2 (by rfl) ⟨374913, by rfl⟩ : syracuseStep 999769 = 749827) (by norm_num)
theorem B999805 : Blo 888571 999805 := bbase (se 3 (by rfl) ⟨187463, by rfl⟩ : syracuseStep 999805 = 374927) (by norm_num)
theorem B999841 : Blo 888571 999841 := bbase (se 2 (by rfl) ⟨374940, by rfl⟩ : syracuseStep 999841 = 749881) (by norm_num)
theorem B999877 : Blo 888571 999877 := bbase (se 4 (by rfl) ⟨93738, by rfl⟩ : syracuseStep 999877 = 187477) (by norm_num)
theorem B2539973 : Blo 888571 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B999913 : Blo 888571 999913 := bbase (se 2 (by rfl) ⟨374967, by rfl⟩ : syracuseStep 999913 = 749935) (by norm_num)
theorem B1688053 : Blo 888571 1688053 := bbase (se 5 (by rfl) ⟨79127, by rfl⟩ : syracuseStep 1688053 = 158255) (by norm_num)
theorem B999949 : Blo 888571 999949 := bbase (se 3 (by rfl) ⟨187490, by rfl⟩ : syracuseStep 999949 = 374981) (by norm_num)
theorem B901649 : Blo 888571 901649 := bbase (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) (by norm_num)
theorem B999985 : Blo 888571 999985 := bbase (se 2 (by rfl) ⟨374994, by rfl⟩ : syracuseStep 999985 = 749989) (by norm_num)
theorem B1000021 : Blo 888571 1000021 := bbase (se 8 (by rfl) ⟨5859, by rfl⟩ : syracuseStep 1000021 = 11719) (by norm_num)
theorem B1000057 : Blo 888571 1000057 := bbase (se 2 (by rfl) ⟨375021, by rfl⟩ : syracuseStep 1000057 = 750043) (by norm_num)
theorem B1688197 : Blo 888571 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B1000093 : Blo 888571 1000093 := bbase (se 3 (by rfl) ⟨187517, by rfl⟩ : syracuseStep 1000093 = 375035) (by norm_num)
theorem B4276901 : Blo 888571 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B1000129 : Blo 888571 1000129 := bbase (se 2 (by rfl) ⟨375048, by rfl⟩ : syracuseStep 1000129 = 750097) (by norm_num)
theorem B2998997 : Blo 888571 2998997 := bbase (se 7 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 2998997 = 70289) (by norm_num)
theorem B1000165 : Blo 888571 1000165 := bbase (se 4 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 1000165 = 187531) (by norm_num)
theorem B1000201 : Blo 888571 1000201 := bbase (se 2 (by rfl) ⟨375075, by rfl⟩ : syracuseStep 1000201 = 750151) (by norm_num)
theorem B1688357 : Blo 888571 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B1000237 : Blo 888571 1000237 := bbase (se 3 (by rfl) ⟨187544, by rfl⟩ : syracuseStep 1000237 = 375089) (by norm_num)
theorem B1000273 : Blo 888571 1000273 := bbase (se 2 (by rfl) ⟨375102, by rfl⟩ : syracuseStep 1000273 = 750205) (by norm_num)
theorem B1000309 : Blo 888571 1000309 := bbase (se 5 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 1000309 = 93779) (by norm_num)
theorem B1000345 : Blo 888571 1000345 := bbase (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) (by norm_num)
theorem B1688501 : Blo 888571 1688501 := bbase (se 5 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 1688501 = 158297) (by norm_num)
theorem B1000381 : Blo 888571 1000381 := bbase (se 3 (by rfl) ⟨187571, by rfl⟩ : syracuseStep 1000381 = 375143) (by norm_num)
theorem B1000417 : Blo 888571 1000417 := bbase (se 2 (by rfl) ⟨375156, by rfl⟩ : syracuseStep 1000417 = 750313) (by norm_num)
theorem B1000453 : Blo 888571 1000453 := bbase (se 4 (by rfl) ⟨93792, by rfl⟩ : syracuseStep 1000453 = 187585) (by norm_num)
theorem B1000489 : Blo 888571 1000489 := bbase (se 2 (by rfl) ⟨375183, by rfl⟩ : syracuseStep 1000489 = 750367) (by norm_num)
theorem B4506677 : Blo 888571 4506677 := bbase (se 5 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 4506677 = 422501) (by norm_num)
theorem B1000525 : Blo 888571 1000525 := bbase (se 3 (by rfl) ⟨187598, by rfl⟩ : syracuseStep 1000525 = 375197) (by norm_num)
theorem B902225 : Blo 888571 902225 := bbase (se 2 (by rfl) ⟨338334, by rfl⟩ : syracuseStep 902225 = 676669) (by norm_num)
theorem B1000561 : Blo 888571 1000561 := bbase (se 2 (by rfl) ⟨375210, by rfl⟩ : syracuseStep 1000561 = 750421) (by norm_num)
theorem B2999429 : Blo 888571 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B1000597 : Blo 888571 1000597 := bbase (se 6 (by rfl) ⟨23451, by rfl⟩ : syracuseStep 1000597 = 46903) (by norm_num)
theorem B1000633 : Blo 888571 1000633 := bbase (se 2 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 1000633 = 750475) (by norm_num)
theorem B1688789 : Blo 888571 1688789 := bbase (se 7 (by rfl) ⟨19790, by rfl⟩ : syracuseStep 1688789 = 39581) (by norm_num)
theorem B1000669 : Blo 888571 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B1000705 : Blo 888571 1000705 := bbase (se 2 (by rfl) ⟨375264, by rfl⟩ : syracuseStep 1000705 = 750529) (by norm_num)
theorem B1000741 : Blo 888571 1000741 := bbase (se 4 (by rfl) ⟨93819, by rfl⟩ : syracuseStep 1000741 = 187639) (by norm_num)
theorem B1000777 : Blo 888571 1000777 := bbase (se 2 (by rfl) ⟨375291, by rfl⟩ : syracuseStep 1000777 = 750583) (by norm_num)
theorem B1000813 : Blo 888571 1000813 := bbase (se 3 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 1000813 = 375305) (by norm_num)
theorem B1688941 : Blo 888571 1688941 := bbase (se 3 (by rfl) ⟨316676, by rfl⟩ : syracuseStep 1688941 = 633353) (by norm_num)
theorem B1000849 : Blo 888571 1000849 := bbase (se 2 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 1000849 = 750637) (by norm_num)
theorem B902549 : Blo 888571 902549 := bbase (se 6 (by rfl) ⟨21153, by rfl⟩ : syracuseStep 902549 = 42307) (by norm_num)
theorem B1000885 : Blo 888571 1000885 := bbase (se 5 (by rfl) ⟨46916, by rfl⟩ : syracuseStep 1000885 = 93833) (by norm_num)
theorem B1000921 : Blo 888571 1000921 := bbase (se 2 (by rfl) ⟨375345, by rfl⟩ : syracuseStep 1000921 = 750691) (by norm_num)
theorem B1000957 : Blo 888571 1000957 := bbase (se 3 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 1000957 = 375359) (by norm_num)
theorem B1000993 : Blo 888571 1000993 := bbase (se 2 (by rfl) ⟨375372, by rfl⟩ : syracuseStep 1000993 = 750745) (by norm_num)
theorem B2999861 : Blo 888571 2999861 := bbase (se 5 (by rfl) ⟨140618, by rfl⟩ : syracuseStep 2999861 = 281237) (by norm_num)
theorem B1001029 : Blo 888571 1001029 := bbase (se 4 (by rfl) ⟨93846, by rfl⟩ : syracuseStep 1001029 = 187693) (by norm_num)
theorem B1001065 : Blo 888571 1001065 := bbase (se 2 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 1001065 = 750799) (by norm_num)
theorem B1427069 : Blo 888571 1427069 := bbase (se 3 (by rfl) ⟨267575, by rfl⟩ : syracuseStep 1427069 = 535151) (by norm_num)
theorem B1001101 : Blo 888571 1001101 := bbase (se 3 (by rfl) ⟨187706, by rfl⟩ : syracuseStep 1001101 = 375413) (by norm_num)
theorem B1689245 : Blo 888571 1689245 := bbase (se 3 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 1689245 = 633467) (by norm_num)
theorem B1525405 : Blo 888571 1525405 := bbase (se 3 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 1525405 = 572027) (by norm_num)
theorem B1001137 : Blo 888571 1001137 := bbase (se 2 (by rfl) ⟨375426, by rfl⟩ : syracuseStep 1001137 = 750853) (by norm_num)
theorem B1001173 : Blo 888571 1001173 := bbase (se 7 (by rfl) ⟨11732, by rfl⟩ : syracuseStep 1001173 = 23465) (by norm_num)
theorem B902881 : Blo 888571 902881 := bbase (se 2 (by rfl) ⟨338580, by rfl⟩ : syracuseStep 902881 = 677161) (by norm_num)
theorem B1001209 : Blo 888571 1001209 := bbase (se 2 (by rfl) ⟨375453, by rfl⟩ : syracuseStep 1001209 = 750907) (by norm_num)
theorem B1001245 : Blo 888571 1001245 := bbase (se 3 (by rfl) ⟨187733, by rfl⟩ : syracuseStep 1001245 = 375467) (by norm_num)
theorem B1001281 : Blo 888571 1001281 := bbase (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) (by norm_num)
theorem B1001317 : Blo 888571 1001317 := bbase (se 4 (by rfl) ⟨93873, by rfl⟩ : syracuseStep 1001317 = 187747) (by norm_num)
theorem B1001353 : Blo 888571 1001353 := bbase (se 2 (by rfl) ⟨375507, by rfl⟩ : syracuseStep 1001353 = 751015) (by norm_num)
theorem B1001389 : Blo 888571 1001389 := bbase (se 3 (by rfl) ⟨187760, by rfl⟩ : syracuseStep 1001389 = 375521) (by norm_num)
theorem B1001425 : Blo 888571 1001425 := bbase (se 2 (by rfl) ⟨375534, by rfl⟩ : syracuseStep 1001425 = 751069) (by norm_num)
theorem B3000293 : Blo 888571 3000293 := bbase (se 4 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 3000293 = 562555) (by norm_num)
theorem B1001461 : Blo 888571 1001461 := bbase (se 5 (by rfl) ⟨46943, by rfl⟩ : syracuseStep 1001461 = 93887) (by norm_num)
theorem B2541557 : Blo 888571 2541557 := bbase (se 5 (by rfl) ⟨119135, by rfl⟩ : syracuseStep 2541557 = 238271) (by norm_num)
theorem B1001497 : Blo 888571 1001497 := bbase (se 2 (by rfl) ⟨375561, by rfl⟩ : syracuseStep 1001497 = 751123) (by norm_num)
theorem B1001533 : Blo 888571 1001533 := bbase (se 3 (by rfl) ⟨187787, by rfl⟩ : syracuseStep 1001533 = 375575) (by norm_num)
theorem B1001569 : Blo 888571 1001569 := bbase (se 2 (by rfl) ⟨375588, by rfl⟩ : syracuseStep 1001569 = 751177) (by norm_num)
theorem B1001605 : Blo 888571 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B1001641 : Blo 888571 1001641 := bbase (se 2 (by rfl) ⟨375615, by rfl⟩ : syracuseStep 1001641 = 751231) (by norm_num)
theorem B1001677 : Blo 888571 1001677 := bbase (se 3 (by rfl) ⟨187814, by rfl⟩ : syracuseStep 1001677 = 375629) (by norm_num)
theorem B1001713 : Blo 888571 1001713 := bbase (se 2 (by rfl) ⟨375642, by rfl⟩ : syracuseStep 1001713 = 751285) (by norm_num)
theorem B8669429 : Blo 888571 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B1001749 : Blo 888571 1001749 := bbase (se 6 (by rfl) ⟨23478, by rfl⟩ : syracuseStep 1001749 = 46957) (by norm_num)
theorem B1001785 : Blo 888571 1001785 := bbase (se 2 (by rfl) ⟨375669, by rfl⟩ : syracuseStep 1001785 = 751339) (by norm_num)
theorem B4507973 : Blo 888571 4507973 := bbase (se 4 (by rfl) ⟨422622, by rfl⟩ : syracuseStep 4507973 = 845245) (by norm_num)
theorem B1001821 : Blo 888571 1001821 := bbase (se 3 (by rfl) ⟨187841, by rfl⟩ : syracuseStep 1001821 = 375683) (by norm_num)
theorem B1001857 : Blo 888571 1001857 := bbase (se 2 (by rfl) ⟨375696, by rfl⟩ : syracuseStep 1001857 = 751393) (by norm_num)
theorem B1689997 : Blo 888571 1689997 := bbase (se 3 (by rfl) ⟨316874, by rfl⟩ : syracuseStep 1689997 = 633749) (by norm_num)
theorem B3000725 : Blo 888571 3000725 := bbase (se 6 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 3000725 = 140659) (by norm_num)
theorem B1001893 : Blo 888571 1001893 := bbase (se 4 (by rfl) ⟨93927, by rfl⟩ : syracuseStep 1001893 = 187855) (by norm_num)
theorem B1001929 : Blo 888571 1001929 := bbase (se 2 (by rfl) ⟨375723, by rfl⟩ : syracuseStep 1001929 = 751447) (by norm_num)
theorem B1001965 : Blo 888571 1001965 := bbase (se 3 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 1001965 = 375737) (by norm_num)
theorem B1002001 : Blo 888571 1002001 := bbase (se 2 (by rfl) ⟨375750, by rfl⟩ : syracuseStep 1002001 = 751501) (by norm_num)
theorem B1690141 : Blo 888571 1690141 := bbase (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) (by norm_num)
theorem B1428005 : Blo 888571 1428005 := bbase (se 4 (by rfl) ⟨133875, by rfl⟩ : syracuseStep 1428005 = 267751) (by norm_num)
theorem B1002037 : Blo 888571 1002037 := bbase (se 5 (by rfl) ⟨46970, by rfl⟩ : syracuseStep 1002037 = 93941) (by norm_num)
theorem B1002073 : Blo 888571 1002073 := bbase (se 2 (by rfl) ⟨375777, by rfl⟩ : syracuseStep 1002073 = 751555) (by norm_num)
theorem B1002109 : Blo 888571 1002109 := bbase (se 3 (by rfl) ⟨187895, by rfl⟩ : syracuseStep 1002109 = 375791) (by norm_num)
theorem B1002145 : Blo 888571 1002145 := bbase (se 2 (by rfl) ⟨375804, by rfl⟩ : syracuseStep 1002145 = 751609) (by norm_num)
theorem B1690301 : Blo 888571 1690301 := bbase (se 3 (by rfl) ⟨316931, by rfl⟩ : syracuseStep 1690301 = 633863) (by norm_num)
theorem B1002181 : Blo 888571 1002181 := bbase (se 4 (by rfl) ⟨93954, by rfl⟩ : syracuseStep 1002181 = 187909) (by norm_num)
theorem B1002217 : Blo 888571 1002217 := bbase (se 2 (by rfl) ⟨375831, by rfl⟩ : syracuseStep 1002217 = 751663) (by norm_num)
theorem B1002253 : Blo 888571 1002253 := bbase (se 3 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 1002253 = 375845) (by norm_num)
theorem B1002289 : Blo 888571 1002289 := bbase (se 2 (by rfl) ⟨375858, by rfl⟩ : syracuseStep 1002289 = 751717) (by norm_num)
theorem B1067837 : Blo 888571 1067837 := bbase (se 3 (by rfl) ⟨200219, by rfl⟩ : syracuseStep 1067837 = 400439) (by norm_num)
theorem B3001157 : Blo 888571 3001157 := bbase (se 4 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 3001157 = 562717) (by norm_num)
theorem B1690445 : Blo 888571 1690445 := bbase (se 3 (by rfl) ⟨316958, by rfl⟩ : syracuseStep 1690445 = 633917) (by norm_num)
theorem B1067861 : Blo 888571 1067861 := bbase (se 9 (by rfl) ⟨3128, by rfl⟩ : syracuseStep 1067861 = 6257) (by norm_num)
theorem B1002325 : Blo 888571 1002325 := bbase (se 9 (by rfl) ⟨2936, by rfl⟩ : syracuseStep 1002325 = 5873) (by norm_num)
theorem B6769493 : Blo 888571 6769493 := bbase (se 9 (by rfl) ⟨19832, by rfl⟩ : syracuseStep 6769493 = 39665) (by norm_num)
theorem B1002361 : Blo 888571 1002361 := bbase (se 2 (by rfl) ⟨375885, by rfl⟩ : syracuseStep 1002361 = 751771) (by norm_num)
theorem B1002397 : Blo 888571 1002397 := bbase (se 3 (by rfl) ⟨187949, by rfl⟩ : syracuseStep 1002397 = 375899) (by norm_num)
theorem B1002433 : Blo 888571 1002433 := bbase (se 2 (by rfl) ⟨375912, by rfl⟩ : syracuseStep 1002433 = 751825) (by norm_num)
theorem B5065685 : Blo 888571 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B1002469 : Blo 888571 1002469 := bbase (se 4 (by rfl) ⟨93981, by rfl⟩ : syracuseStep 1002469 = 187963) (by norm_num)
theorem B1002505 : Blo 888571 1002505 := bbase (se 2 (by rfl) ⟨375939, by rfl⟩ : syracuseStep 1002505 = 751879) (by norm_num)
theorem B1002541 : Blo 888571 1002541 := bbase (se 3 (by rfl) ⟨187976, by rfl⟩ : syracuseStep 1002541 = 375953) (by norm_num)
theorem B1002577 : Blo 888571 1002577 := bbase (se 2 (by rfl) ⟨375966, by rfl⟩ : syracuseStep 1002577 = 751933) (by norm_num)
theorem B1690733 : Blo 888571 1690733 := bbase (se 3 (by rfl) ⟨317012, by rfl⟩ : syracuseStep 1690733 = 634025) (by norm_num)
theorem B1002613 : Blo 888571 1002613 := bbase (se 5 (by rfl) ⟨46997, by rfl⟩ : syracuseStep 1002613 = 93995) (by norm_num)
theorem B1068169 : Blo 888571 1068169 := bbase (se 2 (by rfl) ⟨400563, by rfl⟩ : syracuseStep 1068169 = 801127) (by norm_num)
theorem B1002649 : Blo 888571 1002649 := bbase (se 2 (by rfl) ⟨375993, by rfl⟩ : syracuseStep 1002649 = 751987) (by norm_num)
theorem B1428653 : Blo 888571 1428653 := bbase (se 3 (by rfl) ⟨267872, by rfl⟩ : syracuseStep 1428653 = 535745) (by norm_num)
theorem B1002685 : Blo 888571 1002685 := bbase (se 3 (by rfl) ⟨188003, by rfl⟩ : syracuseStep 1002685 = 376007) (by norm_num)
theorem B1002721 : Blo 888571 1002721 := bbase (se 2 (by rfl) ⟨376020, by rfl⟩ : syracuseStep 1002721 = 752041) (by norm_num)
theorem B3001589 : Blo 888571 3001589 := bbase (se 5 (by rfl) ⟨140699, by rfl⟩ : syracuseStep 3001589 = 281399) (by norm_num)
theorem B1690885 : Blo 888571 1690885 := bbase (se 4 (by rfl) ⟨158520, by rfl⟩ : syracuseStep 1690885 = 317041) (by norm_num)
theorem B1002757 : Blo 888571 1002757 := bbase (se 4 (by rfl) ⟨94008, by rfl⟩ : syracuseStep 1002757 = 188017) (by norm_num)
theorem B1101089 : Blo 888571 1101089 := bbase (se 2 (by rfl) ⟨412908, by rfl⟩ : syracuseStep 1101089 = 825817) (by norm_num)
theorem B1002793 : Blo 888571 1002793 := bbase (se 2 (by rfl) ⟨376047, by rfl⟩ : syracuseStep 1002793 = 752095) (by norm_num)
theorem B1068341 : Blo 888571 1068341 := bbase (se 5 (by rfl) ⟨50078, by rfl⟩ : syracuseStep 1068341 = 100157) (by norm_num)
theorem B1002829 : Blo 888571 1002829 := bbase (se 3 (by rfl) ⟨188030, by rfl⟩ : syracuseStep 1002829 = 376061) (by norm_num)
theorem B1625429 : Blo 888571 1625429 := bbase (se 11 (by rfl) ⟨1190, by rfl⟩ : syracuseStep 1625429 = 2381) (by norm_num)
theorem B1002865 : Blo 888571 1002865 := bbase (se 2 (by rfl) ⟨376074, by rfl⟩ : syracuseStep 1002865 = 752149) (by norm_num)
theorem B10833301 : Blo 888571 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B1002901 : Blo 888571 1002901 := bbase (se 6 (by rfl) ⟨23505, by rfl⟩ : syracuseStep 1002901 = 47011) (by norm_num)
theorem B1068457 : Blo 888571 1068457 := bbase (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) (by norm_num)
theorem B1002937 : Blo 888571 1002937 := bbase (se 2 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 1002937 = 752203) (by norm_num)
theorem B1002973 : Blo 888571 1002973 := bbase (se 3 (by rfl) ⟨188057, by rfl⟩ : syracuseStep 1002973 = 376115) (by norm_num)
theorem B1003009 : Blo 888571 1003009 := bbase (se 2 (by rfl) ⟨376128, by rfl⟩ : syracuseStep 1003009 = 752257) (by norm_num)
theorem B1068553 : Blo 888571 1068553 := bbase (se 2 (by rfl) ⟨400707, by rfl⟩ : syracuseStep 1068553 = 801415) (by norm_num)
theorem B1003045 : Blo 888571 1003045 := bbase (se 4 (by rfl) ⟨94035, by rfl⟩ : syracuseStep 1003045 = 188071) (by norm_num)
theorem B1691189 : Blo 888571 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B1003081 : Blo 888571 1003081 := bbase (se 2 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 1003081 = 752311) (by norm_num)
theorem B4509269 : Blo 888571 4509269 := bbase (se 8 (by rfl) ⟨26421, by rfl⟩ : syracuseStep 4509269 = 52843) (by norm_num)
theorem B1003117 : Blo 888571 1003117 := bbase (se 3 (by rfl) ⟨188084, by rfl⟩ : syracuseStep 1003117 = 376169) (by norm_num)
theorem B1003153 : Blo 888571 1003153 := bbase (se 2 (by rfl) ⟨376182, by rfl⟩ : syracuseStep 1003153 = 752365) (by norm_num)
theorem B1068697 : Blo 888571 1068697 := bbase (se 2 (by rfl) ⟨400761, by rfl⟩ : syracuseStep 1068697 = 801523) (by norm_num)
theorem B3002021 : Blo 888571 3002021 := bbase (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) (by norm_num)
theorem B1101485 : Blo 888571 1101485 := bbase (se 3 (by rfl) ⟨206528, by rfl⟩ : syracuseStep 1101485 = 413057) (by norm_num)
theorem B1003189 : Blo 888571 1003189 := bbase (se 5 (by rfl) ⟨47024, by rfl⟩ : syracuseStep 1003189 = 94049) (by norm_num)
theorem B1003225 : Blo 888571 1003225 := bbase (se 2 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 1003225 = 752419) (by norm_num)
theorem B1003261 : Blo 888571 1003261 := bbase (se 3 (by rfl) ⟨188111, by rfl⟩ : syracuseStep 1003261 = 376223) (by norm_num)
theorem B14634773 : Blo 888571 14634773 := bbase (se 6 (by rfl) ⟨343002, by rfl⟩ : syracuseStep 14634773 = 686005) (by norm_num)
theorem B12865301 : Blo 888571 12865301 := bbase (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) (by norm_num)
theorem B1003297 : Blo 888571 1003297 := bbase (se 2 (by rfl) ⟨376236, by rfl⟩ : syracuseStep 1003297 = 752473) (by norm_num)
theorem B2608949 : Blo 888571 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B1003333 : Blo 888571 1003333 := bbase (se 4 (by rfl) ⟨94062, by rfl⟩ : syracuseStep 1003333 = 188125) (by norm_num)
theorem B1003369 : Blo 888571 1003369 := bbase (se 2 (by rfl) ⟨376263, by rfl⟩ : syracuseStep 1003369 = 752527) (by norm_num)
theorem B1003405 : Blo 888571 1003405 := bbase (se 3 (by rfl) ⟨188138, by rfl⟩ : syracuseStep 1003405 = 376277) (by norm_num)
theorem B1003441 : Blo 888571 1003441 := bbase (se 2 (by rfl) ⟨376290, by rfl⟩ : syracuseStep 1003441 = 752581) (by norm_num)
theorem B1003477 : Blo 888571 1003477 := bbase (se 7 (by rfl) ⟨11759, by rfl⟩ : syracuseStep 1003477 = 23519) (by norm_num)
theorem B1003513 : Blo 888571 1003513 := bbase (se 2 (by rfl) ⟨376317, by rfl⟩ : syracuseStep 1003513 = 752635) (by norm_num)
theorem B8572949 : Blo 888571 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B1003549 : Blo 888571 1003549 := bbase (se 3 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 1003549 = 376331) (by norm_num)
theorem B1003585 : Blo 888571 1003585 := bbase (se 2 (by rfl) ⟨376344, by rfl⟩ : syracuseStep 1003585 = 752689) (by norm_num)
theorem B3002453 : Blo 888571 3002453 := bbase (se 8 (by rfl) ⟨17592, by rfl⟩ : syracuseStep 3002453 = 35185) (by norm_num)
theorem B7721045 : Blo 888571 7721045 := bbase (se 8 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 7721045 = 90481) (by norm_num)
theorem B1003621 : Blo 888571 1003621 := bbase (se 4 (by rfl) ⟨94089, by rfl⟩ : syracuseStep 1003621 = 188179) (by norm_num)
theorem B1003657 : Blo 888571 1003657 := bbase (se 2 (by rfl) ⟨376371, by rfl⟩ : syracuseStep 1003657 = 752743) (by norm_num)
theorem B1429645 : Blo 888571 1429645 := bbase (se 3 (by rfl) ⟨268058, by rfl⟩ : syracuseStep 1429645 = 536117) (by norm_num)
theorem B2281621 : Blo 888571 2281621 := bbase (se 6 (by rfl) ⟨53475, by rfl⟩ : syracuseStep 2281621 = 106951) (by norm_num)
theorem B1003693 : Blo 888571 1003693 := bbase (se 3 (by rfl) ⟨188192, by rfl⟩ : syracuseStep 1003693 = 376385) (by norm_num)
theorem B1003729 : Blo 888571 1003729 := bbase (se 2 (by rfl) ⟨376398, by rfl⟩ : syracuseStep 1003729 = 752797) (by norm_num)
theorem B1003765 : Blo 888571 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B1003801 : Blo 888571 1003801 := bbase (se 2 (by rfl) ⟨376425, by rfl⟩ : syracuseStep 1003801 = 752851) (by norm_num)
theorem B1691941 : Blo 888571 1691941 := bbase (se 4 (by rfl) ⟨158619, by rfl⟩ : syracuseStep 1691941 = 317239) (by norm_num)
theorem B1003837 : Blo 888571 1003837 := bbase (se 3 (by rfl) ⟨188219, by rfl⟩ : syracuseStep 1003837 = 376439) (by norm_num)
theorem B1003873 : Blo 888571 1003873 := bbase (se 2 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 1003873 = 752905) (by norm_num)
theorem B1003909 : Blo 888571 1003909 := bbase (se 4 (by rfl) ⟨94116, by rfl⟩ : syracuseStep 1003909 = 188233) (by norm_num)
theorem B1003945 : Blo 888571 1003945 := bbase (se 2 (by rfl) ⟨376479, by rfl⟩ : syracuseStep 1003945 = 752959) (by norm_num)
theorem B1692085 : Blo 888571 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B1003981 : Blo 888571 1003981 := bbase (se 3 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 1003981 = 376493) (by norm_num)
theorem B1004017 : Blo 888571 1004017 := bbase (se 2 (by rfl) ⟨376506, by rfl⟩ : syracuseStep 1004017 = 753013) (by norm_num)
theorem B3002885 : Blo 888571 3002885 := bbase (se 4 (by rfl) ⟨281520, by rfl⟩ : syracuseStep 3002885 = 563041) (by norm_num)
theorem B1004053 : Blo 888571 1004053 := bbase (se 6 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 1004053 = 47065) (by norm_num)
theorem B1266205 : Blo 888571 1266205 := bbase (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) (by norm_num)
theorem B1004089 : Blo 888571 1004089 := bbase (se 2 (by rfl) ⟨376533, by rfl⟩ : syracuseStep 1004089 = 753067) (by norm_num)
theorem B1462853 : Blo 888571 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B1692245 : Blo 888571 1692245 := bbase (se 8 (by rfl) ⟨9915, by rfl⟩ : syracuseStep 1692245 = 19831) (by norm_num)
theorem B11424341 : Blo 888571 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B2249309 : Blo 888571 2249309 := bbase (se 3 (by rfl) ⟨421745, by rfl⟩ : syracuseStep 2249309 = 843491) (by norm_num)
theorem B1004125 : Blo 888571 1004125 := bbase (se 3 (by rfl) ⟨188273, by rfl⟩ : syracuseStep 1004125 = 376547) (by norm_num)
theorem B6509173 : Blo 888571 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B1692389 : Blo 888571 1692389 := bbase (se 4 (by rfl) ⟨158661, by rfl⟩ : syracuseStep 1692389 = 317323) (by norm_num)
theorem B4510565 : Blo 888571 4510565 := bbase (se 4 (by rfl) ⟨422865, by rfl⟩ : syracuseStep 4510565 = 845731) (by norm_num)
theorem B2249653 : Blo 888571 2249653 := bbase (se 5 (by rfl) ⟨105452, by rfl⟩ : syracuseStep 2249653 = 210905) (by norm_num)
theorem B3003317 : Blo 888571 3003317 := bbase (se 5 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 3003317 = 281561) (by norm_num)
theorem B1463269 : Blo 888571 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B1692677 : Blo 888571 1692677 := bbase (se 4 (by rfl) ⟨158688, by rfl⟩ : syracuseStep 1692677 = 317377) (by norm_num)
theorem B2249765 : Blo 888571 2249765 := bbase (se 4 (by rfl) ⟨210915, by rfl⟩ : syracuseStep 2249765 = 421831) (by norm_num)
theorem B2282597 : Blo 888571 2282597 := bbase (se 4 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 2282597 = 427987) (by norm_num)
theorem B1266797 : Blo 888571 1266797 := bbase (se 3 (by rfl) ⟨237524, by rfl⟩ : syracuseStep 1266797 = 475049) (by norm_num)
theorem B1692829 : Blo 888571 1692829 := bbase (se 3 (by rfl) ⟨317405, by rfl⟩ : syracuseStep 1692829 = 634811) (by norm_num)
theorem B1266877 : Blo 888571 1266877 := bbase (se 3 (by rfl) ⟨237539, by rfl⟩ : syracuseStep 1266877 = 475079) (by norm_num)
theorem B2249957 : Blo 888571 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B3855637 : Blo 888571 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B1266997 : Blo 888571 1266997 := bbase (se 5 (by rfl) ⟨59390, by rfl⟩ : syracuseStep 1266997 = 118781) (by norm_num)
theorem B1070417 : Blo 888571 1070417 := bbase (se 2 (by rfl) ⟨401406, by rfl⟩ : syracuseStep 1070417 = 802813) (by norm_num)
theorem B3003749 : Blo 888571 3003749 := bbase (se 4 (by rfl) ⟨281601, by rfl⟩ : syracuseStep 3003749 = 563203) (by norm_num)
theorem B1267093 : Blo 888571 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B1070533 : Blo 888571 1070533 := bbase (se 4 (by rfl) ⟨100362, by rfl⟩ : syracuseStep 1070533 = 200725) (by norm_num)
theorem B1693133 : Blo 888571 1693133 := bbase (se 3 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 1693133 = 634925) (by norm_num)
theorem B1070605 : Blo 888571 1070605 := bbase (se 3 (by rfl) ⟨200738, by rfl⟩ : syracuseStep 1070605 = 401477) (by norm_num)
theorem B2250301 : Blo 888571 2250301 := bbase (se 3 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 2250301 = 843863) (by norm_num)
theorem B1332869 : Blo 888571 1332869 := bbase (se 4 (by rfl) ⟨124956, by rfl⟩ : syracuseStep 1332869 = 249913) (by norm_num)
theorem B1070725 : Blo 888571 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B1332893 : Blo 888571 1332893 := bbase (se 3 (by rfl) ⟨249917, by rfl⟩ : syracuseStep 1332893 = 499835) (by norm_num)
theorem B2250413 : Blo 888571 2250413 := bbase (se 3 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 2250413 = 843905) (by norm_num)
theorem B1332917 : Blo 888571 1332917 := bbase (se 5 (by rfl) ⟨62480, by rfl⟩ : syracuseStep 1332917 = 124961) (by norm_num)
theorem B1332941 : Blo 888571 1332941 := bbase (se 3 (by rfl) ⟨249926, by rfl⟩ : syracuseStep 1332941 = 499853) (by norm_num)
theorem B1332965 : Blo 888571 1332965 := bbase (se 4 (by rfl) ⟨124965, by rfl⟩ : syracuseStep 1332965 = 249931) (by norm_num)
theorem B1332989 : Blo 888571 1332989 := bbase (se 3 (by rfl) ⟨249935, by rfl⟩ : syracuseStep 1332989 = 499871) (by norm_num)
theorem B1333013 : Blo 888571 1333013 := bbase (se 6 (by rfl) ⟨31242, by rfl⟩ : syracuseStep 1333013 = 62485) (by norm_num)
theorem B3004181 : Blo 888571 3004181 := bbase (se 6 (by rfl) ⟨70410, by rfl⟩ : syracuseStep 3004181 = 140821) (by norm_num)
theorem B1333037 : Blo 888571 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B2709301 : Blo 888571 2709301 := bbase (se 5 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 2709301 = 253997) (by norm_num)
theorem B1333061 : Blo 888571 1333061 := bbase (se 4 (by rfl) ⟨124974, by rfl⟩ : syracuseStep 1333061 = 249949) (by norm_num)
theorem B1333085 : Blo 888571 1333085 := bbase (se 3 (by rfl) ⟨249953, by rfl⟩ : syracuseStep 1333085 = 499907) (by norm_num)
theorem B2250605 : Blo 888571 2250605 := bbase (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) (by norm_num)
theorem B1333109 : Blo 888571 1333109 := bbase (se 5 (by rfl) ⟨62489, by rfl⟩ : syracuseStep 1333109 = 124979) (by norm_num)
theorem B1267589 : Blo 888571 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B1333133 : Blo 888571 1333133 := bbase (se 3 (by rfl) ⟨249962, by rfl⟩ : syracuseStep 1333133 = 499925) (by norm_num)
theorem B1333157 : Blo 888571 1333157 := bbase (se 4 (by rfl) ⟨124983, by rfl⟩ : syracuseStep 1333157 = 249967) (by norm_num)
theorem B1333181 : Blo 888571 1333181 := bbase (se 3 (by rfl) ⟨249971, by rfl⟩ : syracuseStep 1333181 = 499943) (by norm_num)
theorem B1333205 : Blo 888571 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B1333229 : Blo 888571 1333229 := bbase (se 3 (by rfl) ⟨249980, by rfl⟩ : syracuseStep 1333229 = 499961) (by norm_num)
theorem B2316269 : Blo 888571 2316269 := bbase (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) (by norm_num)
theorem B1333253 : Blo 888571 1333253 := bbase (se 4 (by rfl) ⟨124992, by rfl⟩ : syracuseStep 1333253 = 249985) (by norm_num)
theorem B1071109 : Blo 888571 1071109 := bbase (se 4 (by rfl) ⟨100416, by rfl⟩ : syracuseStep 1071109 = 200833) (by norm_num)
theorem B1333277 : Blo 888571 1333277 := bbase (se 3 (by rfl) ⟨249989, by rfl⟩ : syracuseStep 1333277 = 499979) (by norm_num)
theorem B1333301 : Blo 888571 1333301 := bbase (se 5 (by rfl) ⟨62498, by rfl⟩ : syracuseStep 1333301 = 124997) (by norm_num)
theorem B1333325 : Blo 888571 1333325 := bbase (se 3 (by rfl) ⟨249998, by rfl⟩ : syracuseStep 1333325 = 499997) (by norm_num)
theorem B1333349 : Blo 888571 1333349 := bbase (se 4 (by rfl) ⟨125001, by rfl⟩ : syracuseStep 1333349 = 250003) (by norm_num)
theorem B4511861 : Blo 888571 4511861 := bbase (se 5 (by rfl) ⟨211493, by rfl⟩ : syracuseStep 4511861 = 422987) (by norm_num)
theorem B1333373 : Blo 888571 1333373 := bbase (se 3 (by rfl) ⟨250007, by rfl⟩ : syracuseStep 1333373 = 500015) (by norm_num)
theorem B1333397 : Blo 888571 1333397 := bbase (se 6 (by rfl) ⟨31251, by rfl⟩ : syracuseStep 1333397 = 62503) (by norm_num)
theorem B1333421 : Blo 888571 1333421 := bbase (se 3 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 1333421 = 500033) (by norm_num)
theorem B1693885 : Blo 888571 1693885 := bbase (se 3 (by rfl) ⟨317603, by rfl⟩ : syracuseStep 1693885 = 635207) (by norm_num)
theorem B1333445 : Blo 888571 1333445 := bbase (se 4 (by rfl) ⟨125010, by rfl⟩ : syracuseStep 1333445 = 250021) (by norm_num)
theorem B2250949 : Blo 888571 2250949 := bbase (se 4 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 2250949 = 422053) (by norm_num)
theorem B3004613 : Blo 888571 3004613 := bbase (se 4 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 3004613 = 563365) (by norm_num)
theorem B1333469 : Blo 888571 1333469 := bbase (se 3 (by rfl) ⟨250025, by rfl⟩ : syracuseStep 1333469 = 500051) (by norm_num)
theorem B1333493 : Blo 888571 1333493 := bbase (se 5 (by rfl) ⟨62507, by rfl⟩ : syracuseStep 1333493 = 125015) (by norm_num)
theorem B1333517 : Blo 888571 1333517 := bbase (se 3 (by rfl) ⟨250034, by rfl⟩ : syracuseStep 1333517 = 500069) (by norm_num)
theorem B1333541 : Blo 888571 1333541 := bbase (se 4 (by rfl) ⟨125019, by rfl⟩ : syracuseStep 1333541 = 250039) (by norm_num)
theorem B2251061 : Blo 888571 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B1333565 : Blo 888571 1333565 := bbase (se 3 (by rfl) ⟨250043, by rfl⟩ : syracuseStep 1333565 = 500087) (by norm_num)
theorem B1694029 : Blo 888571 1694029 := bbase (se 3 (by rfl) ⟨317630, by rfl⟩ : syracuseStep 1694029 = 635261) (by norm_num)
theorem B1333589 : Blo 888571 1333589 := bbase (se 10 (by rfl) ⟨1953, by rfl⟩ : syracuseStep 1333589 = 3907) (by norm_num)
theorem B1333613 : Blo 888571 1333613 := bbase (se 3 (by rfl) ⟨250052, by rfl⟩ : syracuseStep 1333613 = 500105) (by norm_num)
theorem B1333637 : Blo 888571 1333637 := bbase (se 4 (by rfl) ⟨125028, by rfl⟩ : syracuseStep 1333637 = 250057) (by norm_num)
theorem B1333661 : Blo 888571 1333661 := bbase (se 3 (by rfl) ⟨250061, by rfl⟩ : syracuseStep 1333661 = 500123) (by norm_num)
theorem B1268141 : Blo 888571 1268141 := bbase (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) (by norm_num)
theorem B1333685 : Blo 888571 1333685 := bbase (se 5 (by rfl) ⟨62516, by rfl⟩ : syracuseStep 1333685 = 125033) (by norm_num)
theorem B1333709 : Blo 888571 1333709 := bbase (se 3 (by rfl) ⟨250070, by rfl⟩ : syracuseStep 1333709 = 500141) (by norm_num)
theorem B1333733 : Blo 888571 1333733 := bbase (se 4 (by rfl) ⟨125037, by rfl⟩ : syracuseStep 1333733 = 250075) (by norm_num)
theorem B1694189 : Blo 888571 1694189 := bbase (se 3 (by rfl) ⟨317660, by rfl⟩ : syracuseStep 1694189 = 635321) (by norm_num)
theorem B2251253 : Blo 888571 2251253 := bbase (se 5 (by rfl) ⟨105527, by rfl⟩ : syracuseStep 2251253 = 211055) (by norm_num)
theorem B1333757 : Blo 888571 1333757 := bbase (se 3 (by rfl) ⟨250079, by rfl⟩ : syracuseStep 1333757 = 500159) (by norm_num)
theorem B1333781 : Blo 888571 1333781 := bbase (se 6 (by rfl) ⟨31260, by rfl⟩ : syracuseStep 1333781 = 62521) (by norm_num)
theorem B1333805 : Blo 888571 1333805 := bbase (se 3 (by rfl) ⟨250088, by rfl⟩ : syracuseStep 1333805 = 500177) (by norm_num)
theorem B1333829 : Blo 888571 1333829 := bbase (se 4 (by rfl) ⟨125046, by rfl⟩ : syracuseStep 1333829 = 250093) (by norm_num)
theorem B1333853 : Blo 888571 1333853 := bbase (se 3 (by rfl) ⟨250097, by rfl⟩ : syracuseStep 1333853 = 500195) (by norm_num)
theorem B1333877 : Blo 888571 1333877 := bbase (se 5 (by rfl) ⟨62525, by rfl⟩ : syracuseStep 1333877 = 125051) (by norm_num)
theorem B3005045 : Blo 888571 3005045 := bbase (se 5 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 3005045 = 281723) (by norm_num)
theorem B1694333 : Blo 888571 1694333 := bbase (se 3 (by rfl) ⟨317687, by rfl⟩ : syracuseStep 1694333 = 635375) (by norm_num)
theorem B1333901 : Blo 888571 1333901 := bbase (se 3 (by rfl) ⟨250106, by rfl⟩ : syracuseStep 1333901 = 500213) (by norm_num)
theorem B1333925 : Blo 888571 1333925 := bbase (se 4 (by rfl) ⟨125055, by rfl⟩ : syracuseStep 1333925 = 250111) (by norm_num)
theorem B1071797 : Blo 888571 1071797 := bbase (se 5 (by rfl) ⟨50240, by rfl⟩ : syracuseStep 1071797 = 100481) (by norm_num)
theorem B1333949 : Blo 888571 1333949 := bbase (se 3 (by rfl) ⟨250115, by rfl⟩ : syracuseStep 1333949 = 500231) (by norm_num)
theorem B1333973 : Blo 888571 1333973 := bbase (se 7 (by rfl) ⟨15632, by rfl⟩ : syracuseStep 1333973 = 31265) (by norm_num)
theorem B1333997 : Blo 888571 1333997 := bbase (se 3 (by rfl) ⟨250124, by rfl⟩ : syracuseStep 1333997 = 500249) (by norm_num)
theorem B1334021 : Blo 888571 1334021 := bbase (se 4 (by rfl) ⟨125064, by rfl⟩ : syracuseStep 1334021 = 250129) (by norm_num)
theorem B1334045 : Blo 888571 1334045 := bbase (se 3 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 1334045 = 500267) (by norm_num)
theorem B1334069 : Blo 888571 1334069 := bbase (se 5 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 1334069 = 125069) (by norm_num)
theorem B1334093 : Blo 888571 1334093 := bbase (se 3 (by rfl) ⟨250142, by rfl⟩ : syracuseStep 1334093 = 500285) (by norm_num)
theorem B2251597 : Blo 888571 2251597 := bbase (se 3 (by rfl) ⟨422174, by rfl⟩ : syracuseStep 2251597 = 844349) (by norm_num)
theorem B1334117 : Blo 888571 1334117 := bbase (se 4 (by rfl) ⟨125073, by rfl⟩ : syracuseStep 1334117 = 250147) (by norm_num)
theorem B3431285 : Blo 888571 3431285 := bbase (se 5 (by rfl) ⟨160841, by rfl⟩ : syracuseStep 3431285 = 321683) (by norm_num)
theorem B1334141 : Blo 888571 1334141 := bbase (se 3 (by rfl) ⟨250151, by rfl⟩ : syracuseStep 1334141 = 500303) (by norm_num)
theorem B1334165 : Blo 888571 1334165 := bbase (se 6 (by rfl) ⟨31269, by rfl⟩ : syracuseStep 1334165 = 62539) (by norm_num)
theorem B1334189 : Blo 888571 1334189 := bbase (se 3 (by rfl) ⟨250160, by rfl⟩ : syracuseStep 1334189 = 500321) (by norm_num)
theorem B2251709 : Blo 888571 2251709 := bbase (se 3 (by rfl) ⟨422195, by rfl⟩ : syracuseStep 2251709 = 844391) (by norm_num)
theorem B1334213 : Blo 888571 1334213 := bbase (se 4 (by rfl) ⟨125082, by rfl⟩ : syracuseStep 1334213 = 250165) (by norm_num)
theorem B1334237 : Blo 888571 1334237 := bbase (se 3 (by rfl) ⟨250169, by rfl⟩ : syracuseStep 1334237 = 500339) (by norm_num)
theorem B1334261 : Blo 888571 1334261 := bbase (se 5 (by rfl) ⟨62543, by rfl⟩ : syracuseStep 1334261 = 125087) (by norm_num)
theorem B1334285 : Blo 888571 1334285 := bbase (se 3 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 1334285 = 500357) (by norm_num)
theorem B1334309 : Blo 888571 1334309 := bbase (se 4 (by rfl) ⟨125091, by rfl⟩ : syracuseStep 1334309 = 250183) (by norm_num)
theorem B3005477 : Blo 888571 3005477 := bbase (se 4 (by rfl) ⟨281763, by rfl⟩ : syracuseStep 3005477 = 563527) (by norm_num)
theorem B2710565 : Blo 888571 2710565 := bbase (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) (by norm_num)
theorem B1334333 : Blo 888571 1334333 := bbase (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) (by norm_num)
theorem B1334357 : Blo 888571 1334357 := bbase (se 8 (by rfl) ⟨7818, by rfl⟩ : syracuseStep 1334357 = 15637) (by norm_num)
theorem B1236061 : Blo 888571 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B1334381 : Blo 888571 1334381 := bbase (se 3 (by rfl) ⟨250196, by rfl⟩ : syracuseStep 1334381 = 500393) (by norm_num)
theorem B2251901 : Blo 888571 2251901 := bbase (se 3 (by rfl) ⟨422231, by rfl⟩ : syracuseStep 2251901 = 844463) (by norm_num)
theorem B1334405 : Blo 888571 1334405 := bbase (se 4 (by rfl) ⟨125100, by rfl⟩ : syracuseStep 1334405 = 250201) (by norm_num)
theorem B1334429 : Blo 888571 1334429 := bbase (se 3 (by rfl) ⟨250205, by rfl⟩ : syracuseStep 1334429 = 500411) (by norm_num)
theorem B1268893 : Blo 888571 1268893 := bbase (se 3 (by rfl) ⟨237917, by rfl⟩ : syracuseStep 1268893 = 475835) (by norm_num)
theorem B1334453 : Blo 888571 1334453 := bbase (se 5 (by rfl) ⟨62552, by rfl⟩ : syracuseStep 1334453 = 125105) (by norm_num)
theorem B1334477 : Blo 888571 1334477 := bbase (se 3 (by rfl) ⟨250214, by rfl⟩ : syracuseStep 1334477 = 500429) (by norm_num)
theorem B1334501 : Blo 888571 1334501 := bbase (se 4 (by rfl) ⟨125109, by rfl⟩ : syracuseStep 1334501 = 250219) (by norm_num)
theorem B1334525 : Blo 888571 1334525 := bbase (se 3 (by rfl) ⟨250223, by rfl⟩ : syracuseStep 1334525 = 500447) (by norm_num)
theorem B1334549 : Blo 888571 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B1334573 : Blo 888571 1334573 := bbase (se 3 (by rfl) ⟨250232, by rfl⟩ : syracuseStep 1334573 = 500465) (by norm_num)
theorem B1334597 : Blo 888571 1334597 := bbase (se 4 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 1334597 = 250237) (by norm_num)
theorem B1334621 : Blo 888571 1334621 := bbase (se 3 (by rfl) ⟨250241, by rfl⟩ : syracuseStep 1334621 = 500483) (by norm_num)
theorem B1334645 : Blo 888571 1334645 := bbase (se 5 (by rfl) ⟨62561, by rfl⟩ : syracuseStep 1334645 = 125123) (by norm_num)
theorem B4513157 : Blo 888571 4513157 := bbase (se 4 (by rfl) ⟨423108, by rfl⟩ : syracuseStep 4513157 = 846217) (by norm_num)
theorem B1334669 : Blo 888571 1334669 := bbase (se 3 (by rfl) ⟨250250, by rfl⟩ : syracuseStep 1334669 = 500501) (by norm_num)
theorem B1334693 : Blo 888571 1334693 := bbase (se 4 (by rfl) ⟨125127, by rfl⟩ : syracuseStep 1334693 = 250255) (by norm_num)
theorem B1334717 : Blo 888571 1334717 := bbase (se 3 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 1334717 = 500519) (by norm_num)
theorem B2252245 : Blo 888571 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B1334741 : Blo 888571 1334741 := bbase (se 7 (by rfl) ⟨15641, by rfl⟩ : syracuseStep 1334741 = 31283) (by norm_num)
theorem B3005909 : Blo 888571 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B1334765 : Blo 888571 1334765 := bbase (se 3 (by rfl) ⟨250268, by rfl⟩ : syracuseStep 1334765 = 500537) (by norm_num)
theorem B1334789 : Blo 888571 1334789 := bbase (se 4 (by rfl) ⟨125136, by rfl⟩ : syracuseStep 1334789 = 250273) (by norm_num)
theorem B1334813 : Blo 888571 1334813 := bbase (se 3 (by rfl) ⟨250277, by rfl⟩ : syracuseStep 1334813 = 500555) (by norm_num)
theorem B1334837 : Blo 888571 1334837 := bbase (se 5 (by rfl) ⟨62570, by rfl⟩ : syracuseStep 1334837 = 125141) (by norm_num)
theorem B2252357 : Blo 888571 2252357 := bbase (se 4 (by rfl) ⟨211158, by rfl⟩ : syracuseStep 2252357 = 422317) (by norm_num)
theorem B1334861 : Blo 888571 1334861 := bbase (se 3 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 1334861 = 500573) (by norm_num)
theorem B1334885 : Blo 888571 1334885 := bbase (se 4 (by rfl) ⟨125145, by rfl⟩ : syracuseStep 1334885 = 250291) (by norm_num)
theorem B1334909 : Blo 888571 1334909 := bbase (se 3 (by rfl) ⟨250295, by rfl⟩ : syracuseStep 1334909 = 500591) (by norm_num)
theorem B1334933 : Blo 888571 1334933 := bbase (se 6 (by rfl) ⟨31287, by rfl⟩ : syracuseStep 1334933 = 62575) (by norm_num)
theorem B4284053 : Blo 888571 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B1334957 : Blo 888571 1334957 := bbase (se 3 (by rfl) ⟨250304, by rfl⟩ : syracuseStep 1334957 = 500609) (by norm_num)
theorem B1334981 : Blo 888571 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B1335005 : Blo 888571 1335005 := bbase (se 3 (by rfl) ⟨250313, by rfl⟩ : syracuseStep 1335005 = 500627) (by norm_num)
theorem B1335029 : Blo 888571 1335029 := bbase (se 5 (by rfl) ⟨62579, by rfl⟩ : syracuseStep 1335029 = 125159) (by norm_num)
theorem B2252549 : Blo 888571 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B1335053 : Blo 888571 1335053 := bbase (se 3 (by rfl) ⟨250322, by rfl⟩ : syracuseStep 1335053 = 500645) (by norm_num)
theorem B1335077 : Blo 888571 1335077 := bbase (se 4 (by rfl) ⟨125163, by rfl⟩ : syracuseStep 1335077 = 250327) (by norm_num)
theorem B1335101 : Blo 888571 1335101 := bbase (se 3 (by rfl) ⟨250331, by rfl⟩ : syracuseStep 1335101 = 500663) (by norm_num)
theorem B1335125 : Blo 888571 1335125 := bbase (se 9 (by rfl) ⟨3911, by rfl⟩ : syracuseStep 1335125 = 7823) (by norm_num)
theorem B1335149 : Blo 888571 1335149 := bbase (se 3 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 1335149 = 500681) (by norm_num)
theorem B1204085 : Blo 888571 1204085 := bbase (se 5 (by rfl) ⟨56441, by rfl⟩ : syracuseStep 1204085 = 112883) (by norm_num)
theorem B1335173 : Blo 888571 1335173 := bbase (se 4 (by rfl) ⟨125172, by rfl⟩ : syracuseStep 1335173 = 250345) (by norm_num)
theorem B3006341 : Blo 888571 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B1335197 : Blo 888571 1335197 := bbase (se 3 (by rfl) ⟨250349, by rfl⟩ : syracuseStep 1335197 = 500699) (by norm_num)
theorem B1335221 : Blo 888571 1335221 := bbase (se 5 (by rfl) ⟨62588, by rfl⟩ : syracuseStep 1335221 = 125177) (by norm_num)
theorem B1269685 : Blo 888571 1269685 := bbase (se 5 (by rfl) ⟨59516, by rfl⟩ : syracuseStep 1269685 = 119033) (by norm_num)
theorem B1335245 : Blo 888571 1335245 := bbase (se 3 (by rfl) ⟨250358, by rfl⟩ : syracuseStep 1335245 = 500717) (by norm_num)
theorem B1335269 : Blo 888571 1335269 := bbase (se 4 (by rfl) ⟨125181, by rfl⟩ : syracuseStep 1335269 = 250363) (by norm_num)
theorem B1335293 : Blo 888571 1335293 := bbase (se 3 (by rfl) ⟨250367, by rfl⟩ : syracuseStep 1335293 = 500735) (by norm_num)
theorem B1335317 : Blo 888571 1335317 := bbase (se 6 (by rfl) ⟨31296, by rfl⟩ : syracuseStep 1335317 = 62593) (by norm_num)
theorem B1335341 : Blo 888571 1335341 := bbase (se 3 (by rfl) ⟨250376, by rfl⟩ : syracuseStep 1335341 = 500753) (by norm_num)
theorem B1335365 : Blo 888571 1335365 := bbase (se 4 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 1335365 = 250381) (by norm_num)
theorem B2252893 : Blo 888571 2252893 := bbase (se 3 (by rfl) ⟨422417, by rfl⟩ : syracuseStep 2252893 = 844835) (by norm_num)
theorem B1335389 : Blo 888571 1335389 := bbase (se 3 (by rfl) ⟨250385, by rfl⟩ : syracuseStep 1335389 = 500771) (by norm_num)
theorem B1335413 : Blo 888571 1335413 := bbase (se 5 (by rfl) ⟨62597, by rfl⟩ : syracuseStep 1335413 = 125195) (by norm_num)
theorem B1335437 : Blo 888571 1335437 := bbase (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) (by norm_num)
theorem B1335461 : Blo 888571 1335461 := bbase (se 4 (by rfl) ⟨125199, by rfl⟩ : syracuseStep 1335461 = 250399) (by norm_num)
theorem B1335485 : Blo 888571 1335485 := bbase (se 3 (by rfl) ⟨250403, by rfl⟩ : syracuseStep 1335485 = 500807) (by norm_num)
theorem B2253005 : Blo 888571 2253005 := bbase (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) (by norm_num)
theorem B1335509 : Blo 888571 1335509 := bbase (se 7 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 1335509 = 31301) (by norm_num)
theorem B1335533 : Blo 888571 1335533 := bbase (se 3 (by rfl) ⟨250412, by rfl⟩ : syracuseStep 1335533 = 500825) (by norm_num)
theorem B1335557 : Blo 888571 1335557 := bbase (se 4 (by rfl) ⟨125208, by rfl⟩ : syracuseStep 1335557 = 250417) (by norm_num)
theorem B1270021 : Blo 888571 1270021 := bbase (se 4 (by rfl) ⟨119064, by rfl⟩ : syracuseStep 1270021 = 238129) (by norm_num)
theorem B1335581 : Blo 888571 1335581 := bbase (se 3 (by rfl) ⟨250421, by rfl⟩ : syracuseStep 1335581 = 500843) (by norm_num)
theorem B1335605 : Blo 888571 1335605 := bbase (se 5 (by rfl) ⟨62606, by rfl⟩ : syracuseStep 1335605 = 125213) (by norm_num)
theorem B3006773 : Blo 888571 3006773 := bbase (se 5 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 3006773 = 281885) (by norm_num)
theorem B1335629 : Blo 888571 1335629 := bbase (se 3 (by rfl) ⟨250430, by rfl⟩ : syracuseStep 1335629 = 500861) (by norm_num)
theorem B1499485 : Blo 888571 1499485 := bbase (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) (by norm_num)
theorem B1335653 : Blo 888571 1335653 := bbase (se 4 (by rfl) ⟨125217, by rfl⟩ : syracuseStep 1335653 = 250435) (by norm_num)
theorem B7594357 : Blo 888571 7594357 := bbase (se 5 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 7594357 = 711971) (by norm_num)
theorem B1335677 : Blo 888571 1335677 := bbase (se 3 (by rfl) ⟨250439, by rfl⟩ : syracuseStep 1335677 = 500879) (by norm_num)
theorem B2253197 : Blo 888571 2253197 := bbase (se 3 (by rfl) ⟨422474, by rfl⟩ : syracuseStep 2253197 = 844949) (by norm_num)
theorem B1335701 : Blo 888571 1335701 := bbase (se 6 (by rfl) ⟨31305, by rfl⟩ : syracuseStep 1335701 = 62611) (by norm_num)
theorem B1335725 : Blo 888571 1335725 := bbase (se 3 (by rfl) ⟨250448, by rfl⟩ : syracuseStep 1335725 = 500897) (by norm_num)
theorem B1499573 : Blo 888571 1499573 := bbase (se 5 (by rfl) ⟨70292, by rfl⟩ : syracuseStep 1499573 = 140585) (by norm_num)
theorem B3203525 : Blo 888571 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B1335749 : Blo 888571 1335749 := bbase (se 4 (by rfl) ⟨125226, by rfl⟩ : syracuseStep 1335749 = 250453) (by norm_num)
theorem B1335773 : Blo 888571 1335773 := bbase (se 3 (by rfl) ⟨250457, by rfl⟩ : syracuseStep 1335773 = 500915) (by norm_num)
theorem B1270237 : Blo 888571 1270237 := bbase (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) (by norm_num)
theorem B1204717 : Blo 888571 1204717 := bbase (se 3 (by rfl) ⟨225884, by rfl⟩ : syracuseStep 1204717 = 451769) (by norm_num)
theorem B1335797 : Blo 888571 1335797 := bbase (se 5 (by rfl) ⟨62615, by rfl⟩ : syracuseStep 1335797 = 125231) (by norm_num)
theorem B1335821 : Blo 888571 1335821 := bbase (se 3 (by rfl) ⟨250466, by rfl⟩ : syracuseStep 1335821 = 500933) (by norm_num)
theorem B1335845 : Blo 888571 1335845 := bbase (se 4 (by rfl) ⟨125235, by rfl⟩ : syracuseStep 1335845 = 250471) (by norm_num)
theorem B1499701 : Blo 888571 1499701 := bbase (se 5 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 1499701 = 140597) (by norm_num)
theorem B1335869 : Blo 888571 1335869 := bbase (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) (by norm_num)
theorem B1335893 : Blo 888571 1335893 := bbase (se 8 (by rfl) ⟨7827, by rfl⟩ : syracuseStep 1335893 = 15655) (by norm_num)
theorem B51372629 : Blo 888571 51372629 := bbase (se 8 (by rfl) ⟨301011, by rfl⟩ : syracuseStep 51372629 = 602023) (by norm_num)
theorem B1335917 : Blo 888571 1335917 := bbase (se 3 (by rfl) ⟨250484, by rfl⟩ : syracuseStep 1335917 = 500969) (by norm_num)
theorem B1335941 : Blo 888571 1335941 := bbase (se 4 (by rfl) ⟨125244, by rfl⟩ : syracuseStep 1335941 = 250489) (by norm_num)
theorem B1499789 : Blo 888571 1499789 := bbase (se 3 (by rfl) ⟨281210, by rfl⟩ : syracuseStep 1499789 = 562421) (by norm_num)
theorem B4514453 : Blo 888571 4514453 := bbase (se 6 (by rfl) ⟨105807, by rfl⟩ : syracuseStep 4514453 = 211615) (by norm_num)
theorem B1335965 : Blo 888571 1335965 := bbase (se 3 (by rfl) ⟨250493, by rfl⟩ : syracuseStep 1335965 = 500987) (by norm_num)
theorem B1335989 : Blo 888571 1335989 := bbase (se 5 (by rfl) ⟨62624, by rfl⟩ : syracuseStep 1335989 = 125249) (by norm_num)
theorem B1336013 : Blo 888571 1336013 := bbase (se 3 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 1336013 = 501005) (by norm_num)
theorem B3203813 : Blo 888571 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B2253541 : Blo 888571 2253541 := bbase (se 4 (by rfl) ⟨211269, by rfl⟩ : syracuseStep 2253541 = 422539) (by norm_num)
theorem B1336037 : Blo 888571 1336037 := bbase (se 4 (by rfl) ⟨125253, by rfl⟩ : syracuseStep 1336037 = 250507) (by norm_num)
theorem B3007205 : Blo 888571 3007205 := bbase (se 4 (by rfl) ⟨281925, by rfl⟩ : syracuseStep 3007205 = 563851) (by norm_num)
theorem B1336061 : Blo 888571 1336061 := bbase (se 3 (by rfl) ⟨250511, by rfl⟩ : syracuseStep 1336061 = 501023) (by norm_num)
theorem B1499917 : Blo 888571 1499917 := bbase (se 3 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 1499917 = 562469) (by norm_num)
theorem B1336085 : Blo 888571 1336085 := bbase (se 6 (by rfl) ⟨31314, by rfl⟩ : syracuseStep 1336085 = 62629) (by norm_num)
theorem B1336109 : Blo 888571 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B1336133 : Blo 888571 1336133 := bbase (se 4 (by rfl) ⟨125262, by rfl⟩ : syracuseStep 1336133 = 250525) (by norm_num)
theorem B2253653 : Blo 888571 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1270613 : Blo 888571 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B1336157 : Blo 888571 1336157 := bbase (se 3 (by rfl) ⟨250529, by rfl⟩ : syracuseStep 1336157 = 501059) (by norm_num)
theorem B1500005 : Blo 888571 1500005 := bbase (se 4 (by rfl) ⟨140625, by rfl⟩ : syracuseStep 1500005 = 281251) (by norm_num)
theorem B1336181 : Blo 888571 1336181 := bbase (se 5 (by rfl) ⟨62633, by rfl⟩ : syracuseStep 1336181 = 125267) (by norm_num)
theorem B7725941 : Blo 888571 7725941 := bbase (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) (by norm_num)
theorem B1336205 : Blo 888571 1336205 := bbase (se 3 (by rfl) ⟨250538, by rfl⟩ : syracuseStep 1336205 = 501077) (by norm_num)
theorem B1336229 : Blo 888571 1336229 := bbase (se 4 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 1336229 = 250543) (by norm_num)
theorem B1336253 : Blo 888571 1336253 := bbase (se 3 (by rfl) ⟨250547, by rfl⟩ : syracuseStep 1336253 = 501095) (by norm_num)
theorem B1336277 : Blo 888571 1336277 := bbase (se 7 (by rfl) ⟨15659, by rfl⟩ : syracuseStep 1336277 = 31319) (by norm_num)
theorem B1500133 : Blo 888571 1500133 := bbase (se 4 (by rfl) ⟨140637, by rfl⟩ : syracuseStep 1500133 = 281275) (by norm_num)
theorem B1336301 : Blo 888571 1336301 := bbase (se 3 (by rfl) ⟨250556, by rfl⟩ : syracuseStep 1336301 = 501113) (by norm_num)
theorem B1336325 : Blo 888571 1336325 := bbase (se 4 (by rfl) ⟨125280, by rfl⟩ : syracuseStep 1336325 = 250561) (by norm_num)
theorem B2253845 : Blo 888571 2253845 := bbase (se 6 (by rfl) ⟨52824, by rfl⟩ : syracuseStep 2253845 = 105649) (by norm_num)
theorem B1336349 : Blo 888571 1336349 := bbase (se 3 (by rfl) ⟨250565, by rfl⟩ : syracuseStep 1336349 = 501131) (by norm_num)
theorem B1336373 : Blo 888571 1336373 := bbase (se 5 (by rfl) ⟨62642, by rfl⟩ : syracuseStep 1336373 = 125285) (by norm_num)
theorem B1500221 : Blo 888571 1500221 := bbase (se 3 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 1500221 = 562583) (by norm_num)
theorem B1336397 : Blo 888571 1336397 := bbase (se 3 (by rfl) ⟨250574, by rfl⟩ : syracuseStep 1336397 = 501149) (by norm_num)
theorem B1336421 : Blo 888571 1336421 := bbase (se 4 (by rfl) ⟨125289, by rfl⟩ : syracuseStep 1336421 = 250579) (by norm_num)
theorem B1336445 : Blo 888571 1336445 := bbase (se 3 (by rfl) ⟨250583, by rfl⟩ : syracuseStep 1336445 = 501167) (by norm_num)
theorem B1336469 : Blo 888571 1336469 := bbase (se 6 (by rfl) ⟨31323, by rfl⟩ : syracuseStep 1336469 = 62647) (by norm_num)
theorem B3007637 : Blo 888571 3007637 := bbase (se 6 (by rfl) ⟨70491, by rfl⟩ : syracuseStep 3007637 = 140983) (by norm_num)
theorem B3433637 : Blo 888571 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B1336493 : Blo 888571 1336493 := bbase (se 3 (by rfl) ⟨250592, by rfl⟩ : syracuseStep 1336493 = 501185) (by norm_num)
theorem B1500349 : Blo 888571 1500349 := bbase (se 3 (by rfl) ⟨281315, by rfl⟩ : syracuseStep 1500349 = 562631) (by norm_num)
theorem B1336517 : Blo 888571 1336517 := bbase (se 4 (by rfl) ⟨125298, by rfl⟩ : syracuseStep 1336517 = 250597) (by norm_num)
theorem B1336541 : Blo 888571 1336541 := bbase (se 3 (by rfl) ⟨250601, by rfl⟩ : syracuseStep 1336541 = 501203) (by norm_num)
theorem B1336565 : Blo 888571 1336565 := bbase (se 5 (by rfl) ⟨62651, by rfl⟩ : syracuseStep 1336565 = 125303) (by norm_num)
theorem B1336589 : Blo 888571 1336589 := bbase (se 3 (by rfl) ⟨250610, by rfl⟩ : syracuseStep 1336589 = 501221) (by norm_num)
theorem B1500437 : Blo 888571 1500437 := bbase (se 6 (by rfl) ⟨35166, by rfl⟩ : syracuseStep 1500437 = 70333) (by norm_num)
theorem B1336613 : Blo 888571 1336613 := bbase (se 4 (by rfl) ⟨125307, by rfl⟩ : syracuseStep 1336613 = 250615) (by norm_num)
theorem B1336637 : Blo 888571 1336637 := bbase (se 3 (by rfl) ⟨250619, by rfl⟩ : syracuseStep 1336637 = 501239) (by norm_num)
theorem B38495573 : Blo 888571 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B1336661 : Blo 888571 1336661 := bbase (se 12 (by rfl) ⟨489, by rfl⟩ : syracuseStep 1336661 = 979) (by norm_num)
theorem B2254189 : Blo 888571 2254189 := bbase (se 3 (by rfl) ⟨422660, by rfl⟩ : syracuseStep 2254189 = 845321) (by norm_num)
theorem B1336685 : Blo 888571 1336685 := bbase (se 3 (by rfl) ⟨250628, by rfl⟩ : syracuseStep 1336685 = 501257) (by norm_num)
theorem B1336709 : Blo 888571 1336709 := bbase (se 4 (by rfl) ⟨125316, by rfl⟩ : syracuseStep 1336709 = 250633) (by norm_num)
theorem B1500565 : Blo 888571 1500565 := bbase (se 6 (by rfl) ⟨35169, by rfl⟩ : syracuseStep 1500565 = 70339) (by norm_num)
theorem B1336733 : Blo 888571 1336733 := bbase (se 3 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 1336733 = 501275) (by norm_num)
theorem B1336757 : Blo 888571 1336757 := bbase (se 5 (by rfl) ⟨62660, by rfl⟩ : syracuseStep 1336757 = 125321) (by norm_num)
theorem B1336781 : Blo 888571 1336781 := bbase (se 3 (by rfl) ⟨250646, by rfl⟩ : syracuseStep 1336781 = 501293) (by norm_num)
theorem B2254301 : Blo 888571 2254301 := bbase (se 3 (by rfl) ⟨422681, by rfl⟩ : syracuseStep 2254301 = 845363) (by norm_num)
theorem B1336805 : Blo 888571 1336805 := bbase (se 4 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 1336805 = 250651) (by norm_num)
theorem B1500653 : Blo 888571 1500653 := bbase (se 3 (by rfl) ⟨281372, by rfl⟩ : syracuseStep 1500653 = 562745) (by norm_num)
theorem B1336829 : Blo 888571 1336829 := bbase (se 3 (by rfl) ⟨250655, by rfl⟩ : syracuseStep 1336829 = 501311) (by norm_num)
theorem B1336853 : Blo 888571 1336853 := bbase (se 6 (by rfl) ⟨31332, by rfl⟩ : syracuseStep 1336853 = 62665) (by norm_num)
theorem B1336877 : Blo 888571 1336877 := bbase (se 3 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 1336877 = 501329) (by norm_num)
theorem B1336901 : Blo 888571 1336901 := bbase (se 4 (by rfl) ⟨125334, by rfl⟩ : syracuseStep 1336901 = 250669) (by norm_num)
theorem B3008069 : Blo 888571 3008069 := bbase (se 4 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 3008069 = 564013) (by norm_num)
theorem B1336925 : Blo 888571 1336925 := bbase (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) (by norm_num)
theorem B1500781 : Blo 888571 1500781 := bbase (se 3 (by rfl) ⟨281396, by rfl⟩ : syracuseStep 1500781 = 562793) (by norm_num)
theorem B1336949 : Blo 888571 1336949 := bbase (se 5 (by rfl) ⟨62669, by rfl⟩ : syracuseStep 1336949 = 125339) (by norm_num)
theorem B1336973 : Blo 888571 1336973 := bbase (se 3 (by rfl) ⟨250682, by rfl⟩ : syracuseStep 1336973 = 501365) (by norm_num)
theorem B2254493 : Blo 888571 2254493 := bbase (se 3 (by rfl) ⟨422717, by rfl⟩ : syracuseStep 2254493 = 845435) (by norm_num)
theorem B1205917 : Blo 888571 1205917 := bbase (se 3 (by rfl) ⟨226109, by rfl⟩ : syracuseStep 1205917 = 452219) (by norm_num)
theorem B1336997 : Blo 888571 1336997 := bbase (se 4 (by rfl) ⟨125343, by rfl⟩ : syracuseStep 1336997 = 250687) (by norm_num)
theorem B1337021 : Blo 888571 1337021 := bbase (se 3 (by rfl) ⟨250691, by rfl⟩ : syracuseStep 1337021 = 501383) (by norm_num)
theorem B1500869 : Blo 888571 1500869 := bbase (se 4 (by rfl) ⟨140706, by rfl⟩ : syracuseStep 1500869 = 281413) (by norm_num)
theorem B1337045 : Blo 888571 1337045 := bbase (se 7 (by rfl) ⟨15668, by rfl⟩ : syracuseStep 1337045 = 31337) (by norm_num)
theorem B1337069 : Blo 888571 1337069 := bbase (se 3 (by rfl) ⟨250700, by rfl⟩ : syracuseStep 1337069 = 501401) (by norm_num)
theorem B1337093 : Blo 888571 1337093 := bbase (se 4 (by rfl) ⟨125352, by rfl⟩ : syracuseStep 1337093 = 250705) (by norm_num)
theorem B1337117 : Blo 888571 1337117 := bbase (se 3 (by rfl) ⟨250709, by rfl⟩ : syracuseStep 1337117 = 501419) (by norm_num)
theorem B1337141 : Blo 888571 1337141 := bbase (se 5 (by rfl) ⟨62678, by rfl⟩ : syracuseStep 1337141 = 125357) (by norm_num)
theorem B1828669 : Blo 888571 1828669 := bbase (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) (by norm_num)
theorem B1500997 : Blo 888571 1500997 := bbase (se 4 (by rfl) ⟨140718, by rfl⟩ : syracuseStep 1500997 = 281437) (by norm_num)
theorem B1337165 : Blo 888571 1337165 := bbase (se 3 (by rfl) ⟨250718, by rfl⟩ : syracuseStep 1337165 = 501437) (by norm_num)
theorem B1206101 : Blo 888571 1206101 := bbase (se 9 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 1206101 = 7067) (by norm_num)
theorem B1337189 : Blo 888571 1337189 := bbase (se 4 (by rfl) ⟨125361, by rfl⟩ : syracuseStep 1337189 = 250723) (by norm_num)
theorem B1337213 : Blo 888571 1337213 := bbase (se 3 (by rfl) ⟨250727, by rfl⟩ : syracuseStep 1337213 = 501455) (by norm_num)
theorem B1337237 : Blo 888571 1337237 := bbase (se 6 (by rfl) ⟨31341, by rfl⟩ : syracuseStep 1337237 = 62683) (by norm_num)
theorem B1501085 : Blo 888571 1501085 := bbase (se 3 (by rfl) ⟨281453, by rfl⟩ : syracuseStep 1501085 = 562907) (by norm_num)
theorem B4515749 : Blo 888571 4515749 := bbase (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) (by norm_num)
theorem B1337261 : Blo 888571 1337261 := bbase (se 3 (by rfl) ⟨250736, by rfl⟩ : syracuseStep 1337261 = 501473) (by norm_num)
theorem B1337285 : Blo 888571 1337285 := bbase (se 4 (by rfl) ⟨125370, by rfl⟩ : syracuseStep 1337285 = 250741) (by norm_num)
theorem B1337309 : Blo 888571 1337309 := bbase (se 3 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 1337309 = 501491) (by norm_num)
theorem B2254837 : Blo 888571 2254837 := bbase (se 5 (by rfl) ⟨105695, by rfl⟩ : syracuseStep 2254837 = 211391) (by norm_num)
theorem B3008501 : Blo 888571 3008501 := bbase (se 5 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 3008501 = 282047) (by norm_num)
theorem B1337333 : Blo 888571 1337333 := bbase (se 5 (by rfl) ⟨62687, by rfl⟩ : syracuseStep 1337333 = 125375) (by norm_num)
theorem B1337357 : Blo 888571 1337357 := bbase (se 3 (by rfl) ⟨250754, by rfl⟩ : syracuseStep 1337357 = 501509) (by norm_num)
theorem B1501213 : Blo 888571 1501213 := bbase (se 3 (by rfl) ⟨281477, by rfl⟩ : syracuseStep 1501213 = 562955) (by norm_num)
theorem B1337381 : Blo 888571 1337381 := bbase (se 4 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 1337381 = 250759) (by norm_num)
theorem B5695541 : Blo 888571 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B1337405 : Blo 888571 1337405 := bbase (se 3 (by rfl) ⟨250763, by rfl⟩ : syracuseStep 1337405 = 501527) (by norm_num)
theorem B1337429 : Blo 888571 1337429 := bbase (se 8 (by rfl) ⟨7836, by rfl⟩ : syracuseStep 1337429 = 15673) (by norm_num)
theorem B2254949 : Blo 888571 2254949 := bbase (se 4 (by rfl) ⟨211401, by rfl⟩ : syracuseStep 2254949 = 422803) (by norm_num)
theorem B1337453 : Blo 888571 1337453 := bbase (se 3 (by rfl) ⟨250772, by rfl⟩ : syracuseStep 1337453 = 501545) (by norm_num)
theorem B1501301 : Blo 888571 1501301 := bbase (se 5 (by rfl) ⟨70373, by rfl⟩ : syracuseStep 1501301 = 140747) (by norm_num)
theorem B6514805 : Blo 888571 6514805 := bbase (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) (by norm_num)
theorem B1337477 : Blo 888571 1337477 := bbase (se 4 (by rfl) ⟨125388, by rfl⟩ : syracuseStep 1337477 = 250777) (by norm_num)
theorem B1337501 : Blo 888571 1337501 := bbase (se 3 (by rfl) ⟨250781, by rfl⟩ : syracuseStep 1337501 = 501563) (by norm_num)
theorem B1140913 : Blo 888571 1140913 := bbase (se 2 (by rfl) ⟨427842, by rfl⟩ : syracuseStep 1140913 = 855685) (by norm_num)
theorem B1337525 : Blo 888571 1337525 := bbase (se 5 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 1337525 = 125393) (by norm_num)
theorem B1337549 : Blo 888571 1337549 := bbase (se 3 (by rfl) ⟨250790, by rfl⟩ : syracuseStep 1337549 = 501581) (by norm_num)
theorem B1337573 : Blo 888571 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1501429 : Blo 888571 1501429 := bbase (se 5 (by rfl) ⟨70379, by rfl⟩ : syracuseStep 1501429 = 140759) (by norm_num)
theorem B1337597 : Blo 888571 1337597 := bbase (se 3 (by rfl) ⟨250799, by rfl⟩ : syracuseStep 1337597 = 501599) (by norm_num)
theorem B1337621 : Blo 888571 1337621 := bbase (se 6 (by rfl) ⟨31350, by rfl⟩ : syracuseStep 1337621 = 62701) (by norm_num)
theorem B4057381 : Blo 888571 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B2255141 : Blo 888571 2255141 := bbase (se 4 (by rfl) ⟨211419, by rfl⟩ : syracuseStep 2255141 = 422839) (by norm_num)
theorem B1337645 : Blo 888571 1337645 := bbase (se 3 (by rfl) ⟨250808, by rfl⟩ : syracuseStep 1337645 = 501617) (by norm_num)
theorem B7596341 : Blo 888571 7596341 := bbase (se 5 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 7596341 = 712157) (by norm_num)
theorem B1337669 : Blo 888571 1337669 := bbase (se 4 (by rfl) ⟨125406, by rfl⟩ : syracuseStep 1337669 = 250813) (by norm_num)
theorem B1501517 : Blo 888571 1501517 := bbase (se 3 (by rfl) ⟨281534, by rfl⟩ : syracuseStep 1501517 = 563069) (by norm_num)
theorem B1337693 : Blo 888571 1337693 := bbase (se 3 (by rfl) ⟨250817, by rfl⟩ : syracuseStep 1337693 = 501635) (by norm_num)
theorem B1337717 : Blo 888571 1337717 := bbase (se 5 (by rfl) ⟨62705, by rfl⟩ : syracuseStep 1337717 = 125411) (by norm_num)
theorem B1337741 : Blo 888571 1337741 := bbase (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) (by norm_num)
theorem B3008933 : Blo 888571 3008933 := bbase (se 4 (by rfl) ⟨282087, by rfl⟩ : syracuseStep 3008933 = 564175) (by norm_num)
theorem B1337765 : Blo 888571 1337765 := bbase (se 4 (by rfl) ⟨125415, by rfl⟩ : syracuseStep 1337765 = 250831) (by norm_num)
theorem B6777269 : Blo 888571 6777269 := bbase (se 5 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 6777269 = 635369) (by norm_num)
theorem B1337789 : Blo 888571 1337789 := bbase (se 3 (by rfl) ⟨250835, by rfl⟩ : syracuseStep 1337789 = 501671) (by norm_num)
theorem B1501645 : Blo 888571 1501645 := bbase (se 3 (by rfl) ⟨281558, by rfl⟩ : syracuseStep 1501645 = 563117) (by norm_num)
theorem B1337813 : Blo 888571 1337813 := bbase (se 7 (by rfl) ⟨15677, by rfl⟩ : syracuseStep 1337813 = 31355) (by norm_num)
theorem B1337837 : Blo 888571 1337837 := bbase (se 3 (by rfl) ⟨250844, by rfl⟩ : syracuseStep 1337837 = 501689) (by norm_num)
theorem B1141241 : Blo 888571 1141241 := bbase (se 2 (by rfl) ⟨427965, by rfl⟩ : syracuseStep 1141241 = 855931) (by norm_num)
theorem B1337861 : Blo 888571 1337861 := bbase (se 4 (by rfl) ⟨125424, by rfl⟩ : syracuseStep 1337861 = 250849) (by norm_num)
theorem B1337885 : Blo 888571 1337885 := bbase (se 3 (by rfl) ⟨250853, by rfl⟩ : syracuseStep 1337885 = 501707) (by norm_num)
theorem B1501733 : Blo 888571 1501733 := bbase (se 4 (by rfl) ⟨140787, by rfl⟩ : syracuseStep 1501733 = 281575) (by norm_num)
theorem B1337909 : Blo 888571 1337909 := bbase (se 5 (by rfl) ⟨62714, by rfl⟩ : syracuseStep 1337909 = 125429) (by norm_num)
theorem B2714165 : Blo 888571 2714165 := bbase (se 5 (by rfl) ⟨127226, by rfl⟩ : syracuseStep 2714165 = 254453) (by norm_num)
theorem B1337933 : Blo 888571 1337933 := bbase (se 3 (by rfl) ⟨250862, by rfl⟩ : syracuseStep 1337933 = 501725) (by norm_num)
theorem B1337957 : Blo 888571 1337957 := bbase (se 4 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 1337957 = 250867) (by norm_num)
theorem B2255485 : Blo 888571 2255485 := bbase (se 3 (by rfl) ⟨422903, by rfl⟩ : syracuseStep 2255485 = 845807) (by norm_num)
theorem B1337981 : Blo 888571 1337981 := bbase (se 3 (by rfl) ⟨250871, by rfl⟩ : syracuseStep 1337981 = 501743) (by norm_num)
theorem B1338005 : Blo 888571 1338005 := bbase (se 6 (by rfl) ⟨31359, by rfl⟩ : syracuseStep 1338005 = 62719) (by norm_num)
theorem B1501861 : Blo 888571 1501861 := bbase (se 4 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 1501861 = 281599) (by norm_num)
theorem B1338029 : Blo 888571 1338029 := bbase (se 3 (by rfl) ⟨250880, by rfl⟩ : syracuseStep 1338029 = 501761) (by norm_num)
theorem B1338053 : Blo 888571 1338053 := bbase (se 4 (by rfl) ⟨125442, by rfl⟩ : syracuseStep 1338053 = 250885) (by norm_num)
theorem B1338077 : Blo 888571 1338077 := bbase (se 3 (by rfl) ⟨250889, by rfl⟩ : syracuseStep 1338077 = 501779) (by norm_num)
theorem B2255597 : Blo 888571 2255597 := bbase (se 3 (by rfl) ⟨422924, by rfl⟩ : syracuseStep 2255597 = 845849) (by norm_num)
theorem B1338101 : Blo 888571 1338101 := bbase (se 5 (by rfl) ⟨62723, by rfl⟩ : syracuseStep 1338101 = 125447) (by norm_num)
theorem B1501949 : Blo 888571 1501949 := bbase (se 3 (by rfl) ⟨281615, by rfl⟩ : syracuseStep 1501949 = 563231) (by norm_num)
theorem B1338125 : Blo 888571 1338125 := bbase (se 3 (by rfl) ⟨250898, by rfl⟩ : syracuseStep 1338125 = 501797) (by norm_num)
theorem B1338149 : Blo 888571 1338149 := bbase (se 4 (by rfl) ⟨125451, by rfl⟩ : syracuseStep 1338149 = 250903) (by norm_num)
theorem B1338173 : Blo 888571 1338173 := bbase (se 3 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 1338173 = 501815) (by norm_num)
theorem B5073749 : Blo 888571 5073749 := bbase (se 9 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 5073749 = 29729) (by norm_num)
theorem B3009365 : Blo 888571 3009365 := bbase (se 9 (by rfl) ⟨8816, by rfl⟩ : syracuseStep 3009365 = 17633) (by norm_num)
theorem B1338197 : Blo 888571 1338197 := bbase (se 9 (by rfl) ⟨3920, by rfl⟩ : syracuseStep 1338197 = 7841) (by norm_num)
theorem B1338221 : Blo 888571 1338221 := bbase (se 3 (by rfl) ⟨250916, by rfl⟩ : syracuseStep 1338221 = 501833) (by norm_num)
theorem B1502077 : Blo 888571 1502077 := bbase (se 3 (by rfl) ⟨281639, by rfl⟩ : syracuseStep 1502077 = 563279) (by norm_num)
theorem B1338245 : Blo 888571 1338245 := bbase (se 4 (by rfl) ⟨125460, by rfl⟩ : syracuseStep 1338245 = 250921) (by norm_num)
theorem B1338269 : Blo 888571 1338269 := bbase (se 3 (by rfl) ⟨250925, by rfl⟩ : syracuseStep 1338269 = 501851) (by norm_num)
theorem B2255789 : Blo 888571 2255789 := bbase (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) (by norm_num)
theorem B1338293 : Blo 888571 1338293 := bbase (se 5 (by rfl) ⟨62732, by rfl⟩ : syracuseStep 1338293 = 125465) (by norm_num)
theorem B1141709 : Blo 888571 1141709 := bbase (se 3 (by rfl) ⟨214070, by rfl⟩ : syracuseStep 1141709 = 428141) (by norm_num)
theorem B1338317 : Blo 888571 1338317 := bbase (se 3 (by rfl) ⟨250934, by rfl⟩ : syracuseStep 1338317 = 501869) (by norm_num)
theorem B1502165 : Blo 888571 1502165 := bbase (se 7 (by rfl) ⟨17603, by rfl⟩ : syracuseStep 1502165 = 35207) (by norm_num)
theorem B1338341 : Blo 888571 1338341 := bbase (se 4 (by rfl) ⟨125469, by rfl⟩ : syracuseStep 1338341 = 250939) (by norm_num)
theorem B1338365 : Blo 888571 1338365 := bbase (se 3 (by rfl) ⟨250943, by rfl⟩ : syracuseStep 1338365 = 501887) (by norm_num)
theorem B1338389 : Blo 888571 1338389 := bbase (se 6 (by rfl) ⟨31368, by rfl⟩ : syracuseStep 1338389 = 62737) (by norm_num)
theorem B1338413 : Blo 888571 1338413 := bbase (se 3 (by rfl) ⟨250952, by rfl⟩ : syracuseStep 1338413 = 501905) (by norm_num)
theorem B1338437 : Blo 888571 1338437 := bbase (se 4 (by rfl) ⟨125478, by rfl⟩ : syracuseStep 1338437 = 250957) (by norm_num)
theorem B1502293 : Blo 888571 1502293 := bbase (se 8 (by rfl) ⟨8802, by rfl⟩ : syracuseStep 1502293 = 17605) (by norm_num)
theorem B1338461 : Blo 888571 1338461 := bbase (se 3 (by rfl) ⟨250961, by rfl⟩ : syracuseStep 1338461 = 501923) (by norm_num)
theorem B1174637 : Blo 888571 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B3796085 : Blo 888571 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B1338485 : Blo 888571 1338485 := bbase (se 5 (by rfl) ⟨62741, by rfl⟩ : syracuseStep 1338485 = 125483) (by norm_num)
theorem B1338509 : Blo 888571 1338509 := bbase (se 3 (by rfl) ⟨250970, by rfl⟩ : syracuseStep 1338509 = 501941) (by norm_num)
theorem B4942997 : Blo 888571 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B1338533 : Blo 888571 1338533 := bbase (se 4 (by rfl) ⟨125487, by rfl⟩ : syracuseStep 1338533 = 250975) (by norm_num)
theorem B1502381 : Blo 888571 1502381 := bbase (se 3 (by rfl) ⟨281696, by rfl⟩ : syracuseStep 1502381 = 563393) (by norm_num)
theorem B4517045 : Blo 888571 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B1338557 : Blo 888571 1338557 := bbase (se 3 (by rfl) ⟨250979, by rfl⟩ : syracuseStep 1338557 = 501959) (by norm_num)
theorem B1338581 : Blo 888571 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B1338605 : Blo 888571 1338605 := bbase (se 3 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 1338605 = 501977) (by norm_num)
theorem B2256133 : Blo 888571 2256133 := bbase (se 4 (by rfl) ⟨211512, by rfl⟩ : syracuseStep 2256133 = 423025) (by norm_num)
theorem B3009797 : Blo 888571 3009797 := bbase (se 4 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 3009797 = 564337) (by norm_num)
theorem B1338629 : Blo 888571 1338629 := bbase (se 4 (by rfl) ⟨125496, by rfl⟩ : syracuseStep 1338629 = 250993) (by norm_num)
theorem B1338653 : Blo 888571 1338653 := bbase (se 3 (by rfl) ⟨250997, by rfl⟩ : syracuseStep 1338653 = 501995) (by norm_num)
theorem B1502509 : Blo 888571 1502509 := bbase (se 3 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 1502509 = 563441) (by norm_num)
theorem B1338677 : Blo 888571 1338677 := bbase (se 5 (by rfl) ⟨62750, by rfl⟩ : syracuseStep 1338677 = 125501) (by norm_num)
theorem B1338701 : Blo 888571 1338701 := bbase (se 3 (by rfl) ⟨251006, by rfl⟩ : syracuseStep 1338701 = 502013) (by norm_num)
theorem B1338725 : Blo 888571 1338725 := bbase (se 4 (by rfl) ⟨125505, by rfl⟩ : syracuseStep 1338725 = 251011) (by norm_num)
theorem B2256245 : Blo 888571 2256245 := bbase (se 5 (by rfl) ⟨105761, by rfl⟩ : syracuseStep 2256245 = 211523) (by norm_num)
theorem B1338749 : Blo 888571 1338749 := bbase (se 3 (by rfl) ⟨251015, by rfl⟩ : syracuseStep 1338749 = 502031) (by norm_num)
theorem B1502597 : Blo 888571 1502597 := bbase (se 4 (by rfl) ⟨140868, by rfl⟩ : syracuseStep 1502597 = 281737) (by norm_num)
theorem B1338773 : Blo 888571 1338773 := bbase (se 6 (by rfl) ⟨31377, by rfl⟩ : syracuseStep 1338773 = 62755) (by norm_num)
theorem B1338797 : Blo 888571 1338797 := bbase (se 3 (by rfl) ⟨251024, by rfl⟩ : syracuseStep 1338797 = 502049) (by norm_num)
theorem B1338821 : Blo 888571 1338821 := bbase (se 4 (by rfl) ⟨125514, by rfl⟩ : syracuseStep 1338821 = 251029) (by norm_num)
theorem B1338845 : Blo 888571 1338845 := bbase (se 3 (by rfl) ⟨251033, by rfl⟩ : syracuseStep 1338845 = 502067) (by norm_num)
theorem B4287973 : Blo 888571 4287973 := bbase (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) (by norm_num)
theorem B1502725 : Blo 888571 1502725 := bbase (se 4 (by rfl) ⟨140880, by rfl⟩ : syracuseStep 1502725 = 281761) (by norm_num)
theorem B1142309 : Blo 888571 1142309 := bbase (se 4 (by rfl) ⟨107091, by rfl⟩ : syracuseStep 1142309 = 214183) (by norm_num)
theorem B2256437 : Blo 888571 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B1502813 : Blo 888571 1502813 := bbase (se 3 (by rfl) ⟨281777, by rfl⟩ : syracuseStep 1502813 = 563555) (by norm_num)
theorem B1142381 : Blo 888571 1142381 := bbase (se 3 (by rfl) ⟨214196, by rfl⟩ : syracuseStep 1142381 = 428393) (by norm_num)
theorem B3010229 : Blo 888571 3010229 := bbase (se 5 (by rfl) ⟨141104, by rfl⟩ : syracuseStep 3010229 = 282209) (by norm_num)
theorem B1502941 : Blo 888571 1502941 := bbase (se 3 (by rfl) ⟨281801, by rfl⟩ : syracuseStep 1502941 = 563603) (by norm_num)
theorem B1503029 : Blo 888571 1503029 := bbase (se 5 (by rfl) ⟨70454, by rfl⟩ : syracuseStep 1503029 = 140909) (by norm_num)
theorem B2256781 : Blo 888571 2256781 := bbase (se 3 (by rfl) ⟨423146, by rfl⟩ : syracuseStep 2256781 = 846293) (by norm_num)
theorem B1503157 : Blo 888571 1503157 := bbase (se 5 (by rfl) ⟨70460, by rfl⟩ : syracuseStep 1503157 = 140921) (by norm_num)
theorem B5074933 : Blo 888571 5074933 := bbase (se 5 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 5074933 = 475775) (by norm_num)
theorem B1929205 : Blo 888571 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B2256893 : Blo 888571 2256893 := bbase (se 3 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 2256893 = 846335) (by norm_num)
theorem B1503245 : Blo 888571 1503245 := bbase (se 3 (by rfl) ⟨281858, by rfl⟩ : syracuseStep 1503245 = 563717) (by norm_num)
theorem B3797077 : Blo 888571 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B3010661 : Blo 888571 3010661 := bbase (se 4 (by rfl) ⟨282249, by rfl⟩ : syracuseStep 3010661 = 564499) (by norm_num)
theorem B1503373 : Blo 888571 1503373 := bbase (se 3 (by rfl) ⟨281882, by rfl⟩ : syracuseStep 1503373 = 563765) (by norm_num)
theorem B2257085 : Blo 888571 2257085 := bbase (se 3 (by rfl) ⟨423203, by rfl⟩ : syracuseStep 2257085 = 846407) (by norm_num)
theorem B1503461 : Blo 888571 1503461 := bbase (se 4 (by rfl) ⟨140949, by rfl⟩ : syracuseStep 1503461 = 281899) (by norm_num)
theorem B1143109 : Blo 888571 1143109 := bbase (se 4 (by rfl) ⟨107166, by rfl⟩ : syracuseStep 1143109 = 214333) (by norm_num)
theorem B1503589 : Blo 888571 1503589 := bbase (se 4 (by rfl) ⟨140961, by rfl⟩ : syracuseStep 1503589 = 281923) (by norm_num)
theorem B1503677 : Blo 888571 1503677 := bbase (se 3 (by rfl) ⟨281939, by rfl⟩ : syracuseStep 1503677 = 563879) (by norm_num)
theorem B4518341 : Blo 888571 4518341 := bbase (se 4 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 4518341 = 847189) (by norm_num)
theorem B2257429 : Blo 888571 2257429 := bbase (se 6 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 2257429 = 105817) (by norm_num)
theorem B3011093 : Blo 888571 3011093 := bbase (se 6 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 3011093 = 141145) (by norm_num)
theorem B1143325 : Blo 888571 1143325 := bbase (se 3 (by rfl) ⟨214373, by rfl⟩ : syracuseStep 1143325 = 428747) (by norm_num)
theorem B2847269 : Blo 888571 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B1602109 : Blo 888571 1602109 := bbase (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) (by norm_num)
theorem B1503805 : Blo 888571 1503805 := bbase (se 3 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 1503805 = 563927) (by norm_num)
theorem B2257541 : Blo 888571 2257541 := bbase (se 4 (by rfl) ⟨211644, by rfl⟩ : syracuseStep 2257541 = 423289) (by norm_num)
theorem B1503893 : Blo 888571 1503893 := bbase (se 6 (by rfl) ⟨35247, by rfl⟩ : syracuseStep 1503893 = 70495) (by norm_num)
theorem B17330965 : Blo 888571 17330965 := bbase (se 6 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 17330965 = 812389) (by norm_num)
theorem B1504021 : Blo 888571 1504021 := bbase (se 6 (by rfl) ⟨35250, by rfl⟩ : syracuseStep 1504021 = 70501) (by norm_num)
theorem B2028325 : Blo 888571 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B2257733 : Blo 888571 2257733 := bbase (se 4 (by rfl) ⟨211662, by rfl⟩ : syracuseStep 2257733 = 423325) (by norm_num)
theorem B1504109 : Blo 888571 1504109 := bbase (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) (by norm_num)
theorem B3011525 : Blo 888571 3011525 := bbase (se 4 (by rfl) ⟨282330, by rfl⟩ : syracuseStep 3011525 = 564661) (by norm_num)
theorem B1504237 : Blo 888571 1504237 := bbase (se 3 (by rfl) ⟨282044, by rfl⟩ : syracuseStep 1504237 = 564089) (by norm_num)
theorem B1504325 : Blo 888571 1504325 := bbase (se 4 (by rfl) ⟨141030, by rfl⟩ : syracuseStep 1504325 = 282061) (by norm_num)
theorem B2258077 : Blo 888571 2258077 := bbase (se 3 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 2258077 = 846779) (by norm_num)
theorem B1504453 : Blo 888571 1504453 := bbase (se 4 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 1504453 = 282085) (by norm_num)
theorem B914641 : Blo 888571 914641 := bbase (se 2 (by rfl) ⟨342990, by rfl⟩ : syracuseStep 914641 = 685981) (by norm_num)
theorem B2258189 : Blo 888571 2258189 := bbase (se 3 (by rfl) ⟨423410, by rfl⟩ : syracuseStep 2258189 = 846821) (by norm_num)
theorem B1504541 : Blo 888571 1504541 := bbase (se 3 (by rfl) ⟨282101, by rfl⟩ : syracuseStep 1504541 = 564203) (by norm_num)
theorem B3011957 : Blo 888571 3011957 := bbase (se 5 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 3011957 = 282371) (by norm_num)
theorem B1504669 : Blo 888571 1504669 := bbase (se 3 (by rfl) ⟨282125, by rfl⟩ : syracuseStep 1504669 = 564251) (by norm_num)
theorem B1602973 : Blo 888571 1602973 := bbase (se 3 (by rfl) ⟨300557, by rfl⟩ : syracuseStep 1602973 = 601115) (by norm_num)
theorem B2258381 : Blo 888571 2258381 := bbase (se 3 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 2258381 = 846893) (by norm_num)
theorem B1504757 : Blo 888571 1504757 := bbase (se 5 (by rfl) ⟨70535, by rfl⟩ : syracuseStep 1504757 = 141071) (by norm_num)
theorem B1504885 : Blo 888571 1504885 := bbase (se 5 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 1504885 = 141083) (by norm_num)
theorem B1504973 : Blo 888571 1504973 := bbase (se 3 (by rfl) ⟨282182, by rfl⟩ : syracuseStep 1504973 = 564365) (by norm_num)
theorem B2258725 : Blo 888571 2258725 := bbase (se 4 (by rfl) ⟨211755, by rfl⟩ : syracuseStep 2258725 = 423511) (by norm_num)
theorem B3012389 : Blo 888571 3012389 := bbase (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) (by norm_num)
theorem B1898309 : Blo 888571 1898309 := bbase (se 4 (by rfl) ⟨177966, by rfl⟩ : syracuseStep 1898309 = 355933) (by norm_num)
theorem B1505101 : Blo 888571 1505101 := bbase (se 3 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 1505101 = 564413) (by norm_num)
theorem B4061029 : Blo 888571 4061029 := bbase (se 4 (by rfl) ⟨380721, by rfl⟩ : syracuseStep 4061029 = 761443) (by norm_num)
theorem B2258837 : Blo 888571 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B1603493 : Blo 888571 1603493 := bbase (se 4 (by rfl) ⟨150327, by rfl⟩ : syracuseStep 1603493 = 300655) (by norm_num)
theorem B1505189 : Blo 888571 1505189 := bbase (se 4 (by rfl) ⟨141111, by rfl⟩ : syracuseStep 1505189 = 282223) (by norm_num)
theorem B5076917 : Blo 888571 5076917 := bbase (se 5 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 5076917 = 475961) (by norm_num)
theorem B1898453 : Blo 888571 1898453 := bbase (se 7 (by rfl) ⟨22247, by rfl⟩ : syracuseStep 1898453 = 44495) (by norm_num)
theorem B1505317 : Blo 888571 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B2259029 : Blo 888571 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B1505405 : Blo 888571 1505405 := bbase (se 3 (by rfl) ⟨282263, by rfl⟩ : syracuseStep 1505405 = 564527) (by norm_num)
theorem B1505533 : Blo 888571 1505533 := bbase (se 3 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 1505533 = 564575) (by norm_num)
theorem B1505621 : Blo 888571 1505621 := bbase (se 10 (by rfl) ⟨2205, by rfl⟩ : syracuseStep 1505621 = 4411) (by norm_num)
theorem B8550805 : Blo 888571 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B1505749 : Blo 888571 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B2849269 : Blo 888571 2849269 := bbase (se 5 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 2849269 = 267119) (by norm_num)
theorem B1505837 : Blo 888571 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B1014401 : Blo 888571 1014401 := bbase (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) (by norm_num)
theorem B948881 : Blo 888571 948881 := bbase (se 2 (by rfl) ⟨355830, by rfl⟩ : syracuseStep 948881 = 711661) (by norm_num)
theorem B1505965 : Blo 888571 1505965 := bbase (se 3 (by rfl) ⟨282368, by rfl⟩ : syracuseStep 1505965 = 564737) (by norm_num)
theorem B1899197 : Blo 888571 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B948953 : Blo 888571 948953 := bbase (se 2 (by rfl) ⟨355857, by rfl⟩ : syracuseStep 948953 = 711715) (by norm_num)
theorem B1506053 : Blo 888571 1506053 := bbase (se 4 (by rfl) ⟨141192, by rfl⟩ : syracuseStep 1506053 = 282385) (by norm_num)
theorem B1014601 : Blo 888571 1014601 := bbase (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) (by norm_num)
theorem B1506181 : Blo 888571 1506181 := bbase (se 4 (by rfl) ⟨141204, by rfl⟩ : syracuseStep 1506181 = 282409) (by norm_num)
theorem B949141 : Blo 888571 949141 := bbase (se 6 (by rfl) ⟨22245, by rfl⟩ : syracuseStep 949141 = 44491) (by norm_num)
theorem B949325 : Blo 888571 949325 := bbase (se 3 (by rfl) ⟨177998, by rfl⟩ : syracuseStep 949325 = 355997) (by norm_num)
theorem B7699637 : Blo 888571 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B3374405 : Blo 888571 3374405 := bbase (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) (by norm_num)
theorem B1899949 : Blo 888571 1899949 := bbase (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) (by norm_num)
theorem B3210677 : Blo 888571 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B2031101 : Blo 888571 2031101 := bbase (se 3 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 2031101 = 761663) (by norm_num)
theorem B1900093 : Blo 888571 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B3374693 : Blo 888571 3374693 := bbase (se 4 (by rfl) ⟨316377, by rfl⟩ : syracuseStep 3374693 = 632755) (by norm_num)
theorem B3210965 : Blo 888571 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B950077 : Blo 888571 950077 := bbase (se 3 (by rfl) ⟨178139, by rfl⟩ : syracuseStep 950077 = 356279) (by norm_num)
theorem B950149 : Blo 888571 950149 := bbase (se 4 (by rfl) ⟨89076, by rfl⟩ : syracuseStep 950149 = 178153) (by norm_num)
theorem B1900469 : Blo 888571 1900469 := bbase (se 5 (by rfl) ⟨89084, by rfl⟩ : syracuseStep 1900469 = 178169) (by norm_num)
theorem B19792069 : Blo 888571 19792069 := bstep (se 4 (by rfl) ⟨1855506, by rfl⟩ : syracuseStep 19792069 = 3711013) B3711013
theorem B21627107 : Blo 888571 21627107 := bstep (se 1 (by rfl) ⟨16220330, by rfl⟩ : syracuseStep 21627107 = 32440661) B32440661
theorem B1900913 : Blo 888571 1900913 := bstep (se 2 (by rfl) ⟨712842, by rfl⟩ : syracuseStep 1900913 = 1425685) B1425685
theorem B3801485 : Blo 888571 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B2032067 : Blo 888571 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B1999313 : Blo 888571 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B1999331 : Blo 888571 1999331 := bstep (se 1 (by rfl) ⟨1499498, by rfl⟩ : syracuseStep 1999331 = 2998997) B2998997
theorem B10125809 : Blo 888571 10125809 := bstep (se 2 (by rfl) ⟨3797178, by rfl⟩ : syracuseStep 10125809 = 7594357) B7594357
theorem B3375665 : Blo 888571 3375665 := bstep (se 2 (by rfl) ⟨1265874, by rfl⟩ : syracuseStep 3375665 = 2531749) B2531749
theorem B1606289 : Blo 888571 1606289 := bstep (se 2 (by rfl) ⟨602358, by rfl⟩ : syracuseStep 1606289 = 1204717) B1204717
theorem B1999601 : Blo 888571 1999601 := bstep (se 2 (by rfl) ⟨749850, by rfl⟩ : syracuseStep 1999601 = 1499701) B1499701
theorem B1999619 : Blo 888571 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B1999889 : Blo 888571 1999889 := bstep (se 2 (by rfl) ⟨749958, by rfl⟩ : syracuseStep 1999889 = 1499917) B1499917
theorem B1999907 : Blo 888571 1999907 := bstep (se 1 (by rfl) ⟨1499930, by rfl⟩ : syracuseStep 1999907 = 2999861) B2999861
theorem B2032771 : Blo 888571 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B2851985 : Blo 888571 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B2000177 : Blo 888571 2000177 := bstep (se 2 (by rfl) ⟨750066, by rfl⟩ : syracuseStep 2000177 = 1500133) B1500133
theorem B2000195 : Blo 888571 2000195 := bstep (se 1 (by rfl) ⟨1500146, by rfl⟩ : syracuseStep 2000195 = 3000293) B3000293
theorem B3606029 : Blo 888571 3606029 := bstep (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) B1352261
theorem B2000465 : Blo 888571 2000465 := bstep (se 2 (by rfl) ⟨750174, by rfl⟩ : syracuseStep 2000465 = 1500349) B1500349
theorem B2000483 : Blo 888571 2000483 := bstep (se 1 (by rfl) ⟨1500362, by rfl⟩ : syracuseStep 2000483 = 3000725) B3000725
theorem B5703331 : Blo 888571 5703331 := bstep (se 1 (by rfl) ⟨4277498, by rfl⟩ : syracuseStep 5703331 = 8554997) B8554997
theorem B952003 : Blo 888571 952003 := bstep (se 1 (by rfl) ⟨714002, by rfl⟩ : syracuseStep 952003 = 1428005) B1428005
theorem B11405069 : Blo 888571 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B2000753 : Blo 888571 2000753 := bstep (se 2 (by rfl) ⟨750282, by rfl⟩ : syracuseStep 2000753 = 1500565) B1500565
theorem B2000771 : Blo 888571 2000771 := bstep (se 1 (by rfl) ⟨1500578, by rfl⟩ : syracuseStep 2000771 = 3001157) B3001157
theorem B3803057 : Blo 888571 3803057 := bstep (se 2 (by rfl) ⟨1426146, by rfl⟩ : syracuseStep 3803057 = 2852293) B2852293
theorem B3377123 : Blo 888571 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B952435 : Blo 888571 952435 := bstep (se 1 (by rfl) ⟨714326, by rfl⟩ : syracuseStep 952435 = 1428653) B1428653
theorem B2001041 : Blo 888571 2001041 := bstep (se 2 (by rfl) ⟨750390, by rfl⟩ : syracuseStep 2001041 = 1500781) B1500781
theorem B2001059 : Blo 888571 2001059 := bstep (se 1 (by rfl) ⟨1500794, by rfl⟩ : syracuseStep 2001059 = 3001589) B3001589
theorem B1804465 : Blo 888571 1804465 := bstep (se 2 (by rfl) ⟨676674, by rfl⟩ : syracuseStep 1804465 = 1353349) B1353349
theorem B2033873 : Blo 888571 2033873 := bstep (se 2 (by rfl) ⟨762702, by rfl⟩ : syracuseStep 2033873 = 1525405) B1525405
theorem B6752483 : Blo 888571 6752483 := bstep (se 1 (by rfl) ⟨5064362, by rfl⟩ : syracuseStep 6752483 = 10128725) B10128725
theorem B1083619 : Blo 888571 1083619 := bstep (se 1 (by rfl) ⟨812714, by rfl⟩ : syracuseStep 1083619 = 1625429) B1625429
theorem B2001329 : Blo 888571 2001329 := bstep (se 2 (by rfl) ⟨750498, by rfl⟩ : syracuseStep 2001329 = 1500997) B1500997
theorem B2001347 : Blo 888571 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B2001617 : Blo 888571 2001617 := bstep (se 2 (by rfl) ⟨750606, by rfl⟩ : syracuseStep 2001617 = 1501213) B1501213
theorem B2001635 : Blo 888571 2001635 := bstep (se 1 (by rfl) ⟨1501226, by rfl⟩ : syracuseStep 2001635 = 3002453) B3002453
theorem B5147363 : Blo 888571 5147363 := bstep (se 1 (by rfl) ⟨3860522, by rfl⟩ : syracuseStep 5147363 = 7721045) B7721045
theorem B6097733 : Blo 888571 6097733 := bstep (se 4 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 6097733 = 1143325) B1143325
theorem B1444721 : Blo 888571 1444721 := bstep (se 2 (by rfl) ⟨541770, by rfl⟩ : syracuseStep 1444721 = 1083541) B1083541
theorem B3378125 : Blo 888571 3378125 := bstep (se 3 (by rfl) ⟨633398, by rfl⟩ : syracuseStep 3378125 = 1266797) B1266797
theorem B2001905 : Blo 888571 2001905 := bstep (se 2 (by rfl) ⟨750714, by rfl⟩ : syracuseStep 2001905 = 1501429) B1501429
theorem B2001923 : Blo 888571 2001923 := bstep (se 1 (by rfl) ⟨1501442, by rfl⟩ : syracuseStep 2001923 = 3002885) B3002885
theorem B5409841 : Blo 888571 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B2002193 : Blo 888571 2002193 := bstep (se 2 (by rfl) ⟨750822, by rfl⟩ : syracuseStep 2002193 = 1501645) B1501645
theorem B2002211 : Blo 888571 2002211 := bstep (se 1 (by rfl) ⟨1501658, by rfl⟩ : syracuseStep 2002211 = 3003317) B3003317
theorem B2854445 : Blo 888571 2854445 := bstep (se 3 (by rfl) ⟨535208, by rfl⟩ : syracuseStep 2854445 = 1070417) B1070417
theorem B2002481 : Blo 888571 2002481 := bstep (se 2 (by rfl) ⟨750930, by rfl⟩ : syracuseStep 2002481 = 1501861) B1501861
theorem B2002499 : Blo 888571 2002499 := bstep (se 1 (by rfl) ⟨1501874, by rfl⟩ : syracuseStep 2002499 = 3003749) B3003749
theorem B1904323 : Blo 888571 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B888579 : Blo 888571 888579 := bstep (se 1 (by rfl) ⟨666434, by rfl⟩ : syracuseStep 888579 = 1332869) B1332869
theorem B888595 : Blo 888571 888595 := bstep (se 1 (by rfl) ⟨666446, by rfl⟩ : syracuseStep 888595 = 1332893) B1332893
theorem B888611 : Blo 888571 888611 := bstep (se 1 (by rfl) ⟨666458, by rfl⟩ : syracuseStep 888611 = 1332917) B1332917
theorem B888627 : Blo 888571 888627 := bstep (se 1 (by rfl) ⟨666470, by rfl⟩ : syracuseStep 888627 = 1332941) B1332941
theorem B888643 : Blo 888571 888643 := bstep (se 1 (by rfl) ⟨666482, by rfl⟩ : syracuseStep 888643 = 1332965) B1332965
theorem B2002769 : Blo 888571 2002769 := bstep (se 2 (by rfl) ⟨751038, by rfl⟩ : syracuseStep 2002769 = 1502077) B1502077
theorem B888659 : Blo 888571 888659 := bstep (se 1 (by rfl) ⟨666494, by rfl⟩ : syracuseStep 888659 = 1332989) B1332989
theorem B888675 : Blo 888571 888675 := bstep (se 1 (by rfl) ⟨666506, by rfl⟩ : syracuseStep 888675 = 1333013) B1333013
theorem B2002787 : Blo 888571 2002787 := bstep (se 1 (by rfl) ⟨1502090, by rfl⟩ : syracuseStep 2002787 = 3004181) B3004181
theorem B888691 : Blo 888571 888691 := bstep (se 1 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 888691 = 1333037) B1333037
theorem B888707 : Blo 888571 888707 := bstep (se 1 (by rfl) ⟨666530, by rfl⟩ : syracuseStep 888707 = 1333061) B1333061
theorem B888723 : Blo 888571 888723 := bstep (se 1 (by rfl) ⟨666542, by rfl⟩ : syracuseStep 888723 = 1333085) B1333085
theorem B888739 : Blo 888571 888739 := bstep (se 1 (by rfl) ⟨666554, by rfl⟩ : syracuseStep 888739 = 1333109) B1333109
theorem B1806257 : Blo 888571 1806257 := bstep (se 2 (by rfl) ⟨677346, by rfl⟩ : syracuseStep 1806257 = 1354693) B1354693
theorem B888755 : Blo 888571 888755 := bstep (se 1 (by rfl) ⟨666566, by rfl⟩ : syracuseStep 888755 = 1333133) B1333133
theorem B888771 : Blo 888571 888771 := bstep (se 1 (by rfl) ⟨666578, by rfl⟩ : syracuseStep 888771 = 1333157) B1333157
theorem B888787 : Blo 888571 888787 := bstep (se 1 (by rfl) ⟨666590, by rfl⟩ : syracuseStep 888787 = 1333181) B1333181
theorem B888803 : Blo 888571 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B888819 : Blo 888571 888819 := bstep (se 1 (by rfl) ⟨666614, by rfl⟩ : syracuseStep 888819 = 1333229) B1333229
theorem B1544179 : Blo 888571 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B888835 : Blo 888571 888835 := bstep (se 1 (by rfl) ⟨666626, by rfl⟩ : syracuseStep 888835 = 1333253) B1333253
theorem B888851 : Blo 888571 888851 := bstep (se 1 (by rfl) ⟨666638, by rfl⟩ : syracuseStep 888851 = 1333277) B1333277
theorem B888867 : Blo 888571 888867 := bstep (se 1 (by rfl) ⟨666650, by rfl⟩ : syracuseStep 888867 = 1333301) B1333301
theorem B888883 : Blo 888571 888883 := bstep (se 1 (by rfl) ⟨666662, by rfl⟩ : syracuseStep 888883 = 1333325) B1333325
theorem B888899 : Blo 888571 888899 := bstep (se 1 (by rfl) ⟨666674, by rfl⟩ : syracuseStep 888899 = 1333349) B1333349
theorem B888915 : Blo 888571 888915 := bstep (se 1 (by rfl) ⟨666686, by rfl⟩ : syracuseStep 888915 = 1333373) B1333373
theorem B888931 : Blo 888571 888931 := bstep (se 1 (by rfl) ⟨666698, by rfl⟩ : syracuseStep 888931 = 1333397) B1333397
theorem B2003057 : Blo 888571 2003057 := bstep (se 2 (by rfl) ⟨751146, by rfl⟩ : syracuseStep 2003057 = 1502293) B1502293
theorem B888947 : Blo 888571 888947 := bstep (se 1 (by rfl) ⟨666710, by rfl⟩ : syracuseStep 888947 = 1333421) B1333421
theorem B888963 : Blo 888571 888963 := bstep (se 1 (by rfl) ⟨666722, by rfl⟩ : syracuseStep 888963 = 1333445) B1333445
theorem B2003075 : Blo 888571 2003075 := bstep (se 1 (by rfl) ⟨1502306, by rfl⟩ : syracuseStep 2003075 = 3004613) B3004613
theorem B888979 : Blo 888571 888979 := bstep (se 1 (by rfl) ⟨666734, by rfl⟩ : syracuseStep 888979 = 1333469) B1333469
theorem B888995 : Blo 888571 888995 := bstep (se 1 (by rfl) ⟨666746, by rfl⟩ : syracuseStep 888995 = 1333493) B1333493
theorem B889011 : Blo 888571 889011 := bstep (se 1 (by rfl) ⟨666758, by rfl⟩ : syracuseStep 889011 = 1333517) B1333517
theorem B889027 : Blo 888571 889027 := bstep (se 1 (by rfl) ⟨666770, by rfl⟩ : syracuseStep 889027 = 1333541) B1333541
theorem B889043 : Blo 888571 889043 := bstep (se 1 (by rfl) ⟨666782, by rfl⟩ : syracuseStep 889043 = 1333565) B1333565
theorem B889059 : Blo 888571 889059 := bstep (se 1 (by rfl) ⟨666794, by rfl⟩ : syracuseStep 889059 = 1333589) B1333589
theorem B889075 : Blo 888571 889075 := bstep (se 1 (by rfl) ⟨666806, by rfl⟩ : syracuseStep 889075 = 1333613) B1333613
theorem B889091 : Blo 888571 889091 := bstep (se 1 (by rfl) ⟨666818, by rfl⟩ : syracuseStep 889091 = 1333637) B1333637
theorem B889107 : Blo 888571 889107 := bstep (se 1 (by rfl) ⟨666830, by rfl⟩ : syracuseStep 889107 = 1333661) B1333661
theorem B889123 : Blo 888571 889123 := bstep (se 1 (by rfl) ⟨666842, by rfl⟩ : syracuseStep 889123 = 1333685) B1333685
theorem B889139 : Blo 888571 889139 := bstep (se 1 (by rfl) ⟨666854, by rfl⟩ : syracuseStep 889139 = 1333709) B1333709
theorem B889155 : Blo 888571 889155 := bstep (se 1 (by rfl) ⟨666866, by rfl⟩ : syracuseStep 889155 = 1333733) B1333733
theorem B3805517 : Blo 888571 3805517 := bstep (se 3 (by rfl) ⟨713534, by rfl⟩ : syracuseStep 3805517 = 1427069) B1427069
theorem B889171 : Blo 888571 889171 := bstep (se 1 (by rfl) ⟨666878, by rfl⟩ : syracuseStep 889171 = 1333757) B1333757
theorem B889187 : Blo 888571 889187 := bstep (se 1 (by rfl) ⟨666890, by rfl⟩ : syracuseStep 889187 = 1333781) B1333781
theorem B889203 : Blo 888571 889203 := bstep (se 1 (by rfl) ⟨666902, by rfl⟩ : syracuseStep 889203 = 1333805) B1333805
theorem B889219 : Blo 888571 889219 := bstep (se 1 (by rfl) ⟨666914, by rfl⟩ : syracuseStep 889219 = 1333829) B1333829
theorem B5706125 : Blo 888571 5706125 := bstep (se 3 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 5706125 = 2139797) B2139797
theorem B2003345 : Blo 888571 2003345 := bstep (se 2 (by rfl) ⟨751254, by rfl⟩ : syracuseStep 2003345 = 1502509) B1502509
theorem B889235 : Blo 888571 889235 := bstep (se 1 (by rfl) ⟨666926, by rfl⟩ : syracuseStep 889235 = 1333853) B1333853
theorem B889251 : Blo 888571 889251 := bstep (se 1 (by rfl) ⟨666938, by rfl⟩ : syracuseStep 889251 = 1333877) B1333877
theorem B2003363 : Blo 888571 2003363 := bstep (se 1 (by rfl) ⟨1502522, by rfl⟩ : syracuseStep 2003363 = 3005045) B3005045
theorem B889267 : Blo 888571 889267 := bstep (se 1 (by rfl) ⟨666950, by rfl⟩ : syracuseStep 889267 = 1333901) B1333901
theorem B889283 : Blo 888571 889283 := bstep (se 1 (by rfl) ⟨666962, by rfl⟩ : syracuseStep 889283 = 1333925) B1333925
theorem B889299 : Blo 888571 889299 := bstep (se 1 (by rfl) ⟨666974, by rfl⟩ : syracuseStep 889299 = 1333949) B1333949
theorem B889315 : Blo 888571 889315 := bstep (se 1 (by rfl) ⟨666986, by rfl⟩ : syracuseStep 889315 = 1333973) B1333973
theorem B889331 : Blo 888571 889331 := bstep (se 1 (by rfl) ⟨666998, by rfl⟩ : syracuseStep 889331 = 1333997) B1333997
theorem B889347 : Blo 888571 889347 := bstep (se 1 (by rfl) ⟨667010, by rfl⟩ : syracuseStep 889347 = 1334021) B1334021
theorem B889363 : Blo 888571 889363 := bstep (se 1 (by rfl) ⟨667022, by rfl⟩ : syracuseStep 889363 = 1334045) B1334045
theorem B889379 : Blo 888571 889379 := bstep (se 1 (by rfl) ⟨667034, by rfl⟩ : syracuseStep 889379 = 1334069) B1334069
theorem B889395 : Blo 888571 889395 := bstep (se 1 (by rfl) ⟨667046, by rfl⟩ : syracuseStep 889395 = 1334093) B1334093
theorem B889411 : Blo 888571 889411 := bstep (se 1 (by rfl) ⟨667058, by rfl⟩ : syracuseStep 889411 = 1334117) B1334117
theorem B889427 : Blo 888571 889427 := bstep (se 1 (by rfl) ⟨667070, by rfl⟩ : syracuseStep 889427 = 1334141) B1334141
theorem B889443 : Blo 888571 889443 := bstep (se 1 (by rfl) ⟨667082, by rfl⟩ : syracuseStep 889443 = 1334165) B1334165
theorem B889459 : Blo 888571 889459 := bstep (se 1 (by rfl) ⟨667094, by rfl⟩ : syracuseStep 889459 = 1334189) B1334189
theorem B889475 : Blo 888571 889475 := bstep (se 1 (by rfl) ⟨667106, by rfl⟩ : syracuseStep 889475 = 1334213) B1334213
theorem B889491 : Blo 888571 889491 := bstep (se 1 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 889491 = 1334237) B1334237
theorem B889507 : Blo 888571 889507 := bstep (se 1 (by rfl) ⟨667130, by rfl⟩ : syracuseStep 889507 = 1334261) B1334261
theorem B3805859 : Blo 888571 3805859 := bstep (se 1 (by rfl) ⟨2854394, by rfl⟩ : syracuseStep 3805859 = 5708789) B5708789
theorem B2003633 : Blo 888571 2003633 := bstep (se 2 (by rfl) ⟨751362, by rfl⟩ : syracuseStep 2003633 = 1502725) B1502725
theorem B889523 : Blo 888571 889523 := bstep (se 1 (by rfl) ⟨667142, by rfl⟩ : syracuseStep 889523 = 1334285) B1334285
theorem B889539 : Blo 888571 889539 := bstep (se 1 (by rfl) ⟨667154, by rfl⟩ : syracuseStep 889539 = 1334309) B1334309
theorem B2003651 : Blo 888571 2003651 := bstep (se 1 (by rfl) ⟨1502738, by rfl⟩ : syracuseStep 2003651 = 3005477) B3005477
theorem B1807043 : Blo 888571 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B889555 : Blo 888571 889555 := bstep (se 1 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 889555 = 1334333) B1334333
theorem B889571 : Blo 888571 889571 := bstep (se 1 (by rfl) ⟨667178, by rfl⟩ : syracuseStep 889571 = 1334357) B1334357
theorem B889587 : Blo 888571 889587 := bstep (se 1 (by rfl) ⟨667190, by rfl⟩ : syracuseStep 889587 = 1334381) B1334381
theorem B889603 : Blo 888571 889603 := bstep (se 1 (by rfl) ⟨667202, by rfl⟩ : syracuseStep 889603 = 1334405) B1334405
theorem B889619 : Blo 888571 889619 := bstep (se 1 (by rfl) ⟨667214, by rfl⟩ : syracuseStep 889619 = 1334429) B1334429
theorem B889635 : Blo 888571 889635 := bstep (se 1 (by rfl) ⟨667226, by rfl⟩ : syracuseStep 889635 = 1334453) B1334453
theorem B889651 : Blo 888571 889651 := bstep (se 1 (by rfl) ⟨667238, by rfl⟩ : syracuseStep 889651 = 1334477) B1334477
theorem B889667 : Blo 888571 889667 := bstep (se 1 (by rfl) ⟨667250, by rfl⟩ : syracuseStep 889667 = 1334501) B1334501
theorem B889683 : Blo 888571 889683 := bstep (se 1 (by rfl) ⟨667262, by rfl⟩ : syracuseStep 889683 = 1334525) B1334525
theorem B889699 : Blo 888571 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B889715 : Blo 888571 889715 := bstep (se 1 (by rfl) ⟨667286, by rfl⟩ : syracuseStep 889715 = 1334573) B1334573
theorem B889731 : Blo 888571 889731 := bstep (se 1 (by rfl) ⟨667298, by rfl⟩ : syracuseStep 889731 = 1334597) B1334597
theorem B3216269 : Blo 888571 3216269 := bstep (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) B1206101
theorem B889747 : Blo 888571 889747 := bstep (se 1 (by rfl) ⟨667310, by rfl⟩ : syracuseStep 889747 = 1334621) B1334621
theorem B889763 : Blo 888571 889763 := bstep (se 1 (by rfl) ⟨667322, by rfl⟩ : syracuseStep 889763 = 1334645) B1334645
theorem B889779 : Blo 888571 889779 := bstep (se 1 (by rfl) ⟨667334, by rfl⟩ : syracuseStep 889779 = 1334669) B1334669
theorem B889795 : Blo 888571 889795 := bstep (se 1 (by rfl) ⟨667346, by rfl⟩ : syracuseStep 889795 = 1334693) B1334693
theorem B2003921 : Blo 888571 2003921 := bstep (se 2 (by rfl) ⟨751470, by rfl⟩ : syracuseStep 2003921 = 1502941) B1502941
theorem B889811 : Blo 888571 889811 := bstep (se 1 (by rfl) ⟨667358, by rfl⟩ : syracuseStep 889811 = 1334717) B1334717
theorem B889827 : Blo 888571 889827 := bstep (se 1 (by rfl) ⟨667370, by rfl⟩ : syracuseStep 889827 = 1334741) B1334741
theorem B2003939 : Blo 888571 2003939 := bstep (se 1 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 2003939 = 3005909) B3005909
theorem B889843 : Blo 888571 889843 := bstep (se 1 (by rfl) ⟨667382, by rfl⟩ : syracuseStep 889843 = 1334765) B1334765
theorem B889859 : Blo 888571 889859 := bstep (se 1 (by rfl) ⟨667394, by rfl⟩ : syracuseStep 889859 = 1334789) B1334789
theorem B3380237 : Blo 888571 3380237 := bstep (se 3 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 3380237 = 1267589) B1267589
theorem B889875 : Blo 888571 889875 := bstep (se 1 (by rfl) ⟨667406, by rfl⟩ : syracuseStep 889875 = 1334813) B1334813
theorem B889891 : Blo 888571 889891 := bstep (se 1 (by rfl) ⟨667418, by rfl⟩ : syracuseStep 889891 = 1334837) B1334837
theorem B889907 : Blo 888571 889907 := bstep (se 1 (by rfl) ⟨667430, by rfl⟩ : syracuseStep 889907 = 1334861) B1334861
theorem B889923 : Blo 888571 889923 := bstep (se 1 (by rfl) ⟨667442, by rfl⟩ : syracuseStep 889923 = 1334885) B1334885
theorem B889939 : Blo 888571 889939 := bstep (se 1 (by rfl) ⟨667454, by rfl⟩ : syracuseStep 889939 = 1334909) B1334909
theorem B889955 : Blo 888571 889955 := bstep (se 1 (by rfl) ⟨667466, by rfl⟩ : syracuseStep 889955 = 1334933) B1334933
theorem B2856035 : Blo 888571 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B889971 : Blo 888571 889971 := bstep (se 1 (by rfl) ⟨667478, by rfl⟩ : syracuseStep 889971 = 1334957) B1334957
theorem B889987 : Blo 888571 889987 := bstep (se 1 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 889987 = 1334981) B1334981
theorem B890003 : Blo 888571 890003 := bstep (se 1 (by rfl) ⟨667502, by rfl⟩ : syracuseStep 890003 = 1335005) B1335005
theorem B890019 : Blo 888571 890019 := bstep (se 1 (by rfl) ⟨667514, by rfl⟩ : syracuseStep 890019 = 1335029) B1335029
theorem B890035 : Blo 888571 890035 := bstep (se 1 (by rfl) ⟨667526, by rfl⟩ : syracuseStep 890035 = 1335053) B1335053
theorem B890051 : Blo 888571 890051 := bstep (se 1 (by rfl) ⟨667538, by rfl⟩ : syracuseStep 890051 = 1335077) B1335077
theorem B890067 : Blo 888571 890067 := bstep (se 1 (by rfl) ⟨667550, by rfl⟩ : syracuseStep 890067 = 1335101) B1335101
theorem B890083 : Blo 888571 890083 := bstep (se 1 (by rfl) ⟨667562, by rfl⟩ : syracuseStep 890083 = 1335125) B1335125
theorem B2004209 : Blo 888571 2004209 := bstep (se 2 (by rfl) ⟨751578, by rfl⟩ : syracuseStep 2004209 = 1503157) B1503157
theorem B890099 : Blo 888571 890099 := bstep (se 1 (by rfl) ⟨667574, by rfl⟩ : syracuseStep 890099 = 1335149) B1335149
theorem B890115 : Blo 888571 890115 := bstep (se 1 (by rfl) ⟨667586, by rfl⟩ : syracuseStep 890115 = 1335173) B1335173
theorem B2004227 : Blo 888571 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B890131 : Blo 888571 890131 := bstep (se 1 (by rfl) ⟨667598, by rfl⟩ : syracuseStep 890131 = 1335197) B1335197
theorem B890147 : Blo 888571 890147 := bstep (se 1 (by rfl) ⟨667610, by rfl⟩ : syracuseStep 890147 = 1335221) B1335221
theorem B890163 : Blo 888571 890163 := bstep (se 1 (by rfl) ⟨667622, by rfl⟩ : syracuseStep 890163 = 1335245) B1335245
theorem B890179 : Blo 888571 890179 := bstep (se 1 (by rfl) ⟨667634, by rfl⟩ : syracuseStep 890179 = 1335269) B1335269
theorem B890195 : Blo 888571 890195 := bstep (se 1 (by rfl) ⟨667646, by rfl⟩ : syracuseStep 890195 = 1335293) B1335293
theorem B890211 : Blo 888571 890211 := bstep (se 1 (by rfl) ⟨667658, by rfl⟩ : syracuseStep 890211 = 1335317) B1335317
theorem B890227 : Blo 888571 890227 := bstep (se 1 (by rfl) ⟨667670, by rfl⟩ : syracuseStep 890227 = 1335341) B1335341
theorem B890243 : Blo 888571 890243 := bstep (se 1 (by rfl) ⟨667682, by rfl⟩ : syracuseStep 890243 = 1335365) B1335365
theorem B890259 : Blo 888571 890259 := bstep (se 1 (by rfl) ⟨667694, by rfl⟩ : syracuseStep 890259 = 1335389) B1335389
theorem B890275 : Blo 888571 890275 := bstep (se 1 (by rfl) ⟨667706, by rfl⟩ : syracuseStep 890275 = 1335413) B1335413
theorem B890291 : Blo 888571 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B890307 : Blo 888571 890307 := bstep (se 1 (by rfl) ⟨667730, by rfl⟩ : syracuseStep 890307 = 1335461) B1335461
theorem B890323 : Blo 888571 890323 := bstep (se 1 (by rfl) ⟨667742, by rfl⟩ : syracuseStep 890323 = 1335485) B1335485
theorem B890339 : Blo 888571 890339 := bstep (se 1 (by rfl) ⟨667754, by rfl⟩ : syracuseStep 890339 = 1335509) B1335509
theorem B890355 : Blo 888571 890355 := bstep (se 1 (by rfl) ⟨667766, by rfl⟩ : syracuseStep 890355 = 1335533) B1335533
theorem B890371 : Blo 888571 890371 := bstep (se 1 (by rfl) ⟨667778, by rfl⟩ : syracuseStep 890371 = 1335557) B1335557
theorem B2004497 : Blo 888571 2004497 := bstep (se 2 (by rfl) ⟨751686, by rfl⟩ : syracuseStep 2004497 = 1503373) B1503373
theorem B1906193 : Blo 888571 1906193 := bstep (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) B1429645
theorem B890387 : Blo 888571 890387 := bstep (se 1 (by rfl) ⟨667790, by rfl⟩ : syracuseStep 890387 = 1335581) B1335581
theorem B890403 : Blo 888571 890403 := bstep (se 1 (by rfl) ⟨667802, by rfl⟩ : syracuseStep 890403 = 1335605) B1335605
theorem B2004515 : Blo 888571 2004515 := bstep (se 1 (by rfl) ⟨1503386, by rfl⟩ : syracuseStep 2004515 = 3006773) B3006773
theorem B890419 : Blo 888571 890419 := bstep (se 1 (by rfl) ⟨667814, by rfl⟩ : syracuseStep 890419 = 1335629) B1335629
theorem B890435 : Blo 888571 890435 := bstep (se 1 (by rfl) ⟨667826, by rfl⟩ : syracuseStep 890435 = 1335653) B1335653
theorem B890451 : Blo 888571 890451 := bstep (se 1 (by rfl) ⟨667838, by rfl⟩ : syracuseStep 890451 = 1335677) B1335677
theorem B890467 : Blo 888571 890467 := bstep (se 1 (by rfl) ⟨667850, by rfl⟩ : syracuseStep 890467 = 1335701) B1335701
theorem B890483 : Blo 888571 890483 := bstep (se 1 (by rfl) ⟨667862, by rfl⟩ : syracuseStep 890483 = 1335725) B1335725
theorem B2135683 : Blo 888571 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B890499 : Blo 888571 890499 := bstep (se 1 (by rfl) ⟨667874, by rfl⟩ : syracuseStep 890499 = 1335749) B1335749
theorem B890515 : Blo 888571 890515 := bstep (se 1 (by rfl) ⟨667886, by rfl⟩ : syracuseStep 890515 = 1335773) B1335773
theorem B890531 : Blo 888571 890531 := bstep (se 1 (by rfl) ⟨667898, by rfl⟩ : syracuseStep 890531 = 1335797) B1335797
theorem B890547 : Blo 888571 890547 := bstep (se 1 (by rfl) ⟨667910, by rfl⟩ : syracuseStep 890547 = 1335821) B1335821
theorem B890563 : Blo 888571 890563 := bstep (se 1 (by rfl) ⟨667922, by rfl⟩ : syracuseStep 890563 = 1335845) B1335845
theorem B890579 : Blo 888571 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B890595 : Blo 888571 890595 := bstep (se 1 (by rfl) ⟨667946, by rfl⟩ : syracuseStep 890595 = 1335893) B1335893
theorem B34248419 : Blo 888571 34248419 := bstep (se 1 (by rfl) ⟨25686314, by rfl⟩ : syracuseStep 34248419 = 51372629) B51372629
theorem B890611 : Blo 888571 890611 := bstep (se 1 (by rfl) ⟨667958, by rfl⟩ : syracuseStep 890611 = 1335917) B1335917
theorem B890627 : Blo 888571 890627 := bstep (se 1 (by rfl) ⟨667970, by rfl⟩ : syracuseStep 890627 = 1335941) B1335941
theorem B890643 : Blo 888571 890643 := bstep (se 1 (by rfl) ⟨667982, by rfl⟩ : syracuseStep 890643 = 1335965) B1335965
theorem B890659 : Blo 888571 890659 := bstep (se 1 (by rfl) ⟨667994, by rfl⟩ : syracuseStep 890659 = 1335989) B1335989
theorem B3381041 : Blo 888571 3381041 := bstep (se 2 (by rfl) ⟨1267890, by rfl⟩ : syracuseStep 3381041 = 2535781) B2535781
theorem B2004785 : Blo 888571 2004785 := bstep (se 2 (by rfl) ⟨751794, by rfl⟩ : syracuseStep 2004785 = 1503589) B1503589
theorem B890675 : Blo 888571 890675 := bstep (se 1 (by rfl) ⟨668006, by rfl⟩ : syracuseStep 890675 = 1336013) B1336013
theorem B890691 : Blo 888571 890691 := bstep (se 1 (by rfl) ⟨668018, by rfl⟩ : syracuseStep 890691 = 1336037) B1336037
theorem B2004803 : Blo 888571 2004803 := bstep (se 1 (by rfl) ⟨1503602, by rfl⟩ : syracuseStep 2004803 = 3007205) B3007205
theorem B890707 : Blo 888571 890707 := bstep (se 1 (by rfl) ⟨668030, by rfl⟩ : syracuseStep 890707 = 1336061) B1336061
theorem B890723 : Blo 888571 890723 := bstep (se 1 (by rfl) ⟨668042, by rfl⟩ : syracuseStep 890723 = 1336085) B1336085
theorem B890739 : Blo 888571 890739 := bstep (se 1 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 890739 = 1336109) B1336109
theorem B890755 : Blo 888571 890755 := bstep (se 1 (by rfl) ⟨668066, by rfl⟩ : syracuseStep 890755 = 1336133) B1336133
theorem B890771 : Blo 888571 890771 := bstep (se 1 (by rfl) ⟨668078, by rfl⟩ : syracuseStep 890771 = 1336157) B1336157
theorem B890787 : Blo 888571 890787 := bstep (se 1 (by rfl) ⟨668090, by rfl⟩ : syracuseStep 890787 = 1336181) B1336181
theorem B5150627 : Blo 888571 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B890803 : Blo 888571 890803 := bstep (se 1 (by rfl) ⟨668102, by rfl⟩ : syracuseStep 890803 = 1336205) B1336205
theorem B890819 : Blo 888571 890819 := bstep (se 1 (by rfl) ⟨668114, by rfl⟩ : syracuseStep 890819 = 1336229) B1336229
theorem B890835 : Blo 888571 890835 := bstep (se 1 (by rfl) ⟨668126, by rfl⟩ : syracuseStep 890835 = 1336253) B1336253
theorem B890851 : Blo 888571 890851 := bstep (se 1 (by rfl) ⟨668138, by rfl⟩ : syracuseStep 890851 = 1336277) B1336277
theorem B890867 : Blo 888571 890867 := bstep (se 1 (by rfl) ⟨668150, by rfl⟩ : syracuseStep 890867 = 1336301) B1336301
theorem B890883 : Blo 888571 890883 := bstep (se 1 (by rfl) ⟨668162, by rfl⟩ : syracuseStep 890883 = 1336325) B1336325
theorem B890899 : Blo 888571 890899 := bstep (se 1 (by rfl) ⟨668174, by rfl⟩ : syracuseStep 890899 = 1336349) B1336349
theorem B890915 : Blo 888571 890915 := bstep (se 1 (by rfl) ⟨668186, by rfl⟩ : syracuseStep 890915 = 1336373) B1336373
theorem B890931 : Blo 888571 890931 := bstep (se 1 (by rfl) ⟨668198, by rfl⟩ : syracuseStep 890931 = 1336397) B1336397
theorem B890947 : Blo 888571 890947 := bstep (se 1 (by rfl) ⟨668210, by rfl⟩ : syracuseStep 890947 = 1336421) B1336421
theorem B2136145 : Blo 888571 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B2005073 : Blo 888571 2005073 := bstep (se 2 (by rfl) ⟨751902, by rfl⟩ : syracuseStep 2005073 = 1503805) B1503805
theorem B890963 : Blo 888571 890963 := bstep (se 1 (by rfl) ⟨668222, by rfl⟩ : syracuseStep 890963 = 1336445) B1336445
theorem B890979 : Blo 888571 890979 := bstep (se 1 (by rfl) ⟨668234, by rfl⟩ : syracuseStep 890979 = 1336469) B1336469
theorem B2005091 : Blo 888571 2005091 := bstep (se 1 (by rfl) ⟨1503818, by rfl⟩ : syracuseStep 2005091 = 3007637) B3007637
theorem B890995 : Blo 888571 890995 := bstep (se 1 (by rfl) ⟨668246, by rfl⟩ : syracuseStep 890995 = 1336493) B1336493
theorem B891011 : Blo 888571 891011 := bstep (se 1 (by rfl) ⟨668258, by rfl⟩ : syracuseStep 891011 = 1336517) B1336517
theorem B891027 : Blo 888571 891027 := bstep (se 1 (by rfl) ⟨668270, by rfl⟩ : syracuseStep 891027 = 1336541) B1336541
theorem B891043 : Blo 888571 891043 := bstep (se 1 (by rfl) ⟨668282, by rfl⟩ : syracuseStep 891043 = 1336565) B1336565
theorem B1448099 : Blo 888571 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B891059 : Blo 888571 891059 := bstep (se 1 (by rfl) ⟨668294, by rfl⟩ : syracuseStep 891059 = 1336589) B1336589
theorem B891075 : Blo 888571 891075 := bstep (se 1 (by rfl) ⟨668306, by rfl⟩ : syracuseStep 891075 = 1336613) B1336613
theorem B891091 : Blo 888571 891091 := bstep (se 1 (by rfl) ⟨668318, by rfl⟩ : syracuseStep 891091 = 1336637) B1336637
theorem B25663715 : Blo 888571 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B891107 : Blo 888571 891107 := bstep (se 1 (by rfl) ⟨668330, by rfl⟩ : syracuseStep 891107 = 1336661) B1336661
theorem B891123 : Blo 888571 891123 := bstep (se 1 (by rfl) ⟨668342, by rfl⟩ : syracuseStep 891123 = 1336685) B1336685
theorem B891139 : Blo 888571 891139 := bstep (se 1 (by rfl) ⟨668354, by rfl⟩ : syracuseStep 891139 = 1336709) B1336709
theorem B891155 : Blo 888571 891155 := bstep (se 1 (by rfl) ⟨668366, by rfl⟩ : syracuseStep 891155 = 1336733) B1336733
theorem B891171 : Blo 888571 891171 := bstep (se 1 (by rfl) ⟨668378, by rfl⟩ : syracuseStep 891171 = 1336757) B1336757
theorem B2857265 : Blo 888571 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B891187 : Blo 888571 891187 := bstep (se 1 (by rfl) ⟨668390, by rfl⟩ : syracuseStep 891187 = 1336781) B1336781
theorem B891203 : Blo 888571 891203 := bstep (se 1 (by rfl) ⟨668402, by rfl⟩ : syracuseStep 891203 = 1336805) B1336805
theorem B891219 : Blo 888571 891219 := bstep (se 1 (by rfl) ⟨668414, by rfl⟩ : syracuseStep 891219 = 1336829) B1336829
theorem B891235 : Blo 888571 891235 := bstep (se 1 (by rfl) ⟨668426, by rfl⟩ : syracuseStep 891235 = 1336853) B1336853
theorem B2005361 : Blo 888571 2005361 := bstep (se 2 (by rfl) ⟨752010, by rfl⟩ : syracuseStep 2005361 = 1504021) B1504021
theorem B891251 : Blo 888571 891251 := bstep (se 1 (by rfl) ⟨668438, by rfl⟩ : syracuseStep 891251 = 1336877) B1336877
theorem B891267 : Blo 888571 891267 := bstep (se 1 (by rfl) ⟨668450, by rfl⟩ : syracuseStep 891267 = 1336901) B1336901
theorem B2005379 : Blo 888571 2005379 := bstep (se 1 (by rfl) ⟨1504034, by rfl⟩ : syracuseStep 2005379 = 3008069) B3008069
theorem B891283 : Blo 888571 891283 := bstep (se 1 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 891283 = 1336925) B1336925
theorem B891299 : Blo 888571 891299 := bstep (se 1 (by rfl) ⟨668474, by rfl⟩ : syracuseStep 891299 = 1336949) B1336949
theorem B891315 : Blo 888571 891315 := bstep (se 1 (by rfl) ⟨668486, by rfl⟩ : syracuseStep 891315 = 1336973) B1336973
theorem B891331 : Blo 888571 891331 := bstep (se 1 (by rfl) ⟨668498, by rfl⟩ : syracuseStep 891331 = 1336997) B1336997
theorem B3381709 : Blo 888571 3381709 := bstep (se 3 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 3381709 = 1268141) B1268141
theorem B891347 : Blo 888571 891347 := bstep (se 1 (by rfl) ⟨668510, by rfl⟩ : syracuseStep 891347 = 1337021) B1337021
theorem B891363 : Blo 888571 891363 := bstep (se 1 (by rfl) ⟨668522, by rfl⟩ : syracuseStep 891363 = 1337045) B1337045
theorem B891379 : Blo 888571 891379 := bstep (se 1 (by rfl) ⟨668534, by rfl⟩ : syracuseStep 891379 = 1337069) B1337069
theorem B891395 : Blo 888571 891395 := bstep (se 1 (by rfl) ⟨668546, by rfl⟩ : syracuseStep 891395 = 1337093) B1337093
theorem B891411 : Blo 888571 891411 := bstep (se 1 (by rfl) ⟨668558, by rfl⟩ : syracuseStep 891411 = 1337117) B1337117
theorem B891427 : Blo 888571 891427 := bstep (se 1 (by rfl) ⟨668570, by rfl⟩ : syracuseStep 891427 = 1337141) B1337141
theorem B891443 : Blo 888571 891443 := bstep (se 1 (by rfl) ⟨668582, by rfl⟩ : syracuseStep 891443 = 1337165) B1337165
theorem B891459 : Blo 888571 891459 := bstep (se 1 (by rfl) ⟨668594, by rfl⟩ : syracuseStep 891459 = 1337189) B1337189
theorem B891475 : Blo 888571 891475 := bstep (se 1 (by rfl) ⟨668606, by rfl⟩ : syracuseStep 891475 = 1337213) B1337213
theorem B891491 : Blo 888571 891491 := bstep (se 1 (by rfl) ⟨668618, by rfl⟩ : syracuseStep 891491 = 1337237) B1337237
theorem B891507 : Blo 888571 891507 := bstep (se 1 (by rfl) ⟨668630, by rfl⟩ : syracuseStep 891507 = 1337261) B1337261
theorem B891523 : Blo 888571 891523 := bstep (se 1 (by rfl) ⟨668642, by rfl⟩ : syracuseStep 891523 = 1337285) B1337285
theorem B2005649 : Blo 888571 2005649 := bstep (se 2 (by rfl) ⟨752118, by rfl⟩ : syracuseStep 2005649 = 1504237) B1504237
theorem B891539 : Blo 888571 891539 := bstep (se 1 (by rfl) ⟨668654, by rfl⟩ : syracuseStep 891539 = 1337309) B1337309
theorem B2005667 : Blo 888571 2005667 := bstep (se 1 (by rfl) ⟨1504250, by rfl⟩ : syracuseStep 2005667 = 3008501) B3008501
theorem B891555 : Blo 888571 891555 := bstep (se 1 (by rfl) ⟨668666, by rfl⟩ : syracuseStep 891555 = 1337333) B1337333
theorem B891571 : Blo 888571 891571 := bstep (se 1 (by rfl) ⟨668678, by rfl⟩ : syracuseStep 891571 = 1337357) B1337357
theorem B891587 : Blo 888571 891587 := bstep (se 1 (by rfl) ⟨668690, by rfl⟩ : syracuseStep 891587 = 1337381) B1337381
theorem B891603 : Blo 888571 891603 := bstep (se 1 (by rfl) ⟨668702, by rfl⟩ : syracuseStep 891603 = 1337405) B1337405
theorem B891619 : Blo 888571 891619 := bstep (se 1 (by rfl) ⟨668714, by rfl⟩ : syracuseStep 891619 = 1337429) B1337429
theorem B891635 : Blo 888571 891635 := bstep (se 1 (by rfl) ⟨668726, by rfl⟩ : syracuseStep 891635 = 1337453) B1337453
theorem B891651 : Blo 888571 891651 := bstep (se 1 (by rfl) ⟨668738, by rfl⟩ : syracuseStep 891651 = 1337477) B1337477
theorem B891667 : Blo 888571 891667 := bstep (se 1 (by rfl) ⟨668750, by rfl⟩ : syracuseStep 891667 = 1337501) B1337501
theorem B891683 : Blo 888571 891683 := bstep (se 1 (by rfl) ⟨668762, by rfl⟩ : syracuseStep 891683 = 1337525) B1337525
theorem B891699 : Blo 888571 891699 := bstep (se 1 (by rfl) ⟨668774, by rfl⟩ : syracuseStep 891699 = 1337549) B1337549
theorem B891715 : Blo 888571 891715 := bstep (se 1 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 891715 = 1337573) B1337573
theorem B891731 : Blo 888571 891731 := bstep (se 1 (by rfl) ⟨668798, by rfl⟩ : syracuseStep 891731 = 1337597) B1337597
theorem B891747 : Blo 888571 891747 := bstep (se 1 (by rfl) ⟨668810, by rfl⟩ : syracuseStep 891747 = 1337621) B1337621
theorem B891763 : Blo 888571 891763 := bstep (se 1 (by rfl) ⟨668822, by rfl⟩ : syracuseStep 891763 = 1337645) B1337645
theorem B891779 : Blo 888571 891779 := bstep (se 1 (by rfl) ⟨668834, by rfl⟩ : syracuseStep 891779 = 1337669) B1337669
theorem B891795 : Blo 888571 891795 := bstep (se 1 (by rfl) ⟨668846, by rfl⟩ : syracuseStep 891795 = 1337693) B1337693
theorem B891811 : Blo 888571 891811 := bstep (se 1 (by rfl) ⟨668858, by rfl⟩ : syracuseStep 891811 = 1337717) B1337717
theorem B2005937 : Blo 888571 2005937 := bstep (se 2 (by rfl) ⟨752226, by rfl⟩ : syracuseStep 2005937 = 1504453) B1504453
theorem B891827 : Blo 888571 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B2005955 : Blo 888571 2005955 := bstep (se 1 (by rfl) ⟨1504466, by rfl⟩ : syracuseStep 2005955 = 3008933) B3008933
theorem B891843 : Blo 888571 891843 := bstep (se 1 (by rfl) ⟨668882, by rfl⟩ : syracuseStep 891843 = 1337765) B1337765
theorem B891859 : Blo 888571 891859 := bstep (se 1 (by rfl) ⟨668894, by rfl⟩ : syracuseStep 891859 = 1337789) B1337789
theorem B891875 : Blo 888571 891875 := bstep (se 1 (by rfl) ⟨668906, by rfl⟩ : syracuseStep 891875 = 1337813) B1337813
theorem B891891 : Blo 888571 891891 := bstep (se 1 (by rfl) ⟨668918, by rfl⟩ : syracuseStep 891891 = 1337837) B1337837
theorem B891907 : Blo 888571 891907 := bstep (se 1 (by rfl) ⟨668930, by rfl⟩ : syracuseStep 891907 = 1337861) B1337861
theorem B891923 : Blo 888571 891923 := bstep (se 1 (by rfl) ⟨668942, by rfl⟩ : syracuseStep 891923 = 1337885) B1337885
theorem B891939 : Blo 888571 891939 := bstep (se 1 (by rfl) ⟨668954, by rfl⟩ : syracuseStep 891939 = 1337909) B1337909
theorem B1809443 : Blo 888571 1809443 := bstep (se 1 (by rfl) ⟨1357082, by rfl⟩ : syracuseStep 1809443 = 2714165) B2714165
theorem B2530349 : Blo 888571 2530349 := bstep (se 3 (by rfl) ⟨474440, by rfl⟩ : syracuseStep 2530349 = 948881) B948881
theorem B891955 : Blo 888571 891955 := bstep (se 1 (by rfl) ⟨668966, by rfl⟩ : syracuseStep 891955 = 1337933) B1337933
theorem B891971 : Blo 888571 891971 := bstep (se 1 (by rfl) ⟨668978, by rfl⟩ : syracuseStep 891971 = 1337957) B1337957
theorem B891987 : Blo 888571 891987 := bstep (se 1 (by rfl) ⟨668990, by rfl⟩ : syracuseStep 891987 = 1337981) B1337981
theorem B892003 : Blo 888571 892003 := bstep (se 1 (by rfl) ⟨669002, by rfl⟩ : syracuseStep 892003 = 1338005) B1338005
theorem B892019 : Blo 888571 892019 := bstep (se 1 (by rfl) ⟨669014, by rfl⟩ : syracuseStep 892019 = 1338029) B1338029
theorem B892035 : Blo 888571 892035 := bstep (se 1 (by rfl) ⟨669026, by rfl⟩ : syracuseStep 892035 = 1338053) B1338053
theorem B2858125 : Blo 888571 2858125 := bstep (se 3 (by rfl) ⟨535898, by rfl⟩ : syracuseStep 2858125 = 1071797) B1071797
theorem B892051 : Blo 888571 892051 := bstep (se 1 (by rfl) ⟨669038, by rfl⟩ : syracuseStep 892051 = 1338077) B1338077
theorem B892067 : Blo 888571 892067 := bstep (se 1 (by rfl) ⟨669050, by rfl⟩ : syracuseStep 892067 = 1338101) B1338101
theorem B892083 : Blo 888571 892083 := bstep (se 1 (by rfl) ⟨669062, by rfl⟩ : syracuseStep 892083 = 1338125) B1338125
theorem B892099 : Blo 888571 892099 := bstep (se 1 (by rfl) ⟨669074, by rfl⟩ : syracuseStep 892099 = 1338149) B1338149
theorem B2006225 : Blo 888571 2006225 := bstep (se 2 (by rfl) ⟨752334, by rfl⟩ : syracuseStep 2006225 = 1504669) B1504669
theorem B892115 : Blo 888571 892115 := bstep (se 1 (by rfl) ⟨669086, by rfl⟩ : syracuseStep 892115 = 1338173) B1338173
theorem B3382499 : Blo 888571 3382499 := bstep (se 1 (by rfl) ⟨2536874, by rfl⟩ : syracuseStep 3382499 = 5073749) B5073749
theorem B2006243 : Blo 888571 2006243 := bstep (se 1 (by rfl) ⟨1504682, by rfl⟩ : syracuseStep 2006243 = 3009365) B3009365
theorem B892131 : Blo 888571 892131 := bstep (se 1 (by rfl) ⟨669098, by rfl⟩ : syracuseStep 892131 = 1338197) B1338197
theorem B2530541 : Blo 888571 2530541 := bstep (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) B948953
theorem B892147 : Blo 888571 892147 := bstep (se 1 (by rfl) ⟨669110, by rfl⟩ : syracuseStep 892147 = 1338221) B1338221
theorem B892163 : Blo 888571 892163 := bstep (se 1 (by rfl) ⟨669122, by rfl⟩ : syracuseStep 892163 = 1338245) B1338245
theorem B892179 : Blo 888571 892179 := bstep (se 1 (by rfl) ⟨669134, by rfl⟩ : syracuseStep 892179 = 1338269) B1338269
theorem B892195 : Blo 888571 892195 := bstep (se 1 (by rfl) ⟨669146, by rfl⟩ : syracuseStep 892195 = 1338293) B1338293
theorem B892211 : Blo 888571 892211 := bstep (se 1 (by rfl) ⟨669158, by rfl⟩ : syracuseStep 892211 = 1338317) B1338317
theorem B892227 : Blo 888571 892227 := bstep (se 1 (by rfl) ⟨669170, by rfl⟩ : syracuseStep 892227 = 1338341) B1338341
theorem B892243 : Blo 888571 892243 := bstep (se 1 (by rfl) ⟨669182, by rfl⟩ : syracuseStep 892243 = 1338365) B1338365
theorem B892259 : Blo 888571 892259 := bstep (se 1 (by rfl) ⟨669194, by rfl⟩ : syracuseStep 892259 = 1338389) B1338389
theorem B892275 : Blo 888571 892275 := bstep (se 1 (by rfl) ⟨669206, by rfl⟩ : syracuseStep 892275 = 1338413) B1338413
theorem B892291 : Blo 888571 892291 := bstep (se 1 (by rfl) ⟨669218, by rfl⟩ : syracuseStep 892291 = 1338437) B1338437
theorem B892307 : Blo 888571 892307 := bstep (se 1 (by rfl) ⟨669230, by rfl⟩ : syracuseStep 892307 = 1338461) B1338461
theorem B892323 : Blo 888571 892323 := bstep (se 1 (by rfl) ⟨669242, by rfl⟩ : syracuseStep 892323 = 1338485) B1338485
theorem B892339 : Blo 888571 892339 := bstep (se 1 (by rfl) ⟨669254, by rfl⟩ : syracuseStep 892339 = 1338509) B1338509
theorem B892355 : Blo 888571 892355 := bstep (se 1 (by rfl) ⟨669266, by rfl⟩ : syracuseStep 892355 = 1338533) B1338533
theorem B6757829 : Blo 888571 6757829 := bstep (se 4 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 6757829 = 1267093) B1267093
theorem B892371 : Blo 888571 892371 := bstep (se 1 (by rfl) ⟨669278, by rfl⟩ : syracuseStep 892371 = 1338557) B1338557
theorem B892387 : Blo 888571 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B2006513 : Blo 888571 2006513 := bstep (se 2 (by rfl) ⟨752442, by rfl⟩ : syracuseStep 2006513 = 1504885) B1504885
theorem B892403 : Blo 888571 892403 := bstep (se 1 (by rfl) ⟨669302, by rfl⟩ : syracuseStep 892403 = 1338605) B1338605
theorem B2006531 : Blo 888571 2006531 := bstep (se 1 (by rfl) ⟨1504898, by rfl⟩ : syracuseStep 2006531 = 3009797) B3009797
theorem B892419 : Blo 888571 892419 := bstep (se 1 (by rfl) ⟨669314, by rfl⟩ : syracuseStep 892419 = 1338629) B1338629
theorem B892435 : Blo 888571 892435 := bstep (se 1 (by rfl) ⟨669326, by rfl⟩ : syracuseStep 892435 = 1338653) B1338653
theorem B892451 : Blo 888571 892451 := bstep (se 1 (by rfl) ⟨669338, by rfl⟩ : syracuseStep 892451 = 1338677) B1338677
theorem B892467 : Blo 888571 892467 := bstep (se 1 (by rfl) ⟨669350, by rfl⟩ : syracuseStep 892467 = 1338701) B1338701
theorem B892483 : Blo 888571 892483 := bstep (se 1 (by rfl) ⟨669362, by rfl⟩ : syracuseStep 892483 = 1338725) B1338725
theorem B892499 : Blo 888571 892499 := bstep (se 1 (by rfl) ⟨669374, by rfl⟩ : syracuseStep 892499 = 1338749) B1338749
theorem B892515 : Blo 888571 892515 := bstep (se 1 (by rfl) ⟨669386, by rfl⟩ : syracuseStep 892515 = 1338773) B1338773
theorem B892531 : Blo 888571 892531 := bstep (se 1 (by rfl) ⟨669398, by rfl⟩ : syracuseStep 892531 = 1338797) B1338797
theorem B892547 : Blo 888571 892547 := bstep (se 1 (by rfl) ⟨669410, by rfl⟩ : syracuseStep 892547 = 1338821) B1338821
theorem B892563 : Blo 888571 892563 := bstep (se 1 (by rfl) ⟨669422, by rfl⟩ : syracuseStep 892563 = 1338845) B1338845
theorem B3612401 : Blo 888571 3612401 := bstep (se 2 (by rfl) ⟨1354650, by rfl⟩ : syracuseStep 3612401 = 2709301) B2709301
theorem B2006801 : Blo 888571 2006801 := bstep (se 2 (by rfl) ⟨752550, by rfl⟩ : syracuseStep 2006801 = 1505101) B1505101
theorem B2006819 : Blo 888571 2006819 := bstep (se 1 (by rfl) ⟨1505114, by rfl⟩ : syracuseStep 2006819 = 3010229) B3010229
theorem B5414705 : Blo 888571 5414705 := bstep (se 2 (by rfl) ⟨2030514, by rfl⟩ : syracuseStep 5414705 = 4061029) B4061029
theorem B3383153 : Blo 888571 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B6430691 : Blo 888571 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B2007089 : Blo 888571 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B2007107 : Blo 888571 2007107 := bstep (se 1 (by rfl) ⟨1505330, by rfl⟩ : syracuseStep 2007107 = 3010661) B3010661
theorem B2531533 : Blo 888571 2531533 := bstep (se 3 (by rfl) ⟨474662, by rfl⟩ : syracuseStep 2531533 = 949325) B949325
theorem B15212771 : Blo 888571 15212771 := bstep (se 1 (by rfl) ⟨11409578, by rfl⟩ : syracuseStep 15212771 = 22819157) B22819157
theorem B2007377 : Blo 888571 2007377 := bstep (se 2 (by rfl) ⟨752766, by rfl⟩ : syracuseStep 2007377 = 1505533) B1505533
theorem B2007395 : Blo 888571 2007395 := bstep (se 1 (by rfl) ⟨1505546, by rfl⟩ : syracuseStep 2007395 = 3011093) B3011093
theorem B3809891 : Blo 888571 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B4563569 : Blo 888571 4563569 := bstep (se 2 (by rfl) ⟨1711338, by rfl⟩ : syracuseStep 4563569 = 3422677) B3422677
theorem B2007665 : Blo 888571 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B2007683 : Blo 888571 2007683 := bstep (se 1 (by rfl) ⟨1505762, by rfl⟩ : syracuseStep 2007683 = 3011525) B3011525
theorem B6431557 : Blo 888571 6431557 := bstep (se 4 (by rfl) ⟨602958, by rfl⟩ : syracuseStep 6431557 = 1205917) B1205917
theorem B1319825 : Blo 888571 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B2007953 : Blo 888571 2007953 := bstep (se 2 (by rfl) ⟨752982, by rfl⟩ : syracuseStep 2007953 = 1505965) B1505965
theorem B2007971 : Blo 888571 2007971 := bstep (se 1 (by rfl) ⟨1505978, by rfl⟩ : syracuseStep 2007971 = 3011957) B3011957
theorem B1352801 : Blo 888571 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B2008241 : Blo 888571 2008241 := bstep (se 2 (by rfl) ⟨753090, by rfl⟩ : syracuseStep 2008241 = 1506181) B1506181
theorem B2008259 : Blo 888571 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B3384611 : Blo 888571 3384611 := bstep (se 1 (by rfl) ⟨2538458, by rfl⟩ : syracuseStep 3384611 = 5076917) B5076917
theorem B3384625 : Blo 888571 3384625 := bstep (se 2 (by rfl) ⟨1269234, by rfl⟩ : syracuseStep 3384625 = 2538469) B2538469
theorem B1648081 : Blo 888571 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B3811121 : Blo 888571 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B2533265 : Blo 888571 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B2435075 : Blo 888571 2435075 := bstep (se 1 (by rfl) ⟨1826306, by rfl⟩ : syracuseStep 2435075 = 3652613) B3652613
theorem B2533457 : Blo 888571 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B6957197 : Blo 888571 6957197 := bstep (se 3 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 6957197 = 2608949) B2608949
theorem B2140451 : Blo 888571 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B2468141 : Blo 888571 2468141 := bstep (se 3 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 2468141 = 925553) B925553
theorem B1354067 : Blo 888571 1354067 := bstep (se 1 (by rfl) ⟨1015550, by rfl⟩ : syracuseStep 1354067 = 2031101) B2031101
theorem B2140643 : Blo 888571 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B1124867 : Blo 888571 1124867 := bstep (se 1 (by rfl) ⟨843650, by rfl⟩ : syracuseStep 1124867 = 1687301) B1687301
theorem B2402989 : Blo 888571 2402989 := bstep (se 3 (by rfl) ⟨450560, by rfl⟩ : syracuseStep 2402989 = 901121) B901121
theorem B5712581 : Blo 888571 5712581 := bstep (se 4 (by rfl) ⟨535554, by rfl⟩ : syracuseStep 5712581 = 1071109) B1071109
theorem B3386083 : Blo 888571 3386083 := bstep (se 1 (by rfl) ⟨2539562, by rfl⟩ : syracuseStep 3386083 = 5079125) B5079125
theorem B2140931 : Blo 888571 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B2403121 : Blo 888571 2403121 := bstep (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) B1802341
theorem B2534449 : Blo 888571 2534449 := bstep (se 2 (by rfl) ⟨950418, by rfl⟩ : syracuseStep 2534449 = 1900837) B1900837
theorem B1125571 : Blo 888571 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B1125667 : Blo 888571 1125667 := bstep (se 1 (by rfl) ⟨844250, by rfl⟩ : syracuseStep 1125667 = 1688501) B1688501
theorem B2534723 : Blo 888571 2534723 := bstep (se 1 (by rfl) ⟨1901042, by rfl⟩ : syracuseStep 2534723 = 3802085) B3802085
theorem B7613837 : Blo 888571 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B2534915 : Blo 888571 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B4501169 : Blo 888571 4501169 := bstep (se 2 (by rfl) ⟨1687938, by rfl⟩ : syracuseStep 4501169 = 3375877) B3375877
theorem B2141873 : Blo 888571 2141873 := bstep (se 2 (by rfl) ⟨803202, by rfl⟩ : syracuseStep 2141873 = 1606405) B1606405
theorem B1126163 : Blo 888571 1126163 := bstep (se 1 (by rfl) ⟨844622, by rfl⟩ : syracuseStep 1126163 = 1689245) B1689245
theorem B2404397 : Blo 888571 2404397 := bstep (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) B901649
theorem B5779619 : Blo 888571 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B2535725 : Blo 888571 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B1159475 : Blo 888571 1159475 := bstep (se 1 (by rfl) ⟨869606, by rfl⟩ : syracuseStep 1159475 = 1739213) B1739213
theorem B2404721 : Blo 888571 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B1126867 : Blo 888571 1126867 := bstep (se 1 (by rfl) ⟨845150, by rfl⟩ : syracuseStep 1126867 = 1690301) B1690301
theorem B2535907 : Blo 888571 2535907 := bstep (se 1 (by rfl) ⟨1901930, by rfl⟩ : syracuseStep 2535907 = 3803861) B3803861
theorem B1126963 : Blo 888571 1126963 := bstep (se 1 (by rfl) ⟨845222, by rfl⟩ : syracuseStep 1126963 = 1690445) B1690445
theorem B1356353 : Blo 888571 1356353 := bstep (se 2 (by rfl) ⟨508632, by rfl⟩ : syracuseStep 1356353 = 1017265) B1017265
theorem B2142833 : Blo 888571 2142833 := bstep (se 2 (by rfl) ⟨803562, by rfl⟩ : syracuseStep 2142833 = 1607125) B1607125
theorem B4338353 : Blo 888571 4338353 := bstep (se 2 (by rfl) ⟨1626882, by rfl⟩ : syracuseStep 4338353 = 3253765) B3253765
theorem B3388301 : Blo 888571 3388301 := bstep (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) B1270613
theorem B2536397 : Blo 888571 2536397 := bstep (se 3 (by rfl) ⟨475574, by rfl⟩ : syracuseStep 2536397 = 951149) B951149
theorem B1127459 : Blo 888571 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B2438225 : Blo 888571 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B4502627 : Blo 888571 4502627 := bstep (se 1 (by rfl) ⟨3376970, by rfl⟩ : syracuseStep 4502627 = 6753941) B6753941
theorem B2143363 : Blo 888571 2143363 := bstep (se 1 (by rfl) ⟨1607522, by rfl⟩ : syracuseStep 2143363 = 3215045) B3215045
theorem B1356931 : Blo 888571 1356931 := bstep (se 1 (by rfl) ⟨1017698, by rfl⟩ : syracuseStep 1356931 = 2035397) B2035397
theorem B6763661 : Blo 888571 6763661 := bstep (se 3 (by rfl) ⟨1268186, by rfl⟩ : syracuseStep 6763661 = 2536373) B2536373
theorem B5715299 : Blo 888571 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B2405933 : Blo 888571 2405933 := bstep (se 3 (by rfl) ⟨451112, by rfl⟩ : syracuseStep 2405933 = 902225) B902225
theorem B1521217 : Blo 888571 1521217 := bstep (se 2 (by rfl) ⟨570456, by rfl⟩ : syracuseStep 1521217 = 1140913) B1140913
theorem B7616227 : Blo 888571 7616227 := bstep (se 1 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 7616227 = 11424341) B11424341
theorem B1128163 : Blo 888571 1128163 := bstep (se 1 (by rfl) ⟨846122, by rfl⟩ : syracuseStep 1128163 = 1692245) B1692245
theorem B1128259 : Blo 888571 1128259 := bstep (se 1 (by rfl) ⟨846194, by rfl⟩ : syracuseStep 1128259 = 1692389) B1692389
theorem B5420933 : Blo 888571 5420933 := bstep (se 4 (by rfl) ⟨508212, by rfl⟩ : syracuseStep 5420933 = 1016425) B1016425
theorem B4503437 : Blo 888571 4503437 := bstep (se 3 (by rfl) ⟨844394, by rfl⟩ : syracuseStep 4503437 = 1688789) B1688789
theorem B1423379 : Blo 888571 1423379 := bstep (se 1 (by rfl) ⟨1067534, by rfl⟩ : syracuseStep 1423379 = 2135069) B2135069
theorem B1521731 : Blo 888571 1521731 := bstep (se 1 (by rfl) ⟨1141298, by rfl⟩ : syracuseStep 1521731 = 2282597) B2282597
theorem B2537581 : Blo 888571 2537581 := bstep (se 3 (by rfl) ⟨475796, by rfl⟩ : syracuseStep 2537581 = 951593) B951593
theorem B1423507 : Blo 888571 1423507 := bstep (se 1 (by rfl) ⟨1067630, by rfl⟩ : syracuseStep 1423507 = 2135261) B2135261
theorem B1128755 : Blo 888571 1128755 := bstep (se 1 (by rfl) ⟨846566, by rfl⟩ : syracuseStep 1128755 = 1693133) B1693133
theorem B2144593 : Blo 888571 2144593 := bstep (se 2 (by rfl) ⟨804222, by rfl⟩ : syracuseStep 2144593 = 1608445) B1608445
theorem B2406797 : Blo 888571 2406797 := bstep (se 3 (by rfl) ⟨451274, by rfl⟩ : syracuseStep 2406797 = 902549) B902549
theorem B1424147 : Blo 888571 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B1424225 : Blo 888571 1424225 := bstep (se 2 (by rfl) ⟨534084, by rfl⟩ : syracuseStep 1424225 = 1068169) B1068169
theorem B1129459 : Blo 888571 1129459 := bstep (se 1 (by rfl) ⟨847094, by rfl⟩ : syracuseStep 1129459 = 1694189) B1694189
theorem B1129555 : Blo 888571 1129555 := bstep (se 1 (by rfl) ⟨847166, by rfl⟩ : syracuseStep 1129555 = 1694333) B1694333
theorem B2538641 : Blo 888571 2538641 := bstep (se 2 (by rfl) ⟨951990, by rfl⟩ : syracuseStep 2538641 = 1903981) B1903981
theorem B1424609 : Blo 888571 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B5717297 : Blo 888571 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B2407747 : Blo 888571 2407747 := bstep (se 1 (by rfl) ⟨1805810, by rfl⟩ : syracuseStep 2407747 = 3611621) B3611621
theorem B1424737 : Blo 888571 1424737 := bstep (se 2 (by rfl) ⟨534276, by rfl⟩ : syracuseStep 1424737 = 1068553) B1068553
theorem B5062085 : Blo 888571 5062085 := bstep (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) B949141
theorem B1687043 : Blo 888571 1687043 := bstep (se 1 (by rfl) ⟨1265282, by rfl⟩ : syracuseStep 1687043 = 2530565) B2530565
theorem B1687331 : Blo 888571 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B2539313 : Blo 888571 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B12173237 : Blo 888571 12173237 := bstep (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) B1141241
theorem B6766577 : Blo 888571 6766577 := bstep (se 2 (by rfl) ⟨2537466, by rfl⟩ : syracuseStep 6766577 = 5074933) B5074933
theorem B2572273 : Blo 888571 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B11386979 : Blo 888571 11386979 := bstep (se 1 (by rfl) ⟨8540234, by rfl⟩ : syracuseStep 11386979 = 17080469) B17080469
theorem B5062769 : Blo 888571 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B12173453 : Blo 888571 12173453 := bstep (se 3 (by rfl) ⟨2282522, by rfl⟩ : syracuseStep 12173453 = 4565045) B4565045
theorem B5718221 : Blo 888571 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B999715 : Blo 888571 999715 := bstep (se 1 (by rfl) ⟨749786, by rfl⟩ : syracuseStep 999715 = 1499573) B1499573
theorem B1524145 : Blo 888571 1524145 := bstep (se 2 (by rfl) ⟨571554, by rfl⟩ : syracuseStep 1524145 = 1143109) B1143109
theorem B999859 : Blo 888571 999859 := bstep (se 1 (by rfl) ⟨749894, by rfl⟩ : syracuseStep 999859 = 1499789) B1499789
theorem B3654179 : Blo 888571 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B1000003 : Blo 888571 1000003 := bstep (se 1 (by rfl) ⟨750002, by rfl⟩ : syracuseStep 1000003 = 1500005) B1500005
theorem B2540099 : Blo 888571 2540099 := bstep (se 1 (by rfl) ⟨1905074, by rfl⟩ : syracuseStep 2540099 = 3810149) B3810149
theorem B7225969 : Blo 888571 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B901811 : Blo 888571 901811 := bstep (se 1 (by rfl) ⟨676358, by rfl⟩ : syracuseStep 901811 = 1352717) B1352717
theorem B1688273 : Blo 888571 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B1000147 : Blo 888571 1000147 := bstep (se 1 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 1000147 = 1500221) B1500221
theorem B4506353 : Blo 888571 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B1426243 : Blo 888571 1426243 := bstep (se 1 (by rfl) ⟨1069682, by rfl⟩ : syracuseStep 1426243 = 2139365) B2139365
theorem B1000291 : Blo 888571 1000291 := bstep (se 1 (by rfl) ⟨750218, by rfl⟩ : syracuseStep 1000291 = 1500437) B1500437
theorem B7226225 : Blo 888571 7226225 := bstep (se 2 (by rfl) ⟨2709834, by rfl⟩ : syracuseStep 7226225 = 5419669) B5419669
theorem B2540429 : Blo 888571 2540429 := bstep (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) B952661
theorem B2999213 : Blo 888571 2999213 := bstep (se 3 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 2999213 = 1124705) B1124705
theorem B2540497 : Blo 888571 2540497 := bstep (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) B1905373
theorem B2999267 : Blo 888571 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1000435 : Blo 888571 1000435 := bstep (se 1 (by rfl) ⟨750326, by rfl⟩ : syracuseStep 1000435 = 1500653) B1500653
theorem B2704433 : Blo 888571 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B1000579 : Blo 888571 1000579 := bstep (se 1 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 1000579 = 1500869) B1500869
theorem B2540771 : Blo 888571 2540771 := bstep (se 1 (by rfl) ⟨1905578, by rfl⟩ : syracuseStep 2540771 = 3811157) B3811157
theorem B2999537 : Blo 888571 2999537 := bstep (se 2 (by rfl) ⟨1124826, by rfl⟩ : syracuseStep 2999537 = 2249653) B2249653
theorem B1000723 : Blo 888571 1000723 := bstep (se 1 (by rfl) ⟨750542, by rfl⟩ : syracuseStep 1000723 = 1501085) B1501085
theorem B1951025 : Blo 888571 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B1000867 : Blo 888571 1000867 := bstep (se 1 (by rfl) ⟨750650, by rfl⟩ : syracuseStep 1000867 = 1501301) B1501301
theorem B4343203 : Blo 888571 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B1426915 : Blo 888571 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B5064227 : Blo 888571 5064227 := bstep (se 1 (by rfl) ⟨3798170, by rfl⟩ : syracuseStep 5064227 = 7596341) B7596341
theorem B1001011 : Blo 888571 1001011 := bstep (se 1 (by rfl) ⟨750758, by rfl⟩ : syracuseStep 1001011 = 1501517) B1501517
theorem B1689169 : Blo 888571 1689169 := bstep (se 2 (by rfl) ⟨633438, by rfl⟩ : syracuseStep 1689169 = 1266877) B1266877
theorem B2705069 : Blo 888571 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B1001155 : Blo 888571 1001155 := bstep (se 1 (by rfl) ⟨750866, by rfl⟩ : syracuseStep 1001155 = 1501733) B1501733
theorem B1689329 : Blo 888571 1689329 := bstep (se 2 (by rfl) ⟨633498, by rfl⟩ : syracuseStep 1689329 = 1266997) B1266997
theorem B3000077 : Blo 888571 3000077 := bstep (se 3 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 3000077 = 1125029) B1125029
theorem B3000131 : Blo 888571 3000131 := bstep (se 1 (by rfl) ⟨2250098, by rfl⟩ : syracuseStep 3000131 = 4500197) B4500197
theorem B1001299 : Blo 888571 1001299 := bstep (se 1 (by rfl) ⟨750974, by rfl⟩ : syracuseStep 1001299 = 1501949) B1501949
theorem B1427377 : Blo 888571 1427377 := bstep (se 2 (by rfl) ⟨535266, by rfl⟩ : syracuseStep 1427377 = 1070533) B1070533
theorem B1001443 : Blo 888571 1001443 := bstep (se 1 (by rfl) ⟨751082, by rfl⟩ : syracuseStep 1001443 = 1502165) B1502165
theorem B1427473 : Blo 888571 1427473 := bstep (se 2 (by rfl) ⟨535302, by rfl⟩ : syracuseStep 1427473 = 1070605) B1070605
theorem B2541613 : Blo 888571 2541613 := bstep (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) B953105
theorem B3000401 : Blo 888571 3000401 := bstep (se 2 (by rfl) ⟨1125150, by rfl⟩ : syracuseStep 3000401 = 2250301) B2250301
theorem B3295331 : Blo 888571 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B1001587 : Blo 888571 1001587 := bstep (se 1 (by rfl) ⟨751190, by rfl⟩ : syracuseStep 1001587 = 1502381) B1502381
theorem B1689731 : Blo 888571 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B4507811 : Blo 888571 4507811 := bstep (se 1 (by rfl) ⟨3380858, by rfl⟩ : syracuseStep 4507811 = 6761717) B6761717
theorem B1427633 : Blo 888571 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1001731 : Blo 888571 1001731 := bstep (se 1 (by rfl) ⟨751298, by rfl⟩ : syracuseStep 1001731 = 1502597) B1502597
theorem B1001875 : Blo 888571 1001875 := bstep (se 1 (by rfl) ⟨751406, by rfl⟩ : syracuseStep 1001875 = 1502813) B1502813
theorem B1002019 : Blo 888571 1002019 := bstep (se 1 (by rfl) ⟨751514, by rfl⟩ : syracuseStep 1002019 = 1503029) B1503029
theorem B3000941 : Blo 888571 3000941 := bstep (se 3 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 3000941 = 1125353) B1125353
theorem B3000995 : Blo 888571 3000995 := bstep (se 1 (by rfl) ⟨2250746, by rfl⟩ : syracuseStep 3000995 = 4501493) B4501493
theorem B1002163 : Blo 888571 1002163 := bstep (se 1 (by rfl) ⟨751622, by rfl⟩ : syracuseStep 1002163 = 1503245) B1503245
theorem B1002307 : Blo 888571 1002307 := bstep (se 1 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 1002307 = 1503461) B1503461
theorem B3001265 : Blo 888571 3001265 := bstep (se 2 (by rfl) ⟨1125474, by rfl⟩ : syracuseStep 3001265 = 2250949) B2250949
theorem B4508621 : Blo 888571 4508621 := bstep (se 3 (by rfl) ⟨845366, by rfl⟩ : syracuseStep 4508621 = 1690733) B1690733
theorem B3132365 : Blo 888571 3132365 := bstep (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) B1174637
theorem B1002451 : Blo 888571 1002451 := bstep (se 1 (by rfl) ⟨751838, by rfl⟩ : syracuseStep 1002451 = 1503677) B1503677
theorem B1690627 : Blo 888571 1690627 := bstep (se 1 (by rfl) ⟨1267970, by rfl⟩ : syracuseStep 1690627 = 2535941) B2535941
theorem B1002595 : Blo 888571 1002595 := bstep (se 1 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 1002595 = 1503893) B1503893
theorem B1690787 : Blo 888571 1690787 := bstep (se 1 (by rfl) ⟨1268090, by rfl⟩ : syracuseStep 1690787 = 2536181) B2536181
theorem B1002739 : Blo 888571 1002739 := bstep (se 1 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 1002739 = 1504109) B1504109
theorem B1002883 : Blo 888571 1002883 := bstep (se 1 (by rfl) ⟨752162, by rfl⟩ : syracuseStep 1002883 = 1504325) B1504325
theorem B2936237 : Blo 888571 2936237 := bstep (se 3 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 2936237 = 1101089) B1101089
theorem B3001805 : Blo 888571 3001805 := bstep (se 3 (by rfl) ⟨562838, by rfl⟩ : syracuseStep 3001805 = 1125677) B1125677
theorem B3001859 : Blo 888571 3001859 := bstep (se 1 (by rfl) ⟨2251394, by rfl⟩ : syracuseStep 3001859 = 4502789) B4502789
theorem B1003027 : Blo 888571 1003027 := bstep (se 1 (by rfl) ⟨752270, by rfl⟩ : syracuseStep 1003027 = 1504541) B1504541
theorem B1003171 : Blo 888571 1003171 := bstep (se 1 (by rfl) ⟨752378, by rfl⟩ : syracuseStep 1003171 = 1504757) B1504757
theorem B3002129 : Blo 888571 3002129 := bstep (se 2 (by rfl) ⟨1125798, by rfl⟩ : syracuseStep 3002129 = 2251597) B2251597
theorem B1003315 : Blo 888571 1003315 := bstep (se 1 (by rfl) ⟨752486, by rfl⟩ : syracuseStep 1003315 = 1504973) B1504973
theorem B1265539 : Blo 888571 1265539 := bstep (se 1 (by rfl) ⟨949154, by rfl⟩ : syracuseStep 1265539 = 1898309) B1898309
theorem B1429427 : Blo 888571 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B1068995 : Blo 888571 1068995 := bstep (se 1 (by rfl) ⟨801746, by rfl⟩ : syracuseStep 1068995 = 1603493) B1603493
theorem B1003459 : Blo 888571 1003459 := bstep (se 1 (by rfl) ⟨752594, by rfl⟩ : syracuseStep 1003459 = 1505189) B1505189
theorem B1265635 : Blo 888571 1265635 := bstep (se 1 (by rfl) ⟨949226, by rfl⟩ : syracuseStep 1265635 = 1898453) B1898453
theorem B1003603 : Blo 888571 1003603 := bstep (se 1 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 1003603 = 1505405) B1505405
theorem B6410339 : Blo 888571 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B1691857 : Blo 888571 1691857 := bstep (se 2 (by rfl) ⟨634446, by rfl⟩ : syracuseStep 1691857 = 1268893) B1268893
theorem B1003747 : Blo 888571 1003747 := bstep (se 1 (by rfl) ⟨752810, by rfl⟩ : syracuseStep 1003747 = 1505621) B1505621
theorem B3002669 : Blo 888571 3002669 := bstep (se 3 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 3002669 = 1126001) B1126001
theorem B3002723 : Blo 888571 3002723 := bstep (se 1 (by rfl) ⟨2252042, by rfl⟩ : syracuseStep 3002723 = 4504085) B4504085
theorem B1003891 : Blo 888571 1003891 := bstep (se 1 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 1003891 = 1505837) B1505837
theorem B2937293 : Blo 888571 2937293 := bstep (se 3 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 2937293 = 1101485) B1101485
theorem B1266131 : Blo 888571 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B1004035 : Blo 888571 1004035 := bstep (se 1 (by rfl) ⟨753026, by rfl⟩ : syracuseStep 1004035 = 1506053) B1506053
theorem B2249329 : Blo 888571 2249329 := bstep (se 2 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 2249329 = 1686997) B1686997
theorem B3002993 : Blo 888571 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B8245901 : Blo 888571 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B5067461 : Blo 888571 5067461 := bstep (se 4 (by rfl) ⟨475074, by rfl⟩ : syracuseStep 5067461 = 950149) B950149
theorem B5133091 : Blo 888571 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B2249603 : Blo 888571 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B2249795 : Blo 888571 2249795 := bstep (se 1 (by rfl) ⟨1687346, by rfl⟩ : syracuseStep 2249795 = 3374693) B3374693
theorem B1266769 : Blo 888571 1266769 := bstep (se 2 (by rfl) ⟨475038, by rfl⟩ : syracuseStep 1266769 = 950077) B950077
theorem B5067917 : Blo 888571 5067917 := bstep (se 3 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 5067917 = 1900469) B1900469
theorem B3003533 : Blo 888571 3003533 := bstep (se 3 (by rfl) ⟨563162, by rfl⟩ : syracuseStep 3003533 = 1126325) B1126325
theorem B3003587 : Blo 888571 3003587 := bstep (se 1 (by rfl) ⟨2252690, by rfl⟩ : syracuseStep 3003587 = 4505381) B4505381
theorem B1692913 : Blo 888571 1692913 := bstep (se 2 (by rfl) ⟨634842, by rfl⟩ : syracuseStep 1692913 = 1269685) B1269685
theorem B21976433 : Blo 888571 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B1267105 : Blo 888571 1267105 := bstep (se 2 (by rfl) ⟨475164, by rfl⟩ : syracuseStep 1267105 = 950329) B950329
theorem B1201603 : Blo 888571 1201603 := bstep (se 1 (by rfl) ⟨901202, by rfl⟩ : syracuseStep 1201603 = 1802405) B1802405
theorem B3003857 : Blo 888571 3003857 := bstep (se 2 (by rfl) ⟨1126446, by rfl⟩ : syracuseStep 3003857 = 2252893) B2252893
theorem B1693315 : Blo 888571 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B1332881 : Blo 888571 1332881 := bstep (se 2 (by rfl) ⟨499830, by rfl⟩ : syracuseStep 1332881 = 999661) B999661
theorem B1332899 : Blo 888571 1332899 := bstep (se 1 (by rfl) ⟨999674, by rfl⟩ : syracuseStep 1332899 = 1999349) B1999349
theorem B1693361 : Blo 888571 1693361 := bstep (se 2 (by rfl) ⟨635010, by rfl⟩ : syracuseStep 1693361 = 1270021) B1270021
theorem B1332929 : Blo 888571 1332929 := bstep (se 2 (by rfl) ⟨499848, by rfl⟩ : syracuseStep 1332929 = 999697) B999697
theorem B1332947 : Blo 888571 1332947 := bstep (se 1 (by rfl) ⟨999710, by rfl⟩ : syracuseStep 1332947 = 1999421) B1999421
theorem B1332977 : Blo 888571 1332977 := bstep (se 2 (by rfl) ⟨499866, by rfl⟩ : syracuseStep 1332977 = 999733) B999733
theorem B1332995 : Blo 888571 1332995 := bstep (se 1 (by rfl) ⟨999746, by rfl⟩ : syracuseStep 1332995 = 1999493) B1999493
theorem B1333025 : Blo 888571 1333025 := bstep (se 2 (by rfl) ⟨499884, by rfl⟩ : syracuseStep 1333025 = 999769) B999769
theorem B4511537 : Blo 888571 4511537 := bstep (se 2 (by rfl) ⟨1691826, by rfl⟩ : syracuseStep 4511537 = 3383653) B3383653
theorem B1333043 : Blo 888571 1333043 := bstep (se 1 (by rfl) ⟨999782, by rfl⟩ : syracuseStep 1333043 = 1999565) B1999565
theorem B1333073 : Blo 888571 1333073 := bstep (se 2 (by rfl) ⟨499902, by rfl⟩ : syracuseStep 1333073 = 999805) B999805
theorem B1333091 : Blo 888571 1333091 := bstep (se 1 (by rfl) ⟨999818, by rfl⟩ : syracuseStep 1333091 = 1999637) B1999637
theorem B1333121 : Blo 888571 1333121 := bstep (se 2 (by rfl) ⟨499920, by rfl⟩ : syracuseStep 1333121 = 999841) B999841
theorem B1333139 : Blo 888571 1333139 := bstep (se 1 (by rfl) ⟨999854, by rfl⟩ : syracuseStep 1333139 = 1999709) B1999709
theorem B1333169 : Blo 888571 1333169 := bstep (se 2 (by rfl) ⟨499938, by rfl⟩ : syracuseStep 1333169 = 999877) B999877
theorem B1333187 : Blo 888571 1333187 := bstep (se 1 (by rfl) ⟨999890, by rfl⟩ : syracuseStep 1333187 = 1999781) B1999781
theorem B1693649 : Blo 888571 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B1333217 : Blo 888571 1333217 := bstep (se 2 (by rfl) ⟨499956, by rfl⟩ : syracuseStep 1333217 = 999913) B999913
theorem B3004397 : Blo 888571 3004397 := bstep (se 3 (by rfl) ⟨563324, by rfl⟩ : syracuseStep 3004397 = 1126649) B1126649
theorem B2250737 : Blo 888571 2250737 := bstep (se 2 (by rfl) ⟨844026, by rfl⟩ : syracuseStep 2250737 = 1688053) B1688053
theorem B1267697 : Blo 888571 1267697 := bstep (se 2 (by rfl) ⟨475386, by rfl⟩ : syracuseStep 1267697 = 950773) B950773
theorem B1333235 : Blo 888571 1333235 := bstep (se 1 (by rfl) ⟨999926, by rfl⟩ : syracuseStep 1333235 = 1999853) B1999853
theorem B1333265 : Blo 888571 1333265 := bstep (se 2 (by rfl) ⟨499974, by rfl⟩ : syracuseStep 1333265 = 999949) B999949
theorem B1333283 : Blo 888571 1333283 := bstep (se 1 (by rfl) ⟨999962, by rfl⟩ : syracuseStep 1333283 = 1999925) B1999925
theorem B2250787 : Blo 888571 2250787 := bstep (se 1 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 2250787 = 3376181) B3376181
theorem B3004451 : Blo 888571 3004451 := bstep (se 1 (by rfl) ⟨2253338, by rfl⟩ : syracuseStep 3004451 = 4506677) B4506677
theorem B1333313 : Blo 888571 1333313 := bstep (se 2 (by rfl) ⟨499992, by rfl⟩ : syracuseStep 1333313 = 999985) B999985
theorem B1333331 : Blo 888571 1333331 := bstep (se 1 (by rfl) ⟨999998, by rfl⟩ : syracuseStep 1333331 = 1999997) B1999997
theorem B1333361 : Blo 888571 1333361 := bstep (se 2 (by rfl) ⟨500010, by rfl⟩ : syracuseStep 1333361 = 1000021) B1000021
theorem B1333379 : Blo 888571 1333379 := bstep (se 1 (by rfl) ⟨1000034, by rfl⟩ : syracuseStep 1333379 = 2000069) B2000069
theorem B1333409 : Blo 888571 1333409 := bstep (se 2 (by rfl) ⟨500028, by rfl⟩ : syracuseStep 1333409 = 1000057) B1000057
theorem B2250929 : Blo 888571 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B1333427 : Blo 888571 1333427 := bstep (se 1 (by rfl) ⟨1000070, by rfl⟩ : syracuseStep 1333427 = 2000141) B2000141
theorem B1333457 : Blo 888571 1333457 := bstep (se 2 (by rfl) ⟨500046, by rfl⟩ : syracuseStep 1333457 = 1000093) B1000093
theorem B1333475 : Blo 888571 1333475 := bstep (se 1 (by rfl) ⟨1000106, by rfl⟩ : syracuseStep 1333475 = 2000213) B2000213
theorem B1333505 : Blo 888571 1333505 := bstep (se 2 (by rfl) ⟨500064, by rfl⟩ : syracuseStep 1333505 = 1000129) B1000129
theorem B1333523 : Blo 888571 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B1333553 : Blo 888571 1333553 := bstep (se 2 (by rfl) ⟨500082, by rfl⟩ : syracuseStep 1333553 = 1000165) B1000165
theorem B3004721 : Blo 888571 3004721 := bstep (se 2 (by rfl) ⟨1126770, by rfl⟩ : syracuseStep 3004721 = 2253541) B2253541
theorem B1333571 : Blo 888571 1333571 := bstep (se 1 (by rfl) ⟨1000178, by rfl⟩ : syracuseStep 1333571 = 2000357) B2000357
theorem B1333601 : Blo 888571 1333601 := bstep (se 2 (by rfl) ⟨500100, by rfl⟩ : syracuseStep 1333601 = 1000201) B1000201
theorem B1333619 : Blo 888571 1333619 := bstep (se 1 (by rfl) ⟨1000214, by rfl⟩ : syracuseStep 1333619 = 2000429) B2000429
theorem B1333649 : Blo 888571 1333649 := bstep (se 2 (by rfl) ⟨500118, by rfl⟩ : syracuseStep 1333649 = 1000237) B1000237
theorem B1333667 : Blo 888571 1333667 := bstep (se 1 (by rfl) ⟨1000250, by rfl⟩ : syracuseStep 1333667 = 2000501) B2000501
theorem B1333697 : Blo 888571 1333697 := bstep (se 2 (by rfl) ⟨500136, by rfl⟩ : syracuseStep 1333697 = 1000273) B1000273
theorem B1333715 : Blo 888571 1333715 := bstep (se 1 (by rfl) ⟨1000286, by rfl⟩ : syracuseStep 1333715 = 2000573) B2000573
theorem B1071571 : Blo 888571 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B1333745 : Blo 888571 1333745 := bstep (se 2 (by rfl) ⟨500154, by rfl⟩ : syracuseStep 1333745 = 1000309) B1000309
theorem B1333763 : Blo 888571 1333763 := bstep (se 1 (by rfl) ⟨1000322, by rfl⟩ : syracuseStep 1333763 = 2000645) B2000645
theorem B1268227 : Blo 888571 1268227 := bstep (se 1 (by rfl) ⟨951170, by rfl⟩ : syracuseStep 1268227 = 1902341) B1902341
theorem B1333793 : Blo 888571 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B1333811 : Blo 888571 1333811 := bstep (se 1 (by rfl) ⟨1000358, by rfl⟩ : syracuseStep 1333811 = 2000717) B2000717
theorem B1333841 : Blo 888571 1333841 := bstep (se 2 (by rfl) ⟨500190, by rfl⟩ : syracuseStep 1333841 = 1000381) B1000381
theorem B1333859 : Blo 888571 1333859 := bstep (se 1 (by rfl) ⟨1000394, by rfl⟩ : syracuseStep 1333859 = 2000789) B2000789
theorem B1333889 : Blo 888571 1333889 := bstep (se 2 (by rfl) ⟨500208, by rfl⟩ : syracuseStep 1333889 = 1000417) B1000417
theorem B1333907 : Blo 888571 1333907 := bstep (se 1 (by rfl) ⟨1000430, by rfl⟩ : syracuseStep 1333907 = 2000861) B2000861
theorem B1694371 : Blo 888571 1694371 := bstep (se 1 (by rfl) ⟨1270778, by rfl⟩ : syracuseStep 1694371 = 2541557) B2541557
theorem B1333937 : Blo 888571 1333937 := bstep (se 2 (by rfl) ⟨500226, by rfl⟩ : syracuseStep 1333937 = 1000453) B1000453
theorem B1333955 : Blo 888571 1333955 := bstep (se 1 (by rfl) ⟨1000466, by rfl⟩ : syracuseStep 1333955 = 2000933) B2000933
theorem B1333985 : Blo 888571 1333985 := bstep (se 2 (by rfl) ⟨500244, by rfl⟩ : syracuseStep 1333985 = 1000489) B1000489
theorem B1334003 : Blo 888571 1334003 := bstep (se 1 (by rfl) ⟨1000502, by rfl⟩ : syracuseStep 1334003 = 2001005) B2001005
theorem B7592717 : Blo 888571 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B1334033 : Blo 888571 1334033 := bstep (se 2 (by rfl) ⟨500262, by rfl⟩ : syracuseStep 1334033 = 1000525) B1000525
theorem B1334051 : Blo 888571 1334051 := bstep (se 1 (by rfl) ⟨1000538, by rfl⟩ : syracuseStep 1334051 = 2001077) B2001077
theorem B1334081 : Blo 888571 1334081 := bstep (se 2 (by rfl) ⟨500280, by rfl⟩ : syracuseStep 1334081 = 1000561) B1000561
theorem B3005261 : Blo 888571 3005261 := bstep (se 3 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 3005261 = 1126973) B1126973
theorem B1334099 : Blo 888571 1334099 := bstep (se 1 (by rfl) ⟨1000574, by rfl⟩ : syracuseStep 1334099 = 2001149) B2001149
theorem B1268563 : Blo 888571 1268563 := bstep (se 1 (by rfl) ⟨951422, by rfl⟩ : syracuseStep 1268563 = 1902845) B1902845
theorem B1071955 : Blo 888571 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B1334129 : Blo 888571 1334129 := bstep (se 2 (by rfl) ⟨500298, by rfl⟩ : syracuseStep 1334129 = 1000597) B1000597
theorem B1334147 : Blo 888571 1334147 := bstep (se 1 (by rfl) ⟨1000610, by rfl⟩ : syracuseStep 1334147 = 2001221) B2001221
theorem B3005315 : Blo 888571 3005315 := bstep (se 1 (by rfl) ⟨2253986, by rfl⟩ : syracuseStep 3005315 = 4507973) B4507973
theorem B1334177 : Blo 888571 1334177 := bstep (se 2 (by rfl) ⟨500316, by rfl⟩ : syracuseStep 1334177 = 1000633) B1000633
theorem B1334195 : Blo 888571 1334195 := bstep (se 1 (by rfl) ⟨1000646, by rfl⟩ : syracuseStep 1334195 = 2001293) B2001293
theorem B1334225 : Blo 888571 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B1334243 : Blo 888571 1334243 := bstep (se 1 (by rfl) ⟨1000682, by rfl⟩ : syracuseStep 1334243 = 2001365) B2001365
theorem B1334273 : Blo 888571 1334273 := bstep (se 2 (by rfl) ⟨500352, by rfl⟩ : syracuseStep 1334273 = 1000705) B1000705
theorem B1334291 : Blo 888571 1334291 := bstep (se 1 (by rfl) ⟨1000718, by rfl⟩ : syracuseStep 1334291 = 2001437) B2001437
theorem B1334321 : Blo 888571 1334321 := bstep (se 2 (by rfl) ⟨500370, by rfl⟩ : syracuseStep 1334321 = 1000741) B1000741
theorem B1334339 : Blo 888571 1334339 := bstep (se 1 (by rfl) ⟨1000754, by rfl⟩ : syracuseStep 1334339 = 2001509) B2001509
theorem B1334369 : Blo 888571 1334369 := bstep (se 2 (by rfl) ⟨500388, by rfl⟩ : syracuseStep 1334369 = 1000777) B1000777
theorem B1334387 : Blo 888571 1334387 := bstep (se 1 (by rfl) ⟨1000790, by rfl⟩ : syracuseStep 1334387 = 2001581) B2001581
theorem B1334417 : Blo 888571 1334417 := bstep (se 2 (by rfl) ⟨500406, by rfl⟩ : syracuseStep 1334417 = 1000813) B1000813
theorem B2251921 : Blo 888571 2251921 := bstep (se 2 (by rfl) ⟨844470, by rfl⟩ : syracuseStep 2251921 = 1688941) B1688941
theorem B3005585 : Blo 888571 3005585 := bstep (se 2 (by rfl) ⟨1127094, by rfl⟩ : syracuseStep 3005585 = 2254189) B2254189
theorem B1334435 : Blo 888571 1334435 := bstep (se 1 (by rfl) ⟨1000826, by rfl⟩ : syracuseStep 1334435 = 2001653) B2001653
theorem B1334465 : Blo 888571 1334465 := bstep (se 2 (by rfl) ⟨500424, by rfl⟩ : syracuseStep 1334465 = 1000849) B1000849
theorem B1334483 : Blo 888571 1334483 := bstep (se 1 (by rfl) ⟨1000862, by rfl⟩ : syracuseStep 1334483 = 2001725) B2001725
theorem B4512995 : Blo 888571 4512995 := bstep (se 1 (by rfl) ⟨3384746, by rfl⟩ : syracuseStep 4512995 = 6769493) B6769493
theorem B1334513 : Blo 888571 1334513 := bstep (se 2 (by rfl) ⟨500442, by rfl⟩ : syracuseStep 1334513 = 1000885) B1000885
theorem B1334531 : Blo 888571 1334531 := bstep (se 1 (by rfl) ⟨1000898, by rfl⟩ : syracuseStep 1334531 = 2001797) B2001797
theorem B8543501 : Blo 888571 8543501 := bstep (se 3 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 8543501 = 3203813) B3203813
theorem B1334561 : Blo 888571 1334561 := bstep (se 2 (by rfl) ⟨500460, by rfl⟩ : syracuseStep 1334561 = 1000921) B1000921
theorem B1334579 : Blo 888571 1334579 := bstep (se 1 (by rfl) ⟨1000934, by rfl⟩ : syracuseStep 1334579 = 2001869) B2001869
theorem B1334609 : Blo 888571 1334609 := bstep (se 2 (by rfl) ⟨500478, by rfl⟩ : syracuseStep 1334609 = 1000957) B1000957
theorem B1334627 : Blo 888571 1334627 := bstep (se 1 (by rfl) ⟨1000970, by rfl⟩ : syracuseStep 1334627 = 2001941) B2001941
theorem B1334657 : Blo 888571 1334657 := bstep (se 2 (by rfl) ⟨500496, by rfl⟩ : syracuseStep 1334657 = 1000993) B1000993
theorem B1269121 : Blo 888571 1269121 := bstep (se 2 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 1269121 = 951841) B951841
theorem B1334675 : Blo 888571 1334675 := bstep (se 1 (by rfl) ⟨1001006, by rfl⟩ : syracuseStep 1334675 = 2002013) B2002013
theorem B2252195 : Blo 888571 2252195 := bstep (se 1 (by rfl) ⟨1689146, by rfl⟩ : syracuseStep 2252195 = 3378293) B3378293
theorem B1269155 : Blo 888571 1269155 := bstep (se 1 (by rfl) ⟨951866, by rfl⟩ : syracuseStep 1269155 = 1903733) B1903733
theorem B1334705 : Blo 888571 1334705 := bstep (se 2 (by rfl) ⟨500514, by rfl⟩ : syracuseStep 1334705 = 1001029) B1001029
theorem B1334723 : Blo 888571 1334723 := bstep (se 1 (by rfl) ⟨1001042, by rfl⟩ : syracuseStep 1334723 = 2002085) B2002085
theorem B1334753 : Blo 888571 1334753 := bstep (se 2 (by rfl) ⟨500532, by rfl⟩ : syracuseStep 1334753 = 1001065) B1001065
theorem B1334771 : Blo 888571 1334771 := bstep (se 1 (by rfl) ⟨1001078, by rfl⟩ : syracuseStep 1334771 = 2002157) B2002157
theorem B1334801 : Blo 888571 1334801 := bstep (se 2 (by rfl) ⟨500550, by rfl⟩ : syracuseStep 1334801 = 1001101) B1001101
theorem B1334819 : Blo 888571 1334819 := bstep (se 1 (by rfl) ⟨1001114, by rfl⟩ : syracuseStep 1334819 = 2002229) B2002229
theorem B1334849 : Blo 888571 1334849 := bstep (se 2 (by rfl) ⟨500568, by rfl⟩ : syracuseStep 1334849 = 1001137) B1001137
theorem B1334867 : Blo 888571 1334867 := bstep (se 1 (by rfl) ⟨1001150, by rfl⟩ : syracuseStep 1334867 = 2002301) B2002301
theorem B2252387 : Blo 888571 2252387 := bstep (se 1 (by rfl) ⟨1689290, by rfl⟩ : syracuseStep 2252387 = 3378581) B3378581
theorem B1334897 : Blo 888571 1334897 := bstep (se 2 (by rfl) ⟨500586, by rfl⟩ : syracuseStep 1334897 = 1001173) B1001173
theorem B1203841 : Blo 888571 1203841 := bstep (se 2 (by rfl) ⟨451440, by rfl⟩ : syracuseStep 1203841 = 902881) B902881
theorem B1334915 : Blo 888571 1334915 := bstep (se 1 (by rfl) ⟨1001186, by rfl⟩ : syracuseStep 1334915 = 2002373) B2002373
theorem B1334945 : Blo 888571 1334945 := bstep (se 2 (by rfl) ⟨500604, by rfl⟩ : syracuseStep 1334945 = 1001209) B1001209
theorem B3006125 : Blo 888571 3006125 := bstep (se 3 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 3006125 = 1127297) B1127297
theorem B1334963 : Blo 888571 1334963 := bstep (se 1 (by rfl) ⟨1001222, by rfl⟩ : syracuseStep 1334963 = 2002445) B2002445
theorem B1334993 : Blo 888571 1334993 := bstep (se 2 (by rfl) ⟨500622, by rfl⟩ : syracuseStep 1334993 = 1001245) B1001245
theorem B1335011 : Blo 888571 1335011 := bstep (se 1 (by rfl) ⟨1001258, by rfl⟩ : syracuseStep 1335011 = 2002517) B2002517
theorem B3006179 : Blo 888571 3006179 := bstep (se 1 (by rfl) ⟨2254634, by rfl⟩ : syracuseStep 3006179 = 4509269) B4509269
theorem B1335041 : Blo 888571 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B1335059 : Blo 888571 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B1335089 : Blo 888571 1335089 := bstep (se 2 (by rfl) ⟨500658, by rfl⟩ : syracuseStep 1335089 = 1001317) B1001317
theorem B1335107 : Blo 888571 1335107 := bstep (se 1 (by rfl) ⟨1001330, by rfl⟩ : syracuseStep 1335107 = 2002661) B2002661
theorem B1335137 : Blo 888571 1335137 := bstep (se 2 (by rfl) ⟨500676, by rfl⟩ : syracuseStep 1335137 = 1001353) B1001353
theorem B9756515 : Blo 888571 9756515 := bstep (se 1 (by rfl) ⟨7317386, by rfl⟩ : syracuseStep 9756515 = 14634773) B14634773
theorem B8576867 : Blo 888571 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B1335155 : Blo 888571 1335155 := bstep (se 1 (by rfl) ⟨1001366, by rfl⟩ : syracuseStep 1335155 = 2002733) B2002733
theorem B5791621 : Blo 888571 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B1335185 : Blo 888571 1335185 := bstep (se 2 (by rfl) ⟨500694, by rfl⟩ : syracuseStep 1335185 = 1001389) B1001389
theorem B1335203 : Blo 888571 1335203 := bstep (se 1 (by rfl) ⟨1001402, by rfl⟩ : syracuseStep 1335203 = 2002805) B2002805
theorem B4284323 : Blo 888571 4284323 := bstep (se 1 (by rfl) ⟨3213242, by rfl⟩ : syracuseStep 4284323 = 6426485) B6426485
theorem B1335233 : Blo 888571 1335233 := bstep (se 2 (by rfl) ⟨500712, by rfl⟩ : syracuseStep 1335233 = 1001425) B1001425
theorem B1269713 : Blo 888571 1269713 := bstep (se 2 (by rfl) ⟨476142, by rfl⟩ : syracuseStep 1269713 = 952285) B952285
theorem B1335251 : Blo 888571 1335251 := bstep (se 1 (by rfl) ⟨1001438, by rfl⟩ : syracuseStep 1335251 = 2002877) B2002877
theorem B1335281 : Blo 888571 1335281 := bstep (se 2 (by rfl) ⟨500730, by rfl⟩ : syracuseStep 1335281 = 1001461) B1001461
theorem B5070833 : Blo 888571 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B3006449 : Blo 888571 3006449 := bstep (se 2 (by rfl) ⟨1127418, by rfl⟩ : syracuseStep 3006449 = 2254837) B2254837
theorem B1335299 : Blo 888571 1335299 := bstep (se 1 (by rfl) ⟨1001474, by rfl⟩ : syracuseStep 1335299 = 2002949) B2002949
theorem B4513805 : Blo 888571 4513805 := bstep (se 3 (by rfl) ⟨846338, by rfl⟩ : syracuseStep 4513805 = 1692677) B1692677
theorem B1335329 : Blo 888571 1335329 := bstep (se 2 (by rfl) ⟨500748, by rfl⟩ : syracuseStep 1335329 = 1001497) B1001497
theorem B1269793 : Blo 888571 1269793 := bstep (se 2 (by rfl) ⟨476172, by rfl⟩ : syracuseStep 1269793 = 952345) B952345
theorem B1335347 : Blo 888571 1335347 := bstep (se 1 (by rfl) ⟨1001510, by rfl⟩ : syracuseStep 1335347 = 2003021) B2003021
theorem B1335377 : Blo 888571 1335377 := bstep (se 2 (by rfl) ⟨500766, by rfl⟩ : syracuseStep 1335377 = 1001533) B1001533
theorem B1335395 : Blo 888571 1335395 := bstep (se 1 (by rfl) ⟨1001546, by rfl⟩ : syracuseStep 1335395 = 2003093) B2003093
theorem B4284515 : Blo 888571 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B1335425 : Blo 888571 1335425 := bstep (se 2 (by rfl) ⟨500784, by rfl⟩ : syracuseStep 1335425 = 1001569) B1001569
theorem B1335443 : Blo 888571 1335443 := bstep (se 1 (by rfl) ⟨1001582, by rfl⟩ : syracuseStep 1335443 = 2003165) B2003165
theorem B1335473 : Blo 888571 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B1335491 : Blo 888571 1335491 := bstep (se 1 (by rfl) ⟨1001618, by rfl⟩ : syracuseStep 1335491 = 2003237) B2003237
theorem B1335521 : Blo 888571 1335521 := bstep (se 2 (by rfl) ⟨500820, by rfl⟩ : syracuseStep 1335521 = 1001641) B1001641
theorem B1335539 : Blo 888571 1335539 := bstep (se 1 (by rfl) ⟨1001654, by rfl⟩ : syracuseStep 1335539 = 2003309) B2003309
theorem B1335569 : Blo 888571 1335569 := bstep (se 2 (by rfl) ⟨500838, by rfl⟩ : syracuseStep 1335569 = 1001677) B1001677
theorem B1335587 : Blo 888571 1335587 := bstep (se 1 (by rfl) ⟨1001690, by rfl⟩ : syracuseStep 1335587 = 2003381) B2003381
theorem B1335617 : Blo 888571 1335617 := bstep (se 2 (by rfl) ⟨500856, by rfl⟩ : syracuseStep 1335617 = 1001713) B1001713
theorem B1335635 : Blo 888571 1335635 := bstep (se 1 (by rfl) ⟨1001726, by rfl⟩ : syracuseStep 1335635 = 2003453) B2003453
theorem B1335665 : Blo 888571 1335665 := bstep (se 2 (by rfl) ⟨500874, by rfl⟩ : syracuseStep 1335665 = 1001749) B1001749
theorem B975235 : Blo 888571 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B1335683 : Blo 888571 1335683 := bstep (se 1 (by rfl) ⟨1001762, by rfl⟩ : syracuseStep 1335683 = 2003525) B2003525
theorem B1499539 : Blo 888571 1499539 := bstep (se 1 (by rfl) ⟨1124654, by rfl⟩ : syracuseStep 1499539 = 2249309) B2249309
theorem B1335713 : Blo 888571 1335713 := bstep (se 2 (by rfl) ⟨500892, by rfl⟩ : syracuseStep 1335713 = 1001785) B1001785
theorem B1335731 : Blo 888571 1335731 := bstep (se 1 (by rfl) ⟨1001798, by rfl⟩ : syracuseStep 1335731 = 2003597) B2003597
theorem B1335761 : Blo 888571 1335761 := bstep (se 2 (by rfl) ⟨500910, by rfl⟩ : syracuseStep 1335761 = 1001821) B1001821
theorem B1925603 : Blo 888571 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B1335779 : Blo 888571 1335779 := bstep (se 1 (by rfl) ⟨1001834, by rfl⟩ : syracuseStep 1335779 = 2003669) B2003669
theorem B4284899 : Blo 888571 4284899 := bstep (se 1 (by rfl) ⟨3213674, by rfl⟩ : syracuseStep 4284899 = 6427349) B6427349
theorem B1335809 : Blo 888571 1335809 := bstep (se 2 (by rfl) ⟨500928, by rfl⟩ : syracuseStep 1335809 = 1001857) B1001857
theorem B3006989 : Blo 888571 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B2253329 : Blo 888571 2253329 := bstep (se 2 (by rfl) ⟨844998, by rfl⟩ : syracuseStep 2253329 = 1689997) B1689997
theorem B1335827 : Blo 888571 1335827 := bstep (se 1 (by rfl) ⟨1001870, by rfl⟩ : syracuseStep 1335827 = 2003741) B2003741
theorem B1499681 : Blo 888571 1499681 := bstep (se 2 (by rfl) ⟨562380, by rfl⟩ : syracuseStep 1499681 = 1124761) B1124761
theorem B1335857 : Blo 888571 1335857 := bstep (se 2 (by rfl) ⟨500946, by rfl⟩ : syracuseStep 1335857 = 1001893) B1001893
theorem B11395637 : Blo 888571 11395637 := bstep (se 5 (by rfl) ⟨534170, by rfl⟩ : syracuseStep 11395637 = 1068341) B1068341
theorem B2253379 : Blo 888571 2253379 := bstep (se 1 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 2253379 = 3380069) B3380069
theorem B1335875 : Blo 888571 1335875 := bstep (se 1 (by rfl) ⟨1001906, by rfl⟩ : syracuseStep 1335875 = 2003813) B2003813
theorem B3007043 : Blo 888571 3007043 := bstep (se 1 (by rfl) ⟨2255282, by rfl⟩ : syracuseStep 3007043 = 4510565) B4510565
theorem B1335905 : Blo 888571 1335905 := bstep (se 2 (by rfl) ⟨500964, by rfl⟩ : syracuseStep 1335905 = 1001929) B1001929
theorem B1335923 : Blo 888571 1335923 := bstep (se 1 (by rfl) ⟨1001942, by rfl⟩ : syracuseStep 1335923 = 2003885) B2003885
theorem B1335953 : Blo 888571 1335953 := bstep (se 2 (by rfl) ⟨500982, by rfl⟩ : syracuseStep 1335953 = 1001965) B1001965
theorem B1499809 : Blo 888571 1499809 := bstep (se 2 (by rfl) ⟨562428, by rfl⟩ : syracuseStep 1499809 = 1124857) B1124857
theorem B1335971 : Blo 888571 1335971 := bstep (se 1 (by rfl) ⟨1001978, by rfl⟩ : syracuseStep 1335971 = 2003957) B2003957
theorem B1336001 : Blo 888571 1336001 := bstep (se 2 (by rfl) ⟨501000, by rfl⟩ : syracuseStep 1336001 = 1002001) B1002001
theorem B1499843 : Blo 888571 1499843 := bstep (se 1 (by rfl) ⟨1124882, by rfl⟩ : syracuseStep 1499843 = 2249765) B2249765
theorem B2253521 : Blo 888571 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B1336019 : Blo 888571 1336019 := bstep (se 1 (by rfl) ⟨1002014, by rfl⟩ : syracuseStep 1336019 = 2004029) B2004029
theorem B1336049 : Blo 888571 1336049 := bstep (se 2 (by rfl) ⟨501018, by rfl⟩ : syracuseStep 1336049 = 1002037) B1002037
theorem B2712305 : Blo 888571 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B1336067 : Blo 888571 1336067 := bstep (se 1 (by rfl) ⟨1002050, by rfl⟩ : syracuseStep 1336067 = 2004101) B2004101
theorem B1336097 : Blo 888571 1336097 := bstep (se 2 (by rfl) ⟨501036, by rfl⟩ : syracuseStep 1336097 = 1002073) B1002073
theorem B1336115 : Blo 888571 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B1270579 : Blo 888571 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1499971 : Blo 888571 1499971 := bstep (se 1 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 1499971 = 2249957) B2249957
theorem B1336145 : Blo 888571 1336145 := bstep (se 2 (by rfl) ⟨501054, by rfl⟩ : syracuseStep 1336145 = 1002109) B1002109
theorem B3007313 : Blo 888571 3007313 := bstep (se 2 (by rfl) ⟨1127742, by rfl⟩ : syracuseStep 3007313 = 2255485) B2255485
theorem B1336163 : Blo 888571 1336163 := bstep (se 1 (by rfl) ⟨1002122, by rfl⟩ : syracuseStep 1336163 = 2004245) B2004245
theorem B1336193 : Blo 888571 1336193 := bstep (se 2 (by rfl) ⟨501072, by rfl⟩ : syracuseStep 1336193 = 1002145) B1002145
theorem B1336211 : Blo 888571 1336211 := bstep (se 1 (by rfl) ⟨1002158, by rfl⟩ : syracuseStep 1336211 = 2004317) B2004317
theorem B1336241 : Blo 888571 1336241 := bstep (se 2 (by rfl) ⟨501090, by rfl⟩ : syracuseStep 1336241 = 1002181) B1002181
theorem B1336259 : Blo 888571 1336259 := bstep (se 1 (by rfl) ⟨1002194, by rfl⟩ : syracuseStep 1336259 = 2004389) B2004389
theorem B1500113 : Blo 888571 1500113 := bstep (se 2 (by rfl) ⟨562542, by rfl⟩ : syracuseStep 1500113 = 1125085) B1125085
theorem B1336289 : Blo 888571 1336289 := bstep (se 2 (by rfl) ⟨501108, by rfl⟩ : syracuseStep 1336289 = 1002217) B1002217
theorem B1336307 : Blo 888571 1336307 := bstep (se 1 (by rfl) ⟨1002230, by rfl⟩ : syracuseStep 1336307 = 2004461) B2004461
theorem B1336337 : Blo 888571 1336337 := bstep (se 2 (by rfl) ⟨501126, by rfl⟩ : syracuseStep 1336337 = 1002253) B1002253
theorem B1336355 : Blo 888571 1336355 := bstep (se 1 (by rfl) ⟨1002266, by rfl⟩ : syracuseStep 1336355 = 2004533) B2004533
theorem B1336385 : Blo 888571 1336385 := bstep (se 2 (by rfl) ⟨501144, by rfl⟩ : syracuseStep 1336385 = 1002289) B1002289
theorem B1500241 : Blo 888571 1500241 := bstep (se 2 (by rfl) ⟨562590, by rfl⟩ : syracuseStep 1500241 = 1125181) B1125181
theorem B1336403 : Blo 888571 1336403 := bstep (se 1 (by rfl) ⟨1002302, by rfl⟩ : syracuseStep 1336403 = 2004605) B2004605
theorem B1336433 : Blo 888571 1336433 := bstep (se 2 (by rfl) ⟨501162, by rfl⟩ : syracuseStep 1336433 = 1002325) B1002325
theorem B1500275 : Blo 888571 1500275 := bstep (se 1 (by rfl) ⟨1125206, by rfl⟩ : syracuseStep 1500275 = 2250413) B2250413
theorem B1336451 : Blo 888571 1336451 := bstep (se 1 (by rfl) ⟨1002338, by rfl⟩ : syracuseStep 1336451 = 2004677) B2004677
theorem B1336481 : Blo 888571 1336481 := bstep (se 2 (by rfl) ⟨501180, by rfl⟩ : syracuseStep 1336481 = 1002361) B1002361
theorem B1336499 : Blo 888571 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B12838085 : Blo 888571 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B1336529 : Blo 888571 1336529 := bstep (se 2 (by rfl) ⟨501198, by rfl⟩ : syracuseStep 1336529 = 1002397) B1002397
theorem B1336547 : Blo 888571 1336547 := bstep (se 1 (by rfl) ⟨1002410, by rfl⟩ : syracuseStep 1336547 = 2004821) B2004821
theorem B1500403 : Blo 888571 1500403 := bstep (se 1 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 1500403 = 2250605) B2250605
theorem B1336577 : Blo 888571 1336577 := bstep (se 2 (by rfl) ⟨501216, by rfl⟩ : syracuseStep 1336577 = 1002433) B1002433
theorem B1336595 : Blo 888571 1336595 := bstep (se 1 (by rfl) ⟨1002446, by rfl⟩ : syracuseStep 1336595 = 2004893) B2004893
theorem B1336625 : Blo 888571 1336625 := bstep (se 2 (by rfl) ⟨501234, by rfl⟩ : syracuseStep 1336625 = 1002469) B1002469
theorem B1336643 : Blo 888571 1336643 := bstep (se 1 (by rfl) ⟨1002482, by rfl⟩ : syracuseStep 1336643 = 2004965) B2004965
theorem B1336673 : Blo 888571 1336673 := bstep (se 2 (by rfl) ⟨501252, by rfl⟩ : syracuseStep 1336673 = 1002505) B1002505
theorem B1140067 : Blo 888571 1140067 := bstep (se 1 (by rfl) ⟨855050, by rfl⟩ : syracuseStep 1140067 = 1710101) B1710101
theorem B3007853 : Blo 888571 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B1336691 : Blo 888571 1336691 := bstep (se 1 (by rfl) ⟨1002518, by rfl⟩ : syracuseStep 1336691 = 2005037) B2005037
theorem B1500545 : Blo 888571 1500545 := bstep (se 2 (by rfl) ⟨562704, by rfl⟩ : syracuseStep 1500545 = 1125409) B1125409
theorem B1336721 : Blo 888571 1336721 := bstep (se 2 (by rfl) ⟨501270, by rfl⟩ : syracuseStep 1336721 = 1002541) B1002541
theorem B5072291 : Blo 888571 5072291 := bstep (se 1 (by rfl) ⟨3804218, by rfl⟩ : syracuseStep 5072291 = 7608437) B7608437
theorem B1336739 : Blo 888571 1336739 := bstep (se 1 (by rfl) ⟨1002554, by rfl⟩ : syracuseStep 1336739 = 2005109) B2005109
theorem B3007907 : Blo 888571 3007907 := bstep (se 1 (by rfl) ⟨2255930, by rfl⟩ : syracuseStep 3007907 = 4511861) B4511861
theorem B1336769 : Blo 888571 1336769 := bstep (se 2 (by rfl) ⟨501288, by rfl⟩ : syracuseStep 1336769 = 1002577) B1002577
theorem B92431813 : Blo 888571 92431813 := bstep (se 4 (by rfl) ⟨8665482, by rfl⟩ : syracuseStep 92431813 = 17330965) B17330965
theorem B1336787 : Blo 888571 1336787 := bstep (se 1 (by rfl) ⟨1002590, by rfl⟩ : syracuseStep 1336787 = 2005181) B2005181
theorem B3204593 : Blo 888571 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B1336817 : Blo 888571 1336817 := bstep (se 2 (by rfl) ⟨501306, by rfl⟩ : syracuseStep 1336817 = 1002613) B1002613
theorem B1500673 : Blo 888571 1500673 := bstep (se 2 (by rfl) ⟨562752, by rfl⟩ : syracuseStep 1500673 = 1125505) B1125505
theorem B1336835 : Blo 888571 1336835 := bstep (se 1 (by rfl) ⟨1002626, by rfl⟩ : syracuseStep 1336835 = 2005253) B2005253
theorem B1467907 : Blo 888571 1467907 := bstep (se 1 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 1467907 = 2201861) B2201861
theorem B1336865 : Blo 888571 1336865 := bstep (se 2 (by rfl) ⟨501324, by rfl⟩ : syracuseStep 1336865 = 1002649) B1002649
theorem B1500707 : Blo 888571 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B1336883 : Blo 888571 1336883 := bstep (se 1 (by rfl) ⟨1002662, by rfl⟩ : syracuseStep 1336883 = 2005325) B2005325
theorem B1336913 : Blo 888571 1336913 := bstep (se 2 (by rfl) ⟨501342, by rfl⟩ : syracuseStep 1336913 = 1002685) B1002685
theorem B1336931 : Blo 888571 1336931 := bstep (se 1 (by rfl) ⟨1002698, by rfl⟩ : syracuseStep 1336931 = 2005397) B2005397
theorem B1336961 : Blo 888571 1336961 := bstep (se 2 (by rfl) ⟨501360, by rfl⟩ : syracuseStep 1336961 = 1002721) B1002721
theorem B1336979 : Blo 888571 1336979 := bstep (se 1 (by rfl) ⟨1002734, by rfl⟩ : syracuseStep 1336979 = 2005469) B2005469
theorem B1500835 : Blo 888571 1500835 := bstep (se 1 (by rfl) ⟨1125626, by rfl⟩ : syracuseStep 1500835 = 2251253) B2251253
theorem B2254513 : Blo 888571 2254513 := bstep (se 2 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 2254513 = 1690885) B1690885
theorem B3008177 : Blo 888571 3008177 := bstep (se 2 (by rfl) ⟨1128066, by rfl⟩ : syracuseStep 3008177 = 2256133) B2256133
theorem B1337009 : Blo 888571 1337009 := bstep (se 2 (by rfl) ⟨501378, by rfl⟩ : syracuseStep 1337009 = 1002757) B1002757
theorem B1337027 : Blo 888571 1337027 := bstep (se 1 (by rfl) ⟨1002770, by rfl⟩ : syracuseStep 1337027 = 2005541) B2005541
theorem B1337057 : Blo 888571 1337057 := bstep (se 2 (by rfl) ⟨501396, by rfl⟩ : syracuseStep 1337057 = 1002793) B1002793
theorem B1337075 : Blo 888571 1337075 := bstep (se 1 (by rfl) ⟨1002806, by rfl⟩ : syracuseStep 1337075 = 2005613) B2005613
theorem B1337105 : Blo 888571 1337105 := bstep (se 2 (by rfl) ⟨501414, by rfl⟩ : syracuseStep 1337105 = 1002829) B1002829
theorem B1337123 : Blo 888571 1337123 := bstep (se 1 (by rfl) ⟨1002842, by rfl⟩ : syracuseStep 1337123 = 2005685) B2005685
theorem B1500977 : Blo 888571 1500977 := bstep (se 2 (by rfl) ⟨562866, by rfl⟩ : syracuseStep 1500977 = 1125733) B1125733
theorem B1337153 : Blo 888571 1337153 := bstep (se 2 (by rfl) ⟨501432, by rfl⟩ : syracuseStep 1337153 = 1002865) B1002865
theorem B1337171 : Blo 888571 1337171 := bstep (se 1 (by rfl) ⟨1002878, by rfl⟩ : syracuseStep 1337171 = 2005757) B2005757
theorem B14444401 : Blo 888571 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B1337201 : Blo 888571 1337201 := bstep (se 2 (by rfl) ⟨501450, by rfl⟩ : syracuseStep 1337201 = 1002901) B1002901
theorem B1337219 : Blo 888571 1337219 := bstep (se 1 (by rfl) ⟨1002914, by rfl⟩ : syracuseStep 1337219 = 2005829) B2005829
theorem B2713475 : Blo 888571 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B1337249 : Blo 888571 1337249 := bstep (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) B1002937
theorem B2287523 : Blo 888571 2287523 := bstep (se 1 (by rfl) ⟨1715642, by rfl⟩ : syracuseStep 2287523 = 3431285) B3431285
theorem B1501105 : Blo 888571 1501105 := bstep (se 2 (by rfl) ⟨562914, by rfl⟩ : syracuseStep 1501105 = 1125829) B1125829
theorem B1337267 : Blo 888571 1337267 := bstep (se 1 (by rfl) ⟨1002950, by rfl⟩ : syracuseStep 1337267 = 2005901) B2005901
theorem B2254787 : Blo 888571 2254787 := bstep (se 1 (by rfl) ⟨1691090, by rfl⟩ : syracuseStep 2254787 = 3382181) B3382181
theorem B1337297 : Blo 888571 1337297 := bstep (se 2 (by rfl) ⟨501486, by rfl⟩ : syracuseStep 1337297 = 1002973) B1002973
theorem B1501139 : Blo 888571 1501139 := bstep (se 1 (by rfl) ⟨1125854, by rfl⟩ : syracuseStep 1501139 = 2251709) B2251709
theorem B1337315 : Blo 888571 1337315 := bstep (se 1 (by rfl) ⟨1002986, by rfl⟩ : syracuseStep 1337315 = 2005973) B2005973
theorem B1337345 : Blo 888571 1337345 := bstep (se 2 (by rfl) ⟨501504, by rfl⟩ : syracuseStep 1337345 = 1003009) B1003009
theorem B1337363 : Blo 888571 1337363 := bstep (se 1 (by rfl) ⟨1003022, by rfl⟩ : syracuseStep 1337363 = 2006045) B2006045
theorem B1337393 : Blo 888571 1337393 := bstep (se 2 (by rfl) ⟨501522, by rfl⟩ : syracuseStep 1337393 = 1003045) B1003045
theorem B4286513 : Blo 888571 4286513 := bstep (se 2 (by rfl) ⟨1607442, by rfl⟩ : syracuseStep 4286513 = 3214885) B3214885
theorem B1337411 : Blo 888571 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B1501267 : Blo 888571 1501267 := bstep (se 1 (by rfl) ⟨1125950, by rfl⟩ : syracuseStep 1501267 = 2251901) B2251901
theorem B1337441 : Blo 888571 1337441 := bstep (se 2 (by rfl) ⟨501540, by rfl⟩ : syracuseStep 1337441 = 1003081) B1003081
theorem B1337459 : Blo 888571 1337459 := bstep (se 1 (by rfl) ⟨1003094, by rfl⟩ : syracuseStep 1337459 = 2006189) B2006189
theorem B2254979 : Blo 888571 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B1337489 : Blo 888571 1337489 := bstep (se 2 (by rfl) ⟨501558, by rfl⟩ : syracuseStep 1337489 = 1003117) B1003117
theorem B1337507 : Blo 888571 1337507 := bstep (se 1 (by rfl) ⟨1003130, by rfl⟩ : syracuseStep 1337507 = 2006261) B2006261
theorem B1337537 : Blo 888571 1337537 := bstep (se 2 (by rfl) ⟨501576, by rfl⟩ : syracuseStep 1337537 = 1003153) B1003153
theorem B3008717 : Blo 888571 3008717 := bstep (se 3 (by rfl) ⟨564134, by rfl⟩ : syracuseStep 3008717 = 1128269) B1128269
theorem B1337555 : Blo 888571 1337555 := bstep (se 1 (by rfl) ⟨1003166, by rfl⟩ : syracuseStep 1337555 = 2006333) B2006333
theorem B1501409 : Blo 888571 1501409 := bstep (se 2 (by rfl) ⟨563028, by rfl⟩ : syracuseStep 1501409 = 1126057) B1126057
theorem B1337585 : Blo 888571 1337585 := bstep (se 2 (by rfl) ⟨501594, by rfl⟩ : syracuseStep 1337585 = 1003189) B1003189
theorem B3008771 : Blo 888571 3008771 := bstep (se 1 (by rfl) ⟨2256578, by rfl⟩ : syracuseStep 3008771 = 4513157) B4513157
theorem B1337603 : Blo 888571 1337603 := bstep (se 1 (by rfl) ⟨1003202, by rfl⟩ : syracuseStep 1337603 = 2006405) B2006405
theorem B1337633 : Blo 888571 1337633 := bstep (se 2 (by rfl) ⟨501612, by rfl⟩ : syracuseStep 1337633 = 1003225) B1003225
theorem B1337651 : Blo 888571 1337651 := bstep (se 1 (by rfl) ⟨1003238, by rfl⟩ : syracuseStep 1337651 = 2006477) B2006477
theorem B1337681 : Blo 888571 1337681 := bstep (se 2 (by rfl) ⟨501630, by rfl⟩ : syracuseStep 1337681 = 1003261) B1003261
theorem B1501537 : Blo 888571 1501537 := bstep (se 2 (by rfl) ⟨563076, by rfl⟩ : syracuseStep 1501537 = 1126153) B1126153
theorem B1337699 : Blo 888571 1337699 := bstep (se 1 (by rfl) ⟨1003274, by rfl⟩ : syracuseStep 1337699 = 2006549) B2006549
theorem B1337729 : Blo 888571 1337729 := bstep (se 2 (by rfl) ⟨501648, by rfl⟩ : syracuseStep 1337729 = 1003297) B1003297
theorem B1501571 : Blo 888571 1501571 := bstep (se 1 (by rfl) ⟨1126178, by rfl⟩ : syracuseStep 1501571 = 2252357) B2252357
theorem B5073293 : Blo 888571 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B1337747 : Blo 888571 1337747 := bstep (se 1 (by rfl) ⟨1003310, by rfl⟩ : syracuseStep 1337747 = 2006621) B2006621
theorem B1337777 : Blo 888571 1337777 := bstep (se 2 (by rfl) ⟨501666, by rfl⟩ : syracuseStep 1337777 = 1003333) B1003333
theorem B4286897 : Blo 888571 4286897 := bstep (se 2 (by rfl) ⟨1607586, by rfl⟩ : syracuseStep 4286897 = 3215173) B3215173
theorem B1337795 : Blo 888571 1337795 := bstep (se 1 (by rfl) ⟨1003346, by rfl⟩ : syracuseStep 1337795 = 2006693) B2006693
theorem B4811213 : Blo 888571 4811213 := bstep (se 3 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 4811213 = 1804205) B1804205
theorem B1337825 : Blo 888571 1337825 := bstep (se 2 (by rfl) ⟨501684, by rfl⟩ : syracuseStep 1337825 = 1003369) B1003369
theorem B1337843 : Blo 888571 1337843 := bstep (se 1 (by rfl) ⟨1003382, by rfl⟩ : syracuseStep 1337843 = 2006765) B2006765
theorem B1501699 : Blo 888571 1501699 := bstep (se 1 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 1501699 = 2252549) B2252549
theorem B3009041 : Blo 888571 3009041 := bstep (se 2 (by rfl) ⟨1128390, by rfl⟩ : syracuseStep 3009041 = 2256781) B2256781
theorem B1337873 : Blo 888571 1337873 := bstep (se 2 (by rfl) ⟨501702, by rfl⟩ : syracuseStep 1337873 = 1003405) B1003405
theorem B1337891 : Blo 888571 1337891 := bstep (se 1 (by rfl) ⟨1003418, by rfl⟩ : syracuseStep 1337891 = 2006837) B2006837
theorem B1337921 : Blo 888571 1337921 := bstep (se 2 (by rfl) ⟨501720, by rfl⟩ : syracuseStep 1337921 = 1003441) B1003441
theorem B4811341 : Blo 888571 4811341 := bstep (se 3 (by rfl) ⟨902126, by rfl⟩ : syracuseStep 4811341 = 1804253) B1804253
theorem B1337939 : Blo 888571 1337939 := bstep (se 1 (by rfl) ⟨1003454, by rfl⟩ : syracuseStep 1337939 = 2006909) B2006909
theorem B1337969 : Blo 888571 1337969 := bstep (se 2 (by rfl) ⟨501738, by rfl⟩ : syracuseStep 1337969 = 1003477) B1003477
theorem B1337987 : Blo 888571 1337987 := bstep (se 1 (by rfl) ⟨1003490, by rfl⟩ : syracuseStep 1337987 = 2006981) B2006981
theorem B1501841 : Blo 888571 1501841 := bstep (se 2 (by rfl) ⟨563190, by rfl⟩ : syracuseStep 1501841 = 1126381) B1126381
theorem B1338017 : Blo 888571 1338017 := bstep (se 2 (by rfl) ⟨501756, by rfl⟩ : syracuseStep 1338017 = 1003513) B1003513
theorem B1338035 : Blo 888571 1338035 := bstep (se 1 (by rfl) ⟨1003526, by rfl⟩ : syracuseStep 1338035 = 2007053) B2007053
theorem B1338065 : Blo 888571 1338065 := bstep (se 2 (by rfl) ⟨501774, by rfl⟩ : syracuseStep 1338065 = 1003549) B1003549
theorem B1338083 : Blo 888571 1338083 := bstep (se 1 (by rfl) ⟨1003562, by rfl⟩ : syracuseStep 1338083 = 2007125) B2007125
theorem B1338113 : Blo 888571 1338113 := bstep (se 2 (by rfl) ⟨501792, by rfl⟩ : syracuseStep 1338113 = 1003585) B1003585
theorem B1501969 : Blo 888571 1501969 := bstep (se 2 (by rfl) ⟨563238, by rfl⟩ : syracuseStep 1501969 = 1126477) B1126477
theorem B1338131 : Blo 888571 1338131 := bstep (se 1 (by rfl) ⟨1003598, by rfl⟩ : syracuseStep 1338131 = 2007197) B2007197
theorem B1338161 : Blo 888571 1338161 := bstep (se 2 (by rfl) ⟨501810, by rfl⟩ : syracuseStep 1338161 = 1003621) B1003621
theorem B1502003 : Blo 888571 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1338179 : Blo 888571 1338179 := bstep (se 1 (by rfl) ⟨1003634, by rfl⟩ : syracuseStep 1338179 = 2007269) B2007269
theorem B1338209 : Blo 888571 1338209 := bstep (se 2 (by rfl) ⟨501828, by rfl⟩ : syracuseStep 1338209 = 1003657) B1003657
theorem B3042161 : Blo 888571 3042161 := bstep (se 2 (by rfl) ⟨1140810, by rfl⟩ : syracuseStep 3042161 = 2281621) B2281621
theorem B4516721 : Blo 888571 4516721 := bstep (se 2 (by rfl) ⟨1693770, by rfl⟩ : syracuseStep 4516721 = 3387541) B3387541
theorem B1338227 : Blo 888571 1338227 := bstep (se 1 (by rfl) ⟨1003670, by rfl⟩ : syracuseStep 1338227 = 2007341) B2007341
theorem B1338257 : Blo 888571 1338257 := bstep (se 2 (by rfl) ⟨501846, by rfl⟩ : syracuseStep 1338257 = 1003693) B1003693
theorem B1338275 : Blo 888571 1338275 := bstep (se 1 (by rfl) ⟨1003706, by rfl⟩ : syracuseStep 1338275 = 2007413) B2007413
theorem B1502131 : Blo 888571 1502131 := bstep (se 1 (by rfl) ⟨1126598, by rfl⟩ : syracuseStep 1502131 = 2253197) B2253197
theorem B1338305 : Blo 888571 1338305 := bstep (se 2 (by rfl) ⟨501864, by rfl⟩ : syracuseStep 1338305 = 1003729) B1003729
theorem B4287437 : Blo 888571 4287437 := bstep (se 3 (by rfl) ⟨803894, by rfl⟩ : syracuseStep 4287437 = 1607789) B1607789
theorem B1338323 : Blo 888571 1338323 := bstep (se 1 (by rfl) ⟨1003742, by rfl⟩ : syracuseStep 1338323 = 2007485) B2007485
theorem B1338353 : Blo 888571 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B1338371 : Blo 888571 1338371 := bstep (se 1 (by rfl) ⟨1003778, by rfl⟩ : syracuseStep 1338371 = 2007557) B2007557
theorem B1338401 : Blo 888571 1338401 := bstep (se 2 (by rfl) ⟨501900, by rfl⟩ : syracuseStep 1338401 = 1003801) B1003801
theorem B3009581 : Blo 888571 3009581 := bstep (se 3 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 3009581 = 1128593) B1128593
theorem B2255921 : Blo 888571 2255921 := bstep (se 2 (by rfl) ⟨845970, by rfl⟩ : syracuseStep 2255921 = 1691941) B1691941
theorem B1338419 : Blo 888571 1338419 := bstep (se 1 (by rfl) ⟨1003814, by rfl⟩ : syracuseStep 1338419 = 2007629) B2007629
theorem B1502273 : Blo 888571 1502273 := bstep (se 2 (by rfl) ⟨563352, by rfl⟩ : syracuseStep 1502273 = 1126705) B1126705
theorem B1338449 : Blo 888571 1338449 := bstep (se 2 (by rfl) ⟨501918, by rfl⟩ : syracuseStep 1338449 = 1003837) B1003837
theorem B2255971 : Blo 888571 2255971 := bstep (se 1 (by rfl) ⟨1691978, by rfl⟩ : syracuseStep 2255971 = 3383957) B3383957
theorem B3009635 : Blo 888571 3009635 := bstep (se 1 (by rfl) ⟨2257226, by rfl⟩ : syracuseStep 3009635 = 4514453) B4514453
theorem B1338467 : Blo 888571 1338467 := bstep (se 1 (by rfl) ⟨1003850, by rfl⟩ : syracuseStep 1338467 = 2007701) B2007701
theorem B1338497 : Blo 888571 1338497 := bstep (se 2 (by rfl) ⟨501936, by rfl⟩ : syracuseStep 1338497 = 1003873) B1003873
theorem B1338515 : Blo 888571 1338515 := bstep (se 1 (by rfl) ⟨1003886, by rfl⟩ : syracuseStep 1338515 = 2007773) B2007773
theorem B1338545 : Blo 888571 1338545 := bstep (se 2 (by rfl) ⟨501954, by rfl⟩ : syracuseStep 1338545 = 1003909) B1003909
theorem B1502401 : Blo 888571 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B1338563 : Blo 888571 1338563 := bstep (se 1 (by rfl) ⟨1003922, by rfl⟩ : syracuseStep 1338563 = 2007845) B2007845
theorem B1338593 : Blo 888571 1338593 := bstep (se 2 (by rfl) ⟨501972, by rfl⟩ : syracuseStep 1338593 = 1003945) B1003945
theorem B1502435 : Blo 888571 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B2256113 : Blo 888571 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B1338611 : Blo 888571 1338611 := bstep (se 1 (by rfl) ⟨1003958, by rfl⟩ : syracuseStep 1338611 = 2007917) B2007917
theorem B1338641 : Blo 888571 1338641 := bstep (se 2 (by rfl) ⟨501990, by rfl⟩ : syracuseStep 1338641 = 1003981) B1003981
theorem B1338659 : Blo 888571 1338659 := bstep (se 1 (by rfl) ⟨1003994, by rfl⟩ : syracuseStep 1338659 = 2007989) B2007989
theorem B1338689 : Blo 888571 1338689 := bstep (se 2 (by rfl) ⟨502008, by rfl⟩ : syracuseStep 1338689 = 1004017) B1004017
theorem B1338707 : Blo 888571 1338707 := bstep (se 1 (by rfl) ⟨1004030, by rfl⟩ : syracuseStep 1338707 = 2008061) B2008061
theorem B1502563 : Blo 888571 1502563 := bstep (se 1 (by rfl) ⟨1126922, by rfl⟩ : syracuseStep 1502563 = 2253845) B2253845
theorem B3009905 : Blo 888571 3009905 := bstep (se 2 (by rfl) ⟨1128714, by rfl⟩ : syracuseStep 3009905 = 2257429) B2257429
theorem B1338737 : Blo 888571 1338737 := bstep (se 2 (by rfl) ⟨502026, by rfl⟩ : syracuseStep 1338737 = 1004053) B1004053
theorem B1338755 : Blo 888571 1338755 := bstep (se 1 (by rfl) ⟨1004066, by rfl⟩ : syracuseStep 1338755 = 2008133) B2008133
theorem B1338785 : Blo 888571 1338785 := bstep (se 2 (by rfl) ⟨502044, by rfl⟩ : syracuseStep 1338785 = 1004089) B1004089
theorem B1338803 : Blo 888571 1338803 := bstep (se 1 (by rfl) ⟨1004102, by rfl⟩ : syracuseStep 1338803 = 2008205) B2008205
theorem B2289091 : Blo 888571 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B1338833 : Blo 888571 1338833 := bstep (se 2 (by rfl) ⟨502062, by rfl⟩ : syracuseStep 1338833 = 1004125) B1004125
theorem B1338851 : Blo 888571 1338851 := bstep (se 1 (by rfl) ⟨1004138, by rfl⟩ : syracuseStep 1338851 = 2008277) B2008277
theorem B1502705 : Blo 888571 1502705 := bstep (se 2 (by rfl) ⟨563514, by rfl⟩ : syracuseStep 1502705 = 1127029) B1127029
theorem B8678897 : Blo 888571 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B1502833 : Blo 888571 1502833 := bstep (se 2 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 1502833 = 1127125) B1127125
theorem B1502867 : Blo 888571 1502867 := bstep (se 1 (by rfl) ⟨1127150, by rfl⟩ : syracuseStep 1502867 = 2254301) B2254301
theorem B4878085 : Blo 888571 4878085 := bstep (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) B914641
theorem B1502995 : Blo 888571 1502995 := bstep (se 1 (by rfl) ⟨1127246, by rfl⟩ : syracuseStep 1502995 = 2254493) B2254493
theorem B3010445 : Blo 888571 3010445 := bstep (se 3 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 3010445 = 1128917) B1128917
theorem B1503137 : Blo 888571 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B3010499 : Blo 888571 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B1503265 : Blo 888571 1503265 := bstep (se 2 (by rfl) ⟨563724, by rfl⟩ : syracuseStep 1503265 = 1127449) B1127449
theorem B3797027 : Blo 888571 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B1503299 : Blo 888571 1503299 := bstep (se 1 (by rfl) ⟨1127474, by rfl⟩ : syracuseStep 1503299 = 2254949) B2254949
theorem B4288589 : Blo 888571 4288589 := bstep (se 3 (by rfl) ⟨804110, by rfl⟩ : syracuseStep 4288589 = 1608221) B1608221
theorem B1503427 : Blo 888571 1503427 := bstep (se 1 (by rfl) ⟨1127570, by rfl⟩ : syracuseStep 1503427 = 2255141) B2255141
theorem B2257105 : Blo 888571 2257105 := bstep (se 2 (by rfl) ⟨846414, by rfl⟩ : syracuseStep 2257105 = 1692829) B1692829
theorem B3010769 : Blo 888571 3010769 := bstep (se 2 (by rfl) ⟨1129038, by rfl⟩ : syracuseStep 3010769 = 2258077) B2258077
theorem B4878563 : Blo 888571 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B4518179 : Blo 888571 4518179 := bstep (se 1 (by rfl) ⟨3388634, by rfl⟩ : syracuseStep 4518179 = 6777269) B6777269
theorem B1503569 : Blo 888571 1503569 := bstep (se 2 (by rfl) ⟨563838, by rfl⟩ : syracuseStep 1503569 = 1127677) B1127677
theorem B5140849 : Blo 888571 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B1503697 : Blo 888571 1503697 := bstep (se 2 (by rfl) ⟨563886, by rfl⟩ : syracuseStep 1503697 = 1127773) B1127773
theorem B17134051 : Blo 888571 17134051 := bstep (se 1 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 17134051 = 25701077) B25701077
theorem B2257379 : Blo 888571 2257379 := bstep (se 1 (by rfl) ⟨1693034, by rfl⟩ : syracuseStep 2257379 = 3386069) B3386069
theorem B1503731 : Blo 888571 1503731 := bstep (se 1 (by rfl) ⟨1127798, by rfl⟩ : syracuseStep 1503731 = 2255597) B2255597
theorem B1503859 : Blo 888571 1503859 := bstep (se 1 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 1503859 = 2255789) B2255789
theorem B2257571 : Blo 888571 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B3011309 : Blo 888571 3011309 := bstep (se 3 (by rfl) ⟨564620, by rfl⟩ : syracuseStep 3011309 = 1129241) B1129241
theorem B1504001 : Blo 888571 1504001 := bstep (se 2 (by rfl) ⟨564000, by rfl⟩ : syracuseStep 1504001 = 1128001) B1128001
theorem B3011363 : Blo 888571 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B8549189 : Blo 888571 8549189 := bstep (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) B1602973
theorem B2847565 : Blo 888571 2847565 := bstep (se 3 (by rfl) ⟨533918, by rfl⟩ : syracuseStep 2847565 = 1067837) B1067837
theorem B1504129 : Blo 888571 1504129 := bstep (se 2 (by rfl) ⟨564048, by rfl⟩ : syracuseStep 1504129 = 1128097) B1128097
theorem B2847629 : Blo 888571 2847629 := bstep (se 3 (by rfl) ⟨533930, by rfl⟩ : syracuseStep 2847629 = 1067861) B1067861
theorem B1504163 : Blo 888571 1504163 := bstep (se 1 (by rfl) ⟨1128122, by rfl⟩ : syracuseStep 1504163 = 2256245) B2256245
theorem B1504291 : Blo 888571 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B3011633 : Blo 888571 3011633 := bstep (se 2 (by rfl) ⟨1129362, by rfl⟩ : syracuseStep 3011633 = 2258725) B2258725
theorem B1504433 : Blo 888571 1504433 := bstep (se 2 (by rfl) ⟨564162, by rfl⟩ : syracuseStep 1504433 = 1128325) B1128325
theorem B3044557 : Blo 888571 3044557 := bstep (se 3 (by rfl) ⟨570854, by rfl⟩ : syracuseStep 3044557 = 1141709) B1141709
theorem B5076209 : Blo 888571 5076209 := bstep (se 2 (by rfl) ⟨1903578, by rfl⟩ : syracuseStep 5076209 = 3807157) B3807157
theorem B1504561 : Blo 888571 1504561 := bstep (se 2 (by rfl) ⟨564210, by rfl⟩ : syracuseStep 1504561 = 1128421) B1128421
theorem B1504595 : Blo 888571 1504595 := bstep (se 1 (by rfl) ⟨1128446, by rfl⟩ : syracuseStep 1504595 = 2256893) B2256893
theorem B1504723 : Blo 888571 1504723 := bstep (se 1 (by rfl) ⟨1128542, by rfl⟩ : syracuseStep 1504723 = 2257085) B2257085
theorem B5404195 : Blo 888571 5404195 := bstep (se 1 (by rfl) ⟨4053146, by rfl⟩ : syracuseStep 5404195 = 8106293) B8106293
theorem B3012173 : Blo 888571 3012173 := bstep (se 3 (by rfl) ⟨564782, by rfl⟩ : syracuseStep 3012173 = 1129565) B1129565
theorem B2258513 : Blo 888571 2258513 := bstep (se 2 (by rfl) ⟨846942, by rfl⟩ : syracuseStep 2258513 = 1693885) B1693885
theorem B1504865 : Blo 888571 1504865 := bstep (se 2 (by rfl) ⟨564324, by rfl⟩ : syracuseStep 1504865 = 1128649) B1128649
theorem B2258563 : Blo 888571 2258563 := bstep (se 1 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 2258563 = 3387845) B3387845
theorem B3012227 : Blo 888571 3012227 := bstep (se 1 (by rfl) ⟨2259170, by rfl⟩ : syracuseStep 3012227 = 4518341) B4518341
theorem B10122893 : Blo 888571 10122893 := bstep (se 3 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 10122893 = 3796085) B3796085
theorem B1898129 : Blo 888571 1898129 := bstep (se 2 (by rfl) ⟨711798, by rfl⟩ : syracuseStep 1898129 = 1423597) B1423597
theorem B1504993 : Blo 888571 1504993 := bstep (se 2 (by rfl) ⟨564372, by rfl⟩ : syracuseStep 1504993 = 1128745) B1128745
theorem B1505027 : Blo 888571 1505027 := bstep (se 1 (by rfl) ⟨1128770, by rfl⟩ : syracuseStep 1505027 = 2257541) B2257541
theorem B2258705 : Blo 888571 2258705 := bstep (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) B1694029
theorem B11401073 : Blo 888571 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B1505155 : Blo 888571 1505155 := bstep (se 1 (by rfl) ⟨1128866, by rfl⟩ : syracuseStep 1505155 = 2257733) B2257733
theorem B2062307 : Blo 888571 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B3799025 : Blo 888571 3799025 := bstep (se 2 (by rfl) ⟨1424634, by rfl⟩ : syracuseStep 3799025 = 2849269) B2849269
theorem B1505297 : Blo 888571 1505297 := bstep (se 2 (by rfl) ⟨564486, by rfl⟩ : syracuseStep 1505297 = 1128973) B1128973
theorem B5699717 : Blo 888571 5699717 := bstep (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) B1068697
theorem B1505425 : Blo 888571 1505425 := bstep (se 2 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 1505425 = 1129069) B1129069
theorem B1505459 : Blo 888571 1505459 := bstep (se 1 (by rfl) ⟨1129094, by rfl⟩ : syracuseStep 1505459 = 2258189) B2258189
theorem B1505587 : Blo 888571 1505587 := bstep (se 1 (by rfl) ⟨1129190, by rfl⟩ : syracuseStep 1505587 = 2258381) B2258381
theorem B1505729 : Blo 888571 1505729 := bstep (se 2 (by rfl) ⟨564648, by rfl⟩ : syracuseStep 1505729 = 1129297) B1129297
theorem B1604099 : Blo 888571 1604099 := bstep (se 1 (by rfl) ⟨1203074, by rfl⟩ : syracuseStep 1604099 = 2406149) B2406149
theorem B4815409 : Blo 888571 4815409 := bstep (se 2 (by rfl) ⟨1805778, by rfl⟩ : syracuseStep 4815409 = 3611557) B3611557
theorem B1505857 : Blo 888571 1505857 := bstep (se 2 (by rfl) ⟨564696, by rfl⟩ : syracuseStep 1505857 = 1129393) B1129393
theorem B1505891 : Blo 888571 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B2849411 : Blo 888571 2849411 := bstep (se 1 (by rfl) ⟨2137058, by rfl⟩ : syracuseStep 2849411 = 4274117) B4274117
theorem B5077667 : Blo 888571 5077667 := bstep (se 1 (by rfl) ⟨3808250, by rfl⟩ : syracuseStep 5077667 = 7616501) B7616501
theorem B1506019 : Blo 888571 1506019 := bstep (se 1 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 1506019 = 2259029) B2259029
theorem B3046157 : Blo 888571 3046157 := bstep (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) B1142309
theorem B1604387 : Blo 888571 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B1506161 : Blo 888571 1506161 := bstep (se 2 (by rfl) ⟨564810, by rfl⟩ : syracuseStep 1506161 = 1129621) B1129621
theorem B3046349 : Blo 888571 3046349 := bstep (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) B1142381
theorem B949363 : Blo 888571 949363 := bstep (se 1 (by rfl) ⟨712022, by rfl⟩ : syracuseStep 949363 = 1424045) B1424045
theorem B7208261 : Blo 888571 7208261 := bstep (se 4 (by rfl) ⟨675774, by rfl⟩ : syracuseStep 7208261 = 1351549) B1351549
theorem B3210893 : Blo 888571 3210893 := bstep (se 3 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 3210893 = 1204085) B1204085
theorem B3375179 : Blo 888571 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B14418071 : Blo 888571 14418071 := bstep (se 1 (by rfl) ⟨10813553, by rfl⟩ : syracuseStep 14418071 = 21627107) B21627107
theorem B3375377 : Blo 888571 3375377 := bstep (se 2 (by rfl) ⟨1265766, by rfl⟩ : syracuseStep 3375377 = 2531533) B2531533
theorem B6750539 : Blo 888571 6750539 := bstep (se 1 (by rfl) ⟨5062904, by rfl⟩ : syracuseStep 6750539 = 10125809) B10125809
theorem B1999385 : Blo 888571 1999385 := bstep (se 2 (by rfl) ⟨749769, by rfl⟩ : syracuseStep 1999385 = 1499539) B1499539
theorem B2032193 : Blo 888571 2032193 := bstep (se 2 (by rfl) ⟨762072, by rfl⟩ : syracuseStep 2032193 = 1524145) B1524145
theorem B4817483 : Blo 888571 4817483 := bstep (se 1 (by rfl) ⟨3613112, by rfl⟩ : syracuseStep 4817483 = 7226225) B7226225
theorem B13009501 : Blo 888571 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B1999475 : Blo 888571 1999475 := bstep (se 1 (by rfl) ⟨1499606, by rfl⟩ : syracuseStep 1999475 = 2999213) B2999213
theorem B1999511 : Blo 888571 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B1901323 : Blo 888571 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B9634625 : Blo 888571 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B1999691 : Blo 888571 1999691 := bstep (se 1 (by rfl) ⟨1499768, by rfl⟩ : syracuseStep 1999691 = 2999537) B2999537
theorem B1999745 : Blo 888571 1999745 := bstep (se 2 (by rfl) ⟨749904, by rfl⟩ : syracuseStep 1999745 = 1499809) B1499809
theorem B3376151 : Blo 888571 3376151 := bstep (se 1 (by rfl) ⟨2532113, by rfl⟩ : syracuseStep 3376151 = 5064227) B5064227
theorem B1999961 : Blo 888571 1999961 := bstep (se 2 (by rfl) ⟨749985, by rfl⟩ : syracuseStep 1999961 = 1499971) B1499971
theorem B1901657 : Blo 888571 1901657 := bstep (se 2 (by rfl) ⟨713121, by rfl⟩ : syracuseStep 1901657 = 1426243) B1426243
theorem B1803379 : Blo 888571 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B2000051 : Blo 888571 2000051 := bstep (se 1 (by rfl) ⟨1500038, by rfl⟩ : syracuseStep 2000051 = 3000077) B3000077
theorem B7603379 : Blo 888571 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B2000087 : Blo 888571 2000087 := bstep (se 1 (by rfl) ⟨1500065, by rfl⟩ : syracuseStep 2000087 = 3000131) B3000131
theorem B3376349 : Blo 888571 3376349 := bstep (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) B1266131
theorem B2000267 : Blo 888571 2000267 := bstep (se 1 (by rfl) ⟨1500200, by rfl⟩ : syracuseStep 2000267 = 3000401) B3000401
theorem B2196887 : Blo 888571 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B2000321 : Blo 888571 2000321 := bstep (se 2 (by rfl) ⟨750120, by rfl⟩ : syracuseStep 2000321 = 1500241) B1500241
theorem B951755 : Blo 888571 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B2000537 : Blo 888571 2000537 := bstep (se 2 (by rfl) ⟨750201, by rfl⟩ : syracuseStep 2000537 = 1500403) B1500403
theorem B2000627 : Blo 888571 2000627 := bstep (se 1 (by rfl) ⟨1500470, by rfl⟩ : syracuseStep 2000627 = 3000941) B3000941
theorem B2000663 : Blo 888571 2000663 := bstep (se 1 (by rfl) ⟨1500497, by rfl⟩ : syracuseStep 2000663 = 3000995) B3000995
theorem B4818781 : Blo 888571 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B4065155 : Blo 888571 4065155 := bstep (se 1 (by rfl) ⟨3048866, by rfl⟩ : syracuseStep 4065155 = 6097733) B6097733
theorem B123242417 : Blo 888571 123242417 := bstep (se 2 (by rfl) ⟨46215906, by rfl⟩ : syracuseStep 123242417 = 92431813) B92431813
theorem B2197441 : Blo 888571 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B2000843 : Blo 888571 2000843 := bstep (se 1 (by rfl) ⟨1500632, by rfl⟩ : syracuseStep 2000843 = 3001265) B3001265
theorem B2000897 : Blo 888571 2000897 := bstep (se 2 (by rfl) ⟨750336, by rfl⟩ : syracuseStep 2000897 = 1500673) B1500673
theorem B2001113 : Blo 888571 2001113 := bstep (se 2 (by rfl) ⟨750417, by rfl⟩ : syracuseStep 2001113 = 1500835) B1500835
theorem B7604441 : Blo 888571 7604441 := bstep (se 2 (by rfl) ⟨2851665, by rfl⟩ : syracuseStep 7604441 = 5703331) B5703331
theorem B2001203 : Blo 888571 2001203 := bstep (se 1 (by rfl) ⟨1500902, by rfl⟩ : syracuseStep 2001203 = 3001805) B3001805
theorem B2001239 : Blo 888571 2001239 := bstep (se 1 (by rfl) ⟨1500929, by rfl⟩ : syracuseStep 2001239 = 3001859) B3001859
theorem B2001419 : Blo 888571 2001419 := bstep (se 1 (by rfl) ⟨1501064, by rfl⟩ : syracuseStep 2001419 = 3002129) B3002129
theorem B2001473 : Blo 888571 2001473 := bstep (se 2 (by rfl) ⟨750552, by rfl⟩ : syracuseStep 2001473 = 1501105) B1501105
theorem B1903169 : Blo 888571 1903169 := bstep (se 2 (by rfl) ⟨713688, by rfl⟩ : syracuseStep 1903169 = 1427377) B1427377
theorem B2001689 : Blo 888571 2001689 := bstep (se 2 (by rfl) ⟨750633, by rfl⟩ : syracuseStep 2001689 = 1501267) B1501267
theorem B7211821 : Blo 888571 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B2001779 : Blo 888571 2001779 := bstep (se 1 (by rfl) ⟨1501334, by rfl⟩ : syracuseStep 2001779 = 3002669) B3002669
theorem B2001815 : Blo 888571 2001815 := bstep (se 1 (by rfl) ⟨1501361, by rfl⟩ : syracuseStep 2001815 = 3002723) B3002723
theorem B3607469 : Blo 888571 3607469 := bstep (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) B1352801
theorem B3804083 : Blo 888571 3804083 := bstep (se 1 (by rfl) ⟨2853062, by rfl⟩ : syracuseStep 3804083 = 5706125) B5706125
theorem B1444825 : Blo 888571 1444825 := bstep (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) B1083619
theorem B2001995 : Blo 888571 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B2002049 : Blo 888571 2002049 := bstep (se 2 (by rfl) ⟨750768, by rfl⟩ : syracuseStep 2002049 = 1501537) B1501537
theorem B3378307 : Blo 888571 3378307 := bstep (se 1 (by rfl) ⟨2533730, by rfl⟩ : syracuseStep 3378307 = 5067461) B5067461
theorem B2002265 : Blo 888571 2002265 := bstep (se 2 (by rfl) ⟨750849, by rfl⟩ : syracuseStep 2002265 = 1501699) B1501699
theorem B1904023 : Blo 888571 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B3378611 : Blo 888571 3378611 := bstep (se 1 (by rfl) ⟨2533958, by rfl⟩ : syracuseStep 3378611 = 5067917) B5067917
theorem B2002355 : Blo 888571 2002355 := bstep (se 1 (by rfl) ⟨1501766, by rfl⟩ : syracuseStep 2002355 = 3003533) B3003533
theorem B2002391 : Blo 888571 2002391 := bstep (se 1 (by rfl) ⟨1501793, by rfl⟩ : syracuseStep 2002391 = 3003587) B3003587
theorem B12815941 : Blo 888571 12815941 := bstep (se 4 (by rfl) ⟨1201494, by rfl⟩ : syracuseStep 12815941 = 2402989) B2402989
theorem B14650955 : Blo 888571 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B2002571 : Blo 888571 2002571 := bstep (se 1 (by rfl) ⟨1501928, by rfl⟩ : syracuseStep 2002571 = 3003857) B3003857
theorem B2002625 : Blo 888571 2002625 := bstep (se 2 (by rfl) ⟨750984, by rfl⟩ : syracuseStep 2002625 = 1501969) B1501969
theorem B888587 : Blo 888571 888587 := bstep (se 1 (by rfl) ⟨666440, by rfl⟩ : syracuseStep 888587 = 1332881) B1332881
theorem B888599 : Blo 888571 888599 := bstep (se 1 (by rfl) ⟨666449, by rfl⟩ : syracuseStep 888599 = 1332899) B1332899
theorem B888619 : Blo 888571 888619 := bstep (se 1 (by rfl) ⟨666464, by rfl⟩ : syracuseStep 888619 = 1332929) B1332929
theorem B888631 : Blo 888571 888631 := bstep (se 1 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 888631 = 1332947) B1332947
theorem B888651 : Blo 888571 888651 := bstep (se 1 (by rfl) ⟨666488, by rfl⟩ : syracuseStep 888651 = 1332977) B1332977
theorem B888663 : Blo 888571 888663 := bstep (se 1 (by rfl) ⟨666497, by rfl⟩ : syracuseStep 888663 = 1332995) B1332995
theorem B888683 : Blo 888571 888683 := bstep (se 1 (by rfl) ⟨666512, by rfl⟩ : syracuseStep 888683 = 1333025) B1333025
theorem B888695 : Blo 888571 888695 := bstep (se 1 (by rfl) ⟨666521, by rfl⟩ : syracuseStep 888695 = 1333043) B1333043
theorem B888715 : Blo 888571 888715 := bstep (se 1 (by rfl) ⟨666536, by rfl⟩ : syracuseStep 888715 = 1333073) B1333073
theorem B888727 : Blo 888571 888727 := bstep (se 1 (by rfl) ⟨666545, by rfl⟩ : syracuseStep 888727 = 1333091) B1333091
theorem B2002841 : Blo 888571 2002841 := bstep (se 2 (by rfl) ⟨751065, by rfl⟩ : syracuseStep 2002841 = 1502131) B1502131
theorem B888747 : Blo 888571 888747 := bstep (se 1 (by rfl) ⟨666560, by rfl⟩ : syracuseStep 888747 = 1333121) B1333121
theorem B888759 : Blo 888571 888759 := bstep (se 1 (by rfl) ⟨666569, by rfl⟩ : syracuseStep 888759 = 1333139) B1333139
theorem B888779 : Blo 888571 888779 := bstep (se 1 (by rfl) ⟨666584, by rfl⟩ : syracuseStep 888779 = 1333169) B1333169
theorem B888791 : Blo 888571 888791 := bstep (se 1 (by rfl) ⟨666593, by rfl⟩ : syracuseStep 888791 = 1333187) B1333187
theorem B888811 : Blo 888571 888811 := bstep (se 1 (by rfl) ⟨666608, by rfl⟩ : syracuseStep 888811 = 1333217) B1333217
theorem B2002931 : Blo 888571 2002931 := bstep (se 1 (by rfl) ⟨1502198, by rfl⟩ : syracuseStep 2002931 = 3004397) B3004397
theorem B888823 : Blo 888571 888823 := bstep (se 1 (by rfl) ⟨666617, by rfl⟩ : syracuseStep 888823 = 1333235) B1333235
theorem B888843 : Blo 888571 888843 := bstep (se 1 (by rfl) ⟨666632, by rfl⟩ : syracuseStep 888843 = 1333265) B1333265
theorem B888855 : Blo 888571 888855 := bstep (se 1 (by rfl) ⟨666641, by rfl⟩ : syracuseStep 888855 = 1333283) B1333283
theorem B2002967 : Blo 888571 2002967 := bstep (se 1 (by rfl) ⟨1502225, by rfl⟩ : syracuseStep 2002967 = 3004451) B3004451
theorem B888875 : Blo 888571 888875 := bstep (se 1 (by rfl) ⟨666656, by rfl⟩ : syracuseStep 888875 = 1333313) B1333313
theorem B5083181 : Blo 888571 5083181 := bstep (se 3 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 5083181 = 1906193) B1906193
theorem B888887 : Blo 888571 888887 := bstep (se 1 (by rfl) ⟨666665, by rfl⟩ : syracuseStep 888887 = 1333331) B1333331
theorem B7213121 : Blo 888571 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B3379265 : Blo 888571 3379265 := bstep (se 2 (by rfl) ⟨1267224, by rfl⟩ : syracuseStep 3379265 = 2534449) B2534449
theorem B888907 : Blo 888571 888907 := bstep (se 1 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 888907 = 1333361) B1333361
theorem B888919 : Blo 888571 888919 := bstep (se 1 (by rfl) ⟨666689, by rfl⟩ : syracuseStep 888919 = 1333379) B1333379
theorem B888939 : Blo 888571 888939 := bstep (se 1 (by rfl) ⟨666704, by rfl⟩ : syracuseStep 888939 = 1333409) B1333409
theorem B888951 : Blo 888571 888951 := bstep (se 1 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 888951 = 1333427) B1333427
theorem B888971 : Blo 888571 888971 := bstep (se 1 (by rfl) ⟨666728, by rfl⟩ : syracuseStep 888971 = 1333457) B1333457
theorem B888983 : Blo 888571 888983 := bstep (se 1 (by rfl) ⟨666737, by rfl⟩ : syracuseStep 888983 = 1333475) B1333475
theorem B17109143 : Blo 888571 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B889003 : Blo 888571 889003 := bstep (se 1 (by rfl) ⟨666752, by rfl⟩ : syracuseStep 889003 = 1333505) B1333505
theorem B889015 : Blo 888571 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B889035 : Blo 888571 889035 := bstep (se 1 (by rfl) ⟨666776, by rfl⟩ : syracuseStep 889035 = 1333553) B1333553
theorem B2003147 : Blo 888571 2003147 := bstep (se 1 (by rfl) ⟨1502360, by rfl⟩ : syracuseStep 2003147 = 3004721) B3004721
theorem B1904843 : Blo 888571 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B889047 : Blo 888571 889047 := bstep (se 1 (by rfl) ⟨666785, by rfl⟩ : syracuseStep 889047 = 1333571) B1333571
theorem B889067 : Blo 888571 889067 := bstep (se 1 (by rfl) ⟨666800, by rfl⟩ : syracuseStep 889067 = 1333601) B1333601
theorem B889079 : Blo 888571 889079 := bstep (se 1 (by rfl) ⟨666809, by rfl⟩ : syracuseStep 889079 = 1333619) B1333619
theorem B2003201 : Blo 888571 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B889099 : Blo 888571 889099 := bstep (se 1 (by rfl) ⟨666824, by rfl⟩ : syracuseStep 889099 = 1333649) B1333649
theorem B889111 : Blo 888571 889111 := bstep (se 1 (by rfl) ⟨666833, by rfl⟩ : syracuseStep 889111 = 1333667) B1333667
theorem B889131 : Blo 888571 889131 := bstep (se 1 (by rfl) ⟨666848, by rfl⟩ : syracuseStep 889131 = 1333697) B1333697
theorem B889143 : Blo 888571 889143 := bstep (se 1 (by rfl) ⟨666857, by rfl⟩ : syracuseStep 889143 = 1333715) B1333715
theorem B889163 : Blo 888571 889163 := bstep (se 1 (by rfl) ⟨666872, by rfl⟩ : syracuseStep 889163 = 1333745) B1333745
theorem B889175 : Blo 888571 889175 := bstep (se 1 (by rfl) ⟨666881, by rfl⟩ : syracuseStep 889175 = 1333763) B1333763
theorem B889195 : Blo 888571 889195 := bstep (se 1 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 889195 = 1333793) B1333793
theorem B889207 : Blo 888571 889207 := bstep (se 1 (by rfl) ⟨666905, by rfl⟩ : syracuseStep 889207 = 1333811) B1333811
theorem B889227 : Blo 888571 889227 := bstep (se 1 (by rfl) ⟨666920, by rfl⟩ : syracuseStep 889227 = 1333841) B1333841
theorem B889239 : Blo 888571 889239 := bstep (se 1 (by rfl) ⟨666929, by rfl⟩ : syracuseStep 889239 = 1333859) B1333859
theorem B889259 : Blo 888571 889259 := bstep (se 1 (by rfl) ⟨666944, by rfl⟩ : syracuseStep 889259 = 1333889) B1333889
theorem B889271 : Blo 888571 889271 := bstep (se 1 (by rfl) ⟨666953, by rfl⟩ : syracuseStep 889271 = 1333907) B1333907
theorem B889291 : Blo 888571 889291 := bstep (se 1 (by rfl) ⟨666968, by rfl⟩ : syracuseStep 889291 = 1333937) B1333937
theorem B889303 : Blo 888571 889303 := bstep (se 1 (by rfl) ⟨666977, by rfl⟩ : syracuseStep 889303 = 1333955) B1333955
theorem B2003417 : Blo 888571 2003417 := bstep (se 2 (by rfl) ⟨751281, by rfl⟩ : syracuseStep 2003417 = 1502563) B1502563
theorem B889323 : Blo 888571 889323 := bstep (se 1 (by rfl) ⟨666992, by rfl⟩ : syracuseStep 889323 = 1333985) B1333985
theorem B889335 : Blo 888571 889335 := bstep (se 1 (by rfl) ⟨667001, by rfl⟩ : syracuseStep 889335 = 1334003) B1334003
theorem B889355 : Blo 888571 889355 := bstep (se 1 (by rfl) ⟨667016, by rfl⟩ : syracuseStep 889355 = 1334033) B1334033
theorem B889367 : Blo 888571 889367 := bstep (se 1 (by rfl) ⟨667025, by rfl⟩ : syracuseStep 889367 = 1334051) B1334051
theorem B889387 : Blo 888571 889387 := bstep (se 1 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 889387 = 1334081) B1334081
theorem B2003507 : Blo 888571 2003507 := bstep (se 1 (by rfl) ⟨1502630, by rfl⟩ : syracuseStep 2003507 = 3005261) B3005261
theorem B889399 : Blo 888571 889399 := bstep (se 1 (by rfl) ⟨667049, by rfl⟩ : syracuseStep 889399 = 1334099) B1334099
theorem B889419 : Blo 888571 889419 := bstep (se 1 (by rfl) ⟨667064, by rfl⟩ : syracuseStep 889419 = 1334129) B1334129
theorem B889431 : Blo 888571 889431 := bstep (se 1 (by rfl) ⟨667073, by rfl⟩ : syracuseStep 889431 = 1334147) B1334147
theorem B2003543 : Blo 888571 2003543 := bstep (se 1 (by rfl) ⟨1502657, by rfl⟩ : syracuseStep 2003543 = 3005315) B3005315
theorem B3052121 : Blo 888571 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B889451 : Blo 888571 889451 := bstep (se 1 (by rfl) ⟨667088, by rfl⟩ : syracuseStep 889451 = 1334177) B1334177
theorem B889463 : Blo 888571 889463 := bstep (se 1 (by rfl) ⟨667097, by rfl⟩ : syracuseStep 889463 = 1334195) B1334195
theorem B889483 : Blo 888571 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B889495 : Blo 888571 889495 := bstep (se 1 (by rfl) ⟨667121, by rfl⟩ : syracuseStep 889495 = 1334243) B1334243
theorem B889515 : Blo 888571 889515 := bstep (se 1 (by rfl) ⟨667136, by rfl⟩ : syracuseStep 889515 = 1334273) B1334273
theorem B889527 : Blo 888571 889527 := bstep (se 1 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 889527 = 1334291) B1334291
theorem B889547 : Blo 888571 889547 := bstep (se 1 (by rfl) ⟨667160, by rfl⟩ : syracuseStep 889547 = 1334321) B1334321
theorem B889559 : Blo 888571 889559 := bstep (se 1 (by rfl) ⟨667169, by rfl⟩ : syracuseStep 889559 = 1334339) B1334339
theorem B889579 : Blo 888571 889579 := bstep (se 1 (by rfl) ⟨667184, by rfl⟩ : syracuseStep 889579 = 1334369) B1334369
theorem B889591 : Blo 888571 889591 := bstep (se 1 (by rfl) ⟨667193, by rfl⟩ : syracuseStep 889591 = 1334387) B1334387
theorem B889611 : Blo 888571 889611 := bstep (se 1 (by rfl) ⟨667208, by rfl⟩ : syracuseStep 889611 = 1334417) B1334417
theorem B2003723 : Blo 888571 2003723 := bstep (se 1 (by rfl) ⟨1502792, by rfl⟩ : syracuseStep 2003723 = 3005585) B3005585
theorem B889623 : Blo 888571 889623 := bstep (se 1 (by rfl) ⟨667217, by rfl⟩ : syracuseStep 889623 = 1334435) B1334435
theorem B889643 : Blo 888571 889643 := bstep (se 1 (by rfl) ⟨667232, by rfl⟩ : syracuseStep 889643 = 1334465) B1334465
theorem B889655 : Blo 888571 889655 := bstep (se 1 (by rfl) ⟨667241, by rfl⟩ : syracuseStep 889655 = 1334483) B1334483
theorem B2003777 : Blo 888571 2003777 := bstep (se 2 (by rfl) ⟨751416, by rfl⟩ : syracuseStep 2003777 = 1502833) B1502833
theorem B889675 : Blo 888571 889675 := bstep (se 1 (by rfl) ⟨667256, by rfl⟩ : syracuseStep 889675 = 1334513) B1334513
theorem B889687 : Blo 888571 889687 := bstep (se 1 (by rfl) ⟨667265, by rfl⟩ : syracuseStep 889687 = 1334531) B1334531
theorem B889707 : Blo 888571 889707 := bstep (se 1 (by rfl) ⟨667280, by rfl⟩ : syracuseStep 889707 = 1334561) B1334561
theorem B889719 : Blo 888571 889719 := bstep (se 1 (by rfl) ⟨667289, by rfl⟩ : syracuseStep 889719 = 1334579) B1334579
theorem B889739 : Blo 888571 889739 := bstep (se 1 (by rfl) ⟨667304, by rfl⟩ : syracuseStep 889739 = 1334609) B1334609
theorem B889751 : Blo 888571 889751 := bstep (se 1 (by rfl) ⟨667313, by rfl⟩ : syracuseStep 889751 = 1334627) B1334627
theorem B889771 : Blo 888571 889771 := bstep (se 1 (by rfl) ⟨667328, by rfl⟩ : syracuseStep 889771 = 1334657) B1334657
theorem B889783 : Blo 888571 889783 := bstep (se 1 (by rfl) ⟨667337, by rfl⟩ : syracuseStep 889783 = 1334675) B1334675
theorem B889803 : Blo 888571 889803 := bstep (se 1 (by rfl) ⟨667352, by rfl⟩ : syracuseStep 889803 = 1334705) B1334705
theorem B889815 : Blo 888571 889815 := bstep (se 1 (by rfl) ⟨667361, by rfl⟩ : syracuseStep 889815 = 1334723) B1334723
theorem B889835 : Blo 888571 889835 := bstep (se 1 (by rfl) ⟨667376, by rfl⟩ : syracuseStep 889835 = 1334753) B1334753
theorem B889847 : Blo 888571 889847 := bstep (se 1 (by rfl) ⟨667385, by rfl⟩ : syracuseStep 889847 = 1334771) B1334771
theorem B889867 : Blo 888571 889867 := bstep (se 1 (by rfl) ⟨667400, by rfl⟩ : syracuseStep 889867 = 1334801) B1334801
theorem B889879 : Blo 888571 889879 := bstep (se 1 (by rfl) ⟨667409, by rfl⟩ : syracuseStep 889879 = 1334819) B1334819
theorem B2003993 : Blo 888571 2003993 := bstep (se 2 (by rfl) ⟨751497, by rfl⟩ : syracuseStep 2003993 = 1502995) B1502995
theorem B889899 : Blo 888571 889899 := bstep (se 1 (by rfl) ⟨667424, by rfl⟩ : syracuseStep 889899 = 1334849) B1334849
theorem B889911 : Blo 888571 889911 := bstep (se 1 (by rfl) ⟨667433, by rfl⟩ : syracuseStep 889911 = 1334867) B1334867
theorem B889931 : Blo 888571 889931 := bstep (se 1 (by rfl) ⟨667448, by rfl⟩ : syracuseStep 889931 = 1334897) B1334897
theorem B889943 : Blo 888571 889943 := bstep (se 1 (by rfl) ⟨667457, by rfl⟩ : syracuseStep 889943 = 1334915) B1334915
theorem B889963 : Blo 888571 889963 := bstep (se 1 (by rfl) ⟨667472, by rfl⟩ : syracuseStep 889963 = 1334945) B1334945
theorem B2004083 : Blo 888571 2004083 := bstep (se 1 (by rfl) ⟨1503062, by rfl⟩ : syracuseStep 2004083 = 3006125) B3006125
theorem B889975 : Blo 888571 889975 := bstep (se 1 (by rfl) ⟨667481, by rfl⟩ : syracuseStep 889975 = 1334963) B1334963
theorem B889995 : Blo 888571 889995 := bstep (se 1 (by rfl) ⟨667496, by rfl⟩ : syracuseStep 889995 = 1334993) B1334993
theorem B890007 : Blo 888571 890007 := bstep (se 1 (by rfl) ⟨667505, by rfl⟩ : syracuseStep 890007 = 1335011) B1335011
theorem B2004119 : Blo 888571 2004119 := bstep (se 1 (by rfl) ⟨1503089, by rfl⟩ : syracuseStep 2004119 = 3006179) B3006179
theorem B890027 : Blo 888571 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B890039 : Blo 888571 890039 := bstep (se 1 (by rfl) ⟨667529, by rfl⟩ : syracuseStep 890039 = 1335059) B1335059
theorem B890059 : Blo 888571 890059 := bstep (se 1 (by rfl) ⟨667544, by rfl⟩ : syracuseStep 890059 = 1335089) B1335089
theorem B3609803 : Blo 888571 3609803 := bstep (se 1 (by rfl) ⟨2707352, by rfl⟩ : syracuseStep 3609803 = 5414705) B5414705
theorem B890071 : Blo 888571 890071 := bstep (se 1 (by rfl) ⟨667553, by rfl⟩ : syracuseStep 890071 = 1335107) B1335107
theorem B890091 : Blo 888571 890091 := bstep (se 1 (by rfl) ⟨667568, by rfl⟩ : syracuseStep 890091 = 1335137) B1335137
theorem B890103 : Blo 888571 890103 := bstep (se 1 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 890103 = 1335155) B1335155
theorem B890123 : Blo 888571 890123 := bstep (se 1 (by rfl) ⟨667592, by rfl⟩ : syracuseStep 890123 = 1335185) B1335185
theorem B890135 : Blo 888571 890135 := bstep (se 1 (by rfl) ⟨667601, by rfl⟩ : syracuseStep 890135 = 1335203) B1335203
theorem B2856215 : Blo 888571 2856215 := bstep (se 1 (by rfl) ⟨2142161, by rfl⟩ : syracuseStep 2856215 = 4284323) B4284323
theorem B890155 : Blo 888571 890155 := bstep (se 1 (by rfl) ⟨667616, by rfl⟩ : syracuseStep 890155 = 1335233) B1335233
theorem B3380525 : Blo 888571 3380525 := bstep (se 3 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 3380525 = 1267697) B1267697
theorem B890167 : Blo 888571 890167 := bstep (se 1 (by rfl) ⟨667625, by rfl⟩ : syracuseStep 890167 = 1335251) B1335251
theorem B890187 : Blo 888571 890187 := bstep (se 1 (by rfl) ⟨667640, by rfl⟩ : syracuseStep 890187 = 1335281) B1335281
theorem B3380555 : Blo 888571 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2004299 : Blo 888571 2004299 := bstep (se 1 (by rfl) ⟨1503224, by rfl⟩ : syracuseStep 2004299 = 3006449) B3006449
theorem B890199 : Blo 888571 890199 := bstep (se 1 (by rfl) ⟨667649, by rfl⟩ : syracuseStep 890199 = 1335299) B1335299
theorem B890219 : Blo 888571 890219 := bstep (se 1 (by rfl) ⟨667664, by rfl⟩ : syracuseStep 890219 = 1335329) B1335329
theorem B890231 : Blo 888571 890231 := bstep (se 1 (by rfl) ⟨667673, by rfl⟩ : syracuseStep 890231 = 1335347) B1335347
theorem B2004353 : Blo 888571 2004353 := bstep (se 2 (by rfl) ⟨751632, by rfl⟩ : syracuseStep 2004353 = 1503265) B1503265
theorem B890251 : Blo 888571 890251 := bstep (se 1 (by rfl) ⟨667688, by rfl⟩ : syracuseStep 890251 = 1335377) B1335377
theorem B890263 : Blo 888571 890263 := bstep (se 1 (by rfl) ⟨667697, by rfl⟩ : syracuseStep 890263 = 1335395) B1335395
theorem B2856343 : Blo 888571 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B890283 : Blo 888571 890283 := bstep (se 1 (by rfl) ⟨667712, by rfl⟩ : syracuseStep 890283 = 1335425) B1335425
theorem B890295 : Blo 888571 890295 := bstep (se 1 (by rfl) ⟨667721, by rfl⟩ : syracuseStep 890295 = 1335443) B1335443
theorem B890315 : Blo 888571 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B890327 : Blo 888571 890327 := bstep (se 1 (by rfl) ⟨667745, by rfl⟩ : syracuseStep 890327 = 1335491) B1335491
theorem B890347 : Blo 888571 890347 := bstep (se 1 (by rfl) ⟨667760, by rfl⟩ : syracuseStep 890347 = 1335521) B1335521
theorem B890359 : Blo 888571 890359 := bstep (se 1 (by rfl) ⟨667769, by rfl⟩ : syracuseStep 890359 = 1335539) B1335539
theorem B890379 : Blo 888571 890379 := bstep (se 1 (by rfl) ⟨667784, by rfl⟩ : syracuseStep 890379 = 1335569) B1335569
theorem B890391 : Blo 888571 890391 := bstep (se 1 (by rfl) ⟨667793, by rfl⟩ : syracuseStep 890391 = 1335587) B1335587
theorem B890411 : Blo 888571 890411 := bstep (se 1 (by rfl) ⟨667808, by rfl⟩ : syracuseStep 890411 = 1335617) B1335617
theorem B6755885 : Blo 888571 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B890423 : Blo 888571 890423 := bstep (se 1 (by rfl) ⟨667817, by rfl⟩ : syracuseStep 890423 = 1335635) B1335635
theorem B890443 : Blo 888571 890443 := bstep (se 1 (by rfl) ⟨667832, by rfl⟩ : syracuseStep 890443 = 1335665) B1335665
theorem B890455 : Blo 888571 890455 := bstep (se 1 (by rfl) ⟨667841, by rfl⟩ : syracuseStep 890455 = 1335683) B1335683
theorem B2004569 : Blo 888571 2004569 := bstep (se 2 (by rfl) ⟨751713, by rfl⟩ : syracuseStep 2004569 = 1503427) B1503427
theorem B890475 : Blo 888571 890475 := bstep (se 1 (by rfl) ⟨667856, by rfl⟩ : syracuseStep 890475 = 1335713) B1335713
theorem B890487 : Blo 888571 890487 := bstep (se 1 (by rfl) ⟨667865, by rfl⟩ : syracuseStep 890487 = 1335731) B1335731
theorem B890507 : Blo 888571 890507 := bstep (se 1 (by rfl) ⟨667880, by rfl⟩ : syracuseStep 890507 = 1335761) B1335761
theorem B1283735 : Blo 888571 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B890519 : Blo 888571 890519 := bstep (se 1 (by rfl) ⟨667889, by rfl⟩ : syracuseStep 890519 = 1335779) B1335779
theorem B2856599 : Blo 888571 2856599 := bstep (se 1 (by rfl) ⟨2142449, by rfl⟩ : syracuseStep 2856599 = 4284899) B4284899
theorem B890539 : Blo 888571 890539 := bstep (se 1 (by rfl) ⟨667904, by rfl⟩ : syracuseStep 890539 = 1335809) B1335809
theorem B2004659 : Blo 888571 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B890551 : Blo 888571 890551 := bstep (se 1 (by rfl) ⟨667913, by rfl⟩ : syracuseStep 890551 = 1335827) B1335827
theorem B890571 : Blo 888571 890571 := bstep (se 1 (by rfl) ⟨667928, by rfl⟩ : syracuseStep 890571 = 1335857) B1335857
theorem B890583 : Blo 888571 890583 := bstep (se 1 (by rfl) ⟨667937, by rfl⟩ : syracuseStep 890583 = 1335875) B1335875
theorem B2004695 : Blo 888571 2004695 := bstep (se 1 (by rfl) ⟨1503521, by rfl⟩ : syracuseStep 2004695 = 3007043) B3007043
theorem B890603 : Blo 888571 890603 := bstep (se 1 (by rfl) ⟨667952, by rfl⟩ : syracuseStep 890603 = 1335905) B1335905
theorem B890615 : Blo 888571 890615 := bstep (se 1 (by rfl) ⟨667961, by rfl⟩ : syracuseStep 890615 = 1335923) B1335923
theorem B890635 : Blo 888571 890635 := bstep (se 1 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 890635 = 1335953) B1335953
theorem B890647 : Blo 888571 890647 := bstep (se 1 (by rfl) ⟨667985, by rfl⟩ : syracuseStep 890647 = 1335971) B1335971
theorem B890667 : Blo 888571 890667 := bstep (se 1 (by rfl) ⟨668000, by rfl⟩ : syracuseStep 890667 = 1336001) B1336001
theorem B890679 : Blo 888571 890679 := bstep (se 1 (by rfl) ⟨668009, by rfl⟩ : syracuseStep 890679 = 1336019) B1336019
theorem B6854465 : Blo 888571 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B890699 : Blo 888571 890699 := bstep (se 1 (by rfl) ⟨668024, by rfl⟩ : syracuseStep 890699 = 1336049) B1336049
theorem B890711 : Blo 888571 890711 := bstep (se 1 (by rfl) ⟨668033, by rfl⟩ : syracuseStep 890711 = 1336067) B1336067
theorem B890731 : Blo 888571 890731 := bstep (se 1 (by rfl) ⟨668048, by rfl⟩ : syracuseStep 890731 = 1336097) B1336097
theorem B890743 : Blo 888571 890743 := bstep (se 1 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 890743 = 1336115) B1336115
theorem B890763 : Blo 888571 890763 := bstep (se 1 (by rfl) ⟨668072, by rfl⟩ : syracuseStep 890763 = 1336145) B1336145
theorem B2004875 : Blo 888571 2004875 := bstep (se 1 (by rfl) ⟨1503656, by rfl⟩ : syracuseStep 2004875 = 3007313) B3007313
theorem B890775 : Blo 888571 890775 := bstep (se 1 (by rfl) ⟨668081, by rfl⟩ : syracuseStep 890775 = 1336163) B1336163
theorem B890795 : Blo 888571 890795 := bstep (se 1 (by rfl) ⟨668096, by rfl⟩ : syracuseStep 890795 = 1336193) B1336193
theorem B890807 : Blo 888571 890807 := bstep (se 1 (by rfl) ⟨668105, by rfl⟩ : syracuseStep 890807 = 1336211) B1336211
theorem B2004929 : Blo 888571 2004929 := bstep (se 2 (by rfl) ⟨751848, by rfl⟩ : syracuseStep 2004929 = 1503697) B1503697
theorem B890827 : Blo 888571 890827 := bstep (se 1 (by rfl) ⟨668120, by rfl⟩ : syracuseStep 890827 = 1336241) B1336241
theorem B890839 : Blo 888571 890839 := bstep (se 1 (by rfl) ⟨668129, by rfl⟩ : syracuseStep 890839 = 1336259) B1336259
theorem B3381209 : Blo 888571 3381209 := bstep (se 2 (by rfl) ⟨1267953, by rfl⟩ : syracuseStep 3381209 = 2535907) B2535907
theorem B22845401 : Blo 888571 22845401 := bstep (se 2 (by rfl) ⟨8567025, by rfl⟩ : syracuseStep 22845401 = 17134051) B17134051
theorem B890859 : Blo 888571 890859 := bstep (se 1 (by rfl) ⟨668144, by rfl⟩ : syracuseStep 890859 = 1336289) B1336289
theorem B890871 : Blo 888571 890871 := bstep (se 1 (by rfl) ⟨668153, by rfl⟩ : syracuseStep 890871 = 1336307) B1336307
theorem B890891 : Blo 888571 890891 := bstep (se 1 (by rfl) ⟨668168, by rfl⟩ : syracuseStep 890891 = 1336337) B1336337
theorem B890903 : Blo 888571 890903 := bstep (se 1 (by rfl) ⟨668177, by rfl⟩ : syracuseStep 890903 = 1336355) B1336355
theorem B890923 : Blo 888571 890923 := bstep (se 1 (by rfl) ⟨668192, by rfl⟩ : syracuseStep 890923 = 1336385) B1336385
theorem B890935 : Blo 888571 890935 := bstep (se 1 (by rfl) ⟨668201, by rfl⟩ : syracuseStep 890935 = 1336403) B1336403
theorem B890955 : Blo 888571 890955 := bstep (se 1 (by rfl) ⟨668216, by rfl⟩ : syracuseStep 890955 = 1336433) B1336433
theorem B890967 : Blo 888571 890967 := bstep (se 1 (by rfl) ⟨668225, by rfl⟩ : syracuseStep 890967 = 1336451) B1336451
theorem B890987 : Blo 888571 890987 := bstep (se 1 (by rfl) ⟨668240, by rfl⟩ : syracuseStep 890987 = 1336481) B1336481
theorem B890999 : Blo 888571 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B8558723 : Blo 888571 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B891019 : Blo 888571 891019 := bstep (se 1 (by rfl) ⟨668264, by rfl⟩ : syracuseStep 891019 = 1336529) B1336529
theorem B891031 : Blo 888571 891031 := bstep (se 1 (by rfl) ⟨668273, by rfl⟩ : syracuseStep 891031 = 1336547) B1336547
theorem B2005145 : Blo 888571 2005145 := bstep (se 2 (by rfl) ⟨751929, by rfl⟩ : syracuseStep 2005145 = 1503859) B1503859
theorem B891051 : Blo 888571 891051 := bstep (se 1 (by rfl) ⟨668288, by rfl⟩ : syracuseStep 891051 = 1336577) B1336577
theorem B891063 : Blo 888571 891063 := bstep (se 1 (by rfl) ⟨668297, by rfl⟩ : syracuseStep 891063 = 1336595) B1336595
theorem B891083 : Blo 888571 891083 := bstep (se 1 (by rfl) ⟨668312, by rfl⟩ : syracuseStep 891083 = 1336625) B1336625
theorem B891095 : Blo 888571 891095 := bstep (se 1 (by rfl) ⟨668321, by rfl⟩ : syracuseStep 891095 = 1336643) B1336643
theorem B891115 : Blo 888571 891115 := bstep (se 1 (by rfl) ⟨668336, by rfl⟩ : syracuseStep 891115 = 1336673) B1336673
theorem B2005235 : Blo 888571 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B891127 : Blo 888571 891127 := bstep (se 1 (by rfl) ⟨668345, by rfl⟩ : syracuseStep 891127 = 1336691) B1336691
theorem B891147 : Blo 888571 891147 := bstep (se 1 (by rfl) ⟨668360, by rfl⟩ : syracuseStep 891147 = 1336721) B1336721
theorem B3381527 : Blo 888571 3381527 := bstep (se 1 (by rfl) ⟨2536145, by rfl⟩ : syracuseStep 3381527 = 5072291) B5072291
theorem B891159 : Blo 888571 891159 := bstep (se 1 (by rfl) ⟨668369, by rfl⟩ : syracuseStep 891159 = 1336739) B1336739
theorem B2005271 : Blo 888571 2005271 := bstep (se 1 (by rfl) ⟨1503953, by rfl⟩ : syracuseStep 2005271 = 3007907) B3007907
theorem B891179 : Blo 888571 891179 := bstep (se 1 (by rfl) ⟨668384, by rfl⟩ : syracuseStep 891179 = 1336769) B1336769
theorem B891191 : Blo 888571 891191 := bstep (se 1 (by rfl) ⟨668393, by rfl⟩ : syracuseStep 891191 = 1336787) B1336787
theorem B2136395 : Blo 888571 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B891211 : Blo 888571 891211 := bstep (se 1 (by rfl) ⟨668408, by rfl⟩ : syracuseStep 891211 = 1336817) B1336817
theorem B891223 : Blo 888571 891223 := bstep (se 1 (by rfl) ⟨668417, by rfl⟩ : syracuseStep 891223 = 1336835) B1336835
theorem B891243 : Blo 888571 891243 := bstep (se 1 (by rfl) ⟨668432, by rfl⟩ : syracuseStep 891243 = 1336865) B1336865
theorem B891255 : Blo 888571 891255 := bstep (se 1 (by rfl) ⟨668441, by rfl⟩ : syracuseStep 891255 = 1336883) B1336883
theorem B891275 : Blo 888571 891275 := bstep (se 1 (by rfl) ⟨668456, by rfl⟩ : syracuseStep 891275 = 1336913) B1336913
theorem B891287 : Blo 888571 891287 := bstep (se 1 (by rfl) ⟨668465, by rfl⟩ : syracuseStep 891287 = 1336931) B1336931
theorem B891307 : Blo 888571 891307 := bstep (se 1 (by rfl) ⟨668480, by rfl⟩ : syracuseStep 891307 = 1336961) B1336961
theorem B891319 : Blo 888571 891319 := bstep (se 1 (by rfl) ⟨668489, by rfl⟩ : syracuseStep 891319 = 1336979) B1336979
theorem B2005451 : Blo 888571 2005451 := bstep (se 1 (by rfl) ⟨1504088, by rfl⟩ : syracuseStep 2005451 = 3008177) B3008177
theorem B891339 : Blo 888571 891339 := bstep (se 1 (by rfl) ⟨668504, by rfl⟩ : syracuseStep 891339 = 1337009) B1337009
theorem B891351 : Blo 888571 891351 := bstep (se 1 (by rfl) ⟨668513, by rfl⟩ : syracuseStep 891351 = 1337027) B1337027
theorem B891371 : Blo 888571 891371 := bstep (se 1 (by rfl) ⟨668528, by rfl⟩ : syracuseStep 891371 = 1337057) B1337057
theorem B891383 : Blo 888571 891383 := bstep (se 1 (by rfl) ⟨668537, by rfl⟩ : syracuseStep 891383 = 1337075) B1337075
theorem B2005505 : Blo 888571 2005505 := bstep (se 2 (by rfl) ⟨752064, by rfl⟩ : syracuseStep 2005505 = 1504129) B1504129
theorem B891403 : Blo 888571 891403 := bstep (se 1 (by rfl) ⟨668552, by rfl⟩ : syracuseStep 891403 = 1337105) B1337105
theorem B891415 : Blo 888571 891415 := bstep (se 1 (by rfl) ⟨668561, by rfl⟩ : syracuseStep 891415 = 1337123) B1337123
theorem B891435 : Blo 888571 891435 := bstep (se 1 (by rfl) ⟨668576, by rfl⟩ : syracuseStep 891435 = 1337153) B1337153
theorem B891447 : Blo 888571 891447 := bstep (se 1 (by rfl) ⟨668585, by rfl⟩ : syracuseStep 891447 = 1337171) B1337171
theorem B891467 : Blo 888571 891467 := bstep (se 1 (by rfl) ⟨668600, by rfl⟩ : syracuseStep 891467 = 1337201) B1337201
theorem B891479 : Blo 888571 891479 := bstep (se 1 (by rfl) ⟨668609, by rfl⟩ : syracuseStep 891479 = 1337219) B1337219
theorem B1808983 : Blo 888571 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B891499 : Blo 888571 891499 := bstep (se 1 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 891499 = 1337249) B1337249
theorem B891511 : Blo 888571 891511 := bstep (se 1 (by rfl) ⟨668633, by rfl⟩ : syracuseStep 891511 = 1337267) B1337267
theorem B891531 : Blo 888571 891531 := bstep (se 1 (by rfl) ⟨668648, by rfl⟩ : syracuseStep 891531 = 1337297) B1337297
theorem B891543 : Blo 888571 891543 := bstep (se 1 (by rfl) ⟨668657, by rfl⟩ : syracuseStep 891543 = 1337315) B1337315
theorem B891563 : Blo 888571 891563 := bstep (se 1 (by rfl) ⟨668672, by rfl⟩ : syracuseStep 891563 = 1337345) B1337345
theorem B891575 : Blo 888571 891575 := bstep (se 1 (by rfl) ⟨668681, by rfl⟩ : syracuseStep 891575 = 1337363) B1337363
theorem B891595 : Blo 888571 891595 := bstep (se 1 (by rfl) ⟨668696, by rfl⟩ : syracuseStep 891595 = 1337393) B1337393
theorem B2857675 : Blo 888571 2857675 := bstep (se 1 (by rfl) ⟨2143256, by rfl⟩ : syracuseStep 2857675 = 4286513) B4286513
theorem B891607 : Blo 888571 891607 := bstep (se 1 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 891607 = 1337411) B1337411
theorem B2005721 : Blo 888571 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B891627 : Blo 888571 891627 := bstep (se 1 (by rfl) ⟨668720, by rfl⟩ : syracuseStep 891627 = 1337441) B1337441
theorem B891639 : Blo 888571 891639 := bstep (se 1 (by rfl) ⟨668729, by rfl⟩ : syracuseStep 891639 = 1337459) B1337459
theorem B891659 : Blo 888571 891659 := bstep (se 1 (by rfl) ⟨668744, by rfl⟩ : syracuseStep 891659 = 1337489) B1337489
theorem B891671 : Blo 888571 891671 := bstep (se 1 (by rfl) ⟨668753, by rfl⟩ : syracuseStep 891671 = 1337507) B1337507
theorem B891691 : Blo 888571 891691 := bstep (se 1 (by rfl) ⟨668768, by rfl⟩ : syracuseStep 891691 = 1337537) B1337537
theorem B2005811 : Blo 888571 2005811 := bstep (se 1 (by rfl) ⟨1504358, by rfl⟩ : syracuseStep 2005811 = 3008717) B3008717
theorem B891703 : Blo 888571 891703 := bstep (se 1 (by rfl) ⟨668777, by rfl⟩ : syracuseStep 891703 = 1337555) B1337555
theorem B891723 : Blo 888571 891723 := bstep (se 1 (by rfl) ⟨668792, by rfl⟩ : syracuseStep 891723 = 1337585) B1337585
theorem B2005847 : Blo 888571 2005847 := bstep (se 1 (by rfl) ⟨1504385, by rfl⟩ : syracuseStep 2005847 = 3008771) B3008771
theorem B891735 : Blo 888571 891735 := bstep (se 1 (by rfl) ⟨668801, by rfl⟩ : syracuseStep 891735 = 1337603) B1337603
theorem B2857817 : Blo 888571 2857817 := bstep (se 2 (by rfl) ⟨1071681, by rfl⟩ : syracuseStep 2857817 = 2143363) B2143363
theorem B891755 : Blo 888571 891755 := bstep (se 1 (by rfl) ⟨668816, by rfl⟩ : syracuseStep 891755 = 1337633) B1337633
theorem B1645427 : Blo 888571 1645427 := bstep (se 1 (by rfl) ⟨1234070, by rfl⟩ : syracuseStep 1645427 = 2468141) B2468141
theorem B891767 : Blo 888571 891767 := bstep (se 1 (by rfl) ⟨668825, by rfl⟩ : syracuseStep 891767 = 1337651) B1337651
theorem B891787 : Blo 888571 891787 := bstep (se 1 (by rfl) ⟨668840, by rfl⟩ : syracuseStep 891787 = 1337681) B1337681
theorem B891799 : Blo 888571 891799 := bstep (se 1 (by rfl) ⟨668849, by rfl⟩ : syracuseStep 891799 = 1337699) B1337699
theorem B891819 : Blo 888571 891819 := bstep (se 1 (by rfl) ⟨668864, by rfl⟩ : syracuseStep 891819 = 1337729) B1337729
theorem B3382195 : Blo 888571 3382195 := bstep (se 1 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 3382195 = 5073293) B5073293
theorem B891831 : Blo 888571 891831 := bstep (se 1 (by rfl) ⟨668873, by rfl⟩ : syracuseStep 891831 = 1337747) B1337747
theorem B891851 : Blo 888571 891851 := bstep (se 1 (by rfl) ⟨668888, by rfl⟩ : syracuseStep 891851 = 1337777) B1337777
theorem B2857931 : Blo 888571 2857931 := bstep (se 1 (by rfl) ⟨2143448, by rfl⟩ : syracuseStep 2857931 = 4286897) B4286897
theorem B891863 : Blo 888571 891863 := bstep (se 1 (by rfl) ⟨668897, by rfl⟩ : syracuseStep 891863 = 1337795) B1337795
theorem B891883 : Blo 888571 891883 := bstep (se 1 (by rfl) ⟨668912, by rfl⟩ : syracuseStep 891883 = 1337825) B1337825
theorem B891895 : Blo 888571 891895 := bstep (se 1 (by rfl) ⟨668921, by rfl⟩ : syracuseStep 891895 = 1337843) B1337843
theorem B2006027 : Blo 888571 2006027 := bstep (se 1 (by rfl) ⟨1504520, by rfl⟩ : syracuseStep 2006027 = 3009041) B3009041
theorem B891915 : Blo 888571 891915 := bstep (se 1 (by rfl) ⟨668936, by rfl⟩ : syracuseStep 891915 = 1337873) B1337873
theorem B891927 : Blo 888571 891927 := bstep (se 1 (by rfl) ⟨668945, by rfl⟩ : syracuseStep 891927 = 1337891) B1337891
theorem B891947 : Blo 888571 891947 := bstep (se 1 (by rfl) ⟨668960, by rfl⟩ : syracuseStep 891947 = 1337921) B1337921
theorem B891959 : Blo 888571 891959 := bstep (se 1 (by rfl) ⟨668969, by rfl⟩ : syracuseStep 891959 = 1337939) B1337939
theorem B2006081 : Blo 888571 2006081 := bstep (se 2 (by rfl) ⟨752280, by rfl⟩ : syracuseStep 2006081 = 1504561) B1504561
theorem B891979 : Blo 888571 891979 := bstep (se 1 (by rfl) ⟨668984, by rfl⟩ : syracuseStep 891979 = 1337969) B1337969
theorem B891991 : Blo 888571 891991 := bstep (se 1 (by rfl) ⟨668993, by rfl⟩ : syracuseStep 891991 = 1337987) B1337987
theorem B892011 : Blo 888571 892011 := bstep (se 1 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 892011 = 1338017) B1338017
theorem B892023 : Blo 888571 892023 := bstep (se 1 (by rfl) ⟨669017, by rfl⟩ : syracuseStep 892023 = 1338035) B1338035
theorem B3808387 : Blo 888571 3808387 := bstep (se 1 (by rfl) ⟨2856290, by rfl⟩ : syracuseStep 3808387 = 5712581) B5712581
theorem B892043 : Blo 888571 892043 := bstep (se 1 (by rfl) ⟨669032, by rfl⟩ : syracuseStep 892043 = 1338065) B1338065
theorem B892055 : Blo 888571 892055 := bstep (se 1 (by rfl) ⟨669041, by rfl⟩ : syracuseStep 892055 = 1338083) B1338083
theorem B892075 : Blo 888571 892075 := bstep (se 1 (by rfl) ⟨669056, by rfl⟩ : syracuseStep 892075 = 1338113) B1338113
theorem B892087 : Blo 888571 892087 := bstep (se 1 (by rfl) ⟨669065, by rfl⟩ : syracuseStep 892087 = 1338131) B1338131
theorem B892107 : Blo 888571 892107 := bstep (se 1 (by rfl) ⟨669080, by rfl⟩ : syracuseStep 892107 = 1338161) B1338161
theorem B892119 : Blo 888571 892119 := bstep (se 1 (by rfl) ⟨669089, by rfl⟩ : syracuseStep 892119 = 1338179) B1338179
theorem B892139 : Blo 888571 892139 := bstep (se 1 (by rfl) ⟨669104, by rfl⟩ : syracuseStep 892139 = 1338209) B1338209
theorem B892151 : Blo 888571 892151 := bstep (se 1 (by rfl) ⟨669113, by rfl⟩ : syracuseStep 892151 = 1338227) B1338227
theorem B892171 : Blo 888571 892171 := bstep (se 1 (by rfl) ⟨669128, by rfl⟩ : syracuseStep 892171 = 1338257) B1338257
theorem B892183 : Blo 888571 892183 := bstep (se 1 (by rfl) ⟨669137, by rfl⟩ : syracuseStep 892183 = 1338275) B1338275
theorem B2006297 : Blo 888571 2006297 := bstep (se 2 (by rfl) ⟨752361, by rfl⟩ : syracuseStep 2006297 = 1504723) B1504723
theorem B892203 : Blo 888571 892203 := bstep (se 1 (by rfl) ⟨669152, by rfl⟩ : syracuseStep 892203 = 1338305) B1338305
theorem B2858291 : Blo 888571 2858291 := bstep (se 1 (by rfl) ⟨2143718, by rfl⟩ : syracuseStep 2858291 = 4287437) B4287437
theorem B892215 : Blo 888571 892215 := bstep (se 1 (by rfl) ⟨669161, by rfl⟩ : syracuseStep 892215 = 1338323) B1338323
theorem B892235 : Blo 888571 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B892247 : Blo 888571 892247 := bstep (se 1 (by rfl) ⟨669185, by rfl⟩ : syracuseStep 892247 = 1338371) B1338371
theorem B5709149 : Blo 888571 5709149 := bstep (se 3 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 5709149 = 2140931) B2140931
theorem B892267 : Blo 888571 892267 := bstep (se 1 (by rfl) ⟨669200, by rfl⟩ : syracuseStep 892267 = 1338401) B1338401
theorem B2006387 : Blo 888571 2006387 := bstep (se 1 (by rfl) ⟨1504790, by rfl⟩ : syracuseStep 2006387 = 3009581) B3009581
theorem B892279 : Blo 888571 892279 := bstep (se 1 (by rfl) ⟨669209, by rfl⟩ : syracuseStep 892279 = 1338419) B1338419
theorem B892299 : Blo 888571 892299 := bstep (se 1 (by rfl) ⟨669224, by rfl⟩ : syracuseStep 892299 = 1338449) B1338449
theorem B2006423 : Blo 888571 2006423 := bstep (se 1 (by rfl) ⟨1504817, by rfl⟩ : syracuseStep 2006423 = 3009635) B3009635
theorem B892311 : Blo 888571 892311 := bstep (se 1 (by rfl) ⟨669233, by rfl⟩ : syracuseStep 892311 = 1338467) B1338467
theorem B892331 : Blo 888571 892331 := bstep (se 1 (by rfl) ⟨669248, by rfl⟩ : syracuseStep 892331 = 1338497) B1338497
theorem B892343 : Blo 888571 892343 := bstep (se 1 (by rfl) ⟨669257, by rfl⟩ : syracuseStep 892343 = 1338515) B1338515
theorem B892363 : Blo 888571 892363 := bstep (se 1 (by rfl) ⟨669272, by rfl⟩ : syracuseStep 892363 = 1338545) B1338545
theorem B892375 : Blo 888571 892375 := bstep (se 1 (by rfl) ⟨669281, by rfl⟩ : syracuseStep 892375 = 1338563) B1338563
theorem B892395 : Blo 888571 892395 := bstep (se 1 (by rfl) ⟨669296, by rfl⟩ : syracuseStep 892395 = 1338593) B1338593
theorem B892407 : Blo 888571 892407 := bstep (se 1 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 892407 = 1338611) B1338611
theorem B892427 : Blo 888571 892427 := bstep (se 1 (by rfl) ⟨669320, by rfl⟩ : syracuseStep 892427 = 1338641) B1338641
theorem B892439 : Blo 888571 892439 := bstep (se 1 (by rfl) ⟨669329, by rfl⟩ : syracuseStep 892439 = 1338659) B1338659
theorem B892459 : Blo 888571 892459 := bstep (se 1 (by rfl) ⟨669344, by rfl⟩ : syracuseStep 892459 = 1338689) B1338689
theorem B892471 : Blo 888571 892471 := bstep (se 1 (by rfl) ⟨669353, by rfl⟩ : syracuseStep 892471 = 1338707) B1338707
theorem B2006603 : Blo 888571 2006603 := bstep (se 1 (by rfl) ⟨1504952, by rfl⟩ : syracuseStep 2006603 = 3009905) B3009905
theorem B892491 : Blo 888571 892491 := bstep (se 1 (by rfl) ⟨669368, by rfl⟩ : syracuseStep 892491 = 1338737) B1338737
theorem B892503 : Blo 888571 892503 := bstep (se 1 (by rfl) ⟨669377, by rfl⟩ : syracuseStep 892503 = 1338755) B1338755
theorem B892523 : Blo 888571 892523 := bstep (se 1 (by rfl) ⟨669392, by rfl⟩ : syracuseStep 892523 = 1338785) B1338785
theorem B892535 : Blo 888571 892535 := bstep (se 1 (by rfl) ⟨669401, by rfl⟩ : syracuseStep 892535 = 1338803) B1338803
theorem B2006657 : Blo 888571 2006657 := bstep (se 2 (by rfl) ⟨752496, by rfl⟩ : syracuseStep 2006657 = 1504993) B1504993
theorem B892555 : Blo 888571 892555 := bstep (se 1 (by rfl) ⟨669416, by rfl⟩ : syracuseStep 892555 = 1338833) B1338833
theorem B892567 : Blo 888571 892567 := bstep (se 1 (by rfl) ⟨669425, by rfl⟩ : syracuseStep 892567 = 1338851) B1338851
theorem B2006873 : Blo 888571 2006873 := bstep (se 2 (by rfl) ⟨752577, by rfl⟩ : syracuseStep 2006873 = 1505155) B1505155
theorem B7610213 : Blo 888571 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B2006963 : Blo 888571 2006963 := bstep (se 1 (by rfl) ⟨1505222, by rfl⟩ : syracuseStep 2006963 = 3010445) B3010445
theorem B2006999 : Blo 888571 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B2531351 : Blo 888571 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B2859059 : Blo 888571 2859059 := bstep (se 1 (by rfl) ⟨2144294, by rfl⟩ : syracuseStep 2859059 = 4288589) B4288589
theorem B2007179 : Blo 888571 2007179 := bstep (se 1 (by rfl) ⟨1505384, by rfl⟩ : syracuseStep 2007179 = 3010769) B3010769
theorem B3383441 : Blo 888571 3383441 := bstep (se 2 (by rfl) ⟨1268790, by rfl⟩ : syracuseStep 3383441 = 2537581) B2537581
theorem B2007233 : Blo 888571 2007233 := bstep (se 2 (by rfl) ⟨752712, by rfl⟩ : syracuseStep 2007233 = 1505425) B1505425
theorem B2007449 : Blo 888571 2007449 := bstep (se 2 (by rfl) ⟨752793, by rfl⟩ : syracuseStep 2007449 = 1505587) B1505587
theorem B2859457 : Blo 888571 2859457 := bstep (se 2 (by rfl) ⟨1072296, by rfl⟩ : syracuseStep 2859457 = 2144593) B2144593
theorem B2892235 : Blo 888571 2892235 := bstep (se 1 (by rfl) ⟨2169176, by rfl⟩ : syracuseStep 2892235 = 4338353) B4338353
theorem B2007539 : Blo 888571 2007539 := bstep (se 1 (by rfl) ⟨1505654, by rfl⟩ : syracuseStep 2007539 = 3011309) B3011309
theorem B2007575 : Blo 888571 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B2007755 : Blo 888571 2007755 := bstep (se 1 (by rfl) ⟨1505816, by rfl⟩ : syracuseStep 2007755 = 3011633) B3011633
theorem B2007809 : Blo 888571 2007809 := bstep (se 2 (by rfl) ⟨752928, by rfl⟩ : syracuseStep 2007809 = 1505857) B1505857
theorem B3384139 : Blo 888571 3384139 := bstep (se 1 (by rfl) ⟨2538104, by rfl⟩ : syracuseStep 3384139 = 5076209) B5076209
theorem B3810199 : Blo 888571 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B2008025 : Blo 888571 2008025 := bstep (se 2 (by rfl) ⟨753009, by rfl⟩ : syracuseStep 2008025 = 1506019) B1506019
theorem B2008115 : Blo 888571 2008115 := bstep (se 1 (by rfl) ⟨1506086, by rfl⟩ : syracuseStep 2008115 = 3012173) B3012173
theorem B2008151 : Blo 888571 2008151 := bstep (se 1 (by rfl) ⟨1506113, by rfl⟩ : syracuseStep 2008151 = 3012227) B3012227
theorem B3384413 : Blo 888571 3384413 := bstep (se 3 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 3384413 = 1269155) B1269155
theorem B3613955 : Blo 888571 3613955 := bstep (se 1 (by rfl) ⟨2710466, by rfl⟩ : syracuseStep 3613955 = 5420933) B5420933
theorem B2532683 : Blo 888571 2532683 := bstep (se 1 (by rfl) ⟨1899512, by rfl⟩ : syracuseStep 2532683 = 3799025) B3799025
theorem B6759773 : Blo 888571 6759773 := bstep (se 3 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 6759773 = 2534915) B2534915
theorem B7611853 : Blo 888571 7611853 := bstep (se 3 (by rfl) ⟨1427222, by rfl⟩ : syracuseStep 7611853 = 2854445) B2854445
theorem B3810833 : Blo 888571 3810833 := bstep (se 2 (by rfl) ⟨1429062, by rfl⟩ : syracuseStep 3810833 = 2858125) B2858125
theorem B3385111 : Blo 888571 3385111 := bstep (se 1 (by rfl) ⟨2538833, by rfl⟩ : syracuseStep 3385111 = 5077667) B5077667
theorem B4499549 : Blo 888571 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B3811531 : Blo 888571 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B1124695 : Blo 888571 1124695 := bstep (se 1 (by rfl) ⟨843521, by rfl⟩ : syracuseStep 1124695 = 1687043) B1687043
theorem B2140595 : Blo 888571 2140595 := bstep (se 1 (by rfl) ⟨1605446, by rfl⟩ : syracuseStep 2140595 = 3210893) B3210893
theorem B3811805 : Blo 888571 3811805 := bstep (se 3 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 3811805 = 1429427) B1429427
theorem B3385901 : Blo 888571 3385901 := bstep (se 3 (by rfl) ⟨634856, by rfl⟩ : syracuseStep 3385901 = 1269713) B1269713
theorem B17148509 : Blo 888571 17148509 := bstep (se 3 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 17148509 = 6430691) B6430691
theorem B7613189 : Blo 888571 7613189 := bstep (se 4 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 7613189 = 1427473) B1427473
theorem B3812147 : Blo 888571 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B2534323 : Blo 888571 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B2436119 : Blo 888571 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B1125515 : Blo 888571 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B3091933 : Blo 888571 3091933 := bstep (se 3 (by rfl) ⟨579737, by rfl⟩ : syracuseStep 3091933 = 1159475) B1159475
theorem B2404019 : Blo 888571 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B105557701 : Blo 888571 105557701 := bstep (se 4 (by rfl) ⟨9896034, by rfl⟩ : syracuseStep 105557701 = 19792069) B19792069
theorem B1126219 : Blo 888571 1126219 := bstep (se 1 (by rfl) ⟨844664, by rfl⟩ : syracuseStep 1126219 = 1689329) B1689329
theorem B5418845 : Blo 888571 5418845 := bstep (se 3 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 5418845 = 2032067) B2032067
theorem B3387329 : Blo 888571 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B2535371 : Blo 888571 2535371 := bstep (se 1 (by rfl) ⟨1901528, by rfl⟩ : syracuseStep 2535371 = 3803057) B3803057
theorem B1126487 : Blo 888571 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B1355915 : Blo 888571 1355915 := bstep (se 1 (by rfl) ⟨1016936, by rfl⟩ : syracuseStep 1355915 = 2033873) B2033873
theorem B4501655 : Blo 888571 4501655 := bstep (se 1 (by rfl) ⟨3376241, by rfl⟩ : syracuseStep 4501655 = 6752483) B6752483
theorem B5714221 : Blo 888571 5714221 := bstep (se 3 (by rfl) ⟨1071416, by rfl⟩ : syracuseStep 5714221 = 2142833) B2142833
theorem B15446389 : Blo 888571 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B1520089 : Blo 888571 1520089 := bstep (se 2 (by rfl) ⟨570033, by rfl⟩ : syracuseStep 1520089 = 1140067) B1140067
theorem B2404829 : Blo 888571 2404829 := bstep (se 3 (by rfl) ⟨450905, by rfl⟩ : syracuseStep 2404829 = 901811) B901811
theorem B1127191 : Blo 888571 1127191 := bstep (se 1 (by rfl) ⟨845393, by rfl⟩ : syracuseStep 1127191 = 1690787) B1690787
theorem B3519533 : Blo 888571 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B3388817 : Blo 888571 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B4273559 : Blo 888571 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B2537011 : Blo 888571 2537011 := bstep (se 1 (by rfl) ⟨1902758, by rfl⟩ : syracuseStep 2537011 = 3805517) B3805517
theorem B2405953 : Blo 888571 2405953 := bstep (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) B1804465
theorem B2537239 : Blo 888571 2537239 := bstep (se 1 (by rfl) ⟨1902929, by rfl⟩ : syracuseStep 2537239 = 3805859) B3805859
theorem B2144179 : Blo 888571 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B1128907 : Blo 888571 1128907 := bstep (se 1 (by rfl) ⟨846680, by rfl⟩ : syracuseStep 1128907 = 1693361) B1693361
theorem B5061811 : Blo 888571 5061811 := bstep (se 1 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 5061811 = 7592717) B7592717
theorem B1686899 : Blo 888571 1686899 := bstep (se 1 (by rfl) ⟨1265174, by rfl⟩ : syracuseStep 1686899 = 2530349) B2530349
theorem B2539097 : Blo 888571 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B4505219 : Blo 888571 4505219 := bstep (se 1 (by rfl) ⟨3378914, by rfl⟩ : syracuseStep 4505219 = 6757829) B6757829
theorem B6504113 : Blo 888571 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B2408267 : Blo 888571 2408267 := bstep (se 1 (by rfl) ⟨1806200, by rfl⟩ : syracuseStep 2408267 = 3612401) B3612401
theorem B1687385 : Blo 888571 1687385 := bstep (se 2 (by rfl) ⟨632769, by rfl⟩ : syracuseStep 1687385 = 1265539) B1265539
theorem B6504343 : Blo 888571 6504343 := bstep (se 1 (by rfl) ⟨4878257, by rfl⟩ : syracuseStep 6504343 = 9756515) B9756515
theorem B10141847 : Blo 888571 10141847 := bstep (se 1 (by rfl) ⟨7606385, by rfl⟩ : syracuseStep 10141847 = 15212771) B15212771
theorem B999787 : Blo 888571 999787 := bstep (se 1 (by rfl) ⟨749840, by rfl⟩ : syracuseStep 999787 = 1499681) B1499681
theorem B2539927 : Blo 888571 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B999895 : Blo 888571 999895 := bstep (se 1 (by rfl) ⟨749921, by rfl⟩ : syracuseStep 999895 = 1499843) B1499843
theorem B5063269 : Blo 888571 5063269 := bstep (se 4 (by rfl) ⟨474681, by rfl⟩ : syracuseStep 5063269 = 949363) B949363
theorem B1000075 : Blo 888571 1000075 := bstep (se 1 (by rfl) ⟨750056, by rfl⟩ : syracuseStep 1000075 = 1500113) B1500113
theorem B1000183 : Blo 888571 1000183 := bstep (se 1 (by rfl) ⟨750137, by rfl⟩ : syracuseStep 1000183 = 1500275) B1500275
theorem B2999105 : Blo 888571 2999105 := bstep (se 2 (by rfl) ⟨1124664, by rfl⟩ : syracuseStep 2999105 = 2249329) B2249329
theorem B1000363 : Blo 888571 1000363 := bstep (se 1 (by rfl) ⟨750272, by rfl⟩ : syracuseStep 1000363 = 1500545) B1500545
theorem B1000471 : Blo 888571 1000471 := bstep (se 1 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 1000471 = 1500707) B1500707
theorem B1000651 : Blo 888571 1000651 := bstep (se 1 (by rfl) ⟨750488, by rfl⟩ : syracuseStep 1000651 = 1500977) B1500977
theorem B2540747 : Blo 888571 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B1688843 : Blo 888571 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B1525015 : Blo 888571 1525015 := bstep (se 1 (by rfl) ⟨1143761, by rfl⟩ : syracuseStep 1525015 = 2287523) B2287523
theorem B1000759 : Blo 888571 1000759 := bstep (se 1 (by rfl) ⟨750569, by rfl⟩ : syracuseStep 1000759 = 1501139) B1501139
theorem B1623383 : Blo 888571 1623383 := bstep (se 1 (by rfl) ⟨1217537, by rfl⟩ : syracuseStep 1623383 = 2435075) B2435075
theorem B2999645 : Blo 888571 2999645 := bstep (se 3 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 2999645 = 1124867) B1124867
theorem B4638131 : Blo 888571 4638131 := bstep (se 1 (by rfl) ⟨3478598, by rfl⟩ : syracuseStep 4638131 = 6957197) B6957197
theorem B1689025 : Blo 888571 1689025 := bstep (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) B1266769
theorem B1000939 : Blo 888571 1000939 := bstep (se 1 (by rfl) ⟨750704, by rfl⟩ : syracuseStep 1000939 = 1501409) B1501409
theorem B1426967 : Blo 888571 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B902711 : Blo 888571 902711 := bstep (se 1 (by rfl) ⟨677033, by rfl⟩ : syracuseStep 902711 = 1354067) B1354067
theorem B1001047 : Blo 888571 1001047 := bstep (se 1 (by rfl) ⟨750785, by rfl⟩ : syracuseStep 1001047 = 1501571) B1501571
theorem B1427095 : Blo 888571 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B1001227 : Blo 888571 1001227 := bstep (se 1 (by rfl) ⟨750920, by rfl⟩ : syracuseStep 1001227 = 1501841) B1501841
theorem B1001335 : Blo 888571 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B1689473 : Blo 888571 1689473 := bstep (se 2 (by rfl) ⟨633552, by rfl⟩ : syracuseStep 1689473 = 1267105) B1267105
theorem B1001515 : Blo 888571 1001515 := bstep (se 1 (by rfl) ⟨751136, by rfl⟩ : syracuseStep 1001515 = 1502273) B1502273
theorem B4278365 : Blo 888571 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B1001623 : Blo 888571 1001623 := bstep (se 1 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 1001623 = 1502435) B1502435
theorem B1689815 : Blo 888571 1689815 := bstep (se 1 (by rfl) ⟨1267361, by rfl⟩ : syracuseStep 1689815 = 2534723) B2534723
theorem B3852589 : Blo 888571 3852589 := bstep (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) B1444721
theorem B1001803 : Blo 888571 1001803 := bstep (se 1 (by rfl) ⟨751352, by rfl⟩ : syracuseStep 1001803 = 1502705) B1502705
theorem B5785931 : Blo 888571 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B1001911 : Blo 888571 1001911 := bstep (se 1 (by rfl) ⟨751433, by rfl⟩ : syracuseStep 1001911 = 1502867) B1502867
theorem B3000779 : Blo 888571 3000779 := bstep (se 1 (by rfl) ⟨2250584, by rfl⟩ : syracuseStep 3000779 = 4501169) B4501169
theorem B1427915 : Blo 888571 1427915 := bstep (se 1 (by rfl) ⟨1070936, by rfl⟩ : syracuseStep 1427915 = 2141873) B2141873
theorem B1002091 : Blo 888571 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B1002199 : Blo 888571 1002199 := bstep (se 1 (by rfl) ⟨751649, by rfl⟩ : syracuseStep 1002199 = 1503299) B1503299
theorem B3001049 : Blo 888571 3001049 := bstep (se 2 (by rfl) ⟨1125393, by rfl⟩ : syracuseStep 3001049 = 2250787) B2250787
theorem B3853079 : Blo 888571 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B1690483 : Blo 888571 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B15190901 : Blo 888571 15190901 := bstep (se 5 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 15190901 = 1424147) B1424147
theorem B1002379 : Blo 888571 1002379 := bstep (se 1 (by rfl) ⟨751784, by rfl⟩ : syracuseStep 1002379 = 1503569) B1503569
theorem B1002487 : Blo 888571 1002487 := bstep (se 1 (by rfl) ⟨751865, by rfl⟩ : syracuseStep 1002487 = 1503731) B1503731
theorem B904235 : Blo 888571 904235 := bstep (se 1 (by rfl) ⟨678176, by rfl⟩ : syracuseStep 904235 = 1356353) B1356353
theorem B1002667 : Blo 888571 1002667 := bstep (se 1 (by rfl) ⟨752000, by rfl⟩ : syracuseStep 1002667 = 1504001) B1504001
theorem B4508945 : Blo 888571 4508945 := bstep (se 2 (by rfl) ⟨1690854, by rfl⟩ : syracuseStep 4508945 = 3381709) B3381709
theorem B1002775 : Blo 888571 1002775 := bstep (se 1 (by rfl) ⟨752081, by rfl⟩ : syracuseStep 1002775 = 1504163) B1504163
theorem B1428761 : Blo 888571 1428761 := bstep (se 2 (by rfl) ⟨535785, by rfl⟩ : syracuseStep 1428761 = 1071571) B1071571
theorem B1690931 : Blo 888571 1690931 := bstep (se 1 (by rfl) ⟨1268198, by rfl⟩ : syracuseStep 1690931 = 2536397) B2536397
theorem B1690969 : Blo 888571 1690969 := bstep (se 2 (by rfl) ⟨634113, by rfl⟩ : syracuseStep 1690969 = 1268227) B1268227
theorem B1625483 : Blo 888571 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B3001751 : Blo 888571 3001751 := bstep (se 1 (by rfl) ⟨2251313, by rfl⟩ : syracuseStep 3001751 = 4502627) B4502627
theorem B4509107 : Blo 888571 4509107 := bstep (se 1 (by rfl) ⟨3381830, by rfl⟩ : syracuseStep 4509107 = 6763661) B6763661
theorem B1002955 : Blo 888571 1002955 := bstep (se 1 (by rfl) ⟨752216, by rfl⟩ : syracuseStep 1002955 = 1504433) B1504433
theorem B1003063 : Blo 888571 1003063 := bstep (se 1 (by rfl) ⟨752297, by rfl⟩ : syracuseStep 1003063 = 1504595) B1504595
theorem B1003243 : Blo 888571 1003243 := bstep (se 1 (by rfl) ⟨752432, by rfl⟩ : syracuseStep 1003243 = 1504865) B1504865
theorem B1265419 : Blo 888571 1265419 := bstep (se 1 (by rfl) ⟨949064, by rfl⟩ : syracuseStep 1265419 = 1898129) B1898129
theorem B1691417 : Blo 888571 1691417 := bstep (se 2 (by rfl) ⟨634281, by rfl⟩ : syracuseStep 1691417 = 1268563) B1268563
theorem B1429273 : Blo 888571 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B1003351 : Blo 888571 1003351 := bstep (se 1 (by rfl) ⟨752513, by rfl⟩ : syracuseStep 1003351 = 1505027) B1505027
theorem B3002291 : Blo 888571 3002291 := bstep (se 1 (by rfl) ⟨2251718, by rfl⟩ : syracuseStep 3002291 = 4503437) B4503437
theorem B1003531 : Blo 888571 1003531 := bstep (se 1 (by rfl) ⟨752648, by rfl⟩ : syracuseStep 1003531 = 1505297) B1505297
theorem B1003639 : Blo 888571 1003639 := bstep (se 1 (by rfl) ⟨752729, by rfl⟩ : syracuseStep 1003639 = 1505459) B1505459
theorem B3002561 : Blo 888571 3002561 := bstep (se 2 (by rfl) ⟨1125960, by rfl⟩ : syracuseStep 3002561 = 2251921) B2251921
theorem B1003819 : Blo 888571 1003819 := bstep (se 1 (by rfl) ⟨752864, by rfl⟩ : syracuseStep 1003819 = 1505729) B1505729
theorem B1069399 : Blo 888571 1069399 := bstep (se 1 (by rfl) ⟨802049, by rfl⟩ : syracuseStep 1069399 = 1604099) B1604099
theorem B1003927 : Blo 888571 1003927 := bstep (se 1 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 1003927 = 1505891) B1505891
theorem B1692161 : Blo 888571 1692161 := bstep (se 2 (by rfl) ⟨634560, by rfl⟩ : syracuseStep 1692161 = 1269121) B1269121
theorem B1004107 : Blo 888571 1004107 := bstep (se 1 (by rfl) ⟨753080, by rfl⟩ : syracuseStep 1004107 = 1506161) B1506161
theorem B3003101 : Blo 888571 3003101 := bstep (se 3 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 3003101 = 1126163) B1126163
theorem B1692427 : Blo 888571 1692427 := bstep (se 1 (by rfl) ⟨1269320, by rfl⟩ : syracuseStep 1692427 = 2538641) B2538641
theorem B4805507 : Blo 888571 4805507 := bstep (se 1 (by rfl) ⟨3604130, by rfl⟩ : syracuseStep 4805507 = 7208261) B7208261
theorem B7722161 : Blo 888571 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B1692875 : Blo 888571 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B8115491 : Blo 888571 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B3429697 : Blo 888571 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B4511051 : Blo 888571 4511051 := bstep (se 1 (by rfl) ⟨3383288, by rfl⟩ : syracuseStep 4511051 = 6766577) B6766577
theorem B1693057 : Blo 888571 1693057 := bstep (se 2 (by rfl) ⟨634896, by rfl⟩ : syracuseStep 1693057 = 1269793) B1269793
theorem B31315349 : Blo 888571 31315349 := bstep (se 6 (by rfl) ⟨733953, by rfl⟩ : syracuseStep 31315349 = 1467907) B1467907
theorem B7591319 : Blo 888571 7591319 := bstep (se 1 (by rfl) ⟨5693489, by rfl⟩ : syracuseStep 7591319 = 11386979) B11386979
theorem B8115635 : Blo 888571 8115635 := bstep (se 1 (by rfl) ⟨6086726, by rfl⟩ : syracuseStep 8115635 = 12173453) B12173453
theorem B1332875 : Blo 888571 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B1332887 : Blo 888571 1332887 := bstep (se 1 (by rfl) ⟨999665, by rfl⟩ : syracuseStep 1332887 = 1999331) B1999331
theorem B2250443 : Blo 888571 2250443 := bstep (se 1 (by rfl) ⟨1687832, by rfl⟩ : syracuseStep 2250443 = 3375665) B3375665
theorem B1693399 : Blo 888571 1693399 := bstep (se 1 (by rfl) ⟨1270049, by rfl⟩ : syracuseStep 1693399 = 2540099) B2540099
theorem B1332953 : Blo 888571 1332953 := bstep (se 2 (by rfl) ⟨499857, by rfl⟩ : syracuseStep 1332953 = 999715) B999715
theorem B1333067 : Blo 888571 1333067 := bstep (se 1 (by rfl) ⟨999800, by rfl⟩ : syracuseStep 1333067 = 1999601) B1999601
theorem B3004235 : Blo 888571 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B1333079 : Blo 888571 1333079 := bstep (se 1 (by rfl) ⟨999809, by rfl⟩ : syracuseStep 1333079 = 1999619) B1999619
theorem B1300313 : Blo 888571 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B1333145 : Blo 888571 1333145 := bstep (se 2 (by rfl) ⟨499929, by rfl⟩ : syracuseStep 1333145 = 999859) B999859
theorem B1693619 : Blo 888571 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B1333259 : Blo 888571 1333259 := bstep (se 1 (by rfl) ⟨999944, by rfl⟩ : syracuseStep 1333259 = 1999889) B1999889
theorem B1333271 : Blo 888571 1333271 := bstep (se 1 (by rfl) ⟨999953, by rfl⟩ : syracuseStep 1333271 = 1999907) B1999907
theorem B1333337 : Blo 888571 1333337 := bstep (se 2 (by rfl) ⟨500001, by rfl⟩ : syracuseStep 1333337 = 1000003) B1000003
theorem B3004505 : Blo 888571 3004505 := bstep (se 2 (by rfl) ⟨1126689, by rfl⟩ : syracuseStep 3004505 = 2253379) B2253379
theorem B1693847 : Blo 888571 1693847 := bstep (se 1 (by rfl) ⟨1270385, by rfl⟩ : syracuseStep 1693847 = 2540771) B2540771
theorem B1333451 : Blo 888571 1333451 := bstep (se 1 (by rfl) ⟨1000088, by rfl⟩ : syracuseStep 1333451 = 2000177) B2000177
theorem B1333463 : Blo 888571 1333463 := bstep (se 1 (by rfl) ⟨1000097, by rfl⟩ : syracuseStep 1333463 = 2000195) B2000195
theorem B1333529 : Blo 888571 1333529 := bstep (se 2 (by rfl) ⟨500073, by rfl⟩ : syracuseStep 1333529 = 1000147) B1000147
theorem B5069101 : Blo 888571 5069101 := bstep (se 3 (by rfl) ⟨950456, by rfl⟩ : syracuseStep 5069101 = 1900913) B1900913
theorem B1333643 : Blo 888571 1333643 := bstep (se 1 (by rfl) ⟨1000232, by rfl⟩ : syracuseStep 1333643 = 2000465) B2000465
theorem B1333655 : Blo 888571 1333655 := bstep (se 1 (by rfl) ⟨1000241, by rfl⟩ : syracuseStep 1333655 = 2000483) B2000483
theorem B1694105 : Blo 888571 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B8575409 : Blo 888571 8575409 := bstep (se 2 (by rfl) ⟨3215778, by rfl⟩ : syracuseStep 8575409 = 6431557) B6431557
theorem B1333721 : Blo 888571 1333721 := bstep (se 2 (by rfl) ⟨500145, by rfl⟩ : syracuseStep 1333721 = 1000291) B1000291
theorem B1333835 : Blo 888571 1333835 := bstep (se 1 (by rfl) ⟨1000376, by rfl⟩ : syracuseStep 1333835 = 2000753) B2000753
theorem B1333847 : Blo 888571 1333847 := bstep (se 1 (by rfl) ⟨1000385, by rfl⟩ : syracuseStep 1333847 = 2000771) B2000771
theorem B2251415 : Blo 888571 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B1333913 : Blo 888571 1333913 := bstep (se 2 (by rfl) ⟨500217, by rfl⟩ : syracuseStep 1333913 = 1000435) B1000435
theorem B1334027 : Blo 888571 1334027 := bstep (se 1 (by rfl) ⟨1000520, by rfl⟩ : syracuseStep 1334027 = 2001041) B2001041
theorem B1334039 : Blo 888571 1334039 := bstep (se 1 (by rfl) ⟨1000529, by rfl⟩ : syracuseStep 1334039 = 2001059) B2001059
theorem B3005207 : Blo 888571 3005207 := bstep (se 1 (by rfl) ⟨2253905, by rfl⟩ : syracuseStep 3005207 = 4507811) B4507811
theorem B1334105 : Blo 888571 1334105 := bstep (se 2 (by rfl) ⟨500289, by rfl⟩ : syracuseStep 1334105 = 1000579) B1000579
theorem B2710361 : Blo 888571 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B1334219 : Blo 888571 1334219 := bstep (se 1 (by rfl) ⟨1000664, by rfl⟩ : syracuseStep 1334219 = 2001329) B2001329
theorem B1334231 : Blo 888571 1334231 := bstep (se 1 (by rfl) ⟨1000673, by rfl⟩ : syracuseStep 1334231 = 2001347) B2001347
theorem B1334297 : Blo 888571 1334297 := bstep (se 2 (by rfl) ⟨500361, by rfl⟩ : syracuseStep 1334297 = 1000723) B1000723
theorem B4283437 : Blo 888571 4283437 := bstep (se 3 (by rfl) ⟨803144, by rfl⟩ : syracuseStep 4283437 = 1606289) B1606289
theorem B4512833 : Blo 888571 4512833 := bstep (se 2 (by rfl) ⟨1692312, by rfl⟩ : syracuseStep 4512833 = 3384625) B3384625
theorem B1334411 : Blo 888571 1334411 := bstep (se 1 (by rfl) ⟨1000808, by rfl⟩ : syracuseStep 1334411 = 2001617) B2001617
theorem B1334423 : Blo 888571 1334423 := bstep (se 1 (by rfl) ⟨1000817, by rfl⟩ : syracuseStep 1334423 = 2001635) B2001635
theorem B3431575 : Blo 888571 3431575 := bstep (se 1 (by rfl) ⟨2573681, by rfl⟩ : syracuseStep 3431575 = 5147363) B5147363
theorem B1334489 : Blo 888571 1334489 := bstep (se 2 (by rfl) ⟨500433, by rfl⟩ : syracuseStep 1334489 = 1000867) B1000867
theorem B5790937 : Blo 888571 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B7232813 : Blo 888571 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B2252083 : Blo 888571 2252083 := bstep (se 1 (by rfl) ⟨1689062, by rfl⟩ : syracuseStep 2252083 = 3378125) B3378125
theorem B3005747 : Blo 888571 3005747 := bstep (se 1 (by rfl) ⟨2254310, by rfl⟩ : syracuseStep 3005747 = 4508621) B4508621
theorem B1334603 : Blo 888571 1334603 := bstep (se 1 (by rfl) ⟨1000952, by rfl⟩ : syracuseStep 1334603 = 2001905) B2001905
theorem B1334615 : Blo 888571 1334615 := bstep (se 1 (by rfl) ⟨1000961, by rfl⟩ : syracuseStep 1334615 = 2001923) B2001923
theorem B1334681 : Blo 888571 1334681 := bstep (se 2 (by rfl) ⟨500505, by rfl⟩ : syracuseStep 1334681 = 1001011) B1001011
theorem B2252225 : Blo 888571 2252225 := bstep (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) B1689169
theorem B1334795 : Blo 888571 1334795 := bstep (se 1 (by rfl) ⟨1001096, by rfl⟩ : syracuseStep 1334795 = 2002193) B2002193
theorem B1334807 : Blo 888571 1334807 := bstep (se 1 (by rfl) ⟨1001105, by rfl⟩ : syracuseStep 1334807 = 2002211) B2002211
theorem B3006017 : Blo 888571 3006017 := bstep (se 2 (by rfl) ⟨1127256, by rfl⟩ : syracuseStep 3006017 = 2254513) B2254513
theorem B1334873 : Blo 888571 1334873 := bstep (se 2 (by rfl) ⟨500577, by rfl⟩ : syracuseStep 1334873 = 1001155) B1001155
theorem B1334987 : Blo 888571 1334987 := bstep (se 1 (by rfl) ⟨1001240, by rfl⟩ : syracuseStep 1334987 = 2002481) B2002481
theorem B1334999 : Blo 888571 1334999 := bstep (se 1 (by rfl) ⟨1001249, by rfl⟩ : syracuseStep 1334999 = 2002499) B2002499
theorem B1335065 : Blo 888571 1335065 := bstep (se 2 (by rfl) ⟨500649, by rfl⟩ : syracuseStep 1335065 = 1001299) B1001299
theorem B19259201 : Blo 888571 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B1335179 : Blo 888571 1335179 := bstep (se 1 (by rfl) ⟨1001384, by rfl⟩ : syracuseStep 1335179 = 2002769) B2002769
theorem B1335191 : Blo 888571 1335191 := bstep (se 1 (by rfl) ⟨1001393, by rfl⟩ : syracuseStep 1335191 = 2002787) B2002787
theorem B1335257 : Blo 888571 1335257 := bstep (se 2 (by rfl) ⟨500721, by rfl⟩ : syracuseStep 1335257 = 1001443) B1001443
theorem B1335371 : Blo 888571 1335371 := bstep (se 1 (by rfl) ⟨1001528, by rfl⟩ : syracuseStep 1335371 = 2003057) B2003057
theorem B1335383 : Blo 888571 1335383 := bstep (se 1 (by rfl) ⟨1001537, by rfl⟩ : syracuseStep 1335383 = 2003075) B2003075
theorem B3006557 : Blo 888571 3006557 := bstep (se 3 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 3006557 = 1127459) B1127459
theorem B1335449 : Blo 888571 1335449 := bstep (se 2 (by rfl) ⟨500793, by rfl⟩ : syracuseStep 1335449 = 1001587) B1001587
theorem B1269913 : Blo 888571 1269913 := bstep (se 2 (by rfl) ⟨476217, by rfl⟩ : syracuseStep 1269913 = 952435) B952435
theorem B1335563 : Blo 888571 1335563 := bstep (se 1 (by rfl) ⟨1001672, by rfl⟩ : syracuseStep 1335563 = 2003345) B2003345
theorem B1335575 : Blo 888571 1335575 := bstep (se 1 (by rfl) ⟨1001681, by rfl⟩ : syracuseStep 1335575 = 2003363) B2003363
theorem B1958195 : Blo 888571 1958195 := bstep (se 1 (by rfl) ⟨1468646, by rfl⟩ : syracuseStep 1958195 = 2937293) B2937293
theorem B1335641 : Blo 888571 1335641 := bstep (se 2 (by rfl) ⟨500865, by rfl⟩ : syracuseStep 1335641 = 1001731) B1001731
theorem B5497267 : Blo 888571 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B1335755 : Blo 888571 1335755 := bstep (se 1 (by rfl) ⟨1001816, by rfl⟩ : syracuseStep 1335755 = 2003633) B2003633
theorem B1335767 : Blo 888571 1335767 := bstep (se 1 (by rfl) ⟨1001825, by rfl⟩ : syracuseStep 1335767 = 2003651) B2003651
theorem B1335833 : Blo 888571 1335833 := bstep (se 2 (by rfl) ⟨500937, by rfl⟩ : syracuseStep 1335833 = 1001875) B1001875
theorem B1499735 : Blo 888571 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B1335947 : Blo 888571 1335947 := bstep (se 1 (by rfl) ⟨1001960, by rfl⟩ : syracuseStep 1335947 = 2003921) B2003921
theorem B1335959 : Blo 888571 1335959 := bstep (se 1 (by rfl) ⟨1001969, by rfl⟩ : syracuseStep 1335959 = 2003939) B2003939
theorem B2253491 : Blo 888571 2253491 := bstep (se 1 (by rfl) ⟨1690118, by rfl⟩ : syracuseStep 2253491 = 3380237) B3380237
theorem B1499863 : Blo 888571 1499863 := bstep (se 1 (by rfl) ⟨1124897, by rfl⟩ : syracuseStep 1499863 = 2249795) B2249795
theorem B1336025 : Blo 888571 1336025 := bstep (se 2 (by rfl) ⟨501009, by rfl⟩ : syracuseStep 1336025 = 1002019) B1002019
theorem B6415121 : Blo 888571 6415121 := bstep (se 2 (by rfl) ⟨2405670, by rfl⟩ : syracuseStep 6415121 = 4811341) B4811341
theorem B5202733 : Blo 888571 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B1336139 : Blo 888571 1336139 := bstep (se 1 (by rfl) ⟨1002104, by rfl⟩ : syracuseStep 1336139 = 2004209) B2004209
theorem B1336151 : Blo 888571 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B1336217 : Blo 888571 1336217 := bstep (se 2 (by rfl) ⟨501081, by rfl⟩ : syracuseStep 1336217 = 1002163) B1002163
theorem B4514777 : Blo 888571 4514777 := bstep (se 2 (by rfl) ⟨1693041, by rfl⟩ : syracuseStep 4514777 = 3386083) B3386083
theorem B1336331 : Blo 888571 1336331 := bstep (se 1 (by rfl) ⟨1002248, by rfl⟩ : syracuseStep 1336331 = 2004497) B2004497
theorem B1336343 : Blo 888571 1336343 := bstep (se 1 (by rfl) ⟨1002257, by rfl⟩ : syracuseStep 1336343 = 2004515) B2004515
theorem B3204161 : Blo 888571 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B1336409 : Blo 888571 1336409 := bstep (se 2 (by rfl) ⟨501153, by rfl⟩ : syracuseStep 1336409 = 1002307) B1002307
theorem B22832279 : Blo 888571 22832279 := bstep (se 1 (by rfl) ⟨17124209, by rfl⟩ : syracuseStep 22832279 = 34248419) B34248419
theorem B2254027 : Blo 888571 2254027 := bstep (se 1 (by rfl) ⟨1690520, by rfl⟩ : syracuseStep 2254027 = 3381041) B3381041
theorem B1336523 : Blo 888571 1336523 := bstep (se 1 (by rfl) ⟨1002392, by rfl⟩ : syracuseStep 1336523 = 2004785) B2004785
theorem B3007691 : Blo 888571 3007691 := bstep (se 1 (by rfl) ⟨2255768, by rfl⟩ : syracuseStep 3007691 = 4511537) B4511537
theorem B1336535 : Blo 888571 1336535 := bstep (se 1 (by rfl) ⟨1002401, by rfl⟩ : syracuseStep 1336535 = 2004803) B2004803
theorem B3433751 : Blo 888571 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B1336601 : Blo 888571 1336601 := bstep (se 2 (by rfl) ⟨501225, by rfl⟩ : syracuseStep 1336601 = 1002451) B1002451
theorem B1500491 : Blo 888571 1500491 := bstep (se 1 (by rfl) ⟨1125368, by rfl⟩ : syracuseStep 1500491 = 2250737) B2250737
theorem B2254169 : Blo 888571 2254169 := bstep (se 2 (by rfl) ⟨845313, by rfl⟩ : syracuseStep 2254169 = 1690627) B1690627
theorem B1336715 : Blo 888571 1336715 := bstep (se 1 (by rfl) ⟨1002536, by rfl⟩ : syracuseStep 1336715 = 2005073) B2005073
theorem B1336727 : Blo 888571 1336727 := bstep (se 1 (by rfl) ⟨1002545, by rfl⟩ : syracuseStep 1336727 = 2005091) B2005091
theorem B1500619 : Blo 888571 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B1336793 : Blo 888571 1336793 := bstep (se 2 (by rfl) ⟨501297, by rfl⟩ : syracuseStep 1336793 = 1002595) B1002595
theorem B3007961 : Blo 888571 3007961 := bstep (se 2 (by rfl) ⟨1127985, by rfl⟩ : syracuseStep 3007961 = 2255971) B2255971
theorem B1336907 : Blo 888571 1336907 := bstep (se 1 (by rfl) ⟨1002680, by rfl⟩ : syracuseStep 1336907 = 2005361) B2005361
theorem B1336919 : Blo 888571 1336919 := bstep (se 1 (by rfl) ⟨1002689, by rfl⟩ : syracuseStep 1336919 = 2005379) B2005379
theorem B1500761 : Blo 888571 1500761 := bstep (se 2 (by rfl) ⟨562785, by rfl⟩ : syracuseStep 1500761 = 1125571) B1125571
theorem B1336985 : Blo 888571 1336985 := bstep (se 2 (by rfl) ⟨501369, by rfl⟩ : syracuseStep 1336985 = 1002739) B1002739
theorem B1500889 : Blo 888571 1500889 := bstep (se 2 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 1500889 = 1125667) B1125667
theorem B1337099 : Blo 888571 1337099 := bstep (se 1 (by rfl) ⟨1002824, by rfl⟩ : syracuseStep 1337099 = 2005649) B2005649
theorem B1337111 : Blo 888571 1337111 := bstep (se 1 (by rfl) ⟨1002833, by rfl⟩ : syracuseStep 1337111 = 2005667) B2005667
theorem B1337177 : Blo 888571 1337177 := bstep (se 2 (by rfl) ⟨501441, by rfl⟩ : syracuseStep 1337177 = 1002883) B1002883
theorem B1337291 : Blo 888571 1337291 := bstep (se 1 (by rfl) ⟨1002968, by rfl⟩ : syracuseStep 1337291 = 2005937) B2005937
theorem B1337303 : Blo 888571 1337303 := bstep (se 1 (by rfl) ⟨1002977, by rfl⟩ : syracuseStep 1337303 = 2005955) B2005955
theorem B1206295 : Blo 888571 1206295 := bstep (se 1 (by rfl) ⟨904721, by rfl⟩ : syracuseStep 1206295 = 1809443) B1809443
theorem B1337369 : Blo 888571 1337369 := bstep (se 2 (by rfl) ⟨501513, by rfl⟩ : syracuseStep 1337369 = 1003027) B1003027
theorem B1337483 : Blo 888571 1337483 := bstep (se 1 (by rfl) ⟨1003112, by rfl⟩ : syracuseStep 1337483 = 2006225) B2006225
theorem B2254999 : Blo 888571 2254999 := bstep (se 1 (by rfl) ⟨1691249, by rfl⟩ : syracuseStep 2254999 = 3382499) B3382499
theorem B3008663 : Blo 888571 3008663 := bstep (se 1 (by rfl) ⟨2256497, by rfl⟩ : syracuseStep 3008663 = 4512995) B4512995
theorem B1337495 : Blo 888571 1337495 := bstep (se 1 (by rfl) ⟨1003121, by rfl⟩ : syracuseStep 1337495 = 2006243) B2006243
theorem B5695667 : Blo 888571 5695667 := bstep (se 1 (by rfl) ⟨4271750, by rfl⟩ : syracuseStep 5695667 = 8543501) B8543501
theorem B1337561 : Blo 888571 1337561 := bstep (se 2 (by rfl) ⟨501585, by rfl⟩ : syracuseStep 1337561 = 1003171) B1003171
theorem B1501463 : Blo 888571 1501463 := bstep (se 1 (by rfl) ⟨1126097, by rfl⟩ : syracuseStep 1501463 = 2252195) B2252195
theorem B1337675 : Blo 888571 1337675 := bstep (se 1 (by rfl) ⟨1003256, by rfl⟩ : syracuseStep 1337675 = 2006513) B2006513
theorem B1337687 : Blo 888571 1337687 := bstep (se 1 (by rfl) ⟨1003265, by rfl⟩ : syracuseStep 1337687 = 2006531) B2006531
theorem B1501591 : Blo 888571 1501591 := bstep (se 1 (by rfl) ⟨1126193, by rfl⟩ : syracuseStep 1501591 = 2252387) B2252387
theorem B1337753 : Blo 888571 1337753 := bstep (se 2 (by rfl) ⟨501657, by rfl⟩ : syracuseStep 1337753 = 1003315) B1003315
theorem B1337867 : Blo 888571 1337867 := bstep (se 1 (by rfl) ⟨1003400, by rfl⟩ : syracuseStep 1337867 = 2006801) B2006801
theorem B1337879 : Blo 888571 1337879 := bstep (se 1 (by rfl) ⟨1003409, by rfl⟩ : syracuseStep 1337879 = 2006819) B2006819
theorem B4516397 : Blo 888571 4516397 := bstep (se 3 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 4516397 = 1693649) B1693649
theorem B2255435 : Blo 888571 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B1337945 : Blo 888571 1337945 := bstep (se 2 (by rfl) ⟨501729, by rfl⟩ : syracuseStep 1337945 = 1003459) B1003459
theorem B2058905 : Blo 888571 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B3009203 : Blo 888571 3009203 := bstep (se 1 (by rfl) ⟨2256902, by rfl⟩ : syracuseStep 3009203 = 4513805) B4513805
theorem B1338059 : Blo 888571 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B1338071 : Blo 888571 1338071 := bstep (se 1 (by rfl) ⟨1003553, by rfl⟩ : syracuseStep 1338071 = 2007107) B2007107
theorem B1338137 : Blo 888571 1338137 := bstep (se 2 (by rfl) ⟨501801, by rfl⟩ : syracuseStep 1338137 = 1003603) B1003603
theorem B1338251 : Blo 888571 1338251 := bstep (se 1 (by rfl) ⟨1003688, by rfl⟩ : syracuseStep 1338251 = 2007377) B2007377
theorem B1338263 : Blo 888571 1338263 := bstep (se 1 (by rfl) ⟨1003697, by rfl⟩ : syracuseStep 1338263 = 2007395) B2007395
theorem B2255809 : Blo 888571 2255809 := bstep (se 2 (by rfl) ⟨845928, by rfl⟩ : syracuseStep 2255809 = 1691857) B1691857
theorem B3009473 : Blo 888571 3009473 := bstep (se 2 (by rfl) ⟨1128552, by rfl⟩ : syracuseStep 3009473 = 2257105) B2257105
theorem B1338329 : Blo 888571 1338329 := bstep (se 2 (by rfl) ⟨501873, by rfl⟩ : syracuseStep 1338329 = 1003747) B1003747
theorem B1502219 : Blo 888571 1502219 := bstep (se 1 (by rfl) ⟨1126664, by rfl⟩ : syracuseStep 1502219 = 2253329) B2253329
theorem B7597091 : Blo 888571 7597091 := bstep (se 1 (by rfl) ⟨5697818, by rfl⟩ : syracuseStep 7597091 = 11395637) B11395637
theorem B3042379 : Blo 888571 3042379 := bstep (se 1 (by rfl) ⟨2281784, by rfl⟩ : syracuseStep 3042379 = 4563569) B4563569
theorem B1338443 : Blo 888571 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B1338455 : Blo 888571 1338455 := bstep (se 1 (by rfl) ⟨1003841, by rfl⟩ : syracuseStep 1338455 = 2007683) B2007683
theorem B1502347 : Blo 888571 1502347 := bstep (se 1 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 1502347 = 2253521) B2253521
theorem B1338521 : Blo 888571 1338521 := bstep (se 2 (by rfl) ⟨501945, by rfl⟩ : syracuseStep 1338521 = 1003891) B1003891
theorem B1338635 : Blo 888571 1338635 := bstep (se 1 (by rfl) ⟨1003976, by rfl⟩ : syracuseStep 1338635 = 2007953) B2007953
theorem B1338647 : Blo 888571 1338647 := bstep (se 1 (by rfl) ⟨1003985, by rfl⟩ : syracuseStep 1338647 = 2007971) B2007971
theorem B1502489 : Blo 888571 1502489 := bstep (se 2 (by rfl) ⟨563433, by rfl⟩ : syracuseStep 1502489 = 1126867) B1126867
theorem B1338713 : Blo 888571 1338713 := bstep (se 2 (by rfl) ⟨502017, by rfl⟩ : syracuseStep 1338713 = 1004035) B1004035
theorem B7236965 : Blo 888571 7236965 := bstep (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) B1356931
theorem B1502617 : Blo 888571 1502617 := bstep (se 2 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 1502617 = 1126963) B1126963
theorem B1338827 : Blo 888571 1338827 := bstep (se 1 (by rfl) ⟨1004120, by rfl⟩ : syracuseStep 1338827 = 2008241) B2008241
theorem B1338839 : Blo 888571 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B3010013 : Blo 888571 3010013 := bstep (se 3 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 3010013 = 1128755) B1128755
theorem B2256407 : Blo 888571 2256407 := bstep (se 1 (by rfl) ⟨1692305, by rfl⟩ : syracuseStep 2256407 = 3384611) B3384611
theorem B6844121 : Blo 888571 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B3796753 : Blo 888571 3796753 := bstep (se 2 (by rfl) ⟨1423782, by rfl⟩ : syracuseStep 3796753 = 2847565) B2847565
theorem B1503191 : Blo 888571 1503191 := bstep (se 1 (by rfl) ⟨1127393, by rfl⟩ : syracuseStep 1503191 = 2254787) B2254787
theorem B1503319 : Blo 888571 1503319 := bstep (se 1 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 1503319 = 2254979) B2254979
theorem B4059409 : Blo 888571 4059409 := bstep (se 2 (by rfl) ⟨1522278, by rfl⟩ : syracuseStep 4059409 = 3044557) B3044557
theorem B3207475 : Blo 888571 3207475 := bstep (se 1 (by rfl) ⟨2405606, by rfl⟩ : syracuseStep 3207475 = 4811213) B4811213
theorem B2257217 : Blo 888571 2257217 := bstep (se 2 (by rfl) ⟨846456, by rfl⟩ : syracuseStep 2257217 = 1692913) B1692913
theorem B2028107 : Blo 888571 2028107 := bstep (se 1 (by rfl) ⟨1521080, by rfl⟩ : syracuseStep 2028107 = 3042161) B3042161
theorem B3011147 : Blo 888571 3011147 := bstep (se 1 (by rfl) ⟨2258360, by rfl⟩ : syracuseStep 3011147 = 4516721) B4516721
theorem B1602137 : Blo 888571 1602137 := bstep (se 2 (by rfl) ⟨600801, by rfl⟩ : syracuseStep 1602137 = 1201603) B1201603
theorem B1503947 : Blo 888571 1503947 := bstep (se 1 (by rfl) ⟨1127960, by rfl⟩ : syracuseStep 1503947 = 2255921) B2255921
theorem B7205593 : Blo 888571 7205593 := bstep (se 2 (by rfl) ⟨2702097, by rfl⟩ : syracuseStep 7205593 = 5404195) B5404195
theorem B2028289 : Blo 888571 2028289 := bstep (se 2 (by rfl) ⟨760608, by rfl⟩ : syracuseStep 2028289 = 1521217) B1521217
theorem B1504075 : Blo 888571 1504075 := bstep (se 1 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 1504075 = 2256113) B2256113
theorem B2847577 : Blo 888571 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B2257753 : Blo 888571 2257753 := bstep (se 2 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 2257753 = 1693315) B1693315
theorem B3011417 : Blo 888571 3011417 := bstep (se 2 (by rfl) ⟨1129281, by rfl⟩ : syracuseStep 3011417 = 2258563) B2258563
theorem B5075891 : Blo 888571 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B1504217 : Blo 888571 1504217 := bstep (se 2 (by rfl) ⟨564081, by rfl⟩ : syracuseStep 1504217 = 1128163) B1128163
theorem B10154969 : Blo 888571 10154969 := bstep (se 2 (by rfl) ⟨3808113, by rfl⟩ : syracuseStep 10154969 = 7616227) B7616227
theorem B1504345 : Blo 888571 1504345 := bstep (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) B1128259
theorem B8123597 : Blo 888571 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B8352973 : Blo 888571 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B1602931 : Blo 888571 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B2848193 : Blo 888571 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B3012119 : Blo 888571 3012119 := bstep (se 1 (by rfl) ⟨2259089, by rfl⟩ : syracuseStep 3012119 = 4518179) B4518179
theorem B1898009 : Blo 888571 1898009 := bstep (se 2 (by rfl) ⟨711753, by rfl⟩ : syracuseStep 1898009 = 1423507) B1423507
theorem B1603147 : Blo 888571 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B1504919 : Blo 888571 1504919 := bstep (se 1 (by rfl) ⟨1128689, by rfl⟩ : syracuseStep 1504919 = 2257379) B2257379
theorem B1505047 : Blo 888571 1505047 := bstep (se 1 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 1505047 = 2257571) B2257571
theorem B5699459 : Blo 888571 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B1898419 : Blo 888571 1898419 := bstep (se 1 (by rfl) ⟨1423814, by rfl⟩ : syracuseStep 1898419 = 2847629) B2847629
theorem B2258867 : Blo 888571 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B6748109 : Blo 888571 6748109 := bstep (se 3 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 6748109 = 2530541) B2530541
theorem B6420485 : Blo 888571 6420485 := bstep (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) B1203841
theorem B6420545 : Blo 888571 6420545 := bstep (se 2 (by rfl) ⟨2407704, by rfl⟩ : syracuseStep 6420545 = 4815409) B4815409
theorem B2259161 : Blo 888571 2259161 := bstep (se 2 (by rfl) ⟨847185, by rfl⟩ : syracuseStep 2259161 = 1694371) B1694371
theorem B5077349 : Blo 888571 5077349 := bstep (se 4 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 5077349 = 952003) B952003
theorem B1603955 : Blo 888571 1603955 := bstep (se 1 (by rfl) ⟨1202966, by rfl⟩ : syracuseStep 1603955 = 2405933) B2405933
theorem B1505675 : Blo 888571 1505675 := bstep (se 1 (by rfl) ⟨1129256, by rfl⟩ : syracuseStep 1505675 = 2258513) B2258513
theorem B6748595 : Blo 888571 6748595 := bstep (se 1 (by rfl) ⟨5061446, by rfl⟩ : syracuseStep 6748595 = 10122893) B10122893
theorem B7829965 : Blo 888571 7829965 := bstep (se 3 (by rfl) ⟨1468118, by rfl⟩ : syracuseStep 7829965 = 2936237) B2936237
theorem B1505803 : Blo 888571 1505803 := bstep (se 1 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 1505803 = 2258705) B2258705
theorem B7600715 : Blo 888571 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B1374871 : Blo 888571 1374871 := bstep (se 1 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 1374871 = 2062307) B2062307
theorem B1505945 : Blo 888571 1505945 := bstep (se 2 (by rfl) ⟨564729, by rfl⟩ : syracuseStep 1505945 = 1129459) B1129459
theorem B948919 : Blo 888571 948919 := bstep (se 1 (by rfl) ⟨711689, by rfl⟩ : syracuseStep 948919 = 1423379) B1423379
theorem B1014487 : Blo 888571 1014487 := bstep (se 1 (by rfl) ⟨760865, by rfl⟩ : syracuseStep 1014487 = 1521731) B1521731
theorem B3799811 : Blo 888571 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B1506073 : Blo 888571 1506073 := bstep (se 2 (by rfl) ⟨564777, by rfl⟩ : syracuseStep 1506073 = 1129555) B1129555
theorem B1604531 : Blo 888571 1604531 := bstep (se 1 (by rfl) ⟨1203398, by rfl⟩ : syracuseStep 1604531 = 2406797) B2406797
theorem B1899607 : Blo 888571 1899607 := bstep (se 1 (by rfl) ⟨1424705, by rfl⟩ : syracuseStep 1899607 = 2849411) B2849411
theorem B3210329 : Blo 888571 3210329 := bstep (se 2 (by rfl) ⟨1203873, by rfl⟩ : syracuseStep 3210329 = 2407747) B2407747
theorem B1899649 : Blo 888571 1899649 := bstep (se 2 (by rfl) ⟨712368, by rfl⟩ : syracuseStep 1899649 = 1424737) B1424737
theorem B2030771 : Blo 888571 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B949483 : Blo 888571 949483 := bstep (se 1 (by rfl) ⟨712112, by rfl⟩ : syracuseStep 949483 = 1424225) B1424225
theorem B949739 : Blo 888571 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B22871645 : Blo 888571 22871645 := bstep (se 3 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 22871645 = 8576867) B8576867
theorem B3374723 : Blo 888571 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B4816685 : Blo 888571 4816685 := bstep (se 3 (by rfl) ⟨903128, by rfl⟩ : syracuseStep 4816685 = 1806257) B1806257
theorem B2850653 : Blo 888571 2850653 := bstep (se 3 (by rfl) ⟨534497, by rfl⟩ : syracuseStep 2850653 = 1068995) B1068995
theorem B6750053 : Blo 888571 6750053 := bstep (se 4 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 6750053 = 1265635) B1265635
theorem B3211655 : Blo 888571 3211655 := bstep (se 1 (by rfl) ⟨2408741, by rfl⟩ : syracuseStep 3211655 = 4817483) B4817483
theorem B5079581 : Blo 888571 5079581 := bstep (se 3 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 5079581 = 1904843) B1904843
theorem B1999403 : Blo 888571 1999403 := bstep (se 1 (by rfl) ⟨1499552, by rfl⟩ : syracuseStep 1999403 = 2999105) B2999105
theorem B6423083 : Blo 888571 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B6751025 : Blo 888571 6751025 := bstep (se 2 (by rfl) ⟨2531634, by rfl⟩ : syracuseStep 6751025 = 5063269) B5063269
theorem B1082255 : Blo 888571 1082255 := bstep (se 1 (by rfl) ⟨811691, by rfl⟩ : syracuseStep 1082255 = 1623383) B1623383
theorem B1999763 : Blo 888571 1999763 := bstep (se 1 (by rfl) ⟨1499822, by rfl⟩ : syracuseStep 1999763 = 2999645) B2999645
theorem B1999817 : Blo 888571 1999817 := bstep (se 2 (by rfl) ⟨749931, by rfl⟩ : syracuseStep 1999817 = 1499863) B1499863
theorem B951311 : Blo 888571 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B5080265 : Blo 888571 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B2852243 : Blo 888571 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B2000519 : Blo 888571 2000519 := bstep (se 1 (by rfl) ⟨1500389, by rfl⟩ : syracuseStep 2000519 = 3000779) B3000779
theorem B2033353 : Blo 888571 2033353 := bstep (se 2 (by rfl) ⟨762507, by rfl⟩ : syracuseStep 2033353 = 1525015) B1525015
theorem B2000699 : Blo 888571 2000699 := bstep (se 1 (by rfl) ⟨1500524, by rfl⟩ : syracuseStep 2000699 = 3001049) B3001049
theorem B10127267 : Blo 888571 10127267 := bstep (se 1 (by rfl) ⟨7595450, by rfl⟩ : syracuseStep 10127267 = 15190901) B15190901
theorem B2000825 : Blo 888571 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B952507 : Blo 888571 952507 := bstep (se 1 (by rfl) ⟨714380, by rfl⟩ : syracuseStep 952507 = 1428761) B1428761
theorem B1902793 : Blo 888571 1902793 := bstep (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) B1427095
theorem B1083655 : Blo 888571 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B2001167 : Blo 888571 2001167 := bstep (se 1 (by rfl) ⟨1500875, by rfl⟩ : syracuseStep 2001167 = 3001751) B3001751
theorem B2001185 : Blo 888571 2001185 := bstep (se 2 (by rfl) ⟨750444, by rfl⟩ : syracuseStep 2001185 = 1500889) B1500889
theorem B9767303 : Blo 888571 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B6425041 : Blo 888571 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B2001527 : Blo 888571 2001527 := bstep (se 1 (by rfl) ⟨1501145, by rfl⟩ : syracuseStep 2001527 = 3002291) B3002291
theorem B11406095 : Blo 888571 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B2001707 : Blo 888571 2001707 := bstep (se 1 (by rfl) ⟨1501280, by rfl⟩ : syracuseStep 2001707 = 3002561) B3002561
theorem B5082041 : Blo 888571 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B2002067 : Blo 888571 2002067 := bstep (se 1 (by rfl) ⟨1501550, by rfl⟩ : syracuseStep 2002067 = 3003101) B3003101
theorem B2002121 : Blo 888571 2002121 := bstep (se 2 (by rfl) ⟨750795, by rfl⟩ : syracuseStep 2002121 = 1501591) B1501591
theorem B9637213 : Blo 888571 9637213 := bstep (se 3 (by rfl) ⟨1806977, by rfl⟩ : syracuseStep 9637213 = 3613955) B3613955
theorem B5148107 : Blo 888571 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B1904143 : Blo 888571 1904143 := bstep (se 1 (by rfl) ⟨1428107, by rfl⟩ : syracuseStep 1904143 = 2856215) B2856215
theorem B5410327 : Blo 888571 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B5410423 : Blo 888571 5410423 := bstep (se 1 (by rfl) ⟨4057817, by rfl⟩ : syracuseStep 5410423 = 8115635) B8115635
theorem B888583 : Blo 888571 888583 := bstep (se 1 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 888583 = 1332875) B1332875
theorem B888591 : Blo 888571 888591 := bstep (se 1 (by rfl) ⟨666443, by rfl⟩ : syracuseStep 888591 = 1332887) B1332887
theorem B1904399 : Blo 888571 1904399 := bstep (se 1 (by rfl) ⟨1428299, by rfl⟩ : syracuseStep 1904399 = 2856599) B2856599
theorem B5410597 : Blo 888571 5410597 := bstep (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) B1014487
theorem B888635 : Blo 888571 888635 := bstep (se 1 (by rfl) ⟨666476, by rfl⟩ : syracuseStep 888635 = 1332953) B1332953
theorem B888711 : Blo 888571 888711 := bstep (se 1 (by rfl) ⟨666533, by rfl⟩ : syracuseStep 888711 = 1333067) B1333067
theorem B2002823 : Blo 888571 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B888719 : Blo 888571 888719 := bstep (se 1 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 888719 = 1333079) B1333079
theorem B3379097 : Blo 888571 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B888763 : Blo 888571 888763 := bstep (se 1 (by rfl) ⟨666572, by rfl⟩ : syracuseStep 888763 = 1333145) B1333145
theorem B888839 : Blo 888571 888839 := bstep (se 1 (by rfl) ⟨666629, by rfl⟩ : syracuseStep 888839 = 1333259) B1333259
theorem B888847 : Blo 888571 888847 := bstep (se 1 (by rfl) ⟨666635, by rfl⟩ : syracuseStep 888847 = 1333271) B1333271
theorem B888891 : Blo 888571 888891 := bstep (se 1 (by rfl) ⟨666668, by rfl⟩ : syracuseStep 888891 = 1333337) B1333337
theorem B2003003 : Blo 888571 2003003 := bstep (se 1 (by rfl) ⟨1502252, by rfl⟩ : syracuseStep 2003003 = 3004505) B3004505
theorem B5705815 : Blo 888571 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B888967 : Blo 888571 888967 := bstep (se 1 (by rfl) ⟨666725, by rfl⟩ : syracuseStep 888967 = 1333451) B1333451
theorem B888975 : Blo 888571 888975 := bstep (se 1 (by rfl) ⟨666731, by rfl⟩ : syracuseStep 888975 = 1333463) B1333463
theorem B2003129 : Blo 888571 2003129 := bstep (se 2 (by rfl) ⟨751173, by rfl⟩ : syracuseStep 2003129 = 1502347) B1502347
theorem B889019 : Blo 888571 889019 := bstep (se 1 (by rfl) ⟨666764, by rfl⟩ : syracuseStep 889019 = 1333529) B1333529
theorem B889095 : Blo 888571 889095 := bstep (se 1 (by rfl) ⟨666821, by rfl⟩ : syracuseStep 889095 = 1333643) B1333643
theorem B889103 : Blo 888571 889103 := bstep (se 1 (by rfl) ⟨666827, by rfl⟩ : syracuseStep 889103 = 1333655) B1333655
theorem B889147 : Blo 888571 889147 := bstep (se 1 (by rfl) ⟨666860, by rfl⟩ : syracuseStep 889147 = 1333721) B1333721
theorem B889223 : Blo 888571 889223 := bstep (se 1 (by rfl) ⟨666917, by rfl⟩ : syracuseStep 889223 = 1333835) B1333835
theorem B889231 : Blo 888571 889231 := bstep (se 1 (by rfl) ⟨666923, by rfl⟩ : syracuseStep 889231 = 1333847) B1333847
theorem B889275 : Blo 888571 889275 := bstep (se 1 (by rfl) ⟨666956, by rfl⟩ : syracuseStep 889275 = 1333913) B1333913
theorem B889351 : Blo 888571 889351 := bstep (se 1 (by rfl) ⟨667013, by rfl⟩ : syracuseStep 889351 = 1334027) B1334027
theorem B889359 : Blo 888571 889359 := bstep (se 1 (by rfl) ⟨667019, by rfl⟩ : syracuseStep 889359 = 1334039) B1334039
theorem B2003471 : Blo 888571 2003471 := bstep (se 1 (by rfl) ⟨1502603, by rfl⟩ : syracuseStep 2003471 = 3005207) B3005207
theorem B2003489 : Blo 888571 2003489 := bstep (se 2 (by rfl) ⟨751308, by rfl⟩ : syracuseStep 2003489 = 1502617) B1502617
theorem B889403 : Blo 888571 889403 := bstep (se 1 (by rfl) ⟨667052, by rfl⟩ : syracuseStep 889403 = 1334105) B1334105
theorem B1806907 : Blo 888571 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B1905211 : Blo 888571 1905211 := bstep (se 1 (by rfl) ⟨1428908, by rfl⟩ : syracuseStep 1905211 = 2857817) B2857817
theorem B889479 : Blo 888571 889479 := bstep (se 1 (by rfl) ⟨667109, by rfl⟩ : syracuseStep 889479 = 1334219) B1334219
theorem B1905287 : Blo 888571 1905287 := bstep (se 1 (by rfl) ⟨1428965, by rfl⟩ : syracuseStep 1905287 = 2857931) B2857931
theorem B889487 : Blo 888571 889487 := bstep (se 1 (by rfl) ⟨667115, by rfl⟩ : syracuseStep 889487 = 1334231) B1334231
theorem B889531 : Blo 888571 889531 := bstep (se 1 (by rfl) ⟨667148, by rfl⟩ : syracuseStep 889531 = 1334297) B1334297
theorem B889607 : Blo 888571 889607 := bstep (se 1 (by rfl) ⟨667205, by rfl⟩ : syracuseStep 889607 = 1334411) B1334411
theorem B889615 : Blo 888571 889615 := bstep (se 1 (by rfl) ⟨667211, by rfl⟩ : syracuseStep 889615 = 1334423) B1334423
theorem B889659 : Blo 888571 889659 := bstep (se 1 (by rfl) ⟨667244, by rfl⟩ : syracuseStep 889659 = 1334489) B1334489
theorem B4821875 : Blo 888571 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B2003831 : Blo 888571 2003831 := bstep (se 1 (by rfl) ⟨1502873, by rfl⟩ : syracuseStep 2003831 = 3005747) B3005747
theorem B1905527 : Blo 888571 1905527 := bstep (se 1 (by rfl) ⟨1429145, by rfl⟩ : syracuseStep 1905527 = 2858291) B2858291
theorem B889735 : Blo 888571 889735 := bstep (se 1 (by rfl) ⟨667301, by rfl⟩ : syracuseStep 889735 = 1334603) B1334603
theorem B889743 : Blo 888571 889743 := bstep (se 1 (by rfl) ⟨667307, by rfl⟩ : syracuseStep 889743 = 1334615) B1334615
theorem B3806099 : Blo 888571 3806099 := bstep (se 1 (by rfl) ⟨2854574, by rfl⟩ : syracuseStep 3806099 = 5709149) B5709149
theorem B140743601 : Blo 888571 140743601 := bstep (se 2 (by rfl) ⟨52778850, by rfl⟩ : syracuseStep 140743601 = 105557701) B105557701
theorem B889787 : Blo 888571 889787 := bstep (se 1 (by rfl) ⟨667340, by rfl⟩ : syracuseStep 889787 = 1334681) B1334681
theorem B889863 : Blo 888571 889863 := bstep (se 1 (by rfl) ⟨667397, by rfl⟩ : syracuseStep 889863 = 1334795) B1334795
theorem B889871 : Blo 888571 889871 := bstep (se 1 (by rfl) ⟨667403, by rfl⟩ : syracuseStep 889871 = 1334807) B1334807
theorem B1905697 : Blo 888571 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B2004011 : Blo 888571 2004011 := bstep (se 1 (by rfl) ⟨1503008, by rfl⟩ : syracuseStep 2004011 = 3006017) B3006017
theorem B889915 : Blo 888571 889915 := bstep (se 1 (by rfl) ⟨667436, by rfl⟩ : syracuseStep 889915 = 1334873) B1334873
theorem B889991 : Blo 888571 889991 := bstep (se 1 (by rfl) ⟨667493, by rfl⟩ : syracuseStep 889991 = 1334987) B1334987
theorem B889999 : Blo 888571 889999 := bstep (se 1 (by rfl) ⟨667499, by rfl⟩ : syracuseStep 889999 = 1334999) B1334999
theorem B890043 : Blo 888571 890043 := bstep (se 1 (by rfl) ⟨667532, by rfl⟩ : syracuseStep 890043 = 1335065) B1335065
theorem B890119 : Blo 888571 890119 := bstep (se 1 (by rfl) ⟨667589, by rfl⟩ : syracuseStep 890119 = 1335179) B1335179
theorem B890127 : Blo 888571 890127 := bstep (se 1 (by rfl) ⟨667595, by rfl⟩ : syracuseStep 890127 = 1335191) B1335191
theorem B890171 : Blo 888571 890171 := bstep (se 1 (by rfl) ⟨667628, by rfl⟩ : syracuseStep 890171 = 1335257) B1335257
theorem B1906039 : Blo 888571 1906039 := bstep (se 1 (by rfl) ⟨1429529, by rfl⟩ : syracuseStep 1906039 = 2859059) B2859059
theorem B890247 : Blo 888571 890247 := bstep (se 1 (by rfl) ⟨667685, by rfl⟩ : syracuseStep 890247 = 1335371) B1335371
theorem B890255 : Blo 888571 890255 := bstep (se 1 (by rfl) ⟨667691, by rfl⟩ : syracuseStep 890255 = 1335383) B1335383
theorem B2004371 : Blo 888571 2004371 := bstep (se 1 (by rfl) ⟨1503278, by rfl⟩ : syracuseStep 2004371 = 3006557) B3006557
theorem B890299 : Blo 888571 890299 := bstep (se 1 (by rfl) ⟨667724, by rfl⟩ : syracuseStep 890299 = 1335449) B1335449
theorem B2004425 : Blo 888571 2004425 := bstep (se 2 (by rfl) ⟨751659, by rfl⟩ : syracuseStep 2004425 = 1503319) B1503319
theorem B890375 : Blo 888571 890375 := bstep (se 1 (by rfl) ⟨667781, by rfl⟩ : syracuseStep 890375 = 1335563) B1335563
theorem B890383 : Blo 888571 890383 := bstep (se 1 (by rfl) ⟨667787, by rfl⟩ : syracuseStep 890383 = 1335575) B1335575
theorem B890427 : Blo 888571 890427 := bstep (se 1 (by rfl) ⟨667820, by rfl⟩ : syracuseStep 890427 = 1335641) B1335641
theorem B890503 : Blo 888571 890503 := bstep (se 1 (by rfl) ⟨667877, by rfl⟩ : syracuseStep 890503 = 1335755) B1335755
theorem B890511 : Blo 888571 890511 := bstep (se 1 (by rfl) ⟨667883, by rfl⟩ : syracuseStep 890511 = 1335767) B1335767
theorem B890555 : Blo 888571 890555 := bstep (se 1 (by rfl) ⟨667916, by rfl⟩ : syracuseStep 890555 = 1335833) B1335833
theorem B5412545 : Blo 888571 5412545 := bstep (se 2 (by rfl) ⟨2029704, by rfl⟩ : syracuseStep 5412545 = 4059409) B4059409
theorem B16226021 : Blo 888571 16226021 := bstep (se 4 (by rfl) ⟨1521189, by rfl⟩ : syracuseStep 16226021 = 3042379) B3042379
theorem B890631 : Blo 888571 890631 := bstep (se 1 (by rfl) ⟨667973, by rfl⟩ : syracuseStep 890631 = 1335947) B1335947
theorem B890639 : Blo 888571 890639 := bstep (se 1 (by rfl) ⟨667979, by rfl⟩ : syracuseStep 890639 = 1335959) B1335959
theorem B890683 : Blo 888571 890683 := bstep (se 1 (by rfl) ⟨668012, by rfl⟩ : syracuseStep 890683 = 1336025) B1336025
theorem B890759 : Blo 888571 890759 := bstep (se 1 (by rfl) ⟨668069, by rfl⟩ : syracuseStep 890759 = 1336139) B1336139
theorem B890767 : Blo 888571 890767 := bstep (se 1 (by rfl) ⟨668075, by rfl⟩ : syracuseStep 890767 = 1336151) B1336151
theorem B890811 : Blo 888571 890811 := bstep (se 1 (by rfl) ⟨668108, by rfl⟩ : syracuseStep 890811 = 1336217) B1336217
theorem B890887 : Blo 888571 890887 := bstep (se 1 (by rfl) ⟨668165, by rfl⟩ : syracuseStep 890887 = 1336331) B1336331
theorem B890895 : Blo 888571 890895 := bstep (se 1 (by rfl) ⟨668171, by rfl⟩ : syracuseStep 890895 = 1336343) B1336343
theorem B2136107 : Blo 888571 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B890939 : Blo 888571 890939 := bstep (se 1 (by rfl) ⟨668204, by rfl⟩ : syracuseStep 890939 = 1336409) B1336409
theorem B891015 : Blo 888571 891015 := bstep (se 1 (by rfl) ⟨668261, by rfl⟩ : syracuseStep 891015 = 1336523) B1336523
theorem B2005127 : Blo 888571 2005127 := bstep (se 1 (by rfl) ⟨1503845, by rfl⟩ : syracuseStep 2005127 = 3007691) B3007691
theorem B891023 : Blo 888571 891023 := bstep (se 1 (by rfl) ⟨668267, by rfl⟩ : syracuseStep 891023 = 1336535) B1336535
theorem B891067 : Blo 888571 891067 := bstep (se 1 (by rfl) ⟨668300, by rfl⟩ : syracuseStep 891067 = 1336601) B1336601
theorem B891143 : Blo 888571 891143 := bstep (se 1 (by rfl) ⟨668357, by rfl⟩ : syracuseStep 891143 = 1336715) B1336715
theorem B891151 : Blo 888571 891151 := bstep (se 1 (by rfl) ⟨668363, by rfl⟩ : syracuseStep 891151 = 1336727) B1336727
theorem B9607457 : Blo 888571 9607457 := bstep (se 2 (by rfl) ⟨3602796, by rfl⟩ : syracuseStep 9607457 = 7205593) B7205593
theorem B891195 : Blo 888571 891195 := bstep (se 1 (by rfl) ⟨668396, by rfl⟩ : syracuseStep 891195 = 1336793) B1336793
theorem B2005307 : Blo 888571 2005307 := bstep (se 1 (by rfl) ⟨1503980, by rfl⟩ : syracuseStep 2005307 = 3007961) B3007961
theorem B891271 : Blo 888571 891271 := bstep (se 1 (by rfl) ⟨668453, by rfl⟩ : syracuseStep 891271 = 1336907) B1336907
theorem B891279 : Blo 888571 891279 := bstep (se 1 (by rfl) ⟨668459, by rfl⟩ : syracuseStep 891279 = 1336919) B1336919
theorem B2005433 : Blo 888571 2005433 := bstep (se 2 (by rfl) ⟨752037, by rfl⟩ : syracuseStep 2005433 = 1504075) B1504075
theorem B891323 : Blo 888571 891323 := bstep (se 1 (by rfl) ⟨668492, by rfl⟩ : syracuseStep 891323 = 1336985) B1336985
theorem B891399 : Blo 888571 891399 := bstep (se 1 (by rfl) ⟨668549, by rfl⟩ : syracuseStep 891399 = 1337099) B1337099
theorem B891407 : Blo 888571 891407 := bstep (se 1 (by rfl) ⟨668555, by rfl⟩ : syracuseStep 891407 = 1337111) B1337111
theorem B3807773 : Blo 888571 3807773 := bstep (se 3 (by rfl) ⟨713957, by rfl⟩ : syracuseStep 3807773 = 1427915) B1427915
theorem B891451 : Blo 888571 891451 := bstep (se 1 (by rfl) ⟨668588, by rfl⟩ : syracuseStep 891451 = 1337177) B1337177
theorem B891527 : Blo 888571 891527 := bstep (se 1 (by rfl) ⟨668645, by rfl⟩ : syracuseStep 891527 = 1337291) B1337291
theorem B891535 : Blo 888571 891535 := bstep (se 1 (by rfl) ⟨668651, by rfl⟩ : syracuseStep 891535 = 1337303) B1337303
theorem B891579 : Blo 888571 891579 := bstep (se 1 (by rfl) ⟨668684, by rfl⟩ : syracuseStep 891579 = 1337369) B1337369
theorem B891655 : Blo 888571 891655 := bstep (se 1 (by rfl) ⟨668741, by rfl⟩ : syracuseStep 891655 = 1337483) B1337483
theorem B2005775 : Blo 888571 2005775 := bstep (se 1 (by rfl) ⟨1504331, by rfl⟩ : syracuseStep 2005775 = 3008663) B3008663
theorem B891663 : Blo 888571 891663 := bstep (se 1 (by rfl) ⟨668747, by rfl⟩ : syracuseStep 891663 = 1337495) B1337495
theorem B2005793 : Blo 888571 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B891707 : Blo 888571 891707 := bstep (se 1 (by rfl) ⟨668780, by rfl⟩ : syracuseStep 891707 = 1337561) B1337561
theorem B891783 : Blo 888571 891783 := bstep (se 1 (by rfl) ⟨668837, by rfl⟩ : syracuseStep 891783 = 1337675) B1337675
theorem B891791 : Blo 888571 891791 := bstep (se 1 (by rfl) ⟨668843, by rfl⟩ : syracuseStep 891791 = 1337687) B1337687
theorem B891835 : Blo 888571 891835 := bstep (se 1 (by rfl) ⟨668876, by rfl⟩ : syracuseStep 891835 = 1337753) B1337753
theorem B891911 : Blo 888571 891911 := bstep (se 1 (by rfl) ⟨668933, by rfl⟩ : syracuseStep 891911 = 1337867) B1337867
theorem B891919 : Blo 888571 891919 := bstep (se 1 (by rfl) ⟨668939, by rfl⟩ : syracuseStep 891919 = 1337879) B1337879
theorem B891963 : Blo 888571 891963 := bstep (se 1 (by rfl) ⟨668972, by rfl⟩ : syracuseStep 891963 = 1337945) B1337945
theorem B2006135 : Blo 888571 2006135 := bstep (se 1 (by rfl) ⟨1504601, by rfl⟩ : syracuseStep 2006135 = 3009203) B3009203
theorem B892039 : Blo 888571 892039 := bstep (se 1 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 892039 = 1338059) B1338059
theorem B892047 : Blo 888571 892047 := bstep (se 1 (by rfl) ⟨669035, by rfl⟩ : syracuseStep 892047 = 1338071) B1338071
theorem B2137241 : Blo 888571 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B892091 : Blo 888571 892091 := bstep (se 1 (by rfl) ⟨669068, by rfl⟩ : syracuseStep 892091 = 1338137) B1338137
theorem B3808457 : Blo 888571 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B892167 : Blo 888571 892167 := bstep (se 1 (by rfl) ⟨669125, by rfl⟩ : syracuseStep 892167 = 1338251) B1338251
theorem B892175 : Blo 888571 892175 := bstep (se 1 (by rfl) ⟨669131, by rfl⟩ : syracuseStep 892175 = 1338263) B1338263
theorem B2006315 : Blo 888571 2006315 := bstep (se 1 (by rfl) ⟨1504736, by rfl⟩ : syracuseStep 2006315 = 3009473) B3009473
theorem B892219 : Blo 888571 892219 := bstep (se 1 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 892219 = 1338329) B1338329
theorem B892295 : Blo 888571 892295 := bstep (se 1 (by rfl) ⟨669221, by rfl⟩ : syracuseStep 892295 = 1338443) B1338443
theorem B892303 : Blo 888571 892303 := bstep (se 1 (by rfl) ⟨669227, by rfl⟩ : syracuseStep 892303 = 1338455) B1338455
theorem B3382681 : Blo 888571 3382681 := bstep (se 2 (by rfl) ⟨1268505, by rfl⟩ : syracuseStep 3382681 = 2537011) B2537011
theorem B2137529 : Blo 888571 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B892347 : Blo 888571 892347 := bstep (se 1 (by rfl) ⟨669260, by rfl⟩ : syracuseStep 892347 = 1338521) B1338521
theorem B892423 : Blo 888571 892423 := bstep (se 1 (by rfl) ⟨669317, by rfl⟩ : syracuseStep 892423 = 1338635) B1338635
theorem B892431 : Blo 888571 892431 := bstep (se 1 (by rfl) ⟨669323, by rfl⟩ : syracuseStep 892431 = 1338647) B1338647
theorem B892475 : Blo 888571 892475 := bstep (se 1 (by rfl) ⟨669356, by rfl⟩ : syracuseStep 892475 = 1338713) B1338713
theorem B4824643 : Blo 888571 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B892551 : Blo 888571 892551 := bstep (se 1 (by rfl) ⟨669413, by rfl⟩ : syracuseStep 892551 = 1338827) B1338827
theorem B892559 : Blo 888571 892559 := bstep (se 1 (by rfl) ⟨669419, by rfl⟩ : syracuseStep 892559 = 1338839) B1338839
theorem B2006675 : Blo 888571 2006675 := bstep (se 1 (by rfl) ⟨1505006, by rfl⟩ : syracuseStep 2006675 = 3010013) B3010013
theorem B3382985 : Blo 888571 3382985 := bstep (se 2 (by rfl) ⟨1268619, by rfl⟩ : syracuseStep 3382985 = 2537239) B2537239
theorem B2006729 : Blo 888571 2006729 := bstep (se 2 (by rfl) ⟨752523, by rfl⟩ : syracuseStep 2006729 = 1505047) B1505047
theorem B4562747 : Blo 888571 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B3612563 : Blo 888571 3612563 := bstep (se 1 (by rfl) ⟨2709422, by rfl⟩ : syracuseStep 3612563 = 5418845) B5418845
theorem B2531225 : Blo 888571 2531225 := bstep (se 2 (by rfl) ⟨949209, by rfl⟩ : syracuseStep 2531225 = 1898419) B1898419
theorem B2858905 : Blo 888571 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B1352071 : Blo 888571 1352071 := bstep (se 1 (by rfl) ⟨1014053, by rfl⟩ : syracuseStep 1352071 = 2028107) B2028107
theorem B2007431 : Blo 888571 2007431 := bstep (se 1 (by rfl) ⟨1505573, by rfl⟩ : syracuseStep 2007431 = 3011147) B3011147
theorem B6758801 : Blo 888571 6758801 := bstep (se 2 (by rfl) ⟨2534550, by rfl⟩ : syracuseStep 6758801 = 5069101) B5069101
theorem B5415389 : Blo 888571 5415389 := bstep (se 3 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 5415389 = 2030771) B2030771
theorem B2007611 : Blo 888571 2007611 := bstep (se 1 (by rfl) ⟨1505708, by rfl⟩ : syracuseStep 2007611 = 3011417) B3011417
theorem B3383927 : Blo 888571 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B2007737 : Blo 888571 2007737 := bstep (se 2 (by rfl) ⟨752901, by rfl⟩ : syracuseStep 2007737 = 1505803) B1505803
theorem B5415731 : Blo 888571 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B3810233 : Blo 888571 3810233 := bstep (se 2 (by rfl) ⟨1428837, by rfl⟩ : syracuseStep 3810233 = 2857675) B2857675
theorem B2008079 : Blo 888571 2008079 := bstep (se 1 (by rfl) ⟨1506059, by rfl⟩ : syracuseStep 2008079 = 3012119) B3012119
theorem B2008097 : Blo 888571 2008097 := bstep (se 2 (by rfl) ⟨753036, by rfl⟩ : syracuseStep 2008097 = 1506073) B1506073
theorem B2532637 : Blo 888571 2532637 := bstep (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) B949739
theorem B4498739 : Blo 888571 4498739 := bstep (se 1 (by rfl) ⟨3374054, by rfl⟩ : syracuseStep 4498739 = 6748109) B6748109
theorem B5711249 : Blo 888571 5711249 := bstep (se 2 (by rfl) ⟨2141718, by rfl⟩ : syracuseStep 5711249 = 4283437) B4283437
theorem B2532809 : Blo 888571 2532809 := bstep (se 2 (by rfl) ⟨949803, by rfl⟩ : syracuseStep 2532809 = 1899607) B1899607
theorem B2532865 : Blo 888571 2532865 := bstep (se 2 (by rfl) ⟨949824, by rfl⟩ : syracuseStep 2532865 = 1899649) B1899649
theorem B3384899 : Blo 888571 3384899 := bstep (se 1 (by rfl) ⟨2538674, by rfl⟩ : syracuseStep 3384899 = 5077349) B5077349
theorem B4499063 : Blo 888571 4499063 := bstep (se 1 (by rfl) ⟨3374297, by rfl⟩ : syracuseStep 4499063 = 6748595) B6748595
theorem B2533207 : Blo 888571 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B2140219 : Blo 888571 2140219 := bstep (se 1 (by rfl) ⟨1605164, by rfl⟩ : syracuseStep 2140219 = 3210329) B3210329
theorem B1124599 : Blo 888571 1124599 := bstep (se 1 (by rfl) ⟨843449, by rfl⟩ : syracuseStep 1124599 = 1686899) B1686899
theorem B15247763 : Blo 888571 15247763 := bstep (se 1 (by rfl) ⟨11435822, by rfl⟩ : syracuseStep 15247763 = 22871645) B22871645
theorem B4336075 : Blo 888571 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B1124923 : Blo 888571 1124923 := bstep (se 1 (by rfl) ⟨843692, by rfl⟩ : syracuseStep 1124923 = 1687385) B1687385
theorem B4500035 : Blo 888571 4500035 := bstep (se 1 (by rfl) ⟨3375026, by rfl⟩ : syracuseStep 4500035 = 6750053) B6750053
theorem B9612047 : Blo 888571 9612047 := bstep (se 1 (by rfl) ⟨7209035, by rfl⟩ : syracuseStep 9612047 = 14418071) B14418071
theorem B6761231 : Blo 888571 6761231 := bstep (se 1 (by rfl) ⟨5070923, by rfl⟩ : syracuseStep 6761231 = 10141847) B10141847
theorem B4500359 : Blo 888571 4500359 := bstep (se 1 (by rfl) ⟨3375269, by rfl⟩ : syracuseStep 4500359 = 6750539) B6750539
theorem B25734293 : Blo 888571 25734293 := bstep (se 6 (by rfl) ⟨603147, by rfl⟩ : syracuseStep 25734293 = 1206295) B1206295
theorem B3386569 : Blo 888571 3386569 := bstep (se 2 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 3386569 = 2539927) B2539927
theorem B3812609 : Blo 888571 3812609 := bstep (se 2 (by rfl) ⟨1429728, by rfl⟩ : syracuseStep 3812609 = 2859457) B2859457
theorem B17346001 : Blo 888571 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B1125895 : Blo 888571 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B3092087 : Blo 888571 3092087 := bstep (se 1 (by rfl) ⟨2319065, by rfl⟩ : syracuseStep 3092087 = 4638131) B4638131
theorem B1126315 : Blo 888571 1126315 := bstep (se 1 (by rfl) ⟨844736, by rfl⟩ : syracuseStep 1126315 = 1689473) B1689473
theorem B82161611 : Blo 888571 82161611 := bstep (se 1 (by rfl) ⟨61621208, by rfl⟩ : syracuseStep 82161611 = 123242417) B123242417
theorem B1126543 : Blo 888571 1126543 := bstep (se 1 (by rfl) ⟨844907, by rfl⟩ : syracuseStep 1126543 = 1689815) B1689815
theorem B2404505 : Blo 888571 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B5419181 : Blo 888571 5419181 := bstep (se 3 (by rfl) ⟨1016096, by rfl⟩ : syracuseStep 5419181 = 2032193) B2032193
theorem B4272365 : Blo 888571 4272365 := bstep (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) B1602137
theorem B8138989 : Blo 888571 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B2568719 : Blo 888571 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B2404979 : Blo 888571 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B2536055 : Blo 888571 2536055 := bstep (se 1 (by rfl) ⟨1902041, by rfl⟩ : syracuseStep 2536055 = 3804083) B3804083
theorem B1127287 : Blo 888571 1127287 := bstep (se 1 (by rfl) ⟨845465, by rfl⟩ : syracuseStep 1127287 = 1690931) B1690931
theorem B41759813 : Blo 888571 41759813 := bstep (se 4 (by rfl) ⟨3914982, by rfl⟩ : syracuseStep 41759813 = 7829965) B7829965
theorem B8107141 : Blo 888571 8107141 := bstep (se 4 (by rfl) ⟨760044, by rfl⟩ : syracuseStep 8107141 = 1520089) B1520089
theorem B1127611 : Blo 888571 1127611 := bstep (se 1 (by rfl) ⟨845708, by rfl⟩ : syracuseStep 1127611 = 1691417) B1691417
theorem B3388787 : Blo 888571 3388787 := bstep (se 1 (by rfl) ⟨2541590, by rfl⟩ : syracuseStep 3388787 = 5083181) B5083181
theorem B1128107 : Blo 888571 1128107 := bstep (se 1 (by rfl) ⟨846080, by rfl⟩ : syracuseStep 1128107 = 1692161) B1692161
theorem B1128583 : Blo 888571 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B5060879 : Blo 888571 5060879 := bstep (se 1 (by rfl) ⟨3795659, by rfl⟩ : syracuseStep 5060879 = 7591319) B7591319
theorem B4503923 : Blo 888571 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B83507597 : Blo 888571 83507597 := bstep (se 3 (by rfl) ⟨15657674, by rfl⟩ : syracuseStep 83507597 = 31315349) B31315349
theorem B9615761 : Blo 888571 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B4569643 : Blo 888571 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B1129079 : Blo 888571 1129079 := bstep (se 1 (by rfl) ⟨846809, by rfl⟩ : syracuseStep 1129079 = 1693619) B1693619
theorem B10140389 : Blo 888571 10140389 := bstep (se 4 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 10140389 = 1901323) B1901323
theorem B1129231 : Blo 888571 1129231 := bstep (se 1 (by rfl) ⟨846923, by rfl⟩ : syracuseStep 1129231 = 1693847) B1693847
theorem B2407229 : Blo 888571 2407229 := bstep (se 3 (by rfl) ⟨451355, by rfl⟩ : syracuseStep 2407229 = 902711) B902711
theorem B4504409 : Blo 888571 4504409 := bstep (se 2 (by rfl) ⟨1689153, by rfl⟩ : syracuseStep 4504409 = 3378307) B3378307
theorem B1129403 : Blo 888571 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B5716939 : Blo 888571 5716939 := bstep (se 1 (by rfl) ⟨4287704, by rfl⟩ : syracuseStep 5716939 = 8575409) B8575409
theorem B3423293 : Blo 888571 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B2538697 : Blo 888571 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B17087921 : Blo 888571 17087921 := bstep (se 2 (by rfl) ⟨6407970, by rfl⟩ : syracuseStep 17087921 = 12815941) B12815941
theorem B1687225 : Blo 888571 1687225 := bstep (se 2 (by rfl) ⟨632709, by rfl⟩ : syracuseStep 1687225 = 1265419) B1265419
theorem B5062337 : Blo 888571 5062337 := bstep (se 2 (by rfl) ⟨1898376, by rfl⟩ : syracuseStep 5062337 = 3796753) B3796753
theorem B17121293 : Blo 888571 17121293 := bstep (se 3 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 17121293 = 6420485) B6420485
theorem B1687567 : Blo 888571 1687567 := bstep (se 1 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 1687567 = 2531351) B2531351
theorem B999823 : Blo 888571 999823 := bstep (se 1 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 999823 = 1499735) B1499735
theorem B7618961 : Blo 888571 7618961 := bstep (se 2 (by rfl) ⟨2857110, by rfl⟩ : syracuseStep 7618961 = 5714221) B5714221
theorem B4276633 : Blo 888571 4276633 := bstep (se 2 (by rfl) ⟨1603737, by rfl⟩ : syracuseStep 4276633 = 3207475) B3207475
theorem B1425865 : Blo 888571 1425865 := bstep (se 2 (by rfl) ⟨534699, by rfl⟩ : syracuseStep 1425865 = 1069399) B1069399
theorem B20595185 : Blo 888571 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B4276747 : Blo 888571 4276747 := bstep (se 1 (by rfl) ⟨3207560, by rfl⟩ : syracuseStep 4276747 = 6415121) B6415121
theorem B15221519 : Blo 888571 15221519 := bstep (se 1 (by rfl) ⟨11416139, by rfl⟩ : syracuseStep 15221519 = 22832279) B22832279
theorem B18301733 : Blo 888571 18301733 := bstep (se 4 (by rfl) ⟨1715787, by rfl⟩ : syracuseStep 18301733 = 3431575) B3431575
theorem B1000327 : Blo 888571 1000327 := bstep (se 1 (by rfl) ⟨750245, by rfl⟩ : syracuseStep 1000327 = 1500491) B1500491
theorem B1688455 : Blo 888571 1688455 := bstep (se 1 (by rfl) ⟨1266341, by rfl⟩ : syracuseStep 1688455 = 2532683) B2532683
theorem B4506515 : Blo 888571 4506515 := bstep (se 1 (by rfl) ⟨3379886, by rfl⟩ : syracuseStep 4506515 = 6759773) B6759773
theorem B2704385 : Blo 888571 2704385 := bstep (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) B2028289
theorem B2540555 : Blo 888571 2540555 := bstep (se 1 (by rfl) ⟨1905416, by rfl⟩ : syracuseStep 2540555 = 3810833) B3810833
theorem B1000507 : Blo 888571 1000507 := bstep (se 1 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 1000507 = 1500761) B1500761
theorem B2999699 : Blo 888571 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B1000975 : Blo 888571 1000975 := bstep (se 1 (by rfl) ⟨750731, by rfl⟩ : syracuseStep 1000975 = 1501463) B1501463
theorem B1427063 : Blo 888571 1427063 := bstep (se 1 (by rfl) ⟨1070297, by rfl⟩ : syracuseStep 1427063 = 2140595) B2140595
theorem B2541203 : Blo 888571 2541203 := bstep (se 1 (by rfl) ⟨1905902, by rfl⟩ : syracuseStep 2541203 = 3811805) B3811805
theorem B5490413 : Blo 888571 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B4572929 : Blo 888571 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B2541431 : Blo 888571 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B1001479 : Blo 888571 1001479 := bstep (se 1 (by rfl) ⟨751109, by rfl⟩ : syracuseStep 1001479 = 1502219) B1502219
theorem B1624079 : Blo 888571 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B5064727 : Blo 888571 5064727 := bstep (se 1 (by rfl) ⟨3798545, by rfl⟩ : syracuseStep 5064727 = 7597091) B7597091
theorem B1001659 : Blo 888571 1001659 := bstep (se 1 (by rfl) ⟨751244, by rfl⟩ : syracuseStep 1001659 = 1502489) B1502489
theorem B1690247 : Blo 888571 1690247 := bstep (se 1 (by rfl) ⟨1267685, by rfl⟩ : syracuseStep 1690247 = 2535371) B2535371
theorem B1002127 : Blo 888571 1002127 := bstep (se 1 (by rfl) ⟨751595, by rfl⟩ : syracuseStep 1002127 = 1503191) B1503191
theorem B903943 : Blo 888571 903943 := bstep (se 1 (by rfl) ⟨677957, by rfl⟩ : syracuseStep 903943 = 1355915) B1355915
theorem B3001103 : Blo 888571 3001103 := bstep (se 1 (by rfl) ⟨2250827, by rfl⟩ : syracuseStep 3001103 = 4501655) B4501655
theorem B2411293 : Blo 888571 2411293 := bstep (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) B904235
theorem B3001373 : Blo 888571 3001373 := bstep (se 3 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 3001373 = 1125515) B1125515
theorem B1002631 : Blo 888571 1002631 := bstep (se 1 (by rfl) ⟨751973, by rfl⟩ : syracuseStep 1002631 = 1503947) B1503947
theorem B1002811 : Blo 888571 1002811 := bstep (se 1 (by rfl) ⟨752108, by rfl⟩ : syracuseStep 1002811 = 1504217) B1504217
theorem B6769979 : Blo 888571 6769979 := bstep (se 1 (by rfl) ⟨5077484, by rfl⟩ : syracuseStep 6769979 = 10154969) B10154969
theorem B2346355 : Blo 888571 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B2411977 : Blo 888571 2411977 := bstep (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) B1808983
theorem B1265225 : Blo 888571 1265225 := bstep (se 2 (by rfl) ⟨474459, by rfl⟩ : syracuseStep 1265225 = 948919) B948919
theorem B1265339 : Blo 888571 1265339 := bstep (se 1 (by rfl) ⟨949004, by rfl⟩ : syracuseStep 1265339 = 1898009) B1898009
theorem B1003279 : Blo 888571 1003279 := bstep (se 1 (by rfl) ⟨752459, by rfl⟩ : syracuseStep 1003279 = 1504919) B1504919
theorem B4509593 : Blo 888571 4509593 := bstep (se 2 (by rfl) ⟨1691097, by rfl⟩ : syracuseStep 4509593 = 3382195) B3382195
theorem B4280363 : Blo 888571 4280363 := bstep (se 1 (by rfl) ⟨3210272, by rfl⟩ : syracuseStep 4280363 = 6420545) B6420545
theorem B1069303 : Blo 888571 1069303 := bstep (se 1 (by rfl) ⟨801977, by rfl⟩ : syracuseStep 1069303 = 1603955) B1603955
theorem B1003783 : Blo 888571 1003783 := bstep (se 1 (by rfl) ⟨752837, by rfl⟩ : syracuseStep 1003783 = 1505675) B1505675
theorem B7721249 : Blo 888571 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B1265977 : Blo 888571 1265977 := bstep (se 2 (by rfl) ⟨474741, by rfl⟩ : syracuseStep 1265977 = 949483) B949483
theorem B5067143 : Blo 888571 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B3002777 : Blo 888571 3002777 := bstep (se 2 (by rfl) ⟨1126041, by rfl⟩ : syracuseStep 3002777 = 2252083) B2252083
theorem B1003963 : Blo 888571 1003963 := bstep (se 1 (by rfl) ⟨752972, by rfl⟩ : syracuseStep 1003963 = 1505945) B1505945
theorem B1069687 : Blo 888571 1069687 := bstep (se 1 (by rfl) ⟨802265, by rfl⟩ : syracuseStep 1069687 = 1604531) B1604531
theorem B34689829 : Blo 888571 34689829 := bstep (se 4 (by rfl) ⟨3252171, by rfl⟩ : syracuseStep 34689829 = 6504343) B6504343
theorem B11719685 : Blo 888571 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B1692731 : Blo 888571 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B2249815 : Blo 888571 2249815 := bstep (se 1 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 2249815 = 3374723) B3374723
theorem B3003479 : Blo 888571 3003479 := bstep (se 1 (by rfl) ⟨2252609, by rfl⟩ : syracuseStep 3003479 = 4505219) B4505219
theorem B2250119 : Blo 888571 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B2250251 : Blo 888571 2250251 := bstep (se 1 (by rfl) ⟨1687688, by rfl⟩ : syracuseStep 2250251 = 3375377) B3375377
theorem B1693217 : Blo 888571 1693217 := bstep (se 2 (by rfl) ⟨634956, by rfl⟩ : syracuseStep 1693217 = 1269913) B1269913
theorem B3003965 : Blo 888571 3003965 := bstep (se 3 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 3003965 = 1126487) B1126487
theorem B1332923 : Blo 888571 1332923 := bstep (se 1 (by rfl) ⟨999692, by rfl⟩ : syracuseStep 1332923 = 1999385) B1999385
theorem B1332983 : Blo 888571 1332983 := bstep (se 1 (by rfl) ⟨999737, by rfl⟩ : syracuseStep 1332983 = 1999475) B1999475
theorem B1333007 : Blo 888571 1333007 := bstep (se 1 (by rfl) ⟨999755, by rfl⟩ : syracuseStep 1333007 = 1999511) B1999511
theorem B1333049 : Blo 888571 1333049 := bstep (se 2 (by rfl) ⟨499893, by rfl⟩ : syracuseStep 1333049 = 999787) B999787
theorem B1333127 : Blo 888571 1333127 := bstep (se 1 (by rfl) ⟨999845, by rfl⟩ : syracuseStep 1333127 = 1999691) B1999691
theorem B7329689 : Blo 888571 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B1333163 : Blo 888571 1333163 := bstep (se 1 (by rfl) ⟨999872, by rfl⟩ : syracuseStep 1333163 = 1999745) B1999745
theorem B3856313 : Blo 888571 3856313 := bstep (se 2 (by rfl) ⟨1446117, by rfl⟩ : syracuseStep 3856313 = 2892235) B2892235
theorem B1333193 : Blo 888571 1333193 := bstep (se 2 (by rfl) ⟨499947, by rfl⟩ : syracuseStep 1333193 = 999895) B999895
theorem B2250767 : Blo 888571 2250767 := bstep (se 1 (by rfl) ⟨1688075, by rfl⟩ : syracuseStep 2250767 = 3376151) B3376151
theorem B1333307 : Blo 888571 1333307 := bstep (se 1 (by rfl) ⟨999980, by rfl⟩ : syracuseStep 1333307 = 1999961) B1999961
theorem B1333367 : Blo 888571 1333367 := bstep (se 1 (by rfl) ⟨1000025, by rfl⟩ : syracuseStep 1333367 = 2000051) B2000051
theorem B5068919 : Blo 888571 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B1333391 : Blo 888571 1333391 := bstep (se 1 (by rfl) ⟨1000043, by rfl⟩ : syracuseStep 1333391 = 2000087) B2000087
theorem B2250899 : Blo 888571 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B1333433 : Blo 888571 1333433 := bstep (se 2 (by rfl) ⟨500037, by rfl⟩ : syracuseStep 1333433 = 1000075) B1000075
theorem B1333511 : Blo 888571 1333511 := bstep (se 1 (by rfl) ⟨1000133, by rfl⟩ : syracuseStep 1333511 = 2000267) B2000267
theorem B1333547 : Blo 888571 1333547 := bstep (se 1 (by rfl) ⟨1000160, by rfl⟩ : syracuseStep 1333547 = 2000321) B2000321
theorem B1333577 : Blo 888571 1333577 := bstep (se 2 (by rfl) ⟨500091, by rfl⟩ : syracuseStep 1333577 = 1000183) B1000183
theorem B6936977 : Blo 888571 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B4512185 : Blo 888571 4512185 := bstep (se 2 (by rfl) ⟨1692069, by rfl⟩ : syracuseStep 4512185 = 3384139) B3384139
theorem B1333691 : Blo 888571 1333691 := bstep (se 1 (by rfl) ⟨1000268, by rfl⟩ : syracuseStep 1333691 = 2000537) B2000537
theorem B1333751 : Blo 888571 1333751 := bstep (se 1 (by rfl) ⟨1000313, by rfl⟩ : syracuseStep 1333751 = 2000627) B2000627
theorem B1333775 : Blo 888571 1333775 := bstep (se 1 (by rfl) ⟨1000331, by rfl⟩ : syracuseStep 1333775 = 2000663) B2000663
theorem B1333817 : Blo 888571 1333817 := bstep (se 2 (by rfl) ⟨500181, by rfl⟩ : syracuseStep 1333817 = 1000363) B1000363
theorem B6412877 : Blo 888571 6412877 := bstep (se 3 (by rfl) ⟨1202414, by rfl⟩ : syracuseStep 6412877 = 2404829) B2404829
theorem B2710103 : Blo 888571 2710103 := bstep (se 1 (by rfl) ⟨2032577, by rfl⟩ : syracuseStep 2710103 = 4065155) B4065155
theorem B1333895 : Blo 888571 1333895 := bstep (se 1 (by rfl) ⟨1000421, by rfl⟩ : syracuseStep 1333895 = 2000843) B2000843
theorem B1333931 : Blo 888571 1333931 := bstep (se 1 (by rfl) ⟨1000448, by rfl⟩ : syracuseStep 1333931 = 2000897) B2000897
theorem B1333961 : Blo 888571 1333961 := bstep (se 2 (by rfl) ⟨500235, by rfl⟩ : syracuseStep 1333961 = 1000471) B1000471
theorem B1334075 : Blo 888571 1334075 := bstep (se 1 (by rfl) ⟨1000556, by rfl⟩ : syracuseStep 1334075 = 2001113) B2001113
theorem B5069627 : Blo 888571 5069627 := bstep (se 1 (by rfl) ⟨3802220, by rfl⟩ : syracuseStep 5069627 = 7604441) B7604441
theorem B1334135 : Blo 888571 1334135 := bstep (se 1 (by rfl) ⟨1000601, by rfl⟩ : syracuseStep 1334135 = 2001203) B2001203
theorem B1334159 : Blo 888571 1334159 := bstep (se 1 (by rfl) ⟨1000619, by rfl⟩ : syracuseStep 1334159 = 2001239) B2001239
theorem B1334201 : Blo 888571 1334201 := bstep (se 2 (by rfl) ⟨500325, by rfl⟩ : syracuseStep 1334201 = 1000651) B1000651
theorem B3005369 : Blo 888571 3005369 := bstep (se 2 (by rfl) ⟨1127013, by rfl⟩ : syracuseStep 3005369 = 2254027) B2254027
theorem B1334279 : Blo 888571 1334279 := bstep (se 1 (by rfl) ⟨1000709, by rfl⟩ : syracuseStep 1334279 = 2001419) B2001419
theorem B1334315 : Blo 888571 1334315 := bstep (se 1 (by rfl) ⟨1000736, by rfl⟩ : syracuseStep 1334315 = 2001473) B2001473
theorem B1268779 : Blo 888571 1268779 := bstep (se 1 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 1268779 = 1903169) B1903169
theorem B1334345 : Blo 888571 1334345 := bstep (se 2 (by rfl) ⟨500379, by rfl⟩ : syracuseStep 1334345 = 1000759) B1000759
theorem B1334459 : Blo 888571 1334459 := bstep (se 1 (by rfl) ⟨1000844, by rfl⟩ : syracuseStep 1334459 = 2001689) B2001689
theorem B1334519 : Blo 888571 1334519 := bstep (se 1 (by rfl) ⟨1000889, by rfl⟩ : syracuseStep 1334519 = 2001779) B2001779
theorem B2252033 : Blo 888571 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B1334543 : Blo 888571 1334543 := bstep (se 1 (by rfl) ⟨1000907, by rfl⟩ : syracuseStep 1334543 = 2001815) B2001815
theorem B10149137 : Blo 888571 10149137 := bstep (se 2 (by rfl) ⟨3805926, by rfl⟩ : syracuseStep 10149137 = 7611853) B7611853
theorem B1334585 : Blo 888571 1334585 := bstep (se 2 (by rfl) ⟨500469, by rfl⟩ : syracuseStep 1334585 = 1000939) B1000939
theorem B1334663 : Blo 888571 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B1334699 : Blo 888571 1334699 := bstep (se 1 (by rfl) ⟨1001024, by rfl⟩ : syracuseStep 1334699 = 2002049) B2002049
theorem B1334729 : Blo 888571 1334729 := bstep (se 2 (by rfl) ⟨500523, by rfl⟩ : syracuseStep 1334729 = 1001047) B1001047
theorem B3005963 : Blo 888571 3005963 := bstep (se 1 (by rfl) ⟨2254472, by rfl⟩ : syracuseStep 3005963 = 4508945) B4508945
theorem B1334843 : Blo 888571 1334843 := bstep (se 1 (by rfl) ⟨1001132, by rfl⟩ : syracuseStep 1334843 = 2002265) B2002265
theorem B2252407 : Blo 888571 2252407 := bstep (se 1 (by rfl) ⟨1689305, by rfl⟩ : syracuseStep 2252407 = 3378611) B3378611
theorem B1334903 : Blo 888571 1334903 := bstep (se 1 (by rfl) ⟨1001177, by rfl⟩ : syracuseStep 1334903 = 2002355) B2002355
theorem B3006071 : Blo 888571 3006071 := bstep (se 1 (by rfl) ⟨2254553, by rfl⟩ : syracuseStep 3006071 = 4509107) B4509107
theorem B1334927 : Blo 888571 1334927 := bstep (se 1 (by rfl) ⟨1001195, by rfl⟩ : syracuseStep 1334927 = 2002391) B2002391
theorem B1334969 : Blo 888571 1334969 := bstep (se 2 (by rfl) ⟨500613, by rfl⟩ : syracuseStep 1334969 = 1001227) B1001227
theorem B4513481 : Blo 888571 4513481 := bstep (se 2 (by rfl) ⟨1692555, by rfl⟩ : syracuseStep 4513481 = 3385111) B3385111
theorem B1335047 : Blo 888571 1335047 := bstep (se 1 (by rfl) ⟨1001285, by rfl⟩ : syracuseStep 1335047 = 2002571) B2002571
theorem B1335083 : Blo 888571 1335083 := bstep (se 1 (by rfl) ⟨1001312, by rfl⟩ : syracuseStep 1335083 = 2002625) B2002625
theorem B1335113 : Blo 888571 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B1335227 : Blo 888571 1335227 := bstep (se 1 (by rfl) ⟨1001420, by rfl⟩ : syracuseStep 1335227 = 2002841) B2002841
theorem B1335287 : Blo 888571 1335287 := bstep (se 1 (by rfl) ⟨1001465, by rfl⟩ : syracuseStep 1335287 = 2002931) B2002931
theorem B1335311 : Blo 888571 1335311 := bstep (se 1 (by rfl) ⟨1001483, by rfl⟩ : syracuseStep 1335311 = 2002967) B2002967
theorem B4808747 : Blo 888571 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B2252843 : Blo 888571 2252843 := bstep (se 1 (by rfl) ⟨1689632, by rfl⟩ : syracuseStep 2252843 = 3379265) B3379265
theorem B1335353 : Blo 888571 1335353 := bstep (se 2 (by rfl) ⟨500757, by rfl⟩ : syracuseStep 1335353 = 1001515) B1001515
theorem B1335431 : Blo 888571 1335431 := bstep (se 1 (by rfl) ⟨1001573, by rfl⟩ : syracuseStep 1335431 = 2003147) B2003147
theorem B1335467 : Blo 888571 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B1335497 : Blo 888571 1335497 := bstep (se 2 (by rfl) ⟨500811, by rfl⟩ : syracuseStep 1335497 = 1001623) B1001623
theorem B3006665 : Blo 888571 3006665 := bstep (se 2 (by rfl) ⟨1127499, by rfl⟩ : syracuseStep 3006665 = 2254999) B2254999
theorem B5071085 : Blo 888571 5071085 := bstep (se 3 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 5071085 = 1901657) B1901657
theorem B1335611 : Blo 888571 1335611 := bstep (se 1 (by rfl) ⟨1001708, by rfl⟩ : syracuseStep 1335611 = 2003417) B2003417
theorem B1335671 : Blo 888571 1335671 := bstep (se 1 (by rfl) ⟨1001753, by rfl⟩ : syracuseStep 1335671 = 2003507) B2003507
theorem B1335695 : Blo 888571 1335695 := bstep (se 1 (by rfl) ⟨1001771, by rfl⟩ : syracuseStep 1335695 = 2003543) B2003543
theorem B5136785 : Blo 888571 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B1335737 : Blo 888571 1335737 := bstep (se 2 (by rfl) ⟨500901, by rfl⟩ : syracuseStep 1335737 = 1001803) B1001803
theorem B1499593 : Blo 888571 1499593 := bstep (se 2 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 1499593 = 1124695) B1124695
theorem B1335815 : Blo 888571 1335815 := bstep (se 1 (by rfl) ⟨1001861, by rfl⟩ : syracuseStep 1335815 = 2003723) B2003723
theorem B9626141 : Blo 888571 9626141 := bstep (se 3 (by rfl) ⟨1804901, by rfl⟩ : syracuseStep 9626141 = 3609803) B3609803
theorem B6775325 : Blo 888571 6775325 := bstep (se 3 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 6775325 = 2540747) B2540747
theorem B1335851 : Blo 888571 1335851 := bstep (se 1 (by rfl) ⟨1001888, by rfl⟩ : syracuseStep 1335851 = 2003777) B2003777
theorem B1335881 : Blo 888571 1335881 := bstep (se 2 (by rfl) ⟨500955, by rfl⟩ : syracuseStep 1335881 = 1001911) B1001911
theorem B3203671 : Blo 888571 3203671 := bstep (se 1 (by rfl) ⟨2402753, by rfl⟩ : syracuseStep 3203671 = 4805507) B4805507
theorem B1335995 : Blo 888571 1335995 := bstep (se 1 (by rfl) ⟨1001996, by rfl⟩ : syracuseStep 1335995 = 2003993) B2003993
theorem B1336055 : Blo 888571 1336055 := bstep (se 1 (by rfl) ⟨1002041, by rfl⟩ : syracuseStep 1336055 = 2004083) B2004083
theorem B1336079 : Blo 888571 1336079 := bstep (se 1 (by rfl) ⟨1002059, by rfl⟩ : syracuseStep 1336079 = 2004119) B2004119
theorem B1336121 : Blo 888571 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B2253683 : Blo 888571 2253683 := bstep (se 1 (by rfl) ⟨1690262, by rfl⟩ : syracuseStep 2253683 = 3380525) B3380525
theorem B2253703 : Blo 888571 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B1336199 : Blo 888571 1336199 := bstep (se 1 (by rfl) ⟨1002149, by rfl⟩ : syracuseStep 1336199 = 2004299) B2004299
theorem B3007367 : Blo 888571 3007367 := bstep (se 1 (by rfl) ⟨2255525, by rfl⟩ : syracuseStep 3007367 = 4511051) B4511051
theorem B1336235 : Blo 888571 1336235 := bstep (se 1 (by rfl) ⟨1002176, by rfl⟩ : syracuseStep 1336235 = 2004353) B2004353
theorem B1336265 : Blo 888571 1336265 := bstep (se 2 (by rfl) ⟨501099, by rfl⟩ : syracuseStep 1336265 = 1002199) B1002199
theorem B1336379 : Blo 888571 1336379 := bstep (se 1 (by rfl) ⟨1002284, by rfl⟩ : syracuseStep 1336379 = 2004569) B2004569
theorem B5858365 : Blo 888571 5858365 := bstep (se 3 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 5858365 = 2196887) B2196887
theorem B1336439 : Blo 888571 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B1500295 : Blo 888571 1500295 := bstep (se 1 (by rfl) ⟨1125221, by rfl⟩ : syracuseStep 1500295 = 2250443) B2250443
theorem B1336463 : Blo 888571 1336463 := bstep (se 1 (by rfl) ⟨1002347, by rfl⟩ : syracuseStep 1336463 = 2004695) B2004695
theorem B2253977 : Blo 888571 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B1336505 : Blo 888571 1336505 := bstep (se 2 (by rfl) ⟨501189, by rfl⟩ : syracuseStep 1336505 = 1002379) B1002379
theorem B3007745 : Blo 888571 3007745 := bstep (se 2 (by rfl) ⟨1127904, by rfl⟩ : syracuseStep 3007745 = 2255809) B2255809
theorem B1336583 : Blo 888571 1336583 := bstep (se 1 (by rfl) ⟨1002437, by rfl⟩ : syracuseStep 1336583 = 2004875) B2004875
theorem B1926433 : Blo 888571 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B1336619 : Blo 888571 1336619 := bstep (se 1 (by rfl) ⟨1002464, by rfl⟩ : syracuseStep 1336619 = 2004929) B2004929
theorem B2254139 : Blo 888571 2254139 := bstep (se 1 (by rfl) ⟨1690604, by rfl⟩ : syracuseStep 2254139 = 3381209) B3381209
theorem B15230267 : Blo 888571 15230267 := bstep (se 1 (by rfl) ⟨11422700, by rfl⟩ : syracuseStep 15230267 = 22845401) B22845401
theorem B1336649 : Blo 888571 1336649 := bstep (se 2 (by rfl) ⟨501243, by rfl⟩ : syracuseStep 1336649 = 1002487) B1002487
theorem B1336763 : Blo 888571 1336763 := bstep (se 1 (by rfl) ⟨1002572, by rfl⟩ : syracuseStep 1336763 = 2005145) B2005145
theorem B1336823 : Blo 888571 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B2254351 : Blo 888571 2254351 := bstep (se 1 (by rfl) ⟨1690763, by rfl⟩ : syracuseStep 2254351 = 3381527) B3381527
theorem B1336847 : Blo 888571 1336847 := bstep (se 1 (by rfl) ⟨1002635, by rfl⟩ : syracuseStep 1336847 = 2005271) B2005271
theorem B1336889 : Blo 888571 1336889 := bstep (se 2 (by rfl) ⟨501333, by rfl⟩ : syracuseStep 1336889 = 1002667) B1002667
theorem B1336967 : Blo 888571 1336967 := bstep (se 1 (by rfl) ⟨1002725, by rfl⟩ : syracuseStep 1336967 = 2005451) B2005451
theorem B1337003 : Blo 888571 1337003 := bstep (se 1 (by rfl) ⟨1002752, by rfl⟩ : syracuseStep 1337003 = 2005505) B2005505
theorem B1337033 : Blo 888571 1337033 := bstep (se 2 (by rfl) ⟨501387, by rfl⟩ : syracuseStep 1337033 = 1002775) B1002775
theorem B1500943 : Blo 888571 1500943 := bstep (se 1 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 1500943 = 2251415) B2251415
theorem B2254625 : Blo 888571 2254625 := bstep (se 2 (by rfl) ⟨845484, by rfl⟩ : syracuseStep 2254625 = 1690969) B1690969
theorem B1337147 : Blo 888571 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B1337207 : Blo 888571 1337207 := bstep (se 1 (by rfl) ⟨1002905, by rfl⟩ : syracuseStep 1337207 = 2005811) B2005811
theorem B1337231 : Blo 888571 1337231 := bstep (se 1 (by rfl) ⟨1002923, by rfl⟩ : syracuseStep 1337231 = 2005847) B2005847
theorem B1337273 : Blo 888571 1337273 := bstep (se 2 (by rfl) ⟨501477, by rfl⟩ : syracuseStep 1337273 = 1002955) B1002955
theorem B4122577 : Blo 888571 4122577 := bstep (se 2 (by rfl) ⟨1545966, by rfl⟩ : syracuseStep 4122577 = 3091933) B3091933
theorem B1337351 : Blo 888571 1337351 := bstep (se 1 (by rfl) ⟨1003013, by rfl⟩ : syracuseStep 1337351 = 2006027) B2006027
theorem B3008555 : Blo 888571 3008555 := bstep (se 1 (by rfl) ⟨2256416, by rfl⟩ : syracuseStep 3008555 = 4512833) B4512833
theorem B1337387 : Blo 888571 1337387 := bstep (se 1 (by rfl) ⟨1003040, by rfl⟩ : syracuseStep 1337387 = 2006081) B2006081
theorem B1337417 : Blo 888571 1337417 := bstep (se 2 (by rfl) ⟨501531, by rfl⟩ : syracuseStep 1337417 = 1003063) B1003063
theorem B10152053 : Blo 888571 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B1337531 : Blo 888571 1337531 := bstep (se 1 (by rfl) ⟨1003148, by rfl⟩ : syracuseStep 1337531 = 2006297) B2006297
theorem B3467501 : Blo 888571 3467501 := bstep (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) B1300313
theorem B1337591 : Blo 888571 1337591 := bstep (se 1 (by rfl) ⟨1003193, by rfl⟩ : syracuseStep 1337591 = 2006387) B2006387
theorem B1337615 : Blo 888571 1337615 := bstep (se 1 (by rfl) ⟨1003211, by rfl⟩ : syracuseStep 1337615 = 2006423) B2006423
theorem B1501483 : Blo 888571 1501483 := bstep (se 1 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 1501483 = 2252225) B2252225
theorem B1337657 : Blo 888571 1337657 := bstep (se 2 (by rfl) ⟨501621, by rfl⟩ : syracuseStep 1337657 = 1003243) B1003243
theorem B1337735 : Blo 888571 1337735 := bstep (se 1 (by rfl) ⟨1003301, by rfl⟩ : syracuseStep 1337735 = 2006603) B2006603
theorem B1337771 : Blo 888571 1337771 := bstep (se 1 (by rfl) ⟨1003328, by rfl⟩ : syracuseStep 1337771 = 2006657) B2006657
theorem B1501625 : Blo 888571 1501625 := bstep (se 2 (by rfl) ⟨563109, by rfl⟩ : syracuseStep 1501625 = 1126219) B1126219
theorem B1337801 : Blo 888571 1337801 := bstep (se 2 (by rfl) ⟨501675, by rfl⟩ : syracuseStep 1337801 = 1003351) B1003351
theorem B12839467 : Blo 888571 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B1337915 : Blo 888571 1337915 := bstep (se 1 (by rfl) ⟨1003436, by rfl⟩ : syracuseStep 1337915 = 2006873) B2006873
theorem B5073475 : Blo 888571 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B1337975 : Blo 888571 1337975 := bstep (se 1 (by rfl) ⟨1003481, by rfl⟩ : syracuseStep 1337975 = 2006963) B2006963
theorem B1337999 : Blo 888571 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B1338041 : Blo 888571 1338041 := bstep (se 2 (by rfl) ⟨501765, by rfl⟩ : syracuseStep 1338041 = 1003531) B1003531
theorem B1338119 : Blo 888571 1338119 := bstep (se 1 (by rfl) ⟨1003589, by rfl⟩ : syracuseStep 1338119 = 2007179) B2007179
theorem B2255627 : Blo 888571 2255627 := bstep (se 1 (by rfl) ⟨1691720, by rfl⟩ : syracuseStep 2255627 = 3383441) B3383441
theorem B1338155 : Blo 888571 1338155 := bstep (se 1 (by rfl) ⟨1003616, by rfl⟩ : syracuseStep 1338155 = 2007233) B2007233
theorem B1338185 : Blo 888571 1338185 := bstep (se 2 (by rfl) ⟨501819, by rfl⟩ : syracuseStep 1338185 = 1003639) B1003639
theorem B1305463 : Blo 888571 1305463 := bstep (se 1 (by rfl) ⟨979097, by rfl⟩ : syracuseStep 1305463 = 1958195) B1958195
theorem B1338299 : Blo 888571 1338299 := bstep (se 1 (by rfl) ⟨1003724, by rfl⟩ : syracuseStep 1338299 = 2007449) B2007449
theorem B1338359 : Blo 888571 1338359 := bstep (se 1 (by rfl) ⟨1003769, by rfl⟩ : syracuseStep 1338359 = 2007539) B2007539
theorem B1338383 : Blo 888571 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B1338425 : Blo 888571 1338425 := bstep (se 2 (by rfl) ⟨501909, by rfl⟩ : syracuseStep 1338425 = 1003819) B1003819
theorem B1502327 : Blo 888571 1502327 := bstep (se 1 (by rfl) ⟨1126745, by rfl⟩ : syracuseStep 1502327 = 2253491) B2253491
theorem B1338503 : Blo 888571 1338503 := bstep (se 1 (by rfl) ⟨1003877, by rfl⟩ : syracuseStep 1338503 = 2007755) B2007755
theorem B1338539 : Blo 888571 1338539 := bstep (se 1 (by rfl) ⟨1003904, by rfl⟩ : syracuseStep 1338539 = 2007809) B2007809
theorem B1338569 : Blo 888571 1338569 := bstep (se 2 (by rfl) ⟨501963, by rfl⟩ : syracuseStep 1338569 = 1003927) B1003927
theorem B3009851 : Blo 888571 3009851 := bstep (se 1 (by rfl) ⟨2257388, by rfl⟩ : syracuseStep 3009851 = 4514777) B4514777
theorem B1338683 : Blo 888571 1338683 := bstep (se 1 (by rfl) ⟨1004012, by rfl⟩ : syracuseStep 1338683 = 2008025) B2008025
theorem B1338743 : Blo 888571 1338743 := bstep (se 1 (by rfl) ⟨1004057, by rfl⟩ : syracuseStep 1338743 = 2008115) B2008115
theorem B1338767 : Blo 888571 1338767 := bstep (se 1 (by rfl) ⟨1004075, by rfl⟩ : syracuseStep 1338767 = 2008151) B2008151
theorem B2256275 : Blo 888571 2256275 := bstep (se 1 (by rfl) ⟨1692206, by rfl⟩ : syracuseStep 2256275 = 3384413) B3384413
theorem B1338809 : Blo 888571 1338809 := bstep (se 2 (by rfl) ⟨502053, by rfl⟩ : syracuseStep 1338809 = 1004107) B1004107
theorem B2289167 : Blo 888571 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B5697053 : Blo 888571 5697053 := bstep (se 3 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 5697053 = 2136395) B2136395
theorem B15429149 : Blo 888571 15429149 := bstep (se 3 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 15429149 = 5785931) B5785931
theorem B1502779 : Blo 888571 1502779 := bstep (se 1 (by rfl) ⟨1127084, by rfl⟩ : syracuseStep 1502779 = 2254169) B2254169
theorem B2256569 : Blo 888571 2256569 := bstep (se 2 (by rfl) ⟨846213, by rfl⟩ : syracuseStep 2256569 = 1692427) B1692427
theorem B1502921 : Blo 888571 1502921 := bstep (se 2 (by rfl) ⟨563595, by rfl⟩ : syracuseStep 1502921 = 1127191) B1127191
theorem B3796769 : Blo 888571 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B3010337 : Blo 888571 3010337 := bstep (se 2 (by rfl) ⟨1128876, by rfl⟩ : syracuseStep 3010337 = 2257753) B2257753
theorem B3797111 : Blo 888571 3797111 := bstep (se 1 (by rfl) ⟨2847833, by rfl⟩ : syracuseStep 3797111 = 5695667) B5695667
theorem B11137297 : Blo 888571 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B2257267 : Blo 888571 2257267 := bstep (se 1 (by rfl) ⟨1692950, by rfl⟩ : syracuseStep 2257267 = 3385901) B3385901
theorem B3010931 : Blo 888571 3010931 := bstep (se 1 (by rfl) ⟨2258198, by rfl⟩ : syracuseStep 3010931 = 4516397) B4516397
theorem B1503623 : Blo 888571 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B11432339 : Blo 888571 11432339 := bstep (se 1 (by rfl) ⟨8574254, by rfl⟩ : syracuseStep 11432339 = 17148509) B17148509
theorem B2257409 : Blo 888571 2257409 := bstep (se 2 (by rfl) ⟨846528, by rfl⟩ : syracuseStep 2257409 = 1693057) B1693057
theorem B5075459 : Blo 888571 5075459 := bstep (se 1 (by rfl) ⟨3806594, by rfl⟩ : syracuseStep 5075459 = 7613189) B7613189
theorem B3207937 : Blo 888571 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B2257865 : Blo 888571 2257865 := bstep (se 2 (by rfl) ⟨846699, by rfl⟩ : syracuseStep 2257865 = 1693399) B1693399
theorem B4387805 : Blo 888571 4387805 := bstep (se 3 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 4387805 = 1645427) B1645427
theorem B1504271 : Blo 888571 1504271 := bstep (se 1 (by rfl) ⟨1128203, by rfl⟩ : syracuseStep 1504271 = 2256407) B2256407
theorem B1602679 : Blo 888571 1602679 := bstep (se 1 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 1602679 = 2404019) B2404019
theorem B2258219 : Blo 888571 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B1504811 : Blo 888571 1504811 := bstep (se 1 (by rfl) ⟨1128608, by rfl⟩ : syracuseStep 1504811 = 2257217) B2257217
theorem B1505209 : Blo 888571 1505209 := bstep (se 2 (by rfl) ⟨564453, by rfl⟩ : syracuseStep 1505209 = 1128907) B1128907
theorem B1833161 : Blo 888571 1833161 := bstep (se 2 (by rfl) ⟨687435, by rfl⟩ : syracuseStep 1833161 = 1374871) B1374871
theorem B2259211 : Blo 888571 2259211 := bstep (se 1 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 2259211 = 3388817) B3388817
theorem B2849039 : Blo 888571 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B1898795 : Blo 888571 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B3799639 : Blo 888571 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B1505911 : Blo 888571 1505911 := bstep (se 1 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 1505911 = 2258867) B2258867
theorem B1506107 : Blo 888571 1506107 := bstep (se 1 (by rfl) ⟨1129580, by rfl⟩ : syracuseStep 1506107 = 2259161) B2259161
theorem B5077849 : Blo 888571 5077849 := bstep (se 2 (by rfl) ⟨1904193, by rfl⟩ : syracuseStep 5077849 = 3808387) B3808387
theorem B6749081 : Blo 888571 6749081 := bstep (se 2 (by rfl) ⟨2530905, by rfl⟩ : syracuseStep 6749081 = 5061811) B5061811
theorem B12844493 : Blo 888571 12844493 := bstep (se 3 (by rfl) ⟨2408342, by rfl⟩ : syracuseStep 12844493 = 4816685) B4816685
theorem B1605511 : Blo 888571 1605511 := bstep (se 1 (by rfl) ⟨1204133, by rfl⟩ : syracuseStep 1605511 = 2408267) B2408267
theorem B1900435 : Blo 888571 1900435 := bstep (se 1 (by rfl) ⟨1425326, by rfl⟩ : syracuseStep 1900435 = 2850653) B2850653
theorem B5079307 : Blo 888571 5079307 := bstep (se 1 (by rfl) ⟨3809480, by rfl⟩ : syracuseStep 5079307 = 7618961) B7618961
theorem B13730123 : Blo 888571 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B14451149 : Blo 888571 14451149 := bstep (se 3 (by rfl) ⟨2709590, by rfl⟩ : syracuseStep 14451149 = 5419181) B5419181
theorem B5702177 : Blo 888571 5702177 := bstep (se 2 (by rfl) ⟨2138316, by rfl⟩ : syracuseStep 5702177 = 4276633) B4276633
theorem B1999457 : Blo 888571 1999457 := bstep (se 2 (by rfl) ⟨749796, by rfl⟩ : syracuseStep 1999457 = 1499593) B1499593
theorem B1901153 : Blo 888571 1901153 := bstep (se 2 (by rfl) ⟨712932, by rfl⟩ : syracuseStep 1901153 = 1425865) B1425865
theorem B5702329 : Blo 888571 5702329 := bstep (se 2 (by rfl) ⟨2138373, by rfl⟩ : syracuseStep 5702329 = 4276747) B4276747
theorem B1999799 : Blo 888571 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B1901495 : Blo 888571 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B3048619 : Blo 888571 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B6751511 : Blo 888571 6751511 := bstep (se 1 (by rfl) ⟨5063633, by rfl⟩ : syracuseStep 6751511 = 10127267) B10127267
theorem B1082719 : Blo 888571 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B6849917 : Blo 888571 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B2000393 : Blo 888571 2000393 := bstep (se 2 (by rfl) ⟨750147, by rfl⟩ : syracuseStep 2000393 = 1500295) B1500295
theorem B5080765 : Blo 888571 5080765 := bstep (se 3 (by rfl) ⟨952643, by rfl⟩ : syracuseStep 5080765 = 1905287) B1905287
theorem B3376849 : Blo 888571 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B2000735 : Blo 888571 2000735 := bstep (se 1 (by rfl) ⟨1500551, by rfl⟩ : syracuseStep 2000735 = 3001103) B3001103
theorem B7604063 : Blo 888571 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B3377153 : Blo 888571 3377153 := bstep (se 2 (by rfl) ⟨1266432, by rfl⟩ : syracuseStep 3377153 = 2532865) B2532865
theorem B2000915 : Blo 888571 2000915 := bstep (se 1 (by rfl) ⟨1500686, by rfl⟩ : syracuseStep 2000915 = 3001373) B3001373
theorem B7211045 : Blo 888571 7211045 := bstep (se 4 (by rfl) ⟨676035, by rfl⟩ : syracuseStep 7211045 = 1352071) B1352071
theorem B2001257 : Blo 888571 2001257 := bstep (se 2 (by rfl) ⟨750471, by rfl⟩ : syracuseStep 2001257 = 1500943) B1500943
theorem B2886013 : Blo 888571 2886013 := bstep (se 3 (by rfl) ⟨541127, by rfl⟩ : syracuseStep 2886013 = 1082255) B1082255
theorem B3377609 : Blo 888571 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B7211693 : Blo 888571 7211693 := bstep (se 3 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 7211693 = 2704385) B2704385
theorem B2853575 : Blo 888571 2853575 := bstep (se 1 (by rfl) ⟨2140181, by rfl⟩ : syracuseStep 2853575 = 4280363) B4280363
theorem B6752969 : Blo 888571 6752969 := bstep (se 2 (by rfl) ⟨2532363, by rfl⟩ : syracuseStep 6752969 = 5064727) B5064727
theorem B2853625 : Blo 888571 2853625 := bstep (se 2 (by rfl) ⟨1070109, by rfl⟩ : syracuseStep 2853625 = 2140219) B2140219
theorem B3378095 : Blo 888571 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B2001851 : Blo 888571 2001851 := bstep (se 1 (by rfl) ⟨1501388, by rfl⟩ : syracuseStep 2001851 = 3002777) B3002777
theorem B1444873 : Blo 888571 1444873 := bstep (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) B1083655
theorem B2001977 : Blo 888571 2001977 := bstep (se 2 (by rfl) ⟨750741, by rfl⟩ : syracuseStep 2001977 = 1501483) B1501483
theorem B3214583 : Blo 888571 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B2002319 : Blo 888571 2002319 := bstep (se 1 (by rfl) ⟨1501739, by rfl⟩ : syracuseStep 2002319 = 3003479) B3003479
theorem B3215057 : Blo 888571 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B2002643 : Blo 888571 2002643 := bstep (se 1 (by rfl) ⟨1501982, by rfl⟩ : syracuseStep 2002643 = 3003965) B3003965
theorem B888615 : Blo 888571 888615 := bstep (se 1 (by rfl) ⟨666461, by rfl⟩ : syracuseStep 888615 = 1332923) B1332923
theorem B3608363 : Blo 888571 3608363 := bstep (se 1 (by rfl) ⟨2706272, by rfl⟩ : syracuseStep 3608363 = 5412545) B5412545
theorem B10817347 : Blo 888571 10817347 := bstep (se 1 (by rfl) ⟨8113010, by rfl⟩ : syracuseStep 10817347 = 16226021) B16226021
theorem B1740617 : Blo 888571 1740617 := bstep (se 2 (by rfl) ⟨652731, by rfl⟩ : syracuseStep 1740617 = 1305463) B1305463
theorem B888655 : Blo 888571 888655 := bstep (se 1 (by rfl) ⟨666491, by rfl⟩ : syracuseStep 888655 = 1332983) B1332983
theorem B888671 : Blo 888571 888671 := bstep (se 1 (by rfl) ⟨666503, by rfl⟩ : syracuseStep 888671 = 1333007) B1333007
theorem B888699 : Blo 888571 888699 := bstep (se 1 (by rfl) ⟨666524, by rfl⟩ : syracuseStep 888699 = 1333049) B1333049
theorem B888751 : Blo 888571 888751 := bstep (se 1 (by rfl) ⟨666563, by rfl⟩ : syracuseStep 888751 = 1333127) B1333127
theorem B4886459 : Blo 888571 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B888775 : Blo 888571 888775 := bstep (se 1 (by rfl) ⟨666581, by rfl⟩ : syracuseStep 888775 = 1333163) B1333163
theorem B888795 : Blo 888571 888795 := bstep (se 1 (by rfl) ⟨666596, by rfl⟩ : syracuseStep 888795 = 1333193) B1333193
theorem B4821029 : Blo 888571 4821029 := bstep (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) B903943
theorem B888871 : Blo 888571 888871 := bstep (se 1 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 888871 = 1333307) B1333307
theorem B888911 : Blo 888571 888911 := bstep (se 1 (by rfl) ⟨666683, by rfl⟩ : syracuseStep 888911 = 1333367) B1333367
theorem B3379279 : Blo 888571 3379279 := bstep (se 1 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 3379279 = 5068919) B5068919
theorem B888927 : Blo 888571 888927 := bstep (se 1 (by rfl) ⟨666695, by rfl⟩ : syracuseStep 888927 = 1333391) B1333391
theorem B888955 : Blo 888571 888955 := bstep (se 1 (by rfl) ⟨666716, by rfl⟩ : syracuseStep 888955 = 1333433) B1333433
theorem B889007 : Blo 888571 889007 := bstep (se 1 (by rfl) ⟨666755, by rfl⟩ : syracuseStep 889007 = 1333511) B1333511
theorem B889031 : Blo 888571 889031 := bstep (se 1 (by rfl) ⟨666773, by rfl⟩ : syracuseStep 889031 = 1333547) B1333547
theorem B889051 : Blo 888571 889051 := bstep (se 1 (by rfl) ⟨666788, by rfl⟩ : syracuseStep 889051 = 1333577) B1333577
theorem B4624651 : Blo 888571 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B889127 : Blo 888571 889127 := bstep (se 1 (by rfl) ⟨666845, by rfl⟩ : syracuseStep 889127 = 1333691) B1333691
theorem B3805501 : Blo 888571 3805501 := bstep (se 3 (by rfl) ⟨713531, by rfl⟩ : syracuseStep 3805501 = 1427063) B1427063
theorem B889167 : Blo 888571 889167 := bstep (se 1 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 889167 = 1333751) B1333751
theorem B889183 : Blo 888571 889183 := bstep (se 1 (by rfl) ⟨666887, by rfl⟩ : syracuseStep 889183 = 1333775) B1333775
theorem B889211 : Blo 888571 889211 := bstep (se 1 (by rfl) ⟨666908, by rfl⟩ : syracuseStep 889211 = 1333817) B1333817
theorem B889263 : Blo 888571 889263 := bstep (se 1 (by rfl) ⟨666947, by rfl⟩ : syracuseStep 889263 = 1333895) B1333895
theorem B889287 : Blo 888571 889287 := bstep (se 1 (by rfl) ⟨666965, by rfl⟩ : syracuseStep 889287 = 1333931) B1333931
theorem B12849617 : Blo 888571 12849617 := bstep (se 2 (by rfl) ⟨4818606, by rfl⟩ : syracuseStep 12849617 = 9637213) B9637213
theorem B889307 : Blo 888571 889307 := bstep (se 1 (by rfl) ⟨666980, by rfl⟩ : syracuseStep 889307 = 1333961) B1333961
theorem B889383 : Blo 888571 889383 := bstep (se 1 (by rfl) ⟨667037, by rfl⟩ : syracuseStep 889383 = 1334075) B1334075
theorem B3379751 : Blo 888571 3379751 := bstep (se 1 (by rfl) ⟨2534813, by rfl⟩ : syracuseStep 3379751 = 5069627) B5069627
theorem B889423 : Blo 888571 889423 := bstep (se 1 (by rfl) ⟨667067, by rfl⟩ : syracuseStep 889423 = 1334135) B1334135
theorem B889439 : Blo 888571 889439 := bstep (se 1 (by rfl) ⟨667079, by rfl⟩ : syracuseStep 889439 = 1334159) B1334159
theorem B3215969 : Blo 888571 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B889467 : Blo 888571 889467 := bstep (se 1 (by rfl) ⟨667100, by rfl⟩ : syracuseStep 889467 = 1334201) B1334201
theorem B2003579 : Blo 888571 2003579 := bstep (se 1 (by rfl) ⟨1502684, by rfl⟩ : syracuseStep 2003579 = 3005369) B3005369
theorem B889519 : Blo 888571 889519 := bstep (se 1 (by rfl) ⟨667139, by rfl⟩ : syracuseStep 889519 = 1334279) B1334279
theorem B889543 : Blo 888571 889543 := bstep (se 1 (by rfl) ⟨667157, by rfl⟩ : syracuseStep 889543 = 1334315) B1334315
theorem B7213769 : Blo 888571 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B889563 : Blo 888571 889563 := bstep (se 1 (by rfl) ⟨667172, by rfl⟩ : syracuseStep 889563 = 1334345) B1334345
theorem B2003705 : Blo 888571 2003705 := bstep (se 2 (by rfl) ⟨751389, by rfl⟩ : syracuseStep 2003705 = 1502779) B1502779
theorem B889639 : Blo 888571 889639 := bstep (se 1 (by rfl) ⟨667229, by rfl⟩ : syracuseStep 889639 = 1334459) B1334459
theorem B7213897 : Blo 888571 7213897 := bstep (se 2 (by rfl) ⟨2705211, by rfl⟩ : syracuseStep 7213897 = 5410423) B5410423
theorem B889679 : Blo 888571 889679 := bstep (se 1 (by rfl) ⟨667259, by rfl⟩ : syracuseStep 889679 = 1334519) B1334519
theorem B889695 : Blo 888571 889695 := bstep (se 1 (by rfl) ⟨667271, by rfl⟩ : syracuseStep 889695 = 1334543) B1334543
theorem B889723 : Blo 888571 889723 := bstep (se 1 (by rfl) ⟨667292, by rfl⟩ : syracuseStep 889723 = 1334585) B1334585
theorem B889775 : Blo 888571 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B889799 : Blo 888571 889799 := bstep (se 1 (by rfl) ⟨667349, by rfl⟩ : syracuseStep 889799 = 1334699) B1334699
theorem B889819 : Blo 888571 889819 := bstep (se 1 (by rfl) ⟨667364, by rfl⟩ : syracuseStep 889819 = 1334729) B1334729
theorem B2003975 : Blo 888571 2003975 := bstep (se 1 (by rfl) ⟨1502981, by rfl⟩ : syracuseStep 2003975 = 3005963) B3005963
theorem B889895 : Blo 888571 889895 := bstep (se 1 (by rfl) ⟨667421, by rfl⟩ : syracuseStep 889895 = 1334843) B1334843
theorem B7214129 : Blo 888571 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B889935 : Blo 888571 889935 := bstep (se 1 (by rfl) ⟨667451, by rfl⟩ : syracuseStep 889935 = 1334903) B1334903
theorem B2004047 : Blo 888571 2004047 := bstep (se 1 (by rfl) ⟨1503035, by rfl⟩ : syracuseStep 2004047 = 3006071) B3006071
theorem B889951 : Blo 888571 889951 := bstep (se 1 (by rfl) ⟨667463, by rfl⟩ : syracuseStep 889951 = 1334927) B1334927
theorem B889979 : Blo 888571 889979 := bstep (se 1 (by rfl) ⟨667484, by rfl⟩ : syracuseStep 889979 = 1334969) B1334969
theorem B890031 : Blo 888571 890031 := bstep (se 1 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 890031 = 1335047) B1335047
theorem B890055 : Blo 888571 890055 := bstep (se 1 (by rfl) ⟨667541, by rfl⟩ : syracuseStep 890055 = 1335083) B1335083
theorem B890075 : Blo 888571 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B890151 : Blo 888571 890151 := bstep (se 1 (by rfl) ⟨667613, by rfl⟩ : syracuseStep 890151 = 1335227) B1335227
theorem B890191 : Blo 888571 890191 := bstep (se 1 (by rfl) ⟨667643, by rfl⟩ : syracuseStep 890191 = 1335287) B1335287
theorem B890207 : Blo 888571 890207 := bstep (se 1 (by rfl) ⟨667655, by rfl⟩ : syracuseStep 890207 = 1335311) B1335311
theorem B890235 : Blo 888571 890235 := bstep (se 1 (by rfl) ⟨667676, by rfl⟩ : syracuseStep 890235 = 1335353) B1335353
theorem B890287 : Blo 888571 890287 := bstep (se 1 (by rfl) ⟨667715, by rfl⟩ : syracuseStep 890287 = 1335431) B1335431
theorem B890311 : Blo 888571 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B7607753 : Blo 888571 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B890331 : Blo 888571 890331 := bstep (se 1 (by rfl) ⟨667748, by rfl⟩ : syracuseStep 890331 = 1335497) B1335497
theorem B2004443 : Blo 888571 2004443 := bstep (se 1 (by rfl) ⟨1503332, by rfl⟩ : syracuseStep 2004443 = 3006665) B3006665
theorem B3380723 : Blo 888571 3380723 := bstep (se 1 (by rfl) ⟨2535542, by rfl⟩ : syracuseStep 3380723 = 5071085) B5071085
theorem B10163717 : Blo 888571 10163717 := bstep (se 4 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 10163717 = 1905697) B1905697
theorem B890407 : Blo 888571 890407 := bstep (se 1 (by rfl) ⟨667805, by rfl⟩ : syracuseStep 890407 = 1335611) B1335611
theorem B890447 : Blo 888571 890447 := bstep (se 1 (by rfl) ⟨667835, by rfl⟩ : syracuseStep 890447 = 1335671) B1335671
theorem B890463 : Blo 888571 890463 := bstep (se 1 (by rfl) ⟨667847, by rfl⟩ : syracuseStep 890463 = 1335695) B1335695
theorem B890491 : Blo 888571 890491 := bstep (se 1 (by rfl) ⟨667868, by rfl⟩ : syracuseStep 890491 = 1335737) B1335737
theorem B10851985 : Blo 888571 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B3610259 : Blo 888571 3610259 := bstep (se 1 (by rfl) ⟨2707694, by rfl⟩ : syracuseStep 3610259 = 5415389) B5415389
theorem B890543 : Blo 888571 890543 := bstep (se 1 (by rfl) ⟨667907, by rfl⟩ : syracuseStep 890543 = 1335815) B1335815
theorem B14849729 : Blo 888571 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B890567 : Blo 888571 890567 := bstep (se 1 (by rfl) ⟨667925, by rfl⟩ : syracuseStep 890567 = 1335851) B1335851
theorem B890587 : Blo 888571 890587 := bstep (se 1 (by rfl) ⟨667940, by rfl⟩ : syracuseStep 890587 = 1335881) B1335881
theorem B890663 : Blo 888571 890663 := bstep (se 1 (by rfl) ⟨667997, by rfl⟩ : syracuseStep 890663 = 1335995) B1335995
theorem B890703 : Blo 888571 890703 := bstep (se 1 (by rfl) ⟨668027, by rfl⟩ : syracuseStep 890703 = 1336055) B1336055
theorem B890719 : Blo 888571 890719 := bstep (se 1 (by rfl) ⟨668039, by rfl⟩ : syracuseStep 890719 = 1336079) B1336079
theorem B3610487 : Blo 888571 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B890747 : Blo 888571 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B890799 : Blo 888571 890799 := bstep (se 1 (by rfl) ⟨668099, by rfl⟩ : syracuseStep 890799 = 1336199) B1336199
theorem B2004911 : Blo 888571 2004911 := bstep (se 1 (by rfl) ⟨1503683, by rfl⟩ : syracuseStep 2004911 = 3007367) B3007367
theorem B890823 : Blo 888571 890823 := bstep (se 1 (by rfl) ⟨668117, by rfl⟩ : syracuseStep 890823 = 1336235) B1336235
theorem B890843 : Blo 888571 890843 := bstep (se 1 (by rfl) ⟨668132, by rfl⟩ : syracuseStep 890843 = 1336265) B1336265
theorem B890919 : Blo 888571 890919 := bstep (se 1 (by rfl) ⟨668189, by rfl⟩ : syracuseStep 890919 = 1336379) B1336379
theorem B890959 : Blo 888571 890959 := bstep (se 1 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 890959 = 1336439) B1336439
theorem B890975 : Blo 888571 890975 := bstep (se 1 (by rfl) ⟨668231, by rfl⟩ : syracuseStep 890975 = 1336463) B1336463
theorem B891003 : Blo 888571 891003 := bstep (se 1 (by rfl) ⟨668252, by rfl⟩ : syracuseStep 891003 = 1336505) B1336505
theorem B2005163 : Blo 888571 2005163 := bstep (se 1 (by rfl) ⟨1503872, by rfl⟩ : syracuseStep 2005163 = 3007745) B3007745
theorem B891055 : Blo 888571 891055 := bstep (se 1 (by rfl) ⟨668291, by rfl⟩ : syracuseStep 891055 = 1336583) B1336583
theorem B891079 : Blo 888571 891079 := bstep (se 1 (by rfl) ⟨668309, by rfl⟩ : syracuseStep 891079 = 1336619) B1336619
theorem B891099 : Blo 888571 891099 := bstep (se 1 (by rfl) ⟨668324, by rfl⟩ : syracuseStep 891099 = 1336649) B1336649
theorem B28907765 : Blo 888571 28907765 := bstep (se 5 (by rfl) ⟨1355051, by rfl⟩ : syracuseStep 28907765 = 2710103) B2710103
theorem B3807499 : Blo 888571 3807499 := bstep (se 1 (by rfl) ⟨2855624, by rfl⟩ : syracuseStep 3807499 = 5711249) B5711249
theorem B891175 : Blo 888571 891175 := bstep (se 1 (by rfl) ⟨668381, by rfl⟩ : syracuseStep 891175 = 1336763) B1336763
theorem B891215 : Blo 888571 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B891231 : Blo 888571 891231 := bstep (se 1 (by rfl) ⟨668423, by rfl⟩ : syracuseStep 891231 = 1336847) B1336847
theorem B891259 : Blo 888571 891259 := bstep (se 1 (by rfl) ⟨668444, by rfl⟩ : syracuseStep 891259 = 1336889) B1336889
theorem B891311 : Blo 888571 891311 := bstep (se 1 (by rfl) ⟨668483, by rfl⟩ : syracuseStep 891311 = 1336967) B1336967
theorem B891335 : Blo 888571 891335 := bstep (se 1 (by rfl) ⟨668501, by rfl⟩ : syracuseStep 891335 = 1337003) B1337003
theorem B891355 : Blo 888571 891355 := bstep (se 1 (by rfl) ⟨668516, by rfl⟩ : syracuseStep 891355 = 1337033) B1337033
theorem B891431 : Blo 888571 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B891471 : Blo 888571 891471 := bstep (se 1 (by rfl) ⟨668603, by rfl⟩ : syracuseStep 891471 = 1337207) B1337207
theorem B891487 : Blo 888571 891487 := bstep (se 1 (by rfl) ⟨668615, by rfl⟩ : syracuseStep 891487 = 1337231) B1337231
theorem B891515 : Blo 888571 891515 := bstep (se 1 (by rfl) ⟨668636, by rfl⟩ : syracuseStep 891515 = 1337273) B1337273
theorem B891567 : Blo 888571 891567 := bstep (se 1 (by rfl) ⟨668675, by rfl⟩ : syracuseStep 891567 = 1337351) B1337351
theorem B2005703 : Blo 888571 2005703 := bstep (se 1 (by rfl) ⟨1504277, by rfl⟩ : syracuseStep 2005703 = 3008555) B3008555
theorem B891591 : Blo 888571 891591 := bstep (se 1 (by rfl) ⟨668693, by rfl⟩ : syracuseStep 891591 = 1337387) B1337387
theorem B891611 : Blo 888571 891611 := bstep (se 1 (by rfl) ⟨668708, by rfl⟩ : syracuseStep 891611 = 1337417) B1337417
theorem B891687 : Blo 888571 891687 := bstep (se 1 (by rfl) ⟨668765, by rfl⟩ : syracuseStep 891687 = 1337531) B1337531
theorem B2136905 : Blo 888571 2136905 := bstep (se 2 (by rfl) ⟨801339, by rfl⟩ : syracuseStep 2136905 = 1602679) B1602679
theorem B891727 : Blo 888571 891727 := bstep (se 1 (by rfl) ⟨668795, by rfl⟩ : syracuseStep 891727 = 1337591) B1337591
theorem B891743 : Blo 888571 891743 := bstep (se 1 (by rfl) ⟨668807, by rfl⟩ : syracuseStep 891743 = 1337615) B1337615
theorem B891771 : Blo 888571 891771 := bstep (se 1 (by rfl) ⟨668828, by rfl⟩ : syracuseStep 891771 = 1337657) B1337657
theorem B891823 : Blo 888571 891823 := bstep (se 1 (by rfl) ⟨668867, by rfl⟩ : syracuseStep 891823 = 1337735) B1337735
theorem B10165175 : Blo 888571 10165175 := bstep (se 1 (by rfl) ⟨7623881, by rfl⟩ : syracuseStep 10165175 = 15247763) B15247763
theorem B891847 : Blo 888571 891847 := bstep (se 1 (by rfl) ⟨668885, by rfl⟩ : syracuseStep 891847 = 1337771) B1337771
theorem B891867 : Blo 888571 891867 := bstep (se 1 (by rfl) ⟨668900, by rfl⟩ : syracuseStep 891867 = 1337801) B1337801
theorem B891943 : Blo 888571 891943 := bstep (se 1 (by rfl) ⟨668957, by rfl⟩ : syracuseStep 891943 = 1337915) B1337915
theorem B891983 : Blo 888571 891983 := bstep (se 1 (by rfl) ⟨668987, by rfl⟩ : syracuseStep 891983 = 1337975) B1337975
theorem B891999 : Blo 888571 891999 := bstep (se 1 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 891999 = 1337999) B1337999
theorem B892027 : Blo 888571 892027 := bstep (se 1 (by rfl) ⟨669020, by rfl⟩ : syracuseStep 892027 = 1338041) B1338041
theorem B892079 : Blo 888571 892079 := bstep (se 1 (by rfl) ⟨669059, by rfl⟩ : syracuseStep 892079 = 1338119) B1338119
theorem B892103 : Blo 888571 892103 := bstep (se 1 (by rfl) ⟨669077, by rfl⟩ : syracuseStep 892103 = 1338155) B1338155
theorem B892123 : Blo 888571 892123 := bstep (se 1 (by rfl) ⟨669092, by rfl⟩ : syracuseStep 892123 = 1338185) B1338185
theorem B892199 : Blo 888571 892199 := bstep (se 1 (by rfl) ⟨669149, by rfl⟩ : syracuseStep 892199 = 1338299) B1338299
theorem B892239 : Blo 888571 892239 := bstep (se 1 (by rfl) ⟨669179, by rfl⟩ : syracuseStep 892239 = 1338359) B1338359
theorem B892255 : Blo 888571 892255 := bstep (se 1 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 892255 = 1338383) B1338383
theorem B892283 : Blo 888571 892283 := bstep (se 1 (by rfl) ⟨669212, by rfl⟩ : syracuseStep 892283 = 1338425) B1338425
theorem B892335 : Blo 888571 892335 := bstep (se 1 (by rfl) ⟨669251, by rfl⟩ : syracuseStep 892335 = 1338503) B1338503
theorem B892359 : Blo 888571 892359 := bstep (se 1 (by rfl) ⟨669269, by rfl⟩ : syracuseStep 892359 = 1338539) B1338539
theorem B892379 : Blo 888571 892379 := bstep (se 1 (by rfl) ⟨669284, by rfl⟩ : syracuseStep 892379 = 1338569) B1338569
theorem B2006567 : Blo 888571 2006567 := bstep (se 1 (by rfl) ⟨1504925, by rfl⟩ : syracuseStep 2006567 = 3009851) B3009851
theorem B892455 : Blo 888571 892455 := bstep (se 1 (by rfl) ⟨669341, by rfl⟩ : syracuseStep 892455 = 1338683) B1338683
theorem B892495 : Blo 888571 892495 := bstep (se 1 (by rfl) ⟨669371, by rfl⟩ : syracuseStep 892495 = 1338743) B1338743
theorem B892511 : Blo 888571 892511 := bstep (se 1 (by rfl) ⟨669383, by rfl⟩ : syracuseStep 892511 = 1338767) B1338767
theorem B892539 : Blo 888571 892539 := bstep (se 1 (by rfl) ⟨669404, by rfl⟩ : syracuseStep 892539 = 1338809) B1338809
theorem B2531179 : Blo 888571 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B2006891 : Blo 888571 2006891 := bstep (se 1 (by rfl) ⟨1505168, by rfl⟩ : syracuseStep 2006891 = 3010337) B3010337
theorem B2006945 : Blo 888571 2006945 := bstep (se 2 (by rfl) ⟨752604, by rfl⟩ : syracuseStep 2006945 = 1505209) B1505209
theorem B2531407 : Blo 888571 2531407 := bstep (se 1 (by rfl) ⟨1898555, by rfl⟩ : syracuseStep 2531407 = 3797111) B3797111
theorem B2007287 : Blo 888571 2007287 := bstep (se 1 (by rfl) ⟨1505465, by rfl⟩ : syracuseStep 2007287 = 3010931) B3010931
theorem B3383639 : Blo 888571 3383639 := bstep (se 1 (by rfl) ⟨2537729, by rfl⟩ : syracuseStep 3383639 = 5075459) B5075459
theorem B2007881 : Blo 888571 2007881 := bstep (se 2 (by rfl) ⟨752955, by rfl⟩ : syracuseStep 2007881 = 1505911) B1505911
theorem B3384929 : Blo 888571 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B6760259 : Blo 888571 6760259 := bstep (se 1 (by rfl) ⟨5070194, by rfl⟩ : syracuseStep 6760259 = 10140389) B10140389
theorem B4499387 : Blo 888571 4499387 := bstep (se 1 (by rfl) ⟨3374540, by rfl⟩ : syracuseStep 4499387 = 6749081) B6749081
theorem B6432857 : Blo 888571 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B8562995 : Blo 888571 8562995 := bstep (se 1 (by rfl) ⟨6422246, by rfl⟩ : syracuseStep 8562995 = 12844493) B12844493
theorem B46803253 : Blo 888571 46803253 := bstep (se 5 (by rfl) ⟨2193902, by rfl⟩ : syracuseStep 46803253 = 4387805) B4387805
theorem B2140681 : Blo 888571 2140681 := bstep (se 2 (by rfl) ⟨802755, by rfl⟩ : syracuseStep 2140681 = 1605511) B1605511
theorem B2533913 : Blo 888571 2533913 := bstep (se 2 (by rfl) ⟨950217, by rfl⟩ : syracuseStep 2533913 = 1900435) B1900435
theorem B3811873 : Blo 888571 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B11414195 : Blo 888571 11414195 := bstep (se 1 (by rfl) ⟨8560646, by rfl⟩ : syracuseStep 11414195 = 17121293) B17121293
theorem B3386387 : Blo 888571 3386387 := bstep (se 1 (by rfl) ⟨2539790, by rfl⟩ : syracuseStep 3386387 = 5079581) B5079581
theorem B12201155 : Blo 888571 12201155 := bstep (se 1 (by rfl) ⟨9150866, by rfl⟩ : syracuseStep 12201155 = 18301733) B18301733
theorem B4500683 : Blo 888571 4500683 := bstep (se 1 (by rfl) ⟨3375512, by rfl⟩ : syracuseStep 4500683 = 6751025) B6751025
theorem B20589997 : Blo 888571 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B4271561 : Blo 888571 4271561 := bstep (se 2 (by rfl) ⟨1601835, by rfl⟩ : syracuseStep 4271561 = 3203671) B3203671
theorem B3386843 : Blo 888571 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B8564413 : Blo 888571 8564413 := bstep (se 3 (by rfl) ⟨1605827, by rfl⟩ : syracuseStep 8564413 = 3211655) B3211655
theorem B25669709 : Blo 888571 25669709 := bstep (se 3 (by rfl) ⟨4813070, by rfl⟩ : syracuseStep 25669709 = 9626141) B9626141
theorem B7811153 : Blo 888571 7811153 := bstep (se 2 (by rfl) ⟨2929182, by rfl⟩ : syracuseStep 7811153 = 5858365) B5858365
theorem B2568577 : Blo 888571 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B3388027 : Blo 888571 3388027 := bstep (se 1 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 3388027 = 5082041) B5082041
theorem B2536829 : Blo 888571 2536829 := bstep (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) B951311
theorem B2537057 : Blo 888571 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B2537399 : Blo 888571 2537399 := bstep (se 1 (by rfl) ⟨1903049, by rfl⟩ : syracuseStep 2537399 = 3806099) B3806099
theorem B8566721 : Blo 888571 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B93829067 : Blo 888571 93829067 := bstep (se 1 (by rfl) ⟨70371800, by rfl⟩ : syracuseStep 93829067 = 140743601) B140743601
theorem B1128487 : Blo 888571 1128487 := bstep (se 1 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 1128487 = 1692731) B1692731
theorem B17119289 : Blo 888571 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B6764633 : Blo 888571 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B1128811 : Blo 888571 1128811 := bstep (se 1 (by rfl) ⟨846608, by rfl⟩ : syracuseStep 1128811 = 1693217) B1693217
theorem B1424071 : Blo 888571 1424071 := bstep (se 1 (by rfl) ⟨1068053, by rfl⟩ : syracuseStep 1424071 = 2136107) B2136107
theorem B2538515 : Blo 888571 2538515 := bstep (se 1 (by rfl) ⟨1903886, by rfl⟩ : syracuseStep 2538515 = 3807773) B3807773
theorem B4275251 : Blo 888571 4275251 := bstep (se 1 (by rfl) ⟨3206438, by rfl⟩ : syracuseStep 4275251 = 6412877) B6412877
theorem B3128473 : Blo 888571 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B2538857 : Blo 888571 2538857 := bstep (se 2 (by rfl) ⟨952071, by rfl⟩ : syracuseStep 2538857 = 1904143) B1904143
theorem B1424827 : Blo 888571 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B2538971 : Blo 888571 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B6766091 : Blo 888571 6766091 := bstep (se 1 (by rfl) ⟨5074568, by rfl⟩ : syracuseStep 6766091 = 10149137) B10149137
theorem B1425019 : Blo 888571 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B2408375 : Blo 888571 2408375 := bstep (se 1 (by rfl) ⟨1806281, by rfl⟩ : syracuseStep 2408375 = 3612563) B3612563
theorem B1687483 : Blo 888571 1687483 := bstep (se 1 (by rfl) ⟨1265612, by rfl⟩ : syracuseStep 1687483 = 2531225) B2531225
theorem B3424523 : Blo 888571 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B4505867 : Blo 888571 4505867 := bstep (se 1 (by rfl) ⟨3379400, by rfl⟩ : syracuseStep 4505867 = 6758801) B6758801
theorem B1425737 : Blo 888571 1425737 := bstep (se 2 (by rfl) ⟨534651, by rfl⟩ : syracuseStep 1425737 = 1069303) B1069303
theorem B1687969 : Blo 888571 1687969 := bstep (se 2 (by rfl) ⟨632988, by rfl⟩ : syracuseStep 1687969 = 1265977) B1265977
theorem B2540155 : Blo 888571 2540155 := bstep (se 1 (by rfl) ⟨1905116, by rfl⟩ : syracuseStep 2540155 = 3810233) B3810233
theorem B2409209 : Blo 888571 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B2540281 : Blo 888571 2540281 := bstep (se 2 (by rfl) ⟨952605, by rfl⟩ : syracuseStep 2540281 = 1905211) B1905211
theorem B1426249 : Blo 888571 1426249 := bstep (se 2 (by rfl) ⟨534843, by rfl⟩ : syracuseStep 1426249 = 1069687) B1069687
theorem B2999159 : Blo 888571 2999159 := bstep (se 1 (by rfl) ⟨2249369, by rfl⟩ : syracuseStep 2999159 = 4498739) B4498739
theorem B1688539 : Blo 888571 1688539 := bstep (se 1 (by rfl) ⟨1266404, by rfl⟩ : syracuseStep 1688539 = 2532809) B2532809
theorem B4277249 : Blo 888571 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B46253105 : Blo 888571 46253105 := bstep (se 2 (by rfl) ⟨17344914, by rfl⟩ : syracuseStep 46253105 = 34689829) B34689829
theorem B2999375 : Blo 888571 2999375 := bstep (se 1 (by rfl) ⟨2249531, by rfl⟩ : syracuseStep 2999375 = 4499063) B4499063
theorem B6768035 : Blo 888571 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B2999753 : Blo 888571 2999753 := bstep (se 2 (by rfl) ⟨1124907, by rfl⟩ : syracuseStep 2999753 = 2249815) B2249815
theorem B2311667 : Blo 888571 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B1001083 : Blo 888571 1001083 := bstep (se 1 (by rfl) ⟨750812, by rfl⟩ : syracuseStep 1001083 = 1501625) B1501625
theorem B4507325 : Blo 888571 4507325 := bstep (se 3 (by rfl) ⟨845123, by rfl⟩ : syracuseStep 4507325 = 1690247) B1690247
theorem B3000023 : Blo 888571 3000023 := bstep (se 1 (by rfl) ⟨2250017, by rfl⟩ : syracuseStep 3000023 = 4500035) B4500035
theorem B2541385 : Blo 888571 2541385 := bstep (se 2 (by rfl) ⟨953019, by rfl⟩ : syracuseStep 2541385 = 1906039) B1906039
theorem B6408031 : Blo 888571 6408031 := bstep (se 1 (by rfl) ⟨4806023, by rfl⟩ : syracuseStep 6408031 = 9612047) B9612047
theorem B4507487 : Blo 888571 4507487 := bstep (se 1 (by rfl) ⟨3380615, by rfl⟩ : syracuseStep 4507487 = 6761231) B6761231
theorem B3000239 : Blo 888571 3000239 := bstep (se 1 (by rfl) ⟨2250179, by rfl⟩ : syracuseStep 3000239 = 4500359) B4500359
theorem B1001551 : Blo 888571 1001551 := bstep (se 1 (by rfl) ⟨751163, by rfl⟩ : syracuseStep 1001551 = 1502327) B1502327
theorem B17156195 : Blo 888571 17156195 := bstep (se 1 (by rfl) ⟨12867146, by rfl⟩ : syracuseStep 17156195 = 25734293) B25734293
theorem B2541739 : Blo 888571 2541739 := bstep (se 1 (by rfl) ⟨1906304, by rfl⟩ : syracuseStep 2541739 = 3812609) B3812609
theorem B1526111 : Blo 888571 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B1001947 : Blo 888571 1001947 := bstep (se 1 (by rfl) ⟨751460, by rfl⟩ : syracuseStep 1001947 = 1502921) B1502921
theorem B54774407 : Blo 888571 54774407 := bstep (se 1 (by rfl) ⟨41080805, by rfl⟩ : syracuseStep 54774407 = 82161611) B82161611
theorem B1002415 : Blo 888571 1002415 := bstep (se 1 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 1002415 = 1503623) B1503623
theorem B7621559 : Blo 888571 7621559 := bstep (se 1 (by rfl) ⟨5716169, by rfl⟩ : syracuseStep 7621559 = 11432339) B11432339
theorem B1690703 : Blo 888571 1690703 := bstep (se 1 (by rfl) ⟨1268027, by rfl⟩ : syracuseStep 1690703 = 2536055) B2536055
theorem B1002847 : Blo 888571 1002847 := bstep (se 1 (by rfl) ⟨752135, by rfl⟩ : syracuseStep 1002847 = 1504271) B1504271
theorem B27839875 : Blo 888571 27839875 := bstep (se 1 (by rfl) ⟨20879906, by rfl⟩ : syracuseStep 27839875 = 41759813) B41759813
theorem B5066185 : Blo 888571 5066185 := bstep (se 2 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 5066185 = 3799639) B3799639
theorem B1003207 : Blo 888571 1003207 := bstep (se 1 (by rfl) ⟨752405, by rfl⟩ : syracuseStep 1003207 = 1504811) B1504811
theorem B6770465 : Blo 888571 6770465 := bstep (se 2 (by rfl) ⟨2538924, by rfl⟩ : syracuseStep 6770465 = 5077849) B5077849
theorem B7622585 : Blo 888571 7622585 := bstep (se 2 (by rfl) ⟨2858469, by rfl⟩ : syracuseStep 7622585 = 5716939) B5716939
theorem B1691705 : Blo 888571 1691705 := bstep (se 2 (by rfl) ⟨634389, by rfl⟩ : syracuseStep 1691705 = 1268779) B1268779
theorem B1265863 : Blo 888571 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B3002615 : Blo 888571 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B6410507 : Blo 888571 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B4510241 : Blo 888571 4510241 := bstep (se 2 (by rfl) ⟨1691340, by rfl⟩ : syracuseStep 4510241 = 3382681) B3382681
theorem B1004071 : Blo 888571 1004071 := bstep (se 1 (by rfl) ⟨753053, by rfl⟩ : syracuseStep 1004071 = 1506107) B1506107
theorem B3002939 : Blo 888571 3002939 := bstep (se 1 (by rfl) ⟨2252204, by rfl⟩ : syracuseStep 3002939 = 4504409) B4504409
theorem B2282195 : Blo 888571 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B3003209 : Blo 888571 3003209 := bstep (se 2 (by rfl) ⟨1126203, by rfl⟩ : syracuseStep 3003209 = 2252407) B2252407
theorem B2249633 : Blo 888571 2249633 := bstep (se 2 (by rfl) ⟨843612, by rfl⟩ : syracuseStep 2249633 = 1687225) B1687225
theorem B11391947 : Blo 888571 11391947 := bstep (se 1 (by rfl) ⟨8543960, by rfl⟩ : syracuseStep 11391947 = 17087921) B17087921
theorem B2250089 : Blo 888571 2250089 := bstep (se 2 (by rfl) ⟨843783, by rfl⟩ : syracuseStep 2250089 = 1687567) B1687567
theorem B1332935 : Blo 888571 1332935 := bstep (se 1 (by rfl) ⟨999701, by rfl⟩ : syracuseStep 1332935 = 1999403) B1999403
theorem B4282055 : Blo 888571 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B10147679 : Blo 888571 10147679 := bstep (se 1 (by rfl) ⟨7610759, by rfl⟩ : syracuseStep 10147679 = 15221519) B15221519
theorem B1333097 : Blo 888571 1333097 := bstep (se 2 (by rfl) ⟨499911, by rfl⟩ : syracuseStep 1333097 = 999823) B999823
theorem B1333175 : Blo 888571 1333175 := bstep (se 1 (by rfl) ⟨999881, by rfl⟩ : syracuseStep 1333175 = 1999763) B1999763
theorem B3004343 : Blo 888571 3004343 := bstep (se 1 (by rfl) ⟨2253257, by rfl⟩ : syracuseStep 3004343 = 4506515) B4506515
theorem B11392973 : Blo 888571 11392973 := bstep (se 3 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 11392973 = 4272365) B4272365
theorem B1333211 : Blo 888571 1333211 := bstep (se 1 (by rfl) ⟨999908, by rfl⟩ : syracuseStep 1333211 = 1999817) B1999817
theorem B1693703 : Blo 888571 1693703 := bstep (se 1 (by rfl) ⟨1270277, by rfl⟩ : syracuseStep 1693703 = 2540555) B2540555
theorem B1333679 : Blo 888571 1333679 := bstep (se 1 (by rfl) ⟨1000259, by rfl⟩ : syracuseStep 1333679 = 2000519) B2000519
theorem B1694135 : Blo 888571 1694135 := bstep (se 1 (by rfl) ⟨1270601, by rfl⟩ : syracuseStep 1694135 = 2541203) B2541203
theorem B3660275 : Blo 888571 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B1333769 : Blo 888571 1333769 := bstep (se 2 (by rfl) ⟨500163, by rfl⟩ : syracuseStep 1333769 = 1000327) B1000327
theorem B2251273 : Blo 888571 2251273 := bstep (se 2 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 2251273 = 1688455) B1688455
theorem B3004937 : Blo 888571 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B1333799 : Blo 888571 1333799 := bstep (se 1 (by rfl) ⟨1000349, by rfl⟩ : syracuseStep 1333799 = 2000699) B2000699
theorem B1694287 : Blo 888571 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B1333883 : Blo 888571 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B1334009 : Blo 888571 1334009 := bstep (se 2 (by rfl) ⟨500253, by rfl⟩ : syracuseStep 1334009 = 1000507) B1000507
theorem B1334111 : Blo 888571 1334111 := bstep (se 1 (by rfl) ⟨1000583, by rfl⟩ : syracuseStep 1334111 = 2001167) B2001167
theorem B1334123 : Blo 888571 1334123 := bstep (se 1 (by rfl) ⟨1000592, by rfl⟩ : syracuseStep 1334123 = 2001185) B2001185
theorem B6511535 : Blo 888571 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B1334351 : Blo 888571 1334351 := bstep (se 1 (by rfl) ⟨1000763, by rfl⟩ : syracuseStep 1334351 = 2001527) B2001527
theorem B1334471 : Blo 888571 1334471 := bstep (se 1 (by rfl) ⟨1000853, by rfl⟩ : syracuseStep 1334471 = 2001707) B2001707
theorem B1334633 : Blo 888571 1334633 := bstep (se 2 (by rfl) ⟨500487, by rfl⟩ : syracuseStep 1334633 = 1000975) B1000975
theorem B3005801 : Blo 888571 3005801 := bstep (se 2 (by rfl) ⟨1127175, by rfl⟩ : syracuseStep 3005801 = 2254351) B2254351
theorem B19553717 : Blo 888571 19553717 := bstep (se 5 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 19553717 = 1833161) B1833161
theorem B1334711 : Blo 888571 1334711 := bstep (se 1 (by rfl) ⟨1001033, by rfl⟩ : syracuseStep 1334711 = 2002067) B2002067
theorem B1334747 : Blo 888571 1334747 := bstep (se 1 (by rfl) ⟨1001060, by rfl⟩ : syracuseStep 1334747 = 2002121) B2002121
theorem B4513319 : Blo 888571 4513319 := bstep (se 1 (by rfl) ⟨3384989, by rfl⟩ : syracuseStep 4513319 = 6769979) B6769979
theorem B3432071 : Blo 888571 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B23125733 : Blo 888571 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B1269599 : Blo 888571 1269599 := bstep (se 1 (by rfl) ⟨952199, by rfl⟩ : syracuseStep 1269599 = 1904399) B1904399
theorem B1335215 : Blo 888571 1335215 := bstep (se 1 (by rfl) ⟨1001411, by rfl⟩ : syracuseStep 1335215 = 2002823) B2002823
theorem B2252731 : Blo 888571 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B3006395 : Blo 888571 3006395 := bstep (se 1 (by rfl) ⟨2254796, by rfl⟩ : syracuseStep 3006395 = 4509593) B4509593
theorem B5496769 : Blo 888571 5496769 := bstep (se 2 (by rfl) ⟨2061288, by rfl⟩ : syracuseStep 5496769 = 4122577) B4122577
theorem B1335305 : Blo 888571 1335305 := bstep (se 2 (by rfl) ⟨500739, by rfl⟩ : syracuseStep 1335305 = 1001479) B1001479
theorem B31252493 : Blo 888571 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B1335335 : Blo 888571 1335335 := bstep (se 1 (by rfl) ⟨1001501, by rfl⟩ : syracuseStep 1335335 = 2003003) B2003003
theorem B1335419 : Blo 888571 1335419 := bstep (se 1 (by rfl) ⟨1001564, by rfl⟩ : syracuseStep 1335419 = 2003129) B2003129
theorem B1335545 : Blo 888571 1335545 := bstep (se 2 (by rfl) ⟨500829, by rfl⟩ : syracuseStep 1335545 = 1001659) B1001659
theorem B1270009 : Blo 888571 1270009 := bstep (se 2 (by rfl) ⟨476253, by rfl⟩ : syracuseStep 1270009 = 952507) B952507
theorem B1499465 : Blo 888571 1499465 := bstep (se 2 (by rfl) ⟨562299, by rfl⟩ : syracuseStep 1499465 = 1124599) B1124599
theorem B1335647 : Blo 888571 1335647 := bstep (se 1 (by rfl) ⟨1001735, by rfl⟩ : syracuseStep 1335647 = 2003471) B2003471
theorem B1335659 : Blo 888571 1335659 := bstep (se 1 (by rfl) ⟨1001744, by rfl⟩ : syracuseStep 1335659 = 2003489) B2003489
theorem B1335887 : Blo 888571 1335887 := bstep (se 1 (by rfl) ⟨1001915, by rfl⟩ : syracuseStep 1335887 = 2003831) B2003831
theorem B1270351 : Blo 888571 1270351 := bstep (se 1 (by rfl) ⟨952763, by rfl⟩ : syracuseStep 1270351 = 1905527) B1905527
theorem B1336007 : Blo 888571 1336007 := bstep (se 1 (by rfl) ⟨1002005, by rfl⟩ : syracuseStep 1336007 = 2004011) B2004011
theorem B1499897 : Blo 888571 1499897 := bstep (se 2 (by rfl) ⟨562461, by rfl⟩ : syracuseStep 1499897 = 1124923) B1124923
theorem B1336169 : Blo 888571 1336169 := bstep (se 2 (by rfl) ⟨501063, by rfl⟩ : syracuseStep 1336169 = 1002127) B1002127
theorem B1500079 : Blo 888571 1500079 := bstep (se 1 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 1500079 = 2250119) B2250119
theorem B1336247 : Blo 888571 1336247 := bstep (se 1 (by rfl) ⟨1002185, by rfl⟩ : syracuseStep 1336247 = 2004371) B2004371
theorem B1336283 : Blo 888571 1336283 := bstep (se 1 (by rfl) ⟨1002212, by rfl⟩ : syracuseStep 1336283 = 2004425) B2004425
theorem B1500167 : Blo 888571 1500167 := bstep (se 1 (by rfl) ⟨1125125, by rfl⟩ : syracuseStep 1500167 = 2250251) B2250251
theorem B1500511 : Blo 888571 1500511 := bstep (se 1 (by rfl) ⟨1125383, by rfl⟩ : syracuseStep 1500511 = 2250767) B2250767
theorem B1336751 : Blo 888571 1336751 := bstep (se 1 (by rfl) ⟨1002563, by rfl⟩ : syracuseStep 1336751 = 2005127) B2005127
theorem B1500599 : Blo 888571 1500599 := bstep (se 1 (by rfl) ⟨1125449, by rfl⟩ : syracuseStep 1500599 = 2250899) B2250899
theorem B1336841 : Blo 888571 1336841 := bstep (se 2 (by rfl) ⟨501315, by rfl⟩ : syracuseStep 1336841 = 1002631) B1002631
theorem B1336871 : Blo 888571 1336871 := bstep (se 1 (by rfl) ⟨1002653, by rfl⟩ : syracuseStep 1336871 = 2005307) B2005307
theorem B4515425 : Blo 888571 4515425 := bstep (se 2 (by rfl) ⟨1693284, by rfl⟩ : syracuseStep 4515425 = 3386569) B3386569
theorem B3008123 : Blo 888571 3008123 := bstep (se 1 (by rfl) ⟨2256092, by rfl⟩ : syracuseStep 3008123 = 4512185) B4512185
theorem B1336955 : Blo 888571 1336955 := bstep (se 1 (by rfl) ⟨1002716, by rfl⟩ : syracuseStep 1336955 = 2005433) B2005433
theorem B1337081 : Blo 888571 1337081 := bstep (se 2 (by rfl) ⟨501405, by rfl⟩ : syracuseStep 1337081 = 1002811) B1002811
theorem B3008285 : Blo 888571 3008285 := bstep (se 3 (by rfl) ⟨564053, by rfl⟩ : syracuseStep 3008285 = 1128107) B1128107
theorem B1337183 : Blo 888571 1337183 := bstep (se 1 (by rfl) ⟨1002887, by rfl⟩ : syracuseStep 1337183 = 2005775) B2005775
theorem B1337195 : Blo 888571 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B23128001 : Blo 888571 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B1501193 : Blo 888571 1501193 := bstep (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) B1125895
theorem B1337423 : Blo 888571 1337423 := bstep (se 1 (by rfl) ⟨1003067, by rfl⟩ : syracuseStep 1337423 = 2006135) B2006135
theorem B1501355 : Blo 888571 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B1337543 : Blo 888571 1337543 := bstep (se 1 (by rfl) ⟨1003157, by rfl⟩ : syracuseStep 1337543 = 2006315) B2006315
theorem B1337705 : Blo 888571 1337705 := bstep (se 2 (by rfl) ⟨501639, by rfl⟩ : syracuseStep 1337705 = 1003279) B1003279
theorem B1337783 : Blo 888571 1337783 := bstep (se 1 (by rfl) ⟨1003337, by rfl⟩ : syracuseStep 1337783 = 2006675) B2006675
theorem B2255323 : Blo 888571 2255323 := bstep (se 1 (by rfl) ⟨1691492, by rfl⟩ : syracuseStep 2255323 = 3382985) B3382985
theorem B3008987 : Blo 888571 3008987 := bstep (se 1 (by rfl) ⟨2256740, by rfl⟩ : syracuseStep 3008987 = 4513481) B4513481
theorem B1337819 : Blo 888571 1337819 := bstep (se 1 (by rfl) ⟨1003364, by rfl⟩ : syracuseStep 1337819 = 2006729) B2006729
theorem B10283501 : Blo 888571 10283501 := bstep (se 3 (by rfl) ⟨1928156, by rfl⟩ : syracuseStep 10283501 = 3856313) B3856313
theorem B3041831 : Blo 888571 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B1501753 : Blo 888571 1501753 := bstep (se 2 (by rfl) ⟨563157, by rfl⟩ : syracuseStep 1501753 = 1126315) B1126315
theorem B3205831 : Blo 888571 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B1501895 : Blo 888571 1501895 := bstep (se 1 (by rfl) ⟨1126421, by rfl⟩ : syracuseStep 1501895 = 2252843) B2252843
theorem B1502057 : Blo 888571 1502057 := bstep (se 2 (by rfl) ⟨563271, by rfl⟩ : syracuseStep 1502057 = 1126543) B1126543
theorem B1338287 : Blo 888571 1338287 := bstep (se 1 (by rfl) ⟨1003715, by rfl⟩ : syracuseStep 1338287 = 2007431) B2007431
theorem B1338377 : Blo 888571 1338377 := bstep (se 2 (by rfl) ⟨501891, by rfl⟩ : syracuseStep 1338377 = 1003783) B1003783
theorem B4516883 : Blo 888571 4516883 := bstep (se 1 (by rfl) ⟨3387662, by rfl⟩ : syracuseStep 4516883 = 6775325) B6775325
theorem B1338407 : Blo 888571 1338407 := bstep (se 1 (by rfl) ⟨1003805, by rfl⟩ : syracuseStep 1338407 = 2007611) B2007611
theorem B2255951 : Blo 888571 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B1338491 : Blo 888571 1338491 := bstep (se 1 (by rfl) ⟨1003868, by rfl⟩ : syracuseStep 1338491 = 2007737) B2007737
theorem B3009689 : Blo 888571 3009689 := bstep (se 2 (by rfl) ⟨1128633, by rfl⟩ : syracuseStep 3009689 = 2257267) B2257267
theorem B1502455 : Blo 888571 1502455 := bstep (se 1 (by rfl) ⟨1126841, by rfl⟩ : syracuseStep 1502455 = 2253683) B2253683
theorem B1338617 : Blo 888571 1338617 := bstep (se 2 (by rfl) ⟨501981, by rfl⟩ : syracuseStep 1338617 = 1003963) B1003963
theorem B1338719 : Blo 888571 1338719 := bstep (se 1 (by rfl) ⟨1004039, by rfl⟩ : syracuseStep 1338719 = 2008079) B2008079
theorem B1338731 : Blo 888571 1338731 := bstep (se 1 (by rfl) ⟨1004048, by rfl⟩ : syracuseStep 1338731 = 2008097) B2008097
theorem B25619885 : Blo 888571 25619885 := bstep (se 3 (by rfl) ⟨4803728, by rfl⟩ : syracuseStep 25619885 = 9607457) B9607457
theorem B1502651 : Blo 888571 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B1502759 : Blo 888571 1502759 := bstep (se 1 (by rfl) ⟨1127069, by rfl⟩ : syracuseStep 1502759 = 2254139) B2254139
theorem B10153511 : Blo 888571 10153511 := bstep (se 1 (by rfl) ⟨7615133, by rfl⟩ : syracuseStep 10153511 = 15230267) B15230267
theorem B2256599 : Blo 888571 2256599 := bstep (se 1 (by rfl) ⟨1692449, by rfl⟩ : syracuseStep 2256599 = 3384899) B3384899
theorem B1503049 : Blo 888571 1503049 := bstep (se 2 (by rfl) ⟨563643, by rfl⟩ : syracuseStep 1503049 = 1127287) B1127287
theorem B1503083 : Blo 888571 1503083 := bstep (se 1 (by rfl) ⟨1127312, by rfl⟩ : syracuseStep 1503083 = 2254625) B2254625
theorem B10809521 : Blo 888571 10809521 := bstep (se 2 (by rfl) ⟨4053570, by rfl⟩ : syracuseStep 10809521 = 8107141) B8107141
theorem B1503481 : Blo 888571 1503481 := bstep (se 2 (by rfl) ⟨563805, by rfl⟩ : syracuseStep 1503481 = 1127611) B1127611
theorem B3010877 : Blo 888571 3010877 := bstep (se 3 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 3010877 = 1129079) B1129079
theorem B1503751 : Blo 888571 1503751 := bstep (se 1 (by rfl) ⟨1127813, by rfl⟩ : syracuseStep 1503751 = 2255627) B2255627
theorem B1504183 : Blo 888571 1504183 := bstep (se 1 (by rfl) ⟨1128137, by rfl⟩ : syracuseStep 1504183 = 2256275) B2256275
theorem B3798035 : Blo 888571 3798035 := bstep (se 1 (by rfl) ⟨2848526, by rfl⟩ : syracuseStep 3798035 = 5697053) B5697053
theorem B10286099 : Blo 888571 10286099 := bstep (se 1 (by rfl) ⟨7714574, by rfl⟩ : syracuseStep 10286099 = 15429149) B15429149
theorem B2061391 : Blo 888571 2061391 := bstep (se 1 (by rfl) ⟨1546043, by rfl⟩ : syracuseStep 2061391 = 3092087) B3092087
theorem B1504379 : Blo 888571 1504379 := bstep (se 1 (by rfl) ⟨1128284, by rfl⟩ : syracuseStep 1504379 = 2256569) B2256569
theorem B3011741 : Blo 888571 3011741 := bstep (se 3 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 3011741 = 1129403) B1129403
theorem B1603003 : Blo 888571 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B1504777 : Blo 888571 1504777 := bstep (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) B1128583
theorem B1504939 : Blo 888571 1504939 := bstep (se 1 (by rfl) ⟨1128704, by rfl⟩ : syracuseStep 1504939 = 2257409) B2257409
theorem B3012281 : Blo 888571 3012281 := bstep (se 2 (by rfl) ⟨1129605, by rfl⟩ : syracuseStep 3012281 = 2259211) B2259211
theorem B1603319 : Blo 888571 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B1505243 : Blo 888571 1505243 := bstep (se 1 (by rfl) ⟨1128932, by rfl⟩ : syracuseStep 1505243 = 2257865) B2257865
theorem B6092857 : Blo 888571 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B1505479 : Blo 888571 1505479 := bstep (se 1 (by rfl) ⟨1129109, by rfl⟩ : syracuseStep 1505479 = 2258219) B2258219
theorem B2259191 : Blo 888571 2259191 := bstep (se 1 (by rfl) ⟨1694393, by rfl⟩ : syracuseStep 2259191 = 3388787) B3388787
theorem B1505641 : Blo 888571 1505641 := bstep (se 2 (by rfl) ⟨564615, by rfl⟩ : syracuseStep 1505641 = 1129231) B1129231
theorem B10844549 : Blo 888571 10844549 := bstep (se 4 (by rfl) ⟨1016676, by rfl⟩ : syracuseStep 10844549 = 2033353) B2033353
theorem B3373919 : Blo 888571 3373919 := bstep (se 1 (by rfl) ⟨2530439, by rfl⟩ : syracuseStep 3373919 = 5060879) B5060879
theorem B1899359 : Blo 888571 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B3373933 : Blo 888571 3373933 := bstep (se 3 (by rfl) ⟨632612, by rfl⟩ : syracuseStep 3373933 = 1265225) B1265225
theorem B55671731 : Blo 888571 55671731 := bstep (se 1 (by rfl) ⟨41753798, by rfl⟩ : syracuseStep 55671731 = 83507597) B83507597
theorem B3374237 : Blo 888571 3374237 := bstep (se 3 (by rfl) ⟨632669, by rfl⟩ : syracuseStep 3374237 = 1265339) B1265339
theorem B1604819 : Blo 888571 1604819 := bstep (se 1 (by rfl) ⟨1203614, by rfl⟩ : syracuseStep 1604819 = 2407229) B2407229
theorem B3374891 : Blo 888571 3374891 := bstep (se 1 (by rfl) ⟨2531168, by rfl⟩ : syracuseStep 3374891 = 5062337) B5062337
theorem B3375209 : Blo 888571 3375209 := bstep (se 2 (by rfl) ⟨1265703, by rfl⟩ : syracuseStep 3375209 = 2531407) B2531407
theorem B950491 : Blo 888571 950491 := bstep (se 1 (by rfl) ⟨712868, by rfl⟩ : syracuseStep 950491 = 1425737) B1425737
theorem B3801451 : Blo 888571 3801451 := bstep (se 1 (by rfl) ⟨2851088, by rfl⟩ : syracuseStep 3801451 = 5702177) B5702177
theorem B1606139 : Blo 888571 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B1999439 : Blo 888571 1999439 := bstep (se 1 (by rfl) ⟨1499579, by rfl⟩ : syracuseStep 1999439 = 2999159) B2999159
theorem B2851499 : Blo 888571 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B30835403 : Blo 888571 30835403 := bstep (se 1 (by rfl) ⟨23126552, by rfl⟩ : syracuseStep 30835403 = 46253105) B46253105
theorem B1999583 : Blo 888571 1999583 := bstep (se 1 (by rfl) ⟨1499687, by rfl⟩ : syracuseStep 1999583 = 2999375) B2999375
theorem B7603105 : Blo 888571 7603105 := bstep (se 2 (by rfl) ⟨2851164, by rfl⟩ : syracuseStep 7603105 = 5702329) B5702329
theorem B1999835 : Blo 888571 1999835 := bstep (se 1 (by rfl) ⟨1499876, by rfl⟩ : syracuseStep 1999835 = 2999753) B2999753
theorem B1541111 : Blo 888571 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B1901665 : Blo 888571 1901665 := bstep (se 2 (by rfl) ⟨713124, by rfl⟩ : syracuseStep 1901665 = 1426249) B1426249
theorem B2000015 : Blo 888571 2000015 := bstep (se 1 (by rfl) ⟨1500011, by rfl⟩ : syracuseStep 2000015 = 3000023) B3000023
theorem B38536397 : Blo 888571 38536397 := bstep (se 3 (by rfl) ⟨7225574, by rfl⟩ : syracuseStep 38536397 = 14451149) B14451149
theorem B2000105 : Blo 888571 2000105 := bstep (se 2 (by rfl) ⟨750039, by rfl⟩ : syracuseStep 2000105 = 1500079) B1500079
theorem B2000159 : Blo 888571 2000159 := bstep (se 1 (by rfl) ⟨1500119, by rfl⟩ : syracuseStep 2000159 = 3000239) B3000239
theorem B11437463 : Blo 888571 11437463 := bstep (se 1 (by rfl) ⟨8578097, by rfl⟩ : syracuseStep 11437463 = 17156195) B17156195
theorem B4064825 : Blo 888571 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B1017407 : Blo 888571 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B1443625 : Blo 888571 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B2000681 : Blo 888571 2000681 := bstep (se 2 (by rfl) ⟨750255, by rfl⟩ : syracuseStep 2000681 = 1500511) B1500511
theorem B1902383 : Blo 888571 1902383 := bstep (se 1 (by rfl) ⟨1426787, by rfl⟩ : syracuseStep 1902383 = 2853575) B2853575
theorem B5081039 : Blo 888571 5081039 := bstep (se 1 (by rfl) ⟨3810779, by rfl⟩ : syracuseStep 5081039 = 7621559) B7621559
theorem B5081723 : Blo 888571 5081723 := bstep (se 1 (by rfl) ⟨3811292, by rfl⟩ : syracuseStep 5081723 = 7622585) B7622585
theorem B3214019 : Blo 888571 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B2001743 : Blo 888571 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B2001959 : Blo 888571 2001959 := bstep (se 1 (by rfl) ⟨1501469, by rfl⟩ : syracuseStep 2001959 = 3002939) B3002939
theorem B2002139 : Blo 888571 2002139 := bstep (se 1 (by rfl) ⟨1501604, by rfl⟩ : syracuseStep 2002139 = 3003209) B3003209
theorem B2854241 : Blo 888571 2854241 := bstep (se 2 (by rfl) ⟨1070340, by rfl⟩ : syracuseStep 2854241 = 2140681) B2140681
theorem B5082497 : Blo 888571 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B2002337 : Blo 888571 2002337 := bstep (se 2 (by rfl) ⟨750876, by rfl⟩ : syracuseStep 2002337 = 1501753) B1501753
theorem B3804833 : Blo 888571 3804833 := bstep (se 2 (by rfl) ⟨1426812, by rfl⟩ : syracuseStep 3804833 = 2853625) B2853625
theorem B9899819 : Blo 888571 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B888623 : Blo 888571 888623 := bstep (se 1 (by rfl) ⟨666467, by rfl⟩ : syracuseStep 888623 = 1332935) B1332935
theorem B2854703 : Blo 888571 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B888731 : Blo 888571 888731 := bstep (se 1 (by rfl) ⟨666548, by rfl⟩ : syracuseStep 888731 = 1333097) B1333097
theorem B888783 : Blo 888571 888783 := bstep (se 1 (by rfl) ⟨666587, by rfl⟩ : syracuseStep 888783 = 1333175) B1333175
theorem B2002895 : Blo 888571 2002895 := bstep (se 1 (by rfl) ⟨1502171, by rfl⟩ : syracuseStep 2002895 = 3004343) B3004343
theorem B888807 : Blo 888571 888807 := bstep (se 1 (by rfl) ⟨666605, by rfl⟩ : syracuseStep 888807 = 1333211) B1333211
theorem B19271843 : Blo 888571 19271843 := bstep (se 1 (by rfl) ⟨14453882, by rfl⟩ : syracuseStep 19271843 = 28907765) B28907765
theorem B889119 : Blo 888571 889119 := bstep (se 1 (by rfl) ⟨666839, by rfl⟩ : syracuseStep 889119 = 1333679) B1333679
theorem B2003273 : Blo 888571 2003273 := bstep (se 2 (by rfl) ⟨751227, by rfl⟩ : syracuseStep 2003273 = 1502455) B1502455
theorem B889179 : Blo 888571 889179 := bstep (se 1 (by rfl) ⟨666884, by rfl⟩ : syracuseStep 889179 = 1333769) B1333769
theorem B2003291 : Blo 888571 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B889199 : Blo 888571 889199 := bstep (se 1 (by rfl) ⟨666899, by rfl⟩ : syracuseStep 889199 = 1333799) B1333799
theorem B889255 : Blo 888571 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B889339 : Blo 888571 889339 := bstep (se 1 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 889339 = 1334009) B1334009
theorem B889407 : Blo 888571 889407 := bstep (se 1 (by rfl) ⟨667055, by rfl⟩ : syracuseStep 889407 = 1334111) B1334111
theorem B889415 : Blo 888571 889415 := bstep (se 1 (by rfl) ⟨667061, by rfl⟩ : syracuseStep 889415 = 1334123) B1334123
theorem B6754913 : Blo 888571 6754913 := bstep (se 2 (by rfl) ⟨2533092, by rfl⟩ : syracuseStep 6754913 = 5066185) B5066185
theorem B889567 : Blo 888571 889567 := bstep (se 1 (by rfl) ⟨667175, by rfl⟩ : syracuseStep 889567 = 1334351) B1334351
theorem B889647 : Blo 888571 889647 := bstep (se 1 (by rfl) ⟨667235, by rfl⟩ : syracuseStep 889647 = 1334471) B1334471
theorem B889755 : Blo 888571 889755 := bstep (se 1 (by rfl) ⟨667316, by rfl⟩ : syracuseStep 889755 = 1334633) B1334633
theorem B2003867 : Blo 888571 2003867 := bstep (se 1 (by rfl) ⟨1502900, by rfl⟩ : syracuseStep 2003867 = 3005801) B3005801
theorem B889807 : Blo 888571 889807 := bstep (se 1 (by rfl) ⟨667355, by rfl⟩ : syracuseStep 889807 = 1334711) B1334711
theorem B889831 : Blo 888571 889831 := bstep (se 1 (by rfl) ⟨667373, by rfl⟩ : syracuseStep 889831 = 1334747) B1334747
theorem B14423129 : Blo 888571 14423129 := bstep (se 2 (by rfl) ⟨5408673, by rfl⟩ : syracuseStep 14423129 = 10817347) B10817347
theorem B2004065 : Blo 888571 2004065 := bstep (se 2 (by rfl) ⟨751524, by rfl⟩ : syracuseStep 2004065 = 1503049) B1503049
theorem B890143 : Blo 888571 890143 := bstep (se 1 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 890143 = 1335215) B1335215
theorem B2004263 : Blo 888571 2004263 := bstep (se 1 (by rfl) ⟨1503197, by rfl⟩ : syracuseStep 2004263 = 3006395) B3006395
theorem B890203 : Blo 888571 890203 := bstep (se 1 (by rfl) ⟨667652, by rfl⟩ : syracuseStep 890203 = 1335305) B1335305
theorem B890223 : Blo 888571 890223 := bstep (se 1 (by rfl) ⟨667667, by rfl⟩ : syracuseStep 890223 = 1335335) B1335335
theorem B890279 : Blo 888571 890279 := bstep (se 1 (by rfl) ⟨667709, by rfl⟩ : syracuseStep 890279 = 1335419) B1335419
theorem B890363 : Blo 888571 890363 := bstep (se 1 (by rfl) ⟨667772, by rfl⟩ : syracuseStep 890363 = 1335545) B1335545
theorem B890431 : Blo 888571 890431 := bstep (se 1 (by rfl) ⟨667823, by rfl⟩ : syracuseStep 890431 = 1335647) B1335647
theorem B890439 : Blo 888571 890439 := bstep (se 1 (by rfl) ⟨667829, by rfl⟩ : syracuseStep 890439 = 1335659) B1335659
theorem B2004641 : Blo 888571 2004641 := bstep (se 2 (by rfl) ⟨751740, by rfl⟩ : syracuseStep 2004641 = 1503481) B1503481
theorem B6166201 : Blo 888571 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B890591 : Blo 888571 890591 := bstep (se 1 (by rfl) ⟨667943, by rfl⟩ : syracuseStep 890591 = 1335887) B1335887
theorem B890671 : Blo 888571 890671 := bstep (se 1 (by rfl) ⟨668003, by rfl⟩ : syracuseStep 890671 = 1336007) B1336007
theorem B890779 : Blo 888571 890779 := bstep (se 1 (by rfl) ⟨668084, by rfl⟩ : syracuseStep 890779 = 1336169) B1336169
theorem B890831 : Blo 888571 890831 := bstep (se 1 (by rfl) ⟨668123, by rfl⟩ : syracuseStep 890831 = 1336247) B1336247
theorem B890855 : Blo 888571 890855 := bstep (se 1 (by rfl) ⟨668141, by rfl⟩ : syracuseStep 890855 = 1336283) B1336283
theorem B2005001 : Blo 888571 2005001 := bstep (se 2 (by rfl) ⟨751875, by rfl⟩ : syracuseStep 2005001 = 1503751) B1503751
theorem B16685189 : Blo 888571 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B891167 : Blo 888571 891167 := bstep (se 1 (by rfl) ⟨668375, by rfl⟩ : syracuseStep 891167 = 1336751) B1336751
theorem B891227 : Blo 888571 891227 := bstep (se 1 (by rfl) ⟨668420, by rfl⟩ : syracuseStep 891227 = 1336841) B1336841
theorem B891247 : Blo 888571 891247 := bstep (se 1 (by rfl) ⟨668435, by rfl⟩ : syracuseStep 891247 = 1336871) B1336871
theorem B2005415 : Blo 888571 2005415 := bstep (se 1 (by rfl) ⟨1504061, by rfl⟩ : syracuseStep 2005415 = 3008123) B3008123
theorem B891303 : Blo 888571 891303 := bstep (se 1 (by rfl) ⟨668477, by rfl⟩ : syracuseStep 891303 = 1336955) B1336955
theorem B891387 : Blo 888571 891387 := bstep (se 1 (by rfl) ⟨668540, by rfl⟩ : syracuseStep 891387 = 1337081) B1337081
theorem B2005523 : Blo 888571 2005523 := bstep (se 1 (by rfl) ⟨1504142, by rfl⟩ : syracuseStep 2005523 = 3008285) B3008285
theorem B891455 : Blo 888571 891455 := bstep (se 1 (by rfl) ⟨668591, by rfl⟩ : syracuseStep 891455 = 1337183) B1337183
theorem B891463 : Blo 888571 891463 := bstep (se 1 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 891463 = 1337195) B1337195
theorem B2005577 : Blo 888571 2005577 := bstep (se 2 (by rfl) ⟨752091, by rfl⟩ : syracuseStep 2005577 = 1504183) B1504183
theorem B891615 : Blo 888571 891615 := bstep (se 1 (by rfl) ⟨668711, by rfl⟩ : syracuseStep 891615 = 1337423) B1337423
theorem B891695 : Blo 888571 891695 := bstep (se 1 (by rfl) ⟨668771, by rfl⟩ : syracuseStep 891695 = 1337543) B1337543
theorem B5708663 : Blo 888571 5708663 := bstep (se 1 (by rfl) ⟨4281497, by rfl⟩ : syracuseStep 5708663 = 8562995) B8562995
theorem B891803 : Blo 888571 891803 := bstep (se 1 (by rfl) ⟨668852, by rfl⟩ : syracuseStep 891803 = 1337705) B1337705
theorem B891855 : Blo 888571 891855 := bstep (se 1 (by rfl) ⟨668891, by rfl⟩ : syracuseStep 891855 = 1337783) B1337783
theorem B2005991 : Blo 888571 2005991 := bstep (se 1 (by rfl) ⟨1504493, by rfl⟩ : syracuseStep 2005991 = 3008987) B3008987
theorem B891879 : Blo 888571 891879 := bstep (se 1 (by rfl) ⟨668909, by rfl⟩ : syracuseStep 891879 = 1337819) B1337819
theorem B6855667 : Blo 888571 6855667 := bstep (se 1 (by rfl) ⟨5141750, by rfl⟩ : syracuseStep 6855667 = 10283501) B10283501
theorem B7609463 : Blo 888571 7609463 := bstep (se 1 (by rfl) ⟨5707097, by rfl⟩ : syracuseStep 7609463 = 11414195) B11414195
theorem B2137337 : Blo 888571 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B892191 : Blo 888571 892191 := bstep (se 1 (by rfl) ⟨669143, by rfl⟩ : syracuseStep 892191 = 1338287) B1338287
theorem B892251 : Blo 888571 892251 := bstep (se 1 (by rfl) ⟨669188, by rfl⟩ : syracuseStep 892251 = 1338377) B1338377
theorem B2006369 : Blo 888571 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B892271 : Blo 888571 892271 := bstep (se 1 (by rfl) ⟨669203, by rfl⟩ : syracuseStep 892271 = 1338407) B1338407
theorem B892327 : Blo 888571 892327 := bstep (se 1 (by rfl) ⟨669245, by rfl⟩ : syracuseStep 892327 = 1338491) B1338491
theorem B2006459 : Blo 888571 2006459 := bstep (se 1 (by rfl) ⟨1504844, by rfl⟩ : syracuseStep 2006459 = 3009689) B3009689
theorem B8134103 : Blo 888571 8134103 := bstep (se 1 (by rfl) ⟨6100577, by rfl⟩ : syracuseStep 8134103 = 12201155) B12201155
theorem B892411 : Blo 888571 892411 := bstep (se 1 (by rfl) ⟨669308, by rfl⟩ : syracuseStep 892411 = 1338617) B1338617
theorem B2006585 : Blo 888571 2006585 := bstep (se 2 (by rfl) ⟨752469, by rfl⟩ : syracuseStep 2006585 = 1504939) B1504939
theorem B892479 : Blo 888571 892479 := bstep (se 1 (by rfl) ⟨669359, by rfl⟩ : syracuseStep 892479 = 1338719) B1338719
theorem B892487 : Blo 888571 892487 := bstep (se 1 (by rfl) ⟨669365, by rfl⟩ : syracuseStep 892487 = 1338731) B1338731
theorem B17079923 : Blo 888571 17079923 := bstep (se 1 (by rfl) ⟨12809942, by rfl⟩ : syracuseStep 17079923 = 25619885) B25619885
theorem B17113139 : Blo 888571 17113139 := bstep (se 1 (by rfl) ⟨12834854, by rfl⟩ : syracuseStep 17113139 = 25669709) B25669709
theorem B2007251 : Blo 888571 2007251 := bstep (se 1 (by rfl) ⟨1505438, by rfl⟩ : syracuseStep 2007251 = 3010877) B3010877
theorem B2007305 : Blo 888571 2007305 := bstep (se 2 (by rfl) ⟨752739, by rfl⟩ : syracuseStep 2007305 = 1505479) B1505479
theorem B2007521 : Blo 888571 2007521 := bstep (se 2 (by rfl) ⟨752820, by rfl⟩ : syracuseStep 2007521 = 1505641) B1505641
theorem B2532023 : Blo 888571 2532023 := bstep (se 1 (by rfl) ⟨1899017, by rfl⟩ : syracuseStep 2532023 = 3798035) B3798035
theorem B6857399 : Blo 888571 6857399 := bstep (se 1 (by rfl) ⟨5143049, by rfl⟩ : syracuseStep 6857399 = 10286099) B10286099
theorem B2007827 : Blo 888571 2007827 := bstep (se 1 (by rfl) ⟨1505870, by rfl⟩ : syracuseStep 2007827 = 3011741) B3011741
theorem B2008187 : Blo 888571 2008187 := bstep (se 1 (by rfl) ⟨1506140, by rfl⟩ : syracuseStep 2008187 = 3012281) B3012281
theorem B4498577 : Blo 888571 4498577 := bstep (se 2 (by rfl) ⟨1686966, by rfl⟩ : syracuseStep 4498577 = 3373933) B3373933
theorem B5711147 : Blo 888571 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B11412859 : Blo 888571 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B3385597 : Blo 888571 3385597 := bstep (se 3 (by rfl) ⟨634799, by rfl⟩ : syracuseStep 3385597 = 1269599) B1269599
theorem B9153415 : Blo 888571 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B3386873 : Blo 888571 3386873 := bstep (se 2 (by rfl) ⟨1270077, by rfl⟩ : syracuseStep 3386873 = 2540155) B2540155
theorem B4501007 : Blo 888571 4501007 := bstep (se 1 (by rfl) ⟨3375755, by rfl⟩ : syracuseStep 4501007 = 6751511) B6751511
theorem B4566611 : Blo 888571 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B3387041 : Blo 888571 3387041 := bstep (se 2 (by rfl) ⟨1270140, by rfl⟩ : syracuseStep 3387041 = 2540281) B2540281
theorem B36516271 : Blo 888571 36516271 := bstep (se 1 (by rfl) ⟨27387203, by rfl⟩ : syracuseStep 36516271 = 54774407) B54774407
theorem B4501979 : Blo 888571 4501979 := bstep (se 1 (by rfl) ⟨3376484, by rfl⟩ : syracuseStep 4501979 = 6752969) B6752969
theorem B1127135 : Blo 888571 1127135 := bstep (se 1 (by rfl) ⟨845351, by rfl⟩ : syracuseStep 1127135 = 1690703) B1690703
theorem B2143055 : Blo 888571 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B4502465 : Blo 888571 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B3388513 : Blo 888571 3388513 := bstep (se 2 (by rfl) ⟨1270692, by rfl⟩ : syracuseStep 3388513 = 2541385) B2541385
theorem B2405575 : Blo 888571 2405575 := bstep (se 1 (by rfl) ⟨1804181, by rfl⟩ : syracuseStep 2405575 = 3608363) B3608363
theorem B1160411 : Blo 888571 1160411 := bstep (se 1 (by rfl) ⟨870308, by rfl⟩ : syracuseStep 1160411 = 1740617) B1740617
theorem B3257639 : Blo 888571 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B3388985 : Blo 888571 3388985 := bstep (se 2 (by rfl) ⟨1270869, by rfl⟩ : syracuseStep 3388985 = 2541739) B2541739
theorem B8566411 : Blo 888571 8566411 := bstep (se 1 (by rfl) ⟨6424808, by rfl⟩ : syracuseStep 8566411 = 12849617) B12849617
theorem B2143979 : Blo 888571 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B62404337 : Blo 888571 62404337 := bstep (se 2 (by rfl) ⟨23401626, by rfl⟩ : syracuseStep 62404337 = 46803253) B46803253
theorem B4274441 : Blo 888571 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B2406839 : Blo 888571 2406839 := bstep (se 1 (by rfl) ⟨1805129, by rfl⟩ : syracuseStep 2406839 = 3610259) B3610259
theorem B6765119 : Blo 888571 6765119 := bstep (se 1 (by rfl) ⟨5073839, by rfl⟩ : syracuseStep 6765119 = 10147679) B10147679
theorem B2406991 : Blo 888571 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B1129135 : Blo 888571 1129135 := bstep (se 1 (by rfl) ⟨846851, by rfl⟩ : syracuseStep 1129135 = 1693703) B1693703
theorem B1424603 : Blo 888571 1424603 := bstep (se 1 (by rfl) ⟨1068452, by rfl⟩ : syracuseStep 1424603 = 2136905) B2136905
theorem B4341023 : Blo 888571 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B4275517 : Blo 888571 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B11419217 : Blo 888571 11419217 := bstep (se 2 (by rfl) ⟨4282206, by rfl⟩ : syracuseStep 11419217 = 8564413) B8564413
theorem B15417155 : Blo 888571 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B4505705 : Blo 888571 4505705 := bstep (se 2 (by rfl) ⟨1689639, by rfl⟩ : syracuseStep 4505705 = 3379279) B3379279
theorem B999643 : Blo 888571 999643 := bstep (se 1 (by rfl) ⟨749732, by rfl⟩ : syracuseStep 999643 = 1499465) B1499465
theorem B1687817 : Blo 888571 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B999931 : Blo 888571 999931 := bstep (se 1 (by rfl) ⟨749948, by rfl⟩ : syracuseStep 999931 = 1499897) B1499897
theorem B3424769 : Blo 888571 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B1000111 : Blo 888571 1000111 := bstep (se 1 (by rfl) ⟨750083, by rfl⟩ : syracuseStep 1000111 = 1500167) B1500167
theorem B1000399 : Blo 888571 1000399 := bstep (se 1 (by rfl) ⟨750299, by rfl⟩ : syracuseStep 1000399 = 1500599) B1500599
theorem B9618529 : Blo 888571 9618529 := bstep (se 2 (by rfl) ⟨3606948, by rfl⟩ : syracuseStep 9618529 = 7213897) B7213897
theorem B4506839 : Blo 888571 4506839 := bstep (se 1 (by rfl) ⟨3380129, by rfl⟩ : syracuseStep 4506839 = 6760259) B6760259
theorem B2999591 : Blo 888571 2999591 := bstep (se 1 (by rfl) ⟨2249693, by rfl⟩ : syracuseStep 2999591 = 4499387) B4499387
theorem B15418667 : Blo 888571 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B1000795 : Blo 888571 1000795 := bstep (se 1 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 1000795 = 1501193) B1501193
theorem B8111549 : Blo 888571 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B1000903 : Blo 888571 1000903 := bstep (se 1 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 1000903 = 1501355) B1501355
theorem B1689275 : Blo 888571 1689275 := bstep (se 1 (by rfl) ⟨1266956, by rfl⟩ : syracuseStep 1689275 = 2533913) B2533913
theorem B1001263 : Blo 888571 1001263 := bstep (se 1 (by rfl) ⟨750947, by rfl⟩ : syracuseStep 1001263 = 1501895) B1501895
theorem B1001371 : Blo 888571 1001371 := bstep (se 1 (by rfl) ⟨751028, by rfl⟩ : syracuseStep 1001371 = 1502057) B1502057
theorem B3000455 : Blo 888571 3000455 := bstep (se 1 (by rfl) ⟨2250341, by rfl⟩ : syracuseStep 3000455 = 4500683) B4500683
theorem B14469313 : Blo 888571 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B1001767 : Blo 888571 1001767 := bstep (se 1 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 1001767 = 1502651) B1502651
theorem B1001839 : Blo 888571 1001839 := bstep (se 1 (by rfl) ⟨751379, by rfl⟩ : syracuseStep 1001839 = 1502759) B1502759
theorem B6769007 : Blo 888571 6769007 := bstep (se 1 (by rfl) ⟨5076755, by rfl⟩ : syracuseStep 6769007 = 10153511) B10153511
theorem B1002055 : Blo 888571 1002055 := bstep (se 1 (by rfl) ⟨751541, by rfl⟩ : syracuseStep 1002055 = 1503083) B1503083
theorem B3001697 : Blo 888571 3001697 := bstep (se 2 (by rfl) ⟨1125636, by rfl⟩ : syracuseStep 3001697 = 2251273) B2251273
theorem B1002919 : Blo 888571 1002919 := bstep (se 1 (by rfl) ⟨752189, by rfl⟩ : syracuseStep 1002919 = 1504379) B1504379
theorem B1691219 : Blo 888571 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B1691371 : Blo 888571 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B1691599 : Blo 888571 1691599 := bstep (se 1 (by rfl) ⟨1268699, by rfl⟩ : syracuseStep 1691599 = 2537399) B2537399
theorem B1003495 : Blo 888571 1003495 := bstep (se 1 (by rfl) ⟨752621, by rfl⟩ : syracuseStep 1003495 = 1505243) B1505243
theorem B4509755 : Blo 888571 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B7229699 : Blo 888571 7229699 := bstep (se 1 (by rfl) ⟨5422274, by rfl⟩ : syracuseStep 7229699 = 10844549) B10844549
theorem B8573485 : Blo 888571 8573485 := bstep (se 3 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 8573485 = 3215057) B3215057
theorem B2249279 : Blo 888571 2249279 := bstep (se 1 (by rfl) ⟨1686959, by rfl⟩ : syracuseStep 2249279 = 3373919) B3373919
theorem B1266239 : Blo 888571 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B37114487 : Blo 888571 37114487 := bstep (se 1 (by rfl) ⟨27835865, by rfl⟩ : syracuseStep 37114487 = 55671731) B55671731
theorem B1692343 : Blo 888571 1692343 := bstep (se 1 (by rfl) ⟨1269257, by rfl⟩ : syracuseStep 1692343 = 2538515) B2538515
theorem B2249491 : Blo 888571 2249491 := bstep (se 1 (by rfl) ⟨1687118, by rfl⟩ : syracuseStep 2249491 = 3374237) B3374237
theorem B1069879 : Blo 888571 1069879 := bstep (se 1 (by rfl) ⟨802409, by rfl⟩ : syracuseStep 1069879 = 1604819) B1604819
theorem B1692571 : Blo 888571 1692571 := bstep (se 1 (by rfl) ⟨1269428, by rfl⟩ : syracuseStep 1692571 = 2538857) B2538857
theorem B1692647 : Blo 888571 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B4510727 : Blo 888571 4510727 := bstep (se 1 (by rfl) ⟨3383045, by rfl⟩ : syracuseStep 4510727 = 6766091) B6766091
theorem B2249927 : Blo 888571 2249927 := bstep (se 1 (by rfl) ⟨1687445, by rfl⟩ : syracuseStep 2249927 = 3374891) B3374891
theorem B2249977 : Blo 888571 2249977 := bstep (se 2 (by rfl) ⟨843741, by rfl⟩ : syracuseStep 2249977 = 1687483) B1687483
theorem B3003641 : Blo 888571 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B7329025 : Blo 888571 7329025 := bstep (se 2 (by rfl) ⟨2748384, by rfl⟩ : syracuseStep 7329025 = 5496769) B5496769
theorem B4511213 : Blo 888571 4511213 := bstep (se 3 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 4511213 = 1691705) B1691705
theorem B3003911 : Blo 888571 3003911 := bstep (se 1 (by rfl) ⟨2252933, by rfl⟩ : syracuseStep 3003911 = 4505867) B4505867
theorem B6772409 : Blo 888571 6772409 := bstep (se 2 (by rfl) ⟨2539653, by rfl⟩ : syracuseStep 6772409 = 5079307) B5079307
theorem B1332971 : Blo 888571 1332971 := bstep (se 1 (by rfl) ⟨999728, by rfl⟩ : syracuseStep 1332971 = 1999457) B1999457
theorem B1267435 : Blo 888571 1267435 := bstep (se 1 (by rfl) ⟨950576, by rfl⟩ : syracuseStep 1267435 = 1901153) B1901153
theorem B2250625 : Blo 888571 2250625 := bstep (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) B1687969
theorem B1333199 : Blo 888571 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B1267663 : Blo 888571 1267663 := bstep (se 1 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 1267663 = 1901495) B1901495
theorem B17094685 : Blo 888571 17094685 := bstep (se 3 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 17094685 = 6410507) B6410507
theorem B1693801 : Blo 888571 1693801 := bstep (se 2 (by rfl) ⟨635175, by rfl⟩ : syracuseStep 1693801 = 1270351) B1270351
theorem B4512023 : Blo 888571 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B1333595 : Blo 888571 1333595 := bstep (se 1 (by rfl) ⟨1000196, by rfl⟩ : syracuseStep 1333595 = 2000393) B2000393
theorem B3004883 : Blo 888571 3004883 := bstep (se 1 (by rfl) ⟨2253662, by rfl⟩ : syracuseStep 3004883 = 4507325) B4507325
theorem B1333823 : Blo 888571 1333823 := bstep (se 1 (by rfl) ⟨1000367, by rfl⟩ : syracuseStep 1333823 = 2000735) B2000735
theorem B5069375 : Blo 888571 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B3004991 : Blo 888571 3004991 := bstep (se 1 (by rfl) ⟨2253743, by rfl⟩ : syracuseStep 3004991 = 4507487) B4507487
theorem B2251385 : Blo 888571 2251385 := bstep (se 2 (by rfl) ⟨844269, by rfl⟩ : syracuseStep 2251385 = 1688539) B1688539
theorem B6773381 : Blo 888571 6773381 := bstep (se 4 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 6773381 = 1270009) B1270009
theorem B2251435 : Blo 888571 2251435 := bstep (se 1 (by rfl) ⟨1688576, by rfl⟩ : syracuseStep 2251435 = 3377153) B3377153
theorem B1333943 : Blo 888571 1333943 := bstep (se 1 (by rfl) ⟨1000457, by rfl⟩ : syracuseStep 1333943 = 2000915) B2000915
theorem B4807363 : Blo 888571 4807363 := bstep (se 1 (by rfl) ⟨3605522, by rfl⟩ : syracuseStep 4807363 = 7211045) B7211045
theorem B1334171 : Blo 888571 1334171 := bstep (se 1 (by rfl) ⟨1000628, by rfl⟩ : syracuseStep 1334171 = 2001257) B2001257
theorem B2251739 : Blo 888571 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B6085853 : Blo 888571 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B2252063 : Blo 888571 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B1334567 : Blo 888571 1334567 := bstep (se 1 (by rfl) ⟨1000925, by rfl⟩ : syracuseStep 1334567 = 2001851) B2001851
theorem B15392069 : Blo 888571 15392069 := bstep (se 4 (by rfl) ⟨1443006, by rfl⟩ : syracuseStep 15392069 = 2886013) B2886013
theorem B1334651 : Blo 888571 1334651 := bstep (se 1 (by rfl) ⟨1000988, by rfl⟩ : syracuseStep 1334651 = 2001977) B2001977
theorem B1334777 : Blo 888571 1334777 := bstep (se 2 (by rfl) ⟨500541, by rfl⟩ : syracuseStep 1334777 = 1001083) B1001083
theorem B6774353 : Blo 888571 6774353 := bstep (se 2 (by rfl) ⟨2540382, by rfl⟩ : syracuseStep 6774353 = 5080765) B5080765
theorem B1334879 : Blo 888571 1334879 := bstep (se 1 (by rfl) ⟨1001159, by rfl⟩ : syracuseStep 1334879 = 2002319) B2002319
theorem B8544041 : Blo 888571 8544041 := bstep (se 2 (by rfl) ⟨3204015, by rfl⟩ : syracuseStep 8544041 = 6408031) B6408031
theorem B1335095 : Blo 888571 1335095 := bstep (se 1 (by rfl) ⟨1001321, by rfl⟩ : syracuseStep 1335095 = 2002643) B2002643
theorem B4513643 : Blo 888571 4513643 := bstep (se 1 (by rfl) ⟨3385232, by rfl⟩ : syracuseStep 4513643 = 6770465) B6770465
theorem B1335401 : Blo 888571 1335401 := bstep (se 2 (by rfl) ⟨500775, by rfl⟩ : syracuseStep 1335401 = 1001551) B1001551
theorem B36528245 : Blo 888571 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B3006827 : Blo 888571 3006827 := bstep (se 1 (by rfl) ⟨2255120, by rfl⟩ : syracuseStep 3006827 = 4510241) B4510241
theorem B2253167 : Blo 888571 2253167 := bstep (se 1 (by rfl) ⟨1689875, by rfl⟩ : syracuseStep 2253167 = 3379751) B3379751
theorem B1335719 : Blo 888571 1335719 := bstep (se 1 (by rfl) ⟨1001789, by rfl⟩ : syracuseStep 1335719 = 2003579) B2003579
theorem B4809179 : Blo 888571 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B1335803 : Blo 888571 1335803 := bstep (se 1 (by rfl) ⟨1001852, by rfl⟩ : syracuseStep 1335803 = 2003705) B2003705
theorem B1499755 : Blo 888571 1499755 := bstep (se 1 (by rfl) ⟨1124816, by rfl⟩ : syracuseStep 1499755 = 2249633) B2249633
theorem B1335929 : Blo 888571 1335929 := bstep (se 2 (by rfl) ⟨500973, by rfl⟩ : syracuseStep 1335929 = 1001947) B1001947
theorem B3007097 : Blo 888571 3007097 := bstep (se 2 (by rfl) ⟨1127661, by rfl⟩ : syracuseStep 3007097 = 2255323) B2255323
theorem B7594631 : Blo 888571 7594631 := bstep (se 1 (by rfl) ⟨5695973, by rfl⟩ : syracuseStep 7594631 = 11391947) B11391947
theorem B1335983 : Blo 888571 1335983 := bstep (se 1 (by rfl) ⟨1001987, by rfl⟩ : syracuseStep 1335983 = 2003975) B2003975
theorem B4809419 : Blo 888571 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B1336031 : Blo 888571 1336031 := bstep (se 1 (by rfl) ⟨1002023, by rfl⟩ : syracuseStep 1336031 = 2004047) B2004047
theorem B1500059 : Blo 888571 1500059 := bstep (se 1 (by rfl) ⟨1125044, by rfl⟩ : syracuseStep 1500059 = 2250089) B2250089
theorem B5071835 : Blo 888571 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B1336295 : Blo 888571 1336295 := bstep (se 1 (by rfl) ⟨1002221, by rfl⟩ : syracuseStep 1336295 = 2004443) B2004443
theorem B2253815 : Blo 888571 2253815 := bstep (se 1 (by rfl) ⟨1690361, by rfl⟩ : syracuseStep 2253815 = 3380723) B3380723
theorem B6775811 : Blo 888571 6775811 := bstep (se 1 (by rfl) ⟨5081858, by rfl⟩ : syracuseStep 6775811 = 10163717) B10163717
theorem B1336553 : Blo 888571 1336553 := bstep (se 2 (by rfl) ⟨501207, by rfl⟩ : syracuseStep 1336553 = 1002415) B1002415
theorem B1336607 : Blo 888571 1336607 := bstep (se 1 (by rfl) ⟨1002455, by rfl⟩ : syracuseStep 1336607 = 2004911) B2004911
theorem B7595315 : Blo 888571 7595315 := bstep (se 1 (by rfl) ⟨5696486, by rfl⟩ : syracuseStep 7595315 = 11392973) B11392973
theorem B1926497 : Blo 888571 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B1336775 : Blo 888571 1336775 := bstep (se 1 (by rfl) ⟨1002581, by rfl⟩ : syracuseStep 1336775 = 2005163) B2005163
theorem B1337129 : Blo 888571 1337129 := bstep (se 2 (by rfl) ⟨501423, by rfl⟩ : syracuseStep 1337129 = 1002847) B1002847
theorem B1337135 : Blo 888571 1337135 := bstep (se 1 (by rfl) ⟨1002851, by rfl⟩ : syracuseStep 1337135 = 2005703) B2005703
theorem B37119833 : Blo 888571 37119833 := bstep (se 2 (by rfl) ⟨13919937, by rfl⟩ : syracuseStep 37119833 = 27839875) B27839875
theorem B27453329 : Blo 888571 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B6776783 : Blo 888571 6776783 := bstep (se 1 (by rfl) ⟨5082587, by rfl⟩ : syracuseStep 6776783 = 10165175) B10165175
theorem B1337609 : Blo 888571 1337609 := bstep (se 2 (by rfl) ⟨501603, by rfl⟩ : syracuseStep 1337609 = 1003207) B1003207
theorem B13035811 : Blo 888571 13035811 := bstep (se 1 (by rfl) ⟨9776858, by rfl⟩ : syracuseStep 13035811 = 19553717) B19553717
theorem B3008879 : Blo 888571 3008879 := bstep (se 1 (by rfl) ⟨2256659, by rfl⟩ : syracuseStep 3008879 = 4513319) B4513319
theorem B1337711 : Blo 888571 1337711 := bstep (se 1 (by rfl) ⟨1003283, by rfl⟩ : syracuseStep 1337711 = 2006567) B2006567
theorem B2288047 : Blo 888571 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B1337927 : Blo 888571 1337927 := bstep (se 1 (by rfl) ⟨1003445, by rfl⟩ : syracuseStep 1337927 = 2006891) B2006891
theorem B1337963 : Blo 888571 1337963 := bstep (se 1 (by rfl) ⟨1003472, by rfl⟩ : syracuseStep 1337963 = 2006945) B2006945
theorem B20834995 : Blo 888571 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B1338191 : Blo 888571 1338191 := bstep (se 1 (by rfl) ⟨1003643, by rfl⟩ : syracuseStep 1338191 = 2007287) B2007287
theorem B2255759 : Blo 888571 2255759 := bstep (se 1 (by rfl) ⟨1691819, by rfl⟩ : syracuseStep 2255759 = 3383639) B3383639
theorem B5074001 : Blo 888571 5074001 := bstep (se 2 (by rfl) ⟨1902750, by rfl⟩ : syracuseStep 5074001 = 3805501) B3805501
theorem B1338587 : Blo 888571 1338587 := bstep (se 1 (by rfl) ⟨1003940, by rfl⟩ : syracuseStep 1338587 = 2007881) B2007881
theorem B1338761 : Blo 888571 1338761 := bstep (se 2 (by rfl) ⟨502035, by rfl⟩ : syracuseStep 1338761 = 1004071) B1004071
theorem B4517369 : Blo 888571 4517369 := bstep (se 2 (by rfl) ⟨1694013, by rfl⟩ : syracuseStep 4517369 = 3388027) B3388027
theorem B2256619 : Blo 888571 2256619 := bstep (se 1 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 2256619 = 3384929) B3384929
theorem B3010283 : Blo 888571 3010283 := bstep (se 1 (by rfl) ⟨2257712, by rfl⟩ : syracuseStep 3010283 = 4515425) B4515425
theorem B4517693 : Blo 888571 4517693 := bstep (se 3 (by rfl) ⟨847067, by rfl⟩ : syracuseStep 4517693 = 1694135) B1694135
theorem B9760733 : Blo 888571 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B4288571 : Blo 888571 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B2748521 : Blo 888571 2748521 := bstep (se 2 (by rfl) ⟨1030695, by rfl⟩ : syracuseStep 2748521 = 2061391) B2061391
theorem B19231181 : Blo 888571 19231181 := bstep (se 3 (by rfl) ⟨3605846, by rfl⟩ : syracuseStep 19231181 = 7211693) B7211693
theorem B2257591 : Blo 888571 2257591 := bstep (se 1 (by rfl) ⟨1693193, by rfl⟩ : syracuseStep 2257591 = 3386387) B3386387
theorem B3011255 : Blo 888571 3011255 := bstep (se 1 (by rfl) ⟨2258441, by rfl⟩ : syracuseStep 3011255 = 4516883) B4516883
theorem B1503967 : Blo 888571 1503967 := bstep (se 1 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 1503967 = 2255951) B2255951
theorem B2847707 : Blo 888571 2847707 := bstep (se 1 (by rfl) ⟨2135780, by rfl⟩ : syracuseStep 2847707 = 4271561) B4271561
theorem B2257895 : Blo 888571 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B1504399 : Blo 888571 1504399 := bstep (se 1 (by rfl) ⟨1128299, by rfl⟩ : syracuseStep 1504399 = 2256599) B2256599
theorem B1504649 : Blo 888571 1504649 := bstep (se 2 (by rfl) ⟨564243, by rfl⟩ : syracuseStep 1504649 = 1128487) B1128487
theorem B5207435 : Blo 888571 5207435 := bstep (se 1 (by rfl) ⟨3905576, by rfl⟩ : syracuseStep 5207435 = 7811153) B7811153
theorem B8123809 : Blo 888571 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B7206347 : Blo 888571 7206347 := bstep (se 1 (by rfl) ⟨5404760, by rfl⟩ : syracuseStep 7206347 = 10809521) B10809521
theorem B5076665 : Blo 888571 5076665 := bstep (se 2 (by rfl) ⟨1903749, by rfl⟩ : syracuseStep 5076665 = 3807499) B3807499
theorem B1505081 : Blo 888571 1505081 := bstep (se 2 (by rfl) ⟨564405, by rfl⟩ : syracuseStep 1505081 = 1128811) B1128811
theorem B2259049 : Blo 888571 2259049 := bstep (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) B1694287
theorem B1898761 : Blo 888571 1898761 := bstep (se 2 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 1898761 = 1424071) B1424071
theorem B62552711 : Blo 888571 62552711 := bstep (se 1 (by rfl) ⟨46914533, by rfl⟩ : syracuseStep 62552711 = 93829067) B93829067
theorem B1506127 : Blo 888571 1506127 := bstep (se 1 (by rfl) ⟨1129595, by rfl⟩ : syracuseStep 1506127 = 2259191) B2259191
theorem B1899769 : Blo 888571 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B2850167 : Blo 888571 2850167 := bstep (se 1 (by rfl) ⟨2137625, by rfl⟩ : syracuseStep 2850167 = 4275251) B4275251
theorem B1900025 : Blo 888571 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B3374905 : Blo 888571 3374905 := bstep (se 2 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 3374905 = 2531179) B2531179
theorem B1605583 : Blo 888571 1605583 := bstep (se 1 (by rfl) ⟨1204187, by rfl⟩ : syracuseStep 1605583 = 2408375) B2408375
theorem B1900999 : Blo 888571 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B25690931 : Blo 888571 25690931 := bstep (se 1 (by rfl) ⟨19268198, by rfl⟩ : syracuseStep 25690931 = 38536397) B38536397
theorem B1999673 : Blo 888571 1999673 := bstep (se 2 (by rfl) ⟨749877, by rfl⟩ : syracuseStep 1999673 = 1499755) B1499755
theorem B1999727 : Blo 888571 1999727 := bstep (se 1 (by rfl) ⟨1499795, by rfl⟩ : syracuseStep 1999727 = 2999591) B2999591
theorem B2000303 : Blo 888571 2000303 := bstep (se 1 (by rfl) ⟨1500227, by rfl⟩ : syracuseStep 2000303 = 3000455) B3000455
theorem B3376637 : Blo 888571 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B18286397 : Blo 888571 18286397 := bstep (se 3 (by rfl) ⟨3428699, by rfl⟩ : syracuseStep 18286397 = 6857399) B6857399
theorem B2001131 : Blo 888571 2001131 := bstep (se 1 (by rfl) ⟨1500848, by rfl⟩ : syracuseStep 2001131 = 3001697) B3001697
theorem B1902827 : Blo 888571 1902827 := bstep (se 1 (by rfl) ⟨1427120, by rfl⟩ : syracuseStep 1902827 = 2854241) B2854241
theorem B1903135 : Blo 888571 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B12847895 : Blo 888571 12847895 := bstep (se 1 (by rfl) ⟨9635921, by rfl⟩ : syracuseStep 12847895 = 19271843) B19271843
theorem B4819799 : Blo 888571 4819799 := bstep (se 1 (by rfl) ⟨3614849, by rfl⟩ : syracuseStep 4819799 = 7229699) B7229699
theorem B24742991 : Blo 888571 24742991 := bstep (se 1 (by rfl) ⟨18557243, by rfl⟩ : syracuseStep 24742991 = 37114487) B37114487
theorem B3050729 : Blo 888571 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B2002427 : Blo 888571 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B2002607 : Blo 888571 2002607 := bstep (se 1 (by rfl) ⟨1501955, by rfl⟩ : syracuseStep 2002607 = 3003911) B3003911
theorem B888647 : Blo 888571 888647 := bstep (se 1 (by rfl) ⟨666485, by rfl⟩ : syracuseStep 888647 = 1332971) B1332971
theorem B21630797 : Blo 888571 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B888799 : Blo 888571 888799 := bstep (se 1 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 888799 = 1333199) B1333199
theorem B889063 : Blo 888571 889063 := bstep (se 1 (by rfl) ⟨666797, by rfl⟩ : syracuseStep 889063 = 1333595) B1333595
theorem B2003255 : Blo 888571 2003255 := bstep (se 1 (by rfl) ⟨1502441, by rfl⟩ : syracuseStep 2003255 = 3004883) B3004883
theorem B889215 : Blo 888571 889215 := bstep (se 1 (by rfl) ⟨666911, by rfl⟩ : syracuseStep 889215 = 1333823) B1333823
theorem B3379583 : Blo 888571 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B2003327 : Blo 888571 2003327 := bstep (se 1 (by rfl) ⟨1502495, by rfl⟩ : syracuseStep 2003327 = 3004991) B3004991
theorem B889295 : Blo 888571 889295 := bstep (se 1 (by rfl) ⟨666971, by rfl⟩ : syracuseStep 889295 = 1333943) B1333943
theorem B3805775 : Blo 888571 3805775 := bstep (se 1 (by rfl) ⟨2854331, by rfl⟩ : syracuseStep 3805775 = 5708663) B5708663
theorem B889447 : Blo 888571 889447 := bstep (se 1 (by rfl) ⟨667085, by rfl⟩ : syracuseStep 889447 = 1334171) B1334171
theorem B889711 : Blo 888571 889711 := bstep (se 1 (by rfl) ⟨667283, by rfl⟩ : syracuseStep 889711 = 1334567) B1334567
theorem B10261379 : Blo 888571 10261379 := bstep (se 1 (by rfl) ⟨7696034, by rfl⟩ : syracuseStep 10261379 = 15392069) B15392069
theorem B889767 : Blo 888571 889767 := bstep (se 1 (by rfl) ⟨667325, by rfl⟩ : syracuseStep 889767 = 1334651) B1334651
theorem B889851 : Blo 888571 889851 := bstep (se 1 (by rfl) ⟨667388, by rfl⟩ : syracuseStep 889851 = 1334777) B1334777
theorem B889919 : Blo 888571 889919 := bstep (se 1 (by rfl) ⟨667439, by rfl⟩ : syracuseStep 889919 = 1334879) B1334879
theorem B890063 : Blo 888571 890063 := bstep (se 1 (by rfl) ⟨667547, by rfl⟩ : syracuseStep 890063 = 1335095) B1335095
theorem B11408759 : Blo 888571 11408759 := bstep (se 1 (by rfl) ⟨8556569, by rfl⟩ : syracuseStep 11408759 = 17113139) B17113139
theorem B890267 : Blo 888571 890267 := bstep (se 1 (by rfl) ⟨667700, by rfl⟩ : syracuseStep 890267 = 1335401) B1335401
theorem B24352163 : Blo 888571 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B2004551 : Blo 888571 2004551 := bstep (se 1 (by rfl) ⟨1503413, by rfl⟩ : syracuseStep 2004551 = 3006827) B3006827
theorem B890479 : Blo 888571 890479 := bstep (se 1 (by rfl) ⟨667859, by rfl⟩ : syracuseStep 890479 = 1335719) B1335719
theorem B890535 : Blo 888571 890535 := bstep (se 1 (by rfl) ⟨667901, by rfl⟩ : syracuseStep 890535 = 1335803) B1335803
theorem B890619 : Blo 888571 890619 := bstep (se 1 (by rfl) ⟨667964, by rfl⟩ : syracuseStep 890619 = 1335929) B1335929
theorem B2004731 : Blo 888571 2004731 := bstep (se 1 (by rfl) ⟨1503548, by rfl⟩ : syracuseStep 2004731 = 3007097) B3007097
theorem B890655 : Blo 888571 890655 := bstep (se 1 (by rfl) ⟨667991, by rfl⟩ : syracuseStep 890655 = 1335983) B1335983
theorem B890687 : Blo 888571 890687 := bstep (se 1 (by rfl) ⟨668015, by rfl⟩ : syracuseStep 890687 = 1336031) B1336031
theorem B3381223 : Blo 888571 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B890863 : Blo 888571 890863 := bstep (se 1 (by rfl) ⟨668147, by rfl⟩ : syracuseStep 890863 = 1336295) B1336295
theorem B891035 : Blo 888571 891035 := bstep (se 1 (by rfl) ⟨668276, by rfl⟩ : syracuseStep 891035 = 1336553) B1336553
theorem B891071 : Blo 888571 891071 := bstep (se 1 (by rfl) ⟨668303, by rfl⟩ : syracuseStep 891071 = 1336607) B1336607
theorem B3807431 : Blo 888571 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B1284331 : Blo 888571 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B2005289 : Blo 888571 2005289 := bstep (se 2 (by rfl) ⟨751983, by rfl⟩ : syracuseStep 2005289 = 1503967) B1503967
theorem B891183 : Blo 888571 891183 := bstep (se 1 (by rfl) ⟨668387, by rfl⟩ : syracuseStep 891183 = 1336775) B1336775
theorem B891419 : Blo 888571 891419 := bstep (se 1 (by rfl) ⟨668564, by rfl⟩ : syracuseStep 891419 = 1337129) B1337129
theorem B891423 : Blo 888571 891423 := bstep (se 1 (by rfl) ⟨668567, by rfl⟩ : syracuseStep 891423 = 1337135) B1337135
theorem B24746555 : Blo 888571 24746555 := bstep (se 1 (by rfl) ⟨18559916, by rfl⟩ : syracuseStep 24746555 = 37119833) B37119833
theorem B891739 : Blo 888571 891739 := bstep (se 1 (by rfl) ⟨668804, by rfl⟩ : syracuseStep 891739 = 1337609) B1337609
theorem B2005865 : Blo 888571 2005865 := bstep (se 2 (by rfl) ⟨752199, by rfl⟩ : syracuseStep 2005865 = 1504399) B1504399
theorem B2005919 : Blo 888571 2005919 := bstep (se 1 (by rfl) ⟨1504439, by rfl⟩ : syracuseStep 2005919 = 3008879) B3008879
theorem B891807 : Blo 888571 891807 := bstep (se 1 (by rfl) ⟨668855, by rfl⟩ : syracuseStep 891807 = 1337711) B1337711
theorem B891951 : Blo 888571 891951 := bstep (se 1 (by rfl) ⟨668963, by rfl⟩ : syracuseStep 891951 = 1337927) B1337927
theorem B891975 : Blo 888571 891975 := bstep (se 1 (by rfl) ⟨668981, by rfl⟩ : syracuseStep 891975 = 1337963) B1337963
theorem B892127 : Blo 888571 892127 := bstep (se 1 (by rfl) ⟨669095, by rfl⟩ : syracuseStep 892127 = 1338191) B1338191
theorem B3382667 : Blo 888571 3382667 := bstep (se 1 (by rfl) ⟨2537000, by rfl⟩ : syracuseStep 3382667 = 5074001) B5074001
theorem B892391 : Blo 888571 892391 := bstep (se 1 (by rfl) ⟨669293, by rfl⟩ : syracuseStep 892391 = 1338587) B1338587
theorem B892507 : Blo 888571 892507 := bstep (se 1 (by rfl) ⟨669380, by rfl⟩ : syracuseStep 892507 = 1338761) B1338761
theorem B2006855 : Blo 888571 2006855 := bstep (se 1 (by rfl) ⟨1505141, by rfl⟩ : syracuseStep 2006855 = 3010283) B3010283
theorem B2859047 : Blo 888571 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B12820787 : Blo 888571 12820787 := bstep (se 1 (by rfl) ⟨9615590, by rfl⟩ : syracuseStep 12820787 = 19231181) B19231181
theorem B2531681 : Blo 888571 2531681 := bstep (se 2 (by rfl) ⟨949380, by rfl⟩ : syracuseStep 2531681 = 1898761) B1898761
theorem B2007503 : Blo 888571 2007503 := bstep (se 1 (by rfl) ⟨1505627, by rfl⟩ : syracuseStep 2007503 = 3011255) B3011255
theorem B2008169 : Blo 888571 2008169 := bstep (se 2 (by rfl) ⟨753063, by rfl⟩ : syracuseStep 2008169 = 1506127) B1506127
theorem B3384443 : Blo 888571 3384443 := bstep (se 1 (by rfl) ⟨2538332, by rfl⟩ : syracuseStep 3384443 = 5076665) B5076665
theorem B2533025 : Blo 888571 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B2894015 : Blo 888571 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B7612811 : Blo 888571 7612811 := bstep (se 1 (by rfl) ⟨5709608, by rfl⟩ : syracuseStep 7612811 = 11419217) B11419217
theorem B4499873 : Blo 888571 4499873 := bstep (se 2 (by rfl) ⟨1687452, by rfl⟩ : syracuseStep 4499873 = 3374905) B3374905
theorem B2140777 : Blo 888571 2140777 := bstep (se 2 (by rfl) ⟨802791, by rfl⟩ : syracuseStep 2140777 = 1605583) B1605583
theorem B20556935 : Blo 888571 20556935 := bstep (se 1 (by rfl) ⟨15417701, by rfl⟩ : syracuseStep 20556935 = 30835403) B30835403
theorem B4500845 : Blo 888571 4500845 := bstep (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) B1687817
theorem B10137473 : Blo 888571 10137473 := bstep (se 2 (by rfl) ⟨3801552, by rfl⟩ : syracuseStep 10137473 = 7603105) B7603105
theorem B12824477 : Blo 888571 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B3387359 : Blo 888571 3387359 := bstep (se 1 (by rfl) ⟨2540519, by rfl⟩ : syracuseStep 3387359 = 5081039) B5081039
theorem B12824705 : Blo 888571 12824705 := bstep (se 2 (by rfl) ⟨4809264, by rfl⟩ : syracuseStep 12824705 = 9618529) B9618529
theorem B2535553 : Blo 888571 2535553 := bstep (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) B1901665
theorem B3387815 : Blo 888571 3387815 := bstep (se 1 (by rfl) ⟨2540861, by rfl⟩ : syracuseStep 3387815 = 5081723) B5081723
theorem B15217145 : Blo 888571 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B5714813 : Blo 888571 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B3388331 : Blo 888571 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B6599879 : Blo 888571 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B4109629 : Blo 888571 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B17381081 : Blo 888571 17381081 := bstep (se 2 (by rfl) ⟨6517905, by rfl⟩ : syracuseStep 17381081 = 13035811) B13035811
theorem B4503275 : Blo 888571 4503275 := bstep (se 1 (by rfl) ⟨3377456, by rfl⟩ : syracuseStep 4503275 = 6754913) B6754913
theorem B34748149 : Blo 888571 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B3094429 : Blo 888571 3094429 := bstep (se 3 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 3094429 = 1160411) B1160411
theorem B1128431 : Blo 888571 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B9615419 : Blo 888571 9615419 := bstep (se 1 (by rfl) ⟨7211564, by rfl⟩ : syracuseStep 9615419 = 14423129) B14423129
theorem B12204553 : Blo 888571 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B11123459 : Blo 888571 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B4504733 : Blo 888571 4504733 := bstep (se 3 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 4504733 = 1689275) B1689275
theorem B1424891 : Blo 888571 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B5422735 : Blo 888571 5422735 := bstep (se 1 (by rfl) ⟨4067051, by rfl⟩ : syracuseStep 5422735 = 8134103) B8134103
theorem B11386615 : Blo 888571 11386615 := bstep (se 1 (by rfl) ⟨8539961, by rfl⟩ : syracuseStep 11386615 = 17079923) B17079923
theorem B5063087 : Blo 888571 5063087 := bstep (se 1 (by rfl) ⟨3797315, by rfl⟩ : syracuseStep 5063087 = 7594631) B7594631
theorem B1688015 : Blo 888571 1688015 := bstep (se 1 (by rfl) ⟨1266011, by rfl⟩ : syracuseStep 1688015 = 2532023) B2532023
theorem B1000039 : Blo 888571 1000039 := bstep (se 1 (by rfl) ⟨750029, by rfl⟩ : syracuseStep 1000039 = 1500059) B1500059
theorem B2999051 : Blo 888571 2999051 := bstep (se 1 (by rfl) ⟨2249288, by rfl⟩ : syracuseStep 2999051 = 4498577) B4498577
theorem B5063543 : Blo 888571 5063543 := bstep (se 1 (by rfl) ⟨3797657, by rfl⟩ : syracuseStep 5063543 = 7595315) B7595315
theorem B2999321 : Blo 888571 2999321 := bstep (se 2 (by rfl) ⟨1124745, by rfl⟩ : syracuseStep 2999321 = 2249491) B2249491
theorem B1426505 : Blo 888571 1426505 := bstep (se 2 (by rfl) ⟨534939, by rfl⟩ : syracuseStep 1426505 = 1069879) B1069879
theorem B18302219 : Blo 888571 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B2999969 : Blo 888571 2999969 := bstep (se 2 (by rfl) ⟨1124988, by rfl⟩ : syracuseStep 2999969 = 2249977) B2249977
theorem B8570717 : Blo 888571 8570717 := bstep (se 3 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 8570717 = 3214019) B3214019
theorem B10831745 : Blo 888571 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B11421881 : Blo 888571 11421881 := bstep (se 2 (by rfl) ⟨4283205, by rfl⟩ : syracuseStep 11421881 = 8566411) B8566411
theorem B1689913 : Blo 888571 1689913 := bstep (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) B1267435
theorem B3000671 : Blo 888571 3000671 := bstep (se 1 (by rfl) ⟨2250503, by rfl⟩ : syracuseStep 3000671 = 4501007) B4501007
theorem B3000833 : Blo 888571 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B1690217 : Blo 888571 1690217 := bstep (se 2 (by rfl) ⟨633831, by rfl⟩ : syracuseStep 1690217 = 1267663) B1267663
theorem B6507155 : Blo 888571 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B22792913 : Blo 888571 22792913 := bstep (se 2 (by rfl) ⟨8547342, by rfl⟩ : syracuseStep 22792913 = 17094685) B17094685
theorem B3001319 : Blo 888571 3001319 := bstep (se 1 (by rfl) ⟨2250989, by rfl⟩ : syracuseStep 3001319 = 4501979) B4501979
theorem B3001643 : Blo 888571 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B3001913 : Blo 888571 3001913 := bstep (se 2 (by rfl) ⟨1125717, by rfl⟩ : syracuseStep 3001913 = 2251435) B2251435
theorem B6409817 : Blo 888571 6409817 := bstep (se 2 (by rfl) ⟨2403681, by rfl⟩ : syracuseStep 6409817 = 4807363) B4807363
theorem B1003099 : Blo 888571 1003099 := bstep (se 1 (by rfl) ⟨752324, by rfl⟩ : syracuseStep 1003099 = 1504649) B1504649
theorem B4804231 : Blo 888571 4804231 := bstep (se 1 (by rfl) ⟨3603173, by rfl⟩ : syracuseStep 4804231 = 7206347) B7206347
theorem B1429319 : Blo 888571 1429319 := bstep (se 1 (by rfl) ⟨1071989, by rfl⟩ : syracuseStep 1429319 = 2143979) B2143979
theorem B41602891 : Blo 888571 41602891 := bstep (se 1 (by rfl) ⟨31202168, by rfl⟩ : syracuseStep 41602891 = 62404337) B62404337
theorem B1003387 : Blo 888571 1003387 := bstep (se 1 (by rfl) ⟨752540, by rfl⟩ : syracuseStep 1003387 = 1505081) B1505081
theorem B4509917 : Blo 888571 4509917 := bstep (se 3 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 4509917 = 1691219) B1691219
theorem B4510079 : Blo 888571 4510079 := bstep (se 1 (by rfl) ⟨3382559, by rfl⟩ : syracuseStep 4510079 = 6765119) B6765119
theorem B10146221 : Blo 888571 10146221 := bstep (se 3 (by rfl) ⟨1902416, by rfl⟩ : syracuseStep 10146221 = 3804833) B3804833
theorem B41701807 : Blo 888571 41701807 := bstep (se 1 (by rfl) ⟨31276355, by rfl⟩ : syracuseStep 41701807 = 62552711) B62552711
theorem B1266683 : Blo 888571 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B10278103 : Blo 888571 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B2250139 : Blo 888571 2250139 := bstep (se 1 (by rfl) ⟨1687604, by rfl⟩ : syracuseStep 2250139 = 3375209) B3375209
theorem B3003803 : Blo 888571 3003803 := bstep (se 1 (by rfl) ⟨2252852, by rfl⟩ : syracuseStep 3003803 = 4505705) B4505705
theorem B1332857 : Blo 888571 1332857 := bstep (se 2 (by rfl) ⟨499821, by rfl⟩ : syracuseStep 1332857 = 999643) B999643
theorem B1267321 : Blo 888571 1267321 := bstep (se 2 (by rfl) ⟨475245, by rfl⟩ : syracuseStep 1267321 = 950491) B950491
theorem B1070759 : Blo 888571 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B2283179 : Blo 888571 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B1332959 : Blo 888571 1332959 := bstep (se 1 (by rfl) ⟨999719, by rfl⟩ : syracuseStep 1332959 = 1999439) B1999439
theorem B5068601 : Blo 888571 5068601 := bstep (se 2 (by rfl) ⟨1900725, by rfl⟩ : syracuseStep 5068601 = 3801451) B3801451
theorem B1333055 : Blo 888571 1333055 := bstep (se 1 (by rfl) ⟨999791, by rfl⟩ : syracuseStep 1333055 = 1999583) B1999583
theorem B1333223 : Blo 888571 1333223 := bstep (se 1 (by rfl) ⟨999917, by rfl⟩ : syracuseStep 1333223 = 1999835) B1999835
theorem B1333241 : Blo 888571 1333241 := bstep (se 2 (by rfl) ⟨499965, by rfl⟩ : syracuseStep 1333241 = 999931) B999931
theorem B1333343 : Blo 888571 1333343 := bstep (se 1 (by rfl) ⟨1000007, by rfl⟩ : syracuseStep 1333343 = 2000015) B2000015
theorem B3004559 : Blo 888571 3004559 := bstep (se 1 (by rfl) ⟨2253419, by rfl⟩ : syracuseStep 3004559 = 4506839) B4506839
theorem B1333403 : Blo 888571 1333403 := bstep (se 1 (by rfl) ⟨1000052, by rfl⟩ : syracuseStep 1333403 = 2000105) B2000105
theorem B1333439 : Blo 888571 1333439 := bstep (se 1 (by rfl) ⟨1000079, by rfl⟩ : syracuseStep 1333439 = 2000159) B2000159
theorem B10279111 : Blo 888571 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B1333481 : Blo 888571 1333481 := bstep (se 2 (by rfl) ⟨500055, by rfl⟩ : syracuseStep 1333481 = 1000111) B1000111
theorem B7624975 : Blo 888571 7624975 := bstep (se 1 (by rfl) ⟨5718731, by rfl⟩ : syracuseStep 7624975 = 11437463) B11437463
theorem B2709883 : Blo 888571 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B1333787 : Blo 888571 1333787 := bstep (se 1 (by rfl) ⟨1000340, by rfl⟩ : syracuseStep 1333787 = 2000681) B2000681
theorem B1268255 : Blo 888571 1268255 := bstep (se 1 (by rfl) ⟨951191, by rfl⟩ : syracuseStep 1268255 = 1902383) B1902383
theorem B1333865 : Blo 888571 1333865 := bstep (se 2 (by rfl) ⟨500199, by rfl⟩ : syracuseStep 1333865 = 1000399) B1000399
theorem B4512671 : Blo 888571 4512671 := bstep (se 1 (by rfl) ⟨3384503, by rfl⟩ : syracuseStep 4512671 = 6769007) B6769007
theorem B1334393 : Blo 888571 1334393 := bstep (se 2 (by rfl) ⟨500397, by rfl⟩ : syracuseStep 1334393 = 1000795) B1000795
theorem B1334495 : Blo 888571 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B3005693 : Blo 888571 3005693 := bstep (se 3 (by rfl) ⟨563567, by rfl⟩ : syracuseStep 3005693 = 1127135) B1127135
theorem B1334537 : Blo 888571 1334537 := bstep (se 2 (by rfl) ⟨500451, by rfl⟩ : syracuseStep 1334537 = 1000903) B1000903
theorem B1334639 : Blo 888571 1334639 := bstep (se 1 (by rfl) ⟨1000979, by rfl⟩ : syracuseStep 1334639 = 2001959) B2001959
theorem B1334759 : Blo 888571 1334759 := bstep (se 1 (by rfl) ⟨1001069, by rfl⟩ : syracuseStep 1334759 = 2002139) B2002139
theorem B1334891 : Blo 888571 1334891 := bstep (se 1 (by rfl) ⟨1001168, by rfl⟩ : syracuseStep 1334891 = 2002337) B2002337
theorem B1335017 : Blo 888571 1335017 := bstep (se 2 (by rfl) ⟨500631, by rfl⟩ : syracuseStep 1335017 = 1001263) B1001263
theorem B1335161 : Blo 888571 1335161 := bstep (se 2 (by rfl) ⟨500685, by rfl⟩ : syracuseStep 1335161 = 1001371) B1001371
theorem B1335263 : Blo 888571 1335263 := bstep (se 1 (by rfl) ⟨1001447, by rfl⟩ : syracuseStep 1335263 = 2002895) B2002895
theorem B3006503 : Blo 888571 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B1335515 : Blo 888571 1335515 := bstep (se 1 (by rfl) ⟨1001636, by rfl⟩ : syracuseStep 1335515 = 2003273) B2003273
theorem B1335527 : Blo 888571 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B19292417 : Blo 888571 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B4514129 : Blo 888571 4514129 := bstep (se 2 (by rfl) ⟨1692798, by rfl⟩ : syracuseStep 4514129 = 3385597) B3385597
theorem B1499519 : Blo 888571 1499519 := bstep (se 1 (by rfl) ⟨1124639, by rfl⟩ : syracuseStep 1499519 = 2249279) B2249279
theorem B1335689 : Blo 888571 1335689 := bstep (se 2 (by rfl) ⟨500883, by rfl⟩ : syracuseStep 1335689 = 1001767) B1001767
theorem B1335785 : Blo 888571 1335785 := bstep (se 2 (by rfl) ⟨500919, by rfl⟩ : syracuseStep 1335785 = 1001839) B1001839
theorem B1335911 : Blo 888571 1335911 := bstep (se 1 (by rfl) ⟨1001933, by rfl⟩ : syracuseStep 1335911 = 2003867) B2003867
theorem B3007151 : Blo 888571 3007151 := bstep (se 1 (by rfl) ⟨2255363, by rfl⟩ : syracuseStep 3007151 = 4510727) B4510727
theorem B1336043 : Blo 888571 1336043 := bstep (se 1 (by rfl) ⟨1002032, by rfl⟩ : syracuseStep 1336043 = 2004065) B2004065
theorem B1336073 : Blo 888571 1336073 := bstep (se 2 (by rfl) ⟨501027, by rfl⟩ : syracuseStep 1336073 = 1002055) B1002055
theorem B1499951 : Blo 888571 1499951 := bstep (se 1 (by rfl) ⟨1124963, by rfl⟩ : syracuseStep 1499951 = 2249927) B2249927
theorem B1336175 : Blo 888571 1336175 := bstep (se 1 (by rfl) ⟨1002131, by rfl⟩ : syracuseStep 1336175 = 2004263) B2004263
theorem B27779993 : Blo 888571 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B3007475 : Blo 888571 3007475 := bstep (se 1 (by rfl) ⟨2255606, by rfl⟩ : syracuseStep 3007475 = 4511213) B4511213
theorem B1336427 : Blo 888571 1336427 := bstep (se 1 (by rfl) ⟨1002320, by rfl⟩ : syracuseStep 1336427 = 2004641) B2004641
theorem B4514939 : Blo 888571 4514939 := bstep (se 1 (by rfl) ⟨3386204, by rfl⟩ : syracuseStep 4514939 = 6772409) B6772409
theorem B1336667 : Blo 888571 1336667 := bstep (se 1 (by rfl) ⟨1002500, by rfl⟩ : syracuseStep 1336667 = 2005001) B2005001
theorem B2713085 : Blo 888571 2713085 := bstep (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) B1017407
theorem B3008015 : Blo 888571 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B1336943 : Blo 888571 1336943 := bstep (se 1 (by rfl) ⟨1002707, by rfl⟩ : syracuseStep 1336943 = 2005415) B2005415
theorem B1337015 : Blo 888571 1337015 := bstep (se 1 (by rfl) ⟨1002761, by rfl⟩ : syracuseStep 1337015 = 2005523) B2005523
theorem B1337051 : Blo 888571 1337051 := bstep (se 1 (by rfl) ⟨1002788, by rfl⟩ : syracuseStep 1337051 = 2005577) B2005577
theorem B1500923 : Blo 888571 1500923 := bstep (se 1 (by rfl) ⟨1125692, by rfl⟩ : syracuseStep 1500923 = 2251385) B2251385
theorem B4515587 : Blo 888571 4515587 := bstep (se 1 (by rfl) ⟨3386690, by rfl⟩ : syracuseStep 4515587 = 6773381) B6773381
theorem B1337225 : Blo 888571 1337225 := bstep (se 2 (by rfl) ⟨501459, by rfl⟩ : syracuseStep 1337225 = 1002919) B1002919
theorem B1501159 : Blo 888571 1501159 := bstep (se 1 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 1501159 = 2251739) B2251739
theorem B1337327 : Blo 888571 1337327 := bstep (se 1 (by rfl) ⟨1002995, by rfl⟩ : syracuseStep 1337327 = 2005991) B2005991
theorem B5072975 : Blo 888571 5072975 := bstep (se 1 (by rfl) ⟨3804731, by rfl⟩ : syracuseStep 5072975 = 7609463) B7609463
theorem B4057235 : Blo 888571 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B1501375 : Blo 888571 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B1337579 : Blo 888571 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B1337639 : Blo 888571 1337639 := bstep (se 1 (by rfl) ⟨1003229, by rfl⟩ : syracuseStep 1337639 = 2006459) B2006459
theorem B2255161 : Blo 888571 2255161 := bstep (se 2 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 2255161 = 1691371) B1691371
theorem B3008825 : Blo 888571 3008825 := bstep (se 2 (by rfl) ⟨1128309, by rfl⟩ : syracuseStep 3008825 = 2256619) B2256619
theorem B1337723 : Blo 888571 1337723 := bstep (se 1 (by rfl) ⟨1003292, by rfl⟩ : syracuseStep 1337723 = 2006585) B2006585
theorem B4516235 : Blo 888571 4516235 := bstep (se 1 (by rfl) ⟨3387176, by rfl⟩ : syracuseStep 4516235 = 6774353) B6774353
theorem B5696027 : Blo 888571 5696027 := bstep (se 1 (by rfl) ⟨4272020, by rfl⟩ : syracuseStep 5696027 = 8544041) B8544041
theorem B3009095 : Blo 888571 3009095 := bstep (se 1 (by rfl) ⟨2256821, by rfl⟩ : syracuseStep 3009095 = 4513643) B4513643
theorem B36563557 : Blo 888571 36563557 := bstep (se 4 (by rfl) ⟨3427833, by rfl⟩ : syracuseStep 36563557 = 6855667) B6855667
theorem B2255465 : Blo 888571 2255465 := bstep (se 2 (by rfl) ⟨845799, by rfl⟩ : syracuseStep 2255465 = 1691599) B1691599
theorem B1337993 : Blo 888571 1337993 := bstep (se 2 (by rfl) ⟨501747, by rfl⟩ : syracuseStep 1337993 = 1003495) B1003495
theorem B1338167 : Blo 888571 1338167 := bstep (se 1 (by rfl) ⟨1003625, by rfl⟩ : syracuseStep 1338167 = 2007251) B2007251
theorem B1338203 : Blo 888571 1338203 := bstep (se 1 (by rfl) ⟨1003652, by rfl⟩ : syracuseStep 1338203 = 2007305) B2007305
theorem B1502111 : Blo 888571 1502111 := bstep (se 1 (by rfl) ⟨1126583, by rfl⟩ : syracuseStep 1502111 = 2253167) B2253167
theorem B1338347 : Blo 888571 1338347 := bstep (se 1 (by rfl) ⟨1003760, by rfl⟩ : syracuseStep 1338347 = 2007521) B2007521
theorem B3206279 : Blo 888571 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B1338551 : Blo 888571 1338551 := bstep (se 1 (by rfl) ⟨1003913, by rfl⟩ : syracuseStep 1338551 = 2007827) B2007827
theorem B48688361 : Blo 888571 48688361 := bstep (se 2 (by rfl) ⟨18258135, by rfl⟩ : syracuseStep 48688361 = 36516271) B36516271
theorem B1502543 : Blo 888571 1502543 := bstep (se 1 (by rfl) ⟨1126907, by rfl⟩ : syracuseStep 1502543 = 2253815) B2253815
theorem B4517207 : Blo 888571 4517207 := bstep (se 1 (by rfl) ⟨3387905, by rfl⟩ : syracuseStep 4517207 = 6775811) B6775811
theorem B11431313 : Blo 888571 11431313 := bstep (se 2 (by rfl) ⟨4286742, by rfl⟩ : syracuseStep 11431313 = 8573485) B8573485
theorem B1338791 : Blo 888571 1338791 := bstep (se 1 (by rfl) ⟨1004093, by rfl⟩ : syracuseStep 1338791 = 2008187) B2008187
theorem B30797333 : Blo 888571 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B2256457 : Blo 888571 2256457 := bstep (se 2 (by rfl) ⟨846171, by rfl⟩ : syracuseStep 2256457 = 1692343) B1692343
theorem B3010121 : Blo 888571 3010121 := bstep (se 2 (by rfl) ⟨1128795, by rfl⟩ : syracuseStep 3010121 = 2257591) B2257591
theorem B6418237 : Blo 888571 6418237 := bstep (se 3 (by rfl) ⟨1203419, by rfl⟩ : syracuseStep 6418237 = 2406839) B2406839
theorem B2256761 : Blo 888571 2256761 := bstep (se 2 (by rfl) ⟨846285, by rfl⟩ : syracuseStep 2256761 = 1692571) B1692571
theorem B4517855 : Blo 888571 4517855 := bstep (se 1 (by rfl) ⟨3388391, by rfl⟩ : syracuseStep 4517855 = 6776783) B6776783
theorem B39088133 : Blo 888571 39088133 := bstep (se 4 (by rfl) ⟨3664512, by rfl⟩ : syracuseStep 39088133 = 7329025) B7329025
theorem B4518017 : Blo 888571 4518017 := bstep (se 2 (by rfl) ⟨1694256, by rfl⟩ : syracuseStep 4518017 = 3388513) B3388513
theorem B3207433 : Blo 888571 3207433 := bstep (se 2 (by rfl) ⟨1202787, by rfl⟩ : syracuseStep 3207433 = 2405575) B2405575
theorem B1503839 : Blo 888571 1503839 := bstep (se 1 (by rfl) ⟨1127879, by rfl⟩ : syracuseStep 1503839 = 2255759) B2255759
theorem B8221601 : Blo 888571 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B2257915 : Blo 888571 2257915 := bstep (se 1 (by rfl) ⟨1693436, by rfl⟩ : syracuseStep 2257915 = 3386873) B3386873
theorem B3011579 : Blo 888571 3011579 := bstep (se 1 (by rfl) ⟨2258684, by rfl⟩ : syracuseStep 3011579 = 4517369) B4517369
theorem B3044407 : Blo 888571 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B2258027 : Blo 888571 2258027 := bstep (se 1 (by rfl) ⟨1693520, by rfl⟩ : syracuseStep 2258027 = 3387041) B3387041
theorem B3011795 : Blo 888571 3011795 := bstep (se 1 (by rfl) ⟨2258846, by rfl⟩ : syracuseStep 3011795 = 4517693) B4517693
theorem B1832347 : Blo 888571 1832347 := bstep (se 1 (by rfl) ⟨1374260, by rfl⟩ : syracuseStep 1832347 = 2748521) B2748521
theorem B2258401 : Blo 888571 2258401 := bstep (se 2 (by rfl) ⟨846900, by rfl⟩ : syracuseStep 2258401 = 1693801) B1693801
theorem B3012065 : Blo 888571 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B1898471 : Blo 888571 1898471 := bstep (se 1 (by rfl) ⟨1423853, by rfl⟩ : syracuseStep 1898471 = 2847707) B2847707
theorem B1505263 : Blo 888571 1505263 := bstep (se 1 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 1505263 = 2257895) B2257895
theorem B3209321 : Blo 888571 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B1505513 : Blo 888571 1505513 := bstep (se 2 (by rfl) ⟨564567, by rfl⟩ : syracuseStep 1505513 = 1129135) B1129135
theorem B3471623 : Blo 888571 3471623 := bstep (se 1 (by rfl) ⟨2603717, by rfl⟩ : syracuseStep 3471623 = 5207435) B5207435
theorem B2259323 : Blo 888571 2259323 := bstep (se 1 (by rfl) ⟨1694492, by rfl⟩ : syracuseStep 2259323 = 3388985) B3388985
theorem B2849627 : Blo 888571 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B5700689 : Blo 888571 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B949735 : Blo 888571 949735 := bstep (se 1 (by rfl) ⟨712301, by rfl⟩ : syracuseStep 949735 = 1424603) B1424603
theorem B1900111 : Blo 888571 1900111 := bstep (se 1 (by rfl) ⟨1425083, by rfl⟩ : syracuseStep 1900111 = 2850167) B2850167
theorem B3375391 : Blo 888571 3375391 := bstep (se 1 (by rfl) ⟨2531543, by rfl⟩ : syracuseStep 3375391 = 5063087) B5063087
theorem B1999367 : Blo 888571 1999367 := bstep (se 1 (by rfl) ⟨1499525, by rfl⟩ : syracuseStep 1999367 = 2999051) B2999051
theorem B3375695 : Blo 888571 3375695 := bstep (se 1 (by rfl) ⟨2531771, by rfl⟩ : syracuseStep 3375695 = 5063543) B5063543
theorem B1999547 : Blo 888571 1999547 := bstep (se 1 (by rfl) ⟨1499660, by rfl⟩ : syracuseStep 1999547 = 2999321) B2999321
theorem B1999979 : Blo 888571 1999979 := bstep (se 1 (by rfl) ⟨1499984, by rfl⟩ : syracuseStep 1999979 = 2999969) B2999969
theorem B12190931 : Blo 888571 12190931 := bstep (se 1 (by rfl) ⟨9143198, by rfl⟩ : syracuseStep 12190931 = 18286397) B18286397
theorem B2000447 : Blo 888571 2000447 := bstep (se 1 (by rfl) ⟨1500335, by rfl⟩ : syracuseStep 2000447 = 3000671) B3000671
theorem B2000555 : Blo 888571 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B3213199 : Blo 888571 3213199 := bstep (se 1 (by rfl) ⟨2409899, by rfl⟩ : syracuseStep 3213199 = 4819799) B4819799
theorem B2000879 : Blo 888571 2000879 := bstep (se 1 (by rfl) ⟨1500659, by rfl⟩ : syracuseStep 2000879 = 3001319) B3001319
theorem B2033819 : Blo 888571 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B2001095 : Blo 888571 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B2001275 : Blo 888571 2001275 := bstep (se 1 (by rfl) ⟨1500956, by rfl⟩ : syracuseStep 2001275 = 3001913) B3001913
theorem B952879 : Blo 888571 952879 := bstep (se 1 (by rfl) ⟨714659, by rfl⟩ : syracuseStep 952879 = 1429319) B1429319
theorem B14420531 : Blo 888571 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B2001545 : Blo 888571 2001545 := bstep (se 2 (by rfl) ⟨750579, by rfl⟩ : syracuseStep 2001545 = 1501159) B1501159
theorem B3377821 : Blo 888571 3377821 := bstep (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) B1266683
theorem B3804013 : Blo 888571 3804013 := bstep (se 3 (by rfl) ⟨713252, by rfl⟩ : syracuseStep 3804013 = 1426505) B1426505
theorem B2001833 : Blo 888571 2001833 := bstep (se 2 (by rfl) ⟨750687, by rfl⟩ : syracuseStep 2001833 = 1501375) B1501375
theorem B2854369 : Blo 888571 2854369 := bstep (se 2 (by rfl) ⟨1070388, by rfl⟩ : syracuseStep 2854369 = 2140777) B2140777
theorem B7605839 : Blo 888571 7605839 := bstep (se 1 (by rfl) ⟨5704379, by rfl⟩ : syracuseStep 7605839 = 11408759) B11408759
theorem B2002535 : Blo 888571 2002535 := bstep (se 1 (by rfl) ⟨1501901, by rfl⟩ : syracuseStep 2002535 = 3003803) B3003803
theorem B888571 : Blo 888571 888571 := bstep (se 1 (by rfl) ⟨666428, by rfl⟩ : syracuseStep 888571 = 1332857) B1332857
theorem B888639 : Blo 888571 888639 := bstep (se 1 (by rfl) ⟨666479, by rfl⟩ : syracuseStep 888639 = 1332959) B1332959
theorem B3379067 : Blo 888571 3379067 := bstep (se 1 (by rfl) ⟨2534300, by rfl⟩ : syracuseStep 3379067 = 5068601) B5068601
theorem B888703 : Blo 888571 888703 := bstep (se 1 (by rfl) ⟨666527, by rfl⟩ : syracuseStep 888703 = 1333055) B1333055
theorem B888815 : Blo 888571 888815 := bstep (se 1 (by rfl) ⟨666611, by rfl⟩ : syracuseStep 888815 = 1333223) B1333223
theorem B888827 : Blo 888571 888827 := bstep (se 1 (by rfl) ⟨666620, by rfl⟩ : syracuseStep 888827 = 1333241) B1333241
theorem B888895 : Blo 888571 888895 := bstep (se 1 (by rfl) ⟨666671, by rfl⟩ : syracuseStep 888895 = 1333343) B1333343
theorem B2003039 : Blo 888571 2003039 := bstep (se 1 (by rfl) ⟨1502279, by rfl⟩ : syracuseStep 2003039 = 3004559) B3004559
theorem B888935 : Blo 888571 888935 := bstep (se 1 (by rfl) ⟨666701, by rfl⟩ : syracuseStep 888935 = 1333403) B1333403
theorem B888959 : Blo 888571 888959 := bstep (se 1 (by rfl) ⟨666719, by rfl⟩ : syracuseStep 888959 = 1333439) B1333439
theorem B888987 : Blo 888571 888987 := bstep (se 1 (by rfl) ⟨666740, by rfl⟩ : syracuseStep 888987 = 1333481) B1333481
theorem B889191 : Blo 888571 889191 := bstep (se 1 (by rfl) ⟨666893, by rfl⟩ : syracuseStep 889191 = 1333787) B1333787
theorem B889243 : Blo 888571 889243 := bstep (se 1 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 889243 = 1333865) B1333865
theorem B2855357 : Blo 888571 2855357 := bstep (se 3 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 2855357 = 1070759) B1070759
theorem B889595 : Blo 888571 889595 := bstep (se 1 (by rfl) ⟨667196, by rfl⟩ : syracuseStep 889595 = 1334393) B1334393
theorem B889663 : Blo 888571 889663 := bstep (se 1 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 889663 = 1334495) B1334495
theorem B2003795 : Blo 888571 2003795 := bstep (se 1 (by rfl) ⟨1502846, by rfl⟩ : syracuseStep 2003795 = 3005693) B3005693
theorem B889691 : Blo 888571 889691 := bstep (se 1 (by rfl) ⟨667268, by rfl⟩ : syracuseStep 889691 = 1334537) B1334537
theorem B889759 : Blo 888571 889759 := bstep (se 1 (by rfl) ⟨667319, by rfl⟩ : syracuseStep 889759 = 1334639) B1334639
theorem B889839 : Blo 888571 889839 := bstep (se 1 (by rfl) ⟨667379, by rfl⟩ : syracuseStep 889839 = 1334759) B1334759
theorem B889927 : Blo 888571 889927 := bstep (se 1 (by rfl) ⟨667445, by rfl⟩ : syracuseStep 889927 = 1334891) B1334891
theorem B8557649 : Blo 888571 8557649 := bstep (se 2 (by rfl) ⟨3209118, by rfl⟩ : syracuseStep 8557649 = 6418237) B6418237
theorem B890011 : Blo 888571 890011 := bstep (se 1 (by rfl) ⟨667508, by rfl⟩ : syracuseStep 890011 = 1335017) B1335017
theorem B890107 : Blo 888571 890107 := bstep (se 1 (by rfl) ⟨667580, by rfl⟩ : syracuseStep 890107 = 1335161) B1335161
theorem B890175 : Blo 888571 890175 := bstep (se 1 (by rfl) ⟨667631, by rfl⟩ : syracuseStep 890175 = 1335263) B1335263
theorem B2004335 : Blo 888571 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B1906031 : Blo 888571 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B890343 : Blo 888571 890343 := bstep (se 1 (by rfl) ⟨667757, by rfl⟩ : syracuseStep 890343 = 1335515) B1335515
theorem B890351 : Blo 888571 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B3380737 : Blo 888571 3380737 := bstep (se 2 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 3380737 = 2535553) B2535553
theorem B890459 : Blo 888571 890459 := bstep (se 1 (by rfl) ⟨667844, by rfl⟩ : syracuseStep 890459 = 1335689) B1335689
theorem B890523 : Blo 888571 890523 := bstep (se 1 (by rfl) ⟨667892, by rfl⟩ : syracuseStep 890523 = 1335785) B1335785
theorem B890607 : Blo 888571 890607 := bstep (se 1 (by rfl) ⟨667955, by rfl⟩ : syracuseStep 890607 = 1335911) B1335911
theorem B2004767 : Blo 888571 2004767 := bstep (se 1 (by rfl) ⟨1503575, by rfl⟩ : syracuseStep 2004767 = 3007151) B3007151
theorem B890695 : Blo 888571 890695 := bstep (se 1 (by rfl) ⟨668021, by rfl⟩ : syracuseStep 890695 = 1336043) B1336043
theorem B890715 : Blo 888571 890715 := bstep (se 1 (by rfl) ⟨668036, by rfl⟩ : syracuseStep 890715 = 1336073) B1336073
theorem B890783 : Blo 888571 890783 := bstep (se 1 (by rfl) ⟨668087, by rfl⟩ : syracuseStep 890783 = 1336175) B1336175
theorem B18519995 : Blo 888571 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B2004983 : Blo 888571 2004983 := bstep (se 1 (by rfl) ⟨1503737, by rfl⟩ : syracuseStep 2004983 = 3007475) B3007475
theorem B890951 : Blo 888571 890951 := bstep (se 1 (by rfl) ⟨668213, by rfl⟩ : syracuseStep 890951 = 1336427) B1336427
theorem B891111 : Blo 888571 891111 := bstep (se 1 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 891111 = 1336667) B1336667
theorem B1808723 : Blo 888571 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B2005343 : Blo 888571 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B891295 : Blo 888571 891295 := bstep (se 1 (by rfl) ⟨668471, by rfl⟩ : syracuseStep 891295 = 1336943) B1336943
theorem B891343 : Blo 888571 891343 := bstep (se 1 (by rfl) ⟨668507, by rfl⟩ : syracuseStep 891343 = 1337015) B1337015
theorem B891367 : Blo 888571 891367 := bstep (se 1 (by rfl) ⟨668525, by rfl⟩ : syracuseStep 891367 = 1337051) B1337051
theorem B891483 : Blo 888571 891483 := bstep (se 1 (by rfl) ⟨668612, by rfl⟩ : syracuseStep 891483 = 1337225) B1337225
theorem B891551 : Blo 888571 891551 := bstep (se 1 (by rfl) ⟨668663, by rfl⟩ : syracuseStep 891551 = 1337327) B1337327
theorem B3381983 : Blo 888571 3381983 := bstep (se 1 (by rfl) ⟨2536487, by rfl⟩ : syracuseStep 3381983 = 5072975) B5072975
theorem B3382013 : Blo 888571 3382013 := bstep (se 3 (by rfl) ⟨634127, by rfl⟩ : syracuseStep 3382013 = 1268255) B1268255
theorem B891719 : Blo 888571 891719 := bstep (se 1 (by rfl) ⟨668789, by rfl⟩ : syracuseStep 891719 = 1337579) B1337579
theorem B891759 : Blo 888571 891759 := bstep (se 1 (by rfl) ⟨668819, by rfl⟩ : syracuseStep 891759 = 1337639) B1337639
theorem B2005883 : Blo 888571 2005883 := bstep (se 1 (by rfl) ⟨1504412, by rfl⟩ : syracuseStep 2005883 = 3008825) B3008825
theorem B891815 : Blo 888571 891815 := bstep (se 1 (by rfl) ⟨668861, by rfl⟩ : syracuseStep 891815 = 1337723) B1337723
theorem B13704137 : Blo 888571 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B2006063 : Blo 888571 2006063 := bstep (se 1 (by rfl) ⟨1504547, by rfl⟩ : syracuseStep 2006063 = 3009095) B3009095
theorem B5479505 : Blo 888571 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B891995 : Blo 888571 891995 := bstep (se 1 (by rfl) ⟨668996, by rfl⟩ : syracuseStep 891995 = 1337993) B1337993
theorem B24353909 : Blo 888571 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B892111 : Blo 888571 892111 := bstep (se 1 (by rfl) ⟨669083, by rfl⟩ : syracuseStep 892111 = 1338167) B1338167
theorem B892135 : Blo 888571 892135 := bstep (se 1 (by rfl) ⟨669101, by rfl⟩ : syracuseStep 892135 = 1338203) B1338203
theorem B892231 : Blo 888571 892231 := bstep (se 1 (by rfl) ⟨669173, by rfl⟩ : syracuseStep 892231 = 1338347) B1338347
theorem B2137519 : Blo 888571 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B13704623 : Blo 888571 13704623 := bstep (se 1 (by rfl) ⟨10278467, by rfl⟩ : syracuseStep 13704623 = 20556935) B20556935
theorem B892367 : Blo 888571 892367 := bstep (se 1 (by rfl) ⟨669275, by rfl⟩ : syracuseStep 892367 = 1338551) B1338551
theorem B892527 : Blo 888571 892527 := bstep (se 1 (by rfl) ⟨669395, by rfl⟩ : syracuseStep 892527 = 1338791) B1338791
theorem B2006747 : Blo 888571 2006747 := bstep (se 1 (by rfl) ⟨1505060, by rfl⟩ : syracuseStep 2006747 = 3010121) B3010121
theorem B6758315 : Blo 888571 6758315 := bstep (se 1 (by rfl) ⟨5068736, by rfl⟩ : syracuseStep 6758315 = 10137473) B10137473
theorem B2007017 : Blo 888571 2007017 := bstep (se 2 (by rfl) ⟨752631, by rfl⟩ : syracuseStep 2007017 = 1505263) B1505263
theorem B26058755 : Blo 888571 26058755 := bstep (se 1 (by rfl) ⟨19544066, by rfl⟩ : syracuseStep 26058755 = 39088133) B39088133
theorem B13705481 : Blo 888571 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B1712441 : Blo 888571 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B10166633 : Blo 888571 10166633 := bstep (se 2 (by rfl) ⟨3812487, by rfl⟩ : syracuseStep 10166633 = 7624975) B7624975
theorem B3613177 : Blo 888571 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B3809875 : Blo 888571 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B5481067 : Blo 888571 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B2007719 : Blo 888571 2007719 := bstep (se 1 (by rfl) ⟨1505789, by rfl⟩ : syracuseStep 2007719 = 3011579) B3011579
theorem B4399919 : Blo 888571 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B2007863 : Blo 888571 2007863 := bstep (se 1 (by rfl) ⟨1505897, by rfl⟩ : syracuseStep 2007863 = 3011795) B3011795
theorem B2008043 : Blo 888571 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B2139547 : Blo 888571 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B7415639 : Blo 888571 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B2533481 : Blo 888571 2533481 := bstep (se 2 (by rfl) ⟨950055, by rfl⟩ : syracuseStep 2533481 = 1900111) B1900111
theorem B15182153 : Blo 888571 15182153 := bstep (se 2 (by rfl) ⟨5693307, by rfl⟩ : syracuseStep 15182153 = 11386615) B11386615
theorem B1125343 : Blo 888571 1125343 := bstep (se 1 (by rfl) ⟨844007, by rfl⟩ : syracuseStep 1125343 = 1688015) B1688015
theorem B2534665 : Blo 888571 2534665 := bstep (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) B1900999
theorem B12201479 : Blo 888571 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B5713811 : Blo 888571 5713811 := bstep (se 1 (by rfl) ⟨4285358, by rfl⟩ : syracuseStep 5713811 = 8570717) B8570717
theorem B7221163 : Blo 888571 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B7614587 : Blo 888571 7614587 := bstep (se 1 (by rfl) ⟨5710940, by rfl⟩ : syracuseStep 7614587 = 11421881) B11421881
theorem B1126811 : Blo 888571 1126811 := bstep (se 1 (by rfl) ⟨845108, by rfl⟩ : syracuseStep 1126811 = 1690217) B1690217
theorem B4338103 : Blo 888571 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B8565263 : Blo 888571 8565263 := bstep (se 1 (by rfl) ⟨6423947, by rfl⟩ : syracuseStep 8565263 = 12847895) B12847895
theorem B16495327 : Blo 888571 16495327 := bstep (se 1 (by rfl) ⟨12371495, by rfl⟩ : syracuseStep 16495327 = 24742991) B24742991
theorem B4273211 : Blo 888571 4273211 := bstep (se 1 (by rfl) ⟨3204908, by rfl⟩ : syracuseStep 4273211 = 6409817) B6409817
theorem B6764147 : Blo 888571 6764147 := bstep (se 1 (by rfl) ⟨5073110, by rfl⟩ : syracuseStep 6764147 = 10146221) B10146221
theorem B2537183 : Blo 888571 2537183 := bstep (se 1 (by rfl) ⟨1902887, by rfl⟩ : syracuseStep 2537183 = 3805775) B3805775
theorem B2537513 : Blo 888571 2537513 := bstep (se 2 (by rfl) ⟨951567, by rfl⟩ : syracuseStep 2537513 = 1903135) B1903135
theorem B16234775 : Blo 888571 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B2538287 : Blo 888571 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B16497703 : Blo 888571 16497703 := bstep (se 1 (by rfl) ⟨12373277, by rfl⟩ : syracuseStep 16497703 = 24746555) B24746555
theorem B6405641 : Blo 888571 6405641 := bstep (se 2 (by rfl) ⟨2402115, by rfl⟩ : syracuseStep 6405641 = 4804231) B4804231
theorem B12861611 : Blo 888571 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B1687787 : Blo 888571 1687787 := bstep (se 1 (by rfl) ⟨1265840, by rfl⟩ : syracuseStep 1687787 = 2531681) B2531681
theorem B999679 : Blo 888571 999679 := bstep (se 1 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 999679 = 1499519) B1499519
theorem B4276577 : Blo 888571 4276577 := bstep (se 2 (by rfl) ⟨1603716, by rfl⟩ : syracuseStep 4276577 = 3207433) B3207433
theorem B999967 : Blo 888571 999967 := bstep (se 1 (by rfl) ⟨749975, by rfl⟩ : syracuseStep 999967 = 1499951) B1499951
theorem B1688683 : Blo 888571 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B1000615 : Blo 888571 1000615 := bstep (se 1 (by rfl) ⟨750461, by rfl⟩ : syracuseStep 1000615 = 1500923) B1500923
theorem B2704823 : Blo 888571 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B2999915 : Blo 888571 2999915 := bstep (se 1 (by rfl) ⟨2249936, by rfl⟩ : syracuseStep 2999915 = 4499873) B4499873
theorem B3000185 : Blo 888571 3000185 := bstep (se 2 (by rfl) ⟨1125069, by rfl⟩ : syracuseStep 3000185 = 2250139) B2250139
theorem B2443129 : Blo 888571 2443129 := bstep (se 2 (by rfl) ⟨916173, by rfl⟩ : syracuseStep 2443129 = 1832347) B1832347
theorem B1001407 : Blo 888571 1001407 := bstep (se 1 (by rfl) ⟨751055, by rfl⟩ : syracuseStep 1001407 = 1502111) B1502111
theorem B32458907 : Blo 888571 32458907 := bstep (se 1 (by rfl) ⟨24344180, by rfl⟩ : syracuseStep 32458907 = 48688361) B48688361
theorem B1689761 : Blo 888571 1689761 := bstep (se 2 (by rfl) ⟨633660, by rfl⟩ : syracuseStep 1689761 = 1267321) B1267321
theorem B1001695 : Blo 888571 1001695 := bstep (se 1 (by rfl) ⟨751271, by rfl⟩ : syracuseStep 1001695 = 1502543) B1502543
theorem B3000563 : Blo 888571 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B7620875 : Blo 888571 7620875 := bstep (se 1 (by rfl) ⟨5715656, by rfl⟩ : syracuseStep 7620875 = 11431313) B11431313
theorem B20531555 : Blo 888571 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B5065253 : Blo 888571 5065253 := bstep (se 4 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 5065253 = 949735) B949735
theorem B4508297 : Blo 888571 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B10144763 : Blo 888571 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B1002559 : Blo 888571 1002559 := bstep (se 1 (by rfl) ⟨751919, by rfl⟩ : syracuseStep 1002559 = 1503839) B1503839
theorem B16272737 : Blo 888571 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B11587387 : Blo 888571 11587387 := bstep (se 1 (by rfl) ⟨8690540, by rfl⟩ : syracuseStep 11587387 = 17381081) B17381081
theorem B3002183 : Blo 888571 3002183 := bstep (se 1 (by rfl) ⟨2251637, by rfl⟩ : syracuseStep 3002183 = 4503275) B4503275
theorem B1265647 : Blo 888571 1265647 := bstep (se 1 (by rfl) ⟨949235, by rfl⟩ : syracuseStep 1265647 = 1898471) B1898471
theorem B6410279 : Blo 888571 6410279 := bstep (se 1 (by rfl) ⟨4807709, by rfl⟩ : syracuseStep 6410279 = 9615419) B9615419
theorem B1003675 : Blo 888571 1003675 := bstep (se 1 (by rfl) ⟨752756, by rfl⟩ : syracuseStep 1003675 = 1505513) B1505513
theorem B2314415 : Blo 888571 2314415 := bstep (se 1 (by rfl) ⟨1735811, by rfl⟩ : syracuseStep 2314415 = 3471623) B3471623
theorem B3003155 : Blo 888571 3003155 := bstep (se 1 (by rfl) ⟨2252366, by rfl⟩ : syracuseStep 3003155 = 4504733) B4504733
theorem B7230313 : Blo 888571 7230313 := bstep (se 2 (by rfl) ⟨2711367, by rfl⟩ : syracuseStep 7230313 = 5422735) B5422735
theorem B17127287 : Blo 888571 17127287 := bstep (se 1 (by rfl) ⟨12845465, by rfl⟩ : syracuseStep 17127287 = 25690931) B25690931
theorem B1333115 : Blo 888571 1333115 := bstep (se 1 (by rfl) ⟨999836, by rfl⟩ : syracuseStep 1333115 = 1999673) B1999673
theorem B1333151 : Blo 888571 1333151 := bstep (se 1 (by rfl) ⟨999863, by rfl⟩ : syracuseStep 1333151 = 1999727) B1999727
theorem B1333385 : Blo 888571 1333385 := bstep (se 2 (by rfl) ⟨500019, by rfl⟩ : syracuseStep 1333385 = 1000039) B1000039
theorem B1333535 : Blo 888571 1333535 := bstep (se 1 (by rfl) ⟨1000151, by rfl⟩ : syracuseStep 1333535 = 2000303) B2000303
theorem B2251091 : Blo 888571 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B1334087 : Blo 888571 1334087 := bstep (se 1 (by rfl) ⟨1000565, by rfl⟩ : syracuseStep 1334087 = 2001131) B2001131
theorem B1268551 : Blo 888571 1268551 := bstep (se 1 (by rfl) ⟨951413, by rfl⟩ : syracuseStep 1268551 = 1902827) B1902827
theorem B15195275 : Blo 888571 15195275 := bstep (se 1 (by rfl) ⟨11396456, by rfl⟩ : syracuseStep 15195275 = 22792913) B22792913
theorem B1334951 : Blo 888571 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B1335071 : Blo 888571 1335071 := bstep (se 1 (by rfl) ⟨1001303, by rfl⟩ : syracuseStep 1335071 = 2002607) B2002607
theorem B3006611 : Blo 888571 3006611 := bstep (se 1 (by rfl) ⟨2254958, by rfl⟩ : syracuseStep 3006611 = 4509917) B4509917
theorem B1335503 : Blo 888571 1335503 := bstep (se 1 (by rfl) ⟨1001627, by rfl⟩ : syracuseStep 1335503 = 2003255) B2003255
theorem B2253055 : Blo 888571 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B1335551 : Blo 888571 1335551 := bstep (se 1 (by rfl) ⟨1001663, by rfl⟩ : syracuseStep 1335551 = 2003327) B2003327
theorem B3006719 : Blo 888571 3006719 := bstep (se 1 (by rfl) ⟨2255039, by rfl⟩ : syracuseStep 3006719 = 4510079) B4510079
theorem B2253217 : Blo 888571 2253217 := bstep (se 2 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 2253217 = 1689913) B1689913
theorem B3006881 : Blo 888571 3006881 := bstep (se 2 (by rfl) ⟨1127580, by rfl⟩ : syracuseStep 3006881 = 2255161) B2255161
theorem B6840919 : Blo 888571 6840919 := bstep (se 1 (by rfl) ⟨5130689, by rfl⟩ : syracuseStep 6840919 = 10261379) B10261379
theorem B48751409 : Blo 888571 48751409 := bstep (se 2 (by rfl) ⟨18281778, by rfl⟩ : syracuseStep 48751409 = 36563557) B36563557
theorem B1336367 : Blo 888571 1336367 := bstep (se 1 (by rfl) ⟨1002275, by rfl⟩ : syracuseStep 1336367 = 2004551) B2004551
theorem B1336487 : Blo 888571 1336487 := bstep (se 1 (by rfl) ⟨1002365, by rfl⟩ : syracuseStep 1336487 = 2004731) B2004731
theorem B1336859 : Blo 888571 1336859 := bstep (se 1 (by rfl) ⟨1002644, by rfl⟩ : syracuseStep 1336859 = 2005289) B2005289
theorem B1337243 : Blo 888571 1337243 := bstep (se 1 (by rfl) ⟨1002932, by rfl⟩ : syracuseStep 1337243 = 2005865) B2005865
theorem B3008447 : Blo 888571 3008447 := bstep (se 1 (by rfl) ⟨2256335, by rfl⟩ : syracuseStep 3008447 = 4512671) B4512671
theorem B1337279 : Blo 888571 1337279 := bstep (se 1 (by rfl) ⟨1002959, by rfl⟩ : syracuseStep 1337279 = 2005919) B2005919
theorem B3008609 : Blo 888571 3008609 := bstep (se 2 (by rfl) ⟨1128228, by rfl⟩ : syracuseStep 3008609 = 2256457) B2256457
theorem B1337465 : Blo 888571 1337465 := bstep (se 2 (by rfl) ⟨501549, by rfl⟩ : syracuseStep 1337465 = 1003099) B1003099
theorem B2255111 : Blo 888571 2255111 := bstep (se 1 (by rfl) ⟨1691333, by rfl⟩ : syracuseStep 2255111 = 3382667) B3382667
theorem B55470521 : Blo 888571 55470521 := bstep (se 2 (by rfl) ⟨20801445, by rfl⟩ : syracuseStep 55470521 = 41602891) B41602891
theorem B1337849 : Blo 888571 1337849 := bstep (se 2 (by rfl) ⟨501693, by rfl⟩ : syracuseStep 1337849 = 1003387) B1003387
theorem B1337903 : Blo 888571 1337903 := bstep (se 1 (by rfl) ⟨1003427, by rfl⟩ : syracuseStep 1337903 = 2006855) B2006855
theorem B3009149 : Blo 888571 3009149 := bstep (se 3 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 3009149 = 1128431) B1128431
theorem B8547191 : Blo 888571 8547191 := bstep (se 1 (by rfl) ⟨6410393, by rfl⟩ : syracuseStep 8547191 = 12820787) B12820787
theorem B3009419 : Blo 888571 3009419 := bstep (se 1 (by rfl) ⟨2257064, by rfl⟩ : syracuseStep 3009419 = 4514129) B4514129
theorem B1338335 : Blo 888571 1338335 := bstep (se 1 (by rfl) ⟨1003751, by rfl⟩ : syracuseStep 1338335 = 2007503) B2007503
theorem B55602409 : Blo 888571 55602409 := bstep (se 2 (by rfl) ⟨20850903, by rfl⟩ : syracuseStep 55602409 = 41701807) B41701807
theorem B1338779 : Blo 888571 1338779 := bstep (se 1 (by rfl) ⟨1004084, by rfl⟩ : syracuseStep 1338779 = 2008169) B2008169
theorem B2256295 : Blo 888571 2256295 := bstep (se 1 (by rfl) ⟨1692221, by rfl⟩ : syracuseStep 2256295 = 3384443) B3384443
theorem B3009959 : Blo 888571 3009959 := bstep (se 1 (by rfl) ⟨2257469, by rfl⟩ : syracuseStep 3009959 = 4514939) B4514939
theorem B3010391 : Blo 888571 3010391 := bstep (se 1 (by rfl) ⟨2257793, by rfl⟩ : syracuseStep 3010391 = 4515587) B4515587
theorem B3010553 : Blo 888571 3010553 := bstep (se 2 (by rfl) ⟨1128957, by rfl⟩ : syracuseStep 3010553 = 2257915) B2257915
theorem B4059209 : Blo 888571 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B1929343 : Blo 888571 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B5075207 : Blo 888571 5075207 := bstep (se 1 (by rfl) ⟨3806405, by rfl⟩ : syracuseStep 5075207 = 7612811) B7612811
theorem B3010823 : Blo 888571 3010823 := bstep (se 1 (by rfl) ⟨2258117, by rfl⟩ : syracuseStep 3010823 = 4516235) B4516235
theorem B3797351 : Blo 888571 3797351 := bstep (se 1 (by rfl) ⟨2848013, by rfl⟩ : syracuseStep 3797351 = 5696027) B5696027
theorem B1503643 : Blo 888571 1503643 := bstep (se 1 (by rfl) ⟨1127732, by rfl⟩ : syracuseStep 1503643 = 2255465) B2255465
theorem B3011201 : Blo 888571 3011201 := bstep (se 2 (by rfl) ⟨1129200, by rfl⟩ : syracuseStep 3011201 = 2258401) B2258401
theorem B3011471 : Blo 888571 3011471 := bstep (se 1 (by rfl) ⟨2258603, by rfl⟩ : syracuseStep 3011471 = 4517207) B4517207
theorem B7599005 : Blo 888571 7599005 := bstep (se 3 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 7599005 = 2849627) B2849627
theorem B46330865 : Blo 888571 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B4125905 : Blo 888571 4125905 := bstep (se 2 (by rfl) ⟨1547214, by rfl⟩ : syracuseStep 4125905 = 3094429) B3094429
theorem B1504507 : Blo 888571 1504507 := bstep (se 1 (by rfl) ⟨1128380, by rfl⟩ : syracuseStep 1504507 = 2256761) B2256761
theorem B8549651 : Blo 888571 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B2258239 : Blo 888571 2258239 := bstep (se 1 (by rfl) ⟨1693679, by rfl⟩ : syracuseStep 2258239 = 3387359) B3387359
theorem B3011903 : Blo 888571 3011903 := bstep (se 1 (by rfl) ⟨2258927, by rfl⟩ : syracuseStep 3011903 = 4517855) B4517855
theorem B8549803 : Blo 888571 8549803 := bstep (se 1 (by rfl) ⟨6412352, by rfl⟩ : syracuseStep 8549803 = 12824705) B12824705
theorem B3012011 : Blo 888571 3012011 := bstep (se 1 (by rfl) ⟨2259008, by rfl⟩ : syracuseStep 3012011 = 4518017) B4518017
theorem B2258543 : Blo 888571 2258543 := bstep (se 1 (by rfl) ⟨1693907, by rfl⟩ : syracuseStep 2258543 = 3387815) B3387815
theorem B2258887 : Blo 888571 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B1505351 : Blo 888571 1505351 := bstep (se 1 (by rfl) ⟨1129013, by rfl⟩ : syracuseStep 1505351 = 2258027) B2258027
theorem B3799709 : Blo 888571 3799709 := bstep (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) B1424891
theorem B1506215 : Blo 888571 1506215 := bstep (se 1 (by rfl) ⟨1129661, by rfl⟩ : syracuseStep 1506215 = 2259323) B2259323
theorem B3800459 : Blo 888571 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B2851051 : Blo 888571 2851051 := bstep (se 1 (by rfl) ⟨2138288, by rfl⟩ : syracuseStep 2851051 = 4276577) B4276577
theorem B4817569 : Blo 888571 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B5079833 : Blo 888571 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B8127287 : Blo 888571 8127287 := bstep (se 1 (by rfl) ⟨6095465, by rfl⟩ : syracuseStep 8127287 = 12190931) B12190931
theorem B7308089 : Blo 888571 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B1803215 : Blo 888571 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B1999943 : Blo 888571 1999943 := bstep (se 1 (by rfl) ⟨1499957, by rfl⟩ : syracuseStep 1999943 = 2999915) B2999915
theorem B2000123 : Blo 888571 2000123 := bstep (se 1 (by rfl) ⟨1500092, by rfl⟩ : syracuseStep 2000123 = 3000185) B3000185
theorem B2000375 : Blo 888571 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B5080583 : Blo 888571 5080583 := bstep (se 1 (by rfl) ⟨3810437, by rfl⟩ : syracuseStep 5080583 = 7620875) B7620875
theorem B3376835 : Blo 888571 3376835 := bstep (se 1 (by rfl) ⟨2532626, by rfl⟩ : syracuseStep 3376835 = 5065253) B5065253
theorem B2852729 : Blo 888571 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B10848491 : Blo 888571 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B2001455 : Blo 888571 2001455 := bstep (se 1 (by rfl) ⟨1501091, by rfl⟩ : syracuseStep 2001455 = 3002183) B3002183
theorem B1542943 : Blo 888571 1542943 := bstep (se 1 (by rfl) ⟨1157207, by rfl⟩ : syracuseStep 1542943 = 2314415) B2314415
theorem B1903571 : Blo 888571 1903571 := bstep (se 1 (by rfl) ⟨1427678, by rfl⟩ : syracuseStep 1903571 = 2855357) B2855357
theorem B2002103 : Blo 888571 2002103 := bstep (se 1 (by rfl) ⟨1501577, by rfl⟩ : syracuseStep 2002103 = 3003155) B3003155
theorem B5705099 : Blo 888571 5705099 := bstep (se 1 (by rfl) ⟨4278824, by rfl⟩ : syracuseStep 5705099 = 8557649) B8557649
theorem B5082749 : Blo 888571 5082749 := bstep (se 3 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 5082749 = 1906031) B1906031
theorem B888743 : Blo 888571 888743 := bstep (se 1 (by rfl) ⟨666557, by rfl⟩ : syracuseStep 888743 = 1333115) B1333115
theorem B888767 : Blo 888571 888767 := bstep (se 1 (by rfl) ⟨666575, by rfl⟩ : syracuseStep 888767 = 1333151) B1333151
theorem B888923 : Blo 888571 888923 := bstep (se 1 (by rfl) ⟨666692, by rfl⟩ : syracuseStep 888923 = 1333385) B1333385
theorem B889023 : Blo 888571 889023 := bstep (se 1 (by rfl) ⟨666767, by rfl⟩ : syracuseStep 889023 = 1333535) B1333535
theorem B3379553 : Blo 888571 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B889391 : Blo 888571 889391 := bstep (se 1 (by rfl) ⟨667043, by rfl⟩ : syracuseStep 889391 = 1334087) B1334087
theorem B3805825 : Blo 888571 3805825 := bstep (se 2 (by rfl) ⟨1427184, by rfl⟩ : syracuseStep 3805825 = 2854369) B2854369
theorem B10130183 : Blo 888571 10130183 := bstep (se 1 (by rfl) ⟨7597637, by rfl⟩ : syracuseStep 10130183 = 15195275) B15195275
theorem B889967 : Blo 888571 889967 := bstep (se 1 (by rfl) ⟨667475, by rfl⟩ : syracuseStep 889967 = 1334951) B1334951
theorem B890047 : Blo 888571 890047 := bstep (se 1 (by rfl) ⟨667535, by rfl⟩ : syracuseStep 890047 = 1335071) B1335071
theorem B17372503 : Blo 888571 17372503 := bstep (se 1 (by rfl) ⟨13029377, by rfl⟩ : syracuseStep 17372503 = 26058755) B26058755
theorem B2004407 : Blo 888571 2004407 := bstep (se 1 (by rfl) ⟨1503305, by rfl⟩ : syracuseStep 2004407 = 3006611) B3006611
theorem B890335 : Blo 888571 890335 := bstep (se 1 (by rfl) ⟨667751, by rfl⟩ : syracuseStep 890335 = 1335503) B1335503
theorem B890367 : Blo 888571 890367 := bstep (se 1 (by rfl) ⟨667775, by rfl⟩ : syracuseStep 890367 = 1335551) B1335551
theorem B2004479 : Blo 888571 2004479 := bstep (se 1 (by rfl) ⟨1503359, by rfl⟩ : syracuseStep 2004479 = 3006719) B3006719
theorem B2004587 : Blo 888571 2004587 := bstep (se 1 (by rfl) ⟨1503440, by rfl⟩ : syracuseStep 2004587 = 3006881) B3006881
theorem B2004857 : Blo 888571 2004857 := bstep (se 2 (by rfl) ⟨751821, by rfl⟩ : syracuseStep 2004857 = 1503643) B1503643
theorem B890911 : Blo 888571 890911 := bstep (se 1 (by rfl) ⟨668183, by rfl⟩ : syracuseStep 890911 = 1336367) B1336367
theorem B890991 : Blo 888571 890991 := bstep (se 1 (by rfl) ⟨668243, by rfl⟩ : syracuseStep 890991 = 1336487) B1336487
theorem B21993769 : Blo 888571 21993769 := bstep (se 2 (by rfl) ⟨8247663, by rfl⟩ : syracuseStep 21993769 = 16495327) B16495327
theorem B891239 : Blo 888571 891239 := bstep (se 1 (by rfl) ⟨668429, by rfl⟩ : syracuseStep 891239 = 1336859) B1336859
theorem B9640417 : Blo 888571 9640417 := bstep (se 2 (by rfl) ⟨3615156, by rfl⟩ : syracuseStep 9640417 = 7230313) B7230313
theorem B147921389 : Blo 888571 147921389 := bstep (se 3 (by rfl) ⟨27735260, by rfl⟩ : syracuseStep 147921389 = 55470521) B55470521
theorem B891495 : Blo 888571 891495 := bstep (se 1 (by rfl) ⟨668621, by rfl⟩ : syracuseStep 891495 = 1337243) B1337243
theorem B2005631 : Blo 888571 2005631 := bstep (se 1 (by rfl) ⟨1504223, by rfl⟩ : syracuseStep 2005631 = 3008447) B3008447
theorem B891519 : Blo 888571 891519 := bstep (se 1 (by rfl) ⟨668639, by rfl⟩ : syracuseStep 891519 = 1337279) B1337279
theorem B2005739 : Blo 888571 2005739 := bstep (se 1 (by rfl) ⟨1504304, by rfl⟩ : syracuseStep 2005739 = 3008609) B3008609
theorem B891643 : Blo 888571 891643 := bstep (se 1 (by rfl) ⟨668732, by rfl⟩ : syracuseStep 891643 = 1337465) B1337465
theorem B2006009 : Blo 888571 2006009 := bstep (se 2 (by rfl) ⟨752253, by rfl⟩ : syracuseStep 2006009 = 1504507) B1504507
theorem B891899 : Blo 888571 891899 := bstep (se 1 (by rfl) ⟨668924, by rfl⟩ : syracuseStep 891899 = 1337849) B1337849
theorem B891935 : Blo 888571 891935 := bstep (se 1 (by rfl) ⟨668951, by rfl⟩ : syracuseStep 891935 = 1337903) B1337903
theorem B2006099 : Blo 888571 2006099 := bstep (se 1 (by rfl) ⟨1504574, by rfl⟩ : syracuseStep 2006099 = 3009149) B3009149
theorem B2006279 : Blo 888571 2006279 := bstep (se 1 (by rfl) ⟨1504709, by rfl⟩ : syracuseStep 2006279 = 3009419) B3009419
theorem B892223 : Blo 888571 892223 := bstep (se 1 (by rfl) ⟨669167, by rfl⟩ : syracuseStep 892223 = 1338335) B1338335
theorem B892519 : Blo 888571 892519 := bstep (se 1 (by rfl) ⟨669389, by rfl⟩ : syracuseStep 892519 = 1338779) B1338779
theorem B2006639 : Blo 888571 2006639 := bstep (se 1 (by rfl) ⟨1504979, by rfl⟩ : syracuseStep 2006639 = 3009959) B3009959
theorem B8134319 : Blo 888571 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B2006927 : Blo 888571 2006927 := bstep (se 1 (by rfl) ⟨1505195, by rfl⟩ : syracuseStep 2006927 = 3010391) B3010391
theorem B3809207 : Blo 888571 3809207 := bstep (se 1 (by rfl) ⟨2856905, by rfl⟩ : syracuseStep 3809207 = 5713811) B5713811
theorem B2007035 : Blo 888571 2007035 := bstep (se 1 (by rfl) ⟨1505276, by rfl⟩ : syracuseStep 2007035 = 3010553) B3010553
theorem B3383471 : Blo 888571 3383471 := bstep (se 1 (by rfl) ⟨2537603, by rfl⟩ : syracuseStep 3383471 = 5075207) B5075207
theorem B2007215 : Blo 888571 2007215 := bstep (se 1 (by rfl) ⟨1505411, by rfl⟩ : syracuseStep 2007215 = 3010823) B3010823
theorem B2531567 : Blo 888571 2531567 := bstep (se 1 (by rfl) ⟨1898675, by rfl⟩ : syracuseStep 2531567 = 3797351) B3797351
theorem B5710175 : Blo 888571 5710175 := bstep (se 1 (by rfl) ⟨4282631, by rfl⟩ : syracuseStep 5710175 = 8565263) B8565263
theorem B2007467 : Blo 888571 2007467 := bstep (se 1 (by rfl) ⟨1505600, by rfl⟩ : syracuseStep 2007467 = 3011201) B3011201
theorem B2007647 : Blo 888571 2007647 := bstep (se 1 (by rfl) ⟨1505735, by rfl⟩ : syracuseStep 2007647 = 3011471) B3011471
theorem B2007935 : Blo 888571 2007935 := bstep (se 1 (by rfl) ⟨1505951, by rfl⟩ : syracuseStep 2007935 = 3011903) B3011903
theorem B2008007 : Blo 888571 2008007 := bstep (se 1 (by rfl) ⟨1506005, by rfl⟩ : syracuseStep 2008007 = 3012011) B3012011
theorem B10134557 : Blo 888571 10134557 := bstep (se 3 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 10134557 = 3800459) B3800459
theorem B21996937 : Blo 888571 21996937 := bstep (se 2 (by rfl) ⟨8248851, by rfl⟩ : syracuseStep 21996937 = 16497703) B16497703
theorem B10823183 : Blo 888571 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B2533139 : Blo 888571 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B4270427 : Blo 888571 4270427 := bstep (se 1 (by rfl) ⟨3202820, by rfl⟩ : syracuseStep 4270427 = 6405641) B6405641
theorem B1125191 : Blo 888571 1125191 := bstep (se 1 (by rfl) ⟨843893, by rfl⟩ : syracuseStep 1125191 = 1687787) B1687787
theorem B4500521 : Blo 888571 4500521 := bstep (se 2 (by rfl) ⟨1687695, by rfl⟩ : syracuseStep 4500521 = 3375391) B3375391
theorem B36547949 : Blo 888571 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B21639271 : Blo 888571 21639271 := bstep (se 1 (by rfl) ⟨16229453, by rfl⟩ : syracuseStep 21639271 = 32458907) B32458907
theorem B1355879 : Blo 888571 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B9613687 : Blo 888571 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B6763175 : Blo 888571 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B4273519 : Blo 888571 4273519 := bstep (se 1 (by rfl) ⟨3205139, by rfl⟩ : syracuseStep 4273519 = 6410279) B6410279
theorem B36484901 : Blo 888571 36484901 := bstep (se 4 (by rfl) ⟨3420459, by rfl⟩ : syracuseStep 36484901 = 6840919) B6840919
theorem B4503761 : Blo 888571 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B11418191 : Blo 888571 11418191 := bstep (se 1 (by rfl) ⟨8563643, by rfl⟩ : syracuseStep 11418191 = 17127287) B17127287
theorem B74136545 : Blo 888571 74136545 := bstep (se 2 (by rfl) ⟨27801204, by rfl⟩ : syracuseStep 74136545 = 55602409) B55602409
theorem B6765605 : Blo 888571 6765605 := bstep (se 4 (by rfl) ⟨634275, by rfl⟩ : syracuseStep 6765605 = 1268551) B1268551
theorem B3653003 : Blo 888571 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B16235939 : Blo 888571 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B15449849 : Blo 888571 15449849 := bstep (se 2 (by rfl) ⟨5793693, by rfl⟩ : syracuseStep 15449849 = 11587387) B11587387
theorem B4505543 : Blo 888571 4505543 := bstep (se 1 (by rfl) ⟨3379157, by rfl⟩ : syracuseStep 4505543 = 6758315) B6758315
theorem B1687529 : Blo 888571 1687529 := bstep (se 2 (by rfl) ⟨632823, by rfl⟩ : syracuseStep 1687529 = 1265647) B1265647
theorem B2572457 : Blo 888571 2572457 := bstep (se 2 (by rfl) ⟨964671, by rfl⟩ : syracuseStep 2572457 = 1929343) B1929343
theorem B4506029 : Blo 888571 4506029 := bstep (se 3 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 4506029 = 1689761) B1689761
theorem B2933279 : Blo 888571 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B5784137 : Blo 888571 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B1688987 : Blo 888571 1688987 := bstep (se 1 (by rfl) ⟨1266740, by rfl⟩ : syracuseStep 1688987 = 2533481) B2533481
theorem B4507649 : Blo 888571 4507649 := bstep (se 2 (by rfl) ⟨1690368, by rfl⟩ : syracuseStep 4507649 = 3380737) B3380737
theorem B2706139 : Blo 888571 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B5066003 : Blo 888571 5066003 := bstep (se 1 (by rfl) ⟨3799502, by rfl⟩ : syracuseStep 5066003 = 7599005) B7599005
theorem B30887243 : Blo 888571 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B4509431 : Blo 888571 4509431 := bstep (se 1 (by rfl) ⟨3382073, by rfl⟩ : syracuseStep 4509431 = 6764147) B6764147
theorem B1691455 : Blo 888571 1691455 := bstep (se 1 (by rfl) ⟨1268591, by rfl⟩ : syracuseStep 1691455 = 2537183) B2537183
theorem B1691675 : Blo 888571 1691675 := bstep (se 1 (by rfl) ⟨1268756, by rfl⟩ : syracuseStep 1691675 = 2537513) B2537513
theorem B1003567 : Blo 888571 1003567 := bstep (se 1 (by rfl) ⟨752675, by rfl⟩ : syracuseStep 1003567 = 1505351) B1505351
theorem B1692191 : Blo 888571 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1004143 : Blo 888571 1004143 := bstep (se 1 (by rfl) ⟨753107, by rfl⟩ : syracuseStep 1004143 = 1506215) B1506215
theorem B13030021 : Blo 888571 13030021 := bstep (se 4 (by rfl) ⟨1221564, by rfl⟩ : syracuseStep 13030021 = 2443129) B2443129
theorem B8574407 : Blo 888571 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B1332905 : Blo 888571 1332905 := bstep (se 2 (by rfl) ⟨499839, by rfl⟩ : syracuseStep 1332905 = 999679) B999679
theorem B3004073 : Blo 888571 3004073 := bstep (se 2 (by rfl) ⟨1126527, by rfl⟩ : syracuseStep 3004073 = 2253055) B2253055
theorem B1332911 : Blo 888571 1332911 := bstep (se 1 (by rfl) ⟨999683, by rfl⟩ : syracuseStep 1332911 = 1999367) B1999367
theorem B2250463 : Blo 888571 2250463 := bstep (se 1 (by rfl) ⟨1687847, by rfl⟩ : syracuseStep 2250463 = 3375695) B3375695
theorem B1333031 : Blo 888571 1333031 := bstep (se 1 (by rfl) ⟨999773, by rfl⟩ : syracuseStep 1333031 = 1999547) B1999547
theorem B3004289 : Blo 888571 3004289 := bstep (se 2 (by rfl) ⟨1126608, by rfl⟩ : syracuseStep 3004289 = 2253217) B2253217
theorem B1333289 : Blo 888571 1333289 := bstep (se 2 (by rfl) ⟨499983, by rfl⟩ : syracuseStep 1333289 = 999967) B999967
theorem B1333319 : Blo 888571 1333319 := bstep (se 1 (by rfl) ⟨999989, by rfl⟩ : syracuseStep 1333319 = 1999979) B1999979
theorem B1333631 : Blo 888571 1333631 := bstep (se 1 (by rfl) ⟨1000223, by rfl⟩ : syracuseStep 1333631 = 2000447) B2000447
theorem B3004829 : Blo 888571 3004829 := bstep (se 3 (by rfl) ⟨563405, by rfl⟩ : syracuseStep 3004829 = 1126811) B1126811
theorem B1333703 : Blo 888571 1333703 := bstep (se 1 (by rfl) ⟨1000277, by rfl⟩ : syracuseStep 1333703 = 2000555) B2000555
theorem B1333919 : Blo 888571 1333919 := bstep (se 1 (by rfl) ⟨1000439, by rfl⟩ : syracuseStep 1333919 = 2000879) B2000879
theorem B1334063 : Blo 888571 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B2251577 : Blo 888571 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B1334153 : Blo 888571 1334153 := bstep (se 2 (by rfl) ⟨500307, by rfl⟩ : syracuseStep 1334153 = 1000615) B1000615
theorem B13687703 : Blo 888571 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B1334183 : Blo 888571 1334183 := bstep (se 1 (by rfl) ⟨1000637, by rfl⟩ : syracuseStep 1334183 = 2001275) B2001275
theorem B1334363 : Blo 888571 1334363 := bstep (se 1 (by rfl) ⟨1000772, by rfl⟩ : syracuseStep 1334363 = 2001545) B2001545
theorem B3005531 : Blo 888571 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B1334555 : Blo 888571 1334555 := bstep (se 1 (by rfl) ⟨1000916, by rfl⟩ : syracuseStep 1334555 = 2001833) B2001833
theorem B5070559 : Blo 888571 5070559 := bstep (se 1 (by rfl) ⟨3802919, by rfl⟩ : syracuseStep 5070559 = 7605839) B7605839
theorem B1335023 : Blo 888571 1335023 := bstep (se 1 (by rfl) ⟨1001267, by rfl⟩ : syracuseStep 1335023 = 2002535) B2002535
theorem B4284265 : Blo 888571 4284265 := bstep (se 2 (by rfl) ⟨1606599, by rfl⟩ : syracuseStep 4284265 = 3213199) B3213199
theorem B2252711 : Blo 888571 2252711 := bstep (se 1 (by rfl) ⟨1689533, by rfl⟩ : syracuseStep 2252711 = 3379067) B3379067
theorem B1335209 : Blo 888571 1335209 := bstep (se 2 (by rfl) ⟨500703, by rfl⟩ : syracuseStep 1335209 = 1001407) B1001407
theorem B1335359 : Blo 888571 1335359 := bstep (se 1 (by rfl) ⟨1001519, by rfl⟩ : syracuseStep 1335359 = 2003039) B2003039
theorem B1335593 : Blo 888571 1335593 := bstep (se 2 (by rfl) ⟨500847, by rfl⟩ : syracuseStep 1335593 = 1001695) B1001695
theorem B1335863 : Blo 888571 1335863 := bstep (se 1 (by rfl) ⟨1001897, by rfl⟩ : syracuseStep 1335863 = 2003795) B2003795
theorem B1270505 : Blo 888571 1270505 := bstep (se 2 (by rfl) ⟨476439, by rfl⟩ : syracuseStep 1270505 = 952879) B952879
theorem B1336223 : Blo 888571 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B5072017 : Blo 888571 5072017 := bstep (se 2 (by rfl) ⟨1902006, by rfl⟩ : syracuseStep 5072017 = 3804013) B3804013
theorem B1336511 : Blo 888571 1336511 := bstep (se 1 (by rfl) ⟨1002383, by rfl⟩ : syracuseStep 1336511 = 2004767) B2004767
theorem B12346663 : Blo 888571 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1500457 : Blo 888571 1500457 := bstep (se 2 (by rfl) ⟨562671, by rfl⟩ : syracuseStep 1500457 = 1125343) B1125343
theorem B1336655 : Blo 888571 1336655 := bstep (se 1 (by rfl) ⟨1002491, by rfl⟩ : syracuseStep 1336655 = 2004983) B2004983
theorem B1336745 : Blo 888571 1336745 := bstep (se 2 (by rfl) ⟨501279, by rfl⟩ : syracuseStep 1336745 = 1002559) B1002559
theorem B1500727 : Blo 888571 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B1205815 : Blo 888571 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B1336895 : Blo 888571 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B2254655 : Blo 888571 2254655 := bstep (se 1 (by rfl) ⟨1690991, by rfl⟩ : syracuseStep 2254655 = 3381983) B3381983
theorem B2254675 : Blo 888571 2254675 := bstep (se 1 (by rfl) ⟨1691006, by rfl⟩ : syracuseStep 2254675 = 3382013) B3382013
theorem B3008393 : Blo 888571 3008393 := bstep (se 2 (by rfl) ⟨1128147, by rfl⟩ : syracuseStep 3008393 = 2256295) B2256295
theorem B1337255 : Blo 888571 1337255 := bstep (se 1 (by rfl) ⟨1002941, by rfl⟩ : syracuseStep 1337255 = 2005883) B2005883
theorem B9136091 : Blo 888571 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B1337375 : Blo 888571 1337375 := bstep (se 1 (by rfl) ⟨1003031, by rfl⟩ : syracuseStep 1337375 = 2006063) B2006063
theorem B9136415 : Blo 888571 9136415 := bstep (se 1 (by rfl) ⟨6852311, by rfl⟩ : syracuseStep 9136415 = 13704623) B13704623
theorem B1337831 : Blo 888571 1337831 := bstep (se 1 (by rfl) ⟨1003373, by rfl⟩ : syracuseStep 1337831 = 2006747) B2006747
theorem B9628217 : Blo 888571 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B1338011 : Blo 888571 1338011 := bstep (se 1 (by rfl) ⟨1003508, by rfl⟩ : syracuseStep 1338011 = 2007017) B2007017
theorem B1338233 : Blo 888571 1338233 := bstep (se 2 (by rfl) ⟨501837, by rfl⟩ : syracuseStep 1338233 = 1003675) B1003675
theorem B1141627 : Blo 888571 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B6777755 : Blo 888571 6777755 := bstep (se 1 (by rfl) ⟨5083316, by rfl⟩ : syracuseStep 6777755 = 10166633) B10166633
theorem B1338479 : Blo 888571 1338479 := bstep (se 1 (by rfl) ⟨1003859, by rfl⟩ : syracuseStep 1338479 = 2007719) B2007719
theorem B32500939 : Blo 888571 32500939 := bstep (se 1 (by rfl) ⟨24375704, by rfl⟩ : syracuseStep 32500939 = 48751409) B48751409
theorem B1338575 : Blo 888571 1338575 := bstep (se 1 (by rfl) ⟨1003931, by rfl⟩ : syracuseStep 1338575 = 2007863) B2007863
theorem B1338695 : Blo 888571 1338695 := bstep (se 1 (by rfl) ⟨1004021, by rfl⟩ : syracuseStep 1338695 = 2008043) B2008043
theorem B4943759 : Blo 888571 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B1503407 : Blo 888571 1503407 := bstep (se 1 (by rfl) ⟨1127555, by rfl⟩ : syracuseStep 1503407 = 2255111) B2255111
theorem B10121435 : Blo 888571 10121435 := bstep (se 1 (by rfl) ⟨7591076, by rfl⟩ : syracuseStep 10121435 = 15182153) B15182153
theorem B3010985 : Blo 888571 3010985 := bstep (se 2 (by rfl) ⟨1129119, by rfl⟩ : syracuseStep 3010985 = 2258239) B2258239
theorem B11399737 : Blo 888571 11399737 := bstep (se 2 (by rfl) ⟨4274901, by rfl⟩ : syracuseStep 11399737 = 8549803) B8549803
theorem B5698127 : Blo 888571 5698127 := bstep (se 1 (by rfl) ⟨4273595, by rfl⟩ : syracuseStep 5698127 = 8547191) B8547191
theorem B11400101 : Blo 888571 11400101 := bstep (se 4 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 11400101 = 2137519) B2137519
theorem B3011849 : Blo 888571 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B5076391 : Blo 888571 5076391 := bstep (se 1 (by rfl) ⟨3807293, by rfl⟩ : syracuseStep 5076391 = 7614587) B7614587
theorem B2848807 : Blo 888571 2848807 := bstep (se 1 (by rfl) ⟨2136605, by rfl⟩ : syracuseStep 2848807 = 4273211) B4273211
theorem B2750603 : Blo 888571 2750603 := bstep (se 1 (by rfl) ⟨2062952, by rfl⟩ : syracuseStep 2750603 = 4125905) B4125905
theorem B5699767 : Blo 888571 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B1505695 : Blo 888571 1505695 := bstep (se 1 (by rfl) ⟨1129271, by rfl⟩ : syracuseStep 1505695 = 2258543) B2258543
theorem B3801401 : Blo 888571 3801401 := bstep (se 2 (by rfl) ⟨1425525, by rfl⟩ : syracuseStep 3801401 = 2851051) B2851051
theorem B6423425 : Blo 888571 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B1901819 : Blo 888571 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B2000609 : Blo 888571 2000609 := bstep (se 2 (by rfl) ⟨750228, by rfl⟩ : syracuseStep 2000609 = 1500457) B1500457
theorem B29329249 : Blo 888571 29329249 := bstep (se 2 (by rfl) ⟨10998468, by rfl⟩ : syracuseStep 29329249 = 21996937) B21996937
theorem B2000969 : Blo 888571 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B1607753 : Blo 888571 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B3377335 : Blo 888571 3377335 := bstep (se 1 (by rfl) ⟨2533001, by rfl⟩ : syracuseStep 3377335 = 5066003) B5066003
theorem B3803399 : Blo 888571 3803399 := bstep (se 1 (by rfl) ⟨2852549, by rfl⟩ : syracuseStep 3803399 = 5705099) B5705099
theorem B6753455 : Blo 888571 6753455 := bstep (se 1 (by rfl) ⟨5065091, by rfl⟩ : syracuseStep 6753455 = 10130183) B10130183
theorem B3608185 : Blo 888571 3608185 := bstep (se 2 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 3608185 = 2706139) B2706139
theorem B888603 : Blo 888571 888603 := bstep (se 1 (by rfl) ⟨666452, by rfl⟩ : syracuseStep 888603 = 1332905) B1332905
theorem B2002715 : Blo 888571 2002715 := bstep (se 1 (by rfl) ⟨1502036, by rfl⟩ : syracuseStep 2002715 = 3004073) B3004073
theorem B888607 : Blo 888571 888607 := bstep (se 1 (by rfl) ⟨666455, by rfl⟩ : syracuseStep 888607 = 1332911) B1332911
theorem B888687 : Blo 888571 888687 := bstep (se 1 (by rfl) ⟨666515, by rfl⟩ : syracuseStep 888687 = 1333031) B1333031
theorem B2002859 : Blo 888571 2002859 := bstep (se 1 (by rfl) ⟨1502144, by rfl⟩ : syracuseStep 2002859 = 3004289) B3004289
theorem B888859 : Blo 888571 888859 := bstep (se 1 (by rfl) ⟨666644, by rfl⟩ : syracuseStep 888859 = 1333289) B1333289
theorem B888879 : Blo 888571 888879 := bstep (se 1 (by rfl) ⟨666659, by rfl⟩ : syracuseStep 888879 = 1333319) B1333319
theorem B889087 : Blo 888571 889087 := bstep (se 1 (by rfl) ⟨666815, by rfl⟩ : syracuseStep 889087 = 1333631) B1333631
theorem B2003219 : Blo 888571 2003219 := bstep (se 1 (by rfl) ⟨1502414, by rfl⟩ : syracuseStep 2003219 = 3004829) B3004829
theorem B889135 : Blo 888571 889135 := bstep (se 1 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 889135 = 1333703) B1333703
theorem B889279 : Blo 888571 889279 := bstep (se 1 (by rfl) ⟨666959, by rfl⟩ : syracuseStep 889279 = 1333919) B1333919
theorem B889375 : Blo 888571 889375 := bstep (se 1 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 889375 = 1334063) B1334063
theorem B889435 : Blo 888571 889435 := bstep (se 1 (by rfl) ⟨667076, by rfl⟩ : syracuseStep 889435 = 1334153) B1334153
theorem B889455 : Blo 888571 889455 := bstep (se 1 (by rfl) ⟨667091, by rfl⟩ : syracuseStep 889455 = 1334183) B1334183
theorem B889575 : Blo 888571 889575 := bstep (se 1 (by rfl) ⟨667181, by rfl⟩ : syracuseStep 889575 = 1334363) B1334363
theorem B2003687 : Blo 888571 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B889703 : Blo 888571 889703 := bstep (se 1 (by rfl) ⟨667277, by rfl⟩ : syracuseStep 889703 = 1334555) B1334555
theorem B890015 : Blo 888571 890015 := bstep (se 1 (by rfl) ⟨667511, by rfl⟩ : syracuseStep 890015 = 1335023) B1335023
theorem B890139 : Blo 888571 890139 := bstep (se 1 (by rfl) ⟨667604, by rfl⟩ : syracuseStep 890139 = 1335209) B1335209
theorem B890239 : Blo 888571 890239 := bstep (se 1 (by rfl) ⟨667679, by rfl⟩ : syracuseStep 890239 = 1335359) B1335359
theorem B890395 : Blo 888571 890395 := bstep (se 1 (by rfl) ⟨667796, by rfl⟩ : syracuseStep 890395 = 1335593) B1335593
theorem B3806783 : Blo 888571 3806783 := bstep (se 1 (by rfl) ⟨2855087, by rfl⟩ : syracuseStep 3806783 = 5710175) B5710175
theorem B890575 : Blo 888571 890575 := bstep (se 1 (by rfl) ⟨667931, by rfl⟩ : syracuseStep 890575 = 1335863) B1335863
theorem B12818249 : Blo 888571 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B890815 : Blo 888571 890815 := bstep (se 1 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 890815 = 1336223) B1336223
theorem B6756371 : Blo 888571 6756371 := bstep (se 1 (by rfl) ⟨5067278, by rfl⟩ : syracuseStep 6756371 = 10134557) B10134557
theorem B891007 : Blo 888571 891007 := bstep (se 1 (by rfl) ⟨668255, by rfl⟩ : syracuseStep 891007 = 1336511) B1336511
theorem B17373361 : Blo 888571 17373361 := bstep (se 2 (by rfl) ⟨6515010, by rfl⟩ : syracuseStep 17373361 = 13030021) B13030021
theorem B891103 : Blo 888571 891103 := bstep (se 1 (by rfl) ⟨668327, by rfl⟩ : syracuseStep 891103 = 1336655) B1336655
theorem B891163 : Blo 888571 891163 := bstep (se 1 (by rfl) ⟨668372, by rfl⟩ : syracuseStep 891163 = 1336745) B1336745
theorem B7215455 : Blo 888571 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B891263 : Blo 888571 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B2005595 : Blo 888571 2005595 := bstep (se 1 (by rfl) ⟨1504196, by rfl⟩ : syracuseStep 2005595 = 3008393) B3008393
theorem B891503 : Blo 888571 891503 := bstep (se 1 (by rfl) ⟨668627, by rfl⟩ : syracuseStep 891503 = 1337255) B1337255
theorem B891583 : Blo 888571 891583 := bstep (se 1 (by rfl) ⟨668687, by rfl⟩ : syracuseStep 891583 = 1337375) B1337375
theorem B891887 : Blo 888571 891887 := bstep (se 1 (by rfl) ⟨668915, by rfl⟩ : syracuseStep 891887 = 1337831) B1337831
theorem B892007 : Blo 888571 892007 := bstep (se 1 (by rfl) ⟨669005, by rfl⟩ : syracuseStep 892007 = 1338011) B1338011
theorem B892155 : Blo 888571 892155 := bstep (se 1 (by rfl) ⟨669116, by rfl⟩ : syracuseStep 892155 = 1338233) B1338233
theorem B892319 : Blo 888571 892319 := bstep (se 1 (by rfl) ⟨669239, by rfl⟩ : syracuseStep 892319 = 1338479) B1338479
theorem B892383 : Blo 888571 892383 := bstep (se 1 (by rfl) ⟨669287, by rfl⟩ : syracuseStep 892383 = 1338575) B1338575
theorem B892463 : Blo 888571 892463 := bstep (se 1 (by rfl) ⟨669347, by rfl⟩ : syracuseStep 892463 = 1338695) B1338695
theorem B2007323 : Blo 888571 2007323 := bstep (se 1 (by rfl) ⟨1505492, by rfl⟩ : syracuseStep 2007323 = 3010985) B3010985
theorem B2007593 : Blo 888571 2007593 := bstep (se 2 (by rfl) ⟨752847, by rfl⟩ : syracuseStep 2007593 = 1505695) B1505695
theorem B12853889 : Blo 888571 12853889 := bstep (se 2 (by rfl) ⟨4820208, by rfl⟩ : syracuseStep 12853889 = 9640417) B9640417
theorem B2007899 : Blo 888571 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B9741341 : Blo 888571 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B24323267 : Blo 888571 24323267 := bstep (se 1 (by rfl) ⟨18242450, by rfl⟩ : syracuseStep 24323267 = 36484901) B36484901
theorem B7612127 : Blo 888571 7612127 := bstep (se 1 (by rfl) ⟨5709095, by rfl⟩ : syracuseStep 7612127 = 11418191) B11418191
theorem B49424363 : Blo 888571 49424363 := bstep (se 1 (by rfl) ⟨37068272, by rfl⟩ : syracuseStep 49424363 = 74136545) B74136545
theorem B10823959 : Blo 888571 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B6760745 : Blo 888571 6760745 := bstep (se 2 (by rfl) ⟨2535279, by rfl⟩ : syracuseStep 6760745 = 5070559) B5070559
theorem B13183357 : Blo 888571 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B5712353 : Blo 888571 5712353 := bstep (se 2 (by rfl) ⟨2142132, by rfl⟩ : syracuseStep 5712353 = 4284265) B4284265
theorem B10299899 : Blo 888571 10299899 := bstep (se 1 (by rfl) ⟨7724924, by rfl⟩ : syracuseStep 10299899 = 15449849) B15449849
theorem B1125019 : Blo 888571 1125019 := bstep (se 1 (by rfl) ⟨843764, by rfl⟩ : syracuseStep 1125019 = 1687529) B1687529
theorem B3615677 : Blo 888571 3615677 := bstep (se 3 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 3615677 = 1355879) B1355879
theorem B6859885 : Blo 888571 6859885 := bstep (se 3 (by rfl) ⟨1286228, by rfl⟩ : syracuseStep 6859885 = 2572457) B2572457
theorem B3386555 : Blo 888571 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B5418191 : Blo 888571 5418191 := bstep (se 1 (by rfl) ⟨4063643, by rfl⟩ : syracuseStep 5418191 = 8127287) B8127287
theorem B1125991 : Blo 888571 1125991 := bstep (se 1 (by rfl) ⟨844493, by rfl⟩ : syracuseStep 1125991 = 1688987) B1688987
theorem B3387055 : Blo 888571 3387055 := bstep (se 1 (by rfl) ⟨2540291, by rfl⟩ : syracuseStep 3387055 = 5080583) B5080583
theorem B6762689 : Blo 888571 6762689 := bstep (se 2 (by rfl) ⟨2536008, by rfl⟩ : syracuseStep 6762689 = 5072017) B5072017
theorem B16462217 : Blo 888571 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B3388013 : Blo 888571 3388013 := bstep (se 3 (by rfl) ⟨635252, by rfl⟩ : syracuseStep 3388013 = 1270505) B1270505
theorem B20591495 : Blo 888571 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B3388499 : Blo 888571 3388499 := bstep (se 1 (by rfl) ⟨2541374, by rfl⟩ : syracuseStep 3388499 = 5082749) B5082749
theorem B1127783 : Blo 888571 1127783 := bstep (se 1 (by rfl) ⟨845837, by rfl⟩ : syracuseStep 1127783 = 1691675) B1691675
theorem B5716271 : Blo 888571 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B1522169 : Blo 888571 1522169 := bstep (se 2 (by rfl) ⟨570813, by rfl⟩ : syracuseStep 1522169 = 1141627) B1141627
theorem B43334585 : Blo 888571 43334585 := bstep (se 2 (by rfl) ⟨16250469, by rfl⟩ : syracuseStep 43334585 = 32500939) B32500939
theorem B98614259 : Blo 888571 98614259 := bstep (se 1 (by rfl) ⟨73960694, by rfl⟩ : syracuseStep 98614259 = 147921389) B147921389
theorem B9125135 : Blo 888571 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B5422879 : Blo 888571 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B28852361 : Blo 888571 28852361 := bstep (se 2 (by rfl) ⟨10819635, by rfl⟩ : syracuseStep 28852361 = 21639271) B21639271
theorem B1687711 : Blo 888571 1687711 := bstep (se 1 (by rfl) ⟨1265783, by rfl⟩ : syracuseStep 1687711 = 2531567) B2531567
theorem B24363773 : Blo 888571 24363773 := bstep (se 3 (by rfl) ⟨4568207, by rfl⟩ : syracuseStep 24363773 = 9136415) B9136415
theorem B1688759 : Blo 888571 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B6768521 : Blo 888571 6768521 := bstep (se 2 (by rfl) ⟨2538195, by rfl⟩ : syracuseStep 6768521 = 5076391) B5076391
theorem B3000347 : Blo 888571 3000347 := bstep (se 1 (by rfl) ⟨2250260, by rfl⟩ : syracuseStep 3000347 = 4500521) B4500521
theorem B3000509 : Blo 888571 3000509 := bstep (se 3 (by rfl) ⟨562595, by rfl⟩ : syracuseStep 3000509 = 1125191) B1125191
theorem B24365299 : Blo 888571 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B3000617 : Blo 888571 3000617 := bstep (se 2 (by rfl) ⟨1125231, by rfl⟩ : syracuseStep 3000617 = 2250463) B2250463
theorem B1002271 : Blo 888571 1002271 := bstep (se 1 (by rfl) ⟨751703, by rfl⟩ : syracuseStep 1002271 = 1503407) B1503407
theorem B4508783 : Blo 888571 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B3002507 : Blo 888571 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B4510403 : Blo 888571 4510403 := bstep (se 1 (by rfl) ⟨3382802, by rfl⟩ : syracuseStep 4510403 = 6765605) B6765605
theorem B3003695 : Blo 888571 3003695 := bstep (se 1 (by rfl) ⟨2252771, by rfl⟩ : syracuseStep 3003695 = 4505543) B4505543
theorem B3004019 : Blo 888571 3004019 := bstep (se 1 (by rfl) ⟨2253014, by rfl⟩ : syracuseStep 3004019 = 4506029) B4506029
theorem B1955519 : Blo 888571 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B3856091 : Blo 888571 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B4872059 : Blo 888571 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B1333295 : Blo 888571 1333295 := bstep (se 1 (by rfl) ⟨999971, by rfl⟩ : syracuseStep 1333295 = 1999943) B1999943
theorem B1333415 : Blo 888571 1333415 := bstep (se 1 (by rfl) ⟨1000061, by rfl⟩ : syracuseStep 1333415 = 2000123) B2000123
theorem B1333583 : Blo 888571 1333583 := bstep (se 1 (by rfl) ⟨1000187, by rfl⟩ : syracuseStep 1333583 = 2000375) B2000375
theorem B2251223 : Blo 888571 2251223 := bstep (se 1 (by rfl) ⟨1688417, by rfl⟩ : syracuseStep 2251223 = 3376835) B3376835
theorem B3005099 : Blo 888571 3005099 := bstep (se 1 (by rfl) ⟨2253824, by rfl⟩ : syracuseStep 3005099 = 4507649) B4507649
theorem B4512509 : Blo 888571 4512509 := bstep (se 3 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 4512509 = 1692191) B1692191
theorem B7232327 : Blo 888571 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B1334303 : Blo 888571 1334303 := bstep (se 1 (by rfl) ⟨1000727, by rfl⟩ : syracuseStep 1334303 = 2001455) B2001455
theorem B1269047 : Blo 888571 1269047 := bstep (se 1 (by rfl) ⟨951785, by rfl⟩ : syracuseStep 1269047 = 1903571) B1903571
theorem B1334735 : Blo 888571 1334735 := bstep (se 1 (by rfl) ⟨1001051, by rfl⟩ : syracuseStep 1334735 = 2002103) B2002103
theorem B3006233 : Blo 888571 3006233 := bstep (se 2 (by rfl) ⟨1127337, by rfl⟩ : syracuseStep 3006233 = 2254675) B2254675
theorem B3006287 : Blo 888571 3006287 := bstep (se 1 (by rfl) ⟨2254715, by rfl⟩ : syracuseStep 3006287 = 4509431) B4509431
theorem B4808573 : Blo 888571 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B2253035 : Blo 888571 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B1336271 : Blo 888571 1336271 := bstep (se 1 (by rfl) ⟨1002203, by rfl⟩ : syracuseStep 1336271 = 2004407) B2004407
theorem B1336319 : Blo 888571 1336319 := bstep (se 1 (by rfl) ⟨1002239, by rfl⟩ : syracuseStep 1336319 = 2004479) B2004479
theorem B2057257 : Blo 888571 2057257 := bstep (se 2 (by rfl) ⟨771471, by rfl⟩ : syracuseStep 2057257 = 1542943) B1542943
theorem B1336391 : Blo 888571 1336391 := bstep (se 1 (by rfl) ⟨1002293, by rfl⟩ : syracuseStep 1336391 = 2004587) B2004587
theorem B1336571 : Blo 888571 1336571 := bstep (se 1 (by rfl) ⟨1002428, by rfl⟩ : syracuseStep 1336571 = 2004857) B2004857
theorem B1337087 : Blo 888571 1337087 := bstep (se 1 (by rfl) ⟨1002815, by rfl⟩ : syracuseStep 1337087 = 2005631) B2005631
theorem B1337159 : Blo 888571 1337159 := bstep (se 1 (by rfl) ⟨1002869, by rfl⟩ : syracuseStep 1337159 = 2005739) B2005739
theorem B1501051 : Blo 888571 1501051 := bstep (se 1 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 1501051 = 2251577) B2251577
theorem B1337339 : Blo 888571 1337339 := bstep (se 1 (by rfl) ⟨1003004, by rfl⟩ : syracuseStep 1337339 = 2006009) B2006009
theorem B1337399 : Blo 888571 1337399 := bstep (se 1 (by rfl) ⟨1003049, by rfl⟩ : syracuseStep 1337399 = 2006099) B2006099
theorem B1337519 : Blo 888571 1337519 := bstep (se 1 (by rfl) ⟨1003139, by rfl⟩ : syracuseStep 1337519 = 2006279) B2006279
theorem B1337759 : Blo 888571 1337759 := bstep (se 1 (by rfl) ⟨1003319, by rfl⟩ : syracuseStep 1337759 = 2006639) B2006639
theorem B2255273 : Blo 888571 2255273 := bstep (se 2 (by rfl) ⟨845727, by rfl⟩ : syracuseStep 2255273 = 1691455) B1691455
theorem B1337951 : Blo 888571 1337951 := bstep (se 1 (by rfl) ⟨1003463, by rfl⟩ : syracuseStep 1337951 = 2006927) B2006927
theorem B1501807 : Blo 888571 1501807 := bstep (se 1 (by rfl) ⟨1126355, by rfl⟩ : syracuseStep 1501807 = 2252711) B2252711
theorem B1338023 : Blo 888571 1338023 := bstep (se 1 (by rfl) ⟨1003517, by rfl⟩ : syracuseStep 1338023 = 2007035) B2007035
theorem B1338089 : Blo 888571 1338089 := bstep (se 2 (by rfl) ⟨501783, by rfl⟩ : syracuseStep 1338089 = 1003567) B1003567
theorem B2255647 : Blo 888571 2255647 := bstep (se 1 (by rfl) ⟨1691735, by rfl⟩ : syracuseStep 2255647 = 3383471) B3383471
theorem B1338143 : Blo 888571 1338143 := bstep (se 1 (by rfl) ⟨1003607, by rfl⟩ : syracuseStep 1338143 = 2007215) B2007215
theorem B1338311 : Blo 888571 1338311 := bstep (se 1 (by rfl) ⟨1003733, by rfl⟩ : syracuseStep 1338311 = 2007467) B2007467
theorem B7334941 : Blo 888571 7334941 := bstep (se 3 (by rfl) ⟨1375301, by rfl⟩ : syracuseStep 7334941 = 2750603) B2750603
theorem B1338431 : Blo 888571 1338431 := bstep (se 1 (by rfl) ⟨1003823, by rfl⟩ : syracuseStep 1338431 = 2007647) B2007647
theorem B1338623 : Blo 888571 1338623 := bstep (se 1 (by rfl) ⟨1003967, by rfl⟩ : syracuseStep 1338623 = 2007935) B2007935
theorem B1338671 : Blo 888571 1338671 := bstep (se 1 (by rfl) ⟨1004003, by rfl⟩ : syracuseStep 1338671 = 2008007) B2008007
theorem B15199649 : Blo 888571 15199649 := bstep (se 2 (by rfl) ⟨5699868, by rfl⟩ : syracuseStep 15199649 = 11399737) B11399737
theorem B1338857 : Blo 888571 1338857 := bstep (se 2 (by rfl) ⟨502071, by rfl⟩ : syracuseStep 1338857 = 1004143) B1004143
theorem B5074433 : Blo 888571 5074433 := bstep (se 2 (by rfl) ⟨1902912, by rfl⟩ : syracuseStep 5074433 = 3805825) B3805825
theorem B1503103 : Blo 888571 1503103 := bstep (se 1 (by rfl) ⟨1127327, by rfl⟩ : syracuseStep 1503103 = 2254655) B2254655
theorem B6090727 : Blo 888571 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B2846951 : Blo 888571 2846951 := bstep (se 1 (by rfl) ⟨2135213, by rfl⟩ : syracuseStep 2846951 = 4270427) B4270427
theorem B6418811 : Blo 888571 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B23163337 : Blo 888571 23163337 := bstep (se 2 (by rfl) ⟨8686251, by rfl⟩ : syracuseStep 23163337 = 17372503) B17372503
theorem B5698025 : Blo 888571 5698025 := bstep (se 2 (by rfl) ⟨2136759, by rfl⟩ : syracuseStep 5698025 = 4273519) B4273519
theorem B4518503 : Blo 888571 4518503 := bstep (se 1 (by rfl) ⟨3388877, by rfl⟩ : syracuseStep 4518503 = 6777755) B6777755
theorem B3798409 : Blo 888571 3798409 := bstep (se 2 (by rfl) ⟨1424403, by rfl⟩ : syracuseStep 3798409 = 2848807) B2848807
theorem B6747623 : Blo 888571 6747623 := bstep (se 1 (by rfl) ⟨5060717, by rfl⟩ : syracuseStep 6747623 = 10121435) B10121435
theorem B7599689 : Blo 888571 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B3798751 : Blo 888571 3798751 := bstep (se 1 (by rfl) ⟨2849063, by rfl⟩ : syracuseStep 3798751 = 5698127) B5698127
theorem B29325025 : Blo 888571 29325025 := bstep (se 2 (by rfl) ⟨10996884, by rfl⟩ : syracuseStep 29325025 = 21993769) B21993769
theorem B7600067 : Blo 888571 7600067 := bstep (se 1 (by rfl) ⟨5700050, by rfl⟩ : syracuseStep 7600067 = 11400101) B11400101
theorem B10157885 : Blo 888571 10157885 := bstep (se 3 (by rfl) ⟨1904603, by rfl⟩ : syracuseStep 10157885 = 3809207) B3809207
theorem B19234907 : Blo 888571 19234907 := bstep (se 1 (by rfl) ⟨14426180, by rfl⟩ : syracuseStep 19234907 = 28852361) B28852361
theorem B2000231 : Blo 888571 2000231 := bstep (se 1 (by rfl) ⟨1500173, by rfl⟩ : syracuseStep 2000231 = 3000347) B3000347
theorem B2000339 : Blo 888571 2000339 := bstep (se 1 (by rfl) ⟨1500254, by rfl⟩ : syracuseStep 2000339 = 3000509) B3000509
theorem B2000411 : Blo 888571 2000411 := bstep (se 1 (by rfl) ⟨1500308, by rfl⟩ : syracuseStep 2000411 = 3000617) B3000617
theorem B2001401 : Blo 888571 2001401 := bstep (se 2 (by rfl) ⟨750525, by rfl⟩ : syracuseStep 2001401 = 1501051) B1501051
theorem B2001671 : Blo 888571 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B2002409 : Blo 888571 2002409 := bstep (se 2 (by rfl) ⟨750903, by rfl⟩ : syracuseStep 2002409 = 1501807) B1501807
theorem B2002463 : Blo 888571 2002463 := bstep (se 1 (by rfl) ⟨1501847, by rfl⟩ : syracuseStep 2002463 = 3003695) B3003695
theorem B2002679 : Blo 888571 2002679 := bstep (se 1 (by rfl) ⟨1502009, by rfl⟩ : syracuseStep 2002679 = 3004019) B3004019
theorem B3248039 : Blo 888571 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B888863 : Blo 888571 888863 := bstep (se 1 (by rfl) ⟨666647, by rfl⟩ : syracuseStep 888863 = 1333295) B1333295
theorem B888943 : Blo 888571 888943 := bstep (se 1 (by rfl) ⟨666707, by rfl⟩ : syracuseStep 888943 = 1333415) B1333415
theorem B9146513 : Blo 888571 9146513 := bstep (se 2 (by rfl) ⟨3429942, by rfl⟩ : syracuseStep 9146513 = 6859885) B6859885
theorem B889055 : Blo 888571 889055 := bstep (se 1 (by rfl) ⟨666791, by rfl⟩ : syracuseStep 889055 = 1333583) B1333583
theorem B2003399 : Blo 888571 2003399 := bstep (se 1 (by rfl) ⟨1502549, by rfl⟩ : syracuseStep 2003399 = 3005099) B3005099
theorem B4821551 : Blo 888571 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B889535 : Blo 888571 889535 := bstep (se 1 (by rfl) ⟨667151, by rfl⟩ : syracuseStep 889535 = 1334303) B1334303
theorem B889823 : Blo 888571 889823 := bstep (se 1 (by rfl) ⟨667367, by rfl⟩ : syracuseStep 889823 = 1334735) B1334735
theorem B2004137 : Blo 888571 2004137 := bstep (se 2 (by rfl) ⟨751551, by rfl⟩ : syracuseStep 2004137 = 1503103) B1503103
theorem B2004155 : Blo 888571 2004155 := bstep (se 1 (by rfl) ⟨1503116, by rfl⟩ : syracuseStep 2004155 = 3006233) B3006233
theorem B2004191 : Blo 888571 2004191 := bstep (se 1 (by rfl) ⟨1503143, by rfl⟩ : syracuseStep 2004191 = 3006287) B3006287
theorem B890847 : Blo 888571 890847 := bstep (se 1 (by rfl) ⟨668135, by rfl⟩ : syracuseStep 890847 = 1336271) B1336271
theorem B890879 : Blo 888571 890879 := bstep (se 1 (by rfl) ⟨668159, by rfl⟩ : syracuseStep 890879 = 1336319) B1336319
theorem B890927 : Blo 888571 890927 := bstep (se 1 (by rfl) ⟨668195, by rfl⟩ : syracuseStep 890927 = 1336391) B1336391
theorem B15243389 : Blo 888571 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B891047 : Blo 888571 891047 := bstep (se 1 (by rfl) ⟨668285, by rfl⟩ : syracuseStep 891047 = 1336571) B1336571
theorem B891391 : Blo 888571 891391 := bstep (se 1 (by rfl) ⟨668543, by rfl⟩ : syracuseStep 891391 = 1337087) B1337087
theorem B891439 : Blo 888571 891439 := bstep (se 1 (by rfl) ⟨668579, by rfl⟩ : syracuseStep 891439 = 1337159) B1337159
theorem B27466397 : Blo 888571 27466397 := bstep (se 3 (by rfl) ⟨5149949, by rfl⟩ : syracuseStep 27466397 = 10299899) B10299899
theorem B891559 : Blo 888571 891559 := bstep (se 1 (by rfl) ⟨668669, by rfl⟩ : syracuseStep 891559 = 1337339) B1337339
theorem B891599 : Blo 888571 891599 := bstep (se 1 (by rfl) ⟨668699, by rfl⟩ : syracuseStep 891599 = 1337399) B1337399
theorem B891679 : Blo 888571 891679 := bstep (se 1 (by rfl) ⟨668759, by rfl⟩ : syracuseStep 891679 = 1337519) B1337519
theorem B891839 : Blo 888571 891839 := bstep (se 1 (by rfl) ⟨668879, by rfl⟩ : syracuseStep 891839 = 1337759) B1337759
theorem B3808235 : Blo 888571 3808235 := bstep (se 1 (by rfl) ⟨2856176, by rfl⟩ : syracuseStep 3808235 = 5712353) B5712353
theorem B891967 : Blo 888571 891967 := bstep (se 1 (by rfl) ⟨668975, by rfl⟩ : syracuseStep 891967 = 1337951) B1337951
theorem B892015 : Blo 888571 892015 := bstep (se 1 (by rfl) ⟨669011, by rfl⟩ : syracuseStep 892015 = 1338023) B1338023
theorem B892059 : Blo 888571 892059 := bstep (se 1 (by rfl) ⟨669044, by rfl⟩ : syracuseStep 892059 = 1338089) B1338089
theorem B892095 : Blo 888571 892095 := bstep (se 1 (by rfl) ⟨669071, by rfl⟩ : syracuseStep 892095 = 1338143) B1338143
theorem B892207 : Blo 888571 892207 := bstep (se 1 (by rfl) ⟨669155, by rfl⟩ : syracuseStep 892207 = 1338311) B1338311
theorem B892287 : Blo 888571 892287 := bstep (se 1 (by rfl) ⟨669215, by rfl⟩ : syracuseStep 892287 = 1338431) B1338431
theorem B3612127 : Blo 888571 3612127 := bstep (se 1 (by rfl) ⟨2709095, by rfl⟩ : syracuseStep 3612127 = 5418191) B5418191
theorem B892415 : Blo 888571 892415 := bstep (se 1 (by rfl) ⟨669311, by rfl⟩ : syracuseStep 892415 = 1338623) B1338623
theorem B892447 : Blo 888571 892447 := bstep (se 1 (by rfl) ⟨669335, by rfl⟩ : syracuseStep 892447 = 1338671) B1338671
theorem B10133099 : Blo 888571 10133099 := bstep (se 1 (by rfl) ⟨7599824, by rfl⟩ : syracuseStep 10133099 = 15199649) B15199649
theorem B39100033 : Blo 888571 39100033 := bstep (se 2 (by rfl) ⟨14662512, by rfl⟩ : syracuseStep 39100033 = 29325025) B29325025
theorem B892571 : Blo 888571 892571 := bstep (se 1 (by rfl) ⟨669428, by rfl⟩ : syracuseStep 892571 = 1338857) B1338857
theorem B3382955 : Blo 888571 3382955 := bstep (se 1 (by rfl) ⟨2537216, by rfl⟩ : syracuseStep 3382955 = 5074433) B5074433
theorem B3384125 : Blo 888571 3384125 := bstep (se 3 (by rfl) ⟨634523, by rfl⟩ : syracuseStep 3384125 = 1269047) B1269047
theorem B4498415 : Blo 888571 4498415 := bstep (se 1 (by rfl) ⟨3373811, by rfl⟩ : syracuseStep 4498415 = 6747623) B6747623
theorem B65742839 : Blo 888571 65742839 := bstep (se 1 (by rfl) ⟨49307129, by rfl⟩ : syracuseStep 65742839 = 98614259) B98614259
theorem B2534267 : Blo 888571 2534267 := bstep (se 1 (by rfl) ⟨1900700, by rfl⟩ : syracuseStep 2534267 = 3801401) B3801401
theorem B1125839 : Blo 888571 1125839 := bstep (se 1 (by rfl) ⟨844379, by rfl⟩ : syracuseStep 1125839 = 1688759) B1688759
theorem B17116829 : Blo 888571 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B2535599 : Blo 888571 2535599 := bstep (se 1 (by rfl) ⟨1901699, by rfl⟩ : syracuseStep 2535599 = 3803399) B3803399
theorem B4502303 : Blo 888571 4502303 := bstep (se 1 (by rfl) ⟨3376727, by rfl⟩ : syracuseStep 4502303 = 6753455) B6753455
theorem B39105665 : Blo 888571 39105665 := bstep (se 2 (by rfl) ⟨14664624, by rfl⟩ : syracuseStep 39105665 = 29329249) B29329249
theorem B4503113 : Blo 888571 4503113 := bstep (se 2 (by rfl) ⟨1688667, by rfl⟩ : syracuseStep 4503113 = 3377335) B3377335
theorem B32487065 : Blo 888571 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B14431945 : Blo 888571 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B17577809 : Blo 888571 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B2537855 : Blo 888571 2537855 := bstep (se 1 (by rfl) ⟨1903391, by rfl⟩ : syracuseStep 2537855 = 3806783) B3806783
theorem B4504247 : Blo 888571 4504247 := bstep (se 1 (by rfl) ⟨3378185, by rfl⟩ : syracuseStep 4504247 = 6756371) B6756371
theorem B9779921 : Blo 888571 9779921 := bstep (se 2 (by rfl) ⟨3667470, by rfl⟩ : syracuseStep 9779921 = 7334941) B7334941
theorem B8569259 : Blo 888571 8569259 := bstep (se 1 (by rfl) ⟨6426944, by rfl⟩ : syracuseStep 8569259 = 12853889) B12853889
theorem B30884449 : Blo 888571 30884449 := bstep (se 2 (by rfl) ⟨11581668, by rfl⟩ : syracuseStep 30884449 = 23163337) B23163337
theorem B32949575 : Blo 888571 32949575 := bstep (se 1 (by rfl) ⟨24712181, by rfl⟩ : syracuseStep 32949575 = 49424363) B49424363
theorem B4507163 : Blo 888571 4507163 := bstep (se 1 (by rfl) ⟨3380372, by rfl⟩ : syracuseStep 4507163 = 6760745) B6760745
theorem B5064545 : Blo 888571 5064545 := bstep (se 2 (by rfl) ⟨1899204, by rfl⟩ : syracuseStep 5064545 = 3798409) B3798409
theorem B2410451 : Blo 888571 2410451 := bstep (se 1 (by rfl) ⟨1807838, by rfl⟩ : syracuseStep 2410451 = 3615677) B3615677
theorem B5065001 : Blo 888571 5065001 := bstep (se 2 (by rfl) ⟨1899375, by rfl⟩ : syracuseStep 5065001 = 3798751) B3798751
theorem B4508459 : Blo 888571 4508459 := bstep (se 1 (by rfl) ⟨3381344, by rfl⟩ : syracuseStep 4508459 = 6762689) B6762689
theorem B5066459 : Blo 888571 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B5066711 : Blo 888571 5066711 := bstep (se 1 (by rfl) ⟨3800033, by rfl⟩ : syracuseStep 5066711 = 7600067) B7600067
theorem B28889723 : Blo 888571 28889723 := bstep (se 1 (by rfl) ⟨21667292, by rfl⟩ : syracuseStep 28889723 = 43334585) B43334585
theorem B6083423 : Blo 888571 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B7230505 : Blo 888571 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B6771923 : Blo 888571 6771923 := bstep (se 1 (by rfl) ⟨5078942, by rfl⟩ : syracuseStep 6771923 = 10157885) B10157885
theorem B2250281 : Blo 888571 2250281 := bstep (se 2 (by rfl) ⟨843855, by rfl⟩ : syracuseStep 2250281 = 1687711) B1687711
theorem B16242515 : Blo 888571 16242515 := bstep (se 1 (by rfl) ⟨12181886, by rfl⟩ : syracuseStep 16242515 = 24363773) B24363773
theorem B4282283 : Blo 888571 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B1333739 : Blo 888571 1333739 := bstep (se 1 (by rfl) ⟨1000304, by rfl⟩ : syracuseStep 1333739 = 2000609) B2000609
theorem B4512347 : Blo 888571 4512347 := bstep (se 1 (by rfl) ⟨3384260, by rfl⟩ : syracuseStep 4512347 = 6768521) B6768521
theorem B1333979 : Blo 888571 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B1071835 : Blo 888571 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B3005855 : Blo 888571 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B1335143 : Blo 888571 1335143 := bstep (se 1 (by rfl) ⟨1001357, by rfl⟩ : syracuseStep 1335143 = 2002715) B2002715
theorem B1335239 : Blo 888571 1335239 := bstep (se 1 (by rfl) ⟨1001429, by rfl⟩ : syracuseStep 1335239 = 2002859) B2002859
theorem B25976909 : Blo 888571 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B1335479 : Blo 888571 1335479 := bstep (se 1 (by rfl) ⟨1001609, by rfl⟩ : syracuseStep 1335479 = 2003219) B2003219
theorem B3006935 : Blo 888571 3006935 := bstep (se 1 (by rfl) ⟨2255201, by rfl⟩ : syracuseStep 3006935 = 4510403) B4510403
theorem B1335791 : Blo 888571 1335791 := bstep (se 1 (by rfl) ⟨1001843, by rfl⟩ : syracuseStep 1335791 = 2003687) B2003687
theorem B5071517 : Blo 888571 5071517 := bstep (se 3 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 5071517 = 1901819) B1901819
theorem B1500025 : Blo 888571 1500025 := bstep (se 2 (by rfl) ⟨562509, by rfl⟩ : syracuseStep 1500025 = 1125019) B1125019
theorem B3007421 : Blo 888571 3007421 := bstep (se 3 (by rfl) ⟨563891, by rfl⟩ : syracuseStep 3007421 = 1127783) B1127783
theorem B1336361 : Blo 888571 1336361 := bstep (se 2 (by rfl) ⟨501135, by rfl⟩ : syracuseStep 1336361 = 1002271) B1002271
theorem B3007529 : Blo 888571 3007529 := bstep (se 2 (by rfl) ⟨1127823, by rfl⟩ : syracuseStep 3007529 = 2255647) B2255647
theorem B1303679 : Blo 888571 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B8545499 : Blo 888571 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B4810303 : Blo 888571 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B1500815 : Blo 888571 1500815 := bstep (se 1 (by rfl) ⟨1125611, by rfl⟩ : syracuseStep 1500815 = 2251223) B2251223
theorem B1337063 : Blo 888571 1337063 := bstep (se 1 (by rfl) ⟨1002797, by rfl⟩ : syracuseStep 1337063 = 2005595) B2005595
theorem B3008339 : Blo 888571 3008339 := bstep (se 1 (by rfl) ⟨2256254, by rfl⟩ : syracuseStep 3008339 = 4512509) B4512509
theorem B10282909 : Blo 888571 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B1501321 : Blo 888571 1501321 := bstep (se 2 (by rfl) ⟨562995, by rfl⟩ : syracuseStep 1501321 = 1125991) B1125991
theorem B4810913 : Blo 888571 4810913 := bstep (se 2 (by rfl) ⟨1804092, by rfl⟩ : syracuseStep 4810913 = 3608185) B3608185
theorem B4516073 : Blo 888571 4516073 := bstep (se 2 (by rfl) ⟨1693527, by rfl⟩ : syracuseStep 4516073 = 3387055) B3387055
theorem B3205715 : Blo 888571 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B8120969 : Blo 888571 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B1502023 : Blo 888571 1502023 := bstep (se 1 (by rfl) ⟨1126517, by rfl⟩ : syracuseStep 1502023 = 2253035) B2253035
theorem B1338215 : Blo 888571 1338215 := bstep (se 1 (by rfl) ⟨1003661, by rfl⟩ : syracuseStep 1338215 = 2007323) B2007323
theorem B10972037 : Blo 888571 10972037 := bstep (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) B2057257
theorem B1338395 : Blo 888571 1338395 := bstep (se 1 (by rfl) ⟨1003796, by rfl⟩ : syracuseStep 1338395 = 2007593) B2007593
theorem B1338599 : Blo 888571 1338599 := bstep (se 1 (by rfl) ⟨1003949, by rfl⟩ : syracuseStep 1338599 = 2007899) B2007899
theorem B16215511 : Blo 888571 16215511 := bstep (se 1 (by rfl) ⟨12161633, by rfl⟩ : syracuseStep 16215511 = 24323267) B24323267
theorem B5074751 : Blo 888571 5074751 := bstep (se 1 (by rfl) ⟨3806063, by rfl⟩ : syracuseStep 5074751 = 7612127) B7612127
theorem B1503515 : Blo 888571 1503515 := bstep (se 1 (by rfl) ⟨1127636, by rfl⟩ : syracuseStep 1503515 = 2255273) B2255273
theorem B2257703 : Blo 888571 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B1897967 : Blo 888571 1897967 := bstep (se 1 (by rfl) ⟨1423475, by rfl⟩ : syracuseStep 1897967 = 2846951) B2846951
theorem B23164481 : Blo 888571 23164481 := bstep (se 2 (by rfl) ⟨8686680, by rfl⟩ : syracuseStep 23164481 = 17373361) B17373361
theorem B10974811 : Blo 888571 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B3798683 : Blo 888571 3798683 := bstep (se 1 (by rfl) ⟨2849012, by rfl⟩ : syracuseStep 3798683 = 5698025) B5698025
theorem B3012335 : Blo 888571 3012335 := bstep (se 1 (by rfl) ⟨2259251, by rfl⟩ : syracuseStep 3012335 = 4518503) B4518503
theorem B2258675 : Blo 888571 2258675 := bstep (se 1 (by rfl) ⟨1694006, by rfl⟩ : syracuseStep 2258675 = 3388013) B3388013
theorem B13727663 : Blo 888571 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B2258999 : Blo 888571 2258999 := bstep (se 1 (by rfl) ⟨1694249, by rfl⟩ : syracuseStep 2258999 = 3388499) B3388499
theorem B1014779 : Blo 888571 1014779 := bstep (se 1 (by rfl) ⟨761084, by rfl⟩ : syracuseStep 1014779 = 1522169) B1522169
theorem B69271757 : Blo 888571 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B2000033 : Blo 888571 2000033 := bstep (se 2 (by rfl) ⟨750012, by rfl⟩ : syracuseStep 2000033 = 1500025) B1500025
theorem B3376363 : Blo 888571 3376363 := bstep (se 1 (by rfl) ⟨2532272, by rfl⟩ : syracuseStep 3376363 = 5064545) B5064545
theorem B1606967 : Blo 888571 1606967 := bstep (se 1 (by rfl) ⟨1205225, by rfl⟩ : syracuseStep 1606967 = 2410451) B2410451
theorem B3376667 : Blo 888571 3376667 := bstep (se 1 (by rfl) ⟨2532500, by rfl⟩ : syracuseStep 3376667 = 5065001) B5065001
theorem B3377639 : Blo 888571 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B3377807 : Blo 888571 3377807 := bstep (se 1 (by rfl) ⟨2533355, by rfl⟩ : syracuseStep 3377807 = 5066711) B5066711
theorem B6097675 : Blo 888571 6097675 := bstep (se 1 (by rfl) ⟨4573256, by rfl⟩ : syracuseStep 6097675 = 9146513) B9146513
theorem B2001761 : Blo 888571 2001761 := bstep (se 2 (by rfl) ⟨750660, by rfl⟩ : syracuseStep 2001761 = 1501321) B1501321
theorem B3476477 : Blo 888571 3476477 := bstep (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) B1303679
theorem B3214367 : Blo 888571 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B2002697 : Blo 888571 2002697 := bstep (se 2 (by rfl) ⟨751011, by rfl⟩ : syracuseStep 2002697 = 1502023) B1502023
theorem B2854855 : Blo 888571 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B10162259 : Blo 888571 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B889159 : Blo 888571 889159 := bstep (se 1 (by rfl) ⟨666869, by rfl⟩ : syracuseStep 889159 = 1333739) B1333739
theorem B889319 : Blo 888571 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B2003903 : Blo 888571 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B6755399 : Blo 888571 6755399 := bstep (se 1 (by rfl) ⟨5066549, by rfl⟩ : syracuseStep 6755399 = 10133099) B10133099
theorem B890095 : Blo 888571 890095 := bstep (se 1 (by rfl) ⟨667571, by rfl⟩ : syracuseStep 890095 = 1335143) B1335143
theorem B890159 : Blo 888571 890159 := bstep (se 1 (by rfl) ⟨667619, by rfl⟩ : syracuseStep 890159 = 1335239) B1335239
theorem B890319 : Blo 888571 890319 := bstep (se 1 (by rfl) ⟨667739, by rfl⟩ : syracuseStep 890319 = 1335479) B1335479
theorem B2004623 : Blo 888571 2004623 := bstep (se 1 (by rfl) ⟨1503467, by rfl⟩ : syracuseStep 2004623 = 3006935) B3006935
theorem B890527 : Blo 888571 890527 := bstep (se 1 (by rfl) ⟨667895, by rfl⟩ : syracuseStep 890527 = 1335791) B1335791
theorem B3381011 : Blo 888571 3381011 := bstep (se 1 (by rfl) ⟨2535758, by rfl⟩ : syracuseStep 3381011 = 5071517) B5071517
theorem B2004947 : Blo 888571 2004947 := bstep (se 1 (by rfl) ⟨1503710, by rfl⟩ : syracuseStep 2004947 = 3007421) B3007421
theorem B890907 : Blo 888571 890907 := bstep (se 1 (by rfl) ⟨668180, by rfl⟩ : syracuseStep 890907 = 1336361) B1336361
theorem B2005019 : Blo 888571 2005019 := bstep (se 1 (by rfl) ⟨1503764, by rfl⟩ : syracuseStep 2005019 = 3007529) B3007529
theorem B891375 : Blo 888571 891375 := bstep (se 1 (by rfl) ⟨668531, by rfl⟩ : syracuseStep 891375 = 1337063) B1337063
theorem B2005559 : Blo 888571 2005559 := bstep (se 1 (by rfl) ⟨1504169, by rfl⟩ : syracuseStep 2005559 = 3008339) B3008339
theorem B9640673 : Blo 888571 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B5413979 : Blo 888571 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B892143 : Blo 888571 892143 := bstep (se 1 (by rfl) ⟨669107, by rfl⟩ : syracuseStep 892143 = 1338215) B1338215
theorem B892263 : Blo 888571 892263 := bstep (se 1 (by rfl) ⟨669197, by rfl⟩ : syracuseStep 892263 = 1338395) B1338395
theorem B892399 : Blo 888571 892399 := bstep (se 1 (by rfl) ⟨669299, by rfl⟩ : syracuseStep 892399 = 1338599) B1338599
theorem B19242593 : Blo 888571 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B11411219 : Blo 888571 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B3383167 : Blo 888571 3383167 := bstep (se 1 (by rfl) ⟨2537375, by rfl⟩ : syracuseStep 3383167 = 5074751) B5074751
theorem B15442987 : Blo 888571 15442987 := bstep (se 1 (by rfl) ⟨11582240, by rfl⟩ : syracuseStep 15442987 = 23164481) B23164481
theorem B2532455 : Blo 888571 2532455 := bstep (se 1 (by rfl) ⟨1899341, by rfl⟩ : syracuseStep 2532455 = 3798683) B3798683
theorem B2008223 : Blo 888571 2008223 := bstep (se 1 (by rfl) ⟨1506167, by rfl⟩ : syracuseStep 2008223 = 3012335) B3012335
theorem B9151775 : Blo 888571 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B8661437 : Blo 888571 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B12823271 : Blo 888571 12823271 := bstep (se 1 (by rfl) ⟨9617453, by rfl⟩ : syracuseStep 12823271 = 19234907) B19234907
theorem B5712839 : Blo 888571 5712839 := bstep (se 1 (by rfl) ⟨4284629, by rfl⟩ : syracuseStep 5712839 = 8569259) B8569259
theorem B21966383 : Blo 888571 21966383 := bstep (se 1 (by rfl) ⟨16474787, by rfl⟩ : syracuseStep 21966383 = 32949575) B32949575
theorem B13710545 : Blo 888571 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B5716453 : Blo 888571 5716453 := bstep (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) B1071835
theorem B10828343 : Blo 888571 10828343 := bstep (se 1 (by rfl) ⟨8121257, by rfl⟩ : syracuseStep 10828343 = 16242515) B16242515
theorem B2538823 : Blo 888571 2538823 := bstep (se 1 (by rfl) ⟨1904117, by rfl⟩ : syracuseStep 2538823 = 3808235) B3808235
theorem B2998943 : Blo 888571 2998943 := bstep (se 1 (by rfl) ⟨2249207, by rfl⟩ : syracuseStep 2998943 = 4498415) B4498415
theorem B1000543 : Blo 888571 1000543 := bstep (se 1 (by rfl) ⟨750407, by rfl⟩ : syracuseStep 1000543 = 1500815) B1500815
theorem B43828559 : Blo 888571 43828559 := bstep (se 1 (by rfl) ⟨32871419, by rfl⟩ : syracuseStep 43828559 = 65742839) B65742839
theorem B1689511 : Blo 888571 1689511 := bstep (se 1 (by rfl) ⟨1267133, by rfl⟩ : syracuseStep 1689511 = 2534267) B2534267
theorem B14633081 : Blo 888571 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B2706077 : Blo 888571 2706077 := bstep (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) B1014779
theorem B1690399 : Blo 888571 1690399 := bstep (se 1 (by rfl) ⟨1267799, by rfl⟩ : syracuseStep 1690399 = 2535599) B2535599
theorem B1002343 : Blo 888571 1002343 := bstep (se 1 (by rfl) ⟨751757, by rfl⟩ : syracuseStep 1002343 = 1503515) B1503515
theorem B3001535 : Blo 888571 3001535 := bstep (se 1 (by rfl) ⟨2251151, by rfl⟩ : syracuseStep 3001535 = 4502303) B4502303
theorem B26070443 : Blo 888571 26070443 := bstep (se 1 (by rfl) ⟨19552832, by rfl⟩ : syracuseStep 26070443 = 39105665) B39105665
theorem B1265311 : Blo 888571 1265311 := bstep (se 1 (by rfl) ⟨948983, by rfl⟩ : syracuseStep 1265311 = 1897967) B1897967
theorem B3002075 : Blo 888571 3002075 := bstep (se 1 (by rfl) ⟨2251556, by rfl⟩ : syracuseStep 3002075 = 4503113) B4503113
theorem B3002237 : Blo 888571 3002237 := bstep (se 3 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 3002237 = 1125839) B1125839
theorem B11718539 : Blo 888571 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B1691903 : Blo 888571 1691903 := bstep (se 1 (by rfl) ⟨1268927, by rfl⟩ : syracuseStep 1691903 = 2537855) B2537855
theorem B3002831 : Blo 888571 3002831 := bstep (se 1 (by rfl) ⟨2252123, by rfl⟩ : syracuseStep 3002831 = 4504247) B4504247
theorem B41179265 : Blo 888571 41179265 := bstep (se 2 (by rfl) ⟨15442224, by rfl⟩ : syracuseStep 41179265 = 30884449) B30884449
theorem B1333487 : Blo 888571 1333487 := bstep (se 1 (by rfl) ⟨1000115, by rfl⟩ : syracuseStep 1333487 = 2000231) B2000231
theorem B1333559 : Blo 888571 1333559 := bstep (se 1 (by rfl) ⟨1000169, by rfl⟩ : syracuseStep 1333559 = 2000339) B2000339
theorem B1333607 : Blo 888571 1333607 := bstep (se 1 (by rfl) ⟨1000205, by rfl⟩ : syracuseStep 1333607 = 2000411) B2000411
theorem B3004775 : Blo 888571 3004775 := bstep (se 1 (by rfl) ⟨2253581, by rfl⟩ : syracuseStep 3004775 = 4507163) B4507163
theorem B1334267 : Blo 888571 1334267 := bstep (se 1 (by rfl) ⟨1000700, by rfl⟩ : syracuseStep 1334267 = 2001401) B2001401
theorem B1334447 : Blo 888571 1334447 := bstep (se 1 (by rfl) ⟨1000835, by rfl⟩ : syracuseStep 1334447 = 2001671) B2001671
theorem B3005639 : Blo 888571 3005639 := bstep (se 1 (by rfl) ⟨2254229, by rfl⟩ : syracuseStep 3005639 = 4508459) B4508459
theorem B6413737 : Blo 888571 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B1334939 : Blo 888571 1334939 := bstep (se 1 (by rfl) ⟨1001204, by rfl⟩ : syracuseStep 1334939 = 2002409) B2002409
theorem B1334975 : Blo 888571 1334975 := bstep (se 1 (by rfl) ⟨1001231, by rfl⟩ : syracuseStep 1334975 = 2002463) B2002463
theorem B1335119 : Blo 888571 1335119 := bstep (se 1 (by rfl) ⟨1001339, by rfl⟩ : syracuseStep 1335119 = 2002679) B2002679
theorem B1335599 : Blo 888571 1335599 := bstep (se 1 (by rfl) ⟨1001699, by rfl⟩ : syracuseStep 1335599 = 2003399) B2003399
theorem B19259815 : Blo 888571 19259815 := bstep (se 1 (by rfl) ⟨14444861, by rfl⟩ : syracuseStep 19259815 = 28889723) B28889723
theorem B4055615 : Blo 888571 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B1336091 : Blo 888571 1336091 := bstep (se 1 (by rfl) ⟨1002068, by rfl⟩ : syracuseStep 1336091 = 2004137) B2004137
theorem B1336103 : Blo 888571 1336103 := bstep (se 1 (by rfl) ⟨1002077, by rfl⟩ : syracuseStep 1336103 = 2004155) B2004155
theorem B4514615 : Blo 888571 4514615 := bstep (se 1 (by rfl) ⟨3385961, by rfl⟩ : syracuseStep 4514615 = 6771923) B6771923
theorem B1336127 : Blo 888571 1336127 := bstep (se 1 (by rfl) ⟨1002095, by rfl⟩ : syracuseStep 1336127 = 2004191) B2004191
theorem B1500187 : Blo 888571 1500187 := bstep (se 1 (by rfl) ⟨1125140, by rfl⟩ : syracuseStep 1500187 = 2250281) B2250281
theorem B3008231 : Blo 888571 3008231 := bstep (se 1 (by rfl) ⟨2256173, by rfl⟩ : syracuseStep 3008231 = 4512347) B4512347
theorem B18310931 : Blo 888571 18310931 := bstep (se 1 (by rfl) ⟨13733198, by rfl⟩ : syracuseStep 18310931 = 27466397) B27466397
theorem B21620681 : Blo 888571 21620681 := bstep (se 2 (by rfl) ⟨8107755, by rfl⟩ : syracuseStep 21620681 = 16215511) B16215511
theorem B2255303 : Blo 888571 2255303 := bstep (se 1 (by rfl) ⟨1691477, by rfl⟩ : syracuseStep 2255303 = 3382955) B3382955
theorem B2256083 : Blo 888571 2256083 := bstep (se 1 (by rfl) ⟨1692062, by rfl⟩ : syracuseStep 2256083 = 3384125) B3384125
theorem B5696999 : Blo 888571 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B3207275 : Blo 888571 3207275 := bstep (se 1 (by rfl) ⟨2405456, by rfl⟩ : syracuseStep 3207275 = 4810913) B4810913
theorem B3010715 : Blo 888571 3010715 := bstep (se 1 (by rfl) ⟨2258036, by rfl⟩ : syracuseStep 3010715 = 4516073) B4516073
theorem B8548573 : Blo 888571 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B29258765 : Blo 888571 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B1505135 : Blo 888571 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B21658043 : Blo 888571 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B1505783 : Blo 888571 1505783 := bstep (se 1 (by rfl) ⟨1129337, by rfl⟩ : syracuseStep 1505783 = 2258675) B2258675
theorem B1505999 : Blo 888571 1505999 := bstep (se 1 (by rfl) ⟨1129499, by rfl⟩ : syracuseStep 1505999 = 2258999) B2258999
theorem B6519947 : Blo 888571 6519947 := bstep (se 1 (by rfl) ⟨4889960, by rfl⟩ : syracuseStep 6519947 = 9779921) B9779921
theorem B4816169 : Blo 888571 4816169 := bstep (se 2 (by rfl) ⟨1806063, by rfl⟩ : syracuseStep 4816169 = 3612127) B3612127
theorem B52133377 : Blo 888571 52133377 := bstep (se 2 (by rfl) ⟨19550016, by rfl⟩ : syracuseStep 52133377 = 39100033) B39100033
theorem B1999295 : Blo 888571 1999295 := bstep (se 1 (by rfl) ⟨1499471, by rfl⟩ : syracuseStep 1999295 = 2998943) B2998943
theorem B2000249 : Blo 888571 2000249 := bstep (se 2 (by rfl) ⟨750093, by rfl⟩ : syracuseStep 2000249 = 1500187) B1500187
theorem B1804051 : Blo 888571 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B2001023 : Blo 888571 2001023 := bstep (se 1 (by rfl) ⟨1500767, by rfl⟩ : syracuseStep 2001023 = 3001535) B3001535
theorem B2001383 : Blo 888571 2001383 := bstep (se 1 (by rfl) ⟨1501037, by rfl⟩ : syracuseStep 2001383 = 3002075) B3002075
theorem B2001491 : Blo 888571 2001491 := bstep (se 1 (by rfl) ⟨1501118, by rfl⟩ : syracuseStep 2001491 = 3002237) B3002237
theorem B2001887 : Blo 888571 2001887 := bstep (se 1 (by rfl) ⟨1501415, by rfl⟩ : syracuseStep 2001887 = 3002831) B3002831
theorem B8130233 : Blo 888571 8130233 := bstep (se 2 (by rfl) ⟨3048837, by rfl⟩ : syracuseStep 8130233 = 6097675) B6097675
theorem B888991 : Blo 888571 888991 := bstep (se 1 (by rfl) ⟨666743, by rfl⟩ : syracuseStep 888991 = 1333487) B1333487
theorem B889039 : Blo 888571 889039 := bstep (se 1 (by rfl) ⟨666779, by rfl⟩ : syracuseStep 889039 = 1333559) B1333559
theorem B889071 : Blo 888571 889071 := bstep (se 1 (by rfl) ⟨666803, by rfl⟩ : syracuseStep 889071 = 1333607) B1333607
theorem B2003183 : Blo 888571 2003183 := bstep (se 1 (by rfl) ⟨1502387, by rfl⟩ : syracuseStep 2003183 = 3004775) B3004775
theorem B6427115 : Blo 888571 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B889511 : Blo 888571 889511 := bstep (se 1 (by rfl) ⟨667133, by rfl⟩ : syracuseStep 889511 = 1334267) B1334267
theorem B889631 : Blo 888571 889631 := bstep (se 1 (by rfl) ⟨667223, by rfl⟩ : syracuseStep 889631 = 1334447) B1334447
theorem B2003759 : Blo 888571 2003759 := bstep (se 1 (by rfl) ⟨1502819, by rfl⟩ : syracuseStep 2003759 = 3005639) B3005639
theorem B889959 : Blo 888571 889959 := bstep (se 1 (by rfl) ⟨667469, by rfl⟩ : syracuseStep 889959 = 1334939) B1334939
theorem B889983 : Blo 888571 889983 := bstep (se 1 (by rfl) ⟨667487, by rfl⟩ : syracuseStep 889983 = 1334975) B1334975
theorem B7607479 : Blo 888571 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B890079 : Blo 888571 890079 := bstep (se 1 (by rfl) ⟨667559, by rfl⟩ : syracuseStep 890079 = 1335119) B1335119
theorem B890399 : Blo 888571 890399 := bstep (se 1 (by rfl) ⟨667799, by rfl⟩ : syracuseStep 890399 = 1335599) B1335599
theorem B890727 : Blo 888571 890727 := bstep (se 1 (by rfl) ⟨668045, by rfl⟩ : syracuseStep 890727 = 1336091) B1336091
theorem B890735 : Blo 888571 890735 := bstep (se 1 (by rfl) ⟨668051, by rfl⟩ : syracuseStep 890735 = 1336103) B1336103
theorem B890751 : Blo 888571 890751 := bstep (se 1 (by rfl) ⟨668063, by rfl⟩ : syracuseStep 890751 = 1336127) B1336127
theorem B6101183 : Blo 888571 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B2005487 : Blo 888571 2005487 := bstep (se 1 (by rfl) ⟨1504115, by rfl⟩ : syracuseStep 2005487 = 3008231) B3008231
theorem B5774291 : Blo 888571 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B3808559 : Blo 888571 3808559 := bstep (se 1 (by rfl) ⟨2856419, by rfl⟩ : syracuseStep 3808559 = 5712839) B5712839
theorem B2138183 : Blo 888571 2138183 := bstep (se 1 (by rfl) ⟨1603637, by rfl⟩ : syracuseStep 2138183 = 3207275) B3207275
theorem B2007143 : Blo 888571 2007143 := bstep (se 1 (by rfl) ⟨1505357, by rfl⟩ : syracuseStep 2007143 = 3010715) B3010715
theorem B19505843 : Blo 888571 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B7218895 : Blo 888571 7218895 := bstep (se 1 (by rfl) ⟨5414171, by rfl⟩ : syracuseStep 7218895 = 10828343) B10828343
theorem B3385097 : Blo 888571 3385097 := bstep (se 2 (by rfl) ⟨1269411, by rfl⟩ : syracuseStep 3385097 = 2538823) B2538823
theorem B69511169 : Blo 888571 69511169 := bstep (se 2 (by rfl) ⟨26066688, by rfl⟩ : syracuseStep 69511169 = 52133377) B52133377
theorem B46181171 : Blo 888571 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B20590649 : Blo 888571 20590649 := bstep (se 2 (by rfl) ⟨7721493, by rfl⟩ : syracuseStep 20590649 = 15442987) B15442987
theorem B4501817 : Blo 888571 4501817 := bstep (se 2 (by rfl) ⟨1688181, by rfl⟩ : syracuseStep 4501817 = 3376363) B3376363
theorem B2142911 : Blo 888571 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B17380295 : Blo 888571 17380295 := bstep (se 1 (by rfl) ⟨13035221, by rfl⟩ : syracuseStep 17380295 = 26070443) B26070443
theorem B7812359 : Blo 888571 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B1127935 : Blo 888571 1127935 := bstep (se 1 (by rfl) ⟨845951, by rfl⟩ : syracuseStep 1127935 = 1691903) B1691903
theorem B4503599 : Blo 888571 4503599 := bstep (se 1 (by rfl) ⟨3377699, by rfl⟩ : syracuseStep 4503599 = 6755399) B6755399
theorem B1687081 : Blo 888571 1687081 := bstep (se 2 (by rfl) ⟨632655, by rfl⟩ : syracuseStep 1687081 = 1265311) B1265311
theorem B12828395 : Blo 888571 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B2703743 : Blo 888571 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B1688303 : Blo 888571 1688303 := bstep (se 1 (by rfl) ⟨1266227, by rfl⟩ : syracuseStep 1688303 = 2532455) B2532455
theorem B12207287 : Blo 888571 12207287 := bstep (se 1 (by rfl) ⟨9155465, by rfl⟩ : syracuseStep 12207287 = 18310931) B18310931
theorem B14437277 : Blo 888571 14437277 := bstep (se 3 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 14437277 = 5413979) B5413979
theorem B17386525 : Blo 888571 17386525 := bstep (se 3 (by rfl) ⟨3259973, by rfl⟩ : syracuseStep 17386525 = 6519947) B6519947
theorem B7621937 : Blo 888571 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B1003423 : Blo 888571 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B14438695 : Blo 888571 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B1003855 : Blo 888571 1003855 := bstep (se 1 (by rfl) ⟨752891, by rfl⟩ : syracuseStep 1003855 = 1505783) B1505783
theorem B1003999 : Blo 888571 1003999 := bstep (se 1 (by rfl) ⟨752999, by rfl⟩ : syracuseStep 1003999 = 1505999) B1505999
theorem B15225893 : Blo 888571 15225893 := bstep (se 4 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 15225893 = 2854855) B2854855
theorem B4510889 : Blo 888571 4510889 := bstep (se 2 (by rfl) ⟨1691583, by rfl⟩ : syracuseStep 4510889 = 3383167) B3383167
theorem B25679753 : Blo 888571 25679753 := bstep (se 2 (by rfl) ⟨9629907, by rfl⟩ : syracuseStep 25679753 = 19259815) B19259815
theorem B1333355 : Blo 888571 1333355 := bstep (se 1 (by rfl) ⟨1000016, by rfl⟩ : syracuseStep 1333355 = 2000033) B2000033
theorem B1071311 : Blo 888571 1071311 := bstep (se 1 (by rfl) ⟨803483, by rfl⟩ : syracuseStep 1071311 = 1606967) B1606967
theorem B29219039 : Blo 888571 29219039 := bstep (se 1 (by rfl) ⟨21914279, by rfl⟩ : syracuseStep 29219039 = 43828559) B43828559
theorem B2251111 : Blo 888571 2251111 := bstep (se 1 (by rfl) ⟨1688333, by rfl⟩ : syracuseStep 2251111 = 3376667) B3376667
theorem B9755387 : Blo 888571 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B1334057 : Blo 888571 1334057 := bstep (se 2 (by rfl) ⟨500271, by rfl⟩ : syracuseStep 1334057 = 1000543) B1000543
theorem B2251759 : Blo 888571 2251759 := bstep (se 1 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 2251759 = 3377639) B3377639
theorem B2251871 : Blo 888571 2251871 := bstep (se 1 (by rfl) ⟨1688903, by rfl⟩ : syracuseStep 2251871 = 3377807) B3377807
theorem B1334507 : Blo 888571 1334507 := bstep (se 1 (by rfl) ⟨1000880, by rfl⟩ : syracuseStep 1334507 = 2001761) B2001761
theorem B1335131 : Blo 888571 1335131 := bstep (se 1 (by rfl) ⟨1001348, by rfl⟩ : syracuseStep 1335131 = 2002697) B2002697
theorem B2252681 : Blo 888571 2252681 := bstep (se 2 (by rfl) ⟨844755, by rfl⟩ : syracuseStep 2252681 = 1689511) B1689511
theorem B6774839 : Blo 888571 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B1335935 : Blo 888571 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B2253865 : Blo 888571 2253865 := bstep (se 2 (by rfl) ⟨845199, by rfl⟩ : syracuseStep 2253865 = 1690399) B1690399
theorem B1336415 : Blo 888571 1336415 := bstep (se 1 (by rfl) ⟨1002311, by rfl⟩ : syracuseStep 1336415 = 2004623) B2004623
theorem B1336457 : Blo 888571 1336457 := bstep (se 2 (by rfl) ⟨501171, by rfl⟩ : syracuseStep 1336457 = 1002343) B1002343
theorem B2254007 : Blo 888571 2254007 := bstep (se 1 (by rfl) ⟨1690505, by rfl⟩ : syracuseStep 2254007 = 3381011) B3381011
theorem B1336631 : Blo 888571 1336631 := bstep (se 1 (by rfl) ⟨1002473, by rfl⟩ : syracuseStep 1336631 = 2004947) B2004947
theorem B1336679 : Blo 888571 1336679 := bstep (se 1 (by rfl) ⟨1002509, by rfl⟩ : syracuseStep 1336679 = 2005019) B2005019
theorem B27452843 : Blo 888571 27452843 := bstep (se 1 (by rfl) ⟨20589632, by rfl⟩ : syracuseStep 27452843 = 41179265) B41179265
theorem B1337039 : Blo 888571 1337039 := bstep (se 1 (by rfl) ⟨1002779, by rfl⟩ : syracuseStep 1337039 = 2005559) B2005559
theorem B11398097 : Blo 888571 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B3009743 : Blo 888571 3009743 := bstep (se 1 (by rfl) ⟨2257307, by rfl⟩ : syracuseStep 3009743 = 4514615) B4514615
theorem B1338815 : Blo 888571 1338815 := bstep (se 1 (by rfl) ⟨1004111, by rfl⟩ : syracuseStep 1338815 = 2008223) B2008223
theorem B14413787 : Blo 888571 14413787 := bstep (se 1 (by rfl) ⟨10810340, by rfl⟩ : syracuseStep 14413787 = 21620681) B21620681
theorem B1503535 : Blo 888571 1503535 := bstep (se 1 (by rfl) ⟨1127651, by rfl⟩ : syracuseStep 1503535 = 2255303) B2255303
theorem B8548847 : Blo 888571 8548847 := bstep (se 1 (by rfl) ⟨6411635, by rfl⟩ : syracuseStep 8548847 = 12823271) B12823271
theorem B1504055 : Blo 888571 1504055 := bstep (se 1 (by rfl) ⟨1128041, by rfl⟩ : syracuseStep 1504055 = 2256083) B2256083
theorem B3797999 : Blo 888571 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B14644255 : Blo 888571 14644255 := bstep (se 1 (by rfl) ⟨10983191, by rfl⟩ : syracuseStep 14644255 = 21966383) B21966383
theorem B9270605 : Blo 888571 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B9140363 : Blo 888571 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B8551649 : Blo 888571 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B3210779 : Blo 888571 3210779 := bstep (se 1 (by rfl) ⟨2408084, by rfl⟩ : syracuseStep 3210779 = 4816169) B4816169
theorem B1802495 : Blo 888571 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B5081291 : Blo 888571 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B888903 : Blo 888571 888903 := bstep (se 1 (by rfl) ⟨666677, by rfl⟩ : syracuseStep 888903 = 1333355) B1333355
theorem B4067455 : Blo 888571 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B889371 : Blo 888571 889371 := bstep (se 1 (by rfl) ⟨667028, by rfl⟩ : syracuseStep 889371 = 1334057) B1334057
theorem B889671 : Blo 888571 889671 := bstep (se 1 (by rfl) ⟨667253, by rfl⟩ : syracuseStep 889671 = 1334507) B1334507
theorem B890087 : Blo 888571 890087 := bstep (se 1 (by rfl) ⟨667565, by rfl⟩ : syracuseStep 890087 = 1335131) B1335131
theorem B2004713 : Blo 888571 2004713 := bstep (se 2 (by rfl) ⟨751767, by rfl⟩ : syracuseStep 2004713 = 1503535) B1503535
theorem B890623 : Blo 888571 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B890943 : Blo 888571 890943 := bstep (se 1 (by rfl) ⟨668207, by rfl⟩ : syracuseStep 890943 = 1336415) B1336415
theorem B890971 : Blo 888571 890971 := bstep (se 1 (by rfl) ⟨668228, by rfl⟩ : syracuseStep 890971 = 1336457) B1336457
theorem B891087 : Blo 888571 891087 := bstep (se 1 (by rfl) ⟨668315, by rfl⟩ : syracuseStep 891087 = 1336631) B1336631
theorem B891119 : Blo 888571 891119 := bstep (se 1 (by rfl) ⟨668339, by rfl⟩ : syracuseStep 891119 = 1336679) B1336679
theorem B891359 : Blo 888571 891359 := bstep (se 1 (by rfl) ⟨668519, by rfl⟩ : syracuseStep 891359 = 1337039) B1337039
theorem B46340779 : Blo 888571 46340779 := bstep (se 1 (by rfl) ⟨34755584, by rfl⟩ : syracuseStep 46340779 = 69511169) B69511169
theorem B2006495 : Blo 888571 2006495 := bstep (se 1 (by rfl) ⟨1504871, by rfl⟩ : syracuseStep 2006495 = 3009743) B3009743
theorem B892543 : Blo 888571 892543 := bstep (se 1 (by rfl) ⟨669407, by rfl⟩ : syracuseStep 892543 = 1338815) B1338815
theorem B9609191 : Blo 888571 9609191 := bstep (se 1 (by rfl) ⟨7206893, by rfl⟩ : syracuseStep 9609191 = 14413787) B14413787
theorem B2531999 : Blo 888571 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B2140519 : Blo 888571 2140519 := bstep (se 1 (by rfl) ⟨1605389, by rfl⟩ : syracuseStep 2140519 = 3210779) B3210779
theorem B4502141 : Blo 888571 4502141 := bstep (se 3 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 4502141 = 1688303) B1688303
theorem B32552765 : Blo 888571 32552765 := bstep (se 3 (by rfl) ⟨6103643, by rfl⟩ : syracuseStep 32552765 = 12207287) B12207287
theorem B17119835 : Blo 888571 17119835 := bstep (se 1 (by rfl) ⟨12839876, by rfl⟩ : syracuseStep 17119835 = 25679753) B25679753
theorem B23182033 : Blo 888571 23182033 := bstep (se 2 (by rfl) ⟨8693262, by rfl⟩ : syracuseStep 23182033 = 17386525) B17386525
theorem B19479359 : Blo 888571 19479359 := bstep (se 1 (by rfl) ⟨14609519, by rfl⟩ : syracuseStep 19479359 = 29219039) B29219039
theorem B6503591 : Blo 888571 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B3849527 : Blo 888571 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B2539039 : Blo 888571 2539039 := bstep (se 1 (by rfl) ⟨1904279, by rfl⟩ : syracuseStep 2539039 = 3808559) B3808559
theorem B1425455 : Blo 888571 1425455 := bstep (se 1 (by rfl) ⟨1069091, by rfl⟩ : syracuseStep 1425455 = 2138183) B2138183
theorem B19251593 : Blo 888571 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B18301895 : Blo 888571 18301895 := bstep (se 1 (by rfl) ⟨13726421, by rfl⟩ : syracuseStep 18301895 = 27452843) B27452843
theorem B10143305 : Blo 888571 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B30787447 : Blo 888571 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B3001211 : Blo 888571 3001211 := bstep (se 1 (by rfl) ⟨2250908, by rfl⟩ : syracuseStep 3001211 = 4501817) B4501817
theorem B1428607 : Blo 888571 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B3001481 : Blo 888571 3001481 := bstep (se 2 (by rfl) ⟨1125555, by rfl⟩ : syracuseStep 3001481 = 2251111) B2251111
theorem B1002703 : Blo 888571 1002703 := bstep (se 1 (by rfl) ⟨752027, by rfl⟩ : syracuseStep 1002703 = 1504055) B1504055
theorem B11586863 : Blo 888571 11586863 := bstep (se 1 (by rfl) ⟨8690147, by rfl⟩ : syracuseStep 11586863 = 17380295) B17380295
theorem B6180403 : Blo 888571 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B3002345 : Blo 888571 3002345 := bstep (se 2 (by rfl) ⟨1125879, by rfl⟩ : syracuseStep 3002345 = 2251759) B2251759
theorem B3002399 : Blo 888571 3002399 := bstep (se 1 (by rfl) ⟨2251799, by rfl⟩ : syracuseStep 3002399 = 4503599) B4503599
theorem B9621605 : Blo 888571 9621605 := bstep (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) B1804051
theorem B21680621 : Blo 888571 21680621 := bstep (se 3 (by rfl) ⟨4065116, by rfl⟩ : syracuseStep 21680621 = 8130233) B8130233
theorem B2249441 : Blo 888571 2249441 := bstep (se 2 (by rfl) ⟨843540, by rfl⟩ : syracuseStep 2249441 = 1687081) B1687081
theorem B1332863 : Blo 888571 1332863 := bstep (se 1 (by rfl) ⟨999647, by rfl⟩ : syracuseStep 1332863 = 1999295) B1999295
theorem B1333499 : Blo 888571 1333499 := bstep (se 1 (by rfl) ⟨1000124, by rfl⟩ : syracuseStep 1333499 = 2000249) B2000249
theorem B3005153 : Blo 888571 3005153 := bstep (se 2 (by rfl) ⟨1126932, by rfl⟩ : syracuseStep 3005153 = 2253865) B2253865
theorem B1334015 : Blo 888571 1334015 := bstep (se 1 (by rfl) ⟨1000511, by rfl⟩ : syracuseStep 1334015 = 2001023) B2001023
theorem B1334255 : Blo 888571 1334255 := bstep (se 1 (by rfl) ⟨1000691, by rfl⟩ : syracuseStep 1334255 = 2001383) B2001383
theorem B1334327 : Blo 888571 1334327 := bstep (se 1 (by rfl) ⟨1000745, by rfl⟩ : syracuseStep 1334327 = 2001491) B2001491
theorem B9624851 : Blo 888571 9624851 := bstep (se 1 (by rfl) ⟨7218638, by rfl⟩ : syracuseStep 9624851 = 14437277) B14437277
theorem B1334591 : Blo 888571 1334591 := bstep (se 1 (by rfl) ⟨1000943, by rfl⟩ : syracuseStep 1334591 = 2001887) B2001887
theorem B11427317 : Blo 888571 11427317 := bstep (se 5 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 11427317 = 1071311) B1071311
theorem B9625193 : Blo 888571 9625193 := bstep (se 2 (by rfl) ⟨3609447, by rfl⟩ : syracuseStep 9625193 = 7218895) B7218895
theorem B1335455 : Blo 888571 1335455 := bstep (se 1 (by rfl) ⟨1001591, by rfl⟩ : syracuseStep 1335455 = 2003183) B2003183
theorem B4284743 : Blo 888571 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B1335839 : Blo 888571 1335839 := bstep (se 1 (by rfl) ⟨1001879, by rfl⟩ : syracuseStep 1335839 = 2003759) B2003759
theorem B10150595 : Blo 888571 10150595 := bstep (se 1 (by rfl) ⟨7612946, by rfl⟩ : syracuseStep 10150595 = 15225893) B15225893
theorem B3007259 : Blo 888571 3007259 := bstep (se 1 (by rfl) ⟨2255444, by rfl⟩ : syracuseStep 3007259 = 4510889) B4510889
theorem B1336991 : Blo 888571 1336991 := bstep (se 1 (by rfl) ⟨1002743, by rfl⟩ : syracuseStep 1336991 = 2005487) B2005487
theorem B1501247 : Blo 888571 1501247 := bstep (se 1 (by rfl) ⟨1125935, by rfl⟩ : syracuseStep 1501247 = 2251871) B2251871
theorem B1337897 : Blo 888571 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B1501787 : Blo 888571 1501787 := bstep (se 1 (by rfl) ⟨1126340, by rfl⟩ : syracuseStep 1501787 = 2252681) B2252681
theorem B4516559 : Blo 888571 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B1338095 : Blo 888571 1338095 := bstep (se 1 (by rfl) ⟨1003571, by rfl⟩ : syracuseStep 1338095 = 2007143) B2007143
theorem B1338473 : Blo 888571 1338473 := bstep (se 2 (by rfl) ⟨501927, by rfl⟩ : syracuseStep 1338473 = 1003855) B1003855
theorem B13003895 : Blo 888571 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B1338665 : Blo 888571 1338665 := bstep (se 2 (by rfl) ⟨501999, by rfl⟩ : syracuseStep 1338665 = 1003999) B1003999
theorem B1502671 : Blo 888571 1502671 := bstep (se 1 (by rfl) ⟨1127003, by rfl⟩ : syracuseStep 1502671 = 2254007) B2254007
theorem B2256731 : Blo 888571 2256731 := bstep (se 1 (by rfl) ⟨1692548, by rfl⟩ : syracuseStep 2256731 = 3385097) B3385097
theorem B19525673 : Blo 888571 19525673 := bstep (se 2 (by rfl) ⟨7322127, by rfl⟩ : syracuseStep 19525673 = 14644255) B14644255
theorem B7598731 : Blo 888571 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B1503913 : Blo 888571 1503913 := bstep (se 2 (by rfl) ⟨563967, by rfl⟩ : syracuseStep 1503913 = 1127935) B1127935
theorem B13727099 : Blo 888571 13727099 := bstep (se 1 (by rfl) ⟨10295324, by rfl⟩ : syracuseStep 13727099 = 20590649) B20590649
theorem B5699231 : Blo 888571 5699231 := bstep (se 1 (by rfl) ⟨4274423, by rfl⟩ : syracuseStep 5699231 = 8548847) B8548847
theorem B5208239 : Blo 888571 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B6093575 : Blo 888571 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B34209053 : Blo 888571 34209053 := bstep (se 3 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 34209053 = 12828395) B12828395
theorem B5701099 : Blo 888571 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B950303 : Blo 888571 950303 := bstep (se 1 (by rfl) ⟨712727, by rfl⟩ : syracuseStep 950303 = 1425455) B1425455
theorem B6751997 : Blo 888571 6751997 := bstep (se 3 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 6751997 = 2531999) B2531999
theorem B2000807 : Blo 888571 2000807 := bstep (se 1 (by rfl) ⟨1500605, by rfl⟩ : syracuseStep 2000807 = 3001211) B3001211
theorem B2000987 : Blo 888571 2000987 := bstep (se 1 (by rfl) ⟨1500740, by rfl⟩ : syracuseStep 2000987 = 3001481) B3001481
theorem B2001563 : Blo 888571 2001563 := bstep (se 1 (by rfl) ⟨1501172, by rfl⟩ : syracuseStep 2001563 = 3002345) B3002345
theorem B2001599 : Blo 888571 2001599 := bstep (se 1 (by rfl) ⟨1501199, by rfl⟩ : syracuseStep 2001599 = 3002399) B3002399
theorem B14453747 : Blo 888571 14453747 := bstep (se 1 (by rfl) ⟨10840310, by rfl⟩ : syracuseStep 14453747 = 21680621) B21680621
theorem B2854025 : Blo 888571 2854025 := bstep (se 2 (by rfl) ⟨1070259, by rfl⟩ : syracuseStep 2854025 = 2140519) B2140519
theorem B888575 : Blo 888571 888575 := bstep (se 1 (by rfl) ⟨666431, by rfl⟩ : syracuseStep 888575 = 1332863) B1332863
theorem B888999 : Blo 888571 888999 := bstep (se 1 (by rfl) ⟨666749, by rfl⟩ : syracuseStep 888999 = 1333499) B1333499
theorem B1904809 : Blo 888571 1904809 := bstep (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) B1428607
theorem B2003435 : Blo 888571 2003435 := bstep (se 1 (by rfl) ⟨1502576, by rfl⟩ : syracuseStep 2003435 = 3005153) B3005153
theorem B889343 : Blo 888571 889343 := bstep (se 1 (by rfl) ⟨667007, by rfl⟩ : syracuseStep 889343 = 1334015) B1334015
theorem B2003561 : Blo 888571 2003561 := bstep (se 2 (by rfl) ⟨751335, by rfl⟩ : syracuseStep 2003561 = 1502671) B1502671
theorem B889503 : Blo 888571 889503 := bstep (se 1 (by rfl) ⟨667127, by rfl⟩ : syracuseStep 889503 = 1334255) B1334255
theorem B889551 : Blo 888571 889551 := bstep (se 1 (by rfl) ⟨667163, by rfl⟩ : syracuseStep 889551 = 1334327) B1334327
theorem B889727 : Blo 888571 889727 := bstep (se 1 (by rfl) ⟨667295, by rfl⟩ : syracuseStep 889727 = 1334591) B1334591
theorem B890303 : Blo 888571 890303 := bstep (se 1 (by rfl) ⟨667727, by rfl⟩ : syracuseStep 890303 = 1335455) B1335455
theorem B890559 : Blo 888571 890559 := bstep (se 1 (by rfl) ⟨667919, by rfl⟩ : syracuseStep 890559 = 1335839) B1335839
theorem B2004839 : Blo 888571 2004839 := bstep (se 1 (by rfl) ⟨1503629, by rfl⟩ : syracuseStep 2004839 = 3007259) B3007259
theorem B10131641 : Blo 888571 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B2005217 : Blo 888571 2005217 := bstep (se 2 (by rfl) ⟨751956, by rfl⟩ : syracuseStep 2005217 = 1503913) B1503913
theorem B891327 : Blo 888571 891327 := bstep (se 1 (by rfl) ⟨668495, by rfl⟩ : syracuseStep 891327 = 1336991) B1336991
theorem B891931 : Blo 888571 891931 := bstep (se 1 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 891931 = 1337897) B1337897
theorem B892063 : Blo 888571 892063 := bstep (se 1 (by rfl) ⟨669047, by rfl⟩ : syracuseStep 892063 = 1338095) B1338095
theorem B892315 : Blo 888571 892315 := bstep (se 1 (by rfl) ⟨669236, by rfl⟩ : syracuseStep 892315 = 1338473) B1338473
theorem B892443 : Blo 888571 892443 := bstep (se 1 (by rfl) ⟨669332, by rfl⟩ : syracuseStep 892443 = 1338665) B1338665
theorem B13017115 : Blo 888571 13017115 := bstep (se 1 (by rfl) ⟨9762836, by rfl⟩ : syracuseStep 13017115 = 19525673) B19525673
theorem B17342909 : Blo 888571 17342909 := bstep (se 3 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 17342909 = 6503591) B6503591
theorem B9151399 : Blo 888571 9151399 := bstep (se 1 (by rfl) ⟨6863549, by rfl⟩ : syracuseStep 9151399 = 13727099) B13727099
theorem B30909377 : Blo 888571 30909377 := bstep (se 2 (by rfl) ⟨11591016, by rfl⟩ : syracuseStep 30909377 = 23182033) B23182033
theorem B21701843 : Blo 888571 21701843 := bstep (se 1 (by rfl) ⟨16276382, by rfl⟩ : syracuseStep 21701843 = 32552765) B32552765
theorem B11413223 : Blo 888571 11413223 := bstep (se 1 (by rfl) ⟨8559917, by rfl⟩ : syracuseStep 11413223 = 17119835) B17119835
theorem B12986239 : Blo 888571 12986239 := bstep (se 1 (by rfl) ⟨9739679, by rfl⟩ : syracuseStep 12986239 = 19479359) B19479359
theorem B3385385 : Blo 888571 3385385 := bstep (se 2 (by rfl) ⟨1269519, by rfl⟩ : syracuseStep 3385385 = 2539039) B2539039
theorem B2566351 : Blo 888571 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B12201263 : Blo 888571 12201263 := bstep (se 1 (by rfl) ⟨9150947, by rfl⟩ : syracuseStep 12201263 = 18301895) B18301895
theorem B6762203 : Blo 888571 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B3387527 : Blo 888571 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B8240537 : Blo 888571 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B7618211 : Blo 888571 7618211 := bstep (se 1 (by rfl) ⟨5713658, by rfl⟩ : syracuseStep 7618211 = 11427317) B11427317
theorem B6406127 : Blo 888571 6406127 := bstep (se 1 (by rfl) ⟨4804595, by rfl⟩ : syracuseStep 6406127 = 9609191) B9609191
theorem B5423273 : Blo 888571 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B6767063 : Blo 888571 6767063 := bstep (se 1 (by rfl) ⟨5075297, by rfl⟩ : syracuseStep 6767063 = 10150595) B10150595
theorem B1000831 : Blo 888571 1000831 := bstep (se 1 (by rfl) ⟨750623, by rfl⟩ : syracuseStep 1000831 = 1501247) B1501247
theorem B1001191 : Blo 888571 1001191 := bstep (se 1 (by rfl) ⟨750893, by rfl⟩ : syracuseStep 1001191 = 1501787) B1501787
theorem B8669263 : Blo 888571 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B3001427 : Blo 888571 3001427 := bstep (se 1 (by rfl) ⟨2251070, by rfl⟩ : syracuseStep 3001427 = 4502141) B4502141
theorem B61787705 : Blo 888571 61787705 := bstep (se 2 (by rfl) ⟨23170389, by rfl⟩ : syracuseStep 61787705 = 46340779) B46340779
theorem B1201663 : Blo 888571 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B12834395 : Blo 888571 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B11425981 : Blo 888571 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B7724575 : Blo 888571 7724575 := bstep (se 1 (by rfl) ⟨5793431, by rfl⟩ : syracuseStep 7724575 = 11586863) B11586863
theorem B41049929 : Blo 888571 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B6414403 : Blo 888571 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B1499627 : Blo 888571 1499627 := bstep (se 1 (by rfl) ⟨1124720, by rfl⟩ : syracuseStep 1499627 = 2249441) B2249441
theorem B1336475 : Blo 888571 1336475 := bstep (se 1 (by rfl) ⟨1002356, by rfl⟩ : syracuseStep 1336475 = 2004713) B2004713
theorem B1336937 : Blo 888571 1336937 := bstep (se 2 (by rfl) ⟨501351, by rfl⟩ : syracuseStep 1336937 = 1002703) B1002703
theorem B6416567 : Blo 888571 6416567 := bstep (se 1 (by rfl) ⟨4812425, by rfl⟩ : syracuseStep 6416567 = 9624851) B9624851
theorem B1337663 : Blo 888571 1337663 := bstep (se 1 (by rfl) ⟨1003247, by rfl⟩ : syracuseStep 1337663 = 2006495) B2006495
theorem B6416795 : Blo 888571 6416795 := bstep (se 1 (by rfl) ⟨4812596, by rfl⟩ : syracuseStep 6416795 = 9625193) B9625193
theorem B3011039 : Blo 888571 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B1504487 : Blo 888571 1504487 := bstep (se 1 (by rfl) ⟨1128365, by rfl⟩ : syracuseStep 1504487 = 2256731) B2256731
theorem B3799487 : Blo 888571 3799487 := bstep (se 1 (by rfl) ⟨2849615, by rfl⟩ : syracuseStep 3799487 = 5699231) B5699231
theorem B3472159 : Blo 888571 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B4062383 : Blo 888571 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B7601465 : Blo 888571 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B22806035 : Blo 888571 22806035 := bstep (se 1 (by rfl) ⟨17104526, by rfl⟩ : syracuseStep 22806035 = 34209053) B34209053
theorem B8552537 : Blo 888571 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B9635831 : Blo 888571 9635831 := bstep (se 1 (by rfl) ⟨7226873, by rfl⟩ : syracuseStep 9635831 = 14453747) B14453747
theorem B2000951 : Blo 888571 2000951 := bstep (se 1 (by rfl) ⟨1500713, by rfl⟩ : syracuseStep 2000951 = 3001427) B3001427
theorem B1902683 : Blo 888571 1902683 := bstep (se 1 (by rfl) ⟨1427012, by rfl⟩ : syracuseStep 1902683 = 2854025) B2854025
theorem B8556263 : Blo 888571 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B6754427 : Blo 888571 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B27366619 : Blo 888571 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B890983 : Blo 888571 890983 := bstep (se 1 (by rfl) ⟨668237, by rfl⟩ : syracuseStep 890983 = 1336475) B1336475
theorem B891291 : Blo 888571 891291 := bstep (se 1 (by rfl) ⟨668468, by rfl⟩ : syracuseStep 891291 = 1336937) B1336937
theorem B7608815 : Blo 888571 7608815 := bstep (se 1 (by rfl) ⟨5706611, by rfl⟩ : syracuseStep 7608815 = 11413223) B11413223
theorem B891775 : Blo 888571 891775 := bstep (se 1 (by rfl) ⟨668831, by rfl⟩ : syracuseStep 891775 = 1337663) B1337663
theorem B8134175 : Blo 888571 8134175 := bstep (se 1 (by rfl) ⟨6100631, by rfl⟩ : syracuseStep 8134175 = 12201263) B12201263
theorem B2007359 : Blo 888571 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B4629545 : Blo 888571 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B164767213 : Blo 888571 164767213 := bstep (se 3 (by rfl) ⟨30893852, by rfl⟩ : syracuseStep 164767213 = 61787705) B61787705
theorem B2532991 : Blo 888571 2532991 := bstep (se 1 (by rfl) ⟨1899743, by rfl⟩ : syracuseStep 2532991 = 3799487) B3799487
theorem B10299433 : Blo 888571 10299433 := bstep (se 2 (by rfl) ⟨3862287, by rfl⟩ : syracuseStep 10299433 = 7724575) B7724575
theorem B4270751 : Blo 888571 4270751 := bstep (se 1 (by rfl) ⟨3203063, by rfl⟩ : syracuseStep 4270751 = 6406127) B6406127
theorem B2534141 : Blo 888571 2534141 := bstep (se 3 (by rfl) ⟨475151, by rfl⟩ : syracuseStep 2534141 = 950303) B950303
theorem B3615515 : Blo 888571 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B4501331 : Blo 888571 4501331 := bstep (se 1 (by rfl) ⟨3375998, by rfl⟩ : syracuseStep 4501331 = 6751997) B6751997
theorem B17314985 : Blo 888571 17314985 := bstep (se 2 (by rfl) ⟨6493119, by rfl⟩ : syracuseStep 17314985 = 12986239) B12986239
theorem B3421801 : Blo 888571 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B48807461 : Blo 888571 48807461 := bstep (se 4 (by rfl) ⟨4575699, by rfl⟩ : syracuseStep 48807461 = 9151399) B9151399
theorem B2539745 : Blo 888571 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B999751 : Blo 888571 999751 := bstep (se 1 (by rfl) ⟨749813, by rfl⟩ : syracuseStep 999751 = 1499627) B1499627
theorem B14467895 : Blo 888571 14467895 := bstep (se 1 (by rfl) ⟨10850921, by rfl⟩ : syracuseStep 14467895 = 21701843) B21701843
theorem B4277711 : Blo 888571 4277711 := bstep (se 1 (by rfl) ⟨3208283, by rfl⟩ : syracuseStep 4277711 = 6416567) B6416567
theorem B4277863 : Blo 888571 4277863 := bstep (se 1 (by rfl) ⟨3208397, by rfl⟩ : syracuseStep 4277863 = 6416795) B6416795
theorem B4508135 : Blo 888571 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B1002991 : Blo 888571 1002991 := bstep (se 1 (by rfl) ⟨752243, by rfl⟩ : syracuseStep 1002991 = 1504487) B1504487
theorem B2708255 : Blo 888571 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B5067643 : Blo 888571 5067643 := bstep (se 1 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 5067643 = 7601465) B7601465
theorem B5493691 : Blo 888571 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B17356153 : Blo 888571 17356153 := bstep (se 2 (by rfl) ⟨6508557, by rfl⟩ : syracuseStep 17356153 = 13017115) B13017115
theorem B4511375 : Blo 888571 4511375 := bstep (se 1 (by rfl) ⟨3383531, by rfl⟩ : syracuseStep 4511375 = 6767063) B6767063
theorem B1333871 : Blo 888571 1333871 := bstep (se 1 (by rfl) ⟨1000403, by rfl⟩ : syracuseStep 1333871 = 2000807) B2000807
theorem B1333991 : Blo 888571 1333991 := bstep (se 1 (by rfl) ⟨1000493, by rfl⟩ : syracuseStep 1333991 = 2000987) B2000987
theorem B1334375 : Blo 888571 1334375 := bstep (se 1 (by rfl) ⟨1000781, by rfl⟩ : syracuseStep 1334375 = 2001563) B2001563
theorem B1334399 : Blo 888571 1334399 := bstep (se 1 (by rfl) ⟨1000799, by rfl⟩ : syracuseStep 1334399 = 2001599) B2001599
theorem B1334441 : Blo 888571 1334441 := bstep (se 2 (by rfl) ⟨500415, by rfl⟩ : syracuseStep 1334441 = 1000831) B1000831
theorem B1334921 : Blo 888571 1334921 := bstep (se 2 (by rfl) ⟨500595, by rfl⟩ : syracuseStep 1334921 = 1001191) B1001191
theorem B11559017 : Blo 888571 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B1335623 : Blo 888571 1335623 := bstep (se 1 (by rfl) ⟨1001717, by rfl⟩ : syracuseStep 1335623 = 2003435) B2003435
theorem B1335707 : Blo 888571 1335707 := bstep (se 1 (by rfl) ⟨1001780, by rfl⟩ : syracuseStep 1335707 = 2003561) B2003561
theorem B1336559 : Blo 888571 1336559 := bstep (se 1 (by rfl) ⟨1002419, by rfl⟩ : syracuseStep 1336559 = 2004839) B2004839
theorem B1336811 : Blo 888571 1336811 := bstep (se 1 (by rfl) ⟨1002608, by rfl⟩ : syracuseStep 1336811 = 2005217) B2005217
theorem B11561939 : Blo 888571 11561939 := bstep (se 1 (by rfl) ⟨8671454, by rfl⟩ : syracuseStep 11561939 = 17342909) B17342909
theorem B20606251 : Blo 888571 20606251 := bstep (se 1 (by rfl) ⟨15454688, by rfl⟩ : syracuseStep 20606251 = 30909377) B30909377
theorem B2256923 : Blo 888571 2256923 := bstep (se 1 (by rfl) ⟨1692692, by rfl⟩ : syracuseStep 2256923 = 3385385) B3385385
theorem B1602217 : Blo 888571 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B2258351 : Blo 888571 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B15234641 : Blo 888571 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B15204023 : Blo 888571 15204023 := bstep (se 1 (by rfl) ⟨11403017, by rfl⟩ : syracuseStep 15204023 = 22806035) B22806035
theorem B5078807 : Blo 888571 5078807 := bstep (se 1 (by rfl) ⟨3809105, by rfl⟩ : syracuseStep 5078807 = 7618211) B7618211
theorem B5701691 : Blo 888571 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B2851807 : Blo 888571 2851807 := bstep (se 1 (by rfl) ⟨2138855, by rfl⟩ : syracuseStep 2851807 = 4277711) B4277711
theorem B6423887 : Blo 888571 6423887 := bstep (se 1 (by rfl) ⟨4817915, by rfl⟩ : syracuseStep 6423887 = 9635831) B9635831
theorem B5703817 : Blo 888571 5703817 := bstep (se 2 (by rfl) ⟨2138931, by rfl⟩ : syracuseStep 5703817 = 4277863) B4277863
theorem B3377321 : Blo 888571 3377321 := bstep (se 2 (by rfl) ⟨1266495, by rfl⟩ : syracuseStep 3377321 = 2532991) B2532991
theorem B5704175 : Blo 888571 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B13732577 : Blo 888571 13732577 := bstep (se 2 (by rfl) ⟨5149716, by rfl⟩ : syracuseStep 13732577 = 10299433) B10299433
theorem B1805503 : Blo 888571 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B889247 : Blo 888571 889247 := bstep (se 1 (by rfl) ⟨666935, by rfl⟩ : syracuseStep 889247 = 1333871) B1333871
theorem B889327 : Blo 888571 889327 := bstep (se 1 (by rfl) ⟨666995, by rfl⟩ : syracuseStep 889327 = 1333991) B1333991
theorem B889583 : Blo 888571 889583 := bstep (se 1 (by rfl) ⟨667187, by rfl⟩ : syracuseStep 889583 = 1334375) B1334375
theorem B889599 : Blo 888571 889599 := bstep (se 1 (by rfl) ⟨667199, by rfl⟩ : syracuseStep 889599 = 1334399) B1334399
theorem B889627 : Blo 888571 889627 := bstep (se 1 (by rfl) ⟨667220, by rfl⟩ : syracuseStep 889627 = 1334441) B1334441
theorem B889947 : Blo 888571 889947 := bstep (se 1 (by rfl) ⟨667460, by rfl⟩ : syracuseStep 889947 = 1334921) B1334921
theorem B7706011 : Blo 888571 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B890415 : Blo 888571 890415 := bstep (se 1 (by rfl) ⟨667811, by rfl⟩ : syracuseStep 890415 = 1335623) B1335623
theorem B890471 : Blo 888571 890471 := bstep (se 1 (by rfl) ⟨667853, by rfl⟩ : syracuseStep 890471 = 1335707) B1335707
theorem B3086363 : Blo 888571 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B891039 : Blo 888571 891039 := bstep (se 1 (by rfl) ⟨668279, by rfl⟩ : syracuseStep 891039 = 1336559) B1336559
theorem B2136289 : Blo 888571 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B891207 : Blo 888571 891207 := bstep (se 1 (by rfl) ⟨668405, by rfl⟩ : syracuseStep 891207 = 1336811) B1336811
theorem B6756857 : Blo 888571 6756857 := bstep (se 2 (by rfl) ⟨2533821, by rfl⟩ : syracuseStep 6756857 = 5067643) B5067643
theorem B23141537 : Blo 888571 23141537 := bstep (se 2 (by rfl) ⟨8678076, by rfl⟩ : syracuseStep 23141537 = 17356153) B17356153
theorem B7707959 : Blo 888571 7707959 := bstep (se 1 (by rfl) ⟨5780969, by rfl⟩ : syracuseStep 7707959 = 11561939) B11561939
theorem B4562401 : Blo 888571 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B11543323 : Blo 888571 11543323 := bstep (se 1 (by rfl) ⟨8657492, by rfl⟩ : syracuseStep 11543323 = 17314985) B17314985
theorem B10136015 : Blo 888571 10136015 := bstep (se 1 (by rfl) ⟨7602011, by rfl⟩ : syracuseStep 10136015 = 15204023) B15204023
theorem B3385871 : Blo 888571 3385871 := bstep (se 1 (by rfl) ⟨2539403, by rfl⟩ : syracuseStep 3385871 = 5078807) B5078807
theorem B9645263 : Blo 888571 9645263 := bstep (se 1 (by rfl) ⟨7233947, by rfl⟩ : syracuseStep 9645263 = 14467895) B14467895
theorem B219689617 : Blo 888571 219689617 := bstep (se 2 (by rfl) ⟨82383606, by rfl⟩ : syracuseStep 219689617 = 164767213) B164767213
theorem B4502951 : Blo 888571 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B27475001 : Blo 888571 27475001 := bstep (se 2 (by rfl) ⟨10303125, by rfl⟩ : syracuseStep 27475001 = 20606251) B20606251
theorem B5422783 : Blo 888571 5422783 := bstep (se 1 (by rfl) ⟨4067087, by rfl⟩ : syracuseStep 5422783 = 8134175) B8134175
theorem B7324921 : Blo 888571 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B36488825 : Blo 888571 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B1689427 : Blo 888571 1689427 := bstep (se 1 (by rfl) ⟨1267070, by rfl⟩ : syracuseStep 1689427 = 2534141) B2534141
theorem B2410343 : Blo 888571 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B3000887 : Blo 888571 3000887 := bstep (se 1 (by rfl) ⟨2250665, by rfl⟩ : syracuseStep 3000887 = 4501331) B4501331
theorem B1693163 : Blo 888571 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B1333001 : Blo 888571 1333001 := bstep (se 2 (by rfl) ⟨499875, by rfl⟩ : syracuseStep 1333001 = 999751) B999751
theorem B1333967 : Blo 888571 1333967 := bstep (se 1 (by rfl) ⟨1000475, by rfl⟩ : syracuseStep 1333967 = 2000951) B2000951
theorem B1268455 : Blo 888571 1268455 := bstep (se 1 (by rfl) ⟨951341, by rfl⟩ : syracuseStep 1268455 = 1902683) B1902683
theorem B3005423 : Blo 888571 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B3007583 : Blo 888571 3007583 := bstep (se 1 (by rfl) ⟨2255687, by rfl⟩ : syracuseStep 3007583 = 4511375) B4511375
theorem B5072543 : Blo 888571 5072543 := bstep (se 1 (by rfl) ⟨3804407, by rfl⟩ : syracuseStep 5072543 = 7608815) B7608815
theorem B1337321 : Blo 888571 1337321 := bstep (se 2 (by rfl) ⟨501495, by rfl⟩ : syracuseStep 1337321 = 1002991) B1002991
theorem B1338239 : Blo 888571 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B2847167 : Blo 888571 2847167 := bstep (se 1 (by rfl) ⟨2135375, by rfl⟩ : syracuseStep 2847167 = 4270751) B4270751
theorem B1504615 : Blo 888571 1504615 := bstep (se 1 (by rfl) ⟨1128461, by rfl⟩ : syracuseStep 1504615 = 2256923) B2256923
theorem B1505567 : Blo 888571 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B10156427 : Blo 888571 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B32538307 : Blo 888571 32538307 := bstep (se 1 (by rfl) ⟨24403730, by rfl⟩ : syracuseStep 32538307 = 48807461) B48807461
theorem B3801127 : Blo 888571 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B1606895 : Blo 888571 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B3802409 : Blo 888571 3802409 := bstep (se 2 (by rfl) ⟨1425903, by rfl⟩ : syracuseStep 3802409 = 2851807) B2851807
theorem B3802783 : Blo 888571 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B2000591 : Blo 888571 2000591 := bstep (se 1 (by rfl) ⟨1500443, by rfl⟩ : syracuseStep 2000591 = 3000887) B3000887
theorem B7605089 : Blo 888571 7605089 := bstep (se 2 (by rfl) ⟨2851908, by rfl⟩ : syracuseStep 7605089 = 5703817) B5703817
theorem B888667 : Blo 888571 888667 := bstep (se 1 (by rfl) ⟨666500, by rfl⟩ : syracuseStep 888667 = 1333001) B1333001
theorem B889311 : Blo 888571 889311 := bstep (se 1 (by rfl) ⟨666983, by rfl⟩ : syracuseStep 889311 = 1333967) B1333967
theorem B2003615 : Blo 888571 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B2005055 : Blo 888571 2005055 := bstep (se 1 (by rfl) ⟨1503791, by rfl⟩ : syracuseStep 2005055 = 3007583) B3007583
theorem B292919489 : Blo 888571 292919489 := bstep (se 2 (by rfl) ⟨109844808, by rfl⟩ : syracuseStep 292919489 = 219689617) B219689617
theorem B3381695 : Blo 888571 3381695 := bstep (se 1 (by rfl) ⟨2536271, by rfl⟩ : syracuseStep 3381695 = 5072543) B5072543
theorem B39066245 : Blo 888571 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B891547 : Blo 888571 891547 := bstep (se 1 (by rfl) ⟨668660, by rfl⟩ : syracuseStep 891547 = 1337321) B1337321
theorem B6757343 : Blo 888571 6757343 := bstep (se 1 (by rfl) ⟨5068007, by rfl⟩ : syracuseStep 6757343 = 10136015) B10136015
theorem B2006153 : Blo 888571 2006153 := bstep (se 2 (by rfl) ⟨752307, by rfl⟩ : syracuseStep 2006153 = 1504615) B1504615
theorem B892159 : Blo 888571 892159 := bstep (se 1 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 892159 = 1338239) B1338239
theorem B6430175 : Blo 888571 6430175 := bstep (se 1 (by rfl) ⟨4822631, by rfl⟩ : syracuseStep 6430175 = 9645263) B9645263
theorem B24325883 : Blo 888571 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B9155051 : Blo 888571 9155051 := bstep (se 1 (by rfl) ⟨6866288, by rfl⟩ : syracuseStep 9155051 = 13732577) B13732577
theorem B2407337 : Blo 888571 2407337 := bstep (se 2 (by rfl) ⟨902751, by rfl⟩ : syracuseStep 2407337 = 1805503) B1805503
theorem B4504571 : Blo 888571 4504571 := bstep (se 1 (by rfl) ⟨3378428, by rfl⟩ : syracuseStep 4504571 = 6756857) B6756857
theorem B10274681 : Blo 888571 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B3001967 : Blo 888571 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B1691273 : Blo 888571 1691273 := bstep (se 2 (by rfl) ⟨634227, by rfl⟩ : syracuseStep 1691273 = 1268455) B1268455
theorem B1003711 : Blo 888571 1003711 := bstep (se 1 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 1003711 = 1505567) B1505567
theorem B6770951 : Blo 888571 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B6083201 : Blo 888571 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B7230377 : Blo 888571 7230377 := bstep (se 2 (by rfl) ⟨2711391, by rfl⟩ : syracuseStep 7230377 = 5422783) B5422783
theorem B4282591 : Blo 888571 4282591 := bstep (se 1 (by rfl) ⟨3211943, by rfl⟩ : syracuseStep 4282591 = 6423887) B6423887
theorem B15391097 : Blo 888571 15391097 := bstep (se 2 (by rfl) ⟨5771661, by rfl⟩ : syracuseStep 15391097 = 11543323) B11543323
theorem B2251547 : Blo 888571 2251547 := bstep (se 1 (by rfl) ⟨1688660, by rfl⟩ : syracuseStep 2251547 = 3377321) B3377321
theorem B2252569 : Blo 888571 2252569 := bstep (se 2 (by rfl) ⟨844713, by rfl⟩ : syracuseStep 2252569 = 1689427) B1689427
theorem B4515101 : Blo 888571 4515101 := bstep (se 3 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 4515101 = 1693163) B1693163
theorem B2057575 : Blo 888571 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B15427691 : Blo 888571 15427691 := bstep (se 1 (by rfl) ⟨11570768, by rfl⟩ : syracuseStep 15427691 = 23141537) B23141537
theorem B5138639 : Blo 888571 5138639 := bstep (se 1 (by rfl) ⟨3853979, by rfl⟩ : syracuseStep 5138639 = 7707959) B7707959
theorem B2257247 : Blo 888571 2257247 := bstep (se 1 (by rfl) ⟨1692935, by rfl⟩ : syracuseStep 2257247 = 3385871) B3385871
theorem B1898111 : Blo 888571 1898111 := bstep (se 1 (by rfl) ⟨1423583, by rfl⟩ : syracuseStep 1898111 = 2847167) B2847167
theorem B2848385 : Blo 888571 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B18316667 : Blo 888571 18316667 := bstep (se 1 (by rfl) ⟨13737500, by rfl⟩ : syracuseStep 18316667 = 27475001) B27475001
theorem B43384409 : Blo 888571 43384409 := bstep (se 2 (by rfl) ⟨16269153, by rfl⟩ : syracuseStep 43384409 = 32538307) B32538307
theorem B6849787 : Blo 888571 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B16221869 : Blo 888571 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B2001311 : Blo 888571 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B4820251 : Blo 888571 4820251 := bstep (se 1 (by rfl) ⟨3615188, by rfl⟩ : syracuseStep 4820251 = 7230377) B7230377
theorem B10260731 : Blo 888571 10260731 := bstep (se 1 (by rfl) ⟨7695548, by rfl⟩ : syracuseStep 10260731 = 15391097) B15391097
theorem B5710121 : Blo 888571 5710121 := bstep (se 2 (by rfl) ⟨2141295, by rfl⟩ : syracuseStep 5710121 = 4282591) B4282591
theorem B6103367 : Blo 888571 6103367 := bstep (se 1 (by rfl) ⟨4577525, by rfl⟩ : syracuseStep 6103367 = 9155051) B9155051
theorem B2534939 : Blo 888571 2534939 := bstep (se 1 (by rfl) ⟨1901204, by rfl⟩ : syracuseStep 2534939 = 3802409) B3802409
theorem B1127515 : Blo 888571 1127515 := bstep (se 1 (by rfl) ⟨845636, by rfl⟩ : syracuseStep 1127515 = 1691273) B1691273
theorem B195279659 : Blo 888571 195279659 := bstep (se 1 (by rfl) ⟨146459744, by rfl⟩ : syracuseStep 195279659 = 292919489) B292919489
theorem B5061629 : Blo 888571 5061629 := bstep (se 3 (by rfl) ⟨949055, by rfl⟩ : syracuseStep 5061629 = 1898111) B1898111
theorem B4504895 : Blo 888571 4504895 := bstep (se 1 (by rfl) ⟨3378671, by rfl⟩ : syracuseStep 4504895 = 6757343) B6757343
theorem B3425759 : Blo 888571 3425759 := bstep (se 1 (by rfl) ⟨2569319, by rfl⟩ : syracuseStep 3425759 = 5138639) B5138639
theorem B3003047 : Blo 888571 3003047 := bstep (se 1 (by rfl) ⟨2252285, by rfl⟩ : syracuseStep 3003047 = 4504571) B4504571
theorem B12211111 : Blo 888571 12211111 := bstep (se 1 (by rfl) ⟨9158333, by rfl⟩ : syracuseStep 12211111 = 18316667) B18316667
theorem B3003425 : Blo 888571 3003425 := bstep (se 2 (by rfl) ⟨1126284, by rfl⟩ : syracuseStep 3003425 = 2252569) B2252569
theorem B28922939 : Blo 888571 28922939 := bstep (se 1 (by rfl) ⟨21692204, by rfl⟩ : syracuseStep 28922939 = 43384409) B43384409
theorem B5068169 : Blo 888571 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B1071263 : Blo 888571 1071263 := bstep (se 1 (by rfl) ⟨803447, by rfl⟩ : syracuseStep 1071263 = 1606895) B1606895
theorem B1333727 : Blo 888571 1333727 := bstep (se 1 (by rfl) ⟨1000295, by rfl⟩ : syracuseStep 1333727 = 2000591) B2000591
theorem B2743433 : Blo 888571 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B5070059 : Blo 888571 5070059 := bstep (se 1 (by rfl) ⟨3802544, by rfl⟩ : syracuseStep 5070059 = 7605089) B7605089
theorem B5070377 : Blo 888571 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B4513967 : Blo 888571 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B1335743 : Blo 888571 1335743 := bstep (se 1 (by rfl) ⟨1001807, by rfl⟩ : syracuseStep 1335743 = 2003615) B2003615
theorem B1336703 : Blo 888571 1336703 := bstep (se 1 (by rfl) ⟨1002527, by rfl⟩ : syracuseStep 1336703 = 2005055) B2005055
theorem B2254463 : Blo 888571 2254463 := bstep (se 1 (by rfl) ⟨1690847, by rfl⟩ : syracuseStep 2254463 = 3381695) B3381695
theorem B7595693 : Blo 888571 7595693 := bstep (se 3 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 7595693 = 2848385) B2848385
theorem B26044163 : Blo 888571 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B1501031 : Blo 888571 1501031 := bstep (se 1 (by rfl) ⟨1125773, by rfl⟩ : syracuseStep 1501031 = 2251547) B2251547
theorem B1337435 : Blo 888571 1337435 := bstep (se 1 (by rfl) ⟨1003076, by rfl⟩ : syracuseStep 1337435 = 2006153) B2006153
theorem B4286783 : Blo 888571 4286783 := bstep (se 1 (by rfl) ⟨3215087, by rfl⟩ : syracuseStep 4286783 = 6430175) B6430175
theorem B1338281 : Blo 888571 1338281 := bstep (se 2 (by rfl) ⟨501855, by rfl⟩ : syracuseStep 1338281 = 1003711) B1003711
theorem B3010067 : Blo 888571 3010067 := bstep (se 1 (by rfl) ⟨2257550, by rfl⟩ : syracuseStep 3010067 = 4515101) B4515101
theorem B10285127 : Blo 888571 10285127 := bstep (se 1 (by rfl) ⟨7713845, by rfl⟩ : syracuseStep 10285127 = 15427691) B15427691
theorem B16217255 : Blo 888571 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B1504831 : Blo 888571 1504831 := bstep (se 1 (by rfl) ⟨1128623, by rfl⟩ : syracuseStep 1504831 = 2257247) B2257247
theorem B1604891 : Blo 888571 1604891 := bstep (se 1 (by rfl) ⟨1203668, by rfl⟩ : syracuseStep 1604891 = 2407337) B2407337
theorem B10814579 : Blo 888571 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B2002031 : Blo 888571 2002031 := bstep (se 1 (by rfl) ⟨1501523, by rfl⟩ : syracuseStep 2002031 = 3003047) B3003047
theorem B2002283 : Blo 888571 2002283 := bstep (se 1 (by rfl) ⟨1501712, by rfl⟩ : syracuseStep 2002283 = 3003425) B3003425
theorem B3378779 : Blo 888571 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B889151 : Blo 888571 889151 := bstep (se 1 (by rfl) ⟨666863, by rfl⟩ : syracuseStep 889151 = 1333727) B1333727
theorem B6427001 : Blo 888571 6427001 := bstep (se 2 (by rfl) ⟨2410125, by rfl⟩ : syracuseStep 6427001 = 4820251) B4820251
theorem B3380039 : Blo 888571 3380039 := bstep (se 1 (by rfl) ⟨2535029, by rfl⟩ : syracuseStep 3380039 = 5070059) B5070059
theorem B3380251 : Blo 888571 3380251 := bstep (se 1 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 3380251 = 5070377) B5070377
theorem B3806747 : Blo 888571 3806747 := bstep (se 1 (by rfl) ⟨2855060, by rfl⟩ : syracuseStep 3806747 = 5710121) B5710121
theorem B4068911 : Blo 888571 4068911 := bstep (se 1 (by rfl) ⟨3051683, by rfl⟩ : syracuseStep 4068911 = 6103367) B6103367
theorem B890495 : Blo 888571 890495 := bstep (se 1 (by rfl) ⟨667871, by rfl⟩ : syracuseStep 890495 = 1335743) B1335743
theorem B2856701 : Blo 888571 2856701 := bstep (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) B1071263
theorem B891135 : Blo 888571 891135 := bstep (se 1 (by rfl) ⟨668351, by rfl⟩ : syracuseStep 891135 = 1336703) B1336703
theorem B891623 : Blo 888571 891623 := bstep (se 1 (by rfl) ⟨668717, by rfl⟩ : syracuseStep 891623 = 1337435) B1337435
theorem B2857855 : Blo 888571 2857855 := bstep (se 1 (by rfl) ⟨2143391, by rfl⟩ : syracuseStep 2857855 = 4286783) B4286783
theorem B892187 : Blo 888571 892187 := bstep (se 1 (by rfl) ⟨669140, by rfl⟩ : syracuseStep 892187 = 1338281) B1338281
theorem B2006441 : Blo 888571 2006441 := bstep (se 2 (by rfl) ⟨752415, by rfl⟩ : syracuseStep 2006441 = 1504831) B1504831
theorem B2006711 : Blo 888571 2006711 := bstep (se 1 (by rfl) ⟨1505033, by rfl⟩ : syracuseStep 2006711 = 3010067) B3010067
theorem B6856751 : Blo 888571 6856751 := bstep (se 1 (by rfl) ⟨5142563, by rfl⟩ : syracuseStep 6856751 = 10285127) B10285127
theorem B19281959 : Blo 888571 19281959 := bstep (se 1 (by rfl) ⟨14461469, by rfl⟩ : syracuseStep 19281959 = 28922939) B28922939
theorem B5063795 : Blo 888571 5063795 := bstep (se 1 (by rfl) ⟨3797846, by rfl⟩ : syracuseStep 5063795 = 7595693) B7595693
theorem B1000687 : Blo 888571 1000687 := bstep (se 1 (by rfl) ⟨750515, by rfl⟩ : syracuseStep 1000687 = 1501031) B1501031
theorem B1689959 : Blo 888571 1689959 := bstep (se 1 (by rfl) ⟨1267469, by rfl⟩ : syracuseStep 1689959 = 2534939) B2534939
theorem B4279709 : Blo 888571 4279709 := bstep (se 3 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 4279709 = 1604891) B1604891
theorem B3003263 : Blo 888571 3003263 := bstep (se 1 (by rfl) ⟨2252447, by rfl⟩ : syracuseStep 3003263 = 4504895) B4504895
theorem B2283839 : Blo 888571 2283839 := bstep (se 1 (by rfl) ⟨1712879, by rfl⟩ : syracuseStep 2283839 = 3425759) B3425759
theorem B1334207 : Blo 888571 1334207 := bstep (se 1 (by rfl) ⟨1000655, by rfl⟩ : syracuseStep 1334207 = 2001311) B2001311
theorem B9133049 : Blo 888571 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B6840487 : Blo 888571 6840487 := bstep (se 1 (by rfl) ⟨5130365, by rfl⟩ : syracuseStep 6840487 = 10260731) B10260731
theorem B1828955 : Blo 888571 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B3009311 : Blo 888571 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B1502975 : Blo 888571 1502975 := bstep (se 1 (by rfl) ⟨1127231, by rfl⟩ : syracuseStep 1502975 = 2254463) B2254463
theorem B17362775 : Blo 888571 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B16281481 : Blo 888571 16281481 := bstep (se 2 (by rfl) ⟨6105555, by rfl⟩ : syracuseStep 16281481 = 12211111) B12211111
theorem B1503353 : Blo 888571 1503353 := bstep (se 2 (by rfl) ⟨563757, by rfl⟩ : syracuseStep 1503353 = 1127515) B1127515
theorem B10811503 : Blo 888571 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B130186439 : Blo 888571 130186439 := bstep (se 1 (by rfl) ⟨97639829, by rfl⟩ : syracuseStep 130186439 = 195279659) B195279659
theorem B3374419 : Blo 888571 3374419 := bstep (se 1 (by rfl) ⟨2530814, by rfl⟩ : syracuseStep 3374419 = 5061629) B5061629
theorem B7209719 : Blo 888571 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B3375863 : Blo 888571 3375863 := bstep (se 1 (by rfl) ⟨2531897, by rfl⟩ : syracuseStep 3375863 = 5063795) B5063795
theorem B2853139 : Blo 888571 2853139 := bstep (se 1 (by rfl) ⟨2139854, by rfl⟩ : syracuseStep 2853139 = 4279709) B4279709
theorem B2002175 : Blo 888571 2002175 := bstep (se 1 (by rfl) ⟨1501631, by rfl⟩ : syracuseStep 2002175 = 3003263) B3003263
theorem B1904467 : Blo 888571 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B10850429 : Blo 888571 10850429 := bstep (se 3 (by rfl) ⟨2034455, by rfl⟩ : syracuseStep 10850429 = 4068911) B4068911
theorem B889471 : Blo 888571 889471 := bstep (se 1 (by rfl) ⟨667103, by rfl⟩ : syracuseStep 889471 = 1334207) B1334207
theorem B1219303 : Blo 888571 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B2006207 : Blo 888571 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B11575183 : Blo 888571 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B3810473 : Blo 888571 3810473 := bstep (se 2 (by rfl) ⟨1428927, by rfl⟩ : syracuseStep 3810473 = 2857855) B2857855
theorem B12854639 : Blo 888571 12854639 := bstep (se 1 (by rfl) ⟨9640979, by rfl⟩ : syracuseStep 12854639 = 19281959) B19281959
theorem B4499225 : Blo 888571 4499225 := bstep (se 2 (by rfl) ⟨1687209, by rfl⟩ : syracuseStep 4499225 = 3374419) B3374419
theorem B9120649 : Blo 888571 9120649 := bstep (se 2 (by rfl) ⟨3420243, by rfl⟩ : syracuseStep 9120649 = 6840487) B6840487
theorem B1126639 : Blo 888571 1126639 := bstep (se 1 (by rfl) ⟨844979, by rfl⟩ : syracuseStep 1126639 = 1689959) B1689959
theorem B2537831 : Blo 888571 2537831 := bstep (se 1 (by rfl) ⟨1903373, by rfl⟩ : syracuseStep 2537831 = 3806747) B3806747
theorem B1522559 : Blo 888571 1522559 := bstep (se 1 (by rfl) ⟨1141919, by rfl⟩ : syracuseStep 1522559 = 2283839) B2283839
theorem B21708641 : Blo 888571 21708641 := bstep (se 2 (by rfl) ⟨8140740, by rfl⟩ : syracuseStep 21708641 = 16281481) B16281481
theorem B4571167 : Blo 888571 4571167 := bstep (se 1 (by rfl) ⟨3428375, by rfl⟩ : syracuseStep 4571167 = 6856751) B6856751
theorem B4507001 : Blo 888571 4507001 := bstep (se 2 (by rfl) ⟨1690125, by rfl⟩ : syracuseStep 4507001 = 3380251) B3380251
theorem B1001983 : Blo 888571 1001983 := bstep (se 1 (by rfl) ⟨751487, by rfl⟩ : syracuseStep 1001983 = 1502975) B1502975
theorem B1002235 : Blo 888571 1002235 := bstep (se 1 (by rfl) ⟨751676, by rfl⟩ : syracuseStep 1002235 = 1503353) B1503353
theorem B86790959 : Blo 888571 86790959 := bstep (se 1 (by rfl) ⟨65093219, by rfl⟩ : syracuseStep 86790959 = 130186439) B130186439
theorem B1334249 : Blo 888571 1334249 := bstep (se 2 (by rfl) ⟨500343, by rfl⟩ : syracuseStep 1334249 = 1000687) B1000687
theorem B1334687 : Blo 888571 1334687 := bstep (se 1 (by rfl) ⟨1001015, by rfl⟩ : syracuseStep 1334687 = 2002031) B2002031
theorem B1334855 : Blo 888571 1334855 := bstep (se 1 (by rfl) ⟨1001141, by rfl⟩ : syracuseStep 1334855 = 2002283) B2002283
theorem B2252519 : Blo 888571 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B4284667 : Blo 888571 4284667 := bstep (se 1 (by rfl) ⟨3213500, by rfl⟩ : syracuseStep 4284667 = 6427001) B6427001
theorem B2253359 : Blo 888571 2253359 := bstep (se 1 (by rfl) ⟨1690019, by rfl⟩ : syracuseStep 2253359 = 3380039) B3380039
theorem B6088699 : Blo 888571 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B1337627 : Blo 888571 1337627 := bstep (se 1 (by rfl) ⟨1003220, by rfl⟩ : syracuseStep 1337627 = 2006441) B2006441
theorem B1337807 : Blo 888571 1337807 := bstep (se 1 (by rfl) ⟨1003355, by rfl⟩ : syracuseStep 1337807 = 2006711) B2006711
theorem B14415337 : Blo 888571 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B6094889 : Blo 888571 6094889 := bstep (se 2 (by rfl) ⟨2285583, by rfl⟩ : syracuseStep 6094889 = 4571167) B4571167
theorem B3804185 : Blo 888571 3804185 := bstep (se 2 (by rfl) ⟨1426569, by rfl⟩ : syracuseStep 3804185 = 2853139) B2853139
theorem B12160865 : Blo 888571 12160865 := bstep (se 2 (by rfl) ⟨4560324, by rfl⟩ : syracuseStep 12160865 = 9120649) B9120649
theorem B889499 : Blo 888571 889499 := bstep (se 1 (by rfl) ⟨667124, by rfl⟩ : syracuseStep 889499 = 1334249) B1334249
theorem B889791 : Blo 888571 889791 := bstep (se 1 (by rfl) ⟨667343, by rfl⟩ : syracuseStep 889791 = 1334687) B1334687
theorem B889903 : Blo 888571 889903 := bstep (se 1 (by rfl) ⟨667427, by rfl⟩ : syracuseStep 889903 = 1334855) B1334855
theorem B891751 : Blo 888571 891751 := bstep (se 1 (by rfl) ⟨668813, by rfl⟩ : syracuseStep 891751 = 1337627) B1337627
theorem B891871 : Blo 888571 891871 := bstep (se 1 (by rfl) ⟨668903, by rfl⟩ : syracuseStep 891871 = 1337807) B1337807
theorem B76881797 : Blo 888571 76881797 := bstep (se 4 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 76881797 = 14415337) B14415337
theorem B5712889 : Blo 888571 5712889 := bstep (se 2 (by rfl) ⟨2142333, by rfl⟩ : syracuseStep 5712889 = 4284667) B4284667
theorem B2539289 : Blo 888571 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B2540315 : Blo 888571 2540315 := bstep (se 1 (by rfl) ⟨1905236, by rfl⟩ : syracuseStep 2540315 = 3810473) B3810473
theorem B8569759 : Blo 888571 8569759 := bstep (se 1 (by rfl) ⟨6427319, by rfl⟩ : syracuseStep 8569759 = 12854639) B12854639
theorem B6767549 : Blo 888571 6767549 := bstep (se 3 (by rfl) ⟨1268915, by rfl⟩ : syracuseStep 6767549 = 2537831) B2537831
theorem B2999483 : Blo 888571 2999483 := bstep (se 1 (by rfl) ⟨2249612, by rfl⟩ : syracuseStep 2999483 = 4499225) B4499225
theorem B1625737 : Blo 888571 1625737 := bstep (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) B1219303
theorem B14472427 : Blo 888571 14472427 := bstep (se 1 (by rfl) ⟨10854320, by rfl⟩ : syracuseStep 14472427 = 21708641) B21708641
theorem B4806479 : Blo 888571 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B2250575 : Blo 888571 2250575 := bstep (se 1 (by rfl) ⟨1687931, by rfl⟩ : syracuseStep 2250575 = 3375863) B3375863
theorem B3004667 : Blo 888571 3004667 := bstep (se 1 (by rfl) ⟨2253500, by rfl⟩ : syracuseStep 3004667 = 4507001) B4507001
theorem B1334783 : Blo 888571 1334783 := bstep (se 1 (by rfl) ⟨1001087, by rfl⟩ : syracuseStep 1334783 = 2002175) B2002175
theorem B8118265 : Blo 888571 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B7233619 : Blo 888571 7233619 := bstep (se 1 (by rfl) ⟨5425214, by rfl⟩ : syracuseStep 7233619 = 10850429) B10850429
theorem B57860639 : Blo 888571 57860639 := bstep (se 1 (by rfl) ⟨43395479, by rfl⟩ : syracuseStep 57860639 = 86790959) B86790959
theorem B1335977 : Blo 888571 1335977 := bstep (se 2 (by rfl) ⟨500991, by rfl⟩ : syracuseStep 1335977 = 1001983) B1001983
theorem B1336313 : Blo 888571 1336313 := bstep (se 2 (by rfl) ⟨501117, by rfl⟩ : syracuseStep 1336313 = 1002235) B1002235
theorem B1337471 : Blo 888571 1337471 := bstep (se 1 (by rfl) ⟨1003103, by rfl⟩ : syracuseStep 1337471 = 2006207) B2006207
theorem B1501679 : Blo 888571 1501679 := bstep (se 1 (by rfl) ⟨1126259, by rfl⟩ : syracuseStep 1501679 = 2252519) B2252519
theorem B1502185 : Blo 888571 1502185 := bstep (se 2 (by rfl) ⟨563319, by rfl⟩ : syracuseStep 1502185 = 1126639) B1126639
theorem B1502239 : Blo 888571 1502239 := bstep (se 1 (by rfl) ⟨1126679, by rfl⟩ : syracuseStep 1502239 = 2253359) B2253359
theorem B1015039 : Blo 888571 1015039 := bstep (se 1 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 1015039 = 1522559) B1522559
theorem B15433577 : Blo 888571 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B4063259 : Blo 888571 4063259 := bstep (se 1 (by rfl) ⟨3047444, by rfl⟩ : syracuseStep 4063259 = 6094889) B6094889
theorem B1999655 : Blo 888571 1999655 := bstep (se 1 (by rfl) ⟨1499741, by rfl⟩ : syracuseStep 1999655 = 2999483) B2999483
theorem B2002913 : Blo 888571 2002913 := bstep (se 2 (by rfl) ⟨751092, by rfl⟩ : syracuseStep 2002913 = 1502185) B1502185
theorem B2002985 : Blo 888571 2002985 := bstep (se 2 (by rfl) ⟨751119, by rfl⟩ : syracuseStep 2002985 = 1502239) B1502239
theorem B2003111 : Blo 888571 2003111 := bstep (se 1 (by rfl) ⟨1502333, by rfl⟩ : syracuseStep 2003111 = 3004667) B3004667
theorem B2167649 : Blo 888571 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B12817277 : Blo 888571 12817277 := bstep (se 3 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 12817277 = 4806479) B4806479
theorem B889855 : Blo 888571 889855 := bstep (se 1 (by rfl) ⟨667391, by rfl⟩ : syracuseStep 889855 = 1334783) B1334783
theorem B51254531 : Blo 888571 51254531 := bstep (se 1 (by rfl) ⟨38440898, by rfl⟩ : syracuseStep 51254531 = 76881797) B76881797
theorem B38573759 : Blo 888571 38573759 := bstep (se 1 (by rfl) ⟨28930319, by rfl⟩ : syracuseStep 38573759 = 57860639) B57860639
theorem B890651 : Blo 888571 890651 := bstep (se 1 (by rfl) ⟨667988, by rfl⟩ : syracuseStep 890651 = 1335977) B1335977
theorem B890875 : Blo 888571 890875 := bstep (se 1 (by rfl) ⟨668156, by rfl⟩ : syracuseStep 890875 = 1336313) B1336313
theorem B891647 : Blo 888571 891647 := bstep (se 1 (by rfl) ⟨668735, by rfl⟩ : syracuseStep 891647 = 1337471) B1337471
theorem B1353385 : Blo 888571 1353385 := bstep (se 2 (by rfl) ⟨507519, by rfl⟩ : syracuseStep 1353385 = 1015039) B1015039
theorem B10824353 : Blo 888571 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B9644825 : Blo 888571 9644825 := bstep (se 2 (by rfl) ⟨3616809, by rfl⟩ : syracuseStep 9644825 = 7233619) B7233619
theorem B2536123 : Blo 888571 2536123 := bstep (se 1 (by rfl) ⟨1902092, by rfl⟩ : syracuseStep 2536123 = 3804185) B3804185
theorem B7617185 : Blo 888571 7617185 := bstep (se 2 (by rfl) ⟨2856444, by rfl⟩ : syracuseStep 7617185 = 5712889) B5712889
theorem B1001119 : Blo 888571 1001119 := bstep (se 1 (by rfl) ⟨750839, by rfl⟩ : syracuseStep 1001119 = 1501679) B1501679
theorem B6771437 : Blo 888571 6771437 := bstep (se 3 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 6771437 = 2539289) B2539289
theorem B32428973 : Blo 888571 32428973 := bstep (se 3 (by rfl) ⟨6080432, by rfl⟩ : syracuseStep 32428973 = 12160865) B12160865
theorem B1693543 : Blo 888571 1693543 := bstep (se 1 (by rfl) ⟨1270157, by rfl⟩ : syracuseStep 1693543 = 2540315) B2540315
theorem B4511699 : Blo 888571 4511699 := bstep (se 1 (by rfl) ⟨3383774, by rfl⟩ : syracuseStep 4511699 = 6767549) B6767549
theorem B11426345 : Blo 888571 11426345 := bstep (se 2 (by rfl) ⟨4284879, by rfl⟩ : syracuseStep 11426345 = 8569759) B8569759
theorem B1500383 : Blo 888571 1500383 := bstep (se 1 (by rfl) ⟨1125287, by rfl⟩ : syracuseStep 1500383 = 2250575) B2250575
theorem B19296569 : Blo 888571 19296569 := bstep (se 2 (by rfl) ⟨7236213, by rfl⟩ : syracuseStep 19296569 = 14472427) B14472427
theorem B10289051 : Blo 888571 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B1804513 : Blo 888571 1804513 := bstep (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) B1353385
theorem B1445099 : Blo 888571 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B3381497 : Blo 888571 3381497 := bstep (se 2 (by rfl) ⟨1268061, by rfl⟩ : syracuseStep 3381497 = 2536123) B2536123
theorem B7216235 : Blo 888571 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B6429883 : Blo 888571 6429883 := bstep (se 1 (by rfl) ⟨4822412, by rfl⟩ : syracuseStep 6429883 = 9644825) B9644825
theorem B6859367 : Blo 888571 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B7617563 : Blo 888571 7617563 := bstep (se 1 (by rfl) ⟨5713172, by rfl⟩ : syracuseStep 7617563 = 11426345) B11426345
theorem B1000255 : Blo 888571 1000255 := bstep (se 1 (by rfl) ⟨750191, by rfl⟩ : syracuseStep 1000255 = 1500383) B1500383
theorem B12864379 : Blo 888571 12864379 := bstep (se 1 (by rfl) ⟨9648284, by rfl⟩ : syracuseStep 12864379 = 19296569) B19296569
theorem B2708839 : Blo 888571 2708839 := bstep (se 1 (by rfl) ⟨2031629, by rfl⟩ : syracuseStep 2708839 = 4063259) B4063259
theorem B1333103 : Blo 888571 1333103 := bstep (se 1 (by rfl) ⟨999827, by rfl⟩ : syracuseStep 1333103 = 1999655) B1999655
theorem B1334825 : Blo 888571 1334825 := bstep (se 2 (by rfl) ⟨500559, by rfl⟩ : syracuseStep 1334825 = 1001119) B1001119
theorem B1335275 : Blo 888571 1335275 := bstep (se 1 (by rfl) ⟨1001456, by rfl⟩ : syracuseStep 1335275 = 2002913) B2002913
theorem B1335323 : Blo 888571 1335323 := bstep (se 1 (by rfl) ⟨1001492, by rfl⟩ : syracuseStep 1335323 = 2002985) B2002985
theorem B1335407 : Blo 888571 1335407 := bstep (se 1 (by rfl) ⟨1001555, by rfl⟩ : syracuseStep 1335407 = 2003111) B2003111
theorem B4514291 : Blo 888571 4514291 := bstep (se 1 (by rfl) ⟨3385718, by rfl⟩ : syracuseStep 4514291 = 6771437) B6771437
theorem B8544851 : Blo 888571 8544851 := bstep (se 1 (by rfl) ⟨6408638, by rfl⟩ : syracuseStep 8544851 = 12817277) B12817277
theorem B21619315 : Blo 888571 21619315 := bstep (se 1 (by rfl) ⟨16214486, by rfl⟩ : syracuseStep 21619315 = 32428973) B32428973
theorem B34169687 : Blo 888571 34169687 := bstep (se 1 (by rfl) ⟨25627265, by rfl⟩ : syracuseStep 34169687 = 51254531) B51254531
theorem B25715839 : Blo 888571 25715839 := bstep (se 1 (by rfl) ⟨19286879, by rfl⟩ : syracuseStep 25715839 = 38573759) B38573759
theorem B3007799 : Blo 888571 3007799 := bstep (se 1 (by rfl) ⟨2255849, by rfl⟩ : syracuseStep 3007799 = 4511699) B4511699
theorem B2258057 : Blo 888571 2258057 := bstep (se 2 (by rfl) ⟨846771, by rfl⟩ : syracuseStep 2258057 = 1693543) B1693543
theorem B5078123 : Blo 888571 5078123 := bstep (se 1 (by rfl) ⟨3808592, by rfl⟩ : syracuseStep 5078123 = 7617185) B7617185
theorem B888735 : Blo 888571 888735 := bstep (se 1 (by rfl) ⟨666551, by rfl⟩ : syracuseStep 888735 = 1333103) B1333103
theorem B889883 : Blo 888571 889883 := bstep (se 1 (by rfl) ⟨667412, by rfl⟩ : syracuseStep 889883 = 1334825) B1334825
theorem B890183 : Blo 888571 890183 := bstep (se 1 (by rfl) ⟨667637, by rfl⟩ : syracuseStep 890183 = 1335275) B1335275
theorem B890215 : Blo 888571 890215 := bstep (se 1 (by rfl) ⟨667661, by rfl⟩ : syracuseStep 890215 = 1335323) B1335323
theorem B890271 : Blo 888571 890271 := bstep (se 1 (by rfl) ⟨667703, by rfl⟩ : syracuseStep 890271 = 1335407) B1335407
theorem B22779791 : Blo 888571 22779791 := bstep (se 1 (by rfl) ⟨17084843, by rfl⟩ : syracuseStep 22779791 = 34169687) B34169687
theorem B2005199 : Blo 888571 2005199 := bstep (se 1 (by rfl) ⟨1503899, by rfl⟩ : syracuseStep 2005199 = 3007799) B3007799
theorem B3611785 : Blo 888571 3611785 := bstep (se 2 (by rfl) ⟨1354419, by rfl⟩ : syracuseStep 3611785 = 2708839) B2708839
theorem B3385415 : Blo 888571 3385415 := bstep (se 1 (by rfl) ⟨2539061, by rfl⟩ : syracuseStep 3385415 = 5078123) B5078123
theorem B34287785 : Blo 888571 34287785 := bstep (se 2 (by rfl) ⟨12857919, by rfl⟩ : syracuseStep 34287785 = 25715839) B25715839
theorem B2406017 : Blo 888571 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B17152505 : Blo 888571 17152505 := bstep (se 2 (by rfl) ⟨6432189, by rfl⟩ : syracuseStep 17152505 = 12864379) B12864379
theorem B4572911 : Blo 888571 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B3853597 : Blo 888571 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B8573177 : Blo 888571 8573177 := bstep (se 2 (by rfl) ⟨3214941, by rfl⟩ : syracuseStep 8573177 = 6429883) B6429883
theorem B28825753 : Blo 888571 28825753 := bstep (se 2 (by rfl) ⟨10809657, by rfl⟩ : syracuseStep 28825753 = 21619315) B21619315
theorem B1333673 : Blo 888571 1333673 := bstep (se 2 (by rfl) ⟨500127, by rfl⟩ : syracuseStep 1333673 = 1000255) B1000255
theorem B2254331 : Blo 888571 2254331 := bstep (se 1 (by rfl) ⟨1690748, by rfl⟩ : syracuseStep 2254331 = 3381497) B3381497
theorem B4810823 : Blo 888571 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B3009527 : Blo 888571 3009527 := bstep (se 1 (by rfl) ⟨2257145, by rfl⟩ : syracuseStep 3009527 = 4514291) B4514291
theorem B5696567 : Blo 888571 5696567 := bstep (se 1 (by rfl) ⟨4272425, by rfl⟩ : syracuseStep 5696567 = 8544851) B8544851
theorem B1505371 : Blo 888571 1505371 := bstep (se 1 (by rfl) ⟨1129028, by rfl⟩ : syracuseStep 1505371 = 2258057) B2258057
theorem B5078375 : Blo 888571 5078375 := bstep (se 1 (by rfl) ⟨3808781, by rfl⟩ : syracuseStep 5078375 = 7617563) B7617563
theorem B3048607 : Blo 888571 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B889115 : Blo 888571 889115 := bstep (se 1 (by rfl) ⟨666836, by rfl⟩ : syracuseStep 889115 = 1333673) B1333673
theorem B2006351 : Blo 888571 2006351 := bstep (se 1 (by rfl) ⟨1504763, by rfl⟩ : syracuseStep 2006351 = 3009527) B3009527
theorem B2007161 : Blo 888571 2007161 := bstep (se 2 (by rfl) ⟨752685, by rfl⟩ : syracuseStep 2007161 = 1505371) B1505371
theorem B3385583 : Blo 888571 3385583 := bstep (se 1 (by rfl) ⟨2539187, by rfl⟩ : syracuseStep 3385583 = 5078375) B5078375
theorem B5715451 : Blo 888571 5715451 := bstep (se 1 (by rfl) ⟨4286588, by rfl⟩ : syracuseStep 5715451 = 8573177) B8573177
theorem B15186527 : Blo 888571 15186527 := bstep (se 1 (by rfl) ⟨11389895, by rfl⟩ : syracuseStep 15186527 = 22779791) B22779791
theorem B22858523 : Blo 888571 22858523 := bstep (se 1 (by rfl) ⟨17143892, by rfl⟩ : syracuseStep 22858523 = 34287785) B34287785
theorem B1336799 : Blo 888571 1336799 := bstep (se 1 (by rfl) ⟨1002599, by rfl⟩ : syracuseStep 1336799 = 2005199) B2005199
theorem B5138129 : Blo 888571 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B1502887 : Blo 888571 1502887 := bstep (se 1 (by rfl) ⟨1127165, by rfl⟩ : syracuseStep 1502887 = 2254331) B2254331
theorem B3207215 : Blo 888571 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B2256943 : Blo 888571 2256943 := bstep (se 1 (by rfl) ⟨1692707, by rfl⟩ : syracuseStep 2256943 = 3385415) B3385415
theorem B3797711 : Blo 888571 3797711 := bstep (se 1 (by rfl) ⟨2848283, by rfl⟩ : syracuseStep 3797711 = 5696567) B5696567
theorem B38434337 : Blo 888571 38434337 := bstep (se 2 (by rfl) ⟨14412876, by rfl⟩ : syracuseStep 38434337 = 28825753) B28825753
theorem B1604011 : Blo 888571 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B4815713 : Blo 888571 4815713 := bstep (se 2 (by rfl) ⟨1805892, by rfl⟩ : syracuseStep 4815713 = 3611785) B3611785
theorem B11435003 : Blo 888571 11435003 := bstep (se 1 (by rfl) ⟨8576252, by rfl⟩ : syracuseStep 11435003 = 17152505) B17152505
theorem B8552573 : Blo 888571 8552573 := bstep (se 3 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 8552573 = 3207215) B3207215
theorem B15239015 : Blo 888571 15239015 := bstep (se 1 (by rfl) ⟨11429261, by rfl⟩ : syracuseStep 15239015 = 22858523) B22858523
theorem B2003849 : Blo 888571 2003849 := bstep (se 2 (by rfl) ⟨751443, by rfl⟩ : syracuseStep 2003849 = 1502887) B1502887
theorem B16259237 : Blo 888571 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B891199 : Blo 888571 891199 := bstep (se 1 (by rfl) ⟨668399, by rfl⟩ : syracuseStep 891199 = 1336799) B1336799
theorem B2531807 : Blo 888571 2531807 := bstep (se 1 (by rfl) ⟨1898855, by rfl⟩ : syracuseStep 2531807 = 3797711) B3797711
theorem B2138681 : Blo 888571 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B3425419 : Blo 888571 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B7620601 : Blo 888571 7620601 := bstep (se 2 (by rfl) ⟨2857725, by rfl⟩ : syracuseStep 7620601 = 5715451) B5715451
theorem B7623335 : Blo 888571 7623335 := bstep (se 1 (by rfl) ⟨5717501, by rfl⟩ : syracuseStep 7623335 = 11435003) B11435003
theorem B1337567 : Blo 888571 1337567 := bstep (se 1 (by rfl) ⟨1003175, by rfl⟩ : syracuseStep 1337567 = 2006351) B2006351
theorem B3009257 : Blo 888571 3009257 := bstep (se 2 (by rfl) ⟨1128471, by rfl⟩ : syracuseStep 3009257 = 2256943) B2256943
theorem B1338107 : Blo 888571 1338107 := bstep (se 1 (by rfl) ⟨1003580, by rfl⟩ : syracuseStep 1338107 = 2007161) B2007161
theorem B2257055 : Blo 888571 2257055 := bstep (se 1 (by rfl) ⟨1692791, by rfl⟩ : syracuseStep 2257055 = 3385583) B3385583
theorem B25622891 : Blo 888571 25622891 := bstep (se 1 (by rfl) ⟨19217168, by rfl⟩ : syracuseStep 25622891 = 38434337) B38434337
theorem B10124351 : Blo 888571 10124351 := bstep (se 1 (by rfl) ⟨7593263, by rfl⟩ : syracuseStep 10124351 = 15186527) B15186527
theorem B3210475 : Blo 888571 3210475 := bstep (se 1 (by rfl) ⟨2407856, by rfl⟩ : syracuseStep 3210475 = 4815713) B4815713
theorem B5701715 : Blo 888571 5701715 := bstep (se 1 (by rfl) ⟨4276286, by rfl⟩ : syracuseStep 5701715 = 8552573) B8552573
theorem B10159343 : Blo 888571 10159343 := bstep (se 1 (by rfl) ⟨7619507, by rfl⟩ : syracuseStep 10159343 = 15239015) B15239015
theorem B5703149 : Blo 888571 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B10160801 : Blo 888571 10160801 := bstep (se 2 (by rfl) ⟨3810300, by rfl⟩ : syracuseStep 10160801 = 7620601) B7620601
theorem B5082223 : Blo 888571 5082223 := bstep (se 1 (by rfl) ⟨3811667, by rfl⟩ : syracuseStep 5082223 = 7623335) B7623335
theorem B891711 : Blo 888571 891711 := bstep (se 1 (by rfl) ⟨668783, by rfl⟩ : syracuseStep 891711 = 1337567) B1337567
theorem B2006171 : Blo 888571 2006171 := bstep (se 1 (by rfl) ⟨1504628, by rfl⟩ : syracuseStep 2006171 = 3009257) B3009257
theorem B892071 : Blo 888571 892071 := bstep (se 1 (by rfl) ⟨669053, by rfl⟩ : syracuseStep 892071 = 1338107) B1338107
theorem B17081927 : Blo 888571 17081927 := bstep (se 1 (by rfl) ⟨12811445, by rfl⟩ : syracuseStep 17081927 = 25622891) B25622891
theorem B1687871 : Blo 888571 1687871 := bstep (se 1 (by rfl) ⟨1265903, by rfl⟩ : syracuseStep 1687871 = 2531807) B2531807
theorem B18268901 : Blo 888571 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B4280633 : Blo 888571 4280633 := bstep (se 2 (by rfl) ⟨1605237, by rfl⟩ : syracuseStep 4280633 = 3210475) B3210475
theorem B1335899 : Blo 888571 1335899 := bstep (se 1 (by rfl) ⟨1001924, by rfl⟩ : syracuseStep 1335899 = 2003849) B2003849
theorem B10839491 : Blo 888571 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B1504703 : Blo 888571 1504703 := bstep (se 1 (by rfl) ⟨1128527, by rfl⟩ : syracuseStep 1504703 = 2257055) B2257055
theorem B6749567 : Blo 888571 6749567 := bstep (se 1 (by rfl) ⟨5062175, by rfl⟩ : syracuseStep 6749567 = 10124351) B10124351
theorem B3801143 : Blo 888571 3801143 := bstep (se 1 (by rfl) ⟨2850857, by rfl⟩ : syracuseStep 3801143 = 5701715) B5701715
theorem B2853755 : Blo 888571 2853755 := bstep (se 1 (by rfl) ⟨2140316, by rfl⟩ : syracuseStep 2853755 = 4280633) B4280633
theorem B15208397 : Blo 888571 15208397 := bstep (se 3 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 15208397 = 5703149) B5703149
theorem B890599 : Blo 888571 890599 := bstep (se 1 (by rfl) ⟨667949, by rfl⟩ : syracuseStep 890599 = 1335899) B1335899
theorem B4499711 : Blo 888571 4499711 := bstep (se 1 (by rfl) ⟨3374783, by rfl⟩ : syracuseStep 4499711 = 6749567) B6749567
theorem B1125247 : Blo 888571 1125247 := bstep (se 1 (by rfl) ⟨843935, by rfl⟩ : syracuseStep 1125247 = 1687871) B1687871
theorem B7226327 : Blo 888571 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B11387951 : Blo 888571 11387951 := bstep (se 1 (by rfl) ⟨8540963, by rfl⟩ : syracuseStep 11387951 = 17081927) B17081927
theorem B1003135 : Blo 888571 1003135 := bstep (se 1 (by rfl) ⟨752351, by rfl⟩ : syracuseStep 1003135 = 1504703) B1504703
theorem B12179267 : Blo 888571 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B6772895 : Blo 888571 6772895 := bstep (se 1 (by rfl) ⟨5079671, by rfl⟩ : syracuseStep 6772895 = 10159343) B10159343
theorem B6773867 : Blo 888571 6773867 := bstep (se 1 (by rfl) ⟨5080400, by rfl⟩ : syracuseStep 6773867 = 10160801) B10160801
theorem B6776297 : Blo 888571 6776297 := bstep (se 2 (by rfl) ⟨2541111, by rfl⟩ : syracuseStep 6776297 = 5082223) B5082223
theorem B1337447 : Blo 888571 1337447 := bstep (se 1 (by rfl) ⟨1003085, by rfl⟩ : syracuseStep 1337447 = 2006171) B2006171
theorem B4817551 : Blo 888571 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B1902503 : Blo 888571 1902503 := bstep (se 1 (by rfl) ⟨1426877, by rfl⟩ : syracuseStep 1902503 = 2853755) B2853755
theorem B891631 : Blo 888571 891631 := bstep (se 1 (by rfl) ⟨668723, by rfl⟩ : syracuseStep 891631 = 1337447) B1337447
theorem B2534095 : Blo 888571 2534095 := bstep (se 1 (by rfl) ⟨1900571, by rfl⟩ : syracuseStep 2534095 = 3801143) B3801143
theorem B10138931 : Blo 888571 10138931 := bstep (se 1 (by rfl) ⟨7604198, by rfl⟩ : syracuseStep 10138931 = 15208397) B15208397
theorem B2999807 : Blo 888571 2999807 := bstep (se 1 (by rfl) ⟨2249855, by rfl⟩ : syracuseStep 2999807 = 4499711) B4499711
theorem B7591967 : Blo 888571 7591967 := bstep (se 1 (by rfl) ⟨5693975, by rfl⟩ : syracuseStep 7591967 = 11387951) B11387951
theorem B1500329 : Blo 888571 1500329 := bstep (se 2 (by rfl) ⟨562623, by rfl⟩ : syracuseStep 1500329 = 1125247) B1125247
theorem B8119511 : Blo 888571 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B4515263 : Blo 888571 4515263 := bstep (se 1 (by rfl) ⟨3386447, by rfl⟩ : syracuseStep 4515263 = 6772895) B6772895
theorem B4515911 : Blo 888571 4515911 := bstep (se 1 (by rfl) ⟨3386933, by rfl⟩ : syracuseStep 4515911 = 6773867) B6773867
theorem B1337513 : Blo 888571 1337513 := bstep (se 2 (by rfl) ⟨501567, by rfl⟩ : syracuseStep 1337513 = 1003135) B1003135
theorem B4517531 : Blo 888571 4517531 := bstep (se 1 (by rfl) ⟨3388148, by rfl⟩ : syracuseStep 4517531 = 6776297) B6776297
theorem B6423401 : Blo 888571 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B1999871 : Blo 888571 1999871 := bstep (se 1 (by rfl) ⟨1499903, by rfl⟩ : syracuseStep 1999871 = 2999807) B2999807
theorem B3378793 : Blo 888571 3378793 := bstep (se 2 (by rfl) ⟨1267047, by rfl⟩ : syracuseStep 3378793 = 2534095) B2534095
theorem B5413007 : Blo 888571 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B891675 : Blo 888571 891675 := bstep (se 1 (by rfl) ⟨668756, by rfl⟩ : syracuseStep 891675 = 1337513) B1337513
theorem B6759287 : Blo 888571 6759287 := bstep (se 1 (by rfl) ⟨5069465, by rfl⟩ : syracuseStep 6759287 = 10138931) B10138931
theorem B5061311 : Blo 888571 5061311 := bstep (se 1 (by rfl) ⟨3795983, by rfl⟩ : syracuseStep 5061311 = 7591967) B7591967
theorem B1000219 : Blo 888571 1000219 := bstep (se 1 (by rfl) ⟨750164, by rfl⟩ : syracuseStep 1000219 = 1500329) B1500329
theorem B1268335 : Blo 888571 1268335 := bstep (se 1 (by rfl) ⟨951251, by rfl⟩ : syracuseStep 1268335 = 1902503) B1902503
theorem B3010175 : Blo 888571 3010175 := bstep (se 1 (by rfl) ⟨2257631, by rfl⟩ : syracuseStep 3010175 = 4515263) B4515263
theorem B3010607 : Blo 888571 3010607 := bstep (se 1 (by rfl) ⟨2257955, by rfl⟩ : syracuseStep 3010607 = 4515911) B4515911
theorem B3011687 : Blo 888571 3011687 := bstep (se 1 (by rfl) ⟨2258765, by rfl⟩ : syracuseStep 3011687 = 4517531) B4517531
theorem B3608671 : Blo 888571 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B2006783 : Blo 888571 2006783 := bstep (se 1 (by rfl) ⟨1505087, by rfl⟩ : syracuseStep 2006783 = 3010175) B3010175
theorem B2007071 : Blo 888571 2007071 := bstep (se 1 (by rfl) ⟨1505303, by rfl⟩ : syracuseStep 2007071 = 3010607) B3010607
theorem B2007791 : Blo 888571 2007791 := bstep (se 1 (by rfl) ⟨1505843, by rfl⟩ : syracuseStep 2007791 = 3011687) B3011687
theorem B4505057 : Blo 888571 4505057 := bstep (se 2 (by rfl) ⟨1689396, by rfl⟩ : syracuseStep 4505057 = 3378793) B3378793
theorem B4506191 : Blo 888571 4506191 := bstep (se 1 (by rfl) ⟨3379643, by rfl⟩ : syracuseStep 4506191 = 6759287) B6759287
theorem B1691113 : Blo 888571 1691113 := bstep (se 2 (by rfl) ⟨634167, by rfl⟩ : syracuseStep 1691113 = 1268335) B1268335
theorem B4282267 : Blo 888571 4282267 := bstep (se 1 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 4282267 = 6423401) B6423401
theorem B1333247 : Blo 888571 1333247 := bstep (se 1 (by rfl) ⟨999935, by rfl⟩ : syracuseStep 1333247 = 1999871) B1999871
theorem B1333625 : Blo 888571 1333625 := bstep (se 2 (by rfl) ⟨500109, by rfl⟩ : syracuseStep 1333625 = 1000219) B1000219
theorem B3374207 : Blo 888571 3374207 := bstep (se 1 (by rfl) ⟨2530655, by rfl⟩ : syracuseStep 3374207 = 5061311) B5061311
theorem B888831 : Blo 888571 888831 := bstep (se 1 (by rfl) ⟨666623, by rfl⟩ : syracuseStep 888831 = 1333247) B1333247
theorem B889083 : Blo 888571 889083 := bstep (se 1 (by rfl) ⟨666812, by rfl⟩ : syracuseStep 889083 = 1333625) B1333625
theorem B5709689 : Blo 888571 5709689 := bstep (se 2 (by rfl) ⟨2141133, by rfl⟩ : syracuseStep 5709689 = 4282267) B4282267
theorem B2249471 : Blo 888571 2249471 := bstep (se 1 (by rfl) ⟨1687103, by rfl⟩ : syracuseStep 2249471 = 3374207) B3374207
theorem B3003371 : Blo 888571 3003371 := bstep (se 1 (by rfl) ⟨2252528, by rfl⟩ : syracuseStep 3003371 = 4505057) B4505057
theorem B3004127 : Blo 888571 3004127 := bstep (se 1 (by rfl) ⟨2253095, by rfl⟩ : syracuseStep 3004127 = 4506191) B4506191
theorem B2254817 : Blo 888571 2254817 := bstep (se 2 (by rfl) ⟨845556, by rfl⟩ : syracuseStep 2254817 = 1691113) B1691113
theorem B1337855 : Blo 888571 1337855 := bstep (se 1 (by rfl) ⟨1003391, by rfl⟩ : syracuseStep 1337855 = 2006783) B2006783
theorem B1338047 : Blo 888571 1338047 := bstep (se 1 (by rfl) ⟨1003535, by rfl⟩ : syracuseStep 1338047 = 2007071) B2007071
theorem B4811561 : Blo 888571 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B1338527 : Blo 888571 1338527 := bstep (se 1 (by rfl) ⟨1003895, by rfl⟩ : syracuseStep 1338527 = 2007791) B2007791
theorem B2002247 : Blo 888571 2002247 := bstep (se 1 (by rfl) ⟨1501685, by rfl⟩ : syracuseStep 2002247 = 3003371) B3003371
theorem B2002751 : Blo 888571 2002751 := bstep (se 1 (by rfl) ⟨1502063, by rfl⟩ : syracuseStep 2002751 = 3004127) B3004127
theorem B3806459 : Blo 888571 3806459 := bstep (se 1 (by rfl) ⟨2854844, by rfl⟩ : syracuseStep 3806459 = 5709689) B5709689
theorem B891903 : Blo 888571 891903 := bstep (se 1 (by rfl) ⟨668927, by rfl⟩ : syracuseStep 891903 = 1337855) B1337855
theorem B892031 : Blo 888571 892031 := bstep (se 1 (by rfl) ⟨669023, by rfl⟩ : syracuseStep 892031 = 1338047) B1338047
theorem B892351 : Blo 888571 892351 := bstep (se 1 (by rfl) ⟨669263, by rfl⟩ : syracuseStep 892351 = 1338527) B1338527
theorem B1499647 : Blo 888571 1499647 := bstep (se 1 (by rfl) ⟨1124735, by rfl⟩ : syracuseStep 1499647 = 2249471) B2249471
theorem B1503211 : Blo 888571 1503211 := bstep (se 1 (by rfl) ⟨1127408, by rfl⟩ : syracuseStep 1503211 = 2254817) B2254817
theorem B3207707 : Blo 888571 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B1999529 : Blo 888571 1999529 := bstep (se 2 (by rfl) ⟨749823, by rfl⟩ : syracuseStep 1999529 = 1499647) B1499647
theorem B2004281 : Blo 888571 2004281 := bstep (se 2 (by rfl) ⟨751605, by rfl⟩ : syracuseStep 2004281 = 1503211) B1503211
theorem B2138471 : Blo 888571 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B2537639 : Blo 888571 2537639 := bstep (se 1 (by rfl) ⟨1903229, by rfl⟩ : syracuseStep 2537639 = 3806459) B3806459
theorem B1334831 : Blo 888571 1334831 := bstep (se 1 (by rfl) ⟨1001123, by rfl⟩ : syracuseStep 1334831 = 2002247) B2002247
theorem B1335167 : Blo 888571 1335167 := bstep (se 1 (by rfl) ⟨1001375, by rfl⟩ : syracuseStep 1335167 = 2002751) B2002751
theorem B889887 : Blo 888571 889887 := bstep (se 1 (by rfl) ⟨667415, by rfl⟩ : syracuseStep 889887 = 1334831) B1334831
theorem B890111 : Blo 888571 890111 := bstep (se 1 (by rfl) ⟨667583, by rfl⟩ : syracuseStep 890111 = 1335167) B1335167
theorem B1425647 : Blo 888571 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B1691759 : Blo 888571 1691759 := bstep (se 1 (by rfl) ⟨1268819, by rfl⟩ : syracuseStep 1691759 = 2537639) B2537639
theorem B1333019 : Blo 888571 1333019 := bstep (se 1 (by rfl) ⟨999764, by rfl⟩ : syracuseStep 1333019 = 1999529) B1999529
theorem B1336187 : Blo 888571 1336187 := bstep (se 1 (by rfl) ⟨1002140, by rfl⟩ : syracuseStep 1336187 = 2004281) B2004281
theorem B3801725 : Blo 888571 3801725 := bstep (se 3 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 3801725 = 1425647) B1425647
theorem B888679 : Blo 888571 888679 := bstep (se 1 (by rfl) ⟨666509, by rfl⟩ : syracuseStep 888679 = 1333019) B1333019
theorem B890791 : Blo 888571 890791 := bstep (se 1 (by rfl) ⟨668093, by rfl⟩ : syracuseStep 890791 = 1336187) B1336187
theorem B1127839 : Blo 888571 1127839 := bstep (se 1 (by rfl) ⟨845879, by rfl⟩ : syracuseStep 1127839 = 1691759) B1691759
theorem B2534483 : Blo 888571 2534483 := bstep (se 1 (by rfl) ⟨1900862, by rfl⟩ : syracuseStep 2534483 = 3801725) B3801725
theorem B1503785 : Blo 888571 1503785 := bstep (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) B1127839
theorem B1689655 : Blo 888571 1689655 := bstep (se 1 (by rfl) ⟨1267241, by rfl⟩ : syracuseStep 1689655 = 2534483) B2534483
theorem B1002523 : Blo 888571 1002523 := bstep (se 1 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 1002523 = 1503785) B1503785
theorem B2252873 : Blo 888571 2252873 := bstep (se 2 (by rfl) ⟨844827, by rfl⟩ : syracuseStep 2252873 = 1689655) B1689655
theorem B1336697 : Blo 888571 1336697 := bstep (se 2 (by rfl) ⟨501261, by rfl⟩ : syracuseStep 1336697 = 1002523) B1002523
theorem B891131 : Blo 888571 891131 := bstep (se 1 (by rfl) ⟨668348, by rfl⟩ : syracuseStep 891131 = 1336697) B1336697
theorem B1501915 : Blo 888571 1501915 := bstep (se 1 (by rfl) ⟨1126436, by rfl⟩ : syracuseStep 1501915 = 2252873) B2252873
theorem B2002553 : Blo 888571 2002553 := bstep (se 2 (by rfl) ⟨750957, by rfl⟩ : syracuseStep 2002553 = 1501915) B1501915
theorem B1335035 : Blo 888571 1335035 := bstep (se 1 (by rfl) ⟨1001276, by rfl⟩ : syracuseStep 1335035 = 2002553) B2002553
theorem B890023 : Blo 888571 890023 := bstep (se 1 (by rfl) ⟨667517, by rfl⟩ : syracuseStep 890023 = 1335035) B1335035

theorem C0 (j : ℕ) (h1 : 222142 ≤ j) (h2 : j ≤ 222841) : Blo 888571 (4 * j + 3) := by
  interval_cases j
  · exact B888571
  · exact B888575
  · exact B888579
  · exact B888583
  · exact B888587
  · exact B888591
  · exact B888595
  · exact B888599
  · exact B888603
  · exact B888607
  · exact B888611
  · exact B888615
  · exact B888619
  · exact B888623
  · exact B888627
  · exact B888631
  · exact B888635
  · exact B888639
  · exact B888643
  · exact B888647
  · exact B888651
  · exact B888655
  · exact B888659
  · exact B888663
  · exact B888667
  · exact B888671
  · exact B888675
  · exact B888679
  · exact B888683
  · exact B888687
  · exact B888691
  · exact B888695
  · exact B888699
  · exact B888703
  · exact B888707
  · exact B888711
  · exact B888715
  · exact B888719
  · exact B888723
  · exact B888727
  · exact B888731
  · exact B888735
  · exact B888739
  · exact B888743
  · exact B888747
  · exact B888751
  · exact B888755
  · exact B888759
  · exact B888763
  · exact B888767
  · exact B888771
  · exact B888775
  · exact B888779
  · exact B888783
  · exact B888787
  · exact B888791
  · exact B888795
  · exact B888799
  · exact B888803
  · exact B888807
  · exact B888811
  · exact B888815
  · exact B888819
  · exact B888823
  · exact B888827
  · exact B888831
  · exact B888835
  · exact B888839
  · exact B888843
  · exact B888847
  · exact B888851
  · exact B888855
  · exact B888859
  · exact B888863
  · exact B888867
  · exact B888871
  · exact B888875
  · exact B888879
  · exact B888883
  · exact B888887
  · exact B888891
  · exact B888895
  · exact B888899
  · exact B888903
  · exact B888907
  · exact B888911
  · exact B888915
  · exact B888919
  · exact B888923
  · exact B888927
  · exact B888931
  · exact B888935
  · exact B888939
  · exact B888943
  · exact B888947
  · exact B888951
  · exact B888955
  · exact B888959
  · exact B888963
  · exact B888967
  · exact B888971
  · exact B888975
  · exact B888979
  · exact B888983
  · exact B888987
  · exact B888991
  · exact B888995
  · exact B888999
  · exact B889003
  · exact B889007
  · exact B889011
  · exact B889015
  · exact B889019
  · exact B889023
  · exact B889027
  · exact B889031
  · exact B889035
  · exact B889039
  · exact B889043
  · exact B889047
  · exact B889051
  · exact B889055
  · exact B889059
  · exact B889063
  · exact B889067
  · exact B889071
  · exact B889075
  · exact B889079
  · exact B889083
  · exact B889087
  · exact B889091
  · exact B889095
  · exact B889099
  · exact B889103
  · exact B889107
  · exact B889111
  · exact B889115
  · exact B889119
  · exact B889123
  · exact B889127
  · exact B889131
  · exact B889135
  · exact B889139
  · exact B889143
  · exact B889147
  · exact B889151
  · exact B889155
  · exact B889159
  · exact B889163
  · exact B889167
  · exact B889171
  · exact B889175
  · exact B889179
  · exact B889183
  · exact B889187
  · exact B889191
  · exact B889195
  · exact B889199
  · exact B889203
  · exact B889207
  · exact B889211
  · exact B889215
  · exact B889219
  · exact B889223
  · exact B889227
  · exact B889231
  · exact B889235
  · exact B889239
  · exact B889243
  · exact B889247
  · exact B889251
  · exact B889255
  · exact B889259
  · exact B889263
  · exact B889267
  · exact B889271
  · exact B889275
  · exact B889279
  · exact B889283
  · exact B889287
  · exact B889291
  · exact B889295
  · exact B889299
  · exact B889303
  · exact B889307
  · exact B889311
  · exact B889315
  · exact B889319
  · exact B889323
  · exact B889327
  · exact B889331
  · exact B889335
  · exact B889339
  · exact B889343
  · exact B889347
  · exact B889351
  · exact B889355
  · exact B889359
  · exact B889363
  · exact B889367
  · exact B889371
  · exact B889375
  · exact B889379
  · exact B889383
  · exact B889387
  · exact B889391
  · exact B889395
  · exact B889399
  · exact B889403
  · exact B889407
  · exact B889411
  · exact B889415
  · exact B889419
  · exact B889423
  · exact B889427
  · exact B889431
  · exact B889435
  · exact B889439
  · exact B889443
  · exact B889447
  · exact B889451
  · exact B889455
  · exact B889459
  · exact B889463
  · exact B889467
  · exact B889471
  · exact B889475
  · exact B889479
  · exact B889483
  · exact B889487
  · exact B889491
  · exact B889495
  · exact B889499
  · exact B889503
  · exact B889507
  · exact B889511
  · exact B889515
  · exact B889519
  · exact B889523
  · exact B889527
  · exact B889531
  · exact B889535
  · exact B889539
  · exact B889543
  · exact B889547
  · exact B889551
  · exact B889555
  · exact B889559
  · exact B889563
  · exact B889567
  · exact B889571
  · exact B889575
  · exact B889579
  · exact B889583
  · exact B889587
  · exact B889591
  · exact B889595
  · exact B889599
  · exact B889603
  · exact B889607
  · exact B889611
  · exact B889615
  · exact B889619
  · exact B889623
  · exact B889627
  · exact B889631
  · exact B889635
  · exact B889639
  · exact B889643
  · exact B889647
  · exact B889651
  · exact B889655
  · exact B889659
  · exact B889663
  · exact B889667
  · exact B889671
  · exact B889675
  · exact B889679
  · exact B889683
  · exact B889687
  · exact B889691
  · exact B889695
  · exact B889699
  · exact B889703
  · exact B889707
  · exact B889711
  · exact B889715
  · exact B889719
  · exact B889723
  · exact B889727
  · exact B889731
  · exact B889735
  · exact B889739
  · exact B889743
  · exact B889747
  · exact B889751
  · exact B889755
  · exact B889759
  · exact B889763
  · exact B889767
  · exact B889771
  · exact B889775
  · exact B889779
  · exact B889783
  · exact B889787
  · exact B889791
  · exact B889795
  · exact B889799
  · exact B889803
  · exact B889807
  · exact B889811
  · exact B889815
  · exact B889819
  · exact B889823
  · exact B889827
  · exact B889831
  · exact B889835
  · exact B889839
  · exact B889843
  · exact B889847
  · exact B889851
  · exact B889855
  · exact B889859
  · exact B889863
  · exact B889867
  · exact B889871
  · exact B889875
  · exact B889879
  · exact B889883
  · exact B889887
  · exact B889891
  · exact B889895
  · exact B889899
  · exact B889903
  · exact B889907
  · exact B889911
  · exact B889915
  · exact B889919
  · exact B889923
  · exact B889927
  · exact B889931
  · exact B889935
  · exact B889939
  · exact B889943
  · exact B889947
  · exact B889951
  · exact B889955
  · exact B889959
  · exact B889963
  · exact B889967
  · exact B889971
  · exact B889975
  · exact B889979
  · exact B889983
  · exact B889987
  · exact B889991
  · exact B889995
  · exact B889999
  · exact B890003
  · exact B890007
  · exact B890011
  · exact B890015
  · exact B890019
  · exact B890023
  · exact B890027
  · exact B890031
  · exact B890035
  · exact B890039
  · exact B890043
  · exact B890047
  · exact B890051
  · exact B890055
  · exact B890059
  · exact B890063
  · exact B890067
  · exact B890071
  · exact B890075
  · exact B890079
  · exact B890083
  · exact B890087
  · exact B890091
  · exact B890095
  · exact B890099
  · exact B890103
  · exact B890107
  · exact B890111
  · exact B890115
  · exact B890119
  · exact B890123
  · exact B890127
  · exact B890131
  · exact B890135
  · exact B890139
  · exact B890143
  · exact B890147
  · exact B890151
  · exact B890155
  · exact B890159
  · exact B890163
  · exact B890167
  · exact B890171
  · exact B890175
  · exact B890179
  · exact B890183
  · exact B890187
  · exact B890191
  · exact B890195
  · exact B890199
  · exact B890203
  · exact B890207
  · exact B890211
  · exact B890215
  · exact B890219
  · exact B890223
  · exact B890227
  · exact B890231
  · exact B890235
  · exact B890239
  · exact B890243
  · exact B890247
  · exact B890251
  · exact B890255
  · exact B890259
  · exact B890263
  · exact B890267
  · exact B890271
  · exact B890275
  · exact B890279
  · exact B890283
  · exact B890287
  · exact B890291
  · exact B890295
  · exact B890299
  · exact B890303
  · exact B890307
  · exact B890311
  · exact B890315
  · exact B890319
  · exact B890323
  · exact B890327
  · exact B890331
  · exact B890335
  · exact B890339
  · exact B890343
  · exact B890347
  · exact B890351
  · exact B890355
  · exact B890359
  · exact B890363
  · exact B890367
  · exact B890371
  · exact B890375
  · exact B890379
  · exact B890383
  · exact B890387
  · exact B890391
  · exact B890395
  · exact B890399
  · exact B890403
  · exact B890407
  · exact B890411
  · exact B890415
  · exact B890419
  · exact B890423
  · exact B890427
  · exact B890431
  · exact B890435
  · exact B890439
  · exact B890443
  · exact B890447
  · exact B890451
  · exact B890455
  · exact B890459
  · exact B890463
  · exact B890467
  · exact B890471
  · exact B890475
  · exact B890479
  · exact B890483
  · exact B890487
  · exact B890491
  · exact B890495
  · exact B890499
  · exact B890503
  · exact B890507
  · exact B890511
  · exact B890515
  · exact B890519
  · exact B890523
  · exact B890527
  · exact B890531
  · exact B890535
  · exact B890539
  · exact B890543
  · exact B890547
  · exact B890551
  · exact B890555
  · exact B890559
  · exact B890563
  · exact B890567
  · exact B890571
  · exact B890575
  · exact B890579
  · exact B890583
  · exact B890587
  · exact B890591
  · exact B890595
  · exact B890599
  · exact B890603
  · exact B890607
  · exact B890611
  · exact B890615
  · exact B890619
  · exact B890623
  · exact B890627
  · exact B890631
  · exact B890635
  · exact B890639
  · exact B890643
  · exact B890647
  · exact B890651
  · exact B890655
  · exact B890659
  · exact B890663
  · exact B890667
  · exact B890671
  · exact B890675
  · exact B890679
  · exact B890683
  · exact B890687
  · exact B890691
  · exact B890695
  · exact B890699
  · exact B890703
  · exact B890707
  · exact B890711
  · exact B890715
  · exact B890719
  · exact B890723
  · exact B890727
  · exact B890731
  · exact B890735
  · exact B890739
  · exact B890743
  · exact B890747
  · exact B890751
  · exact B890755
  · exact B890759
  · exact B890763
  · exact B890767
  · exact B890771
  · exact B890775
  · exact B890779
  · exact B890783
  · exact B890787
  · exact B890791
  · exact B890795
  · exact B890799
  · exact B890803
  · exact B890807
  · exact B890811
  · exact B890815
  · exact B890819
  · exact B890823
  · exact B890827
  · exact B890831
  · exact B890835
  · exact B890839
  · exact B890843
  · exact B890847
  · exact B890851
  · exact B890855
  · exact B890859
  · exact B890863
  · exact B890867
  · exact B890871
  · exact B890875
  · exact B890879
  · exact B890883
  · exact B890887
  · exact B890891
  · exact B890895
  · exact B890899
  · exact B890903
  · exact B890907
  · exact B890911
  · exact B890915
  · exact B890919
  · exact B890923
  · exact B890927
  · exact B890931
  · exact B890935
  · exact B890939
  · exact B890943
  · exact B890947
  · exact B890951
  · exact B890955
  · exact B890959
  · exact B890963
  · exact B890967
  · exact B890971
  · exact B890975
  · exact B890979
  · exact B890983
  · exact B890987
  · exact B890991
  · exact B890995
  · exact B890999
  · exact B891003
  · exact B891007
  · exact B891011
  · exact B891015
  · exact B891019
  · exact B891023
  · exact B891027
  · exact B891031
  · exact B891035
  · exact B891039
  · exact B891043
  · exact B891047
  · exact B891051
  · exact B891055
  · exact B891059
  · exact B891063
  · exact B891067
  · exact B891071
  · exact B891075
  · exact B891079
  · exact B891083
  · exact B891087
  · exact B891091
  · exact B891095
  · exact B891099
  · exact B891103
  · exact B891107
  · exact B891111
  · exact B891115
  · exact B891119
  · exact B891123
  · exact B891127
  · exact B891131
  · exact B891135
  · exact B891139
  · exact B891143
  · exact B891147
  · exact B891151
  · exact B891155
  · exact B891159
  · exact B891163
  · exact B891167
  · exact B891171
  · exact B891175
  · exact B891179
  · exact B891183
  · exact B891187
  · exact B891191
  · exact B891195
  · exact B891199
  · exact B891203
  · exact B891207
  · exact B891211
  · exact B891215
  · exact B891219
  · exact B891223
  · exact B891227
  · exact B891231
  · exact B891235
  · exact B891239
  · exact B891243
  · exact B891247
  · exact B891251
  · exact B891255
  · exact B891259
  · exact B891263
  · exact B891267
  · exact B891271
  · exact B891275
  · exact B891279
  · exact B891283
  · exact B891287
  · exact B891291
  · exact B891295
  · exact B891299
  · exact B891303
  · exact B891307
  · exact B891311
  · exact B891315
  · exact B891319
  · exact B891323
  · exact B891327
  · exact B891331
  · exact B891335
  · exact B891339
  · exact B891343
  · exact B891347
  · exact B891351
  · exact B891355
  · exact B891359
  · exact B891363
  · exact B891367

theorem C1 (j : ℕ) (h1 : 222842 ≤ j) (h2 : j ≤ 223142) : Blo 888571 (4 * j + 3) := by
  interval_cases j
  · exact B891371
  · exact B891375
  · exact B891379
  · exact B891383
  · exact B891387
  · exact B891391
  · exact B891395
  · exact B891399
  · exact B891403
  · exact B891407
  · exact B891411
  · exact B891415
  · exact B891419
  · exact B891423
  · exact B891427
  · exact B891431
  · exact B891435
  · exact B891439
  · exact B891443
  · exact B891447
  · exact B891451
  · exact B891455
  · exact B891459
  · exact B891463
  · exact B891467
  · exact B891471
  · exact B891475
  · exact B891479
  · exact B891483
  · exact B891487
  · exact B891491
  · exact B891495
  · exact B891499
  · exact B891503
  · exact B891507
  · exact B891511
  · exact B891515
  · exact B891519
  · exact B891523
  · exact B891527
  · exact B891531
  · exact B891535
  · exact B891539
  · exact B891543
  · exact B891547
  · exact B891551
  · exact B891555
  · exact B891559
  · exact B891563
  · exact B891567
  · exact B891571
  · exact B891575
  · exact B891579
  · exact B891583
  · exact B891587
  · exact B891591
  · exact B891595
  · exact B891599
  · exact B891603
  · exact B891607
  · exact B891611
  · exact B891615
  · exact B891619
  · exact B891623
  · exact B891627
  · exact B891631
  · exact B891635
  · exact B891639
  · exact B891643
  · exact B891647
  · exact B891651
  · exact B891655
  · exact B891659
  · exact B891663
  · exact B891667
  · exact B891671
  · exact B891675
  · exact B891679
  · exact B891683
  · exact B891687
  · exact B891691
  · exact B891695
  · exact B891699
  · exact B891703
  · exact B891707
  · exact B891711
  · exact B891715
  · exact B891719
  · exact B891723
  · exact B891727
  · exact B891731
  · exact B891735
  · exact B891739
  · exact B891743
  · exact B891747
  · exact B891751
  · exact B891755
  · exact B891759
  · exact B891763
  · exact B891767
  · exact B891771
  · exact B891775
  · exact B891779
  · exact B891783
  · exact B891787
  · exact B891791
  · exact B891795
  · exact B891799
  · exact B891803
  · exact B891807
  · exact B891811
  · exact B891815
  · exact B891819
  · exact B891823
  · exact B891827
  · exact B891831
  · exact B891835
  · exact B891839
  · exact B891843
  · exact B891847
  · exact B891851
  · exact B891855
  · exact B891859
  · exact B891863
  · exact B891867
  · exact B891871
  · exact B891875
  · exact B891879
  · exact B891883
  · exact B891887
  · exact B891891
  · exact B891895
  · exact B891899
  · exact B891903
  · exact B891907
  · exact B891911
  · exact B891915
  · exact B891919
  · exact B891923
  · exact B891927
  · exact B891931
  · exact B891935
  · exact B891939
  · exact B891943
  · exact B891947
  · exact B891951
  · exact B891955
  · exact B891959
  · exact B891963
  · exact B891967
  · exact B891971
  · exact B891975
  · exact B891979
  · exact B891983
  · exact B891987
  · exact B891991
  · exact B891995
  · exact B891999
  · exact B892003
  · exact B892007
  · exact B892011
  · exact B892015
  · exact B892019
  · exact B892023
  · exact B892027
  · exact B892031
  · exact B892035
  · exact B892039
  · exact B892043
  · exact B892047
  · exact B892051
  · exact B892055
  · exact B892059
  · exact B892063
  · exact B892067
  · exact B892071
  · exact B892075
  · exact B892079
  · exact B892083
  · exact B892087
  · exact B892091
  · exact B892095
  · exact B892099
  · exact B892103
  · exact B892107
  · exact B892111
  · exact B892115
  · exact B892119
  · exact B892123
  · exact B892127
  · exact B892131
  · exact B892135
  · exact B892139
  · exact B892143
  · exact B892147
  · exact B892151
  · exact B892155
  · exact B892159
  · exact B892163
  · exact B892167
  · exact B892171
  · exact B892175
  · exact B892179
  · exact B892183
  · exact B892187
  · exact B892191
  · exact B892195
  · exact B892199
  · exact B892203
  · exact B892207
  · exact B892211
  · exact B892215
  · exact B892219
  · exact B892223
  · exact B892227
  · exact B892231
  · exact B892235
  · exact B892239
  · exact B892243
  · exact B892247
  · exact B892251
  · exact B892255
  · exact B892259
  · exact B892263
  · exact B892267
  · exact B892271
  · exact B892275
  · exact B892279
  · exact B892283
  · exact B892287
  · exact B892291
  · exact B892295
  · exact B892299
  · exact B892303
  · exact B892307
  · exact B892311
  · exact B892315
  · exact B892319
  · exact B892323
  · exact B892327
  · exact B892331
  · exact B892335
  · exact B892339
  · exact B892343
  · exact B892347
  · exact B892351
  · exact B892355
  · exact B892359
  · exact B892363
  · exact B892367
  · exact B892371
  · exact B892375
  · exact B892379
  · exact B892383
  · exact B892387
  · exact B892391
  · exact B892395
  · exact B892399
  · exact B892403
  · exact B892407
  · exact B892411
  · exact B892415
  · exact B892419
  · exact B892423
  · exact B892427
  · exact B892431
  · exact B892435
  · exact B892439
  · exact B892443
  · exact B892447
  · exact B892451
  · exact B892455
  · exact B892459
  · exact B892463
  · exact B892467
  · exact B892471
  · exact B892475
  · exact B892479
  · exact B892483
  · exact B892487
  · exact B892491
  · exact B892495
  · exact B892499
  · exact B892503
  · exact B892507
  · exact B892511
  · exact B892515
  · exact B892519
  · exact B892523
  · exact B892527
  · exact B892531
  · exact B892535
  · exact B892539
  · exact B892543
  · exact B892547
  · exact B892551
  · exact B892555
  · exact B892559
  · exact B892563
  · exact B892567
  · exact B892571

theorem solution (m : ℕ) (hlo : 888571 ≤ m) (hhi : m ≤ 892571) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 222142 ≤ j := by omega
    have hj2 : j ≤ 223142 := by omega
    have hb : Blo 888571 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 222842 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
