-- Prove2me | solution 1 for syracuse_descends_range_1232434_1234434
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:03.682862+00:00
-- url     : https://prove2.me/submissions/37540c8c-bc30-4695-b1ae-e17e3c8ac01d

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


theorem B3514373 : Blo 1232434 3514373 := bbase (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) (by norm_num)
theorem B2777093 : Blo 1232434 2777093 := bbase (se 4 (by rfl) ⟨260352, by rfl⟩ : syracuseStep 2777093 = 520705) (by norm_num)
theorem B1851413 : Blo 1232434 1851413 := bbase (se 6 (by rfl) ⟨43392, by rfl⟩ : syracuseStep 1851413 = 86785) (by norm_num)
theorem B1851437 : Blo 1232434 1851437 := bbase (se 3 (by rfl) ⟨347144, by rfl⟩ : syracuseStep 1851437 = 694289) (by norm_num)
theorem B3121213 : Blo 1232434 3121213 := bbase (se 3 (by rfl) ⟨585227, by rfl⟩ : syracuseStep 3121213 = 1170455) (by norm_num)
theorem B2080829 : Blo 1232434 2080829 := bbase (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) (by norm_num)
theorem B3334213 : Blo 1232434 3334213 := bbase (se 4 (by rfl) ⟨312582, by rfl⟩ : syracuseStep 3334213 = 625165) (by norm_num)
theorem B1851461 : Blo 1232434 1851461 := bbase (se 4 (by rfl) ⟨173574, by rfl⟩ : syracuseStep 1851461 = 347149) (by norm_num)
theorem B2777165 : Blo 1232434 2777165 := bbase (se 3 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 2777165 = 1041437) (by norm_num)
theorem B1851485 : Blo 1232434 1851485 := bbase (se 3 (by rfl) ⟨347153, by rfl⟩ : syracuseStep 1851485 = 694307) (by norm_num)
theorem B2252909 : Blo 1232434 2252909 := bbase (se 3 (by rfl) ⟨422420, by rfl⟩ : syracuseStep 2252909 = 844841) (by norm_num)
theorem B1851509 : Blo 1232434 1851509 := bbase (se 5 (by rfl) ⟨86789, by rfl⟩ : syracuseStep 1851509 = 173579) (by norm_num)
theorem B1974413 : Blo 1232434 1974413 := bbase (se 3 (by rfl) ⟨370202, by rfl⟩ : syracuseStep 1974413 = 740405) (by norm_num)
theorem B1851533 : Blo 1232434 1851533 := bbase (se 3 (by rfl) ⟨347162, by rfl⟩ : syracuseStep 1851533 = 694325) (by norm_num)
theorem B2777237 : Blo 1232434 2777237 := bbase (se 6 (by rfl) ⟨65091, by rfl⟩ : syracuseStep 2777237 = 130183) (by norm_num)
theorem B1851557 : Blo 1232434 1851557 := bbase (se 4 (by rfl) ⟨173583, by rfl⟩ : syracuseStep 1851557 = 347167) (by norm_num)
theorem B3121325 : Blo 1232434 3121325 := bbase (se 3 (by rfl) ⟨585248, by rfl⟩ : syracuseStep 3121325 = 1170497) (by norm_num)
theorem B2080957 : Blo 1232434 2080957 := bbase (se 3 (by rfl) ⟨390179, by rfl⟩ : syracuseStep 2080957 = 780359) (by norm_num)
theorem B1851581 : Blo 1232434 1851581 := bbase (se 3 (by rfl) ⟨347171, by rfl⟩ : syracuseStep 1851581 = 694343) (by norm_num)
theorem B1482953 : Blo 1232434 1482953 := bbase (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) (by norm_num)
theorem B6004949 : Blo 1232434 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B1851605 : Blo 1232434 1851605 := bbase (se 7 (by rfl) ⟨21698, by rfl⟩ : syracuseStep 1851605 = 43397) (by norm_num)
theorem B2777309 : Blo 1232434 2777309 := bbase (se 3 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 2777309 = 1041491) (by norm_num)
theorem B1851629 : Blo 1232434 1851629 := bbase (se 3 (by rfl) ⟨347180, by rfl⟩ : syracuseStep 1851629 = 694361) (by norm_num)
theorem B2343181 : Blo 1232434 2343181 := bbase (se 3 (by rfl) ⟨439346, by rfl⟩ : syracuseStep 2343181 = 878693) (by norm_num)
theorem B2081045 : Blo 1232434 2081045 := bbase (se 6 (by rfl) ⟨48774, by rfl⟩ : syracuseStep 2081045 = 97549) (by norm_num)
theorem B2777381 : Blo 1232434 2777381 := bbase (se 4 (by rfl) ⟨260379, by rfl⟩ : syracuseStep 2777381 = 520759) (by norm_num)
theorem B4686133 : Blo 1232434 4686133 := bbase (se 5 (by rfl) ⟨219662, by rfl⟩ : syracuseStep 4686133 = 439325) (by norm_num)
theorem B8896853 : Blo 1232434 8896853 := bbase (se 10 (by rfl) ⟨13032, by rfl⟩ : syracuseStep 8896853 = 26065) (by norm_num)
theorem B4997477 : Blo 1232434 4997477 := bbase (se 4 (by rfl) ⟨468513, by rfl⟩ : syracuseStep 4997477 = 937027) (by norm_num)
theorem B3121517 : Blo 1232434 3121517 := bbase (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) (by norm_num)
theorem B2777453 : Blo 1232434 2777453 := bbase (se 3 (by rfl) ⟨520772, by rfl⟩ : syracuseStep 2777453 = 1041545) (by norm_num)
theorem B4161941 : Blo 1232434 4161941 := bbase (se 6 (by rfl) ⟨97545, by rfl⟩ : syracuseStep 4161941 = 195091) (by norm_num)
theorem B2081173 : Blo 1232434 2081173 := bbase (se 6 (by rfl) ⟨48777, by rfl⟩ : syracuseStep 2081173 = 97555) (by norm_num)
theorem B2343325 : Blo 1232434 2343325 := bbase (se 3 (by rfl) ⟨439373, by rfl⟩ : syracuseStep 2343325 = 878747) (by norm_num)
theorem B2081261 : Blo 1232434 2081261 := bbase (se 3 (by rfl) ⟨390236, by rfl⟩ : syracuseStep 2081261 = 780473) (by norm_num)
theorem B2253349 : Blo 1232434 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B2343485 : Blo 1232434 2343485 := bbase (se 3 (by rfl) ⟨439403, by rfl⟩ : syracuseStep 2343485 = 878807) (by norm_num)
theorem B1876565 : Blo 1232434 1876565 := bbase (se 8 (by rfl) ⟨10995, by rfl⟩ : syracuseStep 1876565 = 21991) (by norm_num)
theorem B4686437 : Blo 1232434 4686437 := bbase (se 4 (by rfl) ⟨439353, by rfl⟩ : syracuseStep 4686437 = 878707) (by norm_num)
theorem B1581673 : Blo 1232434 1581673 := bbase (se 2 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 1581673 = 1186255) (by norm_num)
theorem B2081389 : Blo 1232434 2081389 := bbase (se 3 (by rfl) ⟨390260, by rfl⟩ : syracuseStep 2081389 = 780521) (by norm_num)
theorem B3121861 : Blo 1232434 3121861 := bbase (se 4 (by rfl) ⟨292674, by rfl⟩ : syracuseStep 3121861 = 585349) (by norm_num)
theorem B2081477 : Blo 1232434 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B1876717 : Blo 1232434 1876717 := bbase (se 3 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 1876717 = 703769) (by norm_num)
theorem B10535669 : Blo 1232434 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B3121973 : Blo 1232434 3121973 := bbase (se 5 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 3121973 = 292685) (by norm_num)
theorem B4162373 : Blo 1232434 4162373 := bbase (se 4 (by rfl) ⟨390222, by rfl⟩ : syracuseStep 4162373 = 780445) (by norm_num)
theorem B2081605 : Blo 1232434 2081605 := bbase (se 4 (by rfl) ⟨195150, by rfl⟩ : syracuseStep 2081605 = 390301) (by norm_num)
theorem B2081693 : Blo 1232434 2081693 := bbase (se 3 (by rfl) ⟨390317, by rfl⟩ : syracuseStep 2081693 = 780635) (by norm_num)
theorem B6243317 : Blo 1232434 6243317 := bbase (se 5 (by rfl) ⟨292655, by rfl⟩ : syracuseStep 6243317 = 585311) (by norm_num)
theorem B3122165 : Blo 1232434 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B10003445 : Blo 1232434 10003445 := bbase (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) (by norm_num)
theorem B2221085 : Blo 1232434 2221085 := bbase (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) (by norm_num)
theorem B2081821 : Blo 1232434 2081821 := bbase (se 3 (by rfl) ⟨390341, by rfl⟩ : syracuseStep 2081821 = 780683) (by norm_num)
theorem B1975349 : Blo 1232434 1975349 := bbase (se 5 (by rfl) ⟨92594, by rfl⟩ : syracuseStep 1975349 = 185189) (by norm_num)
theorem B2081909 : Blo 1232434 2081909 := bbase (se 5 (by rfl) ⟨97589, by rfl⟩ : syracuseStep 2081909 = 195179) (by norm_num)
theorem B2811053 : Blo 1232434 2811053 := bbase (se 3 (by rfl) ⟨527072, by rfl⟩ : syracuseStep 2811053 = 1054145) (by norm_num)
theorem B2221229 : Blo 1232434 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B3949813 : Blo 1232434 3949813 := bbase (se 5 (by rfl) ⟨185147, by rfl⟩ : syracuseStep 3949813 = 370295) (by norm_num)
theorem B4162805 : Blo 1232434 4162805 := bbase (se 5 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 4162805 = 390263) (by norm_num)
theorem B2082037 : Blo 1232434 2082037 := bbase (se 5 (by rfl) ⟨97595, by rfl⟩ : syracuseStep 2082037 = 195191) (by norm_num)
theorem B4744469 : Blo 1232434 4744469 := bbase (se 6 (by rfl) ⟨111198, by rfl⟩ : syracuseStep 4744469 = 222397) (by norm_num)
theorem B3802405 : Blo 1232434 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B3949877 : Blo 1232434 3949877 := bbase (se 5 (by rfl) ⟨185150, by rfl⟩ : syracuseStep 3949877 = 370301) (by norm_num)
theorem B3122509 : Blo 1232434 3122509 := bbase (se 3 (by rfl) ⟨585470, by rfl⟩ : syracuseStep 3122509 = 1170941) (by norm_num)
theorem B2082125 : Blo 1232434 2082125 := bbase (se 3 (by rfl) ⟨390398, by rfl⟩ : syracuseStep 2082125 = 780797) (by norm_num)
theorem B1975733 : Blo 1232434 1975733 := bbase (se 5 (by rfl) ⟨92612, by rfl⟩ : syracuseStep 1975733 = 185225) (by norm_num)
theorem B3122621 : Blo 1232434 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B2082253 : Blo 1232434 2082253 := bbase (se 3 (by rfl) ⟨390422, by rfl⟩ : syracuseStep 2082253 = 780845) (by norm_num)
theorem B11855317 : Blo 1232434 11855317 := bbase (se 7 (by rfl) ⟨138929, by rfl⟩ : syracuseStep 11855317 = 277859) (by norm_num)
theorem B3163637 : Blo 1232434 3163637 := bbase (se 5 (by rfl) ⟨148295, by rfl⟩ : syracuseStep 3163637 = 296591) (by norm_num)
theorem B2082341 : Blo 1232434 2082341 := bbase (se 4 (by rfl) ⟨195219, by rfl⟩ : syracuseStep 2082341 = 390439) (by norm_num)
theorem B1975861 : Blo 1232434 1975861 := bbase (se 5 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 1975861 = 185237) (by norm_num)
theorem B3122813 : Blo 1232434 3122813 := bbase (se 3 (by rfl) ⟨585527, by rfl⟩ : syracuseStep 3122813 = 1171055) (by norm_num)
theorem B4163237 : Blo 1232434 4163237 := bbase (se 4 (by rfl) ⟨390303, by rfl⟩ : syracuseStep 4163237 = 780607) (by norm_num)
theorem B2082469 : Blo 1232434 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B2082557 : Blo 1232434 2082557 := bbase (se 3 (by rfl) ⟨390479, by rfl⟩ : syracuseStep 2082557 = 780959) (by norm_num)
theorem B3376997 : Blo 1232434 3376997 := bbase (se 4 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 3376997 = 633187) (by norm_num)
theorem B2082685 : Blo 1232434 2082685 := bbase (se 3 (by rfl) ⟨390503, by rfl⟩ : syracuseStep 2082685 = 781007) (by norm_num)
theorem B30418901 : Blo 1232434 30418901 := bbase (se 7 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 30418901 = 712943) (by norm_num)
theorem B3123157 : Blo 1232434 3123157 := bbase (se 7 (by rfl) ⟨36599, by rfl⟩ : syracuseStep 3123157 = 73199) (by norm_num)
theorem B2082773 : Blo 1232434 2082773 := bbase (se 7 (by rfl) ⟨24407, by rfl⟩ : syracuseStep 2082773 = 48815) (by norm_num)
theorem B1386517 : Blo 1232434 1386517 := bbase (se 6 (by rfl) ⟨32496, by rfl⟩ : syracuseStep 1386517 = 64993) (by norm_num)
theorem B1386553 : Blo 1232434 1386553 := bbase (se 2 (by rfl) ⟨519957, by rfl⟩ : syracuseStep 1386553 = 1039915) (by norm_num)
theorem B5924933 : Blo 1232434 5924933 := bbase (se 4 (by rfl) ⟨555462, by rfl⟩ : syracuseStep 5924933 = 1110925) (by norm_num)
theorem B3123269 : Blo 1232434 3123269 := bbase (se 4 (by rfl) ⟨292806, by rfl⟩ : syracuseStep 3123269 = 585613) (by norm_num)
theorem B4163669 : Blo 1232434 4163669 := bbase (se 8 (by rfl) ⟨24396, by rfl⟩ : syracuseStep 4163669 = 48793) (by norm_num)
theorem B2082901 : Blo 1232434 2082901 := bbase (se 8 (by rfl) ⟨12204, by rfl⟩ : syracuseStep 2082901 = 24409) (by norm_num)
theorem B1386589 : Blo 1232434 1386589 := bbase (se 3 (by rfl) ⟨259985, by rfl⟩ : syracuseStep 1386589 = 519971) (by norm_num)
theorem B1386625 : Blo 1232434 1386625 := bbase (se 2 (by rfl) ⟨519984, by rfl⟩ : syracuseStep 1386625 = 1039969) (by norm_num)
theorem B1386661 : Blo 1232434 1386661 := bbase (se 4 (by rfl) ⟨129999, by rfl⟩ : syracuseStep 1386661 = 259999) (by norm_num)
theorem B2082989 : Blo 1232434 2082989 := bbase (se 3 (by rfl) ⟨390560, by rfl⟩ : syracuseStep 2082989 = 781121) (by norm_num)
theorem B1386697 : Blo 1232434 1386697 := bbase (se 2 (by rfl) ⟨520011, by rfl⟩ : syracuseStep 1386697 = 1040023) (by norm_num)
theorem B15804629 : Blo 1232434 15804629 := bbase (se 7 (by rfl) ⟨185210, by rfl⟩ : syracuseStep 15804629 = 370421) (by norm_num)
theorem B1386733 : Blo 1232434 1386733 := bbase (se 3 (by rfl) ⟨260012, by rfl⟩ : syracuseStep 1386733 = 520025) (by norm_num)
theorem B6244613 : Blo 1232434 6244613 := bbase (se 4 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 6244613 = 1170865) (by norm_num)
theorem B3123461 : Blo 1232434 3123461 := bbase (se 4 (by rfl) ⟨292824, by rfl⟩ : syracuseStep 3123461 = 585649) (by norm_num)
theorem B1386769 : Blo 1232434 1386769 := bbase (se 2 (by rfl) ⟨520038, by rfl⟩ : syracuseStep 1386769 = 1040077) (by norm_num)
theorem B1386805 : Blo 1232434 1386805 := bbase (se 5 (by rfl) ⟨65006, by rfl⟩ : syracuseStep 1386805 = 130013) (by norm_num)
theorem B1386841 : Blo 1232434 1386841 := bbase (se 2 (by rfl) ⟨520065, by rfl⟩ : syracuseStep 1386841 = 1040131) (by norm_num)
theorem B1386877 : Blo 1232434 1386877 := bbase (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) (by norm_num)
theorem B1386913 : Blo 1232434 1386913 := bbase (se 2 (by rfl) ⟨520092, by rfl⟩ : syracuseStep 1386913 = 1040185) (by norm_num)
theorem B1386949 : Blo 1232434 1386949 := bbase (se 4 (by rfl) ⟨130026, by rfl⟩ : syracuseStep 1386949 = 260053) (by norm_num)
theorem B1386985 : Blo 1232434 1386985 := bbase (se 2 (by rfl) ⟨520119, by rfl⟩ : syracuseStep 1386985 = 1040239) (by norm_num)
theorem B4164101 : Blo 1232434 4164101 := bbase (se 4 (by rfl) ⟨390384, by rfl⟩ : syracuseStep 4164101 = 780769) (by norm_num)
theorem B1387021 : Blo 1232434 1387021 := bbase (se 3 (by rfl) ⟨260066, by rfl⟩ : syracuseStep 1387021 = 520133) (by norm_num)
theorem B2001437 : Blo 1232434 2001437 := bbase (se 3 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 2001437 = 750539) (by norm_num)
theorem B1976861 : Blo 1232434 1976861 := bbase (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) (by norm_num)
theorem B1387057 : Blo 1232434 1387057 := bbase (se 2 (by rfl) ⟨520146, by rfl⟩ : syracuseStep 1387057 = 1040293) (by norm_num)
theorem B2632277 : Blo 1232434 2632277 := bbase (se 8 (by rfl) ⟨15423, by rfl⟩ : syracuseStep 2632277 = 30847) (by norm_num)
theorem B1387093 : Blo 1232434 1387093 := bbase (se 8 (by rfl) ⟨8127, by rfl⟩ : syracuseStep 1387093 = 16255) (by norm_num)
theorem B3123805 : Blo 1232434 3123805 := bbase (se 3 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 3123805 = 1171427) (by norm_num)
theorem B1387129 : Blo 1232434 1387129 := bbase (se 2 (by rfl) ⟨520173, by rfl⟩ : syracuseStep 1387129 = 1040347) (by norm_num)
theorem B2001541 : Blo 1232434 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B1387165 : Blo 1232434 1387165 := bbase (se 3 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 1387165 = 520187) (by norm_num)
theorem B1976989 : Blo 1232434 1976989 := bbase (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) (by norm_num)
theorem B1387201 : Blo 1232434 1387201 := bbase (se 2 (by rfl) ⟨520200, by rfl⟩ : syracuseStep 1387201 = 1040401) (by norm_num)
theorem B3123917 : Blo 1232434 3123917 := bbase (se 3 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 3123917 = 1171469) (by norm_num)
theorem B1387237 : Blo 1232434 1387237 := bbase (se 4 (by rfl) ⟨130053, by rfl⟩ : syracuseStep 1387237 = 260107) (by norm_num)
theorem B1387273 : Blo 1232434 1387273 := bbase (se 2 (by rfl) ⟨520227, by rfl⟩ : syracuseStep 1387273 = 1040455) (by norm_num)
theorem B1387309 : Blo 1232434 1387309 := bbase (se 3 (by rfl) ⟨260120, by rfl⟩ : syracuseStep 1387309 = 520241) (by norm_num)
theorem B1387345 : Blo 1232434 1387345 := bbase (se 2 (by rfl) ⟨520254, by rfl⟩ : syracuseStep 1387345 = 1040509) (by norm_num)
theorem B1387381 : Blo 1232434 1387381 := bbase (se 5 (by rfl) ⟨65033, by rfl⟩ : syracuseStep 1387381 = 130067) (by norm_num)
theorem B3124109 : Blo 1232434 3124109 := bbase (se 3 (by rfl) ⟨585770, by rfl⟩ : syracuseStep 3124109 = 1171541) (by norm_num)
theorem B1387417 : Blo 1232434 1387417 := bbase (se 2 (by rfl) ⟨520281, by rfl⟩ : syracuseStep 1387417 = 1040563) (by norm_num)
theorem B5622709 : Blo 1232434 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B4164533 : Blo 1232434 4164533 := bbase (se 5 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 4164533 = 390425) (by norm_num)
theorem B1387453 : Blo 1232434 1387453 := bbase (se 3 (by rfl) ⟨260147, by rfl⟩ : syracuseStep 1387453 = 520295) (by norm_num)
theorem B1756093 : Blo 1232434 1756093 := bbase (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) (by norm_num)
theorem B1387489 : Blo 1232434 1387489 := bbase (se 2 (by rfl) ⟨520308, by rfl⟩ : syracuseStep 1387489 = 1040617) (by norm_num)
theorem B1387525 : Blo 1232434 1387525 := bbase (se 4 (by rfl) ⟨130080, by rfl⟩ : syracuseStep 1387525 = 260161) (by norm_num)
theorem B1387561 : Blo 1232434 1387561 := bbase (se 2 (by rfl) ⟨520335, by rfl⟩ : syracuseStep 1387561 = 1040671) (by norm_num)
theorem B4680773 : Blo 1232434 4680773 := bbase (se 4 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 4680773 = 877645) (by norm_num)
theorem B1387597 : Blo 1232434 1387597 := bbase (se 3 (by rfl) ⟨260174, by rfl⟩ : syracuseStep 1387597 = 520349) (by norm_num)
theorem B3165277 : Blo 1232434 3165277 := bbase (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) (by norm_num)
theorem B1387633 : Blo 1232434 1387633 := bbase (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) (by norm_num)
theorem B9366677 : Blo 1232434 9366677 := bbase (se 6 (by rfl) ⟨219531, by rfl⟩ : syracuseStep 9366677 = 439063) (by norm_num)
theorem B1387669 : Blo 1232434 1387669 := bbase (se 6 (by rfl) ⟨32523, by rfl⟩ : syracuseStep 1387669 = 65047) (by norm_num)
theorem B1387705 : Blo 1232434 1387705 := bbase (se 2 (by rfl) ⟨520389, by rfl⟩ : syracuseStep 1387705 = 1040779) (by norm_num)
theorem B1387741 : Blo 1232434 1387741 := bbase (se 3 (by rfl) ⟨260201, by rfl⟩ : syracuseStep 1387741 = 520403) (by norm_num)
theorem B3124453 : Blo 1232434 3124453 := bbase (se 4 (by rfl) ⟨292917, by rfl⟩ : syracuseStep 3124453 = 585835) (by norm_num)
theorem B1387777 : Blo 1232434 1387777 := bbase (se 2 (by rfl) ⟨520416, by rfl⟩ : syracuseStep 1387777 = 1040833) (by norm_num)
theorem B1559837 : Blo 1232434 1559837 := bbase (se 3 (by rfl) ⟨292469, by rfl⟩ : syracuseStep 1559837 = 584939) (by norm_num)
theorem B1666333 : Blo 1232434 1666333 := bbase (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) (by norm_num)
theorem B1387813 : Blo 1232434 1387813 := bbase (se 4 (by rfl) ⟨130107, by rfl⟩ : syracuseStep 1387813 = 260215) (by norm_num)
theorem B1387849 : Blo 1232434 1387849 := bbase (se 2 (by rfl) ⟨520443, by rfl⟩ : syracuseStep 1387849 = 1040887) (by norm_num)
theorem B1559893 : Blo 1232434 1559893 := bbase (se 11 (by rfl) ⟨1142, by rfl⟩ : syracuseStep 1559893 = 2285) (by norm_num)
theorem B3124565 : Blo 1232434 3124565 := bbase (se 11 (by rfl) ⟨2288, by rfl⟩ : syracuseStep 3124565 = 4577) (by norm_num)
theorem B4681061 : Blo 1232434 4681061 := bbase (se 4 (by rfl) ⟨438849, by rfl⟩ : syracuseStep 4681061 = 877699) (by norm_num)
theorem B4164965 : Blo 1232434 4164965 := bbase (se 4 (by rfl) ⟨390465, by rfl⟩ : syracuseStep 4164965 = 780931) (by norm_num)
theorem B1387885 : Blo 1232434 1387885 := bbase (se 3 (by rfl) ⟨260228, by rfl⟩ : syracuseStep 1387885 = 520457) (by norm_num)
theorem B2502029 : Blo 1232434 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B1387921 : Blo 1232434 1387921 := bbase (se 2 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 1387921 = 1040941) (by norm_num)
theorem B3509669 : Blo 1232434 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B1559989 : Blo 1232434 1559989 := bbase (se 5 (by rfl) ⟨73124, by rfl⟩ : syracuseStep 1559989 = 146249) (by norm_num)
theorem B2633141 : Blo 1232434 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B1387957 : Blo 1232434 1387957 := bbase (se 5 (by rfl) ⟨65060, by rfl⟩ : syracuseStep 1387957 = 130121) (by norm_num)
theorem B1387993 : Blo 1232434 1387993 := bbase (se 2 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 1387993 = 1040995) (by norm_num)
theorem B1388029 : Blo 1232434 1388029 := bbase (se 3 (by rfl) ⟨260255, by rfl⟩ : syracuseStep 1388029 = 520511) (by norm_num)
theorem B1756685 : Blo 1232434 1756685 := bbase (se 3 (by rfl) ⟨329378, by rfl⟩ : syracuseStep 1756685 = 658757) (by norm_num)
theorem B6245909 : Blo 1232434 6245909 := bbase (se 6 (by rfl) ⟨146388, by rfl⟩ : syracuseStep 6245909 = 292777) (by norm_num)
theorem B1388065 : Blo 1232434 1388065 := bbase (se 2 (by rfl) ⟨520524, by rfl⟩ : syracuseStep 1388065 = 1041049) (by norm_num)
theorem B9358901 : Blo 1232434 9358901 := bbase (se 5 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 9358901 = 877397) (by norm_num)
theorem B2633285 : Blo 1232434 2633285 := bbase (se 4 (by rfl) ⟨246870, by rfl⟩ : syracuseStep 2633285 = 493741) (by norm_num)
theorem B1388101 : Blo 1232434 1388101 := bbase (se 4 (by rfl) ⟨130134, by rfl⟩ : syracuseStep 1388101 = 260269) (by norm_num)
theorem B1756765 : Blo 1232434 1756765 := bbase (se 3 (by rfl) ⟨329393, by rfl⟩ : syracuseStep 1756765 = 658787) (by norm_num)
theorem B1560161 : Blo 1232434 1560161 := bbase (se 2 (by rfl) ⟨585060, by rfl⟩ : syracuseStep 1560161 = 1170121) (by norm_num)
theorem B1388137 : Blo 1232434 1388137 := bbase (se 2 (by rfl) ⟨520551, by rfl⟩ : syracuseStep 1388137 = 1041103) (by norm_num)
theorem B1388173 : Blo 1232434 1388173 := bbase (se 3 (by rfl) ⟨260282, by rfl⟩ : syracuseStep 1388173 = 520565) (by norm_num)
theorem B1560217 : Blo 1232434 1560217 := bbase (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) (by norm_num)
theorem B1502885 : Blo 1232434 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B1388209 : Blo 1232434 1388209 := bbase (se 2 (by rfl) ⟨520578, by rfl⟩ : syracuseStep 1388209 = 1041157) (by norm_num)
theorem B1756885 : Blo 1232434 1756885 := bbase (se 7 (by rfl) ⟨20588, by rfl⟩ : syracuseStep 1756885 = 41177) (by norm_num)
theorem B1388245 : Blo 1232434 1388245 := bbase (se 7 (by rfl) ⟨16268, by rfl⟩ : syracuseStep 1388245 = 32537) (by norm_num)
theorem B1560313 : Blo 1232434 1560313 := bbase (se 2 (by rfl) ⟨585117, by rfl⟩ : syracuseStep 1560313 = 1170235) (by norm_num)
theorem B1388281 : Blo 1232434 1388281 := bbase (se 2 (by rfl) ⟨520605, by rfl⟩ : syracuseStep 1388281 = 1041211) (by norm_num)
theorem B3165973 : Blo 1232434 3165973 := bbase (se 6 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 3165973 = 148405) (by norm_num)
theorem B4165397 : Blo 1232434 4165397 := bbase (se 6 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 4165397 = 195253) (by norm_num)
theorem B1388317 : Blo 1232434 1388317 := bbase (se 3 (by rfl) ⟨260309, by rfl⟩ : syracuseStep 1388317 = 520619) (by norm_num)
theorem B7499573 : Blo 1232434 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B1756981 : Blo 1232434 1756981 := bbase (se 5 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 1756981 = 164717) (by norm_num)
theorem B1388353 : Blo 1232434 1388353 := bbase (se 2 (by rfl) ⟨520632, by rfl⟩ : syracuseStep 1388353 = 1041265) (by norm_num)
theorem B5001061 : Blo 1232434 5001061 := bbase (se 4 (by rfl) ⟨468849, by rfl⟩ : syracuseStep 5001061 = 937699) (by norm_num)
theorem B1388389 : Blo 1232434 1388389 := bbase (se 4 (by rfl) ⟨130161, by rfl⟩ : syracuseStep 1388389 = 260323) (by norm_num)
theorem B1388425 : Blo 1232434 1388425 := bbase (se 2 (by rfl) ⟨520659, by rfl⟩ : syracuseStep 1388425 = 1041319) (by norm_num)
theorem B1560485 : Blo 1232434 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B1666981 : Blo 1232434 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B1388461 : Blo 1232434 1388461 := bbase (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) (by norm_num)
theorem B1388497 : Blo 1232434 1388497 := bbase (se 2 (by rfl) ⟨520686, by rfl⟩ : syracuseStep 1388497 = 1041373) (by norm_num)
theorem B1560541 : Blo 1232434 1560541 := bbase (se 3 (by rfl) ⟨292601, by rfl⟩ : syracuseStep 1560541 = 585203) (by norm_num)
theorem B1388533 : Blo 1232434 1388533 := bbase (se 5 (by rfl) ⟨65087, by rfl⟩ : syracuseStep 1388533 = 130175) (by norm_num)
theorem B2772989 : Blo 1232434 2772989 := bbase (se 3 (by rfl) ⟨519935, by rfl⟩ : syracuseStep 2772989 = 1039871) (by norm_num)
theorem B2109445 : Blo 1232434 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B13340693 : Blo 1232434 13340693 := bbase (se 6 (by rfl) ⟨312672, by rfl⟩ : syracuseStep 13340693 = 625345) (by norm_num)
theorem B1388569 : Blo 1232434 1388569 := bbase (se 2 (by rfl) ⟨520713, by rfl⟩ : syracuseStep 1388569 = 1041427) (by norm_num)
theorem B1560637 : Blo 1232434 1560637 := bbase (se 3 (by rfl) ⟨292619, by rfl⟩ : syracuseStep 1560637 = 585239) (by norm_num)
theorem B1388605 : Blo 1232434 1388605 := bbase (se 3 (by rfl) ⟨260363, by rfl⟩ : syracuseStep 1388605 = 520727) (by norm_num)
theorem B2773061 : Blo 1232434 2773061 := bbase (se 4 (by rfl) ⟨259974, by rfl⟩ : syracuseStep 2773061 = 519949) (by norm_num)
theorem B3510341 : Blo 1232434 3510341 := bbase (se 4 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 3510341 = 658189) (by norm_num)
theorem B7499861 : Blo 1232434 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B6672469 : Blo 1232434 6672469 := bbase (se 8 (by rfl) ⟨39096, by rfl⟩ : syracuseStep 6672469 = 78193) (by norm_num)
theorem B1388641 : Blo 1232434 1388641 := bbase (se 2 (by rfl) ⟨520740, by rfl⟩ : syracuseStep 1388641 = 1041481) (by norm_num)
theorem B2003053 : Blo 1232434 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B1249393 : Blo 1232434 1249393 := bbase (se 2 (by rfl) ⟨468522, by rfl⟩ : syracuseStep 1249393 = 937045) (by norm_num)
theorem B1388677 : Blo 1232434 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B2773133 : Blo 1232434 2773133 := bbase (se 3 (by rfl) ⟨519962, by rfl⟩ : syracuseStep 2773133 = 1039925) (by norm_num)
theorem B1388713 : Blo 1232434 1388713 := bbase (se 2 (by rfl) ⟨520767, by rfl⟩ : syracuseStep 1388713 = 1041535) (by norm_num)
theorem B5271749 : Blo 1232434 5271749 := bbase (se 4 (by rfl) ⟨494226, by rfl⟩ : syracuseStep 5271749 = 988453) (by norm_num)
theorem B4165829 : Blo 1232434 4165829 := bbase (se 4 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 4165829 = 781093) (by norm_num)
theorem B2773205 : Blo 1232434 2773205 := bbase (se 7 (by rfl) ⟨32498, by rfl⟩ : syracuseStep 2773205 = 64997) (by norm_num)
theorem B1560809 : Blo 1232434 1560809 := bbase (se 2 (by rfl) ⟨585303, by rfl⟩ : syracuseStep 1560809 = 1170607) (by norm_num)
theorem B3952901 : Blo 1232434 3952901 := bbase (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) (by norm_num)
theorem B3166469 : Blo 1232434 3166469 := bbase (se 4 (by rfl) ⟨296856, by rfl⟩ : syracuseStep 3166469 = 593713) (by norm_num)
theorem B2773277 : Blo 1232434 2773277 := bbase (se 3 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 2773277 = 1039979) (by norm_num)
theorem B1560865 : Blo 1232434 1560865 := bbase (se 2 (by rfl) ⟨585324, by rfl⟩ : syracuseStep 1560865 = 1170649) (by norm_num)
theorem B1757477 : Blo 1232434 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B2634029 : Blo 1232434 2634029 := bbase (se 3 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 2634029 = 987761) (by norm_num)
theorem B2167133 : Blo 1232434 2167133 := bbase (se 3 (by rfl) ⟨406337, by rfl⟩ : syracuseStep 2167133 = 812675) (by norm_num)
theorem B2773349 : Blo 1232434 2773349 := bbase (se 4 (by rfl) ⟨260001, by rfl⟩ : syracuseStep 2773349 = 520003) (by norm_num)
theorem B1560961 : Blo 1232434 1560961 := bbase (se 2 (by rfl) ⟨585360, by rfl⟩ : syracuseStep 1560961 = 1170721) (by norm_num)
theorem B2773421 : Blo 1232434 2773421 := bbase (se 3 (by rfl) ⟨520016, by rfl⟩ : syracuseStep 2773421 = 1040033) (by norm_num)
theorem B5272037 : Blo 1232434 5272037 := bbase (se 4 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 5272037 = 988507) (by norm_num)
theorem B2773493 : Blo 1232434 2773493 := bbase (se 5 (by rfl) ⟨130007, by rfl⟩ : syracuseStep 2773493 = 260015) (by norm_num)
theorem B3510773 : Blo 1232434 3510773 := bbase (se 5 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 3510773 = 329135) (by norm_num)
theorem B4682245 : Blo 1232434 4682245 := bbase (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) (by norm_num)
theorem B3748373 : Blo 1232434 3748373 := bbase (se 6 (by rfl) ⟨87852, by rfl⟩ : syracuseStep 3748373 = 175705) (by norm_num)
theorem B1561133 : Blo 1232434 1561133 := bbase (se 3 (by rfl) ⟨292712, by rfl⟩ : syracuseStep 1561133 = 585425) (by norm_num)
theorem B2773565 : Blo 1232434 2773565 := bbase (se 3 (by rfl) ⟨520043, by rfl⟩ : syracuseStep 2773565 = 1040087) (by norm_num)
theorem B7025237 : Blo 1232434 7025237 := bbase (se 8 (by rfl) ⟨41163, by rfl⟩ : syracuseStep 7025237 = 82327) (by norm_num)
theorem B1561189 : Blo 1232434 1561189 := bbase (se 4 (by rfl) ⟨146361, by rfl⟩ : syracuseStep 1561189 = 292723) (by norm_num)
theorem B2773637 : Blo 1232434 2773637 := bbase (se 4 (by rfl) ⟨260028, by rfl⟩ : syracuseStep 2773637 = 520057) (by norm_num)
theorem B1249973 : Blo 1232434 1249973 := bbase (se 5 (by rfl) ⟨58592, by rfl⟩ : syracuseStep 1249973 = 117185) (by norm_num)
theorem B1561285 : Blo 1232434 1561285 := bbase (se 4 (by rfl) ⟨146370, by rfl⟩ : syracuseStep 1561285 = 292741) (by norm_num)
theorem B2773709 : Blo 1232434 2773709 := bbase (se 3 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 2773709 = 1040141) (by norm_num)
theorem B2773781 : Blo 1232434 2773781 := bbase (se 6 (by rfl) ⟨65010, by rfl⟩ : syracuseStep 2773781 = 130021) (by norm_num)
theorem B6247205 : Blo 1232434 6247205 := bbase (se 4 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 6247205 = 1171351) (by norm_num)
theorem B4682549 : Blo 1232434 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B6673205 : Blo 1232434 6673205 := bbase (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) (by norm_num)
theorem B2773853 : Blo 1232434 2773853 := bbase (se 3 (by rfl) ⟨520097, by rfl⟩ : syracuseStep 2773853 = 1040195) (by norm_num)
theorem B1561457 : Blo 1232434 1561457 := bbase (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) (by norm_num)
theorem B5927813 : Blo 1232434 5927813 := bbase (se 4 (by rfl) ⟨555732, by rfl⟩ : syracuseStep 5927813 = 1111465) (by norm_num)
theorem B2339741 : Blo 1232434 2339741 := bbase (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) (by norm_num)
theorem B2773925 : Blo 1232434 2773925 := bbase (se 4 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 2773925 = 520111) (by norm_num)
theorem B1561513 : Blo 1232434 1561513 := bbase (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) (by norm_num)
theorem B2773997 : Blo 1232434 2773997 := bbase (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) (by norm_num)
theorem B1561609 : Blo 1232434 1561609 := bbase (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) (by norm_num)
theorem B2634781 : Blo 1232434 2634781 := bbase (se 3 (by rfl) ⟨494021, by rfl⟩ : syracuseStep 2634781 = 988043) (by norm_num)
theorem B2774069 : Blo 1232434 2774069 := bbase (se 5 (by rfl) ⟨130034, by rfl⟩ : syracuseStep 2774069 = 260069) (by norm_num)
theorem B2774141 : Blo 1232434 2774141 := bbase (se 3 (by rfl) ⟨520151, by rfl⟩ : syracuseStep 2774141 = 1040303) (by norm_num)
theorem B2634925 : Blo 1232434 2634925 := bbase (se 3 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 2634925 = 988097) (by norm_num)
theorem B1561781 : Blo 1232434 1561781 := bbase (se 5 (by rfl) ⟨73208, by rfl⟩ : syracuseStep 1561781 = 146417) (by norm_num)
theorem B2340029 : Blo 1232434 2340029 := bbase (se 3 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 2340029 = 877511) (by norm_num)
theorem B6239429 : Blo 1232434 6239429 := bbase (se 4 (by rfl) ⟨584946, by rfl⟩ : syracuseStep 6239429 = 1169893) (by norm_num)
theorem B2774213 : Blo 1232434 2774213 := bbase (se 4 (by rfl) ⟨260082, by rfl⟩ : syracuseStep 2774213 = 520165) (by norm_num)
theorem B5272789 : Blo 1232434 5272789 := bbase (se 7 (by rfl) ⟨61790, by rfl⟩ : syracuseStep 5272789 = 123581) (by norm_num)
theorem B3511525 : Blo 1232434 3511525 := bbase (se 4 (by rfl) ⟨329205, by rfl⟩ : syracuseStep 3511525 = 658411) (by norm_num)
theorem B6329573 : Blo 1232434 6329573 := bbase (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) (by norm_num)
theorem B1561837 : Blo 1232434 1561837 := bbase (se 3 (by rfl) ⟨292844, by rfl⟩ : syracuseStep 1561837 = 585689) (by norm_num)
theorem B5002501 : Blo 1232434 5002501 := bbase (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) (by norm_num)
theorem B2774285 : Blo 1232434 2774285 := bbase (se 3 (by rfl) ⟨520178, by rfl⟩ : syracuseStep 2774285 = 1040357) (by norm_num)
theorem B2405693 : Blo 1232434 2405693 := bbase (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) (by norm_num)
theorem B1848653 : Blo 1232434 1848653 := bbase (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) (by norm_num)
theorem B1561933 : Blo 1232434 1561933 := bbase (se 3 (by rfl) ⟨292862, by rfl⟩ : syracuseStep 1561933 = 585725) (by norm_num)
theorem B2340181 : Blo 1232434 2340181 := bbase (se 13 (by rfl) ⟨428, by rfl⟩ : syracuseStep 2340181 = 857) (by norm_num)
theorem B2774357 : Blo 1232434 2774357 := bbase (se 16 (by rfl) ⟨63, by rfl⟩ : syracuseStep 2774357 = 127) (by norm_num)
theorem B1848677 : Blo 1232434 1848677 := bbase (se 4 (by rfl) ⟨173313, by rfl⟩ : syracuseStep 1848677 = 346627) (by norm_num)
theorem B11859317 : Blo 1232434 11859317 := bbase (se 5 (by rfl) ⟨555905, by rfl⟩ : syracuseStep 11859317 = 1111811) (by norm_num)
theorem B1848701 : Blo 1232434 1848701 := bbase (se 3 (by rfl) ⟨346631, by rfl⟩ : syracuseStep 1848701 = 693263) (by norm_num)
theorem B1848725 : Blo 1232434 1848725 := bbase (se 6 (by rfl) ⟨43329, by rfl⟩ : syracuseStep 1848725 = 86659) (by norm_num)
theorem B2774429 : Blo 1232434 2774429 := bbase (se 3 (by rfl) ⟨520205, by rfl⟩ : syracuseStep 2774429 = 1040411) (by norm_num)
theorem B1848749 : Blo 1232434 1848749 := bbase (se 3 (by rfl) ⟨346640, by rfl⟩ : syracuseStep 1848749 = 693281) (by norm_num)
theorem B1848773 : Blo 1232434 1848773 := bbase (se 4 (by rfl) ⟨173322, by rfl⟩ : syracuseStep 1848773 = 346645) (by norm_num)
theorem B1316297 : Blo 1232434 1316297 := bbase (se 2 (by rfl) ⟨493611, by rfl⟩ : syracuseStep 1316297 = 987223) (by norm_num)
theorem B1848797 : Blo 1232434 1848797 := bbase (se 3 (by rfl) ⟨346649, by rfl⟩ : syracuseStep 1848797 = 693299) (by norm_num)
theorem B2774501 : Blo 1232434 2774501 := bbase (se 4 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 2774501 = 520219) (by norm_num)
theorem B1848821 : Blo 1232434 1848821 := bbase (se 5 (by rfl) ⟨86663, by rfl⟩ : syracuseStep 1848821 = 173327) (by norm_num)
theorem B3208693 : Blo 1232434 3208693 := bbase (se 5 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 3208693 = 300815) (by norm_num)
theorem B1562105 : Blo 1232434 1562105 := bbase (se 2 (by rfl) ⟨585789, by rfl⟩ : syracuseStep 1562105 = 1171579) (by norm_num)
theorem B1848845 : Blo 1232434 1848845 := bbase (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) (by norm_num)
theorem B1316369 : Blo 1232434 1316369 := bbase (se 2 (by rfl) ⟨493638, by rfl⟩ : syracuseStep 1316369 = 987277) (by norm_num)
theorem B1406489 : Blo 1232434 1406489 := bbase (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) (by norm_num)
theorem B1250849 : Blo 1232434 1250849 := bbase (se 2 (by rfl) ⟨469068, by rfl⟩ : syracuseStep 1250849 = 938137) (by norm_num)
theorem B1848869 : Blo 1232434 1848869 := bbase (se 4 (by rfl) ⟨173331, by rfl⟩ : syracuseStep 1848869 = 346663) (by norm_num)
theorem B2635301 : Blo 1232434 2635301 := bbase (se 4 (by rfl) ⟨247059, by rfl⟩ : syracuseStep 2635301 = 494119) (by norm_num)
theorem B2774573 : Blo 1232434 2774573 := bbase (se 3 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 2774573 = 1040465) (by norm_num)
theorem B1562161 : Blo 1232434 1562161 := bbase (se 2 (by rfl) ⟨585810, by rfl⟩ : syracuseStep 1562161 = 1171621) (by norm_num)
theorem B1848893 : Blo 1232434 1848893 := bbase (se 3 (by rfl) ⟨346667, by rfl⟩ : syracuseStep 1848893 = 693335) (by norm_num)
theorem B1848917 : Blo 1232434 1848917 := bbase (se 8 (by rfl) ⟨10833, by rfl⟩ : syracuseStep 1848917 = 21667) (by norm_num)
theorem B1848941 : Blo 1232434 1848941 := bbase (se 3 (by rfl) ⟨346676, by rfl⟩ : syracuseStep 1848941 = 693353) (by norm_num)
theorem B2774645 : Blo 1232434 2774645 := bbase (se 5 (by rfl) ⟨130061, by rfl⟩ : syracuseStep 2774645 = 260123) (by norm_num)
theorem B1848965 : Blo 1232434 1848965 := bbase (se 4 (by rfl) ⟨173340, by rfl⟩ : syracuseStep 1848965 = 346681) (by norm_num)
theorem B2340485 : Blo 1232434 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B1562257 : Blo 1232434 1562257 := bbase (se 2 (by rfl) ⟨585846, by rfl⟩ : syracuseStep 1562257 = 1171693) (by norm_num)
theorem B1848989 : Blo 1232434 1848989 := bbase (se 3 (by rfl) ⟨346685, by rfl⟩ : syracuseStep 1848989 = 693371) (by norm_num)
theorem B1849013 : Blo 1232434 1849013 := bbase (se 5 (by rfl) ⟨86672, by rfl⟩ : syracuseStep 1849013 = 173345) (by norm_num)
theorem B2774717 : Blo 1232434 2774717 := bbase (se 3 (by rfl) ⟨520259, by rfl⟩ : syracuseStep 2774717 = 1040519) (by norm_num)
theorem B1849037 : Blo 1232434 1849037 := bbase (se 3 (by rfl) ⟨346694, by rfl⟩ : syracuseStep 1849037 = 693389) (by norm_num)
theorem B1316557 : Blo 1232434 1316557 := bbase (se 3 (by rfl) ⟨246854, by rfl⟩ : syracuseStep 1316557 = 493709) (by norm_num)
theorem B1849061 : Blo 1232434 1849061 := bbase (se 4 (by rfl) ⟨173349, by rfl⟩ : syracuseStep 1849061 = 346699) (by norm_num)
theorem B1849085 : Blo 1232434 1849085 := bbase (se 3 (by rfl) ⟨346703, by rfl⟩ : syracuseStep 1849085 = 693407) (by norm_num)
theorem B2774789 : Blo 1232434 2774789 := bbase (se 4 (by rfl) ⟨260136, by rfl⟩ : syracuseStep 2774789 = 520273) (by norm_num)
theorem B1849109 : Blo 1232434 1849109 := bbase (se 6 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 1849109 = 86677) (by norm_num)
theorem B1849133 : Blo 1232434 1849133 := bbase (se 3 (by rfl) ⟨346712, by rfl⟩ : syracuseStep 1849133 = 693425) (by norm_num)
theorem B1849157 : Blo 1232434 1849157 := bbase (se 4 (by rfl) ⟨173358, by rfl⟩ : syracuseStep 1849157 = 346717) (by norm_num)
theorem B2774861 : Blo 1232434 2774861 := bbase (se 3 (by rfl) ⟨520286, by rfl⟩ : syracuseStep 2774861 = 1040573) (by norm_num)
theorem B1849181 : Blo 1232434 1849181 := bbase (se 3 (by rfl) ⟨346721, by rfl⟩ : syracuseStep 1849181 = 693443) (by norm_num)
theorem B1849205 : Blo 1232434 1849205 := bbase (se 5 (by rfl) ⟨86681, by rfl⟩ : syracuseStep 1849205 = 173363) (by norm_num)
theorem B1406845 : Blo 1232434 1406845 := bbase (se 3 (by rfl) ⟨263783, by rfl⟩ : syracuseStep 1406845 = 527567) (by norm_num)
theorem B1316741 : Blo 1232434 1316741 := bbase (se 4 (by rfl) ⟨123444, by rfl⟩ : syracuseStep 1316741 = 246889) (by norm_num)
theorem B1251209 : Blo 1232434 1251209 := bbase (se 2 (by rfl) ⟨469203, by rfl⟩ : syracuseStep 1251209 = 938407) (by norm_num)
theorem B1849229 : Blo 1232434 1849229 := bbase (se 3 (by rfl) ⟨346730, by rfl⟩ : syracuseStep 1849229 = 693461) (by norm_num)
theorem B2774933 : Blo 1232434 2774933 := bbase (se 6 (by rfl) ⟨65037, by rfl⟩ : syracuseStep 2774933 = 130075) (by norm_num)
theorem B2635669 : Blo 1232434 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B1849253 : Blo 1232434 1849253 := bbase (se 4 (by rfl) ⟨173367, by rfl⟩ : syracuseStep 1849253 = 346735) (by norm_num)
theorem B1849277 : Blo 1232434 1849277 := bbase (se 3 (by rfl) ⟨346739, by rfl⟩ : syracuseStep 1849277 = 693479) (by norm_num)
theorem B4503509 : Blo 1232434 4503509 := bbase (se 7 (by rfl) ⟨52775, by rfl⟩ : syracuseStep 4503509 = 105551) (by norm_num)
theorem B1849301 : Blo 1232434 1849301 := bbase (se 7 (by rfl) ⟨21671, by rfl⟩ : syracuseStep 1849301 = 43343) (by norm_num)
theorem B3381205 : Blo 1232434 3381205 := bbase (se 7 (by rfl) ⟨39623, by rfl⟩ : syracuseStep 3381205 = 79247) (by norm_num)
theorem B2775005 : Blo 1232434 2775005 := bbase (se 3 (by rfl) ⟨520313, by rfl⟩ : syracuseStep 2775005 = 1040627) (by norm_num)
theorem B1849325 : Blo 1232434 1849325 := bbase (se 3 (by rfl) ⟨346748, by rfl⟩ : syracuseStep 1849325 = 693497) (by norm_num)
theorem B1849349 : Blo 1232434 1849349 := bbase (se 4 (by rfl) ⟨173376, by rfl⟩ : syracuseStep 1849349 = 346753) (by norm_num)
theorem B1849373 : Blo 1232434 1849373 := bbase (se 3 (by rfl) ⟨346757, by rfl⟩ : syracuseStep 1849373 = 693515) (by norm_num)
theorem B2775077 : Blo 1232434 2775077 := bbase (se 4 (by rfl) ⟨260163, by rfl⟩ : syracuseStep 2775077 = 520327) (by norm_num)
theorem B1849397 : Blo 1232434 1849397 := bbase (se 5 (by rfl) ⟨86690, by rfl⟩ : syracuseStep 1849397 = 173381) (by norm_num)
theorem B5339189 : Blo 1232434 5339189 := bbase (se 5 (by rfl) ⟨250274, by rfl⟩ : syracuseStep 5339189 = 500549) (by norm_num)
theorem B6248501 : Blo 1232434 6248501 := bbase (se 5 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 6248501 = 585797) (by norm_num)
theorem B1849421 : Blo 1232434 1849421 := bbase (se 3 (by rfl) ⟨346766, by rfl⟩ : syracuseStep 1849421 = 693533) (by norm_num)
theorem B1849445 : Blo 1232434 1849445 := bbase (se 4 (by rfl) ⟨173385, by rfl⟩ : syracuseStep 1849445 = 346771) (by norm_num)
theorem B2775149 : Blo 1232434 2775149 := bbase (se 3 (by rfl) ⟨520340, by rfl⟩ : syracuseStep 2775149 = 1040681) (by norm_num)
theorem B1849469 : Blo 1232434 1849469 := bbase (se 3 (by rfl) ⟨346775, by rfl⟩ : syracuseStep 1849469 = 693551) (by norm_num)
theorem B1267849 : Blo 1232434 1267849 := bbase (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) (by norm_num)
theorem B1849493 : Blo 1232434 1849493 := bbase (se 6 (by rfl) ⟨43347, by rfl⟩ : syracuseStep 1849493 = 86695) (by norm_num)
theorem B1849517 : Blo 1232434 1849517 := bbase (se 3 (by rfl) ⟨346784, by rfl⟩ : syracuseStep 1849517 = 693569) (by norm_num)
theorem B2775221 : Blo 1232434 2775221 := bbase (se 5 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 2775221 = 260177) (by norm_num)
theorem B1849541 : Blo 1232434 1849541 := bbase (se 4 (by rfl) ⟨173394, by rfl⟩ : syracuseStep 1849541 = 346789) (by norm_num)
theorem B5003477 : Blo 1232434 5003477 := bbase (se 7 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 5003477 = 117269) (by norm_num)
theorem B1849565 : Blo 1232434 1849565 := bbase (se 3 (by rfl) ⟨346793, by rfl⟩ : syracuseStep 1849565 = 693587) (by norm_num)
theorem B1849589 : Blo 1232434 1849589 := bbase (se 5 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 1849589 = 173399) (by norm_num)
theorem B2775293 : Blo 1232434 2775293 := bbase (se 3 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 2775293 = 1040735) (by norm_num)
theorem B1849613 : Blo 1232434 1849613 := bbase (se 3 (by rfl) ⟨346802, by rfl⟩ : syracuseStep 1849613 = 693605) (by norm_num)
theorem B4159781 : Blo 1232434 4159781 := bbase (se 4 (by rfl) ⟨389979, by rfl⟩ : syracuseStep 4159781 = 779959) (by norm_num)
theorem B1849637 : Blo 1232434 1849637 := bbase (se 4 (by rfl) ⟨173403, by rfl⟩ : syracuseStep 1849637 = 346807) (by norm_num)
theorem B1849661 : Blo 1232434 1849661 := bbase (se 3 (by rfl) ⟨346811, by rfl⟩ : syracuseStep 1849661 = 693623) (by norm_num)
theorem B2775365 : Blo 1232434 2775365 := bbase (se 4 (by rfl) ⟨260190, by rfl⟩ : syracuseStep 2775365 = 520381) (by norm_num)
theorem B1481041 : Blo 1232434 1481041 := bbase (se 2 (by rfl) ⟨555390, by rfl⟩ : syracuseStep 1481041 = 1110781) (by norm_num)
theorem B5265749 : Blo 1232434 5265749 := bbase (se 10 (by rfl) ⟨7713, by rfl⟩ : syracuseStep 5265749 = 15427) (by norm_num)
theorem B1849685 : Blo 1232434 1849685 := bbase (se 10 (by rfl) ⟨2709, by rfl⟩ : syracuseStep 1849685 = 5419) (by norm_num)
theorem B19003733 : Blo 1232434 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B1481069 : Blo 1232434 1481069 := bbase (se 3 (by rfl) ⟨277700, by rfl⟩ : syracuseStep 1481069 = 555401) (by norm_num)
theorem B1849709 : Blo 1232434 1849709 := bbase (se 3 (by rfl) ⟨346820, by rfl⟩ : syracuseStep 1849709 = 693641) (by norm_num)
theorem B2029933 : Blo 1232434 2029933 := bbase (se 3 (by rfl) ⟨380612, by rfl⟩ : syracuseStep 2029933 = 761225) (by norm_num)
theorem B2341237 : Blo 1232434 2341237 := bbase (se 5 (by rfl) ⟨109745, by rfl⟩ : syracuseStep 2341237 = 219491) (by norm_num)
theorem B4446581 : Blo 1232434 4446581 := bbase (se 5 (by rfl) ⟨208433, by rfl⟩ : syracuseStep 4446581 = 416867) (by norm_num)
theorem B1849733 : Blo 1232434 1849733 := bbase (se 4 (by rfl) ⟨173412, by rfl⟩ : syracuseStep 1849733 = 346825) (by norm_num)
theorem B2775437 : Blo 1232434 2775437 := bbase (se 3 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 2775437 = 1040789) (by norm_num)
theorem B1407373 : Blo 1232434 1407373 := bbase (se 3 (by rfl) ⟨263882, by rfl⟩ : syracuseStep 1407373 = 527765) (by norm_num)
theorem B5003669 : Blo 1232434 5003669 := bbase (se 6 (by rfl) ⟨117273, by rfl⟩ : syracuseStep 5003669 = 234547) (by norm_num)
theorem B1849757 : Blo 1232434 1849757 := bbase (se 3 (by rfl) ⟨346829, by rfl⟩ : syracuseStep 1849757 = 693659) (by norm_num)
theorem B1849781 : Blo 1232434 1849781 := bbase (se 5 (by rfl) ⟨86708, by rfl⟩ : syracuseStep 1849781 = 173417) (by norm_num)
theorem B5339573 : Blo 1232434 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B1849805 : Blo 1232434 1849805 := bbase (se 3 (by rfl) ⟨346838, by rfl⟩ : syracuseStep 1849805 = 693677) (by norm_num)
theorem B6240725 : Blo 1232434 6240725 := bbase (se 7 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 6240725 = 146267) (by norm_num)
theorem B2775509 : Blo 1232434 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B1849829 : Blo 1232434 1849829 := bbase (se 4 (by rfl) ⟨173421, by rfl⟩ : syracuseStep 1849829 = 346843) (by norm_num)
theorem B1849853 : Blo 1232434 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B2341381 : Blo 1232434 2341381 := bbase (se 4 (by rfl) ⟨219504, by rfl⟩ : syracuseStep 2341381 = 439009) (by norm_num)
theorem B1849877 : Blo 1232434 1849877 := bbase (se 6 (by rfl) ⟨43356, by rfl⟩ : syracuseStep 1849877 = 86713) (by norm_num)
theorem B2775581 : Blo 1232434 2775581 := bbase (se 3 (by rfl) ⟨520421, by rfl⟩ : syracuseStep 2775581 = 1040843) (by norm_num)
theorem B1481257 : Blo 1232434 1481257 := bbase (se 2 (by rfl) ⟨555471, by rfl⟩ : syracuseStep 1481257 = 1110943) (by norm_num)
theorem B1849901 : Blo 1232434 1849901 := bbase (se 3 (by rfl) ⟨346856, by rfl⟩ : syracuseStep 1849901 = 693713) (by norm_num)
theorem B1849925 : Blo 1232434 1849925 := bbase (se 4 (by rfl) ⟨173430, by rfl⟩ : syracuseStep 1849925 = 346861) (by norm_num)
theorem B14047829 : Blo 1232434 14047829 := bbase (se 8 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 14047829 = 164623) (by norm_num)
theorem B1849949 : Blo 1232434 1849949 := bbase (se 3 (by rfl) ⟨346865, by rfl⟩ : syracuseStep 1849949 = 693731) (by norm_num)
theorem B2775653 : Blo 1232434 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1849973 : Blo 1232434 1849973 := bbase (se 5 (by rfl) ⟨86717, by rfl⟩ : syracuseStep 1849973 = 173435) (by norm_num)
theorem B1317493 : Blo 1232434 1317493 := bbase (se 5 (by rfl) ⟨61757, by rfl⟩ : syracuseStep 1317493 = 123515) (by norm_num)
theorem B1849997 : Blo 1232434 1849997 := bbase (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) (by norm_num)
theorem B1481377 : Blo 1232434 1481377 := bbase (se 2 (by rfl) ⟨555516, by rfl⟩ : syracuseStep 1481377 = 1111033) (by norm_num)
theorem B1850021 : Blo 1232434 1850021 := bbase (se 4 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 1850021 = 346879) (by norm_num)
theorem B2341541 : Blo 1232434 2341541 := bbase (se 4 (by rfl) ⟨219519, by rfl⟩ : syracuseStep 2341541 = 439039) (by norm_num)
theorem B2775725 : Blo 1232434 2775725 := bbase (se 3 (by rfl) ⟨520448, by rfl⟩ : syracuseStep 2775725 = 1040897) (by norm_num)
theorem B4881077 : Blo 1232434 4881077 := bbase (se 5 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 4881077 = 457601) (by norm_num)
theorem B1850045 : Blo 1232434 1850045 := bbase (se 3 (by rfl) ⟨346883, by rfl⟩ : syracuseStep 1850045 = 693767) (by norm_num)
theorem B1317565 : Blo 1232434 1317565 := bbase (se 3 (by rfl) ⟨247043, by rfl⟩ : syracuseStep 1317565 = 494087) (by norm_num)
theorem B2251477 : Blo 1232434 2251477 := bbase (se 7 (by rfl) ⟨26384, by rfl⟩ : syracuseStep 2251477 = 52769) (by norm_num)
theorem B4160213 : Blo 1232434 4160213 := bbase (se 7 (by rfl) ⟨48752, by rfl⟩ : syracuseStep 4160213 = 97505) (by norm_num)
theorem B1850069 : Blo 1232434 1850069 := bbase (se 7 (by rfl) ⟨21680, by rfl⟩ : syracuseStep 1850069 = 43361) (by norm_num)
theorem B1850093 : Blo 1232434 1850093 := bbase (se 3 (by rfl) ⟨346892, by rfl⟩ : syracuseStep 1850093 = 693785) (by norm_num)
theorem B2964205 : Blo 1232434 2964205 := bbase (se 3 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 2964205 = 1111577) (by norm_num)
theorem B2775797 : Blo 1232434 2775797 := bbase (se 5 (by rfl) ⟨130115, by rfl⟩ : syracuseStep 2775797 = 260231) (by norm_num)
theorem B1850117 : Blo 1232434 1850117 := bbase (se 4 (by rfl) ⟨173448, by rfl⟩ : syracuseStep 1850117 = 346897) (by norm_num)
theorem B1850141 : Blo 1232434 1850141 := bbase (se 3 (by rfl) ⟨346901, by rfl⟩ : syracuseStep 1850141 = 693803) (by norm_num)
theorem B3119917 : Blo 1232434 3119917 := bbase (se 3 (by rfl) ⟨584984, by rfl⟩ : syracuseStep 3119917 = 1169969) (by norm_num)
theorem B10533685 : Blo 1232434 10533685 := bbase (se 5 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 10533685 = 987533) (by norm_num)
theorem B1850165 : Blo 1232434 1850165 := bbase (se 5 (by rfl) ⟨86726, by rfl⟩ : syracuseStep 1850165 = 173453) (by norm_num)
theorem B2341685 : Blo 1232434 2341685 := bbase (se 5 (by rfl) ⟨109766, by rfl⟩ : syracuseStep 2341685 = 219533) (by norm_num)
theorem B2775869 : Blo 1232434 2775869 := bbase (se 3 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 2775869 = 1040951) (by norm_num)
theorem B1850189 : Blo 1232434 1850189 := bbase (se 3 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 1850189 = 693821) (by norm_num)
theorem B1850213 : Blo 1232434 1850213 := bbase (se 4 (by rfl) ⟨173457, by rfl⟩ : syracuseStep 1850213 = 346915) (by norm_num)
theorem B1317745 : Blo 1232434 1317745 := bbase (se 2 (by rfl) ⟨494154, by rfl⟩ : syracuseStep 1317745 = 988309) (by norm_num)
theorem B4684661 : Blo 1232434 4684661 := bbase (se 5 (by rfl) ⟨219593, by rfl⟩ : syracuseStep 4684661 = 439187) (by norm_num)
theorem B1850237 : Blo 1232434 1850237 := bbase (se 3 (by rfl) ⟨346919, by rfl⟩ : syracuseStep 1850237 = 693839) (by norm_num)
theorem B2775941 : Blo 1232434 2775941 := bbase (se 4 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 2775941 = 520489) (by norm_num)
theorem B1850261 : Blo 1232434 1850261 := bbase (se 6 (by rfl) ⟨43365, by rfl⟩ : syracuseStep 1850261 = 86731) (by norm_num)
theorem B3120029 : Blo 1232434 3120029 := bbase (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) (by norm_num)
theorem B1850285 : Blo 1232434 1850285 := bbase (se 3 (by rfl) ⟨346928, by rfl⟩ : syracuseStep 1850285 = 693857) (by norm_num)
theorem B1850309 : Blo 1232434 1850309 := bbase (se 4 (by rfl) ⟨173466, by rfl⟩ : syracuseStep 1850309 = 346933) (by norm_num)
theorem B2776013 : Blo 1232434 2776013 := bbase (se 3 (by rfl) ⟨520502, by rfl⟩ : syracuseStep 2776013 = 1041005) (by norm_num)
theorem B7904213 : Blo 1232434 7904213 := bbase (se 7 (by rfl) ⟨92627, by rfl⟩ : syracuseStep 7904213 = 185255) (by norm_num)
theorem B1850333 : Blo 1232434 1850333 := bbase (se 3 (by rfl) ⟨346937, by rfl⟩ : syracuseStep 1850333 = 693875) (by norm_num)
theorem B1874917 : Blo 1232434 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B1850357 : Blo 1232434 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B2079749 : Blo 1232434 2079749 := bbase (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) (by norm_num)
theorem B1850381 : Blo 1232434 1850381 := bbase (se 3 (by rfl) ⟨346946, by rfl⟩ : syracuseStep 1850381 = 693893) (by norm_num)
theorem B14998549 : Blo 1232434 14998549 := bbase (se 6 (by rfl) ⟨351528, by rfl⟩ : syracuseStep 14998549 = 703057) (by norm_num)
theorem B2776085 : Blo 1232434 2776085 := bbase (se 6 (by rfl) ⟨65064, by rfl⟩ : syracuseStep 2776085 = 130129) (by norm_num)
theorem B5930005 : Blo 1232434 5930005 := bbase (se 6 (by rfl) ⟨138984, by rfl⟩ : syracuseStep 5930005 = 277969) (by norm_num)
theorem B1850405 : Blo 1232434 1850405 := bbase (se 4 (by rfl) ⟨173475, by rfl⟩ : syracuseStep 1850405 = 346951) (by norm_num)
theorem B1850429 : Blo 1232434 1850429 := bbase (se 3 (by rfl) ⟨346955, by rfl⟩ : syracuseStep 1850429 = 693911) (by norm_num)
theorem B2341973 : Blo 1232434 2341973 := bbase (se 8 (by rfl) ⟨13722, by rfl⟩ : syracuseStep 2341973 = 27445) (by norm_num)
theorem B1850453 : Blo 1232434 1850453 := bbase (se 8 (by rfl) ⟨10842, by rfl⟩ : syracuseStep 1850453 = 21685) (by norm_num)
theorem B3120221 : Blo 1232434 3120221 := bbase (se 3 (by rfl) ⟨585041, by rfl⟩ : syracuseStep 3120221 = 1170083) (by norm_num)
theorem B2776157 : Blo 1232434 2776157 := bbase (se 3 (by rfl) ⟨520529, by rfl⟩ : syracuseStep 2776157 = 1041059) (by norm_num)
theorem B1850477 : Blo 1232434 1850477 := bbase (se 3 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 1850477 = 693929) (by norm_num)
theorem B2079877 : Blo 1232434 2079877 := bbase (se 4 (by rfl) ⟨194988, by rfl⟩ : syracuseStep 2079877 = 389977) (by norm_num)
theorem B4160645 : Blo 1232434 4160645 := bbase (se 4 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 4160645 = 780121) (by norm_num)
theorem B1850501 : Blo 1232434 1850501 := bbase (se 4 (by rfl) ⟨173484, by rfl⟩ : syracuseStep 1850501 = 346969) (by norm_num)
theorem B4684949 : Blo 1232434 4684949 := bbase (se 6 (by rfl) ⟨109803, by rfl⟩ : syracuseStep 4684949 = 219607) (by norm_num)
theorem B1850525 : Blo 1232434 1850525 := bbase (se 3 (by rfl) ⟨346973, by rfl⟩ : syracuseStep 1850525 = 693947) (by norm_num)
theorem B2776229 : Blo 1232434 2776229 := bbase (se 4 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 2776229 = 520543) (by norm_num)
theorem B1850549 : Blo 1232434 1850549 := bbase (se 5 (by rfl) ⟨86744, by rfl⟩ : syracuseStep 1850549 = 173489) (by norm_num)
theorem B1850573 : Blo 1232434 1850573 := bbase (se 3 (by rfl) ⟨346982, by rfl⟩ : syracuseStep 1850573 = 693965) (by norm_num)
theorem B2079965 : Blo 1232434 2079965 := bbase (se 3 (by rfl) ⟨389993, by rfl⟩ : syracuseStep 2079965 = 779987) (by norm_num)
theorem B1850597 : Blo 1232434 1850597 := bbase (se 4 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 1850597 = 346987) (by norm_num)
theorem B2342125 : Blo 1232434 2342125 := bbase (se 3 (by rfl) ⟨439148, by rfl⟩ : syracuseStep 2342125 = 878297) (by norm_num)
theorem B2776301 : Blo 1232434 2776301 := bbase (se 3 (by rfl) ⟨520556, by rfl⟩ : syracuseStep 2776301 = 1041113) (by norm_num)
theorem B1850621 : Blo 1232434 1850621 := bbase (se 3 (by rfl) ⟨346991, by rfl⟩ : syracuseStep 1850621 = 693983) (by norm_num)
theorem B1850645 : Blo 1232434 1850645 := bbase (se 6 (by rfl) ⟨43374, by rfl⟩ : syracuseStep 1850645 = 86749) (by norm_num)
theorem B1850669 : Blo 1232434 1850669 := bbase (se 3 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 1850669 = 694001) (by norm_num)
theorem B1318189 : Blo 1232434 1318189 := bbase (se 3 (by rfl) ⟨247160, by rfl⟩ : syracuseStep 1318189 = 494321) (by norm_num)
theorem B5266741 : Blo 1232434 5266741 := bbase (se 5 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 5266741 = 493757) (by norm_num)
theorem B2776373 : Blo 1232434 2776373 := bbase (se 5 (by rfl) ⟨130142, by rfl⟩ : syracuseStep 2776373 = 260285) (by norm_num)
theorem B1850693 : Blo 1232434 1850693 := bbase (se 4 (by rfl) ⟨173502, by rfl⟩ : syracuseStep 1850693 = 347005) (by norm_num)
theorem B2080093 : Blo 1232434 2080093 := bbase (se 3 (by rfl) ⟨390017, by rfl⟩ : syracuseStep 2080093 = 780035) (by norm_num)
theorem B1850717 : Blo 1232434 1850717 := bbase (se 3 (by rfl) ⟨347009, by rfl⟩ : syracuseStep 1850717 = 694019) (by norm_num)
theorem B1850741 : Blo 1232434 1850741 := bbase (se 5 (by rfl) ⟨86753, by rfl⟩ : syracuseStep 1850741 = 173507) (by norm_num)
theorem B2776445 : Blo 1232434 2776445 := bbase (se 3 (by rfl) ⟨520583, by rfl⟩ : syracuseStep 2776445 = 1041167) (by norm_num)
theorem B2964869 : Blo 1232434 2964869 := bbase (se 4 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 2964869 = 555913) (by norm_num)
theorem B1850765 : Blo 1232434 1850765 := bbase (se 3 (by rfl) ⟨347018, by rfl⟩ : syracuseStep 1850765 = 694037) (by norm_num)
theorem B1850789 : Blo 1232434 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B2080181 : Blo 1232434 2080181 := bbase (se 5 (by rfl) ⟨97508, by rfl⟩ : syracuseStep 2080181 = 195017) (by norm_num)
theorem B3120565 : Blo 1232434 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B1850813 : Blo 1232434 1850813 := bbase (se 3 (by rfl) ⟨347027, by rfl⟩ : syracuseStep 1850813 = 694055) (by norm_num)
theorem B2776517 : Blo 1232434 2776517 := bbase (se 4 (by rfl) ⟨260298, by rfl⟩ : syracuseStep 2776517 = 520597) (by norm_num)
theorem B1850837 : Blo 1232434 1850837 := bbase (se 7 (by rfl) ⟨21689, by rfl⟩ : syracuseStep 1850837 = 43379) (by norm_num)
theorem B1850861 : Blo 1232434 1850861 := bbase (se 3 (by rfl) ⟨347036, by rfl⟩ : syracuseStep 1850861 = 694073) (by norm_num)
theorem B1850885 : Blo 1232434 1850885 := bbase (se 4 (by rfl) ⟨173520, by rfl⟩ : syracuseStep 1850885 = 347041) (by norm_num)
theorem B2776589 : Blo 1232434 2776589 := bbase (se 3 (by rfl) ⟨520610, by rfl⟩ : syracuseStep 2776589 = 1041221) (by norm_num)
theorem B2342429 : Blo 1232434 2342429 := bbase (se 3 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 2342429 = 878411) (by norm_num)
theorem B1850909 : Blo 1232434 1850909 := bbase (se 3 (by rfl) ⟨347045, by rfl⟩ : syracuseStep 1850909 = 694091) (by norm_num)
theorem B3120677 : Blo 1232434 3120677 := bbase (se 4 (by rfl) ⟨292563, by rfl⟩ : syracuseStep 3120677 = 585127) (by norm_num)
theorem B2080309 : Blo 1232434 2080309 := bbase (se 5 (by rfl) ⟨97514, by rfl⟩ : syracuseStep 2080309 = 195029) (by norm_num)
theorem B4161077 : Blo 1232434 4161077 := bbase (se 5 (by rfl) ⟨195050, by rfl⟩ : syracuseStep 4161077 = 390101) (by norm_num)
theorem B1850933 : Blo 1232434 1850933 := bbase (se 5 (by rfl) ⟨86762, by rfl⟩ : syracuseStep 1850933 = 173525) (by norm_num)
theorem B1334845 : Blo 1232434 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B1850957 : Blo 1232434 1850957 := bbase (se 3 (by rfl) ⟨347054, by rfl⟩ : syracuseStep 1850957 = 694109) (by norm_num)
theorem B2776661 : Blo 1232434 2776661 := bbase (se 8 (by rfl) ⟨16269, by rfl⟩ : syracuseStep 2776661 = 32539) (by norm_num)
theorem B1850981 : Blo 1232434 1850981 := bbase (se 4 (by rfl) ⟨173529, by rfl⟩ : syracuseStep 1850981 = 347059) (by norm_num)
theorem B1851005 : Blo 1232434 1851005 := bbase (se 3 (by rfl) ⟨347063, by rfl⟩ : syracuseStep 1851005 = 694127) (by norm_num)
theorem B2080397 : Blo 1232434 2080397 := bbase (se 3 (by rfl) ⟨390074, by rfl⟩ : syracuseStep 2080397 = 780149) (by norm_num)
theorem B1851029 : Blo 1232434 1851029 := bbase (se 6 (by rfl) ⟨43383, by rfl⟩ : syracuseStep 1851029 = 86767) (by norm_num)
theorem B2776733 : Blo 1232434 2776733 := bbase (se 3 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 2776733 = 1041275) (by norm_num)
theorem B2965157 : Blo 1232434 2965157 := bbase (se 4 (by rfl) ⟨277983, by rfl⟩ : syracuseStep 2965157 = 555967) (by norm_num)
theorem B1851053 : Blo 1232434 1851053 := bbase (se 3 (by rfl) ⟨347072, by rfl⟩ : syracuseStep 1851053 = 694145) (by norm_num)
theorem B1851077 : Blo 1232434 1851077 := bbase (se 4 (by rfl) ⟨173538, by rfl⟩ : syracuseStep 1851077 = 347077) (by norm_num)
theorem B1851101 : Blo 1232434 1851101 := bbase (se 3 (by rfl) ⟨347081, by rfl⟩ : syracuseStep 1851101 = 694163) (by norm_num)
theorem B3120869 : Blo 1232434 3120869 := bbase (se 4 (by rfl) ⟨292581, by rfl⟩ : syracuseStep 3120869 = 585163) (by norm_num)
theorem B6242021 : Blo 1232434 6242021 := bbase (se 4 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 6242021 = 1170379) (by norm_num)
theorem B2776805 : Blo 1232434 2776805 := bbase (se 4 (by rfl) ⟨260325, by rfl⟩ : syracuseStep 2776805 = 520651) (by norm_num)
theorem B1851125 : Blo 1232434 1851125 := bbase (se 5 (by rfl) ⟨86771, by rfl⟩ : syracuseStep 1851125 = 173543) (by norm_num)
theorem B2080525 : Blo 1232434 2080525 := bbase (se 3 (by rfl) ⟨390098, by rfl⟩ : syracuseStep 2080525 = 780197) (by norm_num)
theorem B1851149 : Blo 1232434 1851149 := bbase (se 3 (by rfl) ⟨347090, by rfl⟩ : syracuseStep 1851149 = 694181) (by norm_num)
theorem B1851173 : Blo 1232434 1851173 := bbase (se 4 (by rfl) ⟨173547, by rfl⟩ : syracuseStep 1851173 = 347095) (by norm_num)
theorem B2776877 : Blo 1232434 2776877 := bbase (se 3 (by rfl) ⟨520664, by rfl⟩ : syracuseStep 2776877 = 1041329) (by norm_num)
theorem B1851197 : Blo 1232434 1851197 := bbase (se 3 (by rfl) ⟨347099, by rfl⟩ : syracuseStep 1851197 = 694199) (by norm_num)
theorem B1851221 : Blo 1232434 1851221 := bbase (se 9 (by rfl) ⟨5423, by rfl⟩ : syracuseStep 1851221 = 10847) (by norm_num)
theorem B2080613 : Blo 1232434 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B1851245 : Blo 1232434 1851245 := bbase (se 3 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 1851245 = 694217) (by norm_num)
theorem B2776949 : Blo 1232434 2776949 := bbase (se 5 (by rfl) ⟨130169, by rfl⟩ : syracuseStep 2776949 = 260339) (by norm_num)
theorem B1851269 : Blo 1232434 1851269 := bbase (se 4 (by rfl) ⟨173556, by rfl⟩ : syracuseStep 1851269 = 347113) (by norm_num)
theorem B1851293 : Blo 1232434 1851293 := bbase (se 3 (by rfl) ⟨347117, by rfl⟩ : syracuseStep 1851293 = 694235) (by norm_num)
theorem B1851317 : Blo 1232434 1851317 := bbase (se 5 (by rfl) ⟨86780, by rfl⟩ : syracuseStep 1851317 = 173561) (by norm_num)
theorem B2777021 : Blo 1232434 2777021 := bbase (se 3 (by rfl) ⟨520691, by rfl⟩ : syracuseStep 2777021 = 1041383) (by norm_num)
theorem B1974221 : Blo 1232434 1974221 := bbase (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) (by norm_num)
theorem B1851341 : Blo 1232434 1851341 := bbase (se 3 (by rfl) ⟨347126, by rfl⟩ : syracuseStep 1851341 = 694253) (by norm_num)
theorem B2080741 : Blo 1232434 2080741 := bbase (se 4 (by rfl) ⟨195069, by rfl⟩ : syracuseStep 2080741 = 390139) (by norm_num)
theorem B4161509 : Blo 1232434 4161509 := bbase (se 4 (by rfl) ⟨390141, by rfl⟩ : syracuseStep 4161509 = 780283) (by norm_num)
theorem B1851365 : Blo 1232434 1851365 := bbase (se 4 (by rfl) ⟨173565, by rfl⟩ : syracuseStep 1851365 = 347131) (by norm_num)
theorem B1851389 : Blo 1232434 1851389 := bbase (se 3 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 1851389 = 694271) (by norm_num)
theorem B2342915 : Blo 1232434 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B1851395 : Blo 1232434 1851395 := bstep (se 1 (by rfl) ⟨1388546, by rfl⟩ : syracuseStep 1851395 = 2777093) B2777093
theorem B1851425 : Blo 1232434 1851425 := bstep (se 2 (by rfl) ⟨694284, by rfl⟩ : syracuseStep 1851425 = 1388569) B1388569
theorem B1851443 : Blo 1232434 1851443 := bstep (se 1 (by rfl) ⟨1388582, by rfl⟩ : syracuseStep 1851443 = 2777165) B2777165
theorem B4161617 : Blo 1232434 4161617 := bstep (se 2 (by rfl) ⟨1560606, by rfl⟩ : syracuseStep 4161617 = 3121213) B3121213
theorem B2080849 : Blo 1232434 2080849 := bstep (se 2 (by rfl) ⟨780318, by rfl⟩ : syracuseStep 2080849 = 1560637) B1560637
theorem B1851473 : Blo 1232434 1851473 := bstep (se 2 (by rfl) ⟨694302, by rfl⟩ : syracuseStep 1851473 = 1388605) B1388605
theorem B1851491 : Blo 1232434 1851491 := bstep (se 1 (by rfl) ⟨1388618, by rfl⟩ : syracuseStep 1851491 = 2777237) B2777237
theorem B8896625 : Blo 1232434 8896625 := bstep (se 2 (by rfl) ⟨3336234, by rfl⟩ : syracuseStep 8896625 = 6672469) B6672469
theorem B2777201 : Blo 1232434 2777201 := bstep (se 2 (by rfl) ⟨1041450, by rfl⟩ : syracuseStep 2777201 = 2082901) B2082901
theorem B2080883 : Blo 1232434 2080883 := bstep (se 1 (by rfl) ⟨1560662, by rfl⟩ : syracuseStep 2080883 = 3121325) B3121325
theorem B1851521 : Blo 1232434 1851521 := bstep (se 2 (by rfl) ⟨694320, by rfl⟩ : syracuseStep 1851521 = 1388641) B1388641
theorem B3514499 : Blo 1232434 3514499 := bstep (se 1 (by rfl) ⟨2635874, by rfl⟩ : syracuseStep 3514499 = 5271749) B5271749
theorem B2777219 : Blo 1232434 2777219 := bstep (se 1 (by rfl) ⟨2082914, by rfl⟩ : syracuseStep 2777219 = 4165829) B4165829
theorem B2670737 : Blo 1232434 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B1851539 : Blo 1232434 1851539 := bstep (se 1 (by rfl) ⟨1388654, by rfl⟩ : syracuseStep 1851539 = 2777309) B2777309
theorem B1851569 : Blo 1232434 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1851587 : Blo 1232434 1851587 := bstep (se 1 (by rfl) ⟨1388690, by rfl⟩ : syracuseStep 1851587 = 2777381) B2777381
theorem B1851617 : Blo 1232434 1851617 := bstep (se 2 (by rfl) ⟨694356, by rfl⟩ : syracuseStep 1851617 = 1388713) B1388713
theorem B5931235 : Blo 1232434 5931235 := bstep (se 1 (by rfl) ⟨4448426, by rfl⟩ : syracuseStep 5931235 = 8896853) B8896853
theorem B2081011 : Blo 1232434 2081011 := bstep (se 1 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 2081011 = 3121517) B3121517
theorem B1851635 : Blo 1232434 1851635 := bstep (se 1 (by rfl) ⟨1388726, by rfl⟩ : syracuseStep 1851635 = 2777453) B2777453
theorem B3514691 : Blo 1232434 3514691 := bstep (se 1 (by rfl) ⟨2636018, by rfl⟩ : syracuseStep 3514691 = 5272037) B5272037
theorem B7119173 : Blo 1232434 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B2498915 : Blo 1232434 2498915 := bstep (se 1 (by rfl) ⟨1874186, by rfl⟩ : syracuseStep 2498915 = 3748373) B3748373
theorem B2081153 : Blo 1232434 2081153 := bstep (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) B1560865
theorem B1974721 : Blo 1232434 1974721 := bstep (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) B1481041
theorem B5923277 : Blo 1232434 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B3121649 : Blo 1232434 3121649 := bstep (se 2 (by rfl) ⟨1170618, by rfl⟩ : syracuseStep 3121649 = 2341237) B2341237
theorem B2081281 : Blo 1232434 2081281 := bstep (se 2 (by rfl) ⟨780480, by rfl⟩ : syracuseStep 2081281 = 1560961) B1560961
theorem B3121699 : Blo 1232434 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B2081315 : Blo 1232434 2081315 := bstep (se 1 (by rfl) ⟨1560986, by rfl⟩ : syracuseStep 2081315 = 3121973) B3121973
theorem B4448803 : Blo 1232434 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B4162157 : Blo 1232434 4162157 := bstep (se 3 (by rfl) ⟨780404, by rfl⟩ : syracuseStep 4162157 = 1560809) B1560809
theorem B4162211 : Blo 1232434 4162211 := bstep (se 1 (by rfl) ⟨3121658, by rfl⟩ : syracuseStep 4162211 = 6243317) B6243317
theorem B2081443 : Blo 1232434 2081443 := bstep (se 1 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 2081443 = 3122165) B3122165
theorem B6668963 : Blo 1232434 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B6242993 : Blo 1232434 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B3121841 : Blo 1232434 3121841 := bstep (se 2 (by rfl) ⟨1170690, by rfl⟩ : syracuseStep 3121841 = 2341381) B2341381
theorem B4686605 : Blo 1232434 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B2081585 : Blo 1232434 2081585 := bstep (se 2 (by rfl) ⟨780594, by rfl⟩ : syracuseStep 2081585 = 1561189) B1561189
theorem B4219715 : Blo 1232434 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B3162979 : Blo 1232434 3162979 := bstep (se 1 (by rfl) ⟨2372234, by rfl⟩ : syracuseStep 3162979 = 4744469) B4744469
theorem B1975169 : Blo 1232434 1975169 := bstep (se 2 (by rfl) ⟨740688, by rfl⟩ : syracuseStep 1975169 = 1481377) B1481377
theorem B14041997 : Blo 1232434 14041997 := bstep (se 3 (by rfl) ⟨2632874, by rfl⟩ : syracuseStep 14041997 = 5265749) B5265749
theorem B7906211 : Blo 1232434 7906211 := bstep (se 1 (by rfl) ⟨5929658, by rfl⟩ : syracuseStep 7906211 = 11859317) B11859317
theorem B4162481 : Blo 1232434 4162481 := bstep (se 2 (by rfl) ⟨1560930, by rfl⟩ : syracuseStep 4162481 = 3121861) B3121861
theorem B2081713 : Blo 1232434 2081713 := bstep (se 2 (by rfl) ⟨780642, by rfl⟩ : syracuseStep 2081713 = 1561285) B1561285
theorem B3949517 : Blo 1232434 3949517 := bstep (se 3 (by rfl) ⟨740534, by rfl⟩ : syracuseStep 3949517 = 1481069) B1481069
theorem B2081747 : Blo 1232434 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B7021637 : Blo 1232434 7021637 := bstep (se 4 (by rfl) ⟨658278, by rfl⟩ : syracuseStep 7021637 = 1316557) B1316557
theorem B2081875 : Blo 1232434 2081875 := bstep (se 1 (by rfl) ⟨1561406, by rfl⟩ : syracuseStep 2081875 = 3122813) B3122813
theorem B2082017 : Blo 1232434 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B7496945 : Blo 1232434 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B2082145 : Blo 1232434 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B19998065 : Blo 1232434 19998065 := bstep (se 2 (by rfl) ⟨7499274, by rfl⟩ : syracuseStep 19998065 = 14998549) B14998549
theorem B7906673 : Blo 1232434 7906673 := bstep (se 2 (by rfl) ⟨2965002, by rfl⟩ : syracuseStep 7906673 = 5930005) B5930005
theorem B3949955 : Blo 1232434 3949955 := bstep (se 1 (by rfl) ⟨2962466, by rfl⟩ : syracuseStep 3949955 = 5924933) B5924933
theorem B2082179 : Blo 1232434 2082179 := bstep (se 1 (by rfl) ⟨1561634, by rfl⟩ : syracuseStep 2082179 = 3123269) B3123269
theorem B3335597 : Blo 1232434 3335597 := bstep (se 3 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 3335597 = 1250849) B1250849
theorem B16885189 : Blo 1232434 16885189 := bstep (se 4 (by rfl) ⟨1582986, by rfl⟩ : syracuseStep 16885189 = 3165973) B3165973
theorem B4163021 : Blo 1232434 4163021 := bstep (se 3 (by rfl) ⟨780566, by rfl⟩ : syracuseStep 4163021 = 1561133) B1561133
theorem B4220369 : Blo 1232434 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B10536419 : Blo 1232434 10536419 := bstep (se 1 (by rfl) ⟨7902314, by rfl⟩ : syracuseStep 10536419 = 15804629) B15804629
theorem B3335651 : Blo 1232434 3335651 := bstep (se 1 (by rfl) ⟨2501738, by rfl⟩ : syracuseStep 3335651 = 5003477) B5003477
theorem B4163075 : Blo 1232434 4163075 := bstep (se 1 (by rfl) ⟨3122306, by rfl⟩ : syracuseStep 4163075 = 6244613) B6244613
theorem B2082307 : Blo 1232434 2082307 := bstep (se 1 (by rfl) ⟨1561730, by rfl⟩ : syracuseStep 2082307 = 3123461) B3123461
theorem B3335779 : Blo 1232434 3335779 := bstep (se 1 (by rfl) ⟨2501834, by rfl⟩ : syracuseStep 3335779 = 5003669) B5003669
theorem B7030385 : Blo 1232434 7030385 := bstep (se 2 (by rfl) ⟨2636394, by rfl⟩ : syracuseStep 7030385 = 5272789) B5272789
theorem B3122833 : Blo 1232434 3122833 := bstep (se 2 (by rfl) ⟨1171062, by rfl⟩ : syracuseStep 3122833 = 2342125) B2342125
theorem B2082449 : Blo 1232434 2082449 := bstep (se 2 (by rfl) ⟨780918, by rfl⟩ : syracuseStep 2082449 = 1561837) B1561837
theorem B6670001 : Blo 1232434 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B2221777 : Blo 1232434 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B9365219 : Blo 1232434 9365219 := bstep (se 1 (by rfl) ⟨7023914, by rfl⟩ : syracuseStep 9365219 = 14047829) B14047829
theorem B7022321 : Blo 1232434 7022321 := bstep (se 2 (by rfl) ⟨2633370, by rfl⟩ : syracuseStep 7022321 = 5266741) B5266741
theorem B4007693 : Blo 1232434 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B4163345 : Blo 1232434 4163345 := bstep (se 2 (by rfl) ⟨1561254, by rfl⟩ : syracuseStep 4163345 = 3122509) B3122509
theorem B2082577 : Blo 1232434 2082577 := bstep (se 2 (by rfl) ⟨780966, by rfl⟩ : syracuseStep 2082577 = 1561933) B1561933
theorem B3254051 : Blo 1232434 3254051 := bstep (se 1 (by rfl) ⟨2440538, by rfl⟩ : syracuseStep 3254051 = 4881077) B4881077
theorem B2082611 : Blo 1232434 2082611 := bstep (se 1 (by rfl) ⟨1561958, by rfl⟩ : syracuseStep 2082611 = 3123917) B3123917
theorem B3123107 : Blo 1232434 3123107 := bstep (se 1 (by rfl) ⟨2342330, by rfl⟩ : syracuseStep 3123107 = 4684661) B4684661
theorem B2082739 : Blo 1232434 2082739 := bstep (se 1 (by rfl) ⟨1562054, by rfl⟩ : syracuseStep 2082739 = 3124109) B3124109
theorem B5269475 : Blo 1232434 5269475 := bstep (se 1 (by rfl) ⟨3952106, by rfl⟩ : syracuseStep 5269475 = 7904213) B7904213
theorem B4278257 : Blo 1232434 4278257 := bstep (se 2 (by rfl) ⟨1604346, by rfl⟩ : syracuseStep 4278257 = 3208693) B3208693
theorem B1386499 : Blo 1232434 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B2082881 : Blo 1232434 2082881 := bstep (se 2 (by rfl) ⟨781080, by rfl⟩ : syracuseStep 2082881 = 1562161) B1562161
theorem B7505989 : Blo 1232434 7505989 := bstep (se 4 (by rfl) ⟨703686, by rfl⟩ : syracuseStep 7505989 = 1407373) B1407373
theorem B6244451 : Blo 1232434 6244451 := bstep (se 1 (by rfl) ⟨4683338, by rfl⟩ : syracuseStep 6244451 = 9366677) B9366677
theorem B3123299 : Blo 1232434 3123299 := bstep (se 1 (by rfl) ⟨2342474, by rfl⟩ : syracuseStep 3123299 = 4684949) B4684949
theorem B1386643 : Blo 1232434 1386643 := bstep (se 1 (by rfl) ⟨1039982, by rfl⟩ : syracuseStep 1386643 = 2079965) B2079965
theorem B2083009 : Blo 1232434 2083009 := bstep (se 2 (by rfl) ⟨781128, by rfl⟩ : syracuseStep 2083009 = 1562257) B1562257
theorem B8890565 : Blo 1232434 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B2083043 : Blo 1232434 2083043 := bstep (se 1 (by rfl) ⟨1562282, by rfl⟩ : syracuseStep 2083043 = 3124565) B3124565
theorem B1976579 : Blo 1232434 1976579 := bstep (se 1 (by rfl) ⟨1482434, by rfl⟩ : syracuseStep 1976579 = 2964869) B2964869
theorem B1386787 : Blo 1232434 1386787 := bstep (se 1 (by rfl) ⟨1040090, by rfl⟩ : syracuseStep 1386787 = 2080181) B2080181
theorem B1755427 : Blo 1232434 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B4163885 : Blo 1232434 4163885 := bstep (se 3 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 4163885 = 1561457) B1561457
theorem B4163939 : Blo 1232434 4163939 := bstep (se 1 (by rfl) ⟨3122954, by rfl⟩ : syracuseStep 4163939 = 6245909) B6245909
theorem B3336557 : Blo 1232434 3336557 := bstep (se 3 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 3336557 = 1251209) B1251209
theorem B1755523 : Blo 1232434 1755523 := bstep (se 1 (by rfl) ⟨1316642, by rfl⟩ : syracuseStep 1755523 = 2633285) B2633285
theorem B1386931 : Blo 1232434 1386931 := bstep (se 1 (by rfl) ⟨1040198, by rfl⟩ : syracuseStep 1386931 = 2080397) B2080397
theorem B1976771 : Blo 1232434 1976771 := bstep (se 1 (by rfl) ⟨1482578, by rfl⟩ : syracuseStep 1976771 = 2965157) B2965157
theorem B4999715 : Blo 1232434 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B1387075 : Blo 1232434 1387075 := bstep (se 1 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 1387075 = 2080613) B2080613
theorem B4164209 : Blo 1232434 4164209 := bstep (se 2 (by rfl) ⟨1561578, by rfl⟩ : syracuseStep 4164209 = 3123157) B3123157
theorem B4508273 : Blo 1232434 4508273 := bstep (se 2 (by rfl) ⟨1690602, by rfl⟩ : syracuseStep 4508273 = 3381205) B3381205
theorem B11250373 : Blo 1232434 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B1387219 : Blo 1232434 1387219 := bstep (se 1 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 1387219 = 2080829) B2080829
theorem B4999907 : Blo 1232434 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B1501939 : Blo 1232434 1501939 := bstep (se 1 (by rfl) ⟨1126454, by rfl⟩ : syracuseStep 1501939 = 2252909) B2252909
theorem B1665857 : Blo 1232434 1665857 := bstep (se 2 (by rfl) ⟨624696, by rfl⟩ : syracuseStep 1665857 = 1249393) B1249393
theorem B1387363 : Blo 1232434 1387363 := bstep (se 1 (by rfl) ⟨1040522, by rfl⟩ : syracuseStep 1387363 = 2081045) B2081045
theorem B1756019 : Blo 1232434 1756019 := bstep (se 1 (by rfl) ⟨1317014, by rfl⟩ : syracuseStep 1756019 = 2634029) B2634029
theorem B7900037 : Blo 1232434 7900037 := bstep (se 4 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 7900037 = 1481257) B1481257
theorem B6245261 : Blo 1232434 6245261 := bstep (se 3 (by rfl) ⟨1170986, by rfl⟩ : syracuseStep 6245261 = 2341973) B2341973
theorem B1387507 : Blo 1232434 1387507 := bstep (se 1 (by rfl) ⟨1040630, by rfl⟩ : syracuseStep 1387507 = 2081261) B2081261
theorem B3124241 : Blo 1232434 3124241 := bstep (se 2 (by rfl) ⟨1171590, by rfl⟩ : syracuseStep 3124241 = 2343181) B2343181
theorem B3124291 : Blo 1232434 3124291 := bstep (se 1 (by rfl) ⟨2343218, by rfl⟩ : syracuseStep 3124291 = 4686437) B4686437
theorem B1387651 : Blo 1232434 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B4164749 : Blo 1232434 4164749 := bstep (se 3 (by rfl) ⟨780890, by rfl⟩ : syracuseStep 4164749 = 1561781) B1561781
theorem B2706577 : Blo 1232434 2706577 := bstep (se 2 (by rfl) ⟨1014966, by rfl⟩ : syracuseStep 2706577 = 2029933) B2029933
theorem B7023779 : Blo 1232434 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B4164803 : Blo 1232434 4164803 := bstep (se 1 (by rfl) ⟨3123602, by rfl⟩ : syracuseStep 4164803 = 6247205) B6247205
theorem B3124433 : Blo 1232434 3124433 := bstep (se 2 (by rfl) ⟨1171662, by rfl⟩ : syracuseStep 3124433 = 2343325) B2343325
theorem B3951875 : Blo 1232434 3951875 := bstep (se 1 (by rfl) ⟨2963906, by rfl⟩ : syracuseStep 3951875 = 5927813) B5927813
theorem B1559827 : Blo 1232434 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B1387795 : Blo 1232434 1387795 := bstep (se 1 (by rfl) ⟨1040846, by rfl⟩ : syracuseStep 1387795 = 2081693) B2081693
theorem B6761861 : Blo 1232434 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B1387939 : Blo 1232434 1387939 := bstep (se 1 (by rfl) ⟨1040954, by rfl⟩ : syracuseStep 1387939 = 2081909) B2081909
theorem B4165073 : Blo 1232434 4165073 := bstep (se 2 (by rfl) ⟨1561902, by rfl⟩ : syracuseStep 4165073 = 3123805) B3123805
theorem B2108897 : Blo 1232434 2108897 := bstep (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) B1581673
theorem B1756657 : Blo 1232434 1756657 := bstep (se 2 (by rfl) ⟨658746, by rfl⟩ : syracuseStep 1756657 = 1317493) B1317493
theorem B2633251 : Blo 1232434 2633251 := bstep (se 1 (by rfl) ⟨1974938, by rfl⟩ : syracuseStep 2633251 = 3949877) B3949877
theorem B1232435 : Blo 1232434 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B1388083 : Blo 1232434 1388083 := bstep (se 1 (by rfl) ⟨1041062, by rfl⟩ : syracuseStep 1388083 = 2082125) B2082125
theorem B1232451 : Blo 1232434 1232451 := bstep (se 1 (by rfl) ⟨924338, by rfl⟩ : syracuseStep 1232451 = 1848677) B1848677
theorem B5779021 : Blo 1232434 5779021 := bstep (se 3 (by rfl) ⟨1083566, by rfl⟩ : syracuseStep 5779021 = 2167133) B2167133
theorem B1232467 : Blo 1232434 1232467 := bstep (se 1 (by rfl) ⟨924350, by rfl⟩ : syracuseStep 1232467 = 1848701) B1848701
theorem B1232483 : Blo 1232434 1232483 := bstep (se 1 (by rfl) ⟨924362, by rfl⟩ : syracuseStep 1232483 = 1848725) B1848725
theorem B3001969 : Blo 1232434 3001969 := bstep (se 2 (by rfl) ⟨1125738, by rfl⟩ : syracuseStep 3001969 = 2251477) B2251477
theorem B1232499 : Blo 1232434 1232499 := bstep (se 1 (by rfl) ⟨924374, by rfl⟩ : syracuseStep 1232499 = 1848749) B1848749
theorem B1232515 : Blo 1232434 1232515 := bstep (se 1 (by rfl) ⟨924386, by rfl⟩ : syracuseStep 1232515 = 1848773) B1848773
theorem B11857549 : Blo 1232434 11857549 := bstep (se 3 (by rfl) ⟨2223290, by rfl⟩ : syracuseStep 11857549 = 4446581) B4446581
theorem B2502289 : Blo 1232434 2502289 := bstep (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) B1876717
theorem B1232531 : Blo 1232434 1232531 := bstep (se 1 (by rfl) ⟨924398, by rfl⟩ : syracuseStep 1232531 = 1848797) B1848797
theorem B1232547 : Blo 1232434 1232547 := bstep (se 1 (by rfl) ⟨924410, by rfl⟩ : syracuseStep 1232547 = 1848821) B1848821
theorem B2109091 : Blo 1232434 2109091 := bstep (se 1 (by rfl) ⟨1581818, by rfl⟩ : syracuseStep 2109091 = 3163637) B3163637
theorem B1232563 : Blo 1232434 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B1232579 : Blo 1232434 1232579 := bstep (se 1 (by rfl) ⟨924434, by rfl⟩ : syracuseStep 1232579 = 1848869) B1848869
theorem B1388227 : Blo 1232434 1388227 := bstep (se 1 (by rfl) ⟨1041170, by rfl⟩ : syracuseStep 1388227 = 2082341) B2082341
theorem B6672077 : Blo 1232434 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B1232595 : Blo 1232434 1232595 := bstep (se 1 (by rfl) ⟨924446, by rfl⟩ : syracuseStep 1232595 = 1848893) B1848893
theorem B1232611 : Blo 1232434 1232611 := bstep (se 1 (by rfl) ⟨924458, by rfl⟩ : syracuseStep 1232611 = 1848917) B1848917
theorem B14044913 : Blo 1232434 14044913 := bstep (se 2 (by rfl) ⟨5266842, by rfl⟩ : syracuseStep 14044913 = 10533685) B10533685
theorem B1232627 : Blo 1232434 1232627 := bstep (se 1 (by rfl) ⟨924470, by rfl⟩ : syracuseStep 1232627 = 1848941) B1848941
theorem B1232643 : Blo 1232434 1232643 := bstep (se 1 (by rfl) ⟨924482, by rfl⟩ : syracuseStep 1232643 = 1848965) B1848965
theorem B1560323 : Blo 1232434 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B1232659 : Blo 1232434 1232659 := bstep (se 1 (by rfl) ⟨924494, by rfl⟩ : syracuseStep 1232659 = 1848989) B1848989
theorem B1232675 : Blo 1232434 1232675 := bstep (se 1 (by rfl) ⟨924506, by rfl⟩ : syracuseStep 1232675 = 1849013) B1849013
theorem B1232691 : Blo 1232434 1232691 := bstep (se 1 (by rfl) ⟨924518, by rfl⟩ : syracuseStep 1232691 = 1849037) B1849037
theorem B1756993 : Blo 1232434 1756993 := bstep (se 2 (by rfl) ⟨658872, by rfl⟩ : syracuseStep 1756993 = 1317745) B1317745
theorem B1232707 : Blo 1232434 1232707 := bstep (se 1 (by rfl) ⟨924530, by rfl⟩ : syracuseStep 1232707 = 1849061) B1849061
theorem B1232723 : Blo 1232434 1232723 := bstep (se 1 (by rfl) ⟨924542, by rfl⟩ : syracuseStep 1232723 = 1849085) B1849085
theorem B1388371 : Blo 1232434 1388371 := bstep (se 1 (by rfl) ⟨1041278, by rfl⟩ : syracuseStep 1388371 = 2082557) B2082557
theorem B1232739 : Blo 1232434 1232739 := bstep (se 1 (by rfl) ⟨924554, by rfl⟩ : syracuseStep 1232739 = 1849109) B1849109
theorem B3510125 : Blo 1232434 3510125 := bstep (se 3 (by rfl) ⟨658148, by rfl⟩ : syracuseStep 3510125 = 1316297) B1316297
theorem B1232755 : Blo 1232434 1232755 := bstep (se 1 (by rfl) ⟨924566, by rfl⟩ : syracuseStep 1232755 = 1849133) B1849133
theorem B1232771 : Blo 1232434 1232771 := bstep (se 1 (by rfl) ⟨924578, by rfl⟩ : syracuseStep 1232771 = 1849157) B1849157
theorem B1232787 : Blo 1232434 1232787 := bstep (se 1 (by rfl) ⟨924590, by rfl⟩ : syracuseStep 1232787 = 1849181) B1849181
theorem B1232803 : Blo 1232434 1232803 := bstep (se 1 (by rfl) ⟨924602, by rfl⟩ : syracuseStep 1232803 = 1849205) B1849205
theorem B1232819 : Blo 1232434 1232819 := bstep (se 1 (by rfl) ⟨924614, by rfl⟩ : syracuseStep 1232819 = 1849229) B1849229
theorem B1232835 : Blo 1232434 1232835 := bstep (se 1 (by rfl) ⟨924626, by rfl⟩ : syracuseStep 1232835 = 1849253) B1849253
theorem B1232851 : Blo 1232434 1232851 := bstep (se 1 (by rfl) ⟨924638, by rfl⟩ : syracuseStep 1232851 = 1849277) B1849277
theorem B3002339 : Blo 1232434 3002339 := bstep (se 1 (by rfl) ⟨2251754, by rfl⟩ : syracuseStep 3002339 = 4503509) B4503509
theorem B1232867 : Blo 1232434 1232867 := bstep (se 1 (by rfl) ⟨924650, by rfl⟩ : syracuseStep 1232867 = 1849301) B1849301
theorem B20279267 : Blo 1232434 20279267 := bstep (se 1 (by rfl) ⟨15209450, by rfl⟩ : syracuseStep 20279267 = 30418901) B30418901
theorem B1388515 : Blo 1232434 1388515 := bstep (se 1 (by rfl) ⟨1041386, by rfl⟩ : syracuseStep 1388515 = 2082773) B2082773
theorem B4165613 : Blo 1232434 4165613 := bstep (se 3 (by rfl) ⟨781052, by rfl⟩ : syracuseStep 4165613 = 1562105) B1562105
theorem B1232883 : Blo 1232434 1232883 := bstep (se 1 (by rfl) ⟨924662, by rfl⟩ : syracuseStep 1232883 = 1849325) B1849325
theorem B1232899 : Blo 1232434 1232899 := bstep (se 1 (by rfl) ⟨924674, by rfl⟩ : syracuseStep 1232899 = 1849349) B1849349
theorem B1232915 : Blo 1232434 1232915 := bstep (se 1 (by rfl) ⟨924686, by rfl⟩ : syracuseStep 1232915 = 1849373) B1849373
theorem B1232931 : Blo 1232434 1232931 := bstep (se 1 (by rfl) ⟨924698, by rfl⟩ : syracuseStep 1232931 = 1849397) B1849397
theorem B3559459 : Blo 1232434 3559459 := bstep (se 1 (by rfl) ⟨2669594, by rfl⟩ : syracuseStep 3559459 = 5339189) B5339189
theorem B4165667 : Blo 1232434 4165667 := bstep (se 1 (by rfl) ⟨3124250, by rfl⟩ : syracuseStep 4165667 = 6248501) B6248501
theorem B3510317 : Blo 1232434 3510317 := bstep (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) B1316369
theorem B1232947 : Blo 1232434 1232947 := bstep (se 1 (by rfl) ⟨924710, by rfl⟩ : syracuseStep 1232947 = 1849421) B1849421
theorem B1232963 : Blo 1232434 1232963 := bstep (se 1 (by rfl) ⟨924722, by rfl⟩ : syracuseStep 1232963 = 1849445) B1849445
theorem B1232979 : Blo 1232434 1232979 := bstep (se 1 (by rfl) ⟨924734, by rfl⟩ : syracuseStep 1232979 = 1849469) B1849469
theorem B1232995 : Blo 1232434 1232995 := bstep (se 1 (by rfl) ⟨924746, by rfl⟩ : syracuseStep 1232995 = 1849493) B1849493
theorem B1233011 : Blo 1232434 1233011 := bstep (se 1 (by rfl) ⟨924758, by rfl⟩ : syracuseStep 1233011 = 1849517) B1849517
theorem B1388659 : Blo 1232434 1388659 := bstep (se 1 (by rfl) ⟨1041494, by rfl⟩ : syracuseStep 1388659 = 2082989) B2082989
theorem B1233027 : Blo 1232434 1233027 := bstep (se 1 (by rfl) ⟨924770, by rfl⟩ : syracuseStep 1233027 = 1849541) B1849541
theorem B1233043 : Blo 1232434 1233043 := bstep (se 1 (by rfl) ⟨924782, by rfl⟩ : syracuseStep 1233043 = 1849565) B1849565
theorem B1233059 : Blo 1232434 1233059 := bstep (se 1 (by rfl) ⟨924794, by rfl⟩ : syracuseStep 1233059 = 1849589) B1849589
theorem B2773169 : Blo 1232434 2773169 := bstep (se 2 (by rfl) ⟨1039938, by rfl⟩ : syracuseStep 2773169 = 2079877) B2079877
theorem B1233075 : Blo 1232434 1233075 := bstep (se 1 (by rfl) ⟨924806, by rfl⟩ : syracuseStep 1233075 = 1849613) B1849613
theorem B2773187 : Blo 1232434 2773187 := bstep (se 1 (by rfl) ⟨2079890, by rfl⟩ : syracuseStep 2773187 = 4159781) B4159781
theorem B1233091 : Blo 1232434 1233091 := bstep (se 1 (by rfl) ⟨924818, by rfl⟩ : syracuseStep 1233091 = 1849637) B1849637
theorem B1233107 : Blo 1232434 1233107 := bstep (se 1 (by rfl) ⟨924830, by rfl⟩ : syracuseStep 1233107 = 1849661) B1849661
theorem B1233123 : Blo 1232434 1233123 := bstep (se 1 (by rfl) ⟨924842, by rfl⟩ : syracuseStep 1233123 = 1849685) B1849685
theorem B12669155 : Blo 1232434 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B1233139 : Blo 1232434 1233139 := bstep (se 1 (by rfl) ⟨924854, by rfl⟩ : syracuseStep 1233139 = 1849709) B1849709
theorem B1233155 : Blo 1232434 1233155 := bstep (se 1 (by rfl) ⟨924866, by rfl⟩ : syracuseStep 1233155 = 1849733) B1849733
theorem B1233171 : Blo 1232434 1233171 := bstep (se 1 (by rfl) ⟨924878, by rfl⟩ : syracuseStep 1233171 = 1849757) B1849757
theorem B1233187 : Blo 1232434 1233187 := bstep (se 1 (by rfl) ⟨924890, by rfl⟩ : syracuseStep 1233187 = 1849781) B1849781
theorem B3559715 : Blo 1232434 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B4682033 : Blo 1232434 4682033 := bstep (se 2 (by rfl) ⟨1755762, by rfl⟩ : syracuseStep 4682033 = 3511525) B3511525
theorem B1233203 : Blo 1232434 1233203 := bstep (se 1 (by rfl) ⟨924902, by rfl⟩ : syracuseStep 1233203 = 1849805) B1849805
theorem B4165937 : Blo 1232434 4165937 := bstep (se 2 (by rfl) ⟨1562226, by rfl⟩ : syracuseStep 4165937 = 3124453) B3124453
theorem B1233219 : Blo 1232434 1233219 := bstep (se 1 (by rfl) ⟨924914, by rfl⟩ : syracuseStep 1233219 = 1849829) B1849829
theorem B1233235 : Blo 1232434 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B1233251 : Blo 1232434 1233251 := bstep (se 1 (by rfl) ⟨924938, by rfl⟩ : syracuseStep 1233251 = 1849877) B1849877
theorem B1233267 : Blo 1232434 1233267 := bstep (se 1 (by rfl) ⟨924950, by rfl⟩ : syracuseStep 1233267 = 1849901) B1849901
theorem B1233283 : Blo 1232434 1233283 := bstep (se 1 (by rfl) ⟨924962, by rfl⟩ : syracuseStep 1233283 = 1849925) B1849925
theorem B1757585 : Blo 1232434 1757585 := bstep (se 2 (by rfl) ⟨659094, by rfl⟩ : syracuseStep 1757585 = 1318189) B1318189
theorem B1233299 : Blo 1232434 1233299 := bstep (se 1 (by rfl) ⟨924974, by rfl⟩ : syracuseStep 1233299 = 1849949) B1849949
theorem B1233315 : Blo 1232434 1233315 := bstep (se 1 (by rfl) ⟨924986, by rfl⟩ : syracuseStep 1233315 = 1849973) B1849973
theorem B1233331 : Blo 1232434 1233331 := bstep (se 1 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 1233331 = 1849997) B1849997
theorem B1233347 : Blo 1232434 1233347 := bstep (se 1 (by rfl) ⟨925010, by rfl⟩ : syracuseStep 1233347 = 1850021) B1850021
theorem B1561027 : Blo 1232434 1561027 := bstep (se 1 (by rfl) ⟨1170770, by rfl⟩ : syracuseStep 1561027 = 2341541) B2341541
theorem B2773457 : Blo 1232434 2773457 := bstep (se 2 (by rfl) ⟨1040046, by rfl⟩ : syracuseStep 2773457 = 2080093) B2080093
theorem B1233363 : Blo 1232434 1233363 := bstep (se 1 (by rfl) ⟨925022, by rfl⟩ : syracuseStep 1233363 = 1850045) B1850045
theorem B2773475 : Blo 1232434 2773475 := bstep (se 1 (by rfl) ⟨2080106, by rfl⟩ : syracuseStep 2773475 = 4160213) B4160213
theorem B1233379 : Blo 1232434 1233379 := bstep (se 1 (by rfl) ⟨925034, by rfl⟩ : syracuseStep 1233379 = 1850069) B1850069
theorem B1233395 : Blo 1232434 1233395 := bstep (se 1 (by rfl) ⟨925046, by rfl⟩ : syracuseStep 1233395 = 1850093) B1850093
theorem B1233411 : Blo 1232434 1233411 := bstep (se 1 (by rfl) ⟨925058, by rfl⟩ : syracuseStep 1233411 = 1850117) B1850117
theorem B1233427 : Blo 1232434 1233427 := bstep (se 1 (by rfl) ⟨925070, by rfl⟩ : syracuseStep 1233427 = 1850141) B1850141
theorem B1233443 : Blo 1232434 1233443 := bstep (se 1 (by rfl) ⟨925082, by rfl⟩ : syracuseStep 1233443 = 1850165) B1850165
theorem B1561123 : Blo 1232434 1561123 := bstep (se 1 (by rfl) ⟨1170842, by rfl⟩ : syracuseStep 1561123 = 2341685) B2341685
theorem B1233459 : Blo 1232434 1233459 := bstep (se 1 (by rfl) ⟨925094, by rfl⟩ : syracuseStep 1233459 = 1850189) B1850189
theorem B13333045 : Blo 1232434 13333045 := bstep (se 5 (by rfl) ⟨624986, by rfl⟩ : syracuseStep 13333045 = 1249973) B1249973
theorem B1233475 : Blo 1232434 1233475 := bstep (se 1 (by rfl) ⟨925106, by rfl⟩ : syracuseStep 1233475 = 1850213) B1850213
theorem B1233491 : Blo 1232434 1233491 := bstep (se 1 (by rfl) ⟨925118, by rfl⟩ : syracuseStep 1233491 = 1850237) B1850237
theorem B1233507 : Blo 1232434 1233507 := bstep (se 1 (by rfl) ⟨925130, by rfl⟩ : syracuseStep 1233507 = 1850261) B1850261
theorem B15807089 : Blo 1232434 15807089 := bstep (se 2 (by rfl) ⟨5927658, by rfl⟩ : syracuseStep 15807089 = 11855317) B11855317
theorem B1233523 : Blo 1232434 1233523 := bstep (se 1 (by rfl) ⟨925142, by rfl⟩ : syracuseStep 1233523 = 1850285) B1850285
theorem B1233539 : Blo 1232434 1233539 := bstep (se 1 (by rfl) ⟨925154, by rfl⟩ : syracuseStep 1233539 = 1850309) B1850309
theorem B1233555 : Blo 1232434 1233555 := bstep (se 1 (by rfl) ⟨925166, by rfl⟩ : syracuseStep 1233555 = 1850333) B1850333
theorem B1233571 : Blo 1232434 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B1233587 : Blo 1232434 1233587 := bstep (se 1 (by rfl) ⟨925190, by rfl⟩ : syracuseStep 1233587 = 1850381) B1850381
theorem B1233603 : Blo 1232434 1233603 := bstep (se 1 (by rfl) ⟨925202, by rfl⟩ : syracuseStep 1233603 = 1850405) B1850405
theorem B1233619 : Blo 1232434 1233619 := bstep (se 1 (by rfl) ⟨925214, by rfl⟩ : syracuseStep 1233619 = 1850429) B1850429
theorem B1233635 : Blo 1232434 1233635 := bstep (se 1 (by rfl) ⟨925226, by rfl⟩ : syracuseStep 1233635 = 1850453) B1850453
theorem B2773745 : Blo 1232434 2773745 := bstep (se 2 (by rfl) ⟨1040154, by rfl⟩ : syracuseStep 2773745 = 2080309) B2080309
theorem B2634481 : Blo 1232434 2634481 := bstep (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) B1975861
theorem B1233651 : Blo 1232434 1233651 := bstep (se 1 (by rfl) ⟨925238, by rfl⟩ : syracuseStep 1233651 = 1850477) B1850477
theorem B2773763 : Blo 1232434 2773763 := bstep (se 1 (by rfl) ⟨2080322, by rfl⟩ : syracuseStep 2773763 = 4160645) B4160645
theorem B1233667 : Blo 1232434 1233667 := bstep (se 1 (by rfl) ⟨925250, by rfl⟩ : syracuseStep 1233667 = 1850501) B1850501
theorem B1233683 : Blo 1232434 1233683 := bstep (se 1 (by rfl) ⟨925262, by rfl⟩ : syracuseStep 1233683 = 1850525) B1850525
theorem B1233699 : Blo 1232434 1233699 := bstep (se 1 (by rfl) ⟨925274, by rfl⟩ : syracuseStep 1233699 = 1850549) B1850549
theorem B1233715 : Blo 1232434 1233715 := bstep (se 1 (by rfl) ⟨925286, by rfl⟩ : syracuseStep 1233715 = 1850573) B1850573
theorem B1233731 : Blo 1232434 1233731 := bstep (se 1 (by rfl) ⟨925298, by rfl⟩ : syracuseStep 1233731 = 1850597) B1850597
theorem B1233747 : Blo 1232434 1233747 := bstep (se 1 (by rfl) ⟨925310, by rfl⟩ : syracuseStep 1233747 = 1850621) B1850621
theorem B1233763 : Blo 1232434 1233763 := bstep (se 1 (by rfl) ⟨925322, by rfl⟩ : syracuseStep 1233763 = 1850645) B1850645
theorem B1233779 : Blo 1232434 1233779 := bstep (se 1 (by rfl) ⟨925334, by rfl⟩ : syracuseStep 1233779 = 1850669) B1850669
theorem B1233795 : Blo 1232434 1233795 := bstep (se 1 (by rfl) ⟨925346, by rfl⟩ : syracuseStep 1233795 = 1850693) B1850693
theorem B1233811 : Blo 1232434 1233811 := bstep (se 1 (by rfl) ⟨925358, by rfl⟩ : syracuseStep 1233811 = 1850717) B1850717
theorem B1233827 : Blo 1232434 1233827 := bstep (se 1 (by rfl) ⟨925370, by rfl⟩ : syracuseStep 1233827 = 1850741) B1850741
theorem B1233843 : Blo 1232434 1233843 := bstep (se 1 (by rfl) ⟨925382, by rfl⟩ : syracuseStep 1233843 = 1850765) B1850765
theorem B2339779 : Blo 1232434 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B1233859 : Blo 1232434 1233859 := bstep (se 1 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 1233859 = 1850789) B1850789
theorem B1233875 : Blo 1232434 1233875 := bstep (se 1 (by rfl) ⟨925406, by rfl⟩ : syracuseStep 1233875 = 1850813) B1850813
theorem B1233891 : Blo 1232434 1233891 := bstep (se 1 (by rfl) ⟨925418, by rfl⟩ : syracuseStep 1233891 = 1850837) B1850837
theorem B1233907 : Blo 1232434 1233907 := bstep (se 1 (by rfl) ⟨925430, by rfl⟩ : syracuseStep 1233907 = 1850861) B1850861
theorem B1233923 : Blo 1232434 1233923 := bstep (se 1 (by rfl) ⟨925442, by rfl⟩ : syracuseStep 1233923 = 1850885) B1850885
theorem B3511309 : Blo 1232434 3511309 := bstep (se 3 (by rfl) ⟨658370, by rfl⟩ : syracuseStep 3511309 = 1316741) B1316741
theorem B2774033 : Blo 1232434 2774033 := bstep (se 2 (by rfl) ⟨1040262, by rfl⟩ : syracuseStep 2774033 = 2080525) B2080525
theorem B1561619 : Blo 1232434 1561619 := bstep (se 1 (by rfl) ⟨1171214, by rfl⟩ : syracuseStep 1561619 = 2342429) B2342429
theorem B1233939 : Blo 1232434 1233939 := bstep (se 1 (by rfl) ⟨925454, by rfl⟩ : syracuseStep 1233939 = 1850909) B1850909
theorem B6239267 : Blo 1232434 6239267 := bstep (se 1 (by rfl) ⟨4679450, by rfl⟩ : syracuseStep 6239267 = 9358901) B9358901
theorem B2774051 : Blo 1232434 2774051 := bstep (se 1 (by rfl) ⟨2080538, by rfl⟩ : syracuseStep 2774051 = 4161077) B4161077
theorem B1233955 : Blo 1232434 1233955 := bstep (se 1 (by rfl) ⟨925466, by rfl⟩ : syracuseStep 1233955 = 1850933) B1850933
theorem B1233971 : Blo 1232434 1233971 := bstep (se 1 (by rfl) ⟨925478, by rfl⟩ : syracuseStep 1233971 = 1850957) B1850957
theorem B1233987 : Blo 1232434 1233987 := bstep (se 1 (by rfl) ⟨925490, by rfl⟩ : syracuseStep 1233987 = 1850981) B1850981
theorem B1234003 : Blo 1232434 1234003 := bstep (se 1 (by rfl) ⟨925502, by rfl⟩ : syracuseStep 1234003 = 1851005) B1851005
theorem B1234019 : Blo 1232434 1234019 := bstep (se 1 (by rfl) ⟨925514, by rfl⟩ : syracuseStep 1234019 = 1851029) B1851029
theorem B1234035 : Blo 1232434 1234035 := bstep (se 1 (by rfl) ⟨925526, by rfl⟩ : syracuseStep 1234035 = 1851053) B1851053
theorem B1234051 : Blo 1232434 1234051 := bstep (se 1 (by rfl) ⟨925538, by rfl⟩ : syracuseStep 1234051 = 1851077) B1851077
theorem B1234067 : Blo 1232434 1234067 := bstep (se 1 (by rfl) ⟨925550, by rfl⟩ : syracuseStep 1234067 = 1851101) B1851101
theorem B1234083 : Blo 1232434 1234083 := bstep (se 1 (by rfl) ⟨925562, by rfl⟩ : syracuseStep 1234083 = 1851125) B1851125
theorem B1234099 : Blo 1232434 1234099 := bstep (se 1 (by rfl) ⟨925574, by rfl⟩ : syracuseStep 1234099 = 1851149) B1851149
theorem B1234115 : Blo 1232434 1234115 := bstep (se 1 (by rfl) ⟨925586, by rfl⟩ : syracuseStep 1234115 = 1851173) B1851173
theorem B9999557 : Blo 1232434 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B1234131 : Blo 1232434 1234131 := bstep (se 1 (by rfl) ⟨925598, by rfl⟩ : syracuseStep 1234131 = 1851197) B1851197
theorem B1234147 : Blo 1232434 1234147 := bstep (se 1 (by rfl) ⟨925610, by rfl⟩ : syracuseStep 1234147 = 1851221) B1851221
theorem B1234163 : Blo 1232434 1234163 := bstep (se 1 (by rfl) ⟨925622, by rfl⟩ : syracuseStep 1234163 = 1851245) B1851245
theorem B1234179 : Blo 1232434 1234179 := bstep (se 1 (by rfl) ⟨925634, by rfl⟩ : syracuseStep 1234179 = 1851269) B1851269
theorem B1234195 : Blo 1232434 1234195 := bstep (se 1 (by rfl) ⟨925646, by rfl⟩ : syracuseStep 1234195 = 1851293) B1851293
theorem B1234211 : Blo 1232434 1234211 := bstep (se 1 (by rfl) ⟨925658, by rfl⟩ : syracuseStep 1234211 = 1851317) B1851317
theorem B2774321 : Blo 1232434 2774321 := bstep (se 2 (by rfl) ⟨1040370, by rfl⟩ : syracuseStep 2774321 = 2080741) B2080741
theorem B1316147 : Blo 1232434 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B1234227 : Blo 1232434 1234227 := bstep (se 1 (by rfl) ⟨925670, by rfl⟩ : syracuseStep 1234227 = 1851341) B1851341
theorem B2774339 : Blo 1232434 2774339 := bstep (se 1 (by rfl) ⟨2080754, by rfl⟩ : syracuseStep 2774339 = 4161509) B4161509
theorem B1234243 : Blo 1232434 1234243 := bstep (se 1 (by rfl) ⟨925682, by rfl⟩ : syracuseStep 1234243 = 1851365) B1851365
theorem B1848659 : Blo 1232434 1848659 := bstep (se 1 (by rfl) ⟨1386494, by rfl⟩ : syracuseStep 1848659 = 2772989) B2772989
theorem B1234259 : Blo 1232434 1234259 := bstep (se 1 (by rfl) ⟨925694, by rfl⟩ : syracuseStep 1234259 = 1851389) B1851389
theorem B8893795 : Blo 1232434 8893795 := bstep (se 1 (by rfl) ⟨6670346, by rfl⟩ : syracuseStep 8893795 = 13340693) B13340693
theorem B1234275 : Blo 1232434 1234275 := bstep (se 1 (by rfl) ⟨925706, by rfl⟩ : syracuseStep 1234275 = 1851413) B1851413
theorem B1848689 : Blo 1232434 1848689 := bstep (se 2 (by rfl) ⟨693258, by rfl⟩ : syracuseStep 1848689 = 1386517) B1386517
theorem B1234291 : Blo 1232434 1234291 := bstep (se 1 (by rfl) ⟨925718, by rfl⟩ : syracuseStep 1234291 = 1851437) B1851437
theorem B1848707 : Blo 1232434 1848707 := bstep (se 1 (by rfl) ⟨1386530, by rfl⟩ : syracuseStep 1848707 = 2773061) B2773061
theorem B2340227 : Blo 1232434 2340227 := bstep (se 1 (by rfl) ⟨1755170, by rfl⟩ : syracuseStep 2340227 = 3510341) B3510341
theorem B1234307 : Blo 1232434 1234307 := bstep (se 1 (by rfl) ⟨925730, by rfl⟩ : syracuseStep 1234307 = 1851461) B1851461
theorem B1234323 : Blo 1232434 1234323 := bstep (se 1 (by rfl) ⟨925742, by rfl⟩ : syracuseStep 1234323 = 1851485) B1851485
theorem B1848737 : Blo 1232434 1848737 := bstep (se 2 (by rfl) ⟨693276, by rfl⟩ : syracuseStep 1848737 = 1386553) B1386553
theorem B1234339 : Blo 1232434 1234339 := bstep (se 1 (by rfl) ⟨925754, by rfl⟩ : syracuseStep 1234339 = 1851509) B1851509
theorem B4445617 : Blo 1232434 4445617 := bstep (se 2 (by rfl) ⟨1667106, by rfl⟩ : syracuseStep 4445617 = 3334213) B3334213
theorem B1848755 : Blo 1232434 1848755 := bstep (se 1 (by rfl) ⟨1386566, by rfl⟩ : syracuseStep 1848755 = 2773133) B2773133
theorem B1234355 : Blo 1232434 1234355 := bstep (se 1 (by rfl) ⟨925766, by rfl⟩ : syracuseStep 1234355 = 1851533) B1851533
theorem B1234371 : Blo 1232434 1234371 := bstep (se 1 (by rfl) ⟨925778, by rfl⟩ : syracuseStep 1234371 = 1851557) B1851557
theorem B1848785 : Blo 1232434 1848785 := bstep (se 2 (by rfl) ⟨693294, by rfl⟩ : syracuseStep 1848785 = 1386589) B1386589
theorem B1234387 : Blo 1232434 1234387 := bstep (se 1 (by rfl) ⟨925790, by rfl⟩ : syracuseStep 1234387 = 1851581) B1851581
theorem B1848803 : Blo 1232434 1848803 := bstep (se 1 (by rfl) ⟨1386602, by rfl⟩ : syracuseStep 1848803 = 2773205) B2773205
theorem B1234403 : Blo 1232434 1234403 := bstep (se 1 (by rfl) ⟨925802, by rfl⟩ : syracuseStep 1234403 = 1851605) B1851605
theorem B1234419 : Blo 1232434 1234419 := bstep (se 1 (by rfl) ⟨925814, by rfl⟩ : syracuseStep 1234419 = 1851629) B1851629
theorem B1848833 : Blo 1232434 1848833 := bstep (se 2 (by rfl) ⟨693312, by rfl⟩ : syracuseStep 1848833 = 1386625) B1386625
theorem B2635267 : Blo 1232434 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B2110979 : Blo 1232434 2110979 := bstep (se 1 (by rfl) ⟨1583234, by rfl⟩ : syracuseStep 2110979 = 3166469) B3166469
theorem B1848851 : Blo 1232434 1848851 := bstep (se 1 (by rfl) ⟨1386638, by rfl⟩ : syracuseStep 1848851 = 2773277) B2773277
theorem B1848881 : Blo 1232434 1848881 := bstep (se 2 (by rfl) ⟨693330, by rfl⟩ : syracuseStep 1848881 = 1386661) B1386661
theorem B3331651 : Blo 1232434 3331651 := bstep (se 1 (by rfl) ⟨2498738, by rfl⟩ : syracuseStep 3331651 = 4997477) B4997477
theorem B1848899 : Blo 1232434 1848899 := bstep (se 1 (by rfl) ⟨1386674, by rfl⟩ : syracuseStep 1848899 = 2773349) B2773349
theorem B2774609 : Blo 1232434 2774609 := bstep (se 2 (by rfl) ⟨1040478, by rfl⟩ : syracuseStep 2774609 = 2080957) B2080957
theorem B1848929 : Blo 1232434 1848929 := bstep (se 2 (by rfl) ⟨693348, by rfl⟩ : syracuseStep 1848929 = 1386697) B1386697
theorem B2774627 : Blo 1232434 2774627 := bstep (se 1 (by rfl) ⟨2080970, by rfl⟩ : syracuseStep 2774627 = 4161941) B4161941
theorem B1848947 : Blo 1232434 1848947 := bstep (se 1 (by rfl) ⟨1386710, by rfl⟩ : syracuseStep 1848947 = 2773421) B2773421
theorem B1848977 : Blo 1232434 1848977 := bstep (se 2 (by rfl) ⟨693366, by rfl⟩ : syracuseStep 1848977 = 1386733) B1386733
theorem B1848995 : Blo 1232434 1848995 := bstep (se 1 (by rfl) ⟨1386746, by rfl⟩ : syracuseStep 1848995 = 2773493) B2773493
theorem B2340515 : Blo 1232434 2340515 := bstep (se 1 (by rfl) ⟨1755386, by rfl⟩ : syracuseStep 2340515 = 3510773) B3510773
theorem B1849025 : Blo 1232434 1849025 := bstep (se 2 (by rfl) ⟨693384, by rfl⟩ : syracuseStep 1849025 = 1386769) B1386769
theorem B5265101 : Blo 1232434 5265101 := bstep (se 3 (by rfl) ⟨987206, by rfl⟩ : syracuseStep 5265101 = 1974413) B1974413
theorem B1849043 : Blo 1232434 1849043 := bstep (se 1 (by rfl) ⟨1386782, by rfl⟩ : syracuseStep 1849043 = 2773565) B2773565
theorem B1562323 : Blo 1232434 1562323 := bstep (se 1 (by rfl) ⟨1171742, by rfl⟩ : syracuseStep 1562323 = 2343485) B2343485
theorem B4683491 : Blo 1232434 4683491 := bstep (se 1 (by rfl) ⟨3512618, by rfl⟩ : syracuseStep 4683491 = 7025237) B7025237
theorem B1849073 : Blo 1232434 1849073 := bstep (se 2 (by rfl) ⟨693402, by rfl⟩ : syracuseStep 1849073 = 1386805) B1386805
theorem B6248177 : Blo 1232434 6248177 := bstep (se 2 (by rfl) ⟨2343066, by rfl⟩ : syracuseStep 6248177 = 4686133) B4686133
theorem B1849091 : Blo 1232434 1849091 := bstep (se 1 (by rfl) ⟨1386818, by rfl⟩ : syracuseStep 1849091 = 2773637) B2773637
theorem B1849121 : Blo 1232434 1849121 := bstep (se 2 (by rfl) ⟨693420, by rfl⟩ : syracuseStep 1849121 = 1386841) B1386841
theorem B1849139 : Blo 1232434 1849139 := bstep (se 1 (by rfl) ⟨1386854, by rfl⟩ : syracuseStep 1849139 = 2773709) B2773709
theorem B6240077 : Blo 1232434 6240077 := bstep (se 3 (by rfl) ⟨1170014, by rfl⟩ : syracuseStep 6240077 = 2340029) B2340029
theorem B1849169 : Blo 1232434 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B1849187 : Blo 1232434 1849187 := bstep (se 1 (by rfl) ⟨1386890, by rfl⟩ : syracuseStep 1849187 = 2773781) B2773781
theorem B3954541 : Blo 1232434 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B2774897 : Blo 1232434 2774897 := bstep (se 2 (by rfl) ⟨1040586, by rfl⟩ : syracuseStep 2774897 = 2081173) B2081173
theorem B1849217 : Blo 1232434 1849217 := bstep (se 2 (by rfl) ⟨693456, by rfl⟩ : syracuseStep 1849217 = 1386913) B1386913
theorem B2774915 : Blo 1232434 2774915 := bstep (se 1 (by rfl) ⟨2081186, by rfl⟩ : syracuseStep 2774915 = 4162373) B4162373
theorem B16013197 : Blo 1232434 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1849235 : Blo 1232434 1849235 := bstep (se 1 (by rfl) ⟨1386926, by rfl⟩ : syracuseStep 1849235 = 2773853) B2773853
theorem B1849265 : Blo 1232434 1849265 := bstep (se 2 (by rfl) ⟨693474, by rfl⟩ : syracuseStep 1849265 = 1386949) B1386949
theorem B1849283 : Blo 1232434 1849283 := bstep (se 1 (by rfl) ⟨1386962, by rfl⟩ : syracuseStep 1849283 = 2773925) B2773925
theorem B1849313 : Blo 1232434 1849313 := bstep (se 2 (by rfl) ⟨693492, by rfl⟩ : syracuseStep 1849313 = 1386985) B1386985
theorem B1849331 : Blo 1232434 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B1849361 : Blo 1232434 1849361 := bstep (se 2 (by rfl) ⟨693510, by rfl⟩ : syracuseStep 1849361 = 1387021) B1387021
theorem B1480723 : Blo 1232434 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B1849379 : Blo 1232434 1849379 := bstep (se 1 (by rfl) ⟨1387034, by rfl⟩ : syracuseStep 1849379 = 2774069) B2774069
theorem B1316899 : Blo 1232434 1316899 := bstep (se 1 (by rfl) ⟨987674, by rfl⟩ : syracuseStep 1316899 = 1975349) B1975349
theorem B3004465 : Blo 1232434 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1849409 : Blo 1232434 1849409 := bstep (se 2 (by rfl) ⟨693528, by rfl⟩ : syracuseStep 1849409 = 1387057) B1387057
theorem B4159565 : Blo 1232434 4159565 := bstep (se 3 (by rfl) ⟨779918, by rfl⟩ : syracuseStep 4159565 = 1559837) B1559837
theorem B1849427 : Blo 1232434 1849427 := bstep (se 1 (by rfl) ⟨1387070, by rfl⟩ : syracuseStep 1849427 = 2774141) B2774141
theorem B1849457 : Blo 1232434 1849457 := bstep (se 2 (by rfl) ⟨693546, by rfl⟩ : syracuseStep 1849457 = 1387093) B1387093
theorem B1874035 : Blo 1232434 1874035 := bstep (se 1 (by rfl) ⟨1405526, by rfl⟩ : syracuseStep 1874035 = 2811053) B2811053
theorem B4159619 : Blo 1232434 4159619 := bstep (se 1 (by rfl) ⟨3119714, by rfl⟩ : syracuseStep 4159619 = 6239429) B6239429
theorem B1849475 : Blo 1232434 1849475 := bstep (se 1 (by rfl) ⟨1387106, by rfl⟩ : syracuseStep 1849475 = 2774213) B2774213
theorem B2775185 : Blo 1232434 2775185 := bstep (se 2 (by rfl) ⟨1040694, by rfl⟩ : syracuseStep 2775185 = 2081389) B2081389
theorem B1849505 : Blo 1232434 1849505 := bstep (se 2 (by rfl) ⟨693564, by rfl⟩ : syracuseStep 1849505 = 1387129) B1387129
theorem B2775203 : Blo 1232434 2775203 := bstep (se 1 (by rfl) ⟨2081402, by rfl⟩ : syracuseStep 2775203 = 4162805) B4162805
theorem B2668721 : Blo 1232434 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B1849523 : Blo 1232434 1849523 := bstep (se 1 (by rfl) ⟨1387142, by rfl⟩ : syracuseStep 1849523 = 2774285) B2774285
theorem B1849553 : Blo 1232434 1849553 := bstep (se 2 (by rfl) ⟨693582, by rfl⟩ : syracuseStep 1849553 = 1387165) B1387165
theorem B2635985 : Blo 1232434 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B1603795 : Blo 1232434 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B1849571 : Blo 1232434 1849571 := bstep (se 1 (by rfl) ⟨1387178, by rfl⟩ : syracuseStep 1849571 = 2774357) B2774357
theorem B1849601 : Blo 1232434 1849601 := bstep (se 2 (by rfl) ⟨693600, by rfl⟩ : syracuseStep 1849601 = 1387201) B1387201
theorem B1849619 : Blo 1232434 1849619 := bstep (se 1 (by rfl) ⟨1387214, by rfl⟩ : syracuseStep 1849619 = 2774429) B2774429
theorem B1317155 : Blo 1232434 1317155 := bstep (se 1 (by rfl) ⟨987866, by rfl⟩ : syracuseStep 1317155 = 1975733) B1975733
theorem B1849649 : Blo 1232434 1849649 := bstep (se 2 (by rfl) ⟨693618, by rfl⟩ : syracuseStep 1849649 = 1387237) B1387237
theorem B1849667 : Blo 1232434 1849667 := bstep (se 1 (by rfl) ⟨1387250, by rfl⟩ : syracuseStep 1849667 = 2774501) B2774501
theorem B7027013 : Blo 1232434 7027013 := bstep (se 4 (by rfl) ⟨658782, by rfl⟩ : syracuseStep 7027013 = 1317565) B1317565
theorem B1849697 : Blo 1232434 1849697 := bstep (se 2 (by rfl) ⟨693636, by rfl⟩ : syracuseStep 1849697 = 1387273) B1387273
theorem B1849715 : Blo 1232434 1849715 := bstep (se 1 (by rfl) ⟨1387286, by rfl⟩ : syracuseStep 1849715 = 2774573) B2774573
theorem B4159889 : Blo 1232434 4159889 := bstep (se 2 (by rfl) ⟨1559958, by rfl⟩ : syracuseStep 4159889 = 3119917) B3119917
theorem B1849745 : Blo 1232434 1849745 := bstep (se 2 (by rfl) ⟨693654, by rfl⟩ : syracuseStep 1849745 = 1387309) B1387309
theorem B1849763 : Blo 1232434 1849763 := bstep (se 1 (by rfl) ⟨1387322, by rfl⟩ : syracuseStep 1849763 = 2774645) B2774645
theorem B2775473 : Blo 1232434 2775473 := bstep (se 2 (by rfl) ⟨1040802, by rfl⟩ : syracuseStep 2775473 = 2081605) B2081605
theorem B1849793 : Blo 1232434 1849793 := bstep (se 2 (by rfl) ⟨693672, by rfl⟩ : syracuseStep 1849793 = 1387345) B1387345
theorem B2775491 : Blo 1232434 2775491 := bstep (se 1 (by rfl) ⟨2081618, by rfl⟩ : syracuseStep 2775491 = 4163237) B4163237
theorem B1849811 : Blo 1232434 1849811 := bstep (se 1 (by rfl) ⟨1387358, by rfl⟩ : syracuseStep 1849811 = 2774717) B2774717
theorem B1849841 : Blo 1232434 1849841 := bstep (se 2 (by rfl) ⟨693690, by rfl⟩ : syracuseStep 1849841 = 1387381) B1387381
theorem B1849859 : Blo 1232434 1849859 := bstep (se 1 (by rfl) ⟨1387394, by rfl⟩ : syracuseStep 1849859 = 2774789) B2774789
theorem B1849889 : Blo 1232434 1849889 := bstep (se 2 (by rfl) ⟨693708, by rfl⟩ : syracuseStep 1849889 = 1387417) B1387417
theorem B1849907 : Blo 1232434 1849907 := bstep (se 1 (by rfl) ⟨1387430, by rfl⟩ : syracuseStep 1849907 = 2774861) B2774861
theorem B2251331 : Blo 1232434 2251331 := bstep (se 1 (by rfl) ⟨1688498, by rfl⟩ : syracuseStep 2251331 = 3376997) B3376997
theorem B15809093 : Blo 1232434 15809093 := bstep (se 4 (by rfl) ⟨1482102, by rfl⟩ : syracuseStep 15809093 = 2964205) B2964205
theorem B1849937 : Blo 1232434 1849937 := bstep (se 2 (by rfl) ⟨693726, by rfl⟩ : syracuseStep 1849937 = 1387453) B1387453
theorem B2341457 : Blo 1232434 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B1849955 : Blo 1232434 1849955 := bstep (se 1 (by rfl) ⟨1387466, by rfl⟩ : syracuseStep 1849955 = 2774933) B2774933
theorem B1849985 : Blo 1232434 1849985 := bstep (se 2 (by rfl) ⟨693744, by rfl⟩ : syracuseStep 1849985 = 1387489) B1387489
theorem B1850003 : Blo 1232434 1850003 := bstep (se 1 (by rfl) ⟨1387502, by rfl⟩ : syracuseStep 1850003 = 2775005) B2775005
theorem B1850033 : Blo 1232434 1850033 := bstep (se 2 (by rfl) ⟨693762, by rfl⟩ : syracuseStep 1850033 = 1387525) B1387525
theorem B1850051 : Blo 1232434 1850051 := bstep (se 1 (by rfl) ⟨1387538, by rfl⟩ : syracuseStep 1850051 = 2775077) B2775077
theorem B4684493 : Blo 1232434 4684493 := bstep (se 3 (by rfl) ⟨878342, by rfl⟩ : syracuseStep 4684493 = 1756685) B1756685
theorem B3513041 : Blo 1232434 3513041 := bstep (se 2 (by rfl) ⟨1317390, by rfl⟩ : syracuseStep 3513041 = 2634781) B2634781
theorem B2775761 : Blo 1232434 2775761 := bstep (se 2 (by rfl) ⟨1040910, by rfl⟩ : syracuseStep 2775761 = 2081821) B2081821
theorem B1850081 : Blo 1232434 1850081 := bstep (se 2 (by rfl) ⟨693780, by rfl⟩ : syracuseStep 1850081 = 1387561) B1387561
theorem B2775779 : Blo 1232434 2775779 := bstep (se 1 (by rfl) ⟨2081834, by rfl⟩ : syracuseStep 2775779 = 4163669) B4163669
theorem B3750637 : Blo 1232434 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B1850099 : Blo 1232434 1850099 := bstep (se 1 (by rfl) ⟨1387574, by rfl⟩ : syracuseStep 1850099 = 2775149) B2775149
theorem B7027469 : Blo 1232434 7027469 := bstep (se 3 (by rfl) ⟨1317650, by rfl⟩ : syracuseStep 7027469 = 2635301) B2635301
theorem B1850129 : Blo 1232434 1850129 := bstep (se 2 (by rfl) ⟨693798, by rfl⟩ : syracuseStep 1850129 = 1387597) B1387597
theorem B1850147 : Blo 1232434 1850147 := bstep (se 1 (by rfl) ⟨1387610, by rfl⟩ : syracuseStep 1850147 = 2775221) B2775221
theorem B1850177 : Blo 1232434 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B1850195 : Blo 1232434 1850195 := bstep (se 1 (by rfl) ⟨1387646, by rfl⟩ : syracuseStep 1850195 = 2775293) B2775293
theorem B1850225 : Blo 1232434 1850225 := bstep (se 2 (by rfl) ⟨693834, by rfl⟩ : syracuseStep 1850225 = 1387669) B1387669
theorem B1850243 : Blo 1232434 1850243 := bstep (se 1 (by rfl) ⟨1387682, by rfl⟩ : syracuseStep 1850243 = 2775365) B2775365
theorem B7019405 : Blo 1232434 7019405 := bstep (se 3 (by rfl) ⟨1316138, by rfl⟩ : syracuseStep 7019405 = 2632277) B2632277
theorem B5004173 : Blo 1232434 5004173 := bstep (se 3 (by rfl) ⟨938282, by rfl⟩ : syracuseStep 5004173 = 1876565) B1876565
theorem B3513233 : Blo 1232434 3513233 := bstep (se 2 (by rfl) ⟨1317462, by rfl⟩ : syracuseStep 3513233 = 2634925) B2634925
theorem B1850273 : Blo 1232434 1850273 := bstep (se 2 (by rfl) ⟨693852, by rfl⟩ : syracuseStep 1850273 = 1387705) B1387705
theorem B4160429 : Blo 1232434 4160429 := bstep (se 3 (by rfl) ⟨780080, by rfl⟩ : syracuseStep 4160429 = 1560161) B1560161
theorem B1850291 : Blo 1232434 1850291 := bstep (se 1 (by rfl) ⟨1387718, by rfl⟩ : syracuseStep 1850291 = 2775437) B2775437
theorem B9370565 : Blo 1232434 9370565 := bstep (se 4 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 9370565 = 1756981) B1756981
theorem B1850321 : Blo 1232434 1850321 := bstep (se 2 (by rfl) ⟨693870, by rfl⟩ : syracuseStep 1850321 = 1387741) B1387741
theorem B4160483 : Blo 1232434 4160483 := bstep (se 1 (by rfl) ⟨3120362, by rfl⟩ : syracuseStep 4160483 = 6240725) B6240725
theorem B1850339 : Blo 1232434 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B5266417 : Blo 1232434 5266417 := bstep (se 2 (by rfl) ⟨1974906, by rfl⟩ : syracuseStep 5266417 = 3949813) B3949813
theorem B2776049 : Blo 1232434 2776049 := bstep (se 2 (by rfl) ⟨1041018, by rfl⟩ : syracuseStep 2776049 = 2082037) B2082037
theorem B1850369 : Blo 1232434 1850369 := bstep (se 2 (by rfl) ⟨693888, by rfl⟩ : syracuseStep 1850369 = 1387777) B1387777
theorem B2776067 : Blo 1232434 2776067 := bstep (se 1 (by rfl) ⟨2082050, by rfl⟩ : syracuseStep 2776067 = 4164101) B4164101
theorem B1334291 : Blo 1232434 1334291 := bstep (se 1 (by rfl) ⟨1000718, by rfl⟩ : syracuseStep 1334291 = 2001437) B2001437
theorem B1850387 : Blo 1232434 1850387 := bstep (se 1 (by rfl) ⟨1387790, by rfl⟩ : syracuseStep 1850387 = 2775581) B2775581
theorem B1317907 : Blo 1232434 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B5069873 : Blo 1232434 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1850417 : Blo 1232434 1850417 := bstep (se 2 (by rfl) ⟨693906, by rfl⟩ : syracuseStep 1850417 = 1387813) B1387813
theorem B1850435 : Blo 1232434 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B1850465 : Blo 1232434 1850465 := bstep (se 2 (by rfl) ⟨693924, by rfl⟩ : syracuseStep 1850465 = 1387849) B1387849
theorem B2079857 : Blo 1232434 2079857 := bstep (se 2 (by rfl) ⟨779946, by rfl⟩ : syracuseStep 2079857 = 1559893) B1559893
theorem B3120241 : Blo 1232434 3120241 := bstep (se 2 (by rfl) ⟨1170090, by rfl⟩ : syracuseStep 3120241 = 2340181) B2340181
theorem B1850483 : Blo 1232434 1850483 := bstep (se 1 (by rfl) ⟨1387862, by rfl⟩ : syracuseStep 1850483 = 2775725) B2775725
theorem B1850513 : Blo 1232434 1850513 := bstep (se 2 (by rfl) ⟨693942, by rfl⟩ : syracuseStep 1850513 = 1387885) B1387885
theorem B1850531 : Blo 1232434 1850531 := bstep (se 1 (by rfl) ⟨1387898, by rfl⟩ : syracuseStep 1850531 = 2775797) B2775797
theorem B1850561 : Blo 1232434 1850561 := bstep (se 2 (by rfl) ⟨693960, by rfl⟩ : syracuseStep 1850561 = 1387921) B1387921
theorem B1850579 : Blo 1232434 1850579 := bstep (se 1 (by rfl) ⟨1387934, by rfl⟩ : syracuseStep 1850579 = 2775869) B2775869
theorem B2079985 : Blo 1232434 2079985 := bstep (se 2 (by rfl) ⟨779994, by rfl⟩ : syracuseStep 2079985 = 1559989) B1559989
theorem B4160753 : Blo 1232434 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B1850609 : Blo 1232434 1850609 := bstep (se 2 (by rfl) ⟨693978, by rfl⟩ : syracuseStep 1850609 = 1387957) B1387957
theorem B1850627 : Blo 1232434 1850627 := bstep (se 1 (by rfl) ⟨1387970, by rfl⟩ : syracuseStep 1850627 = 2775941) B2775941
theorem B2776337 : Blo 1232434 2776337 := bstep (se 2 (by rfl) ⟨1041126, by rfl⟩ : syracuseStep 2776337 = 2082253) B2082253
theorem B2080019 : Blo 1232434 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B1850657 : Blo 1232434 1850657 := bstep (se 2 (by rfl) ⟨693996, by rfl⟩ : syracuseStep 1850657 = 1387993) B1387993
theorem B2776355 : Blo 1232434 2776355 := bstep (se 1 (by rfl) ⟨2082266, by rfl⟩ : syracuseStep 2776355 = 4164533) B4164533
theorem B1850675 : Blo 1232434 1850675 := bstep (se 1 (by rfl) ⟨1388006, by rfl⟩ : syracuseStep 1850675 = 2776013) B2776013
theorem B1850705 : Blo 1232434 1850705 := bstep (se 2 (by rfl) ⟨694014, by rfl⟩ : syracuseStep 1850705 = 1388029) B1388029
theorem B1850723 : Blo 1232434 1850723 := bstep (se 1 (by rfl) ⟨1388042, by rfl⟩ : syracuseStep 1850723 = 2776085) B2776085
theorem B1850753 : Blo 1232434 1850753 := bstep (se 2 (by rfl) ⟨694032, by rfl⟩ : syracuseStep 1850753 = 1388065) B1388065
theorem B3120515 : Blo 1232434 3120515 := bstep (se 1 (by rfl) ⟨2340386, by rfl⟩ : syracuseStep 3120515 = 4680773) B4680773
theorem B2080147 : Blo 1232434 2080147 := bstep (se 1 (by rfl) ⟨1560110, by rfl⟩ : syracuseStep 2080147 = 3120221) B3120221
theorem B1850771 : Blo 1232434 1850771 := bstep (se 1 (by rfl) ⟨1388078, by rfl⟩ : syracuseStep 1850771 = 2776157) B2776157
theorem B1850801 : Blo 1232434 1850801 := bstep (se 2 (by rfl) ⟨694050, by rfl⟩ : syracuseStep 1850801 = 1388101) B1388101
theorem B1850819 : Blo 1232434 1850819 := bstep (se 1 (by rfl) ⟨1388114, by rfl⟩ : syracuseStep 1850819 = 2776229) B2776229
theorem B2342353 : Blo 1232434 2342353 := bstep (se 2 (by rfl) ⟨878382, by rfl⟩ : syracuseStep 2342353 = 1756765) B1756765
theorem B1850849 : Blo 1232434 1850849 := bstep (se 2 (by rfl) ⟨694068, by rfl⟩ : syracuseStep 1850849 = 1388137) B1388137
theorem B1850867 : Blo 1232434 1850867 := bstep (se 1 (by rfl) ⟨1388150, by rfl⟩ : syracuseStep 1850867 = 2776301) B2776301
theorem B1850897 : Blo 1232434 1850897 := bstep (se 2 (by rfl) ⟨694086, by rfl⟩ : syracuseStep 1850897 = 1388173) B1388173
theorem B2080289 : Blo 1232434 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B1850915 : Blo 1232434 1850915 := bstep (se 1 (by rfl) ⟨1388186, by rfl⟩ : syracuseStep 1850915 = 2776373) B2776373
theorem B2776625 : Blo 1232434 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B1850945 : Blo 1232434 1850945 := bstep (se 2 (by rfl) ⟨694104, by rfl⟩ : syracuseStep 1850945 = 1388209) B1388209
theorem B3120707 : Blo 1232434 3120707 := bstep (se 1 (by rfl) ⟨2340530, by rfl⟩ : syracuseStep 3120707 = 4681061) B4681061
theorem B2776643 : Blo 1232434 2776643 := bstep (se 1 (by rfl) ⟨2082482, by rfl⟩ : syracuseStep 2776643 = 4164965) B4164965
theorem B1850963 : Blo 1232434 1850963 := bstep (se 1 (by rfl) ⟨1388222, by rfl⟩ : syracuseStep 1850963 = 2776445) B2776445
theorem B2342513 : Blo 1232434 2342513 := bstep (se 2 (by rfl) ⟨878442, by rfl⟩ : syracuseStep 2342513 = 1756885) B1756885
theorem B1850993 : Blo 1232434 1850993 := bstep (se 2 (by rfl) ⟨694122, by rfl⟩ : syracuseStep 1850993 = 1388245) B1388245
theorem B1851011 : Blo 1232434 1851011 := bstep (se 1 (by rfl) ⟨1388258, by rfl⟩ : syracuseStep 1851011 = 2776517) B2776517
theorem B2080417 : Blo 1232434 2080417 := bstep (se 2 (by rfl) ⟨780156, by rfl⟩ : syracuseStep 2080417 = 1560313) B1560313
theorem B1851041 : Blo 1232434 1851041 := bstep (se 2 (by rfl) ⟨694140, by rfl⟩ : syracuseStep 1851041 = 1388281) B1388281
theorem B1851059 : Blo 1232434 1851059 := bstep (se 1 (by rfl) ⟨1388294, by rfl⟩ : syracuseStep 1851059 = 2776589) B2776589
theorem B2080451 : Blo 1232434 2080451 := bstep (se 1 (by rfl) ⟨1560338, by rfl⟩ : syracuseStep 2080451 = 3120677) B3120677
theorem B1851089 : Blo 1232434 1851089 := bstep (se 2 (by rfl) ⟨694158, by rfl⟩ : syracuseStep 1851089 = 1388317) B1388317
theorem B1851107 : Blo 1232434 1851107 := bstep (se 1 (by rfl) ⟨1388330, by rfl⟩ : syracuseStep 1851107 = 2776661) B2776661
theorem B1851137 : Blo 1232434 1851137 := bstep (se 2 (by rfl) ⟨694176, by rfl⟩ : syracuseStep 1851137 = 1388353) B1388353
theorem B4161293 : Blo 1232434 4161293 := bstep (se 3 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 4161293 = 1560485) B1560485
theorem B1851155 : Blo 1232434 1851155 := bstep (se 1 (by rfl) ⟨1388366, by rfl⟩ : syracuseStep 1851155 = 2776733) B2776733
theorem B6668081 : Blo 1232434 6668081 := bstep (se 2 (by rfl) ⟨2500530, by rfl⟩ : syracuseStep 6668081 = 5001061) B5001061
theorem B1851185 : Blo 1232434 1851185 := bstep (se 2 (by rfl) ⟨694194, by rfl⟩ : syracuseStep 1851185 = 1388389) B1388389
theorem B2080579 : Blo 1232434 2080579 := bstep (se 1 (by rfl) ⟨1560434, by rfl⟩ : syracuseStep 2080579 = 3120869) B3120869
theorem B4161347 : Blo 1232434 4161347 := bstep (se 1 (by rfl) ⟨3121010, by rfl⟩ : syracuseStep 4161347 = 6242021) B6242021
theorem B1851203 : Blo 1232434 1851203 := bstep (se 1 (by rfl) ⟨1388402, by rfl⟩ : syracuseStep 1851203 = 2776805) B2776805
theorem B1875793 : Blo 1232434 1875793 := bstep (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) B1406845
theorem B2776913 : Blo 1232434 2776913 := bstep (se 2 (by rfl) ⟨1041342, by rfl⟩ : syracuseStep 2776913 = 2082685) B2082685
theorem B1851233 : Blo 1232434 1851233 := bstep (se 2 (by rfl) ⟨694212, by rfl⟩ : syracuseStep 1851233 = 1388425) B1388425
theorem B2776931 : Blo 1232434 2776931 := bstep (se 1 (by rfl) ⟨2082698, by rfl⟩ : syracuseStep 2776931 = 4165397) B4165397
theorem B3514225 : Blo 1232434 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B1851251 : Blo 1232434 1851251 := bstep (se 1 (by rfl) ⟨1388438, by rfl⟩ : syracuseStep 1851251 = 2776877) B2776877
theorem B1851281 : Blo 1232434 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1851299 : Blo 1232434 1851299 := bstep (se 1 (by rfl) ⟨1388474, by rfl⟩ : syracuseStep 1851299 = 2776949) B2776949
theorem B1851329 : Blo 1232434 1851329 := bstep (se 2 (by rfl) ⟨694248, by rfl⟩ : syracuseStep 1851329 = 1388497) B1388497
theorem B2080721 : Blo 1232434 2080721 := bstep (se 2 (by rfl) ⟨780270, by rfl⟩ : syracuseStep 2080721 = 1560541) B1560541
theorem B1851347 : Blo 1232434 1851347 := bstep (se 1 (by rfl) ⟨1388510, by rfl⟩ : syracuseStep 1851347 = 2777021) B2777021
theorem B1851377 : Blo 1232434 1851377 := bstep (se 2 (by rfl) ⟨694266, by rfl⟩ : syracuseStep 1851377 = 1388533) B1388533
theorem B2777111 : Blo 1232434 2777111 := bstep (se 1 (by rfl) ⟨2082833, by rfl⟩ : syracuseStep 2777111 = 4165667) B4165667
theorem B4005953 : Blo 1232434 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B5931083 : Blo 1232434 5931083 := bstep (se 1 (by rfl) ⟨4448312, by rfl⟩ : syracuseStep 5931083 = 8896625) B8896625
theorem B1851467 : Blo 1232434 1851467 := bstep (se 1 (by rfl) ⟨1388600, by rfl⟩ : syracuseStep 1851467 = 2777201) B2777201
theorem B2342999 : Blo 1232434 2342999 := bstep (se 1 (by rfl) ⟨1757249, by rfl⟩ : syracuseStep 2342999 = 3514499) B3514499
theorem B1851479 : Blo 1232434 1851479 := bstep (se 1 (by rfl) ⟨1388609, by rfl⟩ : syracuseStep 1851479 = 2777219) B2777219
theorem B7897189 : Blo 1232434 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B8446103 : Blo 1232434 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B1851545 : Blo 1232434 1851545 := bstep (se 2 (by rfl) ⟨694329, by rfl⟩ : syracuseStep 1851545 = 1388659) B1388659
theorem B3121355 : Blo 1232434 3121355 := bstep (se 1 (by rfl) ⟨2341016, by rfl⟩ : syracuseStep 3121355 = 4682033) B4682033
theorem B2777291 : Blo 1232434 2777291 := bstep (se 1 (by rfl) ⟨2082968, by rfl⟩ : syracuseStep 2777291 = 4165937) B4165937
theorem B2777345 : Blo 1232434 2777345 := bstep (se 2 (by rfl) ⟨1041504, by rfl⟩ : syracuseStep 2777345 = 2083009) B2083009
theorem B2138393 : Blo 1232434 2138393 := bstep (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) B1603795
theorem B3948851 : Blo 1232434 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B2081099 : Blo 1232434 2081099 := bstep (se 1 (by rfl) ⟨1560824, by rfl⟩ : syracuseStep 2081099 = 3121649) B3121649
theorem B4161995 : Blo 1232434 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B2081227 : Blo 1232434 2081227 := bstep (se 1 (by rfl) ⟨1560920, by rfl⟩ : syracuseStep 2081227 = 3121841) B3121841
theorem B23708173 : Blo 1232434 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B2081369 : Blo 1232434 2081369 := bstep (se 2 (by rfl) ⟨780513, by rfl⟩ : syracuseStep 2081369 = 1561027) B1561027
theorem B9994853 : Blo 1232434 9994853 := bstep (se 4 (by rfl) ⟨937017, by rfl⟩ : syracuseStep 9994853 = 1874035) B1874035
theorem B4162265 : Blo 1232434 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B2081497 : Blo 1232434 2081497 := bstep (se 2 (by rfl) ⟨780561, by rfl⟩ : syracuseStep 2081497 = 1561123) B1561123
theorem B5931737 : Blo 1232434 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B17777393 : Blo 1232434 17777393 := bstep (se 2 (by rfl) ⟨6666522, by rfl⟩ : syracuseStep 17777393 = 13333045) B13333045
theorem B4997963 : Blo 1232434 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B9372509 : Blo 1232434 9372509 := bstep (se 3 (by rfl) ⟨1757345, by rfl⟩ : syracuseStep 9372509 = 3514691) B3514691
theorem B15000497 : Blo 1232434 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B4686893 : Blo 1232434 4686893 := bstep (se 3 (by rfl) ⟨878792, by rfl⟩ : syracuseStep 4686893 = 1757585) B1757585
theorem B4686923 : Blo 1232434 4686923 := bstep (se 1 (by rfl) ⟨3515192, by rfl⟩ : syracuseStep 4686923 = 7030385) B7030385
theorem B6243479 : Blo 1232434 6243479 := bstep (se 1 (by rfl) ⟨4682609, by rfl⟩ : syracuseStep 6243479 = 9365219) B9365219
theorem B3122327 : Blo 1232434 3122327 := bstep (se 1 (by rfl) ⟨2341745, by rfl⟩ : syracuseStep 3122327 = 4683491) B4683491
theorem B2671795 : Blo 1232434 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B2082071 : Blo 1232434 2082071 := bstep (se 1 (by rfl) ⟨1561553, by rfl⟩ : syracuseStep 2082071 = 3123107) B3123107
theorem B7021889 : Blo 1232434 7021889 := bstep (se 2 (by rfl) ⟨2633208, by rfl⟩ : syracuseStep 7021889 = 5266417) B5266417
theorem B2852171 : Blo 1232434 2852171 := bstep (se 1 (by rfl) ⟨2139128, by rfl⟩ : syracuseStep 2852171 = 4278257) B4278257
theorem B5629277 : Blo 1232434 5629277 := bstep (se 3 (by rfl) ⟨1055489, by rfl⟩ : syracuseStep 5629277 = 2110979) B2110979
theorem B4162967 : Blo 1232434 4162967 := bstep (se 1 (by rfl) ⟨3122225, by rfl⟩ : syracuseStep 4162967 = 6244451) B6244451
theorem B2082199 : Blo 1232434 2082199 := bstep (se 1 (by rfl) ⟨1561649, by rfl⟩ : syracuseStep 2082199 = 3123299) B3123299
theorem B1500887 : Blo 1232434 1500887 := bstep (se 1 (by rfl) ⟨1125665, by rfl⟩ : syracuseStep 1500887 = 2251331) B2251331
theorem B3122995 : Blo 1232434 3122995 := bstep (se 1 (by rfl) ⟨2342246, by rfl⟩ : syracuseStep 3122995 = 4684493) B4684493
theorem B16869221 : Blo 1232434 16869221 := bstep (se 4 (by rfl) ⟨1581489, by rfl⟩ : syracuseStep 16869221 = 3162979) B3162979
theorem B4679603 : Blo 1232434 4679603 := bstep (se 1 (by rfl) ⟨3509702, by rfl⟩ : syracuseStep 4679603 = 7019405) B7019405
theorem B4163507 : Blo 1232434 4163507 := bstep (se 1 (by rfl) ⟨3122630, by rfl⟩ : syracuseStep 4163507 = 6245261) B6245261
theorem B3336115 : Blo 1232434 3336115 := bstep (se 1 (by rfl) ⟨2502086, by rfl⟩ : syracuseStep 3336115 = 5004173) B5004173
theorem B3123137 : Blo 1232434 3123137 := bstep (se 2 (by rfl) ⟨1171176, by rfl⟩ : syracuseStep 3123137 = 2342353) B2342353
theorem B2082827 : Blo 1232434 2082827 := bstep (se 1 (by rfl) ⟨1562120, by rfl⟩ : syracuseStep 2082827 = 3124241) B3124241
theorem B85403717 : Blo 1232434 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B1386571 : Blo 1232434 1386571 := bstep (se 1 (by rfl) ⟨1039928, by rfl⟩ : syracuseStep 1386571 = 2079857) B2079857
theorem B4442201 : Blo 1232434 4442201 := bstep (se 2 (by rfl) ⟨1665825, by rfl⟩ : syracuseStep 4442201 = 3331651) B3331651
theorem B8677469 : Blo 1232434 8677469 := bstep (se 3 (by rfl) ⟨1627025, by rfl⟩ : syracuseStep 8677469 = 3254051) B3254051
theorem B2082955 : Blo 1232434 2082955 := bstep (se 1 (by rfl) ⟨1562216, by rfl⟩ : syracuseStep 2082955 = 3124433) B3124433
theorem B4442285 : Blo 1232434 4442285 := bstep (se 3 (by rfl) ⟨832928, by rfl⟩ : syracuseStep 4442285 = 1665857) B1665857
theorem B1386679 : Blo 1232434 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B4163777 : Blo 1232434 4163777 := bstep (se 2 (by rfl) ⟨1561416, by rfl⟩ : syracuseStep 4163777 = 3122833) B3122833
theorem B3336385 : Blo 1232434 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B2812121 : Blo 1232434 2812121 := bstep (se 2 (by rfl) ⟨1054545, by rfl⟩ : syracuseStep 2812121 = 2109091) B2109091
theorem B4507907 : Blo 1232434 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B2083097 : Blo 1232434 2083097 := bstep (se 2 (by rfl) ⟨781161, by rfl⟩ : syracuseStep 2083097 = 1562323) B1562323
theorem B1386859 : Blo 1232434 1386859 := bstep (se 1 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 1386859 = 2080289) B2080289
theorem B2501057 : Blo 1232434 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B1386967 : Blo 1232434 1386967 := bstep (se 1 (by rfl) ⟨1040225, by rfl⟩ : syracuseStep 1386967 = 2080451) B2080451
theorem B1387147 : Blo 1232434 1387147 := bstep (se 1 (by rfl) ⟨1040360, by rfl⟩ : syracuseStep 1387147 = 2080721) B2080721
theorem B2001559 : Blo 1232434 2001559 := bstep (se 1 (by rfl) ⟨1501169, by rfl⟩ : syracuseStep 2001559 = 3002339) B3002339
theorem B13519511 : Blo 1232434 13519511 := bstep (se 1 (by rfl) ⟨10139633, by rfl⟩ : syracuseStep 13519511 = 20279267) B20279267
theorem B4745945 : Blo 1232434 4745945 := bstep (se 2 (by rfl) ⟨1779729, by rfl⟩ : syracuseStep 4745945 = 3559459) B3559459
theorem B1755865 : Blo 1232434 1755865 := bstep (se 2 (by rfl) ⟨658449, by rfl⟩ : syracuseStep 1755865 = 1316899) B1316899
theorem B3558109 : Blo 1232434 3558109 := bstep (se 3 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 3558109 = 1334291) B1334291
theorem B4164317 : Blo 1232434 4164317 := bstep (se 3 (by rfl) ⟨780809, by rfl⟩ : syracuseStep 4164317 = 1561619) B1561619
theorem B1387255 : Blo 1232434 1387255 := bstep (se 1 (by rfl) ⟨1040441, by rfl⟩ : syracuseStep 1387255 = 2080883) B2080883
theorem B4746115 : Blo 1232434 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B1665943 : Blo 1232434 1665943 := bstep (se 1 (by rfl) ⟨1249457, by rfl⟩ : syracuseStep 1665943 = 2498915) B2498915
theorem B1387435 : Blo 1232434 1387435 := bstep (se 1 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 1387435 = 2081153) B2081153
theorem B7908313 : Blo 1232434 7908313 := bstep (se 2 (by rfl) ⟨2965617, by rfl⟩ : syracuseStep 7908313 = 5931235) B5931235
theorem B57740309 : Blo 1232434 57740309 := bstep (se 6 (by rfl) ⟨1353288, by rfl⟩ : syracuseStep 57740309 = 2706577) B2706577
theorem B1387543 : Blo 1232434 1387543 := bstep (se 1 (by rfl) ⟨1040657, by rfl⟩ : syracuseStep 1387543 = 2081315) B2081315
theorem B10538059 : Blo 1232434 10538059 := bstep (se 1 (by rfl) ⟨7903544, by rfl⟩ : syracuseStep 10538059 = 15807089) B15807089
theorem B3124403 : Blo 1232434 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B1387723 : Blo 1232434 1387723 := bstep (se 1 (by rfl) ⟨1040792, by rfl⟩ : syracuseStep 1387723 = 2081585) B2081585
theorem B2813143 : Blo 1232434 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B2632961 : Blo 1232434 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B5270807 : Blo 1232434 5270807 := bstep (se 1 (by rfl) ⟨3953105, by rfl⟩ : syracuseStep 5270807 = 7906211) B7906211
theorem B1387831 : Blo 1232434 1387831 := bstep (se 1 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 1387831 = 2081747) B2081747
theorem B10538333 : Blo 1232434 10538333 := bstep (se 3 (by rfl) ⟨1975937, by rfl⟩ : syracuseStep 10538333 = 3951875) B3951875
theorem B4681091 : Blo 1232434 4681091 := bstep (se 1 (by rfl) ⟨3510818, by rfl⟩ : syracuseStep 4681091 = 7021637) B7021637
theorem B3509725 : Blo 1232434 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B1388011 : Blo 1232434 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B1232439 : Blo 1232434 1232439 := bstep (se 1 (by rfl) ⟨924329, by rfl⟩ : syracuseStep 1232439 = 1848659) B1848659
theorem B1232459 : Blo 1232434 1232459 := bstep (se 1 (by rfl) ⟨924344, by rfl⟩ : syracuseStep 1232459 = 1848689) B1848689
theorem B13332043 : Blo 1232434 13332043 := bstep (se 1 (by rfl) ⟨9999032, by rfl⟩ : syracuseStep 13332043 = 19998065) B19998065
theorem B5271115 : Blo 1232434 5271115 := bstep (se 1 (by rfl) ⟨3953336, by rfl⟩ : syracuseStep 5271115 = 7906673) B7906673
theorem B1232471 : Blo 1232434 1232471 := bstep (se 1 (by rfl) ⟨924353, by rfl⟩ : syracuseStep 1232471 = 1848707) B1848707
theorem B1560151 : Blo 1232434 1560151 := bstep (se 1 (by rfl) ⟨1170113, by rfl⟩ : syracuseStep 1560151 = 2340227) B2340227
theorem B2633303 : Blo 1232434 2633303 := bstep (se 1 (by rfl) ⟨1974977, by rfl⟩ : syracuseStep 2633303 = 3949955) B3949955
theorem B1388119 : Blo 1232434 1388119 := bstep (se 1 (by rfl) ⟨1041089, by rfl⟩ : syracuseStep 1388119 = 2082179) B2082179
theorem B1232491 : Blo 1232434 1232491 := bstep (se 1 (by rfl) ⟨924368, by rfl⟩ : syracuseStep 1232491 = 1848737) B1848737
theorem B2223731 : Blo 1232434 2223731 := bstep (se 1 (by rfl) ⟨1667798, by rfl⟩ : syracuseStep 2223731 = 3335597) B3335597
theorem B1232503 : Blo 1232434 1232503 := bstep (se 1 (by rfl) ⟨924377, by rfl⟩ : syracuseStep 1232503 = 1848755) B1848755
theorem B1232523 : Blo 1232434 1232523 := bstep (se 1 (by rfl) ⟨924392, by rfl⟩ : syracuseStep 1232523 = 1848785) B1848785
theorem B2813579 : Blo 1232434 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B5000849 : Blo 1232434 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B1232535 : Blo 1232434 1232535 := bstep (se 1 (by rfl) ⟨924401, by rfl⟩ : syracuseStep 1232535 = 1848803) B1848803
theorem B7024279 : Blo 1232434 7024279 := bstep (se 1 (by rfl) ⟨5268209, by rfl⟩ : syracuseStep 7024279 = 10536419) B10536419
theorem B2223767 : Blo 1232434 2223767 := bstep (se 1 (by rfl) ⟨1667825, by rfl⟩ : syracuseStep 2223767 = 3335651) B3335651
theorem B1232555 : Blo 1232434 1232555 := bstep (se 1 (by rfl) ⟨924416, by rfl⟩ : syracuseStep 1232555 = 1848833) B1848833
theorem B1232567 : Blo 1232434 1232567 := bstep (se 1 (by rfl) ⟨924425, by rfl⟩ : syracuseStep 1232567 = 1848851) B1848851
theorem B1232587 : Blo 1232434 1232587 := bstep (se 1 (by rfl) ⟨924440, by rfl⟩ : syracuseStep 1232587 = 1848881) B1848881
theorem B1232599 : Blo 1232434 1232599 := bstep (se 1 (by rfl) ⟨924449, by rfl⟩ : syracuseStep 1232599 = 1848899) B1848899
theorem B1232619 : Blo 1232434 1232619 := bstep (se 1 (by rfl) ⟨924464, by rfl⟩ : syracuseStep 1232619 = 1848929) B1848929
theorem B1232631 : Blo 1232434 1232631 := bstep (se 1 (by rfl) ⟨924473, by rfl⟩ : syracuseStep 1232631 = 1848947) B1848947
theorem B1232651 : Blo 1232434 1232651 := bstep (se 1 (by rfl) ⟨924488, by rfl⟩ : syracuseStep 1232651 = 1848977) B1848977
theorem B1388299 : Blo 1232434 1388299 := bstep (se 1 (by rfl) ⟨1041224, by rfl⟩ : syracuseStep 1388299 = 2082449) B2082449
theorem B1232663 : Blo 1232434 1232663 := bstep (se 1 (by rfl) ⟨924497, by rfl⟩ : syracuseStep 1232663 = 1848995) B1848995
theorem B1232683 : Blo 1232434 1232683 := bstep (se 1 (by rfl) ⟨924512, by rfl⟩ : syracuseStep 1232683 = 1849025) B1849025
theorem B3510067 : Blo 1232434 3510067 := bstep (se 1 (by rfl) ⟨2632550, by rfl⟩ : syracuseStep 3510067 = 5265101) B5265101
theorem B1232695 : Blo 1232434 1232695 := bstep (se 1 (by rfl) ⟨924521, by rfl⟩ : syracuseStep 1232695 = 1849043) B1849043
theorem B35589941 : Blo 1232434 35589941 := bstep (se 5 (by rfl) ⟨1668278, by rfl⟩ : syracuseStep 35589941 = 3336557) B3336557
theorem B1232715 : Blo 1232434 1232715 := bstep (se 1 (by rfl) ⟨924536, by rfl⟩ : syracuseStep 1232715 = 1849073) B1849073
theorem B4681547 : Blo 1232434 4681547 := bstep (se 1 (by rfl) ⟨3511160, by rfl⟩ : syracuseStep 4681547 = 7022321) B7022321
theorem B4165451 : Blo 1232434 4165451 := bstep (se 1 (by rfl) ⟨3124088, by rfl⟩ : syracuseStep 4165451 = 6248177) B6248177
theorem B1232727 : Blo 1232434 1232727 := bstep (se 1 (by rfl) ⟨924545, by rfl⟩ : syracuseStep 1232727 = 1849091) B1849091
theorem B5271389 : Blo 1232434 5271389 := bstep (se 3 (by rfl) ⟨988385, by rfl⟩ : syracuseStep 5271389 = 1976771) B1976771
theorem B1232747 : Blo 1232434 1232747 := bstep (se 1 (by rfl) ⟨924560, by rfl⟩ : syracuseStep 1232747 = 1849121) B1849121
theorem B1232759 : Blo 1232434 1232759 := bstep (se 1 (by rfl) ⟨924569, by rfl⟩ : syracuseStep 1232759 = 1849139) B1849139
theorem B1388407 : Blo 1232434 1388407 := bstep (se 1 (by rfl) ⟨1041305, by rfl⟩ : syracuseStep 1388407 = 2082611) B2082611
theorem B1232779 : Blo 1232434 1232779 := bstep (se 1 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 1232779 = 1849169) B1849169
theorem B1232791 : Blo 1232434 1232791 := bstep (se 1 (by rfl) ⟨924593, by rfl⟩ : syracuseStep 1232791 = 1849187) B1849187
theorem B1232811 : Blo 1232434 1232811 := bstep (se 1 (by rfl) ⟨924608, by rfl⟩ : syracuseStep 1232811 = 1849217) B1849217
theorem B1232823 : Blo 1232434 1232823 := bstep (se 1 (by rfl) ⟨924617, by rfl⟩ : syracuseStep 1232823 = 1849235) B1849235
theorem B1232843 : Blo 1232434 1232843 := bstep (se 1 (by rfl) ⟨924632, by rfl⟩ : syracuseStep 1232843 = 1849265) B1849265
theorem B1232855 : Blo 1232434 1232855 := bstep (se 1 (by rfl) ⟨924641, by rfl⟩ : syracuseStep 1232855 = 1849283) B1849283
theorem B1232875 : Blo 1232434 1232875 := bstep (se 1 (by rfl) ⟨924656, by rfl⟩ : syracuseStep 1232875 = 1849313) B1849313
theorem B1232887 : Blo 1232434 1232887 := bstep (se 1 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 1232887 = 1849331) B1849331
theorem B1232907 : Blo 1232434 1232907 := bstep (se 1 (by rfl) ⟨924680, by rfl⟩ : syracuseStep 1232907 = 1849361) B1849361
theorem B4681745 : Blo 1232434 4681745 := bstep (se 2 (by rfl) ⟨1755654, by rfl⟩ : syracuseStep 4681745 = 3511309) B3511309
theorem B1232919 : Blo 1232434 1232919 := bstep (se 1 (by rfl) ⟨924689, by rfl⟩ : syracuseStep 1232919 = 1849379) B1849379
theorem B1757209 : Blo 1232434 1757209 := bstep (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) B1317907
theorem B1232939 : Blo 1232434 1232939 := bstep (se 1 (by rfl) ⟨924704, by rfl⟩ : syracuseStep 1232939 = 1849409) B1849409
theorem B1388587 : Blo 1232434 1388587 := bstep (se 1 (by rfl) ⟨1041440, by rfl⟩ : syracuseStep 1388587 = 2082881) B2082881
theorem B2773043 : Blo 1232434 2773043 := bstep (se 1 (by rfl) ⟨2079782, by rfl⟩ : syracuseStep 2773043 = 4159565) B4159565
theorem B1232951 : Blo 1232434 1232951 := bstep (se 1 (by rfl) ⟨924713, by rfl⟩ : syracuseStep 1232951 = 1849427) B1849427
theorem B1232971 : Blo 1232434 1232971 := bstep (se 1 (by rfl) ⟨924728, by rfl⟩ : syracuseStep 1232971 = 1849457) B1849457
theorem B2773079 : Blo 1232434 2773079 := bstep (se 1 (by rfl) ⟨2079809, by rfl⟩ : syracuseStep 2773079 = 4159619) B4159619
theorem B1232983 : Blo 1232434 1232983 := bstep (se 1 (by rfl) ⟨924737, by rfl⟩ : syracuseStep 1232983 = 1849475) B1849475
theorem B4165721 : Blo 1232434 4165721 := bstep (se 2 (by rfl) ⟨1562145, by rfl⟩ : syracuseStep 4165721 = 3124291) B3124291
theorem B1233003 : Blo 1232434 1233003 := bstep (se 1 (by rfl) ⟨924752, by rfl⟩ : syracuseStep 1233003 = 1849505) B1849505
theorem B1233015 : Blo 1232434 1233015 := bstep (se 1 (by rfl) ⟨924761, by rfl⟩ : syracuseStep 1233015 = 1849523) B1849523
theorem B1233035 : Blo 1232434 1233035 := bstep (se 1 (by rfl) ⟨924776, by rfl⟩ : syracuseStep 1233035 = 1849553) B1849553
theorem B1757323 : Blo 1232434 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B1233047 : Blo 1232434 1233047 := bstep (se 1 (by rfl) ⟨924785, by rfl⟩ : syracuseStep 1233047 = 1849571) B1849571
theorem B1388695 : Blo 1232434 1388695 := bstep (se 1 (by rfl) ⟨1041521, by rfl⟩ : syracuseStep 1388695 = 2083043) B2083043
theorem B1233067 : Blo 1232434 1233067 := bstep (se 1 (by rfl) ⟨924800, by rfl⟩ : syracuseStep 1233067 = 1849601) B1849601
theorem B28487861 : Blo 1232434 28487861 := bstep (se 5 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 28487861 = 2670737) B2670737
theorem B1233079 : Blo 1232434 1233079 := bstep (se 1 (by rfl) ⟨924809, by rfl⟩ : syracuseStep 1233079 = 1849619) B1849619
theorem B1233099 : Blo 1232434 1233099 := bstep (se 1 (by rfl) ⟨924824, by rfl⟩ : syracuseStep 1233099 = 1849649) B1849649
theorem B1233111 : Blo 1232434 1233111 := bstep (se 1 (by rfl) ⟨924833, by rfl⟩ : syracuseStep 1233111 = 1849667) B1849667
theorem B1233131 : Blo 1232434 1233131 := bstep (se 1 (by rfl) ⟨924848, by rfl⟩ : syracuseStep 1233131 = 1849697) B1849697
theorem B1233143 : Blo 1232434 1233143 := bstep (se 1 (by rfl) ⟨924857, by rfl⟩ : syracuseStep 1233143 = 1849715) B1849715
theorem B2773259 : Blo 1232434 2773259 := bstep (se 1 (by rfl) ⟨2079944, by rfl⟩ : syracuseStep 2773259 = 4159889) B4159889
theorem B1233163 : Blo 1232434 1233163 := bstep (se 1 (by rfl) ⟨924872, by rfl⟩ : syracuseStep 1233163 = 1849745) B1849745
theorem B1233175 : Blo 1232434 1233175 := bstep (se 1 (by rfl) ⟨924881, by rfl⟩ : syracuseStep 1233175 = 1849763) B1849763
theorem B1233195 : Blo 1232434 1233195 := bstep (se 1 (by rfl) ⟨924896, by rfl⟩ : syracuseStep 1233195 = 1849793) B1849793
theorem B1233207 : Blo 1232434 1233207 := bstep (se 1 (by rfl) ⟨924905, by rfl⟩ : syracuseStep 1233207 = 1849811) B1849811
theorem B2773313 : Blo 1232434 2773313 := bstep (se 2 (by rfl) ⟨1039992, by rfl⟩ : syracuseStep 2773313 = 2079985) B2079985
theorem B1233227 : Blo 1232434 1233227 := bstep (se 1 (by rfl) ⟨924920, by rfl⟩ : syracuseStep 1233227 = 1849841) B1849841
theorem B1233239 : Blo 1232434 1233239 := bstep (se 1 (by rfl) ⟨924929, by rfl⟩ : syracuseStep 1233239 = 1849859) B1849859
theorem B1233259 : Blo 1232434 1233259 := bstep (se 1 (by rfl) ⟨924944, by rfl⟩ : syracuseStep 1233259 = 1849889) B1849889
theorem B1233271 : Blo 1232434 1233271 := bstep (se 1 (by rfl) ⟨924953, by rfl⟩ : syracuseStep 1233271 = 1849907) B1849907
theorem B10539395 : Blo 1232434 10539395 := bstep (se 1 (by rfl) ⟨7904546, by rfl⟩ : syracuseStep 10539395 = 15809093) B15809093
theorem B1233291 : Blo 1232434 1233291 := bstep (se 1 (by rfl) ⟨924968, by rfl⟩ : syracuseStep 1233291 = 1849937) B1849937
theorem B1560971 : Blo 1232434 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B1233303 : Blo 1232434 1233303 := bstep (se 1 (by rfl) ⟨924977, by rfl⟩ : syracuseStep 1233303 = 1849955) B1849955
theorem B1233323 : Blo 1232434 1233323 := bstep (se 1 (by rfl) ⟨924992, by rfl⟩ : syracuseStep 1233323 = 1849985) B1849985
theorem B1233335 : Blo 1232434 1233335 := bstep (se 1 (by rfl) ⟨925001, by rfl⟩ : syracuseStep 1233335 = 1850003) B1850003
theorem B1233355 : Blo 1232434 1233355 := bstep (se 1 (by rfl) ⟨925016, by rfl⟩ : syracuseStep 1233355 = 1850033) B1850033
theorem B1233367 : Blo 1232434 1233367 := bstep (se 1 (by rfl) ⟨925025, by rfl⟩ : syracuseStep 1233367 = 1850051) B1850051
theorem B11858393 : Blo 1232434 11858393 := bstep (se 2 (by rfl) ⟨4446897, by rfl⟩ : syracuseStep 11858393 = 8893795) B8893795
theorem B1233387 : Blo 1232434 1233387 := bstep (se 1 (by rfl) ⟨925040, by rfl⟩ : syracuseStep 1233387 = 1850081) B1850081
theorem B1233399 : Blo 1232434 1233399 := bstep (se 1 (by rfl) ⟨925049, by rfl⟩ : syracuseStep 1233399 = 1850099) B1850099
theorem B1233419 : Blo 1232434 1233419 := bstep (se 1 (by rfl) ⟨925064, by rfl⟩ : syracuseStep 1233419 = 1850129) B1850129
theorem B1233431 : Blo 1232434 1233431 := bstep (se 1 (by rfl) ⟨925073, by rfl⟩ : syracuseStep 1233431 = 1850147) B1850147
theorem B2773529 : Blo 1232434 2773529 := bstep (se 2 (by rfl) ⟨1040073, by rfl⟩ : syracuseStep 2773529 = 2080147) B2080147
theorem B1233451 : Blo 1232434 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B1233463 : Blo 1232434 1233463 := bstep (se 1 (by rfl) ⟨925097, by rfl⟩ : syracuseStep 1233463 = 1850195) B1850195
theorem B5927489 : Blo 1232434 5927489 := bstep (se 2 (by rfl) ⟨2222808, by rfl⟩ : syracuseStep 5927489 = 4445617) B4445617
theorem B1233483 : Blo 1232434 1233483 := bstep (se 1 (by rfl) ⟨925112, by rfl⟩ : syracuseStep 1233483 = 1850225) B1850225
theorem B1233495 : Blo 1232434 1233495 := bstep (se 1 (by rfl) ⟨925121, by rfl⟩ : syracuseStep 1233495 = 1850243) B1850243
theorem B1233515 : Blo 1232434 1233515 := bstep (se 1 (by rfl) ⟨925136, by rfl⟩ : syracuseStep 1233515 = 1850273) B1850273
theorem B2773619 : Blo 1232434 2773619 := bstep (se 1 (by rfl) ⟨2080214, by rfl⟩ : syracuseStep 2773619 = 4160429) B4160429
theorem B1233527 : Blo 1232434 1233527 := bstep (se 1 (by rfl) ⟨925145, by rfl⟩ : syracuseStep 1233527 = 1850291) B1850291
theorem B6247043 : Blo 1232434 6247043 := bstep (se 1 (by rfl) ⟨4685282, by rfl⟩ : syracuseStep 6247043 = 9370565) B9370565
theorem B1233547 : Blo 1232434 1233547 := bstep (se 1 (by rfl) ⟨925160, by rfl⟩ : syracuseStep 1233547 = 1850321) B1850321
theorem B2773655 : Blo 1232434 2773655 := bstep (se 1 (by rfl) ⟨2080241, by rfl⟩ : syracuseStep 2773655 = 4160483) B4160483
theorem B1233559 : Blo 1232434 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B1233579 : Blo 1232434 1233579 := bstep (se 1 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 1233579 = 1850369) B1850369
theorem B1233591 : Blo 1232434 1233591 := bstep (se 1 (by rfl) ⟨925193, by rfl⟩ : syracuseStep 1233591 = 1850387) B1850387
theorem B3379915 : Blo 1232434 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B1233611 : Blo 1232434 1233611 := bstep (se 1 (by rfl) ⟨925208, by rfl⟩ : syracuseStep 1233611 = 1850417) B1850417
theorem B1233623 : Blo 1232434 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B3511001 : Blo 1232434 3511001 := bstep (se 2 (by rfl) ⟨1316625, by rfl⟩ : syracuseStep 3511001 = 2633251) B2633251
theorem B1233643 : Blo 1232434 1233643 := bstep (se 1 (by rfl) ⟨925232, by rfl⟩ : syracuseStep 1233643 = 1850465) B1850465
theorem B1233655 : Blo 1232434 1233655 := bstep (se 1 (by rfl) ⟨925241, by rfl⟩ : syracuseStep 1233655 = 1850483) B1850483
theorem B1233675 : Blo 1232434 1233675 := bstep (se 1 (by rfl) ⟨925256, by rfl⟩ : syracuseStep 1233675 = 1850513) B1850513
theorem B7705361 : Blo 1232434 7705361 := bstep (se 2 (by rfl) ⟨2889510, by rfl⟩ : syracuseStep 7705361 = 5779021) B5779021
theorem B4682519 : Blo 1232434 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B1233687 : Blo 1232434 1233687 := bstep (se 1 (by rfl) ⟨925265, by rfl⟩ : syracuseStep 1233687 = 1850531) B1850531
theorem B1233707 : Blo 1232434 1233707 := bstep (se 1 (by rfl) ⟨925280, by rfl⟩ : syracuseStep 1233707 = 1850561) B1850561
theorem B1233719 : Blo 1232434 1233719 := bstep (se 1 (by rfl) ⟨925289, by rfl⟩ : syracuseStep 1233719 = 1850579) B1850579
theorem B4002625 : Blo 1232434 4002625 := bstep (se 2 (by rfl) ⟨1500984, by rfl⟩ : syracuseStep 4002625 = 3001969) B3001969
theorem B2773835 : Blo 1232434 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B1233739 : Blo 1232434 1233739 := bstep (se 1 (by rfl) ⟨925304, by rfl⟩ : syracuseStep 1233739 = 1850609) B1850609
theorem B1233751 : Blo 1232434 1233751 := bstep (se 1 (by rfl) ⟨925313, by rfl⟩ : syracuseStep 1233751 = 1850627) B1850627
theorem B1233771 : Blo 1232434 1233771 := bstep (se 1 (by rfl) ⟨925328, by rfl⟩ : syracuseStep 1233771 = 1850657) B1850657
theorem B1233783 : Blo 1232434 1233783 := bstep (se 1 (by rfl) ⟨925337, by rfl⟩ : syracuseStep 1233783 = 1850675) B1850675
theorem B2773889 : Blo 1232434 2773889 := bstep (se 2 (by rfl) ⟨1040208, by rfl⟩ : syracuseStep 2773889 = 2080417) B2080417
theorem B1233803 : Blo 1232434 1233803 := bstep (se 1 (by rfl) ⟨925352, by rfl⟩ : syracuseStep 1233803 = 1850705) B1850705
theorem B1233815 : Blo 1232434 1233815 := bstep (se 1 (by rfl) ⟨925361, by rfl⟩ : syracuseStep 1233815 = 1850723) B1850723
theorem B1233835 : Blo 1232434 1233835 := bstep (se 1 (by rfl) ⟨925376, by rfl⟩ : syracuseStep 1233835 = 1850753) B1850753
theorem B1233847 : Blo 1232434 1233847 := bstep (se 1 (by rfl) ⟨925385, by rfl⟩ : syracuseStep 1233847 = 1850771) B1850771
theorem B2962369 : Blo 1232434 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B1233867 : Blo 1232434 1233867 := bstep (se 1 (by rfl) ⟨925400, by rfl⟩ : syracuseStep 1233867 = 1850801) B1850801
theorem B1233879 : Blo 1232434 1233879 := bstep (se 1 (by rfl) ⟨925409, by rfl⟩ : syracuseStep 1233879 = 1850819) B1850819
theorem B4682717 : Blo 1232434 4682717 := bstep (se 3 (by rfl) ⟨878009, by rfl⟩ : syracuseStep 4682717 = 1756019) B1756019
theorem B1233899 : Blo 1232434 1233899 := bstep (se 1 (by rfl) ⟨925424, by rfl⟩ : syracuseStep 1233899 = 1850849) B1850849
theorem B1233911 : Blo 1232434 1233911 := bstep (se 1 (by rfl) ⟨925433, by rfl⟩ : syracuseStep 1233911 = 1850867) B1850867
theorem B1233931 : Blo 1232434 1233931 := bstep (se 1 (by rfl) ⟨925448, by rfl⟩ : syracuseStep 1233931 = 1850897) B1850897
theorem B1233943 : Blo 1232434 1233943 := bstep (se 1 (by rfl) ⟨925457, by rfl⟩ : syracuseStep 1233943 = 1850915) B1850915
theorem B1233963 : Blo 1232434 1233963 := bstep (se 1 (by rfl) ⟨925472, by rfl⟩ : syracuseStep 1233963 = 1850945) B1850945
theorem B9368621 : Blo 1232434 9368621 := bstep (se 3 (by rfl) ⟨1756616, by rfl⟩ : syracuseStep 9368621 = 3513233) B3513233
theorem B1233975 : Blo 1232434 1233975 := bstep (se 1 (by rfl) ⟨925481, by rfl⟩ : syracuseStep 1233975 = 1850963) B1850963
theorem B1561675 : Blo 1232434 1561675 := bstep (se 1 (by rfl) ⟨1171256, by rfl⟩ : syracuseStep 1561675 = 2342513) B2342513
theorem B1233995 : Blo 1232434 1233995 := bstep (se 1 (by rfl) ⟨925496, by rfl⟩ : syracuseStep 1233995 = 1850993) B1850993
theorem B1234007 : Blo 1232434 1234007 := bstep (se 1 (by rfl) ⟨925505, by rfl⟩ : syracuseStep 1234007 = 1851011) B1851011
theorem B2774105 : Blo 1232434 2774105 := bstep (se 2 (by rfl) ⟨1040289, by rfl⟩ : syracuseStep 2774105 = 2080579) B2080579
theorem B1234027 : Blo 1232434 1234027 := bstep (se 1 (by rfl) ⟨925520, by rfl⟩ : syracuseStep 1234027 = 1851041) B1851041
theorem B1234039 : Blo 1232434 1234039 := bstep (se 1 (by rfl) ⟨925529, by rfl⟩ : syracuseStep 1234039 = 1851059) B1851059
theorem B1234059 : Blo 1232434 1234059 := bstep (se 1 (by rfl) ⟨925544, by rfl⟩ : syracuseStep 1234059 = 1851089) B1851089
theorem B5272721 : Blo 1232434 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B1234071 : Blo 1232434 1234071 := bstep (se 1 (by rfl) ⟨925553, by rfl⟩ : syracuseStep 1234071 = 1851107) B1851107
theorem B1234091 : Blo 1232434 1234091 := bstep (se 1 (by rfl) ⟨925568, by rfl⟩ : syracuseStep 1234091 = 1851137) B1851137
theorem B2774195 : Blo 1232434 2774195 := bstep (se 1 (by rfl) ⟨2080646, by rfl⟩ : syracuseStep 2774195 = 4161293) B4161293
theorem B1234103 : Blo 1232434 1234103 := bstep (se 1 (by rfl) ⟨925577, by rfl⟩ : syracuseStep 1234103 = 1851155) B1851155
theorem B4445387 : Blo 1232434 4445387 := bstep (se 1 (by rfl) ⟨3334040, by rfl⟩ : syracuseStep 4445387 = 6668081) B6668081
theorem B1234123 : Blo 1232434 1234123 := bstep (se 1 (by rfl) ⟨925592, by rfl⟩ : syracuseStep 1234123 = 1851185) B1851185
theorem B10532045 : Blo 1232434 10532045 := bstep (se 3 (by rfl) ⟨1974758, by rfl⟩ : syracuseStep 10532045 = 3949517) B3949517
theorem B2774231 : Blo 1232434 2774231 := bstep (se 1 (by rfl) ⟨2080673, by rfl⟩ : syracuseStep 2774231 = 4161347) B4161347
theorem B1234135 : Blo 1232434 1234135 := bstep (se 1 (by rfl) ⟨925601, by rfl⟩ : syracuseStep 1234135 = 1851203) B1851203
theorem B1234155 : Blo 1232434 1234155 := bstep (se 1 (by rfl) ⟨925616, by rfl⟩ : syracuseStep 1234155 = 1851233) B1851233
theorem B2340083 : Blo 1232434 2340083 := bstep (se 1 (by rfl) ⟨1755062, by rfl⟩ : syracuseStep 2340083 = 3510125) B3510125
theorem B1234167 : Blo 1232434 1234167 := bstep (se 1 (by rfl) ⟨925625, by rfl⟩ : syracuseStep 1234167 = 1851251) B1851251
theorem B1234187 : Blo 1232434 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B1234199 : Blo 1232434 1234199 := bstep (se 1 (by rfl) ⟨925649, by rfl⟩ : syracuseStep 1234199 = 1851299) B1851299
theorem B1234219 : Blo 1232434 1234219 := bstep (se 1 (by rfl) ⟨925664, by rfl⟩ : syracuseStep 1234219 = 1851329) B1851329
theorem B1234231 : Blo 1232434 1234231 := bstep (se 1 (by rfl) ⟨925673, by rfl⟩ : syracuseStep 1234231 = 1851347) B1851347
theorem B1234251 : Blo 1232434 1234251 := bstep (se 1 (by rfl) ⟨925688, by rfl⟩ : syracuseStep 1234251 = 1851377) B1851377
theorem B1561943 : Blo 1232434 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B1234263 : Blo 1232434 1234263 := bstep (se 1 (by rfl) ⟨925697, by rfl⟩ : syracuseStep 1234263 = 1851395) B1851395
theorem B1848665 : Blo 1232434 1848665 := bstep (se 2 (by rfl) ⟨693249, by rfl⟩ : syracuseStep 1848665 = 1386499) B1386499
theorem B1234283 : Blo 1232434 1234283 := bstep (se 1 (by rfl) ⟨925712, by rfl⟩ : syracuseStep 1234283 = 1851425) B1851425
theorem B1234295 : Blo 1232434 1234295 := bstep (se 1 (by rfl) ⟨925721, by rfl⟩ : syracuseStep 1234295 = 1851443) B1851443
theorem B2774411 : Blo 1232434 2774411 := bstep (se 1 (by rfl) ⟨2080808, by rfl⟩ : syracuseStep 2774411 = 4161617) B4161617
theorem B1234315 : Blo 1232434 1234315 := bstep (se 1 (by rfl) ⟨925736, by rfl⟩ : syracuseStep 1234315 = 1851473) B1851473
theorem B1234327 : Blo 1232434 1234327 := bstep (se 1 (by rfl) ⟨925745, by rfl⟩ : syracuseStep 1234327 = 1851491) B1851491
theorem B1234347 : Blo 1232434 1234347 := bstep (se 1 (by rfl) ⟨925760, by rfl⟩ : syracuseStep 1234347 = 1851521) B1851521
theorem B1234359 : Blo 1232434 1234359 := bstep (se 1 (by rfl) ⟨925769, by rfl⟩ : syracuseStep 1234359 = 1851539) B1851539
theorem B2774465 : Blo 1232434 2774465 := bstep (se 2 (by rfl) ⟨1040424, by rfl⟩ : syracuseStep 2774465 = 2080849) B2080849
theorem B1848779 : Blo 1232434 1848779 := bstep (se 1 (by rfl) ⟨1386584, by rfl⟩ : syracuseStep 1848779 = 2773169) B2773169
theorem B1234379 : Blo 1232434 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B9360845 : Blo 1232434 9360845 := bstep (se 3 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 9360845 = 3510317) B3510317
theorem B1848791 : Blo 1232434 1848791 := bstep (se 1 (by rfl) ⟨1386593, by rfl⟩ : syracuseStep 1848791 = 2773187) B2773187
theorem B1234391 : Blo 1232434 1234391 := bstep (se 1 (by rfl) ⟨925793, by rfl⟩ : syracuseStep 1234391 = 1851587) B1851587
theorem B1234411 : Blo 1232434 1234411 := bstep (se 1 (by rfl) ⟨925808, by rfl⟩ : syracuseStep 1234411 = 1851617) B1851617
theorem B1234423 : Blo 1232434 1234423 := bstep (se 1 (by rfl) ⟨925817, by rfl⟩ : syracuseStep 1234423 = 1851635) B1851635
theorem B2373143 : Blo 1232434 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B1848857 : Blo 1232434 1848857 := bstep (se 2 (by rfl) ⟨693321, by rfl⟩ : syracuseStep 1848857 = 1386643) B1386643
theorem B1848971 : Blo 1232434 1848971 := bstep (se 1 (by rfl) ⟨1386728, by rfl⟩ : syracuseStep 1848971 = 2773457) B2773457
theorem B1848983 : Blo 1232434 1848983 := bstep (se 1 (by rfl) ⟨1386737, by rfl⟩ : syracuseStep 1848983 = 2773475) B2773475
theorem B2774681 : Blo 1232434 2774681 := bstep (se 2 (by rfl) ⟨1040505, by rfl⟩ : syracuseStep 2774681 = 2081011) B2081011
theorem B40031941 : Blo 1232434 40031941 := bstep (se 4 (by rfl) ⟨3752994, by rfl⟩ : syracuseStep 40031941 = 7505989) B7505989
theorem B1849049 : Blo 1232434 1849049 := bstep (se 2 (by rfl) ⟨693393, by rfl⟩ : syracuseStep 1849049 = 1386787) B1386787
theorem B2340569 : Blo 1232434 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B2774771 : Blo 1232434 2774771 := bstep (se 1 (by rfl) ⟨2081078, by rfl⟩ : syracuseStep 2774771 = 4162157) B4162157
theorem B2774807 : Blo 1232434 2774807 := bstep (se 1 (by rfl) ⟨2081105, by rfl⟩ : syracuseStep 2774807 = 4162211) B4162211
theorem B4445975 : Blo 1232434 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B7116589 : Blo 1232434 7116589 := bstep (se 3 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 7116589 = 2668721) B2668721
theorem B1849163 : Blo 1232434 1849163 := bstep (se 1 (by rfl) ⟨1386872, by rfl⟩ : syracuseStep 1849163 = 2773745) B2773745
theorem B1849175 : Blo 1232434 1849175 := bstep (se 1 (by rfl) ⟨1386881, by rfl⟩ : syracuseStep 1849175 = 2773763) B2773763
theorem B1849241 : Blo 1232434 1849241 := bstep (se 2 (by rfl) ⟨693465, by rfl⟩ : syracuseStep 1849241 = 1386931) B1386931
theorem B1316779 : Blo 1232434 1316779 := bstep (se 1 (by rfl) ⟨987584, by rfl⟩ : syracuseStep 1316779 = 1975169) B1975169
theorem B9361331 : Blo 1232434 9361331 := bstep (se 1 (by rfl) ⟨7020998, by rfl⟩ : syracuseStep 9361331 = 14041997) B14041997
theorem B2774987 : Blo 1232434 2774987 := bstep (se 1 (by rfl) ⟨2081240, by rfl⟩ : syracuseStep 2774987 = 4162481) B4162481
theorem B2775041 : Blo 1232434 2775041 := bstep (se 2 (by rfl) ⟨1040640, by rfl⟩ : syracuseStep 2775041 = 2081281) B2081281
theorem B1849355 : Blo 1232434 1849355 := bstep (se 1 (by rfl) ⟨1387016, by rfl⟩ : syracuseStep 1849355 = 2774033) B2774033
theorem B4159511 : Blo 1232434 4159511 := bstep (se 1 (by rfl) ⟨3119633, by rfl⟩ : syracuseStep 4159511 = 6239267) B6239267
theorem B1849367 : Blo 1232434 1849367 := bstep (se 1 (by rfl) ⟨1387025, by rfl⟩ : syracuseStep 1849367 = 2774051) B2774051
theorem B1849433 : Blo 1232434 1849433 := bstep (se 2 (by rfl) ⟨693537, by rfl⟩ : syracuseStep 1849433 = 1387075) B1387075
theorem B3512413 : Blo 1232434 3512413 := bstep (se 3 (by rfl) ⟨658577, by rfl⟩ : syracuseStep 3512413 = 1317155) B1317155
theorem B6666371 : Blo 1232434 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B1849547 : Blo 1232434 1849547 := bstep (se 1 (by rfl) ⟨1387160, by rfl⟩ : syracuseStep 1849547 = 2774321) B2774321
theorem B1849559 : Blo 1232434 1849559 := bstep (se 1 (by rfl) ⟨1387169, by rfl⟩ : syracuseStep 1849559 = 2774339) B2774339
theorem B2775257 : Blo 1232434 2775257 := bstep (se 2 (by rfl) ⟨1040721, by rfl⟩ : syracuseStep 2775257 = 2081443) B2081443
theorem B1849625 : Blo 1232434 1849625 := bstep (se 2 (by rfl) ⟨693609, by rfl⟩ : syracuseStep 1849625 = 1387219) B1387219
theorem B2775347 : Blo 1232434 2775347 := bstep (se 1 (by rfl) ⟨2081510, by rfl⟩ : syracuseStep 2775347 = 4163021) B4163021
theorem B3512641 : Blo 1232434 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B2775383 : Blo 1232434 2775383 := bstep (se 1 (by rfl) ⟨2081537, by rfl⟩ : syracuseStep 2775383 = 4163075) B4163075
theorem B1849739 : Blo 1232434 1849739 := bstep (se 1 (by rfl) ⟨1387304, by rfl⟩ : syracuseStep 1849739 = 2774609) B2774609
theorem B1849751 : Blo 1232434 1849751 := bstep (se 1 (by rfl) ⟨1387313, by rfl⟩ : syracuseStep 1849751 = 2774627) B2774627
theorem B4446667 : Blo 1232434 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B1849817 : Blo 1232434 1849817 := bstep (se 2 (by rfl) ⟨693681, by rfl⟩ : syracuseStep 1849817 = 1387363) B1387363
theorem B2775563 : Blo 1232434 2775563 := bstep (se 1 (by rfl) ⟨2081672, by rfl⟩ : syracuseStep 2775563 = 4163345) B4163345
theorem B4160051 : Blo 1232434 4160051 := bstep (se 1 (by rfl) ⟨3120038, by rfl⟩ : syracuseStep 4160051 = 6240077) B6240077
theorem B2775617 : Blo 1232434 2775617 := bstep (se 2 (by rfl) ⟨1040856, by rfl⟩ : syracuseStep 2775617 = 2081713) B2081713
theorem B1849931 : Blo 1232434 1849931 := bstep (se 1 (by rfl) ⟨1387448, by rfl⟩ : syracuseStep 1849931 = 2774897) B2774897
theorem B1849943 : Blo 1232434 1849943 := bstep (se 1 (by rfl) ⟨1387457, by rfl⟩ : syracuseStep 1849943 = 2774915) B2774915
theorem B3119705 : Blo 1232434 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B8010341 : Blo 1232434 8010341 := bstep (se 4 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 8010341 = 1501939) B1501939
theorem B3512983 : Blo 1232434 3512983 := bstep (se 1 (by rfl) ⟨2634737, by rfl⟩ : syracuseStep 3512983 = 5269475) B5269475
theorem B1850009 : Blo 1232434 1850009 := bstep (se 2 (by rfl) ⟨693753, by rfl⟩ : syracuseStep 1850009 = 1387507) B1387507
theorem B89979605 : Blo 1232434 89979605 := bstep (se 7 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 89979605 = 2108897) B2108897
theorem B1850123 : Blo 1232434 1850123 := bstep (se 1 (by rfl) ⟨1387592, by rfl⟩ : syracuseStep 1850123 = 2775185) B2775185
theorem B1850135 : Blo 1232434 1850135 := bstep (se 1 (by rfl) ⟨1387601, by rfl⟩ : syracuseStep 1850135 = 2775203) B2775203
theorem B2775833 : Blo 1232434 2775833 := bstep (se 2 (by rfl) ⟨1040937, by rfl⟩ : syracuseStep 2775833 = 2081875) B2081875
theorem B4160321 : Blo 1232434 4160321 := bstep (se 2 (by rfl) ⟨1560120, by rfl⟩ : syracuseStep 4160321 = 3120241) B3120241
theorem B1317719 : Blo 1232434 1317719 := bstep (se 1 (by rfl) ⟨988289, by rfl⟩ : syracuseStep 1317719 = 1976579) B1976579
theorem B1850201 : Blo 1232434 1850201 := bstep (se 2 (by rfl) ⟨693825, by rfl⟩ : syracuseStep 1850201 = 1387651) B1387651
theorem B2775923 : Blo 1232434 2775923 := bstep (se 1 (by rfl) ⟨2081942, by rfl⟩ : syracuseStep 2775923 = 4163885) B4163885
theorem B4684675 : Blo 1232434 4684675 := bstep (se 1 (by rfl) ⟨3513506, by rfl⟩ : syracuseStep 4684675 = 7027013) B7027013
theorem B2775959 : Blo 1232434 2775959 := bstep (se 1 (by rfl) ⟨2081969, by rfl⟩ : syracuseStep 2775959 = 4163939) B4163939
theorem B1850315 : Blo 1232434 1850315 := bstep (se 1 (by rfl) ⟨1387736, by rfl⟩ : syracuseStep 1850315 = 2775473) B2775473
theorem B1850327 : Blo 1232434 1850327 := bstep (se 1 (by rfl) ⟨1387745, by rfl⟩ : syracuseStep 1850327 = 2775491) B2775491
theorem B3333143 : Blo 1232434 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B2079769 : Blo 1232434 2079769 := bstep (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) B1559827
theorem B1850393 : Blo 1232434 1850393 := bstep (se 2 (by rfl) ⟨693897, by rfl⟩ : syracuseStep 1850393 = 1387795) B1387795
theorem B2776139 : Blo 1232434 2776139 := bstep (se 1 (by rfl) ⟨2082104, by rfl⟩ : syracuseStep 2776139 = 4164209) B4164209
theorem B3005515 : Blo 1232434 3005515 := bstep (se 1 (by rfl) ⟨2254136, by rfl⟩ : syracuseStep 3005515 = 4508273) B4508273
theorem B6241373 : Blo 1232434 6241373 := bstep (se 3 (by rfl) ⟨1170257, by rfl⟩ : syracuseStep 6241373 = 2340515) B2340515
theorem B2776193 : Blo 1232434 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B2342027 : Blo 1232434 2342027 := bstep (se 1 (by rfl) ⟨1756520, by rfl⟩ : syracuseStep 2342027 = 3513041) B3513041
theorem B1850507 : Blo 1232434 1850507 := bstep (se 1 (by rfl) ⟨1387880, by rfl⟩ : syracuseStep 1850507 = 2775761) B2775761
theorem B3333271 : Blo 1232434 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B1850519 : Blo 1232434 1850519 := bstep (se 1 (by rfl) ⟨1387889, by rfl⟩ : syracuseStep 1850519 = 2775779) B2775779
theorem B4684979 : Blo 1232434 4684979 := bstep (se 1 (by rfl) ⟨3513734, by rfl⟩ : syracuseStep 4684979 = 7027469) B7027469
theorem B1850585 : Blo 1232434 1850585 := bstep (se 2 (by rfl) ⟨693969, by rfl⟩ : syracuseStep 1850585 = 1387939) B1387939
theorem B5266691 : Blo 1232434 5266691 := bstep (se 1 (by rfl) ⟨3950018, by rfl⟩ : syracuseStep 5266691 = 7900037) B7900037
theorem B2342209 : Blo 1232434 2342209 := bstep (se 2 (by rfl) ⟨878328, by rfl⟩ : syracuseStep 2342209 = 1756657) B1756657
theorem B1850699 : Blo 1232434 1850699 := bstep (se 1 (by rfl) ⟨1388024, by rfl⟩ : syracuseStep 1850699 = 2776049) B2776049
theorem B1850711 : Blo 1232434 1850711 := bstep (se 1 (by rfl) ⟨1388033, by rfl⟩ : syracuseStep 1850711 = 2776067) B2776067
theorem B3513689 : Blo 1232434 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B2776409 : Blo 1232434 2776409 := bstep (se 2 (by rfl) ⟨1041153, by rfl⟩ : syracuseStep 2776409 = 2082307) B2082307
theorem B4160861 : Blo 1232434 4160861 := bstep (se 3 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 4160861 = 1560323) B1560323
theorem B9362789 : Blo 1232434 9362789 := bstep (se 4 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 9362789 = 1755523) B1755523
theorem B1850777 : Blo 1232434 1850777 := bstep (se 2 (by rfl) ⟨694041, by rfl⟩ : syracuseStep 1850777 = 1388083) B1388083
theorem B2776499 : Blo 1232434 2776499 := bstep (se 1 (by rfl) ⟨2082374, by rfl⟩ : syracuseStep 2776499 = 4164749) B4164749
theorem B2776535 : Blo 1232434 2776535 := bstep (se 1 (by rfl) ⟨2082401, by rfl⟩ : syracuseStep 2776535 = 4164803) B4164803
theorem B4447705 : Blo 1232434 4447705 := bstep (se 2 (by rfl) ⟨1667889, by rfl⟩ : syracuseStep 4447705 = 3335779) B3335779
theorem B1850891 : Blo 1232434 1850891 := bstep (se 1 (by rfl) ⟨1388168, by rfl⟩ : syracuseStep 1850891 = 2776337) B2776337
theorem B15810065 : Blo 1232434 15810065 := bstep (se 2 (by rfl) ⟨5928774, by rfl⟩ : syracuseStep 15810065 = 11857549) B11857549
theorem B1850903 : Blo 1232434 1850903 := bstep (se 1 (by rfl) ⟨1388177, by rfl⟩ : syracuseStep 1850903 = 2776355) B2776355
theorem B2080343 : Blo 1232434 2080343 := bstep (se 1 (by rfl) ⟨1560257, by rfl⟩ : syracuseStep 2080343 = 3120515) B3120515
theorem B1850969 : Blo 1232434 1850969 := bstep (se 2 (by rfl) ⟨694113, by rfl⟩ : syracuseStep 1850969 = 1388227) B1388227
theorem B2776715 : Blo 1232434 2776715 := bstep (se 1 (by rfl) ⟨2082536, by rfl⟩ : syracuseStep 2776715 = 4165073) B4165073
theorem B2776769 : Blo 1232434 2776769 := bstep (se 2 (by rfl) ⟨1041288, by rfl⟩ : syracuseStep 2776769 = 2082577) B2082577
theorem B90054341 : Blo 1232434 90054341 := bstep (se 4 (by rfl) ⟨8442594, by rfl⟩ : syracuseStep 90054341 = 16885189) B16885189
theorem B1851083 : Blo 1232434 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B2080471 : Blo 1232434 2080471 := bstep (se 1 (by rfl) ⟨1560353, by rfl⟩ : syracuseStep 2080471 = 3120707) B3120707
theorem B1851095 : Blo 1232434 1851095 := bstep (se 1 (by rfl) ⟨1388321, by rfl⟩ : syracuseStep 1851095 = 2776643) B2776643
theorem B2342657 : Blo 1232434 2342657 := bstep (se 2 (by rfl) ⟨878496, by rfl⟩ : syracuseStep 2342657 = 1756993) B1756993
theorem B1851161 : Blo 1232434 1851161 := bstep (se 2 (by rfl) ⟨694185, by rfl⟩ : syracuseStep 1851161 = 1388371) B1388371
theorem B4448051 : Blo 1232434 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B4685633 : Blo 1232434 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B9363275 : Blo 1232434 9363275 := bstep (se 1 (by rfl) ⟨7022456, by rfl⟩ : syracuseStep 9363275 = 14044913) B14044913
theorem B1851275 : Blo 1232434 1851275 := bstep (se 1 (by rfl) ⟨1388456, by rfl⟩ : syracuseStep 1851275 = 2776913) B2776913
theorem B1851287 : Blo 1232434 1851287 := bstep (se 1 (by rfl) ⟨1388465, by rfl⟩ : syracuseStep 1851287 = 2776931) B2776931
theorem B2776985 : Blo 1232434 2776985 := bstep (se 2 (by rfl) ⟨1041369, by rfl⟩ : syracuseStep 2776985 = 2082739) B2082739
theorem B1851353 : Blo 1232434 1851353 := bstep (se 2 (by rfl) ⟨694257, by rfl⟩ : syracuseStep 1851353 = 1388515) B1388515
theorem B2777075 : Blo 1232434 2777075 := bstep (se 1 (by rfl) ⟨2082806, by rfl⟩ : syracuseStep 2777075 = 4165613) B4165613
theorem B3121163 : Blo 1232434 3121163 := bstep (se 1 (by rfl) ⟨2340872, by rfl⟩ : syracuseStep 3121163 = 4681745) B4681745
theorem B1851407 : Blo 1232434 1851407 := bstep (se 1 (by rfl) ⟨1388555, by rfl⟩ : syracuseStep 1851407 = 2777111) B2777111
theorem B2342945 : Blo 1232434 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B2670635 : Blo 1232434 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1851449 : Blo 1232434 1851449 := bstep (se 2 (by rfl) ⟨694293, by rfl⟩ : syracuseStep 1851449 = 1388587) B1388587
theorem B2777147 : Blo 1232434 2777147 := bstep (se 1 (by rfl) ⟨2082860, by rfl⟩ : syracuseStep 2777147 = 4165721) B4165721
theorem B2080903 : Blo 1232434 2080903 := bstep (se 1 (by rfl) ⟨1560677, by rfl⟩ : syracuseStep 2080903 = 3121355) B3121355
theorem B1851527 : Blo 1232434 1851527 := bstep (se 1 (by rfl) ⟨1388645, by rfl⟩ : syracuseStep 1851527 = 2777291) B2777291
theorem B1851563 : Blo 1232434 1851563 := bstep (se 1 (by rfl) ⟨1388672, by rfl⟩ : syracuseStep 1851563 = 2777345) B2777345
theorem B2343097 : Blo 1232434 2343097 := bstep (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) B1757323
theorem B2777273 : Blo 1232434 2777273 := bstep (se 2 (by rfl) ⟨1041477, by rfl⟩ : syracuseStep 2777273 = 2082955) B2082955
theorem B1851593 : Blo 1232434 1851593 := bstep (se 2 (by rfl) ⟨694347, by rfl⟩ : syracuseStep 1851593 = 1388695) B1388695
theorem B4448513 : Blo 1232434 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B7905595 : Blo 1232434 7905595 := bstep (se 1 (by rfl) ⟨5929196, by rfl⟩ : syracuseStep 7905595 = 11858393) B11858393
theorem B5136907 : Blo 1232434 5136907 := bstep (se 1 (by rfl) ⟨3852680, by rfl⟩ : syracuseStep 5136907 = 7705361) B7705361
theorem B3121679 : Blo 1232434 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B3121811 : Blo 1232434 3121811 := bstep (se 1 (by rfl) ⟨2341358, by rfl⟩ : syracuseStep 3121811 = 4682717) B4682717
theorem B5702381 : Blo 1232434 5702381 := bstep (se 3 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 5702381 = 2138393) B2138393
theorem B3515147 : Blo 1232434 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B4162319 : Blo 1232434 4162319 := bstep (se 1 (by rfl) ⟨3121739, by rfl⟩ : syracuseStep 4162319 = 6243479) B6243479
theorem B2081551 : Blo 1232434 2081551 := bstep (se 1 (by rfl) ⟨1561163, by rfl⟩ : syracuseStep 2081551 = 3122327) B3122327
theorem B7021363 : Blo 1232434 7021363 := bstep (se 1 (by rfl) ⟨5266022, by rfl⟩ : syracuseStep 7021363 = 10532045) B10532045
theorem B1901447 : Blo 1232434 1901447 := bstep (se 1 (by rfl) ⟨1426085, by rfl⟩ : syracuseStep 1901447 = 2852171) B2852171
theorem B3752851 : Blo 1232434 3752851 := bstep (se 1 (by rfl) ⟨2814638, by rfl⟩ : syracuseStep 3752851 = 5629277) B5629277
theorem B4506553 : Blo 1232434 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B4744145 : Blo 1232434 4744145 := bstep (se 2 (by rfl) ⟨1779054, by rfl⟩ : syracuseStep 4744145 = 3558109) B3558109
theorem B4162589 : Blo 1232434 4162589 := bstep (se 3 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 4162589 = 1560971) B1560971
theorem B6669485 : Blo 1232434 6669485 := bstep (se 3 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 6669485 = 2501057) B2501057
theorem B3949825 : Blo 1232434 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B10544417 : Blo 1232434 10544417 := bstep (se 2 (by rfl) ⟨3954156, by rfl⟩ : syracuseStep 10544417 = 7908313) B7908313
theorem B2082091 : Blo 1232434 2082091 := bstep (se 1 (by rfl) ⟨1561568, by rfl⟩ : syracuseStep 2082091 = 3123137) B3123137
theorem B56935811 : Blo 1232434 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B5784979 : Blo 1232434 5784979 := bstep (se 1 (by rfl) ⟨4338734, by rfl⟩ : syracuseStep 5784979 = 8677469) B8677469
theorem B14050745 : Blo 1232434 14050745 := bstep (se 2 (by rfl) ⟨5269029, by rfl⟩ : syracuseStep 14050745 = 10538059) B10538059
theorem B2082233 : Blo 1232434 2082233 := bstep (se 2 (by rfl) ⟨780837, by rfl⟩ : syracuseStep 2082233 = 1561675) B1561675
theorem B3122945 : Blo 1232434 3122945 := bstep (se 2 (by rfl) ⟨1171104, by rfl⟩ : syracuseStep 3122945 = 2342209) B2342209
theorem B9013007 : Blo 1232434 9013007 := bstep (se 1 (by rfl) ⟨6759755, by rfl⟩ : syracuseStep 9013007 = 13519511) B13519511
theorem B3163963 : Blo 1232434 3163963 := bstep (se 1 (by rfl) ⟨2372972, by rfl⟩ : syracuseStep 3163963 = 4745945) B4745945
theorem B4679633 : Blo 1232434 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B2222095 : Blo 1232434 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B11855933 : Blo 1232434 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B3123319 : Blo 1232434 3123319 := bstep (se 1 (by rfl) ⟨2342489, by rfl⟩ : syracuseStep 3123319 = 4684979) B4684979
theorem B2082935 : Blo 1232434 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B1755307 : Blo 1232434 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B9365705 : Blo 1232434 9365705 := bstep (se 2 (by rfl) ⟨3512139, by rfl⟩ : syracuseStep 9365705 = 7024279) B7024279
theorem B7022821 : Blo 1232434 7022821 := bstep (se 4 (by rfl) ⟨658389, by rfl⟩ : syracuseStep 7022821 = 1316779) B1316779
theorem B1386895 : Blo 1232434 1386895 := bstep (se 1 (by rfl) ⟨1040171, by rfl⟩ : syracuseStep 1386895 = 2080343) B2080343
theorem B1755535 : Blo 1232434 1755535 := bstep (se 1 (by rfl) ⟨1316651, by rfl⟩ : syracuseStep 1755535 = 2633303) B2633303
theorem B9488785 : Blo 1232434 9488785 := bstep (se 2 (by rfl) ⟨3558294, by rfl⟩ : syracuseStep 9488785 = 7116589) B7116589
theorem B4680089 : Blo 1232434 4680089 := bstep (se 2 (by rfl) ⟨1755033, by rfl⟩ : syracuseStep 4680089 = 3510067) B3510067
theorem B4163993 : Blo 1232434 4163993 := bstep (se 2 (by rfl) ⟨1561497, by rfl⟩ : syracuseStep 4163993 = 3122995) B3122995
theorem B23726627 : Blo 1232434 23726627 := bstep (se 1 (by rfl) ⟨17794970, by rfl⟩ : syracuseStep 23726627 = 35589941) B35589941
theorem B3123755 : Blo 1232434 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B5630735 : Blo 1232434 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B18991907 : Blo 1232434 18991907 := bstep (se 1 (by rfl) ⟨14243930, by rfl⟩ : syracuseStep 18991907 = 28487861) B28487861
theorem B10529585 : Blo 1232434 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B1387399 : Blo 1232434 1387399 := bstep (se 1 (by rfl) ⟨1040549, by rfl⟩ : syracuseStep 1387399 = 2081099) B2081099
theorem B3951659 : Blo 1232434 3951659 := bstep (se 1 (by rfl) ⟨2963744, by rfl⟩ : syracuseStep 3951659 = 5927489) B5927489
theorem B1387579 : Blo 1232434 1387579 := bstep (se 1 (by rfl) ⟨1040684, by rfl⟩ : syracuseStep 1387579 = 2081369) B2081369
theorem B6663235 : Blo 1232434 6663235 := bstep (se 1 (by rfl) ⟨4997426, by rfl⟩ : syracuseStep 6663235 = 9994853) B9994853
theorem B4164695 : Blo 1232434 4164695 := bstep (se 1 (by rfl) ⟨3123521, by rfl⟩ : syracuseStep 4164695 = 6247043) B6247043
theorem B35540117 : Blo 1232434 35540117 := bstep (se 6 (by rfl) ⟨832971, by rfl⟩ : syracuseStep 35540117 = 1665943) B1665943
theorem B12021085 : Blo 1232434 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B6245747 : Blo 1232434 6245747 := bstep (se 1 (by rfl) ⟨4684310, by rfl⟩ : syracuseStep 6245747 = 9368621) B9368621
theorem B3124595 : Blo 1232434 3124595 := bstep (se 1 (by rfl) ⟨2343446, by rfl⟩ : syracuseStep 3124595 = 4686893) B4686893
theorem B3124615 : Blo 1232434 3124615 := bstep (se 1 (by rfl) ⟨2343461, by rfl⟩ : syracuseStep 3124615 = 4686923) B4686923
theorem B10530269 : Blo 1232434 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B1560055 : Blo 1232434 1560055 := bstep (se 1 (by rfl) ⟨1170041, by rfl⟩ : syracuseStep 1560055 = 2340083) B2340083
theorem B1388047 : Blo 1232434 1388047 := bstep (se 1 (by rfl) ⟨1041035, by rfl⟩ : syracuseStep 1388047 = 2082071) B2082071
theorem B4681259 : Blo 1232434 4681259 := bstep (se 1 (by rfl) ⟨3510944, by rfl⟩ : syracuseStep 4681259 = 7021889) B7021889
theorem B1232443 : Blo 1232434 1232443 := bstep (se 1 (by rfl) ⟨924332, by rfl⟩ : syracuseStep 1232443 = 1848665) B1848665
theorem B4165181 : Blo 1232434 4165181 := bstep (se 3 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 4165181 = 1561943) B1561943
theorem B1232519 : Blo 1232434 1232519 := bstep (se 1 (by rfl) ⟨924389, by rfl⟩ : syracuseStep 1232519 = 1848779) B1848779
theorem B1232527 : Blo 1232434 1232527 := bstep (se 1 (by rfl) ⟨924395, by rfl⟩ : syracuseStep 1232527 = 1848791) B1848791
theorem B1232571 : Blo 1232434 1232571 := bstep (se 1 (by rfl) ⟨924428, by rfl⟩ : syracuseStep 1232571 = 1848857) B1848857
theorem B5336833 : Blo 1232434 5336833 := bstep (se 2 (by rfl) ⟨2001312, by rfl⟩ : syracuseStep 5336833 = 4002625) B4002625
theorem B1232647 : Blo 1232434 1232647 := bstep (se 1 (by rfl) ⟨924485, by rfl⟩ : syracuseStep 1232647 = 1848971) B1848971
theorem B1232655 : Blo 1232434 1232655 := bstep (se 1 (by rfl) ⟨924491, by rfl⟩ : syracuseStep 1232655 = 1848983) B1848983
theorem B1232699 : Blo 1232434 1232699 := bstep (se 1 (by rfl) ⟨924524, by rfl⟩ : syracuseStep 1232699 = 1849049) B1849049
theorem B1560379 : Blo 1232434 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B6328153 : Blo 1232434 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B6246233 : Blo 1232434 6246233 := bstep (se 2 (by rfl) ⟨2342337, by rfl⟩ : syracuseStep 6246233 = 4684675) B4684675
theorem B1232775 : Blo 1232434 1232775 := bstep (se 1 (by rfl) ⟨924581, by rfl⟩ : syracuseStep 1232775 = 1849163) B1849163
theorem B1232783 : Blo 1232434 1232783 := bstep (se 1 (by rfl) ⟨924587, by rfl⟩ : syracuseStep 1232783 = 1849175) B1849175
theorem B1232827 : Blo 1232434 1232827 := bstep (se 1 (by rfl) ⟨924620, by rfl⟩ : syracuseStep 1232827 = 1849241) B1849241
theorem B1232903 : Blo 1232434 1232903 := bstep (se 1 (by rfl) ⟨924677, by rfl⟩ : syracuseStep 1232903 = 1849355) B1849355
theorem B1388551 : Blo 1232434 1388551 := bstep (se 1 (by rfl) ⟨1041413, by rfl⟩ : syracuseStep 1388551 = 2082827) B2082827
theorem B2773007 : Blo 1232434 2773007 := bstep (se 1 (by rfl) ⟨2079755, by rfl⟩ : syracuseStep 2773007 = 4159511) B4159511
theorem B1232911 : Blo 1232434 1232911 := bstep (se 1 (by rfl) ⟨924683, by rfl⟩ : syracuseStep 1232911 = 1849367) B1849367
theorem B2773025 : Blo 1232434 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B2961467 : Blo 1232434 2961467 := bstep (se 1 (by rfl) ⟨2221100, by rfl⟩ : syracuseStep 2961467 = 4442201) B4442201
theorem B1232955 : Blo 1232434 1232955 := bstep (se 1 (by rfl) ⟨924716, by rfl⟩ : syracuseStep 1232955 = 1849433) B1849433
theorem B6328381 : Blo 1232434 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B4444247 : Blo 1232434 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B2961523 : Blo 1232434 2961523 := bstep (se 1 (by rfl) ⟨2221142, by rfl⟩ : syracuseStep 2961523 = 4442285) B4442285
theorem B1233031 : Blo 1232434 1233031 := bstep (se 1 (by rfl) ⟨924773, by rfl⟩ : syracuseStep 1233031 = 1849547) B1849547
theorem B1233039 : Blo 1232434 1233039 := bstep (se 1 (by rfl) ⟨924779, by rfl⟩ : syracuseStep 1233039 = 1849559) B1849559
theorem B1233083 : Blo 1232434 1233083 := bstep (se 1 (by rfl) ⟨924812, by rfl⟩ : syracuseStep 1233083 = 1849625) B1849625
theorem B1388731 : Blo 1232434 1388731 := bstep (se 1 (by rfl) ⟨1041548, by rfl⟩ : syracuseStep 1388731 = 2083097) B2083097
theorem B4444361 : Blo 1232434 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B1233159 : Blo 1232434 1233159 := bstep (se 1 (by rfl) ⟨924869, by rfl⟩ : syracuseStep 1233159 = 1849739) B1849739
theorem B1233167 : Blo 1232434 1233167 := bstep (se 1 (by rfl) ⟨924875, by rfl⟩ : syracuseStep 1233167 = 1849751) B1849751
theorem B1233211 : Blo 1232434 1233211 := bstep (se 1 (by rfl) ⟨924908, by rfl⟩ : syracuseStep 1233211 = 1849817) B1849817
theorem B2773367 : Blo 1232434 2773367 := bstep (se 1 (by rfl) ⟨2080025, by rfl⟩ : syracuseStep 2773367 = 4160051) B4160051
theorem B1233287 : Blo 1232434 1233287 := bstep (se 1 (by rfl) ⟨924965, by rfl⟩ : syracuseStep 1233287 = 1849931) B1849931
theorem B1233295 : Blo 1232434 1233295 := bstep (se 1 (by rfl) ⟨924971, by rfl⟩ : syracuseStep 1233295 = 1849943) B1849943
theorem B1233339 : Blo 1232434 1233339 := bstep (se 1 (by rfl) ⟨925004, by rfl⟩ : syracuseStep 1233339 = 1850009) B1850009
theorem B59986403 : Blo 1232434 59986403 := bstep (se 1 (by rfl) ⟨44989802, by rfl⟩ : syracuseStep 59986403 = 89979605) B89979605
theorem B1233415 : Blo 1232434 1233415 := bstep (se 1 (by rfl) ⟨925061, by rfl⟩ : syracuseStep 1233415 = 1850123) B1850123
theorem B1233423 : Blo 1232434 1233423 := bstep (se 1 (by rfl) ⟨925067, by rfl⟩ : syracuseStep 1233423 = 1850135) B1850135
theorem B2773547 : Blo 1232434 2773547 := bstep (se 1 (by rfl) ⟨2080160, by rfl⟩ : syracuseStep 2773547 = 4160321) B4160321
theorem B1233467 : Blo 1232434 1233467 := bstep (se 1 (by rfl) ⟨925100, by rfl⟩ : syracuseStep 1233467 = 1850201) B1850201
theorem B4002365 : Blo 1232434 4002365 := bstep (se 3 (by rfl) ⟨750443, by rfl⟩ : syracuseStep 4002365 = 1500887) B1500887
theorem B1233543 : Blo 1232434 1233543 := bstep (se 1 (by rfl) ⟨925157, by rfl⟩ : syracuseStep 1233543 = 1850315) B1850315
theorem B1233551 : Blo 1232434 1233551 := bstep (se 1 (by rfl) ⟨925163, by rfl⟩ : syracuseStep 1233551 = 1850327) B1850327
theorem B1233595 : Blo 1232434 1233595 := bstep (se 1 (by rfl) ⟨925196, by rfl⟩ : syracuseStep 1233595 = 1850393) B1850393
theorem B1561351 : Blo 1232434 1561351 := bstep (se 1 (by rfl) ⟨1171013, by rfl⟩ : syracuseStep 1561351 = 2342027) B2342027
theorem B1233671 : Blo 1232434 1233671 := bstep (se 1 (by rfl) ⟨925253, by rfl⟩ : syracuseStep 1233671 = 1850507) B1850507
theorem B1233679 : Blo 1232434 1233679 := bstep (se 1 (by rfl) ⟨925259, by rfl⟩ : syracuseStep 1233679 = 1850519) B1850519
theorem B1233723 : Blo 1232434 1233723 := bstep (se 1 (by rfl) ⟨925292, by rfl⟩ : syracuseStep 1233723 = 1850585) B1850585
theorem B3511127 : Blo 1232434 3511127 := bstep (se 1 (by rfl) ⟨2633345, by rfl⟩ : syracuseStep 3511127 = 5266691) B5266691
theorem B1233799 : Blo 1232434 1233799 := bstep (se 1 (by rfl) ⟨925349, by rfl⟩ : syracuseStep 1233799 = 1850699) B1850699
theorem B1233807 : Blo 1232434 1233807 := bstep (se 1 (by rfl) ⟨925355, by rfl⟩ : syracuseStep 1233807 = 1850711) B1850711
theorem B2773907 : Blo 1232434 2773907 := bstep (se 1 (by rfl) ⟨2080430, by rfl⟩ : syracuseStep 2773907 = 4160861) B4160861
theorem B7025555 : Blo 1232434 7025555 := bstep (se 1 (by rfl) ⟨5269166, by rfl⟩ : syracuseStep 7025555 = 10538333) B10538333
theorem B53375921 : Blo 1232434 53375921 := bstep (se 2 (by rfl) ⟨20015970, by rfl⟩ : syracuseStep 53375921 = 40031941) B40031941
theorem B1233851 : Blo 1232434 1233851 := bstep (se 1 (by rfl) ⟨925388, by rfl⟩ : syracuseStep 1233851 = 1850777) B1850777
theorem B2773961 : Blo 1232434 2773961 := bstep (se 2 (by rfl) ⟨1040235, by rfl⟩ : syracuseStep 2773961 = 2080471) B2080471
theorem B1233927 : Blo 1232434 1233927 := bstep (se 1 (by rfl) ⟨925445, by rfl⟩ : syracuseStep 1233927 = 1850891) B1850891
theorem B10540043 : Blo 1232434 10540043 := bstep (se 1 (by rfl) ⟨7905032, by rfl⟩ : syracuseStep 10540043 = 15810065) B15810065
theorem B1233935 : Blo 1232434 1233935 := bstep (se 1 (by rfl) ⟨925451, by rfl⟩ : syracuseStep 1233935 = 1850903) B1850903
theorem B1233979 : Blo 1232434 1233979 := bstep (se 1 (by rfl) ⟨925484, by rfl⟩ : syracuseStep 1233979 = 1850969) B1850969
theorem B60036227 : Blo 1232434 60036227 := bstep (se 1 (by rfl) ⟨45027170, by rfl⟩ : syracuseStep 60036227 = 90054341) B90054341
theorem B1234055 : Blo 1232434 1234055 := bstep (se 1 (by rfl) ⟨925541, by rfl⟩ : syracuseStep 1234055 = 1851083) B1851083
theorem B1234063 : Blo 1232434 1234063 := bstep (se 1 (by rfl) ⟨925547, by rfl⟩ : syracuseStep 1234063 = 1851095) B1851095
theorem B1561771 : Blo 1232434 1561771 := bstep (se 1 (by rfl) ⟨1171328, by rfl⟩ : syracuseStep 1561771 = 2342657) B2342657
theorem B1234107 : Blo 1232434 1234107 := bstep (se 1 (by rfl) ⟨925580, by rfl⟩ : syracuseStep 1234107 = 1851161) B1851161
theorem B1234183 : Blo 1232434 1234183 := bstep (se 1 (by rfl) ⟨925637, by rfl⟩ : syracuseStep 1234183 = 1851275) B1851275
theorem B1234191 : Blo 1232434 1234191 := bstep (se 1 (by rfl) ⟨925643, by rfl⟩ : syracuseStep 1234191 = 1851287) B1851287
theorem B1234235 : Blo 1232434 1234235 := bstep (se 1 (by rfl) ⟨925676, by rfl⟩ : syracuseStep 1234235 = 1851353) B1851353
theorem B1848695 : Blo 1232434 1848695 := bstep (se 1 (by rfl) ⟨1386521, by rfl⟩ : syracuseStep 1848695 = 2773043) B2773043
theorem B3954055 : Blo 1232434 3954055 := bstep (se 1 (by rfl) ⟨2965541, by rfl⟩ : syracuseStep 3954055 = 5931083) B5931083
theorem B1234311 : Blo 1232434 1234311 := bstep (se 1 (by rfl) ⟨925733, by rfl⟩ : syracuseStep 1234311 = 1851467) B1851467
theorem B1848719 : Blo 1232434 1848719 := bstep (se 1 (by rfl) ⟨1386539, by rfl⟩ : syracuseStep 1848719 = 2773079) B2773079
theorem B1561999 : Blo 1232434 1561999 := bstep (se 1 (by rfl) ⟨1171499, by rfl⟩ : syracuseStep 1561999 = 2342999) B2342999
theorem B1234319 : Blo 1232434 1234319 := bstep (se 1 (by rfl) ⟨925739, by rfl⟩ : syracuseStep 1234319 = 1851479) B1851479
theorem B1848761 : Blo 1232434 1848761 := bstep (se 2 (by rfl) ⟨693285, by rfl⟩ : syracuseStep 1848761 = 1386571) B1386571
theorem B1234363 : Blo 1232434 1234363 := bstep (se 1 (by rfl) ⟨925772, by rfl⟩ : syracuseStep 1234363 = 1851545) B1851545
theorem B4683217 : Blo 1232434 4683217 := bstep (se 2 (by rfl) ⟨1756206, by rfl⟩ : syracuseStep 4683217 = 3512413) B3512413
theorem B1848839 : Blo 1232434 1848839 := bstep (se 1 (by rfl) ⟨1386629, by rfl⟩ : syracuseStep 1848839 = 2773259) B2773259
theorem B1848875 : Blo 1232434 1848875 := bstep (se 1 (by rfl) ⟨1386656, by rfl⟩ : syracuseStep 1848875 = 2773313) B2773313
theorem B1848905 : Blo 1232434 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B7026263 : Blo 1232434 7026263 := bstep (se 1 (by rfl) ⟨5269697, by rfl⟩ : syracuseStep 7026263 = 10539395) B10539395
theorem B2774663 : Blo 1232434 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B1849019 : Blo 1232434 1849019 := bstep (se 1 (by rfl) ⟨1386764, by rfl⟩ : syracuseStep 1849019 = 2773529) B2773529
theorem B16029413 : Blo 1232434 16029413 := bstep (se 4 (by rfl) ⟨1502757, by rfl⟩ : syracuseStep 16029413 = 3005515) B3005515
theorem B1849079 : Blo 1232434 1849079 := bstep (se 1 (by rfl) ⟨1386809, by rfl⟩ : syracuseStep 1849079 = 2773619) B2773619
theorem B4683521 : Blo 1232434 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B1849103 : Blo 1232434 1849103 := bstep (se 1 (by rfl) ⟨1386827, by rfl⟩ : syracuseStep 1849103 = 2773655) B2773655
theorem B1849145 : Blo 1232434 1849145 := bstep (se 2 (by rfl) ⟨693429, by rfl⟩ : syracuseStep 1849145 = 1386859) B1386859
theorem B2340667 : Blo 1232434 2340667 := bstep (se 1 (by rfl) ⟨1755500, by rfl⟩ : syracuseStep 2340667 = 3511001) B3511001
theorem B2774843 : Blo 1232434 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B3954491 : Blo 1232434 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B11851595 : Blo 1232434 11851595 := bstep (se 1 (by rfl) ⟨8888696, by rfl⟩ : syracuseStep 11851595 = 17777393) B17777393
theorem B3331975 : Blo 1232434 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B1849223 : Blo 1232434 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B6248339 : Blo 1232434 6248339 := bstep (se 1 (by rfl) ⟨4686254, by rfl⟩ : syracuseStep 6248339 = 9372509) B9372509
theorem B1849259 : Blo 1232434 1849259 := bstep (se 1 (by rfl) ⟨1386944, by rfl⟩ : syracuseStep 1849259 = 2773889) B2773889
theorem B2774969 : Blo 1232434 2774969 := bstep (se 2 (by rfl) ⟨1040613, by rfl⟩ : syracuseStep 2774969 = 2081227) B2081227
theorem B5928889 : Blo 1232434 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B1849289 : Blo 1232434 1849289 := bstep (se 2 (by rfl) ⟨693483, by rfl⟩ : syracuseStep 1849289 = 1386967) B1386967
theorem B10000331 : Blo 1232434 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B31610897 : Blo 1232434 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B1849403 : Blo 1232434 1849403 := bstep (se 1 (by rfl) ⟨1387052, by rfl⟩ : syracuseStep 1849403 = 2774105) B2774105
theorem B1849463 : Blo 1232434 1849463 := bstep (se 1 (by rfl) ⟨1387097, by rfl⟩ : syracuseStep 1849463 = 2774195) B2774195
theorem B2963591 : Blo 1232434 2963591 := bstep (se 1 (by rfl) ⟨2222693, by rfl⟩ : syracuseStep 2963591 = 4445387) B4445387
theorem B1849487 : Blo 1232434 1849487 := bstep (se 1 (by rfl) ⟨1387115, by rfl⟩ : syracuseStep 1849487 = 2774231) B2774231
theorem B1849529 : Blo 1232434 1849529 := bstep (se 2 (by rfl) ⟨693573, by rfl⟩ : syracuseStep 1849529 = 1387147) B1387147
theorem B2668745 : Blo 1232434 2668745 := bstep (se 2 (by rfl) ⟨1000779, by rfl⟩ : syracuseStep 2668745 = 2001559) B2001559
theorem B4683977 : Blo 1232434 4683977 := bstep (se 2 (by rfl) ⟨1756491, by rfl⟩ : syracuseStep 4683977 = 3512983) B3512983
theorem B1849607 : Blo 1232434 1849607 := bstep (se 1 (by rfl) ⟨1387205, by rfl⟩ : syracuseStep 1849607 = 2774411) B2774411
theorem B2775311 : Blo 1232434 2775311 := bstep (se 1 (by rfl) ⟨2081483, by rfl⟩ : syracuseStep 2775311 = 4162967) B4162967
theorem B2341153 : Blo 1232434 2341153 := bstep (se 2 (by rfl) ⟨877932, by rfl⟩ : syracuseStep 2341153 = 1755865) B1755865
theorem B2775329 : Blo 1232434 2775329 := bstep (se 2 (by rfl) ⟨1040748, by rfl⟩ : syracuseStep 2775329 = 2081497) B2081497
theorem B1849643 : Blo 1232434 1849643 := bstep (se 1 (by rfl) ⟨1387232, by rfl⟩ : syracuseStep 1849643 = 2774465) B2774465
theorem B6240563 : Blo 1232434 6240563 := bstep (se 1 (by rfl) ⟨4680422, by rfl⟩ : syracuseStep 6240563 = 9360845) B9360845
theorem B1849673 : Blo 1232434 1849673 := bstep (se 2 (by rfl) ⟨693627, by rfl⟩ : syracuseStep 1849673 = 1387255) B1387255
theorem B1849787 : Blo 1232434 1849787 := bstep (se 1 (by rfl) ⟨1387340, by rfl⟩ : syracuseStep 1849787 = 2774681) B2774681
theorem B1849847 : Blo 1232434 1849847 := bstep (se 1 (by rfl) ⟨1387385, by rfl⟩ : syracuseStep 1849847 = 2774771) B2774771
theorem B1849871 : Blo 1232434 1849871 := bstep (se 1 (by rfl) ⟨1387403, by rfl⟩ : syracuseStep 1849871 = 2774807) B2774807
theorem B1849913 : Blo 1232434 1849913 := bstep (se 2 (by rfl) ⟨693717, by rfl⟩ : syracuseStep 1849913 = 1387435) B1387435
theorem B11246147 : Blo 1232434 11246147 := bstep (se 1 (by rfl) ⟨8434610, by rfl⟩ : syracuseStep 11246147 = 16869221) B16869221
theorem B3119735 : Blo 1232434 3119735 := bstep (se 1 (by rfl) ⟨2339801, by rfl⟩ : syracuseStep 3119735 = 4679603) B4679603
theorem B6240887 : Blo 1232434 6240887 := bstep (se 1 (by rfl) ⟨4680665, by rfl⟩ : syracuseStep 6240887 = 9361331) B9361331
theorem B2775671 : Blo 1232434 2775671 := bstep (se 1 (by rfl) ⟨2081753, by rfl⟩ : syracuseStep 2775671 = 4163507) B4163507
theorem B1849991 : Blo 1232434 1849991 := bstep (se 1 (by rfl) ⟨1387493, by rfl⟩ : syracuseStep 1849991 = 2774987) B2774987
theorem B1850027 : Blo 1232434 1850027 := bstep (se 1 (by rfl) ⟨1387520, by rfl⟩ : syracuseStep 1850027 = 2775041) B2775041
theorem B1850057 : Blo 1232434 1850057 := bstep (se 2 (by rfl) ⟨693771, by rfl⟩ : syracuseStep 1850057 = 1387543) B1387543
theorem B2775851 : Blo 1232434 2775851 := bstep (se 1 (by rfl) ⟨2081888, by rfl⟩ : syracuseStep 2775851 = 4163777) B4163777
theorem B1874747 : Blo 1232434 1874747 := bstep (se 1 (by rfl) ⟨1406060, by rfl⟩ : syracuseStep 1874747 = 2812121) B2812121
theorem B1850171 : Blo 1232434 1850171 := bstep (se 1 (by rfl) ⟨1387628, by rfl⟩ : syracuseStep 1850171 = 2775257) B2775257
theorem B1850231 : Blo 1232434 1850231 := bstep (se 1 (by rfl) ⟨1387673, by rfl⟩ : syracuseStep 1850231 = 2775347) B2775347
theorem B1850255 : Blo 1232434 1850255 := bstep (se 1 (by rfl) ⟨1387691, by rfl⟩ : syracuseStep 1850255 = 2775383) B2775383
theorem B3562393 : Blo 1232434 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B1850297 : Blo 1232434 1850297 := bstep (se 2 (by rfl) ⟨693861, by rfl⟩ : syracuseStep 1850297 = 1387723) B1387723
theorem B3750857 : Blo 1232434 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B5929949 : Blo 1232434 5929949 := bstep (se 3 (by rfl) ⟨1111865, by rfl⟩ : syracuseStep 5929949 = 2223731) B2223731
theorem B1850375 : Blo 1232434 1850375 := bstep (se 1 (by rfl) ⟨1387781, by rfl⟩ : syracuseStep 1850375 = 2775563) B2775563
theorem B1850411 : Blo 1232434 1850411 := bstep (se 1 (by rfl) ⟨1387808, by rfl⟩ : syracuseStep 1850411 = 2775617) B2775617
theorem B2079803 : Blo 1232434 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B5340227 : Blo 1232434 5340227 := bstep (se 1 (by rfl) ⟨4005170, by rfl⟩ : syracuseStep 5340227 = 8010341) B8010341
theorem B1850441 : Blo 1232434 1850441 := bstep (se 2 (by rfl) ⟨693915, by rfl⟩ : syracuseStep 1850441 = 1387831) B1387831
theorem B2776211 : Blo 1232434 2776211 := bstep (se 1 (by rfl) ⟨2082158, by rfl⟩ : syracuseStep 2776211 = 4164317) B4164317
theorem B1850555 : Blo 1232434 1850555 := bstep (se 1 (by rfl) ⟨1387916, by rfl⟩ : syracuseStep 1850555 = 2775833) B2775833
theorem B2776265 : Blo 1232434 2776265 := bstep (se 2 (by rfl) ⟨1041099, by rfl⟩ : syracuseStep 2776265 = 2082199) B2082199
theorem B1850615 : Blo 1232434 1850615 := bstep (se 1 (by rfl) ⟨1387961, by rfl⟩ : syracuseStep 1850615 = 2775923) B2775923
theorem B1850639 : Blo 1232434 1850639 := bstep (se 1 (by rfl) ⟨1387979, by rfl⟩ : syracuseStep 1850639 = 2775959) B2775959
theorem B5930273 : Blo 1232434 5930273 := bstep (se 2 (by rfl) ⟨2223852, by rfl⟩ : syracuseStep 5930273 = 4447705) B4447705
theorem B1850681 : Blo 1232434 1850681 := bstep (se 2 (by rfl) ⟨694005, by rfl⟩ : syracuseStep 1850681 = 1388011) B1388011
theorem B38493539 : Blo 1232434 38493539 := bstep (se 1 (by rfl) ⟨28870154, by rfl⟩ : syracuseStep 38493539 = 57740309) B57740309
theorem B1850759 : Blo 1232434 1850759 := bstep (se 1 (by rfl) ⟨1388069, by rfl⟩ : syracuseStep 1850759 = 2776139) B2776139
theorem B4160915 : Blo 1232434 4160915 := bstep (se 1 (by rfl) ⟨3120686, by rfl⟩ : syracuseStep 4160915 = 6241373) B6241373
theorem B1850795 : Blo 1232434 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B17776057 : Blo 1232434 17776057 := bstep (se 2 (by rfl) ⟨6666021, by rfl⟩ : syracuseStep 17776057 = 13332043) B13332043
theorem B7028153 : Blo 1232434 7028153 := bstep (se 2 (by rfl) ⟨2635557, by rfl⟩ : syracuseStep 7028153 = 5271115) B5271115
theorem B2080201 : Blo 1232434 2080201 := bstep (se 2 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 2080201 = 1560151) B1560151
theorem B1850825 : Blo 1232434 1850825 := bstep (se 2 (by rfl) ⟨694059, by rfl⟩ : syracuseStep 1850825 = 1388119) B1388119
theorem B3513871 : Blo 1232434 3513871 := bstep (se 1 (by rfl) ⟨2635403, by rfl⟩ : syracuseStep 3513871 = 5270807) B5270807
theorem B2342459 : Blo 1232434 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B1850939 : Blo 1232434 1850939 := bstep (se 1 (by rfl) ⟨1388204, by rfl⟩ : syracuseStep 1850939 = 2776409) B2776409
theorem B3513917 : Blo 1232434 3513917 := bstep (se 3 (by rfl) ⟨658859, by rfl⟩ : syracuseStep 3513917 = 1317719) B1317719
theorem B6241859 : Blo 1232434 6241859 := bstep (se 1 (by rfl) ⟨4681394, by rfl⟩ : syracuseStep 6241859 = 9362789) B9362789
theorem B3120727 : Blo 1232434 3120727 := bstep (se 1 (by rfl) ⟨2340545, by rfl⟩ : syracuseStep 3120727 = 4681091) B4681091
theorem B1850999 : Blo 1232434 1850999 := bstep (se 1 (by rfl) ⟨1388249, by rfl⟩ : syracuseStep 1850999 = 2776499) B2776499
theorem B1851023 : Blo 1232434 1851023 := bstep (se 1 (by rfl) ⟨1388267, by rfl⟩ : syracuseStep 1851023 = 2776535) B2776535
theorem B1851065 : Blo 1232434 1851065 := bstep (se 2 (by rfl) ⟨694149, by rfl⟩ : syracuseStep 1851065 = 1388299) B1388299
theorem B1875719 : Blo 1232434 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B1851143 : Blo 1232434 1851143 := bstep (se 1 (by rfl) ⟨1388357, by rfl⟩ : syracuseStep 1851143 = 2776715) B2776715
theorem B3333899 : Blo 1232434 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B1482511 : Blo 1232434 1482511 := bstep (se 1 (by rfl) ⟨1111883, by rfl⟩ : syracuseStep 1482511 = 2223767) B2223767
theorem B1851179 : Blo 1232434 1851179 := bstep (se 1 (by rfl) ⟨1388384, by rfl⟩ : syracuseStep 1851179 = 2776769) B2776769
theorem B1851209 : Blo 1232434 1851209 := bstep (se 2 (by rfl) ⟨694203, by rfl⟩ : syracuseStep 1851209 = 1388407) B1388407
theorem B2965367 : Blo 1232434 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B3121031 : Blo 1232434 3121031 := bstep (se 1 (by rfl) ⟨2340773, by rfl⟩ : syracuseStep 3121031 = 4681547) B4681547
theorem B6242183 : Blo 1232434 6242183 := bstep (se 1 (by rfl) ⟨4681637, by rfl⟩ : syracuseStep 6242183 = 9363275) B9363275
theorem B2776967 : Blo 1232434 2776967 := bstep (se 1 (by rfl) ⟨2082725, by rfl⟩ : syracuseStep 2776967 = 4165451) B4165451
theorem B3514259 : Blo 1232434 3514259 := bstep (se 1 (by rfl) ⟨2635694, by rfl⟩ : syracuseStep 3514259 = 5271389) B5271389
theorem B4448153 : Blo 1232434 4448153 := bstep (se 2 (by rfl) ⟨1668057, by rfl⟩ : syracuseStep 4448153 = 3336115) B3336115
theorem B1851323 : Blo 1232434 1851323 := bstep (se 1 (by rfl) ⟨1388492, by rfl⟩ : syracuseStep 1851323 = 2776985) B2776985
theorem B1851383 : Blo 1232434 1851383 := bstep (se 1 (by rfl) ⟨1388537, by rfl⟩ : syracuseStep 1851383 = 2777075) B2777075
theorem B2080775 : Blo 1232434 2080775 := bstep (se 1 (by rfl) ⟨1560581, by rfl⟩ : syracuseStep 2080775 = 3121163) B3121163
theorem B1851401 : Blo 1232434 1851401 := bstep (se 2 (by rfl) ⟨694275, by rfl⟩ : syracuseStep 1851401 = 1388551) B1388551
theorem B1974311 : Blo 1232434 1974311 := bstep (se 1 (by rfl) ⟨1480733, by rfl⟩ : syracuseStep 1974311 = 2961467) B2961467
theorem B1851431 : Blo 1232434 1851431 := bstep (se 1 (by rfl) ⟨1388573, by rfl⟩ : syracuseStep 1851431 = 2777147) B2777147
theorem B8437841 : Blo 1232434 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B1851515 : Blo 1232434 1851515 := bstep (se 1 (by rfl) ⟨1388636, by rfl⟩ : syracuseStep 1851515 = 2777273) B2777273
theorem B3948697 : Blo 1232434 3948697 := bstep (se 2 (by rfl) ⟨1480761, by rfl⟩ : syracuseStep 3948697 = 2961523) B2961523
theorem B2965675 : Blo 1232434 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B1851641 : Blo 1232434 1851641 := bstep (se 2 (by rfl) ⟨694365, by rfl⟩ : syracuseStep 1851641 = 1388731) B1388731
theorem B9363761 : Blo 1232434 9363761 := bstep (se 2 (by rfl) ⟨3511410, by rfl⟩ : syracuseStep 9363761 = 7022821) B7022821
theorem B2081119 : Blo 1232434 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B3121537 : Blo 1232434 3121537 := bstep (se 2 (by rfl) ⟨1170576, by rfl⟩ : syracuseStep 3121537 = 2341153) B2341153
theorem B2081207 : Blo 1232434 2081207 := bstep (se 1 (by rfl) ⟨1560905, by rfl⟩ : syracuseStep 2081207 = 3121811) B3121811
theorem B3801587 : Blo 1232434 3801587 := bstep (se 1 (by rfl) ⟨2851190, by rfl⟩ : syracuseStep 3801587 = 5702381) B5702381
theorem B2343431 : Blo 1232434 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B3162763 : Blo 1232434 3162763 := bstep (se 1 (by rfl) ⟨2372072, by rfl⟩ : syracuseStep 3162763 = 4744145) B4744145
theorem B6849209 : Blo 1232434 6849209 := bstep (se 2 (by rfl) ⟨2568453, by rfl⟩ : syracuseStep 6849209 = 5136907) B5136907
theorem B7029611 : Blo 1232434 7029611 := bstep (se 1 (by rfl) ⟨5272208, by rfl⟩ : syracuseStep 7029611 = 10544417) B10544417
theorem B2081801 : Blo 1232434 2081801 := bstep (se 2 (by rfl) ⟨780675, by rfl⟩ : syracuseStep 2081801 = 1561351) B1561351
theorem B3122347 : Blo 1232434 3122347 := bstep (se 1 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 3122347 = 4683521) B4683521
theorem B2081963 : Blo 1232434 2081963 := bstep (se 1 (by rfl) ⟨1561472, by rfl⟩ : syracuseStep 2081963 = 3122945) B3122945
theorem B1975727 : Blo 1232434 1975727 := bstep (se 1 (by rfl) ⟨1481795, by rfl⟩ : syracuseStep 1975727 = 2963591) B2963591
theorem B1779163 : Blo 1232434 1779163 := bstep (se 1 (by rfl) ⟨1334372, by rfl⟩ : syracuseStep 1779163 = 2668745) B2668745
theorem B6243803 : Blo 1232434 6243803 := bstep (se 1 (by rfl) ⟨4682852, by rfl⟩ : syracuseStep 6243803 = 9365705) B9365705
theorem B3122651 : Blo 1232434 3122651 := bstep (se 1 (by rfl) ⟨2341988, by rfl⟩ : syracuseStep 3122651 = 4683977) B4683977
theorem B2082361 : Blo 1232434 2082361 := bstep (se 2 (by rfl) ⟨780885, by rfl⟩ : syracuseStep 2082361 = 1561771) B1561771
theorem B2082503 : Blo 1232434 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B7497431 : Blo 1232434 7497431 := bstep (se 1 (by rfl) ⟨5623073, by rfl⟩ : syracuseStep 7497431 = 11246147) B11246147
theorem B3753823 : Blo 1232434 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B2082665 : Blo 1232434 2082665 := bstep (se 2 (by rfl) ⟨780999, by rfl⟩ : syracuseStep 2082665 = 1561999) B1561999
theorem B23701409 : Blo 1232434 23701409 := bstep (se 2 (by rfl) ⟨8888028, by rfl⟩ : syracuseStep 23701409 = 17776057) B17776057
theorem B6244289 : Blo 1232434 6244289 := bstep (se 2 (by rfl) ⟨2341608, by rfl⟩ : syracuseStep 6244289 = 4683217) B4683217
theorem B2500571 : Blo 1232434 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B8890397 : Blo 1232434 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B1386535 : Blo 1232434 1386535 := bstep (se 1 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 1386535 = 2079803) B2079803
theorem B23693411 : Blo 1232434 23693411 := bstep (se 1 (by rfl) ⟨17770058, by rfl⟩ : syracuseStep 23693411 = 35540117) B35540117
theorem B4163831 : Blo 1232434 4163831 := bstep (se 1 (by rfl) ⟨3122873, by rfl⟩ : syracuseStep 4163831 = 6245747) B6245747
theorem B2083063 : Blo 1232434 2083063 := bstep (se 1 (by rfl) ⟨1562297, by rfl⟩ : syracuseStep 2083063 = 3124595) B3124595
theorem B7907645 : Blo 1232434 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B1976681 : Blo 1232434 1976681 := bstep (se 2 (by rfl) ⟨741255, by rfl⟩ : syracuseStep 1976681 = 1482511) B1482511
theorem B4442633 : Blo 1232434 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B4164155 : Blo 1232434 4164155 := bstep (se 1 (by rfl) ⟨3123116, by rfl⟩ : syracuseStep 4164155 = 6246233) B6246233
theorem B1780423 : Blo 1232434 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B4164425 : Blo 1232434 4164425 := bstep (se 2 (by rfl) ⟨1561659, by rfl⟩ : syracuseStep 4164425 = 3123319) B3123319
theorem B14240605 : Blo 1232434 14240605 := bstep (se 3 (by rfl) ⟨2670113, by rfl⟩ : syracuseStep 14240605 = 5340227) B5340227
theorem B3124129 : Blo 1232434 3124129 := bstep (se 2 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 3124129 = 2343097) B2343097
theorem B81128405 : Blo 1232434 81128405 := bstep (se 7 (by rfl) ⟨950723, by rfl⟩ : syracuseStep 81128405 = 1901447) B1901447
theorem B12651713 : Blo 1232434 12651713 := bstep (se 2 (by rfl) ⟨4744392, by rfl⟩ : syracuseStep 12651713 = 9488785) B9488785
theorem B15814061 : Blo 1232434 15814061 := bstep (se 3 (by rfl) ⟨2965136, by rfl⟩ : syracuseStep 15814061 = 5930273) B5930273
theorem B1232463 : Blo 1232434 1232463 := bstep (se 1 (by rfl) ⟨924347, by rfl⟩ : syracuseStep 1232463 = 1848695) B1848695
theorem B37957207 : Blo 1232434 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B1232479 : Blo 1232434 1232479 := bstep (se 1 (by rfl) ⟨924359, by rfl⟩ : syracuseStep 1232479 = 1848719) B1848719
theorem B1232507 : Blo 1232434 1232507 := bstep (se 1 (by rfl) ⟨924380, by rfl⟩ : syracuseStep 1232507 = 1848761) B1848761
theorem B9367163 : Blo 1232434 9367163 := bstep (se 1 (by rfl) ⟨7025372, by rfl⟩ : syracuseStep 9367163 = 14050745) B14050745
theorem B1388155 : Blo 1232434 1388155 := bstep (se 1 (by rfl) ⟨1041116, by rfl⟩ : syracuseStep 1388155 = 2082233) B2082233
theorem B1232559 : Blo 1232434 1232559 := bstep (se 1 (by rfl) ⟨924419, by rfl⟩ : syracuseStep 1232559 = 1848839) B1848839
theorem B1232583 : Blo 1232434 1232583 := bstep (se 1 (by rfl) ⟨924437, by rfl⟩ : syracuseStep 1232583 = 1848875) B1848875
theorem B1232603 : Blo 1232434 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B1232679 : Blo 1232434 1232679 := bstep (se 1 (by rfl) ⟨924509, by rfl⟩ : syracuseStep 1232679 = 1849019) B1849019
theorem B10686275 : Blo 1232434 10686275 := bstep (se 1 (by rfl) ⟨8014706, by rfl⟩ : syracuseStep 10686275 = 16029413) B16029413
theorem B1232719 : Blo 1232434 1232719 := bstep (se 1 (by rfl) ⟨924539, by rfl⟩ : syracuseStep 1232719 = 1849079) B1849079
theorem B1232735 : Blo 1232434 1232735 := bstep (se 1 (by rfl) ⟨924551, by rfl⟩ : syracuseStep 1232735 = 1849103) B1849103
theorem B6008671 : Blo 1232434 6008671 := bstep (se 1 (by rfl) ⟨4506503, by rfl⟩ : syracuseStep 6008671 = 9013007) B9013007
theorem B1232763 : Blo 1232434 1232763 := bstep (se 1 (by rfl) ⟨924572, by rfl⟩ : syracuseStep 1232763 = 1849145) B1849145
theorem B7901063 : Blo 1232434 7901063 := bstep (se 1 (by rfl) ⟨5925797, by rfl⟩ : syracuseStep 7901063 = 11851595) B11851595
theorem B6008737 : Blo 1232434 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B1232815 : Blo 1232434 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B4165559 : Blo 1232434 4165559 := bstep (se 1 (by rfl) ⟨3124169, by rfl⟩ : syracuseStep 4165559 = 6248339) B6248339
theorem B1232839 : Blo 1232434 1232839 := bstep (se 1 (by rfl) ⟨924629, by rfl⟩ : syracuseStep 1232839 = 1849259) B1849259
theorem B1232859 : Blo 1232434 1232859 := bstep (se 1 (by rfl) ⟨924644, by rfl⟩ : syracuseStep 1232859 = 1849289) B1849289
theorem B21073931 : Blo 1232434 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B1232935 : Blo 1232434 1232935 := bstep (se 1 (by rfl) ⟨924701, by rfl⟩ : syracuseStep 1232935 = 1849403) B1849403
theorem B1232975 : Blo 1232434 1232975 := bstep (se 1 (by rfl) ⟨924731, by rfl⟩ : syracuseStep 1232975 = 1849463) B1849463
theorem B1388623 : Blo 1232434 1388623 := bstep (se 1 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 1388623 = 2082935) B2082935
theorem B8884313 : Blo 1232434 8884313 := bstep (se 2 (by rfl) ⟨3331617, by rfl⟩ : syracuseStep 8884313 = 6663235) B6663235
theorem B1232991 : Blo 1232434 1232991 := bstep (se 1 (by rfl) ⟨924743, by rfl⟩ : syracuseStep 1232991 = 1849487) B1849487
theorem B1233019 : Blo 1232434 1233019 := bstep (se 1 (by rfl) ⟨924764, by rfl⟩ : syracuseStep 1233019 = 1849529) B1849529
theorem B6246557 : Blo 1232434 6246557 := bstep (se 3 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 6246557 = 2342459) B2342459
theorem B1233071 : Blo 1232434 1233071 := bstep (se 1 (by rfl) ⟨924803, by rfl⟩ : syracuseStep 1233071 = 1849607) B1849607
theorem B1233095 : Blo 1232434 1233095 := bstep (se 1 (by rfl) ⟨924821, by rfl⟩ : syracuseStep 1233095 = 1849643) B1849643
theorem B1233115 : Blo 1232434 1233115 := bstep (se 1 (by rfl) ⟨924836, by rfl⟩ : syracuseStep 1233115 = 1849673) B1849673
theorem B1233191 : Blo 1232434 1233191 := bstep (se 1 (by rfl) ⟨924893, by rfl⟩ : syracuseStep 1233191 = 1849787) B1849787
theorem B1233231 : Blo 1232434 1233231 := bstep (se 1 (by rfl) ⟨924923, by rfl⟩ : syracuseStep 1233231 = 1849847) B1849847
theorem B1233247 : Blo 1232434 1233247 := bstep (se 1 (by rfl) ⟨924935, by rfl⟩ : syracuseStep 1233247 = 1849871) B1849871
theorem B1233275 : Blo 1232434 1233275 := bstep (se 1 (by rfl) ⟨924956, by rfl⟩ : syracuseStep 1233275 = 1849913) B1849913
theorem B1233327 : Blo 1232434 1233327 := bstep (se 1 (by rfl) ⟨924995, by rfl⟩ : syracuseStep 1233327 = 1849991) B1849991
theorem B1233351 : Blo 1232434 1233351 := bstep (se 1 (by rfl) ⟨925013, by rfl⟩ : syracuseStep 1233351 = 1850027) B1850027
theorem B16028113 : Blo 1232434 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B1233371 : Blo 1232434 1233371 := bstep (se 1 (by rfl) ⟨925028, by rfl⟩ : syracuseStep 1233371 = 1850057) B1850057
theorem B5272073 : Blo 1232434 5272073 := bstep (se 2 (by rfl) ⟨1977027, by rfl⟩ : syracuseStep 5272073 = 3954055) B3954055
theorem B4166153 : Blo 1232434 4166153 := bstep (se 2 (by rfl) ⟨1562307, by rfl⟩ : syracuseStep 4166153 = 3124615) B3124615
theorem B12661271 : Blo 1232434 12661271 := bstep (se 1 (by rfl) ⟨9495953, by rfl⟩ : syracuseStep 12661271 = 18991907) B18991907
theorem B7713305 : Blo 1232434 7713305 := bstep (se 2 (by rfl) ⟨2892489, by rfl⟩ : syracuseStep 7713305 = 5784979) B5784979
theorem B1249831 : Blo 1232434 1249831 := bstep (se 1 (by rfl) ⟨937373, by rfl⟩ : syracuseStep 1249831 = 1874747) B1874747
theorem B1233447 : Blo 1232434 1233447 := bstep (se 1 (by rfl) ⟨925085, by rfl⟩ : syracuseStep 1233447 = 1850171) B1850171
theorem B1233487 : Blo 1232434 1233487 := bstep (se 1 (by rfl) ⟨925115, by rfl⟩ : syracuseStep 1233487 = 1850231) B1850231
theorem B1233503 : Blo 1232434 1233503 := bstep (se 1 (by rfl) ⟨925127, by rfl⟩ : syracuseStep 1233503 = 1850255) B1850255
theorem B2773601 : Blo 1232434 2773601 := bstep (se 2 (by rfl) ⟨1040100, by rfl⟩ : syracuseStep 2773601 = 2080201) B2080201
theorem B1233531 : Blo 1232434 1233531 := bstep (se 1 (by rfl) ⟨925148, by rfl⟩ : syracuseStep 1233531 = 1850297) B1850297
theorem B3953299 : Blo 1232434 3953299 := bstep (se 1 (by rfl) ⟨2964974, by rfl⟩ : syracuseStep 3953299 = 5929949) B5929949
theorem B1233583 : Blo 1232434 1233583 := bstep (se 1 (by rfl) ⟨925187, by rfl⟩ : syracuseStep 1233583 = 1850375) B1850375
theorem B5001917 : Blo 1232434 5001917 := bstep (se 3 (by rfl) ⟨937859, by rfl⟩ : syracuseStep 5001917 = 1875719) B1875719
theorem B2634439 : Blo 1232434 2634439 := bstep (se 1 (by rfl) ⟨1975829, by rfl⟩ : syracuseStep 2634439 = 3951659) B3951659
theorem B1233607 : Blo 1232434 1233607 := bstep (se 1 (by rfl) ⟨925205, by rfl⟩ : syracuseStep 1233607 = 1850411) B1850411
theorem B1233627 : Blo 1232434 1233627 := bstep (se 1 (by rfl) ⟨925220, by rfl⟩ : syracuseStep 1233627 = 1850441) B1850441
theorem B1233703 : Blo 1232434 1233703 := bstep (se 1 (by rfl) ⟨925277, by rfl⟩ : syracuseStep 1233703 = 1850555) B1850555
theorem B1233743 : Blo 1232434 1233743 := bstep (se 1 (by rfl) ⟨925307, by rfl⟩ : syracuseStep 1233743 = 1850615) B1850615
theorem B1233759 : Blo 1232434 1233759 := bstep (se 1 (by rfl) ⟨925319, by rfl⟩ : syracuseStep 1233759 = 1850639) B1850639
theorem B1233787 : Blo 1232434 1233787 := bstep (se 1 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 1233787 = 1850681) B1850681
theorem B25662359 : Blo 1232434 25662359 := bstep (se 1 (by rfl) ⟨19246769, by rfl⟩ : syracuseStep 25662359 = 38493539) B38493539
theorem B1233839 : Blo 1232434 1233839 := bstep (se 1 (by rfl) ⟨925379, by rfl⟩ : syracuseStep 1233839 = 1850759) B1850759
theorem B2773943 : Blo 1232434 2773943 := bstep (se 1 (by rfl) ⟨2080457, by rfl⟩ : syracuseStep 2773943 = 4160915) B4160915
theorem B1233863 : Blo 1232434 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B1233883 : Blo 1232434 1233883 := bstep (se 1 (by rfl) ⟨925412, by rfl⟩ : syracuseStep 1233883 = 1850825) B1850825
theorem B7115777 : Blo 1232434 7115777 := bstep (se 2 (by rfl) ⟨2668416, by rfl⟩ : syracuseStep 7115777 = 5336833) B5336833
theorem B1233959 : Blo 1232434 1233959 := bstep (se 1 (by rfl) ⟨925469, by rfl⟩ : syracuseStep 1233959 = 1850939) B1850939
theorem B1233999 : Blo 1232434 1233999 := bstep (se 1 (by rfl) ⟨925499, by rfl⟩ : syracuseStep 1233999 = 1850999) B1850999
theorem B1234015 : Blo 1232434 1234015 := bstep (se 1 (by rfl) ⟨925511, by rfl⟩ : syracuseStep 1234015 = 1851023) B1851023
theorem B1234043 : Blo 1232434 1234043 := bstep (se 1 (by rfl) ⟨925532, by rfl⟩ : syracuseStep 1234043 = 1851065) B1851065
theorem B1234095 : Blo 1232434 1234095 := bstep (se 1 (by rfl) ⟨925571, by rfl⟩ : syracuseStep 1234095 = 1851143) B1851143
theorem B1234119 : Blo 1232434 1234119 := bstep (se 1 (by rfl) ⟨925589, by rfl⟩ : syracuseStep 1234119 = 1851179) B1851179
theorem B1234139 : Blo 1232434 1234139 := bstep (se 1 (by rfl) ⟨925604, by rfl⟩ : syracuseStep 1234139 = 1851209) B1851209
theorem B1234215 : Blo 1232434 1234215 := bstep (se 1 (by rfl) ⟨925661, by rfl⟩ : syracuseStep 1234215 = 1851323) B1851323
theorem B1234255 : Blo 1232434 1234255 := bstep (se 1 (by rfl) ⟨925691, by rfl⟩ : syracuseStep 1234255 = 1851383) B1851383
theorem B1848671 : Blo 1232434 1848671 := bstep (se 1 (by rfl) ⟨1386503, by rfl⟩ : syracuseStep 1848671 = 2773007) B2773007
theorem B1234271 : Blo 1232434 1234271 := bstep (se 1 (by rfl) ⟨925703, by rfl⟩ : syracuseStep 1234271 = 1851407) B1851407
theorem B2962793 : Blo 1232434 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1848683 : Blo 1232434 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B1234299 : Blo 1232434 1234299 := bstep (se 1 (by rfl) ⟨925724, by rfl⟩ : syracuseStep 1234299 = 1851449) B1851449
theorem B2962831 : Blo 1232434 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B6247853 : Blo 1232434 6247853 := bstep (se 3 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 6247853 = 2342945) B2342945
theorem B1234351 : Blo 1232434 1234351 := bstep (se 1 (by rfl) ⟨925763, by rfl⟩ : syracuseStep 1234351 = 1851527) B1851527
theorem B1234375 : Blo 1232434 1234375 := bstep (se 1 (by rfl) ⟨925781, by rfl⟩ : syracuseStep 1234375 = 1851563) B1851563
theorem B2962907 : Blo 1232434 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B1234395 : Blo 1232434 1234395 := bstep (se 1 (by rfl) ⟨925796, by rfl⟩ : syracuseStep 1234395 = 1851593) B1851593
theorem B2774537 : Blo 1232434 2774537 := bstep (se 2 (by rfl) ⟨1040451, by rfl⟩ : syracuseStep 2774537 = 2080903) B2080903
theorem B2340409 : Blo 1232434 2340409 := bstep (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) B1755307
theorem B1848911 : Blo 1232434 1848911 := bstep (se 1 (by rfl) ⟨1386683, by rfl⟩ : syracuseStep 1848911 = 2773367) B2773367
theorem B39990935 : Blo 1232434 39990935 := bstep (se 1 (by rfl) ⟨29993201, by rfl⟩ : syracuseStep 39990935 = 59986403) B59986403
theorem B1849031 : Blo 1232434 1849031 := bstep (se 1 (by rfl) ⟨1386773, by rfl⟩ : syracuseStep 1849031 = 2773547) B2773547
theorem B2668243 : Blo 1232434 2668243 := bstep (se 1 (by rfl) ⟨2001182, by rfl⟩ : syracuseStep 2668243 = 4002365) B4002365
theorem B10540793 : Blo 1232434 10540793 := bstep (se 2 (by rfl) ⟨3952797, by rfl⟩ : syracuseStep 10540793 = 7905595) B7905595
theorem B2774879 : Blo 1232434 2774879 := bstep (se 1 (by rfl) ⟨2081159, by rfl⟩ : syracuseStep 2774879 = 4162319) B4162319
theorem B1849193 : Blo 1232434 1849193 := bstep (se 2 (by rfl) ⟨693447, by rfl⟩ : syracuseStep 1849193 = 1386895) B1386895
theorem B2340713 : Blo 1232434 2340713 := bstep (se 2 (by rfl) ⟨877767, by rfl⟩ : syracuseStep 2340713 = 1755535) B1755535
theorem B2340751 : Blo 1232434 2340751 := bstep (se 1 (by rfl) ⟨1755563, by rfl⟩ : syracuseStep 2340751 = 3511127) B3511127
theorem B1849271 : Blo 1232434 1849271 := bstep (se 1 (by rfl) ⟨1386953, by rfl⟩ : syracuseStep 1849271 = 2773907) B2773907
theorem B4683703 : Blo 1232434 4683703 := bstep (se 1 (by rfl) ⟨3512777, by rfl⟩ : syracuseStep 4683703 = 7025555) B7025555
theorem B35583947 : Blo 1232434 35583947 := bstep (se 1 (by rfl) ⟨26687960, by rfl⟩ : syracuseStep 35583947 = 53375921) B53375921
theorem B1849307 : Blo 1232434 1849307 := bstep (se 1 (by rfl) ⟨1386980, by rfl⟩ : syracuseStep 1849307 = 2773961) B2773961
theorem B7026695 : Blo 1232434 7026695 := bstep (se 1 (by rfl) ⟨5270021, by rfl⟩ : syracuseStep 7026695 = 10540043) B10540043
theorem B2775059 : Blo 1232434 2775059 := bstep (se 1 (by rfl) ⟨2081294, by rfl⟩ : syracuseStep 2775059 = 4162589) B4162589
theorem B40024151 : Blo 1232434 40024151 := bstep (se 1 (by rfl) ⟨30018113, by rfl⟩ : syracuseStep 40024151 = 60036227) B60036227
theorem B4446323 : Blo 1232434 4446323 := bstep (se 1 (by rfl) ⟨3334742, by rfl⟩ : syracuseStep 4446323 = 6669485) B6669485
theorem B2775401 : Blo 1232434 2775401 := bstep (se 2 (by rfl) ⟨1040775, by rfl⟩ : syracuseStep 2775401 = 2081551) B2081551
theorem B4684175 : Blo 1232434 4684175 := bstep (se 1 (by rfl) ⟨3513131, by rfl⟩ : syracuseStep 4684175 = 7026263) B7026263
theorem B9361817 : Blo 1232434 9361817 := bstep (se 2 (by rfl) ⟨3510681, by rfl⟩ : syracuseStep 9361817 = 7021363) B7021363
theorem B1849775 : Blo 1232434 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B1849865 : Blo 1232434 1849865 := bstep (se 2 (by rfl) ⟨693699, by rfl⟩ : syracuseStep 1849865 = 1387399) B1387399
theorem B5003801 : Blo 1232434 5003801 := bstep (se 2 (by rfl) ⟨1876425, by rfl⟩ : syracuseStep 5003801 = 3752851) B3752851
theorem B4749857 : Blo 1232434 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B1849895 : Blo 1232434 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B2636327 : Blo 1232434 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B1849979 : Blo 1232434 1849979 := bstep (se 1 (by rfl) ⟨1387484, by rfl⟩ : syracuseStep 1849979 = 2774969) B2774969
theorem B6666887 : Blo 1232434 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B3119755 : Blo 1232434 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B7903955 : Blo 1232434 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B1850105 : Blo 1232434 1850105 := bstep (se 2 (by rfl) ⟨693789, by rfl⟩ : syracuseStep 1850105 = 1387579) B1387579
theorem B1850207 : Blo 1232434 1850207 := bstep (se 1 (by rfl) ⟨1387655, by rfl⟩ : syracuseStep 1850207 = 2775311) B2775311
theorem B1850219 : Blo 1232434 1850219 := bstep (se 1 (by rfl) ⟨1387664, by rfl⟩ : syracuseStep 1850219 = 2775329) B2775329
theorem B4160375 : Blo 1232434 4160375 := bstep (se 1 (by rfl) ⟨3120281, by rfl⟩ : syracuseStep 4160375 = 6240563) B6240563
theorem B3120059 : Blo 1232434 3120059 := bstep (se 1 (by rfl) ⟨2340044, by rfl⟩ : syracuseStep 3120059 = 4680089) B4680089
theorem B2775995 : Blo 1232434 2775995 := bstep (se 1 (by rfl) ⟨2081996, by rfl⟩ : syracuseStep 2775995 = 4163993) B4163993
theorem B5266433 : Blo 1232434 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B15817751 : Blo 1232434 15817751 := bstep (se 1 (by rfl) ⟨11863313, by rfl⟩ : syracuseStep 15817751 = 23726627) B23726627
theorem B2776121 : Blo 1232434 2776121 := bstep (se 2 (by rfl) ⟨1041045, by rfl⟩ : syracuseStep 2776121 = 2082091) B2082091
theorem B2079823 : Blo 1232434 2079823 := bstep (se 1 (by rfl) ⟨1559867, by rfl⟩ : syracuseStep 2079823 = 3119735) B3119735
theorem B4160591 : Blo 1232434 4160591 := bstep (se 1 (by rfl) ⟨3120443, by rfl⟩ : syracuseStep 4160591 = 6240887) B6240887
theorem B1850447 : Blo 1232434 1850447 := bstep (se 1 (by rfl) ⟨1387835, by rfl⟩ : syracuseStep 1850447 = 2775671) B2775671
theorem B1850567 : Blo 1232434 1850567 := bstep (se 1 (by rfl) ⟨1387925, by rfl⟩ : syracuseStep 1850567 = 2775851) B2775851
theorem B7019723 : Blo 1232434 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B2080073 : Blo 1232434 2080073 := bstep (se 2 (by rfl) ⟨780027, by rfl⟩ : syracuseStep 2080073 = 1560055) B1560055
theorem B1850729 : Blo 1232434 1850729 := bstep (se 2 (by rfl) ⟨694023, by rfl⟩ : syracuseStep 1850729 = 1388047) B1388047
theorem B4685161 : Blo 1232434 4685161 := bstep (se 2 (by rfl) ⟨1756935, by rfl⟩ : syracuseStep 4685161 = 3513871) B3513871
theorem B2776463 : Blo 1232434 2776463 := bstep (se 1 (by rfl) ⟨2082347, by rfl⟩ : syracuseStep 2776463 = 4164695) B4164695
theorem B1850807 : Blo 1232434 1850807 := bstep (se 1 (by rfl) ⟨1388105, by rfl⟩ : syracuseStep 1850807 = 2776211) B2776211
theorem B4160969 : Blo 1232434 4160969 := bstep (se 2 (by rfl) ⟨1560363, by rfl⟩ : syracuseStep 4160969 = 3120727) B3120727
theorem B1850843 : Blo 1232434 1850843 := bstep (se 1 (by rfl) ⟨1388132, by rfl⟩ : syracuseStep 1850843 = 2776265) B2776265
theorem B4685435 : Blo 1232434 4685435 := bstep (se 1 (by rfl) ⟨3514076, by rfl⟩ : syracuseStep 4685435 = 7028153) B7028153
theorem B7020179 : Blo 1232434 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B3120839 : Blo 1232434 3120839 := bstep (se 1 (by rfl) ⟨2340629, by rfl⟩ : syracuseStep 3120839 = 4681259) B4681259
theorem B2342611 : Blo 1232434 2342611 := bstep (se 1 (by rfl) ⟨1756958, by rfl⟩ : syracuseStep 2342611 = 3513917) B3513917
theorem B2776787 : Blo 1232434 2776787 := bstep (se 1 (by rfl) ⟨2082590, by rfl⟩ : syracuseStep 2776787 = 4165181) B4165181
theorem B4161239 : Blo 1232434 4161239 := bstep (se 1 (by rfl) ⟨3120929, by rfl⟩ : syracuseStep 4161239 = 6241859) B6241859
theorem B11861741 : Blo 1232434 11861741 := bstep (se 3 (by rfl) ⟨2224076, by rfl⟩ : syracuseStep 11861741 = 4448153) B4448153
theorem B2080505 : Blo 1232434 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B3120889 : Blo 1232434 3120889 := bstep (se 2 (by rfl) ⟨1170333, by rfl⟩ : syracuseStep 3120889 = 2340667) B2340667
theorem B4218617 : Blo 1232434 4218617 := bstep (se 2 (by rfl) ⟨1581981, by rfl⟩ : syracuseStep 4218617 = 3163963) B3163963
theorem B8437537 : Blo 1232434 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B7905185 : Blo 1232434 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B2080687 : Blo 1232434 2080687 := bstep (se 1 (by rfl) ⟨1560515, by rfl⟩ : syracuseStep 2080687 = 3121031) B3121031
theorem B4161455 : Blo 1232434 4161455 := bstep (se 1 (by rfl) ⟨3121091, by rfl⟩ : syracuseStep 4161455 = 6242183) B6242183
theorem B1851311 : Blo 1232434 1851311 := bstep (se 1 (by rfl) ⟨1388483, by rfl⟩ : syracuseStep 1851311 = 2776967) B2776967
theorem B2342839 : Blo 1232434 2342839 := bstep (se 1 (by rfl) ⟨1757129, by rfl⟩ : syracuseStep 2342839 = 3514259) B3514259
theorem B14049287 : Blo 1232434 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B5922875 : Blo 1232434 5922875 := bstep (se 1 (by rfl) ⟨4442156, by rfl⟩ : syracuseStep 5922875 = 8884313) B8884313
theorem B1851497 : Blo 1232434 1851497 := bstep (se 2 (by rfl) ⟨694311, by rfl⟩ : syracuseStep 1851497 = 1388623) B1388623
theorem B6242507 : Blo 1232434 6242507 := bstep (se 1 (by rfl) ⟨4681880, by rfl⟩ : syracuseStep 6242507 = 9363761) B9363761
theorem B2777417 : Blo 1232434 2777417 := bstep (se 2 (by rfl) ⟨1041531, by rfl⟩ : syracuseStep 2777417 = 2083063) B2083063
theorem B3514715 : Blo 1232434 3514715 := bstep (se 1 (by rfl) ⟨2636036, by rfl⟩ : syracuseStep 3514715 = 5272073) B5272073
theorem B2777435 : Blo 1232434 2777435 := bstep (se 1 (by rfl) ⟨2083076, by rfl⟩ : syracuseStep 2777435 = 4166153) B4166153
theorem B4162049 : Blo 1232434 4162049 := bstep (se 2 (by rfl) ⟨1560768, by rfl⟩ : syracuseStep 4162049 = 3121537) B3121537
theorem B4686407 : Blo 1232434 4686407 := bstep (se 1 (by rfl) ⟨3514805, by rfl⟩ : syracuseStep 4686407 = 7029611) B7029611
theorem B4743851 : Blo 1232434 4743851 := bstep (se 1 (by rfl) ⟨3557888, by rfl⟩ : syracuseStep 4743851 = 7115777) B7115777
theorem B21087053 : Blo 1232434 21087053 := bstep (se 3 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 21087053 = 7907645) B7907645
theorem B1975195 : Blo 1232434 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B1975271 : Blo 1232434 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B4162535 : Blo 1232434 4162535 := bstep (se 1 (by rfl) ⟨3121901, by rfl⟩ : syracuseStep 4162535 = 6243803) B6243803
theorem B2081767 : Blo 1232434 2081767 := bstep (se 1 (by rfl) ⟨1561325, by rfl⟩ : syracuseStep 2081767 = 3122651) B3122651
theorem B9495589 : Blo 1232434 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B4998287 : Blo 1232434 4998287 := bstep (se 1 (by rfl) ⟨3748715, by rfl⟩ : syracuseStep 4998287 = 7497431) B7497431
theorem B4162859 : Blo 1232434 4162859 := bstep (se 1 (by rfl) ⟨3122144, by rfl⟩ : syracuseStep 4162859 = 6244289) B6244289
theorem B26682767 : Blo 1232434 26682767 := bstep (se 1 (by rfl) ⟨20012075, by rfl⟩ : syracuseStep 26682767 = 40024151) B40024151
theorem B15795607 : Blo 1232434 15795607 := bstep (se 1 (by rfl) ⟨11846705, by rfl⟩ : syracuseStep 15795607 = 23693411) B23693411
theorem B4163129 : Blo 1232434 4163129 := bstep (se 2 (by rfl) ⟨1561173, by rfl⟩ : syracuseStep 4163129 = 3122347) B3122347
theorem B3122783 : Blo 1232434 3122783 := bstep (se 1 (by rfl) ⟨2342087, by rfl⟩ : syracuseStep 3122783 = 4684175) B4684175
theorem B3335867 : Blo 1232434 3335867 := bstep (se 1 (by rfl) ⟨2501900, by rfl⟩ : syracuseStep 3335867 = 5003801) B5003801
theorem B17778365 : Blo 1232434 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B5269303 : Blo 1232434 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B13338445 : Blo 1232434 13338445 := bstep (se 3 (by rfl) ⟨2500958, by rfl⟩ : syracuseStep 13338445 = 5001917) B5001917
theorem B3950441 : Blo 1232434 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B54085603 : Blo 1232434 54085603 := bstep (se 1 (by rfl) ⟨40564202, by rfl⟩ : syracuseStep 54085603 = 81128405) B81128405
theorem B10545167 : Blo 1232434 10545167 := bstep (se 1 (by rfl) ⟨7908875, by rfl⟩ : syracuseStep 10545167 = 15817751) B15817751
theorem B4679815 : Blo 1232434 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B1386715 : Blo 1232434 1386715 := bstep (se 1 (by rfl) ⟨1040036, by rfl⟩ : syracuseStep 1386715 = 2080073) B2080073
theorem B3557657 : Blo 1232434 3557657 := bstep (se 2 (by rfl) ⟨1334121, by rfl⟩ : syracuseStep 3557657 = 2668243) B2668243
theorem B3123481 : Blo 1232434 3123481 := bstep (se 2 (by rfl) ⟨1171305, by rfl⟩ : syracuseStep 3123481 = 2342611) B2342611
theorem B11250049 : Blo 1232434 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B6244775 : Blo 1232434 6244775 := bstep (se 1 (by rfl) ⟨4683581, by rfl⟩ : syracuseStep 6244775 = 9367163) B9367163
theorem B3123623 : Blo 1232434 3123623 := bstep (se 1 (by rfl) ⟨2342717, by rfl⟩ : syracuseStep 3123623 = 4685435) B4685435
theorem B4680119 : Blo 1232434 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B9488869 : Blo 1232434 9488869 := bstep (se 4 (by rfl) ⟨889581, by rfl⟩ : syracuseStep 9488869 = 1779163) B1779163
theorem B7907827 : Blo 1232434 7907827 := bstep (se 1 (by rfl) ⟨5930870, by rfl⟩ : syracuseStep 7907827 = 11861741) B11861741
theorem B1387003 : Blo 1232434 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B2812411 : Blo 1232434 2812411 := bstep (se 1 (by rfl) ⟨2109308, by rfl⟩ : syracuseStep 2812411 = 4218617) B4218617
theorem B6244937 : Blo 1232434 6244937 := bstep (se 2 (by rfl) ⟨2341851, by rfl⟩ : syracuseStep 6244937 = 4683703) B4683703
theorem B3123785 : Blo 1232434 3123785 := bstep (se 2 (by rfl) ⟨1171419, by rfl⟩ : syracuseStep 3123785 = 2342839) B2342839
theorem B5270123 : Blo 1232434 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B1387183 : Blo 1232434 1387183 := bstep (se 1 (by rfl) ⟨1040387, by rfl⟩ : syracuseStep 1387183 = 2080775) B2080775
theorem B4164371 : Blo 1232434 4164371 := bstep (se 1 (by rfl) ⟨3123278, by rfl⟩ : syracuseStep 4164371 = 6246557) B6246557
theorem B1387471 : Blo 1232434 1387471 := bstep (se 1 (by rfl) ⟨1040603, by rfl⟩ : syracuseStep 1387471 = 2081207) B2081207
theorem B8440847 : Blo 1232434 8440847 := bstep (se 1 (by rfl) ⟨6330635, by rfl⟩ : syracuseStep 8440847 = 12661271) B12661271
theorem B4566139 : Blo 1232434 4566139 := bstep (se 1 (by rfl) ⟨3424604, by rfl⟩ : syracuseStep 4566139 = 6849209) B6849209
theorem B1387867 : Blo 1232434 1387867 := bstep (se 1 (by rfl) ⟨1040900, by rfl⟩ : syracuseStep 1387867 = 2081801) B2081801
theorem B1666441 : Blo 1232434 1666441 := bstep (se 2 (by rfl) ⟨624915, by rfl⟩ : syracuseStep 1666441 = 1249831) B1249831
theorem B1387975 : Blo 1232434 1387975 := bstep (se 1 (by rfl) ⟨1040981, by rfl⟩ : syracuseStep 1387975 = 2081963) B2081963
theorem B5271065 : Blo 1232434 5271065 := bstep (se 2 (by rfl) ⟨1976649, by rfl⟩ : syracuseStep 5271065 = 3953299) B3953299
theorem B1232447 : Blo 1232434 1232447 := bstep (se 1 (by rfl) ⟨924335, by rfl⟩ : syracuseStep 1232447 = 1848671) B1848671
theorem B1232455 : Blo 1232434 1232455 := bstep (se 1 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 1232455 = 1848683) B1848683
theorem B5271149 : Blo 1232434 5271149 := bstep (se 3 (by rfl) ⟨988340, by rfl⟩ : syracuseStep 5271149 = 1976681) B1976681
theorem B4165235 : Blo 1232434 4165235 := bstep (se 1 (by rfl) ⟨3123926, by rfl⟩ : syracuseStep 4165235 = 6247853) B6247853
theorem B1232607 : Blo 1232434 1232607 := bstep (se 1 (by rfl) ⟨924455, by rfl⟩ : syracuseStep 1232607 = 1848911) B1848911
theorem B1232687 : Blo 1232434 1232687 := bstep (se 1 (by rfl) ⟨924515, by rfl⟩ : syracuseStep 1232687 = 1849031) B1849031
theorem B1388335 : Blo 1232434 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B4165505 : Blo 1232434 4165505 := bstep (se 2 (by rfl) ⟨1562064, by rfl⟩ : syracuseStep 4165505 = 3124129) B3124129
theorem B1232795 : Blo 1232434 1232795 := bstep (se 1 (by rfl) ⟨924596, by rfl⟩ : syracuseStep 1232795 = 1849193) B1849193
theorem B1560475 : Blo 1232434 1560475 := bstep (se 1 (by rfl) ⟨1170356, by rfl⟩ : syracuseStep 1560475 = 2340713) B2340713
theorem B1388443 : Blo 1232434 1388443 := bstep (se 1 (by rfl) ⟨1041332, by rfl⟩ : syracuseStep 1388443 = 2082665) B2082665
theorem B1232847 : Blo 1232434 1232847 := bstep (se 1 (by rfl) ⟨924635, by rfl⟩ : syracuseStep 1232847 = 1849271) B1849271
theorem B10137565 : Blo 1232434 10137565 := bstep (se 3 (by rfl) ⟨1900793, by rfl⟩ : syracuseStep 10137565 = 3801587) B3801587
theorem B1232871 : Blo 1232434 1232871 := bstep (se 1 (by rfl) ⟨924653, by rfl⟩ : syracuseStep 1232871 = 1849307) B1849307
theorem B1667047 : Blo 1232434 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B5926931 : Blo 1232434 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B2773097 : Blo 1232434 2773097 := bstep (se 2 (by rfl) ⟨1039911, by rfl⟩ : syracuseStep 2773097 = 2079823) B2079823
theorem B1233183 : Blo 1232434 1233183 := bstep (se 1 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 1233183 = 1849775) B1849775
theorem B2961755 : Blo 1232434 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B1233243 : Blo 1232434 1233243 := bstep (se 1 (by rfl) ⟨924932, by rfl⟩ : syracuseStep 1233243 = 1849865) B1849865
theorem B3166571 : Blo 1232434 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1233263 : Blo 1232434 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B1757551 : Blo 1232434 1757551 := bstep (se 1 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 1757551 = 2636327) B2636327
theorem B1233319 : Blo 1232434 1233319 := bstep (se 1 (by rfl) ⟨924989, by rfl⟩ : syracuseStep 1233319 = 1849979) B1849979
theorem B6246881 : Blo 1232434 6246881 := bstep (se 2 (by rfl) ⟨2342580, by rfl⟩ : syracuseStep 6246881 = 4685161) B4685161
theorem B1233403 : Blo 1232434 1233403 := bstep (se 1 (by rfl) ⟨925052, by rfl⟩ : syracuseStep 1233403 = 1850105) B1850105
theorem B1233471 : Blo 1232434 1233471 := bstep (se 1 (by rfl) ⟨925103, by rfl⟩ : syracuseStep 1233471 = 1850207) B1850207
theorem B1233479 : Blo 1232434 1233479 := bstep (se 1 (by rfl) ⟨925109, by rfl⟩ : syracuseStep 1233479 = 1850219) B1850219
theorem B2773583 : Blo 1232434 2773583 := bstep (se 1 (by rfl) ⟨2080187, by rfl⟩ : syracuseStep 2773583 = 4160375) B4160375
theorem B3510955 : Blo 1232434 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B2773727 : Blo 1232434 2773727 := bstep (se 1 (by rfl) ⟨2080295, by rfl⟩ : syracuseStep 2773727 = 4160591) B4160591
theorem B1233631 : Blo 1232434 1233631 := bstep (se 1 (by rfl) ⟨925223, by rfl⟩ : syracuseStep 1233631 = 1850447) B1850447
theorem B8434475 : Blo 1232434 8434475 := bstep (se 1 (by rfl) ⟨6325856, by rfl⟩ : syracuseStep 8434475 = 12651713) B12651713
theorem B1233711 : Blo 1232434 1233711 := bstep (se 1 (by rfl) ⟨925283, by rfl⟩ : syracuseStep 1233711 = 1850567) B1850567
theorem B1233819 : Blo 1232434 1233819 := bstep (se 1 (by rfl) ⟨925364, by rfl⟩ : syracuseStep 1233819 = 1850729) B1850729
theorem B1233871 : Blo 1232434 1233871 := bstep (se 1 (by rfl) ⟨925403, by rfl⟩ : syracuseStep 1233871 = 1850807) B1850807
theorem B2773979 : Blo 1232434 2773979 := bstep (se 1 (by rfl) ⟨2080484, by rfl⟩ : syracuseStep 2773979 = 4160969) B4160969
theorem B1233895 : Blo 1232434 1233895 := bstep (se 1 (by rfl) ⟨925421, by rfl⟩ : syracuseStep 1233895 = 1850843) B1850843
theorem B68432957 : Blo 1232434 68432957 := bstep (se 3 (by rfl) ⟨12831179, by rfl⟩ : syracuseStep 68432957 = 25662359) B25662359
theorem B2774159 : Blo 1232434 2774159 := bstep (se 1 (by rfl) ⟨2080619, by rfl⟩ : syracuseStep 2774159 = 4161239) B4161239
theorem B7124183 : Blo 1232434 7124183 := bstep (se 1 (by rfl) ⟨5343137, by rfl⟩ : syracuseStep 7124183 = 10686275) B10686275
theorem B2774249 : Blo 1232434 2774249 := bstep (se 2 (by rfl) ⟨1040343, by rfl⟩ : syracuseStep 2774249 = 2080687) B2080687
theorem B2774303 : Blo 1232434 2774303 := bstep (se 1 (by rfl) ⟨2080727, by rfl⟩ : syracuseStep 2774303 = 4161455) B4161455
theorem B1234207 : Blo 1232434 1234207 := bstep (se 1 (by rfl) ⟨925655, by rfl⟩ : syracuseStep 1234207 = 1851311) B1851311
theorem B1234267 : Blo 1232434 1234267 := bstep (se 1 (by rfl) ⟨925700, by rfl⟩ : syracuseStep 1234267 = 1851401) B1851401
theorem B1316207 : Blo 1232434 1316207 := bstep (se 1 (by rfl) ⟨987155, by rfl⟩ : syracuseStep 1316207 = 1974311) B1974311
theorem B1234287 : Blo 1232434 1234287 := bstep (se 1 (by rfl) ⟨925715, by rfl⟩ : syracuseStep 1234287 = 1851431) B1851431
theorem B1848713 : Blo 1232434 1848713 := bstep (se 2 (by rfl) ⟨693267, by rfl⟩ : syracuseStep 1848713 = 1386535) B1386535
theorem B5625227 : Blo 1232434 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B1234343 : Blo 1232434 1234343 := bstep (se 1 (by rfl) ⟨925757, by rfl⟩ : syracuseStep 1234343 = 1851515) B1851515
theorem B1234427 : Blo 1232434 1234427 := bstep (se 1 (by rfl) ⟨925820, by rfl⟩ : syracuseStep 1234427 = 1851641) B1851641
theorem B5264929 : Blo 1232434 5264929 := bstep (se 2 (by rfl) ⟨1974348, by rfl⟩ : syracuseStep 5264929 = 3948697) B3948697
theorem B3954233 : Blo 1232434 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B5142203 : Blo 1232434 5142203 := bstep (se 1 (by rfl) ⟨3856652, by rfl⟩ : syracuseStep 5142203 = 7713305) B7713305
theorem B1849067 : Blo 1232434 1849067 := bstep (se 1 (by rfl) ⟨1386800, by rfl⟩ : syracuseStep 1849067 = 2773601) B2773601
theorem B2774825 : Blo 1232434 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B21370817 : Blo 1232434 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B1849295 : Blo 1232434 1849295 := bstep (se 1 (by rfl) ⟨1386971, by rfl⟩ : syracuseStep 1849295 = 2773943) B2773943
theorem B4159673 : Blo 1232434 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B4217017 : Blo 1232434 4217017 := bstep (se 2 (by rfl) ⟨1581381, by rfl⟩ : syracuseStep 4217017 = 3162763) B3162763
theorem B3512585 : Blo 1232434 3512585 := bstep (se 2 (by rfl) ⟨1317219, by rfl⟩ : syracuseStep 3512585 = 2634439) B2634439
theorem B1317151 : Blo 1232434 1317151 := bstep (se 1 (by rfl) ⟨987863, by rfl⟩ : syracuseStep 1317151 = 1975727) B1975727
theorem B1849691 : Blo 1232434 1849691 := bstep (se 1 (by rfl) ⟨1387268, by rfl⟩ : syracuseStep 1849691 = 2774537) B2774537
theorem B18987473 : Blo 1232434 18987473 := bstep (se 2 (by rfl) ⟨7120302, by rfl⟩ : syracuseStep 18987473 = 14240605) B14240605
theorem B7027195 : Blo 1232434 7027195 := bstep (se 1 (by rfl) ⟨5270396, by rfl⟩ : syracuseStep 7027195 = 10540793) B10540793
theorem B1849919 : Blo 1232434 1849919 := bstep (se 1 (by rfl) ⟨1387439, by rfl⟩ : syracuseStep 1849919 = 2774879) B2774879
theorem B15800939 : Blo 1232434 15800939 := bstep (se 1 (by rfl) ⟨11850704, by rfl⟩ : syracuseStep 15800939 = 23701409) B23701409
theorem B23722631 : Blo 1232434 23722631 := bstep (se 1 (by rfl) ⟨17791973, by rfl⟩ : syracuseStep 23722631 = 35583947) B35583947
theorem B4684463 : Blo 1232434 4684463 := bstep (se 1 (by rfl) ⟨3513347, by rfl⟩ : syracuseStep 4684463 = 7026695) B7026695
theorem B1850039 : Blo 1232434 1850039 := bstep (se 1 (by rfl) ⟨1387529, by rfl⟩ : syracuseStep 1850039 = 2775059) B2775059
theorem B6249149 : Blo 1232434 6249149 := bstep (se 3 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 6249149 = 2343431) B2343431
theorem B2964215 : Blo 1232434 2964215 := bstep (se 1 (by rfl) ⟨2223161, by rfl⟩ : syracuseStep 2964215 = 4446323) B4446323
theorem B2775887 : Blo 1232434 2775887 := bstep (se 1 (by rfl) ⟨2081915, by rfl⟩ : syracuseStep 2775887 = 4163831) B4163831
theorem B1850267 : Blo 1232434 1850267 := bstep (se 1 (by rfl) ⟨1387700, by rfl⟩ : syracuseStep 1850267 = 2775401) B2775401
theorem B6241211 : Blo 1232434 6241211 := bstep (se 1 (by rfl) ⟨4680908, by rfl⟩ : syracuseStep 6241211 = 9361817) B9361817
theorem B2776103 : Blo 1232434 2776103 := bstep (se 1 (by rfl) ⟨2082077, by rfl⟩ : syracuseStep 2776103 = 4164155) B4164155
theorem B106642493 : Blo 1232434 106642493 := bstep (se 3 (by rfl) ⟨19995467, by rfl⟩ : syracuseStep 106642493 = 39990935) B39990935
theorem B32046245 : Blo 1232434 32046245 := bstep (se 4 (by rfl) ⟨3004335, by rfl⟩ : syracuseStep 32046245 = 6008671) B6008671
theorem B2776283 : Blo 1232434 2776283 := bstep (se 1 (by rfl) ⟨2082212, by rfl⟩ : syracuseStep 2776283 = 4164425) B4164425
theorem B2080039 : Blo 1232434 2080039 := bstep (se 1 (by rfl) ⟨1560029, by rfl⟩ : syracuseStep 2080039 = 3120059) B3120059
theorem B1850663 : Blo 1232434 1850663 := bstep (se 1 (by rfl) ⟨1387997, by rfl⟩ : syracuseStep 1850663 = 2775995) B2775995
theorem B1850747 : Blo 1232434 1850747 := bstep (se 1 (by rfl) ⟨1388060, by rfl⟩ : syracuseStep 1850747 = 2776121) B2776121
theorem B3120545 : Blo 1232434 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B2776481 : Blo 1232434 2776481 := bstep (se 2 (by rfl) ⟨1041180, by rfl⟩ : syracuseStep 2776481 = 2082361) B2082361
theorem B50609609 : Blo 1232434 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B1850873 : Blo 1232434 1850873 := bstep (se 2 (by rfl) ⟨694077, by rfl⟩ : syracuseStep 1850873 = 1388155) B1388155
theorem B1850975 : Blo 1232434 1850975 := bstep (se 1 (by rfl) ⟨1388231, by rfl⟩ : syracuseStep 1850975 = 2776463) B2776463
theorem B10542707 : Blo 1232434 10542707 := bstep (se 1 (by rfl) ⟨7907030, by rfl⟩ : syracuseStep 10542707 = 15814061) B15814061
theorem B4161185 : Blo 1232434 4161185 := bstep (se 2 (by rfl) ⟨1560444, by rfl⟩ : syracuseStep 4161185 = 3120889) B3120889
theorem B5005097 : Blo 1232434 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B2080559 : Blo 1232434 2080559 := bstep (se 1 (by rfl) ⟨1560419, by rfl⟩ : syracuseStep 2080559 = 3120839) B3120839
theorem B1851191 : Blo 1232434 1851191 := bstep (se 1 (by rfl) ⟨1388393, by rfl⟩ : syracuseStep 1851191 = 2776787) B2776787
theorem B3121001 : Blo 1232434 3121001 := bstep (se 2 (by rfl) ⟨1170375, by rfl⟩ : syracuseStep 3121001 = 2340751) B2340751
theorem B8011649 : Blo 1232434 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B5267375 : Blo 1232434 5267375 := bstep (se 1 (by rfl) ⟨3950531, by rfl⟩ : syracuseStep 5267375 = 7901063) B7901063
theorem B2777039 : Blo 1232434 2777039 := bstep (se 1 (by rfl) ⟨2082779, by rfl⟩ : syracuseStep 2777039 = 4165559) B4165559
theorem B3948583 : Blo 1232434 3948583 := bstep (se 1 (by rfl) ⟨2961437, by rfl⟩ : syracuseStep 3948583 = 5922875) B5922875
theorem B4161671 : Blo 1232434 4161671 := bstep (se 1 (by rfl) ⟨3121253, by rfl⟩ : syracuseStep 4161671 = 6242507) B6242507
theorem B1851611 : Blo 1232434 1851611 := bstep (se 1 (by rfl) ⟨1388708, by rfl⟩ : syracuseStep 1851611 = 2777417) B2777417
theorem B1974503 : Blo 1232434 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B2343143 : Blo 1232434 2343143 := bstep (se 1 (by rfl) ⟨1757357, by rfl⟩ : syracuseStep 2343143 = 3514715) B3514715
theorem B1851623 : Blo 1232434 1851623 := bstep (se 1 (by rfl) ⟨1388717, by rfl⟩ : syracuseStep 1851623 = 2777435) B2777435
theorem B2343401 : Blo 1232434 2343401 := bstep (se 2 (by rfl) ⟨878775, by rfl⟩ : syracuseStep 2343401 = 1757551) B1757551
theorem B15000065 : Blo 1232434 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B14058035 : Blo 1232434 14058035 := bstep (se 1 (by rfl) ⟨10543526, by rfl⟩ : syracuseStep 14058035 = 21087053) B21087053
theorem B10543769 : Blo 1232434 10543769 := bstep (se 2 (by rfl) ⟨3953913, by rfl⟩ : syracuseStep 10543769 = 7907827) B7907827
theorem B45621971 : Blo 1232434 45621971 := bstep (se 1 (by rfl) ⟨34216478, by rfl⟩ : syracuseStep 45621971 = 68432957) B68432957
theorem B2081855 : Blo 1232434 2081855 := bstep (se 1 (by rfl) ⟨1561391, by rfl⟩ : syracuseStep 2081855 = 3122783) B3122783
theorem B7030111 : Blo 1232434 7030111 := bstep (se 1 (by rfl) ⟨5272583, by rfl⟩ : syracuseStep 7030111 = 10545167) B10545167
theorem B4163183 : Blo 1232434 4163183 := bstep (se 1 (by rfl) ⟨3122387, by rfl⟩ : syracuseStep 4163183 = 6244775) B6244775
theorem B2082415 : Blo 1232434 2082415 := bstep (se 1 (by rfl) ⟨1561811, by rfl⟩ : syracuseStep 2082415 = 3123623) B3123623
theorem B12658315 : Blo 1232434 12658315 := bstep (se 1 (by rfl) ⟨9493736, by rfl⟩ : syracuseStep 12658315 = 18987473) B18987473
theorem B4163291 : Blo 1232434 4163291 := bstep (se 1 (by rfl) ⟨3122468, by rfl⟩ : syracuseStep 4163291 = 6244937) B6244937
theorem B2082523 : Blo 1232434 2082523 := bstep (se 1 (by rfl) ⟨1561892, by rfl⟩ : syracuseStep 2082523 = 3123785) B3123785
theorem B12650269 : Blo 1232434 12650269 := bstep (se 3 (by rfl) ⟨2371925, by rfl⟩ : syracuseStep 12650269 = 4743851) B4743851
theorem B3122975 : Blo 1232434 3122975 := bstep (se 1 (by rfl) ⟨2342231, by rfl⟩ : syracuseStep 3122975 = 4684463) B4684463
theorem B1976143 : Blo 1232434 1976143 := bstep (se 1 (by rfl) ⟨1482107, by rfl⟩ : syracuseStep 1976143 = 2964215) B2964215
theorem B2221921 : Blo 1232434 2221921 := bstep (se 2 (by rfl) ⟨833220, by rfl⟩ : syracuseStep 2221921 = 1666441) B1666441
theorem B3336731 : Blo 1232434 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B1387039 : Blo 1232434 1387039 := bstep (se 1 (by rfl) ⟨1040279, by rfl⟩ : syracuseStep 1387039 = 2080559) B2080559
theorem B2222729 : Blo 1232434 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B9366191 : Blo 1232434 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B3951287 : Blo 1232434 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B5622689 : Blo 1232434 5622689 := bstep (se 2 (by rfl) ⟨2108508, by rfl⟩ : syracuseStep 5622689 = 4217017) B4217017
theorem B4164587 : Blo 1232434 4164587 := bstep (se 1 (by rfl) ⟨3123440, by rfl⟩ : syracuseStep 4164587 = 6246881) B6246881
theorem B4164641 : Blo 1232434 4164641 := bstep (se 2 (by rfl) ⟨1561740, by rfl⟩ : syracuseStep 4164641 = 3123481) B3123481
theorem B3124271 : Blo 1232434 3124271 := bstep (se 1 (by rfl) ⟨2343203, by rfl⟩ : syracuseStep 3124271 = 4686407) B4686407
theorem B5622983 : Blo 1232434 5622983 := bstep (se 1 (by rfl) ⟨4217237, by rfl⟩ : syracuseStep 5622983 = 8434475) B8434475
theorem B4681273 : Blo 1232434 4681273 := bstep (se 2 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 4681273 = 3510955) B3510955
theorem B1232475 : Blo 1232434 1232475 := bstep (se 1 (by rfl) ⟨924356, by rfl⟩ : syracuseStep 1232475 = 1848713) B1848713
theorem B17788511 : Blo 1232434 17788511 := bstep (se 1 (by rfl) ⟨13341383, by rfl⟩ : syracuseStep 17788511 = 26682767) B26682767
theorem B3509885 : Blo 1232434 3509885 := bstep (se 3 (by rfl) ⟨658103, by rfl⟩ : syracuseStep 3509885 = 1316207) B1316207
theorem B2223911 : Blo 1232434 2223911 := bstep (se 1 (by rfl) ⟨1667933, by rfl⟩ : syracuseStep 2223911 = 3335867) B3335867
theorem B3428135 : Blo 1232434 3428135 := bstep (se 1 (by rfl) ⟨2571101, by rfl⟩ : syracuseStep 3428135 = 5142203) B5142203
theorem B1232711 : Blo 1232434 1232711 := bstep (se 1 (by rfl) ⟨924533, by rfl⟩ : syracuseStep 1232711 = 1849067) B1849067
theorem B2633593 : Blo 1232434 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B2633627 : Blo 1232434 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B1232863 : Blo 1232434 1232863 := bstep (se 1 (by rfl) ⟨924647, by rfl⟩ : syracuseStep 1232863 = 1849295) B1849295
theorem B12660785 : Blo 1232434 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B2773115 : Blo 1232434 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B7024805 : Blo 1232434 7024805 := bstep (se 4 (by rfl) ⟨658575, by rfl⟩ : syracuseStep 7024805 = 1317151) B1317151
theorem B2371771 : Blo 1232434 2371771 := bstep (se 1 (by rfl) ⟨1778828, by rfl⟩ : syracuseStep 2371771 = 3557657) B3557657
theorem B1233127 : Blo 1232434 1233127 := bstep (se 1 (by rfl) ⟨924845, by rfl⟩ : syracuseStep 1233127 = 1849691) B1849691
theorem B14053661 : Blo 1232434 14053661 := bstep (se 3 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 14053661 = 5270123) B5270123
theorem B1233279 : Blo 1232434 1233279 := bstep (se 1 (by rfl) ⟨924959, by rfl⟩ : syracuseStep 1233279 = 1849919) B1849919
theorem B2773385 : Blo 1232434 2773385 := bstep (se 2 (by rfl) ⟨1040019, by rfl⟩ : syracuseStep 2773385 = 2080039) B2080039
theorem B15815087 : Blo 1232434 15815087 := bstep (se 1 (by rfl) ⟨11861315, by rfl⟩ : syracuseStep 15815087 = 23722631) B23722631
theorem B1233359 : Blo 1232434 1233359 := bstep (se 1 (by rfl) ⟨925019, by rfl⟩ : syracuseStep 1233359 = 1850039) B1850039
theorem B4166099 : Blo 1232434 4166099 := bstep (se 1 (by rfl) ⟨3124574, by rfl⟩ : syracuseStep 4166099 = 6249149) B6249149
theorem B1233511 : Blo 1232434 1233511 := bstep (se 1 (by rfl) ⟨925133, by rfl⟩ : syracuseStep 1233511 = 1850267) B1850267
theorem B71094995 : Blo 1232434 71094995 := bstep (se 1 (by rfl) ⟨53321246, by rfl⟩ : syracuseStep 71094995 = 106642493) B106642493
theorem B1233775 : Blo 1232434 1233775 := bstep (se 1 (by rfl) ⟨925331, by rfl⟩ : syracuseStep 1233775 = 1850663) B1850663
theorem B1233831 : Blo 1232434 1233831 := bstep (se 1 (by rfl) ⟨925373, by rfl⟩ : syracuseStep 1233831 = 1850747) B1850747
theorem B33739739 : Blo 1232434 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B1233915 : Blo 1232434 1233915 := bstep (se 1 (by rfl) ⟨925436, by rfl⟩ : syracuseStep 1233915 = 1850873) B1850873
theorem B1233983 : Blo 1232434 1233983 := bstep (se 1 (by rfl) ⟨925487, by rfl⟩ : syracuseStep 1233983 = 1850975) B1850975
theorem B7025737 : Blo 1232434 7025737 := bstep (se 2 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 7025737 = 5269303) B5269303
theorem B2774123 : Blo 1232434 2774123 := bstep (se 1 (by rfl) ⟨2080592, by rfl⟩ : syracuseStep 2774123 = 4161185) B4161185
theorem B56988845 : Blo 1232434 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B50607301 : Blo 1232434 50607301 := bstep (se 4 (by rfl) ⟨4744434, by rfl⟩ : syracuseStep 50607301 = 9488869) B9488869
theorem B1234127 : Blo 1232434 1234127 := bstep (se 1 (by rfl) ⟨925595, by rfl⟩ : syracuseStep 1234127 = 1851191) B1851191
theorem B3511583 : Blo 1232434 3511583 := bstep (se 1 (by rfl) ⟨2633687, by rfl⟩ : syracuseStep 3511583 = 5267375) B5267375
theorem B1848731 : Blo 1232434 1848731 := bstep (se 1 (by rfl) ⟨1386548, by rfl⟩ : syracuseStep 1848731 = 2773097) B2773097
theorem B1234331 : Blo 1232434 1234331 := bstep (se 1 (by rfl) ⟨925748, by rfl⟩ : syracuseStep 1234331 = 1851497) B1851497
theorem B6239753 : Blo 1232434 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B1848953 : Blo 1232434 1848953 := bstep (se 2 (by rfl) ⟨693357, by rfl⟩ : syracuseStep 1848953 = 1386715) B1386715
theorem B2774699 : Blo 1232434 2774699 := bstep (se 1 (by rfl) ⟨2081024, by rfl⟩ : syracuseStep 2774699 = 4162049) B4162049
theorem B1849055 : Blo 1232434 1849055 := bstep (se 1 (by rfl) ⟨1386791, by rfl⟩ : syracuseStep 1849055 = 2773583) B2773583
theorem B1849151 : Blo 1232434 1849151 := bstep (se 1 (by rfl) ⟨1386863, by rfl⟩ : syracuseStep 1849151 = 2773727) B2773727
theorem B24352741 : Blo 1232434 24352741 := bstep (se 4 (by rfl) ⟨2283069, by rfl⟩ : syracuseStep 24352741 = 4566139) B4566139
theorem B1849319 : Blo 1232434 1849319 := bstep (se 1 (by rfl) ⟨1386989, by rfl⟩ : syracuseStep 1849319 = 2773979) B2773979
theorem B2775023 : Blo 1232434 2775023 := bstep (se 1 (by rfl) ⟨2081267, by rfl⟩ : syracuseStep 2775023 = 4162535) B4162535
theorem B1849337 : Blo 1232434 1849337 := bstep (se 2 (by rfl) ⟨693501, by rfl⟩ : syracuseStep 1849337 = 1387003) B1387003
theorem B9369593 : Blo 1232434 9369593 := bstep (se 2 (by rfl) ⟨3513597, by rfl⟩ : syracuseStep 9369593 = 7027195) B7027195
theorem B3332191 : Blo 1232434 3332191 := bstep (se 1 (by rfl) ⟨2499143, by rfl⟩ : syracuseStep 3332191 = 4998287) B4998287
theorem B1849439 : Blo 1232434 1849439 := bstep (se 1 (by rfl) ⟨1387079, by rfl⟩ : syracuseStep 1849439 = 2774159) B2774159
theorem B4749455 : Blo 1232434 4749455 := bstep (se 1 (by rfl) ⟨3562091, by rfl⟩ : syracuseStep 4749455 = 7124183) B7124183
theorem B1849499 : Blo 1232434 1849499 := bstep (se 1 (by rfl) ⟨1387124, by rfl⟩ : syracuseStep 1849499 = 2774249) B2774249
theorem B1849535 : Blo 1232434 1849535 := bstep (se 1 (by rfl) ⟨1387151, by rfl⟩ : syracuseStep 1849535 = 2774303) B2774303
theorem B2775239 : Blo 1232434 2775239 := bstep (se 1 (by rfl) ⟨2081429, by rfl⟩ : syracuseStep 2775239 = 4162859) B4162859
theorem B1849577 : Blo 1232434 1849577 := bstep (se 2 (by rfl) ⟨693591, by rfl⟩ : syracuseStep 1849577 = 1387183) B1387183
theorem B3750151 : Blo 1232434 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B8444189 : Blo 1232434 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B2775419 : Blo 1232434 2775419 := bstep (se 1 (by rfl) ⟨2081564, by rfl⟩ : syracuseStep 2775419 = 4163129) B4163129
theorem B2636155 : Blo 1232434 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B11852243 : Blo 1232434 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B1849883 : Blo 1232434 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B1849961 : Blo 1232434 1849961 := bstep (se 2 (by rfl) ⟨693735, by rfl⟩ : syracuseStep 1849961 = 1387471) B1387471
theorem B2775689 : Blo 1232434 2775689 := bstep (se 2 (by rfl) ⟨1040883, by rfl⟩ : syracuseStep 2775689 = 2081767) B2081767
theorem B2341723 : Blo 1232434 2341723 := bstep (se 1 (by rfl) ⟨1756292, by rfl⟩ : syracuseStep 2341723 = 3512585) B3512585
theorem B3120079 : Blo 1232434 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B10533959 : Blo 1232434 10533959 := bstep (se 1 (by rfl) ⟨7900469, by rfl⟩ : syracuseStep 10533959 = 15800939) B15800939
theorem B1850489 : Blo 1232434 1850489 := bstep (se 2 (by rfl) ⟨693933, by rfl⟩ : syracuseStep 1850489 = 1387867) B1387867
theorem B2776247 : Blo 1232434 2776247 := bstep (se 1 (by rfl) ⟨2082185, by rfl⟩ : syracuseStep 2776247 = 4164371) B4164371
theorem B21060809 : Blo 1232434 21060809 := bstep (se 2 (by rfl) ⟨7897803, by rfl⟩ : syracuseStep 21060809 = 15795607) B15795607
theorem B1850591 : Blo 1232434 1850591 := bstep (se 1 (by rfl) ⟨1387943, by rfl⟩ : syracuseStep 1850591 = 2775887) B2775887
theorem B1850633 : Blo 1232434 1850633 := bstep (se 2 (by rfl) ⟨693987, by rfl⟩ : syracuseStep 1850633 = 1387975) B1387975
theorem B4160807 : Blo 1232434 4160807 := bstep (se 1 (by rfl) ⟨3120605, by rfl⟩ : syracuseStep 4160807 = 6241211) B6241211
theorem B5627231 : Blo 1232434 5627231 := bstep (se 1 (by rfl) ⟨4220423, by rfl⟩ : syracuseStep 5627231 = 8440847) B8440847
theorem B1850735 : Blo 1232434 1850735 := bstep (se 1 (by rfl) ⟨1388051, by rfl⟩ : syracuseStep 1850735 = 2776103) B2776103
theorem B7019905 : Blo 1232434 7019905 := bstep (se 2 (by rfl) ⟨2632464, by rfl⟩ : syracuseStep 7019905 = 5264929) B5264929
theorem B21364163 : Blo 1232434 21364163 := bstep (se 1 (by rfl) ⟨16023122, by rfl⟩ : syracuseStep 21364163 = 32046245) B32046245
theorem B1850855 : Blo 1232434 1850855 := bstep (se 1 (by rfl) ⟨1388141, by rfl⟩ : syracuseStep 1850855 = 2776283) B2776283
theorem B2080363 : Blo 1232434 2080363 := bstep (se 1 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 2080363 = 3120545) B3120545
theorem B1850987 : Blo 1232434 1850987 := bstep (se 1 (by rfl) ⟨1388240, by rfl⟩ : syracuseStep 1850987 = 2776481) B2776481
theorem B3514043 : Blo 1232434 3514043 := bstep (se 1 (by rfl) ⟨2635532, by rfl⟩ : syracuseStep 3514043 = 5271065) B5271065
theorem B1851113 : Blo 1232434 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B3514099 : Blo 1232434 3514099 := bstep (se 1 (by rfl) ⟨2635574, by rfl⟩ : syracuseStep 3514099 = 5271149) B5271149
theorem B21069557 : Blo 1232434 21069557 := bstep (se 5 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 21069557 = 1975271) B1975271
theorem B7028471 : Blo 1232434 7028471 := bstep (se 1 (by rfl) ⟨5271353, by rfl⟩ : syracuseStep 7028471 = 10542707) B10542707
theorem B2776823 : Blo 1232434 2776823 := bstep (se 1 (by rfl) ⟨2082617, by rfl⟩ : syracuseStep 2776823 = 4165235) B4165235
theorem B17784593 : Blo 1232434 17784593 := bstep (se 2 (by rfl) ⟨6669222, by rfl⟩ : syracuseStep 17784593 = 13338445) B13338445
theorem B2080633 : Blo 1232434 2080633 := bstep (se 2 (by rfl) ⟨780237, by rfl⟩ : syracuseStep 2080633 = 1560475) B1560475
theorem B1851257 : Blo 1232434 1851257 := bstep (se 2 (by rfl) ⟨694221, by rfl⟩ : syracuseStep 1851257 = 1388443) B1388443
theorem B2080667 : Blo 1232434 2080667 := bstep (se 1 (by rfl) ⟨1560500, by rfl⟩ : syracuseStep 2080667 = 3121001) B3121001
theorem B5341099 : Blo 1232434 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B2777003 : Blo 1232434 2777003 := bstep (se 1 (by rfl) ⟨2082752, by rfl⟩ : syracuseStep 2777003 = 4165505) B4165505
theorem B13516753 : Blo 1232434 13516753 := bstep (se 2 (by rfl) ⟨5068782, by rfl⟩ : syracuseStep 13516753 = 10137565) B10137565
theorem B72114137 : Blo 1232434 72114137 := bstep (se 2 (by rfl) ⟨27042801, by rfl⟩ : syracuseStep 72114137 = 54085603) B54085603
theorem B1851359 : Blo 1232434 1851359 := bstep (se 1 (by rfl) ⟨1388519, by rfl⟩ : syracuseStep 1851359 = 2777039) B2777039
theorem B14999525 : Blo 1232434 14999525 := bstep (se 4 (by rfl) ⟨1406205, by rfl⟩ : syracuseStep 14999525 = 2812411) B2812411
theorem B3162361 : Blo 1232434 3162361 := bstep (se 2 (by rfl) ⟨1185885, by rfl⟩ : syracuseStep 3162361 = 2371771) B2371771
theorem B10543391 : Blo 1232434 10543391 := bstep (se 1 (by rfl) ⟨7907543, by rfl⟩ : syracuseStep 10543391 = 15815087) B15815087
theorem B2777399 : Blo 1232434 2777399 := bstep (se 1 (by rfl) ⟨2083049, by rfl⟩ : syracuseStep 2777399 = 4166099) B4166099
theorem B9372023 : Blo 1232434 9372023 := bstep (se 1 (by rfl) ⟨7029017, by rfl⟩ : syracuseStep 9372023 = 14058035) B14058035
theorem B7029179 : Blo 1232434 7029179 := bstep (se 1 (by rfl) ⟨5271884, by rfl⟩ : syracuseStep 7029179 = 10543769) B10543769
theorem B3122297 : Blo 1232434 3122297 := bstep (se 2 (by rfl) ⟨1170861, by rfl⟩ : syracuseStep 3122297 = 2341723) B2341723
theorem B2081983 : Blo 1232434 2081983 := bstep (se 1 (by rfl) ⟨1561487, by rfl⟩ : syracuseStep 2081983 = 3122975) B3122975
theorem B5629459 : Blo 1232434 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B6244127 : Blo 1232434 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B9373481 : Blo 1232434 9373481 := bstep (se 2 (by rfl) ⟨3515055, by rfl⟩ : syracuseStep 9373481 = 7030111) B7030111
theorem B14059493 : Blo 1232434 14059493 := bstep (se 4 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 14059493 = 2636155) B2636155
theorem B2082847 : Blo 1232434 2082847 := bstep (se 1 (by rfl) ⟨1562135, by rfl⟩ : syracuseStep 2082847 = 3124271) B3124271
theorem B7022639 : Blo 1232434 7022639 := bstep (se 1 (by rfl) ⟨5266979, by rfl⟩ : syracuseStep 7022639 = 10533959) B10533959
theorem B16877753 : Blo 1232434 16877753 := bstep (se 2 (by rfl) ⟨6329157, by rfl⟩ : syracuseStep 16877753 = 12658315) B12658315
theorem B11856395 : Blo 1232434 11856395 := bstep (se 1 (by rfl) ⟨8892296, by rfl⟩ : syracuseStep 11856395 = 17784593) B17784593
theorem B7121465 : Blo 1232434 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B1387111 : Blo 1232434 1387111 := bstep (se 1 (by rfl) ⟨1040333, by rfl⟩ : syracuseStep 1387111 = 2080667) B2080667
theorem B1755751 : Blo 1232434 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B8440523 : Blo 1232434 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B4442921 : Blo 1232434 4442921 := bstep (se 2 (by rfl) ⟨1666095, by rfl⟩ : syracuseStep 4442921 = 3332191) B3332191
theorem B5000201 : Blo 1232434 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B1387903 : Blo 1232434 1387903 := bstep (se 1 (by rfl) ⟨1040927, by rfl⟩ : syracuseStep 1387903 = 2081855) B2081855
theorem B1232487 : Blo 1232434 1232487 := bstep (se 1 (by rfl) ⟨924365, by rfl⟩ : syracuseStep 1232487 = 1848731) B1848731
theorem B1232635 : Blo 1232434 1232635 := bstep (se 1 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 1232635 = 1848953) B1848953
theorem B1232703 : Blo 1232434 1232703 := bstep (se 1 (by rfl) ⟨924527, by rfl⟩ : syracuseStep 1232703 = 1849055) B1849055
theorem B1232767 : Blo 1232434 1232767 := bstep (se 1 (by rfl) ⟨924575, by rfl⟩ : syracuseStep 1232767 = 1849151) B1849151
theorem B1232879 : Blo 1232434 1232879 := bstep (se 1 (by rfl) ⟨924659, by rfl⟩ : syracuseStep 1232879 = 1849319) B1849319
theorem B1232891 : Blo 1232434 1232891 := bstep (se 1 (by rfl) ⟨924668, by rfl⟩ : syracuseStep 1232891 = 1849337) B1849337
theorem B6246395 : Blo 1232434 6246395 := bstep (se 1 (by rfl) ⟨4684796, by rfl⟩ : syracuseStep 6246395 = 9369593) B9369593
theorem B1232959 : Blo 1232434 1232959 := bstep (se 1 (by rfl) ⟨924719, by rfl⟩ : syracuseStep 1232959 = 1849439) B1849439
theorem B3166303 : Blo 1232434 3166303 := bstep (se 1 (by rfl) ⟨2374727, by rfl⟩ : syracuseStep 3166303 = 4749455) B4749455
theorem B9367649 : Blo 1232434 9367649 := bstep (se 2 (by rfl) ⟨3512868, by rfl⟩ : syracuseStep 9367649 = 7025737) B7025737
theorem B1232999 : Blo 1232434 1232999 := bstep (se 1 (by rfl) ⟨924749, by rfl⟩ : syracuseStep 1232999 = 1849499) B1849499
theorem B1233023 : Blo 1232434 1233023 := bstep (se 1 (by rfl) ⟨924767, by rfl⟩ : syracuseStep 1233023 = 1849535) B1849535
theorem B1233051 : Blo 1232434 1233051 := bstep (se 1 (by rfl) ⟨924788, by rfl⟩ : syracuseStep 1233051 = 1849577) B1849577
theorem B47436029 : Blo 1232434 47436029 := bstep (se 3 (by rfl) ⟨8894255, by rfl⟩ : syracuseStep 47436029 = 17788511) B17788511
theorem B7901495 : Blo 1232434 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B1233255 : Blo 1232434 1233255 := bstep (se 1 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 1233255 = 1849883) B1849883
theorem B2224487 : Blo 1232434 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B1233307 : Blo 1232434 1233307 := bstep (se 1 (by rfl) ⟨924980, by rfl⟩ : syracuseStep 1233307 = 1849961) B1849961
theorem B2634191 : Blo 1232434 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B9359873 : Blo 1232434 9359873 := bstep (se 2 (by rfl) ⟨3509952, by rfl⟩ : syracuseStep 9359873 = 7019905) B7019905
theorem B11850245 : Blo 1232434 11850245 := bstep (se 4 (by rfl) ⟨1110960, by rfl⟩ : syracuseStep 11850245 = 2221921) B2221921
theorem B3748459 : Blo 1232434 3748459 := bstep (se 1 (by rfl) ⟨2811344, by rfl⟩ : syracuseStep 3748459 = 5622689) B5622689
theorem B1233659 : Blo 1232434 1233659 := bstep (se 1 (by rfl) ⟨925244, by rfl⟩ : syracuseStep 1233659 = 1850489) B1850489
theorem B3748655 : Blo 1232434 3748655 := bstep (se 1 (by rfl) ⟨2811491, by rfl⟩ : syracuseStep 3748655 = 5622983) B5622983
theorem B2773817 : Blo 1232434 2773817 := bstep (se 2 (by rfl) ⟨1040181, by rfl⟩ : syracuseStep 2773817 = 2080363) B2080363
theorem B1233727 : Blo 1232434 1233727 := bstep (se 1 (by rfl) ⟨925295, by rfl⟩ : syracuseStep 1233727 = 1850591) B1850591
theorem B1233755 : Blo 1232434 1233755 := bstep (se 1 (by rfl) ⟨925316, by rfl⟩ : syracuseStep 1233755 = 1850633) B1850633
theorem B2773871 : Blo 1232434 2773871 := bstep (se 1 (by rfl) ⟨2080403, by rfl⟩ : syracuseStep 2773871 = 4160807) B4160807
theorem B1233823 : Blo 1232434 1233823 := bstep (se 1 (by rfl) ⟨925367, by rfl⟩ : syracuseStep 1233823 = 1850735) B1850735
theorem B14242775 : Blo 1232434 14242775 := bstep (se 1 (by rfl) ⟨10682081, by rfl⟩ : syracuseStep 14242775 = 21364163) B21364163
theorem B1233903 : Blo 1232434 1233903 := bstep (se 1 (by rfl) ⟨925427, by rfl⟩ : syracuseStep 1233903 = 1850855) B1850855
theorem B1233991 : Blo 1232434 1233991 := bstep (se 1 (by rfl) ⟨925493, by rfl⟩ : syracuseStep 1233991 = 1850987) B1850987
theorem B2339923 : Blo 1232434 2339923 := bstep (se 1 (by rfl) ⟨1754942, by rfl⟩ : syracuseStep 2339923 = 3509885) B3509885
theorem B2634857 : Blo 1232434 2634857 := bstep (se 2 (by rfl) ⟨988071, by rfl⟩ : syracuseStep 2634857 = 1976143) B1976143
theorem B1234075 : Blo 1232434 1234075 := bstep (se 1 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 1234075 = 1851113) B1851113
theorem B2774177 : Blo 1232434 2774177 := bstep (se 2 (by rfl) ⟨1040316, by rfl⟩ : syracuseStep 2774177 = 2080633) B2080633
theorem B3511457 : Blo 1232434 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B14046371 : Blo 1232434 14046371 := bstep (se 1 (by rfl) ⟨10534778, by rfl⟩ : syracuseStep 14046371 = 21069557) B21069557
theorem B1234171 : Blo 1232434 1234171 := bstep (se 1 (by rfl) ⟨925628, by rfl⟩ : syracuseStep 1234171 = 1851257) B1851257
theorem B32470321 : Blo 1232434 32470321 := bstep (se 2 (by rfl) ⟨12176370, by rfl⟩ : syracuseStep 32470321 = 24352741) B24352741
theorem B48076091 : Blo 1232434 48076091 := bstep (se 1 (by rfl) ⟨36057068, by rfl⟩ : syracuseStep 48076091 = 72114137) B72114137
theorem B1234239 : Blo 1232434 1234239 := bstep (se 1 (by rfl) ⟨925679, by rfl⟩ : syracuseStep 1234239 = 1851359) B1851359
theorem B9999683 : Blo 1232434 9999683 := bstep (se 1 (by rfl) ⟨7499762, by rfl⟩ : syracuseStep 9999683 = 14999525) B14999525
theorem B5264777 : Blo 1232434 5264777 := bstep (se 2 (by rfl) ⟨1974291, by rfl⟩ : syracuseStep 5264777 = 3948583) B3948583
theorem B1848743 : Blo 1232434 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B2774447 : Blo 1232434 2774447 := bstep (se 1 (by rfl) ⟨2080835, by rfl⟩ : syracuseStep 2774447 = 4161671) B4161671
theorem B4683203 : Blo 1232434 4683203 := bstep (se 1 (by rfl) ⟨3512402, by rfl⟩ : syracuseStep 4683203 = 7024805) B7024805
theorem B1234407 : Blo 1232434 1234407 := bstep (se 1 (by rfl) ⟨925805, by rfl⟩ : syracuseStep 1234407 = 1851611) B1851611
theorem B1316335 : Blo 1232434 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B1562095 : Blo 1232434 1562095 := bstep (se 1 (by rfl) ⟨1171571, by rfl⟩ : syracuseStep 1562095 = 2343143) B2343143
theorem B1234415 : Blo 1232434 1234415 := bstep (se 1 (by rfl) ⟨925811, by rfl⟩ : syracuseStep 1234415 = 1851623) B1851623
theorem B9369107 : Blo 1232434 9369107 := bstep (se 1 (by rfl) ⟨7026830, by rfl⟩ : syracuseStep 9369107 = 14053661) B14053661
theorem B1848923 : Blo 1232434 1848923 := bstep (se 1 (by rfl) ⟨1386692, by rfl⟩ : syracuseStep 1848923 = 2773385) B2773385
theorem B1562267 : Blo 1232434 1562267 := bstep (se 1 (by rfl) ⟨1171700, by rfl⟩ : syracuseStep 1562267 = 2343401) B2343401
theorem B10000043 : Blo 1232434 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B47396663 : Blo 1232434 47396663 := bstep (se 1 (by rfl) ⟨35547497, by rfl⟩ : syracuseStep 47396663 = 71094995) B71094995
theorem B30414647 : Blo 1232434 30414647 := bstep (se 1 (by rfl) ⟨22810985, by rfl⟩ : syracuseStep 30414647 = 45621971) B45621971
theorem B22493159 : Blo 1232434 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B1849385 : Blo 1232434 1849385 := bstep (se 2 (by rfl) ⟨693519, by rfl⟩ : syracuseStep 1849385 = 1387039) B1387039
theorem B1849415 : Blo 1232434 1849415 := bstep (se 1 (by rfl) ⟨1387061, by rfl⟩ : syracuseStep 1849415 = 2774123) B2774123
theorem B37992563 : Blo 1232434 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B2341055 : Blo 1232434 2341055 := bstep (se 1 (by rfl) ⟨1755791, by rfl⟩ : syracuseStep 2341055 = 3511583) B3511583
theorem B4159835 : Blo 1232434 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B2775455 : Blo 1232434 2775455 := bstep (se 1 (by rfl) ⟨2081591, by rfl⟩ : syracuseStep 2775455 = 4163183) B4163183
theorem B1849799 : Blo 1232434 1849799 := bstep (se 1 (by rfl) ⟨1387349, by rfl⟩ : syracuseStep 1849799 = 2774699) B2774699
theorem B2775527 : Blo 1232434 2775527 := bstep (se 1 (by rfl) ⟨2081645, by rfl⟩ : syracuseStep 2775527 = 4163291) B4163291
theorem B4160105 : Blo 1232434 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B1850015 : Blo 1232434 1850015 := bstep (se 1 (by rfl) ⟨1387511, by rfl⟩ : syracuseStep 1850015 = 2775023) B2775023
theorem B1850159 : Blo 1232434 1850159 := bstep (se 1 (by rfl) ⟨1387619, by rfl⟩ : syracuseStep 1850159 = 2775239) B2775239
theorem B1850279 : Blo 1232434 1850279 := bstep (se 1 (by rfl) ⟨1387709, by rfl⟩ : syracuseStep 1850279 = 2775419) B2775419
theorem B67476401 : Blo 1232434 67476401 := bstep (se 2 (by rfl) ⟨25303650, by rfl⟩ : syracuseStep 67476401 = 50607301) B50607301
theorem B1481819 : Blo 1232434 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B1850459 : Blo 1232434 1850459 := bstep (se 1 (by rfl) ⟨1387844, by rfl⟩ : syracuseStep 1850459 = 2775689) B2775689
theorem B2776391 : Blo 1232434 2776391 := bstep (se 1 (by rfl) ⟨2082293, by rfl⟩ : syracuseStep 2776391 = 4164587) B4164587
theorem B2776427 : Blo 1232434 2776427 := bstep (se 1 (by rfl) ⟨2082320, by rfl⟩ : syracuseStep 2776427 = 4164641) B4164641
theorem B6241697 : Blo 1232434 6241697 := bstep (se 2 (by rfl) ⟨2340636, by rfl⟩ : syracuseStep 6241697 = 4681273) B4681273
theorem B1850831 : Blo 1232434 1850831 := bstep (se 1 (by rfl) ⟨1388123, by rfl⟩ : syracuseStep 1850831 = 2776247) B2776247
theorem B14040539 : Blo 1232434 14040539 := bstep (se 1 (by rfl) ⟨10530404, by rfl⟩ : syracuseStep 14040539 = 21060809) B21060809
theorem B2776553 : Blo 1232434 2776553 := bstep (se 2 (by rfl) ⟨1041207, by rfl⟩ : syracuseStep 2776553 = 2082415) B2082415
theorem B3751487 : Blo 1232434 3751487 := bstep (se 1 (by rfl) ⟨2813615, by rfl⟩ : syracuseStep 3751487 = 5627231) B5627231
theorem B2776697 : Blo 1232434 2776697 := bstep (se 2 (by rfl) ⟨1041261, by rfl⟩ : syracuseStep 2776697 = 2082523) B2082523
theorem B4685465 : Blo 1232434 4685465 := bstep (se 2 (by rfl) ⟨1757049, by rfl⟩ : syracuseStep 4685465 = 3514099) B3514099
theorem B16867025 : Blo 1232434 16867025 := bstep (se 2 (by rfl) ⟨6325134, by rfl⟩ : syracuseStep 16867025 = 12650269) B12650269
theorem B2342695 : Blo 1232434 2342695 := bstep (se 1 (by rfl) ⟨1757021, by rfl⟩ : syracuseStep 2342695 = 3514043) B3514043
theorem B4685647 : Blo 1232434 4685647 := bstep (se 1 (by rfl) ⟨3514235, by rfl⟩ : syracuseStep 4685647 = 7028471) B7028471
theorem B1851215 : Blo 1232434 1851215 := bstep (se 1 (by rfl) ⟨1388411, by rfl⟩ : syracuseStep 1851215 = 2776823) B2776823
theorem B1482607 : Blo 1232434 1482607 := bstep (se 1 (by rfl) ⟨1111955, by rfl⟩ : syracuseStep 1482607 = 2223911) B2223911
theorem B2285423 : Blo 1232434 2285423 := bstep (se 1 (by rfl) ⟨1714067, by rfl⟩ : syracuseStep 2285423 = 3428135) B3428135
theorem B18022337 : Blo 1232434 18022337 := bstep (se 2 (by rfl) ⟨6758376, by rfl⟩ : syracuseStep 18022337 = 13516753) B13516753
theorem B1851335 : Blo 1232434 1851335 := bstep (se 1 (by rfl) ⟨1388501, by rfl⟩ : syracuseStep 1851335 = 2777003) B2777003
theorem B2777129 : Blo 1232434 2777129 := bstep (se 2 (by rfl) ⟨1041423, by rfl⟩ : syracuseStep 2777129 = 2082847) B2082847
theorem B7028927 : Blo 1232434 7028927 := bstep (se 1 (by rfl) ⟨5271695, by rfl⟩ : syracuseStep 7028927 = 10543391) B10543391
theorem B5267663 : Blo 1232434 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B1851599 : Blo 1232434 1851599 := bstep (se 1 (by rfl) ⟨1388699, by rfl⟩ : syracuseStep 1851599 = 2777399) B2777399
theorem B1482991 : Blo 1232434 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B4686119 : Blo 1232434 4686119 := bstep (se 1 (by rfl) ⟨3514589, by rfl⟩ : syracuseStep 4686119 = 7029179) B7029179
theorem B2499103 : Blo 1232434 2499103 := bstep (se 1 (by rfl) ⟨1874327, by rfl⟩ : syracuseStep 2499103 = 3748655) B3748655
theorem B2081531 : Blo 1232434 2081531 := bstep (se 1 (by rfl) ⟨1561148, by rfl⟩ : syracuseStep 2081531 = 3122297) B3122297
theorem B9364247 : Blo 1232434 9364247 := bstep (se 1 (by rfl) ⟨7023185, by rfl⟩ : syracuseStep 9364247 = 14046371) B14046371
theorem B4997945 : Blo 1232434 4997945 := bstep (se 2 (by rfl) ⟨1874229, by rfl⟩ : syracuseStep 4997945 = 3748459) B3748459
theorem B3122135 : Blo 1232434 3122135 := bstep (se 1 (by rfl) ⟨2341601, by rfl⟩ : syracuseStep 3122135 = 4683203) B4683203
theorem B4162751 : Blo 1232434 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B31597775 : Blo 1232434 31597775 := bstep (se 1 (by rfl) ⟨23698331, by rfl⟩ : syracuseStep 31597775 = 47396663) B47396663
theorem B9372995 : Blo 1232434 9372995 := bstep (se 1 (by rfl) ⟨7029746, by rfl⟩ : syracuseStep 9372995 = 14059493) B14059493
theorem B44984267 : Blo 1232434 44984267 := bstep (se 1 (by rfl) ⟨33738200, by rfl⟩ : syracuseStep 44984267 = 67476401) B67476401
theorem B1755113 : Blo 1232434 1755113 := bstep (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) B1316335
theorem B2082793 : Blo 1232434 2082793 := bstep (se 2 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 2082793 = 1562095) B1562095
theorem B7505945 : Blo 1232434 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B2500991 : Blo 1232434 2500991 := bstep (se 1 (by rfl) ⟨1875743, by rfl⟩ : syracuseStep 2500991 = 3751487) B3751487
theorem B3123593 : Blo 1232434 3123593 := bstep (se 2 (by rfl) ⟨1171347, by rfl⟩ : syracuseStep 3123593 = 2342695) B2342695
theorem B3123643 : Blo 1232434 3123643 := bstep (se 1 (by rfl) ⟨2342732, by rfl⟩ : syracuseStep 3123643 = 4685465) B4685465
theorem B1976809 : Blo 1232434 1976809 := bstep (se 2 (by rfl) ⟨741303, by rfl⟩ : syracuseStep 1976809 = 1482607) B1482607
theorem B37980733 : Blo 1232434 37980733 := bstep (se 3 (by rfl) ⟨7121387, by rfl⟩ : syracuseStep 37980733 = 14242775) B14242775
theorem B4164263 : Blo 1232434 4164263 := bstep (se 1 (by rfl) ⟨3123197, by rfl⟩ : syracuseStep 4164263 = 6246395) B6246395
theorem B6245099 : Blo 1232434 6245099 := bstep (se 1 (by rfl) ⟨4683824, by rfl⟩ : syracuseStep 6245099 = 9367649) B9367649
theorem B4221737 : Blo 1232434 4221737 := bstep (se 2 (by rfl) ⟨1583151, by rfl⟩ : syracuseStep 4221737 = 3166303) B3166303
theorem B31624019 : Blo 1232434 31624019 := bstep (se 1 (by rfl) ⟨23718014, by rfl⟩ : syracuseStep 31624019 = 47436029) B47436029
theorem B3951517 : Blo 1232434 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B1756127 : Blo 1232434 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B7900163 : Blo 1232434 7900163 := bstep (se 1 (by rfl) ⟨5925122, by rfl⟩ : syracuseStep 7900163 = 11850245) B11850245
theorem B1756571 : Blo 1232434 1756571 := bstep (se 1 (by rfl) ⟨1317428, by rfl⟩ : syracuseStep 1756571 = 2634857) B2634857
theorem B32050727 : Blo 1232434 32050727 := bstep (se 1 (by rfl) ⟨24038045, by rfl⟩ : syracuseStep 32050727 = 48076091) B48076091
theorem B3509851 : Blo 1232434 3509851 := bstep (se 1 (by rfl) ⟨2632388, by rfl⟩ : syracuseStep 3509851 = 5264777) B5264777
theorem B1232495 : Blo 1232434 1232495 := bstep (se 1 (by rfl) ⟨924371, by rfl⟩ : syracuseStep 1232495 = 1848743) B1848743
theorem B6246071 : Blo 1232434 6246071 := bstep (se 1 (by rfl) ⟨4684553, by rfl⟩ : syracuseStep 6246071 = 9369107) B9369107
theorem B1232615 : Blo 1232434 1232615 := bstep (se 1 (by rfl) ⟨924461, by rfl⟩ : syracuseStep 1232615 = 1848923) B1848923
theorem B14995439 : Blo 1232434 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B1232923 : Blo 1232434 1232923 := bstep (se 1 (by rfl) ⟨924692, by rfl⟩ : syracuseStep 1232923 = 1849385) B1849385
theorem B4681759 : Blo 1232434 4681759 := bstep (se 1 (by rfl) ⟨3511319, by rfl⟩ : syracuseStep 4681759 = 7022639) B7022639
theorem B1232943 : Blo 1232434 1232943 := bstep (se 1 (by rfl) ⟨924707, by rfl⟩ : syracuseStep 1232943 = 1849415) B1849415
theorem B11251835 : Blo 1232434 11251835 := bstep (se 1 (by rfl) ⟨8438876, by rfl⟩ : syracuseStep 11251835 = 16877753) B16877753
theorem B1560703 : Blo 1232434 1560703 := bstep (se 1 (by rfl) ⟨1170527, by rfl⟩ : syracuseStep 1560703 = 2341055) B2341055
theorem B2773223 : Blo 1232434 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B1233199 : Blo 1232434 1233199 := bstep (se 1 (by rfl) ⟨924899, by rfl⟩ : syracuseStep 1233199 = 1849799) B1849799
theorem B4747643 : Blo 1232434 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B2773403 : Blo 1232434 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B4166045 : Blo 1232434 4166045 := bstep (se 3 (by rfl) ⟨781133, by rfl⟩ : syracuseStep 4166045 = 1562267) B1562267
theorem B1233343 : Blo 1232434 1233343 := bstep (se 1 (by rfl) ⟨925007, by rfl⟩ : syracuseStep 1233343 = 1850015) B1850015
theorem B2961947 : Blo 1232434 2961947 := bstep (se 1 (by rfl) ⟨2221460, by rfl⟩ : syracuseStep 2961947 = 4442921) B4442921
theorem B1233439 : Blo 1232434 1233439 := bstep (se 1 (by rfl) ⟨925079, by rfl⟩ : syracuseStep 1233439 = 1850159) B1850159
theorem B1233519 : Blo 1232434 1233519 := bstep (se 1 (by rfl) ⟨925139, by rfl⟩ : syracuseStep 1233519 = 1850279) B1850279
theorem B1233639 : Blo 1232434 1233639 := bstep (se 1 (by rfl) ⟨925229, by rfl⟩ : syracuseStep 1233639 = 1850459) B1850459
theorem B81105725 : Blo 1232434 81105725 := bstep (se 3 (by rfl) ⟨15207323, by rfl⟩ : syracuseStep 81105725 = 30414647) B30414647
theorem B1233887 : Blo 1232434 1233887 := bstep (se 1 (by rfl) ⟨925415, by rfl⟩ : syracuseStep 1233887 = 1850831) B1850831
theorem B9360359 : Blo 1232434 9360359 := bstep (se 1 (by rfl) ⟨7020269, by rfl⟩ : syracuseStep 9360359 = 14040539) B14040539
theorem B6247529 : Blo 1232434 6247529 := bstep (se 2 (by rfl) ⟨2342823, by rfl⟩ : syracuseStep 6247529 = 4685647) B4685647
theorem B11244683 : Blo 1232434 11244683 := bstep (se 1 (by rfl) ⟨8433512, by rfl⟩ : syracuseStep 11244683 = 16867025) B16867025
theorem B1234143 : Blo 1232434 1234143 := bstep (se 1 (by rfl) ⟨925607, by rfl⟩ : syracuseStep 1234143 = 1851215) B1851215
theorem B12014891 : Blo 1232434 12014891 := bstep (se 1 (by rfl) ⟨9011168, by rfl⟩ : syracuseStep 12014891 = 18022337) B18022337
theorem B1234223 : Blo 1232434 1234223 := bstep (se 1 (by rfl) ⟨925667, by rfl⟩ : syracuseStep 1234223 = 1851335) B1851335
theorem B6248015 : Blo 1232434 6248015 := bstep (se 1 (by rfl) ⟨4686011, by rfl⟩ : syracuseStep 6248015 = 9372023) B9372023
theorem B4216481 : Blo 1232434 4216481 := bstep (se 2 (by rfl) ⟨1581180, by rfl⟩ : syracuseStep 4216481 = 3162361) B3162361
theorem B6239915 : Blo 1232434 6239915 := bstep (se 1 (by rfl) ⟨4679936, by rfl⟩ : syracuseStep 6239915 = 9359873) B9359873
theorem B1849211 : Blo 1232434 1849211 := bstep (se 1 (by rfl) ⟨1386908, by rfl⟩ : syracuseStep 1849211 = 2773817) B2773817
theorem B1849247 : Blo 1232434 1849247 := bstep (se 1 (by rfl) ⟨1386935, by rfl⟩ : syracuseStep 1849247 = 2773871) B2773871
theorem B1849451 : Blo 1232434 1849451 := bstep (se 1 (by rfl) ⟨1387088, by rfl⟩ : syracuseStep 1849451 = 2774177) B2774177
theorem B2340971 : Blo 1232434 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B1849481 : Blo 1232434 1849481 := bstep (se 2 (by rfl) ⟨693555, by rfl⟩ : syracuseStep 1849481 = 1387111) B1387111
theorem B2341001 : Blo 1232434 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B6666455 : Blo 1232434 6666455 := bstep (se 1 (by rfl) ⟨4999841, by rfl⟩ : syracuseStep 6666455 = 9999683) B9999683
theorem B1849631 : Blo 1232434 1849631 := bstep (se 1 (by rfl) ⟨1387223, by rfl⟩ : syracuseStep 1849631 = 2774447) B2774447
theorem B6666695 : Blo 1232434 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B6248987 : Blo 1232434 6248987 := bstep (se 1 (by rfl) ⟨4686740, by rfl⟩ : syracuseStep 6248987 = 9373481) B9373481
theorem B25328375 : Blo 1232434 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B3119897 : Blo 1232434 3119897 := bstep (se 2 (by rfl) ⟨1169961, by rfl⟩ : syracuseStep 3119897 = 2339923) B2339923
theorem B2775977 : Blo 1232434 2775977 := bstep (se 2 (by rfl) ⟨1040991, by rfl⟩ : syracuseStep 2775977 = 2081983) B2081983
theorem B1850303 : Blo 1232434 1850303 := bstep (se 1 (by rfl) ⟨1387727, by rfl⟩ : syracuseStep 1850303 = 2775455) B2775455
theorem B1850351 : Blo 1232434 1850351 := bstep (se 1 (by rfl) ⟨1387763, by rfl⟩ : syracuseStep 1850351 = 2775527) B2775527
theorem B7904263 : Blo 1232434 7904263 := bstep (se 1 (by rfl) ⟨5928197, by rfl⟩ : syracuseStep 7904263 = 11856395) B11856395
theorem B43293761 : Blo 1232434 43293761 := bstep (se 2 (by rfl) ⟨16235160, by rfl⟩ : syracuseStep 43293761 = 32470321) B32470321
theorem B5627015 : Blo 1232434 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B1850537 : Blo 1232434 1850537 := bstep (se 2 (by rfl) ⟨693951, by rfl⟩ : syracuseStep 1850537 = 1387903) B1387903
theorem B3333467 : Blo 1232434 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B1850927 : Blo 1232434 1850927 := bstep (se 1 (by rfl) ⟨1388195, by rfl⟩ : syracuseStep 1850927 = 2776391) B2776391
theorem B1850951 : Blo 1232434 1850951 := bstep (se 1 (by rfl) ⟨1388213, by rfl⟩ : syracuseStep 1850951 = 2776427) B2776427
theorem B4161131 : Blo 1232434 4161131 := bstep (se 1 (by rfl) ⟨3120848, by rfl⟩ : syracuseStep 4161131 = 6241697) B6241697
theorem B1851035 : Blo 1232434 1851035 := bstep (se 1 (by rfl) ⟨1388276, by rfl⟩ : syracuseStep 1851035 = 2776553) B2776553
theorem B1851131 : Blo 1232434 1851131 := bstep (se 1 (by rfl) ⟨1388348, by rfl⟩ : syracuseStep 1851131 = 2776697) B2776697
theorem B1523615 : Blo 1232434 1523615 := bstep (se 1 (by rfl) ⟨1142711, by rfl⟩ : syracuseStep 1523615 = 2285423) B2285423
theorem B1851419 : Blo 1232434 1851419 := bstep (se 1 (by rfl) ⟨1388564, by rfl⟩ : syracuseStep 1851419 = 2777129) B2777129
theorem B6242345 : Blo 1232434 6242345 := bstep (se 2 (by rfl) ⟨2340879, by rfl⟩ : syracuseStep 6242345 = 4681759) B4681759
theorem B4685951 : Blo 1232434 4685951 := bstep (se 1 (by rfl) ⟨3514463, by rfl⟩ : syracuseStep 4685951 = 7028927) B7028927
theorem B13328549 : Blo 1232434 13328549 := bstep (se 4 (by rfl) ⟨1249551, by rfl⟩ : syracuseStep 13328549 = 2499103) B2499103
theorem B2080937 : Blo 1232434 2080937 := bstep (se 2 (by rfl) ⟨780351, by rfl⟩ : syracuseStep 2080937 = 1560703) B1560703
theorem B2777363 : Blo 1232434 2777363 := bstep (se 1 (by rfl) ⟨2083022, by rfl⟩ : syracuseStep 2777363 = 4166045) B4166045
theorem B1974631 : Blo 1232434 1974631 := bstep (se 1 (by rfl) ⟨1480973, by rfl⟩ : syracuseStep 1974631 = 2961947) B2961947
theorem B6242669 : Blo 1232434 6242669 := bstep (se 3 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 6242669 = 2341001) B2341001
theorem B6242831 : Blo 1232434 6242831 := bstep (se 1 (by rfl) ⟨4682123, by rfl⟩ : syracuseStep 6242831 = 9364247) B9364247
theorem B2081423 : Blo 1232434 2081423 := bstep (se 1 (by rfl) ⟨1561067, by rfl⟩ : syracuseStep 2081423 = 3122135) B3122135
theorem B2810987 : Blo 1232434 2810987 := bstep (se 1 (by rfl) ⟨2108240, by rfl⟩ : syracuseStep 2810987 = 4216481) B4216481
theorem B5268689 : Blo 1232434 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B2082395 : Blo 1232434 2082395 := bstep (se 1 (by rfl) ⟨1561796, by rfl⟩ : syracuseStep 2082395 = 3123593) B3123593
theorem B4163399 : Blo 1232434 4163399 := bstep (se 1 (by rfl) ⟨3122549, by rfl⟩ : syracuseStep 4163399 = 6245099) B6245099
theorem B16885583 : Blo 1232434 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B28862507 : Blo 1232434 28862507 := bstep (se 1 (by rfl) ⟨21646880, by rfl⟩ : syracuseStep 28862507 = 43293761) B43293761
theorem B4679801 : Blo 1232434 4679801 := bstep (se 2 (by rfl) ⟨1754925, by rfl⟩ : syracuseStep 4679801 = 3509851) B3509851
theorem B2222311 : Blo 1232434 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B21367151 : Blo 1232434 21367151 := bstep (se 1 (by rfl) ⟨16025363, by rfl⟩ : syracuseStep 21367151 = 32050727) B32050727
theorem B4164047 : Blo 1232434 4164047 := bstep (se 1 (by rfl) ⟨3123035, by rfl⟩ : syracuseStep 4164047 = 6246071) B6246071
theorem B4680301 : Blo 1232434 4680301 := bstep (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) B1755113
theorem B9996959 : Blo 1232434 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B3124079 : Blo 1232434 3124079 := bstep (se 1 (by rfl) ⟨2343059, by rfl⟩ : syracuseStep 3124079 = 4686119) B4686119
theorem B3165095 : Blo 1232434 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B29985821 : Blo 1232434 29985821 := bstep (se 3 (by rfl) ⟨5622341, by rfl⟩ : syracuseStep 29985821 = 11244683) B11244683
theorem B1387687 : Blo 1232434 1387687 := bstep (se 1 (by rfl) ⟨1040765, by rfl⟩ : syracuseStep 1387687 = 2081531) B2081531
theorem B54070483 : Blo 1232434 54070483 := bstep (se 1 (by rfl) ⟨40552862, by rfl⟩ : syracuseStep 54070483 = 81105725) B81105725
theorem B4164857 : Blo 1232434 4164857 := bstep (se 2 (by rfl) ⟨1561821, by rfl⟩ : syracuseStep 4164857 = 3123643) B3123643
theorem B4165019 : Blo 1232434 4165019 := bstep (se 1 (by rfl) ⟨3123764, by rfl⟩ : syracuseStep 4165019 = 6247529) B6247529
theorem B21065183 : Blo 1232434 21065183 := bstep (se 1 (by rfl) ⟨15798887, by rfl⟩ : syracuseStep 21065183 = 31597775) B31597775
theorem B4165343 : Blo 1232434 4165343 := bstep (se 1 (by rfl) ⟨3124007, by rfl⟩ : syracuseStep 4165343 = 6248015) B6248015
theorem B1232807 : Blo 1232434 1232807 := bstep (se 1 (by rfl) ⟨924605, by rfl⟩ : syracuseStep 1232807 = 1849211) B1849211
theorem B1232831 : Blo 1232434 1232831 := bstep (se 1 (by rfl) ⟨924623, by rfl⟩ : syracuseStep 1232831 = 1849247) B1849247
theorem B10539017 : Blo 1232434 10539017 := bstep (se 2 (by rfl) ⟨3952131, by rfl⟩ : syracuseStep 10539017 = 7904263) B7904263
theorem B1232967 : Blo 1232434 1232967 := bstep (se 1 (by rfl) ⟨924725, by rfl⟩ : syracuseStep 1232967 = 1849451) B1849451
theorem B1560647 : Blo 1232434 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B1232987 : Blo 1232434 1232987 := bstep (se 1 (by rfl) ⟨924740, by rfl⟩ : syracuseStep 1232987 = 1849481) B1849481
theorem B4444303 : Blo 1232434 4444303 := bstep (se 1 (by rfl) ⟨3333227, by rfl⟩ : syracuseStep 4444303 = 6666455) B6666455
theorem B1233087 : Blo 1232434 1233087 := bstep (se 1 (by rfl) ⟨924815, by rfl⟩ : syracuseStep 1233087 = 1849631) B1849631
theorem B1667327 : Blo 1232434 1667327 := bstep (se 1 (by rfl) ⟨1250495, by rfl⟩ : syracuseStep 1667327 = 2500991) B2500991
theorem B4444463 : Blo 1232434 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B4165991 : Blo 1232434 4165991 := bstep (se 1 (by rfl) ⟨3124493, by rfl⟩ : syracuseStep 4165991 = 6248987) B6248987
theorem B2814491 : Blo 1232434 2814491 := bstep (se 1 (by rfl) ⟨2110868, by rfl⟩ : syracuseStep 2814491 = 4221737) B4221737
theorem B21082679 : Blo 1232434 21082679 := bstep (se 1 (by rfl) ⟨15812009, by rfl⟩ : syracuseStep 21082679 = 31624019) B31624019
theorem B1233535 : Blo 1232434 1233535 := bstep (se 1 (by rfl) ⟨925151, by rfl⟩ : syracuseStep 1233535 = 1850303) B1850303
theorem B1233567 : Blo 1232434 1233567 := bstep (se 1 (by rfl) ⟨925175, by rfl⟩ : syracuseStep 1233567 = 1850351) B1850351
theorem B1233691 : Blo 1232434 1233691 := bstep (se 1 (by rfl) ⟨925268, by rfl⟩ : syracuseStep 1233691 = 1850537) B1850537
theorem B1233951 : Blo 1232434 1233951 := bstep (se 1 (by rfl) ⟨925463, by rfl⟩ : syracuseStep 1233951 = 1850927) B1850927
theorem B1233967 : Blo 1232434 1233967 := bstep (se 1 (by rfl) ⟨925475, by rfl⟩ : syracuseStep 1233967 = 1850951) B1850951
theorem B2774087 : Blo 1232434 2774087 := bstep (se 1 (by rfl) ⟨2080565, by rfl⟩ : syracuseStep 2774087 = 4161131) B4161131
theorem B1234023 : Blo 1232434 1234023 := bstep (se 1 (by rfl) ⟨925517, by rfl⟩ : syracuseStep 1234023 = 1851035) B1851035
theorem B1234087 : Blo 1232434 1234087 := bstep (se 1 (by rfl) ⟨925565, by rfl⟩ : syracuseStep 1234087 = 1851131) B1851131
theorem B4683005 : Blo 1232434 4683005 := bstep (se 3 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 4683005 = 1756127) B1756127
theorem B7501223 : Blo 1232434 7501223 := bstep (se 1 (by rfl) ⟨5625917, by rfl⟩ : syracuseStep 7501223 = 11251835) B11251835
theorem B3511775 : Blo 1232434 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B1234399 : Blo 1232434 1234399 := bstep (se 1 (by rfl) ⟨925799, by rfl⟩ : syracuseStep 1234399 = 1851599) B1851599
theorem B1848815 : Blo 1232434 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B1848935 : Blo 1232434 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B3331963 : Blo 1232434 3331963 := bstep (se 1 (by rfl) ⟨2498972, by rfl⟩ : syracuseStep 3331963 = 4997945) B4997945
theorem B2635745 : Blo 1232434 2635745 := bstep (se 2 (by rfl) ⟨988404, by rfl⟩ : syracuseStep 2635745 = 1976809) B1976809
theorem B6240239 : Blo 1232434 6240239 := bstep (se 1 (by rfl) ⟨4680179, by rfl⟩ : syracuseStep 6240239 = 9360359) B9360359
theorem B50640977 : Blo 1232434 50640977 := bstep (se 2 (by rfl) ⟨18990366, by rfl⟩ : syracuseStep 50640977 = 37980733) B37980733
theorem B2775167 : Blo 1232434 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B8009927 : Blo 1232434 8009927 := bstep (se 1 (by rfl) ⟨6007445, by rfl⟩ : syracuseStep 8009927 = 12014891) B12014891
theorem B6248663 : Blo 1232434 6248663 := bstep (se 1 (by rfl) ⟨4686497, by rfl⟩ : syracuseStep 6248663 = 9372995) B9372995
theorem B4684189 : Blo 1232434 4684189 := bstep (se 3 (by rfl) ⟨878285, by rfl⟩ : syracuseStep 4684189 = 1756571) B1756571
theorem B4159943 : Blo 1232434 4159943 := bstep (se 1 (by rfl) ⟨3119957, by rfl⟩ : syracuseStep 4159943 = 6239915) B6239915
theorem B29989511 : Blo 1232434 29989511 := bstep (se 1 (by rfl) ⟨22492133, by rfl⟩ : syracuseStep 29989511 = 44984267) B44984267
theorem B5003963 : Blo 1232434 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B16251893 : Blo 1232434 16251893 := bstep (se 5 (by rfl) ⟨761807, by rfl⟩ : syracuseStep 16251893 = 1523615) B1523615
theorem B2776175 : Blo 1232434 2776175 := bstep (se 1 (by rfl) ⟨2082131, by rfl⟩ : syracuseStep 2776175 = 4164263) B4164263
theorem B2079931 : Blo 1232434 2079931 := bstep (se 1 (by rfl) ⟨1559948, by rfl⟩ : syracuseStep 2079931 = 3119897) B3119897
theorem B1850651 : Blo 1232434 1850651 := bstep (se 1 (by rfl) ⟨1387988, by rfl⟩ : syracuseStep 1850651 = 2775977) B2775977
theorem B5266775 : Blo 1232434 5266775 := bstep (se 1 (by rfl) ⟨3950081, by rfl⟩ : syracuseStep 5266775 = 7900163) B7900163
theorem B3751343 : Blo 1232434 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B31637141 : Blo 1232434 31637141 := bstep (se 6 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 31637141 = 1482991) B1482991
theorem B2777057 : Blo 1232434 2777057 := bstep (se 2 (by rfl) ⟨1041396, by rfl⟩ : syracuseStep 2777057 = 2082793) B2082793
theorem B4161563 : Blo 1232434 4161563 := bstep (se 1 (by rfl) ⟨3121172, by rfl⟩ : syracuseStep 4161563 = 6242345) B6242345
theorem B1851575 : Blo 1232434 1851575 := bstep (se 1 (by rfl) ⟨1388681, by rfl⟩ : syracuseStep 1851575 = 2777363) B2777363
theorem B4161725 : Blo 1232434 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B2777327 : Blo 1232434 2777327 := bstep (se 1 (by rfl) ⟨2082995, by rfl⟩ : syracuseStep 2777327 = 4165991) B4165991
theorem B4161779 : Blo 1232434 4161779 := bstep (se 1 (by rfl) ⟨3121334, by rfl⟩ : syracuseStep 4161779 = 6242669) B6242669
theorem B4161887 : Blo 1232434 4161887 := bstep (se 1 (by rfl) ⟨3121415, by rfl⟩ : syracuseStep 4161887 = 6242831) B6242831
theorem B1876327 : Blo 1232434 1876327 := bstep (se 1 (by rfl) ⟨1407245, by rfl⟩ : syracuseStep 1876327 = 2814491) B2814491
theorem B3122003 : Blo 1232434 3122003 := bstep (se 1 (by rfl) ⟨2341502, by rfl⟩ : syracuseStep 3122003 = 4683005) B4683005
theorem B29983861 : Blo 1232434 29983861 := bstep (se 5 (by rfl) ⟨1405493, by rfl⟩ : syracuseStep 29983861 = 2810987) B2810987
theorem B11257055 : Blo 1232434 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B9364733 : Blo 1232434 9364733 := bstep (se 3 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 9364733 = 3511775) B3511775
theorem B33760651 : Blo 1232434 33760651 := bstep (se 1 (by rfl) ⟨25320488, by rfl⟩ : syracuseStep 33760651 = 50640977) B50640977
theorem B3335975 : Blo 1232434 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B2082719 : Blo 1232434 2082719 := bstep (se 1 (by rfl) ⟨1562039, by rfl⟩ : syracuseStep 2082719 = 3124079) B3124079
theorem B19990547 : Blo 1232434 19990547 := bstep (se 1 (by rfl) ⟨14992910, by rfl⟩ : syracuseStep 19990547 = 29985821) B29985821
theorem B2500895 : Blo 1232434 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B14043455 : Blo 1232434 14043455 := bstep (se 1 (by rfl) ⟨10532591, by rfl⟩ : syracuseStep 14043455 = 21065183) B21065183
theorem B4442617 : Blo 1232434 4442617 := bstep (se 2 (by rfl) ⟨1665981, by rfl⟩ : syracuseStep 4442617 = 3331963) B3331963
theorem B3123967 : Blo 1232434 3123967 := bstep (se 1 (by rfl) ⟨2342975, by rfl⟩ : syracuseStep 3123967 = 4685951) B4685951
theorem B1387291 : Blo 1232434 1387291 := bstep (se 1 (by rfl) ⟨1040468, by rfl⟩ : syracuseStep 1387291 = 2080937) B2080937
theorem B5925737 : Blo 1232434 5925737 := bstep (se 2 (by rfl) ⟨2222151, by rfl⟩ : syracuseStep 5925737 = 4444303) B4444303
theorem B1387615 : Blo 1232434 1387615 := bstep (se 1 (by rfl) ⟨1040711, by rfl⟩ : syracuseStep 1387615 = 2081423) B2081423
theorem B2632841 : Blo 1232434 2632841 := bstep (se 2 (by rfl) ⟨987315, by rfl⟩ : syracuseStep 2632841 = 1974631) B1974631
theorem B6245585 : Blo 1232434 6245585 := bstep (se 2 (by rfl) ⟨2342094, by rfl⟩ : syracuseStep 6245585 = 4684189) B4684189
theorem B5000815 : Blo 1232434 5000815 := bstep (se 1 (by rfl) ⟨3750611, by rfl⟩ : syracuseStep 5000815 = 7501223) B7501223
theorem B1232543 : Blo 1232434 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B1388263 : Blo 1232434 1388263 := bstep (se 1 (by rfl) ⟨1041197, by rfl⟩ : syracuseStep 1388263 = 2082395) B2082395
theorem B1232623 : Blo 1232434 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B4165775 : Blo 1232434 4165775 := bstep (se 1 (by rfl) ⟨3124331, by rfl⟩ : syracuseStep 4165775 = 6248663) B6248663
theorem B2773241 : Blo 1232434 2773241 := bstep (se 2 (by rfl) ⟨1039965, by rfl⟩ : syracuseStep 2773241 = 2079931) B2079931
theorem B72093977 : Blo 1232434 72093977 := bstep (se 2 (by rfl) ⟨27035241, by rfl⟩ : syracuseStep 72093977 = 54070483) B54070483
theorem B2773295 : Blo 1232434 2773295 := bstep (se 1 (by rfl) ⟨2079971, by rfl⟩ : syracuseStep 2773295 = 4159943) B4159943
theorem B19993007 : Blo 1232434 19993007 := bstep (se 1 (by rfl) ⟨14994755, by rfl⟩ : syracuseStep 19993007 = 29989511) B29989511
theorem B6664639 : Blo 1232434 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B2110063 : Blo 1232434 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B10834595 : Blo 1232434 10834595 := bstep (se 1 (by rfl) ⟨8125946, by rfl⟩ : syracuseStep 10834595 = 16251893) B16251893
theorem B1233767 : Blo 1232434 1233767 := bstep (se 1 (by rfl) ⟨925325, by rfl⟩ : syracuseStep 1233767 = 1850651) B1850651
theorem B3511183 : Blo 1232434 3511183 := bstep (se 1 (by rfl) ⟨2633387, by rfl⟩ : syracuseStep 3511183 = 5266775) B5266775
theorem B21091427 : Blo 1232434 21091427 := bstep (se 1 (by rfl) ⟨15818570, by rfl⟩ : syracuseStep 21091427 = 31637141) B31637141
theorem B7026011 : Blo 1232434 7026011 := bstep (se 1 (by rfl) ⟨5269508, by rfl⟩ : syracuseStep 7026011 = 10539017) B10539017
theorem B1234279 : Blo 1232434 1234279 := bstep (se 1 (by rfl) ⟨925709, by rfl⟩ : syracuseStep 1234279 = 1851419) B1851419
theorem B8885699 : Blo 1232434 8885699 := bstep (se 1 (by rfl) ⟨6664274, by rfl⟩ : syracuseStep 8885699 = 13328549) B13328549
theorem B2962975 : Blo 1232434 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B2963081 : Blo 1232434 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B14055119 : Blo 1232434 14055119 := bstep (se 1 (by rfl) ⟨10541339, by rfl⟩ : syracuseStep 14055119 = 21082679) B21082679
theorem B1849391 : Blo 1232434 1849391 := bstep (se 1 (by rfl) ⟨1387043, by rfl⟩ : syracuseStep 1849391 = 2774087) B2774087
theorem B3512459 : Blo 1232434 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B6240401 : Blo 1232434 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B2775599 : Blo 1232434 2775599 := bstep (se 1 (by rfl) ⟨2081699, by rfl⟩ : syracuseStep 2775599 = 4163399) B4163399
theorem B4160159 : Blo 1232434 4160159 := bstep (se 1 (by rfl) ⟨3120119, by rfl⟩ : syracuseStep 4160159 = 6240239) B6240239
theorem B19241671 : Blo 1232434 19241671 := bstep (se 1 (by rfl) ⟨14431253, by rfl⟩ : syracuseStep 19241671 = 28862507) B28862507
theorem B3119867 : Blo 1232434 3119867 := bstep (se 1 (by rfl) ⟨2339900, by rfl⟩ : syracuseStep 3119867 = 4679801) B4679801
theorem B1850111 : Blo 1232434 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B5339951 : Blo 1232434 5339951 := bstep (se 1 (by rfl) ⟨4004963, by rfl⟩ : syracuseStep 5339951 = 8009927) B8009927
theorem B1850249 : Blo 1232434 1850249 := bstep (se 2 (by rfl) ⟨693843, by rfl⟩ : syracuseStep 1850249 = 1387687) B1387687
theorem B14244767 : Blo 1232434 14244767 := bstep (se 1 (by rfl) ⟨10683575, by rfl⟩ : syracuseStep 14244767 = 21367151) B21367151
theorem B2776031 : Blo 1232434 2776031 := bstep (se 1 (by rfl) ⟨2082023, by rfl⟩ : syracuseStep 2776031 = 4164047) B4164047
theorem B1850783 : Blo 1232434 1850783 := bstep (se 1 (by rfl) ⟨1388087, by rfl⟩ : syracuseStep 1850783 = 2776175) B2776175
theorem B2776571 : Blo 1232434 2776571 := bstep (se 1 (by rfl) ⟨2082428, by rfl⟩ : syracuseStep 2776571 = 4164857) B4164857
theorem B2776679 : Blo 1232434 2776679 := bstep (se 1 (by rfl) ⟨2082509, by rfl⟩ : syracuseStep 2776679 = 4165019) B4165019
theorem B2776895 : Blo 1232434 2776895 := bstep (se 1 (by rfl) ⟨2082671, by rfl⟩ : syracuseStep 2776895 = 4165343) B4165343
theorem B7028653 : Blo 1232434 7028653 := bstep (se 3 (by rfl) ⟨1317872, by rfl⟩ : syracuseStep 7028653 = 2635745) B2635745
theorem B1851371 : Blo 1232434 1851371 := bstep (se 1 (by rfl) ⟨1388528, by rfl⟩ : syracuseStep 1851371 = 2777057) B2777057
theorem B17784821 : Blo 1232434 17784821 := bstep (se 5 (by rfl) ⟨833663, by rfl⟩ : syracuseStep 17784821 = 1667327) B1667327
theorem B2777183 : Blo 1232434 2777183 := bstep (se 1 (by rfl) ⟨2082887, by rfl⟩ : syracuseStep 2777183 = 4165775) B4165775
theorem B1851551 : Blo 1232434 1851551 := bstep (se 1 (by rfl) ⟨1388663, by rfl⟩ : syracuseStep 1851551 = 2777327) B2777327
theorem B48062651 : Blo 1232434 48062651 := bstep (se 1 (by rfl) ⟨36046988, by rfl⟩ : syracuseStep 48062651 = 72093977) B72093977
theorem B2081335 : Blo 1232434 2081335 := bstep (se 1 (by rfl) ⟨1561001, by rfl⟩ : syracuseStep 2081335 = 3122003) B3122003
theorem B6669053 : Blo 1232434 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B7504703 : Blo 1232434 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B6243155 : Blo 1232434 6243155 := bstep (se 1 (by rfl) ⟨4682366, by rfl⟩ : syracuseStep 6243155 = 9364733) B9364733
theorem B5923799 : Blo 1232434 5923799 := bstep (se 1 (by rfl) ⟨4442849, by rfl⟩ : syracuseStep 5923799 = 8885699) B8885699
theorem B53314685 : Blo 1232434 53314685 := bstep (se 3 (by rfl) ⟨9996503, by rfl⟩ : syracuseStep 53314685 = 19993007) B19993007
theorem B39978481 : Blo 1232434 39978481 := bstep (se 2 (by rfl) ⟨14991930, by rfl⟩ : syracuseStep 39978481 = 29983861) B29983861
theorem B9496511 : Blo 1232434 9496511 := bstep (se 1 (by rfl) ⟨7122383, by rfl⟩ : syracuseStep 9496511 = 14244767) B14244767
theorem B3950633 : Blo 1232434 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B1755227 : Blo 1232434 1755227 := bstep (se 1 (by rfl) ⟨1316420, by rfl⟩ : syracuseStep 1755227 = 2632841) B2632841
theorem B4163723 : Blo 1232434 4163723 := bstep (se 1 (by rfl) ⟨3122792, by rfl⟩ : syracuseStep 4163723 = 6245585) B6245585
theorem B23693957 : Blo 1232434 23693957 := bstep (se 4 (by rfl) ⟨2221308, by rfl⟩ : syracuseStep 23693957 = 4442617) B4442617
theorem B11856547 : Blo 1232434 11856547 := bstep (se 1 (by rfl) ⟨8892410, by rfl⟩ : syracuseStep 11856547 = 17784821) B17784821
theorem B14060951 : Blo 1232434 14060951 := bstep (se 1 (by rfl) ⟨10545713, by rfl⟩ : syracuseStep 14060951 = 21091427) B21091427
theorem B2813417 : Blo 1232434 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B4165289 : Blo 1232434 4165289 := bstep (se 2 (by rfl) ⟨1561983, by rfl⟩ : syracuseStep 4165289 = 3123967) B3123967
theorem B4681577 : Blo 1232434 4681577 := bstep (se 2 (by rfl) ⟨1755591, by rfl⟩ : syracuseStep 4681577 = 3511183) B3511183
theorem B2223983 : Blo 1232434 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B1388479 : Blo 1232434 1388479 := bstep (se 1 (by rfl) ⟨1041359, by rfl⟩ : syracuseStep 1388479 = 2082719) B2082719
theorem B1232927 : Blo 1232434 1232927 := bstep (se 1 (by rfl) ⟨924695, by rfl⟩ : syracuseStep 1232927 = 1849391) B1849391
theorem B7901549 : Blo 1232434 7901549 := bstep (se 3 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 7901549 = 2963081) B2963081
theorem B2773439 : Blo 1232434 2773439 := bstep (se 1 (by rfl) ⟨2080079, by rfl⟩ : syracuseStep 2773439 = 4160159) B4160159
theorem B1233407 : Blo 1232434 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B3559967 : Blo 1232434 3559967 := bstep (se 1 (by rfl) ⟨2669975, by rfl⟩ : syracuseStep 3559967 = 5339951) B5339951
theorem B10007077 : Blo 1232434 10007077 := bstep (se 4 (by rfl) ⟨938163, by rfl⟩ : syracuseStep 10007077 = 1876327) B1876327
theorem B1233499 : Blo 1232434 1233499 := bstep (se 1 (by rfl) ⟨925124, by rfl⟩ : syracuseStep 1233499 = 1850249) B1850249
theorem B1233855 : Blo 1232434 1233855 := bstep (se 1 (by rfl) ⟨925391, by rfl⟩ : syracuseStep 1233855 = 1850783) B1850783
theorem B1234247 : Blo 1232434 1234247 := bstep (se 1 (by rfl) ⟨925685, by rfl⟩ : syracuseStep 1234247 = 1851371) B1851371
theorem B2774375 : Blo 1232434 2774375 := bstep (se 1 (by rfl) ⟨2080781, by rfl⟩ : syracuseStep 2774375 = 4161563) B4161563
theorem B1234383 : Blo 1232434 1234383 := bstep (se 1 (by rfl) ⟨925787, by rfl⟩ : syracuseStep 1234383 = 1851575) B1851575
theorem B2774483 : Blo 1232434 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B2774519 : Blo 1232434 2774519 := bstep (se 1 (by rfl) ⟨2080889, by rfl⟩ : syracuseStep 2774519 = 4161779) B4161779
theorem B1848827 : Blo 1232434 1848827 := bstep (se 1 (by rfl) ⟨1386620, by rfl⟩ : syracuseStep 1848827 = 2773241) B2773241
theorem B1848863 : Blo 1232434 1848863 := bstep (se 1 (by rfl) ⟨1386647, by rfl⟩ : syracuseStep 1848863 = 2773295) B2773295
theorem B2774591 : Blo 1232434 2774591 := bstep (se 1 (by rfl) ⟨2080943, by rfl⟩ : syracuseStep 2774591 = 4161887) B4161887
theorem B7223063 : Blo 1232434 7223063 := bstep (se 1 (by rfl) ⟨5417297, by rfl⟩ : syracuseStep 7223063 = 10834595) B10834595
theorem B8886185 : Blo 1232434 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B4684007 : Blo 1232434 4684007 := bstep (se 1 (by rfl) ⟨3513005, by rfl⟩ : syracuseStep 4684007 = 7026011) B7026011
theorem B25655561 : Blo 1232434 25655561 := bstep (se 2 (by rfl) ⟨9620835, by rfl⟩ : syracuseStep 25655561 = 19241671) B19241671
theorem B1849721 : Blo 1232434 1849721 := bstep (se 2 (by rfl) ⟨693645, by rfl⟩ : syracuseStep 1849721 = 1387291) B1387291
theorem B9370079 : Blo 1232434 9370079 := bstep (se 1 (by rfl) ⟨7027559, by rfl⟩ : syracuseStep 9370079 = 14055119) B14055119
theorem B13327031 : Blo 1232434 13327031 := bstep (se 1 (by rfl) ⟨9995273, by rfl⟩ : syracuseStep 13327031 = 19990547) B19990547
theorem B2341639 : Blo 1232434 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B4160267 : Blo 1232434 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B1850153 : Blo 1232434 1850153 := bstep (se 2 (by rfl) ⟨693807, by rfl⟩ : syracuseStep 1850153 = 1387615) B1387615
theorem B9362303 : Blo 1232434 9362303 := bstep (se 1 (by rfl) ⟨7021727, by rfl⟩ : syracuseStep 9362303 = 14043455) B14043455
theorem B1850399 : Blo 1232434 1850399 := bstep (se 1 (by rfl) ⟨1387799, by rfl⟩ : syracuseStep 1850399 = 2775599) B2775599
theorem B2079911 : Blo 1232434 2079911 := bstep (se 1 (by rfl) ⟨1559933, by rfl⟩ : syracuseStep 2079911 = 3119867) B3119867
theorem B45014201 : Blo 1232434 45014201 := bstep (se 2 (by rfl) ⟨16880325, by rfl⟩ : syracuseStep 45014201 = 33760651) B33760651
theorem B1850687 : Blo 1232434 1850687 := bstep (se 1 (by rfl) ⟨1388015, by rfl⟩ : syracuseStep 1850687 = 2776031) B2776031
theorem B6667753 : Blo 1232434 6667753 := bstep (se 2 (by rfl) ⟨2500407, by rfl⟩ : syracuseStep 6667753 = 5000815) B5000815
theorem B15801965 : Blo 1232434 15801965 := bstep (se 3 (by rfl) ⟨2962868, by rfl⟩ : syracuseStep 15801965 = 5925737) B5925737
theorem B1851017 : Blo 1232434 1851017 := bstep (se 2 (by rfl) ⟨694131, by rfl⟩ : syracuseStep 1851017 = 1388263) B1388263
theorem B1851047 : Blo 1232434 1851047 := bstep (se 1 (by rfl) ⟨1388285, by rfl⟩ : syracuseStep 1851047 = 2776571) B2776571
theorem B1851119 : Blo 1232434 1851119 := bstep (se 1 (by rfl) ⟨1388339, by rfl⟩ : syracuseStep 1851119 = 2776679) B2776679
theorem B1851263 : Blo 1232434 1851263 := bstep (se 1 (by rfl) ⟨1388447, by rfl⟩ : syracuseStep 1851263 = 2776895) B2776895
theorem B9371537 : Blo 1232434 9371537 := bstep (se 2 (by rfl) ⟨3514326, by rfl⟩ : syracuseStep 9371537 = 7028653) B7028653
theorem B1851455 : Blo 1232434 1851455 := bstep (se 1 (by rfl) ⟨1388591, by rfl⟩ : syracuseStep 1851455 = 2777183) B2777183
theorem B10535021 : Blo 1232434 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B5267699 : Blo 1232434 5267699 := bstep (se 1 (by rfl) ⟨3950774, by rfl⟩ : syracuseStep 5267699 = 7901549) B7901549
theorem B77046005 : Blo 1232434 77046005 := bstep (se 5 (by rfl) ⟨3611531, by rfl⟩ : syracuseStep 77046005 = 7223063) B7223063
theorem B4162103 : Blo 1232434 4162103 := bstep (se 1 (by rfl) ⟨3121577, by rfl⟩ : syracuseStep 4162103 = 6243155) B6243155
theorem B3949199 : Blo 1232434 3949199 := bstep (se 1 (by rfl) ⟨2961899, by rfl⟩ : syracuseStep 3949199 = 5923799) B5923799
theorem B3122185 : Blo 1232434 3122185 := bstep (se 2 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 3122185 = 2341639) B2341639
theorem B5924123 : Blo 1232434 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B3122671 : Blo 1232434 3122671 := bstep (se 1 (by rfl) ⟨2342003, by rfl⟩ : syracuseStep 3122671 = 4684007) B4684007
theorem B15795971 : Blo 1232434 15795971 := bstep (se 1 (by rfl) ⟨11846978, by rfl⟩ : syracuseStep 15795971 = 23693957) B23693957
theorem B8890337 : Blo 1232434 8890337 := bstep (se 2 (by rfl) ⟨3333876, by rfl⟩ : syracuseStep 8890337 = 6667753) B6667753
theorem B1386607 : Blo 1232434 1386607 := bstep (se 1 (by rfl) ⟨1039955, by rfl⟩ : syracuseStep 1386607 = 2079911) B2079911
theorem B30009467 : Blo 1232434 30009467 := bstep (se 1 (by rfl) ⟨22507100, by rfl⟩ : syracuseStep 30009467 = 45014201) B45014201
theorem B9373967 : Blo 1232434 9373967 := bstep (se 1 (by rfl) ⟨7030475, by rfl⟩ : syracuseStep 9373967 = 14060951) B14060951
theorem B4680605 : Blo 1232434 4680605 := bstep (se 3 (by rfl) ⟨877613, by rfl⟩ : syracuseStep 4680605 = 1755227) B1755227
theorem B128167069 : Blo 1232434 128167069 := bstep (se 3 (by rfl) ⟨24031325, by rfl⟩ : syracuseStep 128167069 = 48062651) B48062651
theorem B1232551 : Blo 1232434 1232551 := bstep (se 1 (by rfl) ⟨924413, by rfl⟩ : syracuseStep 1232551 = 1848827) B1848827
theorem B1232575 : Blo 1232434 1232575 := bstep (se 1 (by rfl) ⟨924431, by rfl⟩ : syracuseStep 1232575 = 1848863) B1848863
theorem B1233147 : Blo 1232434 1233147 := bstep (se 1 (by rfl) ⟨924860, by rfl⟩ : syracuseStep 1233147 = 1849721) B1849721
theorem B6246719 : Blo 1232434 6246719 := bstep (se 1 (by rfl) ⟨4685039, by rfl⟩ : syracuseStep 6246719 = 9370079) B9370079
theorem B8884687 : Blo 1232434 8884687 := bstep (se 1 (by rfl) ⟨6663515, by rfl⟩ : syracuseStep 8884687 = 13327031) B13327031
theorem B2773511 : Blo 1232434 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B1233435 : Blo 1232434 1233435 := bstep (se 1 (by rfl) ⟨925076, by rfl⟩ : syracuseStep 1233435 = 1850153) B1850153
theorem B1233599 : Blo 1232434 1233599 := bstep (se 1 (by rfl) ⟨925199, by rfl⟩ : syracuseStep 1233599 = 1850399) B1850399
theorem B1233791 : Blo 1232434 1233791 := bstep (se 1 (by rfl) ⟨925343, by rfl⟩ : syracuseStep 1233791 = 1850687) B1850687
theorem B1234011 : Blo 1232434 1234011 := bstep (se 1 (by rfl) ⟨925508, by rfl⟩ : syracuseStep 1234011 = 1851017) B1851017
theorem B1234031 : Blo 1232434 1234031 := bstep (se 1 (by rfl) ⟨925523, by rfl⟩ : syracuseStep 1234031 = 1851047) B1851047
theorem B1234079 : Blo 1232434 1234079 := bstep (se 1 (by rfl) ⟨925559, by rfl⟩ : syracuseStep 1234079 = 1851119) B1851119
theorem B1234175 : Blo 1232434 1234175 := bstep (se 1 (by rfl) ⟨925631, by rfl⟩ : syracuseStep 1234175 = 1851263) B1851263
theorem B6247691 : Blo 1232434 6247691 := bstep (se 1 (by rfl) ⟨4685768, by rfl⟩ : syracuseStep 6247691 = 9371537) B9371537
theorem B1234367 : Blo 1232434 1234367 := bstep (se 1 (by rfl) ⟨925775, by rfl⟩ : syracuseStep 1234367 = 1851551) B1851551
theorem B1848959 : Blo 1232434 1848959 := bstep (se 1 (by rfl) ⟨1386719, by rfl⟩ : syracuseStep 1848959 = 2773439) B2773439
theorem B2373311 : Blo 1232434 2373311 := bstep (se 1 (by rfl) ⟨1779983, by rfl⟩ : syracuseStep 2373311 = 3559967) B3559967
theorem B4446035 : Blo 1232434 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B5003135 : Blo 1232434 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B13342769 : Blo 1232434 13342769 := bstep (se 2 (by rfl) ⟨5003538, by rfl⟩ : syracuseStep 13342769 = 10007077) B10007077
theorem B2775113 : Blo 1232434 2775113 := bstep (se 2 (by rfl) ⟨1040667, by rfl⟩ : syracuseStep 2775113 = 2081335) B2081335
theorem B35543123 : Blo 1232434 35543123 := bstep (se 1 (by rfl) ⟨26657342, by rfl⟩ : syracuseStep 35543123 = 53314685) B53314685
theorem B15808729 : Blo 1232434 15808729 := bstep (se 2 (by rfl) ⟨5928273, by rfl⟩ : syracuseStep 15808729 = 11856547) B11856547
theorem B1849583 : Blo 1232434 1849583 := bstep (se 1 (by rfl) ⟨1387187, by rfl⟩ : syracuseStep 1849583 = 2774375) B2774375
theorem B1849655 : Blo 1232434 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B1849679 : Blo 1232434 1849679 := bstep (se 1 (by rfl) ⟨1387259, by rfl⟩ : syracuseStep 1849679 = 2774519) B2774519
theorem B1849727 : Blo 1232434 1849727 := bstep (se 1 (by rfl) ⟨1387295, by rfl⟩ : syracuseStep 1849727 = 2774591) B2774591
theorem B6331007 : Blo 1232434 6331007 := bstep (se 1 (by rfl) ⟨4748255, by rfl⟩ : syracuseStep 6331007 = 9496511) B9496511
theorem B2775815 : Blo 1232434 2775815 := bstep (se 1 (by rfl) ⟨2081861, by rfl⟩ : syracuseStep 2775815 = 4163723) B4163723
theorem B17103707 : Blo 1232434 17103707 := bstep (se 1 (by rfl) ⟨12827780, by rfl⟩ : syracuseStep 17103707 = 25655561) B25655561
theorem B6241535 : Blo 1232434 6241535 := bstep (se 1 (by rfl) ⟨4681151, by rfl⟩ : syracuseStep 6241535 = 9362303) B9362303
theorem B53304641 : Blo 1232434 53304641 := bstep (se 2 (by rfl) ⟨19989240, by rfl⟩ : syracuseStep 53304641 = 39978481) B39978481
theorem B5930621 : Blo 1232434 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B1875611 : Blo 1232434 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B10534643 : Blo 1232434 10534643 := bstep (se 1 (by rfl) ⟨7900982, by rfl⟩ : syracuseStep 10534643 = 15801965) B15801965
theorem B2776859 : Blo 1232434 2776859 := bstep (se 1 (by rfl) ⟨2082644, by rfl⟩ : syracuseStep 2776859 = 4165289) B4165289
theorem B3121051 : Blo 1232434 3121051 := bstep (se 1 (by rfl) ⟨2340788, by rfl⟩ : syracuseStep 3121051 = 4681577) B4681577
theorem B1851305 : Blo 1232434 1851305 := bstep (se 2 (by rfl) ⟨694239, by rfl⟩ : syracuseStep 1851305 = 1388479) B1388479
theorem B51364003 : Blo 1232434 51364003 := bstep (se 1 (by rfl) ⟨38523002, by rfl⟩ : syracuseStep 51364003 = 77046005) B77046005
theorem B21078305 : Blo 1232434 21078305 := bstep (se 2 (by rfl) ⟨7904364, by rfl⟩ : syracuseStep 21078305 = 15808729) B15808729
theorem B11846249 : Blo 1232434 11846249 := bstep (se 2 (by rfl) ⟨4442343, by rfl⟩ : syracuseStep 11846249 = 8884687) B8884687
theorem B3949415 : Blo 1232434 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B3335423 : Blo 1232434 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B4162913 : Blo 1232434 4162913 := bstep (se 2 (by rfl) ⟨1561092, by rfl⟩ : syracuseStep 4162913 = 3122185) B3122185
theorem B20006311 : Blo 1232434 20006311 := bstep (se 1 (by rfl) ⟨15004733, by rfl⟩ : syracuseStep 20006311 = 30009467) B30009467
theorem B4220671 : Blo 1232434 4220671 := bstep (se 1 (by rfl) ⟨3165503, by rfl⟩ : syracuseStep 4220671 = 6331007) B6331007
theorem B4163561 : Blo 1232434 4163561 := bstep (se 2 (by rfl) ⟨1561335, by rfl⟩ : syracuseStep 4163561 = 3122671) B3122671
theorem B7023095 : Blo 1232434 7023095 := bstep (se 1 (by rfl) ⟨5267321, by rfl⟩ : syracuseStep 7023095 = 10534643) B10534643
theorem B7023347 : Blo 1232434 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B4164479 : Blo 1232434 4164479 := bstep (se 1 (by rfl) ⟨3123359, by rfl⟩ : syracuseStep 4164479 = 6246719) B6246719
theorem B2632799 : Blo 1232434 2632799 := bstep (se 1 (by rfl) ⟨1974599, by rfl⟩ : syracuseStep 2632799 = 3949199) B3949199
theorem B4165127 : Blo 1232434 4165127 := bstep (se 1 (by rfl) ⟨3123845, by rfl⟩ : syracuseStep 4165127 = 6247691) B6247691
theorem B1232639 : Blo 1232434 1232639 := bstep (se 1 (by rfl) ⟨924479, by rfl⟩ : syracuseStep 1232639 = 1848959) B1848959
theorem B10530647 : Blo 1232434 10530647 := bstep (se 1 (by rfl) ⟨7897985, by rfl⟩ : syracuseStep 10530647 = 15795971) B15795971
theorem B5926891 : Blo 1232434 5926891 := bstep (se 1 (by rfl) ⟨4445168, by rfl⟩ : syracuseStep 5926891 = 8890337) B8890337
theorem B23695415 : Blo 1232434 23695415 := bstep (se 1 (by rfl) ⟨17771561, by rfl⟩ : syracuseStep 23695415 = 35543123) B35543123
theorem B1233055 : Blo 1232434 1233055 := bstep (se 1 (by rfl) ⟨924791, by rfl⟩ : syracuseStep 1233055 = 1849583) B1849583
theorem B1233103 : Blo 1232434 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B170889425 : Blo 1232434 170889425 := bstep (se 2 (by rfl) ⟨64083534, by rfl⟩ : syracuseStep 170889425 = 128167069) B128167069
theorem B1233119 : Blo 1232434 1233119 := bstep (se 1 (by rfl) ⟨924839, by rfl⟩ : syracuseStep 1233119 = 1849679) B1849679
theorem B1233151 : Blo 1232434 1233151 := bstep (se 1 (by rfl) ⟨924863, by rfl⟩ : syracuseStep 1233151 = 1849727) B1849727
theorem B6328829 : Blo 1232434 6328829 := bstep (se 3 (by rfl) ⟨1186655, by rfl⟩ : syracuseStep 6328829 = 2373311) B2373311
theorem B3953747 : Blo 1232434 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B1250407 : Blo 1232434 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B1234203 : Blo 1232434 1234203 := bstep (se 1 (by rfl) ⟨925652, by rfl⟩ : syracuseStep 1234203 = 1851305) B1851305
theorem B1234303 : Blo 1232434 1234303 := bstep (se 1 (by rfl) ⟨925727, by rfl⟩ : syracuseStep 1234303 = 1851455) B1851455
theorem B1848809 : Blo 1232434 1848809 := bstep (se 2 (by rfl) ⟨693303, by rfl⟩ : syracuseStep 1848809 = 1386607) B1386607
theorem B3511799 : Blo 1232434 3511799 := bstep (se 1 (by rfl) ⟨2633849, by rfl⟩ : syracuseStep 3511799 = 5267699) B5267699
theorem B1849007 : Blo 1232434 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B2774735 : Blo 1232434 2774735 := bstep (se 1 (by rfl) ⟨2081051, by rfl⟩ : syracuseStep 2774735 = 4162103) B4162103
theorem B2964023 : Blo 1232434 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B8895179 : Blo 1232434 8895179 := bstep (se 1 (by rfl) ⟨6671384, by rfl⟩ : syracuseStep 8895179 = 13342769) B13342769
theorem B1850075 : Blo 1232434 1850075 := bstep (se 1 (by rfl) ⟨1387556, by rfl⟩ : syracuseStep 1850075 = 2775113) B2775113
theorem B6249311 : Blo 1232434 6249311 := bstep (se 1 (by rfl) ⟨4686983, by rfl⟩ : syracuseStep 6249311 = 9373967) B9373967
theorem B1850543 : Blo 1232434 1850543 := bstep (se 1 (by rfl) ⟨1387907, by rfl⟩ : syracuseStep 1850543 = 2775815) B2775815
theorem B11402471 : Blo 1232434 11402471 := bstep (se 1 (by rfl) ⟨8551853, by rfl⟩ : syracuseStep 11402471 = 17103707) B17103707
theorem B3120403 : Blo 1232434 3120403 := bstep (se 1 (by rfl) ⟨2340302, by rfl⟩ : syracuseStep 3120403 = 4680605) B4680605
theorem B4161023 : Blo 1232434 4161023 := bstep (se 1 (by rfl) ⟨3120767, by rfl⟩ : syracuseStep 4161023 = 6241535) B6241535
theorem B35536427 : Blo 1232434 35536427 := bstep (se 1 (by rfl) ⟨26652320, by rfl⟩ : syracuseStep 35536427 = 53304641) B53304641
theorem B1851239 : Blo 1232434 1851239 := bstep (se 1 (by rfl) ⟨1388429, by rfl⟩ : syracuseStep 1851239 = 2776859) B2776859
theorem B4161401 : Blo 1232434 4161401 := bstep (se 2 (by rfl) ⟨1560525, by rfl⟩ : syracuseStep 4161401 = 3121051) B3121051
theorem B113926283 : Blo 1232434 113926283 := bstep (se 1 (by rfl) ⟨85444712, by rfl⟩ : syracuseStep 113926283 = 170889425) B170889425
theorem B68485337 : Blo 1232434 68485337 := bstep (se 2 (by rfl) ⟨25682001, by rfl⟩ : syracuseStep 68485337 = 51364003) B51364003
theorem B4219219 : Blo 1232434 4219219 := bstep (se 1 (by rfl) ⟨3164414, by rfl⟩ : syracuseStep 4219219 = 6328829) B6328829
theorem B7897499 : Blo 1232434 7897499 := bstep (se 1 (by rfl) ⟨5923124, by rfl⟩ : syracuseStep 7897499 = 11846249) B11846249
theorem B6668837 : Blo 1232434 6668837 := bstep (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) B1250407
theorem B1976015 : Blo 1232434 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B26675081 : Blo 1232434 26675081 := bstep (se 2 (by rfl) ⟨10003155, by rfl⟩ : syracuseStep 26675081 = 20006311) B20006311
theorem B1755199 : Blo 1232434 1755199 := bstep (se 1 (by rfl) ⟨1316399, by rfl⟩ : syracuseStep 1755199 = 2632799) B2632799
theorem B15796943 : Blo 1232434 15796943 := bstep (se 1 (by rfl) ⟨11847707, by rfl⟩ : syracuseStep 15796943 = 23695415) B23695415
theorem B14052203 : Blo 1232434 14052203 := bstep (se 1 (by rfl) ⟨10539152, by rfl⟩ : syracuseStep 14052203 = 21078305) B21078305
theorem B2632943 : Blo 1232434 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B1232539 : Blo 1232434 1232539 := bstep (se 1 (by rfl) ⟨924404, by rfl⟩ : syracuseStep 1232539 = 1848809) B1848809
theorem B1232671 : Blo 1232434 1232671 := bstep (se 1 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 1232671 = 1849007) B1849007
theorem B4682063 : Blo 1232434 4682063 := bstep (se 1 (by rfl) ⟨3511547, by rfl⟩ : syracuseStep 4682063 = 7023095) B7023095
theorem B1233383 : Blo 1232434 1233383 := bstep (se 1 (by rfl) ⟨925037, by rfl⟩ : syracuseStep 1233383 = 1850075) B1850075
theorem B4682231 : Blo 1232434 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B4166207 : Blo 1232434 4166207 := bstep (se 1 (by rfl) ⟨3124655, by rfl⟩ : syracuseStep 4166207 = 6249311) B6249311
theorem B1233695 : Blo 1232434 1233695 := bstep (se 1 (by rfl) ⟨925271, by rfl⟩ : syracuseStep 1233695 = 1850543) B1850543
theorem B2774015 : Blo 1232434 2774015 := bstep (se 1 (by rfl) ⟨2080511, by rfl⟩ : syracuseStep 2774015 = 4161023) B4161023
theorem B1234159 : Blo 1232434 1234159 := bstep (se 1 (by rfl) ⟨925619, by rfl⟩ : syracuseStep 1234159 = 1851239) B1851239
theorem B2774267 : Blo 1232434 2774267 := bstep (se 1 (by rfl) ⟨2080700, by rfl⟩ : syracuseStep 2774267 = 4161401) B4161401
theorem B7902521 : Blo 1232434 7902521 := bstep (se 2 (by rfl) ⟨2963445, by rfl⟩ : syracuseStep 7902521 = 5926891) B5926891
theorem B8894461 : Blo 1232434 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B2635831 : Blo 1232434 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B2775275 : Blo 1232434 2775275 := bstep (se 1 (by rfl) ⟨2081456, by rfl⟩ : syracuseStep 2775275 = 4162913) B4162913
theorem B2341199 : Blo 1232434 2341199 := bstep (se 1 (by rfl) ⟨1755899, by rfl⟩ : syracuseStep 2341199 = 3511799) B3511799
theorem B1849823 : Blo 1232434 1849823 := bstep (se 1 (by rfl) ⟨1387367, by rfl⟩ : syracuseStep 1849823 = 2774735) B2774735
theorem B2775707 : Blo 1232434 2775707 := bstep (se 1 (by rfl) ⟨2081780, by rfl⟩ : syracuseStep 2775707 = 4163561) B4163561
theorem B4160537 : Blo 1232434 4160537 := bstep (se 2 (by rfl) ⟨1560201, by rfl⟩ : syracuseStep 4160537 = 3120403) B3120403
theorem B5930119 : Blo 1232434 5930119 := bstep (se 1 (by rfl) ⟨4447589, by rfl⟩ : syracuseStep 5930119 = 8895179) B8895179
theorem B2776319 : Blo 1232434 2776319 := bstep (se 1 (by rfl) ⟨2082239, by rfl⟩ : syracuseStep 2776319 = 4164479) B4164479
theorem B7601647 : Blo 1232434 7601647 := bstep (se 1 (by rfl) ⟨5701235, by rfl⟩ : syracuseStep 7601647 = 11402471) B11402471
theorem B5627561 : Blo 1232434 5627561 := bstep (se 2 (by rfl) ⟨2110335, by rfl⟩ : syracuseStep 5627561 = 4220671) B4220671
theorem B2776751 : Blo 1232434 2776751 := bstep (se 1 (by rfl) ⟨2082563, by rfl⟩ : syracuseStep 2776751 = 4165127) B4165127
theorem B23690951 : Blo 1232434 23690951 := bstep (se 1 (by rfl) ⟨17768213, by rfl⟩ : syracuseStep 23690951 = 35536427) B35536427
theorem B7020431 : Blo 1232434 7020431 := bstep (se 1 (by rfl) ⟨5265323, by rfl⟩ : syracuseStep 7020431 = 10530647) B10530647
theorem B3514441 : Blo 1232434 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B3121375 : Blo 1232434 3121375 := bstep (se 1 (by rfl) ⟨2341031, by rfl⟩ : syracuseStep 3121375 = 4682063) B4682063
theorem B3121487 : Blo 1232434 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B2777471 : Blo 1232434 2777471 := bstep (se 1 (by rfl) ⟨2083103, by rfl⟩ : syracuseStep 2777471 = 4166207) B4166207
theorem B7021181 : Blo 1232434 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B5268347 : Blo 1232434 5268347 := bstep (se 1 (by rfl) ⟨3951260, by rfl⟩ : syracuseStep 5268347 = 7902521) B7902521
theorem B7906825 : Blo 1232434 7906825 := bstep (se 2 (by rfl) ⟨2965059, by rfl⟩ : syracuseStep 7906825 = 5930119) B5930119
theorem B5269373 : Blo 1232434 5269373 := bstep (se 3 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 5269373 = 1976015) B1976015
theorem B10135529 : Blo 1232434 10135529 := bstep (se 2 (by rfl) ⟨3800823, by rfl⟩ : syracuseStep 10135529 = 7601647) B7601647
theorem B4680287 : Blo 1232434 4680287 := bstep (se 1 (by rfl) ⟨3510215, by rfl⟩ : syracuseStep 4680287 = 7020431) B7020431
theorem B75950855 : Blo 1232434 75950855 := bstep (se 1 (by rfl) ⟨56963141, by rfl⟩ : syracuseStep 75950855 = 113926283) B113926283
theorem B45656891 : Blo 1232434 45656891 := bstep (se 1 (by rfl) ⟨34242668, by rfl⟩ : syracuseStep 45656891 = 68485337) B68485337
theorem B1560799 : Blo 1232434 1560799 := bstep (se 1 (by rfl) ⟨1170599, by rfl⟩ : syracuseStep 1560799 = 2341199) B2341199
theorem B1233215 : Blo 1232434 1233215 := bstep (se 1 (by rfl) ⟨924911, by rfl⟩ : syracuseStep 1233215 = 1849823) B1849823
theorem B10531295 : Blo 1232434 10531295 := bstep (se 1 (by rfl) ⟨7898471, by rfl⟩ : syracuseStep 10531295 = 15796943) B15796943
theorem B9368135 : Blo 1232434 9368135 := bstep (se 1 (by rfl) ⟨7026101, by rfl⟩ : syracuseStep 9368135 = 14052203) B14052203
theorem B2773691 : Blo 1232434 2773691 := bstep (se 1 (by rfl) ⟨2080268, by rfl⟩ : syracuseStep 2773691 = 4160537) B4160537
theorem B11859281 : Blo 1232434 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B2340265 : Blo 1232434 2340265 := bstep (se 2 (by rfl) ⟨877599, by rfl⟩ : syracuseStep 2340265 = 1755199) B1755199
theorem B5264999 : Blo 1232434 5264999 := bstep (se 1 (by rfl) ⟨3948749, by rfl⟩ : syracuseStep 5264999 = 7897499) B7897499
theorem B4445891 : Blo 1232434 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B5625625 : Blo 1232434 5625625 := bstep (se 2 (by rfl) ⟨2109609, by rfl⟩ : syracuseStep 5625625 = 4219219) B4219219
theorem B1849343 : Blo 1232434 1849343 := bstep (se 1 (by rfl) ⟨1387007, by rfl⟩ : syracuseStep 1849343 = 2774015) B2774015
theorem B1849511 : Blo 1232434 1849511 := bstep (se 1 (by rfl) ⟨1387133, by rfl⟩ : syracuseStep 1849511 = 2774267) B2774267
theorem B17783387 : Blo 1232434 17783387 := bstep (se 1 (by rfl) ⟨13337540, by rfl⟩ : syracuseStep 17783387 = 26675081) B26675081
theorem B1850183 : Blo 1232434 1850183 := bstep (se 1 (by rfl) ⟨1387637, by rfl⟩ : syracuseStep 1850183 = 2775275) B2775275
theorem B1850471 : Blo 1232434 1850471 := bstep (se 1 (by rfl) ⟨1387853, by rfl⟩ : syracuseStep 1850471 = 2775707) B2775707
theorem B15006829 : Blo 1232434 15006829 := bstep (se 3 (by rfl) ⟨2813780, by rfl⟩ : syracuseStep 15006829 = 5627561) B5627561
theorem B1850879 : Blo 1232434 1850879 := bstep (se 1 (by rfl) ⟨1388159, by rfl⟩ : syracuseStep 1850879 = 2776319) B2776319
theorem B1851167 : Blo 1232434 1851167 := bstep (se 1 (by rfl) ⟨1388375, by rfl⟩ : syracuseStep 1851167 = 2776751) B2776751
theorem B15793967 : Blo 1232434 15793967 := bstep (se 1 (by rfl) ⟨11845475, by rfl⟩ : syracuseStep 15793967 = 23690951) B23690951
theorem B4685921 : Blo 1232434 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B2080991 : Blo 1232434 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B1851647 : Blo 1232434 1851647 := bstep (se 1 (by rfl) ⟨1388735, by rfl⟩ : syracuseStep 1851647 = 2777471) B2777471
theorem B4161833 : Blo 1232434 4161833 := bstep (se 2 (by rfl) ⟨1560687, by rfl⟩ : syracuseStep 4161833 = 3121375) B3121375
theorem B2081065 : Blo 1232434 2081065 := bstep (se 2 (by rfl) ⟨780399, by rfl⟩ : syracuseStep 2081065 = 1560799) B1560799
theorem B7020863 : Blo 1232434 7020863 := bstep (se 1 (by rfl) ⟨5265647, by rfl⟩ : syracuseStep 7020863 = 10531295) B10531295
theorem B7906187 : Blo 1232434 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B11855591 : Blo 1232434 11855591 := bstep (se 1 (by rfl) ⟨8891693, by rfl⟩ : syracuseStep 11855591 = 17783387) B17783387
theorem B10529311 : Blo 1232434 10529311 := bstep (se 1 (by rfl) ⟨7896983, by rfl⟩ : syracuseStep 10529311 = 15793967) B15793967
theorem B6245423 : Blo 1232434 6245423 := bstep (se 1 (by rfl) ⟨4684067, by rfl⟩ : syracuseStep 6245423 = 9368135) B9368135
theorem B4680787 : Blo 1232434 4680787 := bstep (se 1 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 4680787 = 7021181) B7021181
theorem B3509999 : Blo 1232434 3509999 := bstep (se 1 (by rfl) ⟨2632499, by rfl⟩ : syracuseStep 3509999 = 5264999) B5264999
theorem B1232895 : Blo 1232434 1232895 := bstep (se 1 (by rfl) ⟨924671, by rfl⟩ : syracuseStep 1232895 = 1849343) B1849343
theorem B1233007 : Blo 1232434 1233007 := bstep (se 1 (by rfl) ⟨924755, by rfl⟩ : syracuseStep 1233007 = 1849511) B1849511
theorem B20009105 : Blo 1232434 20009105 := bstep (se 2 (by rfl) ⟨7503414, by rfl⟩ : syracuseStep 20009105 = 15006829) B15006829
theorem B30437927 : Blo 1232434 30437927 := bstep (se 1 (by rfl) ⟨22828445, by rfl⟩ : syracuseStep 30437927 = 45656891) B45656891
theorem B1233455 : Blo 1232434 1233455 := bstep (se 1 (by rfl) ⟨925091, by rfl⟩ : syracuseStep 1233455 = 1850183) B1850183
theorem B1233647 : Blo 1232434 1233647 := bstep (se 1 (by rfl) ⟨925235, by rfl⟩ : syracuseStep 1233647 = 1850471) B1850471
theorem B1233919 : Blo 1232434 1233919 := bstep (se 1 (by rfl) ⟨925439, by rfl⟩ : syracuseStep 1233919 = 1850879) B1850879
theorem B7500833 : Blo 1232434 7500833 := bstep (se 2 (by rfl) ⟨2812812, by rfl⟩ : syracuseStep 7500833 = 5625625) B5625625
theorem B1234111 : Blo 1232434 1234111 := bstep (se 1 (by rfl) ⟨925583, by rfl⟩ : syracuseStep 1234111 = 1851167) B1851167
theorem B1849127 : Blo 1232434 1849127 := bstep (se 1 (by rfl) ⟨1386845, by rfl⟩ : syracuseStep 1849127 = 2773691) B2773691
theorem B3512231 : Blo 1232434 3512231 := bstep (se 1 (by rfl) ⟨2634173, by rfl⟩ : syracuseStep 3512231 = 5268347) B5268347
theorem B2963927 : Blo 1232434 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B3512915 : Blo 1232434 3512915 := bstep (se 1 (by rfl) ⟨2634686, by rfl⟩ : syracuseStep 3512915 = 5269373) B5269373
theorem B6757019 : Blo 1232434 6757019 := bstep (se 1 (by rfl) ⟨5067764, by rfl⟩ : syracuseStep 6757019 = 10135529) B10135529
theorem B3120191 : Blo 1232434 3120191 := bstep (se 1 (by rfl) ⟨2340143, by rfl⟩ : syracuseStep 3120191 = 4680287) B4680287
theorem B50633903 : Blo 1232434 50633903 := bstep (se 1 (by rfl) ⟨37975427, by rfl⟩ : syracuseStep 50633903 = 75950855) B75950855
theorem B3120353 : Blo 1232434 3120353 := bstep (se 2 (by rfl) ⟨1170132, by rfl⟩ : syracuseStep 3120353 = 2340265) B2340265
theorem B10542433 : Blo 1232434 10542433 := bstep (se 2 (by rfl) ⟨3953412, by rfl⟩ : syracuseStep 10542433 = 7906825) B7906825
theorem B20291951 : Blo 1232434 20291951 := bstep (se 1 (by rfl) ⟨15218963, by rfl⟩ : syracuseStep 20291951 = 30437927) B30437927
theorem B1975951 : Blo 1232434 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B4163615 : Blo 1232434 4163615 := bstep (se 1 (by rfl) ⟨3122711, by rfl⟩ : syracuseStep 4163615 = 6245423) B6245423
theorem B3123947 : Blo 1232434 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B13339403 : Blo 1232434 13339403 := bstep (se 1 (by rfl) ⟨10004552, by rfl⟩ : syracuseStep 13339403 = 20009105) B20009105
theorem B1387327 : Blo 1232434 1387327 := bstep (se 1 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 1387327 = 2080991) B2080991
theorem B4680575 : Blo 1232434 4680575 := bstep (se 1 (by rfl) ⟨3510431, by rfl⟩ : syracuseStep 4680575 = 7020863) B7020863
theorem B5270791 : Blo 1232434 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B5000555 : Blo 1232434 5000555 := bstep (se 1 (by rfl) ⟨3750416, by rfl⟩ : syracuseStep 5000555 = 7500833) B7500833
theorem B1232751 : Blo 1232434 1232751 := bstep (se 1 (by rfl) ⟨924563, by rfl⟩ : syracuseStep 1232751 = 1849127) B1849127
theorem B33755935 : Blo 1232434 33755935 := bstep (se 1 (by rfl) ⟨25316951, by rfl⟩ : syracuseStep 33755935 = 50633903) B50633903
theorem B2339999 : Blo 1232434 2339999 := bstep (se 1 (by rfl) ⟨1754999, by rfl⟩ : syracuseStep 2339999 = 3509999) B3509999
theorem B1234431 : Blo 1232434 1234431 := bstep (se 1 (by rfl) ⟨925823, by rfl⟩ : syracuseStep 1234431 = 1851647) B1851647
theorem B2774555 : Blo 1232434 2774555 := bstep (se 1 (by rfl) ⟨2080916, by rfl⟩ : syracuseStep 2774555 = 4161833) B4161833
theorem B2774753 : Blo 1232434 2774753 := bstep (se 2 (by rfl) ⟨1040532, by rfl⟩ : syracuseStep 2774753 = 2081065) B2081065
theorem B14039081 : Blo 1232434 14039081 := bstep (se 2 (by rfl) ⟨5264655, by rfl⟩ : syracuseStep 14039081 = 10529311) B10529311
theorem B7903727 : Blo 1232434 7903727 := bstep (se 1 (by rfl) ⟨5927795, by rfl⟩ : syracuseStep 7903727 = 11855591) B11855591
theorem B2341487 : Blo 1232434 2341487 := bstep (se 1 (by rfl) ⟨1756115, by rfl⟩ : syracuseStep 2341487 = 3512231) B3512231
theorem B6241049 : Blo 1232434 6241049 := bstep (se 2 (by rfl) ⟨2340393, by rfl⟩ : syracuseStep 6241049 = 4680787) B4680787
theorem B2341943 : Blo 1232434 2341943 := bstep (se 1 (by rfl) ⟨1756457, by rfl⟩ : syracuseStep 2341943 = 3512915) B3512915
theorem B4504679 : Blo 1232434 4504679 := bstep (se 1 (by rfl) ⟨3378509, by rfl⟩ : syracuseStep 4504679 = 6757019) B6757019
theorem B14056577 : Blo 1232434 14056577 := bstep (se 2 (by rfl) ⟨5271216, by rfl⟩ : syracuseStep 14056577 = 10542433) B10542433
theorem B2080127 : Blo 1232434 2080127 := bstep (se 1 (by rfl) ⟨1560095, by rfl⟩ : syracuseStep 2080127 = 3120191) B3120191
theorem B2080235 : Blo 1232434 2080235 := bstep (se 1 (by rfl) ⟨1560176, by rfl⟩ : syracuseStep 2080235 = 3120353) B3120353
theorem B45007913 : Blo 1232434 45007913 := bstep (se 2 (by rfl) ⟨16877967, by rfl⟩ : syracuseStep 45007913 = 33755935) B33755935
theorem B6243965 : Blo 1232434 6243965 := bstep (se 3 (by rfl) ⟨1170743, by rfl⟩ : syracuseStep 6243965 = 2341487) B2341487
theorem B5269151 : Blo 1232434 5269151 := bstep (se 1 (by rfl) ⟨3951863, by rfl⟩ : syracuseStep 5269151 = 7903727) B7903727
theorem B2082631 : Blo 1232434 2082631 := bstep (se 1 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 2082631 = 3123947) B3123947
theorem B1386751 : Blo 1232434 1386751 := bstep (se 1 (by rfl) ⟨1040063, by rfl⟩ : syracuseStep 1386751 = 2080127) B2080127
theorem B1386823 : Blo 1232434 1386823 := bstep (se 1 (by rfl) ⟨1040117, by rfl⟩ : syracuseStep 1386823 = 2080235) B2080235
theorem B13527967 : Blo 1232434 13527967 := bstep (se 1 (by rfl) ⟨10145975, by rfl⟩ : syracuseStep 13527967 = 20291951) B20291951
theorem B1559999 : Blo 1232434 1559999 := bstep (se 1 (by rfl) ⟨1169999, by rfl⟩ : syracuseStep 1559999 = 2339999) B2339999
theorem B9359387 : Blo 1232434 9359387 := bstep (se 1 (by rfl) ⟨7019540, by rfl⟩ : syracuseStep 9359387 = 14039081) B14039081
theorem B8892935 : Blo 1232434 8892935 := bstep (se 1 (by rfl) ⟨6669701, by rfl⟩ : syracuseStep 8892935 = 13339403) B13339403
theorem B1561295 : Blo 1232434 1561295 := bstep (se 1 (by rfl) ⟨1170971, by rfl⟩ : syracuseStep 1561295 = 2341943) B2341943
theorem B3003119 : Blo 1232434 3003119 := bstep (se 1 (by rfl) ⟨2252339, by rfl⟩ : syracuseStep 3003119 = 4504679) B4504679
theorem B2634601 : Blo 1232434 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B13334813 : Blo 1232434 13334813 := bstep (se 3 (by rfl) ⟨2500277, by rfl⟩ : syracuseStep 13334813 = 5000555) B5000555
theorem B1849703 : Blo 1232434 1849703 := bstep (se 1 (by rfl) ⟨1387277, by rfl⟩ : syracuseStep 1849703 = 2774555) B2774555
theorem B1849769 : Blo 1232434 1849769 := bstep (se 2 (by rfl) ⟨693663, by rfl⟩ : syracuseStep 1849769 = 1387327) B1387327
theorem B1849835 : Blo 1232434 1849835 := bstep (se 1 (by rfl) ⟨1387376, by rfl⟩ : syracuseStep 1849835 = 2774753) B2774753
theorem B2775743 : Blo 1232434 2775743 := bstep (se 1 (by rfl) ⟨2081807, by rfl⟩ : syracuseStep 2775743 = 4163615) B4163615
theorem B7027721 : Blo 1232434 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B4160699 : Blo 1232434 4160699 := bstep (se 1 (by rfl) ⟨3120524, by rfl⟩ : syracuseStep 4160699 = 6241049) B6241049
theorem B3120383 : Blo 1232434 3120383 := bstep (se 1 (by rfl) ⟨2340287, by rfl⟩ : syracuseStep 3120383 = 4680575) B4680575
theorem B9371051 : Blo 1232434 9371051 := bstep (se 1 (by rfl) ⟨7028288, by rfl⟩ : syracuseStep 9371051 = 14056577) B14056577
theorem B4162643 : Blo 1232434 4162643 := bstep (se 1 (by rfl) ⟨3121982, by rfl⟩ : syracuseStep 4162643 = 6243965) B6243965
theorem B8889875 : Blo 1232434 8889875 := bstep (se 1 (by rfl) ⟨6667406, by rfl⟩ : syracuseStep 8889875 = 13334813) B13334813
theorem B4163453 : Blo 1232434 4163453 := bstep (se 3 (by rfl) ⟨780647, by rfl⟩ : syracuseStep 4163453 = 1561295) B1561295
theorem B2002079 : Blo 1232434 2002079 := bstep (se 1 (by rfl) ⟨1501559, by rfl⟩ : syracuseStep 2002079 = 3003119) B3003119
theorem B1233135 : Blo 1232434 1233135 := bstep (se 1 (by rfl) ⟨924851, by rfl⟩ : syracuseStep 1233135 = 1849703) B1849703
theorem B1233179 : Blo 1232434 1233179 := bstep (se 1 (by rfl) ⟨924884, by rfl⟩ : syracuseStep 1233179 = 1849769) B1849769
theorem B1233223 : Blo 1232434 1233223 := bstep (se 1 (by rfl) ⟨924917, by rfl⟩ : syracuseStep 1233223 = 1849835) B1849835
theorem B2773799 : Blo 1232434 2773799 := bstep (se 1 (by rfl) ⟨2080349, by rfl⟩ : syracuseStep 2773799 = 4160699) B4160699
theorem B6247367 : Blo 1232434 6247367 := bstep (se 1 (by rfl) ⟨4685525, by rfl⟩ : syracuseStep 6247367 = 9371051) B9371051
theorem B6239591 : Blo 1232434 6239591 := bstep (se 1 (by rfl) ⟨4679693, by rfl⟩ : syracuseStep 6239591 = 9359387) B9359387
theorem B1849001 : Blo 1232434 1849001 := bstep (se 2 (by rfl) ⟨693375, by rfl⟩ : syracuseStep 1849001 = 1386751) B1386751
theorem B5928623 : Blo 1232434 5928623 := bstep (se 1 (by rfl) ⟨4446467, by rfl⟩ : syracuseStep 5928623 = 8892935) B8892935
theorem B1849097 : Blo 1232434 1849097 := bstep (se 2 (by rfl) ⟨693411, by rfl⟩ : syracuseStep 1849097 = 1386823) B1386823
theorem B30005275 : Blo 1232434 30005275 := bstep (se 1 (by rfl) ⟨22503956, by rfl⟩ : syracuseStep 30005275 = 45007913) B45007913
theorem B3512767 : Blo 1232434 3512767 := bstep (se 1 (by rfl) ⟨2634575, by rfl⟩ : syracuseStep 3512767 = 5269151) B5269151
theorem B3512801 : Blo 1232434 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B4159997 : Blo 1232434 4159997 := bstep (se 3 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 4159997 = 1559999) B1559999
theorem B18037289 : Blo 1232434 18037289 := bstep (se 2 (by rfl) ⟨6763983, by rfl⟩ : syracuseStep 18037289 = 13527967) B13527967
theorem B1850495 : Blo 1232434 1850495 := bstep (se 1 (by rfl) ⟨1387871, by rfl⟩ : syracuseStep 1850495 = 2775743) B2775743
theorem B4685147 : Blo 1232434 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B2080255 : Blo 1232434 2080255 := bstep (se 1 (by rfl) ⟨1560191, by rfl⟩ : syracuseStep 2080255 = 3120383) B3120383
theorem B2776841 : Blo 1232434 2776841 := bstep (se 2 (by rfl) ⟨1041315, by rfl⟩ : syracuseStep 2776841 = 2082631) B2082631
theorem B3123431 : Blo 1232434 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B4164911 : Blo 1232434 4164911 := bstep (se 1 (by rfl) ⟨3123683, by rfl⟩ : syracuseStep 4164911 = 6247367) B6247367
theorem B5926583 : Blo 1232434 5926583 := bstep (se 1 (by rfl) ⟨4444937, by rfl⟩ : syracuseStep 5926583 = 8889875) B8889875
theorem B1232667 : Blo 1232434 1232667 := bstep (se 1 (by rfl) ⟨924500, by rfl⟩ : syracuseStep 1232667 = 1849001) B1849001
theorem B3952415 : Blo 1232434 3952415 := bstep (se 1 (by rfl) ⟨2964311, by rfl⟩ : syracuseStep 3952415 = 5928623) B5928623
theorem B1232731 : Blo 1232434 1232731 := bstep (se 1 (by rfl) ⟨924548, by rfl⟩ : syracuseStep 1232731 = 1849097) B1849097
theorem B2773331 : Blo 1232434 2773331 := bstep (se 1 (by rfl) ⟨2079998, by rfl⟩ : syracuseStep 2773331 = 4159997) B4159997
theorem B2773673 : Blo 1232434 2773673 := bstep (se 2 (by rfl) ⟨1040127, by rfl⟩ : syracuseStep 2773673 = 2080255) B2080255
theorem B1233663 : Blo 1232434 1233663 := bstep (se 1 (by rfl) ⟨925247, by rfl⟩ : syracuseStep 1233663 = 1850495) B1850495
theorem B40007033 : Blo 1232434 40007033 := bstep (se 2 (by rfl) ⟨15002637, by rfl⟩ : syracuseStep 40007033 = 30005275) B30005275
theorem B5338877 : Blo 1232434 5338877 := bstep (se 3 (by rfl) ⟨1001039, by rfl⟩ : syracuseStep 5338877 = 2002079) B2002079
theorem B1849199 : Blo 1232434 1849199 := bstep (se 1 (by rfl) ⟨1386899, by rfl⟩ : syracuseStep 1849199 = 2773799) B2773799
theorem B4683689 : Blo 1232434 4683689 := bstep (se 2 (by rfl) ⟨1756383, by rfl⟩ : syracuseStep 4683689 = 3512767) B3512767
theorem B2775095 : Blo 1232434 2775095 := bstep (se 1 (by rfl) ⟨2081321, by rfl⟩ : syracuseStep 2775095 = 4162643) B4162643
theorem B4159727 : Blo 1232434 4159727 := bstep (se 1 (by rfl) ⟨3119795, by rfl⟩ : syracuseStep 4159727 = 6239591) B6239591
theorem B2775635 : Blo 1232434 2775635 := bstep (se 1 (by rfl) ⟨2081726, by rfl⟩ : syracuseStep 2775635 = 4163453) B4163453
theorem B2341867 : Blo 1232434 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B12024859 : Blo 1232434 12024859 := bstep (se 1 (by rfl) ⟨9018644, by rfl⟩ : syracuseStep 12024859 = 18037289) B18037289
theorem B1851227 : Blo 1232434 1851227 := bstep (se 1 (by rfl) ⟨1388420, by rfl⟩ : syracuseStep 1851227 = 2776841) B2776841
theorem B3122459 : Blo 1232434 3122459 := bstep (se 1 (by rfl) ⟨2341844, by rfl⟩ : syracuseStep 3122459 = 4683689) B4683689
theorem B3122489 : Blo 1232434 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B16033145 : Blo 1232434 16033145 := bstep (se 2 (by rfl) ⟨6012429, by rfl⟩ : syracuseStep 16033145 = 12024859) B12024859
theorem B2082287 : Blo 1232434 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B3951055 : Blo 1232434 3951055 := bstep (se 1 (by rfl) ⟨2963291, by rfl⟩ : syracuseStep 3951055 = 5926583) B5926583
theorem B1232799 : Blo 1232434 1232799 := bstep (se 1 (by rfl) ⟨924599, by rfl⟩ : syracuseStep 1232799 = 1849199) B1849199
theorem B2773151 : Blo 1232434 2773151 := bstep (se 1 (by rfl) ⟨2079863, by rfl⟩ : syracuseStep 2773151 = 4159727) B4159727
theorem B2634943 : Blo 1232434 2634943 := bstep (se 1 (by rfl) ⟨1976207, by rfl⟩ : syracuseStep 2634943 = 3952415) B3952415
theorem B1234151 : Blo 1232434 1234151 := bstep (se 1 (by rfl) ⟨925613, by rfl⟩ : syracuseStep 1234151 = 1851227) B1851227
theorem B1848887 : Blo 1232434 1848887 := bstep (se 1 (by rfl) ⟨1386665, by rfl⟩ : syracuseStep 1848887 = 2773331) B2773331
theorem B1849115 : Blo 1232434 1849115 := bstep (se 1 (by rfl) ⟨1386836, by rfl⟩ : syracuseStep 1849115 = 2773673) B2773673
theorem B26671355 : Blo 1232434 26671355 := bstep (se 1 (by rfl) ⟨20003516, by rfl⟩ : syracuseStep 26671355 = 40007033) B40007033
theorem B1850063 : Blo 1232434 1850063 := bstep (se 1 (by rfl) ⟨1387547, by rfl⟩ : syracuseStep 1850063 = 2775095) B2775095
theorem B1850423 : Blo 1232434 1850423 := bstep (se 1 (by rfl) ⟨1387817, by rfl⟩ : syracuseStep 1850423 = 2775635) B2775635
theorem B14237005 : Blo 1232434 14237005 := bstep (se 3 (by rfl) ⟨2669438, by rfl⟩ : syracuseStep 14237005 = 5338877) B5338877
theorem B2776607 : Blo 1232434 2776607 := bstep (se 1 (by rfl) ⟨2082455, by rfl⟩ : syracuseStep 2776607 = 4164911) B4164911
theorem B5268073 : Blo 1232434 5268073 := bstep (se 2 (by rfl) ⟨1975527, by rfl⟩ : syracuseStep 5268073 = 3951055) B3951055
theorem B2081639 : Blo 1232434 2081639 := bstep (se 1 (by rfl) ⟨1561229, by rfl⟩ : syracuseStep 2081639 = 3122459) B3122459
theorem B2081659 : Blo 1232434 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B42755053 : Blo 1232434 42755053 := bstep (se 3 (by rfl) ⟨8016572, by rfl⟩ : syracuseStep 42755053 = 16033145) B16033145
theorem B18982673 : Blo 1232434 18982673 := bstep (se 2 (by rfl) ⟨7118502, by rfl⟩ : syracuseStep 18982673 = 14237005) B14237005
theorem B1388191 : Blo 1232434 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B1232591 : Blo 1232434 1232591 := bstep (se 1 (by rfl) ⟨924443, by rfl⟩ : syracuseStep 1232591 = 1848887) B1848887
theorem B1232743 : Blo 1232434 1232743 := bstep (se 1 (by rfl) ⟨924557, by rfl⟩ : syracuseStep 1232743 = 1849115) B1849115
theorem B17780903 : Blo 1232434 17780903 := bstep (se 1 (by rfl) ⟨13335677, by rfl⟩ : syracuseStep 17780903 = 26671355) B26671355
theorem B1233375 : Blo 1232434 1233375 := bstep (se 1 (by rfl) ⟨925031, by rfl⟩ : syracuseStep 1233375 = 1850063) B1850063
theorem B1233615 : Blo 1232434 1233615 := bstep (se 1 (by rfl) ⟨925211, by rfl⟩ : syracuseStep 1233615 = 1850423) B1850423
theorem B1848767 : Blo 1232434 1848767 := bstep (se 1 (by rfl) ⟨1386575, by rfl⟩ : syracuseStep 1848767 = 2773151) B2773151
theorem B3513257 : Blo 1232434 3513257 := bstep (se 2 (by rfl) ⟨1317471, by rfl⟩ : syracuseStep 3513257 = 2634943) B2634943
theorem B1851071 : Blo 1232434 1851071 := bstep (se 1 (by rfl) ⟨1388303, by rfl⟩ : syracuseStep 1851071 = 2776607) B2776607
theorem B11853935 : Blo 1232434 11853935 := bstep (se 1 (by rfl) ⟨8890451, by rfl⟩ : syracuseStep 11853935 = 17780903) B17780903
theorem B1387759 : Blo 1232434 1387759 := bstep (se 1 (by rfl) ⟨1040819, by rfl⟩ : syracuseStep 1387759 = 2081639) B2081639
theorem B7024097 : Blo 1232434 7024097 := bstep (se 2 (by rfl) ⟨2634036, by rfl⟩ : syracuseStep 7024097 = 5268073) B5268073
theorem B1232511 : Blo 1232434 1232511 := bstep (se 1 (by rfl) ⟨924383, by rfl⟩ : syracuseStep 1232511 = 1848767) B1848767
theorem B1234047 : Blo 1232434 1234047 := bstep (se 1 (by rfl) ⟨925535, by rfl⟩ : syracuseStep 1234047 = 1851071) B1851071
theorem B2775545 : Blo 1232434 2775545 := bstep (se 2 (by rfl) ⟨1040829, by rfl⟩ : syracuseStep 2775545 = 2081659) B2081659
theorem B12655115 : Blo 1232434 12655115 := bstep (se 1 (by rfl) ⟨9491336, by rfl⟩ : syracuseStep 12655115 = 18982673) B18982673
theorem B57006737 : Blo 1232434 57006737 := bstep (se 2 (by rfl) ⟨21377526, by rfl⟩ : syracuseStep 57006737 = 42755053) B42755053
theorem B2342171 : Blo 1232434 2342171 := bstep (se 1 (by rfl) ⟨1756628, by rfl⟩ : syracuseStep 2342171 = 3513257) B3513257
theorem B1850921 : Blo 1232434 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B38004491 : Blo 1232434 38004491 := bstep (se 1 (by rfl) ⟨28503368, by rfl⟩ : syracuseStep 38004491 = 57006737) B57006737
theorem B1561447 : Blo 1232434 1561447 := bstep (se 1 (by rfl) ⟨1171085, by rfl⟩ : syracuseStep 1561447 = 2342171) B2342171
theorem B4682731 : Blo 1232434 4682731 := bstep (se 1 (by rfl) ⟨3512048, by rfl⟩ : syracuseStep 4682731 = 7024097) B7024097
theorem B1233947 : Blo 1232434 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B7902623 : Blo 1232434 7902623 := bstep (se 1 (by rfl) ⟨5926967, by rfl⟩ : syracuseStep 7902623 = 11853935) B11853935
theorem B1850345 : Blo 1232434 1850345 := bstep (se 2 (by rfl) ⟨693879, by rfl⟩ : syracuseStep 1850345 = 1387759) B1387759
theorem B1850363 : Blo 1232434 1850363 := bstep (se 1 (by rfl) ⟨1387772, by rfl⟩ : syracuseStep 1850363 = 2775545) B2775545
theorem B8436743 : Blo 1232434 8436743 := bstep (se 1 (by rfl) ⟨6327557, by rfl⟩ : syracuseStep 8436743 = 12655115) B12655115
theorem B5268415 : Blo 1232434 5268415 := bstep (se 1 (by rfl) ⟨3951311, by rfl⟩ : syracuseStep 5268415 = 7902623) B7902623
theorem B2081929 : Blo 1232434 2081929 := bstep (se 2 (by rfl) ⟨780723, by rfl⟩ : syracuseStep 2081929 = 1561447) B1561447
theorem B6243641 : Blo 1232434 6243641 := bstep (se 2 (by rfl) ⟨2341365, by rfl⟩ : syracuseStep 6243641 = 4682731) B4682731
theorem B1233563 : Blo 1232434 1233563 := bstep (se 1 (by rfl) ⟨925172, by rfl⟩ : syracuseStep 1233563 = 1850345) B1850345
theorem B1233575 : Blo 1232434 1233575 := bstep (se 1 (by rfl) ⟨925181, by rfl⟩ : syracuseStep 1233575 = 1850363) B1850363
theorem B5624495 : Blo 1232434 5624495 := bstep (se 1 (by rfl) ⟨4218371, by rfl⟩ : syracuseStep 5624495 = 8436743) B8436743
theorem B25336327 : Blo 1232434 25336327 := bstep (se 1 (by rfl) ⟨19002245, by rfl⟩ : syracuseStep 25336327 = 38004491) B38004491
theorem B4162427 : Blo 1232434 4162427 := bstep (se 1 (by rfl) ⟨3121820, by rfl⟩ : syracuseStep 4162427 = 6243641) B6243641
theorem B7024553 : Blo 1232434 7024553 := bstep (se 2 (by rfl) ⟨2634207, by rfl⟩ : syracuseStep 7024553 = 5268415) B5268415
theorem B3749663 : Blo 1232434 3749663 := bstep (se 1 (by rfl) ⟨2812247, by rfl⟩ : syracuseStep 3749663 = 5624495) B5624495
theorem B33781769 : Blo 1232434 33781769 := bstep (se 2 (by rfl) ⟨12668163, by rfl⟩ : syracuseStep 33781769 = 25336327) B25336327
theorem B2775905 : Blo 1232434 2775905 := bstep (se 2 (by rfl) ⟨1040964, by rfl⟩ : syracuseStep 2775905 = 2081929) B2081929
theorem B22521179 : Blo 1232434 22521179 := bstep (se 1 (by rfl) ⟨16890884, by rfl⟩ : syracuseStep 22521179 = 33781769) B33781769
theorem B9999101 : Blo 1232434 9999101 := bstep (se 3 (by rfl) ⟨1874831, by rfl⟩ : syracuseStep 9999101 = 3749663) B3749663
theorem B4683035 : Blo 1232434 4683035 := bstep (se 1 (by rfl) ⟨3512276, by rfl⟩ : syracuseStep 4683035 = 7024553) B7024553
theorem B2774951 : Blo 1232434 2774951 := bstep (se 1 (by rfl) ⟨2081213, by rfl⟩ : syracuseStep 2774951 = 4162427) B4162427
theorem B1850603 : Blo 1232434 1850603 := bstep (se 1 (by rfl) ⟨1387952, by rfl⟩ : syracuseStep 1850603 = 2775905) B2775905
theorem B3122023 : Blo 1232434 3122023 := bstep (se 1 (by rfl) ⟨2341517, by rfl⟩ : syracuseStep 3122023 = 4683035) B4683035
theorem B60056477 : Blo 1232434 60056477 := bstep (se 3 (by rfl) ⟨11260589, by rfl⟩ : syracuseStep 60056477 = 22521179) B22521179
theorem B1233735 : Blo 1232434 1233735 := bstep (se 1 (by rfl) ⟨925301, by rfl⟩ : syracuseStep 1233735 = 1850603) B1850603
theorem B6666067 : Blo 1232434 6666067 := bstep (se 1 (by rfl) ⟨4999550, by rfl⟩ : syracuseStep 6666067 = 9999101) B9999101
theorem B1849967 : Blo 1232434 1849967 := bstep (se 1 (by rfl) ⟨1387475, by rfl⟩ : syracuseStep 1849967 = 2774951) B2774951
theorem B4162697 : Blo 1232434 4162697 := bstep (se 2 (by rfl) ⟨1561011, by rfl⟩ : syracuseStep 4162697 = 3122023) B3122023
theorem B40037651 : Blo 1232434 40037651 := bstep (se 1 (by rfl) ⟨30028238, by rfl⟩ : syracuseStep 40037651 = 60056477) B60056477
theorem B1233311 : Blo 1232434 1233311 := bstep (se 1 (by rfl) ⟨924983, by rfl⟩ : syracuseStep 1233311 = 1849967) B1849967
theorem B8888089 : Blo 1232434 8888089 := bstep (se 2 (by rfl) ⟨3333033, by rfl⟩ : syracuseStep 8888089 = 6666067) B6666067
theorem B26691767 : Blo 1232434 26691767 := bstep (se 1 (by rfl) ⟨20018825, by rfl⟩ : syracuseStep 26691767 = 40037651) B40037651
theorem B11850785 : Blo 1232434 11850785 := bstep (se 2 (by rfl) ⟨4444044, by rfl⟩ : syracuseStep 11850785 = 8888089) B8888089
theorem B2775131 : Blo 1232434 2775131 := bstep (se 1 (by rfl) ⟨2081348, by rfl⟩ : syracuseStep 2775131 = 4162697) B4162697
theorem B17794511 : Blo 1232434 17794511 := bstep (se 1 (by rfl) ⟨13345883, by rfl⟩ : syracuseStep 17794511 = 26691767) B26691767
theorem B7900523 : Blo 1232434 7900523 := bstep (se 1 (by rfl) ⟨5925392, by rfl⟩ : syracuseStep 7900523 = 11850785) B11850785
theorem B1850087 : Blo 1232434 1850087 := bstep (se 1 (by rfl) ⟨1387565, by rfl⟩ : syracuseStep 1850087 = 2775131) B2775131
theorem B11863007 : Blo 1232434 11863007 := bstep (se 1 (by rfl) ⟨8897255, by rfl⟩ : syracuseStep 11863007 = 17794511) B17794511
theorem B1233391 : Blo 1232434 1233391 := bstep (se 1 (by rfl) ⟨925043, by rfl⟩ : syracuseStep 1233391 = 1850087) B1850087
theorem B5267015 : Blo 1232434 5267015 := bstep (se 1 (by rfl) ⟨3950261, by rfl⟩ : syracuseStep 5267015 = 7900523) B7900523
theorem B7908671 : Blo 1232434 7908671 := bstep (se 1 (by rfl) ⟨5931503, by rfl⟩ : syracuseStep 7908671 = 11863007) B11863007
theorem B3511343 : Blo 1232434 3511343 := bstep (se 1 (by rfl) ⟨2633507, by rfl⟩ : syracuseStep 3511343 = 5267015) B5267015
theorem B5272447 : Blo 1232434 5272447 := bstep (se 1 (by rfl) ⟨3954335, by rfl⟩ : syracuseStep 5272447 = 7908671) B7908671
theorem B2340895 : Blo 1232434 2340895 := bstep (se 1 (by rfl) ⟨1755671, by rfl⟩ : syracuseStep 2340895 = 3511343) B3511343
theorem B3121193 : Blo 1232434 3121193 := bstep (se 2 (by rfl) ⟨1170447, by rfl⟩ : syracuseStep 3121193 = 2340895) B2340895
theorem B7029929 : Blo 1232434 7029929 := bstep (se 2 (by rfl) ⟨2636223, by rfl⟩ : syracuseStep 7029929 = 5272447) B5272447
theorem B2080795 : Blo 1232434 2080795 := bstep (se 1 (by rfl) ⟨1560596, by rfl⟩ : syracuseStep 2080795 = 3121193) B3121193
theorem B4686619 : Blo 1232434 4686619 := bstep (se 1 (by rfl) ⟨3514964, by rfl⟩ : syracuseStep 4686619 = 7029929) B7029929
theorem B2774393 : Blo 1232434 2774393 := bstep (se 2 (by rfl) ⟨1040397, by rfl⟩ : syracuseStep 2774393 = 2080795) B2080795
theorem B6248825 : Blo 1232434 6248825 := bstep (se 2 (by rfl) ⟨2343309, by rfl⟩ : syracuseStep 6248825 = 4686619) B4686619
theorem B4165883 : Blo 1232434 4165883 := bstep (se 1 (by rfl) ⟨3124412, by rfl⟩ : syracuseStep 4165883 = 6248825) B6248825
theorem B1849595 : Blo 1232434 1849595 := bstep (se 1 (by rfl) ⟨1387196, by rfl⟩ : syracuseStep 1849595 = 2774393) B2774393
theorem B2777255 : Blo 1232434 2777255 := bstep (se 1 (by rfl) ⟨2082941, by rfl⟩ : syracuseStep 2777255 = 4165883) B4165883
theorem B1233063 : Blo 1232434 1233063 := bstep (se 1 (by rfl) ⟨924797, by rfl⟩ : syracuseStep 1233063 = 1849595) B1849595
theorem B1851503 : Blo 1232434 1851503 := bstep (se 1 (by rfl) ⟨1388627, by rfl⟩ : syracuseStep 1851503 = 2777255) B2777255
theorem B1234335 : Blo 1232434 1234335 := bstep (se 1 (by rfl) ⟨925751, by rfl⟩ : syracuseStep 1234335 = 1851503) B1851503

theorem C0 (j : ℕ) (h1 : 308108 ≤ j) (h2 : j ≤ 308607) : Blo 1232434 (4 * j + 3) := by
  interval_cases j
  · exact B1232435
  · exact B1232439
  · exact B1232443
  · exact B1232447
  · exact B1232451
  · exact B1232455
  · exact B1232459
  · exact B1232463
  · exact B1232467
  · exact B1232471
  · exact B1232475
  · exact B1232479
  · exact B1232483
  · exact B1232487
  · exact B1232491
  · exact B1232495
  · exact B1232499
  · exact B1232503
  · exact B1232507
  · exact B1232511
  · exact B1232515
  · exact B1232519
  · exact B1232523
  · exact B1232527
  · exact B1232531
  · exact B1232535
  · exact B1232539
  · exact B1232543
  · exact B1232547
  · exact B1232551
  · exact B1232555
  · exact B1232559
  · exact B1232563
  · exact B1232567
  · exact B1232571
  · exact B1232575
  · exact B1232579
  · exact B1232583
  · exact B1232587
  · exact B1232591
  · exact B1232595
  · exact B1232599
  · exact B1232603
  · exact B1232607
  · exact B1232611
  · exact B1232615
  · exact B1232619
  · exact B1232623
  · exact B1232627
  · exact B1232631
  · exact B1232635
  · exact B1232639
  · exact B1232643
  · exact B1232647
  · exact B1232651
  · exact B1232655
  · exact B1232659
  · exact B1232663
  · exact B1232667
  · exact B1232671
  · exact B1232675
  · exact B1232679
  · exact B1232683
  · exact B1232687
  · exact B1232691
  · exact B1232695
  · exact B1232699
  · exact B1232703
  · exact B1232707
  · exact B1232711
  · exact B1232715
  · exact B1232719
  · exact B1232723
  · exact B1232727
  · exact B1232731
  · exact B1232735
  · exact B1232739
  · exact B1232743
  · exact B1232747
  · exact B1232751
  · exact B1232755
  · exact B1232759
  · exact B1232763
  · exact B1232767
  · exact B1232771
  · exact B1232775
  · exact B1232779
  · exact B1232783
  · exact B1232787
  · exact B1232791
  · exact B1232795
  · exact B1232799
  · exact B1232803
  · exact B1232807
  · exact B1232811
  · exact B1232815
  · exact B1232819
  · exact B1232823
  · exact B1232827
  · exact B1232831
  · exact B1232835
  · exact B1232839
  · exact B1232843
  · exact B1232847
  · exact B1232851
  · exact B1232855
  · exact B1232859
  · exact B1232863
  · exact B1232867
  · exact B1232871
  · exact B1232875
  · exact B1232879
  · exact B1232883
  · exact B1232887
  · exact B1232891
  · exact B1232895
  · exact B1232899
  · exact B1232903
  · exact B1232907
  · exact B1232911
  · exact B1232915
  · exact B1232919
  · exact B1232923
  · exact B1232927
  · exact B1232931
  · exact B1232935
  · exact B1232939
  · exact B1232943
  · exact B1232947
  · exact B1232951
  · exact B1232955
  · exact B1232959
  · exact B1232963
  · exact B1232967
  · exact B1232971
  · exact B1232975
  · exact B1232979
  · exact B1232983
  · exact B1232987
  · exact B1232991
  · exact B1232995
  · exact B1232999
  · exact B1233003
  · exact B1233007
  · exact B1233011
  · exact B1233015
  · exact B1233019
  · exact B1233023
  · exact B1233027
  · exact B1233031
  · exact B1233035
  · exact B1233039
  · exact B1233043
  · exact B1233047
  · exact B1233051
  · exact B1233055
  · exact B1233059
  · exact B1233063
  · exact B1233067
  · exact B1233071
  · exact B1233075
  · exact B1233079
  · exact B1233083
  · exact B1233087
  · exact B1233091
  · exact B1233095
  · exact B1233099
  · exact B1233103
  · exact B1233107
  · exact B1233111
  · exact B1233115
  · exact B1233119
  · exact B1233123
  · exact B1233127
  · exact B1233131
  · exact B1233135
  · exact B1233139
  · exact B1233143
  · exact B1233147
  · exact B1233151
  · exact B1233155
  · exact B1233159
  · exact B1233163
  · exact B1233167
  · exact B1233171
  · exact B1233175
  · exact B1233179
  · exact B1233183
  · exact B1233187
  · exact B1233191
  · exact B1233195
  · exact B1233199
  · exact B1233203
  · exact B1233207
  · exact B1233211
  · exact B1233215
  · exact B1233219
  · exact B1233223
  · exact B1233227
  · exact B1233231
  · exact B1233235
  · exact B1233239
  · exact B1233243
  · exact B1233247
  · exact B1233251
  · exact B1233255
  · exact B1233259
  · exact B1233263
  · exact B1233267
  · exact B1233271
  · exact B1233275
  · exact B1233279
  · exact B1233283
  · exact B1233287
  · exact B1233291
  · exact B1233295
  · exact B1233299
  · exact B1233303
  · exact B1233307
  · exact B1233311
  · exact B1233315
  · exact B1233319
  · exact B1233323
  · exact B1233327
  · exact B1233331
  · exact B1233335
  · exact B1233339
  · exact B1233343
  · exact B1233347
  · exact B1233351
  · exact B1233355
  · exact B1233359
  · exact B1233363
  · exact B1233367
  · exact B1233371
  · exact B1233375
  · exact B1233379
  · exact B1233383
  · exact B1233387
  · exact B1233391
  · exact B1233395
  · exact B1233399
  · exact B1233403
  · exact B1233407
  · exact B1233411
  · exact B1233415
  · exact B1233419
  · exact B1233423
  · exact B1233427
  · exact B1233431
  · exact B1233435
  · exact B1233439
  · exact B1233443
  · exact B1233447
  · exact B1233451
  · exact B1233455
  · exact B1233459
  · exact B1233463
  · exact B1233467
  · exact B1233471
  · exact B1233475
  · exact B1233479
  · exact B1233483
  · exact B1233487
  · exact B1233491
  · exact B1233495
  · exact B1233499
  · exact B1233503
  · exact B1233507
  · exact B1233511
  · exact B1233515
  · exact B1233519
  · exact B1233523
  · exact B1233527
  · exact B1233531
  · exact B1233535
  · exact B1233539
  · exact B1233543
  · exact B1233547
  · exact B1233551
  · exact B1233555
  · exact B1233559
  · exact B1233563
  · exact B1233567
  · exact B1233571
  · exact B1233575
  · exact B1233579
  · exact B1233583
  · exact B1233587
  · exact B1233591
  · exact B1233595
  · exact B1233599
  · exact B1233603
  · exact B1233607
  · exact B1233611
  · exact B1233615
  · exact B1233619
  · exact B1233623
  · exact B1233627
  · exact B1233631
  · exact B1233635
  · exact B1233639
  · exact B1233643
  · exact B1233647
  · exact B1233651
  · exact B1233655
  · exact B1233659
  · exact B1233663
  · exact B1233667
  · exact B1233671
  · exact B1233675
  · exact B1233679
  · exact B1233683
  · exact B1233687
  · exact B1233691
  · exact B1233695
  · exact B1233699
  · exact B1233703
  · exact B1233707
  · exact B1233711
  · exact B1233715
  · exact B1233719
  · exact B1233723
  · exact B1233727
  · exact B1233731
  · exact B1233735
  · exact B1233739
  · exact B1233743
  · exact B1233747
  · exact B1233751
  · exact B1233755
  · exact B1233759
  · exact B1233763
  · exact B1233767
  · exact B1233771
  · exact B1233775
  · exact B1233779
  · exact B1233783
  · exact B1233787
  · exact B1233791
  · exact B1233795
  · exact B1233799
  · exact B1233803
  · exact B1233807
  · exact B1233811
  · exact B1233815
  · exact B1233819
  · exact B1233823
  · exact B1233827
  · exact B1233831
  · exact B1233835
  · exact B1233839
  · exact B1233843
  · exact B1233847
  · exact B1233851
  · exact B1233855
  · exact B1233859
  · exact B1233863
  · exact B1233867
  · exact B1233871
  · exact B1233875
  · exact B1233879
  · exact B1233883
  · exact B1233887
  · exact B1233891
  · exact B1233895
  · exact B1233899
  · exact B1233903
  · exact B1233907
  · exact B1233911
  · exact B1233915
  · exact B1233919
  · exact B1233923
  · exact B1233927
  · exact B1233931
  · exact B1233935
  · exact B1233939
  · exact B1233943
  · exact B1233947
  · exact B1233951
  · exact B1233955
  · exact B1233959
  · exact B1233963
  · exact B1233967
  · exact B1233971
  · exact B1233975
  · exact B1233979
  · exact B1233983
  · exact B1233987
  · exact B1233991
  · exact B1233995
  · exact B1233999
  · exact B1234003
  · exact B1234007
  · exact B1234011
  · exact B1234015
  · exact B1234019
  · exact B1234023
  · exact B1234027
  · exact B1234031
  · exact B1234035
  · exact B1234039
  · exact B1234043
  · exact B1234047
  · exact B1234051
  · exact B1234055
  · exact B1234059
  · exact B1234063
  · exact B1234067
  · exact B1234071
  · exact B1234075
  · exact B1234079
  · exact B1234083
  · exact B1234087
  · exact B1234091
  · exact B1234095
  · exact B1234099
  · exact B1234103
  · exact B1234107
  · exact B1234111
  · exact B1234115
  · exact B1234119
  · exact B1234123
  · exact B1234127
  · exact B1234131
  · exact B1234135
  · exact B1234139
  · exact B1234143
  · exact B1234147
  · exact B1234151
  · exact B1234155
  · exact B1234159
  · exact B1234163
  · exact B1234167
  · exact B1234171
  · exact B1234175
  · exact B1234179
  · exact B1234183
  · exact B1234187
  · exact B1234191
  · exact B1234195
  · exact B1234199
  · exact B1234203
  · exact B1234207
  · exact B1234211
  · exact B1234215
  · exact B1234219
  · exact B1234223
  · exact B1234227
  · exact B1234231
  · exact B1234235
  · exact B1234239
  · exact B1234243
  · exact B1234247
  · exact B1234251
  · exact B1234255
  · exact B1234259
  · exact B1234263
  · exact B1234267
  · exact B1234271
  · exact B1234275
  · exact B1234279
  · exact B1234283
  · exact B1234287
  · exact B1234291
  · exact B1234295
  · exact B1234299
  · exact B1234303
  · exact B1234307
  · exact B1234311
  · exact B1234315
  · exact B1234319
  · exact B1234323
  · exact B1234327
  · exact B1234331
  · exact B1234335
  · exact B1234339
  · exact B1234343
  · exact B1234347
  · exact B1234351
  · exact B1234355
  · exact B1234359
  · exact B1234363
  · exact B1234367
  · exact B1234371
  · exact B1234375
  · exact B1234379
  · exact B1234383
  · exact B1234387
  · exact B1234391
  · exact B1234395
  · exact B1234399
  · exact B1234403
  · exact B1234407
  · exact B1234411
  · exact B1234415
  · exact B1234419
  · exact B1234423
  · exact B1234427
  · exact B1234431

theorem solution (m : ℕ) (hlo : 1232434 ≤ m) (hhi : m ≤ 1234434) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 308108 ≤ j := by omega
    have hj2 : j ≤ 308607 := by omega
    have hb : Blo 1232434 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
