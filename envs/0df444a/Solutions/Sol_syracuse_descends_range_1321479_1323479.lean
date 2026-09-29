-- Prove2me | solution 1 for syracuse_descends_range_1321479_1323479
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:35.268152+00:00
-- url     : https://prove2.me/submissions/46f7b039-7b6b-4678-895d-1806b9fffcf8

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


theorem B1982477 : Blo 1321479 1982477 := bbase (se 3 (by rfl) ⟨371714, by rfl⟩ : syracuseStep 1982477 = 743429) (by norm_num)
theorem B2973725 : Blo 1321479 2973725 := bbase (se 3 (by rfl) ⟨557573, by rfl⟩ : syracuseStep 2973725 = 1115147) (by norm_num)
theorem B1982501 : Blo 1321479 1982501 := bbase (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) (by norm_num)
theorem B1982525 : Blo 1321479 1982525 := bbase (se 3 (by rfl) ⟨371723, by rfl⟩ : syracuseStep 1982525 = 743447) (by norm_num)
theorem B1982549 : Blo 1321479 1982549 := bbase (se 8 (by rfl) ⟨11616, by rfl⟩ : syracuseStep 1982549 = 23233) (by norm_num)
theorem B2973797 : Blo 1321479 2973797 := bbase (se 4 (by rfl) ⟨278793, by rfl⟩ : syracuseStep 2973797 = 557587) (by norm_num)
theorem B1982573 : Blo 1321479 1982573 := bbase (se 3 (by rfl) ⟨371732, by rfl⟩ : syracuseStep 1982573 = 743465) (by norm_num)
theorem B7528565 : Blo 1321479 7528565 := bbase (se 5 (by rfl) ⟨352901, by rfl⟩ : syracuseStep 7528565 = 705803) (by norm_num)
theorem B1982597 : Blo 1321479 1982597 := bbase (se 4 (by rfl) ⟨185868, by rfl⟩ : syracuseStep 1982597 = 371737) (by norm_num)
theorem B4464773 : Blo 1321479 4464773 := bbase (se 4 (by rfl) ⟨418572, by rfl⟩ : syracuseStep 4464773 = 837145) (by norm_num)
theorem B4767893 : Blo 1321479 4767893 := bbase (se 6 (by rfl) ⟨111747, by rfl⟩ : syracuseStep 4767893 = 223495) (by norm_num)
theorem B1982621 : Blo 1321479 1982621 := bbase (se 3 (by rfl) ⟨371741, by rfl⟩ : syracuseStep 1982621 = 743483) (by norm_num)
theorem B6693029 : Blo 1321479 6693029 := bbase (se 4 (by rfl) ⟨627471, by rfl⟩ : syracuseStep 6693029 = 1254943) (by norm_num)
theorem B2973869 : Blo 1321479 2973869 := bbase (se 3 (by rfl) ⟨557600, by rfl⟩ : syracuseStep 2973869 = 1115201) (by norm_num)
theorem B1982645 : Blo 1321479 1982645 := bbase (se 5 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 1982645 = 185873) (by norm_num)
theorem B1589441 : Blo 1321479 1589441 := bbase (se 2 (by rfl) ⟨596040, by rfl⟩ : syracuseStep 1589441 = 1192081) (by norm_num)
theorem B1982669 : Blo 1321479 1982669 := bbase (se 3 (by rfl) ⟨371750, by rfl⟩ : syracuseStep 1982669 = 743501) (by norm_num)
theorem B10035413 : Blo 1321479 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B1982693 : Blo 1321479 1982693 := bbase (se 4 (by rfl) ⟨185877, by rfl⟩ : syracuseStep 1982693 = 371755) (by norm_num)
theorem B1884397 : Blo 1321479 1884397 := bbase (se 3 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 1884397 = 706649) (by norm_num)
theorem B2973941 : Blo 1321479 2973941 := bbase (se 5 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 2973941 = 278807) (by norm_num)
theorem B2826485 : Blo 1321479 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B1982717 : Blo 1321479 1982717 := bbase (se 3 (by rfl) ⟨371759, by rfl⟩ : syracuseStep 1982717 = 743519) (by norm_num)
theorem B1982741 : Blo 1321479 1982741 := bbase (se 6 (by rfl) ⟨46470, by rfl⟩ : syracuseStep 1982741 = 92941) (by norm_num)
theorem B2449693 : Blo 1321479 2449693 := bbase (se 3 (by rfl) ⟨459317, by rfl⟩ : syracuseStep 2449693 = 918635) (by norm_num)
theorem B1982765 : Blo 1321479 1982765 := bbase (se 3 (by rfl) ⟨371768, by rfl⟩ : syracuseStep 1982765 = 743537) (by norm_num)
theorem B1909045 : Blo 1321479 1909045 := bbase (se 5 (by rfl) ⟨89486, by rfl⟩ : syracuseStep 1909045 = 178973) (by norm_num)
theorem B2974013 : Blo 1321479 2974013 := bbase (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) (by norm_num)
theorem B1982789 : Blo 1321479 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B1810765 : Blo 1321479 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B1982813 : Blo 1321479 1982813 := bbase (se 3 (by rfl) ⟨371777, by rfl⟩ : syracuseStep 1982813 = 743555) (by norm_num)
theorem B1982837 : Blo 1321479 1982837 := bbase (se 5 (by rfl) ⟨92945, by rfl⟩ : syracuseStep 1982837 = 185891) (by norm_num)
theorem B2974085 : Blo 1321479 2974085 := bbase (se 4 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 2974085 = 557641) (by norm_num)
theorem B1982861 : Blo 1321479 1982861 := bbase (se 3 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 1982861 = 743573) (by norm_num)
theorem B1589653 : Blo 1321479 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B1982885 : Blo 1321479 1982885 := bbase (se 4 (by rfl) ⟨185895, by rfl⟩ : syracuseStep 1982885 = 371791) (by norm_num)
theorem B1982909 : Blo 1321479 1982909 := bbase (se 3 (by rfl) ⟨371795, by rfl⟩ : syracuseStep 1982909 = 743591) (by norm_num)
theorem B2974157 : Blo 1321479 2974157 := bbase (se 3 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 2974157 = 1115309) (by norm_num)
theorem B1982933 : Blo 1321479 1982933 := bbase (se 7 (by rfl) ⟨23237, by rfl⟩ : syracuseStep 1982933 = 46475) (by norm_num)
theorem B1982957 : Blo 1321479 1982957 := bbase (se 3 (by rfl) ⟨371804, by rfl⟩ : syracuseStep 1982957 = 743609) (by norm_num)
theorem B1982981 : Blo 1321479 1982981 := bbase (se 4 (by rfl) ⟨185904, by rfl⟩ : syracuseStep 1982981 = 371809) (by norm_num)
theorem B2974229 : Blo 1321479 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B11305493 : Blo 1321479 11305493 := bbase (se 6 (by rfl) ⟨264972, by rfl⟩ : syracuseStep 11305493 = 529945) (by norm_num)
theorem B1983005 : Blo 1321479 1983005 := bbase (se 3 (by rfl) ⟨371813, by rfl⟩ : syracuseStep 1983005 = 743627) (by norm_num)
theorem B1589797 : Blo 1321479 1589797 := bbase (se 4 (by rfl) ⟨149043, by rfl⟩ : syracuseStep 1589797 = 298087) (by norm_num)
theorem B5644853 : Blo 1321479 5644853 := bbase (se 5 (by rfl) ⟨264602, by rfl⟩ : syracuseStep 5644853 = 529205) (by norm_num)
theorem B1983029 : Blo 1321479 1983029 := bbase (se 5 (by rfl) ⟨92954, by rfl⟩ : syracuseStep 1983029 = 185909) (by norm_num)
theorem B4465205 : Blo 1321479 4465205 := bbase (se 5 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 4465205 = 418613) (by norm_num)
theorem B1983053 : Blo 1321479 1983053 := bbase (se 3 (by rfl) ⟨371822, by rfl⟩ : syracuseStep 1983053 = 743645) (by norm_num)
theorem B2974301 : Blo 1321479 2974301 := bbase (se 3 (by rfl) ⟨557681, by rfl⟩ : syracuseStep 2974301 = 1115363) (by norm_num)
theorem B1983077 : Blo 1321479 1983077 := bbase (se 4 (by rfl) ⟨185913, by rfl⟩ : syracuseStep 1983077 = 371827) (by norm_num)
theorem B4022885 : Blo 1321479 4022885 := bbase (se 4 (by rfl) ⟨377145, by rfl⟩ : syracuseStep 4022885 = 754291) (by norm_num)
theorem B1983101 : Blo 1321479 1983101 := bbase (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) (by norm_num)
theorem B1983125 : Blo 1321479 1983125 := bbase (se 6 (by rfl) ⟨46479, by rfl⟩ : syracuseStep 1983125 = 92959) (by norm_num)
theorem B2974373 : Blo 1321479 2974373 := bbase (se 4 (by rfl) ⟨278847, by rfl⟩ : syracuseStep 2974373 = 557695) (by norm_num)
theorem B1983149 : Blo 1321479 1983149 := bbase (se 3 (by rfl) ⟨371840, by rfl⟩ : syracuseStep 1983149 = 743681) (by norm_num)
theorem B1983173 : Blo 1321479 1983173 := bbase (se 4 (by rfl) ⟨185922, by rfl⟩ : syracuseStep 1983173 = 371845) (by norm_num)
theorem B3572437 : Blo 1321479 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B1983197 : Blo 1321479 1983197 := bbase (se 3 (by rfl) ⟨371849, by rfl⟩ : syracuseStep 1983197 = 743699) (by norm_num)
theorem B2974445 : Blo 1321479 2974445 := bbase (se 3 (by rfl) ⟨557708, by rfl⟩ : syracuseStep 2974445 = 1115417) (by norm_num)
theorem B1983221 : Blo 1321479 1983221 := bbase (se 5 (by rfl) ⟨92963, by rfl⟩ : syracuseStep 1983221 = 185927) (by norm_num)
theorem B1983245 : Blo 1321479 1983245 := bbase (se 3 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 1983245 = 743717) (by norm_num)
theorem B2384653 : Blo 1321479 2384653 := bbase (se 3 (by rfl) ⟨447122, by rfl⟩ : syracuseStep 2384653 = 894245) (by norm_num)
theorem B1983269 : Blo 1321479 1983269 := bbase (se 4 (by rfl) ⟨185931, by rfl⟩ : syracuseStep 1983269 = 371863) (by norm_num)
theorem B2974517 : Blo 1321479 2974517 := bbase (se 5 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 2974517 = 278861) (by norm_num)
theorem B1983293 : Blo 1321479 1983293 := bbase (se 3 (by rfl) ⟨371867, by rfl⟩ : syracuseStep 1983293 = 743735) (by norm_num)
theorem B4236101 : Blo 1321479 4236101 := bbase (se 4 (by rfl) ⟨397134, by rfl⟩ : syracuseStep 4236101 = 794269) (by norm_num)
theorem B1983317 : Blo 1321479 1983317 := bbase (se 9 (by rfl) ⟨5810, by rfl⟩ : syracuseStep 1983317 = 11621) (by norm_num)
theorem B1983341 : Blo 1321479 1983341 := bbase (se 3 (by rfl) ⟨371876, by rfl⟩ : syracuseStep 1983341 = 743753) (by norm_num)
theorem B1696621 : Blo 1321479 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B2974589 : Blo 1321479 2974589 := bbase (se 3 (by rfl) ⟨557735, by rfl⟩ : syracuseStep 2974589 = 1115471) (by norm_num)
theorem B1983365 : Blo 1321479 1983365 := bbase (se 4 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 1983365 = 371881) (by norm_num)
theorem B1983389 : Blo 1321479 1983389 := bbase (se 3 (by rfl) ⟨371885, by rfl⟩ : syracuseStep 1983389 = 743771) (by norm_num)
theorem B2679733 : Blo 1321479 2679733 := bbase (se 5 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 2679733 = 251225) (by norm_num)
theorem B1983413 : Blo 1321479 1983413 := bbase (se 5 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 1983413 = 185945) (by norm_num)
theorem B2974661 : Blo 1321479 2974661 := bbase (se 4 (by rfl) ⟨278874, by rfl⟩ : syracuseStep 2974661 = 557749) (by norm_num)
theorem B1983437 : Blo 1321479 1983437 := bbase (se 3 (by rfl) ⟨371894, by rfl⟩ : syracuseStep 1983437 = 743789) (by norm_num)
theorem B15074261 : Blo 1321479 15074261 := bbase (se 7 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 15074261 = 353303) (by norm_num)
theorem B1983461 : Blo 1321479 1983461 := bbase (se 4 (by rfl) ⟨185949, by rfl⟩ : syracuseStep 1983461 = 371899) (by norm_num)
theorem B4465637 : Blo 1321479 4465637 := bbase (se 4 (by rfl) ⟨418653, by rfl⟩ : syracuseStep 4465637 = 837307) (by norm_num)
theorem B1983485 : Blo 1321479 1983485 := bbase (se 3 (by rfl) ⟨371903, by rfl⟩ : syracuseStep 1983485 = 743807) (by norm_num)
theorem B2974733 : Blo 1321479 2974733 := bbase (se 3 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 2974733 = 1115525) (by norm_num)
theorem B3392525 : Blo 1321479 3392525 := bbase (se 3 (by rfl) ⟨636098, by rfl⟩ : syracuseStep 3392525 = 1272197) (by norm_num)
theorem B1983509 : Blo 1321479 1983509 := bbase (se 6 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 1983509 = 92977) (by norm_num)
theorem B1983533 : Blo 1321479 1983533 := bbase (se 3 (by rfl) ⟨371912, by rfl⟩ : syracuseStep 1983533 = 743825) (by norm_num)
theorem B1983557 : Blo 1321479 1983557 := bbase (se 4 (by rfl) ⟨185958, by rfl⟩ : syracuseStep 1983557 = 371917) (by norm_num)
theorem B2974805 : Blo 1321479 2974805 := bbase (se 8 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 2974805 = 34861) (by norm_num)
theorem B1983581 : Blo 1321479 1983581 := bbase (se 3 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 1983581 = 743843) (by norm_num)
theorem B1983605 : Blo 1321479 1983605 := bbase (se 5 (by rfl) ⟨92981, by rfl⟩ : syracuseStep 1983605 = 185963) (by norm_num)
theorem B4768901 : Blo 1321479 4768901 := bbase (se 4 (by rfl) ⟨447084, by rfl⟩ : syracuseStep 4768901 = 894169) (by norm_num)
theorem B1983629 : Blo 1321479 1983629 := bbase (se 3 (by rfl) ⟨371930, by rfl⟩ : syracuseStep 1983629 = 743861) (by norm_num)
theorem B2974877 : Blo 1321479 2974877 := bbase (se 3 (by rfl) ⟨557789, by rfl⟩ : syracuseStep 2974877 = 1115579) (by norm_num)
theorem B1983653 : Blo 1321479 1983653 := bbase (se 4 (by rfl) ⟨185967, by rfl⟩ : syracuseStep 1983653 = 371935) (by norm_num)
theorem B1983677 : Blo 1321479 1983677 := bbase (se 3 (by rfl) ⟨371939, by rfl⟩ : syracuseStep 1983677 = 743879) (by norm_num)
theorem B5022917 : Blo 1321479 5022917 := bbase (se 4 (by rfl) ⟨470898, by rfl⟩ : syracuseStep 5022917 = 941797) (by norm_num)
theorem B1983701 : Blo 1321479 1983701 := bbase (se 7 (by rfl) ⟨23246, by rfl⟩ : syracuseStep 1983701 = 46493) (by norm_num)
theorem B2974949 : Blo 1321479 2974949 := bbase (se 4 (by rfl) ⟨278901, by rfl⟩ : syracuseStep 2974949 = 557803) (by norm_num)
theorem B1983725 : Blo 1321479 1983725 := bbase (se 3 (by rfl) ⟨371948, by rfl⟩ : syracuseStep 1983725 = 743897) (by norm_num)
theorem B1983749 : Blo 1321479 1983749 := bbase (se 4 (by rfl) ⟨185976, by rfl⟩ : syracuseStep 1983749 = 371953) (by norm_num)
theorem B1983773 : Blo 1321479 1983773 := bbase (se 3 (by rfl) ⟨371957, by rfl⟩ : syracuseStep 1983773 = 743915) (by norm_num)
theorem B2975021 : Blo 1321479 2975021 := bbase (se 3 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 2975021 = 1115633) (by norm_num)
theorem B1983797 : Blo 1321479 1983797 := bbase (se 5 (by rfl) ⟨92990, by rfl⟩ : syracuseStep 1983797 = 185981) (by norm_num)
theorem B1983821 : Blo 1321479 1983821 := bbase (se 3 (by rfl) ⟨371966, by rfl⟩ : syracuseStep 1983821 = 743933) (by norm_num)
theorem B1983845 : Blo 1321479 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B2975093 : Blo 1321479 2975093 := bbase (se 5 (by rfl) ⟨139457, by rfl⟩ : syracuseStep 2975093 = 278915) (by norm_num)
theorem B1983869 : Blo 1321479 1983869 := bbase (se 3 (by rfl) ⟨371975, by rfl⟩ : syracuseStep 1983869 = 743951) (by norm_num)
theorem B1672589 : Blo 1321479 1672589 := bbase (se 3 (by rfl) ⟨313610, by rfl⟩ : syracuseStep 1672589 = 627221) (by norm_num)
theorem B1983893 : Blo 1321479 1983893 := bbase (se 6 (by rfl) ⟨46497, by rfl⟩ : syracuseStep 1983893 = 92995) (by norm_num)
theorem B4466069 : Blo 1321479 4466069 := bbase (se 6 (by rfl) ⟨104673, by rfl⟩ : syracuseStep 4466069 = 209347) (by norm_num)
theorem B2680229 : Blo 1321479 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B5727653 : Blo 1321479 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B1983917 : Blo 1321479 1983917 := bbase (se 3 (by rfl) ⟨371984, by rfl⟩ : syracuseStep 1983917 = 743969) (by norm_num)
theorem B6694325 : Blo 1321479 6694325 := bbase (se 5 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 6694325 = 627593) (by norm_num)
theorem B2975165 : Blo 1321479 2975165 := bbase (se 3 (by rfl) ⟨557843, by rfl⟩ : syracuseStep 2975165 = 1115687) (by norm_num)
theorem B1508797 : Blo 1321479 1508797 := bbase (se 3 (by rfl) ⟨282899, by rfl⟩ : syracuseStep 1508797 = 565799) (by norm_num)
theorem B1672645 : Blo 1321479 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B1983941 : Blo 1321479 1983941 := bbase (se 4 (by rfl) ⟨185994, by rfl⟩ : syracuseStep 1983941 = 371989) (by norm_num)
theorem B1983965 : Blo 1321479 1983965 := bbase (se 3 (by rfl) ⟨371993, by rfl⟩ : syracuseStep 1983965 = 743987) (by norm_num)
theorem B5023205 : Blo 1321479 5023205 := bbase (se 4 (by rfl) ⟨470925, by rfl⟩ : syracuseStep 5023205 = 941851) (by norm_num)
theorem B1983989 : Blo 1321479 1983989 := bbase (se 5 (by rfl) ⟨92999, by rfl⟩ : syracuseStep 1983989 = 185999) (by norm_num)
theorem B3311101 : Blo 1321479 3311101 := bbase (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) (by norm_num)
theorem B2975237 : Blo 1321479 2975237 := bbase (se 4 (by rfl) ⟨278928, by rfl⟩ : syracuseStep 2975237 = 557857) (by norm_num)
theorem B1984013 : Blo 1321479 1984013 := bbase (se 3 (by rfl) ⟨372002, by rfl⟩ : syracuseStep 1984013 = 744005) (by norm_num)
theorem B1672741 : Blo 1321479 1672741 := bbase (se 4 (by rfl) ⟨156819, by rfl⟩ : syracuseStep 1672741 = 313639) (by norm_num)
theorem B1984037 : Blo 1321479 1984037 := bbase (se 4 (by rfl) ⟨186003, by rfl⟩ : syracuseStep 1984037 = 372007) (by norm_num)
theorem B1984061 : Blo 1321479 1984061 := bbase (se 3 (by rfl) ⟨372011, by rfl⟩ : syracuseStep 1984061 = 744023) (by norm_num)
theorem B4236869 : Blo 1321479 4236869 := bbase (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) (by norm_num)
theorem B2975309 : Blo 1321479 2975309 := bbase (se 3 (by rfl) ⟨557870, by rfl⟩ : syracuseStep 2975309 = 1115741) (by norm_num)
theorem B1984085 : Blo 1321479 1984085 := bbase (se 8 (by rfl) ⟨11625, by rfl⟩ : syracuseStep 1984085 = 23251) (by norm_num)
theorem B1984109 : Blo 1321479 1984109 := bbase (se 3 (by rfl) ⟨372020, by rfl⟩ : syracuseStep 1984109 = 744041) (by norm_num)
theorem B1984133 : Blo 1321479 1984133 := bbase (se 4 (by rfl) ⟨186012, by rfl⟩ : syracuseStep 1984133 = 372025) (by norm_num)
theorem B2975381 : Blo 1321479 2975381 := bbase (se 6 (by rfl) ⟨69735, by rfl⟩ : syracuseStep 2975381 = 139471) (by norm_num)
theorem B1984157 : Blo 1321479 1984157 := bbase (se 3 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 1984157 = 744059) (by norm_num)
theorem B1984181 : Blo 1321479 1984181 := bbase (se 5 (by rfl) ⟨93008, by rfl⟩ : syracuseStep 1984181 = 186017) (by norm_num)
theorem B1984205 : Blo 1321479 1984205 := bbase (se 3 (by rfl) ⟨372038, by rfl⟩ : syracuseStep 1984205 = 744077) (by norm_num)
theorem B1672913 : Blo 1321479 1672913 := bbase (se 2 (by rfl) ⟨627342, by rfl⟩ : syracuseStep 1672913 = 1254685) (by norm_num)
theorem B2975453 : Blo 1321479 2975453 := bbase (se 3 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 2975453 = 1115795) (by norm_num)
theorem B1984229 : Blo 1321479 1984229 := bbase (se 4 (by rfl) ⟨186021, by rfl⟩ : syracuseStep 1984229 = 372043) (by norm_num)
theorem B2229997 : Blo 1321479 2229997 := bbase (se 3 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 2229997 = 836249) (by norm_num)
theorem B1984253 : Blo 1321479 1984253 := bbase (se 3 (by rfl) ⟨372047, by rfl⟩ : syracuseStep 1984253 = 744095) (by norm_num)
theorem B1672969 : Blo 1321479 1672969 := bbase (se 2 (by rfl) ⟨627363, by rfl⟩ : syracuseStep 1672969 = 1254727) (by norm_num)
theorem B1984277 : Blo 1321479 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B2975525 : Blo 1321479 2975525 := bbase (se 4 (by rfl) ⟨278955, by rfl⟩ : syracuseStep 2975525 = 557911) (by norm_num)
theorem B1984301 : Blo 1321479 1984301 := bbase (se 3 (by rfl) ⟨372056, by rfl⟩ : syracuseStep 1984301 = 744113) (by norm_num)
theorem B2230085 : Blo 1321479 2230085 := bbase (se 4 (by rfl) ⟨209070, by rfl⟩ : syracuseStep 2230085 = 418141) (by norm_num)
theorem B1984325 : Blo 1321479 1984325 := bbase (se 4 (by rfl) ⟨186030, by rfl⟩ : syracuseStep 1984325 = 372061) (by norm_num)
theorem B4466501 : Blo 1321479 4466501 := bbase (se 4 (by rfl) ⟨418734, by rfl⟩ : syracuseStep 4466501 = 837469) (by norm_num)
theorem B1984349 : Blo 1321479 1984349 := bbase (se 3 (by rfl) ⟨372065, by rfl⟩ : syracuseStep 1984349 = 744131) (by norm_num)
theorem B1632101 : Blo 1321479 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B1673065 : Blo 1321479 1673065 := bbase (se 2 (by rfl) ⟨627399, by rfl⟩ : syracuseStep 1673065 = 1254799) (by norm_num)
theorem B2975597 : Blo 1321479 2975597 := bbase (se 3 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 2975597 = 1115849) (by norm_num)
theorem B1984373 : Blo 1321479 1984373 := bbase (se 5 (by rfl) ⟨93017, by rfl⟩ : syracuseStep 1984373 = 186035) (by norm_num)
theorem B1984397 : Blo 1321479 1984397 := bbase (se 3 (by rfl) ⟨372074, by rfl⟩ : syracuseStep 1984397 = 744149) (by norm_num)
theorem B1984421 : Blo 1321479 1984421 := bbase (se 4 (by rfl) ⟨186039, by rfl⟩ : syracuseStep 1984421 = 372079) (by norm_num)
theorem B2975669 : Blo 1321479 2975669 := bbase (se 5 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 2975669 = 278969) (by norm_num)
theorem B1984445 : Blo 1321479 1984445 := bbase (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) (by norm_num)
theorem B2230213 : Blo 1321479 2230213 := bbase (se 4 (by rfl) ⟨209082, by rfl⟩ : syracuseStep 2230213 = 418165) (by norm_num)
theorem B1984469 : Blo 1321479 1984469 := bbase (se 7 (by rfl) ⟨23255, by rfl⟩ : syracuseStep 1984469 = 46511) (by norm_num)
theorem B1984493 : Blo 1321479 1984493 := bbase (se 3 (by rfl) ⟨372092, by rfl⟩ : syracuseStep 1984493 = 744185) (by norm_num)
theorem B2975741 : Blo 1321479 2975741 := bbase (se 3 (by rfl) ⟨557951, by rfl⟩ : syracuseStep 2975741 = 1115903) (by norm_num)
theorem B1984517 : Blo 1321479 1984517 := bbase (se 4 (by rfl) ⟨186048, by rfl⟩ : syracuseStep 1984517 = 372097) (by norm_num)
theorem B1673237 : Blo 1321479 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B2230301 : Blo 1321479 2230301 := bbase (se 3 (by rfl) ⟨418181, by rfl⟩ : syracuseStep 2230301 = 836363) (by norm_num)
theorem B1984541 : Blo 1321479 1984541 := bbase (se 3 (by rfl) ⟨372101, by rfl⟩ : syracuseStep 1984541 = 744203) (by norm_num)
theorem B1984565 : Blo 1321479 1984565 := bbase (se 5 (by rfl) ⟨93026, by rfl⟩ : syracuseStep 1984565 = 186053) (by norm_num)
theorem B2508869 : Blo 1321479 2508869 := bbase (se 4 (by rfl) ⟨235206, by rfl⟩ : syracuseStep 2508869 = 470413) (by norm_num)
theorem B2975813 : Blo 1321479 2975813 := bbase (se 4 (by rfl) ⟨278982, by rfl⟩ : syracuseStep 2975813 = 557965) (by norm_num)
theorem B4237381 : Blo 1321479 4237381 := bbase (se 4 (by rfl) ⟨397254, by rfl⟩ : syracuseStep 4237381 = 794509) (by norm_num)
theorem B1673293 : Blo 1321479 1673293 := bbase (se 3 (by rfl) ⟨313742, by rfl⟩ : syracuseStep 1673293 = 627485) (by norm_num)
theorem B1984589 : Blo 1321479 1984589 := bbase (se 3 (by rfl) ⟨372110, by rfl⟩ : syracuseStep 1984589 = 744221) (by norm_num)
theorem B1984613 : Blo 1321479 1984613 := bbase (se 4 (by rfl) ⟨186057, by rfl⟩ : syracuseStep 1984613 = 372115) (by norm_num)
theorem B2680949 : Blo 1321479 2680949 := bbase (se 5 (by rfl) ⟨125669, by rfl⟩ : syracuseStep 2680949 = 251339) (by norm_num)
theorem B1984637 : Blo 1321479 1984637 := bbase (se 3 (by rfl) ⟨372119, by rfl⟩ : syracuseStep 1984637 = 744239) (by norm_num)
theorem B2975885 : Blo 1321479 2975885 := bbase (se 3 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 2975885 = 1115957) (by norm_num)
theorem B1984661 : Blo 1321479 1984661 := bbase (se 6 (by rfl) ⟨46515, by rfl⟩ : syracuseStep 1984661 = 93031) (by norm_num)
theorem B2230429 : Blo 1321479 2230429 := bbase (se 3 (by rfl) ⟨418205, by rfl⟩ : syracuseStep 2230429 = 836411) (by norm_num)
theorem B1673389 : Blo 1321479 1673389 := bbase (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) (by norm_num)
theorem B1984685 : Blo 1321479 1984685 := bbase (se 3 (by rfl) ⟨372128, by rfl⟩ : syracuseStep 1984685 = 744257) (by norm_num)
theorem B1984709 : Blo 1321479 1984709 := bbase (se 4 (by rfl) ⟨186066, by rfl⟩ : syracuseStep 1984709 = 372133) (by norm_num)
theorem B1411273 : Blo 1321479 1411273 := bbase (se 2 (by rfl) ⟨529227, by rfl⟩ : syracuseStep 1411273 = 1058455) (by norm_num)
theorem B2975957 : Blo 1321479 2975957 := bbase (se 7 (by rfl) ⟨34874, by rfl⟩ : syracuseStep 2975957 = 69749) (by norm_num)
theorem B1984733 : Blo 1321479 1984733 := bbase (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) (by norm_num)
theorem B2230517 : Blo 1321479 2230517 := bbase (se 5 (by rfl) ⟨104555, by rfl⟩ : syracuseStep 2230517 = 209111) (by norm_num)
theorem B1984757 : Blo 1321479 1984757 := bbase (se 5 (by rfl) ⟨93035, by rfl⟩ : syracuseStep 1984757 = 186071) (by norm_num)
theorem B1984781 : Blo 1321479 1984781 := bbase (se 3 (by rfl) ⟨372146, by rfl⟩ : syracuseStep 1984781 = 744293) (by norm_num)
theorem B2976029 : Blo 1321479 2976029 := bbase (se 3 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 2976029 = 1116011) (by norm_num)
theorem B1984805 : Blo 1321479 1984805 := bbase (se 4 (by rfl) ⟨186075, by rfl⟩ : syracuseStep 1984805 = 372151) (by norm_num)
theorem B1984829 : Blo 1321479 1984829 := bbase (se 3 (by rfl) ⟨372155, by rfl⟩ : syracuseStep 1984829 = 744311) (by norm_num)
theorem B8472917 : Blo 1321479 8472917 := bbase (se 10 (by rfl) ⟨12411, by rfl⟩ : syracuseStep 8472917 = 24823) (by norm_num)
theorem B1984853 : Blo 1321479 1984853 := bbase (se 10 (by rfl) ⟨2907, by rfl⟩ : syracuseStep 1984853 = 5815) (by norm_num)
theorem B1673561 : Blo 1321479 1673561 := bbase (se 2 (by rfl) ⟨627585, by rfl⟩ : syracuseStep 1673561 = 1255171) (by norm_num)
theorem B2509157 : Blo 1321479 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B2976101 : Blo 1321479 2976101 := bbase (se 4 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 2976101 = 558019) (by norm_num)
theorem B1984877 : Blo 1321479 1984877 := bbase (se 3 (by rfl) ⟨372164, by rfl⟩ : syracuseStep 1984877 = 744329) (by norm_num)
theorem B2230645 : Blo 1321479 2230645 := bbase (se 5 (by rfl) ⟨104561, by rfl⟩ : syracuseStep 2230645 = 209123) (by norm_num)
theorem B1984901 : Blo 1321479 1984901 := bbase (se 4 (by rfl) ⟨186084, by rfl⟩ : syracuseStep 1984901 = 372169) (by norm_num)
theorem B1673617 : Blo 1321479 1673617 := bbase (se 2 (by rfl) ⟨627606, by rfl⟩ : syracuseStep 1673617 = 1255213) (by norm_num)
theorem B1984925 : Blo 1321479 1984925 := bbase (se 3 (by rfl) ⟨372173, by rfl⟩ : syracuseStep 1984925 = 744347) (by norm_num)
theorem B2976173 : Blo 1321479 2976173 := bbase (se 3 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 2976173 = 1116065) (by norm_num)
theorem B1984949 : Blo 1321479 1984949 := bbase (se 5 (by rfl) ⟨93044, by rfl⟩ : syracuseStep 1984949 = 186089) (by norm_num)
theorem B2230733 : Blo 1321479 2230733 := bbase (se 3 (by rfl) ⟨418262, by rfl⟩ : syracuseStep 2230733 = 836525) (by norm_num)
theorem B1984973 : Blo 1321479 1984973 := bbase (se 3 (by rfl) ⟨372182, by rfl⟩ : syracuseStep 1984973 = 744365) (by norm_num)
theorem B1984997 : Blo 1321479 1984997 := bbase (se 4 (by rfl) ⟨186093, by rfl⟩ : syracuseStep 1984997 = 372187) (by norm_num)
theorem B1673713 : Blo 1321479 1673713 := bbase (se 2 (by rfl) ⟨627642, by rfl⟩ : syracuseStep 1673713 = 1255285) (by norm_num)
theorem B2976245 : Blo 1321479 2976245 := bbase (se 5 (by rfl) ⟨139511, by rfl⟩ : syracuseStep 2976245 = 279023) (by norm_num)
theorem B2509309 : Blo 1321479 2509309 := bbase (se 3 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 2509309 = 940991) (by norm_num)
theorem B1985021 : Blo 1321479 1985021 := bbase (se 3 (by rfl) ⟨372191, by rfl⟩ : syracuseStep 1985021 = 744383) (by norm_num)
theorem B3574277 : Blo 1321479 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B1985045 : Blo 1321479 1985045 := bbase (se 6 (by rfl) ⟨46524, by rfl⟩ : syracuseStep 1985045 = 93049) (by norm_num)
theorem B5802533 : Blo 1321479 5802533 := bbase (se 4 (by rfl) ⟨543987, by rfl⟩ : syracuseStep 5802533 = 1087975) (by norm_num)
theorem B1985069 : Blo 1321479 1985069 := bbase (se 3 (by rfl) ⟨372200, by rfl⟩ : syracuseStep 1985069 = 744401) (by norm_num)
theorem B1813045 : Blo 1321479 1813045 := bbase (se 5 (by rfl) ⟨84986, by rfl⟩ : syracuseStep 1813045 = 169973) (by norm_num)
theorem B2976317 : Blo 1321479 2976317 := bbase (se 3 (by rfl) ⟨558059, by rfl⟩ : syracuseStep 2976317 = 1116119) (by norm_num)
theorem B5360197 : Blo 1321479 5360197 := bbase (se 4 (by rfl) ⟨502518, by rfl⟩ : syracuseStep 5360197 = 1005037) (by norm_num)
theorem B1985093 : Blo 1321479 1985093 := bbase (se 4 (by rfl) ⟨186102, by rfl⟩ : syracuseStep 1985093 = 372205) (by norm_num)
theorem B2230861 : Blo 1321479 2230861 := bbase (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) (by norm_num)
theorem B1985117 : Blo 1321479 1985117 := bbase (se 3 (by rfl) ⟨372209, by rfl⟩ : syracuseStep 1985117 = 744419) (by norm_num)
theorem B1985141 : Blo 1321479 1985141 := bbase (se 5 (by rfl) ⟨93053, by rfl⟩ : syracuseStep 1985141 = 186107) (by norm_num)
theorem B1411705 : Blo 1321479 1411705 := bbase (se 2 (by rfl) ⟨529389, by rfl⟩ : syracuseStep 1411705 = 1058779) (by norm_num)
theorem B2976389 : Blo 1321479 2976389 := bbase (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) (by norm_num)
theorem B5024389 : Blo 1321479 5024389 := bbase (se 4 (by rfl) ⟨471036, by rfl⟩ : syracuseStep 5024389 = 942073) (by norm_num)
theorem B1985165 : Blo 1321479 1985165 := bbase (se 3 (by rfl) ⟨372218, by rfl⟩ : syracuseStep 1985165 = 744437) (by norm_num)
theorem B1673885 : Blo 1321479 1673885 := bbase (se 3 (by rfl) ⟨313853, by rfl⟩ : syracuseStep 1673885 = 627707) (by norm_num)
theorem B2230949 : Blo 1321479 2230949 := bbase (se 4 (by rfl) ⟨209151, by rfl⟩ : syracuseStep 2230949 = 418303) (by norm_num)
theorem B1985189 : Blo 1321479 1985189 := bbase (se 4 (by rfl) ⟨186111, by rfl⟩ : syracuseStep 1985189 = 372223) (by norm_num)
theorem B3345077 : Blo 1321479 3345077 := bbase (se 5 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 3345077 = 313601) (by norm_num)
theorem B1985213 : Blo 1321479 1985213 := bbase (se 3 (by rfl) ⟨372227, by rfl⟩ : syracuseStep 1985213 = 744455) (by norm_num)
theorem B1411777 : Blo 1321479 1411777 := bbase (se 2 (by rfl) ⟨529416, by rfl⟩ : syracuseStep 1411777 = 1058833) (by norm_num)
theorem B6695621 : Blo 1321479 6695621 := bbase (se 4 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 6695621 = 1255429) (by norm_num)
theorem B2976461 : Blo 1321479 2976461 := bbase (se 3 (by rfl) ⟨558086, by rfl⟩ : syracuseStep 2976461 = 1116173) (by norm_num)
theorem B1673941 : Blo 1321479 1673941 := bbase (se 7 (by rfl) ⟨19616, by rfl⟩ : syracuseStep 1673941 = 39233) (by norm_num)
theorem B2976533 : Blo 1321479 2976533 := bbase (se 6 (by rfl) ⟨69762, by rfl⟩ : syracuseStep 2976533 = 139525) (by norm_num)
theorem B2231077 : Blo 1321479 2231077 := bbase (se 4 (by rfl) ⟨209163, by rfl⟩ : syracuseStep 2231077 = 418327) (by norm_num)
theorem B2509613 : Blo 1321479 2509613 := bbase (se 3 (by rfl) ⟨470552, by rfl⟩ : syracuseStep 2509613 = 941105) (by norm_num)
theorem B1674037 : Blo 1321479 1674037 := bbase (se 5 (by rfl) ⟨78470, by rfl⟩ : syracuseStep 1674037 = 156941) (by norm_num)
theorem B4524869 : Blo 1321479 4524869 := bbase (se 4 (by rfl) ⟨424206, by rfl⟩ : syracuseStep 4524869 = 848413) (by norm_num)
theorem B2976605 : Blo 1321479 2976605 := bbase (se 3 (by rfl) ⟨558113, by rfl⟩ : syracuseStep 2976605 = 1116227) (by norm_num)
theorem B2231165 : Blo 1321479 2231165 := bbase (se 3 (by rfl) ⟨418343, by rfl⟩ : syracuseStep 2231165 = 836687) (by norm_num)
theorem B2976677 : Blo 1321479 2976677 := bbase (se 4 (by rfl) ⟨279063, by rfl⟩ : syracuseStep 2976677 = 558127) (by norm_num)
theorem B5024693 : Blo 1321479 5024693 := bbase (se 5 (by rfl) ⟨235532, by rfl⟩ : syracuseStep 5024693 = 471065) (by norm_num)
theorem B1674209 : Blo 1321479 1674209 := bbase (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) (by norm_num)
theorem B6032357 : Blo 1321479 6032357 := bbase (se 4 (by rfl) ⟨565533, by rfl⟩ : syracuseStep 6032357 = 1131067) (by norm_num)
theorem B2976749 : Blo 1321479 2976749 := bbase (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) (by norm_num)
theorem B3763189 : Blo 1321479 3763189 := bbase (se 5 (by rfl) ⟨176399, by rfl⟩ : syracuseStep 3763189 = 352799) (by norm_num)
theorem B2231293 : Blo 1321479 2231293 := bbase (se 3 (by rfl) ⟨418367, by rfl⟩ : syracuseStep 2231293 = 836735) (by norm_num)
theorem B3345421 : Blo 1321479 3345421 := bbase (se 3 (by rfl) ⟨627266, by rfl⟩ : syracuseStep 3345421 = 1254533) (by norm_num)
theorem B1674265 : Blo 1321479 1674265 := bbase (se 2 (by rfl) ⟨627849, by rfl⟩ : syracuseStep 1674265 = 1255699) (by norm_num)
theorem B1412149 : Blo 1321479 1412149 := bbase (se 5 (by rfl) ⟨66194, by rfl⟩ : syracuseStep 1412149 = 132389) (by norm_num)
theorem B2976821 : Blo 1321479 2976821 := bbase (se 5 (by rfl) ⟨139538, by rfl⟩ : syracuseStep 2976821 = 279077) (by norm_num)
theorem B2231381 : Blo 1321479 2231381 := bbase (se 8 (by rfl) ⟨13074, by rfl⟩ : syracuseStep 2231381 = 26149) (by norm_num)
theorem B1674361 : Blo 1321479 1674361 := bbase (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) (by norm_num)
theorem B3345533 : Blo 1321479 3345533 := bbase (se 3 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 3345533 = 1254575) (by norm_num)
theorem B2976893 : Blo 1321479 2976893 := bbase (se 3 (by rfl) ⟨558167, by rfl⟩ : syracuseStep 2976893 = 1116335) (by norm_num)
theorem B2010269 : Blo 1321479 2010269 := bbase (se 3 (by rfl) ⟨376925, by rfl⟩ : syracuseStep 2010269 = 753851) (by norm_num)
theorem B2976965 : Blo 1321479 2976965 := bbase (se 4 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 2976965 = 558181) (by norm_num)
theorem B2231509 : Blo 1321479 2231509 := bbase (se 7 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 2231509 = 52301) (by norm_num)
theorem B2010349 : Blo 1321479 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B2977037 : Blo 1321479 2977037 := bbase (se 3 (by rfl) ⟨558194, by rfl⟩ : syracuseStep 2977037 = 1116389) (by norm_num)
theorem B1396001 : Blo 1321479 1396001 := bbase (se 2 (by rfl) ⟨523500, by rfl⟩ : syracuseStep 1396001 = 1047001) (by norm_num)
theorem B1674533 : Blo 1321479 1674533 := bbase (se 4 (by rfl) ⟨156987, by rfl⟩ : syracuseStep 1674533 = 313975) (by norm_num)
theorem B2231597 : Blo 1321479 2231597 := bbase (se 3 (by rfl) ⟨418424, by rfl⟩ : syracuseStep 2231597 = 836849) (by norm_num)
theorem B3345725 : Blo 1321479 3345725 := bbase (se 3 (by rfl) ⟨627323, by rfl⟩ : syracuseStep 3345725 = 1254647) (by norm_num)
theorem B4828501 : Blo 1321479 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B2977109 : Blo 1321479 2977109 := bbase (se 11 (by rfl) ⟨2180, by rfl⟩ : syracuseStep 2977109 = 4361) (by norm_num)
theorem B1674589 : Blo 1321479 1674589 := bbase (se 3 (by rfl) ⟨313985, by rfl⟩ : syracuseStep 1674589 = 627971) (by norm_num)
theorem B2977181 : Blo 1321479 2977181 := bbase (se 3 (by rfl) ⟨558221, by rfl⟩ : syracuseStep 2977181 = 1116443) (by norm_num)
theorem B2231725 : Blo 1321479 2231725 := bbase (se 3 (by rfl) ⟨418448, by rfl⟩ : syracuseStep 2231725 = 836897) (by norm_num)
theorem B1412525 : Blo 1321479 1412525 := bbase (se 3 (by rfl) ⟨264848, by rfl⟩ : syracuseStep 1412525 = 529697) (by norm_num)
theorem B10177973 : Blo 1321479 10177973 := bbase (se 5 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 10177973 = 954185) (by norm_num)
theorem B1674685 : Blo 1321479 1674685 := bbase (se 3 (by rfl) ⟨314003, by rfl⟩ : syracuseStep 1674685 = 628007) (by norm_num)
theorem B2977253 : Blo 1321479 2977253 := bbase (se 4 (by rfl) ⟨279117, by rfl⟩ : syracuseStep 2977253 = 558235) (by norm_num)
theorem B4460021 : Blo 1321479 4460021 := bbase (se 5 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 4460021 = 418127) (by norm_num)
theorem B1412597 : Blo 1321479 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B2231813 : Blo 1321479 2231813 := bbase (se 4 (by rfl) ⟨209232, by rfl⟩ : syracuseStep 2231813 = 418465) (by norm_num)
theorem B2510365 : Blo 1321479 2510365 := bbase (se 3 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 2510365 = 941387) (by norm_num)
theorem B2977325 : Blo 1321479 2977325 := bbase (se 3 (by rfl) ⟨558248, by rfl⟩ : syracuseStep 2977325 = 1116497) (by norm_num)
theorem B1674857 : Blo 1321479 1674857 := bbase (se 2 (by rfl) ⟨628071, by rfl⟩ : syracuseStep 1674857 = 1256143) (by norm_num)
theorem B2977397 : Blo 1321479 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B2231941 : Blo 1321479 2231941 := bbase (se 4 (by rfl) ⟨209244, by rfl⟩ : syracuseStep 2231941 = 418489) (by norm_num)
theorem B2117269 : Blo 1321479 2117269 := bbase (se 6 (by rfl) ⟨49623, by rfl⟩ : syracuseStep 2117269 = 99247) (by norm_num)
theorem B3346069 : Blo 1321479 3346069 := bbase (se 6 (by rfl) ⟨78423, by rfl⟩ : syracuseStep 3346069 = 156847) (by norm_num)
theorem B12070549 : Blo 1321479 12070549 := bbase (se 6 (by rfl) ⟨282903, by rfl⟩ : syracuseStep 12070549 = 565807) (by norm_num)
theorem B1609373 : Blo 1321479 1609373 := bbase (se 3 (by rfl) ⟨301757, by rfl⟩ : syracuseStep 1609373 = 603515) (by norm_num)
theorem B1674913 : Blo 1321479 1674913 := bbase (se 2 (by rfl) ⟨628092, by rfl⟩ : syracuseStep 1674913 = 1256185) (by norm_num)
theorem B2510509 : Blo 1321479 2510509 := bbase (se 3 (by rfl) ⟨470720, by rfl⟩ : syracuseStep 2510509 = 941441) (by norm_num)
theorem B1412785 : Blo 1321479 1412785 := bbase (se 2 (by rfl) ⟨529794, by rfl⟩ : syracuseStep 1412785 = 1059589) (by norm_num)
theorem B2543285 : Blo 1321479 2543285 := bbase (se 5 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 2543285 = 238433) (by norm_num)
theorem B2977469 : Blo 1321479 2977469 := bbase (se 3 (by rfl) ⟨558275, by rfl⟩ : syracuseStep 2977469 = 1116551) (by norm_num)
theorem B2117333 : Blo 1321479 2117333 := bbase (se 7 (by rfl) ⟨24812, by rfl⟩ : syracuseStep 2117333 = 49625) (by norm_num)
theorem B2232029 : Blo 1321479 2232029 := bbase (se 3 (by rfl) ⟨418505, by rfl⟩ : syracuseStep 2232029 = 837011) (by norm_num)
theorem B6352613 : Blo 1321479 6352613 := bbase (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) (by norm_num)
theorem B2010853 : Blo 1321479 2010853 := bbase (se 4 (by rfl) ⟨188517, by rfl⟩ : syracuseStep 2010853 = 377035) (by norm_num)
theorem B1675009 : Blo 1321479 1675009 := bbase (se 2 (by rfl) ⟨628128, by rfl⟩ : syracuseStep 1675009 = 1256257) (by norm_num)
theorem B3346181 : Blo 1321479 3346181 := bbase (se 4 (by rfl) ⟨313704, by rfl⟩ : syracuseStep 3346181 = 627409) (by norm_num)
theorem B2977541 : Blo 1321479 2977541 := bbase (se 4 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 2977541 = 558289) (by norm_num)
theorem B4239125 : Blo 1321479 4239125 := bbase (se 6 (by rfl) ⟨99354, by rfl⟩ : syracuseStep 4239125 = 198709) (by norm_num)
theorem B1486669 : Blo 1321479 1486669 := bbase (se 3 (by rfl) ⟨278750, by rfl⟩ : syracuseStep 1486669 = 557501) (by norm_num)
theorem B2510669 : Blo 1321479 2510669 := bbase (se 3 (by rfl) ⟨470750, by rfl⟩ : syracuseStep 2510669 = 941501) (by norm_num)
theorem B2977613 : Blo 1321479 2977613 := bbase (se 3 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 2977613 = 1116605) (by norm_num)
theorem B2232157 : Blo 1321479 2232157 := bbase (se 3 (by rfl) ⟨418529, by rfl⟩ : syracuseStep 2232157 = 837059) (by norm_num)
theorem B1412969 : Blo 1321479 1412969 := bbase (se 2 (by rfl) ⟨529863, by rfl⟩ : syracuseStep 1412969 = 1059727) (by norm_num)
theorem B1486705 : Blo 1321479 1486705 := bbase (se 2 (by rfl) ⟨557514, by rfl⟩ : syracuseStep 1486705 = 1115029) (by norm_num)
theorem B1486741 : Blo 1321479 1486741 := bbase (se 6 (by rfl) ⟨34845, by rfl⟩ : syracuseStep 1486741 = 69691) (by norm_num)
theorem B10719125 : Blo 1321479 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B2977685 : Blo 1321479 2977685 := bbase (se 6 (by rfl) ⟨69789, by rfl⟩ : syracuseStep 2977685 = 139579) (by norm_num)
theorem B4460453 : Blo 1321479 4460453 := bbase (se 4 (by rfl) ⟨418167, by rfl⟩ : syracuseStep 4460453 = 836335) (by norm_num)
theorem B2232245 : Blo 1321479 2232245 := bbase (se 5 (by rfl) ⟨104636, by rfl⟩ : syracuseStep 2232245 = 209273) (by norm_num)
theorem B1486777 : Blo 1321479 1486777 := bbase (se 2 (by rfl) ⟨557541, by rfl⟩ : syracuseStep 1486777 = 1115083) (by norm_num)
theorem B3346373 : Blo 1321479 3346373 := bbase (se 4 (by rfl) ⟨313722, by rfl⟩ : syracuseStep 3346373 = 627445) (by norm_num)
theorem B6696917 : Blo 1321479 6696917 := bbase (se 7 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 6696917 = 156959) (by norm_num)
theorem B10874837 : Blo 1321479 10874837 := bbase (se 7 (by rfl) ⟨127439, by rfl⟩ : syracuseStep 10874837 = 254879) (by norm_num)
theorem B4239317 : Blo 1321479 4239317 := bbase (se 7 (by rfl) ⟨49679, by rfl⟩ : syracuseStep 4239317 = 99359) (by norm_num)
theorem B1486813 : Blo 1321479 1486813 := bbase (se 3 (by rfl) ⟨278777, by rfl⟩ : syracuseStep 1486813 = 557555) (by norm_num)
theorem B2510813 : Blo 1321479 2510813 := bbase (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) (by norm_num)
theorem B2977757 : Blo 1321479 2977757 := bbase (se 3 (by rfl) ⟨558329, by rfl⟩ : syracuseStep 2977757 = 1116659) (by norm_num)
theorem B1486849 : Blo 1321479 1486849 := bbase (se 2 (by rfl) ⟨557568, by rfl⟩ : syracuseStep 1486849 = 1115137) (by norm_num)
theorem B1486885 : Blo 1321479 1486885 := bbase (se 4 (by rfl) ⟨139395, by rfl⟩ : syracuseStep 1486885 = 278791) (by norm_num)
theorem B2977829 : Blo 1321479 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B2232373 : Blo 1321479 2232373 := bbase (se 5 (by rfl) ⟨104642, by rfl⟩ : syracuseStep 2232373 = 209285) (by norm_num)
theorem B1486921 : Blo 1321479 1486921 := bbase (se 2 (by rfl) ⟨557595, by rfl⟩ : syracuseStep 1486921 = 1115191) (by norm_num)
theorem B1486957 : Blo 1321479 1486957 := bbase (se 3 (by rfl) ⟨278804, by rfl⟩ : syracuseStep 1486957 = 557609) (by norm_num)
theorem B1609841 : Blo 1321479 1609841 := bbase (se 2 (by rfl) ⟨603690, by rfl⟩ : syracuseStep 1609841 = 1207381) (by norm_num)
theorem B2232461 : Blo 1321479 2232461 := bbase (se 3 (by rfl) ⟨418586, by rfl⟩ : syracuseStep 2232461 = 837173) (by norm_num)
theorem B1486993 : Blo 1321479 1486993 := bbase (se 2 (by rfl) ⟨557622, by rfl⟩ : syracuseStep 1486993 = 1115245) (by norm_num)
theorem B1487029 : Blo 1321479 1487029 := bbase (se 5 (by rfl) ⟨69704, by rfl⟩ : syracuseStep 1487029 = 139409) (by norm_num)
theorem B1487065 : Blo 1321479 1487065 := bbase (se 2 (by rfl) ⟨557649, by rfl⟩ : syracuseStep 1487065 = 1115299) (by norm_num)
theorem B1487101 : Blo 1321479 1487101 := bbase (se 3 (by rfl) ⟨278831, by rfl⟩ : syracuseStep 1487101 = 557663) (by norm_num)
theorem B2511101 : Blo 1321479 2511101 := bbase (se 3 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 2511101 = 941663) (by norm_num)
theorem B2232589 : Blo 1321479 2232589 := bbase (se 3 (by rfl) ⟨418610, by rfl⟩ : syracuseStep 2232589 = 837221) (by norm_num)
theorem B3346717 : Blo 1321479 3346717 := bbase (se 3 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 3346717 = 1255019) (by norm_num)
theorem B1487137 : Blo 1321479 1487137 := bbase (se 2 (by rfl) ⟨557676, by rfl⟩ : syracuseStep 1487137 = 1115353) (by norm_num)
theorem B1487173 : Blo 1321479 1487173 := bbase (se 4 (by rfl) ⟨139422, by rfl⟩ : syracuseStep 1487173 = 278845) (by norm_num)
theorem B4460885 : Blo 1321479 4460885 := bbase (se 10 (by rfl) ⟨6534, by rfl⟩ : syracuseStep 4460885 = 13069) (by norm_num)
theorem B1339745 : Blo 1321479 1339745 := bbase (se 2 (by rfl) ⟨502404, by rfl⟩ : syracuseStep 1339745 = 1004809) (by norm_num)
theorem B2232677 : Blo 1321479 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B1487209 : Blo 1321479 1487209 := bbase (se 2 (by rfl) ⟨557703, by rfl⟩ : syracuseStep 1487209 = 1115407) (by norm_num)
theorem B1487245 : Blo 1321479 1487245 := bbase (se 3 (by rfl) ⟨278858, by rfl⟩ : syracuseStep 1487245 = 557717) (by norm_num)
theorem B3346829 : Blo 1321479 3346829 := bbase (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) (by norm_num)
theorem B2511253 : Blo 1321479 2511253 := bbase (se 6 (by rfl) ⟨58857, by rfl⟩ : syracuseStep 2511253 = 117715) (by norm_num)
theorem B1487281 : Blo 1321479 1487281 := bbase (se 2 (by rfl) ⟨557730, by rfl⟩ : syracuseStep 1487281 = 1115461) (by norm_num)
theorem B8049077 : Blo 1321479 8049077 := bbase (se 5 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 8049077 = 754601) (by norm_num)
theorem B3764693 : Blo 1321479 3764693 := bbase (se 7 (by rfl) ⟨44117, by rfl⟩ : syracuseStep 3764693 = 88235) (by norm_num)
theorem B1487317 : Blo 1321479 1487317 := bbase (se 7 (by rfl) ⟨17429, by rfl⟩ : syracuseStep 1487317 = 34859) (by norm_num)
theorem B2232805 : Blo 1321479 2232805 := bbase (se 4 (by rfl) ⟨209325, by rfl⟩ : syracuseStep 2232805 = 418651) (by norm_num)
theorem B5648885 : Blo 1321479 5648885 := bbase (se 5 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 5648885 = 529583) (by norm_num)
theorem B1487353 : Blo 1321479 1487353 := bbase (se 2 (by rfl) ⟨557757, by rfl⟩ : syracuseStep 1487353 = 1115515) (by norm_num)
theorem B14291477 : Blo 1321479 14291477 := bbase (se 6 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 14291477 = 669913) (by norm_num)
theorem B1487389 : Blo 1321479 1487389 := bbase (se 3 (by rfl) ⟨278885, by rfl⟩ : syracuseStep 1487389 = 557771) (by norm_num)
theorem B2232893 : Blo 1321479 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B1487425 : Blo 1321479 1487425 := bbase (se 2 (by rfl) ⟨557784, by rfl⟩ : syracuseStep 1487425 = 1115569) (by norm_num)
theorem B3347021 : Blo 1321479 3347021 := bbase (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) (by norm_num)
theorem B1487461 : Blo 1321479 1487461 := bbase (se 4 (by rfl) ⟨139449, by rfl⟩ : syracuseStep 1487461 = 278899) (by norm_num)
theorem B5722757 : Blo 1321479 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B1487497 : Blo 1321479 1487497 := bbase (se 2 (by rfl) ⟨557811, by rfl⟩ : syracuseStep 1487497 = 1115623) (by norm_num)
theorem B1340053 : Blo 1321479 1340053 := bbase (se 6 (by rfl) ⟨31407, by rfl⟩ : syracuseStep 1340053 = 62815) (by norm_num)
theorem B1487533 : Blo 1321479 1487533 := bbase (se 3 (by rfl) ⟨278912, by rfl⟩ : syracuseStep 1487533 = 557825) (by norm_num)
theorem B2233021 : Blo 1321479 2233021 := bbase (se 3 (by rfl) ⟨418691, by rfl⟩ : syracuseStep 2233021 = 837383) (by norm_num)
theorem B2511557 : Blo 1321479 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B1487569 : Blo 1321479 1487569 := bbase (se 2 (by rfl) ⟨557838, by rfl⟩ : syracuseStep 1487569 = 1115677) (by norm_num)
theorem B13578965 : Blo 1321479 13578965 := bbase (se 7 (by rfl) ⟨159128, by rfl⟩ : syracuseStep 13578965 = 318257) (by norm_num)
theorem B1487605 : Blo 1321479 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B4461317 : Blo 1321479 4461317 := bbase (se 4 (by rfl) ⟨418248, by rfl⟩ : syracuseStep 4461317 = 836497) (by norm_num)
theorem B2233109 : Blo 1321479 2233109 := bbase (se 6 (by rfl) ⟨52338, by rfl⟩ : syracuseStep 2233109 = 104677) (by norm_num)
theorem B1487641 : Blo 1321479 1487641 := bbase (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) (by norm_num)
theorem B1487677 : Blo 1321479 1487677 := bbase (se 3 (by rfl) ⟨278939, by rfl⟩ : syracuseStep 1487677 = 557879) (by norm_num)
theorem B1487713 : Blo 1321479 1487713 := bbase (se 2 (by rfl) ⟨557892, by rfl⟩ : syracuseStep 1487713 = 1115785) (by norm_num)
theorem B1487749 : Blo 1321479 1487749 := bbase (se 4 (by rfl) ⟨139476, by rfl⟩ : syracuseStep 1487749 = 278953) (by norm_num)
theorem B2233237 : Blo 1321479 2233237 := bbase (se 6 (by rfl) ⟨52341, by rfl⟩ : syracuseStep 2233237 = 104683) (by norm_num)
theorem B3347365 : Blo 1321479 3347365 := bbase (se 4 (by rfl) ⟨313815, by rfl⟩ : syracuseStep 3347365 = 627631) (by norm_num)
theorem B1487785 : Blo 1321479 1487785 := bbase (se 2 (by rfl) ⟨557919, by rfl⟩ : syracuseStep 1487785 = 1115839) (by norm_num)
theorem B1340345 : Blo 1321479 1340345 := bbase (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) (by norm_num)
theorem B1487821 : Blo 1321479 1487821 := bbase (se 3 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 1487821 = 557933) (by norm_num)
theorem B2233325 : Blo 1321479 2233325 := bbase (se 3 (by rfl) ⟨418748, by rfl⟩ : syracuseStep 2233325 = 837497) (by norm_num)
theorem B1487857 : Blo 1321479 1487857 := bbase (se 2 (by rfl) ⟨557946, by rfl⟩ : syracuseStep 1487857 = 1115893) (by norm_num)
theorem B2118653 : Blo 1321479 2118653 := bbase (se 3 (by rfl) ⟨397247, by rfl⟩ : syracuseStep 2118653 = 794495) (by norm_num)
theorem B3347477 : Blo 1321479 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B1487893 : Blo 1321479 1487893 := bbase (se 6 (by rfl) ⟨34872, by rfl⟩ : syracuseStep 1487893 = 69745) (by norm_num)
theorem B1487929 : Blo 1321479 1487929 := bbase (se 2 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 1487929 = 1115947) (by norm_num)
theorem B1487965 : Blo 1321479 1487965 := bbase (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) (by norm_num)
theorem B1430641 : Blo 1321479 1430641 := bbase (se 2 (by rfl) ⟨536490, by rfl⟩ : syracuseStep 1430641 = 1072981) (by norm_num)
theorem B1488001 : Blo 1321479 1488001 := bbase (se 2 (by rfl) ⟨558000, by rfl⟩ : syracuseStep 1488001 = 1116001) (by norm_num)
theorem B1488037 : Blo 1321479 1488037 := bbase (se 4 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 1488037 = 279007) (by norm_num)
theorem B2823349 : Blo 1321479 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B4461749 : Blo 1321479 4461749 := bbase (se 5 (by rfl) ⟨209144, by rfl⟩ : syracuseStep 4461749 = 418289) (by norm_num)
theorem B2118845 : Blo 1321479 2118845 := bbase (se 3 (by rfl) ⟨397283, by rfl⟩ : syracuseStep 2118845 = 794567) (by norm_num)
theorem B1488073 : Blo 1321479 1488073 := bbase (se 2 (by rfl) ⟨558027, by rfl⟩ : syracuseStep 1488073 = 1116055) (by norm_num)
theorem B3347669 : Blo 1321479 3347669 := bbase (se 7 (by rfl) ⟨39230, by rfl⟩ : syracuseStep 3347669 = 78461) (by norm_num)
theorem B6698213 : Blo 1321479 6698213 := bbase (se 4 (by rfl) ⟨627957, by rfl⟩ : syracuseStep 6698213 = 1255915) (by norm_num)
theorem B1488109 : Blo 1321479 1488109 := bbase (se 3 (by rfl) ⟨279020, by rfl⟩ : syracuseStep 1488109 = 558041) (by norm_num)
theorem B1488145 : Blo 1321479 1488145 := bbase (se 2 (by rfl) ⟨558054, by rfl⟩ : syracuseStep 1488145 = 1116109) (by norm_num)
theorem B1471777 : Blo 1321479 1471777 := bbase (se 2 (by rfl) ⟨551916, by rfl⟩ : syracuseStep 1471777 = 1103833) (by norm_num)
theorem B3814709 : Blo 1321479 3814709 := bbase (se 5 (by rfl) ⟨178814, by rfl⟩ : syracuseStep 3814709 = 357629) (by norm_num)
theorem B1488181 : Blo 1321479 1488181 := bbase (se 5 (by rfl) ⟨69758, by rfl⟩ : syracuseStep 1488181 = 139517) (by norm_num)
theorem B2118973 : Blo 1321479 2118973 := bbase (se 3 (by rfl) ⟨397307, by rfl⟩ : syracuseStep 2118973 = 794615) (by norm_num)
theorem B1488217 : Blo 1321479 1488217 := bbase (se 2 (by rfl) ⟨558081, by rfl⟩ : syracuseStep 1488217 = 1116163) (by norm_num)
theorem B2094445 : Blo 1321479 2094445 := bbase (se 3 (by rfl) ⟨392708, by rfl⟩ : syracuseStep 2094445 = 785417) (by norm_num)
theorem B1488253 : Blo 1321479 1488253 := bbase (se 3 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 1488253 = 558095) (by norm_num)
theorem B5019029 : Blo 1321479 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B5092757 : Blo 1321479 5092757 := bbase (se 6 (by rfl) ⟨119361, by rfl⟩ : syracuseStep 5092757 = 238723) (by norm_num)
theorem B1488289 : Blo 1321479 1488289 := bbase (se 2 (by rfl) ⟨558108, by rfl⟩ : syracuseStep 1488289 = 1116217) (by norm_num)
theorem B3487141 : Blo 1321479 3487141 := bbase (se 4 (by rfl) ⟨326919, by rfl⟩ : syracuseStep 3487141 = 653839) (by norm_num)
theorem B2512309 : Blo 1321479 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B1488325 : Blo 1321479 1488325 := bbase (se 4 (by rfl) ⟨139530, by rfl⟩ : syracuseStep 1488325 = 279061) (by norm_num)
theorem B12703189 : Blo 1321479 12703189 := bbase (se 7 (by rfl) ⟨148865, by rfl⟩ : syracuseStep 12703189 = 297731) (by norm_num)
theorem B1340893 : Blo 1321479 1340893 := bbase (se 3 (by rfl) ⟨251417, by rfl⟩ : syracuseStep 1340893 = 502835) (by norm_num)
theorem B1488361 : Blo 1321479 1488361 := bbase (se 2 (by rfl) ⟨558135, by rfl⟩ : syracuseStep 1488361 = 1116271) (by norm_num)
theorem B1488397 : Blo 1321479 1488397 := bbase (se 3 (by rfl) ⟨279074, by rfl⟩ : syracuseStep 1488397 = 558149) (by norm_num)
theorem B3348013 : Blo 1321479 3348013 := bbase (se 3 (by rfl) ⟨627752, by rfl⟩ : syracuseStep 3348013 = 1255505) (by norm_num)
theorem B1488433 : Blo 1321479 1488433 := bbase (se 2 (by rfl) ⟨558162, by rfl⟩ : syracuseStep 1488433 = 1116325) (by norm_num)
theorem B2512453 : Blo 1321479 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B4019797 : Blo 1321479 4019797 := bbase (se 8 (by rfl) ⟨23553, by rfl⟩ : syracuseStep 4019797 = 47107) (by norm_num)
theorem B1488469 : Blo 1321479 1488469 := bbase (se 8 (by rfl) ⟨8721, by rfl⟩ : syracuseStep 1488469 = 17443) (by norm_num)
theorem B4462181 : Blo 1321479 4462181 := bbase (se 4 (by rfl) ⟨418329, by rfl⟩ : syracuseStep 4462181 = 836659) (by norm_num)
theorem B1488505 : Blo 1321479 1488505 := bbase (se 2 (by rfl) ⟨558189, by rfl⟩ : syracuseStep 1488505 = 1116379) (by norm_num)
theorem B6690437 : Blo 1321479 6690437 := bbase (se 4 (by rfl) ⟨627228, by rfl⟩ : syracuseStep 6690437 = 1254457) (by norm_num)
theorem B19060373 : Blo 1321479 19060373 := bbase (se 6 (by rfl) ⟨446727, by rfl⟩ : syracuseStep 19060373 = 893455) (by norm_num)
theorem B3348125 : Blo 1321479 3348125 := bbase (se 3 (by rfl) ⟨627773, by rfl⟩ : syracuseStep 3348125 = 1255547) (by norm_num)
theorem B1488541 : Blo 1321479 1488541 := bbase (se 3 (by rfl) ⟨279101, by rfl⟩ : syracuseStep 1488541 = 558203) (by norm_num)
theorem B5019317 : Blo 1321479 5019317 := bbase (se 5 (by rfl) ⟨235280, by rfl⟩ : syracuseStep 5019317 = 470561) (by norm_num)
theorem B1488577 : Blo 1321479 1488577 := bbase (se 2 (by rfl) ⟨558216, by rfl⟩ : syracuseStep 1488577 = 1116433) (by norm_num)
theorem B1488613 : Blo 1321479 1488613 := bbase (se 4 (by rfl) ⟨139557, by rfl⟩ : syracuseStep 1488613 = 279115) (by norm_num)
theorem B1488649 : Blo 1321479 1488649 := bbase (se 2 (by rfl) ⟨558243, by rfl⟩ : syracuseStep 1488649 = 1116487) (by norm_num)
theorem B1488685 : Blo 1321479 1488685 := bbase (se 3 (by rfl) ⟨279128, by rfl⟩ : syracuseStep 1488685 = 558257) (by norm_num)
theorem B1488721 : Blo 1321479 1488721 := bbase (se 2 (by rfl) ⟨558270, by rfl⟩ : syracuseStep 1488721 = 1116541) (by norm_num)
theorem B3348317 : Blo 1321479 3348317 := bbase (se 3 (by rfl) ⟨627809, by rfl⟩ : syracuseStep 3348317 = 1255619) (by norm_num)
theorem B1488757 : Blo 1321479 1488757 := bbase (se 5 (by rfl) ⟨69785, by rfl⟩ : syracuseStep 1488757 = 139571) (by norm_num)
theorem B1488793 : Blo 1321479 1488793 := bbase (se 2 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 1488793 = 1116595) (by norm_num)
theorem B1882045 : Blo 1321479 1882045 := bbase (se 3 (by rfl) ⟨352883, by rfl⟩ : syracuseStep 1882045 = 705767) (by norm_num)
theorem B2119613 : Blo 1321479 2119613 := bbase (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) (by norm_num)
theorem B1488829 : Blo 1321479 1488829 := bbase (se 3 (by rfl) ⟨279155, by rfl⟩ : syracuseStep 1488829 = 558311) (by norm_num)
theorem B7526357 : Blo 1321479 7526357 := bbase (se 7 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 7526357 = 176399) (by norm_num)
theorem B9050069 : Blo 1321479 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B1488865 : Blo 1321479 1488865 := bbase (se 2 (by rfl) ⟨558324, by rfl⟩ : syracuseStep 1488865 = 1116649) (by norm_num)
theorem B2381797 : Blo 1321479 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B3766277 : Blo 1321479 3766277 := bbase (se 4 (by rfl) ⟨353088, by rfl⟩ : syracuseStep 3766277 = 706177) (by norm_num)
theorem B1488901 : Blo 1321479 1488901 := bbase (se 4 (by rfl) ⟨139584, by rfl⟩ : syracuseStep 1488901 = 279169) (by norm_num)
theorem B4462613 : Blo 1321479 4462613 := bbase (se 6 (by rfl) ⟨104592, by rfl⟩ : syracuseStep 4462613 = 209185) (by norm_num)
theorem B2824237 : Blo 1321479 2824237 := bbase (se 3 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 2824237 = 1059089) (by norm_num)
theorem B2414645 : Blo 1321479 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B2037845 : Blo 1321479 2037845 := bbase (se 8 (by rfl) ⟨11940, by rfl⟩ : syracuseStep 2037845 = 23881) (by norm_num)
theorem B3348661 : Blo 1321479 3348661 := bbase (se 5 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 3348661 = 313937) (by norm_num)
theorem B5650661 : Blo 1321479 5650661 := bbase (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) (by norm_num)
theorem B1882381 : Blo 1321479 1882381 := bbase (se 3 (by rfl) ⟨352946, by rfl⟩ : syracuseStep 1882381 = 705893) (by norm_num)
theorem B3348773 : Blo 1321479 3348773 := bbase (se 4 (by rfl) ⟨313947, by rfl⟩ : syracuseStep 3348773 = 627895) (by norm_num)
theorem B3176749 : Blo 1321479 3176749 := bbase (se 3 (by rfl) ⟨595640, by rfl⟩ : syracuseStep 3176749 = 1191281) (by norm_num)
theorem B6355381 : Blo 1321479 6355381 := bbase (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) (by norm_num)
theorem B4463045 : Blo 1321479 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B1432009 : Blo 1321479 1432009 := bbase (se 2 (by rfl) ⟨537003, by rfl⟩ : syracuseStep 1432009 = 1074007) (by norm_num)
theorem B1882597 : Blo 1321479 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B3348965 : Blo 1321479 3348965 := bbase (se 4 (by rfl) ⟨313965, by rfl⟩ : syracuseStep 3348965 = 627931) (by norm_num)
theorem B6699509 : Blo 1321479 6699509 := bbase (se 5 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 6699509 = 628079) (by norm_num)
theorem B2824733 : Blo 1321479 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B1587745 : Blo 1321479 1587745 := bbase (se 2 (by rfl) ⟨595404, by rfl⟩ : syracuseStep 1587745 = 1190809) (by norm_num)
theorem B11303509 : Blo 1321479 11303509 := bbase (se 8 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 11303509 = 132463) (by norm_num)
theorem B4233845 : Blo 1321479 4233845 := bbase (se 5 (by rfl) ⟨198461, by rfl⟩ : syracuseStep 4233845 = 396923) (by norm_num)
theorem B2382461 : Blo 1321479 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B3766949 : Blo 1321479 3766949 := bbase (se 4 (by rfl) ⟨353151, by rfl⟩ : syracuseStep 3766949 = 706303) (by norm_num)
theorem B2382605 : Blo 1321479 2382605 := bbase (se 3 (by rfl) ⟨446738, by rfl⟩ : syracuseStep 2382605 = 893477) (by norm_num)
theorem B2448181 : Blo 1321479 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B3349309 : Blo 1321479 3349309 := bbase (se 3 (by rfl) ⟨627995, by rfl⟩ : syracuseStep 3349309 = 1255991) (by norm_num)
theorem B5020501 : Blo 1321479 5020501 := bbase (se 9 (by rfl) ⟨14708, by rfl⟩ : syracuseStep 5020501 = 29417) (by norm_num)
theorem B1882973 : Blo 1321479 1882973 := bbase (se 3 (by rfl) ⟨353057, by rfl⟩ : syracuseStep 1882973 = 706115) (by norm_num)
theorem B4463477 : Blo 1321479 4463477 := bbase (se 5 (by rfl) ⟨209225, by rfl⟩ : syracuseStep 4463477 = 418451) (by norm_num)
theorem B6691733 : Blo 1321479 6691733 := bbase (se 6 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 6691733 = 313675) (by norm_num)
theorem B3349421 : Blo 1321479 3349421 := bbase (se 3 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 3349421 = 1256033) (by norm_num)
theorem B3177461 : Blo 1321479 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B3767381 : Blo 1321479 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B3349613 : Blo 1321479 3349613 := bbase (se 3 (by rfl) ⟨628052, by rfl⟩ : syracuseStep 3349613 = 1256105) (by norm_num)
theorem B5020805 : Blo 1321479 5020805 := bbase (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) (by norm_num)
theorem B5364917 : Blo 1321479 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B5651653 : Blo 1321479 5651653 := bbase (se 4 (by rfl) ⟨529842, by rfl⟩ : syracuseStep 5651653 = 1059685) (by norm_num)
theorem B6790405 : Blo 1321479 6790405 := bbase (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) (by norm_num)
theorem B4463909 : Blo 1321479 4463909 := bbase (se 4 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 4463909 = 836983) (by norm_num)
theorem B9534773 : Blo 1321479 9534773 := bbase (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) (by norm_num)
theorem B3177845 : Blo 1321479 3177845 := bbase (se 5 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 3177845 = 297923) (by norm_num)
theorem B2825597 : Blo 1321479 2825597 := bbase (se 3 (by rfl) ⟨529799, by rfl⟩ : syracuseStep 2825597 = 1059599) (by norm_num)
theorem B3349957 : Blo 1321479 3349957 := bbase (se 4 (by rfl) ⟨314058, by rfl⟩ : syracuseStep 3349957 = 628117) (by norm_num)
theorem B2825741 : Blo 1321479 2825741 := bbase (se 3 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 2825741 = 1059653) (by norm_num)
theorem B1359385 : Blo 1321479 1359385 := bbase (se 2 (by rfl) ⟨509769, by rfl⟩ : syracuseStep 1359385 = 1019539) (by norm_num)
theorem B14294677 : Blo 1321479 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B3178133 : Blo 1321479 3178133 := bbase (se 6 (by rfl) ⟨74487, by rfl⟩ : syracuseStep 3178133 = 148975) (by norm_num)
theorem B1719973 : Blo 1321479 1719973 := bbase (se 4 (by rfl) ⟨161247, by rfl⟩ : syracuseStep 1719973 = 322495) (by norm_num)
theorem B2973365 : Blo 1321479 2973365 := bbase (se 5 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 2973365 = 278753) (by norm_num)
theorem B4464341 : Blo 1321479 4464341 := bbase (se 7 (by rfl) ⟨52316, by rfl⟩ : syracuseStep 4464341 = 104633) (by norm_num)
theorem B2973437 : Blo 1321479 2973437 := bbase (se 3 (by rfl) ⟨557519, by rfl⟩ : syracuseStep 2973437 = 1115039) (by norm_num)
theorem B1982237 : Blo 1321479 1982237 := bbase (se 3 (by rfl) ⟨371669, by rfl⟩ : syracuseStep 1982237 = 743339) (by norm_num)
theorem B1982261 : Blo 1321479 1982261 := bbase (se 5 (by rfl) ⟨92918, by rfl⟩ : syracuseStep 1982261 = 185837) (by norm_num)
theorem B10043189 : Blo 1321479 10043189 := bbase (se 5 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 10043189 = 941549) (by norm_num)
theorem B1695553 : Blo 1321479 1695553 := bbase (se 2 (by rfl) ⟨635832, by rfl⟩ : syracuseStep 1695553 = 1271665) (by norm_num)
theorem B2973509 : Blo 1321479 2973509 := bbase (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) (by norm_num)
theorem B3768133 : Blo 1321479 3768133 := bbase (se 4 (by rfl) ⟨353262, by rfl⟩ : syracuseStep 3768133 = 706525) (by norm_num)
theorem B1982285 : Blo 1321479 1982285 := bbase (se 3 (by rfl) ⟨371678, by rfl⟩ : syracuseStep 1982285 = 743357) (by norm_num)
theorem B1982309 : Blo 1321479 1982309 := bbase (se 4 (by rfl) ⟨185841, by rfl⟩ : syracuseStep 1982309 = 371683) (by norm_num)
theorem B1982333 : Blo 1321479 1982333 := bbase (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) (by norm_num)
theorem B2973581 : Blo 1321479 2973581 := bbase (se 3 (by rfl) ⟨557546, by rfl⟩ : syracuseStep 2973581 = 1115093) (by norm_num)
theorem B1982357 : Blo 1321479 1982357 := bbase (se 6 (by rfl) ⟨46461, by rfl⟩ : syracuseStep 1982357 = 92923) (by norm_num)
theorem B1982381 : Blo 1321479 1982381 := bbase (se 3 (by rfl) ⟨371696, by rfl⟩ : syracuseStep 1982381 = 743393) (by norm_num)
theorem B1982405 : Blo 1321479 1982405 := bbase (se 4 (by rfl) ⟨185850, by rfl⟩ : syracuseStep 1982405 = 371701) (by norm_num)
theorem B2973653 : Blo 1321479 2973653 := bbase (se 7 (by rfl) ⟨34847, by rfl⟩ : syracuseStep 2973653 = 69695) (by norm_num)
theorem B1982429 : Blo 1321479 1982429 := bbase (se 3 (by rfl) ⟨371705, by rfl⟩ : syracuseStep 1982429 = 743411) (by norm_num)
theorem B1982453 : Blo 1321479 1982453 := bbase (se 5 (by rfl) ⟨92927, by rfl⟩ : syracuseStep 1982453 = 185855) (by norm_num)
theorem B1982465 : Blo 1321479 1982465 := bstep (se 2 (by rfl) ⟨743424, by rfl⟩ : syracuseStep 1982465 = 1486849) B1486849
theorem B1982483 : Blo 1321479 1982483 := bstep (se 1 (by rfl) ⟨1486862, by rfl⟩ : syracuseStep 1982483 = 2973725) B2973725
theorem B1982513 : Blo 1321479 1982513 := bstep (se 2 (by rfl) ⟨743442, by rfl⟩ : syracuseStep 1982513 = 1486885) B1486885
theorem B1982531 : Blo 1321479 1982531 := bstep (se 1 (by rfl) ⟨1486898, by rfl⟩ : syracuseStep 1982531 = 2973797) B2973797
theorem B1982561 : Blo 1321479 1982561 := bstep (se 2 (by rfl) ⟨743460, by rfl⟩ : syracuseStep 1982561 = 1486921) B1486921
theorem B3178595 : Blo 1321479 3178595 := bstep (se 1 (by rfl) ⟨2383946, by rfl⟩ : syracuseStep 3178595 = 4767893) B4767893
theorem B1982579 : Blo 1321479 1982579 := bstep (se 1 (by rfl) ⟨1486934, by rfl⟩ : syracuseStep 1982579 = 2973869) B2973869
theorem B1982609 : Blo 1321479 1982609 := bstep (se 2 (by rfl) ⟨743478, by rfl⟩ : syracuseStep 1982609 = 1486957) B1486957
theorem B1982627 : Blo 1321479 1982627 := bstep (se 1 (by rfl) ⟨1486970, by rfl⟩ : syracuseStep 1982627 = 2973941) B2973941
theorem B1884323 : Blo 1321479 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B1982657 : Blo 1321479 1982657 := bstep (se 2 (by rfl) ⟨743496, by rfl⟩ : syracuseStep 1982657 = 1486993) B1486993
theorem B8478917 : Blo 1321479 8478917 := bstep (se 4 (by rfl) ⟨794898, by rfl⟩ : syracuseStep 8478917 = 1589797) B1589797
theorem B2973905 : Blo 1321479 2973905 := bstep (se 2 (by rfl) ⟨1115214, by rfl⟩ : syracuseStep 2973905 = 2230429) B2230429
theorem B1982675 : Blo 1321479 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B2973923 : Blo 1321479 2973923 := bstep (se 1 (by rfl) ⟨2230442, by rfl⟩ : syracuseStep 2973923 = 4460885) B4460885
theorem B1982705 : Blo 1321479 1982705 := bstep (se 2 (by rfl) ⟨743514, by rfl⟩ : syracuseStep 1982705 = 1487029) B1487029
theorem B4464881 : Blo 1321479 4464881 := bstep (se 2 (by rfl) ⟨1674330, by rfl⟩ : syracuseStep 4464881 = 3348661) B3348661
theorem B1982723 : Blo 1321479 1982723 := bstep (se 1 (by rfl) ⟨1487042, by rfl⟩ : syracuseStep 1982723 = 2974085) B2974085
theorem B1982753 : Blo 1321479 1982753 := bstep (se 2 (by rfl) ⟨743532, by rfl⟩ : syracuseStep 1982753 = 1487065) B1487065
theorem B5366051 : Blo 1321479 5366051 := bstep (se 1 (by rfl) ⟨4024538, by rfl⟩ : syracuseStep 5366051 = 8049077) B8049077
theorem B4292909 : Blo 1321479 4292909 := bstep (se 3 (by rfl) ⟨804920, by rfl⟩ : syracuseStep 4292909 = 1609841) B1609841
theorem B1982771 : Blo 1321479 1982771 := bstep (se 1 (by rfl) ⟨1487078, by rfl⟩ : syracuseStep 1982771 = 2974157) B2974157
theorem B1982801 : Blo 1321479 1982801 := bstep (se 2 (by rfl) ⟨743550, by rfl⟩ : syracuseStep 1982801 = 1487101) B1487101
theorem B9527651 : Blo 1321479 9527651 := bstep (se 1 (by rfl) ⟨7145738, by rfl⟩ : syracuseStep 9527651 = 14291477) B14291477
theorem B1982819 : Blo 1321479 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B7536995 : Blo 1321479 7536995 := bstep (se 1 (by rfl) ⟨5652746, by rfl⟩ : syracuseStep 7536995 = 11305493) B11305493
theorem B1982849 : Blo 1321479 1982849 := bstep (se 2 (by rfl) ⟨743568, by rfl⟩ : syracuseStep 1982849 = 1487137) B1487137
theorem B4235665 : Blo 1321479 4235665 := bstep (se 2 (by rfl) ⟨1588374, by rfl⟩ : syracuseStep 4235665 = 3176749) B3176749
theorem B1982867 : Blo 1321479 1982867 := bstep (se 1 (by rfl) ⟨1487150, by rfl⟩ : syracuseStep 1982867 = 2974301) B2974301
theorem B1982897 : Blo 1321479 1982897 := bstep (se 2 (by rfl) ⟨743586, by rfl⟩ : syracuseStep 1982897 = 1487173) B1487173
theorem B1982915 : Blo 1321479 1982915 := bstep (se 1 (by rfl) ⟨1487186, by rfl⟩ : syracuseStep 1982915 = 2974373) B2974373
theorem B1982945 : Blo 1321479 1982945 := bstep (se 2 (by rfl) ⟨743604, by rfl⟩ : syracuseStep 1982945 = 1487209) B1487209
theorem B9052643 : Blo 1321479 9052643 := bstep (se 1 (by rfl) ⟨6789482, by rfl⟩ : syracuseStep 9052643 = 13578965) B13578965
theorem B2974193 : Blo 1321479 2974193 := bstep (se 2 (by rfl) ⟨1115322, by rfl⟩ : syracuseStep 2974193 = 2230645) B2230645
theorem B1982963 : Blo 1321479 1982963 := bstep (se 1 (by rfl) ⟨1487222, by rfl⟩ : syracuseStep 1982963 = 2974445) B2974445
theorem B2974211 : Blo 1321479 2974211 := bstep (se 1 (by rfl) ⟨2230658, by rfl⟩ : syracuseStep 2974211 = 4461317) B4461317
theorem B1982993 : Blo 1321479 1982993 := bstep (se 2 (by rfl) ⟨743622, by rfl⟩ : syracuseStep 1982993 = 1487245) B1487245
theorem B29000213 : Blo 1321479 29000213 := bstep (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) B1359385
theorem B1983011 : Blo 1321479 1983011 := bstep (se 1 (by rfl) ⟨1487258, by rfl⟩ : syracuseStep 1983011 = 2974517) B2974517
theorem B1983041 : Blo 1321479 1983041 := bstep (se 2 (by rfl) ⟨743640, by rfl⟩ : syracuseStep 1983041 = 1487281) B1487281
theorem B1983059 : Blo 1321479 1983059 := bstep (se 1 (by rfl) ⟨1487294, by rfl⟩ : syracuseStep 1983059 = 2974589) B2974589
theorem B1983089 : Blo 1321479 1983089 := bstep (se 2 (by rfl) ⟨743658, by rfl⟩ : syracuseStep 1983089 = 1487317) B1487317
theorem B1983107 : Blo 1321479 1983107 := bstep (se 1 (by rfl) ⟨1487330, by rfl⟩ : syracuseStep 1983107 = 2974661) B2974661
theorem B1983137 : Blo 1321479 1983137 := bstep (se 2 (by rfl) ⟨743676, by rfl⟩ : syracuseStep 1983137 = 1487353) B1487353
theorem B1983155 : Blo 1321479 1983155 := bstep (se 1 (by rfl) ⟨1487366, by rfl⟩ : syracuseStep 1983155 = 2974733) B2974733
theorem B2261683 : Blo 1321479 2261683 := bstep (se 1 (by rfl) ⟨1696262, by rfl⟩ : syracuseStep 2261683 = 3392525) B3392525
theorem B1983185 : Blo 1321479 1983185 := bstep (se 2 (by rfl) ⟨743694, by rfl⟩ : syracuseStep 1983185 = 1487389) B1487389
theorem B1983203 : Blo 1321479 1983203 := bstep (se 1 (by rfl) ⟨1487402, by rfl⟩ : syracuseStep 1983203 = 2974805) B2974805
theorem B2417393 : Blo 1321479 2417393 := bstep (se 2 (by rfl) ⟨906522, by rfl⟩ : syracuseStep 2417393 = 1813045) B1813045
theorem B1983233 : Blo 1321479 1983233 := bstep (se 2 (by rfl) ⟨743712, by rfl⟩ : syracuseStep 1983233 = 1487425) B1487425
theorem B3179267 : Blo 1321479 3179267 := bstep (se 1 (by rfl) ⟨2384450, by rfl⟩ : syracuseStep 3179267 = 4768901) B4768901
theorem B4465421 : Blo 1321479 4465421 := bstep (se 3 (by rfl) ⟨837266, by rfl⟩ : syracuseStep 4465421 = 1674533) B1674533
theorem B2974481 : Blo 1321479 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B1983251 : Blo 1321479 1983251 := bstep (se 1 (by rfl) ⟨1487438, by rfl⟩ : syracuseStep 1983251 = 2974877) B2974877
theorem B2974499 : Blo 1321479 2974499 := bstep (se 1 (by rfl) ⟨2230874, by rfl⟩ : syracuseStep 2974499 = 4461749) B4461749
theorem B1983281 : Blo 1321479 1983281 := bstep (se 2 (by rfl) ⟨743730, by rfl⟩ : syracuseStep 1983281 = 1487461) B1487461
theorem B1983299 : Blo 1321479 1983299 := bstep (se 1 (by rfl) ⟨1487474, by rfl⟩ : syracuseStep 1983299 = 2974949) B2974949
theorem B4465475 : Blo 1321479 4465475 := bstep (se 1 (by rfl) ⟨3349106, by rfl⟩ : syracuseStep 4465475 = 6698213) B6698213
theorem B1983329 : Blo 1321479 1983329 := bstep (se 2 (by rfl) ⟨743748, by rfl⟩ : syracuseStep 1983329 = 1487497) B1487497
theorem B1983347 : Blo 1321479 1983347 := bstep (se 1 (by rfl) ⟨1487510, by rfl⟩ : syracuseStep 1983347 = 2975021) B2975021
theorem B1983377 : Blo 1321479 1983377 := bstep (se 2 (by rfl) ⟨743766, by rfl⟩ : syracuseStep 1983377 = 1487533) B1487533
theorem B1983395 : Blo 1321479 1983395 := bstep (se 1 (by rfl) ⟨1487546, by rfl⟩ : syracuseStep 1983395 = 2975093) B2975093
theorem B3572653 : Blo 1321479 3572653 := bstep (se 3 (by rfl) ⟨669872, by rfl⟩ : syracuseStep 3572653 = 1339745) B1339745
theorem B1983425 : Blo 1321479 1983425 := bstep (se 2 (by rfl) ⟨743784, by rfl⟩ : syracuseStep 1983425 = 1487569) B1487569
theorem B3818435 : Blo 1321479 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B1983443 : Blo 1321479 1983443 := bstep (se 1 (by rfl) ⟨1487582, by rfl⟩ : syracuseStep 1983443 = 2975165) B2975165
theorem B1983473 : Blo 1321479 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1983491 : Blo 1321479 1983491 := bstep (se 1 (by rfl) ⟨1487618, by rfl⟩ : syracuseStep 1983491 = 2975237) B2975237
theorem B3179537 : Blo 1321479 3179537 := bstep (se 2 (by rfl) ⟨1192326, by rfl⟩ : syracuseStep 3179537 = 2384653) B2384653
theorem B1983521 : Blo 1321479 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B2974769 : Blo 1321479 2974769 := bstep (se 2 (by rfl) ⟨1115538, by rfl⟩ : syracuseStep 2974769 = 2231077) B2231077
theorem B1983539 : Blo 1321479 1983539 := bstep (se 1 (by rfl) ⟨1487654, by rfl⟩ : syracuseStep 1983539 = 2975309) B2975309
theorem B17409077 : Blo 1321479 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B2974787 : Blo 1321479 2974787 := bstep (se 1 (by rfl) ⟨2231090, by rfl⟩ : syracuseStep 2974787 = 4462181) B4462181
theorem B1983569 : Blo 1321479 1983569 := bstep (se 2 (by rfl) ⟨743838, by rfl⟩ : syracuseStep 1983569 = 1487677) B1487677
theorem B4465745 : Blo 1321479 4465745 := bstep (se 2 (by rfl) ⟨1674654, by rfl⟩ : syracuseStep 4465745 = 3349309) B3349309
theorem B12706915 : Blo 1321479 12706915 := bstep (se 1 (by rfl) ⟨9530186, by rfl⟩ : syracuseStep 12706915 = 19060373) B19060373
theorem B1983587 : Blo 1321479 1983587 := bstep (se 1 (by rfl) ⟨1487690, by rfl⟩ : syracuseStep 1983587 = 2975381) B2975381
theorem B6694001 : Blo 1321479 6694001 := bstep (se 2 (by rfl) ⟨2510250, by rfl⟩ : syracuseStep 6694001 = 5020501) B5020501
theorem B1983617 : Blo 1321479 1983617 := bstep (se 2 (by rfl) ⟨743856, by rfl⟩ : syracuseStep 1983617 = 1487713) B1487713
theorem B2262161 : Blo 1321479 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B1983635 : Blo 1321479 1983635 := bstep (se 1 (by rfl) ⟨1487726, by rfl⟩ : syracuseStep 1983635 = 2975453) B2975453
theorem B1983665 : Blo 1321479 1983665 := bstep (se 2 (by rfl) ⟨743874, by rfl⟩ : syracuseStep 1983665 = 1487749) B1487749
theorem B1983683 : Blo 1321479 1983683 := bstep (se 1 (by rfl) ⟨1487762, by rfl⟩ : syracuseStep 1983683 = 2975525) B2975525
theorem B1983713 : Blo 1321479 1983713 := bstep (se 2 (by rfl) ⟨743892, by rfl⟩ : syracuseStep 1983713 = 1487785) B1487785
theorem B1983731 : Blo 1321479 1983731 := bstep (se 1 (by rfl) ⟨1487798, by rfl⟩ : syracuseStep 1983731 = 2975597) B2975597
theorem B1983761 : Blo 1321479 1983761 := bstep (se 2 (by rfl) ⟨743910, by rfl⟩ : syracuseStep 1983761 = 1487821) B1487821
theorem B1983779 : Blo 1321479 1983779 := bstep (se 1 (by rfl) ⟨1487834, by rfl⟩ : syracuseStep 1983779 = 2975669) B2975669
theorem B1983809 : Blo 1321479 1983809 := bstep (se 2 (by rfl) ⟨743928, by rfl⟩ : syracuseStep 1983809 = 1487857) B1487857
theorem B2975057 : Blo 1321479 2975057 := bstep (se 2 (by rfl) ⟨1115646, by rfl⟩ : syracuseStep 2975057 = 2231293) B2231293
theorem B1983827 : Blo 1321479 1983827 := bstep (se 1 (by rfl) ⟨1487870, by rfl⟩ : syracuseStep 1983827 = 2975741) B2975741
theorem B2975075 : Blo 1321479 2975075 := bstep (se 1 (by rfl) ⟨2231306, by rfl⟩ : syracuseStep 2975075 = 4462613) B4462613
theorem B1983857 : Blo 1321479 1983857 := bstep (se 2 (by rfl) ⟨743946, by rfl⟩ : syracuseStep 1983857 = 1487893) B1487893
theorem B1672579 : Blo 1321479 1672579 := bstep (se 1 (by rfl) ⟨1254434, by rfl⟩ : syracuseStep 1672579 = 2508869) B2508869
theorem B1983875 : Blo 1321479 1983875 := bstep (se 1 (by rfl) ⟨1487906, by rfl⟩ : syracuseStep 1983875 = 2975813) B2975813
theorem B1983905 : Blo 1321479 1983905 := bstep (se 2 (by rfl) ⟨743964, by rfl⟩ : syracuseStep 1983905 = 1487929) B1487929
theorem B1983923 : Blo 1321479 1983923 := bstep (se 1 (by rfl) ⟨1487942, by rfl⟩ : syracuseStep 1983923 = 2975885) B2975885
theorem B1983953 : Blo 1321479 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B1983971 : Blo 1321479 1983971 := bstep (se 1 (by rfl) ⟨1487978, by rfl⟩ : syracuseStep 1983971 = 2975957) B2975957
theorem B1984001 : Blo 1321479 1984001 := bstep (se 2 (by rfl) ⟨744000, by rfl⟩ : syracuseStep 1984001 = 1488001) B1488001
theorem B7849477 : Blo 1321479 7849477 := bstep (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) B1471777
theorem B1984019 : Blo 1321479 1984019 := bstep (se 1 (by rfl) ⟨1488014, by rfl⟩ : syracuseStep 1984019 = 2976029) B2976029
theorem B1984049 : Blo 1321479 1984049 := bstep (se 2 (by rfl) ⟨744018, by rfl⟩ : syracuseStep 1984049 = 1488037) B1488037
theorem B1984067 : Blo 1321479 1984067 := bstep (se 1 (by rfl) ⟨1488050, by rfl⟩ : syracuseStep 1984067 = 2976101) B2976101
theorem B1984097 : Blo 1321479 1984097 := bstep (se 2 (by rfl) ⟨744036, by rfl⟩ : syracuseStep 1984097 = 1488073) B1488073
theorem B4466285 : Blo 1321479 4466285 := bstep (se 3 (by rfl) ⟨837428, by rfl⟩ : syracuseStep 4466285 = 1674857) B1674857
theorem B2975345 : Blo 1321479 2975345 := bstep (se 2 (by rfl) ⟨1115754, by rfl⟩ : syracuseStep 2975345 = 2231509) B2231509
theorem B1984115 : Blo 1321479 1984115 := bstep (se 1 (by rfl) ⟨1488086, by rfl⟩ : syracuseStep 1984115 = 2976173) B2976173
theorem B2975363 : Blo 1321479 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B2680465 : Blo 1321479 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B1984145 : Blo 1321479 1984145 := bstep (se 2 (by rfl) ⟨744054, by rfl⟩ : syracuseStep 1984145 = 1488109) B1488109
theorem B1984163 : Blo 1321479 1984163 := bstep (se 1 (by rfl) ⟨1488122, by rfl⟩ : syracuseStep 1984163 = 2976245) B2976245
theorem B4466339 : Blo 1321479 4466339 := bstep (se 1 (by rfl) ⟨3349754, by rfl⟩ : syracuseStep 4466339 = 6699509) B6699509
theorem B9053873 : Blo 1321479 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B1984193 : Blo 1321479 1984193 := bstep (se 2 (by rfl) ⟨744072, by rfl⟩ : syracuseStep 1984193 = 1488145) B1488145
theorem B3868355 : Blo 1321479 3868355 := bstep (se 1 (by rfl) ⟨2901266, by rfl⟩ : syracuseStep 3868355 = 5802533) B5802533
theorem B1984211 : Blo 1321479 1984211 := bstep (se 1 (by rfl) ⟨1488158, by rfl⟩ : syracuseStep 1984211 = 2976317) B2976317
theorem B1984241 : Blo 1321479 1984241 := bstep (se 2 (by rfl) ⟨744090, by rfl⟩ : syracuseStep 1984241 = 1488181) B1488181
theorem B1984259 : Blo 1321479 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B1984289 : Blo 1321479 1984289 := bstep (se 2 (by rfl) ⟨744108, by rfl⟩ : syracuseStep 1984289 = 1488217) B1488217
theorem B2230051 : Blo 1321479 2230051 := bstep (se 1 (by rfl) ⟨1672538, by rfl⟩ : syracuseStep 2230051 = 3345077) B3345077
theorem B1984307 : Blo 1321479 1984307 := bstep (se 1 (by rfl) ⟨1488230, by rfl⟩ : syracuseStep 1984307 = 2976461) B2976461
theorem B1984337 : Blo 1321479 1984337 := bstep (se 2 (by rfl) ⟨744126, by rfl⟩ : syracuseStep 1984337 = 1488253) B1488253
theorem B1984355 : Blo 1321479 1984355 := bstep (se 1 (by rfl) ⟨1488266, by rfl⟩ : syracuseStep 1984355 = 2976533) B2976533
theorem B1673075 : Blo 1321479 1673075 := bstep (se 1 (by rfl) ⟨1254806, by rfl⟩ : syracuseStep 1673075 = 2509613) B2509613
theorem B1984385 : Blo 1321479 1984385 := bstep (se 2 (by rfl) ⟨744144, by rfl⟩ : syracuseStep 1984385 = 1488289) B1488289
theorem B2975633 : Blo 1321479 2975633 := bstep (se 2 (by rfl) ⟨1115862, by rfl⟩ : syracuseStep 2975633 = 2231725) B2231725
theorem B1984403 : Blo 1321479 1984403 := bstep (se 1 (by rfl) ⟨1488302, by rfl⟩ : syracuseStep 1984403 = 2976605) B2976605
theorem B2975651 : Blo 1321479 2975651 := bstep (se 1 (by rfl) ⟨2231738, by rfl⟩ : syracuseStep 2975651 = 4463477) B4463477
theorem B2230193 : Blo 1321479 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B1984433 : Blo 1321479 1984433 := bstep (se 2 (by rfl) ⟨744162, by rfl⟩ : syracuseStep 1984433 = 1488325) B1488325
theorem B4466609 : Blo 1321479 4466609 := bstep (se 2 (by rfl) ⟨1674978, by rfl⟩ : syracuseStep 4466609 = 3349957) B3349957
theorem B1984451 : Blo 1321479 1984451 := bstep (se 1 (by rfl) ⟨1488338, by rfl⟩ : syracuseStep 1984451 = 2976677) B2976677
theorem B1984481 : Blo 1321479 1984481 := bstep (se 2 (by rfl) ⟨744180, by rfl⟩ : syracuseStep 1984481 = 1488361) B1488361
theorem B1984499 : Blo 1321479 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B1984529 : Blo 1321479 1984529 := bstep (se 2 (by rfl) ⟨744198, by rfl⟩ : syracuseStep 1984529 = 1488397) B1488397
theorem B1984547 : Blo 1321479 1984547 := bstep (se 1 (by rfl) ⟨1488410, by rfl⟩ : syracuseStep 1984547 = 2976821) B2976821
theorem B2230321 : Blo 1321479 2230321 := bstep (se 2 (by rfl) ⟨836370, by rfl⟩ : syracuseStep 2230321 = 1672741) B1672741
theorem B1984577 : Blo 1321479 1984577 := bstep (se 2 (by rfl) ⟨744216, by rfl⟩ : syracuseStep 1984577 = 1488433) B1488433
theorem B2230355 : Blo 1321479 2230355 := bstep (se 1 (by rfl) ⟨1672766, by rfl⟩ : syracuseStep 2230355 = 3345533) B3345533
theorem B1984595 : Blo 1321479 1984595 := bstep (se 1 (by rfl) ⟨1488446, by rfl⟩ : syracuseStep 1984595 = 2976893) B2976893
theorem B5359729 : Blo 1321479 5359729 := bstep (se 2 (by rfl) ⟨2009898, by rfl⟩ : syracuseStep 5359729 = 4019797) B4019797
theorem B1984625 : Blo 1321479 1984625 := bstep (se 2 (by rfl) ⟨744234, by rfl⟩ : syracuseStep 1984625 = 1488469) B1488469
theorem B1984643 : Blo 1321479 1984643 := bstep (se 1 (by rfl) ⟨1488482, by rfl⟩ : syracuseStep 1984643 = 2976965) B2976965
theorem B1984673 : Blo 1321479 1984673 := bstep (se 2 (by rfl) ⟨744252, by rfl⟩ : syracuseStep 1984673 = 1488505) B1488505
theorem B2975921 : Blo 1321479 2975921 := bstep (se 2 (by rfl) ⟨1115970, by rfl⟩ : syracuseStep 2975921 = 2231941) B2231941
theorem B1984691 : Blo 1321479 1984691 := bstep (se 1 (by rfl) ⟨1488518, by rfl⟩ : syracuseStep 1984691 = 2977037) B2977037
theorem B2975939 : Blo 1321479 2975939 := bstep (se 1 (by rfl) ⟨2231954, by rfl⟩ : syracuseStep 2975939 = 4463909) B4463909
theorem B1984721 : Blo 1321479 1984721 := bstep (se 2 (by rfl) ⟨744270, by rfl⟩ : syracuseStep 1984721 = 1488541) B1488541
theorem B2230483 : Blo 1321479 2230483 := bstep (se 1 (by rfl) ⟨1672862, by rfl⟩ : syracuseStep 2230483 = 3345725) B3345725
theorem B1984739 : Blo 1321479 1984739 := bstep (se 1 (by rfl) ⟨1488554, by rfl⟩ : syracuseStep 1984739 = 2977109) B2977109
theorem B1984769 : Blo 1321479 1984769 := bstep (se 2 (by rfl) ⟨744288, by rfl⟩ : syracuseStep 1984769 = 1488577) B1488577
theorem B1984787 : Blo 1321479 1984787 := bstep (se 1 (by rfl) ⟨1488590, by rfl⟩ : syracuseStep 1984787 = 2977181) B2977181
theorem B6785315 : Blo 1321479 6785315 := bstep (se 1 (by rfl) ⟨5088986, by rfl⟩ : syracuseStep 6785315 = 10177973) B10177973
theorem B2681137 : Blo 1321479 2681137 := bstep (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) B2010853
theorem B1984817 : Blo 1321479 1984817 := bstep (se 2 (by rfl) ⟨744306, by rfl⟩ : syracuseStep 1984817 = 1488613) B1488613
theorem B1984835 : Blo 1321479 1984835 := bstep (se 1 (by rfl) ⟨1488626, by rfl⟩ : syracuseStep 1984835 = 2977253) B2977253
theorem B2230625 : Blo 1321479 2230625 := bstep (se 2 (by rfl) ⟨836484, by rfl⟩ : syracuseStep 2230625 = 1672969) B1672969
theorem B1984865 : Blo 1321479 1984865 := bstep (se 2 (by rfl) ⟨744324, by rfl⟩ : syracuseStep 1984865 = 1488649) B1488649
theorem B1984883 : Blo 1321479 1984883 := bstep (se 1 (by rfl) ⟨1488662, by rfl⟩ : syracuseStep 1984883 = 2977325) B2977325
theorem B7637381 : Blo 1321479 7637381 := bstep (se 4 (by rfl) ⟨716004, by rfl⟩ : syracuseStep 7637381 = 1432009) B1432009
theorem B1984913 : Blo 1321479 1984913 := bstep (se 2 (by rfl) ⟨744342, by rfl⟩ : syracuseStep 1984913 = 1488685) B1488685
theorem B1984931 : Blo 1321479 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B5024177 : Blo 1321479 5024177 := bstep (se 2 (by rfl) ⟨1884066, by rfl⟩ : syracuseStep 5024177 = 3768133) B3768133
theorem B1984961 : Blo 1321479 1984961 := bstep (se 2 (by rfl) ⟨744360, by rfl⟩ : syracuseStep 1984961 = 1488721) B1488721
theorem B2976209 : Blo 1321479 2976209 := bstep (se 2 (by rfl) ⟨1116078, by rfl⟩ : syracuseStep 2976209 = 2232157) B2232157
theorem B1984979 : Blo 1321479 1984979 := bstep (se 1 (by rfl) ⟨1488734, by rfl⟩ : syracuseStep 1984979 = 2977469) B2977469
theorem B2230753 : Blo 1321479 2230753 := bstep (se 2 (by rfl) ⟨836532, by rfl⟩ : syracuseStep 2230753 = 1673065) B1673065
theorem B1411555 : Blo 1321479 1411555 := bstep (se 1 (by rfl) ⟨1058666, by rfl⟩ : syracuseStep 1411555 = 2117333) B2117333
theorem B2976227 : Blo 1321479 2976227 := bstep (se 1 (by rfl) ⟨2232170, by rfl⟩ : syracuseStep 2976227 = 4464341) B4464341
theorem B3574253 : Blo 1321479 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B1985009 : Blo 1321479 1985009 := bstep (se 2 (by rfl) ⟨744378, by rfl⟩ : syracuseStep 1985009 = 1488757) B1488757
theorem B2230787 : Blo 1321479 2230787 := bstep (se 1 (by rfl) ⟨1673090, by rfl⟩ : syracuseStep 2230787 = 3346181) B3346181
theorem B1985027 : Blo 1321479 1985027 := bstep (se 1 (by rfl) ⟨1488770, by rfl⟩ : syracuseStep 1985027 = 2977541) B2977541
theorem B1321491 : Blo 1321479 1321491 := bstep (se 1 (by rfl) ⟨991118, by rfl⟩ : syracuseStep 1321491 = 1982237) B1982237
theorem B1985057 : Blo 1321479 1985057 := bstep (se 2 (by rfl) ⟨744396, by rfl⟩ : syracuseStep 1985057 = 1488793) B1488793
theorem B1321507 : Blo 1321479 1321507 := bstep (se 1 (by rfl) ⟨991130, by rfl⟩ : syracuseStep 1321507 = 1982261) B1982261
theorem B6695459 : Blo 1321479 6695459 := bstep (se 1 (by rfl) ⟨5021594, by rfl⟩ : syracuseStep 6695459 = 10043189) B10043189
theorem B1321523 : Blo 1321479 1321523 := bstep (se 1 (by rfl) ⟨991142, by rfl⟩ : syracuseStep 1321523 = 1982285) B1982285
theorem B1673779 : Blo 1321479 1673779 := bstep (se 1 (by rfl) ⟨1255334, by rfl⟩ : syracuseStep 1673779 = 2510669) B2510669
theorem B1985075 : Blo 1321479 1985075 := bstep (se 1 (by rfl) ⟨1488806, by rfl⟩ : syracuseStep 1985075 = 2977613) B2977613
theorem B1321539 : Blo 1321479 1321539 := bstep (se 1 (by rfl) ⟨991154, by rfl⟩ : syracuseStep 1321539 = 1982309) B1982309
theorem B2509393 : Blo 1321479 2509393 := bstep (se 2 (by rfl) ⟨941022, by rfl⟩ : syracuseStep 2509393 = 1882045) B1882045
theorem B1321555 : Blo 1321479 1321555 := bstep (se 1 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 1321555 = 1982333) B1982333
theorem B1985105 : Blo 1321479 1985105 := bstep (se 2 (by rfl) ⟨744414, by rfl⟩ : syracuseStep 1985105 = 1488829) B1488829
theorem B1321571 : Blo 1321479 1321571 := bstep (se 1 (by rfl) ⟨991178, by rfl⟩ : syracuseStep 1321571 = 1982357) B1982357
theorem B7146083 : Blo 1321479 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B1985123 : Blo 1321479 1985123 := bstep (se 1 (by rfl) ⟨1488842, by rfl⟩ : syracuseStep 1985123 = 2977685) B2977685
theorem B1321587 : Blo 1321479 1321587 := bstep (se 1 (by rfl) ⟨991190, by rfl⟩ : syracuseStep 1321587 = 1982381) B1982381
theorem B1985153 : Blo 1321479 1985153 := bstep (se 2 (by rfl) ⟨744432, by rfl⟩ : syracuseStep 1985153 = 1488865) B1488865
theorem B1321603 : Blo 1321479 1321603 := bstep (se 1 (by rfl) ⟨991202, by rfl⟩ : syracuseStep 1321603 = 1982405) B1982405
theorem B2230915 : Blo 1321479 2230915 := bstep (se 1 (by rfl) ⟨1673186, by rfl⟩ : syracuseStep 2230915 = 3346373) B3346373
theorem B1321619 : Blo 1321479 1321619 := bstep (se 1 (by rfl) ⟨991214, by rfl⟩ : syracuseStep 1321619 = 1982429) B1982429
theorem B1673875 : Blo 1321479 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B1985171 : Blo 1321479 1985171 := bstep (se 1 (by rfl) ⟨1488878, by rfl⟩ : syracuseStep 1985171 = 2977757) B2977757
theorem B1321635 : Blo 1321479 1321635 := bstep (se 1 (by rfl) ⟨991226, by rfl⟩ : syracuseStep 1321635 = 1982453) B1982453
theorem B1985201 : Blo 1321479 1985201 := bstep (se 2 (by rfl) ⟨744450, by rfl⟩ : syracuseStep 1985201 = 1488901) B1488901
theorem B1321651 : Blo 1321479 1321651 := bstep (se 1 (by rfl) ⟨991238, by rfl⟩ : syracuseStep 1321651 = 1982477) B1982477
theorem B1321667 : Blo 1321479 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B1985219 : Blo 1321479 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B1321683 : Blo 1321479 1321683 := bstep (se 1 (by rfl) ⟨991262, by rfl⟩ : syracuseStep 1321683 = 1982525) B1982525
theorem B1321699 : Blo 1321479 1321699 := bstep (se 1 (by rfl) ⟨991274, by rfl⟩ : syracuseStep 1321699 = 1982549) B1982549
theorem B2976497 : Blo 1321479 2976497 := bstep (se 2 (by rfl) ⟨1116186, by rfl⟩ : syracuseStep 2976497 = 2232373) B2232373
theorem B1321715 : Blo 1321479 1321715 := bstep (se 1 (by rfl) ⟨991286, by rfl⟩ : syracuseStep 1321715 = 1982573) B1982573
theorem B1321731 : Blo 1321479 1321731 := bstep (se 1 (by rfl) ⟨991298, by rfl⟩ : syracuseStep 1321731 = 1982597) B1982597
theorem B2976515 : Blo 1321479 2976515 := bstep (se 1 (by rfl) ⟨2232386, by rfl⟩ : syracuseStep 2976515 = 4464773) B4464773
theorem B2231057 : Blo 1321479 2231057 := bstep (se 2 (by rfl) ⟨836646, by rfl⟩ : syracuseStep 2231057 = 1673293) B1673293
theorem B1321747 : Blo 1321479 1321747 := bstep (se 1 (by rfl) ⟨991310, by rfl⟩ : syracuseStep 1321747 = 1982621) B1982621
theorem B1321763 : Blo 1321479 1321763 := bstep (se 1 (by rfl) ⟨991322, by rfl⟩ : syracuseStep 1321763 = 1982645) B1982645
theorem B1321779 : Blo 1321479 1321779 := bstep (se 1 (by rfl) ⟨991334, by rfl⟩ : syracuseStep 1321779 = 1982669) B1982669
theorem B1321795 : Blo 1321479 1321795 := bstep (se 1 (by rfl) ⟨991346, by rfl⟩ : syracuseStep 1321795 = 1982693) B1982693
theorem B1321811 : Blo 1321479 1321811 := bstep (se 1 (by rfl) ⟨991358, by rfl⟩ : syracuseStep 1321811 = 1982717) B1982717
theorem B1321827 : Blo 1321479 1321827 := bstep (se 1 (by rfl) ⟨991370, by rfl⟩ : syracuseStep 1321827 = 1982741) B1982741
theorem B1321843 : Blo 1321479 1321843 := bstep (se 1 (by rfl) ⟨991382, by rfl⟩ : syracuseStep 1321843 = 1982765) B1982765
theorem B1321859 : Blo 1321479 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B2231185 : Blo 1321479 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B1321875 : Blo 1321479 1321875 := bstep (se 1 (by rfl) ⟨991406, by rfl⟩ : syracuseStep 1321875 = 1982813) B1982813
theorem B1321891 : Blo 1321479 1321891 := bstep (se 1 (by rfl) ⟨991418, by rfl⟩ : syracuseStep 1321891 = 1982837) B1982837
theorem B1321907 : Blo 1321479 1321907 := bstep (se 1 (by rfl) ⟨991430, by rfl⟩ : syracuseStep 1321907 = 1982861) B1982861
theorem B2231219 : Blo 1321479 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B1321923 : Blo 1321479 1321923 := bstep (se 1 (by rfl) ⟨991442, by rfl⟩ : syracuseStep 1321923 = 1982885) B1982885
theorem B1321939 : Blo 1321479 1321939 := bstep (se 1 (by rfl) ⟨991454, by rfl⟩ : syracuseStep 1321939 = 1982909) B1982909
theorem B1321955 : Blo 1321479 1321955 := bstep (se 1 (by rfl) ⟨991466, by rfl⟩ : syracuseStep 1321955 = 1982933) B1982933
theorem B2509795 : Blo 1321479 2509795 := bstep (se 1 (by rfl) ⟨1882346, by rfl⟩ : syracuseStep 2509795 = 3764693) B3764693
theorem B1321971 : Blo 1321479 1321971 := bstep (se 1 (by rfl) ⟨991478, by rfl⟩ : syracuseStep 1321971 = 1982957) B1982957
theorem B1321987 : Blo 1321479 1321987 := bstep (se 1 (by rfl) ⟨991490, by rfl⟩ : syracuseStep 1321987 = 1982981) B1982981
theorem B2509841 : Blo 1321479 2509841 := bstep (se 2 (by rfl) ⟨941190, by rfl⟩ : syracuseStep 2509841 = 1882381) B1882381
theorem B2976785 : Blo 1321479 2976785 := bstep (se 2 (by rfl) ⟨1116294, by rfl⟩ : syracuseStep 2976785 = 2232589) B2232589
theorem B1322003 : Blo 1321479 1322003 := bstep (se 1 (by rfl) ⟨991502, by rfl⟩ : syracuseStep 1322003 = 1983005) B1983005
theorem B3763235 : Blo 1321479 3763235 := bstep (se 1 (by rfl) ⟨2822426, by rfl⟩ : syracuseStep 3763235 = 5644853) B5644853
theorem B1322019 : Blo 1321479 1322019 := bstep (se 1 (by rfl) ⟨991514, by rfl⟩ : syracuseStep 1322019 = 1983029) B1983029
theorem B2976803 : Blo 1321479 2976803 := bstep (se 1 (by rfl) ⟨2232602, by rfl⟩ : syracuseStep 2976803 = 4465205) B4465205
theorem B1322035 : Blo 1321479 1322035 := bstep (se 1 (by rfl) ⟨991526, by rfl⟩ : syracuseStep 1322035 = 1983053) B1983053
theorem B2231347 : Blo 1321479 2231347 := bstep (se 1 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 2231347 = 3347021) B3347021
theorem B1322051 : Blo 1321479 1322051 := bstep (se 1 (by rfl) ⟨991538, by rfl⟩ : syracuseStep 1322051 = 1983077) B1983077
theorem B2681923 : Blo 1321479 2681923 := bstep (se 1 (by rfl) ⟨2011442, by rfl⟩ : syracuseStep 2681923 = 4022885) B4022885
theorem B5360717 : Blo 1321479 5360717 := bstep (se 3 (by rfl) ⟨1005134, by rfl⟩ : syracuseStep 5360717 = 2010269) B2010269
theorem B1322067 : Blo 1321479 1322067 := bstep (se 1 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 1322067 = 1983101) B1983101
theorem B1322083 : Blo 1321479 1322083 := bstep (se 1 (by rfl) ⟨991562, by rfl⟩ : syracuseStep 1322083 = 1983125) B1983125
theorem B1322099 : Blo 1321479 1322099 := bstep (se 1 (by rfl) ⟨991574, by rfl⟩ : syracuseStep 1322099 = 1983149) B1983149
theorem B1322115 : Blo 1321479 1322115 := bstep (se 1 (by rfl) ⟨991586, by rfl⟩ : syracuseStep 1322115 = 1983173) B1983173
theorem B1674371 : Blo 1321479 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B1322131 : Blo 1321479 1322131 := bstep (se 1 (by rfl) ⟨991598, by rfl⟩ : syracuseStep 1322131 = 1983197) B1983197
theorem B1322147 : Blo 1321479 1322147 := bstep (se 1 (by rfl) ⟨991610, by rfl⟩ : syracuseStep 1322147 = 1983221) B1983221
theorem B4238509 : Blo 1321479 4238509 := bstep (se 3 (by rfl) ⟨794720, by rfl⟩ : syracuseStep 4238509 = 1589441) B1589441
theorem B1322163 : Blo 1321479 1322163 := bstep (se 1 (by rfl) ⟨991622, by rfl⟩ : syracuseStep 1322163 = 1983245) B1983245
theorem B2231489 : Blo 1321479 2231489 := bstep (se 2 (by rfl) ⟨836808, by rfl⟩ : syracuseStep 2231489 = 1673617) B1673617
theorem B1322179 : Blo 1321479 1322179 := bstep (se 1 (by rfl) ⟨991634, by rfl⟩ : syracuseStep 1322179 = 1983269) B1983269
theorem B1322195 : Blo 1321479 1322195 := bstep (se 1 (by rfl) ⟨991646, by rfl⟩ : syracuseStep 1322195 = 1983293) B1983293
theorem B1322211 : Blo 1321479 1322211 := bstep (se 1 (by rfl) ⟨991658, by rfl⟩ : syracuseStep 1322211 = 1983317) B1983317
theorem B8473841 : Blo 1321479 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B1322227 : Blo 1321479 1322227 := bstep (se 1 (by rfl) ⟨991670, by rfl⟩ : syracuseStep 1322227 = 1983341) B1983341
theorem B1322243 : Blo 1321479 1322243 := bstep (se 1 (by rfl) ⟨991682, by rfl⟩ : syracuseStep 1322243 = 1983365) B1983365
theorem B7630085 : Blo 1321479 7630085 := bstep (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) B1430641
theorem B15068429 : Blo 1321479 15068429 := bstep (se 3 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 15068429 = 5650661) B5650661
theorem B1322259 : Blo 1321479 1322259 := bstep (se 1 (by rfl) ⟨991694, by rfl⟩ : syracuseStep 1322259 = 1983389) B1983389
theorem B1322275 : Blo 1321479 1322275 := bstep (se 1 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 1322275 = 1983413) B1983413
theorem B2510129 : Blo 1321479 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B2977073 : Blo 1321479 2977073 := bstep (se 2 (by rfl) ⟨1116402, by rfl⟩ : syracuseStep 2977073 = 2232805) B2232805
theorem B1322291 : Blo 1321479 1322291 := bstep (se 1 (by rfl) ⟨991718, by rfl⟩ : syracuseStep 1322291 = 1983437) B1983437
theorem B2231617 : Blo 1321479 2231617 := bstep (se 2 (by rfl) ⟨836856, by rfl⟩ : syracuseStep 2231617 = 1673713) B1673713
theorem B1322307 : Blo 1321479 1322307 := bstep (se 1 (by rfl) ⟨991730, by rfl⟩ : syracuseStep 1322307 = 1983461) B1983461
theorem B2977091 : Blo 1321479 2977091 := bstep (se 1 (by rfl) ⟨2232818, by rfl⟩ : syracuseStep 2977091 = 4465637) B4465637
theorem B6696269 : Blo 1321479 6696269 := bstep (se 3 (by rfl) ⟨1255550, by rfl⟩ : syracuseStep 6696269 = 2511101) B2511101
theorem B3345745 : Blo 1321479 3345745 := bstep (se 2 (by rfl) ⟨1254654, by rfl⟩ : syracuseStep 3345745 = 2509309) B2509309
theorem B1322323 : Blo 1321479 1322323 := bstep (se 1 (by rfl) ⟨991742, by rfl⟩ : syracuseStep 1322323 = 1983485) B1983485
theorem B1412435 : Blo 1321479 1412435 := bstep (se 1 (by rfl) ⟨1059326, by rfl⟩ : syracuseStep 1412435 = 2118653) B2118653
theorem B1322339 : Blo 1321479 1322339 := bstep (se 1 (by rfl) ⟨991754, by rfl⟩ : syracuseStep 1322339 = 1983509) B1983509
theorem B2231651 : Blo 1321479 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B1322355 : Blo 1321479 1322355 := bstep (se 1 (by rfl) ⟨991766, by rfl⟩ : syracuseStep 1322355 = 1983533) B1983533
theorem B1322371 : Blo 1321479 1322371 := bstep (se 1 (by rfl) ⟨991778, by rfl⟩ : syracuseStep 1322371 = 1983557) B1983557
theorem B1322387 : Blo 1321479 1322387 := bstep (se 1 (by rfl) ⟨991790, by rfl⟩ : syracuseStep 1322387 = 1983581) B1983581
theorem B1322403 : Blo 1321479 1322403 := bstep (se 1 (by rfl) ⟨991802, by rfl⟩ : syracuseStep 1322403 = 1983605) B1983605
theorem B3722669 : Blo 1321479 3722669 := bstep (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) B1396001
theorem B7146929 : Blo 1321479 7146929 := bstep (se 2 (by rfl) ⟨2680098, by rfl⟩ : syracuseStep 7146929 = 5360197) B5360197
theorem B1322419 : Blo 1321479 1322419 := bstep (se 1 (by rfl) ⟨991814, by rfl⟩ : syracuseStep 1322419 = 1983629) B1983629
theorem B1322435 : Blo 1321479 1322435 := bstep (se 1 (by rfl) ⟨991826, by rfl⟩ : syracuseStep 1322435 = 1983653) B1983653
theorem B7146949 : Blo 1321479 7146949 := bstep (se 4 (by rfl) ⟨670026, by rfl⟩ : syracuseStep 7146949 = 1340053) B1340053
theorem B1322451 : Blo 1321479 1322451 := bstep (se 1 (by rfl) ⟨991838, by rfl⟩ : syracuseStep 1322451 = 1983677) B1983677
theorem B1412563 : Blo 1321479 1412563 := bstep (se 1 (by rfl) ⟨1059422, by rfl⟩ : syracuseStep 1412563 = 2118845) B2118845
theorem B1322467 : Blo 1321479 1322467 := bstep (se 1 (by rfl) ⟨991850, by rfl⟩ : syracuseStep 1322467 = 1983701) B1983701
theorem B2231779 : Blo 1321479 2231779 := bstep (se 1 (by rfl) ⟨1673834, by rfl⟩ : syracuseStep 2231779 = 3347669) B3347669
theorem B1322483 : Blo 1321479 1322483 := bstep (se 1 (by rfl) ⟨991862, by rfl⟩ : syracuseStep 1322483 = 1983725) B1983725
theorem B1322499 : Blo 1321479 1322499 := bstep (se 1 (by rfl) ⟨991874, by rfl⟩ : syracuseStep 1322499 = 1983749) B1983749
theorem B1322515 : Blo 1321479 1322515 := bstep (se 1 (by rfl) ⟨991886, by rfl⟩ : syracuseStep 1322515 = 1983773) B1983773
theorem B1322531 : Blo 1321479 1322531 := bstep (se 1 (by rfl) ⟨991898, by rfl⟩ : syracuseStep 1322531 = 1983797) B1983797
theorem B1322547 : Blo 1321479 1322547 := bstep (se 1 (by rfl) ⟨991910, by rfl⟩ : syracuseStep 1322547 = 1983821) B1983821
theorem B1322563 : Blo 1321479 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B2977361 : Blo 1321479 2977361 := bstep (se 2 (by rfl) ⟨1116510, by rfl⟩ : syracuseStep 2977361 = 2233021) B2233021
theorem B1322579 : Blo 1321479 1322579 := bstep (se 1 (by rfl) ⟨991934, by rfl⟩ : syracuseStep 1322579 = 1983869) B1983869
theorem B3346019 : Blo 1321479 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B1322595 : Blo 1321479 1322595 := bstep (se 1 (by rfl) ⟨991946, by rfl⟩ : syracuseStep 1322595 = 1983893) B1983893
theorem B3395171 : Blo 1321479 3395171 := bstep (se 1 (by rfl) ⟨2546378, by rfl⟩ : syracuseStep 3395171 = 5092757) B5092757
theorem B2977379 : Blo 1321479 2977379 := bstep (se 1 (by rfl) ⟨2233034, by rfl⟩ : syracuseStep 2977379 = 4466069) B4466069
theorem B4763249 : Blo 1321479 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B2231921 : Blo 1321479 2231921 := bstep (se 2 (by rfl) ⟨836970, by rfl⟩ : syracuseStep 2231921 = 1673941) B1673941
theorem B1322611 : Blo 1321479 1322611 := bstep (se 1 (by rfl) ⟨991958, by rfl⟩ : syracuseStep 1322611 = 1983917) B1983917
theorem B1322627 : Blo 1321479 1322627 := bstep (se 1 (by rfl) ⟨991970, by rfl⟩ : syracuseStep 1322627 = 1983941) B1983941
theorem B1322643 : Blo 1321479 1322643 := bstep (se 1 (by rfl) ⟨991982, by rfl⟩ : syracuseStep 1322643 = 1983965) B1983965
theorem B1322659 : Blo 1321479 1322659 := bstep (se 1 (by rfl) ⟨991994, by rfl⟩ : syracuseStep 1322659 = 1983989) B1983989
theorem B1322675 : Blo 1321479 1322675 := bstep (se 1 (by rfl) ⟨992006, by rfl⟩ : syracuseStep 1322675 = 1984013) B1984013
theorem B1322691 : Blo 1321479 1322691 := bstep (se 1 (by rfl) ⟨992018, by rfl⟩ : syracuseStep 1322691 = 1984037) B1984037
theorem B4460237 : Blo 1321479 4460237 := bstep (se 3 (by rfl) ⟨836294, by rfl⟩ : syracuseStep 4460237 = 1672589) B1672589
theorem B1322707 : Blo 1321479 1322707 := bstep (se 1 (by rfl) ⟨992030, by rfl⟩ : syracuseStep 1322707 = 1984061) B1984061
theorem B1322723 : Blo 1321479 1322723 := bstep (se 1 (by rfl) ⟨992042, by rfl⟩ : syracuseStep 1322723 = 1984085) B1984085
theorem B3264241 : Blo 1321479 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B2232049 : Blo 1321479 2232049 := bstep (se 2 (by rfl) ⟨837018, by rfl⟩ : syracuseStep 2232049 = 1674037) B1674037
theorem B1322739 : Blo 1321479 1322739 := bstep (se 1 (by rfl) ⟨992054, by rfl⟩ : syracuseStep 1322739 = 1984109) B1984109
theorem B4460291 : Blo 1321479 4460291 := bstep (se 1 (by rfl) ⟨3345218, by rfl⟩ : syracuseStep 4460291 = 6690437) B6690437
theorem B1322755 : Blo 1321479 1322755 := bstep (se 1 (by rfl) ⟨992066, by rfl⟩ : syracuseStep 1322755 = 1984133) B1984133
theorem B7147277 : Blo 1321479 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B2232083 : Blo 1321479 2232083 := bstep (se 1 (by rfl) ⟨1674062, by rfl⟩ : syracuseStep 2232083 = 3348125) B3348125
theorem B1322771 : Blo 1321479 1322771 := bstep (se 1 (by rfl) ⟨992078, by rfl⟩ : syracuseStep 1322771 = 1984157) B1984157
theorem B3346211 : Blo 1321479 3346211 := bstep (se 1 (by rfl) ⟨2509658, by rfl⟩ : syracuseStep 3346211 = 5019317) B5019317
theorem B1322787 : Blo 1321479 1322787 := bstep (se 1 (by rfl) ⟨992090, by rfl⟩ : syracuseStep 1322787 = 1984181) B1984181
theorem B1322803 : Blo 1321479 1322803 := bstep (se 1 (by rfl) ⟨992102, by rfl⟩ : syracuseStep 1322803 = 1984205) B1984205
theorem B1322819 : Blo 1321479 1322819 := bstep (se 1 (by rfl) ⟨992114, by rfl⟩ : syracuseStep 1322819 = 1984229) B1984229
theorem B1322835 : Blo 1321479 1322835 := bstep (se 1 (by rfl) ⟨992126, by rfl⟩ : syracuseStep 1322835 = 1984253) B1984253
theorem B1322851 : Blo 1321479 1322851 := bstep (se 1 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 1322851 = 1984277) B1984277
theorem B2977649 : Blo 1321479 2977649 := bstep (se 2 (by rfl) ⟨1116618, by rfl⟩ : syracuseStep 2977649 = 2233237) B2233237
theorem B1322867 : Blo 1321479 1322867 := bstep (se 1 (by rfl) ⟨992150, by rfl⟩ : syracuseStep 1322867 = 1984301) B1984301
theorem B1486723 : Blo 1321479 1486723 := bstep (se 1 (by rfl) ⟨1115042, by rfl⟩ : syracuseStep 1486723 = 2230085) B2230085
theorem B1322883 : Blo 1321479 1322883 := bstep (se 1 (by rfl) ⟨992162, by rfl⟩ : syracuseStep 1322883 = 1984325) B1984325
theorem B2977667 : Blo 1321479 2977667 := bstep (se 1 (by rfl) ⟨2233250, by rfl⟩ : syracuseStep 2977667 = 4466501) B4466501
theorem B2232211 : Blo 1321479 2232211 := bstep (se 1 (by rfl) ⟨1674158, by rfl⟩ : syracuseStep 2232211 = 3348317) B3348317
theorem B1322899 : Blo 1321479 1322899 := bstep (se 1 (by rfl) ⟨992174, by rfl⟩ : syracuseStep 1322899 = 1984349) B1984349
theorem B1322915 : Blo 1321479 1322915 := bstep (se 1 (by rfl) ⟨992186, by rfl⟩ : syracuseStep 1322915 = 1984373) B1984373
theorem B1322931 : Blo 1321479 1322931 := bstep (se 1 (by rfl) ⟨992198, by rfl⟩ : syracuseStep 1322931 = 1984397) B1984397
theorem B1322947 : Blo 1321479 1322947 := bstep (se 1 (by rfl) ⟨992210, by rfl⟩ : syracuseStep 1322947 = 1984421) B1984421
theorem B1322963 : Blo 1321479 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B5017571 : Blo 1321479 5017571 := bstep (se 1 (by rfl) ⟨3763178, by rfl⟩ : syracuseStep 5017571 = 7526357) B7526357
theorem B6033379 : Blo 1321479 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B1322979 : Blo 1321479 1322979 := bstep (se 1 (by rfl) ⟨992234, by rfl⟩ : syracuseStep 1322979 = 1984469) B1984469
theorem B5017585 : Blo 1321479 5017585 := bstep (se 2 (by rfl) ⟨1881594, by rfl⟩ : syracuseStep 5017585 = 3763189) B3763189
theorem B1322995 : Blo 1321479 1322995 := bstep (se 1 (by rfl) ⟨992246, by rfl⟩ : syracuseStep 1322995 = 1984493) B1984493
theorem B2510851 : Blo 1321479 2510851 := bstep (se 1 (by rfl) ⟨1883138, by rfl⟩ : syracuseStep 2510851 = 3766277) B3766277
theorem B1323011 : Blo 1321479 1323011 := bstep (se 1 (by rfl) ⟨992258, by rfl⟩ : syracuseStep 1323011 = 1984517) B1984517
theorem B4460561 : Blo 1321479 4460561 := bstep (se 2 (by rfl) ⟨1672710, by rfl⟩ : syracuseStep 4460561 = 3345421) B3345421
theorem B1486867 : Blo 1321479 1486867 := bstep (se 1 (by rfl) ⟨1115150, by rfl⟩ : syracuseStep 1486867 = 2230301) B2230301
theorem B1323027 : Blo 1321479 1323027 := bstep (se 1 (by rfl) ⟨992270, by rfl⟩ : syracuseStep 1323027 = 1984541) B1984541
theorem B2232353 : Blo 1321479 2232353 := bstep (se 2 (by rfl) ⟨837132, by rfl⟩ : syracuseStep 2232353 = 1674265) B1674265
theorem B1609763 : Blo 1321479 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B1323043 : Blo 1321479 1323043 := bstep (se 1 (by rfl) ⟨992282, by rfl⟩ : syracuseStep 1323043 = 1984565) B1984565
theorem B1323059 : Blo 1321479 1323059 := bstep (se 1 (by rfl) ⟨992294, by rfl⟩ : syracuseStep 1323059 = 1984589) B1984589
theorem B1323075 : Blo 1321479 1323075 := bstep (se 1 (by rfl) ⟨992306, by rfl⟩ : syracuseStep 1323075 = 1984613) B1984613
theorem B7532621 : Blo 1321479 7532621 := bstep (se 3 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 7532621 = 2824733) B2824733
theorem B1323091 : Blo 1321479 1323091 := bstep (se 1 (by rfl) ⟨992318, by rfl⟩ : syracuseStep 1323091 = 1984637) B1984637
theorem B1323107 : Blo 1321479 1323107 := bstep (se 1 (by rfl) ⟨992330, by rfl⟩ : syracuseStep 1323107 = 1984661) B1984661
theorem B1323123 : Blo 1321479 1323123 := bstep (se 1 (by rfl) ⟨992342, by rfl⟩ : syracuseStep 1323123 = 1984685) B1984685
theorem B1323139 : Blo 1321479 1323139 := bstep (se 1 (by rfl) ⟨992354, by rfl⟩ : syracuseStep 1323139 = 1984709) B1984709
theorem B1323155 : Blo 1321479 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B2232481 : Blo 1321479 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B1487011 : Blo 1321479 1487011 := bstep (se 1 (by rfl) ⟨1115258, by rfl⟩ : syracuseStep 1487011 = 2230517) B2230517
theorem B1323171 : Blo 1321479 1323171 := bstep (se 1 (by rfl) ⟨992378, by rfl⟩ : syracuseStep 1323171 = 1984757) B1984757
theorem B1323187 : Blo 1321479 1323187 := bstep (se 1 (by rfl) ⟨992390, by rfl⟩ : syracuseStep 1323187 = 1984781) B1984781
theorem B2232515 : Blo 1321479 2232515 := bstep (se 1 (by rfl) ⟨1674386, by rfl⟩ : syracuseStep 2232515 = 3348773) B3348773
theorem B1323203 : Blo 1321479 1323203 := bstep (se 1 (by rfl) ⟨992402, by rfl⟩ : syracuseStep 1323203 = 1984805) B1984805
theorem B1323219 : Blo 1321479 1323219 := bstep (se 1 (by rfl) ⟨992414, by rfl⟩ : syracuseStep 1323219 = 1984829) B1984829
theorem B5648611 : Blo 1321479 5648611 := bstep (se 1 (by rfl) ⟨4236458, by rfl⟩ : syracuseStep 5648611 = 8472917) B8472917
theorem B1323235 : Blo 1321479 1323235 := bstep (se 1 (by rfl) ⟨992426, by rfl⟩ : syracuseStep 1323235 = 1984853) B1984853
theorem B3764465 : Blo 1321479 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B1323251 : Blo 1321479 1323251 := bstep (se 1 (by rfl) ⟨992438, by rfl⟩ : syracuseStep 1323251 = 1984877) B1984877
theorem B1323267 : Blo 1321479 1323267 := bstep (se 1 (by rfl) ⟨992450, by rfl⟩ : syracuseStep 1323267 = 1984901) B1984901
theorem B1323283 : Blo 1321479 1323283 := bstep (se 1 (by rfl) ⟨992462, by rfl⟩ : syracuseStep 1323283 = 1984925) B1984925
theorem B1323299 : Blo 1321479 1323299 := bstep (se 1 (by rfl) ⟨992474, by rfl⟩ : syracuseStep 1323299 = 1984949) B1984949
theorem B1487155 : Blo 1321479 1487155 := bstep (se 1 (by rfl) ⟨1115366, by rfl⟩ : syracuseStep 1487155 = 2230733) B2230733
theorem B1323315 : Blo 1321479 1323315 := bstep (se 1 (by rfl) ⟨992486, by rfl⟩ : syracuseStep 1323315 = 1984973) B1984973
theorem B2232643 : Blo 1321479 2232643 := bstep (se 1 (by rfl) ⟨1674482, by rfl⟩ : syracuseStep 2232643 = 3348965) B3348965
theorem B1323331 : Blo 1321479 1323331 := bstep (se 1 (by rfl) ⟨992498, by rfl⟩ : syracuseStep 1323331 = 1984997) B1984997
theorem B1323347 : Blo 1321479 1323347 := bstep (se 1 (by rfl) ⟨992510, by rfl⟩ : syracuseStep 1323347 = 1985021) B1985021
theorem B1323363 : Blo 1321479 1323363 := bstep (se 1 (by rfl) ⟨992522, by rfl⟩ : syracuseStep 1323363 = 1985045) B1985045
theorem B1323379 : Blo 1321479 1323379 := bstep (se 1 (by rfl) ⟨992534, by rfl⟩ : syracuseStep 1323379 = 1985069) B1985069
theorem B1323395 : Blo 1321479 1323395 := bstep (se 1 (by rfl) ⟨992546, by rfl⟩ : syracuseStep 1323395 = 1985093) B1985093
theorem B1323411 : Blo 1321479 1323411 := bstep (se 1 (by rfl) ⟨992558, by rfl⟩ : syracuseStep 1323411 = 1985117) B1985117
theorem B2822563 : Blo 1321479 2822563 := bstep (se 1 (by rfl) ⟨2116922, by rfl⟩ : syracuseStep 2822563 = 4233845) B4233845
theorem B1323427 : Blo 1321479 1323427 := bstep (se 1 (by rfl) ⟨992570, by rfl⟩ : syracuseStep 1323427 = 1985141) B1985141
theorem B1323443 : Blo 1321479 1323443 := bstep (se 1 (by rfl) ⟨992582, by rfl⟩ : syracuseStep 1323443 = 1985165) B1985165
theorem B1487299 : Blo 1321479 1487299 := bstep (se 1 (by rfl) ⟨1115474, by rfl⟩ : syracuseStep 1487299 = 2230949) B2230949
theorem B2511299 : Blo 1321479 2511299 := bstep (se 1 (by rfl) ⟨1883474, by rfl⟩ : syracuseStep 2511299 = 3766949) B3766949
theorem B1323459 : Blo 1321479 1323459 := bstep (se 1 (by rfl) ⟨992594, by rfl⟩ : syracuseStep 1323459 = 1985189) B1985189
theorem B2232785 : Blo 1321479 2232785 := bstep (se 2 (by rfl) ⟨837294, by rfl⟩ : syracuseStep 2232785 = 1674589) B1674589
theorem B1323475 : Blo 1321479 1323475 := bstep (se 1 (by rfl) ⟨992606, by rfl⟩ : syracuseStep 1323475 = 1985213) B1985213
theorem B4461101 : Blo 1321479 4461101 := bstep (se 3 (by rfl) ⟨836456, by rfl⟩ : syracuseStep 4461101 = 1672913) B1672913
theorem B4649521 : Blo 1321479 4649521 := bstep (se 2 (by rfl) ⟨1743570, by rfl⟩ : syracuseStep 4649521 = 3487141) B3487141
theorem B2011729 : Blo 1321479 2011729 := bstep (se 2 (by rfl) ⟨754398, by rfl⟩ : syracuseStep 2011729 = 1508797) B1508797
theorem B2232913 : Blo 1321479 2232913 := bstep (se 2 (by rfl) ⟨837342, by rfl⟩ : syracuseStep 2232913 = 1674685) B1674685
theorem B1487443 : Blo 1321479 1487443 := bstep (se 1 (by rfl) ⟨1115582, by rfl⟩ : syracuseStep 1487443 = 2231165) B2231165
theorem B4461155 : Blo 1321479 4461155 := bstep (se 1 (by rfl) ⟨3345866, by rfl⟩ : syracuseStep 4461155 = 6691733) B6691733
theorem B16937585 : Blo 1321479 16937585 := bstep (se 2 (by rfl) ⟨6351594, by rfl⟩ : syracuseStep 16937585 = 12703189) B12703189
theorem B2232947 : Blo 1321479 2232947 := bstep (se 1 (by rfl) ⟨1674710, by rfl⟩ : syracuseStep 2232947 = 3349421) B3349421
theorem B2118307 : Blo 1321479 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B3347153 : Blo 1321479 3347153 := bstep (se 2 (by rfl) ⟨1255182, by rfl⟩ : syracuseStep 3347153 = 2510365) B2510365
theorem B1487587 : Blo 1321479 1487587 := bstep (se 1 (by rfl) ⟨1115690, by rfl⟩ : syracuseStep 1487587 = 2231381) B2231381
theorem B2511587 : Blo 1321479 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B2233075 : Blo 1321479 2233075 := bstep (se 1 (by rfl) ⟨1674806, by rfl⟩ : syracuseStep 2233075 = 3349613) B3349613
theorem B3347203 : Blo 1321479 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B3576611 : Blo 1321479 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B2823025 : Blo 1321479 2823025 := bstep (se 2 (by rfl) ⟨1058634, by rfl⟩ : syracuseStep 2823025 = 2117269) B2117269
theorem B4461425 : Blo 1321479 4461425 := bstep (se 2 (by rfl) ⟨1673034, by rfl⟩ : syracuseStep 4461425 = 3346069) B3346069
theorem B19059569 : Blo 1321479 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B1487731 : Blo 1321479 1487731 := bstep (se 1 (by rfl) ⟨1115798, by rfl⟩ : syracuseStep 1487731 = 2231597) B2231597
theorem B16094065 : Blo 1321479 16094065 := bstep (se 2 (by rfl) ⟨6035274, by rfl⟩ : syracuseStep 16094065 = 12070549) B12070549
theorem B2233217 : Blo 1321479 2233217 := bstep (se 2 (by rfl) ⟨837456, by rfl⟩ : syracuseStep 2233217 = 1674913) B1674913
theorem B3347345 : Blo 1321479 3347345 := bstep (se 2 (by rfl) ⟨1255254, by rfl⟩ : syracuseStep 3347345 = 2510509) B2510509
theorem B2118563 : Blo 1321479 2118563 := bstep (se 1 (by rfl) ⟨1588922, by rfl⟩ : syracuseStep 2118563 = 3177845) B3177845
theorem B14291909 : Blo 1321479 14291909 := bstep (se 4 (by rfl) ⟨1339866, by rfl⟩ : syracuseStep 14291909 = 2679733) B2679733
theorem B2233345 : Blo 1321479 2233345 := bstep (se 2 (by rfl) ⟨837504, by rfl⟩ : syracuseStep 2233345 = 1675009) B1675009
theorem B1487875 : Blo 1321479 1487875 := bstep (se 1 (by rfl) ⟨1115906, by rfl⟩ : syracuseStep 1487875 = 2231813) B2231813
theorem B2118755 : Blo 1321479 2118755 := bstep (se 1 (by rfl) ⟨1589066, by rfl⟩ : syracuseStep 2118755 = 3178133) B3178133
theorem B1488019 : Blo 1321479 1488019 := bstep (se 1 (by rfl) ⟨1116014, by rfl⟩ : syracuseStep 1488019 = 2232029) B2232029
theorem B1488163 : Blo 1321479 1488163 := bstep (se 1 (by rfl) ⟨1116122, by rfl⟩ : syracuseStep 1488163 = 2232245) B2232245
theorem B3175729 : Blo 1321479 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B17659205 : Blo 1321479 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B4461965 : Blo 1321479 4461965 := bstep (se 3 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 4461965 = 1673237) B1673237
theorem B5019043 : Blo 1321479 5019043 := bstep (se 1 (by rfl) ⟨3764282, by rfl⟩ : syracuseStep 5019043 = 7528565) B7528565
theorem B5649841 : Blo 1321479 5649841 := bstep (se 2 (by rfl) ⟨2118690, by rfl⟩ : syracuseStep 5649841 = 4237381) B4237381
theorem B1488307 : Blo 1321479 1488307 := bstep (se 1 (by rfl) ⟨1116230, by rfl⟩ : syracuseStep 1488307 = 2232461) B2232461
theorem B4462019 : Blo 1321479 4462019 := bstep (se 1 (by rfl) ⟨3346514, by rfl⟩ : syracuseStep 4462019 = 6693029) B6693029
theorem B6690275 : Blo 1321479 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B8467973 : Blo 1321479 8467973 := bstep (se 4 (by rfl) ⟨793872, by rfl⟩ : syracuseStep 8467973 = 1587745) B1587745
theorem B1488451 : Blo 1321479 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B15062597 : Blo 1321479 15062597 := bstep (se 4 (by rfl) ⟨1412118, by rfl⟩ : syracuseStep 15062597 = 2824237) B2824237
theorem B7149197 : Blo 1321479 7149197 := bstep (se 3 (by rfl) ⟨1340474, by rfl⟩ : syracuseStep 7149197 = 2680949) B2680949
theorem B2512529 : Blo 1321479 2512529 := bstep (se 2 (by rfl) ⟨942198, by rfl⟩ : syracuseStep 2512529 = 1884397) B1884397
theorem B3765923 : Blo 1321479 3765923 := bstep (se 1 (by rfl) ⟨2824442, by rfl⟩ : syracuseStep 3765923 = 5648885) B5648885
theorem B4462289 : Blo 1321479 4462289 := bstep (se 2 (by rfl) ⟨1673358, by rfl⟩ : syracuseStep 4462289 = 3346717) B3346717
theorem B3266257 : Blo 1321479 3266257 := bstep (se 2 (by rfl) ⟨1224846, by rfl⟩ : syracuseStep 3266257 = 2449693) B2449693
theorem B1488595 : Blo 1321479 1488595 := bstep (se 1 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 1488595 = 2232893) B2232893
theorem B2545393 : Blo 1321479 2545393 := bstep (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) B1909045
theorem B3815171 : Blo 1321479 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B1488739 : Blo 1321479 1488739 := bstep (se 1 (by rfl) ⟨1116554, by rfl⟩ : syracuseStep 1488739 = 2233109) B2233109
theorem B3348337 : Blo 1321479 3348337 := bstep (se 2 (by rfl) ⟨1255626, by rfl⟩ : syracuseStep 3348337 = 2511253) B2511253
theorem B2119537 : Blo 1321479 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B2824067 : Blo 1321479 2824067 := bstep (se 1 (by rfl) ⟨2118050, by rfl⟩ : syracuseStep 2824067 = 4236101) B4236101
theorem B10049507 : Blo 1321479 10049507 := bstep (se 1 (by rfl) ⟨7537130, by rfl⟩ : syracuseStep 10049507 = 15074261) B15074261
theorem B1488883 : Blo 1321479 1488883 := bstep (se 1 (by rfl) ⟨1116662, by rfl⟩ : syracuseStep 1488883 = 2233325) B2233325
theorem B15071345 : Blo 1321479 15071345 := bstep (se 2 (by rfl) ⟨5651754, by rfl⟩ : syracuseStep 15071345 = 11303509) B11303509
theorem B3348611 : Blo 1321479 3348611 := bstep (se 1 (by rfl) ⟨2511458, by rfl⟩ : syracuseStep 3348611 = 5022917) B5022917
theorem B10172557 : Blo 1321479 10172557 := bstep (se 3 (by rfl) ⟨1907354, by rfl⟩ : syracuseStep 10172557 = 3814709) B3814709
theorem B25426061 : Blo 1321479 25426061 := bstep (se 3 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 25426061 = 9534773) B9534773
theorem B1882273 : Blo 1321479 1882273 := bstep (se 2 (by rfl) ⟨705852, by rfl⟩ : syracuseStep 1882273 = 1411705) B1411705
theorem B6699185 : Blo 1321479 6699185 := bstep (se 2 (by rfl) ⟨2512194, by rfl⟩ : syracuseStep 6699185 = 5024389) B5024389
theorem B9173189 : Blo 1321479 9173189 := bstep (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) B1719973
theorem B4462829 : Blo 1321479 4462829 := bstep (se 3 (by rfl) ⟨836780, by rfl⟩ : syracuseStep 4462829 = 1673561) B1673561
theorem B1882369 : Blo 1321479 1882369 := bstep (se 2 (by rfl) ⟨705888, by rfl⟩ : syracuseStep 1882369 = 1411777) B1411777
theorem B7534853 : Blo 1321479 7534853 := bstep (se 4 (by rfl) ⟨706392, by rfl⟩ : syracuseStep 7534853 = 1412785) B1412785
theorem B6691085 : Blo 1321479 6691085 := bstep (se 3 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 6691085 = 2509157) B2509157
theorem B4462883 : Blo 1321479 4462883 := bstep (se 1 (by rfl) ⟨3347162, by rfl⟩ : syracuseStep 4462883 = 6694325) B6694325
theorem B3348803 : Blo 1321479 3348803 := bstep (se 1 (by rfl) ⟨2511602, by rfl⟩ : syracuseStep 3348803 = 5023205) B5023205
theorem B2824579 : Blo 1321479 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B7526789 : Blo 1321479 7526789 := bstep (se 4 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 7526789 = 1411273) B1411273
theorem B3766733 : Blo 1321479 3766733 := bstep (se 3 (by rfl) ⟨706262, by rfl⟩ : syracuseStep 3766733 = 1412525) B1412525
theorem B4463153 : Blo 1321479 4463153 := bstep (se 2 (by rfl) ⟨1673682, by rfl⟩ : syracuseStep 4463153 = 3347365) B3347365
theorem B3766925 : Blo 1321479 3766925 := bstep (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) B1412597
theorem B1358563 : Blo 1321479 1358563 := bstep (se 1 (by rfl) ⟨1018922, by rfl⟩ : syracuseStep 1358563 = 2037845) B2037845
theorem B1882865 : Blo 1321479 1882865 := bstep (se 2 (by rfl) ⟨706074, by rfl⟩ : syracuseStep 1882865 = 1412149) B1412149
theorem B7535537 : Blo 1321479 7535537 := bstep (se 2 (by rfl) ⟨2825826, by rfl⟩ : syracuseStep 7535537 = 5651653) B5651653
theorem B2382851 : Blo 1321479 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B9042949 : Blo 1321479 9042949 := bstep (se 4 (by rfl) ⟨847776, by rfl⟩ : syracuseStep 9042949 = 1695553) B1695553
theorem B9657413 : Blo 1321479 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B4291661 : Blo 1321479 4291661 := bstep (se 3 (by rfl) ⟨804686, by rfl⟩ : syracuseStep 4291661 = 1609373) B1609373
theorem B4463693 : Blo 1321479 4463693 := bstep (se 3 (by rfl) ⟨836942, by rfl⟩ : syracuseStep 4463693 = 1673885) B1673885
theorem B2825297 : Blo 1321479 2825297 := bstep (se 2 (by rfl) ⟨1059486, by rfl⟩ : syracuseStep 2825297 = 2118973) B2118973
theorem B1588307 : Blo 1321479 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B6438001 : Blo 1321479 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B4463747 : Blo 1321479 4463747 := bstep (se 1 (by rfl) ⟨3347810, by rfl⟩ : syracuseStep 4463747 = 6695621) B6695621
theorem B6782093 : Blo 1321479 6782093 := bstep (se 3 (by rfl) ⟨1271642, by rfl⟩ : syracuseStep 6782093 = 2543285) B2543285
theorem B2792593 : Blo 1321479 2792593 := bstep (se 2 (by rfl) ⟨1047222, by rfl⟩ : syracuseStep 2792593 = 2094445) B2094445
theorem B1588403 : Blo 1321479 1588403 := bstep (se 1 (by rfl) ⟨1191302, by rfl⟩ : syracuseStep 1588403 = 2382605) B2382605
theorem B3349745 : Blo 1321479 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B3349795 : Blo 1321479 3349795 := bstep (se 1 (by rfl) ⟨2512346, by rfl⟩ : syracuseStep 3349795 = 5024693) B5024693
theorem B22609205 : Blo 1321479 22609205 := bstep (se 5 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 22609205 = 2119613) B2119613
theorem B4021571 : Blo 1321479 4021571 := bstep (se 1 (by rfl) ⟨3016178, by rfl⟩ : syracuseStep 4021571 = 6032357) B6032357
theorem B4464017 : Blo 1321479 4464017 := bstep (se 2 (by rfl) ⟨1674006, by rfl⟩ : syracuseStep 4464017 = 3348013) B3348013
theorem B3349937 : Blo 1321479 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B12066317 : Blo 1321479 12066317 := bstep (se 3 (by rfl) ⟨2262434, by rfl⟩ : syracuseStep 12066317 = 4524869) B4524869
theorem B5021261 : Blo 1321479 5021261 := bstep (se 3 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 5021261 = 1882973) B1882973
theorem B1883731 : Blo 1321479 1883731 := bstep (se 1 (by rfl) ⟨1412798, by rfl⟩ : syracuseStep 1883731 = 2825597) B2825597
theorem B3767917 : Blo 1321479 3767917 := bstep (se 3 (by rfl) ⟨706484, by rfl⟩ : syracuseStep 3767917 = 1412969) B1412969
theorem B2973329 : Blo 1321479 2973329 := bstep (se 2 (by rfl) ⟨1114998, by rfl⟩ : syracuseStep 2973329 = 2229997) B2229997
theorem B2973347 : Blo 1321479 2973347 := bstep (se 1 (by rfl) ⟨2230010, by rfl⟩ : syracuseStep 2973347 = 4460021) B4460021
theorem B1883827 : Blo 1321479 1883827 := bstep (se 1 (by rfl) ⟨1412870, by rfl⟩ : syracuseStep 1883827 = 2825741) B2825741
theorem B1982225 : Blo 1321479 1982225 := bstep (se 2 (by rfl) ⟨743334, by rfl⟩ : syracuseStep 1982225 = 1486669) B1486669
theorem B1982243 : Blo 1321479 1982243 := bstep (se 1 (by rfl) ⟨1486682, by rfl⟩ : syracuseStep 1982243 = 2973365) B2973365
theorem B1982273 : Blo 1321479 1982273 := bstep (se 2 (by rfl) ⟨743352, by rfl⟩ : syracuseStep 1982273 = 1486705) B1486705
theorem B4235075 : Blo 1321479 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B7151429 : Blo 1321479 7151429 := bstep (se 4 (by rfl) ⟨670446, by rfl⟩ : syracuseStep 7151429 = 1340893) B1340893
theorem B1982291 : Blo 1321479 1982291 := bstep (se 1 (by rfl) ⟨1486718, by rfl⟩ : syracuseStep 1982291 = 2973437) B2973437
theorem B2826083 : Blo 1321479 2826083 := bstep (se 1 (by rfl) ⟨2119562, by rfl⟩ : syracuseStep 2826083 = 4239125) B4239125
theorem B1982321 : Blo 1321479 1982321 := bstep (se 2 (by rfl) ⟨743370, by rfl⟩ : syracuseStep 1982321 = 1486741) B1486741
theorem B1982339 : Blo 1321479 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B28999565 : Blo 1321479 28999565 := bstep (se 3 (by rfl) ⟨5437418, by rfl⟩ : syracuseStep 28999565 = 10874837) B10874837
theorem B11304845 : Blo 1321479 11304845 := bstep (se 3 (by rfl) ⟨2119658, by rfl⟩ : syracuseStep 11304845 = 4239317) B4239317
theorem B1982369 : Blo 1321479 1982369 := bstep (se 2 (by rfl) ⟨743388, by rfl⟩ : syracuseStep 1982369 = 1486777) B1486777
theorem B4464557 : Blo 1321479 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B2973617 : Blo 1321479 2973617 := bstep (se 2 (by rfl) ⟨1115106, by rfl⟩ : syracuseStep 2973617 = 2230213) B2230213
theorem B1982387 : Blo 1321479 1982387 := bstep (se 1 (by rfl) ⟨1486790, by rfl⟩ : syracuseStep 1982387 = 2973581) B2973581
theorem B2973635 : Blo 1321479 2973635 := bstep (se 1 (by rfl) ⟨2230226, by rfl⟩ : syracuseStep 2973635 = 4460453) B4460453
theorem B1982417 : Blo 1321479 1982417 := bstep (se 2 (by rfl) ⟨743406, by rfl⟩ : syracuseStep 1982417 = 1486813) B1486813
theorem B1982435 : Blo 1321479 1982435 := bstep (se 1 (by rfl) ⟨1486826, by rfl⟩ : syracuseStep 1982435 = 2973653) B2973653
theorem B4464611 : Blo 1321479 4464611 := bstep (se 1 (by rfl) ⟨3348458, by rfl⟩ : syracuseStep 4464611 = 6696917) B6696917
theorem B2973707 : Blo 1321479 2973707 := bstep (se 1 (by rfl) ⟨2230280, by rfl⟩ : syracuseStep 2973707 = 4460561) B4460561
theorem B1982489 : Blo 1321479 1982489 := bstep (se 2 (by rfl) ⟨743433, by rfl⟩ : syracuseStep 1982489 = 1486867) B1486867
theorem B5021747 : Blo 1321479 5021747 := bstep (se 1 (by rfl) ⟨3766310, by rfl⟩ : syracuseStep 5021747 = 7532621) B7532621
theorem B2973761 : Blo 1321479 2973761 := bstep (se 2 (by rfl) ⟨1115160, by rfl⟩ : syracuseStep 2973761 = 2230321) B2230321
theorem B5652611 : Blo 1321479 5652611 := bstep (se 1 (by rfl) ⟨4239458, by rfl⟩ : syracuseStep 5652611 = 8478917) B8478917
theorem B1982603 : Blo 1321479 1982603 := bstep (se 1 (by rfl) ⟨1486952, by rfl⟩ : syracuseStep 1982603 = 2973905) B2973905
theorem B1982615 : Blo 1321479 1982615 := bstep (se 1 (by rfl) ⟨1486961, by rfl⟩ : syracuseStep 1982615 = 2973923) B2973923
theorem B11444429 : Blo 1321479 11444429 := bstep (se 3 (by rfl) ⟨2145830, by rfl⟩ : syracuseStep 11444429 = 4291661) B4291661
theorem B1982681 : Blo 1321479 1982681 := bstep (se 2 (by rfl) ⟨743505, by rfl⟩ : syracuseStep 1982681 = 1487011) B1487011
theorem B4235485 : Blo 1321479 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B2973977 : Blo 1321479 2973977 := bstep (se 2 (by rfl) ⟨1115241, by rfl⟩ : syracuseStep 2973977 = 2230483) B2230483
theorem B1982795 : Blo 1321479 1982795 := bstep (se 1 (by rfl) ⟨1487096, by rfl⟩ : syracuseStep 1982795 = 2974193) B2974193
theorem B1982807 : Blo 1321479 1982807 := bstep (se 1 (by rfl) ⟨1487105, by rfl⟩ : syracuseStep 1982807 = 2974211) B2974211
theorem B4464989 : Blo 1321479 4464989 := bstep (se 3 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 4464989 = 1674371) B1674371
theorem B19333475 : Blo 1321479 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B2974067 : Blo 1321479 2974067 := bstep (se 1 (by rfl) ⟨2230550, by rfl⟩ : syracuseStep 2974067 = 4461101) B4461101
theorem B17170805 : Blo 1321479 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B2974103 : Blo 1321479 2974103 := bstep (se 1 (by rfl) ⟨2230577, by rfl⟩ : syracuseStep 2974103 = 4461155) B4461155
theorem B1982873 : Blo 1321479 1982873 := bstep (se 2 (by rfl) ⟨743577, by rfl⟩ : syracuseStep 1982873 = 1487155) B1487155
theorem B4235741 : Blo 1321479 4235741 := bstep (se 3 (by rfl) ⟨794201, by rfl⟩ : syracuseStep 4235741 = 1588403) B1588403
theorem B1982987 : Blo 1321479 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B24461837 : Blo 1321479 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B1982999 : Blo 1321479 1982999 := bstep (se 1 (by rfl) ⟨1487249, by rfl⟩ : syracuseStep 1982999 = 2974499) B2974499
theorem B2384407 : Blo 1321479 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B2974283 : Blo 1321479 2974283 := bstep (se 1 (by rfl) ⟨2230712, by rfl⟩ : syracuseStep 2974283 = 4461425) B4461425
theorem B12706379 : Blo 1321479 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B1983065 : Blo 1321479 1983065 := bstep (se 2 (by rfl) ⟨743649, by rfl⟩ : syracuseStep 1983065 = 1487299) B1487299
theorem B2974337 : Blo 1321479 2974337 := bstep (se 2 (by rfl) ⟨1115376, by rfl⟩ : syracuseStep 2974337 = 2230753) B2230753
theorem B9527939 : Blo 1321479 9527939 := bstep (se 1 (by rfl) ⟨7145954, by rfl⟩ : syracuseStep 9527939 = 14291909) B14291909
theorem B1983179 : Blo 1321479 1983179 := bstep (se 1 (by rfl) ⟨1487384, by rfl⟩ : syracuseStep 1983179 = 2974769) B2974769
theorem B1983191 : Blo 1321479 1983191 := bstep (se 1 (by rfl) ⟨1487393, by rfl⟩ : syracuseStep 1983191 = 2974787) B2974787
theorem B1508107 : Blo 1321479 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B1983257 : Blo 1321479 1983257 := bstep (se 2 (by rfl) ⟨743721, by rfl⟩ : syracuseStep 1983257 = 1487443) B1487443
theorem B6693677 : Blo 1321479 6693677 := bstep (se 3 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 6693677 = 2510129) B2510129
theorem B2974553 : Blo 1321479 2974553 := bstep (se 2 (by rfl) ⟨1115457, by rfl⟩ : syracuseStep 2974553 = 2230915) B2230915
theorem B11772803 : Blo 1321479 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B1983371 : Blo 1321479 1983371 := bstep (se 1 (by rfl) ⟨1487528, by rfl⟩ : syracuseStep 1983371 = 2975057) B2975057
theorem B1983383 : Blo 1321479 1983383 := bstep (se 1 (by rfl) ⟨1487537, by rfl⟩ : syracuseStep 1983383 = 2975075) B2975075
theorem B3015577 : Blo 1321479 3015577 := bstep (se 2 (by rfl) ⟨1130841, by rfl⟩ : syracuseStep 3015577 = 2261683) B2261683
theorem B2974643 : Blo 1321479 2974643 := bstep (se 1 (by rfl) ⟨2230982, by rfl⟩ : syracuseStep 2974643 = 4461965) B4461965
theorem B2974679 : Blo 1321479 2974679 := bstep (se 1 (by rfl) ⟨2231009, by rfl⟩ : syracuseStep 2974679 = 4462019) B4462019
theorem B1811417 : Blo 1321479 1811417 := bstep (se 2 (by rfl) ⟨679281, by rfl⟩ : syracuseStep 1811417 = 1358563) B1358563
theorem B1983449 : Blo 1321479 1983449 := bstep (se 2 (by rfl) ⟨743793, by rfl⟩ : syracuseStep 1983449 = 1487587) B1487587
theorem B5645315 : Blo 1321479 5645315 := bstep (se 1 (by rfl) ⟨4233986, by rfl⟩ : syracuseStep 5645315 = 8467973) B8467973
theorem B1983563 : Blo 1321479 1983563 := bstep (se 1 (by rfl) ⟨1487672, by rfl⟩ : syracuseStep 1983563 = 2975345) B2975345
theorem B1983575 : Blo 1321479 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B2974859 : Blo 1321479 2974859 := bstep (se 1 (by rfl) ⟨2231144, by rfl⟩ : syracuseStep 2974859 = 4462289) B4462289
theorem B1983641 : Blo 1321479 1983641 := bstep (se 2 (by rfl) ⟨743865, by rfl⟩ : syracuseStep 1983641 = 1487731) B1487731
theorem B2974913 : Blo 1321479 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B1983755 : Blo 1321479 1983755 := bstep (se 1 (by rfl) ⟨1487816, by rfl⟩ : syracuseStep 1983755 = 2975633) B2975633
theorem B1983767 : Blo 1321479 1983767 := bstep (se 1 (by rfl) ⟨1487825, by rfl⟩ : syracuseStep 1983767 = 2975651) B2975651
theorem B1983833 : Blo 1321479 1983833 := bstep (se 2 (by rfl) ⟨743937, by rfl⟩ : syracuseStep 1983833 = 1487875) B1487875
theorem B2975129 : Blo 1321479 2975129 := bstep (se 2 (by rfl) ⟨1115673, by rfl⟩ : syracuseStep 2975129 = 2231347) B2231347
theorem B16950707 : Blo 1321479 16950707 := bstep (se 1 (by rfl) ⟨12713030, by rfl⟩ : syracuseStep 16950707 = 25426061) B25426061
theorem B1983947 : Blo 1321479 1983947 := bstep (se 1 (by rfl) ⟨1487960, by rfl⟩ : syracuseStep 1983947 = 2975921) B2975921
theorem B4466123 : Blo 1321479 4466123 := bstep (se 1 (by rfl) ⟨3349592, by rfl⟩ : syracuseStep 4466123 = 6699185) B6699185
theorem B1983959 : Blo 1321479 1983959 := bstep (se 1 (by rfl) ⟨1487969, by rfl⟩ : syracuseStep 1983959 = 2975939) B2975939
theorem B16942553 : Blo 1321479 16942553 := bstep (se 2 (by rfl) ⟨6353457, by rfl⟩ : syracuseStep 16942553 = 12706915) B12706915
theorem B2975219 : Blo 1321479 2975219 := bstep (se 1 (by rfl) ⟨2231414, by rfl⟩ : syracuseStep 2975219 = 4462829) B4462829
theorem B5023235 : Blo 1321479 5023235 := bstep (se 1 (by rfl) ⟨3767426, by rfl⟩ : syracuseStep 5023235 = 7534853) B7534853
theorem B4523543 : Blo 1321479 4523543 := bstep (se 1 (by rfl) ⟨3392657, by rfl⟩ : syracuseStep 4523543 = 6785315) B6785315
theorem B2975255 : Blo 1321479 2975255 := bstep (se 1 (by rfl) ⟨2231441, by rfl⟩ : syracuseStep 2975255 = 4462883) B4462883
theorem B1984025 : Blo 1321479 1984025 := bstep (se 2 (by rfl) ⟨744009, by rfl⟩ : syracuseStep 1984025 = 1488019) B1488019
theorem B19056221 : Blo 1321479 19056221 := bstep (se 3 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 19056221 = 7146083) B7146083
theorem B1984139 : Blo 1321479 1984139 := bstep (se 1 (by rfl) ⟨1488104, by rfl⟩ : syracuseStep 1984139 = 2976209) B2976209
theorem B1984151 : Blo 1321479 1984151 := bstep (se 1 (by rfl) ⟨1488113, by rfl⟩ : syracuseStep 1984151 = 2976227) B2976227
theorem B2975435 : Blo 1321479 2975435 := bstep (se 1 (by rfl) ⟨2231576, by rfl⟩ : syracuseStep 2975435 = 4463153) B4463153
theorem B10045133 : Blo 1321479 10045133 := bstep (se 3 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 10045133 = 3766925) B3766925
theorem B1984217 : Blo 1321479 1984217 := bstep (se 2 (by rfl) ⟨744081, by rfl⟩ : syracuseStep 1984217 = 1488163) B1488163
theorem B4466393 : Blo 1321479 4466393 := bstep (se 2 (by rfl) ⟨1674897, by rfl⟩ : syracuseStep 4466393 = 3349795) B3349795
theorem B2975489 : Blo 1321479 2975489 := bstep (se 2 (by rfl) ⟨1115808, by rfl⟩ : syracuseStep 2975489 = 2231617) B2231617
theorem B1984331 : Blo 1321479 1984331 := bstep (se 1 (by rfl) ⟨1488248, by rfl⟩ : syracuseStep 1984331 = 2976497) B2976497
theorem B1984343 : Blo 1321479 1984343 := bstep (se 1 (by rfl) ⟨1488257, by rfl⟩ : syracuseStep 1984343 = 2976515) B2976515
theorem B2230105 : Blo 1321479 2230105 := bstep (se 2 (by rfl) ⟨836289, by rfl⟩ : syracuseStep 2230105 = 1672579) B1672579
theorem B10315613 : Blo 1321479 10315613 := bstep (se 3 (by rfl) ⟨1934177, by rfl⟩ : syracuseStep 10315613 = 3868355) B3868355
theorem B1984409 : Blo 1321479 1984409 := bstep (se 2 (by rfl) ⟨744153, by rfl⟩ : syracuseStep 1984409 = 1488307) B1488307
theorem B9529265 : Blo 1321479 9529265 := bstep (se 2 (by rfl) ⟨3573474, by rfl⟩ : syracuseStep 9529265 = 7146949) B7146949
theorem B5023691 : Blo 1321479 5023691 := bstep (se 1 (by rfl) ⟨3767768, by rfl⟩ : syracuseStep 5023691 = 7535537) B7535537
theorem B2975705 : Blo 1321479 2975705 := bstep (se 2 (by rfl) ⟨1115889, by rfl⟩ : syracuseStep 2975705 = 2231779) B2231779
theorem B1673227 : Blo 1321479 1673227 := bstep (se 1 (by rfl) ⟨1254920, by rfl⟩ : syracuseStep 1673227 = 2509841) B2509841
theorem B1984523 : Blo 1321479 1984523 := bstep (se 1 (by rfl) ⟨1488392, by rfl⟩ : syracuseStep 1984523 = 2976785) B2976785
theorem B2508823 : Blo 1321479 2508823 := bstep (se 1 (by rfl) ⟨1881617, by rfl⟩ : syracuseStep 2508823 = 3763235) B3763235
theorem B1984535 : Blo 1321479 1984535 := bstep (se 1 (by rfl) ⟨1488401, by rfl⟩ : syracuseStep 1984535 = 2976803) B2976803
theorem B3573811 : Blo 1321479 3573811 := bstep (se 1 (by rfl) ⟨2680358, by rfl⟩ : syracuseStep 3573811 = 5360717) B5360717
theorem B2975795 : Blo 1321479 2975795 := bstep (se 1 (by rfl) ⟨2231846, by rfl⟩ : syracuseStep 2975795 = 4463693) B4463693
theorem B2975831 : Blo 1321479 2975831 := bstep (se 1 (by rfl) ⟨2231873, by rfl⟩ : syracuseStep 2975831 = 4463747) B4463747
theorem B1984601 : Blo 1321479 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B5023889 : Blo 1321479 5023889 := bstep (se 2 (by rfl) ⟨1883958, by rfl⟩ : syracuseStep 5023889 = 3767917) B3767917
theorem B10045619 : Blo 1321479 10045619 := bstep (se 1 (by rfl) ⟨7534214, by rfl⟩ : syracuseStep 10045619 = 15068429) B15068429
theorem B3573953 : Blo 1321479 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B1984715 : Blo 1321479 1984715 := bstep (se 1 (by rfl) ⟨1488536, by rfl⟩ : syracuseStep 1984715 = 2977073) B2977073
theorem B2681047 : Blo 1321479 2681047 := bstep (se 1 (by rfl) ⟨2010785, by rfl⟩ : syracuseStep 2681047 = 4021571) B4021571
theorem B1984727 : Blo 1321479 1984727 := bstep (se 1 (by rfl) ⟨1488545, by rfl⟩ : syracuseStep 1984727 = 2977091) B2977091
theorem B2976011 : Blo 1321479 2976011 := bstep (se 1 (by rfl) ⟨2232008, by rfl⟩ : syracuseStep 2976011 = 4464017) B4464017
theorem B1984793 : Blo 1321479 1984793 := bstep (se 2 (by rfl) ⟨744297, by rfl⟩ : syracuseStep 1984793 = 1488595) B1488595
theorem B4352321 : Blo 1321479 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B2976065 : Blo 1321479 2976065 := bstep (se 2 (by rfl) ⟨1116024, by rfl⟩ : syracuseStep 2976065 = 2232049) B2232049
theorem B3393857 : Blo 1321479 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B1984907 : Blo 1321479 1984907 := bstep (se 1 (by rfl) ⟨1488680, by rfl⟩ : syracuseStep 1984907 = 2977361) B2977361
theorem B2230679 : Blo 1321479 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B2263447 : Blo 1321479 2263447 := bstep (se 1 (by rfl) ⟨1697585, by rfl⟩ : syracuseStep 2263447 = 3395171) B3395171
theorem B1984919 : Blo 1321479 1984919 := bstep (se 1 (by rfl) ⟨1488689, by rfl⟩ : syracuseStep 1984919 = 2977379) B2977379
theorem B1984985 : Blo 1321479 1984985 := bstep (se 2 (by rfl) ⟨744369, by rfl⟩ : syracuseStep 1984985 = 1488739) B1488739
theorem B1321483 : Blo 1321479 1321483 := bstep (se 1 (by rfl) ⟨991112, by rfl⟩ : syracuseStep 1321483 = 1982225) B1982225
theorem B1321495 : Blo 1321479 1321495 := bstep (se 1 (by rfl) ⟨991121, by rfl⟩ : syracuseStep 1321495 = 1982243) B1982243
theorem B2230807 : Blo 1321479 2230807 := bstep (se 1 (by rfl) ⟨1673105, by rfl⟩ : syracuseStep 2230807 = 3346211) B3346211
theorem B2976281 : Blo 1321479 2976281 := bstep (se 2 (by rfl) ⟨1116105, by rfl⟩ : syracuseStep 2976281 = 2232211) B2232211
theorem B1321515 : Blo 1321479 1321515 := bstep (se 1 (by rfl) ⟨991136, by rfl⟩ : syracuseStep 1321515 = 1982273) B1982273
theorem B1321527 : Blo 1321479 1321527 := bstep (se 1 (by rfl) ⟨991145, by rfl⟩ : syracuseStep 1321527 = 1982291) B1982291
theorem B1321547 : Blo 1321479 1321547 := bstep (se 1 (by rfl) ⟨991160, by rfl⟩ : syracuseStep 1321547 = 1982321) B1982321
theorem B1985099 : Blo 1321479 1985099 := bstep (se 1 (by rfl) ⟨1488824, by rfl⟩ : syracuseStep 1985099 = 2977649) B2977649
theorem B1321559 : Blo 1321479 1321559 := bstep (se 1 (by rfl) ⟨991169, by rfl⟩ : syracuseStep 1321559 = 1982339) B1982339
theorem B1985111 : Blo 1321479 1985111 := bstep (se 1 (by rfl) ⟨1488833, by rfl⟩ : syracuseStep 1985111 = 2977667) B2977667
theorem B1321579 : Blo 1321479 1321579 := bstep (se 1 (by rfl) ⟨991184, by rfl⟩ : syracuseStep 1321579 = 1982369) B1982369
theorem B2976371 : Blo 1321479 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1321591 : Blo 1321479 1321591 := bstep (se 1 (by rfl) ⟨991193, by rfl⟩ : syracuseStep 1321591 = 1982387) B1982387
theorem B1321611 : Blo 1321479 1321611 := bstep (se 1 (by rfl) ⟨991208, by rfl⟩ : syracuseStep 1321611 = 1982417) B1982417
theorem B3345047 : Blo 1321479 3345047 := bstep (se 1 (by rfl) ⟨2508785, by rfl⟩ : syracuseStep 3345047 = 5017571) B5017571
theorem B1321623 : Blo 1321479 1321623 := bstep (se 1 (by rfl) ⟨991217, by rfl⟩ : syracuseStep 1321623 = 1982435) B1982435
theorem B2976407 : Blo 1321479 2976407 := bstep (se 1 (by rfl) ⟨2232305, by rfl⟩ : syracuseStep 2976407 = 4464611) B4464611
theorem B1985177 : Blo 1321479 1985177 := bstep (se 2 (by rfl) ⟨744441, by rfl⟩ : syracuseStep 1985177 = 1488883) B1488883
theorem B1321643 : Blo 1321479 1321643 := bstep (se 1 (by rfl) ⟨991232, by rfl⟩ : syracuseStep 1321643 = 1982465) B1982465
theorem B1321655 : Blo 1321479 1321655 := bstep (se 1 (by rfl) ⟨991241, by rfl⟩ : syracuseStep 1321655 = 1982483) B1982483
theorem B41863877 : Blo 1321479 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B1321675 : Blo 1321479 1321675 := bstep (se 1 (by rfl) ⟨991256, by rfl⟩ : syracuseStep 1321675 = 1982513) B1982513
theorem B1321687 : Blo 1321479 1321687 := bstep (se 1 (by rfl) ⟨991265, by rfl⟩ : syracuseStep 1321687 = 1982531) B1982531
theorem B1321707 : Blo 1321479 1321707 := bstep (se 1 (by rfl) ⟨991280, by rfl⟩ : syracuseStep 1321707 = 1982561) B1982561
theorem B1321719 : Blo 1321479 1321719 := bstep (se 1 (by rfl) ⟨991289, by rfl⟩ : syracuseStep 1321719 = 1982579) B1982579
theorem B1321739 : Blo 1321479 1321739 := bstep (se 1 (by rfl) ⟨991304, by rfl⟩ : syracuseStep 1321739 = 1982609) B1982609
theorem B1321751 : Blo 1321479 1321751 := bstep (se 1 (by rfl) ⟨991313, by rfl⟩ : syracuseStep 1321751 = 1982627) B1982627
theorem B1321771 : Blo 1321479 1321771 := bstep (se 1 (by rfl) ⟨991328, by rfl⟩ : syracuseStep 1321771 = 1982657) B1982657
theorem B1321783 : Blo 1321479 1321783 := bstep (se 1 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 1321783 = 1982675) B1982675
theorem B7146305 : Blo 1321479 7146305 := bstep (se 2 (by rfl) ⟨2679864, by rfl⟩ : syracuseStep 7146305 = 5359729) B5359729
theorem B1321803 : Blo 1321479 1321803 := bstep (se 1 (by rfl) ⟨991352, by rfl⟩ : syracuseStep 1321803 = 1982705) B1982705
theorem B2509643 : Blo 1321479 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B2976587 : Blo 1321479 2976587 := bstep (se 1 (by rfl) ⟨2232440, by rfl⟩ : syracuseStep 2976587 = 4464881) B4464881
theorem B1321815 : Blo 1321479 1321815 := bstep (se 1 (by rfl) ⟨991361, by rfl⟩ : syracuseStep 1321815 = 1982723) B1982723
theorem B1321835 : Blo 1321479 1321835 := bstep (se 1 (by rfl) ⟨991376, by rfl⟩ : syracuseStep 1321835 = 1982753) B1982753
theorem B2861939 : Blo 1321479 2861939 := bstep (se 1 (by rfl) ⟨2146454, by rfl⟩ : syracuseStep 2861939 = 4292909) B4292909
theorem B1321847 : Blo 1321479 1321847 := bstep (se 1 (by rfl) ⟨991385, by rfl⟩ : syracuseStep 1321847 = 1982771) B1982771
theorem B2509697 : Blo 1321479 2509697 := bstep (se 2 (by rfl) ⟨941136, by rfl⟩ : syracuseStep 2509697 = 1882273) B1882273
theorem B2976641 : Blo 1321479 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B1321867 : Blo 1321479 1321867 := bstep (se 1 (by rfl) ⟨991400, by rfl⟩ : syracuseStep 1321867 = 1982801) B1982801
theorem B6351767 : Blo 1321479 6351767 := bstep (se 1 (by rfl) ⟨4763825, by rfl⟩ : syracuseStep 6351767 = 9527651) B9527651
theorem B1321879 : Blo 1321479 1321879 := bstep (se 1 (by rfl) ⟨991409, by rfl⟩ : syracuseStep 1321879 = 1982819) B1982819
theorem B5024663 : Blo 1321479 5024663 := bstep (se 1 (by rfl) ⟨3768497, by rfl⟩ : syracuseStep 5024663 = 7536995) B7536995
theorem B1321899 : Blo 1321479 1321899 := bstep (se 1 (by rfl) ⟨991424, by rfl⟩ : syracuseStep 1321899 = 1982849) B1982849
theorem B1321911 : Blo 1321479 1321911 := bstep (se 1 (by rfl) ⟨991433, by rfl⟩ : syracuseStep 1321911 = 1982867) B1982867
theorem B1321931 : Blo 1321479 1321931 := bstep (se 1 (by rfl) ⟨991448, by rfl⟩ : syracuseStep 1321931 = 1982897) B1982897
theorem B1321943 : Blo 1321479 1321943 := bstep (se 1 (by rfl) ⟨991457, by rfl⟩ : syracuseStep 1321943 = 1982915) B1982915
theorem B1674199 : Blo 1321479 1674199 := bstep (se 1 (by rfl) ⟨1255649, by rfl⟩ : syracuseStep 1674199 = 2511299) B2511299
theorem B7531481 : Blo 1321479 7531481 := bstep (se 2 (by rfl) ⟨2824305, by rfl⟩ : syracuseStep 7531481 = 5648611) B5648611
theorem B1321963 : Blo 1321479 1321963 := bstep (se 1 (by rfl) ⟨991472, by rfl⟩ : syracuseStep 1321963 = 1982945) B1982945
theorem B1321975 : Blo 1321479 1321975 := bstep (se 1 (by rfl) ⟨991481, by rfl⟩ : syracuseStep 1321975 = 1982963) B1982963
theorem B1321995 : Blo 1321479 1321995 := bstep (se 1 (by rfl) ⟨991496, by rfl⟩ : syracuseStep 1321995 = 1982993) B1982993
theorem B1322007 : Blo 1321479 1322007 := bstep (se 1 (by rfl) ⟨991505, by rfl⟩ : syracuseStep 1322007 = 1983011) B1983011
theorem B1322027 : Blo 1321479 1322027 := bstep (se 1 (by rfl) ⟨991520, by rfl⟩ : syracuseStep 1322027 = 1983041) B1983041
theorem B1322039 : Blo 1321479 1322039 := bstep (se 1 (by rfl) ⟨991529, by rfl⟩ : syracuseStep 1322039 = 1983059) B1983059
theorem B3574849 : Blo 1321479 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B11291723 : Blo 1321479 11291723 := bstep (se 1 (by rfl) ⟨8468792, by rfl⟩ : syracuseStep 11291723 = 16937585) B16937585
theorem B1322059 : Blo 1321479 1322059 := bstep (se 1 (by rfl) ⟨991544, by rfl⟩ : syracuseStep 1322059 = 1983089) B1983089
theorem B1322071 : Blo 1321479 1322071 := bstep (se 1 (by rfl) ⟨991553, by rfl⟩ : syracuseStep 1322071 = 1983107) B1983107
theorem B2976857 : Blo 1321479 2976857 := bstep (se 2 (by rfl) ⟨1116321, by rfl⟩ : syracuseStep 2976857 = 2232643) B2232643
theorem B5024861 : Blo 1321479 5024861 := bstep (se 3 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 5024861 = 1884323) B1884323
theorem B1322091 : Blo 1321479 1322091 := bstep (se 1 (by rfl) ⟨991568, by rfl⟩ : syracuseStep 1322091 = 1983137) B1983137
theorem B1322103 : Blo 1321479 1322103 := bstep (se 1 (by rfl) ⟨991577, by rfl⟩ : syracuseStep 1322103 = 1983155) B1983155
theorem B1322123 : Blo 1321479 1322123 := bstep (se 1 (by rfl) ⟨991592, by rfl⟩ : syracuseStep 1322123 = 1983185) B1983185
theorem B2231435 : Blo 1321479 2231435 := bstep (se 1 (by rfl) ⟨1673576, by rfl⟩ : syracuseStep 2231435 = 3347153) B3347153
theorem B1322135 : Blo 1321479 1322135 := bstep (se 1 (by rfl) ⟨991601, by rfl⟩ : syracuseStep 1322135 = 1983203) B1983203
theorem B1322155 : Blo 1321479 1322155 := bstep (se 1 (by rfl) ⟨991616, by rfl⟩ : syracuseStep 1322155 = 1983233) B1983233
theorem B2976947 : Blo 1321479 2976947 := bstep (se 1 (by rfl) ⟨2232710, by rfl⟩ : syracuseStep 2976947 = 4465421) B4465421
theorem B1322167 : Blo 1321479 1322167 := bstep (se 1 (by rfl) ⟨991625, by rfl⟩ : syracuseStep 1322167 = 1983251) B1983251
theorem B5647553 : Blo 1321479 5647553 := bstep (se 2 (by rfl) ⟨2117832, by rfl⟩ : syracuseStep 5647553 = 4235665) B4235665
theorem B1322187 : Blo 1321479 1322187 := bstep (se 1 (by rfl) ⟨991640, by rfl⟩ : syracuseStep 1322187 = 1983281) B1983281
theorem B1322199 : Blo 1321479 1322199 := bstep (se 1 (by rfl) ⟨991649, by rfl⟩ : syracuseStep 1322199 = 1983299) B1983299
theorem B2976983 : Blo 1321479 2976983 := bstep (se 1 (by rfl) ⟨2232737, by rfl⟩ : syracuseStep 2976983 = 4465475) B4465475
theorem B3763417 : Blo 1321479 3763417 := bstep (se 2 (by rfl) ⟨1411281, by rfl⟩ : syracuseStep 3763417 = 2822563) B2822563
theorem B1322219 : Blo 1321479 1322219 := bstep (se 1 (by rfl) ⟨991664, by rfl⟩ : syracuseStep 1322219 = 1983329) B1983329
theorem B1322231 : Blo 1321479 1322231 := bstep (se 1 (by rfl) ⟨991673, by rfl⟩ : syracuseStep 1322231 = 1983347) B1983347
theorem B1322251 : Blo 1321479 1322251 := bstep (se 1 (by rfl) ⟨991688, by rfl⟩ : syracuseStep 1322251 = 1983377) B1983377
theorem B2231563 : Blo 1321479 2231563 := bstep (se 1 (by rfl) ⟨1673672, by rfl⟩ : syracuseStep 2231563 = 3347345) B3347345
theorem B1322263 : Blo 1321479 1322263 := bstep (se 1 (by rfl) ⟨991697, by rfl⟩ : syracuseStep 1322263 = 1983395) B1983395
theorem B1412375 : Blo 1321479 1412375 := bstep (se 1 (by rfl) ⟨1059281, by rfl⟩ : syracuseStep 1412375 = 2118563) B2118563
theorem B1322283 : Blo 1321479 1322283 := bstep (se 1 (by rfl) ⟨991712, by rfl⟩ : syracuseStep 1322283 = 1983425) B1983425
theorem B1322295 : Blo 1321479 1322295 := bstep (se 1 (by rfl) ⟨991721, by rfl⟩ : syracuseStep 1322295 = 1983443) B1983443
theorem B1322315 : Blo 1321479 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B1322327 : Blo 1321479 1322327 := bstep (se 1 (by rfl) ⟨991745, by rfl⟩ : syracuseStep 1322327 = 1983491) B1983491
theorem B1322347 : Blo 1321479 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B1322359 : Blo 1321479 1322359 := bstep (se 1 (by rfl) ⟨991769, by rfl⟩ : syracuseStep 1322359 = 1983539) B1983539
theorem B1322379 : Blo 1321479 1322379 := bstep (se 1 (by rfl) ⟨991784, by rfl⟩ : syracuseStep 1322379 = 1983569) B1983569
theorem B2977163 : Blo 1321479 2977163 := bstep (se 1 (by rfl) ⟨2232872, by rfl⟩ : syracuseStep 2977163 = 4465745) B4465745
theorem B1322391 : Blo 1321479 1322391 := bstep (se 1 (by rfl) ⟨991793, by rfl⟩ : syracuseStep 1322391 = 1983587) B1983587
theorem B2231705 : Blo 1321479 2231705 := bstep (se 2 (by rfl) ⟨836889, by rfl⟩ : syracuseStep 2231705 = 1673779) B1673779
theorem B1322411 : Blo 1321479 1322411 := bstep (se 1 (by rfl) ⟨991808, by rfl⟩ : syracuseStep 1322411 = 1983617) B1983617
theorem B1322423 : Blo 1321479 1322423 := bstep (se 1 (by rfl) ⟨991817, by rfl⟩ : syracuseStep 1322423 = 1983635) B1983635
theorem B3345857 : Blo 1321479 3345857 := bstep (se 2 (by rfl) ⟨1254696, by rfl⟩ : syracuseStep 3345857 = 2509393) B2509393
theorem B2682305 : Blo 1321479 2682305 := bstep (se 2 (by rfl) ⟨1005864, by rfl⟩ : syracuseStep 2682305 = 2011729) B2011729
theorem B2977217 : Blo 1321479 2977217 := bstep (se 2 (by rfl) ⟨1116456, by rfl⟩ : syracuseStep 2977217 = 2232913) B2232913
theorem B1322443 : Blo 1321479 1322443 := bstep (se 1 (by rfl) ⟨991832, by rfl⟩ : syracuseStep 1322443 = 1983665) B1983665
theorem B1322455 : Blo 1321479 1322455 := bstep (se 1 (by rfl) ⟨991841, by rfl⟩ : syracuseStep 1322455 = 1983683) B1983683
theorem B1322475 : Blo 1321479 1322475 := bstep (se 1 (by rfl) ⟨991856, by rfl⟩ : syracuseStep 1322475 = 1983713) B1983713
theorem B1322487 : Blo 1321479 1322487 := bstep (se 1 (by rfl) ⟨991865, by rfl⟩ : syracuseStep 1322487 = 1983731) B1983731
theorem B1322507 : Blo 1321479 1322507 := bstep (se 1 (by rfl) ⟨991880, by rfl⟩ : syracuseStep 1322507 = 1983761) B1983761
theorem B1322519 : Blo 1321479 1322519 := bstep (se 1 (by rfl) ⟨991889, by rfl⟩ : syracuseStep 1322519 = 1983779) B1983779
theorem B2231833 : Blo 1321479 2231833 := bstep (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) B1673875
theorem B1322539 : Blo 1321479 1322539 := bstep (se 1 (by rfl) ⟨991904, by rfl⟩ : syracuseStep 1322539 = 1983809) B1983809
theorem B1322551 : Blo 1321479 1322551 := bstep (se 1 (by rfl) ⟨991913, by rfl⟩ : syracuseStep 1322551 = 1983827) B1983827
theorem B1322571 : Blo 1321479 1322571 := bstep (se 1 (by rfl) ⟨991928, by rfl⟩ : syracuseStep 1322571 = 1983857) B1983857
theorem B1322583 : Blo 1321479 1322583 := bstep (se 1 (by rfl) ⟨991937, by rfl⟩ : syracuseStep 1322583 = 1983875) B1983875
theorem B10047077 : Blo 1321479 10047077 := bstep (se 4 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 10047077 = 1883827) B1883827
theorem B1322603 : Blo 1321479 1322603 := bstep (se 1 (by rfl) ⟨991952, by rfl⟩ : syracuseStep 1322603 = 1983905) B1983905
theorem B1322615 : Blo 1321479 1322615 := bstep (se 1 (by rfl) ⟨991961, by rfl⟩ : syracuseStep 1322615 = 1983923) B1983923
theorem B1322635 : Blo 1321479 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B4460183 : Blo 1321479 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B1322647 : Blo 1321479 1322647 := bstep (se 1 (by rfl) ⟨991985, by rfl⟩ : syracuseStep 1322647 = 1983971) B1983971
theorem B2977433 : Blo 1321479 2977433 := bstep (se 2 (by rfl) ⟨1116537, by rfl⟩ : syracuseStep 2977433 = 2233075) B2233075
theorem B1322667 : Blo 1321479 1322667 := bstep (se 1 (by rfl) ⟨992000, by rfl⟩ : syracuseStep 1322667 = 1984001) B1984001
theorem B1322679 : Blo 1321479 1322679 := bstep (se 1 (by rfl) ⟨992009, by rfl⟩ : syracuseStep 1322679 = 1984019) B1984019
theorem B1322699 : Blo 1321479 1322699 := bstep (se 1 (by rfl) ⟨992024, by rfl⟩ : syracuseStep 1322699 = 1984049) B1984049
theorem B1322711 : Blo 1321479 1322711 := bstep (se 1 (by rfl) ⟨992033, by rfl⟩ : syracuseStep 1322711 = 1984067) B1984067
theorem B1322731 : Blo 1321479 1322731 := bstep (se 1 (by rfl) ⟨992048, by rfl⟩ : syracuseStep 1322731 = 1984097) B1984097
theorem B2977523 : Blo 1321479 2977523 := bstep (se 1 (by rfl) ⟨2233142, by rfl⟩ : syracuseStep 2977523 = 4466285) B4466285
theorem B1322743 : Blo 1321479 1322743 := bstep (se 1 (by rfl) ⟨992057, by rfl⟩ : syracuseStep 1322743 = 1984115) B1984115
theorem B1322763 : Blo 1321479 1322763 := bstep (se 1 (by rfl) ⟨992072, by rfl⟩ : syracuseStep 1322763 = 1984145) B1984145
theorem B1675019 : Blo 1321479 1675019 := bstep (se 1 (by rfl) ⟨1256264, by rfl⟩ : syracuseStep 1675019 = 2512529) B2512529
theorem B2510615 : Blo 1321479 2510615 := bstep (se 1 (by rfl) ⟨1882961, by rfl⟩ : syracuseStep 2510615 = 3765923) B3765923
theorem B1322775 : Blo 1321479 1322775 := bstep (se 1 (by rfl) ⟨992081, by rfl⟩ : syracuseStep 1322775 = 1984163) B1984163
theorem B2977559 : Blo 1321479 2977559 := bstep (se 1 (by rfl) ⟨2233169, by rfl⟩ : syracuseStep 2977559 = 4466339) B4466339
theorem B1322795 : Blo 1321479 1322795 := bstep (se 1 (by rfl) ⟨992096, by rfl⟩ : syracuseStep 1322795 = 1984193) B1984193
theorem B1322807 : Blo 1321479 1322807 := bstep (se 1 (by rfl) ⟨992105, by rfl⟩ : syracuseStep 1322807 = 1984211) B1984211
theorem B3764033 : Blo 1321479 3764033 := bstep (se 2 (by rfl) ⟨1411512, by rfl⟩ : syracuseStep 3764033 = 2823025) B2823025
theorem B21458753 : Blo 1321479 21458753 := bstep (se 2 (by rfl) ⟨8047032, by rfl⟩ : syracuseStep 21458753 = 16094065) B16094065
theorem B1322827 : Blo 1321479 1322827 := bstep (se 1 (by rfl) ⟨992120, by rfl⟩ : syracuseStep 1322827 = 1984241) B1984241
theorem B2543447 : Blo 1321479 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B1322839 : Blo 1321479 1322839 := bstep (se 1 (by rfl) ⟨992129, by rfl⟩ : syracuseStep 1322839 = 1984259) B1984259
theorem B1322859 : Blo 1321479 1322859 := bstep (se 1 (by rfl) ⟨992144, by rfl⟩ : syracuseStep 1322859 = 1984289) B1984289
theorem B1322871 : Blo 1321479 1322871 := bstep (se 1 (by rfl) ⟨992153, by rfl⟩ : syracuseStep 1322871 = 1984307) B1984307
theorem B1322891 : Blo 1321479 1322891 := bstep (se 1 (by rfl) ⟨992168, by rfl⟩ : syracuseStep 1322891 = 1984337) B1984337
theorem B4763537 : Blo 1321479 4763537 := bstep (se 2 (by rfl) ⟨1786326, by rfl⟩ : syracuseStep 4763537 = 3572653) B3572653
theorem B1322903 : Blo 1321479 1322903 := bstep (se 1 (by rfl) ⟨992177, by rfl⟩ : syracuseStep 1322903 = 1984355) B1984355
theorem B1322923 : Blo 1321479 1322923 := bstep (se 1 (by rfl) ⟨992192, by rfl⟩ : syracuseStep 1322923 = 1984385) B1984385
theorem B1322935 : Blo 1321479 1322935 := bstep (se 1 (by rfl) ⟨992201, by rfl⟩ : syracuseStep 1322935 = 1984403) B1984403
theorem B1486795 : Blo 1321479 1486795 := bstep (se 1 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 1486795 = 2230193) B2230193
theorem B9531341 : Blo 1321479 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B1322955 : Blo 1321479 1322955 := bstep (se 1 (by rfl) ⟨992216, by rfl⟩ : syracuseStep 1322955 = 1984433) B1984433
theorem B2977739 : Blo 1321479 2977739 := bstep (se 1 (by rfl) ⟨2233304, by rfl⟩ : syracuseStep 2977739 = 4466609) B4466609
theorem B1322967 : Blo 1321479 1322967 := bstep (se 1 (by rfl) ⟨992225, by rfl⟩ : syracuseStep 1322967 = 1984451) B1984451
theorem B3346393 : Blo 1321479 3346393 := bstep (se 2 (by rfl) ⟨1254897, by rfl⟩ : syracuseStep 3346393 = 2509795) B2509795
theorem B1322987 : Blo 1321479 1322987 := bstep (se 1 (by rfl) ⟨992240, by rfl⟩ : syracuseStep 1322987 = 1984481) B1984481
theorem B1322999 : Blo 1321479 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B2977793 : Blo 1321479 2977793 := bstep (se 2 (by rfl) ⟨1116672, by rfl⟩ : syracuseStep 2977793 = 2233345) B2233345
theorem B10039301 : Blo 1321479 10039301 := bstep (se 4 (by rfl) ⟨941184, by rfl⟩ : syracuseStep 10039301 = 1882369) B1882369
theorem B1323019 : Blo 1321479 1323019 := bstep (se 1 (by rfl) ⟨992264, by rfl⟩ : syracuseStep 1323019 = 1984529) B1984529
theorem B1323031 : Blo 1321479 1323031 := bstep (se 1 (by rfl) ⟨992273, by rfl⟩ : syracuseStep 1323031 = 1984547) B1984547
theorem B1323051 : Blo 1321479 1323051 := bstep (se 1 (by rfl) ⟨992288, by rfl⟩ : syracuseStep 1323051 = 1984577) B1984577
theorem B1486903 : Blo 1321479 1486903 := bstep (se 1 (by rfl) ⟨1115177, by rfl⟩ : syracuseStep 1486903 = 2230355) B2230355
theorem B1323063 : Blo 1321479 1323063 := bstep (se 1 (by rfl) ⟨992297, by rfl⟩ : syracuseStep 1323063 = 1984595) B1984595
theorem B1323083 : Blo 1321479 1323083 := bstep (se 1 (by rfl) ⟨992312, by rfl⟩ : syracuseStep 1323083 = 1984625) B1984625
theorem B10047563 : Blo 1321479 10047563 := bstep (se 1 (by rfl) ⟨7535672, by rfl⟩ : syracuseStep 10047563 = 15071345) B15071345
theorem B2232407 : Blo 1321479 2232407 := bstep (se 1 (by rfl) ⟨1674305, by rfl⟩ : syracuseStep 2232407 = 3348611) B3348611
theorem B1323095 : Blo 1321479 1323095 := bstep (se 1 (by rfl) ⟨992321, by rfl⟩ : syracuseStep 1323095 = 1984643) B1984643
theorem B3575897 : Blo 1321479 3575897 := bstep (se 2 (by rfl) ⟨1340961, by rfl⟩ : syracuseStep 3575897 = 2681923) B2681923
theorem B1323115 : Blo 1321479 1323115 := bstep (se 1 (by rfl) ⟨992336, by rfl⟩ : syracuseStep 1323115 = 1984673) B1984673
theorem B1323127 : Blo 1321479 1323127 := bstep (se 1 (by rfl) ⟨992345, by rfl⟩ : syracuseStep 1323127 = 1984691) B1984691
theorem B1323147 : Blo 1321479 1323147 := bstep (se 1 (by rfl) ⟨992360, by rfl⟩ : syracuseStep 1323147 = 1984721) B1984721
theorem B1323159 : Blo 1321479 1323159 := bstep (se 1 (by rfl) ⟨992369, by rfl⟩ : syracuseStep 1323159 = 1984739) B1984739
theorem B1323179 : Blo 1321479 1323179 := bstep (se 1 (by rfl) ⟨992384, by rfl⟩ : syracuseStep 1323179 = 1984769) B1984769
theorem B4460723 : Blo 1321479 4460723 := bstep (se 1 (by rfl) ⟨3345542, by rfl⟩ : syracuseStep 4460723 = 6691085) B6691085
theorem B1323191 : Blo 1321479 1323191 := bstep (se 1 (by rfl) ⟨992393, by rfl⟩ : syracuseStep 1323191 = 1984787) B1984787
theorem B3723457 : Blo 1321479 3723457 := bstep (se 2 (by rfl) ⟨1396296, by rfl⟩ : syracuseStep 3723457 = 2792593) B2792593
theorem B1323211 : Blo 1321479 1323211 := bstep (se 1 (by rfl) ⟨992408, by rfl⟩ : syracuseStep 1323211 = 1984817) B1984817
theorem B2232535 : Blo 1321479 2232535 := bstep (se 1 (by rfl) ⟨1674401, by rfl⟩ : syracuseStep 2232535 = 3348803) B3348803
theorem B1323223 : Blo 1321479 1323223 := bstep (se 1 (by rfl) ⟨992417, by rfl⟩ : syracuseStep 1323223 = 1984835) B1984835
theorem B1487083 : Blo 1321479 1487083 := bstep (se 1 (by rfl) ⟨1115312, by rfl⟩ : syracuseStep 1487083 = 2230625) B2230625
theorem B1323243 : Blo 1321479 1323243 := bstep (se 1 (by rfl) ⟨992432, by rfl⟩ : syracuseStep 1323243 = 1984865) B1984865
theorem B1323255 : Blo 1321479 1323255 := bstep (se 1 (by rfl) ⟨992441, by rfl⟩ : syracuseStep 1323255 = 1984883) B1984883
theorem B5017859 : Blo 1321479 5017859 := bstep (se 1 (by rfl) ⟨3763394, by rfl⟩ : syracuseStep 5017859 = 7526789) B7526789
theorem B5091587 : Blo 1321479 5091587 := bstep (se 1 (by rfl) ⟨3818690, by rfl⟩ : syracuseStep 5091587 = 7637381) B7637381
theorem B16937221 : Blo 1321479 16937221 := bstep (se 4 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 16937221 = 3175729) B3175729
theorem B1323275 : Blo 1321479 1323275 := bstep (se 1 (by rfl) ⟨992456, by rfl⟩ : syracuseStep 1323275 = 1984913) B1984913
theorem B1323287 : Blo 1321479 1323287 := bstep (se 1 (by rfl) ⟨992465, by rfl⟩ : syracuseStep 1323287 = 1984931) B1984931
theorem B1323307 : Blo 1321479 1323307 := bstep (se 1 (by rfl) ⟨992480, by rfl⟩ : syracuseStep 1323307 = 1984961) B1984961
theorem B2511155 : Blo 1321479 2511155 := bstep (se 1 (by rfl) ⟨1883366, by rfl⟩ : syracuseStep 2511155 = 3766733) B3766733
theorem B1323319 : Blo 1321479 1323319 := bstep (se 1 (by rfl) ⟨992489, by rfl⟩ : syracuseStep 1323319 = 1984979) B1984979
theorem B1323339 : Blo 1321479 1323339 := bstep (se 1 (by rfl) ⟨992504, by rfl⟩ : syracuseStep 1323339 = 1985009) B1985009
theorem B1487191 : Blo 1321479 1487191 := bstep (se 1 (by rfl) ⟨1115393, by rfl⟩ : syracuseStep 1487191 = 2230787) B2230787
theorem B1323351 : Blo 1321479 1323351 := bstep (se 1 (by rfl) ⟨992513, by rfl⟩ : syracuseStep 1323351 = 1985027) B1985027
theorem B1323371 : Blo 1321479 1323371 := bstep (se 1 (by rfl) ⟨992528, by rfl⟩ : syracuseStep 1323371 = 1985057) B1985057
theorem B1323383 : Blo 1321479 1323383 := bstep (se 1 (by rfl) ⟨992537, by rfl⟩ : syracuseStep 1323383 = 1985075) B1985075
theorem B1323403 : Blo 1321479 1323403 := bstep (se 1 (by rfl) ⟨992552, by rfl⟩ : syracuseStep 1323403 = 1985105) B1985105
theorem B1323415 : Blo 1321479 1323415 := bstep (se 1 (by rfl) ⟨992561, by rfl⟩ : syracuseStep 1323415 = 1985123) B1985123
theorem B1323435 : Blo 1321479 1323435 := bstep (se 1 (by rfl) ⟨992576, by rfl⟩ : syracuseStep 1323435 = 1985153) B1985153
theorem B1323447 : Blo 1321479 1323447 := bstep (se 1 (by rfl) ⟨992585, by rfl⟩ : syracuseStep 1323447 = 1985171) B1985171
theorem B4460993 : Blo 1321479 4460993 := bstep (se 2 (by rfl) ⟨1672872, by rfl⟩ : syracuseStep 4460993 = 3345745) B3345745
theorem B1323467 : Blo 1321479 1323467 := bstep (se 1 (by rfl) ⟨992600, by rfl⟩ : syracuseStep 1323467 = 1985201) B1985201
theorem B1323479 : Blo 1321479 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B1487371 : Blo 1321479 1487371 := bstep (se 1 (by rfl) ⟨1115528, by rfl⟩ : syracuseStep 1487371 = 2231057) B2231057
theorem B7533121 : Blo 1321479 7533121 := bstep (se 2 (by rfl) ⟨2824920, by rfl⟩ : syracuseStep 7533121 = 5649841) B5649841
theorem B6697565 : Blo 1321479 6697565 := bstep (se 3 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 6697565 = 2511587) B2511587
theorem B1487479 : Blo 1321479 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B2511641 : Blo 1321479 2511641 := bstep (se 2 (by rfl) ⟨941865, by rfl⟩ : syracuseStep 2511641 = 1883731) B1883731
theorem B1487659 : Blo 1321479 1487659 := bstep (se 1 (by rfl) ⟨1115744, by rfl⟩ : syracuseStep 1487659 = 2231489) B2231489
theorem B5649227 : Blo 1321479 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B2233163 : Blo 1321479 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B1487767 : Blo 1321479 1487767 := bstep (se 1 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 1487767 = 2231651) B2231651
theorem B4355009 : Blo 1321479 4355009 := bstep (se 2 (by rfl) ⟨1633128, by rfl⟩ : syracuseStep 4355009 = 3266257) B3266257
theorem B4764619 : Blo 1321479 4764619 := bstep (se 1 (by rfl) ⟨3573464, by rfl⟩ : syracuseStep 4764619 = 7146929) B7146929
theorem B2233291 : Blo 1321479 2233291 := bstep (se 1 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 2233291 = 3349937) B3349937
theorem B4461533 : Blo 1321479 4461533 := bstep (se 3 (by rfl) ⟨836537, by rfl⟩ : syracuseStep 4461533 = 1673075) B1673075
theorem B3347507 : Blo 1321479 3347507 := bstep (se 1 (by rfl) ⟨2510630, by rfl⟩ : syracuseStep 3347507 = 5021261) B5021261
theorem B3175499 : Blo 1321479 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B1487947 : Blo 1321479 1487947 := bstep (se 1 (by rfl) ⟨1115960, by rfl⟩ : syracuseStep 1487947 = 2231921) B2231921
theorem B4764851 : Blo 1321479 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B1488055 : Blo 1321479 1488055 := bstep (se 1 (by rfl) ⟨1116041, by rfl⟩ : syracuseStep 1488055 = 2232083) B2232083
theorem B2823383 : Blo 1321479 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B6690113 : Blo 1321479 6690113 := bstep (se 2 (by rfl) ⟨2508792, by rfl⟩ : syracuseStep 6690113 = 5017585) B5017585
theorem B3347801 : Blo 1321479 3347801 := bstep (se 2 (by rfl) ⟨1255425, by rfl⟩ : syracuseStep 3347801 = 2510851) B2510851
theorem B1488235 : Blo 1321479 1488235 := bstep (se 1 (by rfl) ⟨1116176, by rfl⟩ : syracuseStep 1488235 = 2232353) B2232353
theorem B2119063 : Blo 1321479 2119063 := bstep (se 1 (by rfl) ⟨1589297, by rfl⟩ : syracuseStep 2119063 = 3178595) B3178595
theorem B1488343 : Blo 1321479 1488343 := bstep (se 1 (by rfl) ⟨1116257, by rfl⟩ : syracuseStep 1488343 = 2232515) B2232515
theorem B13563409 : Blo 1321479 13563409 := bstep (se 2 (by rfl) ⟨5086278, by rfl⟩ : syracuseStep 13563409 = 10172557) B10172557
theorem B3577367 : Blo 1321479 3577367 := bstep (se 1 (by rfl) ⟨2683025, by rfl⟩ : syracuseStep 3577367 = 5366051) B5366051
theorem B5650013 : Blo 1321479 5650013 := bstep (se 3 (by rfl) ⟨1059377, by rfl⟩ : syracuseStep 5650013 = 2118755) B2118755
theorem B1488523 : Blo 1321479 1488523 := bstep (se 1 (by rfl) ⟨1116392, by rfl⟩ : syracuseStep 1488523 = 2232785) B2232785
theorem B6035095 : Blo 1321479 6035095 := bstep (se 1 (by rfl) ⟨4526321, by rfl⟩ : syracuseStep 6035095 = 9052643) B9052643
theorem B1488631 : Blo 1321479 1488631 := bstep (se 1 (by rfl) ⟨1116473, by rfl⟩ : syracuseStep 1488631 = 2232947) B2232947
theorem B1611595 : Blo 1321479 1611595 := bstep (se 1 (by rfl) ⟨1208696, by rfl⟩ : syracuseStep 1611595 = 2417393) B2417393
theorem B2119511 : Blo 1321479 2119511 := bstep (se 1 (by rfl) ⟨1589633, by rfl⟩ : syracuseStep 2119511 = 3179267) B3179267
theorem B3766105 : Blo 1321479 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B1488811 : Blo 1321479 1488811 := bstep (se 1 (by rfl) ⟨1116608, by rfl⟩ : syracuseStep 1488811 = 2233217) B2233217
theorem B1882073 : Blo 1321479 1882073 := bstep (se 2 (by rfl) ⟨705777, by rfl⟩ : syracuseStep 1882073 = 1411555) B1411555
theorem B2119691 : Blo 1321479 2119691 := bstep (se 1 (by rfl) ⟨1589768, by rfl⟩ : syracuseStep 2119691 = 3179537) B3179537
theorem B11606051 : Blo 1321479 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B6199361 : Blo 1321479 6199361 := bstep (se 2 (by rfl) ⟨2324760, by rfl⟩ : syracuseStep 6199361 = 4649521) B4649521
theorem B4462667 : Blo 1321479 4462667 := bstep (se 1 (by rfl) ⟨3347000, by rfl⟩ : syracuseStep 4462667 = 6694001) B6694001
theorem B2824409 : Blo 1321479 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B3766493 : Blo 1321479 3766493 := bstep (se 3 (by rfl) ⟨706217, by rfl⟩ : syracuseStep 3766493 = 1412435) B1412435
theorem B4462937 : Blo 1321479 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B10041731 : Blo 1321479 10041731 := bstep (se 1 (by rfl) ⟨7531298, by rfl⟩ : syracuseStep 10041731 = 15062597) B15062597
theorem B4766131 : Blo 1321479 4766131 := bstep (se 1 (by rfl) ⟨3574598, by rfl⟩ : syracuseStep 4766131 = 7149197) B7149197
theorem B6035915 : Blo 1321479 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B1882711 : Blo 1321479 1882711 := bstep (se 1 (by rfl) ⟨1412033, by rfl⟩ : syracuseStep 1882711 = 2824067) B2824067
theorem B6699671 : Blo 1321479 6699671 := bstep (se 1 (by rfl) ⟨5024753, by rfl⟩ : syracuseStep 6699671 = 10049507) B10049507
theorem B12057265 : Blo 1321479 12057265 := bstep (se 2 (by rfl) ⟨4521474, by rfl⟩ : syracuseStep 12057265 = 9042949) B9042949
theorem B8584001 : Blo 1321479 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B5651345 : Blo 1321479 5651345 := bstep (se 2 (by rfl) ⟨2119254, by rfl⟩ : syracuseStep 5651345 = 4238509) B4238509
theorem B3349451 : Blo 1321479 3349451 := bstep (se 1 (by rfl) ⟨2512088, by rfl⟩ : syracuseStep 3349451 = 5024177) B5024177
theorem B4463639 : Blo 1321479 4463639 := bstep (se 1 (by rfl) ⟨3347729, by rfl⟩ : syracuseStep 4463639 = 6695459) B6695459
theorem B6692057 : Blo 1321479 6692057 := bstep (se 2 (by rfl) ⟨2509521, by rfl⟩ : syracuseStep 6692057 = 5019043) B5019043
theorem B1883417 : Blo 1321479 1883417 := bstep (se 2 (by rfl) ⟨706281, by rfl⟩ : syracuseStep 1883417 = 1412563) B1412563
theorem B5020973 : Blo 1321479 5020973 := bstep (se 3 (by rfl) ⟨941432, by rfl⟩ : syracuseStep 5020973 = 1882865) B1882865
theorem B1588567 : Blo 1321479 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B6438275 : Blo 1321479 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B1883531 : Blo 1321479 1883531 := bstep (se 1 (by rfl) ⟨1412648, by rfl⟩ : syracuseStep 1883531 = 2825297) B2825297
theorem B4521395 : Blo 1321479 4521395 := bstep (se 1 (by rfl) ⟨3391046, by rfl⟩ : syracuseStep 4521395 = 6782093) B6782093
theorem B5086723 : Blo 1321479 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B15072803 : Blo 1321479 15072803 := bstep (se 1 (by rfl) ⟨11304602, by rfl⟩ : syracuseStep 15072803 = 22609205) B22609205
theorem B4464179 : Blo 1321479 4464179 := bstep (se 1 (by rfl) ⟨3348134, by rfl⟩ : syracuseStep 4464179 = 6696269) B6696269
theorem B2481779 : Blo 1321479 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B8044211 : Blo 1321479 8044211 := bstep (se 1 (by rfl) ⟨6033158, by rfl⟩ : syracuseStep 8044211 = 12066317) B12066317
theorem B2973401 : Blo 1321479 2973401 := bstep (se 2 (by rfl) ⟨1115025, by rfl⟩ : syracuseStep 2973401 = 2230051) B2230051
theorem B1982219 : Blo 1321479 1982219 := bstep (se 1 (by rfl) ⟨1486664, by rfl⟩ : syracuseStep 1982219 = 2973329) B2973329
theorem B1982231 : Blo 1321479 1982231 := bstep (se 1 (by rfl) ⟨1486673, by rfl⟩ : syracuseStep 1982231 = 2973347) B2973347
theorem B2973491 : Blo 1321479 2973491 := bstep (se 1 (by rfl) ⟨2230118, by rfl⟩ : syracuseStep 2973491 = 4460237) B4460237
theorem B4464449 : Blo 1321479 4464449 := bstep (se 2 (by rfl) ⟨1674168, by rfl⟩ : syracuseStep 4464449 = 3348337) B3348337
theorem B2826049 : Blo 1321479 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B2973527 : Blo 1321479 2973527 := bstep (se 1 (by rfl) ⟨2230145, by rfl⟩ : syracuseStep 2973527 = 4460291) B4460291
theorem B1982297 : Blo 1321479 1982297 := bstep (se 2 (by rfl) ⟨743361, by rfl⟩ : syracuseStep 1982297 = 1486723) B1486723
theorem B10182493 : Blo 1321479 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B4767619 : Blo 1321479 4767619 := bstep (se 1 (by rfl) ⟨3575714, by rfl⟩ : syracuseStep 4767619 = 7151429) B7151429
theorem B1884055 : Blo 1321479 1884055 := bstep (se 1 (by rfl) ⟨1413041, by rfl⟩ : syracuseStep 1884055 = 2826083) B2826083
theorem B19333043 : Blo 1321479 19333043 := bstep (se 1 (by rfl) ⟨14499782, by rfl⟩ : syracuseStep 19333043 = 28999565) B28999565
theorem B7536563 : Blo 1321479 7536563 := bstep (se 1 (by rfl) ⟨5652422, by rfl⟩ : syracuseStep 7536563 = 11304845) B11304845
theorem B1982411 : Blo 1321479 1982411 := bstep (se 1 (by rfl) ⟨1486808, by rfl⟩ : syracuseStep 1982411 = 2973617) B2973617
theorem B1982423 : Blo 1321479 1982423 := bstep (se 1 (by rfl) ⟨1486817, by rfl⟩ : syracuseStep 1982423 = 2973635) B2973635
theorem B8044505 : Blo 1321479 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B6692867 : Blo 1321479 6692867 := bstep (se 1 (by rfl) ⟨5019650, by rfl⟩ : syracuseStep 6692867 = 10039301) B10039301
theorem B1982471 : Blo 1321479 1982471 := bstep (se 1 (by rfl) ⟨1486853, by rfl⟩ : syracuseStep 1982471 = 2973707) B2973707
theorem B1982507 : Blo 1321479 1982507 := bstep (se 1 (by rfl) ⟨1486880, by rfl⟩ : syracuseStep 1982507 = 2973761) B2973761
theorem B2383931 : Blo 1321479 2383931 := bstep (se 1 (by rfl) ⟨1787948, by rfl⟩ : syracuseStep 2383931 = 3575897) B3575897
theorem B1982537 : Blo 1321479 1982537 := bstep (se 2 (by rfl) ⟨743451, by rfl⟩ : syracuseStep 1982537 = 1486903) B1486903
theorem B3768407 : Blo 1321479 3768407 := bstep (se 1 (by rfl) ⟨2826305, by rfl⟩ : syracuseStep 3768407 = 5652611) B5652611
theorem B2973815 : Blo 1321479 2973815 := bstep (se 1 (by rfl) ⟨2230361, by rfl⟩ : syracuseStep 2973815 = 4460723) B4460723
theorem B1982651 : Blo 1321479 1982651 := bstep (se 1 (by rfl) ⟨1486988, by rfl⟩ : syracuseStep 1982651 = 2973977) B2973977
theorem B1982711 : Blo 1321479 1982711 := bstep (se 1 (by rfl) ⟨1487033, by rfl⟩ : syracuseStep 1982711 = 2974067) B2974067
theorem B4964609 : Blo 1321479 4964609 := bstep (se 2 (by rfl) ⟨1861728, by rfl⟩ : syracuseStep 4964609 = 3723457) B3723457
theorem B1982735 : Blo 1321479 1982735 := bstep (se 1 (by rfl) ⟨1487051, by rfl⟩ : syracuseStep 1982735 = 2974103) B2974103
theorem B2973995 : Blo 1321479 2973995 := bstep (se 1 (by rfl) ⟨2230496, by rfl⟩ : syracuseStep 2973995 = 4460993) B4460993
theorem B1982777 : Blo 1321479 1982777 := bstep (se 2 (by rfl) ⟨743541, by rfl⟩ : syracuseStep 1982777 = 1487083) B1487083
theorem B1982855 : Blo 1321479 1982855 := bstep (se 1 (by rfl) ⟨1487141, by rfl⟩ : syracuseStep 1982855 = 2974283) B2974283
theorem B8470919 : Blo 1321479 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B4465043 : Blo 1321479 4465043 := bstep (se 1 (by rfl) ⟨3348782, by rfl⟩ : syracuseStep 4465043 = 6697565) B6697565
theorem B1982891 : Blo 1321479 1982891 := bstep (se 1 (by rfl) ⟨1487168, by rfl⟩ : syracuseStep 1982891 = 2974337) B2974337
theorem B1982921 : Blo 1321479 1982921 := bstep (se 2 (by rfl) ⟨743595, by rfl⟩ : syracuseStep 1982921 = 1487191) B1487191
theorem B1983035 : Blo 1321479 1983035 := bstep (se 1 (by rfl) ⟨1487276, by rfl⟩ : syracuseStep 1983035 = 2974553) B2974553
theorem B7529021 : Blo 1321479 7529021 := bstep (se 3 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 7529021 = 2823383) B2823383
theorem B7848535 : Blo 1321479 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B1983095 : Blo 1321479 1983095 := bstep (se 1 (by rfl) ⟨1487321, by rfl⟩ : syracuseStep 1983095 = 2974643) B2974643
theorem B1983119 : Blo 1321479 1983119 := bstep (se 1 (by rfl) ⟨1487339, by rfl⟩ : syracuseStep 1983119 = 2974679) B2974679
theorem B2974355 : Blo 1321479 2974355 := bstep (se 1 (by rfl) ⟨2230766, by rfl⟩ : syracuseStep 2974355 = 4461533) B4461533
theorem B1983161 : Blo 1321479 1983161 := bstep (se 2 (by rfl) ⟨743685, by rfl⟩ : syracuseStep 1983161 = 1487371) B1487371
theorem B2974409 : Blo 1321479 2974409 := bstep (se 2 (by rfl) ⟨1115403, by rfl⟩ : syracuseStep 2974409 = 2230807) B2230807
theorem B5022445 : Blo 1321479 5022445 := bstep (se 3 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 5022445 = 1883417) B1883417
theorem B10044161 : Blo 1321479 10044161 := bstep (se 2 (by rfl) ⟨3766560, by rfl⟩ : syracuseStep 10044161 = 7533121) B7533121
theorem B1983239 : Blo 1321479 1983239 := bstep (se 1 (by rfl) ⟨1487429, by rfl⟩ : syracuseStep 1983239 = 2974859) B2974859
theorem B1983275 : Blo 1321479 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B1983305 : Blo 1321479 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B1983419 : Blo 1321479 1983419 := bstep (se 1 (by rfl) ⟨1487564, by rfl⟩ : syracuseStep 1983419 = 2975129) B2975129
theorem B1983479 : Blo 1321479 1983479 := bstep (se 1 (by rfl) ⟨1487609, by rfl⟩ : syracuseStep 1983479 = 2975219) B2975219
theorem B3015695 : Blo 1321479 3015695 := bstep (se 1 (by rfl) ⟨2261771, by rfl⟩ : syracuseStep 3015695 = 4523543) B4523543
theorem B1983503 : Blo 1321479 1983503 := bstep (se 1 (by rfl) ⟨1487627, by rfl⟩ : syracuseStep 1983503 = 2975255) B2975255
theorem B2384911 : Blo 1321479 2384911 := bstep (se 1 (by rfl) ⟨1788683, by rfl⟩ : syracuseStep 2384911 = 3577367) B3577367
theorem B5022749 : Blo 1321479 5022749 := bstep (se 3 (by rfl) ⟨941765, by rfl⟩ : syracuseStep 5022749 = 1883531) B1883531
theorem B1983545 : Blo 1321479 1983545 := bstep (se 2 (by rfl) ⟨743829, by rfl⟩ : syracuseStep 1983545 = 1487659) B1487659
theorem B1983623 : Blo 1321479 1983623 := bstep (se 1 (by rfl) ⟨1487717, by rfl⟩ : syracuseStep 1983623 = 2975435) B2975435
theorem B1983659 : Blo 1321479 1983659 := bstep (se 1 (by rfl) ⟨1487744, by rfl⟩ : syracuseStep 1983659 = 2975489) B2975489
theorem B1983689 : Blo 1321479 1983689 := bstep (se 2 (by rfl) ⟨743883, by rfl⟩ : syracuseStep 1983689 = 1487767) B1487767
theorem B1983803 : Blo 1321479 1983803 := bstep (se 1 (by rfl) ⟨1487852, by rfl⟩ : syracuseStep 1983803 = 2975705) B2975705
theorem B1983863 : Blo 1321479 1983863 := bstep (se 1 (by rfl) ⟨1487897, by rfl⟩ : syracuseStep 1983863 = 2975795) B2975795
theorem B2975111 : Blo 1321479 2975111 := bstep (se 1 (by rfl) ⟨2231333, by rfl⟩ : syracuseStep 2975111 = 4462667) B4462667
theorem B1983887 : Blo 1321479 1983887 := bstep (se 1 (by rfl) ⟨1487915, by rfl⟩ : syracuseStep 1983887 = 2975831) B2975831
theorem B1983929 : Blo 1321479 1983929 := bstep (se 2 (by rfl) ⟨743973, by rfl⟩ : syracuseStep 1983929 = 1487947) B1487947
theorem B1984007 : Blo 1321479 1984007 := bstep (se 1 (by rfl) ⟨1488005, by rfl⟩ : syracuseStep 1984007 = 2976011) B2976011
theorem B2901547 : Blo 1321479 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B1984043 : Blo 1321479 1984043 := bstep (se 1 (by rfl) ⟨1488032, by rfl⟩ : syracuseStep 1984043 = 2976065) B2976065
theorem B2975291 : Blo 1321479 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B1984073 : Blo 1321479 1984073 := bstep (se 2 (by rfl) ⟨744027, by rfl⟩ : syracuseStep 1984073 = 1488055) B1488055
theorem B6694487 : Blo 1321479 6694487 := bstep (se 1 (by rfl) ⟨5020865, by rfl⟩ : syracuseStep 6694487 = 10041731) B10041731
theorem B2975417 : Blo 1321479 2975417 := bstep (se 2 (by rfl) ⟨1115781, by rfl⟩ : syracuseStep 2975417 = 2231563) B2231563
theorem B1984187 : Blo 1321479 1984187 := bstep (se 1 (by rfl) ⟨1488140, by rfl⟩ : syracuseStep 1984187 = 2976281) B2976281
theorem B8595173 : Blo 1321479 8595173 := bstep (se 4 (by rfl) ⟨805797, by rfl⟩ : syracuseStep 8595173 = 1611595) B1611595
theorem B1984247 : Blo 1321479 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B2230031 : Blo 1321479 2230031 := bstep (se 1 (by rfl) ⟨1672523, by rfl⟩ : syracuseStep 2230031 = 3345047) B3345047
theorem B1984271 : Blo 1321479 1984271 := bstep (se 1 (by rfl) ⟨1488203, by rfl⟩ : syracuseStep 1984271 = 2976407) B2976407
theorem B4466447 : Blo 1321479 4466447 := bstep (se 1 (by rfl) ⟨3349835, by rfl⟩ : syracuseStep 4466447 = 6699671) B6699671
theorem B1984313 : Blo 1321479 1984313 := bstep (se 2 (by rfl) ⟨744117, by rfl⟩ : syracuseStep 1984313 = 1488235) B1488235
theorem B206219125 : Blo 1321479 206219125 := bstep (se 5 (by rfl) ⟨9666521, by rfl⟩ : syracuseStep 206219125 = 19333043) B19333043
theorem B1984391 : Blo 1321479 1984391 := bstep (se 1 (by rfl) ⟨1488293, by rfl⟩ : syracuseStep 1984391 = 2976587) B2976587
theorem B1673131 : Blo 1321479 1673131 := bstep (se 1 (by rfl) ⟨1254848, by rfl⟩ : syracuseStep 1673131 = 2509697) B2509697
theorem B1984427 : Blo 1321479 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B1984457 : Blo 1321479 1984457 := bstep (se 2 (by rfl) ⟨744171, by rfl⟩ : syracuseStep 1984457 = 1488343) B1488343
theorem B2975759 : Blo 1321479 2975759 := bstep (se 1 (by rfl) ⟨2231819, by rfl⟩ : syracuseStep 2975759 = 4463639) B4463639
theorem B4466717 : Blo 1321479 4466717 := bstep (se 3 (by rfl) ⟨837509, by rfl⟩ : syracuseStep 4466717 = 1675019) B1675019
theorem B2975777 : Blo 1321479 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B1984571 : Blo 1321479 1984571 := bstep (se 1 (by rfl) ⟨1488428, by rfl⟩ : syracuseStep 1984571 = 2976857) B2976857
theorem B6694973 : Blo 1321479 6694973 := bstep (se 3 (by rfl) ⟨1255307, by rfl⟩ : syracuseStep 6694973 = 2510615) B2510615
theorem B1984631 : Blo 1321479 1984631 := bstep (se 1 (by rfl) ⟨1488473, by rfl⟩ : syracuseStep 1984631 = 2976947) B2976947
theorem B1984655 : Blo 1321479 1984655 := bstep (se 1 (by rfl) ⟨1488491, by rfl⟩ : syracuseStep 1984655 = 2976983) B2976983
theorem B1984697 : Blo 1321479 1984697 := bstep (se 2 (by rfl) ⟨744261, by rfl⟩ : syracuseStep 1984697 = 1488523) B1488523
theorem B8046793 : Blo 1321479 8046793 := bstep (se 2 (by rfl) ⟨3017547, by rfl⟩ : syracuseStep 8046793 = 6035095) B6035095
theorem B1984775 : Blo 1321479 1984775 := bstep (se 1 (by rfl) ⟨1488581, by rfl⟩ : syracuseStep 1984775 = 2977163) B2977163
theorem B2230571 : Blo 1321479 2230571 := bstep (se 1 (by rfl) ⟨1672928, by rfl⟩ : syracuseStep 2230571 = 3345857) B3345857
theorem B1788203 : Blo 1321479 1788203 := bstep (se 1 (by rfl) ⟨1341152, by rfl⟩ : syracuseStep 1788203 = 2682305) B2682305
theorem B1984811 : Blo 1321479 1984811 := bstep (se 1 (by rfl) ⟨1488608, by rfl⟩ : syracuseStep 1984811 = 2977217) B2977217
theorem B1984841 : Blo 1321479 1984841 := bstep (se 2 (by rfl) ⟨744315, by rfl⟩ : syracuseStep 1984841 = 1488631) B1488631
theorem B2976119 : Blo 1321479 2976119 := bstep (se 1 (by rfl) ⟨2232089, by rfl⟩ : syracuseStep 2976119 = 4464179) B4464179
theorem B1984955 : Blo 1321479 1984955 := bstep (se 1 (by rfl) ⟨1488716, by rfl⟩ : syracuseStep 1984955 = 2977433) B2977433
theorem B13576657 : Blo 1321479 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B1985015 : Blo 1321479 1985015 := bstep (se 1 (by rfl) ⟨1488761, by rfl⟩ : syracuseStep 1985015 = 2977523) B2977523
theorem B1321479 : Blo 1321479 1321479 := bstep (se 1 (by rfl) ⟨991109, by rfl⟩ : syracuseStep 1321479 = 1982219) B1982219
theorem B1321487 : Blo 1321479 1321487 := bstep (se 1 (by rfl) ⟨991115, by rfl⟩ : syracuseStep 1321487 = 1982231) B1982231
theorem B1985039 : Blo 1321479 1985039 := bstep (se 1 (by rfl) ⟨1488779, by rfl⟩ : syracuseStep 1985039 = 2977559) B2977559
theorem B2509355 : Blo 1321479 2509355 := bstep (se 1 (by rfl) ⟨1882016, by rfl⟩ : syracuseStep 2509355 = 3764033) B3764033
theorem B2976299 : Blo 1321479 2976299 := bstep (se 1 (by rfl) ⟨2232224, by rfl⟩ : syracuseStep 2976299 = 4464449) B4464449
theorem B14305835 : Blo 1321479 14305835 := bstep (se 1 (by rfl) ⟨10729376, by rfl⟩ : syracuseStep 14305835 = 21458753) B21458753
theorem B1985081 : Blo 1321479 1985081 := bstep (se 2 (by rfl) ⟨744405, by rfl⟩ : syracuseStep 1985081 = 1488811) B1488811
theorem B1321531 : Blo 1321479 1321531 := bstep (se 1 (by rfl) ⟨991148, by rfl⟩ : syracuseStep 1321531 = 1982297) B1982297
theorem B5024375 : Blo 1321479 5024375 := bstep (se 1 (by rfl) ⟨3768281, by rfl⟩ : syracuseStep 5024375 = 7536563) B7536563
theorem B1321607 : Blo 1321479 1321607 := bstep (se 1 (by rfl) ⟨991205, by rfl⟩ : syracuseStep 1321607 = 1982411) B1982411
theorem B1985159 : Blo 1321479 1985159 := bstep (se 1 (by rfl) ⟨1488869, by rfl⟩ : syracuseStep 1985159 = 2977739) B2977739
theorem B1321615 : Blo 1321479 1321615 := bstep (se 1 (by rfl) ⟨991211, by rfl⟩ : syracuseStep 1321615 = 1982423) B1982423
theorem B1985195 : Blo 1321479 1985195 := bstep (se 1 (by rfl) ⟨1488896, by rfl⟩ : syracuseStep 1985195 = 2977793) B2977793
theorem B2230969 : Blo 1321479 2230969 := bstep (se 2 (by rfl) ⟨836613, by rfl⟩ : syracuseStep 2230969 = 1673227) B1673227
theorem B1321659 : Blo 1321479 1321659 := bstep (se 1 (by rfl) ⟨991244, by rfl⟩ : syracuseStep 1321659 = 1982489) B1982489
theorem B3345097 : Blo 1321479 3345097 := bstep (se 2 (by rfl) ⟨1254411, by rfl⟩ : syracuseStep 3345097 = 2508823) B2508823
theorem B1321735 : Blo 1321479 1321735 := bstep (se 1 (by rfl) ⟨991301, by rfl⟩ : syracuseStep 1321735 = 1982603) B1982603
theorem B1321743 : Blo 1321479 1321743 := bstep (se 1 (by rfl) ⟨991307, by rfl⟩ : syracuseStep 1321743 = 1982615) B1982615
theorem B12716837 : Blo 1321479 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B1321787 : Blo 1321479 1321787 := bstep (se 1 (by rfl) ⟨991340, by rfl⟩ : syracuseStep 1321787 = 1982681) B1982681
theorem B3345239 : Blo 1321479 3345239 := bstep (se 1 (by rfl) ⟨2508929, by rfl⟩ : syracuseStep 3345239 = 5017859) B5017859
theorem B3394391 : Blo 1321479 3394391 := bstep (se 1 (by rfl) ⟨2545793, by rfl⟩ : syracuseStep 3394391 = 5091587) B5091587
theorem B1674103 : Blo 1321479 1674103 := bstep (se 1 (by rfl) ⟨1255577, by rfl⟩ : syracuseStep 1674103 = 2511155) B2511155
theorem B1321863 : Blo 1321479 1321863 := bstep (se 1 (by rfl) ⟨991397, by rfl⟩ : syracuseStep 1321863 = 1982795) B1982795
theorem B1321871 : Blo 1321479 1321871 := bstep (se 1 (by rfl) ⟨991403, by rfl⟩ : syracuseStep 1321871 = 1982807) B1982807
theorem B2976659 : Blo 1321479 2976659 := bstep (se 1 (by rfl) ⟨2232494, by rfl⟩ : syracuseStep 2976659 = 4464989) B4464989
theorem B12888983 : Blo 1321479 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B11447203 : Blo 1321479 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1321915 : Blo 1321479 1321915 := bstep (se 1 (by rfl) ⟨991436, by rfl⟩ : syracuseStep 1321915 = 1982873) B1982873
theorem B3574729 : Blo 1321479 3574729 := bstep (se 2 (by rfl) ⟨1340523, by rfl⟩ : syracuseStep 3574729 = 2681047) B2681047
theorem B2976713 : Blo 1321479 2976713 := bstep (se 2 (by rfl) ⟨1116267, by rfl⟩ : syracuseStep 2976713 = 2232535) B2232535
theorem B5647313 : Blo 1321479 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B1321991 : Blo 1321479 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B1321999 : Blo 1321479 1321999 := bstep (se 1 (by rfl) ⟨991499, by rfl⟩ : syracuseStep 1321999 = 1982999) B1982999
theorem B1322043 : Blo 1321479 1322043 := bstep (se 1 (by rfl) ⟨991532, by rfl⟩ : syracuseStep 1322043 = 1983065) B1983065
theorem B6351959 : Blo 1321479 6351959 := bstep (se 1 (by rfl) ⟨4763969, by rfl⟩ : syracuseStep 6351959 = 9527939) B9527939
theorem B1322119 : Blo 1321479 1322119 := bstep (se 1 (by rfl) ⟨991589, by rfl⟩ : syracuseStep 1322119 = 1983179) B1983179
theorem B1322127 : Blo 1321479 1322127 := bstep (se 1 (by rfl) ⟨991595, by rfl⟩ : syracuseStep 1322127 = 1983191) B1983191
theorem B1322171 : Blo 1321479 1322171 := bstep (se 1 (by rfl) ⟨991628, by rfl⟩ : syracuseStep 1322171 = 1983257) B1983257
theorem B1674427 : Blo 1321479 1674427 := bstep (se 1 (by rfl) ⟨1255820, by rfl⟩ : syracuseStep 1674427 = 2511641) B2511641
theorem B30518477 : Blo 1321479 30518477 := bstep (se 3 (by rfl) ⟨5722214, by rfl⟩ : syracuseStep 30518477 = 11444429) B11444429
theorem B1322247 : Blo 1321479 1322247 := bstep (se 1 (by rfl) ⟨991685, by rfl⟩ : syracuseStep 1322247 = 1983371) B1983371
theorem B1322255 : Blo 1321479 1322255 := bstep (se 1 (by rfl) ⟨991691, by rfl⟩ : syracuseStep 1322255 = 1983383) B1983383
theorem B1322299 : Blo 1321479 1322299 := bstep (se 1 (by rfl) ⟨991724, by rfl⟩ : syracuseStep 1322299 = 1983449) B1983449
theorem B3763543 : Blo 1321479 3763543 := bstep (se 1 (by rfl) ⟨2822657, by rfl⟩ : syracuseStep 3763543 = 5645315) B5645315
theorem B2231671 : Blo 1321479 2231671 := bstep (se 1 (by rfl) ⟨1673753, by rfl⟩ : syracuseStep 2231671 = 3347507) B3347507
theorem B2116999 : Blo 1321479 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B1322375 : Blo 1321479 1322375 := bstep (se 1 (by rfl) ⟨991781, by rfl⟩ : syracuseStep 1322375 = 1983563) B1983563
theorem B1322383 : Blo 1321479 1322383 := bstep (se 1 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 1322383 = 1983575) B1983575
theorem B1322427 : Blo 1321479 1322427 := bstep (se 1 (by rfl) ⟨991820, by rfl⟩ : syracuseStep 1322427 = 1983641) B1983641
theorem B2510281 : Blo 1321479 2510281 := bstep (se 2 (by rfl) ⟨941355, by rfl⟩ : syracuseStep 2510281 = 1882711) B1882711
theorem B1322503 : Blo 1321479 1322503 := bstep (se 1 (by rfl) ⟨991877, by rfl⟩ : syracuseStep 1322503 = 1983755) B1983755
theorem B1322511 : Blo 1321479 1322511 := bstep (se 1 (by rfl) ⟨991883, by rfl⟩ : syracuseStep 1322511 = 1983767) B1983767
theorem B4460075 : Blo 1321479 4460075 := bstep (se 1 (by rfl) ⟨3345056, by rfl⟩ : syracuseStep 4460075 = 6690113) B6690113
theorem B1322555 : Blo 1321479 1322555 := bstep (se 1 (by rfl) ⟨991916, by rfl⟩ : syracuseStep 1322555 = 1983833) B1983833
theorem B2231867 : Blo 1321479 2231867 := bstep (se 1 (by rfl) ⟨1673900, by rfl⟩ : syracuseStep 2231867 = 3347801) B3347801
theorem B16076353 : Blo 1321479 16076353 := bstep (se 2 (by rfl) ⟨6028632, by rfl⟩ : syracuseStep 16076353 = 12057265) B12057265
theorem B11300471 : Blo 1321479 11300471 := bstep (se 1 (by rfl) ⟨8475353, by rfl⟩ : syracuseStep 11300471 = 16950707) B16950707
theorem B1322631 : Blo 1321479 1322631 := bstep (se 1 (by rfl) ⟨991973, by rfl⟩ : syracuseStep 1322631 = 1983947) B1983947
theorem B2977415 : Blo 1321479 2977415 := bstep (se 1 (by rfl) ⟨2233061, by rfl⟩ : syracuseStep 2977415 = 4466123) B4466123
theorem B1322639 : Blo 1321479 1322639 := bstep (se 1 (by rfl) ⟨991979, by rfl⟩ : syracuseStep 1322639 = 1983959) B1983959
theorem B2010809 : Blo 1321479 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1322683 : Blo 1321479 1322683 := bstep (se 1 (by rfl) ⟨992012, by rfl⟩ : syracuseStep 1322683 = 1984025) B1984025
theorem B1322759 : Blo 1321479 1322759 := bstep (se 1 (by rfl) ⟨992069, by rfl⟩ : syracuseStep 1322759 = 1984139) B1984139
theorem B1322767 : Blo 1321479 1322767 := bstep (se 1 (by rfl) ⟨992075, by rfl⟩ : syracuseStep 1322767 = 1984151) B1984151
theorem B6696755 : Blo 1321479 6696755 := bstep (se 1 (by rfl) ⟨5022566, by rfl⟩ : syracuseStep 6696755 = 10045133) B10045133
theorem B1322811 : Blo 1321479 1322811 := bstep (se 1 (by rfl) ⟨992108, by rfl⟩ : syracuseStep 1322811 = 1984217) B1984217
theorem B2977595 : Blo 1321479 2977595 := bstep (se 1 (by rfl) ⟨2233196, by rfl⟩ : syracuseStep 2977595 = 4466393) B4466393
theorem B1322887 : Blo 1321479 1322887 := bstep (se 1 (by rfl) ⟨992165, by rfl⟩ : syracuseStep 1322887 = 1984331) B1984331
theorem B1322895 : Blo 1321479 1322895 := bstep (se 1 (by rfl) ⟨992171, by rfl⟩ : syracuseStep 1322895 = 1984343) B1984343
theorem B1413007 : Blo 1321479 1413007 := bstep (se 1 (by rfl) ⟨1059755, by rfl⟩ : syracuseStep 1413007 = 2119511) B2119511
theorem B6352825 : Blo 1321479 6352825 := bstep (se 2 (by rfl) ⟨2382309, by rfl⟩ : syracuseStep 6352825 = 4764619) B4764619
theorem B1322939 : Blo 1321479 1322939 := bstep (se 1 (by rfl) ⟨992204, by rfl⟩ : syracuseStep 1322939 = 1984409) B1984409
theorem B2977721 : Blo 1321479 2977721 := bstep (se 2 (by rfl) ⟨1116645, by rfl⟩ : syracuseStep 2977721 = 2233291) B2233291
theorem B2232265 : Blo 1321479 2232265 := bstep (se 2 (by rfl) ⟨837099, by rfl⟩ : syracuseStep 2232265 = 1674199) B1674199
theorem B6352843 : Blo 1321479 6352843 := bstep (se 1 (by rfl) ⟨4764632, by rfl⟩ : syracuseStep 6352843 = 9529265) B9529265
theorem B1323015 : Blo 1321479 1323015 := bstep (se 1 (by rfl) ⟨992261, by rfl⟩ : syracuseStep 1323015 = 1984523) B1984523
theorem B1413127 : Blo 1321479 1413127 := bstep (se 1 (by rfl) ⟨1059845, by rfl⟩ : syracuseStep 1413127 = 2119691) B2119691
theorem B1323023 : Blo 1321479 1323023 := bstep (se 1 (by rfl) ⟨992267, by rfl⟩ : syracuseStep 1323023 = 1984535) B1984535
theorem B7737367 : Blo 1321479 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B4132907 : Blo 1321479 4132907 := bstep (se 1 (by rfl) ⟨3099680, by rfl⟩ : syracuseStep 4132907 = 6199361) B6199361
theorem B1323067 : Blo 1321479 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B6697079 : Blo 1321479 6697079 := bstep (se 1 (by rfl) ⟨5022809, by rfl⟩ : syracuseStep 6697079 = 10045619) B10045619
theorem B1323143 : Blo 1321479 1323143 := bstep (se 1 (by rfl) ⟨992357, by rfl⟩ : syracuseStep 1323143 = 1984715) B1984715
theorem B1323151 : Blo 1321479 1323151 := bstep (se 1 (by rfl) ⟨992363, by rfl⟩ : syracuseStep 1323151 = 1984727) B1984727
theorem B2510995 : Blo 1321479 2510995 := bstep (se 1 (by rfl) ⟨1883246, by rfl⟩ : syracuseStep 2510995 = 3766493) B3766493
theorem B1323195 : Blo 1321479 1323195 := bstep (se 1 (by rfl) ⟨992396, by rfl⟩ : syracuseStep 1323195 = 1984793) B1984793
theorem B1323271 : Blo 1321479 1323271 := bstep (se 1 (by rfl) ⟨992453, by rfl⟩ : syracuseStep 1323271 = 1984907) B1984907
theorem B1487119 : Blo 1321479 1487119 := bstep (se 1 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 1487119 = 2230679) B2230679
theorem B1323279 : Blo 1321479 1323279 := bstep (se 1 (by rfl) ⟨992459, by rfl⟩ : syracuseStep 1323279 = 1984919) B1984919
theorem B5017889 : Blo 1321479 5017889 := bstep (se 2 (by rfl) ⟨1881708, by rfl⟩ : syracuseStep 5017889 = 3763417) B3763417
theorem B1323323 : Blo 1321479 1323323 := bstep (se 1 (by rfl) ⟨992492, by rfl⟩ : syracuseStep 1323323 = 1984985) B1984985
theorem B1323399 : Blo 1321479 1323399 := bstep (se 1 (by rfl) ⟨992549, by rfl⟩ : syracuseStep 1323399 = 1985099) B1985099
theorem B1323407 : Blo 1321479 1323407 := bstep (se 1 (by rfl) ⟨992555, by rfl⟩ : syracuseStep 1323407 = 1985111) B1985111
theorem B1323451 : Blo 1321479 1323451 := bstep (se 1 (by rfl) ⟨992588, by rfl⟩ : syracuseStep 1323451 = 1985177) B1985177
theorem B2118089 : Blo 1321479 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B5722667 : Blo 1321479 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B4764203 : Blo 1321479 4764203 := bstep (se 1 (by rfl) ⟨3573152, by rfl⟩ : syracuseStep 4764203 = 7146305) B7146305
theorem B2232967 : Blo 1321479 2232967 := bstep (se 1 (by rfl) ⟨1674725, by rfl⟩ : syracuseStep 2232967 = 3349451) B3349451
theorem B46453429 : Blo 1321479 46453429 := bstep (se 5 (by rfl) ⟨2177504, by rfl⟩ : syracuseStep 46453429 = 4355009) B4355009
theorem B18084545 : Blo 1321479 18084545 := bstep (se 2 (by rfl) ⟨6781704, by rfl⟩ : syracuseStep 18084545 = 13563409) B13563409
theorem B1487623 : Blo 1321479 1487623 := bstep (se 1 (by rfl) ⟨1115717, by rfl⟩ : syracuseStep 1487623 = 2231435) B2231435
theorem B12071717 : Blo 1321479 12071717 := bstep (se 4 (by rfl) ⟨1131723, by rfl⟩ : syracuseStep 12071717 = 2263447) B2263447
theorem B3765035 : Blo 1321479 3765035 := bstep (se 1 (by rfl) ⟨2823776, by rfl⟩ : syracuseStep 3765035 = 5647553) B5647553
theorem B4461371 : Blo 1321479 4461371 := bstep (se 1 (by rfl) ⟨3346028, by rfl⟩ : syracuseStep 4461371 = 6692057) B6692057
theorem B3347315 : Blo 1321479 3347315 := bstep (se 1 (by rfl) ⟨2510486, by rfl⟩ : syracuseStep 3347315 = 5020973) B5020973
theorem B1487803 : Blo 1321479 1487803 := bstep (se 1 (by rfl) ⟨1115852, by rfl⟩ : syracuseStep 1487803 = 2231705) B2231705
theorem B10048535 : Blo 1321479 10048535 := bstep (se 1 (by rfl) ⟨7536401, by rfl⟩ : syracuseStep 10048535 = 15072803) B15072803
theorem B6698051 : Blo 1321479 6698051 := bstep (se 1 (by rfl) ⟨5023538, by rfl⟩ : syracuseStep 6698051 = 10047077) B10047077
theorem B5362807 : Blo 1321479 5362807 := bstep (se 1 (by rfl) ⟨4022105, by rfl⟩ : syracuseStep 5362807 = 8044211) B8044211
theorem B2512073 : Blo 1321479 2512073 := bstep (se 2 (by rfl) ⟨942027, by rfl⟩ : syracuseStep 2512073 = 1884055) B1884055
theorem B5018861 : Blo 1321479 5018861 := bstep (se 3 (by rfl) ⟨941036, by rfl⟩ : syracuseStep 5018861 = 1882073) B1882073
theorem B4830445 : Blo 1321479 4830445 := bstep (se 3 (by rfl) ⟨905708, by rfl⟩ : syracuseStep 4830445 = 1811417) B1811417
theorem B3175691 : Blo 1321479 3175691 := bstep (se 1 (by rfl) ⟨2381768, by rfl⟩ : syracuseStep 3175691 = 4763537) B4763537
theorem B4461857 : Blo 1321479 4461857 := bstep (se 2 (by rfl) ⟨1673196, by rfl⟩ : syracuseStep 4461857 = 3346393) B3346393
theorem B6354227 : Blo 1321479 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B5363003 : Blo 1321479 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B3347831 : Blo 1321479 3347831 := bstep (se 1 (by rfl) ⟨2510873, by rfl⟩ : syracuseStep 3347831 = 5021747) B5021747
theorem B6698375 : Blo 1321479 6698375 := bstep (se 1 (by rfl) ⟨5023781, by rfl⟩ : syracuseStep 6698375 = 10047563) B10047563
theorem B1488271 : Blo 1321479 1488271 := bstep (se 1 (by rfl) ⟨1116203, by rfl⟩ : syracuseStep 1488271 = 2232407) B2232407
theorem B4765081 : Blo 1321479 4765081 := bstep (se 2 (by rfl) ⟨1786905, by rfl⟩ : syracuseStep 4765081 = 3573811) B3573811
theorem B2823827 : Blo 1321479 2823827 := bstep (se 1 (by rfl) ⟨2117870, by rfl⟩ : syracuseStep 2823827 = 4235741) B4235741
theorem B22582961 : Blo 1321479 22582961 := bstep (se 2 (by rfl) ⟨8468610, by rfl⟩ : syracuseStep 22582961 = 16937221) B16937221
theorem B16307891 : Blo 1321479 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B4462451 : Blo 1321479 4462451 := bstep (se 1 (by rfl) ⟨3346838, by rfl⟩ : syracuseStep 4462451 = 6693677) B6693677
theorem B3766151 : Blo 1321479 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B1488775 : Blo 1321479 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B3766333 : Blo 1321479 3766333 := bstep (se 3 (by rfl) ⟨706187, by rfl⟩ : syracuseStep 3766333 = 1412375) B1412375
theorem B3176567 : Blo 1321479 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B9050285 : Blo 1321479 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B11295035 : Blo 1321479 11295035 := bstep (se 1 (by rfl) ⟨8471276, by rfl⟩ : syracuseStep 11295035 = 16942553) B16942553
theorem B3348823 : Blo 1321479 3348823 := bstep (se 1 (by rfl) ⟨2511617, by rfl⟩ : syracuseStep 3348823 = 5023235) B5023235
theorem B12704147 : Blo 1321479 12704147 := bstep (se 1 (by rfl) ⟨9528110, by rfl⟩ : syracuseStep 12704147 = 19056221) B19056221
theorem B3766675 : Blo 1321479 3766675 := bstep (se 1 (by rfl) ⟨2825006, by rfl⟩ : syracuseStep 3766675 = 5650013) B5650013
theorem B16095773 : Blo 1321479 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B4020769 : Blo 1321479 4020769 := bstep (se 2 (by rfl) ⟨1507788, by rfl⟩ : syracuseStep 4020769 = 3015577) B3015577
theorem B3349127 : Blo 1321479 3349127 := bstep (se 1 (by rfl) ⟨2511845, by rfl⟩ : syracuseStep 3349127 = 5023691) B5023691
theorem B4766465 : Blo 1321479 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B3349259 : Blo 1321479 3349259 := bstep (se 1 (by rfl) ⟨2511944, by rfl⟩ : syracuseStep 3349259 = 5023889) B5023889
theorem B2382635 : Blo 1321479 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B1882939 : Blo 1321479 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B6618077 : Blo 1321479 6618077 := bstep (se 3 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 6618077 = 2481779) B2481779
theorem B27909251 : Blo 1321479 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B2825417 : Blo 1321479 2825417 := bstep (se 2 (by rfl) ⟨1059531, by rfl⟩ : syracuseStep 2825417 = 2119063) B2119063
theorem B1907959 : Blo 1321479 1907959 := bstep (se 1 (by rfl) ⟨1430969, by rfl⟩ : syracuseStep 1907959 = 2861939) B2861939
theorem B3767563 : Blo 1321479 3767563 := bstep (se 1 (by rfl) ⟨2825672, by rfl⟩ : syracuseStep 3767563 = 5651345) B5651345
theorem B4234511 : Blo 1321479 4234511 := bstep (se 1 (by rfl) ⟨3175883, by rfl⟩ : syracuseStep 4234511 = 6351767) B6351767
theorem B3349775 : Blo 1321479 3349775 := bstep (se 1 (by rfl) ⟨2512331, by rfl⟩ : syracuseStep 3349775 = 5024663) B5024663
theorem B5020987 : Blo 1321479 5020987 := bstep (se 1 (by rfl) ⟨3765740, by rfl⟩ : syracuseStep 5020987 = 7531481) B7531481
theorem B6782297 : Blo 1321479 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B7527815 : Blo 1321479 7527815 := bstep (se 1 (by rfl) ⟨5645861, by rfl⟩ : syracuseStep 7527815 = 11291723) B11291723
theorem B3349907 : Blo 1321479 3349907 := bstep (se 1 (by rfl) ⟨2512430, by rfl⟩ : syracuseStep 3349907 = 5024861) B5024861
theorem B6692381 : Blo 1321479 6692381 := bstep (se 3 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 6692381 = 2509643) B2509643
theorem B6782525 : Blo 1321479 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B27508301 : Blo 1321479 27508301 := bstep (se 3 (by rfl) ⟨5157806, by rfl⟩ : syracuseStep 27508301 = 10315613) B10315613
theorem B4292183 : Blo 1321479 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B25419365 : Blo 1321479 25419365 := bstep (se 4 (by rfl) ⟨2383065, by rfl⟩ : syracuseStep 25419365 = 4766131) B4766131
theorem B3014263 : Blo 1321479 3014263 := bstep (se 1 (by rfl) ⟨2260697, by rfl⟩ : syracuseStep 3014263 = 4521395) B4521395
theorem B3768065 : Blo 1321479 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B2973455 : Blo 1321479 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B2973473 : Blo 1321479 2973473 := bstep (se 2 (by rfl) ⟨1115052, by rfl⟩ : syracuseStep 2973473 = 2230105) B2230105
theorem B5021473 : Blo 1321479 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B1982267 : Blo 1321479 1982267 := bstep (se 1 (by rfl) ⟨1486700, by rfl⟩ : syracuseStep 1982267 = 2973401) B2973401
theorem B6356825 : Blo 1321479 6356825 := bstep (se 2 (by rfl) ⟨2383809, by rfl⟩ : syracuseStep 6356825 = 4767619) B4767619
theorem B1982327 : Blo 1321479 1982327 := bstep (se 1 (by rfl) ⟨1486745, by rfl⟩ : syracuseStep 1982327 = 2973491) B2973491
theorem B1982351 : Blo 1321479 1982351 := bstep (se 1 (by rfl) ⟨1486763, by rfl⟩ : syracuseStep 1982351 = 2973527) B2973527
theorem B1982393 : Blo 1321479 1982393 := bstep (se 2 (by rfl) ⟨743397, by rfl⟩ : syracuseStep 1982393 = 1486795) B1486795
theorem B1884169 : Blo 1321479 1884169 := bstep (se 2 (by rfl) ⟨706563, by rfl⟩ : syracuseStep 1884169 = 1413127) B1413127
theorem B1982543 : Blo 1321479 1982543 := bstep (se 1 (by rfl) ⟨1486907, by rfl⟩ : syracuseStep 1982543 = 2973815) B2973815
theorem B4464719 : Blo 1321479 4464719 := bstep (se 1 (by rfl) ⟨3348539, by rfl⟩ : syracuseStep 4464719 = 6697079) B6697079
theorem B5021777 : Blo 1321479 5021777 := bstep (se 2 (by rfl) ⟨1883166, by rfl⟩ : syracuseStep 5021777 = 3766333) B3766333
theorem B6357149 : Blo 1321479 6357149 := bstep (se 3 (by rfl) ⟨1191965, by rfl⟩ : syracuseStep 6357149 = 2383931) B2383931
theorem B1982663 : Blo 1321479 1982663 := bstep (se 1 (by rfl) ⟨1486997, by rfl⟩ : syracuseStep 1982663 = 2973995) B2973995
theorem B1982825 : Blo 1321479 1982825 := bstep (se 2 (by rfl) ⟨743559, by rfl⟩ : syracuseStep 1982825 = 1487119) B1487119
theorem B1982903 : Blo 1321479 1982903 := bstep (se 1 (by rfl) ⟨1487177, by rfl⟩ : syracuseStep 1982903 = 2974355) B2974355
theorem B4465097 : Blo 1321479 4465097 := bstep (se 2 (by rfl) ⟨1674411, by rfl⟩ : syracuseStep 4465097 = 3348823) B3348823
theorem B1982939 : Blo 1321479 1982939 := bstep (se 1 (by rfl) ⟨1487204, by rfl⟩ : syracuseStep 1982939 = 2974409) B2974409
theorem B5022233 : Blo 1321479 5022233 := bstep (se 2 (by rfl) ⟨1883337, by rfl⟩ : syracuseStep 5022233 = 3766675) B3766675
theorem B2974247 : Blo 1321479 2974247 := bstep (se 1 (by rfl) ⟨2230685, by rfl⟩ : syracuseStep 2974247 = 4461371) B4461371
theorem B13238957 : Blo 1321479 13238957 := bstep (se 3 (by rfl) ⟨2482304, by rfl⟩ : syracuseStep 13238957 = 4964609) B4964609
theorem B4465367 : Blo 1321479 4465367 := bstep (se 1 (by rfl) ⟨3349025, by rfl⟩ : syracuseStep 4465367 = 6698051) B6698051
theorem B4768541 : Blo 1321479 4768541 := bstep (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) B1788203
theorem B2974571 : Blo 1321479 2974571 := bstep (se 1 (by rfl) ⟨2230928, by rfl⟩ : syracuseStep 2974571 = 4461857) B4461857
theorem B4236151 : Blo 1321479 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B2974625 : Blo 1321479 2974625 := bstep (se 2 (by rfl) ⟨1115484, by rfl⟩ : syracuseStep 2974625 = 2230969) B2230969
theorem B1983407 : Blo 1321479 1983407 := bstep (se 1 (by rfl) ⟨1487555, by rfl⟩ : syracuseStep 1983407 = 2975111) B2975111
theorem B4465583 : Blo 1321479 4465583 := bstep (se 1 (by rfl) ⟨3349187, by rfl⟩ : syracuseStep 4465583 = 6698375) B6698375
theorem B1983497 : Blo 1321479 1983497 := bstep (se 2 (by rfl) ⟨743811, by rfl⟩ : syracuseStep 1983497 = 1487623) B1487623
theorem B1983527 : Blo 1321479 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B10871927 : Blo 1321479 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B1983611 : Blo 1321479 1983611 := bstep (se 1 (by rfl) ⟨1487708, by rfl⟩ : syracuseStep 1983611 = 2975417) B2975417
theorem B15262937 : Blo 1321479 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B2974967 : Blo 1321479 2974967 := bstep (se 1 (by rfl) ⟨2231225, by rfl⟩ : syracuseStep 2974967 = 4462451) B4462451
theorem B1983737 : Blo 1321479 1983737 := bstep (se 2 (by rfl) ⟨743901, by rfl⟩ : syracuseStep 1983737 = 1487803) B1487803
theorem B1983839 : Blo 1321479 1983839 := bstep (se 1 (by rfl) ⟨1487879, by rfl⟩ : syracuseStep 1983839 = 2975759) B2975759
theorem B3179881 : Blo 1321479 3179881 := bstep (se 2 (by rfl) ⟨1192455, by rfl⟩ : syracuseStep 3179881 = 2384911) B2384911
theorem B1983851 : Blo 1321479 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B7530023 : Blo 1321479 7530023 := bstep (se 1 (by rfl) ⟨5647517, by rfl⟩ : syracuseStep 7530023 = 11295035) B11295035
theorem B1984079 : Blo 1321479 1984079 := bstep (se 1 (by rfl) ⟨1488059, by rfl⟩ : syracuseStep 1984079 = 2976119) B2976119
theorem B5023417 : Blo 1321479 5023417 := bstep (se 2 (by rfl) ⟨1883781, by rfl⟩ : syracuseStep 5023417 = 3767563) B3767563
theorem B1672903 : Blo 1321479 1672903 := bstep (se 1 (by rfl) ⟨1254677, by rfl⟩ : syracuseStep 1672903 = 2509355) B2509355
theorem B1984199 : Blo 1321479 1984199 := bstep (se 1 (by rfl) ⟨1488149, by rfl⟩ : syracuseStep 1984199 = 2976299) B2976299
theorem B9537223 : Blo 1321479 9537223 := bstep (se 1 (by rfl) ⟨7152917, by rfl⟩ : syracuseStep 9537223 = 14305835) B14305835
theorem B7530205 : Blo 1321479 7530205 := bstep (se 3 (by rfl) ⟨1411913, by rfl⟩ : syracuseStep 7530205 = 2823827) B2823827
theorem B6694649 : Blo 1321479 6694649 := bstep (se 2 (by rfl) ⟨2510493, by rfl⟩ : syracuseStep 6694649 = 5020987) B5020987
theorem B2975561 : Blo 1321479 2975561 := bstep (se 2 (by rfl) ⟨1115835, by rfl⟩ : syracuseStep 2975561 = 2231671) B2231671
theorem B1984361 : Blo 1321479 1984361 := bstep (se 2 (by rfl) ⟨744135, by rfl⟩ : syracuseStep 1984361 = 1488271) B1488271
theorem B2230159 : Blo 1321479 2230159 := bstep (se 1 (by rfl) ⟨1672619, by rfl⟩ : syracuseStep 2230159 = 3345239) B3345239
theorem B1984439 : Blo 1321479 1984439 := bstep (se 1 (by rfl) ⟨1488329, by rfl⟩ : syracuseStep 1984439 = 2976659) B2976659
theorem B1984475 : Blo 1321479 1984475 := bstep (se 1 (by rfl) ⟨1488356, by rfl⟩ : syracuseStep 1984475 = 2976713) B2976713
theorem B11290661 : Blo 1321479 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B3868729 : Blo 1321479 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B18606167 : Blo 1321479 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B6695297 : Blo 1321479 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B2861455 : Blo 1321479 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B1984943 : Blo 1321479 1984943 := bstep (se 1 (by rfl) ⟨1488707, by rfl⟩ : syracuseStep 1984943 = 2977415) B2977415
theorem B274958833 : Blo 1321479 274958833 := bstep (se 2 (by rfl) ⟨103109562, by rfl⟩ : syracuseStep 274958833 = 206219125) B206219125
theorem B1985033 : Blo 1321479 1985033 := bstep (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) B1488775
theorem B1321511 : Blo 1321479 1321511 := bstep (se 1 (by rfl) ⟨991133, by rfl⟩ : syracuseStep 1321511 = 1982267) B1982267
theorem B1985063 : Blo 1321479 1985063 := bstep (se 1 (by rfl) ⟨1488797, by rfl⟩ : syracuseStep 1985063 = 2977595) B2977595
theorem B2230841 : Blo 1321479 2230841 := bstep (se 2 (by rfl) ⟨836565, by rfl⟩ : syracuseStep 2230841 = 1673131) B1673131
theorem B4237883 : Blo 1321479 4237883 := bstep (se 1 (by rfl) ⟨3178412, by rfl⟩ : syracuseStep 4237883 = 6356825) B6356825
theorem B1321551 : Blo 1321479 1321551 := bstep (se 1 (by rfl) ⟨991163, by rfl⟩ : syracuseStep 1321551 = 1982327) B1982327
theorem B1321567 : Blo 1321479 1321567 := bstep (se 1 (by rfl) ⟨991175, by rfl⟩ : syracuseStep 1321567 = 1982351) B1982351
theorem B2976353 : Blo 1321479 2976353 := bstep (se 2 (by rfl) ⟨1116132, by rfl⟩ : syracuseStep 2976353 = 2232265) B2232265
theorem B1321595 : Blo 1321479 1321595 := bstep (se 1 (by rfl) ⟨991196, by rfl⟩ : syracuseStep 1321595 = 1982393) B1982393
theorem B1985147 : Blo 1321479 1985147 := bstep (se 1 (by rfl) ⟨1488860, by rfl⟩ : syracuseStep 1985147 = 2977721) B2977721
theorem B1321647 : Blo 1321479 1321647 := bstep (se 1 (by rfl) ⟨991235, by rfl⟩ : syracuseStep 1321647 = 1982471) B1982471
theorem B1321671 : Blo 1321479 1321671 := bstep (se 1 (by rfl) ⟨991253, by rfl⟩ : syracuseStep 1321671 = 1982507) B1982507
theorem B10316489 : Blo 1321479 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B2755271 : Blo 1321479 2755271 := bstep (se 1 (by rfl) ⟨2066453, by rfl⟩ : syracuseStep 2755271 = 4132907) B4132907
theorem B1321691 : Blo 1321479 1321691 := bstep (se 1 (by rfl) ⟨991268, by rfl⟩ : syracuseStep 1321691 = 1982537) B1982537
theorem B1321767 : Blo 1321479 1321767 := bstep (se 1 (by rfl) ⟨991325, by rfl⟩ : syracuseStep 1321767 = 1982651) B1982651
theorem B1321807 : Blo 1321479 1321807 := bstep (se 1 (by rfl) ⟨991355, by rfl⟩ : syracuseStep 1321807 = 1982711) B1982711
theorem B1321823 : Blo 1321479 1321823 := bstep (se 1 (by rfl) ⟨991367, by rfl⟩ : syracuseStep 1321823 = 1982735) B1982735
theorem B3345259 : Blo 1321479 3345259 := bstep (se 1 (by rfl) ⟨2508944, by rfl⟩ : syracuseStep 3345259 = 5017889) B5017889
theorem B1321851 : Blo 1321479 1321851 := bstep (se 1 (by rfl) ⟨991388, by rfl⟩ : syracuseStep 1321851 = 1982777) B1982777
theorem B1321903 : Blo 1321479 1321903 := bstep (se 1 (by rfl) ⟨991427, by rfl⟩ : syracuseStep 1321903 = 1982855) B1982855
theorem B5647279 : Blo 1321479 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B2976695 : Blo 1321479 2976695 := bstep (se 1 (by rfl) ⟨2232521, by rfl⟩ : syracuseStep 2976695 = 4465043) B4465043
theorem B1321927 : Blo 1321479 1321927 := bstep (se 1 (by rfl) ⟨991445, by rfl⟩ : syracuseStep 1321927 = 1982891) B1982891
theorem B1321947 : Blo 1321479 1321947 := bstep (se 1 (by rfl) ⟨991460, by rfl⟩ : syracuseStep 1321947 = 1982921) B1982921
theorem B1322023 : Blo 1321479 1322023 := bstep (se 1 (by rfl) ⟨991517, by rfl⟩ : syracuseStep 1322023 = 1983035) B1983035
theorem B1322063 : Blo 1321479 1322063 := bstep (se 1 (by rfl) ⟨991547, by rfl⟩ : syracuseStep 1322063 = 1983095) B1983095
theorem B1322079 : Blo 1321479 1322079 := bstep (se 1 (by rfl) ⟨991559, by rfl⟩ : syracuseStep 1322079 = 1983119) B1983119
theorem B1322107 : Blo 1321479 1322107 := bstep (se 1 (by rfl) ⟨991580, by rfl⟩ : syracuseStep 1322107 = 1983161) B1983161
theorem B6696107 : Blo 1321479 6696107 := bstep (se 1 (by rfl) ⟨5022080, by rfl⟩ : syracuseStep 6696107 = 10044161) B10044161
theorem B1322159 : Blo 1321479 1322159 := bstep (se 1 (by rfl) ⟨991619, by rfl⟩ : syracuseStep 1322159 = 1983239) B1983239
theorem B8047811 : Blo 1321479 8047811 := bstep (se 1 (by rfl) ⟨6035858, by rfl⟩ : syracuseStep 8047811 = 12071717) B12071717
theorem B2510023 : Blo 1321479 2510023 := bstep (se 1 (by rfl) ⟨1882517, by rfl⟩ : syracuseStep 2510023 = 3765035) B3765035
theorem B1322183 : Blo 1321479 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1322203 : Blo 1321479 1322203 := bstep (se 1 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 1322203 = 1983305) B1983305
theorem B2231543 : Blo 1321479 2231543 := bstep (se 1 (by rfl) ⟨1673657, by rfl⟩ : syracuseStep 2231543 = 3347315) B3347315
theorem B16076069 : Blo 1321479 16076069 := bstep (se 4 (by rfl) ⟨1507131, by rfl⟩ : syracuseStep 16076069 = 3014263) B3014263
theorem B1322279 : Blo 1321479 1322279 := bstep (se 1 (by rfl) ⟨991709, by rfl⟩ : syracuseStep 1322279 = 1983419) B1983419
theorem B1322319 : Blo 1321479 1322319 := bstep (se 1 (by rfl) ⟨991739, by rfl⟩ : syracuseStep 1322319 = 1983479) B1983479
theorem B2010463 : Blo 1321479 2010463 := bstep (se 1 (by rfl) ⟨1507847, by rfl⟩ : syracuseStep 2010463 = 3015695) B3015695
theorem B1322335 : Blo 1321479 1322335 := bstep (se 1 (by rfl) ⟨991751, by rfl⟩ : syracuseStep 1322335 = 1983503) B1983503
theorem B1322363 : Blo 1321479 1322363 := bstep (se 1 (by rfl) ⟨991772, by rfl⟩ : syracuseStep 1322363 = 1983545) B1983545
theorem B5361025 : Blo 1321479 5361025 := bstep (se 2 (by rfl) ⟨2010384, by rfl⟩ : syracuseStep 5361025 = 4020769) B4020769
theorem B1322415 : Blo 1321479 1322415 := bstep (se 1 (by rfl) ⟨991811, by rfl⟩ : syracuseStep 1322415 = 1983623) B1983623
theorem B1322439 : Blo 1321479 1322439 := bstep (se 1 (by rfl) ⟨991829, by rfl⟩ : syracuseStep 1322439 = 1983659) B1983659
theorem B10464713 : Blo 1321479 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B1322459 : Blo 1321479 1322459 := bstep (se 1 (by rfl) ⟨991844, by rfl⟩ : syracuseStep 1322459 = 1983689) B1983689
theorem B3345907 : Blo 1321479 3345907 := bstep (se 1 (by rfl) ⟨2509430, by rfl⟩ : syracuseStep 3345907 = 5018861) B5018861
theorem B2977289 : Blo 1321479 2977289 := bstep (se 2 (by rfl) ⟨1116483, by rfl⟩ : syracuseStep 2977289 = 2232967) B2232967
theorem B1322535 : Blo 1321479 1322535 := bstep (se 1 (by rfl) ⟨991901, by rfl⟩ : syracuseStep 1322535 = 1983803) B1983803
theorem B3575335 : Blo 1321479 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1322575 : Blo 1321479 1322575 := bstep (se 1 (by rfl) ⟨991931, by rfl⟩ : syracuseStep 1322575 = 1983863) B1983863
theorem B2231887 : Blo 1321479 2231887 := bstep (se 1 (by rfl) ⟨1673915, by rfl⟩ : syracuseStep 2231887 = 3347831) B3347831
theorem B1322591 : Blo 1321479 1322591 := bstep (se 1 (by rfl) ⟨991943, by rfl⟩ : syracuseStep 1322591 = 1983887) B1983887
theorem B4460129 : Blo 1321479 4460129 := bstep (se 2 (by rfl) ⟨1672548, by rfl⟩ : syracuseStep 4460129 = 3345097) B3345097
theorem B1322619 : Blo 1321479 1322619 := bstep (se 1 (by rfl) ⟨991964, by rfl⟩ : syracuseStep 1322619 = 1983929) B1983929
theorem B6696593 : Blo 1321479 6696593 := bstep (se 2 (by rfl) ⟨2511222, by rfl⟩ : syracuseStep 6696593 = 5022445) B5022445
theorem B1322671 : Blo 1321479 1322671 := bstep (se 1 (by rfl) ⟨992003, by rfl⟩ : syracuseStep 1322671 = 1984007) B1984007
theorem B1322695 : Blo 1321479 1322695 := bstep (se 1 (by rfl) ⟨992021, by rfl⟩ : syracuseStep 1322695 = 1984043) B1984043
theorem B1322715 : Blo 1321479 1322715 := bstep (se 1 (by rfl) ⟨992036, by rfl⟩ : syracuseStep 1322715 = 1984073) B1984073
theorem B2510585 : Blo 1321479 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B1322791 : Blo 1321479 1322791 := bstep (se 1 (by rfl) ⟨992093, by rfl⟩ : syracuseStep 1322791 = 1984187) B1984187
theorem B5730115 : Blo 1321479 5730115 := bstep (se 1 (by rfl) ⟨4297586, by rfl⟩ : syracuseStep 5730115 = 8595173) B8595173
theorem B2232137 : Blo 1321479 2232137 := bstep (se 2 (by rfl) ⟨837051, by rfl⟩ : syracuseStep 2232137 = 1674103) B1674103
theorem B1322831 : Blo 1321479 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B1486687 : Blo 1321479 1486687 := bstep (se 1 (by rfl) ⟨1115015, by rfl⟩ : syracuseStep 1486687 = 2230031) B2230031
theorem B1322847 : Blo 1321479 1322847 := bstep (se 1 (by rfl) ⟨992135, by rfl⟩ : syracuseStep 1322847 = 1984271) B1984271
theorem B2977631 : Blo 1321479 2977631 := bstep (se 1 (by rfl) ⟨2233223, by rfl⟩ : syracuseStep 2977631 = 4466447) B4466447
theorem B5648237 : Blo 1321479 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B1322875 : Blo 1321479 1322875 := bstep (se 1 (by rfl) ⟨992156, by rfl⟩ : syracuseStep 1322875 = 1984313) B1984313
theorem B2510767 : Blo 1321479 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B1322927 : Blo 1321479 1322927 := bstep (se 1 (by rfl) ⟨992195, by rfl⟩ : syracuseStep 1322927 = 1984391) B1984391
theorem B1322951 : Blo 1321479 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B1322971 : Blo 1321479 1322971 := bstep (se 1 (by rfl) ⟨992228, by rfl⟩ : syracuseStep 1322971 = 1984457) B1984457
theorem B2977811 : Blo 1321479 2977811 := bstep (se 1 (by rfl) ⟨2233358, by rfl⟩ : syracuseStep 2977811 = 4466717) B4466717
theorem B1323047 : Blo 1321479 1323047 := bstep (se 1 (by rfl) ⟨992285, by rfl⟩ : syracuseStep 1323047 = 1984571) B1984571
theorem B42922061 : Blo 1321479 42922061 := bstep (se 3 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 42922061 = 16095773) B16095773
theorem B2117711 : Blo 1321479 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B1323087 : Blo 1321479 1323087 := bstep (se 1 (by rfl) ⟨992315, by rfl⟩ : syracuseStep 1323087 = 1984631) B1984631
theorem B1323103 : Blo 1321479 1323103 := bstep (se 1 (by rfl) ⟨992327, by rfl⟩ : syracuseStep 1323103 = 1984655) B1984655
theorem B6033523 : Blo 1321479 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B1323131 : Blo 1321479 1323131 := bstep (se 1 (by rfl) ⟨992348, by rfl⟩ : syracuseStep 1323131 = 1984697) B1984697
theorem B1323183 : Blo 1321479 1323183 := bstep (se 1 (by rfl) ⟨992387, by rfl⟩ : syracuseStep 1323183 = 1984775) B1984775
theorem B1487047 : Blo 1321479 1487047 := bstep (se 1 (by rfl) ⟨1115285, by rfl⟩ : syracuseStep 1487047 = 2230571) B2230571
theorem B1323207 : Blo 1321479 1323207 := bstep (se 1 (by rfl) ⟨992405, by rfl⟩ : syracuseStep 1323207 = 1984811) B1984811
theorem B1323227 : Blo 1321479 1323227 := bstep (se 1 (by rfl) ⟨992420, by rfl⟩ : syracuseStep 1323227 = 1984841) B1984841
theorem B2232569 : Blo 1321479 2232569 := bstep (se 2 (by rfl) ⟨837213, by rfl⟩ : syracuseStep 2232569 = 1674427) B1674427
theorem B1323303 : Blo 1321479 1323303 := bstep (se 1 (by rfl) ⟨992477, by rfl⟩ : syracuseStep 1323303 = 1984955) B1984955
theorem B2543945 : Blo 1321479 2543945 := bstep (se 2 (by rfl) ⟨953979, by rfl⟩ : syracuseStep 2543945 = 1907959) B1907959
theorem B1323343 : Blo 1321479 1323343 := bstep (se 1 (by rfl) ⟨992507, by rfl⟩ : syracuseStep 1323343 = 1985015) B1985015
theorem B1323359 : Blo 1321479 1323359 := bstep (se 1 (by rfl) ⟨992519, by rfl⟩ : syracuseStep 1323359 = 1985039) B1985039
theorem B1323387 : Blo 1321479 1323387 := bstep (se 1 (by rfl) ⟨992540, by rfl⟩ : syracuseStep 1323387 = 1985081) B1985081
theorem B2232751 : Blo 1321479 2232751 := bstep (se 1 (by rfl) ⟨1674563, by rfl⟩ : syracuseStep 2232751 = 3349127) B3349127
theorem B1323439 : Blo 1321479 1323439 := bstep (se 1 (by rfl) ⟨992579, by rfl⟩ : syracuseStep 1323439 = 1985159) B1985159
theorem B1323463 : Blo 1321479 1323463 := bstep (se 1 (by rfl) ⟨992597, by rfl⟩ : syracuseStep 1323463 = 1985195) B1985195
theorem B5018057 : Blo 1321479 5018057 := bstep (se 2 (by rfl) ⟨1881771, by rfl⟩ : syracuseStep 5018057 = 3763543) B3763543
theorem B5362157 : Blo 1321479 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B2232839 : Blo 1321479 2232839 := bstep (se 1 (by rfl) ⟨1674629, by rfl⟩ : syracuseStep 2232839 = 3349259) B3349259
theorem B6353441 : Blo 1321479 6353441 := bstep (se 2 (by rfl) ⟨2382540, by rfl⟩ : syracuseStep 6353441 = 4765081) B4765081
theorem B3347041 : Blo 1321479 3347041 := bstep (se 2 (by rfl) ⟨1255140, by rfl⟩ : syracuseStep 3347041 = 2510281) B2510281
theorem B3764875 : Blo 1321479 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B4412051 : Blo 1321479 4412051 := bstep (se 1 (by rfl) ⟨3309038, by rfl⟩ : syracuseStep 4412051 = 6618077) B6618077
theorem B21435137 : Blo 1321479 21435137 := bstep (se 2 (by rfl) ⟨8038176, by rfl⟩ : syracuseStep 21435137 = 16076353) B16076353
theorem B20345651 : Blo 1321479 20345651 := bstep (se 1 (by rfl) ⟨15259238, by rfl⟩ : syracuseStep 20345651 = 30518477) B30518477
theorem B2823007 : Blo 1321479 2823007 := bstep (se 1 (by rfl) ⟨2117255, by rfl⟩ : syracuseStep 2823007 = 4234511) B4234511
theorem B2233183 : Blo 1321479 2233183 := bstep (se 1 (by rfl) ⟨1674887, by rfl⟩ : syracuseStep 2233183 = 3349775) B3349775
theorem B5018543 : Blo 1321479 5018543 := bstep (se 1 (by rfl) ⟨3763907, by rfl⟩ : syracuseStep 5018543 = 7527815) B7527815
theorem B2233271 : Blo 1321479 2233271 := bstep (se 1 (by rfl) ⟨1674953, by rfl⟩ : syracuseStep 2233271 = 3349907) B3349907
theorem B4461587 : Blo 1321479 4461587 := bstep (se 1 (by rfl) ⟨3346190, by rfl⟩ : syracuseStep 4461587 = 6692381) B6692381
theorem B1487911 : Blo 1321479 1487911 := bstep (se 1 (by rfl) ⟨1115933, by rfl⟩ : syracuseStep 1487911 = 2231867) B2231867
theorem B18338867 : Blo 1321479 18338867 := bstep (se 1 (by rfl) ⟨13754150, by rfl⟩ : syracuseStep 18338867 = 27508301) B27508301
theorem B16946243 : Blo 1321479 16946243 := bstep (se 1 (by rfl) ⟨12709682, by rfl⟩ : syracuseStep 16946243 = 25419365) B25419365
theorem B7533647 : Blo 1321479 7533647 := bstep (se 1 (by rfl) ⟨5650235, by rfl⟩ : syracuseStep 7533647 = 11300471) B11300471
theorem B2512043 : Blo 1321479 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B4461911 : Blo 1321479 4461911 := bstep (se 1 (by rfl) ⟨3346433, by rfl⟩ : syracuseStep 4461911 = 6692867) B6692867
theorem B2512271 : Blo 1321479 2512271 := bstep (se 1 (by rfl) ⟨1884203, by rfl⟩ : syracuseStep 2512271 = 3768407) B3768407
theorem B3347993 : Blo 1321479 3347993 := bstep (se 2 (by rfl) ⟨1255497, by rfl⟩ : syracuseStep 3347993 = 2510995) B2510995
theorem B16938557 : Blo 1321479 16938557 := bstep (se 3 (by rfl) ⟨3175979, by rfl⟩ : syracuseStep 16938557 = 6351959) B6351959
theorem B10729057 : Blo 1321479 10729057 := bstep (se 2 (by rfl) ⟨4023396, by rfl⟩ : syracuseStep 10729057 = 8046793) B8046793
theorem B3815111 : Blo 1321479 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B3176135 : Blo 1321479 3176135 := bstep (se 1 (by rfl) ⟨2382101, by rfl⟩ : syracuseStep 3176135 = 4764203) B4764203
theorem B5019347 : Blo 1321479 5019347 := bstep (se 1 (by rfl) ⟨3764510, by rfl⟩ : syracuseStep 5019347 = 7529021) B7529021
theorem B12056363 : Blo 1321479 12056363 := bstep (se 1 (by rfl) ⟨9042272, by rfl⟩ : syracuseStep 12056363 = 18084545) B18084545
theorem B6698861 : Blo 1321479 6698861 := bstep (se 3 (by rfl) ⟨1256036, by rfl⟩ : syracuseStep 6698861 = 2512073) B2512073
theorem B18102209 : Blo 1321479 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B6699023 : Blo 1321479 6699023 := bstep (se 1 (by rfl) ⟨5024267, by rfl⟩ : syracuseStep 6699023 = 10048535) B10048535
theorem B3348499 : Blo 1321479 3348499 := bstep (se 1 (by rfl) ⟨2511374, by rfl⟩ : syracuseStep 3348499 = 5022749) B5022749
theorem B8468509 : Blo 1321479 8468509 := bstep (se 3 (by rfl) ⟨1587845, by rfl⟩ : syracuseStep 8468509 = 3175691) B3175691
theorem B18086125 : Blo 1321479 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B61937905 : Blo 1321479 61937905 := bstep (se 2 (by rfl) ⟨23226714, by rfl⟩ : syracuseStep 61937905 = 46453429) B46453429
theorem B4462991 : Blo 1321479 4462991 := bstep (se 1 (by rfl) ⟨3347243, by rfl⟩ : syracuseStep 4462991 = 6694487) B6694487
theorem B15055307 : Blo 1321479 15055307 := bstep (se 1 (by rfl) ⟨11291480, by rfl⟩ : syracuseStep 15055307 = 22582961) B22582961
theorem B25762373 : Blo 1321479 25762373 := bstep (se 4 (by rfl) ⟨2415222, by rfl⟩ : syracuseStep 25762373 = 4830445) B4830445
theorem B4766305 : Blo 1321479 4766305 := bstep (se 2 (by rfl) ⟨1787364, by rfl⟩ : syracuseStep 4766305 = 3574729) B3574729
theorem B4463315 : Blo 1321479 4463315 := bstep (se 1 (by rfl) ⟨3347486, by rfl⟩ : syracuseStep 4463315 = 6694973) B6694973
theorem B7150409 : Blo 1321479 7150409 := bstep (se 2 (by rfl) ⟨2681403, by rfl⟩ : syracuseStep 7150409 = 5362807) B5362807
theorem B8469431 : Blo 1321479 8469431 := bstep (se 1 (by rfl) ⟨6352073, by rfl⟩ : syracuseStep 8469431 = 12704147) B12704147
theorem B3349583 : Blo 1321479 3349583 := bstep (se 1 (by rfl) ⟨2512187, by rfl⟩ : syracuseStep 3349583 = 5024375) B5024375
theorem B3177643 : Blo 1321479 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B8477891 : Blo 1321479 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B1588423 : Blo 1321479 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B8592655 : Blo 1321479 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B7536037 : Blo 1321479 7536037 := bstep (se 4 (by rfl) ⟨706503, by rfl⟩ : syracuseStep 7536037 = 1413007) B1413007
theorem B1883611 : Blo 1321479 1883611 := bstep (se 1 (by rfl) ⟨1412708, by rfl⟩ : syracuseStep 1883611 = 2825417) B2825417
theorem B9051709 : Blo 1321479 9051709 := bstep (se 3 (by rfl) ⟨1697195, by rfl⟩ : syracuseStep 9051709 = 3394391) B3394391
theorem B2973383 : Blo 1321479 2973383 := bstep (se 1 (by rfl) ⟨2230037, by rfl⟩ : syracuseStep 2973383 = 4460075) B4460075
theorem B4521683 : Blo 1321479 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B1982303 : Blo 1321479 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B1982315 : Blo 1321479 1982315 := bstep (se 1 (by rfl) ⟨1486736, by rfl⟩ : syracuseStep 1982315 = 2973473) B2973473
theorem B4464503 : Blo 1321479 4464503 := bstep (se 1 (by rfl) ⟨3348377, by rfl⟩ : syracuseStep 4464503 = 6696755) B6696755
theorem B8470433 : Blo 1321479 8470433 := bstep (se 2 (by rfl) ⟨3176412, by rfl⟩ : syracuseStep 8470433 = 6352825) B6352825
theorem B8470457 : Blo 1321479 8470457 := bstep (se 2 (by rfl) ⟨3176421, by rfl⟩ : syracuseStep 8470457 = 6352843) B6352843
theorem B4464665 : Blo 1321479 4464665 := bstep (se 2 (by rfl) ⟨1674249, by rfl⟩ : syracuseStep 4464665 = 3348499) B3348499
theorem B28614707 : Blo 1321479 28614707 := bstep (se 1 (by rfl) ⟨21461030, by rfl⟩ : syracuseStep 28614707 = 42922061) B42922061
theorem B8044697 : Blo 1321479 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B1982729 : Blo 1321479 1982729 := bstep (se 2 (by rfl) ⟨743523, by rfl⟩ : syracuseStep 1982729 = 1487047) B1487047
theorem B82583873 : Blo 1321479 82583873 := bstep (se 2 (by rfl) ⟨30968952, by rfl⟩ : syracuseStep 82583873 = 61937905) B61937905
theorem B4235627 : Blo 1321479 4235627 := bstep (se 1 (by rfl) ⟨3176720, by rfl⟩ : syracuseStep 4235627 = 6353441) B6353441
theorem B1982831 : Blo 1321479 1982831 := bstep (se 1 (by rfl) ⟨1487123, by rfl⟩ : syracuseStep 1982831 = 2974247) B2974247
theorem B2941367 : Blo 1321479 2941367 := bstep (se 1 (by rfl) ⟨2206025, by rfl⟩ : syracuseStep 2941367 = 4412051) B4412051
theorem B3179027 : Blo 1321479 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B1983047 : Blo 1321479 1983047 := bstep (se 1 (by rfl) ⟨1487285, by rfl⟩ : syracuseStep 1983047 = 2974571) B2974571
theorem B1983083 : Blo 1321479 1983083 := bstep (se 1 (by rfl) ⟨1487312, by rfl⟩ : syracuseStep 1983083 = 2974625) B2974625
theorem B2974391 : Blo 1321479 2974391 := bstep (se 1 (by rfl) ⟨2230793, by rfl⟩ : syracuseStep 2974391 = 4461587) B4461587
theorem B11297495 : Blo 1321479 11297495 := bstep (se 1 (by rfl) ⟨8473121, by rfl⟩ : syracuseStep 11297495 = 16946243) B16946243
theorem B5022431 : Blo 1321479 5022431 := bstep (se 1 (by rfl) ⟨3766823, by rfl⟩ : syracuseStep 5022431 = 7533647) B7533647
theorem B10175291 : Blo 1321479 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1983311 : Blo 1321479 1983311 := bstep (se 1 (by rfl) ⟨1487483, by rfl⟩ : syracuseStep 1983311 = 2974967) B2974967
theorem B6783853 : Blo 1321479 6783853 := bstep (se 3 (by rfl) ⟨1271972, by rfl⟩ : syracuseStep 6783853 = 2543945) B2543945
theorem B2974607 : Blo 1321479 2974607 := bstep (se 1 (by rfl) ⟨2230955, by rfl⟩ : syracuseStep 2974607 = 4461911) B4461911
theorem B8037575 : Blo 1321479 8037575 := bstep (se 1 (by rfl) ⟨6028181, by rfl⟩ : syracuseStep 8037575 = 12056363) B12056363
theorem B1983707 : Blo 1321479 1983707 := bstep (se 1 (by rfl) ⟨1487780, by rfl⟩ : syracuseStep 1983707 = 2975561) B2975561
theorem B7529705 : Blo 1321479 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B4465907 : Blo 1321479 4465907 := bstep (se 1 (by rfl) ⟨3349430, by rfl⟩ : syracuseStep 4465907 = 6698861) B6698861
theorem B4466015 : Blo 1321479 4466015 := bstep (se 1 (by rfl) ⟨3349511, by rfl⟩ : syracuseStep 4466015 = 6699023) B6699023
theorem B1983881 : Blo 1321479 1983881 := bstep (se 2 (by rfl) ⟨743955, by rfl⟩ : syracuseStep 1983881 = 1487911) B1487911
theorem B12404111 : Blo 1321479 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B4236857 : Blo 1321479 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B2975327 : Blo 1321479 2975327 := bstep (se 1 (by rfl) ⟨2231495, by rfl⟩ : syracuseStep 2975327 = 4462991) B4462991
theorem B10036871 : Blo 1321479 10036871 := bstep (se 1 (by rfl) ⟨7527653, by rfl⟩ : syracuseStep 10036871 = 15055307) B15055307
theorem B1984235 : Blo 1321479 1984235 := bstep (se 1 (by rfl) ⟨1488176, by rfl⟩ : syracuseStep 1984235 = 2976353) B2976353
theorem B1836847 : Blo 1321479 1836847 := bstep (se 1 (by rfl) ⟨1377635, by rfl⟩ : syracuseStep 1836847 = 2755271) B2755271
theorem B2975543 : Blo 1321479 2975543 := bstep (se 1 (by rfl) ⟨2231657, by rfl⟩ : syracuseStep 2975543 = 4463315) B4463315
theorem B16959365 : Blo 1321479 16959365 := bstep (se 4 (by rfl) ⟨1589940, by rfl⟩ : syracuseStep 16959365 = 3179881) B3179881
theorem B5646287 : Blo 1321479 5646287 := bstep (se 1 (by rfl) ⟨4234715, by rfl⟩ : syracuseStep 5646287 = 8469431) B8469431
theorem B1984463 : Blo 1321479 1984463 := bstep (se 1 (by rfl) ⟨1488347, by rfl⟩ : syracuseStep 1984463 = 2976695) B2976695
theorem B12068945 : Blo 1321479 12068945 := bstep (se 2 (by rfl) ⟨4525854, by rfl⟩ : syracuseStep 12068945 = 9051709) B9051709
theorem B2975849 : Blo 1321479 2975849 := bstep (se 2 (by rfl) ⟨1115943, by rfl⟩ : syracuseStep 2975849 = 2231887) B2231887
theorem B14305409 : Blo 1321479 14305409 := bstep (se 2 (by rfl) ⟨5364528, by rfl⟩ : syracuseStep 14305409 = 10729057) B10729057
theorem B10717379 : Blo 1321479 10717379 := bstep (se 1 (by rfl) ⟨8038034, by rfl⟩ : syracuseStep 10717379 = 16076069) B16076069
theorem B2230537 : Blo 1321479 2230537 := bstep (se 2 (by rfl) ⟨836451, by rfl⟩ : syracuseStep 2230537 = 1672903) B1672903
theorem B12716297 : Blo 1321479 12716297 := bstep (se 2 (by rfl) ⟨4768611, by rfl⟩ : syracuseStep 12716297 = 9537223) B9537223
theorem B1984859 : Blo 1321479 1984859 := bstep (se 1 (by rfl) ⟨1488644, by rfl⟩ : syracuseStep 1984859 = 2977289) B2977289
theorem B1673723 : Blo 1321479 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B1321535 : Blo 1321479 1321535 := bstep (se 1 (by rfl) ⟨991151, by rfl⟩ : syracuseStep 1321535 = 1982303) B1982303
theorem B1985087 : Blo 1321479 1985087 := bstep (se 1 (by rfl) ⟨1488815, by rfl⟩ : syracuseStep 1985087 = 2977631) B2977631
theorem B1321543 : Blo 1321479 1321543 := bstep (se 1 (by rfl) ⟨991157, by rfl⟩ : syracuseStep 1321543 = 1982315) B1982315
theorem B2976335 : Blo 1321479 2976335 := bstep (se 1 (by rfl) ⟨2232251, by rfl⟩ : syracuseStep 2976335 = 4464503) B4464503
theorem B5646955 : Blo 1321479 5646955 := bstep (se 1 (by rfl) ⟨4235216, by rfl⟩ : syracuseStep 5646955 = 8470433) B8470433
theorem B5646971 : Blo 1321479 5646971 := bstep (se 1 (by rfl) ⟨4235228, by rfl⟩ : syracuseStep 5646971 = 8470457) B8470457
theorem B1985207 : Blo 1321479 1985207 := bstep (se 1 (by rfl) ⟨1488905, by rfl⟩ : syracuseStep 1985207 = 2977811) B2977811
theorem B11291345 : Blo 1321479 11291345 := bstep (se 2 (by rfl) ⟨4234254, by rfl⟩ : syracuseStep 11291345 = 8468509) B8468509
theorem B1321695 : Blo 1321479 1321695 := bstep (se 1 (by rfl) ⟨991271, by rfl⟩ : syracuseStep 1321695 = 1982543) B1982543
theorem B2976479 : Blo 1321479 2976479 := bstep (se 1 (by rfl) ⟨2232359, by rfl⟩ : syracuseStep 2976479 = 4464719) B4464719
theorem B4238099 : Blo 1321479 4238099 := bstep (se 1 (by rfl) ⟨3178574, by rfl⟩ : syracuseStep 4238099 = 6357149) B6357149
theorem B1321775 : Blo 1321479 1321775 := bstep (se 1 (by rfl) ⟨991331, by rfl⟩ : syracuseStep 1321775 = 1982663) B1982663
theorem B5647229 : Blo 1321479 5647229 := bstep (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) B2117711
theorem B1321883 : Blo 1321479 1321883 := bstep (se 1 (by rfl) ⟨991412, by rfl⟩ : syracuseStep 1321883 = 1982825) B1982825
theorem B1321935 : Blo 1321479 1321935 := bstep (se 1 (by rfl) ⟨991451, by rfl⟩ : syracuseStep 1321935 = 1982903) B1982903
theorem B3345371 : Blo 1321479 3345371 := bstep (se 1 (by rfl) ⟨2509028, by rfl⟩ : syracuseStep 3345371 = 5018057) B5018057
theorem B2976731 : Blo 1321479 2976731 := bstep (se 1 (by rfl) ⟨2232548, by rfl⟩ : syracuseStep 2976731 = 4465097) B4465097
theorem B1321959 : Blo 1321479 1321959 := bstep (se 1 (by rfl) ⟨991469, by rfl⟩ : syracuseStep 1321959 = 1982939) B1982939
theorem B8825971 : Blo 1321479 8825971 := bstep (se 1 (by rfl) ⟨6619478, by rfl⟩ : syracuseStep 8825971 = 13238957) B13238957
theorem B2976911 : Blo 1321479 2976911 := bstep (se 1 (by rfl) ⟨2232683, by rfl⟩ : syracuseStep 2976911 = 4465367) B4465367
theorem B14290091 : Blo 1321479 14290091 := bstep (se 1 (by rfl) ⟨10717568, by rfl⟩ : syracuseStep 14290091 = 21435137) B21435137
theorem B2977001 : Blo 1321479 2977001 := bstep (se 2 (by rfl) ⟨1116375, by rfl⟩ : syracuseStep 2977001 = 2232751) B2232751
theorem B3345695 : Blo 1321479 3345695 := bstep (se 1 (by rfl) ⟨2509271, by rfl⟩ : syracuseStep 3345695 = 5018543) B5018543
theorem B1322271 : Blo 1321479 1322271 := bstep (se 1 (by rfl) ⟨991703, by rfl⟩ : syracuseStep 1322271 = 1983407) B1983407
theorem B2977055 : Blo 1321479 2977055 := bstep (se 1 (by rfl) ⟨2232791, by rfl⟩ : syracuseStep 2977055 = 4465583) B4465583
theorem B366611777 : Blo 1321479 366611777 := bstep (se 2 (by rfl) ⟨137479416, by rfl⟩ : syracuseStep 366611777 = 274958833) B274958833
theorem B1322331 : Blo 1321479 1322331 := bstep (se 1 (by rfl) ⟨991748, by rfl⟩ : syracuseStep 1322331 = 1983497) B1983497
theorem B1322351 : Blo 1321479 1322351 := bstep (se 1 (by rfl) ⟨991763, by rfl⟩ : syracuseStep 1322351 = 1983527) B1983527
theorem B12225911 : Blo 1321479 12225911 := bstep (se 1 (by rfl) ⟨9169433, by rfl⟩ : syracuseStep 12225911 = 18338867) B18338867
theorem B1322407 : Blo 1321479 1322407 := bstep (se 1 (by rfl) ⟨991805, by rfl⟩ : syracuseStep 1322407 = 1983611) B1983611
theorem B1674695 : Blo 1321479 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B1322491 : Blo 1321479 1322491 := bstep (se 1 (by rfl) ⟨991868, by rfl⟩ : syracuseStep 1322491 = 1983737) B1983737
theorem B1322559 : Blo 1321479 1322559 := bstep (se 1 (by rfl) ⟨991919, by rfl⟩ : syracuseStep 1322559 = 1983839) B1983839
theorem B1322567 : Blo 1321479 1322567 := bstep (se 1 (by rfl) ⟨991925, by rfl⟩ : syracuseStep 1322567 = 1983851) B1983851
theorem B1674847 : Blo 1321479 1674847 := bstep (se 1 (by rfl) ⟨1256135, by rfl⟩ : syracuseStep 1674847 = 2512271) B2512271
theorem B2231995 : Blo 1321479 2231995 := bstep (se 1 (by rfl) ⟨1673996, by rfl⟩ : syracuseStep 2231995 = 3347993) B3347993
theorem B11292371 : Blo 1321479 11292371 := bstep (se 1 (by rfl) ⟨8469278, by rfl⟩ : syracuseStep 11292371 = 16938557) B16938557
theorem B1322719 : Blo 1321479 1322719 := bstep (se 1 (by rfl) ⟨992039, by rfl⟩ : syracuseStep 1322719 = 1984079) B1984079
theorem B3764009 : Blo 1321479 3764009 := bstep (se 2 (by rfl) ⟨1411503, by rfl⟩ : syracuseStep 3764009 = 2823007) B2823007
theorem B2977577 : Blo 1321479 2977577 := bstep (se 2 (by rfl) ⟨1116591, by rfl⟩ : syracuseStep 2977577 = 2233183) B2233183
theorem B2543407 : Blo 1321479 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B2117423 : Blo 1321479 2117423 := bstep (se 1 (by rfl) ⟨1588067, by rfl⟩ : syracuseStep 2117423 = 3176135) B3176135
theorem B1322799 : Blo 1321479 1322799 := bstep (se 1 (by rfl) ⟨992099, by rfl⟩ : syracuseStep 1322799 = 1984199) B1984199
theorem B3346231 : Blo 1321479 3346231 := bstep (se 1 (by rfl) ⟨2509673, by rfl⟩ : syracuseStep 3346231 = 5019347) B5019347
theorem B4460345 : Blo 1321479 4460345 := bstep (se 2 (by rfl) ⟨1672629, by rfl⟩ : syracuseStep 4460345 = 3345259) B3345259
theorem B5648201 : Blo 1321479 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B1322907 : Blo 1321479 1322907 := bstep (se 1 (by rfl) ⟨992180, by rfl⟩ : syracuseStep 1322907 = 1984361) B1984361
theorem B14299085 : Blo 1321479 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B1322959 : Blo 1321479 1322959 := bstep (se 1 (by rfl) ⟨992219, by rfl⟩ : syracuseStep 1322959 = 1984439) B1984439
theorem B1322983 : Blo 1321479 1322983 := bstep (se 1 (by rfl) ⟨992237, by rfl⟩ : syracuseStep 1322983 = 1984475) B1984475
theorem B3346697 : Blo 1321479 3346697 := bstep (se 2 (by rfl) ⟨1255011, by rfl⟩ : syracuseStep 3346697 = 2510023) B2510023
theorem B2117897 : Blo 1321479 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B1323295 : Blo 1321479 1323295 := bstep (se 1 (by rfl) ⟨992471, by rfl⟩ : syracuseStep 1323295 = 1984943) B1984943
theorem B1323355 : Blo 1321479 1323355 := bstep (se 1 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 1323355 = 1985033) B1985033
theorem B11456873 : Blo 1321479 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B1323375 : Blo 1321479 1323375 := bstep (se 1 (by rfl) ⟨992531, by rfl⟩ : syracuseStep 1323375 = 1985063) B1985063
theorem B1487227 : Blo 1321479 1487227 := bstep (se 1 (by rfl) ⟨1115420, by rfl⟩ : syracuseStep 1487227 = 2230841) B2230841
theorem B17174915 : Blo 1321479 17174915 := bstep (se 1 (by rfl) ⟨12881186, by rfl⟩ : syracuseStep 17174915 = 25762373) B25762373
theorem B1323431 : Blo 1321479 1323431 := bstep (se 1 (by rfl) ⟨992573, by rfl⟩ : syracuseStep 1323431 = 1985147) B1985147
theorem B7148033 : Blo 1321479 7148033 := bstep (se 2 (by rfl) ⟨2680512, by rfl⟩ : syracuseStep 7148033 = 5361025) B5361025
theorem B10048049 : Blo 1321479 10048049 := bstep (se 2 (by rfl) ⟨3768018, by rfl⟩ : syracuseStep 10048049 = 7536037) B7536037
theorem B2511481 : Blo 1321479 2511481 := bstep (se 2 (by rfl) ⟨941805, by rfl⟩ : syracuseStep 2511481 = 1883611) B1883611
theorem B4461209 : Blo 1321479 4461209 := bstep (se 2 (by rfl) ⟨1672953, by rfl⟩ : syracuseStep 4461209 = 3345907) B3345907
theorem B193090229 : Blo 1321479 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B2233055 : Blo 1321479 2233055 := bstep (se 1 (by rfl) ⟨1674791, by rfl⟩ : syracuseStep 2233055 = 3349583) B3349583
theorem B1487695 : Blo 1321479 1487695 := bstep (se 1 (by rfl) ⟨1115771, by rfl⟩ : syracuseStep 1487695 = 2231543) B2231543
theorem B6697889 : Blo 1321479 6697889 := bstep (se 2 (by rfl) ⟨2511708, by rfl⟩ : syracuseStep 6697889 = 5023417) B5023417
theorem B10040273 : Blo 1321479 10040273 := bstep (se 2 (by rfl) ⟨3765102, by rfl⟩ : syracuseStep 10040273 = 7530205) B7530205
theorem B6976475 : Blo 1321479 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B7640153 : Blo 1321479 7640153 := bstep (se 2 (by rfl) ⟨2865057, by rfl⟩ : syracuseStep 7640153 = 5730115) B5730115
theorem B1488091 : Blo 1321479 1488091 := bstep (se 1 (by rfl) ⟨1116068, by rfl⟩ : syracuseStep 1488091 = 2232137) B2232137
theorem B3347689 : Blo 1321479 3347689 := bstep (se 2 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 3347689 = 2510767) B2510767
theorem B3765491 : Blo 1321479 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B2512225 : Blo 1321479 2512225 := bstep (se 2 (by rfl) ⟨942084, by rfl⟩ : syracuseStep 2512225 = 1884169) B1884169
theorem B3347851 : Blo 1321479 3347851 := bstep (se 1 (by rfl) ⟨2510888, by rfl⟩ : syracuseStep 3347851 = 5021777) B5021777
theorem B1488379 : Blo 1321479 1488379 := bstep (se 1 (by rfl) ⟨1116284, by rfl⟩ : syracuseStep 1488379 = 2232569) B2232569
theorem B20633221 : Blo 1321479 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B24114833 : Blo 1321479 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B1488559 : Blo 1321479 1488559 := bstep (se 1 (by rfl) ⟨1116419, by rfl⟩ : syracuseStep 1488559 = 2232839) B2232839
theorem B3348155 : Blo 1321479 3348155 := bstep (se 1 (by rfl) ⟨2511116, by rfl⟩ : syracuseStep 3348155 = 5022233) B5022233
theorem B3815273 : Blo 1321479 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B13563767 : Blo 1321479 13563767 := bstep (se 1 (by rfl) ⟨10172825, by rfl⟩ : syracuseStep 13563767 = 20345651) B20345651
theorem B1488847 : Blo 1321479 1488847 := bstep (se 1 (by rfl) ⟨1116635, by rfl⟩ : syracuseStep 1488847 = 2233271) B2233271
theorem B7247951 : Blo 1321479 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B4462721 : Blo 1321479 4462721 := bstep (se 2 (by rfl) ⟨1673520, by rfl⟩ : syracuseStep 4462721 = 3347041) B3347041
theorem B6355073 : Blo 1321479 6355073 := bstep (se 2 (by rfl) ⟨2383152, by rfl⟩ : syracuseStep 6355073 = 4766305) B4766305
theorem B5019833 : Blo 1321479 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B5020015 : Blo 1321479 5020015 := bstep (se 1 (by rfl) ⟨3765011, by rfl⟩ : syracuseStep 5020015 = 7530023) B7530023
theorem B4463099 : Blo 1321479 4463099 := bstep (se 1 (by rfl) ⟨3347324, by rfl⟩ : syracuseStep 4463099 = 6694649) B6694649
theorem B7527107 : Blo 1321479 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B4463531 : Blo 1321479 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B2825255 : Blo 1321479 2825255 := bstep (se 1 (by rfl) ⟨2118941, by rfl⟩ : syracuseStep 2825255 = 4237883) B4237883
theorem B10722469 : Blo 1321479 10722469 := bstep (se 4 (by rfl) ⟨1005231, by rfl⟩ : syracuseStep 10722469 = 2010463) B2010463
theorem B4766939 : Blo 1321479 4766939 := bstep (se 1 (by rfl) ⟨3575204, by rfl⟩ : syracuseStep 4766939 = 7150409) B7150409
theorem B12057821 : Blo 1321479 12057821 := bstep (se 3 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 12057821 = 4521683) B4521683
theorem B4767113 : Blo 1321479 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B110042549 : Blo 1321479 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B4464071 : Blo 1321479 4464071 := bstep (se 1 (by rfl) ⟨3348053, by rfl⟩ : syracuseStep 4464071 = 6696107) B6696107
theorem B5651927 : Blo 1321479 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B5365207 : Blo 1321479 5365207 := bstep (se 1 (by rfl) ⟨4023905, by rfl⟩ : syracuseStep 5365207 = 8047811) B8047811
theorem B2973419 : Blo 1321479 2973419 := bstep (se 1 (by rfl) ⟨2230064, by rfl⟩ : syracuseStep 2973419 = 4460129) B4460129
theorem B4464395 : Blo 1321479 4464395 := bstep (se 1 (by rfl) ⟨3348296, by rfl⟩ : syracuseStep 4464395 = 6696593) B6696593
theorem B1982249 : Blo 1321479 1982249 := bstep (se 2 (by rfl) ⟨743343, by rfl⟩ : syracuseStep 1982249 = 1486687) B1486687
theorem B1982255 : Blo 1321479 1982255 := bstep (se 1 (by rfl) ⟨1486691, by rfl⟩ : syracuseStep 1982255 = 2973383) B2973383
theorem B2973545 : Blo 1321479 2973545 := bstep (se 2 (by rfl) ⟨1115079, by rfl⟩ : syracuseStep 2973545 = 2230159) B2230159
theorem B2974049 : Blo 1321479 2974049 := bstep (se 2 (by rfl) ⟨1115268, by rfl⟩ : syracuseStep 2974049 = 2230537) B2230537
theorem B2974139 : Blo 1321479 2974139 := bstep (se 1 (by rfl) ⟨2230604, by rfl⟩ : syracuseStep 2974139 = 4461209) B4461209
theorem B1982927 : Blo 1321479 1982927 := bstep (se 1 (by rfl) ⟨1487195, by rfl⟩ : syracuseStep 1982927 = 2974391) B2974391
theorem B6693353 : Blo 1321479 6693353 := bstep (se 2 (by rfl) ⟨2510007, by rfl⟩ : syracuseStep 6693353 = 5020015) B5020015
theorem B1982969 : Blo 1321479 1982969 := bstep (se 2 (by rfl) ⟨743613, by rfl⟩ : syracuseStep 1982969 = 1487227) B1487227
theorem B6783527 : Blo 1321479 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B1983071 : Blo 1321479 1983071 := bstep (se 1 (by rfl) ⟨1487303, by rfl⟩ : syracuseStep 1983071 = 2974607) B2974607
theorem B4465259 : Blo 1321479 4465259 := bstep (se 1 (by rfl) ⟨3348944, by rfl⟩ : syracuseStep 4465259 = 6697889) B6697889
theorem B6693515 : Blo 1321479 6693515 := bstep (se 1 (by rfl) ⟨5020136, by rfl⟩ : syracuseStep 6693515 = 10040273) B10040273
theorem B5358383 : Blo 1321479 5358383 := bstep (se 1 (by rfl) ⟨4018787, by rfl⟩ : syracuseStep 5358383 = 8037575) B8037575
theorem B7529273 : Blo 1321479 7529273 := bstep (se 2 (by rfl) ⟨2823477, by rfl⟩ : syracuseStep 7529273 = 5646955) B5646955
theorem B1983551 : Blo 1321479 1983551 := bstep (se 1 (by rfl) ⟨1487663, by rfl⟩ : syracuseStep 1983551 = 2975327) B2975327
theorem B1983593 : Blo 1321479 1983593 := bstep (se 2 (by rfl) ⟨743847, by rfl⟩ : syracuseStep 1983593 = 1487695) B1487695
theorem B9045137 : Blo 1321479 9045137 := bstep (se 2 (by rfl) ⟨3391926, by rfl⟩ : syracuseStep 9045137 = 6783853) B6783853
theorem B4465853 : Blo 1321479 4465853 := bstep (se 3 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 4465853 = 1674695) B1674695
theorem B1983695 : Blo 1321479 1983695 := bstep (se 1 (by rfl) ⟨1487771, by rfl⟩ : syracuseStep 1983695 = 2975543) B2975543
theorem B11306243 : Blo 1321479 11306243 := bstep (se 1 (by rfl) ⟨8479682, by rfl⟩ : syracuseStep 11306243 = 16959365) B16959365
theorem B8045963 : Blo 1321479 8045963 := bstep (se 1 (by rfl) ⟨6034472, by rfl⟩ : syracuseStep 8045963 = 12068945) B12068945
theorem B1983899 : Blo 1321479 1983899 := bstep (se 1 (by rfl) ⟨1487924, by rfl⟩ : syracuseStep 1983899 = 2975849) B2975849
theorem B2975147 : Blo 1321479 2975147 := bstep (se 1 (by rfl) ⟨2231360, by rfl⟩ : syracuseStep 2975147 = 4462721) B4462721
theorem B4236715 : Blo 1321479 4236715 := bstep (se 1 (by rfl) ⟨3177536, by rfl⟩ : syracuseStep 4236715 = 6355073) B6355073
theorem B9536939 : Blo 1321479 9536939 := bstep (se 1 (by rfl) ⟨7152704, by rfl⟩ : syracuseStep 9536939 = 14305409) B14305409
theorem B7144919 : Blo 1321479 7144919 := bstep (se 1 (by rfl) ⟨5358689, by rfl⟩ : syracuseStep 7144919 = 10717379) B10717379
theorem B14296625 : Blo 1321479 14296625 := bstep (se 2 (by rfl) ⟨5361234, by rfl⟩ : syracuseStep 14296625 = 10722469) B10722469
theorem B1984121 : Blo 1321479 1984121 := bstep (se 2 (by rfl) ⟨744045, by rfl⟩ : syracuseStep 1984121 = 1488091) B1488091
theorem B2975399 : Blo 1321479 2975399 := bstep (se 1 (by rfl) ⟨2231549, by rfl⟩ : syracuseStep 2975399 = 4463099) B4463099
theorem B1984223 : Blo 1321479 1984223 := bstep (se 1 (by rfl) ⟨1488167, by rfl⟩ : syracuseStep 1984223 = 2976335) B2976335
theorem B1984319 : Blo 1321479 1984319 := bstep (se 1 (by rfl) ⟨1488239, by rfl⟩ : syracuseStep 1984319 = 2976479) B2976479
theorem B2975687 : Blo 1321479 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B7153609 : Blo 1321479 7153609 := bstep (se 2 (by rfl) ⟨2682603, by rfl⟩ : syracuseStep 7153609 = 5365207) B5365207
theorem B2230247 : Blo 1321479 2230247 := bstep (se 1 (by rfl) ⟨1672685, by rfl⟩ : syracuseStep 2230247 = 3345371) B3345371
theorem B1984487 : Blo 1321479 1984487 := bstep (se 1 (by rfl) ⟨1488365, by rfl⟩ : syracuseStep 1984487 = 2976731) B2976731
theorem B1984505 : Blo 1321479 1984505 := bstep (se 2 (by rfl) ⟨744189, by rfl⟩ : syracuseStep 1984505 = 1488379) B1488379
theorem B1984607 : Blo 1321479 1984607 := bstep (se 1 (by rfl) ⟨1488455, by rfl⟩ : syracuseStep 1984607 = 2976911) B2976911
theorem B10037357 : Blo 1321479 10037357 := bstep (se 3 (by rfl) ⟨1882004, by rfl⟩ : syracuseStep 10037357 = 3764009) B3764009
theorem B8038547 : Blo 1321479 8038547 := bstep (se 1 (by rfl) ⟨6028910, by rfl⟩ : syracuseStep 8038547 = 12057821) B12057821
theorem B1984667 : Blo 1321479 1984667 := bstep (se 1 (by rfl) ⟨1488500, by rfl⟩ : syracuseStep 1984667 = 2977001) B2977001
theorem B27510961 : Blo 1321479 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B2230463 : Blo 1321479 2230463 := bstep (se 1 (by rfl) ⟨1672847, by rfl⟩ : syracuseStep 2230463 = 3345695) B3345695
theorem B1984703 : Blo 1321479 1984703 := bstep (se 1 (by rfl) ⟨1488527, by rfl⟩ : syracuseStep 1984703 = 2977055) B2977055
theorem B1984745 : Blo 1321479 1984745 := bstep (se 2 (by rfl) ⟨744279, by rfl⟩ : syracuseStep 1984745 = 1488559) B1488559
theorem B2975993 : Blo 1321479 2975993 := bstep (se 2 (by rfl) ⟨1115997, by rfl⟩ : syracuseStep 2975993 = 2231995) B2231995
theorem B73361699 : Blo 1321479 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B2976047 : Blo 1321479 2976047 := bstep (se 1 (by rfl) ⟨2232035, by rfl⟩ : syracuseStep 2976047 = 4464071) B4464071
theorem B2976263 : Blo 1321479 2976263 := bstep (se 1 (by rfl) ⟨2232197, by rfl⟩ : syracuseStep 2976263 = 4464395) B4464395
theorem B1321499 : Blo 1321479 1321499 := bstep (se 1 (by rfl) ⟨991124, by rfl⟩ : syracuseStep 1321499 = 1982249) B1982249
theorem B1985051 : Blo 1321479 1985051 := bstep (se 1 (by rfl) ⟨1488788, by rfl⟩ : syracuseStep 1985051 = 2977577) B2977577
theorem B1321503 : Blo 1321479 1321503 := bstep (se 1 (by rfl) ⟨991127, by rfl⟩ : syracuseStep 1321503 = 1982255) B1982255
theorem B1411615 : Blo 1321479 1411615 := bstep (se 1 (by rfl) ⟨1058711, by rfl⟩ : syracuseStep 1411615 = 2117423) B2117423
theorem B1985129 : Blo 1321479 1985129 := bstep (se 2 (by rfl) ⟨744423, by rfl⟩ : syracuseStep 1985129 = 1488847) B1488847
theorem B2976443 : Blo 1321479 2976443 := bstep (se 1 (by rfl) ⟨2232332, by rfl⟩ : syracuseStep 2976443 = 4464665) B4464665
theorem B1321819 : Blo 1321479 1321819 := bstep (se 1 (by rfl) ⟨991364, by rfl⟩ : syracuseStep 1321819 = 1982729) B1982729
theorem B2231131 : Blo 1321479 2231131 := bstep (se 1 (by rfl) ⟨1673348, by rfl⟩ : syracuseStep 2231131 = 3346697) B3346697
theorem B1411931 : Blo 1321479 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B7637915 : Blo 1321479 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B1321887 : Blo 1321479 1321887 := bstep (se 1 (by rfl) ⟨991415, by rfl⟩ : syracuseStep 1321887 = 1982831) B1982831
theorem B1322031 : Blo 1321479 1322031 := bstep (se 1 (by rfl) ⟨991523, by rfl⟩ : syracuseStep 1322031 = 1983047) B1983047
theorem B1322055 : Blo 1321479 1322055 := bstep (se 1 (by rfl) ⟨991541, by rfl⟩ : syracuseStep 1322055 = 1983083) B1983083
theorem B7531663 : Blo 1321479 7531663 := bstep (se 1 (by rfl) ⟨5648747, by rfl⟩ : syracuseStep 7531663 = 11297495) B11297495
theorem B1322207 : Blo 1321479 1322207 := bstep (se 1 (by rfl) ⟨991655, by rfl⟩ : syracuseStep 1322207 = 1983311) B1983311
theorem B1322471 : Blo 1321479 1322471 := bstep (se 1 (by rfl) ⟨991853, by rfl⟩ : syracuseStep 1322471 = 1983707) B1983707
theorem B2510327 : Blo 1321479 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B2977271 : Blo 1321479 2977271 := bstep (se 1 (by rfl) ⟨2232953, by rfl⟩ : syracuseStep 2977271 = 4465907) B4465907
theorem B2977343 : Blo 1321479 2977343 := bstep (se 1 (by rfl) ⟨2233007, by rfl⟩ : syracuseStep 2977343 = 4466015) B4466015
theorem B1322587 : Blo 1321479 1322587 := bstep (se 1 (by rfl) ⟨991940, by rfl⟩ : syracuseStep 1322587 = 1983881) B1983881
theorem B16076555 : Blo 1321479 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B2232103 : Blo 1321479 2232103 := bstep (se 1 (by rfl) ⟨1674077, by rfl⟩ : syracuseStep 2232103 = 3348155) B3348155
theorem B7843645 : Blo 1321479 7843645 := bstep (se 3 (by rfl) ⟨1470683, by rfl⟩ : syracuseStep 7843645 = 2941367) B2941367
theorem B1322823 : Blo 1321479 1322823 := bstep (se 1 (by rfl) ⟨992117, by rfl⟩ : syracuseStep 1322823 = 1984235) B1984235
theorem B1322975 : Blo 1321479 1322975 := bstep (se 1 (by rfl) ⟨992231, by rfl⟩ : syracuseStep 1322975 = 1984463) B1984463
theorem B3346555 : Blo 1321479 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B11767961 : Blo 1321479 11767961 := bstep (se 2 (by rfl) ⟨4412985, by rfl⟩ : syracuseStep 11767961 = 8825971) B8825971
theorem B1323239 : Blo 1321479 1323239 := bstep (se 1 (by rfl) ⟨992429, by rfl⟩ : syracuseStep 1323239 = 1984859) B1984859
theorem B1323391 : Blo 1321479 1323391 := bstep (se 1 (by rfl) ⟨992543, by rfl⟩ : syracuseStep 1323391 = 1985087) B1985087
theorem B3764647 : Blo 1321479 3764647 := bstep (se 1 (by rfl) ⟨2823485, by rfl⟩ : syracuseStep 3764647 = 5646971) B5646971
theorem B1323471 : Blo 1321479 1323471 := bstep (se 1 (by rfl) ⟨992603, by rfl⟩ : syracuseStep 1323471 = 1985207) B1985207
theorem B5018071 : Blo 1321479 5018071 := bstep (se 1 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 5018071 = 7527107) B7527107
theorem B3764819 : Blo 1321479 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B2233129 : Blo 1321479 2233129 := bstep (se 2 (by rfl) ⟨837423, by rfl⟩ : syracuseStep 2233129 = 1674847) B1674847
theorem B4461641 : Blo 1321479 4461641 := bstep (se 2 (by rfl) ⟨1673115, by rfl⟩ : syracuseStep 4461641 = 3346231) B3346231
theorem B3765467 : Blo 1321479 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B9532723 : Blo 1321479 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B19076471 : Blo 1321479 19076471 := bstep (se 1 (by rfl) ⟨14307353, by rfl⟩ : syracuseStep 19076471 = 28614707) B28614707
theorem B55055915 : Blo 1321479 55055915 := bstep (se 1 (by rfl) ⟨41291936, by rfl⟩ : syracuseStep 55055915 = 82583873) B82583873
theorem B2823751 : Blo 1321479 2823751 := bstep (se 1 (by rfl) ⟨2117813, by rfl⟩ : syracuseStep 2823751 = 4235627) B4235627
theorem B11449943 : Blo 1321479 11449943 := bstep (se 1 (by rfl) ⟨8587457, by rfl⟩ : syracuseStep 11449943 = 17174915) B17174915
theorem B4765355 : Blo 1321479 4765355 := bstep (se 1 (by rfl) ⟨3574016, by rfl⟩ : syracuseStep 4765355 = 7148033) B7148033
theorem B6698699 : Blo 1321479 6698699 := bstep (se 1 (by rfl) ⟨5024024, by rfl⟩ : syracuseStep 6698699 = 10048049) B10048049
theorem B21452525 : Blo 1321479 21452525 := bstep (se 3 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 21452525 = 8044697) B8044697
theorem B128726819 : Blo 1321479 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B3348287 : Blo 1321479 3348287 := bstep (se 1 (by rfl) ⟨2511215, by rfl⟩ : syracuseStep 3348287 = 5022431) B5022431
theorem B1488703 : Blo 1321479 1488703 := bstep (se 1 (by rfl) ⟨1116527, by rfl⟩ : syracuseStep 1488703 = 2233055) B2233055
theorem B4650983 : Blo 1321479 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B5093435 : Blo 1321479 5093435 := bstep (se 1 (by rfl) ⟨3820076, by rfl⟩ : syracuseStep 5093435 = 7640153) B7640153
theorem B5019803 : Blo 1321479 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B3348641 : Blo 1321479 3348641 := bstep (se 2 (by rfl) ⟨1255740, by rfl⟩ : syracuseStep 3348641 = 2511481) B2511481
theorem B32602429 : Blo 1321479 32602429 := bstep (se 3 (by rfl) ⟨6112955, by rfl⟩ : syracuseStep 32602429 = 12225911) B12225911
theorem B12712301 : Blo 1321479 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B2824571 : Blo 1321479 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B33077629 : Blo 1321479 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B6691247 : Blo 1321479 6691247 := bstep (se 1 (by rfl) ⟨5018435, by rfl⟩ : syracuseStep 6691247 = 10036871) B10036871
theorem B9042511 : Blo 1321479 9042511 := bstep (se 1 (by rfl) ⟨6781883, by rfl⟩ : syracuseStep 9042511 = 13563767) B13563767
theorem B4463261 : Blo 1321479 4463261 := bstep (se 3 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 4463261 = 1673723) B1673723
theorem B8477405 : Blo 1321479 8477405 := bstep (se 3 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 8477405 = 3179027) B3179027
theorem B4831967 : Blo 1321479 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B8477531 : Blo 1321479 8477531 := bstep (se 1 (by rfl) ⟨6358148, by rfl⟩ : syracuseStep 8477531 = 12716297) B12716297
theorem B13564837 : Blo 1321479 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B4463585 : Blo 1321479 4463585 := bstep (se 2 (by rfl) ⟨1673844, by rfl⟩ : syracuseStep 4463585 = 3347689) B3347689
theorem B3349633 : Blo 1321479 3349633 := bstep (se 2 (by rfl) ⟨1256112, by rfl⟩ : syracuseStep 3349633 = 2512225) B2512225
theorem B7527563 : Blo 1321479 7527563 := bstep (se 1 (by rfl) ⟨5645672, by rfl⟩ : syracuseStep 7527563 = 11291345) B11291345
theorem B2825399 : Blo 1321479 2825399 := bstep (se 1 (by rfl) ⟨2119049, by rfl⟩ : syracuseStep 2825399 = 4238099) B4238099
theorem B4463801 : Blo 1321479 4463801 := bstep (se 2 (by rfl) ⟨1673925, by rfl⟩ : syracuseStep 4463801 = 3347851) B3347851
theorem B1883503 : Blo 1321479 1883503 := bstep (se 1 (by rfl) ⟨1412627, by rfl⟩ : syracuseStep 1883503 = 2825255) B2825255
theorem B9526727 : Blo 1321479 9526727 := bstep (se 1 (by rfl) ⟨7145045, by rfl⟩ : syracuseStep 9526727 = 14290091) B14290091
theorem B3177959 : Blo 1321479 3177959 := bstep (se 1 (by rfl) ⟨2383469, by rfl⟩ : syracuseStep 3177959 = 4766939) B4766939
theorem B244407851 : Blo 1321479 244407851 := bstep (se 1 (by rfl) ⟨183305888, by rfl⟩ : syracuseStep 244407851 = 366611777) B366611777
theorem B10174061 : Blo 1321479 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B3767951 : Blo 1321479 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2449129 : Blo 1321479 2449129 := bstep (se 2 (by rfl) ⟨918423, by rfl⟩ : syracuseStep 2449129 = 1836847) B1836847
theorem B7528247 : Blo 1321479 7528247 := bstep (se 1 (by rfl) ⟨5646185, by rfl⟩ : syracuseStep 7528247 = 11292371) B11292371
theorem B1982279 : Blo 1321479 1982279 := bstep (se 1 (by rfl) ⟨1486709, by rfl⟩ : syracuseStep 1982279 = 2973419) B2973419
theorem B2973563 : Blo 1321479 2973563 := bstep (se 1 (by rfl) ⟨2230172, by rfl⟩ : syracuseStep 2973563 = 4460345) B4460345
theorem B15056765 : Blo 1321479 15056765 := bstep (se 3 (by rfl) ⟨2823143, by rfl⟩ : syracuseStep 15056765 = 5646287) B5646287
theorem B1982363 : Blo 1321479 1982363 := bstep (se 1 (by rfl) ⟨1486772, by rfl⟩ : syracuseStep 1982363 = 2973545) B2973545
theorem B1982699 : Blo 1321479 1982699 := bstep (se 1 (by rfl) ⟨1487024, by rfl⟩ : syracuseStep 1982699 = 2974049) B2974049
theorem B1982759 : Blo 1321479 1982759 := bstep (se 1 (by rfl) ⟨1487069, by rfl⟩ : syracuseStep 1982759 = 2974139) B2974139
theorem B3572255 : Blo 1321479 3572255 := bstep (se 1 (by rfl) ⟨2679191, by rfl⟩ : syracuseStep 3572255 = 5358383) B5358383
theorem B2974427 : Blo 1321479 2974427 := bstep (se 1 (by rfl) ⟨2230820, by rfl⟩ : syracuseStep 2974427 = 4461641) B4461641
theorem B6030091 : Blo 1321479 6030091 := bstep (se 1 (by rfl) ⟨4522568, by rfl⟩ : syracuseStep 6030091 = 9045137) B9045137
theorem B7537495 : Blo 1321479 7537495 := bstep (se 1 (by rfl) ⟨5653121, by rfl⟩ : syracuseStep 7537495 = 11306243) B11306243
theorem B1983431 : Blo 1321479 1983431 := bstep (se 1 (by rfl) ⟨1487573, by rfl⟩ : syracuseStep 1983431 = 2975147) B2975147
theorem B6357959 : Blo 1321479 6357959 := bstep (se 1 (by rfl) ⟨4768469, by rfl⟩ : syracuseStep 6357959 = 9536939) B9536939
theorem B1983599 : Blo 1321479 1983599 := bstep (se 1 (by rfl) ⟨1487699, by rfl⟩ : syracuseStep 1983599 = 2975399) B2975399
theorem B2974841 : Blo 1321479 2974841 := bstep (se 2 (by rfl) ⟨1115565, by rfl⟩ : syracuseStep 2974841 = 2231131) B2231131
theorem B4465799 : Blo 1321479 4465799 := bstep (se 1 (by rfl) ⟨3349349, by rfl⟩ : syracuseStep 4465799 = 6698699) B6698699
theorem B1983791 : Blo 1321479 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B5359031 : Blo 1321479 5359031 := bstep (se 1 (by rfl) ⟨4019273, by rfl⟩ : syracuseStep 5359031 = 8038547) B8038547
theorem B18089405 : Blo 1321479 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B1983995 : Blo 1321479 1983995 := bstep (se 1 (by rfl) ⟨1487996, by rfl⟩ : syracuseStep 1983995 = 2975993) B2975993
theorem B4466177 : Blo 1321479 4466177 := bstep (se 2 (by rfl) ⟨1674816, by rfl⟩ : syracuseStep 4466177 = 3349633) B3349633
theorem B48907799 : Blo 1321479 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B1984031 : Blo 1321479 1984031 := bstep (se 1 (by rfl) ⟨1488023, by rfl⟩ : syracuseStep 1984031 = 2976047) B2976047
theorem B1984175 : Blo 1321479 1984175 := bstep (se 1 (by rfl) ⟨1488131, by rfl⟩ : syracuseStep 1984175 = 2976263) B2976263
theorem B2975507 : Blo 1321479 2975507 := bstep (se 1 (by rfl) ⟨2231630, by rfl⟩ : syracuseStep 2975507 = 4463261) B4463261
theorem B1984295 : Blo 1321479 1984295 := bstep (se 1 (by rfl) ⟨1488221, by rfl⟩ : syracuseStep 1984295 = 2976443) B2976443
theorem B3221311 : Blo 1321479 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B2975723 : Blo 1321479 2975723 := bstep (se 1 (by rfl) ⟨2231792, by rfl⟩ : syracuseStep 2975723 = 4463585) B4463585
theorem B2975867 : Blo 1321479 2975867 := bstep (se 1 (by rfl) ⟨2231900, by rfl⟩ : syracuseStep 2975867 = 4463801) B4463801
theorem B6351151 : Blo 1321479 6351151 := bstep (se 1 (by rfl) ⟨4763363, by rfl⟩ : syracuseStep 6351151 = 9526727) B9526727
theorem B1673551 : Blo 1321479 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B1984847 : Blo 1321479 1984847 := bstep (se 1 (by rfl) ⟨1488635, by rfl⟩ : syracuseStep 1984847 = 2977271) B2977271
theorem B1984895 : Blo 1321479 1984895 := bstep (se 1 (by rfl) ⟨1488671, by rfl⟩ : syracuseStep 1984895 = 2977343) B2977343
theorem B2976137 : Blo 1321479 2976137 := bstep (se 2 (by rfl) ⟨1116051, by rfl⟩ : syracuseStep 2976137 = 2232103) B2232103
theorem B20367773 : Blo 1321479 20367773 := bstep (se 3 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 20367773 = 7637915) B7637915
theorem B1984937 : Blo 1321479 1984937 := bstep (se 2 (by rfl) ⟨744351, by rfl⟩ : syracuseStep 1984937 = 1488703) B1488703
theorem B10717703 : Blo 1321479 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B1321519 : Blo 1321479 1321519 := bstep (se 1 (by rfl) ⟨991139, by rfl⟩ : syracuseStep 1321519 = 1982279) B1982279
theorem B10037843 : Blo 1321479 10037843 := bstep (se 1 (by rfl) ⟨7528382, by rfl⟩ : syracuseStep 10037843 = 15056765) B15056765
theorem B9538145 : Blo 1321479 9538145 := bstep (se 2 (by rfl) ⟨3576804, by rfl⟩ : syracuseStep 9538145 = 7153609) B7153609
theorem B1321575 : Blo 1321479 1321575 := bstep (se 1 (by rfl) ⟨991181, by rfl⟩ : syracuseStep 1321575 = 1982363) B1982363
theorem B1321951 : Blo 1321479 1321951 := bstep (se 1 (by rfl) ⟨991463, by rfl⟩ : syracuseStep 1321951 = 1982927) B1982927
theorem B1321979 : Blo 1321479 1321979 := bstep (se 1 (by rfl) ⟨991484, by rfl⟩ : syracuseStep 1321979 = 1982969) B1982969
theorem B2509879 : Blo 1321479 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B1322047 : Blo 1321479 1322047 := bstep (se 1 (by rfl) ⟨991535, by rfl⟩ : syracuseStep 1322047 = 1983071) B1983071
theorem B2976839 : Blo 1321479 2976839 := bstep (se 1 (by rfl) ⟨2232629, by rfl⟩ : syracuseStep 2976839 = 4465259) B4465259
theorem B43469905 : Blo 1321479 43469905 := bstep (se 2 (by rfl) ⟨16301214, by rfl⟩ : syracuseStep 43469905 = 32602429) B32602429
theorem B1322367 : Blo 1321479 1322367 := bstep (se 1 (by rfl) ⟨991775, by rfl⟩ : syracuseStep 1322367 = 1983551) B1983551
theorem B1322395 : Blo 1321479 1322395 := bstep (se 1 (by rfl) ⟨991796, by rfl⟩ : syracuseStep 1322395 = 1983593) B1983593
theorem B2977235 : Blo 1321479 2977235 := bstep (se 1 (by rfl) ⟨2232926, by rfl⟩ : syracuseStep 2977235 = 4465853) B4465853
theorem B1322463 : Blo 1321479 1322463 := bstep (se 1 (by rfl) ⟨991847, by rfl⟩ : syracuseStep 1322463 = 1983695) B1983695
theorem B12717647 : Blo 1321479 12717647 := bstep (se 1 (by rfl) ⟨9538235, by rfl⟩ : syracuseStep 12717647 = 19076471) B19076471
theorem B1322599 : Blo 1321479 1322599 := bstep (se 1 (by rfl) ⟨991949, by rfl⟩ : syracuseStep 1322599 = 1983899) B1983899
theorem B4763279 : Blo 1321479 4763279 := bstep (se 1 (by rfl) ⟨3572459, by rfl⟩ : syracuseStep 4763279 = 7144919) B7144919
theorem B7532189 : Blo 1321479 7532189 := bstep (se 3 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 7532189 = 2824571) B2824571
theorem B36703943 : Blo 1321479 36703943 := bstep (se 1 (by rfl) ⟨27527957, by rfl⟩ : syracuseStep 36703943 = 55055915) B55055915
theorem B9531083 : Blo 1321479 9531083 := bstep (se 1 (by rfl) ⟨7148312, by rfl⟩ : syracuseStep 9531083 = 14296625) B14296625
theorem B2977505 : Blo 1321479 2977505 := bstep (se 2 (by rfl) ⟨1116564, by rfl⟩ : syracuseStep 2977505 = 2233129) B2233129
theorem B1322747 : Blo 1321479 1322747 := bstep (se 1 (by rfl) ⟨992060, by rfl⟩ : syracuseStep 1322747 = 1984121) B1984121
theorem B1322815 : Blo 1321479 1322815 := bstep (se 1 (by rfl) ⟨992111, by rfl⟩ : syracuseStep 1322815 = 1984223) B1984223
theorem B2232191 : Blo 1321479 2232191 := bstep (se 1 (by rfl) ⟨1674143, by rfl⟩ : syracuseStep 2232191 = 3348287) B3348287
theorem B1322879 : Blo 1321479 1322879 := bstep (se 1 (by rfl) ⟨992159, by rfl⟩ : syracuseStep 1322879 = 1984319) B1984319
theorem B8474557 : Blo 1321479 8474557 := bstep (se 3 (by rfl) ⟨1588979, by rfl⟩ : syracuseStep 8474557 = 3177959) B3177959
theorem B1486831 : Blo 1321479 1486831 := bstep (se 1 (by rfl) ⟨1115123, by rfl⟩ : syracuseStep 1486831 = 2230247) B2230247
theorem B1322991 : Blo 1321479 1322991 := bstep (se 1 (by rfl) ⟨992243, by rfl⟩ : syracuseStep 1322991 = 1984487) B1984487
theorem B3100655 : Blo 1321479 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B1323003 : Blo 1321479 1323003 := bstep (se 1 (by rfl) ⟨992252, by rfl⟩ : syracuseStep 1323003 = 1984505) B1984505
theorem B3395623 : Blo 1321479 3395623 := bstep (se 1 (by rfl) ⟨2546717, by rfl⟩ : syracuseStep 3395623 = 5093435) B5093435
theorem B1323071 : Blo 1321479 1323071 := bstep (se 1 (by rfl) ⟨992303, by rfl⟩ : syracuseStep 1323071 = 1984607) B1984607
theorem B3346535 : Blo 1321479 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B1323111 : Blo 1321479 1323111 := bstep (se 1 (by rfl) ⟨992333, by rfl⟩ : syracuseStep 1323111 = 1984667) B1984667
theorem B2232427 : Blo 1321479 2232427 := bstep (se 1 (by rfl) ⟨1674320, by rfl⟩ : syracuseStep 2232427 = 3348641) B3348641
theorem B1486975 : Blo 1321479 1486975 := bstep (se 1 (by rfl) ⟨1115231, by rfl⟩ : syracuseStep 1486975 = 2230463) B2230463
theorem B1323135 : Blo 1321479 1323135 := bstep (se 1 (by rfl) ⟨992351, by rfl⟩ : syracuseStep 1323135 = 1984703) B1984703
theorem B1323163 : Blo 1321479 1323163 := bstep (se 1 (by rfl) ⟨992372, by rfl⟩ : syracuseStep 1323163 = 1984745) B1984745
theorem B8474867 : Blo 1321479 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B4460831 : Blo 1321479 4460831 := bstep (se 1 (by rfl) ⟨3345623, by rfl⟩ : syracuseStep 4460831 = 6691247) B6691247
theorem B41832773 : Blo 1321479 41832773 := bstep (se 4 (by rfl) ⟨3921822, by rfl⟩ : syracuseStep 41832773 = 7843645) B7843645
theorem B1323367 : Blo 1321479 1323367 := bstep (se 1 (by rfl) ⟨992525, by rfl⟩ : syracuseStep 1323367 = 1985051) B1985051
theorem B12710297 : Blo 1321479 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B1323419 : Blo 1321479 1323419 := bstep (se 1 (by rfl) ⟨992564, by rfl⟩ : syracuseStep 1323419 = 1985129) B1985129
theorem B2511337 : Blo 1321479 2511337 := bstep (se 2 (by rfl) ⟨941751, by rfl⟩ : syracuseStep 2511337 = 1883503) B1883503
theorem B5648953 : Blo 1321479 5648953 := bstep (se 2 (by rfl) ⟨2118357, by rfl⟩ : syracuseStep 5648953 = 4236715) B4236715
theorem B5018375 : Blo 1321479 5018375 := bstep (se 1 (by rfl) ⟨3763781, by rfl⟩ : syracuseStep 5018375 = 7527563) B7527563
theorem B3765001 : Blo 1321479 3765001 := bstep (se 2 (by rfl) ⟨1411875, by rfl⟩ : syracuseStep 3765001 = 2823751) B2823751
theorem B3765149 : Blo 1321479 3765149 := bstep (se 3 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 3765149 = 1411931) B1411931
theorem B3265505 : Blo 1321479 3265505 := bstep (se 2 (by rfl) ⟨1224564, by rfl⟩ : syracuseStep 3265505 = 2449129) B2449129
theorem B2511967 : Blo 1321479 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B5018831 : Blo 1321479 5018831 := bstep (se 1 (by rfl) ⟨3764123, by rfl⟩ : syracuseStep 5018831 = 7528247) B7528247
theorem B4462073 : Blo 1321479 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B36681281 : Blo 1321479 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B4462235 : Blo 1321479 4462235 := bstep (se 1 (by rfl) ⟨3346676, by rfl⟩ : syracuseStep 4462235 = 6693353) B6693353
theorem B31381229 : Blo 1321479 31381229 := bstep (se 3 (by rfl) ⟨5883980, by rfl⟩ : syracuseStep 31381229 = 11767961) B11767961
theorem B4462343 : Blo 1321479 4462343 := bstep (se 1 (by rfl) ⟨3346757, by rfl⟩ : syracuseStep 4462343 = 6693515) B6693515
theorem B7534397 : Blo 1321479 7534397 := bstep (se 3 (by rfl) ⟨1412699, by rfl⟩ : syracuseStep 7534397 = 2825399) B2825399
theorem B5019515 : Blo 1321479 5019515 := bstep (se 1 (by rfl) ⟨3764636, by rfl⟩ : syracuseStep 5019515 = 7529273) B7529273
theorem B5019529 : Blo 1321479 5019529 := bstep (se 2 (by rfl) ⟨1882323, by rfl⟩ : syracuseStep 5019529 = 3764647) B3764647
theorem B10041245 : Blo 1321479 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B6690761 : Blo 1321479 6690761 := bstep (se 2 (by rfl) ⟨2509035, by rfl⟩ : syracuseStep 6690761 = 5018071) B5018071
theorem B1882153 : Blo 1321479 1882153 := bstep (se 2 (by rfl) ⟨705807, by rfl⟩ : syracuseStep 1882153 = 1411615) B1411615
theorem B12056681 : Blo 1321479 12056681 := bstep (se 2 (by rfl) ⟨4521255, by rfl⟩ : syracuseStep 12056681 = 9042511) B9042511
theorem B5363975 : Blo 1321479 5363975 := bstep (se 1 (by rfl) ⟨4022981, by rfl⟩ : syracuseStep 5363975 = 8045963) B8045963
theorem B7633295 : Blo 1321479 7633295 := bstep (se 1 (by rfl) ⟨5724971, by rfl⟩ : syracuseStep 7633295 = 11449943) B11449943
theorem B3176903 : Blo 1321479 3176903 := bstep (se 1 (by rfl) ⟨2382677, by rfl⟩ : syracuseStep 3176903 = 4765355) B4765355
theorem B14301683 : Blo 1321479 14301683 := bstep (se 1 (by rfl) ⟨10726262, by rfl⟩ : syracuseStep 14301683 = 21452525) B21452525
theorem B85817879 : Blo 1321479 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B18086449 : Blo 1321479 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B6691571 : Blo 1321479 6691571 := bstep (se 1 (by rfl) ⟨5018678, by rfl⟩ : syracuseStep 6691571 = 10037357) B10037357
theorem B10042217 : Blo 1321479 10042217 := bstep (se 2 (by rfl) ⟨3765831, by rfl⟩ : syracuseStep 10042217 = 7531663) B7531663
theorem B5651603 : Blo 1321479 5651603 := bstep (se 1 (by rfl) ⟨4238702, by rfl⟩ : syracuseStep 5651603 = 8477405) B8477405
theorem B5651687 : Blo 1321479 5651687 := bstep (se 1 (by rfl) ⟨4238765, by rfl⟩ : syracuseStep 5651687 = 8477531) B8477531
theorem B176414021 : Blo 1321479 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B162938567 : Blo 1321479 162938567 := bstep (se 1 (by rfl) ⟨122203925, by rfl⟩ : syracuseStep 162938567 = 244407851) B244407851
theorem B6782707 : Blo 1321479 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B1982375 : Blo 1321479 1982375 := bstep (se 1 (by rfl) ⟨1486781, by rfl⟩ : syracuseStep 1982375 = 2973563) B2973563
theorem B1982633 : Blo 1321479 1982633 := bstep (se 2 (by rfl) ⟨743487, by rfl⟩ : syracuseStep 1982633 = 1486975) B1486975
theorem B2973887 : Blo 1321479 2973887 := bstep (se 1 (by rfl) ⟨2230415, by rfl⟩ : syracuseStep 2973887 = 4460831) B4460831
theorem B1982951 : Blo 1321479 1982951 := bstep (se 1 (by rfl) ⟨1487213, by rfl⟩ : syracuseStep 1982951 = 2974427) B2974427
theorem B1983227 : Blo 1321479 1983227 := bstep (se 1 (by rfl) ⟨1487420, by rfl⟩ : syracuseStep 1983227 = 2974841) B2974841
theorem B3572687 : Blo 1321479 3572687 := bstep (se 1 (by rfl) ⟨2679515, by rfl⟩ : syracuseStep 3572687 = 5359031) B5359031
theorem B12059603 : Blo 1321479 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B2974715 : Blo 1321479 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B32605199 : Blo 1321479 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B24454187 : Blo 1321479 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B2974823 : Blo 1321479 2974823 := bstep (se 1 (by rfl) ⟨2231117, by rfl⟩ : syracuseStep 2974823 = 4462235) B4462235
theorem B2974895 : Blo 1321479 2974895 := bstep (se 1 (by rfl) ⟨2231171, by rfl⟩ : syracuseStep 2974895 = 4462343) B4462343
theorem B1983671 : Blo 1321479 1983671 := bstep (se 1 (by rfl) ⟨1487753, by rfl⟩ : syracuseStep 1983671 = 2975507) B2975507
theorem B5022931 : Blo 1321479 5022931 := bstep (se 1 (by rfl) ⟨3767198, by rfl⟩ : syracuseStep 5022931 = 7534397) B7534397
theorem B6694163 : Blo 1321479 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B1983815 : Blo 1321479 1983815 := bstep (se 1 (by rfl) ⟨1487861, by rfl⟩ : syracuseStep 1983815 = 2975723) B2975723
theorem B8037787 : Blo 1321479 8037787 := bstep (se 1 (by rfl) ⟨6028340, by rfl⟩ : syracuseStep 8037787 = 12056681) B12056681
theorem B1983911 : Blo 1321479 1983911 := bstep (se 1 (by rfl) ⟨1487933, by rfl⟩ : syracuseStep 1983911 = 2975867) B2975867
theorem B57959873 : Blo 1321479 57959873 := bstep (se 2 (by rfl) ⟨21734952, by rfl⟩ : syracuseStep 57959873 = 43469905) B43469905
theorem B1984091 : Blo 1321479 1984091 := bstep (se 1 (by rfl) ⟨1488068, by rfl⟩ : syracuseStep 1984091 = 2976137) B2976137
theorem B5088863 : Blo 1321479 5088863 := bstep (se 1 (by rfl) ⟨3816647, by rfl⟩ : syracuseStep 5088863 = 7633295) B7633295
theorem B7145135 : Blo 1321479 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B6358763 : Blo 1321479 6358763 := bstep (se 1 (by rfl) ⟨4769072, by rfl⟩ : syracuseStep 6358763 = 9538145) B9538145
theorem B6694811 : Blo 1321479 6694811 := bstep (se 1 (by rfl) ⟨5021108, by rfl⟩ : syracuseStep 6694811 = 10042217) B10042217
theorem B83683277 : Blo 1321479 83683277 := bstep (se 3 (by rfl) ⟨15690614, by rfl⟩ : syracuseStep 83683277 = 31381229) B31381229
theorem B1984559 : Blo 1321479 1984559 := bstep (se 1 (by rfl) ⟨1488419, by rfl⟩ : syracuseStep 1984559 = 2976839) B2976839
theorem B1984823 : Blo 1321479 1984823 := bstep (se 1 (by rfl) ⟨1488617, by rfl⟩ : syracuseStep 1984823 = 2977235) B2977235
theorem B4295081 : Blo 1321479 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B1985003 : Blo 1321479 1985003 := bstep (se 1 (by rfl) ⟨1488752, by rfl⟩ : syracuseStep 1985003 = 2977505) B2977505
theorem B11299409 : Blo 1321479 11299409 := bstep (se 2 (by rfl) ⟨4237278, by rfl⟩ : syracuseStep 11299409 = 8474557) B8474557
theorem B1321583 : Blo 1321479 1321583 := bstep (se 1 (by rfl) ⟨991187, by rfl⟩ : syracuseStep 1321583 = 1982375) B1982375
theorem B2067103 : Blo 1321479 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B2509537 : Blo 1321479 2509537 := bstep (se 2 (by rfl) ⟨941076, by rfl⟩ : syracuseStep 2509537 = 1882153) B1882153
theorem B2231023 : Blo 1321479 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B2976569 : Blo 1321479 2976569 := bstep (se 2 (by rfl) ⟨1116213, by rfl⟩ : syracuseStep 2976569 = 2232427) B2232427
theorem B1321799 : Blo 1321479 1321799 := bstep (se 1 (by rfl) ⟨991349, by rfl⟩ : syracuseStep 1321799 = 1982699) B1982699
theorem B1321839 : Blo 1321479 1321839 := bstep (se 1 (by rfl) ⟨991379, by rfl⟩ : syracuseStep 1321839 = 1982759) B1982759
theorem B27888515 : Blo 1321479 27888515 := bstep (se 1 (by rfl) ⟨20916386, by rfl⟩ : syracuseStep 27888515 = 41832773) B41832773
theorem B2231401 : Blo 1321479 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B3345583 : Blo 1321479 3345583 := bstep (se 1 (by rfl) ⟨2509187, by rfl⟩ : syracuseStep 3345583 = 5018375) B5018375
theorem B2510099 : Blo 1321479 2510099 := bstep (se 1 (by rfl) ⟨1882574, by rfl⟩ : syracuseStep 2510099 = 3765149) B3765149
theorem B1322287 : Blo 1321479 1322287 := bstep (se 1 (by rfl) ⟨991715, by rfl⟩ : syracuseStep 1322287 = 1983431) B1983431
theorem B4238639 : Blo 1321479 4238639 := bstep (se 1 (by rfl) ⟨3178979, by rfl⟩ : syracuseStep 4238639 = 6357959) B6357959
theorem B1322399 : Blo 1321479 1322399 := bstep (se 1 (by rfl) ⟨991799, by rfl⟩ : syracuseStep 1322399 = 1983599) B1983599
theorem B7531937 : Blo 1321479 7531937 := bstep (se 2 (by rfl) ⟨2824476, by rfl⟩ : syracuseStep 7531937 = 5648953) B5648953
theorem B2977199 : Blo 1321479 2977199 := bstep (se 1 (by rfl) ⟨2232899, by rfl⟩ : syracuseStep 2977199 = 4465799) B4465799
theorem B3345887 : Blo 1321479 3345887 := bstep (se 1 (by rfl) ⟨2509415, by rfl⟩ : syracuseStep 3345887 = 5018831) B5018831
theorem B1322527 : Blo 1321479 1322527 := bstep (se 1 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 1322527 = 1983791) B1983791
theorem B1322663 : Blo 1321479 1322663 := bstep (se 1 (by rfl) ⟨991997, by rfl⟩ : syracuseStep 1322663 = 1983995) B1983995
theorem B2977451 : Blo 1321479 2977451 := bstep (se 1 (by rfl) ⟨2233088, by rfl⟩ : syracuseStep 2977451 = 4466177) B4466177
theorem B1322687 : Blo 1321479 1322687 := bstep (se 1 (by rfl) ⟨992015, by rfl⟩ : syracuseStep 1322687 = 1984031) B1984031
theorem B33894125 : Blo 1321479 33894125 := bstep (se 3 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 33894125 = 12710297) B12710297
theorem B1322783 : Blo 1321479 1322783 := bstep (se 1 (by rfl) ⟨992087, by rfl⟩ : syracuseStep 1322783 = 1984175) B1984175
theorem B1322863 : Blo 1321479 1322863 := bstep (se 1 (by rfl) ⟨992147, by rfl⟩ : syracuseStep 1322863 = 1984295) B1984295
theorem B3346343 : Blo 1321479 3346343 := bstep (se 1 (by rfl) ⟨2509757, by rfl⟩ : syracuseStep 3346343 = 5019515) B5019515
theorem B4460507 : Blo 1321479 4460507 := bstep (se 1 (by rfl) ⟨3345380, by rfl⟩ : syracuseStep 4460507 = 6690761) B6690761
theorem B3346505 : Blo 1321479 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B3575983 : Blo 1321479 3575983 := bstep (se 1 (by rfl) ⟨2681987, by rfl⟩ : syracuseStep 3575983 = 5363975) B5363975
theorem B1323231 : Blo 1321479 1323231 := bstep (se 1 (by rfl) ⟨992423, by rfl⟩ : syracuseStep 1323231 = 1984847) B1984847
theorem B1323263 : Blo 1321479 1323263 := bstep (se 1 (by rfl) ⟨992447, by rfl⟩ : syracuseStep 1323263 = 1984895) B1984895
theorem B13578515 : Blo 1321479 13578515 := bstep (se 1 (by rfl) ⟨10183886, by rfl⟩ : syracuseStep 13578515 = 20367773) B20367773
theorem B1323291 : Blo 1321479 1323291 := bstep (se 1 (by rfl) ⟨992468, by rfl⟩ : syracuseStep 1323291 = 1984937) B1984937
theorem B2117935 : Blo 1321479 2117935 := bstep (se 1 (by rfl) ⟨1588451, by rfl⟩ : syracuseStep 2117935 = 3176903) B3176903
theorem B4461047 : Blo 1321479 4461047 := bstep (se 1 (by rfl) ⟨3345785, by rfl⟩ : syracuseStep 4461047 = 6691571) B6691571
theorem B117609347 : Blo 1321479 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B3175519 : Blo 1321479 3175519 := bstep (se 1 (by rfl) ⟨2381639, by rfl⟩ : syracuseStep 3175519 = 4763279) B4763279
theorem B6354055 : Blo 1321479 6354055 := bstep (se 1 (by rfl) ⟨4765541, by rfl⟩ : syracuseStep 6354055 = 9531083) B9531083
theorem B1488127 : Blo 1321479 1488127 := bstep (se 1 (by rfl) ⟨1116095, by rfl⟩ : syracuseStep 1488127 = 2232191) B2232191
theorem B4527497 : Blo 1321479 4527497 := bstep (se 2 (by rfl) ⟨1697811, by rfl⟩ : syracuseStep 4527497 = 3395623) B3395623
theorem B5649911 : Blo 1321479 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B2381503 : Blo 1321479 2381503 := bstep (se 1 (by rfl) ⟨1786127, by rfl⟩ : syracuseStep 2381503 = 3572255) B3572255
theorem B8468201 : Blo 1321479 8468201 := bstep (se 2 (by rfl) ⟨3175575, by rfl⟩ : syracuseStep 8468201 = 6351151) B6351151
theorem B3348449 : Blo 1321479 3348449 := bstep (se 2 (by rfl) ⟨1255668, by rfl⟩ : syracuseStep 3348449 = 2511337) B2511337
theorem B2177003 : Blo 1321479 2177003 := bstep (se 1 (by rfl) ⟨1632752, by rfl⟩ : syracuseStep 2177003 = 3265505) B3265505
theorem B24115265 : Blo 1321479 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B5020001 : Blo 1321479 5020001 := bstep (se 2 (by rfl) ⟨1882500, by rfl⟩ : syracuseStep 5020001 = 3765001) B3765001
theorem B10049993 : Blo 1321479 10049993 := bstep (se 2 (by rfl) ⟨3768747, by rfl⟩ : syracuseStep 10049993 = 7537495) B7537495
theorem B36174437 : Blo 1321479 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B32160485 : Blo 1321479 32160485 := bstep (se 4 (by rfl) ⟨3015045, by rfl⟩ : syracuseStep 32160485 = 6030091) B6030091
theorem B3349289 : Blo 1321479 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B9534455 : Blo 1321479 9534455 := bstep (se 1 (by rfl) ⟨7150841, by rfl⟩ : syracuseStep 9534455 = 14301683) B14301683
theorem B57211919 : Blo 1321479 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B6691895 : Blo 1321479 6691895 := bstep (se 1 (by rfl) ⟨5018921, by rfl⟩ : syracuseStep 6691895 = 10037843) B10037843
theorem B3767735 : Blo 1321479 3767735 := bstep (se 1 (by rfl) ⟨2825801, by rfl⟩ : syracuseStep 3767735 = 5651603) B5651603
theorem B3767791 : Blo 1321479 3767791 := bstep (se 1 (by rfl) ⟨2825843, by rfl⟩ : syracuseStep 3767791 = 5651687) B5651687
theorem B8478431 : Blo 1321479 8478431 := bstep (se 1 (by rfl) ⟨6358823, by rfl⟩ : syracuseStep 8478431 = 12717647) B12717647
theorem B5021459 : Blo 1321479 5021459 := bstep (se 1 (by rfl) ⟨3766094, by rfl⟩ : syracuseStep 5021459 = 7532189) B7532189
theorem B108625711 : Blo 1321479 108625711 := bstep (se 1 (by rfl) ⟨81469283, by rfl⟩ : syracuseStep 108625711 = 162938567) B162938567
theorem B24469295 : Blo 1321479 24469295 := bstep (se 1 (by rfl) ⟨18351971, by rfl⟩ : syracuseStep 24469295 = 36703943) B36703943
theorem B6692705 : Blo 1321479 6692705 := bstep (se 2 (by rfl) ⟨2509764, by rfl⟩ : syracuseStep 6692705 = 5019529) B5019529
theorem B1982441 : Blo 1321479 1982441 := bstep (se 2 (by rfl) ⟨743415, by rfl⟩ : syracuseStep 1982441 = 1486831) B1486831
theorem B1982591 : Blo 1321479 1982591 := bstep (se 1 (by rfl) ⟨1486943, by rfl⟩ : syracuseStep 1982591 = 2973887) B2973887
theorem B9052343 : Blo 1321479 9052343 := bstep (se 1 (by rfl) ⟨6789257, by rfl⟩ : syracuseStep 9052343 = 13578515) B13578515
theorem B4767977 : Blo 1321479 4767977 := bstep (se 2 (by rfl) ⟨1787991, by rfl⟩ : syracuseStep 4767977 = 3575983) B3575983
theorem B2974031 : Blo 1321479 2974031 := bstep (se 1 (by rfl) ⟨2230523, by rfl⟩ : syracuseStep 2974031 = 4461047) B4461047
theorem B1983143 : Blo 1321479 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B16302791 : Blo 1321479 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B1983215 : Blo 1321479 1983215 := bstep (se 1 (by rfl) ⟨1487411, by rfl⟩ : syracuseStep 1983215 = 2974823) B2974823
theorem B1983263 : Blo 1321479 1983263 := bstep (se 1 (by rfl) ⟨1487447, by rfl⟩ : syracuseStep 1983263 = 2974895) B2974895
theorem B2974697 : Blo 1321479 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B5645467 : Blo 1321479 5645467 := bstep (se 1 (by rfl) ⟨4234100, by rfl⟩ : syracuseStep 5645467 = 8468201) B8468201
theorem B55788851 : Blo 1321479 55788851 := bstep (se 1 (by rfl) ⟨41841638, by rfl⟩ : syracuseStep 55788851 = 83683277) B83683277
theorem B2975201 : Blo 1321479 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B8472073 : Blo 1321479 8472073 := bstep (se 2 (by rfl) ⟨3177027, by rfl⟩ : syracuseStep 8472073 = 6354055) B6354055
theorem B1984169 : Blo 1321479 1984169 := bstep (se 2 (by rfl) ⟨744063, by rfl⟩ : syracuseStep 1984169 = 1488127) B1488127
theorem B21440323 : Blo 1321479 21440323 := bstep (se 1 (by rfl) ⟨16080242, by rfl⟩ : syracuseStep 21440323 = 32160485) B32160485
theorem B10717049 : Blo 1321479 10717049 := bstep (se 2 (by rfl) ⟨4018893, by rfl⟩ : syracuseStep 10717049 = 8037787) B8037787
theorem B1984379 : Blo 1321479 1984379 := bstep (se 1 (by rfl) ⟨1488284, by rfl⟩ : syracuseStep 1984379 = 2976569) B2976569
theorem B5023721 : Blo 1321479 5023721 := bstep (se 2 (by rfl) ⟨1883895, by rfl⟩ : syracuseStep 5023721 = 3767791) B3767791
theorem B65251453 : Blo 1321479 65251453 := bstep (se 3 (by rfl) ⟨12234647, by rfl⟩ : syracuseStep 65251453 = 24469295) B24469295
theorem B1673399 : Blo 1321479 1673399 := bstep (se 1 (by rfl) ⟨1255049, by rfl⟩ : syracuseStep 1673399 = 2510099) B2510099
theorem B1984799 : Blo 1321479 1984799 := bstep (se 1 (by rfl) ⟨1488599, by rfl⟩ : syracuseStep 1984799 = 2977199) B2977199
theorem B2230591 : Blo 1321479 2230591 := bstep (se 1 (by rfl) ⟨1672943, by rfl⟩ : syracuseStep 2230591 = 3345887) B3345887
theorem B313624925 : Blo 1321479 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B1984967 : Blo 1321479 1984967 := bstep (se 1 (by rfl) ⟨1488725, by rfl⟩ : syracuseStep 1984967 = 2977451) B2977451
theorem B22596083 : Blo 1321479 22596083 := bstep (se 1 (by rfl) ⟨16947062, by rfl⟩ : syracuseStep 22596083 = 33894125) B33894125
theorem B2230895 : Blo 1321479 2230895 := bstep (se 1 (by rfl) ⟨1673171, by rfl⟩ : syracuseStep 2230895 = 3346343) B3346343
theorem B1321627 : Blo 1321479 1321627 := bstep (se 1 (by rfl) ⟨991220, by rfl⟩ : syracuseStep 1321627 = 1982441) B1982441
theorem B2231003 : Blo 1321479 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B1321755 : Blo 1321479 1321755 := bstep (se 1 (by rfl) ⟨991316, by rfl⟩ : syracuseStep 1321755 = 1982633) B1982633
theorem B1321967 : Blo 1321479 1321967 := bstep (se 1 (by rfl) ⟨991475, by rfl⟩ : syracuseStep 1321967 = 1982951) B1982951
theorem B1322151 : Blo 1321479 1322151 := bstep (se 1 (by rfl) ⟨991613, by rfl⟩ : syracuseStep 1322151 = 1983227) B1983227
theorem B8039735 : Blo 1321479 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B21736799 : Blo 1321479 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B1322447 : Blo 1321479 1322447 := bstep (se 1 (by rfl) ⟨991835, by rfl⟩ : syracuseStep 1322447 = 1983671) B1983671
theorem B1322543 : Blo 1321479 1322543 := bstep (se 1 (by rfl) ⟨991907, by rfl⟩ : syracuseStep 1322543 = 1983815) B1983815
theorem B3018331 : Blo 1321479 3018331 := bstep (se 1 (by rfl) ⟨2263748, by rfl⟩ : syracuseStep 3018331 = 4527497) B4527497
theorem B1322607 : Blo 1321479 1322607 := bstep (se 1 (by rfl) ⟨991955, by rfl⟩ : syracuseStep 1322607 = 1983911) B1983911
theorem B3346049 : Blo 1321479 3346049 := bstep (se 2 (by rfl) ⟨1254768, by rfl⟩ : syracuseStep 3346049 = 2509537) B2509537
theorem B1322727 : Blo 1321479 1322727 := bstep (se 1 (by rfl) ⟨992045, by rfl⟩ : syracuseStep 1322727 = 1984091) B1984091
theorem B4763423 : Blo 1321479 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B2232299 : Blo 1321479 2232299 := bstep (se 1 (by rfl) ⟨1674224, by rfl⟩ : syracuseStep 2232299 = 3348449) B3348449
theorem B1323039 : Blo 1321479 1323039 := bstep (se 1 (by rfl) ⟨992279, by rfl⟩ : syracuseStep 1323039 = 1984559) B1984559
theorem B16076843 : Blo 1321479 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B1323215 : Blo 1321479 1323215 := bstep (se 1 (by rfl) ⟨992411, by rfl⟩ : syracuseStep 1323215 = 1984823) B1984823
theorem B4460777 : Blo 1321479 4460777 := bstep (se 2 (by rfl) ⟨1672791, by rfl⟩ : syracuseStep 4460777 = 3345583) B3345583
theorem B3346667 : Blo 1321479 3346667 := bstep (se 1 (by rfl) ⟨2510000, by rfl⟩ : syracuseStep 3346667 = 5020001) B5020001
theorem B13570301 : Blo 1321479 13570301 := bstep (se 3 (by rfl) ⟨2544431, by rfl⟩ : syracuseStep 13570301 = 5088863) B5088863
theorem B6697241 : Blo 1321479 6697241 := bstep (se 2 (by rfl) ⟨2511465, by rfl⟩ : syracuseStep 6697241 = 5022931) B5022931
theorem B2863387 : Blo 1321479 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B1323335 : Blo 1321479 1323335 := bstep (se 1 (by rfl) ⟨992501, by rfl⟩ : syracuseStep 1323335 = 1985003) B1985003
theorem B7532939 : Blo 1321479 7532939 := bstep (se 1 (by rfl) ⟨5649704, by rfl⟩ : syracuseStep 7532939 = 11299409) B11299409
theorem B2232859 : Blo 1321479 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B18592343 : Blo 1321479 18592343 := bstep (se 1 (by rfl) ⟨13944257, by rfl⟩ : syracuseStep 18592343 = 27888515) B27888515
theorem B4461263 : Blo 1321479 4461263 := bstep (se 1 (by rfl) ⟨3345947, by rfl⟩ : syracuseStep 4461263 = 6691895) B6691895
theorem B3175337 : Blo 1321479 3175337 := bstep (se 2 (by rfl) ⟨1190751, by rfl⟩ : syracuseStep 3175337 = 2381503) B2381503
theorem B2511823 : Blo 1321479 2511823 := bstep (se 1 (by rfl) ⟨1883867, by rfl⟩ : syracuseStep 2511823 = 3767735) B3767735
theorem B3347639 : Blo 1321479 3347639 := bstep (se 1 (by rfl) ⟨2510729, by rfl⟩ : syracuseStep 3347639 = 5021459) B5021459
theorem B4461803 : Blo 1321479 4461803 := bstep (se 1 (by rfl) ⟨3346352, by rfl⟩ : syracuseStep 4461803 = 6692705) B6692705
theorem B5805341 : Blo 1321479 5805341 := bstep (se 3 (by rfl) ⟨1088501, by rfl⟩ : syracuseStep 5805341 = 2177003) B2177003
theorem B2823913 : Blo 1321479 2823913 := bstep (se 2 (by rfl) ⟨1058967, by rfl⟩ : syracuseStep 2823913 = 2117935) B2117935
theorem B11024549 : Blo 1321479 11024549 := bstep (se 4 (by rfl) ⟨1033551, by rfl⟩ : syracuseStep 11024549 = 2067103) B2067103
theorem B4462775 : Blo 1321479 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B38639915 : Blo 1321479 38639915 := bstep (se 1 (by rfl) ⟨28979936, by rfl⟩ : syracuseStep 38639915 = 57959873) B57959873
theorem B3766607 : Blo 1321479 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B4463207 : Blo 1321479 4463207 := bstep (se 1 (by rfl) ⟨3347405, by rfl⟩ : syracuseStep 4463207 = 6694811) B6694811
theorem B4234025 : Blo 1321479 4234025 := bstep (se 2 (by rfl) ⟨1587759, by rfl⟩ : syracuseStep 4234025 = 3175519) B3175519
theorem B6699995 : Blo 1321479 6699995 := bstep (se 1 (by rfl) ⟨5024996, by rfl⟩ : syracuseStep 6699995 = 10049993) B10049993
theorem B24116291 : Blo 1321479 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B16956701 : Blo 1321479 16956701 := bstep (se 3 (by rfl) ⟨3179381, by rfl⟩ : syracuseStep 16956701 = 6358763) B6358763
theorem B6356303 : Blo 1321479 6356303 := bstep (se 1 (by rfl) ⟨4767227, by rfl⟩ : syracuseStep 6356303 = 9534455) B9534455
theorem B38141279 : Blo 1321479 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B2825759 : Blo 1321479 2825759 := bstep (se 1 (by rfl) ⟨2119319, by rfl⟩ : syracuseStep 2825759 = 4238639) B4238639
theorem B5021291 : Blo 1321479 5021291 := bstep (se 1 (by rfl) ⟨3765968, by rfl⟩ : syracuseStep 5021291 = 7531937) B7531937
theorem B144834281 : Blo 1321479 144834281 := bstep (se 2 (by rfl) ⟨54312855, by rfl⟩ : syracuseStep 144834281 = 108625711) B108625711
theorem B5652287 : Blo 1321479 5652287 := bstep (se 1 (by rfl) ⟨4239215, by rfl⟩ : syracuseStep 5652287 = 8478431) B8478431
theorem B9527165 : Blo 1321479 9527165 := bstep (se 3 (by rfl) ⟨1786343, by rfl⟩ : syracuseStep 9527165 = 3572687) B3572687
theorem B2973671 : Blo 1321479 2973671 := bstep (se 1 (by rfl) ⟨2230253, by rfl⟩ : syracuseStep 2973671 = 4460507) B4460507
theorem B2973851 : Blo 1321479 2973851 := bstep (se 1 (by rfl) ⟨2230388, by rfl⟩ : syracuseStep 2973851 = 4460777) B4460777
theorem B3178651 : Blo 1321479 3178651 := bstep (se 1 (by rfl) ⟨2383988, by rfl⟩ : syracuseStep 3178651 = 4767977) B4767977
theorem B4464827 : Blo 1321479 4464827 := bstep (se 1 (by rfl) ⟨3348620, by rfl⟩ : syracuseStep 4464827 = 6697241) B6697241
theorem B1982687 : Blo 1321479 1982687 := bstep (se 1 (by rfl) ⟨1487015, by rfl⟩ : syracuseStep 1982687 = 2974031) B2974031
theorem B5021959 : Blo 1321479 5021959 := bstep (se 1 (by rfl) ⟨3766469, by rfl⟩ : syracuseStep 5021959 = 7532939) B7532939
theorem B3817849 : Blo 1321479 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B12394895 : Blo 1321479 12394895 := bstep (se 1 (by rfl) ⟨9296171, by rfl⟩ : syracuseStep 12394895 = 18592343) B18592343
theorem B2974121 : Blo 1321479 2974121 := bstep (se 2 (by rfl) ⟨1115295, by rfl⟩ : syracuseStep 2974121 = 2230591) B2230591
theorem B2974175 : Blo 1321479 2974175 := bstep (se 1 (by rfl) ⟨2230631, by rfl⟩ : syracuseStep 2974175 = 4461263) B4461263
theorem B1983131 : Blo 1321479 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B2974535 : Blo 1321479 2974535 := bstep (se 1 (by rfl) ⟨2230901, by rfl⟩ : syracuseStep 2974535 = 4461803) B4461803
theorem B37192567 : Blo 1321479 37192567 := bstep (se 1 (by rfl) ⟨27894425, by rfl⟩ : syracuseStep 37192567 = 55788851) B55788851
theorem B1983467 : Blo 1321479 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B7144699 : Blo 1321479 7144699 := bstep (se 1 (by rfl) ⟨5358524, by rfl⟩ : syracuseStep 7144699 = 10717049) B10717049
theorem B7349699 : Blo 1321479 7349699 := bstep (se 1 (by rfl) ⟨5512274, by rfl⟩ : syracuseStep 7349699 = 11024549) B11024549
theorem B2975183 : Blo 1321479 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B2975471 : Blo 1321479 2975471 := bstep (se 1 (by rfl) ⟨2231603, by rfl⟩ : syracuseStep 2975471 = 4463207) B4463207
theorem B4466663 : Blo 1321479 4466663 := bstep (se 1 (by rfl) ⟨3349997, by rfl⟩ : syracuseStep 4466663 = 6699995) B6699995
theorem B4024441 : Blo 1321479 4024441 := bstep (se 2 (by rfl) ⟨1509165, by rfl⟩ : syracuseStep 4024441 = 3018331) B3018331
theorem B5359823 : Blo 1321479 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B4237535 : Blo 1321479 4237535 := bstep (se 1 (by rfl) ⟨3178151, by rfl⟩ : syracuseStep 4237535 = 6356303) B6356303
theorem B2230699 : Blo 1321479 2230699 := bstep (se 1 (by rfl) ⟨1673024, by rfl⟩ : syracuseStep 2230699 = 3346049) B3346049
theorem B6351443 : Blo 1321479 6351443 := bstep (se 1 (by rfl) ⟨4763582, by rfl⟩ : syracuseStep 6351443 = 9527165) B9527165
theorem B10717895 : Blo 1321479 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B1321727 : Blo 1321479 1321727 := bstep (se 1 (by rfl) ⟨991295, by rfl⟩ : syracuseStep 1321727 = 1982591) B1982591
theorem B2231111 : Blo 1321479 2231111 := bstep (se 1 (by rfl) ⟨1673333, by rfl⟩ : syracuseStep 2231111 = 3346667) B3346667
theorem B87001937 : Blo 1321479 87001937 := bstep (se 2 (by rfl) ⟨32625726, by rfl⟩ : syracuseStep 87001937 = 65251453) B65251453
theorem B1322095 : Blo 1321479 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B1322143 : Blo 1321479 1322143 := bstep (se 1 (by rfl) ⟨991607, by rfl⟩ : syracuseStep 1322143 = 1983215) B1983215
theorem B1322175 : Blo 1321479 1322175 := bstep (se 1 (by rfl) ⟨991631, by rfl⟩ : syracuseStep 1322175 = 1983263) B1983263
theorem B2116891 : Blo 1321479 2116891 := bstep (se 1 (by rfl) ⟨1587668, by rfl⟩ : syracuseStep 2116891 = 3175337) B3175337
theorem B36187469 : Blo 1321479 36187469 := bstep (se 3 (by rfl) ⟨6785150, by rfl⟩ : syracuseStep 36187469 = 13570301) B13570301
theorem B2977145 : Blo 1321479 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B2231759 : Blo 1321479 2231759 := bstep (se 1 (by rfl) ⟨1673819, by rfl⟩ : syracuseStep 2231759 = 3347639) B3347639
theorem B3870227 : Blo 1321479 3870227 := bstep (se 1 (by rfl) ⟨2902670, by rfl⟩ : syracuseStep 3870227 = 5805341) B5805341
theorem B1322779 : Blo 1321479 1322779 := bstep (se 1 (by rfl) ⟨992084, by rfl⟩ : syracuseStep 1322779 = 1984169) B1984169
theorem B1322919 : Blo 1321479 1322919 := bstep (se 1 (by rfl) ⟨992189, by rfl⟩ : syracuseStep 1322919 = 1984379) B1984379
theorem B1323199 : Blo 1321479 1323199 := bstep (se 1 (by rfl) ⟨992399, by rfl⟩ : syracuseStep 1323199 = 1984799) B1984799
theorem B25759943 : Blo 1321479 25759943 := bstep (se 1 (by rfl) ⟨19319957, by rfl⟩ : syracuseStep 25759943 = 38639915) B38639915
theorem B2511071 : Blo 1321479 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B1323311 : Blo 1321479 1323311 := bstep (se 1 (by rfl) ⟨992483, by rfl⟩ : syracuseStep 1323311 = 1984967) B1984967
theorem B1487263 : Blo 1321479 1487263 := bstep (se 1 (by rfl) ⟨1115447, by rfl⟩ : syracuseStep 1487263 = 2230895) B2230895
theorem B1487335 : Blo 1321479 1487335 := bstep (se 1 (by rfl) ⟨1115501, by rfl⟩ : syracuseStep 1487335 = 2231003) B2231003
theorem B2822683 : Blo 1321479 2822683 := bstep (se 1 (by rfl) ⟨2117012, by rfl⟩ : syracuseStep 2822683 = 4234025) B4234025
theorem B16077527 : Blo 1321479 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B3765217 : Blo 1321479 3765217 := bstep (se 2 (by rfl) ⟨1411956, by rfl⟩ : syracuseStep 3765217 = 2823913) B2823913
theorem B3347527 : Blo 1321479 3347527 := bstep (se 1 (by rfl) ⟨2510645, by rfl⟩ : syracuseStep 3347527 = 5021291) B5021291
theorem B28587097 : Blo 1321479 28587097 := bstep (se 2 (by rfl) ⟨10720161, by rfl⟩ : syracuseStep 28587097 = 21440323) B21440323
theorem B96556187 : Blo 1321479 96556187 := bstep (se 1 (by rfl) ⟨72417140, by rfl⟩ : syracuseStep 96556187 = 144834281) B144834281
theorem B3175615 : Blo 1321479 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B1488199 : Blo 1321479 1488199 := bstep (se 1 (by rfl) ⟨1116149, by rfl⟩ : syracuseStep 1488199 = 2232299) B2232299
theorem B6034895 : Blo 1321479 6034895 := bstep (se 1 (by rfl) ⟨4526171, by rfl⟩ : syracuseStep 6034895 = 9052343) B9052343
theorem B10868527 : Blo 1321479 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B4462397 : Blo 1321479 4462397 := bstep (se 3 (by rfl) ⟨836699, by rfl⟩ : syracuseStep 4462397 = 1673399) B1673399
theorem B3349097 : Blo 1321479 3349097 := bstep (se 2 (by rfl) ⟨1255911, by rfl⟩ : syracuseStep 3349097 = 2511823) B2511823
theorem B3349147 : Blo 1321479 3349147 := bstep (se 1 (by rfl) ⟨2511860, by rfl⟩ : syracuseStep 3349147 = 5023721) B5023721
theorem B7527289 : Blo 1321479 7527289 := bstep (se 2 (by rfl) ⟨2822733, by rfl⟩ : syracuseStep 7527289 = 5645467) B5645467
theorem B209083283 : Blo 1321479 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B15064055 : Blo 1321479 15064055 := bstep (se 1 (by rfl) ⟨11298041, by rfl⟩ : syracuseStep 15064055 = 22596083) B22596083
theorem B11296097 : Blo 1321479 11296097 := bstep (se 2 (by rfl) ⟨4236036, by rfl⟩ : syracuseStep 11296097 = 8472073) B8472073
theorem B11304467 : Blo 1321479 11304467 := bstep (se 1 (by rfl) ⟨8478350, by rfl⟩ : syracuseStep 11304467 = 16956701) B16956701
theorem B14491199 : Blo 1321479 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B25427519 : Blo 1321479 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B1883839 : Blo 1321479 1883839 := bstep (se 1 (by rfl) ⟨1412879, by rfl⟩ : syracuseStep 1883839 = 2825759) B2825759
theorem B3768191 : Blo 1321479 3768191 := bstep (se 1 (by rfl) ⟨2826143, by rfl⟩ : syracuseStep 3768191 = 5652287) B5652287
theorem B1982447 : Blo 1321479 1982447 := bstep (se 1 (by rfl) ⟨1486835, by rfl⟩ : syracuseStep 1982447 = 2973671) B2973671
theorem B1982567 : Blo 1321479 1982567 := bstep (se 1 (by rfl) ⟨1486925, by rfl⟩ : syracuseStep 1982567 = 2973851) B2973851
theorem B5365921 : Blo 1321479 5365921 := bstep (se 2 (by rfl) ⟨2012220, by rfl⟩ : syracuseStep 5365921 = 4024441) B4024441
theorem B1982747 : Blo 1321479 1982747 := bstep (se 1 (by rfl) ⟨1487060, by rfl⟩ : syracuseStep 1982747 = 2974121) B2974121
theorem B1982783 : Blo 1321479 1982783 := bstep (se 1 (by rfl) ⟨1487087, by rfl⟩ : syracuseStep 1982783 = 2974175) B2974175
theorem B1983017 : Blo 1321479 1983017 := bstep (se 2 (by rfl) ⟨743631, by rfl⟩ : syracuseStep 1983017 = 1487263) B1487263
theorem B1983023 : Blo 1321479 1983023 := bstep (se 1 (by rfl) ⟨1487267, by rfl⟩ : syracuseStep 1983023 = 2974535) B2974535
theorem B2974265 : Blo 1321479 2974265 := bstep (se 2 (by rfl) ⟨1115349, by rfl⟩ : syracuseStep 2974265 = 2230699) B2230699
theorem B1983113 : Blo 1321479 1983113 := bstep (se 2 (by rfl) ⟨743667, by rfl⟩ : syracuseStep 1983113 = 1487335) B1487335
theorem B4465529 : Blo 1321479 4465529 := bstep (se 2 (by rfl) ⟨1674573, by rfl⟩ : syracuseStep 4465529 = 3349147) B3349147
theorem B4899799 : Blo 1321479 4899799 := bstep (se 1 (by rfl) ⟨3674849, by rfl⟩ : syracuseStep 4899799 = 7349699) B7349699
theorem B1983455 : Blo 1321479 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B4023263 : Blo 1321479 4023263 := bstep (se 1 (by rfl) ⟨3017447, by rfl⟩ : syracuseStep 4023263 = 6034895) B6034895
theorem B1983647 : Blo 1321479 1983647 := bstep (se 1 (by rfl) ⟨1487735, by rfl⟩ : syracuseStep 1983647 = 2975471) B2975471
theorem B10036385 : Blo 1321479 10036385 := bstep (se 2 (by rfl) ⟨3763644, by rfl⟩ : syracuseStep 10036385 = 7527289) B7527289
theorem B2974931 : Blo 1321479 2974931 := bstep (se 1 (by rfl) ⟨2231198, by rfl⟩ : syracuseStep 2974931 = 4462397) B4462397
theorem B3573215 : Blo 1321479 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B1984265 : Blo 1321479 1984265 := bstep (se 2 (by rfl) ⟨744099, by rfl⟩ : syracuseStep 1984265 = 1488199) B1488199
theorem B7145263 : Blo 1321479 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B58001291 : Blo 1321479 58001291 := bstep (se 1 (by rfl) ⟨43500968, by rfl⟩ : syracuseStep 58001291 = 87001937) B87001937
theorem B139388855 : Blo 1321479 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B7530731 : Blo 1321479 7530731 := bstep (se 1 (by rfl) ⟨5648048, by rfl⟩ : syracuseStep 7530731 = 11296097) B11296097
theorem B1984763 : Blo 1321479 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B9660799 : Blo 1321479 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B16951679 : Blo 1321479 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B1321631 : Blo 1321479 1321631 := bstep (se 1 (by rfl) ⟨991223, by rfl⟩ : syracuseStep 1321631 = 1982447) B1982447
theorem B2976551 : Blo 1321479 2976551 := bstep (se 1 (by rfl) ⟨2232413, by rfl⟩ : syracuseStep 2976551 = 4464827) B4464827
theorem B17173295 : Blo 1321479 17173295 := bstep (se 1 (by rfl) ⟨12879971, by rfl⟩ : syracuseStep 17173295 = 25759943) B25759943
theorem B1321791 : Blo 1321479 1321791 := bstep (se 1 (by rfl) ⟨991343, by rfl⟩ : syracuseStep 1321791 = 1982687) B1982687
theorem B1674047 : Blo 1321479 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B4238201 : Blo 1321479 4238201 := bstep (se 2 (by rfl) ⟨1589325, by rfl⟩ : syracuseStep 4238201 = 3178651) B3178651
theorem B6695945 : Blo 1321479 6695945 := bstep (se 2 (by rfl) ⟨2510979, by rfl⟩ : syracuseStep 6695945 = 5021959) B5021959
theorem B1322087 : Blo 1321479 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B10718351 : Blo 1321479 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B5090465 : Blo 1321479 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B11300093 : Blo 1321479 11300093 := bstep (se 3 (by rfl) ⟨2118767, by rfl⟩ : syracuseStep 11300093 = 4237535) B4237535
theorem B1322311 : Blo 1321479 1322311 := bstep (se 1 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 1322311 = 1983467) B1983467
theorem B3763577 : Blo 1321479 3763577 := bstep (se 2 (by rfl) ⟨1411341, by rfl⟩ : syracuseStep 3763577 = 2822683) B2822683
theorem B49590089 : Blo 1321479 49590089 := bstep (se 2 (by rfl) ⟨18596283, by rfl⟩ : syracuseStep 49590089 = 37192567) B37192567
theorem B2977775 : Blo 1321479 2977775 := bstep (se 1 (by rfl) ⟨2233331, by rfl⟩ : syracuseStep 2977775 = 4466663) B4466663
theorem B2822521 : Blo 1321479 2822521 := bstep (se 2 (by rfl) ⟨1058445, by rfl⟩ : syracuseStep 2822521 = 2116891) B2116891
theorem B2232731 : Blo 1321479 2232731 := bstep (se 1 (by rfl) ⟨1674548, by rfl⟩ : syracuseStep 2232731 = 3349097) B3349097
theorem B1487407 : Blo 1321479 1487407 := bstep (se 1 (by rfl) ⟨1115555, by rfl⟩ : syracuseStep 1487407 = 2231111) B2231111
theorem B2511785 : Blo 1321479 2511785 := bstep (se 2 (by rfl) ⟨941919, by rfl⟩ : syracuseStep 2511785 = 1883839) B1883839
theorem B1487839 : Blo 1321479 1487839 := bstep (se 1 (by rfl) ⟨1115879, by rfl⟩ : syracuseStep 1487839 = 2231759) B2231759
theorem B2512127 : Blo 1321479 2512127 := bstep (se 1 (by rfl) ⟨1884095, by rfl⟩ : syracuseStep 2512127 = 3768191) B3768191
theorem B64370791 : Blo 1321479 64370791 := bstep (se 1 (by rfl) ⟨48278093, by rfl⟩ : syracuseStep 64370791 = 96556187) B96556187
theorem B33053053 : Blo 1321479 33053053 := bstep (se 3 (by rfl) ⟨6197447, by rfl⟩ : syracuseStep 33053053 = 12394895) B12394895
theorem B5020289 : Blo 1321479 5020289 := bstep (se 2 (by rfl) ⟨1882608, by rfl⟩ : syracuseStep 5020289 = 3765217) B3765217
theorem B4463369 : Blo 1321479 4463369 := bstep (se 2 (by rfl) ⟨1673763, by rfl⟩ : syracuseStep 4463369 = 3347527) B3347527
theorem B38116129 : Blo 1321479 38116129 := bstep (se 2 (by rfl) ⟨14293548, by rfl⟩ : syracuseStep 38116129 = 28587097) B28587097
theorem B4234153 : Blo 1321479 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B9526265 : Blo 1321479 9526265 := bstep (se 2 (by rfl) ⟨3572349, by rfl⟩ : syracuseStep 9526265 = 7144699) B7144699
theorem B4234295 : Blo 1321479 4234295 := bstep (se 1 (by rfl) ⟨3175721, by rfl⟩ : syracuseStep 4234295 = 6351443) B6351443
theorem B10042703 : Blo 1321479 10042703 := bstep (se 1 (by rfl) ⟨7532027, by rfl⟩ : syracuseStep 10042703 = 15064055) B15064055
theorem B24124979 : Blo 1321479 24124979 := bstep (se 1 (by rfl) ⟨18093734, by rfl⟩ : syracuseStep 24124979 = 36187469) B36187469
theorem B2580151 : Blo 1321479 2580151 := bstep (se 1 (by rfl) ⟨1935113, by rfl⟩ : syracuseStep 2580151 = 3870227) B3870227
theorem B7536311 : Blo 1321479 7536311 := bstep (se 1 (by rfl) ⟨5652233, by rfl⟩ : syracuseStep 7536311 = 11304467) B11304467
theorem B14491369 : Blo 1321479 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B85827721 : Blo 1321479 85827721 := bstep (se 2 (by rfl) ⟨32185395, by rfl⟩ : syracuseStep 85827721 = 64370791) B64370791
theorem B1982843 : Blo 1321479 1982843 := bstep (se 1 (by rfl) ⟨1487132, by rfl⟩ : syracuseStep 1982843 = 2974265) B2974265
theorem B13574573 : Blo 1321479 13574573 := bstep (se 3 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 13574573 = 5090465) B5090465
theorem B1983209 : Blo 1321479 1983209 := bstep (se 2 (by rfl) ⟨743703, by rfl⟩ : syracuseStep 1983209 = 1487407) B1487407
theorem B1983287 : Blo 1321479 1983287 := bstep (se 1 (by rfl) ⟨1487465, by rfl⟩ : syracuseStep 1983287 = 2974931) B2974931
theorem B5645537 : Blo 1321479 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B38667527 : Blo 1321479 38667527 := bstep (se 1 (by rfl) ⟨29000645, by rfl⟩ : syracuseStep 38667527 = 58001291) B58001291
theorem B1983785 : Blo 1321479 1983785 := bstep (se 2 (by rfl) ⟨743919, by rfl⟩ : syracuseStep 1983785 = 1487839) B1487839
theorem B2975579 : Blo 1321479 2975579 := bstep (se 1 (by rfl) ⟨2231684, by rfl⟩ : syracuseStep 2975579 = 4463369) B4463369
theorem B1984367 : Blo 1321479 1984367 := bstep (se 1 (by rfl) ⟨1488275, by rfl⟩ : syracuseStep 1984367 = 2976551) B2976551
theorem B6350843 : Blo 1321479 6350843 := bstep (se 1 (by rfl) ⟨4763132, by rfl⟩ : syracuseStep 6350843 = 9526265) B9526265
theorem B7145567 : Blo 1321479 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B6695135 : Blo 1321479 6695135 := bstep (se 1 (by rfl) ⟨5021351, by rfl⟩ : syracuseStep 6695135 = 10042703) B10042703
theorem B2509051 : Blo 1321479 2509051 := bstep (se 1 (by rfl) ⟨1881788, by rfl⟩ : syracuseStep 2509051 = 3763577) B3763577
theorem B16083319 : Blo 1321479 16083319 := bstep (se 1 (by rfl) ⟨12062489, by rfl⟩ : syracuseStep 16083319 = 24124979) B24124979
theorem B5024207 : Blo 1321479 5024207 := bstep (se 1 (by rfl) ⟨3768155, by rfl⟩ : syracuseStep 5024207 = 7536311) B7536311
theorem B1985183 : Blo 1321479 1985183 := bstep (se 1 (by rfl) ⟨1488887, by rfl⟩ : syracuseStep 1985183 = 2977775) B2977775
theorem B1321711 : Blo 1321479 1321711 := bstep (se 1 (by rfl) ⟨991283, by rfl⟩ : syracuseStep 1321711 = 1982567) B1982567
theorem B1321831 : Blo 1321479 1321831 := bstep (se 1 (by rfl) ⟨991373, by rfl⟩ : syracuseStep 1321831 = 1982747) B1982747
theorem B1321855 : Blo 1321479 1321855 := bstep (se 1 (by rfl) ⟨991391, by rfl⟩ : syracuseStep 1321855 = 1982783) B1982783
theorem B7154561 : Blo 1321479 7154561 := bstep (se 2 (by rfl) ⟨2682960, by rfl⟩ : syracuseStep 7154561 = 5365921) B5365921
theorem B1322011 : Blo 1321479 1322011 := bstep (se 1 (by rfl) ⟨991508, by rfl⟩ : syracuseStep 1322011 = 1983017) B1983017
theorem B1322015 : Blo 1321479 1322015 := bstep (se 1 (by rfl) ⟨991511, by rfl⟩ : syracuseStep 1322015 = 1983023) B1983023
theorem B1322075 : Blo 1321479 1322075 := bstep (se 1 (by rfl) ⟨991556, by rfl⟩ : syracuseStep 1322075 = 1983113) B1983113
theorem B3763361 : Blo 1321479 3763361 := bstep (se 2 (by rfl) ⟨1411260, by rfl⟩ : syracuseStep 3763361 = 2822521) B2822521
theorem B12881065 : Blo 1321479 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B2977019 : Blo 1321479 2977019 := bstep (se 1 (by rfl) ⟨2232764, by rfl⟩ : syracuseStep 2977019 = 4465529) B4465529
theorem B1674523 : Blo 1321479 1674523 := bstep (se 1 (by rfl) ⟨1255892, by rfl⟩ : syracuseStep 1674523 = 2511785) B2511785
theorem B1322303 : Blo 1321479 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B2682175 : Blo 1321479 2682175 := bstep (se 1 (by rfl) ⟨2011631, by rfl⟩ : syracuseStep 2682175 = 4023263) B4023263
theorem B1322431 : Blo 1321479 1322431 := bstep (se 1 (by rfl) ⟨991823, by rfl⟩ : syracuseStep 1322431 = 1983647) B1983647
theorem B1674751 : Blo 1321479 1674751 := bstep (se 1 (by rfl) ⟨1256063, by rfl⟩ : syracuseStep 1674751 = 2512127) B2512127
theorem B1322843 : Blo 1321479 1322843 := bstep (se 1 (by rfl) ⟨992132, by rfl⟩ : syracuseStep 1322843 = 1984265) B1984265
theorem B6533065 : Blo 1321479 6533065 := bstep (se 2 (by rfl) ⟨2449899, by rfl⟩ : syracuseStep 6533065 = 4899799) B4899799
theorem B1323175 : Blo 1321479 1323175 := bstep (se 1 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 1323175 = 1984763) B1984763
theorem B11301119 : Blo 1321479 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B3346859 : Blo 1321479 3346859 := bstep (se 1 (by rfl) ⟨2510144, by rfl⟩ : syracuseStep 3346859 = 5020289) B5020289
theorem B11448863 : Blo 1321479 11448863 := bstep (se 1 (by rfl) ⟨8586647, by rfl⟩ : syracuseStep 11448863 = 17173295) B17173295
theorem B2822863 : Blo 1321479 2822863 := bstep (se 1 (by rfl) ⟨2117147, by rfl⟩ : syracuseStep 2822863 = 4234295) B4234295
theorem B7533395 : Blo 1321479 7533395 := bstep (se 1 (by rfl) ⟨5650046, by rfl⟩ : syracuseStep 7533395 = 11300093) B11300093
theorem B19321825 : Blo 1321479 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B11301869 : Blo 1321479 11301869 := bstep (se 3 (by rfl) ⟨2119100, by rfl⟩ : syracuseStep 11301869 = 4238201) B4238201
theorem B33060059 : Blo 1321479 33060059 := bstep (se 1 (by rfl) ⟨24795044, by rfl⟩ : syracuseStep 33060059 = 49590089) B49590089
theorem B1488487 : Blo 1321479 1488487 := bstep (se 1 (by rfl) ⟨1116365, by rfl⟩ : syracuseStep 1488487 = 2232731) B2232731
theorem B44070737 : Blo 1321479 44070737 := bstep (se 2 (by rfl) ⟨16526526, by rfl⟩ : syracuseStep 44070737 = 33053053) B33053053
theorem B6690923 : Blo 1321479 6690923 := bstep (se 1 (by rfl) ⟨5018192, by rfl⟩ : syracuseStep 6690923 = 10036385) B10036385
theorem B2382143 : Blo 1321479 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B50821505 : Blo 1321479 50821505 := bstep (se 2 (by rfl) ⟨19058064, by rfl⟩ : syracuseStep 50821505 = 38116129) B38116129
theorem B5020487 : Blo 1321479 5020487 := bstep (se 1 (by rfl) ⟨3765365, by rfl⟩ : syracuseStep 5020487 = 7530731) B7530731
theorem B4463963 : Blo 1321479 4463963 := bstep (se 1 (by rfl) ⟨3347972, by rfl⟩ : syracuseStep 4463963 = 6695945) B6695945
theorem B4464125 : Blo 1321479 4464125 := bstep (se 3 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 4464125 = 1674047) B1674047
theorem B3440201 : Blo 1321479 3440201 := bstep (se 2 (by rfl) ⟨1290075, by rfl⟩ : syracuseStep 3440201 = 2580151) B2580151
theorem B9527017 : Blo 1321479 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B371703613 : Blo 1321479 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B5022263 : Blo 1321479 5022263 := bstep (se 1 (by rfl) ⟨3766697, by rfl⟩ : syracuseStep 5022263 = 7533395) B7533395
theorem B1983719 : Blo 1321479 1983719 := bstep (se 1 (by rfl) ⟨1487789, by rfl⟩ : syracuseStep 1983719 = 2975579) B2975579
theorem B4769707 : Blo 1321479 4769707 := bstep (se 1 (by rfl) ⟨3577280, by rfl⟩ : syracuseStep 4769707 = 7154561) B7154561
theorem B2508907 : Blo 1321479 2508907 := bstep (se 1 (by rfl) ⟨1881680, by rfl⟩ : syracuseStep 2508907 = 3763361) B3763361
theorem B1984649 : Blo 1321479 1984649 := bstep (se 2 (by rfl) ⟨744243, by rfl⟩ : syracuseStep 1984649 = 1488487) B1488487
theorem B1984679 : Blo 1321479 1984679 := bstep (se 1 (by rfl) ⟨1488509, by rfl⟩ : syracuseStep 1984679 = 2977019) B2977019
theorem B2975975 : Blo 1321479 2975975 := bstep (se 1 (by rfl) ⟨2231981, by rfl⟩ : syracuseStep 2975975 = 4463963) B4463963
theorem B2976083 : Blo 1321479 2976083 := bstep (se 1 (by rfl) ⟨2232062, by rfl⟩ : syracuseStep 2976083 = 4464125) B4464125
theorem B8710753 : Blo 1321479 8710753 := bstep (se 2 (by rfl) ⟨3266532, by rfl⟩ : syracuseStep 8710753 = 6533065) B6533065
theorem B16935581 : Blo 1321479 16935581 := bstep (se 3 (by rfl) ⟨3175421, by rfl⟩ : syracuseStep 16935581 = 6350843) B6350843
theorem B114436961 : Blo 1321479 114436961 := bstep (se 2 (by rfl) ⟨42913860, by rfl⟩ : syracuseStep 114436961 = 85827721) B85827721
theorem B1321895 : Blo 1321479 1321895 := bstep (se 1 (by rfl) ⟨991421, by rfl⟩ : syracuseStep 1321895 = 1982843) B1982843
theorem B2231239 : Blo 1321479 2231239 := bstep (se 1 (by rfl) ⟨1673429, by rfl⟩ : syracuseStep 2231239 = 3346859) B3346859
theorem B3345401 : Blo 1321479 3345401 := bstep (se 2 (by rfl) ⟨1254525, by rfl⟩ : syracuseStep 3345401 = 2509051) B2509051
theorem B1322139 : Blo 1321479 1322139 := bstep (se 1 (by rfl) ⟨991604, by rfl⟩ : syracuseStep 1322139 = 1983209) B1983209
theorem B1322191 : Blo 1321479 1322191 := bstep (se 1 (by rfl) ⟨991643, by rfl⟩ : syracuseStep 1322191 = 1983287) B1983287
theorem B36695477 : Blo 1321479 36695477 := bstep (se 5 (by rfl) ⟨1720100, by rfl⟩ : syracuseStep 36695477 = 3440201) B3440201
theorem B22040039 : Blo 1321479 22040039 := bstep (se 1 (by rfl) ⟨16530029, by rfl⟩ : syracuseStep 22040039 = 33060059) B33060059
theorem B3763691 : Blo 1321479 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B6352381 : Blo 1321479 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B1322523 : Blo 1321479 1322523 := bstep (se 1 (by rfl) ⟨991892, by rfl⟩ : syracuseStep 1322523 = 1983785) B1983785
theorem B3763817 : Blo 1321479 3763817 := bstep (se 2 (by rfl) ⟨1411431, by rfl⟩ : syracuseStep 3763817 = 2822863) B2822863
theorem B1322911 : Blo 1321479 1322911 := bstep (se 1 (by rfl) ⟨992183, by rfl⟩ : syracuseStep 1322911 = 1984367) B1984367
theorem B4763711 : Blo 1321479 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B4460615 : Blo 1321479 4460615 := bstep (se 1 (by rfl) ⟨3345461, by rfl⟩ : syracuseStep 4460615 = 6690923) B6690923
theorem B17174753 : Blo 1321479 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B2232697 : Blo 1321479 2232697 := bstep (se 2 (by rfl) ⟨837261, by rfl⟩ : syracuseStep 2232697 = 1674523) B1674523
theorem B3576233 : Blo 1321479 3576233 := bstep (se 2 (by rfl) ⟨1341087, by rfl⟩ : syracuseStep 3576233 = 2682175) B2682175
theorem B1323455 : Blo 1321479 1323455 := bstep (se 1 (by rfl) ⟨992591, by rfl⟩ : syracuseStep 1323455 = 1985183) B1985183
theorem B3346991 : Blo 1321479 3346991 := bstep (se 1 (by rfl) ⟨2510243, by rfl⟩ : syracuseStep 3346991 = 5020487) B5020487
theorem B2233001 : Blo 1321479 2233001 := bstep (se 2 (by rfl) ⟨837375, by rfl⟩ : syracuseStep 2233001 = 1674751) B1674751
theorem B12702689 : Blo 1321479 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B495604817 : Blo 1321479 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B7534079 : Blo 1321479 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B9049715 : Blo 1321479 9049715 := bstep (se 1 (by rfl) ⟨6787286, by rfl⟩ : syracuseStep 9049715 = 13574573) B13574573
theorem B7632575 : Blo 1321479 7632575 := bstep (se 1 (by rfl) ⟨5724431, by rfl⟩ : syracuseStep 7632575 = 11448863) B11448863
theorem B21444425 : Blo 1321479 21444425 := bstep (se 2 (by rfl) ⟨8041659, by rfl⟩ : syracuseStep 21444425 = 16083319) B16083319
theorem B7534579 : Blo 1321479 7534579 := bstep (se 1 (by rfl) ⟨5650934, by rfl⟩ : syracuseStep 7534579 = 11301869) B11301869
theorem B25778351 : Blo 1321479 25778351 := bstep (se 1 (by rfl) ⟨19333763, by rfl⟩ : syracuseStep 25778351 = 38667527) B38667527
theorem B25762433 : Blo 1321479 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B4463423 : Blo 1321479 4463423 := bstep (se 1 (by rfl) ⟨3347567, by rfl⟩ : syracuseStep 4463423 = 6695135) B6695135
theorem B33881003 : Blo 1321479 33881003 := bstep (se 1 (by rfl) ⟨25410752, by rfl⟩ : syracuseStep 33881003 = 50821505) B50821505
theorem B3349471 : Blo 1321479 3349471 := bstep (se 1 (by rfl) ⟨2512103, by rfl⟩ : syracuseStep 3349471 = 5024207) B5024207
theorem B117521965 : Blo 1321479 117521965 := bstep (se 3 (by rfl) ⟨22035368, by rfl⟩ : syracuseStep 117521965 = 44070737) B44070737
theorem B2973743 : Blo 1321479 2973743 := bstep (se 1 (by rfl) ⟨2230307, by rfl⟩ : syracuseStep 2973743 = 4460615) B4460615
theorem B2384155 : Blo 1321479 2384155 := bstep (se 1 (by rfl) ⟨1788116, by rfl⟩ : syracuseStep 2384155 = 3576233) B3576233
theorem B5022719 : Blo 1321479 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B5088383 : Blo 1321479 5088383 := bstep (se 1 (by rfl) ⟨3816287, by rfl⟩ : syracuseStep 5088383 = 7632575) B7632575
theorem B97854605 : Blo 1321479 97854605 := bstep (se 3 (by rfl) ⟨18347738, by rfl⟩ : syracuseStep 97854605 = 36695477) B36695477
theorem B14296283 : Blo 1321479 14296283 := bstep (se 1 (by rfl) ⟨10722212, by rfl⟩ : syracuseStep 14296283 = 21444425) B21444425
theorem B2974985 : Blo 1321479 2974985 := bstep (se 2 (by rfl) ⟨1115619, by rfl⟩ : syracuseStep 2974985 = 2231239) B2231239
theorem B4465961 : Blo 1321479 4465961 := bstep (se 2 (by rfl) ⟨1674735, by rfl⟩ : syracuseStep 4465961 = 3349471) B3349471
theorem B1983983 : Blo 1321479 1983983 := bstep (se 1 (by rfl) ⟨1487987, by rfl⟩ : syracuseStep 1983983 = 2975975) B2975975
theorem B1984055 : Blo 1321479 1984055 := bstep (se 1 (by rfl) ⟨1488041, by rfl⟩ : syracuseStep 1984055 = 2976083) B2976083
theorem B68699821 : Blo 1321479 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B11290387 : Blo 1321479 11290387 := bstep (se 1 (by rfl) ⟨8467790, by rfl⟩ : syracuseStep 11290387 = 16935581) B16935581
theorem B2975615 : Blo 1321479 2975615 := bstep (se 1 (by rfl) ⟨2231711, by rfl⟩ : syracuseStep 2975615 = 4463423) B4463423
theorem B22587335 : Blo 1321479 22587335 := bstep (se 1 (by rfl) ⟨16940501, by rfl⟩ : syracuseStep 22587335 = 33881003) B33881003
theorem B2230267 : Blo 1321479 2230267 := bstep (se 1 (by rfl) ⟨1672700, by rfl⟩ : syracuseStep 2230267 = 3345401) B3345401
theorem B2509127 : Blo 1321479 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B2509211 : Blo 1321479 2509211 := bstep (se 1 (by rfl) ⟨1881908, by rfl⟩ : syracuseStep 2509211 = 3763817) B3763817
theorem B6359609 : Blo 1321479 6359609 := bstep (se 2 (by rfl) ⟨2384853, by rfl⟩ : syracuseStep 6359609 = 4769707) B4769707
theorem B10046105 : Blo 1321479 10046105 := bstep (se 2 (by rfl) ⟨3767289, by rfl⟩ : syracuseStep 10046105 = 7534579) B7534579
theorem B3345209 : Blo 1321479 3345209 := bstep (se 2 (by rfl) ⟨1254453, by rfl⟩ : syracuseStep 3345209 = 2508907) B2508907
theorem B2231327 : Blo 1321479 2231327 := bstep (se 1 (by rfl) ⟨1673495, by rfl⟩ : syracuseStep 2231327 = 3346991) B3346991
theorem B2976929 : Blo 1321479 2976929 := bstep (se 2 (by rfl) ⟨1116348, by rfl⟩ : syracuseStep 2976929 = 2232697) B2232697
theorem B330403211 : Blo 1321479 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B1322479 : Blo 1321479 1322479 := bstep (se 1 (by rfl) ⟨991859, by rfl⟩ : syracuseStep 1322479 = 1983719) B1983719
theorem B6033143 : Blo 1321479 6033143 := bstep (se 1 (by rfl) ⟨4524857, by rfl⟩ : syracuseStep 6033143 = 9049715) B9049715
theorem B58773437 : Blo 1321479 58773437 := bstep (se 3 (by rfl) ⟨11020019, by rfl⟩ : syracuseStep 58773437 = 22040039) B22040039
theorem B1323099 : Blo 1321479 1323099 := bstep (se 1 (by rfl) ⟨992324, by rfl⟩ : syracuseStep 1323099 = 1984649) B1984649
theorem B1323119 : Blo 1321479 1323119 := bstep (se 1 (by rfl) ⟨992339, by rfl⟩ : syracuseStep 1323119 = 1984679) B1984679
theorem B3175807 : Blo 1321479 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B11449835 : Blo 1321479 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B3348175 : Blo 1321479 3348175 := bstep (se 1 (by rfl) ⟨2511131, by rfl⟩ : syracuseStep 3348175 = 5022263) B5022263
theorem B1488667 : Blo 1321479 1488667 := bstep (se 1 (by rfl) ⟨1116500, by rfl⟩ : syracuseStep 1488667 = 2233001) B2233001
theorem B8468459 : Blo 1321479 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B11614337 : Blo 1321479 11614337 := bstep (se 2 (by rfl) ⟨4355376, by rfl⟩ : syracuseStep 11614337 = 8710753) B8710753
theorem B17185567 : Blo 1321479 17185567 := bstep (se 1 (by rfl) ⟨12889175, by rfl⟩ : syracuseStep 17185567 = 25778351) B25778351
theorem B76291307 : Blo 1321479 76291307 := bstep (se 1 (by rfl) ⟨57218480, by rfl⟩ : syracuseStep 76291307 = 114436961) B114436961
theorem B8469841 : Blo 1321479 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B156695953 : Blo 1321479 156695953 := bstep (se 2 (by rfl) ⟨58760982, by rfl⟩ : syracuseStep 156695953 = 117521965) B117521965
theorem B1982495 : Blo 1321479 1982495 := bstep (se 1 (by rfl) ⟨1486871, by rfl⟩ : syracuseStep 1982495 = 2973743) B2973743
theorem B3178873 : Blo 1321479 3178873 := bstep (se 2 (by rfl) ⟨1192077, by rfl⟩ : syracuseStep 3178873 = 2384155) B2384155
theorem B3392255 : Blo 1321479 3392255 := bstep (se 1 (by rfl) ⟨2544191, by rfl⟩ : syracuseStep 3392255 = 5088383) B5088383
theorem B1983323 : Blo 1321479 1983323 := bstep (se 1 (by rfl) ⟨1487492, by rfl⟩ : syracuseStep 1983323 = 2974985) B2974985
theorem B22914089 : Blo 1321479 22914089 := bstep (se 2 (by rfl) ⟨8592783, by rfl⟩ : syracuseStep 22914089 = 17185567) B17185567
theorem B1983743 : Blo 1321479 1983743 := bstep (se 1 (by rfl) ⟨1487807, by rfl⟩ : syracuseStep 1983743 = 2975615) B2975615
theorem B15058223 : Blo 1321479 15058223 := bstep (se 1 (by rfl) ⟨11293667, by rfl⟩ : syracuseStep 15058223 = 22587335) B22587335
theorem B5645639 : Blo 1321479 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B7742891 : Blo 1321479 7742891 := bstep (se 1 (by rfl) ⟨5807168, by rfl⟩ : syracuseStep 7742891 = 11614337) B11614337
theorem B1672751 : Blo 1321479 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B1672807 : Blo 1321479 1672807 := bstep (se 1 (by rfl) ⟨1254605, by rfl⟩ : syracuseStep 1672807 = 2509211) B2509211
theorem B2230139 : Blo 1321479 2230139 := bstep (se 1 (by rfl) ⟨1672604, by rfl⟩ : syracuseStep 2230139 = 3345209) B3345209
theorem B1984619 : Blo 1321479 1984619 := bstep (se 1 (by rfl) ⟨1488464, by rfl⟩ : syracuseStep 1984619 = 2976929) B2976929
theorem B220268807 : Blo 1321479 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B1984889 : Blo 1321479 1984889 := bstep (se 2 (by rfl) ⟨744333, by rfl⟩ : syracuseStep 1984889 = 1488667) B1488667
theorem B65236403 : Blo 1321479 65236403 := bstep (se 1 (by rfl) ⟨48927302, by rfl⟩ : syracuseStep 65236403 = 97854605) B97854605
theorem B9530855 : Blo 1321479 9530855 := bstep (se 1 (by rfl) ⟨7148141, by rfl⟩ : syracuseStep 9530855 = 14296283) B14296283
theorem B2977307 : Blo 1321479 2977307 := bstep (se 1 (by rfl) ⟨2232980, by rfl⟩ : syracuseStep 2977307 = 4465961) B4465961
theorem B1322655 : Blo 1321479 1322655 := bstep (se 1 (by rfl) ⟨991991, by rfl⟩ : syracuseStep 1322655 = 1983983) B1983983
theorem B1322703 : Blo 1321479 1322703 := bstep (se 1 (by rfl) ⟨992027, by rfl⟩ : syracuseStep 1322703 = 1984055) B1984055
theorem B4239739 : Blo 1321479 4239739 := bstep (se 1 (by rfl) ⟨3179804, by rfl⟩ : syracuseStep 4239739 = 6359609) B6359609
theorem B6697403 : Blo 1321479 6697403 := bstep (se 1 (by rfl) ⟨5023052, by rfl⟩ : syracuseStep 6697403 = 10046105) B10046105
theorem B11293121 : Blo 1321479 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B1487551 : Blo 1321479 1487551 := bstep (se 1 (by rfl) ⟨1115663, by rfl⟩ : syracuseStep 1487551 = 2231327) B2231327
theorem B50860871 : Blo 1321479 50860871 := bstep (se 1 (by rfl) ⟨38145653, by rfl⟩ : syracuseStep 50860871 = 76291307) B76291307
theorem B91599761 : Blo 1321479 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B15053849 : Blo 1321479 15053849 := bstep (se 2 (by rfl) ⟨5645193, by rfl⟩ : syracuseStep 15053849 = 11290387) B11290387
theorem B3348479 : Blo 1321479 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B7633223 : Blo 1321479 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B4234409 : Blo 1321479 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B208927937 : Blo 1321479 208927937 := bstep (se 2 (by rfl) ⟨78347976, by rfl⟩ : syracuseStep 208927937 = 156695953) B156695953
theorem B4464233 : Blo 1321479 4464233 := bstep (se 2 (by rfl) ⟨1674087, by rfl⟩ : syracuseStep 4464233 = 3348175) B3348175
theorem B4022095 : Blo 1321479 4022095 := bstep (se 1 (by rfl) ⟨3016571, by rfl⟩ : syracuseStep 4022095 = 6033143) B6033143
theorem B39182291 : Blo 1321479 39182291 := bstep (se 1 (by rfl) ⟨29386718, by rfl⟩ : syracuseStep 39182291 = 58773437) B58773437
theorem B2973689 : Blo 1321479 2973689 := bstep (se 2 (by rfl) ⟨1115133, by rfl⟩ : syracuseStep 2973689 = 2230267) B2230267
theorem B4464935 : Blo 1321479 4464935 := bstep (se 1 (by rfl) ⟨3348701, by rfl⟩ : syracuseStep 4464935 = 6697403) B6697403
theorem B7528747 : Blo 1321479 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B5652985 : Blo 1321479 5652985 := bstep (se 2 (by rfl) ⟨2119869, by rfl⟩ : syracuseStep 5652985 = 4239739) B4239739
theorem B33907247 : Blo 1321479 33907247 := bstep (se 1 (by rfl) ⟨25430435, by rfl⟩ : syracuseStep 33907247 = 50860871) B50860871
theorem B10035899 : Blo 1321479 10035899 := bstep (se 1 (by rfl) ⟨7526924, by rfl⟩ : syracuseStep 10035899 = 15053849) B15053849
theorem B1983401 : Blo 1321479 1983401 := bstep (se 2 (by rfl) ⟨743775, by rfl⟩ : syracuseStep 1983401 = 1487551) B1487551
theorem B5088815 : Blo 1321479 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B9046013 : Blo 1321479 9046013 := bstep (se 3 (by rfl) ⟨1696127, by rfl⟩ : syracuseStep 9046013 = 3392255) B3392255
theorem B2230409 : Blo 1321479 2230409 := bstep (se 2 (by rfl) ⟨836403, by rfl⟩ : syracuseStep 2230409 = 1672807) B1672807
theorem B1984871 : Blo 1321479 1984871 := bstep (se 1 (by rfl) ⟨1488653, by rfl⟩ : syracuseStep 1984871 = 2977307) B2977307
theorem B2976155 : Blo 1321479 2976155 := bstep (se 1 (by rfl) ⟨2232116, by rfl⟩ : syracuseStep 2976155 = 4464233) B4464233
theorem B1321663 : Blo 1321479 1321663 := bstep (se 1 (by rfl) ⟨991247, by rfl⟩ : syracuseStep 1321663 = 1982495) B1982495
theorem B4238497 : Blo 1321479 4238497 := bstep (se 2 (by rfl) ⟨1589436, by rfl⟩ : syracuseStep 4238497 = 3178873) B3178873
theorem B1322215 : Blo 1321479 1322215 := bstep (se 1 (by rfl) ⟨991661, by rfl⟩ : syracuseStep 1322215 = 1983323) B1983323
theorem B61066507 : Blo 1321479 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B1322495 : Blo 1321479 1322495 := bstep (se 1 (by rfl) ⟨991871, by rfl⟩ : syracuseStep 1322495 = 1983743) B1983743
theorem B10038815 : Blo 1321479 10038815 := bstep (se 1 (by rfl) ⟨7529111, by rfl⟩ : syracuseStep 10038815 = 15058223) B15058223
theorem B3763759 : Blo 1321479 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B20647709 : Blo 1321479 20647709 := bstep (se 3 (by rfl) ⟨3871445, by rfl⟩ : syracuseStep 20647709 = 7742891) B7742891
theorem B1486759 : Blo 1321479 1486759 := bstep (se 1 (by rfl) ⟨1115069, by rfl⟩ : syracuseStep 1486759 = 2230139) B2230139
theorem B2232319 : Blo 1321479 2232319 := bstep (se 1 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 2232319 = 3348479) B3348479
theorem B1323079 : Blo 1321479 1323079 := bstep (se 1 (by rfl) ⟨992309, by rfl⟩ : syracuseStep 1323079 = 1984619) B1984619
theorem B4460669 : Blo 1321479 4460669 := bstep (se 3 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 4460669 = 1672751) B1672751
theorem B146845871 : Blo 1321479 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B1323259 : Blo 1321479 1323259 := bstep (se 1 (by rfl) ⟨992444, by rfl⟩ : syracuseStep 1323259 = 1984889) B1984889
theorem B2822939 : Blo 1321479 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B139285291 : Blo 1321479 139285291 := bstep (se 1 (by rfl) ⟨104463968, by rfl⟩ : syracuseStep 139285291 = 208927937) B208927937
theorem B6353903 : Blo 1321479 6353903 := bstep (se 1 (by rfl) ⟨4765427, by rfl⟩ : syracuseStep 6353903 = 9530855) B9530855
theorem B5362793 : Blo 1321479 5362793 := bstep (se 2 (by rfl) ⟨2011047, by rfl⟩ : syracuseStep 5362793 = 4022095) B4022095
theorem B26121527 : Blo 1321479 26121527 := bstep (se 1 (by rfl) ⟨19591145, by rfl⟩ : syracuseStep 26121527 = 39182291) B39182291
theorem B15276059 : Blo 1321479 15276059 := bstep (se 1 (by rfl) ⟨11457044, by rfl⟩ : syracuseStep 15276059 = 22914089) B22914089
theorem B43490935 : Blo 1321479 43490935 := bstep (se 1 (by rfl) ⟨32618201, by rfl⟩ : syracuseStep 43490935 = 65236403) B65236403
theorem B1982459 : Blo 1321479 1982459 := bstep (se 1 (by rfl) ⟨1486844, by rfl⟩ : syracuseStep 1982459 = 2973689) B2973689
theorem B2973779 : Blo 1321479 2973779 := bstep (se 1 (by rfl) ⟨2230334, by rfl⟩ : syracuseStep 2973779 = 4460669) B4460669
theorem B4235935 : Blo 1321479 4235935 := bstep (se 1 (by rfl) ⟨3176951, by rfl⟩ : syracuseStep 4235935 = 6353903) B6353903
theorem B7537313 : Blo 1321479 7537313 := bstep (se 2 (by rfl) ⟨2826492, by rfl⟩ : syracuseStep 7537313 = 5652985) B5652985
theorem B3392543 : Blo 1321479 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B185713721 : Blo 1321479 185713721 := bstep (se 2 (by rfl) ⟨69642645, by rfl⟩ : syracuseStep 185713721 = 139285291) B139285291
theorem B10184039 : Blo 1321479 10184039 := bstep (se 1 (by rfl) ⟨7638029, by rfl⟩ : syracuseStep 10184039 = 15276059) B15276059
theorem B1984103 : Blo 1321479 1984103 := bstep (se 1 (by rfl) ⟨1488077, by rfl⟩ : syracuseStep 1984103 = 2976155) B2976155
theorem B81422009 : Blo 1321479 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B13765139 : Blo 1321479 13765139 := bstep (se 1 (by rfl) ⟨10323854, by rfl⟩ : syracuseStep 13765139 = 20647709) B20647709
theorem B1321639 : Blo 1321479 1321639 := bstep (se 1 (by rfl) ⟨991229, by rfl⟩ : syracuseStep 1321639 = 1982459) B1982459
theorem B2976425 : Blo 1321479 2976425 := bstep (se 2 (by rfl) ⟨1116159, by rfl⟩ : syracuseStep 2976425 = 2232319) B2232319
theorem B97897247 : Blo 1321479 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B2976623 : Blo 1321479 2976623 := bstep (se 1 (by rfl) ⟨2232467, by rfl⟩ : syracuseStep 2976623 = 4464935) B4464935
theorem B22604831 : Blo 1321479 22604831 := bstep (se 1 (by rfl) ⟨16953623, by rfl⟩ : syracuseStep 22604831 = 33907247) B33907247
theorem B10038329 : Blo 1321479 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B1322267 : Blo 1321479 1322267 := bstep (se 1 (by rfl) ⟨991700, by rfl⟩ : syracuseStep 1322267 = 1983401) B1983401
theorem B3575195 : Blo 1321479 3575195 := bstep (se 1 (by rfl) ⟨2681396, by rfl⟩ : syracuseStep 3575195 = 5362793) B5362793
theorem B1486939 : Blo 1321479 1486939 := bstep (se 1 (by rfl) ⟨1115204, by rfl⟩ : syracuseStep 1486939 = 2230409) B2230409
theorem B1323247 : Blo 1321479 1323247 := bstep (se 1 (by rfl) ⟨992435, by rfl⟩ : syracuseStep 1323247 = 1984871) B1984871
theorem B5018345 : Blo 1321479 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B57987913 : Blo 1321479 57987913 := bstep (se 2 (by rfl) ⟨21745467, by rfl⟩ : syracuseStep 57987913 = 43490935) B43490935
theorem B24122701 : Blo 1321479 24122701 := bstep (se 3 (by rfl) ⟨4523006, by rfl⟩ : syracuseStep 24122701 = 9046013) B9046013
theorem B6690599 : Blo 1321479 6690599 := bstep (se 1 (by rfl) ⟨5017949, by rfl⟩ : syracuseStep 6690599 = 10035899) B10035899
theorem B1881959 : Blo 1321479 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B17414351 : Blo 1321479 17414351 := bstep (se 1 (by rfl) ⟨13060763, by rfl⟩ : syracuseStep 17414351 = 26121527) B26121527
theorem B5651329 : Blo 1321479 5651329 := bstep (se 2 (by rfl) ⟨2119248, by rfl⟩ : syracuseStep 5651329 = 4238497) B4238497
theorem B6692543 : Blo 1321479 6692543 := bstep (se 1 (by rfl) ⟨5019407, by rfl⟩ : syracuseStep 6692543 = 10038815) B10038815
theorem B1982345 : Blo 1321479 1982345 := bstep (se 2 (by rfl) ⟨743379, by rfl⟩ : syracuseStep 1982345 = 1486759) B1486759
theorem B1982519 : Blo 1321479 1982519 := bstep (se 1 (by rfl) ⟨1486889, by rfl⟩ : syracuseStep 1982519 = 2973779) B2973779
theorem B1982585 : Blo 1321479 1982585 := bstep (se 2 (by rfl) ⟨743469, by rfl⟩ : syracuseStep 1982585 = 1486939) B1486939
theorem B77317217 : Blo 1321479 77317217 := bstep (se 2 (by rfl) ⟨28993956, by rfl⟩ : syracuseStep 77317217 = 57987913) B57987913
theorem B54281339 : Blo 1321479 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B11609567 : Blo 1321479 11609567 := bstep (se 1 (by rfl) ⟨8707175, by rfl⟩ : syracuseStep 11609567 = 17414351) B17414351
theorem B9176759 : Blo 1321479 9176759 := bstep (se 1 (by rfl) ⟨6882569, by rfl⟩ : syracuseStep 9176759 = 13765139) B13765139
theorem B32163601 : Blo 1321479 32163601 := bstep (se 2 (by rfl) ⟨12061350, by rfl⟩ : syracuseStep 32163601 = 24122701) B24122701
theorem B1984283 : Blo 1321479 1984283 := bstep (se 1 (by rfl) ⟨1488212, by rfl⟩ : syracuseStep 1984283 = 2976425) B2976425
theorem B1984415 : Blo 1321479 1984415 := bstep (se 1 (by rfl) ⟨1488311, by rfl⟩ : syracuseStep 1984415 = 2976623) B2976623
theorem B1321563 : Blo 1321479 1321563 := bstep (se 1 (by rfl) ⟨991172, by rfl⟩ : syracuseStep 1321563 = 1982345) B1982345
theorem B9046781 : Blo 1321479 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B5024875 : Blo 1321479 5024875 := bstep (se 1 (by rfl) ⟨3768656, by rfl⟩ : syracuseStep 5024875 = 7537313) B7537313
theorem B3345563 : Blo 1321479 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B123809147 : Blo 1321479 123809147 := bstep (se 1 (by rfl) ⟨92856860, by rfl⟩ : syracuseStep 123809147 = 185713721) B185713721
theorem B5647913 : Blo 1321479 5647913 := bstep (se 2 (by rfl) ⟨2117967, by rfl⟩ : syracuseStep 5647913 = 4235935) B4235935
theorem B1322735 : Blo 1321479 1322735 := bstep (se 1 (by rfl) ⟨992051, by rfl⟩ : syracuseStep 1322735 = 1984103) B1984103
theorem B4460399 : Blo 1321479 4460399 := bstep (se 1 (by rfl) ⟨3345299, by rfl⟩ : syracuseStep 4460399 = 6690599) B6690599
theorem B15069887 : Blo 1321479 15069887 := bstep (se 1 (by rfl) ⟨11302415, by rfl⟩ : syracuseStep 15069887 = 22604831) B22604831
theorem B5018557 : Blo 1321479 5018557 := bstep (se 3 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 5018557 = 1881959) B1881959
theorem B4461695 : Blo 1321479 4461695 := bstep (se 1 (by rfl) ⟨3346271, by rfl⟩ : syracuseStep 4461695 = 6692543) B6692543
theorem B6789359 : Blo 1321479 6789359 := bstep (se 1 (by rfl) ⟨5092019, by rfl⟩ : syracuseStep 6789359 = 10184039) B10184039
theorem B7535105 : Blo 1321479 7535105 := bstep (se 2 (by rfl) ⟨2825664, by rfl⟩ : syracuseStep 7535105 = 5651329) B5651329
theorem B65264831 : Blo 1321479 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B6692219 : Blo 1321479 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B2383463 : Blo 1321479 2383463 := bstep (se 1 (by rfl) ⟨1787597, by rfl⟩ : syracuseStep 2383463 = 3575195) B3575195
theorem B18104957 : Blo 1321479 18104957 := bstep (se 3 (by rfl) ⟨3394679, by rfl⟩ : syracuseStep 18104957 = 6789359) B6789359
theorem B51544811 : Blo 1321479 51544811 := bstep (se 1 (by rfl) ⟨38658608, by rfl⟩ : syracuseStep 51544811 = 77317217) B77317217
theorem B2974463 : Blo 1321479 2974463 := bstep (se 1 (by rfl) ⟨2230847, by rfl⟩ : syracuseStep 2974463 = 4461695) B4461695
theorem B5023403 : Blo 1321479 5023403 := bstep (se 1 (by rfl) ⟨3767552, by rfl⟩ : syracuseStep 5023403 = 7535105) B7535105
theorem B6031187 : Blo 1321479 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B2230375 : Blo 1321479 2230375 := bstep (se 1 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 2230375 = 3345563) B3345563
theorem B43509887 : Blo 1321479 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B1321679 : Blo 1321479 1321679 := bstep (se 1 (by rfl) ⟨991259, by rfl⟩ : syracuseStep 1321679 = 1982519) B1982519
theorem B1321723 : Blo 1321479 1321723 := bstep (se 1 (by rfl) ⟨991292, by rfl⟩ : syracuseStep 1321723 = 1982585) B1982585
theorem B10046591 : Blo 1321479 10046591 := bstep (se 1 (by rfl) ⟨7534943, by rfl⟩ : syracuseStep 10046591 = 15069887) B15069887
theorem B36187559 : Blo 1321479 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B1322855 : Blo 1321479 1322855 := bstep (se 1 (by rfl) ⟨992141, by rfl⟩ : syracuseStep 1322855 = 1984283) B1984283
theorem B1322943 : Blo 1321479 1322943 := bstep (se 1 (by rfl) ⟨992207, by rfl⟩ : syracuseStep 1322943 = 1984415) B1984415
theorem B4461479 : Blo 1321479 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B82539431 : Blo 1321479 82539431 := bstep (se 1 (by rfl) ⟨61904573, by rfl⟩ : syracuseStep 82539431 = 123809147) B123809147
theorem B3765275 : Blo 1321479 3765275 := bstep (se 1 (by rfl) ⟨2823956, by rfl⟩ : syracuseStep 3765275 = 5647913) B5647913
theorem B7739711 : Blo 1321479 7739711 := bstep (se 1 (by rfl) ⟨5804783, by rfl⟩ : syracuseStep 7739711 = 11609567) B11609567
theorem B6117839 : Blo 1321479 6117839 := bstep (se 1 (by rfl) ⟨4588379, by rfl⟩ : syracuseStep 6117839 = 9176759) B9176759
theorem B6691409 : Blo 1321479 6691409 := bstep (se 2 (by rfl) ⟨2509278, by rfl⟩ : syracuseStep 6691409 = 5018557) B5018557
theorem B6699833 : Blo 1321479 6699833 := bstep (se 2 (by rfl) ⟨2512437, by rfl⟩ : syracuseStep 6699833 = 5024875) B5024875
theorem B6355901 : Blo 1321479 6355901 := bstep (se 3 (by rfl) ⟨1191731, by rfl⟩ : syracuseStep 6355901 = 2383463) B2383463
theorem B42884801 : Blo 1321479 42884801 := bstep (se 2 (by rfl) ⟨16081800, by rfl⟩ : syracuseStep 42884801 = 32163601) B32163601
theorem B2973599 : Blo 1321479 2973599 := bstep (se 1 (by rfl) ⟨2230199, by rfl⟩ : syracuseStep 2973599 = 4460399) B4460399
theorem B2973833 : Blo 1321479 2973833 := bstep (se 2 (by rfl) ⟨1115187, by rfl⟩ : syracuseStep 2973833 = 2230375) B2230375
theorem B1982975 : Blo 1321479 1982975 := bstep (se 1 (by rfl) ⟨1487231, by rfl⟩ : syracuseStep 1982975 = 2974463) B2974463
theorem B2974319 : Blo 1321479 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B55026287 : Blo 1321479 55026287 := bstep (se 1 (by rfl) ⟨41269715, by rfl⟩ : syracuseStep 55026287 = 82539431) B82539431
theorem B4466555 : Blo 1321479 4466555 := bstep (se 1 (by rfl) ⟨3349916, by rfl⟩ : syracuseStep 4466555 = 6699833) B6699833
theorem B4237267 : Blo 1321479 4237267 := bstep (se 1 (by rfl) ⟨3177950, by rfl⟩ : syracuseStep 4237267 = 6355901) B6355901
theorem B12069971 : Blo 1321479 12069971 := bstep (se 1 (by rfl) ⟨9052478, by rfl⟩ : syracuseStep 12069971 = 18104957) B18104957
theorem B2510183 : Blo 1321479 2510183 := bstep (se 1 (by rfl) ⟨1882637, by rfl⟩ : syracuseStep 2510183 = 3765275) B3765275
theorem B4460939 : Blo 1321479 4460939 := bstep (se 1 (by rfl) ⟨3345704, by rfl⟩ : syracuseStep 4460939 = 6691409) B6691409
theorem B6697727 : Blo 1321479 6697727 := bstep (se 1 (by rfl) ⟨5023295, by rfl⟩ : syracuseStep 6697727 = 10046591) B10046591
theorem B34363207 : Blo 1321479 34363207 := bstep (se 1 (by rfl) ⟨25772405, by rfl⟩ : syracuseStep 34363207 = 51544811) B51544811
theorem B3348935 : Blo 1321479 3348935 := bstep (se 1 (by rfl) ⟨2511701, by rfl⟩ : syracuseStep 3348935 = 5023403) B5023403
theorem B4020791 : Blo 1321479 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B29006591 : Blo 1321479 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B5159807 : Blo 1321479 5159807 := bstep (se 1 (by rfl) ⟨3869855, by rfl⟩ : syracuseStep 5159807 = 7739711) B7739711
theorem B4078559 : Blo 1321479 4078559 := bstep (se 1 (by rfl) ⟨3058919, by rfl⟩ : syracuseStep 4078559 = 6117839) B6117839
theorem B24125039 : Blo 1321479 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B28589867 : Blo 1321479 28589867 := bstep (se 1 (by rfl) ⟨21442400, by rfl⟩ : syracuseStep 28589867 = 42884801) B42884801
theorem B1982399 : Blo 1321479 1982399 := bstep (se 1 (by rfl) ⟨1486799, by rfl⟩ : syracuseStep 1982399 = 2973599) B2973599
theorem B1982555 : Blo 1321479 1982555 := bstep (se 1 (by rfl) ⟨1486916, by rfl⟩ : syracuseStep 1982555 = 2973833) B2973833
theorem B2973959 : Blo 1321479 2973959 := bstep (se 1 (by rfl) ⟨2230469, by rfl⟩ : syracuseStep 2973959 = 4460939) B4460939
theorem B1982879 : Blo 1321479 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B36684191 : Blo 1321479 36684191 := bstep (se 1 (by rfl) ⟨27513143, by rfl⟩ : syracuseStep 36684191 = 55026287) B55026287
theorem B4465151 : Blo 1321479 4465151 := bstep (se 1 (by rfl) ⟨3348863, by rfl⟩ : syracuseStep 4465151 = 6697727) B6697727
theorem B77350909 : Blo 1321479 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B8046647 : Blo 1321479 8046647 := bstep (se 1 (by rfl) ⟨6034985, by rfl⟩ : syracuseStep 8046647 = 12069971) B12069971
theorem B1673455 : Blo 1321479 1673455 := bstep (se 1 (by rfl) ⟨1255091, by rfl⟩ : syracuseStep 1673455 = 2510183) B2510183
theorem B16083359 : Blo 1321479 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B1321599 : Blo 1321479 1321599 := bstep (se 1 (by rfl) ⟨991199, by rfl⟩ : syracuseStep 1321599 = 1982399) B1982399
theorem B1321983 : Blo 1321479 1321983 := bstep (se 1 (by rfl) ⟨991487, by rfl⟩ : syracuseStep 1321983 = 1982975) B1982975
theorem B42888437 : Blo 1321479 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B2977703 : Blo 1321479 2977703 := bstep (se 1 (by rfl) ⟨2233277, by rfl⟩ : syracuseStep 2977703 = 4466555) B4466555
theorem B2232623 : Blo 1321479 2232623 := bstep (se 1 (by rfl) ⟨1674467, by rfl⟩ : syracuseStep 2232623 = 3348935) B3348935
theorem B19059911 : Blo 1321479 19059911 := bstep (se 1 (by rfl) ⟨14294933, by rfl⟩ : syracuseStep 19059911 = 28589867) B28589867
theorem B10876157 : Blo 1321479 10876157 := bstep (se 3 (by rfl) ⟨2039279, by rfl⟩ : syracuseStep 10876157 = 4078559) B4078559
theorem B5649689 : Blo 1321479 5649689 := bstep (se 2 (by rfl) ⟨2118633, by rfl⟩ : syracuseStep 5649689 = 4237267) B4237267
theorem B3439871 : Blo 1321479 3439871 := bstep (se 1 (by rfl) ⟨2579903, by rfl⟩ : syracuseStep 3439871 = 5159807) B5159807
theorem B45817609 : Blo 1321479 45817609 := bstep (se 2 (by rfl) ⟨17181603, by rfl⟩ : syracuseStep 45817609 = 34363207) B34363207
theorem B1982639 : Blo 1321479 1982639 := bstep (se 1 (by rfl) ⟨1486979, by rfl⟩ : syracuseStep 1982639 = 2973959) B2973959
theorem B12706607 : Blo 1321479 12706607 := bstep (se 1 (by rfl) ⟨9529955, by rfl⟩ : syracuseStep 12706607 = 19059911) B19059911
theorem B7250771 : Blo 1321479 7250771 := bstep (se 1 (by rfl) ⟨5438078, by rfl⟩ : syracuseStep 7250771 = 10876157) B10876157
theorem B28592291 : Blo 1321479 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B61090145 : Blo 1321479 61090145 := bstep (se 2 (by rfl) ⟨22908804, by rfl⟩ : syracuseStep 61090145 = 45817609) B45817609
theorem B1985135 : Blo 1321479 1985135 := bstep (se 1 (by rfl) ⟨1488851, by rfl⟩ : syracuseStep 1985135 = 2977703) B2977703
theorem B1321703 : Blo 1321479 1321703 := bstep (se 1 (by rfl) ⟨991277, by rfl⟩ : syracuseStep 1321703 = 1982555) B1982555
theorem B1321919 : Blo 1321479 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B24456127 : Blo 1321479 24456127 := bstep (se 1 (by rfl) ⟨18342095, by rfl⟩ : syracuseStep 24456127 = 36684191) B36684191
theorem B2231273 : Blo 1321479 2231273 := bstep (se 2 (by rfl) ⟨836727, by rfl⟩ : syracuseStep 2231273 = 1673455) B1673455
theorem B2976767 : Blo 1321479 2976767 := bstep (se 1 (by rfl) ⟨2232575, by rfl⟩ : syracuseStep 2976767 = 4465151) B4465151
theorem B103134545 : Blo 1321479 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B1488415 : Blo 1321479 1488415 := bstep (se 1 (by rfl) ⟨1116311, by rfl⟩ : syracuseStep 1488415 = 2232623) B2232623
theorem B3766459 : Blo 1321479 3766459 := bstep (se 1 (by rfl) ⟨2824844, by rfl⟩ : syracuseStep 3766459 = 5649689) B5649689
theorem B5364431 : Blo 1321479 5364431 := bstep (se 1 (by rfl) ⟨4023323, by rfl⟩ : syracuseStep 5364431 = 8046647) B8046647
theorem B10722239 : Blo 1321479 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B2293247 : Blo 1321479 2293247 := bstep (se 1 (by rfl) ⟨1719935, by rfl⟩ : syracuseStep 2293247 = 3439871) B3439871
theorem B5021945 : Blo 1321479 5021945 := bstep (se 2 (by rfl) ⟨1883229, by rfl⟩ : syracuseStep 5021945 = 3766459) B3766459
theorem B8471071 : Blo 1321479 8471071 := bstep (se 1 (by rfl) ⟨6353303, by rfl⟩ : syracuseStep 8471071 = 12706607) B12706607
theorem B4833847 : Blo 1321479 4833847 := bstep (se 1 (by rfl) ⟨3625385, by rfl⟩ : syracuseStep 4833847 = 7250771) B7250771
theorem B68756363 : Blo 1321479 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B1984511 : Blo 1321479 1984511 := bstep (se 1 (by rfl) ⟨1488383, by rfl⟩ : syracuseStep 1984511 = 2976767) B2976767
theorem B1984553 : Blo 1321479 1984553 := bstep (se 2 (by rfl) ⟨744207, by rfl⟩ : syracuseStep 1984553 = 1488415) B1488415
theorem B1321759 : Blo 1321479 1321759 := bstep (se 1 (by rfl) ⟨991319, by rfl⟩ : syracuseStep 1321759 = 1982639) B1982639
theorem B32608169 : Blo 1321479 32608169 := bstep (se 2 (by rfl) ⟨12228063, by rfl⟩ : syracuseStep 32608169 = 24456127) B24456127
theorem B40726763 : Blo 1321479 40726763 := bstep (se 1 (by rfl) ⟨30545072, by rfl⟩ : syracuseStep 40726763 = 61090145) B61090145
theorem B1323423 : Blo 1321479 1323423 := bstep (se 1 (by rfl) ⟨992567, by rfl⟩ : syracuseStep 1323423 = 1985135) B1985135
theorem B3576287 : Blo 1321479 3576287 := bstep (se 1 (by rfl) ⟨2682215, by rfl⟩ : syracuseStep 3576287 = 5364431) B5364431
theorem B7148159 : Blo 1321479 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B1487515 : Blo 1321479 1487515 := bstep (se 1 (by rfl) ⟨1115636, by rfl⟩ : syracuseStep 1487515 = 2231273) B2231273
theorem B1528831 : Blo 1321479 1528831 := bstep (se 1 (by rfl) ⟨1146623, by rfl⟩ : syracuseStep 1528831 = 2293247) B2293247
theorem B19061527 : Blo 1321479 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B2384191 : Blo 1321479 2384191 := bstep (se 1 (by rfl) ⟨1788143, by rfl⟩ : syracuseStep 2384191 = 3576287) B3576287
theorem B1983353 : Blo 1321479 1983353 := bstep (se 2 (by rfl) ⟨743757, by rfl⟩ : syracuseStep 1983353 = 1487515) B1487515
theorem B27151175 : Blo 1321479 27151175 := bstep (se 1 (by rfl) ⟨20363381, by rfl⟩ : syracuseStep 27151175 = 40726763) B40726763
theorem B45837575 : Blo 1321479 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B25415369 : Blo 1321479 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B1323007 : Blo 1321479 1323007 := bstep (se 1 (by rfl) ⟨992255, by rfl⟩ : syracuseStep 1323007 = 1984511) B1984511
theorem B1323035 : Blo 1321479 1323035 := bstep (se 1 (by rfl) ⟨992276, by rfl⟩ : syracuseStep 1323035 = 1984553) B1984553
theorem B21738779 : Blo 1321479 21738779 := bstep (se 1 (by rfl) ⟨16304084, by rfl⟩ : syracuseStep 21738779 = 32608169) B32608169
theorem B3347963 : Blo 1321479 3347963 := bstep (se 1 (by rfl) ⟨2510972, by rfl⟩ : syracuseStep 3347963 = 5021945) B5021945
theorem B4765439 : Blo 1321479 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B11294761 : Blo 1321479 11294761 := bstep (se 2 (by rfl) ⟨4235535, by rfl⟩ : syracuseStep 11294761 = 8471071) B8471071
theorem B6445129 : Blo 1321479 6445129 := bstep (se 2 (by rfl) ⟨2416923, by rfl⟩ : syracuseStep 6445129 = 4833847) B4833847
theorem B2038441 : Blo 1321479 2038441 := bstep (se 2 (by rfl) ⟨764415, by rfl⟩ : syracuseStep 2038441 = 1528831) B1528831
theorem B8593505 : Blo 1321479 8593505 := bstep (se 2 (by rfl) ⟨3222564, by rfl⟩ : syracuseStep 8593505 = 6445129) B6445129
theorem B3178921 : Blo 1321479 3178921 := bstep (se 2 (by rfl) ⟨1192095, by rfl⟩ : syracuseStep 3178921 = 2384191) B2384191
theorem B14492519 : Blo 1321479 14492519 := bstep (se 1 (by rfl) ⟨10869389, by rfl⟩ : syracuseStep 14492519 = 21738779) B21738779
theorem B12707837 : Blo 1321479 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B30558383 : Blo 1321479 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B16943579 : Blo 1321479 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B15059681 : Blo 1321479 15059681 := bstep (se 2 (by rfl) ⟨5647380, by rfl⟩ : syracuseStep 15059681 = 11294761) B11294761
theorem B1322235 : Blo 1321479 1322235 := bstep (se 1 (by rfl) ⟨991676, by rfl⟩ : syracuseStep 1322235 = 1983353) B1983353
theorem B2231975 : Blo 1321479 2231975 := bstep (se 1 (by rfl) ⟨1673981, by rfl⟩ : syracuseStep 2231975 = 3347963) B3347963
theorem B18100783 : Blo 1321479 18100783 := bstep (se 1 (by rfl) ⟨13575587, by rfl⟩ : syracuseStep 18100783 = 27151175) B27151175
theorem B2717921 : Blo 1321479 2717921 := bstep (se 2 (by rfl) ⟨1019220, by rfl⟩ : syracuseStep 2717921 = 2038441) B2038441
theorem B24134377 : Blo 1321479 24134377 := bstep (se 2 (by rfl) ⟨9050391, by rfl⟩ : syracuseStep 24134377 = 18100783) B18100783
theorem B8471891 : Blo 1321479 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B5729003 : Blo 1321479 5729003 := bstep (se 1 (by rfl) ⟨4296752, by rfl⟩ : syracuseStep 5729003 = 8593505) B8593505
theorem B4238561 : Blo 1321479 4238561 := bstep (se 2 (by rfl) ⟨1589460, by rfl⟩ : syracuseStep 4238561 = 3178921) B3178921
theorem B9661679 : Blo 1321479 9661679 := bstep (se 1 (by rfl) ⟨7246259, by rfl⟩ : syracuseStep 9661679 = 14492519) B14492519
theorem B10039787 : Blo 1321479 10039787 := bstep (se 1 (by rfl) ⟨7529840, by rfl⟩ : syracuseStep 10039787 = 15059681) B15059681
theorem B1487983 : Blo 1321479 1487983 := bstep (se 1 (by rfl) ⟨1115987, by rfl⟩ : syracuseStep 1487983 = 2231975) B2231975
theorem B7247789 : Blo 1321479 7247789 := bstep (se 3 (by rfl) ⟨1358960, by rfl⟩ : syracuseStep 7247789 = 2717921) B2717921
theorem B20372255 : Blo 1321479 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B11295719 : Blo 1321479 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B6693191 : Blo 1321479 6693191 := bstep (se 1 (by rfl) ⟨5019893, by rfl⟩ : syracuseStep 6693191 = 10039787) B10039787
theorem B32179169 : Blo 1321479 32179169 := bstep (se 2 (by rfl) ⟨12067188, by rfl⟩ : syracuseStep 32179169 = 24134377) B24134377
theorem B1983977 : Blo 1321479 1983977 := bstep (se 2 (by rfl) ⟨743991, by rfl⟩ : syracuseStep 1983977 = 1487983) B1487983
theorem B3819335 : Blo 1321479 3819335 := bstep (se 1 (by rfl) ⟨2864501, by rfl⟩ : syracuseStep 3819335 = 5729003) B5729003
theorem B7530479 : Blo 1321479 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B6441119 : Blo 1321479 6441119 := bstep (se 1 (by rfl) ⟨4830839, by rfl⟩ : syracuseStep 6441119 = 9661679) B9661679
theorem B22591709 : Blo 1321479 22591709 := bstep (se 3 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 22591709 = 8471891) B8471891
theorem B4831859 : Blo 1321479 4831859 := bstep (se 1 (by rfl) ⟨3623894, by rfl⟩ : syracuseStep 4831859 = 7247789) B7247789
theorem B13581503 : Blo 1321479 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B2825707 : Blo 1321479 2825707 := bstep (se 1 (by rfl) ⟨2119280, by rfl⟩ : syracuseStep 2825707 = 4238561) B4238561
theorem B40739573 : Blo 1321479 40739573 := bstep (se 5 (by rfl) ⟨1909667, by rfl⟩ : syracuseStep 40739573 = 3819335) B3819335
theorem B4294079 : Blo 1321479 4294079 := bstep (se 1 (by rfl) ⟨3220559, by rfl⟩ : syracuseStep 4294079 = 6441119) B6441119
theorem B9054335 : Blo 1321479 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B1322651 : Blo 1321479 1322651 := bstep (se 1 (by rfl) ⟨991988, by rfl⟩ : syracuseStep 1322651 = 1983977) B1983977
theorem B15061139 : Blo 1321479 15061139 := bstep (se 1 (by rfl) ⟨11295854, by rfl⟩ : syracuseStep 15061139 = 22591709) B22591709
theorem B4462127 : Blo 1321479 4462127 := bstep (se 1 (by rfl) ⟨3346595, by rfl⟩ : syracuseStep 4462127 = 6693191) B6693191
theorem B21452779 : Blo 1321479 21452779 := bstep (se 1 (by rfl) ⟨16089584, by rfl⟩ : syracuseStep 21452779 = 32179169) B32179169
theorem B5020319 : Blo 1321479 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B12884957 : Blo 1321479 12884957 := bstep (se 3 (by rfl) ⟨2415929, by rfl⟩ : syracuseStep 12884957 = 4831859) B4831859
theorem B3767609 : Blo 1321479 3767609 := bstep (se 2 (by rfl) ⟨1412853, by rfl⟩ : syracuseStep 3767609 = 2825707) B2825707
theorem B2974751 : Blo 1321479 2974751 := bstep (se 1 (by rfl) ⟨2231063, by rfl⟩ : syracuseStep 2974751 = 4462127) B4462127
theorem B27159715 : Blo 1321479 27159715 := bstep (se 1 (by rfl) ⟨20369786, by rfl⟩ : syracuseStep 27159715 = 40739573) B40739573
theorem B2862719 : Blo 1321479 2862719 := bstep (se 1 (by rfl) ⟨2147039, by rfl⟩ : syracuseStep 2862719 = 4294079) B4294079
theorem B3346879 : Blo 1321479 3346879 := bstep (se 1 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 3346879 = 5020319) B5020319
theorem B8589971 : Blo 1321479 8589971 := bstep (se 1 (by rfl) ⟨6442478, by rfl⟩ : syracuseStep 8589971 = 12884957) B12884957
theorem B2511739 : Blo 1321479 2511739 := bstep (se 1 (by rfl) ⟨1883804, by rfl⟩ : syracuseStep 2511739 = 3767609) B3767609
theorem B28603705 : Blo 1321479 28603705 := bstep (se 2 (by rfl) ⟨10726389, by rfl⟩ : syracuseStep 28603705 = 21452779) B21452779
theorem B10040759 : Blo 1321479 10040759 := bstep (se 1 (by rfl) ⟨7530569, by rfl⟩ : syracuseStep 10040759 = 15061139) B15061139
theorem B6036223 : Blo 1321479 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B5726647 : Blo 1321479 5726647 := bstep (se 1 (by rfl) ⟨4294985, by rfl⟩ : syracuseStep 5726647 = 8589971) B8589971
theorem B1983167 : Blo 1321479 1983167 := bstep (se 1 (by rfl) ⟨1487375, by rfl⟩ : syracuseStep 1983167 = 2974751) B2974751
theorem B144851813 : Blo 1321479 144851813 := bstep (se 4 (by rfl) ⟨13579857, by rfl⟩ : syracuseStep 144851813 = 27159715) B27159715
theorem B6693839 : Blo 1321479 6693839 := bstep (se 1 (by rfl) ⟨5020379, by rfl⟩ : syracuseStep 6693839 = 10040759) B10040759
theorem B8048297 : Blo 1321479 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B38138273 : Blo 1321479 38138273 := bstep (se 2 (by rfl) ⟨14301852, by rfl⟩ : syracuseStep 38138273 = 28603705) B28603705
theorem B4462505 : Blo 1321479 4462505 := bstep (se 2 (by rfl) ⟨1673439, by rfl⟩ : syracuseStep 4462505 = 3346879) B3346879
theorem B3348985 : Blo 1321479 3348985 := bstep (se 2 (by rfl) ⟨1255869, by rfl⟩ : syracuseStep 3348985 = 2511739) B2511739
theorem B1908479 : Blo 1321479 1908479 := bstep (se 1 (by rfl) ⟨1431359, by rfl⟩ : syracuseStep 1908479 = 2862719) B2862719
theorem B96567875 : Blo 1321479 96567875 := bstep (se 1 (by rfl) ⟨72425906, by rfl⟩ : syracuseStep 96567875 = 144851813) B144851813
theorem B7635529 : Blo 1321479 7635529 := bstep (se 2 (by rfl) ⟨2863323, by rfl⟩ : syracuseStep 7635529 = 5726647) B5726647
theorem B4465313 : Blo 1321479 4465313 := bstep (se 2 (by rfl) ⟨1674492, by rfl⟩ : syracuseStep 4465313 = 3348985) B3348985
theorem B2975003 : Blo 1321479 2975003 := bstep (se 1 (by rfl) ⟨2231252, by rfl⟩ : syracuseStep 2975003 = 4462505) B4462505
theorem B5089277 : Blo 1321479 5089277 := bstep (se 3 (by rfl) ⟨954239, by rfl⟩ : syracuseStep 5089277 = 1908479) B1908479
theorem B1322111 : Blo 1321479 1322111 := bstep (se 1 (by rfl) ⟨991583, by rfl⟩ : syracuseStep 1322111 = 1983167) B1983167
theorem B25425515 : Blo 1321479 25425515 := bstep (se 1 (by rfl) ⟨19069136, by rfl⟩ : syracuseStep 25425515 = 38138273) B38138273
theorem B4462559 : Blo 1321479 4462559 := bstep (se 1 (by rfl) ⟨3346919, by rfl⟩ : syracuseStep 4462559 = 6693839) B6693839
theorem B5365531 : Blo 1321479 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B40722821 : Blo 1321479 40722821 := bstep (se 4 (by rfl) ⟨3817764, by rfl⟩ : syracuseStep 40722821 = 7635529) B7635529
theorem B1983335 : Blo 1321479 1983335 := bstep (se 1 (by rfl) ⟨1487501, by rfl⟩ : syracuseStep 1983335 = 2975003) B2975003
theorem B16950343 : Blo 1321479 16950343 := bstep (se 1 (by rfl) ⟨12712757, by rfl⟩ : syracuseStep 16950343 = 25425515) B25425515
theorem B2975039 : Blo 1321479 2975039 := bstep (se 1 (by rfl) ⟨2231279, by rfl⟩ : syracuseStep 2975039 = 4462559) B4462559
theorem B3392851 : Blo 1321479 3392851 := bstep (se 1 (by rfl) ⟨2544638, by rfl⟩ : syracuseStep 3392851 = 5089277) B5089277
theorem B28616165 : Blo 1321479 28616165 := bstep (se 4 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 28616165 = 5365531) B5365531
theorem B2976875 : Blo 1321479 2976875 := bstep (se 1 (by rfl) ⟨2232656, by rfl⟩ : syracuseStep 2976875 = 4465313) B4465313
theorem B64378583 : Blo 1321479 64378583 := bstep (se 1 (by rfl) ⟨48283937, by rfl⟩ : syracuseStep 64378583 = 96567875) B96567875
theorem B27148547 : Blo 1321479 27148547 := bstep (se 1 (by rfl) ⟨20361410, by rfl⟩ : syracuseStep 27148547 = 40722821) B40722821
theorem B1983359 : Blo 1321479 1983359 := bstep (se 1 (by rfl) ⟨1487519, by rfl⟩ : syracuseStep 1983359 = 2975039) B2975039
theorem B42919055 : Blo 1321479 42919055 := bstep (se 1 (by rfl) ⟨32189291, by rfl⟩ : syracuseStep 42919055 = 64378583) B64378583
theorem B4523801 : Blo 1321479 4523801 := bstep (se 2 (by rfl) ⟨1696425, by rfl⟩ : syracuseStep 4523801 = 3392851) B3392851
theorem B1984583 : Blo 1321479 1984583 := bstep (se 1 (by rfl) ⟨1488437, by rfl⟩ : syracuseStep 1984583 = 2976875) B2976875
theorem B1322223 : Blo 1321479 1322223 := bstep (se 1 (by rfl) ⟨991667, by rfl⟩ : syracuseStep 1322223 = 1983335) B1983335
theorem B19077443 : Blo 1321479 19077443 := bstep (se 1 (by rfl) ⟨14308082, by rfl⟩ : syracuseStep 19077443 = 28616165) B28616165
theorem B22600457 : Blo 1321479 22600457 := bstep (se 2 (by rfl) ⟨8475171, by rfl⟩ : syracuseStep 22600457 = 16950343) B16950343
theorem B15066971 : Blo 1321479 15066971 := bstep (se 1 (by rfl) ⟨11300228, by rfl⟩ : syracuseStep 15066971 = 22600457) B22600457
theorem B48253877 : Blo 1321479 48253877 := bstep (se 5 (by rfl) ⟨2261900, by rfl⟩ : syracuseStep 48253877 = 4523801) B4523801
theorem B1322239 : Blo 1321479 1322239 := bstep (se 1 (by rfl) ⟨991679, by rfl⟩ : syracuseStep 1322239 = 1983359) B1983359
theorem B72396125 : Blo 1321479 72396125 := bstep (se 3 (by rfl) ⟨13574273, by rfl⟩ : syracuseStep 72396125 = 27148547) B27148547
theorem B1323055 : Blo 1321479 1323055 := bstep (se 1 (by rfl) ⟨992291, by rfl⟩ : syracuseStep 1323055 = 1984583) B1984583
theorem B12718295 : Blo 1321479 12718295 := bstep (se 1 (by rfl) ⟨9538721, by rfl⟩ : syracuseStep 12718295 = 19077443) B19077443
theorem B28612703 : Blo 1321479 28612703 := bstep (se 1 (by rfl) ⟨21459527, by rfl⟩ : syracuseStep 28612703 = 42919055) B42919055
theorem B8478863 : Blo 1321479 8478863 := bstep (se 1 (by rfl) ⟨6359147, by rfl⟩ : syracuseStep 8478863 = 12718295) B12718295
theorem B10044647 : Blo 1321479 10044647 := bstep (se 1 (by rfl) ⟨7533485, by rfl⟩ : syracuseStep 10044647 = 15066971) B15066971
theorem B19075135 : Blo 1321479 19075135 := bstep (se 1 (by rfl) ⟨14306351, by rfl⟩ : syracuseStep 19075135 = 28612703) B28612703
theorem B48264083 : Blo 1321479 48264083 := bstep (se 1 (by rfl) ⟨36198062, by rfl⟩ : syracuseStep 48264083 = 72396125) B72396125
theorem B32169251 : Blo 1321479 32169251 := bstep (se 1 (by rfl) ⟨24126938, by rfl⟩ : syracuseStep 32169251 = 48253877) B48253877
theorem B5652575 : Blo 1321479 5652575 := bstep (se 1 (by rfl) ⟨4239431, by rfl⟩ : syracuseStep 5652575 = 8478863) B8478863
theorem B6696431 : Blo 1321479 6696431 := bstep (se 1 (by rfl) ⟨5022323, by rfl⟩ : syracuseStep 6696431 = 10044647) B10044647
theorem B25433513 : Blo 1321479 25433513 := bstep (se 2 (by rfl) ⟨9537567, by rfl⟩ : syracuseStep 25433513 = 19075135) B19075135
theorem B32176055 : Blo 1321479 32176055 := bstep (se 1 (by rfl) ⟨24132041, by rfl⟩ : syracuseStep 32176055 = 48264083) B48264083
theorem B21446167 : Blo 1321479 21446167 := bstep (se 1 (by rfl) ⟨16084625, by rfl⟩ : syracuseStep 21446167 = 32169251) B32169251
theorem B3768383 : Blo 1321479 3768383 := bstep (se 1 (by rfl) ⟨2826287, by rfl⟩ : syracuseStep 3768383 = 5652575) B5652575
theorem B28594889 : Blo 1321479 28594889 := bstep (se 2 (by rfl) ⟨10723083, by rfl⟩ : syracuseStep 28594889 = 21446167) B21446167
theorem B16955675 : Blo 1321479 16955675 := bstep (se 1 (by rfl) ⟨12716756, by rfl⟩ : syracuseStep 16955675 = 25433513) B25433513
theorem B4464287 : Blo 1321479 4464287 := bstep (se 1 (by rfl) ⟨3348215, by rfl⟩ : syracuseStep 4464287 = 6696431) B6696431
theorem B85802813 : Blo 1321479 85802813 := bstep (se 3 (by rfl) ⟨16088027, by rfl⟩ : syracuseStep 85802813 = 32176055) B32176055
theorem B19063259 : Blo 1321479 19063259 := bstep (se 1 (by rfl) ⟨14297444, by rfl⟩ : syracuseStep 19063259 = 28594889) B28594889
theorem B2976191 : Blo 1321479 2976191 := bstep (se 1 (by rfl) ⟨2232143, by rfl⟩ : syracuseStep 2976191 = 4464287) B4464287
theorem B57201875 : Blo 1321479 57201875 := bstep (se 1 (by rfl) ⟨42901406, by rfl⟩ : syracuseStep 57201875 = 85802813) B85802813
theorem B10049021 : Blo 1321479 10049021 := bstep (se 3 (by rfl) ⟨1884191, by rfl⟩ : syracuseStep 10049021 = 3768383) B3768383
theorem B11303783 : Blo 1321479 11303783 := bstep (se 1 (by rfl) ⟨8477837, by rfl⟩ : syracuseStep 11303783 = 16955675) B16955675
theorem B38134583 : Blo 1321479 38134583 := bstep (se 1 (by rfl) ⟨28600937, by rfl⟩ : syracuseStep 38134583 = 57201875) B57201875
theorem B1984127 : Blo 1321479 1984127 := bstep (se 1 (by rfl) ⟨1488095, by rfl⟩ : syracuseStep 1984127 = 2976191) B2976191
theorem B12708839 : Blo 1321479 12708839 := bstep (se 1 (by rfl) ⟨9531629, by rfl⟩ : syracuseStep 12708839 = 19063259) B19063259
theorem B6699347 : Blo 1321479 6699347 := bstep (se 1 (by rfl) ⟨5024510, by rfl⟩ : syracuseStep 6699347 = 10049021) B10049021
theorem B7535855 : Blo 1321479 7535855 := bstep (se 1 (by rfl) ⟨5651891, by rfl⟩ : syracuseStep 7535855 = 11303783) B11303783
theorem B4466231 : Blo 1321479 4466231 := bstep (se 1 (by rfl) ⟨3349673, by rfl⟩ : syracuseStep 4466231 = 6699347) B6699347
theorem B8472559 : Blo 1321479 8472559 := bstep (se 1 (by rfl) ⟨6354419, by rfl⟩ : syracuseStep 8472559 = 12708839) B12708839
theorem B5023903 : Blo 1321479 5023903 := bstep (se 1 (by rfl) ⟨3767927, by rfl⟩ : syracuseStep 5023903 = 7535855) B7535855
theorem B25423055 : Blo 1321479 25423055 := bstep (se 1 (by rfl) ⟨19067291, by rfl⟩ : syracuseStep 25423055 = 38134583) B38134583
theorem B1322751 : Blo 1321479 1322751 := bstep (se 1 (by rfl) ⟨992063, by rfl⟩ : syracuseStep 1322751 = 1984127) B1984127
theorem B2977487 : Blo 1321479 2977487 := bstep (se 1 (by rfl) ⟨2233115, by rfl⟩ : syracuseStep 2977487 = 4466231) B4466231
theorem B6698537 : Blo 1321479 6698537 := bstep (se 2 (by rfl) ⟨2511951, by rfl⟩ : syracuseStep 6698537 = 5023903) B5023903
theorem B16948703 : Blo 1321479 16948703 := bstep (se 1 (by rfl) ⟨12711527, by rfl⟩ : syracuseStep 16948703 = 25423055) B25423055
theorem B11296745 : Blo 1321479 11296745 := bstep (se 2 (by rfl) ⟨4236279, by rfl⟩ : syracuseStep 11296745 = 8472559) B8472559
theorem B4465691 : Blo 1321479 4465691 := bstep (se 1 (by rfl) ⟨3349268, by rfl⟩ : syracuseStep 4465691 = 6698537) B6698537
theorem B11299135 : Blo 1321479 11299135 := bstep (se 1 (by rfl) ⟨8474351, by rfl⟩ : syracuseStep 11299135 = 16948703) B16948703
theorem B1984991 : Blo 1321479 1984991 := bstep (se 1 (by rfl) ⟨1488743, by rfl⟩ : syracuseStep 1984991 = 2977487) B2977487
theorem B7531163 : Blo 1321479 7531163 := bstep (se 1 (by rfl) ⟨5648372, by rfl⟩ : syracuseStep 7531163 = 11296745) B11296745
theorem B15065513 : Blo 1321479 15065513 := bstep (se 2 (by rfl) ⟨5649567, by rfl⟩ : syracuseStep 15065513 = 11299135) B11299135
theorem B2977127 : Blo 1321479 2977127 := bstep (se 1 (by rfl) ⟨2232845, by rfl⟩ : syracuseStep 2977127 = 4465691) B4465691
theorem B1323327 : Blo 1321479 1323327 := bstep (se 1 (by rfl) ⟨992495, by rfl⟩ : syracuseStep 1323327 = 1984991) B1984991
theorem B5020775 : Blo 1321479 5020775 := bstep (se 1 (by rfl) ⟨3765581, by rfl⟩ : syracuseStep 5020775 = 7531163) B7531163
theorem B10043675 : Blo 1321479 10043675 := bstep (se 1 (by rfl) ⟨7532756, by rfl⟩ : syracuseStep 10043675 = 15065513) B15065513
theorem B1984751 : Blo 1321479 1984751 := bstep (se 1 (by rfl) ⟨1488563, by rfl⟩ : syracuseStep 1984751 = 2977127) B2977127
theorem B3347183 : Blo 1321479 3347183 := bstep (se 1 (by rfl) ⟨2510387, by rfl⟩ : syracuseStep 3347183 = 5020775) B5020775
theorem B6695783 : Blo 1321479 6695783 := bstep (se 1 (by rfl) ⟨5021837, by rfl⟩ : syracuseStep 6695783 = 10043675) B10043675
theorem B2231455 : Blo 1321479 2231455 := bstep (se 1 (by rfl) ⟨1673591, by rfl⟩ : syracuseStep 2231455 = 3347183) B3347183
theorem B1323167 : Blo 1321479 1323167 := bstep (se 1 (by rfl) ⟨992375, by rfl⟩ : syracuseStep 1323167 = 1984751) B1984751
theorem B2975273 : Blo 1321479 2975273 := bstep (se 2 (by rfl) ⟨1115727, by rfl⟩ : syracuseStep 2975273 = 2231455) B2231455
theorem B4463855 : Blo 1321479 4463855 := bstep (se 1 (by rfl) ⟨3347891, by rfl⟩ : syracuseStep 4463855 = 6695783) B6695783
theorem B1983515 : Blo 1321479 1983515 := bstep (se 1 (by rfl) ⟨1487636, by rfl⟩ : syracuseStep 1983515 = 2975273) B2975273
theorem B2975903 : Blo 1321479 2975903 := bstep (se 1 (by rfl) ⟨2231927, by rfl⟩ : syracuseStep 2975903 = 4463855) B4463855
theorem B1983935 : Blo 1321479 1983935 := bstep (se 1 (by rfl) ⟨1487951, by rfl⟩ : syracuseStep 1983935 = 2975903) B2975903
theorem B1322343 : Blo 1321479 1322343 := bstep (se 1 (by rfl) ⟨991757, by rfl⟩ : syracuseStep 1322343 = 1983515) B1983515
theorem B1322623 : Blo 1321479 1322623 := bstep (se 1 (by rfl) ⟨991967, by rfl⟩ : syracuseStep 1322623 = 1983935) B1983935

theorem C0 (j : ℕ) (h1 : 330369 ≤ j) (h2 : j ≤ 330869) : Blo 1321479 (4 * j + 3) := by
  interval_cases j
  · exact B1321479
  · exact B1321483
  · exact B1321487
  · exact B1321491
  · exact B1321495
  · exact B1321499
  · exact B1321503
  · exact B1321507
  · exact B1321511
  · exact B1321515
  · exact B1321519
  · exact B1321523
  · exact B1321527
  · exact B1321531
  · exact B1321535
  · exact B1321539
  · exact B1321543
  · exact B1321547
  · exact B1321551
  · exact B1321555
  · exact B1321559
  · exact B1321563
  · exact B1321567
  · exact B1321571
  · exact B1321575
  · exact B1321579
  · exact B1321583
  · exact B1321587
  · exact B1321591
  · exact B1321595
  · exact B1321599
  · exact B1321603
  · exact B1321607
  · exact B1321611
  · exact B1321615
  · exact B1321619
  · exact B1321623
  · exact B1321627
  · exact B1321631
  · exact B1321635
  · exact B1321639
  · exact B1321643
  · exact B1321647
  · exact B1321651
  · exact B1321655
  · exact B1321659
  · exact B1321663
  · exact B1321667
  · exact B1321671
  · exact B1321675
  · exact B1321679
  · exact B1321683
  · exact B1321687
  · exact B1321691
  · exact B1321695
  · exact B1321699
  · exact B1321703
  · exact B1321707
  · exact B1321711
  · exact B1321715
  · exact B1321719
  · exact B1321723
  · exact B1321727
  · exact B1321731
  · exact B1321735
  · exact B1321739
  · exact B1321743
  · exact B1321747
  · exact B1321751
  · exact B1321755
  · exact B1321759
  · exact B1321763
  · exact B1321767
  · exact B1321771
  · exact B1321775
  · exact B1321779
  · exact B1321783
  · exact B1321787
  · exact B1321791
  · exact B1321795
  · exact B1321799
  · exact B1321803
  · exact B1321807
  · exact B1321811
  · exact B1321815
  · exact B1321819
  · exact B1321823
  · exact B1321827
  · exact B1321831
  · exact B1321835
  · exact B1321839
  · exact B1321843
  · exact B1321847
  · exact B1321851
  · exact B1321855
  · exact B1321859
  · exact B1321863
  · exact B1321867
  · exact B1321871
  · exact B1321875
  · exact B1321879
  · exact B1321883
  · exact B1321887
  · exact B1321891
  · exact B1321895
  · exact B1321899
  · exact B1321903
  · exact B1321907
  · exact B1321911
  · exact B1321915
  · exact B1321919
  · exact B1321923
  · exact B1321927
  · exact B1321931
  · exact B1321935
  · exact B1321939
  · exact B1321943
  · exact B1321947
  · exact B1321951
  · exact B1321955
  · exact B1321959
  · exact B1321963
  · exact B1321967
  · exact B1321971
  · exact B1321975
  · exact B1321979
  · exact B1321983
  · exact B1321987
  · exact B1321991
  · exact B1321995
  · exact B1321999
  · exact B1322003
  · exact B1322007
  · exact B1322011
  · exact B1322015
  · exact B1322019
  · exact B1322023
  · exact B1322027
  · exact B1322031
  · exact B1322035
  · exact B1322039
  · exact B1322043
  · exact B1322047
  · exact B1322051
  · exact B1322055
  · exact B1322059
  · exact B1322063
  · exact B1322067
  · exact B1322071
  · exact B1322075
  · exact B1322079
  · exact B1322083
  · exact B1322087
  · exact B1322091
  · exact B1322095
  · exact B1322099
  · exact B1322103
  · exact B1322107
  · exact B1322111
  · exact B1322115
  · exact B1322119
  · exact B1322123
  · exact B1322127
  · exact B1322131
  · exact B1322135
  · exact B1322139
  · exact B1322143
  · exact B1322147
  · exact B1322151
  · exact B1322155
  · exact B1322159
  · exact B1322163
  · exact B1322167
  · exact B1322171
  · exact B1322175
  · exact B1322179
  · exact B1322183
  · exact B1322187
  · exact B1322191
  · exact B1322195
  · exact B1322199
  · exact B1322203
  · exact B1322207
  · exact B1322211
  · exact B1322215
  · exact B1322219
  · exact B1322223
  · exact B1322227
  · exact B1322231
  · exact B1322235
  · exact B1322239
  · exact B1322243
  · exact B1322247
  · exact B1322251
  · exact B1322255
  · exact B1322259
  · exact B1322263
  · exact B1322267
  · exact B1322271
  · exact B1322275
  · exact B1322279
  · exact B1322283
  · exact B1322287
  · exact B1322291
  · exact B1322295
  · exact B1322299
  · exact B1322303
  · exact B1322307
  · exact B1322311
  · exact B1322315
  · exact B1322319
  · exact B1322323
  · exact B1322327
  · exact B1322331
  · exact B1322335
  · exact B1322339
  · exact B1322343
  · exact B1322347
  · exact B1322351
  · exact B1322355
  · exact B1322359
  · exact B1322363
  · exact B1322367
  · exact B1322371
  · exact B1322375
  · exact B1322379
  · exact B1322383
  · exact B1322387
  · exact B1322391
  · exact B1322395
  · exact B1322399
  · exact B1322403
  · exact B1322407
  · exact B1322411
  · exact B1322415
  · exact B1322419
  · exact B1322423
  · exact B1322427
  · exact B1322431
  · exact B1322435
  · exact B1322439
  · exact B1322443
  · exact B1322447
  · exact B1322451
  · exact B1322455
  · exact B1322459
  · exact B1322463
  · exact B1322467
  · exact B1322471
  · exact B1322475
  · exact B1322479
  · exact B1322483
  · exact B1322487
  · exact B1322491
  · exact B1322495
  · exact B1322499
  · exact B1322503
  · exact B1322507
  · exact B1322511
  · exact B1322515
  · exact B1322519
  · exact B1322523
  · exact B1322527
  · exact B1322531
  · exact B1322535
  · exact B1322539
  · exact B1322543
  · exact B1322547
  · exact B1322551
  · exact B1322555
  · exact B1322559
  · exact B1322563
  · exact B1322567
  · exact B1322571
  · exact B1322575
  · exact B1322579
  · exact B1322583
  · exact B1322587
  · exact B1322591
  · exact B1322595
  · exact B1322599
  · exact B1322603
  · exact B1322607
  · exact B1322611
  · exact B1322615
  · exact B1322619
  · exact B1322623
  · exact B1322627
  · exact B1322631
  · exact B1322635
  · exact B1322639
  · exact B1322643
  · exact B1322647
  · exact B1322651
  · exact B1322655
  · exact B1322659
  · exact B1322663
  · exact B1322667
  · exact B1322671
  · exact B1322675
  · exact B1322679
  · exact B1322683
  · exact B1322687
  · exact B1322691
  · exact B1322695
  · exact B1322699
  · exact B1322703
  · exact B1322707
  · exact B1322711
  · exact B1322715
  · exact B1322719
  · exact B1322723
  · exact B1322727
  · exact B1322731
  · exact B1322735
  · exact B1322739
  · exact B1322743
  · exact B1322747
  · exact B1322751
  · exact B1322755
  · exact B1322759
  · exact B1322763
  · exact B1322767
  · exact B1322771
  · exact B1322775
  · exact B1322779
  · exact B1322783
  · exact B1322787
  · exact B1322791
  · exact B1322795
  · exact B1322799
  · exact B1322803
  · exact B1322807
  · exact B1322811
  · exact B1322815
  · exact B1322819
  · exact B1322823
  · exact B1322827
  · exact B1322831
  · exact B1322835
  · exact B1322839
  · exact B1322843
  · exact B1322847
  · exact B1322851
  · exact B1322855
  · exact B1322859
  · exact B1322863
  · exact B1322867
  · exact B1322871
  · exact B1322875
  · exact B1322879
  · exact B1322883
  · exact B1322887
  · exact B1322891
  · exact B1322895
  · exact B1322899
  · exact B1322903
  · exact B1322907
  · exact B1322911
  · exact B1322915
  · exact B1322919
  · exact B1322923
  · exact B1322927
  · exact B1322931
  · exact B1322935
  · exact B1322939
  · exact B1322943
  · exact B1322947
  · exact B1322951
  · exact B1322955
  · exact B1322959
  · exact B1322963
  · exact B1322967
  · exact B1322971
  · exact B1322975
  · exact B1322979
  · exact B1322983
  · exact B1322987
  · exact B1322991
  · exact B1322995
  · exact B1322999
  · exact B1323003
  · exact B1323007
  · exact B1323011
  · exact B1323015
  · exact B1323019
  · exact B1323023
  · exact B1323027
  · exact B1323031
  · exact B1323035
  · exact B1323039
  · exact B1323043
  · exact B1323047
  · exact B1323051
  · exact B1323055
  · exact B1323059
  · exact B1323063
  · exact B1323067
  · exact B1323071
  · exact B1323075
  · exact B1323079
  · exact B1323083
  · exact B1323087
  · exact B1323091
  · exact B1323095
  · exact B1323099
  · exact B1323103
  · exact B1323107
  · exact B1323111
  · exact B1323115
  · exact B1323119
  · exact B1323123
  · exact B1323127
  · exact B1323131
  · exact B1323135
  · exact B1323139
  · exact B1323143
  · exact B1323147
  · exact B1323151
  · exact B1323155
  · exact B1323159
  · exact B1323163
  · exact B1323167
  · exact B1323171
  · exact B1323175
  · exact B1323179
  · exact B1323183
  · exact B1323187
  · exact B1323191
  · exact B1323195
  · exact B1323199
  · exact B1323203
  · exact B1323207
  · exact B1323211
  · exact B1323215
  · exact B1323219
  · exact B1323223
  · exact B1323227
  · exact B1323231
  · exact B1323235
  · exact B1323239
  · exact B1323243
  · exact B1323247
  · exact B1323251
  · exact B1323255
  · exact B1323259
  · exact B1323263
  · exact B1323267
  · exact B1323271
  · exact B1323275
  · exact B1323279
  · exact B1323283
  · exact B1323287
  · exact B1323291
  · exact B1323295
  · exact B1323299
  · exact B1323303
  · exact B1323307
  · exact B1323311
  · exact B1323315
  · exact B1323319
  · exact B1323323
  · exact B1323327
  · exact B1323331
  · exact B1323335
  · exact B1323339
  · exact B1323343
  · exact B1323347
  · exact B1323351
  · exact B1323355
  · exact B1323359
  · exact B1323363
  · exact B1323367
  · exact B1323371
  · exact B1323375
  · exact B1323379
  · exact B1323383
  · exact B1323387
  · exact B1323391
  · exact B1323395
  · exact B1323399
  · exact B1323403
  · exact B1323407
  · exact B1323411
  · exact B1323415
  · exact B1323419
  · exact B1323423
  · exact B1323427
  · exact B1323431
  · exact B1323435
  · exact B1323439
  · exact B1323443
  · exact B1323447
  · exact B1323451
  · exact B1323455
  · exact B1323459
  · exact B1323463
  · exact B1323467
  · exact B1323471
  · exact B1323475
  · exact B1323479

theorem solution (m : ℕ) (hlo : 1321479 ≤ m) (hhi : m ≤ 1323479) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 330369 ≤ j := by omega
    have hj2 : j ≤ 330869 := by omega
    have hb : Blo 1321479 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
