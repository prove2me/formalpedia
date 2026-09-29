-- Prove2me | solution 1 for syracuse_descends_range_247818_251818
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:02.839446+00:00
-- url     : https://prove2.me/submissions/3ed0d02f-d3a9-4b0c-846a-16d14320abba

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


theorem B1605653 : Blo 247818 1605653 := bbase (se 6 (by rfl) ⟨37632, by rfl⟩ : syracuseStep 1605653 = 75265) (by norm_num)
theorem B852133 : Blo 247818 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B4882837 : Blo 247818 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B1147429 : Blo 247818 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B557621 : Blo 247818 557621 := bbase (se 5 (by rfl) ⟨26138, by rfl⟩ : syracuseStep 557621 = 52277) (by norm_num)
theorem B557693 : Blo 247818 557693 := bbase (se 3 (by rfl) ⟨104567, by rfl⟩ : syracuseStep 557693 = 209135) (by norm_num)
theorem B557765 : Blo 247818 557765 := bbase (se 4 (by rfl) ⟨52290, by rfl⟩ : syracuseStep 557765 = 104581) (by norm_num)
theorem B557837 : Blo 247818 557837 := bbase (se 3 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 557837 = 209189) (by norm_num)
theorem B1016597 : Blo 247818 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B557909 : Blo 247818 557909 := bbase (se 9 (by rfl) ⟨1634, by rfl⟩ : syracuseStep 557909 = 3269) (by norm_num)
theorem B557981 : Blo 247818 557981 := bbase (se 3 (by rfl) ⟨104621, by rfl⟩ : syracuseStep 557981 = 209243) (by norm_num)
theorem B1344437 : Blo 247818 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B558053 : Blo 247818 558053 := bbase (se 4 (by rfl) ⟨52317, by rfl⟩ : syracuseStep 558053 = 104635) (by norm_num)
theorem B558125 : Blo 247818 558125 := bbase (se 3 (by rfl) ⟨104648, by rfl⟩ : syracuseStep 558125 = 209297) (by norm_num)
theorem B558197 : Blo 247818 558197 := bbase (se 5 (by rfl) ⟨26165, by rfl⟩ : syracuseStep 558197 = 52331) (by norm_num)
theorem B361589 : Blo 247818 361589 := bbase (se 5 (by rfl) ⟨16949, by rfl⟩ : syracuseStep 361589 = 33899) (by norm_num)
theorem B1901717 : Blo 247818 1901717 := bbase (se 6 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 1901717 = 89143) (by norm_num)
theorem B558269 : Blo 247818 558269 := bbase (se 3 (by rfl) ⟨104675, by rfl⟩ : syracuseStep 558269 = 209351) (by norm_num)
theorem B558341 : Blo 247818 558341 := bbase (se 4 (by rfl) ⟨52344, by rfl⟩ : syracuseStep 558341 = 104689) (by norm_num)
theorem B558413 : Blo 247818 558413 := bbase (se 3 (by rfl) ⟨104702, by rfl⟩ : syracuseStep 558413 = 209405) (by norm_num)
theorem B755077 : Blo 247818 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B558485 : Blo 247818 558485 := bbase (se 6 (by rfl) ⟨13089, by rfl⟩ : syracuseStep 558485 = 26179) (by norm_num)
theorem B558557 : Blo 247818 558557 := bbase (se 3 (by rfl) ⟨104729, by rfl⟩ : syracuseStep 558557 = 209459) (by norm_num)
theorem B558629 : Blo 247818 558629 := bbase (se 4 (by rfl) ⟨52371, by rfl⟩ : syracuseStep 558629 = 104743) (by norm_num)
theorem B558701 : Blo 247818 558701 := bbase (se 3 (by rfl) ⟨104756, by rfl⟩ : syracuseStep 558701 = 209513) (by norm_num)
theorem B558773 : Blo 247818 558773 := bbase (se 5 (by rfl) ⟨26192, by rfl⟩ : syracuseStep 558773 = 52385) (by norm_num)
theorem B558845 : Blo 247818 558845 := bbase (se 3 (by rfl) ⟨104783, by rfl⟩ : syracuseStep 558845 = 209567) (by norm_num)
theorem B558917 : Blo 247818 558917 := bbase (se 4 (by rfl) ⟨52398, by rfl⟩ : syracuseStep 558917 = 104797) (by norm_num)
theorem B952181 : Blo 247818 952181 := bbase (se 5 (by rfl) ⟨44633, by rfl⟩ : syracuseStep 952181 = 89267) (by norm_num)
theorem B558989 : Blo 247818 558989 := bbase (se 3 (by rfl) ⟨104810, by rfl⟩ : syracuseStep 558989 = 209621) (by norm_num)
theorem B427933 : Blo 247818 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B559061 : Blo 247818 559061 := bbase (se 7 (by rfl) ⟨6551, by rfl⟩ : syracuseStep 559061 = 13103) (by norm_num)
theorem B559133 : Blo 247818 559133 := bbase (se 3 (by rfl) ⟨104837, by rfl⟩ : syracuseStep 559133 = 209675) (by norm_num)
theorem B559205 : Blo 247818 559205 := bbase (se 4 (by rfl) ⟨52425, by rfl⟩ : syracuseStep 559205 = 104851) (by norm_num)
theorem B952469 : Blo 247818 952469 := bbase (se 6 (by rfl) ⟨22323, by rfl⟩ : syracuseStep 952469 = 44647) (by norm_num)
theorem B559277 : Blo 247818 559277 := bbase (se 3 (by rfl) ⟨104864, by rfl⟩ : syracuseStep 559277 = 209729) (by norm_num)
theorem B559349 : Blo 247818 559349 := bbase (se 5 (by rfl) ⟨26219, by rfl⟩ : syracuseStep 559349 = 52439) (by norm_num)
theorem B559421 : Blo 247818 559421 := bbase (se 3 (by rfl) ⟨104891, by rfl⟩ : syracuseStep 559421 = 209783) (by norm_num)
theorem B297317 : Blo 247818 297317 := bbase (se 4 (by rfl) ⟨27873, by rfl⟩ : syracuseStep 297317 = 55747) (by norm_num)
theorem B559493 : Blo 247818 559493 := bbase (se 4 (by rfl) ⟨52452, by rfl⟩ : syracuseStep 559493 = 104905) (by norm_num)
theorem B559565 : Blo 247818 559565 := bbase (se 3 (by rfl) ⟨104918, by rfl⟩ : syracuseStep 559565 = 209837) (by norm_num)
theorem B559637 : Blo 247818 559637 := bbase (se 6 (by rfl) ⟨13116, by rfl⟩ : syracuseStep 559637 = 26233) (by norm_num)
theorem B559709 : Blo 247818 559709 := bbase (se 3 (by rfl) ⟨104945, by rfl⟩ : syracuseStep 559709 = 209891) (by norm_num)
theorem B559781 : Blo 247818 559781 := bbase (se 4 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 559781 = 104959) (by norm_num)
theorem B1378997 : Blo 247818 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B559853 : Blo 247818 559853 := bbase (se 3 (by rfl) ⟨104972, by rfl⟩ : syracuseStep 559853 = 209945) (by norm_num)
theorem B559925 : Blo 247818 559925 := bbase (se 5 (by rfl) ⟨26246, by rfl⟩ : syracuseStep 559925 = 52493) (by norm_num)
theorem B297793 : Blo 247818 297793 := bbase (se 2 (by rfl) ⟨111672, by rfl⟩ : syracuseStep 297793 = 223345) (by norm_num)
theorem B265037 : Blo 247818 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B559997 : Blo 247818 559997 := bbase (se 3 (by rfl) ⟨104999, by rfl⟩ : syracuseStep 559997 = 209999) (by norm_num)
theorem B560069 : Blo 247818 560069 := bbase (se 4 (by rfl) ⟨52506, by rfl⟩ : syracuseStep 560069 = 105013) (by norm_num)
theorem B297985 : Blo 247818 297985 := bbase (se 2 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 297985 = 223489) (by norm_num)
theorem B560141 : Blo 247818 560141 := bbase (se 3 (by rfl) ⟨105026, by rfl⟩ : syracuseStep 560141 = 210053) (by norm_num)
theorem B298009 : Blo 247818 298009 := bbase (se 2 (by rfl) ⟨111753, by rfl⟩ : syracuseStep 298009 = 223507) (by norm_num)
theorem B298013 : Blo 247818 298013 := bbase (se 3 (by rfl) ⟨55877, by rfl⟩ : syracuseStep 298013 = 111755) (by norm_num)
theorem B265285 : Blo 247818 265285 := bbase (se 4 (by rfl) ⟨24870, by rfl⟩ : syracuseStep 265285 = 49741) (by norm_num)
theorem B560213 : Blo 247818 560213 := bbase (se 8 (by rfl) ⟨3282, by rfl⟩ : syracuseStep 560213 = 6565) (by norm_num)
theorem B560285 : Blo 247818 560285 := bbase (se 3 (by rfl) ⟨105053, by rfl⟩ : syracuseStep 560285 = 210107) (by norm_num)
theorem B756965 : Blo 247818 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B560357 : Blo 247818 560357 := bbase (se 4 (by rfl) ⟨52533, by rfl⟩ : syracuseStep 560357 = 105067) (by norm_num)
theorem B855317 : Blo 247818 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B560429 : Blo 247818 560429 := bbase (se 3 (by rfl) ⟨105080, by rfl⟩ : syracuseStep 560429 = 210161) (by norm_num)
theorem B953653 : Blo 247818 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B1412437 : Blo 247818 1412437 := bbase (se 11 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 1412437 = 2069) (by norm_num)
theorem B560501 : Blo 247818 560501 := bbase (se 5 (by rfl) ⟨26273, by rfl⟩ : syracuseStep 560501 = 52547) (by norm_num)
theorem B560573 : Blo 247818 560573 := bbase (se 3 (by rfl) ⟨105107, by rfl⟩ : syracuseStep 560573 = 210215) (by norm_num)
theorem B265717 : Blo 247818 265717 := bbase (se 5 (by rfl) ⟨12455, by rfl⟩ : syracuseStep 265717 = 24911) (by norm_num)
theorem B560645 : Blo 247818 560645 := bbase (se 4 (by rfl) ⟨52560, by rfl⟩ : syracuseStep 560645 = 105121) (by norm_num)
theorem B298513 : Blo 247818 298513 := bbase (se 2 (by rfl) ⟨111942, by rfl⟩ : syracuseStep 298513 = 223885) (by norm_num)
theorem B1510933 : Blo 247818 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B265789 : Blo 247818 265789 := bbase (se 3 (by rfl) ⟨49835, by rfl⟩ : syracuseStep 265789 = 99671) (by norm_num)
theorem B560717 : Blo 247818 560717 := bbase (se 3 (by rfl) ⟨105134, by rfl⟩ : syracuseStep 560717 = 210269) (by norm_num)
theorem B953957 : Blo 247818 953957 := bbase (se 4 (by rfl) ⟨89433, by rfl⟩ : syracuseStep 953957 = 178867) (by norm_num)
theorem B298609 : Blo 247818 298609 := bbase (se 2 (by rfl) ⟨111978, by rfl⟩ : syracuseStep 298609 = 223957) (by norm_num)
theorem B560789 : Blo 247818 560789 := bbase (se 6 (by rfl) ⟨13143, by rfl⟩ : syracuseStep 560789 = 26287) (by norm_num)
theorem B560861 : Blo 247818 560861 := bbase (se 3 (by rfl) ⟨105161, by rfl⟩ : syracuseStep 560861 = 210323) (by norm_num)
theorem B560933 : Blo 247818 560933 := bbase (se 4 (by rfl) ⟨52587, by rfl⟩ : syracuseStep 560933 = 105175) (by norm_num)
theorem B561005 : Blo 247818 561005 := bbase (se 3 (by rfl) ⟨105188, by rfl⟩ : syracuseStep 561005 = 210377) (by norm_num)
theorem B266161 : Blo 247818 266161 := bbase (se 2 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 266161 = 199621) (by norm_num)
theorem B561077 : Blo 247818 561077 := bbase (se 5 (by rfl) ⟨26300, by rfl⟩ : syracuseStep 561077 = 52601) (by norm_num)
theorem B561149 : Blo 247818 561149 := bbase (se 3 (by rfl) ⟨105215, by rfl⟩ : syracuseStep 561149 = 210431) (by norm_num)
theorem B561221 : Blo 247818 561221 := bbase (se 4 (by rfl) ⟨52614, by rfl⟩ : syracuseStep 561221 = 105229) (by norm_num)
theorem B561293 : Blo 247818 561293 := bbase (se 3 (by rfl) ⟨105242, by rfl⟩ : syracuseStep 561293 = 210485) (by norm_num)
theorem B561365 : Blo 247818 561365 := bbase (se 7 (by rfl) ⟨6578, by rfl⟩ : syracuseStep 561365 = 13157) (by norm_num)
theorem B2396405 : Blo 247818 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B561437 : Blo 247818 561437 := bbase (se 3 (by rfl) ⟨105269, by rfl⟩ : syracuseStep 561437 = 210539) (by norm_num)
theorem B266537 : Blo 247818 266537 := bbase (se 2 (by rfl) ⟨99951, by rfl⟩ : syracuseStep 266537 = 199903) (by norm_num)
theorem B561509 : Blo 247818 561509 := bbase (se 4 (by rfl) ⟨52641, by rfl⟩ : syracuseStep 561509 = 105283) (by norm_num)
theorem B266609 : Blo 247818 266609 := bbase (se 2 (by rfl) ⟨99978, by rfl⟩ : syracuseStep 266609 = 199957) (by norm_num)
theorem B397685 : Blo 247818 397685 := bbase (se 5 (by rfl) ⟨18641, by rfl⟩ : syracuseStep 397685 = 37283) (by norm_num)
theorem B561581 : Blo 247818 561581 := bbase (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) (by norm_num)
theorem B561653 : Blo 247818 561653 := bbase (se 5 (by rfl) ⟨26327, by rfl⟩ : syracuseStep 561653 = 52655) (by norm_num)
theorem B1217045 : Blo 247818 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B266797 : Blo 247818 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B561725 : Blo 247818 561725 := bbase (se 3 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 561725 = 210647) (by norm_num)
theorem B299585 : Blo 247818 299585 := bbase (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) (by norm_num)
theorem B397909 : Blo 247818 397909 := bbase (se 8 (by rfl) ⟨2331, by rfl⟩ : syracuseStep 397909 = 4663) (by norm_num)
theorem B7246421 : Blo 247818 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B561797 : Blo 247818 561797 := bbase (se 4 (by rfl) ⟨52668, by rfl⟩ : syracuseStep 561797 = 105337) (by norm_num)
theorem B627365 : Blo 247818 627365 := bbase (se 4 (by rfl) ⟨58815, by rfl⟩ : syracuseStep 627365 = 117631) (by norm_num)
theorem B561869 : Blo 247818 561869 := bbase (se 3 (by rfl) ⟨105350, by rfl⟩ : syracuseStep 561869 = 210701) (by norm_num)
theorem B266981 : Blo 247818 266981 := bbase (se 4 (by rfl) ⟨25029, by rfl⟩ : syracuseStep 266981 = 50059) (by norm_num)
theorem B561941 : Blo 247818 561941 := bbase (se 6 (by rfl) ⟨13170, by rfl⟩ : syracuseStep 561941 = 26341) (by norm_num)
theorem B2036501 : Blo 247818 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B562013 : Blo 247818 562013 := bbase (se 3 (by rfl) ⟨105377, by rfl⟩ : syracuseStep 562013 = 210755) (by norm_num)
theorem B562085 : Blo 247818 562085 := bbase (se 4 (by rfl) ⟨52695, by rfl⟩ : syracuseStep 562085 = 105391) (by norm_num)
theorem B529357 : Blo 247818 529357 := bbase (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) (by norm_num)
theorem B562157 : Blo 247818 562157 := bbase (se 3 (by rfl) ⟨105404, by rfl⟩ : syracuseStep 562157 = 210809) (by norm_num)
theorem B627709 : Blo 247818 627709 := bbase (se 3 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 627709 = 235391) (by norm_num)
theorem B300061 : Blo 247818 300061 := bbase (se 3 (by rfl) ⟨56261, by rfl⟩ : syracuseStep 300061 = 112523) (by norm_num)
theorem B562229 : Blo 247818 562229 := bbase (se 5 (by rfl) ⟨26354, by rfl⟩ : syracuseStep 562229 = 52709) (by norm_num)
theorem B300089 : Blo 247818 300089 := bbase (se 2 (by rfl) ⟨112533, by rfl⟩ : syracuseStep 300089 = 225067) (by norm_num)
theorem B627821 : Blo 247818 627821 := bbase (se 3 (by rfl) ⟨117716, by rfl⟩ : syracuseStep 627821 = 235433) (by norm_num)
theorem B562301 : Blo 247818 562301 := bbase (se 3 (by rfl) ⟨105431, by rfl⟩ : syracuseStep 562301 = 210863) (by norm_num)
theorem B562373 : Blo 247818 562373 := bbase (se 4 (by rfl) ⟨52722, by rfl⟩ : syracuseStep 562373 = 105445) (by norm_num)
theorem B300277 : Blo 247818 300277 := bbase (se 5 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 300277 = 28151) (by norm_num)
theorem B562445 : Blo 247818 562445 := bbase (se 3 (by rfl) ⟨105458, by rfl⟩ : syracuseStep 562445 = 210917) (by norm_num)
theorem B1414421 : Blo 247818 1414421 := bbase (se 6 (by rfl) ⟨33150, by rfl⟩ : syracuseStep 1414421 = 66301) (by norm_num)
theorem B628013 : Blo 247818 628013 := bbase (se 3 (by rfl) ⟨117752, by rfl⟩ : syracuseStep 628013 = 235505) (by norm_num)
theorem B529733 : Blo 247818 529733 := bbase (se 4 (by rfl) ⟨49662, by rfl⟩ : syracuseStep 529733 = 99325) (by norm_num)
theorem B562517 : Blo 247818 562517 := bbase (se 14 (by rfl) ⟨51, by rfl⟩ : syracuseStep 562517 = 103) (by norm_num)
theorem B300397 : Blo 247818 300397 := bbase (se 3 (by rfl) ⟨56324, by rfl⟩ : syracuseStep 300397 = 112649) (by norm_num)
theorem B562589 : Blo 247818 562589 := bbase (se 3 (by rfl) ⟨105485, by rfl⟩ : syracuseStep 562589 = 210971) (by norm_num)
theorem B267733 : Blo 247818 267733 := bbase (se 7 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 267733 = 6275) (by norm_num)
theorem B562661 : Blo 247818 562661 := bbase (se 4 (by rfl) ⟨52749, by rfl⟩ : syracuseStep 562661 = 105499) (by norm_num)
theorem B267805 : Blo 247818 267805 := bbase (se 3 (by rfl) ⟨50213, by rfl⟩ : syracuseStep 267805 = 100427) (by norm_num)
theorem B562733 : Blo 247818 562733 := bbase (se 3 (by rfl) ⟨105512, by rfl⟩ : syracuseStep 562733 = 211025) (by norm_num)
theorem B2135605 : Blo 247818 2135605 := bbase (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) (by norm_num)
theorem B562805 : Blo 247818 562805 := bbase (se 5 (by rfl) ⟨26381, by rfl⟩ : syracuseStep 562805 = 52763) (by norm_num)
theorem B628357 : Blo 247818 628357 := bbase (se 4 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 628357 = 117817) (by norm_num)
theorem B956069 : Blo 247818 956069 := bbase (se 4 (by rfl) ⟨89631, by rfl⟩ : syracuseStep 956069 = 179263) (by norm_num)
theorem B562877 : Blo 247818 562877 := bbase (se 3 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 562877 = 211079) (by norm_num)
theorem B267985 : Blo 247818 267985 := bbase (se 2 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 267985 = 200989) (by norm_num)
theorem B1218277 : Blo 247818 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B628469 : Blo 247818 628469 := bbase (se 5 (by rfl) ⟨29459, by rfl⟩ : syracuseStep 628469 = 58919) (by norm_num)
theorem B562949 : Blo 247818 562949 := bbase (se 4 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 562949 = 105553) (by norm_num)
theorem B563021 : Blo 247818 563021 := bbase (se 3 (by rfl) ⟨105566, by rfl⟩ : syracuseStep 563021 = 211133) (by norm_num)
theorem B563093 : Blo 247818 563093 := bbase (se 6 (by rfl) ⟨13197, by rfl⟩ : syracuseStep 563093 = 26395) (by norm_num)
theorem B628661 : Blo 247818 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B956357 : Blo 247818 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B399325 : Blo 247818 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B563165 : Blo 247818 563165 := bbase (se 3 (by rfl) ⟨105593, by rfl⟩ : syracuseStep 563165 = 211187) (by norm_num)
theorem B366557 : Blo 247818 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B563237 : Blo 247818 563237 := bbase (se 4 (by rfl) ⟨52803, by rfl⟩ : syracuseStep 563237 = 105607) (by norm_num)
theorem B563309 : Blo 247818 563309 := bbase (se 3 (by rfl) ⟨105620, by rfl⟩ : syracuseStep 563309 = 211241) (by norm_num)
theorem B268429 : Blo 247818 268429 := bbase (se 3 (by rfl) ⟨50330, by rfl⟩ : syracuseStep 268429 = 100661) (by norm_num)
theorem B563381 : Blo 247818 563381 := bbase (se 5 (by rfl) ⟨26408, by rfl⟩ : syracuseStep 563381 = 52817) (by norm_num)
theorem B5445845 : Blo 247818 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B399581 : Blo 247818 399581 := bbase (se 3 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 399581 = 149843) (by norm_num)
theorem B563453 : Blo 247818 563453 := bbase (se 3 (by rfl) ⟨105647, by rfl⟩ : syracuseStep 563453 = 211295) (by norm_num)
theorem B268553 : Blo 247818 268553 := bbase (se 2 (by rfl) ⟨100707, by rfl⟩ : syracuseStep 268553 = 201415) (by norm_num)
theorem B629005 : Blo 247818 629005 := bbase (se 3 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 629005 = 235877) (by norm_num)
theorem B563525 : Blo 247818 563525 := bbase (se 4 (by rfl) ⟨52830, by rfl⟩ : syracuseStep 563525 = 105661) (by norm_num)
theorem B629117 : Blo 247818 629117 := bbase (se 3 (by rfl) ⟨117959, by rfl⟩ : syracuseStep 629117 = 235919) (by norm_num)
theorem B563597 : Blo 247818 563597 := bbase (se 3 (by rfl) ⟨105674, by rfl⟩ : syracuseStep 563597 = 211349) (by norm_num)
theorem B399773 : Blo 247818 399773 := bbase (se 3 (by rfl) ⟨74957, by rfl⟩ : syracuseStep 399773 = 149915) (by norm_num)
theorem B563669 : Blo 247818 563669 := bbase (se 7 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 563669 = 13211) (by norm_num)
theorem B268805 : Blo 247818 268805 := bbase (se 4 (by rfl) ⟨25200, by rfl⟩ : syracuseStep 268805 = 50401) (by norm_num)
theorem B563741 : Blo 247818 563741 := bbase (se 3 (by rfl) ⟨105701, by rfl⟩ : syracuseStep 563741 = 211403) (by norm_num)
theorem B629309 : Blo 247818 629309 := bbase (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) (by norm_num)
theorem B1350229 : Blo 247818 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B563813 : Blo 247818 563813 := bbase (se 4 (by rfl) ⟨52857, by rfl⟩ : syracuseStep 563813 = 105715) (by norm_num)
theorem B563885 : Blo 247818 563885 := bbase (se 3 (by rfl) ⟨105728, by rfl⟩ : syracuseStep 563885 = 211457) (by norm_num)
theorem B3185365 : Blo 247818 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B563957 : Blo 247818 563957 := bbase (se 5 (by rfl) ⟨26435, by rfl⟩ : syracuseStep 563957 = 52871) (by norm_num)
theorem B564029 : Blo 247818 564029 := bbase (se 3 (by rfl) ⟨105755, by rfl⟩ : syracuseStep 564029 = 211511) (by norm_num)
theorem B760661 : Blo 247818 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B564101 : Blo 247818 564101 := bbase (se 4 (by rfl) ⟨52884, by rfl⟩ : syracuseStep 564101 = 105769) (by norm_num)
theorem B629653 : Blo 247818 629653 := bbase (se 6 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 629653 = 29515) (by norm_num)
theorem B301973 : Blo 247818 301973 := bbase (se 6 (by rfl) ⟨7077, by rfl⟩ : syracuseStep 301973 = 14155) (by norm_num)
theorem B531373 : Blo 247818 531373 := bbase (se 3 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 531373 = 199265) (by norm_num)
theorem B564173 : Blo 247818 564173 := bbase (se 3 (by rfl) ⟨105782, by rfl⟩ : syracuseStep 564173 = 211565) (by norm_num)
theorem B629765 : Blo 247818 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B564245 : Blo 247818 564245 := bbase (se 6 (by rfl) ⟨13224, by rfl⟩ : syracuseStep 564245 = 26449) (by norm_num)
theorem B564317 : Blo 247818 564317 := bbase (se 3 (by rfl) ⟨105809, by rfl⟩ : syracuseStep 564317 = 211619) (by norm_num)
theorem B564389 : Blo 247818 564389 := bbase (se 4 (by rfl) ⟨52911, by rfl⟩ : syracuseStep 564389 = 105823) (by norm_num)
theorem B629957 : Blo 247818 629957 := bbase (se 4 (by rfl) ⟨59058, by rfl⟩ : syracuseStep 629957 = 118117) (by norm_num)
theorem B564461 : Blo 247818 564461 := bbase (se 3 (by rfl) ⟨105836, by rfl⟩ : syracuseStep 564461 = 211673) (by norm_num)
theorem B564533 : Blo 247818 564533 := bbase (se 5 (by rfl) ⟨26462, by rfl⟩ : syracuseStep 564533 = 52925) (by norm_num)
theorem B400709 : Blo 247818 400709 := bbase (se 4 (by rfl) ⟨37566, by rfl⟩ : syracuseStep 400709 = 75133) (by norm_num)
theorem B269693 : Blo 247818 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B564605 : Blo 247818 564605 := bbase (se 3 (by rfl) ⟨105863, by rfl⟩ : syracuseStep 564605 = 211727) (by norm_num)
theorem B1416629 : Blo 247818 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B564677 : Blo 247818 564677 := bbase (se 4 (by rfl) ⟨52938, by rfl⟩ : syracuseStep 564677 = 105877) (by norm_num)
theorem B2137589 : Blo 247818 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B564749 : Blo 247818 564749 := bbase (se 3 (by rfl) ⟨105890, by rfl⟩ : syracuseStep 564749 = 211781) (by norm_num)
theorem B630301 : Blo 247818 630301 := bbase (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) (by norm_num)
theorem B564821 : Blo 247818 564821 := bbase (se 8 (by rfl) ⟨3309, by rfl⟩ : syracuseStep 564821 = 6619) (by norm_num)
theorem B630413 : Blo 247818 630413 := bbase (se 3 (by rfl) ⟨118202, by rfl⟩ : syracuseStep 630413 = 236405) (by norm_num)
theorem B1023637 : Blo 247818 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B564893 : Blo 247818 564893 := bbase (se 3 (by rfl) ⟨105917, by rfl⟩ : syracuseStep 564893 = 211835) (by norm_num)
theorem B401093 : Blo 247818 401093 := bbase (se 4 (by rfl) ⟨37602, by rfl⟩ : syracuseStep 401093 = 75205) (by norm_num)
theorem B564965 : Blo 247818 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B532261 : Blo 247818 532261 := bbase (se 4 (by rfl) ⟨49899, by rfl⟩ : syracuseStep 532261 = 99799) (by norm_num)
theorem B565037 : Blo 247818 565037 := bbase (se 3 (by rfl) ⟨105944, by rfl⟩ : syracuseStep 565037 = 211889) (by norm_num)
theorem B401221 : Blo 247818 401221 := bbase (se 4 (by rfl) ⟨37614, by rfl⟩ : syracuseStep 401221 = 75229) (by norm_num)
theorem B630605 : Blo 247818 630605 := bbase (se 3 (by rfl) ⟨118238, by rfl⟩ : syracuseStep 630605 = 236477) (by norm_num)
theorem B565109 : Blo 247818 565109 := bbase (se 5 (by rfl) ⟨26489, by rfl⟩ : syracuseStep 565109 = 52979) (by norm_num)
theorem B794549 : Blo 247818 794549 := bbase (se 5 (by rfl) ⟨37244, by rfl⟩ : syracuseStep 794549 = 74489) (by norm_num)
theorem B565181 : Blo 247818 565181 := bbase (se 3 (by rfl) ⟨105971, by rfl⟩ : syracuseStep 565181 = 211943) (by norm_num)
theorem B303049 : Blo 247818 303049 := bbase (se 2 (by rfl) ⟨113643, by rfl⟩ : syracuseStep 303049 = 227287) (by norm_num)
theorem B565253 : Blo 247818 565253 := bbase (se 4 (by rfl) ⟨52992, by rfl⟩ : syracuseStep 565253 = 105985) (by norm_num)
theorem B335893 : Blo 247818 335893 := bbase (se 6 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 335893 = 15745) (by norm_num)
theorem B565325 : Blo 247818 565325 := bbase (se 3 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 565325 = 211997) (by norm_num)
theorem B598141 : Blo 247818 598141 := bbase (se 3 (by rfl) ⟨112151, by rfl⟩ : syracuseStep 598141 = 224303) (by norm_num)
theorem B565397 : Blo 247818 565397 := bbase (se 6 (by rfl) ⟨13251, by rfl⟩ : syracuseStep 565397 = 26503) (by norm_num)
theorem B630949 : Blo 247818 630949 := bbase (se 4 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 630949 = 118303) (by norm_num)
theorem B565469 : Blo 247818 565469 := bbase (se 3 (by rfl) ⟨106025, by rfl⟩ : syracuseStep 565469 = 212051) (by norm_num)
theorem B631061 : Blo 247818 631061 := bbase (se 6 (by rfl) ⟨14790, by rfl⟩ : syracuseStep 631061 = 29581) (by norm_num)
theorem B532757 : Blo 247818 532757 := bbase (se 6 (by rfl) ⟨12486, by rfl⟩ : syracuseStep 532757 = 24973) (by norm_num)
theorem B565541 : Blo 247818 565541 := bbase (se 4 (by rfl) ⟨53019, by rfl⟩ : syracuseStep 565541 = 106039) (by norm_num)
theorem B270637 : Blo 247818 270637 := bbase (se 3 (by rfl) ⟨50744, by rfl⟩ : syracuseStep 270637 = 101489) (by norm_num)
theorem B598333 : Blo 247818 598333 := bbase (se 3 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 598333 = 224375) (by norm_num)
theorem B598373 : Blo 247818 598373 := bbase (se 4 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 598373 = 112195) (by norm_num)
theorem B565613 : Blo 247818 565613 := bbase (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) (by norm_num)
theorem B565685 : Blo 247818 565685 := bbase (se 5 (by rfl) ⟨26516, by rfl⟩ : syracuseStep 565685 = 53033) (by norm_num)
theorem B631253 : Blo 247818 631253 := bbase (se 7 (by rfl) ⟨7397, by rfl⟩ : syracuseStep 631253 = 14795) (by norm_num)
theorem B565757 : Blo 247818 565757 := bbase (se 3 (by rfl) ⟨106079, by rfl⟩ : syracuseStep 565757 = 212159) (by norm_num)
theorem B565829 : Blo 247818 565829 := bbase (se 4 (by rfl) ⟨53046, by rfl⟩ : syracuseStep 565829 = 106093) (by norm_num)
theorem B598661 : Blo 247818 598661 := bbase (se 4 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 598661 = 112249) (by norm_num)
theorem B565901 : Blo 247818 565901 := bbase (se 3 (by rfl) ⟨106106, by rfl⟩ : syracuseStep 565901 = 212213) (by norm_num)
theorem B565925 : Blo 247818 565925 := bbase (se 4 (by rfl) ⟨53055, by rfl⟩ : syracuseStep 565925 = 106111) (by norm_num)
theorem B565973 : Blo 247818 565973 := bbase (se 7 (by rfl) ⟨6632, by rfl⟩ : syracuseStep 565973 = 13265) (by norm_num)
theorem B303845 : Blo 247818 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B1909493 : Blo 247818 1909493 := bbase (se 5 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 1909493 = 179015) (by norm_num)
theorem B566045 : Blo 247818 566045 := bbase (se 3 (by rfl) ⟨106133, by rfl⟩ : syracuseStep 566045 = 212267) (by norm_num)
theorem B631597 : Blo 247818 631597 := bbase (se 3 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 631597 = 236849) (by norm_num)
theorem B402221 : Blo 247818 402221 := bbase (se 3 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 402221 = 150833) (by norm_num)
theorem B566117 : Blo 247818 566117 := bbase (se 4 (by rfl) ⟨53073, by rfl⟩ : syracuseStep 566117 = 106147) (by norm_num)
theorem B3449749 : Blo 247818 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B631709 : Blo 247818 631709 := bbase (se 3 (by rfl) ⟨118445, by rfl⟩ : syracuseStep 631709 = 236891) (by norm_num)
theorem B402349 : Blo 247818 402349 := bbase (se 3 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 402349 = 150881) (by norm_num)
theorem B566189 : Blo 247818 566189 := bbase (se 3 (by rfl) ⟨106160, by rfl⟩ : syracuseStep 566189 = 212321) (by norm_num)
theorem B566261 : Blo 247818 566261 := bbase (se 5 (by rfl) ⟨26543, by rfl⟩ : syracuseStep 566261 = 53087) (by norm_num)
theorem B566333 : Blo 247818 566333 := bbase (se 3 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 566333 = 212375) (by norm_num)
theorem B631901 : Blo 247818 631901 := bbase (se 3 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 631901 = 236963) (by norm_num)
theorem B533621 : Blo 247818 533621 := bbase (se 5 (by rfl) ⟨25013, by rfl⟩ : syracuseStep 533621 = 50027) (by norm_num)
theorem B566405 : Blo 247818 566405 := bbase (se 4 (by rfl) ⟨53100, by rfl⟩ : syracuseStep 566405 = 106201) (by norm_num)
theorem B566477 : Blo 247818 566477 := bbase (se 3 (by rfl) ⟨106214, by rfl⟩ : syracuseStep 566477 = 212429) (by norm_num)
theorem B533765 : Blo 247818 533765 := bbase (se 4 (by rfl) ⟨50040, by rfl⟩ : syracuseStep 533765 = 100081) (by norm_num)
theorem B566549 : Blo 247818 566549 := bbase (se 6 (by rfl) ⟨13278, by rfl⟩ : syracuseStep 566549 = 26557) (by norm_num)
theorem B402733 : Blo 247818 402733 := bbase (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) (by norm_num)
theorem B763253 : Blo 247818 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B632245 : Blo 247818 632245 := bbase (se 5 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 632245 = 59273) (by norm_num)
theorem B763397 : Blo 247818 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B632357 : Blo 247818 632357 := bbase (se 4 (by rfl) ⟨59283, by rfl⟩ : syracuseStep 632357 = 118567) (by norm_num)
theorem B402989 : Blo 247818 402989 := bbase (se 3 (by rfl) ⟨75560, by rfl⟩ : syracuseStep 402989 = 151121) (by norm_num)
theorem B337493 : Blo 247818 337493 := bbase (se 8 (by rfl) ⟨1977, by rfl⟩ : syracuseStep 337493 = 3955) (by norm_num)
theorem B1255013 : Blo 247818 1255013 := bbase (se 4 (by rfl) ⟨117657, by rfl⟩ : syracuseStep 1255013 = 235315) (by norm_num)
theorem B304769 : Blo 247818 304769 := bbase (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) (by norm_num)
theorem B632549 : Blo 247818 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B304921 : Blo 247818 304921 := bbase (se 2 (by rfl) ⟨114345, by rfl⟩ : syracuseStep 304921 = 228691) (by norm_num)
theorem B1058629 : Blo 247818 1058629 := bbase (se 4 (by rfl) ⟨99246, by rfl⟩ : syracuseStep 1058629 = 198493) (by norm_num)
theorem B1058645 : Blo 247818 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B1517429 : Blo 247818 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B534509 : Blo 247818 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B632893 : Blo 247818 632893 := bbase (se 3 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 632893 = 237335) (by norm_num)
theorem B764005 : Blo 247818 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B633005 : Blo 247818 633005 := bbase (se 3 (by rfl) ⟨118688, by rfl⟩ : syracuseStep 633005 = 237377) (by norm_num)
theorem B305353 : Blo 247818 305353 := bbase (se 2 (by rfl) ⟨114507, by rfl⟩ : syracuseStep 305353 = 229015) (by norm_num)
theorem B633197 : Blo 247818 633197 := bbase (se 3 (by rfl) ⟨118724, by rfl⟩ : syracuseStep 633197 = 237449) (by norm_num)
theorem B633541 : Blo 247818 633541 := bbase (se 4 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 633541 = 118789) (by norm_num)
theorem B535261 : Blo 247818 535261 := bbase (se 3 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 535261 = 200723) (by norm_num)
theorem B633653 : Blo 247818 633653 := bbase (se 5 (by rfl) ⟨29702, by rfl⟩ : syracuseStep 633653 = 59405) (by norm_num)
theorem B535405 : Blo 247818 535405 := bbase (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) (by norm_num)
theorem B1256309 : Blo 247818 1256309 := bbase (se 5 (by rfl) ⟨58889, by rfl⟩ : syracuseStep 1256309 = 117779) (by norm_num)
theorem B633845 : Blo 247818 633845 := bbase (se 5 (by rfl) ⟨29711, by rfl⟩ : syracuseStep 633845 = 59423) (by norm_num)
theorem B797701 : Blo 247818 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B568333 : Blo 247818 568333 := bbase (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) (by norm_num)
theorem B371741 : Blo 247818 371741 := bbase (se 3 (by rfl) ⟨69701, by rfl⟩ : syracuseStep 371741 = 139403) (by norm_num)
theorem B371765 : Blo 247818 371765 := bbase (se 5 (by rfl) ⟨17426, by rfl⟩ : syracuseStep 371765 = 34853) (by norm_num)
theorem B371789 : Blo 247818 371789 := bbase (se 3 (by rfl) ⟨69710, by rfl⟩ : syracuseStep 371789 = 139421) (by norm_num)
theorem B371813 : Blo 247818 371813 := bbase (se 4 (by rfl) ⟨34857, by rfl⟩ : syracuseStep 371813 = 69715) (by norm_num)
theorem B371837 : Blo 247818 371837 := bbase (se 3 (by rfl) ⟨69719, by rfl⟩ : syracuseStep 371837 = 139439) (by norm_num)
theorem B371861 : Blo 247818 371861 := bbase (se 6 (by rfl) ⟨8715, by rfl⟩ : syracuseStep 371861 = 17431) (by norm_num)
theorem B339109 : Blo 247818 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B371885 : Blo 247818 371885 := bbase (se 3 (by rfl) ⟨69728, by rfl⟩ : syracuseStep 371885 = 139457) (by norm_num)
theorem B371909 : Blo 247818 371909 := bbase (se 4 (by rfl) ⟨34866, by rfl⟩ : syracuseStep 371909 = 69733) (by norm_num)
theorem B371933 : Blo 247818 371933 := bbase (se 3 (by rfl) ⟨69737, by rfl⟩ : syracuseStep 371933 = 139475) (by norm_num)
theorem B535781 : Blo 247818 535781 := bbase (se 4 (by rfl) ⟨50229, by rfl⟩ : syracuseStep 535781 = 100459) (by norm_num)
theorem B371957 : Blo 247818 371957 := bbase (se 5 (by rfl) ⟨17435, by rfl⟩ : syracuseStep 371957 = 34871) (by norm_num)
theorem B765173 : Blo 247818 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B371981 : Blo 247818 371981 := bbase (se 3 (by rfl) ⟨69746, by rfl⟩ : syracuseStep 371981 = 139493) (by norm_num)
theorem B372005 : Blo 247818 372005 := bbase (se 4 (by rfl) ⟨34875, by rfl⟩ : syracuseStep 372005 = 69751) (by norm_num)
theorem B372029 : Blo 247818 372029 := bbase (se 3 (by rfl) ⟨69755, by rfl⟩ : syracuseStep 372029 = 139511) (by norm_num)
theorem B634189 : Blo 247818 634189 := bbase (se 3 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 634189 = 237821) (by norm_num)
theorem B372053 : Blo 247818 372053 := bbase (se 11 (by rfl) ⟨272, by rfl⟩ : syracuseStep 372053 = 545) (by norm_num)
theorem B372077 : Blo 247818 372077 := bbase (se 3 (by rfl) ⟨69764, by rfl⟩ : syracuseStep 372077 = 139529) (by norm_num)
theorem B372101 : Blo 247818 372101 := bbase (se 4 (by rfl) ⟨34884, by rfl⟩ : syracuseStep 372101 = 69769) (by norm_num)
theorem B372125 : Blo 247818 372125 := bbase (se 3 (by rfl) ⟨69773, by rfl⟩ : syracuseStep 372125 = 139547) (by norm_num)
theorem B372149 : Blo 247818 372149 := bbase (se 5 (by rfl) ⟨17444, by rfl⟩ : syracuseStep 372149 = 34889) (by norm_num)
theorem B634301 : Blo 247818 634301 := bbase (se 3 (by rfl) ⟨118931, by rfl⟩ : syracuseStep 634301 = 237863) (by norm_num)
theorem B372173 : Blo 247818 372173 := bbase (se 3 (by rfl) ⟨69782, by rfl⟩ : syracuseStep 372173 = 139565) (by norm_num)
theorem B372197 : Blo 247818 372197 := bbase (se 4 (by rfl) ⟨34893, by rfl⟩ : syracuseStep 372197 = 69787) (by norm_num)
theorem B372221 : Blo 247818 372221 := bbase (se 3 (by rfl) ⟨69791, by rfl⟩ : syracuseStep 372221 = 139583) (by norm_num)
theorem B372245 : Blo 247818 372245 := bbase (se 6 (by rfl) ⟨8724, by rfl⟩ : syracuseStep 372245 = 17449) (by norm_num)
theorem B372269 : Blo 247818 372269 := bbase (se 3 (by rfl) ⟨69800, by rfl⟩ : syracuseStep 372269 = 139601) (by norm_num)
theorem B372293 : Blo 247818 372293 := bbase (se 4 (by rfl) ⟨34902, by rfl⟩ : syracuseStep 372293 = 69805) (by norm_num)
theorem B536149 : Blo 247818 536149 := bbase (se 8 (by rfl) ⟨3141, by rfl⟩ : syracuseStep 536149 = 6283) (by norm_num)
theorem B372317 : Blo 247818 372317 := bbase (se 3 (by rfl) ⟨69809, by rfl⟩ : syracuseStep 372317 = 139619) (by norm_num)
theorem B372341 : Blo 247818 372341 := bbase (se 5 (by rfl) ⟨17453, by rfl⟩ : syracuseStep 372341 = 34907) (by norm_num)
theorem B634493 : Blo 247818 634493 := bbase (se 3 (by rfl) ⟨118967, by rfl⟩ : syracuseStep 634493 = 237935) (by norm_num)
theorem B372365 : Blo 247818 372365 := bbase (se 3 (by rfl) ⟨69818, by rfl⟩ : syracuseStep 372365 = 139637) (by norm_num)
theorem B372389 : Blo 247818 372389 := bbase (se 4 (by rfl) ⟨34911, by rfl⟩ : syracuseStep 372389 = 69823) (by norm_num)
theorem B372413 : Blo 247818 372413 := bbase (se 3 (by rfl) ⟨69827, by rfl⟩ : syracuseStep 372413 = 139655) (by norm_num)
theorem B372437 : Blo 247818 372437 := bbase (se 7 (by rfl) ⟨4364, by rfl⟩ : syracuseStep 372437 = 8729) (by norm_num)
theorem B569045 : Blo 247818 569045 := bbase (se 7 (by rfl) ⟨6668, by rfl⟩ : syracuseStep 569045 = 13337) (by norm_num)
theorem B372461 : Blo 247818 372461 := bbase (se 3 (by rfl) ⟨69836, by rfl⟩ : syracuseStep 372461 = 139673) (by norm_num)
theorem B372485 : Blo 247818 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B372509 : Blo 247818 372509 := bbase (se 3 (by rfl) ⟨69845, by rfl⟩ : syracuseStep 372509 = 139691) (by norm_num)
theorem B372533 : Blo 247818 372533 := bbase (se 5 (by rfl) ⟨17462, by rfl⟩ : syracuseStep 372533 = 34925) (by norm_num)
theorem B372557 : Blo 247818 372557 := bbase (se 3 (by rfl) ⟨69854, by rfl⟩ : syracuseStep 372557 = 139709) (by norm_num)
theorem B372581 : Blo 247818 372581 := bbase (se 4 (by rfl) ⟨34929, by rfl⟩ : syracuseStep 372581 = 69859) (by norm_num)
theorem B372605 : Blo 247818 372605 := bbase (se 3 (by rfl) ⟨69863, by rfl⟩ : syracuseStep 372605 = 139727) (by norm_num)
theorem B372629 : Blo 247818 372629 := bbase (se 6 (by rfl) ⟨8733, by rfl⟩ : syracuseStep 372629 = 17467) (by norm_num)
theorem B372653 : Blo 247818 372653 := bbase (se 3 (by rfl) ⟨69872, by rfl⟩ : syracuseStep 372653 = 139745) (by norm_num)
theorem B372677 : Blo 247818 372677 := bbase (se 4 (by rfl) ⟨34938, by rfl⟩ : syracuseStep 372677 = 69877) (by norm_num)
theorem B634837 : Blo 247818 634837 := bbase (se 7 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 634837 = 14879) (by norm_num)
theorem B372701 : Blo 247818 372701 := bbase (se 3 (by rfl) ⟨69881, by rfl⟩ : syracuseStep 372701 = 139763) (by norm_num)
theorem B372725 : Blo 247818 372725 := bbase (se 5 (by rfl) ⟨17471, by rfl⟩ : syracuseStep 372725 = 34943) (by norm_num)
theorem B372749 : Blo 247818 372749 := bbase (se 3 (by rfl) ⟨69890, by rfl⟩ : syracuseStep 372749 = 139781) (by norm_num)
theorem B1060901 : Blo 247818 1060901 := bbase (se 4 (by rfl) ⟨99459, by rfl⟩ : syracuseStep 1060901 = 198919) (by norm_num)
theorem B372773 : Blo 247818 372773 := bbase (se 4 (by rfl) ⟨34947, by rfl⟩ : syracuseStep 372773 = 69895) (by norm_num)
theorem B372797 : Blo 247818 372797 := bbase (se 3 (by rfl) ⟨69899, by rfl⟩ : syracuseStep 372797 = 139799) (by norm_num)
theorem B471109 : Blo 247818 471109 := bbase (se 4 (by rfl) ⟨44166, by rfl⟩ : syracuseStep 471109 = 88333) (by norm_num)
theorem B634949 : Blo 247818 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B372821 : Blo 247818 372821 := bbase (se 8 (by rfl) ⟨2184, by rfl⟩ : syracuseStep 372821 = 4369) (by norm_num)
theorem B372845 : Blo 247818 372845 := bbase (se 3 (by rfl) ⟨69908, by rfl⟩ : syracuseStep 372845 = 139817) (by norm_num)
theorem B1257605 : Blo 247818 1257605 := bbase (se 4 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 1257605 = 235801) (by norm_num)
theorem B372869 : Blo 247818 372869 := bbase (se 4 (by rfl) ⟨34956, by rfl⟩ : syracuseStep 372869 = 69913) (by norm_num)
theorem B602245 : Blo 247818 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B372893 : Blo 247818 372893 := bbase (se 3 (by rfl) ⟨69917, by rfl⟩ : syracuseStep 372893 = 139835) (by norm_num)
theorem B372917 : Blo 247818 372917 := bbase (se 5 (by rfl) ⟨17480, by rfl⟩ : syracuseStep 372917 = 34961) (by norm_num)
theorem B372941 : Blo 247818 372941 := bbase (se 3 (by rfl) ⟨69926, by rfl⟩ : syracuseStep 372941 = 139853) (by norm_num)
theorem B471253 : Blo 247818 471253 := bbase (se 7 (by rfl) ⟨5522, by rfl⟩ : syracuseStep 471253 = 11045) (by norm_num)
theorem B372965 : Blo 247818 372965 := bbase (se 4 (by rfl) ⟨34965, by rfl⟩ : syracuseStep 372965 = 69931) (by norm_num)
theorem B372989 : Blo 247818 372989 := bbase (se 3 (by rfl) ⟨69935, by rfl⟩ : syracuseStep 372989 = 139871) (by norm_num)
theorem B635141 : Blo 247818 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B373013 : Blo 247818 373013 := bbase (se 6 (by rfl) ⟨8742, by rfl⟩ : syracuseStep 373013 = 17485) (by norm_num)
theorem B373037 : Blo 247818 373037 := bbase (se 3 (by rfl) ⟨69944, by rfl⟩ : syracuseStep 373037 = 139889) (by norm_num)
theorem B373061 : Blo 247818 373061 := bbase (se 4 (by rfl) ⟨34974, by rfl⟩ : syracuseStep 373061 = 69949) (by norm_num)
theorem B373085 : Blo 247818 373085 := bbase (se 3 (by rfl) ⟨69953, by rfl⟩ : syracuseStep 373085 = 139907) (by norm_num)
theorem B471413 : Blo 247818 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B373109 : Blo 247818 373109 := bbase (se 5 (by rfl) ⟨17489, by rfl⟩ : syracuseStep 373109 = 34979) (by norm_num)
theorem B373133 : Blo 247818 373133 := bbase (se 3 (by rfl) ⟨69962, by rfl⟩ : syracuseStep 373133 = 139925) (by norm_num)
theorem B373157 : Blo 247818 373157 := bbase (se 4 (by rfl) ⟨34983, by rfl⟩ : syracuseStep 373157 = 69967) (by norm_num)
theorem B373181 : Blo 247818 373181 := bbase (se 3 (by rfl) ⟨69971, by rfl⟩ : syracuseStep 373181 = 139943) (by norm_num)
theorem B373205 : Blo 247818 373205 := bbase (se 7 (by rfl) ⟨4373, by rfl⟩ : syracuseStep 373205 = 8747) (by norm_num)
theorem B373229 : Blo 247818 373229 := bbase (se 3 (by rfl) ⟨69980, by rfl⟩ : syracuseStep 373229 = 139961) (by norm_num)
theorem B471557 : Blo 247818 471557 := bbase (se 4 (by rfl) ⟨44208, by rfl⟩ : syracuseStep 471557 = 88417) (by norm_num)
theorem B373253 : Blo 247818 373253 := bbase (se 4 (by rfl) ⟨34992, by rfl⟩ : syracuseStep 373253 = 69985) (by norm_num)
theorem B373277 : Blo 247818 373277 := bbase (se 3 (by rfl) ⟨69989, by rfl⟩ : syracuseStep 373277 = 139979) (by norm_num)
theorem B373301 : Blo 247818 373301 := bbase (se 5 (by rfl) ⟨17498, by rfl⟩ : syracuseStep 373301 = 34997) (by norm_num)
theorem B373325 : Blo 247818 373325 := bbase (se 3 (by rfl) ⟨69998, by rfl⟩ : syracuseStep 373325 = 139997) (by norm_num)
theorem B635485 : Blo 247818 635485 := bbase (se 3 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 635485 = 238307) (by norm_num)
theorem B373349 : Blo 247818 373349 := bbase (se 4 (by rfl) ⟨35001, by rfl⟩ : syracuseStep 373349 = 70003) (by norm_num)
theorem B373373 : Blo 247818 373373 := bbase (se 3 (by rfl) ⟨70007, by rfl⟩ : syracuseStep 373373 = 140015) (by norm_num)
theorem B373397 : Blo 247818 373397 := bbase (se 6 (by rfl) ⟨8751, by rfl⟩ : syracuseStep 373397 = 17503) (by norm_num)
theorem B373421 : Blo 247818 373421 := bbase (se 3 (by rfl) ⟨70016, by rfl⟩ : syracuseStep 373421 = 140033) (by norm_num)
theorem B373445 : Blo 247818 373445 := bbase (se 4 (by rfl) ⟨35010, by rfl⟩ : syracuseStep 373445 = 70021) (by norm_num)
theorem B635597 : Blo 247818 635597 := bbase (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) (by norm_num)
theorem B373469 : Blo 247818 373469 := bbase (se 3 (by rfl) ⟨70025, by rfl⟩ : syracuseStep 373469 = 140051) (by norm_num)
theorem B373493 : Blo 247818 373493 := bbase (se 5 (by rfl) ⟨17507, by rfl⟩ : syracuseStep 373493 = 35015) (by norm_num)
theorem B373517 : Blo 247818 373517 := bbase (se 3 (by rfl) ⟨70034, by rfl⟩ : syracuseStep 373517 = 140069) (by norm_num)
theorem B602909 : Blo 247818 602909 := bbase (se 3 (by rfl) ⟨113045, by rfl⟩ : syracuseStep 602909 = 226091) (by norm_num)
theorem B471845 : Blo 247818 471845 := bbase (se 4 (by rfl) ⟨44235, by rfl⟩ : syracuseStep 471845 = 88471) (by norm_num)
theorem B373541 : Blo 247818 373541 := bbase (se 4 (by rfl) ⟨35019, by rfl⟩ : syracuseStep 373541 = 70039) (by norm_num)
theorem B373565 : Blo 247818 373565 := bbase (se 3 (by rfl) ⟨70043, by rfl⟩ : syracuseStep 373565 = 140087) (by norm_num)
theorem B340805 : Blo 247818 340805 := bbase (se 4 (by rfl) ⟨31950, by rfl⟩ : syracuseStep 340805 = 63901) (by norm_num)
theorem B373589 : Blo 247818 373589 := bbase (se 9 (by rfl) ⟨1094, by rfl⟩ : syracuseStep 373589 = 2189) (by norm_num)
theorem B1192805 : Blo 247818 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B373613 : Blo 247818 373613 := bbase (se 3 (by rfl) ⟨70052, by rfl⟩ : syracuseStep 373613 = 140105) (by norm_num)
theorem B373637 : Blo 247818 373637 := bbase (se 4 (by rfl) ⟨35028, by rfl⟩ : syracuseStep 373637 = 70057) (by norm_num)
theorem B635789 : Blo 247818 635789 := bbase (se 3 (by rfl) ⟨119210, by rfl⟩ : syracuseStep 635789 = 238421) (by norm_num)
theorem B373661 : Blo 247818 373661 := bbase (se 3 (by rfl) ⟨70061, by rfl⟩ : syracuseStep 373661 = 140123) (by norm_num)
theorem B373685 : Blo 247818 373685 := bbase (se 5 (by rfl) ⟨17516, by rfl⟩ : syracuseStep 373685 = 35033) (by norm_num)
theorem B471997 : Blo 247818 471997 := bbase (se 3 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 471997 = 176999) (by norm_num)
theorem B373709 : Blo 247818 373709 := bbase (se 3 (by rfl) ⟨70070, by rfl⟩ : syracuseStep 373709 = 140141) (by norm_num)
theorem B373733 : Blo 247818 373733 := bbase (se 4 (by rfl) ⟨35037, by rfl⟩ : syracuseStep 373733 = 70075) (by norm_num)
theorem B373757 : Blo 247818 373757 := bbase (se 3 (by rfl) ⟨70079, by rfl⟩ : syracuseStep 373757 = 140159) (by norm_num)
theorem B373781 : Blo 247818 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B373805 : Blo 247818 373805 := bbase (se 3 (by rfl) ⟨70088, by rfl⟩ : syracuseStep 373805 = 140177) (by norm_num)
theorem B537653 : Blo 247818 537653 := bbase (se 5 (by rfl) ⟨25202, by rfl⟩ : syracuseStep 537653 = 50405) (by norm_num)
theorem B603197 : Blo 247818 603197 := bbase (se 3 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 603197 = 226199) (by norm_num)
theorem B373829 : Blo 247818 373829 := bbase (se 4 (by rfl) ⟨35046, by rfl⟩ : syracuseStep 373829 = 70093) (by norm_num)
theorem B373853 : Blo 247818 373853 := bbase (se 3 (by rfl) ⟨70097, by rfl⟩ : syracuseStep 373853 = 140195) (by norm_num)
theorem B373877 : Blo 247818 373877 := bbase (se 5 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 373877 = 35051) (by norm_num)
theorem B275581 : Blo 247818 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B504973 : Blo 247818 504973 := bbase (se 3 (by rfl) ⟨94682, by rfl⟩ : syracuseStep 504973 = 189365) (by norm_num)
theorem B373901 : Blo 247818 373901 := bbase (se 3 (by rfl) ⟨70106, by rfl⟩ : syracuseStep 373901 = 140213) (by norm_num)
theorem B373925 : Blo 247818 373925 := bbase (se 4 (by rfl) ⟨35055, by rfl⟩ : syracuseStep 373925 = 70111) (by norm_num)
theorem B373949 : Blo 247818 373949 := bbase (se 3 (by rfl) ⟨70115, by rfl⟩ : syracuseStep 373949 = 140231) (by norm_num)
theorem B537797 : Blo 247818 537797 := bbase (se 4 (by rfl) ⟨50418, by rfl⟩ : syracuseStep 537797 = 100837) (by norm_num)
theorem B373973 : Blo 247818 373973 := bbase (se 7 (by rfl) ⟨4382, by rfl⟩ : syracuseStep 373973 = 8765) (by norm_num)
theorem B636133 : Blo 247818 636133 := bbase (se 4 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 636133 = 119275) (by norm_num)
theorem B472301 : Blo 247818 472301 := bbase (se 3 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 472301 = 177113) (by norm_num)
theorem B373997 : Blo 247818 373997 := bbase (se 3 (by rfl) ⟨70124, by rfl⟩ : syracuseStep 373997 = 140249) (by norm_num)
theorem B374021 : Blo 247818 374021 := bbase (se 4 (by rfl) ⟨35064, by rfl⟩ : syracuseStep 374021 = 70129) (by norm_num)
theorem B374045 : Blo 247818 374045 := bbase (se 3 (by rfl) ⟨70133, by rfl⟩ : syracuseStep 374045 = 140267) (by norm_num)
theorem B374069 : Blo 247818 374069 := bbase (se 5 (by rfl) ⟨17534, by rfl⟩ : syracuseStep 374069 = 35069) (by norm_num)
theorem B374093 : Blo 247818 374093 := bbase (se 3 (by rfl) ⟨70142, by rfl⟩ : syracuseStep 374093 = 140285) (by norm_num)
theorem B636245 : Blo 247818 636245 := bbase (se 13 (by rfl) ⟨116, by rfl⟩ : syracuseStep 636245 = 233) (by norm_num)
theorem B374117 : Blo 247818 374117 := bbase (se 4 (by rfl) ⟨35073, by rfl⟩ : syracuseStep 374117 = 70147) (by norm_num)
theorem B374141 : Blo 247818 374141 := bbase (se 3 (by rfl) ⟨70151, by rfl⟩ : syracuseStep 374141 = 140303) (by norm_num)
theorem B1258901 : Blo 247818 1258901 := bbase (se 6 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 1258901 = 59011) (by norm_num)
theorem B374165 : Blo 247818 374165 := bbase (se 6 (by rfl) ⟨8769, by rfl⟩ : syracuseStep 374165 = 17539) (by norm_num)
theorem B374189 : Blo 247818 374189 := bbase (se 3 (by rfl) ⟨70160, by rfl⟩ : syracuseStep 374189 = 140321) (by norm_num)
theorem B374213 : Blo 247818 374213 := bbase (se 4 (by rfl) ⟨35082, by rfl⟩ : syracuseStep 374213 = 70165) (by norm_num)
theorem B374237 : Blo 247818 374237 := bbase (se 3 (by rfl) ⟨70169, by rfl⟩ : syracuseStep 374237 = 140339) (by norm_num)
theorem B374261 : Blo 247818 374261 := bbase (se 5 (by rfl) ⟨17543, by rfl⟩ : syracuseStep 374261 = 35087) (by norm_num)
theorem B374285 : Blo 247818 374285 := bbase (se 3 (by rfl) ⟨70178, by rfl⟩ : syracuseStep 374285 = 140357) (by norm_num)
theorem B636437 : Blo 247818 636437 := bbase (se 6 (by rfl) ⟨14916, by rfl⟩ : syracuseStep 636437 = 29833) (by norm_num)
theorem B374309 : Blo 247818 374309 := bbase (se 4 (by rfl) ⟨35091, by rfl⟩ : syracuseStep 374309 = 70183) (by norm_num)
theorem B374333 : Blo 247818 374333 := bbase (se 3 (by rfl) ⟨70187, by rfl⟩ : syracuseStep 374333 = 140375) (by norm_num)
theorem B374357 : Blo 247818 374357 := bbase (se 8 (by rfl) ⟨2193, by rfl⟩ : syracuseStep 374357 = 4387) (by norm_num)
theorem B374381 : Blo 247818 374381 := bbase (se 3 (by rfl) ⟨70196, by rfl⟩ : syracuseStep 374381 = 140393) (by norm_num)
theorem B374405 : Blo 247818 374405 := bbase (se 4 (by rfl) ⟨35100, by rfl⟩ : syracuseStep 374405 = 70201) (by norm_num)
theorem B374429 : Blo 247818 374429 := bbase (se 3 (by rfl) ⟨70205, by rfl⟩ : syracuseStep 374429 = 140411) (by norm_num)
theorem B374453 : Blo 247818 374453 := bbase (se 5 (by rfl) ⟨17552, by rfl⟩ : syracuseStep 374453 = 35105) (by norm_num)
theorem B374477 : Blo 247818 374477 := bbase (se 3 (by rfl) ⟨70214, by rfl⟩ : syracuseStep 374477 = 140429) (by norm_num)
theorem B374501 : Blo 247818 374501 := bbase (se 4 (by rfl) ⟨35109, by rfl⟩ : syracuseStep 374501 = 70219) (by norm_num)
theorem B374525 : Blo 247818 374525 := bbase (se 3 (by rfl) ⟨70223, by rfl⟩ : syracuseStep 374525 = 140447) (by norm_num)
theorem B374549 : Blo 247818 374549 := bbase (se 6 (by rfl) ⟨8778, by rfl⟩ : syracuseStep 374549 = 17557) (by norm_num)
theorem B800533 : Blo 247818 800533 := bbase (se 6 (by rfl) ⟨18762, by rfl⟩ : syracuseStep 800533 = 37525) (by norm_num)
theorem B374573 : Blo 247818 374573 := bbase (se 3 (by rfl) ⟨70232, by rfl⟩ : syracuseStep 374573 = 140465) (by norm_num)
theorem B374597 : Blo 247818 374597 := bbase (se 4 (by rfl) ⟨35118, by rfl⟩ : syracuseStep 374597 = 70237) (by norm_num)
theorem B800597 : Blo 247818 800597 := bbase (se 9 (by rfl) ⟨2345, by rfl⟩ : syracuseStep 800597 = 4691) (by norm_num)
theorem B374621 : Blo 247818 374621 := bbase (se 3 (by rfl) ⟨70241, by rfl⟩ : syracuseStep 374621 = 140483) (by norm_num)
theorem B636781 : Blo 247818 636781 := bbase (se 3 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 636781 = 238793) (by norm_num)
theorem B374645 : Blo 247818 374645 := bbase (se 5 (by rfl) ⟨17561, by rfl⟩ : syracuseStep 374645 = 35123) (by norm_num)
theorem B374669 : Blo 247818 374669 := bbase (se 3 (by rfl) ⟨70250, by rfl⟩ : syracuseStep 374669 = 140501) (by norm_num)
theorem B374693 : Blo 247818 374693 := bbase (se 4 (by rfl) ⟨35127, by rfl⟩ : syracuseStep 374693 = 70255) (by norm_num)
theorem B374717 : Blo 247818 374717 := bbase (se 3 (by rfl) ⟨70259, by rfl⟩ : syracuseStep 374717 = 140519) (by norm_num)
theorem B374741 : Blo 247818 374741 := bbase (se 7 (by rfl) ⟨4391, by rfl⟩ : syracuseStep 374741 = 8783) (by norm_num)
theorem B636893 : Blo 247818 636893 := bbase (se 3 (by rfl) ⟨119417, by rfl⟩ : syracuseStep 636893 = 238835) (by norm_num)
theorem B473053 : Blo 247818 473053 := bbase (se 3 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 473053 = 177395) (by norm_num)
theorem B374765 : Blo 247818 374765 := bbase (se 3 (by rfl) ⟨70268, by rfl⟩ : syracuseStep 374765 = 140537) (by norm_num)
theorem B374789 : Blo 247818 374789 := bbase (se 4 (by rfl) ⟨35136, by rfl⟩ : syracuseStep 374789 = 70273) (by norm_num)
theorem B374813 : Blo 247818 374813 := bbase (se 3 (by rfl) ⟨70277, by rfl⟩ : syracuseStep 374813 = 140555) (by norm_num)
theorem B374837 : Blo 247818 374837 := bbase (se 5 (by rfl) ⟨17570, by rfl⟩ : syracuseStep 374837 = 35141) (by norm_num)
theorem B374861 : Blo 247818 374861 := bbase (se 3 (by rfl) ⟨70286, by rfl⟩ : syracuseStep 374861 = 140573) (by norm_num)
theorem B374885 : Blo 247818 374885 := bbase (se 4 (by rfl) ⟨35145, by rfl⟩ : syracuseStep 374885 = 70291) (by norm_num)
theorem B473197 : Blo 247818 473197 := bbase (se 3 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 473197 = 177449) (by norm_num)
theorem B374909 : Blo 247818 374909 := bbase (se 3 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 374909 = 140591) (by norm_num)
theorem B374933 : Blo 247818 374933 := bbase (se 6 (by rfl) ⟨8787, by rfl⟩ : syracuseStep 374933 = 17575) (by norm_num)
theorem B637085 : Blo 247818 637085 := bbase (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) (by norm_num)
theorem B374957 : Blo 247818 374957 := bbase (se 3 (by rfl) ⟨70304, by rfl⟩ : syracuseStep 374957 = 140609) (by norm_num)
theorem B374981 : Blo 247818 374981 := bbase (se 4 (by rfl) ⟨35154, by rfl⟩ : syracuseStep 374981 = 70309) (by norm_num)
theorem B2865365 : Blo 247818 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B506069 : Blo 247818 506069 := bbase (se 7 (by rfl) ⟨5930, by rfl⟩ : syracuseStep 506069 = 11861) (by norm_num)
theorem B375005 : Blo 247818 375005 := bbase (se 3 (by rfl) ⟨70313, by rfl⟩ : syracuseStep 375005 = 140627) (by norm_num)
theorem B375029 : Blo 247818 375029 := bbase (se 5 (by rfl) ⟨17579, by rfl⟩ : syracuseStep 375029 = 35159) (by norm_num)
theorem B473357 : Blo 247818 473357 := bbase (se 3 (by rfl) ⟨88754, by rfl⟩ : syracuseStep 473357 = 177509) (by norm_num)
theorem B375053 : Blo 247818 375053 := bbase (se 3 (by rfl) ⟨70322, by rfl⟩ : syracuseStep 375053 = 140645) (by norm_num)
theorem B375077 : Blo 247818 375077 := bbase (se 4 (by rfl) ⟨35163, by rfl⟩ : syracuseStep 375077 = 70327) (by norm_num)
theorem B375101 : Blo 247818 375101 := bbase (se 3 (by rfl) ⟨70331, by rfl⟩ : syracuseStep 375101 = 140663) (by norm_num)
theorem B375125 : Blo 247818 375125 := bbase (se 10 (by rfl) ⟨549, by rfl⟩ : syracuseStep 375125 = 1099) (by norm_num)
theorem B375149 : Blo 247818 375149 := bbase (se 3 (by rfl) ⟨70340, by rfl⟩ : syracuseStep 375149 = 140681) (by norm_num)
theorem B375173 : Blo 247818 375173 := bbase (se 4 (by rfl) ⟨35172, by rfl⟩ : syracuseStep 375173 = 70345) (by norm_num)
theorem B473501 : Blo 247818 473501 := bbase (se 3 (by rfl) ⟨88781, by rfl⟩ : syracuseStep 473501 = 177563) (by norm_num)
theorem B375197 : Blo 247818 375197 := bbase (se 3 (by rfl) ⟨70349, by rfl⟩ : syracuseStep 375197 = 140699) (by norm_num)
theorem B375221 : Blo 247818 375221 := bbase (se 5 (by rfl) ⟨17588, by rfl⟩ : syracuseStep 375221 = 35177) (by norm_num)
theorem B375245 : Blo 247818 375245 := bbase (se 3 (by rfl) ⟨70358, by rfl⟩ : syracuseStep 375245 = 140717) (by norm_num)
theorem B375269 : Blo 247818 375269 := bbase (se 4 (by rfl) ⟨35181, by rfl⟩ : syracuseStep 375269 = 70363) (by norm_num)
theorem B375293 : Blo 247818 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B375317 : Blo 247818 375317 := bbase (se 6 (by rfl) ⟨8796, by rfl⟩ : syracuseStep 375317 = 17593) (by norm_num)
theorem B375341 : Blo 247818 375341 := bbase (se 3 (by rfl) ⟨70376, by rfl⟩ : syracuseStep 375341 = 140753) (by norm_num)
theorem B375365 : Blo 247818 375365 := bbase (se 4 (by rfl) ⟨35190, by rfl⟩ : syracuseStep 375365 = 70381) (by norm_num)
theorem B375389 : Blo 247818 375389 := bbase (se 3 (by rfl) ⟨70385, by rfl⟩ : syracuseStep 375389 = 140771) (by norm_num)
theorem B637541 : Blo 247818 637541 := bbase (se 4 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 637541 = 119539) (by norm_num)
theorem B375413 : Blo 247818 375413 := bbase (se 5 (by rfl) ⟨17597, by rfl⟩ : syracuseStep 375413 = 35195) (by norm_num)
theorem B375437 : Blo 247818 375437 := bbase (se 3 (by rfl) ⟨70394, by rfl⟩ : syracuseStep 375437 = 140789) (by norm_num)
theorem B1260197 : Blo 247818 1260197 := bbase (se 4 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 1260197 = 236287) (by norm_num)
theorem B375461 : Blo 247818 375461 := bbase (se 4 (by rfl) ⟨35199, by rfl⟩ : syracuseStep 375461 = 70399) (by norm_num)
theorem B473789 : Blo 247818 473789 := bbase (se 3 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 473789 = 177671) (by norm_num)
theorem B375485 : Blo 247818 375485 := bbase (se 3 (by rfl) ⟨70403, by rfl⟩ : syracuseStep 375485 = 140807) (by norm_num)
theorem B375509 : Blo 247818 375509 := bbase (se 7 (by rfl) ⟨4400, by rfl⟩ : syracuseStep 375509 = 8801) (by norm_num)
theorem B375533 : Blo 247818 375533 := bbase (se 3 (by rfl) ⟨70412, by rfl⟩ : syracuseStep 375533 = 140825) (by norm_num)
theorem B375557 : Blo 247818 375557 := bbase (se 4 (by rfl) ⟨35208, by rfl⟩ : syracuseStep 375557 = 70417) (by norm_num)
theorem B375581 : Blo 247818 375581 := bbase (se 3 (by rfl) ⟨70421, by rfl⟩ : syracuseStep 375581 = 140843) (by norm_num)
theorem B637733 : Blo 247818 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B375605 : Blo 247818 375605 := bbase (se 5 (by rfl) ⟨17606, by rfl⟩ : syracuseStep 375605 = 35213) (by norm_num)
theorem B1194821 : Blo 247818 1194821 := bbase (se 4 (by rfl) ⟨112014, by rfl⟩ : syracuseStep 1194821 = 224029) (by norm_num)
theorem B375629 : Blo 247818 375629 := bbase (se 3 (by rfl) ⟨70430, by rfl⟩ : syracuseStep 375629 = 140861) (by norm_num)
theorem B473941 : Blo 247818 473941 := bbase (se 9 (by rfl) ⟨1388, by rfl⟩ : syracuseStep 473941 = 2777) (by norm_num)
theorem B375653 : Blo 247818 375653 := bbase (se 4 (by rfl) ⟨35217, by rfl⟩ : syracuseStep 375653 = 70435) (by norm_num)
theorem B375677 : Blo 247818 375677 := bbase (se 3 (by rfl) ⟨70439, by rfl⟩ : syracuseStep 375677 = 140879) (by norm_num)
theorem B375701 : Blo 247818 375701 := bbase (se 6 (by rfl) ⟨8805, by rfl⟩ : syracuseStep 375701 = 17611) (by norm_num)
theorem B375725 : Blo 247818 375725 := bbase (se 3 (by rfl) ⟨70448, by rfl⟩ : syracuseStep 375725 = 140897) (by norm_num)
theorem B867269 : Blo 247818 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B375749 : Blo 247818 375749 := bbase (se 4 (by rfl) ⟨35226, by rfl⟩ : syracuseStep 375749 = 70453) (by norm_num)
theorem B1391573 : Blo 247818 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B375773 : Blo 247818 375773 := bbase (se 3 (by rfl) ⟨70457, by rfl⟩ : syracuseStep 375773 = 140915) (by norm_num)
theorem B375797 : Blo 247818 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B1195013 : Blo 247818 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B375821 : Blo 247818 375821 := bbase (se 3 (by rfl) ⟨70466, by rfl⟩ : syracuseStep 375821 = 140933) (by norm_num)
theorem B375845 : Blo 247818 375845 := bbase (se 4 (by rfl) ⟨35235, by rfl⟩ : syracuseStep 375845 = 70471) (by norm_num)
theorem B2407477 : Blo 247818 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B375869 : Blo 247818 375869 := bbase (se 3 (by rfl) ⟨70475, by rfl⟩ : syracuseStep 375869 = 140951) (by norm_num)
theorem B15416405 : Blo 247818 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B375893 : Blo 247818 375893 := bbase (se 8 (by rfl) ⟨2202, by rfl⟩ : syracuseStep 375893 = 4405) (by norm_num)
theorem B375917 : Blo 247818 375917 := bbase (se 3 (by rfl) ⟨70484, by rfl⟩ : syracuseStep 375917 = 140969) (by norm_num)
theorem B474245 : Blo 247818 474245 := bbase (se 4 (by rfl) ⟨44460, by rfl⟩ : syracuseStep 474245 = 88921) (by norm_num)
theorem B375941 : Blo 247818 375941 := bbase (se 4 (by rfl) ⟨35244, by rfl⟩ : syracuseStep 375941 = 70489) (by norm_num)
theorem B375965 : Blo 247818 375965 := bbase (se 3 (by rfl) ⟨70493, by rfl⟩ : syracuseStep 375965 = 140987) (by norm_num)
theorem B375989 : Blo 247818 375989 := bbase (se 5 (by rfl) ⟨17624, by rfl⟩ : syracuseStep 375989 = 35249) (by norm_num)
theorem B376013 : Blo 247818 376013 := bbase (se 3 (by rfl) ⟨70502, by rfl⟩ : syracuseStep 376013 = 141005) (by norm_num)
theorem B376037 : Blo 247818 376037 := bbase (se 4 (by rfl) ⟨35253, by rfl⟩ : syracuseStep 376037 = 70507) (by norm_num)
theorem B376061 : Blo 247818 376061 := bbase (se 3 (by rfl) ⟨70511, by rfl⟩ : syracuseStep 376061 = 141023) (by norm_num)
theorem B376085 : Blo 247818 376085 := bbase (se 6 (by rfl) ⟨8814, by rfl⟩ : syracuseStep 376085 = 17629) (by norm_num)
theorem B376109 : Blo 247818 376109 := bbase (se 3 (by rfl) ⟨70520, by rfl⟩ : syracuseStep 376109 = 141041) (by norm_num)
theorem B507197 : Blo 247818 507197 := bbase (se 3 (by rfl) ⟨95099, by rfl⟩ : syracuseStep 507197 = 190199) (by norm_num)
theorem B376133 : Blo 247818 376133 := bbase (se 4 (by rfl) ⟨35262, by rfl⟩ : syracuseStep 376133 = 70525) (by norm_num)
theorem B376157 : Blo 247818 376157 := bbase (se 3 (by rfl) ⟨70529, by rfl⟩ : syracuseStep 376157 = 141059) (by norm_num)
theorem B376181 : Blo 247818 376181 := bbase (se 5 (by rfl) ⟨17633, by rfl⟩ : syracuseStep 376181 = 35267) (by norm_num)
theorem B376205 : Blo 247818 376205 := bbase (se 3 (by rfl) ⟨70538, by rfl⟩ : syracuseStep 376205 = 141077) (by norm_num)
theorem B376229 : Blo 247818 376229 := bbase (se 4 (by rfl) ⟨35271, by rfl⟩ : syracuseStep 376229 = 70543) (by norm_num)
theorem B376253 : Blo 247818 376253 := bbase (se 3 (by rfl) ⟨70547, by rfl⟩ : syracuseStep 376253 = 141095) (by norm_num)
theorem B376277 : Blo 247818 376277 := bbase (se 7 (by rfl) ⟨4409, by rfl⟩ : syracuseStep 376277 = 8819) (by norm_num)
theorem B376301 : Blo 247818 376301 := bbase (se 3 (by rfl) ⟨70556, by rfl⟩ : syracuseStep 376301 = 141113) (by norm_num)
theorem B376325 : Blo 247818 376325 := bbase (se 4 (by rfl) ⟨35280, by rfl⟩ : syracuseStep 376325 = 70561) (by norm_num)
theorem B376349 : Blo 247818 376349 := bbase (se 3 (by rfl) ⟨70565, by rfl⟩ : syracuseStep 376349 = 141131) (by norm_num)
theorem B376373 : Blo 247818 376373 := bbase (se 5 (by rfl) ⟨17642, by rfl⟩ : syracuseStep 376373 = 35285) (by norm_num)
theorem B638533 : Blo 247818 638533 := bbase (se 4 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 638533 = 119725) (by norm_num)
theorem B376397 : Blo 247818 376397 := bbase (se 3 (by rfl) ⟨70574, by rfl⟩ : syracuseStep 376397 = 141149) (by norm_num)
theorem B376421 : Blo 247818 376421 := bbase (se 4 (by rfl) ⟨35289, by rfl⟩ : syracuseStep 376421 = 70579) (by norm_num)
theorem B376445 : Blo 247818 376445 := bbase (se 3 (by rfl) ⟨70583, by rfl⟩ : syracuseStep 376445 = 141167) (by norm_num)
theorem B376469 : Blo 247818 376469 := bbase (se 6 (by rfl) ⟨8823, by rfl⟩ : syracuseStep 376469 = 17647) (by norm_num)
theorem B376493 : Blo 247818 376493 := bbase (se 3 (by rfl) ⟨70592, by rfl⟩ : syracuseStep 376493 = 141185) (by norm_num)
theorem B376517 : Blo 247818 376517 := bbase (se 4 (by rfl) ⟨35298, by rfl⟩ : syracuseStep 376517 = 70597) (by norm_num)
theorem B376541 : Blo 247818 376541 := bbase (se 3 (by rfl) ⟨70601, by rfl⟩ : syracuseStep 376541 = 141203) (by norm_num)
theorem B376565 : Blo 247818 376565 := bbase (se 5 (by rfl) ⟨17651, by rfl⟩ : syracuseStep 376565 = 35303) (by norm_num)
theorem B376589 : Blo 247818 376589 := bbase (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) (by norm_num)
theorem B376613 : Blo 247818 376613 := bbase (se 4 (by rfl) ⟨35307, by rfl⟩ : syracuseStep 376613 = 70615) (by norm_num)
theorem B376637 : Blo 247818 376637 := bbase (se 3 (by rfl) ⟨70619, by rfl⟩ : syracuseStep 376637 = 141239) (by norm_num)
theorem B376661 : Blo 247818 376661 := bbase (se 9 (by rfl) ⟨1103, by rfl⟩ : syracuseStep 376661 = 2207) (by norm_num)
theorem B376685 : Blo 247818 376685 := bbase (se 3 (by rfl) ⟨70628, by rfl⟩ : syracuseStep 376685 = 141257) (by norm_num)
theorem B474997 : Blo 247818 474997 := bbase (se 5 (by rfl) ⟨22265, by rfl⟩ : syracuseStep 474997 = 44531) (by norm_num)
theorem B376709 : Blo 247818 376709 := bbase (se 4 (by rfl) ⟨35316, by rfl⟩ : syracuseStep 376709 = 70633) (by norm_num)
theorem B376733 : Blo 247818 376733 := bbase (se 3 (by rfl) ⟨70637, by rfl⟩ : syracuseStep 376733 = 141275) (by norm_num)
theorem B1261493 : Blo 247818 1261493 := bbase (se 5 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 1261493 = 118265) (by norm_num)
theorem B376757 : Blo 247818 376757 := bbase (se 5 (by rfl) ⟨17660, by rfl⟩ : syracuseStep 376757 = 35321) (by norm_num)
theorem B376781 : Blo 247818 376781 := bbase (se 3 (by rfl) ⟨70646, by rfl⟩ : syracuseStep 376781 = 141293) (by norm_num)
theorem B1064933 : Blo 247818 1064933 := bbase (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) (by norm_num)
theorem B376805 : Blo 247818 376805 := bbase (se 4 (by rfl) ⟨35325, by rfl⟩ : syracuseStep 376805 = 70651) (by norm_num)
theorem B376829 : Blo 247818 376829 := bbase (se 3 (by rfl) ⟨70655, by rfl⟩ : syracuseStep 376829 = 141311) (by norm_num)
theorem B475141 : Blo 247818 475141 := bbase (se 4 (by rfl) ⟨44544, by rfl⟩ : syracuseStep 475141 = 89089) (by norm_num)
theorem B376853 : Blo 247818 376853 := bbase (se 6 (by rfl) ⟨8832, by rfl⟩ : syracuseStep 376853 = 17665) (by norm_num)
theorem B376877 : Blo 247818 376877 := bbase (se 3 (by rfl) ⟨70664, by rfl⟩ : syracuseStep 376877 = 141329) (by norm_num)
theorem B376901 : Blo 247818 376901 := bbase (se 4 (by rfl) ⟨35334, by rfl⟩ : syracuseStep 376901 = 70669) (by norm_num)
theorem B376925 : Blo 247818 376925 := bbase (se 3 (by rfl) ⟨70673, by rfl⟩ : syracuseStep 376925 = 141347) (by norm_num)
theorem B376949 : Blo 247818 376949 := bbase (se 5 (by rfl) ⟨17669, by rfl⟩ : syracuseStep 376949 = 35339) (by norm_num)
theorem B376973 : Blo 247818 376973 := bbase (se 3 (by rfl) ⟨70682, by rfl⟩ : syracuseStep 376973 = 141365) (by norm_num)
theorem B1130645 : Blo 247818 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B475301 : Blo 247818 475301 := bbase (se 4 (by rfl) ⟨44559, by rfl⟩ : syracuseStep 475301 = 89119) (by norm_num)
theorem B376997 : Blo 247818 376997 := bbase (se 4 (by rfl) ⟨35343, by rfl⟩ : syracuseStep 376997 = 70687) (by norm_num)
theorem B377021 : Blo 247818 377021 := bbase (se 3 (by rfl) ⟨70691, by rfl⟩ : syracuseStep 377021 = 141383) (by norm_num)
theorem B377045 : Blo 247818 377045 := bbase (se 7 (by rfl) ⟨4418, by rfl⟩ : syracuseStep 377045 = 8837) (by norm_num)
theorem B377069 : Blo 247818 377069 := bbase (se 3 (by rfl) ⟨70700, by rfl⟩ : syracuseStep 377069 = 141401) (by norm_num)
theorem B377093 : Blo 247818 377093 := bbase (se 4 (by rfl) ⟨35352, by rfl⟩ : syracuseStep 377093 = 70705) (by norm_num)
theorem B278797 : Blo 247818 278797 := bbase (se 3 (by rfl) ⟨52274, by rfl⟩ : syracuseStep 278797 = 104549) (by norm_num)
theorem B377117 : Blo 247818 377117 := bbase (se 3 (by rfl) ⟨70709, by rfl⟩ : syracuseStep 377117 = 141419) (by norm_num)
theorem B278833 : Blo 247818 278833 := bbase (se 2 (by rfl) ⟨104562, by rfl⟩ : syracuseStep 278833 = 209125) (by norm_num)
theorem B475445 : Blo 247818 475445 := bbase (se 5 (by rfl) ⟨22286, by rfl⟩ : syracuseStep 475445 = 44573) (by norm_num)
theorem B377141 : Blo 247818 377141 := bbase (se 5 (by rfl) ⟨17678, by rfl⟩ : syracuseStep 377141 = 35357) (by norm_num)
theorem B377165 : Blo 247818 377165 := bbase (se 3 (by rfl) ⟨70718, by rfl⟩ : syracuseStep 377165 = 141437) (by norm_num)
theorem B278869 : Blo 247818 278869 := bbase (se 10 (by rfl) ⟨408, by rfl⟩ : syracuseStep 278869 = 817) (by norm_num)
theorem B377189 : Blo 247818 377189 := bbase (se 4 (by rfl) ⟨35361, by rfl⟩ : syracuseStep 377189 = 70723) (by norm_num)
theorem B278905 : Blo 247818 278905 := bbase (se 2 (by rfl) ⟨104589, by rfl⟩ : syracuseStep 278905 = 209179) (by norm_num)
theorem B377213 : Blo 247818 377213 := bbase (se 3 (by rfl) ⟨70727, by rfl⟩ : syracuseStep 377213 = 141455) (by norm_num)
theorem B377237 : Blo 247818 377237 := bbase (se 6 (by rfl) ⟨8841, by rfl⟩ : syracuseStep 377237 = 17683) (by norm_num)
theorem B278941 : Blo 247818 278941 := bbase (se 3 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 278941 = 104603) (by norm_num)
theorem B377261 : Blo 247818 377261 := bbase (se 3 (by rfl) ⟨70736, by rfl⟩ : syracuseStep 377261 = 141473) (by norm_num)
theorem B278977 : Blo 247818 278977 := bbase (se 2 (by rfl) ⟨104616, by rfl⟩ : syracuseStep 278977 = 209233) (by norm_num)
theorem B377285 : Blo 247818 377285 := bbase (se 4 (by rfl) ⟨35370, by rfl⟩ : syracuseStep 377285 = 70741) (by norm_num)
theorem B4047317 : Blo 247818 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B377309 : Blo 247818 377309 := bbase (se 3 (by rfl) ⟨70745, by rfl⟩ : syracuseStep 377309 = 141491) (by norm_num)
theorem B279013 : Blo 247818 279013 := bbase (se 4 (by rfl) ⟨26157, by rfl⟩ : syracuseStep 279013 = 52315) (by norm_num)
theorem B377333 : Blo 247818 377333 := bbase (se 5 (by rfl) ⟨17687, by rfl⟩ : syracuseStep 377333 = 35375) (by norm_num)
theorem B279049 : Blo 247818 279049 := bbase (se 2 (by rfl) ⟨104643, by rfl⟩ : syracuseStep 279049 = 209287) (by norm_num)
theorem B377357 : Blo 247818 377357 := bbase (se 3 (by rfl) ⟨70754, by rfl⟩ : syracuseStep 377357 = 141509) (by norm_num)
theorem B377381 : Blo 247818 377381 := bbase (se 4 (by rfl) ⟨35379, by rfl⟩ : syracuseStep 377381 = 70759) (by norm_num)
theorem B279085 : Blo 247818 279085 := bbase (se 3 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 279085 = 104657) (by norm_num)
theorem B1589813 : Blo 247818 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B377405 : Blo 247818 377405 := bbase (se 3 (by rfl) ⟨70763, by rfl⟩ : syracuseStep 377405 = 141527) (by norm_num)
theorem B279121 : Blo 247818 279121 := bbase (se 2 (by rfl) ⟨104670, by rfl⟩ : syracuseStep 279121 = 209341) (by norm_num)
theorem B475733 : Blo 247818 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B377429 : Blo 247818 377429 := bbase (se 8 (by rfl) ⟨2211, by rfl⟩ : syracuseStep 377429 = 4423) (by norm_num)
theorem B377453 : Blo 247818 377453 := bbase (se 3 (by rfl) ⟨70772, by rfl⟩ : syracuseStep 377453 = 141545) (by norm_num)
theorem B279157 : Blo 247818 279157 := bbase (se 5 (by rfl) ⟨13085, by rfl⟩ : syracuseStep 279157 = 26171) (by norm_num)
theorem B377477 : Blo 247818 377477 := bbase (se 4 (by rfl) ⟨35388, by rfl⟩ : syracuseStep 377477 = 70777) (by norm_num)
theorem B279193 : Blo 247818 279193 := bbase (se 2 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 279193 = 209395) (by norm_num)
theorem B377501 : Blo 247818 377501 := bbase (se 3 (by rfl) ⟨70781, by rfl⟩ : syracuseStep 377501 = 141563) (by norm_num)
theorem B377525 : Blo 247818 377525 := bbase (se 5 (by rfl) ⟨17696, by rfl⟩ : syracuseStep 377525 = 35393) (by norm_num)
theorem B279229 : Blo 247818 279229 := bbase (se 3 (by rfl) ⟨52355, by rfl⟩ : syracuseStep 279229 = 104711) (by norm_num)
theorem B377549 : Blo 247818 377549 := bbase (se 3 (by rfl) ⟨70790, by rfl⟩ : syracuseStep 377549 = 141581) (by norm_num)
theorem B541397 : Blo 247818 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B279265 : Blo 247818 279265 := bbase (se 2 (by rfl) ⟨104724, by rfl⟩ : syracuseStep 279265 = 209449) (by norm_num)
theorem B377573 : Blo 247818 377573 := bbase (se 4 (by rfl) ⟨35397, by rfl⟩ : syracuseStep 377573 = 70795) (by norm_num)
theorem B475885 : Blo 247818 475885 := bbase (se 3 (by rfl) ⟨89228, by rfl⟩ : syracuseStep 475885 = 178457) (by norm_num)
theorem B377597 : Blo 247818 377597 := bbase (se 3 (by rfl) ⟨70799, by rfl⟩ : syracuseStep 377597 = 141599) (by norm_num)
theorem B279301 : Blo 247818 279301 := bbase (se 4 (by rfl) ⟨26184, by rfl⟩ : syracuseStep 279301 = 52369) (by norm_num)
theorem B377621 : Blo 247818 377621 := bbase (se 6 (by rfl) ⟨8850, by rfl⟩ : syracuseStep 377621 = 17701) (by norm_num)
theorem B803621 : Blo 247818 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B279337 : Blo 247818 279337 := bbase (se 2 (by rfl) ⟨104751, by rfl⟩ : syracuseStep 279337 = 209503) (by norm_num)
theorem B377645 : Blo 247818 377645 := bbase (se 3 (by rfl) ⟨70808, by rfl⟩ : syracuseStep 377645 = 141617) (by norm_num)
theorem B836405 : Blo 247818 836405 := bbase (se 5 (by rfl) ⟨39206, by rfl⟩ : syracuseStep 836405 = 78413) (by norm_num)
theorem B344893 : Blo 247818 344893 := bbase (se 3 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 344893 = 129335) (by norm_num)
theorem B377669 : Blo 247818 377669 := bbase (se 4 (by rfl) ⟨35406, by rfl⟩ : syracuseStep 377669 = 70813) (by norm_num)
theorem B279373 : Blo 247818 279373 := bbase (se 3 (by rfl) ⟨52382, by rfl⟩ : syracuseStep 279373 = 104765) (by norm_num)
theorem B377693 : Blo 247818 377693 := bbase (se 3 (by rfl) ⟨70817, by rfl⟩ : syracuseStep 377693 = 141635) (by norm_num)
theorem B279409 : Blo 247818 279409 := bbase (se 2 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 279409 = 209557) (by norm_num)
theorem B377717 : Blo 247818 377717 := bbase (se 5 (by rfl) ⟨17705, by rfl⟩ : syracuseStep 377717 = 35411) (by norm_num)
theorem B279445 : Blo 247818 279445 := bbase (se 6 (by rfl) ⟨6549, by rfl⟩ : syracuseStep 279445 = 13099) (by norm_num)
theorem B279481 : Blo 247818 279481 := bbase (se 2 (by rfl) ⟨104805, by rfl⟩ : syracuseStep 279481 = 209611) (by norm_num)
theorem B279517 : Blo 247818 279517 := bbase (se 3 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 279517 = 104819) (by norm_num)
theorem B279553 : Blo 247818 279553 := bbase (se 2 (by rfl) ⟨104832, by rfl⟩ : syracuseStep 279553 = 209665) (by norm_num)
theorem B476189 : Blo 247818 476189 := bbase (se 3 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 476189 = 178571) (by norm_num)
theorem B279589 : Blo 247818 279589 := bbase (se 4 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 279589 = 52423) (by norm_num)
theorem B574517 : Blo 247818 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B1197109 : Blo 247818 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B508997 : Blo 247818 508997 := bbase (se 4 (by rfl) ⟨47718, by rfl⟩ : syracuseStep 508997 = 95437) (by norm_num)
theorem B279625 : Blo 247818 279625 := bbase (se 2 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 279625 = 209719) (by norm_num)
theorem B1426517 : Blo 247818 1426517 := bbase (se 8 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 1426517 = 16717) (by norm_num)
theorem B279661 : Blo 247818 279661 := bbase (se 3 (by rfl) ⟨52436, by rfl⟩ : syracuseStep 279661 = 104873) (by norm_num)
theorem B279697 : Blo 247818 279697 := bbase (se 2 (by rfl) ⟨104886, by rfl⟩ : syracuseStep 279697 = 209773) (by norm_num)
theorem B279733 : Blo 247818 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B1033397 : Blo 247818 1033397 := bbase (se 5 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 1033397 = 96881) (by norm_num)
theorem B1262789 : Blo 247818 1262789 := bbase (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) (by norm_num)
theorem B279769 : Blo 247818 279769 := bbase (se 2 (by rfl) ⟨104913, by rfl⟩ : syracuseStep 279769 = 209827) (by norm_num)
theorem B836837 : Blo 247818 836837 := bbase (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) (by norm_num)
theorem B279805 : Blo 247818 279805 := bbase (se 3 (by rfl) ⟨52463, by rfl⟩ : syracuseStep 279805 = 104927) (by norm_num)
theorem B279841 : Blo 247818 279841 := bbase (se 2 (by rfl) ⟨104940, by rfl⟩ : syracuseStep 279841 = 209881) (by norm_num)
theorem B279877 : Blo 247818 279877 := bbase (se 4 (by rfl) ⟨26238, by rfl⟩ : syracuseStep 279877 = 52477) (by norm_num)
theorem B279913 : Blo 247818 279913 := bbase (se 2 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 279913 = 209935) (by norm_num)
theorem B640381 : Blo 247818 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B279949 : Blo 247818 279949 := bbase (se 3 (by rfl) ⟨52490, by rfl⟩ : syracuseStep 279949 = 104981) (by norm_num)
theorem B279985 : Blo 247818 279985 := bbase (se 2 (by rfl) ⟨104994, by rfl⟩ : syracuseStep 279985 = 209989) (by norm_num)
theorem B378317 : Blo 247818 378317 := bbase (se 3 (by rfl) ⟨70934, by rfl⟩ : syracuseStep 378317 = 141869) (by norm_num)
theorem B280021 : Blo 247818 280021 := bbase (se 7 (by rfl) ⟨3281, by rfl⟩ : syracuseStep 280021 = 6563) (by norm_num)
theorem B378341 : Blo 247818 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B280057 : Blo 247818 280057 := bbase (se 2 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 280057 = 210043) (by norm_num)
theorem B902677 : Blo 247818 902677 := bbase (se 6 (by rfl) ⟨21156, by rfl⟩ : syracuseStep 902677 = 42313) (by norm_num)
theorem B280093 : Blo 247818 280093 := bbase (se 3 (by rfl) ⟨52517, by rfl⟩ : syracuseStep 280093 = 105035) (by norm_num)
theorem B280129 : Blo 247818 280129 := bbase (se 2 (by rfl) ⟨105048, by rfl⟩ : syracuseStep 280129 = 210097) (by norm_num)
theorem B706117 : Blo 247818 706117 := bbase (se 4 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 706117 = 132397) (by norm_num)
theorem B2475605 : Blo 247818 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B280165 : Blo 247818 280165 := bbase (se 4 (by rfl) ⟨26265, by rfl⟩ : syracuseStep 280165 = 52531) (by norm_num)
theorem B280201 : Blo 247818 280201 := bbase (se 2 (by rfl) ⟨105075, by rfl⟩ : syracuseStep 280201 = 210151) (by norm_num)
theorem B837269 : Blo 247818 837269 := bbase (se 6 (by rfl) ⟨19623, by rfl⟩ : syracuseStep 837269 = 39247) (by norm_num)
theorem B673429 : Blo 247818 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B280237 : Blo 247818 280237 := bbase (se 3 (by rfl) ⟨52544, by rfl⟩ : syracuseStep 280237 = 105089) (by norm_num)
theorem B1525429 : Blo 247818 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B509645 : Blo 247818 509645 := bbase (se 3 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 509645 = 191117) (by norm_num)
theorem B280273 : Blo 247818 280273 := bbase (se 2 (by rfl) ⟨105102, by rfl⟩ : syracuseStep 280273 = 210205) (by norm_num)
theorem B1066709 : Blo 247818 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B280309 : Blo 247818 280309 := bbase (se 5 (by rfl) ⟨13139, by rfl⟩ : syracuseStep 280309 = 26279) (by norm_num)
theorem B476941 : Blo 247818 476941 := bbase (se 3 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 476941 = 178853) (by norm_num)
theorem B280345 : Blo 247818 280345 := bbase (se 2 (by rfl) ⟨105129, by rfl⟩ : syracuseStep 280345 = 210259) (by norm_num)
theorem B280381 : Blo 247818 280381 := bbase (se 3 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 280381 = 105143) (by norm_num)
theorem B280417 : Blo 247818 280417 := bbase (se 2 (by rfl) ⟨105156, by rfl⟩ : syracuseStep 280417 = 210313) (by norm_num)
theorem B280453 : Blo 247818 280453 := bbase (se 4 (by rfl) ⟨26292, by rfl⟩ : syracuseStep 280453 = 52585) (by norm_num)
theorem B477085 : Blo 247818 477085 := bbase (se 3 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 477085 = 178907) (by norm_num)
theorem B280489 : Blo 247818 280489 := bbase (se 2 (by rfl) ⟨105183, by rfl⟩ : syracuseStep 280489 = 210367) (by norm_num)
theorem B280525 : Blo 247818 280525 := bbase (se 3 (by rfl) ⟨52598, by rfl⟩ : syracuseStep 280525 = 105197) (by norm_num)
theorem B1886165 : Blo 247818 1886165 := bbase (se 7 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 1886165 = 44207) (by norm_num)
theorem B280561 : Blo 247818 280561 := bbase (se 2 (by rfl) ⟨105210, by rfl⟩ : syracuseStep 280561 = 210421) (by norm_num)
theorem B280597 : Blo 247818 280597 := bbase (se 6 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 280597 = 13153) (by norm_num)
theorem B280633 : Blo 247818 280633 := bbase (se 2 (by rfl) ⟨105237, by rfl⟩ : syracuseStep 280633 = 210475) (by norm_num)
theorem B477245 : Blo 247818 477245 := bbase (se 3 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 477245 = 178967) (by norm_num)
theorem B837701 : Blo 247818 837701 := bbase (se 4 (by rfl) ⟨78534, by rfl⟩ : syracuseStep 837701 = 157069) (by norm_num)
theorem B280669 : Blo 247818 280669 := bbase (se 3 (by rfl) ⟨52625, by rfl⟩ : syracuseStep 280669 = 105251) (by norm_num)
theorem B280705 : Blo 247818 280705 := bbase (se 2 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 280705 = 210529) (by norm_num)
theorem B280741 : Blo 247818 280741 := bbase (se 4 (by rfl) ⟨26319, by rfl⟩ : syracuseStep 280741 = 52639) (by norm_num)
theorem B280777 : Blo 247818 280777 := bbase (se 2 (by rfl) ⟨105291, by rfl⟩ : syracuseStep 280777 = 210583) (by norm_num)
theorem B477389 : Blo 247818 477389 := bbase (se 3 (by rfl) ⟨89510, by rfl⟩ : syracuseStep 477389 = 179021) (by norm_num)
theorem B280813 : Blo 247818 280813 := bbase (se 3 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 280813 = 105305) (by norm_num)
theorem B280849 : Blo 247818 280849 := bbase (se 2 (by rfl) ⟨105318, by rfl⟩ : syracuseStep 280849 = 210637) (by norm_num)
theorem B280885 : Blo 247818 280885 := bbase (se 5 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 280885 = 26333) (by norm_num)
theorem B280921 : Blo 247818 280921 := bbase (se 2 (by rfl) ⟨105345, by rfl⟩ : syracuseStep 280921 = 210691) (by norm_num)
theorem B280957 : Blo 247818 280957 := bbase (se 3 (by rfl) ⟨52679, by rfl⟩ : syracuseStep 280957 = 105359) (by norm_num)
theorem B313733 : Blo 247818 313733 := bbase (se 4 (by rfl) ⟨29412, by rfl⟩ : syracuseStep 313733 = 58825) (by norm_num)
theorem B280993 : Blo 247818 280993 := bbase (se 2 (by rfl) ⟨105372, by rfl⟩ : syracuseStep 280993 = 210745) (by norm_num)
theorem B313789 : Blo 247818 313789 := bbase (se 3 (by rfl) ⟨58835, by rfl⟩ : syracuseStep 313789 = 117671) (by norm_num)
theorem B281029 : Blo 247818 281029 := bbase (se 4 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 281029 = 52693) (by norm_num)
theorem B1264085 : Blo 247818 1264085 := bbase (se 7 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 1264085 = 29627) (by norm_num)
theorem B281065 : Blo 247818 281065 := bbase (se 2 (by rfl) ⟨105399, by rfl⟩ : syracuseStep 281065 = 210799) (by norm_num)
theorem B477677 : Blo 247818 477677 := bbase (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) (by norm_num)
theorem B838133 : Blo 247818 838133 := bbase (se 5 (by rfl) ⟨39287, by rfl⟩ : syracuseStep 838133 = 78575) (by norm_num)
theorem B281101 : Blo 247818 281101 := bbase (se 3 (by rfl) ⟨52706, by rfl⟩ : syracuseStep 281101 = 105413) (by norm_num)
theorem B313885 : Blo 247818 313885 := bbase (se 3 (by rfl) ⟨58853, by rfl⟩ : syracuseStep 313885 = 117707) (by norm_num)
theorem B281137 : Blo 247818 281137 := bbase (se 2 (by rfl) ⟨105426, by rfl⟩ : syracuseStep 281137 = 210853) (by norm_num)
theorem B281173 : Blo 247818 281173 := bbase (se 8 (by rfl) ⟨1647, by rfl⟩ : syracuseStep 281173 = 3295) (by norm_num)
theorem B281209 : Blo 247818 281209 := bbase (se 2 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 281209 = 210907) (by norm_num)
theorem B477829 : Blo 247818 477829 := bbase (se 4 (by rfl) ⟨44796, by rfl⟩ : syracuseStep 477829 = 89593) (by norm_num)
theorem B707221 : Blo 247818 707221 := bbase (se 6 (by rfl) ⟨16575, by rfl⟩ : syracuseStep 707221 = 33151) (by norm_num)
theorem B281245 : Blo 247818 281245 := bbase (se 3 (by rfl) ⟨52733, by rfl⟩ : syracuseStep 281245 = 105467) (by norm_num)
theorem B1067701 : Blo 247818 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B281281 : Blo 247818 281281 := bbase (se 2 (by rfl) ⟨105480, by rfl⟩ : syracuseStep 281281 = 210961) (by norm_num)
theorem B314057 : Blo 247818 314057 := bbase (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) (by norm_num)
theorem B281317 : Blo 247818 281317 := bbase (se 4 (by rfl) ⟨26373, by rfl⟩ : syracuseStep 281317 = 52747) (by norm_num)
theorem B314113 : Blo 247818 314113 := bbase (se 2 (by rfl) ⟨117792, by rfl⟩ : syracuseStep 314113 = 235585) (by norm_num)
theorem B281353 : Blo 247818 281353 := bbase (se 2 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 281353 = 211015) (by norm_num)
theorem B281389 : Blo 247818 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B281425 : Blo 247818 281425 := bbase (se 2 (by rfl) ⟨105534, by rfl⟩ : syracuseStep 281425 = 211069) (by norm_num)
theorem B314209 : Blo 247818 314209 := bbase (se 2 (by rfl) ⟨117828, by rfl⟩ : syracuseStep 314209 = 235657) (by norm_num)
theorem B281461 : Blo 247818 281461 := bbase (se 5 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 281461 = 26387) (by norm_num)
theorem B281497 : Blo 247818 281497 := bbase (se 2 (by rfl) ⟨105561, by rfl⟩ : syracuseStep 281497 = 211123) (by norm_num)
theorem B838565 : Blo 247818 838565 := bbase (se 4 (by rfl) ⟨78615, by rfl⟩ : syracuseStep 838565 = 157231) (by norm_num)
theorem B281533 : Blo 247818 281533 := bbase (se 3 (by rfl) ⟨52787, by rfl⟩ : syracuseStep 281533 = 105575) (by norm_num)
theorem B2411477 : Blo 247818 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B281569 : Blo 247818 281569 := bbase (se 2 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 281569 = 211177) (by norm_num)
theorem B281605 : Blo 247818 281605 := bbase (se 4 (by rfl) ⟨26400, by rfl⟩ : syracuseStep 281605 = 52801) (by norm_num)
theorem B314381 : Blo 247818 314381 := bbase (se 3 (by rfl) ⟨58946, by rfl⟩ : syracuseStep 314381 = 117893) (by norm_num)
theorem B281641 : Blo 247818 281641 := bbase (se 2 (by rfl) ⟨105615, by rfl⟩ : syracuseStep 281641 = 211231) (by norm_num)
theorem B314437 : Blo 247818 314437 := bbase (se 4 (by rfl) ⟨29478, by rfl⟩ : syracuseStep 314437 = 58957) (by norm_num)
theorem B281677 : Blo 247818 281677 := bbase (se 3 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 281677 = 105629) (by norm_num)
theorem B281713 : Blo 247818 281713 := bbase (se 2 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 281713 = 211285) (by norm_num)
theorem B281749 : Blo 247818 281749 := bbase (se 6 (by rfl) ⟨6603, by rfl⟩ : syracuseStep 281749 = 13207) (by norm_num)
theorem B314533 : Blo 247818 314533 := bbase (se 4 (by rfl) ⟨29487, by rfl⟩ : syracuseStep 314533 = 58975) (by norm_num)
theorem B380069 : Blo 247818 380069 := bbase (se 4 (by rfl) ⟨35631, by rfl⟩ : syracuseStep 380069 = 71263) (by norm_num)
theorem B281785 : Blo 247818 281785 := bbase (se 2 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 281785 = 211339) (by norm_num)
theorem B281821 : Blo 247818 281821 := bbase (se 3 (by rfl) ⟨52841, by rfl⟩ : syracuseStep 281821 = 105683) (by norm_num)
theorem B281857 : Blo 247818 281857 := bbase (se 2 (by rfl) ⟨105696, by rfl⟩ : syracuseStep 281857 = 211393) (by norm_num)
theorem B281893 : Blo 247818 281893 := bbase (se 4 (by rfl) ⟨26427, by rfl⟩ : syracuseStep 281893 = 52855) (by norm_num)
theorem B2149685 : Blo 247818 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B281929 : Blo 247818 281929 := bbase (se 2 (by rfl) ⟨105723, by rfl⟩ : syracuseStep 281929 = 211447) (by norm_num)
theorem B314705 : Blo 247818 314705 := bbase (se 2 (by rfl) ⟨118014, by rfl⟩ : syracuseStep 314705 = 236029) (by norm_num)
theorem B838997 : Blo 247818 838997 := bbase (se 11 (by rfl) ⟨614, by rfl⟩ : syracuseStep 838997 = 1229) (by norm_num)
theorem B281965 : Blo 247818 281965 := bbase (se 3 (by rfl) ⟨52868, by rfl⟩ : syracuseStep 281965 = 105737) (by norm_num)
theorem B314761 : Blo 247818 314761 := bbase (se 2 (by rfl) ⟨118035, by rfl⟩ : syracuseStep 314761 = 236071) (by norm_num)
theorem B282001 : Blo 247818 282001 := bbase (se 2 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 282001 = 211501) (by norm_num)
theorem B282037 : Blo 247818 282037 := bbase (se 5 (by rfl) ⟨13220, by rfl⟩ : syracuseStep 282037 = 26441) (by norm_num)
theorem B282073 : Blo 247818 282073 := bbase (se 2 (by rfl) ⟨105777, by rfl⟩ : syracuseStep 282073 = 211555) (by norm_num)
theorem B314857 : Blo 247818 314857 := bbase (se 2 (by rfl) ⟨118071, by rfl⟩ : syracuseStep 314857 = 236143) (by norm_num)
theorem B282109 : Blo 247818 282109 := bbase (se 3 (by rfl) ⟨52895, by rfl⟩ : syracuseStep 282109 = 105791) (by norm_num)
theorem B282145 : Blo 247818 282145 := bbase (se 2 (by rfl) ⟨105804, by rfl⟩ : syracuseStep 282145 = 211609) (by norm_num)
theorem B282181 : Blo 247818 282181 := bbase (se 4 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 282181 = 52909) (by norm_num)
theorem B609893 : Blo 247818 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B282217 : Blo 247818 282217 := bbase (se 2 (by rfl) ⟨105831, by rfl⟩ : syracuseStep 282217 = 211663) (by norm_num)
theorem B675461 : Blo 247818 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B282253 : Blo 247818 282253 := bbase (se 3 (by rfl) ⟨52922, by rfl⟩ : syracuseStep 282253 = 105845) (by norm_num)
theorem B315029 : Blo 247818 315029 := bbase (se 6 (by rfl) ⟨7383, by rfl⟩ : syracuseStep 315029 = 14767) (by norm_num)
theorem B282289 : Blo 247818 282289 := bbase (se 2 (by rfl) ⟨105858, by rfl⟩ : syracuseStep 282289 = 211717) (by norm_num)
theorem B315085 : Blo 247818 315085 := bbase (se 3 (by rfl) ⟨59078, by rfl⟩ : syracuseStep 315085 = 118157) (by norm_num)
theorem B282325 : Blo 247818 282325 := bbase (se 7 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 282325 = 6617) (by norm_num)
theorem B1265381 : Blo 247818 1265381 := bbase (se 4 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 1265381 = 237259) (by norm_num)
theorem B282361 : Blo 247818 282361 := bbase (se 2 (by rfl) ⟨105885, by rfl⟩ : syracuseStep 282361 = 211771) (by norm_num)
theorem B839429 : Blo 247818 839429 := bbase (se 4 (by rfl) ⟨78696, by rfl⟩ : syracuseStep 839429 = 157393) (by norm_num)
theorem B282397 : Blo 247818 282397 := bbase (se 3 (by rfl) ⟨52949, by rfl⟩ : syracuseStep 282397 = 105899) (by norm_num)
theorem B315181 : Blo 247818 315181 := bbase (se 3 (by rfl) ⟨59096, by rfl⟩ : syracuseStep 315181 = 118193) (by norm_num)
theorem B282433 : Blo 247818 282433 := bbase (se 2 (by rfl) ⟨105912, by rfl⟩ : syracuseStep 282433 = 211825) (by norm_num)
theorem B282469 : Blo 247818 282469 := bbase (se 4 (by rfl) ⟨26481, by rfl⟩ : syracuseStep 282469 = 52963) (by norm_num)
theorem B282505 : Blo 247818 282505 := bbase (se 2 (by rfl) ⟨105939, by rfl⟩ : syracuseStep 282505 = 211879) (by norm_num)
theorem B282541 : Blo 247818 282541 := bbase (se 3 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 282541 = 105953) (by norm_num)
theorem B282577 : Blo 247818 282577 := bbase (se 2 (by rfl) ⟨105966, by rfl⟩ : syracuseStep 282577 = 211933) (by norm_num)
theorem B315353 : Blo 247818 315353 := bbase (se 2 (by rfl) ⟨118257, by rfl⟩ : syracuseStep 315353 = 236515) (by norm_num)
theorem B282613 : Blo 247818 282613 := bbase (se 5 (by rfl) ⟨13247, by rfl⟩ : syracuseStep 282613 = 26495) (by norm_num)
theorem B315409 : Blo 247818 315409 := bbase (se 2 (by rfl) ⟨118278, by rfl⟩ : syracuseStep 315409 = 236557) (by norm_num)
theorem B282649 : Blo 247818 282649 := bbase (se 2 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 282649 = 211987) (by norm_num)
theorem B643133 : Blo 247818 643133 := bbase (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) (by norm_num)
theorem B282685 : Blo 247818 282685 := bbase (se 3 (by rfl) ⟨53003, by rfl⟩ : syracuseStep 282685 = 106007) (by norm_num)
theorem B282721 : Blo 247818 282721 := bbase (se 2 (by rfl) ⟨106020, by rfl⟩ : syracuseStep 282721 = 212041) (by norm_num)
theorem B315505 : Blo 247818 315505 := bbase (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) (by norm_num)
theorem B708725 : Blo 247818 708725 := bbase (se 5 (by rfl) ⟨33221, by rfl⟩ : syracuseStep 708725 = 66443) (by norm_num)
theorem B282757 : Blo 247818 282757 := bbase (se 4 (by rfl) ⟨26508, by rfl⟩ : syracuseStep 282757 = 53017) (by norm_num)
theorem B282793 : Blo 247818 282793 := bbase (se 2 (by rfl) ⟨106047, by rfl⟩ : syracuseStep 282793 = 212095) (by norm_num)
theorem B839861 : Blo 247818 839861 := bbase (se 5 (by rfl) ⟨39368, by rfl⟩ : syracuseStep 839861 = 78737) (by norm_num)
theorem B282829 : Blo 247818 282829 := bbase (se 3 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 282829 = 106061) (by norm_num)
theorem B282865 : Blo 247818 282865 := bbase (se 2 (by rfl) ⟨106074, by rfl⟩ : syracuseStep 282865 = 212149) (by norm_num)
theorem B446725 : Blo 247818 446725 := bbase (se 4 (by rfl) ⟨41880, by rfl⟩ : syracuseStep 446725 = 83761) (by norm_num)
theorem B282901 : Blo 247818 282901 := bbase (se 6 (by rfl) ⟨6630, by rfl⟩ : syracuseStep 282901 = 13261) (by norm_num)
theorem B315677 : Blo 247818 315677 := bbase (se 3 (by rfl) ⟨59189, by rfl⟩ : syracuseStep 315677 = 118379) (by norm_num)
theorem B282937 : Blo 247818 282937 := bbase (se 2 (by rfl) ⟨106101, by rfl⟩ : syracuseStep 282937 = 212203) (by norm_num)
theorem B446789 : Blo 247818 446789 := bbase (se 4 (by rfl) ⟨41886, by rfl⟩ : syracuseStep 446789 = 83773) (by norm_num)
theorem B315733 : Blo 247818 315733 := bbase (se 10 (by rfl) ⟨462, by rfl⟩ : syracuseStep 315733 = 925) (by norm_num)
theorem B282973 : Blo 247818 282973 := bbase (se 3 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 282973 = 106115) (by norm_num)
theorem B905573 : Blo 247818 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B283009 : Blo 247818 283009 := bbase (se 2 (by rfl) ⟨106128, by rfl⟩ : syracuseStep 283009 = 212257) (by norm_num)
theorem B283045 : Blo 247818 283045 := bbase (se 4 (by rfl) ⟨26535, by rfl⟩ : syracuseStep 283045 = 53071) (by norm_num)
theorem B315829 : Blo 247818 315829 := bbase (se 5 (by rfl) ⟨14804, by rfl⟩ : syracuseStep 315829 = 29609) (by norm_num)
theorem B283081 : Blo 247818 283081 := bbase (se 2 (by rfl) ⟨106155, by rfl⟩ : syracuseStep 283081 = 212311) (by norm_num)
theorem B283117 : Blo 247818 283117 := bbase (se 3 (by rfl) ⟨53084, by rfl⟩ : syracuseStep 283117 = 106169) (by norm_num)
theorem B283153 : Blo 247818 283153 := bbase (se 2 (by rfl) ⟨106182, by rfl⟩ : syracuseStep 283153 = 212365) (by norm_num)
theorem B283189 : Blo 247818 283189 := bbase (se 5 (by rfl) ⟨13274, by rfl⟩ : syracuseStep 283189 = 26549) (by norm_num)
theorem B283225 : Blo 247818 283225 := bbase (se 2 (by rfl) ⟨106209, by rfl⟩ : syracuseStep 283225 = 212419) (by norm_num)
theorem B316001 : Blo 247818 316001 := bbase (se 2 (by rfl) ⟨118500, by rfl⟩ : syracuseStep 316001 = 237001) (by norm_num)
theorem B840293 : Blo 247818 840293 := bbase (se 4 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 840293 = 157555) (by norm_num)
theorem B283261 : Blo 247818 283261 := bbase (se 3 (by rfl) ⟨53111, by rfl⟩ : syracuseStep 283261 = 106223) (by norm_num)
theorem B316057 : Blo 247818 316057 := bbase (se 2 (by rfl) ⟨118521, by rfl⟩ : syracuseStep 316057 = 237043) (by norm_num)
theorem B348845 : Blo 247818 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B316153 : Blo 247818 316153 := bbase (se 2 (by rfl) ⟨118557, by rfl⟩ : syracuseStep 316153 = 237115) (by norm_num)
theorem B1201013 : Blo 247818 1201013 := bbase (se 5 (by rfl) ⟨56297, by rfl⟩ : syracuseStep 1201013 = 112595) (by norm_num)
theorem B676757 : Blo 247818 676757 := bbase (se 6 (by rfl) ⟨15861, by rfl⟩ : syracuseStep 676757 = 31723) (by norm_num)
theorem B316325 : Blo 247818 316325 := bbase (se 4 (by rfl) ⟨29655, by rfl⟩ : syracuseStep 316325 = 59311) (by norm_num)
theorem B316381 : Blo 247818 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B1266677 : Blo 247818 1266677 := bbase (se 5 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 1266677 = 118751) (by norm_num)
theorem B283657 : Blo 247818 283657 := bbase (se 2 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 283657 = 212743) (by norm_num)
theorem B840725 : Blo 247818 840725 := bbase (se 6 (by rfl) ⟨19704, by rfl⟩ : syracuseStep 840725 = 39409) (by norm_num)
theorem B316477 : Blo 247818 316477 := bbase (se 3 (by rfl) ⟨59339, by rfl⟩ : syracuseStep 316477 = 118679) (by norm_num)
theorem B316649 : Blo 247818 316649 := bbase (se 2 (by rfl) ⟨118743, by rfl⟩ : syracuseStep 316649 = 237487) (by norm_num)
theorem B316705 : Blo 247818 316705 := bbase (se 2 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 316705 = 237529) (by norm_num)
theorem B382277 : Blo 247818 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B316801 : Blo 247818 316801 := bbase (se 2 (by rfl) ⟨118800, by rfl⟩ : syracuseStep 316801 = 237601) (by norm_num)
theorem B841157 : Blo 247818 841157 := bbase (se 4 (by rfl) ⟨78858, by rfl⟩ : syracuseStep 841157 = 157717) (by norm_num)
theorem B1136117 : Blo 247818 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B316973 : Blo 247818 316973 := bbase (se 3 (by rfl) ⟨59432, by rfl⟩ : syracuseStep 316973 = 118865) (by norm_num)
theorem B317029 : Blo 247818 317029 := bbase (se 4 (by rfl) ⟨29721, by rfl⟩ : syracuseStep 317029 = 59443) (by norm_num)
theorem B710309 : Blo 247818 710309 := bbase (se 4 (by rfl) ⟨66591, by rfl⟩ : syracuseStep 710309 = 133183) (by norm_num)
theorem B317125 : Blo 247818 317125 := bbase (se 4 (by rfl) ⟨29730, by rfl⟩ : syracuseStep 317125 = 59461) (by norm_num)
theorem B284377 : Blo 247818 284377 := bbase (se 2 (by rfl) ⟨106641, by rfl⟩ : syracuseStep 284377 = 213283) (by norm_num)
theorem B2119445 : Blo 247818 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B317297 : Blo 247818 317297 := bbase (se 2 (by rfl) ⟨118986, by rfl⟩ : syracuseStep 317297 = 237973) (by norm_num)
theorem B841589 : Blo 247818 841589 := bbase (se 5 (by rfl) ⟨39449, by rfl⟩ : syracuseStep 841589 = 78899) (by norm_num)
theorem B317353 : Blo 247818 317353 := bbase (se 2 (by rfl) ⟨119007, by rfl⟩ : syracuseStep 317353 = 238015) (by norm_num)
theorem B317449 : Blo 247818 317449 := bbase (se 2 (by rfl) ⟨119043, by rfl⟩ : syracuseStep 317449 = 238087) (by norm_num)
theorem B252001 : Blo 247818 252001 := bbase (se 2 (by rfl) ⟨94500, by rfl⟩ : syracuseStep 252001 = 189001) (by norm_num)
theorem B3037333 : Blo 247818 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B317621 : Blo 247818 317621 := bbase (se 5 (by rfl) ⟨14888, by rfl⟩ : syracuseStep 317621 = 29777) (by norm_num)
theorem B317677 : Blo 247818 317677 := bbase (se 3 (by rfl) ⟨59564, by rfl⟩ : syracuseStep 317677 = 119129) (by norm_num)
theorem B1267973 : Blo 247818 1267973 := bbase (se 4 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 1267973 = 237745) (by norm_num)
theorem B842021 : Blo 247818 842021 := bbase (se 4 (by rfl) ⟨78939, by rfl⟩ : syracuseStep 842021 = 157879) (by norm_num)
theorem B710981 : Blo 247818 710981 := bbase (se 4 (by rfl) ⟨66654, by rfl⟩ : syracuseStep 710981 = 133309) (by norm_num)
theorem B317773 : Blo 247818 317773 := bbase (se 3 (by rfl) ⟨59582, by rfl⟩ : syracuseStep 317773 = 119165) (by norm_num)
theorem B18340181 : Blo 247818 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B1431989 : Blo 247818 1431989 := bbase (se 5 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 1431989 = 134249) (by norm_num)
theorem B317945 : Blo 247818 317945 := bbase (se 2 (by rfl) ⟨119229, by rfl⟩ : syracuseStep 317945 = 238459) (by norm_num)
theorem B318001 : Blo 247818 318001 := bbase (se 2 (by rfl) ⟨119250, by rfl⟩ : syracuseStep 318001 = 238501) (by norm_num)
theorem B645749 : Blo 247818 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B318097 : Blo 247818 318097 := bbase (se 2 (by rfl) ⟨119286, by rfl⟩ : syracuseStep 318097 = 238573) (by norm_num)
theorem B842453 : Blo 247818 842453 := bbase (se 7 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 842453 = 19745) (by norm_num)
theorem B252649 : Blo 247818 252649 := bbase (se 2 (by rfl) ⟨94743, by rfl⟩ : syracuseStep 252649 = 189487) (by norm_num)
theorem B711413 : Blo 247818 711413 := bbase (se 5 (by rfl) ⟨33347, by rfl⟩ : syracuseStep 711413 = 66695) (by norm_num)
theorem B285481 : Blo 247818 285481 := bbase (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) (by norm_num)
theorem B318269 : Blo 247818 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B908101 : Blo 247818 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B645965 : Blo 247818 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B318325 : Blo 247818 318325 := bbase (se 5 (by rfl) ⟨14921, by rfl⟩ : syracuseStep 318325 = 29843) (by norm_num)
theorem B318421 : Blo 247818 318421 := bbase (se 7 (by rfl) ⟨3731, by rfl⟩ : syracuseStep 318421 = 7463) (by norm_num)
theorem B252941 : Blo 247818 252941 := bbase (se 3 (by rfl) ⟨47426, by rfl⟩ : syracuseStep 252941 = 94853) (by norm_num)
theorem B318593 : Blo 247818 318593 := bbase (se 2 (by rfl) ⟨119472, by rfl⟩ : syracuseStep 318593 = 238945) (by norm_num)
theorem B842885 : Blo 247818 842885 := bbase (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) (by norm_num)
theorem B318649 : Blo 247818 318649 := bbase (se 2 (by rfl) ⟨119493, by rfl⟩ : syracuseStep 318649 = 238987) (by norm_num)
theorem B1137941 : Blo 247818 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B712165 : Blo 247818 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B1269269 : Blo 247818 1269269 := bbase (se 6 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 1269269 = 59497) (by norm_num)
theorem B286237 : Blo 247818 286237 := bbase (se 3 (by rfl) ⟨53669, by rfl⟩ : syracuseStep 286237 = 107339) (by norm_num)
theorem B253477 : Blo 247818 253477 := bbase (se 4 (by rfl) ⟨23763, by rfl⟩ : syracuseStep 253477 = 47527) (by norm_num)
theorem B843317 : Blo 247818 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B1072709 : Blo 247818 1072709 := bbase (se 4 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 1072709 = 201133) (by norm_num)
theorem B253525 : Blo 247818 253525 := bbase (se 8 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 253525 = 2971) (by norm_num)
theorem B286357 : Blo 247818 286357 := bbase (se 6 (by rfl) ⟨6711, by rfl⟩ : syracuseStep 286357 = 13423) (by norm_num)
theorem B1203893 : Blo 247818 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B1072997 : Blo 247818 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B286621 : Blo 247818 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B941989 : Blo 247818 941989 := bbase (se 4 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 941989 = 176623) (by norm_num)
theorem B843749 : Blo 247818 843749 := bbase (se 4 (by rfl) ⟨79101, by rfl⟩ : syracuseStep 843749 = 158203) (by norm_num)
theorem B286913 : Blo 247818 286913 := bbase (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) (by norm_num)
theorem B942293 : Blo 247818 942293 := bbase (se 7 (by rfl) ⟨11042, by rfl⟩ : syracuseStep 942293 = 22085) (by norm_num)
theorem B1138949 : Blo 247818 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B483685 : Blo 247818 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B680293 : Blo 247818 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B844181 : Blo 247818 844181 := bbase (se 6 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 844181 = 39571) (by norm_num)
theorem B418277 : Blo 247818 418277 := bbase (se 4 (by rfl) ⟨39213, by rfl⟩ : syracuseStep 418277 = 78427) (by norm_num)
theorem B1073749 : Blo 247818 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B418405 : Blo 247818 418405 := bbase (se 4 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 418405 = 78451) (by norm_num)
theorem B418493 : Blo 247818 418493 := bbase (se 3 (by rfl) ⟨78467, by rfl⟩ : syracuseStep 418493 = 156935) (by norm_num)
theorem B1270565 : Blo 247818 1270565 := bbase (se 4 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 1270565 = 238231) (by norm_num)
theorem B418621 : Blo 247818 418621 := bbase (se 3 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 418621 = 156983) (by norm_num)
theorem B844613 : Blo 247818 844613 := bbase (se 4 (by rfl) ⟨79182, by rfl⟩ : syracuseStep 844613 = 158365) (by norm_num)
theorem B418709 : Blo 247818 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B353269 : Blo 247818 353269 := bbase (se 5 (by rfl) ⟨16559, by rfl⟩ : syracuseStep 353269 = 33119) (by norm_num)
theorem B418837 : Blo 247818 418837 := bbase (se 6 (by rfl) ⟨9816, by rfl⟩ : syracuseStep 418837 = 19633) (by norm_num)
theorem B484373 : Blo 247818 484373 := bbase (se 6 (by rfl) ⟨11352, by rfl⟩ : syracuseStep 484373 = 22705) (by norm_num)
theorem B418925 : Blo 247818 418925 := bbase (se 3 (by rfl) ⟨78548, by rfl⟩ : syracuseStep 418925 = 157097) (by norm_num)
theorem B419053 : Blo 247818 419053 := bbase (se 3 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 419053 = 157145) (by norm_num)
theorem B845045 : Blo 247818 845045 := bbase (se 5 (by rfl) ⟨39611, by rfl⟩ : syracuseStep 845045 = 79223) (by norm_num)
theorem B1074485 : Blo 247818 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B419141 : Blo 247818 419141 := bbase (se 4 (by rfl) ⟨39294, by rfl⟩ : syracuseStep 419141 = 78589) (by norm_num)
theorem B419269 : Blo 247818 419269 := bbase (se 4 (by rfl) ⟨39306, by rfl⟩ : syracuseStep 419269 = 78613) (by norm_num)
theorem B419357 : Blo 247818 419357 := bbase (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) (by norm_num)
theorem B1893941 : Blo 247818 1893941 := bbase (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) (by norm_num)
theorem B419485 : Blo 247818 419485 := bbase (se 3 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 419485 = 157307) (by norm_num)
theorem B845477 : Blo 247818 845477 := bbase (se 4 (by rfl) ⟨79263, by rfl⟩ : syracuseStep 845477 = 158527) (by norm_num)
theorem B452261 : Blo 247818 452261 := bbase (se 4 (by rfl) ⟨42399, by rfl⟩ : syracuseStep 452261 = 84799) (by norm_num)
theorem B419573 : Blo 247818 419573 := bbase (se 5 (by rfl) ⟨19667, by rfl⟩ : syracuseStep 419573 = 39335) (by norm_num)
theorem B354061 : Blo 247818 354061 := bbase (se 3 (by rfl) ⟨66386, by rfl⟩ : syracuseStep 354061 = 132773) (by norm_num)
theorem B1206085 : Blo 247818 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B419701 : Blo 247818 419701 := bbase (se 5 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 419701 = 39347) (by norm_num)
theorem B419789 : Blo 247818 419789 := bbase (se 3 (by rfl) ⟨78710, by rfl⟩ : syracuseStep 419789 = 157421) (by norm_num)
theorem B1271861 : Blo 247818 1271861 := bbase (se 5 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 1271861 = 119237) (by norm_num)
theorem B419917 : Blo 247818 419917 := bbase (se 3 (by rfl) ⟨78734, by rfl⟩ : syracuseStep 419917 = 157469) (by norm_num)
theorem B682069 : Blo 247818 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B845909 : Blo 247818 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B354397 : Blo 247818 354397 := bbase (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) (by norm_num)
theorem B256129 : Blo 247818 256129 := bbase (se 2 (by rfl) ⟨96048, by rfl⟩ : syracuseStep 256129 = 192097) (by norm_num)
theorem B420005 : Blo 247818 420005 := bbase (se 4 (by rfl) ⟨39375, by rfl⟩ : syracuseStep 420005 = 78751) (by norm_num)
theorem B715013 : Blo 247818 715013 := bbase (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) (by norm_num)
theorem B944405 : Blo 247818 944405 := bbase (se 6 (by rfl) ⟨22134, by rfl⟩ : syracuseStep 944405 = 44269) (by norm_num)
theorem B420133 : Blo 247818 420133 := bbase (se 4 (by rfl) ⟨39387, by rfl⟩ : syracuseStep 420133 = 78775) (by norm_num)
theorem B354613 : Blo 247818 354613 := bbase (se 5 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 354613 = 33245) (by norm_num)
theorem B1272181 : Blo 247818 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B420221 : Blo 247818 420221 := bbase (se 3 (by rfl) ⟨78791, by rfl⟩ : syracuseStep 420221 = 157583) (by norm_num)
theorem B256493 : Blo 247818 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B420349 : Blo 247818 420349 := bbase (se 3 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 420349 = 157631) (by norm_num)
theorem B846341 : Blo 247818 846341 := bbase (se 4 (by rfl) ⟨79344, by rfl⟩ : syracuseStep 846341 = 158689) (by norm_num)
theorem B944693 : Blo 247818 944693 := bbase (se 5 (by rfl) ⟨44282, by rfl⟩ : syracuseStep 944693 = 88565) (by norm_num)
theorem B420437 : Blo 247818 420437 := bbase (se 8 (by rfl) ⟨2463, by rfl⟩ : syracuseStep 420437 = 4927) (by norm_num)
theorem B453205 : Blo 247818 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B354989 : Blo 247818 354989 := bbase (se 3 (by rfl) ⟨66560, by rfl⟩ : syracuseStep 354989 = 133121) (by norm_num)
theorem B420565 : Blo 247818 420565 := bbase (se 7 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 420565 = 9857) (by norm_num)
theorem B420653 : Blo 247818 420653 := bbase (se 3 (by rfl) ⟨78872, by rfl⟩ : syracuseStep 420653 = 157745) (by norm_num)
theorem B420781 : Blo 247818 420781 := bbase (se 3 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 420781 = 157793) (by norm_num)
theorem B846773 : Blo 247818 846773 := bbase (se 5 (by rfl) ⟨39692, by rfl⟩ : syracuseStep 846773 = 79385) (by norm_num)
theorem B420869 : Blo 247818 420869 := bbase (se 4 (by rfl) ⟨39456, by rfl⟩ : syracuseStep 420869 = 78913) (by norm_num)
theorem B1534997 : Blo 247818 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B453709 : Blo 247818 453709 := bbase (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) (by norm_num)
theorem B420997 : Blo 247818 420997 := bbase (se 4 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 420997 = 78937) (by norm_num)
theorem B421085 : Blo 247818 421085 := bbase (se 3 (by rfl) ⟨78953, by rfl⟩ : syracuseStep 421085 = 157907) (by norm_num)
theorem B1273157 : Blo 247818 1273157 := bbase (se 4 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 1273157 = 238717) (by norm_num)
theorem B421213 : Blo 247818 421213 := bbase (se 3 (by rfl) ⟨78977, by rfl⟩ : syracuseStep 421213 = 157955) (by norm_num)
theorem B847205 : Blo 247818 847205 := bbase (se 4 (by rfl) ⟨79425, by rfl⟩ : syracuseStep 847205 = 158851) (by norm_num)
theorem B1076597 : Blo 247818 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B716197 : Blo 247818 716197 := bbase (se 4 (by rfl) ⟨67143, by rfl⟩ : syracuseStep 716197 = 134287) (by norm_num)
theorem B421301 : Blo 247818 421301 := bbase (se 5 (by rfl) ⟨19748, by rfl⟩ : syracuseStep 421301 = 39497) (by norm_num)
theorem B1797653 : Blo 247818 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B421429 : Blo 247818 421429 := bbase (se 5 (by rfl) ⟨19754, by rfl⟩ : syracuseStep 421429 = 39509) (by norm_num)
theorem B716357 : Blo 247818 716357 := bbase (se 4 (by rfl) ⟨67158, by rfl⟩ : syracuseStep 716357 = 134317) (by norm_num)
theorem B421517 : Blo 247818 421517 := bbase (se 3 (by rfl) ⟨79034, by rfl⟩ : syracuseStep 421517 = 158069) (by norm_num)
theorem B945877 : Blo 247818 945877 := bbase (se 7 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 945877 = 22169) (by norm_num)
theorem B257773 : Blo 247818 257773 := bbase (se 3 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 257773 = 96665) (by norm_num)
theorem B421645 : Blo 247818 421645 := bbase (se 3 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 421645 = 158117) (by norm_num)
theorem B847637 : Blo 247818 847637 := bbase (se 6 (by rfl) ⟨19866, by rfl⟩ : syracuseStep 847637 = 39733) (by norm_num)
theorem B716597 : Blo 247818 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B421733 : Blo 247818 421733 := bbase (se 4 (by rfl) ⟨39537, by rfl⟩ : syracuseStep 421733 = 79075) (by norm_num)
theorem B421861 : Blo 247818 421861 := bbase (se 4 (by rfl) ⟨39549, by rfl⟩ : syracuseStep 421861 = 79099) (by norm_num)
theorem B716789 : Blo 247818 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B946181 : Blo 247818 946181 := bbase (se 4 (by rfl) ⟨88704, by rfl⟩ : syracuseStep 946181 = 177409) (by norm_num)
theorem B421949 : Blo 247818 421949 := bbase (se 3 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 421949 = 158231) (by norm_num)
theorem B356413 : Blo 247818 356413 := bbase (se 3 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 356413 = 133655) (by norm_num)
theorem B422077 : Blo 247818 422077 := bbase (se 3 (by rfl) ⟨79139, by rfl⟩ : syracuseStep 422077 = 158279) (by norm_num)
theorem B1142981 : Blo 247818 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B848069 : Blo 247818 848069 := bbase (se 4 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 848069 = 159013) (by norm_num)
theorem B618725 : Blo 247818 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B422165 : Blo 247818 422165 := bbase (se 6 (by rfl) ⟨9894, by rfl⟩ : syracuseStep 422165 = 19789) (by norm_num)
theorem B3207509 : Blo 247818 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B422293 : Blo 247818 422293 := bbase (se 6 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 422293 = 19795) (by norm_num)
theorem B422381 : Blo 247818 422381 := bbase (se 3 (by rfl) ⟨79196, by rfl⟩ : syracuseStep 422381 = 158393) (by norm_num)
theorem B1274453 : Blo 247818 1274453 := bbase (se 8 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 1274453 = 14935) (by norm_num)
theorem B422509 : Blo 247818 422509 := bbase (se 3 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 422509 = 158441) (by norm_num)
theorem B848501 : Blo 247818 848501 := bbase (se 5 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 848501 = 79547) (by norm_num)
theorem B357005 : Blo 247818 357005 := bbase (se 3 (by rfl) ⟨66938, by rfl⟩ : syracuseStep 357005 = 133877) (by norm_num)
theorem B1077941 : Blo 247818 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B422597 : Blo 247818 422597 := bbase (se 4 (by rfl) ⟨39618, by rfl⟩ : syracuseStep 422597 = 79237) (by norm_num)
theorem B357085 : Blo 247818 357085 := bbase (se 3 (by rfl) ⟨66953, by rfl⟩ : syracuseStep 357085 = 133907) (by norm_num)
theorem B455429 : Blo 247818 455429 := bbase (se 4 (by rfl) ⟨42696, by rfl⟩ : syracuseStep 455429 = 85393) (by norm_num)
theorem B422725 : Blo 247818 422725 := bbase (se 4 (by rfl) ⟨39630, by rfl⟩ : syracuseStep 422725 = 79261) (by norm_num)
theorem B357205 : Blo 247818 357205 := bbase (se 9 (by rfl) ⟨1046, by rfl⟩ : syracuseStep 357205 = 2093) (by norm_num)
theorem B422813 : Blo 247818 422813 := bbase (se 3 (by rfl) ⟨79277, by rfl⟩ : syracuseStep 422813 = 158555) (by norm_num)
theorem B357301 : Blo 247818 357301 := bbase (se 5 (by rfl) ⟨16748, by rfl⟩ : syracuseStep 357301 = 33497) (by norm_num)
theorem B422941 : Blo 247818 422941 := bbase (se 3 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 422941 = 158603) (by norm_num)
theorem B848933 : Blo 247818 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B423029 : Blo 247818 423029 := bbase (se 5 (by rfl) ⟨19829, by rfl⟩ : syracuseStep 423029 = 39659) (by norm_num)
theorem B423157 : Blo 247818 423157 := bbase (se 5 (by rfl) ⟨19835, by rfl⟩ : syracuseStep 423157 = 39671) (by norm_num)
theorem B423245 : Blo 247818 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B357797 : Blo 247818 357797 := bbase (se 4 (by rfl) ⟨33543, by rfl⟩ : syracuseStep 357797 = 67087) (by norm_num)
theorem B423373 : Blo 247818 423373 := bbase (se 3 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 423373 = 158765) (by norm_num)
theorem B849365 : Blo 247818 849365 := bbase (se 7 (by rfl) ⟨9953, by rfl⟩ : syracuseStep 849365 = 19907) (by norm_num)
theorem B423461 : Blo 247818 423461 := bbase (se 4 (by rfl) ⟨39699, by rfl⟩ : syracuseStep 423461 = 79399) (by norm_num)
theorem B423589 : Blo 247818 423589 := bbase (se 4 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 423589 = 79423) (by norm_num)
theorem B1210085 : Blo 247818 1210085 := bbase (se 4 (by rfl) ⟨113445, by rfl⟩ : syracuseStep 1210085 = 226891) (by norm_num)
theorem B423677 : Blo 247818 423677 := bbase (se 3 (by rfl) ⟨79439, by rfl⟩ : syracuseStep 423677 = 158879) (by norm_num)
theorem B423805 : Blo 247818 423805 := bbase (se 3 (by rfl) ⟨79463, by rfl⟩ : syracuseStep 423805 = 158927) (by norm_num)
theorem B849797 : Blo 247818 849797 := bbase (se 4 (by rfl) ⟨79668, by rfl⟩ : syracuseStep 849797 = 159337) (by norm_num)
theorem B358349 : Blo 247818 358349 := bbase (se 3 (by rfl) ⟨67190, by rfl⟩ : syracuseStep 358349 = 134381) (by norm_num)
theorem B358357 : Blo 247818 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B423893 : Blo 247818 423893 := bbase (se 7 (by rfl) ⟨4967, by rfl⟩ : syracuseStep 423893 = 9935) (by norm_num)
theorem B948293 : Blo 247818 948293 := bbase (se 4 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 948293 = 177805) (by norm_num)
theorem B424021 : Blo 247818 424021 := bbase (se 8 (by rfl) ⟨2484, by rfl⟩ : syracuseStep 424021 = 4969) (by norm_num)
theorem B424109 : Blo 247818 424109 := bbase (se 3 (by rfl) ⟨79520, by rfl⟩ : syracuseStep 424109 = 159041) (by norm_num)
theorem B424237 : Blo 247818 424237 := bbase (se 3 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 424237 = 159089) (by norm_num)
theorem B948581 : Blo 247818 948581 := bbase (se 4 (by rfl) ⟨88929, by rfl⟩ : syracuseStep 948581 = 177859) (by norm_num)
theorem B424325 : Blo 247818 424325 := bbase (se 4 (by rfl) ⟨39780, by rfl⟩ : syracuseStep 424325 = 79561) (by norm_num)
theorem B424453 : Blo 247818 424453 := bbase (se 4 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 424453 = 79585) (by norm_num)
theorem B424541 : Blo 247818 424541 := bbase (se 3 (by rfl) ⟨79601, by rfl⟩ : syracuseStep 424541 = 159203) (by norm_num)
theorem B424669 : Blo 247818 424669 := bbase (se 3 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 424669 = 159251) (by norm_num)
theorem B424757 : Blo 247818 424757 := bbase (se 5 (by rfl) ⟨19910, by rfl⟩ : syracuseStep 424757 = 39821) (by norm_num)
theorem B424885 : Blo 247818 424885 := bbase (se 5 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 424885 = 39833) (by norm_num)
theorem B1440949 : Blo 247818 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B425245 : Blo 247818 425245 := bbase (se 3 (by rfl) ⟨79733, by rfl⟩ : syracuseStep 425245 = 159467) (by norm_num)
theorem B2293109 : Blo 247818 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B949765 : Blo 247818 949765 := bbase (se 4 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 949765 = 178081) (by norm_num)
theorem B2850389 : Blo 247818 2850389 := bbase (se 8 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 2850389 = 33403) (by norm_num)
theorem B1703605 : Blo 247818 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B294701 : Blo 247818 294701 := bbase (se 3 (by rfl) ⟨55256, by rfl⟩ : syracuseStep 294701 = 110513) (by norm_num)
theorem B950069 : Blo 247818 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B1834805 : Blo 247818 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B3015053 : Blo 247818 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B360931 : Blo 247818 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B557603 : Blo 247818 557603 := bstep (se 1 (by rfl) ⟨418202, by rfl⟩ : syracuseStep 557603 = 836405) B836405
theorem B6390413 : Blo 247818 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B3211973 : Blo 247818 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B951011 : Blo 247818 951011 := bstep (se 1 (by rfl) ⟨713258, by rfl⟩ : syracuseStep 951011 = 1426517) B1426517
theorem B688931 : Blo 247818 688931 := bstep (se 1 (by rfl) ⟨516698, by rfl⟩ : syracuseStep 688931 = 1033397) B1033397
theorem B557873 : Blo 247818 557873 := bstep (se 2 (by rfl) ⟨209202, by rfl⟩ : syracuseStep 557873 = 418405) B418405
theorem B557891 : Blo 247818 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B558161 : Blo 247818 558161 := bstep (se 2 (by rfl) ⟨209310, by rfl⟩ : syracuseStep 558161 = 418621) B418621
theorem B459857 : Blo 247818 459857 := bstep (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) B344893
theorem B558179 : Blo 247818 558179 := bstep (se 1 (by rfl) ⟨418634, by rfl⟩ : syracuseStep 558179 = 837269) B837269
theorem B558449 : Blo 247818 558449 := bstep (se 2 (by rfl) ⟨209418, by rfl⟩ : syracuseStep 558449 = 418837) B418837
theorem B558467 : Blo 247818 558467 := bstep (se 1 (by rfl) ⟨418850, by rfl⟩ : syracuseStep 558467 = 837701) B837701
theorem B558737 : Blo 247818 558737 := bstep (se 2 (by rfl) ⟨209526, by rfl⟩ : syracuseStep 558737 = 419053) B419053
theorem B558755 : Blo 247818 558755 := bstep (se 1 (by rfl) ⟨419066, by rfl⟩ : syracuseStep 558755 = 838133) B838133
theorem B952013 : Blo 247818 952013 := bstep (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) B357005
theorem B1509133 : Blo 247818 1509133 := bstep (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) B565925
theorem B919331 : Blo 247818 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B853841 : Blo 247818 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B559025 : Blo 247818 559025 := bstep (se 2 (by rfl) ⟨209634, by rfl⟩ : syracuseStep 559025 = 419269) B419269
theorem B559043 : Blo 247818 559043 := bstep (se 1 (by rfl) ⟨419282, by rfl⟩ : syracuseStep 559043 = 838565) B838565
theorem B1607651 : Blo 247818 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B1214477 : Blo 247818 1214477 := bstep (se 3 (by rfl) ⟨227714, by rfl⟩ : syracuseStep 1214477 = 455429) B455429
theorem B559313 : Blo 247818 559313 := bstep (se 2 (by rfl) ⟨209742, by rfl⟩ : syracuseStep 559313 = 419485) B419485
theorem B559331 : Blo 247818 559331 := bstep (se 1 (by rfl) ⟨419498, by rfl⟩ : syracuseStep 559331 = 838997) B838997
theorem B2033905 : Blo 247818 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B1804685 : Blo 247818 1804685 := bstep (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) B676757
theorem B1411505 : Blo 247818 1411505 := bstep (se 2 (by rfl) ⟨529314, by rfl⟩ : syracuseStep 1411505 = 1058629) B1058629
theorem B1608113 : Blo 247818 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B559601 : Blo 247818 559601 := bstep (se 2 (by rfl) ⟨209850, by rfl⟩ : syracuseStep 559601 = 419701) B419701
theorem B559619 : Blo 247818 559619 := bstep (se 1 (by rfl) ⟨419714, by rfl⟩ : syracuseStep 559619 = 839429) B839429
theorem B428755 : Blo 247818 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B559889 : Blo 247818 559889 := bstep (se 2 (by rfl) ⟨209958, by rfl⟩ : syracuseStep 559889 = 419917) B419917
theorem B559907 : Blo 247818 559907 := bstep (se 1 (by rfl) ⟨419930, by rfl⟩ : syracuseStep 559907 = 839861) B839861
theorem B1018673 : Blo 247818 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B265123 : Blo 247818 265123 := bstep (se 1 (by rfl) ⟨198842, by rfl⟩ : syracuseStep 265123 = 397685) B397685
theorem B560177 : Blo 247818 560177 := bstep (se 2 (by rfl) ⟨210066, by rfl⟩ : syracuseStep 560177 = 420133) B420133
theorem B560195 : Blo 247818 560195 := bstep (se 1 (by rfl) ⟨420146, by rfl⟩ : syracuseStep 560195 = 840293) B840293
theorem B560465 : Blo 247818 560465 := bstep (se 2 (by rfl) ⟨210174, by rfl⟩ : syracuseStep 560465 = 420349) B420349
theorem B560483 : Blo 247818 560483 := bstep (se 1 (by rfl) ⟨420362, by rfl⟩ : syracuseStep 560483 = 840725) B840725
theorem B1019405 : Blo 247818 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B560753 : Blo 247818 560753 := bstep (se 2 (by rfl) ⟨210282, by rfl⟩ : syracuseStep 560753 = 420565) B420565
theorem B560771 : Blo 247818 560771 := bstep (se 1 (by rfl) ⟨420578, by rfl⟩ : syracuseStep 560771 = 841157) B841157
theorem B397057 : Blo 247818 397057 := bstep (se 2 (by rfl) ⟨148896, by rfl⟩ : syracuseStep 397057 = 297793) B297793
theorem B954125 : Blo 247818 954125 := bstep (se 3 (by rfl) ⟨178898, by rfl⟩ : syracuseStep 954125 = 357797) B357797
theorem B1412963 : Blo 247818 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B1347461 : Blo 247818 1347461 := bstep (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) B252649
theorem B561041 : Blo 247818 561041 := bstep (se 2 (by rfl) ⟨210390, by rfl⟩ : syracuseStep 561041 = 420781) B420781
theorem B561059 : Blo 247818 561059 := bstep (se 1 (by rfl) ⟨420794, by rfl⟩ : syracuseStep 561059 = 841589) B841589
theorem B397313 : Blo 247818 397313 := bstep (se 2 (by rfl) ⟨148992, by rfl⟩ : syracuseStep 397313 = 297985) B297985
theorem B757777 : Blo 247818 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B266387 : Blo 247818 266387 := bstep (se 1 (by rfl) ⟨199790, by rfl⟩ : syracuseStep 266387 = 399581) B399581
theorem B561329 : Blo 247818 561329 := bstep (se 2 (by rfl) ⟨210498, by rfl⟩ : syracuseStep 561329 = 420997) B420997
theorem B561347 : Blo 247818 561347 := bstep (se 1 (by rfl) ⟨421010, by rfl⟩ : syracuseStep 561347 = 842021) B842021
theorem B12226787 : Blo 247818 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B954659 : Blo 247818 954659 := bstep (se 1 (by rfl) ⟨715994, by rfl⟩ : syracuseStep 954659 = 1431989) B1431989
theorem B430499 : Blo 247818 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B561617 : Blo 247818 561617 := bstep (se 2 (by rfl) ⟨210606, by rfl⟩ : syracuseStep 561617 = 421213) B421213
theorem B561635 : Blo 247818 561635 := bstep (se 1 (by rfl) ⟨421226, by rfl⟩ : syracuseStep 561635 = 842453) B842453
theorem B954929 : Blo 247818 954929 := bstep (se 2 (by rfl) ⟨358098, by rfl⟩ : syracuseStep 954929 = 716197) B716197
theorem B430643 : Blo 247818 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B398017 : Blo 247818 398017 := bstep (se 2 (by rfl) ⟨149256, by rfl⟩ : syracuseStep 398017 = 298513) B298513
theorem B561905 : Blo 247818 561905 := bstep (se 2 (by rfl) ⟨210714, by rfl⟩ : syracuseStep 561905 = 421429) B421429
theorem B561923 : Blo 247818 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B758627 : Blo 247818 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B267139 : Blo 247818 267139 := bstep (se 1 (by rfl) ⟨200354, by rfl⟩ : syracuseStep 267139 = 400709) B400709
theorem B1905605 : Blo 247818 1905605 := bstep (se 4 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 1905605 = 357301) B357301
theorem B562193 : Blo 247818 562193 := bstep (se 2 (by rfl) ⟨210822, by rfl⟩ : syracuseStep 562193 = 421645) B421645
theorem B562211 : Blo 247818 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B267395 : Blo 247818 267395 := bstep (se 1 (by rfl) ⟨200546, by rfl⟩ : syracuseStep 267395 = 401093) B401093
theorem B955597 : Blo 247818 955597 := bstep (se 3 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 955597 = 358349) B358349
theorem B529699 : Blo 247818 529699 := bstep (se 1 (by rfl) ⟨397274, by rfl⟩ : syracuseStep 529699 = 794549) B794549
theorem B562481 : Blo 247818 562481 := bstep (se 2 (by rfl) ⟨210930, by rfl⟩ : syracuseStep 562481 = 421861) B421861
theorem B562499 : Blo 247818 562499 := bstep (se 1 (by rfl) ⟨421874, by rfl⟩ : syracuseStep 562499 = 843749) B843749
theorem B628145 : Blo 247818 628145 := bstep (se 2 (by rfl) ⟨235554, by rfl⟩ : syracuseStep 628145 = 471109) B471109
theorem B628195 : Blo 247818 628195 := bstep (se 1 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 628195 = 942293) B942293
theorem B759299 : Blo 247818 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B398915 : Blo 247818 398915 := bstep (se 1 (by rfl) ⟨299186, by rfl⟩ : syracuseStep 398915 = 598373) B598373
theorem B562769 : Blo 247818 562769 := bstep (se 2 (by rfl) ⟨211038, by rfl⟩ : syracuseStep 562769 = 422077) B422077
theorem B562787 : Blo 247818 562787 := bstep (se 1 (by rfl) ⟨422090, by rfl⟩ : syracuseStep 562787 = 844181) B844181
theorem B628337 : Blo 247818 628337 := bstep (se 2 (by rfl) ⟨235626, by rfl⟩ : syracuseStep 628337 = 471253) B471253
theorem B1414853 : Blo 247818 1414853 := bstep (se 4 (by rfl) ⟨132642, by rfl⟩ : syracuseStep 1414853 = 265285) B265285
theorem B399107 : Blo 247818 399107 := bstep (se 1 (by rfl) ⟨299330, by rfl⟩ : syracuseStep 399107 = 598661) B598661
theorem B563057 : Blo 247818 563057 := bstep (se 2 (by rfl) ⟨211146, by rfl⟩ : syracuseStep 563057 = 422293) B422293
theorem B268147 : Blo 247818 268147 := bstep (se 1 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 268147 = 402221) B402221
theorem B563075 : Blo 247818 563075 := bstep (se 1 (by rfl) ⟨422306, by rfl⟩ : syracuseStep 563075 = 844613) B844613
theorem B2693189 : Blo 247818 2693189 := bstep (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) B504973
theorem B25860181 : Blo 247818 25860181 := bstep (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) B303049
theorem B530545 : Blo 247818 530545 := bstep (se 2 (by rfl) ⟨198954, by rfl⟩ : syracuseStep 530545 = 397909) B397909
theorem B563345 : Blo 247818 563345 := bstep (se 2 (by rfl) ⟨211254, by rfl⟩ : syracuseStep 563345 = 422509) B422509
theorem B563363 : Blo 247818 563363 := bstep (se 1 (by rfl) ⟨422522, by rfl⟩ : syracuseStep 563363 = 845045) B845045
theorem B1808581 : Blo 247818 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B792845 : Blo 247818 792845 := bstep (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) B297317
theorem B5773589 : Blo 247818 5773589 := bstep (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) B270637
theorem B563633 : Blo 247818 563633 := bstep (se 2 (by rfl) ⟨211362, by rfl⟩ : syracuseStep 563633 = 422725) B422725
theorem B563651 : Blo 247818 563651 := bstep (se 1 (by rfl) ⟨422738, by rfl⟩ : syracuseStep 563651 = 845477) B845477
theorem B629329 : Blo 247818 629329 := bstep (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) B471997
theorem B400081 : Blo 247818 400081 := bstep (se 2 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 400081 = 300061) B300061
theorem B563921 : Blo 247818 563921 := bstep (se 2 (by rfl) ⟨211470, by rfl⟩ : syracuseStep 563921 = 422941) B422941
theorem B563939 : Blo 247818 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B629603 : Blo 247818 629603 := bstep (se 1 (by rfl) ⟨472202, by rfl⟩ : syracuseStep 629603 = 944405) B944405
theorem B564209 : Blo 247818 564209 := bstep (se 2 (by rfl) ⟨211578, by rfl⟩ : syracuseStep 564209 = 423157) B423157
theorem B564227 : Blo 247818 564227 := bstep (se 1 (by rfl) ⟨423170, by rfl⟩ : syracuseStep 564227 = 846341) B846341
theorem B629795 : Blo 247818 629795 := bstep (se 1 (by rfl) ⟨472346, by rfl⟩ : syracuseStep 629795 = 944693) B944693
theorem B400529 : Blo 247818 400529 := bstep (se 2 (by rfl) ⟨150198, by rfl⟩ : syracuseStep 400529 = 300397) B300397
theorem B564497 : Blo 247818 564497 := bstep (se 2 (by rfl) ⟨211686, by rfl⟩ : syracuseStep 564497 = 423373) B423373
theorem B564515 : Blo 247818 564515 := bstep (se 1 (by rfl) ⟨423386, by rfl⟩ : syracuseStep 564515 = 846773) B846773
theorem B1023331 : Blo 247818 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B564785 : Blo 247818 564785 := bstep (se 2 (by rfl) ⟨211794, by rfl⟩ : syracuseStep 564785 = 423589) B423589
theorem B564803 : Blo 247818 564803 := bstep (se 1 (by rfl) ⟨423602, by rfl⟩ : syracuseStep 564803 = 847205) B847205
theorem B565073 : Blo 247818 565073 := bstep (se 2 (by rfl) ⟨211902, by rfl⟩ : syracuseStep 565073 = 423805) B423805
theorem B565091 : Blo 247818 565091 := bstep (se 1 (by rfl) ⟨423818, by rfl⟩ : syracuseStep 565091 = 847637) B847637
theorem B3710861 : Blo 247818 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B630737 : Blo 247818 630737 := bstep (se 2 (by rfl) ⟨236526, by rfl⟩ : syracuseStep 630737 = 473053) B473053
theorem B532433 : Blo 247818 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B630787 : Blo 247818 630787 := bstep (se 1 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 630787 = 946181) B946181
theorem B3186701 : Blo 247818 3186701 := bstep (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) B1195013
theorem B794701 : Blo 247818 794701 := bstep (se 3 (by rfl) ⟨149006, by rfl⟩ : syracuseStep 794701 = 298013) B298013
theorem B565361 : Blo 247818 565361 := bstep (se 2 (by rfl) ⟨212010, by rfl⟩ : syracuseStep 565361 = 424021) B424021
theorem B336001 : Blo 247818 336001 := bstep (se 2 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 336001 = 252001) B252001
theorem B761987 : Blo 247818 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B565379 : Blo 247818 565379 := bstep (se 1 (by rfl) ⟨424034, by rfl⟩ : syracuseStep 565379 = 848069) B848069
theorem B630929 : Blo 247818 630929 := bstep (se 2 (by rfl) ⟨236598, by rfl⟩ : syracuseStep 630929 = 473197) B473197
theorem B2138339 : Blo 247818 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B565649 : Blo 247818 565649 := bstep (se 2 (by rfl) ⟨212118, by rfl⟩ : syracuseStep 565649 = 424237) B424237
theorem B565667 : Blo 247818 565667 := bstep (se 1 (by rfl) ⟨424250, by rfl⟩ : syracuseStep 565667 = 848501) B848501
theorem B401939 : Blo 247818 401939 := bstep (se 1 (by rfl) ⟨301454, by rfl⟩ : syracuseStep 401939 = 602909) B602909
theorem B795203 : Blo 247818 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B2040461 : Blo 247818 2040461 := bstep (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) B765173
theorem B565937 : Blo 247818 565937 := bstep (se 2 (by rfl) ⟨212226, by rfl⟩ : syracuseStep 565937 = 424453) B424453
theorem B565955 : Blo 247818 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B402131 : Blo 247818 402131 := bstep (se 1 (by rfl) ⟨301598, by rfl⟩ : syracuseStep 402131 = 603197) B603197
theorem B2827061 : Blo 247818 2827061 := bstep (se 5 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 2827061 = 265037) B265037
theorem B566225 : Blo 247818 566225 := bstep (se 2 (by rfl) ⟨212334, by rfl⟩ : syracuseStep 566225 = 424669) B424669
theorem B566243 : Blo 247818 566243 := bstep (se 1 (by rfl) ⟨424682, by rfl⟩ : syracuseStep 566243 = 849365) B849365
theorem B631921 : Blo 247818 631921 := bstep (se 2 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 631921 = 473941) B473941
theorem B533731 : Blo 247818 533731 := bstep (se 1 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 533731 = 800597) B800597
theorem B566513 : Blo 247818 566513 := bstep (se 2 (by rfl) ⟨212442, by rfl⟩ : syracuseStep 566513 = 424885) B424885
theorem B566531 : Blo 247818 566531 := bstep (se 1 (by rfl) ⟨424898, by rfl⟩ : syracuseStep 566531 = 849797) B849797
theorem B632195 : Blo 247818 632195 := bstep (se 1 (by rfl) ⟨474146, by rfl⟩ : syracuseStep 632195 = 948293) B948293
theorem B1910243 : Blo 247818 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B337379 : Blo 247818 337379 := bstep (se 1 (by rfl) ⟨253034, by rfl⟩ : syracuseStep 337379 = 506069) B506069
theorem B632387 : Blo 247818 632387 := bstep (se 1 (by rfl) ⟨474290, by rfl⟩ : syracuseStep 632387 = 948581) B948581
theorem B566993 : Blo 247818 566993 := bstep (se 2 (by rfl) ⟨212622, by rfl⟩ : syracuseStep 566993 = 425245) B425245
theorem B796547 : Blo 247818 796547 := bstep (se 1 (by rfl) ⟨597410, by rfl⟩ : syracuseStep 796547 = 1194821) B1194821
theorem B1517453 : Blo 247818 1517453 := bstep (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) B569045
theorem B337969 : Blo 247818 337969 := bstep (se 2 (by rfl) ⟨126738, by rfl⟩ : syracuseStep 337969 = 253477) B253477
theorem B338033 : Blo 247818 338033 := bstep (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) B253525
theorem B338131 : Blo 247818 338131 := bstep (se 1 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 338131 = 507197) B507197
theorem B2271473 : Blo 247818 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B3909941 : Blo 247818 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B534961 : Blo 247818 534961 := bstep (se 2 (by rfl) ⟨200610, by rfl⟩ : syracuseStep 534961 = 401221) B401221
theorem B633329 : Blo 247818 633329 := bstep (se 2 (by rfl) ⟨237498, by rfl⟩ : syracuseStep 633329 = 474997) B474997
theorem B1223203 : Blo 247818 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B633379 : Blo 247818 633379 := bstep (se 1 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 633379 = 950069) B950069
theorem B1255985 : Blo 247818 1255985 := bstep (se 2 (by rfl) ⟨470994, by rfl⟩ : syracuseStep 1255985 = 941989) B941989
theorem B1911437 : Blo 247818 1911437 := bstep (se 3 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 1911437 = 716789) B716789
theorem B633521 : Blo 247818 633521 := bstep (se 2 (by rfl) ⟨237570, by rfl⟩ : syracuseStep 633521 = 475141) B475141
theorem B797521 : Blo 247818 797521 := bstep (se 2 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 797521 = 598141) B598141
theorem B2698211 : Blo 247818 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B371729 : Blo 247818 371729 := bstep (se 2 (by rfl) ⟨139398, by rfl⟩ : syracuseStep 371729 = 278797) B278797
theorem B371747 : Blo 247818 371747 := bstep (se 1 (by rfl) ⟨278810, by rfl⟩ : syracuseStep 371747 = 557621) B557621
theorem B1059875 : Blo 247818 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B371777 : Blo 247818 371777 := bstep (se 2 (by rfl) ⟨139416, by rfl⟩ : syracuseStep 371777 = 278833) B278833
theorem B797777 : Blo 247818 797777 := bstep (se 2 (by rfl) ⟨299166, by rfl⟩ : syracuseStep 797777 = 598333) B598333
theorem B371795 : Blo 247818 371795 := bstep (se 1 (by rfl) ⟨278846, by rfl⟩ : syracuseStep 371795 = 557693) B557693
theorem B371825 : Blo 247818 371825 := bstep (se 2 (by rfl) ⟨139434, by rfl⟩ : syracuseStep 371825 = 278869) B278869
theorem B371843 : Blo 247818 371843 := bstep (se 1 (by rfl) ⟨278882, by rfl⟩ : syracuseStep 371843 = 557765) B557765
theorem B371873 : Blo 247818 371873 := bstep (se 2 (by rfl) ⟨139452, by rfl⟩ : syracuseStep 371873 = 278905) B278905
theorem B765101 : Blo 247818 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B371891 : Blo 247818 371891 := bstep (se 1 (by rfl) ⟨278918, by rfl⟩ : syracuseStep 371891 = 557837) B557837
theorem B535747 : Blo 247818 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B371921 : Blo 247818 371921 := bstep (se 2 (by rfl) ⟨139470, by rfl⟩ : syracuseStep 371921 = 278941) B278941
theorem B371939 : Blo 247818 371939 := bstep (se 1 (by rfl) ⟨278954, by rfl⟩ : syracuseStep 371939 = 557909) B557909
theorem B371969 : Blo 247818 371969 := bstep (se 2 (by rfl) ⟨139488, by rfl⟩ : syracuseStep 371969 = 278977) B278977
theorem B1649933 : Blo 247818 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B371987 : Blo 247818 371987 := bstep (se 1 (by rfl) ⟨278990, by rfl⟩ : syracuseStep 371987 = 557981) B557981
theorem B896291 : Blo 247818 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B372017 : Blo 247818 372017 := bstep (se 2 (by rfl) ⟨139506, by rfl⟩ : syracuseStep 372017 = 279013) B279013
theorem B372035 : Blo 247818 372035 := bstep (se 1 (by rfl) ⟨279026, by rfl⟩ : syracuseStep 372035 = 558053) B558053
theorem B372065 : Blo 247818 372065 := bstep (se 2 (by rfl) ⟨139524, by rfl⟩ : syracuseStep 372065 = 279049) B279049
theorem B372083 : Blo 247818 372083 := bstep (se 1 (by rfl) ⟨279062, by rfl⟩ : syracuseStep 372083 = 558125) B558125
theorem B339331 : Blo 247818 339331 := bstep (se 1 (by rfl) ⟨254498, by rfl⟩ : syracuseStep 339331 = 508997) B508997
theorem B1420685 : Blo 247818 1420685 := bstep (se 3 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 1420685 = 532757) B532757
theorem B372113 : Blo 247818 372113 := bstep (se 2 (by rfl) ⟨139542, by rfl⟩ : syracuseStep 372113 = 279085) B279085
theorem B372131 : Blo 247818 372131 := bstep (se 1 (by rfl) ⟨279098, by rfl⟩ : syracuseStep 372131 = 558197) B558197
theorem B372161 : Blo 247818 372161 := bstep (se 2 (by rfl) ⟨139560, by rfl⟩ : syracuseStep 372161 = 279121) B279121
theorem B372179 : Blo 247818 372179 := bstep (se 1 (by rfl) ⟨279134, by rfl⟩ : syracuseStep 372179 = 558269) B558269
theorem B372209 : Blo 247818 372209 := bstep (se 2 (by rfl) ⟨139578, by rfl⟩ : syracuseStep 372209 = 279157) B279157
theorem B372227 : Blo 247818 372227 := bstep (se 1 (by rfl) ⟨279170, by rfl⟩ : syracuseStep 372227 = 558341) B558341
theorem B1191437 : Blo 247818 1191437 := bstep (se 3 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 1191437 = 446789) B446789
theorem B372257 : Blo 247818 372257 := bstep (se 2 (by rfl) ⟨139596, by rfl⟩ : syracuseStep 372257 = 279193) B279193
theorem B372275 : Blo 247818 372275 := bstep (se 1 (by rfl) ⟨279206, by rfl⟩ : syracuseStep 372275 = 558413) B558413
theorem B372305 : Blo 247818 372305 := bstep (se 2 (by rfl) ⟨139614, by rfl⟩ : syracuseStep 372305 = 279229) B279229
theorem B372323 : Blo 247818 372323 := bstep (se 1 (by rfl) ⟨279242, by rfl⟩ : syracuseStep 372323 = 558485) B558485
theorem B372353 : Blo 247818 372353 := bstep (se 2 (by rfl) ⟨139632, by rfl⟩ : syracuseStep 372353 = 279265) B279265
theorem B634513 : Blo 247818 634513 := bstep (se 2 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 634513 = 475885) B475885
theorem B372371 : Blo 247818 372371 := bstep (se 1 (by rfl) ⟨279278, by rfl⟩ : syracuseStep 372371 = 558557) B558557
theorem B372401 : Blo 247818 372401 := bstep (se 2 (by rfl) ⟨139650, by rfl⟩ : syracuseStep 372401 = 279301) B279301
theorem B372419 : Blo 247818 372419 := bstep (se 1 (by rfl) ⟨279314, by rfl⟩ : syracuseStep 372419 = 558629) B558629
theorem B372449 : Blo 247818 372449 := bstep (se 2 (by rfl) ⟨139668, by rfl⟩ : syracuseStep 372449 = 279337) B279337
theorem B1650403 : Blo 247818 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B372467 : Blo 247818 372467 := bstep (se 1 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 372467 = 558701) B558701
theorem B372497 : Blo 247818 372497 := bstep (se 2 (by rfl) ⟨139686, by rfl⟩ : syracuseStep 372497 = 279373) B279373
theorem B372515 : Blo 247818 372515 := bstep (se 1 (by rfl) ⟨279386, by rfl⟩ : syracuseStep 372515 = 558773) B558773
theorem B339763 : Blo 247818 339763 := bstep (se 1 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 339763 = 509645) B509645
theorem B372545 : Blo 247818 372545 := bstep (se 2 (by rfl) ⟨139704, by rfl⟩ : syracuseStep 372545 = 279409) B279409
theorem B372563 : Blo 247818 372563 := bstep (se 1 (by rfl) ⟨279422, by rfl⟩ : syracuseStep 372563 = 558845) B558845
theorem B372593 : Blo 247818 372593 := bstep (se 2 (by rfl) ⟨139722, by rfl⟩ : syracuseStep 372593 = 279445) B279445
theorem B4599665 : Blo 247818 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B372611 : Blo 247818 372611 := bstep (se 1 (by rfl) ⟨279458, by rfl⟩ : syracuseStep 372611 = 558917) B558917
theorem B536465 : Blo 247818 536465 := bstep (se 2 (by rfl) ⟨201174, by rfl⟩ : syracuseStep 536465 = 402349) B402349
theorem B372641 : Blo 247818 372641 := bstep (se 2 (by rfl) ⟨139740, by rfl⟩ : syracuseStep 372641 = 279481) B279481
theorem B634787 : Blo 247818 634787 := bstep (se 1 (by rfl) ⟨476090, by rfl⟩ : syracuseStep 634787 = 952181) B952181
theorem B372659 : Blo 247818 372659 := bstep (se 1 (by rfl) ⟨279494, by rfl⟩ : syracuseStep 372659 = 558989) B558989
theorem B372689 : Blo 247818 372689 := bstep (se 2 (by rfl) ⟨139758, by rfl⟩ : syracuseStep 372689 = 279517) B279517
theorem B1257443 : Blo 247818 1257443 := bstep (se 1 (by rfl) ⟨943082, by rfl⟩ : syracuseStep 1257443 = 1886165) B1886165
theorem B372707 : Blo 247818 372707 := bstep (se 1 (by rfl) ⟨279530, by rfl⟩ : syracuseStep 372707 = 559061) B559061
theorem B471025 : Blo 247818 471025 := bstep (se 2 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 471025 = 353269) B353269
theorem B372737 : Blo 247818 372737 := bstep (se 2 (by rfl) ⟨139776, by rfl⟩ : syracuseStep 372737 = 279553) B279553
theorem B372755 : Blo 247818 372755 := bstep (se 1 (by rfl) ⟨279566, by rfl⟩ : syracuseStep 372755 = 559133) B559133
theorem B372785 : Blo 247818 372785 := bstep (se 2 (by rfl) ⟨139794, by rfl⟩ : syracuseStep 372785 = 279589) B279589
theorem B372803 : Blo 247818 372803 := bstep (se 1 (by rfl) ⟨279602, by rfl⟩ : syracuseStep 372803 = 559205) B559205
theorem B372833 : Blo 247818 372833 := bstep (se 2 (by rfl) ⟨139812, by rfl⟩ : syracuseStep 372833 = 279625) B279625
theorem B634979 : Blo 247818 634979 := bstep (se 1 (by rfl) ⟨476234, by rfl⟩ : syracuseStep 634979 = 952469) B952469
theorem B372851 : Blo 247818 372851 := bstep (se 1 (by rfl) ⟨279638, by rfl⟩ : syracuseStep 372851 = 559277) B559277
theorem B372881 : Blo 247818 372881 := bstep (se 2 (by rfl) ⟨139830, by rfl⟩ : syracuseStep 372881 = 279661) B279661
theorem B372899 : Blo 247818 372899 := bstep (se 1 (by rfl) ⟨279674, by rfl⟩ : syracuseStep 372899 = 559349) B559349
theorem B798893 : Blo 247818 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B372929 : Blo 247818 372929 := bstep (se 2 (by rfl) ⟨139848, by rfl⟩ : syracuseStep 372929 = 279697) B279697
theorem B372947 : Blo 247818 372947 := bstep (se 1 (by rfl) ⟨279710, by rfl⟩ : syracuseStep 372947 = 559421) B559421
theorem B372977 : Blo 247818 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B372995 : Blo 247818 372995 := bstep (se 1 (by rfl) ⟨279746, by rfl⟩ : syracuseStep 372995 = 559493) B559493
theorem B373025 : Blo 247818 373025 := bstep (se 2 (by rfl) ⟨139884, by rfl⟩ : syracuseStep 373025 = 279769) B279769
theorem B373043 : Blo 247818 373043 := bstep (se 1 (by rfl) ⟨279782, by rfl⟩ : syracuseStep 373043 = 559565) B559565
theorem B373073 : Blo 247818 373073 := bstep (se 2 (by rfl) ⟨139902, by rfl⟩ : syracuseStep 373073 = 279805) B279805
theorem B373091 : Blo 247818 373091 := bstep (se 1 (by rfl) ⟨279818, by rfl⟩ : syracuseStep 373091 = 559637) B559637
theorem B373121 : Blo 247818 373121 := bstep (se 2 (by rfl) ⟨139920, by rfl⟩ : syracuseStep 373121 = 279841) B279841
theorem B536977 : Blo 247818 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B373139 : Blo 247818 373139 := bstep (se 1 (by rfl) ⟨279854, by rfl⟩ : syracuseStep 373139 = 559709) B559709
theorem B373169 : Blo 247818 373169 := bstep (se 2 (by rfl) ⟨139938, by rfl⟩ : syracuseStep 373169 = 279877) B279877
theorem B373187 : Blo 247818 373187 := bstep (se 1 (by rfl) ⟨279890, by rfl⟩ : syracuseStep 373187 = 559781) B559781
theorem B930253 : Blo 247818 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B373217 : Blo 247818 373217 := bstep (se 2 (by rfl) ⟨139956, by rfl⟩ : syracuseStep 373217 = 279913) B279913
theorem B373235 : Blo 247818 373235 := bstep (se 1 (by rfl) ⟨279926, by rfl⟩ : syracuseStep 373235 = 559853) B559853
theorem B373265 : Blo 247818 373265 := bstep (se 2 (by rfl) ⟨139974, by rfl⟩ : syracuseStep 373265 = 279949) B279949
theorem B373283 : Blo 247818 373283 := bstep (se 1 (by rfl) ⟨279962, by rfl⟩ : syracuseStep 373283 = 559925) B559925
theorem B373313 : Blo 247818 373313 := bstep (se 2 (by rfl) ⟨139992, by rfl⟩ : syracuseStep 373313 = 279985) B279985
theorem B373331 : Blo 247818 373331 := bstep (se 1 (by rfl) ⟨279998, by rfl⟩ : syracuseStep 373331 = 559997) B559997
theorem B373361 : Blo 247818 373361 := bstep (se 2 (by rfl) ⟨140010, by rfl⟩ : syracuseStep 373361 = 280021) B280021
theorem B373379 : Blo 247818 373379 := bstep (se 1 (by rfl) ⟨280034, by rfl⟩ : syracuseStep 373379 = 560069) B560069
theorem B373409 : Blo 247818 373409 := bstep (se 2 (by rfl) ⟨140028, by rfl⟩ : syracuseStep 373409 = 280057) B280057
theorem B373427 : Blo 247818 373427 := bstep (se 1 (by rfl) ⟨280070, by rfl⟩ : syracuseStep 373427 = 560141) B560141
theorem B373457 : Blo 247818 373457 := bstep (se 2 (by rfl) ⟨140046, by rfl⟩ : syracuseStep 373457 = 280093) B280093
theorem B373475 : Blo 247818 373475 := bstep (se 1 (by rfl) ⟨280106, by rfl⟩ : syracuseStep 373475 = 560213) B560213
theorem B373505 : Blo 247818 373505 := bstep (se 2 (by rfl) ⟨140064, by rfl⟩ : syracuseStep 373505 = 280129) B280129
theorem B1258253 : Blo 247818 1258253 := bstep (se 3 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 1258253 = 471845) B471845
theorem B373523 : Blo 247818 373523 := bstep (se 1 (by rfl) ⟨280142, by rfl⟩ : syracuseStep 373523 = 560285) B560285
theorem B373553 : Blo 247818 373553 := bstep (se 2 (by rfl) ⟨140082, by rfl⟩ : syracuseStep 373553 = 280165) B280165
theorem B504643 : Blo 247818 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B373571 : Blo 247818 373571 := bstep (se 1 (by rfl) ⟨280178, by rfl⟩ : syracuseStep 373571 = 560357) B560357
theorem B373601 : Blo 247818 373601 := bstep (se 2 (by rfl) ⟨140100, by rfl⟩ : syracuseStep 373601 = 280201) B280201
theorem B897905 : Blo 247818 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B373619 : Blo 247818 373619 := bstep (se 1 (by rfl) ⟨280214, by rfl⟩ : syracuseStep 373619 = 560429) B560429
theorem B373649 : Blo 247818 373649 := bstep (se 2 (by rfl) ⟨140118, by rfl⟩ : syracuseStep 373649 = 280237) B280237
theorem B373667 : Blo 247818 373667 := bstep (se 1 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 373667 = 560501) B560501
theorem B373697 : Blo 247818 373697 := bstep (se 2 (by rfl) ⟨140136, by rfl⟩ : syracuseStep 373697 = 280273) B280273
theorem B373715 : Blo 247818 373715 := bstep (se 1 (by rfl) ⟨280286, by rfl⟩ : syracuseStep 373715 = 560573) B560573
theorem B373745 : Blo 247818 373745 := bstep (se 2 (by rfl) ⟨140154, by rfl⟩ : syracuseStep 373745 = 280309) B280309
theorem B373763 : Blo 247818 373763 := bstep (se 1 (by rfl) ⟨280322, by rfl⟩ : syracuseStep 373763 = 560645) B560645
theorem B472081 : Blo 247818 472081 := bstep (se 2 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 472081 = 354061) B354061
theorem B635921 : Blo 247818 635921 := bstep (se 2 (by rfl) ⟨238470, by rfl⟩ : syracuseStep 635921 = 476941) B476941
theorem B373793 : Blo 247818 373793 := bstep (se 2 (by rfl) ⟨140172, by rfl⟩ : syracuseStep 373793 = 280345) B280345
theorem B406561 : Blo 247818 406561 := bstep (se 2 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 406561 = 304921) B304921
theorem B373811 : Blo 247818 373811 := bstep (se 1 (by rfl) ⟨280358, by rfl⟩ : syracuseStep 373811 = 560717) B560717
theorem B406595 : Blo 247818 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B635971 : Blo 247818 635971 := bstep (se 1 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 635971 = 953957) B953957
theorem B373841 : Blo 247818 373841 := bstep (se 2 (by rfl) ⟨140190, by rfl⟩ : syracuseStep 373841 = 280381) B280381
theorem B373859 : Blo 247818 373859 := bstep (se 1 (by rfl) ⟨280394, by rfl⟩ : syracuseStep 373859 = 560789) B560789
theorem B373889 : Blo 247818 373889 := bstep (se 2 (by rfl) ⟨140208, by rfl⟩ : syracuseStep 373889 = 280417) B280417
theorem B373907 : Blo 247818 373907 := bstep (se 1 (by rfl) ⟨280430, by rfl⟩ : syracuseStep 373907 = 560861) B560861
theorem B373937 : Blo 247818 373937 := bstep (se 2 (by rfl) ⟨140226, by rfl⟩ : syracuseStep 373937 = 280453) B280453
theorem B373955 : Blo 247818 373955 := bstep (se 1 (by rfl) ⟨280466, by rfl⟩ : syracuseStep 373955 = 560933) B560933
theorem B636113 : Blo 247818 636113 := bstep (se 2 (by rfl) ⟨238542, by rfl⟩ : syracuseStep 636113 = 477085) B477085
theorem B570577 : Blo 247818 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B373985 : Blo 247818 373985 := bstep (se 2 (by rfl) ⟨140244, by rfl⟩ : syracuseStep 373985 = 280489) B280489
theorem B374003 : Blo 247818 374003 := bstep (se 1 (by rfl) ⟨280502, by rfl⟩ : syracuseStep 374003 = 561005) B561005
theorem B374033 : Blo 247818 374033 := bstep (se 2 (by rfl) ⟨140262, by rfl⟩ : syracuseStep 374033 = 280525) B280525
theorem B374051 : Blo 247818 374051 := bstep (se 1 (by rfl) ⟨280538, by rfl⟩ : syracuseStep 374051 = 561077) B561077
theorem B374081 : Blo 247818 374081 := bstep (se 2 (by rfl) ⟨140280, by rfl⟩ : syracuseStep 374081 = 280561) B280561
theorem B374099 : Blo 247818 374099 := bstep (se 1 (by rfl) ⟨280574, by rfl⟩ : syracuseStep 374099 = 561149) B561149
theorem B374129 : Blo 247818 374129 := bstep (se 2 (by rfl) ⟨140298, by rfl⟩ : syracuseStep 374129 = 280597) B280597
theorem B374147 : Blo 247818 374147 := bstep (se 1 (by rfl) ⟨280610, by rfl⟩ : syracuseStep 374147 = 561221) B561221
theorem B374177 : Blo 247818 374177 := bstep (se 2 (by rfl) ⟨140316, by rfl⟩ : syracuseStep 374177 = 280633) B280633
theorem B472483 : Blo 247818 472483 := bstep (se 1 (by rfl) ⟨354362, by rfl⟩ : syracuseStep 472483 = 708725) B708725
theorem B374195 : Blo 247818 374195 := bstep (se 1 (by rfl) ⟨280646, by rfl⟩ : syracuseStep 374195 = 561293) B561293
theorem B472529 : Blo 247818 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B374225 : Blo 247818 374225 := bstep (se 2 (by rfl) ⟨140334, by rfl⟩ : syracuseStep 374225 = 280669) B280669
theorem B374243 : Blo 247818 374243 := bstep (se 1 (by rfl) ⟨280682, by rfl⟩ : syracuseStep 374243 = 561365) B561365
theorem B800237 : Blo 247818 800237 := bstep (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) B300089
theorem B374273 : Blo 247818 374273 := bstep (se 2 (by rfl) ⟨140352, by rfl⟩ : syracuseStep 374273 = 280705) B280705
theorem B374291 : Blo 247818 374291 := bstep (se 1 (by rfl) ⟨280718, by rfl⟩ : syracuseStep 374291 = 561437) B561437
theorem B374321 : Blo 247818 374321 := bstep (se 2 (by rfl) ⟨140370, by rfl⟩ : syracuseStep 374321 = 280741) B280741
theorem B374339 : Blo 247818 374339 := bstep (se 1 (by rfl) ⟨280754, by rfl⟩ : syracuseStep 374339 = 561509) B561509
theorem B603715 : Blo 247818 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B1422917 : Blo 247818 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B374369 : Blo 247818 374369 := bstep (se 2 (by rfl) ⟨140388, by rfl⟩ : syracuseStep 374369 = 280777) B280777
theorem B374387 : Blo 247818 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B964237 : Blo 247818 964237 := bstep (se 3 (by rfl) ⟨180794, by rfl⟩ : syracuseStep 964237 = 361589) B361589
theorem B374417 : Blo 247818 374417 := bstep (se 2 (by rfl) ⟨140406, by rfl⟩ : syracuseStep 374417 = 280813) B280813
theorem B374435 : Blo 247818 374435 := bstep (se 1 (by rfl) ⟨280826, by rfl⟩ : syracuseStep 374435 = 561653) B561653
theorem B374465 : Blo 247818 374465 := bstep (se 2 (by rfl) ⟨140424, by rfl⟩ : syracuseStep 374465 = 280849) B280849
theorem B374483 : Blo 247818 374483 := bstep (se 1 (by rfl) ⟨280862, by rfl⟩ : syracuseStep 374483 = 561725) B561725
theorem B4830947 : Blo 247818 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B472817 : Blo 247818 472817 := bstep (se 2 (by rfl) ⟨177306, by rfl⟩ : syracuseStep 472817 = 354613) B354613
theorem B374513 : Blo 247818 374513 := bstep (se 2 (by rfl) ⟨140442, by rfl⟩ : syracuseStep 374513 = 280885) B280885
theorem B374531 : Blo 247818 374531 := bstep (se 1 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 374531 = 561797) B561797
theorem B374561 : Blo 247818 374561 := bstep (se 2 (by rfl) ⟨140460, by rfl⟩ : syracuseStep 374561 = 280921) B280921
theorem B374579 : Blo 247818 374579 := bstep (se 1 (by rfl) ⟨280934, by rfl⟩ : syracuseStep 374579 = 561869) B561869
theorem B374609 : Blo 247818 374609 := bstep (se 2 (by rfl) ⟨140478, by rfl⟩ : syracuseStep 374609 = 280957) B280957
theorem B374627 : Blo 247818 374627 := bstep (se 1 (by rfl) ⟨280970, by rfl⟩ : syracuseStep 374627 = 561941) B561941
theorem B1357667 : Blo 247818 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B374657 : Blo 247818 374657 := bstep (se 2 (by rfl) ⟨140496, by rfl⟩ : syracuseStep 374657 = 280993) B280993
theorem B374675 : Blo 247818 374675 := bstep (se 1 (by rfl) ⟨281006, by rfl⟩ : syracuseStep 374675 = 562013) B562013
theorem B800675 : Blo 247818 800675 := bstep (se 1 (by rfl) ⟨600506, by rfl⟩ : syracuseStep 800675 = 1201013) B1201013
theorem B374705 : Blo 247818 374705 := bstep (se 2 (by rfl) ⟨140514, by rfl⟩ : syracuseStep 374705 = 281029) B281029
theorem B374723 : Blo 247818 374723 := bstep (se 1 (by rfl) ⟨281042, by rfl⟩ : syracuseStep 374723 = 562085) B562085
theorem B374753 : Blo 247818 374753 := bstep (se 2 (by rfl) ⟨140532, by rfl⟩ : syracuseStep 374753 = 281065) B281065
theorem B374771 : Blo 247818 374771 := bstep (se 1 (by rfl) ⟨281078, by rfl⟩ : syracuseStep 374771 = 562157) B562157
theorem B374801 : Blo 247818 374801 := bstep (se 2 (by rfl) ⟨140550, by rfl⟩ : syracuseStep 374801 = 281101) B281101
theorem B374819 : Blo 247818 374819 := bstep (se 1 (by rfl) ⟨281114, by rfl⟩ : syracuseStep 374819 = 562229) B562229
theorem B374849 : Blo 247818 374849 := bstep (se 2 (by rfl) ⟨140568, by rfl⟩ : syracuseStep 374849 = 281137) B281137
theorem B374867 : Blo 247818 374867 := bstep (se 1 (by rfl) ⟨281150, by rfl⟩ : syracuseStep 374867 = 562301) B562301
theorem B374897 : Blo 247818 374897 := bstep (se 2 (by rfl) ⟨140586, by rfl⟩ : syracuseStep 374897 = 281173) B281173
theorem B604273 : Blo 247818 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B374915 : Blo 247818 374915 := bstep (se 1 (by rfl) ⟨281186, by rfl⟩ : syracuseStep 374915 = 562373) B562373
theorem B374945 : Blo 247818 374945 := bstep (se 2 (by rfl) ⟨140604, by rfl⟩ : syracuseStep 374945 = 281209) B281209
theorem B637105 : Blo 247818 637105 := bstep (se 2 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 637105 = 477829) B477829
theorem B374963 : Blo 247818 374963 := bstep (se 1 (by rfl) ⟨281222, by rfl⟩ : syracuseStep 374963 = 562445) B562445
theorem B374993 : Blo 247818 374993 := bstep (se 2 (by rfl) ⟨140622, by rfl⟩ : syracuseStep 374993 = 281245) B281245
theorem B375011 : Blo 247818 375011 := bstep (se 1 (by rfl) ⟨281258, by rfl⟩ : syracuseStep 375011 = 562517) B562517
theorem B1423601 : Blo 247818 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B375041 : Blo 247818 375041 := bstep (se 2 (by rfl) ⟨140640, by rfl⟩ : syracuseStep 375041 = 281281) B281281
theorem B375059 : Blo 247818 375059 := bstep (se 1 (by rfl) ⟨281294, by rfl⟩ : syracuseStep 375059 = 562589) B562589
theorem B375089 : Blo 247818 375089 := bstep (se 2 (by rfl) ⟨140658, by rfl⟩ : syracuseStep 375089 = 281317) B281317
theorem B375107 : Blo 247818 375107 := bstep (se 1 (by rfl) ⟨281330, by rfl⟩ : syracuseStep 375107 = 562661) B562661
theorem B375137 : Blo 247818 375137 := bstep (se 2 (by rfl) ⟨140676, by rfl⟩ : syracuseStep 375137 = 281353) B281353
theorem B375155 : Blo 247818 375155 := bstep (se 1 (by rfl) ⟨281366, by rfl⟩ : syracuseStep 375155 = 562733) B562733
theorem B375185 : Blo 247818 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B375203 : Blo 247818 375203 := bstep (se 1 (by rfl) ⟨281402, by rfl⟩ : syracuseStep 375203 = 562805) B562805
theorem B375233 : Blo 247818 375233 := bstep (se 2 (by rfl) ⟨140712, by rfl⟩ : syracuseStep 375233 = 281425) B281425
theorem B473539 : Blo 247818 473539 := bstep (se 1 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 473539 = 710309) B710309
theorem B637379 : Blo 247818 637379 := bstep (se 1 (by rfl) ⟨478034, by rfl⟩ : syracuseStep 637379 = 956069) B956069
theorem B375251 : Blo 247818 375251 := bstep (se 1 (by rfl) ⟨281438, by rfl⟩ : syracuseStep 375251 = 562877) B562877
theorem B375281 : Blo 247818 375281 := bstep (se 2 (by rfl) ⟨140730, by rfl⟩ : syracuseStep 375281 = 281461) B281461
theorem B375299 : Blo 247818 375299 := bstep (se 1 (by rfl) ⟨281474, by rfl⟩ : syracuseStep 375299 = 562949) B562949
theorem B375329 : Blo 247818 375329 := bstep (se 2 (by rfl) ⟨140748, by rfl⟩ : syracuseStep 375329 = 281497) B281497
theorem B375347 : Blo 247818 375347 := bstep (se 1 (by rfl) ⟨281510, by rfl⟩ : syracuseStep 375347 = 563021) B563021
theorem B375377 : Blo 247818 375377 := bstep (se 2 (by rfl) ⟨140766, by rfl⟩ : syracuseStep 375377 = 281533) B281533
theorem B375395 : Blo 247818 375395 := bstep (se 1 (by rfl) ⟨281546, by rfl⟩ : syracuseStep 375395 = 563093) B563093
theorem B375425 : Blo 247818 375425 := bstep (se 2 (by rfl) ⟨140784, by rfl⟩ : syracuseStep 375425 = 281569) B281569
theorem B637571 : Blo 247818 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B3029645 : Blo 247818 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B375443 : Blo 247818 375443 := bstep (se 1 (by rfl) ⟨281582, by rfl⟩ : syracuseStep 375443 = 563165) B563165
theorem B1063601 : Blo 247818 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B375473 : Blo 247818 375473 := bstep (se 2 (by rfl) ⟨140802, by rfl⟩ : syracuseStep 375473 = 281605) B281605
theorem B375491 : Blo 247818 375491 := bstep (se 1 (by rfl) ⟨281618, by rfl⟩ : syracuseStep 375491 = 563237) B563237
theorem B375521 : Blo 247818 375521 := bstep (se 2 (by rfl) ⟨140820, by rfl⟩ : syracuseStep 375521 = 281641) B281641
theorem B375539 : Blo 247818 375539 := bstep (se 1 (by rfl) ⟨281654, by rfl⟩ : syracuseStep 375539 = 563309) B563309
theorem B375569 : Blo 247818 375569 := bstep (se 2 (by rfl) ⟨140838, by rfl⟩ : syracuseStep 375569 = 281677) B281677
theorem B604945 : Blo 247818 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B375587 : Blo 247818 375587 := bstep (se 1 (by rfl) ⟨281690, by rfl⟩ : syracuseStep 375587 = 563381) B563381
theorem B375617 : Blo 247818 375617 := bstep (se 2 (by rfl) ⟨140856, by rfl⟩ : syracuseStep 375617 = 281713) B281713
theorem B375635 : Blo 247818 375635 := bstep (se 1 (by rfl) ⟨281726, by rfl⟩ : syracuseStep 375635 = 563453) B563453
theorem B375665 : Blo 247818 375665 := bstep (se 2 (by rfl) ⟨140874, by rfl⟩ : syracuseStep 375665 = 281749) B281749
theorem B473987 : Blo 247818 473987 := bstep (se 1 (by rfl) ⟨355490, by rfl⟩ : syracuseStep 473987 = 710981) B710981
theorem B375683 : Blo 247818 375683 := bstep (se 1 (by rfl) ⟨281762, by rfl⟩ : syracuseStep 375683 = 563525) B563525
theorem B899981 : Blo 247818 899981 := bstep (se 3 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 899981 = 337493) B337493
theorem B375713 : Blo 247818 375713 := bstep (se 2 (by rfl) ⟨140892, by rfl⟩ : syracuseStep 375713 = 281785) B281785
theorem B375731 : Blo 247818 375731 := bstep (se 1 (by rfl) ⟨281798, by rfl⟩ : syracuseStep 375731 = 563597) B563597
theorem B375761 : Blo 247818 375761 := bstep (se 2 (by rfl) ⟨140910, by rfl⟩ : syracuseStep 375761 = 281821) B281821
theorem B375779 : Blo 247818 375779 := bstep (se 1 (by rfl) ⟨281834, by rfl⟩ : syracuseStep 375779 = 563669) B563669
theorem B375809 : Blo 247818 375809 := bstep (se 2 (by rfl) ⟨140928, by rfl⟩ : syracuseStep 375809 = 281857) B281857
theorem B375827 : Blo 247818 375827 := bstep (se 1 (by rfl) ⟨281870, by rfl⟩ : syracuseStep 375827 = 563741) B563741
theorem B375857 : Blo 247818 375857 := bstep (se 2 (by rfl) ⟨140946, by rfl⟩ : syracuseStep 375857 = 281893) B281893
theorem B375875 : Blo 247818 375875 := bstep (se 1 (by rfl) ⟨281906, by rfl⟩ : syracuseStep 375875 = 563813) B563813
theorem B375905 : Blo 247818 375905 := bstep (se 2 (by rfl) ⟨140964, by rfl⟩ : syracuseStep 375905 = 281929) B281929
theorem B1883249 : Blo 247818 1883249 := bstep (se 2 (by rfl) ⟨706218, by rfl⟩ : syracuseStep 1883249 = 1412437) B1412437
theorem B375923 : Blo 247818 375923 := bstep (se 1 (by rfl) ⟨281942, by rfl⟩ : syracuseStep 375923 = 563885) B563885
theorem B375953 : Blo 247818 375953 := bstep (se 2 (by rfl) ⟨140982, by rfl⟩ : syracuseStep 375953 = 281965) B281965
theorem B474275 : Blo 247818 474275 := bstep (se 1 (by rfl) ⟨355706, by rfl⟩ : syracuseStep 474275 = 711413) B711413
theorem B375971 : Blo 247818 375971 := bstep (se 1 (by rfl) ⟨281978, by rfl⟩ : syracuseStep 375971 = 563957) B563957
theorem B376001 : Blo 247818 376001 := bstep (se 2 (by rfl) ⟨141000, by rfl⟩ : syracuseStep 376001 = 282001) B282001
theorem B376019 : Blo 247818 376019 := bstep (se 1 (by rfl) ⟨282014, by rfl⟩ : syracuseStep 376019 = 564029) B564029
theorem B507107 : Blo 247818 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B376049 : Blo 247818 376049 := bstep (se 2 (by rfl) ⟨141018, by rfl⟩ : syracuseStep 376049 = 282037) B282037
theorem B376067 : Blo 247818 376067 := bstep (se 1 (by rfl) ⟨282050, by rfl⟩ : syracuseStep 376067 = 564101) B564101
theorem B376097 : Blo 247818 376097 := bstep (se 2 (by rfl) ⟨141036, by rfl⟩ : syracuseStep 376097 = 282073) B282073
theorem B376115 : Blo 247818 376115 := bstep (se 1 (by rfl) ⟨282086, by rfl⟩ : syracuseStep 376115 = 564173) B564173
theorem B376145 : Blo 247818 376145 := bstep (se 2 (by rfl) ⟨141054, by rfl⟩ : syracuseStep 376145 = 282109) B282109
theorem B376163 : Blo 247818 376163 := bstep (se 1 (by rfl) ⟨282122, by rfl⟩ : syracuseStep 376163 = 564245) B564245
theorem B2014577 : Blo 247818 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B376193 : Blo 247818 376193 := bstep (se 2 (by rfl) ⟨141072, by rfl⟩ : syracuseStep 376193 = 282145) B282145
theorem B376211 : Blo 247818 376211 := bstep (se 1 (by rfl) ⟨282158, by rfl⟩ : syracuseStep 376211 = 564317) B564317
theorem B376241 : Blo 247818 376241 := bstep (se 2 (by rfl) ⟨141090, by rfl⟩ : syracuseStep 376241 = 282181) B282181
theorem B376259 : Blo 247818 376259 := bstep (se 1 (by rfl) ⟨282194, by rfl⟩ : syracuseStep 376259 = 564389) B564389
theorem B376289 : Blo 247818 376289 := bstep (se 2 (by rfl) ⟨141108, by rfl⟩ : syracuseStep 376289 = 282217) B282217
theorem B376307 : Blo 247818 376307 := bstep (se 1 (by rfl) ⟨282230, by rfl⟩ : syracuseStep 376307 = 564461) B564461
theorem B376337 : Blo 247818 376337 := bstep (se 2 (by rfl) ⟨141126, by rfl⟩ : syracuseStep 376337 = 282253) B282253
theorem B376355 : Blo 247818 376355 := bstep (se 1 (by rfl) ⟨282266, by rfl⟩ : syracuseStep 376355 = 564533) B564533
theorem B376385 : Blo 247818 376385 := bstep (se 2 (by rfl) ⟨141144, by rfl⟩ : syracuseStep 376385 = 282289) B282289
theorem B376403 : Blo 247818 376403 := bstep (se 1 (by rfl) ⟨282302, by rfl⟩ : syracuseStep 376403 = 564605) B564605
theorem B1261169 : Blo 247818 1261169 := bstep (se 2 (by rfl) ⟨472938, by rfl⟩ : syracuseStep 1261169 = 945877) B945877
theorem B376433 : Blo 247818 376433 := bstep (se 2 (by rfl) ⟨141162, by rfl⟩ : syracuseStep 376433 = 282325) B282325
theorem B376451 : Blo 247818 376451 := bstep (se 1 (by rfl) ⟨282338, by rfl⟩ : syracuseStep 376451 = 564677) B564677
theorem B343697 : Blo 247818 343697 := bstep (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) B257773
theorem B376481 : Blo 247818 376481 := bstep (se 2 (by rfl) ⟨141180, by rfl⟩ : syracuseStep 376481 = 282361) B282361
theorem B1425059 : Blo 247818 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B376499 : Blo 247818 376499 := bstep (se 1 (by rfl) ⟨282374, by rfl⟩ : syracuseStep 376499 = 564749) B564749
theorem B376529 : Blo 247818 376529 := bstep (se 2 (by rfl) ⟨141198, by rfl⟩ : syracuseStep 376529 = 282397) B282397
theorem B376547 : Blo 247818 376547 := bstep (se 1 (by rfl) ⟨282410, by rfl⟩ : syracuseStep 376547 = 564821) B564821
theorem B376577 : Blo 247818 376577 := bstep (se 2 (by rfl) ⟨141216, by rfl⟩ : syracuseStep 376577 = 282433) B282433
theorem B376595 : Blo 247818 376595 := bstep (se 1 (by rfl) ⟨282446, by rfl⟩ : syracuseStep 376595 = 564893) B564893
theorem B802595 : Blo 247818 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B376625 : Blo 247818 376625 := bstep (se 2 (by rfl) ⟨141234, by rfl⟩ : syracuseStep 376625 = 282469) B282469
theorem B376643 : Blo 247818 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B376673 : Blo 247818 376673 := bstep (se 2 (by rfl) ⟨141252, by rfl⟩ : syracuseStep 376673 = 282505) B282505
theorem B376691 : Blo 247818 376691 := bstep (se 1 (by rfl) ⟨282518, by rfl⟩ : syracuseStep 376691 = 565037) B565037
theorem B376721 : Blo 247818 376721 := bstep (se 2 (by rfl) ⟨141270, by rfl⟩ : syracuseStep 376721 = 282541) B282541
theorem B376739 : Blo 247818 376739 := bstep (se 1 (by rfl) ⟨282554, by rfl⟩ : syracuseStep 376739 = 565109) B565109
theorem B376769 : Blo 247818 376769 := bstep (se 2 (by rfl) ⟨141288, by rfl⟩ : syracuseStep 376769 = 282577) B282577
theorem B376787 : Blo 247818 376787 := bstep (se 1 (by rfl) ⟨282590, by rfl⟩ : syracuseStep 376787 = 565181) B565181
theorem B376817 : Blo 247818 376817 := bstep (se 2 (by rfl) ⟨141306, by rfl⟩ : syracuseStep 376817 = 282613) B282613
theorem B376835 : Blo 247818 376835 := bstep (se 1 (by rfl) ⟨282626, by rfl⟩ : syracuseStep 376835 = 565253) B565253
theorem B376865 : Blo 247818 376865 := bstep (se 2 (by rfl) ⟨141324, by rfl⟩ : syracuseStep 376865 = 282649) B282649
theorem B376883 : Blo 247818 376883 := bstep (se 1 (by rfl) ⟨282662, by rfl⟩ : syracuseStep 376883 = 565325) B565325
theorem B475217 : Blo 247818 475217 := bstep (se 2 (by rfl) ⟨178206, by rfl⟩ : syracuseStep 475217 = 356413) B356413
theorem B376913 : Blo 247818 376913 := bstep (se 2 (by rfl) ⟨141342, by rfl⟩ : syracuseStep 376913 = 282685) B282685
theorem B376931 : Blo 247818 376931 := bstep (se 1 (by rfl) ⟨282698, by rfl⟩ : syracuseStep 376931 = 565397) B565397
theorem B376961 : Blo 247818 376961 := bstep (se 2 (by rfl) ⟨141360, by rfl⟩ : syracuseStep 376961 = 282721) B282721
theorem B1589381 : Blo 247818 1589381 := bstep (se 4 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 1589381 = 298009) B298009
theorem B376979 : Blo 247818 376979 := bstep (se 1 (by rfl) ⟨282734, by rfl⟩ : syracuseStep 376979 = 565469) B565469
theorem B377009 : Blo 247818 377009 := bstep (se 2 (by rfl) ⟨141378, by rfl⟩ : syracuseStep 377009 = 282757) B282757
theorem B377027 : Blo 247818 377027 := bstep (se 1 (by rfl) ⟨282770, by rfl⟩ : syracuseStep 377027 = 565541) B565541
theorem B377057 : Blo 247818 377057 := bstep (se 2 (by rfl) ⟨141396, by rfl⟩ : syracuseStep 377057 = 282793) B282793
theorem B377075 : Blo 247818 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B377105 : Blo 247818 377105 := bstep (se 2 (by rfl) ⟨141414, by rfl⟩ : syracuseStep 377105 = 282829) B282829
theorem B377123 : Blo 247818 377123 := bstep (se 1 (by rfl) ⟨282842, by rfl⟩ : syracuseStep 377123 = 565685) B565685
theorem B377153 : Blo 247818 377153 := bstep (se 2 (by rfl) ⟨141432, by rfl⟩ : syracuseStep 377153 = 282865) B282865
theorem B278851 : Blo 247818 278851 := bstep (se 1 (by rfl) ⟨209138, by rfl⟩ : syracuseStep 278851 = 418277) B418277
theorem B377171 : Blo 247818 377171 := bstep (se 1 (by rfl) ⟨282878, by rfl⟩ : syracuseStep 377171 = 565757) B565757
theorem B377201 : Blo 247818 377201 := bstep (se 2 (by rfl) ⟨141450, by rfl⟩ : syracuseStep 377201 = 282901) B282901
theorem B377219 : Blo 247818 377219 := bstep (se 1 (by rfl) ⟨282914, by rfl⟩ : syracuseStep 377219 = 565829) B565829
theorem B377249 : Blo 247818 377249 := bstep (se 2 (by rfl) ⟨141468, by rfl⟩ : syracuseStep 377249 = 282937) B282937
theorem B377267 : Blo 247818 377267 := bstep (se 1 (by rfl) ⟨282950, by rfl⟩ : syracuseStep 377267 = 565901) B565901
theorem B377297 : Blo 247818 377297 := bstep (se 2 (by rfl) ⟨141486, by rfl⟩ : syracuseStep 377297 = 282973) B282973
theorem B278995 : Blo 247818 278995 := bstep (se 1 (by rfl) ⟨209246, by rfl⟩ : syracuseStep 278995 = 418493) B418493
theorem B377315 : Blo 247818 377315 := bstep (se 1 (by rfl) ⟨282986, by rfl⟩ : syracuseStep 377315 = 565973) B565973
theorem B377345 : Blo 247818 377345 := bstep (se 2 (by rfl) ⟨141504, by rfl⟩ : syracuseStep 377345 = 283009) B283009
theorem B377363 : Blo 247818 377363 := bstep (se 1 (by rfl) ⟨283022, by rfl⟩ : syracuseStep 377363 = 566045) B566045
theorem B377393 : Blo 247818 377393 := bstep (se 2 (by rfl) ⟨141522, by rfl⟩ : syracuseStep 377393 = 283045) B283045
theorem B377411 : Blo 247818 377411 := bstep (se 1 (by rfl) ⟨283058, by rfl⟩ : syracuseStep 377411 = 566117) B566117
theorem B377441 : Blo 247818 377441 := bstep (se 2 (by rfl) ⟨141540, by rfl⟩ : syracuseStep 377441 = 283081) B283081
theorem B279139 : Blo 247818 279139 := bstep (se 1 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 279139 = 418709) B418709
theorem B377459 : Blo 247818 377459 := bstep (se 1 (by rfl) ⟨283094, by rfl⟩ : syracuseStep 377459 = 566189) B566189
theorem B377489 : Blo 247818 377489 := bstep (se 2 (by rfl) ⟨141558, by rfl⟩ : syracuseStep 377489 = 283117) B283117
theorem B377507 : Blo 247818 377507 := bstep (se 1 (by rfl) ⟨283130, by rfl⟩ : syracuseStep 377507 = 566261) B566261
theorem B377537 : Blo 247818 377537 := bstep (se 2 (by rfl) ⟨141576, by rfl⟩ : syracuseStep 377537 = 283153) B283153
theorem B377555 : Blo 247818 377555 := bstep (se 1 (by rfl) ⟨283166, by rfl⟩ : syracuseStep 377555 = 566333) B566333
theorem B377585 : Blo 247818 377585 := bstep (se 2 (by rfl) ⟨141594, by rfl⟩ : syracuseStep 377585 = 283189) B283189
theorem B279283 : Blo 247818 279283 := bstep (se 1 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 279283 = 418925) B418925
theorem B377603 : Blo 247818 377603 := bstep (se 1 (by rfl) ⟨283202, by rfl⟩ : syracuseStep 377603 = 566405) B566405
theorem B377633 : Blo 247818 377633 := bstep (se 2 (by rfl) ⟨141612, by rfl⟩ : syracuseStep 377633 = 283225) B283225
theorem B377651 : Blo 247818 377651 := bstep (se 1 (by rfl) ⟨283238, by rfl⟩ : syracuseStep 377651 = 566477) B566477
theorem B377681 : Blo 247818 377681 := bstep (se 2 (by rfl) ⟨141630, by rfl⟩ : syracuseStep 377681 = 283261) B283261
theorem B377699 : Blo 247818 377699 := bstep (se 1 (by rfl) ⟨283274, by rfl⟩ : syracuseStep 377699 = 566549) B566549
theorem B279427 : Blo 247818 279427 := bstep (se 1 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 279427 = 419141) B419141
theorem B508835 : Blo 247818 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B476113 : Blo 247818 476113 := bstep (se 2 (by rfl) ⟨178542, by rfl⟩ : syracuseStep 476113 = 357085) B357085
theorem B508931 : Blo 247818 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B836621 : Blo 247818 836621 := bstep (se 3 (by rfl) ⟨156866, by rfl⟩ : syracuseStep 836621 = 313733) B313733
theorem B279571 : Blo 247818 279571 := bstep (se 1 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 279571 = 419357) B419357
theorem B1262627 : Blo 247818 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B836675 : Blo 247818 836675 := bstep (se 1 (by rfl) ⟨627506, by rfl⟩ : syracuseStep 836675 = 1255013) B1255013
theorem B1066061 : Blo 247818 1066061 := bstep (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) B399773
theorem B476273 : Blo 247818 476273 := bstep (se 2 (by rfl) ⟨178602, by rfl⟩ : syracuseStep 476273 = 357205) B357205
theorem B279715 : Blo 247818 279715 := bstep (se 1 (by rfl) ⟨209786, by rfl⟩ : syracuseStep 279715 = 419573) B419573
theorem B705763 : Blo 247818 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B705809 : Blo 247818 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B279859 : Blo 247818 279859 := bstep (se 1 (by rfl) ⟨209894, by rfl⟩ : syracuseStep 279859 = 419789) B419789
theorem B836945 : Blo 247818 836945 := bstep (se 2 (by rfl) ⟨313854, by rfl⟩ : syracuseStep 836945 = 627709) B627709
theorem B378209 : Blo 247818 378209 := bstep (se 2 (by rfl) ⟨141828, by rfl⟩ : syracuseStep 378209 = 283657) B283657
theorem B280003 : Blo 247818 280003 := bstep (se 1 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 280003 = 420005) B420005
theorem B476675 : Blo 247818 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B280147 : Blo 247818 280147 := bstep (se 1 (by rfl) ⟨210110, by rfl⟩ : syracuseStep 280147 = 420221) B420221
theorem B280291 : Blo 247818 280291 := bstep (se 1 (by rfl) ⟨210218, by rfl⟩ : syracuseStep 280291 = 420437) B420437
theorem B1263437 : Blo 247818 1263437 := bstep (se 3 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 1263437 = 473789) B473789
theorem B837485 : Blo 247818 837485 := bstep (se 3 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 837485 = 314057) B314057
theorem B280435 : Blo 247818 280435 := bstep (se 1 (by rfl) ⟨210326, by rfl⟩ : syracuseStep 280435 = 420653) B420653
theorem B837539 : Blo 247818 837539 := bstep (se 1 (by rfl) ⟨628154, by rfl⟩ : syracuseStep 837539 = 1256309) B1256309
theorem B280579 : Blo 247818 280579 := bstep (se 1 (by rfl) ⟨210434, by rfl⟩ : syracuseStep 280579 = 420869) B420869
theorem B247827 : Blo 247818 247827 := bstep (se 1 (by rfl) ⟨185870, by rfl⟩ : syracuseStep 247827 = 371741) B371741
theorem B247843 : Blo 247818 247843 := bstep (se 1 (by rfl) ⟨185882, by rfl⟩ : syracuseStep 247843 = 371765) B371765
theorem B247859 : Blo 247818 247859 := bstep (se 1 (by rfl) ⟨185894, by rfl⟩ : syracuseStep 247859 = 371789) B371789
theorem B247875 : Blo 247818 247875 := bstep (se 1 (by rfl) ⟨185906, by rfl⟩ : syracuseStep 247875 = 371813) B371813
theorem B247891 : Blo 247818 247891 := bstep (se 1 (by rfl) ⟨185918, by rfl⟩ : syracuseStep 247891 = 371837) B371837
theorem B247907 : Blo 247818 247907 := bstep (se 1 (by rfl) ⟨185930, by rfl⟩ : syracuseStep 247907 = 371861) B371861
theorem B247923 : Blo 247818 247923 := bstep (se 1 (by rfl) ⟨185942, by rfl⟩ : syracuseStep 247923 = 371885) B371885
theorem B247939 : Blo 247818 247939 := bstep (se 1 (by rfl) ⟨185954, by rfl⟩ : syracuseStep 247939 = 371909) B371909
theorem B247955 : Blo 247818 247955 := bstep (se 1 (by rfl) ⟨185966, by rfl⟩ : syracuseStep 247955 = 371933) B371933
theorem B280723 : Blo 247818 280723 := bstep (se 1 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 280723 = 421085) B421085
theorem B247971 : Blo 247818 247971 := bstep (se 1 (by rfl) ⟨185978, by rfl⟩ : syracuseStep 247971 = 371957) B371957
theorem B837809 : Blo 247818 837809 := bstep (se 2 (by rfl) ⟨314178, by rfl⟩ : syracuseStep 837809 = 628357) B628357
theorem B247987 : Blo 247818 247987 := bstep (se 1 (by rfl) ⟨185990, by rfl⟩ : syracuseStep 247987 = 371981) B371981
theorem B248003 : Blo 247818 248003 := bstep (se 1 (by rfl) ⟨186002, by rfl⟩ : syracuseStep 248003 = 372005) B372005
theorem B248019 : Blo 247818 248019 := bstep (se 1 (by rfl) ⟨186014, by rfl⟩ : syracuseStep 248019 = 372029) B372029
theorem B248035 : Blo 247818 248035 := bstep (se 1 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 248035 = 372053) B372053
theorem B248051 : Blo 247818 248051 := bstep (se 1 (by rfl) ⟨186038, by rfl⟩ : syracuseStep 248051 = 372077) B372077
theorem B248067 : Blo 247818 248067 := bstep (se 1 (by rfl) ⟨186050, by rfl⟩ : syracuseStep 248067 = 372101) B372101
theorem B248083 : Blo 247818 248083 := bstep (se 1 (by rfl) ⟨186062, by rfl⟩ : syracuseStep 248083 = 372125) B372125
theorem B379169 : Blo 247818 379169 := bstep (se 2 (by rfl) ⟨142188, by rfl⟩ : syracuseStep 379169 = 284377) B284377
theorem B248099 : Blo 247818 248099 := bstep (se 1 (by rfl) ⟨186074, by rfl⟩ : syracuseStep 248099 = 372149) B372149
theorem B280867 : Blo 247818 280867 := bstep (se 1 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 280867 = 421301) B421301
theorem B1624369 : Blo 247818 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B248115 : Blo 247818 248115 := bstep (se 1 (by rfl) ⟨186086, by rfl⟩ : syracuseStep 248115 = 372173) B372173
theorem B248131 : Blo 247818 248131 := bstep (se 1 (by rfl) ⟨186098, by rfl⟩ : syracuseStep 248131 = 372197) B372197
theorem B248147 : Blo 247818 248147 := bstep (se 1 (by rfl) ⟨186110, by rfl⟩ : syracuseStep 248147 = 372221) B372221
theorem B248163 : Blo 247818 248163 := bstep (se 1 (by rfl) ⟨186122, by rfl⟩ : syracuseStep 248163 = 372245) B372245
theorem B1198435 : Blo 247818 1198435 := bstep (se 1 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 1198435 = 1797653) B1797653
theorem B1067377 : Blo 247818 1067377 := bstep (se 2 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 1067377 = 800533) B800533
theorem B248179 : Blo 247818 248179 := bstep (se 1 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 248179 = 372269) B372269
theorem B248195 : Blo 247818 248195 := bstep (se 1 (by rfl) ⟨186146, by rfl⟩ : syracuseStep 248195 = 372293) B372293
theorem B477571 : Blo 247818 477571 := bstep (se 1 (by rfl) ⟨358178, by rfl⟩ : syracuseStep 477571 = 716357) B716357
theorem B805261 : Blo 247818 805261 := bstep (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) B301973
theorem B248211 : Blo 247818 248211 := bstep (se 1 (by rfl) ⟨186158, by rfl⟩ : syracuseStep 248211 = 372317) B372317
theorem B248227 : Blo 247818 248227 := bstep (se 1 (by rfl) ⟨186170, by rfl⟩ : syracuseStep 248227 = 372341) B372341
theorem B248243 : Blo 247818 248243 := bstep (se 1 (by rfl) ⟨186182, by rfl⟩ : syracuseStep 248243 = 372365) B372365
theorem B281011 : Blo 247818 281011 := bstep (se 1 (by rfl) ⟨210758, by rfl⟩ : syracuseStep 281011 = 421517) B421517
theorem B248259 : Blo 247818 248259 := bstep (se 1 (by rfl) ⟨186194, by rfl⟩ : syracuseStep 248259 = 372389) B372389
theorem B248275 : Blo 247818 248275 := bstep (se 1 (by rfl) ⟨186206, by rfl⟩ : syracuseStep 248275 = 372413) B372413
theorem B248291 : Blo 247818 248291 := bstep (se 1 (by rfl) ⟨186218, by rfl⟩ : syracuseStep 248291 = 372437) B372437
theorem B248307 : Blo 247818 248307 := bstep (se 1 (by rfl) ⟨186230, by rfl⟩ : syracuseStep 248307 = 372461) B372461
theorem B248323 : Blo 247818 248323 := bstep (se 1 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 248323 = 372485) B372485
theorem B248339 : Blo 247818 248339 := bstep (se 1 (by rfl) ⟨186254, by rfl⟩ : syracuseStep 248339 = 372509) B372509
theorem B477731 : Blo 247818 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B248355 : Blo 247818 248355 := bstep (se 1 (by rfl) ⟨186266, by rfl⟩ : syracuseStep 248355 = 372533) B372533
theorem B248371 : Blo 247818 248371 := bstep (se 1 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 248371 = 372557) B372557
theorem B248387 : Blo 247818 248387 := bstep (se 1 (by rfl) ⟨186290, by rfl⟩ : syracuseStep 248387 = 372581) B372581
theorem B281155 : Blo 247818 281155 := bstep (se 1 (by rfl) ⟨210866, by rfl⟩ : syracuseStep 281155 = 421733) B421733
theorem B248403 : Blo 247818 248403 := bstep (se 1 (by rfl) ⟨186302, by rfl⟩ : syracuseStep 248403 = 372605) B372605
theorem B248419 : Blo 247818 248419 := bstep (se 1 (by rfl) ⟨186314, by rfl⟩ : syracuseStep 248419 = 372629) B372629
theorem B477809 : Blo 247818 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B248435 : Blo 247818 248435 := bstep (se 1 (by rfl) ⟨186326, by rfl⟩ : syracuseStep 248435 = 372653) B372653
theorem B248451 : Blo 247818 248451 := bstep (se 1 (by rfl) ⟨186338, by rfl⟩ : syracuseStep 248451 = 372677) B372677
theorem B248467 : Blo 247818 248467 := bstep (se 1 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 248467 = 372701) B372701
theorem B248483 : Blo 247818 248483 := bstep (se 1 (by rfl) ⟨186362, by rfl⟩ : syracuseStep 248483 = 372725) B372725
theorem B248499 : Blo 247818 248499 := bstep (se 1 (by rfl) ⟨186374, by rfl⟩ : syracuseStep 248499 = 372749) B372749
theorem B707267 : Blo 247818 707267 := bstep (se 1 (by rfl) ⟨530450, by rfl⟩ : syracuseStep 707267 = 1060901) B1060901
theorem B248515 : Blo 247818 248515 := bstep (se 1 (by rfl) ⟨186386, by rfl⟩ : syracuseStep 248515 = 372773) B372773
theorem B838349 : Blo 247818 838349 := bstep (se 3 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 838349 = 314381) B314381
theorem B674509 : Blo 247818 674509 := bstep (se 3 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 674509 = 252941) B252941
theorem B248531 : Blo 247818 248531 := bstep (se 1 (by rfl) ⟨186398, by rfl⟩ : syracuseStep 248531 = 372797) B372797
theorem B281299 : Blo 247818 281299 := bstep (se 1 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 281299 = 421949) B421949
theorem B248547 : Blo 247818 248547 := bstep (se 1 (by rfl) ⟨186410, by rfl⟩ : syracuseStep 248547 = 372821) B372821
theorem B248563 : Blo 247818 248563 := bstep (se 1 (by rfl) ⟨186422, by rfl⟩ : syracuseStep 248563 = 372845) B372845
theorem B838403 : Blo 247818 838403 := bstep (se 1 (by rfl) ⟨628802, by rfl⟩ : syracuseStep 838403 = 1257605) B1257605
theorem B248579 : Blo 247818 248579 := bstep (se 1 (by rfl) ⟨186434, by rfl⟩ : syracuseStep 248579 = 372869) B372869
theorem B248595 : Blo 247818 248595 := bstep (se 1 (by rfl) ⟨186446, by rfl⟩ : syracuseStep 248595 = 372893) B372893
theorem B248611 : Blo 247818 248611 := bstep (se 1 (by rfl) ⟨186458, by rfl⟩ : syracuseStep 248611 = 372917) B372917
theorem B248627 : Blo 247818 248627 := bstep (se 1 (by rfl) ⟨186470, by rfl⟩ : syracuseStep 248627 = 372941) B372941
theorem B248643 : Blo 247818 248643 := bstep (se 1 (by rfl) ⟨186482, by rfl⟩ : syracuseStep 248643 = 372965) B372965
theorem B1428293 : Blo 247818 1428293 := bstep (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) B267805
theorem B1526597 : Blo 247818 1526597 := bstep (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) B286237
theorem B248659 : Blo 247818 248659 := bstep (se 1 (by rfl) ⟨186494, by rfl⟩ : syracuseStep 248659 = 372989) B372989
theorem B248675 : Blo 247818 248675 := bstep (se 1 (by rfl) ⟨186506, by rfl⟩ : syracuseStep 248675 = 373013) B373013
theorem B281443 : Blo 247818 281443 := bstep (se 1 (by rfl) ⟨211082, by rfl⟩ : syracuseStep 281443 = 422165) B422165
theorem B4049777 : Blo 247818 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B248691 : Blo 247818 248691 := bstep (se 1 (by rfl) ⟨186518, by rfl⟩ : syracuseStep 248691 = 373037) B373037
theorem B248707 : Blo 247818 248707 := bstep (se 1 (by rfl) ⟨186530, by rfl⟩ : syracuseStep 248707 = 373061) B373061
theorem B248723 : Blo 247818 248723 := bstep (se 1 (by rfl) ⟨186542, by rfl⟩ : syracuseStep 248723 = 373085) B373085
theorem B314275 : Blo 247818 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B248739 : Blo 247818 248739 := bstep (se 1 (by rfl) ⟨186554, by rfl⟩ : syracuseStep 248739 = 373109) B373109
theorem B248755 : Blo 247818 248755 := bstep (se 1 (by rfl) ⟨186566, by rfl⟩ : syracuseStep 248755 = 373133) B373133
theorem B248771 : Blo 247818 248771 := bstep (se 1 (by rfl) ⟨186578, by rfl⟩ : syracuseStep 248771 = 373157) B373157
theorem B248787 : Blo 247818 248787 := bstep (se 1 (by rfl) ⟨186590, by rfl⟩ : syracuseStep 248787 = 373181) B373181
theorem B248803 : Blo 247818 248803 := bstep (se 1 (by rfl) ⟨186602, by rfl⟩ : syracuseStep 248803 = 373205) B373205
theorem B248819 : Blo 247818 248819 := bstep (se 1 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 248819 = 373229) B373229
theorem B281587 : Blo 247818 281587 := bstep (se 1 (by rfl) ⟨211190, by rfl⟩ : syracuseStep 281587 = 422381) B422381
theorem B314371 : Blo 247818 314371 := bstep (se 1 (by rfl) ⟨235778, by rfl⟩ : syracuseStep 314371 = 471557) B471557
theorem B248835 : Blo 247818 248835 := bstep (se 1 (by rfl) ⟨186626, by rfl⟩ : syracuseStep 248835 = 373253) B373253
theorem B838673 : Blo 247818 838673 := bstep (se 2 (by rfl) ⟨314502, by rfl⟩ : syracuseStep 838673 = 629005) B629005
theorem B248851 : Blo 247818 248851 := bstep (se 1 (by rfl) ⟨186638, by rfl⟩ : syracuseStep 248851 = 373277) B373277
theorem B248867 : Blo 247818 248867 := bstep (se 1 (by rfl) ⟨186650, by rfl⟩ : syracuseStep 248867 = 373301) B373301
theorem B248883 : Blo 247818 248883 := bstep (se 1 (by rfl) ⟨186662, by rfl⟩ : syracuseStep 248883 = 373325) B373325
theorem B248899 : Blo 247818 248899 := bstep (se 1 (by rfl) ⟨186674, by rfl⟩ : syracuseStep 248899 = 373349) B373349
theorem B248915 : Blo 247818 248915 := bstep (se 1 (by rfl) ⟨186686, by rfl⟩ : syracuseStep 248915 = 373373) B373373
theorem B248931 : Blo 247818 248931 := bstep (se 1 (by rfl) ⟨186698, by rfl⟩ : syracuseStep 248931 = 373397) B373397
theorem B248947 : Blo 247818 248947 := bstep (se 1 (by rfl) ⟨186710, by rfl⟩ : syracuseStep 248947 = 373421) B373421
theorem B248963 : Blo 247818 248963 := bstep (se 1 (by rfl) ⟨186722, by rfl⟩ : syracuseStep 248963 = 373445) B373445
theorem B281731 : Blo 247818 281731 := bstep (se 1 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 281731 = 422597) B422597
theorem B248979 : Blo 247818 248979 := bstep (se 1 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 248979 = 373469) B373469
theorem B248995 : Blo 247818 248995 := bstep (se 1 (by rfl) ⟨186746, by rfl⟩ : syracuseStep 248995 = 373493) B373493
theorem B249011 : Blo 247818 249011 := bstep (se 1 (by rfl) ⟨186758, by rfl⟩ : syracuseStep 249011 = 373517) B373517
theorem B249027 : Blo 247818 249027 := bstep (se 1 (by rfl) ⟨186770, by rfl⟩ : syracuseStep 249027 = 373541) B373541
theorem B249043 : Blo 247818 249043 := bstep (se 1 (by rfl) ⟨186782, by rfl⟩ : syracuseStep 249043 = 373565) B373565
theorem B249059 : Blo 247818 249059 := bstep (se 1 (by rfl) ⟨186794, by rfl⟩ : syracuseStep 249059 = 373589) B373589
theorem B249075 : Blo 247818 249075 := bstep (se 1 (by rfl) ⟨186806, by rfl⟩ : syracuseStep 249075 = 373613) B373613
theorem B249091 : Blo 247818 249091 := bstep (se 1 (by rfl) ⟨186818, by rfl⟩ : syracuseStep 249091 = 373637) B373637
theorem B1592581 : Blo 247818 1592581 := bstep (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) B298609
theorem B1428749 : Blo 247818 1428749 := bstep (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) B535781
theorem B281875 : Blo 247818 281875 := bstep (se 1 (by rfl) ⟨211406, by rfl⟩ : syracuseStep 281875 = 422813) B422813
theorem B249107 : Blo 247818 249107 := bstep (se 1 (by rfl) ⟨186830, by rfl⟩ : syracuseStep 249107 = 373661) B373661
theorem B249123 : Blo 247818 249123 := bstep (se 1 (by rfl) ⟨186842, by rfl⟩ : syracuseStep 249123 = 373685) B373685
theorem B249139 : Blo 247818 249139 := bstep (se 1 (by rfl) ⟨186854, by rfl⟩ : syracuseStep 249139 = 373709) B373709
theorem B249155 : Blo 247818 249155 := bstep (se 1 (by rfl) ⟨186866, by rfl⟩ : syracuseStep 249155 = 373733) B373733
theorem B249171 : Blo 247818 249171 := bstep (se 1 (by rfl) ⟨186878, by rfl⟩ : syracuseStep 249171 = 373757) B373757
theorem B249187 : Blo 247818 249187 := bstep (se 1 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 249187 = 373781) B373781
theorem B249203 : Blo 247818 249203 := bstep (se 1 (by rfl) ⟨186902, by rfl⟩ : syracuseStep 249203 = 373805) B373805
theorem B249219 : Blo 247818 249219 := bstep (se 1 (by rfl) ⟨186914, by rfl⟩ : syracuseStep 249219 = 373829) B373829
theorem B2280845 : Blo 247818 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B249235 : Blo 247818 249235 := bstep (se 1 (by rfl) ⟨186926, by rfl⟩ : syracuseStep 249235 = 373853) B373853
theorem B249251 : Blo 247818 249251 := bstep (se 1 (by rfl) ⟨186938, by rfl⟩ : syracuseStep 249251 = 373877) B373877
theorem B282019 : Blo 247818 282019 := bstep (se 1 (by rfl) ⟨211514, by rfl⟩ : syracuseStep 282019 = 423029) B423029
theorem B249267 : Blo 247818 249267 := bstep (se 1 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 249267 = 373901) B373901
theorem B249283 : Blo 247818 249283 := bstep (se 1 (by rfl) ⟨186962, by rfl⟩ : syracuseStep 249283 = 373925) B373925
theorem B249299 : Blo 247818 249299 := bstep (se 1 (by rfl) ⟨186974, by rfl⟩ : syracuseStep 249299 = 373949) B373949
theorem B249315 : Blo 247818 249315 := bstep (se 1 (by rfl) ⟨186986, by rfl⟩ : syracuseStep 249315 = 373973) B373973
theorem B314867 : Blo 247818 314867 := bstep (se 1 (by rfl) ⟨236150, by rfl⟩ : syracuseStep 314867 = 472301) B472301
theorem B249331 : Blo 247818 249331 := bstep (se 1 (by rfl) ⟨186998, by rfl⟩ : syracuseStep 249331 = 373997) B373997
theorem B249347 : Blo 247818 249347 := bstep (se 1 (by rfl) ⟨187010, by rfl⟩ : syracuseStep 249347 = 374021) B374021
theorem B249363 : Blo 247818 249363 := bstep (se 1 (by rfl) ⟨187022, by rfl⟩ : syracuseStep 249363 = 374045) B374045
theorem B249379 : Blo 247818 249379 := bstep (se 1 (by rfl) ⟨187034, by rfl⟩ : syracuseStep 249379 = 374069) B374069
theorem B839213 : Blo 247818 839213 := bstep (se 3 (by rfl) ⟨157352, by rfl⟩ : syracuseStep 839213 = 314705) B314705
theorem B249395 : Blo 247818 249395 := bstep (se 1 (by rfl) ⟨187046, by rfl⟩ : syracuseStep 249395 = 374093) B374093
theorem B282163 : Blo 247818 282163 := bstep (se 1 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 282163 = 423245) B423245
theorem B249411 : Blo 247818 249411 := bstep (se 1 (by rfl) ⟨187058, by rfl⟩ : syracuseStep 249411 = 374117) B374117
theorem B249427 : Blo 247818 249427 := bstep (se 1 (by rfl) ⟨187070, by rfl⟩ : syracuseStep 249427 = 374141) B374141
theorem B839267 : Blo 247818 839267 := bstep (se 1 (by rfl) ⟨629450, by rfl⟩ : syracuseStep 839267 = 1258901) B1258901
theorem B249443 : Blo 247818 249443 := bstep (se 1 (by rfl) ⟨187082, by rfl⟩ : syracuseStep 249443 = 374165) B374165
theorem B4247153 : Blo 247818 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B249459 : Blo 247818 249459 := bstep (se 1 (by rfl) ⟨187094, by rfl⟩ : syracuseStep 249459 = 374189) B374189
theorem B249475 : Blo 247818 249475 := bstep (se 1 (by rfl) ⟨187106, by rfl⟩ : syracuseStep 249475 = 374213) B374213
theorem B249491 : Blo 247818 249491 := bstep (se 1 (by rfl) ⟨187118, by rfl⟩ : syracuseStep 249491 = 374237) B374237
theorem B249507 : Blo 247818 249507 := bstep (se 1 (by rfl) ⟨187130, by rfl⟩ : syracuseStep 249507 = 374261) B374261
theorem B249523 : Blo 247818 249523 := bstep (se 1 (by rfl) ⟨187142, by rfl⟩ : syracuseStep 249523 = 374285) B374285
theorem B249539 : Blo 247818 249539 := bstep (se 1 (by rfl) ⟨187154, by rfl⟩ : syracuseStep 249539 = 374309) B374309
theorem B282307 : Blo 247818 282307 := bstep (se 1 (by rfl) ⟨211730, by rfl⟩ : syracuseStep 282307 = 423461) B423461
theorem B249555 : Blo 247818 249555 := bstep (se 1 (by rfl) ⟨187166, by rfl⟩ : syracuseStep 249555 = 374333) B374333
theorem B380641 : Blo 247818 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B249571 : Blo 247818 249571 := bstep (se 1 (by rfl) ⟨187178, by rfl⟩ : syracuseStep 249571 = 374357) B374357
theorem B249587 : Blo 247818 249587 := bstep (se 1 (by rfl) ⟨187190, by rfl⟩ : syracuseStep 249587 = 374381) B374381
theorem B249603 : Blo 247818 249603 := bstep (se 1 (by rfl) ⟨187202, by rfl⟩ : syracuseStep 249603 = 374405) B374405
theorem B249619 : Blo 247818 249619 := bstep (se 1 (by rfl) ⟨187214, by rfl⟩ : syracuseStep 249619 = 374429) B374429
theorem B249635 : Blo 247818 249635 := bstep (se 1 (by rfl) ⟨187226, by rfl⟩ : syracuseStep 249635 = 374453) B374453
theorem B249651 : Blo 247818 249651 := bstep (se 1 (by rfl) ⟨187238, by rfl⟩ : syracuseStep 249651 = 374477) B374477
theorem B249667 : Blo 247818 249667 := bstep (se 1 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 249667 = 374501) B374501
theorem B806723 : Blo 247818 806723 := bstep (se 1 (by rfl) ⟨605042, by rfl⟩ : syracuseStep 806723 = 1210085) B1210085
theorem B249683 : Blo 247818 249683 := bstep (se 1 (by rfl) ⟨187262, by rfl⟩ : syracuseStep 249683 = 374525) B374525
theorem B282451 : Blo 247818 282451 := bstep (se 1 (by rfl) ⟨211838, by rfl⟩ : syracuseStep 282451 = 423677) B423677
theorem B249699 : Blo 247818 249699 := bstep (se 1 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 249699 = 374549) B374549
theorem B839537 : Blo 247818 839537 := bstep (se 2 (by rfl) ⟨314826, by rfl⟩ : syracuseStep 839537 = 629653) B629653
theorem B249715 : Blo 247818 249715 := bstep (se 1 (by rfl) ⟨187286, by rfl⟩ : syracuseStep 249715 = 374573) B374573
theorem B249731 : Blo 247818 249731 := bstep (se 1 (by rfl) ⟨187298, by rfl⟩ : syracuseStep 249731 = 374597) B374597
theorem B708497 : Blo 247818 708497 := bstep (se 2 (by rfl) ⟨265686, by rfl⟩ : syracuseStep 708497 = 531373) B531373
theorem B249747 : Blo 247818 249747 := bstep (se 1 (by rfl) ⟨187310, by rfl⟩ : syracuseStep 249747 = 374621) B374621
theorem B249763 : Blo 247818 249763 := bstep (se 1 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 249763 = 374645) B374645
theorem B249779 : Blo 247818 249779 := bstep (se 1 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 249779 = 374669) B374669
theorem B249795 : Blo 247818 249795 := bstep (se 1 (by rfl) ⟨187346, by rfl⟩ : syracuseStep 249795 = 374693) B374693
theorem B249811 : Blo 247818 249811 := bstep (se 1 (by rfl) ⟨187358, by rfl⟩ : syracuseStep 249811 = 374717) B374717
theorem B249827 : Blo 247818 249827 := bstep (se 1 (by rfl) ⟨187370, by rfl⟩ : syracuseStep 249827 = 374741) B374741
theorem B282595 : Blo 247818 282595 := bstep (se 1 (by rfl) ⟨211946, by rfl⟩ : syracuseStep 282595 = 423893) B423893
theorem B249843 : Blo 247818 249843 := bstep (se 1 (by rfl) ⟨187382, by rfl⟩ : syracuseStep 249843 = 374765) B374765
theorem B249859 : Blo 247818 249859 := bstep (se 1 (by rfl) ⟨187394, by rfl⟩ : syracuseStep 249859 = 374789) B374789
theorem B249875 : Blo 247818 249875 := bstep (se 1 (by rfl) ⟨187406, by rfl⟩ : syracuseStep 249875 = 374813) B374813
theorem B249891 : Blo 247818 249891 := bstep (se 1 (by rfl) ⟨187418, by rfl⟩ : syracuseStep 249891 = 374837) B374837
theorem B249907 : Blo 247818 249907 := bstep (se 1 (by rfl) ⟨187430, by rfl⟩ : syracuseStep 249907 = 374861) B374861
theorem B249923 : Blo 247818 249923 := bstep (se 1 (by rfl) ⟨187442, by rfl⟩ : syracuseStep 249923 = 374885) B374885
theorem B249939 : Blo 247818 249939 := bstep (se 1 (by rfl) ⟨187454, by rfl⟩ : syracuseStep 249939 = 374909) B374909
theorem B249955 : Blo 247818 249955 := bstep (se 1 (by rfl) ⟨187466, by rfl⟩ : syracuseStep 249955 = 374933) B374933
theorem B249971 : Blo 247818 249971 := bstep (se 1 (by rfl) ⟨187478, by rfl⟩ : syracuseStep 249971 = 374957) B374957
theorem B282739 : Blo 247818 282739 := bstep (se 1 (by rfl) ⟨212054, by rfl⟩ : syracuseStep 282739 = 424109) B424109
theorem B249987 : Blo 247818 249987 := bstep (se 1 (by rfl) ⟨187490, by rfl⟩ : syracuseStep 249987 = 374981) B374981
theorem B250003 : Blo 247818 250003 := bstep (se 1 (by rfl) ⟨187502, by rfl⟩ : syracuseStep 250003 = 375005) B375005
theorem B250019 : Blo 247818 250019 := bstep (se 1 (by rfl) ⟨187514, by rfl⟩ : syracuseStep 250019 = 375029) B375029
theorem B315571 : Blo 247818 315571 := bstep (se 1 (by rfl) ⟨236678, by rfl⟩ : syracuseStep 315571 = 473357) B473357
theorem B250035 : Blo 247818 250035 := bstep (se 1 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 250035 = 375053) B375053
theorem B250051 : Blo 247818 250051 := bstep (se 1 (by rfl) ⟨187538, by rfl⟩ : syracuseStep 250051 = 375077) B375077
theorem B2838725 : Blo 247818 2838725 := bstep (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) B532261
theorem B250067 : Blo 247818 250067 := bstep (se 1 (by rfl) ⟨187550, by rfl⟩ : syracuseStep 250067 = 375101) B375101
theorem B250083 : Blo 247818 250083 := bstep (se 1 (by rfl) ⟨187562, by rfl⟩ : syracuseStep 250083 = 375125) B375125
theorem B1921265 : Blo 247818 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B250099 : Blo 247818 250099 := bstep (se 1 (by rfl) ⟨187574, by rfl⟩ : syracuseStep 250099 = 375149) B375149
theorem B250115 : Blo 247818 250115 := bstep (se 1 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 250115 = 375173) B375173
theorem B282883 : Blo 247818 282883 := bstep (se 1 (by rfl) ⟨212162, by rfl⟩ : syracuseStep 282883 = 424325) B424325
theorem B315667 : Blo 247818 315667 := bstep (se 1 (by rfl) ⟨236750, by rfl⟩ : syracuseStep 315667 = 473501) B473501
theorem B250131 : Blo 247818 250131 := bstep (se 1 (by rfl) ⟨187598, by rfl⟩ : syracuseStep 250131 = 375197) B375197
theorem B250147 : Blo 247818 250147 := bstep (se 1 (by rfl) ⟨187610, by rfl⟩ : syracuseStep 250147 = 375221) B375221
theorem B250163 : Blo 247818 250163 := bstep (se 1 (by rfl) ⟨187622, by rfl⟩ : syracuseStep 250163 = 375245) B375245
theorem B250179 : Blo 247818 250179 := bstep (se 1 (by rfl) ⟨187634, by rfl⟩ : syracuseStep 250179 = 375269) B375269
theorem B250195 : Blo 247818 250195 := bstep (se 1 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 250195 = 375293) B375293
theorem B250211 : Blo 247818 250211 := bstep (se 1 (by rfl) ⟨187658, by rfl⟩ : syracuseStep 250211 = 375317) B375317
theorem B250227 : Blo 247818 250227 := bstep (se 1 (by rfl) ⟨187670, by rfl⟩ : syracuseStep 250227 = 375341) B375341
theorem B250243 : Blo 247818 250243 := bstep (se 1 (by rfl) ⟨187682, by rfl⟩ : syracuseStep 250243 = 375365) B375365
theorem B840077 : Blo 247818 840077 := bstep (se 3 (by rfl) ⟨157514, by rfl⟩ : syracuseStep 840077 = 315029) B315029
theorem B250259 : Blo 247818 250259 := bstep (se 1 (by rfl) ⟨187694, by rfl⟩ : syracuseStep 250259 = 375389) B375389
theorem B283027 : Blo 247818 283027 := bstep (se 1 (by rfl) ⟨212270, by rfl⟩ : syracuseStep 283027 = 424541) B424541
theorem B250275 : Blo 247818 250275 := bstep (se 1 (by rfl) ⟨187706, by rfl⟩ : syracuseStep 250275 = 375413) B375413
theorem B250291 : Blo 247818 250291 := bstep (se 1 (by rfl) ⟨187718, by rfl⟩ : syracuseStep 250291 = 375437) B375437
theorem B840131 : Blo 247818 840131 := bstep (se 1 (by rfl) ⟨630098, by rfl⟩ : syracuseStep 840131 = 1260197) B1260197
theorem B250307 : Blo 247818 250307 := bstep (se 1 (by rfl) ⟨187730, by rfl⟩ : syracuseStep 250307 = 375461) B375461
theorem B250323 : Blo 247818 250323 := bstep (se 1 (by rfl) ⟨187742, by rfl⟩ : syracuseStep 250323 = 375485) B375485
theorem B250339 : Blo 247818 250339 := bstep (se 1 (by rfl) ⟨187754, by rfl⟩ : syracuseStep 250339 = 375509) B375509
theorem B250355 : Blo 247818 250355 := bstep (se 1 (by rfl) ⟨187766, by rfl⟩ : syracuseStep 250355 = 375533) B375533
theorem B250371 : Blo 247818 250371 := bstep (se 1 (by rfl) ⟨187778, by rfl⟩ : syracuseStep 250371 = 375557) B375557
theorem B250387 : Blo 247818 250387 := bstep (se 1 (by rfl) ⟨187790, by rfl⟩ : syracuseStep 250387 = 375581) B375581
theorem B250403 : Blo 247818 250403 := bstep (se 1 (by rfl) ⟨187802, by rfl⟩ : syracuseStep 250403 = 375605) B375605
theorem B283171 : Blo 247818 283171 := bstep (se 1 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 283171 = 424757) B424757
theorem B250419 : Blo 247818 250419 := bstep (se 1 (by rfl) ⟨187814, by rfl⟩ : syracuseStep 250419 = 375629) B375629
theorem B250435 : Blo 247818 250435 := bstep (se 1 (by rfl) ⟨187826, by rfl⟩ : syracuseStep 250435 = 375653) B375653
theorem B250451 : Blo 247818 250451 := bstep (se 1 (by rfl) ⟨187838, by rfl⟩ : syracuseStep 250451 = 375677) B375677
theorem B250467 : Blo 247818 250467 := bstep (se 1 (by rfl) ⟨187850, by rfl⟩ : syracuseStep 250467 = 375701) B375701
theorem B250483 : Blo 247818 250483 := bstep (se 1 (by rfl) ⟨187862, by rfl⟩ : syracuseStep 250483 = 375725) B375725
theorem B578179 : Blo 247818 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B250499 : Blo 247818 250499 := bstep (se 1 (by rfl) ⟨187874, by rfl⟩ : syracuseStep 250499 = 375749) B375749
theorem B250515 : Blo 247818 250515 := bstep (se 1 (by rfl) ⟨187886, by rfl⟩ : syracuseStep 250515 = 375773) B375773
theorem B250531 : Blo 247818 250531 := bstep (se 1 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 250531 = 375797) B375797
theorem B1266353 : Blo 247818 1266353 := bstep (se 2 (by rfl) ⟨474882, by rfl⟩ : syracuseStep 1266353 = 949765) B949765
theorem B250547 : Blo 247818 250547 := bstep (se 1 (by rfl) ⟨187910, by rfl⟩ : syracuseStep 250547 = 375821) B375821
theorem B250563 : Blo 247818 250563 := bstep (se 1 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 250563 = 375845) B375845
theorem B840401 : Blo 247818 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B250579 : Blo 247818 250579 := bstep (se 1 (by rfl) ⟨187934, by rfl⟩ : syracuseStep 250579 = 375869) B375869
theorem B10277603 : Blo 247818 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B250595 : Blo 247818 250595 := bstep (se 1 (by rfl) ⟨187946, by rfl⟩ : syracuseStep 250595 = 375893) B375893
theorem B250611 : Blo 247818 250611 := bstep (se 1 (by rfl) ⟨187958, by rfl⟩ : syracuseStep 250611 = 375917) B375917
theorem B316163 : Blo 247818 316163 := bstep (se 1 (by rfl) ⟨237122, by rfl⟩ : syracuseStep 316163 = 474245) B474245
theorem B250627 : Blo 247818 250627 := bstep (se 1 (by rfl) ⟨187970, by rfl⟩ : syracuseStep 250627 = 375941) B375941
theorem B250643 : Blo 247818 250643 := bstep (se 1 (by rfl) ⟨187982, by rfl⟩ : syracuseStep 250643 = 375965) B375965
theorem B250659 : Blo 247818 250659 := bstep (se 1 (by rfl) ⟨187994, by rfl⟩ : syracuseStep 250659 = 375989) B375989
theorem B250675 : Blo 247818 250675 := bstep (se 1 (by rfl) ⟨188006, by rfl⟩ : syracuseStep 250675 = 376013) B376013
theorem B250691 : Blo 247818 250691 := bstep (se 1 (by rfl) ⟨188018, by rfl⟩ : syracuseStep 250691 = 376037) B376037
theorem B1528645 : Blo 247818 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B250707 : Blo 247818 250707 := bstep (se 1 (by rfl) ⟨188030, by rfl⟩ : syracuseStep 250707 = 376061) B376061
theorem B250723 : Blo 247818 250723 := bstep (se 1 (by rfl) ⟨188042, by rfl⟩ : syracuseStep 250723 = 376085) B376085
theorem B1364849 : Blo 247818 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B381809 : Blo 247818 381809 := bstep (se 2 (by rfl) ⟨143178, by rfl⟩ : syracuseStep 381809 = 286357) B286357
theorem B250739 : Blo 247818 250739 := bstep (se 1 (by rfl) ⟨188054, by rfl⟩ : syracuseStep 250739 = 376109) B376109
theorem B250755 : Blo 247818 250755 := bstep (se 1 (by rfl) ⟨188066, by rfl⟩ : syracuseStep 250755 = 376133) B376133
theorem B250771 : Blo 247818 250771 := bstep (se 1 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 250771 = 376157) B376157
theorem B1528739 : Blo 247818 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B250787 : Blo 247818 250787 := bstep (se 1 (by rfl) ⟨188090, by rfl⟩ : syracuseStep 250787 = 376181) B376181
theorem B250803 : Blo 247818 250803 := bstep (se 1 (by rfl) ⟨188102, by rfl⟩ : syracuseStep 250803 = 376205) B376205
theorem B250819 : Blo 247818 250819 := bstep (se 1 (by rfl) ⟨188114, by rfl⟩ : syracuseStep 250819 = 376229) B376229
theorem B250835 : Blo 247818 250835 := bstep (se 1 (by rfl) ⟨188126, by rfl⟩ : syracuseStep 250835 = 376253) B376253
theorem B250851 : Blo 247818 250851 := bstep (se 1 (by rfl) ⟨188138, by rfl⟩ : syracuseStep 250851 = 376277) B376277
theorem B250867 : Blo 247818 250867 := bstep (se 1 (by rfl) ⟨188150, by rfl⟩ : syracuseStep 250867 = 376301) B376301
theorem B250883 : Blo 247818 250883 := bstep (se 1 (by rfl) ⟨188162, by rfl⟩ : syracuseStep 250883 = 376325) B376325
theorem B250899 : Blo 247818 250899 := bstep (se 1 (by rfl) ⟨188174, by rfl⟩ : syracuseStep 250899 = 376349) B376349
theorem B250915 : Blo 247818 250915 := bstep (se 1 (by rfl) ⟨188186, by rfl⟩ : syracuseStep 250915 = 376373) B376373
theorem B250931 : Blo 247818 250931 := bstep (se 1 (by rfl) ⟨188198, by rfl⟩ : syracuseStep 250931 = 376397) B376397
theorem B250947 : Blo 247818 250947 := bstep (se 1 (by rfl) ⟨188210, by rfl⟩ : syracuseStep 250947 = 376421) B376421
theorem B250963 : Blo 247818 250963 := bstep (se 1 (by rfl) ⟨188222, by rfl⟩ : syracuseStep 250963 = 376445) B376445
theorem B250979 : Blo 247818 250979 := bstep (se 1 (by rfl) ⟨188234, by rfl⟩ : syracuseStep 250979 = 376469) B376469
theorem B250995 : Blo 247818 250995 := bstep (se 1 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 250995 = 376493) B376493
theorem B251011 : Blo 247818 251011 := bstep (se 1 (by rfl) ⟨188258, by rfl⟩ : syracuseStep 251011 = 376517) B376517
theorem B251027 : Blo 247818 251027 := bstep (se 1 (by rfl) ⟨188270, by rfl⟩ : syracuseStep 251027 = 376541) B376541
theorem B251043 : Blo 247818 251043 := bstep (se 1 (by rfl) ⟨188282, by rfl⟩ : syracuseStep 251043 = 376565) B376565
theorem B251059 : Blo 247818 251059 := bstep (se 1 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 251059 = 376589) B376589
theorem B251075 : Blo 247818 251075 := bstep (se 1 (by rfl) ⟨188306, by rfl⟩ : syracuseStep 251075 = 376613) B376613
theorem B251091 : Blo 247818 251091 := bstep (se 1 (by rfl) ⟨188318, by rfl⟩ : syracuseStep 251091 = 376637) B376637
theorem B251107 : Blo 247818 251107 := bstep (se 1 (by rfl) ⟨188330, by rfl⟩ : syracuseStep 251107 = 376661) B376661
theorem B840941 : Blo 247818 840941 := bstep (se 3 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 840941 = 315353) B315353
theorem B251123 : Blo 247818 251123 := bstep (se 1 (by rfl) ⟨188342, by rfl⟩ : syracuseStep 251123 = 376685) B376685
theorem B251139 : Blo 247818 251139 := bstep (se 1 (by rfl) ⟨188354, by rfl⟩ : syracuseStep 251139 = 376709) B376709
theorem B251155 : Blo 247818 251155 := bstep (se 1 (by rfl) ⟨188366, by rfl⟩ : syracuseStep 251155 = 376733) B376733
theorem B840995 : Blo 247818 840995 := bstep (se 1 (by rfl) ⟨630746, by rfl⟩ : syracuseStep 840995 = 1261493) B1261493
theorem B251171 : Blo 247818 251171 := bstep (se 1 (by rfl) ⟨188378, by rfl⟩ : syracuseStep 251171 = 376757) B376757
theorem B251187 : Blo 247818 251187 := bstep (se 1 (by rfl) ⟨188390, by rfl⟩ : syracuseStep 251187 = 376781) B376781
theorem B709955 : Blo 247818 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B251203 : Blo 247818 251203 := bstep (se 1 (by rfl) ⟨188402, by rfl⟩ : syracuseStep 251203 = 376805) B376805
theorem B251219 : Blo 247818 251219 := bstep (se 1 (by rfl) ⟨188414, by rfl⟩ : syracuseStep 251219 = 376829) B376829
theorem B1070435 : Blo 247818 1070435 := bstep (se 1 (by rfl) ⟨802826, by rfl⟩ : syracuseStep 1070435 = 1605653) B1605653
theorem B251235 : Blo 247818 251235 := bstep (se 1 (by rfl) ⟨188426, by rfl⟩ : syracuseStep 251235 = 376853) B376853
theorem B447857 : Blo 247818 447857 := bstep (se 2 (by rfl) ⟨167946, by rfl⟩ : syracuseStep 447857 = 335893) B335893
theorem B251251 : Blo 247818 251251 := bstep (se 1 (by rfl) ⟨188438, by rfl⟩ : syracuseStep 251251 = 376877) B376877
theorem B251267 : Blo 247818 251267 := bstep (se 1 (by rfl) ⟨188450, by rfl⟩ : syracuseStep 251267 = 376901) B376901
theorem B251283 : Blo 247818 251283 := bstep (se 1 (by rfl) ⟨188462, by rfl⟩ : syracuseStep 251283 = 376925) B376925
theorem B251299 : Blo 247818 251299 := bstep (se 1 (by rfl) ⟨188474, by rfl⟩ : syracuseStep 251299 = 376949) B376949
theorem B251315 : Blo 247818 251315 := bstep (se 1 (by rfl) ⟨188486, by rfl⟩ : syracuseStep 251315 = 376973) B376973
theorem B316867 : Blo 247818 316867 := bstep (se 1 (by rfl) ⟨237650, by rfl⟩ : syracuseStep 316867 = 475301) B475301
theorem B251331 : Blo 247818 251331 := bstep (se 1 (by rfl) ⟨188498, by rfl⟩ : syracuseStep 251331 = 376997) B376997
theorem B251347 : Blo 247818 251347 := bstep (se 1 (by rfl) ⟨188510, by rfl⟩ : syracuseStep 251347 = 377021) B377021
theorem B251363 : Blo 247818 251363 := bstep (se 1 (by rfl) ⟨188522, by rfl⟩ : syracuseStep 251363 = 377045) B377045
theorem B251379 : Blo 247818 251379 := bstep (se 1 (by rfl) ⟨188534, by rfl⟩ : syracuseStep 251379 = 377069) B377069
theorem B251395 : Blo 247818 251395 := bstep (se 1 (by rfl) ⟨188546, by rfl⟩ : syracuseStep 251395 = 377093) B377093
theorem B251411 : Blo 247818 251411 := bstep (se 1 (by rfl) ⟨188558, by rfl⟩ : syracuseStep 251411 = 377117) B377117
theorem B316963 : Blo 247818 316963 := bstep (se 1 (by rfl) ⟨237722, by rfl⟩ : syracuseStep 316963 = 475445) B475445
theorem B251427 : Blo 247818 251427 := bstep (se 1 (by rfl) ⟨188570, by rfl⟩ : syracuseStep 251427 = 377141) B377141
theorem B1136177 : Blo 247818 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B841265 : Blo 247818 841265 := bstep (se 2 (by rfl) ⟨315474, by rfl⟩ : syracuseStep 841265 = 630949) B630949
theorem B251443 : Blo 247818 251443 := bstep (se 1 (by rfl) ⟨188582, by rfl⟩ : syracuseStep 251443 = 377165) B377165
theorem B251459 : Blo 247818 251459 := bstep (se 1 (by rfl) ⟨188594, by rfl⟩ : syracuseStep 251459 = 377189) B377189
theorem B251475 : Blo 247818 251475 := bstep (se 1 (by rfl) ⟨188606, by rfl⟩ : syracuseStep 251475 = 377213) B377213
theorem B251491 : Blo 247818 251491 := bstep (se 1 (by rfl) ⟨188618, by rfl⟩ : syracuseStep 251491 = 377237) B377237
theorem B251507 : Blo 247818 251507 := bstep (se 1 (by rfl) ⟨188630, by rfl⟩ : syracuseStep 251507 = 377261) B377261
theorem B251523 : Blo 247818 251523 := bstep (se 1 (by rfl) ⟨188642, by rfl⟩ : syracuseStep 251523 = 377285) B377285
theorem B251539 : Blo 247818 251539 := bstep (se 1 (by rfl) ⟨188654, by rfl⟩ : syracuseStep 251539 = 377309) B377309
theorem B251555 : Blo 247818 251555 := bstep (se 1 (by rfl) ⟨188666, by rfl⟩ : syracuseStep 251555 = 377333) B377333
theorem B251571 : Blo 247818 251571 := bstep (se 1 (by rfl) ⟨188678, by rfl⟩ : syracuseStep 251571 = 377357) B377357
theorem B251587 : Blo 247818 251587 := bstep (se 1 (by rfl) ⟨188690, by rfl⟩ : syracuseStep 251587 = 377381) B377381
theorem B251603 : Blo 247818 251603 := bstep (se 1 (by rfl) ⟨188702, by rfl⟩ : syracuseStep 251603 = 377405) B377405
theorem B251619 : Blo 247818 251619 := bstep (se 1 (by rfl) ⟨188714, by rfl⟩ : syracuseStep 251619 = 377429) B377429
theorem B251635 : Blo 247818 251635 := bstep (se 1 (by rfl) ⟨188726, by rfl⟩ : syracuseStep 251635 = 377453) B377453
theorem B251651 : Blo 247818 251651 := bstep (se 1 (by rfl) ⟨188738, by rfl⟩ : syracuseStep 251651 = 377477) B377477
theorem B251667 : Blo 247818 251667 := bstep (se 1 (by rfl) ⟨188750, by rfl⟩ : syracuseStep 251667 = 377501) B377501
theorem B251683 : Blo 247818 251683 := bstep (se 1 (by rfl) ⟨188762, by rfl⟩ : syracuseStep 251683 = 377525) B377525
theorem B907057 : Blo 247818 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B251699 : Blo 247818 251699 := bstep (se 1 (by rfl) ⟨188774, by rfl⟩ : syracuseStep 251699 = 377549) B377549
theorem B251715 : Blo 247818 251715 := bstep (se 1 (by rfl) ⟨188786, by rfl⟩ : syracuseStep 251715 = 377573) B377573
theorem B251731 : Blo 247818 251731 := bstep (se 1 (by rfl) ⟨188798, by rfl⟩ : syracuseStep 251731 = 377597) B377597
theorem B677731 : Blo 247818 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B251747 : Blo 247818 251747 := bstep (se 1 (by rfl) ⟨188810, by rfl⟩ : syracuseStep 251747 = 377621) B377621
theorem B6510449 : Blo 247818 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B251763 : Blo 247818 251763 := bstep (se 1 (by rfl) ⟨188822, by rfl⟩ : syracuseStep 251763 = 377645) B377645
theorem B251779 : Blo 247818 251779 := bstep (se 1 (by rfl) ⟨188834, by rfl⟩ : syracuseStep 251779 = 377669) B377669
theorem B251795 : Blo 247818 251795 := bstep (se 1 (by rfl) ⟨188846, by rfl⟩ : syracuseStep 251795 = 377693) B377693
theorem B251811 : Blo 247818 251811 := bstep (se 1 (by rfl) ⟨188858, by rfl⟩ : syracuseStep 251811 = 377717) B377717
theorem B1366021 : Blo 247818 1366021 := bstep (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) B256129
theorem B317459 : Blo 247818 317459 := bstep (se 1 (by rfl) ⟨238094, by rfl⟩ : syracuseStep 317459 = 476189) B476189
theorem B841805 : Blo 247818 841805 := bstep (se 3 (by rfl) ⟨157838, by rfl⟩ : syracuseStep 841805 = 315677) B315677
theorem B1267811 : Blo 247818 1267811 := bstep (se 1 (by rfl) ⟨950858, by rfl⟩ : syracuseStep 1267811 = 1901717) B1901717
theorem B710765 : Blo 247818 710765 := bstep (se 3 (by rfl) ⟨133268, by rfl⟩ : syracuseStep 710765 = 266537) B266537
theorem B1431665 : Blo 247818 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B841859 : Blo 247818 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B710957 : Blo 247818 710957 := bstep (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) B266609
theorem B252227 : Blo 247818 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B1628549 : Blo 247818 1628549 := bstep (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) B305353
theorem B842129 : Blo 247818 842129 := bstep (se 2 (by rfl) ⟨315798, by rfl⟩ : syracuseStep 842129 = 631597) B631597
theorem B2382533 : Blo 247818 2382533 := bstep (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) B446725
theorem B318163 : Blo 247818 318163 := bstep (se 1 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 318163 = 477245) B477245
theorem B1596145 : Blo 247818 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B318259 : Blo 247818 318259 := bstep (se 1 (by rfl) ⟨238694, by rfl⟩ : syracuseStep 318259 = 477389) B477389
theorem B1268621 : Blo 247818 1268621 := bstep (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) B475733
theorem B842669 : Blo 247818 842669 := bstep (se 3 (by rfl) ⟨158000, by rfl⟩ : syracuseStep 842669 = 316001) B316001
theorem B842723 : Blo 247818 842723 := bstep (se 1 (by rfl) ⟨632042, by rfl⟩ : syracuseStep 842723 = 1264085) B1264085
theorem B1006769 : Blo 247818 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B2579653 : Blo 247818 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B842993 : Blo 247818 842993 := bstep (se 2 (by rfl) ⟨316122, by rfl⟩ : syracuseStep 842993 = 632245) B632245
theorem B810253 : Blo 247818 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B711949 : Blo 247818 711949 := bstep (se 3 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 711949 = 266981) B266981
theorem B1203569 : Blo 247818 1203569 := bstep (se 2 (by rfl) ⟨451338, by rfl⟩ : syracuseStep 1203569 = 902677) B902677
theorem B941489 : Blo 247818 941489 := bstep (se 2 (by rfl) ⟨353058, by rfl⟩ : syracuseStep 941489 = 706117) B706117
theorem B253379 : Blo 247818 253379 := bstep (se 1 (by rfl) ⟨190034, by rfl⟩ : syracuseStep 253379 = 380069) B380069
theorem B908813 : Blo 247818 908813 := bstep (se 3 (by rfl) ⟨170402, by rfl⟩ : syracuseStep 908813 = 340805) B340805
theorem B1433123 : Blo 247818 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B450307 : Blo 247818 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B843533 : Blo 247818 843533 := bstep (se 3 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 843533 = 316325) B316325
theorem B843587 : Blo 247818 843587 := bstep (se 1 (by rfl) ⟨632690, by rfl⟩ : syracuseStep 843587 = 1265381) B1265381
theorem B843857 : Blo 247818 843857 := bstep (se 2 (by rfl) ⟨316446, by rfl⟩ : syracuseStep 843857 = 632893) B632893
theorem B909425 : Blo 247818 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B1532045 : Blo 247818 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B6119621 : Blo 247818 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B811363 : Blo 247818 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B418243 : Blo 247818 418243 := bstep (se 1 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 418243 = 627365) B627365
theorem B1696241 : Blo 247818 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1434125 : Blo 247818 1434125 := bstep (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) B537797
theorem B418385 : Blo 247818 418385 := bstep (se 2 (by rfl) ⟨156894, by rfl⟩ : syracuseStep 418385 = 313789) B313789
theorem B844397 : Blo 247818 844397 := bstep (se 3 (by rfl) ⟨158324, by rfl⟩ : syracuseStep 844397 = 316649) B316649
theorem B844451 : Blo 247818 844451 := bstep (se 1 (by rfl) ⟨633338, by rfl⟩ : syracuseStep 844451 = 1266677) B1266677
theorem B418513 : Blo 247818 418513 := bstep (se 2 (by rfl) ⟨156942, by rfl⟩ : syracuseStep 418513 = 313885) B313885
theorem B418547 : Blo 247818 418547 := bstep (se 1 (by rfl) ⟨313910, by rfl⟩ : syracuseStep 418547 = 627821) B627821
theorem B942947 : Blo 247818 942947 := bstep (se 1 (by rfl) ⟨707210, by rfl⟩ : syracuseStep 942947 = 1414421) B1414421
theorem B942961 : Blo 247818 942961 := bstep (se 2 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 942961 = 707221) B707221
theorem B418675 : Blo 247818 418675 := bstep (se 1 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 418675 = 628013) B628013
theorem B353155 : Blo 247818 353155 := bstep (se 1 (by rfl) ⟨264866, by rfl⟩ : syracuseStep 353155 = 529733) B529733
theorem B844721 : Blo 247818 844721 := bstep (se 2 (by rfl) ⟨316770, by rfl⟩ : syracuseStep 844721 = 633541) B633541
theorem B713681 : Blo 247818 713681 := bstep (se 2 (by rfl) ⟨267630, by rfl⟩ : syracuseStep 713681 = 535261) B535261
theorem B418817 : Blo 247818 418817 := bstep (se 2 (by rfl) ⟨157056, by rfl⟩ : syracuseStep 418817 = 314113) B314113
theorem B418945 : Blo 247818 418945 := bstep (se 2 (by rfl) ⟨157104, by rfl⟩ : syracuseStep 418945 = 314209) B314209
theorem B713873 : Blo 247818 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B418979 : Blo 247818 418979 := bstep (se 1 (by rfl) ⟨314234, by rfl⟩ : syracuseStep 418979 = 628469) B628469
theorem B1008845 : Blo 247818 1008845 := bstep (se 3 (by rfl) ⟨189158, by rfl⟩ : syracuseStep 1008845 = 378317) B378317
theorem B419107 : Blo 247818 419107 := bstep (se 1 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 419107 = 628661) B628661
theorem B2876725 : Blo 247818 2876725 := bstep (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) B269693
theorem B419249 : Blo 247818 419249 := bstep (se 2 (by rfl) ⟨157218, by rfl⟩ : syracuseStep 419249 = 314437) B314437
theorem B845261 : Blo 247818 845261 := bstep (se 3 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 845261 = 316973) B316973
theorem B1074637 : Blo 247818 1074637 := bstep (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) B402989
theorem B3630563 : Blo 247818 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B845315 : Blo 247818 845315 := bstep (se 1 (by rfl) ⟨633986, by rfl⟩ : syracuseStep 845315 = 1267973) B1267973
theorem B419377 : Blo 247818 419377 := bstep (se 2 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 419377 = 314533) B314533
theorem B419411 : Blo 247818 419411 := bstep (se 1 (by rfl) ⟨314558, by rfl⟩ : syracuseStep 419411 = 629117) B629117
theorem B812717 : Blo 247818 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B419539 : Blo 247818 419539 := bstep (se 1 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 419539 = 629309) B629309
theorem B1271537 : Blo 247818 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B1206029 : Blo 247818 1206029 := bstep (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) B452261
theorem B845585 : Blo 247818 845585 := bstep (se 2 (by rfl) ⟨317094, by rfl⟩ : syracuseStep 845585 = 634189) B634189
theorem B419681 : Blo 247818 419681 := bstep (se 2 (by rfl) ⟨157380, by rfl⟩ : syracuseStep 419681 = 314761) B314761
theorem B2844557 : Blo 247818 2844557 := bstep (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) B1066709
theorem B419809 : Blo 247818 419809 := bstep (se 2 (by rfl) ⟨157428, by rfl⟩ : syracuseStep 419809 = 314857) B314857
theorem B354289 : Blo 247818 354289 := bstep (se 2 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 354289 = 265717) B265717
theorem B419843 : Blo 247818 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B354385 : Blo 247818 354385 := bstep (se 2 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 354385 = 265789) B265789
theorem B714865 : Blo 247818 714865 := bstep (se 2 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 714865 = 536149) B536149
theorem B419971 : Blo 247818 419971 := bstep (se 1 (by rfl) ⟨314978, by rfl⟩ : syracuseStep 419971 = 629957) B629957
theorem B420113 : Blo 247818 420113 := bstep (se 2 (by rfl) ⟨157542, by rfl⟩ : syracuseStep 420113 = 315085) B315085
theorem B944419 : Blo 247818 944419 := bstep (se 1 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 944419 = 1416629) B1416629
theorem B846125 : Blo 247818 846125 := bstep (se 3 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 846125 = 317297) B317297
theorem B846179 : Blo 247818 846179 := bstep (se 1 (by rfl) ⟨634634, by rfl⟩ : syracuseStep 846179 = 1269269) B1269269
theorem B715139 : Blo 247818 715139 := bstep (se 1 (by rfl) ⟨536354, by rfl⟩ : syracuseStep 715139 = 1072709) B1072709
theorem B420241 : Blo 247818 420241 := bstep (se 2 (by rfl) ⟨157590, by rfl⟩ : syracuseStep 420241 = 315181) B315181
theorem B420275 : Blo 247818 420275 := bstep (se 1 (by rfl) ⟨315206, by rfl⟩ : syracuseStep 420275 = 630413) B630413
theorem B420403 : Blo 247818 420403 := bstep (se 1 (by rfl) ⟨315302, by rfl⟩ : syracuseStep 420403 = 630605) B630605
theorem B354881 : Blo 247818 354881 := bstep (se 2 (by rfl) ⟨133080, by rfl⟩ : syracuseStep 354881 = 266161) B266161
theorem B715331 : Blo 247818 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B846449 : Blo 247818 846449 := bstep (se 2 (by rfl) ⟨317418, by rfl⟩ : syracuseStep 846449 = 634837) B634837
theorem B420545 : Blo 247818 420545 := bstep (se 2 (by rfl) ⟨157704, by rfl⟩ : syracuseStep 420545 = 315409) B315409
theorem B420673 : Blo 247818 420673 := bstep (se 2 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 420673 = 315505) B315505
theorem B420707 : Blo 247818 420707 := bstep (se 1 (by rfl) ⟨315530, by rfl⟩ : syracuseStep 420707 = 631061) B631061
theorem B420835 : Blo 247818 420835 := bstep (se 1 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 420835 = 631253) B631253
theorem B420977 : Blo 247818 420977 := bstep (se 2 (by rfl) ⟨157866, by rfl⟩ : syracuseStep 420977 = 315733) B315733
theorem B846989 : Blo 247818 846989 := bstep (se 3 (by rfl) ⟨158810, by rfl⟩ : syracuseStep 846989 = 317621) B317621
theorem B1272995 : Blo 247818 1272995 := bstep (se 1 (by rfl) ⟨954746, by rfl⟩ : syracuseStep 1272995 = 1909493) B1909493
theorem B847043 : Blo 247818 847043 := bstep (se 1 (by rfl) ⟨635282, by rfl⟩ : syracuseStep 847043 = 1270565) B1270565
theorem B421105 : Blo 247818 421105 := bstep (se 2 (by rfl) ⟨157914, by rfl⟩ : syracuseStep 421105 = 315829) B315829
theorem B421139 : Blo 247818 421139 := bstep (se 1 (by rfl) ⟨315854, by rfl⟩ : syracuseStep 421139 = 631709) B631709
theorem B1469765 : Blo 247818 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B322915 : Blo 247818 322915 := bstep (se 1 (by rfl) ⟨242186, by rfl⟩ : syracuseStep 322915 = 484373) B484373
theorem B716141 : Blo 247818 716141 := bstep (se 3 (by rfl) ⟨134276, by rfl⟩ : syracuseStep 716141 = 268553) B268553
theorem B421267 : Blo 247818 421267 := bstep (se 1 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 421267 = 631901) B631901
theorem B355747 : Blo 247818 355747 := bstep (se 1 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 355747 = 533621) B533621
theorem B847313 : Blo 247818 847313 := bstep (se 2 (by rfl) ⟨317742, by rfl⟩ : syracuseStep 847313 = 635485) B635485
theorem B355843 : Blo 247818 355843 := bstep (se 1 (by rfl) ⟨266882, by rfl⟩ : syracuseStep 355843 = 533765) B533765
theorem B421409 : Blo 247818 421409 := bstep (se 2 (by rfl) ⟨158028, by rfl⟩ : syracuseStep 421409 = 316057) B316057
theorem B716323 : Blo 247818 716323 := bstep (se 1 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 716323 = 1074485) B1074485
theorem B421537 : Blo 247818 421537 := bstep (se 2 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 421537 = 316153) B316153
theorem B421571 : Blo 247818 421571 := bstep (se 1 (by rfl) ⟨316178, by rfl⟩ : syracuseStep 421571 = 632357) B632357
theorem B421699 : Blo 247818 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B1011619 : Blo 247818 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B1601477 : Blo 247818 1601477 := bstep (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) B300277
theorem B683981 : Blo 247818 683981 := bstep (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) B256493
theorem B1273805 : Blo 247818 1273805 := bstep (se 3 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 1273805 = 477677) B477677
theorem B421841 : Blo 247818 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B847853 : Blo 247818 847853 := bstep (se 3 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 847853 = 317945) B317945
theorem B356339 : Blo 247818 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B716813 : Blo 247818 716813 := bstep (se 3 (by rfl) ⟨134402, by rfl⟩ : syracuseStep 716813 = 268805) B268805
theorem B847907 : Blo 247818 847907 := bstep (se 1 (by rfl) ⟨635930, by rfl⟩ : syracuseStep 847907 = 1271861) B1271861
theorem B421969 : Blo 247818 421969 := bstep (se 2 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 421969 = 316477) B316477
theorem B422003 : Blo 247818 422003 := bstep (se 1 (by rfl) ⟨316502, by rfl⟩ : syracuseStep 422003 = 633005) B633005
theorem B422131 : Blo 247818 422131 := bstep (se 1 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 422131 = 633197) B633197
theorem B848177 : Blo 247818 848177 := bstep (se 2 (by rfl) ⟨318066, by rfl⟩ : syracuseStep 848177 = 636133) B636133
theorem B422273 : Blo 247818 422273 := bstep (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) B316705
theorem B946637 : Blo 247818 946637 := bstep (se 3 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 946637 = 354989) B354989
theorem B422401 : Blo 247818 422401 := bstep (se 2 (by rfl) ⟨158400, by rfl⟩ : syracuseStep 422401 = 316801) B316801
theorem B422435 : Blo 247818 422435 := bstep (se 1 (by rfl) ⟨316826, by rfl⟩ : syracuseStep 422435 = 633653) B633653
theorem B356977 : Blo 247818 356977 := bstep (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) B267733
theorem B422563 : Blo 247818 422563 := bstep (se 1 (by rfl) ⟨316922, by rfl⟩ : syracuseStep 422563 = 633845) B633845
theorem B2847473 : Blo 247818 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1700621 : Blo 247818 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B422705 : Blo 247818 422705 := bstep (se 2 (by rfl) ⟨158514, by rfl⟩ : syracuseStep 422705 = 317029) B317029
theorem B848717 : Blo 247818 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B848771 : Blo 247818 848771 := bstep (se 1 (by rfl) ⟨636578, by rfl⟩ : syracuseStep 848771 = 1273157) B1273157
theorem B717731 : Blo 247818 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B422833 : Blo 247818 422833 := bstep (se 2 (by rfl) ⟨158562, by rfl⟩ : syracuseStep 422833 = 317125) B317125
theorem B357313 : Blo 247818 357313 := bstep (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) B267985
theorem B422867 : Blo 247818 422867 := bstep (se 1 (by rfl) ⟨317150, by rfl⟩ : syracuseStep 422867 = 634301) B634301
theorem B422995 : Blo 247818 422995 := bstep (se 1 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 422995 = 634493) B634493
theorem B849041 : Blo 247818 849041 := bstep (se 2 (by rfl) ⟨318390, by rfl⟩ : syracuseStep 849041 = 636781) B636781
theorem B423137 : Blo 247818 423137 := bstep (se 2 (by rfl) ⟨158676, by rfl⟩ : syracuseStep 423137 = 317353) B317353
theorem B423265 : Blo 247818 423265 := bstep (se 2 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 423265 = 317449) B317449
theorem B423299 : Blo 247818 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B423427 : Blo 247818 423427 := bstep (se 1 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 423427 = 635141) B635141
theorem B357905 : Blo 247818 357905 := bstep (se 2 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 357905 = 268429) B268429
theorem B423569 : Blo 247818 423569 := bstep (se 2 (by rfl) ⟨158838, by rfl⟩ : syracuseStep 423569 = 317677) B317677
theorem B849581 : Blo 247818 849581 := bstep (se 3 (by rfl) ⟨159296, by rfl⟩ : syracuseStep 849581 = 318593) B318593
theorem B3405509 : Blo 247818 3405509 := bstep (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) B638533
theorem B849635 : Blo 247818 849635 := bstep (se 1 (by rfl) ⟨637226, by rfl⟩ : syracuseStep 849635 = 1274453) B1274453
theorem B423697 : Blo 247818 423697 := bstep (se 2 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 423697 = 317773) B317773
theorem B718627 : Blo 247818 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B423731 : Blo 247818 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B3143477 : Blo 247818 3143477 := bstep (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) B294701
theorem B423859 : Blo 247818 423859 := bstep (se 1 (by rfl) ⟨317894, by rfl⟩ : syracuseStep 423859 = 635789) B635789
theorem B358435 : Blo 247818 358435 := bstep (se 1 (by rfl) ⟨268826, by rfl⟩ : syracuseStep 358435 = 537653) B537653
theorem B424001 : Blo 247818 424001 := bstep (se 2 (by rfl) ⟨159000, by rfl⟩ : syracuseStep 424001 = 318001) B318001
theorem B1800305 : Blo 247818 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B424129 : Blo 247818 424129 := bstep (se 2 (by rfl) ⟨159048, by rfl⟩ : syracuseStep 424129 = 318097) B318097
theorem B424163 : Blo 247818 424163 := bstep (se 1 (by rfl) ⟨318122, by rfl⟩ : syracuseStep 424163 = 636245) B636245
theorem B424291 : Blo 247818 424291 := bstep (se 1 (by rfl) ⟨318218, by rfl⟩ : syracuseStep 424291 = 636437) B636437
theorem B1210801 : Blo 247818 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B424433 : Blo 247818 424433 := bstep (se 2 (by rfl) ⟨159162, by rfl⟩ : syracuseStep 424433 = 318325) B318325
theorem B424561 : Blo 247818 424561 := bstep (se 2 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 424561 = 318421) B318421
theorem B424595 : Blo 247818 424595 := bstep (se 1 (by rfl) ⟨318446, by rfl⟩ : syracuseStep 424595 = 636893) B636893
theorem B3209969 : Blo 247818 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B424723 : Blo 247818 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B424865 : Blo 247818 424865 := bstep (se 2 (by rfl) ⟨159324, by rfl⟩ : syracuseStep 424865 = 318649) B318649
theorem B425027 : Blo 247818 425027 := bstep (se 1 (by rfl) ⟨318770, by rfl⟩ : syracuseStep 425027 = 637541) B637541
theorem B949553 : Blo 247818 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B1900259 : Blo 247818 1900259 := bstep (se 1 (by rfl) ⟨1425194, by rfl⟩ : syracuseStep 1900259 = 2850389) B2850389
theorem B2425133 : Blo 247818 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B2031965 : Blo 247818 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B4260275 : Blo 247818 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B1081817 : Blo 247818 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B459287 : Blo 247818 459287 := bstep (se 1 (by rfl) ⟨344465, by rfl⟩ : syracuseStep 459287 = 688931) B688931
theorem B557657 : Blo 247818 557657 := bstep (se 2 (by rfl) ⟨209121, by rfl⟩ : syracuseStep 557657 = 418243) B418243
theorem B557747 : Blo 247818 557747 := bstep (se 1 (by rfl) ⟨418310, by rfl⟩ : syracuseStep 557747 = 836621) B836621
theorem B557783 : Blo 247818 557783 := bstep (se 1 (by rfl) ⟨418337, by rfl⟩ : syracuseStep 557783 = 836675) B836675
theorem B557963 : Blo 247818 557963 := bstep (se 1 (by rfl) ⟨418472, by rfl⟩ : syracuseStep 557963 = 836945) B836945
theorem B558017 : Blo 247818 558017 := bstep (se 2 (by rfl) ⟨209256, by rfl⟩ : syracuseStep 558017 = 418513) B418513
theorem B558233 : Blo 247818 558233 := bstep (se 2 (by rfl) ⟨209337, by rfl⟩ : syracuseStep 558233 = 418675) B418675
theorem B558323 : Blo 247818 558323 := bstep (se 1 (by rfl) ⟨418742, by rfl⟩ : syracuseStep 558323 = 837485) B837485
theorem B558359 : Blo 247818 558359 := bstep (se 1 (by rfl) ⟨418769, by rfl⟩ : syracuseStep 558359 = 837539) B837539
theorem B4523309 : Blo 247818 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B558539 : Blo 247818 558539 := bstep (se 1 (by rfl) ⟨418904, by rfl⟩ : syracuseStep 558539 = 837809) B837809
theorem B1148381 : Blo 247818 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B558593 : Blo 247818 558593 := bstep (se 2 (by rfl) ⟨209472, by rfl⟩ : syracuseStep 558593 = 418945) B418945
theorem B558809 : Blo 247818 558809 := bstep (se 2 (by rfl) ⟨209553, by rfl⟩ : syracuseStep 558809 = 419107) B419107
theorem B3835633 : Blo 247818 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B558899 : Blo 247818 558899 := bstep (se 1 (by rfl) ⟨419174, by rfl⟩ : syracuseStep 558899 = 838349) B838349
theorem B558935 : Blo 247818 558935 := bstep (se 1 (by rfl) ⟨419201, by rfl⟩ : syracuseStep 558935 = 838403) B838403
theorem B952195 : Blo 247818 952195 := bstep (se 1 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 952195 = 1428293) B1428293
theorem B1017731 : Blo 247818 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B559115 : Blo 247818 559115 := bstep (se 1 (by rfl) ⟨419336, by rfl⟩ : syracuseStep 559115 = 838673) B838673
theorem B559169 : Blo 247818 559169 := bstep (se 2 (by rfl) ⟨209688, by rfl⟩ : syracuseStep 559169 = 419377) B419377
theorem B952499 : Blo 247818 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B559385 : Blo 247818 559385 := bstep (se 2 (by rfl) ⟨209769, by rfl⟩ : syracuseStep 559385 = 419539) B419539
theorem B559475 : Blo 247818 559475 := bstep (se 1 (by rfl) ⟨419606, by rfl⟩ : syracuseStep 559475 = 839213) B839213
theorem B559511 : Blo 247818 559511 := bstep (se 1 (by rfl) ⟨419633, by rfl⟩ : syracuseStep 559511 = 839267) B839267
theorem B559691 : Blo 247818 559691 := bstep (se 1 (by rfl) ⟨419768, by rfl⟩ : syracuseStep 559691 = 839537) B839537
theorem B559745 : Blo 247818 559745 := bstep (se 2 (by rfl) ⟨209904, by rfl⟩ : syracuseStep 559745 = 419809) B419809
theorem B264875 : Blo 247818 264875 := bstep (se 1 (by rfl) ⟨198656, by rfl⟩ : syracuseStep 264875 = 397313) B397313
theorem B953153 : Blo 247818 953153 := bstep (se 2 (by rfl) ⟨357432, by rfl⟩ : syracuseStep 953153 = 714865) B714865
theorem B1280843 : Blo 247818 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B559961 : Blo 247818 559961 := bstep (se 2 (by rfl) ⟨209985, by rfl⟩ : syracuseStep 559961 = 419971) B419971
theorem B560051 : Blo 247818 560051 := bstep (se 1 (by rfl) ⟨420038, by rfl⟩ : syracuseStep 560051 = 840077) B840077
theorem B560087 : Blo 247818 560087 := bstep (se 1 (by rfl) ⟨420065, by rfl⟩ : syracuseStep 560087 = 840131) B840131
theorem B1903661 : Blo 247818 1903661 := bstep (se 3 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 1903661 = 713873) B713873
theorem B2165825 : Blo 247818 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B560267 : Blo 247818 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B6851735 : Blo 247818 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B560321 : Blo 247818 560321 := bstep (se 2 (by rfl) ⟨210120, by rfl⟩ : syracuseStep 560321 = 420241) B420241
theorem B1019159 : Blo 247818 1019159 := bstep (se 1 (by rfl) ⟨764369, by rfl⟩ : syracuseStep 1019159 = 1528739) B1528739
theorem B560537 : Blo 247818 560537 := bstep (se 2 (by rfl) ⟨210201, by rfl⟩ : syracuseStep 560537 = 420403) B420403
theorem B560627 : Blo 247818 560627 := bstep (se 1 (by rfl) ⟨420470, by rfl⟩ : syracuseStep 560627 = 840941) B840941
theorem B560663 : Blo 247818 560663 := bstep (se 1 (by rfl) ⟨420497, by rfl⟩ : syracuseStep 560663 = 840995) B840995
theorem B298571 : Blo 247818 298571 := bstep (se 1 (by rfl) ⟨223928, by rfl⟩ : syracuseStep 298571 = 447857) B447857
theorem B757451 : Blo 247818 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B560843 : Blo 247818 560843 := bstep (se 1 (by rfl) ⟨420632, by rfl⟩ : syracuseStep 560843 = 841265) B841265
theorem B265943 : Blo 247818 265943 := bstep (se 1 (by rfl) ⟨199457, by rfl⟩ : syracuseStep 265943 = 398915) B398915
theorem B560897 : Blo 247818 560897 := bstep (se 2 (by rfl) ⟨210336, by rfl⟩ : syracuseStep 560897 = 420673) B420673
theorem B2133965 : Blo 247818 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B561113 : Blo 247818 561113 := bstep (se 2 (by rfl) ⟨210417, by rfl⟩ : syracuseStep 561113 = 420835) B420835
theorem B954413 : Blo 247818 954413 := bstep (se 3 (by rfl) ⟨178952, by rfl⟩ : syracuseStep 954413 = 357905) B357905
theorem B561203 : Blo 247818 561203 := bstep (se 1 (by rfl) ⟨420902, by rfl⟩ : syracuseStep 561203 = 841805) B841805
theorem B954443 : Blo 247818 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B561239 : Blo 247818 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B528563 : Blo 247818 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B1085699 : Blo 247818 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B561419 : Blo 247818 561419 := bstep (se 1 (by rfl) ⟨421064, by rfl⟩ : syracuseStep 561419 = 842129) B842129
theorem B561473 : Blo 247818 561473 := bstep (se 2 (by rfl) ⟨210552, by rfl⟩ : syracuseStep 561473 = 421105) B421105
theorem B430553 : Blo 247818 430553 := bstep (se 2 (by rfl) ⟨161457, by rfl⟩ : syracuseStep 430553 = 322915) B322915
theorem B561689 : Blo 247818 561689 := bstep (se 2 (by rfl) ⟨210633, by rfl⟩ : syracuseStep 561689 = 421267) B421267
theorem B561779 : Blo 247818 561779 := bstep (se 1 (by rfl) ⟨421334, by rfl⟩ : syracuseStep 561779 = 842669) B842669
theorem B561815 : Blo 247818 561815 := bstep (se 1 (by rfl) ⟨421361, by rfl⟩ : syracuseStep 561815 = 842723) B842723
theorem B955097 : Blo 247818 955097 := bstep (se 2 (by rfl) ⟨358161, by rfl⟩ : syracuseStep 955097 = 716323) B716323
theorem B267019 : Blo 247818 267019 := bstep (se 1 (by rfl) ⟨200264, by rfl⟩ : syracuseStep 267019 = 400529) B400529
theorem B561995 : Blo 247818 561995 := bstep (se 1 (by rfl) ⟨421496, by rfl⟩ : syracuseStep 561995 = 842993) B842993
theorem B562049 : Blo 247818 562049 := bstep (se 2 (by rfl) ⟨210768, by rfl⟩ : syracuseStep 562049 = 421537) B421537
theorem B627659 : Blo 247818 627659 := bstep (se 1 (by rfl) ⟨470744, by rfl⟩ : syracuseStep 627659 = 941489) B941489
theorem B2200537 : Blo 247818 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B529409 : Blo 247818 529409 := bstep (se 2 (by rfl) ⟨198528, by rfl⟩ : syracuseStep 529409 = 397057) B397057
theorem B955415 : Blo 247818 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B562265 : Blo 247818 562265 := bstep (se 2 (by rfl) ⟨210849, by rfl⟩ : syracuseStep 562265 = 421699) B421699
theorem B562355 : Blo 247818 562355 := bstep (se 1 (by rfl) ⟨421766, by rfl⟩ : syracuseStep 562355 = 843533) B843533
theorem B562391 : Blo 247818 562391 := bstep (se 1 (by rfl) ⟨421793, by rfl⟩ : syracuseStep 562391 = 843587) B843587
theorem B1348825 : Blo 247818 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B628033 : Blo 247818 628033 := bstep (se 2 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 628033 = 471025) B471025
theorem B562571 : Blo 247818 562571 := bstep (se 1 (by rfl) ⟨421928, by rfl⟩ : syracuseStep 562571 = 843857) B843857
theorem B562625 : Blo 247818 562625 := bstep (se 2 (by rfl) ⟨210984, by rfl⟩ : syracuseStep 562625 = 421969) B421969
theorem B562841 : Blo 247818 562841 := bstep (se 2 (by rfl) ⟨211065, by rfl⟩ : syracuseStep 562841 = 422131) B422131
theorem B956083 : Blo 247818 956083 := bstep (se 1 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 956083 = 1434125) B1434125
theorem B267959 : Blo 247818 267959 := bstep (se 1 (by rfl) ⟨200969, by rfl⟩ : syracuseStep 267959 = 401939) B401939
theorem B530135 : Blo 247818 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B562931 : Blo 247818 562931 := bstep (se 1 (by rfl) ⟨422198, by rfl⟩ : syracuseStep 562931 = 844397) B844397
theorem B562967 : Blo 247818 562967 := bstep (se 1 (by rfl) ⟨422225, by rfl⟩ : syracuseStep 562967 = 844451) B844451
theorem B628631 : Blo 247818 628631 := bstep (se 1 (by rfl) ⟨471473, by rfl⟩ : syracuseStep 628631 = 942947) B942947
theorem B563147 : Blo 247818 563147 := bstep (se 1 (by rfl) ⟨422360, by rfl⟩ : syracuseStep 563147 = 844721) B844721
theorem B563201 : Blo 247818 563201 := bstep (se 2 (by rfl) ⟨211200, by rfl⟩ : syracuseStep 563201 = 422401) B422401
theorem B563417 : Blo 247818 563417 := bstep (se 2 (by rfl) ⟨211281, by rfl⟩ : syracuseStep 563417 = 422563) B422563
theorem B563507 : Blo 247818 563507 := bstep (se 1 (by rfl) ⟨422630, by rfl⟩ : syracuseStep 563507 = 845261) B845261
theorem B563543 : Blo 247818 563543 := bstep (se 1 (by rfl) ⟨422657, by rfl⟩ : syracuseStep 563543 = 845315) B845315
theorem B2038193 : Blo 247818 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B563723 : Blo 247818 563723 := bstep (se 1 (by rfl) ⟨422792, by rfl⟩ : syracuseStep 563723 = 845585) B845585
theorem B563777 : Blo 247818 563777 := bstep (se 2 (by rfl) ⟨211416, by rfl⟩ : syracuseStep 563777 = 422833) B422833
theorem B531031 : Blo 247818 531031 := bstep (se 1 (by rfl) ⟨398273, by rfl⟩ : syracuseStep 531031 = 796547) B796547
theorem B629441 : Blo 247818 629441 := bstep (se 2 (by rfl) ⟨236040, by rfl⟩ : syracuseStep 629441 = 472081) B472081
theorem B563993 : Blo 247818 563993 := bstep (se 2 (by rfl) ⟨211497, by rfl⟩ : syracuseStep 563993 = 422995) B422995
theorem B1514315 : Blo 247818 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B1907549 : Blo 247818 1907549 := bstep (se 3 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 1907549 = 715331) B715331
theorem B564083 : Blo 247818 564083 := bstep (se 1 (by rfl) ⟨423062, by rfl⟩ : syracuseStep 564083 = 846125) B846125
theorem B564119 : Blo 247818 564119 := bstep (se 1 (by rfl) ⟨423089, by rfl⟩ : syracuseStep 564119 = 846179) B846179
theorem B760769 : Blo 247818 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B564299 : Blo 247818 564299 := bstep (se 1 (by rfl) ⟨423224, by rfl⟩ : syracuseStep 564299 = 846449) B846449
theorem B564353 : Blo 247818 564353 := bstep (se 2 (by rfl) ⟨211632, by rfl⟩ : syracuseStep 564353 = 423265) B423265
theorem B629977 : Blo 247818 629977 := bstep (se 2 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 629977 = 472483) B472483
theorem B564569 : Blo 247818 564569 := bstep (se 2 (by rfl) ⟨211713, by rfl⟩ : syracuseStep 564569 = 423427) B423427
theorem B531851 : Blo 247818 531851 := bstep (se 1 (by rfl) ⟨398888, by rfl⟩ : syracuseStep 531851 = 797777) B797777
theorem B564659 : Blo 247818 564659 := bstep (se 1 (by rfl) ⟨423494, by rfl⟩ : syracuseStep 564659 = 846989) B846989
theorem B564695 : Blo 247818 564695 := bstep (se 1 (by rfl) ⟨423521, by rfl⟩ : syracuseStep 564695 = 847043) B847043
theorem B1285649 : Blo 247818 1285649 := bstep (se 2 (by rfl) ⟨482118, by rfl⟩ : syracuseStep 1285649 = 964237) B964237
theorem B597527 : Blo 247818 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B564875 : Blo 247818 564875 := bstep (se 1 (by rfl) ⟨423656, by rfl⟩ : syracuseStep 564875 = 847313) B847313
theorem B794291 : Blo 247818 794291 := bstep (se 1 (by rfl) ⟨595718, by rfl⟩ : syracuseStep 794291 = 1191437) B1191437
theorem B564929 : Blo 247818 564929 := bstep (se 2 (by rfl) ⟨211848, by rfl⟩ : syracuseStep 564929 = 423697) B423697
theorem B958169 : Blo 247818 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B565145 : Blo 247818 565145 := bstep (se 2 (by rfl) ⟨211929, by rfl⟩ : syracuseStep 565145 = 423859) B423859
theorem B565235 : Blo 247818 565235 := bstep (se 1 (by rfl) ⟨423926, by rfl⟩ : syracuseStep 565235 = 847853) B847853
theorem B565271 : Blo 247818 565271 := bstep (se 1 (by rfl) ⟨423953, by rfl⟩ : syracuseStep 565271 = 847907) B847907
theorem B34480241 : Blo 247818 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B532595 : Blo 247818 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B565451 : Blo 247818 565451 := bstep (se 1 (by rfl) ⟨424088, by rfl⟩ : syracuseStep 565451 = 848177) B848177
theorem B565505 : Blo 247818 565505 := bstep (se 2 (by rfl) ⟨212064, by rfl⟩ : syracuseStep 565505 = 424129) B424129
theorem B631091 : Blo 247818 631091 := bstep (se 1 (by rfl) ⟨473318, by rfl⟩ : syracuseStep 631091 = 946637) B946637
theorem B565721 : Blo 247818 565721 := bstep (se 2 (by rfl) ⟨212145, by rfl⟩ : syracuseStep 565721 = 424291) B424291
theorem B565811 : Blo 247818 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B1614401 : Blo 247818 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B598603 : Blo 247818 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B565847 : Blo 247818 565847 := bstep (se 1 (by rfl) ⟨424385, by rfl⟩ : syracuseStep 565847 = 848771) B848771
theorem B631385 : Blo 247818 631385 := bstep (se 2 (by rfl) ⟨236769, by rfl⟩ : syracuseStep 631385 = 473539) B473539
theorem B1352285 : Blo 247818 1352285 := bstep (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) B507107
theorem B271063 : Blo 247818 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B566027 : Blo 247818 566027 := bstep (se 1 (by rfl) ⟨424520, by rfl⟩ : syracuseStep 566027 = 849041) B849041
theorem B566081 : Blo 247818 566081 := bstep (se 2 (by rfl) ⟨212280, by rfl⟩ : syracuseStep 566081 = 424561) B424561
theorem B533441 : Blo 247818 533441 := bstep (se 2 (by rfl) ⟨200040, by rfl⟩ : syracuseStep 533441 = 400081) B400081
theorem B566297 : Blo 247818 566297 := bstep (se 2 (by rfl) ⟨212361, by rfl⟩ : syracuseStep 566297 = 424723) B424723
theorem B566387 : Blo 247818 566387 := bstep (se 1 (by rfl) ⟨424790, by rfl⟩ : syracuseStep 566387 = 849581) B849581
theorem B2270339 : Blo 247818 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B3220631 : Blo 247818 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B566423 : Blo 247818 566423 := bstep (se 1 (by rfl) ⟨424817, by rfl⟩ : syracuseStep 566423 = 849635) B849635
theorem B533783 : Blo 247818 533783 := bstep (se 1 (by rfl) ⟨400337, by rfl⟩ : syracuseStep 533783 = 800675) B800675
theorem B2139979 : Blo 247818 2139979 := bstep (se 1 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 2139979 = 3209969) B3209969
theorem B599987 : Blo 247818 599987 := bstep (se 1 (by rfl) ⟨449990, by rfl⟩ : syracuseStep 599987 = 899981) B899981
theorem B1255499 : Blo 247818 1255499 := bstep (se 1 (by rfl) ⟨941624, by rfl⟩ : syracuseStep 1255499 = 1883249) B1883249
theorem B2140253 : Blo 247818 2140253 := bstep (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) B802595
theorem B633035 : Blo 247818 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B600409 : Blo 247818 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B1059587 : Blo 247818 1059587 := bstep (se 1 (by rfl) ⟨794690, by rfl⟩ : syracuseStep 1059587 = 1589381) B1589381
theorem B2010035 : Blo 247818 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B371735 : Blo 247818 371735 := bstep (se 1 (by rfl) ⟨278801, by rfl⟩ : syracuseStep 371735 = 557603) B557603
theorem B4238405 : Blo 247818 4238405 := bstep (se 4 (by rfl) ⟨397350, by rfl⟩ : syracuseStep 4238405 = 794701) B794701
theorem B371801 : Blo 247818 371801 := bstep (se 2 (by rfl) ⟨139425, by rfl⟩ : syracuseStep 371801 = 278851) B278851
theorem B2141315 : Blo 247818 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B634007 : Blo 247818 634007 := bstep (se 1 (by rfl) ⟨475505, by rfl⟩ : syracuseStep 634007 = 951011) B951011
theorem B371915 : Blo 247818 371915 := bstep (se 1 (by rfl) ⟨278936, by rfl⟩ : syracuseStep 371915 = 557873) B557873
theorem B371927 : Blo 247818 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B339223 : Blo 247818 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B371993 : Blo 247818 371993 := bstep (se 2 (by rfl) ⟨139497, by rfl⟩ : syracuseStep 371993 = 278995) B278995
theorem B339287 : Blo 247818 339287 := bstep (se 1 (by rfl) ⟨254465, by rfl⟩ : syracuseStep 339287 = 508931) B508931
theorem B372107 : Blo 247818 372107 := bstep (se 1 (by rfl) ⟨279080, by rfl⟩ : syracuseStep 372107 = 558161) B558161
theorem B372119 : Blo 247818 372119 := bstep (se 1 (by rfl) ⟨279089, by rfl⟩ : syracuseStep 372119 = 558179) B558179
theorem B372185 : Blo 247818 372185 := bstep (se 2 (by rfl) ⟨139569, by rfl⟩ : syracuseStep 372185 = 279139) B279139
theorem B470539 : Blo 247818 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B372299 : Blo 247818 372299 := bstep (se 1 (by rfl) ⟨279224, by rfl⟩ : syracuseStep 372299 = 558449) B558449
theorem B372311 : Blo 247818 372311 := bstep (se 1 (by rfl) ⟨279233, by rfl⟩ : syracuseStep 372311 = 558467) B558467
theorem B372377 : Blo 247818 372377 := bstep (se 2 (by rfl) ⟨139641, by rfl⟩ : syracuseStep 372377 = 279283) B279283
theorem B372491 : Blo 247818 372491 := bstep (se 1 (by rfl) ⟨279368, by rfl⟩ : syracuseStep 372491 = 558737) B558737
theorem B372503 : Blo 247818 372503 := bstep (se 1 (by rfl) ⟨279377, by rfl⟩ : syracuseStep 372503 = 558755) B558755
theorem B634675 : Blo 247818 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B1257281 : Blo 247818 1257281 := bstep (se 2 (by rfl) ⟨471480, by rfl⟩ : syracuseStep 1257281 = 942961) B942961
theorem B470873 : Blo 247818 470873 := bstep (se 2 (by rfl) ⟨176577, by rfl⟩ : syracuseStep 470873 = 353155) B353155
theorem B372569 : Blo 247818 372569 := bstep (se 2 (by rfl) ⟨139713, by rfl⟩ : syracuseStep 372569 = 279427) B279427
theorem B634817 : Blo 247818 634817 := bstep (se 2 (by rfl) ⟨238056, by rfl⟩ : syracuseStep 634817 = 476113) B476113
theorem B372683 : Blo 247818 372683 := bstep (se 1 (by rfl) ⟨279512, by rfl⟩ : syracuseStep 372683 = 559025) B559025
theorem B372695 : Blo 247818 372695 := bstep (se 1 (by rfl) ⟨279521, by rfl⟩ : syracuseStep 372695 = 559043) B559043
theorem B372761 : Blo 247818 372761 := bstep (se 2 (by rfl) ⟨139785, by rfl⟩ : syracuseStep 372761 = 279571) B279571
theorem B372875 : Blo 247818 372875 := bstep (se 1 (by rfl) ⟨279656, by rfl⟩ : syracuseStep 372875 = 559313) B559313
theorem B372887 : Blo 247818 372887 := bstep (se 1 (by rfl) ⟨279665, by rfl⟩ : syracuseStep 372887 = 559331) B559331
theorem B372953 : Blo 247818 372953 := bstep (se 2 (by rfl) ⟨139857, by rfl⟩ : syracuseStep 372953 = 279715) B279715
theorem B373067 : Blo 247818 373067 := bstep (se 1 (by rfl) ⟨279800, by rfl⟩ : syracuseStep 373067 = 559601) B559601
theorem B373079 : Blo 247818 373079 := bstep (se 1 (by rfl) ⟨279809, by rfl⟩ : syracuseStep 373079 = 559619) B559619
theorem B373145 : Blo 247818 373145 := bstep (se 2 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 373145 = 279859) B279859
theorem B471511 : Blo 247818 471511 := bstep (se 1 (by rfl) ⟨353633, by rfl⟩ : syracuseStep 471511 = 707267) B707267
theorem B373259 : Blo 247818 373259 := bstep (se 1 (by rfl) ⟨279944, by rfl⟩ : syracuseStep 373259 = 559889) B559889
theorem B373271 : Blo 247818 373271 := bstep (se 1 (by rfl) ⟨279953, by rfl⟩ : syracuseStep 373271 = 559907) B559907
theorem B373337 : Blo 247818 373337 := bstep (se 2 (by rfl) ⟨140001, by rfl⟩ : syracuseStep 373337 = 280003) B280003
theorem B373451 : Blo 247818 373451 := bstep (se 1 (by rfl) ⟨280088, by rfl⟩ : syracuseStep 373451 = 560177) B560177
theorem B373463 : Blo 247818 373463 := bstep (se 1 (by rfl) ⟨280097, by rfl⟩ : syracuseStep 373463 = 560195) B560195
theorem B373529 : Blo 247818 373529 := bstep (se 2 (by rfl) ⟨140073, by rfl⟩ : syracuseStep 373529 = 280147) B280147
theorem B373643 : Blo 247818 373643 := bstep (se 1 (by rfl) ⟨280232, by rfl⟩ : syracuseStep 373643 = 560465) B560465
theorem B373655 : Blo 247818 373655 := bstep (se 1 (by rfl) ⟨280241, by rfl⟩ : syracuseStep 373655 = 560483) B560483
theorem B373721 : Blo 247818 373721 := bstep (se 2 (by rfl) ⟨140145, by rfl⟩ : syracuseStep 373721 = 280291) B280291
theorem B2012177 : Blo 247818 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B2831435 : Blo 247818 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B373835 : Blo 247818 373835 := bstep (se 1 (by rfl) ⟨280376, by rfl⟩ : syracuseStep 373835 = 560753) B560753
theorem B373847 : Blo 247818 373847 := bstep (se 1 (by rfl) ⟨280385, by rfl⟩ : syracuseStep 373847 = 560771) B560771
theorem B373913 : Blo 247818 373913 := bstep (se 2 (by rfl) ⟨140217, by rfl⟩ : syracuseStep 373913 = 280435) B280435
theorem B636083 : Blo 247818 636083 := bstep (se 1 (by rfl) ⟨477062, by rfl⟩ : syracuseStep 636083 = 954125) B954125
theorem B537815 : Blo 247818 537815 := bstep (se 1 (by rfl) ⟨403361, by rfl⟩ : syracuseStep 537815 = 806723) B806723
theorem B898307 : Blo 247818 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B472331 : Blo 247818 472331 := bstep (se 1 (by rfl) ⟨354248, by rfl⟩ : syracuseStep 472331 = 708497) B708497
theorem B374027 : Blo 247818 374027 := bstep (se 1 (by rfl) ⟨280520, by rfl⟩ : syracuseStep 374027 = 561041) B561041
theorem B374039 : Blo 247818 374039 := bstep (se 1 (by rfl) ⟨280529, by rfl⟩ : syracuseStep 374039 = 561059) B561059
theorem B472385 : Blo 247818 472385 := bstep (se 2 (by rfl) ⟨177144, by rfl⟩ : syracuseStep 472385 = 354289) B354289
theorem B374105 : Blo 247818 374105 := bstep (se 2 (by rfl) ⟨140289, by rfl⟩ : syracuseStep 374105 = 280579) B280579
theorem B374219 : Blo 247818 374219 := bstep (se 1 (by rfl) ⟨280664, by rfl⟩ : syracuseStep 374219 = 561329) B561329
theorem B374231 : Blo 247818 374231 := bstep (se 1 (by rfl) ⟨280673, by rfl⟩ : syracuseStep 374231 = 561347) B561347
theorem B636439 : Blo 247818 636439 := bstep (se 1 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 636439 = 954659) B954659
theorem B374297 : Blo 247818 374297 := bstep (se 2 (by rfl) ⟨140361, by rfl⟩ : syracuseStep 374297 = 280723) B280723
theorem B1226285 : Blo 247818 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B374411 : Blo 247818 374411 := bstep (se 1 (by rfl) ⟨280808, by rfl⟩ : syracuseStep 374411 = 561617) B561617
theorem B374423 : Blo 247818 374423 := bstep (se 1 (by rfl) ⟨280817, by rfl⟩ : syracuseStep 374423 = 561635) B561635
theorem B636619 : Blo 247818 636619 := bstep (se 1 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 636619 = 954929) B954929
theorem B1259225 : Blo 247818 1259225 := bstep (se 2 (by rfl) ⟨472209, by rfl⟩ : syracuseStep 1259225 = 944419) B944419
theorem B374489 : Blo 247818 374489 := bstep (se 2 (by rfl) ⟨140433, by rfl⟩ : syracuseStep 374489 = 280867) B280867
theorem B1423169 : Blo 247818 1423169 := bstep (se 2 (by rfl) ⟨533688, by rfl⟩ : syracuseStep 1423169 = 1067377) B1067377
theorem B374603 : Blo 247818 374603 := bstep (se 1 (by rfl) ⟨280952, by rfl⟩ : syracuseStep 374603 = 561905) B561905
theorem B374615 : Blo 247818 374615 := bstep (se 1 (by rfl) ⟨280961, by rfl⟩ : syracuseStep 374615 = 561923) B561923
theorem B636761 : Blo 247818 636761 := bstep (se 2 (by rfl) ⟨238785, by rfl⟩ : syracuseStep 636761 = 477571) B477571
theorem B374681 : Blo 247818 374681 := bstep (se 2 (by rfl) ⟨140505, by rfl⟩ : syracuseStep 374681 = 281011) B281011
theorem B374795 : Blo 247818 374795 := bstep (se 1 (by rfl) ⟨281096, by rfl⟩ : syracuseStep 374795 = 562193) B562193
theorem B374807 : Blo 247818 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B374873 : Blo 247818 374873 := bstep (se 2 (by rfl) ⟨140577, by rfl⟩ : syracuseStep 374873 = 281155) B281155
theorem B374987 : Blo 247818 374987 := bstep (se 1 (by rfl) ⟨281240, by rfl⟩ : syracuseStep 374987 = 562481) B562481
theorem B473303 : Blo 247818 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B374999 : Blo 247818 374999 := bstep (se 1 (by rfl) ⟨281249, by rfl⟩ : syracuseStep 374999 = 562499) B562499
theorem B899345 : Blo 247818 899345 := bstep (se 2 (by rfl) ⟨337254, by rfl⟩ : syracuseStep 899345 = 674509) B674509
theorem B375065 : Blo 247818 375065 := bstep (se 2 (by rfl) ⟨140649, by rfl⟩ : syracuseStep 375065 = 281299) B281299
theorem B571673 : Blo 247818 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B375179 : Blo 247818 375179 := bstep (se 1 (by rfl) ⟨281384, by rfl⟩ : syracuseStep 375179 = 562769) B562769
theorem B375191 : Blo 247818 375191 := bstep (se 1 (by rfl) ⟨281393, by rfl⟩ : syracuseStep 375191 = 562787) B562787
theorem B1063361 : Blo 247818 1063361 := bstep (se 2 (by rfl) ⟨398760, by rfl⟩ : syracuseStep 1063361 = 797521) B797521
theorem B375257 : Blo 247818 375257 := bstep (se 2 (by rfl) ⟨140721, by rfl⟩ : syracuseStep 375257 = 281443) B281443
theorem B375371 : Blo 247818 375371 := bstep (se 1 (by rfl) ⟨281528, by rfl⟩ : syracuseStep 375371 = 563057) B563057
theorem B4340299 : Blo 247818 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B375383 : Blo 247818 375383 := bstep (se 1 (by rfl) ⟨281537, by rfl⟩ : syracuseStep 375383 = 563075) B563075
theorem B899677 : Blo 247818 899677 := bstep (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) B337379
theorem B375449 : Blo 247818 375449 := bstep (se 2 (by rfl) ⟨140793, by rfl⟩ : syracuseStep 375449 = 281587) B281587
theorem B473843 : Blo 247818 473843 := bstep (se 1 (by rfl) ⟨355382, by rfl⟩ : syracuseStep 473843 = 710765) B710765
theorem B375563 : Blo 247818 375563 := bstep (se 1 (by rfl) ⟨281672, by rfl⟩ : syracuseStep 375563 = 563345) B563345
theorem B375575 : Blo 247818 375575 := bstep (se 1 (by rfl) ⟨281681, by rfl⟩ : syracuseStep 375575 = 563363) B563363
theorem B375641 : Blo 247818 375641 := bstep (se 2 (by rfl) ⟨140865, by rfl⟩ : syracuseStep 375641 = 281731) B281731
theorem B3849059 : Blo 247818 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B375755 : Blo 247818 375755 := bstep (se 1 (by rfl) ⟨281816, by rfl⟩ : syracuseStep 375755 = 563633) B563633
theorem B375767 : Blo 247818 375767 := bstep (se 1 (by rfl) ⟨281825, by rfl⟩ : syracuseStep 375767 = 563651) B563651
theorem B375833 : Blo 247818 375833 := bstep (se 2 (by rfl) ⟨140937, by rfl⟩ : syracuseStep 375833 = 281875) B281875
theorem B1588355 : Blo 247818 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B375947 : Blo 247818 375947 := bstep (se 1 (by rfl) ⟨281960, by rfl⟩ : syracuseStep 375947 = 563921) B563921
theorem B375959 : Blo 247818 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B474329 : Blo 247818 474329 := bstep (se 2 (by rfl) ⟨177873, by rfl⟩ : syracuseStep 474329 = 355747) B355747
theorem B376025 : Blo 247818 376025 := bstep (se 2 (by rfl) ⟨141009, by rfl⟩ : syracuseStep 376025 = 282019) B282019
theorem B1260845 : Blo 247818 1260845 := bstep (se 3 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 1260845 = 472817) B472817
theorem B376139 : Blo 247818 376139 := bstep (se 1 (by rfl) ⟨282104, by rfl⟩ : syracuseStep 376139 = 564209) B564209
theorem B376151 : Blo 247818 376151 := bstep (se 1 (by rfl) ⟨282113, by rfl⟩ : syracuseStep 376151 = 564227) B564227
theorem B1064285 : Blo 247818 1064285 := bstep (se 3 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 1064285 = 399107) B399107
theorem B376217 : Blo 247818 376217 := bstep (se 2 (by rfl) ⟨141081, by rfl⟩ : syracuseStep 376217 = 282163) B282163
theorem B671179 : Blo 247818 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B376331 : Blo 247818 376331 := bstep (se 1 (by rfl) ⟨282248, by rfl⟩ : syracuseStep 376331 = 564497) B564497
theorem B376343 : Blo 247818 376343 := bstep (se 1 (by rfl) ⟨282257, by rfl⟩ : syracuseStep 376343 = 564515) B564515
theorem B2276909 : Blo 247818 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B802379 : Blo 247818 802379 := bstep (se 1 (by rfl) ⟨601784, by rfl⟩ : syracuseStep 802379 = 1203569) B1203569
theorem B376409 : Blo 247818 376409 := bstep (se 2 (by rfl) ⟨141153, by rfl⟩ : syracuseStep 376409 = 282307) B282307
theorem B507521 : Blo 247818 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B605875 : Blo 247818 605875 := bstep (se 1 (by rfl) ⟨454406, by rfl⟩ : syracuseStep 605875 = 908813) B908813
theorem B376523 : Blo 247818 376523 := bstep (se 1 (by rfl) ⟨282392, by rfl⟩ : syracuseStep 376523 = 564785) B564785
theorem B376535 : Blo 247818 376535 := bstep (se 1 (by rfl) ⟨282401, by rfl⟩ : syracuseStep 376535 = 564803) B564803
theorem B376601 : Blo 247818 376601 := bstep (se 2 (by rfl) ⟨141225, by rfl⟩ : syracuseStep 376601 = 282451) B282451
theorem B376715 : Blo 247818 376715 := bstep (se 1 (by rfl) ⟨282536, by rfl⟩ : syracuseStep 376715 = 565073) B565073
theorem B376727 : Blo 247818 376727 := bstep (se 1 (by rfl) ⟨282545, by rfl⟩ : syracuseStep 376727 = 565091) B565091
theorem B2473907 : Blo 247818 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B376793 : Blo 247818 376793 := bstep (se 2 (by rfl) ⟨141297, by rfl⟩ : syracuseStep 376793 = 282595) B282595
theorem B376907 : Blo 247818 376907 := bstep (se 1 (by rfl) ⟨282680, by rfl⟩ : syracuseStep 376907 = 565361) B565361
theorem B376919 : Blo 247818 376919 := bstep (se 1 (by rfl) ⟨282689, by rfl⟩ : syracuseStep 376919 = 565379) B565379
theorem B4079747 : Blo 247818 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B1425559 : Blo 247818 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B376985 : Blo 247818 376985 := bstep (se 2 (by rfl) ⟨141369, by rfl⟩ : syracuseStep 376985 = 282739) B282739
theorem B377099 : Blo 247818 377099 := bstep (se 1 (by rfl) ⟨282824, by rfl⟩ : syracuseStep 377099 = 565649) B565649
theorem B377111 : Blo 247818 377111 := bstep (se 1 (by rfl) ⟨282833, by rfl⟩ : syracuseStep 377111 = 565667) B565667
theorem B901421 : Blo 247818 901421 := bstep (se 3 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 901421 = 338033) B338033
theorem B377177 : Blo 247818 377177 := bstep (se 2 (by rfl) ⟨141441, by rfl⟩ : syracuseStep 377177 = 282883) B282883
theorem B278923 : Blo 247818 278923 := bstep (se 1 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 278923 = 418385) B418385
theorem B1360307 : Blo 247818 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B377291 : Blo 247818 377291 := bstep (se 1 (by rfl) ⟨282968, by rfl⟩ : syracuseStep 377291 = 565937) B565937
theorem B377303 : Blo 247818 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B279031 : Blo 247818 279031 := bstep (se 1 (by rfl) ⟨209273, by rfl⟩ : syracuseStep 279031 = 418547) B418547
theorem B377369 : Blo 247818 377369 := bstep (se 2 (by rfl) ⟨141513, by rfl⟩ : syracuseStep 377369 = 283027) B283027
theorem B1884707 : Blo 247818 1884707 := bstep (se 1 (by rfl) ⟨1413530, by rfl⟩ : syracuseStep 1884707 = 2827061) B2827061
theorem B475787 : Blo 247818 475787 := bstep (se 1 (by rfl) ⟨356840, by rfl⟩ : syracuseStep 475787 = 713681) B713681
theorem B377483 : Blo 247818 377483 := bstep (se 1 (by rfl) ⟨283112, by rfl⟩ : syracuseStep 377483 = 566225) B566225
theorem B377495 : Blo 247818 377495 := bstep (se 1 (by rfl) ⟨283121, by rfl⟩ : syracuseStep 377495 = 566243) B566243
theorem B279211 : Blo 247818 279211 := bstep (se 1 (by rfl) ⟨209408, by rfl⟩ : syracuseStep 279211 = 418817) B418817
theorem B377561 : Blo 247818 377561 := bstep (se 2 (by rfl) ⟨141585, by rfl⟩ : syracuseStep 377561 = 283171) B283171
theorem B279319 : Blo 247818 279319 := bstep (se 1 (by rfl) ⟨209489, by rfl⟩ : syracuseStep 279319 = 418979) B418979
theorem B672563 : Blo 247818 672563 := bstep (se 1 (by rfl) ⟨504422, by rfl⟩ : syracuseStep 672563 = 1008845) B1008845
theorem B475969 : Blo 247818 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B377675 : Blo 247818 377675 := bstep (se 1 (by rfl) ⟨283256, by rfl⟩ : syracuseStep 377675 = 566513) B566513
theorem B377687 : Blo 247818 377687 := bstep (se 1 (by rfl) ⟨283265, by rfl⟩ : syracuseStep 377687 = 566531) B566531
theorem B770905 : Blo 247818 770905 := bstep (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) B578179
theorem B672605 : Blo 247818 672605 := bstep (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) B252227
theorem B279499 : Blo 247818 279499 := bstep (se 1 (by rfl) ⟨209624, by rfl⟩ : syracuseStep 279499 = 419249) B419249
theorem B279607 : Blo 247818 279607 := bstep (se 1 (by rfl) ⟨209705, by rfl⟩ : syracuseStep 279607 = 419411) B419411
theorem B672857 : Blo 247818 672857 := bstep (se 2 (by rfl) ⟨252321, by rfl⟩ : syracuseStep 672857 = 504643) B504643
theorem B541811 : Blo 247818 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B377995 : Blo 247818 377995 := bstep (se 1 (by rfl) ⟨283496, by rfl⟩ : syracuseStep 377995 = 566993) B566993
theorem B804019 : Blo 247818 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B279787 : Blo 247818 279787 := bstep (se 1 (by rfl) ⟨209840, by rfl⟩ : syracuseStep 279787 = 419681) B419681
theorem B476417 : Blo 247818 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B279895 : Blo 247818 279895 := bstep (se 1 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 279895 = 419843) B419843
theorem B542081 : Blo 247818 542081 := bstep (se 2 (by rfl) ⟨203280, by rfl⟩ : syracuseStep 542081 = 406561) B406561
theorem B280075 : Blo 247818 280075 := bstep (se 1 (by rfl) ⟨210056, by rfl⟩ : syracuseStep 280075 = 420113) B420113
theorem B2606627 : Blo 247818 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B476759 : Blo 247818 476759 := bstep (se 1 (by rfl) ⟨357569, by rfl⟩ : syracuseStep 476759 = 715139) B715139
theorem B280183 : Blo 247818 280183 := bstep (se 1 (by rfl) ⟨210137, by rfl⟩ : syracuseStep 280183 = 420275) B420275
theorem B837323 : Blo 247818 837323 := bstep (se 1 (by rfl) ⟨627992, by rfl⟩ : syracuseStep 837323 = 1255985) B1255985
theorem B706265 : Blo 247818 706265 := bstep (se 2 (by rfl) ⟨264849, by rfl⟩ : syracuseStep 706265 = 529699) B529699
theorem B280363 : Blo 247818 280363 := bstep (se 1 (by rfl) ⟨210272, by rfl⟩ : syracuseStep 280363 = 420545) B420545
theorem B280471 : Blo 247818 280471 := bstep (se 1 (by rfl) ⟨210353, by rfl⟩ : syracuseStep 280471 = 420707) B420707
theorem B837593 : Blo 247818 837593 := bstep (se 2 (by rfl) ⟨314097, by rfl⟩ : syracuseStep 837593 = 628195) B628195
theorem B247819 : Blo 247818 247819 := bstep (se 1 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 247819 = 371729) B371729
theorem B247831 : Blo 247818 247831 := bstep (se 1 (by rfl) ⟨185873, by rfl⟩ : syracuseStep 247831 = 371747) B371747
theorem B706583 : Blo 247818 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B247851 : Blo 247818 247851 := bstep (se 1 (by rfl) ⟨185888, by rfl⟩ : syracuseStep 247851 = 371777) B371777
theorem B247863 : Blo 247818 247863 := bstep (se 1 (by rfl) ⟨185897, by rfl⟩ : syracuseStep 247863 = 371795) B371795
theorem B247883 : Blo 247818 247883 := bstep (se 1 (by rfl) ⟨185912, by rfl⟩ : syracuseStep 247883 = 371825) B371825
theorem B280651 : Blo 247818 280651 := bstep (se 1 (by rfl) ⟨210488, by rfl⟩ : syracuseStep 280651 = 420977) B420977
theorem B247895 : Blo 247818 247895 := bstep (se 1 (by rfl) ⟨185921, by rfl⟩ : syracuseStep 247895 = 371843) B371843
theorem B804953 : Blo 247818 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B247915 : Blo 247818 247915 := bstep (se 1 (by rfl) ⟨185936, by rfl⟩ : syracuseStep 247915 = 371873) B371873
theorem B510067 : Blo 247818 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B247927 : Blo 247818 247927 := bstep (se 1 (by rfl) ⟨185945, by rfl⟩ : syracuseStep 247927 = 371891) B371891
theorem B247947 : Blo 247818 247947 := bstep (se 1 (by rfl) ⟨185960, by rfl⟩ : syracuseStep 247947 = 371921) B371921
theorem B247959 : Blo 247818 247959 := bstep (se 1 (by rfl) ⟨185969, by rfl⟩ : syracuseStep 247959 = 371939) B371939
theorem B247979 : Blo 247818 247979 := bstep (se 1 (by rfl) ⟨185984, by rfl⟩ : syracuseStep 247979 = 371969) B371969
theorem B1099955 : Blo 247818 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B247991 : Blo 247818 247991 := bstep (se 1 (by rfl) ⟨185993, by rfl⟩ : syracuseStep 247991 = 371987) B371987
theorem B280759 : Blo 247818 280759 := bstep (se 1 (by rfl) ⟨210569, by rfl⟩ : syracuseStep 280759 = 421139) B421139
theorem B248011 : Blo 247818 248011 := bstep (se 1 (by rfl) ⟨186008, by rfl⟩ : syracuseStep 248011 = 372017) B372017
theorem B248023 : Blo 247818 248023 := bstep (se 1 (by rfl) ⟨186017, by rfl⟩ : syracuseStep 248023 = 372035) B372035
theorem B248043 : Blo 247818 248043 := bstep (se 1 (by rfl) ⟨186032, by rfl⟩ : syracuseStep 248043 = 372065) B372065
theorem B477427 : Blo 247818 477427 := bstep (se 1 (by rfl) ⟨358070, by rfl⟩ : syracuseStep 477427 = 716141) B716141
theorem B248055 : Blo 247818 248055 := bstep (se 1 (by rfl) ⟨186041, by rfl⟩ : syracuseStep 248055 = 372083) B372083
theorem B248075 : Blo 247818 248075 := bstep (se 1 (by rfl) ⟨186056, by rfl⟩ : syracuseStep 248075 = 372113) B372113
theorem B248087 : Blo 247818 248087 := bstep (se 1 (by rfl) ⟨186065, by rfl⟩ : syracuseStep 248087 = 372131) B372131
theorem B248107 : Blo 247818 248107 := bstep (se 1 (by rfl) ⟨186080, by rfl⟩ : syracuseStep 248107 = 372161) B372161
theorem B10799405 : Blo 247818 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B248119 : Blo 247818 248119 := bstep (se 1 (by rfl) ⟨186089, by rfl⟩ : syracuseStep 248119 = 372179) B372179
theorem B248139 : Blo 247818 248139 := bstep (se 1 (by rfl) ⟨186104, by rfl⟩ : syracuseStep 248139 = 372209) B372209
theorem B248151 : Blo 247818 248151 := bstep (se 1 (by rfl) ⟨186113, by rfl⟩ : syracuseStep 248151 = 372227) B372227
theorem B248171 : Blo 247818 248171 := bstep (se 1 (by rfl) ⟨186128, by rfl⟩ : syracuseStep 248171 = 372257) B372257
theorem B280939 : Blo 247818 280939 := bstep (se 1 (by rfl) ⟨210704, by rfl⟩ : syracuseStep 280939 = 421409) B421409
theorem B248183 : Blo 247818 248183 := bstep (se 1 (by rfl) ⟨186137, by rfl⟩ : syracuseStep 248183 = 372275) B372275
theorem B248203 : Blo 247818 248203 := bstep (se 1 (by rfl) ⟨186152, by rfl⟩ : syracuseStep 248203 = 372305) B372305
theorem B248215 : Blo 247818 248215 := bstep (se 1 (by rfl) ⟨186161, by rfl⟩ : syracuseStep 248215 = 372323) B372323
theorem B248235 : Blo 247818 248235 := bstep (se 1 (by rfl) ⟨186176, by rfl⟩ : syracuseStep 248235 = 372353) B372353
theorem B248247 : Blo 247818 248247 := bstep (se 1 (by rfl) ⟨186185, by rfl⟩ : syracuseStep 248247 = 372371) B372371
theorem B248267 : Blo 247818 248267 := bstep (se 1 (by rfl) ⟨186200, by rfl⟩ : syracuseStep 248267 = 372401) B372401
theorem B248279 : Blo 247818 248279 := bstep (se 1 (by rfl) ⟨186209, by rfl⟩ : syracuseStep 248279 = 372419) B372419
theorem B281047 : Blo 247818 281047 := bstep (se 1 (by rfl) ⟨210785, by rfl⟩ : syracuseStep 281047 = 421571) B421571
theorem B903641 : Blo 247818 903641 := bstep (se 2 (by rfl) ⟨338865, by rfl⟩ : syracuseStep 903641 = 677731) B677731
theorem B248299 : Blo 247818 248299 := bstep (se 1 (by rfl) ⟨186224, by rfl⟩ : syracuseStep 248299 = 372449) B372449
theorem B248311 : Blo 247818 248311 := bstep (se 1 (by rfl) ⟨186233, by rfl⟩ : syracuseStep 248311 = 372467) B372467
theorem B248331 : Blo 247818 248331 := bstep (se 1 (by rfl) ⟨186248, by rfl⟩ : syracuseStep 248331 = 372497) B372497
theorem B248343 : Blo 247818 248343 := bstep (se 1 (by rfl) ⟨186257, by rfl⟩ : syracuseStep 248343 = 372515) B372515
theorem B248363 : Blo 247818 248363 := bstep (se 1 (by rfl) ⟨186272, by rfl⟩ : syracuseStep 248363 = 372545) B372545
theorem B248375 : Blo 247818 248375 := bstep (se 1 (by rfl) ⟨186281, by rfl⟩ : syracuseStep 248375 = 372563) B372563
theorem B248395 : Blo 247818 248395 := bstep (se 1 (by rfl) ⟨186296, by rfl⟩ : syracuseStep 248395 = 372593) B372593
theorem B3066443 : Blo 247818 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B248407 : Blo 247818 248407 := bstep (se 1 (by rfl) ⟨186305, by rfl⟩ : syracuseStep 248407 = 372611) B372611
theorem B248427 : Blo 247818 248427 := bstep (se 1 (by rfl) ⟨186320, by rfl⟩ : syracuseStep 248427 = 372641) B372641
theorem B248439 : Blo 247818 248439 := bstep (se 1 (by rfl) ⟨186329, by rfl⟩ : syracuseStep 248439 = 372659) B372659
theorem B1067651 : Blo 247818 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B248459 : Blo 247818 248459 := bstep (se 1 (by rfl) ⟨186344, by rfl⟩ : syracuseStep 248459 = 372689) B372689
theorem B281227 : Blo 247818 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B838295 : Blo 247818 838295 := bstep (se 1 (by rfl) ⟨628721, by rfl⟩ : syracuseStep 838295 = 1257443) B1257443
theorem B248471 : Blo 247818 248471 := bstep (se 1 (by rfl) ⟨186353, by rfl⟩ : syracuseStep 248471 = 372707) B372707
theorem B248491 : Blo 247818 248491 := bstep (se 1 (by rfl) ⟨186368, by rfl⟩ : syracuseStep 248491 = 372737) B372737
theorem B1821361 : Blo 247818 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B477875 : Blo 247818 477875 := bstep (se 1 (by rfl) ⟨358406, by rfl⟩ : syracuseStep 477875 = 716813) B716813
theorem B248503 : Blo 247818 248503 := bstep (se 1 (by rfl) ⟨186377, by rfl⟩ : syracuseStep 248503 = 372755) B372755
theorem B248523 : Blo 247818 248523 := bstep (se 1 (by rfl) ⟨186392, by rfl⟩ : syracuseStep 248523 = 372785) B372785
theorem B248535 : Blo 247818 248535 := bstep (se 1 (by rfl) ⟨186401, by rfl⟩ : syracuseStep 248535 = 372803) B372803
theorem B477913 : Blo 247818 477913 := bstep (se 2 (by rfl) ⟨179217, by rfl⟩ : syracuseStep 477913 = 358435) B358435
theorem B248555 : Blo 247818 248555 := bstep (se 1 (by rfl) ⟨186416, by rfl⟩ : syracuseStep 248555 = 372833) B372833
theorem B248567 : Blo 247818 248567 := bstep (se 1 (by rfl) ⟨186425, by rfl⟩ : syracuseStep 248567 = 372851) B372851
theorem B281335 : Blo 247818 281335 := bstep (se 1 (by rfl) ⟨211001, by rfl⟩ : syracuseStep 281335 = 422003) B422003
theorem B248587 : Blo 247818 248587 := bstep (se 1 (by rfl) ⟨186440, by rfl⟩ : syracuseStep 248587 = 372881) B372881
theorem B248599 : Blo 247818 248599 := bstep (se 1 (by rfl) ⟨186449, by rfl⟩ : syracuseStep 248599 = 372899) B372899
theorem B248619 : Blo 247818 248619 := bstep (se 1 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 248619 = 372929) B372929
theorem B248631 : Blo 247818 248631 := bstep (se 1 (by rfl) ⟨186473, by rfl⟩ : syracuseStep 248631 = 372947) B372947
theorem B707393 : Blo 247818 707393 := bstep (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) B530545
theorem B805697 : Blo 247818 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B248651 : Blo 247818 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B248663 : Blo 247818 248663 := bstep (se 1 (by rfl) ⟨186497, by rfl⟩ : syracuseStep 248663 = 372995) B372995
theorem B248683 : Blo 247818 248683 := bstep (se 1 (by rfl) ⟨186512, by rfl⟩ : syracuseStep 248683 = 373025) B373025
theorem B248695 : Blo 247818 248695 := bstep (se 1 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 248695 = 373043) B373043
theorem B248715 : Blo 247818 248715 := bstep (se 1 (by rfl) ⟨186536, by rfl⟩ : syracuseStep 248715 = 373073) B373073
theorem B248727 : Blo 247818 248727 := bstep (se 1 (by rfl) ⟨186545, by rfl⟩ : syracuseStep 248727 = 373091) B373091
theorem B248747 : Blo 247818 248747 := bstep (se 1 (by rfl) ⟨186560, by rfl⟩ : syracuseStep 248747 = 373121) B373121
theorem B281515 : Blo 247818 281515 := bstep (se 1 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 281515 = 422273) B422273
theorem B2411441 : Blo 247818 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B248759 : Blo 247818 248759 := bstep (se 1 (by rfl) ⟨186569, by rfl⟩ : syracuseStep 248759 = 373139) B373139
theorem B248779 : Blo 247818 248779 := bstep (se 1 (by rfl) ⟨186584, by rfl⟩ : syracuseStep 248779 = 373169) B373169
theorem B248791 : Blo 247818 248791 := bstep (se 1 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 248791 = 373187) B373187
theorem B248811 : Blo 247818 248811 := bstep (se 1 (by rfl) ⟨186608, by rfl⟩ : syracuseStep 248811 = 373217) B373217
theorem B248823 : Blo 247818 248823 := bstep (se 1 (by rfl) ⟨186617, by rfl⟩ : syracuseStep 248823 = 373235) B373235
theorem B248843 : Blo 247818 248843 := bstep (se 1 (by rfl) ⟨186632, by rfl⟩ : syracuseStep 248843 = 373265) B373265
theorem B248855 : Blo 247818 248855 := bstep (se 1 (by rfl) ⟨186641, by rfl⟩ : syracuseStep 248855 = 373283) B373283
theorem B281623 : Blo 247818 281623 := bstep (se 1 (by rfl) ⟨211217, by rfl⟩ : syracuseStep 281623 = 422435) B422435
theorem B248875 : Blo 247818 248875 := bstep (se 1 (by rfl) ⟨186656, by rfl⟩ : syracuseStep 248875 = 373313) B373313
theorem B248887 : Blo 247818 248887 := bstep (se 1 (by rfl) ⟨186665, by rfl⟩ : syracuseStep 248887 = 373331) B373331
theorem B248907 : Blo 247818 248907 := bstep (se 1 (by rfl) ⟨186680, by rfl⟩ : syracuseStep 248907 = 373361) B373361
theorem B248919 : Blo 247818 248919 := bstep (se 1 (by rfl) ⟨186689, by rfl⟩ : syracuseStep 248919 = 373379) B373379
theorem B1264733 : Blo 247818 1264733 := bstep (se 3 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 1264733 = 474275) B474275
theorem B248939 : Blo 247818 248939 := bstep (se 1 (by rfl) ⟨186704, by rfl⟩ : syracuseStep 248939 = 373409) B373409
theorem B248951 : Blo 247818 248951 := bstep (se 1 (by rfl) ⟨186713, by rfl⟩ : syracuseStep 248951 = 373427) B373427
theorem B248971 : Blo 247818 248971 := bstep (se 1 (by rfl) ⟨186728, by rfl⟩ : syracuseStep 248971 = 373457) B373457
theorem B248983 : Blo 247818 248983 := bstep (se 1 (by rfl) ⟨186737, by rfl⟩ : syracuseStep 248983 = 373475) B373475
theorem B249003 : Blo 247818 249003 := bstep (se 1 (by rfl) ⟨186752, by rfl⟩ : syracuseStep 249003 = 373505) B373505
theorem B838835 : Blo 247818 838835 := bstep (se 1 (by rfl) ⟨629126, by rfl⟩ : syracuseStep 838835 = 1258253) B1258253
theorem B1133747 : Blo 247818 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B249015 : Blo 247818 249015 := bstep (se 1 (by rfl) ⟨186761, by rfl⟩ : syracuseStep 249015 = 373523) B373523
theorem B249035 : Blo 247818 249035 := bstep (se 1 (by rfl) ⟨186776, by rfl⟩ : syracuseStep 249035 = 373553) B373553
theorem B281803 : Blo 247818 281803 := bstep (se 1 (by rfl) ⟨211352, by rfl⟩ : syracuseStep 281803 = 422705) B422705
theorem B249047 : Blo 247818 249047 := bstep (se 1 (by rfl) ⟨186785, by rfl⟩ : syracuseStep 249047 = 373571) B373571
theorem B249067 : Blo 247818 249067 := bstep (se 1 (by rfl) ⟨186800, by rfl⟩ : syracuseStep 249067 = 373601) B373601
theorem B249079 : Blo 247818 249079 := bstep (se 1 (by rfl) ⟨186809, by rfl⟩ : syracuseStep 249079 = 373619) B373619
theorem B249099 : Blo 247818 249099 := bstep (se 1 (by rfl) ⟨186824, by rfl⟩ : syracuseStep 249099 = 373649) B373649
theorem B478487 : Blo 247818 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B249111 : Blo 247818 249111 := bstep (se 1 (by rfl) ⟨186833, by rfl⟩ : syracuseStep 249111 = 373667) B373667
theorem B249131 : Blo 247818 249131 := bstep (se 1 (by rfl) ⟨186848, by rfl⟩ : syracuseStep 249131 = 373697) B373697
theorem B249143 : Blo 247818 249143 := bstep (se 1 (by rfl) ⟨186857, by rfl⟩ : syracuseStep 249143 = 373715) B373715
theorem B281911 : Blo 247818 281911 := bstep (se 1 (by rfl) ⟨211433, by rfl⟩ : syracuseStep 281911 = 422867) B422867
theorem B249163 : Blo 247818 249163 := bstep (se 1 (by rfl) ⟨186872, by rfl⟩ : syracuseStep 249163 = 373745) B373745
theorem B249175 : Blo 247818 249175 := bstep (se 1 (by rfl) ⟨186881, by rfl⟩ : syracuseStep 249175 = 373763) B373763
theorem B249195 : Blo 247818 249195 := bstep (se 1 (by rfl) ⟨186896, by rfl⟩ : syracuseStep 249195 = 373793) B373793
theorem B249207 : Blo 247818 249207 := bstep (se 1 (by rfl) ⟨186905, by rfl⟩ : syracuseStep 249207 = 373811) B373811
theorem B249227 : Blo 247818 249227 := bstep (se 1 (by rfl) ⟨186920, by rfl⟩ : syracuseStep 249227 = 373841) B373841
theorem B249239 : Blo 247818 249239 := bstep (se 1 (by rfl) ⟨186929, by rfl⟩ : syracuseStep 249239 = 373859) B373859
theorem B249259 : Blo 247818 249259 := bstep (se 1 (by rfl) ⟨186944, by rfl⟩ : syracuseStep 249259 = 373889) B373889
theorem B249271 : Blo 247818 249271 := bstep (se 1 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 249271 = 373907) B373907
theorem B839105 : Blo 247818 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B249291 : Blo 247818 249291 := bstep (se 1 (by rfl) ⟨186968, by rfl⟩ : syracuseStep 249291 = 373937) B373937
theorem B249303 : Blo 247818 249303 := bstep (se 1 (by rfl) ⟨186977, by rfl⟩ : syracuseStep 249303 = 373955) B373955
theorem B249323 : Blo 247818 249323 := bstep (se 1 (by rfl) ⟨186992, by rfl⟩ : syracuseStep 249323 = 373985) B373985
theorem B282091 : Blo 247818 282091 := bstep (se 1 (by rfl) ⟨211568, by rfl⟩ : syracuseStep 282091 = 423137) B423137
theorem B249335 : Blo 247818 249335 := bstep (se 1 (by rfl) ⟨187001, by rfl⟩ : syracuseStep 249335 = 374003) B374003
theorem B249355 : Blo 247818 249355 := bstep (se 1 (by rfl) ⟨187016, by rfl⟩ : syracuseStep 249355 = 374033) B374033
theorem B3919373 : Blo 247818 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B249367 : Blo 247818 249367 := bstep (se 1 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 249367 = 374051) B374051
theorem B249387 : Blo 247818 249387 := bstep (se 1 (by rfl) ⟨187040, by rfl⟩ : syracuseStep 249387 = 374081) B374081
theorem B249399 : Blo 247818 249399 := bstep (se 1 (by rfl) ⟨187049, by rfl⟩ : syracuseStep 249399 = 374099) B374099
theorem B249419 : Blo 247818 249419 := bstep (se 1 (by rfl) ⟨187064, by rfl⟩ : syracuseStep 249419 = 374129) B374129
theorem B249431 : Blo 247818 249431 := bstep (se 1 (by rfl) ⟨187073, by rfl⟩ : syracuseStep 249431 = 374147) B374147
theorem B282199 : Blo 247818 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B249451 : Blo 247818 249451 := bstep (se 1 (by rfl) ⟨187088, by rfl⟩ : syracuseStep 249451 = 374177) B374177
theorem B249463 : Blo 247818 249463 := bstep (se 1 (by rfl) ⟨187097, by rfl⟩ : syracuseStep 249463 = 374195) B374195
theorem B315019 : Blo 247818 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B249483 : Blo 247818 249483 := bstep (se 1 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 249483 = 374225) B374225
theorem B249495 : Blo 247818 249495 := bstep (se 1 (by rfl) ⟨187121, by rfl⟩ : syracuseStep 249495 = 374243) B374243
theorem B249515 : Blo 247818 249515 := bstep (se 1 (by rfl) ⟨187136, by rfl⟩ : syracuseStep 249515 = 374273) B374273
theorem B249527 : Blo 247818 249527 := bstep (se 1 (by rfl) ⟨187145, by rfl⟩ : syracuseStep 249527 = 374291) B374291
theorem B806593 : Blo 247818 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B249547 : Blo 247818 249547 := bstep (se 1 (by rfl) ⟨187160, by rfl⟩ : syracuseStep 249547 = 374321) B374321
theorem B6082253 : Blo 247818 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B249559 : Blo 247818 249559 := bstep (se 1 (by rfl) ⟨187169, by rfl⟩ : syracuseStep 249559 = 374339) B374339
theorem B249579 : Blo 247818 249579 := bstep (se 1 (by rfl) ⟨187184, by rfl⟩ : syracuseStep 249579 = 374369) B374369
theorem B249591 : Blo 247818 249591 := bstep (se 1 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 249591 = 374387) B374387
theorem B249611 : Blo 247818 249611 := bstep (se 1 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 249611 = 374417) B374417
theorem B282379 : Blo 247818 282379 := bstep (se 1 (by rfl) ⟨211784, by rfl⟩ : syracuseStep 282379 = 423569) B423569
theorem B249623 : Blo 247818 249623 := bstep (se 1 (by rfl) ⟨187217, by rfl⟩ : syracuseStep 249623 = 374435) B374435
theorem B249643 : Blo 247818 249643 := bstep (se 1 (by rfl) ⟨187232, by rfl⟩ : syracuseStep 249643 = 374465) B374465
theorem B249655 : Blo 247818 249655 := bstep (se 1 (by rfl) ⟨187241, by rfl⟩ : syracuseStep 249655 = 374483) B374483
theorem B249675 : Blo 247818 249675 := bstep (se 1 (by rfl) ⟨187256, by rfl⟩ : syracuseStep 249675 = 374513) B374513
theorem B249687 : Blo 247818 249687 := bstep (se 1 (by rfl) ⟨187265, by rfl⟩ : syracuseStep 249687 = 374531) B374531
theorem B675677 : Blo 247818 675677 := bstep (se 3 (by rfl) ⟨126689, by rfl⟩ : syracuseStep 675677 = 253379) B253379
theorem B249707 : Blo 247818 249707 := bstep (se 1 (by rfl) ⟨187280, by rfl⟩ : syracuseStep 249707 = 374561) B374561
theorem B249719 : Blo 247818 249719 := bstep (se 1 (by rfl) ⟨187289, by rfl⟩ : syracuseStep 249719 = 374579) B374579
theorem B282487 : Blo 247818 282487 := bstep (se 1 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 282487 = 423731) B423731
theorem B249739 : Blo 247818 249739 := bstep (se 1 (by rfl) ⟨187304, by rfl⟩ : syracuseStep 249739 = 374609) B374609
theorem B249751 : Blo 247818 249751 := bstep (se 1 (by rfl) ⟨187313, by rfl⟩ : syracuseStep 249751 = 374627) B374627
theorem B905111 : Blo 247818 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B249771 : Blo 247818 249771 := bstep (se 1 (by rfl) ⟨187328, by rfl⟩ : syracuseStep 249771 = 374657) B374657
theorem B249783 : Blo 247818 249783 := bstep (se 1 (by rfl) ⟨187337, by rfl⟩ : syracuseStep 249783 = 374675) B374675
theorem B249803 : Blo 247818 249803 := bstep (se 1 (by rfl) ⟨187352, by rfl⟩ : syracuseStep 249803 = 374705) B374705
theorem B249815 : Blo 247818 249815 := bstep (se 1 (by rfl) ⟨187361, by rfl⟩ : syracuseStep 249815 = 374723) B374723
theorem B839645 : Blo 247818 839645 := bstep (se 3 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 839645 = 314867) B314867
theorem B249835 : Blo 247818 249835 := bstep (se 1 (by rfl) ⟨187376, by rfl⟩ : syracuseStep 249835 = 374753) B374753
theorem B249847 : Blo 247818 249847 := bstep (se 1 (by rfl) ⟨187385, by rfl⟩ : syracuseStep 249847 = 374771) B374771
theorem B249867 : Blo 247818 249867 := bstep (se 1 (by rfl) ⟨187400, by rfl⟩ : syracuseStep 249867 = 374801) B374801
theorem B249879 : Blo 247818 249879 := bstep (se 1 (by rfl) ⟨187409, by rfl⟩ : syracuseStep 249879 = 374819) B374819
theorem B249899 : Blo 247818 249899 := bstep (se 1 (by rfl) ⟨187424, by rfl⟩ : syracuseStep 249899 = 374849) B374849
theorem B282667 : Blo 247818 282667 := bstep (se 1 (by rfl) ⟨212000, by rfl⟩ : syracuseStep 282667 = 424001) B424001
theorem B249911 : Blo 247818 249911 := bstep (se 1 (by rfl) ⟨187433, by rfl⟩ : syracuseStep 249911 = 374867) B374867
theorem B1200203 : Blo 247818 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B249931 : Blo 247818 249931 := bstep (se 1 (by rfl) ⟨187448, by rfl⟩ : syracuseStep 249931 = 374897) B374897
theorem B249943 : Blo 247818 249943 := bstep (se 1 (by rfl) ⟨187457, by rfl⟩ : syracuseStep 249943 = 374915) B374915
theorem B249963 : Blo 247818 249963 := bstep (se 1 (by rfl) ⟨187472, by rfl⟩ : syracuseStep 249963 = 374945) B374945
theorem B249975 : Blo 247818 249975 := bstep (se 1 (by rfl) ⟨187481, by rfl⟩ : syracuseStep 249975 = 374963) B374963
theorem B249995 : Blo 247818 249995 := bstep (se 1 (by rfl) ⟨187496, by rfl⟩ : syracuseStep 249995 = 374993) B374993
theorem B250007 : Blo 247818 250007 := bstep (se 1 (by rfl) ⟨187505, by rfl⟩ : syracuseStep 250007 = 375011) B375011
theorem B282775 : Blo 247818 282775 := bstep (se 1 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 282775 = 424163) B424163
theorem B250027 : Blo 247818 250027 := bstep (se 1 (by rfl) ⟨187520, by rfl⟩ : syracuseStep 250027 = 375041) B375041
theorem B250039 : Blo 247818 250039 := bstep (se 1 (by rfl) ⟨187529, by rfl⟩ : syracuseStep 250039 = 375059) B375059
theorem B250059 : Blo 247818 250059 := bstep (se 1 (by rfl) ⟨187544, by rfl⟩ : syracuseStep 250059 = 375089) B375089
theorem B250071 : Blo 247818 250071 := bstep (se 1 (by rfl) ⟨187553, by rfl⟩ : syracuseStep 250071 = 375107) B375107
theorem B250091 : Blo 247818 250091 := bstep (se 1 (by rfl) ⟨187568, by rfl⟩ : syracuseStep 250091 = 375137) B375137
theorem B250103 : Blo 247818 250103 := bstep (se 1 (by rfl) ⟨187577, by rfl⟩ : syracuseStep 250103 = 375155) B375155
theorem B4837637 : Blo 247818 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B250123 : Blo 247818 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B250135 : Blo 247818 250135 := bstep (se 1 (by rfl) ⟨187601, by rfl⟩ : syracuseStep 250135 = 375203) B375203
theorem B250155 : Blo 247818 250155 := bstep (se 1 (by rfl) ⟨187616, by rfl⟩ : syracuseStep 250155 = 375233) B375233
theorem B250167 : Blo 247818 250167 := bstep (se 1 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 250167 = 375251) B375251
theorem B250187 : Blo 247818 250187 := bstep (se 1 (by rfl) ⟨187640, by rfl⟩ : syracuseStep 250187 = 375281) B375281
theorem B282955 : Blo 247818 282955 := bstep (se 1 (by rfl) ⟨212216, by rfl⟩ : syracuseStep 282955 = 424433) B424433
theorem B250199 : Blo 247818 250199 := bstep (se 1 (by rfl) ⟨187649, by rfl⟩ : syracuseStep 250199 = 375299) B375299
theorem B250219 : Blo 247818 250219 := bstep (se 1 (by rfl) ⟨187664, by rfl⟩ : syracuseStep 250219 = 375329) B375329
theorem B250231 : Blo 247818 250231 := bstep (se 1 (by rfl) ⟨187673, by rfl⟩ : syracuseStep 250231 = 375347) B375347
theorem B250251 : Blo 247818 250251 := bstep (se 1 (by rfl) ⟨187688, by rfl⟩ : syracuseStep 250251 = 375377) B375377
theorem B250263 : Blo 247818 250263 := bstep (se 1 (by rfl) ⟨187697, by rfl⟩ : syracuseStep 250263 = 375395) B375395
theorem B250283 : Blo 247818 250283 := bstep (se 1 (by rfl) ⟨187712, by rfl⟩ : syracuseStep 250283 = 375425) B375425
theorem B2019763 : Blo 247818 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B283063 : Blo 247818 283063 := bstep (se 1 (by rfl) ⟨212297, by rfl⟩ : syracuseStep 283063 = 424595) B424595
theorem B250295 : Blo 247818 250295 := bstep (se 1 (by rfl) ⟨187721, by rfl⟩ : syracuseStep 250295 = 375443) B375443
theorem B709067 : Blo 247818 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B250315 : Blo 247818 250315 := bstep (se 1 (by rfl) ⟨187736, by rfl⟩ : syracuseStep 250315 = 375473) B375473
theorem B250327 : Blo 247818 250327 := bstep (se 1 (by rfl) ⟨187745, by rfl⟩ : syracuseStep 250327 = 375491) B375491
theorem B1364441 : Blo 247818 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B250347 : Blo 247818 250347 := bstep (se 1 (by rfl) ⟨187760, by rfl⟩ : syracuseStep 250347 = 375521) B375521
theorem B250359 : Blo 247818 250359 := bstep (se 1 (by rfl) ⟨187769, by rfl⟩ : syracuseStep 250359 = 375539) B375539
theorem B250379 : Blo 247818 250379 := bstep (se 1 (by rfl) ⟨187784, by rfl⟩ : syracuseStep 250379 = 375569) B375569
theorem B250391 : Blo 247818 250391 := bstep (se 1 (by rfl) ⟨187793, by rfl⟩ : syracuseStep 250391 = 375587) B375587
theorem B250411 : Blo 247818 250411 := bstep (se 1 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 250411 = 375617) B375617
theorem B250423 : Blo 247818 250423 := bstep (se 1 (by rfl) ⟨187817, by rfl⟩ : syracuseStep 250423 = 375635) B375635
theorem B250443 : Blo 247818 250443 := bstep (se 1 (by rfl) ⟨187832, by rfl⟩ : syracuseStep 250443 = 375665) B375665
theorem B315991 : Blo 247818 315991 := bstep (se 1 (by rfl) ⟨236993, by rfl⟩ : syracuseStep 315991 = 473987) B473987
theorem B250455 : Blo 247818 250455 := bstep (se 1 (by rfl) ⟨187841, by rfl⟩ : syracuseStep 250455 = 375683) B375683
theorem B250475 : Blo 247818 250475 := bstep (se 1 (by rfl) ⟨187856, by rfl⟩ : syracuseStep 250475 = 375713) B375713
theorem B283243 : Blo 247818 283243 := bstep (se 1 (by rfl) ⟨212432, by rfl⟩ : syracuseStep 283243 = 424865) B424865
theorem B250487 : Blo 247818 250487 := bstep (se 1 (by rfl) ⟨187865, by rfl⟩ : syracuseStep 250487 = 375731) B375731
theorem B250507 : Blo 247818 250507 := bstep (se 1 (by rfl) ⟨187880, by rfl⟩ : syracuseStep 250507 = 375761) B375761
theorem B250519 : Blo 247818 250519 := bstep (se 1 (by rfl) ⟨187889, by rfl⟩ : syracuseStep 250519 = 375779) B375779
theorem B250539 : Blo 247818 250539 := bstep (se 1 (by rfl) ⟨187904, by rfl⟩ : syracuseStep 250539 = 375809) B375809
theorem B250551 : Blo 247818 250551 := bstep (se 1 (by rfl) ⟨187913, by rfl⟩ : syracuseStep 250551 = 375827) B375827
theorem B250571 : Blo 247818 250571 := bstep (se 1 (by rfl) ⟨187928, by rfl⟩ : syracuseStep 250571 = 375857) B375857
theorem B283351 : Blo 247818 283351 := bstep (se 1 (by rfl) ⟨212513, by rfl⟩ : syracuseStep 283351 = 425027) B425027
theorem B250583 : Blo 247818 250583 := bstep (se 1 (by rfl) ⟨187937, by rfl⟩ : syracuseStep 250583 = 375875) B375875
theorem B250603 : Blo 247818 250603 := bstep (se 1 (by rfl) ⟨187952, by rfl⟩ : syracuseStep 250603 = 375905) B375905
theorem B250615 : Blo 247818 250615 := bstep (se 1 (by rfl) ⟨187961, by rfl⟩ : syracuseStep 250615 = 375923) B375923
theorem B250635 : Blo 247818 250635 := bstep (se 1 (by rfl) ⟨187976, by rfl⟩ : syracuseStep 250635 = 375953) B375953
theorem B250647 : Blo 247818 250647 := bstep (se 1 (by rfl) ⟨187985, by rfl⟩ : syracuseStep 250647 = 375971) B375971
theorem B250667 : Blo 247818 250667 := bstep (se 1 (by rfl) ⟨188000, by rfl⟩ : syracuseStep 250667 = 376001) B376001
theorem B250679 : Blo 247818 250679 := bstep (se 1 (by rfl) ⟨188009, by rfl⟩ : syracuseStep 250679 = 376019) B376019
theorem B250699 : Blo 247818 250699 := bstep (se 1 (by rfl) ⟨188024, by rfl⟩ : syracuseStep 250699 = 376049) B376049
theorem B250711 : Blo 247818 250711 := bstep (se 1 (by rfl) ⟨188033, by rfl⟩ : syracuseStep 250711 = 376067) B376067
theorem B250731 : Blo 247818 250731 := bstep (se 1 (by rfl) ⟨188048, by rfl⟩ : syracuseStep 250731 = 376097) B376097
theorem B250743 : Blo 247818 250743 := bstep (se 1 (by rfl) ⟨188057, by rfl⟩ : syracuseStep 250743 = 376115) B376115
theorem B250763 : Blo 247818 250763 := bstep (se 1 (by rfl) ⟨188072, by rfl⟩ : syracuseStep 250763 = 376145) B376145
theorem B250775 : Blo 247818 250775 := bstep (se 1 (by rfl) ⟨188081, by rfl⟩ : syracuseStep 250775 = 376163) B376163
theorem B250795 : Blo 247818 250795 := bstep (se 1 (by rfl) ⟨188096, by rfl⟩ : syracuseStep 250795 = 376193) B376193
theorem B250807 : Blo 247818 250807 := bstep (se 1 (by rfl) ⟨188105, by rfl⟩ : syracuseStep 250807 = 376211) B376211
theorem B250827 : Blo 247818 250827 := bstep (se 1 (by rfl) ⟨188120, by rfl⟩ : syracuseStep 250827 = 376241) B376241
theorem B250839 : Blo 247818 250839 := bstep (se 1 (by rfl) ⟨188129, by rfl⟩ : syracuseStep 250839 = 376259) B376259
theorem B250859 : Blo 247818 250859 := bstep (se 1 (by rfl) ⟨188144, by rfl⟩ : syracuseStep 250859 = 376289) B376289
theorem B250871 : Blo 247818 250871 := bstep (se 1 (by rfl) ⟨188153, by rfl⟩ : syracuseStep 250871 = 376307) B376307
theorem B250891 : Blo 247818 250891 := bstep (se 1 (by rfl) ⟨188168, by rfl⟩ : syracuseStep 250891 = 376337) B376337
theorem B250903 : Blo 247818 250903 := bstep (se 1 (by rfl) ⟨188177, by rfl⟩ : syracuseStep 250903 = 376355) B376355
theorem B250923 : Blo 247818 250923 := bstep (se 1 (by rfl) ⟨188192, by rfl⟩ : syracuseStep 250923 = 376385) B376385
theorem B250935 : Blo 247818 250935 := bstep (se 1 (by rfl) ⟨188201, by rfl⟩ : syracuseStep 250935 = 376403) B376403
theorem B840779 : Blo 247818 840779 := bstep (se 1 (by rfl) ⟨630584, by rfl⟩ : syracuseStep 840779 = 1261169) B1261169
theorem B250955 : Blo 247818 250955 := bstep (se 1 (by rfl) ⟨188216, by rfl⟩ : syracuseStep 250955 = 376433) B376433
theorem B250967 : Blo 247818 250967 := bstep (se 1 (by rfl) ⟨188225, by rfl⟩ : syracuseStep 250967 = 376451) B376451
theorem B250987 : Blo 247818 250987 := bstep (se 1 (by rfl) ⟨188240, by rfl⟩ : syracuseStep 250987 = 376481) B376481
theorem B250999 : Blo 247818 250999 := bstep (se 1 (by rfl) ⟨188249, by rfl⟩ : syracuseStep 250999 = 376499) B376499
theorem B251019 : Blo 247818 251019 := bstep (se 1 (by rfl) ⟨188264, by rfl⟩ : syracuseStep 251019 = 376529) B376529
theorem B1266839 : Blo 247818 1266839 := bstep (se 1 (by rfl) ⟨950129, by rfl⟩ : syracuseStep 1266839 = 1900259) B1900259
theorem B251031 : Blo 247818 251031 := bstep (se 1 (by rfl) ⟨188273, by rfl⟩ : syracuseStep 251031 = 376547) B376547
theorem B251051 : Blo 247818 251051 := bstep (se 1 (by rfl) ⟨188288, by rfl⟩ : syracuseStep 251051 = 376577) B376577
theorem B251063 : Blo 247818 251063 := bstep (se 1 (by rfl) ⟨188297, by rfl⟩ : syracuseStep 251063 = 376595) B376595
theorem B251083 : Blo 247818 251083 := bstep (se 1 (by rfl) ⟨188312, by rfl⟩ : syracuseStep 251083 = 376625) B376625
theorem B251095 : Blo 247818 251095 := bstep (se 1 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 251095 = 376643) B376643
theorem B251115 : Blo 247818 251115 := bstep (se 1 (by rfl) ⟨188336, by rfl⟩ : syracuseStep 251115 = 376673) B376673
theorem B251127 : Blo 247818 251127 := bstep (se 1 (by rfl) ⟨188345, by rfl⟩ : syracuseStep 251127 = 376691) B376691
theorem B251147 : Blo 247818 251147 := bstep (se 1 (by rfl) ⟨188360, by rfl⟩ : syracuseStep 251147 = 376721) B376721
theorem B251159 : Blo 247818 251159 := bstep (se 1 (by rfl) ⟨188369, by rfl⟩ : syracuseStep 251159 = 376739) B376739
theorem B251179 : Blo 247818 251179 := bstep (se 1 (by rfl) ⟨188384, by rfl⟩ : syracuseStep 251179 = 376769) B376769
theorem B251191 : Blo 247818 251191 := bstep (se 1 (by rfl) ⟨188393, by rfl⟩ : syracuseStep 251191 = 376787) B376787
theorem B251211 : Blo 247818 251211 := bstep (se 1 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 251211 = 376817) B376817
theorem B251223 : Blo 247818 251223 := bstep (se 1 (by rfl) ⟨188417, by rfl⟩ : syracuseStep 251223 = 376835) B376835
theorem B841049 : Blo 247818 841049 := bstep (se 2 (by rfl) ⟨315393, by rfl⟩ : syracuseStep 841049 = 630787) B630787
theorem B251243 : Blo 247818 251243 := bstep (se 1 (by rfl) ⟨188432, by rfl⟩ : syracuseStep 251243 = 376865) B376865
theorem B251255 : Blo 247818 251255 := bstep (se 1 (by rfl) ⟨188441, by rfl⟩ : syracuseStep 251255 = 376883) B376883
theorem B316811 : Blo 247818 316811 := bstep (se 1 (by rfl) ⟨237608, by rfl⟩ : syracuseStep 316811 = 475217) B475217
theorem B251275 : Blo 247818 251275 := bstep (se 1 (by rfl) ⟨188456, by rfl⟩ : syracuseStep 251275 = 376913) B376913
theorem B251287 : Blo 247818 251287 := bstep (se 1 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 251287 = 376931) B376931
theorem B251307 : Blo 247818 251307 := bstep (se 1 (by rfl) ⟨188480, by rfl⟩ : syracuseStep 251307 = 376961) B376961
theorem B251319 : Blo 247818 251319 := bstep (se 1 (by rfl) ⟨188489, by rfl⟩ : syracuseStep 251319 = 376979) B376979
theorem B251339 : Blo 247818 251339 := bstep (se 1 (by rfl) ⟨188504, by rfl⟩ : syracuseStep 251339 = 377009) B377009
theorem B251351 : Blo 247818 251351 := bstep (se 1 (by rfl) ⟨188513, by rfl⟩ : syracuseStep 251351 = 377027) B377027
theorem B251371 : Blo 247818 251371 := bstep (se 1 (by rfl) ⟨188528, by rfl⟩ : syracuseStep 251371 = 377057) B377057
theorem B251383 : Blo 247818 251383 := bstep (se 1 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 251383 = 377075) B377075
theorem B448001 : Blo 247818 448001 := bstep (se 2 (by rfl) ⟨168000, by rfl⟩ : syracuseStep 448001 = 336001) B336001
theorem B251403 : Blo 247818 251403 := bstep (se 1 (by rfl) ⟨188552, by rfl⟩ : syracuseStep 251403 = 377105) B377105
theorem B251415 : Blo 247818 251415 := bstep (se 1 (by rfl) ⟨188561, by rfl⟩ : syracuseStep 251415 = 377123) B377123
theorem B251435 : Blo 247818 251435 := bstep (se 1 (by rfl) ⟨188576, by rfl⟩ : syracuseStep 251435 = 377153) B377153
theorem B251447 : Blo 247818 251447 := bstep (se 1 (by rfl) ⟨188585, by rfl⟩ : syracuseStep 251447 = 377171) B377171
theorem B251467 : Blo 247818 251467 := bstep (se 1 (by rfl) ⟨188600, by rfl⟩ : syracuseStep 251467 = 377201) B377201
theorem B251479 : Blo 247818 251479 := bstep (se 1 (by rfl) ⟨188609, by rfl⟩ : syracuseStep 251479 = 377219) B377219
theorem B251499 : Blo 247818 251499 := bstep (se 1 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 251499 = 377249) B377249
theorem B251511 : Blo 247818 251511 := bstep (se 1 (by rfl) ⟨188633, by rfl⟩ : syracuseStep 251511 = 377267) B377267
theorem B251531 : Blo 247818 251531 := bstep (se 1 (by rfl) ⟨188648, by rfl⟩ : syracuseStep 251531 = 377297) B377297
theorem B251543 : Blo 247818 251543 := bstep (se 1 (by rfl) ⟨188657, by rfl⟩ : syracuseStep 251543 = 377315) B377315
theorem B251563 : Blo 247818 251563 := bstep (se 1 (by rfl) ⟨188672, by rfl⟩ : syracuseStep 251563 = 377345) B377345
theorem B251575 : Blo 247818 251575 := bstep (se 1 (by rfl) ⟨188681, by rfl⟩ : syracuseStep 251575 = 377363) B377363
theorem B251595 : Blo 247818 251595 := bstep (se 1 (by rfl) ⟨188696, by rfl⟩ : syracuseStep 251595 = 377393) B377393
theorem B4085453 : Blo 247818 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B251607 : Blo 247818 251607 := bstep (se 1 (by rfl) ⟨188705, by rfl⟩ : syracuseStep 251607 = 377411) B377411
theorem B710365 : Blo 247818 710365 := bstep (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) B266387
theorem B251627 : Blo 247818 251627 := bstep (se 1 (by rfl) ⟨188720, by rfl⟩ : syracuseStep 251627 = 377441) B377441
theorem B251639 : Blo 247818 251639 := bstep (se 1 (by rfl) ⟨188729, by rfl⟩ : syracuseStep 251639 = 377459) B377459
theorem B1890053 : Blo 247818 1890053 := bstep (se 4 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 1890053 = 354385) B354385
theorem B251659 : Blo 247818 251659 := bstep (se 1 (by rfl) ⟨188744, by rfl⟩ : syracuseStep 251659 = 377489) B377489
theorem B251671 : Blo 247818 251671 := bstep (se 1 (by rfl) ⟨188753, by rfl⟩ : syracuseStep 251671 = 377507) B377507
theorem B251691 : Blo 247818 251691 := bstep (se 1 (by rfl) ⟨188768, by rfl⟩ : syracuseStep 251691 = 377537) B377537
theorem B251703 : Blo 247818 251703 := bstep (se 1 (by rfl) ⟨188777, by rfl⟩ : syracuseStep 251703 = 377555) B377555
theorem B251723 : Blo 247818 251723 := bstep (se 1 (by rfl) ⟨188792, by rfl⟩ : syracuseStep 251723 = 377585) B377585
theorem B251735 : Blo 247818 251735 := bstep (se 1 (by rfl) ⟨188801, by rfl⟩ : syracuseStep 251735 = 377603) B377603
theorem B251755 : Blo 247818 251755 := bstep (se 1 (by rfl) ⟨188816, by rfl⟩ : syracuseStep 251755 = 377633) B377633
theorem B251767 : Blo 247818 251767 := bstep (se 1 (by rfl) ⟨188825, by rfl⟩ : syracuseStep 251767 = 377651) B377651
theorem B251787 : Blo 247818 251787 := bstep (se 1 (by rfl) ⟨188840, by rfl⟩ : syracuseStep 251787 = 377681) B377681
theorem B251799 : Blo 247818 251799 := bstep (se 1 (by rfl) ⟨188849, by rfl⟩ : syracuseStep 251799 = 377699) B377699
theorem B481241 : Blo 247818 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B841751 : Blo 247818 841751 := bstep (se 1 (by rfl) ⟨631313, by rfl⟩ : syracuseStep 841751 = 1262627) B1262627
theorem B710707 : Blo 247818 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B317515 : Blo 247818 317515 := bstep (se 1 (by rfl) ⟨238136, by rfl⟩ : syracuseStep 317515 = 476273) B476273
theorem B317783 : Blo 247818 317783 := bstep (se 1 (by rfl) ⟨238337, by rfl⟩ : syracuseStep 317783 = 476675) B476675
theorem B612887 : Blo 247818 612887 := bstep (se 1 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 612887 = 919331) B919331
theorem B842291 : Blo 247818 842291 := bstep (se 1 (by rfl) ⟨631718, by rfl⟩ : syracuseStep 842291 = 1263437) B1263437
theorem B1071767 : Blo 247818 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B809651 : Blo 247818 809651 := bstep (se 1 (by rfl) ⟨607238, by rfl⟩ : syracuseStep 809651 = 1214477) B1214477
theorem B842561 : Blo 247818 842561 := bstep (se 2 (by rfl) ⟨315960, by rfl⟩ : syracuseStep 842561 = 631921) B631921
theorem B252779 : Blo 247818 252779 := bstep (se 1 (by rfl) ⟨189584, by rfl⟩ : syracuseStep 252779 = 379169) B379169
theorem B941003 : Blo 247818 941003 := bstep (se 1 (by rfl) ⟨705752, by rfl⟩ : syracuseStep 941003 = 1411505) B1411505
theorem B1072075 : Blo 247818 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B941017 : Blo 247818 941017 := bstep (se 2 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 941017 = 705763) B705763
theorem B711641 : Blo 247818 711641 := bstep (se 2 (by rfl) ⟨266865, by rfl⟩ : syracuseStep 711641 = 533731) B533731
theorem B318487 : Blo 247818 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B318539 : Blo 247818 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B679115 : Blo 247818 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B1072349 : Blo 247818 1072349 := bstep (se 3 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 1072349 = 402131) B402131
theorem B1432849 : Blo 247818 1432849 := bstep (se 2 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 1432849 = 1074637) B1074637
theorem B843101 : Blo 247818 843101 := bstep (se 3 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 843101 = 316163) B316163
theorem B679603 : Blo 247818 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B941975 : Blo 247818 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B450625 : Blo 247818 450625 := bstep (se 2 (by rfl) ⟨168984, by rfl⟩ : syracuseStep 450625 = 337969) B337969
theorem B1892483 : Blo 247818 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B8151191 : Blo 247818 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B286999 : Blo 247818 286999 := bstep (se 1 (by rfl) ⟨215249, by rfl⟩ : syracuseStep 286999 = 430499) B430499
theorem B450841 : Blo 247818 450841 := bstep (se 2 (by rfl) ⟨169065, by rfl⟩ : syracuseStep 450841 = 338131) B338131
theorem B2711873 : Blo 247818 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B713053 : Blo 247818 713053 := bstep (se 3 (by rfl) ⟨133697, by rfl⟩ : syracuseStep 713053 = 267395) B267395
theorem B844235 : Blo 247818 844235 := bstep (se 1 (by rfl) ⟨633176, by rfl⟩ : syracuseStep 844235 = 1266353) B1266353
theorem B1597913 : Blo 247818 1597913 := bstep (se 2 (by rfl) ⟨599217, by rfl⟩ : syracuseStep 1597913 = 1198435) B1198435
theorem B1073681 : Blo 247818 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B713281 : Blo 247818 713281 := bstep (se 2 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 713281 = 534961) B534961
theorem B909899 : Blo 247818 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B254539 : Blo 247818 254539 := bstep (se 1 (by rfl) ⟨190904, by rfl⟩ : syracuseStep 254539 = 381809) B381809
theorem B1270403 : Blo 247818 1270403 := bstep (se 1 (by rfl) ⟨952802, by rfl⟩ : syracuseStep 1270403 = 1905605) B1905605
theorem B844505 : Blo 247818 844505 := bstep (se 2 (by rfl) ⟨316689, by rfl⟩ : syracuseStep 844505 = 633379) B633379
theorem B1630937 : Blo 247818 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B713623 : Blo 247818 713623 := bstep (se 1 (by rfl) ⟨535217, by rfl⟩ : syracuseStep 713623 = 1070435) B1070435
theorem B1008557 : Blo 247818 1008557 := bstep (se 3 (by rfl) ⟨189104, by rfl⟩ : syracuseStep 1008557 = 378209) B378209
theorem B418763 : Blo 247818 418763 := bstep (se 1 (by rfl) ⟨314072, by rfl⟩ : syracuseStep 418763 = 628145) B628145
theorem B2122757 : Blo 247818 2122757 := bstep (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) B398017
theorem B418891 : Blo 247818 418891 := bstep (se 1 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 418891 = 628337) B628337
theorem B943235 : Blo 247818 943235 := bstep (se 1 (by rfl) ⟨707426, by rfl⟩ : syracuseStep 943235 = 1414853) B1414853
theorem B353497 : Blo 247818 353497 := bstep (se 2 (by rfl) ⟨132561, by rfl⟩ : syracuseStep 353497 = 265123) B265123
theorem B419033 : Blo 247818 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B419161 : Blo 247818 419161 := bstep (se 2 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 419161 = 314371) B314371
theorem B2024797 : Blo 247818 2024797 := bstep (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) B759299
theorem B1795459 : Blo 247818 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B845207 : Blo 247818 845207 := bstep (se 1 (by rfl) ⟨633905, by rfl⟩ : syracuseStep 845207 = 1267811) B1267811
theorem B714329 : Blo 247818 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B2123441 : Blo 247818 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B452441 : Blo 247818 452441 := bstep (se 2 (by rfl) ⟨169665, by rfl⟩ : syracuseStep 452441 = 339331) B339331
theorem B419735 : Blo 247818 419735 := bstep (se 1 (by rfl) ⟨314801, by rfl⟩ : syracuseStep 419735 = 629603) B629603
theorem B845747 : Blo 247818 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B419863 : Blo 247818 419863 := bstep (se 1 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 419863 = 629795) B629795
theorem B846017 : Blo 247818 846017 := bstep (se 2 (by rfl) ⟨317256, by rfl⟩ : syracuseStep 846017 = 634513) B634513
theorem B453017 : Blo 247818 453017 := bstep (se 2 (by rfl) ⟨169881, by rfl⟩ : syracuseStep 453017 = 339763) B339763
theorem B420491 : Blo 247818 420491 := bstep (se 1 (by rfl) ⟨315368, by rfl⟩ : syracuseStep 420491 = 630737) B630737
theorem B354955 : Blo 247818 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B2124467 : Blo 247818 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B1010369 : Blo 247818 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B846557 : Blo 247818 846557 := bstep (se 3 (by rfl) ⟨158729, by rfl⟩ : syracuseStep 846557 = 317459) B317459
theorem B420619 : Blo 247818 420619 := bstep (se 1 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 420619 = 630929) B630929
theorem B420761 : Blo 247818 420761 := bstep (se 2 (by rfl) ⟨157785, by rfl⟩ : syracuseStep 420761 = 315571) B315571
theorem B420889 : Blo 247818 420889 := bstep (se 2 (by rfl) ⟨157833, by rfl⟩ : syracuseStep 420889 = 315667) B315667
theorem B715969 : Blo 247818 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B1240337 : Blo 247818 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B1895885 : Blo 247818 1895885 := bstep (se 3 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 1895885 = 710957) B710957
theorem B421463 : Blo 247818 421463 := bstep (se 1 (by rfl) ⟨316097, by rfl⟩ : syracuseStep 421463 = 632195) B632195
theorem B1273495 : Blo 247818 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B2420375 : Blo 247818 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B13758149 : Blo 247818 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B4812493 : Blo 247818 4812493 := bstep (se 3 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 4812493 = 1804685) B1804685
theorem B421591 : Blo 247818 421591 := bstep (se 1 (by rfl) ⟨316193, by rfl⟩ : syracuseStep 421591 = 632387) B632387
theorem B847691 : Blo 247818 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B356185 : Blo 247818 356185 := bstep (se 2 (by rfl) ⟨133569, by rfl⟩ : syracuseStep 356185 = 267139) B267139
theorem B1011635 : Blo 247818 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B1896371 : Blo 247818 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B847961 : Blo 247818 847961 := bstep (se 2 (by rfl) ⟨317985, by rfl⟩ : syracuseStep 847961 = 635971) B635971
theorem B946349 : Blo 247818 946349 := bstep (se 3 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 946349 = 354881) B354881
theorem B1274129 : Blo 247818 1274129 := bstep (se 2 (by rfl) ⟨477798, by rfl⟩ : syracuseStep 1274129 = 955597) B955597
theorem B422219 : Blo 247818 422219 := bstep (se 1 (by rfl) ⟨316664, by rfl⟩ : syracuseStep 422219 = 633329) B633329
theorem B1700189 : Blo 247818 1700189 := bstep (se 3 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 1700189 = 637571) B637571
theorem B1274291 : Blo 247818 1274291 := bstep (se 1 (by rfl) ⟨955718, by rfl⟩ : syracuseStep 1274291 = 1911437) B1911437
theorem B422347 : Blo 247818 422347 := bstep (se 1 (by rfl) ⟨316760, by rfl⟩ : syracuseStep 422347 = 633521) B633521
theorem B422489 : Blo 247818 422489 := bstep (se 2 (by rfl) ⟨158433, by rfl⟩ : syracuseStep 422489 = 316867) B316867
theorem B1798807 : Blo 247818 1798807 := bstep (se 1 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 1798807 = 2698211) B2698211
theorem B422617 : Blo 247818 422617 := bstep (se 2 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 422617 = 316963) B316963
theorem B848663 : Blo 247818 848663 := bstep (se 1 (by rfl) ⟨636497, by rfl⟩ : syracuseStep 848663 = 1272995) B1272995
theorem B947123 : Blo 247818 947123 := bstep (se 1 (by rfl) ⟨710342, by rfl⟩ : syracuseStep 947123 = 1420685) B1420685
theorem B357529 : Blo 247818 357529 := bstep (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) B268147
theorem B357643 : Blo 247818 357643 := bstep (se 1 (by rfl) ⟨268232, by rfl⟩ : syracuseStep 357643 = 536465) B536465
theorem B423191 : Blo 247818 423191 := bstep (se 1 (by rfl) ⟨317393, by rfl⟩ : syracuseStep 423191 = 634787) B634787
theorem B455987 : Blo 247818 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B849203 : Blo 247818 849203 := bstep (se 1 (by rfl) ⟨636902, by rfl⟩ : syracuseStep 849203 = 1273805) B1273805
theorem B1897829 : Blo 247818 1897829 := bstep (se 4 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 1897829 = 355843) B355843
theorem B423319 : Blo 247818 423319 := bstep (se 1 (by rfl) ⟨317489, by rfl⟩ : syracuseStep 423319 = 634979) B634979
theorem B849473 : Blo 247818 849473 := bstep (se 2 (by rfl) ⟨318552, by rfl⟩ : syracuseStep 849473 = 637105) B637105
theorem B1898315 : Blo 247818 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B423947 : Blo 247818 423947 := bstep (se 1 (by rfl) ⟨317960, by rfl⟩ : syracuseStep 423947 = 635921) B635921
theorem B424075 : Blo 247818 424075 := bstep (se 1 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 424075 = 636113) B636113
theorem B424217 : Blo 247818 424217 := bstep (se 2 (by rfl) ⟨159081, by rfl⟩ : syracuseStep 424217 = 318163) B318163
theorem B2128193 : Blo 247818 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B8092021 : Blo 247818 8092021 := bstep (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) B758627
theorem B948611 : Blo 247818 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B424345 : Blo 247818 424345 := bstep (se 2 (by rfl) ⟨159129, by rfl⟩ : syracuseStep 424345 = 318259) B318259
theorem B2095651 : Blo 247818 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B949067 : Blo 247818 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B424919 : Blo 247818 424919 := bstep (se 1 (by rfl) ⟨318689, by rfl⟩ : syracuseStep 424919 = 637379) B637379
theorem B1080337 : Blo 247818 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B949265 : Blo 247818 949265 := bstep (se 2 (by rfl) ⟨355974, by rfl⟩ : syracuseStep 949265 = 711949) B711949
theorem B916525 : Blo 247818 916525 := bstep (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) B343697
theorem B1343051 : Blo 247818 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B950039 : Blo 247818 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B950237 : Blo 247818 950237 := bstep (se 3 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 950237 = 356339) B356339
theorem B2719831 : Blo 247818 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B1900745 : Blo 247818 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B950737 : Blo 247818 950737 := bstep (se 2 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 950737 = 713053) B713053
theorem B1409501 : Blo 247818 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B361207 : Blo 247818 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B951041 : Blo 247818 951041 := bstep (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) B713281
theorem B3015539 : Blo 247818 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B361387 : Blo 247818 361387 := bstep (se 1 (by rfl) ⟨271040, by rfl⟩ : syracuseStep 361387 = 542081) B542081
theorem B361417 : Blo 247818 361417 := bstep (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) B271063
theorem B558215 : Blo 247818 558215 := bstep (se 1 (by rfl) ⟨418661, by rfl⟩ : syracuseStep 558215 = 837323) B837323
theorem B951497 : Blo 247818 951497 := bstep (se 2 (by rfl) ⟨356811, by rfl⟩ : syracuseStep 951497 = 713623) B713623
theorem B558395 : Blo 247818 558395 := bstep (se 1 (by rfl) ⟨418796, by rfl⟩ : syracuseStep 558395 = 837593) B837593
theorem B558521 : Blo 247818 558521 := bstep (se 2 (by rfl) ⟨209445, by rfl⟩ : syracuseStep 558521 = 418891) B418891
theorem B558863 : Blo 247818 558863 := bstep (se 1 (by rfl) ⟨419147, by rfl⟩ : syracuseStep 558863 = 838295) B838295
theorem B558881 : Blo 247818 558881 := bstep (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) B419161
theorem B2393945 : Blo 247818 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B853895 : Blo 247818 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B1607627 : Blo 247818 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B559223 : Blo 247818 559223 := bstep (se 1 (by rfl) ⟨419417, by rfl⟩ : syracuseStep 559223 = 838835) B838835
theorem B755831 : Blo 247818 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B559403 : Blo 247818 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B5114177 : Blo 247818 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B2853305 : Blo 247818 2853305 := bstep (se 2 (by rfl) ⟨1069989, by rfl⟩ : syracuseStep 2853305 = 2139979) B2139979
theorem B559763 : Blo 247818 559763 := bstep (se 1 (by rfl) ⟨419822, by rfl⟩ : syracuseStep 559763 = 839645) B839645
theorem B559817 : Blo 247818 559817 := bstep (se 2 (by rfl) ⟨209931, by rfl⟩ : syracuseStep 559817 = 419863) B419863
theorem B723799 : Blo 247818 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B560519 : Blo 247818 560519 := bstep (se 1 (by rfl) ⟨420389, by rfl⟩ : syracuseStep 560519 = 840779) B840779
theorem B1215965 : Blo 247818 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B560699 : Blo 247818 560699 := bstep (se 1 (by rfl) ⟨420524, by rfl⟩ : syracuseStep 560699 = 841049) B841049
theorem B2428481 : Blo 247818 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B298667 : Blo 247818 298667 := bstep (se 1 (by rfl) ⟨224000, by rfl⟩ : syracuseStep 298667 = 448001) B448001
theorem B560825 : Blo 247818 560825 := bstep (se 2 (by rfl) ⟨210309, by rfl⟩ : syracuseStep 560825 = 420619) B420619
theorem B2723635 : Blo 247818 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B561167 : Blo 247818 561167 := bstep (se 1 (by rfl) ⟨420875, by rfl⟩ : syracuseStep 561167 = 841751) B841751
theorem B561185 : Blo 247818 561185 := bstep (se 2 (by rfl) ⟨210444, by rfl⟩ : syracuseStep 561185 = 420889) B420889
theorem B6951005 : Blo 247818 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B954625 : Blo 247818 954625 := bstep (se 2 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 954625 = 715969) B715969
theorem B561527 : Blo 247818 561527 := bstep (se 1 (by rfl) ⟨421145, by rfl⟩ : syracuseStep 561527 = 842291) B842291
theorem B561707 : Blo 247818 561707 := bstep (se 1 (by rfl) ⟨421280, by rfl⟩ : syracuseStep 561707 = 842561) B842561
theorem B627335 : Blo 247818 627335 := bstep (se 1 (by rfl) ⟨470501, by rfl⟩ : syracuseStep 627335 = 941003) B941003
theorem B627385 : Blo 247818 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B562067 : Blo 247818 562067 := bstep (se 1 (by rfl) ⟨421550, by rfl⟩ : syracuseStep 562067 = 843101) B843101
theorem B14554037 : Blo 247818 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B562121 : Blo 247818 562121 := bstep (se 2 (by rfl) ⟨210795, by rfl⟩ : syracuseStep 562121 = 421591) B421591
theorem B857099 : Blo 247818 857099 := bstep (se 1 (by rfl) ⟨642824, by rfl⟩ : syracuseStep 857099 = 1285649) B1285649
theorem B398351 : Blo 247818 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B1283309 : Blo 247818 1283309 := bstep (se 3 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 1283309 = 481241) B481241
theorem B627983 : Blo 247818 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B1807915 : Blo 247818 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B562823 : Blo 247818 562823 := bstep (se 1 (by rfl) ⟨422117, by rfl⟩ : syracuseStep 562823 = 844235) B844235
theorem B563003 : Blo 247818 563003 := bstep (se 1 (by rfl) ⟨422252, by rfl⟩ : syracuseStep 563003 = 844505) B844505
theorem B1087291 : Blo 247818 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B2693017 : Blo 247818 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B563129 : Blo 247818 563129 := bstep (se 2 (by rfl) ⟨211173, by rfl⟩ : syracuseStep 563129 = 422347) B422347
theorem B628681 : Blo 247818 628681 := bstep (se 2 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 628681 = 471511) B471511
theorem B1415171 : Blo 247818 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B628823 : Blo 247818 628823 := bstep (se 1 (by rfl) ⟨471617, by rfl⟩ : syracuseStep 628823 = 943235) B943235
theorem B1513559 : Blo 247818 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B2398409 : Blo 247818 2398409 := bstep (se 2 (by rfl) ⟨899403, by rfl⟩ : syracuseStep 2398409 = 1798807) B1798807
theorem B563471 : Blo 247818 563471 := bstep (se 1 (by rfl) ⟨422603, by rfl⟩ : syracuseStep 563471 = 845207) B845207
theorem B563489 : Blo 247818 563489 := bstep (se 2 (by rfl) ⟨211308, by rfl⟩ : syracuseStep 563489 = 422617) B422617
theorem B1415627 : Blo 247818 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B301627 : Blo 247818 301627 := bstep (se 1 (by rfl) ⟨226220, by rfl⟩ : syracuseStep 301627 = 452441) B452441
theorem B399991 : Blo 247818 399991 := bstep (se 1 (by rfl) ⟨299993, by rfl⟩ : syracuseStep 399991 = 599987) B599987
theorem B563831 : Blo 247818 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B564011 : Blo 247818 564011 := bstep (se 1 (by rfl) ⟨423008, by rfl⟩ : syracuseStep 564011 = 846017) B846017
theorem B302011 : Blo 247818 302011 := bstep (se 1 (by rfl) ⟨226508, by rfl⟩ : syracuseStep 302011 = 453017) B453017
theorem B1416311 : Blo 247818 1416311 := bstep (se 1 (by rfl) ⟨1062233, by rfl⟩ : syracuseStep 1416311 = 2124467) B2124467
theorem B564371 : Blo 247818 564371 := bstep (se 1 (by rfl) ⟨423278, by rfl⟩ : syracuseStep 564371 = 846557) B846557
theorem B564425 : Blo 247818 564425 := bstep (se 2 (by rfl) ⟨211659, by rfl⟩ : syracuseStep 564425 = 423319) B423319
theorem B2825603 : Blo 247818 2825603 := bstep (se 1 (by rfl) ⟨2119202, by rfl⟩ : syracuseStep 2825603 = 4238405) B4238405
theorem B826891 : Blo 247818 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B4038173 : Blo 247818 4038173 := bstep (se 3 (by rfl) ⟨757157, by rfl⟩ : syracuseStep 4038173 = 1514315) B1514315
theorem B565127 : Blo 247818 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B565307 : Blo 247818 565307 := bstep (se 1 (by rfl) ⟨423980, by rfl⟩ : syracuseStep 565307 = 847961) B847961
theorem B630899 : Blo 247818 630899 := bstep (se 1 (by rfl) ⟨473174, by rfl⟩ : syracuseStep 630899 = 946349) B946349
theorem B5775533 : Blo 247818 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B565433 : Blo 247818 565433 := bstep (se 2 (by rfl) ⟨212037, by rfl⟩ : syracuseStep 565433 = 424075) B424075
theorem B10789361 : Blo 247818 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B565775 : Blo 247818 565775 := bstep (se 1 (by rfl) ⟨424331, by rfl⟩ : syracuseStep 565775 = 848663) B848663
theorem B1810973 : Blo 247818 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B565793 : Blo 247818 565793 := bstep (se 2 (by rfl) ⟨212172, by rfl⟩ : syracuseStep 565793 = 424345) B424345
theorem B631415 : Blo 247818 631415 := bstep (se 1 (by rfl) ⟨473561, by rfl⟩ : syracuseStep 631415 = 947123) B947123
theorem B2794201 : Blo 247818 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B598871 : Blo 247818 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B566135 : Blo 247818 566135 := bstep (se 1 (by rfl) ⟨424601, by rfl⟩ : syracuseStep 566135 = 849203) B849203
theorem B1418269 : Blo 247818 1418269 := bstep (se 3 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 1418269 = 531851) B531851
theorem B566315 : Blo 247818 566315 := bstep (se 1 (by rfl) ⟨424736, by rfl⟩ : syracuseStep 566315 = 849473) B849473
theorem B1254689 : Blo 247818 1254689 := bstep (se 2 (by rfl) ⟨470508, by rfl⟩ : syracuseStep 1254689 = 941017) B941017
theorem B1222033 : Blo 247818 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B599563 : Blo 247818 599563 := bstep (se 1 (by rfl) ⟨449672, by rfl⟩ : syracuseStep 599563 = 899345) B899345
theorem B796189 : Blo 247818 796189 := bstep (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) B298571
theorem B1418795 : Blo 247818 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B632407 : Blo 247818 632407 := bstep (se 1 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 632407 = 948611) B948611
theorem B1910465 : Blo 247818 1910465 := bstep (se 2 (by rfl) ⟨716424, by rfl⟩ : syracuseStep 1910465 = 1432849) B1432849
theorem B26388341 : Blo 247818 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B632711 : Blo 247818 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B2566039 : Blo 247818 2566039 := bstep (se 1 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 2566039 = 3849059) B3849059
theorem B894905 : Blo 247818 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B632843 : Blo 247818 632843 := bstep (se 1 (by rfl) ⟨474632, by rfl⟩ : syracuseStep 632843 = 949265) B949265
theorem B1058903 : Blo 247818 1058903 := bstep (se 1 (by rfl) ⟨794177, by rfl⟩ : syracuseStep 1058903 = 1588355) B1588355
theorem B1255661 : Blo 247818 1255661 := bstep (se 3 (by rfl) ⟨235436, by rfl⟩ : syracuseStep 1255661 = 470873) B470873
theorem B1517939 : Blo 247818 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B895367 : Blo 247818 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B534919 : Blo 247818 534919 := bstep (se 1 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 534919 = 802379) B802379
theorem B338347 : Blo 247818 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B633359 : Blo 247818 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B633491 : Blo 247818 633491 := bstep (se 1 (by rfl) ⟨475118, by rfl⟩ : syracuseStep 633491 = 950237) B950237
theorem B600833 : Blo 247818 600833 := bstep (se 2 (by rfl) ⟨225312, by rfl⟩ : syracuseStep 600833 = 450625) B450625
theorem B1616755 : Blo 247818 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B600947 : Blo 247818 600947 := bstep (se 1 (by rfl) ⟨450710, by rfl⟩ : syracuseStep 600947 = 901421) B901421
theorem B1354643 : Blo 247818 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B1420253 : Blo 247818 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B306191 : Blo 247818 306191 := bstep (se 1 (by rfl) ⟨229643, by rfl⟩ : syracuseStep 306191 = 459287) B459287
theorem B1256471 : Blo 247818 1256471 := bstep (se 1 (by rfl) ⟨942353, by rfl⟩ : syracuseStep 1256471 = 1884707) B1884707
theorem B601121 : Blo 247818 601121 := bstep (se 2 (by rfl) ⟨225420, by rfl⟩ : syracuseStep 601121 = 450841) B450841
theorem B371771 : Blo 247818 371771 := bstep (se 1 (by rfl) ⟨278828, by rfl⟩ : syracuseStep 371771 = 557657) B557657
theorem B371831 : Blo 247818 371831 := bstep (se 1 (by rfl) ⟨278873, by rfl⟩ : syracuseStep 371831 = 557747) B557747
theorem B371855 : Blo 247818 371855 := bstep (se 1 (by rfl) ⟨278891, by rfl⟩ : syracuseStep 371855 = 557783) B557783
theorem B371897 : Blo 247818 371897 := bstep (se 2 (by rfl) ⟨139461, by rfl⟩ : syracuseStep 371897 = 278923) B278923
theorem B371975 : Blo 247818 371975 := bstep (se 1 (by rfl) ⟨278981, by rfl⟩ : syracuseStep 371975 = 557963) B557963
theorem B372011 : Blo 247818 372011 := bstep (se 1 (by rfl) ⟨279008, by rfl⟩ : syracuseStep 372011 = 558017) B558017
theorem B372041 : Blo 247818 372041 := bstep (se 2 (by rfl) ⟨139515, by rfl⟩ : syracuseStep 372041 = 279031) B279031
theorem B798137 : Blo 247818 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B339385 : Blo 247818 339385 := bstep (se 2 (by rfl) ⟨127269, by rfl⟩ : syracuseStep 339385 = 254539) B254539
theorem B372155 : Blo 247818 372155 := bstep (se 1 (by rfl) ⟨279116, by rfl⟩ : syracuseStep 372155 = 558233) B558233
theorem B372215 : Blo 247818 372215 := bstep (se 1 (by rfl) ⟨279161, by rfl⟩ : syracuseStep 372215 = 558323) B558323
theorem B372239 : Blo 247818 372239 := bstep (se 1 (by rfl) ⟨279179, by rfl⟩ : syracuseStep 372239 = 558359) B558359
theorem B372281 : Blo 247818 372281 := bstep (se 2 (by rfl) ⟨139605, by rfl⟩ : syracuseStep 372281 = 279211) B279211
theorem B372359 : Blo 247818 372359 := bstep (se 1 (by rfl) ⟨279269, by rfl⟩ : syracuseStep 372359 = 558539) B558539
theorem B765587 : Blo 247818 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B372395 : Blo 247818 372395 := bstep (se 1 (by rfl) ⟨279296, by rfl⟩ : syracuseStep 372395 = 558593) B558593
theorem B372425 : Blo 247818 372425 := bstep (se 2 (by rfl) ⟨139659, by rfl⟩ : syracuseStep 372425 = 279319) B279319
theorem B634625 : Blo 247818 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B1027873 : Blo 247818 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B470843 : Blo 247818 470843 := bstep (se 1 (by rfl) ⟨353132, by rfl⟩ : syracuseStep 470843 = 706265) B706265
theorem B372539 : Blo 247818 372539 := bstep (se 1 (by rfl) ⟨279404, by rfl⟩ : syracuseStep 372539 = 558809) B558809
theorem B372599 : Blo 247818 372599 := bstep (se 1 (by rfl) ⟨279449, by rfl⟩ : syracuseStep 372599 = 558899) B558899
theorem B372623 : Blo 247818 372623 := bstep (se 1 (by rfl) ⟨279467, by rfl⟩ : syracuseStep 372623 = 558935) B558935
theorem B372665 : Blo 247818 372665 := bstep (se 2 (by rfl) ⟨139749, by rfl⟩ : syracuseStep 372665 = 279499) B279499
theorem B372743 : Blo 247818 372743 := bstep (se 1 (by rfl) ⟨279557, by rfl⟩ : syracuseStep 372743 = 559115) B559115
theorem B372779 : Blo 247818 372779 := bstep (se 1 (by rfl) ⟨279584, by rfl⟩ : syracuseStep 372779 = 559169) B559169
theorem B536635 : Blo 247818 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B372809 : Blo 247818 372809 := bstep (se 2 (by rfl) ⟨139803, by rfl⟩ : syracuseStep 372809 = 279607) B279607
theorem B733303 : Blo 247818 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B634999 : Blo 247818 634999 := bstep (se 1 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 634999 = 952499) B952499
theorem B503993 : Blo 247818 503993 := bstep (se 2 (by rfl) ⟨188997, by rfl⟩ : syracuseStep 503993 = 377995) B377995
theorem B372923 : Blo 247818 372923 := bstep (se 1 (by rfl) ⟨279692, by rfl⟩ : syracuseStep 372923 = 559385) B559385
theorem B372983 : Blo 247818 372983 := bstep (se 1 (by rfl) ⟨279737, by rfl⟩ : syracuseStep 372983 = 559475) B559475
theorem B373007 : Blo 247818 373007 := bstep (se 1 (by rfl) ⟨279755, by rfl⟩ : syracuseStep 373007 = 559511) B559511
theorem B471329 : Blo 247818 471329 := bstep (se 2 (by rfl) ⟨176748, by rfl⟩ : syracuseStep 471329 = 353497) B353497
theorem B373049 : Blo 247818 373049 := bstep (se 2 (by rfl) ⟨139893, by rfl⟩ : syracuseStep 373049 = 279787) B279787
theorem B2044295 : Blo 247818 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B373127 : Blo 247818 373127 := bstep (se 1 (by rfl) ⟨279845, by rfl⟩ : syracuseStep 373127 = 559691) B559691
theorem B373163 : Blo 247818 373163 := bstep (se 1 (by rfl) ⟨279872, by rfl⟩ : syracuseStep 373163 = 559745) B559745
theorem B373193 : Blo 247818 373193 := bstep (se 2 (by rfl) ⟨139947, by rfl⟩ : syracuseStep 373193 = 279895) B279895
theorem B2699729 : Blo 247818 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B471595 : Blo 247818 471595 := bstep (se 1 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 471595 = 707393) B707393
theorem B635435 : Blo 247818 635435 := bstep (se 1 (by rfl) ⟨476576, by rfl⟩ : syracuseStep 635435 = 953153) B953153
theorem B537131 : Blo 247818 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B373307 : Blo 247818 373307 := bstep (se 1 (by rfl) ⟨279980, by rfl⟩ : syracuseStep 373307 = 559961) B559961
theorem B373367 : Blo 247818 373367 := bstep (se 1 (by rfl) ⟨280025, by rfl⟩ : syracuseStep 373367 = 560051) B560051
theorem B373391 : Blo 247818 373391 := bstep (se 1 (by rfl) ⟨280043, by rfl⟩ : syracuseStep 373391 = 560087) B560087
theorem B373433 : Blo 247818 373433 := bstep (se 2 (by rfl) ⟨140037, by rfl⟩ : syracuseStep 373433 = 280075) B280075
theorem B373511 : Blo 247818 373511 := bstep (se 1 (by rfl) ⟨280133, by rfl⟩ : syracuseStep 373511 = 560267) B560267
theorem B4567823 : Blo 247818 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B373547 : Blo 247818 373547 := bstep (se 1 (by rfl) ⟨280160, by rfl⟩ : syracuseStep 373547 = 560321) B560321
theorem B373577 : Blo 247818 373577 := bstep (se 2 (by rfl) ⟨140091, by rfl⟩ : syracuseStep 373577 = 280183) B280183
theorem B373691 : Blo 247818 373691 := bstep (se 1 (by rfl) ⟨280268, by rfl⟩ : syracuseStep 373691 = 560537) B560537
theorem B373751 : Blo 247818 373751 := bstep (se 1 (by rfl) ⟨280313, by rfl⟩ : syracuseStep 373751 = 560627) B560627
theorem B373775 : Blo 247818 373775 := bstep (se 1 (by rfl) ⟨280331, by rfl⟩ : syracuseStep 373775 = 560663) B560663
theorem B373817 : Blo 247818 373817 := bstep (se 2 (by rfl) ⟨140181, by rfl⟩ : syracuseStep 373817 = 280363) B280363
theorem B504967 : Blo 247818 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B373895 : Blo 247818 373895 := bstep (se 1 (by rfl) ⟨280421, by rfl⟩ : syracuseStep 373895 = 560843) B560843
theorem B373931 : Blo 247818 373931 := bstep (se 1 (by rfl) ⟨280448, by rfl⟩ : syracuseStep 373931 = 560897) B560897
theorem B373961 : Blo 247818 373961 := bstep (se 2 (by rfl) ⟨140235, by rfl⟩ : syracuseStep 373961 = 280471) B280471
theorem B603407 : Blo 247818 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B1422643 : Blo 247818 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B374075 : Blo 247818 374075 := bstep (se 1 (by rfl) ⟨280556, by rfl⟩ : syracuseStep 374075 = 561113) B561113
theorem B636275 : Blo 247818 636275 := bstep (se 1 (by rfl) ⟨477206, by rfl⟩ : syracuseStep 636275 = 954413) B954413
theorem B374135 : Blo 247818 374135 := bstep (se 1 (by rfl) ⟨280601, by rfl⟩ : syracuseStep 374135 = 561203) B561203
theorem B800135 : Blo 247818 800135 := bstep (se 1 (by rfl) ⟨600101, by rfl⟩ : syracuseStep 800135 = 1200203) B1200203
theorem B636295 : Blo 247818 636295 := bstep (se 1 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 636295 = 954443) B954443
theorem B374159 : Blo 247818 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B374201 : Blo 247818 374201 := bstep (se 2 (by rfl) ⟨140325, by rfl⟩ : syracuseStep 374201 = 280651) B280651
theorem B3225091 : Blo 247818 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B374279 : Blo 247818 374279 := bstep (se 1 (by rfl) ⟨280709, by rfl⟩ : syracuseStep 374279 = 561419) B561419
theorem B374315 : Blo 247818 374315 := bstep (se 1 (by rfl) ⟨280736, by rfl⟩ : syracuseStep 374315 = 561473) B561473
theorem B374345 : Blo 247818 374345 := bstep (se 2 (by rfl) ⟨140379, by rfl⟩ : syracuseStep 374345 = 280759) B280759
theorem B472711 : Blo 247818 472711 := bstep (se 1 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 472711 = 709067) B709067
theorem B636569 : Blo 247818 636569 := bstep (se 2 (by rfl) ⟨238713, by rfl⟩ : syracuseStep 636569 = 477427) B477427
theorem B374459 : Blo 247818 374459 := bstep (se 1 (by rfl) ⟨280844, by rfl⟩ : syracuseStep 374459 = 561689) B561689
theorem B374519 : Blo 247818 374519 := bstep (se 1 (by rfl) ⟨280889, by rfl⟩ : syracuseStep 374519 = 561779) B561779
theorem B374543 : Blo 247818 374543 := bstep (se 1 (by rfl) ⟨280907, by rfl⟩ : syracuseStep 374543 = 561815) B561815
theorem B800545 : Blo 247818 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B374585 : Blo 247818 374585 := bstep (se 2 (by rfl) ⟨140469, by rfl⟩ : syracuseStep 374585 = 280939) B280939
theorem B636731 : Blo 247818 636731 := bstep (se 1 (by rfl) ⟨477548, by rfl⟩ : syracuseStep 636731 = 955097) B955097
theorem B4798277 : Blo 247818 4798277 := bstep (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) B899677
theorem B374663 : Blo 247818 374663 := bstep (se 1 (by rfl) ⟨280997, by rfl⟩ : syracuseStep 374663 = 561995) B561995
theorem B374699 : Blo 247818 374699 := bstep (se 1 (by rfl) ⟨281024, by rfl⟩ : syracuseStep 374699 = 562049) B562049
theorem B374729 : Blo 247818 374729 := bstep (se 2 (by rfl) ⟨140523, by rfl⟩ : syracuseStep 374729 = 281047) B281047
theorem B636943 : Blo 247818 636943 := bstep (se 1 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 636943 = 955415) B955415
theorem B1259549 : Blo 247818 1259549 := bstep (se 3 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 1259549 = 472331) B472331
theorem B374843 : Blo 247818 374843 := bstep (se 1 (by rfl) ⟨281132, by rfl⟩ : syracuseStep 374843 = 562265) B562265
theorem B374903 : Blo 247818 374903 := bstep (se 1 (by rfl) ⟨281177, by rfl⟩ : syracuseStep 374903 = 562355) B562355
theorem B374927 : Blo 247818 374927 := bstep (se 1 (by rfl) ⟨281195, by rfl⟩ : syracuseStep 374927 = 562391) B562391
theorem B473273 : Blo 247818 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B374969 : Blo 247818 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B375047 : Blo 247818 375047 := bstep (se 1 (by rfl) ⟨281285, by rfl⟩ : syracuseStep 375047 = 562571) B562571
theorem B637217 : Blo 247818 637217 := bstep (se 2 (by rfl) ⟨238956, by rfl⟩ : syracuseStep 637217 = 477913) B477913
theorem B375083 : Blo 247818 375083 := bstep (se 1 (by rfl) ⟨281312, by rfl⟩ : syracuseStep 375083 = 562625) B562625
theorem B375113 : Blo 247818 375113 := bstep (se 2 (by rfl) ⟨140667, by rfl⟩ : syracuseStep 375113 = 281335) B281335
theorem B375227 : Blo 247818 375227 := bstep (se 1 (by rfl) ⟨281420, by rfl⟩ : syracuseStep 375227 = 562841) B562841
theorem B375287 : Blo 247818 375287 := bstep (se 1 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 375287 = 562931) B562931
theorem B1260035 : Blo 247818 1260035 := bstep (se 1 (by rfl) ⟨945026, by rfl⟩ : syracuseStep 1260035 = 1890053) B1890053
theorem B375311 : Blo 247818 375311 := bstep (se 1 (by rfl) ⟨281483, by rfl⟩ : syracuseStep 375311 = 562967) B562967
theorem B375353 : Blo 247818 375353 := bstep (se 2 (by rfl) ⟨140757, by rfl⟩ : syracuseStep 375353 = 281515) B281515
theorem B375431 : Blo 247818 375431 := bstep (se 1 (by rfl) ⟨281573, by rfl⟩ : syracuseStep 375431 = 563147) B563147
theorem B375467 : Blo 247818 375467 := bstep (se 1 (by rfl) ⟨281600, by rfl⟩ : syracuseStep 375467 = 563201) B563201
theorem B375497 : Blo 247818 375497 := bstep (se 2 (by rfl) ⟨140811, by rfl⟩ : syracuseStep 375497 = 281623) B281623
theorem B1424101 : Blo 247818 1424101 := bstep (se 4 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 1424101 = 267019) B267019
theorem B375611 : Blo 247818 375611 := bstep (se 1 (by rfl) ⟨281708, by rfl⟩ : syracuseStep 375611 = 563417) B563417
theorem B375671 : Blo 247818 375671 := bstep (se 1 (by rfl) ⟨281753, by rfl⟩ : syracuseStep 375671 = 563507) B563507
theorem B375695 : Blo 247818 375695 := bstep (se 1 (by rfl) ⟨281771, by rfl⟩ : syracuseStep 375695 = 563543) B563543
theorem B375737 : Blo 247818 375737 := bstep (se 2 (by rfl) ⟨140901, by rfl⟩ : syracuseStep 375737 = 281803) B281803
theorem B1358795 : Blo 247818 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B375815 : Blo 247818 375815 := bstep (se 1 (by rfl) ⟨281861, by rfl⟩ : syracuseStep 375815 = 563723) B563723
theorem B375851 : Blo 247818 375851 := bstep (se 1 (by rfl) ⟨281888, by rfl⟩ : syracuseStep 375851 = 563777) B563777
theorem B375881 : Blo 247818 375881 := bstep (se 2 (by rfl) ⟨140955, by rfl⟩ : syracuseStep 375881 = 281911) B281911
theorem B539767 : Blo 247818 539767 := bstep (se 1 (by rfl) ⟨404825, by rfl⟩ : syracuseStep 539767 = 809651) B809651
theorem B375995 : Blo 247818 375995 := bstep (se 1 (by rfl) ⟨281996, by rfl⟩ : syracuseStep 375995 = 563993) B563993
theorem B376055 : Blo 247818 376055 := bstep (se 1 (by rfl) ⟨282041, by rfl⟩ : syracuseStep 376055 = 564083) B564083
theorem B376079 : Blo 247818 376079 := bstep (se 1 (by rfl) ⟨282059, by rfl⟩ : syracuseStep 376079 = 564119) B564119
theorem B507179 : Blo 247818 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B376121 : Blo 247818 376121 := bstep (se 2 (by rfl) ⟨141045, by rfl⟩ : syracuseStep 376121 = 282091) B282091
theorem B474427 : Blo 247818 474427 := bstep (se 1 (by rfl) ⟨355820, by rfl⟩ : syracuseStep 474427 = 711641) B711641
theorem B376199 : Blo 247818 376199 := bstep (se 1 (by rfl) ⟨282149, by rfl⟩ : syracuseStep 376199 = 564299) B564299
theorem B376235 : Blo 247818 376235 := bstep (se 1 (by rfl) ⟨282176, by rfl⟩ : syracuseStep 376235 = 564353) B564353
theorem B376265 : Blo 247818 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B376379 : Blo 247818 376379 := bstep (se 1 (by rfl) ⟨282284, by rfl⟩ : syracuseStep 376379 = 564569) B564569
theorem B376439 : Blo 247818 376439 := bstep (se 1 (by rfl) ⟨282329, by rfl⟩ : syracuseStep 376439 = 564659) B564659
theorem B376463 : Blo 247818 376463 := bstep (se 1 (by rfl) ⟨282347, by rfl⟩ : syracuseStep 376463 = 564695) B564695
theorem B376505 : Blo 247818 376505 := bstep (se 2 (by rfl) ⟨141189, by rfl⟩ : syracuseStep 376505 = 282379) B282379
theorem B376583 : Blo 247818 376583 := bstep (se 1 (by rfl) ⟨282437, by rfl⟩ : syracuseStep 376583 = 564875) B564875
theorem B474913 : Blo 247818 474913 := bstep (se 2 (by rfl) ⟨178092, by rfl⟩ : syracuseStep 474913 = 356185) B356185
theorem B376619 : Blo 247818 376619 := bstep (se 1 (by rfl) ⟨282464, by rfl⟩ : syracuseStep 376619 = 564929) B564929
theorem B638779 : Blo 247818 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B376649 : Blo 247818 376649 := bstep (se 2 (by rfl) ⟨141243, by rfl⟩ : syracuseStep 376649 = 282487) B282487
theorem B376763 : Blo 247818 376763 := bstep (se 1 (by rfl) ⟨282572, by rfl⟩ : syracuseStep 376763 = 565145) B565145
theorem B376823 : Blo 247818 376823 := bstep (se 1 (by rfl) ⟨282617, by rfl⟩ : syracuseStep 376823 = 565235) B565235
theorem B376847 : Blo 247818 376847 := bstep (se 1 (by rfl) ⟨282635, by rfl⟩ : syracuseStep 376847 = 565271) B565271
theorem B376889 : Blo 247818 376889 := bstep (se 2 (by rfl) ⟨141333, by rfl⟩ : syracuseStep 376889 = 282667) B282667
theorem B1884221 : Blo 247818 1884221 := bstep (se 3 (by rfl) ⟨353291, by rfl⟩ : syracuseStep 1884221 = 706583) B706583
theorem B22986827 : Blo 247818 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1261655 : Blo 247818 1261655 := bstep (se 1 (by rfl) ⟨946241, by rfl⟩ : syracuseStep 1261655 = 1892483) B1892483
theorem B376967 : Blo 247818 376967 := bstep (se 1 (by rfl) ⟨282725, by rfl⟩ : syracuseStep 376967 = 565451) B565451
theorem B377003 : Blo 247818 377003 := bstep (se 1 (by rfl) ⟨282752, by rfl⟩ : syracuseStep 377003 = 565505) B565505
theorem B377033 : Blo 247818 377033 := bstep (se 2 (by rfl) ⟨141387, by rfl⟩ : syracuseStep 377033 = 282775) B282775
theorem B1065275 : Blo 247818 1065275 := bstep (se 1 (by rfl) ⟨798956, by rfl⟩ : syracuseStep 1065275 = 1597913) B1597913
theorem B377147 : Blo 247818 377147 := bstep (se 1 (by rfl) ⟨282860, by rfl⟩ : syracuseStep 377147 = 565721) B565721
theorem B377207 : Blo 247818 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B606599 : Blo 247818 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B377231 : Blo 247818 377231 := bstep (se 1 (by rfl) ⟨282923, by rfl⟩ : syracuseStep 377231 = 565847) B565847
theorem B901523 : Blo 247818 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B377273 : Blo 247818 377273 := bstep (se 2 (by rfl) ⟨141477, by rfl⟩ : syracuseStep 377273 = 282955) B282955
theorem B377351 : Blo 247818 377351 := bstep (se 1 (by rfl) ⟨283013, by rfl⟩ : syracuseStep 377351 = 566027) B566027
theorem B377387 : Blo 247818 377387 := bstep (se 1 (by rfl) ⟨283040, by rfl⟩ : syracuseStep 377387 = 566081) B566081
theorem B1262141 : Blo 247818 1262141 := bstep (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) B473303
theorem B377417 : Blo 247818 377417 := bstep (se 2 (by rfl) ⟨141531, by rfl⟩ : syracuseStep 377417 = 283063) B283063
theorem B672371 : Blo 247818 672371 := bstep (se 1 (by rfl) ⟨504278, by rfl⟩ : syracuseStep 672371 = 1008557) B1008557
theorem B279175 : Blo 247818 279175 := bstep (se 1 (by rfl) ⟨209381, by rfl⟩ : syracuseStep 279175 = 418763) B418763
theorem B377531 : Blo 247818 377531 := bstep (se 1 (by rfl) ⟨283148, by rfl⟩ : syracuseStep 377531 = 566297) B566297
theorem B377591 : Blo 247818 377591 := bstep (se 1 (by rfl) ⟨283193, by rfl⟩ : syracuseStep 377591 = 566387) B566387
theorem B2147087 : Blo 247818 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B377615 : Blo 247818 377615 := bstep (se 1 (by rfl) ⟨283211, by rfl⟩ : syracuseStep 377615 = 566423) B566423
theorem B377657 : Blo 247818 377657 := bstep (se 2 (by rfl) ⟨141621, by rfl⟩ : syracuseStep 377657 = 283243) B283243
theorem B279355 : Blo 247818 279355 := bstep (se 1 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 279355 = 419033) B419033
theorem B377801 : Blo 247818 377801 := bstep (se 2 (by rfl) ⟨141675, by rfl⟩ : syracuseStep 377801 = 283351) B283351
theorem B476219 : Blo 247818 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B2409709 : Blo 247818 2409709 := bstep (se 3 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 2409709 = 903641) B903641
theorem B279823 : Blo 247818 279823 := bstep (se 1 (by rfl) ⟨209867, by rfl⟩ : syracuseStep 279823 = 419735) B419735
theorem B2934049 : Blo 247818 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B836999 : Blo 247818 836999 := bstep (se 1 (by rfl) ⟨627749, by rfl⟩ : syracuseStep 836999 = 1255499) B1255499
theorem B1426835 : Blo 247818 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B476705 : Blo 247818 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B476857 : Blo 247818 476857 := bstep (se 2 (by rfl) ⟨178821, by rfl⟩ : syracuseStep 476857 = 357643) B357643
theorem B837377 : Blo 247818 837377 := bstep (se 2 (by rfl) ⟨314016, by rfl⟩ : syracuseStep 837377 = 628033) B628033
theorem B280327 : Blo 247818 280327 := bstep (se 1 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 280327 = 420491) B420491
theorem B706333 : Blo 247818 706333 := bstep (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) B264875
theorem B673579 : Blo 247818 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B706391 : Blo 247818 706391 := bstep (se 1 (by rfl) ⟨529793, by rfl⟩ : syracuseStep 706391 = 1059587) B1059587
theorem B280507 : Blo 247818 280507 := bstep (se 1 (by rfl) ⟨210380, by rfl⟩ : syracuseStep 280507 = 420761) B420761
theorem B247823 : Blo 247818 247823 := bstep (se 1 (by rfl) ⟨185867, by rfl⟩ : syracuseStep 247823 = 371735) B371735
theorem B247867 : Blo 247818 247867 := bstep (se 1 (by rfl) ⟨185900, by rfl⟩ : syracuseStep 247867 = 371801) B371801
theorem B1427543 : Blo 247818 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B247943 : Blo 247818 247943 := bstep (se 1 (by rfl) ⟨185957, by rfl⟩ : syracuseStep 247943 = 371915) B371915
theorem B247951 : Blo 247818 247951 := bstep (se 1 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 247951 = 371927) B371927
theorem B247995 : Blo 247818 247995 := bstep (se 1 (by rfl) ⟨185996, by rfl⟩ : syracuseStep 247995 = 371993) B371993
theorem B248071 : Blo 247818 248071 := bstep (se 1 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 248071 = 372107) B372107
theorem B248079 : Blo 247818 248079 := bstep (se 1 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 248079 = 372119) B372119
theorem B674077 : Blo 247818 674077 := bstep (se 3 (by rfl) ⟨126389, by rfl⟩ : syracuseStep 674077 = 252779) B252779
theorem B1263923 : Blo 247818 1263923 := bstep (se 1 (by rfl) ⟨947942, by rfl⟩ : syracuseStep 1263923 = 1895885) B1895885
theorem B248123 : Blo 247818 248123 := bstep (se 1 (by rfl) ⟨186092, by rfl⟩ : syracuseStep 248123 = 372185) B372185
theorem B248199 : Blo 247818 248199 := bstep (se 1 (by rfl) ⟨186149, by rfl⟩ : syracuseStep 248199 = 372299) B372299
theorem B248207 : Blo 247818 248207 := bstep (se 1 (by rfl) ⟨186155, by rfl⟩ : syracuseStep 248207 = 372311) B372311
theorem B280975 : Blo 247818 280975 := bstep (se 1 (by rfl) ⟨210731, by rfl⟩ : syracuseStep 280975 = 421463) B421463
theorem B248251 : Blo 247818 248251 := bstep (se 1 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 248251 = 372377) B372377
theorem B248327 : Blo 247818 248327 := bstep (se 1 (by rfl) ⟨186245, by rfl⟩ : syracuseStep 248327 = 372491) B372491
theorem B248335 : Blo 247818 248335 := bstep (se 1 (by rfl) ⟨186251, by rfl⟩ : syracuseStep 248335 = 372503) B372503
theorem B838187 : Blo 247818 838187 := bstep (se 1 (by rfl) ⟨628640, by rfl⟩ : syracuseStep 838187 = 1257281) B1257281
theorem B248379 : Blo 247818 248379 := bstep (se 1 (by rfl) ⟨186284, by rfl⟩ : syracuseStep 248379 = 372569) B372569
theorem B674423 : Blo 247818 674423 := bstep (se 1 (by rfl) ⟨505817, by rfl⟩ : syracuseStep 674423 = 1011635) B1011635
theorem B1264247 : Blo 247818 1264247 := bstep (se 1 (by rfl) ⟨948185, by rfl⟩ : syracuseStep 1264247 = 1896371) B1896371
theorem B248455 : Blo 247818 248455 := bstep (se 1 (by rfl) ⟨186341, by rfl⟩ : syracuseStep 248455 = 372683) B372683
theorem B248463 : Blo 247818 248463 := bstep (se 1 (by rfl) ⟨186347, by rfl⟩ : syracuseStep 248463 = 372695) B372695
theorem B248507 : Blo 247818 248507 := bstep (se 1 (by rfl) ⟨186380, by rfl⟩ : syracuseStep 248507 = 372761) B372761
theorem B248583 : Blo 247818 248583 := bstep (se 1 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 248583 = 372875) B372875
theorem B248591 : Blo 247818 248591 := bstep (se 1 (by rfl) ⟨186443, by rfl⟩ : syracuseStep 248591 = 372887) B372887
theorem B248635 : Blo 247818 248635 := bstep (se 1 (by rfl) ⟨186476, by rfl⟩ : syracuseStep 248635 = 372953) B372953
theorem B248711 : Blo 247818 248711 := bstep (se 1 (by rfl) ⟨186533, by rfl⟩ : syracuseStep 248711 = 373067) B373067
theorem B281479 : Blo 247818 281479 := bstep (se 1 (by rfl) ⟨211109, by rfl⟩ : syracuseStep 281479 = 422219) B422219
theorem B248719 : Blo 247818 248719 := bstep (se 1 (by rfl) ⟨186539, by rfl⟩ : syracuseStep 248719 = 373079) B373079
theorem B1133459 : Blo 247818 1133459 := bstep (se 1 (by rfl) ⟨850094, by rfl⟩ : syracuseStep 1133459 = 1700189) B1700189
theorem B248763 : Blo 247818 248763 := bstep (se 1 (by rfl) ⟨186572, by rfl⟩ : syracuseStep 248763 = 373145) B373145
theorem B248839 : Blo 247818 248839 := bstep (se 1 (by rfl) ⟨186629, by rfl⟩ : syracuseStep 248839 = 373259) B373259
theorem B248847 : Blo 247818 248847 := bstep (se 1 (by rfl) ⟨186635, by rfl⟩ : syracuseStep 248847 = 373271) B373271
theorem B248891 : Blo 247818 248891 := bstep (se 1 (by rfl) ⟨186668, by rfl⟩ : syracuseStep 248891 = 373337) B373337
theorem B281659 : Blo 247818 281659 := bstep (se 1 (by rfl) ⟨211244, by rfl⟩ : syracuseStep 281659 = 422489) B422489
theorem B248967 : Blo 247818 248967 := bstep (se 1 (by rfl) ⟨186725, by rfl⟩ : syracuseStep 248967 = 373451) B373451
theorem B248975 : Blo 247818 248975 := bstep (se 1 (by rfl) ⟨186731, by rfl⟩ : syracuseStep 248975 = 373463) B373463
theorem B249019 : Blo 247818 249019 := bstep (se 1 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 249019 = 373529) B373529
theorem B249095 : Blo 247818 249095 := bstep (se 1 (by rfl) ⟨186821, by rfl⟩ : syracuseStep 249095 = 373643) B373643
theorem B249103 : Blo 247818 249103 := bstep (se 1 (by rfl) ⟨186827, by rfl⟩ : syracuseStep 249103 = 373655) B373655
theorem B249147 : Blo 247818 249147 := bstep (se 1 (by rfl) ⟨186860, by rfl⟩ : syracuseStep 249147 = 373721) B373721
theorem B1887623 : Blo 247818 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B249223 : Blo 247818 249223 := bstep (se 1 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 249223 = 373835) B373835
theorem B249231 : Blo 247818 249231 := bstep (se 1 (by rfl) ⟨186923, by rfl⟩ : syracuseStep 249231 = 373847) B373847
theorem B5787065 : Blo 247818 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B249275 : Blo 247818 249275 := bstep (se 1 (by rfl) ⟨186956, by rfl⟩ : syracuseStep 249275 = 373913) B373913
theorem B708041 : Blo 247818 708041 := bstep (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) B531031
theorem B249351 : Blo 247818 249351 := bstep (se 1 (by rfl) ⟨187013, by rfl⟩ : syracuseStep 249351 = 374027) B374027
theorem B282127 : Blo 247818 282127 := bstep (se 1 (by rfl) ⟨211595, by rfl⟩ : syracuseStep 282127 = 423191) B423191
theorem B249359 : Blo 247818 249359 := bstep (se 1 (by rfl) ⟨187019, by rfl⟩ : syracuseStep 249359 = 374039) B374039
theorem B314923 : Blo 247818 314923 := bstep (se 1 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 314923 = 472385) B472385
theorem B249403 : Blo 247818 249403 := bstep (se 1 (by rfl) ⟨187052, by rfl⟩ : syracuseStep 249403 = 374105) B374105
theorem B904765 : Blo 247818 904765 := bstep (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) B339287
theorem B1265219 : Blo 247818 1265219 := bstep (se 1 (by rfl) ⟨948914, by rfl⟩ : syracuseStep 1265219 = 1897829) B1897829
theorem B249479 : Blo 247818 249479 := bstep (se 1 (by rfl) ⟨187109, by rfl⟩ : syracuseStep 249479 = 374219) B374219
theorem B249487 : Blo 247818 249487 := bstep (se 1 (by rfl) ⟨187115, by rfl⟩ : syracuseStep 249487 = 374231) B374231
theorem B249531 : Blo 247818 249531 := bstep (se 1 (by rfl) ⟨187148, by rfl⟩ : syracuseStep 249531 = 374297) B374297
theorem B46157525 : Blo 247818 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B249607 : Blo 247818 249607 := bstep (se 1 (by rfl) ⟨187205, by rfl⟩ : syracuseStep 249607 = 374411) B374411
theorem B249615 : Blo 247818 249615 := bstep (se 1 (by rfl) ⟨187211, by rfl⟩ : syracuseStep 249615 = 374423) B374423
theorem B839483 : Blo 247818 839483 := bstep (se 1 (by rfl) ⟨629612, by rfl⟩ : syracuseStep 839483 = 1259225) B1259225
theorem B249659 : Blo 247818 249659 := bstep (se 1 (by rfl) ⟨187244, by rfl⟩ : syracuseStep 249659 = 374489) B374489
theorem B249735 : Blo 247818 249735 := bstep (se 1 (by rfl) ⟨187301, by rfl⟩ : syracuseStep 249735 = 374603) B374603
theorem B1265543 : Blo 247818 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B249743 : Blo 247818 249743 := bstep (se 1 (by rfl) ⟨187307, by rfl⟩ : syracuseStep 249743 = 374615) B374615
theorem B1429433 : Blo 247818 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B249787 : Blo 247818 249787 := bstep (se 1 (by rfl) ⟨187340, by rfl⟩ : syracuseStep 249787 = 374681) B374681
theorem B249863 : Blo 247818 249863 := bstep (se 1 (by rfl) ⟨187397, by rfl⟩ : syracuseStep 249863 = 374795) B374795
theorem B282631 : Blo 247818 282631 := bstep (se 1 (by rfl) ⟨211973, by rfl⟩ : syracuseStep 282631 = 423947) B423947
theorem B249871 : Blo 247818 249871 := bstep (se 1 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 249871 = 374807) B374807
theorem B249915 : Blo 247818 249915 := bstep (se 1 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 249915 = 374873) B374873
theorem B249991 : Blo 247818 249991 := bstep (se 1 (by rfl) ⟨187493, by rfl⟩ : syracuseStep 249991 = 374987) B374987
theorem B249999 : Blo 247818 249999 := bstep (se 1 (by rfl) ⟨187499, by rfl⟩ : syracuseStep 249999 = 374999) B374999
theorem B250043 : Blo 247818 250043 := bstep (se 1 (by rfl) ⟨187532, by rfl⟩ : syracuseStep 250043 = 375065) B375065
theorem B381115 : Blo 247818 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B282811 : Blo 247818 282811 := bstep (se 1 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 282811 = 424217) B424217
theorem B250119 : Blo 247818 250119 := bstep (se 1 (by rfl) ⟨187589, by rfl⟩ : syracuseStep 250119 = 375179) B375179
theorem B250127 : Blo 247818 250127 := bstep (se 1 (by rfl) ⟨187595, by rfl⟩ : syracuseStep 250127 = 375191) B375191
theorem B839969 : Blo 247818 839969 := bstep (se 2 (by rfl) ⟨314988, by rfl⟩ : syracuseStep 839969 = 629977) B629977
theorem B708907 : Blo 247818 708907 := bstep (se 1 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 708907 = 1063361) B1063361
theorem B250171 : Blo 247818 250171 := bstep (se 1 (by rfl) ⟨187628, by rfl⟩ : syracuseStep 250171 = 375257) B375257
theorem B250247 : Blo 247818 250247 := bstep (se 1 (by rfl) ⟨187685, by rfl⟩ : syracuseStep 250247 = 375371) B375371
theorem B250255 : Blo 247818 250255 := bstep (se 1 (by rfl) ⟨187691, by rfl⟩ : syracuseStep 250255 = 375383) B375383
theorem B250299 : Blo 247818 250299 := bstep (se 1 (by rfl) ⟨187724, by rfl⟩ : syracuseStep 250299 = 375449) B375449
theorem B2118109 : Blo 247818 2118109 := bstep (se 3 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 2118109 = 794291) B794291
theorem B315895 : Blo 247818 315895 := bstep (se 1 (by rfl) ⟨236921, by rfl⟩ : syracuseStep 315895 = 473843) B473843
theorem B250375 : Blo 247818 250375 := bstep (se 1 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 250375 = 375563) B375563
theorem B250383 : Blo 247818 250383 := bstep (se 1 (by rfl) ⟨187787, by rfl⟩ : syracuseStep 250383 = 375575) B375575
theorem B250427 : Blo 247818 250427 := bstep (se 1 (by rfl) ⟨187820, by rfl⟩ : syracuseStep 250427 = 375641) B375641
theorem B709181 : Blo 247818 709181 := bstep (se 3 (by rfl) ⟨132971, by rfl⟩ : syracuseStep 709181 = 265943) B265943
theorem B250503 : Blo 247818 250503 := bstep (se 1 (by rfl) ⟨187877, by rfl⟩ : syracuseStep 250503 = 375755) B375755
theorem B250511 : Blo 247818 250511 := bstep (se 1 (by rfl) ⟨187883, by rfl⟩ : syracuseStep 250511 = 375767) B375767
theorem B283279 : Blo 247818 283279 := bstep (se 1 (by rfl) ⟨212459, by rfl⟩ : syracuseStep 283279 = 424919) B424919
theorem B250555 : Blo 247818 250555 := bstep (se 1 (by rfl) ⟨187916, by rfl⟩ : syracuseStep 250555 = 375833) B375833
theorem B250631 : Blo 247818 250631 := bstep (se 1 (by rfl) ⟨187973, by rfl⟩ : syracuseStep 250631 = 375947) B375947
theorem B250639 : Blo 247818 250639 := bstep (se 1 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 250639 = 375959) B375959
theorem B316219 : Blo 247818 316219 := bstep (se 1 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 316219 = 474329) B474329
theorem B250683 : Blo 247818 250683 := bstep (se 1 (by rfl) ⟨188012, by rfl⟩ : syracuseStep 250683 = 376025) B376025
theorem B840563 : Blo 247818 840563 := bstep (se 1 (by rfl) ⟨630422, by rfl⟩ : syracuseStep 840563 = 1260845) B1260845
theorem B250759 : Blo 247818 250759 := bstep (se 1 (by rfl) ⟨188069, by rfl⟩ : syracuseStep 250759 = 376139) B376139
theorem B250767 : Blo 247818 250767 := bstep (se 1 (by rfl) ⟨188075, by rfl⟩ : syracuseStep 250767 = 376151) B376151
theorem B709523 : Blo 247818 709523 := bstep (se 1 (by rfl) ⟨532142, by rfl⟩ : syracuseStep 709523 = 1064285) B1064285
theorem B807833 : Blo 247818 807833 := bstep (se 2 (by rfl) ⟨302937, by rfl⟩ : syracuseStep 807833 = 605875) B605875
theorem B906137 : Blo 247818 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B250811 : Blo 247818 250811 := bstep (se 1 (by rfl) ⟨188108, by rfl⟩ : syracuseStep 250811 = 376217) B376217
theorem B250887 : Blo 247818 250887 := bstep (se 1 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 250887 = 376331) B376331
theorem B250895 : Blo 247818 250895 := bstep (se 1 (by rfl) ⟨188171, by rfl⟩ : syracuseStep 250895 = 376343) B376343
theorem B250939 : Blo 247818 250939 := bstep (se 1 (by rfl) ⟨188204, by rfl⟩ : syracuseStep 250939 = 376409) B376409
theorem B251015 : Blo 247818 251015 := bstep (se 1 (by rfl) ⟨188261, by rfl⟩ : syracuseStep 251015 = 376523) B376523
theorem B251023 : Blo 247818 251023 := bstep (se 1 (by rfl) ⟨188267, by rfl⟩ : syracuseStep 251023 = 376535) B376535
theorem B251067 : Blo 247818 251067 := bstep (se 1 (by rfl) ⟨188300, by rfl⟩ : syracuseStep 251067 = 376601) B376601
theorem B251143 : Blo 247818 251143 := bstep (se 1 (by rfl) ⟨188357, by rfl⟩ : syracuseStep 251143 = 376715) B376715
theorem B251151 : Blo 247818 251151 := bstep (se 1 (by rfl) ⟨188363, by rfl⟩ : syracuseStep 251151 = 376727) B376727
theorem B251195 : Blo 247818 251195 := bstep (se 1 (by rfl) ⟨188396, by rfl⟩ : syracuseStep 251195 = 376793) B376793
theorem B251271 : Blo 247818 251271 := bstep (se 1 (by rfl) ⟨188453, by rfl⟩ : syracuseStep 251271 = 376907) B376907
theorem B251279 : Blo 247818 251279 := bstep (se 1 (by rfl) ⟨188459, by rfl⟩ : syracuseStep 251279 = 376919) B376919
theorem B251323 : Blo 247818 251323 := bstep (se 1 (by rfl) ⟨188492, by rfl⟩ : syracuseStep 251323 = 376985) B376985
theorem B251399 : Blo 247818 251399 := bstep (se 1 (by rfl) ⟨188549, by rfl⟩ : syracuseStep 251399 = 377099) B377099
theorem B251407 : Blo 247818 251407 := bstep (se 1 (by rfl) ⟨188555, by rfl⟩ : syracuseStep 251407 = 377111) B377111
theorem B251451 : Blo 247818 251451 := bstep (se 1 (by rfl) ⟨188588, by rfl⟩ : syracuseStep 251451 = 377177) B377177
theorem B2840183 : Blo 247818 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B906871 : Blo 247818 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B251527 : Blo 247818 251527 := bstep (se 1 (by rfl) ⟨188645, by rfl⟩ : syracuseStep 251527 = 377291) B377291
theorem B251535 : Blo 247818 251535 := bstep (se 1 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 251535 = 377303) B377303
theorem B251579 : Blo 247818 251579 := bstep (se 1 (by rfl) ⟨188684, by rfl⟩ : syracuseStep 251579 = 377369) B377369
theorem B317191 : Blo 247818 317191 := bstep (se 1 (by rfl) ⟨237893, by rfl⟩ : syracuseStep 317191 = 475787) B475787
theorem B251655 : Blo 247818 251655 := bstep (se 1 (by rfl) ⟨188741, by rfl⟩ : syracuseStep 251655 = 377483) B377483
theorem B251663 : Blo 247818 251663 := bstep (se 1 (by rfl) ⟨188747, by rfl⟩ : syracuseStep 251663 = 377495) B377495
theorem B251707 : Blo 247818 251707 := bstep (se 1 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 251707 = 377561) B377561
theorem B251783 : Blo 247818 251783 := bstep (se 1 (by rfl) ⟨188837, by rfl⟩ : syracuseStep 251783 = 377675) B377675
theorem B251791 : Blo 247818 251791 := bstep (se 1 (by rfl) ⟨188843, by rfl⟩ : syracuseStep 251791 = 377687) B377687
theorem B448571 : Blo 247818 448571 := bstep (se 1 (by rfl) ⟨336428, by rfl⟩ : syracuseStep 448571 = 672857) B672857
theorem B317611 : Blo 247818 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B317839 : Blo 247818 317839 := bstep (se 1 (by rfl) ⟨238379, by rfl⟩ : syracuseStep 317839 = 476759) B476759
theorem B1530661 : Blo 247818 1530661 := bstep (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) B286999
theorem B7199603 : Blo 247818 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B1072025 : Blo 247818 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B711767 : Blo 247818 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B318583 : Blo 247818 318583 := bstep (se 1 (by rfl) ⟨238937, by rfl⟩ : syracuseStep 318583 = 477875) B477875
theorem B1269107 : Blo 247818 1269107 := bstep (se 1 (by rfl) ⟨951830, by rfl⟩ : syracuseStep 1269107 = 1903661) B1903661
theorem B843155 : Blo 247818 843155 := bstep (se 1 (by rfl) ⟨632366, by rfl⟩ : syracuseStep 843155 = 1264733) B1264733
theorem B1793501 : Blo 247818 1793501 := bstep (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) B672563
theorem B679439 : Blo 247818 679439 := bstep (se 1 (by rfl) ⟨509579, by rfl⟩ : syracuseStep 679439 = 1019159) B1019159
theorem B318991 : Blo 247818 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B2612915 : Blo 247818 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B4054835 : Blo 247818 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B1269593 : Blo 247818 1269593 := bstep (se 2 (by rfl) ⟨476097, by rfl⟩ : syracuseStep 1269593 = 952195) B952195
theorem B450451 : Blo 247818 450451 := bstep (se 1 (by rfl) ⟨337838, by rfl⟩ : syracuseStep 450451 = 675677) B675677
theorem B680089 : Blo 247818 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B287035 : Blo 247818 287035 := bstep (se 1 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 287035 = 430553) B430553
theorem B418439 : Blo 247818 418439 := bstep (se 1 (by rfl) ⟨313829, by rfl⟩ : syracuseStep 418439 = 627659) B627659
theorem B352939 : Blo 247818 352939 := bstep (se 1 (by rfl) ⟨264704, by rfl⟩ : syracuseStep 352939 = 529409) B529409
theorem B844559 : Blo 247818 844559 := bstep (se 1 (by rfl) ⟨633419, by rfl⟩ : syracuseStep 844559 = 1266839) B1266839
theorem B844829 : Blo 247818 844829 := bstep (se 3 (by rfl) ⟨158405, by rfl⟩ : syracuseStep 844829 = 316811) B316811
theorem B353423 : Blo 247818 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B419087 : Blo 247818 419087 := bstep (se 1 (by rfl) ⟨314315, by rfl⟩ : syracuseStep 419087 = 628631) B628631
theorem B452297 : Blo 247818 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B714511 : Blo 247818 714511 := bstep (se 1 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 714511 = 1071767) B1071767
theorem B419627 : Blo 247818 419627 := bstep (se 1 (by rfl) ⟨314720, by rfl⟩ : syracuseStep 419627 = 629441) B629441
theorem B714557 : Blo 247818 714557 := bstep (se 3 (by rfl) ⟨133979, by rfl⟩ : syracuseStep 714557 = 267959) B267959
theorem B1271699 : Blo 247818 1271699 := bstep (se 1 (by rfl) ⟨953774, by rfl⟩ : syracuseStep 1271699 = 1907549) B1907549
theorem B714899 : Blo 247818 714899 := bstep (se 1 (by rfl) ⟨536174, by rfl⟩ : syracuseStep 714899 = 1072349) B1072349
theorem B420025 : Blo 247818 420025 := bstep (se 2 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 420025 = 315019) B315019
theorem B1697993 : Blo 247818 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B1075457 : Blo 247818 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B6416657 : Blo 247818 6416657 := bstep (se 2 (by rfl) ⟨2406246, by rfl⟩ : syracuseStep 6416657 = 4812493) B4812493
theorem B2713949 : Blo 247818 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B846233 : Blo 247818 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B5434127 : Blo 247818 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B420727 : Blo 247818 420727 := bstep (se 1 (by rfl) ⟨315545, by rfl⟩ : syracuseStep 420727 = 631091) B631091
theorem B715787 : Blo 247818 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B1076267 : Blo 247818 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B420923 : Blo 247818 420923 := bstep (se 1 (by rfl) ⟨315692, by rfl⟩ : syracuseStep 420923 = 631385) B631385
theorem B846935 : Blo 247818 846935 := bstep (se 1 (by rfl) ⟨635201, by rfl⟩ : syracuseStep 846935 = 1270403) B1270403
theorem B355627 : Blo 247818 355627 := bstep (se 1 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 355627 = 533441) B533441
theorem B421321 : Blo 247818 421321 := bstep (se 2 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 421321 = 315991) B315991
theorem B355855 : Blo 247818 355855 := bstep (se 1 (by rfl) ⟨266891, by rfl⟩ : syracuseStep 355855 = 533783) B533783
theorem B847421 : Blo 247818 847421 := bstep (se 3 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 847421 = 317783) B317783
theorem B1634365 : Blo 247818 1634365 := bstep (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) B612887
theorem B422023 : Blo 247818 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B1798433 : Blo 247818 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B1340023 : Blo 247818 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B848585 : Blo 247818 848585 := bstep (se 2 (by rfl) ⟨318219, by rfl⟩ : syracuseStep 848585 = 636439) B636439
theorem B422671 : Blo 247818 422671 := bstep (se 1 (by rfl) ⟨317003, by rfl⟩ : syracuseStep 422671 = 634007) B634007
theorem B1274777 : Blo 247818 1274777 := bstep (se 2 (by rfl) ⟨478041, by rfl⟩ : syracuseStep 1274777 = 956083) B956083
theorem B848825 : Blo 247818 848825 := bstep (se 2 (by rfl) ⟨318309, by rfl⟩ : syracuseStep 848825 = 636619) B636619
theorem B947153 : Blo 247818 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B9172099 : Blo 247818 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B423211 : Blo 247818 423211 := bstep (se 1 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 423211 = 634817) B634817
theorem B947609 : Blo 247818 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B423353 : Blo 247818 423353 := bstep (se 2 (by rfl) ⟨158757, by rfl⟩ : syracuseStep 423353 = 317515) B317515
theorem B849419 : Blo 247818 849419 := bstep (se 1 (by rfl) ⟨637064, by rfl⟩ : syracuseStep 849419 = 1274129) B1274129
theorem B849437 : Blo 247818 849437 := bstep (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) B318539
theorem B849527 : Blo 247818 849527 := bstep (se 1 (by rfl) ⟨637145, by rfl⟩ : syracuseStep 849527 = 1274291) B1274291
theorem B1341451 : Blo 247818 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B424055 : Blo 247818 424055 := bstep (se 1 (by rfl) ⟨318041, by rfl⟩ : syracuseStep 424055 = 636083) B636083
theorem B358543 : Blo 247818 358543 := bstep (se 1 (by rfl) ⟨268907, by rfl⟩ : syracuseStep 358543 = 537815) B537815
theorem B7174453 : Blo 247818 7174453 := bstep (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) B672605
theorem B817523 : Blo 247818 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B948779 : Blo 247818 948779 := bstep (se 1 (by rfl) ⟨711584, by rfl⟩ : syracuseStep 948779 = 1423169) B1423169
theorem B424507 : Blo 247818 424507 := bstep (se 1 (by rfl) ⟨318380, by rfl⟩ : syracuseStep 424507 = 636761) B636761
theorem B1440449 : Blo 247818 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B424649 : Blo 247818 424649 := bstep (se 2 (by rfl) ⟨159243, by rfl⟩ : syracuseStep 424649 = 318487) B318487
theorem B6454333 : Blo 247818 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B557999 : Blo 247818 557999 := bstep (se 1 (by rfl) ⟨418499, by rfl⟩ : syracuseStep 557999 = 836999) B836999
theorem B951223 : Blo 247818 951223 := bstep (se 1 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 951223 = 1426835) B1426835
theorem B2032613 : Blo 247818 2032613 := bstep (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) B381115
theorem B558251 : Blo 247818 558251 := bstep (se 1 (by rfl) ⟨418688, by rfl⟩ : syracuseStep 558251 = 837377) B837377
theorem B951695 : Blo 247818 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B3409451 : Blo 247818 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B1902203 : Blo 247818 1902203 := bstep (se 1 (by rfl) ⟨1426652, by rfl⟩ : syracuseStep 1902203 = 2853305) B2853305
theorem B3212945 : Blo 247818 3212945 := bstep (se 2 (by rfl) ⟨1204854, by rfl⟩ : syracuseStep 3212945 = 2409709) B2409709
theorem B558791 : Blo 247818 558791 := bstep (se 1 (by rfl) ⟨419093, by rfl⟩ : syracuseStep 558791 = 838187) B838187
theorem B755639 : Blo 247818 755639 := bstep (se 1 (by rfl) ⟨566729, by rfl⟩ : syracuseStep 755639 = 1133459) B1133459
theorem B1804517 : Blo 247818 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B952681 : Blo 247818 952681 := bstep (se 2 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 952681 = 714511) B714511
theorem B30771683 : Blo 247818 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B559655 : Blo 247818 559655 := bstep (se 1 (by rfl) ⟨419741, by rfl⟩ : syracuseStep 559655 = 839483) B839483
theorem B952955 : Blo 247818 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B559979 : Blo 247818 559979 := bstep (se 1 (by rfl) ⟨419984, by rfl⟩ : syracuseStep 559979 = 839969) B839969
theorem B560033 : Blo 247818 560033 := bstep (se 2 (by rfl) ⟨210012, by rfl⟩ : syracuseStep 560033 = 420025) B420025
theorem B560375 : Blo 247818 560375 := bstep (se 1 (by rfl) ⟨420281, by rfl⟩ : syracuseStep 560375 = 840563) B840563
theorem B265567 : Blo 247818 265567 := bstep (se 1 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 265567 = 398351) B398351
theorem B1609085 : Blo 247818 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B855539 : Blo 247818 855539 := bstep (se 1 (by rfl) ⟨641654, by rfl⟩ : syracuseStep 855539 = 1283309) B1283309
theorem B560969 : Blo 247818 560969 := bstep (se 2 (by rfl) ⟨210363, by rfl⟩ : syracuseStep 560969 = 420727) B420727
theorem B299047 : Blo 247818 299047 := bstep (se 1 (by rfl) ⟨224285, by rfl⟩ : syracuseStep 299047 = 448571) B448571
theorem B59609621 : Blo 247818 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B561761 : Blo 247818 561761 := bstep (se 2 (by rfl) ⟨210660, by rfl⟩ : syracuseStep 561761 = 421321) B421321
theorem B562103 : Blo 247818 562103 := bstep (se 1 (by rfl) ⟨421577, by rfl⟩ : syracuseStep 562103 = 843155) B843155
theorem B2692115 : Blo 247818 2692115 := bstep (se 1 (by rfl) ⟨2019086, by rfl⟩ : syracuseStep 2692115 = 4038173) B4038173
theorem B1741943 : Blo 247818 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B562697 : Blo 247818 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B563039 : Blo 247818 563039 := bstep (se 1 (by rfl) ⟨422279, by rfl⟩ : syracuseStep 563039 = 844559) B844559
theorem B2824145 : Blo 247818 2824145 := bstep (se 2 (by rfl) ⟨1059054, by rfl⟩ : syracuseStep 2824145 = 2118109) B2118109
theorem B563219 : Blo 247818 563219 := bstep (se 1 (by rfl) ⟨422414, by rfl⟩ : syracuseStep 563219 = 844829) B844829
theorem B628793 : Blo 247818 628793 := bstep (se 2 (by rfl) ⟨235797, by rfl⟩ : syracuseStep 628793 = 471595) B471595
theorem B563561 : Blo 247818 563561 := bstep (se 2 (by rfl) ⟨211335, by rfl⟩ : syracuseStep 563561 = 422671) B422671
theorem B301531 : Blo 247818 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B596603 : Blo 247818 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B12229465 : Blo 247818 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B1809299 : Blo 247818 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B596911 : Blo 247818 596911 := bstep (se 1 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 596911 = 895367) B895367
theorem B564155 : Blo 247818 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B564281 : Blo 247818 564281 := bstep (se 2 (by rfl) ⟨211605, by rfl⟩ : syracuseStep 564281 = 423211) B423211
theorem B400555 : Blo 247818 400555 := bstep (se 1 (by rfl) ⟨300416, by rfl⟩ : syracuseStep 400555 = 600833) B600833
theorem B400631 : Blo 247818 400631 := bstep (se 1 (by rfl) ⟨300473, by rfl⟩ : syracuseStep 400631 = 600947) B600947
theorem B4300121 : Blo 247818 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B564623 : Blo 247818 564623 := bstep (se 1 (by rfl) ⟨423467, by rfl⟩ : syracuseStep 564623 = 846935) B846935
theorem B630281 : Blo 247818 630281 := bstep (se 2 (by rfl) ⟨236355, by rfl⟩ : syracuseStep 630281 = 472711) B472711
theorem B532091 : Blo 247818 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B564947 : Blo 247818 564947 := bstep (se 1 (by rfl) ⟨423710, by rfl⟩ : syracuseStep 564947 = 847421) B847421
theorem B1449721 : Blo 247818 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B335995 : Blo 247818 335995 := bstep (se 1 (by rfl) ⟨251996, by rfl⟩ : syracuseStep 335995 = 503993) B503993
theorem B565723 : Blo 247818 565723 := bstep (se 1 (by rfl) ⟨424292, by rfl⟩ : syracuseStep 565723 = 848585) B848585
theorem B565883 : Blo 247818 565883 := bstep (se 1 (by rfl) ⟨424412, by rfl⟩ : syracuseStep 565883 = 848825) B848825
theorem B631435 : Blo 247818 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B402169 : Blo 247818 402169 := bstep (se 2 (by rfl) ⟨150813, by rfl⟩ : syracuseStep 402169 = 301627) B301627
theorem B566009 : Blo 247818 566009 := bstep (se 2 (by rfl) ⟨212253, by rfl⟩ : syracuseStep 566009 = 424507) B424507
theorem B1352477 : Blo 247818 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B533321 : Blo 247818 533321 := bstep (se 2 (by rfl) ⟨199995, by rfl⟩ : syracuseStep 533321 = 399991) B399991
theorem B533423 : Blo 247818 533423 := bstep (se 1 (by rfl) ⟨400067, by rfl⟩ : syracuseStep 533423 = 800135) B800135
theorem B631739 : Blo 247818 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B566279 : Blo 247818 566279 := bstep (se 1 (by rfl) ⟨424709, by rfl⟩ : syracuseStep 566279 = 849419) B849419
theorem B566291 : Blo 247818 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B2040881 : Blo 247818 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B566351 : Blo 247818 566351 := bstep (se 1 (by rfl) ⟨424763, by rfl⟩ : syracuseStep 566351 = 849527) B849527
theorem B5481989 : Blo 247818 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B14526053 : Blo 247818 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B632519 : Blo 247818 632519 := bstep (se 1 (by rfl) ⟨474389, by rfl⟩ : syracuseStep 632519 = 948779) B948779
theorem B632569 : Blo 247818 632569 := bstep (se 2 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 632569 = 474427) B474427
theorem B796445 : Blo 247818 796445 := bstep (se 3 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 796445 = 298667) B298667
theorem B960299 : Blo 247818 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B2402405 : Blo 247818 2402405 := bstep (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) B450451
theorem B633217 : Blo 247818 633217 := bstep (se 2 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 633217 = 474913) B474913
theorem B1256147 : Blo 247818 1256147 := bstep (se 1 (by rfl) ⟨942110, by rfl⟩ : syracuseStep 1256147 = 1884221) B1884221
theorem B404399 : Blo 247818 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B601015 : Blo 247818 601015 := bstep (se 1 (by rfl) ⟨450761, by rfl⟩ : syracuseStep 601015 = 901523) B901523
theorem B2862053 : Blo 247818 2862053 := bstep (se 4 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 2862053 = 536635) B536635
theorem B634027 : Blo 247818 634027 := bstep (se 1 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 634027 = 951041) B951041
theorem B2010359 : Blo 247818 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B3910949 : Blo 247818 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B372143 : Blo 247818 372143 := bstep (se 1 (by rfl) ⟨279107, by rfl⟩ : syracuseStep 372143 = 558215) B558215
theorem B634331 : Blo 247818 634331 := bstep (se 1 (by rfl) ⟨475748, by rfl⟩ : syracuseStep 634331 = 951497) B951497
theorem B372233 : Blo 247818 372233 := bstep (se 2 (by rfl) ⟨139587, by rfl⟩ : syracuseStep 372233 = 279175) B279175
theorem B372263 : Blo 247818 372263 := bstep (se 1 (by rfl) ⟨279197, by rfl⟩ : syracuseStep 372263 = 558395) B558395
theorem B470585 : Blo 247818 470585 := bstep (se 2 (by rfl) ⟨176469, by rfl⟩ : syracuseStep 470585 = 352939) B352939
theorem B372347 : Blo 247818 372347 := bstep (se 1 (by rfl) ⟨279260, by rfl⟩ : syracuseStep 372347 = 558521) B558521
theorem B372473 : Blo 247818 372473 := bstep (se 2 (by rfl) ⟨139677, by rfl⟩ : syracuseStep 372473 = 279355) B279355
theorem B372575 : Blo 247818 372575 := bstep (se 1 (by rfl) ⟨279431, by rfl⟩ : syracuseStep 372575 = 558863) B558863
theorem B372587 : Blo 247818 372587 := bstep (se 1 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 372587 = 558881) B558881
theorem B470927 : Blo 247818 470927 := bstep (se 1 (by rfl) ⟨353195, by rfl⟩ : syracuseStep 470927 = 706391) B706391
theorem B569263 : Blo 247818 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B372815 : Blo 247818 372815 := bstep (se 1 (by rfl) ⟨279611, by rfl⟩ : syracuseStep 372815 = 559223) B559223
theorem B372935 : Blo 247818 372935 := bstep (se 1 (by rfl) ⟨279701, by rfl⟩ : syracuseStep 372935 = 559403) B559403
theorem B373097 : Blo 247818 373097 := bstep (se 2 (by rfl) ⟨139911, by rfl⟩ : syracuseStep 373097 = 279823) B279823
theorem B3912065 : Blo 247818 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B373175 : Blo 247818 373175 := bstep (se 1 (by rfl) ⟨279881, by rfl⟩ : syracuseStep 373175 = 559763) B559763
theorem B373211 : Blo 247818 373211 := bstep (se 1 (by rfl) ⟨279908, by rfl⟩ : syracuseStep 373211 = 559817) B559817
theorem B799417 : Blo 247818 799417 := bstep (se 2 (by rfl) ⟨299781, by rfl⟩ : syracuseStep 799417 = 599563) B599563
theorem B1061585 : Blo 247818 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B635809 : Blo 247818 635809 := bstep (se 2 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 635809 = 476857) B476857
theorem B1258415 : Blo 247818 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B373679 : Blo 247818 373679 := bstep (se 1 (by rfl) ⟨280259, by rfl⟩ : syracuseStep 373679 = 560519) B560519
theorem B373769 : Blo 247818 373769 := bstep (se 2 (by rfl) ⟨140163, by rfl⟩ : syracuseStep 373769 = 280327) B280327
theorem B373799 : Blo 247818 373799 := bstep (se 1 (by rfl) ⟨280349, by rfl⟩ : syracuseStep 373799 = 560699) B560699
theorem B373883 : Blo 247818 373883 := bstep (se 1 (by rfl) ⟨280412, by rfl⟩ : syracuseStep 373883 = 560825) B560825
theorem B38810765 : Blo 247818 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B3421385 : Blo 247818 3421385 := bstep (se 2 (by rfl) ⟨1283019, by rfl⟩ : syracuseStep 3421385 = 2566039) B2566039
theorem B374009 : Blo 247818 374009 := bstep (se 2 (by rfl) ⟨140253, by rfl⟩ : syracuseStep 374009 = 280507) B280507
theorem B374111 : Blo 247818 374111 := bstep (se 1 (by rfl) ⟨280583, by rfl⟩ : syracuseStep 374111 = 561167) B561167
theorem B374123 : Blo 247818 374123 := bstep (se 1 (by rfl) ⟨280592, by rfl⟩ : syracuseStep 374123 = 561185) B561185
theorem B4634003 : Blo 247818 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B374351 : Blo 247818 374351 := bstep (se 1 (by rfl) ⟨280763, by rfl⟩ : syracuseStep 374351 = 561527) B561527
theorem B374471 : Blo 247818 374471 := bstep (se 1 (by rfl) ⟨280853, by rfl⟩ : syracuseStep 374471 = 561707) B561707
theorem B898769 : Blo 247818 898769 := bstep (se 2 (by rfl) ⟨337038, by rfl⟩ : syracuseStep 898769 = 674077) B674077
theorem B472787 : Blo 247818 472787 := bstep (se 1 (by rfl) ⟨354590, by rfl⟩ : syracuseStep 472787 = 709181) B709181
theorem B374633 : Blo 247818 374633 := bstep (se 2 (by rfl) ⟨140487, by rfl⟩ : syracuseStep 374633 = 280975) B280975
theorem B473015 : Blo 247818 473015 := bstep (se 1 (by rfl) ⟨354761, by rfl⟩ : syracuseStep 473015 = 709523) B709523
theorem B374711 : Blo 247818 374711 := bstep (se 1 (by rfl) ⟨281033, by rfl⟩ : syracuseStep 374711 = 562067) B562067
theorem B538555 : Blo 247818 538555 := bstep (se 1 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 538555 = 807833) B807833
theorem B604091 : Blo 247818 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B374747 : Blo 247818 374747 := bstep (se 1 (by rfl) ⟨281060, by rfl⟩ : syracuseStep 374747 = 562121) B562121
theorem B375215 : Blo 247818 375215 := bstep (se 1 (by rfl) ⟨281411, by rfl⟩ : syracuseStep 375215 = 562823) B562823
theorem B375305 : Blo 247818 375305 := bstep (se 2 (by rfl) ⟨140739, by rfl⟩ : syracuseStep 375305 = 281479) B281479
theorem B375335 : Blo 247818 375335 := bstep (se 1 (by rfl) ⟨281501, by rfl⟩ : syracuseStep 375335 = 563003) B563003
theorem B375419 : Blo 247818 375419 := bstep (se 1 (by rfl) ⟨281564, by rfl⟩ : syracuseStep 375419 = 563129) B563129
theorem B375545 : Blo 247818 375545 := bstep (se 2 (by rfl) ⟨140829, by rfl⟩ : syracuseStep 375545 = 281659) B281659
theorem B375647 : Blo 247818 375647 := bstep (se 1 (by rfl) ⟨281735, by rfl⟩ : syracuseStep 375647 = 563471) B563471
theorem B375659 : Blo 247818 375659 := bstep (se 1 (by rfl) ⟨281744, by rfl⟩ : syracuseStep 375659 = 563489) B563489
theorem B474169 : Blo 247818 474169 := bstep (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) B355627
theorem B375887 : Blo 247818 375887 := bstep (se 1 (by rfl) ⟨281915, by rfl⟩ : syracuseStep 375887 = 563831) B563831
theorem B376007 : Blo 247818 376007 := bstep (se 1 (by rfl) ⟨282005, by rfl⟩ : syracuseStep 376007 = 564011) B564011
theorem B4799735 : Blo 247818 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B474473 : Blo 247818 474473 := bstep (se 2 (by rfl) ⟨177927, by rfl⟩ : syracuseStep 474473 = 355855) B355855
theorem B376169 : Blo 247818 376169 := bstep (se 2 (by rfl) ⟨141063, by rfl⟩ : syracuseStep 376169 = 282127) B282127
theorem B474511 : Blo 247818 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B376247 : Blo 247818 376247 := bstep (se 1 (by rfl) ⟨282185, by rfl⟩ : syracuseStep 376247 = 564371) B564371
theorem B376283 : Blo 247818 376283 := bstep (se 1 (by rfl) ⟨282212, by rfl⟩ : syracuseStep 376283 = 564425) B564425
theorem B1883735 : Blo 247818 1883735 := bstep (se 1 (by rfl) ⟨1412801, by rfl⟩ : syracuseStep 1883735 = 2825603) B2825603
theorem B1195667 : Blo 247818 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B2703223 : Blo 247818 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B376751 : Blo 247818 376751 := bstep (se 1 (by rfl) ⟨282563, by rfl⟩ : syracuseStep 376751 = 565127) B565127
theorem B376841 : Blo 247818 376841 := bstep (se 2 (by rfl) ⟨141315, by rfl⟩ : syracuseStep 376841 = 282631) B282631
theorem B376871 : Blo 247818 376871 := bstep (se 1 (by rfl) ⟨282653, by rfl⟩ : syracuseStep 376871 = 565307) B565307
theorem B2179153 : Blo 247818 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B3850355 : Blo 247818 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B376955 : Blo 247818 376955 := bstep (se 1 (by rfl) ⟨282716, by rfl⟩ : syracuseStep 376955 = 565433) B565433
theorem B377081 : Blo 247818 377081 := bstep (se 2 (by rfl) ⟨141405, by rfl⟩ : syracuseStep 377081 = 282811) B282811
theorem B2015549 : Blo 247818 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B7192907 : Blo 247818 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B377183 : Blo 247818 377183 := bstep (se 1 (by rfl) ⟨282887, by rfl⟩ : syracuseStep 377183 = 565775) B565775
theorem B377195 : Blo 247818 377195 := bstep (se 1 (by rfl) ⟨282896, by rfl⟩ : syracuseStep 377195 = 565793) B565793
theorem B278959 : Blo 247818 278959 := bstep (se 1 (by rfl) ⟨209219, by rfl⟩ : syracuseStep 278959 = 418439) B418439
theorem B377423 : Blo 247818 377423 := bstep (se 1 (by rfl) ⟨283067, by rfl⟩ : syracuseStep 377423 = 566135) B566135
theorem B2867885 : Blo 247818 2867885 := bstep (se 3 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 2867885 = 1075457) B1075457
theorem B377543 : Blo 247818 377543 := bstep (se 1 (by rfl) ⟨283157, by rfl⟩ : syracuseStep 377543 = 566315) B566315
theorem B1786697 : Blo 247818 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B279391 : Blo 247818 279391 := bstep (se 1 (by rfl) ⟨209543, by rfl⟩ : syracuseStep 279391 = 419087) B419087
theorem B377705 : Blo 247818 377705 := bstep (se 2 (by rfl) ⟨141639, by rfl⟩ : syracuseStep 377705 = 283279) B283279
theorem B836459 : Blo 247818 836459 := bstep (se 1 (by rfl) ⟨627344, by rfl⟩ : syracuseStep 836459 = 1254689) B1254689
theorem B836513 : Blo 247818 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B279751 : Blo 247818 279751 := bstep (se 1 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 279751 = 419627) B419627
theorem B476371 : Blo 247818 476371 := bstep (se 1 (by rfl) ⟨357278, by rfl⟩ : syracuseStep 476371 = 714557) B714557
theorem B705935 : Blo 247818 705935 := bstep (se 1 (by rfl) ⟨529451, by rfl⟩ : syracuseStep 705935 = 1058903) B1058903
theorem B476599 : Blo 247818 476599 := bstep (se 1 (by rfl) ⟨357449, by rfl⟩ : syracuseStep 476599 = 714899) B714899
theorem B1131995 : Blo 247818 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B837107 : Blo 247818 837107 := bstep (se 1 (by rfl) ⟨627830, by rfl⟩ : syracuseStep 837107 = 1255661) B1255661
theorem B673289 : Blo 247818 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B4277771 : Blo 247818 4277771 := bstep (se 1 (by rfl) ⟨3208328, by rfl⟩ : syracuseStep 4277771 = 6416657) B6416657
theorem B3622751 : Blo 247818 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B903095 : Blo 247818 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B477191 : Blo 247818 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B837647 : Blo 247818 837647 := bstep (se 1 (by rfl) ⟨628235, by rfl⟩ : syracuseStep 837647 = 1256471) B1256471
theorem B247847 : Blo 247818 247847 := bstep (se 1 (by rfl) ⟨185885, by rfl⟩ : syracuseStep 247847 = 371771) B371771
theorem B280615 : Blo 247818 280615 := bstep (se 1 (by rfl) ⟨210461, by rfl⟩ : syracuseStep 280615 = 420923) B420923
theorem B2410553 : Blo 247818 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B247887 : Blo 247818 247887 := bstep (se 1 (by rfl) ⟨185915, by rfl⟩ : syracuseStep 247887 = 371831) B371831
theorem B247903 : Blo 247818 247903 := bstep (se 1 (by rfl) ⟨185927, by rfl⟩ : syracuseStep 247903 = 371855) B371855
theorem B247931 : Blo 247818 247931 := bstep (se 1 (by rfl) ⟨185948, by rfl⟩ : syracuseStep 247931 = 371897) B371897
theorem B247983 : Blo 247818 247983 := bstep (se 1 (by rfl) ⟨185987, by rfl⟩ : syracuseStep 247983 = 371975) B371975
theorem B248007 : Blo 247818 248007 := bstep (se 1 (by rfl) ⟨186005, by rfl⟩ : syracuseStep 248007 = 372011) B372011
theorem B248027 : Blo 247818 248027 := bstep (se 1 (by rfl) ⟨186020, by rfl⟩ : syracuseStep 248027 = 372041) B372041
theorem B248103 : Blo 247818 248103 := bstep (se 1 (by rfl) ⟨186077, by rfl⟩ : syracuseStep 248103 = 372155) B372155
theorem B248143 : Blo 247818 248143 := bstep (se 1 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 248143 = 372215) B372215
theorem B248159 : Blo 247818 248159 := bstep (se 1 (by rfl) ⟨186119, by rfl⟩ : syracuseStep 248159 = 372239) B372239
theorem B248187 : Blo 247818 248187 := bstep (se 1 (by rfl) ⟨186140, by rfl⟩ : syracuseStep 248187 = 372281) B372281
theorem B1067393 : Blo 247818 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B248239 : Blo 247818 248239 := bstep (se 1 (by rfl) ⟨186179, by rfl⟩ : syracuseStep 248239 = 372359) B372359
theorem B510391 : Blo 247818 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B248263 : Blo 247818 248263 := bstep (se 1 (by rfl) ⟨186197, by rfl⟩ : syracuseStep 248263 = 372395) B372395
theorem B248283 : Blo 247818 248283 := bstep (se 1 (by rfl) ⟨186212, by rfl⟩ : syracuseStep 248283 = 372425) B372425
theorem B3590689 : Blo 247818 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B313895 : Blo 247818 313895 := bstep (se 1 (by rfl) ⟨235421, by rfl⟩ : syracuseStep 313895 = 470843) B470843
theorem B248359 : Blo 247818 248359 := bstep (se 1 (by rfl) ⟨186269, by rfl⟩ : syracuseStep 248359 = 372539) B372539
theorem B248399 : Blo 247818 248399 := bstep (se 1 (by rfl) ⟨186299, by rfl⟩ : syracuseStep 248399 = 372599) B372599
theorem B248415 : Blo 247818 248415 := bstep (se 1 (by rfl) ⟨186311, by rfl⟩ : syracuseStep 248415 = 372623) B372623
theorem B838241 : Blo 247818 838241 := bstep (se 2 (by rfl) ⟨314340, by rfl⟩ : syracuseStep 838241 = 628681) B628681
theorem B248443 : Blo 247818 248443 := bstep (se 1 (by rfl) ⟨186332, by rfl⟩ : syracuseStep 248443 = 372665) B372665
theorem B248495 : Blo 247818 248495 := bstep (se 1 (by rfl) ⟨186371, by rfl⟩ : syracuseStep 248495 = 372743) B372743
theorem B1788601 : Blo 247818 1788601 := bstep (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) B1341451
theorem B248519 : Blo 247818 248519 := bstep (se 1 (by rfl) ⟨186389, by rfl⟩ : syracuseStep 248519 = 372779) B372779
theorem B248539 : Blo 247818 248539 := bstep (se 1 (by rfl) ⟨186404, by rfl⟩ : syracuseStep 248539 = 372809) B372809
theorem B4410085 : Blo 247818 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B248615 : Blo 247818 248615 := bstep (se 1 (by rfl) ⟨186461, by rfl⟩ : syracuseStep 248615 = 372923) B372923
theorem B248655 : Blo 247818 248655 := bstep (se 1 (by rfl) ⟨186491, by rfl⟩ : syracuseStep 248655 = 372983) B372983
theorem B248671 : Blo 247818 248671 := bstep (se 1 (by rfl) ⟨186503, by rfl⟩ : syracuseStep 248671 = 373007) B373007
theorem B478057 : Blo 247818 478057 := bstep (se 2 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 478057 = 358543) B358543
theorem B314219 : Blo 247818 314219 := bstep (se 1 (by rfl) ⟨235664, by rfl⟩ : syracuseStep 314219 = 471329) B471329
theorem B1198955 : Blo 247818 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B248699 : Blo 247818 248699 := bstep (se 1 (by rfl) ⟨186524, by rfl⟩ : syracuseStep 248699 = 373049) B373049
theorem B1362863 : Blo 247818 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B248751 : Blo 247818 248751 := bstep (se 1 (by rfl) ⟨186563, by rfl⟩ : syracuseStep 248751 = 373127) B373127
theorem B248775 : Blo 247818 248775 := bstep (se 1 (by rfl) ⟨186581, by rfl⟩ : syracuseStep 248775 = 373163) B373163
theorem B248795 : Blo 247818 248795 := bstep (se 1 (by rfl) ⟨186596, by rfl⟩ : syracuseStep 248795 = 373193) B373193
theorem B248871 : Blo 247818 248871 := bstep (se 1 (by rfl) ⟨186653, by rfl⟩ : syracuseStep 248871 = 373307) B373307
theorem B248911 : Blo 247818 248911 := bstep (se 1 (by rfl) ⟨186683, by rfl⟩ : syracuseStep 248911 = 373367) B373367
theorem B248927 : Blo 247818 248927 := bstep (se 1 (by rfl) ⟨186695, by rfl⟩ : syracuseStep 248927 = 373391) B373391
theorem B248955 : Blo 247818 248955 := bstep (se 1 (by rfl) ⟨186716, by rfl⟩ : syracuseStep 248955 = 373433) B373433
theorem B249007 : Blo 247818 249007 := bstep (se 1 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 249007 = 373511) B373511
theorem B249031 : Blo 247818 249031 := bstep (se 1 (by rfl) ⟨186773, by rfl⟩ : syracuseStep 249031 = 373547) B373547
theorem B249051 : Blo 247818 249051 := bstep (se 1 (by rfl) ⟨186788, by rfl⟩ : syracuseStep 249051 = 373577) B373577
theorem B249127 : Blo 247818 249127 := bstep (se 1 (by rfl) ⟨186845, by rfl⟩ : syracuseStep 249127 = 373691) B373691
theorem B249167 : Blo 247818 249167 := bstep (se 1 (by rfl) ⟨186875, by rfl⟩ : syracuseStep 249167 = 373751) B373751
theorem B249183 : Blo 247818 249183 := bstep (se 1 (by rfl) ⟨186887, by rfl⟩ : syracuseStep 249183 = 373775) B373775
theorem B249211 : Blo 247818 249211 := bstep (se 1 (by rfl) ⟨186908, by rfl⟩ : syracuseStep 249211 = 373817) B373817
theorem B249263 : Blo 247818 249263 := bstep (se 1 (by rfl) ⟨186947, by rfl⟩ : syracuseStep 249263 = 373895) B373895
theorem B249287 : Blo 247818 249287 := bstep (se 1 (by rfl) ⟨186965, by rfl⟩ : syracuseStep 249287 = 373931) B373931
theorem B249307 : Blo 247818 249307 := bstep (se 1 (by rfl) ⟨186980, by rfl⟩ : syracuseStep 249307 = 373961) B373961
theorem B249383 : Blo 247818 249383 := bstep (se 1 (by rfl) ⟨187037, by rfl⟩ : syracuseStep 249383 = 374075) B374075
theorem B249423 : Blo 247818 249423 := bstep (se 1 (by rfl) ⟨187067, by rfl⟩ : syracuseStep 249423 = 374135) B374135
theorem B249439 : Blo 247818 249439 := bstep (se 1 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 249439 = 374159) B374159
theorem B249467 : Blo 247818 249467 := bstep (se 1 (by rfl) ⟨187100, by rfl⟩ : syracuseStep 249467 = 374201) B374201
theorem B282235 : Blo 247818 282235 := bstep (se 1 (by rfl) ⟨211676, by rfl⟩ : syracuseStep 282235 = 423353) B423353
theorem B249519 : Blo 247818 249519 := bstep (se 1 (by rfl) ⟨187139, by rfl⟩ : syracuseStep 249519 = 374279) B374279
theorem B249543 : Blo 247818 249543 := bstep (se 1 (by rfl) ⟨187157, by rfl⟩ : syracuseStep 249543 = 374315) B374315
theorem B249563 : Blo 247818 249563 := bstep (se 1 (by rfl) ⟨187172, by rfl⟩ : syracuseStep 249563 = 374345) B374345
theorem B249639 : Blo 247818 249639 := bstep (se 1 (by rfl) ⟨187229, by rfl⟩ : syracuseStep 249639 = 374459) B374459
theorem B249679 : Blo 247818 249679 := bstep (se 1 (by rfl) ⟨187259, by rfl⟩ : syracuseStep 249679 = 374519) B374519
theorem B249695 : Blo 247818 249695 := bstep (se 1 (by rfl) ⟨187271, by rfl⟩ : syracuseStep 249695 = 374543) B374543
theorem B1888109 : Blo 247818 1888109 := bstep (se 3 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 1888109 = 708041) B708041
theorem B249723 : Blo 247818 249723 := bstep (se 1 (by rfl) ⟨187292, by rfl⟩ : syracuseStep 249723 = 374585) B374585
theorem B3198851 : Blo 247818 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B6442901 : Blo 247818 6442901 := bstep (se 6 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 6442901 = 302011) B302011
theorem B249775 : Blo 247818 249775 := bstep (se 1 (by rfl) ⟨187331, by rfl⟩ : syracuseStep 249775 = 374663) B374663
theorem B249799 : Blo 247818 249799 := bstep (se 1 (by rfl) ⟨187349, by rfl⟩ : syracuseStep 249799 = 374699) B374699
theorem B249819 : Blo 247818 249819 := bstep (se 1 (by rfl) ⟨187364, by rfl⟩ : syracuseStep 249819 = 374729) B374729
theorem B839699 : Blo 247818 839699 := bstep (se 1 (by rfl) ⟨629774, by rfl⟩ : syracuseStep 839699 = 1259549) B1259549
theorem B249895 : Blo 247818 249895 := bstep (se 1 (by rfl) ⟨187421, by rfl⟩ : syracuseStep 249895 = 374843) B374843
theorem B249935 : Blo 247818 249935 := bstep (se 1 (by rfl) ⟨187451, by rfl⟩ : syracuseStep 249935 = 374903) B374903
theorem B282703 : Blo 247818 282703 := bstep (se 1 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 282703 = 424055) B424055
theorem B8605777 : Blo 247818 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B249951 : Blo 247818 249951 := bstep (se 1 (by rfl) ⟨187463, by rfl⟩ : syracuseStep 249951 = 374927) B374927
theorem B315515 : Blo 247818 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B249979 : Blo 247818 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B6475949 : Blo 247818 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B250031 : Blo 247818 250031 := bstep (se 1 (by rfl) ⟨187523, by rfl⟩ : syracuseStep 250031 = 375047) B375047
theorem B250055 : Blo 247818 250055 := bstep (se 1 (by rfl) ⟨187541, by rfl⟩ : syracuseStep 250055 = 375083) B375083
theorem B250075 : Blo 247818 250075 := bstep (se 1 (by rfl) ⟨187556, by rfl⟩ : syracuseStep 250075 = 375113) B375113
theorem B3592421 : Blo 247818 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B545015 : Blo 247818 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B250151 : Blo 247818 250151 := bstep (se 1 (by rfl) ⟨187613, by rfl⟩ : syracuseStep 250151 = 375227) B375227
theorem B250191 : Blo 247818 250191 := bstep (se 1 (by rfl) ⟨187643, by rfl⟩ : syracuseStep 250191 = 375287) B375287
theorem B840023 : Blo 247818 840023 := bstep (se 1 (by rfl) ⟨630017, by rfl⟩ : syracuseStep 840023 = 1260035) B1260035
theorem B250207 : Blo 247818 250207 := bstep (se 1 (by rfl) ⟨187655, by rfl⟩ : syracuseStep 250207 = 375311) B375311
theorem B250235 : Blo 247818 250235 := bstep (se 1 (by rfl) ⟨187676, by rfl⟩ : syracuseStep 250235 = 375353) B375353
theorem B250287 : Blo 247818 250287 := bstep (se 1 (by rfl) ⟨187715, by rfl⟩ : syracuseStep 250287 = 375431) B375431
theorem B250311 : Blo 247818 250311 := bstep (se 1 (by rfl) ⟨187733, by rfl⟩ : syracuseStep 250311 = 375467) B375467
theorem B283099 : Blo 247818 283099 := bstep (se 1 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 283099 = 424649) B424649
theorem B250331 : Blo 247818 250331 := bstep (se 1 (by rfl) ⟨187748, by rfl⟩ : syracuseStep 250331 = 375497) B375497
theorem B250407 : Blo 247818 250407 := bstep (se 1 (by rfl) ⟨187805, by rfl⟩ : syracuseStep 250407 = 375611) B375611
theorem B250447 : Blo 247818 250447 := bstep (se 1 (by rfl) ⟨187835, by rfl⟩ : syracuseStep 250447 = 375671) B375671
theorem B250463 : Blo 247818 250463 := bstep (se 1 (by rfl) ⟨187847, by rfl⟩ : syracuseStep 250463 = 375695) B375695
theorem B250491 : Blo 247818 250491 := bstep (se 1 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 250491 = 375737) B375737
theorem B905863 : Blo 247818 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B250543 : Blo 247818 250543 := bstep (se 1 (by rfl) ⟨187907, by rfl⟩ : syracuseStep 250543 = 375815) B375815
theorem B250567 : Blo 247818 250567 := bstep (se 1 (by rfl) ⟨187925, by rfl⟩ : syracuseStep 250567 = 375851) B375851
theorem B250587 : Blo 247818 250587 := bstep (se 1 (by rfl) ⟨187940, by rfl⟩ : syracuseStep 250587 = 375881) B375881
theorem B250663 : Blo 247818 250663 := bstep (se 1 (by rfl) ⟨187997, by rfl⟩ : syracuseStep 250663 = 375995) B375995
theorem B250703 : Blo 247818 250703 := bstep (se 1 (by rfl) ⟨188027, by rfl⟩ : syracuseStep 250703 = 376055) B376055
theorem B250719 : Blo 247818 250719 := bstep (se 1 (by rfl) ⟨188039, by rfl⟩ : syracuseStep 250719 = 376079) B376079
theorem B250747 : Blo 247818 250747 := bstep (se 1 (by rfl) ⟨188060, by rfl⟩ : syracuseStep 250747 = 376121) B376121
theorem B250799 : Blo 247818 250799 := bstep (se 1 (by rfl) ⟨188099, by rfl⟩ : syracuseStep 250799 = 376199) B376199
theorem B250823 : Blo 247818 250823 := bstep (se 1 (by rfl) ⟨188117, by rfl⟩ : syracuseStep 250823 = 376235) B376235
theorem B250843 : Blo 247818 250843 := bstep (se 1 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 250843 = 376265) B376265
theorem B250919 : Blo 247818 250919 := bstep (se 1 (by rfl) ⟨188189, by rfl⟩ : syracuseStep 250919 = 376379) B376379
theorem B250959 : Blo 247818 250959 := bstep (se 1 (by rfl) ⟨188219, by rfl⟩ : syracuseStep 250959 = 376439) B376439
theorem B250975 : Blo 247818 250975 := bstep (se 1 (by rfl) ⟨188231, by rfl⟩ : syracuseStep 250975 = 376463) B376463
theorem B251003 : Blo 247818 251003 := bstep (se 1 (by rfl) ⟨188252, by rfl⟩ : syracuseStep 251003 = 376505) B376505
theorem B251055 : Blo 247818 251055 := bstep (se 1 (by rfl) ⟨188291, by rfl⟩ : syracuseStep 251055 = 376583) B376583
theorem B251079 : Blo 247818 251079 := bstep (se 1 (by rfl) ⟨188309, by rfl⟩ : syracuseStep 251079 = 376619) B376619
theorem B251099 : Blo 247818 251099 := bstep (se 1 (by rfl) ⟨188324, by rfl⟩ : syracuseStep 251099 = 376649) B376649
theorem B251175 : Blo 247818 251175 := bstep (se 1 (by rfl) ⟨188381, by rfl⟩ : syracuseStep 251175 = 376763) B376763
theorem B251215 : Blo 247818 251215 := bstep (se 1 (by rfl) ⟨188411, by rfl⟩ : syracuseStep 251215 = 376823) B376823
theorem B251231 : Blo 247818 251231 := bstep (se 1 (by rfl) ⟨188423, by rfl⟩ : syracuseStep 251231 = 376847) B376847
theorem B251259 : Blo 247818 251259 := bstep (se 1 (by rfl) ⟨188444, by rfl⟩ : syracuseStep 251259 = 376889) B376889
theorem B15324551 : Blo 247818 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B841103 : Blo 247818 841103 := bstep (se 1 (by rfl) ⟨630827, by rfl⟩ : syracuseStep 841103 = 1261655) B1261655
theorem B251311 : Blo 247818 251311 := bstep (se 1 (by rfl) ⟨188483, by rfl⟩ : syracuseStep 251311 = 376967) B376967
theorem B251335 : Blo 247818 251335 := bstep (se 1 (by rfl) ⟨188501, by rfl⟩ : syracuseStep 251335 = 377003) B377003
theorem B3626441 : Blo 247818 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B1267163 : Blo 247818 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B251355 : Blo 247818 251355 := bstep (se 1 (by rfl) ⟨188516, by rfl⟩ : syracuseStep 251355 = 377033) B377033
theorem B906785 : Blo 247818 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B710183 : Blo 247818 710183 := bstep (se 1 (by rfl) ⟨532637, by rfl⟩ : syracuseStep 710183 = 1065275) B1065275
theorem B251431 : Blo 247818 251431 := bstep (se 1 (by rfl) ⟨188573, by rfl⟩ : syracuseStep 251431 = 377147) B377147
theorem B251471 : Blo 247818 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B251487 : Blo 247818 251487 := bstep (se 1 (by rfl) ⟨188615, by rfl⟩ : syracuseStep 251487 = 377231) B377231
theorem B251515 : Blo 247818 251515 := bstep (se 1 (by rfl) ⟨188636, by rfl⟩ : syracuseStep 251515 = 377273) B377273
theorem B251567 : Blo 247818 251567 := bstep (se 1 (by rfl) ⟨188675, by rfl⟩ : syracuseStep 251567 = 377351) B377351
theorem B251591 : Blo 247818 251591 := bstep (se 1 (by rfl) ⟨188693, by rfl⟩ : syracuseStep 251591 = 377387) B377387
theorem B841427 : Blo 247818 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B251611 : Blo 247818 251611 := bstep (se 1 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 251611 = 377417) B377417
theorem B448247 : Blo 247818 448247 := bstep (se 1 (by rfl) ⟨336185, by rfl⟩ : syracuseStep 448247 = 672371) B672371
theorem B251687 : Blo 247818 251687 := bstep (se 1 (by rfl) ⟨188765, by rfl⟩ : syracuseStep 251687 = 377531) B377531
theorem B251727 : Blo 247818 251727 := bstep (se 1 (by rfl) ⟨188795, by rfl⟩ : syracuseStep 251727 = 377591) B377591
theorem B1431391 : Blo 247818 1431391 := bstep (se 1 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 1431391 = 2147087) B2147087
theorem B251743 : Blo 247818 251743 := bstep (se 1 (by rfl) ⟨188807, by rfl⟩ : syracuseStep 251743 = 377615) B377615
theorem B251771 : Blo 247818 251771 := bstep (se 1 (by rfl) ⟨188828, by rfl⟩ : syracuseStep 251771 = 377657) B377657
theorem B1267649 : Blo 247818 1267649 := bstep (se 2 (by rfl) ⟨475368, by rfl⟩ : syracuseStep 1267649 = 950737) B950737
theorem B251867 : Blo 247818 251867 := bstep (se 1 (by rfl) ⟨188900, by rfl⟩ : syracuseStep 251867 = 377801) B377801
theorem B481609 : Blo 247818 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B1595963 : Blo 247818 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B3758669 : Blo 247818 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B481889 : Blo 247818 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B1071751 : Blo 247818 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1891025 : Blo 247818 1891025 := bstep (se 2 (by rfl) ⟨709134, by rfl⟩ : syracuseStep 1891025 = 1418269) B1418269
theorem B1432349 : Blo 247818 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B1006445 : Blo 247818 1006445 := bstep (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) B377417
theorem B842615 : Blo 247818 842615 := bstep (se 1 (by rfl) ⟨631961, by rfl⟩ : syracuseStep 842615 = 1263923) B1263923
theorem B449615 : Blo 247818 449615 := bstep (se 1 (by rfl) ⟨337211, by rfl⟩ : syracuseStep 449615 = 674423) B674423
theorem B842831 : Blo 247818 842831 := bstep (se 1 (by rfl) ⟨632123, by rfl⟩ : syracuseStep 842831 = 1264247) B1264247
theorem B1629377 : Blo 247818 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B843209 : Blo 247818 843209 := bstep (se 2 (by rfl) ⟨316203, by rfl⟩ : syracuseStep 843209 = 632407) B632407
theorem B1596989 : Blo 247818 1596989 := bstep (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) B598871
theorem B3858043 : Blo 247818 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B810643 : Blo 247818 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B941777 : Blo 247818 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B843479 : Blo 247818 843479 := bstep (se 1 (by rfl) ⟨632609, by rfl⟩ : syracuseStep 843479 = 1265219) B1265219
theorem B843695 : Blo 247818 843695 := bstep (se 1 (by rfl) ⟨632771, by rfl⟩ : syracuseStep 843695 = 1265543) B1265543
theorem B2285597 : Blo 247818 2285597 := bstep (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) B857099
theorem B1269917 : Blo 247818 1269917 := bstep (se 3 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 1269917 = 476219) B476219
theorem B942461 : Blo 247818 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B418223 : Blo 247818 418223 := bstep (se 1 (by rfl) ⟨313667, by rfl⟩ : syracuseStep 418223 = 627335) B627335
theorem B713225 : Blo 247818 713225 := bstep (se 2 (by rfl) ⟨267459, by rfl⟩ : syracuseStep 713225 = 534919) B534919
theorem B418655 : Blo 247818 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B1893455 : Blo 247818 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B2155673 : Blo 247818 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B943447 : Blo 247818 943447 := bstep (se 1 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 943447 = 1415171) B1415171
theorem B419215 : Blo 247818 419215 := bstep (se 1 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 419215 = 628823) B628823
theorem B1009039 : Blo 247818 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B1271213 : Blo 247818 1271213 := bstep (se 3 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 1271213 = 476705) B476705
theorem B1598939 : Blo 247818 1598939 := bstep (se 1 (by rfl) ⟨1199204, by rfl⟩ : syracuseStep 1598939 = 2398409) B2398409
theorem B943751 : Blo 247818 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B3860261 : Blo 247818 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B452513 : Blo 247818 452513 := bstep (se 2 (by rfl) ⟨169692, by rfl⟩ : syracuseStep 452513 = 339385) B339385
theorem B714683 : Blo 247818 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B419897 : Blo 247818 419897 := bstep (se 2 (by rfl) ⟨157461, by rfl⟩ : syracuseStep 419897 = 314923) B314923
theorem B944207 : Blo 247818 944207 := bstep (se 1 (by rfl) ⟨708155, by rfl⟩ : syracuseStep 944207 = 1416311) B1416311
theorem B1206353 : Blo 247818 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B1927397 : Blo 247818 1927397 := bstep (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) B361387
theorem B846071 : Blo 247818 846071 := bstep (se 1 (by rfl) ⟨634553, by rfl⟩ : syracuseStep 846071 = 1269107) B1269107
theorem B452959 : Blo 247818 452959 := bstep (se 1 (by rfl) ⟨339719, by rfl⟩ : syracuseStep 452959 = 679439) B679439
theorem B846395 : Blo 247818 846395 := bstep (se 1 (by rfl) ⟨634796, by rfl⟩ : syracuseStep 846395 = 1269593) B1269593
theorem B420599 : Blo 247818 420599 := bstep (se 1 (by rfl) ⟨315449, by rfl⟩ : syracuseStep 420599 = 630899) B630899
theorem B846665 : Blo 247818 846665 := bstep (se 2 (by rfl) ⟨317499, by rfl⟩ : syracuseStep 846665 = 634999) B634999
theorem B1272833 : Blo 247818 1272833 := bstep (se 2 (by rfl) ⟨477312, by rfl⟩ : syracuseStep 1272833 = 954625) B954625
theorem B1207315 : Blo 247818 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B945209 : Blo 247818 945209 := bstep (se 2 (by rfl) ⟨354453, by rfl⟩ : syracuseStep 945209 = 708907) B708907
theorem B420943 : Blo 247818 420943 := bstep (se 1 (by rfl) ⟨315707, by rfl⟩ : syracuseStep 420943 = 631415) B631415
theorem B421193 : Blo 247818 421193 := bstep (se 2 (by rfl) ⟨157947, by rfl⟩ : syracuseStep 421193 = 315895) B315895
theorem B945863 : Blo 247818 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B421625 : Blo 247818 421625 := bstep (se 2 (by rfl) ⟨158109, by rfl⟩ : syracuseStep 421625 = 316219) B316219
theorem B1273643 : Blo 247818 1273643 := bstep (se 1 (by rfl) ⟨955232, by rfl⟩ : syracuseStep 1273643 = 1910465) B1910465
theorem B6123413 : Blo 247818 6123413 := bstep (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) B287035
theorem B17592227 : Blo 247818 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B421807 : Blo 247818 421807 := bstep (se 1 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 421807 = 632711) B632711
theorem B847799 : Blo 247818 847799 := bstep (se 1 (by rfl) ⟨635849, by rfl⟩ : syracuseStep 847799 = 1271699) B1271699
theorem B421895 : Blo 247818 421895 := bstep (se 1 (by rfl) ⟨316421, by rfl⟩ : syracuseStep 421895 = 632843) B632843
theorem B1011959 : Blo 247818 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B422239 : Blo 247818 422239 := bstep (se 1 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 422239 = 633359) B633359
theorem B1896857 : Blo 247818 1896857 := bstep (se 2 (by rfl) ⟨711321, by rfl⟩ : syracuseStep 1896857 = 1422643) B1422643
theorem B422327 : Blo 247818 422327 := bstep (se 1 (by rfl) ⟨316745, by rfl⟩ : syracuseStep 422327 = 633491) B633491
theorem B848393 : Blo 247818 848393 := bstep (se 2 (by rfl) ⟨318147, by rfl⟩ : syracuseStep 848393 = 636295) B636295
theorem B946835 : Blo 247818 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B717511 : Blo 247818 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B1209161 : Blo 247818 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B422921 : Blo 247818 422921 := bstep (se 2 (by rfl) ⟨158595, by rfl⟩ : syracuseStep 422921 = 317191) B317191
theorem B423083 : Blo 247818 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B849257 : Blo 247818 849257 := bstep (se 2 (by rfl) ⟨318471, by rfl⟩ : syracuseStep 849257 = 636943) B636943
theorem B816509 : Blo 247818 816509 := bstep (se 3 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 816509 = 306191) B306191
theorem B1602989 : Blo 247818 1602989 := bstep (se 3 (by rfl) ⟨300560, by rfl⟩ : syracuseStep 1602989 = 601121) B601121
theorem B423481 : Blo 247818 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B1799819 : Blo 247818 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B423623 : Blo 247818 423623 := bstep (se 1 (by rfl) ⟨317717, by rfl⟩ : syracuseStep 423623 = 635435) B635435
theorem B9565937 : Blo 247818 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B3045215 : Blo 247818 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B423785 : Blo 247818 423785 := bstep (se 2 (by rfl) ⟨158919, by rfl⟩ : syracuseStep 423785 = 317839) B317839
theorem B849851 : Blo 247818 849851 := bstep (se 1 (by rfl) ⟨637388, by rfl⟩ : syracuseStep 849851 = 1274777) B1274777
theorem B424183 : Blo 247818 424183 := bstep (se 1 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 424183 = 636275) B636275
theorem B1898801 : Blo 247818 1898801 := bstep (se 2 (by rfl) ⟨712050, by rfl⟩ : syracuseStep 1898801 = 1424101) B1424101
theorem B424379 : Blo 247818 424379 := bstep (se 1 (by rfl) ⟨318284, by rfl⟩ : syracuseStep 424379 = 636569) B636569
theorem B424487 : Blo 247818 424487 := bstep (se 1 (by rfl) ⟨318365, by rfl⟩ : syracuseStep 424487 = 636731) B636731
theorem B719689 : Blo 247818 719689 := bstep (se 2 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 719689 = 539767) B539767
theorem B424777 : Blo 247818 424777 := bstep (se 2 (by rfl) ⟨159291, by rfl⟩ : syracuseStep 424777 = 318583) B318583
theorem B424811 : Blo 247818 424811 := bstep (se 1 (by rfl) ⟨318608, by rfl⟩ : syracuseStep 424811 = 637217) B637217
theorem B425321 : Blo 247818 425321 := bstep (se 2 (by rfl) ⟨159495, by rfl⟩ : syracuseStep 425321 = 318991) B318991
theorem B851705 : Blo 247818 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B1343699 : Blo 247818 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B557639 : Blo 247818 557639 := bstep (se 1 (by rfl) ⟨418229, by rfl⟩ : syracuseStep 557639 = 836459) B836459
theorem B557675 : Blo 247818 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B558071 : Blo 247818 558071 := bstep (se 1 (by rfl) ⟨418553, by rfl⟩ : syracuseStep 558071 = 837107) B837107
theorem B2851847 : Blo 247818 2851847 := bstep (se 1 (by rfl) ⟨2138885, by rfl⟩ : syracuseStep 2851847 = 4277771) B4277771
theorem B558431 : Blo 247818 558431 := bstep (se 1 (by rfl) ⟨418823, by rfl⟩ : syracuseStep 558431 = 837647) B837647
theorem B1607035 : Blo 247818 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B20514455 : Blo 247818 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B558827 : Blo 247818 558827 := bstep (se 1 (by rfl) ⟨419120, by rfl⟩ : syracuseStep 558827 = 838241) B838241
theorem B558953 : Blo 247818 558953 := bstep (se 2 (by rfl) ⟨209607, by rfl⟩ : syracuseStep 558953 = 419215) B419215
theorem B1345385 : Blo 247818 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B3606605 : Blo 247818 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B2722085 : Blo 247818 2722085 := bstep (se 4 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 2722085 = 510391) B510391
theorem B3017189 : Blo 247818 3017189 := bstep (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) B565723
theorem B2132567 : Blo 247818 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B4295267 : Blo 247818 4295267 := bstep (se 1 (by rfl) ⟨3221450, by rfl⟩ : syracuseStep 4295267 = 6442901) B6442901
theorem B559799 : Blo 247818 559799 := bstep (se 1 (by rfl) ⟨419849, by rfl⟩ : syracuseStep 559799 = 839699) B839699
theorem B1510109 : Blo 247818 1510109 := bstep (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) B566291
theorem B5442349 : Blo 247818 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B2394947 : Blo 247818 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B560015 : Blo 247818 560015 := bstep (se 1 (by rfl) ⟨420011, by rfl⟩ : syracuseStep 560015 = 840023) B840023
theorem B4787585 : Blo 247818 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B560735 : Blo 247818 560735 := bstep (se 1 (by rfl) ⟨420551, by rfl⟩ : syracuseStep 560735 = 841103) B841103
theorem B560951 : Blo 247818 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B298831 : Blo 247818 298831 := bstep (se 1 (by rfl) ⟨224123, by rfl⟩ : syracuseStep 298831 = 448247) B448247
theorem B3018653 : Blo 247818 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B1609753 : Blo 247818 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B561257 : Blo 247818 561257 := bstep (se 2 (by rfl) ⟨210471, by rfl⟩ : syracuseStep 561257 = 420943) B420943
theorem B954899 : Blo 247818 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B561743 : Blo 247818 561743 := bstep (se 1 (by rfl) ⟨421307, by rfl⟩ : syracuseStep 561743 = 842615) B842615
theorem B299743 : Blo 247818 299743 := bstep (se 1 (by rfl) ⟨224807, by rfl⟩ : syracuseStep 299743 = 449615) B449615
theorem B561887 : Blo 247818 561887 := bstep (se 1 (by rfl) ⟨421415, by rfl⟩ : syracuseStep 561887 = 842831) B842831
theorem B1086251 : Blo 247818 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B562139 : Blo 247818 562139 := bstep (se 1 (by rfl) ⟨421604, by rfl⟩ : syracuseStep 562139 = 843209) B843209
theorem B627851 : Blo 247818 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B562319 : Blo 247818 562319 := bstep (se 1 (by rfl) ⟨421739, by rfl⟩ : syracuseStep 562319 = 843479) B843479
theorem B759017 : Blo 247818 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B562409 : Blo 247818 562409 := bstep (se 2 (by rfl) ⟨210903, by rfl⟩ : syracuseStep 562409 = 421807) B421807
theorem B562463 : Blo 247818 562463 := bstep (se 1 (by rfl) ⟨421847, by rfl⟩ : syracuseStep 562463 = 843695) B843695
theorem B398729 : Blo 247818 398729 := bstep (se 2 (by rfl) ⟨149523, by rfl⟩ : syracuseStep 398729 = 299047) B299047
theorem B11474369 : Blo 247818 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B3216941 : Blo 247818 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B628307 : Blo 247818 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B562985 : Blo 247818 562985 := bstep (se 2 (by rfl) ⟨211119, by rfl⟩ : syracuseStep 562985 = 422239) B422239
theorem B956681 : Blo 247818 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B629167 : Blo 247818 629167 := bstep (se 1 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 629167 = 943751) B943751
theorem B530963 : Blo 247818 530963 := bstep (se 1 (by rfl) ⟨398222, by rfl⟩ : syracuseStep 530963 = 796445) B796445
theorem B629471 : Blo 247818 629471 := bstep (se 1 (by rfl) ⟨472103, by rfl⟩ : syracuseStep 629471 = 944207) B944207
theorem B1284931 : Blo 247818 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B564047 : Blo 247818 564047 := bstep (se 1 (by rfl) ⟨423035, by rfl⟩ : syracuseStep 564047 = 846071) B846071
theorem B564263 : Blo 247818 564263 := bstep (se 1 (by rfl) ⟨423197, by rfl⟩ : syracuseStep 564263 = 846395) B846395
theorem B564443 : Blo 247818 564443 := bstep (se 1 (by rfl) ⟨423332, by rfl⟩ : syracuseStep 564443 = 846665) B846665
theorem B1908035 : Blo 247818 1908035 := bstep (se 1 (by rfl) ⟨1431026, by rfl⟩ : syracuseStep 1908035 = 2862053) B2862053
theorem B630139 : Blo 247818 630139 := bstep (se 1 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 630139 = 945209) B945209
theorem B564641 : Blo 247818 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B1908521 : Blo 247818 1908521 := bstep (se 2 (by rfl) ⟨715695, by rfl⟩ : syracuseStep 1908521 = 1431391) B1431391
theorem B630575 : Blo 247818 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B565199 : Blo 247818 565199 := bstep (se 1 (by rfl) ⟨423899, by rfl⟩ : syracuseStep 565199 = 847799) B847799
theorem B565577 : Blo 247818 565577 := bstep (se 2 (by rfl) ⟨212091, by rfl⟩ : syracuseStep 565577 = 424183) B424183
theorem B565595 : Blo 247818 565595 := bstep (se 1 (by rfl) ⟨424196, by rfl⟩ : syracuseStep 565595 = 848393) B848393
theorem B631223 : Blo 247818 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B402041 : Blo 247818 402041 := bstep (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) B301531
theorem B566171 : Blo 247818 566171 := bstep (se 1 (by rfl) ⟨424628, by rfl⟩ : syracuseStep 566171 = 849257) B849257
theorem B3089335 : Blo 247818 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B959585 : Blo 247818 959585 := bstep (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) B719689
theorem B566369 : Blo 247818 566369 := bstep (se 2 (by rfl) ⟨212388, by rfl⟩ : syracuseStep 566369 = 424777) B424777
theorem B599179 : Blo 247818 599179 := bstep (se 1 (by rfl) ⟨449384, by rfl⟩ : syracuseStep 599179 = 898769) B898769
theorem B795881 : Blo 247818 795881 := bstep (se 2 (by rfl) ⟨298455, by rfl⟩ : syracuseStep 795881 = 596911) B596911
theorem B402727 : Blo 247818 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B566567 : Blo 247818 566567 := bstep (se 1 (by rfl) ⟨424925, by rfl⟩ : syracuseStep 566567 = 849851) B849851
theorem B632225 : Blo 247818 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B534073 : Blo 247818 534073 := bstep (se 2 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 534073 = 400555) B400555
theorem B632681 : Blo 247818 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B1255823 : Blo 247818 1255823 := bstep (se 1 (by rfl) ⟨941867, by rfl⟩ : syracuseStep 1255823 = 1883735) B1883735
theorem B797111 : Blo 247818 797111 := bstep (se 1 (by rfl) ⟨597833, by rfl⟩ : syracuseStep 797111 = 1195667) B1195667
theorem B567803 : Blo 247818 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B2566903 : Blo 247818 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B4795271 : Blo 247818 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1911923 : Blo 247818 1911923 := bstep (se 1 (by rfl) ⟨1433942, by rfl⟩ : syracuseStep 1911923 = 2867885) B2867885
theorem B1191131 : Blo 247818 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B371945 : Blo 247818 371945 := bstep (se 2 (by rfl) ⟨139479, by rfl⟩ : syracuseStep 371945 = 278959) B278959
theorem B371999 : Blo 247818 371999 := bstep (se 1 (by rfl) ⟨278999, by rfl⟩ : syracuseStep 371999 = 557999) B557999
theorem B1453373 : Blo 247818 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B1355075 : Blo 247818 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B372167 : Blo 247818 372167 := bstep (se 1 (by rfl) ⟨279125, by rfl⟩ : syracuseStep 372167 = 558251) B558251
theorem B470623 : Blo 247818 470623 := bstep (se 1 (by rfl) ⟨352967, by rfl⟩ : syracuseStep 470623 = 705935) B705935
theorem B634463 : Blo 247818 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B536225 : Blo 247818 536225 := bstep (se 2 (by rfl) ⟨201084, by rfl⟩ : syracuseStep 536225 = 402169) B402169
theorem B2272967 : Blo 247818 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B2141963 : Blo 247818 2141963 := bstep (se 1 (by rfl) ⟨1606472, by rfl⟩ : syracuseStep 2141963 = 3212945) B3212945
theorem B372521 : Blo 247818 372521 := bstep (se 2 (by rfl) ⟨139695, by rfl⟩ : syracuseStep 372521 = 279391) B279391
theorem B372527 : Blo 247818 372527 := bstep (se 1 (by rfl) ⟨279395, by rfl⟩ : syracuseStep 372527 = 558791) B558791
theorem B503759 : Blo 247818 503759 := bstep (se 1 (by rfl) ⟨377819, by rfl⟩ : syracuseStep 503759 = 755639) B755639
theorem B602063 : Blo 247818 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B373001 : Blo 247818 373001 := bstep (se 2 (by rfl) ⟨139875, by rfl⟩ : syracuseStep 373001 = 279751) B279751
theorem B635161 : Blo 247818 635161 := bstep (se 2 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 635161 = 476371) B476371
theorem B373103 : Blo 247818 373103 := bstep (se 1 (by rfl) ⟨279827, by rfl⟩ : syracuseStep 373103 = 559655) B559655
theorem B2568581 : Blo 247818 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B635303 : Blo 247818 635303 := bstep (se 1 (by rfl) ⟨476477, by rfl⟩ : syracuseStep 635303 = 952955) B952955
theorem B1257929 : Blo 247818 1257929 := bstep (se 2 (by rfl) ⟨471723, by rfl⟩ : syracuseStep 1257929 = 943447) B943447
theorem B373319 : Blo 247818 373319 := bstep (se 1 (by rfl) ⟨279989, by rfl⟩ : syracuseStep 373319 = 559979) B559979
theorem B799303 : Blo 247818 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B635465 : Blo 247818 635465 := bstep (se 2 (by rfl) ⟨238299, by rfl⟩ : syracuseStep 635465 = 476599) B476599
theorem B373355 : Blo 247818 373355 := bstep (se 1 (by rfl) ⟨280016, by rfl⟩ : syracuseStep 373355 = 560033) B560033
theorem B373583 : Blo 247818 373583 := bstep (se 1 (by rfl) ⟨280187, by rfl⟩ : syracuseStep 373583 = 560375) B560375
theorem B570359 : Blo 247818 570359 := bstep (se 1 (by rfl) ⟨427769, by rfl⟩ : syracuseStep 570359 = 855539) B855539
theorem B1422461 : Blo 247818 1422461 := bstep (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) B533423
theorem B373979 : Blo 247818 373979 := bstep (se 1 (by rfl) ⟨280484, by rfl⟩ : syracuseStep 373979 = 560969) B560969
theorem B1258739 : Blo 247818 1258739 := bstep (se 1 (by rfl) ⟨944054, by rfl⟩ : syracuseStep 1258739 = 1888109) B1888109
theorem B4273397 : Blo 247818 4273397 := bstep (se 5 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 4273397 = 400631) B400631
theorem B374153 : Blo 247818 374153 := bstep (se 2 (by rfl) ⟨140307, by rfl⟩ : syracuseStep 374153 = 280615) B280615
theorem B374507 : Blo 247818 374507 := bstep (se 1 (by rfl) ⟨280880, by rfl⟩ : syracuseStep 374507 = 561761) B561761
theorem B374735 : Blo 247818 374735 := bstep (se 1 (by rfl) ⟨281051, by rfl⟩ : syracuseStep 374735 = 562103) B562103
theorem B5880113 : Blo 247818 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B375131 : Blo 247818 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B604523 : Blo 247818 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B473455 : Blo 247818 473455 := bstep (se 1 (by rfl) ⟨355091, by rfl⟩ : syracuseStep 473455 = 710183) B710183
theorem B637409 : Blo 247818 637409 := bstep (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) B478057
theorem B375359 : Blo 247818 375359 := bstep (se 1 (by rfl) ⟨281519, by rfl⟩ : syracuseStep 375359 = 563039) B563039
theorem B801353 : Blo 247818 801353 := bstep (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) B601015
theorem B1882763 : Blo 247818 1882763 := bstep (se 1 (by rfl) ⟨1412072, by rfl⟩ : syracuseStep 1882763 = 2824145) B2824145
theorem B375479 : Blo 247818 375479 := bstep (se 1 (by rfl) ⟨281609, by rfl⟩ : syracuseStep 375479 = 563219) B563219
theorem B375707 : Blo 247818 375707 := bstep (se 1 (by rfl) ⟨281780, by rfl⟩ : syracuseStep 375707 = 563561) B563561
theorem B2505779 : Blo 247818 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1260683 : Blo 247818 1260683 := bstep (se 1 (by rfl) ⟨945512, by rfl⟩ : syracuseStep 1260683 = 1891025) B1891025
theorem B670963 : Blo 247818 670963 := bstep (se 1 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 670963 = 1006445) B1006445
theorem B376103 : Blo 247818 376103 := bstep (se 1 (by rfl) ⟨282077, by rfl⟩ : syracuseStep 376103 = 564155) B564155
theorem B376187 : Blo 247818 376187 := bstep (se 1 (by rfl) ⟨282140, by rfl⟩ : syracuseStep 376187 = 564281) B564281
theorem B376313 : Blo 247818 376313 := bstep (se 2 (by rfl) ⟨141117, by rfl⟩ : syracuseStep 376313 = 282235) B282235
theorem B2866747 : Blo 247818 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B376415 : Blo 247818 376415 := bstep (se 1 (by rfl) ⟨282311, by rfl⟩ : syracuseStep 376415 = 564623) B564623
theorem B1064659 : Blo 247818 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B376631 : Blo 247818 376631 := bstep (se 1 (by rfl) ⟨282473, by rfl⟩ : syracuseStep 376631 = 564947) B564947
theorem B671645 : Blo 247818 671645 := bstep (se 3 (by rfl) ⟨125933, by rfl⟩ : syracuseStep 671645 = 251867) B251867
theorem B1523731 : Blo 247818 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B376937 : Blo 247818 376937 := bstep (se 2 (by rfl) ⟨141351, by rfl⟩ : syracuseStep 376937 = 282703) B282703
theorem B278815 : Blo 247818 278815 := bstep (se 1 (by rfl) ⟨209111, by rfl⟩ : syracuseStep 278815 = 418223) B418223
theorem B475483 : Blo 247818 475483 := bstep (se 1 (by rfl) ⟨356612, by rfl⟩ : syracuseStep 475483 = 713225) B713225
theorem B377255 : Blo 247818 377255 := bstep (se 1 (by rfl) ⟨282941, by rfl⟩ : syracuseStep 377255 = 565883) B565883
theorem B377339 : Blo 247818 377339 := bstep (se 1 (by rfl) ⟨283004, by rfl⟩ : syracuseStep 377339 = 566009) B566009
theorem B279103 : Blo 247818 279103 := bstep (se 1 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 279103 = 418655) B418655
theorem B377465 : Blo 247818 377465 := bstep (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) B283099
theorem B377519 : Blo 247818 377519 := bstep (se 1 (by rfl) ⟨283139, by rfl⟩ : syracuseStep 377519 = 566279) B566279
theorem B1262303 : Blo 247818 1262303 := bstep (se 1 (by rfl) ⟨946727, by rfl⟩ : syracuseStep 1262303 = 1893455) B1893455
theorem B377567 : Blo 247818 377567 := bstep (se 1 (by rfl) ⟨283175, by rfl⟩ : syracuseStep 377567 = 566351) B566351
theorem B1065889 : Blo 247818 1065889 := bstep (se 2 (by rfl) ⟨399708, by rfl⟩ : syracuseStep 1065889 = 799417) B799417
theorem B1065959 : Blo 247818 1065959 := bstep (se 1 (by rfl) ⟨799469, by rfl⟩ : syracuseStep 1065959 = 1598939) B1598939
theorem B3654659 : Blo 247818 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B9684035 : Blo 247818 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B2573507 : Blo 247818 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B640199 : Blo 247818 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B476455 : Blo 247818 476455 := bstep (se 1 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 476455 = 714683) B714683
theorem B279931 : Blo 247818 279931 := bstep (se 1 (by rfl) ⟨209948, by rfl⟩ : syracuseStep 279931 = 419897) B419897
theorem B837053 : Blo 247818 837053 := bstep (se 3 (by rfl) ⟨156947, by rfl⟩ : syracuseStep 837053 = 313895) B313895
theorem B1590941 : Blo 247818 1590941 := bstep (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) B596603
theorem B837431 : Blo 247818 837431 := bstep (se 1 (by rfl) ⟨628073, by rfl⟩ : syracuseStep 837431 = 1256147) B1256147
theorem B280399 : Blo 247818 280399 := bstep (se 1 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 280399 = 420599) B420599
theorem B2607299 : Blo 247818 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B280795 : Blo 247818 280795 := bstep (se 1 (by rfl) ⟨210596, by rfl⟩ : syracuseStep 280795 = 421193) B421193
theorem B837917 : Blo 247818 837917 := bstep (se 3 (by rfl) ⟨157109, by rfl⟩ : syracuseStep 837917 = 314219) B314219
theorem B248095 : Blo 247818 248095 := bstep (se 1 (by rfl) ⟨186071, by rfl⟩ : syracuseStep 248095 = 372143) B372143
theorem B248155 : Blo 247818 248155 := bstep (se 1 (by rfl) ⟨186116, by rfl⟩ : syracuseStep 248155 = 372233) B372233
theorem B248175 : Blo 247818 248175 := bstep (se 1 (by rfl) ⟨186131, by rfl⟩ : syracuseStep 248175 = 372263) B372263
theorem B313723 : Blo 247818 313723 := bstep (se 1 (by rfl) ⟨235292, by rfl⟩ : syracuseStep 313723 = 470585) B470585
theorem B248231 : Blo 247818 248231 := bstep (se 1 (by rfl) ⟨186173, by rfl⟩ : syracuseStep 248231 = 372347) B372347
theorem B248315 : Blo 247818 248315 := bstep (se 1 (by rfl) ⟨186236, by rfl⟩ : syracuseStep 248315 = 372473) B372473
theorem B281083 : Blo 247818 281083 := bstep (se 1 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 281083 = 421625) B421625
theorem B248383 : Blo 247818 248383 := bstep (se 1 (by rfl) ⟨186287, by rfl⟩ : syracuseStep 248383 = 372575) B372575
theorem B248391 : Blo 247818 248391 := bstep (se 1 (by rfl) ⟨186293, by rfl⟩ : syracuseStep 248391 = 372587) B372587
theorem B313951 : Blo 247818 313951 := bstep (se 1 (by rfl) ⟨235463, by rfl⟩ : syracuseStep 313951 = 470927) B470927
theorem B4082275 : Blo 247818 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B281263 : Blo 247818 281263 := bstep (se 1 (by rfl) ⟨210947, by rfl⟩ : syracuseStep 281263 = 421895) B421895
theorem B248543 : Blo 247818 248543 := bstep (se 1 (by rfl) ⟨186407, by rfl⟩ : syracuseStep 248543 = 372815) B372815
theorem B248623 : Blo 247818 248623 := bstep (se 1 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 248623 = 372935) B372935
theorem B674639 : Blo 247818 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B248731 : Blo 247818 248731 := bstep (se 1 (by rfl) ⟨186548, by rfl⟩ : syracuseStep 248731 = 373097) B373097
theorem B2608043 : Blo 247818 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1264571 : Blo 247818 1264571 := bstep (se 1 (by rfl) ⟨948428, by rfl⟩ : syracuseStep 1264571 = 1896857) B1896857
theorem B248783 : Blo 247818 248783 := bstep (se 1 (by rfl) ⟨186587, by rfl⟩ : syracuseStep 248783 = 373175) B373175
theorem B281551 : Blo 247818 281551 := bstep (se 1 (by rfl) ⟨211163, by rfl⟩ : syracuseStep 281551 = 422327) B422327
theorem B248807 : Blo 247818 248807 := bstep (se 1 (by rfl) ⟨186605, by rfl⟩ : syracuseStep 248807 = 373211) B373211
theorem B707723 : Blo 247818 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B806107 : Blo 247818 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B838943 : Blo 247818 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B249119 : Blo 247818 249119 := bstep (se 1 (by rfl) ⟨186839, by rfl⟩ : syracuseStep 249119 = 373679) B373679
theorem B281947 : Blo 247818 281947 := bstep (se 1 (by rfl) ⟨211460, by rfl⟩ : syracuseStep 281947 = 422921) B422921
theorem B249179 : Blo 247818 249179 := bstep (se 1 (by rfl) ⟨186884, by rfl⟩ : syracuseStep 249179 = 373769) B373769
theorem B249199 : Blo 247818 249199 := bstep (se 1 (by rfl) ⟨186899, by rfl⟩ : syracuseStep 249199 = 373799) B373799
theorem B249255 : Blo 247818 249255 := bstep (se 1 (by rfl) ⟨186941, by rfl⟩ : syracuseStep 249255 = 373883) B373883
theorem B25873843 : Blo 247818 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B282055 : Blo 247818 282055 := bstep (se 1 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 282055 = 423083) B423083
theorem B2280923 : Blo 247818 2280923 := bstep (se 1 (by rfl) ⟨1710692, by rfl⟩ : syracuseStep 2280923 = 3421385) B3421385
theorem B249339 : Blo 247818 249339 := bstep (se 1 (by rfl) ⟨187004, by rfl⟩ : syracuseStep 249339 = 374009) B374009
theorem B1429001 : Blo 247818 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B249407 : Blo 247818 249407 := bstep (se 1 (by rfl) ⟨187055, by rfl⟩ : syracuseStep 249407 = 374111) B374111
theorem B249415 : Blo 247818 249415 := bstep (se 1 (by rfl) ⟨187061, by rfl⟩ : syracuseStep 249415 = 374123) B374123
theorem B544339 : Blo 247818 544339 := bstep (se 1 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 544339 = 816509) B816509
theorem B1068659 : Blo 247818 1068659 := bstep (se 1 (by rfl) ⟨801494, by rfl⟩ : syracuseStep 1068659 = 1602989) B1602989
theorem B249567 : Blo 247818 249567 := bstep (se 1 (by rfl) ⟨187175, by rfl⟩ : syracuseStep 249567 = 374351) B374351
theorem B1199879 : Blo 247818 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B16305953 : Blo 247818 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B249647 : Blo 247818 249647 := bstep (se 1 (by rfl) ⟨187235, by rfl⟩ : syracuseStep 249647 = 374471) B374471
theorem B282415 : Blo 247818 282415 := bstep (se 1 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 282415 = 423623) B423623
theorem B315191 : Blo 247818 315191 := bstep (se 1 (by rfl) ⟨236393, by rfl⟩ : syracuseStep 315191 = 472787) B472787
theorem B6377291 : Blo 247818 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B249755 : Blo 247818 249755 := bstep (se 1 (by rfl) ⟨187316, by rfl⟩ : syracuseStep 249755 = 374633) B374633
theorem B282523 : Blo 247818 282523 := bstep (se 1 (by rfl) ⟨211892, by rfl⟩ : syracuseStep 282523 = 423785) B423785
theorem B315343 : Blo 247818 315343 := bstep (se 1 (by rfl) ⟨236507, by rfl⟩ : syracuseStep 315343 = 473015) B473015
theorem B249807 : Blo 247818 249807 := bstep (se 1 (by rfl) ⟨187355, by rfl⟩ : syracuseStep 249807 = 374711) B374711
theorem B249831 : Blo 247818 249831 := bstep (se 1 (by rfl) ⟨187373, by rfl⟩ : syracuseStep 249831 = 374747) B374747
theorem B1265867 : Blo 247818 1265867 := bstep (se 1 (by rfl) ⟨949400, by rfl⟩ : syracuseStep 1265867 = 1898801) B1898801
theorem B250143 : Blo 247818 250143 := bstep (se 1 (by rfl) ⟨187607, by rfl⟩ : syracuseStep 250143 = 375215) B375215
theorem B282919 : Blo 247818 282919 := bstep (se 1 (by rfl) ⟨212189, by rfl⟩ : syracuseStep 282919 = 424379) B424379
theorem B250203 : Blo 247818 250203 := bstep (se 1 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 250203 = 375305) B375305
theorem B250223 : Blo 247818 250223 := bstep (se 1 (by rfl) ⟨187667, by rfl⟩ : syracuseStep 250223 = 375335) B375335
theorem B282991 : Blo 247818 282991 := bstep (se 1 (by rfl) ⟨212243, by rfl⟩ : syracuseStep 282991 = 424487) B424487
theorem B250279 : Blo 247818 250279 := bstep (se 1 (by rfl) ⟨187709, by rfl⟩ : syracuseStep 250279 = 375419) B375419
theorem B250363 : Blo 247818 250363 := bstep (se 1 (by rfl) ⟨187772, by rfl⟩ : syracuseStep 250363 = 375545) B375545
theorem B250431 : Blo 247818 250431 := bstep (se 1 (by rfl) ⟨187823, by rfl⟩ : syracuseStep 250431 = 375647) B375647
theorem B250439 : Blo 247818 250439 := bstep (se 1 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 250439 = 375659) B375659
theorem B283207 : Blo 247818 283207 := bstep (se 1 (by rfl) ⟨212405, by rfl⟩ : syracuseStep 283207 = 424811) B424811
theorem B250591 : Blo 247818 250591 := bstep (se 1 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 250591 = 375887) B375887
theorem B250671 : Blo 247818 250671 := bstep (se 1 (by rfl) ⟨188003, by rfl⟩ : syracuseStep 250671 = 376007) B376007
theorem B3199823 : Blo 247818 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B283547 : Blo 247818 283547 := bstep (se 1 (by rfl) ⟨212660, by rfl⟩ : syracuseStep 283547 = 425321) B425321
theorem B316315 : Blo 247818 316315 := bstep (se 1 (by rfl) ⟨237236, by rfl⟩ : syracuseStep 316315 = 474473) B474473
theorem B250779 : Blo 247818 250779 := bstep (se 1 (by rfl) ⟨188084, by rfl⟩ : syracuseStep 250779 = 376169) B376169
theorem B250831 : Blo 247818 250831 := bstep (se 1 (by rfl) ⟨188123, by rfl⟩ : syracuseStep 250831 = 376247) B376247
theorem B250855 : Blo 247818 250855 := bstep (se 1 (by rfl) ⟨188141, by rfl⟩ : syracuseStep 250855 = 376283) B376283
theorem B251167 : Blo 247818 251167 := bstep (se 1 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 251167 = 376751) B376751
theorem B251227 : Blo 247818 251227 := bstep (se 1 (by rfl) ⟨188420, by rfl⟩ : syracuseStep 251227 = 376841) B376841
theorem B251247 : Blo 247818 251247 := bstep (se 1 (by rfl) ⟨188435, by rfl⟩ : syracuseStep 251247 = 376871) B376871
theorem B251303 : Blo 247818 251303 := bstep (se 1 (by rfl) ⟨188477, by rfl⟩ : syracuseStep 251303 = 376955) B376955
theorem B2905537 : Blo 247818 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B251387 : Blo 247818 251387 := bstep (se 1 (by rfl) ⟨188540, by rfl⟩ : syracuseStep 251387 = 377081) B377081
theorem B251455 : Blo 247818 251455 := bstep (se 1 (by rfl) ⟨188591, by rfl⟩ : syracuseStep 251455 = 377183) B377183
theorem B251463 : Blo 247818 251463 := bstep (se 1 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 251463 = 377195) B377195
theorem B841373 : Blo 247818 841373 := bstep (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) B315515
theorem B251615 : Blo 247818 251615 := bstep (se 1 (by rfl) ⟨188711, by rfl⟩ : syracuseStep 251615 = 377423) B377423
theorem B251695 : Blo 247818 251695 := bstep (se 1 (by rfl) ⟨188771, by rfl⟩ : syracuseStep 251695 = 377543) B377543
theorem B251803 : Blo 247818 251803 := bstep (se 1 (by rfl) ⟨188852, by rfl⟩ : syracuseStep 251803 = 377705) B377705
theorem B1791973 : Blo 247818 1791973 := bstep (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) B335995
theorem B841913 : Blo 247818 841913 := bstep (se 2 (by rfl) ⟨315717, by rfl⟩ : syracuseStep 841913 = 631435) B631435
theorem B448859 : Blo 247818 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B1268135 : Blo 247818 1268135 := bstep (se 1 (by rfl) ⟨951101, by rfl⟩ : syracuseStep 1268135 = 1902203) B1902203
theorem B2415167 : Blo 247818 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B1268297 : Blo 247818 1268297 := bstep (se 2 (by rfl) ⟨475611, by rfl⟩ : syracuseStep 1268297 = 951223) B951223
theorem B1203011 : Blo 247818 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B711595 : Blo 247818 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B2415781 : Blo 247818 2415781 := bstep (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) B452959
theorem B843425 : Blo 247818 843425 := bstep (se 2 (by rfl) ⟨316284, by rfl⟩ : syracuseStep 843425 = 632569) B632569
theorem B4317299 : Blo 247818 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B4645181 : Blo 247818 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B39739747 : Blo 247818 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B1270241 : Blo 247818 1270241 := bstep (se 2 (by rfl) ⟨476340, by rfl⟩ : syracuseStep 1270241 = 952681) B952681
theorem B844289 : Blo 247818 844289 := bstep (se 2 (by rfl) ⟨316608, by rfl⟩ : syracuseStep 844289 = 633217) B633217
theorem B1794743 : Blo 247818 1794743 := bstep (se 1 (by rfl) ⟨1346057, by rfl⟩ : syracuseStep 1794743 = 2692115) B2692115
theorem B2384801 : Blo 247818 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B10216367 : Blo 247818 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B2417627 : Blo 247818 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B844775 : Blo 247818 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B845099 : Blo 247818 845099 := bstep (se 1 (by rfl) ⟨633824, by rfl⟩ : syracuseStep 845099 = 1267649) B1267649
theorem B419195 : Blo 247818 419195 := bstep (se 1 (by rfl) ⟨314396, by rfl⟩ : syracuseStep 419195 = 628793) B628793
theorem B845369 : Blo 247818 845369 := bstep (se 2 (by rfl) ⟨317013, by rfl⟩ : syracuseStep 845369 = 634027) B634027
theorem B321259 : Blo 247818 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B354089 : Blo 247818 354089 := bstep (se 2 (by rfl) ⟨132783, by rfl⟩ : syracuseStep 354089 = 265567) B265567
theorem B1206199 : Blo 247818 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B8120573 : Blo 247818 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B420187 : Blo 247818 420187 := bstep (se 1 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 420187 = 630281) B630281
theorem B354727 : Blo 247818 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B1206701 : Blo 247818 1206701 := bstep (se 3 (by rfl) ⟨226256, by rfl⟩ : syracuseStep 1206701 = 452513) B452513
theorem B1272509 : Blo 247818 1272509 := bstep (se 3 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 1272509 = 477191) B477191
theorem B846611 : Blo 247818 846611 := bstep (se 1 (by rfl) ⟨634958, by rfl⟩ : syracuseStep 846611 = 1269917) B1269917
theorem B355547 : Blo 247818 355547 := bstep (se 1 (by rfl) ⟨266660, by rfl⟩ : syracuseStep 355547 = 533321) B533321
theorem B421159 : Blo 247818 421159 := bstep (se 1 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 421159 = 631739) B631739
theorem B1437115 : Blo 247818 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B1207817 : Blo 247818 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B847475 : Blo 247818 847475 := bstep (se 1 (by rfl) ⟨635606, by rfl⟩ : syracuseStep 847475 = 1271213) B1271213
theorem B421679 : Blo 247818 421679 := bstep (se 1 (by rfl) ⟨316259, by rfl⟩ : syracuseStep 421679 = 632519) B632519
theorem B847745 : Blo 247818 847745 := bstep (se 2 (by rfl) ⟨317904, by rfl⟩ : syracuseStep 847745 = 635809) B635809
theorem B1601603 : Blo 247818 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B4255901 : Blo 247818 4255901 := bstep (se 3 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 4255901 = 1595963) B1595963
theorem B848555 : Blo 247818 848555 := bstep (se 1 (by rfl) ⟨636416, by rfl⟩ : syracuseStep 848555 = 1272833) B1272833
theorem B1340239 : Blo 247818 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B422887 : Blo 247818 422887 := bstep (se 1 (by rfl) ⟨317165, by rfl⟩ : syracuseStep 422887 = 634331) B634331
theorem B3634301 : Blo 247818 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B1078397 : Blo 247818 1078397 := bstep (se 3 (by rfl) ⟨202199, by rfl⟩ : syracuseStep 1078397 = 404399) B404399
theorem B849095 : Blo 247818 849095 := bstep (se 1 (by rfl) ⟨636821, by rfl⟩ : syracuseStep 849095 = 1273643) B1273643
theorem B718073 : Blo 247818 718073 := bstep (se 2 (by rfl) ⟨269277, by rfl⟩ : syracuseStep 718073 = 538555) B538555
theorem B11728151 : Blo 247818 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B4290893 : Blo 247818 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B7731845 : Blo 247818 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B5144057 : Blo 247818 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B1080857 : Blo 247818 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B3604297 : Blo 247818 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B2031641 : Blo 247818 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B52986329 : Blo 247818 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B1901231 : Blo 247818 1901231 := bstep (se 1 (by rfl) ⟨1425923, by rfl⟩ : syracuseStep 1901231 = 2851847) B2851847
theorem B6456023 : Blo 247818 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B426799 : Blo 247818 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B558035 : Blo 247818 558035 := bstep (se 1 (by rfl) ⟨418526, by rfl⟩ : syracuseStep 558035 = 837053) B837053
theorem B558287 : Blo 247818 558287 := bstep (se 1 (by rfl) ⟨418715, by rfl⟩ : syracuseStep 558287 = 837431) B837431
theorem B1738199 : Blo 247818 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B558611 : Blo 247818 558611 := bstep (se 1 (by rfl) ⟨418958, by rfl⟩ : syracuseStep 558611 = 837917) B837917
theorem B559295 : Blo 247818 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B428345 : Blo 247818 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B952667 : Blo 247818 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B756125 : Blo 247818 756125 := bstep (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) B283547
theorem B1608265 : Blo 247818 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B2558893 : Blo 247818 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B560249 : Blo 247818 560249 := bstep (se 2 (by rfl) ⟨210093, by rfl⟩ : syracuseStep 560249 = 420187) B420187
theorem B2133215 : Blo 247818 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B5443033 : Blo 247818 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B560915 : Blo 247818 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B561275 : Blo 247818 561275 := bstep (se 1 (by rfl) ⟨420956, by rfl⟩ : syracuseStep 561275 = 841913) B841913
theorem B1610111 : Blo 247818 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B561545 : Blo 247818 561545 := bstep (se 2 (by rfl) ⟨210579, by rfl⟩ : syracuseStep 561545 = 421159) B421159
theorem B725785 : Blo 247818 725785 := bstep (se 2 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 725785 = 544339) B544339
theorem B627497 : Blo 247818 627497 := bstep (se 2 (by rfl) ⟨235311, by rfl⟩ : syracuseStep 627497 = 470623) B470623
theorem B398441 : Blo 247818 398441 := bstep (se 2 (by rfl) ⟨149415, by rfl⟩ : syracuseStep 398441 = 298831) B298831
theorem B562283 : Blo 247818 562283 := bstep (se 1 (by rfl) ⟨421712, by rfl⟩ : syracuseStep 562283 = 843425) B843425
theorem B562859 : Blo 247818 562859 := bstep (se 1 (by rfl) ⟨422144, by rfl⟩ : syracuseStep 562859 = 844289) B844289
theorem B1611751 : Blo 247818 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B563183 : Blo 247818 563183 := bstep (se 1 (by rfl) ⟨422387, by rfl⟩ : syracuseStep 563183 = 844775) B844775
theorem B530587 : Blo 247818 530587 := bstep (se 1 (by rfl) ⟨397940, by rfl⟩ : syracuseStep 530587 = 795881) B795881
theorem B563399 : Blo 247818 563399 := bstep (se 1 (by rfl) ⟨422549, by rfl⟩ : syracuseStep 563399 = 845099) B845099
theorem B1612061 : Blo 247818 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B563579 : Blo 247818 563579 := bstep (se 1 (by rfl) ⟨422684, by rfl⟩ : syracuseStep 563579 = 845369) B845369
theorem B563849 : Blo 247818 563849 := bstep (se 2 (by rfl) ⟨211443, by rfl⟩ : syracuseStep 563849 = 422887) B422887
theorem B1514141 : Blo 247818 1514141 := bstep (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) B567803
theorem B5413715 : Blo 247818 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B2136941 : Blo 247818 2136941 := bstep (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) B801353
theorem B531407 : Blo 247818 531407 := bstep (se 1 (by rfl) ⟨398555, by rfl⟩ : syracuseStep 531407 = 797111) B797111
theorem B564407 : Blo 247818 564407 := bstep (se 1 (by rfl) ⟨423305, by rfl⟩ : syracuseStep 564407 = 846611) B846611
theorem B3874049 : Blo 247818 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B794087 : Blo 247818 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B564983 : Blo 247818 564983 := bstep (se 1 (by rfl) ⟨423737, by rfl⟩ : syracuseStep 564983 = 847475) B847475
theorem B6954781 : Blo 247818 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B1515311 : Blo 247818 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B565163 : Blo 247818 565163 := bstep (se 1 (by rfl) ⟨423872, by rfl⟩ : syracuseStep 565163 = 847745) B847745
theorem B335839 : Blo 247818 335839 := bstep (se 1 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 335839 = 503759) B503759
theorem B401375 : Blo 247818 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B1712387 : Blo 247818 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B565703 : Blo 247818 565703 := bstep (se 1 (by rfl) ⟨424277, by rfl⟩ : syracuseStep 565703 = 848555) B848555
theorem B631273 : Blo 247818 631273 := bstep (se 2 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 631273 = 473455) B473455
theorem B566063 : Blo 247818 566063 := bstep (se 1 (by rfl) ⟨424547, by rfl⟩ : syracuseStep 566063 = 849095) B849095
theorem B1713241 : Blo 247818 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B3221041 : Blo 247818 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B2860595 : Blo 247818 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B894617 : Blo 247818 894617 := bstep (se 2 (by rfl) ⟨335481, by rfl⟩ : syracuseStep 894617 = 670963) B670963
theorem B5154563 : Blo 247818 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B1255175 : Blo 247818 1255175 := bstep (se 1 (by rfl) ⟨941381, by rfl⟩ : syracuseStep 1255175 = 1882763) B1882763
theorem B1419545 : Blo 247818 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B895799 : Blo 247818 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B371753 : Blo 247818 371753 := bstep (se 2 (by rfl) ⟨139407, by rfl⟩ : syracuseStep 371753 = 278815) B278815
theorem B371759 : Blo 247818 371759 := bstep (se 1 (by rfl) ⟨278819, by rfl⟩ : syracuseStep 371759 = 557639) B557639
theorem B371783 : Blo 247818 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B633977 : Blo 247818 633977 := bstep (se 2 (by rfl) ⟨237741, by rfl⟩ : syracuseStep 633977 = 475483) B475483
theorem B372047 : Blo 247818 372047 := bstep (se 1 (by rfl) ⟨279035, by rfl⟩ : syracuseStep 372047 = 558071) B558071
theorem B2436439 : Blo 247818 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B372137 : Blo 247818 372137 := bstep (se 2 (by rfl) ⟨139551, by rfl⟩ : syracuseStep 372137 = 279103) B279103
theorem B1715671 : Blo 247818 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B372287 : Blo 247818 372287 := bstep (se 1 (by rfl) ⟨279215, by rfl⟩ : syracuseStep 372287 = 558431) B558431
theorem B13676303 : Blo 247818 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B1060627 : Blo 247818 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B372551 : Blo 247818 372551 := bstep (se 1 (by rfl) ⟨279413, by rfl⟩ : syracuseStep 372551 = 558827) B558827
theorem B1421185 : Blo 247818 1421185 := bstep (se 2 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 1421185 = 1065889) B1065889
theorem B372635 : Blo 247818 372635 := bstep (se 1 (by rfl) ⟨279476, by rfl⟩ : syracuseStep 372635 = 558953) B558953
theorem B896923 : Blo 247818 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B2404403 : Blo 247818 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B798905 : Blo 247818 798905 := bstep (se 2 (by rfl) ⟨299589, by rfl⟩ : syracuseStep 798905 = 599179) B599179
theorem B1814723 : Blo 247818 1814723 := bstep (se 1 (by rfl) ⟨1361042, by rfl⟩ : syracuseStep 1814723 = 2722085) B2722085
theorem B635273 : Blo 247818 635273 := bstep (se 2 (by rfl) ⟨238227, by rfl⟩ : syracuseStep 635273 = 476455) B476455
theorem B536969 : Blo 247818 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B1421711 : Blo 247818 1421711 := bstep (se 1 (by rfl) ⟨1066283, by rfl⟩ : syracuseStep 1421711 = 2132567) B2132567
theorem B2863511 : Blo 247818 2863511 := bstep (se 1 (by rfl) ⟨2147633, by rfl⟩ : syracuseStep 2863511 = 4295267) B4295267
theorem B373199 : Blo 247818 373199 := bstep (se 1 (by rfl) ⟨279899, by rfl⟩ : syracuseStep 373199 = 559799) B559799
theorem B373241 : Blo 247818 373241 := bstep (se 2 (by rfl) ⟨139965, by rfl⟩ : syracuseStep 373241 = 279931) B279931
theorem B2142713 : Blo 247818 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B373343 : Blo 247818 373343 := bstep (se 1 (by rfl) ⟨280007, by rfl⟩ : syracuseStep 373343 = 560015) B560015
theorem B471815 : Blo 247818 471815 := bstep (se 1 (by rfl) ⟨353861, by rfl⟩ : syracuseStep 471815 = 707723) B707723
theorem B2896669 : Blo 247818 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B3191723 : Blo 247818 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B1520615 : Blo 247818 1520615 := bstep (se 1 (by rfl) ⟨1140461, by rfl⟩ : syracuseStep 1520615 = 2280923) B2280923
theorem B373823 : Blo 247818 373823 := bstep (se 1 (by rfl) ⟨280367, by rfl⟩ : syracuseStep 373823 = 560735) B560735
theorem B373865 : Blo 247818 373865 := bstep (se 2 (by rfl) ⟨140199, by rfl⟩ : syracuseStep 373865 = 280399) B280399
theorem B799919 : Blo 247818 799919 := bstep (se 1 (by rfl) ⟨599939, by rfl⟩ : syracuseStep 799919 = 1199879) B1199879
theorem B373967 : Blo 247818 373967 := bstep (se 1 (by rfl) ⟨280475, by rfl⟩ : syracuseStep 373967 = 560951) B560951
theorem B2012435 : Blo 247818 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B1520957 : Blo 247818 1520957 := bstep (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) B570359
theorem B374171 : Blo 247818 374171 := bstep (se 1 (by rfl) ⟨280628, by rfl⟩ : syracuseStep 374171 = 561257) B561257
theorem B374393 : Blo 247818 374393 := bstep (se 2 (by rfl) ⟨140397, by rfl⟩ : syracuseStep 374393 = 280795) B280795
theorem B636599 : Blo 247818 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B374495 : Blo 247818 374495 := bstep (se 1 (by rfl) ⟨280871, by rfl⟩ : syracuseStep 374495 = 561743) B561743
theorem B374591 : Blo 247818 374591 := bstep (se 1 (by rfl) ⟨280943, by rfl⟩ : syracuseStep 374591 = 561887) B561887
theorem B472969 : Blo 247818 472969 := bstep (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) B354727
theorem B374759 : Blo 247818 374759 := bstep (se 1 (by rfl) ⟨281069, by rfl⟩ : syracuseStep 374759 = 562139) B562139
theorem B374777 : Blo 247818 374777 := bstep (se 2 (by rfl) ⟨140541, by rfl⟩ : syracuseStep 374777 = 281083) B281083
theorem B374879 : Blo 247818 374879 := bstep (se 1 (by rfl) ⟨281159, by rfl⟩ : syracuseStep 374879 = 562319) B562319
theorem B506011 : Blo 247818 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B374939 : Blo 247818 374939 := bstep (se 1 (by rfl) ⟨281204, by rfl⟩ : syracuseStep 374939 = 562409) B562409
theorem B374975 : Blo 247818 374975 := bstep (se 1 (by rfl) ⟨281231, by rfl⟩ : syracuseStep 374975 = 562463) B562463
theorem B375017 : Blo 247818 375017 := bstep (se 2 (by rfl) ⟨140631, by rfl⟩ : syracuseStep 375017 = 281263) B281263
theorem B7649579 : Blo 247818 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B3422537 : Blo 247818 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B1063277 : Blo 247818 1063277 := bstep (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) B398729
theorem B2144627 : Blo 247818 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B7256465 : Blo 247818 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B670141 : Blo 247818 670141 := bstep (se 3 (by rfl) ⟨125651, by rfl⟩ : syracuseStep 670141 = 251303) B251303
theorem B375323 : Blo 247818 375323 := bstep (se 1 (by rfl) ⟨281492, by rfl⟩ : syracuseStep 375323 = 562985) B562985
theorem B375401 : Blo 247818 375401 := bstep (se 2 (by rfl) ⟨140775, by rfl⟩ : syracuseStep 375401 = 281551) B281551
theorem B637787 : Blo 247818 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B375929 : Blo 247818 375929 := bstep (se 2 (by rfl) ⟨140973, by rfl⟩ : syracuseStep 375929 = 281947) B281947
theorem B802007 : Blo 247818 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B376031 : Blo 247818 376031 := bstep (se 1 (by rfl) ⟨282023, by rfl⟩ : syracuseStep 376031 = 564047) B564047
theorem B1916153 : Blo 247818 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B376073 : Blo 247818 376073 := bstep (se 2 (by rfl) ⟨141027, by rfl⟩ : syracuseStep 376073 = 282055) B282055
theorem B376175 : Blo 247818 376175 := bstep (se 1 (by rfl) ⟨282131, by rfl⟩ : syracuseStep 376175 = 564263) B564263
theorem B376295 : Blo 247818 376295 := bstep (se 1 (by rfl) ⟨282221, by rfl⟩ : syracuseStep 376295 = 564443) B564443
theorem B376427 : Blo 247818 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B376553 : Blo 247818 376553 := bstep (se 2 (by rfl) ⟨141207, by rfl⟩ : syracuseStep 376553 = 282415) B282415
theorem B376697 : Blo 247818 376697 := bstep (se 2 (by rfl) ⟨141261, by rfl⟩ : syracuseStep 376697 = 282523) B282523
theorem B376799 : Blo 247818 376799 := bstep (se 1 (by rfl) ⟨282599, by rfl⟩ : syracuseStep 376799 = 565199) B565199
theorem B2146337 : Blo 247818 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B3096787 : Blo 247818 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B377051 : Blo 247818 377051 := bstep (se 1 (by rfl) ⟨282788, by rfl⟩ : syracuseStep 377051 = 565577) B565577
theorem B377063 : Blo 247818 377063 := bstep (se 1 (by rfl) ⟨282797, by rfl⟩ : syracuseStep 377063 = 565595) B565595
theorem B377225 : Blo 247818 377225 := bstep (se 2 (by rfl) ⟨141459, by rfl⟩ : syracuseStep 377225 = 282919) B282919
theorem B1196495 : Blo 247818 1196495 := bstep (se 1 (by rfl) ⟨897371, by rfl⟩ : syracuseStep 1196495 = 1794743) B1794743
theorem B377321 : Blo 247818 377321 := bstep (se 2 (by rfl) ⟨141495, by rfl⟩ : syracuseStep 377321 = 282991) B282991
theorem B377447 : Blo 247818 377447 := bstep (se 1 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 377447 = 566171) B566171
theorem B1589867 : Blo 247818 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B377579 : Blo 247818 377579 := bstep (se 1 (by rfl) ⟨283184, by rfl⟩ : syracuseStep 377579 = 566369) B566369
theorem B1065737 : Blo 247818 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B377609 : Blo 247818 377609 := bstep (se 2 (by rfl) ⟨141603, by rfl⟩ : syracuseStep 377609 = 283207) B283207
theorem B377711 : Blo 247818 377711 := bstep (se 1 (by rfl) ⟨283283, by rfl⟩ : syracuseStep 377711 = 566567) B566567
theorem B1196957 : Blo 247818 1196957 := bstep (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) B448859
theorem B279463 : Blo 247818 279463 := bstep (se 1 (by rfl) ⟨209597, by rfl⟩ : syracuseStep 279463 = 419195) B419195
theorem B1786985 : Blo 247818 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B8045837 : Blo 247818 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B837215 : Blo 247818 837215 := bstep (se 1 (by rfl) ⟨627911, by rfl⟩ : syracuseStep 837215 = 1255823) B1255823
theorem B804467 : Blo 247818 804467 := bstep (se 1 (by rfl) ⟨603350, by rfl⟩ : syracuseStep 804467 = 1206701) B1206701
theorem B3196847 : Blo 247818 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B247963 : Blo 247818 247963 := bstep (se 1 (by rfl) ⟨185972, by rfl⟩ : syracuseStep 247963 = 371945) B371945
theorem B247999 : Blo 247818 247999 := bstep (se 1 (by rfl) ⟨185999, by rfl⟩ : syracuseStep 247999 = 371999) B371999
theorem B968915 : Blo 247818 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B903383 : Blo 247818 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B248111 : Blo 247818 248111 := bstep (se 1 (by rfl) ⟨186083, by rfl⟩ : syracuseStep 248111 = 372167) B372167
theorem B805211 : Blo 247818 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B1427975 : Blo 247818 1427975 := bstep (se 1 (by rfl) ⟨1070981, by rfl⟩ : syracuseStep 1427975 = 2141963) B2141963
theorem B248347 : Blo 247818 248347 := bstep (se 1 (by rfl) ⟨186260, by rfl⟩ : syracuseStep 248347 = 372521) B372521
theorem B248351 : Blo 247818 248351 := bstep (se 1 (by rfl) ⟨186263, by rfl⟩ : syracuseStep 248351 = 372527) B372527
theorem B281119 : Blo 247818 281119 := bstep (se 1 (by rfl) ⟨210839, by rfl⟩ : syracuseStep 281119 = 421679) B421679
theorem B1067735 : Blo 247818 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B2837267 : Blo 247818 2837267 := bstep (se 1 (by rfl) ⟨2127950, by rfl⟩ : syracuseStep 2837267 = 4255901) B4255901
theorem B248667 : Blo 247818 248667 := bstep (se 1 (by rfl) ⟨186500, by rfl⟩ : syracuseStep 248667 = 373001) B373001
theorem B248735 : Blo 247818 248735 := bstep (se 1 (by rfl) ⟨186551, by rfl⟩ : syracuseStep 248735 = 373103) B373103
theorem B838619 : Blo 247818 838619 := bstep (se 1 (by rfl) ⟨628964, by rfl⟩ : syracuseStep 838619 = 1257929) B1257929
theorem B248879 : Blo 247818 248879 := bstep (se 1 (by rfl) ⟨186659, by rfl⟩ : syracuseStep 248879 = 373319) B373319
theorem B248903 : Blo 247818 248903 := bstep (se 1 (by rfl) ⟨186677, by rfl⟩ : syracuseStep 248903 = 373355) B373355
theorem B249055 : Blo 247818 249055 := bstep (se 1 (by rfl) ⟨186791, by rfl⟩ : syracuseStep 249055 = 373583) B373583
theorem B838889 : Blo 247818 838889 := bstep (se 2 (by rfl) ⟨314583, by rfl⟩ : syracuseStep 838889 = 629167) B629167
theorem B249319 : Blo 247818 249319 := bstep (se 1 (by rfl) ⟨186989, by rfl⟩ : syracuseStep 249319 = 373979) B373979
theorem B839159 : Blo 247818 839159 := bstep (se 1 (by rfl) ⟨629369, by rfl⟩ : syracuseStep 839159 = 1258739) B1258739
theorem B478715 : Blo 247818 478715 := bstep (se 1 (by rfl) ⟨359036, by rfl⟩ : syracuseStep 478715 = 718073) B718073
theorem B7818767 : Blo 247818 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B249435 : Blo 247818 249435 := bstep (se 1 (by rfl) ⟨187076, by rfl⟩ : syracuseStep 249435 = 374153) B374153
theorem B249671 : Blo 247818 249671 := bstep (se 1 (by rfl) ⟨187253, by rfl⟩ : syracuseStep 249671 = 374507) B374507
theorem B249823 : Blo 247818 249823 := bstep (se 1 (by rfl) ⟨187367, by rfl⟩ : syracuseStep 249823 = 374735) B374735
theorem B3920075 : Blo 247818 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B250087 : Blo 247818 250087 := bstep (se 1 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 250087 = 375131) B375131
theorem B250239 : Blo 247818 250239 := bstep (se 1 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 250239 = 375359) B375359
theorem B1429933 : Blo 247818 1429933 := bstep (se 3 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 1429933 = 536225) B536225
theorem B250319 : Blo 247818 250319 := bstep (se 1 (by rfl) ⟨187739, by rfl⟩ : syracuseStep 250319 = 375479) B375479
theorem B840185 : Blo 247818 840185 := bstep (se 2 (by rfl) ⟨315069, by rfl⟩ : syracuseStep 840185 = 630139) B630139
theorem B250471 : Blo 247818 250471 := bstep (se 1 (by rfl) ⟨187853, by rfl⟩ : syracuseStep 250471 = 375707) B375707
theorem B3822329 : Blo 247818 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B840455 : Blo 247818 840455 := bstep (se 1 (by rfl) ⟨630341, by rfl⟩ : syracuseStep 840455 = 1260683) B1260683
theorem B840509 : Blo 247818 840509 := bstep (se 3 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 840509 = 315191) B315191
theorem B250735 : Blo 247818 250735 := bstep (se 1 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 250735 = 376103) B376103
theorem B250791 : Blo 247818 250791 := bstep (se 1 (by rfl) ⟨188093, by rfl⟩ : syracuseStep 250791 = 376187) B376187
theorem B3429371 : Blo 247818 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B250875 : Blo 247818 250875 := bstep (se 1 (by rfl) ⟨188156, by rfl⟩ : syracuseStep 250875 = 376313) B376313
theorem B250943 : Blo 247818 250943 := bstep (se 1 (by rfl) ⟨188207, by rfl⟩ : syracuseStep 250943 = 376415) B376415
theorem B4805729 : Blo 247818 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B251087 : Blo 247818 251087 := bstep (se 1 (by rfl) ⟨188315, by rfl⟩ : syracuseStep 251087 = 376631) B376631
theorem B447763 : Blo 247818 447763 := bstep (se 1 (by rfl) ⟨335822, by rfl⟩ : syracuseStep 447763 = 671645) B671645
theorem B251291 : Blo 247818 251291 := bstep (se 1 (by rfl) ⟨188468, by rfl⟩ : syracuseStep 251291 = 376937) B376937
theorem B251503 : Blo 247818 251503 := bstep (se 1 (by rfl) ⟨188627, by rfl⟩ : syracuseStep 251503 = 377255) B377255
theorem B251559 : Blo 247818 251559 := bstep (se 1 (by rfl) ⟨188669, by rfl⟩ : syracuseStep 251559 = 377339) B377339
theorem B251643 : Blo 247818 251643 := bstep (se 1 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 251643 = 377465) B377465
theorem B251679 : Blo 247818 251679 := bstep (se 1 (by rfl) ⟨188759, by rfl⟩ : syracuseStep 251679 = 377519) B377519
theorem B841535 : Blo 247818 841535 := bstep (se 1 (by rfl) ⟨631151, by rfl⟩ : syracuseStep 841535 = 1262303) B1262303
theorem B251711 : Blo 247818 251711 := bstep (se 1 (by rfl) ⟨188783, by rfl⟩ : syracuseStep 251711 = 377567) B377567
theorem B710639 : Blo 247818 710639 := bstep (se 1 (by rfl) ⟨532979, by rfl⟩ : syracuseStep 710639 = 1065959) B1065959
theorem B4119113 : Blo 247818 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1006573 : Blo 247818 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B1072109 : Blo 247818 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B1006739 : Blo 247818 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B1596631 : Blo 247818 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B449759 : Blo 247818 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B843047 : Blo 247818 843047 := bstep (se 1 (by rfl) ⟨632285, by rfl⟩ : syracuseStep 843047 = 1264571) B1264571
theorem B712097 : Blo 247818 712097 := bstep (se 2 (by rfl) ⟨267036, by rfl⟩ : syracuseStep 712097 = 534073) B534073
theorem B712439 : Blo 247818 712439 := bstep (se 1 (by rfl) ⟨534329, by rfl⟩ : syracuseStep 712439 = 1068659) B1068659
theorem B4251527 : Blo 247818 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B843911 : Blo 247818 843911 := bstep (se 1 (by rfl) ⟨632933, by rfl⟩ : syracuseStep 843911 = 1265867) B1265867
theorem B9691469 : Blo 247818 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B418297 : Blo 247818 418297 := bstep (se 2 (by rfl) ⟨156861, by rfl⟩ : syracuseStep 418297 = 313723) B313723
theorem B418567 : Blo 247818 418567 := bstep (se 1 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 418567 = 627851) B627851
theorem B418601 : Blo 247818 418601 := bstep (se 2 (by rfl) ⟨156975, by rfl⟩ : syracuseStep 418601 = 313951) B313951
theorem B418871 : Blo 247818 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B1598629 : Blo 247818 1598629 := bstep (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) B299743
theorem B845423 : Blo 247818 845423 := bstep (se 1 (by rfl) ⟨634067, by rfl⟩ : syracuseStep 845423 = 1268135) B1268135
theorem B1074809 : Blo 247818 1074809 := bstep (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) B806107
theorem B353975 : Blo 247818 353975 := bstep (se 1 (by rfl) ⟨265481, by rfl⟩ : syracuseStep 353975 = 530963) B530963
theorem B845531 : Blo 247818 845531 := bstep (se 1 (by rfl) ⟨634148, by rfl⟩ : syracuseStep 845531 = 1268297) B1268297
theorem B419647 : Blo 247818 419647 := bstep (se 1 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 419647 = 629471) B629471
theorem B34498457 : Blo 247818 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B944237 : Blo 247818 944237 := bstep (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) B354089
theorem B1272023 : Blo 247818 1272023 := bstep (se 1 (by rfl) ⟨954017, by rfl⟩ : syracuseStep 1272023 = 1908035) B1908035
theorem B1272347 : Blo 247818 1272347 := bstep (se 1 (by rfl) ⟨954260, by rfl⟩ : syracuseStep 1272347 = 1908521) B1908521
theorem B420383 : Blo 247818 420383 := bstep (se 1 (by rfl) ⟨315287, by rfl⟩ : syracuseStep 420383 = 630575) B630575
theorem B420457 : Blo 247818 420457 := bstep (se 2 (by rfl) ⟨157671, by rfl⟩ : syracuseStep 420457 = 315343) B315343
theorem B2878199 : Blo 247818 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B420815 : Blo 247818 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B846827 : Blo 247818 846827 := bstep (se 1 (by rfl) ⟨635120, by rfl⟩ : syracuseStep 846827 = 1270241) B1270241
theorem B846881 : Blo 247818 846881 := bstep (se 2 (by rfl) ⟨317580, by rfl⟩ : syracuseStep 846881 = 635161) B635161
theorem B6810911 : Blo 247818 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B421483 : Blo 247818 421483 := bstep (se 1 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 421483 = 632225) B632225
theorem B421753 : Blo 247818 421753 := bstep (se 2 (by rfl) ⟨158157, by rfl⟩ : syracuseStep 421753 = 316315) B316315
theorem B421787 : Blo 247818 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B848339 : Blo 247818 848339 := bstep (se 1 (by rfl) ⟨636254, by rfl⟩ : syracuseStep 848339 = 1272509) B1272509
theorem B1274615 : Blo 247818 1274615 := bstep (se 1 (by rfl) ⟨955961, by rfl⟩ : syracuseStep 1274615 = 1911923) B1911923
theorem B422975 : Blo 247818 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B2389297 : Blo 247818 2389297 := bstep (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) B1791973
theorem B423535 : Blo 247818 423535 := bstep (se 1 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 423535 = 635303) B635303
theorem B173930165 : Blo 247818 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B423643 : Blo 247818 423643 := bstep (se 1 (by rfl) ⟨317732, by rfl⟩ : syracuseStep 423643 = 635465) B635465
theorem B948125 : Blo 247818 948125 := bstep (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) B355547
theorem B718931 : Blo 247818 718931 := bstep (se 1 (by rfl) ⟨539198, by rfl⟩ : syracuseStep 718931 = 1078397) B1078397
theorem B948307 : Blo 247818 948307 := bstep (se 1 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 948307 = 1422461) B1422461
theorem B2848931 : Blo 247818 2848931 := bstep (se 1 (by rfl) ⟨2136698, by rfl⟩ : syracuseStep 2848931 = 4273397) B4273397
theorem B948793 : Blo 247818 948793 := bstep (se 2 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 948793 = 711595) B711595
theorem B424939 : Blo 247818 424939 := bstep (se 1 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 424939 = 637409) B637409
theorem B1670519 : Blo 247818 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B720571 : Blo 247818 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B4129049 : Blo 247818 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B35324219 : Blo 247818 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B557729 : Blo 247818 557729 := bstep (se 2 (by rfl) ⟨209148, by rfl⟩ : syracuseStep 557729 = 418297) B418297
theorem B558089 : Blo 247818 558089 := bstep (se 2 (by rfl) ⟨209283, by rfl⟩ : syracuseStep 558089 = 418567) B418567
theorem B558143 : Blo 247818 558143 := bstep (se 1 (by rfl) ⟨418607, by rfl⟩ : syracuseStep 558143 = 837215) B837215
theorem B2131231 : Blo 247818 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B2131505 : Blo 247818 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B951983 : Blo 247818 951983 := bstep (se 1 (by rfl) ⟨713987, by rfl⟩ : syracuseStep 951983 = 1427975) B1427975
theorem B559079 : Blo 247818 559079 := bstep (se 1 (by rfl) ⟨419309, by rfl⟩ : syracuseStep 559079 = 838619) B838619
theorem B10192877 : Blo 247818 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B4294721 : Blo 247818 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B559259 : Blo 247818 559259 := bstep (se 1 (by rfl) ⟨419444, by rfl⟩ : syracuseStep 559259 = 838889) B838889
theorem B559439 : Blo 247818 559439 := bstep (se 1 (by rfl) ⟨419579, by rfl⟩ : syracuseStep 559439 = 839159) B839159
theorem B5212511 : Blo 247818 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B559529 : Blo 247818 559529 := bstep (se 2 (by rfl) ⟨209823, by rfl⟩ : syracuseStep 559529 = 419647) B419647
theorem B560123 : Blo 247818 560123 := bstep (se 1 (by rfl) ⟨420092, by rfl⟩ : syracuseStep 560123 = 840185) B840185
theorem B560303 : Blo 247818 560303 := bstep (se 1 (by rfl) ⟨420227, by rfl⟩ : syracuseStep 560303 = 840455) B840455
theorem B560339 : Blo 247818 560339 := bstep (se 1 (by rfl) ⟨420254, by rfl⟩ : syracuseStep 560339 = 840509) B840509
theorem B265627 : Blo 247818 265627 := bstep (se 1 (by rfl) ⟨199220, by rfl⟩ : syracuseStep 265627 = 398441) B398441
theorem B560609 : Blo 247818 560609 := bstep (se 2 (by rfl) ⟨210228, by rfl⟩ : syracuseStep 560609 = 420457) B420457
theorem B561023 : Blo 247818 561023 := bstep (se 1 (by rfl) ⟨420767, by rfl⟩ : syracuseStep 561023 = 841535) B841535
theorem B3411857 : Blo 247818 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B3248585 : Blo 247818 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B3609143 : Blo 247818 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B561977 : Blo 247818 561977 := bstep (se 2 (by rfl) ⟨210741, by rfl⟩ : syracuseStep 561977 = 421483) B421483
theorem B562031 : Blo 247818 562031 := bstep (se 1 (by rfl) ⟨421523, by rfl⟩ : syracuseStep 562031 = 843047) B843047
theorem B529391 : Blo 247818 529391 := bstep (se 1 (by rfl) ⟨397043, by rfl⟩ : syracuseStep 529391 = 794087) B794087
theorem B1414169 : Blo 247818 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B562337 : Blo 247818 562337 := bstep (se 2 (by rfl) ⟨210876, by rfl⟩ : syracuseStep 562337 = 421753) B421753
theorem B562607 : Blo 247818 562607 := bstep (se 1 (by rfl) ⟨421955, by rfl⟩ : syracuseStep 562607 = 843911) B843911
theorem B6460979 : Blo 247818 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B1906577 : Blo 247818 1906577 := bstep (se 2 (by rfl) ⟨714966, by rfl⟩ : syracuseStep 1906577 = 1429933) B1429933
theorem B1907063 : Blo 247818 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B563615 : Blo 247818 563615 := bstep (se 1 (by rfl) ⟨422711, by rfl⟩ : syracuseStep 563615 = 845423) B845423
theorem B596411 : Blo 247818 596411 := bstep (se 1 (by rfl) ⟨447308, by rfl⟩ : syracuseStep 596411 = 894617) B894617
theorem B563687 : Blo 247818 563687 := bstep (se 1 (by rfl) ⟨422765, by rfl⟩ : syracuseStep 563687 = 845531) B845531
theorem B629491 : Blo 247818 629491 := bstep (se 1 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 629491 = 944237) B944237
theorem B597017 : Blo 247818 597017 := bstep (se 2 (by rfl) ⟨223881, by rfl⟩ : syracuseStep 597017 = 447763) B447763
theorem B3185729 : Blo 247818 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B564551 : Blo 247818 564551 := bstep (se 1 (by rfl) ⟨423413, by rfl⟩ : syracuseStep 564551 = 846827) B846827
theorem B564587 : Blo 247818 564587 := bstep (se 1 (by rfl) ⟨423440, by rfl⟩ : syracuseStep 564587 = 846881) B846881
theorem B564713 : Blo 247818 564713 := bstep (se 2 (by rfl) ⟨211767, by rfl⟩ : syracuseStep 564713 = 423535) B423535
theorem B564857 : Blo 247818 564857 := bstep (se 2 (by rfl) ⟨211821, by rfl⟩ : syracuseStep 564857 = 423643) B423643
theorem B9117535 : Blo 247818 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B630625 : Blo 247818 630625 := bstep (se 2 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 630625 = 472969) B472969
theorem B1417085 : Blo 247818 1417085 := bstep (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) B531407
theorem B532603 : Blo 247818 532603 := bstep (se 1 (by rfl) ⟨399452, by rfl⟩ : syracuseStep 532603 = 798905) B798905
theorem B1909007 : Blo 247818 1909007 := bstep (se 1 (by rfl) ⟨1431755, by rfl⟩ : syracuseStep 1909007 = 2863511) B2863511
theorem B565559 : Blo 247818 565559 := bstep (se 1 (by rfl) ⟨424169, by rfl⟩ : syracuseStep 565559 = 848339) B848339
theorem B893521 : Blo 247818 893521 := bstep (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) B670141
theorem B533279 : Blo 247818 533279 := bstep (se 1 (by rfl) ⟨399959, by rfl⟩ : syracuseStep 533279 = 799919) B799919
theorem B632083 : Blo 247818 632083 := bstep (se 1 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 632083 = 948125) B948125
theorem B566585 : Blo 247818 566585 := bstep (se 2 (by rfl) ⟨212469, by rfl⟩ : syracuseStep 566585 = 424939) B424939
theorem B534671 : Blo 247818 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B960761 : Blo 247818 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B1354427 : Blo 247818 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B797663 : Blo 247818 797663 := bstep (se 1 (by rfl) ⟨598247, by rfl⟩ : syracuseStep 797663 = 1196495) B1196495
theorem B1059911 : Blo 247818 1059911 := bstep (se 1 (by rfl) ⟨794933, by rfl⟩ : syracuseStep 1059911 = 1589867) B1589867
theorem B4304015 : Blo 247818 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B797971 : Blo 247818 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B372023 : Blo 247818 372023 := bstep (se 1 (by rfl) ⟨279017, by rfl⟩ : syracuseStep 372023 = 558035) B558035
theorem B4566365 : Blo 247818 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1191323 : Blo 247818 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B372191 : Blo 247818 372191 := bstep (se 1 (by rfl) ⟨279143, by rfl⟩ : syracuseStep 372191 = 558287) B558287
theorem B1158799 : Blo 247818 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B372407 : Blo 247818 372407 := bstep (se 1 (by rfl) ⟨279305, by rfl⟩ : syracuseStep 372407 = 558611) B558611
theorem B569065 : Blo 247818 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B536311 : Blo 247818 536311 := bstep (se 1 (by rfl) ⟨402233, by rfl⟩ : syracuseStep 536311 = 804467) B804467
theorem B372617 : Blo 247818 372617 := bstep (se 2 (by rfl) ⟨139731, by rfl⟩ : syracuseStep 372617 = 279463) B279463
theorem B372863 : Blo 247818 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B602255 : Blo 247818 602255 := bstep (se 1 (by rfl) ⟨451691, by rfl⟩ : syracuseStep 602255 = 903383) B903383
theorem B635111 : Blo 247818 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B536807 : Blo 247818 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B504083 : Blo 247818 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B373499 : Blo 247818 373499 := bstep (se 1 (by rfl) ⟨280124, by rfl⟩ : syracuseStep 373499 = 560249) B560249
theorem B1422143 : Blo 247818 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B373943 : Blo 247818 373943 := bstep (se 1 (by rfl) ⟨280457, by rfl⟩ : syracuseStep 373943 = 560915) B560915
theorem B374183 : Blo 247818 374183 := bstep (se 1 (by rfl) ⟨280637, by rfl⟩ : syracuseStep 374183 = 561275) B561275
theorem B374363 : Blo 247818 374363 := bstep (se 1 (by rfl) ⟨280772, by rfl⟩ : syracuseStep 374363 = 561545) B561545
theorem B374825 : Blo 247818 374825 := bstep (se 2 (by rfl) ⟨140559, by rfl⟩ : syracuseStep 374825 = 281119) B281119
theorem B374855 : Blo 247818 374855 := bstep (se 1 (by rfl) ⟨281141, by rfl⟩ : syracuseStep 374855 = 562283) B562283
theorem B2144353 : Blo 247818 2144353 := bstep (se 2 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 2144353 = 1608265) B1608265
theorem B375239 : Blo 247818 375239 := bstep (se 1 (by rfl) ⟨281429, by rfl⟩ : syracuseStep 375239 = 562859) B562859
theorem B473759 : Blo 247818 473759 := bstep (se 1 (by rfl) ⟨355319, by rfl⟩ : syracuseStep 473759 = 710639) B710639
theorem B375455 : Blo 247818 375455 := bstep (se 1 (by rfl) ⟨281591, by rfl⟩ : syracuseStep 375455 = 563183) B563183
theorem B375599 : Blo 247818 375599 := bstep (se 1 (by rfl) ⟨281699, by rfl⟩ : syracuseStep 375599 = 563399) B563399
theorem B375719 : Blo 247818 375719 := bstep (se 1 (by rfl) ⟨281789, by rfl⟩ : syracuseStep 375719 = 563579) B563579
theorem B375899 : Blo 247818 375899 := bstep (se 1 (by rfl) ⟨281924, by rfl⟩ : syracuseStep 375899 = 563849) B563849
theorem B1424627 : Blo 247818 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B7257377 : Blo 247818 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B13745501 : Blo 247818 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B671159 : Blo 247818 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B376271 : Blo 247818 376271 := bstep (se 1 (by rfl) ⟨282203, by rfl⟩ : syracuseStep 376271 = 564407) B564407
theorem B474731 : Blo 247818 474731 := bstep (se 1 (by rfl) ⟨356048, by rfl⟩ : syracuseStep 474731 = 712097) B712097
theorem B474959 : Blo 247818 474959 := bstep (se 1 (by rfl) ⟨356219, by rfl⟩ : syracuseStep 474959 = 712439) B712439
theorem B376655 : Blo 247818 376655 := bstep (se 1 (by rfl) ⟨282491, by rfl⟩ : syracuseStep 376655 = 564983) B564983
theorem B1195897 : Blo 247818 1195897 := bstep (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) B896923
theorem B2834351 : Blo 247818 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B376775 : Blo 247818 376775 := bstep (se 1 (by rfl) ⟨282581, by rfl⟩ : syracuseStep 376775 = 565163) B565163
theorem B377135 : Blo 247818 377135 := bstep (se 1 (by rfl) ⟨282851, by rfl⟩ : syracuseStep 377135 = 565703) B565703
theorem B15483413 : Blo 247818 15483413 := bstep (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) B725785
theorem B279067 : Blo 247818 279067 := bstep (se 1 (by rfl) ⟨209300, by rfl⟩ : syracuseStep 279067 = 418601) B418601
theorem B377375 : Blo 247818 377375 := bstep (se 1 (by rfl) ⟨283031, by rfl⟩ : syracuseStep 377375 = 566063) B566063
theorem B279247 : Blo 247818 279247 := bstep (se 1 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 279247 = 418871) B418871
theorem B836783 : Blo 247818 836783 := bstep (se 1 (by rfl) ⟨627587, by rfl⟩ : syracuseStep 836783 = 1255175) B1255175
theorem B280255 : Blo 247818 280255 := bstep (se 1 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 280255 = 420383) B420383
theorem B1918799 : Blo 247818 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B280543 : Blo 247818 280543 := bstep (se 1 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 280543 = 420815) B420815
theorem B247835 : Blo 247818 247835 := bstep (se 1 (by rfl) ⟨185876, by rfl⟩ : syracuseStep 247835 = 371753) B371753
theorem B247839 : Blo 247818 247839 := bstep (se 1 (by rfl) ⟨185879, by rfl⟩ : syracuseStep 247839 = 371759) B371759
theorem B247855 : Blo 247818 247855 := bstep (se 1 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 247855 = 371783) B371783
theorem B4540607 : Blo 247818 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B248031 : Blo 247818 248031 := bstep (se 1 (by rfl) ⟨186023, by rfl⟩ : syracuseStep 248031 = 372047) B372047
theorem B248091 : Blo 247818 248091 := bstep (se 1 (by rfl) ⟨186068, by rfl⟩ : syracuseStep 248091 = 372137) B372137
theorem B248191 : Blo 247818 248191 := bstep (se 1 (by rfl) ⟨186143, by rfl⟩ : syracuseStep 248191 = 372287) B372287
theorem B248367 : Blo 247818 248367 := bstep (se 1 (by rfl) ⟨186275, by rfl⟩ : syracuseStep 248367 = 372551) B372551
theorem B248423 : Blo 247818 248423 := bstep (se 1 (by rfl) ⟨186317, by rfl⟩ : syracuseStep 248423 = 372635) B372635
theorem B281191 : Blo 247818 281191 := bstep (se 1 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 281191 = 421787) B421787
theorem B2149001 : Blo 247818 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B1264409 : Blo 247818 1264409 := bstep (se 2 (by rfl) ⟨474153, by rfl⟩ : syracuseStep 1264409 = 948307) B948307
theorem B707449 : Blo 247818 707449 := bstep (se 2 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 707449 = 530587) B530587
theorem B674681 : Blo 247818 674681 := bstep (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) B506011
theorem B248799 : Blo 247818 248799 := bstep (se 1 (by rfl) ⟨186599, by rfl⟩ : syracuseStep 248799 = 373199) B373199
theorem B248827 : Blo 247818 248827 := bstep (se 1 (by rfl) ⟨186620, by rfl⟩ : syracuseStep 248827 = 373241) B373241
theorem B1428475 : Blo 247818 1428475 := bstep (se 1 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 1428475 = 2142713) B2142713
theorem B248895 : Blo 247818 248895 := bstep (se 1 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 248895 = 373343) B373343
theorem B314543 : Blo 247818 314543 := bstep (se 1 (by rfl) ⟨235907, by rfl⟩ : syracuseStep 314543 = 471815) B471815
theorem B1199357 : Blo 247818 1199357 := bstep (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) B449759
theorem B249215 : Blo 247818 249215 := bstep (se 1 (by rfl) ⟨186911, by rfl⟩ : syracuseStep 249215 = 373823) B373823
theorem B281983 : Blo 247818 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B249243 : Blo 247818 249243 := bstep (se 1 (by rfl) ⟨186932, by rfl⟩ : syracuseStep 249243 = 373865) B373865
theorem B1265057 : Blo 247818 1265057 := bstep (se 2 (by rfl) ⟨474396, by rfl⟩ : syracuseStep 1265057 = 948793) B948793
theorem B249311 : Blo 247818 249311 := bstep (se 1 (by rfl) ⟨186983, by rfl⟩ : syracuseStep 249311 = 373967) B373967
theorem B249447 : Blo 247818 249447 := bstep (se 1 (by rfl) ⟨187085, by rfl⟩ : syracuseStep 249447 = 374171) B374171
theorem B249595 : Blo 247818 249595 := bstep (se 1 (by rfl) ⟨187196, by rfl⟩ : syracuseStep 249595 = 374393) B374393
theorem B115953443 : Blo 247818 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B249663 : Blo 247818 249663 := bstep (se 1 (by rfl) ⟨187247, by rfl⟩ : syracuseStep 249663 = 374495) B374495
theorem B249727 : Blo 247818 249727 := bstep (se 1 (by rfl) ⟨187295, by rfl⟩ : syracuseStep 249727 = 374591) B374591
theorem B249839 : Blo 247818 249839 := bstep (se 1 (by rfl) ⟨187379, by rfl⟩ : syracuseStep 249839 = 374759) B374759
theorem B249851 : Blo 247818 249851 := bstep (se 1 (by rfl) ⟨187388, by rfl⟩ : syracuseStep 249851 = 374777) B374777
theorem B479287 : Blo 247818 479287 := bstep (se 1 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 479287 = 718931) B718931
theorem B249919 : Blo 247818 249919 := bstep (se 1 (by rfl) ⟨187439, by rfl⟩ : syracuseStep 249919 = 374879) B374879
theorem B249959 : Blo 247818 249959 := bstep (se 1 (by rfl) ⟨187469, by rfl⟩ : syracuseStep 249959 = 374939) B374939
theorem B249983 : Blo 247818 249983 := bstep (se 1 (by rfl) ⟨187487, by rfl⟩ : syracuseStep 249983 = 374975) B374975
theorem B250011 : Blo 247818 250011 := bstep (se 1 (by rfl) ⟨187508, by rfl⟩ : syracuseStep 250011 = 375017) B375017
theorem B5099719 : Blo 247818 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B2281691 : Blo 247818 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B708851 : Blo 247818 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B1429751 : Blo 247818 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B4837643 : Blo 247818 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B250215 : Blo 247818 250215 := bstep (se 1 (by rfl) ⟨187661, by rfl⟩ : syracuseStep 250215 = 375323) B375323
theorem B250267 : Blo 247818 250267 := bstep (se 1 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 250267 = 375401) B375401
theorem B250619 : Blo 247818 250619 := bstep (se 1 (by rfl) ⟨187964, by rfl⟩ : syracuseStep 250619 = 375929) B375929
theorem B250687 : Blo 247818 250687 := bstep (se 1 (by rfl) ⟨188015, by rfl⟩ : syracuseStep 250687 = 376031) B376031
theorem B250715 : Blo 247818 250715 := bstep (se 1 (by rfl) ⟨188036, by rfl⟩ : syracuseStep 250715 = 376073) B376073
theorem B250783 : Blo 247818 250783 := bstep (se 1 (by rfl) ⟨188087, by rfl⟩ : syracuseStep 250783 = 376175) B376175
theorem B250863 : Blo 247818 250863 := bstep (se 1 (by rfl) ⟨188147, by rfl⟩ : syracuseStep 250863 = 376295) B376295
theorem B250951 : Blo 247818 250951 := bstep (se 1 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 250951 = 376427) B376427
theorem B251035 : Blo 247818 251035 := bstep (se 1 (by rfl) ⟨188276, by rfl⟩ : syracuseStep 251035 = 376553) B376553
theorem B251131 : Blo 247818 251131 := bstep (se 1 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 251131 = 376697) B376697
theorem B1070333 : Blo 247818 1070333 := bstep (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) B401375
theorem B447785 : Blo 247818 447785 := bstep (se 2 (by rfl) ⟨167919, by rfl⟩ : syracuseStep 447785 = 335839) B335839
theorem B251199 : Blo 247818 251199 := bstep (se 1 (by rfl) ⟨188399, by rfl⟩ : syracuseStep 251199 = 376799) B376799
theorem B1430891 : Blo 247818 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B251367 : Blo 247818 251367 := bstep (se 1 (by rfl) ⟨188525, by rfl⟩ : syracuseStep 251367 = 377051) B377051
theorem B251375 : Blo 247818 251375 := bstep (se 1 (by rfl) ⟨188531, by rfl⟩ : syracuseStep 251375 = 377063) B377063
theorem B251483 : Blo 247818 251483 := bstep (se 1 (by rfl) ⟨188612, by rfl⟩ : syracuseStep 251483 = 377225) B377225
theorem B251547 : Blo 247818 251547 := bstep (se 1 (by rfl) ⟨188660, by rfl⟩ : syracuseStep 251547 = 377321) B377321
theorem B251631 : Blo 247818 251631 := bstep (se 1 (by rfl) ⟨188723, by rfl⟩ : syracuseStep 251631 = 377447) B377447
theorem B1267487 : Blo 247818 1267487 := bstep (se 1 (by rfl) ⟨950615, by rfl⟩ : syracuseStep 1267487 = 1901231) B1901231
theorem B251719 : Blo 247818 251719 := bstep (se 1 (by rfl) ⟨188789, by rfl⟩ : syracuseStep 251719 = 377579) B377579
theorem B710491 : Blo 247818 710491 := bstep (se 1 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 710491 = 1065737) B1065737
theorem B251739 : Blo 247818 251739 := bstep (se 1 (by rfl) ⟨188804, by rfl⟩ : syracuseStep 251739 = 377609) B377609
theorem B251807 : Blo 247818 251807 := bstep (se 1 (by rfl) ⟨188855, by rfl⟩ : syracuseStep 251807 = 377711) B377711
theorem B841697 : Blo 247818 841697 := bstep (se 2 (by rfl) ⟨315636, by rfl⟩ : syracuseStep 841697 = 631273) B631273
theorem B5363891 : Blo 247818 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B1431917 : Blo 247818 1431917 := bstep (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) B536969
theorem B2284321 : Blo 247818 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B645943 : Blo 247818 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B285563 : Blo 247818 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B711823 : Blo 247818 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B1891511 : Blo 247818 1891511 := bstep (se 1 (by rfl) ⟨1418633, by rfl⟩ : syracuseStep 1891511 = 2837267) B2837267
theorem B2613383 : Blo 247818 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B1073407 : Blo 247818 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B418331 : Blo 247818 418331 := bstep (se 1 (by rfl) ⟨313748, by rfl⟩ : syracuseStep 418331 = 627497) B627497
theorem B2286247 : Blo 247818 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B3203819 : Blo 247818 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B1074707 : Blo 247818 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B2746075 : Blo 247818 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1009427 : Blo 247818 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B943933 : Blo 247818 943933 := bstep (se 3 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 943933 = 353975) B353975
theorem B2287561 : Blo 247818 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B714739 : Blo 247818 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B2582699 : Blo 247818 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1894913 : Blo 247818 1894913 := bstep (se 2 (by rfl) ⟨710592, by rfl⟩ : syracuseStep 1894913 = 1421185) B1421185
theorem B1010207 : Blo 247818 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B3862225 : Blo 247818 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B716539 : Blo 247818 716539 := bstep (se 1 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 716539 = 1074809) B1074809
theorem B22998971 : Blo 247818 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B848015 : Blo 247818 848015 := bstep (se 1 (by rfl) ⟨636011, by rfl⟩ : syracuseStep 848015 = 1272023) B1272023
theorem B946363 : Blo 247818 946363 := bstep (se 1 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 946363 = 1419545) B1419545
theorem B848231 : Blo 247818 848231 := bstep (se 1 (by rfl) ⟨636173, by rfl⟩ : syracuseStep 848231 = 1272347) B1272347
theorem B422651 : Blo 247818 422651 := bstep (se 1 (by rfl) ⟨316988, by rfl⟩ : syracuseStep 422651 = 633977) B633977
theorem B2388797 : Blo 247818 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B1602935 : Blo 247818 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B1209815 : Blo 247818 1209815 := bstep (se 1 (by rfl) ⟨907361, by rfl⟩ : syracuseStep 1209815 = 1814723) B1814723
theorem B423515 : Blo 247818 423515 := bstep (se 1 (by rfl) ⟨317636, by rfl⟩ : syracuseStep 423515 = 635273) B635273
theorem B947807 : Blo 247818 947807 := bstep (se 1 (by rfl) ⟨710855, by rfl⟩ : syracuseStep 947807 = 1421711) B1421711
theorem B849743 : Blo 247818 849743 := bstep (se 1 (by rfl) ⟨637307, by rfl⟩ : syracuseStep 849743 = 1274615) B1274615
theorem B2127815 : Blo 247818 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B1013743 : Blo 247818 1013743 := bstep (se 1 (by rfl) ⟨760307, by rfl⟩ : syracuseStep 1013743 = 1520615) B1520615
theorem B1341623 : Blo 247818 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B1013971 : Blo 247818 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B424399 : Blo 247818 424399 := bstep (se 1 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 424399 = 636599) B636599
theorem B1342097 : Blo 247818 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B1276573 : Blo 247818 1276573 := bstep (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) B478715
theorem B1899287 : Blo 247818 1899287 := bstep (se 1 (by rfl) ⟨1424465, by rfl⟩ : syracuseStep 1899287 = 2848931) B2848931
theorem B2128841 : Blo 247818 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B425191 : Blo 247818 425191 := bstep (se 1 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 425191 = 637787) B637787
theorem B1277435 : Blo 247818 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B1113679 : Blo 247818 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B9273041 : Blo 247818 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B2752699 : Blo 247818 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B10322275 : Blo 247818 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B1344221 : Blo 247818 1344221 := bstep (se 3 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 1344221 = 504083) B504083
theorem B557855 : Blo 247818 557855 := bstep (se 1 (by rfl) ⟨418391, by rfl⟩ : syracuseStep 557855 = 836783) B836783
theorem B3048329 : Blo 247818 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B1279199 : Blo 247818 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B3475007 : Blo 247818 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B77302295 : Blo 247818 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B3050081 : Blo 247818 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B952985 : Blo 247818 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B953167 : Blo 247818 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B2165723 : Blo 247818 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B298523 : Blo 247818 298523 := bstep (se 1 (by rfl) ⟨223892, by rfl⟩ : syracuseStep 298523 = 447785) B447785
theorem B953927 : Blo 247818 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B561131 : Blo 247818 561131 := bstep (se 1 (by rfl) ⟨420848, by rfl⟩ : syracuseStep 561131 = 841697) B841697
theorem B1904633 : Blo 247818 1904633 := bstep (se 2 (by rfl) ⟨714237, by rfl⟩ : syracuseStep 1904633 = 1428475) B1428475
theorem B3575927 : Blo 247818 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B954611 : Blo 247818 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B397607 : Blo 247818 397607 := bstep (se 1 (by rfl) ⟨298205, by rfl⟩ : syracuseStep 397607 = 596411) B596411
theorem B2691805 : Blo 247818 2691805 := bstep (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) B1009427
theorem B1545065 : Blo 247818 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B758753 : Blo 247818 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B955385 : Blo 247818 955385 := bstep (se 2 (by rfl) ⟨358269, by rfl⟩ : syracuseStep 955385 = 716539) B716539
theorem B1742255 : Blo 247818 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B6887197 : Blo 247818 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B2135879 : Blo 247818 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B531775 : Blo 247818 531775 := bstep (se 1 (by rfl) ⟨398831, by rfl⟩ : syracuseStep 531775 = 797663) B797663
theorem B794215 : Blo 247818 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B761501 : Blo 247818 761501 := bstep (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) B285563
theorem B1351657 : Blo 247818 1351657 := bstep (se 2 (by rfl) ⟨506871, by rfl⟩ : syracuseStep 1351657 = 1013743) B1013743
theorem B401503 : Blo 247818 401503 := bstep (se 1 (by rfl) ⟨301127, by rfl⟩ : syracuseStep 401503 = 602255) B602255
theorem B565343 : Blo 247818 565343 := bstep (se 1 (by rfl) ⟨424007, by rfl⟩ : syracuseStep 565343 = 848015) B848015
theorem B2859137 : Blo 247818 2859137 := bstep (se 2 (by rfl) ⟨1072176, by rfl⟩ : syracuseStep 2859137 = 2144353) B2144353
theorem B565487 : Blo 247818 565487 := bstep (se 1 (by rfl) ⟨424115, by rfl⟩ : syracuseStep 565487 = 848231) B848231
theorem B1351961 : Blo 247818 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B565865 : Blo 247818 565865 := bstep (se 2 (by rfl) ⟨212199, by rfl⟩ : syracuseStep 565865 = 424399) B424399
theorem B631871 : Blo 247818 631871 := bstep (se 1 (by rfl) ⟨473903, by rfl⟩ : syracuseStep 631871 = 947807) B947807
theorem B861257 : Blo 247818 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B566495 : Blo 247818 566495 := bstep (se 1 (by rfl) ⟨424871, by rfl⟩ : syracuseStep 566495 = 849743) B849743
theorem B1418543 : Blo 247818 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B894415 : Blo 247818 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B566921 : Blo 247818 566921 := bstep (se 2 (by rfl) ⟨212595, by rfl⟩ : syracuseStep 566921 = 425191) B425191
theorem B894731 : Blo 247818 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1419227 : Blo 247818 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B1484905 : Blo 247818 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B371819 : Blo 247818 371819 := bstep (se 1 (by rfl) ⟨278864, by rfl⟩ : syracuseStep 371819 = 557729) B557729
theorem B372059 : Blo 247818 372059 := bstep (se 1 (by rfl) ⟨279044, by rfl⟩ : syracuseStep 372059 = 558089) B558089
theorem B372089 : Blo 247818 372089 := bstep (se 2 (by rfl) ⟨139533, by rfl⟩ : syracuseStep 372089 = 279067) B279067
theorem B372095 : Blo 247818 372095 := bstep (se 1 (by rfl) ⟨279071, by rfl⟩ : syracuseStep 372095 = 558143) B558143
theorem B1191361 : Blo 247818 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B372329 : Blo 247818 372329 := bstep (se 2 (by rfl) ⟨139623, by rfl⟩ : syracuseStep 372329 = 279247) B279247
theorem B1421003 : Blo 247818 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B634655 : Blo 247818 634655 := bstep (se 1 (by rfl) ⟨475991, by rfl⟩ : syracuseStep 634655 = 951983) B951983
theorem B372719 : Blo 247818 372719 := bstep (se 1 (by rfl) ⟨279539, by rfl⟩ : syracuseStep 372719 = 559079) B559079
theorem B6795251 : Blo 247818 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B372839 : Blo 247818 372839 := bstep (se 1 (by rfl) ⟨279629, by rfl⟩ : syracuseStep 372839 = 559259) B559259
theorem B3027071 : Blo 247818 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B372959 : Blo 247818 372959 := bstep (se 1 (by rfl) ⟨279719, by rfl⟩ : syracuseStep 372959 = 559439) B559439
theorem B373019 : Blo 247818 373019 := bstep (se 1 (by rfl) ⟨279764, by rfl⟩ : syracuseStep 373019 = 559529) B559529
theorem B373415 : Blo 247818 373415 := bstep (se 1 (by rfl) ⟨280061, by rfl⟩ : syracuseStep 373415 = 560123) B560123
theorem B373535 : Blo 247818 373535 := bstep (se 1 (by rfl) ⟨280151, by rfl⟩ : syracuseStep 373535 = 560303) B560303
theorem B373559 : Blo 247818 373559 := bstep (se 1 (by rfl) ⟨280169, by rfl⟩ : syracuseStep 373559 = 560339) B560339
theorem B799571 : Blo 247818 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B373673 : Blo 247818 373673 := bstep (se 2 (by rfl) ⟨140127, by rfl⟩ : syracuseStep 373673 = 280255) B280255
theorem B373739 : Blo 247818 373739 := bstep (se 1 (by rfl) ⟨280304, by rfl⟩ : syracuseStep 373739 = 560609) B560609
theorem B1258577 : Blo 247818 1258577 := bstep (se 2 (by rfl) ⟨471966, by rfl⟩ : syracuseStep 1258577 = 943933) B943933
theorem B374015 : Blo 247818 374015 := bstep (se 1 (by rfl) ⟨280511, by rfl⟩ : syracuseStep 374015 = 561023) B561023
theorem B2274571 : Blo 247818 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B374057 : Blo 247818 374057 := bstep (se 2 (by rfl) ⟨140271, by rfl⟩ : syracuseStep 374057 = 280543) B280543
theorem B1521127 : Blo 247818 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B472567 : Blo 247818 472567 := bstep (se 1 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 472567 = 708851) B708851
theorem B3225095 : Blo 247818 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B2406095 : Blo 247818 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B374651 : Blo 247818 374651 := bstep (se 1 (by rfl) ⟨280988, by rfl⟩ : syracuseStep 374651 = 561977) B561977
theorem B374687 : Blo 247818 374687 := bstep (se 1 (by rfl) ⟨281015, by rfl⟩ : syracuseStep 374687 = 562031) B562031
theorem B374891 : Blo 247818 374891 := bstep (se 1 (by rfl) ⟨281168, by rfl⟩ : syracuseStep 374891 = 562337) B562337
theorem B374921 : Blo 247818 374921 := bstep (se 2 (by rfl) ⟨140595, by rfl⟩ : syracuseStep 374921 = 281191) B281191
theorem B375071 : Blo 247818 375071 := bstep (se 1 (by rfl) ⟨281303, by rfl⟩ : syracuseStep 375071 = 562607) B562607
theorem B375743 : Blo 247818 375743 := bstep (se 1 (by rfl) ⟨281807, by rfl⟩ : syracuseStep 375743 = 563615) B563615
theorem B375791 : Blo 247818 375791 := bstep (se 1 (by rfl) ⟨281843, by rfl⟩ : syracuseStep 375791 = 563687) B563687
theorem B1063961 : Blo 247818 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B375977 : Blo 247818 375977 := bstep (se 2 (by rfl) ⟨140991, by rfl⟩ : syracuseStep 375977 = 281983) B281983
theorem B1261007 : Blo 247818 1261007 := bstep (se 1 (by rfl) ⟨945755, by rfl⟩ : syracuseStep 1261007 = 1891511) B1891511
theorem B376367 : Blo 247818 376367 := bstep (se 1 (by rfl) ⟨282275, by rfl⟩ : syracuseStep 376367 = 564551) B564551
theorem B376391 : Blo 247818 376391 := bstep (se 1 (by rfl) ⟨282293, by rfl⟩ : syracuseStep 376391 = 564587) B564587
theorem B376475 : Blo 247818 376475 := bstep (se 1 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 376475 = 564713) B564713
theorem B376571 : Blo 247818 376571 := bstep (se 1 (by rfl) ⟨282428, by rfl⟩ : syracuseStep 376571 = 564857) B564857
theorem B639049 : Blo 247818 639049 := bstep (se 2 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 639049 = 479287) B479287
theorem B11452589 : Blo 247818 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B377039 : Blo 247818 377039 := bstep (se 1 (by rfl) ⟨282779, by rfl⟩ : syracuseStep 377039 = 565559) B565559
theorem B1261817 : Blo 247818 1261817 := bstep (se 2 (by rfl) ⟨473181, by rfl⟩ : syracuseStep 1261817 = 946363) B946363
theorem B6799625 : Blo 247818 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B278887 : Blo 247818 278887 := bstep (se 1 (by rfl) ⟨209165, by rfl⟩ : syracuseStep 278887 = 418331) B418331
theorem B377723 : Blo 247818 377723 := bstep (se 1 (by rfl) ⟨283292, by rfl⟩ : syracuseStep 377723 = 566585) B566585
theorem B640507 : Blo 247818 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B1263275 : Blo 247818 1263275 := bstep (se 1 (by rfl) ⟨947456, by rfl⟩ : syracuseStep 1263275 = 1894913) B1894913
theorem B673471 : Blo 247818 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B902951 : Blo 247818 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B706607 : Blo 247818 706607 := bstep (se 1 (by rfl) ⟨529955, by rfl⟩ : syracuseStep 706607 = 1059911) B1059911
theorem B2869343 : Blo 247818 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B248015 : Blo 247818 248015 := bstep (se 1 (by rfl) ⟨186011, by rfl⟩ : syracuseStep 248015 = 372023) B372023
theorem B248127 : Blo 247818 248127 := bstep (se 1 (by rfl) ⟨186095, by rfl⟩ : syracuseStep 248127 = 372191) B372191
theorem B248271 : Blo 247818 248271 := bstep (se 1 (by rfl) ⟨186203, by rfl⟩ : syracuseStep 248271 = 372407) B372407
theorem B248411 : Blo 247818 248411 := bstep (se 1 (by rfl) ⟨186308, by rfl⟩ : syracuseStep 248411 = 372617) B372617
theorem B1592045 : Blo 247818 1592045 := bstep (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) B597017
theorem B248575 : Blo 247818 248575 := bstep (se 1 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 248575 = 372863) B372863
theorem B838781 : Blo 247818 838781 := bstep (se 3 (by rfl) ⟨157271, by rfl⟩ : syracuseStep 838781 = 314543) B314543
theorem B248999 : Blo 247818 248999 := bstep (se 1 (by rfl) ⟨186749, by rfl⟩ : syracuseStep 248999 = 373499) B373499
theorem B281767 : Blo 247818 281767 := bstep (se 1 (by rfl) ⟨211325, by rfl⟩ : syracuseStep 281767 = 422651) B422651
theorem B1592531 : Blo 247818 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B19353005 : Blo 247818 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B249295 : Blo 247818 249295 := bstep (se 1 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 249295 = 373943) B373943
theorem B1068623 : Blo 247818 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B249455 : Blo 247818 249455 := bstep (se 1 (by rfl) ⟨187091, by rfl⟩ : syracuseStep 249455 = 374183) B374183
theorem B806543 : Blo 247818 806543 := bstep (se 1 (by rfl) ⟨604907, by rfl⟩ : syracuseStep 806543 = 1209815) B1209815
theorem B839321 : Blo 247818 839321 := bstep (se 2 (by rfl) ⟨314745, by rfl⟩ : syracuseStep 839321 = 629491) B629491
theorem B249575 : Blo 247818 249575 := bstep (se 1 (by rfl) ⟨187181, by rfl⟩ : syracuseStep 249575 = 374363) B374363
theorem B282343 : Blo 247818 282343 := bstep (se 1 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 282343 = 423515) B423515
theorem B20598533 : Blo 247818 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B7196597 : Blo 247818 7196597 := bstep (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) B674681
theorem B249883 : Blo 247818 249883 := bstep (se 1 (by rfl) ⟨187412, by rfl⟩ : syracuseStep 249883 = 374825) B374825
theorem B249903 : Blo 247818 249903 := bstep (se 1 (by rfl) ⟨187427, by rfl⟩ : syracuseStep 249903 = 374855) B374855
theorem B250159 : Blo 247818 250159 := bstep (se 1 (by rfl) ⟨187619, by rfl⟩ : syracuseStep 250159 = 375239) B375239
theorem B315839 : Blo 247818 315839 := bstep (se 1 (by rfl) ⟨236879, by rfl⟩ : syracuseStep 315839 = 473759) B473759
theorem B250303 : Blo 247818 250303 := bstep (se 1 (by rfl) ⟨187727, by rfl⟩ : syracuseStep 250303 = 375455) B375455
theorem B1266191 : Blo 247818 1266191 := bstep (se 1 (by rfl) ⟨949643, by rfl⟩ : syracuseStep 1266191 = 1899287) B1899287
theorem B250399 : Blo 247818 250399 := bstep (se 1 (by rfl) ⟨187799, by rfl⟩ : syracuseStep 250399 = 375599) B375599
theorem B250479 : Blo 247818 250479 := bstep (se 1 (by rfl) ⟨187859, by rfl⟩ : syracuseStep 250479 = 375719) B375719
theorem B250599 : Blo 247818 250599 := bstep (se 1 (by rfl) ⟨187949, by rfl⟩ : syracuseStep 250599 = 375899) B375899
theorem B9163667 : Blo 247818 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B447439 : Blo 247818 447439 := bstep (se 1 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 447439 = 671159) B671159
theorem B250847 : Blo 247818 250847 := bstep (se 1 (by rfl) ⟨188135, by rfl⟩ : syracuseStep 250847 = 376271) B376271
theorem B316487 : Blo 247818 316487 := bstep (se 1 (by rfl) ⟨237365, by rfl⟩ : syracuseStep 316487 = 474731) B474731
theorem B840833 : Blo 247818 840833 := bstep (se 2 (by rfl) ⟨315312, by rfl⟩ : syracuseStep 840833 = 630625) B630625
theorem B6182027 : Blo 247818 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1594529 : Blo 247818 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B316639 : Blo 247818 316639 := bstep (se 1 (by rfl) ⟨237479, by rfl⟩ : syracuseStep 316639 = 474959) B474959
theorem B251103 : Blo 247818 251103 := bstep (se 1 (by rfl) ⟨188327, by rfl⟩ : syracuseStep 251103 = 376655) B376655
theorem B1889567 : Blo 247818 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B251183 : Blo 247818 251183 := bstep (se 1 (by rfl) ⟨188387, by rfl⟩ : syracuseStep 251183 = 376775) B376775
theorem B710137 : Blo 247818 710137 := bstep (se 2 (by rfl) ⟨266301, by rfl⟩ : syracuseStep 710137 = 532603) B532603
theorem B251423 : Blo 247818 251423 := bstep (se 1 (by rfl) ⟨188567, by rfl⟩ : syracuseStep 251423 = 377135) B377135
theorem B1431209 : Blo 247818 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B251583 : Blo 247818 251583 := bstep (se 1 (by rfl) ⟨188687, by rfl⟩ : syracuseStep 251583 = 377375) B377375
theorem B94197917 : Blo 247818 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B842777 : Blo 247818 842777 := bstep (se 2 (by rfl) ⟨316041, by rfl⟩ : syracuseStep 842777 = 632083) B632083
theorem B2841641 : Blo 247818 2841641 := bstep (se 2 (by rfl) ⟨1065615, by rfl⟩ : syracuseStep 2841641 = 2131231) B2131231
theorem B1432667 : Blo 247818 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B842939 : Blo 247818 842939 := bstep (se 1 (by rfl) ⟨632204, by rfl⟩ : syracuseStep 842939 = 1264409) B1264409
theorem B843371 : Blo 247818 843371 := bstep (se 1 (by rfl) ⟨632528, by rfl⟩ : syracuseStep 843371 = 1265057) B1265057
theorem B3661433 : Blo 247818 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B352927 : Blo 247818 352927 := bstep (se 1 (by rfl) ⟨264695, by rfl⟩ : syracuseStep 352927 = 529391) B529391
theorem B942779 : Blo 247818 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B713555 : Blo 247818 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B943265 : Blo 247818 943265 := bstep (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) B707449
theorem B844991 : Blo 247818 844991 := bstep (se 1 (by rfl) ⟨633743, by rfl⟩ : syracuseStep 844991 = 1267487) B1267487
theorem B1271051 : Blo 247818 1271051 := bstep (se 1 (by rfl) ⟨953288, by rfl⟩ : syracuseStep 1271051 = 1906577) B1906577
theorem B17229277 : Blo 247818 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B1271375 : Blo 247818 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B354169 : Blo 247818 354169 := bstep (se 2 (by rfl) ⟨132813, by rfl⟩ : syracuseStep 354169 = 265627) B265627
theorem B2123819 : Blo 247818 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B715081 : Blo 247818 715081 := bstep (se 2 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 715081 = 536311) B536311
theorem B944723 : Blo 247818 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B1272671 : Blo 247818 1272671 := bstep (se 1 (by rfl) ⟨954503, by rfl⟩ : syracuseStep 1272671 = 1909007) B1909007
theorem B355519 : Blo 247818 355519 := bstep (se 1 (by rfl) ⟨266639, by rfl⟩ : syracuseStep 355519 = 533279) B533279
theorem B716471 : Blo 247818 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B356447 : Blo 247818 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B3044243 : Blo 247818 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B947321 : Blo 247818 947321 := bstep (se 2 (by rfl) ⟨355245, by rfl⟩ : syracuseStep 947321 = 710491) B710491
theorem B15332647 : Blo 247818 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B423407 : Blo 247818 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B357871 : Blo 247818 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B948095 : Blo 247818 948095 := bstep (se 1 (by rfl) ⟨711071, by rfl⟩ : syracuseStep 948095 = 1422143) B1422143
theorem B1702097 : Blo 247818 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B3045761 : Blo 247818 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B949097 : Blo 247818 949097 := bstep (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) B711823
theorem B949751 : Blo 247818 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B851623 : Blo 247818 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B12156713 : Blo 247818 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B852065 : Blo 247818 852065 := bstep (se 2 (by rfl) ⟨319524, by rfl⟩ : syracuseStep 852065 = 639049) B639049
theorem B7635059 : Blo 247818 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B3670265 : Blo 247818 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B950525 : Blo 247818 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B13763033 : Blo 247818 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B2032219 : Blo 247818 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B2033387 : Blo 247818 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B22972369 : Blo 247818 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B1443815 : Blo 247818 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B854009 : Blo 247818 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B559187 : Blo 247818 559187 := bstep (se 1 (by rfl) ⟨419390, by rfl⟩ : syracuseStep 559187 = 838781) B838781
theorem B2132189 : Blo 247818 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B559547 : Blo 247818 559547 := bstep (se 1 (by rfl) ⟨419660, by rfl⟩ : syracuseStep 559547 = 839321) B839321
theorem B13732355 : Blo 247818 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B953441 : Blo 247818 953441 := bstep (se 2 (by rfl) ⟨357540, by rfl⟩ : syracuseStep 953441 = 715081) B715081
theorem B3411197 : Blo 247818 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B560555 : Blo 247818 560555 := bstep (se 1 (by rfl) ⟨420416, by rfl⟩ : syracuseStep 560555 = 840833) B840833
theorem B954139 : Blo 247818 954139 := bstep (se 1 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 954139 = 1431209) B1431209
theorem B561851 : Blo 247818 561851 := bstep (se 1 (by rfl) ⟨421388, by rfl⟩ : syracuseStep 561851 = 842777) B842777
theorem B955111 : Blo 247818 955111 := bstep (se 1 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 955111 = 1432667) B1432667
theorem B561959 : Blo 247818 561959 := bstep (se 1 (by rfl) ⟨421469, by rfl⟩ : syracuseStep 561959 = 842939) B842939
theorem B562247 : Blo 247818 562247 := bstep (se 1 (by rfl) ⟨421685, by rfl⟩ : syracuseStep 562247 = 843371) B843371
theorem B1906091 : Blo 247818 1906091 := bstep (se 1 (by rfl) ⟨1429568, by rfl⟩ : syracuseStep 1906091 = 2859137) B2859137
theorem B628519 : Blo 247818 628519 := bstep (se 1 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 628519 = 942779) B942779
theorem B628843 : Blo 247818 628843 := bstep (se 1 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 628843 = 943265) B943265
theorem B563327 : Blo 247818 563327 := bstep (se 1 (by rfl) ⟨422495, by rfl⟩ : syracuseStep 563327 = 844991) B844991
theorem B596585 : Blo 247818 596585 := bstep (se 2 (by rfl) ⟨223719, by rfl⟩ : syracuseStep 596585 = 447439) B447439
theorem B1415879 : Blo 247818 1415879 := bstep (se 1 (by rfl) ⟨1061909, by rfl⟩ : syracuseStep 1415879 = 2123819) B2123819
theorem B629815 : Blo 247818 629815 := bstep (se 1 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 629815 = 944723) B944723
theorem B630089 : Blo 247818 630089 := bstep (se 2 (by rfl) ⟨236283, by rfl⟩ : syracuseStep 630089 = 472567) B472567
theorem B9182929 : Blo 247818 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B4530167 : Blo 247818 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B631547 : Blo 247818 631547 := bstep (se 1 (by rfl) ⟨473660, by rfl⟩ : syracuseStep 631547 = 947321) B947321
theorem B632063 : Blo 247818 632063 := bstep (se 1 (by rfl) ⟨474047, by rfl⟩ : syracuseStep 632063 = 948095) B948095
theorem B796061 : Blo 247818 796061 := bstep (se 3 (by rfl) ⟨149261, by rfl⟩ : syracuseStep 796061 = 298523) B298523
theorem B632731 : Blo 247818 632731 := bstep (se 1 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 632731 = 949097) B949097
theorem B1058953 : Blo 247818 1058953 := bstep (se 2 (by rfl) ⟨397107, by rfl⟩ : syracuseStep 1058953 = 794215) B794215
theorem B633167 : Blo 247818 633167 := bstep (se 1 (by rfl) ⟨474875, by rfl⟩ : syracuseStep 633167 = 949751) B949751
theorem B8104475 : Blo 247818 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B535337 : Blo 247818 535337 := bstep (se 2 (by rfl) ⟨200751, by rfl⟩ : syracuseStep 535337 = 401503) B401503
theorem B4533083 : Blo 247818 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B371849 : Blo 247818 371849 := bstep (se 2 (by rfl) ⟨139443, by rfl⟩ : syracuseStep 371849 = 278887) B278887
theorem B896147 : Blo 247818 896147 := bstep (se 1 (by rfl) ⟨672110, by rfl⟩ : syracuseStep 896147 = 1344221) B1344221
theorem B371903 : Blo 247818 371903 := bstep (se 1 (by rfl) ⟨278927, by rfl⟩ : syracuseStep 371903 = 557855) B557855
theorem B1060285 : Blo 247818 1060285 := bstep (se 3 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 1060285 = 397607) B397607
theorem B601967 : Blo 247818 601967 := bstep (se 1 (by rfl) ⟨451475, by rfl⟩ : syracuseStep 601967 = 902951) B902951
theorem B471071 : Blo 247818 471071 := bstep (se 1 (by rfl) ⟨353303, by rfl⟩ : syracuseStep 471071 = 706607) B706607
theorem B1912895 : Blo 247818 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B635323 : Blo 247818 635323 := bstep (se 1 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 635323 = 952985) B952985
theorem B1061363 : Blo 247818 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1192553 : Blo 247818 1192553 := bstep (se 2 (by rfl) ⟨447207, by rfl⟩ : syracuseStep 1192553 = 894415) B894415
theorem B1061687 : Blo 247818 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B897961 : Blo 247818 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B635951 : Blo 247818 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B537695 : Blo 247818 537695 := bstep (se 1 (by rfl) ⟨403271, by rfl⟩ : syracuseStep 537695 = 806543) B806543
theorem B472225 : Blo 247818 472225 := bstep (se 2 (by rfl) ⟨177084, by rfl⟩ : syracuseStep 472225 = 354169) B354169
theorem B4797731 : Blo 247818 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B374087 : Blo 247818 374087 := bstep (se 1 (by rfl) ⟨280565, by rfl⟩ : syracuseStep 374087 = 561131) B561131
theorem B1979873 : Blo 247818 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B636407 : Blo 247818 636407 := bstep (se 1 (by rfl) ⟨477305, by rfl⟩ : syracuseStep 636407 = 954611) B954611
theorem B1030043 : Blo 247818 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B6109111 : Blo 247818 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B505835 : Blo 247818 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B636923 : Blo 247818 636923 := bstep (se 1 (by rfl) ⟨477692, by rfl⟩ : syracuseStep 636923 = 955385) B955385
theorem B1063019 : Blo 247818 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B1882277 : Blo 247818 1882277 := bstep (se 4 (by rfl) ⟨176463, by rfl⟩ : syracuseStep 1882277 = 352927) B352927
theorem B1259711 : Blo 247818 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B1161503 : Blo 247818 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B1423919 : Blo 247818 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B62798611 : Blo 247818 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B375689 : Blo 247818 375689 := bstep (se 2 (by rfl) ⟨140883, by rfl⟩ : syracuseStep 375689 = 281767) B281767
theorem B474025 : Blo 247818 474025 := bstep (se 2 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 474025 = 355519) B355519
theorem B1588481 : Blo 247818 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B376457 : Blo 247818 376457 := bstep (se 2 (by rfl) ⟨141171, by rfl⟩ : syracuseStep 376457 = 282343) B282343
theorem B2440955 : Blo 247818 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B507667 : Blo 247818 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B376895 : Blo 247818 376895 := bstep (se 1 (by rfl) ⟨282671, by rfl⟩ : syracuseStep 376895 = 565343) B565343
theorem B376991 : Blo 247818 376991 := bstep (se 1 (by rfl) ⟨282743, by rfl⟩ : syracuseStep 376991 = 565487) B565487
theorem B901307 : Blo 247818 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B377243 : Blo 247818 377243 := bstep (se 1 (by rfl) ⟨282932, by rfl⟩ : syracuseStep 377243 = 565865) B565865
theorem B475703 : Blo 247818 475703 := bstep (se 1 (by rfl) ⟨356777, by rfl⟩ : syracuseStep 475703 = 713555) B713555
theorem B574171 : Blo 247818 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B377663 : Blo 247818 377663 := bstep (se 1 (by rfl) ⟨283247, by rfl⟩ : syracuseStep 377663 = 566495) B566495
theorem B3589073 : Blo 247818 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B377947 : Blo 247818 377947 := bstep (se 1 (by rfl) ⟨283460, by rfl⟩ : syracuseStep 377947 = 566921) B566921
theorem B3032761 : Blo 247818 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B477161 : Blo 247818 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B247879 : Blo 247818 247879 := bstep (se 1 (by rfl) ⟨185909, by rfl⟩ : syracuseStep 247879 = 371819) B371819
theorem B248039 : Blo 247818 248039 := bstep (se 1 (by rfl) ⟨186029, by rfl⟩ : syracuseStep 248039 = 372059) B372059
theorem B248059 : Blo 247818 248059 := bstep (se 1 (by rfl) ⟨186044, by rfl⟩ : syracuseStep 248059 = 372089) B372089
theorem B248063 : Blo 247818 248063 := bstep (se 1 (by rfl) ⟨186047, by rfl⟩ : syracuseStep 248063 = 372095) B372095
theorem B248219 : Blo 247818 248219 := bstep (se 1 (by rfl) ⟨186164, by rfl⟩ : syracuseStep 248219 = 372329) B372329
theorem B477647 : Blo 247818 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B248479 : Blo 247818 248479 := bstep (se 1 (by rfl) ⟨186359, by rfl⟩ : syracuseStep 248479 = 372719) B372719
theorem B248559 : Blo 247818 248559 := bstep (se 1 (by rfl) ⟨186419, by rfl⟩ : syracuseStep 248559 = 372839) B372839
theorem B2018047 : Blo 247818 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B248639 : Blo 247818 248639 := bstep (se 1 (by rfl) ⟨186479, by rfl⟩ : syracuseStep 248639 = 372959) B372959
theorem B248679 : Blo 247818 248679 := bstep (se 1 (by rfl) ⟨186509, by rfl⟩ : syracuseStep 248679 = 373019) B373019
theorem B248943 : Blo 247818 248943 := bstep (se 1 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 248943 = 373415) B373415
theorem B249023 : Blo 247818 249023 := bstep (se 1 (by rfl) ⟨186767, by rfl⟩ : syracuseStep 249023 = 373535) B373535
theorem B249039 : Blo 247818 249039 := bstep (se 1 (by rfl) ⟨186779, by rfl⟩ : syracuseStep 249039 = 373559) B373559
theorem B249115 : Blo 247818 249115 := bstep (se 1 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 249115 = 373673) B373673
theorem B249159 : Blo 247818 249159 := bstep (se 1 (by rfl) ⟨186869, by rfl⟩ : syracuseStep 249159 = 373739) B373739
theorem B839051 : Blo 247818 839051 := bstep (se 1 (by rfl) ⟨629288, by rfl⟩ : syracuseStep 839051 = 1258577) B1258577
theorem B249343 : Blo 247818 249343 := bstep (se 1 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 249343 = 374015) B374015
theorem B249371 : Blo 247818 249371 := bstep (se 1 (by rfl) ⟨187028, by rfl⟩ : syracuseStep 249371 = 374057) B374057
theorem B4541989 : Blo 247818 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B282271 : Blo 247818 282271 := bstep (se 1 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 282271 = 423407) B423407
theorem B2150063 : Blo 247818 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B249767 : Blo 247818 249767 := bstep (se 1 (by rfl) ⟨187325, by rfl⟩ : syracuseStep 249767 = 374651) B374651
theorem B249791 : Blo 247818 249791 := bstep (se 1 (by rfl) ⟨187343, by rfl⟩ : syracuseStep 249791 = 374687) B374687
theorem B249927 : Blo 247818 249927 := bstep (se 1 (by rfl) ⟨187445, by rfl⟩ : syracuseStep 249927 = 374891) B374891
theorem B249947 : Blo 247818 249947 := bstep (se 1 (by rfl) ⟨187460, by rfl⟩ : syracuseStep 249947 = 374921) B374921
theorem B1134731 : Blo 247818 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B250047 : Blo 247818 250047 := bstep (se 1 (by rfl) ⟨187535, by rfl⟩ : syracuseStep 250047 = 375071) B375071
theorem B709033 : Blo 247818 709033 := bstep (se 2 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 709033 = 531775) B531775
theorem B250495 : Blo 247818 250495 := bstep (se 1 (by rfl) ⟨187871, by rfl⟩ : syracuseStep 250495 = 375743) B375743
theorem B250527 : Blo 247818 250527 := bstep (se 1 (by rfl) ⟨187895, by rfl⟩ : syracuseStep 250527 = 375791) B375791
theorem B709307 : Blo 247818 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B250651 : Blo 247818 250651 := bstep (se 1 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 250651 = 375977) B375977
theorem B840671 : Blo 247818 840671 := bstep (se 1 (by rfl) ⟨630503, by rfl⟩ : syracuseStep 840671 = 1261007) B1261007
theorem B250911 : Blo 247818 250911 := bstep (se 1 (by rfl) ⟨188183, by rfl⟩ : syracuseStep 250911 = 376367) B376367
theorem B250927 : Blo 247818 250927 := bstep (se 1 (by rfl) ⟨188195, by rfl⟩ : syracuseStep 250927 = 376391) B376391
theorem B250983 : Blo 247818 250983 := bstep (se 1 (by rfl) ⟨188237, by rfl⟩ : syracuseStep 250983 = 376475) B376475
theorem B251047 : Blo 247818 251047 := bstep (se 1 (by rfl) ⟨188285, by rfl⟩ : syracuseStep 251047 = 376571) B376571
theorem B251359 : Blo 247818 251359 := bstep (se 1 (by rfl) ⟨188519, by rfl⟩ : syracuseStep 251359 = 377039) B377039
theorem B841211 : Blo 247818 841211 := bstep (se 1 (by rfl) ⟨630908, by rfl⟩ : syracuseStep 841211 = 1261817) B1261817
theorem B251815 : Blo 247818 251815 := bstep (se 1 (by rfl) ⟨188861, by rfl⟩ : syracuseStep 251815 = 377723) B377723
theorem B2316671 : Blo 247818 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B842183 : Blo 247818 842183 := bstep (se 1 (by rfl) ⟨631637, by rfl⟩ : syracuseStep 842183 = 1263275) B1263275
theorem B842237 : Blo 247818 842237 := bstep (se 3 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 842237 = 315839) B315839
theorem B51534863 : Blo 247818 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B12902003 : Blo 247818 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B712415 : Blo 247818 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B1269755 : Blo 247818 1269755 := bstep (se 1 (by rfl) ⟨952316, by rfl⟩ : syracuseStep 1269755 = 1904633) B1904633
theorem B2383951 : Blo 247818 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B843965 : Blo 247818 843965 := bstep (se 3 (by rfl) ⟨158243, by rfl⟩ : syracuseStep 843965 = 316487) B316487
theorem B844127 : Blo 247818 844127 := bstep (se 1 (by rfl) ⟨633095, by rfl⟩ : syracuseStep 844127 = 1266191) B1266191
theorem B4121351 : Blo 247818 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B1270889 : Blo 247818 1270889 := bstep (se 2 (by rfl) ⟨476583, by rfl⟩ : syracuseStep 1270889 = 953167) B953167
theorem B1894427 : Blo 247818 1894427 := bstep (se 1 (by rfl) ⟨1420820, by rfl⟩ : syracuseStep 1894427 = 2841641) B2841641
theorem B2385949 : Blo 247818 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B421247 : Blo 247818 421247 := bstep (se 1 (by rfl) ⟨315935, by rfl⟩ : syracuseStep 421247 = 631871) B631871
theorem B847367 : Blo 247818 847367 := bstep (se 1 (by rfl) ⟨635525, by rfl⟩ : syracuseStep 847367 = 1271051) B1271051
theorem B945695 : Blo 247818 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B847583 : Blo 247818 847583 := bstep (se 1 (by rfl) ⟨635687, by rfl⟩ : syracuseStep 847583 = 1271375) B1271375
theorem B946151 : Blo 247818 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B422185 : Blo 247818 422185 := bstep (se 2 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 422185 = 316639) B316639
theorem B20443529 : Blo 247818 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B848447 : Blo 247818 848447 := bstep (se 1 (by rfl) ⟨636335, by rfl⟩ : syracuseStep 848447 = 1272671) B1272671
theorem B2028169 : Blo 247818 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B946849 : Blo 247818 946849 := bstep (se 2 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 946849 = 710137) B710137
theorem B947335 : Blo 247818 947335 := bstep (se 1 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 947335 = 1421003) B1421003
theorem B423103 : Blo 247818 423103 := bstep (se 1 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 423103 = 634655) B634655
theorem B2029495 : Blo 247818 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B1604063 : Blo 247818 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B2030507 : Blo 247818 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B1802209 : Blo 247818 1802209 := bstep (se 2 (by rfl) ⟨675828, by rfl⟩ : syracuseStep 1802209 = 1351657) B1351657
theorem B3178601 : Blo 247818 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B9175355 : Blo 247818 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B2392715 : Blo 247818 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B559367 : Blo 247818 559367 := bstep (se 1 (by rfl) ⟨419525, by rfl⟩ : syracuseStep 559367 = 839051) B839051
theorem B3181265 : Blo 247818 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B756487 : Blo 247818 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B1411937 : Blo 247818 1411937 := bstep (se 2 (by rfl) ⟨529476, by rfl⟩ : syracuseStep 1411937 = 1058953) B1058953
theorem B560447 : Blo 247818 560447 := bstep (se 1 (by rfl) ⟨420335, by rfl⟩ : syracuseStep 560447 = 840671) B840671
theorem B560807 : Blo 247818 560807 := bstep (se 1 (by rfl) ⟨420605, by rfl⟩ : syracuseStep 560807 = 841211) B841211
theorem B2690729 : Blo 247818 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B1544447 : Blo 247818 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B561455 : Blo 247818 561455 := bstep (se 1 (by rfl) ⟨421091, by rfl⟩ : syracuseStep 561455 = 842183) B842183
theorem B561491 : Blo 247818 561491 := bstep (se 1 (by rfl) ⟨421118, by rfl⟩ : syracuseStep 561491 = 842237) B842237
theorem B397723 : Blo 247818 397723 := bstep (se 1 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 397723 = 596585) B596585
theorem B1413713 : Blo 247818 1413713 := bstep (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) B1060285
theorem B3020111 : Blo 247818 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B562643 : Blo 247818 562643 := bstep (se 1 (by rfl) ⟨421982, by rfl⟩ : syracuseStep 562643 = 843965) B843965
theorem B562751 : Blo 247818 562751 := bstep (se 1 (by rfl) ⟨422063, by rfl⟩ : syracuseStep 562751 = 844127) B844127
theorem B562913 : Blo 247818 562913 := bstep (se 2 (by rfl) ⟨211092, by rfl⟩ : syracuseStep 562913 = 422185) B422185
theorem B530707 : Blo 247818 530707 := bstep (se 1 (by rfl) ⟨398030, by rfl⟩ : syracuseStep 530707 = 796061) B796061
theorem B629633 : Blo 247818 629633 := bstep (se 2 (by rfl) ⟨236112, by rfl⟩ : syracuseStep 629633 = 472225) B472225
theorem B564137 : Blo 247818 564137 := bstep (se 2 (by rfl) ⟨211551, by rfl⟩ : syracuseStep 564137 = 423103) B423103
theorem B3022055 : Blo 247818 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B597431 : Blo 247818 597431 := bstep (se 1 (by rfl) ⟨448073, by rfl⟩ : syracuseStep 597431 = 896147) B896147
theorem B564911 : Blo 247818 564911 := bstep (se 1 (by rfl) ⟨423683, by rfl⟩ : syracuseStep 564911 = 847367) B847367
theorem B630463 : Blo 247818 630463 := bstep (se 1 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 630463 = 945695) B945695
theorem B565055 : Blo 247818 565055 := bstep (se 1 (by rfl) ⟨423791, by rfl⟩ : syracuseStep 565055 = 847583) B847583
theorem B401311 : Blo 247818 401311 := bstep (se 1 (by rfl) ⟨300983, by rfl⟩ : syracuseStep 401311 = 601967) B601967
theorem B630767 : Blo 247818 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B565631 : Blo 247818 565631 := bstep (se 1 (by rfl) ⟨424223, by rfl⟩ : syracuseStep 565631 = 848447) B848447
theorem B795035 : Blo 247818 795035 := bstep (se 1 (by rfl) ⟨596276, by rfl⟩ : syracuseStep 795035 = 1192553) B1192553
theorem B1319915 : Blo 247818 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B83731481 : Blo 247818 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B632033 : Blo 247818 632033 := bstep (se 2 (by rfl) ⟨237012, by rfl⟩ : syracuseStep 632033 = 474025) B474025
theorem B337223 : Blo 247818 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B1254851 : Blo 247818 1254851 := bstep (se 1 (by rfl) ⟨941138, by rfl⟩ : syracuseStep 1254851 = 1882277) B1882277
theorem B1353671 : Blo 247818 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B1058987 : Blo 247818 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B2402945 : Blo 247818 2402945 := bstep (se 2 (by rfl) ⟨901104, by rfl⟩ : syracuseStep 2402945 = 1802209) B1802209
theorem B568043 : Blo 247818 568043 := bstep (se 1 (by rfl) ⟨426032, by rfl⟩ : syracuseStep 568043 = 852065) B852065
theorem B5090039 : Blo 247818 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B600871 : Blo 247818 600871 := bstep (se 1 (by rfl) ⟨450653, by rfl⟩ : syracuseStep 600871 = 901307) B901307
theorem B633683 : Blo 247818 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B1355591 : Blo 247818 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B962543 : Blo 247818 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B569339 : Blo 247818 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B372791 : Blo 247818 372791 := bstep (se 1 (by rfl) ⟨279593, by rfl⟩ : syracuseStep 372791 = 559187) B559187
theorem B503929 : Blo 247818 503929 := bstep (se 2 (by rfl) ⟨188973, by rfl⟩ : syracuseStep 503929 = 377947) B377947
theorem B1421459 : Blo 247818 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B373031 : Blo 247818 373031 := bstep (se 1 (by rfl) ⟨279773, by rfl⟩ : syracuseStep 373031 = 559547) B559547
theorem B9154903 : Blo 247818 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B635627 : Blo 247818 635627 := bstep (se 1 (by rfl) ⟨476720, by rfl⟩ : syracuseStep 635627 = 953441) B953441
theorem B2274131 : Blo 247818 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B4043681 : Blo 247818 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B373703 : Blo 247818 373703 := bstep (se 1 (by rfl) ⟨280277, by rfl⟩ : syracuseStep 373703 = 560555) B560555
theorem B472871 : Blo 247818 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B374567 : Blo 247818 374567 := bstep (se 1 (by rfl) ⟨280925, by rfl⟩ : syracuseStep 374567 = 561851) B561851
theorem B374639 : Blo 247818 374639 := bstep (se 1 (by rfl) ⟨280979, by rfl⟩ : syracuseStep 374639 = 561959) B561959
theorem B374831 : Blo 247818 374831 := bstep (se 1 (by rfl) ⟨281123, by rfl⟩ : syracuseStep 374831 = 562247) B562247
theorem B3062245 : Blo 247818 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B375551 : Blo 247818 375551 := bstep (se 1 (by rfl) ⟨281663, by rfl⟩ : syracuseStep 375551 = 563327) B563327
theorem B34356575 : Blo 247818 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B376361 : Blo 247818 376361 := bstep (se 2 (by rfl) ⟨141135, by rfl⟩ : syracuseStep 376361 = 282271) B282271
theorem B8601335 : Blo 247818 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B2704225 : Blo 247818 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B1262465 : Blo 247818 1262465 := bstep (se 2 (by rfl) ⟨473424, by rfl⟩ : syracuseStep 1262465 = 946849) B946849
theorem B1197281 : Blo 247818 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B1262951 : Blo 247818 1262951 := bstep (se 1 (by rfl) ⟨947213, by rfl⟩ : syracuseStep 1262951 = 1894427) B1894427
theorem B21611933 : Blo 247818 21611933 := bstep (se 3 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 21611933 = 8104475) B8104475
theorem B1263113 : Blo 247818 1263113 := bstep (se 2 (by rfl) ⟨473667, by rfl⟩ : syracuseStep 1263113 = 947335) B947335
theorem B247899 : Blo 247818 247899 := bstep (se 1 (by rfl) ⟨185924, by rfl⟩ : syracuseStep 247899 = 371849) B371849
theorem B247935 : Blo 247818 247935 := bstep (se 1 (by rfl) ⟨185951, by rfl⟩ : syracuseStep 247935 = 371903) B371903
theorem B280831 : Blo 247818 280831 := bstep (se 1 (by rfl) ⟨210623, by rfl⟩ : syracuseStep 280831 = 421247) B421247
theorem B838025 : Blo 247818 838025 := bstep (se 2 (by rfl) ⟨314259, by rfl⟩ : syracuseStep 838025 = 628519) B628519
theorem B2705993 : Blo 247818 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B8145481 : Blo 247818 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B314047 : Blo 247818 314047 := bstep (se 1 (by rfl) ⟨235535, by rfl⟩ : syracuseStep 314047 = 471071) B471071
theorem B838457 : Blo 247818 838457 := bstep (se 2 (by rfl) ⟨314421, by rfl⟩ : syracuseStep 838457 = 628843) B628843
theorem B707575 : Blo 247818 707575 := bstep (se 1 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 707575 = 1061363) B1061363
theorem B707791 : Blo 247818 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B3198487 : Blo 247818 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B249391 : Blo 247818 249391 := bstep (se 1 (by rfl) ⟨187043, by rfl⟩ : syracuseStep 249391 = 374087) B374087
theorem B708679 : Blo 247818 708679 := bstep (se 1 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 708679 = 1063019) B1063019
theorem B839753 : Blo 247818 839753 := bstep (se 2 (by rfl) ⟨314907, by rfl⟩ : syracuseStep 839753 = 629815) B629815
theorem B839807 : Blo 247818 839807 := bstep (se 1 (by rfl) ⟨629855, by rfl⟩ : syracuseStep 839807 = 1259711) B1259711
theorem B774335 : Blo 247818 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B1069375 : Blo 247818 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B250459 : Blo 247818 250459 := bstep (se 1 (by rfl) ⟨187844, by rfl⟩ : syracuseStep 250459 = 375689) B375689
theorem B12243905 : Blo 247818 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B676889 : Blo 247818 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B250971 : Blo 247818 250971 := bstep (se 1 (by rfl) ⟨188228, by rfl⟩ : syracuseStep 250971 = 376457) B376457
theorem B1627303 : Blo 247818 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B251263 : Blo 247818 251263 := bstep (se 1 (by rfl) ⟨188447, by rfl⟩ : syracuseStep 251263 = 376895) B376895
theorem B251327 : Blo 247818 251327 := bstep (se 1 (by rfl) ⟨188495, by rfl⟩ : syracuseStep 251327 = 376991) B376991
theorem B2446843 : Blo 247818 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B251495 : Blo 247818 251495 := bstep (se 1 (by rfl) ⟨188621, by rfl⟩ : syracuseStep 251495 = 377243) B377243
theorem B317135 : Blo 247818 317135 := bstep (se 1 (by rfl) ⟨237851, by rfl⟩ : syracuseStep 317135 = 475703) B475703
theorem B251775 : Blo 247818 251775 := bstep (se 1 (by rfl) ⟨188831, by rfl⟩ : syracuseStep 251775 = 377663) B377663
theorem B2709625 : Blo 247818 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B318107 : Blo 247818 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B318431 : Blo 247818 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B1433375 : Blo 247818 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B843641 : Blo 247818 843641 := bstep (se 2 (by rfl) ⟨316365, by rfl⟩ : syracuseStep 843641 = 632731) B632731
theorem B30629825 : Blo 247818 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B1270727 : Blo 247818 1270727 := bstep (se 1 (by rfl) ⟨953045, by rfl⟩ : syracuseStep 1270727 = 1906091) B1906091
theorem B943919 : Blo 247818 943919 := bstep (se 1 (by rfl) ⟨707939, by rfl⟩ : syracuseStep 943919 = 1415879) B1415879
theorem B6055985 : Blo 247818 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B420059 : Blo 247818 420059 := bstep (se 1 (by rfl) ⟨315044, by rfl⟩ : syracuseStep 420059 = 630089) B630089
theorem B1272185 : Blo 247818 1272185 := bstep (se 2 (by rfl) ⟨477069, by rfl⟩ : syracuseStep 1272185 = 954139) B954139
theorem B2746781 : Blo 247818 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B846503 : Blo 247818 846503 := bstep (se 1 (by rfl) ⟨634877, by rfl⟩ : syracuseStep 846503 = 1269755) B1269755
theorem B421031 : Blo 247818 421031 := bstep (se 1 (by rfl) ⟨315773, by rfl⟩ : syracuseStep 421031 = 631547) B631547
theorem B2747567 : Blo 247818 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B945377 : Blo 247818 945377 := bstep (se 2 (by rfl) ⟨354516, by rfl⟩ : syracuseStep 945377 = 709033) B709033
theorem B847097 : Blo 247818 847097 := bstep (se 2 (by rfl) ⟨317661, by rfl⟩ : syracuseStep 847097 = 635323) B635323
theorem B847259 : Blo 247818 847259 := bstep (se 1 (by rfl) ⟨635444, by rfl⟩ : syracuseStep 847259 = 1270889) B1270889
theorem B421375 : Blo 247818 421375 := bstep (se 1 (by rfl) ⟨316031, by rfl⟩ : syracuseStep 421375 = 632063) B632063
theorem B1273481 : Blo 247818 1273481 := bstep (se 2 (by rfl) ⟨477555, by rfl⟩ : syracuseStep 1273481 = 955111) B955111
theorem B422111 : Blo 247818 422111 := bstep (se 1 (by rfl) ⟨316583, by rfl⟩ : syracuseStep 422111 = 633167) B633167
theorem B356891 : Blo 247818 356891 := bstep (se 1 (by rfl) ⟨267668, by rfl⟩ : syracuseStep 356891 = 535337) B535337
theorem B1275263 : Blo 247818 1275263 := bstep (se 1 (by rfl) ⟨956447, by rfl⟩ : syracuseStep 1275263 = 1912895) B1912895
theorem B13629019 : Blo 247818 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B423967 : Blo 247818 423967 := bstep (se 1 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 423967 = 635951) B635951
theorem B358463 : Blo 247818 358463 := bstep (se 1 (by rfl) ⟨268847, by rfl⟩ : syracuseStep 358463 = 537695) B537695
theorem B424271 : Blo 247818 424271 := bstep (se 1 (by rfl) ⟨318203, by rfl⟩ : syracuseStep 424271 = 636407) B636407
theorem B424615 : Blo 247818 424615 := bstep (se 1 (by rfl) ⟨318461, by rfl⟩ : syracuseStep 424615 = 636923) B636923
theorem B949279 : Blo 247818 949279 := bstep (se 1 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 949279 = 1423919) B1423919
theorem B1899773 : Blo 247818 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B3605633 : Blo 247818 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B951709 : Blo 247818 951709 := bstep (se 3 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 951709 = 356891) B356891
theorem B558683 : Blo 247818 558683 := bstep (se 1 (by rfl) ⟨419012, by rfl⟩ : syracuseStep 558683 = 838025) B838025
theorem B1803995 : Blo 247818 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B558971 : Blo 247818 558971 := bstep (se 1 (by rfl) ⟨419228, by rfl⟩ : syracuseStep 558971 = 838457) B838457
theorem B559835 : Blo 247818 559835 := bstep (se 1 (by rfl) ⟨419876, by rfl⟩ : syracuseStep 559835 = 839753) B839753
theorem B559871 : Blo 247818 559871 := bstep (se 1 (by rfl) ⟨419903, by rfl⟩ : syracuseStep 559871 = 839807) B839807
theorem B8162603 : Blo 247818 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B561833 : Blo 247818 561833 := bstep (se 2 (by rfl) ⟨210687, by rfl⟩ : syracuseStep 561833 = 421375) B421375
theorem B4264649 : Blo 247818 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B398287 : Blo 247818 398287 := bstep (se 1 (by rfl) ⟨298715, by rfl⟩ : syracuseStep 398287 = 597431) B597431
theorem B955583 : Blo 247818 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B562427 : Blo 247818 562427 := bstep (se 1 (by rfl) ⟨421820, by rfl⟩ : syracuseStep 562427 = 843641) B843641
theorem B20419883 : Blo 247818 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B955901 : Blo 247818 955901 := bstep (se 3 (by rfl) ⟨179231, by rfl⟩ : syracuseStep 955901 = 358463) B358463
theorem B530297 : Blo 247818 530297 := bstep (se 2 (by rfl) ⟨198861, by rfl⟩ : syracuseStep 530297 = 397723) B397723
theorem B629279 : Blo 247818 629279 := bstep (se 1 (by rfl) ⟨471959, by rfl⟩ : syracuseStep 629279 = 943919) B943919
theorem B4037323 : Blo 247818 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B2169737 : Blo 247818 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B564335 : Blo 247818 564335 := bstep (se 1 (by rfl) ⟨423251, by rfl⟩ : syracuseStep 564335 = 846503) B846503
theorem B630251 : Blo 247818 630251 := bstep (se 1 (by rfl) ⟨472688, by rfl⟩ : syracuseStep 630251 = 945377) B945377
theorem B564731 : Blo 247818 564731 := bstep (se 1 (by rfl) ⟨423548, by rfl⟩ : syracuseStep 564731 = 847097) B847097
theorem B564839 : Blo 247818 564839 := bstep (se 1 (by rfl) ⟨423629, by rfl⟩ : syracuseStep 564839 = 847259) B847259
theorem B565289 : Blo 247818 565289 := bstep (se 2 (by rfl) ⟨211983, by rfl⟩ : syracuseStep 565289 = 423967) B423967
theorem B3612833 : Blo 247818 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B1516087 : Blo 247818 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B2695787 : Blo 247818 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B566153 : Blo 247818 566153 := bstep (se 2 (by rfl) ⟨212307, by rfl⟩ : syracuseStep 566153 = 424615) B424615
theorem B535081 : Blo 247818 535081 := bstep (se 2 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 535081 = 401311) B401311
theorem B798187 : Blo 247818 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B372911 : Blo 247818 372911 := bstep (se 1 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 372911 = 559367) B559367
theorem B373631 : Blo 247818 373631 := bstep (se 1 (by rfl) ⟨280223, by rfl⟩ : syracuseStep 373631 = 560447) B560447
theorem B373871 : Blo 247818 373871 := bstep (se 1 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 373871 = 560807) B560807
theorem B3519773 : Blo 247818 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B1029631 : Blo 247818 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B374303 : Blo 247818 374303 := bstep (se 1 (by rfl) ⟨280727, by rfl⟩ : syracuseStep 374303 = 561455) B561455
theorem B374327 : Blo 247818 374327 := bstep (se 1 (by rfl) ⟨280745, by rfl⟩ : syracuseStep 374327 = 561491) B561491
theorem B374441 : Blo 247818 374441 := bstep (se 2 (by rfl) ⟨140415, by rfl⟩ : syracuseStep 374441 = 280831) B280831
theorem B10860641 : Blo 247818 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B899261 : Blo 247818 899261 := bstep (se 3 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 899261 = 337223) B337223
theorem B2013407 : Blo 247818 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B375095 : Blo 247818 375095 := bstep (se 1 (by rfl) ⟨281321, by rfl⟩ : syracuseStep 375095 = 562643) B562643
theorem B375167 : Blo 247818 375167 := bstep (se 1 (by rfl) ⟨281375, by rfl⟩ : syracuseStep 375167 = 562751) B562751
theorem B801161 : Blo 247818 801161 := bstep (se 2 (by rfl) ⟨300435, by rfl⟩ : syracuseStep 801161 = 600871) B600871
theorem B375275 : Blo 247818 375275 := bstep (se 1 (by rfl) ⟨281456, by rfl⟩ : syracuseStep 375275 = 562913) B562913
theorem B376091 : Blo 247818 376091 := bstep (se 1 (by rfl) ⟨282068, by rfl⟩ : syracuseStep 376091 = 564137) B564137
theorem B2014703 : Blo 247818 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B376607 : Blo 247818 376607 := bstep (se 1 (by rfl) ⟨282455, by rfl⟩ : syracuseStep 376607 = 564911) B564911
theorem B376703 : Blo 247818 376703 := bstep (se 1 (by rfl) ⟨282527, by rfl⟩ : syracuseStep 376703 = 565055) B565055
theorem B671905 : Blo 247818 671905 := bstep (se 2 (by rfl) ⟨251964, by rfl⟩ : syracuseStep 671905 = 503929) B503929
theorem B377087 : Blo 247818 377087 := bstep (se 1 (by rfl) ⟨282815, by rfl⟩ : syracuseStep 377087 = 565631) B565631
theorem B1425833 : Blo 247818 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B12206537 : Blo 247818 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B55820987 : Blo 247818 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B836567 : Blo 247818 836567 := bstep (se 1 (by rfl) ⟨627425, by rfl⟩ : syracuseStep 836567 = 1254851) B1254851
theorem B902447 : Blo 247818 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B705991 : Blo 247818 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B280039 : Blo 247818 280039 := bstep (se 1 (by rfl) ⟨210029, by rfl⟩ : syracuseStep 280039 = 420059) B420059
theorem B378695 : Blo 247818 378695 := bstep (se 1 (by rfl) ⟨284021, by rfl⟩ : syracuseStep 378695 = 568043) B568043
theorem B3393359 : Blo 247818 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B3262457 : Blo 247818 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B280687 : Blo 247818 280687 := bstep (se 1 (by rfl) ⟨210515, by rfl⟩ : syracuseStep 280687 = 421031) B421031
theorem B18172025 : Blo 247818 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B903727 : Blo 247818 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B641695 : Blo 247818 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B379559 : Blo 247818 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B248527 : Blo 247818 248527 := bstep (se 1 (by rfl) ⟨186395, by rfl⟩ : syracuseStep 248527 = 372791) B372791
theorem B281407 : Blo 247818 281407 := bstep (se 1 (by rfl) ⟨211055, by rfl⟩ : syracuseStep 281407 = 422111) B422111
theorem B248687 : Blo 247818 248687 := bstep (se 1 (by rfl) ⟨186515, by rfl⟩ : syracuseStep 248687 = 373031) B373031
theorem B707609 : Blo 247818 707609 := bstep (se 2 (by rfl) ⟨265353, by rfl⟩ : syracuseStep 707609 = 530707) B530707
theorem B7326845 : Blo 247818 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B249135 : Blo 247818 249135 := bstep (se 1 (by rfl) ⟨186851, by rfl⟩ : syracuseStep 249135 = 373703) B373703
theorem B4082993 : Blo 247818 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B315247 : Blo 247818 315247 := bstep (se 1 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 315247 = 472871) B472871
theorem B249711 : Blo 247818 249711 := bstep (se 1 (by rfl) ⟨187283, by rfl⟩ : syracuseStep 249711 = 374567) B374567
theorem B249759 : Blo 247818 249759 := bstep (se 1 (by rfl) ⟨187319, by rfl⟩ : syracuseStep 249759 = 374639) B374639
theorem B249887 : Blo 247818 249887 := bstep (se 1 (by rfl) ⟨187415, by rfl⟩ : syracuseStep 249887 = 374831) B374831
theorem B1265705 : Blo 247818 1265705 := bstep (se 2 (by rfl) ⟨474639, by rfl⟩ : syracuseStep 1265705 = 949279) B949279
theorem B282847 : Blo 247818 282847 := bstep (se 1 (by rfl) ⟨212135, by rfl⟩ : syracuseStep 282847 = 424271) B424271
theorem B250367 : Blo 247818 250367 := bstep (se 1 (by rfl) ⟨187775, by rfl⟩ : syracuseStep 250367 = 375551) B375551
theorem B1266515 : Blo 247818 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B840617 : Blo 247818 840617 := bstep (se 2 (by rfl) ⟨315231, by rfl⟩ : syracuseStep 840617 = 630463) B630463
theorem B250907 : Blo 247818 250907 := bstep (se 1 (by rfl) ⟨188180, by rfl⟩ : syracuseStep 250907 = 376361) B376361
theorem B2119067 : Blo 247818 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B6116903 : Blo 247818 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B1595143 : Blo 247818 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B841643 : Blo 247818 841643 := bstep (se 1 (by rfl) ⟨631232, by rfl⟩ : syracuseStep 841643 = 1262465) B1262465
theorem B841967 : Blo 247818 841967 := bstep (se 1 (by rfl) ⟨631475, by rfl⟩ : syracuseStep 841967 = 1262951) B1262951
theorem B14407955 : Blo 247818 14407955 := bstep (se 1 (by rfl) ⟨10805966, by rfl⟩ : syracuseStep 14407955 = 21611933) B21611933
theorem B842075 : Blo 247818 842075 := bstep (se 1 (by rfl) ⟨631556, by rfl⟩ : syracuseStep 842075 = 1263113) B1263113
theorem B2120093 : Blo 247818 2120093 := bstep (se 3 (by rfl) ⟨397517, by rfl⟩ : syracuseStep 2120093 = 795035) B795035
theorem B2120843 : Blo 247818 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B941291 : Blo 247818 941291 := bstep (se 1 (by rfl) ⟨705968, by rfl⟩ : syracuseStep 941291 = 1411937) B1411937
theorem B1793819 : Blo 247818 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B516223 : Blo 247818 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B942475 : Blo 247818 942475 := bstep (se 1 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 942475 = 1413713) B1413713
theorem B451259 : Blo 247818 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B418729 : Blo 247818 418729 := bstep (se 2 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 418729 = 314047) B314047
theorem B1008649 : Blo 247818 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B943433 : Blo 247818 943433 := bstep (se 2 (by rfl) ⟨353787, by rfl⟩ : syracuseStep 943433 = 707575) B707575
theorem B943721 : Blo 247818 943721 := bstep (se 2 (by rfl) ⟨353895, by rfl⟩ : syracuseStep 943721 = 707791) B707791
theorem B845693 : Blo 247818 845693 := bstep (se 3 (by rfl) ⟨158567, by rfl⟩ : syracuseStep 845693 = 317135) B317135
theorem B419755 : Blo 247818 419755 := bstep (se 1 (by rfl) ⟨314816, by rfl⟩ : syracuseStep 419755 = 629633) B629633
theorem B420511 : Blo 247818 420511 := bstep (se 1 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 420511 = 630767) B630767
theorem B944905 : Blo 247818 944905 := bstep (se 2 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 944905 = 708679) B708679
theorem B847151 : Blo 247818 847151 := bstep (se 1 (by rfl) ⟨635363, by rfl⟩ : syracuseStep 847151 = 1270727) B1270727
theorem B421355 : Blo 247818 421355 := bstep (se 1 (by rfl) ⟨316016, by rfl⟩ : syracuseStep 421355 = 632033) B632033
theorem B848123 : Blo 247818 848123 := bstep (se 1 (by rfl) ⟨636092, by rfl⟩ : syracuseStep 848123 = 1272185) B1272185
theorem B1831187 : Blo 247818 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B848285 : Blo 247818 848285 := bstep (se 3 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 848285 = 318107) B318107
theorem B1601963 : Blo 247818 1601963 := bstep (se 1 (by rfl) ⟨1201472, by rfl⟩ : syracuseStep 1601963 = 2402945) B2402945
theorem B422455 : Blo 247818 422455 := bstep (se 1 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 422455 = 633683) B633683
theorem B848987 : Blo 247818 848987 := bstep (se 1 (by rfl) ⟨636740, by rfl⟩ : syracuseStep 848987 = 1273481) B1273481
theorem B849149 : Blo 247818 849149 := bstep (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) B318431
theorem B947639 : Blo 247818 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B423751 : Blo 247818 423751 := bstep (se 1 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 423751 = 635627) B635627
theorem B850175 : Blo 247818 850175 := bstep (se 1 (by rfl) ⟨637631, by rfl⟩ : syracuseStep 850175 = 1275263) B1275263
theorem B22904383 : Blo 247818 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B5734223 : Blo 247818 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B688297 : Blo 247818 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B950555 : Blo 247818 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B557711 : Blo 247818 557711 := bstep (se 1 (by rfl) ⟨418283, by rfl⟩ : syracuseStep 557711 = 836567) B836567
theorem B2262239 : Blo 247818 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B558305 : Blo 247818 558305 := bstep (se 2 (by rfl) ⟨209364, by rfl⟩ : syracuseStep 558305 = 418729) B418729
theorem B1344865 : Blo 247818 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B4884563 : Blo 247818 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B5441735 : Blo 247818 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B2721995 : Blo 247818 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B559673 : Blo 247818 559673 := bstep (se 2 (by rfl) ⟨209877, by rfl⟩ : syracuseStep 559673 = 419755) B419755
theorem B560411 : Blo 247818 560411 := bstep (se 1 (by rfl) ⟨420308, by rfl⟩ : syracuseStep 560411 = 840617) B840617
theorem B560681 : Blo 247818 560681 := bstep (se 2 (by rfl) ⟨210255, by rfl⟩ : syracuseStep 560681 = 420511) B420511
theorem B855593 : Blo 247818 855593 := bstep (se 2 (by rfl) ⟨320847, by rfl⟩ : syracuseStep 855593 = 641695) B641695
theorem B1412711 : Blo 247818 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B561095 : Blo 247818 561095 := bstep (se 1 (by rfl) ⟨420821, by rfl⟩ : syracuseStep 561095 = 841643) B841643
theorem B561311 : Blo 247818 561311 := bstep (se 1 (by rfl) ⟨420983, by rfl⟩ : syracuseStep 561311 = 841967) B841967
theorem B9605303 : Blo 247818 9605303 := bstep (se 1 (by rfl) ⟨7203977, by rfl⟩ : syracuseStep 9605303 = 14407955) B14407955
theorem B561383 : Blo 247818 561383 := bstep (se 1 (by rfl) ⟨421037, by rfl⟩ : syracuseStep 561383 = 842075) B842075
theorem B1413395 : Blo 247818 1413395 := bstep (se 1 (by rfl) ⟨1060046, by rfl⟩ : syracuseStep 1413395 = 2120093) B2120093
theorem B1446491 : Blo 247818 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B1413895 : Blo 247818 1413895 := bstep (se 1 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 1413895 = 2120843) B2120843
theorem B627527 : Blo 247818 627527 := bstep (se 1 (by rfl) ⟨470645, by rfl⟩ : syracuseStep 627527 = 941291) B941291
theorem B300839 : Blo 247818 300839 := bstep (se 1 (by rfl) ⟨225629, by rfl⟩ : syracuseStep 300839 = 451259) B451259
theorem B563273 : Blo 247818 563273 := bstep (se 2 (by rfl) ⟨211227, by rfl⟩ : syracuseStep 563273 = 422455) B422455
theorem B628955 : Blo 247818 628955 := bstep (se 1 (by rfl) ⟨471716, by rfl⟩ : syracuseStep 628955 = 943433) B943433
theorem B629147 : Blo 247818 629147 := bstep (se 1 (by rfl) ⟨471860, by rfl⟩ : syracuseStep 629147 = 943721) B943721
theorem B563795 : Blo 247818 563795 := bstep (se 1 (by rfl) ⟨422846, by rfl⟩ : syracuseStep 563795 = 845693) B845693
theorem B531049 : Blo 247818 531049 := bstep (se 2 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 531049 = 398287) B398287
theorem B564767 : Blo 247818 564767 := bstep (se 1 (by rfl) ⟨423575, by rfl⟩ : syracuseStep 564767 = 847151) B847151
theorem B565001 : Blo 247818 565001 := bstep (se 2 (by rfl) ⟨211875, by rfl⟩ : syracuseStep 565001 = 423751) B423751
theorem B565415 : Blo 247818 565415 := bstep (se 1 (by rfl) ⟨424061, by rfl⟩ : syracuseStep 565415 = 848123) B848123
theorem B1220791 : Blo 247818 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B565523 : Blo 247818 565523 := bstep (se 1 (by rfl) ⟨424142, by rfl⟩ : syracuseStep 565523 = 848285) B848285
theorem B565991 : Blo 247818 565991 := bstep (se 1 (by rfl) ⟨424493, by rfl⟩ : syracuseStep 565991 = 848987) B848987
theorem B566099 : Blo 247818 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B5383097 : Blo 247818 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B631759 : Blo 247818 631759 := bstep (se 1 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 631759 = 947639) B947639
theorem B599507 : Blo 247818 599507 := bstep (se 1 (by rfl) ⟨449630, by rfl⟩ : syracuseStep 599507 = 899261) B899261
theorem B566783 : Blo 247818 566783 := bstep (se 1 (by rfl) ⟨425087, by rfl⟩ : syracuseStep 566783 = 850175) B850175
theorem B534107 : Blo 247818 534107 := bstep (se 1 (by rfl) ⟨400580, by rfl⟩ : syracuseStep 534107 = 801161) B801161
theorem B895873 : Blo 247818 895873 := bstep (se 2 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 895873 = 671905) B671905
theorem B8137691 : Blo 247818 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B1256633 : Blo 247818 1256633 := bstep (se 2 (by rfl) ⟨471237, by rfl⟩ : syracuseStep 1256633 = 942475) B942475
theorem B2403755 : Blo 247818 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B601631 : Blo 247818 601631 := bstep (se 1 (by rfl) ⟨451223, by rfl⟩ : syracuseStep 601631 = 902447) B902447
theorem B372455 : Blo 247818 372455 := bstep (se 1 (by rfl) ⟨279341, by rfl⟩ : syracuseStep 372455 = 558683) B558683
theorem B372647 : Blo 247818 372647 := bstep (se 1 (by rfl) ⟨279485, by rfl⟩ : syracuseStep 372647 = 558971) B558971
theorem B373223 : Blo 247818 373223 := bstep (se 1 (by rfl) ⟨279917, by rfl⟩ : syracuseStep 373223 = 559835) B559835
theorem B373247 : Blo 247818 373247 := bstep (se 1 (by rfl) ⟨279935, by rfl⟩ : syracuseStep 373247 = 559871) B559871
theorem B373385 : Blo 247818 373385 := bstep (se 2 (by rfl) ⟨140019, by rfl⟩ : syracuseStep 373385 = 280039) B280039
theorem B471739 : Blo 247818 471739 := bstep (se 1 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 471739 = 707609) B707609
theorem B374249 : Blo 247818 374249 := bstep (se 2 (by rfl) ⟨140343, by rfl⟩ : syracuseStep 374249 = 280687) B280687
theorem B374555 : Blo 247818 374555 := bstep (se 1 (by rfl) ⟨280916, by rfl⟩ : syracuseStep 374555 = 561833) B561833
theorem B637055 : Blo 247818 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B374951 : Blo 247818 374951 := bstep (se 1 (by rfl) ⟨281213, by rfl⟩ : syracuseStep 374951 = 562427) B562427
theorem B13613255 : Blo 247818 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B637267 : Blo 247818 637267 := bstep (se 1 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 637267 = 955901) B955901
theorem B1259873 : Blo 247818 1259873 := bstep (se 2 (by rfl) ⟨472452, by rfl⟩ : syracuseStep 1259873 = 944905) B944905
theorem B4077935 : Blo 247818 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B375209 : Blo 247818 375209 := bstep (se 2 (by rfl) ⟨140703, by rfl⟩ : syracuseStep 375209 = 281407) B281407
theorem B1064249 : Blo 247818 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B376223 : Blo 247818 376223 := bstep (se 1 (by rfl) ⟨282167, by rfl⟩ : syracuseStep 376223 = 564335) B564335
theorem B376487 : Blo 247818 376487 := bstep (se 1 (by rfl) ⟨282365, by rfl⟩ : syracuseStep 376487 = 564731) B564731
theorem B376559 : Blo 247818 376559 := bstep (se 1 (by rfl) ⟨282419, by rfl⟩ : syracuseStep 376559 = 564839) B564839
theorem B1195879 : Blo 247818 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B8699885 : Blo 247818 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B376859 : Blo 247818 376859 := bstep (se 1 (by rfl) ⟨282644, by rfl⟩ : syracuseStep 376859 = 565289) B565289
theorem B2408555 : Blo 247818 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B377129 : Blo 247818 377129 := bstep (se 2 (by rfl) ⟨141423, by rfl⟩ : syracuseStep 377129 = 282847) B282847
theorem B377435 : Blo 247818 377435 := bstep (se 1 (by rfl) ⟨283076, by rfl⟩ : syracuseStep 377435 = 566153) B566153
theorem B280903 : Blo 247818 280903 := bstep (se 1 (by rfl) ⟨210677, by rfl⟩ : syracuseStep 280903 = 421355) B421355
theorem B248607 : Blo 247818 248607 := bstep (se 1 (by rfl) ⟨186455, by rfl⟩ : syracuseStep 248607 = 372911) B372911
theorem B1067975 : Blo 247818 1067975 := bstep (se 1 (by rfl) ⟨800981, by rfl⟩ : syracuseStep 1067975 = 1601963) B1601963
theorem B249087 : Blo 247818 249087 := bstep (se 1 (by rfl) ⟨186815, by rfl⟩ : syracuseStep 249087 = 373631) B373631
theorem B249247 : Blo 247818 249247 := bstep (se 1 (by rfl) ⟨186935, by rfl⟩ : syracuseStep 249247 = 373871) B373871
theorem B2346515 : Blo 247818 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B249535 : Blo 247818 249535 := bstep (se 1 (by rfl) ⟨187151, by rfl⟩ : syracuseStep 249535 = 374303) B374303
theorem B249551 : Blo 247818 249551 := bstep (se 1 (by rfl) ⟨187163, by rfl⟩ : syracuseStep 249551 = 374327) B374327
theorem B249627 : Blo 247818 249627 := bstep (se 1 (by rfl) ⟨187220, by rfl⟩ : syracuseStep 249627 = 374441) B374441
theorem B250063 : Blo 247818 250063 := bstep (se 1 (by rfl) ⟨187547, by rfl⟩ : syracuseStep 250063 = 375095) B375095
theorem B250111 : Blo 247818 250111 := bstep (se 1 (by rfl) ⟨187583, by rfl⟩ : syracuseStep 250111 = 375167) B375167
theorem B250183 : Blo 247818 250183 := bstep (se 1 (by rfl) ⟨187637, by rfl⟩ : syracuseStep 250183 = 375275) B375275
theorem B250727 : Blo 247818 250727 := bstep (se 1 (by rfl) ⟨188045, by rfl⟩ : syracuseStep 250727 = 376091) B376091
theorem B251071 : Blo 247818 251071 := bstep (se 1 (by rfl) ⟨188303, by rfl⟩ : syracuseStep 251071 = 376607) B376607
theorem B3822815 : Blo 247818 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B251135 : Blo 247818 251135 := bstep (se 1 (by rfl) ⟨188351, by rfl⟩ : syracuseStep 251135 = 376703) B376703
theorem B251391 : Blo 247818 251391 := bstep (se 1 (by rfl) ⟨188543, by rfl⟩ : syracuseStep 251391 = 377087) B377087
theorem B37213991 : Blo 247818 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B2021449 : Blo 247818 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B1202663 : Blo 247818 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B12114683 : Blo 247818 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B253039 : Blo 247818 253039 := bstep (se 1 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 253039 = 379559) B379559
theorem B1268945 : Blo 247818 1268945 := bstep (se 2 (by rfl) ⟨475854, by rfl⟩ : syracuseStep 1268945 = 951709) B951709
theorem B941321 : Blo 247818 941321 := bstep (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) B705991
theorem B843803 : Blo 247818 843803 := bstep (se 1 (by rfl) ⟨632852, by rfl⟩ : syracuseStep 843803 = 1265705) B1265705
theorem B2843099 : Blo 247818 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B844343 : Blo 247818 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B713441 : Blo 247818 713441 := bstep (se 2 (by rfl) ⟨267540, by rfl⟩ : syracuseStep 713441 = 535081) B535081
theorem B1204969 : Blo 247818 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B353531 : Blo 247818 353531 := bstep (se 1 (by rfl) ⟨265148, by rfl⟩ : syracuseStep 353531 = 530297) B530297
theorem B419519 : Blo 247818 419519 := bstep (se 1 (by rfl) ⟨314639, by rfl⟩ : syracuseStep 419519 = 629279) B629279
theorem B1009853 : Blo 247818 1009853 := bstep (se 3 (by rfl) ⟨189347, by rfl⟩ : syracuseStep 1009853 = 378695) B378695
theorem B420167 : Blo 247818 420167 := bstep (se 1 (by rfl) ⟨315125, by rfl⟩ : syracuseStep 420167 = 630251) B630251
theorem B420329 : Blo 247818 420329 := bstep (se 2 (by rfl) ⟨157623, by rfl⟩ : syracuseStep 420329 = 315247) B315247
theorem B1797191 : Blo 247818 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B1372841 : Blo 247818 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B2126857 : Blo 247818 2126857 := bstep (se 2 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 2126857 = 1595143) B1595143
theorem B7240427 : Blo 247818 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B1342271 : Blo 247818 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B30539177 : Blo 247818 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B1343135 : Blo 247818 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B1605703 : Blo 247818 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B917729 : Blo 247818 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B1508159 : Blo 247818 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B1606625 : Blo 247818 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B10194173 : Blo 247818 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B24809327 : Blo 247818 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B627547 : Blo 247818 627547 := bstep (se 1 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 627547 = 941321) B941321
theorem B562535 : Blo 247818 562535 := bstep (se 1 (by rfl) ⟨421901, by rfl⟩ : syracuseStep 562535 = 843803) B843803
theorem B562895 : Blo 247818 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B628985 : Blo 247818 628985 := bstep (se 2 (by rfl) ⟨235869, by rfl⟩ : syracuseStep 628985 = 471739) B471739
theorem B399671 : Blo 247818 399671 := bstep (se 1 (by rfl) ⟨299753, by rfl⟩ : syracuseStep 399671 = 599507) B599507
theorem B3579389 : Blo 247818 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B401087 : Blo 247818 401087 := bstep (se 1 (by rfl) ⟨300815, by rfl⟩ : syracuseStep 401087 = 601631) B601631
theorem B2695265 : Blo 247818 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B337385 : Blo 247818 337385 := bstep (se 2 (by rfl) ⟨126519, by rfl⟩ : syracuseStep 337385 = 253039) B253039
theorem B4826951 : Blo 247818 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B20359451 : Blo 247818 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B895423 : Blo 247818 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B633703 : Blo 247818 633703 := bstep (se 1 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 633703 = 950555) B950555
theorem B371807 : Blo 247818 371807 := bstep (se 1 (by rfl) ⟨278855, by rfl⟩ : syracuseStep 371807 = 557711) B557711
theorem B372203 : Blo 247818 372203 := bstep (se 1 (by rfl) ⟨279152, by rfl⟩ : syracuseStep 372203 = 558305) B558305
theorem B3256375 : Blo 247818 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1814663 : Blo 247818 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B373115 : Blo 247818 373115 := bstep (se 1 (by rfl) ⟨279836, by rfl⟩ : syracuseStep 373115 = 559673) B559673
theorem B373607 : Blo 247818 373607 := bstep (se 1 (by rfl) ⟨280205, by rfl⟩ : syracuseStep 373607 = 560411) B560411
theorem B373787 : Blo 247818 373787 := bstep (se 1 (by rfl) ⟨280340, by rfl⟩ : syracuseStep 373787 = 560681) B560681
theorem B570395 : Blo 247818 570395 := bstep (se 1 (by rfl) ⟨427796, by rfl⟩ : syracuseStep 570395 = 855593) B855593
theorem B374063 : Blo 247818 374063 := bstep (se 1 (by rfl) ⟨280547, by rfl⟩ : syracuseStep 374063 = 561095) B561095
theorem B374207 : Blo 247818 374207 := bstep (se 1 (by rfl) ⟨280655, by rfl⟩ : syracuseStep 374207 = 561311) B561311
theorem B6403535 : Blo 247818 6403535 := bstep (se 1 (by rfl) ⟨4802651, by rfl⟩ : syracuseStep 6403535 = 9605303) B9605303
theorem B374255 : Blo 247818 374255 := bstep (se 1 (by rfl) ⟨280691, by rfl⟩ : syracuseStep 374255 = 561383) B561383
theorem B964327 : Blo 247818 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B374537 : Blo 247818 374537 := bstep (se 2 (by rfl) ⟨140451, by rfl⟩ : syracuseStep 374537 = 280903) B280903
theorem B1194497 : Blo 247818 1194497 := bstep (se 2 (by rfl) ⟨447936, by rfl⟩ : syracuseStep 1194497 = 895873) B895873
theorem B375515 : Blo 247818 375515 := bstep (se 1 (by rfl) ⟨281636, by rfl⟩ : syracuseStep 375515 = 563273) B563273
theorem B801775 : Blo 247818 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B375863 : Blo 247818 375863 := bstep (se 1 (by rfl) ⟨281897, by rfl⟩ : syracuseStep 375863 = 563795) B563795
theorem B8076455 : Blo 247818 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B802237 : Blo 247818 802237 := bstep (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) B300839
theorem B376511 : Blo 247818 376511 := bstep (se 1 (by rfl) ⟨282383, by rfl⟩ : syracuseStep 376511 = 564767) B564767
theorem B376667 : Blo 247818 376667 := bstep (se 1 (by rfl) ⟨282500, by rfl⟩ : syracuseStep 376667 = 565001) B565001
theorem B376943 : Blo 247818 376943 := bstep (se 1 (by rfl) ⟨282707, by rfl⟩ : syracuseStep 376943 = 565415) B565415
theorem B377015 : Blo 247818 377015 := bstep (se 1 (by rfl) ⟨282761, by rfl⟩ : syracuseStep 377015 = 565523) B565523
theorem B475627 : Blo 247818 475627 := bstep (se 1 (by rfl) ⟨356720, by rfl⟩ : syracuseStep 475627 = 713441) B713441
theorem B377327 : Blo 247818 377327 := bstep (se 1 (by rfl) ⟨282995, by rfl⟩ : syracuseStep 377327 = 565991) B565991
theorem B377399 : Blo 247818 377399 := bstep (se 1 (by rfl) ⟨283049, by rfl⟩ : syracuseStep 377399 = 566099) B566099
theorem B3588731 : Blo 247818 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B377855 : Blo 247818 377855 := bstep (se 1 (by rfl) ⟨283391, by rfl⟩ : syracuseStep 377855 = 566783) B566783
theorem B1885193 : Blo 247818 1885193 := bstep (se 2 (by rfl) ⟨706947, by rfl⟩ : syracuseStep 1885193 = 1413895) B1413895
theorem B279679 : Blo 247818 279679 := bstep (se 1 (by rfl) ⟨209759, by rfl⟩ : syracuseStep 279679 = 419519) B419519
theorem B2835809 : Blo 247818 2835809 := bstep (se 2 (by rfl) ⟨1063428, by rfl⟩ : syracuseStep 2835809 = 2126857) B2126857
theorem B673235 : Blo 247818 673235 := bstep (se 1 (by rfl) ⟨504926, by rfl⟩ : syracuseStep 673235 = 1009853) B1009853
theorem B280111 : Blo 247818 280111 := bstep (se 1 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 280111 = 420167) B420167
theorem B280219 : Blo 247818 280219 := bstep (se 1 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 280219 = 420329) B420329
theorem B5425127 : Blo 247818 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B1198127 : Blo 247818 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B837755 : Blo 247818 837755 := bstep (se 1 (by rfl) ⟨628316, by rfl⟩ : syracuseStep 837755 = 1256633) B1256633
theorem B248303 : Blo 247818 248303 := bstep (se 1 (by rfl) ⟨186227, by rfl⟩ : syracuseStep 248303 = 372455) B372455
theorem B248431 : Blo 247818 248431 := bstep (se 1 (by rfl) ⟨186323, by rfl⟩ : syracuseStep 248431 = 372647) B372647
theorem B248815 : Blo 247818 248815 := bstep (se 1 (by rfl) ⟨186611, by rfl⟩ : syracuseStep 248815 = 373223) B373223
theorem B248831 : Blo 247818 248831 := bstep (se 1 (by rfl) ⟨186623, by rfl⟩ : syracuseStep 248831 = 373247) B373247
theorem B248923 : Blo 247818 248923 := bstep (se 1 (by rfl) ⟨186692, by rfl⟩ : syracuseStep 248923 = 373385) B373385
theorem B708065 : Blo 247818 708065 := bstep (se 2 (by rfl) ⟨265524, by rfl⟩ : syracuseStep 708065 = 531049) B531049
theorem B249499 : Blo 247818 249499 := bstep (se 1 (by rfl) ⟨187124, by rfl⟩ : syracuseStep 249499 = 374249) B374249
theorem B249703 : Blo 247818 249703 := bstep (se 1 (by rfl) ⟨187277, by rfl⟩ : syracuseStep 249703 = 374555) B374555
theorem B249967 : Blo 247818 249967 := bstep (se 1 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 249967 = 374951) B374951
theorem B839915 : Blo 247818 839915 := bstep (se 1 (by rfl) ⟨629936, by rfl⟩ : syracuseStep 839915 = 1259873) B1259873
theorem B250139 : Blo 247818 250139 := bstep (se 1 (by rfl) ⟨187604, by rfl⟩ : syracuseStep 250139 = 375209) B375209
theorem B709499 : Blo 247818 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B250815 : Blo 247818 250815 := bstep (se 1 (by rfl) ⟨188111, by rfl⟩ : syracuseStep 250815 = 376223) B376223
theorem B250991 : Blo 247818 250991 := bstep (se 1 (by rfl) ⟨188243, by rfl⟩ : syracuseStep 250991 = 376487) B376487
theorem B1594505 : Blo 247818 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B251039 : Blo 247818 251039 := bstep (se 1 (by rfl) ⟨188279, by rfl⟩ : syracuseStep 251039 = 376559) B376559
theorem B251239 : Blo 247818 251239 := bstep (se 1 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 251239 = 376859) B376859
theorem B251419 : Blo 247818 251419 := bstep (se 1 (by rfl) ⟨188564, by rfl⟩ : syracuseStep 251419 = 377129) B377129
theorem B1627721 : Blo 247818 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B251623 : Blo 247818 251623 := bstep (se 1 (by rfl) ⟨188717, by rfl⟩ : syracuseStep 251623 = 377435) B377435
theorem B842345 : Blo 247818 842345 := bstep (se 2 (by rfl) ⟨315879, by rfl⟩ : syracuseStep 842345 = 631759) B631759
theorem B3627823 : Blo 247818 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B1793153 : Blo 247818 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B711983 : Blo 247818 711983 := bstep (se 1 (by rfl) ⟨533987, by rfl⟩ : syracuseStep 711983 = 1067975) B1067975
theorem B1564343 : Blo 247818 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B941807 : Blo 247818 941807 := bstep (se 1 (by rfl) ⟨706355, by rfl⟩ : syracuseStep 941807 = 1412711) B1412711
theorem B942263 : Blo 247818 942263 := bstep (se 1 (by rfl) ⟨706697, by rfl⟩ : syracuseStep 942263 = 1413395) B1413395
theorem B418351 : Blo 247818 418351 := bstep (se 1 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 418351 = 627527) B627527
theorem B942749 : Blo 247818 942749 := bstep (se 3 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 942749 = 353531) B353531
theorem B419303 : Blo 247818 419303 := bstep (se 1 (by rfl) ⟨314477, by rfl⟩ : syracuseStep 419303 = 628955) B628955
theorem B419431 : Blo 247818 419431 := bstep (se 1 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 419431 = 629147) B629147
theorem B845963 : Blo 247818 845963 := bstep (se 1 (by rfl) ⟨634472, by rfl⟩ : syracuseStep 845963 = 1268945) B1268945
theorem B1895399 : Blo 247818 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B356071 : Blo 247818 356071 := bstep (se 1 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 356071 = 534107) B534107
theorem B1602503 : Blo 247818 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B849689 : Blo 247818 849689 := bstep (se 2 (by rfl) ⟨318633, by rfl⟩ : syracuseStep 849689 = 637267) B637267
theorem B915227 : Blo 247818 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B424703 : Blo 247818 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B9075503 : Blo 247818 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B2718623 : Blo 247818 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B5799923 : Blo 247818 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B2392487 : Blo 247818 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B557801 : Blo 247818 557801 := bstep (se 2 (by rfl) ⟨209175, by rfl⟩ : syracuseStep 557801 = 418351) B418351
theorem B558503 : Blo 247818 558503 := bstep (se 1 (by rfl) ⟨418877, by rfl⟩ : syracuseStep 558503 = 837755) B837755
theorem B559241 : Blo 247818 559241 := bstep (se 2 (by rfl) ⟨209715, by rfl⟩ : syracuseStep 559241 = 419431) B419431
theorem B559943 : Blo 247818 559943 := bstep (se 1 (by rfl) ⟨419957, by rfl⟩ : syracuseStep 559943 = 839915) B839915
theorem B1085147 : Blo 247818 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B266447 : Blo 247818 266447 := bstep (se 1 (by rfl) ⟨199835, by rfl⟩ : syracuseStep 266447 = 399671) B399671
theorem B561563 : Blo 247818 561563 := bstep (se 1 (by rfl) ⟨421172, by rfl⟩ : syracuseStep 561563 = 842345) B842345
theorem B267391 : Blo 247818 267391 := bstep (se 1 (by rfl) ⟨200543, by rfl⟩ : syracuseStep 267391 = 401087) B401087
theorem B627871 : Blo 247818 627871 := bstep (se 1 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 627871 = 941807) B941807
theorem B628175 : Blo 247818 628175 := bstep (se 1 (by rfl) ⟨471131, by rfl⟩ : syracuseStep 628175 = 942263) B942263
theorem B628499 : Blo 247818 628499 := bstep (se 1 (by rfl) ⟨471374, by rfl⟩ : syracuseStep 628499 = 942749) B942749
theorem B3217967 : Blo 247818 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B563975 : Blo 247818 563975 := bstep (se 1 (by rfl) ⟨422981, by rfl⟩ : syracuseStep 563975 = 845963) B845963
theorem B13572967 : Blo 247818 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B1285769 : Blo 247818 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B4269023 : Blo 247818 4269023 := bstep (se 1 (by rfl) ⟨3201767, by rfl⟩ : syracuseStep 4269023 = 6403535) B6403535
theorem B566459 : Blo 247818 566459 := bstep (se 1 (by rfl) ⟨424844, by rfl⟩ : syracuseStep 566459 = 849689) B849689
theorem B796331 : Blo 247818 796331 := bstep (se 1 (by rfl) ⟨597248, by rfl⟩ : syracuseStep 796331 = 1194497) B1194497
theorem B1812415 : Blo 247818 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B5384303 : Blo 247818 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B2140937 : Blo 247818 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B634169 : Blo 247818 634169 := bstep (se 2 (by rfl) ⟨237813, by rfl⟩ : syracuseStep 634169 = 475627) B475627
theorem B1256795 : Blo 247818 1256795 := bstep (se 1 (by rfl) ⟨942596, by rfl⟩ : syracuseStep 1256795 = 1885193) B1885193
theorem B3616751 : Blo 247818 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B798751 : Blo 247818 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B372905 : Blo 247818 372905 := bstep (se 2 (by rfl) ⟨139839, by rfl⟩ : syracuseStep 372905 = 279679) B279679
theorem B373481 : Blo 247818 373481 := bstep (se 2 (by rfl) ⟨140055, by rfl⟩ : syracuseStep 373481 = 280111) B280111
theorem B6796115 : Blo 247818 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B373625 : Blo 247818 373625 := bstep (se 2 (by rfl) ⟨140109, by rfl⟩ : syracuseStep 373625 = 280219) B280219
theorem B472043 : Blo 247818 472043 := bstep (se 1 (by rfl) ⟨354032, by rfl⟩ : syracuseStep 472043 = 708065) B708065
theorem B1193897 : Blo 247818 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1063003 : Blo 247818 1063003 := bstep (se 1 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 1063003 = 1594505) B1594505
theorem B375023 : Blo 247818 375023 := bstep (se 1 (by rfl) ⟨281267, by rfl⟩ : syracuseStep 375023 = 562535) B562535
theorem B375263 : Blo 247818 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B899693 : Blo 247818 899693 := bstep (se 3 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 899693 = 337385) B337385
theorem B1195435 : Blo 247818 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B474655 : Blo 247818 474655 := bstep (se 1 (by rfl) ⟨355991, by rfl⟩ : syracuseStep 474655 = 711983) B711983
theorem B474761 : Blo 247818 474761 := bstep (se 2 (by rfl) ⟨178035, by rfl⟩ : syracuseStep 474761 = 356071) B356071
theorem B4341833 : Blo 247818 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B279535 : Blo 247818 279535 := bstep (se 1 (by rfl) ⟨209651, by rfl⟩ : syracuseStep 279535 = 419303) B419303
theorem B836729 : Blo 247818 836729 := bstep (se 2 (by rfl) ⟨313773, by rfl⟩ : syracuseStep 836729 = 627547) B627547
theorem B1263599 : Blo 247818 1263599 := bstep (se 1 (by rfl) ⟨947699, by rfl⟩ : syracuseStep 1263599 = 1895399) B1895399
theorem B247871 : Blo 247818 247871 := bstep (se 1 (by rfl) ⟨185903, by rfl⟩ : syracuseStep 247871 = 371807) B371807
theorem B248135 : Blo 247818 248135 := bstep (se 1 (by rfl) ⟨186101, by rfl⟩ : syracuseStep 248135 = 372203) B372203
theorem B248743 : Blo 247818 248743 := bstep (se 1 (by rfl) ⟨186557, by rfl⟩ : syracuseStep 248743 = 373115) B373115
theorem B249071 : Blo 247818 249071 := bstep (se 1 (by rfl) ⟨186803, by rfl⟩ : syracuseStep 249071 = 373607) B373607
theorem B1068335 : Blo 247818 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B249191 : Blo 247818 249191 := bstep (se 1 (by rfl) ⟨186893, by rfl⟩ : syracuseStep 249191 = 373787) B373787
theorem B380263 : Blo 247818 380263 := bstep (se 1 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 380263 = 570395) B570395
theorem B249375 : Blo 247818 249375 := bstep (se 1 (by rfl) ⟨187031, by rfl⟩ : syracuseStep 249375 = 374063) B374063
theorem B249471 : Blo 247818 249471 := bstep (se 1 (by rfl) ⟨187103, by rfl⟩ : syracuseStep 249471 = 374207) B374207
theorem B249503 : Blo 247818 249503 := bstep (se 1 (by rfl) ⟨187127, by rfl⟩ : syracuseStep 249503 = 374255) B374255
theorem B4837097 : Blo 247818 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B249691 : Blo 247818 249691 := bstep (se 1 (by rfl) ⟨187268, by rfl⟩ : syracuseStep 249691 = 374537) B374537
theorem B610151 : Blo 247818 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B1069033 : Blo 247818 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B250343 : Blo 247818 250343 := bstep (se 1 (by rfl) ⟨187757, by rfl⟩ : syracuseStep 250343 = 375515) B375515
theorem B283135 : Blo 247818 283135 := bstep (se 1 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 283135 = 424703) B424703
theorem B6050335 : Blo 247818 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B1069649 : Blo 247818 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B250575 : Blo 247818 250575 := bstep (se 1 (by rfl) ⟨187931, by rfl⟩ : syracuseStep 250575 = 375863) B375863
theorem B251007 : Blo 247818 251007 := bstep (se 1 (by rfl) ⟨188255, by rfl⟩ : syracuseStep 251007 = 376511) B376511
theorem B251111 : Blo 247818 251111 := bstep (se 1 (by rfl) ⟨188333, by rfl⟩ : syracuseStep 251111 = 376667) B376667
theorem B251295 : Blo 247818 251295 := bstep (se 1 (by rfl) ⟨188471, by rfl⟩ : syracuseStep 251295 = 376943) B376943
theorem B251343 : Blo 247818 251343 := bstep (se 1 (by rfl) ⟨188507, by rfl⟩ : syracuseStep 251343 = 377015) B377015
theorem B611819 : Blo 247818 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B251551 : Blo 247818 251551 := bstep (se 1 (by rfl) ⟨188663, by rfl⟩ : syracuseStep 251551 = 377327) B377327
theorem B4839101 : Blo 247818 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B251599 : Blo 247818 251599 := bstep (se 1 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 251599 = 377399) B377399
theorem B1071083 : Blo 247818 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B251903 : Blo 247818 251903 := bstep (se 1 (by rfl) ⟨188927, by rfl⟩ : syracuseStep 251903 = 377855) B377855
theorem B1890539 : Blo 247818 1890539 := bstep (se 1 (by rfl) ⟨1417904, by rfl⟩ : syracuseStep 1890539 = 2835809) B2835809
theorem B448823 : Blo 247818 448823 := bstep (se 1 (by rfl) ⟨336617, by rfl⟩ : syracuseStep 448823 = 673235) B673235
theorem B4021757 : Blo 247818 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B1891997 : Blo 247818 1891997 := bstep (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) B709499
theorem B16539551 : Blo 247818 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B844937 : Blo 247818 844937 := bstep (se 2 (by rfl) ⟨316851, by rfl⟩ : syracuseStep 844937 = 633703) B633703
theorem B419323 : Blo 247818 419323 := bstep (se 1 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 419323 = 628985) B628985
theorem B2386259 : Blo 247818 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B1042895 : Blo 247818 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B1796843 : Blo 247818 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B3866615 : Blo 247818 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B557819 : Blo 247818 557819 := bstep (se 1 (by rfl) ⟨418364, by rfl⟩ : syracuseStep 557819 = 836729) B836729
theorem B559097 : Blo 247818 559097 := bstep (se 2 (by rfl) ⟨209661, by rfl⟩ : syracuseStep 559097 = 419323) B419323
theorem B723431 : Blo 247818 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B299215 : Blo 247818 299215 := bstep (se 1 (by rfl) ⟨224411, by rfl⟩ : syracuseStep 299215 = 448823) B448823
theorem B857179 : Blo 247818 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B3183725 : Blo 247818 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B2856221 : Blo 247818 2856221 := bstep (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) B1071083
theorem B8067113 : Blo 247818 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B563291 : Blo 247818 563291 := bstep (se 1 (by rfl) ⟨422468, by rfl⟩ : syracuseStep 563291 = 844937) B844937
theorem B530887 : Blo 247818 530887 := bstep (se 1 (by rfl) ⟨398165, by rfl⟩ : syracuseStep 530887 = 796331) B796331
theorem B4791581 : Blo 247818 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B1417337 : Blo 247818 1417337 := bstep (se 2 (by rfl) ⟨531501, by rfl⟩ : syracuseStep 1417337 = 1063003) B1063003
theorem B4530743 : Blo 247818 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B18097289 : Blo 247818 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B599795 : Blo 247818 599795 := bstep (se 1 (by rfl) ⟨449846, by rfl⟩ : syracuseStep 599795 = 899693) B899693
theorem B632873 : Blo 247818 632873 := bstep (se 2 (by rfl) ⟨237327, by rfl⟩ : syracuseStep 632873 = 474655) B474655
theorem B9644669 : Blo 247818 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B2894555 : Blo 247818 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B371867 : Blo 247818 371867 := bstep (se 1 (by rfl) ⟨278900, by rfl⟩ : syracuseStep 371867 = 557801) B557801
theorem B372335 : Blo 247818 372335 := bstep (se 1 (by rfl) ⟨279251, by rfl⟩ : syracuseStep 372335 = 558503) B558503
theorem B372713 : Blo 247818 372713 := bstep (se 2 (by rfl) ⟨139767, by rfl⟩ : syracuseStep 372713 = 279535) B279535
theorem B372827 : Blo 247818 372827 := bstep (se 1 (by rfl) ⟨279620, by rfl⟩ : syracuseStep 372827 = 559241) B559241
theorem B373295 : Blo 247818 373295 := bstep (se 1 (by rfl) ⟨279971, by rfl⟩ : syracuseStep 373295 = 559943) B559943
theorem B3224731 : Blo 247818 3224731 := bstep (se 1 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 3224731 = 4837097) B4837097
theorem B374375 : Blo 247818 374375 := bstep (se 1 (by rfl) ⟨280781, by rfl⟩ : syracuseStep 374375 = 561563) B561563
theorem B407879 : Blo 247818 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B3226067 : Blo 247818 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B1260359 : Blo 247818 1260359 := bstep (se 1 (by rfl) ⟨945269, by rfl⟩ : syracuseStep 1260359 = 1890539) B1890539
theorem B2145311 : Blo 247818 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B507017 : Blo 247818 507017 := bstep (se 2 (by rfl) ⟨190131, by rfl⟩ : syracuseStep 507017 = 380263) B380263
theorem B375983 : Blo 247818 375983 := bstep (se 1 (by rfl) ⟨281987, by rfl⟩ : syracuseStep 375983 = 563975) B563975
theorem B1261331 : Blo 247818 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B11026367 : Blo 247818 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B1425377 : Blo 247818 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B671741 : Blo 247818 671741 := bstep (se 3 (by rfl) ⟨125951, by rfl⟩ : syracuseStep 671741 = 251903) B251903
theorem B1065001 : Blo 247818 1065001 := bstep (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) B798751
theorem B1426085 : Blo 247818 1426085 := bstep (se 4 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 1426085 = 267391) B267391
theorem B377513 : Blo 247818 377513 := bstep (se 2 (by rfl) ⟨141567, by rfl⟩ : syracuseStep 377513 = 283135) B283135
theorem B377639 : Blo 247818 377639 := bstep (se 1 (by rfl) ⟨283229, by rfl⟩ : syracuseStep 377639 = 566459) B566459
theorem B3589535 : Blo 247818 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B837161 : Blo 247818 837161 := bstep (se 2 (by rfl) ⟨313935, by rfl⟩ : syracuseStep 837161 = 627871) B627871
theorem B1590839 : Blo 247818 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1427291 : Blo 247818 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B837863 : Blo 247818 837863 := bstep (se 1 (by rfl) ⟨628397, by rfl⟩ : syracuseStep 837863 = 1256795) B1256795
theorem B248603 : Blo 247818 248603 := bstep (se 1 (by rfl) ⟨186452, by rfl⟩ : syracuseStep 248603 = 372905) B372905
theorem B248987 : Blo 247818 248987 := bstep (se 1 (by rfl) ⟨186740, by rfl⟩ : syracuseStep 248987 = 373481) B373481
theorem B249083 : Blo 247818 249083 := bstep (se 1 (by rfl) ⟨186812, by rfl⟩ : syracuseStep 249083 = 373625) B373625
theorem B314695 : Blo 247818 314695 := bstep (se 1 (by rfl) ⟨236021, by rfl⟩ : syracuseStep 314695 = 472043) B472043
theorem B250015 : Blo 247818 250015 := bstep (se 1 (by rfl) ⟨187511, by rfl⟩ : syracuseStep 250015 = 375023) B375023
theorem B250175 : Blo 247818 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B1266029 : Blo 247818 1266029 := bstep (se 3 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 1266029 = 474761) B474761
theorem B1593913 : Blo 247818 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B1627069 : Blo 247818 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B2577743 : Blo 247818 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B1594991 : Blo 247818 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B710525 : Blo 247818 710525 := bstep (se 3 (by rfl) ⟨133223, by rfl⟩ : syracuseStep 710525 = 266447) B266447
theorem B842399 : Blo 247818 842399 := bstep (se 1 (by rfl) ⟨631799, by rfl⟩ : syracuseStep 842399 = 1263599) B1263599
theorem B712223 : Blo 247818 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B2416553 : Blo 247818 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B713099 : Blo 247818 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B418783 : Blo 247818 418783 := bstep (se 1 (by rfl) ⟨314087, by rfl⟩ : syracuseStep 418783 = 628175) B628175
theorem B418999 : Blo 247818 418999 := bstep (se 1 (by rfl) ⟨314249, by rfl⟩ : syracuseStep 418999 = 628499) B628499
theorem B2681171 : Blo 247818 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B2846015 : Blo 247818 2846015 := bstep (se 1 (by rfl) ⟨2134511, by rfl⟩ : syracuseStep 2846015 = 4269023) B4269023
theorem B2781053 : Blo 247818 2781053 := bstep (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) B1042895
theorem B422779 : Blo 247818 422779 := bstep (se 1 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 422779 = 634169) B634169
theorem B950723 : Blo 247818 950723 := bstep (se 1 (by rfl) ⟨713042, by rfl⟩ : syracuseStep 950723 = 1426085) B1426085
theorem B2393023 : Blo 247818 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B558107 : Blo 247818 558107 := bstep (se 1 (by rfl) ⟨418580, by rfl⟩ : syracuseStep 558107 = 837161) B837161
theorem B951527 : Blo 247818 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B558377 : Blo 247818 558377 := bstep (se 2 (by rfl) ⟨209391, by rfl⟩ : syracuseStep 558377 = 418783) B418783
theorem B558575 : Blo 247818 558575 := bstep (se 1 (by rfl) ⟨418931, by rfl⟩ : syracuseStep 558575 = 837863) B837863
theorem B558665 : Blo 247818 558665 := bstep (se 2 (by rfl) ⟨209499, by rfl⟩ : syracuseStep 558665 = 418999) B418999
theorem B1904147 : Blo 247818 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B5378075 : Blo 247818 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B561599 : Blo 247818 561599 := bstep (se 1 (by rfl) ⟨421199, by rfl⟩ : syracuseStep 561599 = 842399) B842399
theorem B1611035 : Blo 247818 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B398953 : Blo 247818 398953 := bstep (se 2 (by rfl) ⟨149607, by rfl⟩ : syracuseStep 398953 = 299215) B299215
theorem B3020495 : Blo 247818 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B12064859 : Blo 247818 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B399863 : Blo 247818 399863 := bstep (se 1 (by rfl) ⟨299897, by rfl⟩ : syracuseStep 399863 = 599795) B599795
theorem B563705 : Blo 247818 563705 := bstep (se 2 (by rfl) ⟨211389, by rfl⟩ : syracuseStep 563705 = 422779) B422779
theorem B2169425 : Blo 247818 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B4299641 : Blo 247818 4299641 := bstep (se 2 (by rfl) ⟨1612365, by rfl⟩ : syracuseStep 4299641 = 3224731) B3224731
theorem B6429779 : Blo 247818 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B1352045 : Blo 247818 1352045 := bstep (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) B507017
theorem B271919 : Blo 247818 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B7350911 : Blo 247818 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B1420001 : Blo 247818 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B371879 : Blo 247818 371879 := bstep (se 1 (by rfl) ⟨278909, by rfl⟩ : syracuseStep 371879 = 557819) B557819
theorem B1060559 : Blo 247818 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B372731 : Blo 247818 372731 := bstep (se 1 (by rfl) ⟨279548, by rfl⟩ : syracuseStep 372731 = 559097) B559097
theorem B1718495 : Blo 247818 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B1063327 : Blo 247818 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B473683 : Blo 247818 473683 := bstep (se 1 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 473683 = 710525) B710525
theorem B375527 : Blo 247818 375527 := bstep (se 1 (by rfl) ⟨281645, by rfl⟩ : syracuseStep 375527 = 563291) B563291
theorem B3194387 : Blo 247818 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B474815 : Blo 247818 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B475399 : Blo 247818 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B1787447 : Blo 247818 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B7718813 : Blo 247818 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B247911 : Blo 247818 247911 := bstep (se 1 (by rfl) ⟨185933, by rfl⟩ : syracuseStep 247911 = 371867) B371867
theorem B248223 : Blo 247818 248223 := bstep (se 1 (by rfl) ⟨186167, by rfl⟩ : syracuseStep 248223 = 372335) B372335
theorem B1854035 : Blo 247818 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B248475 : Blo 247818 248475 := bstep (se 1 (by rfl) ⟨186356, by rfl⟩ : syracuseStep 248475 = 372713) B372713
theorem B248551 : Blo 247818 248551 := bstep (se 1 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 248551 = 372827) B372827
theorem B248863 : Blo 247818 248863 := bstep (se 1 (by rfl) ⟨186647, by rfl⟩ : syracuseStep 248863 = 373295) B373295
theorem B707849 : Blo 247818 707849 := bstep (se 2 (by rfl) ⟨265443, by rfl⟩ : syracuseStep 707849 = 530887) B530887
theorem B249583 : Blo 247818 249583 := bstep (se 1 (by rfl) ⟨187187, by rfl⟩ : syracuseStep 249583 = 374375) B374375
theorem B2150711 : Blo 247818 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B840239 : Blo 247818 840239 := bstep (se 1 (by rfl) ⟨630179, by rfl⟩ : syracuseStep 840239 = 1260359) B1260359
theorem B1430207 : Blo 247818 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B250655 : Blo 247818 250655 := bstep (se 1 (by rfl) ⟨187991, by rfl⟩ : syracuseStep 250655 = 375983) B375983
theorem B840887 : Blo 247818 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B447827 : Blo 247818 447827 := bstep (se 1 (by rfl) ⟨335870, by rfl⟩ : syracuseStep 447827 = 671741) B671741
theorem B251675 : Blo 247818 251675 := bstep (se 1 (by rfl) ⟨188756, by rfl⟩ : syracuseStep 251675 = 377513) B377513
theorem B251759 : Blo 247818 251759 := bstep (se 1 (by rfl) ⟨188819, by rfl⟩ : syracuseStep 251759 = 377639) B377639
theorem B482287 : Blo 247818 482287 := bstep (se 1 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 482287 = 723431) B723431
theorem B844019 : Blo 247818 844019 := bstep (se 1 (by rfl) ⟨633014, by rfl⟩ : syracuseStep 844019 = 1266029) B1266029
theorem B2122483 : Blo 247818 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B419593 : Blo 247818 419593 := bstep (se 2 (by rfl) ⟨157347, by rfl⟩ : syracuseStep 419593 = 314695) B314695
theorem B944891 : Blo 247818 944891 := bstep (se 1 (by rfl) ⟨708668, by rfl⟩ : syracuseStep 944891 = 1417337) B1417337
theorem B2125217 : Blo 247818 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B421915 : Blo 247818 421915 := bstep (se 1 (by rfl) ⟨316436, by rfl⟩ : syracuseStep 421915 = 632873) B632873
theorem B1142905 : Blo 247818 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B1897343 : Blo 247818 1897343 := bstep (se 1 (by rfl) ⟨1423007, by rfl⟩ : syracuseStep 1897343 = 2846015) B2846015
theorem B950251 : Blo 247818 950251 := bstep (se 1 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 950251 = 1425377) B1425377
theorem B5145875 : Blo 247818 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B559457 : Blo 247818 559457 := bstep (se 2 (by rfl) ⟨209796, by rfl⟩ : syracuseStep 559457 = 419593) B419593
theorem B560159 : Blo 247818 560159 := bstep (se 1 (by rfl) ⟨420119, by rfl⟩ : syracuseStep 560159 = 840239) B840239
theorem B953471 : Blo 247818 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B560591 : Blo 247818 560591 := bstep (se 1 (by rfl) ⟨420443, by rfl⟩ : syracuseStep 560591 = 840887) B840887
theorem B725117 : Blo 247818 725117 := bstep (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) B271919
theorem B266575 : Blo 247818 266575 := bstep (se 1 (by rfl) ⟨199931, by rfl⟩ : syracuseStep 266575 = 399863) B399863
theorem B1446283 : Blo 247818 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B562553 : Blo 247818 562553 := bstep (se 2 (by rfl) ⟨210957, by rfl⟩ : syracuseStep 562553 = 421915) B421915
theorem B562679 : Blo 247818 562679 := bstep (se 1 (by rfl) ⟨422009, by rfl⟩ : syracuseStep 562679 = 844019) B844019
theorem B629927 : Blo 247818 629927 := bstep (se 1 (by rfl) ⟨472445, by rfl⟩ : syracuseStep 629927 = 944891) B944891
theorem B531937 : Blo 247818 531937 := bstep (se 2 (by rfl) ⟨199476, by rfl⟩ : syracuseStep 531937 = 398953) B398953
theorem B1416811 : Blo 247818 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B1417769 : Blo 247818 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B631577 : Blo 247818 631577 := bstep (se 2 (by rfl) ⟨236841, by rfl⟩ : syracuseStep 631577 = 473683) B473683
theorem B633815 : Blo 247818 633815 := bstep (se 1 (by rfl) ⟨475361, by rfl⟩ : syracuseStep 633815 = 950723) B950723
theorem B633865 : Blo 247818 633865 := bstep (se 2 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 633865 = 475399) B475399
theorem B372071 : Blo 247818 372071 := bstep (se 1 (by rfl) ⟨279053, by rfl⟩ : syracuseStep 372071 = 558107) B558107
theorem B634351 : Blo 247818 634351 := bstep (se 1 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 634351 = 951527) B951527
theorem B372251 : Blo 247818 372251 := bstep (se 1 (by rfl) ⟨279188, by rfl⟩ : syracuseStep 372251 = 558377) B558377
theorem B2829977 : Blo 247818 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B372383 : Blo 247818 372383 := bstep (se 1 (by rfl) ⟨279287, by rfl⟩ : syracuseStep 372383 = 558575) B558575
theorem B1191631 : Blo 247818 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B372443 : Blo 247818 372443 := bstep (se 1 (by rfl) ⟨279332, by rfl⟩ : syracuseStep 372443 = 558665) B558665
theorem B3190697 : Blo 247818 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B471899 : Blo 247818 471899 := bstep (se 1 (by rfl) ⟨353924, by rfl⟩ : syracuseStep 471899 = 707849) B707849
theorem B3585383 : Blo 247818 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B374399 : Blo 247818 374399 := bstep (se 1 (by rfl) ⟨280799, by rfl⟩ : syracuseStep 374399 = 561599) B561599
theorem B1194205 : Blo 247818 1194205 := bstep (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) B447827
theorem B8043239 : Blo 247818 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B375803 : Blo 247818 375803 := bstep (se 1 (by rfl) ⟨281852, by rfl⟩ : syracuseStep 375803 = 563705) B563705
theorem B2866427 : Blo 247818 2866427 := bstep (se 1 (by rfl) ⟨2149820, by rfl⟩ : syracuseStep 2866427 = 4299641) B4299641
theorem B1523873 : Blo 247818 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B901363 : Blo 247818 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B4900607 : Blo 247818 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B247919 : Blo 247818 247919 := bstep (se 1 (by rfl) ⟨185939, by rfl⟩ : syracuseStep 247919 = 371879) B371879
theorem B707039 : Blo 247818 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B248487 : Blo 247818 248487 := bstep (se 1 (by rfl) ⟨186365, by rfl⟩ : syracuseStep 248487 = 372731) B372731
theorem B1264895 : Blo 247818 1264895 := bstep (se 1 (by rfl) ⟨948671, by rfl⟩ : syracuseStep 1264895 = 1897343) B1897343
theorem B643049 : Blo 247818 643049 := bstep (se 2 (by rfl) ⟨241143, by rfl⟩ : syracuseStep 643049 = 482287) B482287
theorem B250351 : Blo 247818 250351 := bstep (se 1 (by rfl) ⟨187763, by rfl⟩ : syracuseStep 250351 = 375527) B375527
theorem B316543 : Blo 247818 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B1267001 : Blo 247818 1267001 := bstep (se 2 (by rfl) ⟨475125, by rfl⟩ : syracuseStep 1267001 = 950251) B950251
theorem B1236023 : Blo 247818 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B1269431 : Blo 247818 1269431 := bstep (se 1 (by rfl) ⟨952073, by rfl⟩ : syracuseStep 1269431 = 1904147) B1904147
theorem B1433807 : Blo 247818 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B1074023 : Blo 247818 1074023 := bstep (se 1 (by rfl) ⟨805517, by rfl⟩ : syracuseStep 1074023 = 1611035) B1611035
theorem B8054653 : Blo 247818 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B4286519 : Blo 247818 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B946667 : Blo 247818 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B1145663 : Blo 247818 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B2129591 : Blo 247818 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B1015915 : Blo 247818 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B1933645 : Blo 247818 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B428699 : Blo 247818 428699 := bstep (se 1 (by rfl) ⟨321524, by rfl⟩ : syracuseStep 428699 = 643049) B643049
theorem B824015 : Blo 247818 824015 := bstep (se 1 (by rfl) ⟨618011, by rfl⟩ : syracuseStep 824015 = 1236023) B1236023
theorem B955871 : Blo 247818 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B2857679 : Blo 247818 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B631111 : Blo 247818 631111 := bstep (se 1 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 631111 = 946667) B946667
theorem B763775 : Blo 247818 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B1910951 : Blo 247818 1910951 := bstep (se 1 (by rfl) ⟨1433213, by rfl⟩ : syracuseStep 1910951 = 2866427) B2866427
theorem B1419727 : Blo 247818 1419727 := bstep (se 1 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 1419727 = 2129591) B2129591
theorem B372971 : Blo 247818 372971 := bstep (se 1 (by rfl) ⟨279728, by rfl⟩ : syracuseStep 372971 = 559457) B559457
theorem B471359 : Blo 247818 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B373439 : Blo 247818 373439 := bstep (se 1 (by rfl) ⟨280079, by rfl⟩ : syracuseStep 373439 = 560159) B560159
theorem B635647 : Blo 247818 635647 := bstep (se 1 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 635647 = 953471) B953471
theorem B373727 : Blo 247818 373727 := bstep (se 1 (by rfl) ⟨280295, by rfl⟩ : syracuseStep 373727 = 560591) B560591
theorem B375035 : Blo 247818 375035 := bstep (se 1 (by rfl) ⟨281276, by rfl⟩ : syracuseStep 375035 = 562553) B562553
theorem B375119 : Blo 247818 375119 := bstep (se 1 (by rfl) ⟨281339, by rfl⟩ : syracuseStep 375119 = 562679) B562679
theorem B1588841 : Blo 247818 1588841 := bstep (se 2 (by rfl) ⟨595815, by rfl⟩ : syracuseStep 1588841 = 1191631) B1191631
theorem B248047 : Blo 247818 248047 := bstep (se 1 (by rfl) ⟨186035, by rfl⟩ : syracuseStep 248047 = 372071) B372071
theorem B248167 : Blo 247818 248167 := bstep (se 1 (by rfl) ⟨186125, by rfl⟩ : syracuseStep 248167 = 372251) B372251
theorem B1886651 : Blo 247818 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B248255 : Blo 247818 248255 := bstep (se 1 (by rfl) ⟨186191, by rfl⟩ : syracuseStep 248255 = 372383) B372383
theorem B248295 : Blo 247818 248295 := bstep (se 1 (by rfl) ⟨186221, by rfl⟩ : syracuseStep 248295 = 372443) B372443
theorem B1592273 : Blo 247818 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B314599 : Blo 247818 314599 := bstep (se 1 (by rfl) ⟨235949, by rfl⟩ : syracuseStep 314599 = 471899) B471899
theorem B249599 : Blo 247818 249599 := bstep (se 1 (by rfl) ⟨187199, by rfl⟩ : syracuseStep 249599 = 374399) B374399
theorem B5362159 : Blo 247818 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B709249 : Blo 247818 709249 := bstep (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) B531937
theorem B250535 : Blo 247818 250535 := bstep (se 1 (by rfl) ⟨187901, by rfl⟩ : syracuseStep 250535 = 375803) B375803
theorem B1889081 : Blo 247818 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B1201817 : Blo 247818 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B3430583 : Blo 247818 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B3267071 : Blo 247818 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B843263 : Blo 247818 843263 := bstep (se 1 (by rfl) ⟨632447, by rfl⟩ : syracuseStep 843263 = 1264895) B1264895
theorem B10739537 : Blo 247818 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B844667 : Blo 247818 844667 := bstep (se 1 (by rfl) ⟨633500, by rfl⟩ : syracuseStep 844667 = 1267001) B1267001
theorem B845153 : Blo 247818 845153 := bstep (se 2 (by rfl) ⟨316932, by rfl⟩ : syracuseStep 845153 = 633865) B633865
theorem B845801 : Blo 247818 845801 := bstep (se 2 (by rfl) ⟨317175, by rfl⟩ : syracuseStep 845801 = 634351) B634351
theorem B419951 : Blo 247818 419951 := bstep (se 1 (by rfl) ⟨314963, by rfl⟩ : syracuseStep 419951 = 629927) B629927
theorem B846287 : Blo 247818 846287 := bstep (se 1 (by rfl) ⟨634715, by rfl⟩ : syracuseStep 846287 = 1269431) B1269431
theorem B945179 : Blo 247818 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B355433 : Blo 247818 355433 := bstep (se 2 (by rfl) ⟨133287, by rfl⟩ : syracuseStep 355433 = 266575) B266575
theorem B1928377 : Blo 247818 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B421051 : Blo 247818 421051 := bstep (se 1 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 421051 = 631577) B631577
theorem B716015 : Blo 247818 716015 := bstep (se 1 (by rfl) ⟨537011, by rfl⟩ : syracuseStep 716015 = 1074023) B1074023
theorem B422057 : Blo 247818 422057 := bstep (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) B316543
theorem B422543 : Blo 247818 422543 := bstep (se 1 (by rfl) ⟨316907, by rfl⟩ : syracuseStep 422543 = 633815) B633815
theorem B2127131 : Blo 247818 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B2390255 : Blo 247818 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B561401 : Blo 247818 561401 := bstep (se 2 (by rfl) ⟨210525, by rfl⟩ : syracuseStep 561401 = 421051) B421051
theorem B1905119 : Blo 247818 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B562175 : Blo 247818 562175 := bstep (se 1 (by rfl) ⟨421631, by rfl⟩ : syracuseStep 562175 = 843263) B843263
theorem B563111 : Blo 247818 563111 := bstep (se 1 (by rfl) ⟨422333, by rfl⟩ : syracuseStep 563111 = 844667) B844667
theorem B7149545 : Blo 247818 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B563435 : Blo 247818 563435 := bstep (se 1 (by rfl) ⟨422576, by rfl⟩ : syracuseStep 563435 = 845153) B845153
theorem B563867 : Blo 247818 563867 := bstep (se 1 (by rfl) ⟨422900, by rfl⟩ : syracuseStep 563867 = 845801) B845801
theorem B564191 : Blo 247818 564191 := bstep (se 1 (by rfl) ⟨423143, by rfl⟩ : syracuseStep 564191 = 846287) B846287
theorem B630119 : Blo 247818 630119 := bstep (se 1 (by rfl) ⟨472589, by rfl⟩ : syracuseStep 630119 = 945179) B945179
theorem B1418087 : Blo 247818 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1059227 : Blo 247818 1059227 := bstep (se 1 (by rfl) ⟨794420, by rfl⟩ : syracuseStep 1059227 = 1588841) B1588841
theorem B1354553 : Blo 247818 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B1256957 : Blo 247818 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B1257767 : Blo 247818 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1061515 : Blo 247818 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B1259387 : Blo 247818 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B637247 : Blo 247818 637247 := bstep (se 1 (by rfl) ⟨477935, by rfl⟩ : syracuseStep 637247 = 955871) B955871
theorem B2178047 : Blo 247818 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B7159691 : Blo 247818 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B509183 : Blo 247818 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B279967 : Blo 247818 279967 := bstep (se 1 (by rfl) ⟨209975, by rfl⟩ : syracuseStep 279967 = 419951) B419951
theorem B477343 : Blo 247818 477343 := bstep (se 1 (by rfl) ⟨358007, by rfl⟩ : syracuseStep 477343 = 716015) B716015
theorem B281371 : Blo 247818 281371 := bstep (se 1 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 281371 = 422057) B422057
theorem B248647 : Blo 247818 248647 := bstep (se 1 (by rfl) ⟨186485, by rfl⟩ : syracuseStep 248647 = 372971) B372971
theorem B281695 : Blo 247818 281695 := bstep (se 1 (by rfl) ⟨211271, by rfl⟩ : syracuseStep 281695 = 422543) B422543
theorem B248959 : Blo 247818 248959 := bstep (se 1 (by rfl) ⟨186719, by rfl⟩ : syracuseStep 248959 = 373439) B373439
theorem B249151 : Blo 247818 249151 := bstep (se 1 (by rfl) ⟨186863, by rfl⟩ : syracuseStep 249151 = 373727) B373727
theorem B1593503 : Blo 247818 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B250023 : Blo 247818 250023 := bstep (se 1 (by rfl) ⟨187517, by rfl⟩ : syracuseStep 250023 = 375035) B375035
theorem B250079 : Blo 247818 250079 := bstep (se 1 (by rfl) ⟨187559, by rfl⟩ : syracuseStep 250079 = 375119) B375119
theorem B841481 : Blo 247818 841481 := bstep (se 2 (by rfl) ⟨315555, by rfl⟩ : syracuseStep 841481 = 631111) B631111
theorem B2578193 : Blo 247818 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B549343 : Blo 247818 549343 := bstep (se 1 (by rfl) ⟨412007, by rfl⟩ : syracuseStep 549343 = 824015) B824015
theorem B1892969 : Blo 247818 1892969 := bstep (se 2 (by rfl) ⟨709863, by rfl⟩ : syracuseStep 1892969 = 1419727) B1419727
theorem B2287055 : Blo 247818 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B419465 : Blo 247818 419465 := bstep (se 2 (by rfl) ⟨157299, by rfl⟩ : syracuseStep 419465 = 314599) B314599
theorem B3204845 : Blo 247818 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B945665 : Blo 247818 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B10284677 : Blo 247818 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B847529 : Blo 247818 847529 := bstep (se 2 (by rfl) ⟨317823, by rfl⟩ : syracuseStep 847529 = 635647) B635647
theorem B1273967 : Blo 247818 1273967 := bstep (se 1 (by rfl) ⟨955475, by rfl⟩ : syracuseStep 1273967 = 1910951) B1910951
theorem B1143197 : Blo 247818 1143197 := bstep (se 3 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 1143197 = 428699) B428699
theorem B947821 : Blo 247818 947821 := bstep (se 3 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 947821 = 355433) B355433
theorem B560987 : Blo 247818 560987 := bstep (se 1 (by rfl) ⟨420740, by rfl⟩ : syracuseStep 560987 = 841481) B841481
theorem B6098813 : Blo 247818 6098813 := bstep (se 3 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 6098813 = 2287055) B2287055
theorem B1415353 : Blo 247818 1415353 := bstep (se 2 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 1415353 = 1061515) B1061515
theorem B2136563 : Blo 247818 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B630443 : Blo 247818 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B6856451 : Blo 247818 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B565019 : Blo 247818 565019 := bstep (se 1 (by rfl) ⟨423764, by rfl⟩ : syracuseStep 565019 = 847529) B847529
theorem B5808125 : Blo 247818 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B762131 : Blo 247818 762131 := bstep (se 1 (by rfl) ⟨571598, by rfl⟩ : syracuseStep 762131 = 1143197) B1143197
theorem B339455 : Blo 247818 339455 := bstep (se 1 (by rfl) ⟨254591, by rfl⟩ : syracuseStep 339455 = 509183) B509183
theorem B373289 : Blo 247818 373289 := bstep (se 2 (by rfl) ⟨139983, by rfl⟩ : syracuseStep 373289 = 279967) B279967
theorem B2929829 : Blo 247818 2929829 := bstep (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) B549343
theorem B1062335 : Blo 247818 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B374267 : Blo 247818 374267 := bstep (se 1 (by rfl) ⟨280700, by rfl⟩ : syracuseStep 374267 = 561401) B561401
theorem B636457 : Blo 247818 636457 := bstep (se 2 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 636457 = 477343) B477343
theorem B374783 : Blo 247818 374783 := bstep (se 1 (by rfl) ⟨281087, by rfl⟩ : syracuseStep 374783 = 562175) B562175
theorem B375161 : Blo 247818 375161 := bstep (se 2 (by rfl) ⟨140685, by rfl⟩ : syracuseStep 375161 = 281371) B281371
theorem B1718795 : Blo 247818 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B375407 : Blo 247818 375407 := bstep (se 1 (by rfl) ⟨281555, by rfl⟩ : syracuseStep 375407 = 563111) B563111
theorem B4766363 : Blo 247818 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B375593 : Blo 247818 375593 := bstep (se 2 (by rfl) ⟨140847, by rfl⟩ : syracuseStep 375593 = 281695) B281695
theorem B375623 : Blo 247818 375623 := bstep (se 1 (by rfl) ⟨281717, by rfl⟩ : syracuseStep 375623 = 563435) B563435
theorem B375911 : Blo 247818 375911 := bstep (se 1 (by rfl) ⟨281933, by rfl⟩ : syracuseStep 375911 = 563867) B563867
theorem B376127 : Blo 247818 376127 := bstep (se 1 (by rfl) ⟨282095, by rfl⟩ : syracuseStep 376127 = 564191) B564191
theorem B1261979 : Blo 247818 1261979 := bstep (se 1 (by rfl) ⟨946484, by rfl⟩ : syracuseStep 1261979 = 1892969) B1892969
theorem B279643 : Blo 247818 279643 := bstep (se 1 (by rfl) ⟨209732, by rfl⟩ : syracuseStep 279643 = 419465) B419465
theorem B706151 : Blo 247818 706151 := bstep (se 1 (by rfl) ⟨529613, by rfl⟩ : syracuseStep 706151 = 1059227) B1059227
theorem B903035 : Blo 247818 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1263761 : Blo 247818 1263761 := bstep (se 2 (by rfl) ⟨473910, by rfl⟩ : syracuseStep 1263761 = 947821) B947821
theorem B837971 : Blo 247818 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B838511 : Blo 247818 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B839591 : Blo 247818 839591 := bstep (se 1 (by rfl) ⟨629693, by rfl⟩ : syracuseStep 839591 = 1259387) B1259387
theorem B4773127 : Blo 247818 4773127 := bstep (se 1 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 4773127 = 7159691) B7159691
theorem B1270079 : Blo 247818 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B420079 : Blo 247818 420079 := bstep (se 1 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 420079 = 630119) B630119
theorem B945391 : Blo 247818 945391 := bstep (se 1 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 945391 = 1418087) B1418087
theorem B849311 : Blo 247818 849311 := bstep (se 1 (by rfl) ⟨636983, by rfl⟩ : syracuseStep 849311 = 1273967) B1273967
theorem B424831 : Blo 247818 424831 := bstep (se 1 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 424831 = 637247) B637247
theorem B558647 : Blo 247818 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B559007 : Blo 247818 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B4065875 : Blo 247818 4065875 := bstep (se 1 (by rfl) ⟨3049406, by rfl⟩ : syracuseStep 4065875 = 6098813) B6098813
theorem B559727 : Blo 247818 559727 := bstep (se 1 (by rfl) ⟨419795, by rfl⟩ : syracuseStep 559727 = 839591) B839591
theorem B560105 : Blo 247818 560105 := bstep (se 2 (by rfl) ⟨210039, by rfl⟩ : syracuseStep 560105 = 420079) B420079
theorem B3872083 : Blo 247818 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B6364169 : Blo 247818 6364169 := bstep (se 2 (by rfl) ⟨2386563, by rfl⟩ : syracuseStep 6364169 = 4773127) B4773127
theorem B566207 : Blo 247818 566207 := bstep (se 1 (by rfl) ⟨424655, by rfl⟩ : syracuseStep 566207 = 849311) B849311
theorem B566441 : Blo 247818 566441 := bstep (se 2 (by rfl) ⟨212415, by rfl⟩ : syracuseStep 566441 = 424831) B424831
theorem B470767 : Blo 247818 470767 := bstep (se 1 (by rfl) ⟨353075, by rfl⟩ : syracuseStep 470767 = 706151) B706151
theorem B372857 : Blo 247818 372857 := bstep (se 2 (by rfl) ⟨139821, by rfl⟩ : syracuseStep 372857 = 279643) B279643
theorem B373991 : Blo 247818 373991 := bstep (se 1 (by rfl) ⟨280493, by rfl⟩ : syracuseStep 373991 = 560987) B560987
theorem B7812877 : Blo 247818 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B2832893 : Blo 247818 2832893 := bstep (se 3 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 2832893 = 1062335) B1062335
theorem B1260521 : Blo 247818 1260521 := bstep (se 2 (by rfl) ⟨472695, by rfl⟩ : syracuseStep 1260521 = 945391) B945391
theorem B1424375 : Blo 247818 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B2408093 : Blo 247818 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B4570967 : Blo 247818 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B376679 : Blo 247818 376679 := bstep (se 1 (by rfl) ⟨282509, by rfl⟩ : syracuseStep 376679 = 565019) B565019
theorem B508087 : Blo 247818 508087 := bstep (se 1 (by rfl) ⟨381065, by rfl⟩ : syracuseStep 508087 = 762131) B762131
theorem B1887137 : Blo 247818 1887137 := bstep (se 2 (by rfl) ⟨707676, by rfl⟩ : syracuseStep 1887137 = 1415353) B1415353
theorem B248859 : Blo 247818 248859 := bstep (se 1 (by rfl) ⟨186644, by rfl⟩ : syracuseStep 248859 = 373289) B373289
theorem B249511 : Blo 247818 249511 := bstep (se 1 (by rfl) ⟨187133, by rfl⟩ : syracuseStep 249511 = 374267) B374267
theorem B905213 : Blo 247818 905213 := bstep (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) B339455
theorem B249855 : Blo 247818 249855 := bstep (se 1 (by rfl) ⟨187391, by rfl⟩ : syracuseStep 249855 = 374783) B374783
theorem B250107 : Blo 247818 250107 := bstep (se 1 (by rfl) ⟨187580, by rfl⟩ : syracuseStep 250107 = 375161) B375161
theorem B250271 : Blo 247818 250271 := bstep (se 1 (by rfl) ⟨187703, by rfl⟩ : syracuseStep 250271 = 375407) B375407
theorem B250395 : Blo 247818 250395 := bstep (se 1 (by rfl) ⟨187796, by rfl⟩ : syracuseStep 250395 = 375593) B375593
theorem B250415 : Blo 247818 250415 := bstep (se 1 (by rfl) ⟨187811, by rfl⟩ : syracuseStep 250415 = 375623) B375623
theorem B250607 : Blo 247818 250607 := bstep (se 1 (by rfl) ⟨187955, by rfl⟩ : syracuseStep 250607 = 375911) B375911
theorem B250751 : Blo 247818 250751 := bstep (se 1 (by rfl) ⟨188063, by rfl⟩ : syracuseStep 250751 = 376127) B376127
theorem B841319 : Blo 247818 841319 := bstep (se 1 (by rfl) ⟨630989, by rfl⟩ : syracuseStep 841319 = 1261979) B1261979
theorem B842507 : Blo 247818 842507 := bstep (se 1 (by rfl) ⟨631880, by rfl⟩ : syracuseStep 842507 = 1263761) B1263761
theorem B420295 : Blo 247818 420295 := bstep (se 1 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 420295 = 630443) B630443
theorem B846719 : Blo 247818 846719 := bstep (se 1 (by rfl) ⟨635039, by rfl⟩ : syracuseStep 846719 = 1270079) B1270079
theorem B848609 : Blo 247818 848609 := bstep (se 2 (by rfl) ⟨318228, by rfl⟩ : syracuseStep 848609 = 636457) B636457
theorem B1145863 : Blo 247818 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B3177575 : Blo 247818 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B560393 : Blo 247818 560393 := bstep (se 2 (by rfl) ⟨210147, by rfl⟩ : syracuseStep 560393 = 420295) B420295
theorem B560879 : Blo 247818 560879 := bstep (se 1 (by rfl) ⟨420659, by rfl⟩ : syracuseStep 560879 = 841319) B841319
theorem B561671 : Blo 247818 561671 := bstep (se 1 (by rfl) ⟨421253, by rfl⟩ : syracuseStep 561671 = 842507) B842507
theorem B627689 : Blo 247818 627689 := bstep (se 2 (by rfl) ⟨235383, by rfl⟩ : syracuseStep 627689 = 470767) B470767
theorem B564479 : Blo 247818 564479 := bstep (se 1 (by rfl) ⟨423359, by rfl⟩ : syracuseStep 564479 = 846719) B846719
theorem B565739 : Blo 247818 565739 := bstep (se 1 (by rfl) ⟨424304, by rfl⟩ : syracuseStep 565739 = 848609) B848609
theorem B372431 : Blo 247818 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B372671 : Blo 247818 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B373151 : Blo 247818 373151 := bstep (se 1 (by rfl) ⟨279863, by rfl⟩ : syracuseStep 373151 = 559727) B559727
theorem B1258091 : Blo 247818 1258091 := bstep (se 1 (by rfl) ⟨943568, by rfl⟩ : syracuseStep 1258091 = 1887137) B1887137
theorem B373403 : Blo 247818 373403 := bstep (se 1 (by rfl) ⟨280052, by rfl⟩ : syracuseStep 373403 = 560105) B560105
theorem B4242779 : Blo 247818 4242779 := bstep (se 1 (by rfl) ⟨3182084, by rfl⟩ : syracuseStep 4242779 = 6364169) B6364169
theorem B377471 : Blo 247818 377471 := bstep (se 1 (by rfl) ⟨283103, by rfl⟩ : syracuseStep 377471 = 566207) B566207
theorem B377627 : Blo 247818 377627 := bstep (se 1 (by rfl) ⟨283220, by rfl⟩ : syracuseStep 377627 = 566441) B566441
theorem B5162777 : Blo 247818 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B248571 : Blo 247818 248571 := bstep (se 1 (by rfl) ⟨186428, by rfl⟩ : syracuseStep 248571 = 372857) B372857
theorem B249327 : Blo 247818 249327 := bstep (se 1 (by rfl) ⟨186995, by rfl⟩ : syracuseStep 249327 = 373991) B373991
theorem B1527817 : Blo 247818 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B1888595 : Blo 247818 1888595 := bstep (se 1 (by rfl) ⟨1416446, by rfl⟩ : syracuseStep 1888595 = 2832893) B2832893
theorem B840347 : Blo 247818 840347 := bstep (se 1 (by rfl) ⟨630260, by rfl⟩ : syracuseStep 840347 = 1260521) B1260521
theorem B2118383 : Blo 247818 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B251119 : Blo 247818 251119 := bstep (se 1 (by rfl) ⟨188339, by rfl⟩ : syracuseStep 251119 = 376679) B376679
theorem B2413901 : Blo 247818 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B677449 : Blo 247818 677449 := bstep (se 2 (by rfl) ⟨254043, by rfl⟩ : syracuseStep 677449 = 508087) B508087
theorem B2710583 : Blo 247818 2710583 := bstep (se 1 (by rfl) ⟨2032937, by rfl⟩ : syracuseStep 2710583 = 4065875) B4065875
theorem B10417169 : Blo 247818 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B949583 : Blo 247818 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B1605395 : Blo 247818 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B3047311 : Blo 247818 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B3441851 : Blo 247818 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B560231 : Blo 247818 560231 := bstep (se 1 (by rfl) ⟨420173, by rfl⟩ : syracuseStep 560231 = 840347) B840347
theorem B1412255 : Blo 247818 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1609267 : Blo 247818 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B1807055 : Blo 247818 1807055 := bstep (se 1 (by rfl) ⟨1355291, by rfl⟩ : syracuseStep 1807055 = 2710583) B2710583
theorem B2037089 : Blo 247818 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B3613061 : Blo 247818 3613061 := bstep (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) B677449
theorem B633055 : Blo 247818 633055 := bstep (se 1 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 633055 = 949583) B949583
theorem B2828519 : Blo 247818 2828519 := bstep (se 1 (by rfl) ⟨2121389, by rfl⟩ : syracuseStep 2828519 = 4242779) B4242779
theorem B373595 : Blo 247818 373595 := bstep (se 1 (by rfl) ⟨280196, by rfl⟩ : syracuseStep 373595 = 560393) B560393
theorem B373919 : Blo 247818 373919 := bstep (se 1 (by rfl) ⟨280439, by rfl⟩ : syracuseStep 373919 = 560879) B560879
theorem B1259063 : Blo 247818 1259063 := bstep (se 1 (by rfl) ⟨944297, by rfl⟩ : syracuseStep 1259063 = 1888595) B1888595
theorem B374447 : Blo 247818 374447 := bstep (se 1 (by rfl) ⟨280835, by rfl⟩ : syracuseStep 374447 = 561671) B561671
theorem B376319 : Blo 247818 376319 := bstep (se 1 (by rfl) ⟨282239, by rfl⟩ : syracuseStep 376319 = 564479) B564479
theorem B377159 : Blo 247818 377159 := bstep (se 1 (by rfl) ⟨282869, by rfl⟩ : syracuseStep 377159 = 565739) B565739
theorem B248287 : Blo 247818 248287 := bstep (se 1 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 248287 = 372431) B372431
theorem B248447 : Blo 247818 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B248767 : Blo 247818 248767 := bstep (se 1 (by rfl) ⟨186575, by rfl⟩ : syracuseStep 248767 = 373151) B373151
theorem B838727 : Blo 247818 838727 := bstep (se 1 (by rfl) ⟨629045, by rfl⟩ : syracuseStep 838727 = 1258091) B1258091
theorem B248935 : Blo 247818 248935 := bstep (se 1 (by rfl) ⟨186701, by rfl⟩ : syracuseStep 248935 = 373403) B373403
theorem B1070263 : Blo 247818 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B251647 : Blo 247818 251647 := bstep (se 1 (by rfl) ⟨188735, by rfl⟩ : syracuseStep 251647 = 377471) B377471
theorem B251751 : Blo 247818 251751 := bstep (se 1 (by rfl) ⟨188813, by rfl⟩ : syracuseStep 251751 = 377627) B377627
theorem B418459 : Blo 247818 418459 := bstep (se 1 (by rfl) ⟨313844, by rfl⟩ : syracuseStep 418459 = 627689) B627689
theorem B6944779 : Blo 247818 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B4063081 : Blo 247818 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B2294567 : Blo 247818 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B557945 : Blo 247818 557945 := bstep (se 2 (by rfl) ⟨209229, by rfl⟩ : syracuseStep 557945 = 418459) B418459
theorem B559151 : Blo 247818 559151 := bstep (se 1 (by rfl) ⟨419363, by rfl⟩ : syracuseStep 559151 = 838727) B838727
theorem B5417441 : Blo 247818 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B373487 : Blo 247818 373487 := bstep (se 1 (by rfl) ⟨280115, by rfl⟩ : syracuseStep 373487 = 560231) B560231
theorem B1358059 : Blo 247818 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B2145689 : Blo 247818 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B2408707 : Blo 247818 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B1885679 : Blo 247818 1885679 := bstep (se 1 (by rfl) ⟨1414259, by rfl⟩ : syracuseStep 1885679 = 2828519) B2828519
theorem B1427017 : Blo 247818 1427017 := bstep (se 2 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 1427017 = 1070263) B1070263
theorem B9259705 : Blo 247818 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B249063 : Blo 247818 249063 := bstep (se 1 (by rfl) ⟨186797, by rfl⟩ : syracuseStep 249063 = 373595) B373595
theorem B249279 : Blo 247818 249279 := bstep (se 1 (by rfl) ⟨186959, by rfl⟩ : syracuseStep 249279 = 373919) B373919
theorem B839375 : Blo 247818 839375 := bstep (se 1 (by rfl) ⟨629531, by rfl⟩ : syracuseStep 839375 = 1259063) B1259063
theorem B249631 : Blo 247818 249631 := bstep (se 1 (by rfl) ⟨187223, by rfl⟩ : syracuseStep 249631 = 374447) B374447
theorem B250879 : Blo 247818 250879 := bstep (se 1 (by rfl) ⟨188159, by rfl⟩ : syracuseStep 250879 = 376319) B376319
theorem B251439 : Blo 247818 251439 := bstep (se 1 (by rfl) ⟨188579, by rfl⟩ : syracuseStep 251439 = 377159) B377159
theorem B941503 : Blo 247818 941503 := bstep (se 1 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 941503 = 1412255) B1412255
theorem B844073 : Blo 247818 844073 := bstep (se 2 (by rfl) ⟨316527, by rfl⟩ : syracuseStep 844073 = 633055) B633055
theorem B1204703 : Blo 247818 1204703 := bstep (se 1 (by rfl) ⟨903527, by rfl⟩ : syracuseStep 1204703 = 1807055) B1807055
theorem B3211609 : Blo 247818 3211609 := bstep (se 2 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 3211609 = 2408707) B2408707
theorem B1902689 : Blo 247818 1902689 := bstep (se 2 (by rfl) ⟨713508, by rfl⟩ : syracuseStep 1902689 = 1427017) B1427017
theorem B559583 : Blo 247818 559583 := bstep (se 1 (by rfl) ⟨419687, by rfl⟩ : syracuseStep 559583 = 839375) B839375
theorem B562715 : Blo 247818 562715 := bstep (se 1 (by rfl) ⟨422036, by rfl⟩ : syracuseStep 562715 = 844073) B844073
theorem B3611627 : Blo 247818 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B1810745 : Blo 247818 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B1255337 : Blo 247818 1255337 := bstep (se 2 (by rfl) ⟨470751, by rfl⟩ : syracuseStep 1255337 = 941503) B941503
theorem B371963 : Blo 247818 371963 := bstep (se 1 (by rfl) ⟨278972, by rfl⟩ : syracuseStep 371963 = 557945) B557945
theorem B1257119 : Blo 247818 1257119 := bstep (se 1 (by rfl) ⟨942839, by rfl⟩ : syracuseStep 1257119 = 1885679) B1885679
theorem B372767 : Blo 247818 372767 := bstep (se 1 (by rfl) ⟨279575, by rfl⟩ : syracuseStep 372767 = 559151) B559151
theorem B803135 : Blo 247818 803135 := bstep (se 1 (by rfl) ⟨602351, by rfl⟩ : syracuseStep 803135 = 1204703) B1204703
theorem B248991 : Blo 247818 248991 := bstep (se 1 (by rfl) ⟨186743, by rfl⟩ : syracuseStep 248991 = 373487) B373487
theorem B1430459 : Blo 247818 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B1529711 : Blo 247818 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B12346273 : Blo 247818 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B953639 : Blo 247818 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B1019807 : Blo 247818 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B535423 : Blo 247818 535423 := bstep (se 1 (by rfl) ⟨401567, by rfl⟩ : syracuseStep 535423 = 803135) B803135
theorem B373055 : Blo 247818 373055 := bstep (se 1 (by rfl) ⟨279791, by rfl⟩ : syracuseStep 373055 = 559583) B559583
theorem B375143 : Blo 247818 375143 := bstep (se 1 (by rfl) ⟨281357, by rfl⟩ : syracuseStep 375143 = 562715) B562715
theorem B2407751 : Blo 247818 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B65846789 : Blo 247818 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B836891 : Blo 247818 836891 := bstep (se 1 (by rfl) ⟨627668, by rfl⟩ : syracuseStep 836891 = 1255337) B1255337
theorem B247975 : Blo 247818 247975 := bstep (se 1 (by rfl) ⟨185981, by rfl⟩ : syracuseStep 247975 = 371963) B371963
theorem B838079 : Blo 247818 838079 := bstep (se 1 (by rfl) ⟨628559, by rfl⟩ : syracuseStep 838079 = 1257119) B1257119
theorem B248511 : Blo 247818 248511 := bstep (se 1 (by rfl) ⟨186383, by rfl⟩ : syracuseStep 248511 = 372767) B372767
theorem B4282145 : Blo 247818 4282145 := bstep (se 2 (by rfl) ⟨1605804, by rfl⟩ : syracuseStep 4282145 = 3211609) B3211609
theorem B1268459 : Blo 247818 1268459 := bstep (se 1 (by rfl) ⟨951344, by rfl⟩ : syracuseStep 1268459 = 1902689) B1902689
theorem B1207163 : Blo 247818 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B557927 : Blo 247818 557927 := bstep (se 1 (by rfl) ⟨418445, by rfl⟩ : syracuseStep 557927 = 836891) B836891
theorem B558719 : Blo 247818 558719 := bstep (se 1 (by rfl) ⟨419039, by rfl⟩ : syracuseStep 558719 = 838079) B838079
theorem B2854763 : Blo 247818 2854763 := bstep (se 1 (by rfl) ⟨2141072, by rfl⟩ : syracuseStep 2854763 = 4282145) B4282145
theorem B635759 : Blo 247818 635759 := bstep (se 1 (by rfl) ⟨476819, by rfl⟩ : syracuseStep 635759 = 953639) B953639
theorem B804775 : Blo 247818 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B248703 : Blo 247818 248703 := bstep (se 1 (by rfl) ⟨186527, by rfl⟩ : syracuseStep 248703 = 373055) B373055
theorem B250095 : Blo 247818 250095 := bstep (se 1 (by rfl) ⟨187571, by rfl⟩ : syracuseStep 250095 = 375143) B375143
theorem B43897859 : Blo 247818 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B679871 : Blo 247818 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B713897 : Blo 247818 713897 := bstep (se 2 (by rfl) ⟨267711, by rfl⟩ : syracuseStep 713897 = 535423) B535423
theorem B845639 : Blo 247818 845639 := bstep (se 1 (by rfl) ⟨634229, by rfl⟩ : syracuseStep 845639 = 1268459) B1268459
theorem B1605167 : Blo 247818 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B1903175 : Blo 247818 1903175 := bstep (se 1 (by rfl) ⟨1427381, by rfl⟩ : syracuseStep 1903175 = 2854763) B2854763
theorem B29265239 : Blo 247818 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B563759 : Blo 247818 563759 := bstep (se 1 (by rfl) ⟨422819, by rfl⟩ : syracuseStep 563759 = 845639) B845639
theorem B1812989 : Blo 247818 1812989 := bstep (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) B679871
theorem B371951 : Blo 247818 371951 := bstep (se 1 (by rfl) ⟨278963, by rfl⟩ : syracuseStep 371951 = 557927) B557927
theorem B372479 : Blo 247818 372479 := bstep (se 1 (by rfl) ⟨279359, by rfl⟩ : syracuseStep 372479 = 558719) B558719
theorem B475931 : Blo 247818 475931 := bstep (se 1 (by rfl) ⟨356948, by rfl⟩ : syracuseStep 475931 = 713897) B713897
theorem B1070111 : Blo 247818 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B1073033 : Blo 247818 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B423839 : Blo 247818 423839 := bstep (se 1 (by rfl) ⟨317879, by rfl⟩ : syracuseStep 423839 = 635759) B635759
theorem B19510159 : Blo 247818 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B375839 : Blo 247818 375839 := bstep (se 1 (by rfl) ⟨281879, by rfl⟩ : syracuseStep 375839 = 563759) B563759
theorem B4834637 : Blo 247818 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B247967 : Blo 247818 247967 := bstep (se 1 (by rfl) ⟨185975, by rfl⟩ : syracuseStep 247967 = 371951) B371951
theorem B248319 : Blo 247818 248319 := bstep (se 1 (by rfl) ⟨186239, by rfl⟩ : syracuseStep 248319 = 372479) B372479
theorem B282559 : Blo 247818 282559 := bstep (se 1 (by rfl) ⟨211919, by rfl⟩ : syracuseStep 282559 = 423839) B423839
theorem B317287 : Blo 247818 317287 := bstep (se 1 (by rfl) ⟨237965, by rfl⟩ : syracuseStep 317287 = 475931) B475931
theorem B1268783 : Blo 247818 1268783 := bstep (se 1 (by rfl) ⟨951587, by rfl⟩ : syracuseStep 1268783 = 1903175) B1903175
theorem B713407 : Blo 247818 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B715355 : Blo 247818 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B951209 : Blo 247818 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B3223091 : Blo 247818 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B376745 : Blo 247818 376745 := bstep (se 2 (by rfl) ⟨141279, by rfl⟩ : syracuseStep 376745 = 282559) B282559
theorem B476903 : Blo 247818 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B250559 : Blo 247818 250559 := bstep (se 1 (by rfl) ⟨187919, by rfl⟩ : syracuseStep 250559 = 375839) B375839
theorem B845855 : Blo 247818 845855 := bstep (se 1 (by rfl) ⟨634391, by rfl⟩ : syracuseStep 845855 = 1268783) B1268783
theorem B26013545 : Blo 247818 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B423049 : Blo 247818 423049 := bstep (se 2 (by rfl) ⟨158643, by rfl⟩ : syracuseStep 423049 = 317287) B317287
theorem B563903 : Blo 247818 563903 := bstep (se 1 (by rfl) ⟨422927, by rfl⟩ : syracuseStep 563903 = 845855) B845855
theorem B564065 : Blo 247818 564065 := bstep (se 2 (by rfl) ⟨211524, by rfl⟩ : syracuseStep 564065 = 423049) B423049
theorem B17342363 : Blo 247818 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B634139 : Blo 247818 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B2148727 : Blo 247818 2148727 := bstep (se 1 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 2148727 = 3223091) B3223091
theorem B251163 : Blo 247818 251163 := bstep (se 1 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 251163 = 376745) B376745
theorem B317935 : Blo 247818 317935 := bstep (se 1 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 317935 = 476903) B476903
theorem B2864969 : Blo 247818 2864969 := bstep (se 2 (by rfl) ⟨1074363, by rfl⟩ : syracuseStep 2864969 = 2148727) B2148727
theorem B375935 : Blo 247818 375935 := bstep (se 1 (by rfl) ⟨281951, by rfl⟩ : syracuseStep 375935 = 563903) B563903
theorem B376043 : Blo 247818 376043 := bstep (se 1 (by rfl) ⟨282032, by rfl⟩ : syracuseStep 376043 = 564065) B564065
theorem B11561575 : Blo 247818 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B422759 : Blo 247818 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B423913 : Blo 247818 423913 := bstep (se 2 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 423913 = 317935) B317935
theorem B565217 : Blo 247818 565217 := bstep (se 2 (by rfl) ⟨211956, by rfl⟩ : syracuseStep 565217 = 423913) B423913
theorem B1909979 : Blo 247818 1909979 := bstep (se 1 (by rfl) ⟨1432484, by rfl⟩ : syracuseStep 1909979 = 2864969) B2864969
theorem B15415433 : Blo 247818 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B281839 : Blo 247818 281839 := bstep (se 1 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 281839 = 422759) B422759
theorem B250623 : Blo 247818 250623 := bstep (se 1 (by rfl) ⟨187967, by rfl⟩ : syracuseStep 250623 = 375935) B375935
theorem B250695 : Blo 247818 250695 := bstep (se 1 (by rfl) ⟨188021, by rfl⟩ : syracuseStep 250695 = 376043) B376043
theorem B375785 : Blo 247818 375785 := bstep (se 2 (by rfl) ⟨140919, by rfl⟩ : syracuseStep 375785 = 281839) B281839
theorem B376811 : Blo 247818 376811 := bstep (se 1 (by rfl) ⟨282608, by rfl⟩ : syracuseStep 376811 = 565217) B565217
theorem B10276955 : Blo 247818 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B1273319 : Blo 247818 1273319 := bstep (se 1 (by rfl) ⟨954989, by rfl⟩ : syracuseStep 1273319 = 1909979) B1909979
theorem B6851303 : Blo 247818 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B250523 : Blo 247818 250523 := bstep (se 1 (by rfl) ⟨187892, by rfl⟩ : syracuseStep 250523 = 375785) B375785
theorem B251207 : Blo 247818 251207 := bstep (se 1 (by rfl) ⟨188405, by rfl⟩ : syracuseStep 251207 = 376811) B376811
theorem B848879 : Blo 247818 848879 := bstep (se 1 (by rfl) ⟨636659, by rfl⟩ : syracuseStep 848879 = 1273319) B1273319
theorem B565919 : Blo 247818 565919 := bstep (se 1 (by rfl) ⟨424439, by rfl⟩ : syracuseStep 565919 = 848879) B848879
theorem B4567535 : Blo 247818 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B377279 : Blo 247818 377279 := bstep (se 1 (by rfl) ⟨282959, by rfl⟩ : syracuseStep 377279 = 565919) B565919
theorem B3045023 : Blo 247818 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B251519 : Blo 247818 251519 := bstep (se 1 (by rfl) ⟨188639, by rfl⟩ : syracuseStep 251519 = 377279) B377279
theorem B2030015 : Blo 247818 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B1353343 : Blo 247818 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B1804457 : Blo 247818 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B1202971 : Blo 247818 1202971 := bstep (se 1 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 1202971 = 1804457) B1804457
theorem B1603961 : Blo 247818 1603961 := bstep (se 2 (by rfl) ⟨601485, by rfl⟩ : syracuseStep 1603961 = 1202971) B1202971
theorem B1069307 : Blo 247818 1069307 := bstep (se 1 (by rfl) ⟨801980, by rfl⟩ : syracuseStep 1069307 = 1603961) B1603961
theorem B712871 : Blo 247818 712871 := bstep (se 1 (by rfl) ⟨534653, by rfl⟩ : syracuseStep 712871 = 1069307) B1069307
theorem B475247 : Blo 247818 475247 := bstep (se 1 (by rfl) ⟨356435, by rfl⟩ : syracuseStep 475247 = 712871) B712871
theorem B1267325 : Blo 247818 1267325 := bstep (se 3 (by rfl) ⟨237623, by rfl⟩ : syracuseStep 1267325 = 475247) B475247
theorem B844883 : Blo 247818 844883 := bstep (se 1 (by rfl) ⟨633662, by rfl⟩ : syracuseStep 844883 = 1267325) B1267325
theorem B563255 : Blo 247818 563255 := bstep (se 1 (by rfl) ⟨422441, by rfl⟩ : syracuseStep 563255 = 844883) B844883
theorem B375503 : Blo 247818 375503 := bstep (se 1 (by rfl) ⟨281627, by rfl⟩ : syracuseStep 375503 = 563255) B563255
theorem B250335 : Blo 247818 250335 := bstep (se 1 (by rfl) ⟨187751, by rfl⟩ : syracuseStep 250335 = 375503) B375503

theorem C0 (j : ℕ) (h1 : 61954 ≤ j) (h2 : j ≤ 62653) : Blo 247818 (4 * j + 3) := by
  interval_cases j
  · exact B247819
  · exact B247823
  · exact B247827
  · exact B247831
  · exact B247835
  · exact B247839
  · exact B247843
  · exact B247847
  · exact B247851
  · exact B247855
  · exact B247859
  · exact B247863
  · exact B247867
  · exact B247871
  · exact B247875
  · exact B247879
  · exact B247883
  · exact B247887
  · exact B247891
  · exact B247895
  · exact B247899
  · exact B247903
  · exact B247907
  · exact B247911
  · exact B247915
  · exact B247919
  · exact B247923
  · exact B247927
  · exact B247931
  · exact B247935
  · exact B247939
  · exact B247943
  · exact B247947
  · exact B247951
  · exact B247955
  · exact B247959
  · exact B247963
  · exact B247967
  · exact B247971
  · exact B247975
  · exact B247979
  · exact B247983
  · exact B247987
  · exact B247991
  · exact B247995
  · exact B247999
  · exact B248003
  · exact B248007
  · exact B248011
  · exact B248015
  · exact B248019
  · exact B248023
  · exact B248027
  · exact B248031
  · exact B248035
  · exact B248039
  · exact B248043
  · exact B248047
  · exact B248051
  · exact B248055
  · exact B248059
  · exact B248063
  · exact B248067
  · exact B248071
  · exact B248075
  · exact B248079
  · exact B248083
  · exact B248087
  · exact B248091
  · exact B248095
  · exact B248099
  · exact B248103
  · exact B248107
  · exact B248111
  · exact B248115
  · exact B248119
  · exact B248123
  · exact B248127
  · exact B248131
  · exact B248135
  · exact B248139
  · exact B248143
  · exact B248147
  · exact B248151
  · exact B248155
  · exact B248159
  · exact B248163
  · exact B248167
  · exact B248171
  · exact B248175
  · exact B248179
  · exact B248183
  · exact B248187
  · exact B248191
  · exact B248195
  · exact B248199
  · exact B248203
  · exact B248207
  · exact B248211
  · exact B248215
  · exact B248219
  · exact B248223
  · exact B248227
  · exact B248231
  · exact B248235
  · exact B248239
  · exact B248243
  · exact B248247
  · exact B248251
  · exact B248255
  · exact B248259
  · exact B248263
  · exact B248267
  · exact B248271
  · exact B248275
  · exact B248279
  · exact B248283
  · exact B248287
  · exact B248291
  · exact B248295
  · exact B248299
  · exact B248303
  · exact B248307
  · exact B248311
  · exact B248315
  · exact B248319
  · exact B248323
  · exact B248327
  · exact B248331
  · exact B248335
  · exact B248339
  · exact B248343
  · exact B248347
  · exact B248351
  · exact B248355
  · exact B248359
  · exact B248363
  · exact B248367
  · exact B248371
  · exact B248375
  · exact B248379
  · exact B248383
  · exact B248387
  · exact B248391
  · exact B248395
  · exact B248399
  · exact B248403
  · exact B248407
  · exact B248411
  · exact B248415
  · exact B248419
  · exact B248423
  · exact B248427
  · exact B248431
  · exact B248435
  · exact B248439
  · exact B248443
  · exact B248447
  · exact B248451
  · exact B248455
  · exact B248459
  · exact B248463
  · exact B248467
  · exact B248471
  · exact B248475
  · exact B248479
  · exact B248483
  · exact B248487
  · exact B248491
  · exact B248495
  · exact B248499
  · exact B248503
  · exact B248507
  · exact B248511
  · exact B248515
  · exact B248519
  · exact B248523
  · exact B248527
  · exact B248531
  · exact B248535
  · exact B248539
  · exact B248543
  · exact B248547
  · exact B248551
  · exact B248555
  · exact B248559
  · exact B248563
  · exact B248567
  · exact B248571
  · exact B248575
  · exact B248579
  · exact B248583
  · exact B248587
  · exact B248591
  · exact B248595
  · exact B248599
  · exact B248603
  · exact B248607
  · exact B248611
  · exact B248615
  · exact B248619
  · exact B248623
  · exact B248627
  · exact B248631
  · exact B248635
  · exact B248639
  · exact B248643
  · exact B248647
  · exact B248651
  · exact B248655
  · exact B248659
  · exact B248663
  · exact B248667
  · exact B248671
  · exact B248675
  · exact B248679
  · exact B248683
  · exact B248687
  · exact B248691
  · exact B248695
  · exact B248699
  · exact B248703
  · exact B248707
  · exact B248711
  · exact B248715
  · exact B248719
  · exact B248723
  · exact B248727
  · exact B248731
  · exact B248735
  · exact B248739
  · exact B248743
  · exact B248747
  · exact B248751
  · exact B248755
  · exact B248759
  · exact B248763
  · exact B248767
  · exact B248771
  · exact B248775
  · exact B248779
  · exact B248783
  · exact B248787
  · exact B248791
  · exact B248795
  · exact B248799
  · exact B248803
  · exact B248807
  · exact B248811
  · exact B248815
  · exact B248819
  · exact B248823
  · exact B248827
  · exact B248831
  · exact B248835
  · exact B248839
  · exact B248843
  · exact B248847
  · exact B248851
  · exact B248855
  · exact B248859
  · exact B248863
  · exact B248867
  · exact B248871
  · exact B248875
  · exact B248879
  · exact B248883
  · exact B248887
  · exact B248891
  · exact B248895
  · exact B248899
  · exact B248903
  · exact B248907
  · exact B248911
  · exact B248915
  · exact B248919
  · exact B248923
  · exact B248927
  · exact B248931
  · exact B248935
  · exact B248939
  · exact B248943
  · exact B248947
  · exact B248951
  · exact B248955
  · exact B248959
  · exact B248963
  · exact B248967
  · exact B248971
  · exact B248975
  · exact B248979
  · exact B248983
  · exact B248987
  · exact B248991
  · exact B248995
  · exact B248999
  · exact B249003
  · exact B249007
  · exact B249011
  · exact B249015
  · exact B249019
  · exact B249023
  · exact B249027
  · exact B249031
  · exact B249035
  · exact B249039
  · exact B249043
  · exact B249047
  · exact B249051
  · exact B249055
  · exact B249059
  · exact B249063
  · exact B249067
  · exact B249071
  · exact B249075
  · exact B249079
  · exact B249083
  · exact B249087
  · exact B249091
  · exact B249095
  · exact B249099
  · exact B249103
  · exact B249107
  · exact B249111
  · exact B249115
  · exact B249119
  · exact B249123
  · exact B249127
  · exact B249131
  · exact B249135
  · exact B249139
  · exact B249143
  · exact B249147
  · exact B249151
  · exact B249155
  · exact B249159
  · exact B249163
  · exact B249167
  · exact B249171
  · exact B249175
  · exact B249179
  · exact B249183
  · exact B249187
  · exact B249191
  · exact B249195
  · exact B249199
  · exact B249203
  · exact B249207
  · exact B249211
  · exact B249215
  · exact B249219
  · exact B249223
  · exact B249227
  · exact B249231
  · exact B249235
  · exact B249239
  · exact B249243
  · exact B249247
  · exact B249251
  · exact B249255
  · exact B249259
  · exact B249263
  · exact B249267
  · exact B249271
  · exact B249275
  · exact B249279
  · exact B249283
  · exact B249287
  · exact B249291
  · exact B249295
  · exact B249299
  · exact B249303
  · exact B249307
  · exact B249311
  · exact B249315
  · exact B249319
  · exact B249323
  · exact B249327
  · exact B249331
  · exact B249335
  · exact B249339
  · exact B249343
  · exact B249347
  · exact B249351
  · exact B249355
  · exact B249359
  · exact B249363
  · exact B249367
  · exact B249371
  · exact B249375
  · exact B249379
  · exact B249383
  · exact B249387
  · exact B249391
  · exact B249395
  · exact B249399
  · exact B249403
  · exact B249407
  · exact B249411
  · exact B249415
  · exact B249419
  · exact B249423
  · exact B249427
  · exact B249431
  · exact B249435
  · exact B249439
  · exact B249443
  · exact B249447
  · exact B249451
  · exact B249455
  · exact B249459
  · exact B249463
  · exact B249467
  · exact B249471
  · exact B249475
  · exact B249479
  · exact B249483
  · exact B249487
  · exact B249491
  · exact B249495
  · exact B249499
  · exact B249503
  · exact B249507
  · exact B249511
  · exact B249515
  · exact B249519
  · exact B249523
  · exact B249527
  · exact B249531
  · exact B249535
  · exact B249539
  · exact B249543
  · exact B249547
  · exact B249551
  · exact B249555
  · exact B249559
  · exact B249563
  · exact B249567
  · exact B249571
  · exact B249575
  · exact B249579
  · exact B249583
  · exact B249587
  · exact B249591
  · exact B249595
  · exact B249599
  · exact B249603
  · exact B249607
  · exact B249611
  · exact B249615
  · exact B249619
  · exact B249623
  · exact B249627
  · exact B249631
  · exact B249635
  · exact B249639
  · exact B249643
  · exact B249647
  · exact B249651
  · exact B249655
  · exact B249659
  · exact B249663
  · exact B249667
  · exact B249671
  · exact B249675
  · exact B249679
  · exact B249683
  · exact B249687
  · exact B249691
  · exact B249695
  · exact B249699
  · exact B249703
  · exact B249707
  · exact B249711
  · exact B249715
  · exact B249719
  · exact B249723
  · exact B249727
  · exact B249731
  · exact B249735
  · exact B249739
  · exact B249743
  · exact B249747
  · exact B249751
  · exact B249755
  · exact B249759
  · exact B249763
  · exact B249767
  · exact B249771
  · exact B249775
  · exact B249779
  · exact B249783
  · exact B249787
  · exact B249791
  · exact B249795
  · exact B249799
  · exact B249803
  · exact B249807
  · exact B249811
  · exact B249815
  · exact B249819
  · exact B249823
  · exact B249827
  · exact B249831
  · exact B249835
  · exact B249839
  · exact B249843
  · exact B249847
  · exact B249851
  · exact B249855
  · exact B249859
  · exact B249863
  · exact B249867
  · exact B249871
  · exact B249875
  · exact B249879
  · exact B249883
  · exact B249887
  · exact B249891
  · exact B249895
  · exact B249899
  · exact B249903
  · exact B249907
  · exact B249911
  · exact B249915
  · exact B249919
  · exact B249923
  · exact B249927
  · exact B249931
  · exact B249935
  · exact B249939
  · exact B249943
  · exact B249947
  · exact B249951
  · exact B249955
  · exact B249959
  · exact B249963
  · exact B249967
  · exact B249971
  · exact B249975
  · exact B249979
  · exact B249983
  · exact B249987
  · exact B249991
  · exact B249995
  · exact B249999
  · exact B250003
  · exact B250007
  · exact B250011
  · exact B250015
  · exact B250019
  · exact B250023
  · exact B250027
  · exact B250031
  · exact B250035
  · exact B250039
  · exact B250043
  · exact B250047
  · exact B250051
  · exact B250055
  · exact B250059
  · exact B250063
  · exact B250067
  · exact B250071
  · exact B250075
  · exact B250079
  · exact B250083
  · exact B250087
  · exact B250091
  · exact B250095
  · exact B250099
  · exact B250103
  · exact B250107
  · exact B250111
  · exact B250115
  · exact B250119
  · exact B250123
  · exact B250127
  · exact B250131
  · exact B250135
  · exact B250139
  · exact B250143
  · exact B250147
  · exact B250151
  · exact B250155
  · exact B250159
  · exact B250163
  · exact B250167
  · exact B250171
  · exact B250175
  · exact B250179
  · exact B250183
  · exact B250187
  · exact B250191
  · exact B250195
  · exact B250199
  · exact B250203
  · exact B250207
  · exact B250211
  · exact B250215
  · exact B250219
  · exact B250223
  · exact B250227
  · exact B250231
  · exact B250235
  · exact B250239
  · exact B250243
  · exact B250247
  · exact B250251
  · exact B250255
  · exact B250259
  · exact B250263
  · exact B250267
  · exact B250271
  · exact B250275
  · exact B250279
  · exact B250283
  · exact B250287
  · exact B250291
  · exact B250295
  · exact B250299
  · exact B250303
  · exact B250307
  · exact B250311
  · exact B250315
  · exact B250319
  · exact B250323
  · exact B250327
  · exact B250331
  · exact B250335
  · exact B250339
  · exact B250343
  · exact B250347
  · exact B250351
  · exact B250355
  · exact B250359
  · exact B250363
  · exact B250367
  · exact B250371
  · exact B250375
  · exact B250379
  · exact B250383
  · exact B250387
  · exact B250391
  · exact B250395
  · exact B250399
  · exact B250403
  · exact B250407
  · exact B250411
  · exact B250415
  · exact B250419
  · exact B250423
  · exact B250427
  · exact B250431
  · exact B250435
  · exact B250439
  · exact B250443
  · exact B250447
  · exact B250451
  · exact B250455
  · exact B250459
  · exact B250463
  · exact B250467
  · exact B250471
  · exact B250475
  · exact B250479
  · exact B250483
  · exact B250487
  · exact B250491
  · exact B250495
  · exact B250499
  · exact B250503
  · exact B250507
  · exact B250511
  · exact B250515
  · exact B250519
  · exact B250523
  · exact B250527
  · exact B250531
  · exact B250535
  · exact B250539
  · exact B250543
  · exact B250547
  · exact B250551
  · exact B250555
  · exact B250559
  · exact B250563
  · exact B250567
  · exact B250571
  · exact B250575
  · exact B250579
  · exact B250583
  · exact B250587
  · exact B250591
  · exact B250595
  · exact B250599
  · exact B250603
  · exact B250607
  · exact B250611
  · exact B250615

theorem C1 (j : ℕ) (h1 : 62654 ≤ j) (h2 : j ≤ 62953) : Blo 247818 (4 * j + 3) := by
  interval_cases j
  · exact B250619
  · exact B250623
  · exact B250627
  · exact B250631
  · exact B250635
  · exact B250639
  · exact B250643
  · exact B250647
  · exact B250651
  · exact B250655
  · exact B250659
  · exact B250663
  · exact B250667
  · exact B250671
  · exact B250675
  · exact B250679
  · exact B250683
  · exact B250687
  · exact B250691
  · exact B250695
  · exact B250699
  · exact B250703
  · exact B250707
  · exact B250711
  · exact B250715
  · exact B250719
  · exact B250723
  · exact B250727
  · exact B250731
  · exact B250735
  · exact B250739
  · exact B250743
  · exact B250747
  · exact B250751
  · exact B250755
  · exact B250759
  · exact B250763
  · exact B250767
  · exact B250771
  · exact B250775
  · exact B250779
  · exact B250783
  · exact B250787
  · exact B250791
  · exact B250795
  · exact B250799
  · exact B250803
  · exact B250807
  · exact B250811
  · exact B250815
  · exact B250819
  · exact B250823
  · exact B250827
  · exact B250831
  · exact B250835
  · exact B250839
  · exact B250843
  · exact B250847
  · exact B250851
  · exact B250855
  · exact B250859
  · exact B250863
  · exact B250867
  · exact B250871
  · exact B250875
  · exact B250879
  · exact B250883
  · exact B250887
  · exact B250891
  · exact B250895
  · exact B250899
  · exact B250903
  · exact B250907
  · exact B250911
  · exact B250915
  · exact B250919
  · exact B250923
  · exact B250927
  · exact B250931
  · exact B250935
  · exact B250939
  · exact B250943
  · exact B250947
  · exact B250951
  · exact B250955
  · exact B250959
  · exact B250963
  · exact B250967
  · exact B250971
  · exact B250975
  · exact B250979
  · exact B250983
  · exact B250987
  · exact B250991
  · exact B250995
  · exact B250999
  · exact B251003
  · exact B251007
  · exact B251011
  · exact B251015
  · exact B251019
  · exact B251023
  · exact B251027
  · exact B251031
  · exact B251035
  · exact B251039
  · exact B251043
  · exact B251047
  · exact B251051
  · exact B251055
  · exact B251059
  · exact B251063
  · exact B251067
  · exact B251071
  · exact B251075
  · exact B251079
  · exact B251083
  · exact B251087
  · exact B251091
  · exact B251095
  · exact B251099
  · exact B251103
  · exact B251107
  · exact B251111
  · exact B251115
  · exact B251119
  · exact B251123
  · exact B251127
  · exact B251131
  · exact B251135
  · exact B251139
  · exact B251143
  · exact B251147
  · exact B251151
  · exact B251155
  · exact B251159
  · exact B251163
  · exact B251167
  · exact B251171
  · exact B251175
  · exact B251179
  · exact B251183
  · exact B251187
  · exact B251191
  · exact B251195
  · exact B251199
  · exact B251203
  · exact B251207
  · exact B251211
  · exact B251215
  · exact B251219
  · exact B251223
  · exact B251227
  · exact B251231
  · exact B251235
  · exact B251239
  · exact B251243
  · exact B251247
  · exact B251251
  · exact B251255
  · exact B251259
  · exact B251263
  · exact B251267
  · exact B251271
  · exact B251275
  · exact B251279
  · exact B251283
  · exact B251287
  · exact B251291
  · exact B251295
  · exact B251299
  · exact B251303
  · exact B251307
  · exact B251311
  · exact B251315
  · exact B251319
  · exact B251323
  · exact B251327
  · exact B251331
  · exact B251335
  · exact B251339
  · exact B251343
  · exact B251347
  · exact B251351
  · exact B251355
  · exact B251359
  · exact B251363
  · exact B251367
  · exact B251371
  · exact B251375
  · exact B251379
  · exact B251383
  · exact B251387
  · exact B251391
  · exact B251395
  · exact B251399
  · exact B251403
  · exact B251407
  · exact B251411
  · exact B251415
  · exact B251419
  · exact B251423
  · exact B251427
  · exact B251431
  · exact B251435
  · exact B251439
  · exact B251443
  · exact B251447
  · exact B251451
  · exact B251455
  · exact B251459
  · exact B251463
  · exact B251467
  · exact B251471
  · exact B251475
  · exact B251479
  · exact B251483
  · exact B251487
  · exact B251491
  · exact B251495
  · exact B251499
  · exact B251503
  · exact B251507
  · exact B251511
  · exact B251515
  · exact B251519
  · exact B251523
  · exact B251527
  · exact B251531
  · exact B251535
  · exact B251539
  · exact B251543
  · exact B251547
  · exact B251551
  · exact B251555
  · exact B251559
  · exact B251563
  · exact B251567
  · exact B251571
  · exact B251575
  · exact B251579
  · exact B251583
  · exact B251587
  · exact B251591
  · exact B251595
  · exact B251599
  · exact B251603
  · exact B251607
  · exact B251611
  · exact B251615
  · exact B251619
  · exact B251623
  · exact B251627
  · exact B251631
  · exact B251635
  · exact B251639
  · exact B251643
  · exact B251647
  · exact B251651
  · exact B251655
  · exact B251659
  · exact B251663
  · exact B251667
  · exact B251671
  · exact B251675
  · exact B251679
  · exact B251683
  · exact B251687
  · exact B251691
  · exact B251695
  · exact B251699
  · exact B251703
  · exact B251707
  · exact B251711
  · exact B251715
  · exact B251719
  · exact B251723
  · exact B251727
  · exact B251731
  · exact B251735
  · exact B251739
  · exact B251743
  · exact B251747
  · exact B251751
  · exact B251755
  · exact B251759
  · exact B251763
  · exact B251767
  · exact B251771
  · exact B251775
  · exact B251779
  · exact B251783
  · exact B251787
  · exact B251791
  · exact B251795
  · exact B251799
  · exact B251803
  · exact B251807
  · exact B251811
  · exact B251815

theorem solution (m : ℕ) (hlo : 247818 ≤ m) (hhi : m ≤ 251818) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 61954 ≤ j := by omega
    have hj2 : j ≤ 62953 := by omega
    have hb : Blo 247818 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 62654 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
