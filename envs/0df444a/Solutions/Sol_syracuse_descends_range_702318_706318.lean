-- Prove2me | solution 1 for syracuse_descends_range_702318_706318
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:59.767891+00:00
-- url     : https://prove2.me/submissions/d1a2823c-6698-4e50-8dd5-b7e57fbab95a

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


theorem B1507493 : Blo 702318 1507493 := bbase (se 4 (by rfl) ⟨141327, by rfl⟩ : syracuseStep 1507493 = 282655) (by norm_num)
theorem B3801269 : Blo 702318 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B22839509 : Blo 702318 22839509 := bbase (se 7 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 22839509 = 535301) (by norm_num)
theorem B2261317 : Blo 702318 2261317 := bbase (se 4 (by rfl) ⟨211998, by rfl⟩ : syracuseStep 2261317 = 423997) (by norm_num)
theorem B1901045 : Blo 702318 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B3572261 : Blo 702318 3572261 := bbase (se 4 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 3572261 = 669799) (by norm_num)
theorem B950869 : Blo 702318 950869 := bbase (se 8 (by rfl) ⟨5571, by rfl⟩ : syracuseStep 950869 = 11143) (by norm_num)
theorem B6095477 : Blo 702318 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B1507997 : Blo 702318 1507997 := bbase (se 3 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 1507997 = 565499) (by norm_num)
theorem B1508005 : Blo 702318 1508005 := bbase (se 4 (by rfl) ⟨141375, by rfl⟩ : syracuseStep 1508005 = 282751) (by norm_num)
theorem B1737509 : Blo 702318 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B4522837 : Blo 702318 4522837 := bbase (se 9 (by rfl) ⟨13250, by rfl⟩ : syracuseStep 4522837 = 26501) (by norm_num)
theorem B951301 : Blo 702318 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B8029205 : Blo 702318 8029205 := bbase (se 6 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 8029205 = 376369) (by norm_num)
theorem B6947893 : Blo 702318 6947893 := bbase (se 5 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 6947893 = 651365) (by norm_num)
theorem B951517 : Blo 702318 951517 := bbase (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) (by norm_num)
theorem B1901909 : Blo 702318 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B951733 : Blo 702318 951733 := bbase (se 5 (by rfl) ⟨44612, by rfl⟩ : syracuseStep 951733 = 89225) (by norm_num)
theorem B1607357 : Blo 702318 1607357 := bbase (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) (by norm_num)
theorem B3573557 : Blo 702318 3573557 := bbase (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) (by norm_num)
theorem B2000821 : Blo 702318 2000821 := bbase (se 5 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 2000821 = 187577) (by norm_num)
theorem B3213269 : Blo 702318 3213269 := bbase (se 7 (by rfl) ⟨37655, by rfl⟩ : syracuseStep 3213269 = 75311) (by norm_num)
theorem B3016693 : Blo 702318 3016693 := bbase (se 5 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 3016693 = 282815) (by norm_num)
theorem B3377173 : Blo 702318 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B9635861 : Blo 702318 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B2852981 : Blo 702318 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B2034229 : Blo 702318 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2886533 : Blo 702318 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B4000661 : Blo 702318 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B723901 : Blo 702318 723901 := bbase (se 3 (by rfl) ⟨135731, by rfl⟩ : syracuseStep 723901 = 271463) (by norm_num)
theorem B2001925 : Blo 702318 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B3574853 : Blo 702318 3574853 := bbase (se 4 (by rfl) ⟨335142, by rfl⟩ : syracuseStep 3574853 = 670285) (by norm_num)
theorem B1019309 : Blo 702318 1019309 := bbase (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) (by norm_num)
theorem B790141 : Blo 702318 790141 := bbase (se 3 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 790141 = 296303) (by norm_num)
theorem B790177 : Blo 702318 790177 := bbase (se 2 (by rfl) ⟨296316, by rfl⟩ : syracuseStep 790177 = 592633) (by norm_num)
theorem B790213 : Blo 702318 790213 := bbase (se 4 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 790213 = 148165) (by norm_num)
theorem B790249 : Blo 702318 790249 := bbase (se 2 (by rfl) ⟨296343, by rfl⟩ : syracuseStep 790249 = 592687) (by norm_num)
theorem B790285 : Blo 702318 790285 := bbase (se 3 (by rfl) ⟨148178, by rfl⟩ : syracuseStep 790285 = 296357) (by norm_num)
theorem B790321 : Blo 702318 790321 := bbase (se 2 (by rfl) ⟨296370, by rfl⟩ : syracuseStep 790321 = 592741) (by norm_num)
theorem B1806149 : Blo 702318 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B790357 : Blo 702318 790357 := bbase (se 9 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 790357 = 4631) (by norm_num)
theorem B1740629 : Blo 702318 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B790393 : Blo 702318 790393 := bbase (se 2 (by rfl) ⟨296397, by rfl⟩ : syracuseStep 790393 = 592795) (by norm_num)
theorem B790429 : Blo 702318 790429 := bbase (se 3 (by rfl) ⟨148205, by rfl⟩ : syracuseStep 790429 = 296411) (by norm_num)
theorem B790465 : Blo 702318 790465 := bbase (se 2 (by rfl) ⟨296424, by rfl⟩ : syracuseStep 790465 = 592849) (by norm_num)
theorem B1904581 : Blo 702318 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B790501 : Blo 702318 790501 := bbase (se 4 (by rfl) ⟨74109, by rfl⟩ : syracuseStep 790501 = 148219) (by norm_num)
theorem B790537 : Blo 702318 790537 := bbase (se 2 (by rfl) ⟨296451, by rfl⟩ : syracuseStep 790537 = 592903) (by norm_num)
theorem B790573 : Blo 702318 790573 := bbase (se 3 (by rfl) ⟨148232, by rfl⟩ : syracuseStep 790573 = 296465) (by norm_num)
theorem B4001845 : Blo 702318 4001845 := bbase (se 5 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 4001845 = 375173) (by norm_num)
theorem B888889 : Blo 702318 888889 := bbase (se 2 (by rfl) ⟨333333, by rfl⟩ : syracuseStep 888889 = 666667) (by norm_num)
theorem B790609 : Blo 702318 790609 := bbase (se 2 (by rfl) ⟨296478, by rfl⟩ : syracuseStep 790609 = 592957) (by norm_num)
theorem B790645 : Blo 702318 790645 := bbase (se 5 (by rfl) ⟨37061, by rfl⟩ : syracuseStep 790645 = 74123) (by norm_num)
theorem B888985 : Blo 702318 888985 := bbase (se 2 (by rfl) ⟨333369, by rfl⟩ : syracuseStep 888985 = 666739) (by norm_num)
theorem B790681 : Blo 702318 790681 := bbase (se 2 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 790681 = 593011) (by norm_num)
theorem B6787253 : Blo 702318 6787253 := bbase (se 5 (by rfl) ⟨318152, by rfl⟩ : syracuseStep 6787253 = 636305) (by norm_num)
theorem B790717 : Blo 702318 790717 := bbase (se 3 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 790717 = 296519) (by norm_num)
theorem B790753 : Blo 702318 790753 := bbase (se 2 (by rfl) ⟨296532, by rfl⟩ : syracuseStep 790753 = 593065) (by norm_num)
theorem B790789 : Blo 702318 790789 := bbase (se 4 (by rfl) ⟨74136, by rfl⟩ : syracuseStep 790789 = 148273) (by norm_num)
theorem B790825 : Blo 702318 790825 := bbase (se 2 (by rfl) ⟨296559, by rfl⟩ : syracuseStep 790825 = 593119) (by norm_num)
theorem B889157 : Blo 702318 889157 := bbase (se 4 (by rfl) ⟨83358, by rfl⟩ : syracuseStep 889157 = 166717) (by norm_num)
theorem B790861 : Blo 702318 790861 := bbase (se 3 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 790861 = 296573) (by norm_num)
theorem B790897 : Blo 702318 790897 := bbase (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) (by norm_num)
theorem B889213 : Blo 702318 889213 := bbase (se 3 (by rfl) ⟨166727, by rfl⟩ : syracuseStep 889213 = 333455) (by norm_num)
theorem B790933 : Blo 702318 790933 := bbase (se 6 (by rfl) ⟨18537, by rfl⟩ : syracuseStep 790933 = 37075) (by norm_num)
theorem B790969 : Blo 702318 790969 := bbase (se 2 (by rfl) ⟨296613, by rfl⟩ : syracuseStep 790969 = 593227) (by norm_num)
theorem B889309 : Blo 702318 889309 := bbase (se 3 (by rfl) ⟨166745, by rfl⟩ : syracuseStep 889309 = 333491) (by norm_num)
theorem B791005 : Blo 702318 791005 := bbase (se 3 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 791005 = 296627) (by norm_num)
theorem B2003429 : Blo 702318 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B791041 : Blo 702318 791041 := bbase (se 2 (by rfl) ⟨296640, by rfl⟩ : syracuseStep 791041 = 593281) (by norm_num)
theorem B791077 : Blo 702318 791077 := bbase (se 4 (by rfl) ⟨74163, by rfl⟩ : syracuseStep 791077 = 148327) (by norm_num)
theorem B791113 : Blo 702318 791113 := bbase (se 2 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 791113 = 593335) (by norm_num)
theorem B791149 : Blo 702318 791149 := bbase (se 3 (by rfl) ⟨148340, by rfl⟩ : syracuseStep 791149 = 296681) (by norm_num)
theorem B889481 : Blo 702318 889481 := bbase (se 2 (by rfl) ⟨333555, by rfl⟩ : syracuseStep 889481 = 667111) (by norm_num)
theorem B791185 : Blo 702318 791185 := bbase (se 2 (by rfl) ⟨296694, by rfl⟩ : syracuseStep 791185 = 593389) (by norm_num)
theorem B791221 : Blo 702318 791221 := bbase (se 5 (by rfl) ⟨37088, by rfl⟩ : syracuseStep 791221 = 74177) (by norm_num)
theorem B889537 : Blo 702318 889537 := bbase (se 2 (by rfl) ⟨333576, by rfl⟩ : syracuseStep 889537 = 667153) (by norm_num)
theorem B2888405 : Blo 702318 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B791257 : Blo 702318 791257 := bbase (se 2 (by rfl) ⟨296721, by rfl⟩ : syracuseStep 791257 = 593443) (by norm_num)
theorem B791293 : Blo 702318 791293 := bbase (se 3 (by rfl) ⟨148367, by rfl⟩ : syracuseStep 791293 = 296735) (by norm_num)
theorem B889633 : Blo 702318 889633 := bbase (se 2 (by rfl) ⟨333612, by rfl⟩ : syracuseStep 889633 = 667225) (by norm_num)
theorem B791329 : Blo 702318 791329 := bbase (se 2 (by rfl) ⟨296748, by rfl⟩ : syracuseStep 791329 = 593497) (by norm_num)
theorem B1053485 : Blo 702318 1053485 := bbase (se 3 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 1053485 = 395057) (by norm_num)
theorem B1053509 : Blo 702318 1053509 := bbase (se 4 (by rfl) ⟨98766, by rfl⟩ : syracuseStep 1053509 = 197533) (by norm_num)
theorem B791365 : Blo 702318 791365 := bbase (se 4 (by rfl) ⟨74190, by rfl⟩ : syracuseStep 791365 = 148381) (by norm_num)
theorem B1053533 : Blo 702318 1053533 := bbase (se 3 (by rfl) ⟨197537, by rfl⟩ : syracuseStep 1053533 = 395075) (by norm_num)
theorem B791401 : Blo 702318 791401 := bbase (se 2 (by rfl) ⟨296775, by rfl⟩ : syracuseStep 791401 = 593551) (by norm_num)
theorem B1053557 : Blo 702318 1053557 := bbase (se 5 (by rfl) ⟨49385, by rfl⟩ : syracuseStep 1053557 = 98771) (by norm_num)
theorem B1807237 : Blo 702318 1807237 := bbase (se 4 (by rfl) ⟨169428, by rfl⟩ : syracuseStep 1807237 = 338857) (by norm_num)
theorem B1053581 : Blo 702318 1053581 := bbase (se 3 (by rfl) ⟨197546, by rfl⟩ : syracuseStep 1053581 = 395093) (by norm_num)
theorem B791437 : Blo 702318 791437 := bbase (se 3 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 791437 = 296789) (by norm_num)
theorem B1053605 : Blo 702318 1053605 := bbase (se 4 (by rfl) ⟨98775, by rfl⟩ : syracuseStep 1053605 = 197551) (by norm_num)
theorem B791473 : Blo 702318 791473 := bbase (se 2 (by rfl) ⟨296802, by rfl⟩ : syracuseStep 791473 = 593605) (by norm_num)
theorem B1053629 : Blo 702318 1053629 := bbase (se 3 (by rfl) ⟨197555, by rfl⟩ : syracuseStep 1053629 = 395111) (by norm_num)
theorem B889805 : Blo 702318 889805 := bbase (se 3 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 889805 = 333677) (by norm_num)
theorem B1053653 : Blo 702318 1053653 := bbase (se 7 (by rfl) ⟨12347, by rfl⟩ : syracuseStep 1053653 = 24695) (by norm_num)
theorem B791509 : Blo 702318 791509 := bbase (se 7 (by rfl) ⟨9275, by rfl⟩ : syracuseStep 791509 = 18551) (by norm_num)
theorem B1053677 : Blo 702318 1053677 := bbase (se 3 (by rfl) ⟨197564, by rfl⟩ : syracuseStep 1053677 = 395129) (by norm_num)
theorem B791545 : Blo 702318 791545 := bbase (se 2 (by rfl) ⟨296829, by rfl⟩ : syracuseStep 791545 = 593659) (by norm_num)
theorem B1053701 : Blo 702318 1053701 := bbase (se 4 (by rfl) ⟨98784, by rfl⟩ : syracuseStep 1053701 = 197569) (by norm_num)
theorem B889861 : Blo 702318 889861 := bbase (se 4 (by rfl) ⟨83424, by rfl⟩ : syracuseStep 889861 = 166849) (by norm_num)
theorem B1053725 : Blo 702318 1053725 := bbase (se 3 (by rfl) ⟨197573, by rfl⟩ : syracuseStep 1053725 = 395147) (by norm_num)
theorem B791581 : Blo 702318 791581 := bbase (se 3 (by rfl) ⟨148421, by rfl⟩ : syracuseStep 791581 = 296843) (by norm_num)
theorem B1053749 : Blo 702318 1053749 := bbase (se 5 (by rfl) ⟨49394, by rfl⟩ : syracuseStep 1053749 = 98789) (by norm_num)
theorem B1610813 : Blo 702318 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B791617 : Blo 702318 791617 := bbase (se 2 (by rfl) ⟨296856, by rfl⟩ : syracuseStep 791617 = 593713) (by norm_num)
theorem B1053773 : Blo 702318 1053773 := bbase (se 3 (by rfl) ⟨197582, by rfl⟩ : syracuseStep 1053773 = 395165) (by norm_num)
theorem B1053797 : Blo 702318 1053797 := bbase (se 4 (by rfl) ⟨98793, by rfl⟩ : syracuseStep 1053797 = 197587) (by norm_num)
theorem B889957 : Blo 702318 889957 := bbase (se 4 (by rfl) ⟨83433, by rfl⟩ : syracuseStep 889957 = 166867) (by norm_num)
theorem B791653 : Blo 702318 791653 := bbase (se 4 (by rfl) ⟨74217, by rfl⟩ : syracuseStep 791653 = 148435) (by norm_num)
theorem B1053821 : Blo 702318 1053821 := bbase (se 3 (by rfl) ⟨197591, by rfl⟩ : syracuseStep 1053821 = 395183) (by norm_num)
theorem B791689 : Blo 702318 791689 := bbase (se 2 (by rfl) ⟨296883, by rfl⟩ : syracuseStep 791689 = 593767) (by norm_num)
theorem B1053845 : Blo 702318 1053845 := bbase (se 6 (by rfl) ⟨24699, by rfl⟩ : syracuseStep 1053845 = 49399) (by norm_num)
theorem B1053869 : Blo 702318 1053869 := bbase (se 3 (by rfl) ⟨197600, by rfl⟩ : syracuseStep 1053869 = 395201) (by norm_num)
theorem B791725 : Blo 702318 791725 := bbase (se 3 (by rfl) ⟨148448, by rfl⟩ : syracuseStep 791725 = 296897) (by norm_num)
theorem B5346485 : Blo 702318 5346485 := bbase (se 5 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 5346485 = 501233) (by norm_num)
theorem B1053893 : Blo 702318 1053893 := bbase (se 4 (by rfl) ⟨98802, by rfl⟩ : syracuseStep 1053893 = 197605) (by norm_num)
theorem B791761 : Blo 702318 791761 := bbase (se 2 (by rfl) ⟨296910, by rfl⟩ : syracuseStep 791761 = 593821) (by norm_num)
theorem B1053917 : Blo 702318 1053917 := bbase (se 3 (by rfl) ⟨197609, by rfl⟩ : syracuseStep 1053917 = 395219) (by norm_num)
theorem B1053941 : Blo 702318 1053941 := bbase (se 5 (by rfl) ⟨49403, by rfl⟩ : syracuseStep 1053941 = 98807) (by norm_num)
theorem B791797 : Blo 702318 791797 := bbase (se 5 (by rfl) ⟨37115, by rfl⟩ : syracuseStep 791797 = 74231) (by norm_num)
theorem B1053965 : Blo 702318 1053965 := bbase (se 3 (by rfl) ⟨197618, by rfl⟩ : syracuseStep 1053965 = 395237) (by norm_num)
theorem B890129 : Blo 702318 890129 := bbase (se 2 (by rfl) ⟨333798, by rfl⟩ : syracuseStep 890129 = 667597) (by norm_num)
theorem B791833 : Blo 702318 791833 := bbase (se 2 (by rfl) ⟨296937, by rfl⟩ : syracuseStep 791833 = 593875) (by norm_num)
theorem B1053989 : Blo 702318 1053989 := bbase (se 4 (by rfl) ⟨98811, by rfl⟩ : syracuseStep 1053989 = 197623) (by norm_num)
theorem B1054013 : Blo 702318 1054013 := bbase (se 3 (by rfl) ⟨197627, by rfl⟩ : syracuseStep 1054013 = 395255) (by norm_num)
theorem B791869 : Blo 702318 791869 := bbase (se 3 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 791869 = 296951) (by norm_num)
theorem B890185 : Blo 702318 890185 := bbase (se 2 (by rfl) ⟨333819, by rfl⟩ : syracuseStep 890185 = 667639) (by norm_num)
theorem B1054037 : Blo 702318 1054037 := bbase (se 14 (by rfl) ⟨96, by rfl⟩ : syracuseStep 1054037 = 193) (by norm_num)
theorem B791905 : Blo 702318 791905 := bbase (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) (by norm_num)
theorem B1054061 : Blo 702318 1054061 := bbase (se 3 (by rfl) ⟨197636, by rfl⟩ : syracuseStep 1054061 = 395273) (by norm_num)
theorem B1054085 : Blo 702318 1054085 := bbase (se 4 (by rfl) ⟨98820, by rfl⟩ : syracuseStep 1054085 = 197641) (by norm_num)
theorem B791941 : Blo 702318 791941 := bbase (se 4 (by rfl) ⟨74244, by rfl⟩ : syracuseStep 791941 = 148489) (by norm_num)
theorem B1054109 : Blo 702318 1054109 := bbase (se 3 (by rfl) ⟨197645, by rfl⟩ : syracuseStep 1054109 = 395291) (by norm_num)
theorem B890281 : Blo 702318 890281 := bbase (se 2 (by rfl) ⟨333855, by rfl⟩ : syracuseStep 890281 = 667711) (by norm_num)
theorem B791977 : Blo 702318 791977 := bbase (se 2 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 791977 = 593983) (by norm_num)
theorem B1185205 : Blo 702318 1185205 := bbase (se 5 (by rfl) ⟨55556, by rfl⟩ : syracuseStep 1185205 = 111113) (by norm_num)
theorem B1054133 : Blo 702318 1054133 := bbase (se 5 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 1054133 = 98825) (by norm_num)
theorem B1054157 : Blo 702318 1054157 := bbase (se 3 (by rfl) ⟨197654, by rfl⟩ : syracuseStep 1054157 = 395309) (by norm_num)
theorem B792013 : Blo 702318 792013 := bbase (se 3 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 792013 = 297005) (by norm_num)
theorem B1054181 : Blo 702318 1054181 := bbase (se 4 (by rfl) ⟨98829, by rfl⟩ : syracuseStep 1054181 = 197659) (by norm_num)
theorem B792049 : Blo 702318 792049 := bbase (se 2 (by rfl) ⟨297018, by rfl⟩ : syracuseStep 792049 = 594037) (by norm_num)
theorem B1283573 : Blo 702318 1283573 := bbase (se 5 (by rfl) ⟨60167, by rfl⟩ : syracuseStep 1283573 = 120335) (by norm_num)
theorem B1054205 : Blo 702318 1054205 := bbase (se 3 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 1054205 = 395327) (by norm_num)
theorem B1185293 : Blo 702318 1185293 := bbase (se 3 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 1185293 = 444485) (by norm_num)
theorem B1054229 : Blo 702318 1054229 := bbase (se 6 (by rfl) ⟨24708, by rfl⟩ : syracuseStep 1054229 = 49417) (by norm_num)
theorem B792085 : Blo 702318 792085 := bbase (se 6 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 792085 = 37129) (by norm_num)
theorem B2856485 : Blo 702318 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B1054253 : Blo 702318 1054253 := bbase (se 3 (by rfl) ⟨197672, by rfl⟩ : syracuseStep 1054253 = 395345) (by norm_num)
theorem B792121 : Blo 702318 792121 := bbase (se 2 (by rfl) ⟨297045, by rfl⟩ : syracuseStep 792121 = 594091) (by norm_num)
theorem B1054277 : Blo 702318 1054277 := bbase (se 4 (by rfl) ⟨98838, by rfl⟩ : syracuseStep 1054277 = 197677) (by norm_num)
theorem B890453 : Blo 702318 890453 := bbase (se 8 (by rfl) ⟨5217, by rfl⟩ : syracuseStep 890453 = 10435) (by norm_num)
theorem B1054301 : Blo 702318 1054301 := bbase (se 3 (by rfl) ⟨197681, by rfl⟩ : syracuseStep 1054301 = 395363) (by norm_num)
theorem B792157 : Blo 702318 792157 := bbase (se 3 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 792157 = 297059) (by norm_num)
theorem B1054325 : Blo 702318 1054325 := bbase (se 5 (by rfl) ⟨49421, by rfl⟩ : syracuseStep 1054325 = 98843) (by norm_num)
theorem B792193 : Blo 702318 792193 := bbase (se 2 (by rfl) ⟨297072, by rfl⟩ : syracuseStep 792193 = 594145) (by norm_num)
theorem B1185421 : Blo 702318 1185421 := bbase (se 3 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 1185421 = 444533) (by norm_num)
theorem B1054349 : Blo 702318 1054349 := bbase (se 3 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 1054349 = 395381) (by norm_num)
theorem B890509 : Blo 702318 890509 := bbase (se 3 (by rfl) ⟨166970, by rfl⟩ : syracuseStep 890509 = 333941) (by norm_num)
theorem B7214741 : Blo 702318 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B1054373 : Blo 702318 1054373 := bbase (se 4 (by rfl) ⟨98847, by rfl⟩ : syracuseStep 1054373 = 197695) (by norm_num)
theorem B792229 : Blo 702318 792229 := bbase (se 4 (by rfl) ⟨74271, by rfl⟩ : syracuseStep 792229 = 148543) (by norm_num)
theorem B1054397 : Blo 702318 1054397 := bbase (se 3 (by rfl) ⟨197699, by rfl⟩ : syracuseStep 1054397 = 395399) (by norm_num)
theorem B792265 : Blo 702318 792265 := bbase (se 2 (by rfl) ⟨297099, by rfl⟩ : syracuseStep 792265 = 594199) (by norm_num)
theorem B1054421 : Blo 702318 1054421 := bbase (se 7 (by rfl) ⟨12356, by rfl⟩ : syracuseStep 1054421 = 24713) (by norm_num)
theorem B1185509 : Blo 702318 1185509 := bbase (se 4 (by rfl) ⟨111141, by rfl⟩ : syracuseStep 1185509 = 222283) (by norm_num)
theorem B1054445 : Blo 702318 1054445 := bbase (se 3 (by rfl) ⟨197708, by rfl⟩ : syracuseStep 1054445 = 395417) (by norm_num)
theorem B890605 : Blo 702318 890605 := bbase (se 3 (by rfl) ⟨166988, by rfl⟩ : syracuseStep 890605 = 333977) (by norm_num)
theorem B792301 : Blo 702318 792301 := bbase (se 3 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 792301 = 297113) (by norm_num)
theorem B1054469 : Blo 702318 1054469 := bbase (se 4 (by rfl) ⟨98856, by rfl⟩ : syracuseStep 1054469 = 197713) (by norm_num)
theorem B792337 : Blo 702318 792337 := bbase (se 2 (by rfl) ⟨297126, by rfl⟩ : syracuseStep 792337 = 594253) (by norm_num)
theorem B1054493 : Blo 702318 1054493 := bbase (se 3 (by rfl) ⟨197717, by rfl⟩ : syracuseStep 1054493 = 395435) (by norm_num)
theorem B1054517 : Blo 702318 1054517 := bbase (se 5 (by rfl) ⟨49430, by rfl⟩ : syracuseStep 1054517 = 98861) (by norm_num)
theorem B792373 : Blo 702318 792373 := bbase (se 5 (by rfl) ⟨37142, by rfl⟩ : syracuseStep 792373 = 74285) (by norm_num)
theorem B1054541 : Blo 702318 1054541 := bbase (se 3 (by rfl) ⟨197726, by rfl⟩ : syracuseStep 1054541 = 395453) (by norm_num)
theorem B792409 : Blo 702318 792409 := bbase (se 2 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 792409 = 594307) (by norm_num)
theorem B1185637 : Blo 702318 1185637 := bbase (se 4 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 1185637 = 222307) (by norm_num)
theorem B1054565 : Blo 702318 1054565 := bbase (se 4 (by rfl) ⟨98865, by rfl⟩ : syracuseStep 1054565 = 197731) (by norm_num)
theorem B1054589 : Blo 702318 1054589 := bbase (se 3 (by rfl) ⟨197735, by rfl⟩ : syracuseStep 1054589 = 395471) (by norm_num)
theorem B792445 : Blo 702318 792445 := bbase (se 3 (by rfl) ⟨148583, by rfl⟩ : syracuseStep 792445 = 297167) (by norm_num)
theorem B1054613 : Blo 702318 1054613 := bbase (se 6 (by rfl) ⟨24717, by rfl⟩ : syracuseStep 1054613 = 49435) (by norm_num)
theorem B890777 : Blo 702318 890777 := bbase (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) (by norm_num)
theorem B792481 : Blo 702318 792481 := bbase (se 2 (by rfl) ⟨297180, by rfl⟩ : syracuseStep 792481 = 594361) (by norm_num)
theorem B1054637 : Blo 702318 1054637 := bbase (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) (by norm_num)
theorem B1185725 : Blo 702318 1185725 := bbase (se 3 (by rfl) ⟨222323, by rfl⟩ : syracuseStep 1185725 = 444647) (by norm_num)
theorem B1054661 : Blo 702318 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B792517 : Blo 702318 792517 := bbase (se 4 (by rfl) ⟨74298, by rfl⟩ : syracuseStep 792517 = 148597) (by norm_num)
theorem B1087429 : Blo 702318 1087429 := bbase (se 4 (by rfl) ⟨101946, by rfl⟩ : syracuseStep 1087429 = 203893) (by norm_num)
theorem B890833 : Blo 702318 890833 := bbase (se 2 (by rfl) ⟨334062, by rfl⟩ : syracuseStep 890833 = 668125) (by norm_num)
theorem B1054685 : Blo 702318 1054685 := bbase (se 3 (by rfl) ⟨197753, by rfl⟩ : syracuseStep 1054685 = 395507) (by norm_num)
theorem B792553 : Blo 702318 792553 := bbase (se 2 (by rfl) ⟨297207, by rfl⟩ : syracuseStep 792553 = 594415) (by norm_num)
theorem B4003829 : Blo 702318 4003829 := bbase (se 5 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 4003829 = 375359) (by norm_num)
theorem B1054709 : Blo 702318 1054709 := bbase (se 5 (by rfl) ⟨49439, by rfl⟩ : syracuseStep 1054709 = 98879) (by norm_num)
theorem B1054733 : Blo 702318 1054733 := bbase (se 3 (by rfl) ⟨197762, by rfl⟩ : syracuseStep 1054733 = 395525) (by norm_num)
theorem B792589 : Blo 702318 792589 := bbase (se 3 (by rfl) ⟨148610, by rfl⟩ : syracuseStep 792589 = 297221) (by norm_num)
theorem B2005013 : Blo 702318 2005013 := bbase (se 6 (by rfl) ⟨46992, by rfl⟩ : syracuseStep 2005013 = 93985) (by norm_num)
theorem B1054757 : Blo 702318 1054757 := bbase (se 4 (by rfl) ⟨98883, by rfl⟩ : syracuseStep 1054757 = 197767) (by norm_num)
theorem B890929 : Blo 702318 890929 := bbase (se 2 (by rfl) ⟨334098, by rfl⟩ : syracuseStep 890929 = 668197) (by norm_num)
theorem B792625 : Blo 702318 792625 := bbase (se 2 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 792625 = 594469) (by norm_num)
theorem B1185853 : Blo 702318 1185853 := bbase (se 3 (by rfl) ⟨222347, by rfl⟩ : syracuseStep 1185853 = 444695) (by norm_num)
theorem B1054781 : Blo 702318 1054781 := bbase (se 3 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 1054781 = 395543) (by norm_num)
theorem B1054805 : Blo 702318 1054805 := bbase (se 8 (by rfl) ⟨6180, by rfl⟩ : syracuseStep 1054805 = 12361) (by norm_num)
theorem B792661 : Blo 702318 792661 := bbase (se 8 (by rfl) ⟨4644, by rfl⟩ : syracuseStep 792661 = 9289) (by norm_num)
theorem B1054829 : Blo 702318 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B3381365 : Blo 702318 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B792697 : Blo 702318 792697 := bbase (se 2 (by rfl) ⟨297261, by rfl⟩ : syracuseStep 792697 = 594523) (by norm_num)
theorem B1054853 : Blo 702318 1054853 := bbase (se 4 (by rfl) ⟨98892, by rfl⟩ : syracuseStep 1054853 = 197785) (by norm_num)
theorem B1185941 : Blo 702318 1185941 := bbase (se 6 (by rfl) ⟨27795, by rfl⟩ : syracuseStep 1185941 = 55591) (by norm_num)
theorem B1054877 : Blo 702318 1054877 := bbase (se 3 (by rfl) ⟨197789, by rfl⟩ : syracuseStep 1054877 = 395579) (by norm_num)
theorem B792733 : Blo 702318 792733 := bbase (se 3 (by rfl) ⟨148637, by rfl⟩ : syracuseStep 792733 = 297275) (by norm_num)
theorem B1054901 : Blo 702318 1054901 := bbase (se 5 (by rfl) ⟨49448, by rfl⟩ : syracuseStep 1054901 = 98897) (by norm_num)
theorem B792769 : Blo 702318 792769 := bbase (se 2 (by rfl) ⟨297288, by rfl⟩ : syracuseStep 792769 = 594577) (by norm_num)
theorem B1054925 : Blo 702318 1054925 := bbase (se 3 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 1054925 = 395597) (by norm_num)
theorem B891101 : Blo 702318 891101 := bbase (se 3 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 891101 = 334163) (by norm_num)
theorem B1054949 : Blo 702318 1054949 := bbase (se 4 (by rfl) ⟨98901, by rfl⟩ : syracuseStep 1054949 = 197803) (by norm_num)
theorem B792805 : Blo 702318 792805 := bbase (se 4 (by rfl) ⟨74325, by rfl⟩ : syracuseStep 792805 = 148651) (by norm_num)
theorem B1054973 : Blo 702318 1054973 := bbase (se 3 (by rfl) ⟨197807, by rfl⟩ : syracuseStep 1054973 = 395615) (by norm_num)
theorem B792841 : Blo 702318 792841 := bbase (se 2 (by rfl) ⟨297315, by rfl⟩ : syracuseStep 792841 = 594631) (by norm_num)
theorem B1186069 : Blo 702318 1186069 := bbase (se 6 (by rfl) ⟨27798, by rfl⟩ : syracuseStep 1186069 = 55597) (by norm_num)
theorem B1054997 : Blo 702318 1054997 := bbase (se 6 (by rfl) ⟨24726, by rfl⟩ : syracuseStep 1054997 = 49453) (by norm_num)
theorem B891157 : Blo 702318 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B1055021 : Blo 702318 1055021 := bbase (se 3 (by rfl) ⟨197816, by rfl⟩ : syracuseStep 1055021 = 395633) (by norm_num)
theorem B792877 : Blo 702318 792877 := bbase (se 3 (by rfl) ⟨148664, by rfl⟩ : syracuseStep 792877 = 297329) (by norm_num)
theorem B1055045 : Blo 702318 1055045 := bbase (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) (by norm_num)
theorem B792913 : Blo 702318 792913 := bbase (se 2 (by rfl) ⟨297342, by rfl⟩ : syracuseStep 792913 = 594685) (by norm_num)
theorem B1055069 : Blo 702318 1055069 := bbase (se 3 (by rfl) ⟨197825, by rfl⟩ : syracuseStep 1055069 = 395651) (by norm_num)
theorem B1186157 : Blo 702318 1186157 := bbase (se 3 (by rfl) ⟨222404, by rfl⟩ : syracuseStep 1186157 = 444809) (by norm_num)
theorem B1055093 : Blo 702318 1055093 := bbase (se 5 (by rfl) ⟨49457, by rfl⟩ : syracuseStep 1055093 = 98915) (by norm_num)
theorem B891253 : Blo 702318 891253 := bbase (se 5 (by rfl) ⟨41777, by rfl⟩ : syracuseStep 891253 = 83555) (by norm_num)
theorem B792949 : Blo 702318 792949 := bbase (se 5 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 792949 = 74339) (by norm_num)
theorem B1055117 : Blo 702318 1055117 := bbase (se 3 (by rfl) ⟨197834, by rfl⟩ : syracuseStep 1055117 = 395669) (by norm_num)
theorem B5151125 : Blo 702318 5151125 := bbase (se 6 (by rfl) ⟨120729, by rfl⟩ : syracuseStep 5151125 = 241459) (by norm_num)
theorem B792985 : Blo 702318 792985 := bbase (se 2 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 792985 = 594739) (by norm_num)
theorem B1055141 : Blo 702318 1055141 := bbase (se 4 (by rfl) ⟨98919, by rfl⟩ : syracuseStep 1055141 = 197839) (by norm_num)
theorem B1055165 : Blo 702318 1055165 := bbase (se 3 (by rfl) ⟨197843, by rfl⟩ : syracuseStep 1055165 = 395687) (by norm_num)
theorem B793021 : Blo 702318 793021 := bbase (se 3 (by rfl) ⟨148691, by rfl⟩ : syracuseStep 793021 = 297383) (by norm_num)
theorem B1055189 : Blo 702318 1055189 := bbase (se 7 (by rfl) ⟨12365, by rfl⟩ : syracuseStep 1055189 = 24731) (by norm_num)
theorem B793057 : Blo 702318 793057 := bbase (se 2 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 793057 = 594793) (by norm_num)
theorem B1186285 : Blo 702318 1186285 := bbase (se 3 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 1186285 = 444857) (by norm_num)
theorem B1055213 : Blo 702318 1055213 := bbase (se 3 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 1055213 = 395705) (by norm_num)
theorem B1055237 : Blo 702318 1055237 := bbase (se 4 (by rfl) ⟨98928, by rfl⟩ : syracuseStep 1055237 = 197857) (by norm_num)
theorem B793093 : Blo 702318 793093 := bbase (se 4 (by rfl) ⟨74352, by rfl⟩ : syracuseStep 793093 = 148705) (by norm_num)
theorem B1088021 : Blo 702318 1088021 := bbase (se 6 (by rfl) ⟨25500, by rfl⟩ : syracuseStep 1088021 = 51001) (by norm_num)
theorem B1055261 : Blo 702318 1055261 := bbase (se 3 (by rfl) ⟨197861, by rfl⟩ : syracuseStep 1055261 = 395723) (by norm_num)
theorem B891425 : Blo 702318 891425 := bbase (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) (by norm_num)
theorem B793129 : Blo 702318 793129 := bbase (se 2 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 793129 = 594847) (by norm_num)
theorem B1055285 : Blo 702318 1055285 := bbase (se 5 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 1055285 = 98933) (by norm_num)
theorem B1186373 : Blo 702318 1186373 := bbase (se 4 (by rfl) ⟨111222, by rfl⟩ : syracuseStep 1186373 = 222445) (by norm_num)
theorem B1055309 : Blo 702318 1055309 := bbase (se 3 (by rfl) ⟨197870, by rfl⟩ : syracuseStep 1055309 = 395741) (by norm_num)
theorem B793165 : Blo 702318 793165 := bbase (se 3 (by rfl) ⟨148718, by rfl⟩ : syracuseStep 793165 = 297437) (by norm_num)
theorem B891481 : Blo 702318 891481 := bbase (se 2 (by rfl) ⟨334305, by rfl⟩ : syracuseStep 891481 = 668611) (by norm_num)
theorem B1055333 : Blo 702318 1055333 := bbase (se 4 (by rfl) ⟨98937, by rfl⟩ : syracuseStep 1055333 = 197875) (by norm_num)
theorem B793201 : Blo 702318 793201 := bbase (se 2 (by rfl) ⟨297450, by rfl⟩ : syracuseStep 793201 = 594901) (by norm_num)
theorem B1055357 : Blo 702318 1055357 := bbase (se 3 (by rfl) ⟨197879, by rfl⟩ : syracuseStep 1055357 = 395759) (by norm_num)
theorem B1055381 : Blo 702318 1055381 := bbase (se 6 (by rfl) ⟨24735, by rfl⟩ : syracuseStep 1055381 = 49471) (by norm_num)
theorem B793237 : Blo 702318 793237 := bbase (se 6 (by rfl) ⟨18591, by rfl⟩ : syracuseStep 793237 = 37183) (by norm_num)
theorem B989869 : Blo 702318 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B1055405 : Blo 702318 1055405 := bbase (se 3 (by rfl) ⟨197888, by rfl⟩ : syracuseStep 1055405 = 395777) (by norm_num)
theorem B2005685 : Blo 702318 2005685 := bbase (se 5 (by rfl) ⟨94016, by rfl⟩ : syracuseStep 2005685 = 188033) (by norm_num)
theorem B1907381 : Blo 702318 1907381 := bbase (se 5 (by rfl) ⟨89408, by rfl⟩ : syracuseStep 1907381 = 178817) (by norm_num)
theorem B793273 : Blo 702318 793273 := bbase (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) (by norm_num)
theorem B891577 : Blo 702318 891577 := bbase (se 2 (by rfl) ⟨334341, by rfl⟩ : syracuseStep 891577 = 668683) (by norm_num)
theorem B1186501 : Blo 702318 1186501 := bbase (se 4 (by rfl) ⟨111234, by rfl⟩ : syracuseStep 1186501 = 222469) (by norm_num)
theorem B1055429 : Blo 702318 1055429 := bbase (se 4 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 1055429 = 197893) (by norm_num)
theorem B1055453 : Blo 702318 1055453 := bbase (se 3 (by rfl) ⟨197897, by rfl⟩ : syracuseStep 1055453 = 395795) (by norm_num)
theorem B793309 : Blo 702318 793309 := bbase (se 3 (by rfl) ⟨148745, by rfl⟩ : syracuseStep 793309 = 297491) (by norm_num)
theorem B4692725 : Blo 702318 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B1055477 : Blo 702318 1055477 := bbase (se 5 (by rfl) ⟨49475, by rfl⟩ : syracuseStep 1055477 = 98951) (by norm_num)
theorem B793345 : Blo 702318 793345 := bbase (se 2 (by rfl) ⟨297504, by rfl⟩ : syracuseStep 793345 = 595009) (by norm_num)
theorem B1055501 : Blo 702318 1055501 := bbase (se 3 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 1055501 = 395813) (by norm_num)
theorem B1186589 : Blo 702318 1186589 := bbase (se 3 (by rfl) ⟨222485, by rfl⟩ : syracuseStep 1186589 = 444971) (by norm_num)
theorem B1055525 : Blo 702318 1055525 := bbase (se 4 (by rfl) ⟨98955, by rfl⟩ : syracuseStep 1055525 = 197911) (by norm_num)
theorem B793381 : Blo 702318 793381 := bbase (se 4 (by rfl) ⟨74379, by rfl⟩ : syracuseStep 793381 = 148759) (by norm_num)
theorem B1055549 : Blo 702318 1055549 := bbase (se 3 (by rfl) ⟨197915, by rfl⟩ : syracuseStep 1055549 = 395831) (by norm_num)
theorem B793417 : Blo 702318 793417 := bbase (se 2 (by rfl) ⟨297531, by rfl⟩ : syracuseStep 793417 = 595063) (by norm_num)
theorem B1055573 : Blo 702318 1055573 := bbase (se 9 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 1055573 = 6185) (by norm_num)
theorem B891749 : Blo 702318 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B1055597 : Blo 702318 1055597 := bbase (se 3 (by rfl) ⟨197924, by rfl⟩ : syracuseStep 1055597 = 395849) (by norm_num)
theorem B793453 : Blo 702318 793453 := bbase (se 3 (by rfl) ⟨148772, by rfl⟩ : syracuseStep 793453 = 297545) (by norm_num)
theorem B1055621 : Blo 702318 1055621 := bbase (se 4 (by rfl) ⟨98964, by rfl⟩ : syracuseStep 1055621 = 197929) (by norm_num)
theorem B793489 : Blo 702318 793489 := bbase (se 2 (by rfl) ⟨297558, by rfl⟩ : syracuseStep 793489 = 595117) (by norm_num)
theorem B1186717 : Blo 702318 1186717 := bbase (se 3 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 1186717 = 445019) (by norm_num)
theorem B1055645 : Blo 702318 1055645 := bbase (se 3 (by rfl) ⟨197933, by rfl⟩ : syracuseStep 1055645 = 395867) (by norm_num)
theorem B891805 : Blo 702318 891805 := bbase (se 3 (by rfl) ⟨167213, by rfl⟩ : syracuseStep 891805 = 334427) (by norm_num)
theorem B1055669 : Blo 702318 1055669 := bbase (se 5 (by rfl) ⟨49484, by rfl⟩ : syracuseStep 1055669 = 98969) (by norm_num)
theorem B793525 : Blo 702318 793525 := bbase (se 5 (by rfl) ⟨37196, by rfl⟩ : syracuseStep 793525 = 74393) (by norm_num)
theorem B1055693 : Blo 702318 1055693 := bbase (se 3 (by rfl) ⟨197942, by rfl⟩ : syracuseStep 1055693 = 395885) (by norm_num)
theorem B793561 : Blo 702318 793561 := bbase (se 2 (by rfl) ⟨297585, by rfl⟩ : syracuseStep 793561 = 595171) (by norm_num)
theorem B1055717 : Blo 702318 1055717 := bbase (se 4 (by rfl) ⟨98973, by rfl⟩ : syracuseStep 1055717 = 197947) (by norm_num)
theorem B1186805 : Blo 702318 1186805 := bbase (se 5 (by rfl) ⟨55631, by rfl⟩ : syracuseStep 1186805 = 111263) (by norm_num)
theorem B1055741 : Blo 702318 1055741 := bbase (se 3 (by rfl) ⟨197951, by rfl⟩ : syracuseStep 1055741 = 395903) (by norm_num)
theorem B891901 : Blo 702318 891901 := bbase (se 3 (by rfl) ⟨167231, by rfl⟩ : syracuseStep 891901 = 334463) (by norm_num)
theorem B793597 : Blo 702318 793597 := bbase (se 3 (by rfl) ⟨148799, by rfl⟩ : syracuseStep 793597 = 297599) (by norm_num)
theorem B1055765 : Blo 702318 1055765 := bbase (se 6 (by rfl) ⟨24744, by rfl⟩ : syracuseStep 1055765 = 49489) (by norm_num)
theorem B793633 : Blo 702318 793633 := bbase (se 2 (by rfl) ⟨297612, by rfl⟩ : syracuseStep 793633 = 595225) (by norm_num)
theorem B1055789 : Blo 702318 1055789 := bbase (se 3 (by rfl) ⟨197960, by rfl⟩ : syracuseStep 1055789 = 395921) (by norm_num)
theorem B1055813 : Blo 702318 1055813 := bbase (se 4 (by rfl) ⟨98982, by rfl⟩ : syracuseStep 1055813 = 197965) (by norm_num)
theorem B793669 : Blo 702318 793669 := bbase (se 4 (by rfl) ⟨74406, by rfl⟩ : syracuseStep 793669 = 148813) (by norm_num)
theorem B1055837 : Blo 702318 1055837 := bbase (se 3 (by rfl) ⟨197969, by rfl⟩ : syracuseStep 1055837 = 395939) (by norm_num)
theorem B2006117 : Blo 702318 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B793705 : Blo 702318 793705 := bbase (se 2 (by rfl) ⟨297639, by rfl⟩ : syracuseStep 793705 = 595279) (by norm_num)
theorem B1186933 : Blo 702318 1186933 := bbase (se 5 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 1186933 = 111275) (by norm_num)
theorem B1055861 : Blo 702318 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B1055885 : Blo 702318 1055885 := bbase (se 3 (by rfl) ⟨197978, by rfl⟩ : syracuseStep 1055885 = 395957) (by norm_num)
theorem B793741 : Blo 702318 793741 := bbase (se 3 (by rfl) ⟨148826, by rfl⟩ : syracuseStep 793741 = 297653) (by norm_num)
theorem B1055909 : Blo 702318 1055909 := bbase (se 4 (by rfl) ⟨98991, by rfl⟩ : syracuseStep 1055909 = 197983) (by norm_num)
theorem B892073 : Blo 702318 892073 := bbase (se 2 (by rfl) ⟨334527, by rfl⟩ : syracuseStep 892073 = 669055) (by norm_num)
theorem B793777 : Blo 702318 793777 := bbase (se 2 (by rfl) ⟨297666, by rfl⟩ : syracuseStep 793777 = 595333) (by norm_num)
theorem B1055933 : Blo 702318 1055933 := bbase (se 3 (by rfl) ⟨197987, by rfl⟩ : syracuseStep 1055933 = 395975) (by norm_num)
theorem B1580237 : Blo 702318 1580237 := bbase (se 3 (by rfl) ⟨296294, by rfl⟩ : syracuseStep 1580237 = 592589) (by norm_num)
theorem B1187021 : Blo 702318 1187021 := bbase (se 3 (by rfl) ⟨222566, by rfl⟩ : syracuseStep 1187021 = 445133) (by norm_num)
theorem B1055957 : Blo 702318 1055957 := bbase (se 7 (by rfl) ⟨12374, by rfl⟩ : syracuseStep 1055957 = 24749) (by norm_num)
theorem B793813 : Blo 702318 793813 := bbase (se 7 (by rfl) ⟨9302, by rfl⟩ : syracuseStep 793813 = 18605) (by norm_num)
theorem B892129 : Blo 702318 892129 := bbase (se 2 (by rfl) ⟨334548, by rfl⟩ : syracuseStep 892129 = 669097) (by norm_num)
theorem B1055981 : Blo 702318 1055981 := bbase (se 3 (by rfl) ⟨197996, by rfl⟩ : syracuseStep 1055981 = 395993) (by norm_num)
theorem B793849 : Blo 702318 793849 := bbase (se 2 (by rfl) ⟨297693, by rfl⟩ : syracuseStep 793849 = 595387) (by norm_num)
theorem B1056005 : Blo 702318 1056005 := bbase (se 4 (by rfl) ⟨99000, by rfl⟩ : syracuseStep 1056005 = 198001) (by norm_num)
theorem B1580309 : Blo 702318 1580309 := bbase (se 6 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 1580309 = 74077) (by norm_num)
theorem B1056029 : Blo 702318 1056029 := bbase (se 3 (by rfl) ⟨198005, by rfl⟩ : syracuseStep 1056029 = 396011) (by norm_num)
theorem B793885 : Blo 702318 793885 := bbase (se 3 (by rfl) ⟨148853, by rfl⟩ : syracuseStep 793885 = 297707) (by norm_num)
theorem B1056053 : Blo 702318 1056053 := bbase (se 5 (by rfl) ⟨49502, by rfl⟩ : syracuseStep 1056053 = 99005) (by norm_num)
theorem B892225 : Blo 702318 892225 := bbase (se 2 (by rfl) ⟨334584, by rfl⟩ : syracuseStep 892225 = 669169) (by norm_num)
theorem B793921 : Blo 702318 793921 := bbase (se 2 (by rfl) ⟨297720, by rfl⟩ : syracuseStep 793921 = 595441) (by norm_num)
theorem B1187149 : Blo 702318 1187149 := bbase (se 3 (by rfl) ⟨222590, by rfl⟩ : syracuseStep 1187149 = 445181) (by norm_num)
theorem B1056077 : Blo 702318 1056077 := bbase (se 3 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 1056077 = 396029) (by norm_num)
theorem B1580381 : Blo 702318 1580381 := bbase (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) (by norm_num)
theorem B1056101 : Blo 702318 1056101 := bbase (se 4 (by rfl) ⟨99009, by rfl⟩ : syracuseStep 1056101 = 198019) (by norm_num)
theorem B793957 : Blo 702318 793957 := bbase (se 4 (by rfl) ⟨74433, by rfl⟩ : syracuseStep 793957 = 148867) (by norm_num)
theorem B1056125 : Blo 702318 1056125 := bbase (se 3 (by rfl) ⟨198023, by rfl⟩ : syracuseStep 1056125 = 396047) (by norm_num)
theorem B793993 : Blo 702318 793993 := bbase (se 2 (by rfl) ⟨297747, by rfl⟩ : syracuseStep 793993 = 595495) (by norm_num)
theorem B1056149 : Blo 702318 1056149 := bbase (se 6 (by rfl) ⟨24753, by rfl⟩ : syracuseStep 1056149 = 49507) (by norm_num)
theorem B1580453 : Blo 702318 1580453 := bbase (se 4 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 1580453 = 296335) (by norm_num)
theorem B1187237 : Blo 702318 1187237 := bbase (se 4 (by rfl) ⟨111303, by rfl⟩ : syracuseStep 1187237 = 222607) (by norm_num)
theorem B1056173 : Blo 702318 1056173 := bbase (se 3 (by rfl) ⟨198032, by rfl⟩ : syracuseStep 1056173 = 396065) (by norm_num)
theorem B794029 : Blo 702318 794029 := bbase (se 3 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 794029 = 297761) (by norm_num)
theorem B1056197 : Blo 702318 1056197 := bbase (se 4 (by rfl) ⟨99018, by rfl⟩ : syracuseStep 1056197 = 198037) (by norm_num)
theorem B794065 : Blo 702318 794065 := bbase (se 2 (by rfl) ⟨297774, by rfl⟩ : syracuseStep 794065 = 595549) (by norm_num)
theorem B1056221 : Blo 702318 1056221 := bbase (se 3 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 1056221 = 396083) (by norm_num)
theorem B892397 : Blo 702318 892397 := bbase (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) (by norm_num)
theorem B1580525 : Blo 702318 1580525 := bbase (se 3 (by rfl) ⟨296348, by rfl⟩ : syracuseStep 1580525 = 592697) (by norm_num)
theorem B1056245 : Blo 702318 1056245 := bbase (se 5 (by rfl) ⟨49511, by rfl⟩ : syracuseStep 1056245 = 99023) (by norm_num)
theorem B794101 : Blo 702318 794101 := bbase (se 5 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 794101 = 74447) (by norm_num)
theorem B1056269 : Blo 702318 1056269 := bbase (se 3 (by rfl) ⟨198050, by rfl⟩ : syracuseStep 1056269 = 396101) (by norm_num)
theorem B794137 : Blo 702318 794137 := bbase (se 2 (by rfl) ⟨297801, by rfl⟩ : syracuseStep 794137 = 595603) (by norm_num)
theorem B1187365 : Blo 702318 1187365 := bbase (se 4 (by rfl) ⟨111315, by rfl⟩ : syracuseStep 1187365 = 222631) (by norm_num)
theorem B1056293 : Blo 702318 1056293 := bbase (se 4 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 1056293 = 198055) (by norm_num)
theorem B892453 : Blo 702318 892453 := bbase (se 4 (by rfl) ⟨83667, by rfl⟩ : syracuseStep 892453 = 167335) (by norm_num)
theorem B1580597 : Blo 702318 1580597 := bbase (se 5 (by rfl) ⟨74090, by rfl⟩ : syracuseStep 1580597 = 148181) (by norm_num)
theorem B1056317 : Blo 702318 1056317 := bbase (se 3 (by rfl) ⟨198059, by rfl⟩ : syracuseStep 1056317 = 396119) (by norm_num)
theorem B794173 : Blo 702318 794173 := bbase (se 3 (by rfl) ⟨148907, by rfl⟩ : syracuseStep 794173 = 297815) (by norm_num)
theorem B1056341 : Blo 702318 1056341 := bbase (se 8 (by rfl) ⟨6189, by rfl⟩ : syracuseStep 1056341 = 12379) (by norm_num)
theorem B794209 : Blo 702318 794209 := bbase (se 2 (by rfl) ⟨297828, by rfl⟩ : syracuseStep 794209 = 595657) (by norm_num)
theorem B1056365 : Blo 702318 1056365 := bbase (se 3 (by rfl) ⟨198068, by rfl⟩ : syracuseStep 1056365 = 396137) (by norm_num)
theorem B1580669 : Blo 702318 1580669 := bbase (se 3 (by rfl) ⟨296375, by rfl⟩ : syracuseStep 1580669 = 592751) (by norm_num)
theorem B1187453 : Blo 702318 1187453 := bbase (se 3 (by rfl) ⟨222647, by rfl⟩ : syracuseStep 1187453 = 445295) (by norm_num)
theorem B1056389 : Blo 702318 1056389 := bbase (se 4 (by rfl) ⟨99036, by rfl⟩ : syracuseStep 1056389 = 198073) (by norm_num)
theorem B892549 : Blo 702318 892549 := bbase (se 4 (by rfl) ⟨83676, by rfl⟩ : syracuseStep 892549 = 167353) (by norm_num)
theorem B794245 : Blo 702318 794245 := bbase (se 4 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 794245 = 148921) (by norm_num)
theorem B1056413 : Blo 702318 1056413 := bbase (se 3 (by rfl) ⟨198077, by rfl⟩ : syracuseStep 1056413 = 396155) (by norm_num)
theorem B794281 : Blo 702318 794281 := bbase (se 2 (by rfl) ⟨297855, by rfl⟩ : syracuseStep 794281 = 595711) (by norm_num)
theorem B1056437 : Blo 702318 1056437 := bbase (se 5 (by rfl) ⟨49520, by rfl⟩ : syracuseStep 1056437 = 99041) (by norm_num)
theorem B1580741 : Blo 702318 1580741 := bbase (se 4 (by rfl) ⟨148194, by rfl⟩ : syracuseStep 1580741 = 296389) (by norm_num)
theorem B1056461 : Blo 702318 1056461 := bbase (se 3 (by rfl) ⟨198086, by rfl⟩ : syracuseStep 1056461 = 396173) (by norm_num)
theorem B794317 : Blo 702318 794317 := bbase (se 3 (by rfl) ⟨148934, by rfl⟩ : syracuseStep 794317 = 297869) (by norm_num)
theorem B1056485 : Blo 702318 1056485 := bbase (se 4 (by rfl) ⟨99045, by rfl⟩ : syracuseStep 1056485 = 198091) (by norm_num)
theorem B794353 : Blo 702318 794353 := bbase (se 2 (by rfl) ⟨297882, by rfl⟩ : syracuseStep 794353 = 595765) (by norm_num)
theorem B1187581 : Blo 702318 1187581 := bbase (se 3 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 1187581 = 445343) (by norm_num)
theorem B1056509 : Blo 702318 1056509 := bbase (se 3 (by rfl) ⟨198095, by rfl⟩ : syracuseStep 1056509 = 396191) (by norm_num)
theorem B1580813 : Blo 702318 1580813 := bbase (se 3 (by rfl) ⟨296402, by rfl⟩ : syracuseStep 1580813 = 592805) (by norm_num)
theorem B1056533 : Blo 702318 1056533 := bbase (se 6 (by rfl) ⟨24762, by rfl⟩ : syracuseStep 1056533 = 49525) (by norm_num)
theorem B794389 : Blo 702318 794389 := bbase (se 6 (by rfl) ⟨18618, by rfl⟩ : syracuseStep 794389 = 37237) (by norm_num)
theorem B1056557 : Blo 702318 1056557 := bbase (se 3 (by rfl) ⟨198104, by rfl⟩ : syracuseStep 1056557 = 396209) (by norm_num)
theorem B892721 : Blo 702318 892721 := bbase (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) (by norm_num)
theorem B794425 : Blo 702318 794425 := bbase (se 2 (by rfl) ⟨297909, by rfl⟩ : syracuseStep 794425 = 595819) (by norm_num)
theorem B1056581 : Blo 702318 1056581 := bbase (se 4 (by rfl) ⟨99054, by rfl⟩ : syracuseStep 1056581 = 198109) (by norm_num)
theorem B2006869 : Blo 702318 2006869 := bbase (se 9 (by rfl) ⟨5879, by rfl⟩ : syracuseStep 2006869 = 11759) (by norm_num)
theorem B1580885 : Blo 702318 1580885 := bbase (se 9 (by rfl) ⟨4631, by rfl⟩ : syracuseStep 1580885 = 9263) (by norm_num)
theorem B1187669 : Blo 702318 1187669 := bbase (se 9 (by rfl) ⟨3479, by rfl⟩ : syracuseStep 1187669 = 6959) (by norm_num)
theorem B1056605 : Blo 702318 1056605 := bbase (se 3 (by rfl) ⟨198113, by rfl⟩ : syracuseStep 1056605 = 396227) (by norm_num)
theorem B794461 : Blo 702318 794461 := bbase (se 3 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 794461 = 297923) (by norm_num)
theorem B892777 : Blo 702318 892777 := bbase (se 2 (by rfl) ⟨334791, by rfl⟩ : syracuseStep 892777 = 669583) (by norm_num)
theorem B1056629 : Blo 702318 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B794497 : Blo 702318 794497 := bbase (se 2 (by rfl) ⟨297936, by rfl⟩ : syracuseStep 794497 = 595873) (by norm_num)
theorem B1908613 : Blo 702318 1908613 := bbase (se 4 (by rfl) ⟨178932, by rfl⟩ : syracuseStep 1908613 = 357865) (by norm_num)
theorem B1056653 : Blo 702318 1056653 := bbase (se 3 (by rfl) ⟨198122, by rfl⟩ : syracuseStep 1056653 = 396245) (by norm_num)
theorem B1580957 : Blo 702318 1580957 := bbase (se 3 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 1580957 = 592859) (by norm_num)
theorem B2138021 : Blo 702318 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B1056677 : Blo 702318 1056677 := bbase (se 4 (by rfl) ⟨99063, by rfl⟩ : syracuseStep 1056677 = 198127) (by norm_num)
theorem B794533 : Blo 702318 794533 := bbase (se 4 (by rfl) ⟨74487, by rfl⟩ : syracuseStep 794533 = 148975) (by norm_num)
theorem B1056701 : Blo 702318 1056701 := bbase (se 3 (by rfl) ⟨198131, by rfl⟩ : syracuseStep 1056701 = 396263) (by norm_num)
theorem B892873 : Blo 702318 892873 := bbase (se 2 (by rfl) ⟨334827, by rfl⟩ : syracuseStep 892873 = 669655) (by norm_num)
theorem B794569 : Blo 702318 794569 := bbase (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) (by norm_num)
theorem B1187797 : Blo 702318 1187797 := bbase (se 7 (by rfl) ⟨13919, by rfl⟩ : syracuseStep 1187797 = 27839) (by norm_num)
theorem B1056725 : Blo 702318 1056725 := bbase (se 7 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 1056725 = 24767) (by norm_num)
theorem B1581029 : Blo 702318 1581029 := bbase (se 4 (by rfl) ⟨148221, by rfl⟩ : syracuseStep 1581029 = 296443) (by norm_num)
theorem B1056749 : Blo 702318 1056749 := bbase (se 3 (by rfl) ⟨198140, by rfl⟩ : syracuseStep 1056749 = 396281) (by norm_num)
theorem B794605 : Blo 702318 794605 := bbase (se 3 (by rfl) ⟨148988, by rfl⟩ : syracuseStep 794605 = 297977) (by norm_num)
theorem B1056773 : Blo 702318 1056773 := bbase (se 4 (by rfl) ⟨99072, by rfl⟩ : syracuseStep 1056773 = 198145) (by norm_num)
theorem B1056797 : Blo 702318 1056797 := bbase (se 3 (by rfl) ⟨198149, by rfl⟩ : syracuseStep 1056797 = 396299) (by norm_num)
theorem B1581101 : Blo 702318 1581101 := bbase (se 3 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 1581101 = 592913) (by norm_num)
theorem B1187885 : Blo 702318 1187885 := bbase (se 3 (by rfl) ⟨222728, by rfl⟩ : syracuseStep 1187885 = 445457) (by norm_num)
theorem B1056821 : Blo 702318 1056821 := bbase (se 5 (by rfl) ⟨49538, by rfl⟩ : syracuseStep 1056821 = 99077) (by norm_num)
theorem B1056845 : Blo 702318 1056845 := bbase (se 3 (by rfl) ⟨198158, by rfl⟩ : syracuseStep 1056845 = 396317) (by norm_num)
theorem B1056869 : Blo 702318 1056869 := bbase (se 4 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 1056869 = 198163) (by norm_num)
theorem B1581173 : Blo 702318 1581173 := bbase (se 5 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 1581173 = 148235) (by norm_num)
theorem B893045 : Blo 702318 893045 := bbase (se 5 (by rfl) ⟨41861, by rfl⟩ : syracuseStep 893045 = 83723) (by norm_num)
theorem B1056893 : Blo 702318 1056893 := bbase (se 3 (by rfl) ⟨198167, by rfl⟩ : syracuseStep 1056893 = 396335) (by norm_num)
theorem B4006037 : Blo 702318 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B1056917 : Blo 702318 1056917 := bbase (se 6 (by rfl) ⟨24771, by rfl⟩ : syracuseStep 1056917 = 49543) (by norm_num)
theorem B1188013 : Blo 702318 1188013 := bbase (se 3 (by rfl) ⟨222752, by rfl⟩ : syracuseStep 1188013 = 445505) (by norm_num)
theorem B1056941 : Blo 702318 1056941 := bbase (se 3 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 1056941 = 396353) (by norm_num)
theorem B893101 : Blo 702318 893101 := bbase (se 3 (by rfl) ⟨167456, by rfl⟩ : syracuseStep 893101 = 334913) (by norm_num)
theorem B1581245 : Blo 702318 1581245 := bbase (se 3 (by rfl) ⟨296483, by rfl⟩ : syracuseStep 1581245 = 592967) (by norm_num)
theorem B1056965 : Blo 702318 1056965 := bbase (se 4 (by rfl) ⟨99090, by rfl⟩ : syracuseStep 1056965 = 198181) (by norm_num)
theorem B1056989 : Blo 702318 1056989 := bbase (se 3 (by rfl) ⟨198185, by rfl⟩ : syracuseStep 1056989 = 396371) (by norm_num)
theorem B1777909 : Blo 702318 1777909 := bbase (se 5 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 1777909 = 166679) (by norm_num)
theorem B1057013 : Blo 702318 1057013 := bbase (se 5 (by rfl) ⟨49547, by rfl⟩ : syracuseStep 1057013 = 99095) (by norm_num)
theorem B1581317 : Blo 702318 1581317 := bbase (se 4 (by rfl) ⟨148248, by rfl⟩ : syracuseStep 1581317 = 296497) (by norm_num)
theorem B1188101 : Blo 702318 1188101 := bbase (se 4 (by rfl) ⟨111384, by rfl⟩ : syracuseStep 1188101 = 222769) (by norm_num)
theorem B1057037 : Blo 702318 1057037 := bbase (se 3 (by rfl) ⟨198194, by rfl⟩ : syracuseStep 1057037 = 396389) (by norm_num)
theorem B893197 : Blo 702318 893197 := bbase (se 3 (by rfl) ⟨167474, by rfl⟩ : syracuseStep 893197 = 334949) (by norm_num)
theorem B1057061 : Blo 702318 1057061 := bbase (se 4 (by rfl) ⟨99099, by rfl⟩ : syracuseStep 1057061 = 198199) (by norm_num)
theorem B1057085 : Blo 702318 1057085 := bbase (se 3 (by rfl) ⟨198203, by rfl⟩ : syracuseStep 1057085 = 396407) (by norm_num)
theorem B1581389 : Blo 702318 1581389 := bbase (se 3 (by rfl) ⟨296510, by rfl⟩ : syracuseStep 1581389 = 593021) (by norm_num)
theorem B1057109 : Blo 702318 1057109 := bbase (se 10 (by rfl) ⟨1548, by rfl⟩ : syracuseStep 1057109 = 3097) (by norm_num)
theorem B1778021 : Blo 702318 1778021 := bbase (se 4 (by rfl) ⟨166689, by rfl⟩ : syracuseStep 1778021 = 333379) (by norm_num)
theorem B1057133 : Blo 702318 1057133 := bbase (se 3 (by rfl) ⟨198212, by rfl⟩ : syracuseStep 1057133 = 396425) (by norm_num)
theorem B1188229 : Blo 702318 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B1057157 : Blo 702318 1057157 := bbase (se 4 (by rfl) ⟨99108, by rfl⟩ : syracuseStep 1057157 = 198217) (by norm_num)
theorem B1581461 : Blo 702318 1581461 := bbase (se 6 (by rfl) ⟨37065, by rfl⟩ : syracuseStep 1581461 = 74131) (by norm_num)
theorem B1057181 : Blo 702318 1057181 := bbase (se 3 (by rfl) ⟨198221, by rfl⟩ : syracuseStep 1057181 = 396443) (by norm_num)
theorem B1057205 : Blo 702318 1057205 := bbase (se 5 (by rfl) ⟨49556, by rfl⟩ : syracuseStep 1057205 = 99113) (by norm_num)
theorem B893369 : Blo 702318 893369 := bbase (se 2 (by rfl) ⟨335013, by rfl⟩ : syracuseStep 893369 = 670027) (by norm_num)
theorem B1057229 : Blo 702318 1057229 := bbase (se 3 (by rfl) ⟨198230, by rfl⟩ : syracuseStep 1057229 = 396461) (by norm_num)
theorem B1581533 : Blo 702318 1581533 := bbase (se 3 (by rfl) ⟨296537, by rfl⟩ : syracuseStep 1581533 = 593075) (by norm_num)
theorem B1188317 : Blo 702318 1188317 := bbase (se 3 (by rfl) ⟨222809, by rfl⟩ : syracuseStep 1188317 = 445619) (by norm_num)
theorem B1057253 : Blo 702318 1057253 := bbase (se 4 (by rfl) ⟨99117, by rfl⟩ : syracuseStep 1057253 = 198235) (by norm_num)
theorem B893425 : Blo 702318 893425 := bbase (se 2 (by rfl) ⟨335034, by rfl⟩ : syracuseStep 893425 = 670069) (by norm_num)
theorem B1057277 : Blo 702318 1057277 := bbase (se 3 (by rfl) ⟨198239, by rfl⟩ : syracuseStep 1057277 = 396479) (by norm_num)
theorem B1057301 : Blo 702318 1057301 := bbase (se 6 (by rfl) ⟨24780, by rfl⟩ : syracuseStep 1057301 = 49561) (by norm_num)
theorem B1778213 : Blo 702318 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B1581605 : Blo 702318 1581605 := bbase (se 4 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 1581605 = 296551) (by norm_num)
theorem B1057325 : Blo 702318 1057325 := bbase (se 3 (by rfl) ⟨198248, by rfl⟩ : syracuseStep 1057325 = 396497) (by norm_num)
theorem B1057349 : Blo 702318 1057349 := bbase (se 4 (by rfl) ⟨99126, by rfl⟩ : syracuseStep 1057349 = 198253) (by norm_num)
theorem B893521 : Blo 702318 893521 := bbase (se 2 (by rfl) ⟨335070, by rfl⟩ : syracuseStep 893521 = 670141) (by norm_num)
theorem B1188445 : Blo 702318 1188445 := bbase (se 3 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 1188445 = 445667) (by norm_num)
theorem B1057373 : Blo 702318 1057373 := bbase (se 3 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 1057373 = 396515) (by norm_num)
theorem B1581677 : Blo 702318 1581677 := bbase (se 3 (by rfl) ⟨296564, by rfl⟩ : syracuseStep 1581677 = 593129) (by norm_num)
theorem B1057397 : Blo 702318 1057397 := bbase (se 5 (by rfl) ⟨49565, by rfl⟩ : syracuseStep 1057397 = 99131) (by norm_num)
theorem B1057421 : Blo 702318 1057421 := bbase (se 3 (by rfl) ⟨198266, by rfl⟩ : syracuseStep 1057421 = 396533) (by norm_num)
theorem B1057445 : Blo 702318 1057445 := bbase (se 4 (by rfl) ⟨99135, by rfl⟩ : syracuseStep 1057445 = 198271) (by norm_num)
theorem B1581749 : Blo 702318 1581749 := bbase (se 5 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 1581749 = 148289) (by norm_num)
theorem B1188533 : Blo 702318 1188533 := bbase (se 5 (by rfl) ⟨55712, by rfl⟩ : syracuseStep 1188533 = 111425) (by norm_num)
theorem B1057469 : Blo 702318 1057469 := bbase (se 3 (by rfl) ⟨198275, by rfl⟩ : syracuseStep 1057469 = 396551) (by norm_num)
theorem B1057493 : Blo 702318 1057493 := bbase (se 7 (by rfl) ⟨12392, by rfl⟩ : syracuseStep 1057493 = 24785) (by norm_num)
theorem B1057517 : Blo 702318 1057517 := bbase (se 3 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 1057517 = 396569) (by norm_num)
theorem B2138869 : Blo 702318 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B1581821 : Blo 702318 1581821 := bbase (se 3 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 1581821 = 593183) (by norm_num)
theorem B893693 : Blo 702318 893693 := bbase (se 3 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 893693 = 335135) (by norm_num)
theorem B1057541 : Blo 702318 1057541 := bbase (se 4 (by rfl) ⟨99144, by rfl⟩ : syracuseStep 1057541 = 198289) (by norm_num)
theorem B1057565 : Blo 702318 1057565 := bbase (se 3 (by rfl) ⟨198293, by rfl⟩ : syracuseStep 1057565 = 396587) (by norm_num)
theorem B1188661 : Blo 702318 1188661 := bbase (se 5 (by rfl) ⟨55718, by rfl⟩ : syracuseStep 1188661 = 111437) (by norm_num)
theorem B1057589 : Blo 702318 1057589 := bbase (se 5 (by rfl) ⟨49574, by rfl⟩ : syracuseStep 1057589 = 99149) (by norm_num)
theorem B893749 : Blo 702318 893749 := bbase (se 5 (by rfl) ⟨41894, by rfl⟩ : syracuseStep 893749 = 83789) (by norm_num)
theorem B1581893 : Blo 702318 1581893 := bbase (se 4 (by rfl) ⟨148302, by rfl⟩ : syracuseStep 1581893 = 296605) (by norm_num)
theorem B1057613 : Blo 702318 1057613 := bbase (se 3 (by rfl) ⟨198302, by rfl⟩ : syracuseStep 1057613 = 396605) (by norm_num)
theorem B1057637 : Blo 702318 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B1778557 : Blo 702318 1778557 := bbase (se 3 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 1778557 = 666959) (by norm_num)
theorem B1057661 : Blo 702318 1057661 := bbase (se 3 (by rfl) ⟨198311, by rfl⟩ : syracuseStep 1057661 = 396623) (by norm_num)
theorem B1581965 : Blo 702318 1581965 := bbase (se 3 (by rfl) ⟨296618, by rfl⟩ : syracuseStep 1581965 = 593237) (by norm_num)
theorem B1188749 : Blo 702318 1188749 := bbase (se 3 (by rfl) ⟨222890, by rfl⟩ : syracuseStep 1188749 = 445781) (by norm_num)
theorem B1057685 : Blo 702318 1057685 := bbase (se 6 (by rfl) ⟨24789, by rfl⟩ : syracuseStep 1057685 = 49579) (by norm_num)
theorem B893845 : Blo 702318 893845 := bbase (se 6 (by rfl) ⟨20949, by rfl⟩ : syracuseStep 893845 = 41899) (by norm_num)
theorem B1057709 : Blo 702318 1057709 := bbase (se 3 (by rfl) ⟨198320, by rfl⟩ : syracuseStep 1057709 = 396641) (by norm_num)
theorem B1057733 : Blo 702318 1057733 := bbase (se 4 (by rfl) ⟨99162, by rfl⟩ : syracuseStep 1057733 = 198325) (by norm_num)
theorem B1582037 : Blo 702318 1582037 := bbase (se 7 (by rfl) ⟨18539, by rfl⟩ : syracuseStep 1582037 = 37079) (by norm_num)
theorem B1057757 : Blo 702318 1057757 := bbase (se 3 (by rfl) ⟨198329, by rfl⟩ : syracuseStep 1057757 = 396659) (by norm_num)
theorem B1778669 : Blo 702318 1778669 := bbase (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) (by norm_num)
theorem B1057781 : Blo 702318 1057781 := bbase (se 5 (by rfl) ⟨49583, by rfl⟩ : syracuseStep 1057781 = 99167) (by norm_num)
theorem B1188877 : Blo 702318 1188877 := bbase (se 3 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 1188877 = 445829) (by norm_num)
theorem B1057805 : Blo 702318 1057805 := bbase (se 3 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 1057805 = 396677) (by norm_num)
theorem B1582109 : Blo 702318 1582109 := bbase (se 3 (by rfl) ⟨296645, by rfl⟩ : syracuseStep 1582109 = 593291) (by norm_num)
theorem B1057829 : Blo 702318 1057829 := bbase (se 4 (by rfl) ⟨99171, by rfl⟩ : syracuseStep 1057829 = 198343) (by norm_num)
theorem B1057853 : Blo 702318 1057853 := bbase (se 3 (by rfl) ⟨198347, by rfl⟩ : syracuseStep 1057853 = 396695) (by norm_num)
theorem B762949 : Blo 702318 762949 := bbase (se 4 (by rfl) ⟨71526, by rfl⟩ : syracuseStep 762949 = 143053) (by norm_num)
theorem B1057877 : Blo 702318 1057877 := bbase (se 8 (by rfl) ⟨6198, by rfl⟩ : syracuseStep 1057877 = 12397) (by norm_num)
theorem B1582181 : Blo 702318 1582181 := bbase (se 4 (by rfl) ⟨148329, by rfl⟩ : syracuseStep 1582181 = 296659) (by norm_num)
theorem B1188965 : Blo 702318 1188965 := bbase (se 4 (by rfl) ⟨111465, by rfl⟩ : syracuseStep 1188965 = 222931) (by norm_num)
theorem B1057901 : Blo 702318 1057901 := bbase (se 3 (by rfl) ⟨198356, by rfl⟩ : syracuseStep 1057901 = 396713) (by norm_num)
theorem B1057925 : Blo 702318 1057925 := bbase (se 4 (by rfl) ⟨99180, by rfl⟩ : syracuseStep 1057925 = 198361) (by norm_num)
theorem B1057949 : Blo 702318 1057949 := bbase (se 3 (by rfl) ⟨198365, by rfl⟩ : syracuseStep 1057949 = 396731) (by norm_num)
theorem B3515557 : Blo 702318 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B1778861 : Blo 702318 1778861 := bbase (se 3 (by rfl) ⟨333536, by rfl⟩ : syracuseStep 1778861 = 667073) (by norm_num)
theorem B1582253 : Blo 702318 1582253 := bbase (se 3 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 1582253 = 593345) (by norm_num)
theorem B1156277 : Blo 702318 1156277 := bbase (se 5 (by rfl) ⟨54200, by rfl⟩ : syracuseStep 1156277 = 108401) (by norm_num)
theorem B1057973 : Blo 702318 1057973 := bbase (se 5 (by rfl) ⟨49592, by rfl⟩ : syracuseStep 1057973 = 99185) (by norm_num)
theorem B1057997 : Blo 702318 1057997 := bbase (se 3 (by rfl) ⟨198374, by rfl⟩ : syracuseStep 1057997 = 396749) (by norm_num)
theorem B1189093 : Blo 702318 1189093 := bbase (se 4 (by rfl) ⟨111477, by rfl⟩ : syracuseStep 1189093 = 222955) (by norm_num)
theorem B1058021 : Blo 702318 1058021 := bbase (se 4 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 1058021 = 198379) (by norm_num)
theorem B1582325 : Blo 702318 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B1058045 : Blo 702318 1058045 := bbase (se 3 (by rfl) ⟨198383, by rfl⟩ : syracuseStep 1058045 = 396767) (by norm_num)
theorem B1713421 : Blo 702318 1713421 := bbase (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) (by norm_num)
theorem B1058069 : Blo 702318 1058069 := bbase (se 6 (by rfl) ⟨24798, by rfl⟩ : syracuseStep 1058069 = 49597) (by norm_num)
theorem B1058093 : Blo 702318 1058093 := bbase (se 3 (by rfl) ⟨198392, by rfl⟩ : syracuseStep 1058093 = 396785) (by norm_num)
theorem B1582397 : Blo 702318 1582397 := bbase (se 3 (by rfl) ⟨296699, by rfl⟩ : syracuseStep 1582397 = 593399) (by norm_num)
theorem B1189181 : Blo 702318 1189181 := bbase (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) (by norm_num)
theorem B1058117 : Blo 702318 1058117 := bbase (se 4 (by rfl) ⟨99198, by rfl⟩ : syracuseStep 1058117 = 198397) (by norm_num)
theorem B1058141 : Blo 702318 1058141 := bbase (se 3 (by rfl) ⟨198401, by rfl⟩ : syracuseStep 1058141 = 396803) (by norm_num)
theorem B1058165 : Blo 702318 1058165 := bbase (se 5 (by rfl) ⟨49601, by rfl⟩ : syracuseStep 1058165 = 99203) (by norm_num)
theorem B1582469 : Blo 702318 1582469 := bbase (se 4 (by rfl) ⟨148356, by rfl⟩ : syracuseStep 1582469 = 296713) (by norm_num)
theorem B1058189 : Blo 702318 1058189 := bbase (se 3 (by rfl) ⟨198410, by rfl⟩ : syracuseStep 1058189 = 396821) (by norm_num)
theorem B1058213 : Blo 702318 1058213 := bbase (se 4 (by rfl) ⟨99207, by rfl⟩ : syracuseStep 1058213 = 198415) (by norm_num)
theorem B1189309 : Blo 702318 1189309 := bbase (se 3 (by rfl) ⟨222995, by rfl⟩ : syracuseStep 1189309 = 445991) (by norm_num)
theorem B1058237 : Blo 702318 1058237 := bbase (se 3 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 1058237 = 396839) (by norm_num)
theorem B1582541 : Blo 702318 1582541 := bbase (se 3 (by rfl) ⟨296726, by rfl⟩ : syracuseStep 1582541 = 593453) (by norm_num)
theorem B1713613 : Blo 702318 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B1058261 : Blo 702318 1058261 := bbase (se 7 (by rfl) ⟨12401, by rfl⟩ : syracuseStep 1058261 = 24803) (by norm_num)
theorem B1058285 : Blo 702318 1058285 := bbase (se 3 (by rfl) ⟨198428, by rfl⟩ : syracuseStep 1058285 = 396857) (by norm_num)
theorem B1779205 : Blo 702318 1779205 := bbase (se 4 (by rfl) ⟨166800, by rfl⟩ : syracuseStep 1779205 = 333601) (by norm_num)
theorem B1058309 : Blo 702318 1058309 := bbase (se 4 (by rfl) ⟨99216, by rfl⟩ : syracuseStep 1058309 = 198433) (by norm_num)
theorem B1582613 : Blo 702318 1582613 := bbase (se 6 (by rfl) ⟨37092, by rfl⟩ : syracuseStep 1582613 = 74185) (by norm_num)
theorem B1189397 : Blo 702318 1189397 := bbase (se 6 (by rfl) ⟨27876, by rfl⟩ : syracuseStep 1189397 = 55753) (by norm_num)
theorem B1058333 : Blo 702318 1058333 := bbase (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) (by norm_num)
theorem B1058357 : Blo 702318 1058357 := bbase (se 5 (by rfl) ⟨49610, by rfl⟩ : syracuseStep 1058357 = 99221) (by norm_num)
theorem B1058381 : Blo 702318 1058381 := bbase (se 3 (by rfl) ⟨198446, by rfl⟩ : syracuseStep 1058381 = 396893) (by norm_num)
theorem B1582685 : Blo 702318 1582685 := bbase (se 3 (by rfl) ⟨296753, by rfl⟩ : syracuseStep 1582685 = 593507) (by norm_num)
theorem B1058405 : Blo 702318 1058405 := bbase (se 4 (by rfl) ⟨99225, by rfl⟩ : syracuseStep 1058405 = 198451) (by norm_num)
theorem B1779317 : Blo 702318 1779317 := bbase (se 5 (by rfl) ⟨83405, by rfl⟩ : syracuseStep 1779317 = 166811) (by norm_num)
theorem B1058429 : Blo 702318 1058429 := bbase (se 3 (by rfl) ⟨198455, by rfl⟩ : syracuseStep 1058429 = 396911) (by norm_num)
theorem B763537 : Blo 702318 763537 := bbase (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) (by norm_num)
theorem B1189525 : Blo 702318 1189525 := bbase (se 6 (by rfl) ⟨27879, by rfl⟩ : syracuseStep 1189525 = 55759) (by norm_num)
theorem B1058453 : Blo 702318 1058453 := bbase (se 6 (by rfl) ⟨24807, by rfl⟩ : syracuseStep 1058453 = 49615) (by norm_num)
theorem B1582757 : Blo 702318 1582757 := bbase (se 4 (by rfl) ⟨148383, by rfl⟩ : syracuseStep 1582757 = 296767) (by norm_num)
theorem B1058477 : Blo 702318 1058477 := bbase (se 3 (by rfl) ⟨198464, by rfl⟩ : syracuseStep 1058477 = 396929) (by norm_num)
theorem B1058501 : Blo 702318 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B1058525 : Blo 702318 1058525 := bbase (se 3 (by rfl) ⟨198473, by rfl⟩ : syracuseStep 1058525 = 396947) (by norm_num)
theorem B1582829 : Blo 702318 1582829 := bbase (se 3 (by rfl) ⟨296780, by rfl⟩ : syracuseStep 1582829 = 593561) (by norm_num)
theorem B1189613 : Blo 702318 1189613 := bbase (se 3 (by rfl) ⟨223052, by rfl⟩ : syracuseStep 1189613 = 446105) (by norm_num)
theorem B1058549 : Blo 702318 1058549 := bbase (se 5 (by rfl) ⟨49619, by rfl⟩ : syracuseStep 1058549 = 99239) (by norm_num)
theorem B1058573 : Blo 702318 1058573 := bbase (se 3 (by rfl) ⟨198482, by rfl⟩ : syracuseStep 1058573 = 396965) (by norm_num)
theorem B4073237 : Blo 702318 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1058597 : Blo 702318 1058597 := bbase (se 4 (by rfl) ⟨99243, by rfl⟩ : syracuseStep 1058597 = 198487) (by norm_num)
theorem B1779509 : Blo 702318 1779509 := bbase (se 5 (by rfl) ⟨83414, by rfl⟩ : syracuseStep 1779509 = 166829) (by norm_num)
theorem B1582901 : Blo 702318 1582901 := bbase (se 5 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 1582901 = 148397) (by norm_num)
theorem B1058621 : Blo 702318 1058621 := bbase (se 3 (by rfl) ⟨198491, by rfl⟩ : syracuseStep 1058621 = 396983) (by norm_num)
theorem B1058645 : Blo 702318 1058645 := bbase (se 9 (by rfl) ⟨3101, by rfl⟩ : syracuseStep 1058645 = 6203) (by norm_num)
theorem B1189741 : Blo 702318 1189741 := bbase (se 3 (by rfl) ⟨223076, by rfl⟩ : syracuseStep 1189741 = 446153) (by norm_num)
theorem B1288045 : Blo 702318 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B1058669 : Blo 702318 1058669 := bbase (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) (by norm_num)
theorem B1582973 : Blo 702318 1582973 := bbase (se 3 (by rfl) ⟨296807, by rfl⟩ : syracuseStep 1582973 = 593615) (by norm_num)
theorem B2140037 : Blo 702318 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B1058693 : Blo 702318 1058693 := bbase (se 4 (by rfl) ⟨99252, by rfl⟩ : syracuseStep 1058693 = 198505) (by norm_num)
theorem B1058717 : Blo 702318 1058717 := bbase (se 3 (by rfl) ⟨198509, by rfl⟩ : syracuseStep 1058717 = 397019) (by norm_num)
theorem B1058741 : Blo 702318 1058741 := bbase (se 5 (by rfl) ⟨49628, by rfl⟩ : syracuseStep 1058741 = 99257) (by norm_num)
theorem B1583045 : Blo 702318 1583045 := bbase (se 4 (by rfl) ⟨148410, by rfl⟩ : syracuseStep 1583045 = 296821) (by norm_num)
theorem B1189829 : Blo 702318 1189829 := bbase (se 4 (by rfl) ⟨111546, by rfl⟩ : syracuseStep 1189829 = 223093) (by norm_num)
theorem B1058765 : Blo 702318 1058765 := bbase (se 3 (by rfl) ⟨198518, by rfl⟩ : syracuseStep 1058765 = 397037) (by norm_num)
theorem B1058789 : Blo 702318 1058789 := bbase (se 4 (by rfl) ⟨99261, by rfl⟩ : syracuseStep 1058789 = 198523) (by norm_num)
theorem B1058813 : Blo 702318 1058813 := bbase (se 3 (by rfl) ⟨198527, by rfl⟩ : syracuseStep 1058813 = 397055) (by norm_num)
theorem B1583117 : Blo 702318 1583117 := bbase (se 3 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 1583117 = 593669) (by norm_num)
theorem B1058837 : Blo 702318 1058837 := bbase (se 6 (by rfl) ⟨24816, by rfl⟩ : syracuseStep 1058837 = 49633) (by norm_num)
theorem B1288237 : Blo 702318 1288237 := bbase (se 3 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 1288237 = 483089) (by norm_num)
theorem B1058861 : Blo 702318 1058861 := bbase (se 3 (by rfl) ⟨198536, by rfl⟩ : syracuseStep 1058861 = 397073) (by norm_num)
theorem B1189957 : Blo 702318 1189957 := bbase (se 4 (by rfl) ⟨111558, by rfl⟩ : syracuseStep 1189957 = 223117) (by norm_num)
theorem B1058885 : Blo 702318 1058885 := bbase (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) (by norm_num)
theorem B6006869 : Blo 702318 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B1583189 : Blo 702318 1583189 := bbase (se 8 (by rfl) ⟨9276, by rfl⟩ : syracuseStep 1583189 = 18553) (by norm_num)
theorem B5711957 : Blo 702318 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B1058909 : Blo 702318 1058909 := bbase (se 3 (by rfl) ⟨198545, by rfl⟩ : syracuseStep 1058909 = 397091) (by norm_num)
theorem B1058933 : Blo 702318 1058933 := bbase (se 5 (by rfl) ⟨49637, by rfl⟩ : syracuseStep 1058933 = 99275) (by norm_num)
theorem B1779853 : Blo 702318 1779853 := bbase (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) (by norm_num)
theorem B1058957 : Blo 702318 1058957 := bbase (se 3 (by rfl) ⟨198554, by rfl⟩ : syracuseStep 1058957 = 397109) (by norm_num)
theorem B1583261 : Blo 702318 1583261 := bbase (se 3 (by rfl) ⟨296861, by rfl⟩ : syracuseStep 1583261 = 593723) (by norm_num)
theorem B1190045 : Blo 702318 1190045 := bbase (se 3 (by rfl) ⟨223133, by rfl⟩ : syracuseStep 1190045 = 446267) (by norm_num)
theorem B1058981 : Blo 702318 1058981 := bbase (se 4 (by rfl) ⟨99279, by rfl⟩ : syracuseStep 1058981 = 198559) (by norm_num)
theorem B1059005 : Blo 702318 1059005 := bbase (se 3 (by rfl) ⟨198563, by rfl⟩ : syracuseStep 1059005 = 397127) (by norm_num)
theorem B1059029 : Blo 702318 1059029 := bbase (se 7 (by rfl) ⟨12410, by rfl⟩ : syracuseStep 1059029 = 24821) (by norm_num)
theorem B1583333 : Blo 702318 1583333 := bbase (se 4 (by rfl) ⟨148437, by rfl⟩ : syracuseStep 1583333 = 296875) (by norm_num)
theorem B1059053 : Blo 702318 1059053 := bbase (se 3 (by rfl) ⟨198572, by rfl⟩ : syracuseStep 1059053 = 397145) (by norm_num)
theorem B1779965 : Blo 702318 1779965 := bbase (se 3 (by rfl) ⟨333743, by rfl⟩ : syracuseStep 1779965 = 667487) (by norm_num)
theorem B1059077 : Blo 702318 1059077 := bbase (se 4 (by rfl) ⟨99288, by rfl⟩ : syracuseStep 1059077 = 198577) (by norm_num)
theorem B1190173 : Blo 702318 1190173 := bbase (se 3 (by rfl) ⟨223157, by rfl⟩ : syracuseStep 1190173 = 446315) (by norm_num)
theorem B1059101 : Blo 702318 1059101 := bbase (se 3 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 1059101 = 397163) (by norm_num)
theorem B1583405 : Blo 702318 1583405 := bbase (se 3 (by rfl) ⟨296888, by rfl⟩ : syracuseStep 1583405 = 593777) (by norm_num)
theorem B1059125 : Blo 702318 1059125 := bbase (se 5 (by rfl) ⟨49646, by rfl⟩ : syracuseStep 1059125 = 99293) (by norm_num)
theorem B1059149 : Blo 702318 1059149 := bbase (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) (by norm_num)
theorem B1059173 : Blo 702318 1059173 := bbase (se 4 (by rfl) ⟨99297, by rfl⟩ : syracuseStep 1059173 = 198595) (by norm_num)
theorem B1583477 : Blo 702318 1583477 := bbase (se 5 (by rfl) ⟨74225, by rfl⟩ : syracuseStep 1583477 = 148451) (by norm_num)
theorem B1190261 : Blo 702318 1190261 := bbase (se 5 (by rfl) ⟨55793, by rfl⟩ : syracuseStep 1190261 = 111587) (by norm_num)
theorem B1059197 : Blo 702318 1059197 := bbase (se 3 (by rfl) ⟨198599, by rfl⟩ : syracuseStep 1059197 = 397199) (by norm_num)
theorem B1059221 : Blo 702318 1059221 := bbase (se 6 (by rfl) ⟨24825, by rfl⟩ : syracuseStep 1059221 = 49651) (by norm_num)
theorem B1059245 : Blo 702318 1059245 := bbase (se 3 (by rfl) ⟨198608, by rfl⟩ : syracuseStep 1059245 = 397217) (by norm_num)
theorem B1780157 : Blo 702318 1780157 := bbase (se 3 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 1780157 = 667559) (by norm_num)
theorem B1583549 : Blo 702318 1583549 := bbase (se 3 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 1583549 = 593831) (by norm_num)
theorem B1059269 : Blo 702318 1059269 := bbase (se 4 (by rfl) ⟨99306, by rfl⟩ : syracuseStep 1059269 = 198613) (by norm_num)
theorem B1059293 : Blo 702318 1059293 := bbase (se 3 (by rfl) ⟨198617, by rfl⟩ : syracuseStep 1059293 = 397235) (by norm_num)
theorem B1190389 : Blo 702318 1190389 := bbase (se 5 (by rfl) ⟨55799, by rfl⟩ : syracuseStep 1190389 = 111599) (by norm_num)
theorem B1059317 : Blo 702318 1059317 := bbase (se 5 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 1059317 = 99311) (by norm_num)
theorem B1583621 : Blo 702318 1583621 := bbase (se 4 (by rfl) ⟨148464, by rfl⟩ : syracuseStep 1583621 = 296929) (by norm_num)
theorem B1059341 : Blo 702318 1059341 := bbase (se 3 (by rfl) ⟨198626, by rfl⟩ : syracuseStep 1059341 = 397253) (by norm_num)
theorem B1059365 : Blo 702318 1059365 := bbase (se 4 (by rfl) ⟨99315, by rfl⟩ : syracuseStep 1059365 = 198631) (by norm_num)
theorem B1059389 : Blo 702318 1059389 := bbase (se 3 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 1059389 = 397271) (by norm_num)
theorem B1583693 : Blo 702318 1583693 := bbase (se 3 (by rfl) ⟨296942, by rfl⟩ : syracuseStep 1583693 = 593885) (by norm_num)
theorem B1190477 : Blo 702318 1190477 := bbase (se 3 (by rfl) ⟨223214, by rfl⟩ : syracuseStep 1190477 = 446429) (by norm_num)
theorem B1059413 : Blo 702318 1059413 := bbase (se 8 (by rfl) ⟨6207, by rfl⟩ : syracuseStep 1059413 = 12415) (by norm_num)
theorem B1059437 : Blo 702318 1059437 := bbase (se 3 (by rfl) ⟨198644, by rfl⟩ : syracuseStep 1059437 = 397289) (by norm_num)
theorem B2009717 : Blo 702318 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B1059461 : Blo 702318 1059461 := bbase (se 4 (by rfl) ⟨99324, by rfl⟩ : syracuseStep 1059461 = 198649) (by norm_num)
theorem B1583765 : Blo 702318 1583765 := bbase (se 6 (by rfl) ⟨37119, by rfl⟩ : syracuseStep 1583765 = 74239) (by norm_num)
theorem B1190605 : Blo 702318 1190605 := bbase (se 3 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 1190605 = 446477) (by norm_num)
theorem B1583837 : Blo 702318 1583837 := bbase (se 3 (by rfl) ⟨296969, by rfl⟩ : syracuseStep 1583837 = 593939) (by norm_num)
theorem B1125109 : Blo 702318 1125109 := bbase (se 5 (by rfl) ⟨52739, by rfl⟩ : syracuseStep 1125109 = 105479) (by norm_num)
theorem B1780501 : Blo 702318 1780501 := bbase (se 6 (by rfl) ⟨41730, by rfl⟩ : syracuseStep 1780501 = 83461) (by norm_num)
theorem B11578133 : Blo 702318 11578133 := bbase (se 6 (by rfl) ⟨271362, by rfl⟩ : syracuseStep 11578133 = 542725) (by norm_num)
theorem B1583909 : Blo 702318 1583909 := bbase (se 4 (by rfl) ⟨148491, by rfl⟩ : syracuseStep 1583909 = 296983) (by norm_num)
theorem B1190693 : Blo 702318 1190693 := bbase (se 4 (by rfl) ⟨111627, by rfl⟩ : syracuseStep 1190693 = 223255) (by norm_num)
theorem B1583981 : Blo 702318 1583981 := bbase (se 3 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 1583981 = 593993) (by norm_num)
theorem B2370437 : Blo 702318 2370437 := bbase (se 4 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 2370437 = 444457) (by norm_num)
theorem B1780613 : Blo 702318 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B1190821 : Blo 702318 1190821 := bbase (se 4 (by rfl) ⟨111639, by rfl⟩ : syracuseStep 1190821 = 223279) (by norm_num)
theorem B1584053 : Blo 702318 1584053 := bbase (se 5 (by rfl) ⟨74252, by rfl⟩ : syracuseStep 1584053 = 148505) (by norm_num)
theorem B1584125 : Blo 702318 1584125 := bbase (se 3 (by rfl) ⟨297023, by rfl⟩ : syracuseStep 1584125 = 594047) (by norm_num)
theorem B1190909 : Blo 702318 1190909 := bbase (se 3 (by rfl) ⟨223295, by rfl⟩ : syracuseStep 1190909 = 446591) (by norm_num)
theorem B2534437 : Blo 702318 2534437 := bbase (se 4 (by rfl) ⟨237603, by rfl⟩ : syracuseStep 2534437 = 475207) (by norm_num)
theorem B1780805 : Blo 702318 1780805 := bbase (se 4 (by rfl) ⟨166950, by rfl⟩ : syracuseStep 1780805 = 333901) (by norm_num)
theorem B1584197 : Blo 702318 1584197 := bbase (se 4 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 1584197 = 297037) (by norm_num)
theorem B1191037 : Blo 702318 1191037 := bbase (se 3 (by rfl) ⟨223319, by rfl⟩ : syracuseStep 1191037 = 446639) (by norm_num)
theorem B1584269 : Blo 702318 1584269 := bbase (se 3 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 1584269 = 594101) (by norm_num)
theorem B1584341 : Blo 702318 1584341 := bbase (se 7 (by rfl) ⟨18566, by rfl⟩ : syracuseStep 1584341 = 37133) (by norm_num)
theorem B1191125 : Blo 702318 1191125 := bbase (se 7 (by rfl) ⟨13958, by rfl⟩ : syracuseStep 1191125 = 27917) (by norm_num)
theorem B1584413 : Blo 702318 1584413 := bbase (se 3 (by rfl) ⟨297077, by rfl⟩ : syracuseStep 1584413 = 594155) (by norm_num)
theorem B2370869 : Blo 702318 2370869 := bbase (se 5 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 2370869 = 222269) (by norm_num)
theorem B1191253 : Blo 702318 1191253 := bbase (se 11 (by rfl) ⟨872, by rfl⟩ : syracuseStep 1191253 = 1745) (by norm_num)
theorem B1584485 : Blo 702318 1584485 := bbase (se 4 (by rfl) ⟨148545, by rfl⟩ : syracuseStep 1584485 = 297091) (by norm_num)
theorem B1781149 : Blo 702318 1781149 := bbase (se 3 (by rfl) ⟨333965, by rfl⟩ : syracuseStep 1781149 = 667931) (by norm_num)
theorem B1584557 : Blo 702318 1584557 := bbase (se 3 (by rfl) ⟨297104, by rfl⟩ : syracuseStep 1584557 = 594209) (by norm_num)
theorem B1191341 : Blo 702318 1191341 := bbase (se 3 (by rfl) ⟨223376, by rfl⟩ : syracuseStep 1191341 = 446753) (by norm_num)
theorem B2862533 : Blo 702318 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B1584629 : Blo 702318 1584629 := bbase (se 5 (by rfl) ⟨74279, by rfl⟩ : syracuseStep 1584629 = 148559) (by norm_num)
theorem B1781261 : Blo 702318 1781261 := bbase (se 3 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 1781261 = 667973) (by norm_num)
theorem B13544981 : Blo 702318 13544981 := bbase (se 6 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 13544981 = 634921) (by norm_num)
theorem B1191469 : Blo 702318 1191469 := bbase (se 3 (by rfl) ⟨223400, by rfl⟩ : syracuseStep 1191469 = 446801) (by norm_num)
theorem B1584701 : Blo 702318 1584701 := bbase (se 3 (by rfl) ⟨297131, by rfl⟩ : syracuseStep 1584701 = 594263) (by norm_num)
theorem B2862661 : Blo 702318 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B1584773 : Blo 702318 1584773 := bbase (se 4 (by rfl) ⟨148572, by rfl⟩ : syracuseStep 1584773 = 297145) (by norm_num)
theorem B1191557 : Blo 702318 1191557 := bbase (se 4 (by rfl) ⟨111708, by rfl⟩ : syracuseStep 1191557 = 223417) (by norm_num)
theorem B1781453 : Blo 702318 1781453 := bbase (se 3 (by rfl) ⟨334022, by rfl⟩ : syracuseStep 1781453 = 668045) (by norm_num)
theorem B1584845 : Blo 702318 1584845 := bbase (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) (by norm_num)
theorem B1126109 : Blo 702318 1126109 := bbase (se 3 (by rfl) ⟨211145, by rfl⟩ : syracuseStep 1126109 = 422291) (by norm_num)
theorem B2371301 : Blo 702318 2371301 := bbase (se 4 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 2371301 = 444619) (by norm_num)
theorem B1191685 : Blo 702318 1191685 := bbase (se 4 (by rfl) ⟨111720, by rfl⟩ : syracuseStep 1191685 = 223441) (by norm_num)
theorem B1584917 : Blo 702318 1584917 := bbase (se 6 (by rfl) ⟨37146, by rfl⟩ : syracuseStep 1584917 = 74293) (by norm_num)
theorem B2010901 : Blo 702318 2010901 := bbase (se 6 (by rfl) ⟨47130, by rfl⟩ : syracuseStep 2010901 = 94261) (by norm_num)
theorem B1584989 : Blo 702318 1584989 := bbase (se 3 (by rfl) ⟨297185, by rfl⟩ : syracuseStep 1584989 = 594371) (by norm_num)
theorem B1191773 : Blo 702318 1191773 := bbase (se 3 (by rfl) ⟨223457, by rfl⟩ : syracuseStep 1191773 = 446915) (by norm_num)
theorem B1585061 : Blo 702318 1585061 := bbase (se 4 (by rfl) ⟨148599, by rfl⟩ : syracuseStep 1585061 = 297199) (by norm_num)
theorem B2011061 : Blo 702318 2011061 := bbase (se 5 (by rfl) ⟨94268, by rfl⟩ : syracuseStep 2011061 = 188537) (by norm_num)
theorem B1191901 : Blo 702318 1191901 := bbase (se 3 (by rfl) ⟨223481, by rfl⟩ : syracuseStep 1191901 = 446963) (by norm_num)
theorem B1585133 : Blo 702318 1585133 := bbase (se 3 (by rfl) ⟨297212, by rfl⟩ : syracuseStep 1585133 = 594425) (by norm_num)
theorem B1781797 : Blo 702318 1781797 := bbase (se 4 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 1781797 = 334087) (by norm_num)
theorem B1585205 : Blo 702318 1585205 := bbase (se 5 (by rfl) ⟨74306, by rfl⟩ : syracuseStep 1585205 = 148613) (by norm_num)
theorem B1585277 : Blo 702318 1585277 := bbase (se 3 (by rfl) ⟨297239, by rfl⟩ : syracuseStep 1585277 = 594479) (by norm_num)
theorem B2371733 : Blo 702318 2371733 := bbase (se 6 (by rfl) ⟨55587, by rfl⟩ : syracuseStep 2371733 = 111175) (by norm_num)
theorem B1781909 : Blo 702318 1781909 := bbase (se 6 (by rfl) ⟨41763, by rfl⟩ : syracuseStep 1781909 = 83527) (by norm_num)
theorem B2011301 : Blo 702318 2011301 := bbase (se 4 (by rfl) ⟨188559, by rfl⟩ : syracuseStep 2011301 = 377119) (by norm_num)
theorem B1585349 : Blo 702318 1585349 := bbase (se 4 (by rfl) ⟨148626, by rfl⟩ : syracuseStep 1585349 = 297253) (by norm_num)
theorem B1585421 : Blo 702318 1585421 := bbase (se 3 (by rfl) ⟨297266, by rfl⟩ : syracuseStep 1585421 = 594533) (by norm_num)
theorem B2666789 : Blo 702318 2666789 := bbase (se 4 (by rfl) ⟨250011, by rfl⟩ : syracuseStep 2666789 = 500023) (by norm_num)
theorem B13873493 : Blo 702318 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B1782101 : Blo 702318 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B1585493 : Blo 702318 1585493 := bbase (se 10 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 1585493 = 4645) (by norm_num)
theorem B1585565 : Blo 702318 1585565 := bbase (se 3 (by rfl) ⟨297293, by rfl⟩ : syracuseStep 1585565 = 594587) (by norm_num)
theorem B1585637 : Blo 702318 1585637 := bbase (se 4 (by rfl) ⟨148653, by rfl⟩ : syracuseStep 1585637 = 297307) (by norm_num)
theorem B1585709 : Blo 702318 1585709 := bbase (se 3 (by rfl) ⟨297320, by rfl⟩ : syracuseStep 1585709 = 594641) (by norm_num)
theorem B2667077 : Blo 702318 2667077 := bbase (se 4 (by rfl) ⟨250038, by rfl⟩ : syracuseStep 2667077 = 500077) (by norm_num)
theorem B2372165 : Blo 702318 2372165 := bbase (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) (by norm_num)
theorem B1585781 : Blo 702318 1585781 := bbase (se 5 (by rfl) ⟨74333, by rfl⟩ : syracuseStep 1585781 = 148667) (by norm_num)
theorem B1782445 : Blo 702318 1782445 := bbase (se 3 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 1782445 = 668417) (by norm_num)
theorem B1585853 : Blo 702318 1585853 := bbase (se 3 (by rfl) ⟨297347, by rfl⟩ : syracuseStep 1585853 = 594695) (by norm_num)
theorem B1585925 : Blo 702318 1585925 := bbase (se 4 (by rfl) ⟨148680, by rfl⟩ : syracuseStep 1585925 = 297361) (by norm_num)
theorem B5354261 : Blo 702318 5354261 := bbase (se 6 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 5354261 = 250981) (by norm_num)
theorem B1782557 : Blo 702318 1782557 := bbase (se 3 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 1782557 = 668459) (by norm_num)
theorem B1585997 : Blo 702318 1585997 := bbase (se 3 (by rfl) ⟨297374, by rfl⟩ : syracuseStep 1585997 = 594749) (by norm_num)
theorem B1586069 : Blo 702318 1586069 := bbase (se 6 (by rfl) ⟨37173, by rfl⟩ : syracuseStep 1586069 = 74347) (by norm_num)
theorem B1782749 : Blo 702318 1782749 := bbase (se 3 (by rfl) ⟨334265, by rfl⟩ : syracuseStep 1782749 = 668531) (by norm_num)
theorem B1586141 : Blo 702318 1586141 := bbase (se 3 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 1586141 = 594803) (by norm_num)
theorem B2372597 : Blo 702318 2372597 := bbase (se 5 (by rfl) ⟨111215, by rfl⟩ : syracuseStep 2372597 = 222431) (by norm_num)
theorem B1586213 : Blo 702318 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B1586285 : Blo 702318 1586285 := bbase (se 3 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 1586285 = 594857) (by norm_num)
theorem B1586357 : Blo 702318 1586357 := bbase (se 5 (by rfl) ⟨74360, by rfl⟩ : syracuseStep 1586357 = 148721) (by norm_num)
theorem B1127621 : Blo 702318 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B1586429 : Blo 702318 1586429 := bbase (se 3 (by rfl) ⟨297455, by rfl⟩ : syracuseStep 1586429 = 594911) (by norm_num)
theorem B1783093 : Blo 702318 1783093 := bbase (se 5 (by rfl) ⟨83582, by rfl⟩ : syracuseStep 1783093 = 167165) (by norm_num)
theorem B1586501 : Blo 702318 1586501 := bbase (se 4 (by rfl) ⟨148734, by rfl⟩ : syracuseStep 1586501 = 297469) (by norm_num)
theorem B1586573 : Blo 702318 1586573 := bbase (se 3 (by rfl) ⟨297482, by rfl⟩ : syracuseStep 1586573 = 594965) (by norm_num)
theorem B2373029 : Blo 702318 2373029 := bbase (se 4 (by rfl) ⟨222471, by rfl⟩ : syracuseStep 2373029 = 444943) (by norm_num)
theorem B1783205 : Blo 702318 1783205 := bbase (se 4 (by rfl) ⟨167175, by rfl⟩ : syracuseStep 1783205 = 334351) (by norm_num)
theorem B14464469 : Blo 702318 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B1586645 : Blo 702318 1586645 := bbase (se 7 (by rfl) ⟨18593, by rfl⟩ : syracuseStep 1586645 = 37187) (by norm_num)
theorem B1586717 : Blo 702318 1586717 := bbase (se 3 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 1586717 = 595019) (by norm_num)
theorem B1783397 : Blo 702318 1783397 := bbase (se 4 (by rfl) ⟨167193, by rfl⟩ : syracuseStep 1783397 = 334387) (by norm_num)
theorem B1586789 : Blo 702318 1586789 := bbase (se 4 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 1586789 = 297523) (by norm_num)
theorem B1128077 : Blo 702318 1128077 := bbase (se 3 (by rfl) ⟨211514, by rfl⟩ : syracuseStep 1128077 = 423029) (by norm_num)
theorem B1586861 : Blo 702318 1586861 := bbase (se 3 (by rfl) ⟨297536, by rfl⟩ : syracuseStep 1586861 = 595073) (by norm_num)
theorem B2668261 : Blo 702318 2668261 := bbase (se 4 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 2668261 = 500299) (by norm_num)
theorem B1586933 : Blo 702318 1586933 := bbase (se 5 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 1586933 = 148775) (by norm_num)
theorem B2406149 : Blo 702318 2406149 := bbase (se 4 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 2406149 = 451153) (by norm_num)
theorem B1587005 : Blo 702318 1587005 := bbase (se 3 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 1587005 = 595127) (by norm_num)
theorem B2373461 : Blo 702318 2373461 := bbase (se 9 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 2373461 = 13907) (by norm_num)
theorem B1587077 : Blo 702318 1587077 := bbase (se 4 (by rfl) ⟨148788, by rfl⟩ : syracuseStep 1587077 = 297577) (by norm_num)
theorem B2537365 : Blo 702318 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B1783741 : Blo 702318 1783741 := bbase (se 3 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 1783741 = 668903) (by norm_num)
theorem B1587149 : Blo 702318 1587149 := bbase (se 3 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 1587149 = 595181) (by norm_num)
theorem B11548693 : Blo 702318 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B2668565 : Blo 702318 2668565 := bbase (se 6 (by rfl) ⟨62544, by rfl⟩ : syracuseStep 2668565 = 125089) (by norm_num)
theorem B1587221 : Blo 702318 1587221 := bbase (se 6 (by rfl) ⟨37200, by rfl⟩ : syracuseStep 1587221 = 74401) (by norm_num)
theorem B1783853 : Blo 702318 1783853 := bbase (se 3 (by rfl) ⟨334472, by rfl⟩ : syracuseStep 1783853 = 668945) (by norm_num)
theorem B1587293 : Blo 702318 1587293 := bbase (se 3 (by rfl) ⟨297617, by rfl⟩ : syracuseStep 1587293 = 595235) (by norm_num)
theorem B9615509 : Blo 702318 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B2144405 : Blo 702318 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B1587365 : Blo 702318 1587365 := bbase (se 4 (by rfl) ⟨148815, by rfl⟩ : syracuseStep 1587365 = 297631) (by norm_num)
theorem B1784045 : Blo 702318 1784045 := bbase (se 3 (by rfl) ⟨334508, by rfl⟩ : syracuseStep 1784045 = 669017) (by norm_num)
theorem B1587437 : Blo 702318 1587437 := bbase (se 3 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 1587437 = 595289) (by norm_num)
theorem B2373893 : Blo 702318 2373893 := bbase (se 4 (by rfl) ⟨222552, by rfl⟩ : syracuseStep 2373893 = 445105) (by norm_num)
theorem B1587509 : Blo 702318 1587509 := bbase (se 5 (by rfl) ⟨74414, by rfl⟩ : syracuseStep 1587509 = 148829) (by norm_num)
theorem B1587581 : Blo 702318 1587581 := bbase (se 3 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 1587581 = 595343) (by norm_num)
theorem B1587653 : Blo 702318 1587653 := bbase (se 4 (by rfl) ⟨148842, by rfl⟩ : syracuseStep 1587653 = 297685) (by norm_num)
theorem B1587725 : Blo 702318 1587725 := bbase (se 3 (by rfl) ⟨297698, by rfl⟩ : syracuseStep 1587725 = 595397) (by norm_num)
theorem B1784389 : Blo 702318 1784389 := bbase (se 4 (by rfl) ⟨167286, by rfl⟩ : syracuseStep 1784389 = 334573) (by norm_num)
theorem B1587797 : Blo 702318 1587797 := bbase (se 8 (by rfl) ⟨9303, by rfl⟩ : syracuseStep 1587797 = 18607) (by norm_num)
theorem B1129069 : Blo 702318 1129069 := bbase (se 3 (by rfl) ⟨211700, by rfl⟩ : syracuseStep 1129069 = 423401) (by norm_num)
theorem B1587869 : Blo 702318 1587869 := bbase (se 3 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 1587869 = 595451) (by norm_num)
theorem B2374325 : Blo 702318 2374325 := bbase (se 5 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 2374325 = 222593) (by norm_num)
theorem B1784501 : Blo 702318 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B1587941 : Blo 702318 1587941 := bbase (se 4 (by rfl) ⟨148869, by rfl⟩ : syracuseStep 1587941 = 297739) (by norm_num)
theorem B801565 : Blo 702318 801565 := bbase (se 3 (by rfl) ⟨150293, by rfl⟩ : syracuseStep 801565 = 300587) (by norm_num)
theorem B3390245 : Blo 702318 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B1588013 : Blo 702318 1588013 := bbase (se 3 (by rfl) ⟨297752, by rfl⟩ : syracuseStep 1588013 = 595505) (by norm_num)
theorem B1784693 : Blo 702318 1784693 := bbase (se 5 (by rfl) ⟨83657, by rfl⟩ : syracuseStep 1784693 = 167315) (by norm_num)
theorem B1588085 : Blo 702318 1588085 := bbase (se 5 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 1588085 = 148883) (by norm_num)
theorem B1588157 : Blo 702318 1588157 := bbase (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) (by norm_num)
theorem B1588229 : Blo 702318 1588229 := bbase (se 4 (by rfl) ⟨148896, by rfl⟩ : syracuseStep 1588229 = 297793) (by norm_num)
theorem B1588301 : Blo 702318 1588301 := bbase (se 3 (by rfl) ⟨297806, by rfl⟩ : syracuseStep 1588301 = 595613) (by norm_num)
theorem B2374757 : Blo 702318 2374757 := bbase (se 4 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 2374757 = 445267) (by norm_num)
theorem B1588373 : Blo 702318 1588373 := bbase (se 6 (by rfl) ⟨37227, by rfl⟩ : syracuseStep 1588373 = 74455) (by norm_num)
theorem B1785037 : Blo 702318 1785037 := bbase (se 3 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 1785037 = 669389) (by norm_num)
theorem B1588445 : Blo 702318 1588445 := bbase (se 3 (by rfl) ⟨297833, by rfl⟩ : syracuseStep 1588445 = 595667) (by norm_num)
theorem B1129717 : Blo 702318 1129717 := bbase (se 5 (by rfl) ⟨52955, by rfl⟩ : syracuseStep 1129717 = 105911) (by norm_num)
theorem B1588517 : Blo 702318 1588517 := bbase (se 4 (by rfl) ⟨148923, by rfl⟩ : syracuseStep 1588517 = 297847) (by norm_num)
theorem B1785149 : Blo 702318 1785149 := bbase (se 3 (by rfl) ⟨334715, by rfl⟩ : syracuseStep 1785149 = 669431) (by norm_num)
theorem B11124053 : Blo 702318 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B1588589 : Blo 702318 1588589 := bbase (se 3 (by rfl) ⟨297860, by rfl⟩ : syracuseStep 1588589 = 595721) (by norm_num)
theorem B12041621 : Blo 702318 12041621 := bbase (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) (by norm_num)
theorem B1588661 : Blo 702318 1588661 := bbase (se 5 (by rfl) ⟨74468, by rfl⟩ : syracuseStep 1588661 = 148937) (by norm_num)
theorem B1785341 : Blo 702318 1785341 := bbase (se 3 (by rfl) ⟨334751, by rfl⟩ : syracuseStep 1785341 = 669503) (by norm_num)
theorem B1588733 : Blo 702318 1588733 := bbase (se 3 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 1588733 = 595775) (by norm_num)
theorem B2375189 : Blo 702318 2375189 := bbase (se 6 (by rfl) ⟨55668, by rfl⟩ : syracuseStep 2375189 = 111337) (by norm_num)
theorem B1588805 : Blo 702318 1588805 := bbase (se 4 (by rfl) ⟨148950, by rfl⟩ : syracuseStep 1588805 = 297901) (by norm_num)
theorem B2637413 : Blo 702318 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B1588877 : Blo 702318 1588877 := bbase (se 3 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 1588877 = 595829) (by norm_num)
theorem B1588949 : Blo 702318 1588949 := bbase (se 7 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 1588949 = 37241) (by norm_num)
theorem B1589021 : Blo 702318 1589021 := bbase (se 3 (by rfl) ⟨297941, by rfl⟩ : syracuseStep 1589021 = 595883) (by norm_num)
theorem B802633 : Blo 702318 802633 := bbase (se 2 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 802633 = 601975) (by norm_num)
theorem B1785685 : Blo 702318 1785685 := bbase (se 9 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 1785685 = 10463) (by norm_num)
theorem B1589093 : Blo 702318 1589093 := bbase (se 4 (by rfl) ⟨148977, by rfl⟩ : syracuseStep 1589093 = 297955) (by norm_num)
theorem B1589165 : Blo 702318 1589165 := bbase (se 3 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 1589165 = 595937) (by norm_num)
theorem B2375621 : Blo 702318 2375621 := bbase (se 4 (by rfl) ⟨222714, by rfl⟩ : syracuseStep 2375621 = 445429) (by norm_num)
theorem B1785797 : Blo 702318 1785797 := bbase (se 4 (by rfl) ⟨167418, by rfl⟩ : syracuseStep 1785797 = 334837) (by norm_num)
theorem B868357 : Blo 702318 868357 := bbase (se 4 (by rfl) ⟨81408, by rfl⟩ : syracuseStep 868357 = 162817) (by norm_num)
theorem B2670677 : Blo 702318 2670677 := bbase (se 8 (by rfl) ⟨15648, by rfl⟩ : syracuseStep 2670677 = 31297) (by norm_num)
theorem B901249 : Blo 702318 901249 := bbase (se 2 (by rfl) ⟨337968, by rfl⟩ : syracuseStep 901249 = 675937) (by norm_num)
theorem B1785989 : Blo 702318 1785989 := bbase (se 4 (by rfl) ⟨167436, by rfl⟩ : syracuseStep 1785989 = 334873) (by norm_num)
theorem B1425557 : Blo 702318 1425557 := bbase (se 6 (by rfl) ⟨33411, by rfl⟩ : syracuseStep 1425557 = 66823) (by norm_num)
theorem B1130645 : Blo 702318 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B1425605 : Blo 702318 1425605 := bbase (se 4 (by rfl) ⟨133650, by rfl⟩ : syracuseStep 1425605 = 267301) (by norm_num)
theorem B1524077 : Blo 702318 1524077 := bbase (se 3 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 1524077 = 571529) (by norm_num)
theorem B2670965 : Blo 702318 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B2376053 : Blo 702318 2376053 := bbase (se 5 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 2376053 = 222755) (by norm_num)
theorem B2539973 : Blo 702318 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B1786333 : Blo 702318 1786333 := bbase (se 3 (by rfl) ⟨334937, by rfl⟩ : syracuseStep 1786333 = 669875) (by norm_num)
theorem B901649 : Blo 702318 901649 := bbase (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) (by norm_num)
theorem B1688125 : Blo 702318 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B1786445 : Blo 702318 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B1131101 : Blo 702318 1131101 := bbase (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) (by norm_num)
theorem B3424949 : Blo 702318 3424949 := bbase (se 5 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 3424949 = 321089) (by norm_num)
theorem B2540261 : Blo 702318 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B803569 : Blo 702318 803569 := bbase (se 2 (by rfl) ⟨301338, by rfl⟩ : syracuseStep 803569 = 602677) (by norm_num)
theorem B1786637 : Blo 702318 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B1688357 : Blo 702318 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B2376485 : Blo 702318 2376485 := bbase (se 4 (by rfl) ⟨222795, by rfl⟩ : syracuseStep 2376485 = 445591) (by norm_num)
theorem B1688501 : Blo 702318 1688501 := bbase (se 5 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 1688501 = 158297) (by norm_num)
theorem B1786981 : Blo 702318 1786981 := bbase (se 4 (by rfl) ⟨167529, by rfl⟩ : syracuseStep 1786981 = 335059) (by norm_num)
theorem B1688741 : Blo 702318 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B1000621 : Blo 702318 1000621 := bbase (se 3 (by rfl) ⟨187616, by rfl⟩ : syracuseStep 1000621 = 375233) (by norm_num)
theorem B2376917 : Blo 702318 2376917 := bbase (se 7 (by rfl) ⟨27854, by rfl⟩ : syracuseStep 2376917 = 55709) (by norm_num)
theorem B1787093 : Blo 702318 1787093 := bbase (se 7 (by rfl) ⟨20942, by rfl⟩ : syracuseStep 1787093 = 41885) (by norm_num)
theorem B3556709 : Blo 702318 3556709 := bbase (se 4 (by rfl) ⟨333441, by rfl⟩ : syracuseStep 3556709 = 666883) (by norm_num)
theorem B4506997 : Blo 702318 4506997 := bbase (se 5 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 4506997 = 422531) (by norm_num)
theorem B1787285 : Blo 702318 1787285 := bbase (se 6 (by rfl) ⟨41889, by rfl⟩ : syracuseStep 1787285 = 83779) (by norm_num)
theorem B2672149 : Blo 702318 2672149 := bbase (se 6 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 2672149 = 125257) (by norm_num)
theorem B804449 : Blo 702318 804449 := bbase (se 2 (by rfl) ⟨301668, by rfl⟩ : syracuseStep 804449 = 603337) (by norm_num)
theorem B2377349 : Blo 702318 2377349 := bbase (se 4 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 2377349 = 445753) (by norm_num)
theorem B1787629 : Blo 702318 1787629 := bbase (se 3 (by rfl) ⟨335180, by rfl⟩ : syracuseStep 1787629 = 670361) (by norm_num)
theorem B4015925 : Blo 702318 4015925 := bbase (se 5 (by rfl) ⟨188246, by rfl⟩ : syracuseStep 4015925 = 376493) (by norm_num)
theorem B2672453 : Blo 702318 2672453 := bbase (se 4 (by rfl) ⟨250542, by rfl⟩ : syracuseStep 2672453 = 501085) (by norm_num)
theorem B1787741 : Blo 702318 1787741 := bbase (se 3 (by rfl) ⟨335201, by rfl⟩ : syracuseStep 1787741 = 670403) (by norm_num)
theorem B1689509 : Blo 702318 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B1001413 : Blo 702318 1001413 := bbase (se 4 (by rfl) ⟨93882, by rfl⟩ : syracuseStep 1001413 = 187765) (by norm_num)
theorem B2377781 : Blo 702318 2377781 := bbase (se 5 (by rfl) ⟨111458, by rfl⟩ : syracuseStep 2377781 = 222917) (by norm_num)
theorem B12863573 : Blo 702318 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B1001749 : Blo 702318 1001749 := bbase (se 6 (by rfl) ⟨23478, by rfl⟩ : syracuseStep 1001749 = 46957) (by norm_num)
theorem B903485 : Blo 702318 903485 := bbase (se 3 (by rfl) ⟨169403, by rfl⟩ : syracuseStep 903485 = 338807) (by norm_num)
theorem B1427861 : Blo 702318 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B2378213 : Blo 702318 2378213 := bbase (se 4 (by rfl) ⟨222957, by rfl⟩ : syracuseStep 2378213 = 445915) (by norm_num)
theorem B1001965 : Blo 702318 1001965 := bbase (se 3 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 1001965 = 375737) (by norm_num)
theorem B805433 : Blo 702318 805433 := bbase (se 2 (by rfl) ⟨302037, by rfl⟩ : syracuseStep 805433 = 604075) (by norm_num)
theorem B3558005 : Blo 702318 3558005 := bbase (se 5 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 3558005 = 333563) (by norm_num)
theorem B1592045 : Blo 702318 1592045 := bbase (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) (by norm_num)
theorem B1002341 : Blo 702318 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B2378645 : Blo 702318 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B1428509 : Blo 702318 1428509 := bbase (se 3 (by rfl) ⟨267845, by rfl⟩ : syracuseStep 1428509 = 535691) (by norm_num)
theorem B1690885 : Blo 702318 1690885 := bbase (se 4 (by rfl) ⟨158520, by rfl⟩ : syracuseStep 1690885 = 317041) (by norm_num)
theorem B2379077 : Blo 702318 2379077 := bbase (se 4 (by rfl) ⟨223038, by rfl⟩ : syracuseStep 2379077 = 446077) (by norm_num)
theorem B904717 : Blo 702318 904717 := bbase (se 3 (by rfl) ⟨169634, by rfl⟩ : syracuseStep 904717 = 339269) (by norm_num)
theorem B1429157 : Blo 702318 1429157 := bbase (se 4 (by rfl) ⟨133983, by rfl⟩ : syracuseStep 1429157 = 267967) (by norm_num)
theorem B2379509 : Blo 702318 2379509 := bbase (se 5 (by rfl) ⟨111539, by rfl⟩ : syracuseStep 2379509 = 223079) (by norm_num)
theorem B905045 : Blo 702318 905045 := bbase (se 9 (by rfl) ⟨2651, by rfl⟩ : syracuseStep 905045 = 5303) (by norm_num)
theorem B3559301 : Blo 702318 3559301 := bbase (se 4 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 3559301 = 667369) (by norm_num)
theorem B2674565 : Blo 702318 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B3002341 : Blo 702318 3002341 := bbase (se 4 (by rfl) ⟨281469, by rfl⟩ : syracuseStep 3002341 = 562939) (by norm_num)
theorem B8572949 : Blo 702318 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B2674853 : Blo 702318 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B2379941 : Blo 702318 2379941 := bbase (se 4 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 2379941 = 446239) (by norm_num)
theorem B1003765 : Blo 702318 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B5067029 : Blo 702318 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B1429805 : Blo 702318 1429805 := bbase (se 3 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 1429805 = 536177) (by norm_num)
theorem B5362037 : Blo 702318 5362037 := bbase (se 5 (by rfl) ⟨251345, by rfl⟩ : syracuseStep 5362037 = 502691) (by norm_num)
theorem B1692085 : Blo 702318 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B2380373 : Blo 702318 2380373 := bbase (se 8 (by rfl) ⟨13947, by rfl⟩ : syracuseStep 2380373 = 27895) (by norm_num)
theorem B2708117 : Blo 702318 2708117 := bbase (se 6 (by rfl) ⟨63471, by rfl⟩ : syracuseStep 2708117 = 126943) (by norm_num)
theorem B1430293 : Blo 702318 1430293 := bbase (se 6 (by rfl) ⟨33522, by rfl⟩ : syracuseStep 1430293 = 67045) (by norm_num)
theorem B1004357 : Blo 702318 1004357 := bbase (se 4 (by rfl) ⟨94158, by rfl⟩ : syracuseStep 1004357 = 188317) (by norm_num)
theorem B1004437 : Blo 702318 1004437 := bbase (se 6 (by rfl) ⟨23541, by rfl⟩ : syracuseStep 1004437 = 47083) (by norm_num)
theorem B2380805 : Blo 702318 2380805 := bbase (se 4 (by rfl) ⟨223200, by rfl⟩ : syracuseStep 2380805 = 446401) (by norm_num)
theorem B1070093 : Blo 702318 1070093 := bbase (se 3 (by rfl) ⟨200642, by rfl⟩ : syracuseStep 1070093 = 401285) (by norm_num)
theorem B1004557 : Blo 702318 1004557 := bbase (se 3 (by rfl) ⟨188354, by rfl⟩ : syracuseStep 1004557 = 376709) (by norm_num)
theorem B1692701 : Blo 702318 1692701 := bbase (se 3 (by rfl) ⟨317381, by rfl⟩ : syracuseStep 1692701 = 634763) (by norm_num)
theorem B1004653 : Blo 702318 1004653 := bbase (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) (by norm_num)
theorem B3560597 : Blo 702318 3560597 := bbase (se 6 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 3560597 = 166903) (by norm_num)
theorem B1692893 : Blo 702318 1692893 := bbase (se 3 (by rfl) ⟨317417, by rfl⟩ : syracuseStep 1692893 = 634835) (by norm_num)
theorem B4510997 : Blo 702318 4510997 := bbase (se 6 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 4510997 = 211453) (by norm_num)
theorem B1692989 : Blo 702318 1692989 := bbase (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) (by norm_num)
theorem B2676037 : Blo 702318 2676037 := bbase (se 4 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 2676037 = 501757) (by norm_num)
theorem B2315621 : Blo 702318 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B2413925 : Blo 702318 2413925 := bbase (se 4 (by rfl) ⟨226305, by rfl⟩ : syracuseStep 2413925 = 452611) (by norm_num)
theorem B2381237 : Blo 702318 2381237 := bbase (se 5 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 2381237 = 223241) (by norm_num)
theorem B1005149 : Blo 702318 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B2676341 : Blo 702318 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B1070725 : Blo 702318 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B2381669 : Blo 702318 2381669 := bbase (se 4 (by rfl) ⟨223281, by rfl⟩ : syracuseStep 2381669 = 446563) (by norm_num)
theorem B2250629 : Blo 702318 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B2709413 : Blo 702318 2709413 := bbase (se 4 (by rfl) ⟨254007, by rfl⟩ : syracuseStep 2709413 = 508015) (by norm_num)
theorem B2414549 : Blo 702318 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B2250757 : Blo 702318 2250757 := bbase (se 4 (by rfl) ⟨211008, by rfl⟩ : syracuseStep 2250757 = 422017) (by norm_num)
theorem B2414645 : Blo 702318 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B1333493 : Blo 702318 1333493 := bbase (se 5 (by rfl) ⟨62507, by rfl⟩ : syracuseStep 1333493 = 125015) (by norm_num)
theorem B2382101 : Blo 702318 2382101 := bbase (se 6 (by rfl) ⟨55830, by rfl⟩ : syracuseStep 2382101 = 111661) (by norm_num)
theorem B3561893 : Blo 702318 3561893 := bbase (se 4 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 3561893 = 667855) (by norm_num)
theorem B1268141 : Blo 702318 1268141 := bbase (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) (by norm_num)
theorem B1268221 : Blo 702318 1268221 := bbase (se 3 (by rfl) ⟨237791, by rfl⟩ : syracuseStep 1268221 = 475583) (by norm_num)
theorem B2447941 : Blo 702318 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B6085205 : Blo 702318 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B2382533 : Blo 702318 2382533 := bbase (se 4 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 2382533 = 446725) (by norm_num)
theorem B1268453 : Blo 702318 1268453 := bbase (se 4 (by rfl) ⟨118917, by rfl⟩ : syracuseStep 1268453 = 237835) (by norm_num)
theorem B3005333 : Blo 702318 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B1334245 : Blo 702318 1334245 := bbase (se 4 (by rfl) ⟨125085, by rfl⟩ : syracuseStep 1334245 = 250171) (by norm_num)
theorem B1334389 : Blo 702318 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B2382965 : Blo 702318 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B2415781 : Blo 702318 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1072397 : Blo 702318 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B1334549 : Blo 702318 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B712081 : Blo 702318 712081 := bbase (se 2 (by rfl) ⟨267030, by rfl⟩ : syracuseStep 712081 = 534061) (by norm_num)
theorem B1072549 : Blo 702318 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B1334693 : Blo 702318 1334693 := bbase (se 4 (by rfl) ⟨125127, by rfl⟩ : syracuseStep 1334693 = 250255) (by norm_num)
theorem B3431909 : Blo 702318 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B2383397 : Blo 702318 2383397 := bbase (se 4 (by rfl) ⟨223443, by rfl⟩ : syracuseStep 2383397 = 446887) (by norm_num)
theorem B3563189 : Blo 702318 3563189 := bbase (se 5 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 3563189 = 334049) (by norm_num)
theorem B2678453 : Blo 702318 2678453 := bbase (se 5 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 2678453 = 251105) (by norm_num)
theorem B1695421 : Blo 702318 1695421 := bbase (se 3 (by rfl) ⟨317891, by rfl⟩ : syracuseStep 1695421 = 635783) (by norm_num)
theorem B1334981 : Blo 702318 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B1335133 : Blo 702318 1335133 := bbase (se 3 (by rfl) ⟨250337, by rfl⟩ : syracuseStep 1335133 = 500675) (by norm_num)
theorem B1269605 : Blo 702318 1269605 := bbase (se 4 (by rfl) ⟨119025, by rfl⟩ : syracuseStep 1269605 = 238051) (by norm_num)
theorem B3006341 : Blo 702318 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B1269685 : Blo 702318 1269685 := bbase (se 5 (by rfl) ⟨59516, by rfl⟩ : syracuseStep 1269685 = 119033) (by norm_num)
theorem B2678741 : Blo 702318 2678741 := bbase (se 7 (by rfl) ⟨31391, by rfl⟩ : syracuseStep 2678741 = 62783) (by norm_num)
theorem B712681 : Blo 702318 712681 := bbase (se 2 (by rfl) ⟨267255, by rfl⟩ : syracuseStep 712681 = 534511) (by norm_num)
theorem B712697 : Blo 702318 712697 := bbase (se 2 (by rfl) ⟨267261, by rfl⟩ : syracuseStep 712697 = 534523) (by norm_num)
theorem B1695757 : Blo 702318 1695757 := bbase (se 3 (by rfl) ⟨317954, by rfl⟩ : syracuseStep 1695757 = 635909) (by norm_num)
theorem B1925141 : Blo 702318 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B843905 : Blo 702318 843905 := bbase (se 2 (by rfl) ⟨316464, by rfl⟩ : syracuseStep 843905 = 632929) (by norm_num)
theorem B1335437 : Blo 702318 1335437 := bbase (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) (by norm_num)
theorem B5726485 : Blo 702318 5726485 := bbase (se 6 (by rfl) ⟨134214, by rfl⟩ : syracuseStep 5726485 = 268429) (by norm_num)
theorem B1696373 : Blo 702318 1696373 := bbase (se 5 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 1696373 = 159035) (by norm_num)
theorem B2253653 : Blo 702318 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1631069 : Blo 702318 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B1336189 : Blo 702318 1336189 := bbase (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) (by norm_num)
theorem B1500077 : Blo 702318 1500077 := bbase (se 3 (by rfl) ⟨281264, by rfl⟩ : syracuseStep 1500077 = 562529) (by norm_num)
theorem B3564485 : Blo 702318 3564485 := bbase (se 4 (by rfl) ⟨334170, by rfl⟩ : syracuseStep 3564485 = 668341) (by norm_num)
theorem B1270765 : Blo 702318 1270765 := bbase (se 3 (by rfl) ⟨238268, by rfl⟩ : syracuseStep 1270765 = 476537) (by norm_num)
theorem B1336333 : Blo 702318 1336333 := bbase (se 3 (by rfl) ⟨250562, by rfl⟩ : syracuseStep 1336333 = 501125) (by norm_num)
theorem B1696805 : Blo 702318 1696805 := bbase (se 4 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 1696805 = 318151) (by norm_num)
theorem B2679925 : Blo 702318 2679925 := bbase (se 5 (by rfl) ⟨125621, by rfl⟩ : syracuseStep 2679925 = 251243) (by norm_num)
theorem B1270909 : Blo 702318 1270909 := bbase (se 3 (by rfl) ⟨238295, by rfl⟩ : syracuseStep 1270909 = 476591) (by norm_num)
theorem B1336493 : Blo 702318 1336493 := bbase (se 3 (by rfl) ⟨250592, by rfl⟩ : syracuseStep 1336493 = 501185) (by norm_num)
theorem B1500437 : Blo 702318 1500437 := bbase (se 6 (by rfl) ⟨35166, by rfl⟩ : syracuseStep 1500437 = 70333) (by norm_num)
theorem B1271069 : Blo 702318 1271069 := bbase (se 3 (by rfl) ⟨238325, by rfl⟩ : syracuseStep 1271069 = 476651) (by norm_num)
theorem B845101 : Blo 702318 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B1336637 : Blo 702318 1336637 := bbase (se 3 (by rfl) ⟨250619, by rfl⟩ : syracuseStep 1336637 = 501239) (by norm_num)
theorem B30532949 : Blo 702318 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B845173 : Blo 702318 845173 := bbase (se 5 (by rfl) ⟨39617, by rfl⟩ : syracuseStep 845173 = 79235) (by norm_num)
theorem B2680229 : Blo 702318 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B1336925 : Blo 702318 1336925 := bbase (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) (by norm_num)
theorem B3008117 : Blo 702318 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B1762973 : Blo 702318 1762973 := bbase (se 3 (by rfl) ⟨330557, by rfl⟩ : syracuseStep 1762973 = 661115) (by norm_num)
theorem B1337077 : Blo 702318 1337077 := bbase (se 5 (by rfl) ⟨62675, by rfl⟩ : syracuseStep 1337077 = 125351) (by norm_num)
theorem B1337381 : Blo 702318 1337381 := bbase (se 4 (by rfl) ⟨125379, by rfl⟩ : syracuseStep 1337381 = 250759) (by norm_num)
theorem B1501325 : Blo 702318 1501325 := bbase (se 3 (by rfl) ⟨281498, by rfl⟩ : syracuseStep 1501325 = 562997) (by norm_num)
theorem B3565781 : Blo 702318 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B714997 : Blo 702318 714997 := bbase (se 5 (by rfl) ⟨33515, by rfl⟩ : syracuseStep 714997 = 67031) (by norm_num)
theorem B846173 : Blo 702318 846173 := bbase (se 3 (by rfl) ⟨158657, by rfl⟩ : syracuseStep 846173 = 317315) (by norm_num)
theorem B1501573 : Blo 702318 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B3467669 : Blo 702318 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B715321 : Blo 702318 715321 := bbase (se 2 (by rfl) ⟨268245, by rfl⟩ : syracuseStep 715321 = 536491) (by norm_num)
theorem B1338133 : Blo 702318 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B1502077 : Blo 702318 1502077 := bbase (se 3 (by rfl) ⟨281639, by rfl⟩ : syracuseStep 1502077 = 563279) (by norm_num)
theorem B715649 : Blo 702318 715649 := bbase (se 2 (by rfl) ⟨268368, by rfl⟩ : syracuseStep 715649 = 536737) (by norm_num)
theorem B715681 : Blo 702318 715681 := bbase (se 2 (by rfl) ⟨268380, by rfl⟩ : syracuseStep 715681 = 536761) (by norm_num)
theorem B1338277 : Blo 702318 1338277 := bbase (se 4 (by rfl) ⟨125463, by rfl⟩ : syracuseStep 1338277 = 250927) (by norm_num)
theorem B3206101 : Blo 702318 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B2255845 : Blo 702318 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B846865 : Blo 702318 846865 := bbase (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) (by norm_num)
theorem B846869 : Blo 702318 846869 := bbase (se 6 (by rfl) ⟨19848, by rfl⟩ : syracuseStep 846869 = 39697) (by norm_num)
theorem B1338437 : Blo 702318 1338437 := bbase (se 4 (by rfl) ⟨125478, by rfl⟩ : syracuseStep 1338437 = 250957) (by norm_num)
theorem B1174637 : Blo 702318 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B715925 : Blo 702318 715925 := bbase (se 6 (by rfl) ⟨16779, by rfl⟩ : syracuseStep 715925 = 33559) (by norm_num)
theorem B4517045 : Blo 702318 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B1338581 : Blo 702318 1338581 := bbase (se 7 (by rfl) ⟨15686, by rfl⟩ : syracuseStep 1338581 = 31373) (by norm_num)
theorem B3042613 : Blo 702318 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B3567077 : Blo 702318 3567077 := bbase (se 4 (by rfl) ⟨334413, by rfl⟩ : syracuseStep 3567077 = 668827) (by norm_num)
theorem B1338869 : Blo 702318 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B847369 : Blo 702318 847369 := bbase (se 2 (by rfl) ⟨317763, by rfl⟩ : syracuseStep 847369 = 635527) (by norm_num)
theorem B1339021 : Blo 702318 1339021 := bbase (se 3 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 1339021 = 502133) (by norm_num)
theorem B1502965 : Blo 702318 1502965 := bbase (se 5 (by rfl) ⟨70451, by rfl⟩ : syracuseStep 1502965 = 140903) (by norm_num)
theorem B2256677 : Blo 702318 2256677 := bbase (se 4 (by rfl) ⟨211563, by rfl⟩ : syracuseStep 2256677 = 423127) (by norm_num)
theorem B847753 : Blo 702318 847753 := bbase (se 2 (by rfl) ⟨317907, by rfl⟩ : syracuseStep 847753 = 635815) (by norm_num)
theorem B1339325 : Blo 702318 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B913369 : Blo 702318 913369 := bbase (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) (by norm_num)
theorem B1503461 : Blo 702318 1503461 := bbase (se 4 (by rfl) ⟨140949, by rfl⟩ : syracuseStep 1503461 = 281899) (by norm_num)
theorem B1340077 : Blo 702318 1340077 := bbase (se 3 (by rfl) ⟨251264, by rfl⟩ : syracuseStep 1340077 = 502529) (by norm_num)
theorem B2716357 : Blo 702318 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B3568373 : Blo 702318 3568373 := bbase (se 5 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 3568373 = 334535) (by norm_num)
theorem B1176325 : Blo 702318 1176325 := bbase (se 4 (by rfl) ⟨110280, by rfl⟩ : syracuseStep 1176325 = 220561) (by norm_num)
theorem B750389 : Blo 702318 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B1340221 : Blo 702318 1340221 := bbase (se 3 (by rfl) ⟨251291, by rfl⟩ : syracuseStep 1340221 = 502583) (by norm_num)
theorem B1340381 : Blo 702318 1340381 := bbase (se 3 (by rfl) ⟨251321, by rfl⟩ : syracuseStep 1340381 = 502643) (by norm_num)
theorem B750637 : Blo 702318 750637 := bbase (se 3 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 750637 = 281489) (by norm_num)
theorem B1504349 : Blo 702318 1504349 := bbase (se 3 (by rfl) ⟨282065, by rfl⟩ : syracuseStep 1504349 = 564131) (by norm_num)
theorem B1340525 : Blo 702318 1340525 := bbase (se 3 (by rfl) ⟨251348, by rfl⟩ : syracuseStep 1340525 = 502697) (by norm_num)
theorem B3798197 : Blo 702318 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B1504469 : Blo 702318 1504469 := bbase (se 7 (by rfl) ⟨17630, by rfl⟩ : syracuseStep 1504469 = 35261) (by norm_num)
theorem B1340813 : Blo 702318 1340813 := bbase (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) (by norm_num)
theorem B751081 : Blo 702318 751081 := bbase (se 2 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 751081 = 563311) (by norm_num)
theorem B751141 : Blo 702318 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B5338709 : Blo 702318 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B2258549 : Blo 702318 2258549 := bbase (se 5 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 2258549 = 211739) (by norm_num)
theorem B1603205 : Blo 702318 1603205 := bbase (se 4 (by rfl) ⟨150300, by rfl⟩ : syracuseStep 1603205 = 300601) (by norm_num)
theorem B3012389 : Blo 702318 3012389 := bbase (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) (by norm_num)
theorem B1505101 : Blo 702318 1505101 := bbase (se 3 (by rfl) ⟨282206, by rfl⟩ : syracuseStep 1505101 = 564413) (by norm_num)
theorem B751457 : Blo 702318 751457 := bbase (se 2 (by rfl) ⟨281796, by rfl⟩ : syracuseStep 751457 = 563593) (by norm_num)
theorem B3569669 : Blo 702318 3569669 := bbase (se 4 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 3569669 = 669313) (by norm_num)
theorem B9140309 : Blo 702318 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B751901 : Blo 702318 751901 := bbase (se 3 (by rfl) ⟨140981, by rfl⟩ : syracuseStep 751901 = 281963) (by norm_num)
theorem B1603925 : Blo 702318 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B751961 : Blo 702318 751961 := bbase (se 2 (by rfl) ⟨281985, by rfl⟩ : syracuseStep 751961 = 563971) (by norm_num)
theorem B2685349 : Blo 702318 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B752089 : Blo 702318 752089 := bbase (se 2 (by rfl) ⟨282033, by rfl⟩ : syracuseStep 752089 = 564067) (by norm_num)
theorem B1505989 : Blo 702318 1505989 := bbase (se 4 (by rfl) ⟨141186, by rfl⟩ : syracuseStep 1505989 = 282373) (by norm_num)
theorem B8583893 : Blo 702318 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B1506109 : Blo 702318 1506109 := bbase (se 3 (by rfl) ⟨282395, by rfl⟩ : syracuseStep 1506109 = 564791) (by norm_num)
theorem B752533 : Blo 702318 752533 := bbase (se 6 (by rfl) ⟨17637, by rfl⟩ : syracuseStep 752533 = 35275) (by norm_num)
theorem B752653 : Blo 702318 752653 := bbase (se 3 (by rfl) ⟨141122, by rfl⟩ : syracuseStep 752653 = 282245) (by norm_num)
theorem B1506365 : Blo 702318 1506365 := bbase (se 3 (by rfl) ⟨282443, by rfl⟩ : syracuseStep 1506365 = 564887) (by norm_num)
theorem B752905 : Blo 702318 752905 := bbase (se 2 (by rfl) ⟨282339, by rfl⟩ : syracuseStep 752905 = 564679) (by norm_num)
theorem B752909 : Blo 702318 752909 := bbase (se 3 (by rfl) ⟨141170, by rfl⟩ : syracuseStep 752909 = 282341) (by norm_num)
theorem B3570965 : Blo 702318 3570965 := bbase (se 6 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 3570965 = 167389) (by norm_num)
theorem B3014165 : Blo 702318 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B3014405 : Blo 702318 3014405 := bbase (se 4 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 3014405 = 565201) (by norm_num)
theorem B753473 : Blo 702318 753473 := bbase (se 2 (by rfl) ⟨282552, by rfl⟩ : syracuseStep 753473 = 565105) (by norm_num)
theorem B1507253 : Blo 702318 1507253 := bbase (se 5 (by rfl) ⟨70652, by rfl⟩ : syracuseStep 1507253 = 141305) (by norm_num)
theorem B753661 : Blo 702318 753661 := bbase (se 3 (by rfl) ⟨141311, by rfl⟩ : syracuseStep 753661 = 282623) (by norm_num)
theorem B2261009 : Blo 702318 2261009 := bstep (se 2 (by rfl) ⟨847878, by rfl⟩ : syracuseStep 2261009 = 1695757) B1695757
theorem B1016051 : Blo 702318 1016051 := bstep (se 1 (by rfl) ⟨762038, by rfl⟩ : syracuseStep 1016051 = 1524077) B1524077
theorem B7635313 : Blo 702318 7635313 := bstep (se 2 (by rfl) ⟨2863242, by rfl⟩ : syracuseStep 7635313 = 5726485) B5726485
theorem B3801485 : Blo 702318 3801485 := bstep (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) B1425557
theorem B3015053 : Blo 702318 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B754067 : Blo 702318 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B4063651 : Blo 702318 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B3015089 : Blo 702318 3015089 := bstep (se 2 (by rfl) ⟨1130658, by rfl⟩ : syracuseStep 3015089 = 2261317) B2261317
theorem B6030449 : Blo 702318 6030449 := bstep (se 2 (by rfl) ⟨2261418, by rfl⟩ : syracuseStep 6030449 = 4522837) B4522837
theorem B6423907 : Blo 702318 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B1901987 : Blo 702318 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B1017265 : Blo 702318 1017265 := bstep (se 2 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 1017265 = 762949) B762949
theorem B3573233 : Blo 702318 3573233 := bstep (se 2 (by rfl) ⟨1339962, by rfl⟩ : syracuseStep 3573233 = 2679925) B2679925
theorem B4687409 : Blo 702318 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B951907 : Blo 702318 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B952339 : Blo 702318 952339 := bstep (se 1 (by rfl) ⟨714254, by rfl⟩ : syracuseStep 952339 = 1428509) B1428509
theorem B15206453 : Blo 702318 15206453 := bstep (se 5 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 15206453 = 1425605) B1425605
theorem B2001037 : Blo 702318 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B1018049 : Blo 702318 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B952771 : Blo 702318 952771 := bstep (se 1 (by rfl) ⟨714578, by rfl⟩ : syracuseStep 952771 = 1429157) B1429157
theorem B4000205 : Blo 702318 4000205 := bstep (se 3 (by rfl) ⟨750038, by rfl⟩ : syracuseStep 4000205 = 1500077) B1500077
theorem B4524835 : Blo 702318 4524835 := bstep (se 1 (by rfl) ⟨3393626, by rfl⟩ : syracuseStep 4524835 = 6787253) B6787253
theorem B4295501 : Blo 702318 4295501 := bstep (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) B1610813
theorem B3378019 : Blo 702318 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B3574691 : Blo 702318 3574691 := bstep (se 1 (by rfl) ⟨2681018, by rfl⟩ : syracuseStep 3574691 = 5362037) B5362037
theorem B1805411 : Blo 702318 1805411 := bstep (se 1 (by rfl) ⟨1354058, by rfl⟩ : syracuseStep 1805411 = 2708117) B2708117
theorem B3083405 : Blo 702318 3083405 := bstep (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) B1156277
theorem B2002097 : Blo 702318 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B1543747 : Blo 702318 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B1609283 : Blo 702318 1609283 := bstep (se 1 (by rfl) ⟨1206962, by rfl⟩ : syracuseStep 1609283 = 2413925) B2413925
theorem B855715 : Blo 702318 855715 := bstep (se 1 (by rfl) ⟨641786, by rfl⟩ : syracuseStep 855715 = 1283573) B1283573
theorem B790195 : Blo 702318 790195 := bstep (se 1 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 790195 = 1185293) B1185293
theorem B1904323 : Blo 702318 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B3575501 : Blo 702318 3575501 := bstep (se 3 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 3575501 = 1340813) B1340813
theorem B790339 : Blo 702318 790339 := bstep (se 1 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 790339 = 1185509) B1185509
theorem B2002769 : Blo 702318 2002769 := bstep (se 2 (by rfl) ⟨751038, by rfl⟩ : syracuseStep 2002769 = 1502077) B1502077
theorem B1806275 : Blo 702318 1806275 := bstep (se 1 (by rfl) ⟨1354706, by rfl⟩ : syracuseStep 1806275 = 2709413) B2709413
theorem B6000581 : Blo 702318 6000581 := bstep (se 4 (by rfl) ⟨562554, by rfl⟩ : syracuseStep 6000581 = 1125109) B1125109
theorem B11407301 : Blo 702318 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B790483 : Blo 702318 790483 := bstep (se 1 (by rfl) ⟨592862, by rfl⟩ : syracuseStep 790483 = 1185725) B1185725
theorem B1609699 : Blo 702318 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B1609763 : Blo 702318 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B3379249 : Blo 702318 3379249 := bstep (se 2 (by rfl) ⟨1267218, by rfl⟩ : syracuseStep 3379249 = 2534437) B2534437
theorem B790627 : Blo 702318 790627 := bstep (se 1 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 790627 = 1185941) B1185941
theorem B888995 : Blo 702318 888995 := bstep (se 1 (by rfl) ⟨666746, by rfl⟩ : syracuseStep 888995 = 1333493) B1333493
theorem B790771 : Blo 702318 790771 := bstep (se 1 (by rfl) ⟨593078, by rfl⟩ : syracuseStep 790771 = 1186157) B1186157
theorem B725347 : Blo 702318 725347 := bstep (se 1 (by rfl) ⟨544010, by rfl⟩ : syracuseStep 725347 = 1088021) B1088021
theorem B790915 : Blo 702318 790915 := bstep (se 1 (by rfl) ⟨593186, by rfl⟩ : syracuseStep 790915 = 1186373) B1186373
theorem B791059 : Blo 702318 791059 := bstep (se 1 (by rfl) ⟨593294, by rfl⟩ : syracuseStep 791059 = 1186589) B1186589
theorem B2003555 : Blo 702318 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B791203 : Blo 702318 791203 := bstep (se 1 (by rfl) ⟨593402, by rfl⟩ : syracuseStep 791203 = 1186805) B1186805
theorem B9638597 : Blo 702318 9638597 := bstep (se 4 (by rfl) ⟨903618, by rfl⟩ : syracuseStep 9638597 = 1807237) B1807237
theorem B1053491 : Blo 702318 1053491 := bstep (se 1 (by rfl) ⟨790118, by rfl⟩ : syracuseStep 1053491 = 1580237) B1580237
theorem B791347 : Blo 702318 791347 := bstep (se 1 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 791347 = 1187021) B1187021
theorem B1053521 : Blo 702318 1053521 := bstep (se 2 (by rfl) ⟨395070, by rfl⟩ : syracuseStep 1053521 = 790141) B790141
theorem B1053539 : Blo 702318 1053539 := bstep (se 1 (by rfl) ⟨790154, by rfl⟩ : syracuseStep 1053539 = 1580309) B1580309
theorem B889699 : Blo 702318 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B1053569 : Blo 702318 1053569 := bstep (se 2 (by rfl) ⟨395088, by rfl⟩ : syracuseStep 1053569 = 790177) B790177
theorem B1053587 : Blo 702318 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B2003885 : Blo 702318 2003885 := bstep (se 3 (by rfl) ⟨375728, by rfl⟩ : syracuseStep 2003885 = 751457) B751457
theorem B1053617 : Blo 702318 1053617 := bstep (se 2 (by rfl) ⟨395106, by rfl⟩ : syracuseStep 1053617 = 790213) B790213
theorem B1053635 : Blo 702318 1053635 := bstep (se 1 (by rfl) ⟨790226, by rfl⟩ : syracuseStep 1053635 = 1580453) B1580453
theorem B889795 : Blo 702318 889795 := bstep (se 1 (by rfl) ⟨667346, by rfl⟩ : syracuseStep 889795 = 1334693) B1334693
theorem B791491 : Blo 702318 791491 := bstep (se 1 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 791491 = 1187237) B1187237
theorem B1053665 : Blo 702318 1053665 := bstep (se 2 (by rfl) ⟨395124, by rfl⟩ : syracuseStep 1053665 = 790249) B790249
theorem B2003953 : Blo 702318 2003953 := bstep (se 2 (by rfl) ⟨751482, by rfl⟩ : syracuseStep 2003953 = 1502965) B1502965
theorem B1053683 : Blo 702318 1053683 := bstep (se 1 (by rfl) ⟨790262, by rfl⟩ : syracuseStep 1053683 = 1580525) B1580525
theorem B1053713 : Blo 702318 1053713 := bstep (se 2 (by rfl) ⟨395142, by rfl⟩ : syracuseStep 1053713 = 790285) B790285
theorem B1053731 : Blo 702318 1053731 := bstep (se 1 (by rfl) ⟨790298, by rfl⟩ : syracuseStep 1053731 = 1580597) B1580597
theorem B1053761 : Blo 702318 1053761 := bstep (se 2 (by rfl) ⟨395160, by rfl⟩ : syracuseStep 1053761 = 790321) B790321
theorem B1053779 : Blo 702318 1053779 := bstep (se 1 (by rfl) ⟨790334, by rfl⟩ : syracuseStep 1053779 = 1580669) B1580669
theorem B791635 : Blo 702318 791635 := bstep (se 1 (by rfl) ⟨593726, by rfl⟩ : syracuseStep 791635 = 1187453) B1187453
theorem B1053809 : Blo 702318 1053809 := bstep (se 2 (by rfl) ⟨395178, by rfl⟩ : syracuseStep 1053809 = 790357) B790357
theorem B1053827 : Blo 702318 1053827 := bstep (se 1 (by rfl) ⟨790370, by rfl⟩ : syracuseStep 1053827 = 1580741) B1580741
theorem B1053857 : Blo 702318 1053857 := bstep (se 2 (by rfl) ⟨395196, by rfl⟩ : syracuseStep 1053857 = 790393) B790393
theorem B1053875 : Blo 702318 1053875 := bstep (se 1 (by rfl) ⟨790406, by rfl⟩ : syracuseStep 1053875 = 1580813) B1580813
theorem B1053905 : Blo 702318 1053905 := bstep (se 2 (by rfl) ⟨395214, by rfl⟩ : syracuseStep 1053905 = 790429) B790429
theorem B1053923 : Blo 702318 1053923 := bstep (se 1 (by rfl) ⟨790442, by rfl⟩ : syracuseStep 1053923 = 1580885) B1580885
theorem B791779 : Blo 702318 791779 := bstep (se 1 (by rfl) ⟨593834, by rfl⟩ : syracuseStep 791779 = 1187669) B1187669
theorem B1053953 : Blo 702318 1053953 := bstep (se 2 (by rfl) ⟨395232, by rfl⟩ : syracuseStep 1053953 = 790465) B790465
theorem B2004227 : Blo 702318 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B1053971 : Blo 702318 1053971 := bstep (se 1 (by rfl) ⟨790478, by rfl⟩ : syracuseStep 1053971 = 1580957) B1580957
theorem B1217825 : Blo 702318 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B1054001 : Blo 702318 1054001 := bstep (se 2 (by rfl) ⟨395250, by rfl⟩ : syracuseStep 1054001 = 790501) B790501
theorem B4003121 : Blo 702318 4003121 := bstep (se 2 (by rfl) ⟨1501170, by rfl⟩ : syracuseStep 4003121 = 3002341) B3002341
theorem B1054019 : Blo 702318 1054019 := bstep (se 1 (by rfl) ⟨790514, by rfl⟩ : syracuseStep 1054019 = 1581029) B1581029
theorem B1054049 : Blo 702318 1054049 := bstep (se 2 (by rfl) ⟨395268, by rfl⟩ : syracuseStep 1054049 = 790537) B790537
theorem B1054067 : Blo 702318 1054067 := bstep (se 1 (by rfl) ⟨790550, by rfl⟩ : syracuseStep 1054067 = 1581101) B1581101
theorem B791923 : Blo 702318 791923 := bstep (se 1 (by rfl) ⟨593942, by rfl⟩ : syracuseStep 791923 = 1187885) B1187885
theorem B1054097 : Blo 702318 1054097 := bstep (se 2 (by rfl) ⟨395286, by rfl⟩ : syracuseStep 1054097 = 790573) B790573
theorem B1185185 : Blo 702318 1185185 := bstep (se 2 (by rfl) ⟨444444, by rfl⟩ : syracuseStep 1185185 = 888889) B888889
theorem B1054115 : Blo 702318 1054115 := bstep (se 1 (by rfl) ⟨790586, by rfl⟩ : syracuseStep 1054115 = 1581173) B1581173
theorem B890291 : Blo 702318 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B1054145 : Blo 702318 1054145 := bstep (se 2 (by rfl) ⟨395304, by rfl⟩ : syracuseStep 1054145 = 790609) B790609
theorem B1054163 : Blo 702318 1054163 := bstep (se 1 (by rfl) ⟨790622, by rfl⟩ : syracuseStep 1054163 = 1581245) B1581245
theorem B1054193 : Blo 702318 1054193 := bstep (se 2 (by rfl) ⟨395322, by rfl⟩ : syracuseStep 1054193 = 790645) B790645
theorem B1054211 : Blo 702318 1054211 := bstep (se 1 (by rfl) ⟨790658, by rfl⟩ : syracuseStep 1054211 = 1581317) B1581317
theorem B792067 : Blo 702318 792067 := bstep (se 1 (by rfl) ⟨594050, by rfl⟩ : syracuseStep 792067 = 1188101) B1188101
theorem B1185313 : Blo 702318 1185313 := bstep (se 2 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 1185313 = 888985) B888985
theorem B1054241 : Blo 702318 1054241 := bstep (se 2 (by rfl) ⟨395340, by rfl⟩ : syracuseStep 1054241 = 790681) B790681
theorem B1054259 : Blo 702318 1054259 := bstep (se 1 (by rfl) ⟨790694, by rfl⟩ : syracuseStep 1054259 = 1581389) B1581389
theorem B1185347 : Blo 702318 1185347 := bstep (se 1 (by rfl) ⟨889010, by rfl⟩ : syracuseStep 1185347 = 1778021) B1778021
theorem B1054289 : Blo 702318 1054289 := bstep (se 2 (by rfl) ⟨395358, by rfl⟩ : syracuseStep 1054289 = 790717) B790717
theorem B1054307 : Blo 702318 1054307 := bstep (se 1 (by rfl) ⟨790730, by rfl⟩ : syracuseStep 1054307 = 1581461) B1581461
theorem B1054337 : Blo 702318 1054337 := bstep (se 2 (by rfl) ⟨395376, by rfl⟩ : syracuseStep 1054337 = 790753) B790753
theorem B1054355 : Blo 702318 1054355 := bstep (se 1 (by rfl) ⟨790766, by rfl⟩ : syracuseStep 1054355 = 1581533) B1581533
theorem B792211 : Blo 702318 792211 := bstep (se 1 (by rfl) ⟨594158, by rfl⟩ : syracuseStep 792211 = 1188317) B1188317
theorem B1054385 : Blo 702318 1054385 := bstep (se 2 (by rfl) ⟨395394, by rfl⟩ : syracuseStep 1054385 = 790789) B790789
theorem B1185475 : Blo 702318 1185475 := bstep (se 1 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 1185475 = 1778213) B1778213
theorem B1054403 : Blo 702318 1054403 := bstep (se 1 (by rfl) ⟨790802, by rfl⟩ : syracuseStep 1054403 = 1581605) B1581605
theorem B1054433 : Blo 702318 1054433 := bstep (se 2 (by rfl) ⟨395412, by rfl⟩ : syracuseStep 1054433 = 790825) B790825
theorem B1054451 : Blo 702318 1054451 := bstep (se 1 (by rfl) ⟨790838, by rfl⟩ : syracuseStep 1054451 = 1581677) B1581677
theorem B1054481 : Blo 702318 1054481 := bstep (se 2 (by rfl) ⟨395430, by rfl⟩ : syracuseStep 1054481 = 790861) B790861
theorem B1054499 : Blo 702318 1054499 := bstep (se 1 (by rfl) ⟨790874, by rfl⟩ : syracuseStep 1054499 = 1581749) B1581749
theorem B792355 : Blo 702318 792355 := bstep (se 1 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 792355 = 1188533) B1188533
theorem B1054529 : Blo 702318 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B1185617 : Blo 702318 1185617 := bstep (se 2 (by rfl) ⟨444606, by rfl⟩ : syracuseStep 1185617 = 889213) B889213
theorem B1054547 : Blo 702318 1054547 := bstep (se 1 (by rfl) ⟨790910, by rfl⟩ : syracuseStep 1054547 = 1581821) B1581821
theorem B1054577 : Blo 702318 1054577 := bstep (se 2 (by rfl) ⟨395466, by rfl⟩ : syracuseStep 1054577 = 790933) B790933
theorem B1054595 : Blo 702318 1054595 := bstep (se 1 (by rfl) ⟨790946, by rfl⟩ : syracuseStep 1054595 = 1581893) B1581893
theorem B1087379 : Blo 702318 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B1054625 : Blo 702318 1054625 := bstep (se 2 (by rfl) ⟨395484, by rfl⟩ : syracuseStep 1054625 = 790969) B790969
theorem B1054643 : Blo 702318 1054643 := bstep (se 1 (by rfl) ⟨790982, by rfl⟩ : syracuseStep 1054643 = 1581965) B1581965
theorem B792499 : Blo 702318 792499 := bstep (se 1 (by rfl) ⟨594374, by rfl⟩ : syracuseStep 792499 = 1188749) B1188749
theorem B8591285 : Blo 702318 8591285 := bstep (se 5 (by rfl) ⟨402716, by rfl⟩ : syracuseStep 8591285 = 805433) B805433
theorem B1185745 : Blo 702318 1185745 := bstep (se 2 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 1185745 = 889309) B889309
theorem B1054673 : Blo 702318 1054673 := bstep (se 2 (by rfl) ⟨395502, by rfl⟩ : syracuseStep 1054673 = 791005) B791005
theorem B1054691 : Blo 702318 1054691 := bstep (se 1 (by rfl) ⟨791018, by rfl⟩ : syracuseStep 1054691 = 1582037) B1582037
theorem B1185779 : Blo 702318 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B1054721 : Blo 702318 1054721 := bstep (se 2 (by rfl) ⟨395520, by rfl⟩ : syracuseStep 1054721 = 791041) B791041
theorem B1054739 : Blo 702318 1054739 := bstep (se 1 (by rfl) ⟨791054, by rfl⟩ : syracuseStep 1054739 = 1582109) B1582109
theorem B1054769 : Blo 702318 1054769 := bstep (se 2 (by rfl) ⟨395538, by rfl⟩ : syracuseStep 1054769 = 791077) B791077
theorem B1054787 : Blo 702318 1054787 := bstep (se 1 (by rfl) ⟨791090, by rfl⟩ : syracuseStep 1054787 = 1582181) B1582181
theorem B792643 : Blo 702318 792643 := bstep (se 1 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 792643 = 1188965) B1188965
theorem B2005069 : Blo 702318 2005069 := bstep (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) B751901
theorem B1054817 : Blo 702318 1054817 := bstep (se 2 (by rfl) ⟨395556, by rfl⟩ : syracuseStep 1054817 = 791113) B791113
theorem B1185907 : Blo 702318 1185907 := bstep (se 1 (by rfl) ⟨889430, by rfl⟩ : syracuseStep 1185907 = 1778861) B1778861
theorem B1054835 : Blo 702318 1054835 := bstep (se 1 (by rfl) ⟨791126, by rfl⟩ : syracuseStep 1054835 = 1582253) B1582253
theorem B890995 : Blo 702318 890995 := bstep (se 1 (by rfl) ⟨668246, by rfl⟩ : syracuseStep 890995 = 1336493) B1336493
theorem B1054865 : Blo 702318 1054865 := bstep (se 2 (by rfl) ⟨395574, by rfl⟩ : syracuseStep 1054865 = 791149) B791149
theorem B1054883 : Blo 702318 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B1054913 : Blo 702318 1054913 := bstep (se 2 (by rfl) ⟨395592, by rfl⟩ : syracuseStep 1054913 = 791185) B791185
theorem B1054931 : Blo 702318 1054931 := bstep (se 1 (by rfl) ⟨791198, by rfl⟩ : syracuseStep 1054931 = 1582397) B1582397
theorem B891091 : Blo 702318 891091 := bstep (se 1 (by rfl) ⟨668318, by rfl⟩ : syracuseStep 891091 = 1336637) B1336637
theorem B792787 : Blo 702318 792787 := bstep (se 1 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 792787 = 1189181) B1189181
theorem B20355299 : Blo 702318 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B2005229 : Blo 702318 2005229 := bstep (se 3 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 2005229 = 751961) B751961
theorem B1054961 : Blo 702318 1054961 := bstep (se 2 (by rfl) ⟨395610, by rfl⟩ : syracuseStep 1054961 = 791221) B791221
theorem B1186049 : Blo 702318 1186049 := bstep (se 2 (by rfl) ⟨444768, by rfl⟩ : syracuseStep 1186049 = 889537) B889537
theorem B1054979 : Blo 702318 1054979 := bstep (se 1 (by rfl) ⟨791234, by rfl⟩ : syracuseStep 1054979 = 1582469) B1582469
theorem B1055009 : Blo 702318 1055009 := bstep (se 2 (by rfl) ⟨395628, by rfl⟩ : syracuseStep 1055009 = 791257) B791257
theorem B1055027 : Blo 702318 1055027 := bstep (se 1 (by rfl) ⟨791270, by rfl⟩ : syracuseStep 1055027 = 1582541) B1582541
theorem B1055057 : Blo 702318 1055057 := bstep (se 2 (by rfl) ⟨395646, by rfl⟩ : syracuseStep 1055057 = 791293) B791293
theorem B1055075 : Blo 702318 1055075 := bstep (se 1 (by rfl) ⟨791306, by rfl⟩ : syracuseStep 1055075 = 1582613) B1582613
theorem B792931 : Blo 702318 792931 := bstep (se 1 (by rfl) ⟨594698, by rfl⟩ : syracuseStep 792931 = 1189397) B1189397
theorem B1907057 : Blo 702318 1907057 := bstep (se 2 (by rfl) ⟨715146, by rfl⟩ : syracuseStep 1907057 = 1430293) B1430293
theorem B1186177 : Blo 702318 1186177 := bstep (se 2 (by rfl) ⟨444816, by rfl⟩ : syracuseStep 1186177 = 889633) B889633
theorem B1055105 : Blo 702318 1055105 := bstep (se 2 (by rfl) ⟨395664, by rfl⟩ : syracuseStep 1055105 = 791329) B791329
theorem B9247117 : Blo 702318 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B1055123 : Blo 702318 1055123 := bstep (se 1 (by rfl) ⟨791342, by rfl⟩ : syracuseStep 1055123 = 1582685) B1582685
theorem B1186211 : Blo 702318 1186211 := bstep (se 1 (by rfl) ⟨889658, by rfl⟩ : syracuseStep 1186211 = 1779317) B1779317
theorem B2005411 : Blo 702318 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B1055153 : Blo 702318 1055153 := bstep (se 2 (by rfl) ⟨395682, by rfl⟩ : syracuseStep 1055153 = 791365) B791365
theorem B1055171 : Blo 702318 1055171 := bstep (se 1 (by rfl) ⟨791378, by rfl⟩ : syracuseStep 1055171 = 1582757) B1582757
theorem B1055201 : Blo 702318 1055201 := bstep (se 2 (by rfl) ⟨395700, by rfl⟩ : syracuseStep 1055201 = 791401) B791401
theorem B1055219 : Blo 702318 1055219 := bstep (se 1 (by rfl) ⟨791414, by rfl⟩ : syracuseStep 1055219 = 1582829) B1582829
theorem B793075 : Blo 702318 793075 := bstep (se 1 (by rfl) ⟨594806, by rfl⟩ : syracuseStep 793075 = 1189613) B1189613
theorem B1055249 : Blo 702318 1055249 := bstep (se 2 (by rfl) ⟨395718, by rfl⟩ : syracuseStep 1055249 = 791437) B791437
theorem B1186339 : Blo 702318 1186339 := bstep (se 1 (by rfl) ⟨889754, by rfl⟩ : syracuseStep 1186339 = 1779509) B1779509
theorem B1055267 : Blo 702318 1055267 := bstep (se 1 (by rfl) ⟨791450, by rfl⟩ : syracuseStep 1055267 = 1582901) B1582901
theorem B1055297 : Blo 702318 1055297 := bstep (se 2 (by rfl) ⟨395736, by rfl⟩ : syracuseStep 1055297 = 791473) B791473
theorem B1055315 : Blo 702318 1055315 := bstep (se 1 (by rfl) ⟨791486, by rfl⟩ : syracuseStep 1055315 = 1582973) B1582973
theorem B1055345 : Blo 702318 1055345 := bstep (se 2 (by rfl) ⟨395754, by rfl⟩ : syracuseStep 1055345 = 791509) B791509
theorem B1055363 : Blo 702318 1055363 := bstep (se 1 (by rfl) ⟨791522, by rfl⟩ : syracuseStep 1055363 = 1583045) B1583045
theorem B793219 : Blo 702318 793219 := bstep (se 1 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 793219 = 1189829) B1189829
theorem B1055393 : Blo 702318 1055393 := bstep (se 2 (by rfl) ⟨395772, by rfl⟩ : syracuseStep 1055393 = 791545) B791545
theorem B1186481 : Blo 702318 1186481 := bstep (se 2 (by rfl) ⟨444930, by rfl⟩ : syracuseStep 1186481 = 889861) B889861
theorem B1055411 : Blo 702318 1055411 := bstep (se 1 (by rfl) ⟨791558, by rfl⟩ : syracuseStep 1055411 = 1583117) B1583117
theorem B891587 : Blo 702318 891587 := bstep (se 1 (by rfl) ⟨668690, by rfl⟩ : syracuseStep 891587 = 1337381) B1337381
theorem B1055441 : Blo 702318 1055441 := bstep (se 2 (by rfl) ⟨395790, by rfl⟩ : syracuseStep 1055441 = 791581) B791581
theorem B3807971 : Blo 702318 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B4004579 : Blo 702318 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B1055459 : Blo 702318 1055459 := bstep (se 1 (by rfl) ⟨791594, by rfl⟩ : syracuseStep 1055459 = 1583189) B1583189
theorem B1055489 : Blo 702318 1055489 := bstep (se 2 (by rfl) ⟨395808, by rfl⟩ : syracuseStep 1055489 = 791617) B791617
theorem B1055507 : Blo 702318 1055507 := bstep (se 1 (by rfl) ⟨791630, by rfl⟩ : syracuseStep 1055507 = 1583261) B1583261
theorem B793363 : Blo 702318 793363 := bstep (se 1 (by rfl) ⟨595022, by rfl⟩ : syracuseStep 793363 = 1190045) B1190045
theorem B1186609 : Blo 702318 1186609 := bstep (se 2 (by rfl) ⟨444978, by rfl⟩ : syracuseStep 1186609 = 889957) B889957
theorem B1055537 : Blo 702318 1055537 := bstep (se 2 (by rfl) ⟨395826, by rfl⟩ : syracuseStep 1055537 = 791653) B791653
theorem B1055555 : Blo 702318 1055555 := bstep (se 1 (by rfl) ⟨791666, by rfl⟩ : syracuseStep 1055555 = 1583333) B1583333
theorem B1186643 : Blo 702318 1186643 := bstep (se 1 (by rfl) ⟨889982, by rfl⟩ : syracuseStep 1186643 = 1779965) B1779965
theorem B1055585 : Blo 702318 1055585 := bstep (se 2 (by rfl) ⟨395844, by rfl⟩ : syracuseStep 1055585 = 791689) B791689
theorem B1055603 : Blo 702318 1055603 := bstep (se 1 (by rfl) ⟨791702, by rfl⟩ : syracuseStep 1055603 = 1583405) B1583405
theorem B1055633 : Blo 702318 1055633 := bstep (se 2 (by rfl) ⟨395862, by rfl⟩ : syracuseStep 1055633 = 791725) B791725
theorem B1055651 : Blo 702318 1055651 := bstep (se 1 (by rfl) ⟨791738, by rfl⟩ : syracuseStep 1055651 = 1583477) B1583477
theorem B793507 : Blo 702318 793507 := bstep (se 1 (by rfl) ⟨595130, by rfl⟩ : syracuseStep 793507 = 1190261) B1190261
theorem B1055681 : Blo 702318 1055681 := bstep (se 2 (by rfl) ⟨395880, by rfl⟩ : syracuseStep 1055681 = 791761) B791761
theorem B1186771 : Blo 702318 1186771 := bstep (se 1 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 1186771 = 1780157) B1780157
theorem B1055699 : Blo 702318 1055699 := bstep (se 1 (by rfl) ⟨791774, by rfl⟩ : syracuseStep 1055699 = 1583549) B1583549
theorem B1055729 : Blo 702318 1055729 := bstep (se 2 (by rfl) ⟨395898, by rfl⟩ : syracuseStep 1055729 = 791797) B791797
theorem B1055747 : Blo 702318 1055747 := bstep (se 1 (by rfl) ⟨791810, by rfl⟩ : syracuseStep 1055747 = 1583621) B1583621
theorem B1055777 : Blo 702318 1055777 := bstep (se 2 (by rfl) ⟨395916, by rfl⟩ : syracuseStep 1055777 = 791833) B791833
theorem B1055795 : Blo 702318 1055795 := bstep (se 1 (by rfl) ⟨791846, by rfl⟩ : syracuseStep 1055795 = 1583693) B1583693
theorem B793651 : Blo 702318 793651 := bstep (se 1 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 793651 = 1190477) B1190477
theorem B1055825 : Blo 702318 1055825 := bstep (se 2 (by rfl) ⟨395934, by rfl⟩ : syracuseStep 1055825 = 791869) B791869
theorem B1186913 : Blo 702318 1186913 := bstep (se 2 (by rfl) ⟨445092, by rfl⟩ : syracuseStep 1186913 = 890185) B890185
theorem B1055843 : Blo 702318 1055843 := bstep (se 1 (by rfl) ⟨791882, by rfl⟩ : syracuseStep 1055843 = 1583765) B1583765
theorem B1055873 : Blo 702318 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B1055891 : Blo 702318 1055891 := bstep (se 1 (by rfl) ⟨791918, by rfl⟩ : syracuseStep 1055891 = 1583837) B1583837
theorem B1055921 : Blo 702318 1055921 := bstep (se 2 (by rfl) ⟨395970, by rfl⟩ : syracuseStep 1055921 = 791941) B791941
theorem B1055939 : Blo 702318 1055939 := bstep (se 1 (by rfl) ⟨791954, by rfl⟩ : syracuseStep 1055939 = 1583909) B1583909
theorem B793795 : Blo 702318 793795 := bstep (se 1 (by rfl) ⟨595346, by rfl⟩ : syracuseStep 793795 = 1190693) B1190693
theorem B1187041 : Blo 702318 1187041 := bstep (se 2 (by rfl) ⟨445140, by rfl⟩ : syracuseStep 1187041 = 890281) B890281
theorem B1055969 : Blo 702318 1055969 := bstep (se 2 (by rfl) ⟨395988, by rfl⟩ : syracuseStep 1055969 = 791977) B791977
theorem B1580273 : Blo 702318 1580273 := bstep (se 2 (by rfl) ⟨592602, by rfl⟩ : syracuseStep 1580273 = 1185205) B1185205
theorem B1055987 : Blo 702318 1055987 := bstep (se 1 (by rfl) ⟨791990, by rfl⟩ : syracuseStep 1055987 = 1583981) B1583981
theorem B1580291 : Blo 702318 1580291 := bstep (se 1 (by rfl) ⟨1185218, by rfl⟩ : syracuseStep 1580291 = 2370437) B2370437
theorem B1187075 : Blo 702318 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B1056017 : Blo 702318 1056017 := bstep (se 2 (by rfl) ⟨396006, by rfl⟩ : syracuseStep 1056017 = 792013) B792013
theorem B1056035 : Blo 702318 1056035 := bstep (se 1 (by rfl) ⟨792026, by rfl⟩ : syracuseStep 1056035 = 1584053) B1584053
theorem B1056065 : Blo 702318 1056065 := bstep (se 2 (by rfl) ⟨396024, by rfl⟩ : syracuseStep 1056065 = 792049) B792049
theorem B1056083 : Blo 702318 1056083 := bstep (se 1 (by rfl) ⟨792062, by rfl⟩ : syracuseStep 1056083 = 1584125) B1584125
theorem B793939 : Blo 702318 793939 := bstep (se 1 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 793939 = 1190909) B1190909
theorem B1056113 : Blo 702318 1056113 := bstep (se 2 (by rfl) ⟨396042, by rfl⟩ : syracuseStep 1056113 = 792085) B792085
theorem B1187203 : Blo 702318 1187203 := bstep (se 1 (by rfl) ⟨890402, by rfl⟩ : syracuseStep 1187203 = 1780805) B1780805
theorem B1056131 : Blo 702318 1056131 := bstep (se 1 (by rfl) ⟨792098, by rfl⟩ : syracuseStep 1056131 = 1584197) B1584197
theorem B892291 : Blo 702318 892291 := bstep (se 1 (by rfl) ⟨669218, by rfl⟩ : syracuseStep 892291 = 1338437) B1338437
theorem B1056161 : Blo 702318 1056161 := bstep (se 2 (by rfl) ⟨396060, by rfl⟩ : syracuseStep 1056161 = 792121) B792121
theorem B1056179 : Blo 702318 1056179 := bstep (se 1 (by rfl) ⟨792134, by rfl⟩ : syracuseStep 1056179 = 1584269) B1584269
theorem B1056209 : Blo 702318 1056209 := bstep (se 2 (by rfl) ⟨396078, by rfl⟩ : syracuseStep 1056209 = 792157) B792157
theorem B1056227 : Blo 702318 1056227 := bstep (se 1 (by rfl) ⟨792170, by rfl⟩ : syracuseStep 1056227 = 1584341) B1584341
theorem B892387 : Blo 702318 892387 := bstep (se 1 (by rfl) ⟨669290, by rfl⟩ : syracuseStep 892387 = 1338581) B1338581
theorem B794083 : Blo 702318 794083 := bstep (se 1 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 794083 = 1191125) B1191125
theorem B1056257 : Blo 702318 1056257 := bstep (se 2 (by rfl) ⟨396096, by rfl⟩ : syracuseStep 1056257 = 792193) B792193
theorem B1580561 : Blo 702318 1580561 := bstep (se 2 (by rfl) ⟨592710, by rfl⟩ : syracuseStep 1580561 = 1185421) B1185421
theorem B1187345 : Blo 702318 1187345 := bstep (se 2 (by rfl) ⟨445254, by rfl⟩ : syracuseStep 1187345 = 890509) B890509
theorem B1056275 : Blo 702318 1056275 := bstep (se 1 (by rfl) ⟨792206, by rfl⟩ : syracuseStep 1056275 = 1584413) B1584413
theorem B1580579 : Blo 702318 1580579 := bstep (se 1 (by rfl) ⟨1185434, by rfl⟩ : syracuseStep 1580579 = 2370869) B2370869
theorem B1056305 : Blo 702318 1056305 := bstep (se 2 (by rfl) ⟨396114, by rfl⟩ : syracuseStep 1056305 = 792229) B792229
theorem B1056323 : Blo 702318 1056323 := bstep (se 1 (by rfl) ⟨792242, by rfl⟩ : syracuseStep 1056323 = 1584485) B1584485
theorem B1056353 : Blo 702318 1056353 := bstep (se 2 (by rfl) ⟨396132, by rfl⟩ : syracuseStep 1056353 = 792265) B792265
theorem B1056371 : Blo 702318 1056371 := bstep (se 1 (by rfl) ⟨792278, by rfl⟩ : syracuseStep 1056371 = 1584557) B1584557
theorem B794227 : Blo 702318 794227 := bstep (se 1 (by rfl) ⟨595670, by rfl⟩ : syracuseStep 794227 = 1191341) B1191341
theorem B1908355 : Blo 702318 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B1187473 : Blo 702318 1187473 := bstep (se 2 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 1187473 = 890605) B890605
theorem B1056401 : Blo 702318 1056401 := bstep (se 2 (by rfl) ⟨396150, by rfl⟩ : syracuseStep 1056401 = 792301) B792301
theorem B1056419 : Blo 702318 1056419 := bstep (se 1 (by rfl) ⟨792314, by rfl⟩ : syracuseStep 1056419 = 1584629) B1584629
theorem B1908397 : Blo 702318 1908397 := bstep (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) B715649
theorem B1187507 : Blo 702318 1187507 := bstep (se 1 (by rfl) ⟨890630, by rfl⟩ : syracuseStep 1187507 = 1781261) B1781261
theorem B1056449 : Blo 702318 1056449 := bstep (se 2 (by rfl) ⟨396168, by rfl⟩ : syracuseStep 1056449 = 792337) B792337
theorem B1056467 : Blo 702318 1056467 := bstep (se 1 (by rfl) ⟨792350, by rfl⟩ : syracuseStep 1056467 = 1584701) B1584701
theorem B1056497 : Blo 702318 1056497 := bstep (se 2 (by rfl) ⟨396186, by rfl⟩ : syracuseStep 1056497 = 792373) B792373
theorem B1056515 : Blo 702318 1056515 := bstep (se 1 (by rfl) ⟨792386, by rfl⟩ : syracuseStep 1056515 = 1584773) B1584773
theorem B794371 : Blo 702318 794371 := bstep (se 1 (by rfl) ⟨595778, by rfl⟩ : syracuseStep 794371 = 1191557) B1191557
theorem B2006801 : Blo 702318 2006801 := bstep (se 2 (by rfl) ⟨752550, by rfl⟩ : syracuseStep 2006801 = 1505101) B1505101
theorem B1056545 : Blo 702318 1056545 := bstep (se 2 (by rfl) ⟨396204, by rfl⟩ : syracuseStep 1056545 = 792409) B792409
theorem B1580849 : Blo 702318 1580849 := bstep (se 2 (by rfl) ⟨592818, by rfl⟩ : syracuseStep 1580849 = 1185637) B1185637
theorem B1187635 : Blo 702318 1187635 := bstep (se 1 (by rfl) ⟨890726, by rfl⟩ : syracuseStep 1187635 = 1781453) B1781453
theorem B1056563 : Blo 702318 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B1580867 : Blo 702318 1580867 := bstep (se 1 (by rfl) ⟨1185650, by rfl⟩ : syracuseStep 1580867 = 2371301) B2371301
theorem B1056593 : Blo 702318 1056593 := bstep (se 2 (by rfl) ⟨396222, by rfl⟩ : syracuseStep 1056593 = 792445) B792445
theorem B1056611 : Blo 702318 1056611 := bstep (se 1 (by rfl) ⟨792458, by rfl⟩ : syracuseStep 1056611 = 1584917) B1584917
theorem B3383153 : Blo 702318 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B1056641 : Blo 702318 1056641 := bstep (se 2 (by rfl) ⟨396240, by rfl⟩ : syracuseStep 1056641 = 792481) B792481
theorem B1056659 : Blo 702318 1056659 := bstep (se 1 (by rfl) ⟨792494, by rfl⟩ : syracuseStep 1056659 = 1584989) B1584989
theorem B794515 : Blo 702318 794515 := bstep (se 1 (by rfl) ⟨595886, by rfl⟩ : syracuseStep 794515 = 1191773) B1191773
theorem B1056689 : Blo 702318 1056689 := bstep (se 2 (by rfl) ⟨396258, by rfl⟩ : syracuseStep 1056689 = 792517) B792517
theorem B1449905 : Blo 702318 1449905 := bstep (se 2 (by rfl) ⟨543714, by rfl⟩ : syracuseStep 1449905 = 1087429) B1087429
theorem B1187777 : Blo 702318 1187777 := bstep (se 2 (by rfl) ⟨445416, by rfl⟩ : syracuseStep 1187777 = 890833) B890833
theorem B1056707 : Blo 702318 1056707 := bstep (se 1 (by rfl) ⟨792530, by rfl⟩ : syracuseStep 1056707 = 1585061) B1585061
theorem B892883 : Blo 702318 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B1056737 : Blo 702318 1056737 := bstep (se 2 (by rfl) ⟨396276, by rfl⟩ : syracuseStep 1056737 = 792553) B792553
theorem B1056755 : Blo 702318 1056755 := bstep (se 1 (by rfl) ⟨792566, by rfl⟩ : syracuseStep 1056755 = 1585133) B1585133
theorem B1056785 : Blo 702318 1056785 := bstep (se 2 (by rfl) ⟨396294, by rfl⟩ : syracuseStep 1056785 = 792589) B792589
theorem B1056803 : Blo 702318 1056803 := bstep (se 1 (by rfl) ⟨792602, by rfl⟩ : syracuseStep 1056803 = 1585205) B1585205
theorem B1187905 : Blo 702318 1187905 := bstep (se 2 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 1187905 = 890929) B890929
theorem B1056833 : Blo 702318 1056833 := bstep (se 2 (by rfl) ⟨396312, by rfl⟩ : syracuseStep 1056833 = 792625) B792625
theorem B1581137 : Blo 702318 1581137 := bstep (se 2 (by rfl) ⟨592926, by rfl⟩ : syracuseStep 1581137 = 1185853) B1185853
theorem B1056851 : Blo 702318 1056851 := bstep (se 1 (by rfl) ⟨792638, by rfl⟩ : syracuseStep 1056851 = 1585277) B1585277
theorem B1581155 : Blo 702318 1581155 := bstep (se 1 (by rfl) ⟨1185866, by rfl⟩ : syracuseStep 1581155 = 2371733) B2371733
theorem B1187939 : Blo 702318 1187939 := bstep (se 1 (by rfl) ⟨890954, by rfl⟩ : syracuseStep 1187939 = 1781909) B1781909
theorem B1056881 : Blo 702318 1056881 := bstep (se 2 (by rfl) ⟨396330, by rfl⟩ : syracuseStep 1056881 = 792661) B792661
theorem B1056899 : Blo 702318 1056899 := bstep (se 1 (by rfl) ⟨792674, by rfl⟩ : syracuseStep 1056899 = 1585349) B1585349
theorem B1056929 : Blo 702318 1056929 := bstep (se 2 (by rfl) ⟨396348, by rfl⟩ : syracuseStep 1056929 = 792697) B792697
theorem B1056947 : Blo 702318 1056947 := bstep (se 1 (by rfl) ⟨792710, by rfl⟩ : syracuseStep 1056947 = 1585421) B1585421
theorem B1777859 : Blo 702318 1777859 := bstep (se 1 (by rfl) ⟨1333394, by rfl⟩ : syracuseStep 1777859 = 2666789) B2666789
theorem B1056977 : Blo 702318 1056977 := bstep (se 2 (by rfl) ⟨396366, by rfl⟩ : syracuseStep 1056977 = 792733) B792733
theorem B9248995 : Blo 702318 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B1188067 : Blo 702318 1188067 := bstep (se 1 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 1188067 = 1782101) B1782101
theorem B1056995 : Blo 702318 1056995 := bstep (se 1 (by rfl) ⟨792746, by rfl⟩ : syracuseStep 1056995 = 1585493) B1585493
theorem B1057025 : Blo 702318 1057025 := bstep (se 2 (by rfl) ⟨396384, by rfl⟩ : syracuseStep 1057025 = 792769) B792769
theorem B1057043 : Blo 702318 1057043 := bstep (se 1 (by rfl) ⟨792782, by rfl⟩ : syracuseStep 1057043 = 1585565) B1585565
theorem B1057073 : Blo 702318 1057073 := bstep (se 2 (by rfl) ⟨396402, by rfl⟩ : syracuseStep 1057073 = 792805) B792805
theorem B1057091 : Blo 702318 1057091 := bstep (se 1 (by rfl) ⟨792818, by rfl⟩ : syracuseStep 1057091 = 1585637) B1585637
theorem B1057121 : Blo 702318 1057121 := bstep (se 2 (by rfl) ⟨396420, by rfl⟩ : syracuseStep 1057121 = 792841) B792841
theorem B1581425 : Blo 702318 1581425 := bstep (se 2 (by rfl) ⟨593034, by rfl⟩ : syracuseStep 1581425 = 1186069) B1186069
theorem B1188209 : Blo 702318 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B1057139 : Blo 702318 1057139 := bstep (se 1 (by rfl) ⟨792854, by rfl⟩ : syracuseStep 1057139 = 1585709) B1585709
theorem B1778051 : Blo 702318 1778051 := bstep (se 1 (by rfl) ⟨1333538, by rfl⟩ : syracuseStep 1778051 = 2667077) B2667077
theorem B1581443 : Blo 702318 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B1909133 : Blo 702318 1909133 := bstep (se 3 (by rfl) ⟨357962, by rfl⟩ : syracuseStep 1909133 = 715925) B715925
theorem B1057169 : Blo 702318 1057169 := bstep (se 2 (by rfl) ⟨396438, by rfl⟩ : syracuseStep 1057169 = 792877) B792877
theorem B1057187 : Blo 702318 1057187 := bstep (se 1 (by rfl) ⟨792890, by rfl⟩ : syracuseStep 1057187 = 1585781) B1585781
theorem B1057217 : Blo 702318 1057217 := bstep (se 2 (by rfl) ⟨396456, by rfl⟩ : syracuseStep 1057217 = 792913) B792913
theorem B1057235 : Blo 702318 1057235 := bstep (se 1 (by rfl) ⟨792926, by rfl⟩ : syracuseStep 1057235 = 1585853) B1585853
theorem B1188337 : Blo 702318 1188337 := bstep (se 2 (by rfl) ⟨445626, by rfl⟩ : syracuseStep 1188337 = 891253) B891253
theorem B1057265 : Blo 702318 1057265 := bstep (se 2 (by rfl) ⟨396474, by rfl⟩ : syracuseStep 1057265 = 792949) B792949
theorem B1057283 : Blo 702318 1057283 := bstep (se 1 (by rfl) ⟨792962, by rfl⟩ : syracuseStep 1057283 = 1585925) B1585925
theorem B1188371 : Blo 702318 1188371 := bstep (se 1 (by rfl) ⟨891278, by rfl⟩ : syracuseStep 1188371 = 1782557) B1782557
theorem B1057313 : Blo 702318 1057313 := bstep (se 2 (by rfl) ⟨396492, by rfl⟩ : syracuseStep 1057313 = 792985) B792985
theorem B3580465 : Blo 702318 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B1057331 : Blo 702318 1057331 := bstep (se 1 (by rfl) ⟨792998, by rfl⟩ : syracuseStep 1057331 = 1585997) B1585997
theorem B1057361 : Blo 702318 1057361 := bstep (se 2 (by rfl) ⟨396510, by rfl⟩ : syracuseStep 1057361 = 793021) B793021
theorem B1057379 : Blo 702318 1057379 := bstep (se 1 (by rfl) ⟨793034, by rfl⟩ : syracuseStep 1057379 = 1586069) B1586069
theorem B1057409 : Blo 702318 1057409 := bstep (se 2 (by rfl) ⟨396528, by rfl⟩ : syracuseStep 1057409 = 793057) B793057
theorem B1581713 : Blo 702318 1581713 := bstep (se 2 (by rfl) ⟨593142, by rfl⟩ : syracuseStep 1581713 = 1186285) B1186285
theorem B1188499 : Blo 702318 1188499 := bstep (se 1 (by rfl) ⟨891374, by rfl⟩ : syracuseStep 1188499 = 1782749) B1782749
theorem B1057427 : Blo 702318 1057427 := bstep (se 1 (by rfl) ⟨793070, by rfl⟩ : syracuseStep 1057427 = 1586141) B1586141
theorem B893587 : Blo 702318 893587 := bstep (se 1 (by rfl) ⟨670190, by rfl⟩ : syracuseStep 893587 = 1340381) B1340381
theorem B1581731 : Blo 702318 1581731 := bstep (se 1 (by rfl) ⟨1186298, by rfl⟩ : syracuseStep 1581731 = 2372597) B2372597
theorem B1057457 : Blo 702318 1057457 := bstep (se 2 (by rfl) ⟨396546, by rfl⟩ : syracuseStep 1057457 = 793093) B793093
theorem B1057475 : Blo 702318 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B2007757 : Blo 702318 2007757 := bstep (se 3 (by rfl) ⟨376454, by rfl⟩ : syracuseStep 2007757 = 752909) B752909
theorem B2859725 : Blo 702318 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B1057505 : Blo 702318 1057505 := bstep (se 2 (by rfl) ⟨396564, by rfl⟩ : syracuseStep 1057505 = 793129) B793129
theorem B1057523 : Blo 702318 1057523 := bstep (se 1 (by rfl) ⟨793142, by rfl⟩ : syracuseStep 1057523 = 1586285) B1586285
theorem B893683 : Blo 702318 893683 := bstep (se 1 (by rfl) ⟨670262, by rfl⟩ : syracuseStep 893683 = 1340525) B1340525
theorem B1057553 : Blo 702318 1057553 := bstep (se 2 (by rfl) ⟨396582, by rfl⟩ : syracuseStep 1057553 = 793165) B793165
theorem B1188641 : Blo 702318 1188641 := bstep (se 2 (by rfl) ⟨445740, by rfl⟩ : syracuseStep 1188641 = 891481) B891481
theorem B2532131 : Blo 702318 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B1057571 : Blo 702318 1057571 := bstep (se 1 (by rfl) ⟨793178, by rfl⟩ : syracuseStep 1057571 = 1586357) B1586357
theorem B1057601 : Blo 702318 1057601 := bstep (se 2 (by rfl) ⟨396600, by rfl⟩ : syracuseStep 1057601 = 793201) B793201
theorem B1057619 : Blo 702318 1057619 := bstep (se 1 (by rfl) ⟨793214, by rfl⟩ : syracuseStep 1057619 = 1586429) B1586429
theorem B1057649 : Blo 702318 1057649 := bstep (se 2 (by rfl) ⟨396618, by rfl⟩ : syracuseStep 1057649 = 793237) B793237
theorem B1057667 : Blo 702318 1057667 := bstep (se 1 (by rfl) ⟨793250, by rfl⟩ : syracuseStep 1057667 = 1586501) B1586501
theorem B1319825 : Blo 702318 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B1188769 : Blo 702318 1188769 := bstep (se 2 (by rfl) ⟨445788, by rfl⟩ : syracuseStep 1188769 = 891577) B891577
theorem B1057697 : Blo 702318 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B1582001 : Blo 702318 1582001 := bstep (se 2 (by rfl) ⟨593250, by rfl⟩ : syracuseStep 1582001 = 1186501) B1186501
theorem B2007985 : Blo 702318 2007985 := bstep (se 2 (by rfl) ⟨752994, by rfl⟩ : syracuseStep 2007985 = 1505989) B1505989
theorem B1057715 : Blo 702318 1057715 := bstep (se 1 (by rfl) ⟨793286, by rfl⟩ : syracuseStep 1057715 = 1586573) B1586573
theorem B1582019 : Blo 702318 1582019 := bstep (se 1 (by rfl) ⟨1186514, by rfl⟩ : syracuseStep 1582019 = 2373029) B2373029
theorem B1188803 : Blo 702318 1188803 := bstep (se 1 (by rfl) ⟨891602, by rfl⟩ : syracuseStep 1188803 = 1783205) B1783205
theorem B1057745 : Blo 702318 1057745 := bstep (se 2 (by rfl) ⟨396654, by rfl⟩ : syracuseStep 1057745 = 793309) B793309
theorem B9642979 : Blo 702318 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B1057763 : Blo 702318 1057763 := bstep (se 1 (by rfl) ⟨793322, by rfl⟩ : syracuseStep 1057763 = 1586645) B1586645
theorem B1057793 : Blo 702318 1057793 := bstep (se 2 (by rfl) ⟨396672, by rfl⟩ : syracuseStep 1057793 = 793345) B793345
theorem B1057811 : Blo 702318 1057811 := bstep (se 1 (by rfl) ⟨793358, by rfl⟩ : syracuseStep 1057811 = 1586717) B1586717
theorem B1057841 : Blo 702318 1057841 := bstep (se 2 (by rfl) ⟨396690, by rfl⟩ : syracuseStep 1057841 = 793381) B793381
theorem B1188931 : Blo 702318 1188931 := bstep (se 1 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 1188931 = 1783397) B1783397
theorem B1057859 : Blo 702318 1057859 := bstep (se 1 (by rfl) ⟨793394, by rfl⟩ : syracuseStep 1057859 = 1586789) B1586789
theorem B2008145 : Blo 702318 2008145 := bstep (se 2 (by rfl) ⟨753054, by rfl⟩ : syracuseStep 2008145 = 1506109) B1506109
theorem B1057889 : Blo 702318 1057889 := bstep (se 2 (by rfl) ⟨396708, by rfl⟩ : syracuseStep 1057889 = 793417) B793417
theorem B1057907 : Blo 702318 1057907 := bstep (se 1 (by rfl) ⟨793430, by rfl⟩ : syracuseStep 1057907 = 1586861) B1586861
theorem B1057937 : Blo 702318 1057937 := bstep (se 2 (by rfl) ⟨396726, by rfl⟩ : syracuseStep 1057937 = 793453) B793453
theorem B1057955 : Blo 702318 1057955 := bstep (se 1 (by rfl) ⟨793466, by rfl⟩ : syracuseStep 1057955 = 1586933) B1586933
theorem B1057985 : Blo 702318 1057985 := bstep (se 2 (by rfl) ⟨396744, by rfl⟩ : syracuseStep 1057985 = 793489) B793489
theorem B2008259 : Blo 702318 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B1582289 : Blo 702318 1582289 := bstep (se 2 (by rfl) ⟨593358, by rfl⟩ : syracuseStep 1582289 = 1186717) B1186717
theorem B1189073 : Blo 702318 1189073 := bstep (se 2 (by rfl) ⟨445902, by rfl⟩ : syracuseStep 1189073 = 891805) B891805
theorem B1058003 : Blo 702318 1058003 := bstep (se 1 (by rfl) ⟨793502, by rfl⟩ : syracuseStep 1058003 = 1587005) B1587005
theorem B1582307 : Blo 702318 1582307 := bstep (se 1 (by rfl) ⟨1186730, by rfl⟩ : syracuseStep 1582307 = 2373461) B2373461
theorem B1058033 : Blo 702318 1058033 := bstep (se 2 (by rfl) ⟨396762, by rfl⟩ : syracuseStep 1058033 = 793525) B793525
theorem B1058051 : Blo 702318 1058051 := bstep (se 1 (by rfl) ⟨793538, by rfl⟩ : syracuseStep 1058051 = 1587077) B1587077
theorem B1058081 : Blo 702318 1058081 := bstep (se 2 (by rfl) ⟨396780, by rfl⟩ : syracuseStep 1058081 = 793561) B793561
theorem B1778993 : Blo 702318 1778993 := bstep (se 2 (by rfl) ⟨667122, by rfl⟩ : syracuseStep 1778993 = 1334245) B1334245
theorem B1058099 : Blo 702318 1058099 := bstep (se 1 (by rfl) ⟨793574, by rfl⟩ : syracuseStep 1058099 = 1587149) B1587149
theorem B1189201 : Blo 702318 1189201 := bstep (se 2 (by rfl) ⟨445950, by rfl⟩ : syracuseStep 1189201 = 891901) B891901
theorem B1058129 : Blo 702318 1058129 := bstep (se 2 (by rfl) ⟨396798, by rfl⟩ : syracuseStep 1058129 = 793597) B793597
theorem B1779043 : Blo 702318 1779043 := bstep (se 1 (by rfl) ⟨1334282, by rfl⟩ : syracuseStep 1779043 = 2668565) B2668565
theorem B1058147 : Blo 702318 1058147 := bstep (se 1 (by rfl) ⟨793610, by rfl⟩ : syracuseStep 1058147 = 1587221) B1587221
theorem B1189235 : Blo 702318 1189235 := bstep (se 1 (by rfl) ⟨891926, by rfl⟩ : syracuseStep 1189235 = 1783853) B1783853
theorem B1058177 : Blo 702318 1058177 := bstep (se 2 (by rfl) ⟨396816, by rfl⟩ : syracuseStep 1058177 = 793633) B793633
theorem B1058195 : Blo 702318 1058195 := bstep (se 1 (by rfl) ⟨793646, by rfl⟩ : syracuseStep 1058195 = 1587293) B1587293
theorem B1058225 : Blo 702318 1058225 := bstep (se 2 (by rfl) ⟨396834, by rfl⟩ : syracuseStep 1058225 = 793669) B793669
theorem B1058243 : Blo 702318 1058243 := bstep (se 1 (by rfl) ⟨793682, by rfl⟩ : syracuseStep 1058243 = 1587365) B1587365
theorem B1058273 : Blo 702318 1058273 := bstep (se 2 (by rfl) ⟨396852, by rfl⟩ : syracuseStep 1058273 = 793705) B793705
theorem B1779185 : Blo 702318 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1582577 : Blo 702318 1582577 := bstep (se 2 (by rfl) ⟨593466, by rfl⟩ : syracuseStep 1582577 = 1186933) B1186933
theorem B1189363 : Blo 702318 1189363 := bstep (se 1 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 1189363 = 1784045) B1784045
theorem B1058291 : Blo 702318 1058291 := bstep (se 1 (by rfl) ⟨793718, by rfl⟩ : syracuseStep 1058291 = 1587437) B1587437
theorem B1582595 : Blo 702318 1582595 := bstep (se 1 (by rfl) ⟨1186946, by rfl⟩ : syracuseStep 1582595 = 2373893) B2373893
theorem B1058321 : Blo 702318 1058321 := bstep (se 2 (by rfl) ⟨396870, by rfl⟩ : syracuseStep 1058321 = 793741) B793741
theorem B1058339 : Blo 702318 1058339 := bstep (se 1 (by rfl) ⟨793754, by rfl⟩ : syracuseStep 1058339 = 1587509) B1587509
theorem B3221041 : Blo 702318 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1058369 : Blo 702318 1058369 := bstep (se 2 (by rfl) ⟨396888, by rfl⟩ : syracuseStep 1058369 = 793777) B793777
theorem B1058387 : Blo 702318 1058387 := bstep (se 1 (by rfl) ⟨793790, by rfl⟩ : syracuseStep 1058387 = 1587581) B1587581
theorem B1058417 : Blo 702318 1058417 := bstep (se 2 (by rfl) ⟨396906, by rfl⟩ : syracuseStep 1058417 = 793813) B793813
theorem B1189505 : Blo 702318 1189505 := bstep (se 2 (by rfl) ⟨446064, by rfl⟩ : syracuseStep 1189505 = 892129) B892129
theorem B1058435 : Blo 702318 1058435 := bstep (se 1 (by rfl) ⟨793826, by rfl⟩ : syracuseStep 1058435 = 1587653) B1587653
theorem B1058465 : Blo 702318 1058465 := bstep (se 2 (by rfl) ⟨396924, by rfl⟩ : syracuseStep 1058465 = 793849) B793849
theorem B1058483 : Blo 702318 1058483 := bstep (se 1 (by rfl) ⟨793862, by rfl⟩ : syracuseStep 1058483 = 1587725) B1587725
theorem B1058513 : Blo 702318 1058513 := bstep (se 2 (by rfl) ⟨396942, by rfl⟩ : syracuseStep 1058513 = 793885) B793885
theorem B1058531 : Blo 702318 1058531 := bstep (se 1 (by rfl) ⟨793898, by rfl⟩ : syracuseStep 1058531 = 1587797) B1587797
theorem B1189633 : Blo 702318 1189633 := bstep (se 2 (by rfl) ⟨446112, by rfl⟩ : syracuseStep 1189633 = 892225) B892225
theorem B1058561 : Blo 702318 1058561 := bstep (se 2 (by rfl) ⟨396960, by rfl⟩ : syracuseStep 1058561 = 793921) B793921
theorem B1582865 : Blo 702318 1582865 := bstep (se 2 (by rfl) ⟨593574, by rfl⟩ : syracuseStep 1582865 = 1187149) B1187149
theorem B1058579 : Blo 702318 1058579 := bstep (se 1 (by rfl) ⟨793934, by rfl⟩ : syracuseStep 1058579 = 1587869) B1587869
theorem B1582883 : Blo 702318 1582883 := bstep (se 1 (by rfl) ⟨1187162, by rfl⟩ : syracuseStep 1582883 = 2374325) B2374325
theorem B1189667 : Blo 702318 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B1058609 : Blo 702318 1058609 := bstep (se 2 (by rfl) ⟨396978, by rfl⟩ : syracuseStep 1058609 = 793957) B793957
theorem B1058627 : Blo 702318 1058627 := bstep (se 1 (by rfl) ⟨793970, by rfl⟩ : syracuseStep 1058627 = 1587941) B1587941
theorem B1058657 : Blo 702318 1058657 := bstep (se 2 (by rfl) ⟨396996, by rfl⟩ : syracuseStep 1058657 = 793993) B793993
theorem B1058675 : Blo 702318 1058675 := bstep (se 1 (by rfl) ⟨794006, by rfl⟩ : syracuseStep 1058675 = 1588013) B1588013
theorem B1058705 : Blo 702318 1058705 := bstep (se 2 (by rfl) ⟨397014, by rfl⟩ : syracuseStep 1058705 = 794029) B794029
theorem B1189795 : Blo 702318 1189795 := bstep (se 1 (by rfl) ⟨892346, by rfl⟩ : syracuseStep 1189795 = 1784693) B1784693
theorem B1058723 : Blo 702318 1058723 := bstep (se 1 (by rfl) ⟨794042, by rfl⟩ : syracuseStep 1058723 = 1588085) B1588085
theorem B1058753 : Blo 702318 1058753 := bstep (se 2 (by rfl) ⟨397032, by rfl⟩ : syracuseStep 1058753 = 794065) B794065
theorem B1058771 : Blo 702318 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B1058801 : Blo 702318 1058801 := bstep (se 2 (by rfl) ⟨397050, by rfl⟩ : syracuseStep 1058801 = 794101) B794101
theorem B1058819 : Blo 702318 1058819 := bstep (se 1 (by rfl) ⟨794114, by rfl⟩ : syracuseStep 1058819 = 1588229) B1588229
theorem B1058849 : Blo 702318 1058849 := bstep (se 2 (by rfl) ⟨397068, by rfl⟩ : syracuseStep 1058849 = 794137) B794137
theorem B1583153 : Blo 702318 1583153 := bstep (se 2 (by rfl) ⟨593682, by rfl⟩ : syracuseStep 1583153 = 1187365) B1187365
theorem B1189937 : Blo 702318 1189937 := bstep (se 2 (by rfl) ⟨446226, by rfl⟩ : syracuseStep 1189937 = 892453) B892453
theorem B1058867 : Blo 702318 1058867 := bstep (se 1 (by rfl) ⟨794150, by rfl⟩ : syracuseStep 1058867 = 1588301) B1588301
theorem B1583171 : Blo 702318 1583171 := bstep (se 1 (by rfl) ⟨1187378, by rfl⟩ : syracuseStep 1583171 = 2374757) B2374757
theorem B1058897 : Blo 702318 1058897 := bstep (se 2 (by rfl) ⟨397086, by rfl⟩ : syracuseStep 1058897 = 794173) B794173
theorem B1058915 : Blo 702318 1058915 := bstep (se 1 (by rfl) ⟨794186, by rfl⟩ : syracuseStep 1058915 = 1588373) B1588373
theorem B1058945 : Blo 702318 1058945 := bstep (se 2 (by rfl) ⟨397104, by rfl⟩ : syracuseStep 1058945 = 794209) B794209
theorem B1058963 : Blo 702318 1058963 := bstep (se 1 (by rfl) ⟨794222, by rfl⟩ : syracuseStep 1058963 = 1588445) B1588445
theorem B2009261 : Blo 702318 2009261 := bstep (se 3 (by rfl) ⟨376736, by rfl⟩ : syracuseStep 2009261 = 753473) B753473
theorem B1190065 : Blo 702318 1190065 := bstep (se 2 (by rfl) ⟨446274, by rfl⟩ : syracuseStep 1190065 = 892549) B892549
theorem B1058993 : Blo 702318 1058993 := bstep (se 2 (by rfl) ⟨397122, by rfl⟩ : syracuseStep 1058993 = 794245) B794245
theorem B1059011 : Blo 702318 1059011 := bstep (se 1 (by rfl) ⟨794258, by rfl⟩ : syracuseStep 1059011 = 1588517) B1588517
theorem B1190099 : Blo 702318 1190099 := bstep (se 1 (by rfl) ⟨892574, by rfl⟩ : syracuseStep 1190099 = 1785149) B1785149
theorem B1059041 : Blo 702318 1059041 := bstep (se 2 (by rfl) ⟨397140, by rfl⟩ : syracuseStep 1059041 = 794281) B794281
theorem B7416035 : Blo 702318 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B1059059 : Blo 702318 1059059 := bstep (se 1 (by rfl) ⟨794294, by rfl⟩ : syracuseStep 1059059 = 1588589) B1588589
theorem B3385613 : Blo 702318 3385613 := bstep (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) B1269605
theorem B1059089 : Blo 702318 1059089 := bstep (se 2 (by rfl) ⟨397158, by rfl⟩ : syracuseStep 1059089 = 794317) B794317
theorem B1059107 : Blo 702318 1059107 := bstep (se 1 (by rfl) ⟨794330, by rfl⟩ : syracuseStep 1059107 = 1588661) B1588661
theorem B1059137 : Blo 702318 1059137 := bstep (se 2 (by rfl) ⟨397176, by rfl⟩ : syracuseStep 1059137 = 794353) B794353
theorem B1583441 : Blo 702318 1583441 := bstep (se 2 (by rfl) ⟨593790, by rfl⟩ : syracuseStep 1583441 = 1187581) B1187581
theorem B1190227 : Blo 702318 1190227 := bstep (se 1 (by rfl) ⟨892670, by rfl⟩ : syracuseStep 1190227 = 1785341) B1785341
theorem B1059155 : Blo 702318 1059155 := bstep (se 1 (by rfl) ⟨794366, by rfl⟩ : syracuseStep 1059155 = 1588733) B1588733
theorem B1583459 : Blo 702318 1583459 := bstep (se 1 (by rfl) ⟨1187594, by rfl⟩ : syracuseStep 1583459 = 2375189) B2375189
theorem B2009443 : Blo 702318 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B1059185 : Blo 702318 1059185 := bstep (se 2 (by rfl) ⟨397194, by rfl⟩ : syracuseStep 1059185 = 794389) B794389
theorem B1059203 : Blo 702318 1059203 := bstep (se 1 (by rfl) ⟨794402, by rfl⟩ : syracuseStep 1059203 = 1588805) B1588805
theorem B1059233 : Blo 702318 1059233 := bstep (se 2 (by rfl) ⟨397212, by rfl⟩ : syracuseStep 1059233 = 794425) B794425
theorem B1059251 : Blo 702318 1059251 := bstep (se 1 (by rfl) ⟨794438, by rfl⟩ : syracuseStep 1059251 = 1588877) B1588877
theorem B1780177 : Blo 702318 1780177 := bstep (se 2 (by rfl) ⟨667566, by rfl⟩ : syracuseStep 1780177 = 1335133) B1335133
theorem B1059281 : Blo 702318 1059281 := bstep (se 2 (by rfl) ⟨397230, by rfl⟩ : syracuseStep 1059281 = 794461) B794461
theorem B1190369 : Blo 702318 1190369 := bstep (se 2 (by rfl) ⟨446388, by rfl⟩ : syracuseStep 1190369 = 892777) B892777
theorem B1059299 : Blo 702318 1059299 := bstep (se 1 (by rfl) ⟨794474, by rfl⟩ : syracuseStep 1059299 = 1588949) B1588949
theorem B1059329 : Blo 702318 1059329 := bstep (se 2 (by rfl) ⟨397248, by rfl⟩ : syracuseStep 1059329 = 794497) B794497
theorem B2009603 : Blo 702318 2009603 := bstep (se 1 (by rfl) ⟨1507202, by rfl⟩ : syracuseStep 2009603 = 3014405) B3014405
theorem B1059347 : Blo 702318 1059347 := bstep (se 1 (by rfl) ⟨794510, by rfl⟩ : syracuseStep 1059347 = 1589021) B1589021
theorem B1059377 : Blo 702318 1059377 := bstep (se 2 (by rfl) ⟨397266, by rfl⟩ : syracuseStep 1059377 = 794533) B794533
theorem B1059395 : Blo 702318 1059395 := bstep (se 1 (by rfl) ⟨794546, by rfl⟩ : syracuseStep 1059395 = 1589093) B1589093
theorem B1190497 : Blo 702318 1190497 := bstep (se 2 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 1190497 = 892873) B892873
theorem B1059425 : Blo 702318 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B1583729 : Blo 702318 1583729 := bstep (se 2 (by rfl) ⟨593898, by rfl⟩ : syracuseStep 1583729 = 1187797) B1187797
theorem B1059443 : Blo 702318 1059443 := bstep (se 1 (by rfl) ⟨794582, by rfl⟩ : syracuseStep 1059443 = 1589165) B1589165
theorem B1583747 : Blo 702318 1583747 := bstep (se 1 (by rfl) ⟨1187810, by rfl⟩ : syracuseStep 1583747 = 2375621) B2375621
theorem B1190531 : Blo 702318 1190531 := bstep (se 1 (by rfl) ⟨892898, by rfl⟩ : syracuseStep 1190531 = 1785797) B1785797
theorem B1059473 : Blo 702318 1059473 := bstep (se 2 (by rfl) ⟨397302, by rfl⟩ : syracuseStep 1059473 = 794605) B794605
theorem B1157809 : Blo 702318 1157809 := bstep (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) B868357
theorem B1780451 : Blo 702318 1780451 := bstep (se 1 (by rfl) ⟨1335338, by rfl⟩ : syracuseStep 1780451 = 2670677) B2670677
theorem B1190659 : Blo 702318 1190659 := bstep (se 1 (by rfl) ⟨892994, by rfl⟩ : syracuseStep 1190659 = 1785989) B1785989
theorem B2534179 : Blo 702318 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B1584017 : Blo 702318 1584017 := bstep (se 2 (by rfl) ⟨594006, by rfl⟩ : syracuseStep 1584017 = 1188013) B1188013
theorem B1190801 : Blo 702318 1190801 := bstep (se 2 (by rfl) ⟨446550, by rfl⟩ : syracuseStep 1190801 = 893101) B893101
theorem B1780643 : Blo 702318 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B1584035 : Blo 702318 1584035 := bstep (se 1 (by rfl) ⟨1188026, by rfl⟩ : syracuseStep 1584035 = 2376053) B2376053
theorem B2370545 : Blo 702318 2370545 := bstep (se 2 (by rfl) ⟨888954, by rfl⟩ : syracuseStep 2370545 = 1777909) B1777909
theorem B1190929 : Blo 702318 1190929 := bstep (se 2 (by rfl) ⟨446598, by rfl⟩ : syracuseStep 1190929 = 893197) B893197
theorem B1190963 : Blo 702318 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B1584305 : Blo 702318 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B1191091 : Blo 702318 1191091 := bstep (se 1 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 1191091 = 1786637) B1786637
theorem B1125571 : Blo 702318 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B1584323 : Blo 702318 1584323 := bstep (se 1 (by rfl) ⟨1188242, by rfl⟩ : syracuseStep 1584323 = 2376485) B2376485
theorem B1125667 : Blo 702318 1125667 := bstep (se 1 (by rfl) ⟨844250, by rfl⟩ : syracuseStep 1125667 = 1688501) B1688501
theorem B1191233 : Blo 702318 1191233 := bstep (se 2 (by rfl) ⟨446712, by rfl⟩ : syracuseStep 1191233 = 893425) B893425
theorem B5352803 : Blo 702318 5352803 := bstep (se 1 (by rfl) ⟨4014602, by rfl⟩ : syracuseStep 5352803 = 8029205) B8029205
theorem B1191361 : Blo 702318 1191361 := bstep (se 2 (by rfl) ⟨446760, by rfl⟩ : syracuseStep 1191361 = 893521) B893521
theorem B1125827 : Blo 702318 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B3812813 : Blo 702318 3812813 := bstep (se 3 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 3812813 = 1429805) B1429805
theorem B1584593 : Blo 702318 1584593 := bstep (se 2 (by rfl) ⟨594222, by rfl⟩ : syracuseStep 1584593 = 1188445) B1188445
theorem B1584611 : Blo 702318 1584611 := bstep (se 1 (by rfl) ⟨1188458, by rfl⟩ : syracuseStep 1584611 = 2376917) B2376917
theorem B1191395 : Blo 702318 1191395 := bstep (se 1 (by rfl) ⟨893546, by rfl⟩ : syracuseStep 1191395 = 1787093) B1787093
theorem B2371085 : Blo 702318 2371085 := bstep (se 3 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 2371085 = 889157) B889157
theorem B2010673 : Blo 702318 2010673 := bstep (se 2 (by rfl) ⟨754002, by rfl⟩ : syracuseStep 2010673 = 1508005) B1508005
theorem B2371139 : Blo 702318 2371139 := bstep (se 1 (by rfl) ⟨1778354, by rfl⟩ : syracuseStep 2371139 = 3556709) B3556709
theorem B1191523 : Blo 702318 1191523 := bstep (se 1 (by rfl) ⟨893642, by rfl⟩ : syracuseStep 1191523 = 1787285) B1787285
theorem B1584881 : Blo 702318 1584881 := bstep (se 2 (by rfl) ⟨594330, by rfl⟩ : syracuseStep 1584881 = 1188661) B1188661
theorem B1191665 : Blo 702318 1191665 := bstep (se 2 (by rfl) ⟨446874, by rfl⟩ : syracuseStep 1191665 = 893749) B893749
theorem B1584899 : Blo 702318 1584899 := bstep (se 1 (by rfl) ⟨1188674, by rfl⟩ : syracuseStep 1584899 = 2377349) B2377349
theorem B2371409 : Blo 702318 2371409 := bstep (se 2 (by rfl) ⟨889278, by rfl⟩ : syracuseStep 2371409 = 1778557) B1778557
theorem B1781585 : Blo 702318 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B1191793 : Blo 702318 1191793 := bstep (se 2 (by rfl) ⟨446922, by rfl⟩ : syracuseStep 1191793 = 893845) B893845
theorem B1781635 : Blo 702318 1781635 := bstep (se 1 (by rfl) ⟨1336226, by rfl⟩ : syracuseStep 1781635 = 2672453) B2672453
theorem B1191827 : Blo 702318 1191827 := bstep (se 1 (by rfl) ⟨893870, by rfl⟩ : syracuseStep 1191827 = 1787741) B1787741
theorem B3813317 : Blo 702318 3813317 := bstep (se 4 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 3813317 = 714997) B714997
theorem B2142179 : Blo 702318 2142179 := bstep (se 1 (by rfl) ⟨1606634, by rfl⟩ : syracuseStep 2142179 = 3213269) B3213269
theorem B1781777 : Blo 702318 1781777 := bstep (se 2 (by rfl) ⟨668166, by rfl⟩ : syracuseStep 1781777 = 1336333) B1336333
theorem B1585169 : Blo 702318 1585169 := bstep (se 2 (by rfl) ⟨594438, by rfl⟩ : syracuseStep 1585169 = 1188877) B1188877
theorem B1585187 : Blo 702318 1585187 := bstep (se 1 (by rfl) ⟨1188890, by rfl⟩ : syracuseStep 1585187 = 2377781) B2377781
theorem B2404397 : Blo 702318 2404397 := bstep (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) B901649
theorem B1585457 : Blo 702318 1585457 := bstep (se 2 (by rfl) ⟨594546, by rfl⟩ : syracuseStep 1585457 = 1189093) B1189093
theorem B1585475 : Blo 702318 1585475 := bstep (se 1 (by rfl) ⟨1189106, by rfl⟩ : syracuseStep 1585475 = 2378213) B2378213
theorem B2371949 : Blo 702318 2371949 := bstep (se 3 (by rfl) ⟨444740, by rfl⟩ : syracuseStep 2371949 = 889481) B889481
theorem B1126801 : Blo 702318 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B2372003 : Blo 702318 2372003 := bstep (se 1 (by rfl) ⟨1779002, by rfl⟩ : syracuseStep 2372003 = 3558005) B3558005
theorem B6009329 : Blo 702318 6009329 := bstep (se 2 (by rfl) ⟨2253498, by rfl⟩ : syracuseStep 6009329 = 4506997) B4506997
theorem B1061363 : Blo 702318 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1585745 : Blo 702318 1585745 := bstep (se 2 (by rfl) ⟨594654, by rfl⟩ : syracuseStep 1585745 = 1189309) B1189309
theorem B2667107 : Blo 702318 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B1585763 : Blo 702318 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B2372273 : Blo 702318 2372273 := bstep (se 2 (by rfl) ⟨889602, by rfl⟩ : syracuseStep 2372273 = 1779205) B1779205
theorem B4633357 : Blo 702318 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B1586033 : Blo 702318 1586033 := bstep (se 2 (by rfl) ⟨594762, by rfl⟩ : syracuseStep 1586033 = 1189525) B1189525
theorem B1586051 : Blo 702318 1586051 := bstep (se 1 (by rfl) ⟨1189538, by rfl⟩ : syracuseStep 1586051 = 2379077) B2379077
theorem B1782769 : Blo 702318 1782769 := bstep (se 2 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 1782769 = 1337077) B1337077
theorem B1586321 : Blo 702318 1586321 := bstep (se 2 (by rfl) ⟨594870, by rfl⟩ : syracuseStep 1586321 = 1189741) B1189741
theorem B1586339 : Blo 702318 1586339 := bstep (se 1 (by rfl) ⟨1189754, by rfl⟩ : syracuseStep 1586339 = 2379509) B2379509
theorem B2372813 : Blo 702318 2372813 := bstep (se 3 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 2372813 = 889805) B889805
theorem B2667761 : Blo 702318 2667761 := bstep (se 2 (by rfl) ⟨1000410, by rfl⟩ : syracuseStep 2667761 = 2000821) B2000821
theorem B2372867 : Blo 702318 2372867 := bstep (se 1 (by rfl) ⟨1779650, by rfl⟩ : syracuseStep 2372867 = 3559301) B3559301
theorem B1783043 : Blo 702318 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B5715299 : Blo 702318 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B4502897 : Blo 702318 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B1717649 : Blo 702318 1717649 := bstep (se 2 (by rfl) ⟨644118, by rfl⟩ : syracuseStep 1717649 = 1288237) B1288237
theorem B1586609 : Blo 702318 1586609 := bstep (se 2 (by rfl) ⟨594978, by rfl⟩ : syracuseStep 1586609 = 1189957) B1189957
theorem B1783235 : Blo 702318 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B1586627 : Blo 702318 1586627 := bstep (se 1 (by rfl) ⟨1189970, by rfl⟩ : syracuseStep 1586627 = 2379941) B2379941
theorem B2373137 : Blo 702318 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B3815045 : Blo 702318 3815045 := bstep (se 4 (by rfl) ⟨357660, by rfl⟩ : syracuseStep 3815045 = 715321) B715321
theorem B1586897 : Blo 702318 1586897 := bstep (se 2 (by rfl) ⟨595086, by rfl⟩ : syracuseStep 1586897 = 1190173) B1190173
theorem B1586915 : Blo 702318 1586915 := bstep (se 1 (by rfl) ⟨1190186, by rfl⟩ : syracuseStep 1586915 = 2380373) B2380373
theorem B702323 : Blo 702318 702323 := bstep (se 1 (by rfl) ⟨526742, by rfl⟩ : syracuseStep 702323 = 1053485) B1053485
theorem B702339 : Blo 702318 702339 := bstep (se 1 (by rfl) ⟨526754, by rfl⟩ : syracuseStep 702339 = 1053509) B1053509
theorem B702355 : Blo 702318 702355 := bstep (se 1 (by rfl) ⟨526766, by rfl⟩ : syracuseStep 702355 = 1053533) B1053533
theorem B702371 : Blo 702318 702371 := bstep (se 1 (by rfl) ⟨526778, by rfl⟩ : syracuseStep 702371 = 1053557) B1053557
theorem B702387 : Blo 702318 702387 := bstep (se 1 (by rfl) ⟨526790, by rfl⟩ : syracuseStep 702387 = 1053581) B1053581
theorem B702403 : Blo 702318 702403 := bstep (se 1 (by rfl) ⟨526802, by rfl⟩ : syracuseStep 702403 = 1053605) B1053605
theorem B702419 : Blo 702318 702419 := bstep (se 1 (by rfl) ⟨526814, by rfl⟩ : syracuseStep 702419 = 1053629) B1053629
theorem B702435 : Blo 702318 702435 := bstep (se 1 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 702435 = 1053653) B1053653
theorem B1587185 : Blo 702318 1587185 := bstep (se 2 (by rfl) ⟨595194, by rfl⟩ : syracuseStep 1587185 = 1190389) B1190389
theorem B702451 : Blo 702318 702451 := bstep (se 1 (by rfl) ⟨526838, by rfl⟩ : syracuseStep 702451 = 1053677) B1053677
theorem B702467 : Blo 702318 702467 := bstep (se 1 (by rfl) ⟨526850, by rfl⟩ : syracuseStep 702467 = 1053701) B1053701
theorem B1587203 : Blo 702318 1587203 := bstep (se 1 (by rfl) ⟨1190402, by rfl⟩ : syracuseStep 1587203 = 2380805) B2380805
theorem B1128467 : Blo 702318 1128467 := bstep (se 1 (by rfl) ⟨846350, by rfl⟩ : syracuseStep 1128467 = 1692701) B1692701
theorem B702483 : Blo 702318 702483 := bstep (se 1 (by rfl) ⟨526862, by rfl⟩ : syracuseStep 702483 = 1053725) B1053725
theorem B702499 : Blo 702318 702499 := bstep (se 1 (by rfl) ⟨526874, by rfl⟩ : syracuseStep 702499 = 1053749) B1053749
theorem B2373677 : Blo 702318 2373677 := bstep (se 3 (by rfl) ⟨445064, by rfl⟩ : syracuseStep 2373677 = 890129) B890129
theorem B702515 : Blo 702318 702515 := bstep (se 1 (by rfl) ⟨526886, by rfl⟩ : syracuseStep 702515 = 1053773) B1053773
theorem B702531 : Blo 702318 702531 := bstep (se 1 (by rfl) ⟨526898, by rfl⟩ : syracuseStep 702531 = 1053797) B1053797
theorem B702547 : Blo 702318 702547 := bstep (se 1 (by rfl) ⟨526910, by rfl⟩ : syracuseStep 702547 = 1053821) B1053821
theorem B702563 : Blo 702318 702563 := bstep (se 1 (by rfl) ⟨526922, by rfl⟩ : syracuseStep 702563 = 1053845) B1053845
theorem B2373731 : Blo 702318 2373731 := bstep (se 1 (by rfl) ⟨1780298, by rfl⟩ : syracuseStep 2373731 = 3560597) B3560597
theorem B702579 : Blo 702318 702579 := bstep (se 1 (by rfl) ⟨526934, by rfl⟩ : syracuseStep 702579 = 1053869) B1053869
theorem B702595 : Blo 702318 702595 := bstep (se 1 (by rfl) ⟨526946, by rfl⟩ : syracuseStep 702595 = 1053893) B1053893
theorem B702611 : Blo 702318 702611 := bstep (se 1 (by rfl) ⟨526958, by rfl⟩ : syracuseStep 702611 = 1053917) B1053917
theorem B1128595 : Blo 702318 1128595 := bstep (se 1 (by rfl) ⟨846446, by rfl⟩ : syracuseStep 1128595 = 1692893) B1692893
theorem B702627 : Blo 702318 702627 := bstep (se 1 (by rfl) ⟨526970, by rfl⟩ : syracuseStep 702627 = 1053941) B1053941
theorem B702643 : Blo 702318 702643 := bstep (se 1 (by rfl) ⟨526982, by rfl⟩ : syracuseStep 702643 = 1053965) B1053965
theorem B702659 : Blo 702318 702659 := bstep (se 1 (by rfl) ⟨526994, by rfl⟩ : syracuseStep 702659 = 1053989) B1053989
theorem B702675 : Blo 702318 702675 := bstep (se 1 (by rfl) ⟨527006, by rfl⟩ : syracuseStep 702675 = 1054013) B1054013
theorem B1128659 : Blo 702318 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B702691 : Blo 702318 702691 := bstep (se 1 (by rfl) ⟨527018, by rfl⟩ : syracuseStep 702691 = 1054037) B1054037
theorem B702707 : Blo 702318 702707 := bstep (se 1 (by rfl) ⟨527030, by rfl⟩ : syracuseStep 702707 = 1054061) B1054061
theorem B702723 : Blo 702318 702723 := bstep (se 1 (by rfl) ⟨527042, by rfl⟩ : syracuseStep 702723 = 1054085) B1054085
theorem B1587473 : Blo 702318 1587473 := bstep (se 2 (by rfl) ⟨595302, by rfl⟩ : syracuseStep 1587473 = 1190605) B1190605
theorem B702739 : Blo 702318 702739 := bstep (se 1 (by rfl) ⟨527054, by rfl⟩ : syracuseStep 702739 = 1054109) B1054109
theorem B702755 : Blo 702318 702755 := bstep (se 1 (by rfl) ⟨527066, by rfl⟩ : syracuseStep 702755 = 1054133) B1054133
theorem B1587491 : Blo 702318 1587491 := bstep (se 1 (by rfl) ⟨1190618, by rfl⟩ : syracuseStep 1587491 = 2381237) B2381237
theorem B702771 : Blo 702318 702771 := bstep (se 1 (by rfl) ⟨527078, by rfl⟩ : syracuseStep 702771 = 1054157) B1054157
theorem B702787 : Blo 702318 702787 := bstep (se 1 (by rfl) ⟨527090, by rfl⟩ : syracuseStep 702787 = 1054181) B1054181
theorem B702803 : Blo 702318 702803 := bstep (se 1 (by rfl) ⟨527102, by rfl⟩ : syracuseStep 702803 = 1054205) B1054205
theorem B702819 : Blo 702318 702819 := bstep (se 1 (by rfl) ⟨527114, by rfl⟩ : syracuseStep 702819 = 1054229) B1054229
theorem B2374001 : Blo 702318 2374001 := bstep (se 2 (by rfl) ⟨890250, by rfl⟩ : syracuseStep 2374001 = 1780501) B1780501
theorem B1784177 : Blo 702318 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B702835 : Blo 702318 702835 := bstep (se 1 (by rfl) ⟨527126, by rfl⟩ : syracuseStep 702835 = 1054253) B1054253
theorem B702851 : Blo 702318 702851 := bstep (se 1 (by rfl) ⟨527138, by rfl⟩ : syracuseStep 702851 = 1054277) B1054277
theorem B702867 : Blo 702318 702867 := bstep (se 1 (by rfl) ⟨527150, by rfl⟩ : syracuseStep 702867 = 1054301) B1054301
theorem B702883 : Blo 702318 702883 := bstep (se 1 (by rfl) ⟨527162, by rfl⟩ : syracuseStep 702883 = 1054325) B1054325
theorem B1784227 : Blo 702318 1784227 := bstep (se 1 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 1784227 = 2676341) B2676341
theorem B702899 : Blo 702318 702899 := bstep (se 1 (by rfl) ⟨527174, by rfl⟩ : syracuseStep 702899 = 1054349) B1054349
theorem B702915 : Blo 702318 702915 := bstep (se 1 (by rfl) ⟨527186, by rfl⟩ : syracuseStep 702915 = 1054373) B1054373
theorem B702931 : Blo 702318 702931 := bstep (se 1 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 702931 = 1054397) B1054397
theorem B702947 : Blo 702318 702947 := bstep (se 1 (by rfl) ⟨527210, by rfl⟩ : syracuseStep 702947 = 1054421) B1054421
theorem B702963 : Blo 702318 702963 := bstep (se 1 (by rfl) ⟨527222, by rfl⟩ : syracuseStep 702963 = 1054445) B1054445
theorem B702979 : Blo 702318 702979 := bstep (se 1 (by rfl) ⟨527234, by rfl⟩ : syracuseStep 702979 = 1054469) B1054469
theorem B702995 : Blo 702318 702995 := bstep (se 1 (by rfl) ⟨527246, by rfl⟩ : syracuseStep 702995 = 1054493) B1054493
theorem B703011 : Blo 702318 703011 := bstep (se 1 (by rfl) ⟨527258, by rfl⟩ : syracuseStep 703011 = 1054517) B1054517
theorem B1784369 : Blo 702318 1784369 := bstep (se 2 (by rfl) ⟨669138, by rfl⟩ : syracuseStep 1784369 = 1338277) B1338277
theorem B1587761 : Blo 702318 1587761 := bstep (se 2 (by rfl) ⟨595410, by rfl⟩ : syracuseStep 1587761 = 1190821) B1190821
theorem B703027 : Blo 702318 703027 := bstep (se 1 (by rfl) ⟨527270, by rfl⟩ : syracuseStep 703027 = 1054541) B1054541
theorem B703043 : Blo 702318 703043 := bstep (se 1 (by rfl) ⟨527282, by rfl⟩ : syracuseStep 703043 = 1054565) B1054565
theorem B1587779 : Blo 702318 1587779 := bstep (se 1 (by rfl) ⟨1190834, by rfl⟩ : syracuseStep 1587779 = 2381669) B2381669
theorem B965201 : Blo 702318 965201 := bstep (se 2 (by rfl) ⟨361950, by rfl⟩ : syracuseStep 965201 = 723901) B723901
theorem B703059 : Blo 702318 703059 := bstep (se 1 (by rfl) ⟨527294, by rfl⟩ : syracuseStep 703059 = 1054589) B1054589
theorem B703075 : Blo 702318 703075 := bstep (se 1 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 703075 = 1054613) B1054613
theorem B4274801 : Blo 702318 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B703091 : Blo 702318 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B703107 : Blo 702318 703107 := bstep (se 1 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 703107 = 1054661) B1054661
theorem B703123 : Blo 702318 703123 := bstep (se 1 (by rfl) ⟨527342, by rfl⟩ : syracuseStep 703123 = 1054685) B1054685
theorem B2669219 : Blo 702318 2669219 := bstep (se 1 (by rfl) ⟨2001914, by rfl⟩ : syracuseStep 2669219 = 4003829) B4003829
theorem B703139 : Blo 702318 703139 := bstep (se 1 (by rfl) ⟨527354, by rfl⟩ : syracuseStep 703139 = 1054709) B1054709
theorem B2669233 : Blo 702318 2669233 := bstep (se 2 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 2669233 = 2001925) B2001925
theorem B703155 : Blo 702318 703155 := bstep (se 1 (by rfl) ⟨527366, by rfl⟩ : syracuseStep 703155 = 1054733) B1054733
theorem B1129153 : Blo 702318 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B703171 : Blo 702318 703171 := bstep (se 1 (by rfl) ⟨527378, by rfl⟩ : syracuseStep 703171 = 1054757) B1054757
theorem B6273733 : Blo 702318 6273733 := bstep (se 4 (by rfl) ⟨588162, by rfl⟩ : syracuseStep 6273733 = 1176325) B1176325
theorem B703187 : Blo 702318 703187 := bstep (se 1 (by rfl) ⟨527390, by rfl⟩ : syracuseStep 703187 = 1054781) B1054781
theorem B703203 : Blo 702318 703203 := bstep (se 1 (by rfl) ⟨527402, by rfl⟩ : syracuseStep 703203 = 1054805) B1054805
theorem B703219 : Blo 702318 703219 := bstep (se 1 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 703219 = 1054829) B1054829
theorem B703235 : Blo 702318 703235 := bstep (se 1 (by rfl) ⟨527426, by rfl⟩ : syracuseStep 703235 = 1054853) B1054853
theorem B703251 : Blo 702318 703251 := bstep (se 1 (by rfl) ⟨527438, by rfl⟩ : syracuseStep 703251 = 1054877) B1054877
theorem B703267 : Blo 702318 703267 := bstep (se 1 (by rfl) ⟨527450, by rfl⟩ : syracuseStep 703267 = 1054901) B1054901
theorem B703283 : Blo 702318 703283 := bstep (se 1 (by rfl) ⟨527462, by rfl⟩ : syracuseStep 703283 = 1054925) B1054925
theorem B703299 : Blo 702318 703299 := bstep (se 1 (by rfl) ⟨527474, by rfl⟩ : syracuseStep 703299 = 1054949) B1054949
theorem B4275013 : Blo 702318 4275013 := bstep (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) B801565
theorem B1588049 : Blo 702318 1588049 := bstep (se 2 (by rfl) ⟨595518, by rfl⟩ : syracuseStep 1588049 = 1191037) B1191037
theorem B703315 : Blo 702318 703315 := bstep (se 1 (by rfl) ⟨527486, by rfl⟩ : syracuseStep 703315 = 1054973) B1054973
theorem B703331 : Blo 702318 703331 := bstep (se 1 (by rfl) ⟨527498, by rfl⟩ : syracuseStep 703331 = 1054997) B1054997
theorem B1588067 : Blo 702318 1588067 := bstep (se 1 (by rfl) ⟨1191050, by rfl⟩ : syracuseStep 1588067 = 2382101) B2382101
theorem B703347 : Blo 702318 703347 := bstep (se 1 (by rfl) ⟨527510, by rfl⟩ : syracuseStep 703347 = 1055021) B1055021
theorem B703363 : Blo 702318 703363 := bstep (se 1 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 703363 = 1055045) B1055045
theorem B2374541 : Blo 702318 2374541 := bstep (se 3 (by rfl) ⟨445226, by rfl⟩ : syracuseStep 2374541 = 890453) B890453
theorem B703379 : Blo 702318 703379 := bstep (se 1 (by rfl) ⟨527534, by rfl⟩ : syracuseStep 703379 = 1055069) B1055069
theorem B703395 : Blo 702318 703395 := bstep (se 1 (by rfl) ⟨527546, by rfl⟩ : syracuseStep 703395 = 1055093) B1055093
theorem B2145197 : Blo 702318 2145197 := bstep (se 3 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 2145197 = 804449) B804449
theorem B703411 : Blo 702318 703411 := bstep (se 1 (by rfl) ⟨527558, by rfl⟩ : syracuseStep 703411 = 1055117) B1055117
theorem B703427 : Blo 702318 703427 := bstep (se 1 (by rfl) ⟨527570, by rfl⟩ : syracuseStep 703427 = 1055141) B1055141
theorem B2374595 : Blo 702318 2374595 := bstep (se 1 (by rfl) ⟨1780946, by rfl⟩ : syracuseStep 2374595 = 3561893) B3561893
theorem B703443 : Blo 702318 703443 := bstep (se 1 (by rfl) ⟨527582, by rfl⟩ : syracuseStep 703443 = 1055165) B1055165
theorem B703459 : Blo 702318 703459 := bstep (se 1 (by rfl) ⟨527594, by rfl⟩ : syracuseStep 703459 = 1055189) B1055189
theorem B703475 : Blo 702318 703475 := bstep (se 1 (by rfl) ⟨527606, by rfl⟩ : syracuseStep 703475 = 1055213) B1055213
theorem B703491 : Blo 702318 703491 := bstep (se 1 (by rfl) ⟨527618, by rfl⟩ : syracuseStep 703491 = 1055237) B1055237
theorem B703507 : Blo 702318 703507 := bstep (se 1 (by rfl) ⟨527630, by rfl⟩ : syracuseStep 703507 = 1055261) B1055261
theorem B703523 : Blo 702318 703523 := bstep (se 1 (by rfl) ⟨527642, by rfl⟩ : syracuseStep 703523 = 1055285) B1055285
theorem B703539 : Blo 702318 703539 := bstep (se 1 (by rfl) ⟨527654, by rfl⟩ : syracuseStep 703539 = 1055309) B1055309
theorem B703555 : Blo 702318 703555 := bstep (se 1 (by rfl) ⟨527666, by rfl⟩ : syracuseStep 703555 = 1055333) B1055333
theorem B703571 : Blo 702318 703571 := bstep (se 1 (by rfl) ⟨527678, by rfl⟩ : syracuseStep 703571 = 1055357) B1055357
theorem B703587 : Blo 702318 703587 := bstep (se 1 (by rfl) ⟨527690, by rfl⟩ : syracuseStep 703587 = 1055381) B1055381
theorem B1588337 : Blo 702318 1588337 := bstep (se 2 (by rfl) ⟨595626, by rfl⟩ : syracuseStep 1588337 = 1191253) B1191253
theorem B703603 : Blo 702318 703603 := bstep (se 1 (by rfl) ⟨527702, by rfl⟩ : syracuseStep 703603 = 1055405) B1055405
theorem B703619 : Blo 702318 703619 := bstep (se 1 (by rfl) ⟨527714, by rfl⟩ : syracuseStep 703619 = 1055429) B1055429
theorem B1588355 : Blo 702318 1588355 := bstep (se 1 (by rfl) ⟨1191266, by rfl⟩ : syracuseStep 1588355 = 2382533) B2382533
theorem B703635 : Blo 702318 703635 := bstep (se 1 (by rfl) ⟨527726, by rfl⟩ : syracuseStep 703635 = 1055453) B1055453
theorem B3128483 : Blo 702318 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B703651 : Blo 702318 703651 := bstep (se 1 (by rfl) ⟨527738, by rfl⟩ : syracuseStep 703651 = 1055477) B1055477
theorem B703667 : Blo 702318 703667 := bstep (se 1 (by rfl) ⟨527750, by rfl⟩ : syracuseStep 703667 = 1055501) B1055501
theorem B703683 : Blo 702318 703683 := bstep (se 1 (by rfl) ⟨527762, by rfl⟩ : syracuseStep 703683 = 1055525) B1055525
theorem B2374865 : Blo 702318 2374865 := bstep (se 2 (by rfl) ⟨890574, by rfl⟩ : syracuseStep 2374865 = 1781149) B1781149
theorem B703699 : Blo 702318 703699 := bstep (se 1 (by rfl) ⟨527774, by rfl⟩ : syracuseStep 703699 = 1055549) B1055549
theorem B703715 : Blo 702318 703715 := bstep (se 1 (by rfl) ⟨527786, by rfl⟩ : syracuseStep 703715 = 1055573) B1055573
theorem B703731 : Blo 702318 703731 := bstep (se 1 (by rfl) ⟨527798, by rfl⟩ : syracuseStep 703731 = 1055597) B1055597
theorem B703747 : Blo 702318 703747 := bstep (se 1 (by rfl) ⟨527810, by rfl⟩ : syracuseStep 703747 = 1055621) B1055621
theorem B703763 : Blo 702318 703763 := bstep (se 1 (by rfl) ⟨527822, by rfl⟩ : syracuseStep 703763 = 1055645) B1055645
theorem B703779 : Blo 702318 703779 := bstep (se 1 (by rfl) ⟨527834, by rfl⟩ : syracuseStep 703779 = 1055669) B1055669
theorem B703795 : Blo 702318 703795 := bstep (se 1 (by rfl) ⟨527846, by rfl⟩ : syracuseStep 703795 = 1055693) B1055693
theorem B703811 : Blo 702318 703811 := bstep (se 1 (by rfl) ⟨527858, by rfl⟩ : syracuseStep 703811 = 1055717) B1055717
theorem B703827 : Blo 702318 703827 := bstep (se 1 (by rfl) ⟨527870, by rfl⟩ : syracuseStep 703827 = 1055741) B1055741
theorem B1129825 : Blo 702318 1129825 := bstep (se 2 (by rfl) ⟨423684, by rfl⟩ : syracuseStep 1129825 = 847369) B847369
theorem B703843 : Blo 702318 703843 := bstep (se 1 (by rfl) ⟨527882, by rfl⟩ : syracuseStep 703843 = 1055765) B1055765
theorem B703859 : Blo 702318 703859 := bstep (se 1 (by rfl) ⟨527894, by rfl⟩ : syracuseStep 703859 = 1055789) B1055789
theorem B703875 : Blo 702318 703875 := bstep (se 1 (by rfl) ⟨527906, by rfl⟩ : syracuseStep 703875 = 1055813) B1055813
theorem B1588625 : Blo 702318 1588625 := bstep (se 2 (by rfl) ⟨595734, by rfl⟩ : syracuseStep 1588625 = 1191469) B1191469
theorem B703891 : Blo 702318 703891 := bstep (se 1 (by rfl) ⟨527918, by rfl⟩ : syracuseStep 703891 = 1055837) B1055837
theorem B703907 : Blo 702318 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B1588643 : Blo 702318 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B3816881 : Blo 702318 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B703923 : Blo 702318 703923 := bstep (se 1 (by rfl) ⟨527942, by rfl⟩ : syracuseStep 703923 = 1055885) B1055885
theorem B703939 : Blo 702318 703939 := bstep (se 1 (by rfl) ⟨527954, by rfl⟩ : syracuseStep 703939 = 1055909) B1055909
theorem B4013509 : Blo 702318 4013509 := bstep (se 4 (by rfl) ⟨376266, by rfl⟩ : syracuseStep 4013509 = 752533) B752533
theorem B703955 : Blo 702318 703955 := bstep (se 1 (by rfl) ⟨527966, by rfl⟩ : syracuseStep 703955 = 1055933) B1055933
theorem B703971 : Blo 702318 703971 := bstep (se 1 (by rfl) ⟨527978, by rfl⟩ : syracuseStep 703971 = 1055957) B1055957
theorem B703987 : Blo 702318 703987 := bstep (se 1 (by rfl) ⟨527990, by rfl⟩ : syracuseStep 703987 = 1055981) B1055981
theorem B704003 : Blo 702318 704003 := bstep (se 1 (by rfl) ⟨528002, by rfl⟩ : syracuseStep 704003 = 1056005) B1056005
theorem B3816965 : Blo 702318 3816965 := bstep (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) B715681
theorem B1785361 : Blo 702318 1785361 := bstep (se 2 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 1785361 = 1339021) B1339021
theorem B704019 : Blo 702318 704019 := bstep (se 1 (by rfl) ⟨528014, by rfl⟩ : syracuseStep 704019 = 1056029) B1056029
theorem B704035 : Blo 702318 704035 := bstep (se 1 (by rfl) ⟨528026, by rfl⟩ : syracuseStep 704035 = 1056053) B1056053
theorem B704051 : Blo 702318 704051 := bstep (se 1 (by rfl) ⟨528038, by rfl⟩ : syracuseStep 704051 = 1056077) B1056077
theorem B704067 : Blo 702318 704067 := bstep (se 1 (by rfl) ⟨528050, by rfl⟩ : syracuseStep 704067 = 1056101) B1056101
theorem B704083 : Blo 702318 704083 := bstep (se 1 (by rfl) ⟨528062, by rfl⟩ : syracuseStep 704083 = 1056125) B1056125
theorem B704099 : Blo 702318 704099 := bstep (se 1 (by rfl) ⟨528074, by rfl⟩ : syracuseStep 704099 = 1056149) B1056149
theorem B704115 : Blo 702318 704115 := bstep (se 1 (by rfl) ⟨528086, by rfl⟩ : syracuseStep 704115 = 1056173) B1056173
theorem B704131 : Blo 702318 704131 := bstep (se 1 (by rfl) ⟨528098, by rfl⟩ : syracuseStep 704131 = 1056197) B1056197
theorem B704147 : Blo 702318 704147 := bstep (se 1 (by rfl) ⟨528110, by rfl⟩ : syracuseStep 704147 = 1056221) B1056221
theorem B704163 : Blo 702318 704163 := bstep (se 1 (by rfl) ⟨528122, by rfl⟩ : syracuseStep 704163 = 1056245) B1056245
theorem B1588913 : Blo 702318 1588913 := bstep (se 2 (by rfl) ⟨595842, by rfl⟩ : syracuseStep 1588913 = 1191685) B1191685
theorem B704179 : Blo 702318 704179 := bstep (se 1 (by rfl) ⟨528134, by rfl⟩ : syracuseStep 704179 = 1056269) B1056269
theorem B704195 : Blo 702318 704195 := bstep (se 1 (by rfl) ⟨528146, by rfl⟩ : syracuseStep 704195 = 1056293) B1056293
theorem B1588931 : Blo 702318 1588931 := bstep (se 1 (by rfl) ⟨1191698, by rfl⟩ : syracuseStep 1588931 = 2383397) B2383397
theorem B704211 : Blo 702318 704211 := bstep (se 1 (by rfl) ⟨528158, by rfl⟩ : syracuseStep 704211 = 1056317) B1056317
theorem B704227 : Blo 702318 704227 := bstep (se 1 (by rfl) ⟨528170, by rfl⟩ : syracuseStep 704227 = 1056341) B1056341
theorem B2375405 : Blo 702318 2375405 := bstep (se 3 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 2375405 = 890777) B890777
theorem B704243 : Blo 702318 704243 := bstep (se 1 (by rfl) ⟨528182, by rfl⟩ : syracuseStep 704243 = 1056365) B1056365
theorem B704259 : Blo 702318 704259 := bstep (se 1 (by rfl) ⟨528194, by rfl⟩ : syracuseStep 704259 = 1056389) B1056389
theorem B4505357 : Blo 702318 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B704275 : Blo 702318 704275 := bstep (se 1 (by rfl) ⟨528206, by rfl⟩ : syracuseStep 704275 = 1056413) B1056413
theorem B2375459 : Blo 702318 2375459 := bstep (se 1 (by rfl) ⟨1781594, by rfl⟩ : syracuseStep 2375459 = 3563189) B3563189
theorem B704291 : Blo 702318 704291 := bstep (se 1 (by rfl) ⟨528218, by rfl⟩ : syracuseStep 704291 = 1056437) B1056437
theorem B1785635 : Blo 702318 1785635 := bstep (se 1 (by rfl) ⟨1339226, by rfl⟩ : syracuseStep 1785635 = 2678453) B2678453
theorem B704307 : Blo 702318 704307 := bstep (se 1 (by rfl) ⟨528230, by rfl⟩ : syracuseStep 704307 = 1056461) B1056461
theorem B704323 : Blo 702318 704323 := bstep (se 1 (by rfl) ⟨528242, by rfl⟩ : syracuseStep 704323 = 1056485) B1056485
theorem B704339 : Blo 702318 704339 := bstep (se 1 (by rfl) ⟨528254, by rfl⟩ : syracuseStep 704339 = 1056509) B1056509
theorem B704355 : Blo 702318 704355 := bstep (se 1 (by rfl) ⟨528266, by rfl⟩ : syracuseStep 704355 = 1056533) B1056533
theorem B704371 : Blo 702318 704371 := bstep (se 1 (by rfl) ⟨528278, by rfl⟩ : syracuseStep 704371 = 1056557) B1056557
theorem B704387 : Blo 702318 704387 := bstep (se 1 (by rfl) ⟨528290, by rfl⟩ : syracuseStep 704387 = 1056581) B1056581
theorem B704403 : Blo 702318 704403 := bstep (se 1 (by rfl) ⟨528302, by rfl⟩ : syracuseStep 704403 = 1056605) B1056605
theorem B704419 : Blo 702318 704419 := bstep (se 1 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 704419 = 1056629) B1056629
theorem B2539441 : Blo 702318 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B704435 : Blo 702318 704435 := bstep (se 1 (by rfl) ⟨528326, by rfl⟩ : syracuseStep 704435 = 1056653) B1056653
theorem B1425347 : Blo 702318 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B704451 : Blo 702318 704451 := bstep (se 1 (by rfl) ⟨528338, by rfl⟩ : syracuseStep 704451 = 1056677) B1056677
theorem B1589201 : Blo 702318 1589201 := bstep (se 2 (by rfl) ⟨595950, by rfl⟩ : syracuseStep 1589201 = 1191901) B1191901
theorem B704467 : Blo 702318 704467 := bstep (se 1 (by rfl) ⟨528350, by rfl⟩ : syracuseStep 704467 = 1056701) B1056701
theorem B704483 : Blo 702318 704483 := bstep (se 1 (by rfl) ⟨528362, by rfl⟩ : syracuseStep 704483 = 1056725) B1056725
theorem B1785827 : Blo 702318 1785827 := bstep (se 1 (by rfl) ⟨1339370, by rfl⟩ : syracuseStep 1785827 = 2678741) B2678741
theorem B704499 : Blo 702318 704499 := bstep (se 1 (by rfl) ⟨528374, by rfl⟩ : syracuseStep 704499 = 1056749) B1056749
theorem B704515 : Blo 702318 704515 := bstep (se 1 (by rfl) ⟨528386, by rfl⟩ : syracuseStep 704515 = 1056773) B1056773
theorem B704531 : Blo 702318 704531 := bstep (se 1 (by rfl) ⟨528398, by rfl⟩ : syracuseStep 704531 = 1056797) B1056797
theorem B704547 : Blo 702318 704547 := bstep (se 1 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 704547 = 1056821) B1056821
theorem B2375729 : Blo 702318 2375729 := bstep (se 2 (by rfl) ⟨890898, by rfl⟩ : syracuseStep 2375729 = 1781797) B1781797
theorem B704563 : Blo 702318 704563 := bstep (se 1 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 704563 = 1056845) B1056845
theorem B704579 : Blo 702318 704579 := bstep (se 1 (by rfl) ⟨528434, by rfl⟩ : syracuseStep 704579 = 1056869) B1056869
theorem B704595 : Blo 702318 704595 := bstep (se 1 (by rfl) ⟨528446, by rfl⟩ : syracuseStep 704595 = 1056893) B1056893
theorem B2670691 : Blo 702318 2670691 := bstep (se 1 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 2670691 = 4006037) B4006037
theorem B704611 : Blo 702318 704611 := bstep (se 1 (by rfl) ⟨528458, by rfl⟩ : syracuseStep 704611 = 1056917) B1056917
theorem B704627 : Blo 702318 704627 := bstep (se 1 (by rfl) ⟨528470, by rfl⟩ : syracuseStep 704627 = 1056941) B1056941
theorem B704643 : Blo 702318 704643 := bstep (se 1 (by rfl) ⟨528482, by rfl⟩ : syracuseStep 704643 = 1056965) B1056965
theorem B704659 : Blo 702318 704659 := bstep (se 1 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 704659 = 1056989) B1056989
theorem B704675 : Blo 702318 704675 := bstep (se 1 (by rfl) ⟨528506, by rfl⟩ : syracuseStep 704675 = 1057013) B1057013
theorem B704691 : Blo 702318 704691 := bstep (se 1 (by rfl) ⟨528518, by rfl⟩ : syracuseStep 704691 = 1057037) B1057037
theorem B704707 : Blo 702318 704707 := bstep (se 1 (by rfl) ⟨528530, by rfl⟩ : syracuseStep 704707 = 1057061) B1057061
theorem B704723 : Blo 702318 704723 := bstep (se 1 (by rfl) ⟨528542, by rfl⟩ : syracuseStep 704723 = 1057085) B1057085
theorem B704739 : Blo 702318 704739 := bstep (se 1 (by rfl) ⟨528554, by rfl⟩ : syracuseStep 704739 = 1057109) B1057109
theorem B704755 : Blo 702318 704755 := bstep (se 1 (by rfl) ⟨528566, by rfl⟩ : syracuseStep 704755 = 1057133) B1057133
theorem B704771 : Blo 702318 704771 := bstep (se 1 (by rfl) ⟨528578, by rfl⟩ : syracuseStep 704771 = 1057157) B1057157
theorem B704787 : Blo 702318 704787 := bstep (se 1 (by rfl) ⟨528590, by rfl⟩ : syracuseStep 704787 = 1057181) B1057181
theorem B704803 : Blo 702318 704803 := bstep (se 1 (by rfl) ⟨528602, by rfl⟩ : syracuseStep 704803 = 1057205) B1057205
theorem B704819 : Blo 702318 704819 := bstep (se 1 (by rfl) ⟨528614, by rfl⟩ : syracuseStep 704819 = 1057229) B1057229
theorem B704835 : Blo 702318 704835 := bstep (se 1 (by rfl) ⟨528626, by rfl⟩ : syracuseStep 704835 = 1057253) B1057253
theorem B704851 : Blo 702318 704851 := bstep (se 1 (by rfl) ⟨528638, by rfl⟩ : syracuseStep 704851 = 1057277) B1057277
theorem B704867 : Blo 702318 704867 := bstep (se 1 (by rfl) ⟨528650, by rfl⟩ : syracuseStep 704867 = 1057301) B1057301
theorem B704883 : Blo 702318 704883 := bstep (se 1 (by rfl) ⟨528662, by rfl⟩ : syracuseStep 704883 = 1057325) B1057325
theorem B704899 : Blo 702318 704899 := bstep (se 1 (by rfl) ⟨528674, by rfl⟩ : syracuseStep 704899 = 1057349) B1057349
theorem B5718413 : Blo 702318 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B704915 : Blo 702318 704915 := bstep (se 1 (by rfl) ⟨528686, by rfl⟩ : syracuseStep 704915 = 1057373) B1057373
theorem B704931 : Blo 702318 704931 := bstep (se 1 (by rfl) ⟨528698, by rfl⟩ : syracuseStep 704931 = 1057397) B1057397
theorem B1130915 : Blo 702318 1130915 := bstep (se 1 (by rfl) ⟨848186, by rfl⟩ : syracuseStep 1130915 = 1696373) B1696373
theorem B704947 : Blo 702318 704947 := bstep (se 1 (by rfl) ⟨528710, by rfl⟩ : syracuseStep 704947 = 1057421) B1057421
theorem B704963 : Blo 702318 704963 := bstep (se 1 (by rfl) ⟨528722, by rfl⟩ : syracuseStep 704963 = 1057445) B1057445
theorem B704979 : Blo 702318 704979 := bstep (se 1 (by rfl) ⟨528734, by rfl⟩ : syracuseStep 704979 = 1057469) B1057469
theorem B704995 : Blo 702318 704995 := bstep (se 1 (by rfl) ⟨528746, by rfl⟩ : syracuseStep 704995 = 1057493) B1057493
theorem B705011 : Blo 702318 705011 := bstep (se 1 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 705011 = 1057517) B1057517
theorem B705027 : Blo 702318 705027 := bstep (se 1 (by rfl) ⟨528770, by rfl⟩ : syracuseStep 705027 = 1057541) B1057541
theorem B705043 : Blo 702318 705043 := bstep (se 1 (by rfl) ⟨528782, by rfl⟩ : syracuseStep 705043 = 1057565) B1057565
theorem B705059 : Blo 702318 705059 := bstep (se 1 (by rfl) ⟨528794, by rfl⟩ : syracuseStep 705059 = 1057589) B1057589
theorem B705075 : Blo 702318 705075 := bstep (se 1 (by rfl) ⟨528806, by rfl⟩ : syracuseStep 705075 = 1057613) B1057613
theorem B705091 : Blo 702318 705091 := bstep (se 1 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 705091 = 1057637) B1057637
theorem B5358149 : Blo 702318 5358149 := bstep (se 4 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 5358149 = 1004653) B1004653
theorem B2376269 : Blo 702318 2376269 := bstep (se 3 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 2376269 = 891101) B891101
theorem B705107 : Blo 702318 705107 := bstep (se 1 (by rfl) ⟨528830, by rfl⟩ : syracuseStep 705107 = 1057661) B1057661
theorem B705123 : Blo 702318 705123 := bstep (se 1 (by rfl) ⟨528842, by rfl⟩ : syracuseStep 705123 = 1057685) B1057685
theorem B705139 : Blo 702318 705139 := bstep (se 1 (by rfl) ⟨528854, by rfl⟩ : syracuseStep 705139 = 1057709) B1057709
theorem B2376323 : Blo 702318 2376323 := bstep (se 1 (by rfl) ⟨1782242, by rfl⟩ : syracuseStep 2376323 = 3564485) B3564485
theorem B705155 : Blo 702318 705155 := bstep (se 1 (by rfl) ⟨528866, by rfl⟩ : syracuseStep 705155 = 1057733) B1057733
theorem B705171 : Blo 702318 705171 := bstep (se 1 (by rfl) ⟨528878, by rfl⟩ : syracuseStep 705171 = 1057757) B1057757
theorem B705187 : Blo 702318 705187 := bstep (se 1 (by rfl) ⟨528890, by rfl⟩ : syracuseStep 705187 = 1057781) B1057781
theorem B705203 : Blo 702318 705203 := bstep (se 1 (by rfl) ⟨528902, by rfl⟩ : syracuseStep 705203 = 1057805) B1057805
theorem B705219 : Blo 702318 705219 := bstep (se 1 (by rfl) ⟨528914, by rfl⟩ : syracuseStep 705219 = 1057829) B1057829
theorem B1131203 : Blo 702318 1131203 := bstep (se 1 (by rfl) ⟨848402, by rfl⟩ : syracuseStep 1131203 = 1696805) B1696805
theorem B705235 : Blo 702318 705235 := bstep (se 1 (by rfl) ⟨528926, by rfl⟩ : syracuseStep 705235 = 1057853) B1057853
theorem B705251 : Blo 702318 705251 := bstep (se 1 (by rfl) ⟨528938, by rfl⟩ : syracuseStep 705251 = 1057877) B1057877
theorem B705267 : Blo 702318 705267 := bstep (se 1 (by rfl) ⟨528950, by rfl⟩ : syracuseStep 705267 = 1057901) B1057901
theorem B705283 : Blo 702318 705283 := bstep (se 1 (by rfl) ⟨528962, by rfl⟩ : syracuseStep 705283 = 1057925) B1057925
theorem B705299 : Blo 702318 705299 := bstep (se 1 (by rfl) ⟨528974, by rfl⟩ : syracuseStep 705299 = 1057949) B1057949
theorem B705315 : Blo 702318 705315 := bstep (se 1 (by rfl) ⟨528986, by rfl⟩ : syracuseStep 705315 = 1057973) B1057973
theorem B705331 : Blo 702318 705331 := bstep (se 1 (by rfl) ⟨528998, by rfl⟩ : syracuseStep 705331 = 1057997) B1057997
theorem B705347 : Blo 702318 705347 := bstep (se 1 (by rfl) ⟨529010, by rfl⟩ : syracuseStep 705347 = 1058021) B1058021
theorem B2409293 : Blo 702318 2409293 := bstep (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) B903485
theorem B705363 : Blo 702318 705363 := bstep (se 1 (by rfl) ⟨529022, by rfl⟩ : syracuseStep 705363 = 1058045) B1058045
theorem B1000291 : Blo 702318 1000291 := bstep (se 1 (by rfl) ⟨750218, by rfl⟩ : syracuseStep 1000291 = 1500437) B1500437
theorem B705379 : Blo 702318 705379 := bstep (se 1 (by rfl) ⟨529034, by rfl⟩ : syracuseStep 705379 = 1058069) B1058069
theorem B705395 : Blo 702318 705395 := bstep (se 1 (by rfl) ⟨529046, by rfl⟩ : syracuseStep 705395 = 1058093) B1058093
theorem B705411 : Blo 702318 705411 := bstep (se 1 (by rfl) ⟨529058, by rfl⟩ : syracuseStep 705411 = 1058117) B1058117
theorem B2376593 : Blo 702318 2376593 := bstep (se 2 (by rfl) ⟨891222, by rfl⟩ : syracuseStep 2376593 = 1782445) B1782445
theorem B1786769 : Blo 702318 1786769 := bstep (se 2 (by rfl) ⟨670038, by rfl⟩ : syracuseStep 1786769 = 1340077) B1340077
theorem B705427 : Blo 702318 705427 := bstep (se 1 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 705427 = 1058141) B1058141
theorem B705443 : Blo 702318 705443 := bstep (se 1 (by rfl) ⟨529082, by rfl⟩ : syracuseStep 705443 = 1058165) B1058165
theorem B3621809 : Blo 702318 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B705459 : Blo 702318 705459 := bstep (se 1 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 705459 = 1058189) B1058189
theorem B705475 : Blo 702318 705475 := bstep (se 1 (by rfl) ⟨529106, by rfl⟩ : syracuseStep 705475 = 1058213) B1058213
theorem B1786819 : Blo 702318 1786819 := bstep (se 1 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 1786819 = 2680229) B2680229
theorem B705491 : Blo 702318 705491 := bstep (se 1 (by rfl) ⟨529118, by rfl⟩ : syracuseStep 705491 = 1058237) B1058237
theorem B705507 : Blo 702318 705507 := bstep (se 1 (by rfl) ⟨529130, by rfl⟩ : syracuseStep 705507 = 1058261) B1058261
theorem B705523 : Blo 702318 705523 := bstep (se 1 (by rfl) ⟨529142, by rfl⟩ : syracuseStep 705523 = 1058285) B1058285
theorem B705539 : Blo 702318 705539 := bstep (se 1 (by rfl) ⟨529154, by rfl⟩ : syracuseStep 705539 = 1058309) B1058309
theorem B705555 : Blo 702318 705555 := bstep (se 1 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 705555 = 1058333) B1058333
theorem B705571 : Blo 702318 705571 := bstep (se 1 (by rfl) ⟨529178, by rfl⟩ : syracuseStep 705571 = 1058357) B1058357
theorem B705587 : Blo 702318 705587 := bstep (se 1 (by rfl) ⟨529190, by rfl⟩ : syracuseStep 705587 = 1058381) B1058381
theorem B705603 : Blo 702318 705603 := bstep (se 1 (by rfl) ⟨529202, by rfl⟩ : syracuseStep 705603 = 1058405) B1058405
theorem B1786961 : Blo 702318 1786961 := bstep (se 2 (by rfl) ⟨670110, by rfl⟩ : syracuseStep 1786961 = 1340221) B1340221
theorem B705619 : Blo 702318 705619 := bstep (se 1 (by rfl) ⟨529214, by rfl⟩ : syracuseStep 705619 = 1058429) B1058429
theorem B705635 : Blo 702318 705635 := bstep (se 1 (by rfl) ⟨529226, by rfl⟩ : syracuseStep 705635 = 1058453) B1058453
theorem B705651 : Blo 702318 705651 := bstep (se 1 (by rfl) ⟨529238, by rfl⟩ : syracuseStep 705651 = 1058477) B1058477
theorem B705667 : Blo 702318 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B705683 : Blo 702318 705683 := bstep (se 1 (by rfl) ⟨529262, by rfl⟩ : syracuseStep 705683 = 1058525) B1058525
theorem B705699 : Blo 702318 705699 := bstep (se 1 (by rfl) ⟨529274, by rfl⟩ : syracuseStep 705699 = 1058549) B1058549
theorem B705715 : Blo 702318 705715 := bstep (se 1 (by rfl) ⟨529286, by rfl⟩ : syracuseStep 705715 = 1058573) B1058573
theorem B705731 : Blo 702318 705731 := bstep (se 1 (by rfl) ⟨529298, by rfl⟩ : syracuseStep 705731 = 1058597) B1058597
theorem B705747 : Blo 702318 705747 := bstep (se 1 (by rfl) ⟨529310, by rfl⟩ : syracuseStep 705747 = 1058621) B1058621
theorem B705763 : Blo 702318 705763 := bstep (se 1 (by rfl) ⟨529322, by rfl⟩ : syracuseStep 705763 = 1058645) B1058645
theorem B705779 : Blo 702318 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B1426691 : Blo 702318 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B705795 : Blo 702318 705795 := bstep (se 1 (by rfl) ⟨529346, by rfl⟩ : syracuseStep 705795 = 1058693) B1058693
theorem B705811 : Blo 702318 705811 := bstep (se 1 (by rfl) ⟨529358, by rfl⟩ : syracuseStep 705811 = 1058717) B1058717
theorem B705827 : Blo 702318 705827 := bstep (se 1 (by rfl) ⟨529370, by rfl⟩ : syracuseStep 705827 = 1058741) B1058741
theorem B705843 : Blo 702318 705843 := bstep (se 1 (by rfl) ⟨529382, by rfl⟩ : syracuseStep 705843 = 1058765) B1058765
theorem B705859 : Blo 702318 705859 := bstep (se 1 (by rfl) ⟨529394, by rfl⟩ : syracuseStep 705859 = 1058789) B1058789
theorem B705875 : Blo 702318 705875 := bstep (se 1 (by rfl) ⟨529406, by rfl⟩ : syracuseStep 705875 = 1058813) B1058813
theorem B705891 : Blo 702318 705891 := bstep (se 1 (by rfl) ⟨529418, by rfl⟩ : syracuseStep 705891 = 1058837) B1058837
theorem B705907 : Blo 702318 705907 := bstep (se 1 (by rfl) ⟨529430, by rfl⟩ : syracuseStep 705907 = 1058861) B1058861
theorem B705923 : Blo 702318 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B4015493 : Blo 702318 4015493 := bstep (se 4 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 4015493 = 752905) B752905
theorem B1000849 : Blo 702318 1000849 := bstep (se 2 (by rfl) ⟨375318, by rfl⟩ : syracuseStep 1000849 = 750637) B750637
theorem B705939 : Blo 702318 705939 := bstep (se 1 (by rfl) ⟨529454, by rfl⟩ : syracuseStep 705939 = 1058909) B1058909
theorem B705955 : Blo 702318 705955 := bstep (se 1 (by rfl) ⟨529466, by rfl⟩ : syracuseStep 705955 = 1058933) B1058933
theorem B2377133 : Blo 702318 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B1000883 : Blo 702318 1000883 := bstep (se 1 (by rfl) ⟨750662, by rfl⟩ : syracuseStep 1000883 = 1501325) B1501325
theorem B705971 : Blo 702318 705971 := bstep (se 1 (by rfl) ⟨529478, by rfl⟩ : syracuseStep 705971 = 1058957) B1058957
theorem B705987 : Blo 702318 705987 := bstep (se 1 (by rfl) ⟨529490, by rfl⟩ : syracuseStep 705987 = 1058981) B1058981
theorem B706003 : Blo 702318 706003 := bstep (se 1 (by rfl) ⟨529502, by rfl⟩ : syracuseStep 706003 = 1059005) B1059005
theorem B2377187 : Blo 702318 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B706019 : Blo 702318 706019 := bstep (se 1 (by rfl) ⟨529514, by rfl⟩ : syracuseStep 706019 = 1059029) B1059029
theorem B706035 : Blo 702318 706035 := bstep (se 1 (by rfl) ⟨529526, by rfl⟩ : syracuseStep 706035 = 1059053) B1059053
theorem B706051 : Blo 702318 706051 := bstep (se 1 (by rfl) ⟨529538, by rfl⟩ : syracuseStep 706051 = 1059077) B1059077
theorem B706067 : Blo 702318 706067 := bstep (se 1 (by rfl) ⟨529550, by rfl⟩ : syracuseStep 706067 = 1059101) B1059101
theorem B706083 : Blo 702318 706083 := bstep (se 1 (by rfl) ⟨529562, by rfl⟩ : syracuseStep 706083 = 1059125) B1059125
theorem B706099 : Blo 702318 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B706115 : Blo 702318 706115 := bstep (se 1 (by rfl) ⟨529586, by rfl⟩ : syracuseStep 706115 = 1059173) B1059173
theorem B706131 : Blo 702318 706131 := bstep (se 1 (by rfl) ⟨529598, by rfl⟩ : syracuseStep 706131 = 1059197) B1059197
theorem B706147 : Blo 702318 706147 := bstep (se 1 (by rfl) ⟨529610, by rfl⟩ : syracuseStep 706147 = 1059221) B1059221
theorem B706163 : Blo 702318 706163 := bstep (se 1 (by rfl) ⟨529622, by rfl⟩ : syracuseStep 706163 = 1059245) B1059245
theorem B706179 : Blo 702318 706179 := bstep (se 1 (by rfl) ⟨529634, by rfl⟩ : syracuseStep 706179 = 1059269) B1059269
theorem B706195 : Blo 702318 706195 := bstep (se 1 (by rfl) ⟨529646, by rfl⟩ : syracuseStep 706195 = 1059293) B1059293
theorem B706211 : Blo 702318 706211 := bstep (se 1 (by rfl) ⟨529658, by rfl⟩ : syracuseStep 706211 = 1059317) B1059317
theorem B706227 : Blo 702318 706227 := bstep (se 1 (by rfl) ⟨529670, by rfl⟩ : syracuseStep 706227 = 1059341) B1059341
theorem B706243 : Blo 702318 706243 := bstep (se 1 (by rfl) ⟨529682, by rfl⟩ : syracuseStep 706243 = 1059365) B1059365
theorem B706259 : Blo 702318 706259 := bstep (se 1 (by rfl) ⟨529694, by rfl⟩ : syracuseStep 706259 = 1059389) B1059389
theorem B706275 : Blo 702318 706275 := bstep (se 1 (by rfl) ⟨529706, by rfl⟩ : syracuseStep 706275 = 1059413) B1059413
theorem B2377457 : Blo 702318 2377457 := bstep (se 2 (by rfl) ⟨891546, by rfl⟩ : syracuseStep 2377457 = 1783093) B1783093
theorem B706291 : Blo 702318 706291 := bstep (se 1 (by rfl) ⟨529718, by rfl⟩ : syracuseStep 706291 = 1059437) B1059437
theorem B706307 : Blo 702318 706307 := bstep (se 1 (by rfl) ⟨529730, by rfl⟩ : syracuseStep 706307 = 1059461) B1059461
theorem B7718755 : Blo 702318 7718755 := bstep (se 1 (by rfl) ⟨5789066, by rfl⟩ : syracuseStep 7718755 = 11578133) B11578133
theorem B4507589 : Blo 702318 4507589 := bstep (se 4 (by rfl) ⟨422586, by rfl⟩ : syracuseStep 4507589 = 845173) B845173
theorem B1001441 : Blo 702318 1001441 := bstep (se 2 (by rfl) ⟨375540, by rfl⟩ : syracuseStep 1001441 = 751081) B751081
theorem B1001521 : Blo 702318 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B1427633 : Blo 702318 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B2672909 : Blo 702318 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B2377997 : Blo 702318 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B3557681 : Blo 702318 3557681 := bstep (se 2 (by rfl) ⟨1334130, by rfl⟩ : syracuseStep 3557681 = 2668261) B2668261
theorem B2378051 : Blo 702318 2378051 := bstep (se 1 (by rfl) ⟨1783538, by rfl⟩ : syracuseStep 2378051 = 3567077) B3567077
theorem B9029987 : Blo 702318 9029987 := bstep (se 1 (by rfl) ⟨6772490, by rfl⟩ : syracuseStep 9029987 = 13544981) B13544981
theorem B2378321 : Blo 702318 2378321 := bstep (se 2 (by rfl) ⟨891870, by rfl⟩ : syracuseStep 2378321 = 1783741) B1783741
theorem B3001009 : Blo 702318 3001009 := bstep (se 2 (by rfl) ⟨1125378, by rfl⟩ : syracuseStep 3001009 = 2250757) B2250757
theorem B1002307 : Blo 702318 1002307 := bstep (se 1 (by rfl) ⟨751730, by rfl⟩ : syracuseStep 1002307 = 1503461) B1503461
theorem B3132365 : Blo 702318 3132365 := bstep (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) B1174637
theorem B2378861 : Blo 702318 2378861 := bstep (se 3 (by rfl) ⟨446036, by rfl⟩ : syracuseStep 2378861 = 892073) B892073
theorem B2378915 : Blo 702318 2378915 := bstep (se 1 (by rfl) ⟨1784186, by rfl⟩ : syracuseStep 2378915 = 3568373) B3568373
theorem B1002785 : Blo 702318 1002785 := bstep (se 2 (by rfl) ⟨376044, by rfl⟩ : syracuseStep 1002785 = 752089) B752089
theorem B1690961 : Blo 702318 1690961 := bstep (se 2 (by rfl) ⟨634110, by rfl⟩ : syracuseStep 1690961 = 1268221) B1268221
theorem B1002899 : Blo 702318 1002899 := bstep (se 1 (by rfl) ⟨752174, by rfl⟩ : syracuseStep 1002899 = 1504349) B1504349
theorem B2379185 : Blo 702318 2379185 := bstep (se 2 (by rfl) ⟨892194, by rfl⟩ : syracuseStep 2379185 = 1784389) B1784389
theorem B3263921 : Blo 702318 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B1002979 : Blo 702318 1002979 := bstep (se 1 (by rfl) ⟨752234, by rfl⟩ : syracuseStep 1002979 = 1504469) B1504469
theorem B9653813 : Blo 702318 9653813 := bstep (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) B905045
theorem B3559139 : Blo 702318 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B1068803 : Blo 702318 1068803 := bstep (se 1 (by rfl) ⟨801602, by rfl⟩ : syracuseStep 1068803 = 1603205) B1603205
theorem B2379725 : Blo 702318 2379725 := bstep (se 3 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 2379725 = 892397) B892397
theorem B2379779 : Blo 702318 2379779 := bstep (se 1 (by rfl) ⟨1784834, by rfl⟩ : syracuseStep 2379779 = 3569669) B3569669
theorem B1003537 : Blo 702318 1003537 := bstep (se 2 (by rfl) ⟨376326, by rfl⟩ : syracuseStep 1003537 = 752653) B752653
theorem B6410339 : Blo 702318 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B1069283 : Blo 702318 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B2380049 : Blo 702318 2380049 := bstep (se 2 (by rfl) ⟨892518, by rfl⟩ : syracuseStep 2380049 = 1785037) B1785037
theorem B5722595 : Blo 702318 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B3559949 : Blo 702318 3559949 := bstep (se 3 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 3559949 = 1334981) B1334981
theorem B1430065 : Blo 702318 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B6869573 : Blo 702318 6869573 := bstep (se 4 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 6869573 = 1288045) B1288045
theorem B3002957 : Blo 702318 3002957 := bstep (se 3 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 3002957 = 1126109) B1126109
theorem B10179269 : Blo 702318 10179269 := bstep (se 4 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 10179269 = 1908613) B1908613
theorem B1004243 : Blo 702318 1004243 := bstep (se 1 (by rfl) ⟨753182, by rfl⟩ : syracuseStep 1004243 = 1506365) B1506365
theorem B2380589 : Blo 702318 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B2380643 : Blo 702318 2380643 := bstep (se 1 (by rfl) ⟨1785482, by rfl⟩ : syracuseStep 2380643 = 3570965) B3570965
theorem B4641677 : Blo 702318 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1758275 : Blo 702318 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1070177 : Blo 702318 1070177 := bstep (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) B802633
theorem B2675825 : Blo 702318 2675825 := bstep (se 2 (by rfl) ⟨1003434, by rfl⟩ : syracuseStep 2675825 = 2006869) B2006869
theorem B2380913 : Blo 702318 2380913 := bstep (se 2 (by rfl) ⟨892842, by rfl⟩ : syracuseStep 2380913 = 1785685) B1785685
theorem B4019341 : Blo 702318 4019341 := bstep (se 3 (by rfl) ⟨753626, by rfl⟩ : syracuseStep 4019341 = 1507253) B1507253
theorem B1692913 : Blo 702318 1692913 := bstep (se 2 (by rfl) ⟨634842, by rfl⟩ : syracuseStep 1692913 = 1269685) B1269685
theorem B1004881 : Blo 702318 1004881 := bstep (se 2 (by rfl) ⟨376830, by rfl⟩ : syracuseStep 1004881 = 753661) B753661
theorem B5133709 : Blo 702318 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B1004995 : Blo 702318 1004995 := bstep (se 1 (by rfl) ⟨753746, by rfl⟩ : syracuseStep 1004995 = 1507493) B1507493
theorem B15226339 : Blo 702318 15226339 := bstep (se 1 (by rfl) ⟨11419754, by rfl⟩ : syracuseStep 15226339 = 22839509) B22839509
theorem B1693315 : Blo 702318 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B2381453 : Blo 702318 2381453 := bstep (se 3 (by rfl) ⟨446522, by rfl⟩ : syracuseStep 2381453 = 893045) B893045
theorem B1267363 : Blo 702318 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B2250413 : Blo 702318 2250413 := bstep (se 3 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 2250413 = 843905) B843905
theorem B2381507 : Blo 702318 2381507 := bstep (se 1 (by rfl) ⟨1786130, by rfl⟩ : syracuseStep 2381507 = 3572261) B3572261
theorem B2283299 : Blo 702318 2283299 := bstep (se 1 (by rfl) ⟨1712474, by rfl⟩ : syracuseStep 2283299 = 3424949) B3424949
theorem B2381777 : Blo 702318 2381777 := bstep (se 2 (by rfl) ⟨893166, by rfl⟩ : syracuseStep 2381777 = 1786333) B1786333
theorem B4806661 : Blo 702318 4806661 := bstep (se 4 (by rfl) ⟨450624, by rfl⟩ : syracuseStep 4806661 = 901249) B901249
theorem B2250833 : Blo 702318 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B1267825 : Blo 702318 1267825 := bstep (se 2 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 1267825 = 950869) B950869
theorem B1267939 : Blo 702318 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B1071425 : Blo 702318 1071425 := bstep (se 2 (by rfl) ⟨401784, by rfl⟩ : syracuseStep 1071425 = 803569) B803569
theorem B1071571 : Blo 702318 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B2382317 : Blo 702318 2382317 := bstep (se 3 (by rfl) ⟨446684, by rfl⟩ : syracuseStep 2382317 = 893369) B893369
theorem B2677283 : Blo 702318 2677283 := bstep (se 1 (by rfl) ⟨2007962, by rfl⟩ : syracuseStep 2677283 = 4015925) B4015925
theorem B2382371 : Blo 702318 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B1694353 : Blo 702318 1694353 := bstep (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) B1270765
theorem B1268401 : Blo 702318 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B8575715 : Blo 702318 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B9263857 : Blo 702318 9263857 := bstep (se 2 (by rfl) ⟨3473946, by rfl⟩ : syracuseStep 9263857 = 6947893) B6947893
theorem B2382641 : Blo 702318 2382641 := bstep (se 2 (by rfl) ⟨893490, by rfl⟩ : syracuseStep 2382641 = 1786981) B1786981
theorem B1334161 : Blo 702318 1334161 := bstep (se 2 (by rfl) ⟨500310, by rfl⟩ : syracuseStep 1334161 = 1000621) B1000621
theorem B2284561 : Blo 702318 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B4021325 : Blo 702318 4021325 := bstep (se 3 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 4021325 = 1507997) B1507997
theorem B1924355 : Blo 702318 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B6774029 : Blo 702318 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B2284817 : Blo 702318 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B2383181 : Blo 702318 2383181 := bstep (se 3 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 2383181 = 893693) B893693
theorem B3562865 : Blo 702318 3562865 := bstep (se 2 (by rfl) ⟨1336074, by rfl⟩ : syracuseStep 3562865 = 2672149) B2672149
theorem B2383235 : Blo 702318 2383235 := bstep (se 1 (by rfl) ⟨1787426, by rfl⟩ : syracuseStep 2383235 = 3574853) B3574853
theorem B2678285 : Blo 702318 2678285 := bstep (se 3 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 2678285 = 1004357) B1004357
theorem B2383505 : Blo 702318 2383505 := bstep (se 2 (by rfl) ⟨893814, by rfl⟩ : syracuseStep 2383505 = 1787629) B1787629
theorem B1335217 : Blo 702318 1335217 := bstep (se 2 (by rfl) ⟨500706, by rfl⟩ : syracuseStep 1335217 = 1001413) B1001413
theorem B4022257 : Blo 702318 4022257 := bstep (se 2 (by rfl) ⟨1508346, by rfl⟩ : syracuseStep 4022257 = 3016693) B3016693
theorem B1335619 : Blo 702318 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B1335665 : Blo 702318 1335665 := bstep (se 2 (by rfl) ⟨500874, by rfl⟩ : syracuseStep 1335665 = 1001749) B1001749
theorem B1925603 : Blo 702318 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B3006989 : Blo 702318 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B6021701 : Blo 702318 6021701 := bstep (se 4 (by rfl) ⟨564534, by rfl⟩ : syracuseStep 6021701 = 1129069) B1129069
theorem B1335953 : Blo 702318 1335953 := bstep (se 2 (by rfl) ⟨500982, by rfl⟩ : syracuseStep 1335953 = 1001965) B1001965
theorem B713395 : Blo 702318 713395 := bstep (se 1 (by rfl) ⟨535046, by rfl⟩ : syracuseStep 713395 = 1070093) B1070093
theorem B2712305 : Blo 702318 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B3564323 : Blo 702318 3564323 := bstep (se 1 (by rfl) ⟨2673242, by rfl⟩ : syracuseStep 3564323 = 5346485) B5346485
theorem B3007331 : Blo 702318 3007331 := bstep (se 1 (by rfl) ⟨2255498, by rfl⟩ : syracuseStep 3007331 = 4510997) B4510997
theorem B4809827 : Blo 702318 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B1500419 : Blo 702318 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B3007793 : Blo 702318 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B1336675 : Blo 702318 1336675 := bstep (se 1 (by rfl) ⟨1002506, by rfl⟩ : syracuseStep 1336675 = 2005013) B2005013
theorem B2254243 : Blo 702318 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B3565133 : Blo 702318 3565133 := bstep (se 3 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 3565133 = 1336925) B1336925
theorem B2680397 : Blo 702318 2680397 := bstep (se 3 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 2680397 = 1005149) B1005149
theorem B3434083 : Blo 702318 3434083 := bstep (se 1 (by rfl) ⟨2575562, by rfl⟩ : syracuseStep 3434083 = 5151125) B5151125
theorem B2254513 : Blo 702318 2254513 := bstep (se 2 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 2254513 = 1690885) B1690885
theorem B4056803 : Blo 702318 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B4056817 : Blo 702318 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1337123 : Blo 702318 1337123 := bstep (se 1 (by rfl) ⟨1002842, by rfl⟩ : syracuseStep 1337123 = 2005685) B2005685
theorem B1271587 : Blo 702318 1271587 := bstep (se 1 (by rfl) ⟨953690, by rfl⟩ : syracuseStep 1271587 = 1907381) B1907381
theorem B13526837 : Blo 702318 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B845635 : Blo 702318 845635 := bstep (se 1 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 845635 = 1268453) B1268453
theorem B1206289 : Blo 702318 1206289 := bstep (se 2 (by rfl) ⟨452358, by rfl⟩ : syracuseStep 1206289 = 904717) B904717
theorem B1337411 : Blo 702318 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B2287939 : Blo 702318 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B2681201 : Blo 702318 2681201 := bstep (se 2 (by rfl) ⟨1005450, by rfl⟩ : syracuseStep 2681201 = 2010901) B2010901
theorem B5335793 : Blo 702318 5335793 := bstep (se 2 (by rfl) ⟨2000922, by rfl⟩ : syracuseStep 5335793 = 4001845) B4001845
theorem B1338353 : Blo 702318 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B1502435 : Blo 702318 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B2256113 : Blo 702318 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B6778181 : Blo 702318 6778181 := bstep (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) B1270909
theorem B847379 : Blo 702318 847379 := bstep (se 1 (by rfl) ⟨635534, by rfl⟩ : syracuseStep 847379 = 1271069) B1271069
theorem B2256461 : Blo 702318 2256461 := bstep (se 3 (by rfl) ⟨423086, by rfl⟩ : syracuseStep 2256461 = 846173) B846173
theorem B1175315 : Blo 702318 1175315 := bstep (se 1 (by rfl) ⟨881486, by rfl⟩ : syracuseStep 1175315 = 1762973) B1762973
theorem B5074757 : Blo 702318 5074757 := bstep (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) B951517
theorem B2715491 : Blo 702318 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B1339249 : Blo 702318 1339249 := bstep (se 2 (by rfl) ⟨502218, by rfl⟩ : syracuseStep 1339249 = 1004437) B1004437
theorem B1339409 : Blo 702318 1339409 := bstep (se 2 (by rfl) ⟨502278, by rfl⟩ : syracuseStep 1339409 = 1004557) B1004557
theorem B1339811 : Blo 702318 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B3568049 : Blo 702318 3568049 := bstep (se 2 (by rfl) ⟨1338018, by rfl⟩ : syracuseStep 3568049 = 2676037) B2676037
theorem B3797765 : Blo 702318 3797765 := bstep (se 4 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 3797765 = 712081) B712081
theorem B3011363 : Blo 702318 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B5075909 : Blo 702318 5075909 := bstep (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) B951733
theorem B1504451 : Blo 702318 1504451 := bstep (se 1 (by rfl) ⟨1128338, by rfl⟩ : syracuseStep 1504451 = 2256677) B2256677
theorem B1340707 : Blo 702318 1340707 := bstep (se 1 (by rfl) ⟨1005530, by rfl⟩ : syracuseStep 1340707 = 2011061) B2011061
theorem B15398257 : Blo 702318 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B2258317 : Blo 702318 2258317 := bstep (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) B846869
theorem B1340867 : Blo 702318 1340867 := bstep (se 1 (by rfl) ⟨1005650, by rfl⟩ : syracuseStep 1340867 = 2011301) B2011301
theorem B3569507 : Blo 702318 3569507 := bstep (se 1 (by rfl) ⟨2677130, by rfl⟩ : syracuseStep 3569507 = 5354261) B5354261
theorem B1505699 : Blo 702318 1505699 := bstep (se 1 (by rfl) ⟨1129274, by rfl⟩ : syracuseStep 1505699 = 2258549) B2258549
theorem B752051 : Blo 702318 752051 := bstep (se 1 (by rfl) ⟨564038, by rfl⟩ : syracuseStep 752051 = 1128077) B1128077
theorem B2718157 : Blo 702318 2718157 := bstep (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) B1019309
theorem B1604099 : Blo 702318 1604099 := bstep (se 1 (by rfl) ⟨1203074, by rfl⟩ : syracuseStep 1604099 = 2406149) B2406149
theorem B3570317 : Blo 702318 3570317 := bstep (se 3 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 3570317 = 1338869) B1338869
theorem B6093539 : Blo 702318 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B1506289 : Blo 702318 1506289 := bstep (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) B1129717
theorem B2260163 : Blo 702318 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B4521349 : Blo 702318 4521349 := bstep (se 4 (by rfl) ⟨423876, by rfl⟩ : syracuseStep 4521349 = 847753) B847753
theorem B4816397 : Blo 702318 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B2260561 : Blo 702318 2260561 := bstep (se 2 (by rfl) ⟨847710, by rfl⟩ : syracuseStep 2260561 = 1695421) B1695421
theorem B8027747 : Blo 702318 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B3800965 : Blo 702318 3800965 := bstep (se 4 (by rfl) ⟨356340, by rfl⟩ : syracuseStep 3800965 = 712681) B712681
theorem B1900525 : Blo 702318 1900525 := bstep (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) B712697
theorem B1507339 : Blo 702318 1507339 := bstep (se 1 (by rfl) ⟨1130504, by rfl⟩ : syracuseStep 1507339 = 2261009) B2261009
theorem B753943 : Blo 702318 753943 := bstep (se 1 (by rfl) ⟨565457, by rfl⟩ : syracuseStep 753943 = 1130915) B1130915
theorem B17170805 : Blo 702318 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B3572099 : Blo 702318 3572099 := bstep (se 1 (by rfl) ⟨2679074, by rfl⟩ : syracuseStep 3572099 = 5358149) B5358149
theorem B1606195 : Blo 702318 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B2851421 : Blo 702318 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B951193 : Blo 702318 951193 := bstep (se 2 (by rfl) ⟨356697, by rfl⟩ : syracuseStep 951193 = 713395) B713395
theorem B951755 : Blo 702318 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B3016541 : Blo 702318 3016541 := bstep (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) B1131203
theorem B3868517 : Blo 702318 3868517 := bstep (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) B725347
theorem B4294721 : Blo 702318 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B5409089 : Blo 702318 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B10291673 : Blo 702318 10291673 := bstep (se 2 (by rfl) ⟨3859377, by rfl⟩ : syracuseStep 10291673 = 7718755) B7718755
theorem B4000387 : Blo 702318 4000387 := bstep (se 1 (by rfl) ⟨3000290, by rfl⟩ : syracuseStep 4000387 = 6000581) B6000581
theorem B7604867 : Blo 702318 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B1608385 : Blo 702318 1608385 := bstep (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) B1206289
theorem B2853805 : Blo 702318 2853805 := bstep (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) B1070177
theorem B2001971 : Blo 702318 2001971 := bstep (se 1 (by rfl) ⟨1501478, by rfl⟩ : syracuseStep 2001971 = 3002957) B3002957
theorem B3050585 : Blo 702318 3050585 := bstep (se 2 (by rfl) ⟨1143969, by rfl⟩ : syracuseStep 3050585 = 2287939) B2287939
theorem B6425731 : Blo 702318 6425731 := bstep (se 1 (by rfl) ⟨4819298, by rfl⟩ : syracuseStep 6425731 = 9638597) B9638597
theorem B6786179 : Blo 702318 6786179 := bstep (se 1 (by rfl) ⟨5089634, by rfl⟩ : syracuseStep 6786179 = 10179269) B10179269
theorem B3804509 : Blo 702318 3804509 := bstep (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) B1426691
theorem B4001345 : Blo 702318 4001345 := bstep (se 2 (by rfl) ⟨1500504, by rfl⟩ : syracuseStep 4001345 = 3001009) B3001009
theorem B1543745 : Blo 702318 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B790123 : Blo 702318 790123 := bstep (se 1 (by rfl) ⟨592592, by rfl⟩ : syracuseStep 790123 = 1185185) B1185185
theorem B790231 : Blo 702318 790231 := bstep (se 1 (by rfl) ⟨592673, by rfl⟩ : syracuseStep 790231 = 1185347) B1185347
theorem B3378905 : Blo 702318 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B6033113 : Blo 702318 6033113 := bstep (se 2 (by rfl) ⟨2262417, by rfl⟩ : syracuseStep 6033113 = 4524835) B4524835
theorem B790411 : Blo 702318 790411 := bstep (se 1 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 790411 = 1185617) B1185617
theorem B790519 : Blo 702318 790519 := bstep (se 1 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 790519 = 1185779) B1185779
theorem B13570199 : Blo 702318 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B790699 : Blo 702318 790699 := bstep (se 1 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 790699 = 1186049) B1186049
theorem B790807 : Blo 702318 790807 := bstep (se 1 (by rfl) ⟨593105, by rfl⟩ : syracuseStep 790807 = 1186211) B1186211
theorem B790987 : Blo 702318 790987 := bstep (se 1 (by rfl) ⟨593240, by rfl⟩ : syracuseStep 790987 = 1186481) B1186481
theorem B791095 : Blo 702318 791095 := bstep (se 1 (by rfl) ⟨593321, by rfl⟩ : syracuseStep 791095 = 1186643) B1186643
theorem B791275 : Blo 702318 791275 := bstep (se 1 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 791275 = 1186913) B1186913
theorem B1053515 : Blo 702318 1053515 := bstep (se 1 (by rfl) ⟨790136, by rfl⟩ : syracuseStep 1053515 = 1580273) B1580273
theorem B1053527 : Blo 702318 1053527 := bstep (se 1 (by rfl) ⟨790145, by rfl⟩ : syracuseStep 1053527 = 1580291) B1580291
theorem B791383 : Blo 702318 791383 := bstep (se 1 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 791383 = 1187075) B1187075
theorem B1053593 : Blo 702318 1053593 := bstep (se 2 (by rfl) ⟨395097, by rfl⟩ : syracuseStep 1053593 = 790195) B790195
theorem B1053707 : Blo 702318 1053707 := bstep (se 1 (by rfl) ⟨790280, by rfl⟩ : syracuseStep 1053707 = 1580561) B1580561
theorem B791563 : Blo 702318 791563 := bstep (se 1 (by rfl) ⟨593672, by rfl⟩ : syracuseStep 791563 = 1187345) B1187345
theorem B1053719 : Blo 702318 1053719 := bstep (se 1 (by rfl) ⟨790289, by rfl⟩ : syracuseStep 1053719 = 1580579) B1580579
theorem B1053785 : Blo 702318 1053785 := bstep (se 2 (by rfl) ⟨395169, by rfl⟩ : syracuseStep 1053785 = 790339) B790339
theorem B791671 : Blo 702318 791671 := bstep (se 1 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 791671 = 1187507) B1187507
theorem B1053899 : Blo 702318 1053899 := bstep (se 1 (by rfl) ⟨790424, by rfl⟩ : syracuseStep 1053899 = 1580849) B1580849
theorem B1053911 : Blo 702318 1053911 := bstep (se 1 (by rfl) ⟨790433, by rfl⟩ : syracuseStep 1053911 = 1580867) B1580867
theorem B1053977 : Blo 702318 1053977 := bstep (se 2 (by rfl) ⟨395241, by rfl⟩ : syracuseStep 1053977 = 790483) B790483
theorem B791851 : Blo 702318 791851 := bstep (se 1 (by rfl) ⟨593888, by rfl⟩ : syracuseStep 791851 = 1187777) B1187777
theorem B1054091 : Blo 702318 1054091 := bstep (se 1 (by rfl) ⟨790568, by rfl⟩ : syracuseStep 1054091 = 1581137) B1581137
theorem B1054103 : Blo 702318 1054103 := bstep (se 1 (by rfl) ⟨790577, by rfl⟩ : syracuseStep 1054103 = 1581155) B1581155
theorem B791959 : Blo 702318 791959 := bstep (se 1 (by rfl) ⟨593969, by rfl⟩ : syracuseStep 791959 = 1187939) B1187939
theorem B1185239 : Blo 702318 1185239 := bstep (se 1 (by rfl) ⟨888929, by rfl⟩ : syracuseStep 1185239 = 1777859) B1777859
theorem B1054169 : Blo 702318 1054169 := bstep (se 2 (by rfl) ⟨395313, by rfl⟩ : syracuseStep 1054169 = 790627) B790627
theorem B6002221 : Blo 702318 6002221 := bstep (se 3 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 6002221 = 2250833) B2250833
theorem B1054283 : Blo 702318 1054283 := bstep (se 1 (by rfl) ⟨790712, by rfl⟩ : syracuseStep 1054283 = 1581425) B1581425
theorem B890443 : Blo 702318 890443 := bstep (se 1 (by rfl) ⟨667832, by rfl⟩ : syracuseStep 890443 = 1335665) B1335665
theorem B792139 : Blo 702318 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B1185367 : Blo 702318 1185367 := bstep (se 1 (by rfl) ⟨889025, by rfl⟩ : syracuseStep 1185367 = 1778051) B1778051
theorem B1054295 : Blo 702318 1054295 := bstep (se 1 (by rfl) ⟨790721, by rfl⟩ : syracuseStep 1054295 = 1581443) B1581443
theorem B1283735 : Blo 702318 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B1054361 : Blo 702318 1054361 := bstep (se 2 (by rfl) ⟨395385, by rfl⟩ : syracuseStep 1054361 = 790771) B790771
theorem B2004659 : Blo 702318 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B792247 : Blo 702318 792247 := bstep (se 1 (by rfl) ⟨594185, by rfl⟩ : syracuseStep 792247 = 1188371) B1188371
theorem B1054475 : Blo 702318 1054475 := bstep (se 1 (by rfl) ⟨790856, by rfl⟩ : syracuseStep 1054475 = 1581713) B1581713
theorem B1054487 : Blo 702318 1054487 := bstep (se 1 (by rfl) ⟨790865, by rfl⟩ : syracuseStep 1054487 = 1581731) B1581731
theorem B1054553 : Blo 702318 1054553 := bstep (se 2 (by rfl) ⟨395457, by rfl⟩ : syracuseStep 1054553 = 790915) B790915
theorem B792427 : Blo 702318 792427 := bstep (se 1 (by rfl) ⟨594320, by rfl⟩ : syracuseStep 792427 = 1188641) B1188641
theorem B2004887 : Blo 702318 2004887 := bstep (se 1 (by rfl) ⟨1503665, by rfl⟩ : syracuseStep 2004887 = 3007331) B3007331
theorem B1054667 : Blo 702318 1054667 := bstep (se 1 (by rfl) ⟨791000, by rfl⟩ : syracuseStep 1054667 = 1582001) B1582001
theorem B1054679 : Blo 702318 1054679 := bstep (se 1 (by rfl) ⟨791009, by rfl⟩ : syracuseStep 1054679 = 1582019) B1582019
theorem B792535 : Blo 702318 792535 := bstep (se 1 (by rfl) ⟨594401, by rfl⟩ : syracuseStep 792535 = 1188803) B1188803
theorem B1054745 : Blo 702318 1054745 := bstep (se 2 (by rfl) ⟨395529, by rfl⟩ : syracuseStep 1054745 = 791059) B791059
theorem B1906753 : Blo 702318 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B1054859 : Blo 702318 1054859 := bstep (se 1 (by rfl) ⟨791144, by rfl⟩ : syracuseStep 1054859 = 1582289) B1582289
theorem B792715 : Blo 702318 792715 := bstep (se 1 (by rfl) ⟨594536, by rfl⟩ : syracuseStep 792715 = 1189073) B1189073
theorem B1054871 : Blo 702318 1054871 := bstep (se 1 (by rfl) ⟨791153, by rfl⟩ : syracuseStep 1054871 = 1582307) B1582307
theorem B2857133 : Blo 702318 2857133 := bstep (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) B1071425
theorem B1185995 : Blo 702318 1185995 := bstep (se 1 (by rfl) ⟨889496, by rfl⟩ : syracuseStep 1185995 = 1778993) B1778993
theorem B2005195 : Blo 702318 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B1054937 : Blo 702318 1054937 := bstep (se 2 (by rfl) ⟨395601, by rfl⟩ : syracuseStep 1054937 = 791203) B791203
theorem B792823 : Blo 702318 792823 := bstep (se 1 (by rfl) ⟨594617, by rfl⟩ : syracuseStep 792823 = 1189235) B1189235
theorem B1186123 : Blo 702318 1186123 := bstep (se 1 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 1186123 = 1779185) B1779185
theorem B1055051 : Blo 702318 1055051 := bstep (se 1 (by rfl) ⟨791288, by rfl⟩ : syracuseStep 1055051 = 1582577) B1582577
theorem B1055063 : Blo 702318 1055063 := bstep (se 1 (by rfl) ⟨791297, by rfl⟩ : syracuseStep 1055063 = 1582595) B1582595
theorem B1055129 : Blo 702318 1055129 := bstep (se 2 (by rfl) ⟨395673, by rfl⟩ : syracuseStep 1055129 = 791347) B791347
theorem B793003 : Blo 702318 793003 := bstep (se 1 (by rfl) ⟨594752, by rfl⟩ : syracuseStep 793003 = 1189505) B1189505
theorem B1186265 : Blo 702318 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B2005469 : Blo 702318 2005469 := bstep (se 3 (by rfl) ⟨376025, by rfl⟩ : syracuseStep 2005469 = 752051) B752051
theorem B1055243 : Blo 702318 1055243 := bstep (se 1 (by rfl) ⟨791432, by rfl⟩ : syracuseStep 1055243 = 1582865) B1582865
theorem B1055255 : Blo 702318 1055255 := bstep (se 1 (by rfl) ⟨791441, by rfl⟩ : syracuseStep 1055255 = 1582883) B1582883
theorem B891415 : Blo 702318 891415 := bstep (se 1 (by rfl) ⟨668561, by rfl⟩ : syracuseStep 891415 = 1337123) B1337123
theorem B793111 : Blo 702318 793111 := bstep (se 1 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 793111 = 1189667) B1189667
theorem B9017891 : Blo 702318 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B1186393 : Blo 702318 1186393 := bstep (se 2 (by rfl) ⟨444897, by rfl⟩ : syracuseStep 1186393 = 889795) B889795
theorem B1055321 : Blo 702318 1055321 := bstep (se 2 (by rfl) ⟨395745, by rfl⟩ : syracuseStep 1055321 = 791491) B791491
theorem B1055435 : Blo 702318 1055435 := bstep (se 1 (by rfl) ⟨791576, by rfl⟩ : syracuseStep 1055435 = 1583153) B1583153
theorem B793291 : Blo 702318 793291 := bstep (se 1 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 793291 = 1189937) B1189937
theorem B1055447 : Blo 702318 1055447 := bstep (se 1 (by rfl) ⟨791585, by rfl⟩ : syracuseStep 1055447 = 1583171) B1583171
theorem B1055513 : Blo 702318 1055513 := bstep (se 2 (by rfl) ⟨395817, by rfl⟩ : syracuseStep 1055513 = 791635) B791635
theorem B793399 : Blo 702318 793399 := bstep (se 1 (by rfl) ⟨595049, by rfl⟩ : syracuseStep 793399 = 1190099) B1190099
theorem B6003557 : Blo 702318 6003557 := bstep (se 4 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 6003557 = 1125667) B1125667
theorem B1055627 : Blo 702318 1055627 := bstep (se 1 (by rfl) ⟨791720, by rfl⟩ : syracuseStep 1055627 = 1583441) B1583441
theorem B1055639 : Blo 702318 1055639 := bstep (se 1 (by rfl) ⟨791729, by rfl⟩ : syracuseStep 1055639 = 1583459) B1583459
theorem B1055705 : Blo 702318 1055705 := bstep (se 2 (by rfl) ⟨395889, by rfl⟩ : syracuseStep 1055705 = 791779) B791779
theorem B793579 : Blo 702318 793579 := bstep (se 1 (by rfl) ⟨595184, by rfl⟩ : syracuseStep 793579 = 1190369) B1190369
theorem B1055819 : Blo 702318 1055819 := bstep (se 1 (by rfl) ⟨791864, by rfl⟩ : syracuseStep 1055819 = 1583729) B1583729
theorem B1055831 : Blo 702318 1055831 := bstep (se 1 (by rfl) ⟨791873, by rfl⟩ : syracuseStep 1055831 = 1583747) B1583747
theorem B793687 : Blo 702318 793687 := bstep (se 1 (by rfl) ⟨595265, by rfl⟩ : syracuseStep 793687 = 1190531) B1190531
theorem B1186967 : Blo 702318 1186967 := bstep (se 1 (by rfl) ⟨890225, by rfl⟩ : syracuseStep 1186967 = 1780451) B1780451
theorem B1055897 : Blo 702318 1055897 := bstep (se 2 (by rfl) ⟨395961, by rfl⟩ : syracuseStep 1055897 = 791923) B791923
theorem B1056011 : Blo 702318 1056011 := bstep (se 1 (by rfl) ⟨792008, by rfl⟩ : syracuseStep 1056011 = 1584017) B1584017
theorem B793867 : Blo 702318 793867 := bstep (se 1 (by rfl) ⟨595400, by rfl⟩ : syracuseStep 793867 = 1190801) B1190801
theorem B1187095 : Blo 702318 1187095 := bstep (se 1 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 1187095 = 1780643) B1780643
theorem B1056023 : Blo 702318 1056023 := bstep (se 1 (by rfl) ⟨792017, by rfl⟩ : syracuseStep 1056023 = 1584035) B1584035
theorem B1580363 : Blo 702318 1580363 := bstep (se 1 (by rfl) ⟨1185272, by rfl⟩ : syracuseStep 1580363 = 2370545) B2370545
theorem B892235 : Blo 702318 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B1056089 : Blo 702318 1056089 := bstep (se 2 (by rfl) ⟨396033, by rfl⟩ : syracuseStep 1056089 = 792067) B792067
theorem B793975 : Blo 702318 793975 := bstep (se 1 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 793975 = 1190963) B1190963
theorem B1580417 : Blo 702318 1580417 := bstep (se 2 (by rfl) ⟨592656, by rfl⟩ : syracuseStep 1580417 = 1185313) B1185313
theorem B1056203 : Blo 702318 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B1056215 : Blo 702318 1056215 := bstep (se 1 (by rfl) ⟨792161, by rfl⟩ : syracuseStep 1056215 = 1584323) B1584323
theorem B1056281 : Blo 702318 1056281 := bstep (se 2 (by rfl) ⟨396105, by rfl⟩ : syracuseStep 1056281 = 792211) B792211
theorem B794155 : Blo 702318 794155 := bstep (se 1 (by rfl) ⟨595616, by rfl⟩ : syracuseStep 794155 = 1191233) B1191233
theorem B1580633 : Blo 702318 1580633 := bstep (se 2 (by rfl) ⟨592737, by rfl⟩ : syracuseStep 1580633 = 1185475) B1185475
theorem B1056395 : Blo 702318 1056395 := bstep (se 1 (by rfl) ⟨792296, by rfl⟩ : syracuseStep 1056395 = 1584593) B1584593
theorem B1056407 : Blo 702318 1056407 := bstep (se 1 (by rfl) ⟨792305, by rfl⟩ : syracuseStep 1056407 = 1584611) B1584611
theorem B794263 : Blo 702318 794263 := bstep (se 1 (by rfl) ⟨595697, by rfl⟩ : syracuseStep 794263 = 1191395) B1191395
theorem B1580723 : Blo 702318 1580723 := bstep (se 1 (by rfl) ⟨1185542, by rfl⟩ : syracuseStep 1580723 = 2371085) B2371085
theorem B1580759 : Blo 702318 1580759 := bstep (se 1 (by rfl) ⟨1185569, by rfl⟩ : syracuseStep 1580759 = 2371139) B2371139
theorem B1056473 : Blo 702318 1056473 := bstep (se 2 (by rfl) ⟨396177, by rfl⟩ : syracuseStep 1056473 = 792355) B792355
theorem B1056587 : Blo 702318 1056587 := bstep (se 1 (by rfl) ⟨792440, by rfl⟩ : syracuseStep 1056587 = 1584881) B1584881
theorem B794443 : Blo 702318 794443 := bstep (se 1 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 794443 = 1191665) B1191665
theorem B1056599 : Blo 702318 1056599 := bstep (se 1 (by rfl) ⟨792449, by rfl⟩ : syracuseStep 1056599 = 1584899) B1584899
theorem B3383171 : Blo 702318 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B1580939 : Blo 702318 1580939 := bstep (se 1 (by rfl) ⟨1185704, by rfl⟩ : syracuseStep 1580939 = 2371409) B2371409
theorem B1187723 : Blo 702318 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B1056665 : Blo 702318 1056665 := bstep (se 2 (by rfl) ⟨396249, by rfl⟩ : syracuseStep 1056665 = 792499) B792499
theorem B794551 : Blo 702318 794551 := bstep (se 1 (by rfl) ⟨595913, by rfl⟩ : syracuseStep 794551 = 1191827) B1191827
theorem B1580993 : Blo 702318 1580993 := bstep (se 2 (by rfl) ⟨592872, by rfl⟩ : syracuseStep 1580993 = 1185745) B1185745
theorem B1187851 : Blo 702318 1187851 := bstep (se 1 (by rfl) ⟨890888, by rfl⟩ : syracuseStep 1187851 = 1781777) B1781777
theorem B1056779 : Blo 702318 1056779 := bstep (se 1 (by rfl) ⟨792584, by rfl⟩ : syracuseStep 1056779 = 1585169) B1585169
theorem B892939 : Blo 702318 892939 := bstep (se 1 (by rfl) ⟨669704, by rfl⟩ : syracuseStep 892939 = 1339409) B1339409
theorem B1056791 : Blo 702318 1056791 := bstep (se 1 (by rfl) ⟨792593, by rfl⟩ : syracuseStep 1056791 = 1585187) B1585187
theorem B1056857 : Blo 702318 1056857 := bstep (se 2 (by rfl) ⟨396321, by rfl⟩ : syracuseStep 1056857 = 792643) B792643
theorem B1581209 : Blo 702318 1581209 := bstep (se 2 (by rfl) ⟨592953, by rfl⟩ : syracuseStep 1581209 = 1185907) B1185907
theorem B1187993 : Blo 702318 1187993 := bstep (se 2 (by rfl) ⟨445497, by rfl⟩ : syracuseStep 1187993 = 890995) B890995
theorem B1056971 : Blo 702318 1056971 := bstep (se 1 (by rfl) ⟨792728, by rfl⟩ : syracuseStep 1056971 = 1585457) B1585457
theorem B1056983 : Blo 702318 1056983 := bstep (se 1 (by rfl) ⟨792737, by rfl⟩ : syracuseStep 1056983 = 1585475) B1585475
theorem B1581299 : Blo 702318 1581299 := bstep (se 1 (by rfl) ⟨1185974, by rfl⟩ : syracuseStep 1581299 = 2371949) B2371949
theorem B1581335 : Blo 702318 1581335 := bstep (se 1 (by rfl) ⟨1186001, by rfl⟩ : syracuseStep 1581335 = 2372003) B2372003
theorem B893207 : Blo 702318 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B1188121 : Blo 702318 1188121 := bstep (se 2 (by rfl) ⟨445545, by rfl⟩ : syracuseStep 1188121 = 891091) B891091
theorem B1057049 : Blo 702318 1057049 := bstep (se 2 (by rfl) ⟨396393, by rfl⟩ : syracuseStep 1057049 = 792787) B792787
theorem B4006219 : Blo 702318 4006219 := bstep (se 1 (by rfl) ⟨3004664, by rfl⟩ : syracuseStep 4006219 = 6009329) B6009329
theorem B1057163 : Blo 702318 1057163 := bstep (se 1 (by rfl) ⟨792872, by rfl⟩ : syracuseStep 1057163 = 1585745) B1585745
theorem B1778071 : Blo 702318 1778071 := bstep (se 1 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 1778071 = 2667107) B2667107
theorem B1057175 : Blo 702318 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B1581515 : Blo 702318 1581515 := bstep (se 1 (by rfl) ⟨1186136, by rfl⟩ : syracuseStep 1581515 = 2372273) B2372273
theorem B1057241 : Blo 702318 1057241 := bstep (se 2 (by rfl) ⟨396465, by rfl⟩ : syracuseStep 1057241 = 792931) B792931
theorem B1581569 : Blo 702318 1581569 := bstep (se 2 (by rfl) ⟨593088, by rfl⟩ : syracuseStep 1581569 = 1186177) B1186177
theorem B2531843 : Blo 702318 2531843 := bstep (se 1 (by rfl) ⟨1898882, by rfl⟩ : syracuseStep 2531843 = 3797765) B3797765
theorem B12329489 : Blo 702318 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B2007575 : Blo 702318 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B1057355 : Blo 702318 1057355 := bstep (se 1 (by rfl) ⟨793016, by rfl⟩ : syracuseStep 1057355 = 1586033) B1586033
theorem B1057367 : Blo 702318 1057367 := bstep (se 1 (by rfl) ⟨793025, by rfl⟩ : syracuseStep 1057367 = 1586051) B1586051
theorem B4006493 : Blo 702318 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B3383939 : Blo 702318 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B1057433 : Blo 702318 1057433 := bstep (se 2 (by rfl) ⟨396537, by rfl⟩ : syracuseStep 1057433 = 793075) B793075
theorem B1581785 : Blo 702318 1581785 := bstep (se 2 (by rfl) ⟨593169, by rfl⟩ : syracuseStep 1581785 = 1186339) B1186339
theorem B1057547 : Blo 702318 1057547 := bstep (se 1 (by rfl) ⟨793160, by rfl⟩ : syracuseStep 1057547 = 1586321) B1586321
theorem B1057559 : Blo 702318 1057559 := bstep (se 1 (by rfl) ⟨793169, by rfl⟩ : syracuseStep 1057559 = 1586339) B1586339
theorem B1581875 : Blo 702318 1581875 := bstep (se 1 (by rfl) ⟨1186406, by rfl⟩ : syracuseStep 1581875 = 2372813) B2372813
theorem B1778507 : Blo 702318 1778507 := bstep (se 1 (by rfl) ⟨1333880, by rfl⟩ : syracuseStep 1778507 = 2667761) B2667761
theorem B1581911 : Blo 702318 1581911 := bstep (se 1 (by rfl) ⟨1186433, by rfl⟩ : syracuseStep 1581911 = 2372867) B2372867
theorem B1188695 : Blo 702318 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B1057625 : Blo 702318 1057625 := bstep (se 2 (by rfl) ⟨396609, by rfl⟩ : syracuseStep 1057625 = 793219) B793219
theorem B3810199 : Blo 702318 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B8364977 : Blo 702318 8364977 := bstep (se 2 (by rfl) ⟨3136866, by rfl⟩ : syracuseStep 8364977 = 6273733) B6273733
theorem B1057739 : Blo 702318 1057739 := bstep (se 1 (by rfl) ⟨793304, by rfl⟩ : syracuseStep 1057739 = 1586609) B1586609
theorem B1188823 : Blo 702318 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B1057751 : Blo 702318 1057751 := bstep (se 1 (by rfl) ⟨793313, by rfl⟩ : syracuseStep 1057751 = 1586627) B1586627
theorem B893911 : Blo 702318 893911 := bstep (se 1 (by rfl) ⟨670433, by rfl⟩ : syracuseStep 893911 = 1340867) B1340867
theorem B1582091 : Blo 702318 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B1057817 : Blo 702318 1057817 := bstep (se 2 (by rfl) ⟨396681, by rfl⟩ : syracuseStep 1057817 = 793363) B793363
theorem B1582145 : Blo 702318 1582145 := bstep (se 2 (by rfl) ⟨593304, by rfl⟩ : syracuseStep 1582145 = 1186609) B1186609
theorem B1057931 : Blo 702318 1057931 := bstep (se 1 (by rfl) ⟨793448, by rfl⟩ : syracuseStep 1057931 = 1586897) B1586897
theorem B1057943 : Blo 702318 1057943 := bstep (se 1 (by rfl) ⟨793457, by rfl⟩ : syracuseStep 1057943 = 1586915) B1586915
theorem B1778881 : Blo 702318 1778881 := bstep (se 2 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 1778881 = 1334161) B1334161
theorem B1058009 : Blo 702318 1058009 := bstep (se 2 (by rfl) ⟨396753, by rfl⟩ : syracuseStep 1058009 = 793507) B793507
theorem B1582361 : Blo 702318 1582361 := bstep (se 2 (by rfl) ⟨593385, by rfl⟩ : syracuseStep 1582361 = 1186771) B1186771
theorem B2008385 : Blo 702318 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B1058123 : Blo 702318 1058123 := bstep (se 1 (by rfl) ⟨793592, by rfl⟩ : syracuseStep 1058123 = 1587185) B1587185
theorem B1058135 : Blo 702318 1058135 := bstep (se 1 (by rfl) ⟨793601, by rfl⟩ : syracuseStep 1058135 = 1587203) B1587203
theorem B1582451 : Blo 702318 1582451 := bstep (se 1 (by rfl) ⟨1186838, by rfl⟩ : syracuseStep 1582451 = 2373677) B2373677
theorem B1582487 : Blo 702318 1582487 := bstep (se 1 (by rfl) ⟨1186865, by rfl⟩ : syracuseStep 1582487 = 2373731) B2373731
theorem B1058201 : Blo 702318 1058201 := bstep (se 2 (by rfl) ⟨396825, by rfl⟩ : syracuseStep 1058201 = 793651) B793651
theorem B1058315 : Blo 702318 1058315 := bstep (se 1 (by rfl) ⟨793736, by rfl⟩ : syracuseStep 1058315 = 1587473) B1587473
theorem B1058327 : Blo 702318 1058327 := bstep (se 1 (by rfl) ⟨793745, by rfl⟩ : syracuseStep 1058327 = 1587491) B1587491
theorem B1582667 : Blo 702318 1582667 := bstep (se 1 (by rfl) ⟨1187000, by rfl⟩ : syracuseStep 1582667 = 2374001) B2374001
theorem B1189451 : Blo 702318 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B1058393 : Blo 702318 1058393 := bstep (se 2 (by rfl) ⟨396897, by rfl⟩ : syracuseStep 1058393 = 793795) B793795
theorem B1582721 : Blo 702318 1582721 := bstep (se 2 (by rfl) ⟨593520, by rfl⟩ : syracuseStep 1582721 = 1187041) B1187041
theorem B1189579 : Blo 702318 1189579 := bstep (se 1 (by rfl) ⟨892184, by rfl⟩ : syracuseStep 1189579 = 1784369) B1784369
theorem B1058507 : Blo 702318 1058507 := bstep (se 1 (by rfl) ⟨793880, by rfl⟩ : syracuseStep 1058507 = 1587761) B1587761
theorem B1058519 : Blo 702318 1058519 := bstep (se 1 (by rfl) ⟨793889, by rfl⟩ : syracuseStep 1058519 = 1587779) B1587779
theorem B1779479 : Blo 702318 1779479 := bstep (se 1 (by rfl) ⟨1334609, by rfl⟩ : syracuseStep 1779479 = 2669219) B2669219
theorem B1058585 : Blo 702318 1058585 := bstep (se 2 (by rfl) ⟨396969, by rfl⟩ : syracuseStep 1058585 = 793939) B793939
theorem B1582937 : Blo 702318 1582937 := bstep (se 2 (by rfl) ⟨593601, by rfl⟩ : syracuseStep 1582937 = 1187203) B1187203
theorem B1189721 : Blo 702318 1189721 := bstep (se 2 (by rfl) ⟨446145, by rfl⟩ : syracuseStep 1189721 = 892291) B892291
theorem B1058699 : Blo 702318 1058699 := bstep (se 1 (by rfl) ⟨794024, by rfl⟩ : syracuseStep 1058699 = 1588049) B1588049
theorem B1058711 : Blo 702318 1058711 := bstep (se 1 (by rfl) ⟨794033, by rfl⟩ : syracuseStep 1058711 = 1588067) B1588067
theorem B5351345 : Blo 702318 5351345 := bstep (se 2 (by rfl) ⟨2006754, by rfl⟩ : syracuseStep 5351345 = 4013509) B4013509
theorem B1583027 : Blo 702318 1583027 := bstep (se 1 (by rfl) ⟨1187270, by rfl⟩ : syracuseStep 1583027 = 2374541) B2374541
theorem B1583063 : Blo 702318 1583063 := bstep (se 1 (by rfl) ⟨1187297, by rfl⟩ : syracuseStep 1583063 = 2374595) B2374595
theorem B1189849 : Blo 702318 1189849 := bstep (se 2 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 1189849 = 892387) B892387
theorem B1058777 : Blo 702318 1058777 := bstep (se 2 (by rfl) ⟨397041, by rfl⟩ : syracuseStep 1058777 = 794083) B794083
theorem B1058891 : Blo 702318 1058891 := bstep (se 1 (by rfl) ⟨794168, by rfl⟩ : syracuseStep 1058891 = 1588337) B1588337
theorem B1058903 : Blo 702318 1058903 := bstep (se 1 (by rfl) ⟨794177, by rfl⟩ : syracuseStep 1058903 = 1588355) B1588355
theorem B1583243 : Blo 702318 1583243 := bstep (se 1 (by rfl) ⟨1187432, by rfl⟩ : syracuseStep 1583243 = 2374865) B2374865
theorem B1058969 : Blo 702318 1058969 := bstep (se 2 (by rfl) ⟨397113, by rfl⟩ : syracuseStep 1058969 = 794227) B794227
theorem B1583297 : Blo 702318 1583297 := bstep (se 2 (by rfl) ⟨593736, by rfl⟩ : syracuseStep 1583297 = 1187473) B1187473
theorem B1059083 : Blo 702318 1059083 := bstep (se 1 (by rfl) ⟨794312, by rfl⟩ : syracuseStep 1059083 = 1588625) B1588625
theorem B1059095 : Blo 702318 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B1059161 : Blo 702318 1059161 := bstep (se 2 (by rfl) ⟨397185, by rfl⟩ : syracuseStep 1059161 = 794371) B794371
theorem B5351831 : Blo 702318 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B1583513 : Blo 702318 1583513 := bstep (se 2 (by rfl) ⟨593817, by rfl⟩ : syracuseStep 1583513 = 1187635) B1187635
theorem B1059275 : Blo 702318 1059275 := bstep (se 1 (by rfl) ⟨794456, by rfl⟩ : syracuseStep 1059275 = 1588913) B1588913
theorem B1059287 : Blo 702318 1059287 := bstep (se 1 (by rfl) ⟨794465, by rfl⟩ : syracuseStep 1059287 = 1588931) B1588931
theorem B1583603 : Blo 702318 1583603 := bstep (se 1 (by rfl) ⟨1187702, by rfl⟩ : syracuseStep 1583603 = 2375405) B2375405
theorem B1583639 : Blo 702318 1583639 := bstep (se 1 (by rfl) ⟨1187729, by rfl⟩ : syracuseStep 1583639 = 2375459) B2375459
theorem B1190423 : Blo 702318 1190423 := bstep (se 1 (by rfl) ⟨892817, by rfl⟩ : syracuseStep 1190423 = 1785635) B1785635
theorem B1059353 : Blo 702318 1059353 := bstep (se 2 (by rfl) ⟨397257, by rfl⟩ : syracuseStep 1059353 = 794515) B794515
theorem B1780289 : Blo 702318 1780289 := bstep (se 2 (by rfl) ⟨667608, by rfl⟩ : syracuseStep 1780289 = 1335217) B1335217
theorem B3385921 : Blo 702318 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B1059467 : Blo 702318 1059467 := bstep (se 1 (by rfl) ⟨794600, by rfl⟩ : syracuseStep 1059467 = 1589201) B1589201
theorem B2534033 : Blo 702318 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B1190551 : Blo 702318 1190551 := bstep (se 1 (by rfl) ⟨892913, by rfl⟩ : syracuseStep 1190551 = 1785827) B1785827
theorem B1583819 : Blo 702318 1583819 := bstep (se 1 (by rfl) ⟨1187864, by rfl⟩ : syracuseStep 1583819 = 2375729) B2375729
theorem B1583873 : Blo 702318 1583873 := bstep (se 2 (by rfl) ⟨593952, by rfl⟩ : syracuseStep 1583873 = 1187905) B1187905
theorem B2534323 : Blo 702318 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B3812275 : Blo 702318 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B2010035 : Blo 702318 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B2010059 : Blo 702318 2010059 := bstep (se 1 (by rfl) ⟨1507544, by rfl⟩ : syracuseStep 2010059 = 3015089) B3015089
theorem B12331993 : Blo 702318 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B1584089 : Blo 702318 1584089 := bstep (se 2 (by rfl) ⟨594033, by rfl⟩ : syracuseStep 1584089 = 1188067) B1188067
theorem B1584179 : Blo 702318 1584179 := bstep (se 1 (by rfl) ⟨1188134, by rfl⟩ : syracuseStep 1584179 = 2376269) B2376269
theorem B1584215 : Blo 702318 1584215 := bstep (se 1 (by rfl) ⟨1188161, by rfl⟩ : syracuseStep 1584215 = 2376323) B2376323
theorem B1780825 : Blo 702318 1780825 := bstep (se 2 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 1780825 = 1335619) B1335619
theorem B2370653 : Blo 702318 2370653 := bstep (se 3 (by rfl) ⟨444497, by rfl⟩ : syracuseStep 2370653 = 888995) B888995
theorem B1584395 : Blo 702318 1584395 := bstep (se 1 (by rfl) ⟨1188296, by rfl⟩ : syracuseStep 1584395 = 2376593) B2376593
theorem B1191179 : Blo 702318 1191179 := bstep (se 1 (by rfl) ⟨893384, by rfl⟩ : syracuseStep 1191179 = 1786769) B1786769
theorem B1584449 : Blo 702318 1584449 := bstep (se 2 (by rfl) ⟨594168, by rfl⟩ : syracuseStep 1584449 = 1188337) B1188337
theorem B1191307 : Blo 702318 1191307 := bstep (se 1 (by rfl) ⟨893480, by rfl⟩ : syracuseStep 1191307 = 1786961) B1786961
theorem B1584665 : Blo 702318 1584665 := bstep (se 2 (by rfl) ⟨594249, by rfl⟩ : syracuseStep 1584665 = 1188499) B1188499
theorem B1191449 : Blo 702318 1191449 := bstep (se 2 (by rfl) ⟨446793, by rfl⟩ : syracuseStep 1191449 = 893587) B893587
theorem B1584755 : Blo 702318 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B1584791 : Blo 702318 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B1191577 : Blo 702318 1191577 := bstep (se 2 (by rfl) ⟨446841, by rfl⟩ : syracuseStep 1191577 = 893683) B893683
theorem B3124939 : Blo 702318 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B2010845 : Blo 702318 2010845 := bstep (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) B754067
theorem B1584971 : Blo 702318 1584971 := bstep (se 1 (by rfl) ⟨1188728, by rfl⟩ : syracuseStep 1584971 = 2377457) B2377457
theorem B6762341 : Blo 702318 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B1585025 : Blo 702318 1585025 := bstep (se 2 (by rfl) ⟨594384, by rfl⟩ : syracuseStep 1585025 = 1188769) B1188769
theorem B12857305 : Blo 702318 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B2830301 : Blo 702318 2830301 := bstep (se 3 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 2830301 = 1061363) B1061363
theorem B10137635 : Blo 702318 10137635 := bstep (se 1 (by rfl) ⟨7603226, by rfl⟩ : syracuseStep 10137635 = 15206453) B15206453
theorem B1585241 : Blo 702318 1585241 := bstep (se 2 (by rfl) ⟨594465, by rfl⟩ : syracuseStep 1585241 = 1188931) B1188931
theorem B1781939 : Blo 702318 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B1585331 : Blo 702318 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B2371787 : Blo 702318 2371787 := bstep (se 1 (by rfl) ⟨1778840, by rfl⟩ : syracuseStep 2371787 = 3557681) B3557681
theorem B1585367 : Blo 702318 1585367 := bstep (se 1 (by rfl) ⟨1189025, by rfl⟩ : syracuseStep 1585367 = 2378051) B2378051
theorem B2666803 : Blo 702318 2666803 := bstep (se 1 (by rfl) ⟨2000102, by rfl⟩ : syracuseStep 2666803 = 4000205) B4000205
theorem B1585547 : Blo 702318 1585547 := bstep (se 1 (by rfl) ⟨1189160, by rfl⟩ : syracuseStep 1585547 = 2378321) B2378321
theorem B1585601 : Blo 702318 1585601 := bstep (se 2 (by rfl) ⟨594600, by rfl⟩ : syracuseStep 1585601 = 1189201) B1189201
theorem B2372057 : Blo 702318 2372057 := bstep (se 2 (by rfl) ⟨889521, by rfl⟩ : syracuseStep 2372057 = 1779043) B1779043
theorem B1782233 : Blo 702318 1782233 := bstep (se 2 (by rfl) ⟨668337, by rfl⟩ : syracuseStep 1782233 = 1336675) B1336675
theorem B8565209 : Blo 702318 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B2863667 : Blo 702318 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B1356353 : Blo 702318 1356353 := bstep (se 2 (by rfl) ⟨508632, by rfl⟩ : syracuseStep 1356353 = 1017265) B1017265
theorem B1585817 : Blo 702318 1585817 := bstep (se 2 (by rfl) ⟨594681, by rfl⟩ : syracuseStep 1585817 = 1189363) B1189363
theorem B1585907 : Blo 702318 1585907 := bstep (se 1 (by rfl) ⟨1189430, by rfl⟩ : syracuseStep 1585907 = 2378861) B2378861
theorem B1585943 : Blo 702318 1585943 := bstep (se 1 (by rfl) ⟨1189457, by rfl⟩ : syracuseStep 1585943 = 2378915) B2378915
theorem B21672805 : Blo 702318 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B1586123 : Blo 702318 1586123 := bstep (se 1 (by rfl) ⟨1189592, by rfl⟩ : syracuseStep 1586123 = 2379185) B2379185
theorem B2175947 : Blo 702318 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1586177 : Blo 702318 1586177 := bstep (se 2 (by rfl) ⟨594816, by rfl⟩ : syracuseStep 1586177 = 1189633) B1189633
theorem B6435875 : Blo 702318 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B3519533 : Blo 702318 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B1127513 : Blo 702318 1127513 := bstep (se 2 (by rfl) ⟨422817, by rfl⟩ : syracuseStep 1127513 = 845635) B845635
theorem B2372759 : Blo 702318 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B1586393 : Blo 702318 1586393 := bstep (se 2 (by rfl) ⟨594897, by rfl⟩ : syracuseStep 1586393 = 1189795) B1189795
theorem B1586483 : Blo 702318 1586483 := bstep (se 1 (by rfl) ⟨1189862, by rfl⟩ : syracuseStep 1586483 = 2379725) B2379725
theorem B1586519 : Blo 702318 1586519 := bstep (se 1 (by rfl) ⟨1189889, by rfl⟩ : syracuseStep 1586519 = 2379779) B2379779
theorem B4273559 : Blo 702318 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B1586699 : Blo 702318 1586699 := bstep (se 1 (by rfl) ⟨1190024, by rfl⟩ : syracuseStep 1586699 = 2380049) B2380049
theorem B2668049 : Blo 702318 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B1586753 : Blo 702318 1586753 := bstep (se 2 (by rfl) ⟨595032, by rfl⟩ : syracuseStep 1586753 = 1190065) B1190065
theorem B73021013 : Blo 702318 73021013 := bstep (se 8 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 73021013 = 855715) B855715
theorem B12826205 : Blo 702318 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B3815063 : Blo 702318 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B2373299 : Blo 702318 2373299 := bstep (se 1 (by rfl) ⟨1779974, by rfl⟩ : syracuseStep 2373299 = 3559949) B3559949
theorem B1586969 : Blo 702318 1586969 := bstep (se 2 (by rfl) ⟨595113, by rfl⟩ : syracuseStep 1586969 = 1190227) B1190227
theorem B4011869 : Blo 702318 4011869 := bstep (se 3 (by rfl) ⟨752225, by rfl⟩ : syracuseStep 4011869 = 1504451) B1504451
theorem B1587059 : Blo 702318 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B702327 : Blo 702318 702327 := bstep (se 1 (by rfl) ⟨526745, by rfl⟩ : syracuseStep 702327 = 1053491) B1053491
theorem B702347 : Blo 702318 702347 := bstep (se 1 (by rfl) ⟨526760, by rfl⟩ : syracuseStep 702347 = 1053521) B1053521
theorem B702359 : Blo 702318 702359 := bstep (se 1 (by rfl) ⟨526769, by rfl⟩ : syracuseStep 702359 = 1053539) B1053539
theorem B1587095 : Blo 702318 1587095 := bstep (se 1 (by rfl) ⟨1190321, by rfl⟩ : syracuseStep 1587095 = 2380643) B2380643
theorem B702379 : Blo 702318 702379 := bstep (se 1 (by rfl) ⟨526784, by rfl⟩ : syracuseStep 702379 = 1053569) B1053569
theorem B3094451 : Blo 702318 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B702391 : Blo 702318 702391 := bstep (se 1 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 702391 = 1053587) B1053587
theorem B2373569 : Blo 702318 2373569 := bstep (se 2 (by rfl) ⟨890088, by rfl⟩ : syracuseStep 2373569 = 1780177) B1780177
theorem B702411 : Blo 702318 702411 := bstep (se 1 (by rfl) ⟨526808, by rfl⟩ : syracuseStep 702411 = 1053617) B1053617
theorem B702423 : Blo 702318 702423 := bstep (se 1 (by rfl) ⟨526817, by rfl⟩ : syracuseStep 702423 = 1053635) B1053635
theorem B702443 : Blo 702318 702443 := bstep (se 1 (by rfl) ⟨526832, by rfl⟩ : syracuseStep 702443 = 1053665) B1053665
theorem B702455 : Blo 702318 702455 := bstep (se 1 (by rfl) ⟨526841, by rfl⟩ : syracuseStep 702455 = 1053683) B1053683
theorem B702475 : Blo 702318 702475 := bstep (se 1 (by rfl) ⟨526856, by rfl⟩ : syracuseStep 702475 = 1053713) B1053713
theorem B702487 : Blo 702318 702487 := bstep (se 1 (by rfl) ⟨526865, by rfl⟩ : syracuseStep 702487 = 1053731) B1053731
theorem B702507 : Blo 702318 702507 := bstep (se 1 (by rfl) ⟨526880, by rfl⟩ : syracuseStep 702507 = 1053761) B1053761
theorem B702519 : Blo 702318 702519 := bstep (se 1 (by rfl) ⟨526889, by rfl⟩ : syracuseStep 702519 = 1053779) B1053779
theorem B702539 : Blo 702318 702539 := bstep (se 1 (by rfl) ⟨526904, by rfl⟩ : syracuseStep 702539 = 1053809) B1053809
theorem B1783883 : Blo 702318 1783883 := bstep (se 1 (by rfl) ⟨1337912, by rfl⟩ : syracuseStep 1783883 = 2675825) B2675825
theorem B1587275 : Blo 702318 1587275 := bstep (se 1 (by rfl) ⟨1190456, by rfl⟩ : syracuseStep 1587275 = 2380913) B2380913
theorem B702551 : Blo 702318 702551 := bstep (se 1 (by rfl) ⟨526913, by rfl⟩ : syracuseStep 702551 = 1053827) B1053827
theorem B702571 : Blo 702318 702571 := bstep (se 1 (by rfl) ⟨526928, by rfl⟩ : syracuseStep 702571 = 1053857) B1053857
theorem B702583 : Blo 702318 702583 := bstep (se 1 (by rfl) ⟨526937, by rfl⟩ : syracuseStep 702583 = 1053875) B1053875
theorem B1587329 : Blo 702318 1587329 := bstep (se 2 (by rfl) ⟨595248, by rfl⟩ : syracuseStep 1587329 = 1190497) B1190497
theorem B702603 : Blo 702318 702603 := bstep (se 1 (by rfl) ⟨526952, by rfl⟩ : syracuseStep 702603 = 1053905) B1053905
theorem B702615 : Blo 702318 702615 := bstep (se 1 (by rfl) ⟨526961, by rfl⟩ : syracuseStep 702615 = 1053923) B1053923
theorem B702635 : Blo 702318 702635 := bstep (se 1 (by rfl) ⟨526976, by rfl⟩ : syracuseStep 702635 = 1053953) B1053953
theorem B702647 : Blo 702318 702647 := bstep (se 1 (by rfl) ⟨526985, by rfl⟩ : syracuseStep 702647 = 1053971) B1053971
theorem B702667 : Blo 702318 702667 := bstep (se 1 (by rfl) ⟨527000, by rfl⟩ : syracuseStep 702667 = 1054001) B1054001
theorem B2668747 : Blo 702318 2668747 := bstep (se 1 (by rfl) ⟨2001560, by rfl⟩ : syracuseStep 2668747 = 4003121) B4003121
theorem B702679 : Blo 702318 702679 := bstep (se 1 (by rfl) ⟨527009, by rfl⟩ : syracuseStep 702679 = 1054019) B1054019
theorem B702699 : Blo 702318 702699 := bstep (se 1 (by rfl) ⟨527024, by rfl⟩ : syracuseStep 702699 = 1054049) B1054049
theorem B702711 : Blo 702318 702711 := bstep (se 1 (by rfl) ⟨527033, by rfl⟩ : syracuseStep 702711 = 1054067) B1054067
theorem B702731 : Blo 702318 702731 := bstep (se 1 (by rfl) ⟨527048, by rfl⟩ : syracuseStep 702731 = 1054097) B1054097
theorem B702743 : Blo 702318 702743 := bstep (se 1 (by rfl) ⟨527057, by rfl⟩ : syracuseStep 702743 = 1054115) B1054115
theorem B702763 : Blo 702318 702763 := bstep (se 1 (by rfl) ⟨527072, by rfl⟩ : syracuseStep 702763 = 1054145) B1054145
theorem B702775 : Blo 702318 702775 := bstep (se 1 (by rfl) ⟨527081, by rfl⟩ : syracuseStep 702775 = 1054163) B1054163
theorem B702795 : Blo 702318 702795 := bstep (se 1 (by rfl) ⟨527096, by rfl⟩ : syracuseStep 702795 = 1054193) B1054193
theorem B702807 : Blo 702318 702807 := bstep (se 1 (by rfl) ⟨527105, by rfl⟩ : syracuseStep 702807 = 1054211) B1054211
theorem B1587545 : Blo 702318 1587545 := bstep (se 2 (by rfl) ⟨595329, by rfl⟩ : syracuseStep 1587545 = 1190659) B1190659
theorem B702827 : Blo 702318 702827 := bstep (se 1 (by rfl) ⟨527120, by rfl⟩ : syracuseStep 702827 = 1054241) B1054241
theorem B702839 : Blo 702318 702839 := bstep (se 1 (by rfl) ⟨527129, by rfl⟩ : syracuseStep 702839 = 1054259) B1054259
theorem B702859 : Blo 702318 702859 := bstep (se 1 (by rfl) ⟨527144, by rfl⟩ : syracuseStep 702859 = 1054289) B1054289
theorem B702871 : Blo 702318 702871 := bstep (se 1 (by rfl) ⟨527153, by rfl⟩ : syracuseStep 702871 = 1054307) B1054307
theorem B702891 : Blo 702318 702891 := bstep (se 1 (by rfl) ⟨527168, by rfl⟩ : syracuseStep 702891 = 1054337) B1054337
theorem B1587635 : Blo 702318 1587635 := bstep (se 1 (by rfl) ⟨1190726, by rfl⟩ : syracuseStep 1587635 = 2381453) B2381453
theorem B702903 : Blo 702318 702903 := bstep (se 1 (by rfl) ⟨527177, by rfl⟩ : syracuseStep 702903 = 1054355) B1054355
theorem B702923 : Blo 702318 702923 := bstep (se 1 (by rfl) ⟨527192, by rfl⟩ : syracuseStep 702923 = 1054385) B1054385
theorem B702935 : Blo 702318 702935 := bstep (se 1 (by rfl) ⟨527201, by rfl⟩ : syracuseStep 702935 = 1054403) B1054403
theorem B1587671 : Blo 702318 1587671 := bstep (se 1 (by rfl) ⟨1190753, by rfl⟩ : syracuseStep 1587671 = 2381507) B2381507
theorem B4504025 : Blo 702318 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B2669021 : Blo 702318 2669021 := bstep (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) B1000883
theorem B2374109 : Blo 702318 2374109 := bstep (se 3 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 2374109 = 890291) B890291
theorem B702955 : Blo 702318 702955 := bstep (se 1 (by rfl) ⟨527216, by rfl⟩ : syracuseStep 702955 = 1054433) B1054433
theorem B702967 : Blo 702318 702967 := bstep (se 1 (by rfl) ⟨527225, by rfl⟩ : syracuseStep 702967 = 1054451) B1054451
theorem B702987 : Blo 702318 702987 := bstep (se 1 (by rfl) ⟨527240, by rfl⟩ : syracuseStep 702987 = 1054481) B1054481
theorem B702999 : Blo 702318 702999 := bstep (se 1 (by rfl) ⟨527249, by rfl⟩ : syracuseStep 702999 = 1054499) B1054499
theorem B1522199 : Blo 702318 1522199 := bstep (se 1 (by rfl) ⟨1141649, by rfl⟩ : syracuseStep 1522199 = 2283299) B2283299
theorem B703019 : Blo 702318 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B703031 : Blo 702318 703031 := bstep (se 1 (by rfl) ⟨527273, by rfl⟩ : syracuseStep 703031 = 1054547) B1054547
theorem B703051 : Blo 702318 703051 := bstep (se 1 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 703051 = 1054577) B1054577
theorem B703063 : Blo 702318 703063 := bstep (se 1 (by rfl) ⟨527297, by rfl⟩ : syracuseStep 703063 = 1054595) B1054595
theorem B703083 : Blo 702318 703083 := bstep (se 1 (by rfl) ⟨527312, by rfl⟩ : syracuseStep 703083 = 1054625) B1054625
theorem B703095 : Blo 702318 703095 := bstep (se 1 (by rfl) ⟨527321, by rfl⟩ : syracuseStep 703095 = 1054643) B1054643
theorem B703115 : Blo 702318 703115 := bstep (se 1 (by rfl) ⟨527336, by rfl⟩ : syracuseStep 703115 = 1054673) B1054673
theorem B1587851 : Blo 702318 1587851 := bstep (se 1 (by rfl) ⟨1190888, by rfl⟩ : syracuseStep 1587851 = 2381777) B2381777
theorem B703127 : Blo 702318 703127 := bstep (se 1 (by rfl) ⟨527345, by rfl⟩ : syracuseStep 703127 = 1054691) B1054691
theorem B703147 : Blo 702318 703147 := bstep (se 1 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 703147 = 1054721) B1054721
theorem B703159 : Blo 702318 703159 := bstep (se 1 (by rfl) ⟨527369, by rfl⟩ : syracuseStep 703159 = 1054739) B1054739
theorem B1587905 : Blo 702318 1587905 := bstep (se 2 (by rfl) ⟨595464, by rfl⟩ : syracuseStep 1587905 = 1190929) B1190929
theorem B703179 : Blo 702318 703179 := bstep (se 1 (by rfl) ⟨527384, by rfl⟩ : syracuseStep 703179 = 1054769) B1054769
theorem B703191 : Blo 702318 703191 := bstep (se 1 (by rfl) ⟨527393, by rfl⟩ : syracuseStep 703191 = 1054787) B1054787
theorem B703211 : Blo 702318 703211 := bstep (se 1 (by rfl) ⟨527408, by rfl⟩ : syracuseStep 703211 = 1054817) B1054817
theorem B703223 : Blo 702318 703223 := bstep (se 1 (by rfl) ⟨527417, by rfl⟩ : syracuseStep 703223 = 1054835) B1054835
theorem B703243 : Blo 702318 703243 := bstep (se 1 (by rfl) ⟨527432, by rfl⟩ : syracuseStep 703243 = 1054865) B1054865
theorem B703255 : Blo 702318 703255 := bstep (se 1 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 703255 = 1054883) B1054883
theorem B703275 : Blo 702318 703275 := bstep (se 1 (by rfl) ⟨527456, by rfl⟩ : syracuseStep 703275 = 1054913) B1054913
theorem B703287 : Blo 702318 703287 := bstep (se 1 (by rfl) ⟨527465, by rfl⟩ : syracuseStep 703287 = 1054931) B1054931
theorem B703307 : Blo 702318 703307 := bstep (se 1 (by rfl) ⟨527480, by rfl⟩ : syracuseStep 703307 = 1054961) B1054961
theorem B703319 : Blo 702318 703319 := bstep (se 1 (by rfl) ⟨527489, by rfl⟩ : syracuseStep 703319 = 1054979) B1054979
theorem B703339 : Blo 702318 703339 := bstep (se 1 (by rfl) ⟨527504, by rfl⟩ : syracuseStep 703339 = 1055009) B1055009
theorem B703351 : Blo 702318 703351 := bstep (se 1 (by rfl) ⟨527513, by rfl⟩ : syracuseStep 703351 = 1055027) B1055027
theorem B703371 : Blo 702318 703371 := bstep (se 1 (by rfl) ⟨527528, by rfl⟩ : syracuseStep 703371 = 1055057) B1055057
theorem B703383 : Blo 702318 703383 := bstep (se 1 (by rfl) ⟨527537, by rfl⟩ : syracuseStep 703383 = 1055075) B1055075
theorem B1588121 : Blo 702318 1588121 := bstep (se 2 (by rfl) ⟨595545, by rfl⟩ : syracuseStep 1588121 = 1191091) B1191091
theorem B703403 : Blo 702318 703403 := bstep (se 1 (by rfl) ⟨527552, by rfl⟩ : syracuseStep 703403 = 1055105) B1055105
theorem B703415 : Blo 702318 703415 := bstep (se 1 (by rfl) ⟨527561, by rfl⟩ : syracuseStep 703415 = 1055123) B1055123
theorem B703435 : Blo 702318 703435 := bstep (se 1 (by rfl) ⟨527576, by rfl⟩ : syracuseStep 703435 = 1055153) B1055153
theorem B703447 : Blo 702318 703447 := bstep (se 1 (by rfl) ⟨527585, by rfl⟩ : syracuseStep 703447 = 1055171) B1055171
theorem B703467 : Blo 702318 703467 := bstep (se 1 (by rfl) ⟨527600, by rfl⟩ : syracuseStep 703467 = 1055201) B1055201
theorem B1588211 : Blo 702318 1588211 := bstep (se 1 (by rfl) ⟨1191158, by rfl⟩ : syracuseStep 1588211 = 2382317) B2382317
theorem B703479 : Blo 702318 703479 := bstep (se 1 (by rfl) ⟨527609, by rfl⟩ : syracuseStep 703479 = 1055219) B1055219
theorem B703499 : Blo 702318 703499 := bstep (se 1 (by rfl) ⟨527624, by rfl⟩ : syracuseStep 703499 = 1055249) B1055249
theorem B703511 : Blo 702318 703511 := bstep (se 1 (by rfl) ⟨527633, by rfl⟩ : syracuseStep 703511 = 1055267) B1055267
theorem B1784855 : Blo 702318 1784855 := bstep (se 1 (by rfl) ⟨1338641, by rfl⟩ : syracuseStep 1784855 = 2677283) B2677283
theorem B1588247 : Blo 702318 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B703531 : Blo 702318 703531 := bstep (se 1 (by rfl) ⟨527648, by rfl⟩ : syracuseStep 703531 = 1055297) B1055297
theorem B703543 : Blo 702318 703543 := bstep (se 1 (by rfl) ⟨527657, by rfl⟩ : syracuseStep 703543 = 1055315) B1055315
theorem B703563 : Blo 702318 703563 := bstep (se 1 (by rfl) ⟨527672, by rfl⟩ : syracuseStep 703563 = 1055345) B1055345
theorem B703575 : Blo 702318 703575 := bstep (se 1 (by rfl) ⟨527681, by rfl⟩ : syracuseStep 703575 = 1055363) B1055363
theorem B703595 : Blo 702318 703595 := bstep (se 1 (by rfl) ⟨527696, by rfl⟩ : syracuseStep 703595 = 1055393) B1055393
theorem B703607 : Blo 702318 703607 := bstep (se 1 (by rfl) ⟨527705, by rfl⟩ : syracuseStep 703607 = 1055411) B1055411
theorem B703627 : Blo 702318 703627 := bstep (se 1 (by rfl) ⟨527720, by rfl⟩ : syracuseStep 703627 = 1055441) B1055441
theorem B2538647 : Blo 702318 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B5717143 : Blo 702318 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B2669719 : Blo 702318 2669719 := bstep (se 1 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 2669719 = 4004579) B4004579
theorem B703639 : Blo 702318 703639 := bstep (se 1 (by rfl) ⟨527729, by rfl⟩ : syracuseStep 703639 = 1055459) B1055459
theorem B703659 : Blo 702318 703659 := bstep (se 1 (by rfl) ⟨527744, by rfl⟩ : syracuseStep 703659 = 1055489) B1055489
theorem B703671 : Blo 702318 703671 := bstep (se 1 (by rfl) ⟨527753, by rfl⟩ : syracuseStep 703671 = 1055507) B1055507
theorem B703691 : Blo 702318 703691 := bstep (se 1 (by rfl) ⟨527768, by rfl⟩ : syracuseStep 703691 = 1055537) B1055537
theorem B1588427 : Blo 702318 1588427 := bstep (se 1 (by rfl) ⟨1191320, by rfl⟩ : syracuseStep 1588427 = 2382641) B2382641
theorem B703703 : Blo 702318 703703 := bstep (se 1 (by rfl) ⟨527777, by rfl⟩ : syracuseStep 703703 = 1055555) B1055555
theorem B703723 : Blo 702318 703723 := bstep (se 1 (by rfl) ⟨527792, by rfl⟩ : syracuseStep 703723 = 1055585) B1055585
theorem B703735 : Blo 702318 703735 := bstep (se 1 (by rfl) ⟨527801, by rfl⟩ : syracuseStep 703735 = 1055603) B1055603
theorem B1588481 : Blo 702318 1588481 := bstep (se 2 (by rfl) ⟨595680, by rfl⟩ : syracuseStep 1588481 = 1191361) B1191361
theorem B703755 : Blo 702318 703755 := bstep (se 1 (by rfl) ⟨527816, by rfl⟩ : syracuseStep 703755 = 1055633) B1055633
theorem B703767 : Blo 702318 703767 := bstep (se 1 (by rfl) ⟨527825, by rfl⟩ : syracuseStep 703767 = 1055651) B1055651
theorem B703787 : Blo 702318 703787 := bstep (se 1 (by rfl) ⟨527840, by rfl⟩ : syracuseStep 703787 = 1055681) B1055681
theorem B703799 : Blo 702318 703799 := bstep (se 1 (by rfl) ⟨527849, by rfl⟩ : syracuseStep 703799 = 1055699) B1055699
theorem B703819 : Blo 702318 703819 := bstep (se 1 (by rfl) ⟨527864, by rfl⟩ : syracuseStep 703819 = 1055729) B1055729
theorem B703831 : Blo 702318 703831 := bstep (se 1 (by rfl) ⟨527873, by rfl⟩ : syracuseStep 703831 = 1055747) B1055747
theorem B703851 : Blo 702318 703851 := bstep (se 1 (by rfl) ⟨527888, by rfl⟩ : syracuseStep 703851 = 1055777) B1055777
theorem B703863 : Blo 702318 703863 := bstep (se 1 (by rfl) ⟨527897, by rfl⟩ : syracuseStep 703863 = 1055795) B1055795
theorem B703883 : Blo 702318 703883 := bstep (se 1 (by rfl) ⟨527912, by rfl⟩ : syracuseStep 703883 = 1055825) B1055825
theorem B703895 : Blo 702318 703895 := bstep (se 1 (by rfl) ⟨527921, by rfl⟩ : syracuseStep 703895 = 1055843) B1055843
theorem B703915 : Blo 702318 703915 := bstep (se 1 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 703915 = 1055873) B1055873
theorem B703927 : Blo 702318 703927 := bstep (se 1 (by rfl) ⟨527945, by rfl⟩ : syracuseStep 703927 = 1055891) B1055891
theorem B703947 : Blo 702318 703947 := bstep (se 1 (by rfl) ⟨527960, by rfl⟩ : syracuseStep 703947 = 1055921) B1055921
theorem B703959 : Blo 702318 703959 := bstep (se 1 (by rfl) ⟨527969, by rfl⟩ : syracuseStep 703959 = 1055939) B1055939
theorem B1588697 : Blo 702318 1588697 := bstep (se 2 (by rfl) ⟨595761, by rfl⟩ : syracuseStep 1588697 = 1191523) B1191523
theorem B703979 : Blo 702318 703979 := bstep (se 1 (by rfl) ⟨527984, by rfl⟩ : syracuseStep 703979 = 1055969) B1055969
theorem B703991 : Blo 702318 703991 := bstep (se 1 (by rfl) ⟨527993, by rfl⟩ : syracuseStep 703991 = 1055987) B1055987
theorem B704011 : Blo 702318 704011 := bstep (se 1 (by rfl) ⟨528008, by rfl⟩ : syracuseStep 704011 = 1056017) B1056017
theorem B704023 : Blo 702318 704023 := bstep (se 1 (by rfl) ⟨528017, by rfl⟩ : syracuseStep 704023 = 1056035) B1056035
theorem B704043 : Blo 702318 704043 := bstep (se 1 (by rfl) ⟨528032, by rfl⟩ : syracuseStep 704043 = 1056065) B1056065
theorem B1588787 : Blo 702318 1588787 := bstep (se 1 (by rfl) ⟨1191590, by rfl⟩ : syracuseStep 1588787 = 2383181) B2383181
theorem B704055 : Blo 702318 704055 := bstep (se 1 (by rfl) ⟨528041, by rfl⟩ : syracuseStep 704055 = 1056083) B1056083
theorem B2375243 : Blo 702318 2375243 := bstep (se 1 (by rfl) ⟨1781432, by rfl⟩ : syracuseStep 2375243 = 3562865) B3562865
theorem B704075 : Blo 702318 704075 := bstep (se 1 (by rfl) ⟨528056, by rfl⟩ : syracuseStep 704075 = 1056113) B1056113
theorem B704087 : Blo 702318 704087 := bstep (se 1 (by rfl) ⟨528065, by rfl⟩ : syracuseStep 704087 = 1056131) B1056131
theorem B1588823 : Blo 702318 1588823 := bstep (se 1 (by rfl) ⟨1191617, by rfl⟩ : syracuseStep 1588823 = 2383235) B2383235
theorem B2539097 : Blo 702318 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B704107 : Blo 702318 704107 := bstep (se 1 (by rfl) ⟨528080, by rfl⟩ : syracuseStep 704107 = 1056161) B1056161
theorem B704119 : Blo 702318 704119 := bstep (se 1 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 704119 = 1056179) B1056179
theorem B704139 : Blo 702318 704139 := bstep (se 1 (by rfl) ⟨528104, by rfl⟩ : syracuseStep 704139 = 1056209) B1056209
theorem B704151 : Blo 702318 704151 := bstep (se 1 (by rfl) ⟨528113, by rfl⟩ : syracuseStep 704151 = 1056227) B1056227
theorem B704171 : Blo 702318 704171 := bstep (se 1 (by rfl) ⟨528128, by rfl⟩ : syracuseStep 704171 = 1056257) B1056257
theorem B1785523 : Blo 702318 1785523 := bstep (se 1 (by rfl) ⟨1339142, by rfl⟩ : syracuseStep 1785523 = 2678285) B2678285
theorem B704183 : Blo 702318 704183 := bstep (se 1 (by rfl) ⟨528137, by rfl⟩ : syracuseStep 704183 = 1056275) B1056275
theorem B704203 : Blo 702318 704203 := bstep (se 1 (by rfl) ⟨528152, by rfl⟩ : syracuseStep 704203 = 1056305) B1056305
theorem B704215 : Blo 702318 704215 := bstep (se 1 (by rfl) ⟨528161, by rfl⟩ : syracuseStep 704215 = 1056323) B1056323
theorem B704235 : Blo 702318 704235 := bstep (se 1 (by rfl) ⟨528176, by rfl⟩ : syracuseStep 704235 = 1056353) B1056353
theorem B704247 : Blo 702318 704247 := bstep (se 1 (by rfl) ⟨528185, by rfl⟩ : syracuseStep 704247 = 1056371) B1056371
theorem B704267 : Blo 702318 704267 := bstep (se 1 (by rfl) ⟨528200, by rfl⟩ : syracuseStep 704267 = 1056401) B1056401
theorem B1589003 : Blo 702318 1589003 := bstep (se 1 (by rfl) ⟨1191752, by rfl⟩ : syracuseStep 1589003 = 2383505) B2383505
theorem B704279 : Blo 702318 704279 := bstep (se 1 (by rfl) ⟨528209, by rfl⟩ : syracuseStep 704279 = 1056419) B1056419
theorem B704299 : Blo 702318 704299 := bstep (se 1 (by rfl) ⟨528224, by rfl⟩ : syracuseStep 704299 = 1056449) B1056449
theorem B704311 : Blo 702318 704311 := bstep (se 1 (by rfl) ⟨528233, by rfl⟩ : syracuseStep 704311 = 1056467) B1056467
theorem B1785665 : Blo 702318 1785665 := bstep (se 2 (by rfl) ⟨669624, by rfl⟩ : syracuseStep 1785665 = 1339249) B1339249
theorem B1589057 : Blo 702318 1589057 := bstep (se 2 (by rfl) ⟨595896, by rfl⟩ : syracuseStep 1589057 = 1191793) B1191793
theorem B704331 : Blo 702318 704331 := bstep (se 1 (by rfl) ⟨528248, by rfl⟩ : syracuseStep 704331 = 1056497) B1056497
theorem B704343 : Blo 702318 704343 := bstep (se 1 (by rfl) ⟨528257, by rfl⟩ : syracuseStep 704343 = 1056515) B1056515
theorem B2375513 : Blo 702318 2375513 := bstep (se 2 (by rfl) ⟨890817, by rfl⟩ : syracuseStep 2375513 = 1781635) B1781635
theorem B704363 : Blo 702318 704363 := bstep (se 1 (by rfl) ⟨528272, by rfl⟩ : syracuseStep 704363 = 1056545) B1056545
theorem B704375 : Blo 702318 704375 := bstep (se 1 (by rfl) ⟨528281, by rfl⟩ : syracuseStep 704375 = 1056563) B1056563
theorem B704395 : Blo 702318 704395 := bstep (se 1 (by rfl) ⟨528296, by rfl⟩ : syracuseStep 704395 = 1056593) B1056593
theorem B704407 : Blo 702318 704407 := bstep (se 1 (by rfl) ⟨528305, by rfl⟩ : syracuseStep 704407 = 1056611) B1056611
theorem B704427 : Blo 702318 704427 := bstep (se 1 (by rfl) ⟨528320, by rfl⟩ : syracuseStep 704427 = 1056641) B1056641
theorem B2670509 : Blo 702318 2670509 := bstep (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) B1001441
theorem B704439 : Blo 702318 704439 := bstep (se 1 (by rfl) ⟨528329, by rfl⟩ : syracuseStep 704439 = 1056659) B1056659
theorem B704459 : Blo 702318 704459 := bstep (se 1 (by rfl) ⟨528344, by rfl⟩ : syracuseStep 704459 = 1056689) B1056689
theorem B704471 : Blo 702318 704471 := bstep (se 1 (by rfl) ⟨528353, by rfl⟩ : syracuseStep 704471 = 1056707) B1056707
theorem B2146265 : Blo 702318 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B704491 : Blo 702318 704491 := bstep (se 1 (by rfl) ⟨528368, by rfl⟩ : syracuseStep 704491 = 1056737) B1056737
theorem B704503 : Blo 702318 704503 := bstep (se 1 (by rfl) ⟨528377, by rfl⟩ : syracuseStep 704503 = 1056755) B1056755
theorem B704523 : Blo 702318 704523 := bstep (se 1 (by rfl) ⟨528392, by rfl⟩ : syracuseStep 704523 = 1056785) B1056785
theorem B704535 : Blo 702318 704535 := bstep (se 1 (by rfl) ⟨528401, by rfl⟩ : syracuseStep 704535 = 1056803) B1056803
theorem B704555 : Blo 702318 704555 := bstep (se 1 (by rfl) ⟨528416, by rfl⟩ : syracuseStep 704555 = 1056833) B1056833
theorem B704567 : Blo 702318 704567 := bstep (se 1 (by rfl) ⟨528425, by rfl⟩ : syracuseStep 704567 = 1056851) B1056851
theorem B4505665 : Blo 702318 4505665 := bstep (se 2 (by rfl) ⟨1689624, by rfl⟩ : syracuseStep 4505665 = 3379249) B3379249
theorem B704587 : Blo 702318 704587 := bstep (se 1 (by rfl) ⟨528440, by rfl⟩ : syracuseStep 704587 = 1056881) B1056881
theorem B704599 : Blo 702318 704599 := bstep (se 1 (by rfl) ⟨528449, by rfl⟩ : syracuseStep 704599 = 1056899) B1056899
theorem B704619 : Blo 702318 704619 := bstep (se 1 (by rfl) ⟨528464, by rfl⟩ : syracuseStep 704619 = 1056929) B1056929
theorem B704631 : Blo 702318 704631 := bstep (se 1 (by rfl) ⟨528473, by rfl⟩ : syracuseStep 704631 = 1056947) B1056947
theorem B704651 : Blo 702318 704651 := bstep (se 1 (by rfl) ⟨528488, by rfl⟩ : syracuseStep 704651 = 1056977) B1056977
theorem B704663 : Blo 702318 704663 := bstep (se 1 (by rfl) ⟨528497, by rfl⟩ : syracuseStep 704663 = 1056995) B1056995
theorem B704683 : Blo 702318 704683 := bstep (se 1 (by rfl) ⟨528512, by rfl⟩ : syracuseStep 704683 = 1057025) B1057025
theorem B704695 : Blo 702318 704695 := bstep (se 1 (by rfl) ⟨528521, by rfl⟩ : syracuseStep 704695 = 1057043) B1057043
theorem B704715 : Blo 702318 704715 := bstep (se 1 (by rfl) ⟨528536, by rfl⟩ : syracuseStep 704715 = 1057073) B1057073
theorem B704727 : Blo 702318 704727 := bstep (se 1 (by rfl) ⟨528545, by rfl⟩ : syracuseStep 704727 = 1057091) B1057091
theorem B704747 : Blo 702318 704747 := bstep (se 1 (by rfl) ⟨528560, by rfl⟩ : syracuseStep 704747 = 1057121) B1057121
theorem B704759 : Blo 702318 704759 := bstep (se 1 (by rfl) ⟨528569, by rfl⟩ : syracuseStep 704759 = 1057139) B1057139
theorem B704779 : Blo 702318 704779 := bstep (se 1 (by rfl) ⟨528584, by rfl⟩ : syracuseStep 704779 = 1057169) B1057169
theorem B704791 : Blo 702318 704791 := bstep (se 1 (by rfl) ⟨528593, by rfl⟩ : syracuseStep 704791 = 1057187) B1057187
theorem B704811 : Blo 702318 704811 := bstep (se 1 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 704811 = 1057217) B1057217
theorem B704823 : Blo 702318 704823 := bstep (se 1 (by rfl) ⟨528617, by rfl⟩ : syracuseStep 704823 = 1057235) B1057235
theorem B704843 : Blo 702318 704843 := bstep (se 1 (by rfl) ⟨528632, by rfl⟩ : syracuseStep 704843 = 1057265) B1057265
theorem B704855 : Blo 702318 704855 := bstep (se 1 (by rfl) ⟨528641, by rfl⟩ : syracuseStep 704855 = 1057283) B1057283
theorem B704875 : Blo 702318 704875 := bstep (se 1 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 704875 = 1057313) B1057313
theorem B704887 : Blo 702318 704887 := bstep (se 1 (by rfl) ⟨528665, by rfl⟩ : syracuseStep 704887 = 1057331) B1057331
theorem B4014467 : Blo 702318 4014467 := bstep (se 1 (by rfl) ⟨3010850, by rfl⟩ : syracuseStep 4014467 = 6021701) B6021701
theorem B704907 : Blo 702318 704907 := bstep (se 1 (by rfl) ⟨528680, by rfl⟩ : syracuseStep 704907 = 1057361) B1057361
theorem B704919 : Blo 702318 704919 := bstep (se 1 (by rfl) ⟨528689, by rfl⟩ : syracuseStep 704919 = 1057379) B1057379
theorem B704939 : Blo 702318 704939 := bstep (se 1 (by rfl) ⟨528704, by rfl⟩ : syracuseStep 704939 = 1057409) B1057409
theorem B704951 : Blo 702318 704951 := bstep (se 1 (by rfl) ⟨528713, by rfl⟩ : syracuseStep 704951 = 1057427) B1057427
theorem B704971 : Blo 702318 704971 := bstep (se 1 (by rfl) ⟨528728, by rfl⟩ : syracuseStep 704971 = 1057457) B1057457
theorem B704983 : Blo 702318 704983 := bstep (se 1 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 704983 = 1057475) B1057475
theorem B705003 : Blo 702318 705003 := bstep (se 1 (by rfl) ⟨528752, by rfl⟩ : syracuseStep 705003 = 1057505) B1057505
theorem B705015 : Blo 702318 705015 := bstep (se 1 (by rfl) ⟨528761, by rfl⟩ : syracuseStep 705015 = 1057523) B1057523
theorem B705035 : Blo 702318 705035 := bstep (se 1 (by rfl) ⟨528776, by rfl⟩ : syracuseStep 705035 = 1057553) B1057553
theorem B1688087 : Blo 702318 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B2376215 : Blo 702318 2376215 := bstep (se 1 (by rfl) ⟨1782161, by rfl⟩ : syracuseStep 2376215 = 3564323) B3564323
theorem B705047 : Blo 702318 705047 := bstep (se 1 (by rfl) ⟨528785, by rfl⟩ : syracuseStep 705047 = 1057571) B1057571
theorem B705067 : Blo 702318 705067 := bstep (se 1 (by rfl) ⟨528800, by rfl⟩ : syracuseStep 705067 = 1057601) B1057601
theorem B705079 : Blo 702318 705079 := bstep (se 1 (by rfl) ⟨528809, by rfl⟩ : syracuseStep 705079 = 1057619) B1057619
theorem B705099 : Blo 702318 705099 := bstep (se 1 (by rfl) ⟨528824, by rfl⟩ : syracuseStep 705099 = 1057649) B1057649
theorem B705111 : Blo 702318 705111 := bstep (se 1 (by rfl) ⟨528833, by rfl⟩ : syracuseStep 705111 = 1057667) B1057667
theorem B705131 : Blo 702318 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B705143 : Blo 702318 705143 := bstep (se 1 (by rfl) ⟨528857, by rfl⟩ : syracuseStep 705143 = 1057715) B1057715
theorem B705163 : Blo 702318 705163 := bstep (se 1 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 705163 = 1057745) B1057745
theorem B705175 : Blo 702318 705175 := bstep (se 1 (by rfl) ⟨528881, by rfl⟩ : syracuseStep 705175 = 1057763) B1057763
theorem B705195 : Blo 702318 705195 := bstep (se 1 (by rfl) ⟨528896, by rfl⟩ : syracuseStep 705195 = 1057793) B1057793
theorem B705207 : Blo 702318 705207 := bstep (se 1 (by rfl) ⟨528905, by rfl⟩ : syracuseStep 705207 = 1057811) B1057811
theorem B705227 : Blo 702318 705227 := bstep (se 1 (by rfl) ⟨528920, by rfl⟩ : syracuseStep 705227 = 1057841) B1057841
theorem B705239 : Blo 702318 705239 := bstep (se 1 (by rfl) ⟨528929, by rfl⟩ : syracuseStep 705239 = 1057859) B1057859
theorem B705259 : Blo 702318 705259 := bstep (se 1 (by rfl) ⟨528944, by rfl⟩ : syracuseStep 705259 = 1057889) B1057889
theorem B705271 : Blo 702318 705271 := bstep (se 1 (by rfl) ⟨528953, by rfl⟩ : syracuseStep 705271 = 1057907) B1057907
theorem B705291 : Blo 702318 705291 := bstep (se 1 (by rfl) ⟨528968, by rfl⟩ : syracuseStep 705291 = 1057937) B1057937
theorem B705303 : Blo 702318 705303 := bstep (se 1 (by rfl) ⟨528977, by rfl⟩ : syracuseStep 705303 = 1057955) B1057955
theorem B705323 : Blo 702318 705323 := bstep (se 1 (by rfl) ⟨528992, by rfl⟩ : syracuseStep 705323 = 1057985) B1057985
theorem B705335 : Blo 702318 705335 := bstep (se 1 (by rfl) ⟨529001, by rfl⟩ : syracuseStep 705335 = 1058003) B1058003
theorem B705355 : Blo 702318 705355 := bstep (se 1 (by rfl) ⟨529016, by rfl⟩ : syracuseStep 705355 = 1058033) B1058033
theorem B1000279 : Blo 702318 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B705367 : Blo 702318 705367 := bstep (se 1 (by rfl) ⟨529025, by rfl⟩ : syracuseStep 705367 = 1058051) B1058051
theorem B705387 : Blo 702318 705387 := bstep (se 1 (by rfl) ⟨529040, by rfl⟩ : syracuseStep 705387 = 1058081) B1058081
theorem B705399 : Blo 702318 705399 := bstep (se 1 (by rfl) ⟨529049, by rfl⟩ : syracuseStep 705399 = 1058099) B1058099
theorem B705419 : Blo 702318 705419 := bstep (se 1 (by rfl) ⟨529064, by rfl⟩ : syracuseStep 705419 = 1058129) B1058129
theorem B705431 : Blo 702318 705431 := bstep (se 1 (by rfl) ⟨529073, by rfl⟩ : syracuseStep 705431 = 1058147) B1058147
theorem B705451 : Blo 702318 705451 := bstep (se 1 (by rfl) ⟨529088, by rfl⟩ : syracuseStep 705451 = 1058177) B1058177
theorem B705463 : Blo 702318 705463 := bstep (se 1 (by rfl) ⟨529097, by rfl⟩ : syracuseStep 705463 = 1058195) B1058195
theorem B705483 : Blo 702318 705483 := bstep (se 1 (by rfl) ⟨529112, by rfl⟩ : syracuseStep 705483 = 1058225) B1058225
theorem B705495 : Blo 702318 705495 := bstep (se 1 (by rfl) ⟨529121, by rfl⟩ : syracuseStep 705495 = 1058243) B1058243
theorem B705515 : Blo 702318 705515 := bstep (se 1 (by rfl) ⟨529136, by rfl⟩ : syracuseStep 705515 = 1058273) B1058273
theorem B705527 : Blo 702318 705527 := bstep (se 1 (by rfl) ⟨529145, by rfl⟩ : syracuseStep 705527 = 1058291) B1058291
theorem B705547 : Blo 702318 705547 := bstep (se 1 (by rfl) ⟨529160, by rfl⟩ : syracuseStep 705547 = 1058321) B1058321
theorem B6177809 : Blo 702318 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B705559 : Blo 702318 705559 := bstep (se 1 (by rfl) ⟨529169, by rfl⟩ : syracuseStep 705559 = 1058339) B1058339
theorem B705579 : Blo 702318 705579 := bstep (se 1 (by rfl) ⟨529184, by rfl⟩ : syracuseStep 705579 = 1058369) B1058369
theorem B2376755 : Blo 702318 2376755 := bstep (se 1 (by rfl) ⟨1782566, by rfl⟩ : syracuseStep 2376755 = 3565133) B3565133
theorem B1786931 : Blo 702318 1786931 := bstep (se 1 (by rfl) ⟨1340198, by rfl⟩ : syracuseStep 1786931 = 2680397) B2680397
theorem B705591 : Blo 702318 705591 := bstep (se 1 (by rfl) ⟨529193, by rfl⟩ : syracuseStep 705591 = 1058387) B1058387
theorem B705611 : Blo 702318 705611 := bstep (se 1 (by rfl) ⟨529208, by rfl⟩ : syracuseStep 705611 = 1058417) B1058417
theorem B705623 : Blo 702318 705623 := bstep (se 1 (by rfl) ⟨529217, by rfl⟩ : syracuseStep 705623 = 1058435) B1058435
theorem B705643 : Blo 702318 705643 := bstep (se 1 (by rfl) ⟨529232, by rfl⟩ : syracuseStep 705643 = 1058465) B1058465
theorem B705655 : Blo 702318 705655 := bstep (se 1 (by rfl) ⟨529241, by rfl⟩ : syracuseStep 705655 = 1058483) B1058483
theorem B705675 : Blo 702318 705675 := bstep (se 1 (by rfl) ⟨529256, by rfl⟩ : syracuseStep 705675 = 1058513) B1058513
theorem B2704535 : Blo 702318 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B705687 : Blo 702318 705687 := bstep (se 1 (by rfl) ⟨529265, by rfl⟩ : syracuseStep 705687 = 1058531) B1058531
theorem B705707 : Blo 702318 705707 := bstep (se 1 (by rfl) ⟨529280, by rfl⟩ : syracuseStep 705707 = 1058561) B1058561
theorem B705719 : Blo 702318 705719 := bstep (se 1 (by rfl) ⟨529289, by rfl⟩ : syracuseStep 705719 = 1058579) B1058579
theorem B705739 : Blo 702318 705739 := bstep (se 1 (by rfl) ⟨529304, by rfl⟩ : syracuseStep 705739 = 1058609) B1058609
theorem B705751 : Blo 702318 705751 := bstep (se 1 (by rfl) ⟨529313, by rfl⟩ : syracuseStep 705751 = 1058627) B1058627
theorem B705771 : Blo 702318 705771 := bstep (se 1 (by rfl) ⟨529328, by rfl⟩ : syracuseStep 705771 = 1058657) B1058657
theorem B705783 : Blo 702318 705783 := bstep (se 1 (by rfl) ⟨529337, by rfl⟩ : syracuseStep 705783 = 1058675) B1058675
theorem B705803 : Blo 702318 705803 := bstep (se 1 (by rfl) ⟨529352, by rfl⟩ : syracuseStep 705803 = 1058705) B1058705
theorem B705815 : Blo 702318 705815 := bstep (se 1 (by rfl) ⟨529361, by rfl⟩ : syracuseStep 705815 = 1058723) B1058723
theorem B705835 : Blo 702318 705835 := bstep (se 1 (by rfl) ⟨529376, by rfl⟩ : syracuseStep 705835 = 1058753) B1058753
theorem B705847 : Blo 702318 705847 := bstep (se 1 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 705847 = 1058771) B1058771
theorem B2671937 : Blo 702318 2671937 := bstep (se 2 (by rfl) ⟨1001976, by rfl⟩ : syracuseStep 2671937 = 2003953) B2003953
theorem B2377025 : Blo 702318 2377025 := bstep (se 2 (by rfl) ⟨891384, by rfl⟩ : syracuseStep 2377025 = 1782769) B1782769
theorem B705867 : Blo 702318 705867 := bstep (se 1 (by rfl) ⟨529400, by rfl⟩ : syracuseStep 705867 = 1058801) B1058801
theorem B705879 : Blo 702318 705879 := bstep (se 1 (by rfl) ⟨529409, by rfl⟩ : syracuseStep 705879 = 1058819) B1058819
theorem B705899 : Blo 702318 705899 := bstep (se 1 (by rfl) ⟨529424, by rfl⟩ : syracuseStep 705899 = 1058849) B1058849
theorem B705911 : Blo 702318 705911 := bstep (se 1 (by rfl) ⟨529433, by rfl⟩ : syracuseStep 705911 = 1058867) B1058867
theorem B705931 : Blo 702318 705931 := bstep (se 1 (by rfl) ⟨529448, by rfl⟩ : syracuseStep 705931 = 1058897) B1058897
theorem B705943 : Blo 702318 705943 := bstep (se 1 (by rfl) ⟨529457, by rfl⟩ : syracuseStep 705943 = 1058915) B1058915
theorem B705963 : Blo 702318 705963 := bstep (se 1 (by rfl) ⟨529472, by rfl⟩ : syracuseStep 705963 = 1058945) B1058945
theorem B705975 : Blo 702318 705975 := bstep (se 1 (by rfl) ⟨529481, by rfl⟩ : syracuseStep 705975 = 1058963) B1058963
theorem B705995 : Blo 702318 705995 := bstep (se 1 (by rfl) ⟨529496, by rfl⟩ : syracuseStep 705995 = 1058993) B1058993
theorem B706007 : Blo 702318 706007 := bstep (se 1 (by rfl) ⟨529505, by rfl⟩ : syracuseStep 706007 = 1059011) B1059011
theorem B706027 : Blo 702318 706027 := bstep (se 1 (by rfl) ⟨529520, by rfl⟩ : syracuseStep 706027 = 1059041) B1059041
theorem B706039 : Blo 702318 706039 := bstep (se 1 (by rfl) ⟨529529, by rfl⟩ : syracuseStep 706039 = 1059059) B1059059
theorem B706059 : Blo 702318 706059 := bstep (se 1 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 706059 = 1059089) B1059089
theorem B5359121 : Blo 702318 5359121 := bstep (se 2 (by rfl) ⟨2009670, by rfl⟩ : syracuseStep 5359121 = 4019341) B4019341
theorem B706071 : Blo 702318 706071 := bstep (se 1 (by rfl) ⟨529553, by rfl⟩ : syracuseStep 706071 = 1059107) B1059107
theorem B706091 : Blo 702318 706091 := bstep (se 1 (by rfl) ⟨529568, by rfl⟩ : syracuseStep 706091 = 1059137) B1059137
theorem B2573869 : Blo 702318 2573869 := bstep (se 3 (by rfl) ⟨482600, by rfl⟩ : syracuseStep 2573869 = 965201) B965201
theorem B706103 : Blo 702318 706103 := bstep (se 1 (by rfl) ⟨529577, by rfl⟩ : syracuseStep 706103 = 1059155) B1059155
theorem B706123 : Blo 702318 706123 := bstep (se 1 (by rfl) ⟨529592, by rfl⟩ : syracuseStep 706123 = 1059185) B1059185
theorem B1787467 : Blo 702318 1787467 := bstep (se 1 (by rfl) ⟨1340600, by rfl⟩ : syracuseStep 1787467 = 2681201) B2681201
theorem B706135 : Blo 702318 706135 := bstep (se 1 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 706135 = 1059203) B1059203
theorem B706155 : Blo 702318 706155 := bstep (se 1 (by rfl) ⟨529616, by rfl⟩ : syracuseStep 706155 = 1059233) B1059233
theorem B706167 : Blo 702318 706167 := bstep (se 1 (by rfl) ⟨529625, by rfl⟩ : syracuseStep 706167 = 1059251) B1059251
theorem B706187 : Blo 702318 706187 := bstep (se 1 (by rfl) ⟨529640, by rfl⟩ : syracuseStep 706187 = 1059281) B1059281
theorem B706199 : Blo 702318 706199 := bstep (se 1 (by rfl) ⟨529649, by rfl⟩ : syracuseStep 706199 = 1059299) B1059299
theorem B706219 : Blo 702318 706219 := bstep (se 1 (by rfl) ⟨529664, by rfl⟩ : syracuseStep 706219 = 1059329) B1059329
theorem B706231 : Blo 702318 706231 := bstep (se 1 (by rfl) ⟨529673, by rfl⟩ : syracuseStep 706231 = 1059347) B1059347
theorem B706251 : Blo 702318 706251 := bstep (se 1 (by rfl) ⟨529688, by rfl⟩ : syracuseStep 706251 = 1059377) B1059377
theorem B706263 : Blo 702318 706263 := bstep (se 1 (by rfl) ⟨529697, by rfl⟩ : syracuseStep 706263 = 1059395) B1059395
theorem B1787609 : Blo 702318 1787609 := bstep (se 2 (by rfl) ⟨670353, by rfl⟩ : syracuseStep 1787609 = 1340707) B1340707
theorem B706283 : Blo 702318 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B706295 : Blo 702318 706295 := bstep (se 1 (by rfl) ⟨529721, by rfl⟩ : syracuseStep 706295 = 1059443) B1059443
theorem B706315 : Blo 702318 706315 := bstep (se 1 (by rfl) ⟨529736, by rfl⟩ : syracuseStep 706315 = 1059473) B1059473
theorem B20531009 : Blo 702318 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B3557195 : Blo 702318 3557195 := bstep (se 1 (by rfl) ⟨2667896, by rfl⟩ : syracuseStep 3557195 = 5335793) B5335793
theorem B2377565 : Blo 702318 2377565 := bstep (se 3 (by rfl) ⟨445793, by rfl⟩ : syracuseStep 2377565 = 891587) B891587
theorem B20301785 : Blo 702318 20301785 := bstep (se 2 (by rfl) ⟨7613169, by rfl⟩ : syracuseStep 20301785 = 15226339) B15226339
theorem B1689817 : Blo 702318 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B2541875 : Blo 702318 2541875 := bstep (se 1 (by rfl) ⟨1906406, by rfl⟩ : syracuseStep 2541875 = 3812813) B3812813
theorem B2542211 : Blo 702318 2542211 := bstep (se 1 (by rfl) ⟨1906658, by rfl⟩ : syracuseStep 2542211 = 3813317) B3813317
theorem B1428119 : Blo 702318 1428119 := bstep (se 1 (by rfl) ⟨1071089, by rfl⟩ : syracuseStep 1428119 = 2142179) B2142179
theorem B6408881 : Blo 702318 6408881 := bstep (se 2 (by rfl) ⟨2403330, by rfl⟩ : syracuseStep 6408881 = 4806661) B4806661
theorem B2673425 : Blo 702318 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B1690433 : Blo 702318 1690433 := bstep (se 2 (by rfl) ⟨633912, by rfl⟩ : syracuseStep 1690433 = 1267825) B1267825
theorem B2378699 : Blo 702318 2378699 := bstep (se 1 (by rfl) ⟨1784024, by rfl⟩ : syracuseStep 2378699 = 3568049) B3568049
theorem B8342621 : Blo 702318 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B2673881 : Blo 702318 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B2378969 : Blo 702318 2378969 := bstep (se 2 (by rfl) ⟨892113, by rfl⟩ : syracuseStep 2378969 = 1784227) B1784227
theorem B3624209 : Blo 702318 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B1428761 : Blo 702318 1428761 := bstep (se 2 (by rfl) ⟨535785, by rfl⟩ : syracuseStep 1428761 = 1071571) B1071571
theorem B6016301 : Blo 702318 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B5131613 : Blo 702318 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B9031013 : Blo 702318 9031013 := bstep (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) B1693315
theorem B2674093 : Blo 702318 2674093 := bstep (se 3 (by rfl) ⟨501392, by rfl⟩ : syracuseStep 2674093 = 1002785) B1002785
theorem B4509229 : Blo 702318 4509229 := bstep (se 3 (by rfl) ⟨845480, by rfl⟩ : syracuseStep 4509229 = 1690961) B1690961
theorem B3558977 : Blo 702318 3558977 := bstep (se 2 (by rfl) ⟨1334616, by rfl⟩ : syracuseStep 3558977 = 2669233) B2669233
theorem B1691201 : Blo 702318 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B3001931 : Blo 702318 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B2674397 : Blo 702318 2674397 := bstep (se 3 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 2674397 = 1002899) B1002899
theorem B2543363 : Blo 702318 2543363 := bstep (se 1 (by rfl) ⟨1907522, by rfl⟩ : syracuseStep 2543363 = 3815045) B3815045
theorem B2379671 : Blo 702318 2379671 := bstep (se 1 (by rfl) ⟨1784753, by rfl⟩ : syracuseStep 2379671 = 3569507) B3569507
theorem B1003799 : Blo 702318 1003799 := bstep (se 1 (by rfl) ⟨752849, by rfl⟩ : syracuseStep 1003799 = 1505699) B1505699
theorem B1069399 : Blo 702318 1069399 := bstep (se 1 (by rfl) ⟨802049, by rfl⟩ : syracuseStep 1069399 = 1604099) B1604099
theorem B2380211 : Blo 702318 2380211 := bstep (se 1 (by rfl) ⟨1785158, by rfl⟩ : syracuseStep 2380211 = 3570317) B3570317
theorem B1430131 : Blo 702318 1430131 := bstep (se 1 (by rfl) ⟨1072598, by rfl⟩ : syracuseStep 1430131 = 2145197) B2145197
theorem B2380481 : Blo 702318 2380481 := bstep (se 2 (by rfl) ⟨892680, by rfl⟩ : syracuseStep 2380481 = 1785361) B1785361
theorem B3134173 : Blo 702318 3134173 := bstep (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) B1175315
theorem B2544473 : Blo 702318 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B2544529 : Blo 702318 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B2544587 : Blo 702318 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B2544643 : Blo 702318 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B5067953 : Blo 702318 5067953 := bstep (se 2 (by rfl) ⟨1900482, by rfl⟩ : syracuseStep 5067953 = 3800965) B3800965
theorem B3003571 : Blo 702318 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B2381021 : Blo 702318 2381021 := bstep (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) B892883
theorem B5363009 : Blo 702318 5363009 := bstep (se 2 (by rfl) ⟨2011128, by rfl⟩ : syracuseStep 5363009 = 4022257) B4022257
theorem B3560921 : Blo 702318 3560921 := bstep (se 2 (by rfl) ⟨1335345, by rfl⟩ : syracuseStep 3560921 = 2670691) B2670691
theorem B10180417 : Blo 702318 10180417 := bstep (se 2 (by rfl) ⟨3817656, by rfl⟩ : syracuseStep 10180417 = 7635313) B7635313
theorem B2414539 : Blo 702318 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B2709469 : Blo 702318 2709469 := bstep (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) B1016051
theorem B4773953 : Blo 702318 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B4020299 : Blo 702318 4020299 := bstep (se 1 (by rfl) ⟨3015224, by rfl⟩ : syracuseStep 4020299 = 6030449) B6030449
theorem B2676995 : Blo 702318 2676995 := bstep (se 1 (by rfl) ⟨2007746, by rfl⟩ : syracuseStep 2676995 = 4015493) B4015493
theorem B2677009 : Blo 702318 2677009 := bstep (se 2 (by rfl) ⟨1003878, by rfl⟩ : syracuseStep 2677009 = 2007757) B2007757
theorem B1267991 : Blo 702318 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B2382155 : Blo 702318 2382155 := bstep (se 1 (by rfl) ⟨1786616, by rfl⟩ : syracuseStep 2382155 = 3573233) B3573233
theorem B1333721 : Blo 702318 1333721 := bstep (se 2 (by rfl) ⟨500145, by rfl⟩ : syracuseStep 1333721 = 1000291) B1000291
theorem B2677313 : Blo 702318 2677313 := bstep (se 2 (by rfl) ⟨1003992, by rfl⟩ : syracuseStep 2677313 = 2007985) B2007985
theorem B2382425 : Blo 702318 2382425 := bstep (se 2 (by rfl) ⟨893409, by rfl⟩ : syracuseStep 2382425 = 1786819) B1786819
theorem B3005059 : Blo 702318 3005059 := bstep (se 1 (by rfl) ⟨2253794, by rfl⟩ : syracuseStep 3005059 = 4507589) B4507589
theorem B32889653 : Blo 702318 32889653 := bstep (se 5 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 32889653 = 3083405) B3083405
theorem B6019991 : Blo 702318 6019991 := bstep (se 1 (by rfl) ⟨4514993, by rfl⟩ : syracuseStep 6019991 = 9029987) B9029987
theorem B3562541 : Blo 702318 3562541 := bstep (se 3 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 3562541 = 1335953) B1335953
theorem B1334465 : Blo 702318 1334465 := bstep (se 2 (by rfl) ⟨500424, by rfl⟩ : syracuseStep 1334465 = 1000849) B1000849
theorem B7625933 : Blo 702318 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B3005657 : Blo 702318 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B2677981 : Blo 702318 2677981 := bstep (se 3 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 2677981 = 1004243) B1004243
theorem B2383127 : Blo 702318 2383127 := bstep (se 1 (by rfl) ⟨1787345, by rfl⟩ : syracuseStep 2383127 = 3574691) B3574691
theorem B7232813 : Blo 702318 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B1203607 : Blo 702318 1203607 := bstep (se 1 (by rfl) ⟨902705, by rfl⟩ : syracuseStep 1203607 = 1805411) B1805411
theorem B1334731 : Blo 702318 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B1269209 : Blo 702318 1269209 := bstep (se 2 (by rfl) ⟨475953, by rfl⟩ : syracuseStep 1269209 = 951907) B951907
theorem B3006017 : Blo 702318 3006017 := bstep (se 2 (by rfl) ⟨1127256, by rfl⟩ : syracuseStep 3006017 = 2254513) B2254513
theorem B1072855 : Blo 702318 1072855 := bstep (se 1 (by rfl) ⟨804641, by rfl⟩ : syracuseStep 1072855 = 1609283) B1609283
theorem B1695449 : Blo 702318 1695449 := bstep (se 2 (by rfl) ⟨635793, by rfl⟩ : syracuseStep 1695449 = 1271587) B1271587
theorem B2383667 : Blo 702318 2383667 := bstep (se 1 (by rfl) ⟨1787750, by rfl⟩ : syracuseStep 2383667 = 3575501) B3575501
theorem B712535 : Blo 702318 712535 := bstep (se 1 (by rfl) ⟨534401, by rfl⟩ : syracuseStep 712535 = 1068803) B1068803
theorem B1335179 : Blo 702318 1335179 := bstep (se 1 (by rfl) ⟨1001384, by rfl⟩ : syracuseStep 1335179 = 2002769) B2002769
theorem B1204183 : Blo 702318 1204183 := bstep (se 1 (by rfl) ⟨903137, by rfl⟩ : syracuseStep 1204183 = 1806275) B1806275
theorem B1269785 : Blo 702318 1269785 := bstep (se 2 (by rfl) ⟨476169, by rfl⟩ : syracuseStep 1269785 = 952339) B952339
theorem B1335361 : Blo 702318 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B24371381 : Blo 702318 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B4579715 : Blo 702318 4579715 := bstep (se 1 (by rfl) ⟨3434786, by rfl⟩ : syracuseStep 4579715 = 6869573) B6869573
theorem B1335703 : Blo 702318 1335703 := bstep (se 1 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 1335703 = 2003555) B2003555
theorem B2679257 : Blo 702318 2679257 := bstep (se 2 (by rfl) ⟨1004721, by rfl⟩ : syracuseStep 2679257 = 2009443) B2009443
theorem B1270361 : Blo 702318 1270361 := bstep (se 2 (by rfl) ⟨476385, by rfl⟩ : syracuseStep 1270361 = 952771) B952771
theorem B1335923 : Blo 702318 1335923 := bstep (se 1 (by rfl) ⟨1001942, by rfl⟩ : syracuseStep 1335923 = 2003885) B2003885
theorem B1172183 : Blo 702318 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1336151 : Blo 702318 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B811883 : Blo 702318 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B1336409 : Blo 702318 1336409 := bstep (se 2 (by rfl) ⟨501153, by rfl⟩ : syracuseStep 1336409 = 1002307) B1002307
theorem B1500275 : Blo 702318 1500275 := bstep (se 1 (by rfl) ⟨1125206, by rfl⟩ : syracuseStep 1500275 = 2250413) B2250413
theorem B5727523 : Blo 702318 5727523 := bstep (se 1 (by rfl) ⟨4295642, by rfl⟩ : syracuseStep 5727523 = 8591285) B8591285
theorem B1336819 : Blo 702318 1336819 := bstep (se 1 (by rfl) ⟨1002614, by rfl⟩ : syracuseStep 1336819 = 2005229) B2005229
theorem B1271371 : Blo 702318 1271371 := bstep (se 1 (by rfl) ⟨953528, by rfl⟩ : syracuseStep 1271371 = 1907057) B1907057
theorem B1500761 : Blo 702318 1500761 := bstep (se 2 (by rfl) ⟨562785, by rfl⟩ : syracuseStep 1500761 = 1125571) B1125571
theorem B1337305 : Blo 702318 1337305 := bstep (se 2 (by rfl) ⟨501489, by rfl⟩ : syracuseStep 1337305 = 1002979) B1002979
theorem B2680883 : Blo 702318 2680883 := bstep (se 1 (by rfl) ⟨2010662, by rfl⟩ : syracuseStep 2680883 = 4021325) B4021325
theorem B2680897 : Blo 702318 2680897 := bstep (se 2 (by rfl) ⟨1005336, by rfl⟩ : syracuseStep 2680897 = 2010673) B2010673
theorem B2058329 : Blo 702318 2058329 := bstep (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) B1543747
theorem B4516019 : Blo 702318 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B1337867 : Blo 702318 1337867 := bstep (se 1 (by rfl) ⟨1003400, by rfl⟩ : syracuseStep 1337867 = 2006801) B2006801
theorem B2255435 : Blo 702318 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B1338049 : Blo 702318 1338049 := bstep (se 2 (by rfl) ⟨501768, by rfl⟩ : syracuseStep 1338049 = 1003537) B1003537
theorem B3566429 : Blo 702318 3566429 := bstep (se 3 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 3566429 = 1337411) B1337411
theorem B1272755 : Blo 702318 1272755 := bstep (se 1 (by rfl) ⟨954566, by rfl⟩ : syracuseStep 1272755 = 1909133) B1909133
theorem B2714797 : Blo 702318 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B1502401 : Blo 702318 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B3009757 : Blo 702318 3009757 := bstep (se 3 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 3009757 = 1128659) B1128659
theorem B1338763 : Blo 702318 1338763 := bstep (se 1 (by rfl) ⟨1004072, by rfl⟩ : syracuseStep 1338763 = 2008145) B2008145
theorem B1338839 : Blo 702318 1338839 := bstep (se 1 (by rfl) ⟨1004129, by rfl⟩ : syracuseStep 1338839 = 2008259) B2008259
theorem B1339507 : Blo 702318 1339507 := bstep (se 1 (by rfl) ⟨1004630, by rfl⟩ : syracuseStep 1339507 = 2009261) B2009261
theorem B4944023 : Blo 702318 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B2257075 : Blo 702318 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B2257217 : Blo 702318 2257217 := bstep (se 2 (by rfl) ⟨846456, by rfl⟩ : syracuseStep 2257217 = 1692913) B1692913
theorem B1339735 : Blo 702318 1339735 := bstep (se 1 (by rfl) ⟨1004801, by rfl⟩ : syracuseStep 1339735 = 2009603) B2009603
theorem B1339841 : Blo 702318 1339841 := bstep (se 2 (by rfl) ⟨502440, by rfl⟩ : syracuseStep 1339841 = 1004881) B1004881
theorem B6844945 : Blo 702318 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B3011089 : Blo 702318 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B1339993 : Blo 702318 1339993 := bstep (se 2 (by rfl) ⟨502497, by rfl⟩ : syracuseStep 1339993 = 1004995) B1004995
theorem B4518787 : Blo 702318 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B3568535 : Blo 702318 3568535 := bstep (se 1 (by rfl) ⟨2676401, by rfl⟩ : syracuseStep 3568535 = 5352803) B5352803
theorem B750551 : Blo 702318 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B1504307 : Blo 702318 1504307 := bstep (se 1 (by rfl) ⟨1128230, by rfl⟩ : syracuseStep 1504307 = 2256461) B2256461
theorem B8352973 : Blo 702318 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B1602931 : Blo 702318 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B1504793 : Blo 702318 1504793 := bstep (se 2 (by rfl) ⟨564297, by rfl⟩ : syracuseStep 1504793 = 1128595) B1128595
theorem B18315109 : Blo 702318 18315109 := bstep (se 4 (by rfl) ⟨1717041, by rfl⟩ : syracuseStep 18315109 = 3434083) B3434083
theorem B2259137 : Blo 702318 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B1505537 : Blo 702318 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B1145099 : Blo 702318 1145099 := bstep (se 1 (by rfl) ⟨858824, by rfl⟩ : syracuseStep 1145099 = 1717649) B1717649
theorem B12351809 : Blo 702318 12351809 := bstep (se 2 (by rfl) ⟨4631928, by rfl⟩ : syracuseStep 12351809 = 9263857) B9263857
theorem B5700017 : Blo 702318 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B752311 : Blo 702318 752311 := bstep (se 1 (by rfl) ⟨564233, by rfl⟩ : syracuseStep 752311 = 1128467) B1128467
theorem B3046081 : Blo 702318 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B2259677 : Blo 702318 2259677 := bstep (se 3 (by rfl) ⟨423689, by rfl⟩ : syracuseStep 2259677 = 847379) B847379
theorem B11598709 : Blo 702318 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B2849867 : Blo 702318 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B1506433 : Blo 702318 1506433 := bstep (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) B1129825
theorem B4062359 : Blo 702318 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B6028465 : Blo 702318 6028465 := bstep (se 2 (by rfl) ⟨2260674, by rfl⟩ : syracuseStep 6028465 = 4521349) B4521349
theorem B15465653 : Blo 702318 15465653 := bstep (se 5 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 15465653 = 1449905) B1449905
theorem B3014081 : Blo 702318 3014081 := bstep (se 2 (by rfl) ⟨1130280, by rfl⟩ : syracuseStep 3014081 = 2260561) B2260561
theorem B1506775 : Blo 702318 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B7241309 : Blo 702318 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B3210931 : Blo 702318 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B950231 : Blo 702318 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B5341625 : Blo 702318 5341625 := bstep (se 2 (by rfl) ⟨2003109, by rfl⟩ : syracuseStep 5341625 = 4006219) B4006219
theorem B1803023 : Blo 702318 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B3572747 : Blo 702318 3572747 := bstep (se 1 (by rfl) ⟨2679560, by rfl⟩ : syracuseStep 3572747 = 5359121) B5359121
theorem B3572909 : Blo 702318 3572909 := bstep (se 3 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 3572909 = 1339841) B1339841
theorem B5080265 : Blo 702318 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B13534523 : Blo 702318 13534523 := bstep (se 1 (by rfl) ⟨10150892, by rfl⟩ : syracuseStep 13534523 = 20301785) B20301785
theorem B3606059 : Blo 702318 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B7603789 : Blo 702318 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B7636697 : Blo 702318 7636697 := bstep (se 2 (by rfl) ⟨2863761, by rfl⟩ : syracuseStep 7636697 = 5727523) B5727523
theorem B952079 : Blo 702318 952079 := bstep (se 1 (by rfl) ⟨714059, by rfl⟩ : syracuseStep 952079 = 1428119) B1428119
theorem B2033723 : Blo 702318 2033723 := bstep (se 1 (by rfl) ⟨1525292, by rfl⟩ : syracuseStep 2033723 = 3050585) B3050585
theorem B4524119 : Blo 702318 4524119 := bstep (se 1 (by rfl) ⟨3393089, by rfl⟩ : syracuseStep 4524119 = 6786179) B6786179
theorem B952507 : Blo 702318 952507 := bstep (se 1 (by rfl) ⟨714380, by rfl⟩ : syracuseStep 952507 = 1428761) B1428761
theorem B2165021 : Blo 702318 2165021 := bstep (se 3 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 2165021 = 811883) B811883
theorem B2001287 : Blo 702318 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B3574529 : Blo 702318 3574529 := bstep (se 2 (by rfl) ⟨1340448, by rfl⟩ : syracuseStep 3574529 = 2680897) B2680897
theorem B9046799 : Blo 702318 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B3378635 : Blo 702318 3378635 := bstep (se 1 (by rfl) ⟨2533976, by rfl⟩ : syracuseStep 3378635 = 5067953) B5067953
theorem B3575339 : Blo 702318 3575339 := bstep (se 1 (by rfl) ⟨2681504, by rfl⟩ : syracuseStep 3575339 = 5363009) B5363009
theorem B790159 : Blo 702318 790159 := bstep (se 1 (by rfl) ⟨592619, by rfl⟩ : syracuseStep 790159 = 1185239) B1185239
theorem B3805073 : Blo 702318 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B3379097 : Blo 702318 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B5083033 : Blo 702318 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B3182635 : Blo 702318 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B1904755 : Blo 702318 1904755 := bstep (se 1 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 1904755 = 2857133) B2857133
theorem B790663 : Blo 702318 790663 := bstep (se 1 (by rfl) ⟨592997, by rfl⟩ : syracuseStep 790663 = 1185995) B1185995
theorem B2003201 : Blo 702318 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B889147 : Blo 702318 889147 := bstep (se 1 (by rfl) ⟨666860, by rfl⟩ : syracuseStep 889147 = 1333721) B1333721
theorem B790843 : Blo 702318 790843 := bstep (se 1 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 790843 = 1186265) B1186265
theorem B21926435 : Blo 702318 21926435 := bstep (se 1 (by rfl) ⟨16444826, by rfl⟩ : syracuseStep 21926435 = 32889653) B32889653
theorem B4002371 : Blo 702318 4002371 := bstep (se 1 (by rfl) ⟨3001778, by rfl⟩ : syracuseStep 4002371 = 6003557) B6003557
theorem B791311 : Blo 702318 791311 := bstep (se 1 (by rfl) ⟨593483, by rfl⟩ : syracuseStep 791311 = 1186967) B1186967
theorem B889643 : Blo 702318 889643 := bstep (se 1 (by rfl) ⟨667232, by rfl⟩ : syracuseStep 889643 = 1334465) B1334465
theorem B5083955 : Blo 702318 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B1053497 : Blo 702318 1053497 := bstep (se 2 (by rfl) ⟨395061, by rfl⟩ : syracuseStep 1053497 = 790123) B790123
theorem B2003771 : Blo 702318 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B4821875 : Blo 702318 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B1053575 : Blo 702318 1053575 := bstep (se 1 (by rfl) ⟨790181, by rfl⟩ : syracuseStep 1053575 = 1580363) B1580363
theorem B1053611 : Blo 702318 1053611 := bstep (se 1 (by rfl) ⟨790208, by rfl⟩ : syracuseStep 1053611 = 1580417) B1580417
theorem B4166585 : Blo 702318 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B1053641 : Blo 702318 1053641 := bstep (se 2 (by rfl) ⟨395115, by rfl⟩ : syracuseStep 1053641 = 790231) B790231
theorem B2004011 : Blo 702318 2004011 := bstep (se 1 (by rfl) ⟨1503008, by rfl⟩ : syracuseStep 2004011 = 3006017) B3006017
theorem B1053755 : Blo 702318 1053755 := bstep (se 1 (by rfl) ⟨790316, by rfl⟩ : syracuseStep 1053755 = 1580633) B1580633
theorem B1053815 : Blo 702318 1053815 := bstep (se 1 (by rfl) ⟨790361, by rfl⟩ : syracuseStep 1053815 = 1580723) B1580723
theorem B1053839 : Blo 702318 1053839 := bstep (se 1 (by rfl) ⟨790379, by rfl⟩ : syracuseStep 1053839 = 1580759) B1580759
theorem B1053881 : Blo 702318 1053881 := bstep (se 2 (by rfl) ⟨395205, by rfl⟩ : syracuseStep 1053881 = 790411) B790411
theorem B1053959 : Blo 702318 1053959 := bstep (se 1 (by rfl) ⟨790469, by rfl⟩ : syracuseStep 1053959 = 1580939) B1580939
theorem B890119 : Blo 702318 890119 := bstep (se 1 (by rfl) ⟨667589, by rfl⟩ : syracuseStep 890119 = 1335179) B1335179
theorem B791815 : Blo 702318 791815 := bstep (se 1 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 791815 = 1187723) B1187723
theorem B17143073 : Blo 702318 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B1053995 : Blo 702318 1053995 := bstep (se 1 (by rfl) ⟨790496, by rfl⟩ : syracuseStep 1053995 = 1580993) B1580993
theorem B1054025 : Blo 702318 1054025 := bstep (se 2 (by rfl) ⟨395259, by rfl⟩ : syracuseStep 1054025 = 790519) B790519
theorem B1054139 : Blo 702318 1054139 := bstep (se 1 (by rfl) ⟨790604, by rfl⟩ : syracuseStep 1054139 = 1581209) B1581209
theorem B791995 : Blo 702318 791995 := bstep (se 1 (by rfl) ⟨593996, by rfl⟩ : syracuseStep 791995 = 1187993) B1187993
theorem B1054199 : Blo 702318 1054199 := bstep (se 1 (by rfl) ⟨790649, by rfl⟩ : syracuseStep 1054199 = 1581299) B1581299
theorem B1054223 : Blo 702318 1054223 := bstep (se 1 (by rfl) ⟨790667, by rfl⟩ : syracuseStep 1054223 = 1581335) B1581335
theorem B1054265 : Blo 702318 1054265 := bstep (se 2 (by rfl) ⟨395349, by rfl⟩ : syracuseStep 1054265 = 790699) B790699
theorem B3053143 : Blo 702318 3053143 := bstep (se 1 (by rfl) ⟨2289857, by rfl⟩ : syracuseStep 3053143 = 4579715) B4579715
theorem B1054343 : Blo 702318 1054343 := bstep (se 1 (by rfl) ⟨790757, by rfl⟩ : syracuseStep 1054343 = 1581515) B1581515
theorem B1054379 : Blo 702318 1054379 := bstep (se 1 (by rfl) ⟨790784, by rfl⟩ : syracuseStep 1054379 = 1581569) B1581569
theorem B1054409 : Blo 702318 1054409 := bstep (se 2 (by rfl) ⟨395403, by rfl⟩ : syracuseStep 1054409 = 790807) B790807
theorem B890615 : Blo 702318 890615 := bstep (se 1 (by rfl) ⟨667961, by rfl⟩ : syracuseStep 890615 = 1335923) B1335923
theorem B1054523 : Blo 702318 1054523 := bstep (se 1 (by rfl) ⟨790892, by rfl⟩ : syracuseStep 1054523 = 1581785) B1581785
theorem B1054583 : Blo 702318 1054583 := bstep (se 1 (by rfl) ⟨790937, by rfl⟩ : syracuseStep 1054583 = 1581875) B1581875
theorem B1185671 : Blo 702318 1185671 := bstep (se 1 (by rfl) ⟨889253, by rfl⟩ : syracuseStep 1185671 = 1778507) B1778507
theorem B1054607 : Blo 702318 1054607 := bstep (se 1 (by rfl) ⟨790955, by rfl⟩ : syracuseStep 1054607 = 1581911) B1581911
theorem B890767 : Blo 702318 890767 := bstep (se 1 (by rfl) ⟨668075, by rfl⟩ : syracuseStep 890767 = 1336151) B1336151
theorem B792463 : Blo 702318 792463 := bstep (se 1 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 792463 = 1188695) B1188695
theorem B1054649 : Blo 702318 1054649 := bstep (se 2 (by rfl) ⟨395493, by rfl⟩ : syracuseStep 1054649 = 790987) B790987
theorem B5576651 : Blo 702318 5576651 := bstep (se 1 (by rfl) ⟨4182488, by rfl⟩ : syracuseStep 5576651 = 8364977) B8364977
theorem B1054727 : Blo 702318 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B1054763 : Blo 702318 1054763 := bstep (se 1 (by rfl) ⟨791072, by rfl⟩ : syracuseStep 1054763 = 1582145) B1582145
theorem B890939 : Blo 702318 890939 := bstep (se 1 (by rfl) ⟨668204, by rfl⟩ : syracuseStep 890939 = 1336409) B1336409
theorem B1054793 : Blo 702318 1054793 := bstep (se 2 (by rfl) ⟨395547, by rfl⟩ : syracuseStep 1054793 = 791095) B791095
theorem B1906841 : Blo 702318 1906841 := bstep (se 2 (by rfl) ⟨715065, by rfl⟩ : syracuseStep 1906841 = 1430131) B1430131
theorem B32938157 : Blo 702318 32938157 := bstep (se 3 (by rfl) ⟨6175904, by rfl⟩ : syracuseStep 32938157 = 12351809) B12351809
theorem B1054907 : Blo 702318 1054907 := bstep (se 1 (by rfl) ⟨791180, by rfl⟩ : syracuseStep 1054907 = 1582361) B1582361
theorem B1054967 : Blo 702318 1054967 := bstep (se 1 (by rfl) ⟨791225, by rfl⟩ : syracuseStep 1054967 = 1582451) B1582451
theorem B1054991 : Blo 702318 1054991 := bstep (se 1 (by rfl) ⟨791243, by rfl⟩ : syracuseStep 1054991 = 1582487) B1582487
theorem B1055033 : Blo 702318 1055033 := bstep (se 2 (by rfl) ⟨395637, by rfl⟩ : syracuseStep 1055033 = 791275) B791275
theorem B1055111 : Blo 702318 1055111 := bstep (se 1 (by rfl) ⟨791333, by rfl⟩ : syracuseStep 1055111 = 1582667) B1582667
theorem B792967 : Blo 702318 792967 := bstep (se 1 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 792967 = 1189451) B1189451
theorem B1055147 : Blo 702318 1055147 := bstep (se 1 (by rfl) ⟨791360, by rfl⟩ : syracuseStep 1055147 = 1582721) B1582721
theorem B1055177 : Blo 702318 1055177 := bstep (se 2 (by rfl) ⟨395691, by rfl⟩ : syracuseStep 1055177 = 791383) B791383
theorem B1186319 : Blo 702318 1186319 := bstep (se 1 (by rfl) ⟨889739, by rfl⟩ : syracuseStep 1186319 = 1779479) B1779479
theorem B1055291 : Blo 702318 1055291 := bstep (se 1 (by rfl) ⟨791468, by rfl⟩ : syracuseStep 1055291 = 1582937) B1582937
theorem B793147 : Blo 702318 793147 := bstep (se 1 (by rfl) ⟨594860, by rfl⟩ : syracuseStep 793147 = 1189721) B1189721
theorem B1055351 : Blo 702318 1055351 := bstep (se 1 (by rfl) ⟨791513, by rfl⟩ : syracuseStep 1055351 = 1583027) B1583027
theorem B1055375 : Blo 702318 1055375 := bstep (se 1 (by rfl) ⟨791531, by rfl⟩ : syracuseStep 1055375 = 1583063) B1583063
theorem B1055417 : Blo 702318 1055417 := bstep (se 2 (by rfl) ⟨395781, by rfl⟩ : syracuseStep 1055417 = 791563) B791563
theorem B1055495 : Blo 702318 1055495 := bstep (se 1 (by rfl) ⟨791621, by rfl⟩ : syracuseStep 1055495 = 1583243) B1583243
theorem B1055531 : Blo 702318 1055531 := bstep (se 1 (by rfl) ⟨791648, by rfl⟩ : syracuseStep 1055531 = 1583297) B1583297
theorem B1055561 : Blo 702318 1055561 := bstep (se 2 (by rfl) ⟨395835, by rfl⟩ : syracuseStep 1055561 = 791671) B791671
theorem B4004761 : Blo 702318 4004761 := bstep (se 2 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 4004761 = 3003571) B3003571
theorem B1055675 : Blo 702318 1055675 := bstep (se 1 (by rfl) ⟨791756, by rfl⟩ : syracuseStep 1055675 = 1583513) B1583513
theorem B1055735 : Blo 702318 1055735 := bstep (se 1 (by rfl) ⟨791801, by rfl⟩ : syracuseStep 1055735 = 1583603) B1583603
theorem B891911 : Blo 702318 891911 := bstep (se 1 (by rfl) ⟨668933, by rfl⟩ : syracuseStep 891911 = 1337867) B1337867
theorem B1055759 : Blo 702318 1055759 := bstep (se 1 (by rfl) ⟨791819, by rfl⟩ : syracuseStep 1055759 = 1583639) B1583639
theorem B793615 : Blo 702318 793615 := bstep (se 1 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 793615 = 1190423) B1190423
theorem B1186859 : Blo 702318 1186859 := bstep (se 1 (by rfl) ⟨890144, by rfl⟩ : syracuseStep 1186859 = 1780289) B1780289
theorem B1055801 : Blo 702318 1055801 := bstep (se 2 (by rfl) ⟨395925, by rfl⟩ : syracuseStep 1055801 = 791851) B791851
theorem B1055879 : Blo 702318 1055879 := bstep (se 1 (by rfl) ⟨791909, by rfl⟩ : syracuseStep 1055879 = 1583819) B1583819
theorem B2137241 : Blo 702318 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B1055915 : Blo 702318 1055915 := bstep (se 1 (by rfl) ⟨791936, by rfl⟩ : syracuseStep 1055915 = 1583873) B1583873
theorem B1055945 : Blo 702318 1055945 := bstep (se 2 (by rfl) ⟨395979, by rfl⟩ : syracuseStep 1055945 = 791959) B791959
theorem B1056059 : Blo 702318 1056059 := bstep (se 1 (by rfl) ⟨792044, by rfl⟩ : syracuseStep 1056059 = 1584089) B1584089
theorem B1056119 : Blo 702318 1056119 := bstep (se 1 (by rfl) ⟨792089, by rfl⟩ : syracuseStep 1056119 = 1584179) B1584179
theorem B1056143 : Blo 702318 1056143 := bstep (se 1 (by rfl) ⟨792107, by rfl⟩ : syracuseStep 1056143 = 1584215) B1584215
theorem B8002961 : Blo 702318 8002961 := bstep (se 2 (by rfl) ⟨3001110, by rfl⟩ : syracuseStep 8002961 = 6002221) B6002221
theorem B1580435 : Blo 702318 1580435 := bstep (se 1 (by rfl) ⟨1185326, by rfl⟩ : syracuseStep 1580435 = 2370653) B2370653
theorem B1187257 : Blo 702318 1187257 := bstep (se 2 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 1187257 = 890443) B890443
theorem B1056185 : Blo 702318 1056185 := bstep (se 2 (by rfl) ⟨396069, by rfl⟩ : syracuseStep 1056185 = 792139) B792139
theorem B1580489 : Blo 702318 1580489 := bstep (se 2 (by rfl) ⟨592683, by rfl⟩ : syracuseStep 1580489 = 1185367) B1185367
theorem B1056263 : Blo 702318 1056263 := bstep (se 1 (by rfl) ⟨792197, by rfl⟩ : syracuseStep 1056263 = 1584395) B1584395
theorem B794119 : Blo 702318 794119 := bstep (se 1 (by rfl) ⟨595589, by rfl⟩ : syracuseStep 794119 = 1191179) B1191179
theorem B1056299 : Blo 702318 1056299 := bstep (se 1 (by rfl) ⟨792224, by rfl⟩ : syracuseStep 1056299 = 1584449) B1584449
theorem B1056329 : Blo 702318 1056329 := bstep (se 2 (by rfl) ⟨396123, by rfl⟩ : syracuseStep 1056329 = 792247) B792247
theorem B892559 : Blo 702318 892559 := bstep (se 1 (by rfl) ⟨669419, by rfl⟩ : syracuseStep 892559 = 1338839) B1338839
theorem B1056443 : Blo 702318 1056443 := bstep (se 1 (by rfl) ⟨792332, by rfl⟩ : syracuseStep 1056443 = 1584665) B1584665
theorem B794299 : Blo 702318 794299 := bstep (se 1 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 794299 = 1191449) B1191449
theorem B1056503 : Blo 702318 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B13573889 : Blo 702318 13573889 := bstep (se 2 (by rfl) ⟨5090208, by rfl⟩ : syracuseStep 13573889 = 10180417) B10180417
theorem B1056527 : Blo 702318 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B24420145 : Blo 702318 24420145 := bstep (se 2 (by rfl) ⟨9157554, by rfl⟩ : syracuseStep 24420145 = 18315109) B18315109
theorem B1056569 : Blo 702318 1056569 := bstep (se 2 (by rfl) ⟨396213, by rfl⟩ : syracuseStep 1056569 = 792427) B792427
theorem B1056647 : Blo 702318 1056647 := bstep (se 1 (by rfl) ⟨792485, by rfl⟩ : syracuseStep 1056647 = 1584971) B1584971
theorem B1056683 : Blo 702318 1056683 := bstep (se 1 (by rfl) ⟨792512, by rfl⟩ : syracuseStep 1056683 = 1585025) B1585025
theorem B3219385 : Blo 702318 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B1056713 : Blo 702318 1056713 := bstep (se 2 (by rfl) ⟨396267, by rfl⟩ : syracuseStep 1056713 = 792535) B792535
theorem B6758423 : Blo 702318 6758423 := bstep (se 1 (by rfl) ⟨5068817, by rfl⟩ : syracuseStep 6758423 = 10137635) B10137635
theorem B1056827 : Blo 702318 1056827 := bstep (se 1 (by rfl) ⟨792620, by rfl⟩ : syracuseStep 1056827 = 1585241) B1585241
theorem B1187959 : Blo 702318 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B1056887 : Blo 702318 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B1581191 : Blo 702318 1581191 := bstep (se 1 (by rfl) ⟨1185893, by rfl⟩ : syracuseStep 1581191 = 2371787) B2371787
theorem B1056911 : Blo 702318 1056911 := bstep (se 1 (by rfl) ⟨792683, by rfl⟩ : syracuseStep 1056911 = 1585367) B1585367
theorem B1056953 : Blo 702318 1056953 := bstep (se 2 (by rfl) ⟨396357, by rfl⟩ : syracuseStep 1056953 = 792715) B792715
theorem B1057031 : Blo 702318 1057031 := bstep (se 1 (by rfl) ⟨792773, by rfl⟩ : syracuseStep 1057031 = 1585547) B1585547
theorem B1057067 : Blo 702318 1057067 := bstep (se 1 (by rfl) ⟨792800, by rfl⟩ : syracuseStep 1057067 = 1585601) B1585601
theorem B1581371 : Blo 702318 1581371 := bstep (se 1 (by rfl) ⟨1186028, by rfl⟩ : syracuseStep 1581371 = 2372057) B2372057
theorem B1188155 : Blo 702318 1188155 := bstep (se 1 (by rfl) ⟨891116, by rfl⟩ : syracuseStep 1188155 = 1782233) B1782233
theorem B5710139 : Blo 702318 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B1057097 : Blo 702318 1057097 := bstep (se 2 (by rfl) ⟨396411, by rfl⟩ : syracuseStep 1057097 = 792823) B792823
theorem B1909111 : Blo 702318 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B1581497 : Blo 702318 1581497 := bstep (se 2 (by rfl) ⟨593061, by rfl⟩ : syracuseStep 1581497 = 1186123) B1186123
theorem B1057211 : Blo 702318 1057211 := bstep (se 1 (by rfl) ⟨792908, by rfl⟩ : syracuseStep 1057211 = 1585817) B1585817
theorem B1057271 : Blo 702318 1057271 := bstep (se 1 (by rfl) ⟨792953, by rfl⟩ : syracuseStep 1057271 = 1585907) B1585907
theorem B1057295 : Blo 702318 1057295 := bstep (se 1 (by rfl) ⟨792971, by rfl⟩ : syracuseStep 1057295 = 1585943) B1585943
theorem B1057337 : Blo 702318 1057337 := bstep (se 2 (by rfl) ⟨396501, by rfl⟩ : syracuseStep 1057337 = 793003) B793003
theorem B1057415 : Blo 702318 1057415 := bstep (se 1 (by rfl) ⟨793061, by rfl⟩ : syracuseStep 1057415 = 1586123) B1586123
theorem B1450631 : Blo 702318 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B1057451 : Blo 702318 1057451 := bstep (se 1 (by rfl) ⟨793088, by rfl⟩ : syracuseStep 1057451 = 1586177) B1586177
theorem B1188553 : Blo 702318 1188553 := bstep (se 2 (by rfl) ⟨445707, by rfl⟩ : syracuseStep 1188553 = 891415) B891415
theorem B1057481 : Blo 702318 1057481 := bstep (se 2 (by rfl) ⟨396555, by rfl⟩ : syracuseStep 1057481 = 793111) B793111
theorem B1581839 : Blo 702318 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B1581857 : Blo 702318 1581857 := bstep (se 2 (by rfl) ⟨593196, by rfl⟩ : syracuseStep 1581857 = 1186393) B1186393
theorem B1057595 : Blo 702318 1057595 := bstep (se 1 (by rfl) ⟨793196, by rfl⟩ : syracuseStep 1057595 = 1586393) B1586393
theorem B4006745 : Blo 702318 4006745 := bstep (se 2 (by rfl) ⟨1502529, by rfl⟩ : syracuseStep 4006745 = 3005059) B3005059
theorem B1057655 : Blo 702318 1057655 := bstep (se 1 (by rfl) ⟨793241, by rfl⟩ : syracuseStep 1057655 = 1586483) B1586483
theorem B1057679 : Blo 702318 1057679 := bstep (se 1 (by rfl) ⟨793259, by rfl⟩ : syracuseStep 1057679 = 1586519) B1586519
theorem B1057721 : Blo 702318 1057721 := bstep (se 2 (by rfl) ⟨396645, by rfl⟩ : syracuseStep 1057721 = 793291) B793291
theorem B1057799 : Blo 702318 1057799 := bstep (se 1 (by rfl) ⟨793349, by rfl⟩ : syracuseStep 1057799 = 1586699) B1586699
theorem B1778699 : Blo 702318 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1057835 : Blo 702318 1057835 := bstep (se 1 (by rfl) ⟨793376, by rfl⟩ : syracuseStep 1057835 = 1586753) B1586753
theorem B1057865 : Blo 702318 1057865 := bstep (se 2 (by rfl) ⟨396699, by rfl⟩ : syracuseStep 1057865 = 793399) B793399
theorem B1582199 : Blo 702318 1582199 := bstep (se 1 (by rfl) ⟨1186649, by rfl⟩ : syracuseStep 1582199 = 2373299) B2373299
theorem B1057979 : Blo 702318 1057979 := bstep (se 1 (by rfl) ⟨793484, by rfl⟩ : syracuseStep 1057979 = 1586969) B1586969
theorem B1058039 : Blo 702318 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B1058063 : Blo 702318 1058063 := bstep (se 1 (by rfl) ⟨793547, by rfl⟩ : syracuseStep 1058063 = 1587095) B1587095
theorem B1582379 : Blo 702318 1582379 := bstep (se 1 (by rfl) ⟨1186784, by rfl⟩ : syracuseStep 1582379 = 2373569) B2373569
theorem B1058105 : Blo 702318 1058105 := bstep (se 2 (by rfl) ⟨396789, by rfl⟩ : syracuseStep 1058105 = 793579) B793579
theorem B1189255 : Blo 702318 1189255 := bstep (se 1 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 1189255 = 1783883) B1783883
theorem B1058183 : Blo 702318 1058183 := bstep (se 1 (by rfl) ⟨793637, by rfl⟩ : syracuseStep 1058183 = 1587275) B1587275
theorem B1058219 : Blo 702318 1058219 := bstep (se 1 (by rfl) ⟨793664, by rfl⟩ : syracuseStep 1058219 = 1587329) B1587329
theorem B1058249 : Blo 702318 1058249 := bstep (se 2 (by rfl) ⟨396843, by rfl⟩ : syracuseStep 1058249 = 793687) B793687
theorem B2008577 : Blo 702318 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B763399 : Blo 702318 763399 := bstep (se 1 (by rfl) ⟨572549, by rfl⟩ : syracuseStep 763399 = 1145099) B1145099
theorem B1058363 : Blo 702318 1058363 := bstep (se 1 (by rfl) ⟨793772, by rfl⟩ : syracuseStep 1058363 = 1587545) B1587545
theorem B8037953 : Blo 702318 8037953 := bstep (se 2 (by rfl) ⟨3014232, by rfl⟩ : syracuseStep 8037953 = 6028465) B6028465
theorem B1058423 : Blo 702318 1058423 := bstep (se 1 (by rfl) ⟨793817, by rfl⟩ : syracuseStep 1058423 = 1587635) B1587635
theorem B1058447 : Blo 702318 1058447 := bstep (se 1 (by rfl) ⟨793835, by rfl⟩ : syracuseStep 1058447 = 1587671) B1587671
theorem B1779347 : Blo 702318 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B1582739 : Blo 702318 1582739 := bstep (se 1 (by rfl) ⟨1187054, by rfl⟩ : syracuseStep 1582739 = 2374109) B2374109
theorem B1058489 : Blo 702318 1058489 := bstep (se 2 (by rfl) ⟨396933, by rfl⟩ : syracuseStep 1058489 = 793867) B793867
theorem B1582793 : Blo 702318 1582793 := bstep (se 2 (by rfl) ⟨593547, by rfl⟩ : syracuseStep 1582793 = 1187095) B1187095
theorem B1058567 : Blo 702318 1058567 := bstep (se 1 (by rfl) ⟨793925, by rfl⟩ : syracuseStep 1058567 = 1587851) B1587851
theorem B1058603 : Blo 702318 1058603 := bstep (se 1 (by rfl) ⟨793952, by rfl⟩ : syracuseStep 1058603 = 1587905) B1587905
theorem B1058633 : Blo 702318 1058633 := bstep (se 2 (by rfl) ⟨396987, by rfl⟩ : syracuseStep 1058633 = 793975) B793975
theorem B1779641 : Blo 702318 1779641 := bstep (se 2 (by rfl) ⟨667365, by rfl⟩ : syracuseStep 1779641 = 1334731) B1334731
theorem B1058747 : Blo 702318 1058747 := bstep (se 1 (by rfl) ⟨794060, by rfl⟩ : syracuseStep 1058747 = 1588121) B1588121
theorem B2009033 : Blo 702318 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B1058807 : Blo 702318 1058807 := bstep (se 1 (by rfl) ⟨794105, by rfl⟩ : syracuseStep 1058807 = 1588211) B1588211
theorem B1189903 : Blo 702318 1189903 := bstep (se 1 (by rfl) ⟨892427, by rfl⟩ : syracuseStep 1189903 = 1784855) B1784855
theorem B1058831 : Blo 702318 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B1058873 : Blo 702318 1058873 := bstep (se 2 (by rfl) ⟨397077, by rfl⟩ : syracuseStep 1058873 = 794155) B794155
theorem B1058951 : Blo 702318 1058951 := bstep (se 1 (by rfl) ⟨794213, by rfl⟩ : syracuseStep 1058951 = 1588427) B1588427
theorem B1058987 : Blo 702318 1058987 := bstep (se 1 (by rfl) ⟨794240, by rfl⟩ : syracuseStep 1058987 = 1588481) B1588481
theorem B1059017 : Blo 702318 1059017 := bstep (se 2 (by rfl) ⟨397131, by rfl⟩ : syracuseStep 1059017 = 794263) B794263
theorem B8005877 : Blo 702318 8005877 := bstep (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) B750551
theorem B2009387 : Blo 702318 2009387 := bstep (se 1 (by rfl) ⟨1507040, by rfl⟩ : syracuseStep 2009387 = 3014081) B3014081
theorem B1059131 : Blo 702318 1059131 := bstep (se 1 (by rfl) ⟨794348, by rfl⟩ : syracuseStep 1059131 = 1588697) B1588697
theorem B1059191 : Blo 702318 1059191 := bstep (se 1 (by rfl) ⟨794393, by rfl⟩ : syracuseStep 1059191 = 1588787) B1588787
theorem B1583495 : Blo 702318 1583495 := bstep (se 1 (by rfl) ⟨1187621, by rfl⟩ : syracuseStep 1583495 = 2375243) B2375243
theorem B1059215 : Blo 702318 1059215 := bstep (se 1 (by rfl) ⟨794411, by rfl⟩ : syracuseStep 1059215 = 1588823) B1588823
theorem B4827539 : Blo 702318 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B1059257 : Blo 702318 1059257 := bstep (se 2 (by rfl) ⟨397221, by rfl⟩ : syracuseStep 1059257 = 794443) B794443
theorem B1059335 : Blo 702318 1059335 := bstep (se 1 (by rfl) ⟨794501, by rfl⟩ : syracuseStep 1059335 = 1589003) B1589003
theorem B1190443 : Blo 702318 1190443 := bstep (se 1 (by rfl) ⟨892832, by rfl⟩ : syracuseStep 1190443 = 1785665) B1785665
theorem B1059371 : Blo 702318 1059371 := bstep (se 1 (by rfl) ⟨794528, by rfl⟩ : syracuseStep 1059371 = 1589057) B1589057
theorem B1583675 : Blo 702318 1583675 := bstep (se 1 (by rfl) ⟨1187756, by rfl⟩ : syracuseStep 1583675 = 2375513) B2375513
theorem B2533949 : Blo 702318 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B1059401 : Blo 702318 1059401 := bstep (se 2 (by rfl) ⟨397275, by rfl⟩ : syracuseStep 1059401 = 794551) B794551
theorem B1780339 : Blo 702318 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B1583801 : Blo 702318 1583801 := bstep (se 2 (by rfl) ⟨593925, by rfl⟩ : syracuseStep 1583801 = 1187851) B1187851
theorem B1190585 : Blo 702318 1190585 := bstep (se 2 (by rfl) ⟨446469, by rfl⟩ : syracuseStep 1190585 = 892939) B892939
theorem B2009785 : Blo 702318 2009785 := bstep (se 2 (by rfl) ⟨753669, by rfl⟩ : syracuseStep 2009785 = 1507339) B1507339
theorem B6007553 : Blo 702318 6007553 := bstep (se 2 (by rfl) ⟨2252832, by rfl⟩ : syracuseStep 6007553 = 4505665) B4505665
theorem B1780481 : Blo 702318 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B11447203 : Blo 702318 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1584143 : Blo 702318 1584143 := bstep (se 1 (by rfl) ⟨1188107, by rfl⟩ : syracuseStep 1584143 = 2376215) B2376215
theorem B1584161 : Blo 702318 1584161 := bstep (se 2 (by rfl) ⟨594060, by rfl⟩ : syracuseStep 1584161 = 1188121) B1188121
theorem B64990349 : Blo 702318 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B2370761 : Blo 702318 2370761 := bstep (se 2 (by rfl) ⟨889035, by rfl⟩ : syracuseStep 2370761 = 1778071) B1778071
theorem B1780937 : Blo 702318 1780937 := bstep (se 2 (by rfl) ⟨667851, by rfl⟩ : syracuseStep 1780937 = 1335703) B1335703
theorem B1584503 : Blo 702318 1584503 := bstep (se 1 (by rfl) ⟨1188377, by rfl⟩ : syracuseStep 1584503 = 2376755) B2376755
theorem B1191287 : Blo 702318 1191287 := bstep (se 1 (by rfl) ⟨893465, by rfl⟩ : syracuseStep 1191287 = 1786931) B1786931
theorem B1781291 : Blo 702318 1781291 := bstep (se 1 (by rfl) ⟨1335968, by rfl⟩ : syracuseStep 1781291 = 2671937) B2671937
theorem B1584683 : Blo 702318 1584683 := bstep (se 1 (by rfl) ⟨1188512, by rfl⟩ : syracuseStep 1584683 = 2377025) B2377025
theorem B1191739 : Blo 702318 1191739 := bstep (se 1 (by rfl) ⟨893804, by rfl⟩ : syracuseStep 1191739 = 1787609) B1787609
theorem B2371463 : Blo 702318 2371463 := bstep (se 1 (by rfl) ⟨1778597, by rfl⟩ : syracuseStep 2371463 = 3557195) B3557195
theorem B1585043 : Blo 702318 1585043 := bstep (se 1 (by rfl) ⟨1188782, by rfl⟩ : syracuseStep 1585043 = 2377565) B2377565
theorem B2011027 : Blo 702318 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B1585097 : Blo 702318 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B1191881 : Blo 702318 1191881 := bstep (se 2 (by rfl) ⟨446955, by rfl⟩ : syracuseStep 1191881 = 893911) B893911
theorem B4501565 : Blo 702318 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B3387629 : Blo 702318 3387629 := bstep (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) B1270361
theorem B2371841 : Blo 702318 2371841 := bstep (se 2 (by rfl) ⟨889440, by rfl⟩ : syracuseStep 2371841 = 1778881) B1778881
theorem B6861115 : Blo 702318 6861115 := bstep (se 1 (by rfl) ⟨5145836, by rfl⟩ : syracuseStep 6861115 = 10291673) B10291673
theorem B4272587 : Blo 702318 4272587 := bstep (se 1 (by rfl) ⟨3204440, by rfl⟩ : syracuseStep 4272587 = 6408881) B6408881
theorem B1782283 : Blo 702318 1782283 := bstep (se 1 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 1782283 = 2673425) B2673425
theorem B1126955 : Blo 702318 1126955 := bstep (se 1 (by rfl) ⟨845216, by rfl⟩ : syracuseStep 1126955 = 1690433) B1690433
theorem B1585799 : Blo 702318 1585799 := bstep (se 1 (by rfl) ⟨1189349, by rfl⟩ : syracuseStep 1585799 = 2378699) B2378699
theorem B1782425 : Blo 702318 1782425 := bstep (se 2 (by rfl) ⟨668409, by rfl⟩ : syracuseStep 1782425 = 1336819) B1336819
theorem B1782587 : Blo 702318 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B1585979 : Blo 702318 1585979 := bstep (se 1 (by rfl) ⟨1189484, by rfl⟩ : syracuseStep 1585979 = 2378969) B2378969
theorem B4010867 : Blo 702318 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B1586105 : Blo 702318 1586105 := bstep (se 2 (by rfl) ⟨594789, by rfl⟩ : syracuseStep 1586105 = 1189579) B1189579
theorem B1127467 : Blo 702318 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B2667563 : Blo 702318 2667563 := bstep (se 1 (by rfl) ⟨2000672, by rfl⟩ : syracuseStep 2667563 = 4001345) B4001345
theorem B2372651 : Blo 702318 2372651 := bstep (se 1 (by rfl) ⟨1779488, by rfl⟩ : syracuseStep 2372651 = 3558977) B3558977
theorem B1782931 : Blo 702318 1782931 := bstep (se 1 (by rfl) ⟨1337198, by rfl⟩ : syracuseStep 1782931 = 2674397) B2674397
theorem B1586447 : Blo 702318 1586447 := bstep (se 1 (by rfl) ⟨1189835, by rfl⟩ : syracuseStep 1586447 = 2379671) B2379671
theorem B1783073 : Blo 702318 1783073 := bstep (se 2 (by rfl) ⟨668652, by rfl⟩ : syracuseStep 1783073 = 1337305) B1337305
theorem B1586465 : Blo 702318 1586465 := bstep (se 2 (by rfl) ⟨594924, by rfl⟩ : syracuseStep 1586465 = 1189849) B1189849
theorem B8566373 : Blo 702318 8566373 := bstep (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) B1606195
theorem B1586807 : Blo 702318 1586807 := bstep (se 1 (by rfl) ⟨1190105, by rfl⟩ : syracuseStep 1586807 = 2380211) B2380211
theorem B1586987 : Blo 702318 1586987 := bstep (se 1 (by rfl) ⟨1190240, by rfl⟩ : syracuseStep 1586987 = 2380481) B2380481
theorem B702343 : Blo 702318 702343 := bstep (se 1 (by rfl) ⟨526757, by rfl⟩ : syracuseStep 702343 = 1053515) B1053515
theorem B702351 : Blo 702318 702351 := bstep (se 1 (by rfl) ⟨526763, by rfl⟩ : syracuseStep 702351 = 1053527) B1053527
theorem B702395 : Blo 702318 702395 := bstep (se 1 (by rfl) ⟨526796, by rfl⟩ : syracuseStep 702395 = 1053593) B1053593
theorem B702471 : Blo 702318 702471 := bstep (se 1 (by rfl) ⟨526853, by rfl⟩ : syracuseStep 702471 = 1053707) B1053707
theorem B702479 : Blo 702318 702479 := bstep (se 1 (by rfl) ⟨526859, by rfl⟩ : syracuseStep 702479 = 1053719) B1053719
theorem B702523 : Blo 702318 702523 := bstep (se 1 (by rfl) ⟨526892, by rfl⟩ : syracuseStep 702523 = 1053785) B1053785
theorem B702599 : Blo 702318 702599 := bstep (se 1 (by rfl) ⟨526949, by rfl⟩ : syracuseStep 702599 = 1053899) B1053899
theorem B702607 : Blo 702318 702607 := bstep (se 1 (by rfl) ⟨526955, by rfl⟩ : syracuseStep 702607 = 1053911) B1053911
theorem B1587347 : Blo 702318 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B702651 : Blo 702318 702651 := bstep (se 1 (by rfl) ⟨526988, by rfl⟩ : syracuseStep 702651 = 1053977) B1053977
theorem B1587401 : Blo 702318 1587401 := bstep (se 2 (by rfl) ⟨595275, by rfl⟩ : syracuseStep 1587401 = 1190551) B1190551
theorem B2144513 : Blo 702318 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B1784065 : Blo 702318 1784065 := bstep (se 2 (by rfl) ⟨669024, by rfl⟩ : syracuseStep 1784065 = 1338049) B1338049
theorem B702727 : Blo 702318 702727 := bstep (se 1 (by rfl) ⟨527045, by rfl⟩ : syracuseStep 702727 = 1054091) B1054091
theorem B702735 : Blo 702318 702735 := bstep (se 1 (by rfl) ⟨527051, by rfl⟩ : syracuseStep 702735 = 1054103) B1054103
theorem B4012325 : Blo 702318 4012325 := bstep (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) B752311
theorem B702779 : Blo 702318 702779 := bstep (se 1 (by rfl) ⟨527084, by rfl⟩ : syracuseStep 702779 = 1054169) B1054169
theorem B2373947 : Blo 702318 2373947 := bstep (se 1 (by rfl) ⟨1780460, by rfl⟩ : syracuseStep 2373947 = 3560921) B3560921
theorem B702855 : Blo 702318 702855 := bstep (se 1 (by rfl) ⟨527141, by rfl⟩ : syracuseStep 702855 = 1054283) B1054283
theorem B702863 : Blo 702318 702863 := bstep (se 1 (by rfl) ⟨527147, by rfl⟩ : syracuseStep 702863 = 1054295) B1054295
theorem B702907 : Blo 702318 702907 := bstep (se 1 (by rfl) ⟨527180, by rfl⟩ : syracuseStep 702907 = 1054361) B1054361
theorem B702983 : Blo 702318 702983 := bstep (se 1 (by rfl) ⟨527237, by rfl⟩ : syracuseStep 702983 = 1054475) B1054475
theorem B702991 : Blo 702318 702991 := bstep (se 1 (by rfl) ⟨527243, by rfl⟩ : syracuseStep 702991 = 1054487) B1054487
theorem B703035 : Blo 702318 703035 := bstep (se 1 (by rfl) ⟨527276, by rfl⟩ : syracuseStep 703035 = 1054553) B1054553
theorem B703111 : Blo 702318 703111 := bstep (se 1 (by rfl) ⟨527333, by rfl⟩ : syracuseStep 703111 = 1054667) B1054667
theorem B703119 : Blo 702318 703119 := bstep (se 1 (by rfl) ⟨527339, by rfl⟩ : syracuseStep 703119 = 1054679) B1054679
theorem B703163 : Blo 702318 703163 := bstep (se 1 (by rfl) ⟨527372, by rfl⟩ : syracuseStep 703163 = 1054745) B1054745
theorem B703239 : Blo 702318 703239 := bstep (se 1 (by rfl) ⟨527429, by rfl⟩ : syracuseStep 703239 = 1054859) B1054859
theorem B703247 : Blo 702318 703247 := bstep (se 1 (by rfl) ⟨527435, by rfl⟩ : syracuseStep 703247 = 1054871) B1054871
theorem B2374433 : Blo 702318 2374433 := bstep (se 2 (by rfl) ⟨890412, by rfl⟩ : syracuseStep 2374433 = 1780825) B1780825
theorem B703291 : Blo 702318 703291 := bstep (se 1 (by rfl) ⟨527468, by rfl⟩ : syracuseStep 703291 = 1054937) B1054937
theorem B8567641 : Blo 702318 8567641 := bstep (se 2 (by rfl) ⟨3212865, by rfl⟩ : syracuseStep 8567641 = 6425731) B6425731
theorem B1784663 : Blo 702318 1784663 := bstep (se 1 (by rfl) ⟨1338497, by rfl⟩ : syracuseStep 1784663 = 2676995) B2676995
theorem B703367 : Blo 702318 703367 := bstep (se 1 (by rfl) ⟨527525, by rfl⟩ : syracuseStep 703367 = 1055051) B1055051
theorem B1588103 : Blo 702318 1588103 := bstep (se 1 (by rfl) ⟨1191077, by rfl⟩ : syracuseStep 1588103 = 2382155) B2382155
theorem B703375 : Blo 702318 703375 := bstep (se 1 (by rfl) ⟨527531, by rfl⟩ : syracuseStep 703375 = 1055063) B1055063
theorem B3619729 : Blo 702318 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B703419 : Blo 702318 703419 := bstep (se 1 (by rfl) ⟨527564, by rfl⟩ : syracuseStep 703419 = 1055129) B1055129
theorem B4013009 : Blo 702318 4013009 := bstep (se 2 (by rfl) ⟨1504878, by rfl⟩ : syracuseStep 4013009 = 3009757) B3009757
theorem B703495 : Blo 702318 703495 := bstep (se 1 (by rfl) ⟨527621, by rfl⟩ : syracuseStep 703495 = 1055243) B1055243
theorem B703503 : Blo 702318 703503 := bstep (se 1 (by rfl) ⟨527627, by rfl⟩ : syracuseStep 703503 = 1055255) B1055255
theorem B6011927 : Blo 702318 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B1784875 : Blo 702318 1784875 := bstep (se 1 (by rfl) ⟨1338656, by rfl⟩ : syracuseStep 1784875 = 2677313) B2677313
theorem B703547 : Blo 702318 703547 := bstep (se 1 (by rfl) ⟨527660, by rfl⟩ : syracuseStep 703547 = 1055321) B1055321
theorem B1588283 : Blo 702318 1588283 := bstep (se 1 (by rfl) ⟨1191212, by rfl⟩ : syracuseStep 1588283 = 2382425) B2382425
theorem B3423293 : Blo 702318 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B703623 : Blo 702318 703623 := bstep (se 1 (by rfl) ⟨527717, by rfl⟩ : syracuseStep 703623 = 1055435) B1055435
theorem B703631 : Blo 702318 703631 := bstep (se 1 (by rfl) ⟨527723, by rfl⟩ : syracuseStep 703631 = 1055447) B1055447
theorem B1785017 : Blo 702318 1785017 := bstep (se 2 (by rfl) ⟨669381, by rfl⟩ : syracuseStep 1785017 = 1338763) B1338763
theorem B1588409 : Blo 702318 1588409 := bstep (se 2 (by rfl) ⟨595653, by rfl⟩ : syracuseStep 1588409 = 1191307) B1191307
theorem B703675 : Blo 702318 703675 := bstep (se 1 (by rfl) ⟨527756, by rfl⟩ : syracuseStep 703675 = 1055513) B1055513
theorem B703751 : Blo 702318 703751 := bstep (se 1 (by rfl) ⟨527813, by rfl⟩ : syracuseStep 703751 = 1055627) B1055627
theorem B703759 : Blo 702318 703759 := bstep (se 1 (by rfl) ⟨527819, by rfl⟩ : syracuseStep 703759 = 1055639) B1055639
theorem B4013327 : Blo 702318 4013327 := bstep (se 1 (by rfl) ⟨3009995, by rfl⟩ : syracuseStep 4013327 = 6019991) B6019991
theorem B703803 : Blo 702318 703803 := bstep (se 1 (by rfl) ⟨527852, by rfl⟩ : syracuseStep 703803 = 1055705) B1055705
theorem B2375027 : Blo 702318 2375027 := bstep (se 1 (by rfl) ⟨1781270, by rfl⟩ : syracuseStep 2375027 = 3562541) B3562541
theorem B703879 : Blo 702318 703879 := bstep (se 1 (by rfl) ⟨527909, by rfl⟩ : syracuseStep 703879 = 1055819) B1055819
theorem B703887 : Blo 702318 703887 := bstep (se 1 (by rfl) ⟨527915, by rfl⟩ : syracuseStep 703887 = 1055831) B1055831
theorem B6012305 : Blo 702318 6012305 := bstep (se 2 (by rfl) ⟨2254614, by rfl⟩ : syracuseStep 6012305 = 4509229) B4509229
theorem B703931 : Blo 702318 703931 := bstep (se 1 (by rfl) ⟨527948, by rfl⟩ : syracuseStep 703931 = 1055897) B1055897
theorem B704007 : Blo 702318 704007 := bstep (se 1 (by rfl) ⟨528005, by rfl⟩ : syracuseStep 704007 = 1056011) B1056011
theorem B704015 : Blo 702318 704015 := bstep (se 1 (by rfl) ⟨528011, by rfl⟩ : syracuseStep 704015 = 1056023) B1056023
theorem B1588751 : Blo 702318 1588751 := bstep (se 1 (by rfl) ⟨1191563, by rfl⟩ : syracuseStep 1588751 = 2383127) B2383127
theorem B1588769 : Blo 702318 1588769 := bstep (se 2 (by rfl) ⟨595788, by rfl⟩ : syracuseStep 1588769 = 1191577) B1191577
theorem B704059 : Blo 702318 704059 := bstep (se 1 (by rfl) ⟨528044, by rfl⟩ : syracuseStep 704059 = 1056089) B1056089
theorem B704135 : Blo 702318 704135 := bstep (se 1 (by rfl) ⟨528101, by rfl⟩ : syracuseStep 704135 = 1056203) B1056203
theorem B704143 : Blo 702318 704143 := bstep (se 1 (by rfl) ⟨528107, by rfl⟩ : syracuseStep 704143 = 1056215) B1056215
theorem B704187 : Blo 702318 704187 := bstep (se 1 (by rfl) ⟨528140, by rfl⟩ : syracuseStep 704187 = 1056281) B1056281
theorem B704263 : Blo 702318 704263 := bstep (se 1 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 704263 = 1056395) B1056395
theorem B704271 : Blo 702318 704271 := bstep (se 1 (by rfl) ⟨528203, by rfl⟩ : syracuseStep 704271 = 1056407) B1056407
theorem B704315 : Blo 702318 704315 := bstep (se 1 (by rfl) ⟨528236, by rfl⟩ : syracuseStep 704315 = 1056473) B1056473
theorem B1589111 : Blo 702318 1589111 := bstep (se 1 (by rfl) ⟨1191833, by rfl⟩ : syracuseStep 1589111 = 2383667) B2383667
theorem B704391 : Blo 702318 704391 := bstep (se 1 (by rfl) ⟨528293, by rfl⟩ : syracuseStep 704391 = 1056587) B1056587
theorem B704399 : Blo 702318 704399 := bstep (se 1 (by rfl) ⟨528299, by rfl⟩ : syracuseStep 704399 = 1056599) B1056599
theorem B704443 : Blo 702318 704443 := bstep (se 1 (by rfl) ⟨528332, by rfl⟩ : syracuseStep 704443 = 1056665) B1056665
theorem B704519 : Blo 702318 704519 := bstep (se 1 (by rfl) ⟨528389, by rfl⟩ : syracuseStep 704519 = 1056779) B1056779
theorem B704527 : Blo 702318 704527 := bstep (se 1 (by rfl) ⟨528395, by rfl⟩ : syracuseStep 704527 = 1056791) B1056791
theorem B704571 : Blo 702318 704571 := bstep (se 1 (by rfl) ⟨528428, by rfl⟩ : syracuseStep 704571 = 1056857) B1056857
theorem B704647 : Blo 702318 704647 := bstep (se 1 (by rfl) ⟨528485, by rfl⟩ : syracuseStep 704647 = 1056971) B1056971
theorem B704655 : Blo 702318 704655 := bstep (se 1 (by rfl) ⟨528491, by rfl⟩ : syracuseStep 704655 = 1056983) B1056983
theorem B1786009 : Blo 702318 1786009 := bstep (se 2 (by rfl) ⟨669753, by rfl⟩ : syracuseStep 1786009 = 1339507) B1339507
theorem B11452589 : Blo 702318 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B704699 : Blo 702318 704699 := bstep (se 1 (by rfl) ⟨528524, by rfl⟩ : syracuseStep 704699 = 1057049) B1057049
theorem B5488877 : Blo 702318 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B704775 : Blo 702318 704775 := bstep (se 1 (by rfl) ⟨528581, by rfl⟩ : syracuseStep 704775 = 1057163) B1057163
theorem B704783 : Blo 702318 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B704827 : Blo 702318 704827 := bstep (se 1 (by rfl) ⟨528620, by rfl⟩ : syracuseStep 704827 = 1057241) B1057241
theorem B1786171 : Blo 702318 1786171 := bstep (se 1 (by rfl) ⟨1339628, by rfl⟩ : syracuseStep 1786171 = 2679257) B2679257
theorem B1687895 : Blo 702318 1687895 := bstep (se 1 (by rfl) ⟨1265921, by rfl⟩ : syracuseStep 1687895 = 2531843) B2531843
theorem B704903 : Blo 702318 704903 := bstep (se 1 (by rfl) ⟨528677, by rfl⟩ : syracuseStep 704903 = 1057355) B1057355
theorem B704911 : Blo 702318 704911 := bstep (se 1 (by rfl) ⟨528683, by rfl⟩ : syracuseStep 704911 = 1057367) B1057367
theorem B2670995 : Blo 702318 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B3555737 : Blo 702318 3555737 := bstep (se 2 (by rfl) ⟨1333401, by rfl⟩ : syracuseStep 3555737 = 2666803) B2666803
theorem B704955 : Blo 702318 704955 := bstep (se 1 (by rfl) ⟨528716, by rfl⟩ : syracuseStep 704955 = 1057433) B1057433
theorem B1425865 : Blo 702318 1425865 := bstep (se 2 (by rfl) ⟨534699, by rfl⟩ : syracuseStep 1425865 = 1069399) B1069399
theorem B1786313 : Blo 702318 1786313 := bstep (se 2 (by rfl) ⟨669867, by rfl⟩ : syracuseStep 1786313 = 1339735) B1339735
theorem B705031 : Blo 702318 705031 := bstep (se 1 (by rfl) ⟨528773, by rfl⟩ : syracuseStep 705031 = 1057547) B1057547
theorem B705039 : Blo 702318 705039 := bstep (se 1 (by rfl) ⟨528779, by rfl⟩ : syracuseStep 705039 = 1057559) B1057559
theorem B705083 : Blo 702318 705083 := bstep (se 1 (by rfl) ⟨528812, by rfl⟩ : syracuseStep 705083 = 1057625) B1057625
theorem B705159 : Blo 702318 705159 := bstep (se 1 (by rfl) ⟨528869, by rfl⟩ : syracuseStep 705159 = 1057739) B1057739
theorem B705167 : Blo 702318 705167 := bstep (se 1 (by rfl) ⟨528875, by rfl⟩ : syracuseStep 705167 = 1057751) B1057751
theorem B705211 : Blo 702318 705211 := bstep (se 1 (by rfl) ⟨528908, by rfl⟩ : syracuseStep 705211 = 1057817) B1057817
theorem B9126593 : Blo 702318 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B4014785 : Blo 702318 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B1000183 : Blo 702318 1000183 := bstep (se 1 (by rfl) ⟨750137, by rfl⟩ : syracuseStep 1000183 = 1500275) B1500275
theorem B705287 : Blo 702318 705287 := bstep (se 1 (by rfl) ⟨528965, by rfl⟩ : syracuseStep 705287 = 1057931) B1057931
theorem B705295 : Blo 702318 705295 := bstep (se 1 (by rfl) ⟨528971, by rfl⟩ : syracuseStep 705295 = 1057943) B1057943
theorem B1786657 : Blo 702318 1786657 := bstep (se 2 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 1786657 = 1339993) B1339993
theorem B705339 : Blo 702318 705339 := bstep (se 1 (by rfl) ⟨529004, by rfl⟩ : syracuseStep 705339 = 1058009) B1058009
theorem B705415 : Blo 702318 705415 := bstep (se 1 (by rfl) ⟨529061, by rfl⟩ : syracuseStep 705415 = 1058123) B1058123
theorem B705423 : Blo 702318 705423 := bstep (se 1 (by rfl) ⟨529067, by rfl⟩ : syracuseStep 705423 = 1058135) B1058135
theorem B705467 : Blo 702318 705467 := bstep (se 1 (by rfl) ⟨529100, by rfl⟩ : syracuseStep 705467 = 1058201) B1058201
theorem B4178897 : Blo 702318 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B705543 : Blo 702318 705543 := bstep (se 1 (by rfl) ⟨529157, by rfl⟩ : syracuseStep 705543 = 1058315) B1058315
theorem B705551 : Blo 702318 705551 := bstep (se 1 (by rfl) ⟨529163, by rfl⟩ : syracuseStep 705551 = 1058327) B1058327
theorem B1000507 : Blo 702318 1000507 := bstep (se 1 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 1000507 = 1500761) B1500761
theorem B705595 : Blo 702318 705595 := bstep (se 1 (by rfl) ⟨529196, by rfl⟩ : syracuseStep 705595 = 1058393) B1058393
theorem B705671 : Blo 702318 705671 := bstep (se 1 (by rfl) ⟨529253, by rfl⟩ : syracuseStep 705671 = 1058507) B1058507
theorem B705679 : Blo 702318 705679 := bstep (se 1 (by rfl) ⟨529259, by rfl⟩ : syracuseStep 705679 = 1058519) B1058519
theorem B705723 : Blo 702318 705723 := bstep (se 1 (by rfl) ⟨529292, by rfl⟩ : syracuseStep 705723 = 1058585) B1058585
theorem B3392705 : Blo 702318 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B705799 : Blo 702318 705799 := bstep (se 1 (by rfl) ⟨529349, by rfl⟩ : syracuseStep 705799 = 1058699) B1058699
theorem B705807 : Blo 702318 705807 := bstep (se 1 (by rfl) ⟨529355, by rfl⟩ : syracuseStep 705807 = 1058711) B1058711
theorem B705851 : Blo 702318 705851 := bstep (se 1 (by rfl) ⟨529388, by rfl⟩ : syracuseStep 705851 = 1058777) B1058777
theorem B3392857 : Blo 702318 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B1787255 : Blo 702318 1787255 := bstep (se 1 (by rfl) ⟨1340441, by rfl⟩ : syracuseStep 1787255 = 2680883) B2680883
theorem B705927 : Blo 702318 705927 := bstep (se 1 (by rfl) ⟨529445, by rfl⟩ : syracuseStep 705927 = 1058891) B1058891
theorem B705935 : Blo 702318 705935 := bstep (se 1 (by rfl) ⟨529451, by rfl⟩ : syracuseStep 705935 = 1058903) B1058903
theorem B705979 : Blo 702318 705979 := bstep (se 1 (by rfl) ⟨529484, by rfl⟩ : syracuseStep 705979 = 1058969) B1058969
theorem B706055 : Blo 702318 706055 := bstep (se 1 (by rfl) ⟨529541, by rfl⟩ : syracuseStep 706055 = 1059083) B1059083
theorem B706063 : Blo 702318 706063 := bstep (se 1 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 706063 = 1059095) B1059095
theorem B706107 : Blo 702318 706107 := bstep (se 1 (by rfl) ⟨529580, by rfl⟩ : syracuseStep 706107 = 1059161) B1059161
theorem B706183 : Blo 702318 706183 := bstep (se 1 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 706183 = 1059275) B1059275
theorem B706191 : Blo 702318 706191 := bstep (se 1 (by rfl) ⟨529643, by rfl⟩ : syracuseStep 706191 = 1059287) B1059287
theorem B706235 : Blo 702318 706235 := bstep (se 1 (by rfl) ⟨529676, by rfl⟩ : syracuseStep 706235 = 1059353) B1059353
theorem B706311 : Blo 702318 706311 := bstep (se 1 (by rfl) ⟨529733, by rfl⟩ : syracuseStep 706311 = 1059467) B1059467
theorem B1689355 : Blo 702318 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B2377619 : Blo 702318 2377619 := bstep (se 1 (by rfl) ⟨1783214, by rfl⟩ : syracuseStep 2377619 = 3566429) B3566429
theorem B12503285 : Blo 702318 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B5360093 : Blo 702318 5360093 := bstep (se 3 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 5360093 = 2010035) B2010035
theorem B4508227 : Blo 702318 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B1886867 : Blo 702318 1886867 := bstep (se 1 (by rfl) ⟨1415150, by rfl⟩ : syracuseStep 1886867 = 2830301) B2830301
theorem B2542337 : Blo 702318 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B3296015 : Blo 702318 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B3558329 : Blo 702318 3558329 := bstep (se 2 (by rfl) ⟨1334373, by rfl⟩ : syracuseStep 3558329 = 2668747) B2668747
theorem B2673593 : Blo 702318 2673593 := bstep (se 2 (by rfl) ⟨1002597, by rfl⟩ : syracuseStep 2673593 = 2005195) B2005195
theorem B904235 : Blo 702318 904235 := bstep (se 1 (by rfl) ⟨678176, by rfl⟩ : syracuseStep 904235 = 1356353) B1356353
theorem B2379023 : Blo 702318 2379023 := bstep (se 1 (by rfl) ⟨1784267, by rfl⟩ : syracuseStep 2379023 = 3568535) B3568535
theorem B2346355 : Blo 702318 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B1002871 : Blo 702318 1002871 := bstep (se 1 (by rfl) ⟨752153, by rfl⟩ : syracuseStep 1002871 = 1504307) B1504307
theorem B2379293 : Blo 702318 2379293 := bstep (se 3 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 2379293 = 892235) B892235
theorem B13684301 : Blo 702318 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B10145357 : Blo 702318 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B1003195 : Blo 702318 1003195 := bstep (se 1 (by rfl) ⟨752396, by rfl⟩ : syracuseStep 1003195 = 1504793) B1504793
theorem B48680675 : Blo 702318 48680675 := bstep (se 1 (by rfl) ⟨36510506, by rfl⟩ : syracuseStep 48680675 = 73021013) B73021013
theorem B2543375 : Blo 702318 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B2674579 : Blo 702318 2674579 := bstep (se 1 (by rfl) ⟨2005934, by rfl⟩ : syracuseStep 2674579 = 4011869) B4011869
theorem B1003691 : Blo 702318 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B4116653 : Blo 702318 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B3559625 : Blo 702318 3559625 := bstep (se 2 (by rfl) ⟨1334859, by rfl⟩ : syracuseStep 3559625 = 2669719) B2669719
theorem B7622857 : Blo 702318 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B3002683 : Blo 702318 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B2708239 : Blo 702318 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B1692431 : Blo 702318 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B10310435 : Blo 702318 10310435 := bstep (se 1 (by rfl) ⟨7732826, by rfl⟩ : syracuseStep 10310435 = 15465653) B15465653
theorem B4281241 : Blo 702318 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B2380697 : Blo 702318 2380697 := bstep (se 2 (by rfl) ⟨892761, by rfl⟩ : syracuseStep 2380697 = 1785523) B1785523
theorem B1430473 : Blo 702318 1430473 := bstep (se 2 (by rfl) ⟨536427, by rfl⟩ : syracuseStep 1430473 = 1072855) B1072855
theorem B1692731 : Blo 702318 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B1430843 : Blo 702318 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B2676311 : Blo 702318 2676311 := bstep (se 1 (by rfl) ⟨2007233, by rfl⟩ : syracuseStep 2676311 = 4014467) B4014467
theorem B2381399 : Blo 702318 2381399 := bstep (se 1 (by rfl) ⟨1786049, by rfl⟩ : syracuseStep 2381399 = 3572099) B3572099
theorem B1005257 : Blo 702318 1005257 := bstep (se 2 (by rfl) ⟨376971, by rfl⟩ : syracuseStep 1005257 = 753943) B753943
theorem B4118539 : Blo 702318 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B2676797 : Blo 702318 2676797 := bstep (se 3 (by rfl) ⟨501899, by rfl⟩ : syracuseStep 2676797 = 1003799) B1003799
theorem B2381885 : Blo 702318 2381885 := bstep (se 3 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 2381885 = 893207) B893207
theorem B13687339 : Blo 702318 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B5069911 : Blo 702318 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B1694807 : Blo 702318 1694807 := bstep (se 1 (by rfl) ⟨1271105, by rfl⟩ : syracuseStep 1694807 = 2542211) B2542211
theorem B1334647 : Blo 702318 1334647 := bstep (se 1 (by rfl) ⟨1000985, by rfl⟩ : syracuseStep 1334647 = 2001971) B2001971
theorem B3431825 : Blo 702318 3431825 := bstep (se 2 (by rfl) ⟨1286934, by rfl⟩ : syracuseStep 3431825 = 2573869) B2573869
theorem B5561747 : Blo 702318 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B1695161 : Blo 702318 1695161 := bstep (se 2 (by rfl) ⟨635685, by rfl⟩ : syracuseStep 1695161 = 1271371) B1271371
theorem B2383289 : Blo 702318 2383289 := bstep (se 2 (by rfl) ⟨893733, by rfl⟩ : syracuseStep 2383289 = 1787467) B1787467
theorem B2416139 : Blo 702318 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B6020675 : Blo 702318 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B2252603 : Blo 702318 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B4022075 : Blo 702318 4022075 := bstep (se 1 (by rfl) ⟨3016556, by rfl⟩ : syracuseStep 4022075 = 6033113) B6033113
theorem B1695575 : Blo 702318 1695575 := bstep (se 1 (by rfl) ⟨1271681, by rfl⟩ : syracuseStep 1695575 = 2543363) B2543363
theorem B2253089 : Blo 702318 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B1696315 : Blo 702318 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B1696391 : Blo 702318 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B4514561 : Blo 702318 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B5333849 : Blo 702318 5333849 := bstep (se 2 (by rfl) ⟨2000193, by rfl⟩ : syracuseStep 5333849 = 4000387) B4000387
theorem B1336439 : Blo 702318 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B1336591 : Blo 702318 1336591 := bstep (se 1 (by rfl) ⟨1002443, by rfl⟩ : syracuseStep 1336591 = 2004887) B2004887
theorem B16442657 : Blo 702318 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B2680199 : Blo 702318 2680199 := bstep (se 1 (by rfl) ⟨2010149, by rfl⟩ : syracuseStep 2680199 = 4020299) B4020299
theorem B845327 : Blo 702318 845327 := bstep (se 1 (by rfl) ⟨633995, by rfl⟩ : syracuseStep 845327 = 1267991) B1267991
theorem B1336979 : Blo 702318 1336979 := bstep (se 1 (by rfl) ⟨1002734, by rfl⟩ : syracuseStep 1336979 = 2005469) B2005469
theorem B5334821 : Blo 702318 5334821 := bstep (se 4 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 5334821 = 1000279) B1000279
theorem B3565457 : Blo 702318 3565457 := bstep (se 2 (by rfl) ⟨1337046, by rfl⟩ : syracuseStep 3565457 = 2674093) B2674093
theorem B10152053 : Blo 702318 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B5073029 : Blo 702318 5073029 := bstep (se 4 (by rfl) ⟨475596, by rfl⟩ : syracuseStep 5073029 = 951193) B951193
theorem B10316045 : Blo 702318 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B846139 : Blo 702318 846139 := bstep (se 1 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 846139 = 1269209) B1269209
theorem B2255447 : Blo 702318 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B846523 : Blo 702318 846523 := bstep (se 1 (by rfl) ⟨634892, by rfl⟩ : syracuseStep 846523 = 1269785) B1269785
theorem B3009433 : Blo 702318 3009433 := bstep (se 2 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 3009433 = 2257075) B2257075
theorem B8219659 : Blo 702318 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B1338383 : Blo 702318 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B2255959 : Blo 702318 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B6024365 : Blo 702318 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B6778333 : Blo 702318 6778333 := bstep (se 3 (by rfl) ⟨1270937, by rfl⟩ : syracuseStep 6778333 = 2541875) B2541875
theorem B1338923 : Blo 702318 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B15200045 : Blo 702318 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B28897073 : Blo 702318 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B6025049 : Blo 702318 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B3567563 : Blo 702318 3567563 := bstep (se 1 (by rfl) ⟨2675672, by rfl⟩ : syracuseStep 3567563 = 5351345) B5351345
theorem B3010679 : Blo 702318 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B3567887 : Blo 702318 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B11137297 : Blo 702318 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B1503623 : Blo 702318 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B848503 : Blo 702318 848503 := bstep (se 1 (by rfl) ⟨636377, by rfl⟩ : syracuseStep 848503 = 1272755) B1272755
theorem B1340039 : Blo 702318 1340039 := bstep (se 1 (by rfl) ⟨1005029, by rfl⟩ : syracuseStep 1340039 = 2010059) B2010059
theorem B1340563 : Blo 702318 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B1504811 : Blo 702318 1504811 := bstep (se 1 (by rfl) ⟨1128608, by rfl⟩ : syracuseStep 1504811 = 2257217) B2257217
theorem B3569345 : Blo 702318 3569345 := bstep (se 2 (by rfl) ⟨1338504, by rfl⟩ : syracuseStep 3569345 = 2677009) B2677009
theorem B4290583 : Blo 702318 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B751675 : Blo 702318 751675 := bstep (se 1 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 751675 = 1127513) B1127513
theorem B4061441 : Blo 702318 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B2849039 : Blo 702318 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B8550803 : Blo 702318 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B15464945 : Blo 702318 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B2062967 : Blo 702318 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B3570641 : Blo 702318 3570641 := bstep (se 2 (by rfl) ⟨1338990, by rfl⟩ : syracuseStep 3570641 = 2677981) B2677981
theorem B1014799 : Blo 702318 1014799 := bstep (se 1 (by rfl) ⟨761099, by rfl⟩ : syracuseStep 1014799 = 1522199) B1522199
theorem B1506451 : Blo 702318 1506451 := bstep (se 1 (by rfl) ⟨1129838, by rfl⟩ : syracuseStep 1506451 = 2259677) B2259677
theorem B1604809 : Blo 702318 1604809 := bstep (se 2 (by rfl) ⟨601803, by rfl⟩ : syracuseStep 1604809 = 1203607) B1203607
theorem B4521197 : Blo 702318 4521197 := bstep (se 3 (by rfl) ⟨847724, by rfl⟩ : syracuseStep 4521197 = 1695449) B1695449
theorem B1899911 : Blo 702318 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B1900093 : Blo 702318 1900093 := bstep (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) B712535
theorem B14450501 : Blo 702318 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B1605577 : Blo 702318 1605577 := bstep (se 2 (by rfl) ⟨602091, by rfl⟩ : syracuseStep 1605577 = 1204183) B1204183
theorem B7635059 : Blo 702318 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B1901153 : Blo 702318 1901153 := bstep (se 2 (by rfl) ⟨712932, by rfl⟩ : syracuseStep 1901153 = 1425865) B1425865
theorem B2785931 : Blo 702318 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B2261753 : Blo 702318 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B2261803 : Blo 702318 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B3016079 : Blo 702318 3016079 := bstep (se 1 (by rfl) ⟨2262059, by rfl⟩ : syracuseStep 3016079 = 4524119) B4524119
theorem B1443347 : Blo 702318 1443347 := bstep (se 1 (by rfl) ⟨1082510, by rfl⟩ : syracuseStep 1443347 = 2165021) B2165021
theorem B3573395 : Blo 702318 3573395 := bstep (se 1 (by rfl) ⟨2680046, by rfl⟩ : syracuseStep 3573395 = 5360093) B5360093
theorem B2197343 : Blo 702318 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B6031199 : Blo 702318 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B1017865 : Blo 702318 1017865 := bstep (se 2 (by rfl) ⟨381699, by rfl⟩ : syracuseStep 1017865 = 763399) B763399
theorem B3214583 : Blo 702318 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B790447 : Blo 702318 790447 := bstep (se 1 (by rfl) ⟨592835, by rfl⟩ : syracuseStep 790447 = 1185671) B1185671
theorem B21958771 : Blo 702318 21958771 := bstep (se 1 (by rfl) ⟨16469078, by rfl⟩ : syracuseStep 21958771 = 32938157) B32938157
theorem B790879 : Blo 702318 790879 := bstep (se 1 (by rfl) ⟨593159, by rfl⟩ : syracuseStep 790879 = 1186319) B1186319
theorem B791239 : Blo 702318 791239 := bstep (se 1 (by rfl) ⟨593429, by rfl⟩ : syracuseStep 791239 = 1186859) B1186859
theorem B1053545 : Blo 702318 1053545 := bstep (se 2 (by rfl) ⟨395079, by rfl⟩ : syracuseStep 1053545 = 790159) B790159
theorem B1053623 : Blo 702318 1053623 := bstep (se 1 (by rfl) ⟨790217, by rfl⟩ : syracuseStep 1053623 = 1580435) B1580435
theorem B3707831 : Blo 702318 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B1053659 : Blo 702318 1053659 := bstep (se 1 (by rfl) ⟨790244, by rfl⟩ : syracuseStep 1053659 = 1580489) B1580489
theorem B1610759 : Blo 702318 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B9049259 : Blo 702318 9049259 := bstep (se 1 (by rfl) ⟨6786944, by rfl⟩ : syracuseStep 9049259 = 13573889) B13573889
theorem B1054127 : Blo 702318 1054127 := bstep (se 1 (by rfl) ⟨790595, by rfl⟩ : syracuseStep 1054127 = 1581191) B1581191
theorem B1054217 : Blo 702318 1054217 := bstep (se 2 (by rfl) ⟨395331, by rfl⟩ : syracuseStep 1054217 = 790663) B790663
theorem B1054247 : Blo 702318 1054247 := bstep (se 1 (by rfl) ⟨790685, by rfl⟩ : syracuseStep 1054247 = 1581371) B1581371
theorem B792103 : Blo 702318 792103 := bstep (se 1 (by rfl) ⟨594077, by rfl⟩ : syracuseStep 792103 = 1188155) B1188155
theorem B3806759 : Blo 702318 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B10163809 : Blo 702318 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B1054331 : Blo 702318 1054331 := bstep (se 1 (by rfl) ⟨790748, by rfl⟩ : syracuseStep 1054331 = 1581497) B1581497
theorem B14849729 : Blo 702318 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B1185529 : Blo 702318 1185529 := bstep (se 2 (by rfl) ⟨444573, by rfl⟩ : syracuseStep 1185529 = 889147) B889147
theorem B4003577 : Blo 702318 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B1054457 : Blo 702318 1054457 := bstep (se 2 (by rfl) ⟨395421, by rfl⟩ : syracuseStep 1054457 = 790843) B790843
theorem B9148153 : Blo 702318 9148153 := bstep (se 2 (by rfl) ⟨3430557, by rfl⟩ : syracuseStep 9148153 = 6861115) B6861115
theorem B1054559 : Blo 702318 1054559 := bstep (se 1 (by rfl) ⟨790919, by rfl⟩ : syracuseStep 1054559 = 1581839) B1581839
theorem B1054571 : Blo 702318 1054571 := bstep (se 1 (by rfl) ⟨790928, by rfl⟩ : syracuseStep 1054571 = 1581857) B1581857
theorem B1185799 : Blo 702318 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1054799 : Blo 702318 1054799 := bstep (se 1 (by rfl) ⟨791099, by rfl⟩ : syracuseStep 1054799 = 1582199) B1582199
theorem B1054919 : Blo 702318 1054919 := bstep (se 1 (by rfl) ⟨791189, by rfl⟩ : syracuseStep 1054919 = 1582379) B1582379
theorem B1055081 : Blo 702318 1055081 := bstep (se 2 (by rfl) ⟨395655, by rfl⟩ : syracuseStep 1055081 = 791311) B791311
theorem B3610985 : Blo 702318 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B1186231 : Blo 702318 1186231 := bstep (se 1 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 1186231 = 1779347) B1779347
theorem B1055159 : Blo 702318 1055159 := bstep (se 1 (by rfl) ⟨791369, by rfl⟩ : syracuseStep 1055159 = 1582739) B1582739
theorem B891319 : Blo 702318 891319 := bstep (se 1 (by rfl) ⟨668489, by rfl⟩ : syracuseStep 891319 = 1336979) B1336979
theorem B1055195 : Blo 702318 1055195 := bstep (se 1 (by rfl) ⟨791396, by rfl⟩ : syracuseStep 1055195 = 1582793) B1582793
theorem B5708321 : Blo 702318 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B1907297 : Blo 702318 1907297 := bstep (se 2 (by rfl) ⟨715236, by rfl⟩ : syracuseStep 1907297 = 1430473) B1430473
theorem B1186427 : Blo 702318 1186427 := bstep (se 1 (by rfl) ⟨889820, by rfl⟩ : syracuseStep 1186427 = 1779641) B1779641
theorem B3382019 : Blo 702318 3382019 := bstep (se 1 (by rfl) ⟨2536514, by rfl⟩ : syracuseStep 3382019 = 5073029) B5073029
theorem B1055663 : Blo 702318 1055663 := bstep (se 1 (by rfl) ⟨791747, by rfl⟩ : syracuseStep 1055663 = 1583495) B1583495
theorem B3218359 : Blo 702318 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B1186825 : Blo 702318 1186825 := bstep (se 2 (by rfl) ⟨445059, by rfl⟩ : syracuseStep 1186825 = 890119) B890119
theorem B1055753 : Blo 702318 1055753 := bstep (se 2 (by rfl) ⟨395907, by rfl⟩ : syracuseStep 1055753 = 791815) B791815
theorem B1055783 : Blo 702318 1055783 := bstep (se 1 (by rfl) ⟨791837, by rfl⟩ : syracuseStep 1055783 = 1583675) B1583675
theorem B1055867 : Blo 702318 1055867 := bstep (se 1 (by rfl) ⟨791900, by rfl⟩ : syracuseStep 1055867 = 1583801) B1583801
theorem B793723 : Blo 702318 793723 := bstep (se 1 (by rfl) ⟨595292, by rfl⟩ : syracuseStep 793723 = 1190585) B1190585
theorem B18095237 : Blo 702318 18095237 := bstep (se 4 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 18095237 = 3392857) B3392857
theorem B4005035 : Blo 702318 4005035 := bstep (se 1 (by rfl) ⟨3003776, by rfl⟩ : syracuseStep 4005035 = 6007553) B6007553
theorem B1186987 : Blo 702318 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B1055993 : Blo 702318 1055993 := bstep (se 2 (by rfl) ⟨395997, by rfl⟩ : syracuseStep 1055993 = 791995) B791995
theorem B1056095 : Blo 702318 1056095 := bstep (se 1 (by rfl) ⟨792071, by rfl⟩ : syracuseStep 1056095 = 1584143) B1584143
theorem B1056107 : Blo 702318 1056107 := bstep (se 1 (by rfl) ⟨792080, by rfl⟩ : syracuseStep 1056107 = 1584161) B1584161
theorem B43326899 : Blo 702318 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B4070857 : Blo 702318 4070857 := bstep (se 2 (by rfl) ⟨1526571, by rfl⟩ : syracuseStep 4070857 = 3053143) B3053143
theorem B1580507 : Blo 702318 1580507 := bstep (se 1 (by rfl) ⟨1185380, by rfl⟩ : syracuseStep 1580507 = 2370761) B2370761
theorem B1187291 : Blo 702318 1187291 := bstep (se 1 (by rfl) ⟨890468, by rfl⟩ : syracuseStep 1187291 = 1780937) B1780937
theorem B1056335 : Blo 702318 1056335 := bstep (se 1 (by rfl) ⟨792251, by rfl⟩ : syracuseStep 1056335 = 1584503) B1584503
theorem B794191 : Blo 702318 794191 := bstep (se 1 (by rfl) ⟨595643, by rfl⟩ : syracuseStep 794191 = 1191287) B1191287
theorem B1187527 : Blo 702318 1187527 := bstep (se 1 (by rfl) ⟨890645, by rfl⟩ : syracuseStep 1187527 = 1781291) B1781291
theorem B1056455 : Blo 702318 1056455 := bstep (se 1 (by rfl) ⟨792341, by rfl⟩ : syracuseStep 1056455 = 1584683) B1584683
theorem B892615 : Blo 702318 892615 := bstep (se 1 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 892615 = 1338923) B1338923
theorem B1187689 : Blo 702318 1187689 := bstep (se 2 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 1187689 = 890767) B890767
theorem B1056617 : Blo 702318 1056617 := bstep (se 2 (by rfl) ⟨396231, by rfl⟩ : syracuseStep 1056617 = 792463) B792463
theorem B10133363 : Blo 702318 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B1580975 : Blo 702318 1580975 := bstep (se 1 (by rfl) ⟨1185731, by rfl⟩ : syracuseStep 1580975 = 2371463) B2371463
theorem B1056695 : Blo 702318 1056695 := bstep (se 1 (by rfl) ⟨792521, by rfl⟩ : syracuseStep 1056695 = 1585043) B1585043
theorem B1056731 : Blo 702318 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B794587 : Blo 702318 794587 := bstep (se 1 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 794587 = 1191881) B1191881
theorem B2007119 : Blo 702318 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B1581227 : Blo 702318 1581227 := bstep (se 1 (by rfl) ⟨1185920, by rfl⟩ : syracuseStep 1581227 = 2371841) B2371841
theorem B1057199 : Blo 702318 1057199 := bstep (se 1 (by rfl) ⟨792899, by rfl⟩ : syracuseStep 1057199 = 1585799) B1585799
theorem B893359 : Blo 702318 893359 := bstep (se 1 (by rfl) ⟨670019, by rfl⟩ : syracuseStep 893359 = 1340039) B1340039
theorem B1188283 : Blo 702318 1188283 := bstep (se 1 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 1188283 = 1782425) B1782425
theorem B1057289 : Blo 702318 1057289 := bstep (se 2 (by rfl) ⟨396483, by rfl⟩ : syracuseStep 1057289 = 792967) B792967
theorem B1188391 : Blo 702318 1188391 := bstep (se 1 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 1188391 = 1782587) B1782587
theorem B1057319 : Blo 702318 1057319 := bstep (se 1 (by rfl) ⟨792989, by rfl⟩ : syracuseStep 1057319 = 1585979) B1585979
theorem B1057403 : Blo 702318 1057403 := bstep (se 1 (by rfl) ⟨793052, by rfl⟩ : syracuseStep 1057403 = 1586105) B1586105
theorem B1778375 : Blo 702318 1778375 := bstep (se 1 (by rfl) ⟨1333781, by rfl⟩ : syracuseStep 1778375 = 2667563) B2667563
theorem B1581767 : Blo 702318 1581767 := bstep (se 1 (by rfl) ⟨1186325, by rfl⟩ : syracuseStep 1581767 = 2372651) B2372651
theorem B1057529 : Blo 702318 1057529 := bstep (se 2 (by rfl) ⟨396573, by rfl⟩ : syracuseStep 1057529 = 793147) B793147
theorem B1057631 : Blo 702318 1057631 := bstep (se 1 (by rfl) ⟨793223, by rfl⟩ : syracuseStep 1057631 = 1586447) B1586447
theorem B1188715 : Blo 702318 1188715 := bstep (se 1 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 1188715 = 1783073) B1783073
theorem B1057643 : Blo 702318 1057643 := bstep (se 1 (by rfl) ⟨793232, by rfl⟩ : syracuseStep 1057643 = 1586465) B1586465
theorem B5350373 : Blo 702318 5350373 := bstep (se 4 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 5350373 = 1003195) B1003195
theorem B5710915 : Blo 702318 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B1057871 : Blo 702318 1057871 := bstep (se 1 (by rfl) ⟨793403, by rfl⟩ : syracuseStep 1057871 = 1586807) B1586807
theorem B4826305 : Blo 702318 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1057991 : Blo 702318 1057991 := bstep (se 1 (by rfl) ⟨793493, by rfl⟩ : syracuseStep 1057991 = 1586987) B1586987
theorem B1058153 : Blo 702318 1058153 := bstep (se 2 (by rfl) ⟨396807, by rfl⟩ : syracuseStep 1058153 = 793615) B793615
theorem B1058231 : Blo 702318 1058231 := bstep (se 1 (by rfl) ⟨793673, by rfl⟩ : syracuseStep 1058231 = 1587347) B1587347
theorem B6759881 : Blo 702318 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B1058267 : Blo 702318 1058267 := bstep (se 1 (by rfl) ⟨793700, by rfl⟩ : syracuseStep 1058267 = 1587401) B1587401
theorem B2008601 : Blo 702318 2008601 := bstep (se 2 (by rfl) ⟨753225, by rfl⟩ : syracuseStep 2008601 = 1506451) B1506451
theorem B1582631 : Blo 702318 1582631 := bstep (se 1 (by rfl) ⟨1186973, by rfl⟩ : syracuseStep 1582631 = 2373947) B2373947
theorem B2139745 : Blo 702318 2139745 := bstep (se 2 (by rfl) ⟨802404, by rfl⟩ : syracuseStep 2139745 = 1604809) B1604809
theorem B1779529 : Blo 702318 1779529 := bstep (se 2 (by rfl) ⟨667323, by rfl⟩ : syracuseStep 1779529 = 1334647) B1334647
theorem B1582955 : Blo 702318 1582955 := bstep (se 1 (by rfl) ⟨1187216, by rfl⟩ : syracuseStep 1582955 = 2374433) B2374433
theorem B1189775 : Blo 702318 1189775 := bstep (se 1 (by rfl) ⟨892331, by rfl⟩ : syracuseStep 1189775 = 1784663) B1784663
theorem B1583009 : Blo 702318 1583009 := bstep (se 2 (by rfl) ⟨593628, by rfl⟩ : syracuseStep 1583009 = 1187257) B1187257
theorem B1058735 : Blo 702318 1058735 := bstep (se 1 (by rfl) ⟨794051, by rfl⟩ : syracuseStep 1058735 = 1588103) B1588103
theorem B1058825 : Blo 702318 1058825 := bstep (se 2 (by rfl) ⟨397059, by rfl⟩ : syracuseStep 1058825 = 794119) B794119
theorem B4007951 : Blo 702318 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B1058855 : Blo 702318 1058855 := bstep (se 1 (by rfl) ⟨794141, by rfl⟩ : syracuseStep 1058855 = 1588283) B1588283
theorem B2533457 : Blo 702318 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B1190011 : Blo 702318 1190011 := bstep (se 1 (by rfl) ⟨892508, by rfl⟩ : syracuseStep 1190011 = 1785017) B1785017
theorem B1058939 : Blo 702318 1058939 := bstep (se 1 (by rfl) ⟨794204, by rfl⟩ : syracuseStep 1058939 = 1588409) B1588409
theorem B1583351 : Blo 702318 1583351 := bstep (se 1 (by rfl) ⟨1187513, by rfl⟩ : syracuseStep 1583351 = 2375027) B2375027
theorem B1059065 : Blo 702318 1059065 := bstep (se 2 (by rfl) ⟨397149, by rfl⟩ : syracuseStep 1059065 = 794299) B794299
theorem B4008203 : Blo 702318 4008203 := bstep (se 1 (by rfl) ⟨3006152, by rfl⟩ : syracuseStep 4008203 = 6012305) B6012305
theorem B1059167 : Blo 702318 1059167 := bstep (se 1 (by rfl) ⟨794375, by rfl⟩ : syracuseStep 1059167 = 1588751) B1588751
theorem B1059179 : Blo 702318 1059179 := bstep (se 1 (by rfl) ⟨794384, by rfl⟩ : syracuseStep 1059179 = 1588769) B1588769
theorem B1059407 : Blo 702318 1059407 := bstep (se 1 (by rfl) ⟨794555, by rfl⟩ : syracuseStep 1059407 = 1589111) B1589111
theorem B2140769 : Blo 702318 2140769 := bstep (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) B1605577
theorem B1583945 : Blo 702318 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B1125263 : Blo 702318 1125263 := bstep (se 1 (by rfl) ⟨843947, by rfl⟩ : syracuseStep 1125263 = 1687895) B1687895
theorem B1780663 : Blo 702318 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B2370491 : Blo 702318 2370491 := bstep (se 1 (by rfl) ⟨1777868, by rfl⟩ : syracuseStep 2370491 = 3555737) B3555737
theorem B1190875 : Blo 702318 1190875 := bstep (se 1 (by rfl) ⟨893156, by rfl⟩ : syracuseStep 1190875 = 1786313) B1786313
theorem B3386843 : Blo 702318 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B9023015 : Blo 702318 9023015 := bstep (se 1 (by rfl) ⟨6767261, by rfl⟩ : syracuseStep 9023015 = 13534523) B13534523
theorem B1191503 : Blo 702318 1191503 := bstep (se 1 (by rfl) ⟨893627, by rfl⟩ : syracuseStep 1191503 = 1787255) B1787255
theorem B1584737 : Blo 702318 1584737 := bstep (se 2 (by rfl) ⟨594276, by rfl⟩ : syracuseStep 1584737 = 1188553) B1188553
theorem B4009661 : Blo 702318 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B5091131 : Blo 702318 5091131 := bstep (se 1 (by rfl) ⟨3818348, by rfl⟩ : syracuseStep 5091131 = 7636697) B7636697
theorem B1585079 : Blo 702318 1585079 := bstep (se 1 (by rfl) ⟨1188809, by rfl⟩ : syracuseStep 1585079 = 2377619) B2377619
theorem B1355815 : Blo 702318 1355815 := bstep (se 1 (by rfl) ⟨1016861, by rfl⟩ : syracuseStep 1355815 = 2033723) B2033723
theorem B58470493 : Blo 702318 58470493 := bstep (se 3 (by rfl) ⟨10963217, by rfl⟩ : syracuseStep 58470493 = 21926435) B21926435
theorem B8335523 : Blo 702318 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B1782121 : Blo 702318 1782121 := bstep (se 2 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 1782121 = 1336591) B1336591
theorem B1257911 : Blo 702318 1257911 := bstep (se 1 (by rfl) ⟨943433, by rfl⟩ : syracuseStep 1257911 = 1886867) B1886867
theorem B1585673 : Blo 702318 1585673 := bstep (se 2 (by rfl) ⟨594627, by rfl⟩ : syracuseStep 1585673 = 1189255) B1189255
theorem B2372219 : Blo 702318 2372219 := bstep (se 1 (by rfl) ⟨1779164, by rfl⟩ : syracuseStep 2372219 = 3558329) B3558329
theorem B1782395 : Blo 702318 1782395 := bstep (se 1 (by rfl) ⟨1336796, by rfl⟩ : syracuseStep 1782395 = 2673593) B2673593
theorem B10138385 : Blo 702318 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B2372381 : Blo 702318 2372381 := bstep (se 3 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 2372381 = 889643) B889643
theorem B1586015 : Blo 702318 1586015 := bstep (se 1 (by rfl) ⟨1189511, by rfl⟩ : syracuseStep 1586015 = 2379023) B2379023
theorem B1586195 : Blo 702318 1586195 := bstep (se 1 (by rfl) ⟨1189646, by rfl⟩ : syracuseStep 1586195 = 2379293) B2379293
theorem B9122867 : Blo 702318 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B6763571 : Blo 702318 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B32453783 : Blo 702318 32453783 := bstep (se 1 (by rfl) ⟨24340337, by rfl⟩ : syracuseStep 32453783 = 48680675) B48680675
theorem B2536715 : Blo 702318 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B1586537 : Blo 702318 1586537 := bstep (se 2 (by rfl) ⟨594951, by rfl⟩ : syracuseStep 1586537 = 1189903) B1189903
theorem B2373083 : Blo 702318 2373083 := bstep (se 1 (by rfl) ⟨1779812, by rfl⟩ : syracuseStep 2373083 = 3559625) B3559625
theorem B2668247 : Blo 702318 2668247 := bstep (se 1 (by rfl) ⟨2001185, by rfl⟩ : syracuseStep 2668247 = 4002371) B4002371
theorem B1128185 : Blo 702318 1128185 := bstep (se 2 (by rfl) ⟨423069, by rfl⟩ : syracuseStep 1128185 = 846139) B846139
theorem B1128287 : Blo 702318 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B3389303 : Blo 702318 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B702331 : Blo 702318 702331 := bstep (se 1 (by rfl) ⟨526748, by rfl⟩ : syracuseStep 702331 = 1053497) B1053497
theorem B702383 : Blo 702318 702383 := bstep (se 1 (by rfl) ⟨526787, by rfl⟩ : syracuseStep 702383 = 1053575) B1053575
theorem B1587131 : Blo 702318 1587131 := bstep (se 1 (by rfl) ⟨1190348, by rfl⟩ : syracuseStep 1587131 = 2380697) B2380697
theorem B702407 : Blo 702318 702407 := bstep (se 1 (by rfl) ⟨526805, by rfl⟩ : syracuseStep 702407 = 1053611) B1053611
theorem B702427 : Blo 702318 702427 := bstep (se 1 (by rfl) ⟨526820, by rfl⟩ : syracuseStep 702427 = 1053641) B1053641
theorem B702503 : Blo 702318 702503 := bstep (se 1 (by rfl) ⟨526877, by rfl⟩ : syracuseStep 702503 = 1053755) B1053755
theorem B1128487 : Blo 702318 1128487 := bstep (se 1 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 1128487 = 1692731) B1692731
theorem B1587257 : Blo 702318 1587257 := bstep (se 2 (by rfl) ⟨595221, by rfl⟩ : syracuseStep 1587257 = 1190443) B1190443
theorem B702543 : Blo 702318 702543 := bstep (se 1 (by rfl) ⟨526907, by rfl⟩ : syracuseStep 702543 = 1053815) B1053815
theorem B6010969 : Blo 702318 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B702559 : Blo 702318 702559 := bstep (se 1 (by rfl) ⟨526919, by rfl⟩ : syracuseStep 702559 = 1053839) B1053839
theorem B702587 : Blo 702318 702587 := bstep (se 1 (by rfl) ⟨526940, by rfl⟩ : syracuseStep 702587 = 1053881) B1053881
theorem B2373785 : Blo 702318 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B3815581 : Blo 702318 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B702639 : Blo 702318 702639 := bstep (se 1 (by rfl) ⟨526979, by rfl⟩ : syracuseStep 702639 = 1053959) B1053959
theorem B702663 : Blo 702318 702663 := bstep (se 1 (by rfl) ⟨526997, by rfl⟩ : syracuseStep 702663 = 1053995) B1053995
theorem B702683 : Blo 702318 702683 := bstep (se 1 (by rfl) ⟨527012, by rfl⟩ : syracuseStep 702683 = 1054025) B1054025
theorem B1128697 : Blo 702318 1128697 := bstep (se 2 (by rfl) ⟨423261, by rfl⟩ : syracuseStep 1128697 = 846523) B846523
theorem B702759 : Blo 702318 702759 := bstep (se 1 (by rfl) ⟨527069, by rfl⟩ : syracuseStep 702759 = 1054139) B1054139
theorem B702799 : Blo 702318 702799 := bstep (se 1 (by rfl) ⟨527099, by rfl⟩ : syracuseStep 702799 = 1054199) B1054199
theorem B702815 : Blo 702318 702815 := bstep (se 1 (by rfl) ⟨527111, by rfl⟩ : syracuseStep 702815 = 1054223) B1054223
theorem B702843 : Blo 702318 702843 := bstep (se 1 (by rfl) ⟨527132, by rfl⟩ : syracuseStep 702843 = 1054265) B1054265
theorem B1784207 : Blo 702318 1784207 := bstep (se 1 (by rfl) ⟨1338155, by rfl⟩ : syracuseStep 1784207 = 2676311) B2676311
theorem B1587599 : Blo 702318 1587599 := bstep (se 1 (by rfl) ⟨1190699, by rfl⟩ : syracuseStep 1587599 = 2381399) B2381399
theorem B702895 : Blo 702318 702895 := bstep (se 1 (by rfl) ⟨527171, by rfl⟩ : syracuseStep 702895 = 1054343) B1054343
theorem B702919 : Blo 702318 702919 := bstep (se 1 (by rfl) ⟨527189, by rfl⟩ : syracuseStep 702919 = 1054379) B1054379
theorem B702939 : Blo 702318 702939 := bstep (se 1 (by rfl) ⟨527204, by rfl⟩ : syracuseStep 702939 = 1054409) B1054409
theorem B4012577 : Blo 702318 4012577 := bstep (se 2 (by rfl) ⟨1504716, by rfl⟩ : syracuseStep 4012577 = 3009433) B3009433
theorem B703015 : Blo 702318 703015 := bstep (se 1 (by rfl) ⟨527261, by rfl⟩ : syracuseStep 703015 = 1054523) B1054523
theorem B703055 : Blo 702318 703055 := bstep (se 1 (by rfl) ⟨527291, by rfl⟩ : syracuseStep 703055 = 1054583) B1054583
theorem B703071 : Blo 702318 703071 := bstep (se 1 (by rfl) ⟨527303, by rfl⟩ : syracuseStep 703071 = 1054607) B1054607
theorem B703099 : Blo 702318 703099 := bstep (se 1 (by rfl) ⟨527324, by rfl⟩ : syracuseStep 703099 = 1054649) B1054649
theorem B3717767 : Blo 702318 3717767 := bstep (se 1 (by rfl) ⟨2788325, by rfl⟩ : syracuseStep 3717767 = 5576651) B5576651
theorem B5356205 : Blo 702318 5356205 := bstep (se 3 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 5356205 = 2008577) B2008577
theorem B703151 : Blo 702318 703151 := bstep (se 1 (by rfl) ⟨527363, by rfl⟩ : syracuseStep 703151 = 1054727) B1054727
theorem B10959545 : Blo 702318 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B703175 : Blo 702318 703175 := bstep (se 1 (by rfl) ⟨527381, by rfl⟩ : syracuseStep 703175 = 1054763) B1054763
theorem B1784531 : Blo 702318 1784531 := bstep (se 1 (by rfl) ⟨1338398, by rfl⟩ : syracuseStep 1784531 = 2676797) B2676797
theorem B1587923 : Blo 702318 1587923 := bstep (se 1 (by rfl) ⟨1190942, by rfl⟩ : syracuseStep 1587923 = 2381885) B2381885
theorem B703195 : Blo 702318 703195 := bstep (se 1 (by rfl) ⟨527396, by rfl⟩ : syracuseStep 703195 = 1054793) B1054793
theorem B9616157 : Blo 702318 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B703271 : Blo 702318 703271 := bstep (se 1 (by rfl) ⟨527453, by rfl⟩ : syracuseStep 703271 = 1054907) B1054907
theorem B703311 : Blo 702318 703311 := bstep (se 1 (by rfl) ⟨527483, by rfl⟩ : syracuseStep 703311 = 1054967) B1054967
theorem B703327 : Blo 702318 703327 := bstep (se 1 (by rfl) ⟨527495, by rfl⟩ : syracuseStep 703327 = 1054991) B1054991
theorem B703355 : Blo 702318 703355 := bstep (se 1 (by rfl) ⟨527516, by rfl⟩ : syracuseStep 703355 = 1055033) B1055033
theorem B703407 : Blo 702318 703407 := bstep (se 1 (by rfl) ⟨527555, by rfl⟩ : syracuseStep 703407 = 1055111) B1055111
theorem B703431 : Blo 702318 703431 := bstep (se 1 (by rfl) ⟨527573, by rfl⟩ : syracuseStep 703431 = 1055147) B1055147
theorem B703451 : Blo 702318 703451 := bstep (se 1 (by rfl) ⟨527588, by rfl⟩ : syracuseStep 703451 = 1055177) B1055177
theorem B703527 : Blo 702318 703527 := bstep (se 1 (by rfl) ⟨527645, by rfl⟩ : syracuseStep 703527 = 1055291) B1055291
theorem B703567 : Blo 702318 703567 := bstep (se 1 (by rfl) ⟨527675, by rfl⟩ : syracuseStep 703567 = 1055351) B1055351
theorem B703583 : Blo 702318 703583 := bstep (se 1 (by rfl) ⟨527687, by rfl⟩ : syracuseStep 703583 = 1055375) B1055375
theorem B703611 : Blo 702318 703611 := bstep (se 1 (by rfl) ⟨527708, by rfl⟩ : syracuseStep 703611 = 1055417) B1055417
theorem B3128473 : Blo 702318 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B703663 : Blo 702318 703663 := bstep (se 1 (by rfl) ⟨527747, by rfl⟩ : syracuseStep 703663 = 1055495) B1055495
theorem B703687 : Blo 702318 703687 := bstep (se 1 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 703687 = 1055531) B1055531
theorem B703707 : Blo 702318 703707 := bstep (se 1 (by rfl) ⟨527780, by rfl⟩ : syracuseStep 703707 = 1055561) B1055561
theorem B703783 : Blo 702318 703783 := bstep (se 1 (by rfl) ⟨527837, by rfl⟩ : syracuseStep 703783 = 1055675) B1055675
theorem B2374973 : Blo 702318 2374973 := bstep (se 3 (by rfl) ⟨445307, by rfl⟩ : syracuseStep 2374973 = 890615) B890615
theorem B703823 : Blo 702318 703823 := bstep (se 1 (by rfl) ⟨527867, by rfl⟩ : syracuseStep 703823 = 1055735) B1055735
theorem B703839 : Blo 702318 703839 := bstep (se 1 (by rfl) ⟨527879, by rfl⟩ : syracuseStep 703839 = 1055759) B1055759
theorem B703867 : Blo 702318 703867 := bstep (se 1 (by rfl) ⟨527900, by rfl⟩ : syracuseStep 703867 = 1055801) B1055801
theorem B2538877 : Blo 702318 2538877 := bstep (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) B952079
theorem B1129871 : Blo 702318 1129871 := bstep (se 1 (by rfl) ⟨847403, by rfl⟩ : syracuseStep 1129871 = 1694807) B1694807
theorem B703919 : Blo 702318 703919 := bstep (se 1 (by rfl) ⟨527939, by rfl⟩ : syracuseStep 703919 = 1055879) B1055879
theorem B1424827 : Blo 702318 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B703943 : Blo 702318 703943 := bstep (se 1 (by rfl) ⟨527957, by rfl⟩ : syracuseStep 703943 = 1055915) B1055915
theorem B703963 : Blo 702318 703963 := bstep (se 1 (by rfl) ⟨527972, by rfl⟩ : syracuseStep 703963 = 1055945) B1055945
theorem B704039 : Blo 702318 704039 := bstep (se 1 (by rfl) ⟨528029, by rfl⟩ : syracuseStep 704039 = 1056059) B1056059
theorem B704079 : Blo 702318 704079 := bstep (se 1 (by rfl) ⟨528059, by rfl⟩ : syracuseStep 704079 = 1056119) B1056119
theorem B704095 : Blo 702318 704095 := bstep (se 1 (by rfl) ⟨528071, by rfl⟩ : syracuseStep 704095 = 1056143) B1056143
theorem B704123 : Blo 702318 704123 := bstep (se 1 (by rfl) ⟨528092, by rfl⟩ : syracuseStep 704123 = 1056185) B1056185
theorem B1130107 : Blo 702318 1130107 := bstep (se 1 (by rfl) ⟨847580, by rfl⟩ : syracuseStep 1130107 = 1695161) B1695161
theorem B1588859 : Blo 702318 1588859 := bstep (se 1 (by rfl) ⟨1191644, by rfl⟩ : syracuseStep 1588859 = 2383289) B2383289
theorem B704175 : Blo 702318 704175 := bstep (se 1 (by rfl) ⟨528131, by rfl⟩ : syracuseStep 704175 = 1056263) B1056263
theorem B704199 : Blo 702318 704199 := bstep (se 1 (by rfl) ⟨528149, by rfl⟩ : syracuseStep 704199 = 1056299) B1056299
theorem B4013783 : Blo 702318 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B704219 : Blo 702318 704219 := bstep (se 1 (by rfl) ⟨528164, by rfl⟩ : syracuseStep 704219 = 1056329) B1056329
theorem B1588985 : Blo 702318 1588985 := bstep (se 2 (by rfl) ⟨595869, by rfl⟩ : syracuseStep 1588985 = 1191739) B1191739
theorem B704295 : Blo 702318 704295 := bstep (se 1 (by rfl) ⟨528221, by rfl⟩ : syracuseStep 704295 = 1056443) B1056443
theorem B704335 : Blo 702318 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B704351 : Blo 702318 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B704379 : Blo 702318 704379 := bstep (se 1 (by rfl) ⟨528284, by rfl⟩ : syracuseStep 704379 = 1056569) B1056569
theorem B1130383 : Blo 702318 1130383 := bstep (se 1 (by rfl) ⟨847787, by rfl⟩ : syracuseStep 1130383 = 1695575) B1695575
theorem B704431 : Blo 702318 704431 := bstep (se 1 (by rfl) ⟨528323, by rfl⟩ : syracuseStep 704431 = 1056647) B1056647
theorem B704455 : Blo 702318 704455 := bstep (se 1 (by rfl) ⟨528341, by rfl⟩ : syracuseStep 704455 = 1056683) B1056683
theorem B704475 : Blo 702318 704475 := bstep (se 1 (by rfl) ⟨528356, by rfl⟩ : syracuseStep 704475 = 1056713) B1056713
theorem B4505615 : Blo 702318 4505615 := bstep (se 1 (by rfl) ⟨3379211, by rfl⟩ : syracuseStep 4505615 = 6758423) B6758423
theorem B704551 : Blo 702318 704551 := bstep (se 1 (by rfl) ⟨528413, by rfl⟩ : syracuseStep 704551 = 1056827) B1056827
theorem B4243513 : Blo 702318 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B704591 : Blo 702318 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B704607 : Blo 702318 704607 := bstep (se 1 (by rfl) ⟨528455, by rfl⟩ : syracuseStep 704607 = 1056911) B1056911
theorem B704635 : Blo 702318 704635 := bstep (se 1 (by rfl) ⟨528476, by rfl⟩ : syracuseStep 704635 = 1056953) B1056953
theorem B2539673 : Blo 702318 2539673 := bstep (se 2 (by rfl) ⟨952377, by rfl⟩ : syracuseStep 2539673 = 1904755) B1904755
theorem B2375837 : Blo 702318 2375837 := bstep (se 3 (by rfl) ⟨445469, by rfl⟩ : syracuseStep 2375837 = 890939) B890939
theorem B704687 : Blo 702318 704687 := bstep (se 1 (by rfl) ⟨528515, by rfl⟩ : syracuseStep 704687 = 1057031) B1057031
theorem B704711 : Blo 702318 704711 := bstep (se 1 (by rfl) ⟨528533, by rfl⟩ : syracuseStep 704711 = 1057067) B1057067
theorem B704731 : Blo 702318 704731 := bstep (se 1 (by rfl) ⟨528548, by rfl⟩ : syracuseStep 704731 = 1057097) B1057097
theorem B704807 : Blo 702318 704807 := bstep (se 1 (by rfl) ⟨528605, by rfl⟩ : syracuseStep 704807 = 1057211) B1057211
theorem B704847 : Blo 702318 704847 := bstep (se 1 (by rfl) ⟨528635, by rfl⟩ : syracuseStep 704847 = 1057271) B1057271
theorem B704863 : Blo 702318 704863 := bstep (se 1 (by rfl) ⟨528647, by rfl⟩ : syracuseStep 704863 = 1057295) B1057295
theorem B704891 : Blo 702318 704891 := bstep (se 1 (by rfl) ⟨528668, by rfl⟩ : syracuseStep 704891 = 1057337) B1057337
theorem B704943 : Blo 702318 704943 := bstep (se 1 (by rfl) ⟨528707, by rfl⟩ : syracuseStep 704943 = 1057415) B1057415
theorem B967087 : Blo 702318 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B1130927 : Blo 702318 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B704967 : Blo 702318 704967 := bstep (se 1 (by rfl) ⟨528725, by rfl⟩ : syracuseStep 704967 = 1057451) B1057451
theorem B704987 : Blo 702318 704987 := bstep (se 1 (by rfl) ⟨528740, by rfl⟩ : syracuseStep 704987 = 1057481) B1057481
theorem B705063 : Blo 702318 705063 := bstep (se 1 (by rfl) ⟨528797, by rfl⟩ : syracuseStep 705063 = 1057595) B1057595
theorem B3555899 : Blo 702318 3555899 := bstep (se 1 (by rfl) ⟨2666924, by rfl⟩ : syracuseStep 3555899 = 5333849) B5333849
theorem B2671163 : Blo 702318 2671163 := bstep (se 1 (by rfl) ⟨2003372, by rfl⟩ : syracuseStep 2671163 = 4006745) B4006745
theorem B705103 : Blo 702318 705103 := bstep (se 1 (by rfl) ⟨528827, by rfl⟩ : syracuseStep 705103 = 1057655) B1057655
theorem B705119 : Blo 702318 705119 := bstep (se 1 (by rfl) ⟨528839, by rfl⟩ : syracuseStep 705119 = 1057679) B1057679
theorem B705147 : Blo 702318 705147 := bstep (se 1 (by rfl) ⟨528860, by rfl⟩ : syracuseStep 705147 = 1057721) B1057721
theorem B5718701 : Blo 702318 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B705199 : Blo 702318 705199 := bstep (se 1 (by rfl) ⟨528899, by rfl⟩ : syracuseStep 705199 = 1057799) B1057799
theorem B2376377 : Blo 702318 2376377 := bstep (se 2 (by rfl) ⟨891141, by rfl⟩ : syracuseStep 2376377 = 1782283) B1782283
theorem B705223 : Blo 702318 705223 := bstep (se 1 (by rfl) ⟨528917, by rfl⟩ : syracuseStep 705223 = 1057835) B1057835
theorem B27509453 : Blo 702318 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B705243 : Blo 702318 705243 := bstep (se 1 (by rfl) ⟨528932, by rfl⟩ : syracuseStep 705243 = 1057865) B1057865
theorem B705319 : Blo 702318 705319 := bstep (se 1 (by rfl) ⟨528989, by rfl⟩ : syracuseStep 705319 = 1057979) B1057979
theorem B1131337 : Blo 702318 1131337 := bstep (se 2 (by rfl) ⟨424251, by rfl⟩ : syracuseStep 1131337 = 848503) B848503
theorem B705359 : Blo 702318 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B705375 : Blo 702318 705375 := bstep (se 1 (by rfl) ⟨529031, by rfl⟩ : syracuseStep 705375 = 1058063) B1058063
theorem B10961771 : Blo 702318 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B705403 : Blo 702318 705403 := bstep (se 1 (by rfl) ⟨529052, by rfl⟩ : syracuseStep 705403 = 1058105) B1058105
theorem B705455 : Blo 702318 705455 := bstep (se 1 (by rfl) ⟨529091, by rfl⟩ : syracuseStep 705455 = 1058183) B1058183
theorem B1786799 : Blo 702318 1786799 := bstep (se 1 (by rfl) ⟨1340099, by rfl⟩ : syracuseStep 1786799 = 2680199) B2680199
theorem B705479 : Blo 702318 705479 := bstep (se 1 (by rfl) ⟨529109, by rfl⟩ : syracuseStep 705479 = 1058219) B1058219
theorem B705499 : Blo 702318 705499 := bstep (se 1 (by rfl) ⟨529124, by rfl⟩ : syracuseStep 705499 = 1058249) B1058249
theorem B705575 : Blo 702318 705575 := bstep (se 1 (by rfl) ⟨529181, by rfl⟩ : syracuseStep 705575 = 1058363) B1058363
theorem B5358635 : Blo 702318 5358635 := bstep (se 1 (by rfl) ⟨4018976, by rfl⟩ : syracuseStep 5358635 = 8037953) B8037953
theorem B705615 : Blo 702318 705615 := bstep (se 1 (by rfl) ⟨529211, by rfl⟩ : syracuseStep 705615 = 1058423) B1058423
theorem B705631 : Blo 702318 705631 := bstep (se 1 (by rfl) ⟨529223, by rfl⟩ : syracuseStep 705631 = 1058447) B1058447
theorem B705659 : Blo 702318 705659 := bstep (se 1 (by rfl) ⟨529244, by rfl⟩ : syracuseStep 705659 = 1058489) B1058489
theorem B705711 : Blo 702318 705711 := bstep (se 1 (by rfl) ⟨529283, by rfl⟩ : syracuseStep 705711 = 1058567) B1058567
theorem B3556547 : Blo 702318 3556547 := bstep (se 1 (by rfl) ⟨2667410, by rfl⟩ : syracuseStep 3556547 = 5334821) B5334821
theorem B705735 : Blo 702318 705735 := bstep (se 1 (by rfl) ⟨529301, by rfl⟩ : syracuseStep 705735 = 1058603) B1058603
theorem B705755 : Blo 702318 705755 := bstep (se 1 (by rfl) ⟨529316, by rfl⟩ : syracuseStep 705755 = 1058633) B1058633
theorem B2376971 : Blo 702318 2376971 := bstep (se 1 (by rfl) ⟨1782728, by rfl⟩ : syracuseStep 2376971 = 3565457) B3565457
theorem B705831 : Blo 702318 705831 := bstep (se 1 (by rfl) ⟨529373, by rfl⟩ : syracuseStep 705831 = 1058747) B1058747
theorem B705871 : Blo 702318 705871 := bstep (se 1 (by rfl) ⟨529403, by rfl⟩ : syracuseStep 705871 = 1058807) B1058807
theorem B705887 : Blo 702318 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B705915 : Blo 702318 705915 := bstep (se 1 (by rfl) ⟨529436, by rfl⟩ : syracuseStep 705915 = 1058873) B1058873
theorem B6768035 : Blo 702318 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B705967 : Blo 702318 705967 := bstep (se 1 (by rfl) ⟨529475, by rfl⟩ : syracuseStep 705967 = 1058951) B1058951
theorem B705991 : Blo 702318 705991 := bstep (se 1 (by rfl) ⟨529493, by rfl⟩ : syracuseStep 705991 = 1058987) B1058987
theorem B706011 : Blo 702318 706011 := bstep (se 1 (by rfl) ⟨529508, by rfl⟩ : syracuseStep 706011 = 1059017) B1059017
theorem B2377241 : Blo 702318 2377241 := bstep (se 2 (by rfl) ⟨891465, by rfl⟩ : syracuseStep 2377241 = 1782931) B1782931
theorem B1787417 : Blo 702318 1787417 := bstep (se 2 (by rfl) ⟨670281, by rfl⟩ : syracuseStep 1787417 = 1340563) B1340563
theorem B706087 : Blo 702318 706087 := bstep (se 1 (by rfl) ⟨529565, by rfl⟩ : syracuseStep 706087 = 1059131) B1059131
theorem B706127 : Blo 702318 706127 := bstep (se 1 (by rfl) ⟨529595, by rfl⟩ : syracuseStep 706127 = 1059191) B1059191
theorem B706143 : Blo 702318 706143 := bstep (se 1 (by rfl) ⟨529607, by rfl⟩ : syracuseStep 706143 = 1059215) B1059215
theorem B706171 : Blo 702318 706171 := bstep (se 1 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 706171 = 1059257) B1059257
theorem B706223 : Blo 702318 706223 := bstep (se 1 (by rfl) ⟨529667, by rfl⟩ : syracuseStep 706223 = 1059335) B1059335
theorem B706247 : Blo 702318 706247 := bstep (se 1 (by rfl) ⟨529685, by rfl⟩ : syracuseStep 706247 = 1059371) B1059371
theorem B1689299 : Blo 702318 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B706267 : Blo 702318 706267 := bstep (se 1 (by rfl) ⟨529700, by rfl⟩ : syracuseStep 706267 = 1059401) B1059401
theorem B4016243 : Blo 702318 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B4016699 : Blo 702318 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B2378375 : Blo 702318 2378375 := bstep (se 1 (by rfl) ⟨1783781, by rfl⟩ : syracuseStep 2378375 = 3567563) B3567563
theorem B5491385 : Blo 702318 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B2378429 : Blo 702318 2378429 := bstep (se 3 (by rfl) ⟨445955, by rfl⟩ : syracuseStep 2378429 = 891911) B891911
theorem B5720777 : Blo 702318 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B3001043 : Blo 702318 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B1002233 : Blo 702318 1002233 := bstep (se 2 (by rfl) ⟨375837, by rfl⟩ : syracuseStep 1002233 = 751675) B751675
theorem B2411293 : Blo 702318 2411293 := bstep (se 3 (by rfl) ⟨452117, by rfl⟩ : syracuseStep 2411293 = 904235) B904235
theorem B2378591 : Blo 702318 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B2378753 : Blo 702318 2378753 := bstep (se 2 (by rfl) ⟨892032, by rfl⟩ : syracuseStep 2378753 = 1784065) B1784065
theorem B2673911 : Blo 702318 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B1003207 : Blo 702318 1003207 := bstep (se 1 (by rfl) ⟨752405, by rfl⟩ : syracuseStep 1003207 = 1504811) B1504811
theorem B11423521 : Blo 702318 11423521 := bstep (se 2 (by rfl) ⟨4283820, by rfl⟩ : syracuseStep 11423521 = 8567641) B8567641
theorem B2379563 : Blo 702318 2379563 := bstep (se 1 (by rfl) ⟨1784672, by rfl⟩ : syracuseStep 2379563 = 3569345) B3569345
theorem B2379833 : Blo 702318 2379833 := bstep (se 2 (by rfl) ⟨892437, by rfl⟩ : syracuseStep 2379833 = 1784875) B1784875
theorem B2707627 : Blo 702318 2707627 := bstep (se 1 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 2707627 = 4061441) B4061441
theorem B2674883 : Blo 702318 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B10309963 : Blo 702318 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B2380157 : Blo 702318 2380157 := bstep (se 3 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 2380157 = 892559) B892559
theorem B2675339 : Blo 702318 2675339 := bstep (se 1 (by rfl) ⟨2006504, by rfl⟩ : syracuseStep 2675339 = 4013009) B4013009
theorem B2380427 : Blo 702318 2380427 := bstep (se 1 (by rfl) ⟨1785320, by rfl⟩ : syracuseStep 2380427 = 3570641) B3570641
theorem B2282195 : Blo 702318 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B2675551 : Blo 702318 2675551 := bstep (se 1 (by rfl) ⟨2006663, by rfl⟩ : syracuseStep 2675551 = 4013327) B4013327
theorem B1266607 : Blo 702318 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B32560193 : Blo 702318 32560193 := bstep (se 2 (by rfl) ⟨12210072, by rfl⟩ : syracuseStep 32560193 = 24420145) B24420145
theorem B3659251 : Blo 702318 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B2381345 : Blo 702318 2381345 := bstep (se 2 (by rfl) ⟨893004, by rfl⟩ : syracuseStep 2381345 = 1786009) B1786009
theorem B3561083 : Blo 702318 3561083 := bstep (se 1 (by rfl) ⟨2670812, by rfl⟩ : syracuseStep 3561083 = 5341625) B5341625
theorem B21649045 : Blo 702318 21649045 := bstep (se 6 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 21649045 = 1014799) B1014799
theorem B2381561 : Blo 702318 2381561 := bstep (se 2 (by rfl) ⟨893085, by rfl⟩ : syracuseStep 2381561 = 1786171) B1786171
theorem B2676509 : Blo 702318 2676509 := bstep (se 3 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 2676509 = 1003691) B1003691
theorem B6084395 : Blo 702318 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B2676523 : Blo 702318 2676523 := bstep (se 1 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 2676523 = 4014785) B4014785
theorem B2545481 : Blo 702318 2545481 := bstep (se 2 (by rfl) ⟨954555, by rfl⟩ : syracuseStep 2545481 = 1909111) B1909111
theorem B1202015 : Blo 702318 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B9033677 : Blo 702318 9033677 := bstep (se 3 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 9033677 = 3387629) B3387629
theorem B2381831 : Blo 702318 2381831 := bstep (se 1 (by rfl) ⟨1786373, by rfl⟩ : syracuseStep 2381831 = 3572747) B3572747
theorem B2381939 : Blo 702318 2381939 := bstep (se 1 (by rfl) ⟨1786454, by rfl⟩ : syracuseStep 2381939 = 3572909) B3572909
theorem B1333577 : Blo 702318 1333577 := bstep (se 2 (by rfl) ⟨500091, by rfl⟩ : syracuseStep 1333577 = 1000183) B1000183
theorem B2382209 : Blo 702318 2382209 := bstep (se 2 (by rfl) ⟨893328, by rfl⟩ : syracuseStep 2382209 = 1786657) B1786657
theorem B1334009 : Blo 702318 1334009 := bstep (se 2 (by rfl) ⟨500253, by rfl⟩ : syracuseStep 1334009 = 1000507) B1000507
theorem B1694891 : Blo 702318 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B2383019 : Blo 702318 2383019 := bstep (se 1 (by rfl) ⟨1787264, by rfl⟩ : syracuseStep 2383019 = 3574529) B3574529
theorem B2252423 : Blo 702318 2252423 := bstep (se 1 (by rfl) ⟨1689317, by rfl⟩ : syracuseStep 2252423 = 3378635) B3378635
theorem B2383559 : Blo 702318 2383559 := bstep (se 1 (by rfl) ⟨1787669, by rfl⟩ : syracuseStep 2383559 = 3575339) B3575339
theorem B1695583 : Blo 702318 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B2252731 : Blo 702318 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B2744435 : Blo 702318 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B1335467 : Blo 702318 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B1270009 : Blo 702318 1270009 := bstep (se 2 (by rfl) ⟨476253, by rfl⟩ : syracuseStep 1270009 = 952507) B952507
theorem B3563837 : Blo 702318 3563837 := bstep (se 3 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 3563837 = 1336439) B1336439
theorem B6873623 : Blo 702318 6873623 := bstep (se 1 (by rfl) ⟨5155217, by rfl⟩ : syracuseStep 6873623 = 10310435) B10310435
theorem B1335847 : Blo 702318 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B2777723 : Blo 702318 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B1336007 : Blo 702318 1336007 := bstep (se 1 (by rfl) ⟨1002005, by rfl⟩ : syracuseStep 1336007 = 2004011) B2004011
theorem B11428715 : Blo 702318 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B2679713 : Blo 702318 2679713 := bstep (se 2 (by rfl) ⟨1004892, by rfl⟩ : syracuseStep 2679713 = 2009785) B2009785
theorem B15262937 : Blo 702318 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B2254205 : Blo 702318 2254205 := bstep (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) B845327
theorem B1271227 : Blo 702318 1271227 := bstep (se 1 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 1271227 = 1906841) B1906841
theorem B3007945 : Blo 702318 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B1337161 : Blo 702318 1337161 := bstep (se 2 (by rfl) ⟨501435, by rfl⟩ : syracuseStep 1337161 = 1002871) B1002871
theorem B2680685 : Blo 702318 2680685 := bstep (se 3 (by rfl) ⟨502628, by rfl⟩ : syracuseStep 2680685 = 1005257) B1005257
theorem B9037777 : Blo 702318 9037777 := bstep (se 2 (by rfl) ⟨3389166, by rfl⟩ : syracuseStep 9037777 = 6778333) B6778333
theorem B5335307 : Blo 702318 5335307 := bstep (se 1 (by rfl) ⟨4001480, by rfl⟩ : syracuseStep 5335307 = 8002961) B8002961
theorem B2287883 : Blo 702318 2287883 := bstep (se 1 (by rfl) ⟨1715912, by rfl⟩ : syracuseStep 2287883 = 3431825) B3431825
theorem B3566105 : Blo 702318 3566105 := bstep (se 2 (by rfl) ⟨1337289, by rfl⟩ : syracuseStep 3566105 = 2674579) B2674579
theorem B2681369 : Blo 702318 2681369 := bstep (se 2 (by rfl) ⟨1005513, by rfl⟩ : syracuseStep 2681369 = 2011027) B2011027
theorem B6777377 : Blo 702318 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B1501735 : Blo 702318 1501735 := bstep (se 1 (by rfl) ⟨1126301, by rfl⟩ : syracuseStep 1501735 = 2252603) B2252603
theorem B2681383 : Blo 702318 2681383 := bstep (se 1 (by rfl) ⟨2011037, by rfl⟩ : syracuseStep 2681383 = 4022075) B4022075
theorem B1502059 : Blo 702318 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B3009707 : Blo 702318 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B5336765 : Blo 702318 5336765 := bstep (se 3 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 5336765 = 2001287) B2001287
theorem B22802141 : Blo 702318 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B1339355 : Blo 702318 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B1503289 : Blo 702318 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B5337251 : Blo 702318 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B1339591 : Blo 702318 1339591 := bstep (se 1 (by rfl) ⟨1004693, by rfl⟩ : syracuseStep 1339591 = 2009387) B2009387
theorem B5501245 : Blo 702318 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B1503631 : Blo 702318 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B19264715 : Blo 702318 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B3569021 : Blo 702318 3569021 := bstep (se 3 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 3569021 = 1338383) B1338383
theorem B2848391 : Blo 702318 2848391 := bstep (se 1 (by rfl) ⟨2136293, by rfl⟩ : syracuseStep 2848391 = 4272587) B4272587
theorem B751303 : Blo 702318 751303 := bstep (se 1 (by rfl) ⟨563477, by rfl⟩ : syracuseStep 751303 = 1126955) B1126955
theorem B18249785 : Blo 702318 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B5339681 : Blo 702318 5339681 := bstep (se 2 (by rfl) ⟨2002380, by rfl⟩ : syracuseStep 5339681 = 4004761) B4004761
theorem B9009893 : Blo 702318 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B1899359 : Blo 702318 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B3014131 : Blo 702318 3014131 := bstep (se 1 (by rfl) ⟨2260598, by rfl⟩ : syracuseStep 3014131 = 4521197) B4521197
theorem B9633667 : Blo 702318 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B4292513 : Blo 702318 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B1507835 : Blo 702318 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B3572423 : Blo 702318 3572423 := bstep (se 1 (by rfl) ⟨2679317, by rfl⟩ : syracuseStep 3572423 = 5358635) B5358635
theorem B3015737 : Blo 702318 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B3015805 : Blo 702318 3015805 := bstep (se 3 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 3015805 = 1130927) B1130927
theorem B2000695 : Blo 702318 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B2852993 : Blo 702318 2852993 := bstep (se 2 (by rfl) ⟨1069872, by rfl⟩ : syracuseStep 2852993 = 2139745) B2139745
theorem B29231389 : Blo 702318 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B2002313 : Blo 702318 2002313 := bstep (se 2 (by rfl) ⟨750867, by rfl⟩ : syracuseStep 2002313 = 1501735) B1501735
theorem B3575177 : Blo 702318 3575177 := bstep (se 2 (by rfl) ⟨1340691, by rfl⟩ : syracuseStep 3575177 = 2681383) B2681383
theorem B6032839 : Blo 702318 6032839 := bstep (se 1 (by rfl) ⟨4524629, by rfl⟩ : syracuseStep 6032839 = 9049259) B9049259
theorem B3215057 : Blo 702318 3215057 := bstep (se 2 (by rfl) ⟨1205646, by rfl⟩ : syracuseStep 3215057 = 2411293) B2411293
theorem B9899819 : Blo 702318 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B2002745 : Blo 702318 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B889051 : Blo 702318 889051 := bstep (se 1 (by rfl) ⟨666788, by rfl⟩ : syracuseStep 889051 = 1333577) B1333577
theorem B3805547 : Blo 702318 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B6033797 : Blo 702318 6033797 := bstep (se 4 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 6033797 = 1131337) B1131337
theorem B790951 : Blo 702318 790951 := bstep (se 1 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 790951 = 1186427) B1186427
theorem B12063491 : Blo 702318 12063491 := bstep (se 1 (by rfl) ⟨9047618, by rfl⟩ : syracuseStep 12063491 = 18095237) B18095237
theorem B1053671 : Blo 702318 1053671 := bstep (se 1 (by rfl) ⟨790253, by rfl⟩ : syracuseStep 1053671 = 1580507) B1580507
theorem B791527 : Blo 702318 791527 := bstep (se 1 (by rfl) ⟨593645, by rfl⟩ : syracuseStep 791527 = 1187291) B1187291
theorem B1053929 : Blo 702318 1053929 := bstep (se 2 (by rfl) ⟨395223, by rfl⟩ : syracuseStep 1053929 = 790447) B790447
theorem B6755575 : Blo 702318 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B1053983 : Blo 702318 1053983 := bstep (se 1 (by rfl) ⟨790487, by rfl⟩ : syracuseStep 1053983 = 1580975) B1580975
theorem B1807753 : Blo 702318 1807753 := bstep (se 2 (by rfl) ⟨677907, by rfl⟩ : syracuseStep 1807753 = 1355815) B1355815
theorem B1054151 : Blo 702318 1054151 := bstep (se 1 (by rfl) ⟨790613, by rfl⟩ : syracuseStep 1054151 = 1581227) B1581227
theorem B77960657 : Blo 702318 77960657 := bstep (se 2 (by rfl) ⟨29235246, by rfl⟩ : syracuseStep 77960657 = 58470493) B58470493
theorem B6755885 : Blo 702318 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B3610169 : Blo 702318 3610169 := bstep (se 2 (by rfl) ⟨1353813, by rfl⟩ : syracuseStep 3610169 = 2707627) B2707627
theorem B1054505 : Blo 702318 1054505 := bstep (se 2 (by rfl) ⟨395439, by rfl⟩ : syracuseStep 1054505 = 790879) B790879
theorem B1185583 : Blo 702318 1185583 := bstep (se 1 (by rfl) ⟨889187, by rfl⟩ : syracuseStep 1185583 = 1778375) B1778375
theorem B1054511 : Blo 702318 1054511 := bstep (se 1 (by rfl) ⟨790883, by rfl⟩ : syracuseStep 1054511 = 1581767) B1581767
theorem B890671 : Blo 702318 890671 := bstep (se 1 (by rfl) ⟨668003, by rfl⟩ : syracuseStep 890671 = 1336007) B1336007
theorem B2004841 : Blo 702318 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B6101021 : Blo 702318 6101021 := bstep (se 3 (by rfl) ⟨1143941, by rfl⟩ : syracuseStep 6101021 = 2287883) B2287883
theorem B16685189 : Blo 702318 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B1054985 : Blo 702318 1054985 := bstep (se 2 (by rfl) ⟨395619, by rfl⟩ : syracuseStep 1054985 = 791239) B791239
theorem B1055087 : Blo 702318 1055087 := bstep (se 1 (by rfl) ⟨791315, by rfl⟩ : syracuseStep 1055087 = 1582631) B1582631
theorem B1055303 : Blo 702318 1055303 := bstep (se 1 (by rfl) ⟨791477, by rfl⟩ : syracuseStep 1055303 = 1582955) B1582955
theorem B793183 : Blo 702318 793183 := bstep (se 1 (by rfl) ⟨594887, by rfl⟩ : syracuseStep 793183 = 1189775) B1189775
theorem B1055339 : Blo 702318 1055339 := bstep (se 1 (by rfl) ⟨791504, by rfl⟩ : syracuseStep 1055339 = 1583009) B1583009
theorem B1055567 : Blo 702318 1055567 := bstep (se 1 (by rfl) ⟨791675, by rfl⟩ : syracuseStep 1055567 = 1583351) B1583351
theorem B1055963 : Blo 702318 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B1580327 : Blo 702318 1580327 := bstep (se 1 (by rfl) ⟨1185245, by rfl⟩ : syracuseStep 1580327 = 2370491) B2370491
theorem B1056137 : Blo 702318 1056137 := bstep (se 2 (by rfl) ⟨396051, by rfl⟩ : syracuseStep 1056137 = 792103) B792103
theorem B2006471 : Blo 702318 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B1580705 : Blo 702318 1580705 := bstep (se 2 (by rfl) ⟨592764, by rfl⟩ : syracuseStep 1580705 = 1185529) B1185529
theorem B12197537 : Blo 702318 12197537 := bstep (se 2 (by rfl) ⟨4574076, by rfl⟩ : syracuseStep 12197537 = 9148153) B9148153
theorem B794335 : Blo 702318 794335 := bstep (se 1 (by rfl) ⟨595751, by rfl⟩ : syracuseStep 794335 = 1191503) B1191503
theorem B1056491 : Blo 702318 1056491 := bstep (se 1 (by rfl) ⟨792368, by rfl⟩ : syracuseStep 1056491 = 1584737) B1584737
theorem B1056719 : Blo 702318 1056719 := bstep (se 1 (by rfl) ⟨792539, by rfl⟩ : syracuseStep 1056719 = 1585079) B1585079
theorem B1581065 : Blo 702318 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B5087441 : Blo 702318 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B1057115 : Blo 702318 1057115 := bstep (se 1 (by rfl) ⟨792836, by rfl⟩ : syracuseStep 1057115 = 1585673) B1585673
theorem B1581479 : Blo 702318 1581479 := bstep (se 1 (by rfl) ⟨1186109, by rfl⟩ : syracuseStep 1581479 = 2372219) B2372219
theorem B1188263 : Blo 702318 1188263 := bstep (se 1 (by rfl) ⟨891197, by rfl⟩ : syracuseStep 1188263 = 1782395) B1782395
theorem B6758923 : Blo 702318 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B1581587 : Blo 702318 1581587 := bstep (se 1 (by rfl) ⟨1186190, by rfl⟩ : syracuseStep 1581587 = 2372381) B2372381
theorem B1057343 : Blo 702318 1057343 := bstep (se 1 (by rfl) ⟨793007, by rfl⟩ : syracuseStep 1057343 = 1586015) B1586015
theorem B1581641 : Blo 702318 1581641 := bstep (se 2 (by rfl) ⟨593115, by rfl⟩ : syracuseStep 1581641 = 1186231) B1186231
theorem B1188425 : Blo 702318 1188425 := bstep (se 2 (by rfl) ⟨445659, by rfl⟩ : syracuseStep 1188425 = 891319) B891319
theorem B1057463 : Blo 702318 1057463 := bstep (se 1 (by rfl) ⟨793097, by rfl⟩ : syracuseStep 1057463 = 1586195) B1586195
theorem B21635855 : Blo 702318 21635855 := bstep (se 1 (by rfl) ⟨16226891, by rfl⟩ : syracuseStep 21635855 = 32453783) B32453783
theorem B1057691 : Blo 702318 1057691 := bstep (se 1 (by rfl) ⟨793268, by rfl⟩ : syracuseStep 1057691 = 1586537) B1586537
theorem B1582055 : Blo 702318 1582055 := bstep (se 1 (by rfl) ⟨1186541, by rfl⟩ : syracuseStep 1582055 = 2373083) B2373083
theorem B1778831 : Blo 702318 1778831 := bstep (se 1 (by rfl) ⟨1334123, by rfl⟩ : syracuseStep 1778831 = 2668247) B2668247
theorem B1058087 : Blo 702318 1058087 := bstep (se 1 (by rfl) ⟨793565, by rfl⟩ : syracuseStep 1058087 = 1587131) B1587131
theorem B1582433 : Blo 702318 1582433 := bstep (se 2 (by rfl) ⟨593412, by rfl⟩ : syracuseStep 1582433 = 1186825) B1186825
theorem B12166523 : Blo 702318 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B1058171 : Blo 702318 1058171 := bstep (se 1 (by rfl) ⟨793628, by rfl⟩ : syracuseStep 1058171 = 1587257) B1587257
theorem B1582523 : Blo 702318 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B1058297 : Blo 702318 1058297 := bstep (se 2 (by rfl) ⟨396861, by rfl⟩ : syracuseStep 1058297 = 793723) B793723
theorem B1582649 : Blo 702318 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B1189471 : Blo 702318 1189471 := bstep (se 1 (by rfl) ⟨892103, by rfl⟩ : syracuseStep 1189471 = 1784207) B1784207
theorem B1058399 : Blo 702318 1058399 := bstep (se 1 (by rfl) ⟨793799, by rfl⟩ : syracuseStep 1058399 = 1587599) B1587599
theorem B1189687 : Blo 702318 1189687 := bstep (se 1 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 1189687 = 1784531) B1784531
theorem B1058615 : Blo 702318 1058615 := bstep (se 1 (by rfl) ⟨793961, by rfl⟩ : syracuseStep 1058615 = 1587923) B1587923
theorem B6006595 : Blo 702318 6006595 := bstep (se 1 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 6006595 = 9009893) B9009893
theorem B3385169 : Blo 702318 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B1058921 : Blo 702318 1058921 := bstep (se 2 (by rfl) ⟨397095, by rfl⟩ : syracuseStep 1058921 = 794191) B794191
theorem B13576349 : Blo 702318 13576349 := bstep (se 3 (by rfl) ⟨2545565, by rfl⟩ : syracuseStep 13576349 = 5091131) B5091131
theorem B1583315 : Blo 702318 1583315 := bstep (se 1 (by rfl) ⟨1187486, by rfl⟩ : syracuseStep 1583315 = 2374973) B2374973
theorem B1583369 : Blo 702318 1583369 := bstep (se 2 (by rfl) ⟨593763, by rfl⟩ : syracuseStep 1583369 = 1187527) B1187527
theorem B1190153 : Blo 702318 1190153 := bstep (se 2 (by rfl) ⟨446307, by rfl⟩ : syracuseStep 1190153 = 892615) B892615
theorem B1059239 : Blo 702318 1059239 := bstep (se 1 (by rfl) ⟨794429, by rfl⟩ : syracuseStep 1059239 = 1588859) B1588859
theorem B1583585 : Blo 702318 1583585 := bstep (se 2 (by rfl) ⟨593844, by rfl⟩ : syracuseStep 1583585 = 1187689) B1187689
theorem B1059323 : Blo 702318 1059323 := bstep (se 1 (by rfl) ⟨794492, by rfl⟩ : syracuseStep 1059323 = 1588985) B1588985
theorem B2861675 : Blo 702318 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1059449 : Blo 702318 1059449 := bstep (se 2 (by rfl) ⟨397293, by rfl⟩ : syracuseStep 1059449 = 794587) B794587
theorem B5090039 : Blo 702318 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B1583891 : Blo 702318 1583891 := bstep (se 1 (by rfl) ⟨1187918, by rfl⟩ : syracuseStep 1583891 = 2375837) B2375837
theorem B5352317 : Blo 702318 5352317 := bstep (se 3 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 5352317 = 2007119) B2007119
theorem B2370599 : Blo 702318 2370599 := bstep (se 1 (by rfl) ⟨1777949, by rfl⟩ : syracuseStep 2370599 = 3555899) B3555899
theorem B1780775 : Blo 702318 1780775 := bstep (se 1 (by rfl) ⟨1335581, by rfl⟩ : syracuseStep 1780775 = 2671163) B2671163
theorem B1584251 : Blo 702318 1584251 := bstep (se 1 (by rfl) ⟨1188188, by rfl⟩ : syracuseStep 1584251 = 2376377) B2376377
theorem B1191145 : Blo 702318 1191145 := bstep (se 2 (by rfl) ⟨446679, by rfl⟩ : syracuseStep 1191145 = 893359) B893359
theorem B1289449 : Blo 702318 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B1584377 : Blo 702318 1584377 := bstep (se 2 (by rfl) ⟨594141, by rfl⟩ : syracuseStep 1584377 = 1188283) B1188283
theorem B1191199 : Blo 702318 1191199 := bstep (se 1 (by rfl) ⟨893399, by rfl⟩ : syracuseStep 1191199 = 1786799) B1786799
theorem B1781129 : Blo 702318 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B1584521 : Blo 702318 1584521 := bstep (se 2 (by rfl) ⟨594195, by rfl⟩ : syracuseStep 1584521 = 1188391) B1188391
theorem B2371031 : Blo 702318 2371031 := bstep (se 1 (by rfl) ⟨1778273, by rfl⟩ : syracuseStep 2371031 = 3556547) B3556547
theorem B1584647 : Blo 702318 1584647 := bstep (se 1 (by rfl) ⟨1188485, by rfl⟩ : syracuseStep 1584647 = 2376971) B2376971
theorem B2010719 : Blo 702318 2010719 := bstep (se 1 (by rfl) ⟨1508039, by rfl⟩ : syracuseStep 2010719 = 3016079) B3016079
theorem B962231 : Blo 702318 962231 := bstep (se 1 (by rfl) ⟨721673, by rfl⟩ : syracuseStep 962231 = 1443347) B1443347
theorem B1584827 : Blo 702318 1584827 := bstep (se 1 (by rfl) ⟨1188620, by rfl⟩ : syracuseStep 1584827 = 2377241) B2377241
theorem B1191611 : Blo 702318 1191611 := bstep (se 1 (by rfl) ⟨893708, by rfl⟩ : syracuseStep 1191611 = 1787417) B1787417
theorem B1126199 : Blo 702318 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B1584953 : Blo 702318 1584953 := bstep (se 2 (by rfl) ⟨594357, by rfl⟩ : syracuseStep 1584953 = 1188715) B1188715
theorem B6435073 : Blo 702318 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B1585583 : Blo 702318 1585583 := bstep (se 1 (by rfl) ⟨1189187, by rfl⟩ : syracuseStep 1585583 = 2378375) B2378375
theorem B15249869 : Blo 702318 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B1585619 : Blo 702318 1585619 := bstep (se 1 (by rfl) ⟨1189214, by rfl⟩ : syracuseStep 1585619 = 2378429) B2378429
theorem B3813851 : Blo 702318 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B1585727 : Blo 702318 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B4010593 : Blo 702318 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B1585835 : Blo 702318 1585835 := bstep (se 1 (by rfl) ⟨1189376, by rfl⟩ : syracuseStep 1585835 = 2378753) B2378753
theorem B1782607 : Blo 702318 1782607 := bstep (se 1 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 1782607 = 2673911) B2673911
theorem B2143055 : Blo 702318 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B2372705 : Blo 702318 2372705 := bstep (se 2 (by rfl) ⟨889764, by rfl⟩ : syracuseStep 2372705 = 1779529) B1779529
theorem B1782881 : Blo 702318 1782881 := bstep (se 2 (by rfl) ⟨668580, by rfl⟩ : syracuseStep 1782881 = 1337161) B1337161
theorem B1586375 : Blo 702318 1586375 := bstep (se 1 (by rfl) ⟨1189781, by rfl⟩ : syracuseStep 1586375 = 2379563) B2379563
theorem B1586555 : Blo 702318 1586555 := bstep (se 1 (by rfl) ⟨1189916, by rfl⟩ : syracuseStep 1586555 = 2379833) B2379833
theorem B1783255 : Blo 702318 1783255 := bstep (se 1 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 1783255 = 2674883) B2674883
theorem B1586681 : Blo 702318 1586681 := bstep (se 2 (by rfl) ⟨595005, by rfl⟩ : syracuseStep 1586681 = 1190011) B1190011
theorem B1586771 : Blo 702318 1586771 := bstep (se 1 (by rfl) ⟨1190078, by rfl⟩ : syracuseStep 1586771 = 2380157) B2380157
theorem B1783559 : Blo 702318 1783559 := bstep (se 1 (by rfl) ⟨1337669, by rfl⟩ : syracuseStep 1783559 = 2675339) B2675339
theorem B1586951 : Blo 702318 1586951 := bstep (se 1 (by rfl) ⟨1190213, by rfl⟩ : syracuseStep 1586951 = 2380427) B2380427
theorem B702363 : Blo 702318 702363 := bstep (se 1 (by rfl) ⟨526772, by rfl⟩ : syracuseStep 702363 = 1053545) B1053545
theorem B702415 : Blo 702318 702415 := bstep (se 1 (by rfl) ⟨526811, by rfl⟩ : syracuseStep 702415 = 1053623) B1053623
theorem B2471887 : Blo 702318 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B702439 : Blo 702318 702439 := bstep (se 1 (by rfl) ⟨526829, by rfl⟩ : syracuseStep 702439 = 1053659) B1053659
theorem B6764573 : Blo 702318 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B21706795 : Blo 702318 21706795 := bstep (se 1 (by rfl) ⟨16280096, by rfl⟩ : syracuseStep 21706795 = 32560193) B32560193
theorem B702751 : Blo 702318 702751 := bstep (se 1 (by rfl) ⟨527063, by rfl⟩ : syracuseStep 702751 = 1054127) B1054127
theorem B702811 : Blo 702318 702811 := bstep (se 1 (by rfl) ⟨527108, by rfl⟩ : syracuseStep 702811 = 1054217) B1054217
theorem B1587563 : Blo 702318 1587563 := bstep (se 1 (by rfl) ⟨1190672, by rfl⟩ : syracuseStep 1587563 = 2381345) B2381345
theorem B702831 : Blo 702318 702831 := bstep (se 1 (by rfl) ⟨527123, by rfl⟩ : syracuseStep 702831 = 1054247) B1054247
theorem B2537839 : Blo 702318 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B702887 : Blo 702318 702887 := bstep (se 1 (by rfl) ⟨527165, by rfl⟩ : syracuseStep 702887 = 1054331) B1054331
theorem B2374055 : Blo 702318 2374055 := bstep (se 1 (by rfl) ⟨1780541, by rfl⟩ : syracuseStep 2374055 = 3561083) B3561083
theorem B2669051 : Blo 702318 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B702971 : Blo 702318 702971 := bstep (se 1 (by rfl) ⟨527228, by rfl⟩ : syracuseStep 702971 = 1054457) B1054457
theorem B1587707 : Blo 702318 1587707 := bstep (se 1 (by rfl) ⟨1190780, by rfl⟩ : syracuseStep 1587707 = 2381561) B2381561
theorem B1784339 : Blo 702318 1784339 := bstep (se 1 (by rfl) ⟨1338254, by rfl⟩ : syracuseStep 1784339 = 2676509) B2676509
theorem B801343 : Blo 702318 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B703039 : Blo 702318 703039 := bstep (se 1 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 703039 = 1054559) B1054559
theorem B703047 : Blo 702318 703047 := bstep (se 1 (by rfl) ⟨527285, by rfl⟩ : syracuseStep 703047 = 1054571) B1054571
theorem B2374217 : Blo 702318 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B1587833 : Blo 702318 1587833 := bstep (se 2 (by rfl) ⟨595437, by rfl⟩ : syracuseStep 1587833 = 1190875) B1190875
theorem B1587887 : Blo 702318 1587887 := bstep (se 1 (by rfl) ⟨1190915, by rfl⟩ : syracuseStep 1587887 = 2381831) B2381831
theorem B703199 : Blo 702318 703199 := bstep (se 1 (by rfl) ⟨527399, by rfl⟩ : syracuseStep 703199 = 1054799) B1054799
theorem B1587959 : Blo 702318 1587959 := bstep (se 1 (by rfl) ⟨1190969, by rfl⟩ : syracuseStep 1587959 = 2381939) B2381939
theorem B703279 : Blo 702318 703279 := bstep (se 1 (by rfl) ⟨527459, by rfl⟩ : syracuseStep 703279 = 1054919) B1054919
theorem B703387 : Blo 702318 703387 := bstep (se 1 (by rfl) ⟨527540, by rfl⟩ : syracuseStep 703387 = 1055081) B1055081
theorem B1588139 : Blo 702318 1588139 := bstep (se 1 (by rfl) ⟨1191104, by rfl⟩ : syracuseStep 1588139 = 2382209) B2382209
theorem B703439 : Blo 702318 703439 := bstep (se 1 (by rfl) ⟨527579, by rfl⟩ : syracuseStep 703439 = 1055159) B1055159
theorem B703463 : Blo 702318 703463 := bstep (se 1 (by rfl) ⟨527597, by rfl⟩ : syracuseStep 703463 = 1055195) B1055195
theorem B703775 : Blo 702318 703775 := bstep (se 1 (by rfl) ⟨527831, by rfl⟩ : syracuseStep 703775 = 1055663) B1055663
theorem B703835 : Blo 702318 703835 := bstep (se 1 (by rfl) ⟨527876, by rfl⟩ : syracuseStep 703835 = 1055753) B1055753
theorem B703855 : Blo 702318 703855 := bstep (se 1 (by rfl) ⟨527891, by rfl⟩ : syracuseStep 703855 = 1055783) B1055783
theorem B703911 : Blo 702318 703911 := bstep (se 1 (by rfl) ⟨527933, by rfl⟩ : syracuseStep 703911 = 1055867) B1055867
theorem B2670023 : Blo 702318 2670023 := bstep (se 1 (by rfl) ⟨2002517, by rfl⟩ : syracuseStep 2670023 = 4005035) B4005035
theorem B1588679 : Blo 702318 1588679 := bstep (se 1 (by rfl) ⟨1191509, by rfl⟩ : syracuseStep 1588679 = 2383019) B2383019
theorem B703995 : Blo 702318 703995 := bstep (se 1 (by rfl) ⟨527996, by rfl⟩ : syracuseStep 703995 = 1055993) B1055993
theorem B704063 : Blo 702318 704063 := bstep (se 1 (by rfl) ⟨528047, by rfl⟩ : syracuseStep 704063 = 1056095) B1056095
theorem B704071 : Blo 702318 704071 := bstep (se 1 (by rfl) ⟨528053, by rfl⟩ : syracuseStep 704071 = 1056107) B1056107
theorem B28884599 : Blo 702318 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B704223 : Blo 702318 704223 := bstep (se 1 (by rfl) ⟨528167, by rfl⟩ : syracuseStep 704223 = 1056335) B1056335
theorem B704303 : Blo 702318 704303 := bstep (se 1 (by rfl) ⟨528227, by rfl⟩ : syracuseStep 704303 = 1056455) B1056455
theorem B1589039 : Blo 702318 1589039 := bstep (se 1 (by rfl) ⟨1191779, by rfl⟩ : syracuseStep 1589039 = 2383559) B2383559
theorem B704411 : Blo 702318 704411 := bstep (se 1 (by rfl) ⟨528308, by rfl⟩ : syracuseStep 704411 = 1056617) B1056617
theorem B704463 : Blo 702318 704463 := bstep (se 1 (by rfl) ⟨528347, by rfl⟩ : syracuseStep 704463 = 1056695) B1056695
theorem B704487 : Blo 702318 704487 := bstep (se 1 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 704487 = 1056731) B1056731
theorem B29278361 : Blo 702318 29278361 := bstep (se 2 (by rfl) ⟨10979385, by rfl⟩ : syracuseStep 29278361 = 21958771) B21958771
theorem B2375891 : Blo 702318 2375891 := bstep (se 1 (by rfl) ⟨1781918, by rfl⟩ : syracuseStep 2375891 = 3563837) B3563837
theorem B1786121 : Blo 702318 1786121 := bstep (se 2 (by rfl) ⟨669795, by rfl⟩ : syracuseStep 1786121 = 1339591) B1339591
theorem B704799 : Blo 702318 704799 := bstep (se 1 (by rfl) ⟨528599, by rfl⟩ : syracuseStep 704799 = 1057199) B1057199
theorem B704859 : Blo 702318 704859 := bstep (se 1 (by rfl) ⟨528644, by rfl⟩ : syracuseStep 704859 = 1057289) B1057289
theorem B30458213 : Blo 702318 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B704879 : Blo 702318 704879 := bstep (se 1 (by rfl) ⟨528659, by rfl⟩ : syracuseStep 704879 = 1057319) B1057319
theorem B1851815 : Blo 702318 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B704935 : Blo 702318 704935 := bstep (se 1 (by rfl) ⟨528701, by rfl⟩ : syracuseStep 704935 = 1057403) B1057403
theorem B13746617 : Blo 702318 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B2376161 : Blo 702318 2376161 := bstep (se 2 (by rfl) ⟨891060, by rfl⟩ : syracuseStep 2376161 = 1782121) B1782121
theorem B705019 : Blo 702318 705019 := bstep (se 1 (by rfl) ⟨528764, by rfl⟩ : syracuseStep 705019 = 1057529) B1057529
theorem B705087 : Blo 702318 705087 := bstep (se 1 (by rfl) ⟨528815, by rfl⟩ : syracuseStep 705087 = 1057631) B1057631
theorem B7619143 : Blo 702318 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B705095 : Blo 702318 705095 := bstep (se 1 (by rfl) ⟨528821, by rfl⟩ : syracuseStep 705095 = 1057643) B1057643
theorem B1786475 : Blo 702318 1786475 := bstep (se 1 (by rfl) ⟨1339856, by rfl⟩ : syracuseStep 1786475 = 2679713) B2679713
theorem B705247 : Blo 702318 705247 := bstep (se 1 (by rfl) ⟨528935, by rfl⟩ : syracuseStep 705247 = 1057871) B1057871
theorem B705327 : Blo 702318 705327 := bstep (se 1 (by rfl) ⟨528995, by rfl⟩ : syracuseStep 705327 = 1057991) B1057991
theorem B10175291 : Blo 702318 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B705435 : Blo 702318 705435 := bstep (se 1 (by rfl) ⟨529076, by rfl⟩ : syracuseStep 705435 = 1058153) B1058153
theorem B705487 : Blo 702318 705487 := bstep (se 1 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 705487 = 1058231) B1058231
theorem B4506587 : Blo 702318 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B705511 : Blo 702318 705511 := bstep (se 1 (by rfl) ⟨529133, by rfl⟩ : syracuseStep 705511 = 1058267) B1058267
theorem B1688809 : Blo 702318 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B1787123 : Blo 702318 1787123 := bstep (se 1 (by rfl) ⟨1340342, by rfl⟩ : syracuseStep 1787123 = 2680685) B2680685
theorem B705823 : Blo 702318 705823 := bstep (se 1 (by rfl) ⟨529367, by rfl⟩ : syracuseStep 705823 = 1058735) B1058735
theorem B705883 : Blo 702318 705883 := bstep (se 1 (by rfl) ⟨529412, by rfl⟩ : syracuseStep 705883 = 1058825) B1058825
theorem B2671967 : Blo 702318 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B705903 : Blo 702318 705903 := bstep (se 1 (by rfl) ⟨529427, by rfl⟩ : syracuseStep 705903 = 1058855) B1058855
theorem B705959 : Blo 702318 705959 := bstep (se 1 (by rfl) ⟨529469, by rfl⟩ : syracuseStep 705959 = 1058939) B1058939
theorem B706043 : Blo 702318 706043 := bstep (se 1 (by rfl) ⟨529532, by rfl⟩ : syracuseStep 706043 = 1059065) B1059065
theorem B3556871 : Blo 702318 3556871 := bstep (se 1 (by rfl) ⟨2667653, by rfl⟩ : syracuseStep 3556871 = 5335307) B5335307
theorem B2672135 : Blo 702318 2672135 := bstep (se 1 (by rfl) ⟨2004101, by rfl⟩ : syracuseStep 2672135 = 4008203) B4008203
theorem B706111 : Blo 702318 706111 := bstep (se 1 (by rfl) ⟨529583, by rfl⟩ : syracuseStep 706111 = 1059167) B1059167
theorem B706119 : Blo 702318 706119 := bstep (se 1 (by rfl) ⟨529589, by rfl⟩ : syracuseStep 706119 = 1059179) B1059179
theorem B2377403 : Blo 702318 2377403 := bstep (se 1 (by rfl) ⟨1783052, by rfl⟩ : syracuseStep 2377403 = 3566105) B3566105
theorem B1787579 : Blo 702318 1787579 := bstep (se 1 (by rfl) ⟨1340684, by rfl⟩ : syracuseStep 1787579 = 2681369) B2681369
theorem B706271 : Blo 702318 706271 := bstep (se 1 (by rfl) ⟨529703, by rfl⟩ : syracuseStep 706271 = 1059407) B1059407
theorem B1427179 : Blo 702318 1427179 := bstep (se 1 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 1427179 = 2140769) B2140769
theorem B3557357 : Blo 702318 3557357 := bstep (se 3 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 3557357 = 1334009) B1334009
theorem B2672621 : Blo 702318 2672621 := bstep (se 3 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 2672621 = 1002233) B1002233
theorem B13551745 : Blo 702318 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B1001737 : Blo 702318 1001737 := bstep (se 2 (by rfl) ⟨375651, by rfl⟩ : syracuseStep 1001737 = 751303) B751303
theorem B6015343 : Blo 702318 6015343 := bstep (se 1 (by rfl) ⟨4511507, by rfl⟩ : syracuseStep 6015343 = 9023015) B9023015
theorem B3000701 : Blo 702318 3000701 := bstep (se 3 (by rfl) ⟨562631, by rfl⟩ : syracuseStep 3000701 = 1125263) B1125263
theorem B3557843 : Blo 702318 3557843 := bstep (se 1 (by rfl) ⟨2668382, by rfl⟩ : syracuseStep 3557843 = 5336765) B5336765
theorem B2673107 : Blo 702318 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B5557015 : Blo 702318 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B3558167 : Blo 702318 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B8014625 : Blo 702318 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B838607 : Blo 702318 838607 := bstep (se 1 (by rfl) ⟨628955, by rfl⟩ : syracuseStep 838607 = 1257911) B1257911
theorem B6081911 : Blo 702318 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B4509047 : Blo 702318 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B2379347 : Blo 702318 2379347 := bstep (se 1 (by rfl) ⟨1784510, by rfl⟩ : syracuseStep 2379347 = 3569021) B3569021
theorem B3559787 : Blo 702318 3559787 := bstep (se 1 (by rfl) ⟨2669840, by rfl⟩ : syracuseStep 3559787 = 5339681) B5339681
theorem B2675051 : Blo 702318 2675051 := bstep (se 1 (by rfl) ⟨2006288, by rfl⟩ : syracuseStep 2675051 = 4012577) B4012577
theorem B2478511 : Blo 702318 2478511 := bstep (se 1 (by rfl) ⟨1858883, by rfl⟩ : syracuseStep 2478511 = 3717767) B3717767
theorem B6410771 : Blo 702318 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B1266239 : Blo 702318 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B5427809 : Blo 702318 5427809 := bstep (se 2 (by rfl) ⟨2035428, by rfl⟩ : syracuseStep 5427809 = 4070857) B4070857
theorem B4018841 : Blo 702318 4018841 := bstep (se 2 (by rfl) ⟨1507065, by rfl⟩ : syracuseStep 4018841 = 3014131) B3014131
theorem B2675855 : Blo 702318 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B3003641 : Blo 702318 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B3003743 : Blo 702318 3003743 := bstep (se 1 (by rfl) ⟨2252807, by rfl⟩ : syracuseStep 3003743 = 4505615) B4505615
theorem B5428613 : Blo 702318 5428613 := bstep (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) B1017865
theorem B5658017 : Blo 702318 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B1693115 : Blo 702318 1693115 := bstep (se 1 (by rfl) ⟨1269836, by rfl⟩ : syracuseStep 1693115 = 2539673) B2539673
theorem B8017541 : Blo 702318 8017541 := bstep (se 4 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 8017541 = 1503289) B1503289
theorem B1267435 : Blo 702318 1267435 := bstep (se 1 (by rfl) ⟨950576, by rfl⟩ : syracuseStep 1267435 = 1901153) B1901153
theorem B1857287 : Blo 702318 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B3561245 : Blo 702318 3561245 := bstep (se 3 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 3561245 = 1335467) B1335467
theorem B18339635 : Blo 702318 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B4512023 : Blo 702318 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B2382263 : Blo 702318 2382263 := bstep (se 1 (by rfl) ⟨1786697, by rfl⟩ : syracuseStep 2382263 = 3573395) B3573395
theorem B1464895 : Blo 702318 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B4020799 : Blo 702318 4020799 := bstep (se 1 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 4020799 = 6031199) B6031199
theorem B6019717 : Blo 702318 6019717 := bstep (se 4 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 6019717 = 1128697) B1128697
theorem B6773381 : Blo 702318 6773381 := bstep (se 4 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 6773381 = 1270009) B1270009
theorem B2677495 : Blo 702318 2677495 := bstep (se 1 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 2677495 = 4016243) B4016243
theorem B2677799 : Blo 702318 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B3660923 : Blo 702318 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B6085853 : Blo 702318 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B1694969 : Blo 702318 1694969 := bstep (se 2 (by rfl) ⟨635613, by rfl⟩ : syracuseStep 1694969 = 1271227) B1271227
theorem B12050369 : Blo 702318 12050369 := bstep (se 2 (by rfl) ⟨4518888, by rfl⟩ : syracuseStep 12050369 = 9037777) B9037777
theorem B1073839 : Blo 702318 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B4056263 : Blo 702318 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B1696987 : Blo 702318 1696987 := bstep (se 1 (by rfl) ⟨1272740, by rfl⟩ : syracuseStep 1696987 = 2545481) B2545481
theorem B6022451 : Blo 702318 6022451 := bstep (se 1 (by rfl) ⟨4516838, by rfl⟩ : syracuseStep 6022451 = 9033677) B9033677
theorem B1271531 : Blo 702318 1271531 := bstep (se 1 (by rfl) ⟨953648, by rfl⟩ : syracuseStep 1271531 = 1907297) B1907297
theorem B2254679 : Blo 702318 2254679 := bstep (se 1 (by rfl) ⟨1691009, by rfl⟩ : syracuseStep 2254679 = 3382019) B3382019
theorem B3008765 : Blo 702318 3008765 := bstep (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) B1128287
theorem B1337609 : Blo 702318 1337609 := bstep (se 2 (by rfl) ⟨501603, by rfl⟩ : syracuseStep 1337609 = 1003207) B1003207
theorem B9038141 : Blo 702318 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B15231361 : Blo 702318 15231361 := bstep (se 2 (by rfl) ⟨5711760, by rfl⟩ : syracuseStep 15231361 = 11423521) B11423521
theorem B1501615 : Blo 702318 1501615 := bstep (se 1 (by rfl) ⟨1126211, by rfl⟩ : syracuseStep 1501615 = 2252423) B2252423
theorem B1829623 : Blo 702318 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B4582415 : Blo 702318 4582415 := bstep (se 1 (by rfl) ⟨3436811, by rfl⟩ : syracuseStep 4582415 = 6873623) B6873623
theorem B7334993 : Blo 702318 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B3566915 : Blo 702318 3566915 := bstep (se 1 (by rfl) ⟨2675186, by rfl⟩ : syracuseStep 3566915 = 5350373) B5350373
theorem B1502803 : Blo 702318 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B9629293 : Blo 702318 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B1339067 : Blo 702318 1339067 := bstep (se 1 (by rfl) ⟨1004300, by rfl⟩ : syracuseStep 1339067 = 2008601) B2008601
theorem B3567401 : Blo 702318 3567401 := bstep (se 2 (by rfl) ⟨1337775, by rfl⟩ : syracuseStep 3567401 = 2675551) B2675551
theorem B4518251 : Blo 702318 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B4879001 : Blo 702318 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B28865393 : Blo 702318 28865393 := bstep (se 2 (by rfl) ⟨10824522, by rfl⟩ : syracuseStep 28865393 = 21649045) B21649045
theorem B2257895 : Blo 702318 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B3568697 : Blo 702318 3568697 := bstep (se 2 (by rfl) ⟨1338261, by rfl⟩ : syracuseStep 3568697 = 2676523) B2676523
theorem B15201427 : Blo 702318 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B1504649 : Blo 702318 1504649 := bstep (se 2 (by rfl) ⟨564243, by rfl⟩ : syracuseStep 1504649 = 1128487) B1128487
theorem B4519709 : Blo 702318 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B12843143 : Blo 702318 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B1898927 : Blo 702318 1898927 := bstep (se 1 (by rfl) ⟨1424195, by rfl⟩ : syracuseStep 1898927 = 2848391) B2848391
theorem B752123 : Blo 702318 752123 := bstep (se 1 (by rfl) ⟨564092, by rfl⟩ : syracuseStep 752123 = 1128185) B1128185
theorem B4291145 : Blo 702318 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B3570803 : Blo 702318 3570803 := bstep (se 1 (by rfl) ⟨2678102, by rfl⟩ : syracuseStep 3570803 = 5356205) B5356205
theorem B7306363 : Blo 702318 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B9043109 : Blo 702318 9043109 := bstep (se 4 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 9043109 = 1695583) B1695583
theorem B1899769 : Blo 702318 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B1506809 : Blo 702318 1506809 := bstep (se 2 (by rfl) ⟨565053, by rfl⟩ : syracuseStep 1506809 = 1130107) B1130107
theorem B753247 : Blo 702318 753247 := bstep (se 1 (by rfl) ⟨564935, by rfl⟩ : syracuseStep 753247 = 1129871) B1129871
theorem B12844889 : Blo 702318 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B1507177 : Blo 702318 1507177 := bstep (se 2 (by rfl) ⟨565191, by rfl⟩ : syracuseStep 1507177 = 1130383) B1130383
theorem B3571613 : Blo 702318 3571613 := bstep (se 3 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 3571613 = 1339355) B1339355
theorem B6783527 : Blo 702318 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B9011897 : Blo 702318 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B10158857 : Blo 702318 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B5342597 : Blo 702318 5342597 := bstep (se 4 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 5342597 = 1001737) B1001737
theorem B3376637 : Blo 702318 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B2000467 : Blo 702318 2000467 := bstep (se 1 (by rfl) ⟨1500350, by rfl⟩ : syracuseStep 2000467 = 3000701) B3000701
theorem B2262649 : Blo 702318 2262649 := bstep (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) B1696987
theorem B5343083 : Blo 702318 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B1902905 : Blo 702318 1902905 := bstep (se 2 (by rfl) ⟨713589, by rfl⟩ : syracuseStep 1902905 = 1427179) B1427179
theorem B2002153 : Blo 702318 2002153 := bstep (se 2 (by rfl) ⟨750807, by rfl⟩ : syracuseStep 2002153 = 1501615) B1501615
theorem B2002427 : Blo 702318 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B2002495 : Blo 702318 2002495 := bstep (se 1 (by rfl) ⟨1501871, by rfl⟩ : syracuseStep 2002495 = 3003743) B3003743
theorem B51973771 : Blo 702318 51973771 := bstep (se 1 (by rfl) ⟨38980328, by rfl⟩ : syracuseStep 51973771 = 77960657) B77960657
theorem B5345027 : Blo 702318 5345027 := bstep (se 1 (by rfl) ⟨4008770, by rfl⟩ : syracuseStep 5345027 = 8017541) B8017541
theorem B4067347 : Blo 702318 4067347 := bstep (se 1 (by rfl) ⟨3050510, by rfl⟩ : syracuseStep 4067347 = 6101021) B6101021
theorem B4952765 : Blo 702318 4952765 := bstep (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) B1857287
theorem B2003737 : Blo 702318 2003737 := bstep (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) B1502803
theorem B1053551 : Blo 702318 1053551 := bstep (se 1 (by rfl) ⟨790163, by rfl⟩ : syracuseStep 1053551 = 1580327) B1580327
theorem B1053803 : Blo 702318 1053803 := bstep (se 1 (by rfl) ⟨790352, by rfl⟩ : syracuseStep 1053803 = 1580705) B1580705
theorem B8131691 : Blo 702318 8131691 := bstep (se 1 (by rfl) ⟨6098768, by rfl⟩ : syracuseStep 8131691 = 12197537) B12197537
theorem B8033579 : Blo 702318 8033579 := bstep (se 1 (by rfl) ⟨6025184, by rfl⟩ : syracuseStep 8033579 = 12050369) B12050369
theorem B1054043 : Blo 702318 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B1054319 : Blo 702318 1054319 := bstep (se 1 (by rfl) ⟨790739, by rfl⟩ : syracuseStep 1054319 = 1581479) B1581479
theorem B792175 : Blo 702318 792175 := bstep (se 1 (by rfl) ⟨594131, by rfl⟩ : syracuseStep 792175 = 1188263) B1188263
theorem B1185401 : Blo 702318 1185401 := bstep (se 2 (by rfl) ⟨444525, by rfl⟩ : syracuseStep 1185401 = 889051) B889051
theorem B7607981 : Blo 702318 7607981 := bstep (se 3 (by rfl) ⟨1426496, by rfl⟩ : syracuseStep 7607981 = 2852993) B2852993
theorem B1054391 : Blo 702318 1054391 := bstep (se 1 (by rfl) ⟨790793, by rfl⟩ : syracuseStep 1054391 = 1581587) B1581587
theorem B1054427 : Blo 702318 1054427 := bstep (se 1 (by rfl) ⟨790820, by rfl⟩ : syracuseStep 1054427 = 1581641) B1581641
theorem B792283 : Blo 702318 792283 := bstep (se 1 (by rfl) ⟨594212, by rfl⟩ : syracuseStep 792283 = 1188425) B1188425
theorem B14423903 : Blo 702318 14423903 := bstep (se 1 (by rfl) ⟨10817927, by rfl⟩ : syracuseStep 14423903 = 21635855) B21635855
theorem B1054601 : Blo 702318 1054601 := bstep (se 2 (by rfl) ⟨395475, by rfl⟩ : syracuseStep 1054601 = 790951) B790951
theorem B1054703 : Blo 702318 1054703 := bstep (se 1 (by rfl) ⟨791027, by rfl⟩ : syracuseStep 1054703 = 1582055) B1582055
theorem B1185887 : Blo 702318 1185887 := bstep (se 1 (by rfl) ⟨889415, by rfl⟩ : syracuseStep 1185887 = 1778831) B1778831
theorem B5347457 : Blo 702318 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B1054955 : Blo 702318 1054955 := bstep (se 1 (by rfl) ⟨791216, by rfl⟩ : syracuseStep 1054955 = 1582433) B1582433
theorem B1055015 : Blo 702318 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B1055099 : Blo 702318 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B1055369 : Blo 702318 1055369 := bstep (se 2 (by rfl) ⟨395763, by rfl⟩ : syracuseStep 1055369 = 791527) B791527
theorem B2005661 : Blo 702318 2005661 := bstep (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) B752123
theorem B9050899 : Blo 702318 9050899 := bstep (se 1 (by rfl) ⟨6788174, by rfl⟩ : syracuseStep 9050899 = 13576349) B13576349
theorem B1055543 : Blo 702318 1055543 := bstep (se 1 (by rfl) ⟨791657, by rfl⟩ : syracuseStep 1055543 = 1583315) B1583315
theorem B1055579 : Blo 702318 1055579 := bstep (se 1 (by rfl) ⟨791684, by rfl⟩ : syracuseStep 1055579 = 1583369) B1583369
theorem B891739 : Blo 702318 891739 := bstep (se 1 (by rfl) ⟨668804, by rfl⟩ : syracuseStep 891739 = 1337609) B1337609
theorem B793435 : Blo 702318 793435 := bstep (se 1 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 793435 = 1190153) B1190153
theorem B1055723 : Blo 702318 1055723 := bstep (se 1 (by rfl) ⟨791792, by rfl⟩ : syracuseStep 1055723 = 1583585) B1583585
theorem B1907783 : Blo 702318 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B1055927 : Blo 702318 1055927 := bstep (se 1 (by rfl) ⟨791945, by rfl⟩ : syracuseStep 1055927 = 1583891) B1583891
theorem B3054943 : Blo 702318 3054943 := bstep (se 1 (by rfl) ⟨2291207, by rfl⟩ : syracuseStep 3054943 = 4582415) B4582415
theorem B1580399 : Blo 702318 1580399 := bstep (se 1 (by rfl) ⟨1185299, by rfl⟩ : syracuseStep 1580399 = 2370599) B2370599
theorem B1187183 : Blo 702318 1187183 := bstep (se 1 (by rfl) ⟨890387, by rfl⟩ : syracuseStep 1187183 = 1780775) B1780775
theorem B1056167 : Blo 702318 1056167 := bstep (se 1 (by rfl) ⟨792125, by rfl⟩ : syracuseStep 1056167 = 1584251) B1584251
theorem B1056251 : Blo 702318 1056251 := bstep (se 1 (by rfl) ⟨792188, by rfl⟩ : syracuseStep 1056251 = 1584377) B1584377
theorem B1187419 : Blo 702318 1187419 := bstep (se 1 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 1187419 = 1781129) B1781129
theorem B1056347 : Blo 702318 1056347 := bstep (se 1 (by rfl) ⟨792260, by rfl⟩ : syracuseStep 1056347 = 1584521) B1584521
theorem B1580687 : Blo 702318 1580687 := bstep (se 1 (by rfl) ⟨1185515, by rfl⟩ : syracuseStep 1580687 = 2371031) B2371031
theorem B1056431 : Blo 702318 1056431 := bstep (se 1 (by rfl) ⟨792323, by rfl⟩ : syracuseStep 1056431 = 1584647) B1584647
theorem B1580777 : Blo 702318 1580777 := bstep (se 2 (by rfl) ⟨592791, by rfl⟩ : syracuseStep 1580777 = 1185583) B1185583
theorem B1187561 : Blo 702318 1187561 := bstep (se 2 (by rfl) ⟨445335, by rfl⟩ : syracuseStep 1187561 = 890671) B890671
theorem B1056551 : Blo 702318 1056551 := bstep (se 1 (by rfl) ⟨792413, by rfl⟩ : syracuseStep 1056551 = 1584827) B1584827
theorem B892711 : Blo 702318 892711 := bstep (se 1 (by rfl) ⟨669533, by rfl⟩ : syracuseStep 892711 = 1339067) B1339067
theorem B794407 : Blo 702318 794407 := bstep (se 1 (by rfl) ⟨595805, by rfl⟩ : syracuseStep 794407 = 1191611) B1191611
theorem B1056635 : Blo 702318 1056635 := bstep (se 1 (by rfl) ⟨792476, by rfl⟩ : syracuseStep 1056635 = 1584953) B1584953
theorem B2236285 : Blo 702318 2236285 := bstep (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) B838607
theorem B28942393 : Blo 702318 28942393 := bstep (se 2 (by rfl) ⟨10853397, by rfl⟩ : syracuseStep 28942393 = 21706795) B21706795
theorem B1057055 : Blo 702318 1057055 := bstep (se 1 (by rfl) ⟨792791, by rfl⟩ : syracuseStep 1057055 = 1585583) B1585583
theorem B10166579 : Blo 702318 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B1057079 : Blo 702318 1057079 := bstep (se 1 (by rfl) ⟨792809, by rfl⟩ : syracuseStep 1057079 = 1585619) B1585619
theorem B1057151 : Blo 702318 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B3252667 : Blo 702318 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B1057223 : Blo 702318 1057223 := bstep (se 1 (by rfl) ⟨792917, by rfl⟩ : syracuseStep 1057223 = 1585835) B1585835
theorem B3383785 : Blo 702318 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B19243595 : Blo 702318 19243595 := bstep (se 1 (by rfl) ⟨14432696, by rfl⟩ : syracuseStep 19243595 = 28865393) B28865393
theorem B1581803 : Blo 702318 1581803 := bstep (se 1 (by rfl) ⟨1186352, by rfl⟩ : syracuseStep 1581803 = 2372705) B2372705
theorem B1188587 : Blo 702318 1188587 := bstep (se 1 (by rfl) ⟨891440, by rfl⟩ : syracuseStep 1188587 = 1782881) B1782881
theorem B1057577 : Blo 702318 1057577 := bstep (se 2 (by rfl) ⟨396591, by rfl⟩ : syracuseStep 1057577 = 793183) B793183
theorem B1057583 : Blo 702318 1057583 := bstep (se 1 (by rfl) ⟨793187, by rfl⟩ : syracuseStep 1057583 = 1586375) B1586375
theorem B1057703 : Blo 702318 1057703 := bstep (se 1 (by rfl) ⟨793277, by rfl⟩ : syracuseStep 1057703 = 1586555) B1586555
theorem B1057787 : Blo 702318 1057787 := bstep (se 1 (by rfl) ⟨793340, by rfl⟩ : syracuseStep 1057787 = 1586681) B1586681
theorem B1057847 : Blo 702318 1057847 := bstep (se 1 (by rfl) ⟨793385, by rfl⟩ : syracuseStep 1057847 = 1586771) B1586771
theorem B1189039 : Blo 702318 1189039 := bstep (se 1 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 1189039 = 1783559) B1783559
theorem B1057967 : Blo 702318 1057967 := bstep (se 1 (by rfl) ⟨793475, by rfl⟩ : syracuseStep 1057967 = 1586951) B1586951
theorem B8562095 : Blo 702318 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B9741817 : Blo 702318 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B1058375 : Blo 702318 1058375 := bstep (se 1 (by rfl) ⟨793781, by rfl⟩ : syracuseStep 1058375 = 1587563) B1587563
theorem B1582703 : Blo 702318 1582703 := bstep (se 1 (by rfl) ⟨1187027, by rfl⟩ : syracuseStep 1582703 = 2374055) B2374055
theorem B2533025 : Blo 702318 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B1779367 : Blo 702318 1779367 := bstep (se 1 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 1779367 = 2669051) B2669051
theorem B1058471 : Blo 702318 1058471 := bstep (se 1 (by rfl) ⟨793853, by rfl⟩ : syracuseStep 1058471 = 1587707) B1587707
theorem B1189559 : Blo 702318 1189559 := bstep (se 1 (by rfl) ⟨892169, by rfl⟩ : syracuseStep 1189559 = 1784339) B1784339
theorem B1582811 : Blo 702318 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B2860763 : Blo 702318 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B1058555 : Blo 702318 1058555 := bstep (se 1 (by rfl) ⟨793916, by rfl⟩ : syracuseStep 1058555 = 1587833) B1587833
theorem B1058591 : Blo 702318 1058591 := bstep (se 1 (by rfl) ⟨793943, by rfl⟩ : syracuseStep 1058591 = 1587887) B1587887
theorem B2565949 : Blo 702318 2565949 := bstep (se 3 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 2565949 = 962231) B962231
theorem B1058639 : Blo 702318 1058639 := bstep (se 1 (by rfl) ⟨793979, by rfl⟩ : syracuseStep 1058639 = 1587959) B1587959
theorem B1058759 : Blo 702318 1058759 := bstep (se 1 (by rfl) ⟨794069, by rfl⟩ : syracuseStep 1058759 = 1588139) B1588139
theorem B1059113 : Blo 702318 1059113 := bstep (se 2 (by rfl) ⟨397167, by rfl⟩ : syracuseStep 1059113 = 794335) B794335
theorem B1780015 : Blo 702318 1780015 := bstep (se 1 (by rfl) ⟨1335011, by rfl⟩ : syracuseStep 1780015 = 2670023) B2670023
theorem B1059119 : Blo 702318 1059119 := bstep (se 1 (by rfl) ⟨794339, by rfl⟩ : syracuseStep 1059119 = 1588679) B1588679
theorem B13183397 : Blo 702318 13183397 := bstep (se 4 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 13183397 = 2471887) B2471887
theorem B2009569 : Blo 702318 2009569 := bstep (se 2 (by rfl) ⟨753588, by rfl⟩ : syracuseStep 2009569 = 1507177) B1507177
theorem B1059359 : Blo 702318 1059359 := bstep (se 1 (by rfl) ⟨794519, by rfl⟩ : syracuseStep 1059359 = 1589039) B1589039
theorem B8563259 : Blo 702318 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B1583927 : Blo 702318 1583927 := bstep (se 1 (by rfl) ⟨1187945, by rfl⟩ : syracuseStep 1583927 = 2375891) B2375891
theorem B1190747 : Blo 702318 1190747 := bstep (se 1 (by rfl) ⟨893060, by rfl⟩ : syracuseStep 1190747 = 1786121) B1786121
theorem B1584107 : Blo 702318 1584107 := bstep (se 1 (by rfl) ⟨1188080, by rfl⟩ : syracuseStep 1584107 = 2376161) B2376161
theorem B1190983 : Blo 702318 1190983 := bstep (se 1 (by rfl) ⟨893237, by rfl⟩ : syracuseStep 1190983 = 1786475) B1786475
theorem B2010491 : Blo 702318 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B1191415 : Blo 702318 1191415 := bstep (se 1 (by rfl) ⟨893561, by rfl⟩ : syracuseStep 1191415 = 1787123) B1787123
theorem B1781311 : Blo 702318 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B2371247 : Blo 702318 2371247 := bstep (se 1 (by rfl) ⟨1778435, by rfl⟩ : syracuseStep 2371247 = 3556871) B3556871
theorem B1781423 : Blo 702318 1781423 := bstep (se 1 (by rfl) ⟨1336067, by rfl⟩ : syracuseStep 1781423 = 2672135) B2672135
theorem B1584935 : Blo 702318 1584935 := bstep (se 1 (by rfl) ⟨1188701, by rfl⟩ : syracuseStep 1584935 = 2377403) B2377403
theorem B1191719 : Blo 702318 1191719 := bstep (se 1 (by rfl) ⟨893789, by rfl⟩ : syracuseStep 1191719 = 1787579) B1787579
theorem B10170269 : Blo 702318 10170269 := bstep (se 3 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 10170269 = 3813851) B3813851
theorem B2371571 : Blo 702318 2371571 := bstep (se 1 (by rfl) ⟨1778678, by rfl⟩ : syracuseStep 2371571 = 3557357) B3557357
theorem B1781747 : Blo 702318 1781747 := bstep (se 1 (by rfl) ⟨1336310, by rfl⟩ : syracuseStep 1781747 = 2672621) B2672621
theorem B2371895 : Blo 702318 2371895 := bstep (se 1 (by rfl) ⟨1778921, by rfl⟩ : syracuseStep 2371895 = 3557843) B3557843
theorem B1782071 : Blo 702318 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B2372111 : Blo 702318 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B1585961 : Blo 702318 1585961 := bstep (se 2 (by rfl) ⟨594735, by rfl⟩ : syracuseStep 1585961 = 1189471) B1189471
theorem B5714813 : Blo 702318 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B1586231 : Blo 702318 1586231 := bstep (se 1 (by rfl) ⟨1189673, by rfl⟩ : syracuseStep 1586231 = 2379347) B2379347
theorem B2667593 : Blo 702318 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B1586249 : Blo 702318 1586249 := bstep (se 2 (by rfl) ⟨594843, by rfl⟩ : syracuseStep 1586249 = 1189687) B1189687
theorem B8008793 : Blo 702318 8008793 := bstep (se 2 (by rfl) ⟨3003297, by rfl⟩ : syracuseStep 8008793 = 6006595) B6006595
theorem B6599879 : Blo 702318 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B18068993 : Blo 702318 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B2373191 : Blo 702318 2373191 := bstep (se 1 (by rfl) ⟨1779893, by rfl⟩ : syracuseStep 2373191 = 3559787) B3559787
theorem B1783367 : Blo 702318 1783367 := bstep (se 1 (by rfl) ⟨1337525, by rfl⟩ : syracuseStep 1783367 = 2675051) B2675051
theorem B4273847 : Blo 702318 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 702318 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B3618539 : Blo 702318 3618539 := bstep (se 1 (by rfl) ⟨2713904, by rfl⟩ : syracuseStep 3618539 = 5427809) B5427809
theorem B8042327 : Blo 702318 8042327 := bstep (se 1 (by rfl) ⟨6031745, by rfl⟩ : syracuseStep 8042327 = 12063491) B12063491
theorem B702447 : Blo 702318 702447 := bstep (se 1 (by rfl) ⟨526835, by rfl⟩ : syracuseStep 702447 = 1053671) B1053671
theorem B1783903 : Blo 702318 1783903 := bstep (se 1 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 1783903 = 2675855) B2675855
theorem B702619 : Blo 702318 702619 := bstep (se 1 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 702619 = 1053929) B1053929
theorem B702655 : Blo 702318 702655 := bstep (se 1 (by rfl) ⟨526991, by rfl⟩ : syracuseStep 702655 = 1053983) B1053983
theorem B3619075 : Blo 702318 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B1128743 : Blo 702318 1128743 := bstep (se 1 (by rfl) ⟨846557, by rfl⟩ : syracuseStep 1128743 = 1693115) B1693115
theorem B702767 : Blo 702318 702767 := bstep (se 1 (by rfl) ⟨527075, by rfl⟩ : syracuseStep 702767 = 1054151) B1054151
theorem B2439497 : Blo 702318 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B4503923 : Blo 702318 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B2406779 : Blo 702318 2406779 := bstep (se 1 (by rfl) ⟨1805084, by rfl⟩ : syracuseStep 2406779 = 3610169) B3610169
theorem B15088045 : Blo 702318 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B2374163 : Blo 702318 2374163 := bstep (se 1 (by rfl) ⟨1780622, by rfl⟩ : syracuseStep 2374163 = 3561245) B3561245
theorem B703003 : Blo 702318 703003 := bstep (se 1 (by rfl) ⟨527252, by rfl⟩ : syracuseStep 703003 = 1054505) B1054505
theorem B703007 : Blo 702318 703007 := bstep (se 1 (by rfl) ⟨527255, by rfl⟩ : syracuseStep 703007 = 1054511) B1054511
theorem B11123459 : Blo 702318 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B29637413 : Blo 702318 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B703323 : Blo 702318 703323 := bstep (se 1 (by rfl) ⟨527492, by rfl⟩ : syracuseStep 703323 = 1054985) B1054985
theorem B703391 : Blo 702318 703391 := bstep (se 1 (by rfl) ⟨527543, by rfl⟩ : syracuseStep 703391 = 1055087) B1055087
theorem B1588175 : Blo 702318 1588175 := bstep (se 1 (by rfl) ⟨1191131, by rfl⟩ : syracuseStep 1588175 = 2382263) B2382263
theorem B1588193 : Blo 702318 1588193 := bstep (se 2 (by rfl) ⟨595572, by rfl⟩ : syracuseStep 1588193 = 1191145) B1191145
theorem B1719265 : Blo 702318 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B1588265 : Blo 702318 1588265 := bstep (se 2 (by rfl) ⟨595599, by rfl⟩ : syracuseStep 1588265 = 1191199) B1191199
theorem B703535 : Blo 702318 703535 := bstep (se 1 (by rfl) ⟨527651, by rfl⟩ : syracuseStep 703535 = 1055303) B1055303
theorem B703559 : Blo 702318 703559 := bstep (se 1 (by rfl) ⟨527669, by rfl⟩ : syracuseStep 703559 = 1055339) B1055339
theorem B703711 : Blo 702318 703711 := bstep (se 1 (by rfl) ⟨527783, by rfl⟩ : syracuseStep 703711 = 1055567) B1055567
theorem B8043785 : Blo 702318 8043785 := bstep (se 2 (by rfl) ⟨3016419, by rfl⟩ : syracuseStep 8043785 = 6032839) B6032839
theorem B1785199 : Blo 702318 1785199 := bstep (se 1 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 1785199 = 2677799) B2677799
theorem B48905693 : Blo 702318 48905693 := bstep (se 3 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 48905693 = 18339635) B18339635
theorem B703975 : Blo 702318 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B1129979 : Blo 702318 1129979 := bstep (se 1 (by rfl) ⟨847484, by rfl⟩ : syracuseStep 1129979 = 1694969) B1694969
theorem B704091 : Blo 702318 704091 := bstep (se 1 (by rfl) ⟨528068, by rfl⟩ : syracuseStep 704091 = 1056137) B1056137
theorem B704327 : Blo 702318 704327 := bstep (se 1 (by rfl) ⟨528245, by rfl⟩ : syracuseStep 704327 = 1056491) B1056491
theorem B704479 : Blo 702318 704479 := bstep (se 1 (by rfl) ⟨528359, by rfl⟩ : syracuseStep 704479 = 1056719) B1056719
theorem B3391627 : Blo 702318 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B704743 : Blo 702318 704743 := bstep (se 1 (by rfl) ⟨528557, by rfl⟩ : syracuseStep 704743 = 1057115) B1057115
theorem B704895 : Blo 702318 704895 := bstep (se 1 (by rfl) ⟨528671, by rfl⟩ : syracuseStep 704895 = 1057343) B1057343
theorem B704975 : Blo 702318 704975 := bstep (se 1 (by rfl) ⟨528731, by rfl⟩ : syracuseStep 704975 = 1057463) B1057463
theorem B705127 : Blo 702318 705127 := bstep (se 1 (by rfl) ⟨528845, by rfl⟩ : syracuseStep 705127 = 1057691) B1057691
theorem B2704175 : Blo 702318 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B705391 : Blo 702318 705391 := bstep (se 1 (by rfl) ⟨529043, by rfl⟩ : syracuseStep 705391 = 1058087) B1058087
theorem B4014967 : Blo 702318 4014967 := bstep (se 1 (by rfl) ⟨3011225, by rfl⟩ : syracuseStep 4014967 = 6022451) B6022451
theorem B8111015 : Blo 702318 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B705447 : Blo 702318 705447 := bstep (se 1 (by rfl) ⟨529085, by rfl⟩ : syracuseStep 705447 = 1058171) B1058171
theorem B705531 : Blo 702318 705531 := bstep (se 1 (by rfl) ⟨529148, by rfl⟩ : syracuseStep 705531 = 1058297) B1058297
theorem B705599 : Blo 702318 705599 := bstep (se 1 (by rfl) ⟨529199, by rfl⟩ : syracuseStep 705599 = 1058399) B1058399
theorem B2376809 : Blo 702318 2376809 := bstep (se 2 (by rfl) ⟨891303, by rfl⟩ : syracuseStep 2376809 = 1782607) B1782607
theorem B705743 : Blo 702318 705743 := bstep (se 1 (by rfl) ⟨529307, by rfl⟩ : syracuseStep 705743 = 1058615) B1058615
theorem B705947 : Blo 702318 705947 := bstep (se 1 (by rfl) ⟨529460, by rfl⟩ : syracuseStep 705947 = 1058921) B1058921
theorem B20268569 : Blo 702318 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B706159 : Blo 702318 706159 := bstep (se 1 (by rfl) ⟨529619, by rfl⟩ : syracuseStep 706159 = 1059239) B1059239
theorem B706215 : Blo 702318 706215 := bstep (se 1 (by rfl) ⟨529661, by rfl⟩ : syracuseStep 706215 = 1059323) B1059323
theorem B706299 : Blo 702318 706299 := bstep (se 1 (by rfl) ⟨529724, by rfl⟩ : syracuseStep 706299 = 1059449) B1059449
theorem B3393359 : Blo 702318 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2410337 : Blo 702318 2410337 := bstep (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) B1807753
theorem B2377673 : Blo 702318 2377673 := bstep (se 2 (by rfl) ⟨891627, by rfl⟩ : syracuseStep 2377673 = 1783255) B1783255
theorem B2377943 : Blo 702318 2377943 := bstep (se 1 (by rfl) ⟨1783457, by rfl⟩ : syracuseStep 2377943 = 3566915) B3566915
theorem B1689913 : Blo 702318 1689913 := bstep (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) B1267435
theorem B2673121 : Blo 702318 2673121 := bstep (se 2 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 2673121 = 2004841) B2004841
theorem B2378267 : Blo 702318 2378267 := bstep (se 1 (by rfl) ⟨1783700, by rfl⟩ : syracuseStep 2378267 = 3567401) B3567401
theorem B2379131 : Blo 702318 2379131 := bstep (se 1 (by rfl) ⟨1784348, by rfl⟩ : syracuseStep 2379131 = 3568697) B3568697
theorem B1068457 : Blo 702318 1068457 := bstep (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) B801343
theorem B1953193 : Blo 702318 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B5361065 : Blo 702318 5361065 := bstep (se 2 (by rfl) ⟨2010399, by rfl⟩ : syracuseStep 5361065 = 4020799) B4020799
theorem B1003099 : Blo 702318 1003099 := bstep (se 1 (by rfl) ⟨752324, by rfl⟩ : syracuseStep 1003099 = 1504649) B1504649
theorem B4018157 : Blo 702318 4018157 := bstep (se 3 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 4018157 = 1506809) B1506809
theorem B4509715 : Blo 702318 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B1265951 : Blo 702318 1265951 := bstep (se 1 (by rfl) ⟨949463, by rfl⟩ : syracuseStep 1265951 = 1898927) B1898927
theorem B8573485 : Blo 702318 8573485 := bstep (se 3 (by rfl) ⟨1607528, by rfl⟩ : syracuseStep 8573485 = 3215057) B3215057
theorem B2380535 : Blo 702318 2380535 := bstep (se 1 (by rfl) ⟨1785401, by rfl⟩ : syracuseStep 2380535 = 3570803) B3570803
theorem B1004329 : Blo 702318 1004329 := bstep (se 2 (by rfl) ⟨376623, by rfl⟩ : syracuseStep 1004329 = 753247) B753247
theorem B19256399 : Blo 702318 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B2381075 : Blo 702318 2381075 := bstep (se 1 (by rfl) ⟨1785806, by rfl⟩ : syracuseStep 2381075 = 3571613) B3571613
theorem B19518907 : Blo 702318 19518907 := bstep (se 1 (by rfl) ⟨14639180, by rfl⟩ : syracuseStep 19518907 = 29278361) B29278361
theorem B20305475 : Blo 702318 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B1234543 : Blo 702318 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B9164411 : Blo 702318 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B1005223 : Blo 702318 1005223 := bstep (se 1 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 1005223 = 1507835) B1507835
theorem B2381615 : Blo 702318 2381615 := bstep (se 1 (by rfl) ⟨1786211, by rfl⟩ : syracuseStep 2381615 = 3572423) B3572423
theorem B3004391 : Blo 702318 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B1431785 : Blo 702318 1431785 := bstep (se 2 (by rfl) ⟨536919, by rfl⟩ : syracuseStep 1431785 = 1073839) B1073839
theorem B10148125 : Blo 702318 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B4021073 : Blo 702318 4021073 := bstep (se 2 (by rfl) ⟨1507902, by rfl⟩ : syracuseStep 4021073 = 3015805) B3015805
theorem B2251745 : Blo 702318 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B4054607 : Blo 702318 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1334875 : Blo 702318 1334875 := bstep (se 1 (by rfl) ⟨1001156, by rfl⟩ : syracuseStep 1334875 = 2002313) B2002313
theorem B2383451 : Blo 702318 2383451 := bstep (se 1 (by rfl) ⟨1787588, by rfl⟩ : syracuseStep 2383451 = 3575177) B3575177
theorem B6021053 : Blo 702318 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B4022531 : Blo 702318 4022531 := bstep (se 1 (by rfl) ⟨3016898, by rfl⟩ : syracuseStep 4022531 = 6033797) B6033797
theorem B2679227 : Blo 702318 2679227 := bstep (se 1 (by rfl) ⟨2009420, by rfl⟩ : syracuseStep 2679227 = 4018841) B4018841
theorem B8020457 : Blo 702318 8020457 := bstep (se 2 (by rfl) ⟨3007671, by rfl⟩ : syracuseStep 8020457 = 6015343) B6015343
theorem B20308481 : Blo 702318 20308481 := bstep (se 2 (by rfl) ⟨7615680, by rfl⟩ : syracuseStep 20308481 = 15231361) B15231361
theorem B3008015 : Blo 702318 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B4515587 : Blo 702318 4515587 := bstep (se 1 (by rfl) ⟨3386690, by rfl⟩ : syracuseStep 4515587 = 6773381) B6773381
theorem B12839057 : Blo 702318 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B4057235 : Blo 702318 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B1337647 : Blo 702318 1337647 := bstep (se 1 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 1337647 = 2006471) B2006471
theorem B8580097 : Blo 702318 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B3304681 : Blo 702318 3304681 := bstep (se 2 (by rfl) ⟨1239255, by rfl⟩ : syracuseStep 3304681 = 2478511) B2478511
theorem B8023373 : Blo 702318 8023373 := bstep (se 3 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 8023373 = 3008765) B3008765
theorem B847687 : Blo 702318 847687 := bstep (se 1 (by rfl) ⟨635765, by rfl⟩ : syracuseStep 847687 = 1271531) B1271531
theorem B2256779 : Blo 702318 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B1503119 : Blo 702318 1503119 := bstep (se 1 (by rfl) ⟨1127339, by rfl⟩ : syracuseStep 1503119 = 2254679) B2254679
theorem B6025427 : Blo 702318 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B9007433 : Blo 702318 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B3568211 : Blo 702318 3568211 := bstep (se 1 (by rfl) ⟨2676158, by rfl⟩ : syracuseStep 3568211 = 5352317) B5352317
theorem B1340479 : Blo 702318 1340479 := bstep (se 1 (by rfl) ⟨1005359, by rfl⟩ : syracuseStep 1340479 = 2010719) B2010719
theorem B750799 : Blo 702318 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B19559981 : Blo 702318 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B3012167 : Blo 702318 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B9762461 : Blo 702318 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B8026289 : Blo 702318 8026289 := bstep (se 2 (by rfl) ⟨3009858, by rfl⟩ : syracuseStep 8026289 = 6019717) B6019717
theorem B12024125 : Blo 702318 12024125 := bstep (se 3 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 12024125 = 4509047) B4509047
theorem B3569993 : Blo 702318 3569993 := bstep (se 2 (by rfl) ⟨1338747, by rfl⟩ : syracuseStep 3569993 = 2677495) B2677495
theorem B3013139 : Blo 702318 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B6028739 : Blo 702318 6028739 := bstep (se 1 (by rfl) ⟨4521554, by rfl⟩ : syracuseStep 6028739 = 9043109) B9043109
theorem B5340653 : Blo 702318 5340653 := bstep (se 3 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 5340653 = 2002745) B2002745
theorem B4522169 : Blo 702318 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B4522351 : Blo 702318 4522351 := bstep (se 1 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 4522351 = 6783527) B6783527
theorem B1802783 : Blo 702318 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B5407343 : Blo 702318 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B2262239 : Blo 702318 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B1606891 : Blo 702318 1606891 := bstep (se 1 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 1606891 = 2410337) B2410337
theorem B9012869 : Blo 702318 9012869 := bstep (se 4 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 9012869 = 1689913) B1689913
theorem B3016865 : Blo 702318 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B3574043 : Blo 702318 3574043 := bstep (se 1 (by rfl) ⟨2680532, by rfl⟩ : syracuseStep 3574043 = 5361065) B5361065
theorem B13536983 : Blo 702318 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B790267 : Blo 702318 790267 := bstep (se 1 (by rfl) ⟨592700, by rfl⟩ : syracuseStep 790267 = 1185401) B1185401
theorem B11440129 : Blo 702318 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B790591 : Blo 702318 790591 := bstep (se 1 (by rfl) ⟨592943, by rfl⟩ : syracuseStep 790591 = 1185887) B1185887
theorem B954523 : Blo 702318 954523 := bstep (se 1 (by rfl) ⟨715892, by rfl⟩ : syracuseStep 954523 = 1431785) B1431785
theorem B1053599 : Blo 702318 1053599 := bstep (se 1 (by rfl) ⟨790199, by rfl⟩ : syracuseStep 1053599 = 1580399) B1580399
theorem B791455 : Blo 702318 791455 := bstep (se 1 (by rfl) ⟨593591, by rfl⟩ : syracuseStep 791455 = 1187183) B1187183
theorem B1053791 : Blo 702318 1053791 := bstep (se 1 (by rfl) ⟨790343, by rfl⟩ : syracuseStep 1053791 = 1580687) B1580687
theorem B1053851 : Blo 702318 1053851 := bstep (se 1 (by rfl) ⟨790388, by rfl⟩ : syracuseStep 1053851 = 1580777) B1580777
theorem B791707 : Blo 702318 791707 := bstep (se 1 (by rfl) ⟨593780, by rfl⟩ : syracuseStep 791707 = 1187561) B1187561
theorem B5346971 : Blo 702318 5346971 := bstep (se 1 (by rfl) ⟨4010228, by rfl⟩ : syracuseStep 5346971 = 8020457) B8020457
theorem B13538987 : Blo 702318 13538987 := bstep (se 1 (by rfl) ⟨10154240, by rfl⟩ : syracuseStep 13538987 = 20308481) B20308481
theorem B1054535 : Blo 702318 1054535 := bstep (se 1 (by rfl) ⟨790901, by rfl⟩ : syracuseStep 1054535 = 1581803) B1581803
theorem B792391 : Blo 702318 792391 := bstep (se 1 (by rfl) ⟨594293, by rfl⟩ : syracuseStep 792391 = 1188587) B1188587
theorem B5708063 : Blo 702318 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B2005343 : Blo 702318 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B1055135 : Blo 702318 1055135 := bstep (se 1 (by rfl) ⟨791351, by rfl⟩ : syracuseStep 1055135 = 1582703) B1582703
theorem B4004261 : Blo 702318 4004261 := bstep (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) B750799
theorem B793039 : Blo 702318 793039 := bstep (se 1 (by rfl) ⟨594779, by rfl⟩ : syracuseStep 793039 = 1189559) B1189559
theorem B1055207 : Blo 702318 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B8035037 : Blo 702318 8035037 := bstep (se 3 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 8035037 = 3013139) B3013139
theorem B8559371 : Blo 702318 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B8788931 : Blo 702318 8788931 := bstep (se 1 (by rfl) ⟨6591698, by rfl⟩ : syracuseStep 8788931 = 13183397) B13183397
theorem B5348429 : Blo 702318 5348429 := bstep (se 3 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 5348429 = 2005661) B2005661
theorem B1055951 : Blo 702318 1055951 := bstep (se 1 (by rfl) ⟨791963, by rfl⟩ : syracuseStep 1055951 = 1583927) B1583927
theorem B793831 : Blo 702318 793831 := bstep (se 1 (by rfl) ⟨595373, by rfl⟩ : syracuseStep 793831 = 1190747) B1190747
theorem B26025209 : Blo 702318 26025209 := bstep (se 2 (by rfl) ⟨9759453, by rfl⟩ : syracuseStep 26025209 = 19518907) B19518907
theorem B1056071 : Blo 702318 1056071 := bstep (se 1 (by rfl) ⟨792053, by rfl⟩ : syracuseStep 1056071 = 1584107) B1584107
theorem B1056233 : Blo 702318 1056233 := bstep (se 2 (by rfl) ⟨396087, by rfl⟩ : syracuseStep 1056233 = 792175) B792175
theorem B1646057 : Blo 702318 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B5348915 : Blo 702318 5348915 := bstep (se 1 (by rfl) ⟨4011686, by rfl⟩ : syracuseStep 5348915 = 8023373) B8023373
theorem B1056377 : Blo 702318 1056377 := bstep (se 2 (by rfl) ⟨396141, by rfl⟩ : syracuseStep 1056377 = 792283) B792283
theorem B1580831 : Blo 702318 1580831 := bstep (se 1 (by rfl) ⟨1185623, by rfl⟩ : syracuseStep 1580831 = 2371247) B2371247
theorem B1187615 : Blo 702318 1187615 := bstep (se 1 (by rfl) ⟨890711, by rfl⟩ : syracuseStep 1187615 = 1781423) B1781423
theorem B1056623 : Blo 702318 1056623 := bstep (se 1 (by rfl) ⟨792467, by rfl⟩ : syracuseStep 1056623 = 1584935) B1584935
theorem B794479 : Blo 702318 794479 := bstep (se 1 (by rfl) ⟨595859, by rfl⟩ : syracuseStep 794479 = 1191719) B1191719
theorem B1187831 : Blo 702318 1187831 := bstep (se 1 (by rfl) ⟨890873, by rfl⟩ : syracuseStep 1187831 = 1781747) B1781747
theorem B1581047 : Blo 702318 1581047 := bstep (se 1 (by rfl) ⟨1185785, by rfl⟩ : syracuseStep 1581047 = 2371571) B2371571
theorem B1581263 : Blo 702318 1581263 := bstep (se 1 (by rfl) ⟨1185947, by rfl⟩ : syracuseStep 1581263 = 2371895) B2371895
theorem B1188047 : Blo 702318 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B6004955 : Blo 702318 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B4825433 : Blo 702318 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B1581407 : Blo 702318 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B1057307 : Blo 702318 1057307 := bstep (se 1 (by rfl) ⟨792980, by rfl⟩ : syracuseStep 1057307 = 1585961) B1585961
theorem B3809875 : Blo 702318 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B1057487 : Blo 702318 1057487 := bstep (se 1 (by rfl) ⟨793115, by rfl⟩ : syracuseStep 1057487 = 1586231) B1586231
theorem B1778395 : Blo 702318 1778395 := bstep (se 1 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 1778395 = 2667593) B2667593
theorem B1057499 : Blo 702318 1057499 := bstep (se 1 (by rfl) ⟨793124, by rfl⟩ : syracuseStep 1057499 = 1586249) B1586249
theorem B4399919 : Blo 702318 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B12067865 : Blo 702318 12067865 := bstep (se 2 (by rfl) ⟨4525449, by rfl⟩ : syracuseStep 12067865 = 9050899) B9050899
theorem B1582127 : Blo 702318 1582127 := bstep (se 1 (by rfl) ⟨1186595, by rfl⟩ : syracuseStep 1582127 = 2373191) B2373191
theorem B1188911 : Blo 702318 1188911 := bstep (se 1 (by rfl) ⟨891683, by rfl⟩ : syracuseStep 1188911 = 1783367) B1783367
theorem B2008111 : Blo 702318 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B1188985 : Blo 702318 1188985 := bstep (se 2 (by rfl) ⟨445869, by rfl⟩ : syracuseStep 1188985 = 891739) B891739
theorem B1057913 : Blo 702318 1057913 := bstep (se 2 (by rfl) ⟨396717, by rfl⟩ : syracuseStep 1057913 = 793435) B793435
theorem B5350859 : Blo 702318 5350859 := bstep (se 1 (by rfl) ⟨4013144, by rfl⟩ : syracuseStep 5350859 = 8026289) B8026289
theorem B1582775 : Blo 702318 1582775 := bstep (se 1 (by rfl) ⟨1187081, by rfl⟩ : syracuseStep 1582775 = 2374163) B2374163
theorem B4073257 : Blo 702318 4073257 := bstep (se 2 (by rfl) ⟨1527471, by rfl⟩ : syracuseStep 4073257 = 3054943) B3054943
theorem B7415639 : Blo 702318 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B1058783 : Blo 702318 1058783 := bstep (se 1 (by rfl) ⟨794087, by rfl⟩ : syracuseStep 1058783 = 1588175) B1588175
theorem B1058795 : Blo 702318 1058795 := bstep (se 1 (by rfl) ⟨794096, by rfl⟩ : syracuseStep 1058795 = 1588193) B1588193
theorem B1058843 : Blo 702318 1058843 := bstep (se 1 (by rfl) ⟨794132, by rfl⟩ : syracuseStep 1058843 = 1588265) B1588265
theorem B1779833 : Blo 702318 1779833 := bstep (se 2 (by rfl) ⟨667437, by rfl⟩ : syracuseStep 1779833 = 1334875) B1334875
theorem B1583225 : Blo 702318 1583225 := bstep (se 2 (by rfl) ⟨593709, by rfl⟩ : syracuseStep 1583225 = 1187419) B1187419
theorem B1190281 : Blo 702318 1190281 := bstep (se 2 (by rfl) ⟨446355, by rfl⟩ : syracuseStep 1190281 = 892711) B892711
theorem B1059209 : Blo 702318 1059209 := bstep (se 2 (by rfl) ⟨397203, by rfl⟩ : syracuseStep 1059209 = 794407) B794407
theorem B6007931 : Blo 702318 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B1584539 : Blo 702318 1584539 := bstep (se 1 (by rfl) ⟨1188404, by rfl⟩ : syracuseStep 1584539 = 2376809) B2376809
theorem B13512379 : Blo 702318 13512379 := bstep (se 1 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 13512379 = 20268569) B20268569
theorem B5353289 : Blo 702318 5353289 := bstep (se 2 (by rfl) ⟨2007483, by rfl⟩ : syracuseStep 5353289 = 4014967) B4014967
theorem B1585115 : Blo 702318 1585115 := bstep (se 1 (by rfl) ⟨1188836, by rfl⟩ : syracuseStep 1585115 = 2377673) B2377673
theorem B1585295 : Blo 702318 1585295 := bstep (se 1 (by rfl) ⟨1188971, by rfl⟩ : syracuseStep 1585295 = 2377943) B2377943
theorem B1585385 : Blo 702318 1585385 := bstep (se 2 (by rfl) ⟨594519, by rfl⟩ : syracuseStep 1585385 = 1189039) B1189039
theorem B1585511 : Blo 702318 1585511 := bstep (se 1 (by rfl) ⟨1189133, by rfl⟩ : syracuseStep 1585511 = 2378267) B2378267
theorem B12989089 : Blo 702318 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B2667289 : Blo 702318 2667289 := bstep (se 2 (by rfl) ⟨1000233, by rfl⟩ : syracuseStep 2667289 = 2000467) B2000467
theorem B2372489 : Blo 702318 2372489 := bstep (se 2 (by rfl) ⟨889683, by rfl⟩ : syracuseStep 2372489 = 1779367) B1779367
theorem B1586087 : Blo 702318 1586087 := bstep (se 1 (by rfl) ⟨1189565, by rfl⟩ : syracuseStep 1586087 = 2379131) B2379131
theorem B2373353 : Blo 702318 2373353 := bstep (se 2 (by rfl) ⟨890007, by rfl⟩ : syracuseStep 2373353 = 1780015) B1780015
theorem B1783529 : Blo 702318 1783529 := bstep (se 2 (by rfl) ⟨668823, by rfl⟩ : syracuseStep 1783529 = 1337647) B1337647
theorem B1587023 : Blo 702318 1587023 := bstep (se 1 (by rfl) ⟨1190267, by rfl⟩ : syracuseStep 1587023 = 2380535) B2380535
theorem B702367 : Blo 702318 702367 := bstep (se 1 (by rfl) ⟨526775, by rfl⟩ : syracuseStep 702367 = 1053551) B1053551
theorem B702535 : Blo 702318 702535 := bstep (se 1 (by rfl) ⟨526901, by rfl⟩ : syracuseStep 702535 = 1053803) B1053803
theorem B1587383 : Blo 702318 1587383 := bstep (se 1 (by rfl) ⟨1190537, by rfl⟩ : syracuseStep 1587383 = 2381075) B2381075
theorem B5355719 : Blo 702318 5355719 := bstep (se 1 (by rfl) ⟨4016789, by rfl⟩ : syracuseStep 5355719 = 8033579) B8033579
theorem B702695 : Blo 702318 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B702879 : Blo 702318 702879 := bstep (se 1 (by rfl) ⟨527159, by rfl⟩ : syracuseStep 702879 = 1054319) B1054319
theorem B6109607 : Blo 702318 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B702927 : Blo 702318 702927 := bstep (se 1 (by rfl) ⟨527195, by rfl⟩ : syracuseStep 702927 = 1054391) B1054391
theorem B702951 : Blo 702318 702951 := bstep (se 1 (by rfl) ⟨527213, by rfl⟩ : syracuseStep 702951 = 1054427) B1054427
theorem B1587743 : Blo 702318 1587743 := bstep (se 1 (by rfl) ⟨1190807, by rfl⟩ : syracuseStep 1587743 = 2381615) B2381615
theorem B9615935 : Blo 702318 9615935 := bstep (se 1 (by rfl) ⟨7211951, by rfl⟩ : syracuseStep 9615935 = 14423903) B14423903
theorem B703067 : Blo 702318 703067 := bstep (se 1 (by rfl) ⟨527300, by rfl⟩ : syracuseStep 703067 = 1054601) B1054601
theorem B703135 : Blo 702318 703135 := bstep (se 1 (by rfl) ⟨527351, by rfl⟩ : syracuseStep 703135 = 1054703) B1054703
theorem B1587977 : Blo 702318 1587977 := bstep (se 2 (by rfl) ⟨595491, by rfl⟩ : syracuseStep 1587977 = 1190983) B1190983
theorem B703303 : Blo 702318 703303 := bstep (se 1 (by rfl) ⟨527477, by rfl⟩ : syracuseStep 703303 = 1054955) B1054955
theorem B703343 : Blo 702318 703343 := bstep (se 1 (by rfl) ⟨527507, by rfl⟩ : syracuseStep 703343 = 1055015) B1055015
theorem B703399 : Blo 702318 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B2669537 : Blo 702318 2669537 := bstep (se 2 (by rfl) ⟨1001076, by rfl⟩ : syracuseStep 2669537 = 2002153) B2002153
theorem B703579 : Blo 702318 703579 := bstep (se 1 (by rfl) ⟨527684, by rfl⟩ : syracuseStep 703579 = 1055369) B1055369
theorem B703695 : Blo 702318 703695 := bstep (se 1 (by rfl) ⟨527771, by rfl⟩ : syracuseStep 703695 = 1055543) B1055543
theorem B1424609 : Blo 702318 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B2604257 : Blo 702318 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B703719 : Blo 702318 703719 := bstep (se 1 (by rfl) ⟨527789, by rfl⟩ : syracuseStep 703719 = 1055579) B1055579
theorem B703815 : Blo 702318 703815 := bstep (se 1 (by rfl) ⟨527861, by rfl⟩ : syracuseStep 703815 = 1055723) B1055723
theorem B1588553 : Blo 702318 1588553 := bstep (se 2 (by rfl) ⟨595707, by rfl⟩ : syracuseStep 1588553 = 1191415) B1191415
theorem B2669993 : Blo 702318 2669993 := bstep (se 2 (by rfl) ⟨1001247, by rfl⟩ : syracuseStep 2669993 = 2002495) B2002495
theorem B2375081 : Blo 702318 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B703951 : Blo 702318 703951 := bstep (se 1 (by rfl) ⟨527963, by rfl⟩ : syracuseStep 703951 = 1055927) B1055927
theorem B704111 : Blo 702318 704111 := bstep (se 1 (by rfl) ⟨528083, by rfl⟩ : syracuseStep 704111 = 1056167) B1056167
theorem B704167 : Blo 702318 704167 := bstep (se 1 (by rfl) ⟨528125, by rfl⟩ : syracuseStep 704167 = 1056251) B1056251
theorem B2703071 : Blo 702318 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B704231 : Blo 702318 704231 := bstep (se 1 (by rfl) ⟨528173, by rfl⟩ : syracuseStep 704231 = 1056347) B1056347
theorem B1588967 : Blo 702318 1588967 := bstep (se 1 (by rfl) ⟨1191725, by rfl⟩ : syracuseStep 1588967 = 2383451) B2383451
theorem B1130249 : Blo 702318 1130249 := bstep (se 2 (by rfl) ⟨423843, by rfl⟩ : syracuseStep 1130249 = 847687) B847687
theorem B704287 : Blo 702318 704287 := bstep (se 1 (by rfl) ⟨528215, by rfl⟩ : syracuseStep 704287 = 1056431) B1056431
theorem B704367 : Blo 702318 704367 := bstep (se 1 (by rfl) ⟨528275, by rfl⟩ : syracuseStep 704367 = 1056551) B1056551
theorem B704423 : Blo 702318 704423 := bstep (se 1 (by rfl) ⟨528317, by rfl⟩ : syracuseStep 704423 = 1056635) B1056635
theorem B8011709 : Blo 702318 8011709 := bstep (se 3 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 8011709 = 3004391) B3004391
theorem B4014035 : Blo 702318 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B6012953 : Blo 702318 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B5423129 : Blo 702318 5423129 := bstep (se 2 (by rfl) ⟨2033673, by rfl⟩ : syracuseStep 5423129 = 4067347) B4067347
theorem B704703 : Blo 702318 704703 := bstep (se 1 (by rfl) ⟨528527, by rfl⟩ : syracuseStep 704703 = 1057055) B1057055
theorem B704719 : Blo 702318 704719 := bstep (se 1 (by rfl) ⟨528539, by rfl⟩ : syracuseStep 704719 = 1057079) B1057079
theorem B704767 : Blo 702318 704767 := bstep (se 1 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 704767 = 1057151) B1057151
theorem B1786151 : Blo 702318 1786151 := bstep (se 1 (by rfl) ⟨1339613, by rfl⟩ : syracuseStep 1786151 = 2679227) B2679227
theorem B704815 : Blo 702318 704815 := bstep (se 1 (by rfl) ⟨528611, by rfl⟩ : syracuseStep 704815 = 1057223) B1057223
theorem B12829063 : Blo 702318 12829063 := bstep (se 1 (by rfl) ⟨9621797, by rfl⟩ : syracuseStep 12829063 = 19243595) B19243595
theorem B705051 : Blo 702318 705051 := bstep (se 1 (by rfl) ⟨528788, by rfl⟩ : syracuseStep 705051 = 1057577) B1057577
theorem B705055 : Blo 702318 705055 := bstep (se 1 (by rfl) ⟨528791, by rfl⟩ : syracuseStep 705055 = 1057583) B1057583
theorem B705135 : Blo 702318 705135 := bstep (se 1 (by rfl) ⟨528851, by rfl⟩ : syracuseStep 705135 = 1057703) B1057703
theorem B705191 : Blo 702318 705191 := bstep (se 1 (by rfl) ⟨528893, by rfl⟩ : syracuseStep 705191 = 1057787) B1057787
theorem B705231 : Blo 702318 705231 := bstep (se 1 (by rfl) ⟨528923, by rfl⟩ : syracuseStep 705231 = 1057847) B1057847
theorem B705311 : Blo 702318 705311 := bstep (se 1 (by rfl) ⟨528983, by rfl⟩ : syracuseStep 705311 = 1057967) B1057967
theorem B2671649 : Blo 702318 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B705583 : Blo 702318 705583 := bstep (se 1 (by rfl) ⟨529187, by rfl⟩ : syracuseStep 705583 = 1058375) B1058375
theorem B1688683 : Blo 702318 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B705647 : Blo 702318 705647 := bstep (se 1 (by rfl) ⟨529235, by rfl⟩ : syracuseStep 705647 = 1058471) B1058471
theorem B705703 : Blo 702318 705703 := bstep (se 1 (by rfl) ⟨529277, by rfl⟩ : syracuseStep 705703 = 1058555) B1058555
theorem B705727 : Blo 702318 705727 := bstep (se 1 (by rfl) ⟨529295, by rfl⟩ : syracuseStep 705727 = 1058591) B1058591
theorem B705759 : Blo 702318 705759 := bstep (se 1 (by rfl) ⟨529319, by rfl⟩ : syracuseStep 705759 = 1058639) B1058639
theorem B54740245 : Blo 702318 54740245 := bstep (se 6 (by rfl) ⟨1282974, by rfl⟩ : syracuseStep 54740245 = 2565949) B2565949
theorem B705839 : Blo 702318 705839 := bstep (se 1 (by rfl) ⟨529379, by rfl⟩ : syracuseStep 705839 = 1058759) B1058759
theorem B1787305 : Blo 702318 1787305 := bstep (se 2 (by rfl) ⟨670239, by rfl⟩ : syracuseStep 1787305 = 1340479) B1340479
theorem B2704823 : Blo 702318 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B706075 : Blo 702318 706075 := bstep (se 1 (by rfl) ⟨529556, by rfl⟩ : syracuseStep 706075 = 1059113) B1059113
theorem B706079 : Blo 702318 706079 := bstep (se 1 (by rfl) ⟨529559, by rfl⟩ : syracuseStep 706079 = 1059119) B1059119
theorem B706239 : Blo 702318 706239 := bstep (se 1 (by rfl) ⟨529679, by rfl⟩ : syracuseStep 706239 = 1059359) B1059359
theorem B1002079 : Blo 702318 1002079 := bstep (se 1 (by rfl) ⟨751559, by rfl⟩ : syracuseStep 1002079 = 1503119) B1503119
theorem B2378537 : Blo 702318 2378537 := bstep (se 2 (by rfl) ⟨891951, by rfl⟩ : syracuseStep 2378537 = 1783903) B1783903
theorem B4016951 : Blo 702318 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B2378807 : Blo 702318 2378807 := bstep (se 1 (by rfl) ⟨1784105, by rfl⟩ : syracuseStep 2378807 = 3568211) B3568211
theorem B12045995 : Blo 702318 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B207867653 : Blo 702318 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B6508307 : Blo 702318 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B2412359 : Blo 702318 2412359 := bstep (se 1 (by rfl) ⟨1809269, by rfl⟩ : syracuseStep 2412359 = 3618539) B3618539
theorem B5361551 : Blo 702318 5361551 := bstep (se 1 (by rfl) ⟨4021163, by rfl⟩ : syracuseStep 5361551 = 8042327) B8042327
theorem B69390229 : Blo 702318 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B8016083 : Blo 702318 8016083 := bstep (se 1 (by rfl) ⟨6012062, by rfl⟩ : syracuseStep 8016083 = 12024125) B12024125
theorem B1626331 : Blo 702318 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B2379995 : Blo 702318 2379995 := bstep (se 1 (by rfl) ⟨1784996, by rfl⟩ : syracuseStep 2379995 = 3569993) B3569993
theorem B3002615 : Blo 702318 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B2380265 : Blo 702318 2380265 := bstep (se 2 (by rfl) ⟨892599, by rfl⟩ : syracuseStep 2380265 = 1785199) B1785199
theorem B5362523 : Blo 702318 5362523 := bstep (se 1 (by rfl) ⟨4021892, by rfl⟩ : syracuseStep 5362523 = 8043785) B8043785
theorem B4019159 : Blo 702318 4019159 := bstep (se 1 (by rfl) ⟨3014369, by rfl⟩ : syracuseStep 4019159 = 6028739) B6028739
theorem B3560435 : Blo 702318 3560435 := bstep (se 1 (by rfl) ⟨2670326, by rfl⟩ : syracuseStep 3560435 = 5340653) B5340653
theorem B6018077 : Blo 702318 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B38589857 : Blo 702318 38589857 := bstep (se 2 (by rfl) ⟨14471196, by rfl⟩ : syracuseStep 38589857 = 28942393) B28942393
theorem B6772571 : Blo 702318 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B4511713 : Blo 702318 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B3561731 : Blo 702318 3561731 := bstep (se 1 (by rfl) ⟨2671298, by rfl⟩ : syracuseStep 3561731 = 5342597) B5342597
theorem B2251091 : Blo 702318 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B3562055 : Blo 702318 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B1268603 : Blo 702318 1268603 := bstep (se 1 (by rfl) ⟨951452, by rfl⟩ : syracuseStep 1268603 = 1902905) B1902905
theorem B1334951 : Blo 702318 1334951 := bstep (se 1 (by rfl) ⟨1001213, by rfl⟩ : syracuseStep 1334951 = 2002427) B2002427
theorem B3563351 : Blo 702318 3563351 := bstep (se 1 (by rfl) ⟨2672513, by rfl⟩ : syracuseStep 3563351 = 5345027) B5345027
theorem B2678771 : Blo 702318 2678771 := bstep (se 1 (by rfl) ⟨2009078, by rfl⟩ : syracuseStep 2678771 = 4018157) B4018157
theorem B843967 : Blo 702318 843967 := bstep (se 1 (by rfl) ⟨632975, by rfl⟩ : syracuseStep 843967 = 1265951) B1265951
theorem B21684509 : Blo 702318 21684509 := bstep (se 3 (by rfl) ⟨4065845, by rfl⟩ : syracuseStep 21684509 = 8131691) B8131691
theorem B3301843 : Blo 702318 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B3564161 : Blo 702318 3564161 := bstep (se 2 (by rfl) ⟨1336560, by rfl⟩ : syracuseStep 3564161 = 2673121) B2673121
theorem B2679425 : Blo 702318 2679425 := bstep (se 2 (by rfl) ⟨1004784, by rfl⟩ : syracuseStep 2679425 = 2009569) B2009569
theorem B12837599 : Blo 702318 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B5071987 : Blo 702318 5071987 := bstep (se 1 (by rfl) ⟨3803990, by rfl⟩ : syracuseStep 5071987 = 7607981) B7607981
theorem B3564971 : Blo 702318 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B52159949 : Blo 702318 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B2680715 : Blo 702318 2680715 := bstep (se 1 (by rfl) ⟨2010536, by rfl⟩ : syracuseStep 2680715 = 4021073) B4021073
theorem B7628701 : Blo 702318 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B1501163 : Blo 702318 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B1271855 : Blo 702318 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B1337465 : Blo 702318 1337465 := bstep (se 2 (by rfl) ⟨501549, by rfl⟩ : syracuseStep 1337465 = 1003099) B1003099
theorem B69298361 : Blo 702318 69298361 := bstep (se 2 (by rfl) ⟨25986885, by rfl⟩ : syracuseStep 69298361 = 51973771) B51973771
theorem B2681687 : Blo 702318 2681687 := bstep (se 1 (by rfl) ⟨2011265, by rfl⟩ : syracuseStep 2681687 = 4022531) B4022531
theorem B6777719 : Blo 702318 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B11431313 : Blo 702318 11431313 := bstep (se 2 (by rfl) ⟨4286742, by rfl⟩ : syracuseStep 11431313 = 8573485) B8573485
theorem B1339105 : Blo 702318 1339105 := bstep (se 2 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 1339105 = 1004329) B1004329
theorem B3010391 : Blo 702318 3010391 := bstep (se 1 (by rfl) ⟨2257793, by rfl⟩ : syracuseStep 3010391 = 4515587) B4515587
theorem B17624965 : Blo 702318 17624965 := bstep (se 4 (by rfl) ⟨1652340, by rfl⟩ : syracuseStep 17624965 = 3304681) B3304681
theorem B22835357 : Blo 702318 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B1340297 : Blo 702318 1340297 := bstep (se 2 (by rfl) ⟨502611, by rfl⟩ : syracuseStep 1340297 = 1005223) B1005223
theorem B1340327 : Blo 702318 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B6780179 : Blo 702318 6780179 := bstep (se 1 (by rfl) ⟨5085134, by rfl⟩ : syracuseStep 6780179 = 10170269) B10170269
theorem B13530833 : Blo 702318 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B20117393 : Blo 702318 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B5339195 : Blo 702318 5339195 := bstep (se 1 (by rfl) ⟨4004396, by rfl⟩ : syracuseStep 5339195 = 8008793) B8008793
theorem B2849231 : Blo 702318 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B2292353 : Blo 702318 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B752495 : Blo 702318 752495 := bstep (se 1 (by rfl) ⟨564371, by rfl⟩ : syracuseStep 752495 = 1128743) B1128743
theorem B1604519 : Blo 702318 1604519 := bstep (se 1 (by rfl) ⟨1203389, by rfl⟩ : syracuseStep 1604519 = 2406779) B2406779
theorem B19758275 : Blo 702318 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B32603795 : Blo 702318 32603795 := bstep (se 1 (by rfl) ⟨24452846, by rfl⟩ : syracuseStep 32603795 = 48905693) B48905693
theorem B753319 : Blo 702318 753319 := bstep (se 1 (by rfl) ⟨564989, by rfl⟩ : syracuseStep 753319 = 1129979) B1129979
theorem B2981713 : Blo 702318 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3604895 : Blo 702318 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B6029801 : Blo 702318 6029801 := bstep (se 2 (by rfl) ⟨2261175, by rfl⟩ : syracuseStep 6029801 = 4522351) B4522351
theorem B12059117 : Blo 702318 12059117 := bstep (se 3 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 12059117 = 4522169) B4522169
theorem B17105417 : Blo 702318 17105417 := bstep (se 2 (by rfl) ⟨6414531, by rfl⟩ : syracuseStep 17105417 = 12829063) B12829063
theorem B5079833 : Blo 702318 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B1508159 : Blo 702318 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B1803215 : Blo 702318 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B3574205 : Blo 702318 3574205 := bstep (se 3 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 3574205 = 1340327) B1340327
theorem B8030663 : Blo 702318 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B138578435 : Blo 702318 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B1608239 : Blo 702318 1608239 := bstep (se 1 (by rfl) ⟨1206179, by rfl⟩ : syracuseStep 1608239 = 2412359) B2412359
theorem B3574367 : Blo 702318 3574367 := bstep (se 1 (by rfl) ⟨2680775, by rfl⟩ : syracuseStep 3574367 = 5361551) B5361551
theorem B5344055 : Blo 702318 5344055 := bstep (se 1 (by rfl) ⟨4008041, by rfl⟩ : syracuseStep 5344055 = 8016083) B8016083
theorem B2001743 : Blo 702318 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B3575015 : Blo 702318 3575015 := bstep (se 1 (by rfl) ⟨2681261, by rfl⟩ : syracuseStep 3575015 = 5362523) B5362523
theorem B25726571 : Blo 702318 25726571 := bstep (se 1 (by rfl) ⟨19294928, by rfl⟩ : syracuseStep 25726571 = 38589857) B38589857
theorem B3805375 : Blo 702318 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B5706247 : Blo 702318 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B1053689 : Blo 702318 1053689 := bstep (se 2 (by rfl) ⟨395133, by rfl⟩ : syracuseStep 1053689 = 790267) B790267
theorem B889967 : Blo 702318 889967 := bstep (se 1 (by rfl) ⟨667475, by rfl⟩ : syracuseStep 889967 = 1334951) B1334951
theorem B23499953 : Blo 702318 23499953 := bstep (se 2 (by rfl) ⟨8812482, by rfl⟩ : syracuseStep 23499953 = 17624965) B17624965
theorem B1053887 : Blo 702318 1053887 := bstep (se 1 (by rfl) ⟨790415, by rfl⟩ : syracuseStep 1053887 = 1580831) B1580831
theorem B791743 : Blo 702318 791743 := bstep (se 1 (by rfl) ⟨593807, by rfl⟩ : syracuseStep 791743 = 1187615) B1187615
theorem B1054031 : Blo 702318 1054031 := bstep (se 1 (by rfl) ⟨790523, by rfl⟩ : syracuseStep 1054031 = 1581047) B1581047
theorem B791887 : Blo 702318 791887 := bstep (se 1 (by rfl) ⟨593915, by rfl⟩ : syracuseStep 791887 = 1187831) B1187831
theorem B1054121 : Blo 702318 1054121 := bstep (se 2 (by rfl) ⟨395295, by rfl⟩ : syracuseStep 1054121 = 790591) B790591
theorem B1054175 : Blo 702318 1054175 := bstep (se 1 (by rfl) ⟨790631, by rfl⟩ : syracuseStep 1054175 = 1581263) B1581263
theorem B792031 : Blo 702318 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B4003303 : Blo 702318 4003303 := bstep (se 1 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 4003303 = 6004955) B6004955
theorem B14456339 : Blo 702318 14456339 := bstep (se 1 (by rfl) ⟨10842254, by rfl⟩ : syracuseStep 14456339 = 21684509) B21684509
theorem B3216955 : Blo 702318 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B1054271 : Blo 702318 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B2168441 : Blo 702318 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B8558399 : Blo 702318 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B1054751 : Blo 702318 1054751 := bstep (se 1 (by rfl) ⟨791063, by rfl⟩ : syracuseStep 1054751 = 1582127) B1582127
theorem B792607 : Blo 702318 792607 := bstep (se 1 (by rfl) ⟨594455, by rfl⟩ : syracuseStep 792607 = 1188911) B1188911
theorem B34773299 : Blo 702318 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B16292285 : Blo 702318 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B1055183 : Blo 702318 1055183 := bstep (se 1 (by rfl) ⟨791387, by rfl⟩ : syracuseStep 1055183 = 1582775) B1582775
theorem B1055273 : Blo 702318 1055273 := bstep (se 2 (by rfl) ⟨395727, by rfl⟩ : syracuseStep 1055273 = 791455) B791455
theorem B1186555 : Blo 702318 1186555 := bstep (se 1 (by rfl) ⟨889916, by rfl⟩ : syracuseStep 1186555 = 1779833) B1779833
theorem B1055483 : Blo 702318 1055483 := bstep (se 1 (by rfl) ⟨791612, by rfl⟩ : syracuseStep 1055483 = 1583225) B1583225
theorem B891643 : Blo 702318 891643 := bstep (se 1 (by rfl) ⟨668732, by rfl⟩ : syracuseStep 891643 = 1337465) B1337465
theorem B1055609 : Blo 702318 1055609 := bstep (se 2 (by rfl) ⟨395853, by rfl⟩ : syracuseStep 1055609 = 791707) B791707
theorem B4005287 : Blo 702318 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B1056359 : Blo 702318 1056359 := bstep (se 1 (by rfl) ⟨792269, by rfl⟩ : syracuseStep 1056359 = 1584539) B1584539
theorem B2006653 : Blo 702318 2006653 := bstep (se 3 (by rfl) ⟨376247, by rfl⟩ : syracuseStep 2006653 = 752495) B752495
theorem B1056521 : Blo 702318 1056521 := bstep (se 2 (by rfl) ⟨396195, by rfl⟩ : syracuseStep 1056521 = 792391) B792391
theorem B2006927 : Blo 702318 2006927 := bstep (se 1 (by rfl) ⟨1505195, by rfl⟩ : syracuseStep 2006927 = 3010391) B3010391
theorem B1056743 : Blo 702318 1056743 := bstep (se 1 (by rfl) ⟨792557, by rfl⟩ : syracuseStep 1056743 = 1585115) B1585115
theorem B1056863 : Blo 702318 1056863 := bstep (se 1 (by rfl) ⟨792647, by rfl⟩ : syracuseStep 1056863 = 1585295) B1585295
theorem B1056923 : Blo 702318 1056923 := bstep (se 1 (by rfl) ⟨792692, by rfl⟩ : syracuseStep 1056923 = 1585385) B1585385
theorem B1057007 : Blo 702318 1057007 := bstep (se 1 (by rfl) ⟨792755, by rfl⟩ : syracuseStep 1057007 = 1585511) B1585511
theorem B1581659 : Blo 702318 1581659 := bstep (se 1 (by rfl) ⟨1186244, by rfl⟩ : syracuseStep 1581659 = 2372489) B2372489
theorem B893531 : Blo 702318 893531 := bstep (se 1 (by rfl) ⟨670148, by rfl⟩ : syracuseStep 893531 = 1340297) B1340297
theorem B1057385 : Blo 702318 1057385 := bstep (se 2 (by rfl) ⟨396519, by rfl⟩ : syracuseStep 1057385 = 793039) B793039
theorem B1057391 : Blo 702318 1057391 := bstep (se 1 (by rfl) ⟨793043, by rfl⟩ : syracuseStep 1057391 = 1586087) B1586087
theorem B9020555 : Blo 702318 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B1582235 : Blo 702318 1582235 := bstep (se 1 (by rfl) ⟨1186676, by rfl⟩ : syracuseStep 1582235 = 2373353) B2373353
theorem B1189019 : Blo 702318 1189019 := bstep (se 1 (by rfl) ⟨891764, by rfl⟩ : syracuseStep 1189019 = 1783529) B1783529
theorem B1058015 : Blo 702318 1058015 := bstep (se 1 (by rfl) ⟨793511, by rfl⟩ : syracuseStep 1058015 = 1587023) B1587023
theorem B13411595 : Blo 702318 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B1058255 : Blo 702318 1058255 := bstep (se 1 (by rfl) ⟨793691, by rfl⟩ : syracuseStep 1058255 = 1587383) B1587383
theorem B1058441 : Blo 702318 1058441 := bstep (se 2 (by rfl) ⟨396915, by rfl⟩ : syracuseStep 1058441 = 793831) B793831
theorem B1058495 : Blo 702318 1058495 := bstep (se 1 (by rfl) ⟨793871, by rfl⟩ : syracuseStep 1058495 = 1587743) B1587743
theorem B1058651 : Blo 702318 1058651 := bstep (se 1 (by rfl) ⟨793988, by rfl⟩ : syracuseStep 1058651 = 1587977) B1587977
theorem B1779691 : Blo 702318 1779691 := bstep (se 1 (by rfl) ⟨1334768, by rfl⟩ : syracuseStep 1779691 = 2669537) B2669537
theorem B1059035 : Blo 702318 1059035 := bstep (se 1 (by rfl) ⟨794276, by rfl⟩ : syracuseStep 1059035 = 1588553) B1588553
theorem B1779995 : Blo 702318 1779995 := bstep (se 1 (by rfl) ⟨1334996, by rfl⟩ : syracuseStep 1779995 = 2669993) B2669993
theorem B1583387 : Blo 702318 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B21735863 : Blo 702318 21735863 := bstep (se 1 (by rfl) ⟨16301897, by rfl⟩ : syracuseStep 21735863 = 32603795) B32603795
theorem B3975617 : Blo 702318 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B1059305 : Blo 702318 1059305 := bstep (se 2 (by rfl) ⟨397239, by rfl⟩ : syracuseStep 1059305 = 794479) B794479
theorem B1059311 : Blo 702318 1059311 := bstep (se 1 (by rfl) ⟨794483, by rfl⟩ : syracuseStep 1059311 = 1588967) B1588967
theorem B4008635 : Blo 702318 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B3615419 : Blo 702318 3615419 := bstep (se 1 (by rfl) ⟨2711564, by rfl⟩ : syracuseStep 3615419 = 5423129) B5423129
theorem B1190767 : Blo 702318 1190767 := bstep (se 1 (by rfl) ⟨893075, by rfl⟩ : syracuseStep 1190767 = 1786151) B1786151
theorem B1125289 : Blo 702318 1125289 := bstep (se 2 (by rfl) ⟨421983, by rfl⟩ : syracuseStep 1125289 = 843967) B843967
theorem B4402457 : Blo 702318 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B1781099 : Blo 702318 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B5090789 : Blo 702318 5090789 := bstep (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) B954523
theorem B2371193 : Blo 702318 2371193 := bstep (se 2 (by rfl) ⟨889197, by rfl⟩ : syracuseStep 2371193 = 1778395) B1778395
theorem B6008579 : Blo 702318 6008579 := bstep (se 1 (by rfl) ⟨4506434, by rfl⟩ : syracuseStep 6008579 = 9012869) B9012869
theorem B2011243 : Blo 702318 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B6762649 : Blo 702318 6762649 := bstep (se 2 (by rfl) ⟨2535993, by rfl⟩ : syracuseStep 6762649 = 5071987) B5071987
theorem B1585313 : Blo 702318 1585313 := bstep (se 2 (by rfl) ⟨594492, by rfl⟩ : syracuseStep 1585313 = 1188985) B1188985
theorem B2142521 : Blo 702318 2142521 := bstep (se 2 (by rfl) ⟨803445, by rfl⟩ : syracuseStep 2142521 = 1606891) B1606891
theorem B72986993 : Blo 702318 72986993 := bstep (se 2 (by rfl) ⟨27370122, by rfl⟩ : syracuseStep 72986993 = 54740245) B54740245
theorem B1585691 : Blo 702318 1585691 := bstep (se 1 (by rfl) ⟨1189268, by rfl⟩ : syracuseStep 1585691 = 2378537) B2378537
theorem B1585871 : Blo 702318 1585871 := bstep (se 1 (by rfl) ⟨1189403, by rfl⟩ : syracuseStep 1585871 = 2378807) B2378807
theorem B9024655 : Blo 702318 9024655 := bstep (se 1 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 9024655 = 13536983) B13536983
theorem B10171601 : Blo 702318 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B1586663 : Blo 702318 1586663 := bstep (se 1 (by rfl) ⟨1189997, by rfl⟩ : syracuseStep 1586663 = 2379995) B2379995
theorem B1586843 : Blo 702318 1586843 := bstep (se 1 (by rfl) ⟨1190132, by rfl⟩ : syracuseStep 1586843 = 2380265) B2380265
theorem B1587041 : Blo 702318 1587041 := bstep (se 2 (by rfl) ⟨595140, by rfl⟩ : syracuseStep 1587041 = 1190281) B1190281
theorem B702399 : Blo 702318 702399 := bstep (se 1 (by rfl) ⟨526799, by rfl⟩ : syracuseStep 702399 = 1053599) B1053599
theorem B2373623 : Blo 702318 2373623 := bstep (se 1 (by rfl) ⟨1780217, by rfl⟩ : syracuseStep 2373623 = 3560435) B3560435
theorem B4012051 : Blo 702318 4012051 := bstep (se 1 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 4012051 = 6018077) B6018077
theorem B702527 : Blo 702318 702527 := bstep (se 1 (by rfl) ⟨526895, by rfl⟩ : syracuseStep 702527 = 1053791) B1053791
theorem B702567 : Blo 702318 702567 := bstep (se 1 (by rfl) ⟨526925, by rfl⟩ : syracuseStep 702567 = 1053851) B1053851
theorem B9025991 : Blo 702318 9025991 := bstep (se 1 (by rfl) ⟨6769493, by rfl⟩ : syracuseStep 9025991 = 13538987) B13538987
theorem B703023 : Blo 702318 703023 := bstep (se 1 (by rfl) ⟨527267, by rfl⟩ : syracuseStep 703023 = 1054535) B1054535
theorem B2374487 : Blo 702318 2374487 := bstep (se 1 (by rfl) ⟨1780865, by rfl⟩ : syracuseStep 2374487 = 3561731) B3561731
theorem B703423 : Blo 702318 703423 := bstep (se 1 (by rfl) ⟨527567, by rfl⟩ : syracuseStep 703423 = 1055135) B1055135
theorem B2669507 : Blo 702318 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B703471 : Blo 702318 703471 := bstep (se 1 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 703471 = 1055207) B1055207
theorem B2374703 : Blo 702318 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B5356691 : Blo 702318 5356691 := bstep (se 1 (by rfl) ⟨4017518, by rfl⟩ : syracuseStep 5356691 = 8035037) B8035037
theorem B703967 : Blo 702318 703967 := bstep (se 1 (by rfl) ⟨527975, by rfl⟩ : syracuseStep 703967 = 1055951) B1055951
theorem B17350139 : Blo 702318 17350139 := bstep (se 1 (by rfl) ⟨13012604, by rfl⟩ : syracuseStep 17350139 = 26025209) B26025209
theorem B704047 : Blo 702318 704047 := bstep (se 1 (by rfl) ⟨528035, by rfl⟩ : syracuseStep 704047 = 1056071) B1056071
theorem B1785473 : Blo 702318 1785473 := bstep (se 2 (by rfl) ⟨669552, by rfl⟩ : syracuseStep 1785473 = 1339105) B1339105
theorem B1097371 : Blo 702318 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B704155 : Blo 702318 704155 := bstep (se 1 (by rfl) ⟨528116, by rfl⟩ : syracuseStep 704155 = 1056233) B1056233
theorem B704251 : Blo 702318 704251 := bstep (se 1 (by rfl) ⟨528188, by rfl⟩ : syracuseStep 704251 = 1056377) B1056377
theorem B92520305 : Blo 702318 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B2375567 : Blo 702318 2375567 := bstep (se 1 (by rfl) ⟨1781675, by rfl⟩ : syracuseStep 2375567 = 3563351) B3563351
theorem B704415 : Blo 702318 704415 := bstep (se 1 (by rfl) ⟨528311, by rfl⟩ : syracuseStep 704415 = 1056623) B1056623
theorem B1785847 : Blo 702318 1785847 := bstep (se 1 (by rfl) ⟨1339385, by rfl⟩ : syracuseStep 1785847 = 2678771) B2678771
theorem B15253505 : Blo 702318 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B704871 : Blo 702318 704871 := bstep (se 1 (by rfl) ⟨528653, by rfl⟩ : syracuseStep 704871 = 1057307) B1057307
theorem B2376107 : Blo 702318 2376107 := bstep (se 1 (by rfl) ⟨1782080, by rfl⟩ : syracuseStep 2376107 = 3564161) B3564161
theorem B1786283 : Blo 702318 1786283 := bstep (se 1 (by rfl) ⟨1339712, by rfl⟩ : syracuseStep 1786283 = 2679425) B2679425
theorem B704991 : Blo 702318 704991 := bstep (se 1 (by rfl) ⟨528743, by rfl⟩ : syracuseStep 704991 = 1057487) B1057487
theorem B704999 : Blo 702318 704999 := bstep (se 1 (by rfl) ⟨528749, by rfl⟩ : syracuseStep 704999 = 1057499) B1057499
theorem B2933279 : Blo 702318 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B8045243 : Blo 702318 8045243 := bstep (se 1 (by rfl) ⟨6033932, by rfl⟩ : syracuseStep 8045243 = 12067865) B12067865
theorem B705275 : Blo 702318 705275 := bstep (se 1 (by rfl) ⟨528956, by rfl⟩ : syracuseStep 705275 = 1057913) B1057913
theorem B17318785 : Blo 702318 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B2376647 : Blo 702318 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B3556385 : Blo 702318 3556385 := bstep (se 2 (by rfl) ⟨1333644, by rfl⟩ : syracuseStep 3556385 = 2667289) B2667289
theorem B1787143 : Blo 702318 1787143 := bstep (se 1 (by rfl) ⟨1340357, by rfl⟩ : syracuseStep 1787143 = 2680715) B2680715
theorem B705855 : Blo 702318 705855 := bstep (se 1 (by rfl) ⟨529391, by rfl⟩ : syracuseStep 705855 = 1058783) B1058783
theorem B1000775 : Blo 702318 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B705863 : Blo 702318 705863 := bstep (se 1 (by rfl) ⟨529397, by rfl⟩ : syracuseStep 705863 = 1058795) B1058795
theorem B705895 : Blo 702318 705895 := bstep (se 1 (by rfl) ⟨529421, by rfl⟩ : syracuseStep 705895 = 1058843) B1058843
theorem B25642493 : Blo 702318 25642493 := bstep (se 3 (by rfl) ⟨4807967, by rfl⟩ : syracuseStep 25642493 = 9615935) B9615935
theorem B706139 : Blo 702318 706139 := bstep (se 1 (by rfl) ⟨529604, by rfl⟩ : syracuseStep 706139 = 1059209) B1059209
theorem B1787791 : Blo 702318 1787791 := bstep (se 1 (by rfl) ⟨1340843, by rfl⟩ : syracuseStep 1787791 = 2681687) B2681687
theorem B7620875 : Blo 702318 7620875 := bstep (se 1 (by rfl) ⟨5715656, by rfl⟩ : syracuseStep 7620875 = 11431313) B11431313
theorem B6015617 : Blo 702318 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B15223571 : Blo 702318 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B4017701 : Blo 702318 4017701 := bstep (se 4 (by rfl) ⟨376659, by rfl⟩ : syracuseStep 4017701 = 753319) B753319
theorem B3559463 : Blo 702318 3559463 := bstep (se 1 (by rfl) ⟨2669597, by rfl⟩ : syracuseStep 3559463 = 5339195) B5339195
theorem B1528235 : Blo 702318 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B1069679 : Blo 702318 1069679 := bstep (se 1 (by rfl) ⟨802259, by rfl⟩ : syracuseStep 1069679 = 1604519) B1604519
theorem B17355485 : Blo 702318 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B2676023 : Blo 702318 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B1201855 : Blo 702318 1201855 := bstep (se 1 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 1201855 = 1802783) B1802783
theorem B2677481 : Blo 702318 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B2251577 : Blo 702318 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B2382695 : Blo 702318 2382695 := bstep (se 1 (by rfl) ⟨1787021, by rfl⟩ : syracuseStep 2382695 = 3574043) B3574043
theorem B2677967 : Blo 702318 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B2383073 : Blo 702318 2383073 := bstep (se 2 (by rfl) ⟨893652, by rfl⟩ : syracuseStep 2383073 = 1787305) B1787305
theorem B2679439 : Blo 702318 2679439 := bstep (se 1 (by rfl) ⟨2009579, by rfl⟩ : syracuseStep 2679439 = 4019159) B4019159
theorem B1336105 : Blo 702318 1336105 := bstep (se 2 (by rfl) ⟨501039, by rfl⟩ : syracuseStep 1336105 = 1002079) B1002079
theorem B3564647 : Blo 702318 3564647 := bstep (se 1 (by rfl) ⟨2673485, by rfl⟩ : syracuseStep 3564647 = 5346971) B5346971
theorem B4515047 : Blo 702318 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B1500727 : Blo 702318 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B1336895 : Blo 702318 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B845735 : Blo 702318 845735 := bstep (se 1 (by rfl) ⟨634301, by rfl⟩ : syracuseStep 845735 = 1268603) B1268603
theorem B5859287 : Blo 702318 5859287 := bstep (se 1 (by rfl) ⟨4394465, by rfl⟩ : syracuseStep 5859287 = 8788931) B8788931
theorem B3565619 : Blo 702318 3565619 := bstep (se 1 (by rfl) ⟨2674214, by rfl⟩ : syracuseStep 3565619 = 5348429) B5348429
theorem B18016505 : Blo 702318 18016505 := bstep (se 2 (by rfl) ⟨6756189, by rfl⟩ : syracuseStep 18016505 = 13512379) B13512379
theorem B3565943 : Blo 702318 3565943 := bstep (se 1 (by rfl) ⟨2674457, by rfl⟩ : syracuseStep 3565943 = 5348915) B5348915
theorem B3567239 : Blo 702318 3567239 := bstep (se 1 (by rfl) ⟨2675429, by rfl⟩ : syracuseStep 3567239 = 5350859) B5350859
theorem B4943759 : Blo 702318 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B847903 : Blo 702318 847903 := bstep (se 1 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 847903 = 1271855) B1271855
theorem B46198907 : Blo 702318 46198907 := bstep (se 1 (by rfl) ⟨34649180, by rfl⟩ : syracuseStep 46198907 = 69298361) B69298361
theorem B4518479 : Blo 702318 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B3568859 : Blo 702318 3568859 := bstep (se 1 (by rfl) ⟨2676644, by rfl⟩ : syracuseStep 3568859 = 5353289) B5353289
theorem B4520119 : Blo 702318 4520119 := bstep (se 1 (by rfl) ⟨3390089, by rfl⟩ : syracuseStep 4520119 = 6780179) B6780179
theorem B3570479 : Blo 702318 3570479 := bstep (se 1 (by rfl) ⟨2677859, by rfl⟩ : syracuseStep 3570479 = 5355719) B5355719
theorem B21724037 : Blo 702318 21724037 := bstep (se 4 (by rfl) ⟨2036628, by rfl⟩ : syracuseStep 21724037 = 4073257) B4073257
theorem B1899487 : Blo 702318 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B13172183 : Blo 702318 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B949739 : Blo 702318 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B1736171 : Blo 702318 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1802047 : Blo 702318 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B753499 : Blo 702318 753499 := bstep (se 1 (by rfl) ⟨565124, by rfl⟩ : syracuseStep 753499 = 1130249) B1130249
theorem B5341139 : Blo 702318 5341139 := bstep (se 1 (by rfl) ⟨4005854, by rfl⟩ : syracuseStep 5341139 = 8011709) B8011709
theorem B11403611 : Blo 702318 11403611 := bstep (se 1 (by rfl) ⟨8552708, by rfl⟩ : syracuseStep 11403611 = 17105417) B17105417
theorem B3572585 : Blo 702318 3572585 := bstep (se 2 (by rfl) ⟨1339719, by rfl⟩ : syracuseStep 3572585 = 2679439) B2679439
theorem B5080583 : Blo 702318 5080583 := bstep (se 1 (by rfl) ⟨3810437, by rfl⟩ : syracuseStep 5080583 = 7620875) B7620875
theorem B2000969 : Blo 702318 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B1018823 : Blo 702318 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B11570323 : Blo 702318 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B15666635 : Blo 702318 15666635 := bstep (se 1 (by rfl) ⟨11749976, by rfl⟩ : syracuseStep 15666635 = 23499953) B23499953
theorem B9637559 : Blo 702318 9637559 := bstep (se 1 (by rfl) ⟨7228169, by rfl⟩ : syracuseStep 9637559 = 14456339) B14456339
theorem B1445627 : Blo 702318 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B5705599 : Blo 702318 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B9016865 : Blo 702318 9016865 := bstep (se 2 (by rfl) ⟨3381324, by rfl⟩ : syracuseStep 9016865 = 6762649) B6762649
theorem B1054439 : Blo 702318 1054439 := bstep (se 1 (by rfl) ⟨790829, by rfl⟩ : syracuseStep 1054439 = 1581659) B1581659
theorem B7608329 : Blo 702318 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B1054823 : Blo 702318 1054823 := bstep (se 1 (by rfl) ⟨791117, by rfl⟩ : syracuseStep 1054823 = 1582235) B1582235
theorem B792679 : Blo 702318 792679 := bstep (se 1 (by rfl) ⟨594509, by rfl⟩ : syracuseStep 792679 = 1189019) B1189019
theorem B891263 : Blo 702318 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B3906191 : Blo 702318 3906191 := bstep (se 1 (by rfl) ⟨2929643, by rfl⟩ : syracuseStep 3906191 = 5859287) B5859287
theorem B1186663 : Blo 702318 1186663 := bstep (se 1 (by rfl) ⟨889997, by rfl⟩ : syracuseStep 1186663 = 1779995) B1779995
theorem B1055591 : Blo 702318 1055591 := bstep (se 1 (by rfl) ⟨791693, by rfl⟩ : syracuseStep 1055591 = 1583387) B1583387
theorem B12032873 : Blo 702318 12032873 := bstep (se 2 (by rfl) ⟨4512327, by rfl⟩ : syracuseStep 12032873 = 9024655) B9024655
theorem B1055657 : Blo 702318 1055657 := bstep (se 2 (by rfl) ⟨395871, by rfl⟩ : syracuseStep 1055657 = 791743) B791743
theorem B14490575 : Blo 702318 14490575 := bstep (se 1 (by rfl) ⟨10867931, by rfl⟩ : syracuseStep 14490575 = 21735863) B21735863
theorem B1055849 : Blo 702318 1055849 := bstep (se 2 (by rfl) ⟨395943, by rfl⟩ : syracuseStep 1055849 = 791887) B791887
theorem B1056041 : Blo 702318 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B6004205 : Blo 702318 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B1187399 : Blo 702318 1187399 := bstep (se 1 (by rfl) ⟨890549, by rfl⟩ : syracuseStep 1187399 = 1781099) B1781099
theorem B1580795 : Blo 702318 1580795 := bstep (se 1 (by rfl) ⟨1185596, by rfl⟩ : syracuseStep 1580795 = 2371193) B2371193
theorem B4005719 : Blo 702318 4005719 := bstep (se 1 (by rfl) ⟨3004289, by rfl⟩ : syracuseStep 4005719 = 6008579) B6008579
theorem B5349401 : Blo 702318 5349401 := bstep (se 2 (by rfl) ⟨2006025, by rfl⟩ : syracuseStep 5349401 = 4012051) B4012051
theorem B1056809 : Blo 702318 1056809 := bstep (se 2 (by rfl) ⟨396303, by rfl⟩ : syracuseStep 1056809 = 792607) B792607
theorem B1056875 : Blo 702318 1056875 := bstep (se 1 (by rfl) ⟨792656, by rfl⟩ : syracuseStep 1056875 = 1585313) B1585313
theorem B1057127 : Blo 702318 1057127 := bstep (se 1 (by rfl) ⟨792845, by rfl⟩ : syracuseStep 1057127 = 1585691) B1585691
theorem B1057247 : Blo 702318 1057247 := bstep (se 1 (by rfl) ⟨792935, by rfl⟩ : syracuseStep 1057247 = 1585871) B1585871
theorem B1057775 : Blo 702318 1057775 := bstep (se 1 (by rfl) ⟨793331, by rfl⟩ : syracuseStep 1057775 = 1586663) B1586663
theorem B1582073 : Blo 702318 1582073 := bstep (se 2 (by rfl) ⟨593277, by rfl⟩ : syracuseStep 1582073 = 1186555) B1186555
theorem B1188857 : Blo 702318 1188857 := bstep (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) B891643
theorem B1057895 : Blo 702318 1057895 := bstep (se 1 (by rfl) ⟨793421, by rfl⟩ : syracuseStep 1057895 = 1586843) B1586843
theorem B1058027 : Blo 702318 1058027 := bstep (se 1 (by rfl) ⟨793520, by rfl⟩ : syracuseStep 1058027 = 1587041) B1587041
theorem B2532637 : Blo 702318 2532637 := bstep (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) B949739
theorem B2532649 : Blo 702318 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1582415 : Blo 702318 1582415 := bstep (se 1 (by rfl) ⟨1186811, by rfl⟩ : syracuseStep 1582415 = 2373623) B2373623
theorem B1582991 : Blo 702318 1582991 := bstep (se 1 (by rfl) ⟨1187243, by rfl⟩ : syracuseStep 1582991 = 2374487) B2374487
theorem B1779671 : Blo 702318 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B1583135 : Blo 702318 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B1157447 : Blo 702318 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B13183357 : Blo 702318 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B2402729 : Blo 702318 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B1190315 : Blo 702318 1190315 := bstep (se 1 (by rfl) ⟨892736, by rfl⟩ : syracuseStep 1190315 = 1785473) B1785473
theorem B61680203 : Blo 702318 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B1583711 : Blo 702318 1583711 := bstep (se 1 (by rfl) ⟨1187783, by rfl⟩ : syracuseStep 1583711 = 2375567) B2375567
theorem B10169003 : Blo 702318 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B2403263 : Blo 702318 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B1584071 : Blo 702318 1584071 := bstep (se 1 (by rfl) ⟨1188053, by rfl⟩ : syracuseStep 1584071 = 2376107) B2376107
theorem B1190855 : Blo 702318 1190855 := bstep (se 1 (by rfl) ⟨893141, by rfl⟩ : syracuseStep 1190855 = 1786283) B1786283
theorem B8039411 : Blo 702318 8039411 := bstep (se 1 (by rfl) ⟨6029558, by rfl⟩ : syracuseStep 8039411 = 12059117) B12059117
theorem B3386555 : Blo 702318 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B1584431 : Blo 702318 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B2370923 : Blo 702318 2370923 := bstep (se 1 (by rfl) ⟨1778192, by rfl⟩ : syracuseStep 2370923 = 3556385) B3556385
theorem B1781473 : Blo 702318 1781473 := bstep (se 2 (by rfl) ⟨668052, by rfl⟩ : syracuseStep 1781473 = 1336105) B1336105
theorem B5353775 : Blo 702318 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B92385623 : Blo 702318 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B4010411 : Blo 702318 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B17151047 : Blo 702318 17151047 := bstep (se 1 (by rfl) ⟨12863285, by rfl⟩ : syracuseStep 17151047 = 25726571) B25726571
theorem B2372921 : Blo 702318 2372921 := bstep (se 2 (by rfl) ⟨889845, by rfl⟩ : syracuseStep 2372921 = 1779691) B1779691
theorem B2372975 : Blo 702318 2372975 := bstep (se 1 (by rfl) ⟨1779731, by rfl⟩ : syracuseStep 2372975 = 3559463) B3559463
theorem B2373245 : Blo 702318 2373245 := bstep (se 3 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 2373245 = 889967) B889967
theorem B702459 : Blo 702318 702459 := bstep (se 1 (by rfl) ⟨526844, by rfl⟩ : syracuseStep 702459 = 1053689) B1053689
theorem B35764253 : Blo 702318 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B702591 : Blo 702318 702591 := bstep (se 1 (by rfl) ⟨526943, by rfl⟩ : syracuseStep 702591 = 1053887) B1053887
theorem B2668733 : Blo 702318 2668733 := bstep (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) B1000775
theorem B1784015 : Blo 702318 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B702687 : Blo 702318 702687 := bstep (se 1 (by rfl) ⟨527015, by rfl⟩ : syracuseStep 702687 = 1054031) B1054031
theorem B702747 : Blo 702318 702747 := bstep (se 1 (by rfl) ⟨527060, by rfl⟩ : syracuseStep 702747 = 1054121) B1054121
theorem B702783 : Blo 702318 702783 := bstep (se 1 (by rfl) ⟨527087, by rfl⟩ : syracuseStep 702783 = 1054175) B1054175
theorem B702847 : Blo 702318 702847 := bstep (se 1 (by rfl) ⟨527135, by rfl⟩ : syracuseStep 702847 = 1054271) B1054271
theorem B1587689 : Blo 702318 1587689 := bstep (se 2 (by rfl) ⟨595383, by rfl⟩ : syracuseStep 1587689 = 1190767) B1190767
theorem B703167 : Blo 702318 703167 := bstep (se 1 (by rfl) ⟨527375, by rfl⟩ : syracuseStep 703167 = 1054751) B1054751
theorem B23182199 : Blo 702318 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B10861523 : Blo 702318 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B703455 : Blo 702318 703455 := bstep (se 1 (by rfl) ⟨527591, by rfl⟩ : syracuseStep 703455 = 1055183) B1055183
theorem B703515 : Blo 702318 703515 := bstep (se 1 (by rfl) ⟨527636, by rfl⟩ : syracuseStep 703515 = 1055273) B1055273
theorem B1784987 : Blo 702318 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B703655 : Blo 702318 703655 := bstep (se 1 (by rfl) ⟨527741, by rfl⟩ : syracuseStep 703655 = 1055483) B1055483
theorem B1588463 : Blo 702318 1588463 := bstep (se 1 (by rfl) ⟨1191347, by rfl⟩ : syracuseStep 1588463 = 2382695) B2382695
theorem B703739 : Blo 702318 703739 := bstep (se 1 (by rfl) ⟨527804, by rfl⟩ : syracuseStep 703739 = 1055609) B1055609
theorem B1785311 : Blo 702318 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B1588715 : Blo 702318 1588715 := bstep (se 1 (by rfl) ⟨1191536, by rfl⟩ : syracuseStep 1588715 = 2383073) B2383073
theorem B2670191 : Blo 702318 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B704239 : Blo 702318 704239 := bstep (se 1 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 704239 = 1056359) B1056359
theorem B704347 : Blo 702318 704347 := bstep (se 1 (by rfl) ⟨528260, by rfl⟩ : syracuseStep 704347 = 1056521) B1056521
theorem B704495 : Blo 702318 704495 := bstep (se 1 (by rfl) ⟨528371, by rfl⟩ : syracuseStep 704495 = 1056743) B1056743
theorem B1130537 : Blo 702318 1130537 := bstep (se 2 (by rfl) ⟨423951, by rfl⟩ : syracuseStep 1130537 = 847903) B847903
theorem B704575 : Blo 702318 704575 := bstep (se 1 (by rfl) ⟨528431, by rfl⟩ : syracuseStep 704575 = 1056863) B1056863
theorem B704615 : Blo 702318 704615 := bstep (se 1 (by rfl) ⟨528461, by rfl⟩ : syracuseStep 704615 = 1056923) B1056923
theorem B704671 : Blo 702318 704671 := bstep (se 1 (by rfl) ⟨528503, by rfl⟩ : syracuseStep 704671 = 1057007) B1057007
theorem B704923 : Blo 702318 704923 := bstep (se 1 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 704923 = 1057385) B1057385
theorem B704927 : Blo 702318 704927 := bstep (se 1 (by rfl) ⟨528695, by rfl⟩ : syracuseStep 704927 = 1057391) B1057391
theorem B2376431 : Blo 702318 2376431 := bstep (se 1 (by rfl) ⟨1782323, by rfl⟩ : syracuseStep 2376431 = 3564647) B3564647
theorem B6013703 : Blo 702318 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B705343 : Blo 702318 705343 := bstep (se 1 (by rfl) ⟨529007, by rfl⟩ : syracuseStep 705343 = 1058015) B1058015
theorem B705503 : Blo 702318 705503 := bstep (se 1 (by rfl) ⟨529127, by rfl⟩ : syracuseStep 705503 = 1058255) B1058255
theorem B705627 : Blo 702318 705627 := bstep (se 1 (by rfl) ⟨529220, by rfl⟩ : syracuseStep 705627 = 1058441) B1058441
theorem B705663 : Blo 702318 705663 := bstep (se 1 (by rfl) ⟨529247, by rfl⟩ : syracuseStep 705663 = 1058495) B1058495
theorem B705767 : Blo 702318 705767 := bstep (se 1 (by rfl) ⟨529325, by rfl⟩ : syracuseStep 705767 = 1058651) B1058651
theorem B2377079 : Blo 702318 2377079 := bstep (se 1 (by rfl) ⟨1782809, by rfl⟩ : syracuseStep 2377079 = 3565619) B3565619
theorem B706023 : Blo 702318 706023 := bstep (se 1 (by rfl) ⟨529517, by rfl⟩ : syracuseStep 706023 = 1059035) B1059035
theorem B12011003 : Blo 702318 12011003 := bstep (se 1 (by rfl) ⟨9008252, by rfl⟩ : syracuseStep 12011003 = 18016505) B18016505
theorem B2377295 : Blo 702318 2377295 := bstep (se 1 (by rfl) ⟨1782971, by rfl⟩ : syracuseStep 2377295 = 3565943) B3565943
theorem B706203 : Blo 702318 706203 := bstep (se 1 (by rfl) ⟨529652, by rfl⟩ : syracuseStep 706203 = 1059305) B1059305
theorem B706207 : Blo 702318 706207 := bstep (se 1 (by rfl) ⟨529655, by rfl⟩ : syracuseStep 706207 = 1059311) B1059311
theorem B2672423 : Blo 702318 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B2410279 : Blo 702318 2410279 := bstep (se 1 (by rfl) ⟨1807709, by rfl⟩ : syracuseStep 2410279 = 3615419) B3615419
theorem B2934971 : Blo 702318 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B3393859 : Blo 702318 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B2378159 : Blo 702318 2378159 := bstep (se 1 (by rfl) ⟨1783619, by rfl⟩ : syracuseStep 2378159 = 3567239) B3567239
theorem B1428347 : Blo 702318 1428347 := bstep (se 1 (by rfl) ⟨1071260, by rfl⟩ : syracuseStep 1428347 = 2142521) B2142521
theorem B5852645 : Blo 702318 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B2379239 : Blo 702318 2379239 := bstep (se 1 (by rfl) ⟨1784429, by rfl⟩ : syracuseStep 2379239 = 3568859) B3568859
theorem B6017327 : Blo 702318 6017327 := bstep (se 1 (by rfl) ⟨4512995, by rfl⟩ : syracuseStep 6017327 = 9025991) B9025991
theorem B2380319 : Blo 702318 2380319 := bstep (se 1 (by rfl) ⟨1785239, by rfl⟩ : syracuseStep 2380319 = 3570479) B3570479
theorem B2675537 : Blo 702318 2675537 := bstep (se 2 (by rfl) ⟨1003326, by rfl⟩ : syracuseStep 2675537 = 2006653) B2006653
theorem B1004665 : Blo 702318 1004665 := bstep (se 2 (by rfl) ⟨376749, by rfl⟩ : syracuseStep 1004665 = 753499) B753499
theorem B3560759 : Blo 702318 3560759 := bstep (se 1 (by rfl) ⟨2670569, by rfl⟩ : syracuseStep 3560759 = 5341139) B5341139
theorem B2381129 : Blo 702318 2381129 := bstep (se 2 (by rfl) ⟨892923, by rfl⟩ : syracuseStep 2381129 = 1785847) B1785847
theorem B4019867 : Blo 702318 4019867 := bstep (se 1 (by rfl) ⟨3014900, by rfl⟩ : syracuseStep 4019867 = 6029801) B6029801
theorem B1955519 : Blo 702318 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B5363495 : Blo 702318 5363495 := bstep (se 1 (by rfl) ⟨4022621, by rfl⟩ : syracuseStep 5363495 = 8045243) B8045243
theorem B17094995 : Blo 702318 17094995 := bstep (se 1 (by rfl) ⟨12821246, by rfl⟩ : syracuseStep 17094995 = 25642493) B25642493
theorem B23091713 : Blo 702318 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B2382749 : Blo 702318 2382749 := bstep (se 3 (by rfl) ⟨446765, by rfl⟩ : syracuseStep 2382749 = 893531) B893531
theorem B2382803 : Blo 702318 2382803 := bstep (se 1 (by rfl) ⟨1787102, by rfl⟩ : syracuseStep 2382803 = 3574205) B3574205
theorem B2382857 : Blo 702318 2382857 := bstep (se 2 (by rfl) ⟨893571, by rfl⟩ : syracuseStep 2382857 = 1787143) B1787143
theorem B1072159 : Blo 702318 1072159 := bstep (se 1 (by rfl) ⟨804119, by rfl⟩ : syracuseStep 1072159 = 1608239) B1608239
theorem B2382911 : Blo 702318 2382911 := bstep (se 1 (by rfl) ⟨1787183, by rfl⟩ : syracuseStep 2382911 = 3574367) B3574367
theorem B10149047 : Blo 702318 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B3562703 : Blo 702318 3562703 := bstep (se 1 (by rfl) ⟨2672027, by rfl⟩ : syracuseStep 3562703 = 5344055) B5344055
theorem B1334495 : Blo 702318 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B2383343 : Blo 702318 2383343 := bstep (se 1 (by rfl) ⟨1787507, by rfl⟩ : syracuseStep 2383343 = 3575015) B3575015
theorem B4021757 : Blo 702318 4021757 := bstep (se 3 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 4021757 = 1508159) B1508159
theorem B2678467 : Blo 702318 2678467 := bstep (se 1 (by rfl) ⟨2008850, by rfl⟩ : syracuseStep 2678467 = 4017701) B4017701
theorem B2383721 : Blo 702318 2383721 := bstep (se 2 (by rfl) ⟨893895, by rfl⟩ : syracuseStep 2383721 = 1787791) B1787791
theorem B4808573 : Blo 702318 4808573 := bstep (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) B1803215
theorem B713119 : Blo 702318 713119 := bstep (se 1 (by rfl) ⟨534839, by rfl⟩ : syracuseStep 713119 = 1069679) B1069679
theorem B1500385 : Blo 702318 1500385 := bstep (se 2 (by rfl) ⟨562644, by rfl⟩ : syracuseStep 1500385 = 1125289) B1125289
theorem B2255293 : Blo 702318 2255293 := bstep (se 3 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 2255293 = 845735) B845735
theorem B1337951 : Blo 702318 1337951 := bstep (se 1 (by rfl) ⟨1003463, by rfl⟩ : syracuseStep 1337951 = 2006927) B2006927
theorem B2681657 : Blo 702318 2681657 := bstep (se 2 (by rfl) ⟨1005621, by rfl⟩ : syracuseStep 2681657 = 2011243) B2011243
theorem B5073833 : Blo 702318 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B3010031 : Blo 702318 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B2650411 : Blo 702318 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B5337737 : Blo 702318 5337737 := bstep (se 2 (by rfl) ⟨2001651, by rfl⟩ : syracuseStep 5337737 = 4003303) B4003303
theorem B4289273 : Blo 702318 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B1602473 : Blo 702318 1602473 := bstep (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) B1201855
theorem B30799271 : Blo 702318 30799271 := bstep (se 1 (by rfl) ⟨23099453, by rfl⟩ : syracuseStep 30799271 = 46198907) B46198907
theorem B6026825 : Blo 702318 6026825 := bstep (se 2 (by rfl) ⟨2260059, by rfl⟩ : syracuseStep 6026825 = 4520119) B4520119
theorem B48657995 : Blo 702318 48657995 := bstep (se 1 (by rfl) ⟨36493496, by rfl⟩ : syracuseStep 48657995 = 72986993) B72986993
theorem B3012319 : Blo 702318 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B6781067 : Blo 702318 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B14482691 : Blo 702318 14482691 := bstep (se 1 (by rfl) ⟨10862018, by rfl⟩ : syracuseStep 14482691 = 21724037) B21724037
theorem B3571127 : Blo 702318 3571127 := bstep (se 1 (by rfl) ⟨2678345, by rfl⟩ : syracuseStep 3571127 = 5356691) B5356691
theorem B8781455 : Blo 702318 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B11566759 : Blo 702318 11566759 := bstep (se 1 (by rfl) ⟨8675069, by rfl⟩ : syracuseStep 11566759 = 17350139) B17350139
theorem B3014765 : Blo 702318 3014765 := bstep (se 3 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 3014765 = 1130537) B1130537
theorem B7602407 : Blo 702318 7602407 := bstep (se 1 (by rfl) ⟨5701805, by rfl⟩ : syracuseStep 7602407 = 11403611) B11403611
theorem B950825 : Blo 702318 950825 := bstep (se 2 (by rfl) ⟨356559, by rfl⟩ : syracuseStep 950825 = 713119) B713119
theorem B22872725 : Blo 702318 22872725 := bstep (se 6 (by rfl) ⟨536079, by rfl⟩ : syracuseStep 22872725 = 1072159) B1072159
theorem B2000513 : Blo 702318 2000513 := bstep (se 2 (by rfl) ⟨750192, by rfl⟩ : syracuseStep 2000513 = 1500385) B1500385
theorem B3376849 : Blo 702318 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B3376865 : Blo 702318 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B952231 : Blo 702318 952231 := bstep (se 1 (by rfl) ⟨714173, by rfl⟩ : syracuseStep 952231 = 1428347) B1428347
theorem B3901763 : Blo 702318 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B6425039 : Blo 702318 6425039 := bstep (se 1 (by rfl) ⟨4818779, by rfl⟩ : syracuseStep 6425039 = 9637559) B9637559
theorem B4525145 : Blo 702318 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B3575663 : Blo 702318 3575663 := bstep (se 1 (by rfl) ⟨2681747, by rfl⟩ : syracuseStep 3575663 = 5363495) B5363495
theorem B4002803 : Blo 702318 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B791599 : Blo 702318 791599 := bstep (se 1 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 791599 = 1187399) B1187399
theorem B1053863 : Blo 702318 1053863 := bstep (se 1 (by rfl) ⟨790397, by rfl⟩ : syracuseStep 1053863 = 1580795) B1580795
theorem B7607465 : Blo 702318 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B1054715 : Blo 702318 1054715 := bstep (se 1 (by rfl) ⟨791036, by rfl⟩ : syracuseStep 1054715 = 1582073) B1582073
theorem B792571 : Blo 702318 792571 := bstep (se 1 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 792571 = 1188857) B1188857
theorem B3086525 : Blo 702318 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B1054943 : Blo 702318 1054943 := bstep (se 1 (by rfl) ⟨791207, by rfl⟩ : syracuseStep 1054943 = 1582415) B1582415
theorem B1055327 : Blo 702318 1055327 := bstep (se 1 (by rfl) ⟨791495, by rfl⟩ : syracuseStep 1055327 = 1582991) B1582991
theorem B1186447 : Blo 702318 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B1055423 : Blo 702318 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B793543 : Blo 702318 793543 := bstep (se 1 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 793543 = 1190315) B1190315
theorem B1055807 : Blo 702318 1055807 := bstep (se 1 (by rfl) ⟨791855, by rfl⟩ : syracuseStep 1055807 = 1583711) B1583711
theorem B891967 : Blo 702318 891967 := bstep (se 1 (by rfl) ⟨668975, by rfl⟩ : syracuseStep 891967 = 1337951) B1337951
theorem B3382555 : Blo 702318 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B1056047 : Blo 702318 1056047 := bstep (se 1 (by rfl) ⟨792035, by rfl⟩ : syracuseStep 1056047 = 1584071) B1584071
theorem B793903 : Blo 702318 793903 := bstep (se 1 (by rfl) ⟨595427, by rfl⟩ : syracuseStep 793903 = 1190855) B1190855
theorem B1056287 : Blo 702318 1056287 := bstep (se 1 (by rfl) ⟨792215, by rfl⟩ : syracuseStep 1056287 = 1584431) B1584431
theorem B1580615 : Blo 702318 1580615 := bstep (se 1 (by rfl) ⟨1185461, by rfl⟩ : syracuseStep 1580615 = 2370923) B2370923
theorem B2006687 : Blo 702318 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B1056905 : Blo 702318 1056905 := bstep (se 2 (by rfl) ⟨396339, by rfl⟩ : syracuseStep 1056905 = 792679) B792679
theorem B2859515 : Blo 702318 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B1581947 : Blo 702318 1581947 := bstep (se 1 (by rfl) ⟨1186460, by rfl⟩ : syracuseStep 1581947 = 2372921) B2372921
theorem B1581983 : Blo 702318 1581983 := bstep (se 1 (by rfl) ⟨1186487, by rfl⟩ : syracuseStep 1581983 = 2372975) B2372975
theorem B1582163 : Blo 702318 1582163 := bstep (se 1 (by rfl) ⟨1186622, by rfl⟩ : syracuseStep 1582163 = 2373245) B2373245
theorem B1582217 : Blo 702318 1582217 := bstep (se 2 (by rfl) ⟨593331, by rfl⟩ : syracuseStep 1582217 = 1186663) B1186663
theorem B1779155 : Blo 702318 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B1189343 : Blo 702318 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B12854821 : Blo 702318 12854821 := bstep (se 4 (by rfl) ⟨1205139, by rfl⟩ : syracuseStep 12854821 = 2410279) B2410279
theorem B1058459 : Blo 702318 1058459 := bstep (se 1 (by rfl) ⟨793844, by rfl⟩ : syracuseStep 1058459 = 1587689) B1587689
theorem B1189991 : Blo 702318 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B1058975 : Blo 702318 1058975 := bstep (se 1 (by rfl) ⟨794231, by rfl⟩ : syracuseStep 1058975 = 1588463) B1588463
theorem B1190207 : Blo 702318 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B1059143 : Blo 702318 1059143 := bstep (se 1 (by rfl) ⟨794357, by rfl⟩ : syracuseStep 1059143 = 1588715) B1588715
theorem B1780127 : Blo 702318 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B1584287 : Blo 702318 1584287 := bstep (se 1 (by rfl) ⟨1188215, by rfl⟩ : syracuseStep 1584287 = 2376431) B2376431
theorem B4009135 : Blo 702318 4009135 := bstep (se 1 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 4009135 = 6013703) B6013703
theorem B1584719 : Blo 702318 1584719 := bstep (se 1 (by rfl) ⟨1188539, by rfl⟩ : syracuseStep 1584719 = 2377079) B2377079
theorem B8007335 : Blo 702318 8007335 := bstep (se 1 (by rfl) ⟨6005501, by rfl⟩ : syracuseStep 8007335 = 12011003) B12011003
theorem B3387055 : Blo 702318 3387055 := bstep (se 1 (by rfl) ⟨2540291, by rfl⟩ : syracuseStep 3387055 = 5080583) B5080583
theorem B1584863 : Blo 702318 1584863 := bstep (se 1 (by rfl) ⟨1188647, by rfl⟩ : syracuseStep 1584863 = 2377295) B2377295
theorem B1781615 : Blo 702318 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B1585439 : Blo 702318 1585439 := bstep (se 1 (by rfl) ⟨1189079, by rfl⟩ : syracuseStep 1585439 = 2378159) B2378159
theorem B31306357 : Blo 702318 31306357 := bstep (se 5 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 31306357 = 2934971) B2934971
theorem B1586159 : Blo 702318 1586159 := bstep (se 1 (by rfl) ⟨1189619, by rfl⟩ : syracuseStep 1586159 = 2379239) B2379239
theorem B963751 : Blo 702318 963751 := bstep (se 1 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 963751 = 1445627) B1445627
theorem B4011551 : Blo 702318 4011551 := bstep (se 1 (by rfl) ⟨3008663, by rfl⟩ : syracuseStep 4011551 = 6017327) B6017327
theorem B1586879 : Blo 702318 1586879 := bstep (se 1 (by rfl) ⟨1190159, by rfl⟩ : syracuseStep 1586879 = 2380319) B2380319
theorem B17577809 : Blo 702318 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B1783691 : Blo 702318 1783691 := bstep (se 1 (by rfl) ⟨1337768, by rfl⟩ : syracuseStep 1783691 = 2675537) B2675537
theorem B2373839 : Blo 702318 2373839 := bstep (se 1 (by rfl) ⟨1780379, by rfl⟩ : syracuseStep 2373839 = 3560759) B3560759
theorem B1587419 : Blo 702318 1587419 := bstep (se 1 (by rfl) ⟨1190564, by rfl⟩ : syracuseStep 1587419 = 2381129) B2381129
theorem B6011243 : Blo 702318 6011243 := bstep (se 1 (by rfl) ⟨4508432, by rfl⟩ : syracuseStep 6011243 = 9016865) B9016865
theorem B702959 : Blo 702318 702959 := bstep (se 1 (by rfl) ⟨527219, by rfl⟩ : syracuseStep 702959 = 1054439) B1054439
theorem B703215 : Blo 702318 703215 := bstep (se 1 (by rfl) ⟨527411, by rfl⟩ : syracuseStep 703215 = 1054823) B1054823
theorem B703727 : Blo 702318 703727 := bstep (se 1 (by rfl) ⟨527795, by rfl⟩ : syracuseStep 703727 = 1055591) B1055591
theorem B1588499 : Blo 702318 1588499 := bstep (se 1 (by rfl) ⟨1191374, by rfl⟩ : syracuseStep 1588499 = 2382749) B2382749
theorem B703771 : Blo 702318 703771 := bstep (se 1 (by rfl) ⟨527828, by rfl⟩ : syracuseStep 703771 = 1055657) B1055657
theorem B1588535 : Blo 702318 1588535 := bstep (se 1 (by rfl) ⟨1191401, by rfl⟩ : syracuseStep 1588535 = 2382803) B2382803
theorem B1588571 : Blo 702318 1588571 := bstep (se 1 (by rfl) ⟨1191428, by rfl⟩ : syracuseStep 1588571 = 2382857) B2382857
theorem B1588607 : Blo 702318 1588607 := bstep (se 1 (by rfl) ⟨1191455, by rfl⟩ : syracuseStep 1588607 = 2382911) B2382911
theorem B703899 : Blo 702318 703899 := bstep (se 1 (by rfl) ⟨527924, by rfl⟩ : syracuseStep 703899 = 1055849) B1055849
theorem B6766031 : Blo 702318 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B2375135 : Blo 702318 2375135 := bstep (se 1 (by rfl) ⟨1781351, by rfl⟩ : syracuseStep 2375135 = 3562703) B3562703
theorem B704027 : Blo 702318 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B2375297 : Blo 702318 2375297 := bstep (se 2 (by rfl) ⟨890736, by rfl⟩ : syracuseStep 2375297 = 1781473) B1781473
theorem B1588895 : Blo 702318 1588895 := bstep (se 1 (by rfl) ⟨1191671, by rfl⟩ : syracuseStep 1588895 = 2383343) B2383343
theorem B2670479 : Blo 702318 2670479 := bstep (se 1 (by rfl) ⟨2002859, by rfl⟩ : syracuseStep 2670479 = 4005719) B4005719
theorem B1589147 : Blo 702318 1589147 := bstep (se 1 (by rfl) ⟨1191860, by rfl⟩ : syracuseStep 1589147 = 2383721) B2383721
theorem B704539 : Blo 702318 704539 := bstep (se 1 (by rfl) ⟨528404, by rfl⟩ : syracuseStep 704539 = 1056809) B1056809
theorem B704583 : Blo 702318 704583 := bstep (se 1 (by rfl) ⟨528437, by rfl⟩ : syracuseStep 704583 = 1056875) B1056875
theorem B704751 : Blo 702318 704751 := bstep (se 1 (by rfl) ⟨528563, by rfl⟩ : syracuseStep 704751 = 1057127) B1057127
theorem B704831 : Blo 702318 704831 := bstep (se 1 (by rfl) ⟨528623, by rfl⟩ : syracuseStep 704831 = 1057247) B1057247
theorem B705183 : Blo 702318 705183 := bstep (se 1 (by rfl) ⟨528887, by rfl⟩ : syracuseStep 705183 = 1057775) B1057775
theorem B705263 : Blo 702318 705263 := bstep (se 1 (by rfl) ⟨528947, by rfl⟩ : syracuseStep 705263 = 1057895) B1057895
theorem B705351 : Blo 702318 705351 := bstep (se 1 (by rfl) ⟨529013, by rfl⟩ : syracuseStep 705351 = 1058027) B1058027
theorem B2376701 : Blo 702318 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B1787771 : Blo 702318 1787771 := bstep (se 1 (by rfl) ⟨1340828, by rfl⟩ : syracuseStep 1787771 = 2681657) B2681657
theorem B5359607 : Blo 702318 5359607 := bstep (se 1 (by rfl) ⟨4019705, by rfl⟩ : syracuseStep 5359607 = 8039411) B8039411
theorem B4016425 : Blo 702318 4016425 := bstep (se 2 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 4016425 = 3012319) B3012319
theorem B61590415 : Blo 702318 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B2673607 : Blo 702318 2673607 := bstep (se 1 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 2673607 = 4010411) B4010411
theorem B3558491 : Blo 702318 3558491 := bstep (se 1 (by rfl) ⟨2668868, by rfl⟩ : syracuseStep 3558491 = 5337737) B5337737
theorem B3558653 : Blo 702318 3558653 := bstep (se 3 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 3558653 = 1334495) B1334495
theorem B20532847 : Blo 702318 20532847 := bstep (se 1 (by rfl) ⟨15399635, by rfl⟩ : syracuseStep 20532847 = 30799271) B30799271
theorem B4017883 : Blo 702318 4017883 := bstep (se 1 (by rfl) ⟨3013412, by rfl⟩ : syracuseStep 4017883 = 6026825) B6026825
theorem B23842835 : Blo 702318 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B17093045 : Blo 702318 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B15454799 : Blo 702318 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B10867445 : Blo 702318 10867445 := bstep (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) B1018823
theorem B9655127 : Blo 702318 9655127 := bstep (se 1 (by rfl) ⟨7241345, by rfl⟩ : syracuseStep 9655127 = 14482691) B14482691
theorem B15422345 : Blo 702318 15422345 := bstep (se 2 (by rfl) ⟨5783379, by rfl⟩ : syracuseStep 15422345 = 11566759) B11566759
theorem B2380751 : Blo 702318 2380751 := bstep (se 1 (by rfl) ⟨1785563, by rfl⟩ : syracuseStep 2380751 = 3571127) B3571127
theorem B5854303 : Blo 702318 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B2381723 : Blo 702318 2381723 := bstep (se 1 (by rfl) ⟨1786292, by rfl⟩ : syracuseStep 2381723 = 3572585) B3572585
theorem B1333979 : Blo 702318 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B3007057 : Blo 702318 3007057 := bstep (se 2 (by rfl) ⟨1127646, by rfl⟩ : syracuseStep 3007057 = 2255293) B2255293
theorem B2679911 : Blo 702318 2679911 := bstep (se 1 (by rfl) ⟨2009933, by rfl⟩ : syracuseStep 2679911 = 4019867) B4019867
theorem B1303679 : Blo 702318 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B5072219 : Blo 702318 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B15427097 : Blo 702318 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B11396663 : Blo 702318 11396663 := bstep (se 1 (by rfl) ⟨8547497, by rfl⟩ : syracuseStep 11396663 = 17094995) B17094995
theorem B15394475 : Blo 702318 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B8021915 : Blo 702318 8021915 := bstep (se 1 (by rfl) ⟨6016436, by rfl⟩ : syracuseStep 8021915 = 12032873) B12032873
theorem B9660383 : Blo 702318 9660383 := bstep (se 1 (by rfl) ⟨7245287, by rfl⟩ : syracuseStep 9660383 = 14490575) B14490575
theorem B2681171 : Blo 702318 2681171 := bstep (se 1 (by rfl) ⟨2010878, by rfl⟩ : syracuseStep 2681171 = 4021757) B4021757
theorem B3205715 : Blo 702318 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B3566267 : Blo 702318 3566267 := bstep (se 1 (by rfl) ⟨2674700, by rfl⟩ : syracuseStep 3566267 = 5349401) B5349401
theorem B3533881 : Blo 702318 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B1339553 : Blo 702318 1339553 := bstep (se 2 (by rfl) ⟨502332, by rfl⟩ : syracuseStep 1339553 = 1004665) B1004665
theorem B1601819 : Blo 702318 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B10416509 : Blo 702318 10416509 := bstep (se 3 (by rfl) ⟨1953095, by rfl⟩ : syracuseStep 10416509 = 3906191) B3906191
theorem B41120135 : Blo 702318 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B6779335 : Blo 702318 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B1602175 : Blo 702318 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B2257703 : Blo 702318 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B3569183 : Blo 702318 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B11434031 : Blo 702318 11434031 := bstep (se 1 (by rfl) ⟨8575523, by rfl⟩ : syracuseStep 11434031 = 17151047) B17151047
theorem B32438663 : Blo 702318 32438663 := bstep (se 1 (by rfl) ⟨24328997, by rfl⟩ : syracuseStep 32438663 = 48657995) B48657995
theorem B41777693 : Blo 702318 41777693 := bstep (se 3 (by rfl) ⟨7833317, by rfl⟩ : syracuseStep 41777693 = 15666635) B15666635
theorem B4520711 : Blo 702318 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B7241015 : Blo 702318 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B3571289 : Blo 702318 3571289 := bstep (se 2 (by rfl) ⟨1339233, by rfl⟩ : syracuseStep 3571289 = 2678467) B2678467
theorem B45581453 : Blo 702318 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B3573071 : Blo 702318 3573071 := bstep (se 1 (by rfl) ⟨2679803, by rfl⟩ : syracuseStep 3573071 = 5359607) B5359607
theorem B17139761 : Blo 702318 17139761 := bstep (se 2 (by rfl) ⟨6427410, by rfl⟩ : syracuseStep 17139761 = 12854821) B12854821
theorem B3016763 : Blo 702318 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B15895223 : Blo 702318 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B3476477 : Blo 702318 3476477 := bstep (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) B1303679
theorem B7244963 : Blo 702318 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B82120553 : Blo 702318 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B5345513 : Blo 702318 5345513 := bstep (se 2 (by rfl) ⟨2004567, by rfl⟩ : syracuseStep 5345513 = 4009135) B4009135
theorem B889319 : Blo 702318 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B1053743 : Blo 702318 1053743 := bstep (se 1 (by rfl) ⟨790307, by rfl⟩ : syracuseStep 1053743 = 1580615) B1580615
theorem B1906343 : Blo 702318 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B1054631 : Blo 702318 1054631 := bstep (se 1 (by rfl) ⟨790973, by rfl⟩ : syracuseStep 1054631 = 1581947) B1581947
theorem B1054655 : Blo 702318 1054655 := bstep (se 1 (by rfl) ⟨790991, by rfl⟩ : syracuseStep 1054655 = 1581983) B1581983
theorem B1054775 : Blo 702318 1054775 := bstep (se 1 (by rfl) ⟨791081, by rfl⟩ : syracuseStep 1054775 = 1582163) B1582163
theorem B1054811 : Blo 702318 1054811 := bstep (se 1 (by rfl) ⟨791108, by rfl⟩ : syracuseStep 1054811 = 1582217) B1582217
theorem B2136233 : Blo 702318 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B3381479 : Blo 702318 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B1186103 : Blo 702318 1186103 := bstep (se 1 (by rfl) ⟨889577, by rfl⟩ : syracuseStep 1186103 = 1779155) B1779155
theorem B792895 : Blo 702318 792895 := bstep (se 1 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 792895 = 1189343) B1189343
theorem B10262983 : Blo 702318 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B5347943 : Blo 702318 5347943 := bstep (se 1 (by rfl) ⟨4010957, by rfl⟩ : syracuseStep 5347943 = 8021915) B8021915
theorem B1055465 : Blo 702318 1055465 := bstep (se 2 (by rfl) ⟨395799, by rfl⟩ : syracuseStep 1055465 = 791599) B791599
theorem B793327 : Blo 702318 793327 := bstep (se 1 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 793327 = 1189991) B1189991
theorem B7805737 : Blo 702318 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B793471 : Blo 702318 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B1285001 : Blo 702318 1285001 := bstep (se 2 (by rfl) ⟨481875, by rfl⟩ : syracuseStep 1285001 = 963751) B963751
theorem B1186751 : Blo 702318 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B1056191 : Blo 702318 1056191 := bstep (se 1 (by rfl) ⟨792143, by rfl⟩ : syracuseStep 1056191 = 1584287) B1584287
theorem B1056479 : Blo 702318 1056479 := bstep (se 1 (by rfl) ⟨792359, by rfl⟩ : syracuseStep 1056479 = 1584719) B1584719
theorem B1056575 : Blo 702318 1056575 := bstep (se 1 (by rfl) ⟨792431, by rfl⟩ : syracuseStep 1056575 = 1584863) B1584863
theorem B1187743 : Blo 702318 1187743 := bstep (se 1 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 1187743 = 1781615) B1781615
theorem B1056761 : Blo 702318 1056761 := bstep (se 2 (by rfl) ⟨396285, by rfl⟩ : syracuseStep 1056761 = 792571) B792571
theorem B893035 : Blo 702318 893035 := bstep (se 1 (by rfl) ⟨669776, by rfl⟩ : syracuseStep 893035 = 1339553) B1339553
theorem B1056959 : Blo 702318 1056959 := bstep (se 1 (by rfl) ⟨792719, by rfl⟩ : syracuseStep 1056959 = 1585439) B1585439
theorem B1057439 : Blo 702318 1057439 := bstep (se 1 (by rfl) ⟨793079, by rfl⟩ : syracuseStep 1057439 = 1586159) B1586159
theorem B19309373 : Blo 702318 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B1581929 : Blo 702318 1581929 := bstep (se 2 (by rfl) ⟨593223, by rfl⟩ : syracuseStep 1581929 = 1186447) B1186447
theorem B1057919 : Blo 702318 1057919 := bstep (se 1 (by rfl) ⟨793439, by rfl⟩ : syracuseStep 1057919 = 1586879) B1586879
theorem B1189127 : Blo 702318 1189127 := bstep (se 1 (by rfl) ⟨891845, by rfl⟩ : syracuseStep 1189127 = 1783691) B1783691
theorem B1058057 : Blo 702318 1058057 := bstep (se 2 (by rfl) ⟨396771, by rfl⟩ : syracuseStep 1058057 = 793543) B793543
theorem B1189289 : Blo 702318 1189289 := bstep (se 2 (by rfl) ⟨445983, by rfl⟩ : syracuseStep 1189289 = 891967) B891967
theorem B1582559 : Blo 702318 1582559 := bstep (se 1 (by rfl) ⟨1186919, by rfl⟩ : syracuseStep 1582559 = 2373839) B2373839
theorem B1058279 : Blo 702318 1058279 := bstep (se 1 (by rfl) ⟨793709, by rfl⟩ : syracuseStep 1058279 = 1587419) B1587419
theorem B4007495 : Blo 702318 4007495 := bstep (se 1 (by rfl) ⟨3005621, by rfl⟩ : syracuseStep 4007495 = 6011243) B6011243
theorem B1058537 : Blo 702318 1058537 := bstep (se 2 (by rfl) ⟨396951, by rfl⟩ : syracuseStep 1058537 = 793903) B793903
theorem B1058999 : Blo 702318 1058999 := bstep (se 1 (by rfl) ⟨794249, by rfl⟩ : syracuseStep 1058999 = 1588499) B1588499
theorem B1059023 : Blo 702318 1059023 := bstep (se 1 (by rfl) ⟨794267, by rfl⟩ : syracuseStep 1059023 = 1588535) B1588535
theorem B1059047 : Blo 702318 1059047 := bstep (se 1 (by rfl) ⟨794285, by rfl⟩ : syracuseStep 1059047 = 1588571) B1588571
theorem B1059071 : Blo 702318 1059071 := bstep (se 1 (by rfl) ⟨794303, by rfl⟩ : syracuseStep 1059071 = 1588607) B1588607
theorem B1583423 : Blo 702318 1583423 := bstep (se 1 (by rfl) ⟨1187567, by rfl⟩ : syracuseStep 1583423 = 2375135) B2375135
theorem B1583531 : Blo 702318 1583531 := bstep (se 1 (by rfl) ⟨1187648, by rfl⟩ : syracuseStep 1583531 = 2375297) B2375297
theorem B1059263 : Blo 702318 1059263 := bstep (se 1 (by rfl) ⟨794447, by rfl⟩ : syracuseStep 1059263 = 1588895) B1588895
theorem B1780319 : Blo 702318 1780319 := bstep (se 1 (by rfl) ⟨1335239, by rfl⟩ : syracuseStep 1780319 = 2670479) B2670479
theorem B1059431 : Blo 702318 1059431 := bstep (se 1 (by rfl) ⟨794573, by rfl⟩ : syracuseStep 1059431 = 1589147) B1589147
theorem B2009843 : Blo 702318 2009843 := bstep (se 1 (by rfl) ⟨1507382, by rfl⟩ : syracuseStep 2009843 = 3014765) B3014765
theorem B15248483 : Blo 702318 15248483 := bstep (se 1 (by rfl) ⟨11436362, by rfl⟩ : syracuseStep 15248483 = 22872725) B22872725
theorem B1584467 : Blo 702318 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B4009409 : Blo 702318 4009409 := bstep (se 2 (by rfl) ⟨1503528, by rfl⟩ : syracuseStep 4009409 = 3007057) B3007057
theorem B1191847 : Blo 702318 1191847 := bstep (se 1 (by rfl) ⟨893885, by rfl⟩ : syracuseStep 1191847 = 1787771) B1787771
theorem B2535533 : Blo 702318 2535533 := bstep (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) B950825
theorem B2601175 : Blo 702318 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B2372327 : Blo 702318 2372327 := bstep (se 1 (by rfl) ⟨1779245, by rfl⟩ : syracuseStep 2372327 = 3558491) B3558491
theorem B2372435 : Blo 702318 2372435 := bstep (se 1 (by rfl) ⟨1779326, by rfl⟩ : syracuseStep 2372435 = 3558653) B3558653
theorem B4502465 : Blo 702318 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B10303199 : Blo 702318 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B5355233 : Blo 702318 5355233 := bstep (se 2 (by rfl) ⟨2008212, by rfl⟩ : syracuseStep 5355233 = 4016425) B4016425
theorem B6436751 : Blo 702318 6436751 := bstep (se 1 (by rfl) ⟨4827563, by rfl⟩ : syracuseStep 6436751 = 9655127) B9655127
theorem B166967237 : Blo 702318 166967237 := bstep (se 4 (by rfl) ⟨15653178, by rfl⟩ : syracuseStep 166967237 = 31306357) B31306357
theorem B1587167 : Blo 702318 1587167 := bstep (se 1 (by rfl) ⟨1190375, by rfl⟩ : syracuseStep 1587167 = 2380751) B2380751
theorem B2668535 : Blo 702318 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B702575 : Blo 702318 702575 := bstep (se 1 (by rfl) ⟨526931, by rfl⟩ : syracuseStep 702575 = 1053863) B1053863
theorem B1587815 : Blo 702318 1587815 := bstep (se 1 (by rfl) ⟨1190861, by rfl⟩ : syracuseStep 1587815 = 2381723) B2381723
theorem B703143 : Blo 702318 703143 := bstep (se 1 (by rfl) ⟨527357, by rfl⟩ : syracuseStep 703143 = 1054715) B1054715
theorem B703295 : Blo 702318 703295 := bstep (se 1 (by rfl) ⟨527471, by rfl⟩ : syracuseStep 703295 = 1054943) B1054943
theorem B703551 : Blo 702318 703551 := bstep (se 1 (by rfl) ⟨527663, by rfl⟩ : syracuseStep 703551 = 1055327) B1055327
theorem B703615 : Blo 702318 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B703871 : Blo 702318 703871 := bstep (se 1 (by rfl) ⟨527903, by rfl⟩ : syracuseStep 703871 = 1055807) B1055807
theorem B27377129 : Blo 702318 27377129 := bstep (se 2 (by rfl) ⟨10266423, by rfl⟩ : syracuseStep 27377129 = 20532847) B20532847
theorem B704031 : Blo 702318 704031 := bstep (se 1 (by rfl) ⟨528023, by rfl⟩ : syracuseStep 704031 = 1056047) B1056047
theorem B5357177 : Blo 702318 5357177 := bstep (se 2 (by rfl) ⟨2008941, by rfl⟩ : syracuseStep 5357177 = 4017883) B4017883
theorem B704191 : Blo 702318 704191 := bstep (se 1 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 704191 = 1056287) B1056287
theorem B704603 : Blo 702318 704603 := bstep (se 1 (by rfl) ⟨528452, by rfl⟩ : syracuseStep 704603 = 1056905) B1056905
theorem B1786607 : Blo 702318 1786607 := bstep (se 1 (by rfl) ⟨1339955, by rfl⟩ : syracuseStep 1786607 = 2679911) B2679911
theorem B705639 : Blo 702318 705639 := bstep (se 1 (by rfl) ⟨529229, by rfl⟩ : syracuseStep 705639 = 1058459) B1058459
theorem B6440255 : Blo 702318 6440255 := bstep (se 1 (by rfl) ⟨4830191, by rfl⟩ : syracuseStep 6440255 = 9660383) B9660383
theorem B705983 : Blo 702318 705983 := bstep (se 1 (by rfl) ⟨529487, by rfl⟩ : syracuseStep 705983 = 1058975) B1058975
theorem B706095 : Blo 702318 706095 := bstep (se 1 (by rfl) ⟨529571, by rfl⟩ : syracuseStep 706095 = 1059143) B1059143
theorem B1787447 : Blo 702318 1787447 := bstep (se 1 (by rfl) ⟨1340585, by rfl⟩ : syracuseStep 1787447 = 2681171) B2681171
theorem B2377511 : Blo 702318 2377511 := bstep (se 1 (by rfl) ⟨1783133, by rfl⟩ : syracuseStep 2377511 = 3566267) B3566267
theorem B1067879 : Blo 702318 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B27413423 : Blo 702318 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B2674367 : Blo 702318 2674367 := bstep (se 1 (by rfl) ⟨2005775, by rfl⟩ : syracuseStep 2674367 = 4011551) B4011551
theorem B2379455 : Blo 702318 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B18042749 : Blo 702318 18042749 := bstep (se 3 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 18042749 = 6766031) B6766031
theorem B11718539 : Blo 702318 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B7622687 : Blo 702318 7622687 := bstep (se 1 (by rfl) ⟨5717015, by rfl⟩ : syracuseStep 7622687 = 11434031) B11434031
theorem B4510073 : Blo 702318 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B2380859 : Blo 702318 2380859 := bstep (se 1 (by rfl) ⟨1785644, by rfl⟩ : syracuseStep 2380859 = 3571289) B3571289
theorem B5068271 : Blo 702318 5068271 := bstep (se 1 (by rfl) ⟨3801203, by rfl⟩ : syracuseStep 5068271 = 7602407) B7602407
theorem B1333675 : Blo 702318 1333675 := bstep (se 1 (by rfl) ⟨1000256, by rfl⟩ : syracuseStep 1333675 = 2000513) B2000513
theorem B2251243 : Blo 702318 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B1269641 : Blo 702318 1269641 := bstep (se 2 (by rfl) ⟨476115, by rfl⟩ : syracuseStep 1269641 = 952231) B952231
theorem B2383775 : Blo 702318 2383775 := bstep (se 1 (by rfl) ⟨1787831, by rfl⟩ : syracuseStep 2383775 = 3575663) B3575663
theorem B10281563 : Blo 702318 10281563 := bstep (se 1 (by rfl) ⟨7711172, by rfl⟩ : syracuseStep 10281563 = 15422345) B15422345
theorem B5071643 : Blo 702318 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B3564809 : Blo 702318 3564809 := bstep (se 2 (by rfl) ⟨1336803, by rfl⟩ : syracuseStep 3564809 = 2673607) B2673607
theorem B4711841 : Blo 702318 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B2057683 : Blo 702318 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B4516073 : Blo 702318 4516073 := bstep (se 2 (by rfl) ⟨1693527, by rfl⟩ : syracuseStep 4516073 = 3387055) B3387055
theorem B1337791 : Blo 702318 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B9039113 : Blo 702318 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B10284731 : Blo 702318 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B7597775 : Blo 702318 7597775 := bstep (se 1 (by rfl) ⟨5698331, by rfl⟩ : syracuseStep 7597775 = 11396663) B11396663
theorem B17133437 : Blo 702318 17133437 := bstep (se 3 (by rfl) ⟨3212519, by rfl⟩ : syracuseStep 17133437 = 6425039) B6425039
theorem B8548573 : Blo 702318 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B5338223 : Blo 702318 5338223 := bstep (se 1 (by rfl) ⟨4003667, by rfl⟩ : syracuseStep 5338223 = 8007335) B8007335
theorem B6944339 : Blo 702318 6944339 := bstep (se 1 (by rfl) ⟨5208254, by rfl⟩ : syracuseStep 6944339 = 10416509) B10416509
theorem B1505135 : Blo 702318 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B21625775 : Blo 702318 21625775 := bstep (se 1 (by rfl) ⟨16219331, by rfl⟩ : syracuseStep 21625775 = 32438663) B32438663
theorem B27851795 : Blo 702318 27851795 := bstep (se 1 (by rfl) ⟨20888846, by rfl⟩ : syracuseStep 27851795 = 41777693) B41777693
theorem B3013807 : Blo 702318 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B4293503 : Blo 702318 4293503 := bstep (se 1 (by rfl) ⟨3220127, by rfl⟩ : syracuseStep 4293503 = 6440255) B6440255
theorem B12028499 : Blo 702318 12028499 := bstep (se 1 (by rfl) ⟨9021374, by rfl⟩ : syracuseStep 12028499 = 18042749) B18042749
theorem B5081791 : Blo 702318 5081791 := bstep (se 1 (by rfl) ⟨3811343, by rfl⟩ : syracuseStep 5081791 = 7622687) B7622687
theorem B3378847 : Blo 702318 3378847 := bstep (se 1 (by rfl) ⟨2534135, by rfl⟩ : syracuseStep 3378847 = 5068271) B5068271
theorem B790735 : Blo 702318 790735 := bstep (se 1 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 790735 = 1186103) B1186103
theorem B856667 : Blo 702318 856667 := bstep (se 1 (by rfl) ⟨642500, by rfl⟩ : syracuseStep 856667 = 1285001) B1285001
theorem B791167 : Blo 702318 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B6854375 : Blo 702318 6854375 := bstep (se 1 (by rfl) ⟨5140781, by rfl⟩ : syracuseStep 6854375 = 10281563) B10281563
theorem B3381095 : Blo 702318 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B1054619 : Blo 702318 1054619 := bstep (se 1 (by rfl) ⟨790964, by rfl⟩ : syracuseStep 1054619 = 1581929) B1581929
theorem B792751 : Blo 702318 792751 := bstep (se 1 (by rfl) ⟨594563, by rfl⟩ : syracuseStep 792751 = 1189127) B1189127
theorem B792859 : Blo 702318 792859 := bstep (se 1 (by rfl) ⟨594644, by rfl⟩ : syracuseStep 792859 = 1189289) B1189289
theorem B1055039 : Blo 702318 1055039 := bstep (se 1 (by rfl) ⟨791279, by rfl⟩ : syracuseStep 1055039 = 1582559) B1582559
theorem B1055615 : Blo 702318 1055615 := bstep (se 1 (by rfl) ⟨791711, by rfl⟩ : syracuseStep 1055615 = 1583423) B1583423
theorem B1055687 : Blo 702318 1055687 := bstep (se 1 (by rfl) ⟨791765, by rfl⟩ : syracuseStep 1055687 = 1583531) B1583531
theorem B1186879 : Blo 702318 1186879 := bstep (se 1 (by rfl) ⟨890159, by rfl⟩ : syracuseStep 1186879 = 1780319) B1780319
theorem B10165655 : Blo 702318 10165655 := bstep (se 1 (by rfl) ⟨7624241, by rfl⟩ : syracuseStep 10165655 = 15248483) B15248483
theorem B1056311 : Blo 702318 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B6856487 : Blo 702318 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B1057193 : Blo 702318 1057193 := bstep (se 2 (by rfl) ⟨396447, by rfl⟩ : syracuseStep 1057193 = 792895) B792895
theorem B1581551 : Blo 702318 1581551 := bstep (se 1 (by rfl) ⟨1186163, by rfl⟩ : syracuseStep 1581551 = 2372327) B2372327
theorem B1581623 : Blo 702318 1581623 := bstep (se 1 (by rfl) ⟨1186217, by rfl⟩ : syracuseStep 1581623 = 2372435) B2372435
theorem B1778233 : Blo 702318 1778233 := bstep (se 2 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 1778233 = 1333675) B1333675
theorem B1057769 : Blo 702318 1057769 := bstep (se 2 (by rfl) ⟨396663, by rfl⟩ : syracuseStep 1057769 = 793327) B793327
theorem B4629559 : Blo 702318 4629559 := bstep (se 1 (by rfl) ⟨3472169, by rfl⟩ : syracuseStep 4629559 = 6944339) B6944339
theorem B1057961 : Blo 702318 1057961 := bstep (se 2 (by rfl) ⟨396735, by rfl⟩ : syracuseStep 1057961 = 793471) B793471
theorem B1058111 : Blo 702318 1058111 := bstep (se 1 (by rfl) ⟨793583, by rfl⟩ : syracuseStep 1058111 = 1587167) B1587167
theorem B1779023 : Blo 702318 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B1058543 : Blo 702318 1058543 := bstep (se 1 (by rfl) ⟨793907, by rfl⟩ : syracuseStep 1058543 = 1587815) B1587815
theorem B3385709 : Blo 702318 3385709 := bstep (se 3 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 3385709 = 1269641) B1269641
theorem B1583657 : Blo 702318 1583657 := bstep (se 2 (by rfl) ⟨593871, by rfl⟩ : syracuseStep 1583657 = 1187743) B1187743
theorem B1190713 : Blo 702318 1190713 := bstep (se 2 (by rfl) ⟨446517, by rfl⟩ : syracuseStep 1190713 = 893035) B893035
theorem B1191071 : Blo 702318 1191071 := bstep (se 1 (by rfl) ⟨893303, by rfl⟩ : syracuseStep 1191071 = 1786607) B1786607
theorem B30387635 : Blo 702318 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B1191631 : Blo 702318 1191631 := bstep (se 1 (by rfl) ⟨893723, by rfl⟩ : syracuseStep 1191631 = 1787447) B1787447
theorem B1585007 : Blo 702318 1585007 := bstep (se 1 (by rfl) ⟨1188755, by rfl⟩ : syracuseStep 1585007 = 2377511) B2377511
theorem B2371517 : Blo 702318 2371517 := bstep (se 3 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 2371517 = 889319) B889319
theorem B2011175 : Blo 702318 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B10596815 : Blo 702318 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B4829975 : Blo 702318 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B1782911 : Blo 702318 1782911 := bstep (se 1 (by rfl) ⟨1337183, by rfl⟩ : syracuseStep 1782911 = 2674367) B2674367
theorem B1586303 : Blo 702318 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B12006629 : Blo 702318 12006629 := bstep (se 4 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 12006629 = 2251243) B2251243
theorem B7812359 : Blo 702318 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B1783721 : Blo 702318 1783721 := bstep (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) B1337791
theorem B702495 : Blo 702318 702495 := bstep (se 1 (by rfl) ⟨526871, by rfl⟩ : syracuseStep 702495 = 1053743) B1053743
theorem B1587239 : Blo 702318 1587239 := bstep (se 1 (by rfl) ⟨1190429, by rfl⟩ : syracuseStep 1587239 = 2380859) B2380859
theorem B703087 : Blo 702318 703087 := bstep (se 1 (by rfl) ⟨527315, by rfl⟩ : syracuseStep 703087 = 1054631) B1054631
theorem B703103 : Blo 702318 703103 := bstep (se 1 (by rfl) ⟨527327, by rfl⟩ : syracuseStep 703103 = 1054655) B1054655
theorem B703183 : Blo 702318 703183 := bstep (se 1 (by rfl) ⟨527387, by rfl⟩ : syracuseStep 703183 = 1054775) B1054775
theorem B703207 : Blo 702318 703207 := bstep (se 1 (by rfl) ⟨527405, by rfl⟩ : syracuseStep 703207 = 1054811) B1054811
theorem B1424155 : Blo 702318 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B703643 : Blo 702318 703643 := bstep (se 1 (by rfl) ⟨527732, by rfl⟩ : syracuseStep 703643 = 1055465) B1055465
theorem B704127 : Blo 702318 704127 := bstep (se 1 (by rfl) ⟨528095, by rfl⟩ : syracuseStep 704127 = 1056191) B1056191
theorem B704319 : Blo 702318 704319 := bstep (se 1 (by rfl) ⟨528239, by rfl⟩ : syracuseStep 704319 = 1056479) B1056479
theorem B704383 : Blo 702318 704383 := bstep (se 1 (by rfl) ⟨528287, by rfl⟩ : syracuseStep 704383 = 1056575) B1056575
theorem B1589129 : Blo 702318 1589129 := bstep (se 2 (by rfl) ⟨595923, by rfl⟩ : syracuseStep 1589129 = 1191847) B1191847
theorem B1589183 : Blo 702318 1589183 := bstep (se 1 (by rfl) ⟨1191887, by rfl⟩ : syracuseStep 1589183 = 2383775) B2383775
theorem B704507 : Blo 702318 704507 := bstep (se 1 (by rfl) ⟨528380, by rfl⟩ : syracuseStep 704507 = 1056761) B1056761
theorem B704639 : Blo 702318 704639 := bstep (se 1 (by rfl) ⟨528479, by rfl⟩ : syracuseStep 704639 = 1056959) B1056959
theorem B704959 : Blo 702318 704959 := bstep (se 1 (by rfl) ⟨528719, by rfl⟩ : syracuseStep 704959 = 1057439) B1057439
theorem B705279 : Blo 702318 705279 := bstep (se 1 (by rfl) ⟨528959, by rfl⟩ : syracuseStep 705279 = 1057919) B1057919
theorem B2376539 : Blo 702318 2376539 := bstep (se 1 (by rfl) ⟨1782404, by rfl⟩ : syracuseStep 2376539 = 3564809) B3564809
theorem B705371 : Blo 702318 705371 := bstep (se 1 (by rfl) ⟨529028, by rfl⟩ : syracuseStep 705371 = 1058057) B1058057
theorem B705519 : Blo 702318 705519 := bstep (se 1 (by rfl) ⟨529139, by rfl⟩ : syracuseStep 705519 = 1058279) B1058279
theorem B2671663 : Blo 702318 2671663 := bstep (se 1 (by rfl) ⟨2003747, by rfl⟩ : syracuseStep 2671663 = 4007495) B4007495
theorem B705691 : Blo 702318 705691 := bstep (se 1 (by rfl) ⟨529268, by rfl⟩ : syracuseStep 705691 = 1058537) B1058537
theorem B705999 : Blo 702318 705999 := bstep (se 1 (by rfl) ⟨529499, by rfl⟩ : syracuseStep 705999 = 1058999) B1058999
theorem B706015 : Blo 702318 706015 := bstep (se 1 (by rfl) ⟨529511, by rfl⟩ : syracuseStep 706015 = 1059023) B1059023
theorem B706031 : Blo 702318 706031 := bstep (se 1 (by rfl) ⟨529523, by rfl⟩ : syracuseStep 706031 = 1059047) B1059047
theorem B706047 : Blo 702318 706047 := bstep (se 1 (by rfl) ⟨529535, by rfl⟩ : syracuseStep 706047 = 1059071) B1059071
theorem B706175 : Blo 702318 706175 := bstep (se 1 (by rfl) ⟨529631, by rfl⟩ : syracuseStep 706175 = 1059263) B1059263
theorem B706287 : Blo 702318 706287 := bstep (se 1 (by rfl) ⟨529715, by rfl⟩ : syracuseStep 706287 = 1059431) B1059431
theorem B2672939 : Blo 702318 2672939 := bstep (se 1 (by rfl) ⟨2004704, by rfl⟩ : syracuseStep 2672939 = 4009409) B4009409
theorem B5065183 : Blo 702318 5065183 := bstep (se 1 (by rfl) ⟨3798887, by rfl⟩ : syracuseStep 5065183 = 7597775) B7597775
theorem B11422291 : Blo 702318 11422291 := bstep (se 1 (by rfl) ⟨8566718, by rfl⟩ : syracuseStep 11422291 = 17133437) B17133437
theorem B1690355 : Blo 702318 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B13683977 : Blo 702318 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B3001643 : Blo 702318 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B3558815 : Blo 702318 3558815 := bstep (se 1 (by rfl) ⟨2669111, by rfl⟩ : syracuseStep 3558815 = 5338223) B5338223
theorem B10407649 : Blo 702318 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B6868799 : Blo 702318 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B1003423 : Blo 702318 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B4018409 : Blo 702318 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B18567863 : Blo 702318 18567863 := bstep (se 1 (by rfl) ⟨13925897, by rfl⟩ : syracuseStep 18567863 = 27851795) B27851795
theorem B2382047 : Blo 702318 2382047 := bstep (se 1 (by rfl) ⟨1786535, by rfl⟩ : syracuseStep 2382047 = 3573071) B3573071
theorem B11426507 : Blo 702318 11426507 := bstep (se 1 (by rfl) ⟨8569880, by rfl⟩ : syracuseStep 11426507 = 17139761) B17139761
theorem B711919 : Blo 702318 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B2743577 : Blo 702318 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B18275615 : Blo 702318 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B54747035 : Blo 702318 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B3563675 : Blo 702318 3563675 := bstep (se 1 (by rfl) ⟨2672756, by rfl⟩ : syracuseStep 3563675 = 5345513) B5345513
theorem B3006715 : Blo 702318 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B1270895 : Blo 702318 1270895 := bstep (se 1 (by rfl) ⟨953171, by rfl⟩ : syracuseStep 1270895 = 1906343) B1906343
theorem B2254319 : Blo 702318 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B3565295 : Blo 702318 3565295 := bstep (se 1 (by rfl) ⟨2673971, by rfl⟩ : syracuseStep 3565295 = 5347943) B5347943
theorem B17164669 : Blo 702318 17164669 := bstep (se 3 (by rfl) ⟨3218375, by rfl⟩ : syracuseStep 17164669 = 6436751) B6436751
theorem B445245965 : Blo 702318 445245965 := bstep (se 3 (by rfl) ⟨83483618, by rfl⟩ : syracuseStep 445245965 = 166967237) B166967237
theorem B3468233 : Blo 702318 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B11398097 : Blo 702318 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B12872915 : Blo 702318 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B3141227 : Blo 702318 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B3010715 : Blo 702318 3010715 := bstep (se 1 (by rfl) ⟨2258036, by rfl⟩ : syracuseStep 3010715 = 4516073) B4516073
theorem B1339895 : Blo 702318 1339895 := bstep (se 1 (by rfl) ⟨1004921, by rfl⟩ : syracuseStep 1339895 = 2009843) B2009843
theorem B6026075 : Blo 702318 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B9270605 : Blo 702318 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B3570155 : Blo 702318 3570155 := bstep (se 1 (by rfl) ⟨2677616, by rfl⟩ : syracuseStep 3570155 = 5355233) B5355233
theorem B14417183 : Blo 702318 14417183 := bstep (se 1 (by rfl) ⟨10812887, by rfl⟩ : syracuseStep 14417183 = 21625775) B21625775
theorem B18251419 : Blo 702318 18251419 := bstep (se 1 (by rfl) ⟨13688564, by rfl⟩ : syracuseStep 18251419 = 27377129) B27377129
theorem B3571451 : Blo 702318 3571451 := bstep (se 1 (by rfl) ⟨2678588, by rfl⟩ : syracuseStep 3571451 = 5357177) B5357177
theorem B2001095 : Blo 702318 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B6753577 : Blo 702318 6753577 := bstep (se 2 (by rfl) ⟨2532591, by rfl⟩ : syracuseStep 6753577 = 5065183) B5065183
theorem B1054313 : Blo 702318 1054313 := bstep (se 2 (by rfl) ⟨395367, by rfl⟩ : syracuseStep 1054313 = 790735) B790735
theorem B1054367 : Blo 702318 1054367 := bstep (se 1 (by rfl) ⟨790775, by rfl⟩ : syracuseStep 1054367 = 1581551) B1581551
theorem B1054415 : Blo 702318 1054415 := bstep (se 1 (by rfl) ⟨790811, by rfl⟩ : syracuseStep 1054415 = 1581623) B1581623
theorem B1054889 : Blo 702318 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B1186015 : Blo 702318 1186015 := bstep (se 1 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 1186015 = 1779023) B1779023
theorem B1055771 : Blo 702318 1055771 := bstep (se 1 (by rfl) ⟨791828, by rfl⟩ : syracuseStep 1055771 = 1583657) B1583657
theorem B794047 : Blo 702318 794047 := bstep (se 1 (by rfl) ⟨595535, by rfl⟩ : syracuseStep 794047 = 1191071) B1191071
theorem B20258423 : Blo 702318 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B1056671 : Blo 702318 1056671 := bstep (se 1 (by rfl) ⟨792503, by rfl⟩ : syracuseStep 1056671 = 1585007) B1585007
theorem B1581011 : Blo 702318 1581011 := bstep (se 1 (by rfl) ⟨1185758, by rfl⟩ : syracuseStep 1581011 = 2371517) B2371517
theorem B2007143 : Blo 702318 2007143 := bstep (se 1 (by rfl) ⟨1505357, by rfl⟩ : syracuseStep 2007143 = 3010715) B3010715
theorem B1057001 : Blo 702318 1057001 := bstep (se 2 (by rfl) ⟨396375, by rfl⟩ : syracuseStep 1057001 = 792751) B792751
theorem B893263 : Blo 702318 893263 := bstep (se 1 (by rfl) ⟨669947, by rfl⟩ : syracuseStep 893263 = 1339895) B1339895
theorem B1057145 : Blo 702318 1057145 := bstep (se 2 (by rfl) ⟨396429, by rfl⟩ : syracuseStep 1057145 = 792859) B792859
theorem B3219983 : Blo 702318 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B1188607 : Blo 702318 1188607 := bstep (se 1 (by rfl) ⟨891455, by rfl⟩ : syracuseStep 1188607 = 1782911) B1782911
theorem B1057535 : Blo 702318 1057535 := bstep (se 1 (by rfl) ⟨793151, by rfl⟩ : syracuseStep 1057535 = 1586303) B1586303
theorem B8004419 : Blo 702318 8004419 := bstep (se 1 (by rfl) ⟨6003314, by rfl⟩ : syracuseStep 8004419 = 12006629) B12006629
theorem B1189147 : Blo 702318 1189147 := bstep (se 1 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 1189147 = 1783721) B1783721
theorem B1058159 : Blo 702318 1058159 := bstep (se 1 (by rfl) ⟨793619, by rfl⟩ : syracuseStep 1058159 = 1587239) B1587239
theorem B1582505 : Blo 702318 1582505 := bstep (se 2 (by rfl) ⟨593439, by rfl⟩ : syracuseStep 1582505 = 1186879) B1186879
theorem B9611455 : Blo 702318 9611455 := bstep (se 1 (by rfl) ⟨7208591, by rfl⟩ : syracuseStep 9611455 = 14417183) B14417183
theorem B1059419 : Blo 702318 1059419 := bstep (se 1 (by rfl) ⟨794564, by rfl⟩ : syracuseStep 1059419 = 1589129) B1589129
theorem B1059455 : Blo 702318 1059455 := bstep (se 1 (by rfl) ⟨794591, by rfl⟩ : syracuseStep 1059455 = 1589183) B1589183
theorem B4008953 : Blo 702318 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B18997161173 : Blo 702318 18997161173 := bstep (se 7 (by rfl) ⟨222622982, by rfl⟩ : syracuseStep 18997161173 = 445245965) B445245965
theorem B1584359 : Blo 702318 1584359 := bstep (se 1 (by rfl) ⟨1188269, by rfl⟩ : syracuseStep 1584359 = 2376539) B2376539
theorem B2862335 : Blo 702318 2862335 := bstep (se 1 (by rfl) ⟨2146751, by rfl⟩ : syracuseStep 2862335 = 4293503) B4293503
theorem B2370977 : Blo 702318 2370977 := bstep (se 2 (by rfl) ⟨889116, by rfl⟩ : syracuseStep 2370977 = 1778233) B1778233
theorem B6172745 : Blo 702318 6172745 := bstep (se 2 (by rfl) ⟨2314779, by rfl⟩ : syracuseStep 6172745 = 4629559) B4629559
theorem B1781959 : Blo 702318 1781959 := bstep (se 1 (by rfl) ⟨1336469, by rfl⟩ : syracuseStep 1781959 = 2672939) B2672939
theorem B9122651 : Blo 702318 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B2372543 : Blo 702318 2372543 := bstep (se 1 (by rfl) ⟨1779407, by rfl⟩ : syracuseStep 2372543 = 3558815) B3558815
theorem B3389053 : Blo 702318 3389053 := bstep (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) B1270895
theorem B22886225 : Blo 702318 22886225 := bstep (se 2 (by rfl) ⟨8582334, by rfl⟩ : syracuseStep 22886225 = 17164669) B17164669
theorem B1587617 : Blo 702318 1587617 := bstep (se 2 (by rfl) ⟨595356, by rfl⟩ : syracuseStep 1587617 = 1190713) B1190713
theorem B4569583 : Blo 702318 4569583 := bstep (se 1 (by rfl) ⟨3427187, by rfl⟩ : syracuseStep 4569583 = 6854375) B6854375
theorem B703079 : Blo 702318 703079 := bstep (se 1 (by rfl) ⟨527309, by rfl⟩ : syracuseStep 703079 = 1054619) B1054619
theorem B1588031 : Blo 702318 1588031 := bstep (se 1 (by rfl) ⟨1191023, by rfl⟩ : syracuseStep 1588031 = 2382047) B2382047
theorem B703359 : Blo 702318 703359 := bstep (se 1 (by rfl) ⟨527519, by rfl⟩ : syracuseStep 703359 = 1055039) B1055039
theorem B7617671 : Blo 702318 7617671 := bstep (se 1 (by rfl) ⟨5713253, by rfl⟩ : syracuseStep 7617671 = 11426507) B11426507
theorem B703743 : Blo 702318 703743 := bstep (se 1 (by rfl) ⟨527807, by rfl⟩ : syracuseStep 703743 = 1055615) B1055615
theorem B703791 : Blo 702318 703791 := bstep (se 1 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 703791 = 1055687) B1055687
theorem B4505129 : Blo 702318 4505129 := bstep (se 2 (by rfl) ⟨1689423, by rfl⟩ : syracuseStep 4505129 = 3378847) B3378847
theorem B1588841 : Blo 702318 1588841 := bstep (se 2 (by rfl) ⟨595815, by rfl⟩ : syracuseStep 1588841 = 1191631) B1191631
theorem B13876865 : Blo 702318 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B704207 : Blo 702318 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B4570991 : Blo 702318 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B2375783 : Blo 702318 2375783 := bstep (se 1 (by rfl) ⟨1781837, by rfl⟩ : syracuseStep 2375783 = 3563675) B3563675
theorem B704795 : Blo 702318 704795 := bstep (se 1 (by rfl) ⟨528596, by rfl⟩ : syracuseStep 704795 = 1057193) B1057193
theorem B705179 : Blo 702318 705179 := bstep (se 1 (by rfl) ⟨528884, by rfl⟩ : syracuseStep 705179 = 1057769) B1057769
theorem B705307 : Blo 702318 705307 := bstep (se 1 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 705307 = 1057961) B1057961
theorem B705407 : Blo 702318 705407 := bstep (se 1 (by rfl) ⟨529055, by rfl⟩ : syracuseStep 705407 = 1058111) B1058111
theorem B2376863 : Blo 702318 2376863 := bstep (se 1 (by rfl) ⟨1782647, by rfl⟩ : syracuseStep 2376863 = 3565295) B3565295
theorem B705695 : Blo 702318 705695 := bstep (se 1 (by rfl) ⟨529271, by rfl⟩ : syracuseStep 705695 = 1058543) B1058543
theorem B2312155 : Blo 702318 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B4507613 : Blo 702318 4507613 := bstep (se 3 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 4507613 = 1690355) B1690355
theorem B7064543 : Blo 702318 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B4017383 : Blo 702318 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B6180403 : Blo 702318 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B8376605 : Blo 702318 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B2380103 : Blo 702318 2380103 := bstep (se 1 (by rfl) ⟨1785077, by rfl⟩ : syracuseStep 2380103 = 3570155) B3570155
theorem B24335225 : Blo 702318 24335225 := bstep (se 2 (by rfl) ⟨9125709, by rfl⟩ : syracuseStep 24335225 = 18251419) B18251419
theorem B2380967 : Blo 702318 2380967 := bstep (se 1 (by rfl) ⟨1785725, by rfl⟩ : syracuseStep 2380967 = 3571451) B3571451
theorem B3562217 : Blo 702318 3562217 := bstep (se 2 (by rfl) ⟨1335831, by rfl⟩ : syracuseStep 3562217 = 2671663) B2671663
theorem B2284445 : Blo 702318 2284445 := bstep (se 3 (by rfl) ⟨428333, by rfl⟩ : syracuseStep 2284445 = 856667) B856667
theorem B8018999 : Blo 702318 8018999 := bstep (se 1 (by rfl) ⟨6014249, by rfl⟩ : syracuseStep 8018999 = 12028499) B12028499
theorem B4579199 : Blo 702318 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B2678939 : Blo 702318 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B12378575 : Blo 702318 12378575 := bstep (se 1 (by rfl) ⟨9283931, by rfl⟩ : syracuseStep 12378575 = 18567863) B18567863
theorem B15229721 : Blo 702318 15229721 := bstep (se 2 (by rfl) ⟨5711145, by rfl⟩ : syracuseStep 15229721 = 11422291) B11422291
theorem B6775721 : Blo 702318 6775721 := bstep (se 2 (by rfl) ⟨2540895, by rfl⟩ : syracuseStep 6775721 = 5081791) B5081791
theorem B2254063 : Blo 702318 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B1829051 : Blo 702318 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B12183743 : Blo 702318 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B6777103 : Blo 702318 6777103 := bstep (se 1 (by rfl) ⟨5082827, by rfl⟩ : syracuseStep 6777103 = 10165655) B10165655
theorem B1337897 : Blo 702318 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B36498023 : Blo 702318 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B1502879 : Blo 702318 1502879 := bstep (se 1 (by rfl) ⟨1127159, by rfl⟩ : syracuseStep 1502879 = 2254319) B2254319
theorem B2257139 : Blo 702318 2257139 := bstep (se 1 (by rfl) ⟨1692854, by rfl⟩ : syracuseStep 2257139 = 3385709) B3385709
theorem B7598731 : Blo 702318 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B8581943 : Blo 702318 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B1340783 : Blo 702318 1340783 := bstep (se 1 (by rfl) ⟨1005587, by rfl⟩ : syracuseStep 1340783 = 2011175) B2011175
theorem B5208239 : Blo 702318 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B1898873 : Blo 702318 1898873 := bstep (se 2 (by rfl) ⟨712077, by rfl⟩ : syracuseStep 1898873 = 1424155) B1424155
theorem B949225 : Blo 702318 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B3082873 : Blo 702318 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B12815273 : Blo 702318 12815273 := bstep (se 2 (by rfl) ⟨4805727, by rfl⟩ : syracuseStep 12815273 = 9611455) B9611455
theorem B16223483 : Blo 702318 16223483 := bstep (se 1 (by rfl) ⟨12167612, by rfl⟩ : syracuseStep 16223483 = 24335225) B24335225
theorem B5345999 : Blo 702318 5345999 := bstep (se 1 (by rfl) ⟨4009499, by rfl⟩ : syracuseStep 5345999 = 8018999) B8018999
theorem B13505615 : Blo 702318 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B3052799 : Blo 702318 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B1054007 : Blo 702318 1054007 := bstep (se 1 (by rfl) ⟨790505, by rfl⟩ : syracuseStep 1054007 = 1581011) B1581011
theorem B10131641 : Blo 702318 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B1055003 : Blo 702318 1055003 := bstep (se 1 (by rfl) ⟨791252, by rfl⟩ : syracuseStep 1055003 = 1582505) B1582505
theorem B1219367 : Blo 702318 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B12664774115 : Blo 702318 12664774115 := bstep (se 1 (by rfl) ⟨9498580586, by rfl⟩ : syracuseStep 12664774115 = 18997161173) B18997161173
theorem B1056239 : Blo 702318 1056239 := bstep (se 1 (by rfl) ⟨792179, by rfl⟩ : syracuseStep 1056239 = 1584359) B1584359
theorem B1580651 : Blo 702318 1580651 := bstep (se 1 (by rfl) ⟨1185488, by rfl⟩ : syracuseStep 1580651 = 2370977) B2370977
theorem B1581353 : Blo 702318 1581353 := bstep (se 2 (by rfl) ⟨593007, by rfl⟩ : syracuseStep 1581353 = 1186015) B1186015
theorem B1581695 : Blo 702318 1581695 := bstep (se 1 (by rfl) ⟨1186271, by rfl⟩ : syracuseStep 1581695 = 2372543) B2372543
theorem B893855 : Blo 702318 893855 := bstep (se 1 (by rfl) ⟨670391, by rfl⟩ : syracuseStep 893855 = 1340783) B1340783
theorem B1058411 : Blo 702318 1058411 := bstep (se 1 (by rfl) ⟨793808, by rfl⟩ : syracuseStep 1058411 = 1587617) B1587617
theorem B4007677 : Blo 702318 4007677 := bstep (se 3 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 4007677 = 1502879) B1502879
theorem B1058687 : Blo 702318 1058687 := bstep (se 1 (by rfl) ⟨794015, by rfl⟩ : syracuseStep 1058687 = 1588031) B1588031
theorem B1058729 : Blo 702318 1058729 := bstep (se 2 (by rfl) ⟨397023, by rfl⟩ : syracuseStep 1058729 = 794047) B794047
theorem B1059227 : Blo 702318 1059227 := bstep (se 1 (by rfl) ⟨794420, by rfl⟩ : syracuseStep 1059227 = 1588841) B1588841
theorem B9251243 : Blo 702318 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B1583855 : Blo 702318 1583855 := bstep (se 1 (by rfl) ⟨1187891, by rfl⟩ : syracuseStep 1583855 = 2375783) B2375783
theorem B16460653 : Blo 702318 16460653 := bstep (se 3 (by rfl) ⟨3086372, by rfl⟩ : syracuseStep 16460653 = 6172745) B6172745
theorem B1191017 : Blo 702318 1191017 := bstep (se 2 (by rfl) ⟨446631, by rfl⟩ : syracuseStep 1191017 = 893263) B893263
theorem B1584575 : Blo 702318 1584575 := bstep (se 1 (by rfl) ⟨1188431, by rfl⟩ : syracuseStep 1584575 = 2376863) B2376863
theorem B1584809 : Blo 702318 1584809 := bstep (se 2 (by rfl) ⟨594303, by rfl⟩ : syracuseStep 1584809 = 1188607) B1188607
theorem B1585529 : Blo 702318 1585529 := bstep (se 2 (by rfl) ⟨594573, by rfl⟩ : syracuseStep 1585529 = 1189147) B1189147
theorem B5584403 : Blo 702318 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B1586735 : Blo 702318 1586735 := bstep (se 1 (by rfl) ⟨1190051, by rfl⟩ : syracuseStep 1586735 = 2380103) B2380103
theorem B1587311 : Blo 702318 1587311 := bstep (se 1 (by rfl) ⟨1190483, by rfl⟩ : syracuseStep 1587311 = 2380967) B2380967
theorem B702875 : Blo 702318 702875 := bstep (se 1 (by rfl) ⟨527156, by rfl⟩ : syracuseStep 702875 = 1054313) B1054313
theorem B702911 : Blo 702318 702911 := bstep (se 1 (by rfl) ⟨527183, by rfl⟩ : syracuseStep 702911 = 1054367) B1054367
theorem B702943 : Blo 702318 702943 := bstep (se 1 (by rfl) ⟨527207, by rfl⟩ : syracuseStep 702943 = 1054415) B1054415
theorem B703259 : Blo 702318 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B2374811 : Blo 702318 2374811 := bstep (se 1 (by rfl) ⟨1781108, by rfl⟩ : syracuseStep 2374811 = 3562217) B3562217
theorem B1522963 : Blo 702318 1522963 := bstep (se 1 (by rfl) ⟨1142222, by rfl⟩ : syracuseStep 1522963 = 2284445) B2284445
theorem B703847 : Blo 702318 703847 := bstep (se 1 (by rfl) ⟨527885, by rfl⟩ : syracuseStep 703847 = 1055771) B1055771
theorem B8240537 : Blo 702318 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B704447 : Blo 702318 704447 := bstep (se 1 (by rfl) ⟨528335, by rfl⟩ : syracuseStep 704447 = 1056671) B1056671
theorem B1785959 : Blo 702318 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B704667 : Blo 702318 704667 := bstep (se 1 (by rfl) ⟨528500, by rfl⟩ : syracuseStep 704667 = 1057001) B1057001
theorem B704763 : Blo 702318 704763 := bstep (se 1 (by rfl) ⟨528572, by rfl⟩ : syracuseStep 704763 = 1057145) B1057145
theorem B2375945 : Blo 702318 2375945 := bstep (se 2 (by rfl) ⟨890979, by rfl⟩ : syracuseStep 2375945 = 1781959) B1781959
theorem B2146655 : Blo 702318 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B32489981 : Blo 702318 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B705023 : Blo 702318 705023 := bstep (se 1 (by rfl) ⟨528767, by rfl⟩ : syracuseStep 705023 = 1057535) B1057535
theorem B705439 : Blo 702318 705439 := bstep (se 1 (by rfl) ⟨529079, by rfl⟩ : syracuseStep 705439 = 1058159) B1058159
theorem B706279 : Blo 702318 706279 := bstep (se 1 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 706279 = 1059419) B1059419
theorem B24332015 : Blo 702318 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B706303 : Blo 702318 706303 := bstep (se 1 (by rfl) ⟨529727, by rfl⟩ : syracuseStep 706303 = 1059455) B1059455
theorem B2672635 : Blo 702318 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B5721295 : Blo 702318 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B6081767 : Blo 702318 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B15257483 : Blo 702318 15257483 := bstep (se 1 (by rfl) ⟨11443112, by rfl⟩ : syracuseStep 15257483 = 22886225) B22886225
theorem B1265633 : Blo 702318 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B1265915 : Blo 702318 1265915 := bstep (se 1 (by rfl) ⟨949436, by rfl⟩ : syracuseStep 1265915 = 1898873) B1898873
theorem B3003419 : Blo 702318 3003419 := bstep (se 1 (by rfl) ⟨2252564, by rfl⟩ : syracuseStep 3003419 = 4505129) B4505129
theorem B3005075 : Blo 702318 3005075 := bstep (se 1 (by rfl) ⟨2253806, by rfl⟩ : syracuseStep 3005075 = 4507613) B4507613
theorem B1334063 : Blo 702318 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B3005417 : Blo 702318 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B2678255 : Blo 702318 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B9036137 : Blo 702318 9036137 := bstep (se 2 (by rfl) ⟨3388551, by rfl⟩ : syracuseStep 9036137 = 6777103) B6777103
theorem B9004769 : Blo 702318 9004769 := bstep (se 2 (by rfl) ⟨3376788, by rfl⟩ : syracuseStep 9004769 = 6753577) B6753577
theorem B1338095 : Blo 702318 1338095 := bstep (se 1 (by rfl) ⟨1003571, by rfl⟩ : syracuseStep 1338095 = 2007143) B2007143
theorem B8252383 : Blo 702318 8252383 := bstep (se 1 (by rfl) ⟨6189287, by rfl⟩ : syracuseStep 8252383 = 12378575) B12378575
theorem B10153147 : Blo 702318 10153147 := bstep (se 1 (by rfl) ⟨7614860, by rfl⟩ : syracuseStep 10153147 = 15229721) B15229721
theorem B5336279 : Blo 702318 5336279 := bstep (se 1 (by rfl) ⟨4002209, by rfl⟩ : syracuseStep 5336279 = 8004419) B8004419
theorem B4517147 : Blo 702318 4517147 := bstep (se 1 (by rfl) ⟨3387860, by rfl⟩ : syracuseStep 4517147 = 6775721) B6775721
theorem B3567725 : Blo 702318 3567725 := bstep (se 3 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 3567725 = 1337897) B1337897
theorem B4518737 : Blo 702318 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B18838781 : Blo 702318 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B1504759 : Blo 702318 1504759 := bstep (se 1 (by rfl) ⟨1128569, by rfl⟩ : syracuseStep 1504759 = 2257139) B2257139
theorem B6092777 : Blo 702318 6092777 := bstep (se 2 (by rfl) ⟨2284791, by rfl⟩ : syracuseStep 6092777 = 4569583) B4569583
theorem B7632893 : Blo 702318 7632893 := bstep (se 3 (by rfl) ⟨1431167, by rfl⟩ : syracuseStep 7632893 = 2862335) B2862335
theorem B3472159 : Blo 702318 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B5078447 : Blo 702318 5078447 := bstep (se 1 (by rfl) ⟨3808835, by rfl⟩ : syracuseStep 5078447 = 7617671) B7617671
theorem B3047327 : Blo 702318 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B21659987 : Blo 702318 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B10815655 : Blo 702318 10815655 := bstep (se 1 (by rfl) ⟨8111741, by rfl⟩ : syracuseStep 10815655 = 16223483) B16223483
theorem B5343569 : Blo 702318 5343569 := bstep (se 2 (by rfl) ⟨2003838, by rfl⟩ : syracuseStep 5343569 = 4007677) B4007677
theorem B2002279 : Blo 702318 2002279 := bstep (se 1 (by rfl) ⟨1501709, by rfl⟩ : syracuseStep 2002279 = 3003419) B3003419
theorem B2035199 : Blo 702318 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B6754427 : Blo 702318 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B13537529 : Blo 702318 13537529 := bstep (se 2 (by rfl) ⟨5076573, by rfl⟩ : syracuseStep 13537529 = 10153147) B10153147
theorem B2003383 : Blo 702318 2003383 := bstep (se 1 (by rfl) ⟨1502537, by rfl⟩ : syracuseStep 2003383 = 3005075) B3005075
theorem B889375 : Blo 702318 889375 := bstep (se 1 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 889375 = 1334063) B1334063
theorem B64885373 : Blo 702318 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B2003611 : Blo 702318 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B1053767 : Blo 702318 1053767 := bstep (se 1 (by rfl) ⟨790325, by rfl⟩ : syracuseStep 1053767 = 1580651) B1580651
theorem B1054235 : Blo 702318 1054235 := bstep (se 1 (by rfl) ⟨790676, by rfl⟩ : syracuseStep 1054235 = 1581353) B1581353
theorem B1054463 : Blo 702318 1054463 := bstep (se 1 (by rfl) ⟨790847, by rfl⟩ : syracuseStep 1054463 = 1581695) B1581695
theorem B6003179 : Blo 702318 6003179 := bstep (se 1 (by rfl) ⟨4502384, by rfl⟩ : syracuseStep 6003179 = 9004769) B9004769
theorem B6167495 : Blo 702318 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1055903 : Blo 702318 1055903 := bstep (se 1 (by rfl) ⟨791927, by rfl⟩ : syracuseStep 1055903 = 1583855) B1583855
theorem B892063 : Blo 702318 892063 := bstep (se 1 (by rfl) ⟨669047, by rfl⟩ : syracuseStep 892063 = 1338095) B1338095
theorem B2006345 : Blo 702318 2006345 := bstep (se 2 (by rfl) ⟨752379, by rfl⟩ : syracuseStep 2006345 = 1504759) B1504759
theorem B794011 : Blo 702318 794011 := bstep (se 1 (by rfl) ⟨595508, by rfl⟩ : syracuseStep 794011 = 1191017) B1191017
theorem B1056383 : Blo 702318 1056383 := bstep (se 1 (by rfl) ⟨792287, by rfl⟩ : syracuseStep 1056383 = 1584575) B1584575
theorem B1056539 : Blo 702318 1056539 := bstep (se 1 (by rfl) ⟨792404, by rfl⟩ : syracuseStep 1056539 = 1584809) B1584809
theorem B1057019 : Blo 702318 1057019 := bstep (se 1 (by rfl) ⟨792764, by rfl⟩ : syracuseStep 1057019 = 1585529) B1585529
theorem B12559187 : Blo 702318 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B1057823 : Blo 702318 1057823 := bstep (se 1 (by rfl) ⟨793367, by rfl⟩ : syracuseStep 1057823 = 1586735) B1586735
theorem B4629545 : Blo 702318 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B5088595 : Blo 702318 5088595 := bstep (se 1 (by rfl) ⟨3816446, by rfl⟩ : syracuseStep 5088595 = 7632893) B7632893
theorem B1058207 : Blo 702318 1058207 := bstep (se 1 (by rfl) ⟨793655, by rfl⟩ : syracuseStep 1058207 = 1587311) B1587311
theorem B1583207 : Blo 702318 1583207 := bstep (se 1 (by rfl) ⟨1187405, by rfl⟩ : syracuseStep 1583207 = 2374811) B2374811
theorem B3385631 : Blo 702318 3385631 := bstep (se 1 (by rfl) ⟨2539223, by rfl⟩ : syracuseStep 3385631 = 5078447) B5078447
theorem B1190639 : Blo 702318 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B1583963 : Blo 702318 1583963 := bstep (se 1 (by rfl) ⟨1187972, by rfl⟩ : syracuseStep 1583963 = 2375945) B2375945
theorem B10171655 : Blo 702318 10171655 := bstep (se 1 (by rfl) ⟨7628741, by rfl⟩ : syracuseStep 10171655 = 15257483) B15257483
theorem B4110497 : Blo 702318 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B702671 : Blo 702318 702671 := bstep (se 1 (by rfl) ⟨527003, by rfl⟩ : syracuseStep 702671 = 1054007) B1054007
theorem B703335 : Blo 702318 703335 := bstep (se 1 (by rfl) ⟨527501, by rfl⟩ : syracuseStep 703335 = 1055003) B1055003
theorem B8443182743 : Blo 702318 8443182743 := bstep (se 1 (by rfl) ⟨6332387057, by rfl⟩ : syracuseStep 8443182743 = 12664774115) B12664774115
theorem B704159 : Blo 702318 704159 := bstep (se 1 (by rfl) ⟨528119, by rfl⟩ : syracuseStep 704159 = 1056239) B1056239
theorem B1785503 : Blo 702318 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B705607 : Blo 702318 705607 := bstep (se 1 (by rfl) ⟨529205, by rfl⟩ : syracuseStep 705607 = 1058411) B1058411
theorem B705791 : Blo 702318 705791 := bstep (se 1 (by rfl) ⟨529343, by rfl⟩ : syracuseStep 705791 = 1058687) B1058687
theorem B705819 : Blo 702318 705819 := bstep (se 1 (by rfl) ⟨529364, by rfl⟩ : syracuseStep 705819 = 1058729) B1058729
theorem B706151 : Blo 702318 706151 := bstep (se 1 (by rfl) ⟨529613, by rfl⟩ : syracuseStep 706151 = 1059227) B1059227
theorem B3557519 : Blo 702318 3557519 := bstep (se 1 (by rfl) ⟨2668139, by rfl⟩ : syracuseStep 3557519 = 5336279) B5336279
theorem B2378483 : Blo 702318 2378483 := bstep (se 1 (by rfl) ⟨1783862, by rfl⟩ : syracuseStep 2378483 = 3567725) B3567725
theorem B3722935 : Blo 702318 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B5493691 : Blo 702318 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B1431103 : Blo 702318 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B8543515 : Blo 702318 8543515 := bstep (se 1 (by rfl) ⟨6407636, by rfl⟩ : syracuseStep 8543515 = 12815273) B12815273
theorem B4054511 : Blo 702318 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B2383613 : Blo 702318 2383613 := bstep (se 3 (by rfl) ⟨446927, by rfl⟩ : syracuseStep 2383613 = 893855) B893855
theorem B843755 : Blo 702318 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B3563513 : Blo 702318 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B843943 : Blo 702318 843943 := bstep (se 1 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 843943 = 1265915) B1265915
theorem B3563999 : Blo 702318 3563999 := bstep (se 1 (by rfl) ⟨2672999, by rfl⟩ : syracuseStep 3563999 = 5345999) B5345999
theorem B9003743 : Blo 702318 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B21947537 : Blo 702318 21947537 := bstep (se 2 (by rfl) ⟨8230326, by rfl⟩ : syracuseStep 21947537 = 16460653) B16460653
theorem B11003177 : Blo 702318 11003177 := bstep (se 2 (by rfl) ⟨4126191, by rfl⟩ : syracuseStep 11003177 = 8252383) B8252383
theorem B7628393 : Blo 702318 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B812911 : Blo 702318 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B16247405 : Blo 702318 16247405 := bstep (se 3 (by rfl) ⟨3046388, by rfl⟩ : syracuseStep 16247405 = 6092777) B6092777
theorem B6024091 : Blo 702318 6024091 := bstep (se 1 (by rfl) ⟨4518068, by rfl⟩ : syracuseStep 6024091 = 9036137) B9036137
theorem B3011431 : Blo 702318 3011431 := bstep (se 1 (by rfl) ⟨2258573, by rfl⟩ : syracuseStep 3011431 = 4517147) B4517147
theorem B3012491 : Blo 702318 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B2030617 : Blo 702318 2030617 := bstep (se 2 (by rfl) ⟨761481, by rfl⟩ : syracuseStep 2030617 = 1522963) B1522963
theorem B2031551 : Blo 702318 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B6784793 : Blo 702318 6784793 := bstep (se 2 (by rfl) ⟨2544297, by rfl⟩ : syracuseStep 6784793 = 5088595) B5088595
theorem B1083881 : Blo 702318 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B14420873 : Blo 702318 14420873 := bstep (se 2 (by rfl) ⟨5407827, by rfl⟩ : syracuseStep 14420873 = 10815655) B10815655
theorem B43256915 : Blo 702318 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B8032121 : Blo 702318 8032121 := bstep (se 2 (by rfl) ⟨3012045, by rfl⟩ : syracuseStep 8032121 = 6024091) B6024091
theorem B4002119 : Blo 702318 4002119 := bstep (se 1 (by rfl) ⟨3001589, by rfl⟩ : syracuseStep 4002119 = 6003179) B6003179
theorem B6002495 : Blo 702318 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B3086363 : Blo 702318 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B1185833 : Blo 702318 1185833 := bstep (se 2 (by rfl) ⟨444687, by rfl⟩ : syracuseStep 1185833 = 889375) B889375
theorem B5085595 : Blo 702318 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B1055471 : Blo 702318 1055471 := bstep (se 1 (by rfl) ⟨791603, by rfl⟩ : syracuseStep 1055471 = 1583207) B1583207
theorem B793759 : Blo 702318 793759 := bstep (se 1 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 793759 = 1190639) B1190639
theorem B1055975 : Blo 702318 1055975 := bstep (se 1 (by rfl) ⟨791981, by rfl⟩ : syracuseStep 1055975 = 1583963) B1583963
theorem B1908137 : Blo 702318 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B2008327 : Blo 702318 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B1189417 : Blo 702318 1189417 := bstep (se 2 (by rfl) ⟨446031, by rfl⟩ : syracuseStep 1189417 = 892063) B892063
theorem B1058681 : Blo 702318 1058681 := bstep (se 2 (by rfl) ⟨397005, by rfl⟩ : syracuseStep 1058681 = 794011) B794011
theorem B1190335 : Blo 702318 1190335 := bstep (se 1 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 1190335 = 1785503) B1785503
theorem B1354367 : Blo 702318 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B1125257 : Blo 702318 1125257 := bstep (se 2 (by rfl) ⟨421971, by rfl⟩ : syracuseStep 1125257 = 843943) B843943
theorem B2371679 : Blo 702318 2371679 := bstep (se 1 (by rfl) ⟨1778759, by rfl⟩ : syracuseStep 2371679 = 3557519) B3557519
theorem B1585655 : Blo 702318 1585655 := bstep (se 1 (by rfl) ⟨1189241, by rfl⟩ : syracuseStep 1585655 = 2378483) B2378483
theorem B1356799 : Blo 702318 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B4502951 : Blo 702318 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B9025019 : Blo 702318 9025019 := bstep (se 1 (by rfl) ⟨6768764, by rfl⟩ : syracuseStep 9025019 = 13537529) B13537529
theorem B702511 : Blo 702318 702511 := bstep (se 1 (by rfl) ⟨526883, by rfl⟩ : syracuseStep 702511 = 1053767) B1053767
theorem B702823 : Blo 702318 702823 := bstep (se 1 (by rfl) ⟨527117, by rfl⟩ : syracuseStep 702823 = 1054235) B1054235
theorem B702975 : Blo 702318 702975 := bstep (se 1 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 702975 = 1054463) B1054463
theorem B2669705 : Blo 702318 2669705 := bstep (se 2 (by rfl) ⟨1001139, by rfl⟩ : syracuseStep 2669705 = 2002279) B2002279
theorem B4111663 : Blo 702318 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B703935 : Blo 702318 703935 := bstep (se 1 (by rfl) ⟨527951, by rfl⟩ : syracuseStep 703935 = 1055903) B1055903
theorem B4963913 : Blo 702318 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B2703007 : Blo 702318 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B704255 : Blo 702318 704255 := bstep (se 1 (by rfl) ⟨528191, by rfl⟩ : syracuseStep 704255 = 1056383) B1056383
theorem B1589075 : Blo 702318 1589075 := bstep (se 1 (by rfl) ⟨1191806, by rfl⟩ : syracuseStep 1589075 = 2383613) B2383613
theorem B704359 : Blo 702318 704359 := bstep (se 1 (by rfl) ⟨528269, by rfl⟩ : syracuseStep 704359 = 1056539) B1056539
theorem B2375675 : Blo 702318 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B704679 : Blo 702318 704679 := bstep (se 1 (by rfl) ⟨528509, by rfl⟩ : syracuseStep 704679 = 1057019) B1057019
theorem B2375999 : Blo 702318 2375999 := bstep (se 1 (by rfl) ⟨1781999, by rfl⟩ : syracuseStep 2375999 = 3563999) B3563999
theorem B8372791 : Blo 702318 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B2671177 : Blo 702318 2671177 := bstep (se 2 (by rfl) ⟨1001691, by rfl⟩ : syracuseStep 2671177 = 2003383) B2003383
theorem B705215 : Blo 702318 705215 := bstep (se 1 (by rfl) ⟨528911, by rfl⟩ : syracuseStep 705215 = 1057823) B1057823
theorem B14631691 : Blo 702318 14631691 := bstep (se 1 (by rfl) ⟨10973768, by rfl⟩ : syracuseStep 14631691 = 21947537) B21947537
theorem B2671481 : Blo 702318 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B705471 : Blo 702318 705471 := bstep (se 1 (by rfl) ⟨529103, by rfl⟩ : syracuseStep 705471 = 1058207) B1058207
theorem B4015241 : Blo 702318 4015241 := bstep (se 2 (by rfl) ⟨1505715, by rfl⟩ : syracuseStep 4015241 = 3011431) B3011431
theorem B7324921 : Blo 702318 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B10831603 : Blo 702318 10831603 := bstep (se 1 (by rfl) ⟨8123702, by rfl⟩ : syracuseStep 10831603 = 16247405) B16247405
theorem B2707489 : Blo 702318 2707489 := bstep (se 2 (by rfl) ⟨1015308, by rfl⟩ : syracuseStep 2707489 = 2030617) B2030617
theorem B2740331 : Blo 702318 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B11391353 : Blo 702318 11391353 := bstep (se 2 (by rfl) ⟨4271757, by rfl⟩ : syracuseStep 11391353 = 8543515) B8543515
theorem B2250013 : Blo 702318 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B14439991 : Blo 702318 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B3562379 : Blo 702318 3562379 := bstep (se 1 (by rfl) ⟨2671784, by rfl⟩ : syracuseStep 3562379 = 5343569) B5343569
theorem B1337563 : Blo 702318 1337563 := bstep (se 1 (by rfl) ⟨1003172, by rfl⟩ : syracuseStep 1337563 = 2006345) B2006345
theorem B7335451 : Blo 702318 7335451 := bstep (se 1 (by rfl) ⟨5501588, by rfl⟩ : syracuseStep 7335451 = 11003177) B11003177
theorem B2257087 : Blo 702318 2257087 := bstep (se 1 (by rfl) ⟨1692815, by rfl⟩ : syracuseStep 2257087 = 3385631) B3385631
theorem B6781103 : Blo 702318 6781103 := bstep (se 1 (by rfl) ⟨5085827, by rfl⟩ : syracuseStep 6781103 = 10171655) B10171655
theorem B5628788495 : Blo 702318 5628788495 := bstep (se 1 (by rfl) ⟨4221591371, by rfl⟩ : syracuseStep 5628788495 = 8443182743) B8443182743
theorem B4523195 : Blo 702318 4523195 := bstep (se 1 (by rfl) ⟨3392396, by rfl⟩ : syracuseStep 4523195 = 6784793) B6784793
theorem B28837943 : Blo 702318 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B4001663 : Blo 702318 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B790555 : Blo 702318 790555 := bstep (se 1 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 790555 = 1185833) B1185833
theorem B2890349 : Blo 702318 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B39066245 : Blo 702318 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B1809065 : Blo 702318 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B1581119 : Blo 702318 1581119 := bstep (se 1 (by rfl) ⟨1185839, by rfl⟩ : syracuseStep 1581119 = 2371679) B2371679
theorem B1057103 : Blo 702318 1057103 := bstep (se 1 (by rfl) ⟨792827, by rfl⟩ : syracuseStep 1057103 = 1585655) B1585655
theorem B5088365 : Blo 702318 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B1058345 : Blo 702318 1058345 := bstep (se 2 (by rfl) ⟨396879, by rfl⟩ : syracuseStep 1058345 = 793759) B793759
theorem B5482217 : Blo 702318 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B1779803 : Blo 702318 1779803 := bstep (se 1 (by rfl) ⟨1334852, by rfl⟩ : syracuseStep 1779803 = 2669705) B2669705
theorem B1059383 : Blo 702318 1059383 := bstep (se 1 (by rfl) ⟨794537, by rfl⟩ : syracuseStep 1059383 = 1589075) B1589075
theorem B1583783 : Blo 702318 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B1583999 : Blo 702318 1583999 := bstep (se 1 (by rfl) ⟨1187999, by rfl⟩ : syracuseStep 1583999 = 2375999) B2375999
theorem B1780987 : Blo 702318 1780987 := bstep (se 1 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 1780987 = 2671481) B2671481
theorem B19508921 : Blo 702318 19508921 := bstep (se 2 (by rfl) ⟨7315845, by rfl⟩ : syracuseStep 19508921 = 14631691) B14631691
theorem B1585889 : Blo 702318 1585889 := bstep (se 2 (by rfl) ⟨594708, by rfl⟩ : syracuseStep 1585889 = 1189417) B1189417
theorem B5354747 : Blo 702318 5354747 := bstep (se 1 (by rfl) ⟨4016060, by rfl⟩ : syracuseStep 5354747 = 8032121) B8032121
theorem B2668079 : Blo 702318 2668079 := bstep (se 1 (by rfl) ⟨2001059, by rfl⟩ : syracuseStep 2668079 = 4002119) B4002119
theorem B1783417 : Blo 702318 1783417 := bstep (se 2 (by rfl) ⟨668781, by rfl⟩ : syracuseStep 1783417 = 1337563) B1337563
theorem B1587113 : Blo 702318 1587113 := bstep (se 2 (by rfl) ⟨595167, by rfl⟩ : syracuseStep 1587113 = 1190335) B1190335
theorem B703647 : Blo 702318 703647 := bstep (se 1 (by rfl) ⟨527735, by rfl⟩ : syracuseStep 703647 = 1055471) B1055471
theorem B2374919 : Blo 702318 2374919 := bstep (se 1 (by rfl) ⟨1781189, by rfl⟩ : syracuseStep 2374919 = 3562379) B3562379
theorem B9780601 : Blo 702318 9780601 := bstep (se 2 (by rfl) ⟨3667725, by rfl⟩ : syracuseStep 9780601 = 7335451) B7335451
theorem B703983 : Blo 702318 703983 := bstep (se 1 (by rfl) ⟨527987, by rfl⟩ : syracuseStep 703983 = 1055975) B1055975
theorem B705787 : Blo 702318 705787 := bstep (se 1 (by rfl) ⟨529340, by rfl⟩ : syracuseStep 705787 = 1058681) B1058681
theorem B3000017 : Blo 702318 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B902911 : Blo 702318 902911 := bstep (se 1 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 902911 = 1354367) B1354367
theorem B19253321 : Blo 702318 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B3000685 : Blo 702318 3000685 := bstep (se 3 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 3000685 = 1125257) B1125257
theorem B38455661 : Blo 702318 38455661 := bstep (se 3 (by rfl) ⟨7210436, by rfl⟩ : syracuseStep 38455661 = 14420873) B14420873
theorem B3001967 : Blo 702318 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B6016679 : Blo 702318 6016679 := bstep (se 1 (by rfl) ⟨4512509, by rfl⟩ : syracuseStep 6016679 = 9025019) B9025019
theorem B14439941 : Blo 702318 14439941 := bstep (se 4 (by rfl) ⟨1353744, by rfl⟩ : syracuseStep 14439941 = 2707489) B2707489
theorem B2676827 : Blo 702318 2676827 := bstep (se 1 (by rfl) ⟨2007620, by rfl⟩ : syracuseStep 2676827 = 4015241) B4015241
theorem B3561569 : Blo 702318 3561569 := bstep (se 2 (by rfl) ⟨1335588, by rfl⟩ : syracuseStep 3561569 = 2671177) B2671177
theorem B2677769 : Blo 702318 2677769 := bstep (se 2 (by rfl) ⟨1004163, by rfl⟩ : syracuseStep 2677769 = 2008327) B2008327
theorem B27123173 : Blo 702318 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B14442137 : Blo 702318 14442137 := bstep (se 2 (by rfl) ⟨5415801, by rfl⟩ : syracuseStep 14442137 = 10831603) B10831603
theorem B1826887 : Blo 702318 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B7594235 : Blo 702318 7594235 := bstep (se 1 (by rfl) ⟨5695676, by rfl⟩ : syracuseStep 7594235 = 11391353) B11391353
theorem B44654885 : Blo 702318 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B2057575 : Blo 702318 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B3009449 : Blo 702318 3009449 := bstep (se 2 (by rfl) ⟨1128543, by rfl⟩ : syracuseStep 3009449 = 2257087) B2257087
theorem B4520735 : Blo 702318 4520735 := bstep (se 1 (by rfl) ⟨3390551, by rfl⟩ : syracuseStep 4520735 = 6781103) B6781103
theorem B3604009 : Blo 702318 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B3309275 : Blo 702318 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B3752525663 : Blo 702318 3752525663 := bstep (se 1 (by rfl) ⟨2814394247, by rfl⟩ : syracuseStep 3752525663 = 5628788495) B5628788495
theorem B3015463 : Blo 702318 3015463 := bstep (se 1 (by rfl) ⟨2261597, by rfl⟩ : syracuseStep 3015463 = 4523195) B4523195
theorem B2001311 : Blo 702318 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B4000913 : Blo 702318 4000913 := bstep (se 2 (by rfl) ⟨1500342, by rfl⟩ : syracuseStep 4000913 = 3000685) B3000685
theorem B8000045 : Blo 702318 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B1054073 : Blo 702318 1054073 := bstep (se 2 (by rfl) ⟨395277, by rfl⟩ : syracuseStep 1054073 = 790555) B790555
theorem B1054079 : Blo 702318 1054079 := bstep (se 1 (by rfl) ⟨790559, by rfl⟩ : syracuseStep 1054079 = 1581119) B1581119
theorem B1186535 : Blo 702318 1186535 := bstep (se 1 (by rfl) ⟨889901, by rfl⟩ : syracuseStep 1186535 = 1779803) B1779803
theorem B4824173 : Blo 702318 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B1055855 : Blo 702318 1055855 := bstep (se 1 (by rfl) ⟨791891, by rfl⟩ : syracuseStep 1055855 = 1583783) B1583783
theorem B1055999 : Blo 702318 1055999 := bstep (se 1 (by rfl) ⟨791999, by rfl⟩ : syracuseStep 1055999 = 1583999) B1583999
theorem B2006299 : Blo 702318 2006299 := bstep (se 1 (by rfl) ⟨1504724, by rfl⟩ : syracuseStep 2006299 = 3009449) B3009449
theorem B1057259 : Blo 702318 1057259 := bstep (se 1 (by rfl) ⟨792944, by rfl⟩ : syracuseStep 1057259 = 1585889) B1585889
theorem B1778719 : Blo 702318 1778719 := bstep (se 1 (by rfl) ⟨1334039, by rfl⟩ : syracuseStep 1778719 = 2668079) B2668079
theorem B1058075 : Blo 702318 1058075 := bstep (se 1 (by rfl) ⟨793556, by rfl⟩ : syracuseStep 1058075 = 1587113) B1587113
theorem B8824733 : Blo 702318 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B1583279 : Blo 702318 1583279 := bstep (se 1 (by rfl) ⟨1187459, by rfl⟩ : syracuseStep 1583279 = 2374919) B2374919
theorem B2501683775 : Blo 702318 2501683775 := bstep (se 1 (by rfl) ⟨1876262831, by rfl⟩ : syracuseStep 2501683775 = 3752525663) B3752525663
theorem B2435849 : Blo 702318 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B25637107 : Blo 702318 25637107 := bstep (se 1 (by rfl) ⟨19227830, by rfl⟩ : syracuseStep 25637107 = 38455661) B38455661
theorem B4011119 : Blo 702318 4011119 := bstep (se 1 (by rfl) ⟨3008339, by rfl⟩ : syracuseStep 4011119 = 6016679) B6016679
theorem B2667775 : Blo 702318 2667775 := bstep (se 1 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 2667775 = 4001663) B4001663
theorem B1784551 : Blo 702318 1784551 := bstep (se 1 (by rfl) ⟨1338413, by rfl⟩ : syracuseStep 1784551 = 2676827) B2676827
theorem B2374379 : Blo 702318 2374379 := bstep (se 1 (by rfl) ⟨1780784, by rfl⟩ : syracuseStep 2374379 = 3561569) B3561569
theorem B2374649 : Blo 702318 2374649 := bstep (se 2 (by rfl) ⟨890493, by rfl⟩ : syracuseStep 2374649 = 1780987) B1780987
theorem B1785179 : Blo 702318 1785179 := bstep (se 1 (by rfl) ⟨1338884, by rfl⟩ : syracuseStep 1785179 = 2677769) B2677769
theorem B5062823 : Blo 702318 5062823 := bstep (se 1 (by rfl) ⟨3797117, by rfl⟩ : syracuseStep 5062823 = 7594235) B7594235
theorem B29769923 : Blo 702318 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B704735 : Blo 702318 704735 := bstep (se 1 (by rfl) ⟨528551, by rfl⟩ : syracuseStep 704735 = 1057103) B1057103
theorem B3392243 : Blo 702318 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B705563 : Blo 702318 705563 := bstep (se 1 (by rfl) ⟨529172, by rfl⟩ : syracuseStep 705563 = 1058345) B1058345
theorem B3654811 : Blo 702318 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B706255 : Blo 702318 706255 := bstep (se 1 (by rfl) ⟨529691, by rfl⟩ : syracuseStep 706255 = 1059383) B1059383
theorem B2377889 : Blo 702318 2377889 := bstep (se 2 (by rfl) ⟨891708, by rfl⟩ : syracuseStep 2377889 = 1783417) B1783417
theorem B4805345 : Blo 702318 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B19225295 : Blo 702318 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B12835547 : Blo 702318 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B2743433 : Blo 702318 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B1203881 : Blo 702318 1203881 := bstep (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) B902911
theorem B9626627 : Blo 702318 9626627 := bstep (se 1 (by rfl) ⟨7219970, by rfl⟩ : syracuseStep 9626627 = 14439941) B14439941
theorem B1926899 : Blo 702318 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B26044163 : Blo 702318 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B18082115 : Blo 702318 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B9628091 : Blo 702318 9628091 := bstep (se 1 (by rfl) ⟨7221068, by rfl⟩ : syracuseStep 9628091 = 14442137) B14442137
theorem B13005947 : Blo 702318 13005947 := bstep (se 1 (by rfl) ⟨9754460, by rfl⟩ : syracuseStep 13005947 = 19508921) B19508921
theorem B3569831 : Blo 702318 3569831 := bstep (se 1 (by rfl) ⟨2677373, by rfl⟩ : syracuseStep 3569831 = 5354747) B5354747
theorem B13040801 : Blo 702318 13040801 := bstep (se 2 (by rfl) ⟨4890300, by rfl⟩ : syracuseStep 13040801 = 9780601) B9780601
theorem B3013823 : Blo 702318 3013823 := bstep (se 1 (by rfl) ⟨2260367, by rfl⟩ : syracuseStep 3013823 = 4520735) B4520735
theorem B3375215 : Blo 702318 3375215 := bstep (se 1 (by rfl) ⟨2531411, by rfl⟩ : syracuseStep 3375215 = 5062823) B5062823
theorem B2261495 : Blo 702318 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B12816863 : Blo 702318 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B8557031 : Blo 702318 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B791023 : Blo 702318 791023 := bstep (se 1 (by rfl) ⟨593267, by rfl⟩ : syracuseStep 791023 = 1186535) B1186535
theorem B3216115 : Blo 702318 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B34182809 : Blo 702318 34182809 := bstep (se 2 (by rfl) ⟨12818553, by rfl⟩ : syracuseStep 34182809 = 25637107) B25637107
theorem B1284599 : Blo 702318 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B1055519 : Blo 702318 1055519 := bstep (se 1 (by rfl) ⟨791639, by rfl⟩ : syracuseStep 1055519 = 1583279) B1583279
theorem B1582919 : Blo 702318 1582919 := bstep (se 1 (by rfl) ⟨1187189, by rfl⟩ : syracuseStep 1582919 = 2374379) B2374379
theorem B1583099 : Blo 702318 1583099 := bstep (se 1 (by rfl) ⟨1187324, by rfl⟩ : syracuseStep 1583099 = 2374649) B2374649
theorem B8693867 : Blo 702318 8693867 := bstep (se 1 (by rfl) ⟨6520400, by rfl⟩ : syracuseStep 8693867 = 13040801) B13040801
theorem B2009215 : Blo 702318 2009215 := bstep (se 1 (by rfl) ⟨1506911, by rfl⟩ : syracuseStep 2009215 = 3013823) B3013823
theorem B1190119 : Blo 702318 1190119 := bstep (se 1 (by rfl) ⟨892589, by rfl⟩ : syracuseStep 1190119 = 1785179) B1785179
theorem B2371625 : Blo 702318 2371625 := bstep (se 2 (by rfl) ⟨889359, by rfl⟩ : syracuseStep 2371625 = 1778719) B1778719
theorem B1585259 : Blo 702318 1585259 := bstep (se 1 (by rfl) ⟨1188944, by rfl⟩ : syracuseStep 1585259 = 2377889) B2377889
theorem B2667275 : Blo 702318 2667275 := bstep (se 1 (by rfl) ⟨2000456, by rfl⟩ : syracuseStep 2667275 = 4000913) B4000913
theorem B34682525 : Blo 702318 34682525 := bstep (se 3 (by rfl) ⟨6502973, by rfl⟩ : syracuseStep 34682525 = 13005947) B13005947
theorem B702715 : Blo 702318 702715 := bstep (se 1 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 702715 = 1054073) B1054073
theorem B702719 : Blo 702318 702719 := bstep (se 1 (by rfl) ⟨527039, by rfl⟩ : syracuseStep 702719 = 1054079) B1054079
theorem B703903 : Blo 702318 703903 := bstep (se 1 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 703903 = 1055855) B1055855
theorem B703999 : Blo 702318 703999 := bstep (se 1 (by rfl) ⟨527999, by rfl⟩ : syracuseStep 703999 = 1055999) B1055999
theorem B704839 : Blo 702318 704839 := bstep (se 1 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 704839 = 1057259) B1057259
theorem B705383 : Blo 702318 705383 := bstep (se 1 (by rfl) ⟨529037, by rfl⟩ : syracuseStep 705383 = 1058075) B1058075
theorem B5883155 : Blo 702318 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B3557033 : Blo 702318 3557033 := bstep (se 2 (by rfl) ⟨1333887, by rfl⟩ : syracuseStep 3557033 = 2667775) B2667775
theorem B1623899 : Blo 702318 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B2674079 : Blo 702318 2674079 := bstep (se 1 (by rfl) ⟨2005559, by rfl⟩ : syracuseStep 2674079 = 4011119) B4011119
theorem B2379401 : Blo 702318 2379401 := bstep (se 2 (by rfl) ⟨892275, by rfl⟩ : syracuseStep 2379401 = 1784551) B1784551
theorem B2379887 : Blo 702318 2379887 := bstep (se 1 (by rfl) ⟨1784915, by rfl⟩ : syracuseStep 2379887 = 3569831) B3569831
theorem B2675065 : Blo 702318 2675065 := bstep (se 2 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 2675065 = 2006299) B2006299
theorem B19846615 : Blo 702318 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B4020617 : Blo 702318 4020617 := bstep (se 2 (by rfl) ⟨1507731, by rfl⟩ : syracuseStep 4020617 = 3015463) B3015463
theorem B4873081 : Blo 702318 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B1334207 : Blo 702318 1334207 := bstep (se 1 (by rfl) ⟨1000655, by rfl⟩ : syracuseStep 1334207 = 2001311) B2001311
theorem B5333363 : Blo 702318 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B3203563 : Blo 702318 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B1828955 : Blo 702318 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B6417751 : Blo 702318 6417751 := bstep (se 1 (by rfl) ⟨4813313, by rfl⟩ : syracuseStep 6417751 = 9626627) B9626627
theorem B17362775 : Blo 702318 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B12054743 : Blo 702318 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B6418727 : Blo 702318 6418727 := bstep (se 1 (by rfl) ⟨4814045, by rfl⟩ : syracuseStep 6418727 = 9628091) B9628091
theorem B1667789183 : Blo 702318 1667789183 := bstep (se 1 (by rfl) ⟨1250841887, by rfl⟩ : syracuseStep 1667789183 = 2501683775) B2501683775
theorem B3210349 : Blo 702318 3210349 := bstep (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) B1203881
theorem B1507663 : Blo 702318 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B5704687 : Blo 702318 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B856399 : Blo 702318 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B8557001 : Blo 702318 8557001 := bstep (se 2 (by rfl) ⟨3208875, by rfl⟩ : syracuseStep 8557001 = 6417751) B6417751
theorem B889471 : Blo 702318 889471 := bstep (se 1 (by rfl) ⟨667103, by rfl⟩ : syracuseStep 889471 = 1334207) B1334207
theorem B4330397 : Blo 702318 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B1054697 : Blo 702318 1054697 := bstep (se 2 (by rfl) ⟨395511, by rfl⟩ : syracuseStep 1054697 = 791023) B791023
theorem B1055279 : Blo 702318 1055279 := bstep (se 1 (by rfl) ⟨791459, by rfl⟩ : syracuseStep 1055279 = 1582919) B1582919
theorem B1055399 : Blo 702318 1055399 := bstep (se 1 (by rfl) ⟨791549, by rfl⟩ : syracuseStep 1055399 = 1583099) B1583099
theorem B1219303 : Blo 702318 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B11575183 : Blo 702318 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B1581083 : Blo 702318 1581083 := bstep (se 1 (by rfl) ⟨1185812, by rfl⟩ : syracuseStep 1581083 = 2371625) B2371625
theorem B1056839 : Blo 702318 1056839 := bstep (se 1 (by rfl) ⟨792629, by rfl⟩ : syracuseStep 1056839 = 1585259) B1585259
theorem B8036495 : Blo 702318 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B1111859455 : Blo 702318 1111859455 := bstep (se 1 (by rfl) ⟨833894591, by rfl⟩ : syracuseStep 1111859455 = 1667789183) B1667789183
theorem B1778183 : Blo 702318 1778183 := bstep (se 1 (by rfl) ⟨1333637, by rfl⟩ : syracuseStep 1778183 = 2667275) B2667275
theorem B6497441 : Blo 702318 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B4271417 : Blo 702318 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B2371355 : Blo 702318 2371355 := bstep (se 1 (by rfl) ⟨1778516, by rfl⟩ : syracuseStep 2371355 = 3557033) B3557033
theorem B1782719 : Blo 702318 1782719 := bstep (se 1 (by rfl) ⟨1337039, by rfl⟩ : syracuseStep 1782719 = 2674079) B2674079
theorem B1586267 : Blo 702318 1586267 := bstep (se 1 (by rfl) ⟨1189700, by rfl⟩ : syracuseStep 1586267 = 2379401) B2379401
theorem B1586591 : Blo 702318 1586591 := bstep (se 1 (by rfl) ⟨1189943, by rfl⟩ : syracuseStep 1586591 = 2379887) B2379887
theorem B1586825 : Blo 702318 1586825 := bstep (se 2 (by rfl) ⟨595059, by rfl⟩ : syracuseStep 1586825 = 1190119) B1190119
theorem B22788539 : Blo 702318 22788539 := bstep (se 1 (by rfl) ⟨17091404, by rfl⟩ : syracuseStep 22788539 = 34182809) B34182809
theorem B703679 : Blo 702318 703679 := bstep (se 1 (by rfl) ⟨527759, by rfl⟩ : syracuseStep 703679 = 1055519) B1055519
theorem B3555575 : Blo 702318 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B26462153 : Blo 702318 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B4279151 : Blo 702318 4279151 := bstep (se 1 (by rfl) ⟨3209363, by rfl⟩ : syracuseStep 4279151 = 6418727) B6418727
theorem B23121683 : Blo 702318 23121683 := bstep (se 1 (by rfl) ⟨17341262, by rfl⟩ : syracuseStep 23121683 = 34682525) B34682525
theorem B4280465 : Blo 702318 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B2250143 : Blo 702318 2250143 := bstep (se 1 (by rfl) ⟨1687607, by rfl⟩ : syracuseStep 2250143 = 3375215) B3375215
theorem B3922103 : Blo 702318 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B2678953 : Blo 702318 2678953 := bstep (se 2 (by rfl) ⟨1004607, by rfl⟩ : syracuseStep 2678953 = 2009215) B2009215
theorem B8544575 : Blo 702318 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B2680411 : Blo 702318 2680411 := bstep (se 1 (by rfl) ⟨2010308, by rfl⟩ : syracuseStep 2680411 = 4020617) B4020617
theorem B3566753 : Blo 702318 3566753 := bstep (se 2 (by rfl) ⟨1337532, by rfl⟩ : syracuseStep 3566753 = 2675065) B2675065
theorem B4288153 : Blo 702318 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B5795911 : Blo 702318 5795911 := bstep (se 1 (by rfl) ⟨4346933, by rfl⟩ : syracuseStep 5795911 = 8693867) B8693867
theorem B3571937 : Blo 702318 3571937 := bstep (se 2 (by rfl) ⟨1339476, by rfl⟩ : syracuseStep 3571937 = 2678953) B2678953
theorem B2852767 : Blo 702318 2852767 := bstep (se 1 (by rfl) ⟨2139575, by rfl⟩ : syracuseStep 2852767 = 4279151) B4279151
theorem B3573881 : Blo 702318 3573881 := bstep (se 2 (by rfl) ⟨1340205, by rfl⟩ : syracuseStep 3573881 = 2680411) B2680411
theorem B2853643 : Blo 702318 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B5704667 : Blo 702318 5704667 := bstep (se 1 (by rfl) ⟨4278500, by rfl⟩ : syracuseStep 5704667 = 8557001) B8557001
theorem B2886931 : Blo 702318 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B1054055 : Blo 702318 1054055 := bstep (se 1 (by rfl) ⟨790541, by rfl⟩ : syracuseStep 1054055 = 1581083) B1581083
theorem B1185455 : Blo 702318 1185455 := bstep (se 1 (by rfl) ⟨889091, by rfl⟩ : syracuseStep 1185455 = 1778183) B1778183
theorem B4331627 : Blo 702318 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B1185961 : Blo 702318 1185961 := bstep (se 2 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 1185961 = 889471) B889471
theorem B1580903 : Blo 702318 1580903 := bstep (se 1 (by rfl) ⟨1185677, by rfl⟩ : syracuseStep 1580903 = 2371355) B2371355
theorem B1188479 : Blo 702318 1188479 := bstep (se 1 (by rfl) ⟨891359, by rfl⟩ : syracuseStep 1188479 = 1782719) B1782719
theorem B1057511 : Blo 702318 1057511 := bstep (se 1 (by rfl) ⟨793133, by rfl⟩ : syracuseStep 1057511 = 1586267) B1586267
theorem B1057727 : Blo 702318 1057727 := bstep (se 1 (by rfl) ⟨793295, by rfl⟩ : syracuseStep 1057727 = 1586591) B1586591
theorem B1057883 : Blo 702318 1057883 := bstep (se 1 (by rfl) ⟨793412, by rfl⟩ : syracuseStep 1057883 = 1586825) B1586825
theorem B2370383 : Blo 702318 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B22785533 : Blo 702318 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B8040869 : Blo 702318 8040869 := bstep (se 4 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 8040869 = 1507663) B1507663
theorem B15414455 : Blo 702318 15414455 := bstep (se 1 (by rfl) ⟨11560841, by rfl⟩ : syracuseStep 15414455 = 23121683) B23121683
theorem B703131 : Blo 702318 703131 := bstep (se 1 (by rfl) ⟨527348, by rfl⟩ : syracuseStep 703131 = 1054697) B1054697
theorem B703519 : Blo 702318 703519 := bstep (se 1 (by rfl) ⟨527639, by rfl⟩ : syracuseStep 703519 = 1055279) B1055279
theorem B703599 : Blo 702318 703599 := bstep (se 1 (by rfl) ⟨527699, by rfl⟩ : syracuseStep 703599 = 1055399) B1055399
theorem B5717537 : Blo 702318 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B70565741 : Blo 702318 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B30424997 : Blo 702318 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B704559 : Blo 702318 704559 := bstep (se 1 (by rfl) ⟨528419, by rfl⟩ : syracuseStep 704559 = 1056839) B1056839
theorem B5357663 : Blo 702318 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B2377835 : Blo 702318 2377835 := bstep (se 1 (by rfl) ⟨1783376, by rfl⟩ : syracuseStep 2377835 = 3566753) B3566753
theorem B1625737 : Blo 702318 1625737 := bstep (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) B1219303
theorem B15192359 : Blo 702318 15192359 := bstep (se 1 (by rfl) ⟨11394269, by rfl⟩ : syracuseStep 15192359 = 22788539) B22788539
theorem B1482479273 : Blo 702318 1482479273 := bstep (se 2 (by rfl) ⟨555929727, by rfl⟩ : syracuseStep 1482479273 = 1111859455) B1111859455
theorem B1500095 : Blo 702318 1500095 := bstep (se 1 (by rfl) ⟨1125071, by rfl⟩ : syracuseStep 1500095 = 2250143) B2250143
theorem B2614735 : Blo 702318 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B7727881 : Blo 702318 7727881 := bstep (se 2 (by rfl) ⟨2897955, by rfl⟩ : syracuseStep 7727881 = 5795911) B5795911
theorem B1141865 : Blo 702318 1141865 := bstep (se 2 (by rfl) ⟨428199, by rfl⟩ : syracuseStep 1141865 = 856399) B856399
theorem B2847611 : Blo 702318 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B15433577 : Blo 702318 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B3571775 : Blo 702318 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B3803111 : Blo 702318 3803111 := bstep (se 1 (by rfl) ⟨2852333, by rfl⟩ : syracuseStep 3803111 = 5704667) B5704667
theorem B3803689 : Blo 702318 3803689 := bstep (se 2 (by rfl) ⟨1426383, by rfl⟩ : syracuseStep 3803689 = 2852767) B2852767
theorem B10128239 : Blo 702318 10128239 := bstep (se 1 (by rfl) ⟨7596179, by rfl⟩ : syracuseStep 10128239 = 15192359) B15192359
theorem B3804857 : Blo 702318 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B988319515 : Blo 702318 988319515 := bstep (se 1 (by rfl) ⟨741239636, by rfl⟩ : syracuseStep 988319515 = 1482479273) B1482479273
theorem B790303 : Blo 702318 790303 := bstep (se 1 (by rfl) ⟨592727, by rfl⟩ : syracuseStep 790303 = 1185455) B1185455
theorem B2887751 : Blo 702318 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B2167649 : Blo 702318 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B1053935 : Blo 702318 1053935 := bstep (se 1 (by rfl) ⟨790451, by rfl⟩ : syracuseStep 1053935 = 1580903) B1580903
theorem B792319 : Blo 702318 792319 := bstep (se 1 (by rfl) ⟨594239, by rfl⟩ : syracuseStep 792319 = 1188479) B1188479
theorem B1580255 : Blo 702318 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B761243 : Blo 702318 761243 := bstep (se 1 (by rfl) ⟨570932, by rfl⟩ : syracuseStep 761243 = 1141865) B1141865
theorem B1581281 : Blo 702318 1581281 := bstep (se 2 (by rfl) ⟨592980, by rfl⟩ : syracuseStep 1581281 = 1185961) B1185961
theorem B3811691 : Blo 702318 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B1585223 : Blo 702318 1585223 := bstep (se 1 (by rfl) ⟨1188917, by rfl⟩ : syracuseStep 1585223 = 2377835) B2377835
theorem B3486313 : Blo 702318 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B702703 : Blo 702318 702703 := bstep (se 1 (by rfl) ⟨527027, by rfl⟩ : syracuseStep 702703 = 1054055) B1054055
theorem B10303841 : Blo 702318 10303841 := bstep (se 2 (by rfl) ⟨3863940, by rfl⟩ : syracuseStep 10303841 = 7727881) B7727881
theorem B3849241 : Blo 702318 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B705007 : Blo 702318 705007 := bstep (se 1 (by rfl) ⟨528755, by rfl⟩ : syracuseStep 705007 = 1057511) B1057511
theorem B1000063 : Blo 702318 1000063 := bstep (se 1 (by rfl) ⟨750047, by rfl⟩ : syracuseStep 1000063 = 1500095) B1500095
theorem B705151 : Blo 702318 705151 := bstep (se 1 (by rfl) ⟨528863, by rfl⟩ : syracuseStep 705151 = 1057727) B1057727
theorem B705255 : Blo 702318 705255 := bstep (se 1 (by rfl) ⟨528941, by rfl⟩ : syracuseStep 705255 = 1057883) B1057883
theorem B15190355 : Blo 702318 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B5360579 : Blo 702318 5360579 := bstep (se 1 (by rfl) ⟨4020434, by rfl⟩ : syracuseStep 5360579 = 8040869) B8040869
theorem B10276303 : Blo 702318 10276303 := bstep (se 1 (by rfl) ⟨7707227, by rfl⟩ : syracuseStep 10276303 = 15414455) B15414455
theorem B47043827 : Blo 702318 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B2381291 : Blo 702318 2381291 := bstep (se 1 (by rfl) ⟨1785968, by rfl⟩ : syracuseStep 2381291 = 3571937) B3571937
theorem B2382587 : Blo 702318 2382587 := bstep (se 1 (by rfl) ⟨1786940, by rfl⟩ : syracuseStep 2382587 = 3573881) B3573881
theorem B1898407 : Blo 702318 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B10289051 : Blo 702318 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B20283331 : Blo 702318 20283331 := bstep (se 1 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 20283331 = 30424997) B30424997
theorem B7700669 : Blo 702318 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B6752159 : Blo 702318 6752159 := bstep (se 1 (by rfl) ⟨5064119, by rfl⟩ : syracuseStep 6752159 = 10128239) B10128239
theorem B3573719 : Blo 702318 3573719 := bstep (se 1 (by rfl) ⟨2680289, by rfl⟩ : syracuseStep 3573719 = 5360579) B5360579
theorem B1445099 : Blo 702318 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B31362551 : Blo 702318 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B13701737 : Blo 702318 13701737 := bstep (se 2 (by rfl) ⟨5138151, by rfl⟩ : syracuseStep 13701737 = 10276303) B10276303
theorem B1053503 : Blo 702318 1053503 := bstep (se 1 (by rfl) ⟨790127, by rfl⟩ : syracuseStep 1053503 = 1580255) B1580255
theorem B1053737 : Blo 702318 1053737 := bstep (se 2 (by rfl) ⟨395151, by rfl⟩ : syracuseStep 1053737 = 790303) B790303
theorem B1054187 : Blo 702318 1054187 := bstep (se 1 (by rfl) ⟨790640, by rfl⟩ : syracuseStep 1054187 = 1581281) B1581281
theorem B40507613 : Blo 702318 40507613 := bstep (se 3 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 40507613 = 15190355) B15190355
theorem B1056425 : Blo 702318 1056425 := bstep (se 2 (by rfl) ⟨396159, by rfl⟩ : syracuseStep 1056425 = 792319) B792319
theorem B2531209 : Blo 702318 2531209 := bstep (se 2 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 2531209 = 1898407) B1898407
theorem B1056815 : Blo 702318 1056815 := bstep (se 1 (by rfl) ⟨792611, by rfl⟩ : syracuseStep 1056815 = 1585223) B1585223
theorem B27044441 : Blo 702318 27044441 := bstep (se 2 (by rfl) ⟨10141665, by rfl⟩ : syracuseStep 27044441 = 20283331) B20283331
theorem B6859367 : Blo 702318 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B2535407 : Blo 702318 2535407 := bstep (se 1 (by rfl) ⟨1901555, by rfl⟩ : syracuseStep 2535407 = 3803111) B3803111
theorem B2536571 : Blo 702318 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B702623 : Blo 702318 702623 := bstep (se 1 (by rfl) ⟨526967, by rfl⟩ : syracuseStep 702623 = 1053935) B1053935
theorem B1587527 : Blo 702318 1587527 := bstep (se 1 (by rfl) ⟨1190645, by rfl⟩ : syracuseStep 1587527 = 2381291) B2381291
theorem B1588391 : Blo 702318 1588391 := bstep (se 1 (by rfl) ⟨1191293, by rfl⟩ : syracuseStep 1588391 = 2382587) B2382587
theorem B2541127 : Blo 702318 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B5132321 : Blo 702318 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B6869227 : Blo 702318 6869227 := bstep (se 1 (by rfl) ⟨5151920, by rfl⟩ : syracuseStep 6869227 = 10303841) B10303841
theorem B2381183 : Blo 702318 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B1333417 : Blo 702318 1333417 := bstep (se 2 (by rfl) ⟨500031, by rfl⟩ : syracuseStep 1333417 = 1000063) B1000063
theorem B5071585 : Blo 702318 5071585 := bstep (se 2 (by rfl) ⟨1901844, by rfl⟩ : syracuseStep 5071585 = 3803689) B3803689
theorem B1317759353 : Blo 702318 1317759353 := bstep (se 2 (by rfl) ⟨494159757, by rfl⟩ : syracuseStep 1317759353 = 988319515) B988319515
theorem B4648417 : Blo 702318 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B2029981 : Blo 702318 2029981 := bstep (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) B761243
theorem B20908367 : Blo 702318 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B27005075 : Blo 702318 27005075 := bstep (se 1 (by rfl) ⟨20253806, by rfl⟩ : syracuseStep 27005075 = 40507613) B40507613
theorem B18029627 : Blo 702318 18029627 := bstep (se 1 (by rfl) ⟨13522220, by rfl⟩ : syracuseStep 18029627 = 27044441) B27044441
theorem B1777889 : Blo 702318 1777889 := bstep (se 2 (by rfl) ⟨666708, by rfl⟩ : syracuseStep 1777889 = 1333417) B1333417
theorem B1058351 : Blo 702318 1058351 := bstep (se 1 (by rfl) ⟨793763, by rfl⟩ : syracuseStep 1058351 = 1587527) B1587527
theorem B1058927 : Blo 702318 1058927 := bstep (se 1 (by rfl) ⟨794195, by rfl⟩ : syracuseStep 1058927 = 1588391) B1588391
theorem B6762113 : Blo 702318 6762113 := bstep (se 2 (by rfl) ⟨2535792, by rfl⟩ : syracuseStep 6762113 = 5071585) B5071585
theorem B4501439 : Blo 702318 4501439 := bstep (se 1 (by rfl) ⟨3376079, by rfl⟩ : syracuseStep 4501439 = 6752159) B6752159
theorem B3388169 : Blo 702318 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B3421547 : Blo 702318 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B702335 : Blo 702318 702335 := bstep (se 1 (by rfl) ⟨526751, by rfl⟩ : syracuseStep 702335 = 1053503) B1053503
theorem B702491 : Blo 702318 702491 := bstep (se 1 (by rfl) ⟨526868, by rfl⟩ : syracuseStep 702491 = 1053737) B1053737
theorem B1587455 : Blo 702318 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B702791 : Blo 702318 702791 := bstep (se 1 (by rfl) ⟨527093, by rfl⟩ : syracuseStep 702791 = 1054187) B1054187
theorem B704283 : Blo 702318 704283 := bstep (se 1 (by rfl) ⟨528212, by rfl⟩ : syracuseStep 704283 = 1056425) B1056425
theorem B704543 : Blo 702318 704543 := bstep (se 1 (by rfl) ⟨528407, by rfl⟩ : syracuseStep 704543 = 1056815) B1056815
theorem B9158969 : Blo 702318 9158969 := bstep (se 2 (by rfl) ⟨3434613, by rfl⟩ : syracuseStep 9158969 = 6869227) B6869227
theorem B4572911 : Blo 702318 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B24791557 : Blo 702318 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B1690271 : Blo 702318 1690271 := bstep (se 1 (by rfl) ⟨1267703, by rfl⟩ : syracuseStep 1690271 = 2535407) B2535407
theorem B2706641 : Blo 702318 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B3853597 : Blo 702318 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B1691047 : Blo 702318 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B5133779 : Blo 702318 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B2382479 : Blo 702318 2382479 := bstep (se 1 (by rfl) ⟨1786859, by rfl⟩ : syracuseStep 2382479 = 3573719) B3573719
theorem B9134491 : Blo 702318 9134491 := bstep (se 1 (by rfl) ⟨6850868, by rfl⟩ : syracuseStep 9134491 = 13701737) B13701737
theorem B878506235 : Blo 702318 878506235 := bstep (se 1 (by rfl) ⟨658879676, by rfl⟩ : syracuseStep 878506235 = 1317759353) B1317759353
theorem B3374945 : Blo 702318 3374945 := bstep (se 2 (by rfl) ⟨1265604, by rfl⟩ : syracuseStep 3374945 = 2531209) B2531209
theorem B3048607 : Blo 702318 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B1804427 : Blo 702318 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B1185259 : Blo 702318 1185259 := bstep (se 1 (by rfl) ⟨888944, by rfl⟩ : syracuseStep 1185259 = 1777889) B1777889
theorem B585670823 : Blo 702318 585670823 := bstep (se 1 (by rfl) ⟨439253117, by rfl⟩ : syracuseStep 585670823 = 878506235) B878506235
theorem B1058303 : Blo 702318 1058303 := bstep (se 1 (by rfl) ⟨793727, by rfl⟩ : syracuseStep 1058303 = 1587455) B1587455
theorem B6105979 : Blo 702318 6105979 := bstep (se 1 (by rfl) ⟨4579484, by rfl⟩ : syracuseStep 6105979 = 9158969) B9158969
theorem B13938911 : Blo 702318 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B1126847 : Blo 702318 1126847 := bstep (se 1 (by rfl) ⟨845135, by rfl⟩ : syracuseStep 1126847 = 1690271) B1690271
theorem B18003383 : Blo 702318 18003383 := bstep (se 1 (by rfl) ⟨13502537, by rfl⟩ : syracuseStep 18003383 = 27005075) B27005075
theorem B3422519 : Blo 702318 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B1588319 : Blo 702318 1588319 := bstep (se 1 (by rfl) ⟨1191239, by rfl⟩ : syracuseStep 1588319 = 2382479) B2382479
theorem B705567 : Blo 702318 705567 := bstep (se 1 (by rfl) ⟨529175, by rfl⟩ : syracuseStep 705567 = 1058351) B1058351
theorem B705951 : Blo 702318 705951 := bstep (se 1 (by rfl) ⟨529463, by rfl⟩ : syracuseStep 705951 = 1058927) B1058927
theorem B4508075 : Blo 702318 4508075 := bstep (se 1 (by rfl) ⟨3381056, by rfl⟩ : syracuseStep 4508075 = 6762113) B6762113
theorem B3000959 : Blo 702318 3000959 := bstep (se 1 (by rfl) ⟨2250719, by rfl⟩ : syracuseStep 3000959 = 4501439) B4501439
theorem B2281031 : Blo 702318 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B2249963 : Blo 702318 2249963 := bstep (se 1 (by rfl) ⟨1687472, by rfl⟩ : syracuseStep 2249963 = 3374945) B3374945
theorem B12179321 : Blo 702318 12179321 := bstep (se 2 (by rfl) ⟨4567245, by rfl⟩ : syracuseStep 12179321 = 9134491) B9134491
theorem B33055409 : Blo 702318 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B5138129 : Blo 702318 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B2254729 : Blo 702318 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B12019751 : Blo 702318 12019751 := bstep (se 1 (by rfl) ⟨9014813, by rfl⟩ : syracuseStep 12019751 = 18029627) B18029627
theorem B2258779 : Blo 702318 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B2000639 : Blo 702318 2000639 := bstep (se 1 (by rfl) ⟨1500479, by rfl⟩ : syracuseStep 2000639 = 3000959) B3000959
theorem B88147757 : Blo 702318 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B16259237 : Blo 702318 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B1580345 : Blo 702318 1580345 := bstep (se 2 (by rfl) ⟨592629, by rfl⟩ : syracuseStep 1580345 = 1185259) B1185259
theorem B12002255 : Blo 702318 12002255 := bstep (se 1 (by rfl) ⟨9001691, by rfl⟩ : syracuseStep 12002255 = 18003383) B18003383
theorem B1058879 : Blo 702318 1058879 := bstep (se 1 (by rfl) ⟨794159, by rfl⟩ : syracuseStep 1058879 = 1588319) B1588319
theorem B1520687 : Blo 702318 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B8141305 : Blo 702318 8141305 := bstep (se 2 (by rfl) ⟨3052989, by rfl⟩ : syracuseStep 8141305 = 6105979) B6105979
theorem B390447215 : Blo 702318 390447215 := bstep (se 1 (by rfl) ⟨292835411, by rfl⟩ : syracuseStep 390447215 = 585670823) B585670823
theorem B705535 : Blo 702318 705535 := bstep (se 1 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 705535 = 1058303) B1058303
theorem B3425419 : Blo 702318 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B8013167 : Blo 702318 8013167 := bstep (se 1 (by rfl) ⟨6009875, by rfl⟩ : syracuseStep 8013167 = 12019751) B12019751
theorem B9292607 : Blo 702318 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B2281679 : Blo 702318 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B1202951 : Blo 702318 1202951 := bstep (se 1 (by rfl) ⟨902213, by rfl⟩ : syracuseStep 1202951 = 1804427) B1804427
theorem B3005383 : Blo 702318 3005383 := bstep (se 1 (by rfl) ⟨2254037, by rfl⟩ : syracuseStep 3005383 = 4508075) B4508075
theorem B3006305 : Blo 702318 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B1499975 : Blo 702318 1499975 := bstep (se 1 (by rfl) ⟨1124981, by rfl⟩ : syracuseStep 1499975 = 2249963) B2249963
theorem B8119547 : Blo 702318 8119547 := bstep (se 1 (by rfl) ⟨6089660, by rfl⟩ : syracuseStep 8119547 = 12179321) B12179321
theorem B3011705 : Blo 702318 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B751231 : Blo 702318 751231 := bstep (se 1 (by rfl) ⟨563423, by rfl⟩ : syracuseStep 751231 = 1126847) B1126847
theorem B5342111 : Blo 702318 5342111 := bstep (se 1 (by rfl) ⟨4006583, by rfl⟩ : syracuseStep 5342111 = 8013167) B8013167
theorem B6195071 : Blo 702318 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B1053563 : Blo 702318 1053563 := bstep (se 1 (by rfl) ⟨790172, by rfl⟩ : syracuseStep 1053563 = 1580345) B1580345
theorem B2004203 : Blo 702318 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B8001503 : Blo 702318 8001503 := bstep (se 1 (by rfl) ⟨6001127, by rfl⟩ : syracuseStep 8001503 = 12002255) B12002255
theorem B5413031 : Blo 702318 5413031 := bstep (se 1 (by rfl) ⟨4059773, by rfl⟩ : syracuseStep 5413031 = 8119547) B8119547
theorem B10855073 : Blo 702318 10855073 := bstep (se 2 (by rfl) ⟨4070652, by rfl⟩ : syracuseStep 10855073 = 8141305) B8141305
theorem B2007803 : Blo 702318 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B4007177 : Blo 702318 4007177 := bstep (se 2 (by rfl) ⟨1502691, by rfl⟩ : syracuseStep 4007177 = 3005383) B3005383
theorem B58765171 : Blo 702318 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B1521119 : Blo 702318 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B999983 : Blo 702318 999983 := bstep (se 1 (by rfl) ⟨749987, by rfl⟩ : syracuseStep 999983 = 1499975) B1499975
theorem B18268901 : Blo 702318 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B705919 : Blo 702318 705919 := bstep (se 1 (by rfl) ⟨529439, by rfl⟩ : syracuseStep 705919 = 1058879) B1058879
theorem B1001641 : Blo 702318 1001641 := bstep (se 2 (by rfl) ⟨375615, by rfl⟩ : syracuseStep 1001641 = 751231) B751231
theorem B260298143 : Blo 702318 260298143 := bstep (se 1 (by rfl) ⟨195223607, by rfl⟩ : syracuseStep 260298143 = 390447215) B390447215
theorem B1333759 : Blo 702318 1333759 := bstep (se 1 (by rfl) ⟨1000319, by rfl⟩ : syracuseStep 1333759 = 2000639) B2000639
theorem B10839491 : Blo 702318 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B3207869 : Blo 702318 3207869 := bstep (se 3 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 3207869 = 1202951) B1202951
theorem B1013791 : Blo 702318 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B4130047 : Blo 702318 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B5344541 : Blo 702318 5344541 := bstep (se 3 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 5344541 = 2004203) B2004203
theorem B3608687 : Blo 702318 3608687 := bstep (se 1 (by rfl) ⟨2706515, by rfl⟩ : syracuseStep 3608687 = 5413031) B5413031
theorem B78353561 : Blo 702318 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B1351721 : Blo 702318 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B2138579 : Blo 702318 2138579 := bstep (se 1 (by rfl) ⟨1603934, by rfl⟩ : syracuseStep 2138579 = 3207869) B3207869
theorem B1778345 : Blo 702318 1778345 := bstep (se 2 (by rfl) ⟨666879, by rfl⟩ : syracuseStep 1778345 = 1333759) B1333759
theorem B2666621 : Blo 702318 2666621 := bstep (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) B999983
theorem B702375 : Blo 702318 702375 := bstep (se 1 (by rfl) ⟨526781, by rfl⟩ : syracuseStep 702375 = 1053563) B1053563
theorem B2671451 : Blo 702318 2671451 := bstep (se 1 (by rfl) ⟨2003588, by rfl⟩ : syracuseStep 2671451 = 4007177) B4007177
theorem B7226327 : Blo 702318 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B12179267 : Blo 702318 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B3561407 : Blo 702318 3561407 := bstep (se 1 (by rfl) ⟨2671055, by rfl⟩ : syracuseStep 3561407 = 5342111) B5342111
theorem B1335521 : Blo 702318 1335521 := bstep (se 2 (by rfl) ⟨500820, by rfl⟩ : syracuseStep 1335521 = 1001641) B1001641
theorem B173532095 : Blo 702318 173532095 := bstep (se 1 (by rfl) ⟨130149071, by rfl⟩ : syracuseStep 173532095 = 260298143) B260298143
theorem B4056317 : Blo 702318 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B5334335 : Blo 702318 5334335 := bstep (se 1 (by rfl) ⟨4000751, by rfl⟩ : syracuseStep 5334335 = 8001503) B8001503
theorem B7236715 : Blo 702318 7236715 := bstep (se 1 (by rfl) ⟨5427536, by rfl⟩ : syracuseStep 7236715 = 10855073) B10855073
theorem B1338535 : Blo 702318 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B4817551 : Blo 702318 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B52235707 : Blo 702318 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B890347 : Blo 702318 890347 := bstep (se 1 (by rfl) ⟨667760, by rfl⟩ : syracuseStep 890347 = 1335521) B1335521
theorem B1185563 : Blo 702318 1185563 := bstep (se 1 (by rfl) ⟨889172, by rfl⟩ : syracuseStep 1185563 = 1778345) B1778345
theorem B22026917 : Blo 702318 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B1777747 : Blo 702318 1777747 := bstep (se 1 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 1777747 = 2666621) B2666621
theorem B1780967 : Blo 702318 1780967 := bstep (se 1 (by rfl) ⟨1335725, by rfl⟩ : syracuseStep 1780967 = 2671451) B2671451
theorem B2405791 : Blo 702318 2405791 := bstep (se 1 (by rfl) ⟨1804343, by rfl⟩ : syracuseStep 2405791 = 3608687) B3608687
theorem B2374271 : Blo 702318 2374271 := bstep (se 1 (by rfl) ⟨1780703, by rfl⟩ : syracuseStep 2374271 = 3561407) B3561407
theorem B9648953 : Blo 702318 9648953 := bstep (se 2 (by rfl) ⟨3618357, by rfl⟩ : syracuseStep 9648953 = 7236715) B7236715
theorem B1784713 : Blo 702318 1784713 := bstep (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) B1338535
theorem B901147 : Blo 702318 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B1425719 : Blo 702318 1425719 := bstep (se 1 (by rfl) ⟨1069289, by rfl⟩ : syracuseStep 1425719 = 2138579) B2138579
theorem B115688063 : Blo 702318 115688063 := bstep (se 1 (by rfl) ⟨86766047, by rfl⟩ : syracuseStep 115688063 = 173532095) B173532095
theorem B2704211 : Blo 702318 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B3556223 : Blo 702318 3556223 := bstep (se 1 (by rfl) ⟨2667167, by rfl⟩ : syracuseStep 3556223 = 5334335) B5334335
theorem B3563027 : Blo 702318 3563027 := bstep (se 1 (by rfl) ⟨2672270, by rfl⟩ : syracuseStep 3563027 = 5344541) B5344541
theorem B8119511 : Blo 702318 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B1802807 : Blo 702318 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B3801917 : Blo 702318 3801917 := bstep (se 3 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 3801917 = 1425719) B1425719
theorem B6423401 : Blo 702318 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B790375 : Blo 702318 790375 := bstep (se 1 (by rfl) ⟨592781, by rfl⟩ : syracuseStep 790375 = 1185563) B1185563
theorem B14684611 : Blo 702318 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B5413007 : Blo 702318 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B1187129 : Blo 702318 1187129 := bstep (se 2 (by rfl) ⟨445173, by rfl⟩ : syracuseStep 1187129 = 890347) B890347
theorem B1187311 : Blo 702318 1187311 := bstep (se 1 (by rfl) ⟨890483, by rfl⟩ : syracuseStep 1187311 = 1780967) B1780967
theorem B1582847 : Blo 702318 1582847 := bstep (se 1 (by rfl) ⟨1187135, by rfl⟩ : syracuseStep 1582847 = 2374271) B2374271
theorem B6432635 : Blo 702318 6432635 := bstep (se 1 (by rfl) ⟨4824476, by rfl⟩ : syracuseStep 6432635 = 9648953) B9648953
theorem B2370329 : Blo 702318 2370329 := bstep (se 2 (by rfl) ⟨888873, by rfl⟩ : syracuseStep 2370329 = 1777747) B1777747
theorem B2370815 : Blo 702318 2370815 := bstep (se 1 (by rfl) ⟨1778111, by rfl⟩ : syracuseStep 2370815 = 3556223) B3556223
theorem B69647609 : Blo 702318 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B2375351 : Blo 702318 2375351 := bstep (se 1 (by rfl) ⟨1781513, by rfl⟩ : syracuseStep 2375351 = 3563027) B3563027
theorem B2379617 : Blo 702318 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B1201529 : Blo 702318 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B77125375 : Blo 702318 77125375 := bstep (se 1 (by rfl) ⟨57844031, by rfl⟩ : syracuseStep 77125375 = 115688063) B115688063
theorem B3207721 : Blo 702318 3207721 := bstep (se 2 (by rfl) ⟨1202895, by rfl⟩ : syracuseStep 3207721 = 2405791) B2405791
theorem B3608671 : Blo 702318 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B791419 : Blo 702318 791419 := bstep (se 1 (by rfl) ⟨593564, by rfl⟩ : syracuseStep 791419 = 1187129) B1187129
theorem B1053833 : Blo 702318 1053833 := bstep (se 2 (by rfl) ⟨395187, by rfl⟩ : syracuseStep 1053833 = 790375) B790375
theorem B1055231 : Blo 702318 1055231 := bstep (se 1 (by rfl) ⟨791423, by rfl⟩ : syracuseStep 1055231 = 1582847) B1582847
theorem B1580219 : Blo 702318 1580219 := bstep (se 1 (by rfl) ⟨1185164, by rfl⟩ : syracuseStep 1580219 = 2370329) B2370329
theorem B1580543 : Blo 702318 1580543 := bstep (se 1 (by rfl) ⟨1185407, by rfl⟩ : syracuseStep 1580543 = 2370815) B2370815
theorem B102833833 : Blo 702318 102833833 := bstep (se 2 (by rfl) ⟨38562687, by rfl⟩ : syracuseStep 102833833 = 77125375) B77125375
theorem B1583081 : Blo 702318 1583081 := bstep (se 2 (by rfl) ⟨593655, by rfl⟩ : syracuseStep 1583081 = 1187311) B1187311
theorem B1583567 : Blo 702318 1583567 := bstep (se 1 (by rfl) ⟨1187675, by rfl⟩ : syracuseStep 1583567 = 2375351) B2375351
theorem B2534611 : Blo 702318 2534611 := bstep (se 1 (by rfl) ⟨1900958, by rfl⟩ : syracuseStep 2534611 = 3801917) B3801917
theorem B1586411 : Blo 702318 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B801019 : Blo 702318 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B19579481 : Blo 702318 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B4276961 : Blo 702318 4276961 := bstep (se 2 (by rfl) ⟨1603860, by rfl⟩ : syracuseStep 4276961 = 3207721) B3207721
theorem B1201871 : Blo 702318 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B4282267 : Blo 702318 4282267 := bstep (se 1 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 4282267 = 6423401) B6423401
theorem B4288423 : Blo 702318 4288423 := bstep (se 1 (by rfl) ⟨3216317, by rfl⟩ : syracuseStep 4288423 = 6432635) B6432635
theorem B46431739 : Blo 702318 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B2851307 : Blo 702318 2851307 := bstep (se 1 (by rfl) ⟨2138480, by rfl⟩ : syracuseStep 2851307 = 4276961) B4276961
theorem B3379481 : Blo 702318 3379481 := bstep (se 2 (by rfl) ⟨1267305, by rfl⟩ : syracuseStep 3379481 = 2534611) B2534611
theorem B1053479 : Blo 702318 1053479 := bstep (se 1 (by rfl) ⟨790109, by rfl⟩ : syracuseStep 1053479 = 1580219) B1580219
theorem B1053695 : Blo 702318 1053695 := bstep (se 1 (by rfl) ⟨790271, by rfl⟩ : syracuseStep 1053695 = 1580543) B1580543
theorem B1055225 : Blo 702318 1055225 := bstep (se 2 (by rfl) ⟨395709, by rfl⟩ : syracuseStep 1055225 = 791419) B791419
theorem B1055387 : Blo 702318 1055387 := bstep (se 1 (by rfl) ⟨791540, by rfl⟩ : syracuseStep 1055387 = 1583081) B1583081
theorem B1055711 : Blo 702318 1055711 := bstep (se 1 (by rfl) ⟨791783, by rfl⟩ : syracuseStep 1055711 = 1583567) B1583567
theorem B5709689 : Blo 702318 5709689 := bstep (se 2 (by rfl) ⟨2141133, by rfl⟩ : syracuseStep 5709689 = 4282267) B4282267
theorem B1057607 : Blo 702318 1057607 := bstep (se 1 (by rfl) ⟨793205, by rfl⟩ : syracuseStep 1057607 = 1586411) B1586411
theorem B61908985 : Blo 702318 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B137111777 : Blo 702318 137111777 := bstep (se 2 (by rfl) ⟨51416916, by rfl⟩ : syracuseStep 137111777 = 102833833) B102833833
theorem B13052987 : Blo 702318 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B4272101 : Blo 702318 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B702555 : Blo 702318 702555 := bstep (se 1 (by rfl) ⟨526916, by rfl⟩ : syracuseStep 702555 = 1053833) B1053833
theorem B801247 : Blo 702318 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B703487 : Blo 702318 703487 := bstep (se 1 (by rfl) ⟨527615, by rfl⟩ : syracuseStep 703487 = 1055231) B1055231
theorem B5717897 : Blo 702318 5717897 := bstep (se 2 (by rfl) ⟨2144211, by rfl⟩ : syracuseStep 5717897 = 4288423) B4288423
theorem B4811561 : Blo 702318 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B1900871 : Blo 702318 1900871 := bstep (se 1 (by rfl) ⟨1425653, by rfl⟩ : syracuseStep 1900871 = 2851307) B2851307
theorem B82545313 : Blo 702318 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B3806459 : Blo 702318 3806459 := bstep (se 1 (by rfl) ⟨2854844, by rfl⟩ : syracuseStep 3806459 = 5709689) B5709689
theorem B3811931 : Blo 702318 3811931 := bstep (se 1 (by rfl) ⟨2858948, by rfl⟩ : syracuseStep 3811931 = 5717897) B5717897
theorem B702319 : Blo 702318 702319 := bstep (se 1 (by rfl) ⟨526739, by rfl⟩ : syracuseStep 702319 = 1053479) B1053479
theorem B702463 : Blo 702318 702463 := bstep (se 1 (by rfl) ⟨526847, by rfl⟩ : syracuseStep 702463 = 1053695) B1053695
theorem B703483 : Blo 702318 703483 := bstep (se 1 (by rfl) ⟨527612, by rfl⟩ : syracuseStep 703483 = 1055225) B1055225
theorem B703591 : Blo 702318 703591 := bstep (se 1 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 703591 = 1055387) B1055387
theorem B703807 : Blo 702318 703807 := bstep (se 1 (by rfl) ⟨527855, by rfl⟩ : syracuseStep 703807 = 1055711) B1055711
theorem B705071 : Blo 702318 705071 := bstep (se 1 (by rfl) ⟨528803, by rfl⟩ : syracuseStep 705071 = 1057607) B1057607
theorem B91407851 : Blo 702318 91407851 := bstep (se 1 (by rfl) ⟨68555888, by rfl⟩ : syracuseStep 91407851 = 137111777) B137111777
theorem B8701991 : Blo 702318 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B1068329 : Blo 702318 1068329 := bstep (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) B801247
theorem B2252987 : Blo 702318 2252987 := bstep (se 1 (by rfl) ⟨1689740, by rfl⟩ : syracuseStep 2252987 = 3379481) B3379481
theorem B3207707 : Blo 702318 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B2848067 : Blo 702318 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B5801327 : Blo 702318 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B2138471 : Blo 702318 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B2537639 : Blo 702318 2537639 := bstep (se 1 (by rfl) ⟨1903229, by rfl⟩ : syracuseStep 2537639 = 3806459) B3806459
theorem B2541287 : Blo 702318 2541287 := bstep (se 1 (by rfl) ⟨1905965, by rfl⟩ : syracuseStep 2541287 = 3811931) B3811931
theorem B1267247 : Blo 702318 1267247 := bstep (se 1 (by rfl) ⟨950435, by rfl⟩ : syracuseStep 1267247 = 1900871) B1900871
theorem B60938567 : Blo 702318 60938567 := bstep (se 1 (by rfl) ⟨45703925, by rfl⟩ : syracuseStep 60938567 = 91407851) B91407851
theorem B110060417 : Blo 702318 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B1501991 : Blo 702318 1501991 := bstep (se 1 (by rfl) ⟨1126493, by rfl⟩ : syracuseStep 1501991 = 2252987) B2252987
theorem B2848877 : Blo 702318 2848877 := bstep (se 3 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 2848877 = 1068329) B1068329
theorem B1898711 : Blo 702318 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B3867551 : Blo 702318 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B3379325 : Blo 702318 3379325 := bstep (se 3 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 3379325 = 1267247) B1267247
theorem B73373611 : Blo 702318 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B1425647 : Blo 702318 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B1001327 : Blo 702318 1001327 := bstep (se 1 (by rfl) ⟨750995, by rfl⟩ : syracuseStep 1001327 = 1501991) B1501991
theorem B1691759 : Blo 702318 1691759 := bstep (se 1 (by rfl) ⟨1268819, by rfl⟩ : syracuseStep 1691759 = 2537639) B2537639
theorem B1265807 : Blo 702318 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B1694191 : Blo 702318 1694191 := bstep (se 1 (by rfl) ⟨1270643, by rfl⟩ : syracuseStep 1694191 = 2541287) B2541287
theorem B40625711 : Blo 702318 40625711 := bstep (se 1 (by rfl) ⟨30469283, by rfl⟩ : syracuseStep 40625711 = 60938567) B60938567
theorem B1899251 : Blo 702318 1899251 := bstep (se 1 (by rfl) ⟨1424438, by rfl⟩ : syracuseStep 1899251 = 2848877) B2848877
theorem B9011533 : Blo 702318 9011533 := bstep (se 3 (by rfl) ⟨1689662, by rfl⟩ : syracuseStep 9011533 = 3379325) B3379325
theorem B3801725 : Blo 702318 3801725 := bstep (se 3 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 3801725 = 1425647) B1425647
theorem B1127839 : Blo 702318 1127839 := bstep (se 1 (by rfl) ⟨845879, by rfl⟩ : syracuseStep 1127839 = 1691759) B1691759
theorem B2670205 : Blo 702318 2670205 := bstep (se 3 (by rfl) ⟨500663, by rfl⟩ : syracuseStep 2670205 = 1001327) B1001327
theorem B27083807 : Blo 702318 27083807 := bstep (se 1 (by rfl) ⟨20312855, by rfl⟩ : syracuseStep 27083807 = 40625711) B40625711
theorem B97831481 : Blo 702318 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B1266167 : Blo 702318 1266167 := bstep (se 1 (by rfl) ⟨949625, by rfl⟩ : syracuseStep 1266167 = 1899251) B1899251
theorem B843871 : Blo 702318 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B2258921 : Blo 702318 2258921 := bstep (se 2 (by rfl) ⟨847095, by rfl⟩ : syracuseStep 2258921 = 1694191) B1694191
theorem B41253877 : Blo 702318 41253877 := bstep (se 5 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 41253877 = 3867551) B3867551
theorem B18055871 : Blo 702318 18055871 := bstep (se 1 (by rfl) ⟨13541903, by rfl⟩ : syracuseStep 18055871 = 27083807) B27083807
theorem B1043535797 : Blo 702318 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B1125161 : Blo 702318 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B2534483 : Blo 702318 2534483 := bstep (se 1 (by rfl) ⟨1900862, by rfl⟩ : syracuseStep 2534483 = 3801725) B3801725
theorem B55005169 : Blo 702318 55005169 := bstep (se 2 (by rfl) ⟨20626938, by rfl⟩ : syracuseStep 55005169 = 41253877) B41253877
theorem B3560273 : Blo 702318 3560273 := bstep (se 2 (by rfl) ⟨1335102, by rfl⟩ : syracuseStep 3560273 = 2670205) B2670205
theorem B12015377 : Blo 702318 12015377 := bstep (se 2 (by rfl) ⟨4505766, by rfl⟩ : syracuseStep 12015377 = 9011533) B9011533
theorem B844111 : Blo 702318 844111 := bstep (se 1 (by rfl) ⟨633083, by rfl⟩ : syracuseStep 844111 = 1266167) B1266167
theorem B1503785 : Blo 702318 1503785 := bstep (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) B1127839
theorem B1505947 : Blo 702318 1505947 := bstep (se 1 (by rfl) ⟨1129460, by rfl⟩ : syracuseStep 1505947 = 2258921) B2258921
theorem B73340225 : Blo 702318 73340225 := bstep (se 2 (by rfl) ⟨27502584, by rfl⟩ : syracuseStep 73340225 = 55005169) B55005169
theorem B2007929 : Blo 702318 2007929 := bstep (se 2 (by rfl) ⟨752973, by rfl⟩ : syracuseStep 2007929 = 1505947) B1505947
theorem B12037247 : Blo 702318 12037247 := bstep (se 1 (by rfl) ⟨9027935, by rfl⟩ : syracuseStep 12037247 = 18055871) B18055871
theorem B4010093 : Blo 702318 4010093 := bstep (se 3 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 4010093 = 1503785) B1503785
theorem B4501925 : Blo 702318 4501925 := bstep (se 4 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 4501925 = 844111) B844111
theorem B2373515 : Blo 702318 2373515 := bstep (se 1 (by rfl) ⟨1780136, by rfl⟩ : syracuseStep 2373515 = 3560273) B3560273
theorem B8010251 : Blo 702318 8010251 := bstep (se 1 (by rfl) ⟨6007688, by rfl⟩ : syracuseStep 8010251 = 12015377) B12015377
theorem B1689655 : Blo 702318 1689655 := bstep (se 1 (by rfl) ⟨1267241, by rfl⟩ : syracuseStep 1689655 = 2534483) B2534483
theorem B695690531 : Blo 702318 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B750107 : Blo 702318 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 702318 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B48893483 : Blo 702318 48893483 := bstep (se 1 (by rfl) ⟨36670112, by rfl⟩ : syracuseStep 48893483 = 73340225) B73340225
theorem B1582343 : Blo 702318 1582343 := bstep (se 1 (by rfl) ⟨1186757, by rfl⟩ : syracuseStep 1582343 = 2373515) B2373515
theorem B2673395 : Blo 702318 2673395 := bstep (se 1 (by rfl) ⟨2005046, by rfl⟩ : syracuseStep 2673395 = 4010093) B4010093
theorem B3001283 : Blo 702318 3001283 := bstep (se 1 (by rfl) ⟨2250962, by rfl⟩ : syracuseStep 3001283 = 4501925) B4501925
theorem B2252873 : Blo 702318 2252873 := bstep (se 2 (by rfl) ⟨844827, by rfl⟩ : syracuseStep 2252873 = 1689655) B1689655
theorem B1338619 : Blo 702318 1338619 := bstep (se 1 (by rfl) ⟨1003964, by rfl⟩ : syracuseStep 1338619 = 2007929) B2007929
theorem B463793687 : Blo 702318 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B8024831 : Blo 702318 8024831 := bstep (se 1 (by rfl) ⟨6018623, by rfl⟩ : syracuseStep 8024831 = 12037247) B12037247
theorem B5340167 : Blo 702318 5340167 := bstep (se 1 (by rfl) ⟨4005125, by rfl⟩ : syracuseStep 5340167 = 8010251) B8010251
theorem B2000855 : Blo 702318 2000855 := bstep (se 1 (by rfl) ⟨1500641, by rfl⟩ : syracuseStep 2000855 = 3001283) B3001283
theorem B1054895 : Blo 702318 1054895 := bstep (se 1 (by rfl) ⟨791171, by rfl⟩ : syracuseStep 1054895 = 1582343) B1582343
theorem B5349887 : Blo 702318 5349887 := bstep (se 1 (by rfl) ⟨4012415, by rfl⟩ : syracuseStep 5349887 = 8024831) B8024831
theorem B1782263 : Blo 702318 1782263 := bstep (se 1 (by rfl) ⟨1336697, by rfl⟩ : syracuseStep 1782263 = 2673395) B2673395
theorem B1784825 : Blo 702318 1784825 := bstep (se 2 (by rfl) ⟨669309, by rfl⟩ : syracuseStep 1784825 = 1338619) B1338619
theorem B3560111 : Blo 702318 3560111 := bstep (se 1 (by rfl) ⟨2670083, by rfl⟩ : syracuseStep 3560111 = 5340167) B5340167
theorem B1333523 : Blo 702318 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B1501915 : Blo 702318 1501915 := bstep (se 1 (by rfl) ⟨1126436, by rfl⟩ : syracuseStep 1501915 = 2252873) B2252873
theorem B309195791 : Blo 702318 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B130382621 : Blo 702318 130382621 := bstep (se 3 (by rfl) ⟨24446741, by rfl⟩ : syracuseStep 130382621 = 48893483) B48893483
theorem B2002553 : Blo 702318 2002553 := bstep (se 2 (by rfl) ⟨750957, by rfl⟩ : syracuseStep 2002553 = 1501915) B1501915
theorem B1188175 : Blo 702318 1188175 := bstep (se 1 (by rfl) ⟨891131, by rfl⟩ : syracuseStep 1188175 = 1782263) B1782263
theorem B1189883 : Blo 702318 1189883 := bstep (se 1 (by rfl) ⟨892412, by rfl⟩ : syracuseStep 1189883 = 1784825) B1784825
theorem B2373407 : Blo 702318 2373407 := bstep (se 1 (by rfl) ⟨1780055, by rfl⟩ : syracuseStep 2373407 = 3560111) B3560111
theorem B703263 : Blo 702318 703263 := bstep (se 1 (by rfl) ⟨527447, by rfl⟩ : syracuseStep 703263 = 1054895) B1054895
theorem B3556061 : Blo 702318 3556061 := bstep (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) B1333523
theorem B206130527 : Blo 702318 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B86921747 : Blo 702318 86921747 := bstep (se 1 (by rfl) ⟨65191310, by rfl⟩ : syracuseStep 86921747 = 130382621) B130382621
theorem B1333903 : Blo 702318 1333903 := bstep (se 1 (by rfl) ⟨1000427, by rfl⟩ : syracuseStep 1333903 = 2000855) B2000855
theorem B3566591 : Blo 702318 3566591 := bstep (se 1 (by rfl) ⟨2674943, by rfl⟩ : syracuseStep 3566591 = 5349887) B5349887
theorem B793255 : Blo 702318 793255 := bstep (se 1 (by rfl) ⟨594941, by rfl⟩ : syracuseStep 793255 = 1189883) B1189883
theorem B1778537 : Blo 702318 1778537 := bstep (se 2 (by rfl) ⟨666951, by rfl⟩ : syracuseStep 1778537 = 1333903) B1333903
theorem B1582271 : Blo 702318 1582271 := bstep (se 1 (by rfl) ⟨1186703, by rfl⟩ : syracuseStep 1582271 = 2373407) B2373407
theorem B1584233 : Blo 702318 1584233 := bstep (se 2 (by rfl) ⟨594087, by rfl⟩ : syracuseStep 1584233 = 1188175) B1188175
theorem B2370707 : Blo 702318 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B57947831 : Blo 702318 57947831 := bstep (se 1 (by rfl) ⟨43460873, by rfl⟩ : syracuseStep 57947831 = 86921747) B86921747
theorem B2377727 : Blo 702318 2377727 := bstep (se 1 (by rfl) ⟨1783295, by rfl⟩ : syracuseStep 2377727 = 3566591) B3566591
theorem B137420351 : Blo 702318 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B1335035 : Blo 702318 1335035 := bstep (se 1 (by rfl) ⟨1001276, by rfl⟩ : syracuseStep 1335035 = 2002553) B2002553
theorem B890023 : Blo 702318 890023 := bstep (se 1 (by rfl) ⟨667517, by rfl⟩ : syracuseStep 890023 = 1335035) B1335035
theorem B1185691 : Blo 702318 1185691 := bstep (se 1 (by rfl) ⟨889268, by rfl⟩ : syracuseStep 1185691 = 1778537) B1778537
theorem B1054847 : Blo 702318 1054847 := bstep (se 1 (by rfl) ⟨791135, by rfl⟩ : syracuseStep 1054847 = 1582271) B1582271
theorem B1056155 : Blo 702318 1056155 := bstep (se 1 (by rfl) ⟨792116, by rfl⟩ : syracuseStep 1056155 = 1584233) B1584233
theorem B1580471 : Blo 702318 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B1057673 : Blo 702318 1057673 := bstep (se 2 (by rfl) ⟨396627, by rfl⟩ : syracuseStep 1057673 = 793255) B793255
theorem B1585151 : Blo 702318 1585151 := bstep (se 1 (by rfl) ⟨1188863, by rfl⟩ : syracuseStep 1585151 = 2377727) B2377727
theorem B91613567 : Blo 702318 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B38631887 : Blo 702318 38631887 := bstep (se 1 (by rfl) ⟨28973915, by rfl⟩ : syracuseStep 38631887 = 57947831) B57947831
theorem B1053647 : Blo 702318 1053647 := bstep (se 1 (by rfl) ⟨790235, by rfl⟩ : syracuseStep 1053647 = 1580471) B1580471
theorem B1186697 : Blo 702318 1186697 := bstep (se 2 (by rfl) ⟨445011, by rfl⟩ : syracuseStep 1186697 = 890023) B890023
theorem B1580921 : Blo 702318 1580921 := bstep (se 2 (by rfl) ⟨592845, by rfl⟩ : syracuseStep 1580921 = 1185691) B1185691
theorem B1056767 : Blo 702318 1056767 := bstep (se 1 (by rfl) ⟨792575, by rfl⟩ : syracuseStep 1056767 = 1585151) B1585151
theorem B703231 : Blo 702318 703231 := bstep (se 1 (by rfl) ⟨527423, by rfl⟩ : syracuseStep 703231 = 1054847) B1054847
theorem B704103 : Blo 702318 704103 := bstep (se 1 (by rfl) ⟨528077, by rfl⟩ : syracuseStep 704103 = 1056155) B1056155
theorem B705115 : Blo 702318 705115 := bstep (se 1 (by rfl) ⟨528836, by rfl⟩ : syracuseStep 705115 = 1057673) B1057673
theorem B61075711 : Blo 702318 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B25754591 : Blo 702318 25754591 := bstep (se 1 (by rfl) ⟨19315943, by rfl⟩ : syracuseStep 25754591 = 38631887) B38631887
theorem B791131 : Blo 702318 791131 := bstep (se 1 (by rfl) ⟨593348, by rfl⟩ : syracuseStep 791131 = 1186697) B1186697
theorem B1053947 : Blo 702318 1053947 := bstep (se 1 (by rfl) ⟨790460, by rfl⟩ : syracuseStep 1053947 = 1580921) B1580921
theorem B81434281 : Blo 702318 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B702431 : Blo 702318 702431 := bstep (se 1 (by rfl) ⟨526823, by rfl⟩ : syracuseStep 702431 = 1053647) B1053647
theorem B704511 : Blo 702318 704511 := bstep (se 1 (by rfl) ⟨528383, by rfl⟩ : syracuseStep 704511 = 1056767) B1056767
theorem B17169727 : Blo 702318 17169727 := bstep (se 1 (by rfl) ⟨12877295, by rfl⟩ : syracuseStep 17169727 = 25754591) B25754591
theorem B1054841 : Blo 702318 1054841 := bstep (se 2 (by rfl) ⟨395565, by rfl⟩ : syracuseStep 1054841 = 791131) B791131
theorem B702631 : Blo 702318 702631 := bstep (se 1 (by rfl) ⟨526973, by rfl⟩ : syracuseStep 702631 = 1053947) B1053947
theorem B108579041 : Blo 702318 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B22892969 : Blo 702318 22892969 := bstep (se 2 (by rfl) ⟨8584863, by rfl⟩ : syracuseStep 22892969 = 17169727) B17169727
theorem B72386027 : Blo 702318 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B703227 : Blo 702318 703227 := bstep (se 1 (by rfl) ⟨527420, by rfl⟩ : syracuseStep 703227 = 1054841) B1054841
theorem B15261979 : Blo 702318 15261979 := bstep (se 1 (by rfl) ⟨11446484, by rfl⟩ : syracuseStep 15261979 = 22892969) B22892969
theorem B20349305 : Blo 702318 20349305 := bstep (se 2 (by rfl) ⟨7630989, by rfl⟩ : syracuseStep 20349305 = 15261979) B15261979
theorem B48257351 : Blo 702318 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B13566203 : Blo 702318 13566203 := bstep (se 1 (by rfl) ⟨10174652, by rfl⟩ : syracuseStep 13566203 = 20349305) B20349305
theorem B32171567 : Blo 702318 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B9044135 : Blo 702318 9044135 := bstep (se 1 (by rfl) ⟨6783101, by rfl⟩ : syracuseStep 9044135 = 13566203) B13566203
theorem B85790845 : Blo 702318 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B6029423 : Blo 702318 6029423 := bstep (se 1 (by rfl) ⟨4522067, by rfl⟩ : syracuseStep 6029423 = 9044135) B9044135
theorem B457551173 : Blo 702318 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B4019615 : Blo 702318 4019615 := bstep (se 1 (by rfl) ⟨3014711, by rfl⟩ : syracuseStep 4019615 = 6029423) B6029423
theorem B305034115 : Blo 702318 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B2679743 : Blo 702318 2679743 := bstep (se 1 (by rfl) ⟨2009807, by rfl⟩ : syracuseStep 2679743 = 4019615) B4019615
theorem B406712153 : Blo 702318 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B1786495 : Blo 702318 1786495 := bstep (se 1 (by rfl) ⟨1339871, by rfl⟩ : syracuseStep 1786495 = 2679743) B2679743
theorem B271141435 : Blo 702318 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B1446087653 : Blo 702318 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B2381993 : Blo 702318 2381993 := bstep (se 2 (by rfl) ⟨893247, by rfl⟩ : syracuseStep 2381993 = 1786495) B1786495
theorem B1587995 : Blo 702318 1587995 := bstep (se 1 (by rfl) ⟨1190996, by rfl⟩ : syracuseStep 1587995 = 2381993) B2381993
theorem B964058435 : Blo 702318 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B1058663 : Blo 702318 1058663 := bstep (se 1 (by rfl) ⟨793997, by rfl⟩ : syracuseStep 1058663 = 1587995) B1587995
theorem B642705623 : Blo 702318 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B705775 : Blo 702318 705775 := bstep (se 1 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 705775 = 1058663) B1058663
theorem B428470415 : Blo 702318 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B285646943 : Blo 702318 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B761725181 : Blo 702318 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B507816787 : Blo 702318 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B677089049 : Blo 702318 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B1805570797 : Blo 702318 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 702318 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B1604951819 : Blo 702318 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1069967879 : Blo 702318 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B713311919 : Blo 702318 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B475541279 : Blo 702318 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B317027519 : Blo 702318 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B211351679 : Blo 702318 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B140901119 : Blo 702318 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 702318 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B62622719 : Blo 702318 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B41748479 : Blo 702318 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B27832319 : Blo 702318 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B18554879 : Blo 702318 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 702318 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B16493225 : Blo 702318 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B175927733 : Blo 702318 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 702318 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B78190103 : Blo 702318 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 702318 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B69502313 : Blo 702318 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 702318 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B61779833 : Blo 702318 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B41186555 : Blo 702318 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B27457703 : Blo 702318 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 702318 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B12203423 : Blo 702318 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B8135615 : Blo 702318 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B5423743 : Blo 702318 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B28926629 : Blo 702318 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B19284419 : Blo 702318 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B51425117 : Blo 702318 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B34283411 : Blo 702318 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B22855607 : Blo 702318 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B15237071 : Blo 702318 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 702318 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B6772031 : Blo 702318 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B4514687 : Blo 702318 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B3009791 : Blo 702318 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B2006527 : Blo 702318 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 702318 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B1783579 : Blo 702318 1783579 := bstep (se 1 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 1783579 = 2675369) B2675369
theorem B2378105 : Blo 702318 2378105 := bstep (se 2 (by rfl) ⟨891789, by rfl⟩ : syracuseStep 2378105 = 1783579) B1783579
theorem B1585403 : Blo 702318 1585403 := bstep (se 1 (by rfl) ⟨1189052, by rfl⟩ : syracuseStep 1585403 = 2378105) B2378105
theorem B1056935 : Blo 702318 1056935 := bstep (se 1 (by rfl) ⟨792701, by rfl⟩ : syracuseStep 1056935 = 1585403) B1585403
theorem B704623 : Blo 702318 704623 := bstep (se 1 (by rfl) ⟨528467, by rfl⟩ : syracuseStep 704623 = 1056935) B1056935

theorem C0 (j : ℕ) (h1 : 175579 ≤ j) (h2 : j ≤ 176278) : Blo 702318 (4 * j + 3) := by
  interval_cases j
  · exact B702319
  · exact B702323
  · exact B702327
  · exact B702331
  · exact B702335
  · exact B702339
  · exact B702343
  · exact B702347
  · exact B702351
  · exact B702355
  · exact B702359
  · exact B702363
  · exact B702367
  · exact B702371
  · exact B702375
  · exact B702379
  · exact B702383
  · exact B702387
  · exact B702391
  · exact B702395
  · exact B702399
  · exact B702403
  · exact B702407
  · exact B702411
  · exact B702415
  · exact B702419
  · exact B702423
  · exact B702427
  · exact B702431
  · exact B702435
  · exact B702439
  · exact B702443
  · exact B702447
  · exact B702451
  · exact B702455
  · exact B702459
  · exact B702463
  · exact B702467
  · exact B702471
  · exact B702475
  · exact B702479
  · exact B702483
  · exact B702487
  · exact B702491
  · exact B702495
  · exact B702499
  · exact B702503
  · exact B702507
  · exact B702511
  · exact B702515
  · exact B702519
  · exact B702523
  · exact B702527
  · exact B702531
  · exact B702535
  · exact B702539
  · exact B702543
  · exact B702547
  · exact B702551
  · exact B702555
  · exact B702559
  · exact B702563
  · exact B702567
  · exact B702571
  · exact B702575
  · exact B702579
  · exact B702583
  · exact B702587
  · exact B702591
  · exact B702595
  · exact B702599
  · exact B702603
  · exact B702607
  · exact B702611
  · exact B702615
  · exact B702619
  · exact B702623
  · exact B702627
  · exact B702631
  · exact B702635
  · exact B702639
  · exact B702643
  · exact B702647
  · exact B702651
  · exact B702655
  · exact B702659
  · exact B702663
  · exact B702667
  · exact B702671
  · exact B702675
  · exact B702679
  · exact B702683
  · exact B702687
  · exact B702691
  · exact B702695
  · exact B702699
  · exact B702703
  · exact B702707
  · exact B702711
  · exact B702715
  · exact B702719
  · exact B702723
  · exact B702727
  · exact B702731
  · exact B702735
  · exact B702739
  · exact B702743
  · exact B702747
  · exact B702751
  · exact B702755
  · exact B702759
  · exact B702763
  · exact B702767
  · exact B702771
  · exact B702775
  · exact B702779
  · exact B702783
  · exact B702787
  · exact B702791
  · exact B702795
  · exact B702799
  · exact B702803
  · exact B702807
  · exact B702811
  · exact B702815
  · exact B702819
  · exact B702823
  · exact B702827
  · exact B702831
  · exact B702835
  · exact B702839
  · exact B702843
  · exact B702847
  · exact B702851
  · exact B702855
  · exact B702859
  · exact B702863
  · exact B702867
  · exact B702871
  · exact B702875
  · exact B702879
  · exact B702883
  · exact B702887
  · exact B702891
  · exact B702895
  · exact B702899
  · exact B702903
  · exact B702907
  · exact B702911
  · exact B702915
  · exact B702919
  · exact B702923
  · exact B702927
  · exact B702931
  · exact B702935
  · exact B702939
  · exact B702943
  · exact B702947
  · exact B702951
  · exact B702955
  · exact B702959
  · exact B702963
  · exact B702967
  · exact B702971
  · exact B702975
  · exact B702979
  · exact B702983
  · exact B702987
  · exact B702991
  · exact B702995
  · exact B702999
  · exact B703003
  · exact B703007
  · exact B703011
  · exact B703015
  · exact B703019
  · exact B703023
  · exact B703027
  · exact B703031
  · exact B703035
  · exact B703039
  · exact B703043
  · exact B703047
  · exact B703051
  · exact B703055
  · exact B703059
  · exact B703063
  · exact B703067
  · exact B703071
  · exact B703075
  · exact B703079
  · exact B703083
  · exact B703087
  · exact B703091
  · exact B703095
  · exact B703099
  · exact B703103
  · exact B703107
  · exact B703111
  · exact B703115
  · exact B703119
  · exact B703123
  · exact B703127
  · exact B703131
  · exact B703135
  · exact B703139
  · exact B703143
  · exact B703147
  · exact B703151
  · exact B703155
  · exact B703159
  · exact B703163
  · exact B703167
  · exact B703171
  · exact B703175
  · exact B703179
  · exact B703183
  · exact B703187
  · exact B703191
  · exact B703195
  · exact B703199
  · exact B703203
  · exact B703207
  · exact B703211
  · exact B703215
  · exact B703219
  · exact B703223
  · exact B703227
  · exact B703231
  · exact B703235
  · exact B703239
  · exact B703243
  · exact B703247
  · exact B703251
  · exact B703255
  · exact B703259
  · exact B703263
  · exact B703267
  · exact B703271
  · exact B703275
  · exact B703279
  · exact B703283
  · exact B703287
  · exact B703291
  · exact B703295
  · exact B703299
  · exact B703303
  · exact B703307
  · exact B703311
  · exact B703315
  · exact B703319
  · exact B703323
  · exact B703327
  · exact B703331
  · exact B703335
  · exact B703339
  · exact B703343
  · exact B703347
  · exact B703351
  · exact B703355
  · exact B703359
  · exact B703363
  · exact B703367
  · exact B703371
  · exact B703375
  · exact B703379
  · exact B703383
  · exact B703387
  · exact B703391
  · exact B703395
  · exact B703399
  · exact B703403
  · exact B703407
  · exact B703411
  · exact B703415
  · exact B703419
  · exact B703423
  · exact B703427
  · exact B703431
  · exact B703435
  · exact B703439
  · exact B703443
  · exact B703447
  · exact B703451
  · exact B703455
  · exact B703459
  · exact B703463
  · exact B703467
  · exact B703471
  · exact B703475
  · exact B703479
  · exact B703483
  · exact B703487
  · exact B703491
  · exact B703495
  · exact B703499
  · exact B703503
  · exact B703507
  · exact B703511
  · exact B703515
  · exact B703519
  · exact B703523
  · exact B703527
  · exact B703531
  · exact B703535
  · exact B703539
  · exact B703543
  · exact B703547
  · exact B703551
  · exact B703555
  · exact B703559
  · exact B703563
  · exact B703567
  · exact B703571
  · exact B703575
  · exact B703579
  · exact B703583
  · exact B703587
  · exact B703591
  · exact B703595
  · exact B703599
  · exact B703603
  · exact B703607
  · exact B703611
  · exact B703615
  · exact B703619
  · exact B703623
  · exact B703627
  · exact B703631
  · exact B703635
  · exact B703639
  · exact B703643
  · exact B703647
  · exact B703651
  · exact B703655
  · exact B703659
  · exact B703663
  · exact B703667
  · exact B703671
  · exact B703675
  · exact B703679
  · exact B703683
  · exact B703687
  · exact B703691
  · exact B703695
  · exact B703699
  · exact B703703
  · exact B703707
  · exact B703711
  · exact B703715
  · exact B703719
  · exact B703723
  · exact B703727
  · exact B703731
  · exact B703735
  · exact B703739
  · exact B703743
  · exact B703747
  · exact B703751
  · exact B703755
  · exact B703759
  · exact B703763
  · exact B703767
  · exact B703771
  · exact B703775
  · exact B703779
  · exact B703783
  · exact B703787
  · exact B703791
  · exact B703795
  · exact B703799
  · exact B703803
  · exact B703807
  · exact B703811
  · exact B703815
  · exact B703819
  · exact B703823
  · exact B703827
  · exact B703831
  · exact B703835
  · exact B703839
  · exact B703843
  · exact B703847
  · exact B703851
  · exact B703855
  · exact B703859
  · exact B703863
  · exact B703867
  · exact B703871
  · exact B703875
  · exact B703879
  · exact B703883
  · exact B703887
  · exact B703891
  · exact B703895
  · exact B703899
  · exact B703903
  · exact B703907
  · exact B703911
  · exact B703915
  · exact B703919
  · exact B703923
  · exact B703927
  · exact B703931
  · exact B703935
  · exact B703939
  · exact B703943
  · exact B703947
  · exact B703951
  · exact B703955
  · exact B703959
  · exact B703963
  · exact B703967
  · exact B703971
  · exact B703975
  · exact B703979
  · exact B703983
  · exact B703987
  · exact B703991
  · exact B703995
  · exact B703999
  · exact B704003
  · exact B704007
  · exact B704011
  · exact B704015
  · exact B704019
  · exact B704023
  · exact B704027
  · exact B704031
  · exact B704035
  · exact B704039
  · exact B704043
  · exact B704047
  · exact B704051
  · exact B704055
  · exact B704059
  · exact B704063
  · exact B704067
  · exact B704071
  · exact B704075
  · exact B704079
  · exact B704083
  · exact B704087
  · exact B704091
  · exact B704095
  · exact B704099
  · exact B704103
  · exact B704107
  · exact B704111
  · exact B704115
  · exact B704119
  · exact B704123
  · exact B704127
  · exact B704131
  · exact B704135
  · exact B704139
  · exact B704143
  · exact B704147
  · exact B704151
  · exact B704155
  · exact B704159
  · exact B704163
  · exact B704167
  · exact B704171
  · exact B704175
  · exact B704179
  · exact B704183
  · exact B704187
  · exact B704191
  · exact B704195
  · exact B704199
  · exact B704203
  · exact B704207
  · exact B704211
  · exact B704215
  · exact B704219
  · exact B704223
  · exact B704227
  · exact B704231
  · exact B704235
  · exact B704239
  · exact B704243
  · exact B704247
  · exact B704251
  · exact B704255
  · exact B704259
  · exact B704263
  · exact B704267
  · exact B704271
  · exact B704275
  · exact B704279
  · exact B704283
  · exact B704287
  · exact B704291
  · exact B704295
  · exact B704299
  · exact B704303
  · exact B704307
  · exact B704311
  · exact B704315
  · exact B704319
  · exact B704323
  · exact B704327
  · exact B704331
  · exact B704335
  · exact B704339
  · exact B704343
  · exact B704347
  · exact B704351
  · exact B704355
  · exact B704359
  · exact B704363
  · exact B704367
  · exact B704371
  · exact B704375
  · exact B704379
  · exact B704383
  · exact B704387
  · exact B704391
  · exact B704395
  · exact B704399
  · exact B704403
  · exact B704407
  · exact B704411
  · exact B704415
  · exact B704419
  · exact B704423
  · exact B704427
  · exact B704431
  · exact B704435
  · exact B704439
  · exact B704443
  · exact B704447
  · exact B704451
  · exact B704455
  · exact B704459
  · exact B704463
  · exact B704467
  · exact B704471
  · exact B704475
  · exact B704479
  · exact B704483
  · exact B704487
  · exact B704491
  · exact B704495
  · exact B704499
  · exact B704503
  · exact B704507
  · exact B704511
  · exact B704515
  · exact B704519
  · exact B704523
  · exact B704527
  · exact B704531
  · exact B704535
  · exact B704539
  · exact B704543
  · exact B704547
  · exact B704551
  · exact B704555
  · exact B704559
  · exact B704563
  · exact B704567
  · exact B704571
  · exact B704575
  · exact B704579
  · exact B704583
  · exact B704587
  · exact B704591
  · exact B704595
  · exact B704599
  · exact B704603
  · exact B704607
  · exact B704611
  · exact B704615
  · exact B704619
  · exact B704623
  · exact B704627
  · exact B704631
  · exact B704635
  · exact B704639
  · exact B704643
  · exact B704647
  · exact B704651
  · exact B704655
  · exact B704659
  · exact B704663
  · exact B704667
  · exact B704671
  · exact B704675
  · exact B704679
  · exact B704683
  · exact B704687
  · exact B704691
  · exact B704695
  · exact B704699
  · exact B704703
  · exact B704707
  · exact B704711
  · exact B704715
  · exact B704719
  · exact B704723
  · exact B704727
  · exact B704731
  · exact B704735
  · exact B704739
  · exact B704743
  · exact B704747
  · exact B704751
  · exact B704755
  · exact B704759
  · exact B704763
  · exact B704767
  · exact B704771
  · exact B704775
  · exact B704779
  · exact B704783
  · exact B704787
  · exact B704791
  · exact B704795
  · exact B704799
  · exact B704803
  · exact B704807
  · exact B704811
  · exact B704815
  · exact B704819
  · exact B704823
  · exact B704827
  · exact B704831
  · exact B704835
  · exact B704839
  · exact B704843
  · exact B704847
  · exact B704851
  · exact B704855
  · exact B704859
  · exact B704863
  · exact B704867
  · exact B704871
  · exact B704875
  · exact B704879
  · exact B704883
  · exact B704887
  · exact B704891
  · exact B704895
  · exact B704899
  · exact B704903
  · exact B704907
  · exact B704911
  · exact B704915
  · exact B704919
  · exact B704923
  · exact B704927
  · exact B704931
  · exact B704935
  · exact B704939
  · exact B704943
  · exact B704947
  · exact B704951
  · exact B704955
  · exact B704959
  · exact B704963
  · exact B704967
  · exact B704971
  · exact B704975
  · exact B704979
  · exact B704983
  · exact B704987
  · exact B704991
  · exact B704995
  · exact B704999
  · exact B705003
  · exact B705007
  · exact B705011
  · exact B705015
  · exact B705019
  · exact B705023
  · exact B705027
  · exact B705031
  · exact B705035
  · exact B705039
  · exact B705043
  · exact B705047
  · exact B705051
  · exact B705055
  · exact B705059
  · exact B705063
  · exact B705067
  · exact B705071
  · exact B705075
  · exact B705079
  · exact B705083
  · exact B705087
  · exact B705091
  · exact B705095
  · exact B705099
  · exact B705103
  · exact B705107
  · exact B705111
  · exact B705115

theorem C1 (j : ℕ) (h1 : 176279 ≤ j) (h2 : j ≤ 176578) : Blo 702318 (4 * j + 3) := by
  interval_cases j
  · exact B705119
  · exact B705123
  · exact B705127
  · exact B705131
  · exact B705135
  · exact B705139
  · exact B705143
  · exact B705147
  · exact B705151
  · exact B705155
  · exact B705159
  · exact B705163
  · exact B705167
  · exact B705171
  · exact B705175
  · exact B705179
  · exact B705183
  · exact B705187
  · exact B705191
  · exact B705195
  · exact B705199
  · exact B705203
  · exact B705207
  · exact B705211
  · exact B705215
  · exact B705219
  · exact B705223
  · exact B705227
  · exact B705231
  · exact B705235
  · exact B705239
  · exact B705243
  · exact B705247
  · exact B705251
  · exact B705255
  · exact B705259
  · exact B705263
  · exact B705267
  · exact B705271
  · exact B705275
  · exact B705279
  · exact B705283
  · exact B705287
  · exact B705291
  · exact B705295
  · exact B705299
  · exact B705303
  · exact B705307
  · exact B705311
  · exact B705315
  · exact B705319
  · exact B705323
  · exact B705327
  · exact B705331
  · exact B705335
  · exact B705339
  · exact B705343
  · exact B705347
  · exact B705351
  · exact B705355
  · exact B705359
  · exact B705363
  · exact B705367
  · exact B705371
  · exact B705375
  · exact B705379
  · exact B705383
  · exact B705387
  · exact B705391
  · exact B705395
  · exact B705399
  · exact B705403
  · exact B705407
  · exact B705411
  · exact B705415
  · exact B705419
  · exact B705423
  · exact B705427
  · exact B705431
  · exact B705435
  · exact B705439
  · exact B705443
  · exact B705447
  · exact B705451
  · exact B705455
  · exact B705459
  · exact B705463
  · exact B705467
  · exact B705471
  · exact B705475
  · exact B705479
  · exact B705483
  · exact B705487
  · exact B705491
  · exact B705495
  · exact B705499
  · exact B705503
  · exact B705507
  · exact B705511
  · exact B705515
  · exact B705519
  · exact B705523
  · exact B705527
  · exact B705531
  · exact B705535
  · exact B705539
  · exact B705543
  · exact B705547
  · exact B705551
  · exact B705555
  · exact B705559
  · exact B705563
  · exact B705567
  · exact B705571
  · exact B705575
  · exact B705579
  · exact B705583
  · exact B705587
  · exact B705591
  · exact B705595
  · exact B705599
  · exact B705603
  · exact B705607
  · exact B705611
  · exact B705615
  · exact B705619
  · exact B705623
  · exact B705627
  · exact B705631
  · exact B705635
  · exact B705639
  · exact B705643
  · exact B705647
  · exact B705651
  · exact B705655
  · exact B705659
  · exact B705663
  · exact B705667
  · exact B705671
  · exact B705675
  · exact B705679
  · exact B705683
  · exact B705687
  · exact B705691
  · exact B705695
  · exact B705699
  · exact B705703
  · exact B705707
  · exact B705711
  · exact B705715
  · exact B705719
  · exact B705723
  · exact B705727
  · exact B705731
  · exact B705735
  · exact B705739
  · exact B705743
  · exact B705747
  · exact B705751
  · exact B705755
  · exact B705759
  · exact B705763
  · exact B705767
  · exact B705771
  · exact B705775
  · exact B705779
  · exact B705783
  · exact B705787
  · exact B705791
  · exact B705795
  · exact B705799
  · exact B705803
  · exact B705807
  · exact B705811
  · exact B705815
  · exact B705819
  · exact B705823
  · exact B705827
  · exact B705831
  · exact B705835
  · exact B705839
  · exact B705843
  · exact B705847
  · exact B705851
  · exact B705855
  · exact B705859
  · exact B705863
  · exact B705867
  · exact B705871
  · exact B705875
  · exact B705879
  · exact B705883
  · exact B705887
  · exact B705891
  · exact B705895
  · exact B705899
  · exact B705903
  · exact B705907
  · exact B705911
  · exact B705915
  · exact B705919
  · exact B705923
  · exact B705927
  · exact B705931
  · exact B705935
  · exact B705939
  · exact B705943
  · exact B705947
  · exact B705951
  · exact B705955
  · exact B705959
  · exact B705963
  · exact B705967
  · exact B705971
  · exact B705975
  · exact B705979
  · exact B705983
  · exact B705987
  · exact B705991
  · exact B705995
  · exact B705999
  · exact B706003
  · exact B706007
  · exact B706011
  · exact B706015
  · exact B706019
  · exact B706023
  · exact B706027
  · exact B706031
  · exact B706035
  · exact B706039
  · exact B706043
  · exact B706047
  · exact B706051
  · exact B706055
  · exact B706059
  · exact B706063
  · exact B706067
  · exact B706071
  · exact B706075
  · exact B706079
  · exact B706083
  · exact B706087
  · exact B706091
  · exact B706095
  · exact B706099
  · exact B706103
  · exact B706107
  · exact B706111
  · exact B706115
  · exact B706119
  · exact B706123
  · exact B706127
  · exact B706131
  · exact B706135
  · exact B706139
  · exact B706143
  · exact B706147
  · exact B706151
  · exact B706155
  · exact B706159
  · exact B706163
  · exact B706167
  · exact B706171
  · exact B706175
  · exact B706179
  · exact B706183
  · exact B706187
  · exact B706191
  · exact B706195
  · exact B706199
  · exact B706203
  · exact B706207
  · exact B706211
  · exact B706215
  · exact B706219
  · exact B706223
  · exact B706227
  · exact B706231
  · exact B706235
  · exact B706239
  · exact B706243
  · exact B706247
  · exact B706251
  · exact B706255
  · exact B706259
  · exact B706263
  · exact B706267
  · exact B706271
  · exact B706275
  · exact B706279
  · exact B706283
  · exact B706287
  · exact B706291
  · exact B706295
  · exact B706299
  · exact B706303
  · exact B706307
  · exact B706311
  · exact B706315

theorem solution (m : ℕ) (hlo : 702318 ≤ m) (hhi : m ≤ 706318) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 175579 ≤ j := by omega
    have hj2 : j ≤ 176578 := by omega
    have hb : Blo 702318 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 176279 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
