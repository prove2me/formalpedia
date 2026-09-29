-- Prove2me | solution 1 for syracuse_descends_range_1468554_1470554
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:44:53.708402+00:00
-- url     : https://prove2.me/submissions/3ccd6d39-0bba-4322-be5e-681fe575d93f

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


theorem B1859593 : Blo 1468554 1859593 := bbase (se 2 (by rfl) ⟨697347, by rfl⟩ : syracuseStep 1859593 = 1394695) (by norm_num)
theorem B2203661 : Blo 1468554 2203661 := bbase (se 3 (by rfl) ⟨413186, by rfl⟩ : syracuseStep 2203661 = 826373) (by norm_num)
theorem B2203685 : Blo 1468554 2203685 := bbase (se 4 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 2203685 = 413191) (by norm_num)
theorem B2203709 : Blo 1468554 2203709 := bbase (se 3 (by rfl) ⟨413195, by rfl⟩ : syracuseStep 2203709 = 826391) (by norm_num)
theorem B4186181 : Blo 1468554 4186181 := bbase (se 4 (by rfl) ⟨392454, by rfl⟩ : syracuseStep 4186181 = 784909) (by norm_num)
theorem B2203733 : Blo 1468554 2203733 := bbase (se 8 (by rfl) ⟨12912, by rfl⟩ : syracuseStep 2203733 = 25825) (by norm_num)
theorem B1859689 : Blo 1468554 1859689 := bbase (se 2 (by rfl) ⟨697383, by rfl⟩ : syracuseStep 1859689 = 1394767) (by norm_num)
theorem B2203757 : Blo 1468554 2203757 := bbase (se 3 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 2203757 = 826409) (by norm_num)
theorem B3530861 : Blo 1468554 3530861 := bbase (se 3 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 3530861 = 1324073) (by norm_num)
theorem B2203781 : Blo 1468554 2203781 := bbase (se 4 (by rfl) ⟨206604, by rfl⟩ : syracuseStep 2203781 = 413209) (by norm_num)
theorem B8364181 : Blo 1468554 8364181 := bbase (se 6 (by rfl) ⟨196035, by rfl⟩ : syracuseStep 8364181 = 392071) (by norm_num)
theorem B9412757 : Blo 1468554 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B3719317 : Blo 1468554 3719317 := bbase (se 6 (by rfl) ⟨87171, by rfl⟩ : syracuseStep 3719317 = 174343) (by norm_num)
theorem B5578901 : Blo 1468554 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B2203805 : Blo 1468554 2203805 := bbase (se 3 (by rfl) ⟨413213, by rfl⟩ : syracuseStep 2203805 = 826427) (by norm_num)
theorem B2203829 : Blo 1468554 2203829 := bbase (se 5 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 2203829 = 206609) (by norm_num)
theorem B2203853 : Blo 1468554 2203853 := bbase (se 3 (by rfl) ⟨413222, by rfl⟩ : syracuseStep 2203853 = 826445) (by norm_num)
theorem B4956389 : Blo 1468554 4956389 := bbase (se 4 (by rfl) ⟨464661, by rfl⟩ : syracuseStep 4956389 = 929323) (by norm_num)
theorem B2203877 : Blo 1468554 2203877 := bbase (se 4 (by rfl) ⟨206613, by rfl⟩ : syracuseStep 2203877 = 413227) (by norm_num)
theorem B3350765 : Blo 1468554 3350765 := bbase (se 3 (by rfl) ⟨628268, by rfl⟩ : syracuseStep 3350765 = 1256537) (by norm_num)
theorem B2203901 : Blo 1468554 2203901 := bbase (se 3 (by rfl) ⟨413231, by rfl⟩ : syracuseStep 2203901 = 826463) (by norm_num)
theorem B3719429 : Blo 1468554 3719429 := bbase (se 4 (by rfl) ⟨348696, by rfl⟩ : syracuseStep 3719429 = 697393) (by norm_num)
theorem B2203925 : Blo 1468554 2203925 := bbase (se 6 (by rfl) ⟨51654, by rfl⟩ : syracuseStep 2203925 = 103309) (by norm_num)
theorem B1859861 : Blo 1468554 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B2203949 : Blo 1468554 2203949 := bbase (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) (by norm_num)
theorem B2203973 : Blo 1468554 2203973 := bbase (se 4 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 2203973 = 413245) (by norm_num)
theorem B1859917 : Blo 1468554 1859917 := bbase (se 3 (by rfl) ⟨348734, by rfl⟩ : syracuseStep 1859917 = 697469) (by norm_num)
theorem B2203997 : Blo 1468554 2203997 := bbase (se 3 (by rfl) ⟨413249, by rfl⟩ : syracuseStep 2203997 = 826499) (by norm_num)
theorem B2204021 : Blo 1468554 2204021 := bbase (se 5 (by rfl) ⟨103313, by rfl⟩ : syracuseStep 2204021 = 206627) (by norm_num)
theorem B2204045 : Blo 1468554 2204045 := bbase (se 3 (by rfl) ⟨413258, by rfl⟩ : syracuseStep 2204045 = 826517) (by norm_num)
theorem B3350933 : Blo 1468554 3350933 := bbase (se 6 (by rfl) ⟨78537, by rfl⟩ : syracuseStep 3350933 = 157075) (by norm_num)
theorem B2646437 : Blo 1468554 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B2204069 : Blo 1468554 2204069 := bbase (se 4 (by rfl) ⟨206631, by rfl⟩ : syracuseStep 2204069 = 413263) (by norm_num)
theorem B1860013 : Blo 1468554 1860013 := bbase (se 3 (by rfl) ⟨348752, by rfl⟩ : syracuseStep 1860013 = 697505) (by norm_num)
theorem B5579189 : Blo 1468554 5579189 := bbase (se 5 (by rfl) ⟨261524, by rfl⟩ : syracuseStep 5579189 = 523049) (by norm_num)
theorem B2204093 : Blo 1468554 2204093 := bbase (se 3 (by rfl) ⟨413267, by rfl⟩ : syracuseStep 2204093 = 826535) (by norm_num)
theorem B3531197 : Blo 1468554 3531197 := bbase (se 3 (by rfl) ⟨662099, by rfl⟩ : syracuseStep 3531197 = 1324199) (by norm_num)
theorem B3719621 : Blo 1468554 3719621 := bbase (se 4 (by rfl) ⟨348714, by rfl⟩ : syracuseStep 3719621 = 697429) (by norm_num)
theorem B2204117 : Blo 1468554 2204117 := bbase (se 7 (by rfl) ⟨25829, by rfl⟩ : syracuseStep 2204117 = 51659) (by norm_num)
theorem B1884641 : Blo 1468554 1884641 := bbase (se 2 (by rfl) ⟨706740, by rfl⟩ : syracuseStep 1884641 = 1413481) (by norm_num)
theorem B2204141 : Blo 1468554 2204141 := bbase (se 3 (by rfl) ⟨413276, by rfl⟩ : syracuseStep 2204141 = 826553) (by norm_num)
theorem B4710901 : Blo 1468554 4710901 := bbase (se 5 (by rfl) ⟨220823, by rfl⟩ : syracuseStep 4710901 = 441647) (by norm_num)
theorem B2204165 : Blo 1468554 2204165 := bbase (se 4 (by rfl) ⟨206640, by rfl⟩ : syracuseStep 2204165 = 413281) (by norm_num)
theorem B2204189 : Blo 1468554 2204189 := bbase (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) (by norm_num)
theorem B2204213 : Blo 1468554 2204213 := bbase (se 5 (by rfl) ⟨103322, by rfl⟩ : syracuseStep 2204213 = 206645) (by norm_num)
theorem B2646589 : Blo 1468554 2646589 := bbase (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) (by norm_num)
theorem B2204237 : Blo 1468554 2204237 := bbase (se 3 (by rfl) ⟨413294, by rfl⟩ : syracuseStep 2204237 = 826589) (by norm_num)
theorem B1860185 : Blo 1468554 1860185 := bbase (se 2 (by rfl) ⟨697569, by rfl⟩ : syracuseStep 1860185 = 1395139) (by norm_num)
theorem B2204261 : Blo 1468554 2204261 := bbase (se 4 (by rfl) ⟨206649, by rfl⟩ : syracuseStep 2204261 = 413299) (by norm_num)
theorem B2204285 : Blo 1468554 2204285 := bbase (se 3 (by rfl) ⟨413303, by rfl⟩ : syracuseStep 2204285 = 826607) (by norm_num)
theorem B1860241 : Blo 1468554 1860241 := bbase (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) (by norm_num)
theorem B4956821 : Blo 1468554 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B2204309 : Blo 1468554 2204309 := bbase (se 6 (by rfl) ⟨51663, by rfl⟩ : syracuseStep 2204309 = 103327) (by norm_num)
theorem B2204333 : Blo 1468554 2204333 := bbase (se 3 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 2204333 = 826625) (by norm_num)
theorem B2204357 : Blo 1468554 2204357 := bbase (se 4 (by rfl) ⟨206658, by rfl⟩ : syracuseStep 2204357 = 413317) (by norm_num)
theorem B2204381 : Blo 1468554 2204381 := bbase (se 3 (by rfl) ⟨413321, by rfl⟩ : syracuseStep 2204381 = 826643) (by norm_num)
theorem B3138277 : Blo 1468554 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B4186853 : Blo 1468554 4186853 := bbase (se 4 (by rfl) ⟨392517, by rfl⟩ : syracuseStep 4186853 = 785035) (by norm_num)
theorem B1860337 : Blo 1468554 1860337 := bbase (se 2 (by rfl) ⟨697626, by rfl⟩ : syracuseStep 1860337 = 1395253) (by norm_num)
theorem B2204405 : Blo 1468554 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B2204429 : Blo 1468554 2204429 := bbase (se 3 (by rfl) ⟨413330, by rfl⟩ : syracuseStep 2204429 = 826661) (by norm_num)
theorem B3719965 : Blo 1468554 3719965 := bbase (se 3 (by rfl) ⟨697493, by rfl⟩ : syracuseStep 3719965 = 1394987) (by norm_num)
theorem B2204453 : Blo 1468554 2204453 := bbase (se 4 (by rfl) ⟨206667, by rfl⟩ : syracuseStep 2204453 = 413335) (by norm_num)
theorem B2204477 : Blo 1468554 2204477 := bbase (se 3 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 2204477 = 826679) (by norm_num)
theorem B2204501 : Blo 1468554 2204501 := bbase (se 9 (by rfl) ⟨6458, by rfl⟩ : syracuseStep 2204501 = 12917) (by norm_num)
theorem B2204525 : Blo 1468554 2204525 := bbase (se 3 (by rfl) ⟨413348, by rfl⟩ : syracuseStep 2204525 = 826697) (by norm_num)
theorem B2204549 : Blo 1468554 2204549 := bbase (se 4 (by rfl) ⟨206676, by rfl⟩ : syracuseStep 2204549 = 413353) (by norm_num)
theorem B3720077 : Blo 1468554 3720077 := bbase (se 3 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 3720077 = 1395029) (by norm_num)
theorem B2204573 : Blo 1468554 2204573 := bbase (se 3 (by rfl) ⟨413357, by rfl⟩ : syracuseStep 2204573 = 826715) (by norm_num)
theorem B1860509 : Blo 1468554 1860509 := bbase (se 3 (by rfl) ⟨348845, by rfl⟩ : syracuseStep 1860509 = 697691) (by norm_num)
theorem B2204597 : Blo 1468554 2204597 := bbase (se 5 (by rfl) ⟨103340, by rfl⟩ : syracuseStep 2204597 = 206681) (by norm_num)
theorem B2204621 : Blo 1468554 2204621 := bbase (se 3 (by rfl) ⟨413366, by rfl⟩ : syracuseStep 2204621 = 826733) (by norm_num)
theorem B1860565 : Blo 1468554 1860565 := bbase (se 7 (by rfl) ⟨21803, by rfl⟩ : syracuseStep 1860565 = 43607) (by norm_num)
theorem B2204645 : Blo 1468554 2204645 := bbase (se 4 (by rfl) ⟨206685, by rfl⟩ : syracuseStep 2204645 = 413371) (by norm_num)
theorem B2204669 : Blo 1468554 2204669 := bbase (se 3 (by rfl) ⟨413375, by rfl⟩ : syracuseStep 2204669 = 826751) (by norm_num)
theorem B2204693 : Blo 1468554 2204693 := bbase (se 6 (by rfl) ⟨51672, by rfl⟩ : syracuseStep 2204693 = 103345) (by norm_num)
theorem B2204717 : Blo 1468554 2204717 := bbase (se 3 (by rfl) ⟨413384, by rfl⟩ : syracuseStep 2204717 = 826769) (by norm_num)
theorem B1860661 : Blo 1468554 1860661 := bbase (se 5 (by rfl) ⟨87218, by rfl⟩ : syracuseStep 1860661 = 174437) (by norm_num)
theorem B4957253 : Blo 1468554 4957253 := bbase (se 4 (by rfl) ⟨464742, by rfl⟩ : syracuseStep 4957253 = 929485) (by norm_num)
theorem B2204741 : Blo 1468554 2204741 := bbase (se 4 (by rfl) ⟨206694, by rfl⟩ : syracuseStep 2204741 = 413389) (by norm_num)
theorem B3720269 : Blo 1468554 3720269 := bbase (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) (by norm_num)
theorem B2204765 : Blo 1468554 2204765 := bbase (se 3 (by rfl) ⟨413393, by rfl⟩ : syracuseStep 2204765 = 826787) (by norm_num)
theorem B2204789 : Blo 1468554 2204789 := bbase (se 5 (by rfl) ⟨103349, by rfl⟩ : syracuseStep 2204789 = 206699) (by norm_num)
theorem B2204813 : Blo 1468554 2204813 := bbase (se 3 (by rfl) ⟨413402, by rfl⟩ : syracuseStep 2204813 = 826805) (by norm_num)
theorem B4187285 : Blo 1468554 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B7439525 : Blo 1468554 7439525 := bbase (se 4 (by rfl) ⟨697455, by rfl⟩ : syracuseStep 7439525 = 1394911) (by norm_num)
theorem B2204837 : Blo 1468554 2204837 := bbase (se 4 (by rfl) ⟨206703, by rfl⟩ : syracuseStep 2204837 = 413407) (by norm_num)
theorem B2204861 : Blo 1468554 2204861 := bbase (se 3 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 2204861 = 826823) (by norm_num)
theorem B2204885 : Blo 1468554 2204885 := bbase (se 7 (by rfl) ⟨25838, by rfl⟩ : syracuseStep 2204885 = 51677) (by norm_num)
theorem B1860833 : Blo 1468554 1860833 := bbase (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) (by norm_num)
theorem B2204909 : Blo 1468554 2204909 := bbase (se 3 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 2204909 = 826841) (by norm_num)
theorem B2204933 : Blo 1468554 2204933 := bbase (se 4 (by rfl) ⟨206712, by rfl⟩ : syracuseStep 2204933 = 413425) (by norm_num)
theorem B1860889 : Blo 1468554 1860889 := bbase (se 2 (by rfl) ⟨697833, by rfl⟩ : syracuseStep 1860889 = 1395667) (by norm_num)
theorem B2204957 : Blo 1468554 2204957 := bbase (se 3 (by rfl) ⟨413429, by rfl⟩ : syracuseStep 2204957 = 826859) (by norm_num)
theorem B2204981 : Blo 1468554 2204981 := bbase (se 5 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 2204981 = 206717) (by norm_num)
theorem B2205005 : Blo 1468554 2205005 := bbase (se 3 (by rfl) ⟨413438, by rfl⟩ : syracuseStep 2205005 = 826877) (by norm_num)
theorem B3769685 : Blo 1468554 3769685 := bbase (se 12 (by rfl) ⟨1380, by rfl⟩ : syracuseStep 3769685 = 2761) (by norm_num)
theorem B2205029 : Blo 1468554 2205029 := bbase (se 4 (by rfl) ⟨206721, by rfl⟩ : syracuseStep 2205029 = 413443) (by norm_num)
theorem B3974501 : Blo 1468554 3974501 := bbase (se 4 (by rfl) ⟨372609, by rfl⟩ : syracuseStep 3974501 = 745219) (by norm_num)
theorem B3351925 : Blo 1468554 3351925 := bbase (se 5 (by rfl) ⟨157121, by rfl⟩ : syracuseStep 3351925 = 314243) (by norm_num)
theorem B1860985 : Blo 1468554 1860985 := bbase (se 2 (by rfl) ⟨697869, by rfl⟩ : syracuseStep 1860985 = 1395739) (by norm_num)
theorem B2205053 : Blo 1468554 2205053 := bbase (se 3 (by rfl) ⟨413447, by rfl⟩ : syracuseStep 2205053 = 826895) (by norm_num)
theorem B2205077 : Blo 1468554 2205077 := bbase (se 6 (by rfl) ⟨51681, by rfl⟩ : syracuseStep 2205077 = 103363) (by norm_num)
theorem B3720613 : Blo 1468554 3720613 := bbase (se 4 (by rfl) ⟨348807, by rfl⟩ : syracuseStep 3720613 = 697615) (by norm_num)
theorem B2205101 : Blo 1468554 2205101 := bbase (se 3 (by rfl) ⟨413456, by rfl⟩ : syracuseStep 2205101 = 826913) (by norm_num)
theorem B6038981 : Blo 1468554 6038981 := bbase (se 4 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 6038981 = 1132309) (by norm_num)
theorem B2205125 : Blo 1468554 2205125 := bbase (se 4 (by rfl) ⟨206730, by rfl⟩ : syracuseStep 2205125 = 413461) (by norm_num)
theorem B2205149 : Blo 1468554 2205149 := bbase (se 3 (by rfl) ⟨413465, by rfl⟩ : syracuseStep 2205149 = 826931) (by norm_num)
theorem B3532253 : Blo 1468554 3532253 := bbase (se 3 (by rfl) ⟨662297, by rfl⟩ : syracuseStep 3532253 = 1324595) (by norm_num)
theorem B4957685 : Blo 1468554 4957685 := bbase (se 5 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 4957685 = 464783) (by norm_num)
theorem B2205173 : Blo 1468554 2205173 := bbase (se 5 (by rfl) ⟨103367, by rfl⟩ : syracuseStep 2205173 = 206735) (by norm_num)
theorem B2205197 : Blo 1468554 2205197 := bbase (se 3 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 2205197 = 826949) (by norm_num)
theorem B3720725 : Blo 1468554 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B2205221 : Blo 1468554 2205221 := bbase (se 4 (by rfl) ⟨206739, by rfl⟩ : syracuseStep 2205221 = 413479) (by norm_num)
theorem B1861157 : Blo 1468554 1861157 := bbase (se 4 (by rfl) ⟨174483, by rfl⟩ : syracuseStep 1861157 = 348967) (by norm_num)
theorem B2205245 : Blo 1468554 2205245 := bbase (se 3 (by rfl) ⟨413483, by rfl⟩ : syracuseStep 2205245 = 826967) (by norm_num)
theorem B5580373 : Blo 1468554 5580373 := bbase (se 8 (by rfl) ⟨32697, by rfl⟩ : syracuseStep 5580373 = 65395) (by norm_num)
theorem B2205269 : Blo 1468554 2205269 := bbase (se 8 (by rfl) ⟨12921, by rfl⟩ : syracuseStep 2205269 = 25843) (by norm_num)
theorem B3139165 : Blo 1468554 3139165 := bbase (se 3 (by rfl) ⟨588593, by rfl⟩ : syracuseStep 3139165 = 1177187) (by norm_num)
theorem B2205293 : Blo 1468554 2205293 := bbase (se 3 (by rfl) ⟨413492, by rfl⟩ : syracuseStep 2205293 = 826985) (by norm_num)
theorem B2205317 : Blo 1468554 2205317 := bbase (se 4 (by rfl) ⟨206748, by rfl⟩ : syracuseStep 2205317 = 413497) (by norm_num)
theorem B1885853 : Blo 1468554 1885853 := bbase (se 3 (by rfl) ⟨353597, by rfl⟩ : syracuseStep 1885853 = 707195) (by norm_num)
theorem B2205341 : Blo 1468554 2205341 := bbase (se 3 (by rfl) ⟨413501, by rfl⟩ : syracuseStep 2205341 = 827003) (by norm_num)
theorem B2205365 : Blo 1468554 2205365 := bbase (se 5 (by rfl) ⟨103376, by rfl⟩ : syracuseStep 2205365 = 206753) (by norm_num)
theorem B2205389 : Blo 1468554 2205389 := bbase (se 3 (by rfl) ⟨413510, by rfl⟩ : syracuseStep 2205389 = 827021) (by norm_num)
theorem B3720917 : Blo 1468554 3720917 := bbase (se 7 (by rfl) ⟨43604, by rfl⟩ : syracuseStep 3720917 = 87209) (by norm_num)
theorem B2205413 : Blo 1468554 2205413 := bbase (se 4 (by rfl) ⟨206757, by rfl⟩ : syracuseStep 2205413 = 413515) (by norm_num)
theorem B2205437 : Blo 1468554 2205437 := bbase (se 3 (by rfl) ⟨413519, by rfl⟩ : syracuseStep 2205437 = 827039) (by norm_num)
theorem B2352901 : Blo 1468554 2352901 := bbase (se 4 (by rfl) ⟨220584, by rfl⟩ : syracuseStep 2352901 = 441169) (by norm_num)
theorem B2205461 : Blo 1468554 2205461 := bbase (se 6 (by rfl) ⟨51690, by rfl⟩ : syracuseStep 2205461 = 103381) (by norm_num)
theorem B3974933 : Blo 1468554 3974933 := bbase (se 6 (by rfl) ⟨93162, by rfl⟩ : syracuseStep 3974933 = 186325) (by norm_num)
theorem B2205485 : Blo 1468554 2205485 := bbase (se 3 (by rfl) ⟨413528, by rfl⟩ : syracuseStep 2205485 = 827057) (by norm_num)
theorem B2205509 : Blo 1468554 2205509 := bbase (se 4 (by rfl) ⟨206766, by rfl⟩ : syracuseStep 2205509 = 413533) (by norm_num)
theorem B2205533 : Blo 1468554 2205533 := bbase (se 3 (by rfl) ⟨413537, by rfl⟩ : syracuseStep 2205533 = 827075) (by norm_num)
theorem B2205557 : Blo 1468554 2205557 := bbase (se 5 (by rfl) ⟨103385, by rfl⟩ : syracuseStep 2205557 = 206771) (by norm_num)
theorem B5580677 : Blo 1468554 5580677 := bbase (se 4 (by rfl) ⟨523188, by rfl⟩ : syracuseStep 5580677 = 1046377) (by norm_num)
theorem B2205581 : Blo 1468554 2205581 := bbase (se 3 (by rfl) ⟨413546, by rfl⟩ : syracuseStep 2205581 = 827093) (by norm_num)
theorem B4958117 : Blo 1468554 4958117 := bbase (se 4 (by rfl) ⟨464823, by rfl⟩ : syracuseStep 4958117 = 929647) (by norm_num)
theorem B2205605 : Blo 1468554 2205605 := bbase (se 4 (by rfl) ⟨206775, by rfl⟩ : syracuseStep 2205605 = 413551) (by norm_num)
theorem B2205629 : Blo 1468554 2205629 := bbase (se 3 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 2205629 = 827111) (by norm_num)
theorem B14125013 : Blo 1468554 14125013 := bbase (se 7 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 14125013 = 331055) (by norm_num)
theorem B2205653 : Blo 1468554 2205653 := bbase (se 7 (by rfl) ⟨25847, by rfl⟩ : syracuseStep 2205653 = 51695) (by norm_num)
theorem B2205677 : Blo 1468554 2205677 := bbase (se 3 (by rfl) ⟨413564, by rfl⟩ : syracuseStep 2205677 = 827129) (by norm_num)
theorem B2205701 : Blo 1468554 2205701 := bbase (se 4 (by rfl) ⟨206784, by rfl⟩ : syracuseStep 2205701 = 413569) (by norm_num)
theorem B2828317 : Blo 1468554 2828317 := bbase (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) (by norm_num)
theorem B2205725 : Blo 1468554 2205725 := bbase (se 3 (by rfl) ⟨413573, by rfl⟩ : syracuseStep 2205725 = 827147) (by norm_num)
theorem B3721261 : Blo 1468554 3721261 := bbase (se 3 (by rfl) ⟨697736, by rfl⟩ : syracuseStep 3721261 = 1395473) (by norm_num)
theorem B2205749 : Blo 1468554 2205749 := bbase (se 5 (by rfl) ⟨103394, by rfl⟩ : syracuseStep 2205749 = 206789) (by norm_num)
theorem B3139661 : Blo 1468554 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B2205773 : Blo 1468554 2205773 := bbase (se 3 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 2205773 = 827165) (by norm_num)
theorem B8366165 : Blo 1468554 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B2205797 : Blo 1468554 2205797 := bbase (se 4 (by rfl) ⟨206793, by rfl⟩ : syracuseStep 2205797 = 413587) (by norm_num)
theorem B2205821 : Blo 1468554 2205821 := bbase (se 3 (by rfl) ⟨413591, by rfl⟩ : syracuseStep 2205821 = 827183) (by norm_num)
theorem B3721373 : Blo 1468554 3721373 := bbase (se 3 (by rfl) ⟨697757, by rfl⟩ : syracuseStep 3721373 = 1395515) (by norm_num)
theorem B2091205 : Blo 1468554 2091205 := bbase (se 4 (by rfl) ⟨196050, by rfl⟩ : syracuseStep 2091205 = 392101) (by norm_num)
theorem B2648261 : Blo 1468554 2648261 := bbase (se 4 (by rfl) ⟨248274, by rfl⟩ : syracuseStep 2648261 = 496549) (by norm_num)
theorem B4958549 : Blo 1468554 4958549 := bbase (se 10 (by rfl) ⟨7263, by rfl⟩ : syracuseStep 4958549 = 14527) (by norm_num)
theorem B3721565 : Blo 1468554 3721565 := bbase (se 3 (by rfl) ⟨697793, by rfl⟩ : syracuseStep 3721565 = 1395587) (by norm_num)
theorem B7440821 : Blo 1468554 7440821 := bbase (se 5 (by rfl) ⟨348788, by rfl⟩ : syracuseStep 7440821 = 697577) (by norm_num)
theorem B9054773 : Blo 1468554 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B3353165 : Blo 1468554 3353165 := bbase (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) (by norm_num)
theorem B11922005 : Blo 1468554 11922005 := bbase (se 8 (by rfl) ⟨69855, by rfl⟩ : syracuseStep 11922005 = 139711) (by norm_num)
theorem B4360837 : Blo 1468554 4360837 := bbase (se 4 (by rfl) ⟨408828, by rfl⟩ : syracuseStep 4360837 = 817657) (by norm_num)
theorem B3721909 : Blo 1468554 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B4958981 : Blo 1468554 4958981 := bbase (se 4 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 4958981 = 929809) (by norm_num)
theorem B2296613 : Blo 1468554 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B3722021 : Blo 1468554 3722021 := bbase (se 4 (by rfl) ⟨348939, by rfl⟩ : syracuseStep 3722021 = 697879) (by norm_num)
theorem B10734389 : Blo 1468554 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B3304277 : Blo 1468554 3304277 := bbase (se 9 (by rfl) ⟨9680, by rfl⟩ : syracuseStep 3304277 = 19361) (by norm_num)
theorem B5024645 : Blo 1468554 5024645 := bbase (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) (by norm_num)
theorem B3304349 : Blo 1468554 3304349 := bbase (se 3 (by rfl) ⟨619565, by rfl⟩ : syracuseStep 3304349 = 1239131) (by norm_num)
theorem B2354093 : Blo 1468554 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B3140525 : Blo 1468554 3140525 := bbase (se 3 (by rfl) ⟨588848, by rfl⟩ : syracuseStep 3140525 = 1177697) (by norm_num)
theorem B4025285 : Blo 1468554 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B2091997 : Blo 1468554 2091997 := bbase (se 3 (by rfl) ⟨392249, by rfl⟩ : syracuseStep 2091997 = 784499) (by norm_num)
theorem B3304421 : Blo 1468554 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B1985509 : Blo 1468554 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B3722213 : Blo 1468554 3722213 := bbase (se 4 (by rfl) ⟨348957, by rfl⟩ : syracuseStep 3722213 = 697915) (by norm_num)
theorem B2788357 : Blo 1468554 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B29010965 : Blo 1468554 29010965 := bbase (se 6 (by rfl) ⟨679944, by rfl⟩ : syracuseStep 29010965 = 1359889) (by norm_num)
theorem B3304493 : Blo 1468554 3304493 := bbase (se 3 (by rfl) ⟨619592, by rfl⟩ : syracuseStep 3304493 = 1239185) (by norm_num)
theorem B3140669 : Blo 1468554 3140669 := bbase (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) (by norm_num)
theorem B3771461 : Blo 1468554 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B2354285 : Blo 1468554 2354285 := bbase (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) (by norm_num)
theorem B3304565 : Blo 1468554 3304565 := bbase (se 5 (by rfl) ⟨154901, by rfl⟩ : syracuseStep 3304565 = 309803) (by norm_num)
theorem B2788501 : Blo 1468554 2788501 := bbase (se 6 (by rfl) ⟨65355, by rfl⟩ : syracuseStep 2788501 = 130711) (by norm_num)
theorem B4959413 : Blo 1468554 4959413 := bbase (se 5 (by rfl) ⟨232472, by rfl⟩ : syracuseStep 4959413 = 464945) (by norm_num)
theorem B3304637 : Blo 1468554 3304637 := bbase (se 3 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 3304637 = 1239239) (by norm_num)
theorem B1985725 : Blo 1468554 1985725 := bbase (se 3 (by rfl) ⟨372323, by rfl⟩ : syracuseStep 1985725 = 744647) (by norm_num)
theorem B2649277 : Blo 1468554 2649277 := bbase (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) (by norm_num)
theorem B3181781 : Blo 1468554 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B1764589 : Blo 1468554 1764589 := bbase (se 3 (by rfl) ⟨330860, by rfl⟩ : syracuseStep 1764589 = 661721) (by norm_num)
theorem B3304709 : Blo 1468554 3304709 := bbase (se 4 (by rfl) ⟨309816, by rfl⟩ : syracuseStep 3304709 = 619633) (by norm_num)
theorem B10595605 : Blo 1468554 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B2092333 : Blo 1468554 2092333 := bbase (se 3 (by rfl) ⟨392312, by rfl⟩ : syracuseStep 2092333 = 784625) (by norm_num)
theorem B2788661 : Blo 1468554 2788661 := bbase (se 5 (by rfl) ⟨130718, by rfl⟩ : syracuseStep 2788661 = 261437) (by norm_num)
theorem B3304781 : Blo 1468554 3304781 := bbase (se 3 (by rfl) ⟨619646, by rfl⟩ : syracuseStep 3304781 = 1239293) (by norm_num)
theorem B1764685 : Blo 1468554 1764685 := bbase (se 3 (by rfl) ⟨330878, by rfl⟩ : syracuseStep 1764685 = 661757) (by norm_num)
theorem B44125525 : Blo 1468554 44125525 := bbase (se 11 (by rfl) ⟨32318, by rfl⟩ : syracuseStep 44125525 = 64637) (by norm_num)
theorem B10587509 : Blo 1468554 10587509 := bbase (se 5 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 10587509 = 992579) (by norm_num)
theorem B3304853 : Blo 1468554 3304853 := bbase (se 6 (by rfl) ⟨77457, by rfl⟩ : syracuseStep 3304853 = 154915) (by norm_num)
theorem B1912249 : Blo 1468554 1912249 := bbase (se 2 (by rfl) ⟨717093, by rfl⟩ : syracuseStep 1912249 = 1434187) (by norm_num)
theorem B1674689 : Blo 1468554 1674689 := bbase (se 2 (by rfl) ⟨628008, by rfl⟩ : syracuseStep 1674689 = 1256017) (by norm_num)
theorem B2788805 : Blo 1468554 2788805 := bbase (se 4 (by rfl) ⟨261450, by rfl⟩ : syracuseStep 2788805 = 522901) (by norm_num)
theorem B3304925 : Blo 1468554 3304925 := bbase (se 3 (by rfl) ⟨619673, by rfl⟩ : syracuseStep 3304925 = 1239347) (by norm_num)
theorem B2092549 : Blo 1468554 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B3304997 : Blo 1468554 3304997 := bbase (se 4 (by rfl) ⟨309843, by rfl⟩ : syracuseStep 3304997 = 619687) (by norm_num)
theorem B1986125 : Blo 1468554 1986125 := bbase (se 3 (by rfl) ⟨372398, by rfl⟩ : syracuseStep 1986125 = 744797) (by norm_num)
theorem B53612117 : Blo 1468554 53612117 := bbase (se 8 (by rfl) ⟨314133, by rfl⟩ : syracuseStep 53612117 = 628267) (by norm_num)
theorem B6278741 : Blo 1468554 6278741 := bbase (se 8 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 6278741 = 73579) (by norm_num)
theorem B2977373 : Blo 1468554 2977373 := bbase (se 3 (by rfl) ⟨558257, by rfl⟩ : syracuseStep 2977373 = 1116515) (by norm_num)
theorem B4959845 : Blo 1468554 4959845 := bbase (se 4 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 4959845 = 929971) (by norm_num)
theorem B3305069 : Blo 1468554 3305069 := bbase (se 3 (by rfl) ⟨619700, by rfl⟩ : syracuseStep 3305069 = 1239401) (by norm_num)
theorem B2649709 : Blo 1468554 2649709 := bbase (se 3 (by rfl) ⟨496820, by rfl⟩ : syracuseStep 2649709 = 993641) (by norm_num)
theorem B3305141 : Blo 1468554 3305141 := bbase (se 5 (by rfl) ⟨154928, by rfl⟩ : syracuseStep 3305141 = 309857) (by norm_num)
theorem B7442117 : Blo 1468554 7442117 := bbase (se 4 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 7442117 = 1395397) (by norm_num)
theorem B2789093 : Blo 1468554 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B1568489 : Blo 1468554 1568489 := bbase (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) (by norm_num)
theorem B3305213 : Blo 1468554 3305213 := bbase (se 3 (by rfl) ⟨619727, by rfl⟩ : syracuseStep 3305213 = 1239455) (by norm_num)
theorem B1675037 : Blo 1468554 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B3305285 : Blo 1468554 3305285 := bbase (se 4 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 3305285 = 619741) (by norm_num)
theorem B7065413 : Blo 1468554 7065413 := bbase (se 4 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 7065413 = 1324765) (by norm_num)
theorem B2789245 : Blo 1468554 2789245 := bbase (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) (by norm_num)
theorem B2092925 : Blo 1468554 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B3305357 : Blo 1468554 3305357 := bbase (se 3 (by rfl) ⟨619754, by rfl⟩ : syracuseStep 3305357 = 1239509) (by norm_num)
theorem B9187253 : Blo 1468554 9187253 := bbase (se 5 (by rfl) ⟨430652, by rfl⟩ : syracuseStep 9187253 = 861305) (by norm_num)
theorem B5582789 : Blo 1468554 5582789 := bbase (se 4 (by rfl) ⟨523386, by rfl⟩ : syracuseStep 5582789 = 1046773) (by norm_num)
theorem B3305429 : Blo 1468554 3305429 := bbase (se 7 (by rfl) ⟨38735, by rfl⟩ : syracuseStep 3305429 = 77471) (by norm_num)
theorem B1568737 : Blo 1468554 1568737 := bbase (se 2 (by rfl) ⟨588276, by rfl⟩ : syracuseStep 1568737 = 1176553) (by norm_num)
theorem B4181989 : Blo 1468554 4181989 := bbase (se 4 (by rfl) ⟨392061, by rfl⟩ : syracuseStep 4181989 = 784123) (by norm_num)
theorem B4960277 : Blo 1468554 4960277 := bbase (se 6 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 4960277 = 232513) (by norm_num)
theorem B3305501 : Blo 1468554 3305501 := bbase (se 3 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 3305501 = 1239563) (by norm_num)
theorem B3305573 : Blo 1468554 3305573 := bbase (se 4 (by rfl) ⟨309897, by rfl⟩ : syracuseStep 3305573 = 619795) (by norm_num)
theorem B3305645 : Blo 1468554 3305645 := bbase (se 3 (by rfl) ⟨619808, by rfl⟩ : syracuseStep 3305645 = 1239617) (by norm_num)
theorem B2789549 : Blo 1468554 2789549 := bbase (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) (by norm_num)
theorem B2478269 : Blo 1468554 2478269 := bbase (se 3 (by rfl) ⟨464675, by rfl⟩ : syracuseStep 2478269 = 929351) (by norm_num)
theorem B11473109 : Blo 1468554 11473109 := bbase (se 7 (by rfl) ⟨134450, by rfl⟩ : syracuseStep 11473109 = 268901) (by norm_num)
theorem B5583077 : Blo 1468554 5583077 := bbase (se 4 (by rfl) ⟨523413, by rfl⟩ : syracuseStep 5583077 = 1046827) (by norm_num)
theorem B3305717 : Blo 1468554 3305717 := bbase (se 5 (by rfl) ⟨154955, by rfl⟩ : syracuseStep 3305717 = 309911) (by norm_num)
theorem B8368373 : Blo 1468554 8368373 := bbase (se 5 (by rfl) ⟨392267, by rfl⟩ : syracuseStep 8368373 = 784535) (by norm_num)
theorem B1765685 : Blo 1468554 1765685 := bbase (se 5 (by rfl) ⟨82766, by rfl⟩ : syracuseStep 1765685 = 165533) (by norm_num)
theorem B2478397 : Blo 1468554 2478397 := bbase (se 3 (by rfl) ⟨464699, by rfl⟩ : syracuseStep 2478397 = 929399) (by norm_num)
theorem B3305789 : Blo 1468554 3305789 := bbase (se 3 (by rfl) ⟨619835, by rfl⟩ : syracuseStep 3305789 = 1239671) (by norm_num)
theorem B3305861 : Blo 1468554 3305861 := bbase (se 4 (by rfl) ⟨309924, by rfl⟩ : syracuseStep 3305861 = 619849) (by norm_num)
theorem B1675657 : Blo 1468554 1675657 := bbase (se 2 (by rfl) ⟨628371, by rfl⟩ : syracuseStep 1675657 = 1256743) (by norm_num)
theorem B1569169 : Blo 1468554 1569169 := bbase (se 2 (by rfl) ⟨588438, by rfl⟩ : syracuseStep 1569169 = 1176877) (by norm_num)
theorem B2478485 : Blo 1468554 2478485 := bbase (se 6 (by rfl) ⟨58089, by rfl⟩ : syracuseStep 2478485 = 116179) (by norm_num)
theorem B5296565 : Blo 1468554 5296565 := bbase (se 5 (by rfl) ⟨248276, by rfl⟩ : syracuseStep 5296565 = 496553) (by norm_num)
theorem B4960709 : Blo 1468554 4960709 := bbase (se 4 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 4960709 = 930133) (by norm_num)
theorem B3305933 : Blo 1468554 3305933 := bbase (se 3 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 3305933 = 1239725) (by norm_num)
theorem B1569241 : Blo 1468554 1569241 := bbase (se 2 (by rfl) ⟨588465, by rfl⟩ : syracuseStep 1569241 = 1176931) (by norm_num)
theorem B2478613 : Blo 1468554 2478613 := bbase (se 6 (by rfl) ⟨58092, by rfl⟩ : syracuseStep 2478613 = 116185) (by norm_num)
theorem B3306005 : Blo 1468554 3306005 := bbase (se 6 (by rfl) ⟨77484, by rfl⟩ : syracuseStep 3306005 = 154969) (by norm_num)
theorem B1765973 : Blo 1468554 1765973 := bbase (se 8 (by rfl) ⟨10347, by rfl⟩ : syracuseStep 1765973 = 20695) (by norm_num)
theorem B13414997 : Blo 1468554 13414997 := bbase (se 8 (by rfl) ⟨78603, by rfl⟩ : syracuseStep 13414997 = 157207) (by norm_num)
theorem B3306077 : Blo 1468554 3306077 := bbase (se 3 (by rfl) ⟨619889, by rfl⟩ : syracuseStep 3306077 = 1239779) (by norm_num)
theorem B2478701 : Blo 1468554 2478701 := bbase (se 3 (by rfl) ⟨464756, by rfl⟩ : syracuseStep 2478701 = 929513) (by norm_num)
theorem B3306149 : Blo 1468554 3306149 := bbase (se 4 (by rfl) ⟨309951, by rfl⟩ : syracuseStep 3306149 = 619903) (by norm_num)
theorem B2478829 : Blo 1468554 2478829 := bbase (se 3 (by rfl) ⟨464780, by rfl⟩ : syracuseStep 2478829 = 929561) (by norm_num)
theorem B3306221 : Blo 1468554 3306221 := bbase (se 3 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 3306221 = 1239833) (by norm_num)
theorem B1766137 : Blo 1468554 1766137 := bbase (se 2 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 1766137 = 1324603) (by norm_num)
theorem B1766165 : Blo 1468554 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B3306293 : Blo 1468554 3306293 := bbase (se 5 (by rfl) ⟨154982, by rfl⟩ : syracuseStep 3306293 = 309965) (by norm_num)
theorem B2478917 : Blo 1468554 2478917 := bbase (se 4 (by rfl) ⟨232398, by rfl⟩ : syracuseStep 2478917 = 464797) (by norm_num)
theorem B1569613 : Blo 1468554 1569613 := bbase (se 3 (by rfl) ⟨294302, by rfl⟩ : syracuseStep 1569613 = 588605) (by norm_num)
theorem B3969893 : Blo 1468554 3969893 := bbase (se 4 (by rfl) ⟨372177, by rfl⟩ : syracuseStep 3969893 = 744355) (by norm_num)
theorem B2978669 : Blo 1468554 2978669 := bbase (se 3 (by rfl) ⟨558500, by rfl⟩ : syracuseStep 2978669 = 1117001) (by norm_num)
theorem B4961141 : Blo 1468554 4961141 := bbase (se 5 (by rfl) ⟨232553, by rfl⟩ : syracuseStep 4961141 = 465107) (by norm_num)
theorem B3306365 : Blo 1468554 3306365 := bbase (se 3 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 3306365 = 1239887) (by norm_num)
theorem B1766281 : Blo 1468554 1766281 := bbase (se 2 (by rfl) ⟨662355, by rfl⟩ : syracuseStep 1766281 = 1324711) (by norm_num)
theorem B2790301 : Blo 1468554 2790301 := bbase (se 3 (by rfl) ⟨523181, by rfl⟩ : syracuseStep 2790301 = 1046363) (by norm_num)
theorem B2479045 : Blo 1468554 2479045 := bbase (se 4 (by rfl) ⟨232410, by rfl⟩ : syracuseStep 2479045 = 464821) (by norm_num)
theorem B3306437 : Blo 1468554 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B7443413 : Blo 1468554 7443413 := bbase (se 7 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 7443413 = 174455) (by norm_num)
theorem B1766377 : Blo 1468554 1766377 := bbase (se 2 (by rfl) ⟨662391, by rfl⟩ : syracuseStep 1766377 = 1324783) (by norm_num)
theorem B12547061 : Blo 1468554 12547061 := bbase (se 5 (by rfl) ⟨588143, by rfl⟩ : syracuseStep 12547061 = 1176287) (by norm_num)
theorem B3306509 : Blo 1468554 3306509 := bbase (se 3 (by rfl) ⟨619970, by rfl⟩ : syracuseStep 3306509 = 1239941) (by norm_num)
theorem B2479133 : Blo 1468554 2479133 := bbase (se 3 (by rfl) ⟨464837, by rfl⟩ : syracuseStep 2479133 = 929675) (by norm_num)
theorem B2790445 : Blo 1468554 2790445 := bbase (se 3 (by rfl) ⟨523208, by rfl⟩ : syracuseStep 2790445 = 1046417) (by norm_num)
theorem B4183093 : Blo 1468554 4183093 := bbase (se 5 (by rfl) ⟨196082, by rfl⟩ : syracuseStep 4183093 = 392165) (by norm_num)
theorem B3306581 : Blo 1468554 3306581 := bbase (se 8 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 3306581 = 38749) (by norm_num)
theorem B2012293 : Blo 1468554 2012293 := bbase (se 4 (by rfl) ⟨188652, by rfl⟩ : syracuseStep 2012293 = 377305) (by norm_num)
theorem B2479261 : Blo 1468554 2479261 := bbase (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) (by norm_num)
theorem B3306653 : Blo 1468554 3306653 := bbase (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) (by norm_num)
theorem B1569989 : Blo 1468554 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B2790605 : Blo 1468554 2790605 := bbase (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) (by norm_num)
theorem B3306725 : Blo 1468554 3306725 := bbase (se 4 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 3306725 = 620011) (by norm_num)
theorem B2512117 : Blo 1468554 2512117 := bbase (se 5 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 2512117 = 235511) (by norm_num)
theorem B2479349 : Blo 1468554 2479349 := bbase (se 5 (by rfl) ⟨116219, by rfl⟩ : syracuseStep 2479349 = 232439) (by norm_num)
theorem B7156997 : Blo 1468554 7156997 := bbase (se 4 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 7156997 = 1341937) (by norm_num)
theorem B1570061 : Blo 1468554 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B4961573 : Blo 1468554 4961573 := bbase (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) (by norm_num)
theorem B3306797 : Blo 1468554 3306797 := bbase (se 3 (by rfl) ⟨620024, by rfl⟩ : syracuseStep 3306797 = 1240049) (by norm_num)
theorem B3626293 : Blo 1468554 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B11162933 : Blo 1468554 11162933 := bbase (se 5 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 11162933 = 1046525) (by norm_num)
theorem B6280517 : Blo 1468554 6280517 := bbase (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) (by norm_num)
theorem B2790749 : Blo 1468554 2790749 := bbase (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) (by norm_num)
theorem B7435637 : Blo 1468554 7435637 := bbase (se 5 (by rfl) ⟨348545, by rfl⟩ : syracuseStep 7435637 = 697091) (by norm_num)
theorem B2479477 : Blo 1468554 2479477 := bbase (se 5 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 2479477 = 232451) (by norm_num)
theorem B3306869 : Blo 1468554 3306869 := bbase (se 5 (by rfl) ⟨155009, by rfl⟩ : syracuseStep 3306869 = 310019) (by norm_num)
theorem B1652125 : Blo 1468554 1652125 := bbase (se 3 (by rfl) ⟨309773, by rfl⟩ : syracuseStep 1652125 = 619547) (by norm_num)
theorem B2512309 : Blo 1468554 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B3306941 : Blo 1468554 3306941 := bbase (se 3 (by rfl) ⟨620051, by rfl⟩ : syracuseStep 3306941 = 1240103) (by norm_num)
theorem B1652161 : Blo 1468554 1652161 := bbase (se 2 (by rfl) ⟨619560, by rfl⟩ : syracuseStep 1652161 = 1239121) (by norm_num)
theorem B1570249 : Blo 1468554 1570249 := bbase (se 2 (by rfl) ⟨588843, by rfl⟩ : syracuseStep 1570249 = 1177687) (by norm_num)
theorem B2479565 : Blo 1468554 2479565 := bbase (se 3 (by rfl) ⟨464918, by rfl⟩ : syracuseStep 2479565 = 929837) (by norm_num)
theorem B1652197 : Blo 1468554 1652197 := bbase (se 4 (by rfl) ⟨154893, by rfl⟩ : syracuseStep 1652197 = 309787) (by norm_num)
theorem B3307013 : Blo 1468554 3307013 := bbase (se 4 (by rfl) ⟨310032, by rfl⟩ : syracuseStep 3307013 = 620065) (by norm_num)
theorem B1652233 : Blo 1468554 1652233 := bbase (se 2 (by rfl) ⟨619587, by rfl⟩ : syracuseStep 1652233 = 1239175) (by norm_num)
theorem B4707877 : Blo 1468554 4707877 := bbase (se 4 (by rfl) ⟨441363, by rfl⟩ : syracuseStep 4707877 = 882727) (by norm_num)
theorem B1652269 : Blo 1468554 1652269 := bbase (se 3 (by rfl) ⟨309800, by rfl⟩ : syracuseStep 1652269 = 619601) (by norm_num)
theorem B2479693 : Blo 1468554 2479693 := bbase (se 3 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 2479693 = 929885) (by norm_num)
theorem B3307085 : Blo 1468554 3307085 := bbase (se 3 (by rfl) ⟨620078, by rfl⟩ : syracuseStep 3307085 = 1240157) (by norm_num)
theorem B1652305 : Blo 1468554 1652305 := bbase (se 2 (by rfl) ⟨619614, by rfl⟩ : syracuseStep 1652305 = 1239229) (by norm_num)
theorem B1652341 : Blo 1468554 1652341 := bbase (se 5 (by rfl) ⟨77453, by rfl⟩ : syracuseStep 1652341 = 154907) (by norm_num)
theorem B2791037 : Blo 1468554 2791037 := bbase (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) (by norm_num)
theorem B3307157 : Blo 1468554 3307157 := bbase (se 6 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 3307157 = 155023) (by norm_num)
theorem B1652377 : Blo 1468554 1652377 := bbase (se 2 (by rfl) ⟨619641, by rfl⟩ : syracuseStep 1652377 = 1239283) (by norm_num)
theorem B2479781 : Blo 1468554 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B1652413 : Blo 1468554 1652413 := bbase (se 3 (by rfl) ⟨309827, by rfl⟩ : syracuseStep 1652413 = 619655) (by norm_num)
theorem B11155157 : Blo 1468554 11155157 := bbase (se 7 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 11155157 = 261449) (by norm_num)
theorem B4962005 : Blo 1468554 4962005 := bbase (se 7 (by rfl) ⟨58148, by rfl⟩ : syracuseStep 4962005 = 116297) (by norm_num)
theorem B3307229 : Blo 1468554 3307229 := bbase (se 3 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 3307229 = 1240211) (by norm_num)
theorem B1652449 : Blo 1468554 1652449 := bbase (se 2 (by rfl) ⟨619668, by rfl⟩ : syracuseStep 1652449 = 1239337) (by norm_num)
theorem B1652485 : Blo 1468554 1652485 := bbase (se 4 (by rfl) ⟨154920, by rfl⟩ : syracuseStep 1652485 = 309841) (by norm_num)
theorem B2791189 : Blo 1468554 2791189 := bbase (se 6 (by rfl) ⟨65418, by rfl⟩ : syracuseStep 2791189 = 130837) (by norm_num)
theorem B5576485 : Blo 1468554 5576485 := bbase (se 4 (by rfl) ⟨522795, by rfl⟩ : syracuseStep 5576485 = 1045591) (by norm_num)
theorem B2479909 : Blo 1468554 2479909 := bbase (se 4 (by rfl) ⟨232491, by rfl⟩ : syracuseStep 2479909 = 464983) (by norm_num)
theorem B4708133 : Blo 1468554 4708133 := bbase (se 4 (by rfl) ⟨441387, by rfl⟩ : syracuseStep 4708133 = 882775) (by norm_num)
theorem B3307301 : Blo 1468554 3307301 := bbase (se 4 (by rfl) ⟨310059, by rfl⟩ : syracuseStep 3307301 = 620119) (by norm_num)
theorem B1652521 : Blo 1468554 1652521 := bbase (se 2 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 1652521 = 1239391) (by norm_num)
theorem B1652557 : Blo 1468554 1652557 := bbase (se 3 (by rfl) ⟨309854, by rfl⟩ : syracuseStep 1652557 = 619709) (by norm_num)
theorem B3307373 : Blo 1468554 3307373 := bbase (se 3 (by rfl) ⟨620132, by rfl⟩ : syracuseStep 3307373 = 1240265) (by norm_num)
theorem B1652593 : Blo 1468554 1652593 := bbase (se 2 (by rfl) ⟨619722, by rfl⟩ : syracuseStep 1652593 = 1239445) (by norm_num)
theorem B2479997 : Blo 1468554 2479997 := bbase (se 3 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 2479997 = 929999) (by norm_num)
theorem B1652629 : Blo 1468554 1652629 := bbase (se 6 (by rfl) ⟨38733, by rfl⟩ : syracuseStep 1652629 = 77467) (by norm_num)
theorem B3307445 : Blo 1468554 3307445 := bbase (se 5 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 3307445 = 310073) (by norm_num)
theorem B1652665 : Blo 1468554 1652665 := bbase (se 2 (by rfl) ⟨619749, by rfl⟩ : syracuseStep 1652665 = 1239499) (by norm_num)
theorem B2512829 : Blo 1468554 2512829 := bbase (se 3 (by rfl) ⟨471155, by rfl⟩ : syracuseStep 2512829 = 942311) (by norm_num)
theorem B2013125 : Blo 1468554 2013125 := bbase (se 4 (by rfl) ⟨188730, by rfl⟩ : syracuseStep 2013125 = 377461) (by norm_num)
theorem B2119645 : Blo 1468554 2119645 := bbase (se 3 (by rfl) ⟨397433, by rfl⟩ : syracuseStep 2119645 = 794867) (by norm_num)
theorem B1652701 : Blo 1468554 1652701 := bbase (se 3 (by rfl) ⟨309881, by rfl⟩ : syracuseStep 1652701 = 619763) (by norm_num)
theorem B2979821 : Blo 1468554 2979821 := bbase (se 3 (by rfl) ⟨558716, by rfl⟩ : syracuseStep 2979821 = 1117433) (by norm_num)
theorem B2480125 : Blo 1468554 2480125 := bbase (se 3 (by rfl) ⟨465023, by rfl⟩ : syracuseStep 2480125 = 930047) (by norm_num)
theorem B3307517 : Blo 1468554 3307517 := bbase (se 3 (by rfl) ⟨620159, by rfl⟩ : syracuseStep 3307517 = 1240319) (by norm_num)
theorem B1652737 : Blo 1468554 1652737 := bbase (se 2 (by rfl) ⟨619776, by rfl⟩ : syracuseStep 1652737 = 1239553) (by norm_num)
theorem B1652773 : Blo 1468554 1652773 := bbase (se 4 (by rfl) ⟨154947, by rfl⟩ : syracuseStep 1652773 = 309895) (by norm_num)
theorem B3307589 : Blo 1468554 3307589 := bbase (se 4 (by rfl) ⟨310086, by rfl⟩ : syracuseStep 3307589 = 620173) (by norm_num)
theorem B2791493 : Blo 1468554 2791493 := bbase (se 4 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 2791493 = 523405) (by norm_num)
theorem B1652809 : Blo 1468554 1652809 := bbase (se 2 (by rfl) ⟨619803, by rfl⟩ : syracuseStep 1652809 = 1239607) (by norm_num)
theorem B5576789 : Blo 1468554 5576789 := bbase (se 8 (by rfl) ⟨32676, by rfl⟩ : syracuseStep 5576789 = 65353) (by norm_num)
theorem B2480213 : Blo 1468554 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B1652845 : Blo 1468554 1652845 := bbase (se 3 (by rfl) ⟨309908, by rfl⟩ : syracuseStep 1652845 = 619817) (by norm_num)
theorem B4028549 : Blo 1468554 4028549 := bbase (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) (by norm_num)
theorem B4962437 : Blo 1468554 4962437 := bbase (se 4 (by rfl) ⟨465228, by rfl⟩ : syracuseStep 4962437 = 930457) (by norm_num)
theorem B3307661 : Blo 1468554 3307661 := bbase (se 3 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 3307661 = 1240373) (by norm_num)
theorem B1652881 : Blo 1468554 1652881 := bbase (se 2 (by rfl) ⟨619830, by rfl⟩ : syracuseStep 1652881 = 1239661) (by norm_num)
theorem B1652917 : Blo 1468554 1652917 := bbase (se 5 (by rfl) ⟨77480, by rfl⟩ : syracuseStep 1652917 = 154961) (by norm_num)
theorem B2480341 : Blo 1468554 2480341 := bbase (se 7 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 2480341 = 58133) (by norm_num)
theorem B3307733 : Blo 1468554 3307733 := bbase (se 7 (by rfl) ⟨38762, by rfl⟩ : syracuseStep 3307733 = 77525) (by norm_num)
theorem B1652953 : Blo 1468554 1652953 := bbase (se 2 (by rfl) ⟨619857, by rfl⟩ : syracuseStep 1652953 = 1239715) (by norm_num)
theorem B6363365 : Blo 1468554 6363365 := bbase (se 4 (by rfl) ⟨596565, by rfl⟩ : syracuseStep 6363365 = 1193131) (by norm_num)
theorem B3717373 : Blo 1468554 3717373 := bbase (se 3 (by rfl) ⟨697007, by rfl⟩ : syracuseStep 3717373 = 1394015) (by norm_num)
theorem B1652989 : Blo 1468554 1652989 := bbase (se 3 (by rfl) ⟨309935, by rfl⟩ : syracuseStep 1652989 = 619871) (by norm_num)
theorem B3307805 : Blo 1468554 3307805 := bbase (se 3 (by rfl) ⟨620213, by rfl⟩ : syracuseStep 3307805 = 1240427) (by norm_num)
theorem B1653025 : Blo 1468554 1653025 := bbase (se 2 (by rfl) ⟨619884, by rfl⟩ : syracuseStep 1653025 = 1239769) (by norm_num)
theorem B2480429 : Blo 1468554 2480429 := bbase (se 3 (by rfl) ⟨465080, by rfl⟩ : syracuseStep 2480429 = 930161) (by norm_num)
theorem B1489213 : Blo 1468554 1489213 := bbase (se 3 (by rfl) ⟨279227, by rfl⟩ : syracuseStep 1489213 = 558455) (by norm_num)
theorem B1653061 : Blo 1468554 1653061 := bbase (se 4 (by rfl) ⟨154974, by rfl⟩ : syracuseStep 1653061 = 309949) (by norm_num)
theorem B3307877 : Blo 1468554 3307877 := bbase (se 4 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 3307877 = 620227) (by norm_num)
theorem B1653097 : Blo 1468554 1653097 := bbase (se 2 (by rfl) ⟨619911, by rfl⟩ : syracuseStep 1653097 = 1239823) (by norm_num)
theorem B3717485 : Blo 1468554 3717485 := bbase (se 3 (by rfl) ⟨697028, by rfl⟩ : syracuseStep 3717485 = 1394057) (by norm_num)
theorem B1653133 : Blo 1468554 1653133 := bbase (se 3 (by rfl) ⟨309962, by rfl⟩ : syracuseStep 1653133 = 619925) (by norm_num)
theorem B2480557 : Blo 1468554 2480557 := bbase (se 3 (by rfl) ⟨465104, by rfl⟩ : syracuseStep 2480557 = 930209) (by norm_num)
theorem B3307949 : Blo 1468554 3307949 := bbase (se 3 (by rfl) ⟨620240, by rfl⟩ : syracuseStep 3307949 = 1240481) (by norm_num)
theorem B1653169 : Blo 1468554 1653169 := bbase (se 2 (by rfl) ⟨619938, by rfl⟩ : syracuseStep 1653169 = 1239877) (by norm_num)
theorem B1653205 : Blo 1468554 1653205 := bbase (se 7 (by rfl) ⟨19373, by rfl⟩ : syracuseStep 1653205 = 38747) (by norm_num)
theorem B3308021 : Blo 1468554 3308021 := bbase (se 5 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 3308021 = 310127) (by norm_num)
theorem B1653241 : Blo 1468554 1653241 := bbase (se 2 (by rfl) ⟨619965, by rfl⟩ : syracuseStep 1653241 = 1239931) (by norm_num)
theorem B2480645 : Blo 1468554 2480645 := bbase (se 4 (by rfl) ⟨232560, by rfl⟩ : syracuseStep 2480645 = 465121) (by norm_num)
theorem B4184597 : Blo 1468554 4184597 := bbase (se 6 (by rfl) ⟨98076, by rfl⟩ : syracuseStep 4184597 = 196153) (by norm_num)
theorem B1653277 : Blo 1468554 1653277 := bbase (se 3 (by rfl) ⟨309989, by rfl⟩ : syracuseStep 1653277 = 619979) (by norm_num)
theorem B3717677 : Blo 1468554 3717677 := bbase (se 3 (by rfl) ⟨697064, by rfl⟩ : syracuseStep 3717677 = 1394129) (by norm_num)
theorem B4962869 : Blo 1468554 4962869 := bbase (se 5 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 4962869 = 465269) (by norm_num)
theorem B3308093 : Blo 1468554 3308093 := bbase (se 3 (by rfl) ⟨620267, by rfl⟩ : syracuseStep 3308093 = 1240535) (by norm_num)
theorem B1653313 : Blo 1468554 1653313 := bbase (se 2 (by rfl) ⟨619992, by rfl⟩ : syracuseStep 1653313 = 1239985) (by norm_num)
theorem B1653349 : Blo 1468554 1653349 := bbase (se 4 (by rfl) ⟨155001, by rfl⟩ : syracuseStep 1653349 = 310003) (by norm_num)
theorem B7436933 : Blo 1468554 7436933 := bbase (se 4 (by rfl) ⟨697212, by rfl⟩ : syracuseStep 7436933 = 1394425) (by norm_num)
theorem B2480773 : Blo 1468554 2480773 := bbase (se 4 (by rfl) ⟨232572, by rfl⟩ : syracuseStep 2480773 = 465145) (by norm_num)
theorem B3308165 : Blo 1468554 3308165 := bbase (se 4 (by rfl) ⟨310140, by rfl⟩ : syracuseStep 3308165 = 620281) (by norm_num)
theorem B1653385 : Blo 1468554 1653385 := bbase (se 2 (by rfl) ⟨620019, by rfl⟩ : syracuseStep 1653385 = 1240039) (by norm_num)
theorem B22928021 : Blo 1468554 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B1653421 : Blo 1468554 1653421 := bbase (se 3 (by rfl) ⟨310016, by rfl⟩ : syracuseStep 1653421 = 620033) (by norm_num)
theorem B3308237 : Blo 1468554 3308237 := bbase (se 3 (by rfl) ⟨620294, by rfl⟩ : syracuseStep 3308237 = 1240589) (by norm_num)
theorem B1653457 : Blo 1468554 1653457 := bbase (se 2 (by rfl) ⟨620046, by rfl⟩ : syracuseStep 1653457 = 1240093) (by norm_num)
theorem B2480861 : Blo 1468554 2480861 := bbase (se 3 (by rfl) ⟨465161, by rfl⟩ : syracuseStep 2480861 = 930323) (by norm_num)
theorem B1653493 : Blo 1468554 1653493 := bbase (se 5 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 1653493 = 155015) (by norm_num)
theorem B3308309 : Blo 1468554 3308309 := bbase (se 6 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 3308309 = 155077) (by norm_num)
theorem B1653529 : Blo 1468554 1653529 := bbase (se 2 (by rfl) ⟨620073, by rfl⟩ : syracuseStep 1653529 = 1240147) (by norm_num)
theorem B2013997 : Blo 1468554 2013997 := bbase (se 3 (by rfl) ⟨377624, by rfl⟩ : syracuseStep 2013997 = 755249) (by norm_num)
theorem B1653565 : Blo 1468554 1653565 := bbase (se 3 (by rfl) ⟨310043, by rfl⟩ : syracuseStep 1653565 = 620087) (by norm_num)
theorem B2480989 : Blo 1468554 2480989 := bbase (se 3 (by rfl) ⟨465185, by rfl⟩ : syracuseStep 2480989 = 930371) (by norm_num)
theorem B3308381 : Blo 1468554 3308381 := bbase (se 3 (by rfl) ⟨620321, by rfl⟩ : syracuseStep 3308381 = 1240643) (by norm_num)
theorem B1653601 : Blo 1468554 1653601 := bbase (se 2 (by rfl) ⟨620100, by rfl⟩ : syracuseStep 1653601 = 1240201) (by norm_num)
theorem B3718021 : Blo 1468554 3718021 := bbase (se 4 (by rfl) ⟨348564, by rfl⟩ : syracuseStep 3718021 = 697129) (by norm_num)
theorem B1653637 : Blo 1468554 1653637 := bbase (se 4 (by rfl) ⟨155028, by rfl⟩ : syracuseStep 1653637 = 310057) (by norm_num)
theorem B3308453 : Blo 1468554 3308453 := bbase (se 4 (by rfl) ⟨310167, by rfl⟩ : syracuseStep 3308453 = 620335) (by norm_num)
theorem B1653673 : Blo 1468554 1653673 := bbase (se 2 (by rfl) ⟨620127, by rfl⟩ : syracuseStep 1653673 = 1240255) (by norm_num)
theorem B2481077 : Blo 1468554 2481077 := bbase (se 5 (by rfl) ⟨116300, by rfl⟩ : syracuseStep 2481077 = 232601) (by norm_num)
theorem B1653709 : Blo 1468554 1653709 := bbase (se 3 (by rfl) ⟨310070, by rfl⟩ : syracuseStep 1653709 = 620141) (by norm_num)
theorem B2235365 : Blo 1468554 2235365 := bbase (se 4 (by rfl) ⟨209565, by rfl⟩ : syracuseStep 2235365 = 419131) (by norm_num)
theorem B3308525 : Blo 1468554 3308525 := bbase (se 3 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 3308525 = 1240697) (by norm_num)
theorem B1653745 : Blo 1468554 1653745 := bbase (se 2 (by rfl) ⟨620154, by rfl⟩ : syracuseStep 1653745 = 1240309) (by norm_num)
theorem B3718133 : Blo 1468554 3718133 := bbase (se 5 (by rfl) ⟨174287, by rfl⟩ : syracuseStep 3718133 = 348575) (by norm_num)
theorem B4299797 : Blo 1468554 4299797 := bbase (se 6 (by rfl) ⟨100776, by rfl⟩ : syracuseStep 4299797 = 201553) (by norm_num)
theorem B1653781 : Blo 1468554 1653781 := bbase (se 6 (by rfl) ⟨38760, by rfl⟩ : syracuseStep 1653781 = 77521) (by norm_num)
theorem B2481205 : Blo 1468554 2481205 := bbase (se 5 (by rfl) ⟨116306, by rfl⟩ : syracuseStep 2481205 = 232613) (by norm_num)
theorem B3308597 : Blo 1468554 3308597 := bbase (se 5 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 3308597 = 310181) (by norm_num)
theorem B1653817 : Blo 1468554 1653817 := bbase (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) (by norm_num)
theorem B3529813 : Blo 1468554 3529813 := bbase (se 8 (by rfl) ⟨20682, by rfl⟩ : syracuseStep 3529813 = 41365) (by norm_num)
theorem B1653853 : Blo 1468554 1653853 := bbase (se 3 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 1653853 = 620195) (by norm_num)
theorem B4299893 : Blo 1468554 4299893 := bbase (se 5 (by rfl) ⟨201557, by rfl⟩ : syracuseStep 4299893 = 403115) (by norm_num)
theorem B3136637 : Blo 1468554 3136637 := bbase (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) (by norm_num)
theorem B3308669 : Blo 1468554 3308669 := bbase (se 3 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 3308669 = 1240751) (by norm_num)
theorem B1653889 : Blo 1468554 1653889 := bbase (se 2 (by rfl) ⟨620208, by rfl⟩ : syracuseStep 1653889 = 1240417) (by norm_num)
theorem B2481293 : Blo 1468554 2481293 := bbase (se 3 (by rfl) ⟨465242, by rfl⟩ : syracuseStep 2481293 = 930485) (by norm_num)
theorem B1858717 : Blo 1468554 1858717 := bbase (se 3 (by rfl) ⟨348509, by rfl⟩ : syracuseStep 1858717 = 697019) (by norm_num)
theorem B1653925 : Blo 1468554 1653925 := bbase (se 4 (by rfl) ⟨155055, by rfl⟩ : syracuseStep 1653925 = 310111) (by norm_num)
theorem B3718325 : Blo 1468554 3718325 := bbase (se 5 (by rfl) ⟨174296, by rfl⟩ : syracuseStep 3718325 = 348593) (by norm_num)
theorem B3529909 : Blo 1468554 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B3308741 : Blo 1468554 3308741 := bbase (se 4 (by rfl) ⟨310194, by rfl⟩ : syracuseStep 3308741 = 620389) (by norm_num)
theorem B1653961 : Blo 1468554 1653961 := bbase (se 2 (by rfl) ⟨620235, by rfl⟩ : syracuseStep 1653961 = 1240471) (by norm_num)
theorem B20102357 : Blo 1468554 20102357 := bbase (se 7 (by rfl) ⟨235574, by rfl⟩ : syracuseStep 20102357 = 471149) (by norm_num)
theorem B2202845 : Blo 1468554 2202845 := bbase (se 3 (by rfl) ⟨413033, by rfl⟩ : syracuseStep 2202845 = 826067) (by norm_num)
theorem B1653997 : Blo 1468554 1653997 := bbase (se 3 (by rfl) ⟨310124, by rfl⟩ : syracuseStep 1653997 = 620249) (by norm_num)
theorem B2202869 : Blo 1468554 2202869 := bbase (se 5 (by rfl) ⟨103259, by rfl⟩ : syracuseStep 2202869 = 206519) (by norm_num)
theorem B2202893 : Blo 1468554 2202893 := bbase (se 3 (by rfl) ⟨413042, by rfl⟩ : syracuseStep 2202893 = 826085) (by norm_num)
theorem B2481421 : Blo 1468554 2481421 := bbase (se 3 (by rfl) ⟨465266, by rfl⟩ : syracuseStep 2481421 = 930533) (by norm_num)
theorem B1654033 : Blo 1468554 1654033 := bbase (se 2 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 1654033 = 1240525) (by norm_num)
theorem B2202917 : Blo 1468554 2202917 := bbase (se 4 (by rfl) ⟨206523, by rfl⟩ : syracuseStep 2202917 = 413047) (by norm_num)
theorem B1654069 : Blo 1468554 1654069 := bbase (se 5 (by rfl) ⟨77534, by rfl⟩ : syracuseStep 1654069 = 155069) (by norm_num)
theorem B2202941 : Blo 1468554 2202941 := bbase (se 3 (by rfl) ⟨413051, by rfl⟩ : syracuseStep 2202941 = 826103) (by norm_num)
theorem B1858889 : Blo 1468554 1858889 := bbase (se 2 (by rfl) ⟨697083, by rfl⟩ : syracuseStep 1858889 = 1394167) (by norm_num)
theorem B2202965 : Blo 1468554 2202965 := bbase (se 11 (by rfl) ⟨1613, by rfl⟩ : syracuseStep 2202965 = 3227) (by norm_num)
theorem B1654105 : Blo 1468554 1654105 := bbase (se 2 (by rfl) ⟨620289, by rfl⟩ : syracuseStep 1654105 = 1240579) (by norm_num)
theorem B2481509 : Blo 1468554 2481509 := bbase (se 4 (by rfl) ⟨232641, by rfl⟩ : syracuseStep 2481509 = 465283) (by norm_num)
theorem B2202989 : Blo 1468554 2202989 := bbase (se 3 (by rfl) ⟨413060, by rfl⟩ : syracuseStep 2202989 = 826121) (by norm_num)
theorem B3530101 : Blo 1468554 3530101 := bbase (se 5 (by rfl) ⟨165473, by rfl⟩ : syracuseStep 3530101 = 330947) (by norm_num)
theorem B1654141 : Blo 1468554 1654141 := bbase (se 3 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 1654141 = 620303) (by norm_num)
theorem B1858945 : Blo 1468554 1858945 := bbase (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) (by norm_num)
theorem B2203013 : Blo 1468554 2203013 := bbase (se 4 (by rfl) ⟨206532, by rfl⟩ : syracuseStep 2203013 = 413065) (by norm_num)
theorem B2203037 : Blo 1468554 2203037 := bbase (se 3 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 2203037 = 826139) (by norm_num)
theorem B1654177 : Blo 1468554 1654177 := bbase (se 2 (by rfl) ⟨620316, by rfl⟩ : syracuseStep 1654177 = 1240633) (by norm_num)
theorem B2203061 : Blo 1468554 2203061 := bbase (se 5 (by rfl) ⟨103268, by rfl⟩ : syracuseStep 2203061 = 206537) (by norm_num)
theorem B1654213 : Blo 1468554 1654213 := bbase (se 4 (by rfl) ⟨155082, by rfl⟩ : syracuseStep 1654213 = 310165) (by norm_num)
theorem B2203085 : Blo 1468554 2203085 := bbase (se 3 (by rfl) ⟨413078, by rfl⟩ : syracuseStep 2203085 = 826157) (by norm_num)
theorem B1859041 : Blo 1468554 1859041 := bbase (se 2 (by rfl) ⟨697140, by rfl⟩ : syracuseStep 1859041 = 1394281) (by norm_num)
theorem B2203109 : Blo 1468554 2203109 := bbase (se 4 (by rfl) ⟨206541, by rfl⟩ : syracuseStep 2203109 = 413083) (by norm_num)
theorem B1654249 : Blo 1468554 1654249 := bbase (se 2 (by rfl) ⟨620343, by rfl⟩ : syracuseStep 1654249 = 1240687) (by norm_num)
theorem B2203133 : Blo 1468554 2203133 := bbase (se 3 (by rfl) ⟨413087, by rfl⟩ : syracuseStep 2203133 = 826175) (by norm_num)
theorem B3718669 : Blo 1468554 3718669 := bbase (se 3 (by rfl) ⟨697250, by rfl⟩ : syracuseStep 3718669 = 1394501) (by norm_num)
theorem B1654285 : Blo 1468554 1654285 := bbase (se 3 (by rfl) ⟨310178, by rfl⟩ : syracuseStep 1654285 = 620357) (by norm_num)
theorem B2203157 : Blo 1468554 2203157 := bbase (se 6 (by rfl) ⟨51636, by rfl⟩ : syracuseStep 2203157 = 103273) (by norm_num)
theorem B28253717 : Blo 1468554 28253717 := bbase (se 6 (by rfl) ⟨662196, by rfl⟩ : syracuseStep 28253717 = 1324393) (by norm_num)
theorem B2203181 : Blo 1468554 2203181 := bbase (se 3 (by rfl) ⟨413096, by rfl⟩ : syracuseStep 2203181 = 826193) (by norm_num)
theorem B1654321 : Blo 1468554 1654321 := bbase (se 2 (by rfl) ⟨620370, by rfl⟩ : syracuseStep 1654321 = 1240741) (by norm_num)
theorem B2203205 : Blo 1468554 2203205 := bbase (se 4 (by rfl) ⟨206550, by rfl⟩ : syracuseStep 2203205 = 413101) (by norm_num)
theorem B1654357 : Blo 1468554 1654357 := bbase (se 8 (by rfl) ⟨9693, by rfl⟩ : syracuseStep 1654357 = 19387) (by norm_num)
theorem B2203229 : Blo 1468554 2203229 := bbase (se 3 (by rfl) ⟨413105, by rfl⟩ : syracuseStep 2203229 = 826211) (by norm_num)
theorem B2203253 : Blo 1468554 2203253 := bbase (se 5 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 2203253 = 206555) (by norm_num)
theorem B3718781 : Blo 1468554 3718781 := bbase (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) (by norm_num)
theorem B2203277 : Blo 1468554 2203277 := bbase (se 3 (by rfl) ⟨413114, by rfl⟩ : syracuseStep 2203277 = 826229) (by norm_num)
theorem B1859213 : Blo 1468554 1859213 := bbase (se 3 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 1859213 = 697205) (by norm_num)
theorem B6274709 : Blo 1468554 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B2514581 : Blo 1468554 2514581 := bbase (se 6 (by rfl) ⟨58935, by rfl⟩ : syracuseStep 2514581 = 117871) (by norm_num)
theorem B2203301 : Blo 1468554 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B2203325 : Blo 1468554 2203325 := bbase (se 3 (by rfl) ⟨413123, by rfl⟩ : syracuseStep 2203325 = 826247) (by norm_num)
theorem B3530429 : Blo 1468554 3530429 := bbase (se 3 (by rfl) ⟨661955, by rfl⟩ : syracuseStep 3530429 = 1323911) (by norm_num)
theorem B1859269 : Blo 1468554 1859269 := bbase (se 4 (by rfl) ⟨174306, by rfl⟩ : syracuseStep 1859269 = 348613) (by norm_num)
theorem B2203349 : Blo 1468554 2203349 := bbase (se 7 (by rfl) ⟨25820, by rfl⟩ : syracuseStep 2203349 = 51641) (by norm_num)
theorem B2203373 : Blo 1468554 2203373 := bbase (se 3 (by rfl) ⟨413132, by rfl⟩ : syracuseStep 2203373 = 826265) (by norm_num)
theorem B2203397 : Blo 1468554 2203397 := bbase (se 4 (by rfl) ⟨206568, by rfl⟩ : syracuseStep 2203397 = 413137) (by norm_num)
theorem B2121493 : Blo 1468554 2121493 := bbase (se 6 (by rfl) ⟨49722, by rfl⟩ : syracuseStep 2121493 = 99445) (by norm_num)
theorem B2203421 : Blo 1468554 2203421 := bbase (se 3 (by rfl) ⟨413141, by rfl⟩ : syracuseStep 2203421 = 826283) (by norm_num)
theorem B1859365 : Blo 1468554 1859365 := bbase (se 4 (by rfl) ⟨174315, by rfl⟩ : syracuseStep 1859365 = 348631) (by norm_num)
theorem B2203445 : Blo 1468554 2203445 := bbase (se 5 (by rfl) ⟨103286, by rfl⟩ : syracuseStep 2203445 = 206573) (by norm_num)
theorem B3718973 : Blo 1468554 3718973 := bbase (se 3 (by rfl) ⟨697307, by rfl⟩ : syracuseStep 3718973 = 1394615) (by norm_num)
theorem B2203469 : Blo 1468554 2203469 := bbase (se 3 (by rfl) ⟨413150, by rfl⟩ : syracuseStep 2203469 = 826301) (by norm_num)
theorem B2121557 : Blo 1468554 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B2203493 : Blo 1468554 2203493 := bbase (se 4 (by rfl) ⟨206577, by rfl⟩ : syracuseStep 2203493 = 413155) (by norm_num)
theorem B2203517 : Blo 1468554 2203517 := bbase (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) (by norm_num)
theorem B2203541 : Blo 1468554 2203541 := bbase (se 6 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 2203541 = 103291) (by norm_num)
theorem B7438229 : Blo 1468554 7438229 := bbase (se 6 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 7438229 = 348667) (by norm_num)
theorem B7061413 : Blo 1468554 7061413 := bbase (se 4 (by rfl) ⟨662007, by rfl⟩ : syracuseStep 7061413 = 1324015) (by norm_num)
theorem B2203565 : Blo 1468554 2203565 := bbase (se 3 (by rfl) ⟨413168, by rfl⟩ : syracuseStep 2203565 = 826337) (by norm_num)
theorem B2203589 : Blo 1468554 2203589 := bbase (se 4 (by rfl) ⟨206586, by rfl⟩ : syracuseStep 2203589 = 413173) (by norm_num)
theorem B1859537 : Blo 1468554 1859537 := bbase (se 2 (by rfl) ⟨697326, by rfl⟩ : syracuseStep 1859537 = 1394653) (by norm_num)
theorem B2654165 : Blo 1468554 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B2203613 : Blo 1468554 2203613 := bbase (se 3 (by rfl) ⟨413177, by rfl⟩ : syracuseStep 2203613 = 826355) (by norm_num)
theorem B2203637 : Blo 1468554 2203637 := bbase (se 5 (by rfl) ⟨103295, by rfl⟩ : syracuseStep 2203637 = 206591) (by norm_num)
theorem B2203649 : Blo 1468554 2203649 := bstep (se 2 (by rfl) ⟨826368, by rfl⟩ : syracuseStep 2203649 = 1652737) B1652737
theorem B2203667 : Blo 1468554 2203667 := bstep (se 1 (by rfl) ⟨1652750, by rfl⟩ : syracuseStep 2203667 = 3305501) B3305501
theorem B2203697 : Blo 1468554 2203697 := bstep (se 2 (by rfl) ⟨826386, by rfl⟩ : syracuseStep 2203697 = 1652773) B1652773
theorem B2203715 : Blo 1468554 2203715 := bstep (se 1 (by rfl) ⟨1652786, by rfl⟩ : syracuseStep 2203715 = 3305573) B3305573
theorem B2203745 : Blo 1468554 2203745 := bstep (se 2 (by rfl) ⟨826404, by rfl⟩ : syracuseStep 2203745 = 1652809) B1652809
theorem B6275171 : Blo 1468554 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B3719267 : Blo 1468554 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B2203763 : Blo 1468554 2203763 := bstep (se 1 (by rfl) ⟨1652822, by rfl⟩ : syracuseStep 2203763 = 3305645) B3305645
theorem B1859699 : Blo 1468554 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B2203793 : Blo 1468554 2203793 := bstep (se 2 (by rfl) ⟨826422, by rfl⟩ : syracuseStep 2203793 = 1652845) B1652845
theorem B2203811 : Blo 1468554 2203811 := bstep (se 1 (by rfl) ⟨1652858, by rfl⟩ : syracuseStep 2203811 = 3305717) B3305717
theorem B5578915 : Blo 1468554 5578915 := bstep (se 1 (by rfl) ⟨4184186, by rfl⟩ : syracuseStep 5578915 = 8368373) B8368373
theorem B2203841 : Blo 1468554 2203841 := bstep (se 2 (by rfl) ⟨826440, by rfl⟩ : syracuseStep 2203841 = 1652881) B1652881
theorem B8372429 : Blo 1468554 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B2203859 : Blo 1468554 2203859 := bstep (se 1 (by rfl) ⟨1652894, by rfl⟩ : syracuseStep 2203859 = 3305789) B3305789
theorem B2203889 : Blo 1468554 2203889 := bstep (se 2 (by rfl) ⟨826458, by rfl⟩ : syracuseStep 2203889 = 1652917) B1652917
theorem B2203907 : Blo 1468554 2203907 := bstep (se 1 (by rfl) ⟨1652930, by rfl⟩ : syracuseStep 2203907 = 3305861) B3305861
theorem B2203937 : Blo 1468554 2203937 := bstep (se 2 (by rfl) ⟨826476, by rfl⟩ : syracuseStep 2203937 = 1652953) B1652953
theorem B3719459 : Blo 1468554 3719459 := bstep (se 1 (by rfl) ⟨2789594, by rfl⟩ : syracuseStep 3719459 = 5579189) B5579189
theorem B3531043 : Blo 1468554 3531043 := bstep (se 1 (by rfl) ⟨2648282, by rfl⟩ : syracuseStep 3531043 = 5296565) B5296565
theorem B2203955 : Blo 1468554 2203955 := bstep (se 1 (by rfl) ⟨1652966, by rfl⟩ : syracuseStep 2203955 = 3305933) B3305933
theorem B4956497 : Blo 1468554 4956497 := bstep (se 2 (by rfl) ⟨1858686, by rfl⟩ : syracuseStep 4956497 = 3717373) B3717373
theorem B2203985 : Blo 1468554 2203985 := bstep (se 2 (by rfl) ⟨826494, by rfl⟩ : syracuseStep 2203985 = 1652989) B1652989
theorem B2204003 : Blo 1468554 2204003 := bstep (se 1 (by rfl) ⟨1653002, by rfl⟩ : syracuseStep 2204003 = 3306005) B3306005
theorem B2204033 : Blo 1468554 2204033 := bstep (se 2 (by rfl) ⟨826512, by rfl⟩ : syracuseStep 2204033 = 1653025) B1653025
theorem B2204051 : Blo 1468554 2204051 := bstep (se 1 (by rfl) ⟨1653038, by rfl⟩ : syracuseStep 2204051 = 3306077) B3306077
theorem B2204081 : Blo 1468554 2204081 := bstep (se 2 (by rfl) ⟨826530, by rfl⟩ : syracuseStep 2204081 = 1653061) B1653061
theorem B2204099 : Blo 1468554 2204099 := bstep (se 1 (by rfl) ⟨1653074, by rfl⟩ : syracuseStep 2204099 = 3306149) B3306149
theorem B2204129 : Blo 1468554 2204129 := bstep (se 2 (by rfl) ⟨826548, by rfl⟩ : syracuseStep 2204129 = 1653097) B1653097
theorem B2204147 : Blo 1468554 2204147 := bstep (se 1 (by rfl) ⟨1653110, by rfl⟩ : syracuseStep 2204147 = 3306221) B3306221
theorem B7062029 : Blo 1468554 7062029 := bstep (se 3 (by rfl) ⟨1324130, by rfl⟩ : syracuseStep 7062029 = 2648261) B2648261
theorem B4186637 : Blo 1468554 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B2204177 : Blo 1468554 2204177 := bstep (se 2 (by rfl) ⟨826566, by rfl⟩ : syracuseStep 2204177 = 1653133) B1653133
theorem B2204195 : Blo 1468554 2204195 := bstep (se 1 (by rfl) ⟨1653146, by rfl⟩ : syracuseStep 2204195 = 3306293) B3306293
theorem B2204225 : Blo 1468554 2204225 := bstep (se 2 (by rfl) ⟨826584, by rfl⟩ : syracuseStep 2204225 = 1653169) B1653169
theorem B2646595 : Blo 1468554 2646595 := bstep (se 1 (by rfl) ⟨1984946, by rfl⟩ : syracuseStep 2646595 = 3969893) B3969893
theorem B2204243 : Blo 1468554 2204243 := bstep (se 1 (by rfl) ⟨1653182, by rfl⟩ : syracuseStep 2204243 = 3306365) B3306365
theorem B2204273 : Blo 1468554 2204273 := bstep (se 2 (by rfl) ⟨826602, by rfl⟩ : syracuseStep 2204273 = 1653205) B1653205
theorem B2204291 : Blo 1468554 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B2204321 : Blo 1468554 2204321 := bstep (se 2 (by rfl) ⟨826620, by rfl⟩ : syracuseStep 2204321 = 1653241) B1653241
theorem B8364707 : Blo 1468554 8364707 := bstep (se 1 (by rfl) ⟨6273530, by rfl⟩ : syracuseStep 8364707 = 12547061) B12547061
theorem B2204339 : Blo 1468554 2204339 := bstep (se 1 (by rfl) ⟨1653254, by rfl⟩ : syracuseStep 2204339 = 3306509) B3306509
theorem B4186829 : Blo 1468554 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B2204369 : Blo 1468554 2204369 := bstep (se 2 (by rfl) ⟨826638, by rfl⟩ : syracuseStep 2204369 = 1653277) B1653277
theorem B2204387 : Blo 1468554 2204387 := bstep (se 1 (by rfl) ⟨1653290, by rfl⟩ : syracuseStep 2204387 = 3306581) B3306581
theorem B2204417 : Blo 1468554 2204417 := bstep (se 2 (by rfl) ⟨826656, by rfl⟩ : syracuseStep 2204417 = 1653313) B1653313
theorem B2204435 : Blo 1468554 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B2204465 : Blo 1468554 2204465 := bstep (se 2 (by rfl) ⟨826674, by rfl⟩ : syracuseStep 2204465 = 1653349) B1653349
theorem B1860403 : Blo 1468554 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B21185333 : Blo 1468554 21185333 := bstep (se 5 (by rfl) ⟨993062, by rfl⟩ : syracuseStep 21185333 = 1986125) B1986125
theorem B2204483 : Blo 1468554 2204483 := bstep (se 1 (by rfl) ⟨1653362, by rfl⟩ : syracuseStep 2204483 = 3306725) B3306725
theorem B2204513 : Blo 1468554 2204513 := bstep (se 2 (by rfl) ⟨826692, by rfl⟩ : syracuseStep 2204513 = 1653385) B1653385
theorem B4957037 : Blo 1468554 4957037 := bstep (se 3 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 4957037 = 1858889) B1858889
theorem B2204531 : Blo 1468554 2204531 := bstep (se 1 (by rfl) ⟨1653398, by rfl⟩ : syracuseStep 2204531 = 3306797) B3306797
theorem B2204561 : Blo 1468554 2204561 := bstep (se 2 (by rfl) ⟨826710, by rfl⟩ : syracuseStep 2204561 = 1653421) B1653421
theorem B1860499 : Blo 1468554 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B4957091 : Blo 1468554 4957091 := bstep (se 1 (by rfl) ⟨3717818, by rfl⟩ : syracuseStep 4957091 = 7435637) B7435637
theorem B2204579 : Blo 1468554 2204579 := bstep (se 1 (by rfl) ⟨1653434, by rfl⟩ : syracuseStep 2204579 = 3306869) B3306869
theorem B2204609 : Blo 1468554 2204609 := bstep (se 2 (by rfl) ⟨826728, by rfl⟩ : syracuseStep 2204609 = 1653457) B1653457
theorem B2204627 : Blo 1468554 2204627 := bstep (se 1 (by rfl) ⟨1653470, by rfl⟩ : syracuseStep 2204627 = 3306941) B3306941
theorem B2204657 : Blo 1468554 2204657 := bstep (se 2 (by rfl) ⟨826746, by rfl⟩ : syracuseStep 2204657 = 1653493) B1653493
theorem B2204675 : Blo 1468554 2204675 := bstep (se 1 (by rfl) ⟨1653506, by rfl⟩ : syracuseStep 2204675 = 3307013) B3307013
theorem B2204705 : Blo 1468554 2204705 := bstep (se 2 (by rfl) ⟨826764, by rfl⟩ : syracuseStep 2204705 = 1653529) B1653529
theorem B2204723 : Blo 1468554 2204723 := bstep (se 1 (by rfl) ⟨1653542, by rfl⟩ : syracuseStep 2204723 = 3307085) B3307085
theorem B2204753 : Blo 1468554 2204753 := bstep (se 2 (by rfl) ⟨826782, by rfl⟩ : syracuseStep 2204753 = 1653565) B1653565
theorem B2204771 : Blo 1468554 2204771 := bstep (se 1 (by rfl) ⟨1653578, by rfl⟩ : syracuseStep 2204771 = 3307157) B3307157
theorem B2204801 : Blo 1468554 2204801 := bstep (se 2 (by rfl) ⟨826800, by rfl⟩ : syracuseStep 2204801 = 1653601) B1653601
theorem B2204819 : Blo 1468554 2204819 := bstep (se 1 (by rfl) ⟨1653614, by rfl⟩ : syracuseStep 2204819 = 3307229) B3307229
theorem B4465837 : Blo 1468554 4465837 := bstep (se 3 (by rfl) ⟨837344, by rfl⟩ : syracuseStep 4465837 = 1674689) B1674689
theorem B4957361 : Blo 1468554 4957361 := bstep (se 2 (by rfl) ⟨1859010, by rfl⟩ : syracuseStep 4957361 = 3718021) B3718021
theorem B2204849 : Blo 1468554 2204849 := bstep (se 2 (by rfl) ⟨826818, by rfl⟩ : syracuseStep 2204849 = 1653637) B1653637
theorem B3138755 : Blo 1468554 3138755 := bstep (se 1 (by rfl) ⟨2354066, by rfl⟩ : syracuseStep 3138755 = 4708133) B4708133
theorem B2204867 : Blo 1468554 2204867 := bstep (se 1 (by rfl) ⟨1653650, by rfl⟩ : syracuseStep 2204867 = 3307301) B3307301
theorem B3720401 : Blo 1468554 3720401 := bstep (se 2 (by rfl) ⟨1395150, by rfl⟩ : syracuseStep 3720401 = 2790301) B2790301
theorem B2204897 : Blo 1468554 2204897 := bstep (se 2 (by rfl) ⟨826836, by rfl⟩ : syracuseStep 2204897 = 1653673) B1653673
theorem B2204915 : Blo 1468554 2204915 := bstep (se 1 (by rfl) ⟨1653686, by rfl⟩ : syracuseStep 2204915 = 3307373) B3307373
theorem B3720451 : Blo 1468554 3720451 := bstep (se 1 (by rfl) ⟨2790338, by rfl⟩ : syracuseStep 3720451 = 5580677) B5580677
theorem B2204945 : Blo 1468554 2204945 := bstep (se 2 (by rfl) ⟨826854, by rfl⟩ : syracuseStep 2204945 = 1653709) B1653709
theorem B2204963 : Blo 1468554 2204963 := bstep (se 1 (by rfl) ⟨1653722, by rfl⟩ : syracuseStep 2204963 = 3307445) B3307445
theorem B2647345 : Blo 1468554 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B2204993 : Blo 1468554 2204993 := bstep (se 2 (by rfl) ⟨826872, by rfl⟩ : syracuseStep 2204993 = 1653745) B1653745
theorem B2205011 : Blo 1468554 2205011 := bstep (se 1 (by rfl) ⟨1653758, by rfl⟩ : syracuseStep 2205011 = 3307517) B3307517
theorem B2205041 : Blo 1468554 2205041 := bstep (se 2 (by rfl) ⟨826890, by rfl⟩ : syracuseStep 2205041 = 1653781) B1653781
theorem B2205059 : Blo 1468554 2205059 := bstep (se 1 (by rfl) ⟨1653794, by rfl⟩ : syracuseStep 2205059 = 3307589) B3307589
theorem B1860995 : Blo 1468554 1860995 := bstep (se 1 (by rfl) ⟨1395746, by rfl⟩ : syracuseStep 1860995 = 2791493) B2791493
theorem B3720593 : Blo 1468554 3720593 := bstep (se 2 (by rfl) ⟨1395222, by rfl⟩ : syracuseStep 3720593 = 2790445) B2790445
theorem B2205089 : Blo 1468554 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B2205107 : Blo 1468554 2205107 := bstep (se 1 (by rfl) ⟨1653830, by rfl⟩ : syracuseStep 2205107 = 3307661) B3307661
theorem B2205137 : Blo 1468554 2205137 := bstep (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) B1653853
theorem B2205155 : Blo 1468554 2205155 := bstep (se 1 (by rfl) ⟨1653866, by rfl⟩ : syracuseStep 2205155 = 3307733) B3307733
theorem B2205185 : Blo 1468554 2205185 := bstep (se 2 (by rfl) ⟨826944, by rfl⟩ : syracuseStep 2205185 = 1653889) B1653889
theorem B2205203 : Blo 1468554 2205203 := bstep (se 1 (by rfl) ⟨1653902, by rfl⟩ : syracuseStep 2205203 = 3307805) B3307805
theorem B2205233 : Blo 1468554 2205233 := bstep (se 2 (by rfl) ⟨826962, by rfl⟩ : syracuseStep 2205233 = 1653925) B1653925
theorem B2205251 : Blo 1468554 2205251 := bstep (se 1 (by rfl) ⟨1653938, by rfl⟩ : syracuseStep 2205251 = 3307877) B3307877
theorem B2205281 : Blo 1468554 2205281 := bstep (se 2 (by rfl) ⟨826980, by rfl⟩ : syracuseStep 2205281 = 1653961) B1653961
theorem B2205299 : Blo 1468554 2205299 := bstep (se 1 (by rfl) ⟨1653974, by rfl⟩ : syracuseStep 2205299 = 3307949) B3307949
theorem B2352785 : Blo 1468554 2352785 := bstep (se 2 (by rfl) ⟨882294, by rfl⟩ : syracuseStep 2352785 = 1764589) B1764589
theorem B2205329 : Blo 1468554 2205329 := bstep (se 2 (by rfl) ⟨826998, by rfl⟩ : syracuseStep 2205329 = 1653997) B1653997
theorem B2205347 : Blo 1468554 2205347 := bstep (se 1 (by rfl) ⟨1654010, by rfl⟩ : syracuseStep 2205347 = 3308021) B3308021
theorem B2205377 : Blo 1468554 2205377 := bstep (se 2 (by rfl) ⟨827016, by rfl⟩ : syracuseStep 2205377 = 1654033) B1654033
theorem B4957901 : Blo 1468554 4957901 := bstep (se 3 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 4957901 = 1859213) B1859213
theorem B2205395 : Blo 1468554 2205395 := bstep (se 1 (by rfl) ⟨1654046, by rfl⟩ : syracuseStep 2205395 = 3308093) B3308093
theorem B7948003 : Blo 1468554 7948003 := bstep (se 1 (by rfl) ⟨5961002, by rfl⟩ : syracuseStep 7948003 = 11922005) B11922005
theorem B4835057 : Blo 1468554 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B2205425 : Blo 1468554 2205425 := bstep (se 2 (by rfl) ⟨827034, by rfl⟩ : syracuseStep 2205425 = 1654069) B1654069
theorem B4957955 : Blo 1468554 4957955 := bstep (se 1 (by rfl) ⟨3718466, by rfl⟩ : syracuseStep 4957955 = 7436933) B7436933
theorem B2205443 : Blo 1468554 2205443 := bstep (se 1 (by rfl) ⟨1654082, by rfl⟩ : syracuseStep 2205443 = 3308165) B3308165
theorem B2205473 : Blo 1468554 2205473 := bstep (se 2 (by rfl) ⟨827052, by rfl⟩ : syracuseStep 2205473 = 1654105) B1654105
theorem B2205491 : Blo 1468554 2205491 := bstep (se 1 (by rfl) ⟨1654118, by rfl⟩ : syracuseStep 2205491 = 3308237) B3308237
theorem B2205521 : Blo 1468554 2205521 := bstep (se 2 (by rfl) ⟨827070, by rfl⟩ : syracuseStep 2205521 = 1654141) B1654141
theorem B2205539 : Blo 1468554 2205539 := bstep (se 1 (by rfl) ⟨1654154, by rfl⟩ : syracuseStep 2205539 = 3308309) B3308309
theorem B2205569 : Blo 1468554 2205569 := bstep (se 2 (by rfl) ⟨827088, by rfl⟩ : syracuseStep 2205569 = 1654177) B1654177
theorem B2205587 : Blo 1468554 2205587 := bstep (se 1 (by rfl) ⟨1654190, by rfl⟩ : syracuseStep 2205587 = 3308381) B3308381
theorem B2549665 : Blo 1468554 2549665 := bstep (se 2 (by rfl) ⟨956124, by rfl⟩ : syracuseStep 2549665 = 1912249) B1912249
theorem B2205617 : Blo 1468554 2205617 := bstep (se 2 (by rfl) ⟨827106, by rfl⟩ : syracuseStep 2205617 = 1654213) B1654213
theorem B2205635 : Blo 1468554 2205635 := bstep (se 1 (by rfl) ⟨1654226, by rfl⟩ : syracuseStep 2205635 = 3308453) B3308453
theorem B17876933 : Blo 1468554 17876933 := bstep (se 4 (by rfl) ⟨1675962, by rfl⟩ : syracuseStep 17876933 = 3351925) B3351925
theorem B2205665 : Blo 1468554 2205665 := bstep (se 2 (by rfl) ⟨827124, by rfl⟩ : syracuseStep 2205665 = 1654249) B1654249
theorem B2205683 : Blo 1468554 2205683 := bstep (se 1 (by rfl) ⟨1654262, by rfl⟩ : syracuseStep 2205683 = 3308525) B3308525
theorem B4958225 : Blo 1468554 4958225 := bstep (se 2 (by rfl) ⟨1859334, by rfl⟩ : syracuseStep 4958225 = 3718669) B3718669
theorem B2205713 : Blo 1468554 2205713 := bstep (se 2 (by rfl) ⟨827142, by rfl⟩ : syracuseStep 2205713 = 1654285) B1654285
theorem B2205731 : Blo 1468554 2205731 := bstep (se 1 (by rfl) ⟨1654298, by rfl⟩ : syracuseStep 2205731 = 3308597) B3308597
theorem B6277169 : Blo 1468554 6277169 := bstep (se 2 (by rfl) ⟨2353938, by rfl⟩ : syracuseStep 6277169 = 4707877) B4707877
theorem B21473333 : Blo 1468554 21473333 := bstep (se 5 (by rfl) ⟨1006562, by rfl⟩ : syracuseStep 21473333 = 2013125) B2013125
theorem B2205761 : Blo 1468554 2205761 := bstep (se 2 (by rfl) ⟨827160, by rfl⟩ : syracuseStep 2205761 = 1654321) B1654321
theorem B4466765 : Blo 1468554 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B2091091 : Blo 1468554 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B2205779 : Blo 1468554 2205779 := bstep (se 1 (by rfl) ⟨1654334, by rfl⟩ : syracuseStep 2205779 = 3308669) B3308669
theorem B7440497 : Blo 1468554 7440497 := bstep (se 2 (by rfl) ⟨2790186, by rfl⟩ : syracuseStep 7440497 = 5580373) B5580373
theorem B2205809 : Blo 1468554 2205809 := bstep (se 2 (by rfl) ⟨827178, by rfl⟩ : syracuseStep 2205809 = 1654357) B1654357
theorem B2205827 : Blo 1468554 2205827 := bstep (se 1 (by rfl) ⟨1654370, by rfl⟩ : syracuseStep 2205827 = 3308741) B3308741
theorem B3532945 : Blo 1468554 3532945 := bstep (se 2 (by rfl) ⟨1324854, by rfl⟩ : syracuseStep 3532945 = 2649709) B2649709
theorem B1468563 : Blo 1468554 1468563 := bstep (se 1 (by rfl) ⟨1101422, by rfl⟩ : syracuseStep 1468563 = 2202845) B2202845
theorem B1468579 : Blo 1468554 1468579 := bstep (se 1 (by rfl) ⟨1101434, by rfl⟩ : syracuseStep 1468579 = 2202869) B2202869
theorem B1468595 : Blo 1468554 1468595 := bstep (se 1 (by rfl) ⟨1101446, by rfl⟩ : syracuseStep 1468595 = 2202893) B2202893
theorem B1468611 : Blo 1468554 1468611 := bstep (se 1 (by rfl) ⟨1101458, by rfl⟩ : syracuseStep 1468611 = 2202917) B2202917
theorem B1468627 : Blo 1468554 1468627 := bstep (se 1 (by rfl) ⟨1101470, by rfl⟩ : syracuseStep 1468627 = 2202941) B2202941
theorem B1468643 : Blo 1468554 1468643 := bstep (se 1 (by rfl) ⟨1101482, by rfl⟩ : syracuseStep 1468643 = 2202965) B2202965
theorem B1468659 : Blo 1468554 1468659 := bstep (se 1 (by rfl) ⟨1101494, by rfl⟩ : syracuseStep 1468659 = 2202989) B2202989
theorem B1468675 : Blo 1468554 1468675 := bstep (se 1 (by rfl) ⟨1101506, by rfl⟩ : syracuseStep 1468675 = 2203013) B2203013
theorem B1468691 : Blo 1468554 1468691 := bstep (se 1 (by rfl) ⟨1101518, by rfl⟩ : syracuseStep 1468691 = 2203037) B2203037
theorem B1468707 : Blo 1468554 1468707 := bstep (se 1 (by rfl) ⟨1101530, by rfl⟩ : syracuseStep 1468707 = 2203061) B2203061
theorem B1468723 : Blo 1468554 1468723 := bstep (se 1 (by rfl) ⟨1101542, by rfl⟩ : syracuseStep 1468723 = 2203085) B2203085
theorem B1468739 : Blo 1468554 1468739 := bstep (se 1 (by rfl) ⟨1101554, by rfl⟩ : syracuseStep 1468739 = 2203109) B2203109
theorem B5581133 : Blo 1468554 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B1468755 : Blo 1468554 1468755 := bstep (se 1 (by rfl) ⟨1101566, by rfl⟩ : syracuseStep 1468755 = 2203133) B2203133
theorem B1468771 : Blo 1468554 1468771 := bstep (se 1 (by rfl) ⟨1101578, by rfl⟩ : syracuseStep 1468771 = 2203157) B2203157
theorem B18835811 : Blo 1468554 18835811 := bstep (se 1 (by rfl) ⟨14126858, by rfl⟩ : syracuseStep 18835811 = 28253717) B28253717
theorem B2828657 : Blo 1468554 2828657 := bstep (se 2 (by rfl) ⟨1060746, by rfl⟩ : syracuseStep 2828657 = 2121493) B2121493
theorem B3721585 : Blo 1468554 3721585 := bstep (se 2 (by rfl) ⟨1395594, by rfl⟩ : syracuseStep 3721585 = 2791189) B2791189
theorem B1468787 : Blo 1468554 1468787 := bstep (se 1 (by rfl) ⟨1101590, by rfl⟩ : syracuseStep 1468787 = 2203181) B2203181
theorem B1468803 : Blo 1468554 1468803 := bstep (se 1 (by rfl) ⟨1101602, by rfl⟩ : syracuseStep 1468803 = 2203205) B2203205
theorem B8374661 : Blo 1468554 8374661 := bstep (se 4 (by rfl) ⟨785124, by rfl⟩ : syracuseStep 8374661 = 1570249) B1570249
theorem B1984915 : Blo 1468554 1984915 := bstep (se 1 (by rfl) ⟨1488686, by rfl⟩ : syracuseStep 1984915 = 2977373) B2977373
theorem B1468819 : Blo 1468554 1468819 := bstep (se 1 (by rfl) ⟨1101614, by rfl⟩ : syracuseStep 1468819 = 2203229) B2203229
theorem B1468835 : Blo 1468554 1468835 := bstep (se 1 (by rfl) ⟨1101626, by rfl⟩ : syracuseStep 1468835 = 2203253) B2203253
theorem B1468851 : Blo 1468554 1468851 := bstep (se 1 (by rfl) ⟨1101638, by rfl⟩ : syracuseStep 1468851 = 2203277) B2203277
theorem B16730549 : Blo 1468554 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B1468867 : Blo 1468554 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B1468883 : Blo 1468554 1468883 := bstep (se 1 (by rfl) ⟨1101662, by rfl⟩ : syracuseStep 1468883 = 2203325) B2203325
theorem B2353619 : Blo 1468554 2353619 := bstep (se 1 (by rfl) ⟨1765214, by rfl⟩ : syracuseStep 2353619 = 3530429) B3530429
theorem B1468899 : Blo 1468554 1468899 := bstep (se 1 (by rfl) ⟨1101674, by rfl⟩ : syracuseStep 1468899 = 2203349) B2203349
theorem B1468915 : Blo 1468554 1468915 := bstep (se 1 (by rfl) ⟨1101686, by rfl⟩ : syracuseStep 1468915 = 2203373) B2203373
theorem B1468931 : Blo 1468554 1468931 := bstep (se 1 (by rfl) ⟨1101698, by rfl⟩ : syracuseStep 1468931 = 2203397) B2203397
theorem B8366597 : Blo 1468554 8366597 := bstep (se 4 (by rfl) ⟨784368, by rfl⟩ : syracuseStep 8366597 = 1568737) B1568737
theorem B1468947 : Blo 1468554 1468947 := bstep (se 1 (by rfl) ⟨1101710, by rfl⟩ : syracuseStep 1468947 = 2203421) B2203421
theorem B1468963 : Blo 1468554 1468963 := bstep (se 1 (by rfl) ⟨1101722, by rfl⟩ : syracuseStep 1468963 = 2203445) B2203445
theorem B4958765 : Blo 1468554 4958765 := bstep (se 3 (by rfl) ⟨929768, by rfl⟩ : syracuseStep 4958765 = 1859537) B1859537
theorem B9415217 : Blo 1468554 9415217 := bstep (se 2 (by rfl) ⟨3530706, by rfl⟩ : syracuseStep 9415217 = 7061413) B7061413
theorem B1468979 : Blo 1468554 1468979 := bstep (se 1 (by rfl) ⟨1101734, by rfl⟩ : syracuseStep 1468979 = 2203469) B2203469
theorem B1468995 : Blo 1468554 1468995 := bstep (se 1 (by rfl) ⟨1101746, by rfl⟩ : syracuseStep 1468995 = 2203493) B2203493
theorem B1469011 : Blo 1468554 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B1469027 : Blo 1468554 1469027 := bstep (se 1 (by rfl) ⟨1101770, by rfl⟩ : syracuseStep 1469027 = 2203541) B2203541
theorem B4958819 : Blo 1468554 4958819 := bstep (se 1 (by rfl) ⟨3719114, by rfl⟩ : syracuseStep 4958819 = 7438229) B7438229
theorem B1469043 : Blo 1468554 1469043 := bstep (se 1 (by rfl) ⟨1101782, by rfl⟩ : syracuseStep 1469043 = 2203565) B2203565
theorem B1469059 : Blo 1468554 1469059 := bstep (se 1 (by rfl) ⟨1101794, by rfl⟩ : syracuseStep 1469059 = 2203589) B2203589
theorem B3721859 : Blo 1468554 3721859 := bstep (se 1 (by rfl) ⟨2791394, by rfl⟩ : syracuseStep 3721859 = 5582789) B5582789
theorem B1469075 : Blo 1468554 1469075 := bstep (se 1 (by rfl) ⟨1101806, by rfl⟩ : syracuseStep 1469075 = 2203613) B2203613
theorem B1469091 : Blo 1468554 1469091 := bstep (se 1 (by rfl) ⟨1101818, by rfl⟩ : syracuseStep 1469091 = 2203637) B2203637
theorem B1469107 : Blo 1468554 1469107 := bstep (se 1 (by rfl) ⟨1101830, by rfl⟩ : syracuseStep 1469107 = 2203661) B2203661
theorem B1469123 : Blo 1468554 1469123 := bstep (se 1 (by rfl) ⟨1101842, by rfl⟩ : syracuseStep 1469123 = 2203685) B2203685
theorem B3771089 : Blo 1468554 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B1469139 : Blo 1468554 1469139 := bstep (se 1 (by rfl) ⟨1101854, by rfl⟩ : syracuseStep 1469139 = 2203709) B2203709
theorem B1469155 : Blo 1468554 1469155 := bstep (se 1 (by rfl) ⟨1101866, by rfl⟩ : syracuseStep 1469155 = 2203733) B2203733
theorem B1469171 : Blo 1468554 1469171 := bstep (se 1 (by rfl) ⟨1101878, by rfl⟩ : syracuseStep 1469171 = 2203757) B2203757
theorem B2353907 : Blo 1468554 2353907 := bstep (se 1 (by rfl) ⟨1765430, by rfl⟩ : syracuseStep 2353907 = 3530861) B3530861
theorem B1469187 : Blo 1468554 1469187 := bstep (se 1 (by rfl) ⟨1101890, by rfl⟩ : syracuseStep 1469187 = 2203781) B2203781
theorem B1469203 : Blo 1468554 1469203 := bstep (se 1 (by rfl) ⟨1101902, by rfl⟩ : syracuseStep 1469203 = 2203805) B2203805
theorem B1469219 : Blo 1468554 1469219 := bstep (se 1 (by rfl) ⟨1101914, by rfl⟩ : syracuseStep 1469219 = 2203829) B2203829
theorem B1469235 : Blo 1468554 1469235 := bstep (se 1 (by rfl) ⟨1101926, by rfl⟩ : syracuseStep 1469235 = 2203853) B2203853
theorem B3304259 : Blo 1468554 3304259 := bstep (se 1 (by rfl) ⟨2478194, by rfl⟩ : syracuseStep 3304259 = 4956389) B4956389
theorem B1469251 : Blo 1468554 1469251 := bstep (se 1 (by rfl) ⟨1101938, by rfl⟩ : syracuseStep 1469251 = 2203877) B2203877
theorem B3722051 : Blo 1468554 3722051 := bstep (se 1 (by rfl) ⟨2791538, by rfl⟩ : syracuseStep 3722051 = 5583077) B5583077
theorem B1469267 : Blo 1468554 1469267 := bstep (se 1 (by rfl) ⟨1101950, by rfl⟩ : syracuseStep 1469267 = 2203901) B2203901
theorem B1469283 : Blo 1468554 1469283 := bstep (se 1 (by rfl) ⟨1101962, by rfl⟩ : syracuseStep 1469283 = 2203925) B2203925
theorem B11152241 : Blo 1468554 11152241 := bstep (se 2 (by rfl) ⟨4182090, by rfl⟩ : syracuseStep 11152241 = 8364181) B8364181
theorem B4959089 : Blo 1468554 4959089 := bstep (se 2 (by rfl) ⟨1859658, by rfl⟩ : syracuseStep 4959089 = 3719317) B3719317
theorem B1469299 : Blo 1468554 1469299 := bstep (se 1 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 1469299 = 2203949) B2203949
theorem B1469315 : Blo 1468554 1469315 := bstep (se 1 (by rfl) ⟨1101986, by rfl⟩ : syracuseStep 1469315 = 2203973) B2203973
theorem B1469331 : Blo 1468554 1469331 := bstep (se 1 (by rfl) ⟨1101998, by rfl⟩ : syracuseStep 1469331 = 2203997) B2203997
theorem B1469347 : Blo 1468554 1469347 := bstep (se 1 (by rfl) ⟨1102010, by rfl⟩ : syracuseStep 1469347 = 2204021) B2204021
theorem B2788273 : Blo 1468554 2788273 := bstep (se 2 (by rfl) ⟨1045602, by rfl⟩ : syracuseStep 2788273 = 2091205) B2091205
theorem B1469363 : Blo 1468554 1469363 := bstep (se 1 (by rfl) ⟨1102022, by rfl⟩ : syracuseStep 1469363 = 2204045) B2204045
theorem B1469379 : Blo 1468554 1469379 := bstep (se 1 (by rfl) ⟨1102034, by rfl⟩ : syracuseStep 1469379 = 2204069) B2204069
theorem B6278093 : Blo 1468554 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B1469395 : Blo 1468554 1469395 := bstep (se 1 (by rfl) ⟨1102046, by rfl⟩ : syracuseStep 1469395 = 2204093) B2204093
theorem B2354131 : Blo 1468554 2354131 := bstep (se 1 (by rfl) ⟨1765598, by rfl⟩ : syracuseStep 2354131 = 3531197) B3531197
theorem B1469411 : Blo 1468554 1469411 := bstep (se 1 (by rfl) ⟨1102058, by rfl⟩ : syracuseStep 1469411 = 2204117) B2204117
theorem B1469427 : Blo 1468554 1469427 := bstep (se 1 (by rfl) ⟨1102070, by rfl⟩ : syracuseStep 1469427 = 2204141) B2204141
theorem B1469443 : Blo 1468554 1469443 := bstep (se 1 (by rfl) ⟨1102082, by rfl⟩ : syracuseStep 1469443 = 2204165) B2204165
theorem B10742797 : Blo 1468554 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B1469459 : Blo 1468554 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B1469475 : Blo 1468554 1469475 := bstep (se 1 (by rfl) ⟨1102106, by rfl⟩ : syracuseStep 1469475 = 2204213) B2204213
theorem B1469491 : Blo 1468554 1469491 := bstep (se 1 (by rfl) ⟨1102118, by rfl⟩ : syracuseStep 1469491 = 2204237) B2204237
theorem B1469507 : Blo 1468554 1469507 := bstep (se 1 (by rfl) ⟨1102130, by rfl⟩ : syracuseStep 1469507 = 2204261) B2204261
theorem B3304529 : Blo 1468554 3304529 := bstep (se 2 (by rfl) ⟨1239198, by rfl⟩ : syracuseStep 3304529 = 2478397) B2478397
theorem B1985617 : Blo 1468554 1985617 := bstep (se 2 (by rfl) ⟨744606, by rfl⟩ : syracuseStep 1985617 = 1489213) B1489213
theorem B1469523 : Blo 1468554 1469523 := bstep (se 1 (by rfl) ⟨1102142, by rfl⟩ : syracuseStep 1469523 = 2204285) B2204285
theorem B3304547 : Blo 1468554 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B1469539 : Blo 1468554 1469539 := bstep (se 1 (by rfl) ⟨1102154, by rfl⟩ : syracuseStep 1469539 = 2204309) B2204309
theorem B1469555 : Blo 1468554 1469555 := bstep (se 1 (by rfl) ⟨1102166, by rfl⟩ : syracuseStep 1469555 = 2204333) B2204333
theorem B1469571 : Blo 1468554 1469571 := bstep (se 1 (by rfl) ⟨1102178, by rfl⟩ : syracuseStep 1469571 = 2204357) B2204357
theorem B1469587 : Blo 1468554 1469587 := bstep (se 1 (by rfl) ⟨1102190, by rfl⟩ : syracuseStep 1469587 = 2204381) B2204381
theorem B1469603 : Blo 1468554 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B1469619 : Blo 1468554 1469619 := bstep (se 1 (by rfl) ⟨1102214, by rfl⟩ : syracuseStep 1469619 = 2204429) B2204429
theorem B2092225 : Blo 1468554 2092225 := bstep (se 2 (by rfl) ⟨784584, by rfl⟩ : syracuseStep 2092225 = 1569169) B1569169
theorem B1469635 : Blo 1468554 1469635 := bstep (se 1 (by rfl) ⟨1102226, by rfl⟩ : syracuseStep 1469635 = 2204453) B2204453
theorem B1469651 : Blo 1468554 1469651 := bstep (se 1 (by rfl) ⟨1102238, by rfl⟩ : syracuseStep 1469651 = 2204477) B2204477
theorem B1469667 : Blo 1468554 1469667 := bstep (se 1 (by rfl) ⟨1102250, by rfl⟩ : syracuseStep 1469667 = 2204501) B2204501
theorem B1985779 : Blo 1468554 1985779 := bstep (se 1 (by rfl) ⟨1489334, by rfl⟩ : syracuseStep 1985779 = 2978669) B2978669
theorem B1469683 : Blo 1468554 1469683 := bstep (se 1 (by rfl) ⟨1102262, by rfl⟩ : syracuseStep 1469683 = 2204525) B2204525
theorem B1469699 : Blo 1468554 1469699 := bstep (se 1 (by rfl) ⟨1102274, by rfl⟩ : syracuseStep 1469699 = 2204549) B2204549
theorem B1469715 : Blo 1468554 1469715 := bstep (se 1 (by rfl) ⟨1102286, by rfl⟩ : syracuseStep 1469715 = 2204573) B2204573
theorem B2092321 : Blo 1468554 2092321 := bstep (se 2 (by rfl) ⟨784620, by rfl⟩ : syracuseStep 2092321 = 1569241) B1569241
theorem B1469731 : Blo 1468554 1469731 := bstep (se 1 (by rfl) ⟨1102298, by rfl⟩ : syracuseStep 1469731 = 2204597) B2204597
theorem B1469747 : Blo 1468554 1469747 := bstep (se 1 (by rfl) ⟨1102310, by rfl⟩ : syracuseStep 1469747 = 2204621) B2204621
theorem B1469763 : Blo 1468554 1469763 := bstep (se 1 (by rfl) ⟨1102322, by rfl⟩ : syracuseStep 1469763 = 2204645) B2204645
theorem B1469779 : Blo 1468554 1469779 := bstep (se 1 (by rfl) ⟨1102334, by rfl⟩ : syracuseStep 1469779 = 2204669) B2204669
theorem B1469795 : Blo 1468554 1469795 := bstep (se 1 (by rfl) ⟨1102346, by rfl⟩ : syracuseStep 1469795 = 2204693) B2204693
theorem B3304817 : Blo 1468554 3304817 := bstep (se 2 (by rfl) ⟨1239306, by rfl⟩ : syracuseStep 3304817 = 2478613) B2478613
theorem B1469811 : Blo 1468554 1469811 := bstep (se 1 (by rfl) ⟨1102358, by rfl⟩ : syracuseStep 1469811 = 2204717) B2204717
theorem B3304835 : Blo 1468554 3304835 := bstep (se 1 (by rfl) ⟨2478626, by rfl⟩ : syracuseStep 3304835 = 4957253) B4957253
theorem B1469827 : Blo 1468554 1469827 := bstep (se 1 (by rfl) ⟨1102370, by rfl⟩ : syracuseStep 1469827 = 2204741) B2204741
theorem B4959629 : Blo 1468554 4959629 := bstep (se 3 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 4959629 = 1859861) B1859861
theorem B1469843 : Blo 1468554 1469843 := bstep (se 1 (by rfl) ⟨1102382, by rfl⟩ : syracuseStep 1469843 = 2204765) B2204765
theorem B1469859 : Blo 1468554 1469859 := bstep (se 1 (by rfl) ⟨1102394, by rfl⟩ : syracuseStep 1469859 = 2204789) B2204789
theorem B1469875 : Blo 1468554 1469875 := bstep (se 1 (by rfl) ⟨1102406, by rfl⟩ : syracuseStep 1469875 = 2204813) B2204813
theorem B4959683 : Blo 1468554 4959683 := bstep (se 1 (by rfl) ⟨3719762, by rfl⟩ : syracuseStep 4959683 = 7439525) B7439525
theorem B1469891 : Blo 1468554 1469891 := bstep (se 1 (by rfl) ⟨1102418, by rfl⟩ : syracuseStep 1469891 = 2204837) B2204837
theorem B1469907 : Blo 1468554 1469907 := bstep (se 1 (by rfl) ⟨1102430, by rfl⟩ : syracuseStep 1469907 = 2204861) B2204861
theorem B1469923 : Blo 1468554 1469923 := bstep (se 1 (by rfl) ⟨1102442, by rfl⟩ : syracuseStep 1469923 = 2204885) B2204885
theorem B1469939 : Blo 1468554 1469939 := bstep (se 1 (by rfl) ⟨1102454, by rfl⟩ : syracuseStep 1469939 = 2204909) B2204909
theorem B4771331 : Blo 1468554 4771331 := bstep (se 1 (by rfl) ⟨3578498, by rfl⟩ : syracuseStep 4771331 = 7156997) B7156997
theorem B1469955 : Blo 1468554 1469955 := bstep (se 1 (by rfl) ⟨1102466, by rfl⟩ : syracuseStep 1469955 = 2204933) B2204933
theorem B16748045 : Blo 1468554 16748045 := bstep (se 3 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 16748045 = 6280517) B6280517
theorem B1469971 : Blo 1468554 1469971 := bstep (se 1 (by rfl) ⟨1102478, by rfl⟩ : syracuseStep 1469971 = 2204957) B2204957
theorem B1469987 : Blo 1468554 1469987 := bstep (se 1 (by rfl) ⟨1102490, by rfl⟩ : syracuseStep 1469987 = 2204981) B2204981
theorem B7441955 : Blo 1468554 7441955 := bstep (se 1 (by rfl) ⟨5581466, by rfl⟩ : syracuseStep 7441955 = 11162933) B11162933
theorem B1470003 : Blo 1468554 1470003 := bstep (se 1 (by rfl) ⟨1102502, by rfl⟩ : syracuseStep 1470003 = 2205005) B2205005
theorem B1470019 : Blo 1468554 1470019 := bstep (se 1 (by rfl) ⟨1102514, by rfl⟩ : syracuseStep 1470019 = 2205029) B2205029
theorem B2649667 : Blo 1468554 2649667 := bstep (se 1 (by rfl) ⟨1987250, by rfl⟩ : syracuseStep 2649667 = 3974501) B3974501
theorem B1470035 : Blo 1468554 1470035 := bstep (se 1 (by rfl) ⟨1102526, by rfl⟩ : syracuseStep 1470035 = 2205053) B2205053
theorem B1470051 : Blo 1468554 1470051 := bstep (se 1 (by rfl) ⟨1102538, by rfl⟩ : syracuseStep 1470051 = 2205077) B2205077
theorem B1470067 : Blo 1468554 1470067 := bstep (se 1 (by rfl) ⟨1102550, by rfl⟩ : syracuseStep 1470067 = 2205101) B2205101
theorem B4025987 : Blo 1468554 4025987 := bstep (se 1 (by rfl) ⟨3019490, by rfl⟩ : syracuseStep 4025987 = 6038981) B6038981
theorem B1470083 : Blo 1468554 1470083 := bstep (se 1 (by rfl) ⟨1102562, by rfl⟩ : syracuseStep 1470083 = 2205125) B2205125
theorem B3305105 : Blo 1468554 3305105 := bstep (se 2 (by rfl) ⟨1239414, by rfl⟩ : syracuseStep 3305105 = 2478829) B2478829
theorem B1470099 : Blo 1468554 1470099 := bstep (se 1 (by rfl) ⟨1102574, by rfl⟩ : syracuseStep 1470099 = 2205149) B2205149
theorem B2354849 : Blo 1468554 2354849 := bstep (se 2 (by rfl) ⟨883068, by rfl⟩ : syracuseStep 2354849 = 1766137) B1766137
theorem B3305123 : Blo 1468554 3305123 := bstep (se 1 (by rfl) ⟨2478842, by rfl⟩ : syracuseStep 3305123 = 4957685) B4957685
theorem B1470115 : Blo 1468554 1470115 := bstep (se 1 (by rfl) ⟨1102586, by rfl⟩ : syracuseStep 1470115 = 2205173) B2205173
theorem B1470131 : Blo 1468554 1470131 := bstep (se 1 (by rfl) ⟨1102598, by rfl⟩ : syracuseStep 1470131 = 2205197) B2205197
theorem B1470147 : Blo 1468554 1470147 := bstep (se 1 (by rfl) ⟨1102610, by rfl⟩ : syracuseStep 1470147 = 2205221) B2205221
theorem B4959953 : Blo 1468554 4959953 := bstep (se 2 (by rfl) ⟨1859982, by rfl⟩ : syracuseStep 4959953 = 3719965) B3719965
theorem B1470163 : Blo 1468554 1470163 := bstep (se 1 (by rfl) ⟨1102622, by rfl⟩ : syracuseStep 1470163 = 2205245) B2205245
theorem B1470179 : Blo 1468554 1470179 := bstep (se 1 (by rfl) ⟨1102634, by rfl⟩ : syracuseStep 1470179 = 2205269) B2205269
theorem B1470195 : Blo 1468554 1470195 := bstep (se 1 (by rfl) ⟨1102646, by rfl⟩ : syracuseStep 1470195 = 2205293) B2205293
theorem B1470211 : Blo 1468554 1470211 := bstep (se 1 (by rfl) ⟨1102658, by rfl⟩ : syracuseStep 1470211 = 2205317) B2205317
theorem B7057165 : Blo 1468554 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B2092817 : Blo 1468554 2092817 := bstep (se 2 (by rfl) ⟨784806, by rfl⟩ : syracuseStep 2092817 = 1569613) B1569613
theorem B1470227 : Blo 1468554 1470227 := bstep (se 1 (by rfl) ⟨1102670, by rfl⟩ : syracuseStep 1470227 = 2205341) B2205341
theorem B1470243 : Blo 1468554 1470243 := bstep (se 1 (by rfl) ⟨1102682, by rfl⟩ : syracuseStep 1470243 = 2205365) B2205365
theorem B1470259 : Blo 1468554 1470259 := bstep (se 1 (by rfl) ⟨1102694, by rfl⟩ : syracuseStep 1470259 = 2205389) B2205389
theorem B1470275 : Blo 1468554 1470275 := bstep (se 1 (by rfl) ⟨1102706, by rfl⟩ : syracuseStep 1470275 = 2205413) B2205413
theorem B1470291 : Blo 1468554 1470291 := bstep (se 1 (by rfl) ⟨1102718, by rfl⟩ : syracuseStep 1470291 = 2205437) B2205437
theorem B2355041 : Blo 1468554 2355041 := bstep (se 2 (by rfl) ⟨883140, by rfl⟩ : syracuseStep 2355041 = 1766281) B1766281
theorem B1470307 : Blo 1468554 1470307 := bstep (se 1 (by rfl) ⟨1102730, by rfl⟩ : syracuseStep 1470307 = 2205461) B2205461
theorem B1470323 : Blo 1468554 1470323 := bstep (se 1 (by rfl) ⟨1102742, by rfl⟩ : syracuseStep 1470323 = 2205485) B2205485
theorem B1470339 : Blo 1468554 1470339 := bstep (se 1 (by rfl) ⟨1102754, by rfl⟩ : syracuseStep 1470339 = 2205509) B2205509
theorem B1470355 : Blo 1468554 1470355 := bstep (se 1 (by rfl) ⟨1102766, by rfl⟩ : syracuseStep 1470355 = 2205533) B2205533
theorem B1470371 : Blo 1468554 1470371 := bstep (se 1 (by rfl) ⟨1102778, by rfl⟩ : syracuseStep 1470371 = 2205557) B2205557
theorem B5025709 : Blo 1468554 5025709 := bstep (se 3 (by rfl) ⟨942320, by rfl⟩ : syracuseStep 5025709 = 1884641) B1884641
theorem B3305393 : Blo 1468554 3305393 := bstep (se 2 (by rfl) ⟨1239522, by rfl⟩ : syracuseStep 3305393 = 2479045) B2479045
theorem B1470387 : Blo 1468554 1470387 := bstep (se 1 (by rfl) ⟨1102790, by rfl⟩ : syracuseStep 1470387 = 2205581) B2205581
theorem B3305411 : Blo 1468554 3305411 := bstep (se 1 (by rfl) ⟨2479058, by rfl⟩ : syracuseStep 3305411 = 4958117) B4958117
theorem B1470403 : Blo 1468554 1470403 := bstep (se 1 (by rfl) ⟨1102802, by rfl⟩ : syracuseStep 1470403 = 2205605) B2205605
theorem B13397957 : Blo 1468554 13397957 := bstep (se 4 (by rfl) ⟨1256058, by rfl⟩ : syracuseStep 13397957 = 2512117) B2512117
theorem B2789329 : Blo 1468554 2789329 := bstep (se 2 (by rfl) ⟨1045998, by rfl⟩ : syracuseStep 2789329 = 2091997) B2091997
theorem B1470419 : Blo 1468554 1470419 := bstep (se 1 (by rfl) ⟨1102814, by rfl⟩ : syracuseStep 1470419 = 2205629) B2205629
theorem B2355169 : Blo 1468554 2355169 := bstep (se 2 (by rfl) ⟨883188, by rfl⟩ : syracuseStep 2355169 = 1766377) B1766377
theorem B9416675 : Blo 1468554 9416675 := bstep (se 1 (by rfl) ⟨7062506, by rfl⟩ : syracuseStep 9416675 = 14125013) B14125013
theorem B1470435 : Blo 1468554 1470435 := bstep (se 1 (by rfl) ⟨1102826, by rfl⟩ : syracuseStep 1470435 = 2205653) B2205653
theorem B1986547 : Blo 1468554 1986547 := bstep (se 1 (by rfl) ⟨1489910, by rfl⟩ : syracuseStep 1986547 = 2979821) B2979821
theorem B1470451 : Blo 1468554 1470451 := bstep (se 1 (by rfl) ⟨1102838, by rfl⟩ : syracuseStep 1470451 = 2205677) B2205677
theorem B1470467 : Blo 1468554 1470467 := bstep (se 1 (by rfl) ⟨1102850, by rfl⟩ : syracuseStep 1470467 = 2205701) B2205701
theorem B1470483 : Blo 1468554 1470483 := bstep (se 1 (by rfl) ⟨1102862, by rfl⟩ : syracuseStep 1470483 = 2205725) B2205725
theorem B1470499 : Blo 1468554 1470499 := bstep (se 1 (by rfl) ⟨1102874, by rfl⟩ : syracuseStep 1470499 = 2205749) B2205749
theorem B1470515 : Blo 1468554 1470515 := bstep (se 1 (by rfl) ⟨1102886, by rfl⟩ : syracuseStep 1470515 = 2205773) B2205773
theorem B1470531 : Blo 1468554 1470531 := bstep (se 1 (by rfl) ⟨1102898, by rfl⟩ : syracuseStep 1470531 = 2205797) B2205797
theorem B1470547 : Blo 1468554 1470547 := bstep (se 1 (by rfl) ⟨1102910, by rfl⟩ : syracuseStep 1470547 = 2205821) B2205821
theorem B4706417 : Blo 1468554 4706417 := bstep (se 2 (by rfl) ⟨1764906, by rfl⟩ : syracuseStep 4706417 = 3529813) B3529813
theorem B2683057 : Blo 1468554 2683057 := bstep (se 2 (by rfl) ⟨1006146, by rfl⟩ : syracuseStep 2683057 = 2012293) B2012293
theorem B2478289 : Blo 1468554 2478289 := bstep (se 2 (by rfl) ⟨929358, by rfl⟩ : syracuseStep 2478289 = 1858717) B1858717
theorem B3305681 : Blo 1468554 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B3305699 : Blo 1468554 3305699 := bstep (se 1 (by rfl) ⟨2479274, by rfl⟩ : syracuseStep 3305699 = 4958549) B4958549
theorem B4960493 : Blo 1468554 4960493 := bstep (se 3 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 4960493 = 1860185) B1860185
theorem B4706545 : Blo 1468554 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B2478323 : Blo 1468554 2478323 := bstep (se 1 (by rfl) ⟨1858742, by rfl⟩ : syracuseStep 2478323 = 3717485) B3717485
theorem B4960547 : Blo 1468554 4960547 := bstep (se 1 (by rfl) ⟨3720410, by rfl⟩ : syracuseStep 4960547 = 7440821) B7440821
theorem B7442765 : Blo 1468554 7442765 := bstep (se 3 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 7442765 = 2791037) B2791037
theorem B2789731 : Blo 1468554 2789731 := bstep (se 1 (by rfl) ⟨2092298, by rfl⟩ : syracuseStep 2789731 = 4184597) B4184597
theorem B14127473 : Blo 1468554 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B2478451 : Blo 1468554 2478451 := bstep (se 1 (by rfl) ⟨1858838, by rfl⟩ : syracuseStep 2478451 = 3717677) B3717677
theorem B2789777 : Blo 1468554 2789777 := bstep (se 2 (by rfl) ⟨1046166, by rfl⟩ : syracuseStep 2789777 = 2092333) B2092333
theorem B4706801 : Blo 1468554 4706801 := bstep (se 2 (by rfl) ⟨1765050, by rfl⟩ : syracuseStep 4706801 = 3530101) B3530101
theorem B3305969 : Blo 1468554 3305969 := bstep (se 2 (by rfl) ⟨1239738, by rfl⟩ : syracuseStep 3305969 = 2479477) B2479477
theorem B2478593 : Blo 1468554 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B3305987 : Blo 1468554 3305987 := bstep (se 1 (by rfl) ⟨2479490, by rfl⟩ : syracuseStep 3305987 = 4958981) B4958981
theorem B7156259 : Blo 1468554 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B4960817 : Blo 1468554 4960817 := bstep (se 2 (by rfl) ⟨1860306, by rfl⟩ : syracuseStep 4960817 = 3720613) B3720613
theorem B1569395 : Blo 1468554 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B2093683 : Blo 1468554 2093683 := bstep (se 1 (by rfl) ⟨1570262, by rfl⟩ : syracuseStep 2093683 = 3140525) B3140525
theorem B2478721 : Blo 1468554 2478721 := bstep (se 2 (by rfl) ⟨929520, by rfl⟩ : syracuseStep 2478721 = 1859041) B1859041
theorem B2683523 : Blo 1468554 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B2478755 : Blo 1468554 2478755 := bstep (se 1 (by rfl) ⟨1859066, by rfl⟩ : syracuseStep 2478755 = 3718133) B3718133
theorem B2790065 : Blo 1468554 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B2093779 : Blo 1468554 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B6124301 : Blo 1468554 6124301 := bstep (se 3 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 6124301 = 2296613) B2296613
theorem B3306257 : Blo 1468554 3306257 := bstep (se 2 (by rfl) ⟨1239846, by rfl⟩ : syracuseStep 3306257 = 2479693) B2479693
theorem B2478883 : Blo 1468554 2478883 := bstep (se 1 (by rfl) ⟨1859162, by rfl⟩ : syracuseStep 2478883 = 3718325) B3718325
theorem B3306275 : Blo 1468554 3306275 := bstep (se 1 (by rfl) ⟨2479706, by rfl⟩ : syracuseStep 3306275 = 4959413) B4959413
theorem B5657485 : Blo 1468554 5657485 := bstep (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) B2121557
theorem B7058339 : Blo 1468554 7058339 := bstep (se 1 (by rfl) ⟨5293754, by rfl⟩ : syracuseStep 7058339 = 10587509) B10587509
theorem B2479025 : Blo 1468554 2479025 := bstep (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) B1859269
theorem B7435313 : Blo 1468554 7435313 := bstep (se 2 (by rfl) ⟨2788242, by rfl⟩ : syracuseStep 7435313 = 5576485) B5576485
theorem B2479153 : Blo 1468554 2479153 := bstep (se 2 (by rfl) ⟨929682, by rfl⟩ : syracuseStep 2479153 = 1859365) B1859365
theorem B3306545 : Blo 1468554 3306545 := bstep (se 2 (by rfl) ⟨1239954, by rfl⟩ : syracuseStep 3306545 = 2479909) B2479909
theorem B67875893 : Blo 1468554 67875893 := bstep (se 5 (by rfl) ⟨3181682, by rfl⟩ : syracuseStep 67875893 = 6363365) B6363365
theorem B3306563 : Blo 1468554 3306563 := bstep (se 1 (by rfl) ⟨2479922, by rfl⟩ : syracuseStep 3306563 = 4959845) B4959845
theorem B4961357 : Blo 1468554 4961357 := bstep (se 3 (by rfl) ⟨930254, by rfl⟩ : syracuseStep 4961357 = 1860509) B1860509
theorem B2479187 : Blo 1468554 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B4183139 : Blo 1468554 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B1676387 : Blo 1468554 1676387 := bstep (se 1 (by rfl) ⟨1257290, by rfl⟩ : syracuseStep 1676387 = 2514581) B2514581
theorem B4961411 : Blo 1468554 4961411 := bstep (se 1 (by rfl) ⟨3721058, by rfl⟩ : syracuseStep 4961411 = 7442117) B7442117
theorem B2479315 : Blo 1468554 2479315 := bstep (se 1 (by rfl) ⟨1859486, by rfl⟩ : syracuseStep 2479315 = 3718973) B3718973
theorem B6124835 : Blo 1468554 6124835 := bstep (se 1 (by rfl) ⟨4593626, by rfl⟩ : syracuseStep 6124835 = 9187253) B9187253
theorem B5575985 : Blo 1468554 5575985 := bstep (se 2 (by rfl) ⟨2090994, by rfl⟩ : syracuseStep 5575985 = 4181989) B4181989
theorem B3306833 : Blo 1468554 3306833 := bstep (se 2 (by rfl) ⟨1240062, by rfl⟩ : syracuseStep 3306833 = 2480125) B2480125
theorem B2479457 : Blo 1468554 2479457 := bstep (se 2 (by rfl) ⟨929796, by rfl⟩ : syracuseStep 2479457 = 1859593) B1859593
theorem B3306851 : Blo 1468554 3306851 := bstep (se 1 (by rfl) ⟨2480138, by rfl⟩ : syracuseStep 3306851 = 4960277) B4960277
theorem B2790787 : Blo 1468554 2790787 := bstep (se 1 (by rfl) ⟨2093090, by rfl⟩ : syracuseStep 2790787 = 4186181) B4186181
theorem B77362573 : Blo 1468554 77362573 := bstep (se 3 (by rfl) ⟨14505482, by rfl⟩ : syracuseStep 77362573 = 29010965) B29010965
theorem B4961681 : Blo 1468554 4961681 := bstep (se 2 (by rfl) ⟨1860630, by rfl⟩ : syracuseStep 4961681 = 3721261) B3721261
theorem B1652179 : Blo 1468554 1652179 := bstep (se 1 (by rfl) ⟨1239134, by rfl⟩ : syracuseStep 1652179 = 2478269) B2478269
theorem B2479585 : Blo 1468554 2479585 := bstep (se 2 (by rfl) ⟨929844, by rfl⟩ : syracuseStep 2479585 = 1859689) B1859689
theorem B7648739 : Blo 1468554 7648739 := bstep (se 1 (by rfl) ⟨5736554, by rfl⟩ : syracuseStep 7648739 = 11473109) B11473109
theorem B2479619 : Blo 1468554 2479619 := bstep (se 1 (by rfl) ⟨1859714, by rfl⟩ : syracuseStep 2479619 = 3719429) B3719429
theorem B10057229 : Blo 1468554 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B1652323 : Blo 1468554 1652323 := bstep (se 1 (by rfl) ⟨1239242, by rfl⟩ : syracuseStep 1652323 = 2478485) B2478485
theorem B2233955 : Blo 1468554 2233955 := bstep (se 1 (by rfl) ⟨1675466, by rfl⟩ : syracuseStep 2233955 = 3350933) B3350933
theorem B3307121 : Blo 1468554 3307121 := bstep (se 2 (by rfl) ⟨1240170, by rfl⟩ : syracuseStep 3307121 = 2480341) B2480341
theorem B2479747 : Blo 1468554 2479747 := bstep (se 1 (by rfl) ⟨1859810, by rfl⟩ : syracuseStep 2479747 = 3719621) B3719621
theorem B3307139 : Blo 1468554 3307139 := bstep (se 1 (by rfl) ⟨2480354, by rfl⟩ : syracuseStep 3307139 = 4960709) B4960709
theorem B8943331 : Blo 1468554 8943331 := bstep (se 1 (by rfl) ⟨6707498, by rfl⟩ : syracuseStep 8943331 = 13414997) B13414997
theorem B1652467 : Blo 1468554 1652467 := bstep (se 1 (by rfl) ⟨1239350, by rfl⟩ : syracuseStep 1652467 = 2478701) B2478701
theorem B2479889 : Blo 1468554 2479889 := bstep (se 2 (by rfl) ⟨929958, by rfl⟩ : syracuseStep 2479889 = 1859917) B1859917
theorem B2791235 : Blo 1468554 2791235 := bstep (se 1 (by rfl) ⟨2093426, by rfl⟩ : syracuseStep 2791235 = 4186853) B4186853
theorem B16742213 : Blo 1468554 16742213 := bstep (se 4 (by rfl) ⟨1569582, by rfl⟩ : syracuseStep 16742213 = 3139165) B3139165
theorem B2234209 : Blo 1468554 2234209 := bstep (se 2 (by rfl) ⟨837828, by rfl⟩ : syracuseStep 2234209 = 1675657) B1675657
theorem B1652611 : Blo 1468554 1652611 := bstep (se 1 (by rfl) ⟨1239458, by rfl⟩ : syracuseStep 1652611 = 2478917) B2478917
theorem B8484749 : Blo 1468554 8484749 := bstep (se 3 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 8484749 = 3181781) B3181781
theorem B2480017 : Blo 1468554 2480017 := bstep (se 2 (by rfl) ⟨930006, by rfl⟩ : syracuseStep 2480017 = 1860013) B1860013
theorem B3307409 : Blo 1468554 3307409 := bstep (se 2 (by rfl) ⟨1240278, by rfl⟩ : syracuseStep 3307409 = 2480557) B2480557
theorem B3307427 : Blo 1468554 3307427 := bstep (se 1 (by rfl) ⟨2480570, by rfl⟩ : syracuseStep 3307427 = 4961141) B4961141
theorem B4962221 : Blo 1468554 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B2480051 : Blo 1468554 2480051 := bstep (se 1 (by rfl) ⟨1860038, by rfl⟩ : syracuseStep 2480051 = 3720077) B3720077
theorem B8935373 : Blo 1468554 8935373 := bstep (se 3 (by rfl) ⟨1675382, by rfl⟩ : syracuseStep 8935373 = 3350765) B3350765
theorem B4962275 : Blo 1468554 4962275 := bstep (se 1 (by rfl) ⟨3721706, by rfl⟩ : syracuseStep 4962275 = 7443413) B7443413
theorem B6281201 : Blo 1468554 6281201 := bstep (se 2 (by rfl) ⟨2355450, by rfl⟩ : syracuseStep 6281201 = 4710901) B4710901
theorem B1652755 : Blo 1468554 1652755 := bstep (se 1 (by rfl) ⟨1239566, by rfl⟩ : syracuseStep 1652755 = 2479133) B2479133
theorem B2480179 : Blo 1468554 2480179 := bstep (se 1 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 2480179 = 3720269) B3720269
theorem B3528785 : Blo 1468554 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B2791523 : Blo 1468554 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B4708493 : Blo 1468554 4708493 := bstep (se 3 (by rfl) ⟨882842, by rfl⟩ : syracuseStep 4708493 = 1765685) B1765685
theorem B1652899 : Blo 1468554 1652899 := bstep (se 1 (by rfl) ⟨1239674, by rfl⟩ : syracuseStep 1652899 = 2479349) B2479349
theorem B3307697 : Blo 1468554 3307697 := bstep (se 2 (by rfl) ⟨1240386, by rfl⟩ : syracuseStep 3307697 = 2480773) B2480773
theorem B5814449 : Blo 1468554 5814449 := bstep (se 2 (by rfl) ⟨2180418, by rfl⟩ : syracuseStep 5814449 = 4360837) B4360837
theorem B2480321 : Blo 1468554 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B3307715 : Blo 1468554 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B2513123 : Blo 1468554 2513123 := bstep (se 1 (by rfl) ⟨1884842, by rfl⟩ : syracuseStep 2513123 = 3769685) B3769685
theorem B4962545 : Blo 1468554 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B4184369 : Blo 1468554 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B1653043 : Blo 1468554 1653043 := bstep (se 1 (by rfl) ⟨1239782, by rfl⟩ : syracuseStep 1653043 = 2479565) B2479565
theorem B2480449 : Blo 1468554 2480449 := bstep (se 2 (by rfl) ⟨930168, by rfl⟩ : syracuseStep 2480449 = 1860337) B1860337
theorem B10590533 : Blo 1468554 10590533 := bstep (se 4 (by rfl) ⟨992862, by rfl⟩ : syracuseStep 10590533 = 1985725) B1985725
theorem B14129477 : Blo 1468554 14129477 := bstep (se 4 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 14129477 = 2649277) B2649277
theorem B2480483 : Blo 1468554 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B2685329 : Blo 1468554 2685329 := bstep (se 2 (by rfl) ⟨1006998, by rfl⟩ : syracuseStep 2685329 = 2013997) B2013997
theorem B1653187 : Blo 1468554 1653187 := bstep (se 1 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 1653187 = 2479781) B2479781
theorem B3307985 : Blo 1468554 3307985 := bstep (se 2 (by rfl) ⟨1240494, by rfl⟩ : syracuseStep 3307985 = 2480989) B2480989
theorem B7436771 : Blo 1468554 7436771 := bstep (se 1 (by rfl) ⟨5577578, by rfl⟩ : syracuseStep 7436771 = 11155157) B11155157
theorem B2480611 : Blo 1468554 2480611 := bstep (se 1 (by rfl) ⟨1860458, by rfl⟩ : syracuseStep 2480611 = 3720917) B3720917
theorem B3308003 : Blo 1468554 3308003 := bstep (se 1 (by rfl) ⟨2481002, by rfl⟩ : syracuseStep 3308003 = 4962005) B4962005
theorem B9419341 : Blo 1468554 9419341 := bstep (se 3 (by rfl) ⟨1766126, by rfl⟩ : syracuseStep 9419341 = 3532253) B3532253
theorem B1653331 : Blo 1468554 1653331 := bstep (se 1 (by rfl) ⟨1239998, by rfl⟩ : syracuseStep 1653331 = 2479997) B2479997
theorem B2480753 : Blo 1468554 2480753 := bstep (se 2 (by rfl) ⟨930282, by rfl⟩ : syracuseStep 2480753 = 1860565) B1860565
theorem B3717809 : Blo 1468554 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B3717859 : Blo 1468554 3717859 := bstep (se 1 (by rfl) ⟨2788394, by rfl⟩ : syracuseStep 3717859 = 5576789) B5576789
theorem B5577443 : Blo 1468554 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B1653475 : Blo 1468554 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B5577457 : Blo 1468554 5577457 := bstep (se 2 (by rfl) ⟨2091546, by rfl⟩ : syracuseStep 5577457 = 4183093) B4183093
theorem B2480881 : Blo 1468554 2480881 := bstep (se 2 (by rfl) ⟨930330, by rfl⟩ : syracuseStep 2480881 = 1860661) B1860661
theorem B3308273 : Blo 1468554 3308273 := bstep (se 2 (by rfl) ⟨1240602, by rfl⟩ : syracuseStep 3308273 = 2481205) B2481205
theorem B3308291 : Blo 1468554 3308291 := bstep (se 1 (by rfl) ⟨2481218, by rfl⟩ : syracuseStep 3308291 = 4962437) B4962437
theorem B4963085 : Blo 1468554 4963085 := bstep (se 3 (by rfl) ⟨930578, by rfl⟩ : syracuseStep 4963085 = 1861157) B1861157
theorem B2480915 : Blo 1468554 2480915 := bstep (se 1 (by rfl) ⟨1860686, by rfl⟩ : syracuseStep 2480915 = 3721373) B3721373
theorem B3718001 : Blo 1468554 3718001 := bstep (se 2 (by rfl) ⟨1394250, by rfl⟩ : syracuseStep 3718001 = 2788501) B2788501
theorem B1653619 : Blo 1468554 1653619 := bstep (se 1 (by rfl) ⟨1240214, by rfl⟩ : syracuseStep 1653619 = 2480429) B2480429
theorem B4709261 : Blo 1468554 4709261 := bstep (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) B1765973
theorem B2481043 : Blo 1468554 2481043 := bstep (se 1 (by rfl) ⟨1860782, by rfl⟩ : syracuseStep 2481043 = 3721565) B3721565
theorem B1653763 : Blo 1468554 1653763 := bstep (se 1 (by rfl) ⟨1240322, by rfl⟩ : syracuseStep 1653763 = 2480645) B2480645
theorem B3308561 : Blo 1468554 3308561 := bstep (se 2 (by rfl) ⟨1240710, by rfl⟩ : syracuseStep 3308561 = 2481421) B2481421
theorem B6036515 : Blo 1468554 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B2481185 : Blo 1468554 2481185 := bstep (se 2 (by rfl) ⟨930444, by rfl⟩ : syracuseStep 2481185 = 1860889) B1860889
theorem B3308579 : Blo 1468554 3308579 := bstep (se 1 (by rfl) ⟨2481434, by rfl⟩ : syracuseStep 3308579 = 4962869) B4962869
theorem B2235443 : Blo 1468554 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B9411653 : Blo 1468554 9411653 := bstep (se 4 (by rfl) ⟨882342, by rfl⟩ : syracuseStep 9411653 = 1764685) B1764685
theorem B5028941 : Blo 1468554 5028941 := bstep (se 3 (by rfl) ⟨942926, by rfl⟩ : syracuseStep 5028941 = 1885853) B1885853
theorem B15285347 : Blo 1468554 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B58834033 : Blo 1468554 58834033 := bstep (se 2 (by rfl) ⟨22062762, by rfl⟩ : syracuseStep 58834033 = 44125525) B44125525
theorem B1653907 : Blo 1468554 1653907 := bstep (se 1 (by rfl) ⟨1240430, by rfl⟩ : syracuseStep 1653907 = 2480861) B2480861
theorem B2481313 : Blo 1468554 2481313 := bstep (se 2 (by rfl) ⟨930492, by rfl⟩ : syracuseStep 2481313 = 1860985) B1860985
theorem B2481347 : Blo 1468554 2481347 := bstep (se 1 (by rfl) ⟨1861010, by rfl⟩ : syracuseStep 2481347 = 3722021) B3722021
theorem B2202833 : Blo 1468554 2202833 := bstep (se 2 (by rfl) ⟨826062, by rfl⟩ : syracuseStep 2202833 = 1652125) B1652125
theorem B2202851 : Blo 1468554 2202851 := bstep (se 1 (by rfl) ⟨1652138, by rfl⟩ : syracuseStep 2202851 = 3304277) B3304277
theorem B3349745 : Blo 1468554 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B2202881 : Blo 1468554 2202881 := bstep (se 2 (by rfl) ⟨826080, by rfl⟩ : syracuseStep 2202881 = 1652161) B1652161
theorem B3349763 : Blo 1468554 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B7437581 : Blo 1468554 7437581 := bstep (se 3 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 7437581 = 2789093) B2789093
theorem B2202899 : Blo 1468554 2202899 := bstep (se 1 (by rfl) ⟨1652174, by rfl⟩ : syracuseStep 2202899 = 3304349) B3304349
theorem B1654051 : Blo 1468554 1654051 := bstep (se 1 (by rfl) ⟨1240538, by rfl⟩ : syracuseStep 1654051 = 2481077) B2481077
theorem B2202929 : Blo 1468554 2202929 := bstep (se 2 (by rfl) ⟨826098, by rfl⟩ : syracuseStep 2202929 = 1652197) B1652197
theorem B2202947 : Blo 1468554 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B1490243 : Blo 1468554 1490243 := bstep (se 1 (by rfl) ⟨1117682, by rfl⟩ : syracuseStep 1490243 = 2235365) B2235365
theorem B2481475 : Blo 1468554 2481475 := bstep (se 1 (by rfl) ⟨1861106, by rfl⟩ : syracuseStep 2481475 = 3722213) B3722213
theorem B2202977 : Blo 1468554 2202977 := bstep (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) B1652233
theorem B2866531 : Blo 1468554 2866531 := bstep (se 1 (by rfl) ⟨2149898, by rfl⟩ : syracuseStep 2866531 = 4299797) B4299797
theorem B2202995 : Blo 1468554 2202995 := bstep (se 1 (by rfl) ⟨1652246, by rfl⟩ : syracuseStep 2202995 = 3304493) B3304493
theorem B4709773 : Blo 1468554 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B10599821 : Blo 1468554 10599821 := bstep (se 3 (by rfl) ⟨1987466, by rfl⟩ : syracuseStep 10599821 = 3974933) B3974933
theorem B2203025 : Blo 1468554 2203025 := bstep (se 2 (by rfl) ⟨826134, by rfl⟩ : syracuseStep 2203025 = 1652269) B1652269
theorem B2203043 : Blo 1468554 2203043 := bstep (se 1 (by rfl) ⟨1652282, by rfl⟩ : syracuseStep 2203043 = 3304565) B3304565
theorem B2866595 : Blo 1468554 2866595 := bstep (se 1 (by rfl) ⟨2149946, by rfl⟩ : syracuseStep 2866595 = 4299893) B4299893
theorem B1654195 : Blo 1468554 1654195 := bstep (se 1 (by rfl) ⟨1240646, by rfl⟩ : syracuseStep 1654195 = 2481293) B2481293
theorem B2203073 : Blo 1468554 2203073 := bstep (se 2 (by rfl) ⟨826152, by rfl⟩ : syracuseStep 2203073 = 1652305) B1652305
theorem B2203091 : Blo 1468554 2203091 := bstep (se 1 (by rfl) ⟨1652318, by rfl⟩ : syracuseStep 2203091 = 3304637) B3304637
theorem B13401571 : Blo 1468554 13401571 := bstep (se 1 (by rfl) ⟨10051178, by rfl⟩ : syracuseStep 13401571 = 20102357) B20102357
theorem B2203121 : Blo 1468554 2203121 := bstep (se 2 (by rfl) ⟨826170, by rfl⟩ : syracuseStep 2203121 = 1652341) B1652341
theorem B2203139 : Blo 1468554 2203139 := bstep (se 1 (by rfl) ⟨1652354, by rfl⟩ : syracuseStep 2203139 = 3304709) B3304709
theorem B2203169 : Blo 1468554 2203169 := bstep (se 2 (by rfl) ⟨826188, by rfl⟩ : syracuseStep 2203169 = 1652377) B1652377
theorem B1859107 : Blo 1468554 1859107 := bstep (se 1 (by rfl) ⟨1394330, by rfl⟩ : syracuseStep 1859107 = 2788661) B2788661
theorem B2203187 : Blo 1468554 2203187 := bstep (se 1 (by rfl) ⟨1652390, by rfl⟩ : syracuseStep 2203187 = 3304781) B3304781
theorem B1654339 : Blo 1468554 1654339 := bstep (se 1 (by rfl) ⟨1240754, by rfl⟩ : syracuseStep 1654339 = 2481509) B2481509
theorem B2203217 : Blo 1468554 2203217 := bstep (se 2 (by rfl) ⟨826206, by rfl⟩ : syracuseStep 2203217 = 1652413) B1652413
theorem B2203235 : Blo 1468554 2203235 := bstep (se 1 (by rfl) ⟨1652426, by rfl⟩ : syracuseStep 2203235 = 3304853) B3304853
theorem B2203265 : Blo 1468554 2203265 := bstep (se 2 (by rfl) ⟨826224, by rfl⟩ : syracuseStep 2203265 = 1652449) B1652449
theorem B1859203 : Blo 1468554 1859203 := bstep (se 1 (by rfl) ⟨1394402, by rfl⟩ : syracuseStep 1859203 = 2788805) B2788805
theorem B2203283 : Blo 1468554 2203283 := bstep (se 1 (by rfl) ⟨1652462, by rfl⟩ : syracuseStep 2203283 = 3304925) B3304925
theorem B2203313 : Blo 1468554 2203313 := bstep (se 2 (by rfl) ⟨826242, by rfl⟩ : syracuseStep 2203313 = 1652485) B1652485
theorem B3137201 : Blo 1468554 3137201 := bstep (se 2 (by rfl) ⟨1176450, by rfl⟩ : syracuseStep 3137201 = 2352901) B2352901
theorem B2203331 : Blo 1468554 2203331 := bstep (se 1 (by rfl) ⟨1652498, by rfl⟩ : syracuseStep 2203331 = 3304997) B3304997
theorem B2203361 : Blo 1468554 2203361 := bstep (se 2 (by rfl) ⟨826260, by rfl⟩ : syracuseStep 2203361 = 1652521) B1652521
theorem B35741411 : Blo 1468554 35741411 := bstep (se 1 (by rfl) ⟨26806058, by rfl⟩ : syracuseStep 35741411 = 53612117) B53612117
theorem B4185827 : Blo 1468554 4185827 := bstep (se 1 (by rfl) ⟨3139370, by rfl⟩ : syracuseStep 4185827 = 6278741) B6278741
theorem B2203379 : Blo 1468554 2203379 := bstep (se 1 (by rfl) ⟨1652534, by rfl⟩ : syracuseStep 2203379 = 3305069) B3305069
theorem B2203409 : Blo 1468554 2203409 := bstep (se 2 (by rfl) ⟨826278, by rfl⟩ : syracuseStep 2203409 = 1652557) B1652557
theorem B2203427 : Blo 1468554 2203427 := bstep (se 1 (by rfl) ⟨1652570, by rfl⟩ : syracuseStep 2203427 = 3305141) B3305141
theorem B2203457 : Blo 1468554 2203457 := bstep (se 2 (by rfl) ⟨826296, by rfl⟩ : syracuseStep 2203457 = 1652593) B1652593
theorem B6700877 : Blo 1468554 6700877 := bstep (se 3 (by rfl) ⟨1256414, by rfl⟩ : syracuseStep 6700877 = 2512829) B2512829
theorem B3718993 : Blo 1468554 3718993 := bstep (se 2 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 3718993 = 2789245) B2789245
theorem B2203475 : Blo 1468554 2203475 := bstep (se 1 (by rfl) ⟨1652606, by rfl⟩ : syracuseStep 2203475 = 3305213) B3305213
theorem B2203505 : Blo 1468554 2203505 := bstep (se 2 (by rfl) ⟨826314, by rfl⟩ : syracuseStep 2203505 = 1652629) B1652629
theorem B2203523 : Blo 1468554 2203523 := bstep (se 1 (by rfl) ⟨1652642, by rfl⟩ : syracuseStep 2203523 = 3305285) B3305285
theorem B4710275 : Blo 1468554 4710275 := bstep (se 1 (by rfl) ⟨3532706, by rfl⟩ : syracuseStep 4710275 = 7065413) B7065413
theorem B7077773 : Blo 1468554 7077773 := bstep (se 3 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 7077773 = 2654165) B2654165
theorem B2203553 : Blo 1468554 2203553 := bstep (se 2 (by rfl) ⟨826332, by rfl⟩ : syracuseStep 2203553 = 1652665) B1652665
theorem B2203571 : Blo 1468554 2203571 := bstep (se 1 (by rfl) ⟨1652678, by rfl⟩ : syracuseStep 2203571 = 3305357) B3305357
theorem B2826193 : Blo 1468554 2826193 := bstep (se 2 (by rfl) ⟨1059822, by rfl⟩ : syracuseStep 2826193 = 2119645) B2119645
theorem B2203601 : Blo 1468554 2203601 := bstep (se 2 (by rfl) ⟨826350, by rfl⟩ : syracuseStep 2203601 = 1652701) B1652701
theorem B2203619 : Blo 1468554 2203619 := bstep (se 1 (by rfl) ⟨1652714, by rfl⟩ : syracuseStep 2203619 = 3305429) B3305429
theorem B2203673 : Blo 1468554 2203673 := bstep (se 2 (by rfl) ⟨826377, by rfl⟩ : syracuseStep 2203673 = 1652755) B1652755
theorem B3137611 : Blo 1468554 3137611 := bstep (se 1 (by rfl) ⟨2353208, by rfl⟩ : syracuseStep 3137611 = 4706417) B4706417
theorem B2203787 : Blo 1468554 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B2203799 : Blo 1468554 2203799 := bstep (se 1 (by rfl) ⟨1652849, by rfl⟩ : syracuseStep 2203799 = 3305699) B3305699
theorem B4710593 : Blo 1468554 4710593 := bstep (se 2 (by rfl) ⟨1766472, by rfl⟩ : syracuseStep 4710593 = 3532945) B3532945
theorem B11911373 : Blo 1468554 11911373 := bstep (se 3 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 11911373 = 4466765) B4466765
theorem B2203865 : Blo 1468554 2203865 := bstep (se 2 (by rfl) ⟨826449, by rfl⟩ : syracuseStep 2203865 = 1652899) B1652899
theorem B7438553 : Blo 1468554 7438553 := bstep (se 2 (by rfl) ⟨2789457, by rfl⟩ : syracuseStep 7438553 = 5578915) B5578915
theorem B1859851 : Blo 1468554 1859851 := bstep (se 1 (by rfl) ⟨1394888, by rfl⟩ : syracuseStep 1859851 = 2789777) B2789777
theorem B6275393 : Blo 1468554 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B3137867 : Blo 1468554 3137867 := bstep (se 1 (by rfl) ⟨2353400, by rfl⟩ : syracuseStep 3137867 = 4706801) B4706801
theorem B2203979 : Blo 1468554 2203979 := bstep (se 1 (by rfl) ⟨1652984, by rfl⟩ : syracuseStep 2203979 = 3305969) B3305969
theorem B2203991 : Blo 1468554 2203991 := bstep (se 1 (by rfl) ⟨1652993, by rfl⟩ : syracuseStep 2203991 = 3305987) B3305987
theorem B2204057 : Blo 1468554 2204057 := bstep (se 2 (by rfl) ⟨826521, by rfl⟩ : syracuseStep 2204057 = 1653043) B1653043
theorem B3719641 : Blo 1468554 3719641 := bstep (se 2 (by rfl) ⟨1394865, by rfl⟩ : syracuseStep 3719641 = 2789731) B2789731
theorem B2204171 : Blo 1468554 2204171 := bstep (se 1 (by rfl) ⟨1653128, by rfl⟩ : syracuseStep 2204171 = 3306257) B3306257
theorem B2204183 : Blo 1468554 2204183 := bstep (se 1 (by rfl) ⟨1653137, by rfl⟩ : syracuseStep 2204183 = 3306275) B3306275
theorem B2646553 : Blo 1468554 2646553 := bstep (se 2 (by rfl) ⟨992457, by rfl⟩ : syracuseStep 2646553 = 1984915) B1984915
theorem B14123555 : Blo 1468554 14123555 := bstep (se 1 (by rfl) ⟨10592666, by rfl⟩ : syracuseStep 14123555 = 21185333) B21185333
theorem B2204249 : Blo 1468554 2204249 := bstep (se 2 (by rfl) ⟨826593, by rfl⟩ : syracuseStep 2204249 = 1653187) B1653187
theorem B4956875 : Blo 1468554 4956875 := bstep (se 1 (by rfl) ⟨3717656, by rfl⟩ : syracuseStep 4956875 = 7435313) B7435313
theorem B2204363 : Blo 1468554 2204363 := bstep (se 1 (by rfl) ⟨1653272, by rfl⟩ : syracuseStep 2204363 = 3306545) B3306545
theorem B2204375 : Blo 1468554 2204375 := bstep (se 1 (by rfl) ⟨1653281, by rfl⟩ : syracuseStep 2204375 = 3306563) B3306563
theorem B12559121 : Blo 1468554 12559121 := bstep (se 2 (by rfl) ⟨4709670, by rfl⟩ : syracuseStep 12559121 = 9419341) B9419341
theorem B2204441 : Blo 1468554 2204441 := bstep (se 2 (by rfl) ⟨826665, by rfl⟩ : syracuseStep 2204441 = 1653331) B1653331
theorem B3973981 : Blo 1468554 3973981 := bstep (se 3 (by rfl) ⟨745121, by rfl⟩ : syracuseStep 3973981 = 1490243) B1490243
theorem B2204555 : Blo 1468554 2204555 := bstep (se 1 (by rfl) ⟨1653416, by rfl⟩ : syracuseStep 2204555 = 3306833) B3306833
theorem B2204567 : Blo 1468554 2204567 := bstep (se 1 (by rfl) ⟨1653425, by rfl⟩ : syracuseStep 2204567 = 3306851) B3306851
theorem B4957145 : Blo 1468554 4957145 := bstep (se 2 (by rfl) ⟨1858929, by rfl⟩ : syracuseStep 4957145 = 3717859) B3717859
theorem B2204633 : Blo 1468554 2204633 := bstep (se 2 (by rfl) ⟨826737, by rfl⟩ : syracuseStep 2204633 = 1653475) B1653475
theorem B2204747 : Blo 1468554 2204747 := bstep (se 1 (by rfl) ⟨1653560, by rfl⟩ : syracuseStep 2204747 = 3307121) B3307121
theorem B2204759 : Blo 1468554 2204759 := bstep (se 1 (by rfl) ⟨1653569, by rfl⟩ : syracuseStep 2204759 = 3307139) B3307139
theorem B7644253 : Blo 1468554 7644253 := bstep (se 3 (by rfl) ⟨1433297, by rfl⟩ : syracuseStep 7644253 = 2866595) B2866595
theorem B11166821 : Blo 1468554 11166821 := bstep (se 4 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 11166821 = 2093779) B2093779
theorem B2204825 : Blo 1468554 2204825 := bstep (se 2 (by rfl) ⟨826809, by rfl⟩ : syracuseStep 2204825 = 1653619) B1653619
theorem B1860823 : Blo 1468554 1860823 := bstep (se 1 (by rfl) ⟨1395617, by rfl⟩ : syracuseStep 1860823 = 2791235) B2791235
theorem B2204939 : Blo 1468554 2204939 := bstep (se 1 (by rfl) ⟨1653704, by rfl⟩ : syracuseStep 2204939 = 3307409) B3307409
theorem B2204951 : Blo 1468554 2204951 := bstep (se 1 (by rfl) ⟨1653713, by rfl⟩ : syracuseStep 2204951 = 3307427) B3307427
theorem B3138841 : Blo 1468554 3138841 := bstep (se 2 (by rfl) ⟨1177065, by rfl⟩ : syracuseStep 3138841 = 2354131) B2354131
theorem B5956915 : Blo 1468554 5956915 := bstep (se 1 (by rfl) ⟨4467686, by rfl⟩ : syracuseStep 5956915 = 8935373) B8935373
theorem B4187467 : Blo 1468554 4187467 := bstep (se 1 (by rfl) ⟨3140600, by rfl⟩ : syracuseStep 4187467 = 6281201) B6281201
theorem B2205017 : Blo 1468554 2205017 := bstep (se 2 (by rfl) ⟨826881, by rfl⟩ : syracuseStep 2205017 = 1653763) B1653763
theorem B3138995 : Blo 1468554 3138995 := bstep (se 1 (by rfl) ⟨2354246, by rfl⟩ : syracuseStep 3138995 = 4708493) B4708493
theorem B2647489 : Blo 1468554 2647489 := bstep (se 2 (by rfl) ⟨992808, by rfl⟩ : syracuseStep 2647489 = 1985617) B1985617
theorem B2205131 : Blo 1468554 2205131 := bstep (se 1 (by rfl) ⟨1653848, by rfl⟩ : syracuseStep 2205131 = 3307697) B3307697
theorem B3876299 : Blo 1468554 3876299 := bstep (se 1 (by rfl) ⟨2907224, by rfl⟩ : syracuseStep 3876299 = 5814449) B5814449
theorem B2205143 : Blo 1468554 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B11159045 : Blo 1468554 11159045 := bstep (se 4 (by rfl) ⟨1046160, by rfl⟩ : syracuseStep 11159045 = 2092321) B2092321
theorem B2205209 : Blo 1468554 2205209 := bstep (se 2 (by rfl) ⟨826953, by rfl⟩ : syracuseStep 2205209 = 1653907) B1653907
theorem B3720755 : Blo 1468554 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B1885771 : Blo 1468554 1885771 := bstep (se 1 (by rfl) ⟨1414328, by rfl⟩ : syracuseStep 1885771 = 2828657) B2828657
theorem B2205323 : Blo 1468554 2205323 := bstep (se 1 (by rfl) ⟨1653992, by rfl⟩ : syracuseStep 2205323 = 3307985) B3307985
theorem B4957847 : Blo 1468554 4957847 := bstep (se 1 (by rfl) ⟨3718385, by rfl⟩ : syracuseStep 4957847 = 7436771) B7436771
theorem B2205335 : Blo 1468554 2205335 := bstep (se 1 (by rfl) ⟨1654001, by rfl⟩ : syracuseStep 2205335 = 3308003) B3308003
theorem B6276811 : Blo 1468554 6276811 := bstep (se 1 (by rfl) ⟨4707608, by rfl⟩ : syracuseStep 6276811 = 9415217) B9415217
theorem B2205401 : Blo 1468554 2205401 := bstep (se 2 (by rfl) ⟨827025, by rfl⟩ : syracuseStep 2205401 = 1654051) B1654051
theorem B7440173 : Blo 1468554 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B2205515 : Blo 1468554 2205515 := bstep (se 1 (by rfl) ⟨1654136, by rfl⟩ : syracuseStep 2205515 = 3308273) B3308273
theorem B2205527 : Blo 1468554 2205527 := bstep (se 1 (by rfl) ⟨1654145, by rfl⟩ : syracuseStep 2205527 = 3308291) B3308291
theorem B3721049 : Blo 1468554 3721049 := bstep (se 2 (by rfl) ⟨1395393, by rfl⟩ : syracuseStep 3721049 = 2790787) B2790787
theorem B2205593 : Blo 1468554 2205593 := bstep (se 2 (by rfl) ⟨827097, by rfl⟩ : syracuseStep 2205593 = 1654195) B1654195
theorem B3139507 : Blo 1468554 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B17868761 : Blo 1468554 17868761 := bstep (se 2 (by rfl) ⟨6700785, by rfl⟩ : syracuseStep 17868761 = 13401571) B13401571
theorem B6277085 : Blo 1468554 6277085 := bstep (se 3 (by rfl) ⟨1176953, by rfl⟩ : syracuseStep 6277085 = 2353907) B2353907
theorem B2205707 : Blo 1468554 2205707 := bstep (se 1 (by rfl) ⟨1654280, by rfl⟩ : syracuseStep 2205707 = 3308561) B3308561
theorem B4024343 : Blo 1468554 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B2205719 : Blo 1468554 2205719 := bstep (se 1 (by rfl) ⟨1654289, by rfl⟩ : syracuseStep 2205719 = 3308579) B3308579
theorem B5580845 : Blo 1468554 5580845 := bstep (se 3 (by rfl) ⟨1046408, by rfl⟩ : syracuseStep 5580845 = 2092817) B2092817
theorem B3352627 : Blo 1468554 3352627 := bstep (se 1 (by rfl) ⟨2514470, by rfl⟩ : syracuseStep 3352627 = 5028941) B5028941
theorem B3532889 : Blo 1468554 3532889 := bstep (se 2 (by rfl) ⟨1324833, by rfl⟩ : syracuseStep 3532889 = 2649667) B2649667
theorem B2205785 : Blo 1468554 2205785 := bstep (se 2 (by rfl) ⟨827169, by rfl⟩ : syracuseStep 2205785 = 1654339) B1654339
theorem B1468555 : Blo 1468554 1468555 := bstep (se 1 (by rfl) ⟨1101416, by rfl⟩ : syracuseStep 1468555 = 2202833) B2202833
theorem B1468567 : Blo 1468554 1468567 := bstep (se 1 (by rfl) ⟨1101425, by rfl⟩ : syracuseStep 1468567 = 2202851) B2202851
theorem B1468587 : Blo 1468554 1468587 := bstep (se 1 (by rfl) ⟨1101440, by rfl⟩ : syracuseStep 1468587 = 2202881) B2202881
theorem B4958387 : Blo 1468554 4958387 := bstep (se 1 (by rfl) ⟨3718790, by rfl⟩ : syracuseStep 4958387 = 7437581) B7437581
theorem B1468599 : Blo 1468554 1468599 := bstep (se 1 (by rfl) ⟨1101449, by rfl⟩ : syracuseStep 1468599 = 2202899) B2202899
theorem B1468619 : Blo 1468554 1468619 := bstep (se 1 (by rfl) ⟨1101464, by rfl⟩ : syracuseStep 1468619 = 2202929) B2202929
theorem B1468631 : Blo 1468554 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B1468651 : Blo 1468554 1468651 := bstep (se 1 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 1468651 = 2202977) B2202977
theorem B1468663 : Blo 1468554 1468663 := bstep (se 1 (by rfl) ⟨1101497, by rfl⟩ : syracuseStep 1468663 = 2202995) B2202995
theorem B1468683 : Blo 1468554 1468683 := bstep (se 1 (by rfl) ⟨1101512, by rfl⟩ : syracuseStep 1468683 = 2203025) B2203025
theorem B1468695 : Blo 1468554 1468695 := bstep (se 1 (by rfl) ⟨1101521, by rfl⟩ : syracuseStep 1468695 = 2203043) B2203043
theorem B1468715 : Blo 1468554 1468715 := bstep (se 1 (by rfl) ⟨1101536, by rfl⟩ : syracuseStep 1468715 = 2203073) B2203073
theorem B1468727 : Blo 1468554 1468727 := bstep (se 1 (by rfl) ⟨1101545, by rfl⟩ : syracuseStep 1468727 = 2203091) B2203091
theorem B1468747 : Blo 1468554 1468747 := bstep (se 1 (by rfl) ⟨1101560, by rfl⟩ : syracuseStep 1468747 = 2203121) B2203121
theorem B1468759 : Blo 1468554 1468759 := bstep (se 1 (by rfl) ⟨1101569, by rfl⟩ : syracuseStep 1468759 = 2203139) B2203139
theorem B3180887 : Blo 1468554 3180887 := bstep (se 1 (by rfl) ⟨2385665, by rfl⟩ : syracuseStep 3180887 = 4771331) B4771331
theorem B1468779 : Blo 1468554 1468779 := bstep (se 1 (by rfl) ⟨1101584, by rfl⟩ : syracuseStep 1468779 = 2203169) B2203169
theorem B1468791 : Blo 1468554 1468791 := bstep (se 1 (by rfl) ⟨1101593, by rfl⟩ : syracuseStep 1468791 = 2203187) B2203187
theorem B1468811 : Blo 1468554 1468811 := bstep (se 1 (by rfl) ⟨1101608, by rfl⟩ : syracuseStep 1468811 = 2203217) B2203217
theorem B1468823 : Blo 1468554 1468823 := bstep (se 1 (by rfl) ⟨1101617, by rfl⟩ : syracuseStep 1468823 = 2203235) B2203235
theorem B1468843 : Blo 1468554 1468843 := bstep (se 1 (by rfl) ⟨1101632, by rfl⟩ : syracuseStep 1468843 = 2203265) B2203265
theorem B1468855 : Blo 1468554 1468855 := bstep (se 1 (by rfl) ⟨1101641, by rfl⟩ : syracuseStep 1468855 = 2203283) B2203283
theorem B4958657 : Blo 1468554 4958657 := bstep (se 2 (by rfl) ⟨1859496, by rfl⟩ : syracuseStep 4958657 = 3718993) B3718993
theorem B1468875 : Blo 1468554 1468875 := bstep (se 1 (by rfl) ⟨1101656, by rfl⟩ : syracuseStep 1468875 = 2203313) B2203313
theorem B2091467 : Blo 1468554 2091467 := bstep (se 1 (by rfl) ⟨1568600, by rfl⟩ : syracuseStep 2091467 = 3137201) B3137201
theorem B1468887 : Blo 1468554 1468887 := bstep (se 1 (by rfl) ⟨1101665, by rfl⟩ : syracuseStep 1468887 = 2203331) B2203331
theorem B1468907 : Blo 1468554 1468907 := bstep (se 1 (by rfl) ⟨1101680, by rfl⟩ : syracuseStep 1468907 = 2203361) B2203361
theorem B1468919 : Blo 1468554 1468919 := bstep (se 1 (by rfl) ⟨1101689, by rfl⟩ : syracuseStep 1468919 = 2203379) B2203379
theorem B1468939 : Blo 1468554 1468939 := bstep (se 1 (by rfl) ⟨1101704, by rfl⟩ : syracuseStep 1468939 = 2203409) B2203409
theorem B1468951 : Blo 1468554 1468951 := bstep (se 1 (by rfl) ⟨1101713, by rfl⟩ : syracuseStep 1468951 = 2203427) B2203427
theorem B1468971 : Blo 1468554 1468971 := bstep (se 1 (by rfl) ⟨1101728, by rfl⟩ : syracuseStep 1468971 = 2203457) B2203457
theorem B4467251 : Blo 1468554 4467251 := bstep (se 1 (by rfl) ⟨3350438, by rfl⟩ : syracuseStep 4467251 = 6700877) B6700877
theorem B1468983 : Blo 1468554 1468983 := bstep (se 1 (by rfl) ⟨1101737, by rfl⟩ : syracuseStep 1468983 = 2203475) B2203475
theorem B1469003 : Blo 1468554 1469003 := bstep (se 1 (by rfl) ⟨1101752, by rfl⟩ : syracuseStep 1469003 = 2203505) B2203505
theorem B1469015 : Blo 1468554 1469015 := bstep (se 1 (by rfl) ⟨1101761, by rfl⟩ : syracuseStep 1469015 = 2203523) B2203523
theorem B3140183 : Blo 1468554 3140183 := bstep (se 1 (by rfl) ⟨2355137, by rfl⟩ : syracuseStep 3140183 = 4710275) B4710275
theorem B25111133 : Blo 1468554 25111133 := bstep (se 3 (by rfl) ⟨4708337, by rfl⟩ : syracuseStep 25111133 = 9416675) B9416675
theorem B1469035 : Blo 1468554 1469035 := bstep (se 1 (by rfl) ⟨1101776, by rfl⟩ : syracuseStep 1469035 = 2203553) B2203553
theorem B1469047 : Blo 1468554 1469047 := bstep (se 1 (by rfl) ⟨1101785, by rfl⟩ : syracuseStep 1469047 = 2203571) B2203571
theorem B3140225 : Blo 1468554 3140225 := bstep (se 2 (by rfl) ⟨1177584, by rfl⟩ : syracuseStep 3140225 = 2355169) B2355169
theorem B8931971 : Blo 1468554 8931971 := bstep (se 1 (by rfl) ⟨6698978, by rfl⟩ : syracuseStep 8931971 = 13397957) B13397957
theorem B1469067 : Blo 1468554 1469067 := bstep (se 1 (by rfl) ⟨1101800, by rfl⟩ : syracuseStep 1469067 = 2203601) B2203601
theorem B1469079 : Blo 1468554 1469079 := bstep (se 1 (by rfl) ⟨1101809, by rfl⟩ : syracuseStep 1469079 = 2203619) B2203619
theorem B2648729 : Blo 1468554 2648729 := bstep (se 2 (by rfl) ⟨993273, by rfl⟩ : syracuseStep 2648729 = 1986547) B1986547
theorem B1469099 : Blo 1468554 1469099 := bstep (se 1 (by rfl) ⟨1101824, by rfl⟩ : syracuseStep 1469099 = 2203649) B2203649
theorem B1469111 : Blo 1468554 1469111 := bstep (se 1 (by rfl) ⟨1101833, by rfl⟩ : syracuseStep 1469111 = 2203667) B2203667
theorem B1469131 : Blo 1468554 1469131 := bstep (se 1 (by rfl) ⟨1101848, by rfl⟩ : syracuseStep 1469131 = 2203697) B2203697
theorem B1469143 : Blo 1468554 1469143 := bstep (se 1 (by rfl) ⟨1101857, by rfl⟩ : syracuseStep 1469143 = 2203715) B2203715
theorem B1469163 : Blo 1468554 1469163 := bstep (se 1 (by rfl) ⟨1101872, by rfl⟩ : syracuseStep 1469163 = 2203745) B2203745
theorem B1469175 : Blo 1468554 1469175 := bstep (se 1 (by rfl) ⟨1101881, by rfl⟩ : syracuseStep 1469175 = 2203763) B2203763
theorem B1469195 : Blo 1468554 1469195 := bstep (se 1 (by rfl) ⟨1101896, by rfl⟩ : syracuseStep 1469195 = 2203793) B2203793
theorem B1469207 : Blo 1468554 1469207 := bstep (se 1 (by rfl) ⟨1101905, by rfl⟩ : syracuseStep 1469207 = 2203811) B2203811
theorem B2788121 : Blo 1468554 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B1469227 : Blo 1468554 1469227 := bstep (se 1 (by rfl) ⟨1101920, by rfl⟩ : syracuseStep 1469227 = 2203841) B2203841
theorem B5581619 : Blo 1468554 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B1469239 : Blo 1468554 1469239 := bstep (se 1 (by rfl) ⟨1101929, by rfl⟩ : syracuseStep 1469239 = 2203859) B2203859
theorem B1469259 : Blo 1468554 1469259 := bstep (se 1 (by rfl) ⟨1101944, by rfl⟩ : syracuseStep 1469259 = 2203889) B2203889
theorem B1469271 : Blo 1468554 1469271 := bstep (se 1 (by rfl) ⟨1101953, by rfl⟩ : syracuseStep 1469271 = 2203907) B2203907
theorem B1469291 : Blo 1468554 1469291 := bstep (se 1 (by rfl) ⟨1101968, by rfl⟩ : syracuseStep 1469291 = 2203937) B2203937
theorem B1469303 : Blo 1468554 1469303 := bstep (se 1 (by rfl) ⟨1101977, by rfl⟩ : syracuseStep 1469303 = 2203955) B2203955
theorem B3304331 : Blo 1468554 3304331 := bstep (se 1 (by rfl) ⟨2478248, by rfl⟩ : syracuseStep 3304331 = 4956497) B4956497
theorem B1469323 : Blo 1468554 1469323 := bstep (se 1 (by rfl) ⟨1101992, by rfl⟩ : syracuseStep 1469323 = 2203985) B2203985
theorem B1469335 : Blo 1468554 1469335 := bstep (se 1 (by rfl) ⟨1102001, by rfl⟩ : syracuseStep 1469335 = 2204003) B2204003
theorem B1469355 : Blo 1468554 1469355 := bstep (se 1 (by rfl) ⟨1102016, by rfl⟩ : syracuseStep 1469355 = 2204033) B2204033
theorem B1469367 : Blo 1468554 1469367 := bstep (se 1 (by rfl) ⟨1102025, by rfl⟩ : syracuseStep 1469367 = 2204051) B2204051
theorem B3304385 : Blo 1468554 3304385 := bstep (se 2 (by rfl) ⟨1239144, by rfl⟩ : syracuseStep 3304385 = 2478289) B2478289
theorem B1469387 : Blo 1468554 1469387 := bstep (se 1 (by rfl) ⟨1102040, by rfl⟩ : syracuseStep 1469387 = 2204081) B2204081
theorem B1469399 : Blo 1468554 1469399 := bstep (se 1 (by rfl) ⟨1102049, by rfl⟩ : syracuseStep 1469399 = 2204099) B2204099
theorem B4959197 : Blo 1468554 4959197 := bstep (se 3 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 4959197 = 1859699) B1859699
theorem B1469419 : Blo 1468554 1469419 := bstep (se 1 (by rfl) ⟨1102064, by rfl⟩ : syracuseStep 1469419 = 2204129) B2204129
theorem B1469431 : Blo 1468554 1469431 := bstep (se 1 (by rfl) ⟨1102073, by rfl⟩ : syracuseStep 1469431 = 2204147) B2204147
theorem B1469451 : Blo 1468554 1469451 := bstep (se 1 (by rfl) ⟨1102088, by rfl⟩ : syracuseStep 1469451 = 2204177) B2204177
theorem B4770839 : Blo 1468554 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B1469463 : Blo 1468554 1469463 := bstep (se 1 (by rfl) ⟨1102097, by rfl⟩ : syracuseStep 1469463 = 2204195) B2204195
theorem B1469483 : Blo 1468554 1469483 := bstep (se 1 (by rfl) ⟨1102112, by rfl⟩ : syracuseStep 1469483 = 2204225) B2204225
theorem B1469495 : Blo 1468554 1469495 := bstep (se 1 (by rfl) ⟨1102121, by rfl⟩ : syracuseStep 1469495 = 2204243) B2204243
theorem B1469515 : Blo 1468554 1469515 := bstep (se 1 (by rfl) ⟨1102136, by rfl⟩ : syracuseStep 1469515 = 2204273) B2204273
theorem B1789015 : Blo 1468554 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B1469527 : Blo 1468554 1469527 := bstep (se 1 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 1469527 = 2204291) B2204291
theorem B1469547 : Blo 1468554 1469547 := bstep (se 1 (by rfl) ⟨1102160, by rfl⟩ : syracuseStep 1469547 = 2204321) B2204321
theorem B1469559 : Blo 1468554 1469559 := bstep (se 1 (by rfl) ⟨1102169, by rfl⟩ : syracuseStep 1469559 = 2204339) B2204339
theorem B1469579 : Blo 1468554 1469579 := bstep (se 1 (by rfl) ⟨1102184, by rfl⟩ : syracuseStep 1469579 = 2204369) B2204369
theorem B1469591 : Blo 1468554 1469591 := bstep (se 1 (by rfl) ⟨1102193, by rfl⟩ : syracuseStep 1469591 = 2204387) B2204387
theorem B3304601 : Blo 1468554 3304601 := bstep (se 2 (by rfl) ⟨1239225, by rfl⟩ : syracuseStep 3304601 = 2478451) B2478451
theorem B1469611 : Blo 1468554 1469611 := bstep (se 1 (by rfl) ⟨1102208, by rfl⟩ : syracuseStep 1469611 = 2204417) B2204417
theorem B4082867 : Blo 1468554 4082867 := bstep (se 1 (by rfl) ⟨3062150, by rfl⟩ : syracuseStep 4082867 = 6124301) B6124301
theorem B1469623 : Blo 1468554 1469623 := bstep (se 1 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 1469623 = 2204435) B2204435
theorem B1469643 : Blo 1468554 1469643 := bstep (se 1 (by rfl) ⟨1102232, by rfl⟩ : syracuseStep 1469643 = 2204465) B2204465
theorem B1469655 : Blo 1468554 1469655 := bstep (se 1 (by rfl) ⟨1102241, by rfl⟩ : syracuseStep 1469655 = 2204483) B2204483
theorem B1469675 : Blo 1468554 1469675 := bstep (se 1 (by rfl) ⟨1102256, by rfl⟩ : syracuseStep 1469675 = 2204513) B2204513
theorem B3304691 : Blo 1468554 3304691 := bstep (se 1 (by rfl) ⟨2478518, by rfl⟩ : syracuseStep 3304691 = 4957037) B4957037
theorem B1469687 : Blo 1468554 1469687 := bstep (se 1 (by rfl) ⟨1102265, by rfl⟩ : syracuseStep 1469687 = 2204531) B2204531
theorem B313781509 : Blo 1468554 313781509 := bstep (se 4 (by rfl) ⟨29417016, by rfl⟩ : syracuseStep 313781509 = 58834033) B58834033
theorem B1469707 : Blo 1468554 1469707 := bstep (se 1 (by rfl) ⟨1102280, by rfl⟩ : syracuseStep 1469707 = 2204561) B2204561
theorem B3304727 : Blo 1468554 3304727 := bstep (se 1 (by rfl) ⟨2478545, by rfl⟩ : syracuseStep 3304727 = 4957091) B4957091
theorem B4705559 : Blo 1468554 4705559 := bstep (se 1 (by rfl) ⟨3529169, by rfl⟩ : syracuseStep 4705559 = 7058339) B7058339
theorem B1469719 : Blo 1468554 1469719 := bstep (se 1 (by rfl) ⟨1102289, by rfl⟩ : syracuseStep 1469719 = 2204579) B2204579
theorem B1469739 : Blo 1468554 1469739 := bstep (se 1 (by rfl) ⟨1102304, by rfl⟩ : syracuseStep 1469739 = 2204609) B2204609
theorem B1469751 : Blo 1468554 1469751 := bstep (se 1 (by rfl) ⟨1102313, by rfl⟩ : syracuseStep 1469751 = 2204627) B2204627
theorem B1469771 : Blo 1468554 1469771 := bstep (se 1 (by rfl) ⟨1102328, by rfl⟩ : syracuseStep 1469771 = 2204657) B2204657
theorem B1469783 : Blo 1468554 1469783 := bstep (se 1 (by rfl) ⟨1102337, by rfl⟩ : syracuseStep 1469783 = 2204675) B2204675
theorem B1469803 : Blo 1468554 1469803 := bstep (se 1 (by rfl) ⟨1102352, by rfl⟩ : syracuseStep 1469803 = 2204705) B2204705
theorem B1469815 : Blo 1468554 1469815 := bstep (se 1 (by rfl) ⟨1102361, by rfl⟩ : syracuseStep 1469815 = 2204723) B2204723
theorem B1469835 : Blo 1468554 1469835 := bstep (se 1 (by rfl) ⟨1102376, by rfl⟩ : syracuseStep 1469835 = 2204753) B2204753
theorem B2788759 : Blo 1468554 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B1469847 : Blo 1468554 1469847 := bstep (se 1 (by rfl) ⟨1102385, by rfl⟩ : syracuseStep 1469847 = 2204771) B2204771
theorem B1469867 : Blo 1468554 1469867 := bstep (se 1 (by rfl) ⟨1102400, by rfl⟩ : syracuseStep 1469867 = 2204801) B2204801
theorem B1469879 : Blo 1468554 1469879 := bstep (se 1 (by rfl) ⟨1102409, by rfl⟩ : syracuseStep 1469879 = 2204819) B2204819
theorem B3304907 : Blo 1468554 3304907 := bstep (se 1 (by rfl) ⟨2478680, by rfl⟩ : syracuseStep 3304907 = 4957361) B4957361
theorem B1469899 : Blo 1468554 1469899 := bstep (se 1 (by rfl) ⟨1102424, by rfl⟩ : syracuseStep 1469899 = 2204849) B2204849
theorem B1469911 : Blo 1468554 1469911 := bstep (se 1 (by rfl) ⟨1102433, by rfl⟩ : syracuseStep 1469911 = 2204867) B2204867
theorem B1469931 : Blo 1468554 1469931 := bstep (se 1 (by rfl) ⟨1102448, by rfl⟩ : syracuseStep 1469931 = 2204897) B2204897
theorem B1469943 : Blo 1468554 1469943 := bstep (se 1 (by rfl) ⟨1102457, by rfl⟩ : syracuseStep 1469943 = 2204915) B2204915
theorem B3304961 : Blo 1468554 3304961 := bstep (se 2 (by rfl) ⟨1239360, by rfl⟩ : syracuseStep 3304961 = 2478721) B2478721
theorem B1469963 : Blo 1468554 1469963 := bstep (se 1 (by rfl) ⟨1102472, by rfl⟩ : syracuseStep 1469963 = 2204945) B2204945
theorem B1469975 : Blo 1468554 1469975 := bstep (se 1 (by rfl) ⟨1102481, by rfl⟩ : syracuseStep 1469975 = 2204963) B2204963
theorem B1469995 : Blo 1468554 1469995 := bstep (se 1 (by rfl) ⟨1102496, by rfl⟩ : syracuseStep 1469995 = 2204993) B2204993
theorem B1470007 : Blo 1468554 1470007 := bstep (se 1 (by rfl) ⟨1102505, by rfl⟩ : syracuseStep 1470007 = 2205011) B2205011
theorem B23817797 : Blo 1468554 23817797 := bstep (se 4 (by rfl) ⟨2232918, by rfl⟩ : syracuseStep 23817797 = 4465837) B4465837
theorem B1470027 : Blo 1468554 1470027 := bstep (se 1 (by rfl) ⟨1102520, by rfl⟩ : syracuseStep 1470027 = 2205041) B2205041
theorem B1470039 : Blo 1468554 1470039 := bstep (se 1 (by rfl) ⟨1102529, by rfl⟩ : syracuseStep 1470039 = 2205059) B2205059
theorem B1470059 : Blo 1468554 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B1470071 : Blo 1468554 1470071 := bstep (se 1 (by rfl) ⟨1102553, by rfl⟩ : syracuseStep 1470071 = 2205107) B2205107
theorem B1470091 : Blo 1468554 1470091 := bstep (se 1 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 1470091 = 2205137) B2205137
theorem B1470103 : Blo 1468554 1470103 := bstep (se 1 (by rfl) ⟨1102577, by rfl⟩ : syracuseStep 1470103 = 2205155) B2205155
theorem B5099159 : Blo 1468554 5099159 := bstep (se 1 (by rfl) ⟨3824369, by rfl⟩ : syracuseStep 5099159 = 7648739) B7648739
theorem B1470123 : Blo 1468554 1470123 := bstep (se 1 (by rfl) ⟨1102592, by rfl⟩ : syracuseStep 1470123 = 2205185) B2205185
theorem B6704819 : Blo 1468554 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B1470135 : Blo 1468554 1470135 := bstep (se 1 (by rfl) ⟨1102601, by rfl⟩ : syracuseStep 1470135 = 2205203) B2205203
theorem B1470155 : Blo 1468554 1470155 := bstep (se 1 (by rfl) ⟨1102616, by rfl⟩ : syracuseStep 1470155 = 2205233) B2205233
theorem B1470167 : Blo 1468554 1470167 := bstep (se 1 (by rfl) ⟨1102625, by rfl⟩ : syracuseStep 1470167 = 2205251) B2205251
theorem B3305177 : Blo 1468554 3305177 := bstep (se 2 (by rfl) ⟨1239441, by rfl⟩ : syracuseStep 3305177 = 2478883) B2478883
theorem B1470187 : Blo 1468554 1470187 := bstep (se 1 (by rfl) ⟨1102640, by rfl⟩ : syracuseStep 1470187 = 2205281) B2205281
theorem B1470199 : Blo 1468554 1470199 := bstep (se 1 (by rfl) ⟨1102649, by rfl⟩ : syracuseStep 1470199 = 2205299) B2205299
theorem B1470219 : Blo 1468554 1470219 := bstep (se 1 (by rfl) ⟨1102664, by rfl⟩ : syracuseStep 1470219 = 2205329) B2205329
theorem B1470231 : Blo 1468554 1470231 := bstep (se 1 (by rfl) ⟨1102673, by rfl⟩ : syracuseStep 1470231 = 2205347) B2205347
theorem B1470251 : Blo 1468554 1470251 := bstep (se 1 (by rfl) ⟨1102688, by rfl⟩ : syracuseStep 1470251 = 2205377) B2205377
theorem B3305267 : Blo 1468554 3305267 := bstep (se 1 (by rfl) ⟨2478950, by rfl⟩ : syracuseStep 3305267 = 4957901) B4957901
theorem B1470263 : Blo 1468554 1470263 := bstep (se 1 (by rfl) ⟨1102697, by rfl⟩ : syracuseStep 1470263 = 2205395) B2205395
theorem B1470283 : Blo 1468554 1470283 := bstep (se 1 (by rfl) ⟨1102712, by rfl⟩ : syracuseStep 1470283 = 2205425) B2205425
theorem B3305303 : Blo 1468554 3305303 := bstep (se 1 (by rfl) ⟨2478977, by rfl⟩ : syracuseStep 3305303 = 4957955) B4957955
theorem B1470295 : Blo 1468554 1470295 := bstep (se 1 (by rfl) ⟨1102721, by rfl⟩ : syracuseStep 1470295 = 2205443) B2205443
theorem B1470315 : Blo 1468554 1470315 := bstep (se 1 (by rfl) ⟨1102736, by rfl⟩ : syracuseStep 1470315 = 2205473) B2205473
theorem B1470327 : Blo 1468554 1470327 := bstep (se 1 (by rfl) ⟨1102745, by rfl⟩ : syracuseStep 1470327 = 2205491) B2205491
theorem B11161475 : Blo 1468554 11161475 := bstep (se 1 (by rfl) ⟨8371106, by rfl⟩ : syracuseStep 11161475 = 16742213) B16742213
theorem B1470347 : Blo 1468554 1470347 := bstep (se 1 (by rfl) ⟨1102760, by rfl⟩ : syracuseStep 1470347 = 2205521) B2205521
theorem B1470359 : Blo 1468554 1470359 := bstep (se 1 (by rfl) ⟨1102769, by rfl⟩ : syracuseStep 1470359 = 2205539) B2205539
theorem B1470379 : Blo 1468554 1470379 := bstep (se 1 (by rfl) ⟨1102784, by rfl⟩ : syracuseStep 1470379 = 2205569) B2205569
theorem B5656499 : Blo 1468554 5656499 := bstep (se 1 (by rfl) ⟨4242374, by rfl⟩ : syracuseStep 5656499 = 8484749) B8484749
theorem B1470391 : Blo 1468554 1470391 := bstep (se 1 (by rfl) ⟨1102793, by rfl⟩ : syracuseStep 1470391 = 2205587) B2205587
theorem B1470411 : Blo 1468554 1470411 := bstep (se 1 (by rfl) ⟨1102808, by rfl⟩ : syracuseStep 1470411 = 2205617) B2205617
theorem B1470423 : Blo 1468554 1470423 := bstep (se 1 (by rfl) ⟨1102817, by rfl⟩ : syracuseStep 1470423 = 2205635) B2205635
theorem B1470443 : Blo 1468554 1470443 := bstep (se 1 (by rfl) ⟨1102832, by rfl⟩ : syracuseStep 1470443 = 2205665) B2205665
theorem B1470455 : Blo 1468554 1470455 := bstep (se 1 (by rfl) ⟨1102841, by rfl⟩ : syracuseStep 1470455 = 2205683) B2205683
theorem B3305483 : Blo 1468554 3305483 := bstep (se 1 (by rfl) ⟨2479112, by rfl⟩ : syracuseStep 3305483 = 4958225) B4958225
theorem B1470475 : Blo 1468554 1470475 := bstep (se 1 (by rfl) ⟨1102856, by rfl⟩ : syracuseStep 1470475 = 2205713) B2205713
theorem B14323729 : Blo 1468554 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B1470487 : Blo 1468554 1470487 := bstep (se 1 (by rfl) ⟨1102865, by rfl⟩ : syracuseStep 1470487 = 2205731) B2205731
theorem B14315555 : Blo 1468554 14315555 := bstep (se 1 (by rfl) ⟨10736666, by rfl⟩ : syracuseStep 14315555 = 21473333) B21473333
theorem B1470507 : Blo 1468554 1470507 := bstep (se 1 (by rfl) ⟨1102880, by rfl⟩ : syracuseStep 1470507 = 2205761) B2205761
theorem B1470519 : Blo 1468554 1470519 := bstep (se 1 (by rfl) ⟨1102889, by rfl⟩ : syracuseStep 1470519 = 2205779) B2205779
theorem B3305537 : Blo 1468554 3305537 := bstep (se 2 (by rfl) ⟨1239576, by rfl⟩ : syracuseStep 3305537 = 2479153) B2479153
theorem B4960331 : Blo 1468554 4960331 := bstep (se 1 (by rfl) ⟨3720248, by rfl⟩ : syracuseStep 4960331 = 7440497) B7440497
theorem B1470539 : Blo 1468554 1470539 := bstep (se 1 (by rfl) ⟨1102904, by rfl⟩ : syracuseStep 1470539 = 2205809) B2205809
theorem B1470551 : Blo 1468554 1470551 := bstep (se 1 (by rfl) ⟨1102913, by rfl⟩ : syracuseStep 1470551 = 2205827) B2205827
theorem B1675415 : Blo 1468554 1675415 := bstep (se 1 (by rfl) ⟨1256561, by rfl⟩ : syracuseStep 1675415 = 2513123) B2513123
theorem B2789579 : Blo 1468554 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B2789633 : Blo 1468554 2789633 := bstep (se 2 (by rfl) ⟨1046112, by rfl⟩ : syracuseStep 2789633 = 2092225) B2092225
theorem B5583107 : Blo 1468554 5583107 := bstep (se 1 (by rfl) ⟨4187330, by rfl⟩ : syracuseStep 5583107 = 8374661) B8374661
theorem B1790219 : Blo 1468554 1790219 := bstep (se 1 (by rfl) ⟨1342664, by rfl⟩ : syracuseStep 1790219 = 2685329) B2685329
theorem B3305753 : Blo 1468554 3305753 := bstep (se 2 (by rfl) ⟨1239657, by rfl⟩ : syracuseStep 3305753 = 2479315) B2479315
theorem B11153699 : Blo 1468554 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B1569079 : Blo 1468554 1569079 := bstep (se 1 (by rfl) ⟨1176809, by rfl⟩ : syracuseStep 1569079 = 2353619) B2353619
theorem B4960601 : Blo 1468554 4960601 := bstep (se 2 (by rfl) ⟨1860225, by rfl⟩ : syracuseStep 4960601 = 3720451) B3720451
theorem B3305843 : Blo 1468554 3305843 := bstep (se 1 (by rfl) ⟨2479382, by rfl⟩ : syracuseStep 3305843 = 4958765) B4958765
theorem B3305879 : Blo 1468554 3305879 := bstep (se 1 (by rfl) ⟨2479409, by rfl⟩ : syracuseStep 3305879 = 4958819) B4958819
theorem B2478539 : Blo 1468554 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B3822041 : Blo 1468554 3822041 := bstep (se 2 (by rfl) ⟨1433265, by rfl⟩ : syracuseStep 3822041 = 2866531) B2866531
theorem B103150097 : Blo 1468554 103150097 := bstep (se 2 (by rfl) ⟨38681286, by rfl⟩ : syracuseStep 103150097 = 77362573) B77362573
theorem B6279697 : Blo 1468554 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B7434827 : Blo 1468554 7434827 := bstep (se 1 (by rfl) ⟨5576120, by rfl⟩ : syracuseStep 7434827 = 11152241) B11152241
theorem B2478667 : Blo 1468554 2478667 := bstep (se 1 (by rfl) ⟨1859000, by rfl⟩ : syracuseStep 2478667 = 3718001) B3718001
theorem B3306059 : Blo 1468554 3306059 := bstep (se 1 (by rfl) ⟨2479544, by rfl⟩ : syracuseStep 3306059 = 4959089) B4959089
theorem B3306113 : Blo 1468554 3306113 := bstep (se 2 (by rfl) ⟨1239792, by rfl⟩ : syracuseStep 3306113 = 2479585) B2479585
theorem B2478809 : Blo 1468554 2478809 := bstep (se 2 (by rfl) ⟨929553, by rfl⟩ : syracuseStep 2478809 = 1859107) B1859107
theorem B2233163 : Blo 1468554 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B2233175 : Blo 1468554 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B2478937 : Blo 1468554 2478937 := bstep (se 2 (by rfl) ⟨929601, by rfl⟩ : syracuseStep 2478937 = 1859203) B1859203
theorem B3306329 : Blo 1468554 3306329 := bstep (se 2 (by rfl) ⟨1239873, by rfl⟩ : syracuseStep 3306329 = 2479747) B2479747
theorem B3306419 : Blo 1468554 3306419 := bstep (se 1 (by rfl) ⟨2479814, by rfl⟩ : syracuseStep 3306419 = 4959629) B4959629
theorem B7066547 : Blo 1468554 7066547 := bstep (se 1 (by rfl) ⟨5299910, by rfl⟩ : syracuseStep 7066547 = 10599821) B10599821
theorem B3306455 : Blo 1468554 3306455 := bstep (se 1 (by rfl) ⟨2479841, by rfl⟩ : syracuseStep 3306455 = 4959683) B4959683
theorem B10597337 : Blo 1468554 10597337 := bstep (se 2 (by rfl) ⟨3974001, by rfl⟩ : syracuseStep 10597337 = 7948003) B7948003
theorem B11924441 : Blo 1468554 11924441 := bstep (se 2 (by rfl) ⟨4471665, by rfl⟩ : syracuseStep 11924441 = 8943331) B8943331
theorem B9409553 : Blo 1468554 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B4961303 : Blo 1468554 4961303 := bstep (se 1 (by rfl) ⟨3720977, by rfl⟩ : syracuseStep 4961303 = 7441955) B7441955
theorem B2683991 : Blo 1468554 2683991 := bstep (se 1 (by rfl) ⟨2012993, by rfl⟩ : syracuseStep 2683991 = 4025987) B4025987
theorem B1569899 : Blo 1468554 1569899 := bstep (se 1 (by rfl) ⟨1177424, by rfl⟩ : syracuseStep 1569899 = 2354849) B2354849
theorem B2978945 : Blo 1468554 2978945 := bstep (se 2 (by rfl) ⟨1117104, by rfl⟩ : syracuseStep 2978945 = 2234209) B2234209
theorem B3306635 : Blo 1468554 3306635 := bstep (se 1 (by rfl) ⟨2479976, by rfl⟩ : syracuseStep 3306635 = 4959953) B4959953
theorem B23827607 : Blo 1468554 23827607 := bstep (se 1 (by rfl) ⟨17870705, by rfl⟩ : syracuseStep 23827607 = 35741411) B35741411
theorem B2790551 : Blo 1468554 2790551 := bstep (se 1 (by rfl) ⟨2092913, by rfl⟩ : syracuseStep 2790551 = 4185827) B4185827
theorem B51573941 : Blo 1468554 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B3306689 : Blo 1468554 3306689 := bstep (se 2 (by rfl) ⟨1240008, by rfl⟩ : syracuseStep 3306689 = 2480017) B2480017
theorem B1570027 : Blo 1468554 1570027 := bstep (se 1 (by rfl) ⟨1177520, by rfl⟩ : syracuseStep 1570027 = 2355041) B2355041
theorem B4183447 : Blo 1468554 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B2479511 : Blo 1468554 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B3306905 : Blo 1468554 3306905 := bstep (se 2 (by rfl) ⟨1240089, by rfl⟩ : syracuseStep 3306905 = 2480179) B2480179
theorem B3306995 : Blo 1468554 3306995 := bstep (se 1 (by rfl) ⟨2480246, by rfl⟩ : syracuseStep 3306995 = 4960493) B4960493
theorem B1652215 : Blo 1468554 1652215 := bstep (se 1 (by rfl) ⟨1239161, by rfl⟩ : syracuseStep 1652215 = 2478323) B2478323
theorem B2479639 : Blo 1468554 2479639 := bstep (se 1 (by rfl) ⟨1859729, by rfl⟩ : syracuseStep 2479639 = 3719459) B3719459
theorem B3307031 : Blo 1468554 3307031 := bstep (se 1 (by rfl) ⟨2480273, by rfl⟩ : syracuseStep 3307031 = 4960547) B4960547
theorem B9410093 : Blo 1468554 9410093 := bstep (se 3 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 9410093 = 3528785) B3528785
theorem B4961843 : Blo 1468554 4961843 := bstep (se 1 (by rfl) ⟨3721382, by rfl⟩ : syracuseStep 4961843 = 7442765) B7442765
theorem B3577409 : Blo 1468554 3577409 := bstep (se 2 (by rfl) ⟨1341528, by rfl⟩ : syracuseStep 3577409 = 2683057) B2683057
theorem B4470365 : Blo 1468554 4470365 := bstep (se 3 (by rfl) ⟨838193, by rfl⟩ : syracuseStep 4470365 = 1676387) B1676387
theorem B7444061 : Blo 1468554 7444061 := bstep (se 3 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 7444061 = 2791523) B2791523
theorem B1652395 : Blo 1468554 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B4708019 : Blo 1468554 4708019 := bstep (se 1 (by rfl) ⟨3531014, by rfl⟩ : syracuseStep 4708019 = 7062029) B7062029
theorem B2791091 : Blo 1468554 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B3307211 : Blo 1468554 3307211 := bstep (se 1 (by rfl) ⟨2480408, by rfl⟩ : syracuseStep 3307211 = 4960817) B4960817
theorem B4708057 : Blo 1468554 4708057 := bstep (se 2 (by rfl) ⟨1765521, by rfl⟩ : syracuseStep 4708057 = 3531043) B3531043
theorem B3307265 : Blo 1468554 3307265 := bstep (se 2 (by rfl) ⟨1240224, by rfl⟩ : syracuseStep 3307265 = 2480449) B2480449
theorem B5576471 : Blo 1468554 5576471 := bstep (se 1 (by rfl) ⟨4182353, by rfl⟩ : syracuseStep 5576471 = 8364707) B8364707
theorem B1652503 : Blo 1468554 1652503 := bstep (se 1 (by rfl) ⟨1239377, by rfl⟩ : syracuseStep 1652503 = 2478755) B2478755
theorem B4962113 : Blo 1468554 4962113 := bstep (se 2 (by rfl) ⟨1860792, by rfl⟩ : syracuseStep 4962113 = 3721585) B3721585
theorem B8370013 : Blo 1468554 8370013 := bstep (se 3 (by rfl) ⟨1569377, by rfl⟩ : syracuseStep 8370013 = 3138755) B3138755
theorem B23844725 : Blo 1468554 23844725 := bstep (se 5 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 23844725 = 2235443) B2235443
theorem B1652683 : Blo 1468554 1652683 := bstep (se 1 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 1652683 = 2479025) B2479025
theorem B3307481 : Blo 1468554 3307481 := bstep (se 2 (by rfl) ⟨1240305, by rfl⟩ : syracuseStep 3307481 = 2480611) B2480611
theorem B45250595 : Blo 1468554 45250595 := bstep (se 1 (by rfl) ⟨33937946, by rfl⟩ : syracuseStep 45250595 = 67875893) B67875893
theorem B3307571 : Blo 1468554 3307571 := bstep (se 1 (by rfl) ⟨2480678, by rfl⟩ : syracuseStep 3307571 = 4961357) B4961357
theorem B1652791 : Blo 1468554 1652791 := bstep (se 1 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 1652791 = 2479187) B2479187
theorem B3307607 : Blo 1468554 3307607 := bstep (se 1 (by rfl) ⟨2480705, by rfl⟩ : syracuseStep 3307607 = 4961411) B4961411
theorem B3528793 : Blo 1468554 3528793 := bstep (se 2 (by rfl) ⟨1323297, by rfl⟩ : syracuseStep 3528793 = 2646595) B2646595
theorem B16332893 : Blo 1468554 16332893 := bstep (se 3 (by rfl) ⟨3062417, by rfl⟩ : syracuseStep 16332893 = 6124835) B6124835
theorem B2480267 : Blo 1468554 2480267 := bstep (se 1 (by rfl) ⟨1860200, by rfl⟩ : syracuseStep 2480267 = 3720401) B3720401
theorem B2791577 : Blo 1468554 2791577 := bstep (se 2 (by rfl) ⟨1046841, by rfl⟩ : syracuseStep 2791577 = 2093683) B2093683
theorem B3717323 : Blo 1468554 3717323 := bstep (se 1 (by rfl) ⟨2787992, by rfl⟩ : syracuseStep 3717323 = 5575985) B5575985
theorem B1652971 : Blo 1468554 1652971 := bstep (se 1 (by rfl) ⟨1239728, by rfl⟩ : syracuseStep 1652971 = 2479457) B2479457
theorem B2480395 : Blo 1468554 2480395 := bstep (se 1 (by rfl) ⟨1860296, by rfl⟩ : syracuseStep 2480395 = 3720593) B3720593
theorem B3307787 : Blo 1468554 3307787 := bstep (se 1 (by rfl) ⟨2480840, by rfl⟩ : syracuseStep 3307787 = 4961681) B4961681
theorem B37673261 : Blo 1468554 37673261 := bstep (se 3 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 37673261 = 14127473) B14127473
theorem B7436609 : Blo 1468554 7436609 := bstep (se 2 (by rfl) ⟨2788728, by rfl⟩ : syracuseStep 7436609 = 5577457) B5577457
theorem B3307841 : Blo 1468554 3307841 := bstep (se 2 (by rfl) ⟨1240440, by rfl⟩ : syracuseStep 3307841 = 2480881) B2480881
theorem B1653079 : Blo 1468554 1653079 := bstep (se 1 (by rfl) ⟨1239809, by rfl⟩ : syracuseStep 1653079 = 2479619) B2479619
theorem B4962653 : Blo 1468554 4962653 := bstep (se 3 (by rfl) ⟨930497, by rfl⟩ : syracuseStep 4962653 = 1860995) B1860995
theorem B1489303 : Blo 1468554 1489303 := bstep (se 1 (by rfl) ⟨1116977, by rfl⟩ : syracuseStep 1489303 = 2233955) B2233955
theorem B2480537 : Blo 1468554 2480537 := bstep (se 2 (by rfl) ⟨930201, by rfl⟩ : syracuseStep 2480537 = 1860403) B1860403
theorem B1653259 : Blo 1468554 1653259 := bstep (se 1 (by rfl) ⟨1239944, by rfl⟩ : syracuseStep 1653259 = 2479889) B2479889
theorem B7543313 : Blo 1468554 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B2480665 : Blo 1468554 2480665 := bstep (se 2 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 2480665 = 1860499) B1860499
theorem B3308057 : Blo 1468554 3308057 := bstep (se 2 (by rfl) ⟨1240521, by rfl⟩ : syracuseStep 3308057 = 2481043) B2481043
theorem B3717697 : Blo 1468554 3717697 := bstep (se 2 (by rfl) ⟨1394136, by rfl⟩ : syracuseStep 3717697 = 2788273) B2788273
theorem B10590821 : Blo 1468554 10590821 := bstep (se 4 (by rfl) ⟨992889, by rfl⟩ : syracuseStep 10590821 = 1985779) B1985779
theorem B3308147 : Blo 1468554 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B1653367 : Blo 1468554 1653367 := bstep (se 1 (by rfl) ⟨1240025, by rfl⟩ : syracuseStep 1653367 = 2480051) B2480051
theorem B11917955 : Blo 1468554 11917955 := bstep (se 1 (by rfl) ⟨8938466, by rfl⟩ : syracuseStep 11917955 = 17876933) B17876933
theorem B3308183 : Blo 1468554 3308183 := bstep (se 1 (by rfl) ⟨2481137, by rfl⟩ : syracuseStep 3308183 = 4962275) B4962275
theorem B4184779 : Blo 1468554 4184779 := bstep (se 1 (by rfl) ⟨3138584, by rfl⟩ : syracuseStep 4184779 = 6277169) B6277169
theorem B1653547 : Blo 1468554 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B3308363 : Blo 1468554 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B3308417 : Blo 1468554 3308417 := bstep (se 2 (by rfl) ⟨1240656, by rfl⟩ : syracuseStep 3308417 = 2481313) B2481313
theorem B7060355 : Blo 1468554 7060355 := bstep (se 1 (by rfl) ⟨5295266, by rfl⟩ : syracuseStep 7060355 = 10590533) B10590533
theorem B9419651 : Blo 1468554 9419651 := bstep (se 1 (by rfl) ⟨7064738, by rfl⟩ : syracuseStep 9419651 = 14129477) B14129477
theorem B12557207 : Blo 1468554 12557207 := bstep (se 1 (by rfl) ⟨9417905, by rfl⟩ : syracuseStep 12557207 = 18835811) B18835811
theorem B1653655 : Blo 1468554 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B4185053 : Blo 1468554 4185053 := bstep (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) B1569395
theorem B5577731 : Blo 1468554 5577731 := bstep (se 1 (by rfl) ⟨4183298, by rfl⟩ : syracuseStep 5577731 = 8366597) B8366597
theorem B6274093 : Blo 1468554 6274093 := bstep (se 3 (by rfl) ⟨1176392, by rfl⟩ : syracuseStep 6274093 = 2352785) B2352785
theorem B3529793 : Blo 1468554 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B1653835 : Blo 1468554 1653835 := bstep (se 1 (by rfl) ⟨1240376, by rfl⟩ : syracuseStep 1653835 = 2480753) B2480753
theorem B2481239 : Blo 1468554 2481239 := bstep (se 1 (by rfl) ⟨1860929, by rfl⟩ : syracuseStep 2481239 = 3721859) B3721859
theorem B3308633 : Blo 1468554 3308633 := bstep (se 2 (by rfl) ⟨1240737, by rfl⟩ : syracuseStep 3308633 = 2481475) B2481475
theorem B2514059 : Blo 1468554 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B3718295 : Blo 1468554 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B3308723 : Blo 1468554 3308723 := bstep (se 1 (by rfl) ⟨2481542, by rfl⟩ : syracuseStep 3308723 = 4963085) B4963085
theorem B1653943 : Blo 1468554 1653943 := bstep (se 1 (by rfl) ⟨1240457, by rfl⟩ : syracuseStep 1653943 = 2480915) B2480915
theorem B11164877 : Blo 1468554 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B2202839 : Blo 1468554 2202839 := bstep (se 1 (by rfl) ⟨1652129, by rfl⟩ : syracuseStep 2202839 = 3304259) B3304259
theorem B2481367 : Blo 1468554 2481367 := bstep (se 1 (by rfl) ⟨1861025, by rfl⟩ : syracuseStep 2481367 = 3722051) B3722051
theorem B2202905 : Blo 1468554 2202905 := bstep (se 2 (by rfl) ⟨826089, by rfl⟩ : syracuseStep 2202905 = 1652179) B1652179
theorem B4185395 : Blo 1468554 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B1654123 : Blo 1468554 1654123 := bstep (se 1 (by rfl) ⟨1240592, by rfl⟩ : syracuseStep 1654123 = 2481185) B2481185
theorem B6274435 : Blo 1468554 6274435 := bstep (se 1 (by rfl) ⟨4705826, by rfl⟩ : syracuseStep 6274435 = 9411653) B9411653
theorem B2203019 : Blo 1468554 2203019 := bstep (se 1 (by rfl) ⟨1652264, by rfl⟩ : syracuseStep 2203019 = 3304529) B3304529
theorem B2203031 : Blo 1468554 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B10190231 : Blo 1468554 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B1654231 : Blo 1468554 1654231 := bstep (se 1 (by rfl) ⟨1240673, by rfl⟩ : syracuseStep 1654231 = 2481347) B2481347
theorem B2203097 : Blo 1468554 2203097 := bstep (se 2 (by rfl) ⟨826161, by rfl⟩ : syracuseStep 2203097 = 1652323) B1652323
theorem B26803781 : Blo 1468554 26803781 := bstep (se 4 (by rfl) ⟨2512854, by rfl⟩ : syracuseStep 26803781 = 5025709) B5025709
theorem B2203211 : Blo 1468554 2203211 := bstep (se 1 (by rfl) ⟨1652408, by rfl⟩ : syracuseStep 2203211 = 3304817) B3304817
theorem B2203223 : Blo 1468554 2203223 := bstep (se 1 (by rfl) ⟨1652417, by rfl⟩ : syracuseStep 2203223 = 3304835) B3304835
theorem B2203289 : Blo 1468554 2203289 := bstep (se 2 (by rfl) ⟨826233, by rfl⟩ : syracuseStep 2203289 = 1652467) B1652467
theorem B11165363 : Blo 1468554 11165363 := bstep (se 1 (by rfl) ⟨8374022, by rfl⟩ : syracuseStep 11165363 = 16748045) B16748045
theorem B2203403 : Blo 1468554 2203403 := bstep (se 1 (by rfl) ⟨1652552, by rfl⟩ : syracuseStep 2203403 = 3305105) B3305105
theorem B2203415 : Blo 1468554 2203415 := bstep (se 1 (by rfl) ⟨1652561, by rfl⟩ : syracuseStep 2203415 = 3305123) B3305123
theorem B2203481 : Blo 1468554 2203481 := bstep (se 2 (by rfl) ⟨826305, by rfl⟩ : syracuseStep 2203481 = 1652611) B1652611
theorem B3399553 : Blo 1468554 3399553 := bstep (se 2 (by rfl) ⟨1274832, by rfl⟩ : syracuseStep 3399553 = 2549665) B2549665
theorem B4718515 : Blo 1468554 4718515 := bstep (se 1 (by rfl) ⟨3538886, by rfl⟩ : syracuseStep 4718515 = 7077773) B7077773
theorem B3768257 : Blo 1468554 3768257 := bstep (se 2 (by rfl) ⟨1413096, by rfl⟩ : syracuseStep 3768257 = 2826193) B2826193
theorem B3719105 : Blo 1468554 3719105 := bstep (se 2 (by rfl) ⟨1394664, by rfl⟩ : syracuseStep 3719105 = 2789329) B2789329
theorem B2203595 : Blo 1468554 2203595 := bstep (se 1 (by rfl) ⟨1652696, by rfl⟩ : syracuseStep 2203595 = 3305393) B3305393
theorem B2203607 : Blo 1468554 2203607 := bstep (se 1 (by rfl) ⟨1652705, by rfl⟩ : syracuseStep 2203607 = 3305411) B3305411
theorem B2203655 : Blo 1468554 2203655 := bstep (se 1 (by rfl) ⟨1652741, by rfl⟩ : syracuseStep 2203655 = 3305483) B3305483
theorem B9543703 : Blo 1468554 9543703 := bstep (se 1 (by rfl) ⟨7157777, by rfl⟩ : syracuseStep 9543703 = 14315555) B14315555
theorem B2203691 : Blo 1468554 2203691 := bstep (se 1 (by rfl) ⟨1652768, by rfl⟩ : syracuseStep 2203691 = 3305537) B3305537
theorem B2203721 : Blo 1468554 2203721 := bstep (se 2 (by rfl) ⟨826395, by rfl⟩ : syracuseStep 2203721 = 1652791) B1652791
theorem B1859755 : Blo 1468554 1859755 := bstep (se 1 (by rfl) ⟨1394816, by rfl⟩ : syracuseStep 1859755 = 2789633) B2789633
theorem B2203835 : Blo 1468554 2203835 := bstep (se 1 (by rfl) ⟨1652876, by rfl⟩ : syracuseStep 2203835 = 3305753) B3305753
theorem B2203895 : Blo 1468554 2203895 := bstep (se 1 (by rfl) ⟨1652921, by rfl⟩ : syracuseStep 2203895 = 3305843) B3305843
theorem B2203919 : Blo 1468554 2203919 := bstep (se 1 (by rfl) ⟨1652939, by rfl⟩ : syracuseStep 2203919 = 3305879) B3305879
theorem B4186397 : Blo 1468554 4186397 := bstep (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) B1569899
theorem B2203961 : Blo 1468554 2203961 := bstep (se 2 (by rfl) ⟨826485, by rfl⟩ : syracuseStep 2203961 = 1652971) B1652971
theorem B2548027 : Blo 1468554 2548027 := bstep (se 1 (by rfl) ⟨1911020, by rfl⟩ : syracuseStep 2548027 = 3822041) B3822041
theorem B4956551 : Blo 1468554 4956551 := bstep (se 1 (by rfl) ⟨3717413, by rfl⟩ : syracuseStep 4956551 = 7434827) B7434827
theorem B2204039 : Blo 1468554 2204039 := bstep (se 1 (by rfl) ⟨1653029, by rfl⟩ : syracuseStep 2204039 = 3306059) B3306059
theorem B2204075 : Blo 1468554 2204075 := bstep (se 1 (by rfl) ⟨1653056, by rfl⟩ : syracuseStep 2204075 = 3306113) B3306113
theorem B2204105 : Blo 1468554 2204105 := bstep (se 2 (by rfl) ⟨826539, by rfl⟩ : syracuseStep 2204105 = 1653079) B1653079
theorem B8372747 : Blo 1468554 8372747 := bstep (se 1 (by rfl) ⟨6279560, by rfl⟩ : syracuseStep 8372747 = 12559121) B12559121
theorem B7438877 : Blo 1468554 7438877 := bstep (se 3 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 7438877 = 2789579) B2789579
theorem B2204219 : Blo 1468554 2204219 := bstep (se 1 (by rfl) ⟨1653164, by rfl⟩ : syracuseStep 2204219 = 3306329) B3306329
theorem B2204279 : Blo 1468554 2204279 := bstep (se 1 (by rfl) ⟨1653209, by rfl⟩ : syracuseStep 2204279 = 3306419) B3306419
theorem B4711031 : Blo 1468554 4711031 := bstep (se 1 (by rfl) ⟨3533273, by rfl⟩ : syracuseStep 4711031 = 7066547) B7066547
theorem B2204303 : Blo 1468554 2204303 := bstep (se 1 (by rfl) ⟨1653227, by rfl⟩ : syracuseStep 2204303 = 3306455) B3306455
theorem B2204345 : Blo 1468554 2204345 := bstep (se 2 (by rfl) ⟨826629, by rfl⟩ : syracuseStep 2204345 = 1653259) B1653259
theorem B8372929 : Blo 1468554 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B4956929 : Blo 1468554 4956929 := bstep (se 2 (by rfl) ⟨1858848, by rfl⟩ : syracuseStep 4956929 = 3717697) B3717697
theorem B2204423 : Blo 1468554 2204423 := bstep (se 1 (by rfl) ⟨1653317, by rfl⟩ : syracuseStep 2204423 = 3306635) B3306635
theorem B15885071 : Blo 1468554 15885071 := bstep (se 1 (by rfl) ⟨11913803, by rfl⟩ : syracuseStep 15885071 = 23827607) B23827607
theorem B34382627 : Blo 1468554 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B2204459 : Blo 1468554 2204459 := bstep (se 1 (by rfl) ⟨1653344, by rfl⟩ : syracuseStep 2204459 = 3306689) B3306689
theorem B2204489 : Blo 1468554 2204489 := bstep (se 2 (by rfl) ⟨826683, by rfl⟩ : syracuseStep 2204489 = 1653367) B1653367
theorem B5579705 : Blo 1468554 5579705 := bstep (se 2 (by rfl) ⟨2092389, by rfl⟩ : syracuseStep 5579705 = 4184779) B4184779
theorem B2204603 : Blo 1468554 2204603 := bstep (se 1 (by rfl) ⟨1653452, by rfl⟩ : syracuseStep 2204603 = 3306905) B3306905
theorem B2204663 : Blo 1468554 2204663 := bstep (se 1 (by rfl) ⟨1653497, by rfl⟩ : syracuseStep 2204663 = 3306995) B3306995
theorem B7439363 : Blo 1468554 7439363 := bstep (se 1 (by rfl) ⟨5579522, by rfl⟩ : syracuseStep 7439363 = 11159045) B11159045
theorem B2204687 : Blo 1468554 2204687 := bstep (se 1 (by rfl) ⟨1653515, by rfl⟩ : syracuseStep 2204687 = 3307031) B3307031
theorem B2384939 : Blo 1468554 2384939 := bstep (se 1 (by rfl) ⟨1788704, by rfl⟩ : syracuseStep 2384939 = 3577409) B3577409
theorem B2204729 : Blo 1468554 2204729 := bstep (se 2 (by rfl) ⟨826773, by rfl⟩ : syracuseStep 2204729 = 1653547) B1653547
theorem B3138679 : Blo 1468554 3138679 := bstep (se 1 (by rfl) ⟨2354009, by rfl⟩ : syracuseStep 3138679 = 4708019) B4708019
theorem B1860727 : Blo 1468554 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B2204807 : Blo 1468554 2204807 := bstep (se 1 (by rfl) ⟨1653605, by rfl⟩ : syracuseStep 2204807 = 3307211) B3307211
theorem B2204843 : Blo 1468554 2204843 := bstep (se 1 (by rfl) ⟨1653632, by rfl⟩ : syracuseStep 2204843 = 3307265) B3307265
theorem B2204873 : Blo 1468554 2204873 := bstep (se 2 (by rfl) ⟨826827, by rfl⟩ : syracuseStep 2204873 = 1653655) B1653655
theorem B11912507 : Blo 1468554 11912507 := bstep (se 1 (by rfl) ⟨8934380, by rfl⟩ : syracuseStep 11912507 = 17868761) B17868761
theorem B2204987 : Blo 1468554 2204987 := bstep (se 1 (by rfl) ⟨1653740, by rfl⟩ : syracuseStep 2204987 = 3307481) B3307481
theorem B3720563 : Blo 1468554 3720563 := bstep (se 1 (by rfl) ⟨2790422, by rfl⟩ : syracuseStep 3720563 = 5580845) B5580845
theorem B2205047 : Blo 1468554 2205047 := bstep (se 1 (by rfl) ⟨1653785, by rfl⟩ : syracuseStep 2205047 = 3307571) B3307571
theorem B2205071 : Blo 1468554 2205071 := bstep (se 1 (by rfl) ⟨1653803, by rfl⟩ : syracuseStep 2205071 = 3307607) B3307607
theorem B8365457 : Blo 1468554 8365457 := bstep (se 2 (by rfl) ⟨3137046, by rfl⟩ : syracuseStep 8365457 = 6274093) B6274093
theorem B10888595 : Blo 1468554 10888595 := bstep (se 1 (by rfl) ⟨8166446, by rfl⟩ : syracuseStep 10888595 = 16332893) B16332893
theorem B2205113 : Blo 1468554 2205113 := bstep (se 2 (by rfl) ⟨826917, by rfl⟩ : syracuseStep 2205113 = 1653835) B1653835
theorem B1861051 : Blo 1468554 1861051 := bstep (se 1 (by rfl) ⟨1395788, by rfl⟩ : syracuseStep 1861051 = 2791577) B2791577
theorem B2385353 : Blo 1468554 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B10192337 : Blo 1468554 10192337 := bstep (se 2 (by rfl) ⟨3822126, by rfl⟩ : syracuseStep 10192337 = 7644253) B7644253
theorem B2205191 : Blo 1468554 2205191 := bstep (se 1 (by rfl) ⟨1653893, by rfl⟩ : syracuseStep 2205191 = 3307787) B3307787
theorem B4957739 : Blo 1468554 4957739 := bstep (se 1 (by rfl) ⟨3718304, by rfl⟩ : syracuseStep 4957739 = 7436609) B7436609
theorem B2205227 : Blo 1468554 2205227 := bstep (se 1 (by rfl) ⟨1653920, by rfl⟩ : syracuseStep 2205227 = 3307841) B3307841
theorem B2205257 : Blo 1468554 2205257 := bstep (se 2 (by rfl) ⟨826971, by rfl⟩ : syracuseStep 2205257 = 1653943) B1653943
theorem B2205371 : Blo 1468554 2205371 := bstep (se 1 (by rfl) ⟨1654028, by rfl⟩ : syracuseStep 2205371 = 3308057) B3308057
theorem B2205431 : Blo 1468554 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B2205455 : Blo 1468554 2205455 := bstep (se 1 (by rfl) ⟨1654091, by rfl⟩ : syracuseStep 2205455 = 3308183) B3308183
theorem B2205497 : Blo 1468554 2205497 := bstep (se 2 (by rfl) ⟨827061, by rfl⟩ : syracuseStep 2205497 = 1654123) B1654123
theorem B8365913 : Blo 1468554 8365913 := bstep (se 2 (by rfl) ⟨3137217, by rfl⟩ : syracuseStep 8365913 = 6274435) B6274435
theorem B3721079 : Blo 1468554 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B2205575 : Blo 1468554 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B2205611 : Blo 1468554 2205611 := bstep (se 1 (by rfl) ⟨1654208, by rfl⟩ : syracuseStep 2205611 = 3308417) B3308417
theorem B2205641 : Blo 1468554 2205641 := bstep (se 2 (by rfl) ⟨827115, by rfl⟩ : syracuseStep 2205641 = 1654231) B1654231
theorem B18130949 : Blo 1468554 18130949 := bstep (se 4 (by rfl) ⟨1699776, by rfl⟩ : syracuseStep 18130949 = 3399553) B3399553
theorem B3180559 : Blo 1468554 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B2353195 : Blo 1468554 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B2205755 : Blo 1468554 2205755 := bstep (se 1 (by rfl) ⟨1654316, by rfl⟩ : syracuseStep 2205755 = 3308633) B3308633
theorem B2721911 : Blo 1468554 2721911 := bstep (se 1 (by rfl) ⟨2041433, by rfl⟩ : syracuseStep 2721911 = 4082867) B4082867
theorem B2205815 : Blo 1468554 2205815 := bstep (se 1 (by rfl) ⟨1654361, by rfl⟩ : syracuseStep 2205815 = 3308723) B3308723
theorem B1468559 : Blo 1468554 1468559 := bstep (se 1 (by rfl) ⟨1101419, by rfl⟩ : syracuseStep 1468559 = 2202839) B2202839
theorem B1468603 : Blo 1468554 1468603 := bstep (se 1 (by rfl) ⟨1101452, by rfl⟩ : syracuseStep 1468603 = 2202905) B2202905
theorem B1468679 : Blo 1468554 1468679 := bstep (se 1 (by rfl) ⟨1101509, by rfl⟩ : syracuseStep 1468679 = 2203019) B2203019
theorem B1468687 : Blo 1468554 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B6793487 : Blo 1468554 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B6277409 : Blo 1468554 6277409 := bstep (se 2 (by rfl) ⟨2354028, by rfl⟩ : syracuseStep 6277409 = 4708057) B4708057
theorem B1468731 : Blo 1468554 1468731 := bstep (se 1 (by rfl) ⟨1101548, by rfl⟩ : syracuseStep 1468731 = 2203097) B2203097
theorem B15878531 : Blo 1468554 15878531 := bstep (se 1 (by rfl) ⟨11908898, by rfl⟩ : syracuseStep 15878531 = 23817797) B23817797
theorem B17869187 : Blo 1468554 17869187 := bstep (se 1 (by rfl) ⟨13401890, by rfl⟩ : syracuseStep 17869187 = 26803781) B26803781
theorem B1468807 : Blo 1468554 1468807 := bstep (se 1 (by rfl) ⟨1101605, by rfl⟩ : syracuseStep 1468807 = 2203211) B2203211
theorem B1468815 : Blo 1468554 1468815 := bstep (se 1 (by rfl) ⟨1101611, by rfl⟩ : syracuseStep 1468815 = 2203223) B2203223
theorem B1468859 : Blo 1468554 1468859 := bstep (se 1 (by rfl) ⟨1101644, by rfl⟩ : syracuseStep 1468859 = 2203289) B2203289
theorem B11160017 : Blo 1468554 11160017 := bstep (se 2 (by rfl) ⟨4185006, by rfl⟩ : syracuseStep 11160017 = 8370013) B8370013
theorem B1468935 : Blo 1468554 1468935 := bstep (se 1 (by rfl) ⟨1101701, by rfl⟩ : syracuseStep 1468935 = 2203403) B2203403
theorem B1468943 : Blo 1468554 1468943 := bstep (se 1 (by rfl) ⟨1101707, by rfl⟩ : syracuseStep 1468943 = 2203415) B2203415
theorem B1468987 : Blo 1468554 1468987 := bstep (se 1 (by rfl) ⟨1101740, by rfl⟩ : syracuseStep 1468987 = 2203481) B2203481
theorem B7440983 : Blo 1468554 7440983 := bstep (se 1 (by rfl) ⟨5580737, by rfl⟩ : syracuseStep 7440983 = 11161475) B11161475
theorem B3770999 : Blo 1468554 3770999 := bstep (se 1 (by rfl) ⟨2828249, by rfl⟩ : syracuseStep 3770999 = 5656499) B5656499
theorem B1469063 : Blo 1468554 1469063 := bstep (se 1 (by rfl) ⟨1101797, by rfl⟩ : syracuseStep 1469063 = 2203595) B2203595
theorem B1469071 : Blo 1468554 1469071 := bstep (se 1 (by rfl) ⟨1101803, by rfl⟩ : syracuseStep 1469071 = 2203607) B2203607
theorem B1469115 : Blo 1468554 1469115 := bstep (se 1 (by rfl) ⟨1101836, by rfl⟩ : syracuseStep 1469115 = 2203673) B2203673
theorem B19098305 : Blo 1468554 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B1469191 : Blo 1468554 1469191 := bstep (se 1 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 1469191 = 2203787) B2203787
theorem B1469199 : Blo 1468554 1469199 := bstep (se 1 (by rfl) ⟨1101899, by rfl⟩ : syracuseStep 1469199 = 2203799) B2203799
theorem B4705057 : Blo 1468554 4705057 := bstep (se 2 (by rfl) ⟨1764396, by rfl⟩ : syracuseStep 4705057 = 3528793) B3528793
theorem B7940915 : Blo 1468554 7940915 := bstep (se 1 (by rfl) ⟨5955686, by rfl⟩ : syracuseStep 7940915 = 11911373) B11911373
theorem B1469243 : Blo 1468554 1469243 := bstep (se 1 (by rfl) ⟨1101932, by rfl⟩ : syracuseStep 1469243 = 2203865) B2203865
theorem B4959035 : Blo 1468554 4959035 := bstep (se 1 (by rfl) ⟨3719276, by rfl⟩ : syracuseStep 4959035 = 7438553) B7438553
theorem B3722071 : Blo 1468554 3722071 := bstep (se 1 (by rfl) ⟨2791553, by rfl⟩ : syracuseStep 3722071 = 5583107) B5583107
theorem B2091911 : Blo 1468554 2091911 := bstep (se 1 (by rfl) ⟨1568933, by rfl⟩ : syracuseStep 2091911 = 3137867) B3137867
theorem B1469319 : Blo 1468554 1469319 := bstep (se 1 (by rfl) ⟨1101989, by rfl⟩ : syracuseStep 1469319 = 2203979) B2203979
theorem B1469327 : Blo 1468554 1469327 := bstep (se 1 (by rfl) ⟨1101995, by rfl⟩ : syracuseStep 1469327 = 2203991) B2203991
theorem B1469371 : Blo 1468554 1469371 := bstep (se 1 (by rfl) ⟨1102028, by rfl⟩ : syracuseStep 1469371 = 2204057) B2204057
theorem B1469447 : Blo 1468554 1469447 := bstep (se 1 (by rfl) ⟨1102085, by rfl⟩ : syracuseStep 1469447 = 2204171) B2204171
theorem B68766731 : Blo 1468554 68766731 := bstep (se 1 (by rfl) ⟨51575048, by rfl⟩ : syracuseStep 68766731 = 103150097) B103150097
theorem B1469455 : Blo 1468554 1469455 := bstep (se 1 (by rfl) ⟨1102091, by rfl⟩ : syracuseStep 1469455 = 2204183) B2204183
theorem B9415703 : Blo 1468554 9415703 := bstep (se 1 (by rfl) ⟨7061777, by rfl⟩ : syracuseStep 9415703 = 14123555) B14123555
theorem B1469499 : Blo 1468554 1469499 := bstep (se 1 (by rfl) ⟨1102124, by rfl⟩ : syracuseStep 1469499 = 2204249) B2204249
theorem B4467773 : Blo 1468554 4467773 := bstep (se 3 (by rfl) ⟨837707, by rfl⟩ : syracuseStep 4467773 = 1675415) B1675415
theorem B7441469 : Blo 1468554 7441469 := bstep (se 3 (by rfl) ⟨1395275, by rfl⟩ : syracuseStep 7441469 = 2790551) B2790551
theorem B2092105 : Blo 1468554 2092105 := bstep (se 2 (by rfl) ⟨784539, by rfl⟩ : syracuseStep 2092105 = 1569079) B1569079
theorem B3304583 : Blo 1468554 3304583 := bstep (se 1 (by rfl) ⟨2478437, by rfl⟩ : syracuseStep 3304583 = 4956875) B4956875
theorem B1469575 : Blo 1468554 1469575 := bstep (se 1 (by rfl) ⟨1102181, by rfl⟩ : syracuseStep 1469575 = 2204363) B2204363
theorem B1469583 : Blo 1468554 1469583 := bstep (se 1 (by rfl) ⟨1102187, by rfl⟩ : syracuseStep 1469583 = 2204375) B2204375
theorem B12561581 : Blo 1468554 12561581 := bstep (se 3 (by rfl) ⟨2355296, by rfl⟩ : syracuseStep 12561581 = 4710593) B4710593
theorem B1469627 : Blo 1468554 1469627 := bstep (se 1 (by rfl) ⟨1102220, by rfl⟩ : syracuseStep 1469627 = 2204441) B2204441
theorem B1985737 : Blo 1468554 1985737 := bstep (se 2 (by rfl) ⟨744651, by rfl⟩ : syracuseStep 1985737 = 1489303) B1489303
theorem B1469703 : Blo 1468554 1469703 := bstep (se 1 (by rfl) ⟨1102277, by rfl⟩ : syracuseStep 1469703 = 2204555) B2204555
theorem B1469711 : Blo 1468554 1469711 := bstep (se 1 (by rfl) ⟨1102283, by rfl⟩ : syracuseStep 1469711 = 2204567) B2204567
theorem B4959521 : Blo 1468554 4959521 := bstep (se 2 (by rfl) ⟨1859820, by rfl⟩ : syracuseStep 4959521 = 3719641) B3719641
theorem B3304763 : Blo 1468554 3304763 := bstep (se 1 (by rfl) ⟨2478572, by rfl⟩ : syracuseStep 3304763 = 4957145) B4957145
theorem B1469755 : Blo 1468554 1469755 := bstep (se 1 (by rfl) ⟨1102316, by rfl⟩ : syracuseStep 1469755 = 2204633) B2204633
theorem B7064891 : Blo 1468554 7064891 := bstep (se 1 (by rfl) ⟨5298668, by rfl⟩ : syracuseStep 7064891 = 10597337) B10597337
theorem B7949627 : Blo 1468554 7949627 := bstep (se 1 (by rfl) ⟨5962220, by rfl⟩ : syracuseStep 7949627 = 11924441) B11924441
theorem B1469831 : Blo 1468554 1469831 := bstep (se 1 (by rfl) ⟨1102373, by rfl⟩ : syracuseStep 1469831 = 2204747) B2204747
theorem B1789327 : Blo 1468554 1789327 := bstep (se 1 (by rfl) ⟨1341995, by rfl⟩ : syracuseStep 1789327 = 2683991) B2683991
theorem B1469839 : Blo 1468554 1469839 := bstep (se 1 (by rfl) ⟨1102379, by rfl⟩ : syracuseStep 1469839 = 2204759) B2204759
theorem B1985963 : Blo 1468554 1985963 := bstep (se 1 (by rfl) ⟨1489472, by rfl⟩ : syracuseStep 1985963 = 2978945) B2978945
theorem B3304889 : Blo 1468554 3304889 := bstep (se 2 (by rfl) ⟨1239333, by rfl⟩ : syracuseStep 3304889 = 2478667) B2478667
theorem B1469883 : Blo 1468554 1469883 := bstep (se 1 (by rfl) ⟨1102412, by rfl⟩ : syracuseStep 1469883 = 2204825) B2204825
theorem B1469959 : Blo 1468554 1469959 := bstep (se 1 (by rfl) ⟨1102469, by rfl⟩ : syracuseStep 1469959 = 2204939) B2204939
theorem B1469967 : Blo 1468554 1469967 := bstep (se 1 (by rfl) ⟨1102475, by rfl⟩ : syracuseStep 1469967 = 2204951) B2204951
theorem B1470011 : Blo 1468554 1470011 := bstep (se 1 (by rfl) ⟨1102508, by rfl⟩ : syracuseStep 1470011 = 2205017) B2205017
theorem B2092663 : Blo 1468554 2092663 := bstep (se 1 (by rfl) ⟨1569497, by rfl⟩ : syracuseStep 2092663 = 3138995) B3138995
theorem B1470087 : Blo 1468554 1470087 := bstep (se 1 (by rfl) ⟨1102565, by rfl⟩ : syracuseStep 1470087 = 2205131) B2205131
theorem B2584199 : Blo 1468554 2584199 := bstep (se 1 (by rfl) ⟨1938149, by rfl⟩ : syracuseStep 2584199 = 3876299) B3876299
theorem B1470095 : Blo 1468554 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B1470139 : Blo 1468554 1470139 := bstep (se 1 (by rfl) ⟨1102604, by rfl⟩ : syracuseStep 1470139 = 2205209) B2205209
theorem B1470215 : Blo 1468554 1470215 := bstep (se 1 (by rfl) ⟨1102661, by rfl⟩ : syracuseStep 1470215 = 2205323) B2205323
theorem B3305231 : Blo 1468554 3305231 := bstep (se 1 (by rfl) ⟨2478923, by rfl⟩ : syracuseStep 3305231 = 4957847) B4957847
theorem B1470223 : Blo 1468554 1470223 := bstep (se 1 (by rfl) ⟨1102667, by rfl⟩ : syracuseStep 1470223 = 2205335) B2205335
theorem B3305249 : Blo 1468554 3305249 := bstep (se 2 (by rfl) ⟨1239468, by rfl⟩ : syracuseStep 3305249 = 2478937) B2478937
theorem B1470267 : Blo 1468554 1470267 := bstep (se 1 (by rfl) ⟨1102700, by rfl⟩ : syracuseStep 1470267 = 2205401) B2205401
theorem B4960115 : Blo 1468554 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B1470343 : Blo 1468554 1470343 := bstep (se 1 (by rfl) ⟨1102757, by rfl⟩ : syracuseStep 1470343 = 2205515) B2205515
theorem B1470351 : Blo 1468554 1470351 := bstep (se 1 (by rfl) ⟨1102763, by rfl⟩ : syracuseStep 1470351 = 2205527) B2205527
theorem B15896483 : Blo 1468554 15896483 := bstep (se 1 (by rfl) ⟨11922362, by rfl⟩ : syracuseStep 15896483 = 23844725) B23844725
theorem B1470395 : Blo 1468554 1470395 := bstep (se 1 (by rfl) ⟨1102796, by rfl⟩ : syracuseStep 1470395 = 2205593) B2205593
theorem B1470471 : Blo 1468554 1470471 := bstep (se 1 (by rfl) ⟨1102853, by rfl⟩ : syracuseStep 1470471 = 2205707) B2205707
theorem B2682895 : Blo 1468554 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B1470479 : Blo 1468554 1470479 := bstep (se 1 (by rfl) ⟨1102859, by rfl⟩ : syracuseStep 1470479 = 2205719) B2205719
theorem B30167063 : Blo 1468554 30167063 := bstep (se 1 (by rfl) ⟨22625297, by rfl⟩ : syracuseStep 30167063 = 45250595) B45250595
theorem B2355259 : Blo 1468554 2355259 := bstep (se 1 (by rfl) ⟨1766444, by rfl⟩ : syracuseStep 2355259 = 3532889) B3532889
theorem B1470523 : Blo 1468554 1470523 := bstep (se 1 (by rfl) ⟨1102892, by rfl⟩ : syracuseStep 1470523 = 2205785) B2205785
theorem B26816629 : Blo 1468554 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B3305591 : Blo 1468554 3305591 := bstep (se 1 (by rfl) ⟨2479193, by rfl⟩ : syracuseStep 3305591 = 4958387) B4958387
theorem B2478215 : Blo 1468554 2478215 := bstep (se 1 (by rfl) ⟨1858661, by rfl⟩ : syracuseStep 2478215 = 3717323) B3717323
theorem B3305771 : Blo 1468554 3305771 := bstep (se 1 (by rfl) ⟨2479328, by rfl⟩ : syracuseStep 3305771 = 4958657) B4958657
theorem B2093369 : Blo 1468554 2093369 := bstep (se 2 (by rfl) ⟨785013, by rfl⟩ : syracuseStep 2093369 = 1570027) B1570027
theorem B2978167 : Blo 1468554 2978167 := bstep (se 1 (by rfl) ⟨2233625, by rfl⟩ : syracuseStep 2978167 = 4467251) B4467251
theorem B2093455 : Blo 1468554 2093455 := bstep (se 1 (by rfl) ⟨1570091, by rfl⟩ : syracuseStep 2093455 = 3140183) B3140183
theorem B16740755 : Blo 1468554 16740755 := bstep (se 1 (by rfl) ⟨12555566, by rfl⟩ : syracuseStep 16740755 = 25111133) B25111133
theorem B7942553 : Blo 1468554 7942553 := bstep (se 2 (by rfl) ⟨2978457, by rfl⟩ : syracuseStep 7942553 = 5956915) B5956915
theorem B2093483 : Blo 1468554 2093483 := bstep (se 1 (by rfl) ⟨1570112, by rfl⟩ : syracuseStep 2093483 = 3140225) B3140225
theorem B5583289 : Blo 1468554 5583289 := bstep (se 2 (by rfl) ⟨2093733, by rfl⟩ : syracuseStep 5583289 = 4187467) B4187467
theorem B1765819 : Blo 1468554 1765819 := bstep (se 1 (by rfl) ⟨1324364, by rfl⟩ : syracuseStep 1765819 = 2648729) B2648729
theorem B4706903 : Blo 1468554 4706903 := bstep (se 1 (by rfl) ⟨3530177, by rfl⟩ : syracuseStep 4706903 = 7060355) B7060355
theorem B6279767 : Blo 1468554 6279767 := bstep (se 1 (by rfl) ⟨4709825, by rfl⟩ : syracuseStep 6279767 = 9419651) B9419651
theorem B3306131 : Blo 1468554 3306131 := bstep (se 1 (by rfl) ⟨2479598, by rfl⟩ : syracuseStep 3306131 = 4959197) B4959197
theorem B2790035 : Blo 1468554 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B3306185 : Blo 1468554 3306185 := bstep (se 2 (by rfl) ⟨1239819, by rfl⟩ : syracuseStep 3306185 = 2479639) B2479639
theorem B7434989 : Blo 1468554 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B2478863 : Blo 1468554 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B7443251 : Blo 1468554 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B2790263 : Blo 1468554 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B8369081 : Blo 1468554 8369081 := bstep (se 2 (by rfl) ⟨3138405, by rfl⟩ : syracuseStep 8369081 = 6276811) B6276811
theorem B4469879 : Blo 1468554 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B7443575 : Blo 1468554 7443575 := bstep (se 1 (by rfl) ⟨5582681, by rfl⟩ : syracuseStep 7443575 = 11165363) B11165363
theorem B2512171 : Blo 1468554 2512171 := bstep (se 1 (by rfl) ⟨1884128, by rfl⟩ : syracuseStep 2512171 = 3768257) B3768257
theorem B2479403 : Blo 1468554 2479403 := bstep (se 1 (by rfl) ⟨1859552, by rfl⟩ : syracuseStep 2479403 = 3719105) B3719105
theorem B3306887 : Blo 1468554 3306887 := bstep (se 1 (by rfl) ⟨2480165, by rfl⟩ : syracuseStep 3306887 = 4960331) B4960331
theorem B4470169 : Blo 1468554 4470169 := bstep (se 2 (by rfl) ⟨1676313, by rfl⟩ : syracuseStep 4470169 = 3352627) B3352627
theorem B4183481 : Blo 1468554 4183481 := bstep (se 2 (by rfl) ⟨1568805, by rfl⟩ : syracuseStep 4183481 = 3137611) B3137611
theorem B7435799 : Blo 1468554 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B4183595 : Blo 1468554 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B3307067 : Blo 1468554 3307067 := bstep (se 1 (by rfl) ⟨2480300, by rfl⟩ : syracuseStep 3307067 = 4960601) B4960601
theorem B1652359 : Blo 1468554 1652359 := bstep (se 1 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 1652359 = 2478539) B2478539
theorem B2479801 : Blo 1468554 2479801 := bstep (se 2 (by rfl) ⟨929925, by rfl⟩ : syracuseStep 2479801 = 1859851) B1859851
theorem B3307193 : Blo 1468554 3307193 := bstep (se 2 (by rfl) ⟨1240197, by rfl⟩ : syracuseStep 3307193 = 2480395) B2480395
theorem B10057445 : Blo 1468554 10057445 := bstep (se 4 (by rfl) ⟨942885, by rfl⟩ : syracuseStep 10057445 = 1885771) B1885771
theorem B1652539 : Blo 1468554 1652539 := bstep (se 1 (by rfl) ⟨1239404, by rfl⟩ : syracuseStep 1652539 = 2478809) B2478809
theorem B1488775 : Blo 1468554 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B6273035 : Blo 1468554 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B3307535 : Blo 1468554 3307535 := bstep (se 1 (by rfl) ⟨2480651, by rfl⟩ : syracuseStep 3307535 = 4961303) B4961303
theorem B4773917 : Blo 1468554 4773917 := bstep (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) B1790219
theorem B3528737 : Blo 1468554 3528737 := bstep (se 2 (by rfl) ⟨1323276, by rfl⟩ : syracuseStep 3528737 = 2646553) B2646553
theorem B3307553 : Blo 1468554 3307553 := bstep (se 2 (by rfl) ⟨1240332, by rfl⟩ : syracuseStep 3307553 = 2480665) B2480665
theorem B7444547 : Blo 1468554 7444547 := bstep (se 1 (by rfl) ⟨5583410, by rfl⟩ : syracuseStep 7444547 = 11166821) B11166821
theorem B1653007 : Blo 1468554 1653007 := bstep (se 1 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 1653007 = 2479511) B2479511
theorem B6273395 : Blo 1468554 6273395 := bstep (se 1 (by rfl) ⟨4705046, by rfl⟩ : syracuseStep 6273395 = 9410093) B9410093
theorem B2480503 : Blo 1468554 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B3307895 : Blo 1468554 3307895 := bstep (se 1 (by rfl) ⟨2480921, by rfl⟩ : syracuseStep 3307895 = 4961843) B4961843
theorem B2980243 : Blo 1468554 2980243 := bstep (se 1 (by rfl) ⟨2235182, by rfl⟩ : syracuseStep 2980243 = 4470365) B4470365
theorem B4962707 : Blo 1468554 4962707 := bstep (se 1 (by rfl) ⟨3722030, by rfl⟩ : syracuseStep 4962707 = 7444061) B7444061
theorem B5298641 : Blo 1468554 5298641 := bstep (se 2 (by rfl) ⟨1986990, by rfl⟩ : syracuseStep 5298641 = 3973981) B3973981
theorem B3717647 : Blo 1468554 3717647 := bstep (se 1 (by rfl) ⟨2788235, by rfl⟩ : syracuseStep 3717647 = 5576471) B5576471
theorem B5577245 : Blo 1468554 5577245 := bstep (se 3 (by rfl) ⟨1045733, by rfl⟩ : syracuseStep 5577245 = 2091467) B2091467
theorem B3308075 : Blo 1468554 3308075 := bstep (se 1 (by rfl) ⟨2481056, by rfl⟩ : syracuseStep 3308075 = 4962113) B4962113
theorem B2480699 : Blo 1468554 2480699 := bstep (se 1 (by rfl) ⟨1860524, by rfl⟩ : syracuseStep 2480699 = 3721049) B3721049
theorem B4184723 : Blo 1468554 4184723 := bstep (se 1 (by rfl) ⟨3138542, by rfl⟩ : syracuseStep 4184723 = 6277085) B6277085
theorem B1673501381 : Blo 1468554 1673501381 := bstep (se 4 (by rfl) ⟨156890754, by rfl⟩ : syracuseStep 1673501381 = 313781509) B313781509
theorem B1653511 : Blo 1468554 1653511 := bstep (se 1 (by rfl) ⟨1240133, by rfl⟩ : syracuseStep 1653511 = 2480267) B2480267
theorem B25115507 : Blo 1468554 25115507 := bstep (se 1 (by rfl) ⟨18836630, by rfl⟩ : syracuseStep 25115507 = 37673261) B37673261
theorem B2120591 : Blo 1468554 2120591 := bstep (se 1 (by rfl) ⟨1590443, by rfl⟩ : syracuseStep 2120591 = 3180887) B3180887
theorem B3308435 : Blo 1468554 3308435 := bstep (se 1 (by rfl) ⟨2481326, by rfl⟩ : syracuseStep 3308435 = 4962653) B4962653
theorem B1653691 : Blo 1468554 1653691 := bstep (se 1 (by rfl) ⟨1240268, by rfl⟩ : syracuseStep 1653691 = 2480537) B2480537
theorem B2481097 : Blo 1468554 2481097 := bstep (se 2 (by rfl) ⟨930411, by rfl⟩ : syracuseStep 2481097 = 1860823) B1860823
theorem B3308489 : Blo 1468554 3308489 := bstep (se 2 (by rfl) ⟨1240683, by rfl⟩ : syracuseStep 3308489 = 2481367) B2481367
theorem B5028875 : Blo 1468554 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B4185121 : Blo 1468554 4185121 := bstep (se 2 (by rfl) ⟨1569420, by rfl⟩ : syracuseStep 4185121 = 3138841) B3138841
theorem B13597757 : Blo 1468554 13597757 := bstep (se 3 (by rfl) ⟨2549579, by rfl⟩ : syracuseStep 13597757 = 5099159) B5099159
theorem B7060547 : Blo 1468554 7060547 := bstep (se 1 (by rfl) ⟨5295410, by rfl⟩ : syracuseStep 7060547 = 10590821) B10590821
theorem B5954647 : Blo 1468554 5954647 := bstep (se 1 (by rfl) ⟨4465985, by rfl⟩ : syracuseStep 5954647 = 8931971) B8931971
theorem B7945303 : Blo 1468554 7945303 := bstep (se 1 (by rfl) ⟨5958977, by rfl⟩ : syracuseStep 7945303 = 11917955) B11917955
theorem B3718345 : Blo 1468554 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B5577929 : Blo 1468554 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B3529985 : Blo 1468554 3529985 := bstep (se 2 (by rfl) ⟨1323744, by rfl⟩ : syracuseStep 3529985 = 2647489) B2647489
theorem B2202887 : Blo 1468554 2202887 := bstep (se 1 (by rfl) ⟨1652165, by rfl⟩ : syracuseStep 2202887 = 3304331) B3304331
theorem B8371471 : Blo 1468554 8371471 := bstep (se 1 (by rfl) ⟨6278603, by rfl⟩ : syracuseStep 8371471 = 12557207) B12557207
theorem B2202923 : Blo 1468554 2202923 := bstep (se 1 (by rfl) ⟨1652192, by rfl⟩ : syracuseStep 2202923 = 3304385) B3304385
theorem B2202953 : Blo 1468554 2202953 := bstep (se 2 (by rfl) ⟨826107, by rfl⟩ : syracuseStep 2202953 = 1652215) B1652215
theorem B3718487 : Blo 1468554 3718487 := bstep (se 1 (by rfl) ⟨2788865, by rfl⟩ : syracuseStep 3718487 = 5577731) B5577731
theorem B1654159 : Blo 1468554 1654159 := bstep (se 1 (by rfl) ⟨1240619, by rfl⟩ : syracuseStep 1654159 = 2481239) B2481239
theorem B2203067 : Blo 1468554 2203067 := bstep (se 1 (by rfl) ⟨1652300, by rfl⟩ : syracuseStep 2203067 = 3304601) B3304601
theorem B2203127 : Blo 1468554 2203127 := bstep (se 1 (by rfl) ⟨1652345, by rfl⟩ : syracuseStep 2203127 = 3304691) B3304691
theorem B2203151 : Blo 1468554 2203151 := bstep (se 1 (by rfl) ⟨1652363, by rfl⟩ : syracuseStep 2203151 = 3304727) B3304727
theorem B3137039 : Blo 1468554 3137039 := bstep (se 1 (by rfl) ⟨2352779, by rfl⟩ : syracuseStep 3137039 = 4705559) B4705559
theorem B2203193 : Blo 1468554 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B5955133 : Blo 1468554 5955133 := bstep (se 3 (by rfl) ⟨1116587, by rfl⟩ : syracuseStep 5955133 = 2233175) B2233175
theorem B2203271 : Blo 1468554 2203271 := bstep (se 1 (by rfl) ⟨1652453, by rfl⟩ : syracuseStep 2203271 = 3304907) B3304907
theorem B2203307 : Blo 1468554 2203307 := bstep (se 1 (by rfl) ⟨1652480, by rfl⟩ : syracuseStep 2203307 = 3304961) B3304961
theorem B2203337 : Blo 1468554 2203337 := bstep (se 2 (by rfl) ⟨826251, by rfl⟩ : syracuseStep 2203337 = 1652503) B1652503
theorem B2203451 : Blo 1468554 2203451 := bstep (se 1 (by rfl) ⟨1652588, by rfl⟩ : syracuseStep 2203451 = 3305177) B3305177
theorem B2203511 : Blo 1468554 2203511 := bstep (se 1 (by rfl) ⟨1652633, by rfl⟩ : syracuseStep 2203511 = 3305267) B3305267
theorem B2203535 : Blo 1468554 2203535 := bstep (se 1 (by rfl) ⟨1652651, by rfl⟩ : syracuseStep 2203535 = 3305303) B3305303
theorem B6291353 : Blo 1468554 6291353 := bstep (se 2 (by rfl) ⟨2359257, by rfl⟩ : syracuseStep 6291353 = 4718515) B4718515
theorem B4186009 : Blo 1468554 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B2203577 : Blo 1468554 2203577 := bstep (se 2 (by rfl) ⟨826341, by rfl⟩ : syracuseStep 2203577 = 1652683) B1652683
theorem B20111375 : Blo 1468554 20111375 := bstep (se 1 (by rfl) ⟨15083531, by rfl⟩ : syracuseStep 20111375 = 30167063) B30167063
theorem B2203727 : Blo 1468554 2203727 := bstep (se 1 (by rfl) ⟨1652795, by rfl⟩ : syracuseStep 2203727 = 3305591) B3305591
theorem B2203847 : Blo 1468554 2203847 := bstep (se 1 (by rfl) ⟨1652885, by rfl⟩ : syracuseStep 2203847 = 3305771) B3305771
theorem B12550373 : Blo 1468554 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B7258429 : Blo 1468554 7258429 := bstep (se 3 (by rfl) ⟨1360955, by rfl⟩ : syracuseStep 7258429 = 2721911) B2721911
theorem B2204009 : Blo 1468554 2204009 := bstep (se 2 (by rfl) ⟨826503, by rfl⟩ : syracuseStep 2204009 = 1653007) B1653007
theorem B3137935 : Blo 1468554 3137935 := bstep (se 1 (by rfl) ⟨2353451, by rfl⟩ : syracuseStep 3137935 = 4706903) B4706903
theorem B4186511 : Blo 1468554 4186511 := bstep (se 1 (by rfl) ⟨3139883, by rfl⟩ : syracuseStep 4186511 = 6279767) B6279767
theorem B2204087 : Blo 1468554 2204087 := bstep (se 1 (by rfl) ⟨1653065, by rfl⟩ : syracuseStep 2204087 = 3306131) B3306131
theorem B1860023 : Blo 1468554 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B2204123 : Blo 1468554 2204123 := bstep (se 1 (by rfl) ⟨1653092, by rfl⟩ : syracuseStep 2204123 = 3306185) B3306185
theorem B4956659 : Blo 1468554 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B22921751 : Blo 1468554 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B3973657 : Blo 1468554 3973657 := bstep (se 2 (by rfl) ⟨1490121, by rfl⟩ : syracuseStep 3973657 = 2980243) B2980243
theorem B1860175 : Blo 1468554 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B5579387 : Blo 1468554 5579387 := bstep (se 1 (by rfl) ⟨4184540, by rfl⟩ : syracuseStep 5579387 = 8369081) B8369081
theorem B3719803 : Blo 1468554 3719803 := bstep (se 1 (by rfl) ⟨2789852, by rfl⟩ : syracuseStep 3719803 = 5579705) B5579705
theorem B9413293 : Blo 1468554 9413293 := bstep (se 3 (by rfl) ⟨1764992, by rfl⟩ : syracuseStep 9413293 = 3529985) B3529985
theorem B1589959 : Blo 1468554 1589959 := bstep (se 1 (by rfl) ⟨1192469, by rfl⟩ : syracuseStep 1589959 = 2384939) B2384939
theorem B2204591 : Blo 1468554 2204591 := bstep (se 1 (by rfl) ⟨1653443, by rfl⟩ : syracuseStep 2204591 = 3306887) B3306887
theorem B7259063 : Blo 1468554 7259063 := bstep (se 1 (by rfl) ⟨5444297, by rfl⟩ : syracuseStep 7259063 = 10888595) B10888595
theorem B2204681 : Blo 1468554 2204681 := bstep (se 2 (by rfl) ⟨826755, by rfl⟩ : syracuseStep 2204681 = 1653511) B1653511
theorem B4957199 : Blo 1468554 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B2204711 : Blo 1468554 2204711 := bstep (se 1 (by rfl) ⟨1653533, by rfl⟩ : syracuseStep 2204711 = 3307067) B3307067
theorem B2204795 : Blo 1468554 2204795 := bstep (se 1 (by rfl) ⟨1653596, by rfl⟩ : syracuseStep 2204795 = 3307193) B3307193
theorem B2204921 : Blo 1468554 2204921 := bstep (se 2 (by rfl) ⟨826845, by rfl⟩ : syracuseStep 2204921 = 1653691) B1653691
theorem B2205023 : Blo 1468554 2205023 := bstep (se 1 (by rfl) ⟨1653767, by rfl⟩ : syracuseStep 2205023 = 3307535) B3307535
theorem B2352491 : Blo 1468554 2352491 := bstep (se 1 (by rfl) ⟨1764368, by rfl⟩ : syracuseStep 2352491 = 3528737) B3528737
theorem B2205035 : Blo 1468554 2205035 := bstep (se 1 (by rfl) ⟨1653776, by rfl⟩ : syracuseStep 2205035 = 3307553) B3307553
theorem B5580161 : Blo 1468554 5580161 := bstep (se 2 (by rfl) ⟨2092560, by rfl⟩ : syracuseStep 5580161 = 4185121) B4185121
theorem B7939529 : Blo 1468554 7939529 := bstep (se 2 (by rfl) ⟨2977323, by rfl⟩ : syracuseStep 7939529 = 5954647) B5954647
theorem B10593737 : Blo 1468554 10593737 := bstep (se 2 (by rfl) ⟨3972651, by rfl⟩ : syracuseStep 10593737 = 7945303) B7945303
theorem B25093637 : Blo 1468554 25093637 := bstep (se 4 (by rfl) ⟨2352528, by rfl⟩ : syracuseStep 25093637 = 4705057) B4705057
theorem B2205263 : Blo 1468554 2205263 := bstep (se 1 (by rfl) ⟨1653947, by rfl⟩ : syracuseStep 2205263 = 3307895) B3307895
theorem B11912791 : Blo 1468554 11912791 := bstep (se 1 (by rfl) ⟨8934593, by rfl⟩ : syracuseStep 11912791 = 17869187) B17869187
theorem B4957793 : Blo 1468554 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B2647649 : Blo 1468554 2647649 := bstep (se 2 (by rfl) ⟨992868, by rfl⟩ : syracuseStep 2647649 = 1985737) B1985737
theorem B7440011 : Blo 1468554 7440011 := bstep (se 1 (by rfl) ⟨5580008, by rfl⟩ : syracuseStep 7440011 = 11160017) B11160017
theorem B3532427 : Blo 1468554 3532427 := bstep (se 1 (by rfl) ⟨2649320, by rfl⟩ : syracuseStep 3532427 = 5298641) B5298641
theorem B2205383 : Blo 1468554 2205383 := bstep (se 1 (by rfl) ⟨1654037, by rfl⟩ : syracuseStep 2205383 = 3308075) B3308075
theorem B12732203 : Blo 1468554 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B2385769 : Blo 1468554 2385769 := bstep (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) B1789327
theorem B2205545 : Blo 1468554 2205545 := bstep (se 2 (by rfl) ⟨827079, by rfl⟩ : syracuseStep 2205545 = 1654159) B1654159
theorem B5293943 : Blo 1468554 5293943 := bstep (se 1 (by rfl) ⟨3970457, by rfl⟩ : syracuseStep 5293943 = 7940915) B7940915
theorem B2205623 : Blo 1468554 2205623 := bstep (se 1 (by rfl) ⟨1654217, by rfl⟩ : syracuseStep 2205623 = 3308435) B3308435
theorem B2205659 : Blo 1468554 2205659 := bstep (se 1 (by rfl) ⟨1654244, by rfl⟩ : syracuseStep 2205659 = 3308489) B3308489
theorem B45844487 : Blo 1468554 45844487 := bstep (se 1 (by rfl) ⟨34383365, by rfl⟩ : syracuseStep 45844487 = 68766731) B68766731
theorem B3352583 : Blo 1468554 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B6277135 : Blo 1468554 6277135 := bstep (se 1 (by rfl) ⟨4707851, by rfl⟩ : syracuseStep 6277135 = 9415703) B9415703
theorem B7940177 : Blo 1468554 7940177 := bstep (se 2 (by rfl) ⟨2977566, by rfl⟩ : syracuseStep 7940177 = 5955133) B5955133
theorem B8374387 : Blo 1468554 8374387 := bstep (se 1 (by rfl) ⟨6280790, by rfl⟩ : syracuseStep 8374387 = 12561581) B12561581
theorem B1468591 : Blo 1468554 1468591 := bstep (se 1 (by rfl) ⟨1101443, by rfl⟩ : syracuseStep 1468591 = 2202887) B2202887
theorem B1468615 : Blo 1468554 1468615 := bstep (se 1 (by rfl) ⟨1101461, by rfl⟩ : syracuseStep 1468615 = 2202923) B2202923
theorem B1468635 : Blo 1468554 1468635 := bstep (se 1 (by rfl) ⟨1101476, by rfl⟩ : syracuseStep 1468635 = 2202953) B2202953
theorem B1468711 : Blo 1468554 1468711 := bstep (se 1 (by rfl) ⟨1101533, by rfl⟩ : syracuseStep 1468711 = 2203067) B2203067
theorem B1468751 : Blo 1468554 1468751 := bstep (se 1 (by rfl) ⟨1101563, by rfl⟩ : syracuseStep 1468751 = 2203127) B2203127
theorem B1468767 : Blo 1468554 1468767 := bstep (se 1 (by rfl) ⟨1101575, by rfl⟩ : syracuseStep 1468767 = 2203151) B2203151
theorem B2091359 : Blo 1468554 2091359 := bstep (se 1 (by rfl) ⟨1568519, by rfl⟩ : syracuseStep 2091359 = 3137039) B3137039
theorem B1468795 : Blo 1468554 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B5654909 : Blo 1468554 5654909 := bstep (se 3 (by rfl) ⟨1060295, by rfl⟩ : syracuseStep 5654909 = 2120591) B2120591
theorem B1468847 : Blo 1468554 1468847 := bstep (se 1 (by rfl) ⟨1101635, by rfl⟩ : syracuseStep 1468847 = 2203271) B2203271
theorem B1722799 : Blo 1468554 1722799 := bstep (se 1 (by rfl) ⟨1292099, by rfl⟩ : syracuseStep 1722799 = 2584199) B2584199
theorem B1468871 : Blo 1468554 1468871 := bstep (se 1 (by rfl) ⟨1101653, by rfl⟩ : syracuseStep 1468871 = 2203307) B2203307
theorem B1468891 : Blo 1468554 1468891 := bstep (se 1 (by rfl) ⟨1101668, by rfl⟩ : syracuseStep 1468891 = 2203337) B2203337
theorem B1985033 : Blo 1468554 1985033 := bstep (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) B1488775
theorem B5581345 : Blo 1468554 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B1468967 : Blo 1468554 1468967 := bstep (se 1 (by rfl) ⟨1101725, by rfl⟩ : syracuseStep 1468967 = 2203451) B2203451
theorem B1469007 : Blo 1468554 1469007 := bstep (se 1 (by rfl) ⟨1101755, by rfl⟩ : syracuseStep 1469007 = 2203511) B2203511
theorem B1469023 : Blo 1468554 1469023 := bstep (se 1 (by rfl) ⟨1101767, by rfl⟩ : syracuseStep 1469023 = 2203535) B2203535
theorem B1469051 : Blo 1468554 1469051 := bstep (se 1 (by rfl) ⟨1101788, by rfl⟩ : syracuseStep 1469051 = 2203577) B2203577
theorem B1469103 : Blo 1468554 1469103 := bstep (se 1 (by rfl) ⟨1101827, by rfl⟩ : syracuseStep 1469103 = 2203655) B2203655
theorem B1469127 : Blo 1468554 1469127 := bstep (se 1 (by rfl) ⟨1101845, by rfl⟩ : syracuseStep 1469127 = 2203691) B2203691
theorem B12724937 : Blo 1468554 12724937 := bstep (se 2 (by rfl) ⟨4771851, by rfl⟩ : syracuseStep 12724937 = 9543703) B9543703
theorem B1469147 : Blo 1468554 1469147 := bstep (se 1 (by rfl) ⟨1101860, by rfl⟩ : syracuseStep 1469147 = 2203721) B2203721
theorem B3140345 : Blo 1468554 3140345 := bstep (se 2 (by rfl) ⟨1177629, by rfl⟩ : syracuseStep 3140345 = 2355259) B2355259
theorem B1469223 : Blo 1468554 1469223 := bstep (se 1 (by rfl) ⟨1101917, by rfl⟩ : syracuseStep 1469223 = 2203835) B2203835
theorem B1469263 : Blo 1468554 1469263 := bstep (se 1 (by rfl) ⟨1101947, by rfl⟩ : syracuseStep 1469263 = 2203895) B2203895
theorem B18828125 : Blo 1468554 18828125 := bstep (se 3 (by rfl) ⟨3530273, by rfl⟩ : syracuseStep 18828125 = 7060547) B7060547
theorem B1469279 : Blo 1468554 1469279 := bstep (se 1 (by rfl) ⟨1101959, by rfl⟩ : syracuseStep 1469279 = 2203919) B2203919
theorem B1469307 : Blo 1468554 1469307 := bstep (se 1 (by rfl) ⟨1101980, by rfl⟩ : syracuseStep 1469307 = 2203961) B2203961
theorem B3304367 : Blo 1468554 3304367 := bstep (se 1 (by rfl) ⟨2478275, by rfl⟩ : syracuseStep 3304367 = 4956551) B4956551
theorem B1469359 : Blo 1468554 1469359 := bstep (se 1 (by rfl) ⟨1102019, by rfl⟩ : syracuseStep 1469359 = 2204039) B2204039
theorem B11160503 : Blo 1468554 11160503 := bstep (se 1 (by rfl) ⟨8370377, by rfl⟩ : syracuseStep 11160503 = 16740755) B16740755
theorem B5295035 : Blo 1468554 5295035 := bstep (se 1 (by rfl) ⟨3971276, by rfl⟩ : syracuseStep 5295035 = 7942553) B7942553
theorem B1469383 : Blo 1468554 1469383 := bstep (se 1 (by rfl) ⟨1102037, by rfl⟩ : syracuseStep 1469383 = 2204075) B2204075
theorem B1469403 : Blo 1468554 1469403 := bstep (se 1 (by rfl) ⟨1102052, by rfl⟩ : syracuseStep 1469403 = 2204105) B2204105
theorem B5581831 : Blo 1468554 5581831 := bstep (se 1 (by rfl) ⟨4186373, by rfl⟩ : syracuseStep 5581831 = 8372747) B8372747
theorem B4959251 : Blo 1468554 4959251 := bstep (se 1 (by rfl) ⟨3719438, by rfl⟩ : syracuseStep 4959251 = 7438877) B7438877
theorem B1469479 : Blo 1468554 1469479 := bstep (se 1 (by rfl) ⟨1102109, by rfl⟩ : syracuseStep 1469479 = 2204219) B2204219
theorem B1469519 : Blo 1468554 1469519 := bstep (se 1 (by rfl) ⟨1102139, by rfl⟩ : syracuseStep 1469519 = 2204279) B2204279
theorem B3140687 : Blo 1468554 3140687 := bstep (se 1 (by rfl) ⟨2355515, by rfl⟩ : syracuseStep 3140687 = 4711031) B4711031
theorem B1469535 : Blo 1468554 1469535 := bstep (se 1 (by rfl) ⟨1102151, by rfl⟩ : syracuseStep 1469535 = 2204303) B2204303
theorem B1469563 : Blo 1468554 1469563 := bstep (se 1 (by rfl) ⟨1102172, by rfl⟩ : syracuseStep 1469563 = 2204345) B2204345
theorem B3304619 : Blo 1468554 3304619 := bstep (se 1 (by rfl) ⟨2478464, by rfl⟩ : syracuseStep 3304619 = 4956929) B4956929
theorem B1469615 : Blo 1468554 1469615 := bstep (se 1 (by rfl) ⟨1102211, by rfl⟩ : syracuseStep 1469615 = 2204423) B2204423
theorem B1469639 : Blo 1468554 1469639 := bstep (se 1 (by rfl) ⟨1102229, by rfl⟩ : syracuseStep 1469639 = 2204459) B2204459
theorem B1469659 : Blo 1468554 1469659 := bstep (se 1 (by rfl) ⟨1102244, by rfl⟩ : syracuseStep 1469659 = 2204489) B2204489
theorem B1469735 : Blo 1468554 1469735 := bstep (se 1 (by rfl) ⟨1102301, by rfl⟩ : syracuseStep 1469735 = 2204603) B2204603
theorem B1469775 : Blo 1468554 1469775 := bstep (se 1 (by rfl) ⟨1102331, by rfl⟩ : syracuseStep 1469775 = 2204663) B2204663
theorem B4959575 : Blo 1468554 4959575 := bstep (se 1 (by rfl) ⟨3719681, by rfl⟩ : syracuseStep 4959575 = 7439363) B7439363
theorem B1469791 : Blo 1468554 1469791 := bstep (se 1 (by rfl) ⟨1102343, by rfl⟩ : syracuseStep 1469791 = 2204687) B2204687
theorem B1469819 : Blo 1468554 1469819 := bstep (se 1 (by rfl) ⟨1102364, by rfl⟩ : syracuseStep 1469819 = 2204729) B2204729
theorem B1469871 : Blo 1468554 1469871 := bstep (se 1 (by rfl) ⟨1102403, by rfl⟩ : syracuseStep 1469871 = 2204807) B2204807
theorem B1469895 : Blo 1468554 1469895 := bstep (se 1 (by rfl) ⟨1102421, by rfl⟩ : syracuseStep 1469895 = 2204843) B2204843
theorem B1469915 : Blo 1468554 1469915 := bstep (se 1 (by rfl) ⟨1102436, by rfl⟩ : syracuseStep 1469915 = 2204873) B2204873
theorem B5582317 : Blo 1468554 5582317 := bstep (se 3 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 5582317 = 2093369) B2093369
theorem B7941671 : Blo 1468554 7941671 := bstep (se 1 (by rfl) ⟨5956253, by rfl⟩ : syracuseStep 7941671 = 11912507) B11912507
theorem B1469991 : Blo 1468554 1469991 := bstep (se 1 (by rfl) ⟨1102493, by rfl⟩ : syracuseStep 1469991 = 2204987) B2204987
theorem B1470031 : Blo 1468554 1470031 := bstep (se 1 (by rfl) ⟨1102523, by rfl⟩ : syracuseStep 1470031 = 2205047) B2205047
theorem B1470047 : Blo 1468554 1470047 := bstep (se 1 (by rfl) ⟨1102535, by rfl⟩ : syracuseStep 1470047 = 2205071) B2205071
theorem B2788987 : Blo 1468554 2788987 := bstep (se 1 (by rfl) ⟨2091740, by rfl⟩ : syracuseStep 2788987 = 4183481) B4183481
theorem B1470075 : Blo 1468554 1470075 := bstep (se 1 (by rfl) ⟨1102556, by rfl⟩ : syracuseStep 1470075 = 2205113) B2205113
theorem B6794891 : Blo 1468554 6794891 := bstep (se 1 (by rfl) ⟨5096168, by rfl⟩ : syracuseStep 6794891 = 10192337) B10192337
theorem B1470127 : Blo 1468554 1470127 := bstep (se 1 (by rfl) ⟨1102595, by rfl⟩ : syracuseStep 1470127 = 2205191) B2205191
theorem B3305159 : Blo 1468554 3305159 := bstep (se 1 (by rfl) ⟨2478869, by rfl⟩ : syracuseStep 3305159 = 4957739) B4957739
theorem B2789063 : Blo 1468554 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B1470151 : Blo 1468554 1470151 := bstep (se 1 (by rfl) ⟨1102613, by rfl⟩ : syracuseStep 1470151 = 2205227) B2205227
theorem B1470171 : Blo 1468554 1470171 := bstep (se 1 (by rfl) ⟨1102628, by rfl⟩ : syracuseStep 1470171 = 2205257) B2205257
theorem B5295901 : Blo 1468554 5295901 := bstep (se 3 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 5295901 = 1985963) B1985963
theorem B5582621 : Blo 1468554 5582621 := bstep (se 3 (by rfl) ⟨1046741, by rfl⟩ : syracuseStep 5582621 = 2093483) B2093483
theorem B1470247 : Blo 1468554 1470247 := bstep (se 1 (by rfl) ⟨1102685, by rfl⟩ : syracuseStep 1470247 = 2205371) B2205371
theorem B6704963 : Blo 1468554 6704963 := bstep (se 1 (by rfl) ⟨5028722, by rfl⟩ : syracuseStep 6704963 = 10057445) B10057445
theorem B1470287 : Blo 1468554 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B1470303 : Blo 1468554 1470303 := bstep (se 1 (by rfl) ⟨1102727, by rfl⟩ : syracuseStep 1470303 = 2205455) B2205455
theorem B6360941 : Blo 1468554 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B1470331 : Blo 1468554 1470331 := bstep (se 1 (by rfl) ⟨1102748, by rfl⟩ : syracuseStep 1470331 = 2205497) B2205497
theorem B1470383 : Blo 1468554 1470383 := bstep (se 1 (by rfl) ⟨1102787, by rfl⟩ : syracuseStep 1470383 = 2205575) B2205575
theorem B1470407 : Blo 1468554 1470407 := bstep (se 1 (by rfl) ⟨1102805, by rfl⟩ : syracuseStep 1470407 = 2205611) B2205611
theorem B1470427 : Blo 1468554 1470427 := bstep (se 1 (by rfl) ⟨1102820, by rfl⟩ : syracuseStep 1470427 = 2205641) B2205641
theorem B12087299 : Blo 1468554 12087299 := bstep (se 1 (by rfl) ⟨9065474, by rfl⟩ : syracuseStep 12087299 = 18130949) B18130949
theorem B4182023 : Blo 1468554 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B3182611 : Blo 1468554 3182611 := bstep (se 1 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 3182611 = 4773917) B4773917
theorem B1470503 : Blo 1468554 1470503 := bstep (se 1 (by rfl) ⟨1102877, by rfl⟩ : syracuseStep 1470503 = 2205755) B2205755
theorem B1470543 : Blo 1468554 1470543 := bstep (se 1 (by rfl) ⟨1102907, by rfl⟩ : syracuseStep 1470543 = 2205815) B2205815
theorem B2789473 : Blo 1468554 2789473 := bstep (se 2 (by rfl) ⟨1046052, by rfl⟩ : syracuseStep 2789473 = 2092105) B2092105
theorem B4182263 : Blo 1468554 4182263 := bstep (se 1 (by rfl) ⟨3136697, by rfl⟩ : syracuseStep 4182263 = 6273395) B6273395
theorem B2478431 : Blo 1468554 2478431 := bstep (se 1 (by rfl) ⟨1858823, by rfl⟩ : syracuseStep 2478431 = 3717647) B3717647
theorem B11161961 : Blo 1468554 11161961 := bstep (se 2 (by rfl) ⟨4185735, by rfl⟩ : syracuseStep 11161961 = 8371471) B8371471
theorem B4960655 : Blo 1468554 4960655 := bstep (se 1 (by rfl) ⟨3720491, by rfl⟩ : syracuseStep 4960655 = 7440983) B7440983
theorem B2789815 : Blo 1468554 2789815 := bstep (se 1 (by rfl) ⟨2092361, by rfl⟩ : syracuseStep 2789815 = 4184723) B4184723
theorem B5960225 : Blo 1468554 5960225 := bstep (se 2 (by rfl) ⟨2235084, by rfl⟩ : syracuseStep 5960225 = 4470169) B4470169
theorem B3306023 : Blo 1468554 3306023 := bstep (se 1 (by rfl) ⟨2479517, by rfl⟩ : syracuseStep 3306023 = 4959035) B4959035
theorem B2978515 : Blo 1468554 2978515 := bstep (se 1 (by rfl) ⟨2233886, by rfl⟩ : syracuseStep 2978515 = 4467773) B4467773
theorem B4960979 : Blo 1468554 4960979 := bstep (se 1 (by rfl) ⟨3720734, by rfl⟩ : syracuseStep 4960979 = 7441469) B7441469
theorem B9065171 : Blo 1468554 9065171 := bstep (se 1 (by rfl) ⟨6798878, by rfl⟩ : syracuseStep 9065171 = 13597757) B13597757
theorem B2790217 : Blo 1468554 2790217 := bstep (se 2 (by rfl) ⟨1046331, by rfl⟩ : syracuseStep 2790217 = 2092663) B2092663
theorem B3306347 : Blo 1468554 3306347 := bstep (se 1 (by rfl) ⟨2479760, by rfl⟩ : syracuseStep 3306347 = 4959521) B4959521
theorem B2478991 : Blo 1468554 2478991 := bstep (se 1 (by rfl) ⟨1859243, by rfl⟩ : syracuseStep 2478991 = 3718487) B3718487
theorem B3306401 : Blo 1468554 3306401 := bstep (se 2 (by rfl) ⟨1239900, by rfl⟩ : syracuseStep 3306401 = 2479801) B2479801
theorem B9417701 : Blo 1468554 9417701 := bstep (se 4 (by rfl) ⟨882909, by rfl⟩ : syracuseStep 9417701 = 1765819) B1765819
theorem B3306743 : Blo 1468554 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B10597655 : Blo 1468554 10597655 := bstep (se 1 (by rfl) ⟨7948241, by rfl⟩ : syracuseStep 10597655 = 15896483) B15896483
theorem B3577193 : Blo 1468554 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B4240745 : Blo 1468554 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B1652143 : Blo 1468554 1652143 := bstep (se 1 (by rfl) ⟨1239107, by rfl⟩ : syracuseStep 1652143 = 2478215) B2478215
theorem B35755505 : Blo 1468554 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B2790931 : Blo 1468554 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B2479673 : Blo 1468554 2479673 := bstep (se 2 (by rfl) ⟨929877, by rfl⟩ : syracuseStep 2479673 = 1859755) B1859755
theorem B3970889 : Blo 1468554 3970889 := bstep (se 2 (by rfl) ⟨1489083, by rfl⟩ : syracuseStep 3970889 = 2978167) B2978167
theorem B3307337 : Blo 1468554 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B1652575 : Blo 1468554 1652575 := bstep (se 1 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 1652575 = 2478863) B2478863
theorem B10590047 : Blo 1468554 10590047 := bstep (se 1 (by rfl) ⟨7942535, by rfl⟩ : syracuseStep 10590047 = 15885071) B15885071
theorem B2791273 : Blo 1468554 2791273 := bstep (se 2 (by rfl) ⟨1046727, by rfl⟩ : syracuseStep 2791273 = 2093455) B2093455
theorem B4962167 : Blo 1468554 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B7444385 : Blo 1468554 7444385 := bstep (se 2 (by rfl) ⟨2791644, by rfl⟩ : syracuseStep 7444385 = 5583289) B5583289
theorem B2979919 : Blo 1468554 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B4962383 : Blo 1468554 4962383 := bstep (se 1 (by rfl) ⟨3721787, by rfl⟩ : syracuseStep 4962383 = 7443575) B7443575
theorem B1652935 : Blo 1468554 1652935 := bstep (se 1 (by rfl) ⟨1239701, by rfl⟩ : syracuseStep 1652935 = 2479403) B2479403
theorem B2480375 : Blo 1468554 2480375 := bstep (se 1 (by rfl) ⟨1860281, by rfl⟩ : syracuseStep 2480375 = 3720563) B3720563
theorem B11163905 : Blo 1468554 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B5576971 : Blo 1468554 5576971 := bstep (se 1 (by rfl) ⟨4182728, by rfl⟩ : syracuseStep 5576971 = 8365457) B8365457
theorem B42342749 : Blo 1468554 42342749 := bstep (se 3 (by rfl) ⟨7939265, by rfl⟩ : syracuseStep 42342749 = 15878531) B15878531
theorem B4962761 : Blo 1468554 4962761 := bstep (se 2 (by rfl) ⟨1861035, by rfl⟩ : syracuseStep 4962761 = 3722071) B3722071
theorem B5577275 : Blo 1468554 5577275 := bstep (se 1 (by rfl) ⟨4182956, by rfl⟩ : syracuseStep 5577275 = 8365913) B8365913
theorem B2480719 : Blo 1468554 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B3308129 : Blo 1468554 3308129 := bstep (se 2 (by rfl) ⟨1240548, by rfl⟩ : syracuseStep 3308129 = 2481097) B2481097
theorem B4963031 : Blo 1468554 4963031 := bstep (se 1 (by rfl) ⟨3722273, by rfl⟩ : syracuseStep 4963031 = 7444547) B7444547
theorem B4184905 : Blo 1468554 4184905 := bstep (se 2 (by rfl) ⟨1569339, by rfl⟩ : syracuseStep 4184905 = 3138679) B3138679
theorem B2480969 : Blo 1468554 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B1073724245 : Blo 1468554 1073724245 := bstep (se 9 (by rfl) ⟨3145676, by rfl⟩ : syracuseStep 1073724245 = 6291353) B6291353
theorem B4528991 : Blo 1468554 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B4184939 : Blo 1468554 4184939 := bstep (se 1 (by rfl) ⟨3138704, by rfl⟩ : syracuseStep 4184939 = 6277409) B6277409
theorem B3308471 : Blo 1468554 3308471 := bstep (se 1 (by rfl) ⟨2481353, by rfl⟩ : syracuseStep 3308471 = 4962707) B4962707
theorem B13589477 : Blo 1468554 13589477 := bstep (se 4 (by rfl) ⟨1274013, by rfl⟩ : syracuseStep 13589477 = 2548027) B2548027
theorem B3718163 : Blo 1468554 3718163 := bstep (se 1 (by rfl) ⟨2788622, by rfl⟩ : syracuseStep 3718163 = 5577245) B5577245
theorem B1653799 : Blo 1468554 1653799 := bstep (se 1 (by rfl) ⟨1240349, by rfl⟩ : syracuseStep 1653799 = 2480699) B2480699
theorem B3349561 : Blo 1468554 3349561 := bstep (se 2 (by rfl) ⟨1256085, by rfl⟩ : syracuseStep 3349561 = 2512171) B2512171
theorem B2513999 : Blo 1468554 2513999 := bstep (se 1 (by rfl) ⟨1885499, by rfl⟩ : syracuseStep 2513999 = 3770999) B3770999
theorem B1115667587 : Blo 1468554 1115667587 := bstep (se 1 (by rfl) ⟨836750690, by rfl⟩ : syracuseStep 1115667587 = 1673501381) B1673501381
theorem B16743671 : Blo 1468554 16743671 := bstep (se 1 (by rfl) ⟨12557753, by rfl⟩ : syracuseStep 16743671 = 25115507) B25115507
theorem B2481401 : Blo 1468554 2481401 := bstep (se 2 (by rfl) ⟨930525, by rfl⟩ : syracuseStep 2481401 = 1861051) B1861051
theorem B2203055 : Blo 1468554 2203055 := bstep (se 1 (by rfl) ⟨1652291, by rfl⟩ : syracuseStep 2203055 = 3304583) B3304583
theorem B3718619 : Blo 1468554 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B2203145 : Blo 1468554 2203145 := bstep (se 2 (by rfl) ⟨826179, by rfl⟩ : syracuseStep 2203145 = 1652359) B1652359
theorem B2203175 : Blo 1468554 2203175 := bstep (se 1 (by rfl) ⟨1652381, by rfl⟩ : syracuseStep 2203175 = 3304763) B3304763
theorem B4709927 : Blo 1468554 4709927 := bstep (se 1 (by rfl) ⟨3532445, by rfl⟩ : syracuseStep 4709927 = 7064891) B7064891
theorem B5299751 : Blo 1468554 5299751 := bstep (se 1 (by rfl) ⟨3974813, by rfl⟩ : syracuseStep 5299751 = 7949627) B7949627
theorem B2203259 : Blo 1468554 2203259 := bstep (se 1 (by rfl) ⟨1652444, by rfl⟩ : syracuseStep 2203259 = 3304889) B3304889
theorem B5578429 : Blo 1468554 5578429 := bstep (se 3 (by rfl) ⟨1045955, by rfl⟩ : syracuseStep 5578429 = 2091911) B2091911
theorem B2203385 : Blo 1468554 2203385 := bstep (se 2 (by rfl) ⟨826269, by rfl⟩ : syracuseStep 2203385 = 1652539) B1652539
theorem B2203487 : Blo 1468554 2203487 := bstep (se 1 (by rfl) ⟨1652615, by rfl⟩ : syracuseStep 2203487 = 3305231) B3305231
theorem B2203499 : Blo 1468554 2203499 := bstep (se 1 (by rfl) ⟨1652624, by rfl⟩ : syracuseStep 2203499 = 3305249) B3305249
theorem B4243481 : Blo 1468554 4243481 := bstep (se 2 (by rfl) ⟨1591305, by rfl⟩ : syracuseStep 4243481 = 3182611) B3182611
theorem B3973225 : Blo 1468554 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B3719297 : Blo 1468554 3719297 := bstep (se 2 (by rfl) ⟨1394736, by rfl⟩ : syracuseStep 3719297 = 2789473) B2789473
theorem B11165849 : Blo 1468554 11165849 := bstep (se 2 (by rfl) ⟨4187193, by rfl⟩ : syracuseStep 11165849 = 8374387) B8374387
theorem B2203913 : Blo 1468554 2203913 := bstep (se 2 (by rfl) ⟨826467, by rfl⟩ : syracuseStep 2203913 = 1652935) B1652935
theorem B2975113565 : Blo 1468554 2975113565 := bstep (se 3 (by rfl) ⟨557833793, by rfl⟩ : syracuseStep 2975113565 = 1115667587) B1115667587
theorem B3973483 : Blo 1468554 3973483 := bstep (se 1 (by rfl) ⟨2980112, by rfl⟩ : syracuseStep 3973483 = 5960225) B5960225
theorem B2204015 : Blo 1468554 2204015 := bstep (se 1 (by rfl) ⟨1653011, by rfl⟩ : syracuseStep 2204015 = 3306023) B3306023
theorem B3719591 : Blo 1468554 3719591 := bstep (se 1 (by rfl) ⟨2789693, by rfl⟩ : syracuseStep 3719591 = 5579387) B5579387
theorem B2204231 : Blo 1468554 2204231 := bstep (se 1 (by rfl) ⟨1653173, by rfl⟩ : syracuseStep 2204231 = 3306347) B3306347
theorem B3719753 : Blo 1468554 3719753 := bstep (se 2 (by rfl) ⟨1394907, by rfl⟩ : syracuseStep 3719753 = 2789815) B2789815
theorem B2204267 : Blo 1468554 2204267 := bstep (se 1 (by rfl) ⟨1653200, by rfl⟩ : syracuseStep 2204267 = 3306401) B3306401
theorem B2204495 : Blo 1468554 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B12551057 : Blo 1468554 12551057 := bstep (se 2 (by rfl) ⟨4706646, by rfl⟩ : syracuseStep 12551057 = 9413293) B9413293
theorem B2384795 : Blo 1468554 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B2827163 : Blo 1468554 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B3720107 : Blo 1468554 3720107 := bstep (se 1 (by rfl) ⟨2790080, by rfl⟩ : syracuseStep 3720107 = 5580161) B5580161
theorem B5293019 : Blo 1468554 5293019 := bstep (se 1 (by rfl) ⟨3969764, by rfl⟩ : syracuseStep 5293019 = 7939529) B7939529
theorem B7062491 : Blo 1468554 7062491 := bstep (se 1 (by rfl) ⟨5296868, by rfl⟩ : syracuseStep 7062491 = 10593737) B10593737
theorem B16729091 : Blo 1468554 16729091 := bstep (se 1 (by rfl) ⟨12546818, by rfl⟩ : syracuseStep 16729091 = 25093637) B25093637
theorem B5579873 : Blo 1468554 5579873 := bstep (se 2 (by rfl) ⟨2092452, by rfl⟩ : syracuseStep 5579873 = 4184905) B4184905
theorem B3720289 : Blo 1468554 3720289 := bstep (se 2 (by rfl) ⟨1395108, by rfl⟩ : syracuseStep 3720289 = 2790217) B2790217
theorem B2647259 : Blo 1468554 2647259 := bstep (se 1 (by rfl) ⟨1985444, by rfl⟩ : syracuseStep 2647259 = 3970889) B3970889
theorem B2204891 : Blo 1468554 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B5293421 : Blo 1468554 5293421 := bstep (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) B1985033
theorem B2205065 : Blo 1468554 2205065 := bstep (se 2 (by rfl) ⟨826899, by rfl⟩ : syracuseStep 2205065 = 1653799) B1653799
theorem B5293451 : Blo 1468554 5293451 := bstep (se 1 (by rfl) ⟨3970088, by rfl⟩ : syracuseStep 5293451 = 7940177) B7940177
theorem B4466081 : Blo 1468554 4466081 := bstep (se 2 (by rfl) ⟨1674780, by rfl⟩ : syracuseStep 4466081 = 3349561) B3349561
theorem B12559805 : Blo 1468554 12559805 := bstep (se 3 (by rfl) ⟨2354963, by rfl⟩ : syracuseStep 12559805 = 4709927) B4709927
theorem B3769939 : Blo 1468554 3769939 := bstep (se 1 (by rfl) ⟨2827454, by rfl⟩ : syracuseStep 3769939 = 5654909) B5654909
theorem B2205419 : Blo 1468554 2205419 := bstep (se 1 (by rfl) ⟨1654064, by rfl⟩ : syracuseStep 2205419 = 3308129) B3308129
theorem B12552083 : Blo 1468554 12552083 := bstep (se 1 (by rfl) ⟨9414062, by rfl⟩ : syracuseStep 12552083 = 18828125) B18828125
theorem B7440335 : Blo 1468554 7440335 := bstep (se 1 (by rfl) ⟨5580251, by rfl⟩ : syracuseStep 7440335 = 11160503) B11160503
theorem B2205647 : Blo 1468554 2205647 := bstep (se 1 (by rfl) ⟨1654235, by rfl⟩ : syracuseStep 2205647 = 3308471) B3308471
theorem B3721241 : Blo 1468554 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B12077309 : Blo 1468554 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B1468703 : Blo 1468554 1468703 := bstep (se 1 (by rfl) ⟨1101527, by rfl⟩ : syracuseStep 1468703 = 2203055) B2203055
theorem B1468763 : Blo 1468554 1468763 := bstep (se 1 (by rfl) ⟨1101572, by rfl⟩ : syracuseStep 1468763 = 2203145) B2203145
theorem B1468783 : Blo 1468554 1468783 := bstep (se 1 (by rfl) ⟨1101587, by rfl⟩ : syracuseStep 1468783 = 2203175) B2203175
theorem B5294447 : Blo 1468554 5294447 := bstep (se 1 (by rfl) ⟨3970835, by rfl⟩ : syracuseStep 5294447 = 7941671) B7941671
theorem B3533167 : Blo 1468554 3533167 := bstep (se 1 (by rfl) ⟨2649875, by rfl⟩ : syracuseStep 3533167 = 5299751) B5299751
theorem B1468839 : Blo 1468554 1468839 := bstep (se 1 (by rfl) ⟨1101629, by rfl⟩ : syracuseStep 1468839 = 2203259) B2203259
theorem B3181025 : Blo 1468554 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B3721697 : Blo 1468554 3721697 := bstep (se 2 (by rfl) ⟨1395636, by rfl⟩ : syracuseStep 3721697 = 2791273) B2791273
theorem B1468923 : Blo 1468554 1468923 := bstep (se 1 (by rfl) ⟨1101692, by rfl⟩ : syracuseStep 1468923 = 2203385) B2203385
theorem B3721747 : Blo 1468554 3721747 := bstep (se 1 (by rfl) ⟨2791310, by rfl⟩ : syracuseStep 3721747 = 5582621) B5582621
theorem B1468991 : Blo 1468554 1468991 := bstep (se 1 (by rfl) ⟨1101743, by rfl⟩ : syracuseStep 1468991 = 2203487) B2203487
theorem B1468999 : Blo 1468554 1468999 := bstep (se 1 (by rfl) ⟨1101749, by rfl⟩ : syracuseStep 1468999 = 2203499) B2203499
theorem B2788015 : Blo 1468554 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B1469151 : Blo 1468554 1469151 := bstep (se 1 (by rfl) ⟨1101863, by rfl⟩ : syracuseStep 1469151 = 2203727) B2203727
theorem B1469231 : Blo 1468554 1469231 := bstep (se 1 (by rfl) ⟨1101923, by rfl⟩ : syracuseStep 1469231 = 2203847) B2203847
theorem B8366915 : Blo 1468554 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B2788175 : Blo 1468554 2788175 := bstep (se 1 (by rfl) ⟨2091131, by rfl⟩ : syracuseStep 2788175 = 4182263) B4182263
theorem B1469339 : Blo 1468554 1469339 := bstep (se 1 (by rfl) ⟨1102004, by rfl⟩ : syracuseStep 1469339 = 2204009) B2204009
theorem B7441307 : Blo 1468554 7441307 := bstep (se 1 (by rfl) ⟨5580980, by rfl⟩ : syracuseStep 7441307 = 11161961) B11161961
theorem B1469391 : Blo 1468554 1469391 := bstep (se 1 (by rfl) ⟨1102043, by rfl⟩ : syracuseStep 1469391 = 2204087) B2204087
theorem B1469415 : Blo 1468554 1469415 := bstep (se 1 (by rfl) ⟨1102061, by rfl⟩ : syracuseStep 1469415 = 2204123) B2204123
theorem B3304439 : Blo 1468554 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B15281167 : Blo 1468554 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B9677905 : Blo 1468554 9677905 := bstep (se 2 (by rfl) ⟨3629214, by rfl⟩ : syracuseStep 9677905 = 7258429) B7258429
theorem B1469727 : Blo 1468554 1469727 := bstep (se 1 (by rfl) ⟨1102295, by rfl⟩ : syracuseStep 1469727 = 2204591) B2204591
theorem B6278467 : Blo 1468554 6278467 := bstep (se 1 (by rfl) ⟨4708850, by rfl⟩ : syracuseStep 6278467 = 9417701) B9417701
theorem B1469787 : Blo 1468554 1469787 := bstep (se 1 (by rfl) ⟨1102340, by rfl⟩ : syracuseStep 1469787 = 2204681) B2204681
theorem B3304799 : Blo 1468554 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B1469807 : Blo 1468554 1469807 := bstep (se 1 (by rfl) ⟨1102355, by rfl⟩ : syracuseStep 1469807 = 2204711) B2204711
theorem B7441793 : Blo 1468554 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B1469863 : Blo 1468554 1469863 := bstep (se 1 (by rfl) ⟨1102397, by rfl⟩ : syracuseStep 1469863 = 2204795) B2204795
theorem B4959737 : Blo 1468554 4959737 := bstep (se 2 (by rfl) ⟨1859901, by rfl⟩ : syracuseStep 4959737 = 3719803) B3719803
theorem B1469947 : Blo 1468554 1469947 := bstep (se 1 (by rfl) ⟨1102460, by rfl⟩ : syracuseStep 1469947 = 2204921) B2204921
theorem B1470015 : Blo 1468554 1470015 := bstep (se 1 (by rfl) ⟨1102511, by rfl⟩ : syracuseStep 1470015 = 2205023) B2205023
theorem B1568327 : Blo 1468554 1568327 := bstep (se 1 (by rfl) ⟨1176245, by rfl⟩ : syracuseStep 1568327 = 2352491) B2352491
theorem B1470023 : Blo 1468554 1470023 := bstep (se 1 (by rfl) ⟨1102517, by rfl⟩ : syracuseStep 1470023 = 2205035) B2205035
theorem B1470175 : Blo 1468554 1470175 := bstep (se 1 (by rfl) ⟨1102631, by rfl⟩ : syracuseStep 1470175 = 2205263) B2205263
theorem B3305195 : Blo 1468554 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B1765099 : Blo 1468554 1765099 := bstep (se 1 (by rfl) ⟨1323824, by rfl⟩ : syracuseStep 1765099 = 2647649) B2647649
theorem B4960007 : Blo 1468554 4960007 := bstep (se 1 (by rfl) ⟨3720005, by rfl⟩ : syracuseStep 4960007 = 7440011) B7440011
theorem B2354951 : Blo 1468554 2354951 := bstep (se 1 (by rfl) ⟨1766213, by rfl⟩ : syracuseStep 2354951 = 3532427) B3532427
theorem B1470255 : Blo 1468554 1470255 := bstep (se 1 (by rfl) ⟨1102691, by rfl⟩ : syracuseStep 1470255 = 2205383) B2205383
theorem B4960061 : Blo 1468554 4960061 := bstep (se 3 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 4960061 = 1860023) B1860023
theorem B3305321 : Blo 1468554 3305321 := bstep (se 2 (by rfl) ⟨1239495, by rfl⟩ : syracuseStep 3305321 = 2478991) B2478991
theorem B1470363 : Blo 1468554 1470363 := bstep (se 1 (by rfl) ⟨1102772, by rfl⟩ : syracuseStep 1470363 = 2205545) B2205545
theorem B1470415 : Blo 1468554 1470415 := bstep (se 1 (by rfl) ⟨1102811, by rfl⟩ : syracuseStep 1470415 = 2205623) B2205623
theorem B1470439 : Blo 1468554 1470439 := bstep (se 1 (by rfl) ⟨1102829, by rfl⟩ : syracuseStep 1470439 = 2205659) B2205659
theorem B7442441 : Blo 1468554 7442441 := bstep (se 2 (by rfl) ⟨2790915, by rfl⟩ : syracuseStep 7442441 = 5581831) B5581831
theorem B7442603 : Blo 1468554 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B8483291 : Blo 1468554 8483291 := bstep (se 1 (by rfl) ⟨6362468, by rfl⟩ : syracuseStep 8483291 = 12724937) B12724937
theorem B2093563 : Blo 1468554 2093563 := bstep (se 1 (by rfl) ⟨1570172, by rfl⟩ : syracuseStep 2093563 = 3140345) B3140345
theorem B2789959 : Blo 1468554 2789959 := bstep (se 1 (by rfl) ⟨2092469, by rfl⟩ : syracuseStep 2789959 = 4184939) B4184939
theorem B7443089 : Blo 1468554 7443089 := bstep (se 2 (by rfl) ⟨2791158, by rfl⟩ : syracuseStep 7443089 = 5582317) B5582317
theorem B2478775 : Blo 1468554 2478775 := bstep (se 1 (by rfl) ⟨1859081, by rfl⟩ : syracuseStep 2478775 = 3718163) B3718163
theorem B3306167 : Blo 1468554 3306167 := bstep (se 1 (by rfl) ⟨2479625, by rfl⟩ : syracuseStep 3306167 = 4959251) B4959251
theorem B1675999 : Blo 1468554 1675999 := bstep (se 1 (by rfl) ⟨1256999, by rfl⟩ : syracuseStep 1675999 = 2513999) B2513999
theorem B2093791 : Blo 1468554 2093791 := bstep (se 1 (by rfl) ⟨1570343, by rfl⟩ : syracuseStep 2093791 = 3140687) B3140687
theorem B33952541 : Blo 1468554 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B11162447 : Blo 1468554 11162447 := bstep (se 1 (by rfl) ⟨8371835, by rfl⟩ : syracuseStep 11162447 = 16743671) B16743671
theorem B3306383 : Blo 1468554 3306383 := bstep (se 1 (by rfl) ⟨2479787, by rfl⟩ : syracuseStep 3306383 = 4959575) B4959575
theorem B9188261 : Blo 1468554 9188261 := bstep (se 4 (by rfl) ⟨861399, by rfl⟩ : syracuseStep 9188261 = 1722799) B1722799
theorem B16962509 : Blo 1468554 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B2479079 : Blo 1468554 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B4469975 : Blo 1468554 4469975 := bstep (se 1 (by rfl) ⟨3352481, by rfl⟩ : syracuseStep 4469975 = 6704963) B6704963
theorem B8058199 : Blo 1468554 8058199 := bstep (se 1 (by rfl) ⟨6043649, by rfl⟩ : syracuseStep 8058199 = 12087299) B12087299
theorem B8369513 : Blo 1468554 8369513 := bstep (se 2 (by rfl) ⟨3138567, by rfl⟩ : syracuseStep 8369513 = 6277135) B6277135
theorem B53630333 : Blo 1468554 53630333 := bstep (se 3 (by rfl) ⟨10055687, by rfl⟩ : syracuseStep 53630333 = 20111375) B20111375
theorem B1652287 : Blo 1468554 1652287 := bstep (se 1 (by rfl) ⟨1239215, by rfl⟩ : syracuseStep 1652287 = 2478431) B2478431
theorem B3307103 : Blo 1468554 3307103 := bstep (se 1 (by rfl) ⟨2480327, by rfl⟩ : syracuseStep 3307103 = 4960655) B4960655
theorem B2791007 : Blo 1468554 2791007 := bstep (se 1 (by rfl) ⟨2093255, by rfl⟩ : syracuseStep 2791007 = 4186511) B4186511
theorem B7435961 : Blo 1468554 7435961 := bstep (se 2 (by rfl) ⟨2788485, by rfl⟩ : syracuseStep 7435961 = 5576971) B5576971
theorem B3307319 : Blo 1468554 3307319 := bstep (se 1 (by rfl) ⟨2480489, by rfl⟩ : syracuseStep 3307319 = 4960979) B4960979
theorem B6043447 : Blo 1468554 6043447 := bstep (se 1 (by rfl) ⟨4532585, by rfl⟩ : syracuseStep 6043447 = 9065171) B9065171
theorem B4183913 : Blo 1468554 4183913 := bstep (se 2 (by rfl) ⟨1568967, by rfl⟩ : syracuseStep 4183913 = 3137935) B3137935
theorem B5298209 : Blo 1468554 5298209 := bstep (se 2 (by rfl) ⟨1986828, by rfl⟩ : syracuseStep 5298209 = 3973657) B3973657
theorem B28260413 : Blo 1468554 28260413 := bstep (se 3 (by rfl) ⟨5298827, by rfl⟩ : syracuseStep 28260413 = 10597655) B10597655
theorem B2480233 : Blo 1468554 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B3307625 : Blo 1468554 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B5576957 : Blo 1468554 5576957 := bstep (se 3 (by rfl) ⟨1045679, by rfl⟩ : syracuseStep 5576957 = 2091359) B2091359
theorem B2119945 : Blo 1468554 2119945 := bstep (se 2 (by rfl) ⟨794979, by rfl⟩ : syracuseStep 2119945 = 1589959) B1589959
theorem B3971353 : Blo 1468554 3971353 := bstep (se 2 (by rfl) ⟨1489257, by rfl⟩ : syracuseStep 3971353 = 2978515) B2978515
theorem B23837003 : Blo 1468554 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B1653115 : Blo 1468554 1653115 := bstep (se 1 (by rfl) ⟨1239836, by rfl⟩ : syracuseStep 1653115 = 2479673) B2479673
theorem B7060031 : Blo 1468554 7060031 := bstep (se 1 (by rfl) ⟨5295023, by rfl⟩ : syracuseStep 7060031 = 10590047) B10590047
theorem B3529295 : Blo 1468554 3529295 := bstep (se 1 (by rfl) ⟨2646971, by rfl⟩ : syracuseStep 3529295 = 5293943) B5293943
theorem B3308111 : Blo 1468554 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B4962923 : Blo 1468554 4962923 := bstep (se 1 (by rfl) ⟨3722192, by rfl⟩ : syracuseStep 4962923 = 7444385) B7444385
theorem B30562991 : Blo 1468554 30562991 := bstep (se 1 (by rfl) ⟨22922243, by rfl⟩ : syracuseStep 30562991 = 45844487) B45844487
theorem B2235055 : Blo 1468554 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B3308255 : Blo 1468554 3308255 := bstep (se 1 (by rfl) ⟨2481191, by rfl⟩ : syracuseStep 3308255 = 4962383) B4962383
theorem B1653583 : Blo 1468554 1653583 := bstep (se 1 (by rfl) ⟨1240187, by rfl⟩ : syracuseStep 1653583 = 2480375) B2480375
theorem B28228499 : Blo 1468554 28228499 := bstep (se 1 (by rfl) ⟨21171374, by rfl⟩ : syracuseStep 28228499 = 42342749) B42342749
theorem B3308507 : Blo 1468554 3308507 := bstep (se 1 (by rfl) ⟨2481380, by rfl⟩ : syracuseStep 3308507 = 4962761) B4962761
theorem B3718183 : Blo 1468554 3718183 := bstep (se 1 (by rfl) ⟨2788637, by rfl⟩ : syracuseStep 3718183 = 5577275) B5577275
theorem B3308687 : Blo 1468554 3308687 := bstep (se 1 (by rfl) ⟨2481515, by rfl⟩ : syracuseStep 3308687 = 4963031) B4963031
theorem B1653979 : Blo 1468554 1653979 := bstep (se 1 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 1653979 = 2480969) B2480969
theorem B715816163 : Blo 1468554 715816163 := bstep (se 1 (by rfl) ⟨536862122, by rfl⟩ : syracuseStep 715816163 = 1073724245) B1073724245
theorem B2202857 : Blo 1468554 2202857 := bstep (se 2 (by rfl) ⟨826071, by rfl⟩ : syracuseStep 2202857 = 1652143) B1652143
theorem B77430005 : Blo 1468554 77430005 := bstep (se 5 (by rfl) ⟨3629531, by rfl⟩ : syracuseStep 77430005 = 7259063) B7259063
theorem B2202911 : Blo 1468554 2202911 := bstep (se 1 (by rfl) ⟨1652183, by rfl⟩ : syracuseStep 2202911 = 3304367) B3304367
theorem B3530023 : Blo 1468554 3530023 := bstep (se 1 (by rfl) ⟨2647517, by rfl⟩ : syracuseStep 3530023 = 5295035) B5295035
theorem B9059651 : Blo 1468554 9059651 := bstep (se 1 (by rfl) ⟨6794738, by rfl⟩ : syracuseStep 9059651 = 13589477) B13589477
theorem B2203079 : Blo 1468554 2203079 := bstep (se 1 (by rfl) ⟨1652309, by rfl⟩ : syracuseStep 2203079 = 3304619) B3304619
theorem B15883721 : Blo 1468554 15883721 := bstep (se 2 (by rfl) ⟨5956395, by rfl⟩ : syracuseStep 15883721 = 11912791) B11912791
theorem B3718649 : Blo 1468554 3718649 := bstep (se 2 (by rfl) ⟨1394493, by rfl⟩ : syracuseStep 3718649 = 2788987) B2788987
theorem B1654267 : Blo 1468554 1654267 := bstep (se 1 (by rfl) ⟨1240700, by rfl⟩ : syracuseStep 1654267 = 2481401) B2481401
theorem B7437905 : Blo 1468554 7437905 := bstep (se 2 (by rfl) ⟨2789214, by rfl⟩ : syracuseStep 7437905 = 5578429) B5578429
theorem B7061201 : Blo 1468554 7061201 := bstep (se 2 (by rfl) ⟨2647950, by rfl⟩ : syracuseStep 7061201 = 5295901) B5295901
theorem B4529927 : Blo 1468554 4529927 := bstep (se 1 (by rfl) ⟨3397445, by rfl⟩ : syracuseStep 4529927 = 6794891) B6794891
theorem B2203433 : Blo 1468554 2203433 := bstep (se 2 (by rfl) ⟨826287, by rfl⟩ : syracuseStep 2203433 = 1652575) B1652575
theorem B2203439 : Blo 1468554 2203439 := bstep (se 1 (by rfl) ⟨1652579, by rfl⟩ : syracuseStep 2203439 = 3305159) B3305159
theorem B1859375 : Blo 1468554 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B2826593 : Blo 1468554 2826593 := bstep (se 2 (by rfl) ⟨1059972, by rfl⟩ : syracuseStep 2826593 = 2119945) B2119945
theorem B2204111 : Blo 1468554 2204111 := bstep (se 1 (by rfl) ⟨1653083, by rfl⟩ : syracuseStep 2204111 = 3306167) B3306167
theorem B4710889 : Blo 1468554 4710889 := bstep (se 2 (by rfl) ⟨1766583, by rfl⟩ : syracuseStep 4710889 = 3533167) B3533167
theorem B2204153 : Blo 1468554 2204153 := bstep (se 2 (by rfl) ⟨826557, by rfl⟩ : syracuseStep 2204153 = 1653115) B1653115
theorem B2204255 : Blo 1468554 2204255 := bstep (se 1 (by rfl) ⟨1653191, by rfl⟩ : syracuseStep 2204255 = 3306383) B3306383
theorem B3719915 : Blo 1468554 3719915 := bstep (se 1 (by rfl) ⟨2789936, by rfl⟩ : syracuseStep 3719915 = 5579873) B5579873
theorem B3719945 : Blo 1468554 3719945 := bstep (se 2 (by rfl) ⟨1394979, by rfl⟩ : syracuseStep 3719945 = 2789959) B2789959
theorem B5579675 : Blo 1468554 5579675 := bstep (se 1 (by rfl) ⟨4184756, by rfl⟩ : syracuseStep 5579675 = 8369513) B8369513
theorem B8373203 : Blo 1468554 8373203 := bstep (se 1 (by rfl) ⟨6279902, by rfl⟩ : syracuseStep 8373203 = 12559805) B12559805
theorem B14115869 : Blo 1468554 14115869 := bstep (se 3 (by rfl) ⟨2646725, by rfl⟩ : syracuseStep 14115869 = 5293451) B5293451
theorem B2204735 : Blo 1468554 2204735 := bstep (se 1 (by rfl) ⟨1653551, by rfl⟩ : syracuseStep 2204735 = 3307103) B3307103
theorem B1860671 : Blo 1468554 1860671 := bstep (se 1 (by rfl) ⟨1395503, by rfl⟩ : syracuseStep 1860671 = 2791007) B2791007
theorem B2204777 : Blo 1468554 2204777 := bstep (se 2 (by rfl) ⟨826791, by rfl⟩ : syracuseStep 2204777 = 1653583) B1653583
theorem B4957307 : Blo 1468554 4957307 := bstep (se 1 (by rfl) ⟨3717980, by rfl⟩ : syracuseStep 4957307 = 7435961) B7435961
theorem B2204879 : Blo 1468554 2204879 := bstep (se 1 (by rfl) ⟨1653659, by rfl⟩ : syracuseStep 2204879 = 3307319) B3307319
theorem B3532139 : Blo 1468554 3532139 := bstep (se 1 (by rfl) ⟨2649104, by rfl⟩ : syracuseStep 3532139 = 5298209) B5298209
theorem B4957577 : Blo 1468554 4957577 := bstep (se 2 (by rfl) ⟨1859091, by rfl⟩ : syracuseStep 4957577 = 3718183) B3718183
theorem B2205083 : Blo 1468554 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B18826789 : Blo 1468554 18826789 := bstep (se 4 (by rfl) ⟨1765011, by rfl⟩ : syracuseStep 18826789 = 3530023) B3530023
theorem B2205305 : Blo 1468554 2205305 := bstep (se 2 (by rfl) ⟨826989, by rfl⟩ : syracuseStep 2205305 = 1653979) B1653979
theorem B2352863 : Blo 1468554 2352863 := bstep (se 1 (by rfl) ⟨1764647, by rfl⟩ : syracuseStep 2352863 = 3529295) B3529295
theorem B2205407 : Blo 1468554 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B20375327 : Blo 1468554 20375327 := bstep (se 1 (by rfl) ⟨15281495, by rfl⟩ : syracuseStep 20375327 = 30562991) B30562991
theorem B2205503 : Blo 1468554 2205503 := bstep (se 1 (by rfl) ⟨1654127, by rfl⟩ : syracuseStep 2205503 = 3308255) B3308255
theorem B18818999 : Blo 1468554 18818999 := bstep (se 1 (by rfl) ⟨14114249, by rfl⟩ : syracuseStep 18818999 = 28228499) B28228499
theorem B2205671 : Blo 1468554 2205671 := bstep (se 1 (by rfl) ⟨1654253, by rfl⟩ : syracuseStep 2205671 = 3308507) B3308507
theorem B2205689 : Blo 1468554 2205689 := bstep (se 2 (by rfl) ⟨827133, by rfl⟩ : syracuseStep 2205689 = 1654267) B1654267
theorem B90540109 : Blo 1468554 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B2205791 : Blo 1468554 2205791 := bstep (se 1 (by rfl) ⟨1654343, by rfl⟩ : syracuseStep 2205791 = 3308687) B3308687
theorem B4958333 : Blo 1468554 4958333 := bstep (se 3 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 4958333 = 1859375) B1859375
theorem B477210775 : Blo 1468554 477210775 := bstep (se 1 (by rfl) ⟨357908081, by rfl⟩ : syracuseStep 477210775 = 715816163) B715816163
theorem B1468571 : Blo 1468554 1468571 := bstep (se 1 (by rfl) ⟨1101428, by rfl⟩ : syracuseStep 1468571 = 2202857) B2202857
theorem B51620003 : Blo 1468554 51620003 := bstep (se 1 (by rfl) ⟨38715002, by rfl⟩ : syracuseStep 51620003 = 77430005) B77430005
theorem B1468607 : Blo 1468554 1468607 := bstep (se 1 (by rfl) ⟨1101455, by rfl⟩ : syracuseStep 1468607 = 2202911) B2202911
theorem B6039767 : Blo 1468554 6039767 := bstep (se 1 (by rfl) ⟨4529825, by rfl⟩ : syracuseStep 6039767 = 9059651) B9059651
theorem B1468719 : Blo 1468554 1468719 := bstep (se 1 (by rfl) ⟨1101539, by rfl⟩ : syracuseStep 1468719 = 2203079) B2203079
theorem B2353465 : Blo 1468554 2353465 := bstep (se 2 (by rfl) ⟨882549, by rfl⟩ : syracuseStep 2353465 = 1765099) B1765099
theorem B4958603 : Blo 1468554 4958603 := bstep (se 1 (by rfl) ⟨3718952, by rfl⟩ : syracuseStep 4958603 = 7437905) B7437905
theorem B6359453 : Blo 1468554 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B7539101 : Blo 1468554 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B1468955 : Blo 1468554 1468955 := bstep (se 1 (by rfl) ⟨1101716, by rfl⟩ : syracuseStep 1468955 = 2203433) B2203433
theorem B1468959 : Blo 1468554 1468959 := bstep (se 1 (by rfl) ⟨1101719, by rfl⟩ : syracuseStep 1468959 = 2203439) B2203439
theorem B2828987 : Blo 1468554 2828987 := bstep (se 1 (by rfl) ⟨2121740, by rfl⟩ : syracuseStep 2828987 = 4243481) B4243481
theorem B1469275 : Blo 1468554 1469275 := bstep (se 1 (by rfl) ⟨1101956, by rfl⟩ : syracuseStep 1469275 = 2203913) B2203913
theorem B1983409043 : Blo 1468554 1983409043 := bstep (se 1 (by rfl) ⟨1487556782, by rfl⟩ : syracuseStep 1983409043 = 2975113565) B2975113565
theorem B1469343 : Blo 1468554 1469343 := bstep (se 1 (by rfl) ⟨1102007, by rfl⟩ : syracuseStep 1469343 = 2204015) B2204015
theorem B5655527 : Blo 1468554 5655527 := bstep (se 1 (by rfl) ⟨4241645, by rfl⟩ : syracuseStep 5655527 = 8483291) B8483291
theorem B5295137 : Blo 1468554 5295137 := bstep (se 2 (by rfl) ⟨1985676, by rfl⟩ : syracuseStep 5295137 = 3971353) B3971353
theorem B1469487 : Blo 1468554 1469487 := bstep (se 1 (by rfl) ⟨1102115, by rfl⟩ : syracuseStep 1469487 = 2204231) B2204231
theorem B1469511 : Blo 1468554 1469511 := bstep (se 1 (by rfl) ⟨1102133, by rfl⟩ : syracuseStep 1469511 = 2204267) B2204267
theorem B1469663 : Blo 1468554 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B7441631 : Blo 1468554 7441631 := bstep (se 1 (by rfl) ⟨5581223, by rfl⟩ : syracuseStep 7441631 = 11162447) B11162447
theorem B8367371 : Blo 1468554 8367371 := bstep (se 1 (by rfl) ⟨6275528, by rfl⟩ : syracuseStep 8367371 = 12551057) B12551057
theorem B11308339 : Blo 1468554 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B32206157 : Blo 1468554 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B11152727 : Blo 1468554 11152727 := bstep (se 1 (by rfl) ⟨8364545, by rfl⟩ : syracuseStep 11152727 = 16729091) B16729091
theorem B1764839 : Blo 1468554 1764839 := bstep (se 1 (by rfl) ⟨1323629, by rfl⟩ : syracuseStep 1764839 = 2647259) B2647259
theorem B1469927 : Blo 1468554 1469927 := bstep (se 1 (by rfl) ⟨1102445, by rfl⟩ : syracuseStep 1469927 = 2204891) B2204891
theorem B3305033 : Blo 1468554 3305033 := bstep (se 2 (by rfl) ⟨1239387, by rfl⟩ : syracuseStep 3305033 = 2478775) B2478775
theorem B35753555 : Blo 1468554 35753555 := bstep (se 1 (by rfl) ⟨26815166, by rfl⟩ : syracuseStep 35753555 = 53630333) B53630333
theorem B1470043 : Blo 1468554 1470043 := bstep (se 1 (by rfl) ⟨1102532, by rfl⟩ : syracuseStep 1470043 = 2205065) B2205065
theorem B2977387 : Blo 1468554 2977387 := bstep (se 1 (by rfl) ⟨2233040, by rfl⟩ : syracuseStep 2977387 = 4466081) B4466081
theorem B1470279 : Blo 1468554 1470279 := bstep (se 1 (by rfl) ⟨1102709, by rfl⟩ : syracuseStep 1470279 = 2205419) B2205419
theorem B8482733 : Blo 1468554 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B8368055 : Blo 1468554 8368055 := bstep (se 1 (by rfl) ⟨6276041, by rfl⟩ : syracuseStep 8368055 = 12552083) B12552083
theorem B4960223 : Blo 1468554 4960223 := bstep (se 1 (by rfl) ⟨3720167, by rfl⟩ : syracuseStep 4960223 = 7440335) B7440335
theorem B1470431 : Blo 1468554 1470431 := bstep (se 1 (by rfl) ⟨1102823, by rfl⟩ : syracuseStep 1470431 = 2205647) B2205647
theorem B4960385 : Blo 1468554 4960385 := bstep (se 2 (by rfl) ⟨1860144, by rfl⟩ : syracuseStep 4960385 = 3720289) B3720289
theorem B4182205 : Blo 1468554 4182205 := bstep (se 3 (by rfl) ⟨784163, by rfl⟩ : syracuseStep 4182205 = 1568327) B1568327
theorem B4706687 : Blo 1468554 4706687 := bstep (se 1 (by rfl) ⟨3530015, by rfl⟩ : syracuseStep 4706687 = 7060031) B7060031
theorem B10744265 : Blo 1468554 10744265 := bstep (se 2 (by rfl) ⟨4029099, by rfl⟩ : syracuseStep 10744265 = 8058199) B8058199
theorem B4960871 : Blo 1468554 4960871 := bstep (se 1 (by rfl) ⟨3720653, by rfl⟩ : syracuseStep 4960871 = 7441307) B7441307
theorem B6279869 : Blo 1468554 6279869 := bstep (se 3 (by rfl) ⟨1177475, by rfl⟩ : syracuseStep 6279869 = 2354951) B2354951
theorem B5026585 : Blo 1468554 5026585 := bstep (se 2 (by rfl) ⟨1884969, by rfl⟩ : syracuseStep 5026585 = 3769939) B3769939
theorem B4961195 : Blo 1468554 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B10589147 : Blo 1468554 10589147 := bstep (se 1 (by rfl) ⟨7941860, by rfl⟩ : syracuseStep 10589147 = 15883721) B15883721
theorem B2479099 : Blo 1468554 2479099 := bstep (se 1 (by rfl) ⟨1859324, by rfl⟩ : syracuseStep 2479099 = 3718649) B3718649
theorem B3306491 : Blo 1468554 3306491 := bstep (se 1 (by rfl) ⟨2479868, by rfl⟩ : syracuseStep 3306491 = 4959737) B4959737
theorem B8057929 : Blo 1468554 8057929 := bstep (se 2 (by rfl) ⟨3021723, by rfl⟩ : syracuseStep 8057929 = 6043447) B6043447
theorem B4707467 : Blo 1468554 4707467 := bstep (se 1 (by rfl) ⟨3530600, by rfl⟩ : syracuseStep 4707467 = 7061201) B7061201
theorem B3019951 : Blo 1468554 3019951 := bstep (se 1 (by rfl) ⟨2264963, by rfl⟩ : syracuseStep 3019951 = 4529927) B4529927
theorem B3306671 : Blo 1468554 3306671 := bstep (se 1 (by rfl) ⟨2480003, by rfl⟩ : syracuseStep 3306671 = 4960007) B4960007
theorem B3306707 : Blo 1468554 3306707 := bstep (se 1 (by rfl) ⟨2480030, by rfl⟩ : syracuseStep 3306707 = 4960061) B4960061
theorem B4961627 : Blo 1468554 4961627 := bstep (se 1 (by rfl) ⟨3721220, by rfl⟩ : syracuseStep 4961627 = 7442441) B7442441
theorem B2479531 : Blo 1468554 2479531 := bstep (se 1 (by rfl) ⟨1859648, by rfl⟩ : syracuseStep 2479531 = 3719297) B3719297
theorem B7443899 : Blo 1468554 7443899 := bstep (se 1 (by rfl) ⟨5582924, by rfl⟩ : syracuseStep 7443899 = 11165849) B11165849
theorem B4961735 : Blo 1468554 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B3306977 : Blo 1468554 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B5297633 : Blo 1468554 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B2479727 : Blo 1468554 2479727 := bstep (se 1 (by rfl) ⟨1859795, by rfl⟩ : syracuseStep 2479727 = 3719591) B3719591
theorem B325998229 : Blo 1468554 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B2479835 : Blo 1468554 2479835 := bstep (se 1 (by rfl) ⟨1859876, by rfl⟩ : syracuseStep 2479835 = 3719753) B3719753
theorem B4962059 : Blo 1468554 4962059 := bstep (se 1 (by rfl) ⟨3721544, by rfl⟩ : syracuseStep 4962059 = 7443089) B7443089
theorem B5297977 : Blo 1468554 5297977 := bstep (se 2 (by rfl) ⟨1986741, by rfl⟩ : syracuseStep 5297977 = 3973483) B3973483
theorem B6125507 : Blo 1468554 6125507 := bstep (se 1 (by rfl) ⟨4594130, by rfl⟩ : syracuseStep 6125507 = 9188261) B9188261
theorem B2480071 : Blo 1468554 2480071 := bstep (se 1 (by rfl) ⟨1860053, by rfl⟩ : syracuseStep 2480071 = 3720107) B3720107
theorem B3528679 : Blo 1468554 3528679 := bstep (se 1 (by rfl) ⟨2646509, by rfl⟩ : syracuseStep 3528679 = 5293019) B5293019
theorem B4708327 : Blo 1468554 4708327 := bstep (se 1 (by rfl) ⟨3531245, by rfl⟩ : syracuseStep 4708327 = 7062491) B7062491
theorem B1652719 : Blo 1468554 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B2791417 : Blo 1468554 2791417 := bstep (se 2 (by rfl) ⟨1046781, by rfl⟩ : syracuseStep 2791417 = 2093563) B2093563
theorem B4962329 : Blo 1468554 4962329 := bstep (se 2 (by rfl) ⟨1860873, by rfl⟩ : syracuseStep 4962329 = 3721747) B3721747
theorem B2979983 : Blo 1468554 2979983 := bstep (se 1 (by rfl) ⟨2234987, by rfl⟩ : syracuseStep 2979983 = 4469975) B4469975
theorem B3717353 : Blo 1468554 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B2980073 : Blo 1468554 2980073 := bstep (se 2 (by rfl) ⟨1117527, by rfl⟩ : syracuseStep 2980073 = 2235055) B2235055
theorem B3528947 : Blo 1468554 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B2234665 : Blo 1468554 2234665 := bstep (se 2 (by rfl) ⟨837999, by rfl⟩ : syracuseStep 2234665 = 1675999) B1675999
theorem B2791721 : Blo 1468554 2791721 := bstep (se 2 (by rfl) ⟨1046895, by rfl⟩ : syracuseStep 2791721 = 2093791) B2093791
theorem B2480827 : Blo 1468554 2480827 := bstep (se 1 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 2480827 = 3721241) B3721241
theorem B18840275 : Blo 1468554 18840275 := bstep (se 1 (by rfl) ⟨14130206, by rfl⟩ : syracuseStep 18840275 = 28260413) B28260413
theorem B3717971 : Blo 1468554 3717971 := bstep (se 1 (by rfl) ⟨2788478, by rfl⟩ : syracuseStep 3717971 = 5576957) B5576957
theorem B15891335 : Blo 1468554 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B3529631 : Blo 1468554 3529631 := bstep (se 1 (by rfl) ⟨2647223, by rfl⟩ : syracuseStep 3529631 = 5294447) B5294447
theorem B2481131 : Blo 1468554 2481131 := bstep (se 1 (by rfl) ⟨1860848, by rfl⟩ : syracuseStep 2481131 = 3721697) B3721697
theorem B206461973 : Blo 1468554 206461973 := bstep (se 6 (by rfl) ⟨4838952, by rfl⟩ : syracuseStep 206461973 = 9677905) B9677905
theorem B3308615 : Blo 1468554 3308615 := bstep (se 1 (by rfl) ⟨2481461, by rfl⟩ : syracuseStep 3308615 = 4962923) B4962923
theorem B8371289 : Blo 1468554 8371289 := bstep (se 2 (by rfl) ⟨3139233, by rfl⟩ : syracuseStep 8371289 = 6278467) B6278467
theorem B5577943 : Blo 1468554 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B1858783 : Blo 1468554 1858783 := bstep (se 1 (by rfl) ⟨1394087, by rfl⟩ : syracuseStep 1858783 = 2788175) B2788175
theorem B2202959 : Blo 1468554 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B2203049 : Blo 1468554 2203049 := bstep (se 2 (by rfl) ⟨826143, by rfl⟩ : syracuseStep 2203049 = 1652287) B1652287
theorem B2203199 : Blo 1468554 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B11157101 : Blo 1468554 11157101 := bstep (se 3 (by rfl) ⟨2091956, by rfl⟩ : syracuseStep 11157101 = 4183913) B4183913
theorem B2203463 : Blo 1468554 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B2203547 : Blo 1468554 2203547 := bstep (se 1 (by rfl) ⟨1652660, by rfl⟩ : syracuseStep 2203547 = 3305321) B3305321
theorem B636281033 : Blo 1468554 636281033 := bstep (se 2 (by rfl) ⟨238605387, by rfl⟩ : syracuseStep 636281033 = 477210775) B477210775
theorem B1884395 : Blo 1468554 1884395 := bstep (se 1 (by rfl) ⟨1413296, by rfl⟩ : syracuseStep 1884395 = 2826593) B2826593
theorem B3137791 : Blo 1468554 3137791 := bstep (se 1 (by rfl) ⟨2353343, by rfl⟩ : syracuseStep 3137791 = 4706687) B4706687
theorem B3137953 : Blo 1468554 3137953 := bstep (se 2 (by rfl) ⟨1176732, by rfl⟩ : syracuseStep 3137953 = 2353465) B2353465
theorem B4186579 : Blo 1468554 4186579 := bstep (se 1 (by rfl) ⟨3139934, by rfl⟩ : syracuseStep 4186579 = 6279869) B6279869
theorem B3719783 : Blo 1468554 3719783 := bstep (se 1 (by rfl) ⟨2789837, by rfl⟩ : syracuseStep 3719783 = 5579675) B5579675
theorem B2204327 : Blo 1468554 2204327 := bstep (se 1 (by rfl) ⟨1653245, by rfl⟩ : syracuseStep 2204327 = 3306491) B3306491
theorem B3138311 : Blo 1468554 3138311 := bstep (se 1 (by rfl) ⟨2353733, by rfl⟩ : syracuseStep 3138311 = 4707467) B4707467
theorem B2204447 : Blo 1468554 2204447 := bstep (se 1 (by rfl) ⟨1653335, by rfl⟩ : syracuseStep 2204447 = 3306671) B3306671
theorem B2204471 : Blo 1468554 2204471 := bstep (se 1 (by rfl) ⟨1653353, by rfl⟩ : syracuseStep 2204471 = 3306707) B3306707
theorem B2204651 : Blo 1468554 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B3531755 : Blo 1468554 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B6702113 : Blo 1468554 6702113 := bstep (se 2 (by rfl) ⟨2513292, by rfl⟩ : syracuseStep 6702113 = 5026585) B5026585
theorem B1861147 : Blo 1468554 1861147 := bstep (se 1 (by rfl) ⟨1395860, by rfl⟩ : syracuseStep 1861147 = 2791721) B2791721
theorem B60311141 : Blo 1468554 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B12560183 : Blo 1468554 12560183 := bstep (se 1 (by rfl) ⟨9420137, by rfl⟩ : syracuseStep 12560183 = 18840275) B18840275
theorem B10594223 : Blo 1468554 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B2353087 : Blo 1468554 2353087 := bstep (se 1 (by rfl) ⟨1764815, by rfl⟩ : syracuseStep 2353087 = 3529631) B3529631
theorem B3770351 : Blo 1468554 3770351 := bstep (se 1 (by rfl) ⟨2827763, by rfl⟩ : syracuseStep 3770351 = 5655527) B5655527
theorem B2205743 : Blo 1468554 2205743 := bstep (se 1 (by rfl) ⟨1654307, by rfl⟩ : syracuseStep 2205743 = 3308615) B3308615
theorem B25102385 : Blo 1468554 25102385 := bstep (se 2 (by rfl) ⟨9413394, by rfl⟩ : syracuseStep 25102385 = 18826789) B18826789
theorem B5580859 : Blo 1468554 5580859 := bstep (se 1 (by rfl) ⟨4185644, by rfl⟩ : syracuseStep 5580859 = 8371289) B8371289
theorem B1468639 : Blo 1468554 1468639 := bstep (se 1 (by rfl) ⟨1101479, by rfl⟩ : syracuseStep 1468639 = 2202959) B2202959
theorem B1468699 : Blo 1468554 1468699 := bstep (se 1 (by rfl) ⟨1101524, by rfl⟩ : syracuseStep 1468699 = 2203049) B2203049
theorem B1468799 : Blo 1468554 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B7063969 : Blo 1468554 7063969 := bstep (se 2 (by rfl) ⟨2648988, by rfl⟩ : syracuseStep 7063969 = 5297977) B5297977
theorem B1468975 : Blo 1468554 1468975 := bstep (se 1 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 1468975 = 2203463) B2203463
theorem B1469031 : Blo 1468554 1469031 := bstep (se 1 (by rfl) ⟨1101773, by rfl⟩ : syracuseStep 1469031 = 2203547) B2203547
theorem B5655155 : Blo 1468554 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B4704905 : Blo 1468554 4704905 := bstep (se 2 (by rfl) ⟨1764339, by rfl⟩ : syracuseStep 4704905 = 3528679) B3528679
theorem B6277769 : Blo 1468554 6277769 := bstep (se 2 (by rfl) ⟨2354163, by rfl⟩ : syracuseStep 6277769 = 4708327) B4708327
theorem B3721889 : Blo 1468554 3721889 := bstep (se 2 (by rfl) ⟨1395708, by rfl⟩ : syracuseStep 3721889 = 2791417) B2791417
theorem B120720145 : Blo 1468554 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B7162843 : Blo 1468554 7162843 := bstep (se 1 (by rfl) ⟨5372132, by rfl⟩ : syracuseStep 7162843 = 10744265) B10744265
theorem B1469407 : Blo 1468554 1469407 := bstep (se 1 (by rfl) ⟨1102055, by rfl⟩ : syracuseStep 1469407 = 2204111) B2204111
theorem B1469435 : Blo 1468554 1469435 := bstep (se 1 (by rfl) ⟨1102076, by rfl⟩ : syracuseStep 1469435 = 2204153) B2204153
theorem B1469503 : Blo 1468554 1469503 := bstep (se 1 (by rfl) ⟨1102127, by rfl⟩ : syracuseStep 1469503 = 2204255) B2204255
theorem B15879397 : Blo 1468554 15879397 := bstep (se 4 (by rfl) ⟨1488693, by rfl⟩ : syracuseStep 15879397 = 2977387) B2977387
theorem B5582135 : Blo 1468554 5582135 := bstep (se 1 (by rfl) ⟨4186601, by rfl⟩ : syracuseStep 5582135 = 8373203) B8373203
theorem B1469823 : Blo 1468554 1469823 := bstep (se 1 (by rfl) ⟨1102367, by rfl⟩ : syracuseStep 1469823 = 2204735) B2204735
theorem B1469851 : Blo 1468554 1469851 := bstep (se 1 (by rfl) ⟨1102388, by rfl⟩ : syracuseStep 1469851 = 2204777) B2204777
theorem B3304871 : Blo 1468554 3304871 := bstep (se 1 (by rfl) ⟨2478653, by rfl⟩ : syracuseStep 3304871 = 4957307) B4957307
theorem B1469919 : Blo 1468554 1469919 := bstep (se 1 (by rfl) ⟨1102439, by rfl⟩ : syracuseStep 1469919 = 2204879) B2204879
theorem B2354759 : Blo 1468554 2354759 := bstep (se 1 (by rfl) ⟨1766069, by rfl⟩ : syracuseStep 2354759 = 3532139) B3532139
theorem B3305051 : Blo 1468554 3305051 := bstep (se 1 (by rfl) ⟨2478788, by rfl⟩ : syracuseStep 3305051 = 4957577) B4957577
theorem B1470055 : Blo 1468554 1470055 := bstep (se 1 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 1470055 = 2205083) B2205083
theorem B1470203 : Blo 1468554 1470203 := bstep (se 1 (by rfl) ⟨1102652, by rfl⟩ : syracuseStep 1470203 = 2205305) B2205305
theorem B1568575 : Blo 1468554 1568575 := bstep (se 1 (by rfl) ⟨1176431, by rfl⟩ : syracuseStep 1568575 = 2352863) B2352863
theorem B1470271 : Blo 1468554 1470271 := bstep (se 1 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 1470271 = 2205407) B2205407
theorem B1470335 : Blo 1468554 1470335 := bstep (se 1 (by rfl) ⟨1102751, by rfl⟩ : syracuseStep 1470335 = 2205503) B2205503
theorem B4706237 : Blo 1468554 4706237 := bstep (se 3 (by rfl) ⟨882419, by rfl⟩ : syracuseStep 4706237 = 1764839) B1764839
theorem B12545999 : Blo 1468554 12545999 := bstep (se 1 (by rfl) ⟨9409499, by rfl⟩ : syracuseStep 12545999 = 18818999) B18818999
theorem B4083671 : Blo 1468554 4083671 := bstep (se 1 (by rfl) ⟨3062753, by rfl⟩ : syracuseStep 4083671 = 6125507) B6125507
theorem B1470447 : Blo 1468554 1470447 := bstep (se 1 (by rfl) ⟨1102835, by rfl⟩ : syracuseStep 1470447 = 2205671) B2205671
theorem B3305465 : Blo 1468554 3305465 := bstep (se 2 (by rfl) ⟨1239549, by rfl⟩ : syracuseStep 3305465 = 2479099) B2479099
theorem B1470459 : Blo 1468554 1470459 := bstep (se 1 (by rfl) ⟨1102844, by rfl⟩ : syracuseStep 1470459 = 2205689) B2205689
theorem B1470527 : Blo 1468554 1470527 := bstep (se 1 (by rfl) ⟨1102895, by rfl⟩ : syracuseStep 1470527 = 2205791) B2205791
theorem B3305555 : Blo 1468554 3305555 := bstep (se 1 (by rfl) ⟨2479166, by rfl⟩ : syracuseStep 3305555 = 4958333) B4958333
theorem B1986655 : Blo 1468554 1986655 := bstep (se 1 (by rfl) ⟨1489991, by rfl⟩ : syracuseStep 1986655 = 2979983) B2979983
theorem B10743905 : Blo 1468554 10743905 := bstep (se 2 (by rfl) ⟨4028964, by rfl⟩ : syracuseStep 10743905 = 8057929) B8057929
theorem B4026511 : Blo 1468554 4026511 := bstep (se 1 (by rfl) ⟨3019883, by rfl⟩ : syracuseStep 4026511 = 6039767) B6039767
theorem B2478235 : Blo 1468554 2478235 := bstep (se 1 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 2478235 = 3717353) B3717353
theorem B1986715 : Blo 1468554 1986715 := bstep (se 1 (by rfl) ⟨1490036, by rfl⟩ : syracuseStep 1986715 = 2980073) B2980073
theorem B4026601 : Blo 1468554 4026601 := bstep (se 2 (by rfl) ⟨1509975, by rfl⟩ : syracuseStep 4026601 = 3019951) B3019951
theorem B3305735 : Blo 1468554 3305735 := bstep (se 1 (by rfl) ⟨2479301, by rfl⟩ : syracuseStep 3305735 = 4958603) B4958603
theorem B4239635 : Blo 1468554 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B5026067 : Blo 1468554 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B2478377 : Blo 1468554 2478377 := bstep (se 2 (by rfl) ⟨929391, by rfl⟩ : syracuseStep 2478377 = 1858783) B1858783
theorem B2478647 : Blo 1468554 2478647 := bstep (se 1 (by rfl) ⟨1858985, by rfl⟩ : syracuseStep 2478647 = 3717971) B3717971
theorem B3306041 : Blo 1468554 3306041 := bstep (se 2 (by rfl) ⟨1239765, by rfl⟩ : syracuseStep 3306041 = 2479531) B2479531
theorem B30175861 : Blo 1468554 30175861 := bstep (se 5 (by rfl) ⟨1414493, by rfl⟩ : syracuseStep 30175861 = 2828987) B2828987
theorem B54334205 : Blo 1468554 54334205 := bstep (se 3 (by rfl) ⟨10187663, by rfl⟩ : syracuseStep 54334205 = 20375327) B20375327
theorem B4961087 : Blo 1468554 4961087 := bstep (se 1 (by rfl) ⟨3720815, by rfl⟩ : syracuseStep 4961087 = 7441631) B7441631
theorem B434664305 : Blo 1468554 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B7435151 : Blo 1468554 7435151 := bstep (se 1 (by rfl) ⟨5576363, by rfl⟩ : syracuseStep 7435151 = 11152727) B11152727
theorem B23835703 : Blo 1468554 23835703 := bstep (se 1 (by rfl) ⟨17876777, by rfl⟩ : syracuseStep 23835703 = 35753555) B35753555
theorem B3306761 : Blo 1468554 3306761 := bstep (se 2 (by rfl) ⟨1240035, by rfl⟩ : syracuseStep 3306761 = 2480071) B2480071
theorem B3306815 : Blo 1468554 3306815 := bstep (se 1 (by rfl) ⟨2480111, by rfl⟩ : syracuseStep 3306815 = 4960223) B4960223
theorem B3306923 : Blo 1468554 3306923 := bstep (se 1 (by rfl) ⟨2480192, by rfl⟩ : syracuseStep 3306923 = 4960385) B4960385
theorem B14120365 : Blo 1468554 14120365 := bstep (se 3 (by rfl) ⟨2647568, by rfl⟩ : syracuseStep 14120365 = 5295137) B5295137
theorem B4961789 : Blo 1468554 4961789 := bstep (se 3 (by rfl) ⟨930335, by rfl⟩ : syracuseStep 4961789 = 1860671) B1860671
theorem B5576273 : Blo 1468554 5576273 := bstep (se 2 (by rfl) ⟨2091102, by rfl⟩ : syracuseStep 5576273 = 4182205) B4182205
theorem B2979553 : Blo 1468554 2979553 := bstep (se 2 (by rfl) ⟨1117332, by rfl⟩ : syracuseStep 2979553 = 2234665) B2234665
theorem B3307247 : Blo 1468554 3307247 := bstep (se 1 (by rfl) ⟨2480435, by rfl⟩ : syracuseStep 3307247 = 4960871) B4960871
theorem B2479943 : Blo 1468554 2479943 := bstep (se 1 (by rfl) ⟨1859957, by rfl⟩ : syracuseStep 2479943 = 3719915) B3719915
theorem B2479963 : Blo 1468554 2479963 := bstep (se 1 (by rfl) ⟨1859972, by rfl⟩ : syracuseStep 2479963 = 3719945) B3719945
theorem B3307463 : Blo 1468554 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B9410525 : Blo 1468554 9410525 := bstep (se 3 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 9410525 = 3528947) B3528947
theorem B6281185 : Blo 1468554 6281185 := bstep (se 2 (by rfl) ⟨2355444, by rfl⟩ : syracuseStep 6281185 = 4710889) B4710889
theorem B7059431 : Blo 1468554 7059431 := bstep (se 1 (by rfl) ⟨5294573, by rfl⟩ : syracuseStep 7059431 = 10589147) B10589147
theorem B9410579 : Blo 1468554 9410579 := bstep (se 1 (by rfl) ⟨7057934, by rfl⟩ : syracuseStep 9410579 = 14115869) B14115869
theorem B3307751 : Blo 1468554 3307751 := bstep (se 1 (by rfl) ⟨2480813, by rfl⟩ : syracuseStep 3307751 = 4961627) B4961627
theorem B3307769 : Blo 1468554 3307769 := bstep (se 2 (by rfl) ⟨1240413, by rfl⟩ : syracuseStep 3307769 = 2480827) B2480827
theorem B4962599 : Blo 1468554 4962599 := bstep (se 1 (by rfl) ⟨3721949, by rfl⟩ : syracuseStep 4962599 = 7443899) B7443899
theorem B3307823 : Blo 1468554 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B1653151 : Blo 1468554 1653151 := bstep (se 1 (by rfl) ⟨1239863, by rfl⟩ : syracuseStep 1653151 = 2479727) B2479727
theorem B1653223 : Blo 1468554 1653223 := bstep (se 1 (by rfl) ⟨1239917, by rfl⟩ : syracuseStep 1653223 = 2479835) B2479835
theorem B3308039 : Blo 1468554 3308039 := bstep (se 1 (by rfl) ⟨2481029, by rfl⟩ : syracuseStep 3308039 = 4962059) B4962059
theorem B3308219 : Blo 1468554 3308219 := bstep (se 1 (by rfl) ⟨2481164, by rfl⟩ : syracuseStep 3308219 = 4962329) B4962329
theorem B34413335 : Blo 1468554 34413335 := bstep (se 1 (by rfl) ⟨25810001, by rfl⟩ : syracuseStep 34413335 = 51620003) B51620003
theorem B7437257 : Blo 1468554 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B1654087 : Blo 1468554 1654087 := bstep (se 1 (by rfl) ⟨1240565, by rfl⟩ : syracuseStep 1654087 = 2481131) B2481131
theorem B137641315 : Blo 1468554 137641315 := bstep (se 1 (by rfl) ⟨103230986, by rfl⟩ : syracuseStep 137641315 = 206461973) B206461973
theorem B5578247 : Blo 1468554 5578247 := bstep (se 1 (by rfl) ⟨4183685, by rfl⟩ : syracuseStep 5578247 = 8367371) B8367371
theorem B21470771 : Blo 1468554 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B2203355 : Blo 1468554 2203355 := bstep (se 1 (by rfl) ⟨1652516, by rfl⟩ : syracuseStep 2203355 = 3305033) B3305033
theorem B5289090781 : Blo 1468554 5289090781 := bstep (se 3 (by rfl) ⟨991704521, by rfl⟩ : syracuseStep 5289090781 = 1983409043) B1983409043
theorem B7438067 : Blo 1468554 7438067 := bstep (se 1 (by rfl) ⟨5578550, by rfl⟩ : syracuseStep 7438067 = 11157101) B11157101
theorem B5578703 : Blo 1468554 5578703 := bstep (se 1 (by rfl) ⟨4184027, by rfl⟩ : syracuseStep 5578703 = 8368055) B8368055
theorem B2203625 : Blo 1468554 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B2203703 : Blo 1468554 2203703 := bstep (se 1 (by rfl) ⟨1652777, by rfl⟩ : syracuseStep 2203703 = 3305555) B3305555
theorem B2203823 : Blo 1468554 2203823 := bstep (se 1 (by rfl) ⟨1652867, by rfl⟩ : syracuseStep 2203823 = 3305735) B3305735
theorem B3350711 : Blo 1468554 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B2204027 : Blo 1468554 2204027 := bstep (se 1 (by rfl) ⟨1653020, by rfl⟩ : syracuseStep 2204027 = 3306041) B3306041
theorem B2204201 : Blo 1468554 2204201 := bstep (se 2 (by rfl) ⟨826575, by rfl⟩ : syracuseStep 2204201 = 1653151) B1653151
theorem B289776203 : Blo 1468554 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B4956767 : Blo 1468554 4956767 := bstep (se 1 (by rfl) ⟨3717575, by rfl⟩ : syracuseStep 4956767 = 7435151) B7435151
theorem B2204297 : Blo 1468554 2204297 := bstep (se 2 (by rfl) ⟨826611, by rfl⟩ : syracuseStep 2204297 = 1653223) B1653223
theorem B11305693 : Blo 1468554 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B2204507 : Blo 1468554 2204507 := bstep (se 1 (by rfl) ⟨1653380, by rfl⟩ : syracuseStep 2204507 = 3306761) B3306761
theorem B2204543 : Blo 1468554 2204543 := bstep (se 1 (by rfl) ⟨1653407, by rfl⟩ : syracuseStep 2204543 = 3306815) B3306815
theorem B2204615 : Blo 1468554 2204615 := bstep (se 1 (by rfl) ⟨1653461, by rfl⟩ : syracuseStep 2204615 = 3306923) B3306923
theorem B40207427 : Blo 1468554 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B2204831 : Blo 1468554 2204831 := bstep (se 1 (by rfl) ⟨1653623, by rfl⟩ : syracuseStep 2204831 = 3307247) B3307247
theorem B8373455 : Blo 1468554 8373455 := bstep (se 1 (by rfl) ⟨6280091, by rfl⟩ : syracuseStep 8373455 = 12560183) B12560183
theorem B7062815 : Blo 1468554 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B2204975 : Blo 1468554 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B2205167 : Blo 1468554 2205167 := bstep (se 1 (by rfl) ⟨1653875, by rfl⟩ : syracuseStep 2205167 = 3307751) B3307751
theorem B2205179 : Blo 1468554 2205179 := bstep (se 1 (by rfl) ⟨1653884, by rfl⟩ : syracuseStep 2205179 = 3307769) B3307769
theorem B2205215 : Blo 1468554 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B2205359 : Blo 1468554 2205359 := bstep (se 1 (by rfl) ⟨1654019, by rfl⟩ : syracuseStep 2205359 = 3308039) B3308039
theorem B2205449 : Blo 1468554 2205449 := bstep (se 2 (by rfl) ⟨827043, by rfl⟩ : syracuseStep 2205449 = 1654087) B1654087
theorem B2205479 : Blo 1468554 2205479 := bstep (se 1 (by rfl) ⟨1654109, by rfl⟩ : syracuseStep 2205479 = 3308219) B3308219
theorem B18827153 : Blo 1468554 18827153 := bstep (se 2 (by rfl) ⟨7060182, by rfl⟩ : syracuseStep 18827153 = 14120365) B14120365
theorem B4958171 : Blo 1468554 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B3721423 : Blo 1468554 3721423 := bstep (se 1 (by rfl) ⟨2791067, by rfl⟩ : syracuseStep 3721423 = 5582135) B5582135
theorem B14313847 : Blo 1468554 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B2091433 : Blo 1468554 2091433 := bstep (se 2 (by rfl) ⟨784287, by rfl⟩ : syracuseStep 2091433 = 1568575) B1568575
theorem B1468903 : Blo 1468554 1468903 := bstep (se 1 (by rfl) ⟨1101677, by rfl⟩ : syracuseStep 1468903 = 2203355) B2203355
theorem B4958711 : Blo 1468554 4958711 := bstep (se 1 (by rfl) ⟨3719033, by rfl⟩ : syracuseStep 4958711 = 7438067) B7438067
theorem B8374913 : Blo 1468554 8374913 := bstep (se 2 (by rfl) ⟨3140592, by rfl⟩ : syracuseStep 8374913 = 6281185) B6281185
theorem B2722447 : Blo 1468554 2722447 := bstep (se 1 (by rfl) ⟨2041835, by rfl⟩ : syracuseStep 2722447 = 4083671) B4083671
theorem B1469083 : Blo 1468554 1469083 := bstep (se 1 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 1469083 = 2203625) B2203625
theorem B7441145 : Blo 1468554 7441145 := bstep (se 2 (by rfl) ⟨2790429, by rfl⟩ : syracuseStep 7441145 = 5580859) B5580859
theorem B2648873 : Blo 1468554 2648873 := bstep (se 2 (by rfl) ⟨993327, by rfl⟩ : syracuseStep 2648873 = 1986655) B1986655
theorem B5368681 : Blo 1468554 5368681 := bstep (se 2 (by rfl) ⟨2013255, by rfl⟩ : syracuseStep 5368681 = 4026511) B4026511
theorem B3304313 : Blo 1468554 3304313 := bstep (se 2 (by rfl) ⟨1239117, by rfl⟩ : syracuseStep 3304313 = 2478235) B2478235
theorem B2648953 : Blo 1468554 2648953 := bstep (se 2 (by rfl) ⟨993357, by rfl⟩ : syracuseStep 2648953 = 1986715) B1986715
theorem B28650413 : Blo 1468554 28650413 := bstep (se 3 (by rfl) ⟨5371952, by rfl⟩ : syracuseStep 28650413 = 10743905) B10743905
theorem B5368801 : Blo 1468554 5368801 := bstep (se 2 (by rfl) ⟨2013300, by rfl⟩ : syracuseStep 5368801 = 4026601) B4026601
theorem B1469551 : Blo 1468554 1469551 := bstep (se 1 (by rfl) ⟨1102163, by rfl⟩ : syracuseStep 1469551 = 2204327) B2204327
theorem B1469631 : Blo 1468554 1469631 := bstep (se 1 (by rfl) ⟨1102223, by rfl⟩ : syracuseStep 1469631 = 2204447) B2204447
theorem B1469647 : Blo 1468554 1469647 := bstep (se 1 (by rfl) ⟨1102235, by rfl⟩ : syracuseStep 1469647 = 2204471) B2204471
theorem B5582105 : Blo 1468554 5582105 := bstep (se 2 (by rfl) ⟨2093289, by rfl⟩ : syracuseStep 5582105 = 4186579) B4186579
theorem B5025053 : Blo 1468554 5025053 := bstep (se 3 (by rfl) ⟨942197, by rfl⟩ : syracuseStep 5025053 = 1884395) B1884395
theorem B1469767 : Blo 1468554 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B2354503 : Blo 1468554 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B40234481 : Blo 1468554 40234481 := bstep (se 2 (by rfl) ⟨15087930, by rfl⟩ : syracuseStep 40234481 = 30175861) B30175861
theorem B160960193 : Blo 1468554 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B1470495 : Blo 1468554 1470495 := bstep (se 1 (by rfl) ⟨1102871, by rfl⟩ : syracuseStep 1470495 = 2205743) B2205743
theorem B31780937 : Blo 1468554 31780937 := bstep (se 2 (by rfl) ⟨11917851, by rfl⟩ : syracuseStep 31780937 = 23835703) B23835703
theorem B21172529 : Blo 1468554 21172529 := bstep (se 2 (by rfl) ⟨7939698, by rfl⟩ : syracuseStep 21172529 = 15879397) B15879397
theorem B183521753 : Blo 1468554 183521753 := bstep (se 2 (by rfl) ⟨68820657, by rfl⟩ : syracuseStep 183521753 = 137641315) B137641315
theorem B22942223 : Blo 1468554 22942223 := bstep (se 1 (by rfl) ⟨17206667, by rfl⟩ : syracuseStep 22942223 = 34413335) B34413335
theorem B8368829 : Blo 1468554 8368829 := bstep (se 3 (by rfl) ⟨1569155, by rfl⟩ : syracuseStep 8368829 = 3138311) B3138311
theorem B7052121041 : Blo 1468554 7052121041 := bstep (se 2 (by rfl) ⟨2644545390, by rfl⟩ : syracuseStep 7052121041 = 5289090781) B5289090781
theorem B1569839 : Blo 1468554 1569839 := bstep (se 1 (by rfl) ⟨1177379, by rfl⟩ : syracuseStep 1569839 = 2354759) B2354759
theorem B3306617 : Blo 1468554 3306617 := bstep (se 2 (by rfl) ⟨1239981, by rfl⟩ : syracuseStep 3306617 = 2479963) B2479963
theorem B17872301 : Blo 1468554 17872301 := bstep (se 3 (by rfl) ⟨3351056, by rfl⟩ : syracuseStep 17872301 = 6702113) B6702113
theorem B1652251 : Blo 1468554 1652251 := bstep (se 1 (by rfl) ⟨1239188, by rfl⟩ : syracuseStep 1652251 = 2478377) B2478377
theorem B4183721 : Blo 1468554 4183721 := bstep (se 2 (by rfl) ⟨1568895, by rfl⟩ : syracuseStep 4183721 = 3137791) B3137791
theorem B1652431 : Blo 1468554 1652431 := bstep (se 1 (by rfl) ⟨1239323, by rfl⟩ : syracuseStep 1652431 = 2478647) B2478647
theorem B2479855 : Blo 1468554 2479855 := bstep (se 1 (by rfl) ⟨1859891, by rfl⟩ : syracuseStep 2479855 = 3719783) B3719783
theorem B36222803 : Blo 1468554 36222803 := bstep (se 1 (by rfl) ⟨27167102, by rfl⟩ : syracuseStep 36222803 = 54334205) B54334205
theorem B3307391 : Blo 1468554 3307391 := bstep (se 1 (by rfl) ⟨2480543, by rfl⟩ : syracuseStep 3307391 = 4961087) B4961087
theorem B4183937 : Blo 1468554 4183937 := bstep (se 2 (by rfl) ⟨1568976, by rfl⟩ : syracuseStep 4183937 = 3137953) B3137953
theorem B9418625 : Blo 1468554 9418625 := bstep (se 2 (by rfl) ⟨3531984, by rfl⟩ : syracuseStep 9418625 = 7063969) B7063969
theorem B3307859 : Blo 1468554 3307859 := bstep (se 1 (by rfl) ⟨2480894, by rfl⟩ : syracuseStep 3307859 = 4961789) B4961789
theorem B3717515 : Blo 1468554 3717515 := bstep (se 1 (by rfl) ⟨2788136, by rfl⟩ : syracuseStep 3717515 = 5576273) B5576273
theorem B1653295 : Blo 1468554 1653295 := bstep (se 1 (by rfl) ⟨1239971, by rfl⟩ : syracuseStep 1653295 = 2479943) B2479943
theorem B9550457 : Blo 1468554 9550457 := bstep (se 2 (by rfl) ⟨3581421, by rfl⟩ : syracuseStep 9550457 = 7162843) B7162843
theorem B6273683 : Blo 1468554 6273683 := bstep (se 1 (by rfl) ⟨4705262, by rfl⟩ : syracuseStep 6273683 = 9410525) B9410525
theorem B2513567 : Blo 1468554 2513567 := bstep (se 1 (by rfl) ⟨1885175, by rfl⟩ : syracuseStep 2513567 = 3770351) B3770351
theorem B6273719 : Blo 1468554 6273719 := bstep (se 1 (by rfl) ⟨4705289, by rfl⟩ : syracuseStep 6273719 = 9410579) B9410579
theorem B16734923 : Blo 1468554 16734923 := bstep (se 1 (by rfl) ⟨12551192, by rfl⟩ : syracuseStep 16734923 = 25102385) B25102385
theorem B3308399 : Blo 1468554 3308399 := bstep (se 1 (by rfl) ⟨2481299, by rfl⟩ : syracuseStep 3308399 = 4962599) B4962599
theorem B15080413 : Blo 1468554 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B3136603 : Blo 1468554 3136603 := bstep (se 1 (by rfl) ⟨2352452, by rfl⟩ : syracuseStep 3136603 = 4704905) B4704905
theorem B4185179 : Blo 1468554 4185179 := bstep (se 1 (by rfl) ⟨3138884, by rfl⟩ : syracuseStep 4185179 = 6277769) B6277769
theorem B2481259 : Blo 1468554 2481259 := bstep (se 1 (by rfl) ⟨1860944, by rfl⟩ : syracuseStep 2481259 = 3721889) B3721889
theorem B2481529 : Blo 1468554 2481529 := bstep (se 2 (by rfl) ⟨930573, by rfl⟩ : syracuseStep 2481529 = 1861147) B1861147
theorem B6786997685 : Blo 1468554 6786997685 := bstep (se 5 (by rfl) ⟨318140516, by rfl⟩ : syracuseStep 6786997685 = 636281033) B636281033
theorem B2203247 : Blo 1468554 2203247 := bstep (se 1 (by rfl) ⟨1652435, by rfl⟩ : syracuseStep 2203247 = 3304871) B3304871
theorem B3972737 : Blo 1468554 3972737 := bstep (se 2 (by rfl) ⟨1489776, by rfl⟩ : syracuseStep 3972737 = 2979553) B2979553
theorem B3718831 : Blo 1468554 3718831 := bstep (se 1 (by rfl) ⟨2789123, by rfl⟩ : syracuseStep 3718831 = 5578247) B5578247
theorem B2203367 : Blo 1468554 2203367 := bstep (se 1 (by rfl) ⟨1652525, by rfl⟩ : syracuseStep 2203367 = 3305051) B3305051
theorem B3137449 : Blo 1468554 3137449 := bstep (se 2 (by rfl) ⟨1176543, by rfl⟩ : syracuseStep 3137449 = 2353087) B2353087
theorem B18825149 : Blo 1468554 18825149 := bstep (se 3 (by rfl) ⟨3529715, by rfl⟩ : syracuseStep 18825149 = 7059431) B7059431
theorem B3137491 : Blo 1468554 3137491 := bstep (se 1 (by rfl) ⟨2353118, by rfl⟩ : syracuseStep 3137491 = 4706237) B4706237
theorem B8363999 : Blo 1468554 8363999 := bstep (se 1 (by rfl) ⟨6272999, by rfl⟩ : syracuseStep 8363999 = 12545999) B12545999
theorem B3719135 : Blo 1468554 3719135 := bstep (se 1 (by rfl) ⟨2789351, by rfl⟩ : syracuseStep 3719135 = 5578703) B5578703
theorem B2203643 : Blo 1468554 2203643 := bstep (se 1 (by rfl) ⟨1652732, by rfl⟩ : syracuseStep 2203643 = 3305465) B3305465
theorem B4186237 : Blo 1468554 4186237 := bstep (se 3 (by rfl) ⟨784919, by rfl⟩ : syracuseStep 4186237 = 1569839) B1569839
theorem B14115019 : Blo 1468554 14115019 := bstep (se 1 (by rfl) ⟨10586264, by rfl⟩ : syracuseStep 14115019 = 21172529) B21172529
theorem B122347835 : Blo 1468554 122347835 := bstep (se 1 (by rfl) ⟨91760876, by rfl⟩ : syracuseStep 122347835 = 183521753) B183521753
theorem B15294815 : Blo 1468554 15294815 := bstep (se 1 (by rfl) ⟨11471111, by rfl⟩ : syracuseStep 15294815 = 22942223) B22942223
theorem B193184135 : Blo 1468554 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B5579219 : Blo 1468554 5579219 := bstep (se 1 (by rfl) ⟨4184414, by rfl⟩ : syracuseStep 5579219 = 8368829) B8368829
theorem B26804951 : Blo 1468554 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B2204393 : Blo 1468554 2204393 := bstep (se 2 (by rfl) ⟨826647, by rfl⟩ : syracuseStep 2204393 = 1653295) B1653295
theorem B2204411 : Blo 1468554 2204411 := bstep (se 1 (by rfl) ⟨1653308, by rfl⟩ : syracuseStep 2204411 = 3306617) B3306617
theorem B3629929 : Blo 1468554 3629929 := bstep (se 2 (by rfl) ⟨1361223, by rfl⟩ : syracuseStep 3629929 = 2722447) B2722447
theorem B15074257 : Blo 1468554 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B3531937 : Blo 1468554 3531937 := bstep (se 2 (by rfl) ⟨1324476, by rfl⟩ : syracuseStep 3531937 = 2648953) B2648953
theorem B2204927 : Blo 1468554 2204927 := bstep (se 1 (by rfl) ⟨1653695, by rfl⟩ : syracuseStep 2204927 = 3307391) B3307391
theorem B12551435 : Blo 1468554 12551435 := bstep (se 1 (by rfl) ⟨9413576, by rfl⟩ : syracuseStep 12551435 = 18827153) B18827153
theorem B2205239 : Blo 1468554 2205239 := bstep (se 1 (by rfl) ⟨1653929, by rfl⟩ : syracuseStep 2205239 = 3307859) B3307859
theorem B10593965 : Blo 1468554 10593965 := bstep (se 3 (by rfl) ⟨1986368, by rfl⟩ : syracuseStep 10593965 = 3972737) B3972737
theorem B6366971 : Blo 1468554 6366971 := bstep (se 1 (by rfl) ⟨4775228, by rfl⟩ : syracuseStep 6366971 = 9550457) B9550457
theorem B3139337 : Blo 1468554 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B2205599 : Blo 1468554 2205599 := bstep (se 1 (by rfl) ⟨1654199, by rfl⟩ : syracuseStep 2205599 = 3308399) B3308399
theorem B7063661 : Blo 1468554 7063661 := bstep (se 3 (by rfl) ⟨1324436, by rfl⟩ : syracuseStep 7063661 = 2648873) B2648873
theorem B3721403 : Blo 1468554 3721403 := bstep (se 1 (by rfl) ⟨2791052, by rfl⟩ : syracuseStep 3721403 = 5582105) B5582105
theorem B4958441 : Blo 1468554 4958441 := bstep (se 2 (by rfl) ⟨1859415, by rfl⟩ : syracuseStep 4958441 = 3718831) B3718831
theorem B4524665123 : Blo 1468554 4524665123 := bstep (se 1 (by rfl) ⟨3393498842, by rfl⟩ : syracuseStep 4524665123 = 6786997685) B6786997685
theorem B26822987 : Blo 1468554 26822987 := bstep (se 1 (by rfl) ⟨20117240, by rfl⟩ : syracuseStep 26822987 = 40234481) B40234481
theorem B1468831 : Blo 1468554 1468831 := bstep (se 1 (by rfl) ⟨1101623, by rfl⟩ : syracuseStep 1468831 = 2203247) B2203247
theorem B1468911 : Blo 1468554 1468911 := bstep (se 1 (by rfl) ⟨1101683, by rfl⟩ : syracuseStep 1468911 = 2203367) B2203367
theorem B18805656109 : Blo 1468554 18805656109 := bstep (se 3 (by rfl) ⟨3526060520, by rfl⟩ : syracuseStep 18805656109 = 7052121041) B7052121041
theorem B1469095 : Blo 1468554 1469095 := bstep (se 1 (by rfl) ⟨1101821, by rfl⟩ : syracuseStep 1469095 = 2203643) B2203643
theorem B1469135 : Blo 1468554 1469135 := bstep (se 1 (by rfl) ⟨1101851, by rfl⟩ : syracuseStep 1469135 = 2203703) B2203703
theorem B21187291 : Blo 1468554 21187291 := bstep (se 1 (by rfl) ⟨15890468, by rfl⟩ : syracuseStep 21187291 = 31780937) B31780937
theorem B1469215 : Blo 1468554 1469215 := bstep (se 1 (by rfl) ⟨1101911, by rfl⟩ : syracuseStep 1469215 = 2203823) B2203823
theorem B1469351 : Blo 1468554 1469351 := bstep (se 1 (by rfl) ⟨1102013, by rfl⟩ : syracuseStep 1469351 = 2204027) B2204027
theorem B1469467 : Blo 1468554 1469467 := bstep (se 1 (by rfl) ⟨1102100, by rfl⟩ : syracuseStep 1469467 = 2204201) B2204201
theorem B3304511 : Blo 1468554 3304511 := bstep (se 1 (by rfl) ⟨2478383, by rfl⟩ : syracuseStep 3304511 = 4956767) B4956767
theorem B1469531 : Blo 1468554 1469531 := bstep (se 1 (by rfl) ⟨1102148, by rfl⟩ : syracuseStep 1469531 = 2204297) B2204297
theorem B2788577 : Blo 1468554 2788577 := bstep (se 2 (by rfl) ⟨1045716, by rfl⟩ : syracuseStep 2788577 = 2091433) B2091433
theorem B1469671 : Blo 1468554 1469671 := bstep (se 1 (by rfl) ⟨1102253, by rfl⟩ : syracuseStep 1469671 = 2204507) B2204507
theorem B1469695 : Blo 1468554 1469695 := bstep (se 1 (by rfl) ⟨1102271, by rfl⟩ : syracuseStep 1469695 = 2204543) B2204543
theorem B1469743 : Blo 1468554 1469743 := bstep (se 1 (by rfl) ⟨1102307, by rfl⟩ : syracuseStep 1469743 = 2204615) B2204615
theorem B1469887 : Blo 1468554 1469887 := bstep (se 1 (by rfl) ⟨1102415, by rfl⟩ : syracuseStep 1469887 = 2204831) B2204831
theorem B5582303 : Blo 1468554 5582303 := bstep (se 1 (by rfl) ⟨4186727, by rfl⟩ : syracuseStep 5582303 = 8373455) B8373455
theorem B1469983 : Blo 1468554 1469983 := bstep (se 1 (by rfl) ⟨1102487, by rfl⟩ : syracuseStep 1469983 = 2204975) B2204975
theorem B11914867 : Blo 1468554 11914867 := bstep (se 1 (by rfl) ⟨8936150, by rfl⟩ : syracuseStep 11914867 = 17872301) B17872301
theorem B1470111 : Blo 1468554 1470111 := bstep (se 1 (by rfl) ⟨1102583, by rfl⟩ : syracuseStep 1470111 = 2205167) B2205167
theorem B1470119 : Blo 1468554 1470119 := bstep (se 1 (by rfl) ⟨1102589, by rfl⟩ : syracuseStep 1470119 = 2205179) B2205179
theorem B1470143 : Blo 1468554 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B2789147 : Blo 1468554 2789147 := bstep (se 1 (by rfl) ⟨2091860, by rfl⟩ : syracuseStep 2789147 = 4183721) B4183721
theorem B1470239 : Blo 1468554 1470239 := bstep (se 1 (by rfl) ⟨1102679, by rfl⟩ : syracuseStep 1470239 = 2205359) B2205359
theorem B1470299 : Blo 1468554 1470299 := bstep (se 1 (by rfl) ⟨1102724, by rfl⟩ : syracuseStep 1470299 = 2205449) B2205449
theorem B1470319 : Blo 1468554 1470319 := bstep (se 1 (by rfl) ⟨1102739, by rfl⟩ : syracuseStep 1470319 = 2205479) B2205479
theorem B2789291 : Blo 1468554 2789291 := bstep (se 1 (by rfl) ⟨2091968, by rfl⟩ : syracuseStep 2789291 = 4183937) B4183937
theorem B6279083 : Blo 1468554 6279083 := bstep (se 1 (by rfl) ⟨4709312, by rfl⟩ : syracuseStep 6279083 = 9418625) B9418625
theorem B20107217 : Blo 1468554 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B3305447 : Blo 1468554 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B4182137 : Blo 1468554 4182137 := bstep (se 2 (by rfl) ⟨1568301, by rfl⟩ : syracuseStep 4182137 = 3136603) B3136603
theorem B2478343 : Blo 1468554 2478343 := bstep (se 1 (by rfl) ⟨1858757, by rfl⟩ : syracuseStep 2478343 = 3717515) B3717515
theorem B3305807 : Blo 1468554 3305807 := bstep (se 1 (by rfl) ⟨2479355, by rfl⟩ : syracuseStep 3305807 = 4958711) B4958711
theorem B5583275 : Blo 1468554 5583275 := bstep (se 1 (by rfl) ⟨4187456, by rfl⟩ : syracuseStep 5583275 = 8374913) B8374913
theorem B4182455 : Blo 1468554 4182455 := bstep (se 1 (by rfl) ⟨3136841, by rfl⟩ : syracuseStep 4182455 = 6273683) B6273683
theorem B1675711 : Blo 1468554 1675711 := bstep (se 1 (by rfl) ⟨1256783, by rfl⟩ : syracuseStep 1675711 = 2513567) B2513567
theorem B4182479 : Blo 1468554 4182479 := bstep (se 1 (by rfl) ⟨3136859, by rfl⟩ : syracuseStep 4182479 = 6273719) B6273719
theorem B4960763 : Blo 1468554 4960763 := bstep (se 1 (by rfl) ⟨3720572, by rfl⟩ : syracuseStep 4960763 = 7441145) B7441145
theorem B19100275 : Blo 1468554 19100275 := bstep (se 1 (by rfl) ⟨14325206, by rfl⟩ : syracuseStep 19100275 = 28650413) B28650413
theorem B2790119 : Blo 1468554 2790119 := bstep (se 1 (by rfl) ⟨2092589, by rfl⟩ : syracuseStep 2790119 = 4185179) B4185179
theorem B3306473 : Blo 1468554 3306473 := bstep (se 2 (by rfl) ⟨1239927, by rfl⟩ : syracuseStep 3306473 = 2479855) B2479855
theorem B4183265 : Blo 1468554 4183265 := bstep (se 2 (by rfl) ⟨1568724, by rfl⟩ : syracuseStep 4183265 = 3137449) B3137449
theorem B4183321 : Blo 1468554 4183321 := bstep (se 2 (by rfl) ⟨1568745, by rfl⟩ : syracuseStep 4183321 = 3137491) B3137491
theorem B5575999 : Blo 1468554 5575999 := bstep (se 1 (by rfl) ⟨4181999, by rfl⟩ : syracuseStep 5575999 = 8363999) B8363999
theorem B2479423 : Blo 1468554 2479423 := bstep (se 1 (by rfl) ⟨1859567, by rfl⟩ : syracuseStep 2479423 = 3719135) B3719135
theorem B2233807 : Blo 1468554 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B4961897 : Blo 1468554 4961897 := bstep (se 2 (by rfl) ⟨1860711, by rfl⟩ : syracuseStep 4961897 = 3721423) B3721423
theorem B19085129 : Blo 1468554 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B4708543 : Blo 1468554 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B7158241 : Blo 1468554 7158241 := bstep (se 2 (by rfl) ⟨2684340, by rfl⟩ : syracuseStep 7158241 = 5368681) B5368681
theorem B24148535 : Blo 1468554 24148535 := bstep (se 1 (by rfl) ⟨18111401, by rfl⟩ : syracuseStep 24148535 = 36222803) B36222803
theorem B7158401 : Blo 1468554 7158401 := bstep (se 2 (by rfl) ⟨2684400, by rfl⟩ : syracuseStep 7158401 = 5368801) B5368801
theorem B3308345 : Blo 1468554 3308345 := bstep (se 2 (by rfl) ⟨1240629, by rfl⟩ : syracuseStep 3308345 = 2481259) B2481259
theorem B11156615 : Blo 1468554 11156615 := bstep (se 1 (by rfl) ⟨8367461, by rfl⟩ : syracuseStep 11156615 = 16734923) B16734923
theorem B3308705 : Blo 1468554 3308705 := bstep (se 2 (by rfl) ⟨1240764, by rfl⟩ : syracuseStep 3308705 = 2481529) B2481529
theorem B2202875 : Blo 1468554 2202875 := bstep (se 1 (by rfl) ⟨1652156, by rfl⟩ : syracuseStep 2202875 = 3304313) B3304313
theorem B2203001 : Blo 1468554 2203001 := bstep (se 2 (by rfl) ⟨826125, by rfl⟩ : syracuseStep 2203001 = 1652251) B1652251
theorem B3350035 : Blo 1468554 3350035 := bstep (se 1 (by rfl) ⟨2512526, by rfl⟩ : syracuseStep 3350035 = 5025053) B5025053
theorem B2203241 : Blo 1468554 2203241 := bstep (se 2 (by rfl) ⟨826215, by rfl⟩ : syracuseStep 2203241 = 1652431) B1652431
theorem B107306795 : Blo 1468554 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B12550099 : Blo 1468554 12550099 := bstep (se 1 (by rfl) ⟨9412574, by rfl⟩ : syracuseStep 12550099 = 18825149) B18825149
theorem B2203871 : Blo 1468554 2203871 := bstep (se 1 (by rfl) ⟨1652903, by rfl⟩ : syracuseStep 2203871 = 3305807) B3305807
theorem B3719479 : Blo 1468554 3719479 := bstep (se 1 (by rfl) ⟨2789609, by rfl⟩ : syracuseStep 3719479 = 5579219) B5579219
theorem B1860079 : Blo 1468554 1860079 := bstep (se 1 (by rfl) ⟨1395059, by rfl⟩ : syracuseStep 1860079 = 2790119) B2790119
theorem B101868133 : Blo 1468554 101868133 := bstep (se 4 (by rfl) ⟨9550137, by rfl⟩ : syracuseStep 101868133 = 19100275) B19100275
theorem B9544321 : Blo 1468554 9544321 := bstep (se 2 (by rfl) ⟨3579120, by rfl⟩ : syracuseStep 9544321 = 7158241) B7158241
theorem B2204315 : Blo 1468554 2204315 := bstep (se 1 (by rfl) ⟨1653236, by rfl⟩ : syracuseStep 2204315 = 3306473) B3306473
theorem B7062643 : Blo 1468554 7062643 := bstep (se 1 (by rfl) ⟨5296982, by rfl⟩ : syracuseStep 7062643 = 10593965) B10593965
theorem B4244647 : Blo 1468554 4244647 := bstep (se 1 (by rfl) ⟨3183485, by rfl⟩ : syracuseStep 4244647 = 6366971) B6366971
theorem B12723419 : Blo 1468554 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B3016443415 : Blo 1468554 3016443415 := bstep (se 1 (by rfl) ⟨2262332561, by rfl⟩ : syracuseStep 3016443415 = 4524665123) B4524665123
theorem B2205563 : Blo 1468554 2205563 := bstep (se 1 (by rfl) ⟨1654172, by rfl⟩ : syracuseStep 2205563 = 3308345) B3308345
theorem B4466713 : Blo 1468554 4466713 := bstep (se 2 (by rfl) ⟨1675017, by rfl⟩ : syracuseStep 4466713 = 3350035) B3350035
theorem B2205803 : Blo 1468554 2205803 := bstep (se 1 (by rfl) ⟨1654352, by rfl⟩ : syracuseStep 2205803 = 3308705) B3308705
theorem B15886489 : Blo 1468554 15886489 := bstep (se 2 (by rfl) ⟨5957433, by rfl⟩ : syracuseStep 15886489 = 11914867) B11914867
theorem B1468583 : Blo 1468554 1468583 := bstep (se 1 (by rfl) ⟨1101437, by rfl⟩ : syracuseStep 1468583 = 2202875) B2202875
theorem B1468667 : Blo 1468554 1468667 := bstep (se 1 (by rfl) ⟨1101500, by rfl⟩ : syracuseStep 1468667 = 2203001) B2203001
theorem B3721535 : Blo 1468554 3721535 := bstep (se 1 (by rfl) ⟨2791151, by rfl⟩ : syracuseStep 3721535 = 5582303) B5582303
theorem B1468827 : Blo 1468554 1468827 := bstep (se 1 (by rfl) ⟨1101620, by rfl⟩ : syracuseStep 1468827 = 2203241) B2203241
theorem B11913637 : Blo 1468554 11913637 := bstep (se 4 (by rfl) ⟨1116903, by rfl⟩ : syracuseStep 11913637 = 2233807) B2233807
theorem B13404811 : Blo 1468554 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B2788091 : Blo 1468554 2788091 := bstep (se 1 (by rfl) ⟨2091068, by rfl⟩ : syracuseStep 2788091 = 4182137) B4182137
theorem B5581649 : Blo 1468554 5581649 := bstep (se 2 (by rfl) ⟨2093118, by rfl⟩ : syracuseStep 5581649 = 4186237) B4186237
theorem B6278057 : Blo 1468554 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B128789423 : Blo 1468554 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B18820025 : Blo 1468554 18820025 := bstep (se 2 (by rfl) ⟨7057509, by rfl⟩ : syracuseStep 18820025 = 14115019) B14115019
theorem B3722183 : Blo 1468554 3722183 := bstep (se 1 (by rfl) ⟨2791637, by rfl⟩ : syracuseStep 3722183 = 5583275) B5583275
theorem B2788319 : Blo 1468554 2788319 := bstep (se 1 (by rfl) ⟨2091239, by rfl⟩ : syracuseStep 2788319 = 4182479) B4182479
theorem B3304457 : Blo 1468554 3304457 := bstep (se 2 (by rfl) ⟨1239171, by rfl⟩ : syracuseStep 3304457 = 2478343) B2478343
theorem B17869967 : Blo 1468554 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B1469595 : Blo 1468554 1469595 := bstep (se 1 (by rfl) ⟨1102196, by rfl⟩ : syracuseStep 1469595 = 2204393) B2204393
theorem B1469607 : Blo 1468554 1469607 := bstep (se 1 (by rfl) ⟨1102205, by rfl⟩ : syracuseStep 1469607 = 2204411) B2204411
theorem B257584373 : Blo 1468554 257584373 := bstep (se 5 (by rfl) ⟨12074267, by rfl⟩ : syracuseStep 257584373 = 24148535) B24148535
theorem B25074208145 : Blo 1468554 25074208145 := bstep (se 2 (by rfl) ⟨9402828054, by rfl⟩ : syracuseStep 25074208145 = 18805656109) B18805656109
theorem B2788843 : Blo 1468554 2788843 := bstep (se 1 (by rfl) ⟨2091632, by rfl⟩ : syracuseStep 2788843 = 4183265) B4183265
theorem B1469951 : Blo 1468554 1469951 := bstep (se 1 (by rfl) ⟨1102463, by rfl⟩ : syracuseStep 1469951 = 2204927) B2204927
theorem B8367623 : Blo 1468554 8367623 := bstep (se 1 (by rfl) ⟨6275717, by rfl⟩ : syracuseStep 8367623 = 12551435) B12551435
theorem B28249721 : Blo 1468554 28249721 := bstep (se 2 (by rfl) ⟨10593645, by rfl⟩ : syracuseStep 28249721 = 21187291) B21187291
theorem B1470159 : Blo 1468554 1470159 := bstep (se 1 (by rfl) ⟨1102619, by rfl⟩ : syracuseStep 1470159 = 2205239) B2205239
theorem B11153213 : Blo 1468554 11153213 := bstep (se 3 (by rfl) ⟨2091227, by rfl⟩ : syracuseStep 11153213 = 4182455) B4182455
theorem B2092891 : Blo 1468554 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B1470399 : Blo 1468554 1470399 := bstep (se 1 (by rfl) ⟨1102799, by rfl⟩ : syracuseStep 1470399 = 2205599) B2205599
theorem B20099009 : Blo 1468554 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B3305627 : Blo 1468554 3305627 := bstep (se 1 (by rfl) ⟨2479220, by rfl⟩ : syracuseStep 3305627 = 4958441) B4958441
theorem B7434665 : Blo 1468554 7434665 := bstep (se 2 (by rfl) ⟨2787999, by rfl⟩ : syracuseStep 7434665 = 5575999) B5575999
theorem B3305897 : Blo 1468554 3305897 := bstep (se 2 (by rfl) ⟨1239711, by rfl⟩ : syracuseStep 3305897 = 2479423) B2479423
theorem B4772267 : Blo 1468554 4772267 := bstep (se 1 (by rfl) ⟨3579200, by rfl⟩ : syracuseStep 4772267 = 7158401) B7158401
theorem B71537863 : Blo 1468554 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B16733465 : Blo 1468554 16733465 := bstep (se 2 (by rfl) ⟨6275049, by rfl⟩ : syracuseStep 16733465 = 12550099) B12550099
theorem B81565223 : Blo 1468554 81565223 := bstep (se 1 (by rfl) ⟨61173917, by rfl⟩ : syracuseStep 81565223 = 122347835) B122347835
theorem B10196543 : Blo 1468554 10196543 := bstep (se 1 (by rfl) ⟨7647407, by rfl⟩ : syracuseStep 10196543 = 15294815) B15294815
theorem B3307175 : Blo 1468554 3307175 := bstep (se 1 (by rfl) ⟨2480381, by rfl⟩ : syracuseStep 3307175 = 4960763) B4960763
theorem B3307931 : Blo 1468554 3307931 := bstep (se 1 (by rfl) ⟨2480948, by rfl⟩ : syracuseStep 3307931 = 4961897) B4961897
theorem B4839905 : Blo 1468554 4839905 := bstep (se 2 (by rfl) ⟨1814964, by rfl⟩ : syracuseStep 4839905 = 3629929) B3629929
theorem B4709107 : Blo 1468554 4709107 := bstep (se 1 (by rfl) ⟨3531830, by rfl⟩ : syracuseStep 4709107 = 7063661) B7063661
theorem B2480935 : Blo 1468554 2480935 := bstep (se 1 (by rfl) ⟨1860701, by rfl⟩ : syracuseStep 2480935 = 3721403) B3721403
theorem B4709249 : Blo 1468554 4709249 := bstep (se 2 (by rfl) ⟨1765968, by rfl⟩ : syracuseStep 4709249 = 3531937) B3531937
theorem B17881991 : Blo 1468554 17881991 := bstep (se 1 (by rfl) ⟨13411493, by rfl⟩ : syracuseStep 17881991 = 26822987) B26822987
theorem B5577761 : Blo 1468554 5577761 := bstep (se 2 (by rfl) ⟨2091660, by rfl⟩ : syracuseStep 5577761 = 4183321) B4183321
theorem B2203007 : Blo 1468554 2203007 := bstep (se 1 (by rfl) ⟨1652255, by rfl⟩ : syracuseStep 2203007 = 3304511) B3304511
theorem B7437743 : Blo 1468554 7437743 := bstep (se 1 (by rfl) ⟨5578307, by rfl⟩ : syracuseStep 7437743 = 11156615) B11156615
theorem B1859051 : Blo 1468554 1859051 := bstep (se 1 (by rfl) ⟨1394288, by rfl⟩ : syracuseStep 1859051 = 2788577) B2788577
theorem B8937125 : Blo 1468554 8937125 := bstep (se 4 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 8937125 = 1675711) B1675711
theorem B1859431 : Blo 1468554 1859431 := bstep (se 1 (by rfl) ⟨1394573, by rfl⟩ : syracuseStep 1859431 = 2789147) B2789147
theorem B1859527 : Blo 1468554 1859527 := bstep (se 1 (by rfl) ⟨1394645, by rfl⟩ : syracuseStep 1859527 = 2789291) B2789291
theorem B4186055 : Blo 1468554 4186055 := bstep (se 1 (by rfl) ⟨3139541, by rfl⟩ : syracuseStep 4186055 = 6279083) B6279083
theorem B2203631 : Blo 1468554 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B5955617 : Blo 1468554 5955617 := bstep (se 2 (by rfl) ⟨2233356, by rfl⟩ : syracuseStep 5955617 = 4466713) B4466713
theorem B2203751 : Blo 1468554 2203751 := bstep (se 1 (by rfl) ⟨1652813, by rfl⟩ : syracuseStep 2203751 = 3305627) B3305627
theorem B4956443 : Blo 1468554 4956443 := bstep (se 1 (by rfl) ⟨3717332, by rfl⟩ : syracuseStep 4956443 = 7434665) B7434665
theorem B2203931 : Blo 1468554 2203931 := bstep (se 1 (by rfl) ⟨1652948, by rfl⟩ : syracuseStep 2203931 = 3305897) B3305897
theorem B15884849 : Blo 1468554 15884849 := bstep (se 2 (by rfl) ⟨5956818, by rfl⟩ : syracuseStep 15884849 = 11913637) B11913637
theorem B135824177 : Blo 1468554 135824177 := bstep (se 2 (by rfl) ⟨50934066, by rfl⟩ : syracuseStep 135824177 = 101868133) B101868133
theorem B2204783 : Blo 1468554 2204783 := bstep (se 1 (by rfl) ⟨1653587, by rfl⟩ : syracuseStep 2204783 = 3307175) B3307175
theorem B4957469 : Blo 1468554 4957469 := bstep (se 3 (by rfl) ⟨929525, by rfl⟩ : syracuseStep 4957469 = 1859051) B1859051
theorem B2205287 : Blo 1468554 2205287 := bstep (se 1 (by rfl) ⟨1653965, by rfl⟩ : syracuseStep 2205287 = 3307931) B3307931
theorem B3721099 : Blo 1468554 3721099 := bstep (se 1 (by rfl) ⟨2790824, by rfl⟩ : syracuseStep 3721099 = 5581649) B5581649
theorem B3139499 : Blo 1468554 3139499 := bstep (se 1 (by rfl) ⟨2354624, by rfl⟩ : syracuseStep 3139499 = 4709249) B4709249
theorem B11921327 : Blo 1468554 11921327 := bstep (se 1 (by rfl) ⟨8940995, by rfl⟩ : syracuseStep 11921327 = 17881991) B17881991
theorem B11913311 : Blo 1468554 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B171722915 : Blo 1468554 171722915 := bstep (se 1 (by rfl) ⟨128792186, by rfl⟩ : syracuseStep 171722915 = 257584373) B257584373
theorem B1468671 : Blo 1468554 1468671 := bstep (se 1 (by rfl) ⟨1101503, by rfl⟩ : syracuseStep 1468671 = 2203007) B2203007
theorem B16716138763 : Blo 1468554 16716138763 := bstep (se 1 (by rfl) ⟨12537104072, by rfl⟩ : syracuseStep 16716138763 = 25074208145) B25074208145
theorem B4958495 : Blo 1468554 4958495 := bstep (se 1 (by rfl) ⟨3718871, by rfl⟩ : syracuseStep 4958495 = 7437743) B7437743
theorem B5958083 : Blo 1468554 5958083 := bstep (se 1 (by rfl) ⟨4468562, by rfl⟩ : syracuseStep 5958083 = 8937125) B8937125
theorem B1469087 : Blo 1468554 1469087 := bstep (se 1 (by rfl) ⟨1101815, by rfl⟩ : syracuseStep 1469087 = 2203631) B2203631
theorem B1469247 : Blo 1468554 1469247 := bstep (se 1 (by rfl) ⟨1101935, by rfl⟩ : syracuseStep 1469247 = 2203871) B2203871
theorem B3181511 : Blo 1468554 3181511 := bstep (se 1 (by rfl) ⟨2386133, by rfl⟩ : syracuseStep 3181511 = 4772267) B4772267
theorem B4959305 : Blo 1468554 4959305 := bstep (se 2 (by rfl) ⟨1859739, by rfl⟩ : syracuseStep 4959305 = 3719479) B3719479
theorem B1469543 : Blo 1468554 1469543 := bstep (se 1 (by rfl) ⟨1102157, by rfl⟩ : syracuseStep 1469543 = 2204315) B2204315
theorem B12725761 : Blo 1468554 12725761 := bstep (se 2 (by rfl) ⟨4772160, by rfl⟩ : syracuseStep 12725761 = 9544321) B9544321
theorem B6278809 : Blo 1468554 6278809 := bstep (se 2 (by rfl) ⟨2354553, by rfl⟩ : syracuseStep 6278809 = 4709107) B4709107
theorem B1470375 : Blo 1468554 1470375 := bstep (se 1 (by rfl) ⟨1102781, by rfl⟩ : syracuseStep 1470375 = 2205563) B2205563
theorem B1470535 : Blo 1468554 1470535 := bstep (se 1 (by rfl) ⟨1102901, by rfl⟩ : syracuseStep 1470535 = 2205803) B2205803
theorem B9416857 : Blo 1468554 9416857 := bstep (se 2 (by rfl) ⟨3531321, by rfl⟩ : syracuseStep 9416857 = 7062643) B7062643
theorem B95383817 : Blo 1468554 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B12546683 : Blo 1468554 12546683 := bstep (se 1 (by rfl) ⟨9410012, by rfl⟩ : syracuseStep 12546683 = 18820025) B18820025
theorem B4021924553 : Blo 1468554 4021924553 := bstep (se 2 (by rfl) ⟨1508221707, by rfl⟩ : syracuseStep 4021924553 = 3016443415) B3016443415
theorem B2790521 : Blo 1468554 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B2479241 : Blo 1468554 2479241 := bstep (se 2 (by rfl) ⟨929715, by rfl⟩ : syracuseStep 2479241 = 1859431) B1859431
theorem B7435475 : Blo 1468554 7435475 := bstep (se 1 (by rfl) ⟨5576606, by rfl⟩ : syracuseStep 7435475 = 11153213) B11153213
theorem B2479369 : Blo 1468554 2479369 := bstep (se 2 (by rfl) ⟨929763, by rfl⟩ : syracuseStep 2479369 = 1859527) B1859527
theorem B13399339 : Blo 1468554 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B2790703 : Blo 1468554 2790703 := bstep (se 1 (by rfl) ⟨2093027, by rfl⟩ : syracuseStep 2790703 = 4186055) B4186055
theorem B21181985 : Blo 1468554 21181985 := bstep (se 2 (by rfl) ⟨7943244, by rfl⟩ : syracuseStep 21181985 = 15886489) B15886489
theorem B870029045 : Blo 1468554 870029045 := bstep (se 5 (by rfl) ⟨40782611, by rfl⟩ : syracuseStep 870029045 = 81565223) B81565223
theorem B33929117 : Blo 1468554 33929117 := bstep (se 3 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 33929117 = 12723419) B12723419
theorem B2480105 : Blo 1468554 2480105 := bstep (se 2 (by rfl) ⟨930039, by rfl⟩ : syracuseStep 2480105 = 1860079) B1860079
theorem B17873081 : Blo 1468554 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B11155643 : Blo 1468554 11155643 := bstep (se 1 (by rfl) ⟨8366732, by rfl⟩ : syracuseStep 11155643 = 16733465) B16733465
theorem B6797695 : Blo 1468554 6797695 := bstep (se 1 (by rfl) ⟨5098271, by rfl⟩ : syracuseStep 6797695 = 10196543) B10196543
theorem B3307913 : Blo 1468554 3307913 := bstep (se 2 (by rfl) ⟨1240467, by rfl⟩ : syracuseStep 3307913 = 2480935) B2480935
theorem B2481023 : Blo 1468554 2481023 := bstep (se 1 (by rfl) ⟨1860767, by rfl⟩ : syracuseStep 2481023 = 3721535) B3721535
theorem B5659529 : Blo 1468554 5659529 := bstep (se 2 (by rfl) ⟨2122323, by rfl⟩ : syracuseStep 5659529 = 4244647) B4244647
theorem B3226603 : Blo 1468554 3226603 := bstep (se 1 (by rfl) ⟨2419952, by rfl⟩ : syracuseStep 3226603 = 4839905) B4839905
theorem B1858727 : Blo 1468554 1858727 := bstep (se 1 (by rfl) ⟨1394045, by rfl⟩ : syracuseStep 1858727 = 2788091) B2788091
theorem B4185371 : Blo 1468554 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B85859615 : Blo 1468554 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B2481455 : Blo 1468554 2481455 := bstep (se 1 (by rfl) ⟨1861091, by rfl⟩ : syracuseStep 2481455 = 3722183) B3722183
theorem B3718457 : Blo 1468554 3718457 := bstep (se 2 (by rfl) ⟨1394421, by rfl⟩ : syracuseStep 3718457 = 2788843) B2788843
theorem B1858879 : Blo 1468554 1858879 := bstep (se 1 (by rfl) ⟨1394159, by rfl⟩ : syracuseStep 1858879 = 2788319) B2788319
theorem B2202971 : Blo 1468554 2202971 := bstep (se 1 (by rfl) ⟨1652228, by rfl⟩ : syracuseStep 2202971 = 3304457) B3304457
theorem B3718507 : Blo 1468554 3718507 := bstep (se 1 (by rfl) ⟨2788880, by rfl⟩ : syracuseStep 3718507 = 5577761) B5577761
theorem B5578415 : Blo 1468554 5578415 := bstep (se 1 (by rfl) ⟨4183811, by rfl⟩ : syracuseStep 5578415 = 8367623) B8367623
theorem B18833147 : Blo 1468554 18833147 := bstep (se 1 (by rfl) ⟨14124860, by rfl⟩ : syracuseStep 18833147 = 28249721) B28249721
theorem B8364455 : Blo 1468554 8364455 := bstep (se 1 (by rfl) ⟨6273341, by rfl⟩ : syracuseStep 8364455 = 12546683) B12546683
theorem B4956605 : Blo 1468554 4956605 := bstep (se 3 (by rfl) ⟨929363, by rfl⟩ : syracuseStep 4956605 = 1858727) B1858727
theorem B2681283035 : Blo 1468554 2681283035 := bstep (se 1 (by rfl) ⟨2010962276, by rfl⟩ : syracuseStep 2681283035 = 4021924553) B4021924553
theorem B1860347 : Blo 1468554 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B4956983 : Blo 1468554 4956983 := bstep (se 1 (by rfl) ⟨3717737, by rfl⟩ : syracuseStep 4956983 = 7435475) B7435475
theorem B580019363 : Blo 1468554 580019363 := bstep (se 1 (by rfl) ⟨435014522, by rfl⟩ : syracuseStep 580019363 = 870029045) B870029045
theorem B22619411 : Blo 1468554 22619411 := bstep (se 1 (by rfl) ⟨16964558, by rfl⟩ : syracuseStep 22619411 = 33929117) B33929117
theorem B7947551 : Blo 1468554 7947551 := bstep (se 1 (by rfl) ⟨5960663, by rfl⟩ : syracuseStep 7947551 = 11921327) B11921327
theorem B4302137 : Blo 1468554 4302137 := bstep (se 2 (by rfl) ⟨1613301, by rfl⟩ : syracuseStep 4302137 = 3226603) B3226603
theorem B2205275 : Blo 1468554 2205275 := bstep (se 1 (by rfl) ⟨1653956, by rfl⟩ : syracuseStep 2205275 = 3307913) B3307913
theorem B3720937 : Blo 1468554 3720937 := bstep (se 2 (by rfl) ⟨1395351, by rfl⟩ : syracuseStep 3720937 = 2790703) B2790703
theorem B4958009 : Blo 1468554 4958009 := bstep (se 2 (by rfl) ⟨1859253, by rfl⟩ : syracuseStep 4958009 = 3718507) B3718507
theorem B16967681 : Blo 1468554 16967681 := bstep (se 2 (by rfl) ⟨6362880, by rfl⟩ : syracuseStep 16967681 = 12725761) B12725761
theorem B57239743 : Blo 1468554 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B1468647 : Blo 1468554 1468647 := bstep (se 1 (by rfl) ⟨1101485, by rfl⟩ : syracuseStep 1468647 = 2202971) B2202971
theorem B15092077 : Blo 1468554 15092077 := bstep (se 3 (by rfl) ⟨2829764, by rfl⟩ : syracuseStep 15092077 = 5659529) B5659529
theorem B1469167 : Blo 1468554 1469167 := bstep (se 1 (by rfl) ⟨1101875, by rfl⟩ : syracuseStep 1469167 = 2203751) B2203751
theorem B63589211 : Blo 1468554 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B3304295 : Blo 1468554 3304295 := bstep (se 1 (by rfl) ⟨2478221, by rfl⟩ : syracuseStep 3304295 = 4956443) B4956443
theorem B1469287 : Blo 1468554 1469287 := bstep (se 1 (by rfl) ⟨1101965, by rfl⟩ : syracuseStep 1469287 = 2203931) B2203931
theorem B9063593 : Blo 1468554 9063593 := bstep (se 2 (by rfl) ⟨3398847, by rfl⟩ : syracuseStep 9063593 = 6797695) B6797695
theorem B90549451 : Blo 1468554 90549451 := bstep (se 1 (by rfl) ⟨67912088, by rfl⟩ : syracuseStep 90549451 = 135824177) B135824177
theorem B11160989 : Blo 1468554 11160989 := bstep (se 3 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 11160989 = 4185371) B4185371
theorem B1469855 : Blo 1468554 1469855 := bstep (se 1 (by rfl) ⟨1102391, by rfl⟩ : syracuseStep 1469855 = 2204783) B2204783
theorem B3304979 : Blo 1468554 3304979 := bstep (se 1 (by rfl) ⟨2478734, by rfl⟩ : syracuseStep 3304979 = 4957469) B4957469
theorem B1470191 : Blo 1468554 1470191 := bstep (se 1 (by rfl) ⟨1102643, by rfl⟩ : syracuseStep 1470191 = 2205287) B2205287
theorem B15888221 : Blo 1468554 15888221 := bstep (se 3 (by rfl) ⟨2979041, by rfl⟩ : syracuseStep 15888221 = 5958083) B5958083
theorem B7942207 : Blo 1468554 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B11915387 : Blo 1468554 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B3305663 : Blo 1468554 3305663 := bstep (se 1 (by rfl) ⟨2479247, by rfl⟩ : syracuseStep 3305663 = 4958495) B4958495
theorem B3305825 : Blo 1468554 3305825 := bstep (se 2 (by rfl) ⟨1239684, by rfl⟩ : syracuseStep 3305825 = 2479369) B2479369
theorem B2478505 : Blo 1468554 2478505 := bstep (se 2 (by rfl) ⟨929439, by rfl⟩ : syracuseStep 2478505 = 1858879) B1858879
theorem B3306203 : Blo 1468554 3306203 := bstep (se 1 (by rfl) ⟨2479652, by rfl⟩ : syracuseStep 3306203 = 4959305) B4959305
theorem B2478971 : Blo 1468554 2478971 := bstep (se 1 (by rfl) ⟨1859228, by rfl⟩ : syracuseStep 2478971 = 3718457) B3718457
theorem B12555431 : Blo 1468554 12555431 := bstep (se 1 (by rfl) ⟨9416573, by rfl⟩ : syracuseStep 12555431 = 18833147) B18833147
theorem B4961465 : Blo 1468554 4961465 := bstep (se 2 (by rfl) ⟨1860549, by rfl⟩ : syracuseStep 4961465 = 3721099) B3721099
theorem B15881645 : Blo 1468554 15881645 := bstep (se 3 (by rfl) ⟨2977808, by rfl⟩ : syracuseStep 15881645 = 5955617) B5955617
theorem B12555809 : Blo 1468554 12555809 := bstep (se 2 (by rfl) ⟨4708428, by rfl⟩ : syracuseStep 12555809 = 9416857) B9416857
theorem B22288185017 : Blo 1468554 22288185017 := bstep (se 2 (by rfl) ⟨8358069381, by rfl⟩ : syracuseStep 22288185017 = 16716138763) B16716138763
theorem B10589899 : Blo 1468554 10589899 := bstep (se 1 (by rfl) ⟨7942424, by rfl⟩ : syracuseStep 10589899 = 15884849) B15884849
theorem B1652827 : Blo 1468554 1652827 := bstep (se 1 (by rfl) ⟨1239620, by rfl⟩ : syracuseStep 1652827 = 2479241) B2479241
theorem B14121323 : Blo 1468554 14121323 := bstep (se 1 (by rfl) ⟨10590992, by rfl⟩ : syracuseStep 14121323 = 21181985) B21181985
theorem B1653403 : Blo 1468554 1653403 := bstep (se 1 (by rfl) ⟨1240052, by rfl⟩ : syracuseStep 1653403 = 2480105) B2480105
theorem B114481943 : Blo 1468554 114481943 := bstep (se 1 (by rfl) ⟨85861457, by rfl⟩ : syracuseStep 114481943 = 171722915) B171722915
theorem B7437095 : Blo 1468554 7437095 := bstep (se 1 (by rfl) ⟨5577821, by rfl⟩ : syracuseStep 7437095 = 11155643) B11155643
theorem B17865785 : Blo 1468554 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B1654015 : Blo 1468554 1654015 := bstep (se 1 (by rfl) ⟨1240511, by rfl⟩ : syracuseStep 1654015 = 2481023) B2481023
theorem B2121007 : Blo 1468554 2121007 := bstep (se 1 (by rfl) ⟨1590755, by rfl⟩ : syracuseStep 2121007 = 3181511) B3181511
theorem B1654303 : Blo 1468554 1654303 := bstep (se 1 (by rfl) ⟨1240727, by rfl⟩ : syracuseStep 1654303 = 2481455) B2481455
theorem B8371745 : Blo 1468554 8371745 := bstep (se 2 (by rfl) ⟨3139404, by rfl⟩ : syracuseStep 8371745 = 6278809) B6278809
theorem B8371997 : Blo 1468554 8371997 := bstep (se 3 (by rfl) ⟨1569749, by rfl⟩ : syracuseStep 8371997 = 3139499) B3139499
theorem B3718943 : Blo 1468554 3718943 := bstep (se 1 (by rfl) ⟨2789207, by rfl⟩ : syracuseStep 3718943 = 5578415) B5578415
theorem B2203769 : Blo 1468554 2203769 := bstep (se 2 (by rfl) ⟨826413, by rfl⟩ : syracuseStep 2203769 = 1652827) B1652827
theorem B2203775 : Blo 1468554 2203775 := bstep (se 1 (by rfl) ⟨1652831, by rfl⟩ : syracuseStep 2203775 = 3305663) B3305663
theorem B2203883 : Blo 1468554 2203883 := bstep (se 1 (by rfl) ⟨1652912, by rfl⟩ : syracuseStep 2203883 = 3305825) B3305825
theorem B2204135 : Blo 1468554 2204135 := bstep (se 1 (by rfl) ⟨1653101, by rfl⟩ : syracuseStep 2204135 = 3306203) B3306203
theorem B386679575 : Blo 1468554 386679575 := bstep (se 1 (by rfl) ⟨290009681, by rfl⟩ : syracuseStep 386679575 = 580019363) B580019363
theorem B2204537 : Blo 1468554 2204537 := bstep (se 2 (by rfl) ⟨826701, by rfl⟩ : syracuseStep 2204537 = 1653403) B1653403
theorem B2868091 : Blo 1468554 2868091 := bstep (se 1 (by rfl) ⟨2151068, by rfl⟩ : syracuseStep 2868091 = 4302137) B4302137
theorem B14858790011 : Blo 1468554 14858790011 := bstep (se 1 (by rfl) ⟨11144092508, by rfl⟩ : syracuseStep 14858790011 = 22288185017) B22288185017
theorem B9414215 : Blo 1468554 9414215 := bstep (se 1 (by rfl) ⟨7060661, by rfl⟩ : syracuseStep 9414215 = 14121323) B14121323
theorem B2205353 : Blo 1468554 2205353 := bstep (se 2 (by rfl) ⟨827007, by rfl⟩ : syracuseStep 2205353 = 1654015) B1654015
theorem B2828009 : Blo 1468554 2828009 := bstep (se 2 (by rfl) ⟨1060503, by rfl⟩ : syracuseStep 2828009 = 2121007) B2121007
theorem B4958063 : Blo 1468554 4958063 := bstep (se 1 (by rfl) ⟨3718547, by rfl⟩ : syracuseStep 4958063 = 7437095) B7437095
theorem B2205737 : Blo 1468554 2205737 := bstep (se 2 (by rfl) ⟨827151, by rfl⟩ : syracuseStep 2205737 = 1654303) B1654303
theorem B7440659 : Blo 1468554 7440659 := bstep (se 1 (by rfl) ⟨5580494, by rfl⟩ : syracuseStep 7440659 = 11160989) B11160989
theorem B5581163 : Blo 1468554 5581163 := bstep (se 1 (by rfl) ⟨4185872, by rfl⟩ : syracuseStep 5581163 = 8371745) B8371745
theorem B5581331 : Blo 1468554 5581331 := bstep (se 1 (by rfl) ⟨4185998, by rfl⟩ : syracuseStep 5581331 = 8371997) B8371997
theorem B76319657 : Blo 1468554 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B3304403 : Blo 1468554 3304403 := bstep (se 1 (by rfl) ⟨2478302, by rfl⟩ : syracuseStep 3304403 = 4956605) B4956605
theorem B1787522023 : Blo 1468554 1787522023 := bstep (se 1 (by rfl) ⟨1340641517, by rfl⟩ : syracuseStep 1787522023 = 2681283035) B2681283035
theorem B20122769 : Blo 1468554 20122769 := bstep (se 2 (by rfl) ⟨7546038, by rfl⟩ : syracuseStep 20122769 = 15092077) B15092077
theorem B3304655 : Blo 1468554 3304655 := bstep (se 1 (by rfl) ⟨2478491, by rfl⟩ : syracuseStep 3304655 = 4956983) B4956983
theorem B3304673 : Blo 1468554 3304673 := bstep (se 2 (by rfl) ⟨1239252, by rfl⟩ : syracuseStep 3304673 = 2478505) B2478505
theorem B10587763 : Blo 1468554 10587763 := bstep (se 1 (by rfl) ⟨7940822, by rfl⟩ : syracuseStep 10587763 = 15881645) B15881645
theorem B1470183 : Blo 1468554 1470183 := bstep (se 1 (by rfl) ⟨1102637, by rfl⟩ : syracuseStep 1470183 = 2205275) B2205275
theorem B3305339 : Blo 1468554 3305339 := bstep (se 1 (by rfl) ⟨2479004, by rfl⟩ : syracuseStep 3305339 = 4958009) B4958009
theorem B76321295 : Blo 1468554 76321295 := bstep (se 1 (by rfl) ⟨57240971, by rfl⟩ : syracuseStep 76321295 = 114481943) B114481943
theorem B4960925 : Blo 1468554 4960925 := bstep (se 3 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 4960925 = 1860347) B1860347
theorem B6042395 : Blo 1468554 6042395 := bstep (se 1 (by rfl) ⟨4531796, by rfl⟩ : syracuseStep 6042395 = 9063593) B9063593
theorem B14119865 : Blo 1468554 14119865 := bstep (se 2 (by rfl) ⟨5294949, by rfl⟩ : syracuseStep 14119865 = 10589899) B10589899
theorem B4961249 : Blo 1468554 4961249 := bstep (se 2 (by rfl) ⟨1860468, by rfl⟩ : syracuseStep 4961249 = 3720937) B3720937
theorem B2479295 : Blo 1468554 2479295 := bstep (se 1 (by rfl) ⟨1859471, by rfl⟩ : syracuseStep 2479295 = 3718943) B3718943
theorem B7943591 : Blo 1468554 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B10589609 : Blo 1468554 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B5576303 : Blo 1468554 5576303 := bstep (se 1 (by rfl) ⟨4182227, by rfl⟩ : syracuseStep 5576303 = 8364455) B8364455
theorem B1652647 : Blo 1468554 1652647 := bstep (se 1 (by rfl) ⟨1239485, by rfl⟩ : syracuseStep 1652647 = 2478971) B2478971
theorem B8370287 : Blo 1468554 8370287 := bstep (se 1 (by rfl) ⟨6277715, by rfl⟩ : syracuseStep 8370287 = 12555431) B12555431
theorem B3307643 : Blo 1468554 3307643 := bstep (se 1 (by rfl) ⟨2480732, by rfl⟩ : syracuseStep 3307643 = 4961465) B4961465
theorem B15079607 : Blo 1468554 15079607 := bstep (se 1 (by rfl) ⟨11309705, by rfl⟩ : syracuseStep 15079607 = 22619411) B22619411
theorem B5298367 : Blo 1468554 5298367 := bstep (se 1 (by rfl) ⟨3973775, by rfl⟩ : syracuseStep 5298367 = 7947551) B7947551
theorem B8370539 : Blo 1468554 8370539 := bstep (se 1 (by rfl) ⟨6277904, by rfl⟩ : syracuseStep 8370539 = 12555809) B12555809
theorem B11311787 : Blo 1468554 11311787 := bstep (se 1 (by rfl) ⟨8483840, by rfl⟩ : syracuseStep 11311787 = 16967681) B16967681
theorem B120732601 : Blo 1468554 120732601 := bstep (se 2 (by rfl) ⟨45274725, by rfl⟩ : syracuseStep 120732601 = 90549451) B90549451
theorem B42392807 : Blo 1468554 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B2202863 : Blo 1468554 2202863 := bstep (se 1 (by rfl) ⟨1652147, by rfl⟩ : syracuseStep 2202863 = 3304295) B3304295
theorem B11910523 : Blo 1468554 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B2203319 : Blo 1468554 2203319 := bstep (se 1 (by rfl) ⟨1652489, by rfl⟩ : syracuseStep 2203319 = 3304979) B3304979
theorem B10592147 : Blo 1468554 10592147 := bstep (se 1 (by rfl) ⟨7944110, by rfl⟩ : syracuseStep 10592147 = 15888221) B15888221
theorem B50880863 : Blo 1468554 50880863 := bstep (se 1 (by rfl) ⟨38160647, by rfl⟩ : syracuseStep 50880863 = 76321295) B76321295
theorem B257786383 : Blo 1468554 257786383 := bstep (se 1 (by rfl) ⟨193339787, by rfl⟩ : syracuseStep 257786383 = 386679575) B386679575
theorem B9413243 : Blo 1468554 9413243 := bstep (se 1 (by rfl) ⟨7059932, by rfl⟩ : syracuseStep 9413243 = 14119865) B14119865
theorem B6276143 : Blo 1468554 6276143 := bstep (se 1 (by rfl) ⟨4707107, by rfl⟩ : syracuseStep 6276143 = 9414215) B9414215
theorem B1885339 : Blo 1468554 1885339 := bstep (se 1 (by rfl) ⟨1414004, by rfl⟩ : syracuseStep 1885339 = 2828009) B2828009
theorem B5580191 : Blo 1468554 5580191 := bstep (se 1 (by rfl) ⟨4185143, by rfl⟩ : syracuseStep 5580191 = 8370287) B8370287
theorem B2205095 : Blo 1468554 2205095 := bstep (se 1 (by rfl) ⟨1653821, by rfl⟩ : syracuseStep 2205095 = 3307643) B3307643
theorem B10053071 : Blo 1468554 10053071 := bstep (se 1 (by rfl) ⟨7539803, by rfl⟩ : syracuseStep 10053071 = 15079607) B15079607
theorem B5580359 : Blo 1468554 5580359 := bstep (se 1 (by rfl) ⟨4185269, by rfl⟩ : syracuseStep 5580359 = 8370539) B8370539
theorem B3720775 : Blo 1468554 3720775 := bstep (se 1 (by rfl) ⟨2790581, by rfl⟩ : syracuseStep 3720775 = 5581163) B5581163
theorem B3720887 : Blo 1468554 3720887 := bstep (se 1 (by rfl) ⟨2790665, by rfl⟩ : syracuseStep 3720887 = 5581331) B5581331
theorem B14117017 : Blo 1468554 14117017 := bstep (se 2 (by rfl) ⟨5293881, by rfl⟩ : syracuseStep 14117017 = 10587763) B10587763
theorem B1468575 : Blo 1468554 1468575 := bstep (se 1 (by rfl) ⟨1101431, by rfl⟩ : syracuseStep 1468575 = 2202863) B2202863
theorem B1468879 : Blo 1468554 1468879 := bstep (se 1 (by rfl) ⟨1101659, by rfl⟩ : syracuseStep 1468879 = 2203319) B2203319
theorem B9533450789 : Blo 1468554 9533450789 := bstep (se 4 (by rfl) ⟨893761011, by rfl⟩ : syracuseStep 9533450789 = 1787522023) B1787522023
theorem B1469179 : Blo 1468554 1469179 := bstep (se 1 (by rfl) ⟨1101884, by rfl⟩ : syracuseStep 1469179 = 2203769) B2203769
theorem B1469183 : Blo 1468554 1469183 := bstep (se 1 (by rfl) ⟨1101887, by rfl⟩ : syracuseStep 1469183 = 2203775) B2203775
theorem B1469255 : Blo 1468554 1469255 := bstep (se 1 (by rfl) ⟨1101941, by rfl⟩ : syracuseStep 1469255 = 2203883) B2203883
theorem B7064489 : Blo 1468554 7064489 := bstep (se 2 (by rfl) ⟨2649183, by rfl⟩ : syracuseStep 7064489 = 5298367) B5298367
theorem B1469423 : Blo 1468554 1469423 := bstep (se 1 (by rfl) ⟨1102067, by rfl⟩ : syracuseStep 1469423 = 2204135) B2204135
theorem B1469691 : Blo 1468554 1469691 := bstep (se 1 (by rfl) ⟨1102268, by rfl⟩ : syracuseStep 1469691 = 2204537) B2204537
theorem B9905860007 : Blo 1468554 9905860007 := bstep (se 1 (by rfl) ⟨7429395005, by rfl⟩ : syracuseStep 9905860007 = 14858790011) B14858790011
theorem B5295727 : Blo 1468554 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B1470235 : Blo 1468554 1470235 := bstep (se 1 (by rfl) ⟨1102676, by rfl⟩ : syracuseStep 1470235 = 2205353) B2205353
theorem B3305375 : Blo 1468554 3305375 := bstep (se 1 (by rfl) ⟨2479031, by rfl⟩ : syracuseStep 3305375 = 4958063) B4958063
theorem B160976801 : Blo 1468554 160976801 := bstep (se 2 (by rfl) ⟨60366300, by rfl⟩ : syracuseStep 160976801 = 120732601) B120732601
theorem B1470491 : Blo 1468554 1470491 := bstep (se 1 (by rfl) ⟨1102868, by rfl⟩ : syracuseStep 1470491 = 2205737) B2205737
theorem B4960439 : Blo 1468554 4960439 := bstep (se 1 (by rfl) ⟨3720329, by rfl⟩ : syracuseStep 4960439 = 7440659) B7440659
theorem B7541191 : Blo 1468554 7541191 := bstep (se 1 (by rfl) ⟨5655893, by rfl⟩ : syracuseStep 7541191 = 11311787) B11311787
theorem B15880697 : Blo 1468554 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B13415179 : Blo 1468554 13415179 := bstep (se 1 (by rfl) ⟨10061384, by rfl⟩ : syracuseStep 13415179 = 20122769) B20122769
theorem B3307283 : Blo 1468554 3307283 := bstep (se 1 (by rfl) ⟨2480462, by rfl⟩ : syracuseStep 3307283 = 4960925) B4960925
theorem B3307499 : Blo 1468554 3307499 := bstep (se 1 (by rfl) ⟨2480624, by rfl⟩ : syracuseStep 3307499 = 4961249) B4961249
theorem B1652863 : Blo 1468554 1652863 := bstep (se 1 (by rfl) ⟨1239647, by rfl⟩ : syracuseStep 1652863 = 2479295) B2479295
theorem B7059739 : Blo 1468554 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B3717535 : Blo 1468554 3717535 := bstep (se 1 (by rfl) ⟨2788151, by rfl⟩ : syracuseStep 3717535 = 5576303) B5576303
theorem B50879771 : Blo 1468554 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B2202935 : Blo 1468554 2202935 := bstep (se 1 (by rfl) ⟨1652201, by rfl⟩ : syracuseStep 2202935 = 3304403) B3304403
theorem B16113053 : Blo 1468554 16113053 := bstep (se 3 (by rfl) ⟨3021197, by rfl⟩ : syracuseStep 16113053 = 6042395) B6042395
theorem B2203103 : Blo 1468554 2203103 := bstep (se 1 (by rfl) ⟨1652327, by rfl⟩ : syracuseStep 2203103 = 3304655) B3304655
theorem B2203115 : Blo 1468554 2203115 := bstep (se 1 (by rfl) ⟨1652336, by rfl⟩ : syracuseStep 2203115 = 3304673) B3304673
theorem B28261871 : Blo 1468554 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B2203529 : Blo 1468554 2203529 := bstep (se 2 (by rfl) ⟨826323, by rfl⟩ : syracuseStep 2203529 = 1652647) B1652647
theorem B61185941 : Blo 1468554 61185941 := bstep (se 6 (by rfl) ⟨1434045, by rfl⟩ : syracuseStep 61185941 = 2868091) B2868091
theorem B2203559 : Blo 1468554 2203559 := bstep (se 1 (by rfl) ⟨1652669, by rfl⟩ : syracuseStep 2203559 = 3305339) B3305339
theorem B7061431 : Blo 1468554 7061431 := bstep (se 1 (by rfl) ⟨5296073, by rfl⟩ : syracuseStep 7061431 = 10592147) B10592147
theorem B16736381 : Blo 1468554 16736381 := bstep (se 3 (by rfl) ⟨3138071, by rfl⟩ : syracuseStep 16736381 = 6276143) B6276143
theorem B2203817 : Blo 1468554 2203817 := bstep (se 2 (by rfl) ⟨826431, by rfl⟩ : syracuseStep 2203817 = 1652863) B1652863
theorem B9412985 : Blo 1468554 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B6275495 : Blo 1468554 6275495 := bstep (se 1 (by rfl) ⟨4706621, by rfl⟩ : syracuseStep 6275495 = 9413243) B9413243
theorem B4956713 : Blo 1468554 4956713 := bstep (se 2 (by rfl) ⟨1858767, by rfl⟩ : syracuseStep 4956713 = 3717535) B3717535
theorem B3720127 : Blo 1468554 3720127 := bstep (se 1 (by rfl) ⟨2790095, by rfl⟩ : syracuseStep 3720127 = 5580191) B5580191
theorem B6702047 : Blo 1468554 6702047 := bstep (se 1 (by rfl) ⟨5026535, by rfl⟩ : syracuseStep 6702047 = 10053071) B10053071
theorem B3720239 : Blo 1468554 3720239 := bstep (se 1 (by rfl) ⟨2790179, by rfl⟩ : syracuseStep 3720239 = 5580359) B5580359
theorem B42968141 : Blo 1468554 42968141 := bstep (se 3 (by rfl) ⟨8056526, by rfl⟩ : syracuseStep 42968141 = 16113053) B16113053
theorem B2204855 : Blo 1468554 2204855 := bstep (se 1 (by rfl) ⟨1653641, by rfl⟩ : syracuseStep 2204855 = 3307283) B3307283
theorem B2204999 : Blo 1468554 2204999 := bstep (se 1 (by rfl) ⟨1653749, by rfl⟩ : syracuseStep 2204999 = 3307499) B3307499
theorem B6355633859 : Blo 1468554 6355633859 := bstep (se 1 (by rfl) ⟨4766725394, by rfl⟩ : syracuseStep 6355633859 = 9533450789) B9533450789
theorem B1468623 : Blo 1468554 1468623 := bstep (se 1 (by rfl) ⟨1101467, by rfl⟩ : syracuseStep 1468623 = 2202935) B2202935
theorem B1468735 : Blo 1468554 1468735 := bstep (se 1 (by rfl) ⟨1101551, by rfl⟩ : syracuseStep 1468735 = 2203103) B2203103
theorem B1468743 : Blo 1468554 1468743 := bstep (se 1 (by rfl) ⟨1101557, by rfl⟩ : syracuseStep 1468743 = 2203115) B2203115
theorem B9415241 : Blo 1468554 9415241 := bstep (se 2 (by rfl) ⟨3530715, by rfl⟩ : syracuseStep 9415241 = 7061431) B7061431
theorem B1469019 : Blo 1468554 1469019 := bstep (se 1 (by rfl) ⟨1101764, by rfl⟩ : syracuseStep 1469019 = 2203529) B2203529
theorem B40790627 : Blo 1468554 40790627 := bstep (se 1 (by rfl) ⟨30592970, by rfl⟩ : syracuseStep 40790627 = 61185941) B61185941
theorem B107317867 : Blo 1468554 107317867 := bstep (se 1 (by rfl) ⟨80488400, by rfl⟩ : syracuseStep 107317867 = 160976801) B160976801
theorem B1469039 : Blo 1468554 1469039 := bstep (se 1 (by rfl) ⟨1101779, by rfl⟩ : syracuseStep 1469039 = 2203559) B2203559
theorem B10587131 : Blo 1468554 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B10054921 : Blo 1468554 10054921 := bstep (se 2 (by rfl) ⟨3770595, by rfl⟩ : syracuseStep 10054921 = 7541191) B7541191
theorem B343715177 : Blo 1468554 343715177 := bstep (se 2 (by rfl) ⟨128893191, by rfl⟩ : syracuseStep 343715177 = 257786383) B257786383
theorem B10055141 : Blo 1468554 10055141 := bstep (se 4 (by rfl) ⟨942669, by rfl⟩ : syracuseStep 10055141 = 1885339) B1885339
theorem B1470063 : Blo 1468554 1470063 := bstep (se 1 (by rfl) ⟨1102547, by rfl⟩ : syracuseStep 1470063 = 2205095) B2205095
theorem B17886905 : Blo 1468554 17886905 := bstep (se 2 (by rfl) ⟨6707589, by rfl⟩ : syracuseStep 17886905 = 13415179) B13415179
theorem B4961033 : Blo 1468554 4961033 := bstep (se 2 (by rfl) ⟨1860387, by rfl⟩ : syracuseStep 4961033 = 3720775) B3720775
theorem B33919847 : Blo 1468554 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B3306959 : Blo 1468554 3306959 := bstep (se 1 (by rfl) ⟨2480219, by rfl⟩ : syracuseStep 3306959 = 4960439) B4960439
theorem B18822689 : Blo 1468554 18822689 := bstep (se 2 (by rfl) ⟨7058508, by rfl⟩ : syracuseStep 18822689 = 14117017) B14117017
theorem B33920575 : Blo 1468554 33920575 := bstep (se 1 (by rfl) ⟨25440431, by rfl⟩ : syracuseStep 33920575 = 50880863) B50880863
theorem B2480591 : Blo 1468554 2480591 := bstep (se 1 (by rfl) ⟨1860443, by rfl⟩ : syracuseStep 2480591 = 3720887) B3720887
theorem B4709659 : Blo 1468554 4709659 := bstep (se 1 (by rfl) ⟨3532244, by rfl⟩ : syracuseStep 4709659 = 7064489) B7064489
theorem B7060969 : Blo 1468554 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B6603906671 : Blo 1468554 6603906671 := bstep (se 1 (by rfl) ⟨4952930003, by rfl⟩ : syracuseStep 6603906671 = 9905860007) B9905860007
theorem B18841247 : Blo 1468554 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B2203583 : Blo 1468554 2203583 := bstep (se 1 (by rfl) ⟨1652687, by rfl⟩ : syracuseStep 2203583 = 3305375) B3305375
theorem B11157587 : Blo 1468554 11157587 := bstep (se 1 (by rfl) ⟨8368190, by rfl⟩ : syracuseStep 11157587 = 16736381) B16736381
theorem B6275323 : Blo 1468554 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B143090489 : Blo 1468554 143090489 := bstep (se 2 (by rfl) ⟨53658933, by rfl⟩ : syracuseStep 143090489 = 107317867) B107317867
theorem B2204639 : Blo 1468554 2204639 := bstep (se 1 (by rfl) ⟨1653479, by rfl⟩ : syracuseStep 2204639 = 3306959) B3306959
theorem B6276827 : Blo 1468554 6276827 := bstep (se 1 (by rfl) ⟨4707620, by rfl⟩ : syracuseStep 6276827 = 9415241) B9415241
theorem B9414625 : Blo 1468554 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B6703427 : Blo 1468554 6703427 := bstep (se 1 (by rfl) ⟨5027570, by rfl⟩ : syracuseStep 6703427 = 10055141) B10055141
theorem B4402604447 : Blo 1468554 4402604447 := bstep (se 1 (by rfl) ⟨3301953335, by rfl⟩ : syracuseStep 4402604447 = 6603906671) B6603906671
theorem B12560831 : Blo 1468554 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B1469055 : Blo 1468554 1469055 := bstep (se 1 (by rfl) ⟨1101791, by rfl⟩ : syracuseStep 1469055 = 2203583) B2203583
theorem B1469211 : Blo 1468554 1469211 := bstep (se 1 (by rfl) ⟨1101908, by rfl⟩ : syracuseStep 1469211 = 2203817) B2203817
theorem B3304475 : Blo 1468554 3304475 := bstep (se 1 (by rfl) ⟨2478356, by rfl⟩ : syracuseStep 3304475 = 4956713) B4956713
theorem B22613231 : Blo 1468554 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B4468031 : Blo 1468554 4468031 := bstep (se 1 (by rfl) ⟨3351023, by rfl⟩ : syracuseStep 4468031 = 6702047) B6702047
theorem B1469903 : Blo 1468554 1469903 := bstep (se 1 (by rfl) ⟨1102427, by rfl⟩ : syracuseStep 1469903 = 2204855) B2204855
theorem B1469999 : Blo 1468554 1469999 := bstep (se 1 (by rfl) ⟨1102499, by rfl⟩ : syracuseStep 1469999 = 2204999) B2204999
theorem B916573805 : Blo 1468554 916573805 := bstep (se 3 (by rfl) ⟨171857588, by rfl⟩ : syracuseStep 916573805 = 343715177) B343715177
theorem B4960169 : Blo 1468554 4960169 := bstep (se 2 (by rfl) ⟨1860063, by rfl⟩ : syracuseStep 4960169 = 3720127) B3720127
theorem B13406561 : Blo 1468554 13406561 := bstep (se 2 (by rfl) ⟨5027460, by rfl⟩ : syracuseStep 13406561 = 10054921) B10054921
theorem B6279545 : Blo 1468554 6279545 := bstep (se 2 (by rfl) ⟨2354829, by rfl⟩ : syracuseStep 6279545 = 4709659) B4709659
theorem B27193751 : Blo 1468554 27193751 := bstep (se 1 (by rfl) ⟨20395313, by rfl⟩ : syracuseStep 27193751 = 40790627) B40790627
theorem B7058087 : Blo 1468554 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B11924603 : Blo 1468554 11924603 := bstep (se 1 (by rfl) ⟨8943452, by rfl⟩ : syracuseStep 11924603 = 17886905) B17886905
theorem B4183663 : Blo 1468554 4183663 := bstep (se 1 (by rfl) ⟨3137747, by rfl⟩ : syracuseStep 4183663 = 6275495) B6275495
theorem B3307355 : Blo 1468554 3307355 := bstep (se 1 (by rfl) ⟨2480516, by rfl⟩ : syracuseStep 3307355 = 4961033) B4961033
theorem B2480159 : Blo 1468554 2480159 := bstep (se 1 (by rfl) ⟨1860119, by rfl⟩ : syracuseStep 2480159 = 3720239) B3720239
theorem B28645427 : Blo 1468554 28645427 := bstep (se 1 (by rfl) ⟨21484070, by rfl⟩ : syracuseStep 28645427 = 42968141) B42968141
theorem B12548459 : Blo 1468554 12548459 := bstep (se 1 (by rfl) ⟨9411344, by rfl⟩ : syracuseStep 12548459 = 18822689) B18822689
theorem B4237089239 : Blo 1468554 4237089239 := bstep (se 1 (by rfl) ⟨3177816929, by rfl⟩ : syracuseStep 4237089239 = 6355633859) B6355633859
theorem B723638933 : Blo 1468554 723638933 := bstep (se 6 (by rfl) ⟨16960287, by rfl⟩ : syracuseStep 723638933 = 33920575) B33920575
theorem B1653727 : Blo 1468554 1653727 := bstep (se 1 (by rfl) ⟨1240295, by rfl⟩ : syracuseStep 1653727 = 2480591) B2480591
theorem B7438391 : Blo 1468554 7438391 := bstep (se 1 (by rfl) ⟨5578793, by rfl⟩ : syracuseStep 7438391 = 11157587) B11157587
theorem B8937707 : Blo 1468554 8937707 := bstep (se 1 (by rfl) ⟨6703280, by rfl⟩ : syracuseStep 8937707 = 13406561) B13406561
theorem B4186363 : Blo 1468554 4186363 := bstep (se 1 (by rfl) ⟨3139772, by rfl⟩ : syracuseStep 4186363 = 6279545) B6279545
theorem B18129167 : Blo 1468554 18129167 := bstep (se 1 (by rfl) ⟨13596875, by rfl⟩ : syracuseStep 18129167 = 27193751) B27193751
theorem B2204903 : Blo 1468554 2204903 := bstep (se 1 (by rfl) ⟨1653677, by rfl⟩ : syracuseStep 2204903 = 3307355) B3307355
theorem B2204969 : Blo 1468554 2204969 := bstep (se 2 (by rfl) ⟨826863, by rfl⟩ : syracuseStep 2204969 = 1653727) B1653727
theorem B19096951 : Blo 1468554 19096951 := bstep (se 1 (by rfl) ⟨14322713, by rfl⟩ : syracuseStep 19096951 = 28645427) B28645427
theorem B8365639 : Blo 1468554 8365639 := bstep (se 1 (by rfl) ⟨6274229, by rfl⟩ : syracuseStep 8365639 = 12548459) B12548459
theorem B8373887 : Blo 1468554 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B2824726159 : Blo 1468554 2824726159 := bstep (se 1 (by rfl) ⟨2118544619, by rfl⟩ : syracuseStep 2824726159 = 4237089239) B4237089239
theorem B15075487 : Blo 1468554 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B12552833 : Blo 1468554 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B8367097 : Blo 1468554 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B4705391 : Blo 1468554 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B1469759 : Blo 1468554 1469759 := bstep (se 1 (by rfl) ⟨1102319, by rfl⟩ : syracuseStep 1469759 = 2204639) B2204639
theorem B7949735 : Blo 1468554 7949735 := bstep (se 1 (by rfl) ⟨5962301, by rfl⟩ : syracuseStep 7949735 = 11924603) B11924603
theorem B4468951 : Blo 1468554 4468951 := bstep (se 1 (by rfl) ⟨3351713, by rfl⟩ : syracuseStep 4468951 = 6703427) B6703427
theorem B2978687 : Blo 1468554 2978687 := bstep (se 1 (by rfl) ⟨2234015, by rfl⟩ : syracuseStep 2978687 = 4468031) B4468031
theorem B3306779 : Blo 1468554 3306779 := bstep (se 1 (by rfl) ⟨2480084, by rfl⟩ : syracuseStep 3306779 = 4960169) B4960169
theorem B95393659 : Blo 1468554 95393659 := bstep (se 1 (by rfl) ⟨71545244, by rfl⟩ : syracuseStep 95393659 = 143090489) B143090489
theorem B4184551 : Blo 1468554 4184551 := bstep (se 1 (by rfl) ⟨3138413, by rfl⟩ : syracuseStep 4184551 = 6276827) B6276827
theorem B1653439 : Blo 1468554 1653439 := bstep (se 1 (by rfl) ⟨1240079, by rfl⟩ : syracuseStep 1653439 = 2480159) B2480159
theorem B2935069631 : Blo 1468554 2935069631 := bstep (se 1 (by rfl) ⟨2201302223, by rfl⟩ : syracuseStep 2935069631 = 4402604447) B4402604447
theorem B482425955 : Blo 1468554 482425955 := bstep (se 1 (by rfl) ⟨361819466, by rfl⟩ : syracuseStep 482425955 = 723638933) B723638933
theorem B2202983 : Blo 1468554 2202983 := bstep (se 1 (by rfl) ⟨1652237, by rfl⟩ : syracuseStep 2202983 = 3304475) B3304475
theorem B5578217 : Blo 1468554 5578217 := bstep (se 2 (by rfl) ⟨2091831, by rfl⟩ : syracuseStep 5578217 = 4183663) B4183663
theorem B611049203 : Blo 1468554 611049203 := bstep (se 1 (by rfl) ⟨458286902, by rfl⟩ : syracuseStep 611049203 = 916573805) B916573805
theorem B5579401 : Blo 1468554 5579401 := bstep (se 2 (by rfl) ⟨2092275, by rfl⟩ : syracuseStep 5579401 = 4184551) B4184551
theorem B2204519 : Blo 1468554 2204519 := bstep (se 1 (by rfl) ⟨1653389, by rfl⟩ : syracuseStep 2204519 = 3306779) B3306779
theorem B2204585 : Blo 1468554 2204585 := bstep (se 2 (by rfl) ⟨826719, by rfl⟩ : syracuseStep 2204585 = 1653439) B1653439
theorem B25462601 : Blo 1468554 25462601 := bstep (se 2 (by rfl) ⟨9548475, by rfl⟩ : syracuseStep 25462601 = 19096951) B19096951
theorem B1468655 : Blo 1468554 1468655 := bstep (se 1 (by rfl) ⟨1101491, by rfl⟩ : syracuseStep 1468655 = 2202983) B2202983
theorem B407366135 : Blo 1468554 407366135 := bstep (se 1 (by rfl) ⟨305524601, by rfl⟩ : syracuseStep 407366135 = 611049203) B611049203
theorem B127191545 : Blo 1468554 127191545 := bstep (se 2 (by rfl) ⟨47696829, by rfl⟩ : syracuseStep 127191545 = 95393659) B95393659
theorem B4958927 : Blo 1468554 4958927 := bstep (se 1 (by rfl) ⟨3719195, by rfl⟩ : syracuseStep 4958927 = 7438391) B7438391
theorem B12086111 : Blo 1468554 12086111 := bstep (se 1 (by rfl) ⟨9064583, by rfl⟩ : syracuseStep 12086111 = 18129167) B18129167
theorem B5581817 : Blo 1468554 5581817 := bstep (se 2 (by rfl) ⟨2093181, by rfl⟩ : syracuseStep 5581817 = 4186363) B4186363
theorem B1985791 : Blo 1468554 1985791 := bstep (se 1 (by rfl) ⟨1489343, by rfl⟩ : syracuseStep 1985791 = 2978687) B2978687
theorem B23833885 : Blo 1468554 23833885 := bstep (se 3 (by rfl) ⟨4468853, by rfl⟩ : syracuseStep 23833885 = 8937707) B8937707
theorem B1469935 : Blo 1468554 1469935 := bstep (se 1 (by rfl) ⟨1102451, by rfl⟩ : syracuseStep 1469935 = 2204903) B2204903
theorem B1469979 : Blo 1468554 1469979 := bstep (se 1 (by rfl) ⟨1102484, by rfl⟩ : syracuseStep 1469979 = 2204969) B2204969
theorem B5582591 : Blo 1468554 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B23834405 : Blo 1468554 23834405 := bstep (se 4 (by rfl) ⟨2234475, by rfl⟩ : syracuseStep 23834405 = 4468951) B4468951
theorem B8368555 : Blo 1468554 8368555 := bstep (se 1 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 8368555 = 12552833) B12552833
theorem B1956713087 : Blo 1468554 1956713087 := bstep (se 1 (by rfl) ⟨1467534815, by rfl⟩ : syracuseStep 1956713087 = 2935069631) B2935069631
theorem B11154185 : Blo 1468554 11154185 := bstep (se 2 (by rfl) ⟨4182819, by rfl⟩ : syracuseStep 11154185 = 8365639) B8365639
theorem B3766301545 : Blo 1468554 3766301545 := bstep (se 2 (by rfl) ⟨1412363079, by rfl⟩ : syracuseStep 3766301545 = 2824726159) B2824726159
theorem B20100649 : Blo 1468554 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B12547709 : Blo 1468554 12547709 := bstep (se 3 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 12547709 = 4705391) B4705391
theorem B11156129 : Blo 1468554 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B321617303 : Blo 1468554 321617303 := bstep (se 1 (by rfl) ⟨241212977, by rfl⟩ : syracuseStep 321617303 = 482425955) B482425955
theorem B5299823 : Blo 1468554 5299823 := bstep (se 1 (by rfl) ⟨3974867, by rfl⟩ : syracuseStep 5299823 = 7949735) B7949735
theorem B3718811 : Blo 1468554 3718811 := bstep (se 1 (by rfl) ⟨2789108, by rfl⟩ : syracuseStep 3718811 = 5578217) B5578217
theorem B11158073 : Blo 1468554 11158073 := bstep (se 2 (by rfl) ⟨4184277, by rfl⟩ : syracuseStep 11158073 = 8368555) B8368555
theorem B7439201 : Blo 1468554 7439201 := bstep (se 2 (by rfl) ⟨2789700, by rfl⟩ : syracuseStep 7439201 = 5579401) B5579401
theorem B8365139 : Blo 1468554 8365139 := bstep (se 1 (by rfl) ⟨6273854, by rfl⟩ : syracuseStep 8365139 = 12547709) B12547709
theorem B16975067 : Blo 1468554 16975067 := bstep (se 1 (by rfl) ⟨12731300, by rfl⟩ : syracuseStep 16975067 = 25462601) B25462601
theorem B2647721 : Blo 1468554 2647721 := bstep (se 2 (by rfl) ⟨992895, by rfl⟩ : syracuseStep 2647721 = 1985791) B1985791
theorem B31778513 : Blo 1468554 31778513 := bstep (se 2 (by rfl) ⟨11916942, by rfl⟩ : syracuseStep 31778513 = 23833885) B23833885
theorem B3721211 : Blo 1468554 3721211 := bstep (se 1 (by rfl) ⟨2790908, by rfl⟩ : syracuseStep 3721211 = 5581817) B5581817
theorem B214411535 : Blo 1468554 214411535 := bstep (se 1 (by rfl) ⟨160808651, by rfl⟩ : syracuseStep 214411535 = 321617303) B321617303
theorem B3533215 : Blo 1468554 3533215 := bstep (se 1 (by rfl) ⟨2649911, by rfl⟩ : syracuseStep 3533215 = 5299823) B5299823
theorem B3721727 : Blo 1468554 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B1469679 : Blo 1468554 1469679 := bstep (se 1 (by rfl) ⟨1102259, by rfl⟩ : syracuseStep 1469679 = 2204519) B2204519
theorem B1469723 : Blo 1468554 1469723 := bstep (se 1 (by rfl) ⟨1102292, by rfl⟩ : syracuseStep 1469723 = 2204585) B2204585
theorem B271577423 : Blo 1468554 271577423 := bstep (se 1 (by rfl) ⟨203683067, by rfl⟩ : syracuseStep 271577423 = 407366135) B407366135
theorem B3305951 : Blo 1468554 3305951 := bstep (se 1 (by rfl) ⟨2479463, by rfl⟩ : syracuseStep 3305951 = 4958927) B4958927
theorem B8057407 : Blo 1468554 8057407 := bstep (se 1 (by rfl) ⟨6043055, by rfl⟩ : syracuseStep 8057407 = 12086111) B12086111
theorem B26800865 : Blo 1468554 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B2479207 : Blo 1468554 2479207 := bstep (se 1 (by rfl) ⟨1859405, by rfl⟩ : syracuseStep 2479207 = 3718811) B3718811
theorem B15889603 : Blo 1468554 15889603 := bstep (se 1 (by rfl) ⟨11917202, by rfl⟩ : syracuseStep 15889603 = 23834405) B23834405
theorem B1304475391 : Blo 1468554 1304475391 := bstep (se 1 (by rfl) ⟨978356543, by rfl⟩ : syracuseStep 1304475391 = 1956713087) B1956713087
theorem B7436123 : Blo 1468554 7436123 := bstep (se 1 (by rfl) ⟨5577092, by rfl⟩ : syracuseStep 7436123 = 11154185) B11154185
theorem B5021735393 : Blo 1468554 5021735393 := bstep (se 2 (by rfl) ⟨1883150772, by rfl⟩ : syracuseStep 5021735393 = 3766301545) B3766301545
theorem B84794363 : Blo 1468554 84794363 := bstep (se 1 (by rfl) ⟨63595772, by rfl⟩ : syracuseStep 84794363 = 127191545) B127191545
theorem B7437419 : Blo 1468554 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B181051615 : Blo 1468554 181051615 := bstep (se 1 (by rfl) ⟨135788711, by rfl⟩ : syracuseStep 181051615 = 271577423) B271577423
theorem B2203967 : Blo 1468554 2203967 := bstep (se 1 (by rfl) ⟨1652975, by rfl⟩ : syracuseStep 2203967 = 3305951) B3305951
theorem B7438715 : Blo 1468554 7438715 := bstep (se 1 (by rfl) ⟨5579036, by rfl⟩ : syracuseStep 7438715 = 11158073) B11158073
theorem B17867243 : Blo 1468554 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B4710953 : Blo 1468554 4710953 := bstep (se 2 (by rfl) ⟨1766607, by rfl⟩ : syracuseStep 4710953 = 3533215) B3533215
theorem B21185675 : Blo 1468554 21185675 := bstep (se 1 (by rfl) ⟨15889256, by rfl⟩ : syracuseStep 21185675 = 31778513) B31778513
theorem B4957415 : Blo 1468554 4957415 := bstep (se 1 (by rfl) ⟨3718061, by rfl⟩ : syracuseStep 4957415 = 7436123) B7436123
theorem B21186137 : Blo 1468554 21186137 := bstep (se 2 (by rfl) ⟨7944801, by rfl⟩ : syracuseStep 21186137 = 15889603) B15889603
theorem B4958279 : Blo 1468554 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B4959467 : Blo 1468554 4959467 := bstep (se 1 (by rfl) ⟨3719600, by rfl⟩ : syracuseStep 4959467 = 7439201) B7439201
theorem B10743209 : Blo 1468554 10743209 := bstep (se 2 (by rfl) ⟨4028703, by rfl⟩ : syracuseStep 10743209 = 8057407) B8057407
theorem B1765147 : Blo 1468554 1765147 := bstep (se 1 (by rfl) ⟨1323860, by rfl⟩ : syracuseStep 1765147 = 2647721) B2647721
theorem B3305609 : Blo 1468554 3305609 := bstep (se 2 (by rfl) ⟨1239603, by rfl⟩ : syracuseStep 3305609 = 2479207) B2479207
theorem B56529575 : Blo 1468554 56529575 := bstep (se 1 (by rfl) ⟨42397181, by rfl⟩ : syracuseStep 56529575 = 84794363) B84794363
theorem B45266845 : Blo 1468554 45266845 := bstep (se 3 (by rfl) ⟨8487533, by rfl⟩ : syracuseStep 45266845 = 16975067) B16975067
theorem B5576759 : Blo 1468554 5576759 := bstep (se 1 (by rfl) ⟨4182569, by rfl⟩ : syracuseStep 5576759 = 8365139) B8365139
theorem B2480807 : Blo 1468554 2480807 := bstep (se 1 (by rfl) ⟨1860605, by rfl⟩ : syracuseStep 2480807 = 3721211) B3721211
theorem B142941023 : Blo 1468554 142941023 := bstep (se 1 (by rfl) ⟨107205767, by rfl⟩ : syracuseStep 142941023 = 214411535) B214411535
theorem B3347823595 : Blo 1468554 3347823595 := bstep (se 1 (by rfl) ⟨2510867696, by rfl⟩ : syracuseStep 3347823595 = 5021735393) B5021735393
theorem B2481151 : Blo 1468554 2481151 := bstep (se 1 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 2481151 = 3721727) B3721727
theorem B1739300521 : Blo 1468554 1739300521 := bstep (se 2 (by rfl) ⟨652237695, by rfl⟩ : syracuseStep 1739300521 = 1304475391) B1304475391
theorem B2203739 : Blo 1468554 2203739 := bstep (se 1 (by rfl) ⟨1652804, by rfl⟩ : syracuseStep 2203739 = 3305609) B3305609
theorem B241402153 : Blo 1468554 241402153 := bstep (se 2 (by rfl) ⟨90525807, by rfl⟩ : syracuseStep 241402153 = 181051615) B181051615
theorem B14123783 : Blo 1468554 14123783 := bstep (se 1 (by rfl) ⟨10592837, by rfl⟩ : syracuseStep 14123783 = 21185675) B21185675
theorem B14124091 : Blo 1468554 14124091 := bstep (se 1 (by rfl) ⟨10593068, by rfl⟩ : syracuseStep 14124091 = 21186137) B21186137
theorem B47645981 : Blo 1468554 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B4463764793 : Blo 1468554 4463764793 := bstep (se 2 (by rfl) ⟨1673911797, by rfl⟩ : syracuseStep 4463764793 = 3347823595) B3347823595
theorem B2319067361 : Blo 1468554 2319067361 := bstep (se 2 (by rfl) ⟨869650260, by rfl⟩ : syracuseStep 2319067361 = 1739300521) B1739300521
theorem B7162139 : Blo 1468554 7162139 := bstep (se 1 (by rfl) ⟨5371604, by rfl⟩ : syracuseStep 7162139 = 10743209) B10743209
theorem B2353529 : Blo 1468554 2353529 := bstep (se 2 (by rfl) ⟨882573, by rfl⟩ : syracuseStep 2353529 = 1765147) B1765147
theorem B1469311 : Blo 1468554 1469311 := bstep (se 1 (by rfl) ⟨1101983, by rfl⟩ : syracuseStep 1469311 = 2203967) B2203967
theorem B4959143 : Blo 1468554 4959143 := bstep (se 1 (by rfl) ⟨3719357, by rfl⟩ : syracuseStep 4959143 = 7438715) B7438715
theorem B3140635 : Blo 1468554 3140635 := bstep (se 1 (by rfl) ⟨2355476, by rfl⟩ : syracuseStep 3140635 = 4710953) B4710953
theorem B37686383 : Blo 1468554 37686383 := bstep (se 1 (by rfl) ⟨28264787, by rfl⟩ : syracuseStep 37686383 = 56529575) B56529575
theorem B3304943 : Blo 1468554 3304943 := bstep (se 1 (by rfl) ⟨2478707, by rfl⟩ : syracuseStep 3304943 = 4957415) B4957415
theorem B3305519 : Blo 1468554 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B95294015 : Blo 1468554 95294015 := bstep (se 1 (by rfl) ⟨71470511, by rfl⟩ : syracuseStep 95294015 = 142941023) B142941023
theorem B3306311 : Blo 1468554 3306311 := bstep (se 1 (by rfl) ⟨2479733, by rfl⟩ : syracuseStep 3306311 = 4959467) B4959467
theorem B60355793 : Blo 1468554 60355793 := bstep (se 2 (by rfl) ⟨22633422, by rfl⟩ : syracuseStep 60355793 = 45266845) B45266845
theorem B3308201 : Blo 1468554 3308201 := bstep (se 2 (by rfl) ⟨1240575, by rfl⟩ : syracuseStep 3308201 = 2481151) B2481151
theorem B3717839 : Blo 1468554 3717839 := bstep (se 1 (by rfl) ⟨2788379, by rfl⟩ : syracuseStep 3717839 = 5576759) B5576759
theorem B1653871 : Blo 1468554 1653871 := bstep (se 1 (by rfl) ⟨1240403, by rfl⟩ : syracuseStep 1653871 = 2480807) B2480807
theorem B2203679 : Blo 1468554 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B63529343 : Blo 1468554 63529343 := bstep (se 1 (by rfl) ⟨47647007, by rfl⟩ : syracuseStep 63529343 = 95294015) B95294015
theorem B160948781 : Blo 1468554 160948781 := bstep (se 3 (by rfl) ⟨30177896, by rfl⟩ : syracuseStep 160948781 = 60355793) B60355793
theorem B2204207 : Blo 1468554 2204207 := bstep (se 1 (by rfl) ⟨1653155, by rfl⟩ : syracuseStep 2204207 = 3306311) B3306311
theorem B2975843195 : Blo 1468554 2975843195 := bstep (se 1 (by rfl) ⟨2231882396, by rfl⟩ : syracuseStep 2975843195 = 4463764793) B4463764793
theorem B4187513 : Blo 1468554 4187513 := bstep (se 2 (by rfl) ⟨1570317, by rfl⟩ : syracuseStep 4187513 = 3140635) B3140635
theorem B2205161 : Blo 1468554 2205161 := bstep (se 2 (by rfl) ⟨826935, by rfl⟩ : syracuseStep 2205161 = 1653871) B1653871
theorem B1546044907 : Blo 1468554 1546044907 := bstep (se 1 (by rfl) ⟨1159533680, by rfl⟩ : syracuseStep 1546044907 = 2319067361) B2319067361
theorem B2205467 : Blo 1468554 2205467 := bstep (se 1 (by rfl) ⟨1654100, by rfl⟩ : syracuseStep 2205467 = 3308201) B3308201
theorem B1469159 : Blo 1468554 1469159 := bstep (se 1 (by rfl) ⟨1101869, by rfl⟩ : syracuseStep 1469159 = 2203739) B2203739
theorem B9415855 : Blo 1468554 9415855 := bstep (se 1 (by rfl) ⟨7061891, by rfl⟩ : syracuseStep 9415855 = 14123783) B14123783
theorem B19099037 : Blo 1468554 19099037 := bstep (se 3 (by rfl) ⟨3581069, by rfl⟩ : syracuseStep 19099037 = 7162139) B7162139
theorem B31763987 : Blo 1468554 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B1569019 : Blo 1468554 1569019 := bstep (se 1 (by rfl) ⟨1176764, by rfl⟩ : syracuseStep 1569019 = 2353529) B2353529
theorem B2478559 : Blo 1468554 2478559 := bstep (se 1 (by rfl) ⟨1858919, by rfl⟩ : syracuseStep 2478559 = 3717839) B3717839
theorem B3306095 : Blo 1468554 3306095 := bstep (se 1 (by rfl) ⟨2479571, by rfl⟩ : syracuseStep 3306095 = 4959143) B4959143
theorem B321869537 : Blo 1468554 321869537 := bstep (se 2 (by rfl) ⟨120701076, by rfl⟩ : syracuseStep 321869537 = 241402153) B241402153
theorem B18832121 : Blo 1468554 18832121 := bstep (se 2 (by rfl) ⟨7062045, by rfl⟩ : syracuseStep 18832121 = 14124091) B14124091
theorem B25124255 : Blo 1468554 25124255 := bstep (se 1 (by rfl) ⟨18843191, by rfl⟩ : syracuseStep 25124255 = 37686383) B37686383
theorem B2203295 : Blo 1468554 2203295 := bstep (se 1 (by rfl) ⟨1652471, by rfl⟩ : syracuseStep 2203295 = 3304943) B3304943
theorem B42352895 : Blo 1468554 42352895 := bstep (se 1 (by rfl) ⟨31764671, by rfl⟩ : syracuseStep 42352895 = 63529343) B63529343
theorem B107299187 : Blo 1468554 107299187 := bstep (se 1 (by rfl) ⟨80474390, by rfl⟩ : syracuseStep 107299187 = 160948781) B160948781
theorem B2204063 : Blo 1468554 2204063 := bstep (se 1 (by rfl) ⟨1653047, by rfl⟩ : syracuseStep 2204063 = 3306095) B3306095
theorem B50930765 : Blo 1468554 50930765 := bstep (se 3 (by rfl) ⟨9549518, by rfl⟩ : syracuseStep 50930765 = 19099037) B19099037
theorem B1468863 : Blo 1468554 1468863 := bstep (se 1 (by rfl) ⟨1101647, by rfl⟩ : syracuseStep 1468863 = 2203295) B2203295
theorem B1469119 : Blo 1468554 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B2092025 : Blo 1468554 2092025 := bstep (se 2 (by rfl) ⟨784509, by rfl⟩ : syracuseStep 2092025 = 1569019) B1569019
theorem B1469471 : Blo 1468554 1469471 := bstep (se 1 (by rfl) ⟨1102103, by rfl⟩ : syracuseStep 1469471 = 2204207) B2204207
theorem B3304745 : Blo 1468554 3304745 := bstep (se 2 (by rfl) ⟨1239279, by rfl⟩ : syracuseStep 3304745 = 2478559) B2478559
theorem B1470107 : Blo 1468554 1470107 := bstep (se 1 (by rfl) ⟨1102580, by rfl⟩ : syracuseStep 1470107 = 2205161) B2205161
theorem B1470311 : Blo 1468554 1470311 := bstep (se 1 (by rfl) ⟨1102733, by rfl⟩ : syracuseStep 1470311 = 2205467) B2205467
theorem B12554473 : Blo 1468554 12554473 := bstep (se 2 (by rfl) ⟨4707927, by rfl⟩ : syracuseStep 12554473 = 9415855) B9415855
theorem B12554747 : Blo 1468554 12554747 := bstep (se 1 (by rfl) ⟨9416060, by rfl⟩ : syracuseStep 12554747 = 18832121) B18832121
theorem B16749503 : Blo 1468554 16749503 := bstep (se 1 (by rfl) ⟨12562127, by rfl⟩ : syracuseStep 16749503 = 25124255) B25124255
theorem B1983895463 : Blo 1468554 1983895463 := bstep (se 1 (by rfl) ⟨1487921597, by rfl⟩ : syracuseStep 1983895463 = 2975843195) B2975843195
theorem B2791675 : Blo 1468554 2791675 := bstep (se 1 (by rfl) ⟨2093756, by rfl⟩ : syracuseStep 2791675 = 4187513) B4187513
theorem B214579691 : Blo 1468554 214579691 := bstep (se 1 (by rfl) ⟨160934768, by rfl⟩ : syracuseStep 214579691 = 321869537) B321869537
theorem B2061393209 : Blo 1468554 2061393209 := bstep (se 2 (by rfl) ⟨773022453, by rfl⟩ : syracuseStep 2061393209 = 1546044907) B1546044907
theorem B21175991 : Blo 1468554 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B71532791 : Blo 1468554 71532791 := bstep (se 1 (by rfl) ⟨53649593, by rfl⟩ : syracuseStep 71532791 = 107299187) B107299187
theorem B11166335 : Blo 1468554 11166335 := bstep (se 1 (by rfl) ⟨8374751, by rfl⟩ : syracuseStep 11166335 = 16749503) B16749503
theorem B5290387901 : Blo 1468554 5290387901 := bstep (se 3 (by rfl) ⟨991947731, by rfl⟩ : syracuseStep 5290387901 = 1983895463) B1983895463
theorem B14117327 : Blo 1468554 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B1469375 : Blo 1468554 1469375 := bstep (se 1 (by rfl) ⟨1102031, by rfl⟩ : syracuseStep 1469375 = 2204063) B2204063
theorem B16739297 : Blo 1468554 16739297 := bstep (se 2 (by rfl) ⟨6277236, by rfl⟩ : syracuseStep 16739297 = 12554473) B12554473
theorem B3722233 : Blo 1468554 3722233 := bstep (se 2 (by rfl) ⟨1395837, by rfl⟩ : syracuseStep 3722233 = 2791675) B2791675
theorem B143053127 : Blo 1468554 143053127 := bstep (se 1 (by rfl) ⟨107289845, by rfl⟩ : syracuseStep 143053127 = 214579691) B214579691
theorem B1374262139 : Blo 1468554 1374262139 := bstep (se 1 (by rfl) ⟨1030696604, by rfl⟩ : syracuseStep 1374262139 = 2061393209) B2061393209
theorem B28235263 : Blo 1468554 28235263 := bstep (se 1 (by rfl) ⟨21176447, by rfl⟩ : syracuseStep 28235263 = 42352895) B42352895
theorem B8369831 : Blo 1468554 8369831 := bstep (se 1 (by rfl) ⟨6277373, by rfl⟩ : syracuseStep 8369831 = 12554747) B12554747
theorem B33953843 : Blo 1468554 33953843 := bstep (se 1 (by rfl) ⟨25465382, by rfl⟩ : syracuseStep 33953843 = 50930765) B50930765
theorem B2203163 : Blo 1468554 2203163 := bstep (se 1 (by rfl) ⟨1652372, by rfl⟩ : syracuseStep 2203163 = 3304745) B3304745
theorem B5578733 : Blo 1468554 5578733 := bstep (se 3 (by rfl) ⟨1046012, by rfl⟩ : syracuseStep 5578733 = 2092025) B2092025
theorem B5579887 : Blo 1468554 5579887 := bstep (se 1 (by rfl) ⟨4184915, by rfl⟩ : syracuseStep 5579887 = 8369831) B8369831
theorem B22635895 : Blo 1468554 22635895 := bstep (se 1 (by rfl) ⟨16976921, by rfl⟩ : syracuseStep 22635895 = 33953843) B33953843
theorem B11159531 : Blo 1468554 11159531 := bstep (se 1 (by rfl) ⟨8369648, by rfl⟩ : syracuseStep 11159531 = 16739297) B16739297
theorem B1468775 : Blo 1468554 1468775 := bstep (se 1 (by rfl) ⟨1101581, by rfl⟩ : syracuseStep 1468775 = 2203163) B2203163
theorem B47688527 : Blo 1468554 47688527 := bstep (se 1 (by rfl) ⟨35766395, by rfl⟩ : syracuseStep 47688527 = 71532791) B71532791
theorem B37647017 : Blo 1468554 37647017 := bstep (se 2 (by rfl) ⟨14117631, by rfl⟩ : syracuseStep 37647017 = 28235263) B28235263
theorem B95368751 : Blo 1468554 95368751 := bstep (se 1 (by rfl) ⟨71526563, by rfl⟩ : syracuseStep 95368751 = 143053127) B143053127
theorem B7444223 : Blo 1468554 7444223 := bstep (se 1 (by rfl) ⟨5583167, by rfl⟩ : syracuseStep 7444223 = 11166335) B11166335
theorem B916174759 : Blo 1468554 916174759 := bstep (se 1 (by rfl) ⟨687131069, by rfl⟩ : syracuseStep 916174759 = 1374262139) B1374262139
theorem B4962977 : Blo 1468554 4962977 := bstep (se 2 (by rfl) ⟨1861116, by rfl⟩ : syracuseStep 4962977 = 3722233) B3722233
theorem B3526925267 : Blo 1468554 3526925267 := bstep (se 1 (by rfl) ⟨2645193950, by rfl⟩ : syracuseStep 3526925267 = 5290387901) B5290387901
theorem B9411551 : Blo 1468554 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B3719155 : Blo 1468554 3719155 := bstep (se 1 (by rfl) ⟨2789366, by rfl⟩ : syracuseStep 3719155 = 5578733) B5578733
theorem B63579167 : Blo 1468554 63579167 := bstep (se 1 (by rfl) ⟨47684375, by rfl⟩ : syracuseStep 63579167 = 95368751) B95368751
theorem B7439687 : Blo 1468554 7439687 := bstep (se 1 (by rfl) ⟨5579765, by rfl⟩ : syracuseStep 7439687 = 11159531) B11159531
theorem B7439849 : Blo 1468554 7439849 := bstep (se 2 (by rfl) ⟨2789943, by rfl⟩ : syracuseStep 7439849 = 5579887) B5579887
theorem B30181193 : Blo 1468554 30181193 := bstep (se 2 (by rfl) ⟨11317947, by rfl⟩ : syracuseStep 30181193 = 22635895) B22635895
theorem B4958873 : Blo 1468554 4958873 := bstep (se 2 (by rfl) ⟨1859577, by rfl⟩ : syracuseStep 4958873 = 3719155) B3719155
theorem B25098011 : Blo 1468554 25098011 := bstep (se 1 (by rfl) ⟨18823508, by rfl⟩ : syracuseStep 25098011 = 37647017) B37647017
theorem B4962815 : Blo 1468554 4962815 := bstep (se 1 (by rfl) ⟨3722111, by rfl⟩ : syracuseStep 4962815 = 7444223) B7444223
theorem B3308651 : Blo 1468554 3308651 := bstep (se 1 (by rfl) ⟨2481488, by rfl⟩ : syracuseStep 3308651 = 4962977) B4962977
theorem B31792351 : Blo 1468554 31792351 := bstep (se 1 (by rfl) ⟨23844263, by rfl⟩ : syracuseStep 31792351 = 47688527) B47688527
theorem B2351283511 : Blo 1468554 2351283511 := bstep (se 1 (by rfl) ⟨1763462633, by rfl⟩ : syracuseStep 2351283511 = 3526925267) B3526925267
theorem B6274367 : Blo 1468554 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B1221566345 : Blo 1468554 1221566345 := bstep (se 2 (by rfl) ⟨458087379, by rfl⟩ : syracuseStep 1221566345 = 916174759) B916174759
theorem B42386111 : Blo 1468554 42386111 := bstep (se 1 (by rfl) ⟨31789583, by rfl⟩ : syracuseStep 42386111 = 63579167) B63579167
theorem B20120795 : Blo 1468554 20120795 := bstep (se 1 (by rfl) ⟨15090596, by rfl⟩ : syracuseStep 20120795 = 30181193) B30181193
theorem B2205767 : Blo 1468554 2205767 := bstep (se 1 (by rfl) ⟨1654325, by rfl⟩ : syracuseStep 2205767 = 3308651) B3308651
theorem B814377563 : Blo 1468554 814377563 := bstep (se 1 (by rfl) ⟨610783172, by rfl⟩ : syracuseStep 814377563 = 1221566345) B1221566345
theorem B4959791 : Blo 1468554 4959791 := bstep (se 1 (by rfl) ⟨3719843, by rfl⟩ : syracuseStep 4959791 = 7439687) B7439687
theorem B4959899 : Blo 1468554 4959899 := bstep (se 1 (by rfl) ⟨3719924, by rfl⟩ : syracuseStep 4959899 = 7439849) B7439849
theorem B16732007 : Blo 1468554 16732007 := bstep (se 1 (by rfl) ⟨12549005, by rfl⟩ : syracuseStep 16732007 = 25098011) B25098011
theorem B42389801 : Blo 1468554 42389801 := bstep (se 2 (by rfl) ⟨15896175, by rfl⟩ : syracuseStep 42389801 = 31792351) B31792351
theorem B3305915 : Blo 1468554 3305915 := bstep (se 1 (by rfl) ⟨2479436, by rfl⟩ : syracuseStep 3305915 = 4958873) B4958873
theorem B4182911 : Blo 1468554 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B3308543 : Blo 1468554 3308543 := bstep (se 1 (by rfl) ⟨2481407, by rfl⟩ : syracuseStep 3308543 = 4962815) B4962815
theorem B3135044681 : Blo 1468554 3135044681 := bstep (se 2 (by rfl) ⟨1175641755, by rfl⟩ : syracuseStep 3135044681 = 2351283511) B2351283511
theorem B2203943 : Blo 1468554 2203943 := bstep (se 1 (by rfl) ⟨1652957, by rfl⟩ : syracuseStep 2203943 = 3305915) B3305915
theorem B542918375 : Blo 1468554 542918375 := bstep (se 1 (by rfl) ⟨407188781, by rfl⟩ : syracuseStep 542918375 = 814377563) B814377563
theorem B2205695 : Blo 1468554 2205695 := bstep (se 1 (by rfl) ⟨1654271, by rfl⟩ : syracuseStep 2205695 = 3308543) B3308543
theorem B28257407 : Blo 1468554 28257407 := bstep (se 1 (by rfl) ⟨21193055, by rfl⟩ : syracuseStep 28257407 = 42386111) B42386111
theorem B2788607 : Blo 1468554 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B13413863 : Blo 1468554 13413863 := bstep (se 1 (by rfl) ⟨10060397, by rfl⟩ : syracuseStep 13413863 = 20120795) B20120795
theorem B1470511 : Blo 1468554 1470511 := bstep (se 1 (by rfl) ⟨1102883, by rfl⟩ : syracuseStep 1470511 = 2205767) B2205767
theorem B2090029787 : Blo 1468554 2090029787 := bstep (se 1 (by rfl) ⟨1567522340, by rfl⟩ : syracuseStep 2090029787 = 3135044681) B3135044681
theorem B3306527 : Blo 1468554 3306527 := bstep (se 1 (by rfl) ⟨2479895, by rfl⟩ : syracuseStep 3306527 = 4959791) B4959791
theorem B3306599 : Blo 1468554 3306599 := bstep (se 1 (by rfl) ⟨2479949, by rfl⟩ : syracuseStep 3306599 = 4959899) B4959899
theorem B11154671 : Blo 1468554 11154671 := bstep (se 1 (by rfl) ⟨8366003, by rfl⟩ : syracuseStep 11154671 = 16732007) B16732007
theorem B28259867 : Blo 1468554 28259867 := bstep (se 1 (by rfl) ⟨21194900, by rfl⟩ : syracuseStep 28259867 = 42389801) B42389801
theorem B1393353191 : Blo 1468554 1393353191 := bstep (se 1 (by rfl) ⟨1045014893, by rfl⟩ : syracuseStep 1393353191 = 2090029787) B2090029787
theorem B2204351 : Blo 1468554 2204351 := bstep (se 1 (by rfl) ⟨1653263, by rfl⟩ : syracuseStep 2204351 = 3306527) B3306527
theorem B2204399 : Blo 1468554 2204399 := bstep (se 1 (by rfl) ⟨1653299, by rfl⟩ : syracuseStep 2204399 = 3306599) B3306599
theorem B1469295 : Blo 1468554 1469295 := bstep (se 1 (by rfl) ⟨1101971, by rfl⟩ : syracuseStep 1469295 = 2203943) B2203943
theorem B1470463 : Blo 1468554 1470463 := bstep (se 1 (by rfl) ⟨1102847, by rfl⟩ : syracuseStep 1470463 = 2205695) B2205695
theorem B18838271 : Blo 1468554 18838271 := bstep (se 1 (by rfl) ⟨14128703, by rfl⟩ : syracuseStep 18838271 = 28257407) B28257407
theorem B8942575 : Blo 1468554 8942575 := bstep (se 1 (by rfl) ⟨6706931, by rfl⟩ : syracuseStep 8942575 = 13413863) B13413863
theorem B7436285 : Blo 1468554 7436285 := bstep (se 3 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 7436285 = 2788607) B2788607
theorem B7436447 : Blo 1468554 7436447 := bstep (se 1 (by rfl) ⟨5577335, by rfl⟩ : syracuseStep 7436447 = 11154671) B11154671
theorem B18839911 : Blo 1468554 18839911 := bstep (se 1 (by rfl) ⟨14129933, by rfl⟩ : syracuseStep 18839911 = 28259867) B28259867
theorem B361945583 : Blo 1468554 361945583 := bstep (se 1 (by rfl) ⟨271459187, by rfl⟩ : syracuseStep 361945583 = 542918375) B542918375
theorem B12558847 : Blo 1468554 12558847 := bstep (se 1 (by rfl) ⟨9419135, by rfl⟩ : syracuseStep 12558847 = 18838271) B18838271
theorem B4957523 : Blo 1468554 4957523 := bstep (se 1 (by rfl) ⟨3718142, by rfl⟩ : syracuseStep 4957523 = 7436285) B7436285
theorem B4957631 : Blo 1468554 4957631 := bstep (se 1 (by rfl) ⟨3718223, by rfl⟩ : syracuseStep 4957631 = 7436447) B7436447
theorem B241297055 : Blo 1468554 241297055 := bstep (se 1 (by rfl) ⟨180972791, by rfl⟩ : syracuseStep 241297055 = 361945583) B361945583
theorem B928902127 : Blo 1468554 928902127 := bstep (se 1 (by rfl) ⟨696676595, by rfl⟩ : syracuseStep 928902127 = 1393353191) B1393353191
theorem B1469567 : Blo 1468554 1469567 := bstep (se 1 (by rfl) ⟨1102175, by rfl⟩ : syracuseStep 1469567 = 2204351) B2204351
theorem B25119881 : Blo 1468554 25119881 := bstep (se 2 (by rfl) ⟨9419955, by rfl⟩ : syracuseStep 25119881 = 18839911) B18839911
theorem B1469599 : Blo 1468554 1469599 := bstep (se 1 (by rfl) ⟨1102199, by rfl⟩ : syracuseStep 1469599 = 2204399) B2204399
theorem B11923433 : Blo 1468554 11923433 := bstep (se 2 (by rfl) ⟨4471287, by rfl⟩ : syracuseStep 11923433 = 8942575) B8942575
theorem B16745129 : Blo 1468554 16745129 := bstep (se 2 (by rfl) ⟨6279423, by rfl⟩ : syracuseStep 16745129 = 12558847) B12558847
theorem B16746587 : Blo 1468554 16746587 := bstep (se 1 (by rfl) ⟨12559940, by rfl⟩ : syracuseStep 16746587 = 25119881) B25119881
theorem B7948955 : Blo 1468554 7948955 := bstep (se 1 (by rfl) ⟨5961716, by rfl⟩ : syracuseStep 7948955 = 11923433) B11923433
theorem B3305015 : Blo 1468554 3305015 := bstep (se 1 (by rfl) ⟨2478761, by rfl⟩ : syracuseStep 3305015 = 4957523) B4957523
theorem B3305087 : Blo 1468554 3305087 := bstep (se 1 (by rfl) ⟨2478815, by rfl⟩ : syracuseStep 3305087 = 4957631) B4957631
theorem B1238536169 : Blo 1468554 1238536169 := bstep (se 2 (by rfl) ⟨464451063, by rfl⟩ : syracuseStep 1238536169 = 928902127) B928902127
theorem B160864703 : Blo 1468554 160864703 := bstep (se 1 (by rfl) ⟨120648527, by rfl⟩ : syracuseStep 160864703 = 241297055) B241297055
theorem B107243135 : Blo 1468554 107243135 := bstep (se 1 (by rfl) ⟨80432351, by rfl⟩ : syracuseStep 107243135 = 160864703) B160864703
theorem B825690779 : Blo 1468554 825690779 := bstep (se 1 (by rfl) ⟨619268084, by rfl⟩ : syracuseStep 825690779 = 1238536169) B1238536169
theorem B11163419 : Blo 1468554 11163419 := bstep (se 1 (by rfl) ⟨8372564, by rfl⟩ : syracuseStep 11163419 = 16745129) B16745129
theorem B11164391 : Blo 1468554 11164391 := bstep (se 1 (by rfl) ⟨8373293, by rfl⟩ : syracuseStep 11164391 = 16746587) B16746587
theorem B5299303 : Blo 1468554 5299303 := bstep (se 1 (by rfl) ⟨3974477, by rfl⟩ : syracuseStep 5299303 = 7948955) B7948955
theorem B2203343 : Blo 1468554 2203343 := bstep (se 1 (by rfl) ⟨1652507, by rfl⟩ : syracuseStep 2203343 = 3305015) B3305015
theorem B2203391 : Blo 1468554 2203391 := bstep (se 1 (by rfl) ⟨1652543, by rfl⟩ : syracuseStep 2203391 = 3305087) B3305087
theorem B1468895 : Blo 1468554 1468895 := bstep (se 1 (by rfl) ⟨1101671, by rfl⟩ : syracuseStep 1468895 = 2203343) B2203343
theorem B1468927 : Blo 1468554 1468927 := bstep (se 1 (by rfl) ⟨1101695, by rfl⟩ : syracuseStep 1468927 = 2203391) B2203391
theorem B71495423 : Blo 1468554 71495423 := bstep (se 1 (by rfl) ⟨53621567, by rfl⟩ : syracuseStep 71495423 = 107243135) B107243135
theorem B7442279 : Blo 1468554 7442279 := bstep (se 1 (by rfl) ⟨5581709, by rfl⟩ : syracuseStep 7442279 = 11163419) B11163419
theorem B7065737 : Blo 1468554 7065737 := bstep (se 2 (by rfl) ⟨2649651, by rfl⟩ : syracuseStep 7065737 = 5299303) B5299303
theorem B7442927 : Blo 1468554 7442927 := bstep (se 1 (by rfl) ⟨5582195, by rfl⟩ : syracuseStep 7442927 = 11164391) B11164391
theorem B550460519 : Blo 1468554 550460519 := bstep (se 1 (by rfl) ⟨412845389, by rfl⟩ : syracuseStep 550460519 = 825690779) B825690779
theorem B4710491 : Blo 1468554 4710491 := bstep (se 1 (by rfl) ⟨3532868, by rfl⟩ : syracuseStep 4710491 = 7065737) B7065737
theorem B47663615 : Blo 1468554 47663615 := bstep (se 1 (by rfl) ⟨35747711, by rfl⟩ : syracuseStep 47663615 = 71495423) B71495423
theorem B366973679 : Blo 1468554 366973679 := bstep (se 1 (by rfl) ⟨275230259, by rfl⟩ : syracuseStep 366973679 = 550460519) B550460519
theorem B4961519 : Blo 1468554 4961519 := bstep (se 1 (by rfl) ⟨3721139, by rfl⟩ : syracuseStep 4961519 = 7442279) B7442279
theorem B4961951 : Blo 1468554 4961951 := bstep (se 1 (by rfl) ⟨3721463, by rfl⟩ : syracuseStep 4961951 = 7442927) B7442927
theorem B3140327 : Blo 1468554 3140327 := bstep (se 1 (by rfl) ⟨2355245, by rfl⟩ : syracuseStep 3140327 = 4710491) B4710491
theorem B978596477 : Blo 1468554 978596477 := bstep (se 3 (by rfl) ⟨183486839, by rfl⟩ : syracuseStep 978596477 = 366973679) B366973679
theorem B3307679 : Blo 1468554 3307679 := bstep (se 1 (by rfl) ⟨2480759, by rfl⟩ : syracuseStep 3307679 = 4961519) B4961519
theorem B3307967 : Blo 1468554 3307967 := bstep (se 1 (by rfl) ⟨2480975, by rfl⟩ : syracuseStep 3307967 = 4961951) B4961951
theorem B31775743 : Blo 1468554 31775743 := bstep (se 1 (by rfl) ⟨23831807, by rfl⟩ : syracuseStep 31775743 = 47663615) B47663615
theorem B2205119 : Blo 1468554 2205119 := bstep (se 1 (by rfl) ⟨1653839, by rfl⟩ : syracuseStep 2205119 = 3307679) B3307679
theorem B2205311 : Blo 1468554 2205311 := bstep (se 1 (by rfl) ⟨1653983, by rfl⟩ : syracuseStep 2205311 = 3307967) B3307967
theorem B8374205 : Blo 1468554 8374205 := bstep (se 3 (by rfl) ⟨1570163, by rfl⟩ : syracuseStep 8374205 = 3140327) B3140327
theorem B652397651 : Blo 1468554 652397651 := bstep (se 1 (by rfl) ⟨489298238, by rfl⟩ : syracuseStep 652397651 = 978596477) B978596477
theorem B42367657 : Blo 1468554 42367657 := bstep (se 2 (by rfl) ⟨15887871, by rfl⟩ : syracuseStep 42367657 = 31775743) B31775743
theorem B434931767 : Blo 1468554 434931767 := bstep (se 1 (by rfl) ⟨326198825, by rfl⟩ : syracuseStep 434931767 = 652397651) B652397651
theorem B1470079 : Blo 1468554 1470079 := bstep (se 1 (by rfl) ⟨1102559, by rfl⟩ : syracuseStep 1470079 = 2205119) B2205119
theorem B1470207 : Blo 1468554 1470207 := bstep (se 1 (by rfl) ⟨1102655, by rfl⟩ : syracuseStep 1470207 = 2205311) B2205311
theorem B5582803 : Blo 1468554 5582803 := bstep (se 1 (by rfl) ⟨4187102, by rfl⟩ : syracuseStep 5582803 = 8374205) B8374205
theorem B56490209 : Blo 1468554 56490209 := bstep (se 2 (by rfl) ⟨21183828, by rfl⟩ : syracuseStep 56490209 = 42367657) B42367657
theorem B37660139 : Blo 1468554 37660139 := bstep (se 1 (by rfl) ⟨28245104, by rfl⟩ : syracuseStep 37660139 = 56490209) B56490209
theorem B7443737 : Blo 1468554 7443737 := bstep (se 2 (by rfl) ⟨2791401, by rfl⟩ : syracuseStep 7443737 = 5582803) B5582803
theorem B289954511 : Blo 1468554 289954511 := bstep (se 1 (by rfl) ⟨217465883, by rfl⟩ : syracuseStep 289954511 = 434931767) B434931767
theorem B193303007 : Blo 1468554 193303007 := bstep (se 1 (by rfl) ⟨144977255, by rfl⟩ : syracuseStep 193303007 = 289954511) B289954511
theorem B4962491 : Blo 1468554 4962491 := bstep (se 1 (by rfl) ⟨3721868, by rfl⟩ : syracuseStep 4962491 = 7443737) B7443737
theorem B25106759 : Blo 1468554 25106759 := bstep (se 1 (by rfl) ⟨18830069, by rfl⟩ : syracuseStep 25106759 = 37660139) B37660139
theorem B128868671 : Blo 1468554 128868671 := bstep (se 1 (by rfl) ⟨96651503, by rfl⟩ : syracuseStep 128868671 = 193303007) B193303007
theorem B16737839 : Blo 1468554 16737839 := bstep (se 1 (by rfl) ⟨12553379, by rfl⟩ : syracuseStep 16737839 = 25106759) B25106759
theorem B3308327 : Blo 1468554 3308327 := bstep (se 1 (by rfl) ⟨2481245, by rfl⟩ : syracuseStep 3308327 = 4962491) B4962491
theorem B11158559 : Blo 1468554 11158559 := bstep (se 1 (by rfl) ⟨8368919, by rfl⟩ : syracuseStep 11158559 = 16737839) B16737839
theorem B2205551 : Blo 1468554 2205551 := bstep (se 1 (by rfl) ⟨1654163, by rfl⟩ : syracuseStep 2205551 = 3308327) B3308327
theorem B343649789 : Blo 1468554 343649789 := bstep (se 3 (by rfl) ⟨64434335, by rfl⟩ : syracuseStep 343649789 = 128868671) B128868671
theorem B7439039 : Blo 1468554 7439039 := bstep (se 1 (by rfl) ⟨5579279, by rfl⟩ : syracuseStep 7439039 = 11158559) B11158559
theorem B229099859 : Blo 1468554 229099859 := bstep (se 1 (by rfl) ⟨171824894, by rfl⟩ : syracuseStep 229099859 = 343649789) B343649789
theorem B1470367 : Blo 1468554 1470367 := bstep (se 1 (by rfl) ⟨1102775, by rfl⟩ : syracuseStep 1470367 = 2205551) B2205551
theorem B152733239 : Blo 1468554 152733239 := bstep (se 1 (by rfl) ⟨114549929, by rfl⟩ : syracuseStep 152733239 = 229099859) B229099859
theorem B4959359 : Blo 1468554 4959359 := bstep (se 1 (by rfl) ⟨3719519, by rfl⟩ : syracuseStep 4959359 = 7439039) B7439039
theorem B101822159 : Blo 1468554 101822159 := bstep (se 1 (by rfl) ⟨76366619, by rfl⟩ : syracuseStep 101822159 = 152733239) B152733239
theorem B3306239 : Blo 1468554 3306239 := bstep (se 1 (by rfl) ⟨2479679, by rfl⟩ : syracuseStep 3306239 = 4959359) B4959359
theorem B2204159 : Blo 1468554 2204159 := bstep (se 1 (by rfl) ⟨1653119, by rfl⟩ : syracuseStep 2204159 = 3306239) B3306239
theorem B67881439 : Blo 1468554 67881439 := bstep (se 1 (by rfl) ⟨50911079, by rfl⟩ : syracuseStep 67881439 = 101822159) B101822159
theorem B1469439 : Blo 1468554 1469439 := bstep (se 1 (by rfl) ⟨1102079, by rfl⟩ : syracuseStep 1469439 = 2204159) B2204159
theorem B90508585 : Blo 1468554 90508585 := bstep (se 2 (by rfl) ⟨33940719, by rfl⟩ : syracuseStep 90508585 = 67881439) B67881439
theorem B120678113 : Blo 1468554 120678113 := bstep (se 2 (by rfl) ⟨45254292, by rfl⟩ : syracuseStep 120678113 = 90508585) B90508585
theorem B80452075 : Blo 1468554 80452075 := bstep (se 1 (by rfl) ⟨60339056, by rfl⟩ : syracuseStep 80452075 = 120678113) B120678113
theorem B107269433 : Blo 1468554 107269433 := bstep (se 2 (by rfl) ⟨40226037, by rfl⟩ : syracuseStep 107269433 = 80452075) B80452075
theorem B71512955 : Blo 1468554 71512955 := bstep (se 1 (by rfl) ⟨53634716, by rfl⟩ : syracuseStep 71512955 = 107269433) B107269433
theorem B47675303 : Blo 1468554 47675303 := bstep (se 1 (by rfl) ⟨35756477, by rfl⟩ : syracuseStep 47675303 = 71512955) B71512955
theorem B31783535 : Blo 1468554 31783535 := bstep (se 1 (by rfl) ⟨23837651, by rfl⟩ : syracuseStep 31783535 = 47675303) B47675303
theorem B21189023 : Blo 1468554 21189023 := bstep (se 1 (by rfl) ⟨15891767, by rfl⟩ : syracuseStep 21189023 = 31783535) B31783535
theorem B14126015 : Blo 1468554 14126015 := bstep (se 1 (by rfl) ⟨10594511, by rfl⟩ : syracuseStep 14126015 = 21189023) B21189023
theorem B9417343 : Blo 1468554 9417343 := bstep (se 1 (by rfl) ⟨7063007, by rfl⟩ : syracuseStep 9417343 = 14126015) B14126015
theorem B12556457 : Blo 1468554 12556457 := bstep (se 2 (by rfl) ⟨4708671, by rfl⟩ : syracuseStep 12556457 = 9417343) B9417343
theorem B8370971 : Blo 1468554 8370971 := bstep (se 1 (by rfl) ⟨6278228, by rfl⟩ : syracuseStep 8370971 = 12556457) B12556457
theorem B5580647 : Blo 1468554 5580647 := bstep (se 1 (by rfl) ⟨4185485, by rfl⟩ : syracuseStep 5580647 = 8370971) B8370971
theorem B3720431 : Blo 1468554 3720431 := bstep (se 1 (by rfl) ⟨2790323, by rfl⟩ : syracuseStep 3720431 = 5580647) B5580647
theorem B2480287 : Blo 1468554 2480287 := bstep (se 1 (by rfl) ⟨1860215, by rfl⟩ : syracuseStep 2480287 = 3720431) B3720431
theorem B3307049 : Blo 1468554 3307049 := bstep (se 2 (by rfl) ⟨1240143, by rfl⟩ : syracuseStep 3307049 = 2480287) B2480287
theorem B2204699 : Blo 1468554 2204699 := bstep (se 1 (by rfl) ⟨1653524, by rfl⟩ : syracuseStep 2204699 = 3307049) B3307049
theorem B1469799 : Blo 1468554 1469799 := bstep (se 1 (by rfl) ⟨1102349, by rfl⟩ : syracuseStep 1469799 = 2204699) B2204699

theorem C0 (j : ℕ) (h1 : 367138 ≤ j) (h2 : j ≤ 367637) : Blo 1468554 (4 * j + 3) := by
  interval_cases j
  · exact B1468555
  · exact B1468559
  · exact B1468563
  · exact B1468567
  · exact B1468571
  · exact B1468575
  · exact B1468579
  · exact B1468583
  · exact B1468587
  · exact B1468591
  · exact B1468595
  · exact B1468599
  · exact B1468603
  · exact B1468607
  · exact B1468611
  · exact B1468615
  · exact B1468619
  · exact B1468623
  · exact B1468627
  · exact B1468631
  · exact B1468635
  · exact B1468639
  · exact B1468643
  · exact B1468647
  · exact B1468651
  · exact B1468655
  · exact B1468659
  · exact B1468663
  · exact B1468667
  · exact B1468671
  · exact B1468675
  · exact B1468679
  · exact B1468683
  · exact B1468687
  · exact B1468691
  · exact B1468695
  · exact B1468699
  · exact B1468703
  · exact B1468707
  · exact B1468711
  · exact B1468715
  · exact B1468719
  · exact B1468723
  · exact B1468727
  · exact B1468731
  · exact B1468735
  · exact B1468739
  · exact B1468743
  · exact B1468747
  · exact B1468751
  · exact B1468755
  · exact B1468759
  · exact B1468763
  · exact B1468767
  · exact B1468771
  · exact B1468775
  · exact B1468779
  · exact B1468783
  · exact B1468787
  · exact B1468791
  · exact B1468795
  · exact B1468799
  · exact B1468803
  · exact B1468807
  · exact B1468811
  · exact B1468815
  · exact B1468819
  · exact B1468823
  · exact B1468827
  · exact B1468831
  · exact B1468835
  · exact B1468839
  · exact B1468843
  · exact B1468847
  · exact B1468851
  · exact B1468855
  · exact B1468859
  · exact B1468863
  · exact B1468867
  · exact B1468871
  · exact B1468875
  · exact B1468879
  · exact B1468883
  · exact B1468887
  · exact B1468891
  · exact B1468895
  · exact B1468899
  · exact B1468903
  · exact B1468907
  · exact B1468911
  · exact B1468915
  · exact B1468919
  · exact B1468923
  · exact B1468927
  · exact B1468931
  · exact B1468935
  · exact B1468939
  · exact B1468943
  · exact B1468947
  · exact B1468951
  · exact B1468955
  · exact B1468959
  · exact B1468963
  · exact B1468967
  · exact B1468971
  · exact B1468975
  · exact B1468979
  · exact B1468983
  · exact B1468987
  · exact B1468991
  · exact B1468995
  · exact B1468999
  · exact B1469003
  · exact B1469007
  · exact B1469011
  · exact B1469015
  · exact B1469019
  · exact B1469023
  · exact B1469027
  · exact B1469031
  · exact B1469035
  · exact B1469039
  · exact B1469043
  · exact B1469047
  · exact B1469051
  · exact B1469055
  · exact B1469059
  · exact B1469063
  · exact B1469067
  · exact B1469071
  · exact B1469075
  · exact B1469079
  · exact B1469083
  · exact B1469087
  · exact B1469091
  · exact B1469095
  · exact B1469099
  · exact B1469103
  · exact B1469107
  · exact B1469111
  · exact B1469115
  · exact B1469119
  · exact B1469123
  · exact B1469127
  · exact B1469131
  · exact B1469135
  · exact B1469139
  · exact B1469143
  · exact B1469147
  · exact B1469151
  · exact B1469155
  · exact B1469159
  · exact B1469163
  · exact B1469167
  · exact B1469171
  · exact B1469175
  · exact B1469179
  · exact B1469183
  · exact B1469187
  · exact B1469191
  · exact B1469195
  · exact B1469199
  · exact B1469203
  · exact B1469207
  · exact B1469211
  · exact B1469215
  · exact B1469219
  · exact B1469223
  · exact B1469227
  · exact B1469231
  · exact B1469235
  · exact B1469239
  · exact B1469243
  · exact B1469247
  · exact B1469251
  · exact B1469255
  · exact B1469259
  · exact B1469263
  · exact B1469267
  · exact B1469271
  · exact B1469275
  · exact B1469279
  · exact B1469283
  · exact B1469287
  · exact B1469291
  · exact B1469295
  · exact B1469299
  · exact B1469303
  · exact B1469307
  · exact B1469311
  · exact B1469315
  · exact B1469319
  · exact B1469323
  · exact B1469327
  · exact B1469331
  · exact B1469335
  · exact B1469339
  · exact B1469343
  · exact B1469347
  · exact B1469351
  · exact B1469355
  · exact B1469359
  · exact B1469363
  · exact B1469367
  · exact B1469371
  · exact B1469375
  · exact B1469379
  · exact B1469383
  · exact B1469387
  · exact B1469391
  · exact B1469395
  · exact B1469399
  · exact B1469403
  · exact B1469407
  · exact B1469411
  · exact B1469415
  · exact B1469419
  · exact B1469423
  · exact B1469427
  · exact B1469431
  · exact B1469435
  · exact B1469439
  · exact B1469443
  · exact B1469447
  · exact B1469451
  · exact B1469455
  · exact B1469459
  · exact B1469463
  · exact B1469467
  · exact B1469471
  · exact B1469475
  · exact B1469479
  · exact B1469483
  · exact B1469487
  · exact B1469491
  · exact B1469495
  · exact B1469499
  · exact B1469503
  · exact B1469507
  · exact B1469511
  · exact B1469515
  · exact B1469519
  · exact B1469523
  · exact B1469527
  · exact B1469531
  · exact B1469535
  · exact B1469539
  · exact B1469543
  · exact B1469547
  · exact B1469551
  · exact B1469555
  · exact B1469559
  · exact B1469563
  · exact B1469567
  · exact B1469571
  · exact B1469575
  · exact B1469579
  · exact B1469583
  · exact B1469587
  · exact B1469591
  · exact B1469595
  · exact B1469599
  · exact B1469603
  · exact B1469607
  · exact B1469611
  · exact B1469615
  · exact B1469619
  · exact B1469623
  · exact B1469627
  · exact B1469631
  · exact B1469635
  · exact B1469639
  · exact B1469643
  · exact B1469647
  · exact B1469651
  · exact B1469655
  · exact B1469659
  · exact B1469663
  · exact B1469667
  · exact B1469671
  · exact B1469675
  · exact B1469679
  · exact B1469683
  · exact B1469687
  · exact B1469691
  · exact B1469695
  · exact B1469699
  · exact B1469703
  · exact B1469707
  · exact B1469711
  · exact B1469715
  · exact B1469719
  · exact B1469723
  · exact B1469727
  · exact B1469731
  · exact B1469735
  · exact B1469739
  · exact B1469743
  · exact B1469747
  · exact B1469751
  · exact B1469755
  · exact B1469759
  · exact B1469763
  · exact B1469767
  · exact B1469771
  · exact B1469775
  · exact B1469779
  · exact B1469783
  · exact B1469787
  · exact B1469791
  · exact B1469795
  · exact B1469799
  · exact B1469803
  · exact B1469807
  · exact B1469811
  · exact B1469815
  · exact B1469819
  · exact B1469823
  · exact B1469827
  · exact B1469831
  · exact B1469835
  · exact B1469839
  · exact B1469843
  · exact B1469847
  · exact B1469851
  · exact B1469855
  · exact B1469859
  · exact B1469863
  · exact B1469867
  · exact B1469871
  · exact B1469875
  · exact B1469879
  · exact B1469883
  · exact B1469887
  · exact B1469891
  · exact B1469895
  · exact B1469899
  · exact B1469903
  · exact B1469907
  · exact B1469911
  · exact B1469915
  · exact B1469919
  · exact B1469923
  · exact B1469927
  · exact B1469931
  · exact B1469935
  · exact B1469939
  · exact B1469943
  · exact B1469947
  · exact B1469951
  · exact B1469955
  · exact B1469959
  · exact B1469963
  · exact B1469967
  · exact B1469971
  · exact B1469975
  · exact B1469979
  · exact B1469983
  · exact B1469987
  · exact B1469991
  · exact B1469995
  · exact B1469999
  · exact B1470003
  · exact B1470007
  · exact B1470011
  · exact B1470015
  · exact B1470019
  · exact B1470023
  · exact B1470027
  · exact B1470031
  · exact B1470035
  · exact B1470039
  · exact B1470043
  · exact B1470047
  · exact B1470051
  · exact B1470055
  · exact B1470059
  · exact B1470063
  · exact B1470067
  · exact B1470071
  · exact B1470075
  · exact B1470079
  · exact B1470083
  · exact B1470087
  · exact B1470091
  · exact B1470095
  · exact B1470099
  · exact B1470103
  · exact B1470107
  · exact B1470111
  · exact B1470115
  · exact B1470119
  · exact B1470123
  · exact B1470127
  · exact B1470131
  · exact B1470135
  · exact B1470139
  · exact B1470143
  · exact B1470147
  · exact B1470151
  · exact B1470155
  · exact B1470159
  · exact B1470163
  · exact B1470167
  · exact B1470171
  · exact B1470175
  · exact B1470179
  · exact B1470183
  · exact B1470187
  · exact B1470191
  · exact B1470195
  · exact B1470199
  · exact B1470203
  · exact B1470207
  · exact B1470211
  · exact B1470215
  · exact B1470219
  · exact B1470223
  · exact B1470227
  · exact B1470231
  · exact B1470235
  · exact B1470239
  · exact B1470243
  · exact B1470247
  · exact B1470251
  · exact B1470255
  · exact B1470259
  · exact B1470263
  · exact B1470267
  · exact B1470271
  · exact B1470275
  · exact B1470279
  · exact B1470283
  · exact B1470287
  · exact B1470291
  · exact B1470295
  · exact B1470299
  · exact B1470303
  · exact B1470307
  · exact B1470311
  · exact B1470315
  · exact B1470319
  · exact B1470323
  · exact B1470327
  · exact B1470331
  · exact B1470335
  · exact B1470339
  · exact B1470343
  · exact B1470347
  · exact B1470351
  · exact B1470355
  · exact B1470359
  · exact B1470363
  · exact B1470367
  · exact B1470371
  · exact B1470375
  · exact B1470379
  · exact B1470383
  · exact B1470387
  · exact B1470391
  · exact B1470395
  · exact B1470399
  · exact B1470403
  · exact B1470407
  · exact B1470411
  · exact B1470415
  · exact B1470419
  · exact B1470423
  · exact B1470427
  · exact B1470431
  · exact B1470435
  · exact B1470439
  · exact B1470443
  · exact B1470447
  · exact B1470451
  · exact B1470455
  · exact B1470459
  · exact B1470463
  · exact B1470467
  · exact B1470471
  · exact B1470475
  · exact B1470479
  · exact B1470483
  · exact B1470487
  · exact B1470491
  · exact B1470495
  · exact B1470499
  · exact B1470503
  · exact B1470507
  · exact B1470511
  · exact B1470515
  · exact B1470519
  · exact B1470523
  · exact B1470527
  · exact B1470531
  · exact B1470535
  · exact B1470539
  · exact B1470543
  · exact B1470547
  · exact B1470551

theorem solution (m : ℕ) (hlo : 1468554 ≤ m) (hhi : m ≤ 1470554) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 367138 ≤ j := by omega
    have hj2 : j ≤ 367637 := by omega
    have hb : Blo 1468554 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
