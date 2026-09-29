-- Prove2me | solution 1 for syracuse_descends_range_1545470_1547470
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:24.751445+00:00
-- url     : https://prove2.me/submissions/36abb539-613c-4f07-a606-5af59f852c61

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


theorem B3481613 : Blo 1545470 3481613 := bbase (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) (by norm_num)
theorem B2318357 : Blo 1545470 2318357 := bbase (se 6 (by rfl) ⟨54336, by rfl⟩ : syracuseStep 2318357 = 108673) (by norm_num)
theorem B2318381 : Blo 1545470 2318381 := bbase (se 3 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 2318381 = 869393) (by norm_num)
theorem B2318405 : Blo 1545470 2318405 := bbase (se 4 (by rfl) ⟨217350, by rfl⟩ : syracuseStep 2318405 = 434701) (by norm_num)
theorem B3481685 : Blo 1545470 3481685 := bbase (se 8 (by rfl) ⟨20400, by rfl⟩ : syracuseStep 3481685 = 40801) (by norm_num)
theorem B2318429 : Blo 1545470 2318429 := bbase (se 3 (by rfl) ⟨434705, by rfl⟩ : syracuseStep 2318429 = 869411) (by norm_num)
theorem B2318453 : Blo 1545470 2318453 := bbase (se 5 (by rfl) ⟨108677, by rfl⟩ : syracuseStep 2318453 = 217355) (by norm_num)
theorem B2318477 : Blo 1545470 2318477 := bbase (se 3 (by rfl) ⟨434714, by rfl⟩ : syracuseStep 2318477 = 869429) (by norm_num)
theorem B1958033 : Blo 1545470 1958033 := bbase (se 2 (by rfl) ⟨734262, by rfl⟩ : syracuseStep 1958033 = 1468525) (by norm_num)
theorem B2351261 : Blo 1545470 2351261 := bbase (se 3 (by rfl) ⟨440861, by rfl⟩ : syracuseStep 2351261 = 881723) (by norm_num)
theorem B3481757 : Blo 1545470 3481757 := bbase (se 3 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 3481757 = 1305659) (by norm_num)
theorem B2318501 : Blo 1545470 2318501 := bbase (se 4 (by rfl) ⟨217359, by rfl⟩ : syracuseStep 2318501 = 434719) (by norm_num)
theorem B2318525 : Blo 1545470 2318525 := bbase (se 3 (by rfl) ⟨434723, by rfl⟩ : syracuseStep 2318525 = 869447) (by norm_num)
theorem B3915965 : Blo 1545470 3915965 := bbase (se 3 (by rfl) ⟨734243, by rfl⟩ : syracuseStep 3915965 = 1468487) (by norm_num)
theorem B6267077 : Blo 1545470 6267077 := bbase (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) (by norm_num)
theorem B1958089 : Blo 1545470 1958089 := bbase (se 2 (by rfl) ⟨734283, by rfl⟩ : syracuseStep 1958089 = 1468567) (by norm_num)
theorem B2318549 : Blo 1545470 2318549 := bbase (se 7 (by rfl) ⟨27170, by rfl⟩ : syracuseStep 2318549 = 54341) (by norm_num)
theorem B2318573 : Blo 1545470 2318573 := bbase (se 3 (by rfl) ⟨434732, by rfl⟩ : syracuseStep 2318573 = 869465) (by norm_num)
theorem B14106869 : Blo 1545470 14106869 := bbase (se 5 (by rfl) ⟨661259, by rfl⟩ : syracuseStep 14106869 = 1322519) (by norm_num)
theorem B2318597 : Blo 1545470 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B2318621 : Blo 1545470 2318621 := bbase (se 3 (by rfl) ⟨434741, by rfl⟩ : syracuseStep 2318621 = 869483) (by norm_num)
theorem B1958185 : Blo 1545470 1958185 := bbase (se 2 (by rfl) ⟨734319, by rfl⟩ : syracuseStep 1958185 = 1468639) (by norm_num)
theorem B2318645 : Blo 1545470 2318645 := bbase (se 5 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 2318645 = 217373) (by norm_num)
theorem B5218613 : Blo 1545470 5218613 := bbase (se 5 (by rfl) ⟨244622, by rfl⟩ : syracuseStep 5218613 = 489245) (by norm_num)
theorem B2974013 : Blo 1545470 2974013 := bbase (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) (by norm_num)
theorem B2318669 : Blo 1545470 2318669 := bbase (se 3 (by rfl) ⟨434750, by rfl⟩ : syracuseStep 2318669 = 869501) (by norm_num)
theorem B16712021 : Blo 1545470 16712021 := bbase (se 10 (by rfl) ⟨24480, by rfl⟩ : syracuseStep 16712021 = 48961) (by norm_num)
theorem B2318693 : Blo 1545470 2318693 := bbase (se 4 (by rfl) ⟨217377, by rfl⟩ : syracuseStep 2318693 = 434755) (by norm_num)
theorem B2646373 : Blo 1545470 2646373 := bbase (se 4 (by rfl) ⟨248097, by rfl⟩ : syracuseStep 2646373 = 496195) (by norm_num)
theorem B2318717 : Blo 1545470 2318717 := bbase (se 3 (by rfl) ⟨434759, by rfl⟩ : syracuseStep 2318717 = 869519) (by norm_num)
theorem B4178309 : Blo 1545470 4178309 := bbase (se 4 (by rfl) ⟨391716, by rfl⟩ : syracuseStep 4178309 = 783433) (by norm_num)
theorem B2646413 : Blo 1545470 2646413 := bbase (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) (by norm_num)
theorem B2318741 : Blo 1545470 2318741 := bbase (se 6 (by rfl) ⟨54345, by rfl⟩ : syracuseStep 2318741 = 108691) (by norm_num)
theorem B2318765 : Blo 1545470 2318765 := bbase (se 3 (by rfl) ⟨434768, by rfl⟩ : syracuseStep 2318765 = 869537) (by norm_num)
theorem B2318789 : Blo 1545470 2318789 := bbase (se 4 (by rfl) ⟨217386, by rfl⟩ : syracuseStep 2318789 = 434773) (by norm_num)
theorem B6603221 : Blo 1545470 6603221 := bbase (se 7 (by rfl) ⟨77381, by rfl⟩ : syracuseStep 6603221 = 154763) (by norm_num)
theorem B1958357 : Blo 1545470 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B2318813 : Blo 1545470 2318813 := bbase (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) (by norm_num)
theorem B2318837 : Blo 1545470 2318837 := bbase (se 5 (by rfl) ⟨108695, by rfl⟩ : syracuseStep 2318837 = 217391) (by norm_num)
theorem B2318861 : Blo 1545470 2318861 := bbase (se 3 (by rfl) ⟨434786, by rfl⟩ : syracuseStep 2318861 = 869573) (by norm_num)
theorem B1958413 : Blo 1545470 1958413 := bbase (se 3 (by rfl) ⟨367202, by rfl⟩ : syracuseStep 1958413 = 734405) (by norm_num)
theorem B3916309 : Blo 1545470 3916309 := bbase (se 6 (by rfl) ⟨91788, by rfl⟩ : syracuseStep 3916309 = 183577) (by norm_num)
theorem B2318885 : Blo 1545470 2318885 := bbase (se 4 (by rfl) ⟨217395, by rfl⟩ : syracuseStep 2318885 = 434791) (by norm_num)
theorem B2318909 : Blo 1545470 2318909 := bbase (se 3 (by rfl) ⟨434795, by rfl⟩ : syracuseStep 2318909 = 869591) (by norm_num)
theorem B2318933 : Blo 1545470 2318933 := bbase (se 8 (by rfl) ⟨13587, by rfl⟩ : syracuseStep 2318933 = 27175) (by norm_num)
theorem B2318957 : Blo 1545470 2318957 := bbase (se 3 (by rfl) ⟨434804, by rfl⟩ : syracuseStep 2318957 = 869609) (by norm_num)
theorem B1958509 : Blo 1545470 1958509 := bbase (se 3 (by rfl) ⟨367220, by rfl⟩ : syracuseStep 1958509 = 734441) (by norm_num)
theorem B2318981 : Blo 1545470 2318981 := bbase (se 4 (by rfl) ⟨217404, by rfl⟩ : syracuseStep 2318981 = 434809) (by norm_num)
theorem B3302021 : Blo 1545470 3302021 := bbase (se 4 (by rfl) ⟨309564, by rfl⟩ : syracuseStep 3302021 = 619129) (by norm_num)
theorem B3916421 : Blo 1545470 3916421 := bbase (se 4 (by rfl) ⟨367164, by rfl⟩ : syracuseStep 3916421 = 734329) (by norm_num)
theorem B7832213 : Blo 1545470 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B2319005 : Blo 1545470 2319005 := bbase (se 3 (by rfl) ⟨434813, by rfl⟩ : syracuseStep 2319005 = 869627) (by norm_num)
theorem B2319029 : Blo 1545470 2319029 := bbase (se 5 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 2319029 = 217409) (by norm_num)
theorem B2319053 : Blo 1545470 2319053 := bbase (se 3 (by rfl) ⟨434822, by rfl⟩ : syracuseStep 2319053 = 869645) (by norm_num)
theorem B5874389 : Blo 1545470 5874389 := bbase (se 7 (by rfl) ⟨68840, by rfl⟩ : syracuseStep 5874389 = 137681) (by norm_num)
theorem B2319077 : Blo 1545470 2319077 := bbase (se 4 (by rfl) ⟨217413, by rfl⟩ : syracuseStep 2319077 = 434827) (by norm_num)
theorem B5219045 : Blo 1545470 5219045 := bbase (se 4 (by rfl) ⟨489285, by rfl⟩ : syracuseStep 5219045 = 978571) (by norm_num)
theorem B2319101 : Blo 1545470 2319101 := bbase (se 3 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 2319101 = 869663) (by norm_num)
theorem B2319125 : Blo 1545470 2319125 := bbase (se 6 (by rfl) ⟨54354, by rfl⟩ : syracuseStep 2319125 = 108709) (by norm_num)
theorem B3302165 : Blo 1545470 3302165 := bbase (se 6 (by rfl) ⟨77394, by rfl⟩ : syracuseStep 3302165 = 154789) (by norm_num)
theorem B2319149 : Blo 1545470 2319149 := bbase (se 3 (by rfl) ⟨434840, by rfl⟩ : syracuseStep 2319149 = 869681) (by norm_num)
theorem B2089781 : Blo 1545470 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B15876917 : Blo 1545470 15876917 := bbase (se 5 (by rfl) ⟨744230, by rfl⟩ : syracuseStep 15876917 = 1488461) (by norm_num)
theorem B2319173 : Blo 1545470 2319173 := bbase (se 4 (by rfl) ⟨217422, by rfl⟩ : syracuseStep 2319173 = 434845) (by norm_num)
theorem B3916613 : Blo 1545470 3916613 := bbase (se 4 (by rfl) ⟨367182, by rfl⟩ : syracuseStep 3916613 = 734365) (by norm_num)
theorem B7054165 : Blo 1545470 7054165 := bbase (se 9 (by rfl) ⟨20666, by rfl⟩ : syracuseStep 7054165 = 41333) (by norm_num)
theorem B2319197 : Blo 1545470 2319197 := bbase (se 3 (by rfl) ⟨434849, by rfl⟩ : syracuseStep 2319197 = 869699) (by norm_num)
theorem B7054181 : Blo 1545470 7054181 := bbase (se 4 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 7054181 = 1322659) (by norm_num)
theorem B2319221 : Blo 1545470 2319221 := bbase (se 5 (by rfl) ⟨108713, by rfl⟩ : syracuseStep 2319221 = 217427) (by norm_num)
theorem B2319245 : Blo 1545470 2319245 := bbase (se 3 (by rfl) ⟨434858, by rfl⟩ : syracuseStep 2319245 = 869717) (by norm_num)
theorem B2319269 : Blo 1545470 2319269 := bbase (se 4 (by rfl) ⟨217431, by rfl⟩ : syracuseStep 2319269 = 434863) (by norm_num)
theorem B2319293 : Blo 1545470 2319293 := bbase (se 3 (by rfl) ⟨434867, by rfl⟩ : syracuseStep 2319293 = 869735) (by norm_num)
theorem B2319317 : Blo 1545470 2319317 := bbase (se 7 (by rfl) ⟨27179, by rfl⟩ : syracuseStep 2319317 = 54359) (by norm_num)
theorem B2319341 : Blo 1545470 2319341 := bbase (se 3 (by rfl) ⟨434876, by rfl⟩ : syracuseStep 2319341 = 869753) (by norm_num)
theorem B8807413 : Blo 1545470 8807413 := bbase (se 5 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 8807413 = 825695) (by norm_num)
theorem B5874677 : Blo 1545470 5874677 := bbase (se 5 (by rfl) ⟨275375, by rfl⟩ : syracuseStep 5874677 = 550751) (by norm_num)
theorem B2319365 : Blo 1545470 2319365 := bbase (se 4 (by rfl) ⟨217440, by rfl⟩ : syracuseStep 2319365 = 434881) (by norm_num)
theorem B2319389 : Blo 1545470 2319389 := bbase (se 3 (by rfl) ⟨434885, by rfl⟩ : syracuseStep 2319389 = 869771) (by norm_num)
theorem B7824437 : Blo 1545470 7824437 := bbase (se 5 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 7824437 = 733541) (by norm_num)
theorem B2319413 : Blo 1545470 2319413 := bbase (se 5 (by rfl) ⟨108722, by rfl⟩ : syracuseStep 2319413 = 217445) (by norm_num)
theorem B2319437 : Blo 1545470 2319437 := bbase (se 3 (by rfl) ⟨434894, by rfl⟩ : syracuseStep 2319437 = 869789) (by norm_num)
theorem B5022805 : Blo 1545470 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B2319461 : Blo 1545470 2319461 := bbase (se 4 (by rfl) ⟨217449, by rfl⟩ : syracuseStep 2319461 = 434899) (by norm_num)
theorem B3302525 : Blo 1545470 3302525 := bbase (se 3 (by rfl) ⟨619223, by rfl⟩ : syracuseStep 3302525 = 1238447) (by norm_num)
theorem B2319485 : Blo 1545470 2319485 := bbase (se 3 (by rfl) ⟨434903, by rfl⟩ : syracuseStep 2319485 = 869807) (by norm_num)
theorem B2319509 : Blo 1545470 2319509 := bbase (se 6 (by rfl) ⟨54363, by rfl⟩ : syracuseStep 2319509 = 108727) (by norm_num)
theorem B5219477 : Blo 1545470 5219477 := bbase (se 6 (by rfl) ⟨122331, by rfl⟩ : syracuseStep 5219477 = 244663) (by norm_num)
theorem B3916957 : Blo 1545470 3916957 := bbase (se 3 (by rfl) ⟨734429, by rfl⟩ : syracuseStep 3916957 = 1468859) (by norm_num)
theorem B2319533 : Blo 1545470 2319533 := bbase (se 3 (by rfl) ⟨434912, by rfl⟩ : syracuseStep 2319533 = 869825) (by norm_num)
theorem B2319557 : Blo 1545470 2319557 := bbase (se 4 (by rfl) ⟨217458, by rfl⟩ : syracuseStep 2319557 = 434917) (by norm_num)
theorem B2319581 : Blo 1545470 2319581 := bbase (se 3 (by rfl) ⟨434921, by rfl⟩ : syracuseStep 2319581 = 869843) (by norm_num)
theorem B2319605 : Blo 1545470 2319605 := bbase (se 5 (by rfl) ⟨108731, by rfl⟩ : syracuseStep 2319605 = 217463) (by norm_num)
theorem B2319629 : Blo 1545470 2319629 := bbase (se 3 (by rfl) ⟨434930, by rfl⟩ : syracuseStep 2319629 = 869861) (by norm_num)
theorem B2319653 : Blo 1545470 2319653 := bbase (se 4 (by rfl) ⟨217467, by rfl⟩ : syracuseStep 2319653 = 434935) (by norm_num)
theorem B2319677 : Blo 1545470 2319677 := bbase (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) (by norm_num)
theorem B2319701 : Blo 1545470 2319701 := bbase (se 12 (by rfl) ⟨849, by rfl⟩ : syracuseStep 2319701 = 1699) (by norm_num)
theorem B2319725 : Blo 1545470 2319725 := bbase (se 3 (by rfl) ⟨434948, by rfl⟩ : syracuseStep 2319725 = 869897) (by norm_num)
theorem B2319749 : Blo 1545470 2319749 := bbase (se 4 (by rfl) ⟨217476, by rfl⟩ : syracuseStep 2319749 = 434953) (by norm_num)
theorem B2934157 : Blo 1545470 2934157 := bbase (se 3 (by rfl) ⟨550154, by rfl⟩ : syracuseStep 2934157 = 1100309) (by norm_num)
theorem B2319773 : Blo 1545470 2319773 := bbase (se 3 (by rfl) ⟨434957, by rfl⟩ : syracuseStep 2319773 = 869915) (by norm_num)
theorem B14853557 : Blo 1545470 14853557 := bbase (se 5 (by rfl) ⟨696260, by rfl⟩ : syracuseStep 14853557 = 1392521) (by norm_num)
theorem B2319797 : Blo 1545470 2319797 := bbase (se 5 (by rfl) ⟨108740, by rfl⟩ : syracuseStep 2319797 = 217481) (by norm_num)
theorem B2319821 : Blo 1545470 2319821 := bbase (se 3 (by rfl) ⟨434966, by rfl⟩ : syracuseStep 2319821 = 869933) (by norm_num)
theorem B1762789 : Blo 1545470 1762789 := bbase (se 4 (by rfl) ⟨165261, by rfl⟩ : syracuseStep 1762789 = 330523) (by norm_num)
theorem B2319845 : Blo 1545470 2319845 := bbase (se 4 (by rfl) ⟨217485, by rfl⟩ : syracuseStep 2319845 = 434971) (by norm_num)
theorem B13215221 : Blo 1545470 13215221 := bbase (se 5 (by rfl) ⟨619463, by rfl⟩ : syracuseStep 13215221 = 1238927) (by norm_num)
theorem B2319869 : Blo 1545470 2319869 := bbase (se 3 (by rfl) ⟨434975, by rfl⟩ : syracuseStep 2319869 = 869951) (by norm_num)
theorem B2319893 : Blo 1545470 2319893 := bbase (se 6 (by rfl) ⟨54372, by rfl⟩ : syracuseStep 2319893 = 108745) (by norm_num)
theorem B9913877 : Blo 1545470 9913877 := bbase (se 6 (by rfl) ⟨232356, by rfl⟩ : syracuseStep 9913877 = 464713) (by norm_num)
theorem B2934301 : Blo 1545470 2934301 := bbase (se 3 (by rfl) ⟨550181, by rfl⟩ : syracuseStep 2934301 = 1100363) (by norm_num)
theorem B2319917 : Blo 1545470 2319917 := bbase (se 3 (by rfl) ⟨434984, by rfl⟩ : syracuseStep 2319917 = 869969) (by norm_num)
theorem B2319941 : Blo 1545470 2319941 := bbase (se 4 (by rfl) ⟨217494, by rfl⟩ : syracuseStep 2319941 = 434989) (by norm_num)
theorem B5219909 : Blo 1545470 5219909 := bbase (se 4 (by rfl) ⟨489366, by rfl⟩ : syracuseStep 5219909 = 978733) (by norm_num)
theorem B1762889 : Blo 1545470 1762889 := bbase (se 2 (by rfl) ⟨661083, by rfl⟩ : syracuseStep 1762889 = 1322167) (by norm_num)
theorem B28231253 : Blo 1545470 28231253 := bbase (se 8 (by rfl) ⟨165417, by rfl⟩ : syracuseStep 28231253 = 330835) (by norm_num)
theorem B2319965 : Blo 1545470 2319965 := bbase (se 3 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 2319965 = 869987) (by norm_num)
theorem B13207157 : Blo 1545470 13207157 := bbase (se 5 (by rfl) ⟨619085, by rfl⟩ : syracuseStep 13207157 = 1238171) (by norm_num)
theorem B2319989 : Blo 1545470 2319989 := bbase (se 5 (by rfl) ⟨108749, by rfl⟩ : syracuseStep 2319989 = 217499) (by norm_num)
theorem B2320013 : Blo 1545470 2320013 := bbase (se 3 (by rfl) ⟨435002, by rfl⟩ : syracuseStep 2320013 = 870005) (by norm_num)
theorem B1762961 : Blo 1545470 1762961 := bbase (se 2 (by rfl) ⟨661110, by rfl⟩ : syracuseStep 1762961 = 1322221) (by norm_num)
theorem B2320037 : Blo 1545470 2320037 := bbase (se 4 (by rfl) ⟨217503, by rfl⟩ : syracuseStep 2320037 = 435007) (by norm_num)
theorem B2934461 : Blo 1545470 2934461 := bbase (se 3 (by rfl) ⟨550211, by rfl⟩ : syracuseStep 2934461 = 1100423) (by norm_num)
theorem B2320061 : Blo 1545470 2320061 := bbase (se 3 (by rfl) ⟨435011, by rfl⟩ : syracuseStep 2320061 = 870023) (by norm_num)
theorem B2090701 : Blo 1545470 2090701 := bbase (se 3 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 2090701 = 784013) (by norm_num)
theorem B2320085 : Blo 1545470 2320085 := bbase (se 7 (by rfl) ⟨27188, by rfl⟩ : syracuseStep 2320085 = 54377) (by norm_num)
theorem B2320109 : Blo 1545470 2320109 := bbase (se 3 (by rfl) ⟨435020, by rfl⟩ : syracuseStep 2320109 = 870041) (by norm_num)
theorem B1836805 : Blo 1545470 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B2320133 : Blo 1545470 2320133 := bbase (se 4 (by rfl) ⟨217512, by rfl⟩ : syracuseStep 2320133 = 435025) (by norm_num)
theorem B12535573 : Blo 1545470 12535573 := bbase (se 6 (by rfl) ⟨293802, by rfl⟩ : syracuseStep 12535573 = 587605) (by norm_num)
theorem B2320157 : Blo 1545470 2320157 := bbase (se 3 (by rfl) ⟨435029, by rfl⟩ : syracuseStep 2320157 = 870059) (by norm_num)
theorem B2320181 : Blo 1545470 2320181 := bbase (se 5 (by rfl) ⟨108758, by rfl⟩ : syracuseStep 2320181 = 217517) (by norm_num)
theorem B2934605 : Blo 1545470 2934605 := bbase (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) (by norm_num)
theorem B2320205 : Blo 1545470 2320205 := bbase (se 3 (by rfl) ⟨435038, by rfl⟩ : syracuseStep 2320205 = 870077) (by norm_num)
theorem B2320229 : Blo 1545470 2320229 := bbase (se 4 (by rfl) ⟨217521, by rfl⟩ : syracuseStep 2320229 = 435043) (by norm_num)
theorem B2320253 : Blo 1545470 2320253 := bbase (se 3 (by rfl) ⟨435047, by rfl⟩ : syracuseStep 2320253 = 870095) (by norm_num)
theorem B4179845 : Blo 1545470 4179845 := bbase (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) (by norm_num)
theorem B2320277 : Blo 1545470 2320277 := bbase (se 6 (by rfl) ⟨54381, by rfl⟩ : syracuseStep 2320277 = 108763) (by norm_num)
theorem B7833509 : Blo 1545470 7833509 := bbase (se 4 (by rfl) ⟨734391, by rfl⟩ : syracuseStep 7833509 = 1468783) (by norm_num)
theorem B1738669 : Blo 1545470 1738669 := bbase (se 3 (by rfl) ⟨326000, by rfl⟩ : syracuseStep 1738669 = 652001) (by norm_num)
theorem B2320301 : Blo 1545470 2320301 := bbase (se 3 (by rfl) ⟨435056, by rfl⟩ : syracuseStep 2320301 = 870113) (by norm_num)
theorem B2787269 : Blo 1545470 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B2320325 : Blo 1545470 2320325 := bbase (se 4 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 2320325 = 435061) (by norm_num)
theorem B1738705 : Blo 1545470 1738705 := bbase (se 2 (by rfl) ⟨652014, by rfl⟩ : syracuseStep 1738705 = 1304029) (by norm_num)
theorem B2320349 : Blo 1545470 2320349 := bbase (se 3 (by rfl) ⟨435065, by rfl⟩ : syracuseStep 2320349 = 870131) (by norm_num)
theorem B1763309 : Blo 1545470 1763309 := bbase (se 3 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 1763309 = 661241) (by norm_num)
theorem B1738741 : Blo 1545470 1738741 := bbase (se 5 (by rfl) ⟨81503, by rfl⟩ : syracuseStep 1738741 = 163007) (by norm_num)
theorem B3303413 : Blo 1545470 3303413 := bbase (se 5 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 3303413 = 309695) (by norm_num)
theorem B5220341 : Blo 1545470 5220341 := bbase (se 5 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 5220341 = 489407) (by norm_num)
theorem B2320373 : Blo 1545470 2320373 := bbase (se 5 (by rfl) ⟨108767, by rfl⟩ : syracuseStep 2320373 = 217535) (by norm_num)
theorem B4466677 : Blo 1545470 4466677 := bbase (se 5 (by rfl) ⟨209375, by rfl⟩ : syracuseStep 4466677 = 418751) (by norm_num)
theorem B2320397 : Blo 1545470 2320397 := bbase (se 3 (by rfl) ⟨435074, by rfl⟩ : syracuseStep 2320397 = 870149) (by norm_num)
theorem B4769813 : Blo 1545470 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1738777 : Blo 1545470 1738777 := bbase (se 2 (by rfl) ⟨652041, by rfl⟩ : syracuseStep 1738777 = 1304083) (by norm_num)
theorem B2320421 : Blo 1545470 2320421 := bbase (se 4 (by rfl) ⟨217539, by rfl⟩ : syracuseStep 2320421 = 435079) (by norm_num)
theorem B1738813 : Blo 1545470 1738813 := bbase (se 3 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 1738813 = 652055) (by norm_num)
theorem B2320445 : Blo 1545470 2320445 := bbase (se 3 (by rfl) ⟨435083, by rfl⟩ : syracuseStep 2320445 = 870167) (by norm_num)
theorem B2320469 : Blo 1545470 2320469 := bbase (se 8 (by rfl) ⟨13596, by rfl⟩ : syracuseStep 2320469 = 27193) (by norm_num)
theorem B1738849 : Blo 1545470 1738849 := bbase (se 2 (by rfl) ⟨652068, by rfl⟩ : syracuseStep 1738849 = 1304137) (by norm_num)
theorem B2934893 : Blo 1545470 2934893 := bbase (se 3 (by rfl) ⟨550292, by rfl⟩ : syracuseStep 2934893 = 1100585) (by norm_num)
theorem B2320493 : Blo 1545470 2320493 := bbase (se 3 (by rfl) ⟨435092, by rfl⟩ : syracuseStep 2320493 = 870185) (by norm_num)
theorem B1738885 : Blo 1545470 1738885 := bbase (se 4 (by rfl) ⟨163020, by rfl⟩ : syracuseStep 1738885 = 326041) (by norm_num)
theorem B1984645 : Blo 1545470 1984645 := bbase (se 4 (by rfl) ⟨186060, by rfl⟩ : syracuseStep 1984645 = 372121) (by norm_num)
theorem B2320517 : Blo 1545470 2320517 := bbase (se 4 (by rfl) ⟨217548, by rfl⟩ : syracuseStep 2320517 = 435097) (by norm_num)
theorem B2320541 : Blo 1545470 2320541 := bbase (se 3 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 2320541 = 870203) (by norm_num)
theorem B1738921 : Blo 1545470 1738921 := bbase (se 2 (by rfl) ⟨652095, by rfl⟩ : syracuseStep 1738921 = 1304191) (by norm_num)
theorem B2320565 : Blo 1545470 2320565 := bbase (se 5 (by rfl) ⟨108776, by rfl⟩ : syracuseStep 2320565 = 217553) (by norm_num)
theorem B1738957 : Blo 1545470 1738957 := bbase (se 3 (by rfl) ⟨326054, by rfl⟩ : syracuseStep 1738957 = 652109) (by norm_num)
theorem B2320589 : Blo 1545470 2320589 := bbase (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) (by norm_num)
theorem B2320613 : Blo 1545470 2320613 := bbase (se 4 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 2320613 = 435115) (by norm_num)
theorem B3303661 : Blo 1545470 3303661 := bbase (se 3 (by rfl) ⟨619436, by rfl⟩ : syracuseStep 3303661 = 1238873) (by norm_num)
theorem B1738993 : Blo 1545470 1738993 := bbase (se 2 (by rfl) ⟨652122, by rfl⟩ : syracuseStep 1738993 = 1304245) (by norm_num)
theorem B5572853 : Blo 1545470 5572853 := bbase (se 5 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 5572853 = 522455) (by norm_num)
theorem B2091253 : Blo 1545470 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B2320637 : Blo 1545470 2320637 := bbase (se 3 (by rfl) ⟨435119, by rfl⟩ : syracuseStep 2320637 = 870239) (by norm_num)
theorem B2935045 : Blo 1545470 2935045 := bbase (se 4 (by rfl) ⟨275160, by rfl⟩ : syracuseStep 2935045 = 550321) (by norm_num)
theorem B7932181 : Blo 1545470 7932181 := bbase (se 6 (by rfl) ⟨185910, by rfl⟩ : syracuseStep 7932181 = 371821) (by norm_num)
theorem B1739029 : Blo 1545470 1739029 := bbase (se 6 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 1739029 = 81517) (by norm_num)
theorem B2320661 : Blo 1545470 2320661 := bbase (se 6 (by rfl) ⟨54390, by rfl⟩ : syracuseStep 2320661 = 108781) (by norm_num)
theorem B2320685 : Blo 1545470 2320685 := bbase (se 3 (by rfl) ⟨435128, by rfl⟩ : syracuseStep 2320685 = 870257) (by norm_num)
theorem B2091317 : Blo 1545470 2091317 := bbase (se 5 (by rfl) ⟨98030, by rfl⟩ : syracuseStep 2091317 = 196061) (by norm_num)
theorem B1739065 : Blo 1545470 1739065 := bbase (se 2 (by rfl) ⟨652149, by rfl⟩ : syracuseStep 1739065 = 1304299) (by norm_num)
theorem B7825733 : Blo 1545470 7825733 := bbase (se 4 (by rfl) ⟨733662, by rfl⟩ : syracuseStep 7825733 = 1467325) (by norm_num)
theorem B2320709 : Blo 1545470 2320709 := bbase (se 4 (by rfl) ⟨217566, by rfl⟩ : syracuseStep 2320709 = 435133) (by norm_num)
theorem B60229973 : Blo 1545470 60229973 := bbase (se 10 (by rfl) ⟨88227, by rfl⟩ : syracuseStep 60229973 = 176455) (by norm_num)
theorem B1739101 : Blo 1545470 1739101 := bbase (se 3 (by rfl) ⟨326081, by rfl⟩ : syracuseStep 1739101 = 652163) (by norm_num)
theorem B2320733 : Blo 1545470 2320733 := bbase (se 3 (by rfl) ⟨435137, by rfl⟩ : syracuseStep 2320733 = 870275) (by norm_num)
theorem B2320757 : Blo 1545470 2320757 := bbase (se 5 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 2320757 = 217571) (by norm_num)
theorem B1739137 : Blo 1545470 1739137 := bbase (se 2 (by rfl) ⟨652176, by rfl⟩ : syracuseStep 1739137 = 1304353) (by norm_num)
theorem B2320781 : Blo 1545470 2320781 := bbase (se 3 (by rfl) ⟨435146, by rfl⟩ : syracuseStep 2320781 = 870293) (by norm_num)
theorem B1739173 : Blo 1545470 1739173 := bbase (se 4 (by rfl) ⟨163047, by rfl⟩ : syracuseStep 1739173 = 326095) (by norm_num)
theorem B5220773 : Blo 1545470 5220773 := bbase (se 4 (by rfl) ⟨489447, by rfl⟩ : syracuseStep 5220773 = 978895) (by norm_num)
theorem B2320805 : Blo 1545470 2320805 := bbase (se 4 (by rfl) ⟨217575, by rfl⟩ : syracuseStep 2320805 = 435151) (by norm_num)
theorem B2320829 : Blo 1545470 2320829 := bbase (se 3 (by rfl) ⟨435155, by rfl⟩ : syracuseStep 2320829 = 870311) (by norm_num)
theorem B1739209 : Blo 1545470 1739209 := bbase (se 2 (by rfl) ⟨652203, by rfl⟩ : syracuseStep 1739209 = 1304407) (by norm_num)
theorem B2320853 : Blo 1545470 2320853 := bbase (se 7 (by rfl) ⟨27197, by rfl⟩ : syracuseStep 2320853 = 54395) (by norm_num)
theorem B1739245 : Blo 1545470 1739245 := bbase (se 3 (by rfl) ⟨326108, by rfl⟩ : syracuseStep 1739245 = 652217) (by norm_num)
theorem B2320877 : Blo 1545470 2320877 := bbase (se 3 (by rfl) ⟨435164, by rfl⟩ : syracuseStep 2320877 = 870329) (by norm_num)
theorem B5024261 : Blo 1545470 5024261 := bbase (se 4 (by rfl) ⟨471024, by rfl⟩ : syracuseStep 5024261 = 942049) (by norm_num)
theorem B2320901 : Blo 1545470 2320901 := bbase (se 4 (by rfl) ⟨217584, by rfl⟩ : syracuseStep 2320901 = 435169) (by norm_num)
theorem B1739281 : Blo 1545470 1739281 := bbase (se 2 (by rfl) ⟨652230, by rfl⟩ : syracuseStep 1739281 = 1304461) (by norm_num)
theorem B2320925 : Blo 1545470 2320925 := bbase (se 3 (by rfl) ⟨435173, by rfl⟩ : syracuseStep 2320925 = 870347) (by norm_num)
theorem B5868085 : Blo 1545470 5868085 := bbase (se 5 (by rfl) ⟨275066, by rfl⟩ : syracuseStep 5868085 = 550133) (by norm_num)
theorem B1739317 : Blo 1545470 1739317 := bbase (se 5 (by rfl) ⟨81530, by rfl⟩ : syracuseStep 1739317 = 163061) (by norm_num)
theorem B2935349 : Blo 1545470 2935349 := bbase (se 5 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 2935349 = 275189) (by norm_num)
theorem B1763893 : Blo 1545470 1763893 := bbase (se 5 (by rfl) ⟨82682, by rfl⟩ : syracuseStep 1763893 = 165365) (by norm_num)
theorem B2320949 : Blo 1545470 2320949 := bbase (se 5 (by rfl) ⟨108794, by rfl⟩ : syracuseStep 2320949 = 217589) (by norm_num)
theorem B2320973 : Blo 1545470 2320973 := bbase (se 3 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 2320973 = 870365) (by norm_num)
theorem B1739353 : Blo 1545470 1739353 := bbase (se 2 (by rfl) ⟨652257, by rfl⟩ : syracuseStep 1739353 = 1304515) (by norm_num)
theorem B3713629 : Blo 1545470 3713629 := bbase (se 3 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 3713629 = 1392611) (by norm_num)
theorem B1567333 : Blo 1545470 1567333 := bbase (se 4 (by rfl) ⟨146937, by rfl⟩ : syracuseStep 1567333 = 293875) (by norm_num)
theorem B2320997 : Blo 1545470 2320997 := bbase (se 4 (by rfl) ⟨217593, by rfl⟩ : syracuseStep 2320997 = 435187) (by norm_num)
theorem B1739389 : Blo 1545470 1739389 := bbase (se 3 (by rfl) ⟨326135, by rfl⟩ : syracuseStep 1739389 = 652271) (by norm_num)
theorem B2321021 : Blo 1545470 2321021 := bbase (se 3 (by rfl) ⟨435191, by rfl⟩ : syracuseStep 2321021 = 870383) (by norm_num)
theorem B2321045 : Blo 1545470 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B1739425 : Blo 1545470 1739425 := bbase (se 2 (by rfl) ⟨652284, by rfl⟩ : syracuseStep 1739425 = 1304569) (by norm_num)
theorem B2321069 : Blo 1545470 2321069 := bbase (se 3 (by rfl) ⟨435200, by rfl⟩ : syracuseStep 2321069 = 870401) (by norm_num)
theorem B1739461 : Blo 1545470 1739461 := bbase (se 4 (by rfl) ⟨163074, by rfl⟩ : syracuseStep 1739461 = 326149) (by norm_num)
theorem B2321093 : Blo 1545470 2321093 := bbase (se 4 (by rfl) ⟨217602, by rfl⟩ : syracuseStep 2321093 = 435205) (by norm_num)
theorem B2321117 : Blo 1545470 2321117 := bbase (se 3 (by rfl) ⟨435209, by rfl⟩ : syracuseStep 2321117 = 870419) (by norm_num)
theorem B3304165 : Blo 1545470 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B1739497 : Blo 1545470 1739497 := bbase (se 2 (by rfl) ⟨652311, by rfl⟩ : syracuseStep 1739497 = 1304623) (by norm_num)
theorem B2321141 : Blo 1545470 2321141 := bbase (se 5 (by rfl) ⟨108803, by rfl⟩ : syracuseStep 2321141 = 217607) (by norm_num)
theorem B1739533 : Blo 1545470 1739533 := bbase (se 3 (by rfl) ⟨326162, by rfl⟩ : syracuseStep 1739533 = 652325) (by norm_num)
theorem B2321165 : Blo 1545470 2321165 := bbase (se 3 (by rfl) ⟨435218, by rfl⟩ : syracuseStep 2321165 = 870437) (by norm_num)
theorem B2476829 : Blo 1545470 2476829 := bbase (se 3 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 2476829 = 928811) (by norm_num)
theorem B2321189 : Blo 1545470 2321189 := bbase (se 4 (by rfl) ⟨217611, by rfl⟩ : syracuseStep 2321189 = 435223) (by norm_num)
theorem B1739569 : Blo 1545470 1739569 := bbase (se 2 (by rfl) ⟨652338, by rfl⟩ : syracuseStep 1739569 = 1304677) (by norm_num)
theorem B1764161 : Blo 1545470 1764161 := bbase (se 2 (by rfl) ⟨661560, by rfl⟩ : syracuseStep 1764161 = 1323121) (by norm_num)
theorem B1739605 : Blo 1545470 1739605 := bbase (se 9 (by rfl) ⟨5096, by rfl⟩ : syracuseStep 1739605 = 10193) (by norm_num)
theorem B5221205 : Blo 1545470 5221205 := bbase (se 9 (by rfl) ⟨15296, by rfl⟩ : syracuseStep 5221205 = 30593) (by norm_num)
theorem B5868389 : Blo 1545470 5868389 := bbase (se 4 (by rfl) ⟨550161, by rfl⟩ : syracuseStep 5868389 = 1100323) (by norm_num)
theorem B4402021 : Blo 1545470 4402021 := bbase (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) (by norm_num)
theorem B1739641 : Blo 1545470 1739641 := bbase (se 2 (by rfl) ⟨652365, by rfl⟩ : syracuseStep 1739641 = 1304731) (by norm_num)
theorem B2607997 : Blo 1545470 2607997 := bbase (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) (by norm_num)
theorem B1739677 : Blo 1545470 1739677 := bbase (se 3 (by rfl) ⟨326189, by rfl⟩ : syracuseStep 1739677 = 652379) (by norm_num)
theorem B8809397 : Blo 1545470 8809397 := bbase (se 5 (by rfl) ⟨412940, by rfl⟩ : syracuseStep 8809397 = 825881) (by norm_num)
theorem B1739713 : Blo 1545470 1739713 := bbase (se 2 (by rfl) ⟨652392, by rfl⟩ : syracuseStep 1739713 = 1304785) (by norm_num)
theorem B2608085 : Blo 1545470 2608085 := bbase (se 7 (by rfl) ⟨30563, by rfl⟩ : syracuseStep 2608085 = 61127) (by norm_num)
theorem B3714005 : Blo 1545470 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B14871509 : Blo 1545470 14871509 := bbase (se 7 (by rfl) ⟨174275, by rfl⟩ : syracuseStep 14871509 = 348551) (by norm_num)
theorem B1739749 : Blo 1545470 1739749 := bbase (se 4 (by rfl) ⟨163101, by rfl⟩ : syracuseStep 1739749 = 326203) (by norm_num)
theorem B4402181 : Blo 1545470 4402181 := bbase (se 4 (by rfl) ⟨412704, by rfl⟩ : syracuseStep 4402181 = 825409) (by norm_num)
theorem B1739785 : Blo 1545470 1739785 := bbase (se 2 (by rfl) ⟨652419, by rfl⟩ : syracuseStep 1739785 = 1304839) (by norm_num)
theorem B1764385 : Blo 1545470 1764385 := bbase (se 2 (by rfl) ⟨661644, by rfl⟩ : syracuseStep 1764385 = 1323289) (by norm_num)
theorem B1739821 : Blo 1545470 1739821 := bbase (se 3 (by rfl) ⟨326216, by rfl⟩ : syracuseStep 1739821 = 652433) (by norm_num)
theorem B1739857 : Blo 1545470 1739857 := bbase (se 2 (by rfl) ⟨652446, by rfl⟩ : syracuseStep 1739857 = 1304893) (by norm_num)
theorem B2608213 : Blo 1545470 2608213 := bbase (se 8 (by rfl) ⟨15282, by rfl⟩ : syracuseStep 2608213 = 30565) (by norm_num)
theorem B30125141 : Blo 1545470 30125141 := bbase (se 8 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 30125141 = 353029) (by norm_num)
theorem B1739893 : Blo 1545470 1739893 := bbase (se 5 (by rfl) ⟨81557, by rfl⟩ : syracuseStep 1739893 = 163115) (by norm_num)
theorem B7433333 : Blo 1545470 7433333 := bbase (se 5 (by rfl) ⟨348437, by rfl⟩ : syracuseStep 7433333 = 696875) (by norm_num)
theorem B16723093 : Blo 1545470 16723093 := bbase (se 6 (by rfl) ⟨391947, by rfl⟩ : syracuseStep 16723093 = 783895) (by norm_num)
theorem B1739929 : Blo 1545470 1739929 := bbase (se 2 (by rfl) ⟨652473, by rfl⟩ : syracuseStep 1739929 = 1304947) (by norm_num)
theorem B2608301 : Blo 1545470 2608301 := bbase (se 3 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 2608301 = 978113) (by norm_num)
theorem B1739965 : Blo 1545470 1739965 := bbase (se 3 (by rfl) ⟨326243, by rfl⟩ : syracuseStep 1739965 = 652487) (by norm_num)
theorem B1674437 : Blo 1545470 1674437 := bbase (se 4 (by rfl) ⟨156978, by rfl⟩ : syracuseStep 1674437 = 313957) (by norm_num)
theorem B11144405 : Blo 1545470 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B1740001 : Blo 1545470 1740001 := bbase (se 2 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 1740001 = 1305001) (by norm_num)
theorem B3525869 : Blo 1545470 3525869 := bbase (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) (by norm_num)
theorem B4402421 : Blo 1545470 4402421 := bbase (se 5 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 4402421 = 412727) (by norm_num)
theorem B1740037 : Blo 1545470 1740037 := bbase (se 4 (by rfl) ⟨163128, by rfl⟩ : syracuseStep 1740037 = 326257) (by norm_num)
theorem B5221637 : Blo 1545470 5221637 := bbase (se 4 (by rfl) ⟨489528, by rfl⟩ : syracuseStep 5221637 = 979057) (by norm_num)
theorem B2936101 : Blo 1545470 2936101 := bbase (se 4 (by rfl) ⟨275259, by rfl⟩ : syracuseStep 2936101 = 550519) (by norm_num)
theorem B1740073 : Blo 1545470 1740073 := bbase (se 2 (by rfl) ⟨652527, by rfl⟩ : syracuseStep 1740073 = 1305055) (by norm_num)
theorem B2608429 : Blo 1545470 2608429 := bbase (se 3 (by rfl) ⟨489080, by rfl⟩ : syracuseStep 2608429 = 978161) (by norm_num)
theorem B1740109 : Blo 1545470 1740109 := bbase (se 3 (by rfl) ⟨326270, by rfl⟩ : syracuseStep 1740109 = 652541) (by norm_num)
theorem B1740145 : Blo 1545470 1740145 := bbase (se 2 (by rfl) ⟨652554, by rfl⟩ : syracuseStep 1740145 = 1305109) (by norm_num)
theorem B5287301 : Blo 1545470 5287301 := bbase (se 4 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 5287301 = 991369) (by norm_num)
theorem B2608517 : Blo 1545470 2608517 := bbase (se 4 (by rfl) ⟨244548, by rfl⟩ : syracuseStep 2608517 = 489097) (by norm_num)
theorem B3714437 : Blo 1545470 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B1740181 : Blo 1545470 1740181 := bbase (se 6 (by rfl) ⟨40785, by rfl⟩ : syracuseStep 1740181 = 81571) (by norm_num)
theorem B4402613 : Blo 1545470 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B2936245 : Blo 1545470 2936245 := bbase (se 5 (by rfl) ⟨137636, by rfl⟩ : syracuseStep 2936245 = 275273) (by norm_num)
theorem B1740217 : Blo 1545470 1740217 := bbase (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) (by norm_num)
theorem B1740253 : Blo 1545470 1740253 := bbase (se 3 (by rfl) ⟨326297, by rfl⟩ : syracuseStep 1740253 = 652595) (by norm_num)
theorem B1740289 : Blo 1545470 1740289 := bbase (se 2 (by rfl) ⟨652608, by rfl⟩ : syracuseStep 1740289 = 1305217) (by norm_num)
theorem B2608645 : Blo 1545470 2608645 := bbase (se 4 (by rfl) ⟨244560, by rfl⟩ : syracuseStep 2608645 = 489121) (by norm_num)
theorem B1740325 : Blo 1545470 1740325 := bbase (se 4 (by rfl) ⟨163155, by rfl⟩ : syracuseStep 1740325 = 326311) (by norm_num)
theorem B1674821 : Blo 1545470 1674821 := bbase (se 4 (by rfl) ⟨157014, by rfl⟩ : syracuseStep 1674821 = 314029) (by norm_num)
theorem B1740361 : Blo 1545470 1740361 := bbase (se 2 (by rfl) ⟨652635, by rfl⟩ : syracuseStep 1740361 = 1305271) (by norm_num)
theorem B7827029 : Blo 1545470 7827029 := bbase (se 8 (by rfl) ⟨45861, by rfl⟩ : syracuseStep 7827029 = 91723) (by norm_num)
theorem B2936405 : Blo 1545470 2936405 := bbase (se 8 (by rfl) ⟨17205, by rfl⟩ : syracuseStep 2936405 = 34411) (by norm_num)
theorem B2608733 : Blo 1545470 2608733 := bbase (se 3 (by rfl) ⟨489137, by rfl⟩ : syracuseStep 2608733 = 978275) (by norm_num)
theorem B1740397 : Blo 1545470 1740397 := bbase (se 3 (by rfl) ⟨326324, by rfl⟩ : syracuseStep 1740397 = 652649) (by norm_num)
theorem B9907829 : Blo 1545470 9907829 := bbase (se 5 (by rfl) ⟨464429, by rfl⟩ : syracuseStep 9907829 = 928859) (by norm_num)
theorem B1740433 : Blo 1545470 1740433 := bbase (se 2 (by rfl) ⟨652662, by rfl⟩ : syracuseStep 1740433 = 1305325) (by norm_num)
theorem B6606517 : Blo 1545470 6606517 := bbase (se 5 (by rfl) ⟨309680, by rfl⟩ : syracuseStep 6606517 = 619361) (by norm_num)
theorem B1740469 : Blo 1545470 1740469 := bbase (se 5 (by rfl) ⟨81584, by rfl⟩ : syracuseStep 1740469 = 163169) (by norm_num)
theorem B5222069 : Blo 1545470 5222069 := bbase (se 5 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 5222069 = 489569) (by norm_num)
theorem B2477765 : Blo 1545470 2477765 := bbase (se 4 (by rfl) ⟨232290, by rfl⟩ : syracuseStep 2477765 = 464581) (by norm_num)
theorem B1740505 : Blo 1545470 1740505 := bbase (se 2 (by rfl) ⟨652689, by rfl⟩ : syracuseStep 1740505 = 1305379) (by norm_num)
theorem B2608861 : Blo 1545470 2608861 := bbase (se 3 (by rfl) ⟨489161, by rfl⟩ : syracuseStep 2608861 = 978323) (by norm_num)
theorem B2936549 : Blo 1545470 2936549 := bbase (se 4 (by rfl) ⟨275301, by rfl⟩ : syracuseStep 2936549 = 550603) (by norm_num)
theorem B1740541 : Blo 1545470 1740541 := bbase (se 3 (by rfl) ⟨326351, by rfl⟩ : syracuseStep 1740541 = 652703) (by norm_num)
theorem B4951813 : Blo 1545470 4951813 := bbase (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) (by norm_num)
theorem B1568533 : Blo 1545470 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B1740577 : Blo 1545470 1740577 := bbase (se 2 (by rfl) ⟨652716, by rfl⟩ : syracuseStep 1740577 = 1305433) (by norm_num)
theorem B2608949 : Blo 1545470 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B4181813 : Blo 1545470 4181813 := bbase (se 5 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 4181813 = 392045) (by norm_num)
theorem B1568569 : Blo 1545470 1568569 := bbase (se 2 (by rfl) ⟨588213, by rfl⟩ : syracuseStep 1568569 = 1176427) (by norm_num)
theorem B1740613 : Blo 1545470 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B25431893 : Blo 1545470 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B1740649 : Blo 1545470 1740649 := bbase (se 2 (by rfl) ⟨652743, by rfl⟩ : syracuseStep 1740649 = 1305487) (by norm_num)
theorem B3477365 : Blo 1545470 3477365 := bbase (se 5 (by rfl) ⟨163001, by rfl⟩ : syracuseStep 3477365 = 326003) (by norm_num)
theorem B1740685 : Blo 1545470 1740685 := bbase (se 3 (by rfl) ⟨326378, by rfl⟩ : syracuseStep 1740685 = 652757) (by norm_num)
theorem B1740721 : Blo 1545470 1740721 := bbase (se 2 (by rfl) ⟨652770, by rfl⟩ : syracuseStep 1740721 = 1305541) (by norm_num)
theorem B1650613 : Blo 1545470 1650613 := bbase (se 5 (by rfl) ⟨77372, by rfl⟩ : syracuseStep 1650613 = 154745) (by norm_num)
theorem B2609077 : Blo 1545470 2609077 := bbase (se 5 (by rfl) ⟨122300, by rfl⟩ : syracuseStep 2609077 = 244601) (by norm_num)
theorem B3477437 : Blo 1545470 3477437 := bbase (se 3 (by rfl) ⟨652019, by rfl⟩ : syracuseStep 3477437 = 1304039) (by norm_num)
theorem B3715013 : Blo 1545470 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B1740757 : Blo 1545470 1740757 := bbase (se 7 (by rfl) ⟨20399, by rfl⟩ : syracuseStep 1740757 = 40799) (by norm_num)
theorem B1740793 : Blo 1545470 1740793 := bbase (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) (by norm_num)
theorem B3477509 : Blo 1545470 3477509 := bbase (se 4 (by rfl) ⟨326016, by rfl⟩ : syracuseStep 3477509 = 652033) (by norm_num)
theorem B2936837 : Blo 1545470 2936837 := bbase (se 4 (by rfl) ⟨275328, by rfl⟩ : syracuseStep 2936837 = 550657) (by norm_num)
theorem B2609165 : Blo 1545470 2609165 := bbase (se 3 (by rfl) ⟨489218, by rfl⟩ : syracuseStep 2609165 = 978437) (by norm_num)
theorem B1740829 : Blo 1545470 1740829 := bbase (se 3 (by rfl) ⟨326405, by rfl⟩ : syracuseStep 1740829 = 652811) (by norm_num)
theorem B1650737 : Blo 1545470 1650737 := bbase (se 2 (by rfl) ⟨619026, by rfl⟩ : syracuseStep 1650737 = 1238053) (by norm_num)
theorem B2510909 : Blo 1545470 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B1740865 : Blo 1545470 1740865 := bbase (se 2 (by rfl) ⟨652824, by rfl⟩ : syracuseStep 1740865 = 1305649) (by norm_num)
theorem B3477581 : Blo 1545470 3477581 := bbase (se 3 (by rfl) ⟨652046, by rfl⟩ : syracuseStep 3477581 = 1304093) (by norm_num)
theorem B5222501 : Blo 1545470 5222501 := bbase (se 4 (by rfl) ⟨489609, by rfl⟩ : syracuseStep 5222501 = 979219) (by norm_num)
theorem B1740901 : Blo 1545470 1740901 := bbase (se 4 (by rfl) ⟨163209, by rfl⟩ : syracuseStep 1740901 = 326419) (by norm_num)
theorem B2609293 : Blo 1545470 2609293 := bbase (se 3 (by rfl) ⟨489242, by rfl⟩ : syracuseStep 2609293 = 978485) (by norm_num)
theorem B3477653 : Blo 1545470 3477653 := bbase (se 6 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 3477653 = 163015) (by norm_num)
theorem B2936989 : Blo 1545470 2936989 := bbase (se 3 (by rfl) ⟨550685, by rfl⟩ : syracuseStep 2936989 = 1101371) (by norm_num)
theorem B3477725 : Blo 1545470 3477725 := bbase (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) (by norm_num)
theorem B2609381 : Blo 1545470 2609381 := bbase (se 4 (by rfl) ⟨244629, by rfl⟩ : syracuseStep 2609381 = 489259) (by norm_num)
theorem B3477797 : Blo 1545470 3477797 := bbase (se 4 (by rfl) ⟨326043, by rfl⟩ : syracuseStep 3477797 = 652087) (by norm_num)
theorem B1650989 : Blo 1545470 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B2478413 : Blo 1545470 2478413 := bbase (se 3 (by rfl) ⟨464702, by rfl⟩ : syracuseStep 2478413 = 929405) (by norm_num)
theorem B2609509 : Blo 1545470 2609509 := bbase (se 4 (by rfl) ⟨244641, by rfl⟩ : syracuseStep 2609509 = 489283) (by norm_num)
theorem B3477869 : Blo 1545470 3477869 := bbase (se 3 (by rfl) ⟨652100, by rfl⟩ : syracuseStep 3477869 = 1304201) (by norm_num)
theorem B3912077 : Blo 1545470 3912077 := bbase (se 3 (by rfl) ⟨733514, by rfl⟩ : syracuseStep 3912077 = 1467029) (by norm_num)
theorem B4403605 : Blo 1545470 4403605 := bbase (se 6 (by rfl) ⟨103209, by rfl⟩ : syracuseStep 4403605 = 206419) (by norm_num)
theorem B3477941 : Blo 1545470 3477941 := bbase (se 5 (by rfl) ⟨163028, by rfl⟩ : syracuseStep 3477941 = 326057) (by norm_num)
theorem B2609597 : Blo 1545470 2609597 := bbase (se 3 (by rfl) ⟨489299, by rfl⟩ : syracuseStep 2609597 = 978599) (by norm_num)
theorem B2937293 : Blo 1545470 2937293 := bbase (se 3 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 2937293 = 1101485) (by norm_num)
theorem B3478013 : Blo 1545470 3478013 := bbase (se 3 (by rfl) ⟨652127, by rfl⟩ : syracuseStep 3478013 = 1304255) (by norm_num)
theorem B2609725 : Blo 1545470 2609725 := bbase (se 3 (by rfl) ⟨489323, by rfl⟩ : syracuseStep 2609725 = 978647) (by norm_num)
theorem B3478085 : Blo 1545470 3478085 := bbase (se 4 (by rfl) ⟨326070, by rfl⟩ : syracuseStep 3478085 = 652141) (by norm_num)
theorem B3478157 : Blo 1545470 3478157 := bbase (se 3 (by rfl) ⟨652154, by rfl⟩ : syracuseStep 3478157 = 1304309) (by norm_num)
theorem B2609813 : Blo 1545470 2609813 := bbase (se 6 (by rfl) ⟨61167, by rfl⟩ : syracuseStep 2609813 = 122335) (by norm_num)
theorem B3478229 : Blo 1545470 3478229 := bbase (se 7 (by rfl) ⟨40760, by rfl⟩ : syracuseStep 3478229 = 81521) (by norm_num)
theorem B7533269 : Blo 1545470 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B3912421 : Blo 1545470 3912421 := bbase (se 4 (by rfl) ⟨366789, by rfl⟩ : syracuseStep 3912421 = 733579) (by norm_num)
theorem B1651433 : Blo 1545470 1651433 := bbase (se 2 (by rfl) ⟨619287, by rfl⟩ : syracuseStep 1651433 = 1238575) (by norm_num)
theorem B2609941 : Blo 1545470 2609941 := bbase (se 6 (by rfl) ⟨61170, by rfl⟩ : syracuseStep 2609941 = 122341) (by norm_num)
theorem B3478301 : Blo 1545470 3478301 := bbase (se 3 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 3478301 = 1304363) (by norm_num)
theorem B3912533 : Blo 1545470 3912533 := bbase (se 9 (by rfl) ⟨11462, by rfl⟩ : syracuseStep 3912533 = 22925) (by norm_num)
theorem B3478373 : Blo 1545470 3478373 := bbase (se 4 (by rfl) ⟨326097, by rfl⟩ : syracuseStep 3478373 = 652195) (by norm_num)
theorem B7828325 : Blo 1545470 7828325 := bbase (se 4 (by rfl) ⟨733905, by rfl⟩ : syracuseStep 7828325 = 1467811) (by norm_num)
theorem B2610029 : Blo 1545470 2610029 := bbase (se 3 (by rfl) ⟨489380, by rfl⟩ : syracuseStep 2610029 = 978761) (by norm_num)
theorem B5870501 : Blo 1545470 5870501 := bbase (se 4 (by rfl) ⟨550359, by rfl⟩ : syracuseStep 5870501 = 1100719) (by norm_num)
theorem B3478445 : Blo 1545470 3478445 := bbase (se 3 (by rfl) ⟨652208, by rfl⟩ : syracuseStep 3478445 = 1304417) (by norm_num)
theorem B3134381 : Blo 1545470 3134381 := bbase (se 3 (by rfl) ⟨587696, by rfl⟩ : syracuseStep 3134381 = 1175393) (by norm_num)
theorem B3134413 : Blo 1545470 3134413 := bbase (se 3 (by rfl) ⟨587702, by rfl⟩ : syracuseStep 3134413 = 1175405) (by norm_num)
theorem B1651681 : Blo 1545470 1651681 := bbase (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) (by norm_num)
theorem B2610157 : Blo 1545470 2610157 := bbase (se 3 (by rfl) ⟨489404, by rfl⟩ : syracuseStep 2610157 = 978809) (by norm_num)
theorem B3478517 : Blo 1545470 3478517 := bbase (se 5 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 3478517 = 326111) (by norm_num)
theorem B3912725 : Blo 1545470 3912725 := bbase (se 6 (by rfl) ⟨91704, by rfl⟩ : syracuseStep 3912725 = 183409) (by norm_num)
theorem B3478589 : Blo 1545470 3478589 := bbase (se 3 (by rfl) ⟨652235, by rfl⟩ : syracuseStep 3478589 = 1304471) (by norm_num)
theorem B2610245 : Blo 1545470 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B8811605 : Blo 1545470 8811605 := bbase (se 8 (by rfl) ⟨51630, by rfl⟩ : syracuseStep 8811605 = 103261) (by norm_num)
theorem B91681877 : Blo 1545470 91681877 := bbase (se 8 (by rfl) ⟨537198, by rfl⟩ : syracuseStep 91681877 = 1074397) (by norm_num)
theorem B2200709 : Blo 1545470 2200709 := bbase (se 4 (by rfl) ⟨206316, by rfl⟩ : syracuseStep 2200709 = 412633) (by norm_num)
theorem B3478661 : Blo 1545470 3478661 := bbase (se 4 (by rfl) ⟨326124, by rfl⟩ : syracuseStep 3478661 = 652249) (by norm_num)
theorem B5870789 : Blo 1545470 5870789 := bbase (se 4 (by rfl) ⟨550386, by rfl⟩ : syracuseStep 5870789 = 1100773) (by norm_num)
theorem B2610373 : Blo 1545470 2610373 := bbase (se 4 (by rfl) ⟨244722, by rfl⟩ : syracuseStep 2610373 = 489445) (by norm_num)
theorem B3478733 : Blo 1545470 3478733 := bbase (se 3 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 3478733 = 1304525) (by norm_num)
theorem B3478805 : Blo 1545470 3478805 := bbase (se 6 (by rfl) ⟨81534, by rfl⟩ : syracuseStep 3478805 = 163069) (by norm_num)
theorem B2610461 : Blo 1545470 2610461 := bbase (se 3 (by rfl) ⟨489461, by rfl⟩ : syracuseStep 2610461 = 978923) (by norm_num)
theorem B3478877 : Blo 1545470 3478877 := bbase (se 3 (by rfl) ⟨652289, by rfl⟩ : syracuseStep 3478877 = 1304579) (by norm_num)
theorem B3913069 : Blo 1545470 3913069 := bbase (se 3 (by rfl) ⟨733700, by rfl⟩ : syracuseStep 3913069 = 1467401) (by norm_num)
theorem B2610589 : Blo 1545470 2610589 := bbase (se 3 (by rfl) ⟨489485, by rfl⟩ : syracuseStep 2610589 = 978971) (by norm_num)
theorem B1652125 : Blo 1545470 1652125 := bbase (se 3 (by rfl) ⟨309773, by rfl⟩ : syracuseStep 1652125 = 619547) (by norm_num)
theorem B3478949 : Blo 1545470 3478949 := bbase (se 4 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 3478949 = 652303) (by norm_num)
theorem B1652185 : Blo 1545470 1652185 := bbase (se 2 (by rfl) ⟨619569, by rfl⟩ : syracuseStep 1652185 = 1239139) (by norm_num)
theorem B3913181 : Blo 1545470 3913181 := bbase (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) (by norm_num)
theorem B4404709 : Blo 1545470 4404709 := bbase (se 4 (by rfl) ⟨412941, by rfl⟩ : syracuseStep 4404709 = 825883) (by norm_num)
theorem B3479021 : Blo 1545470 3479021 := bbase (se 3 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 3479021 = 1304633) (by norm_num)
theorem B2610677 : Blo 1545470 2610677 := bbase (se 5 (by rfl) ⟨122375, by rfl⟩ : syracuseStep 2610677 = 244751) (by norm_num)
theorem B3479093 : Blo 1545470 3479093 := bbase (se 5 (by rfl) ⟨163082, by rfl⟩ : syracuseStep 3479093 = 326165) (by norm_num)
theorem B2610805 : Blo 1545470 2610805 := bbase (se 5 (by rfl) ⟨122381, by rfl⟩ : syracuseStep 2610805 = 244763) (by norm_num)
theorem B3479165 : Blo 1545470 3479165 := bbase (se 3 (by rfl) ⟨652343, by rfl⟩ : syracuseStep 3479165 = 1304687) (by norm_num)
theorem B3176077 : Blo 1545470 3176077 := bbase (se 3 (by rfl) ⟨595514, by rfl⟩ : syracuseStep 3176077 = 1191029) (by norm_num)
theorem B3913373 : Blo 1545470 3913373 := bbase (se 3 (by rfl) ⟨733757, by rfl⟩ : syracuseStep 3913373 = 1467515) (by norm_num)
theorem B2201261 : Blo 1545470 2201261 := bbase (se 3 (by rfl) ⟨412736, by rfl⟩ : syracuseStep 2201261 = 825473) (by norm_num)
theorem B3479237 : Blo 1545470 3479237 := bbase (se 4 (by rfl) ⟨326178, by rfl⟩ : syracuseStep 3479237 = 652357) (by norm_num)
theorem B2610893 : Blo 1545470 2610893 := bbase (se 3 (by rfl) ⟨489542, by rfl⟩ : syracuseStep 2610893 = 979085) (by norm_num)
theorem B3479309 : Blo 1545470 3479309 := bbase (se 3 (by rfl) ⟨652370, by rfl⟩ : syracuseStep 3479309 = 1304741) (by norm_num)
theorem B5216021 : Blo 1545470 5216021 := bbase (se 6 (by rfl) ⟨122250, by rfl⟩ : syracuseStep 5216021 = 244501) (by norm_num)
theorem B2611021 : Blo 1545470 2611021 := bbase (se 3 (by rfl) ⟨489566, by rfl⟩ : syracuseStep 2611021 = 979133) (by norm_num)
theorem B3479381 : Blo 1545470 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B19822421 : Blo 1545470 19822421 := bbase (se 9 (by rfl) ⟨58073, by rfl⟩ : syracuseStep 19822421 = 116147) (by norm_num)
theorem B3479453 : Blo 1545470 3479453 := bbase (se 3 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 3479453 = 1304795) (by norm_num)
theorem B2611109 : Blo 1545470 2611109 := bbase (se 4 (by rfl) ⟨244791, by rfl⟩ : syracuseStep 2611109 = 489583) (by norm_num)
theorem B3479525 : Blo 1545470 3479525 := bbase (se 4 (by rfl) ⟨326205, by rfl⟩ : syracuseStep 3479525 = 652411) (by norm_num)
theorem B3913717 : Blo 1545470 3913717 := bbase (se 5 (by rfl) ⟨183455, by rfl⟩ : syracuseStep 3913717 = 366911) (by norm_num)
theorem B2611237 : Blo 1545470 2611237 := bbase (se 4 (by rfl) ⟨244803, by rfl⟩ : syracuseStep 2611237 = 489607) (by norm_num)
theorem B3479597 : Blo 1545470 3479597 := bbase (se 3 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 3479597 = 1304849) (by norm_num)
theorem B12064853 : Blo 1545470 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B3913829 : Blo 1545470 3913829 := bbase (se 4 (by rfl) ⟨366921, by rfl⟩ : syracuseStep 3913829 = 733843) (by norm_num)
theorem B3479669 : Blo 1545470 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B7829621 : Blo 1545470 7829621 := bbase (se 5 (by rfl) ⟨367013, by rfl⟩ : syracuseStep 7829621 = 734027) (by norm_num)
theorem B2611325 : Blo 1545470 2611325 := bbase (se 3 (by rfl) ⟨489623, by rfl⟩ : syracuseStep 2611325 = 979247) (by norm_num)
theorem B3479741 : Blo 1545470 3479741 := bbase (se 3 (by rfl) ⟨652451, by rfl⟩ : syracuseStep 3479741 = 1304903) (by norm_num)
theorem B5216453 : Blo 1545470 5216453 := bbase (se 4 (by rfl) ⟨489042, by rfl⟩ : syracuseStep 5216453 = 978085) (by norm_num)
theorem B1857737 : Blo 1545470 1857737 := bbase (se 2 (by rfl) ⟨696651, by rfl⟩ : syracuseStep 1857737 = 1393303) (by norm_num)
theorem B1956089 : Blo 1545470 1956089 := bbase (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) (by norm_num)
theorem B3479813 : Blo 1545470 3479813 := bbase (se 4 (by rfl) ⟨326232, by rfl⟩ : syracuseStep 3479813 = 652465) (by norm_num)
theorem B2717965 : Blo 1545470 2717965 := bbase (se 3 (by rfl) ⟨509618, by rfl⟩ : syracuseStep 2717965 = 1019237) (by norm_num)
theorem B3914021 : Blo 1545470 3914021 := bbase (se 4 (by rfl) ⟨366939, by rfl⟩ : syracuseStep 3914021 = 733879) (by norm_num)
theorem B1956145 : Blo 1545470 1956145 := bbase (se 2 (by rfl) ⟨733554, by rfl⟩ : syracuseStep 1956145 = 1467109) (by norm_num)
theorem B1857853 : Blo 1545470 1857853 := bbase (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) (by norm_num)
theorem B3479885 : Blo 1545470 3479885 := bbase (se 3 (by rfl) ⟨652478, by rfl⟩ : syracuseStep 3479885 = 1304957) (by norm_num)
theorem B5871973 : Blo 1545470 5871973 := bbase (se 4 (by rfl) ⟨550497, by rfl⟩ : syracuseStep 5871973 = 1100995) (by norm_num)
theorem B1857925 : Blo 1545470 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B1956241 : Blo 1545470 1956241 := bbase (se 2 (by rfl) ⟨733590, by rfl⟩ : syracuseStep 1956241 = 1467181) (by norm_num)
theorem B3479957 : Blo 1545470 3479957 := bbase (se 6 (by rfl) ⟨81561, by rfl⟩ : syracuseStep 3479957 = 163123) (by norm_num)
theorem B2202013 : Blo 1545470 2202013 := bbase (se 3 (by rfl) ⟨412877, by rfl⟩ : syracuseStep 2202013 = 825755) (by norm_num)
theorem B3717589 : Blo 1545470 3717589 := bbase (se 7 (by rfl) ⟨43565, by rfl⟩ : syracuseStep 3717589 = 87131) (by norm_num)
theorem B3480029 : Blo 1545470 3480029 := bbase (se 3 (by rfl) ⟨652505, by rfl⟩ : syracuseStep 3480029 = 1305011) (by norm_num)
theorem B1858045 : Blo 1545470 1858045 := bbase (se 3 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 1858045 = 696767) (by norm_num)
theorem B3480101 : Blo 1545470 3480101 := bbase (se 4 (by rfl) ⟨326259, by rfl⟩ : syracuseStep 3480101 = 652519) (by norm_num)
theorem B1956413 : Blo 1545470 1956413 := bbase (se 3 (by rfl) ⟨366827, by rfl⟩ : syracuseStep 1956413 = 733655) (by norm_num)
theorem B4954709 : Blo 1545470 4954709 := bbase (se 8 (by rfl) ⟨29031, by rfl⟩ : syracuseStep 4954709 = 58063) (by norm_num)
theorem B6609509 : Blo 1545470 6609509 := bbase (se 4 (by rfl) ⟨619641, by rfl⟩ : syracuseStep 6609509 = 1239283) (by norm_num)
theorem B3480173 : Blo 1545470 3480173 := bbase (se 3 (by rfl) ⟨652532, by rfl⟩ : syracuseStep 3480173 = 1305065) (by norm_num)
theorem B5216885 : Blo 1545470 5216885 := bbase (se 5 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 5216885 = 489083) (by norm_num)
theorem B1956469 : Blo 1545470 1956469 := bbase (se 5 (by rfl) ⟨91709, by rfl⟩ : syracuseStep 1956469 = 183419) (by norm_num)
theorem B3914365 : Blo 1545470 3914365 := bbase (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) (by norm_num)
theorem B3136133 : Blo 1545470 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B5872277 : Blo 1545470 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B3480245 : Blo 1545470 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B7051973 : Blo 1545470 7051973 := bbase (se 4 (by rfl) ⟨661122, by rfl⟩ : syracuseStep 7051973 = 1322245) (by norm_num)
theorem B5159621 : Blo 1545470 5159621 := bbase (se 4 (by rfl) ⟨483714, by rfl⟩ : syracuseStep 5159621 = 967429) (by norm_num)
theorem B1956565 : Blo 1545470 1956565 := bbase (se 7 (by rfl) ⟨22928, by rfl⟩ : syracuseStep 1956565 = 45857) (by norm_num)
theorem B3914477 : Blo 1545470 3914477 := bbase (se 3 (by rfl) ⟨733964, by rfl⟩ : syracuseStep 3914477 = 1467929) (by norm_num)
theorem B2318333 : Blo 1545470 2318333 := bbase (se 3 (by rfl) ⟨434687, by rfl⟩ : syracuseStep 2318333 = 869375) (by norm_num)
theorem B3480317 : Blo 1545470 3480317 := bbase (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) (by norm_num)
theorem B10582805 : Blo 1545470 10582805 := bbase (se 6 (by rfl) ⟨248034, by rfl⟩ : syracuseStep 10582805 = 496069) (by norm_num)
theorem B15276853 : Blo 1545470 15276853 := bbase (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) (by norm_num)
theorem B3480389 : Blo 1545470 3480389 := bbase (se 4 (by rfl) ⟨326286, by rfl⟩ : syracuseStep 3480389 = 652573) (by norm_num)
theorem B39615317 : Blo 1545470 39615317 := bbase (se 9 (by rfl) ⟨116060, by rfl⟩ : syracuseStep 39615317 = 232121) (by norm_num)
theorem B11746133 : Blo 1545470 11746133 := bbase (se 9 (by rfl) ⟨34412, by rfl⟩ : syracuseStep 11746133 = 68825) (by norm_num)
theorem B1858429 : Blo 1545470 1858429 := bbase (se 3 (by rfl) ⟨348455, by rfl⟩ : syracuseStep 1858429 = 696911) (by norm_num)
theorem B1956737 : Blo 1545470 1956737 := bbase (se 2 (by rfl) ⟨733776, by rfl⟩ : syracuseStep 1956737 = 1467553) (by norm_num)
theorem B3480461 : Blo 1545470 3480461 := bbase (se 3 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 3480461 = 1305173) (by norm_num)
theorem B3914669 : Blo 1545470 3914669 := bbase (se 3 (by rfl) ⟨734000, by rfl⟩ : syracuseStep 3914669 = 1468001) (by norm_num)
theorem B1956793 : Blo 1545470 1956793 := bbase (se 2 (by rfl) ⟨733797, by rfl⟩ : syracuseStep 1956793 = 1467595) (by norm_num)
theorem B4406213 : Blo 1545470 4406213 := bbase (se 4 (by rfl) ⟨413082, by rfl⟩ : syracuseStep 4406213 = 826165) (by norm_num)
theorem B18799573 : Blo 1545470 18799573 := bbase (se 7 (by rfl) ⟨220307, by rfl⟩ : syracuseStep 18799573 = 440615) (by norm_num)
theorem B3480533 : Blo 1545470 3480533 := bbase (se 7 (by rfl) ⟨40787, by rfl⟩ : syracuseStep 3480533 = 81575) (by norm_num)
theorem B6601733 : Blo 1545470 6601733 := bbase (se 4 (by rfl) ⟨618912, by rfl⟩ : syracuseStep 6601733 = 1237825) (by norm_num)
theorem B1956889 : Blo 1545470 1956889 := bbase (se 2 (by rfl) ⟨733833, by rfl⟩ : syracuseStep 1956889 = 1467667) (by norm_num)
theorem B3480605 : Blo 1545470 3480605 := bbase (se 3 (by rfl) ⟨652613, by rfl⟩ : syracuseStep 3480605 = 1305227) (by norm_num)
theorem B5217317 : Blo 1545470 5217317 := bbase (se 4 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 5217317 = 978247) (by norm_num)
theorem B3480677 : Blo 1545470 3480677 := bbase (se 4 (by rfl) ⟨326313, by rfl⟩ : syracuseStep 3480677 = 652627) (by norm_num)
theorem B5291173 : Blo 1545470 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B3480749 : Blo 1545470 3480749 := bbase (se 3 (by rfl) ⟨652640, by rfl⟩ : syracuseStep 3480749 = 1305281) (by norm_num)
theorem B2202805 : Blo 1545470 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1957061 : Blo 1545470 1957061 := bbase (se 4 (by rfl) ⟨183474, by rfl⟩ : syracuseStep 1957061 = 366949) (by norm_num)
theorem B11738357 : Blo 1545470 11738357 := bbase (se 5 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 11738357 = 1100471) (by norm_num)
theorem B3480821 : Blo 1545470 3480821 := bbase (se 5 (by rfl) ⟨163163, by rfl⟩ : syracuseStep 3480821 = 326327) (by norm_num)
theorem B1957117 : Blo 1545470 1957117 := bbase (se 3 (by rfl) ⟨366959, by rfl⟩ : syracuseStep 1957117 = 733919) (by norm_num)
theorem B3915013 : Blo 1545470 3915013 := bbase (se 4 (by rfl) ⟨367032, by rfl⟩ : syracuseStep 3915013 = 734065) (by norm_num)
theorem B3480893 : Blo 1545470 3480893 := bbase (se 3 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 3480893 = 1305335) (by norm_num)
theorem B1957213 : Blo 1545470 1957213 := bbase (se 3 (by rfl) ⟨366977, by rfl⟩ : syracuseStep 1957213 = 733955) (by norm_num)
theorem B3915125 : Blo 1545470 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B2350469 : Blo 1545470 2350469 := bbase (se 4 (by rfl) ⟨220356, by rfl⟩ : syracuseStep 2350469 = 440713) (by norm_num)
theorem B7830917 : Blo 1545470 7830917 := bbase (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) (by norm_num)
theorem B3480965 : Blo 1545470 3480965 := bbase (se 4 (by rfl) ⟨326340, by rfl⟩ : syracuseStep 3480965 = 652681) (by norm_num)
theorem B3481037 : Blo 1545470 3481037 := bbase (se 3 (by rfl) ⟨652694, by rfl⟩ : syracuseStep 3481037 = 1305389) (by norm_num)
theorem B5217749 : Blo 1545470 5217749 := bbase (se 7 (by rfl) ⟨61145, by rfl⟩ : syracuseStep 5217749 = 122291) (by norm_num)
theorem B3915773 : Blo 1545470 3915773 := bbase (se 3 (by rfl) ⟨734207, by rfl⟩ : syracuseStep 3915773 = 1468415) (by norm_num)
theorem B2203141 : Blo 1545470 2203141 := bbase (se 4 (by rfl) ⟨206544, by rfl⟩ : syracuseStep 2203141 = 413089) (by norm_num)
theorem B1957385 : Blo 1545470 1957385 := bbase (se 2 (by rfl) ⟨734019, by rfl⟩ : syracuseStep 1957385 = 1468039) (by norm_num)
theorem B3481109 : Blo 1545470 3481109 := bbase (se 6 (by rfl) ⟨81588, by rfl⟩ : syracuseStep 3481109 = 163177) (by norm_num)
theorem B3915317 : Blo 1545470 3915317 := bbase (se 5 (by rfl) ⟨183530, by rfl⟩ : syracuseStep 3915317 = 367061) (by norm_num)
theorem B1957441 : Blo 1545470 1957441 := bbase (se 2 (by rfl) ⟨734040, by rfl⟩ : syracuseStep 1957441 = 1468081) (by norm_num)
theorem B3481181 : Blo 1545470 3481181 := bbase (se 3 (by rfl) ⟨652721, by rfl⟩ : syracuseStep 3481181 = 1305443) (by norm_num)
theorem B1957537 : Blo 1545470 1957537 := bbase (se 2 (by rfl) ⟨734076, by rfl⟩ : syracuseStep 1957537 = 1468153) (by norm_num)
theorem B3481253 : Blo 1545470 3481253 := bbase (se 4 (by rfl) ⟨326367, by rfl⟩ : syracuseStep 3481253 = 652735) (by norm_num)
theorem B3481325 : Blo 1545470 3481325 := bbase (se 3 (by rfl) ⟨652748, by rfl⟩ : syracuseStep 3481325 = 1305497) (by norm_num)
theorem B6602485 : Blo 1545470 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B3481397 : Blo 1545470 3481397 := bbase (se 5 (by rfl) ⟨163190, by rfl⟩ : syracuseStep 3481397 = 326381) (by norm_num)
theorem B1957709 : Blo 1545470 1957709 := bbase (se 3 (by rfl) ⟨367070, by rfl⟩ : syracuseStep 1957709 = 734141) (by norm_num)
theorem B8806229 : Blo 1545470 8806229 := bbase (se 9 (by rfl) ⟨25799, by rfl⟩ : syracuseStep 8806229 = 51599) (by norm_num)
theorem B4956005 : Blo 1545470 4956005 := bbase (se 4 (by rfl) ⟨464625, by rfl⟩ : syracuseStep 4956005 = 929251) (by norm_num)
theorem B2350957 : Blo 1545470 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B3481469 : Blo 1545470 3481469 := bbase (se 3 (by rfl) ⟨652775, by rfl⟩ : syracuseStep 3481469 = 1305551) (by norm_num)
theorem B2318213 : Blo 1545470 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B5218181 : Blo 1545470 5218181 := bbase (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) (by norm_num)
theorem B1957765 : Blo 1545470 1957765 := bbase (se 4 (by rfl) ⟨183540, by rfl⟩ : syracuseStep 1957765 = 367081) (by norm_num)
theorem B3915661 : Blo 1545470 3915661 := bbase (se 3 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 3915661 = 1468373) (by norm_num)
theorem B2318237 : Blo 1545470 2318237 := bbase (se 3 (by rfl) ⟨434669, by rfl⟩ : syracuseStep 2318237 = 869339) (by norm_num)
theorem B2318261 : Blo 1545470 2318261 := bbase (se 5 (by rfl) ⟨108668, by rfl⟩ : syracuseStep 2318261 = 217337) (by norm_num)
theorem B3481541 : Blo 1545470 3481541 := bbase (se 4 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 3481541 = 652789) (by norm_num)
theorem B2318285 : Blo 1545470 2318285 := bbase (se 3 (by rfl) ⟨434678, by rfl⟩ : syracuseStep 2318285 = 869357) (by norm_num)
theorem B2318309 : Blo 1545470 2318309 := bbase (se 4 (by rfl) ⟨217341, by rfl⟩ : syracuseStep 2318309 = 434683) (by norm_num)
theorem B1957861 : Blo 1545470 1957861 := bbase (se 4 (by rfl) ⟨183549, by rfl⟩ : syracuseStep 1957861 = 367099) (by norm_num)
theorem B2318339 : Blo 1545470 2318339 := bstep (se 1 (by rfl) ⟨1738754, by rfl⟩ : syracuseStep 2318339 = 3477509) B3477509
theorem B7831565 : Blo 1545470 7831565 := bstep (se 3 (by rfl) ⟨1468418, by rfl⟩ : syracuseStep 7831565 = 2936837) B2936837
theorem B2318369 : Blo 1545470 2318369 := bstep (se 2 (by rfl) ⟨869388, by rfl⟩ : syracuseStep 2318369 = 1738777) B1738777
theorem B3481649 : Blo 1545470 3481649 := bstep (se 2 (by rfl) ⟨1305618, by rfl⟩ : syracuseStep 3481649 = 2611237) B2611237
theorem B2318387 : Blo 1545470 2318387 := bstep (se 1 (by rfl) ⟨1738790, by rfl⟩ : syracuseStep 2318387 = 3477581) B3477581
theorem B3481667 : Blo 1545470 3481667 := bstep (se 1 (by rfl) ⟨2611250, by rfl⟩ : syracuseStep 3481667 = 5222501) B5222501
theorem B2318417 : Blo 1545470 2318417 := bstep (se 2 (by rfl) ⟨869406, by rfl⟩ : syracuseStep 2318417 = 1738813) B1738813
theorem B2318435 : Blo 1545470 2318435 := bstep (se 1 (by rfl) ⟨1738826, by rfl⟩ : syracuseStep 2318435 = 3477653) B3477653
theorem B2318465 : Blo 1545470 2318465 := bstep (se 2 (by rfl) ⟨869424, by rfl⟩ : syracuseStep 2318465 = 1738849) B1738849
theorem B4178051 : Blo 1545470 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B2318483 : Blo 1545470 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B9404579 : Blo 1545470 9404579 := bstep (se 1 (by rfl) ⟨7053434, by rfl⟩ : syracuseStep 9404579 = 14106869) B14106869
theorem B2318513 : Blo 1545470 2318513 := bstep (se 2 (by rfl) ⟨869442, by rfl⟩ : syracuseStep 2318513 = 1738885) B1738885
theorem B2318531 : Blo 1545470 2318531 := bstep (se 1 (by rfl) ⟨1738898, by rfl⟩ : syracuseStep 2318531 = 3477797) B3477797
theorem B3915985 : Blo 1545470 3915985 := bstep (se 2 (by rfl) ⟨1468494, by rfl⟩ : syracuseStep 3915985 = 2936989) B2936989
theorem B1982675 : Blo 1545470 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B71459029 : Blo 1545470 71459029 := bstep (se 7 (by rfl) ⟨837410, by rfl⟩ : syracuseStep 71459029 = 1674821) B1674821
theorem B2318561 : Blo 1545470 2318561 := bstep (se 2 (by rfl) ⟨869460, by rfl⟩ : syracuseStep 2318561 = 1738921) B1738921
theorem B2318579 : Blo 1545470 2318579 := bstep (se 1 (by rfl) ⟨1738934, by rfl⟩ : syracuseStep 2318579 = 3477869) B3477869
theorem B2318609 : Blo 1545470 2318609 := bstep (se 2 (by rfl) ⟨869478, by rfl⟩ : syracuseStep 2318609 = 1738957) B1738957
theorem B2318627 : Blo 1545470 2318627 := bstep (se 1 (by rfl) ⟨1738970, by rfl⟩ : syracuseStep 2318627 = 3477941) B3477941
theorem B1958195 : Blo 1545470 1958195 := bstep (se 1 (by rfl) ⟨1468646, by rfl⟩ : syracuseStep 1958195 = 2937293) B2937293
theorem B2318657 : Blo 1545470 2318657 := bstep (se 2 (by rfl) ⟨869496, by rfl⟩ : syracuseStep 2318657 = 1738993) B1738993
theorem B2318675 : Blo 1545470 2318675 := bstep (se 1 (by rfl) ⟨1739006, by rfl⟩ : syracuseStep 2318675 = 3478013) B3478013
theorem B10576241 : Blo 1545470 10576241 := bstep (se 2 (by rfl) ⟨3966090, by rfl⟩ : syracuseStep 10576241 = 7932181) B7932181
theorem B2318705 : Blo 1545470 2318705 := bstep (se 2 (by rfl) ⟨869514, by rfl⟩ : syracuseStep 2318705 = 1739029) B1739029
theorem B2318723 : Blo 1545470 2318723 := bstep (se 1 (by rfl) ⟨1739042, by rfl⟩ : syracuseStep 2318723 = 3478085) B3478085
theorem B2318753 : Blo 1545470 2318753 := bstep (se 2 (by rfl) ⟨869532, by rfl⟩ : syracuseStep 2318753 = 1739065) B1739065
theorem B2318771 : Blo 1545470 2318771 := bstep (se 1 (by rfl) ⟨1739078, by rfl⟩ : syracuseStep 2318771 = 3478157) B3478157
theorem B2318801 : Blo 1545470 2318801 := bstep (se 2 (by rfl) ⟨869550, by rfl⟩ : syracuseStep 2318801 = 1739101) B1739101
theorem B2318819 : Blo 1545470 2318819 := bstep (se 1 (by rfl) ⟨1739114, by rfl⟩ : syracuseStep 2318819 = 3478229) B3478229
theorem B5022179 : Blo 1545470 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3916259 : Blo 1545470 3916259 := bstep (se 1 (by rfl) ⟨2937194, by rfl⟩ : syracuseStep 3916259 = 5874389) B5874389
theorem B2318849 : Blo 1545470 2318849 := bstep (se 2 (by rfl) ⟨869568, by rfl⟩ : syracuseStep 2318849 = 1739137) B1739137
theorem B5218829 : Blo 1545470 5218829 := bstep (se 3 (by rfl) ⟨978530, by rfl⟩ : syracuseStep 5218829 = 1957061) B1957061
theorem B2318867 : Blo 1545470 2318867 := bstep (se 1 (by rfl) ⟨1739150, by rfl⟩ : syracuseStep 2318867 = 3478301) B3478301
theorem B10584611 : Blo 1545470 10584611 := bstep (se 1 (by rfl) ⟨7938458, by rfl⟩ : syracuseStep 10584611 = 15876917) B15876917
theorem B2318897 : Blo 1545470 2318897 := bstep (se 2 (by rfl) ⟨869586, by rfl⟩ : syracuseStep 2318897 = 1739173) B1739173
theorem B2318915 : Blo 1545470 2318915 := bstep (se 1 (by rfl) ⟨1739186, by rfl⟩ : syracuseStep 2318915 = 3478373) B3478373
theorem B5218883 : Blo 1545470 5218883 := bstep (se 1 (by rfl) ⟨3914162, by rfl⟩ : syracuseStep 5218883 = 7828325) B7828325
theorem B4702787 : Blo 1545470 4702787 := bstep (se 1 (by rfl) ⟨3527090, by rfl⟩ : syracuseStep 4702787 = 7054181) B7054181
theorem B2318945 : Blo 1545470 2318945 := bstep (se 2 (by rfl) ⟨869604, by rfl⟩ : syracuseStep 2318945 = 1739209) B1739209
theorem B4956785 : Blo 1545470 4956785 := bstep (se 2 (by rfl) ⟨1858794, by rfl⟩ : syracuseStep 4956785 = 3717589) B3717589
theorem B2318963 : Blo 1545470 2318963 := bstep (se 1 (by rfl) ⟨1739222, by rfl⟩ : syracuseStep 2318963 = 3478445) B3478445
theorem B2318993 : Blo 1545470 2318993 := bstep (se 2 (by rfl) ⟨869622, by rfl⟩ : syracuseStep 2318993 = 1739245) B1739245
theorem B2319011 : Blo 1545470 2319011 := bstep (se 1 (by rfl) ⟨1739258, by rfl⟩ : syracuseStep 2319011 = 3478517) B3478517
theorem B3916451 : Blo 1545470 3916451 := bstep (se 1 (by rfl) ⟨2937338, by rfl⟩ : syracuseStep 3916451 = 5874677) B5874677
theorem B2319041 : Blo 1545470 2319041 := bstep (se 2 (by rfl) ⟨869640, by rfl⟩ : syracuseStep 2319041 = 1739281) B1739281
theorem B10584773 : Blo 1545470 10584773 := bstep (se 4 (by rfl) ⟨992322, by rfl⟩ : syracuseStep 10584773 = 1984645) B1984645
theorem B2319059 : Blo 1545470 2319059 := bstep (se 1 (by rfl) ⟨1739294, by rfl⟩ : syracuseStep 2319059 = 3478589) B3478589
theorem B5874403 : Blo 1545470 5874403 := bstep (se 1 (by rfl) ⟨4405802, by rfl⟩ : syracuseStep 5874403 = 8811605) B8811605
theorem B61121251 : Blo 1545470 61121251 := bstep (se 1 (by rfl) ⟨45840938, by rfl⟩ : syracuseStep 61121251 = 91681877) B91681877
theorem B7824113 : Blo 1545470 7824113 := bstep (se 2 (by rfl) ⟨2934042, by rfl⟩ : syracuseStep 7824113 = 5868085) B5868085
theorem B2319089 : Blo 1545470 2319089 := bstep (se 2 (by rfl) ⟨869658, by rfl⟩ : syracuseStep 2319089 = 1739317) B1739317
theorem B2351857 : Blo 1545470 2351857 := bstep (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) B1763893
theorem B2319107 : Blo 1545470 2319107 := bstep (se 1 (by rfl) ⟨1739330, by rfl⟩ : syracuseStep 2319107 = 3478661) B3478661
theorem B2319137 : Blo 1545470 2319137 := bstep (se 2 (by rfl) ⟨869676, by rfl⟩ : syracuseStep 2319137 = 1739353) B1739353
theorem B2319155 : Blo 1545470 2319155 := bstep (se 1 (by rfl) ⟨1739366, by rfl⟩ : syracuseStep 2319155 = 3478733) B3478733
theorem B2319185 : Blo 1545470 2319185 := bstep (se 2 (by rfl) ⟨869694, by rfl⟩ : syracuseStep 2319185 = 1739389) B1739389
theorem B5219153 : Blo 1545470 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B2319203 : Blo 1545470 2319203 := bstep (se 1 (by rfl) ⟨1739402, by rfl⟩ : syracuseStep 2319203 = 3478805) B3478805
theorem B2319233 : Blo 1545470 2319233 := bstep (se 2 (by rfl) ⟨869712, by rfl⟩ : syracuseStep 2319233 = 1739425) B1739425
theorem B44565389 : Blo 1545470 44565389 := bstep (se 3 (by rfl) ⟨8356010, by rfl⟩ : syracuseStep 44565389 = 16712021) B16712021
theorem B2319251 : Blo 1545470 2319251 := bstep (se 1 (by rfl) ⟨1739438, by rfl⟩ : syracuseStep 2319251 = 3478877) B3478877
theorem B2319281 : Blo 1545470 2319281 := bstep (se 2 (by rfl) ⟨869730, by rfl⟩ : syracuseStep 2319281 = 1739461) B1739461
theorem B2319299 : Blo 1545470 2319299 := bstep (se 1 (by rfl) ⟨1739474, by rfl⟩ : syracuseStep 2319299 = 3478949) B3478949
theorem B2319329 : Blo 1545470 2319329 := bstep (se 2 (by rfl) ⟨869748, by rfl⟩ : syracuseStep 2319329 = 1739497) B1739497
theorem B2319347 : Blo 1545470 2319347 := bstep (se 1 (by rfl) ⟨1739510, by rfl⟩ : syracuseStep 2319347 = 3479021) B3479021
theorem B11142157 : Blo 1545470 11142157 := bstep (se 3 (by rfl) ⟨2089154, by rfl⟩ : syracuseStep 11142157 = 4178309) B4178309
theorem B6267917 : Blo 1545470 6267917 := bstep (se 3 (by rfl) ⟨1175234, by rfl⟩ : syracuseStep 6267917 = 2350469) B2350469
theorem B9905165 : Blo 1545470 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B2319377 : Blo 1545470 2319377 := bstep (se 2 (by rfl) ⟨869766, by rfl⟩ : syracuseStep 2319377 = 1739533) B1739533
theorem B2319395 : Blo 1545470 2319395 := bstep (se 1 (by rfl) ⟨1739546, by rfl⟩ : syracuseStep 2319395 = 3479093) B3479093
theorem B2319425 : Blo 1545470 2319425 := bstep (se 2 (by rfl) ⟨869784, by rfl⟩ : syracuseStep 2319425 = 1739569) B1739569
theorem B11150405 : Blo 1545470 11150405 := bstep (se 4 (by rfl) ⟨1045350, by rfl⟩ : syracuseStep 11150405 = 2090701) B2090701
theorem B2319443 : Blo 1545470 2319443 := bstep (se 1 (by rfl) ⟨1739582, by rfl⟩ : syracuseStep 2319443 = 3479165) B3479165
theorem B2319473 : Blo 1545470 2319473 := bstep (se 2 (by rfl) ⟨869802, by rfl⟩ : syracuseStep 2319473 = 1739605) B1739605
theorem B9405553 : Blo 1545470 9405553 := bstep (se 2 (by rfl) ⟨3527082, by rfl⟩ : syracuseStep 9405553 = 7054165) B7054165
theorem B2319491 : Blo 1545470 2319491 := bstep (se 1 (by rfl) ⟨1739618, by rfl⟩ : syracuseStep 2319491 = 3479237) B3479237
theorem B11740301 : Blo 1545470 11740301 := bstep (se 3 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 11740301 = 4402613) B4402613
theorem B2319521 : Blo 1545470 2319521 := bstep (se 2 (by rfl) ⟨869820, by rfl⟩ : syracuseStep 2319521 = 1739641) B1739641
theorem B2319539 : Blo 1545470 2319539 := bstep (se 1 (by rfl) ⟨1739654, by rfl⟩ : syracuseStep 2319539 = 3479309) B3479309
theorem B2319569 : Blo 1545470 2319569 := bstep (se 2 (by rfl) ⟨869838, by rfl⟩ : syracuseStep 2319569 = 1739677) B1739677
theorem B2319587 : Blo 1545470 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B13214947 : Blo 1545470 13214947 := bstep (se 1 (by rfl) ⟨9911210, by rfl⟩ : syracuseStep 13214947 = 19822421) B19822421
theorem B2319617 : Blo 1545470 2319617 := bstep (se 2 (by rfl) ⟨869856, by rfl⟩ : syracuseStep 2319617 = 1739713) B1739713
theorem B2786563 : Blo 1545470 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B4179217 : Blo 1545470 4179217 := bstep (se 2 (by rfl) ⟨1567206, by rfl⟩ : syracuseStep 4179217 = 3134413) B3134413
theorem B2319635 : Blo 1545470 2319635 := bstep (se 1 (by rfl) ⟨1739726, by rfl⟩ : syracuseStep 2319635 = 3479453) B3479453
theorem B2319665 : Blo 1545470 2319665 := bstep (se 2 (by rfl) ⟨869874, by rfl⟩ : syracuseStep 2319665 = 1739749) B1739749
theorem B2319683 : Blo 1545470 2319683 := bstep (se 1 (by rfl) ⟨1739762, by rfl⟩ : syracuseStep 2319683 = 3479525) B3479525
theorem B2319713 : Blo 1545470 2319713 := bstep (se 2 (by rfl) ⟨869892, by rfl⟩ : syracuseStep 2319713 = 1739785) B1739785
theorem B5219693 : Blo 1545470 5219693 := bstep (se 3 (by rfl) ⟨978692, by rfl⟩ : syracuseStep 5219693 = 1957385) B1957385
theorem B2319731 : Blo 1545470 2319731 := bstep (se 1 (by rfl) ⟨1739798, by rfl⟩ : syracuseStep 2319731 = 3479597) B3479597
theorem B2319761 : Blo 1545470 2319761 := bstep (se 2 (by rfl) ⟨869910, by rfl⟩ : syracuseStep 2319761 = 1739821) B1739821
theorem B2319779 : Blo 1545470 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B5219747 : Blo 1545470 5219747 := bstep (se 1 (by rfl) ⟨3914810, by rfl⟩ : syracuseStep 5219747 = 7829621) B7829621
theorem B2319809 : Blo 1545470 2319809 := bstep (se 2 (by rfl) ⟨869928, by rfl⟩ : syracuseStep 2319809 = 1739857) B1739857
theorem B2319827 : Blo 1545470 2319827 := bstep (se 1 (by rfl) ⟨1739870, by rfl⟩ : syracuseStep 2319827 = 3479741) B3479741
theorem B2319857 : Blo 1545470 2319857 := bstep (se 2 (by rfl) ⟨869946, by rfl⟩ : syracuseStep 2319857 = 1739893) B1739893
theorem B2319875 : Blo 1545470 2319875 := bstep (se 1 (by rfl) ⟨1739906, by rfl⟩ : syracuseStep 2319875 = 3479813) B3479813
theorem B2319905 : Blo 1545470 2319905 := bstep (se 2 (by rfl) ⟨869964, by rfl⟩ : syracuseStep 2319905 = 1739929) B1739929
theorem B7054897 : Blo 1545470 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B2319923 : Blo 1545470 2319923 := bstep (se 1 (by rfl) ⟨1739942, by rfl⟩ : syracuseStep 2319923 = 3479885) B3479885
theorem B2319953 : Blo 1545470 2319953 := bstep (se 2 (by rfl) ⟨869982, by rfl⟩ : syracuseStep 2319953 = 1739965) B1739965
theorem B2319971 : Blo 1545470 2319971 := bstep (se 1 (by rfl) ⟨1739978, by rfl⟩ : syracuseStep 2319971 = 3479957) B3479957
theorem B2320001 : Blo 1545470 2320001 := bstep (se 2 (by rfl) ⟨870000, by rfl⟩ : syracuseStep 2320001 = 1740001) B1740001
theorem B2320019 : Blo 1545470 2320019 := bstep (se 1 (by rfl) ⟨1740014, by rfl⟩ : syracuseStep 2320019 = 3480029) B3480029
theorem B5220017 : Blo 1545470 5220017 := bstep (se 2 (by rfl) ⟨1957506, by rfl⟩ : syracuseStep 5220017 = 3915013) B3915013
theorem B2320049 : Blo 1545470 2320049 := bstep (se 2 (by rfl) ⟨870018, by rfl⟩ : syracuseStep 2320049 = 1740037) B1740037
theorem B2320067 : Blo 1545470 2320067 := bstep (se 1 (by rfl) ⟨1740050, by rfl⟩ : syracuseStep 2320067 = 3480101) B3480101
theorem B2320097 : Blo 1545470 2320097 := bstep (se 2 (by rfl) ⟨870036, by rfl⟩ : syracuseStep 2320097 = 1740073) B1740073
theorem B2320115 : Blo 1545470 2320115 := bstep (se 1 (by rfl) ⟨1740086, by rfl⟩ : syracuseStep 2320115 = 3480173) B3480173
theorem B2090755 : Blo 1545470 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B2320145 : Blo 1545470 2320145 := bstep (se 2 (by rfl) ⟨870054, by rfl⟩ : syracuseStep 2320145 = 1740109) B1740109
theorem B2320163 : Blo 1545470 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B2320193 : Blo 1545470 2320193 := bstep (se 2 (by rfl) ⟨870072, by rfl⟩ : syracuseStep 2320193 = 1740145) B1740145
theorem B2320211 : Blo 1545470 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B7055203 : Blo 1545470 7055203 := bstep (se 1 (by rfl) ⟨5291402, by rfl⟩ : syracuseStep 7055203 = 10582805) B10582805
theorem B2320241 : Blo 1545470 2320241 := bstep (se 2 (by rfl) ⟨870090, by rfl⟩ : syracuseStep 2320241 = 1740181) B1740181
theorem B2320259 : Blo 1545470 2320259 := bstep (se 1 (by rfl) ⟨1740194, by rfl⟩ : syracuseStep 2320259 = 3480389) B3480389
theorem B2320289 : Blo 1545470 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B2320307 : Blo 1545470 2320307 := bstep (se 1 (by rfl) ⟨1740230, by rfl⟩ : syracuseStep 2320307 = 3480461) B3480461
theorem B2320337 : Blo 1545470 2320337 := bstep (se 2 (by rfl) ⟨870126, by rfl⟩ : syracuseStep 2320337 = 1740253) B1740253
theorem B1738723 : Blo 1545470 1738723 := bstep (se 1 (by rfl) ⟨1304042, by rfl⟩ : syracuseStep 1738723 = 2608085) B2608085
theorem B2476003 : Blo 1545470 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B2320355 : Blo 1545470 2320355 := bstep (se 1 (by rfl) ⟨1740266, by rfl⟩ : syracuseStep 2320355 = 3480533) B3480533
theorem B9914339 : Blo 1545470 9914339 := bstep (se 1 (by rfl) ⟨7435754, by rfl⟩ : syracuseStep 9914339 = 14871509) B14871509
theorem B2320385 : Blo 1545470 2320385 := bstep (se 2 (by rfl) ⟨870144, by rfl⟩ : syracuseStep 2320385 = 1740289) B1740289
theorem B4401155 : Blo 1545470 4401155 := bstep (se 1 (by rfl) ⟨3300866, by rfl⟩ : syracuseStep 4401155 = 6601733) B6601733
theorem B2934787 : Blo 1545470 2934787 := bstep (se 1 (by rfl) ⟨2201090, by rfl⟩ : syracuseStep 2934787 = 4402181) B4402181
theorem B2320403 : Blo 1545470 2320403 := bstep (se 1 (by rfl) ⟨1740302, by rfl⟩ : syracuseStep 2320403 = 3480605) B3480605
theorem B2320433 : Blo 1545470 2320433 := bstep (se 2 (by rfl) ⟨870162, by rfl⟩ : syracuseStep 2320433 = 1740325) B1740325
theorem B75221045 : Blo 1545470 75221045 := bstep (se 5 (by rfl) ⟨3525986, by rfl⟩ : syracuseStep 75221045 = 7051973) B7051973
theorem B17860661 : Blo 1545470 17860661 := bstep (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) B1674437
theorem B2320451 : Blo 1545470 2320451 := bstep (se 1 (by rfl) ⟨1740338, by rfl⟩ : syracuseStep 2320451 = 3480677) B3480677
theorem B6604877 : Blo 1545470 6604877 := bstep (se 3 (by rfl) ⟨1238414, by rfl⟩ : syracuseStep 6604877 = 2476829) B2476829
theorem B2320481 : Blo 1545470 2320481 := bstep (se 2 (by rfl) ⟨870180, by rfl⟩ : syracuseStep 2320481 = 1740361) B1740361
theorem B1738867 : Blo 1545470 1738867 := bstep (se 1 (by rfl) ⟨1304150, by rfl⟩ : syracuseStep 1738867 = 2608301) B2608301
theorem B2320499 : Blo 1545470 2320499 := bstep (se 1 (by rfl) ⟨1740374, by rfl⟩ : syracuseStep 2320499 = 3480749) B3480749
theorem B2320529 : Blo 1545470 2320529 := bstep (se 2 (by rfl) ⟨870198, by rfl⟩ : syracuseStep 2320529 = 1740397) B1740397
theorem B7825571 : Blo 1545470 7825571 := bstep (se 1 (by rfl) ⟨5869178, by rfl⟩ : syracuseStep 7825571 = 11738357) B11738357
theorem B2934947 : Blo 1545470 2934947 := bstep (se 1 (by rfl) ⟨2201210, by rfl⟩ : syracuseStep 2934947 = 4402421) B4402421
theorem B2320547 : Blo 1545470 2320547 := bstep (se 1 (by rfl) ⟨1740410, by rfl⟩ : syracuseStep 2320547 = 3480821) B3480821
theorem B2320577 : Blo 1545470 2320577 := bstep (se 2 (by rfl) ⟨870216, by rfl⟩ : syracuseStep 2320577 = 1740433) B1740433
theorem B5220557 : Blo 1545470 5220557 := bstep (se 3 (by rfl) ⟨978854, by rfl⟩ : syracuseStep 5220557 = 1957709) B1957709
theorem B2320595 : Blo 1545470 2320595 := bstep (se 1 (by rfl) ⟨1740446, by rfl⟩ : syracuseStep 2320595 = 3480893) B3480893
theorem B89163989 : Blo 1545470 89163989 := bstep (se 7 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 89163989 = 2089781) B2089781
theorem B8808689 : Blo 1545470 8808689 := bstep (se 2 (by rfl) ⟨3303258, by rfl⟩ : syracuseStep 8808689 = 6606517) B6606517
theorem B2320625 : Blo 1545470 2320625 := bstep (se 2 (by rfl) ⟨870234, by rfl⟩ : syracuseStep 2320625 = 1740469) B1740469
theorem B3524867 : Blo 1545470 3524867 := bstep (se 1 (by rfl) ⟨2643650, by rfl⟩ : syracuseStep 3524867 = 5287301) B5287301
theorem B1739011 : Blo 1545470 1739011 := bstep (se 1 (by rfl) ⟨1304258, by rfl⟩ : syracuseStep 1739011 = 2608517) B2608517
theorem B5220611 : Blo 1545470 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B2320643 : Blo 1545470 2320643 := bstep (se 1 (by rfl) ⟨1740482, by rfl⟩ : syracuseStep 2320643 = 3480965) B3480965
theorem B2320673 : Blo 1545470 2320673 := bstep (se 2 (by rfl) ⟨870252, by rfl⟩ : syracuseStep 2320673 = 1740505) B1740505
theorem B2320691 : Blo 1545470 2320691 := bstep (se 1 (by rfl) ⟨1740518, by rfl⟩ : syracuseStep 2320691 = 3481037) B3481037
theorem B2320721 : Blo 1545470 2320721 := bstep (se 2 (by rfl) ⟨870270, by rfl⟩ : syracuseStep 2320721 = 1740541) B1740541
theorem B2320739 : Blo 1545470 2320739 := bstep (se 1 (by rfl) ⟨1740554, by rfl⟩ : syracuseStep 2320739 = 3481109) B3481109
theorem B16714097 : Blo 1545470 16714097 := bstep (se 2 (by rfl) ⟨6267786, by rfl⟩ : syracuseStep 16714097 = 12535573) B12535573
theorem B2091377 : Blo 1545470 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B2320769 : Blo 1545470 2320769 := bstep (se 2 (by rfl) ⟨870288, by rfl⟩ : syracuseStep 2320769 = 1740577) B1740577
theorem B1739155 : Blo 1545470 1739155 := bstep (se 1 (by rfl) ⟨1304366, by rfl⟩ : syracuseStep 1739155 = 2608733) B2608733
theorem B2320787 : Blo 1545470 2320787 := bstep (se 1 (by rfl) ⟨1740590, by rfl⟩ : syracuseStep 2320787 = 3481181) B3481181
theorem B2091425 : Blo 1545470 2091425 := bstep (se 2 (by rfl) ⟨784284, by rfl⟩ : syracuseStep 2091425 = 1568569) B1568569
theorem B6605219 : Blo 1545470 6605219 := bstep (se 1 (by rfl) ⟨4953914, by rfl⟩ : syracuseStep 6605219 = 9907829) B9907829
theorem B2320817 : Blo 1545470 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B2320835 : Blo 1545470 2320835 := bstep (se 1 (by rfl) ⟨1740626, by rfl⟩ : syracuseStep 2320835 = 3481253) B3481253
theorem B8358349 : Blo 1545470 8358349 := bstep (se 3 (by rfl) ⟨1567190, by rfl⟩ : syracuseStep 8358349 = 3134381) B3134381
theorem B2320865 : Blo 1545470 2320865 := bstep (se 2 (by rfl) ⟨870324, by rfl⟩ : syracuseStep 2320865 = 1740649) B1740649
theorem B2320883 : Blo 1545470 2320883 := bstep (se 1 (by rfl) ⟨1740662, by rfl⟩ : syracuseStep 2320883 = 3481325) B3481325
theorem B7432717 : Blo 1545470 7432717 := bstep (se 3 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 7432717 = 2787269) B2787269
theorem B5220881 : Blo 1545470 5220881 := bstep (se 2 (by rfl) ⟨1957830, by rfl⟩ : syracuseStep 5220881 = 3915661) B3915661
theorem B2320913 : Blo 1545470 2320913 := bstep (se 2 (by rfl) ⟨870342, by rfl⟩ : syracuseStep 2320913 = 1740685) B1740685
theorem B1739299 : Blo 1545470 1739299 := bstep (se 1 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 1739299 = 2608949) B2608949
theorem B2787875 : Blo 1545470 2787875 := bstep (se 1 (by rfl) ⟨2090906, by rfl⟩ : syracuseStep 2787875 = 4181813) B4181813
theorem B2320931 : Blo 1545470 2320931 := bstep (se 1 (by rfl) ⟨1740698, by rfl⟩ : syracuseStep 2320931 = 3481397) B3481397
theorem B2320961 : Blo 1545470 2320961 := bstep (se 2 (by rfl) ⟨870360, by rfl⟩ : syracuseStep 2320961 = 1740721) B1740721
theorem B3304003 : Blo 1545470 3304003 := bstep (se 1 (by rfl) ⟨2478002, by rfl⟩ : syracuseStep 3304003 = 4956005) B4956005
theorem B2320979 : Blo 1545470 2320979 := bstep (se 1 (by rfl) ⟨1740734, by rfl⟩ : syracuseStep 2320979 = 3481469) B3481469
theorem B2321009 : Blo 1545470 2321009 := bstep (se 2 (by rfl) ⟨870378, by rfl⟩ : syracuseStep 2321009 = 1740757) B1740757
theorem B2476675 : Blo 1545470 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B2321027 : Blo 1545470 2321027 := bstep (se 1 (by rfl) ⟨1740770, by rfl⟩ : syracuseStep 2321027 = 3481541) B3481541
theorem B2321057 : Blo 1545470 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B1739443 : Blo 1545470 1739443 := bstep (se 1 (by rfl) ⟨1304582, by rfl⟩ : syracuseStep 1739443 = 2609165) B2609165
theorem B2321075 : Blo 1545470 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B2321105 : Blo 1545470 2321105 := bstep (se 2 (by rfl) ⟨870414, by rfl⟩ : syracuseStep 2321105 = 1740829) B1740829
theorem B1673939 : Blo 1545470 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B75270869 : Blo 1545470 75270869 := bstep (se 7 (by rfl) ⟨882080, by rfl⟩ : syracuseStep 75270869 = 1764161) B1764161
theorem B2321123 : Blo 1545470 2321123 := bstep (se 1 (by rfl) ⟨1740842, by rfl⟩ : syracuseStep 2321123 = 3481685) B3481685
theorem B2321153 : Blo 1545470 2321153 := bstep (se 2 (by rfl) ⟨870432, by rfl⟩ : syracuseStep 2321153 = 1740865) B1740865
theorem B1567507 : Blo 1545470 1567507 := bstep (se 1 (by rfl) ⟨1175630, by rfl⟩ : syracuseStep 1567507 = 2351261) B2351261
theorem B2321171 : Blo 1545470 2321171 := bstep (se 1 (by rfl) ⟨1740878, by rfl⟩ : syracuseStep 2321171 = 3481757) B3481757
theorem B4401965 : Blo 1545470 4401965 := bstep (se 3 (by rfl) ⟨825368, by rfl⟩ : syracuseStep 4401965 = 1650737) B1650737
theorem B2321201 : Blo 1545470 2321201 := bstep (se 2 (by rfl) ⟨870450, by rfl⟩ : syracuseStep 2321201 = 1740901) B1740901
theorem B1739587 : Blo 1545470 1739587 := bstep (se 1 (by rfl) ⟨1304690, by rfl⟩ : syracuseStep 1739587 = 2609381) B2609381
theorem B2608051 : Blo 1545470 2608051 := bstep (se 1 (by rfl) ⟨1956038, by rfl⟩ : syracuseStep 2608051 = 3912077) B3912077
theorem B1764275 : Blo 1545470 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B7826381 : Blo 1545470 7826381 := bstep (se 3 (by rfl) ⟨1467446, by rfl⟩ : syracuseStep 7826381 = 2934893) B2934893
theorem B1739731 : Blo 1545470 1739731 := bstep (se 1 (by rfl) ⟨1304798, by rfl⟩ : syracuseStep 1739731 = 2609597) B2609597
theorem B4402147 : Blo 1545470 4402147 := bstep (se 1 (by rfl) ⟨3301610, by rfl⟩ : syracuseStep 4402147 = 6603221) B6603221
theorem B2788337 : Blo 1545470 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B5868557 : Blo 1545470 5868557 := bstep (se 3 (by rfl) ⟨1100354, by rfl⟩ : syracuseStep 5868557 = 2200709) B2200709
theorem B3623953 : Blo 1545470 3623953 := bstep (se 2 (by rfl) ⟨1358982, by rfl⟩ : syracuseStep 3623953 = 2717965) B2717965
theorem B5221421 : Blo 1545470 5221421 := bstep (se 3 (by rfl) ⟨979016, by rfl⟩ : syracuseStep 5221421 = 1958033) B1958033
theorem B2608193 : Blo 1545470 2608193 := bstep (se 2 (by rfl) ⟨978072, by rfl⟩ : syracuseStep 2608193 = 1956145) B1956145
theorem B2477137 : Blo 1545470 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B1739875 : Blo 1545470 1739875 := bstep (se 1 (by rfl) ⟨1304906, by rfl⟩ : syracuseStep 1739875 = 2609813) B2609813
theorem B5221475 : Blo 1545470 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B2477233 : Blo 1545470 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B2608321 : Blo 1545470 2608321 := bstep (se 2 (by rfl) ⟨978120, by rfl⟩ : syracuseStep 2608321 = 1956241) B1956241
theorem B8359109 : Blo 1545470 8359109 := bstep (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) B1567333
theorem B2936017 : Blo 1545470 2936017 := bstep (se 2 (by rfl) ⟨1101006, by rfl⟩ : syracuseStep 2936017 = 2202013) B2202013
theorem B2608355 : Blo 1545470 2608355 := bstep (se 1 (by rfl) ⟨1956266, by rfl⟩ : syracuseStep 2608355 = 3912533) B3912533
theorem B1740019 : Blo 1545470 1740019 := bstep (se 1 (by rfl) ⟨1305014, by rfl⟩ : syracuseStep 1740019 = 2610029) B2610029
theorem B2477393 : Blo 1545470 2477393 := bstep (se 2 (by rfl) ⟨929022, by rfl⟩ : syracuseStep 2477393 = 1858045) B1858045
theorem B2608483 : Blo 1545470 2608483 := bstep (se 1 (by rfl) ⟨1956362, by rfl⟩ : syracuseStep 2608483 = 3912725) B3912725
theorem B5221745 : Blo 1545470 5221745 := bstep (se 2 (by rfl) ⟨1958154, by rfl⟩ : syracuseStep 5221745 = 3916309) B3916309
theorem B1740163 : Blo 1545470 1740163 := bstep (se 1 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 1740163 = 2610245) B2610245
theorem B4402637 : Blo 1545470 4402637 := bstep (se 3 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 4402637 = 1650989) B1650989
theorem B4951505 : Blo 1545470 4951505 := bstep (se 2 (by rfl) ⟨1856814, by rfl⟩ : syracuseStep 4951505 = 3713629) B3713629
theorem B2608625 : Blo 1545470 2608625 := bstep (se 2 (by rfl) ⟨978234, by rfl⟩ : syracuseStep 2608625 = 1956469) B1956469
theorem B1740307 : Blo 1545470 1740307 := bstep (se 1 (by rfl) ⟨1305230, by rfl⟩ : syracuseStep 1740307 = 2610461) B2610461
theorem B2608753 : Blo 1545470 2608753 := bstep (se 2 (by rfl) ⟨978282, by rfl⟩ : syracuseStep 2608753 = 1956565) B1956565
theorem B2608787 : Blo 1545470 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B8810147 : Blo 1545470 8810147 := bstep (se 1 (by rfl) ⟨6607610, by rfl⟩ : syracuseStep 8810147 = 13215221) B13215221
theorem B1740451 : Blo 1545470 1740451 := bstep (se 1 (by rfl) ⟨1305338, by rfl⟩ : syracuseStep 1740451 = 2610677) B2610677
theorem B18820835 : Blo 1545470 18820835 := bstep (se 1 (by rfl) ⟨14115626, by rfl⟩ : syracuseStep 18820835 = 28231253) B28231253
theorem B2608915 : Blo 1545470 2608915 := bstep (se 1 (by rfl) ⟨1956686, by rfl⟩ : syracuseStep 2608915 = 3913373) B3913373
theorem B5869361 : Blo 1545470 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B1740595 : Blo 1545470 1740595 := bstep (se 1 (by rfl) ⟨1305446, by rfl⟩ : syracuseStep 1740595 = 2610893) B2610893
theorem B3477329 : Blo 1545470 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B3477347 : Blo 1545470 3477347 := bstep (se 1 (by rfl) ⟨2608010, by rfl⟩ : syracuseStep 3477347 = 5216021) B5216021
theorem B5222285 : Blo 1545470 5222285 := bstep (se 3 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 5222285 = 1958357) B1958357
theorem B2609057 : Blo 1545470 2609057 := bstep (se 2 (by rfl) ⟨978396, by rfl⟩ : syracuseStep 2609057 = 1956793) B1956793
theorem B1740739 : Blo 1545470 1740739 := bstep (se 1 (by rfl) ⟨1305554, by rfl⟩ : syracuseStep 1740739 = 2611109) B2611109
theorem B5222339 : Blo 1545470 5222339 := bstep (se 1 (by rfl) ⟨3916754, by rfl⟩ : syracuseStep 5222339 = 7833509) B7833509
theorem B11743217 : Blo 1545470 11743217 := bstep (se 2 (by rfl) ⟨4403706, by rfl⟩ : syracuseStep 11743217 = 8807413) B8807413
theorem B2609185 : Blo 1545470 2609185 := bstep (se 2 (by rfl) ⟨978444, by rfl⟩ : syracuseStep 2609185 = 1956889) B1956889
theorem B2609219 : Blo 1545470 2609219 := bstep (se 1 (by rfl) ⟨1956914, by rfl⟩ : syracuseStep 2609219 = 3913829) B3913829
theorem B1740883 : Blo 1545470 1740883 := bstep (se 1 (by rfl) ⟨1305662, by rfl⟩ : syracuseStep 1740883 = 2611325) B2611325
theorem B3477617 : Blo 1545470 3477617 := bstep (se 2 (by rfl) ⟨1304106, by rfl⟩ : syracuseStep 3477617 = 2608213) B2608213
theorem B6697073 : Blo 1545470 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B3477635 : Blo 1545470 3477635 := bstep (se 1 (by rfl) ⟨2608226, by rfl⟩ : syracuseStep 3477635 = 5216453) B5216453
theorem B3715235 : Blo 1545470 3715235 := bstep (se 1 (by rfl) ⟨2786426, by rfl⟩ : syracuseStep 3715235 = 5572853) B5572853
theorem B2609347 : Blo 1545470 2609347 := bstep (se 1 (by rfl) ⟨1957010, by rfl⟩ : syracuseStep 2609347 = 3914021) B3914021
theorem B5222609 : Blo 1545470 5222609 := bstep (se 2 (by rfl) ⟨1958478, by rfl⟩ : syracuseStep 5222609 = 3916957) B3916957
theorem B40153315 : Blo 1545470 40153315 := bstep (se 1 (by rfl) ⟨30114986, by rfl⟩ : syracuseStep 40153315 = 60229973) B60229973
theorem B2937073 : Blo 1545470 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B2609489 : Blo 1545470 2609489 := bstep (se 2 (by rfl) ⟨978558, by rfl⟩ : syracuseStep 2609489 = 1957117) B1957117
theorem B3477905 : Blo 1545470 3477905 := bstep (se 2 (by rfl) ⟨1304214, by rfl⟩ : syracuseStep 3477905 = 2608429) B2608429
theorem B3477923 : Blo 1545470 3477923 := bstep (se 1 (by rfl) ⟨2608442, by rfl⟩ : syracuseStep 3477923 = 5216885) B5216885
theorem B5870029 : Blo 1545470 5870029 := bstep (se 3 (by rfl) ⟨1100630, by rfl⟩ : syracuseStep 5870029 = 2201261) B2201261
theorem B2609617 : Blo 1545470 2609617 := bstep (se 2 (by rfl) ⟨978606, by rfl⟩ : syracuseStep 2609617 = 1957213) B1957213
theorem B2609651 : Blo 1545470 2609651 := bstep (se 1 (by rfl) ⟨1957238, by rfl⟩ : syracuseStep 2609651 = 3914477) B3914477
theorem B3912209 : Blo 1545470 3912209 := bstep (se 2 (by rfl) ⟨1467078, by rfl⟩ : syracuseStep 3912209 = 2934157) B2934157
theorem B3912259 : Blo 1545470 3912259 := bstep (se 1 (by rfl) ⟨2934194, by rfl⟩ : syracuseStep 3912259 = 5868389) B5868389
theorem B4403821 : Blo 1545470 4403821 := bstep (se 3 (by rfl) ⟨825716, by rfl⟩ : syracuseStep 4403821 = 1651433) B1651433
theorem B2609779 : Blo 1545470 2609779 := bstep (se 1 (by rfl) ⟨1957334, by rfl⟩ : syracuseStep 2609779 = 3914669) B3914669
theorem B2937475 : Blo 1545470 2937475 := bstep (se 1 (by rfl) ⟨2203106, by rfl⟩ : syracuseStep 2937475 = 4406213) B4406213
theorem B3478193 : Blo 1545470 3478193 := bstep (se 2 (by rfl) ⟨1304322, by rfl⟩ : syracuseStep 3478193 = 2608645) B2608645
theorem B2937521 : Blo 1545470 2937521 := bstep (se 2 (by rfl) ⟨1101570, by rfl⟩ : syracuseStep 2937521 = 2203141) B2203141
theorem B3478211 : Blo 1545470 3478211 := bstep (se 1 (by rfl) ⟨2608658, by rfl⟩ : syracuseStep 3478211 = 5217317) B5217317
theorem B3912401 : Blo 1545470 3912401 := bstep (se 2 (by rfl) ⟨1467150, by rfl⟩ : syracuseStep 3912401 = 2934301) B2934301
theorem B20083427 : Blo 1545470 20083427 := bstep (se 1 (by rfl) ⟨15062570, by rfl⟩ : syracuseStep 20083427 = 30125141) B30125141
theorem B2609921 : Blo 1545470 2609921 := bstep (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) B1957441
theorem B2610049 : Blo 1545470 2610049 := bstep (se 2 (by rfl) ⟨978768, by rfl⟩ : syracuseStep 2610049 = 1957537) B1957537
theorem B2610083 : Blo 1545470 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B3478481 : Blo 1545470 3478481 := bstep (se 2 (by rfl) ⟨1304430, by rfl⟩ : syracuseStep 3478481 = 2608861) B2608861
theorem B3478499 : Blo 1545470 3478499 := bstep (se 1 (by rfl) ⟨2608874, by rfl⟩ : syracuseStep 3478499 = 5217749) B5217749
theorem B8803313 : Blo 1545470 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B2610211 : Blo 1545470 2610211 := bstep (se 1 (by rfl) ⟨1957658, by rfl⟩ : syracuseStep 2610211 = 3915317) B3915317
theorem B1651843 : Blo 1545470 1651843 := bstep (se 1 (by rfl) ⟨1238882, by rfl⟩ : syracuseStep 1651843 = 2477765) B2477765
theorem B3134609 : Blo 1545470 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B2610353 : Blo 1545470 2610353 := bstep (se 2 (by rfl) ⟨978882, by rfl⟩ : syracuseStep 2610353 = 1957765) B1957765
theorem B5870819 : Blo 1545470 5870819 := bstep (se 1 (by rfl) ⟨4403114, by rfl⟩ : syracuseStep 5870819 = 8806229) B8806229
theorem B16954595 : Blo 1545470 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B2200817 : Blo 1545470 2200817 := bstep (se 2 (by rfl) ⟨825306, by rfl⟩ : syracuseStep 2200817 = 1650613) B1650613
theorem B3478769 : Blo 1545470 3478769 := bstep (se 2 (by rfl) ⟨1304538, by rfl⟩ : syracuseStep 3478769 = 2609077) B2609077
theorem B1545475 : Blo 1545470 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B3478787 : Blo 1545470 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B1545491 : Blo 1545470 1545491 := bstep (se 1 (by rfl) ⟨1159118, by rfl⟩ : syracuseStep 1545491 = 2318237) B2318237
theorem B1545507 : Blo 1545470 1545507 := bstep (se 1 (by rfl) ⟨1159130, by rfl⟩ : syracuseStep 1545507 = 2318261) B2318261
theorem B2610481 : Blo 1545470 2610481 := bstep (se 2 (by rfl) ⟨978930, by rfl⟩ : syracuseStep 2610481 = 1957861) B1957861
theorem B1545523 : Blo 1545470 1545523 := bstep (se 1 (by rfl) ⟨1159142, by rfl⟩ : syracuseStep 1545523 = 2318285) B2318285
theorem B1545539 : Blo 1545470 1545539 := bstep (se 1 (by rfl) ⟨1159154, by rfl⟩ : syracuseStep 1545539 = 2318309) B2318309
theorem B1545555 : Blo 1545470 1545555 := bstep (se 1 (by rfl) ⟨1159166, by rfl⟩ : syracuseStep 1545555 = 2318333) B2318333
theorem B2610515 : Blo 1545470 2610515 := bstep (se 1 (by rfl) ⟨1957886, by rfl⟩ : syracuseStep 2610515 = 3915773) B3915773
theorem B1545571 : Blo 1545470 1545571 := bstep (se 1 (by rfl) ⟨1159178, by rfl⟩ : syracuseStep 1545571 = 2318357) B2318357
theorem B1545587 : Blo 1545470 1545587 := bstep (se 1 (by rfl) ⟨1159190, by rfl⟩ : syracuseStep 1545587 = 2318381) B2318381
theorem B1545603 : Blo 1545470 1545603 := bstep (se 1 (by rfl) ⟨1159202, by rfl⟩ : syracuseStep 1545603 = 2318405) B2318405
theorem B12719501 : Blo 1545470 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1545619 : Blo 1545470 1545619 := bstep (se 1 (by rfl) ⟨1159214, by rfl⟩ : syracuseStep 1545619 = 2318429) B2318429
theorem B1545635 : Blo 1545470 1545635 := bstep (se 1 (by rfl) ⟨1159226, by rfl⟩ : syracuseStep 1545635 = 2318453) B2318453
theorem B1545651 : Blo 1545470 1545651 := bstep (se 1 (by rfl) ⟨1159238, by rfl⟩ : syracuseStep 1545651 = 2318477) B2318477
theorem B1545667 : Blo 1545470 1545667 := bstep (se 1 (by rfl) ⟨1159250, by rfl⟩ : syracuseStep 1545667 = 2318501) B2318501
theorem B1545683 : Blo 1545470 1545683 := bstep (se 1 (by rfl) ⟨1159262, by rfl⟩ : syracuseStep 1545683 = 2318525) B2318525
theorem B2610643 : Blo 1545470 2610643 := bstep (se 1 (by rfl) ⟨1957982, by rfl⟩ : syracuseStep 2610643 = 3915965) B3915965
theorem B1545699 : Blo 1545470 1545699 := bstep (se 1 (by rfl) ⟨1159274, by rfl⟩ : syracuseStep 1545699 = 2318549) B2318549
theorem B1545715 : Blo 1545470 1545715 := bstep (se 1 (by rfl) ⟨1159286, by rfl⟩ : syracuseStep 1545715 = 2318573) B2318573
theorem B1545731 : Blo 1545470 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B9410053 : Blo 1545470 9410053 := bstep (se 4 (by rfl) ⟨882192, by rfl⟩ : syracuseStep 9410053 = 1764385) B1764385
theorem B3479057 : Blo 1545470 3479057 := bstep (se 2 (by rfl) ⟨1304646, by rfl⟩ : syracuseStep 3479057 = 2609293) B2609293
theorem B1545747 : Blo 1545470 1545747 := bstep (se 1 (by rfl) ⟨1159310, by rfl⟩ : syracuseStep 1545747 = 2318621) B2318621
theorem B1545763 : Blo 1545470 1545763 := bstep (se 1 (by rfl) ⟨1159322, by rfl⟩ : syracuseStep 1545763 = 2318645) B2318645
theorem B3479075 : Blo 1545470 3479075 := bstep (se 1 (by rfl) ⟨2609306, by rfl⟩ : syracuseStep 3479075 = 5218613) B5218613
theorem B1545779 : Blo 1545470 1545779 := bstep (se 1 (by rfl) ⟨1159334, by rfl⟩ : syracuseStep 1545779 = 2318669) B2318669
theorem B1652275 : Blo 1545470 1652275 := bstep (se 1 (by rfl) ⟨1239206, by rfl⟩ : syracuseStep 1652275 = 2478413) B2478413
theorem B1545795 : Blo 1545470 1545795 := bstep (se 1 (by rfl) ⟨1159346, by rfl⟩ : syracuseStep 1545795 = 2318693) B2318693
theorem B1545811 : Blo 1545470 1545811 := bstep (se 1 (by rfl) ⟨1159358, by rfl⟩ : syracuseStep 1545811 = 2318717) B2318717
theorem B2610785 : Blo 1545470 2610785 := bstep (se 2 (by rfl) ⟨979044, by rfl⟩ : syracuseStep 2610785 = 1958089) B1958089
theorem B1545827 : Blo 1545470 1545827 := bstep (se 1 (by rfl) ⟨1159370, by rfl⟩ : syracuseStep 1545827 = 2318741) B2318741
theorem B1545843 : Blo 1545470 1545843 := bstep (se 1 (by rfl) ⟨1159382, by rfl⟩ : syracuseStep 1545843 = 2318765) B2318765
theorem B1545859 : Blo 1545470 1545859 := bstep (se 1 (by rfl) ⟨1159394, by rfl⟩ : syracuseStep 1545859 = 2318789) B2318789
theorem B4404881 : Blo 1545470 4404881 := bstep (se 2 (by rfl) ⟨1651830, by rfl⟩ : syracuseStep 4404881 = 3303661) B3303661
theorem B1545875 : Blo 1545470 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B1545891 : Blo 1545470 1545891 := bstep (se 1 (by rfl) ⟨1159418, by rfl⟩ : syracuseStep 1545891 = 2318837) B2318837
theorem B3913393 : Blo 1545470 3913393 := bstep (se 2 (by rfl) ⟨1467522, by rfl⟩ : syracuseStep 3913393 = 2935045) B2935045
theorem B1545907 : Blo 1545470 1545907 := bstep (se 1 (by rfl) ⟨1159430, by rfl⟩ : syracuseStep 1545907 = 2318861) B2318861
theorem B1545923 : Blo 1545470 1545923 := bstep (se 1 (by rfl) ⟨1159442, by rfl⟩ : syracuseStep 1545923 = 2318885) B2318885
theorem B1545939 : Blo 1545470 1545939 := bstep (se 1 (by rfl) ⟨1159454, by rfl⟩ : syracuseStep 1545939 = 2318909) B2318909
theorem B2610913 : Blo 1545470 2610913 := bstep (se 2 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 2610913 = 1958185) B1958185
theorem B1545955 : Blo 1545470 1545955 := bstep (se 1 (by rfl) ⟨1159466, by rfl⟩ : syracuseStep 1545955 = 2318933) B2318933
theorem B1545971 : Blo 1545470 1545971 := bstep (se 1 (by rfl) ⟨1159478, by rfl⟩ : syracuseStep 1545971 = 2318957) B2318957
theorem B1545987 : Blo 1545470 1545987 := bstep (se 1 (by rfl) ⟨1159490, by rfl⟩ : syracuseStep 1545987 = 2318981) B2318981
theorem B2201347 : Blo 1545470 2201347 := bstep (se 1 (by rfl) ⟨1651010, by rfl⟩ : syracuseStep 2201347 = 3302021) B3302021
theorem B2610947 : Blo 1545470 2610947 := bstep (se 1 (by rfl) ⟨1958210, by rfl⟩ : syracuseStep 2610947 = 3916421) B3916421
theorem B1546003 : Blo 1545470 1546003 := bstep (se 1 (by rfl) ⟨1159502, by rfl⟩ : syracuseStep 1546003 = 2319005) B2319005
theorem B1546019 : Blo 1545470 1546019 := bstep (se 1 (by rfl) ⟨1159514, by rfl⟩ : syracuseStep 1546019 = 2319029) B2319029
theorem B3479345 : Blo 1545470 3479345 := bstep (se 2 (by rfl) ⟨1304754, by rfl⟩ : syracuseStep 3479345 = 2609509) B2609509
theorem B7829297 : Blo 1545470 7829297 := bstep (se 2 (by rfl) ⟨2935986, by rfl⟩ : syracuseStep 7829297 = 5871973) B5871973
theorem B1546035 : Blo 1545470 1546035 := bstep (se 1 (by rfl) ⟨1159526, by rfl⟩ : syracuseStep 1546035 = 2319053) B2319053
theorem B3528497 : Blo 1545470 3528497 := bstep (se 2 (by rfl) ⟨1323186, by rfl⟩ : syracuseStep 3528497 = 2646373) B2646373
theorem B1546051 : Blo 1545470 1546051 := bstep (se 1 (by rfl) ⟨1159538, by rfl⟩ : syracuseStep 1546051 = 2319077) B2319077
theorem B3479363 : Blo 1545470 3479363 := bstep (se 1 (by rfl) ⟨2609522, by rfl⟩ : syracuseStep 3479363 = 5219045) B5219045
theorem B1546067 : Blo 1545470 1546067 := bstep (se 1 (by rfl) ⟨1159550, by rfl⟩ : syracuseStep 1546067 = 2319101) B2319101
theorem B1546083 : Blo 1545470 1546083 := bstep (se 1 (by rfl) ⟨1159562, by rfl⟩ : syracuseStep 1546083 = 2319125) B2319125
theorem B4953965 : Blo 1545470 4953965 := bstep (se 3 (by rfl) ⟨928868, by rfl⟩ : syracuseStep 4953965 = 1857737) B1857737
theorem B5871473 : Blo 1545470 5871473 := bstep (se 2 (by rfl) ⟨2201802, by rfl⟩ : syracuseStep 5871473 = 4403605) B4403605
theorem B1546099 : Blo 1545470 1546099 := bstep (se 1 (by rfl) ⟨1159574, by rfl⟩ : syracuseStep 1546099 = 2319149) B2319149
theorem B1546115 : Blo 1545470 1546115 := bstep (se 1 (by rfl) ⟨1159586, by rfl⟩ : syracuseStep 1546115 = 2319173) B2319173
theorem B2611075 : Blo 1545470 2611075 := bstep (se 1 (by rfl) ⟨1958306, by rfl⟩ : syracuseStep 2611075 = 3916613) B3916613
theorem B29718413 : Blo 1545470 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B1546131 : Blo 1545470 1546131 := bstep (se 1 (by rfl) ⟨1159598, by rfl⟩ : syracuseStep 1546131 = 2319197) B2319197
theorem B1546147 : Blo 1545470 1546147 := bstep (se 1 (by rfl) ⟨1159610, by rfl⟩ : syracuseStep 1546147 = 2319221) B2319221
theorem B1546163 : Blo 1545470 1546163 := bstep (se 1 (by rfl) ⟨1159622, by rfl⟩ : syracuseStep 1546163 = 2319245) B2319245
theorem B3913667 : Blo 1545470 3913667 := bstep (se 1 (by rfl) ⟨2935250, by rfl⟩ : syracuseStep 3913667 = 5870501) B5870501
theorem B1546179 : Blo 1545470 1546179 := bstep (se 1 (by rfl) ⟨1159634, by rfl⟩ : syracuseStep 1546179 = 2319269) B2319269
theorem B9402317 : Blo 1545470 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B1546195 : Blo 1545470 1546195 := bstep (se 1 (by rfl) ⟨1159646, by rfl⟩ : syracuseStep 1546195 = 2319293) B2319293
theorem B1546211 : Blo 1545470 1546211 := bstep (se 1 (by rfl) ⟨1159658, by rfl⟩ : syracuseStep 1546211 = 2319317) B2319317
theorem B5216237 : Blo 1545470 5216237 := bstep (se 3 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 5216237 = 1956089) B1956089
theorem B1546227 : Blo 1545470 1546227 := bstep (se 1 (by rfl) ⟨1159670, by rfl⟩ : syracuseStep 1546227 = 2319341) B2319341
theorem B1546243 : Blo 1545470 1546243 := bstep (se 1 (by rfl) ⟨1159682, by rfl⟩ : syracuseStep 1546243 = 2319365) B2319365
theorem B2611217 : Blo 1545470 2611217 := bstep (se 2 (by rfl) ⟨979206, by rfl⟩ : syracuseStep 2611217 = 1958413) B1958413
theorem B1546259 : Blo 1545470 1546259 := bstep (se 1 (by rfl) ⟨1159694, by rfl⟩ : syracuseStep 1546259 = 2319389) B2319389
theorem B5216291 : Blo 1545470 5216291 := bstep (se 1 (by rfl) ⟨3912218, by rfl⟩ : syracuseStep 5216291 = 7824437) B7824437
theorem B1546275 : Blo 1545470 1546275 := bstep (se 1 (by rfl) ⟨1159706, by rfl⟩ : syracuseStep 1546275 = 2319413) B2319413
theorem B1546291 : Blo 1545470 1546291 := bstep (se 1 (by rfl) ⟨1159718, by rfl⟩ : syracuseStep 1546291 = 2319437) B2319437
theorem B1546307 : Blo 1545470 1546307 := bstep (se 1 (by rfl) ⟨1159730, by rfl⟩ : syracuseStep 1546307 = 2319461) B2319461
theorem B3479633 : Blo 1545470 3479633 := bstep (se 2 (by rfl) ⟨1304862, by rfl⟩ : syracuseStep 3479633 = 2609725) B2609725
theorem B2201683 : Blo 1545470 2201683 := bstep (se 1 (by rfl) ⟨1651262, by rfl⟩ : syracuseStep 2201683 = 3302525) B3302525
theorem B1546323 : Blo 1545470 1546323 := bstep (se 1 (by rfl) ⟨1159742, by rfl⟩ : syracuseStep 1546323 = 2319485) B2319485
theorem B1546339 : Blo 1545470 1546339 := bstep (se 1 (by rfl) ⟨1159754, by rfl⟩ : syracuseStep 1546339 = 2319509) B2319509
theorem B3479651 : Blo 1545470 3479651 := bstep (se 1 (by rfl) ⟨2609738, by rfl⟩ : syracuseStep 3479651 = 5219477) B5219477
theorem B1546355 : Blo 1545470 1546355 := bstep (se 1 (by rfl) ⟨1159766, by rfl⟩ : syracuseStep 1546355 = 2319533) B2319533
theorem B3913859 : Blo 1545470 3913859 := bstep (se 1 (by rfl) ⟨2935394, by rfl⟩ : syracuseStep 3913859 = 5870789) B5870789
theorem B1546371 : Blo 1545470 1546371 := bstep (se 1 (by rfl) ⟨1159778, by rfl⟩ : syracuseStep 1546371 = 2319557) B2319557
theorem B5576845 : Blo 1545470 5576845 := bstep (se 3 (by rfl) ⟨1045658, by rfl⟩ : syracuseStep 5576845 = 2091317) B2091317
theorem B1546387 : Blo 1545470 1546387 := bstep (se 1 (by rfl) ⟨1159790, by rfl⟩ : syracuseStep 1546387 = 2319581) B2319581
theorem B2611345 : Blo 1545470 2611345 := bstep (se 2 (by rfl) ⟨979254, by rfl⟩ : syracuseStep 2611345 = 1958509) B1958509
theorem B1546403 : Blo 1545470 1546403 := bstep (se 1 (by rfl) ⟨1159802, by rfl⟩ : syracuseStep 1546403 = 2319605) B2319605
theorem B1546419 : Blo 1545470 1546419 := bstep (se 1 (by rfl) ⟨1159814, by rfl⟩ : syracuseStep 1546419 = 2319629) B2319629
theorem B1546435 : Blo 1545470 1546435 := bstep (se 1 (by rfl) ⟨1159826, by rfl⟩ : syracuseStep 1546435 = 2319653) B2319653
theorem B1546451 : Blo 1545470 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B1546467 : Blo 1545470 1546467 := bstep (se 1 (by rfl) ⟨1159850, by rfl⟩ : syracuseStep 1546467 = 2319701) B2319701
theorem B1546483 : Blo 1545470 1546483 := bstep (se 1 (by rfl) ⟨1159862, by rfl⟩ : syracuseStep 1546483 = 2319725) B2319725
theorem B1546499 : Blo 1545470 1546499 := bstep (se 1 (by rfl) ⟨1159874, by rfl⟩ : syracuseStep 1546499 = 2319749) B2319749
theorem B1546515 : Blo 1545470 1546515 := bstep (se 1 (by rfl) ⟨1159886, by rfl⟩ : syracuseStep 1546515 = 2319773) B2319773
theorem B9902371 : Blo 1545470 9902371 := bstep (se 1 (by rfl) ⟨7426778, by rfl⟩ : syracuseStep 9902371 = 14853557) B14853557
theorem B1546531 : Blo 1545470 1546531 := bstep (se 1 (by rfl) ⟨1159898, by rfl⟩ : syracuseStep 1546531 = 2319797) B2319797
theorem B5216561 : Blo 1545470 5216561 := bstep (se 2 (by rfl) ⟨1956210, by rfl⟩ : syracuseStep 5216561 = 3912421) B3912421
theorem B1546547 : Blo 1545470 1546547 := bstep (se 1 (by rfl) ⟨1159910, by rfl⟩ : syracuseStep 1546547 = 2319821) B2319821
theorem B4405553 : Blo 1545470 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1546563 : Blo 1545470 1546563 := bstep (se 1 (by rfl) ⟨1159922, by rfl⟩ : syracuseStep 1546563 = 2319845) B2319845
theorem B1546579 : Blo 1545470 1546579 := bstep (se 1 (by rfl) ⟨1159934, by rfl⟩ : syracuseStep 1546579 = 2319869) B2319869
theorem B1546595 : Blo 1545470 1546595 := bstep (se 1 (by rfl) ⟨1159946, by rfl⟩ : syracuseStep 1546595 = 2319893) B2319893
theorem B6609251 : Blo 1545470 6609251 := bstep (se 1 (by rfl) ⟨4956938, by rfl⟩ : syracuseStep 6609251 = 9913877) B9913877
theorem B3479921 : Blo 1545470 3479921 := bstep (se 2 (by rfl) ⟨1304970, by rfl⟩ : syracuseStep 3479921 = 2609941) B2609941
theorem B1546611 : Blo 1545470 1546611 := bstep (se 1 (by rfl) ⟨1159958, by rfl⟩ : syracuseStep 1546611 = 2319917) B2319917
theorem B1546627 : Blo 1545470 1546627 := bstep (se 1 (by rfl) ⟨1159970, by rfl⟩ : syracuseStep 1546627 = 2319941) B2319941
theorem B3479939 : Blo 1545470 3479939 := bstep (se 1 (by rfl) ⟨2609954, by rfl⟩ : syracuseStep 3479939 = 5219909) B5219909
theorem B1546643 : Blo 1545470 1546643 := bstep (se 1 (by rfl) ⟨1159982, by rfl⟩ : syracuseStep 1546643 = 2319965) B2319965
theorem B8804771 : Blo 1545470 8804771 := bstep (se 1 (by rfl) ⟨6603578, by rfl⟩ : syracuseStep 8804771 = 13207157) B13207157
theorem B1546659 : Blo 1545470 1546659 := bstep (se 1 (by rfl) ⟨1159994, by rfl⟩ : syracuseStep 1546659 = 2319989) B2319989
theorem B1546675 : Blo 1545470 1546675 := bstep (se 1 (by rfl) ⟨1160006, by rfl⟩ : syracuseStep 1546675 = 2320013) B2320013
theorem B1546691 : Blo 1545470 1546691 := bstep (se 1 (by rfl) ⟨1160018, by rfl⟩ : syracuseStep 1546691 = 2320037) B2320037
theorem B1956307 : Blo 1545470 1956307 := bstep (se 1 (by rfl) ⟨1467230, by rfl⟩ : syracuseStep 1956307 = 2934461) B2934461
theorem B1546707 : Blo 1545470 1546707 := bstep (se 1 (by rfl) ⟨1160030, by rfl⟩ : syracuseStep 1546707 = 2320061) B2320061
theorem B1546723 : Blo 1545470 1546723 := bstep (se 1 (by rfl) ⟨1160042, by rfl⟩ : syracuseStep 1546723 = 2320085) B2320085
theorem B1546739 : Blo 1545470 1546739 := bstep (se 1 (by rfl) ⟨1160054, by rfl⟩ : syracuseStep 1546739 = 2320109) B2320109
theorem B1546755 : Blo 1545470 1546755 := bstep (se 1 (by rfl) ⟨1160066, by rfl⟩ : syracuseStep 1546755 = 2320133) B2320133
theorem B1546771 : Blo 1545470 1546771 := bstep (se 1 (by rfl) ⟨1160078, by rfl⟩ : syracuseStep 1546771 = 2320157) B2320157
theorem B1546787 : Blo 1545470 1546787 := bstep (se 1 (by rfl) ⟨1160090, by rfl⟩ : syracuseStep 1546787 = 2320181) B2320181
theorem B1956403 : Blo 1545470 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1546803 : Blo 1545470 1546803 := bstep (se 1 (by rfl) ⟨1160102, by rfl⟩ : syracuseStep 1546803 = 2320205) B2320205
theorem B1546819 : Blo 1545470 1546819 := bstep (se 1 (by rfl) ⟨1160114, by rfl⟩ : syracuseStep 1546819 = 2320229) B2320229
theorem B1546835 : Blo 1545470 1546835 := bstep (se 1 (by rfl) ⟨1160126, by rfl⟩ : syracuseStep 1546835 = 2320253) B2320253
theorem B1546851 : Blo 1545470 1546851 := bstep (se 1 (by rfl) ⟨1160138, by rfl⟩ : syracuseStep 1546851 = 2320277) B2320277
theorem B25066097 : Blo 1545470 25066097 := bstep (se 2 (by rfl) ⟨9399786, by rfl⟩ : syracuseStep 25066097 = 18799573) B18799573
theorem B1546867 : Blo 1545470 1546867 := bstep (se 1 (by rfl) ⟨1160150, by rfl⟩ : syracuseStep 1546867 = 2320301) B2320301
theorem B2202241 : Blo 1545470 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B1546883 : Blo 1545470 1546883 := bstep (se 1 (by rfl) ⟨1160162, by rfl⟩ : syracuseStep 1546883 = 2320325) B2320325
theorem B3480209 : Blo 1545470 3480209 := bstep (se 2 (by rfl) ⟨1305078, by rfl⟩ : syracuseStep 3480209 = 2610157) B2610157
theorem B1546899 : Blo 1545470 1546899 := bstep (se 1 (by rfl) ⟨1160174, by rfl⟩ : syracuseStep 1546899 = 2320349) B2320349
theorem B2202275 : Blo 1545470 2202275 := bstep (se 1 (by rfl) ⟨1651706, by rfl⟩ : syracuseStep 2202275 = 3303413) B3303413
theorem B3480227 : Blo 1545470 3480227 := bstep (se 1 (by rfl) ⟨2610170, by rfl⟩ : syracuseStep 3480227 = 5220341) B5220341
theorem B1546915 : Blo 1545470 1546915 := bstep (se 1 (by rfl) ⟨1160186, by rfl⟩ : syracuseStep 1546915 = 2320373) B2320373
theorem B1546931 : Blo 1545470 1546931 := bstep (se 1 (by rfl) ⟨1160198, by rfl⟩ : syracuseStep 1546931 = 2320397) B2320397
theorem B1546947 : Blo 1545470 1546947 := bstep (se 1 (by rfl) ⟨1160210, by rfl⟩ : syracuseStep 1546947 = 2320421) B2320421
theorem B1546963 : Blo 1545470 1546963 := bstep (se 1 (by rfl) ⟨1160222, by rfl⟩ : syracuseStep 1546963 = 2320445) B2320445
theorem B8043235 : Blo 1545470 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B1546979 : Blo 1545470 1546979 := bstep (se 1 (by rfl) ⟨1160234, by rfl⟩ : syracuseStep 1546979 = 2320469) B2320469
theorem B1546995 : Blo 1545470 1546995 := bstep (se 1 (by rfl) ⟨1160246, by rfl⟩ : syracuseStep 1546995 = 2320493) B2320493
theorem B1547011 : Blo 1545470 1547011 := bstep (se 1 (by rfl) ⟨1160258, by rfl⟩ : syracuseStep 1547011 = 2320517) B2320517
theorem B1547027 : Blo 1545470 1547027 := bstep (se 1 (by rfl) ⟨1160270, by rfl⟩ : syracuseStep 1547027 = 2320541) B2320541
theorem B1547043 : Blo 1545470 1547043 := bstep (se 1 (by rfl) ⟨1160282, by rfl⟩ : syracuseStep 1547043 = 2320565) B2320565
theorem B1547059 : Blo 1545470 1547059 := bstep (se 1 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 1547059 = 2320589) B2320589
theorem B1547075 : Blo 1545470 1547075 := bstep (se 1 (by rfl) ⟨1160306, by rfl⟩ : syracuseStep 1547075 = 2320613) B2320613
theorem B5217101 : Blo 1545470 5217101 := bstep (se 3 (by rfl) ⟨978206, by rfl⟩ : syracuseStep 5217101 = 1956413) B1956413
theorem B1547091 : Blo 1545470 1547091 := bstep (se 1 (by rfl) ⟨1160318, by rfl⟩ : syracuseStep 1547091 = 2320637) B2320637
theorem B1547107 : Blo 1545470 1547107 := bstep (se 1 (by rfl) ⟨1160330, by rfl⟩ : syracuseStep 1547107 = 2320661) B2320661
theorem B4701037 : Blo 1545470 4701037 := bstep (se 3 (by rfl) ⟨881444, by rfl⟩ : syracuseStep 4701037 = 1762889) B1762889
theorem B22297457 : Blo 1545470 22297457 := bstep (se 2 (by rfl) ⟨8361546, by rfl⟩ : syracuseStep 22297457 = 16723093) B16723093
theorem B1547123 : Blo 1545470 1547123 := bstep (se 1 (by rfl) ⟨1160342, by rfl⟩ : syracuseStep 1547123 = 2320685) B2320685
theorem B5217155 : Blo 1545470 5217155 := bstep (se 1 (by rfl) ⟨3912866, by rfl⟩ : syracuseStep 5217155 = 7825733) B7825733
theorem B1547139 : Blo 1545470 1547139 := bstep (se 1 (by rfl) ⟨1160354, by rfl⟩ : syracuseStep 1547139 = 2320709) B2320709
theorem B13212557 : Blo 1545470 13212557 := bstep (se 3 (by rfl) ⟨2477354, by rfl⟩ : syracuseStep 13212557 = 4954709) B4954709
theorem B1547155 : Blo 1545470 1547155 := bstep (se 1 (by rfl) ⟨1160366, by rfl⟩ : syracuseStep 1547155 = 2320733) B2320733
theorem B1547171 : Blo 1545470 1547171 := bstep (se 1 (by rfl) ⟨1160378, by rfl⟩ : syracuseStep 1547171 = 2320757) B2320757
theorem B3480497 : Blo 1545470 3480497 := bstep (se 2 (by rfl) ⟨1305186, by rfl⟩ : syracuseStep 3480497 = 2610373) B2610373
theorem B1547187 : Blo 1545470 1547187 := bstep (se 1 (by rfl) ⟨1160390, by rfl⟩ : syracuseStep 1547187 = 2320781) B2320781
theorem B3480515 : Blo 1545470 3480515 := bstep (se 1 (by rfl) ⟨2610386, by rfl⟩ : syracuseStep 3480515 = 5220773) B5220773
theorem B1547203 : Blo 1545470 1547203 := bstep (se 1 (by rfl) ⟨1160402, by rfl⟩ : syracuseStep 1547203 = 2320805) B2320805
theorem B81476549 : Blo 1545470 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1547219 : Blo 1545470 1547219 := bstep (se 1 (by rfl) ⟨1160414, by rfl⟩ : syracuseStep 1547219 = 2320829) B2320829
theorem B1547235 : Blo 1545470 1547235 := bstep (se 1 (by rfl) ⟨1160426, by rfl⟩ : syracuseStep 1547235 = 2320853) B2320853
theorem B1547251 : Blo 1545470 1547251 := bstep (se 1 (by rfl) ⟨1160438, by rfl⟩ : syracuseStep 1547251 = 2320877) B2320877
theorem B3349507 : Blo 1545470 3349507 := bstep (se 1 (by rfl) ⟨2512130, by rfl⟩ : syracuseStep 3349507 = 5024261) B5024261
theorem B1547267 : Blo 1545470 1547267 := bstep (se 1 (by rfl) ⟨1160450, by rfl⟩ : syracuseStep 1547267 = 2320901) B2320901
theorem B1547283 : Blo 1545470 1547283 := bstep (se 1 (by rfl) ⟨1160462, by rfl⟩ : syracuseStep 1547283 = 2320925) B2320925
theorem B1956899 : Blo 1545470 1956899 := bstep (se 1 (by rfl) ⟨1467674, by rfl⟩ : syracuseStep 1956899 = 2935349) B2935349
theorem B1547299 : Blo 1545470 1547299 := bstep (se 1 (by rfl) ⟨1160474, by rfl⟩ : syracuseStep 1547299 = 2320949) B2320949
theorem B4701229 : Blo 1545470 4701229 := bstep (se 3 (by rfl) ⟨881480, by rfl⟩ : syracuseStep 4701229 = 1762961) B1762961
theorem B3914801 : Blo 1545470 3914801 := bstep (se 2 (by rfl) ⟨1468050, by rfl⟩ : syracuseStep 3914801 = 2936101) B2936101
theorem B1547315 : Blo 1545470 1547315 := bstep (se 1 (by rfl) ⟨1160486, by rfl⟩ : syracuseStep 1547315 = 2320973) B2320973
theorem B1547331 : Blo 1545470 1547331 := bstep (se 1 (by rfl) ⟨1160498, by rfl⟩ : syracuseStep 1547331 = 2320997) B2320997
theorem B4406339 : Blo 1545470 4406339 := bstep (se 1 (by rfl) ⟨3304754, by rfl⟩ : syracuseStep 4406339 = 6609509) B6609509
theorem B1547347 : Blo 1545470 1547347 := bstep (se 1 (by rfl) ⟨1160510, by rfl⟩ : syracuseStep 1547347 = 2321021) B2321021
theorem B3914851 : Blo 1545470 3914851 := bstep (se 1 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 3914851 = 5872277) B5872277
theorem B1547363 : Blo 1545470 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B1547379 : Blo 1545470 1547379 := bstep (se 1 (by rfl) ⟨1160534, by rfl⟩ : syracuseStep 1547379 = 2321069) B2321069
theorem B3439747 : Blo 1545470 3439747 := bstep (se 1 (by rfl) ⟨2579810, by rfl⟩ : syracuseStep 3439747 = 5159621) B5159621
theorem B1547395 : Blo 1545470 1547395 := bstep (se 1 (by rfl) ⟨1160546, by rfl⟩ : syracuseStep 1547395 = 2321093) B2321093
theorem B5217425 : Blo 1545470 5217425 := bstep (se 2 (by rfl) ⟨1956534, by rfl⟩ : syracuseStep 5217425 = 3913069) B3913069
theorem B1547411 : Blo 1545470 1547411 := bstep (se 1 (by rfl) ⟨1160558, by rfl⟩ : syracuseStep 1547411 = 2321117) B2321117
theorem B1547427 : Blo 1545470 1547427 := bstep (se 1 (by rfl) ⟨1160570, by rfl⟩ : syracuseStep 1547427 = 2321141) B2321141
theorem B1547443 : Blo 1545470 1547443 := bstep (se 1 (by rfl) ⟨1160582, by rfl⟩ : syracuseStep 1547443 = 2321165) B2321165
theorem B1547459 : Blo 1545470 1547459 := bstep (se 1 (by rfl) ⟨1160594, by rfl⟩ : syracuseStep 1547459 = 2321189) B2321189
theorem B3480785 : Blo 1545470 3480785 := bstep (se 2 (by rfl) ⟨1305294, by rfl⟩ : syracuseStep 3480785 = 2610589) B2610589
theorem B2202833 : Blo 1545470 2202833 := bstep (se 2 (by rfl) ⟨826062, by rfl⟩ : syracuseStep 2202833 = 1652125) B1652125
theorem B26410211 : Blo 1545470 26410211 := bstep (se 1 (by rfl) ⟨19807658, by rfl⟩ : syracuseStep 26410211 = 39615317) B39615317
theorem B7830755 : Blo 1545470 7830755 := bstep (se 1 (by rfl) ⟨5873066, by rfl⟩ : syracuseStep 7830755 = 11746133) B11746133
theorem B3480803 : Blo 1545470 3480803 := bstep (se 1 (by rfl) ⟨2610602, by rfl⟩ : syracuseStep 3480803 = 5221205) B5221205
theorem B3914993 : Blo 1545470 3914993 := bstep (se 2 (by rfl) ⟨1468122, by rfl⟩ : syracuseStep 3914993 = 2936245) B2936245
theorem B2202913 : Blo 1545470 2202913 := bstep (se 2 (by rfl) ⟨826092, by rfl⟩ : syracuseStep 2202913 = 1652185) B1652185
theorem B5872931 : Blo 1545470 5872931 := bstep (se 1 (by rfl) ⟨4404698, by rfl⟩ : syracuseStep 5872931 = 8809397) B8809397
theorem B2350385 : Blo 1545470 2350385 := bstep (se 2 (by rfl) ⟨881394, by rfl⟩ : syracuseStep 2350385 = 1762789) B1762789
theorem B5872945 : Blo 1545470 5872945 := bstep (se 2 (by rfl) ⟨2202354, by rfl⟩ : syracuseStep 5872945 = 4404709) B4404709
theorem B9911621 : Blo 1545470 9911621 := bstep (se 4 (by rfl) ⟨929214, by rfl⟩ : syracuseStep 9911621 = 1858429) B1858429
theorem B8805773 : Blo 1545470 8805773 := bstep (se 3 (by rfl) ⟨1651082, by rfl⟩ : syracuseStep 8805773 = 3302165) B3302165
theorem B4955555 : Blo 1545470 4955555 := bstep (se 1 (by rfl) ⟨3716666, by rfl⟩ : syracuseStep 4955555 = 7433333) B7433333
theorem B3481073 : Blo 1545470 3481073 := bstep (se 2 (by rfl) ⟨1305402, by rfl⟩ : syracuseStep 3481073 = 2610805) B2610805
theorem B3481091 : Blo 1545470 3481091 := bstep (se 1 (by rfl) ⟨2610818, by rfl⟩ : syracuseStep 3481091 = 5221637) B5221637
theorem B4234769 : Blo 1545470 4234769 := bstep (se 2 (by rfl) ⟨1588038, by rfl⟩ : syracuseStep 4234769 = 3176077) B3176077
theorem B5217965 : Blo 1545470 5217965 := bstep (se 3 (by rfl) ⟨978368, by rfl⟩ : syracuseStep 5217965 = 1956737) B1956737
theorem B6602417 : Blo 1545470 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B2449073 : Blo 1545470 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B5218019 : Blo 1545470 5218019 := bstep (se 1 (by rfl) ⟨3913514, by rfl⟩ : syracuseStep 5218019 = 7827029) B7827029
theorem B1957603 : Blo 1545470 1957603 := bstep (se 1 (by rfl) ⟨1468202, by rfl⟩ : syracuseStep 1957603 = 2936405) B2936405
theorem B3481361 : Blo 1545470 3481361 := bstep (se 2 (by rfl) ⟨1305510, by rfl⟩ : syracuseStep 3481361 = 2611021) B2611021
theorem B3481379 : Blo 1545470 3481379 := bstep (se 1 (by rfl) ⟨2611034, by rfl⟩ : syracuseStep 3481379 = 5222069) B5222069
theorem B1957699 : Blo 1545470 1957699 := bstep (se 1 (by rfl) ⟨1468274, by rfl⟩ : syracuseStep 1957699 = 2936549) B2936549
theorem B2318225 : Blo 1545470 2318225 := bstep (se 2 (by rfl) ⟨869334, by rfl⟩ : syracuseStep 2318225 = 1738669) B1738669
theorem B2318243 : Blo 1545470 2318243 := bstep (se 1 (by rfl) ⟨1738682, by rfl⟩ : syracuseStep 2318243 = 3477365) B3477365
theorem B2318273 : Blo 1545470 2318273 := bstep (se 2 (by rfl) ⟨869352, by rfl⟩ : syracuseStep 2318273 = 1738705) B1738705
theorem B4702157 : Blo 1545470 4702157 := bstep (se 3 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 4702157 = 1763309) B1763309
theorem B2318291 : Blo 1545470 2318291 := bstep (se 1 (by rfl) ⟨1738718, by rfl⟩ : syracuseStep 2318291 = 3477437) B3477437
theorem B2318321 : Blo 1545470 2318321 := bstep (se 2 (by rfl) ⟨869370, by rfl⟩ : syracuseStep 2318321 = 1738741) B1738741
theorem B5218289 : Blo 1545470 5218289 := bstep (se 2 (by rfl) ⟨1956858, by rfl⟩ : syracuseStep 5218289 = 3913717) B3913717
theorem B5955569 : Blo 1545470 5955569 := bstep (se 2 (by rfl) ⟨2233338, by rfl⟩ : syracuseStep 5955569 = 4466677) B4466677
theorem B2318411 : Blo 1545470 2318411 := bstep (se 1 (by rfl) ⟨1738808, by rfl⟩ : syracuseStep 2318411 = 3477617) B3477617
theorem B4464715 : Blo 1545470 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B2318423 : Blo 1545470 2318423 := bstep (se 1 (by rfl) ⟨1738817, by rfl⟩ : syracuseStep 2318423 = 3477635) B3477635
theorem B2785367 : Blo 1545470 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B5218397 : Blo 1545470 5218397 := bstep (se 3 (by rfl) ⟨978449, by rfl⟩ : syracuseStep 5218397 = 1956899) B1956899
theorem B3481739 : Blo 1545470 3481739 := bstep (se 1 (by rfl) ⟨2611304, by rfl⟩ : syracuseStep 3481739 = 5222609) B5222609
theorem B2318489 : Blo 1545470 2318489 := bstep (se 2 (by rfl) ⟨869433, by rfl⟩ : syracuseStep 2318489 = 1738867) B1738867
theorem B3481793 : Blo 1545470 3481793 := bstep (se 2 (by rfl) ⟨1305672, by rfl⟩ : syracuseStep 3481793 = 2611345) B2611345
theorem B2318603 : Blo 1545470 2318603 := bstep (se 1 (by rfl) ⟨1738952, by rfl⟩ : syracuseStep 2318603 = 3477905) B3477905
theorem B2318615 : Blo 1545470 2318615 := bstep (se 1 (by rfl) ⟨1738961, by rfl⟩ : syracuseStep 2318615 = 3477923) B3477923
theorem B3916097 : Blo 1545470 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B2318681 : Blo 1545470 2318681 := bstep (se 2 (by rfl) ⟨869505, by rfl⟩ : syracuseStep 2318681 = 1739011) B1739011
theorem B2318795 : Blo 1545470 2318795 := bstep (se 1 (by rfl) ⟨1739096, by rfl⟩ : syracuseStep 2318795 = 3478193) B3478193
theorem B1958347 : Blo 1545470 1958347 := bstep (se 1 (by rfl) ⟨1468760, by rfl⟩ : syracuseStep 1958347 = 2937521) B2937521
theorem B2318807 : Blo 1545470 2318807 := bstep (se 1 (by rfl) ⟨1739105, by rfl⟩ : syracuseStep 2318807 = 3478211) B3478211
theorem B2318873 : Blo 1545470 2318873 := bstep (se 2 (by rfl) ⟨869577, by rfl⟩ : syracuseStep 2318873 = 1739155) B1739155
theorem B5874221 : Blo 1545470 5874221 := bstep (se 3 (by rfl) ⟨1101416, by rfl⟩ : syracuseStep 5874221 = 2202833) B2202833
theorem B2318987 : Blo 1545470 2318987 := bstep (se 1 (by rfl) ⟨1739240, by rfl⟩ : syracuseStep 2318987 = 3478481) B3478481
theorem B2318999 : Blo 1545470 2318999 := bstep (se 1 (by rfl) ⟨1739249, by rfl⟩ : syracuseStep 2318999 = 3478499) B3478499
theorem B4178611 : Blo 1545470 4178611 := bstep (se 1 (by rfl) ⟨3133958, by rfl⟩ : syracuseStep 4178611 = 6267917) B6267917
theorem B6603443 : Blo 1545470 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B2319065 : Blo 1545470 2319065 := bstep (se 2 (by rfl) ⟨869649, by rfl⟩ : syracuseStep 2319065 = 1739299) B1739299
theorem B2089739 : Blo 1545470 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B2319179 : Blo 1545470 2319179 := bstep (se 1 (by rfl) ⟨1739384, by rfl⟩ : syracuseStep 2319179 = 3478769) B3478769
theorem B2319191 : Blo 1545470 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B3916633 : Blo 1545470 3916633 := bstep (se 2 (by rfl) ⟨1468737, by rfl⟩ : syracuseStep 3916633 = 2937475) B2937475
theorem B2319257 : Blo 1545470 2319257 := bstep (se 2 (by rfl) ⟨869721, by rfl⟩ : syracuseStep 2319257 = 1739443) B1739443
theorem B8479667 : Blo 1545470 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B7832537 : Blo 1545470 7832537 := bstep (se 2 (by rfl) ⟨2937201, by rfl⟩ : syracuseStep 7832537 = 5874403) B5874403
theorem B81495001 : Blo 1545470 81495001 := bstep (se 2 (by rfl) ⟨30560625, by rfl⟩ : syracuseStep 81495001 = 61121251) B61121251
theorem B2319371 : Blo 1545470 2319371 := bstep (se 1 (by rfl) ⟨1739528, by rfl⟩ : syracuseStep 2319371 = 3479057) B3479057
theorem B2319383 : Blo 1545470 2319383 := bstep (se 1 (by rfl) ⟨1739537, by rfl⟩ : syracuseStep 2319383 = 3479075) B3479075
theorem B2090009 : Blo 1545470 2090009 := bstep (se 2 (by rfl) ⟨783753, by rfl⟩ : syracuseStep 2090009 = 1567507) B1567507
theorem B2319449 : Blo 1545470 2319449 := bstep (se 2 (by rfl) ⟨869793, by rfl⟩ : syracuseStep 2319449 = 1739587) B1739587
theorem B6268049 : Blo 1545470 6268049 := bstep (se 2 (by rfl) ⟨2350518, by rfl⟩ : syracuseStep 6268049 = 4701037) B4701037
theorem B2319563 : Blo 1545470 2319563 := bstep (se 1 (by rfl) ⟨1739672, by rfl⟩ : syracuseStep 2319563 = 3479345) B3479345
theorem B5219531 : Blo 1545470 5219531 := bstep (se 1 (by rfl) ⟨3914648, by rfl⟩ : syracuseStep 5219531 = 7829297) B7829297
theorem B2352331 : Blo 1545470 2352331 := bstep (se 1 (by rfl) ⟨1764248, by rfl⟩ : syracuseStep 2352331 = 3528497) B3528497
theorem B2319575 : Blo 1545470 2319575 := bstep (se 1 (by rfl) ⟨1739681, by rfl⟩ : syracuseStep 2319575 = 3479363) B3479363
theorem B2319641 : Blo 1545470 2319641 := bstep (se 2 (by rfl) ⟨869865, by rfl⟩ : syracuseStep 2319641 = 1739731) B1739731
theorem B6268211 : Blo 1545470 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B4466009 : Blo 1545470 4466009 := bstep (se 2 (by rfl) ⟨1674753, by rfl⟩ : syracuseStep 4466009 = 3349507) B3349507
theorem B11150693 : Blo 1545470 11150693 := bstep (se 4 (by rfl) ⟨1045377, by rfl⟩ : syracuseStep 11150693 = 2090755) B2090755
theorem B2319755 : Blo 1545470 2319755 := bstep (se 1 (by rfl) ⟨1739816, by rfl⟩ : syracuseStep 2319755 = 3479633) B3479633
theorem B2319767 : Blo 1545470 2319767 := bstep (se 1 (by rfl) ⟨1739825, by rfl⟩ : syracuseStep 2319767 = 3479651) B3479651
theorem B3302849 : Blo 1545470 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B2319833 : Blo 1545470 2319833 := bstep (se 2 (by rfl) ⟨869937, by rfl⟩ : syracuseStep 2319833 = 1739875) B1739875
theorem B5219801 : Blo 1545470 5219801 := bstep (se 2 (by rfl) ⟨1957425, by rfl⟩ : syracuseStep 5219801 = 3914851) B3914851
theorem B59442659 : Blo 1545470 59442659 := bstep (se 1 (by rfl) ⟨44581994, by rfl⟩ : syracuseStep 59442659 = 89163989) B89163989
theorem B11142731 : Blo 1545470 11142731 := bstep (se 1 (by rfl) ⟨8357048, by rfl⟩ : syracuseStep 11142731 = 16714097) B16714097
theorem B2319947 : Blo 1545470 2319947 := bstep (se 1 (by rfl) ⟨1739960, by rfl⟩ : syracuseStep 2319947 = 3479921) B3479921
theorem B2319959 : Blo 1545470 2319959 := bstep (se 1 (by rfl) ⟨1739969, by rfl⟩ : syracuseStep 2319959 = 3479939) B3479939
theorem B2320025 : Blo 1545470 2320025 := bstep (se 2 (by rfl) ⟨870009, by rfl⟩ : syracuseStep 2320025 = 1740019) B1740019
theorem B5572289 : Blo 1545470 5572289 := bstep (se 2 (by rfl) ⟨2089608, by rfl⟩ : syracuseStep 5572289 = 4179217) B4179217
theorem B2320139 : Blo 1545470 2320139 := bstep (se 1 (by rfl) ⟨1740104, by rfl⟩ : syracuseStep 2320139 = 3480209) B3480209
theorem B2320151 : Blo 1545470 2320151 := bstep (se 1 (by rfl) ⟨1740113, by rfl⟩ : syracuseStep 2320151 = 3480227) B3480227
theorem B6530861 : Blo 1545470 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B2320217 : Blo 1545470 2320217 := bstep (se 2 (by rfl) ⟨870081, by rfl⟩ : syracuseStep 2320217 = 1740163) B1740163
theorem B2934643 : Blo 1545470 2934643 := bstep (se 1 (by rfl) ⟨2200982, by rfl⟩ : syracuseStep 2934643 = 4401965) B4401965
theorem B8808371 : Blo 1545470 8808371 := bstep (se 1 (by rfl) ⟨6606278, by rfl⟩ : syracuseStep 8808371 = 13212557) B13212557
theorem B2320331 : Blo 1545470 2320331 := bstep (se 1 (by rfl) ⟨1740248, by rfl⟩ : syracuseStep 2320331 = 3480497) B3480497
theorem B2320343 : Blo 1545470 2320343 := bstep (se 1 (by rfl) ⟨1740257, by rfl⟩ : syracuseStep 2320343 = 3480515) B3480515
theorem B2320409 : Blo 1545470 2320409 := bstep (se 2 (by rfl) ⟨870153, by rfl⟩ : syracuseStep 2320409 = 1740307) B1740307
theorem B1738795 : Blo 1545470 1738795 := bstep (se 1 (by rfl) ⟨1304096, by rfl⟩ : syracuseStep 1738795 = 2608193) B2608193
theorem B9406529 : Blo 1545470 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B5572739 : Blo 1545470 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B2320523 : Blo 1545470 2320523 := bstep (se 1 (by rfl) ⟨1740392, by rfl⟩ : syracuseStep 2320523 = 3480785) B3480785
theorem B1738903 : Blo 1545470 1738903 := bstep (se 1 (by rfl) ⟨1304177, by rfl⟩ : syracuseStep 1738903 = 2608355) B2608355
theorem B17606807 : Blo 1545470 17606807 := bstep (se 1 (by rfl) ⟨13205105, by rfl⟩ : syracuseStep 17606807 = 26410211) B26410211
theorem B5220503 : Blo 1545470 5220503 := bstep (se 1 (by rfl) ⟨3915377, by rfl⟩ : syracuseStep 5220503 = 7830755) B7830755
theorem B2320535 : Blo 1545470 2320535 := bstep (se 1 (by rfl) ⟨1740401, by rfl⟩ : syracuseStep 2320535 = 3480803) B3480803
theorem B1566923 : Blo 1545470 1566923 := bstep (se 1 (by rfl) ⟨1175192, by rfl⟩ : syracuseStep 1566923 = 2350385) B2350385
theorem B2320601 : Blo 1545470 2320601 := bstep (se 2 (by rfl) ⟨870225, by rfl⟩ : syracuseStep 2320601 = 1740451) B1740451
theorem B3303703 : Blo 1545470 3303703 := bstep (se 1 (by rfl) ⟨2477777, by rfl⟩ : syracuseStep 3303703 = 4955555) B4955555
theorem B2935091 : Blo 1545470 2935091 := bstep (se 1 (by rfl) ⟨2201318, by rfl⟩ : syracuseStep 2935091 = 4402637) B4402637
theorem B1739083 : Blo 1545470 1739083 := bstep (se 1 (by rfl) ⟨1304312, by rfl⟩ : syracuseStep 1739083 = 2608625) B2608625
theorem B2320715 : Blo 1545470 2320715 := bstep (se 1 (by rfl) ⟨1740536, by rfl⟩ : syracuseStep 2320715 = 3481073) B3481073
theorem B2320727 : Blo 1545470 2320727 := bstep (se 1 (by rfl) ⟨1740545, by rfl⟩ : syracuseStep 2320727 = 3481091) B3481091
theorem B2935129 : Blo 1545470 2935129 := bstep (se 2 (by rfl) ⟨1100673, by rfl⟩ : syracuseStep 2935129 = 2201347) B2201347
theorem B2320793 : Blo 1545470 2320793 := bstep (se 2 (by rfl) ⟨870297, by rfl⟩ : syracuseStep 2320793 = 1740595) B1740595
theorem B1739191 : Blo 1545470 1739191 := bstep (se 1 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 1739191 = 2608787) B2608787
theorem B4401611 : Blo 1545470 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B9406937 : Blo 1545470 9406937 := bstep (se 2 (by rfl) ⟨3527601, by rfl⟩ : syracuseStep 9406937 = 7055203) B7055203
theorem B4704733 : Blo 1545470 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B2320907 : Blo 1545470 2320907 := bstep (se 1 (by rfl) ⟨1740680, by rfl⟩ : syracuseStep 2320907 = 3481361) B3481361
theorem B2320919 : Blo 1545470 2320919 := bstep (se 1 (by rfl) ⟨1740689, by rfl⟩ : syracuseStep 2320919 = 3481379) B3481379
theorem B2320985 : Blo 1545470 2320985 := bstep (se 2 (by rfl) ⟨870369, by rfl⟩ : syracuseStep 2320985 = 1740739) B1740739
theorem B1739371 : Blo 1545470 1739371 := bstep (se 1 (by rfl) ⟨1304528, by rfl⟩ : syracuseStep 1739371 = 2609057) B2609057
theorem B5221043 : Blo 1545470 5221043 := bstep (se 1 (by rfl) ⟨3915782, by rfl⟩ : syracuseStep 5221043 = 7831565) B7831565
theorem B2321099 : Blo 1545470 2321099 := bstep (se 1 (by rfl) ⟨1740824, by rfl⟩ : syracuseStep 2321099 = 3481649) B3481649
theorem B1739479 : Blo 1545470 1739479 := bstep (se 1 (by rfl) ⟨1304609, by rfl⟩ : syracuseStep 1739479 = 2609219) B2609219
theorem B2321111 : Blo 1545470 2321111 := bstep (se 1 (by rfl) ⟨1740833, by rfl⟩ : syracuseStep 2321111 = 3481667) B3481667
theorem B2476823 : Blo 1545470 2476823 := bstep (se 1 (by rfl) ⟨1857617, by rfl⟩ : syracuseStep 2476823 = 3715235) B3715235
theorem B6269719 : Blo 1545470 6269719 := bstep (se 1 (by rfl) ⟨4702289, by rfl⟩ : syracuseStep 6269719 = 9404579) B9404579
theorem B2935577 : Blo 1545470 2935577 := bstep (se 2 (by rfl) ⟨1100841, by rfl⟩ : syracuseStep 2935577 = 2201683) B2201683
theorem B2321177 : Blo 1545470 2321177 := bstep (se 2 (by rfl) ⟨870441, by rfl⟩ : syracuseStep 2321177 = 1740883) B1740883
theorem B1739659 : Blo 1545470 1739659 := bstep (se 1 (by rfl) ⟨1304744, by rfl⟩ : syracuseStep 1739659 = 2609489) B2609489
theorem B5221313 : Blo 1545470 5221313 := bstep (se 2 (by rfl) ⟨1957992, by rfl⟩ : syracuseStep 5221313 = 3915985) B3915985
theorem B53537753 : Blo 1545470 53537753 := bstep (se 2 (by rfl) ⟨20076657, by rfl⟩ : syracuseStep 53537753 = 40153315) B40153315
theorem B1739767 : Blo 1545470 1739767 := bstep (se 1 (by rfl) ⟨1304825, by rfl⟩ : syracuseStep 1739767 = 2609651) B2609651
theorem B2608139 : Blo 1545470 2608139 := bstep (se 1 (by rfl) ⟨1956104, by rfl⟩ : syracuseStep 2608139 = 3912209) B3912209
theorem B7056407 : Blo 1545470 7056407 := bstep (se 1 (by rfl) ⟨5292305, by rfl⟩ : syracuseStep 7056407 = 10584611) B10584611
theorem B3304523 : Blo 1545470 3304523 := bstep (se 1 (by rfl) ⟨2478392, by rfl⟩ : syracuseStep 3304523 = 4956785) B4956785
theorem B7056515 : Blo 1545470 7056515 := bstep (se 1 (by rfl) ⟨5292386, by rfl⟩ : syracuseStep 7056515 = 10584773) B10584773
theorem B2608267 : Blo 1545470 2608267 := bstep (se 1 (by rfl) ⟨1956200, by rfl⟩ : syracuseStep 2608267 = 3912401) B3912401
theorem B13388951 : Blo 1545470 13388951 := bstep (se 1 (by rfl) ⟨10041713, by rfl⟩ : syracuseStep 13388951 = 20083427) B20083427
theorem B1739947 : Blo 1545470 1739947 := bstep (se 1 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 1739947 = 2609921) B2609921
theorem B5287133 : Blo 1545470 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B7826705 : Blo 1545470 7826705 := bstep (se 2 (by rfl) ⟨2935014, by rfl⟩ : syracuseStep 7826705 = 5870029) B5870029
theorem B11144465 : Blo 1545470 11144465 := bstep (se 2 (by rfl) ⟨4179174, by rfl⟩ : syracuseStep 11144465 = 8358349) B8358349
theorem B1740055 : Blo 1545470 1740055 := bstep (se 1 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 1740055 = 2610083) B2610083
theorem B2608409 : Blo 1545470 2608409 := bstep (se 2 (by rfl) ⟨978153, by rfl⟩ : syracuseStep 2608409 = 1956307) B1956307
theorem B5868845 : Blo 1545470 5868845 := bstep (se 3 (by rfl) ⟨1100408, by rfl⟩ : syracuseStep 5868845 = 2200817) B2200817
theorem B5868875 : Blo 1545470 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B13208933 : Blo 1545470 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B8809829 : Blo 1545470 8809829 := bstep (se 4 (by rfl) ⟨825921, by rfl⟩ : syracuseStep 8809829 = 1651843) B1651843
theorem B7433603 : Blo 1545470 7433603 := bstep (se 1 (by rfl) ⟨5575202, by rfl⟩ : syracuseStep 7433603 = 11150405) B11150405
theorem B2608537 : Blo 1545470 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B7826867 : Blo 1545470 7826867 := bstep (se 1 (by rfl) ⟨5870150, by rfl⟩ : syracuseStep 7826867 = 11740301) B11740301
theorem B1740235 : Blo 1545470 1740235 := bstep (se 1 (by rfl) ⟨1305176, by rfl⟩ : syracuseStep 1740235 = 2610353) B2610353
theorem B5221853 : Blo 1545470 5221853 := bstep (se 3 (by rfl) ⟨979097, by rfl⟩ : syracuseStep 5221853 = 1958195) B1958195
theorem B2936321 : Blo 1545470 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B1740343 : Blo 1545470 1740343 := bstep (se 1 (by rfl) ⟨1305257, by rfl⟩ : syracuseStep 1740343 = 2610515) B2610515
theorem B1740523 : Blo 1545470 1740523 := bstep (se 1 (by rfl) ⟨1305392, by rfl⟩ : syracuseStep 1740523 = 2610785) B2610785
theorem B2936587 : Blo 1545470 2936587 := bstep (se 1 (by rfl) ⟨2202440, by rfl⟩ : syracuseStep 2936587 = 4404881) B4404881
theorem B1740631 : Blo 1545470 1740631 := bstep (se 1 (by rfl) ⟨1305473, by rfl⟩ : syracuseStep 1740631 = 2610947) B2610947
theorem B3477401 : Blo 1545470 3477401 := bstep (se 2 (by rfl) ⟨1304025, by rfl⟩ : syracuseStep 3477401 = 2608051) B2608051
theorem B19812275 : Blo 1545470 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B2609111 : Blo 1545470 2609111 := bstep (se 1 (by rfl) ⟨1956833, by rfl⟩ : syracuseStep 2609111 = 3913667) B3913667
theorem B5869529 : Blo 1545470 5869529 := bstep (se 2 (by rfl) ⟨2201073, by rfl⟩ : syracuseStep 5869529 = 4402147) B4402147
theorem B3477491 : Blo 1545470 3477491 := bstep (se 1 (by rfl) ⟨2608118, by rfl⟩ : syracuseStep 3477491 = 5216237) B5216237
theorem B1740811 : Blo 1545470 1740811 := bstep (se 1 (by rfl) ⟨1305608, by rfl⟩ : syracuseStep 1740811 = 2611217) B2611217
theorem B14856209 : Blo 1545470 14856209 := bstep (se 2 (by rfl) ⟨5571078, by rfl⟩ : syracuseStep 14856209 = 11142157) B11142157
theorem B3477527 : Blo 1545470 3477527 := bstep (se 1 (by rfl) ⟨2608145, by rfl⟩ : syracuseStep 3477527 = 5216291) B5216291
theorem B50147363 : Blo 1545470 50147363 := bstep (se 1 (by rfl) ⟨37610522, by rfl⟩ : syracuseStep 50147363 = 75221045) B75221045
theorem B11907107 : Blo 1545470 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B4403251 : Blo 1545470 4403251 := bstep (se 1 (by rfl) ⟨3302438, by rfl⟩ : syracuseStep 4403251 = 6604877) B6604877
theorem B2609239 : Blo 1545470 2609239 := bstep (se 1 (by rfl) ⟨1956929, by rfl⟩ : syracuseStep 2609239 = 3913859) B3913859
theorem B3477707 : Blo 1545470 3477707 := bstep (se 1 (by rfl) ⟨2608280, by rfl⟩ : syracuseStep 3477707 = 5216561) B5216561
theorem B2937035 : Blo 1545470 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B3477761 : Blo 1545470 3477761 := bstep (se 2 (by rfl) ⟨1304160, by rfl⟩ : syracuseStep 3477761 = 2608321) B2608321
theorem B5869847 : Blo 1545470 5869847 := bstep (se 1 (by rfl) ⟨4402385, by rfl⟩ : syracuseStep 5869847 = 8804771) B8804771
theorem B4403479 : Blo 1545470 4403479 := bstep (se 1 (by rfl) ⟨3302609, by rfl⟩ : syracuseStep 4403479 = 6605219) B6605219
theorem B3715417 : Blo 1545470 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B2937217 : Blo 1545470 2937217 := bstep (se 2 (by rfl) ⟨1101456, by rfl⟩ : syracuseStep 2937217 = 2202913) B2202913
theorem B3477977 : Blo 1545470 3477977 := bstep (se 2 (by rfl) ⟨1304241, by rfl⟩ : syracuseStep 3477977 = 2608483) B2608483
theorem B50180579 : Blo 1545470 50180579 := bstep (se 1 (by rfl) ⟨37635434, by rfl⟩ : syracuseStep 50180579 = 75270869) B75270869
theorem B3478067 : Blo 1545470 3478067 := bstep (se 1 (by rfl) ⟨2608550, by rfl⟩ : syracuseStep 3478067 = 5217101) B5217101
theorem B14864971 : Blo 1545470 14864971 := bstep (se 1 (by rfl) ⟨11148728, by rfl⟩ : syracuseStep 14864971 = 22297457) B22297457
theorem B3478103 : Blo 1545470 3478103 := bstep (se 1 (by rfl) ⟨2608577, by rfl⟩ : syracuseStep 3478103 = 5217155) B5217155
theorem B54317699 : Blo 1545470 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B12546737 : Blo 1545470 12546737 := bstep (se 2 (by rfl) ⟨4705026, by rfl⟩ : syracuseStep 12546737 = 9410053) B9410053
theorem B3912371 : Blo 1545470 3912371 := bstep (se 1 (by rfl) ⟨2934278, by rfl⟩ : syracuseStep 3912371 = 5868557) B5868557
theorem B2609867 : Blo 1545470 2609867 := bstep (se 1 (by rfl) ⟨1957400, by rfl⟩ : syracuseStep 2609867 = 3914801) B3914801
theorem B2937559 : Blo 1545470 2937559 := bstep (se 1 (by rfl) ⟨2203169, by rfl⟩ : syracuseStep 2937559 = 4406339) B4406339
theorem B3478283 : Blo 1545470 3478283 := bstep (se 1 (by rfl) ⟨2608712, by rfl⟩ : syracuseStep 3478283 = 5217425) B5217425
theorem B3478337 : Blo 1545470 3478337 := bstep (se 2 (by rfl) ⟨1304376, by rfl⟩ : syracuseStep 3478337 = 2608753) B2608753
theorem B2609995 : Blo 1545470 2609995 := bstep (se 1 (by rfl) ⟨1957496, by rfl⟩ : syracuseStep 2609995 = 3914993) B3914993
theorem B6607747 : Blo 1545470 6607747 := bstep (se 1 (by rfl) ⟨4955810, by rfl⟩ : syracuseStep 6607747 = 9911621) B9911621
theorem B1651595 : Blo 1545470 1651595 := bstep (se 1 (by rfl) ⟨1238696, by rfl⟩ : syracuseStep 1651595 = 2477393) B2477393
theorem B5870515 : Blo 1545470 5870515 := bstep (se 1 (by rfl) ⟨4402886, by rfl⟩ : syracuseStep 5870515 = 8805773) B8805773
theorem B13210573 : Blo 1545470 13210573 := bstep (se 3 (by rfl) ⟨2476982, by rfl⟩ : syracuseStep 13210573 = 4953965) B4953965
theorem B2610137 : Blo 1545470 2610137 := bstep (se 2 (by rfl) ⟨978801, by rfl⟩ : syracuseStep 2610137 = 1957603) B1957603
theorem B2823179 : Blo 1545470 2823179 := bstep (se 1 (by rfl) ⟨2117384, by rfl⟩ : syracuseStep 2823179 = 4234769) B4234769
theorem B3478553 : Blo 1545470 3478553 := bstep (se 2 (by rfl) ⟨1304457, by rfl⟩ : syracuseStep 3478553 = 2608915) B2608915
theorem B2610265 : Blo 1545470 2610265 := bstep (se 2 (by rfl) ⟨978849, by rfl⟩ : syracuseStep 2610265 = 1957699) B1957699
theorem B3478643 : Blo 1545470 3478643 := bstep (se 1 (by rfl) ⟨2608982, by rfl⟩ : syracuseStep 3478643 = 5217965) B5217965
theorem B3478679 : Blo 1545470 3478679 := bstep (se 1 (by rfl) ⟨2609009, by rfl⟩ : syracuseStep 3478679 = 5218019) B5218019
theorem B12547223 : Blo 1545470 12547223 := bstep (se 1 (by rfl) ⟨9410417, by rfl⟩ : syracuseStep 12547223 = 18820835) B18820835
theorem B3912907 : Blo 1545470 3912907 := bstep (se 1 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 3912907 = 5869361) B5869361
theorem B1545483 : Blo 1545470 1545483 := bstep (se 1 (by rfl) ⟨1159112, by rfl⟩ : syracuseStep 1545483 = 2318225) B2318225
theorem B1545495 : Blo 1545470 1545495 := bstep (se 1 (by rfl) ⟨1159121, by rfl⟩ : syracuseStep 1545495 = 2318243) B2318243
theorem B1545515 : Blo 1545470 1545515 := bstep (se 1 (by rfl) ⟨1159136, by rfl⟩ : syracuseStep 1545515 = 2318273) B2318273
theorem B3134771 : Blo 1545470 3134771 := bstep (se 1 (by rfl) ⟨2351078, by rfl⟩ : syracuseStep 3134771 = 4702157) B4702157
theorem B1545527 : Blo 1545470 1545527 := bstep (se 1 (by rfl) ⟨1159145, by rfl⟩ : syracuseStep 1545527 = 2318291) B2318291
theorem B1545547 : Blo 1545470 1545547 := bstep (se 1 (by rfl) ⟨1159160, by rfl⟩ : syracuseStep 1545547 = 2318321) B2318321
theorem B3478859 : Blo 1545470 3478859 := bstep (se 1 (by rfl) ⟨2609144, by rfl⟩ : syracuseStep 3478859 = 5218289) B5218289
theorem B7828811 : Blo 1545470 7828811 := bstep (se 1 (by rfl) ⟨5871608, by rfl⟩ : syracuseStep 7828811 = 11743217) B11743217
theorem B3970379 : Blo 1545470 3970379 := bstep (se 1 (by rfl) ⟨2977784, by rfl⟩ : syracuseStep 3970379 = 5955569) B5955569
theorem B1545559 : Blo 1545470 1545559 := bstep (se 1 (by rfl) ⟨1159169, by rfl⟩ : syracuseStep 1545559 = 2318339) B2318339
theorem B3913049 : Blo 1545470 3913049 := bstep (se 2 (by rfl) ⟨1467393, by rfl⟩ : syracuseStep 3913049 = 2934787) B2934787
theorem B11736413 : Blo 1545470 11736413 := bstep (se 3 (by rfl) ⟨2200577, by rfl⟩ : syracuseStep 11736413 = 4401155) B4401155
theorem B1545579 : Blo 1545470 1545579 := bstep (se 1 (by rfl) ⟨1159184, by rfl⟩ : syracuseStep 1545579 = 2318369) B2318369
theorem B1545591 : Blo 1545470 1545591 := bstep (se 1 (by rfl) ⟨1159193, by rfl⟩ : syracuseStep 1545591 = 2318387) B2318387
theorem B3478913 : Blo 1545470 3478913 := bstep (se 2 (by rfl) ⟨1304592, by rfl⟩ : syracuseStep 3478913 = 2609185) B2609185
theorem B1545611 : Blo 1545470 1545611 := bstep (se 1 (by rfl) ⟨1159208, by rfl⟩ : syracuseStep 1545611 = 2318417) B2318417
theorem B1545623 : Blo 1545470 1545623 := bstep (se 1 (by rfl) ⟨1159217, by rfl⟩ : syracuseStep 1545623 = 2318435) B2318435
theorem B1545643 : Blo 1545470 1545643 := bstep (se 1 (by rfl) ⟨1159232, by rfl⟩ : syracuseStep 1545643 = 2318465) B2318465
theorem B1545655 : Blo 1545470 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B1545675 : Blo 1545470 1545675 := bstep (se 1 (by rfl) ⟨1159256, by rfl⟩ : syracuseStep 1545675 = 2318513) B2318513
theorem B1545687 : Blo 1545470 1545687 := bstep (se 1 (by rfl) ⟨1159265, by rfl⟩ : syracuseStep 1545687 = 2318531) B2318531
theorem B1545707 : Blo 1545470 1545707 := bstep (se 1 (by rfl) ⟨1159280, by rfl⟩ : syracuseStep 1545707 = 2318561) B2318561
theorem B1545719 : Blo 1545470 1545719 := bstep (se 1 (by rfl) ⟨1159289, by rfl⟩ : syracuseStep 1545719 = 2318579) B2318579
theorem B1545739 : Blo 1545470 1545739 := bstep (se 1 (by rfl) ⟨1159304, by rfl⟩ : syracuseStep 1545739 = 2318609) B2318609
theorem B7435793 : Blo 1545470 7435793 := bstep (se 2 (by rfl) ⟨2788422, by rfl⟩ : syracuseStep 7435793 = 5576845) B5576845
theorem B1545751 : Blo 1545470 1545751 := bstep (se 1 (by rfl) ⟨1159313, by rfl⟩ : syracuseStep 1545751 = 2318627) B2318627
theorem B1545771 : Blo 1545470 1545771 := bstep (se 1 (by rfl) ⟨1159328, by rfl⟩ : syracuseStep 1545771 = 2318657) B2318657
theorem B1545783 : Blo 1545470 1545783 := bstep (se 1 (by rfl) ⟨1159337, by rfl⟩ : syracuseStep 1545783 = 2318675) B2318675
theorem B25073221 : Blo 1545470 25073221 := bstep (se 4 (by rfl) ⟨2350614, by rfl⟩ : syracuseStep 25073221 = 4701229) B4701229
theorem B7050827 : Blo 1545470 7050827 := bstep (se 1 (by rfl) ⟨5288120, by rfl⟩ : syracuseStep 7050827 = 10576241) B10576241
theorem B1545803 : Blo 1545470 1545803 := bstep (se 1 (by rfl) ⟨1159352, by rfl⟩ : syracuseStep 1545803 = 2318705) B2318705
theorem B1545815 : Blo 1545470 1545815 := bstep (se 1 (by rfl) ⟨1159361, by rfl⟩ : syracuseStep 1545815 = 2318723) B2318723
theorem B3479129 : Blo 1545470 3479129 := bstep (se 2 (by rfl) ⟨1304673, by rfl⟩ : syracuseStep 3479129 = 2609347) B2609347
theorem B1545835 : Blo 1545470 1545835 := bstep (se 1 (by rfl) ⟨1159376, by rfl⟩ : syracuseStep 1545835 = 2318753) B2318753
theorem B1545847 : Blo 1545470 1545847 := bstep (se 1 (by rfl) ⟨1159385, by rfl⟩ : syracuseStep 1545847 = 2318771) B2318771
theorem B1545867 : Blo 1545470 1545867 := bstep (se 1 (by rfl) ⟨1159400, by rfl⟩ : syracuseStep 1545867 = 2318801) B2318801
theorem B1545879 : Blo 1545470 1545879 := bstep (se 1 (by rfl) ⟨1159409, by rfl⟩ : syracuseStep 1545879 = 2318819) B2318819
theorem B3348119 : Blo 1545470 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2610839 : Blo 1545470 2610839 := bstep (se 1 (by rfl) ⟨1958129, by rfl⟩ : syracuseStep 2610839 = 3916259) B3916259
theorem B1545899 : Blo 1545470 1545899 := bstep (se 1 (by rfl) ⟨1159424, by rfl⟩ : syracuseStep 1545899 = 2318849) B2318849
theorem B3479219 : Blo 1545470 3479219 := bstep (se 1 (by rfl) ⟨2609414, by rfl⟩ : syracuseStep 3479219 = 5218829) B5218829
theorem B1545911 : Blo 1545470 1545911 := bstep (se 1 (by rfl) ⟨1159433, by rfl⟩ : syracuseStep 1545911 = 2318867) B2318867
theorem B1545931 : Blo 1545470 1545931 := bstep (se 1 (by rfl) ⟨1159448, by rfl⟩ : syracuseStep 1545931 = 2318897) B2318897
theorem B1545943 : Blo 1545470 1545943 := bstep (se 1 (by rfl) ⟨1159457, by rfl⟩ : syracuseStep 1545943 = 2318915) B2318915
theorem B3479255 : Blo 1545470 3479255 := bstep (se 1 (by rfl) ⟨2609441, by rfl⟩ : syracuseStep 3479255 = 5218883) B5218883
theorem B13203161 : Blo 1545470 13203161 := bstep (se 2 (by rfl) ⟨4951185, by rfl⟩ : syracuseStep 13203161 = 9902371) B9902371
theorem B3135191 : Blo 1545470 3135191 := bstep (se 1 (by rfl) ⟨2351393, by rfl⟩ : syracuseStep 3135191 = 4702787) B4702787
theorem B1545963 : Blo 1545470 1545963 := bstep (se 1 (by rfl) ⟨1159472, by rfl⟩ : syracuseStep 1545963 = 2318945) B2318945
theorem B1545975 : Blo 1545470 1545975 := bstep (se 1 (by rfl) ⟨1159481, by rfl⟩ : syracuseStep 1545975 = 2318963) B2318963
theorem B1545995 : Blo 1545470 1545995 := bstep (se 1 (by rfl) ⟨1159496, by rfl⟩ : syracuseStep 1545995 = 2318993) B2318993
theorem B1546007 : Blo 1545470 1546007 := bstep (se 1 (by rfl) ⟨1159505, by rfl⟩ : syracuseStep 1546007 = 2319011) B2319011
theorem B2610967 : Blo 1545470 2610967 := bstep (se 1 (by rfl) ⟨1958225, by rfl⟩ : syracuseStep 2610967 = 3916451) B3916451
theorem B1546027 : Blo 1545470 1546027 := bstep (se 1 (by rfl) ⟨1159520, by rfl⟩ : syracuseStep 1546027 = 2319041) B2319041
theorem B1546039 : Blo 1545470 1546039 := bstep (se 1 (by rfl) ⟨1159529, by rfl⟩ : syracuseStep 1546039 = 2319059) B2319059
theorem B5216075 : Blo 1545470 5216075 := bstep (se 1 (by rfl) ⟨3912056, by rfl⟩ : syracuseStep 5216075 = 7824113) B7824113
theorem B1546059 : Blo 1545470 1546059 := bstep (se 1 (by rfl) ⟨1159544, by rfl⟩ : syracuseStep 1546059 = 2319089) B2319089
theorem B1546071 : Blo 1545470 1546071 := bstep (se 1 (by rfl) ⟨1159553, by rfl⟩ : syracuseStep 1546071 = 2319107) B2319107
theorem B1546091 : Blo 1545470 1546091 := bstep (se 1 (by rfl) ⟨1159568, by rfl⟩ : syracuseStep 1546091 = 2319137) B2319137
theorem B1546103 : Blo 1545470 1546103 := bstep (se 1 (by rfl) ⟨1159577, by rfl⟩ : syracuseStep 1546103 = 2319155) B2319155
theorem B1546123 : Blo 1545470 1546123 := bstep (se 1 (by rfl) ⟨1159592, by rfl⟩ : syracuseStep 1546123 = 2319185) B2319185
theorem B3479435 : Blo 1545470 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B1546135 : Blo 1545470 1546135 := bstep (se 1 (by rfl) ⟨1159601, by rfl⟩ : syracuseStep 1546135 = 2319203) B2319203
theorem B1546155 : Blo 1545470 1546155 := bstep (se 1 (by rfl) ⟨1159616, by rfl⟩ : syracuseStep 1546155 = 2319233) B2319233
theorem B29710259 : Blo 1545470 29710259 := bstep (se 1 (by rfl) ⟨22282694, by rfl⟩ : syracuseStep 29710259 = 44565389) B44565389
theorem B1546167 : Blo 1545470 1546167 := bstep (se 1 (by rfl) ⟨1159625, by rfl⟩ : syracuseStep 1546167 = 2319251) B2319251
theorem B3479489 : Blo 1545470 3479489 := bstep (se 2 (by rfl) ⟨1304808, by rfl⟩ : syracuseStep 3479489 = 2609617) B2609617
theorem B1546187 : Blo 1545470 1546187 := bstep (se 1 (by rfl) ⟨1159640, by rfl⟩ : syracuseStep 1546187 = 2319281) B2319281
theorem B1546199 : Blo 1545470 1546199 := bstep (se 1 (by rfl) ⟨1159649, by rfl⟩ : syracuseStep 1546199 = 2319299) B2319299
theorem B1546219 : Blo 1545470 1546219 := bstep (se 1 (by rfl) ⟨1159664, by rfl⟩ : syracuseStep 1546219 = 2319329) B2319329
theorem B1546231 : Blo 1545470 1546231 := bstep (se 1 (by rfl) ⟨1159673, by rfl⟩ : syracuseStep 1546231 = 2319347) B2319347
theorem B1546251 : Blo 1545470 1546251 := bstep (se 1 (by rfl) ⟨1159688, by rfl⟩ : syracuseStep 1546251 = 2319377) B2319377
theorem B9910289 : Blo 1545470 9910289 := bstep (se 2 (by rfl) ⟨3716358, by rfl⟩ : syracuseStep 9910289 = 7432717) B7432717
theorem B1546263 : Blo 1545470 1546263 := bstep (se 1 (by rfl) ⟨1159697, by rfl⟩ : syracuseStep 1546263 = 2319395) B2319395
theorem B1546283 : Blo 1545470 1546283 := bstep (se 1 (by rfl) ⟨1159712, by rfl⟩ : syracuseStep 1546283 = 2319425) B2319425
theorem B1546295 : Blo 1545470 1546295 := bstep (se 1 (by rfl) ⟨1159721, by rfl⟩ : syracuseStep 1546295 = 2319443) B2319443
theorem B1546315 : Blo 1545470 1546315 := bstep (se 1 (by rfl) ⟨1159736, by rfl⟩ : syracuseStep 1546315 = 2319473) B2319473
theorem B1546327 : Blo 1545470 1546327 := bstep (se 1 (by rfl) ⟨1159745, by rfl⟩ : syracuseStep 1546327 = 2319491) B2319491
theorem B5216345 : Blo 1545470 5216345 := bstep (se 2 (by rfl) ⟨1956129, by rfl⟩ : syracuseStep 5216345 = 3912259) B3912259
theorem B4405337 : Blo 1545470 4405337 := bstep (se 2 (by rfl) ⟨1652001, by rfl⟩ : syracuseStep 4405337 = 3304003) B3304003
theorem B1546347 : Blo 1545470 1546347 := bstep (se 1 (by rfl) ⟨1159760, by rfl⟩ : syracuseStep 1546347 = 2319521) B2319521
theorem B1546359 : Blo 1545470 1546359 := bstep (se 1 (by rfl) ⟨1159769, by rfl⟩ : syracuseStep 1546359 = 2319539) B2319539
theorem B1546379 : Blo 1545470 1546379 := bstep (se 1 (by rfl) ⟨1159784, by rfl⟩ : syracuseStep 1546379 = 2319569) B2319569
theorem B5871761 : Blo 1545470 5871761 := bstep (se 2 (by rfl) ⟨2201910, by rfl⟩ : syracuseStep 5871761 = 4403821) B4403821
theorem B3913879 : Blo 1545470 3913879 := bstep (se 1 (by rfl) ⟨2935409, by rfl⟩ : syracuseStep 3913879 = 5870819) B5870819
theorem B1546391 : Blo 1545470 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B3479705 : Blo 1545470 3479705 := bstep (se 2 (by rfl) ⟨1304889, by rfl⟩ : syracuseStep 3479705 = 2609779) B2609779
theorem B11303063 : Blo 1545470 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B1546411 : Blo 1545470 1546411 := bstep (se 1 (by rfl) ⟨1159808, by rfl⟩ : syracuseStep 1546411 = 2319617) B2319617
theorem B1546423 : Blo 1545470 1546423 := bstep (se 1 (by rfl) ⟨1159817, by rfl⟩ : syracuseStep 1546423 = 2319635) B2319635
theorem B1546443 : Blo 1545470 1546443 := bstep (se 1 (by rfl) ⟨1159832, by rfl⟩ : syracuseStep 1546443 = 2319665) B2319665
theorem B1546455 : Blo 1545470 1546455 := bstep (se 1 (by rfl) ⟨1159841, by rfl⟩ : syracuseStep 1546455 = 2319683) B2319683
theorem B1546475 : Blo 1545470 1546475 := bstep (se 1 (by rfl) ⟨1159856, by rfl⟩ : syracuseStep 1546475 = 2319713) B2319713
theorem B3479795 : Blo 1545470 3479795 := bstep (se 1 (by rfl) ⟨2609846, by rfl⟩ : syracuseStep 3479795 = 5219693) B5219693
theorem B1546487 : Blo 1545470 1546487 := bstep (se 1 (by rfl) ⟨1159865, by rfl⟩ : syracuseStep 1546487 = 2319731) B2319731
theorem B13211909 : Blo 1545470 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B1546507 : Blo 1545470 1546507 := bstep (se 1 (by rfl) ⟨1159880, by rfl⟩ : syracuseStep 1546507 = 2319761) B2319761
theorem B1546519 : Blo 1545470 1546519 := bstep (se 1 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 1546519 = 2319779) B2319779
theorem B3479831 : Blo 1545470 3479831 := bstep (se 1 (by rfl) ⟨2609873, by rfl⟩ : syracuseStep 3479831 = 5219747) B5219747
theorem B1546539 : Blo 1545470 1546539 := bstep (se 1 (by rfl) ⟨1159904, by rfl⟩ : syracuseStep 1546539 = 2319809) B2319809
theorem B5577005 : Blo 1545470 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B1546551 : Blo 1545470 1546551 := bstep (se 1 (by rfl) ⟨1159913, by rfl⟩ : syracuseStep 1546551 = 2319827) B2319827
theorem B3135809 : Blo 1545470 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B1546571 : Blo 1545470 1546571 := bstep (se 1 (by rfl) ⟨1159928, by rfl⟩ : syracuseStep 1546571 = 2319857) B2319857
theorem B1546583 : Blo 1545470 1546583 := bstep (se 1 (by rfl) ⟨1159937, by rfl⟩ : syracuseStep 1546583 = 2319875) B2319875
theorem B1546603 : Blo 1545470 1546603 := bstep (se 1 (by rfl) ⟨1159952, by rfl⟩ : syracuseStep 1546603 = 2319905) B2319905
theorem B1546615 : Blo 1545470 1546615 := bstep (se 1 (by rfl) ⟨1159961, by rfl⟩ : syracuseStep 1546615 = 2319923) B2319923
theorem B1546635 : Blo 1545470 1546635 := bstep (se 1 (by rfl) ⟨1159976, by rfl⟩ : syracuseStep 1546635 = 2319953) B2319953
theorem B1546647 : Blo 1545470 1546647 := bstep (se 1 (by rfl) ⟨1159985, by rfl⟩ : syracuseStep 1546647 = 2319971) B2319971
theorem B1546667 : Blo 1545470 1546667 := bstep (se 1 (by rfl) ⟨1160000, by rfl⟩ : syracuseStep 1546667 = 2320001) B2320001
theorem B5577133 : Blo 1545470 5577133 := bstep (se 3 (by rfl) ⟨1045712, by rfl⟩ : syracuseStep 5577133 = 2091425) B2091425
theorem B1546679 : Blo 1545470 1546679 := bstep (se 1 (by rfl) ⟨1160009, by rfl⟩ : syracuseStep 1546679 = 2320019) B2320019
theorem B381114821 : Blo 1545470 381114821 := bstep (se 4 (by rfl) ⟨35729514, by rfl⟩ : syracuseStep 381114821 = 71459029) B71459029
theorem B3480011 : Blo 1545470 3480011 := bstep (se 1 (by rfl) ⟨2610008, by rfl⟩ : syracuseStep 3480011 = 5220017) B5220017
theorem B1546699 : Blo 1545470 1546699 := bstep (se 1 (by rfl) ⟨1160024, by rfl⟩ : syracuseStep 1546699 = 2320049) B2320049
theorem B1546711 : Blo 1545470 1546711 := bstep (se 1 (by rfl) ⟨1160033, by rfl⟩ : syracuseStep 1546711 = 2320067) B2320067
theorem B1546731 : Blo 1545470 1546731 := bstep (se 1 (by rfl) ⟨1160048, by rfl⟩ : syracuseStep 1546731 = 2320097) B2320097
theorem B1546743 : Blo 1545470 1546743 := bstep (se 1 (by rfl) ⟨1160057, by rfl⟩ : syracuseStep 1546743 = 2320115) B2320115
theorem B3480065 : Blo 1545470 3480065 := bstep (se 2 (by rfl) ⟨1305024, by rfl⟩ : syracuseStep 3480065 = 2610049) B2610049
theorem B1546763 : Blo 1545470 1546763 := bstep (se 1 (by rfl) ⟨1160072, by rfl⟩ : syracuseStep 1546763 = 2320145) B2320145
theorem B1546775 : Blo 1545470 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1546795 : Blo 1545470 1546795 := bstep (se 1 (by rfl) ⟨1160096, by rfl⟩ : syracuseStep 1546795 = 2320193) B2320193
theorem B1546807 : Blo 1545470 1546807 := bstep (se 1 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 1546807 = 2320211) B2320211
theorem B3914315 : Blo 1545470 3914315 := bstep (se 1 (by rfl) ⟨2935736, by rfl⟩ : syracuseStep 3914315 = 5871473) B5871473
theorem B1546827 : Blo 1545470 1546827 := bstep (se 1 (by rfl) ⟨1160120, by rfl⟩ : syracuseStep 1546827 = 2320241) B2320241
theorem B1546839 : Blo 1545470 1546839 := bstep (se 1 (by rfl) ⟨1160129, by rfl⟩ : syracuseStep 1546839 = 2320259) B2320259
theorem B1546859 : Blo 1545470 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B1546871 : Blo 1545470 1546871 := bstep (se 1 (by rfl) ⟨1160153, by rfl⟩ : syracuseStep 1546871 = 2320307) B2320307
theorem B1546891 : Blo 1545470 1546891 := bstep (se 1 (by rfl) ⟨1160168, by rfl⟩ : syracuseStep 1546891 = 2320337) B2320337
theorem B1546903 : Blo 1545470 1546903 := bstep (se 1 (by rfl) ⟨1160177, by rfl⟩ : syracuseStep 1546903 = 2320355) B2320355
theorem B6609559 : Blo 1545470 6609559 := bstep (se 1 (by rfl) ⟨4957169, by rfl⟩ : syracuseStep 6609559 = 9914339) B9914339
theorem B1546923 : Blo 1545470 1546923 := bstep (se 1 (by rfl) ⟨1160192, by rfl⟩ : syracuseStep 1546923 = 2320385) B2320385
theorem B1546935 : Blo 1545470 1546935 := bstep (se 1 (by rfl) ⟨1160201, by rfl⟩ : syracuseStep 1546935 = 2320403) B2320403
theorem B4831937 : Blo 1545470 4831937 := bstep (se 2 (by rfl) ⟨1811976, by rfl⟩ : syracuseStep 4831937 = 3623953) B3623953
theorem B1546955 : Blo 1545470 1546955 := bstep (se 1 (by rfl) ⟨1160216, by rfl⟩ : syracuseStep 1546955 = 2320433) B2320433
theorem B1546967 : Blo 1545470 1546967 := bstep (se 1 (by rfl) ⟨1160225, by rfl⟩ : syracuseStep 1546967 = 2320451) B2320451
theorem B3480281 : Blo 1545470 3480281 := bstep (se 2 (by rfl) ⟨1305105, by rfl⟩ : syracuseStep 3480281 = 2610211) B2610211
theorem B1546987 : Blo 1545470 1546987 := bstep (se 1 (by rfl) ⟨1160240, by rfl⟩ : syracuseStep 1546987 = 2320481) B2320481
theorem B1546999 : Blo 1545470 1546999 := bstep (se 1 (by rfl) ⟨1160249, by rfl⟩ : syracuseStep 1546999 = 2320499) B2320499
theorem B1547019 : Blo 1545470 1547019 := bstep (se 1 (by rfl) ⟨1160264, by rfl⟩ : syracuseStep 1547019 = 2320529) B2320529
theorem B5217047 : Blo 1545470 5217047 := bstep (se 1 (by rfl) ⟨3912785, by rfl⟩ : syracuseStep 5217047 = 7825571) B7825571
theorem B1956631 : Blo 1545470 1956631 := bstep (se 1 (by rfl) ⟨1467473, by rfl⟩ : syracuseStep 1956631 = 2934947) B2934947
theorem B1547031 : Blo 1545470 1547031 := bstep (se 1 (by rfl) ⟨1160273, by rfl⟩ : syracuseStep 1547031 = 2320547) B2320547
theorem B1547051 : Blo 1545470 1547051 := bstep (se 1 (by rfl) ⟨1160288, by rfl⟩ : syracuseStep 1547051 = 2320577) B2320577
theorem B3480371 : Blo 1545470 3480371 := bstep (se 1 (by rfl) ⟨2610278, by rfl⟩ : syracuseStep 3480371 = 5220557) B5220557
theorem B1547063 : Blo 1545470 1547063 := bstep (se 1 (by rfl) ⟨1160297, by rfl⟩ : syracuseStep 1547063 = 2320595) B2320595
theorem B12540737 : Blo 1545470 12540737 := bstep (se 2 (by rfl) ⟨4702776, by rfl⟩ : syracuseStep 12540737 = 9405553) B9405553
theorem B5872459 : Blo 1545470 5872459 := bstep (se 1 (by rfl) ⟨4404344, by rfl⟩ : syracuseStep 5872459 = 8808689) B8808689
theorem B1547083 : Blo 1545470 1547083 := bstep (se 1 (by rfl) ⟨1160312, by rfl⟩ : syracuseStep 1547083 = 2320625) B2320625
theorem B2349911 : Blo 1545470 2349911 := bstep (se 1 (by rfl) ⟨1762433, by rfl⟩ : syracuseStep 2349911 = 3524867) B3524867
theorem B3480407 : Blo 1545470 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B4586329 : Blo 1545470 4586329 := bstep (se 2 (by rfl) ⟨1719873, by rfl⟩ : syracuseStep 4586329 = 3439747) B3439747
theorem B1547095 : Blo 1545470 1547095 := bstep (se 1 (by rfl) ⟨1160321, by rfl⟩ : syracuseStep 1547095 = 2320643) B2320643
theorem B1547115 : Blo 1545470 1547115 := bstep (se 1 (by rfl) ⟨1160336, by rfl⟩ : syracuseStep 1547115 = 2320673) B2320673
theorem B1547127 : Blo 1545470 1547127 := bstep (se 1 (by rfl) ⟨1160345, by rfl⟩ : syracuseStep 1547127 = 2320691) B2320691
theorem B1547147 : Blo 1545470 1547147 := bstep (se 1 (by rfl) ⟨1160360, by rfl⟩ : syracuseStep 1547147 = 2320721) B2320721
theorem B1547159 : Blo 1545470 1547159 := bstep (se 1 (by rfl) ⟨1160369, by rfl⟩ : syracuseStep 1547159 = 2320739) B2320739
theorem B4406167 : Blo 1545470 4406167 := bstep (se 1 (by rfl) ⟨3304625, by rfl⟩ : syracuseStep 4406167 = 6609251) B6609251
theorem B1547179 : Blo 1545470 1547179 := bstep (se 1 (by rfl) ⟨1160384, by rfl⟩ : syracuseStep 1547179 = 2320769) B2320769
theorem B1547191 : Blo 1545470 1547191 := bstep (se 1 (by rfl) ⟨1160393, by rfl⟩ : syracuseStep 1547191 = 2320787) B2320787
theorem B3914689 : Blo 1545470 3914689 := bstep (se 2 (by rfl) ⟨1468008, by rfl⟩ : syracuseStep 3914689 = 2936017) B2936017
theorem B1547211 : Blo 1545470 1547211 := bstep (se 1 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 1547211 = 2320817) B2320817
theorem B1547223 : Blo 1545470 1547223 := bstep (se 1 (by rfl) ⟨1160417, by rfl⟩ : syracuseStep 1547223 = 2320835) B2320835
theorem B17619929 : Blo 1545470 17619929 := bstep (se 2 (by rfl) ⟨6607473, by rfl⟩ : syracuseStep 17619929 = 13214947) B13214947
theorem B1547243 : Blo 1545470 1547243 := bstep (se 1 (by rfl) ⟨1160432, by rfl⟩ : syracuseStep 1547243 = 2320865) B2320865
theorem B1547255 : Blo 1545470 1547255 := bstep (se 1 (by rfl) ⟨1160441, by rfl⟩ : syracuseStep 1547255 = 2320883) B2320883
theorem B3480587 : Blo 1545470 3480587 := bstep (se 1 (by rfl) ⟨2610440, by rfl⟩ : syracuseStep 3480587 = 5220881) B5220881
theorem B1547275 : Blo 1545470 1547275 := bstep (se 1 (by rfl) ⟨1160456, by rfl⟩ : syracuseStep 1547275 = 2320913) B2320913
theorem B1858583 : Blo 1545470 1858583 := bstep (se 1 (by rfl) ⟨1393937, by rfl⟩ : syracuseStep 1858583 = 2787875) B2787875
theorem B1547287 : Blo 1545470 1547287 := bstep (se 1 (by rfl) ⟨1160465, by rfl⟩ : syracuseStep 1547287 = 2320931) B2320931
theorem B1547307 : Blo 1545470 1547307 := bstep (se 1 (by rfl) ⟨1160480, by rfl⟩ : syracuseStep 1547307 = 2320961) B2320961
theorem B1547319 : Blo 1545470 1547319 := bstep (se 1 (by rfl) ⟨1160489, by rfl⟩ : syracuseStep 1547319 = 2320979) B2320979
theorem B7830593 : Blo 1545470 7830593 := bstep (se 2 (by rfl) ⟨2936472, by rfl⟩ : syracuseStep 7830593 = 5872945) B5872945
theorem B3480641 : Blo 1545470 3480641 := bstep (se 2 (by rfl) ⟨1305240, by rfl⟩ : syracuseStep 3480641 = 2610481) B2610481
theorem B16710731 : Blo 1545470 16710731 := bstep (se 1 (by rfl) ⟨12533048, by rfl⟩ : syracuseStep 16710731 = 25066097) B25066097
theorem B1547339 : Blo 1545470 1547339 := bstep (se 1 (by rfl) ⟨1160504, by rfl⟩ : syracuseStep 1547339 = 2321009) B2321009
theorem B1547351 : Blo 1545470 1547351 := bstep (se 1 (by rfl) ⟨1160513, by rfl⟩ : syracuseStep 1547351 = 2321027) B2321027
theorem B5872733 : Blo 1545470 5872733 := bstep (se 3 (by rfl) ⟨1101137, by rfl⟩ : syracuseStep 5872733 = 2202275) B2202275
theorem B1547371 : Blo 1545470 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B1547383 : Blo 1545470 1547383 := bstep (se 1 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 1547383 = 2321075) B2321075
theorem B1547403 : Blo 1545470 1547403 := bstep (se 1 (by rfl) ⟨1160552, by rfl⟩ : syracuseStep 1547403 = 2321105) B2321105
theorem B1547415 : Blo 1545470 1547415 := bstep (se 1 (by rfl) ⟨1160561, by rfl⟩ : syracuseStep 1547415 = 2321123) B2321123
theorem B1547435 : Blo 1545470 1547435 := bstep (se 1 (by rfl) ⟨1160576, by rfl⟩ : syracuseStep 1547435 = 2321153) B2321153
theorem B1547447 : Blo 1545470 1547447 := bstep (se 1 (by rfl) ⟨1160585, by rfl⟩ : syracuseStep 1547447 = 2321171) B2321171
theorem B1547467 : Blo 1545470 1547467 := bstep (se 1 (by rfl) ⟨1160600, by rfl⟩ : syracuseStep 1547467 = 2321201) B2321201
theorem B4463837 : Blo 1545470 4463837 := bstep (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) B1673939
theorem B3480857 : Blo 1545470 3480857 := bstep (se 2 (by rfl) ⟨1305321, by rfl⟩ : syracuseStep 3480857 = 2610643) B2610643
theorem B5217587 : Blo 1545470 5217587 := bstep (se 1 (by rfl) ⟨3913190, by rfl⟩ : syracuseStep 5217587 = 7826381) B7826381
theorem B1858891 : Blo 1545470 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B3480947 : Blo 1545470 3480947 := bstep (se 1 (by rfl) ⟨2610710, by rfl⟩ : syracuseStep 3480947 = 5221421) B5221421
theorem B171589013 : Blo 1545470 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B3480983 : Blo 1545470 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B2203033 : Blo 1545470 2203033 := bstep (se 2 (by rfl) ⟨826137, by rfl⟩ : syracuseStep 2203033 = 1652275) B1652275
theorem B3915287 : Blo 1545470 3915287 := bstep (se 1 (by rfl) ⟨2936465, by rfl⟩ : syracuseStep 3915287 = 5872931) B5872931
theorem B5217857 : Blo 1545470 5217857 := bstep (se 2 (by rfl) ⟨1956696, by rfl⟩ : syracuseStep 5217857 = 3913393) B3913393
theorem B3481163 : Blo 1545470 3481163 := bstep (se 1 (by rfl) ⟨2610872, by rfl⟩ : syracuseStep 3481163 = 5221745) B5221745
theorem B3481217 : Blo 1545470 3481217 := bstep (se 2 (by rfl) ⟨1305456, by rfl⟩ : syracuseStep 3481217 = 2610913) B2610913
theorem B3301003 : Blo 1545470 3301003 := bstep (se 1 (by rfl) ⟨2475752, by rfl⟩ : syracuseStep 3301003 = 4951505) B4951505
theorem B5873431 : Blo 1545470 5873431 := bstep (se 1 (by rfl) ⟨4405073, by rfl⟩ : syracuseStep 5873431 = 8810147) B8810147
theorem B3481433 : Blo 1545470 3481433 := bstep (se 2 (by rfl) ⟨1305537, by rfl⟩ : syracuseStep 3481433 = 2611075) B2611075
theorem B2318219 : Blo 1545470 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B2318231 : Blo 1545470 2318231 := bstep (se 1 (by rfl) ⟨1738673, by rfl⟩ : syracuseStep 2318231 = 3477347) B3477347
theorem B3481523 : Blo 1545470 3481523 := bstep (se 1 (by rfl) ⟨2611142, by rfl⟩ : syracuseStep 3481523 = 5222285) B5222285
theorem B3481559 : Blo 1545470 3481559 := bstep (se 1 (by rfl) ⟨2611169, by rfl⟩ : syracuseStep 3481559 = 5222339) B5222339
theorem B2318297 : Blo 1545470 2318297 := bstep (se 2 (by rfl) ⟨869361, by rfl⟩ : syracuseStep 2318297 = 1738723) B1738723
theorem B3301337 : Blo 1545470 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B9904139 : Blo 1545470 9904139 := bstep (se 1 (by rfl) ⟨7428104, by rfl⟩ : syracuseStep 9904139 = 14856209) B14856209
theorem B2318351 : Blo 1545470 2318351 := bstep (se 1 (by rfl) ⟨1738763, by rfl⟩ : syracuseStep 2318351 = 3477527) B3477527
theorem B33431575 : Blo 1545470 33431575 := bstep (se 1 (by rfl) ⟨25073681, by rfl⟩ : syracuseStep 33431575 = 50147363) B50147363
theorem B7938071 : Blo 1545470 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B7528477 : Blo 1545470 7528477 := bstep (se 3 (by rfl) ⟨1411589, by rfl⟩ : syracuseStep 7528477 = 2823179) B2823179
theorem B2318393 : Blo 1545470 2318393 := bstep (se 2 (by rfl) ⟨869397, by rfl⟩ : syracuseStep 2318393 = 1738795) B1738795
theorem B18817085 : Blo 1545470 18817085 := bstep (se 3 (by rfl) ⟨3528203, by rfl⟩ : syracuseStep 18817085 = 7056407) B7056407
theorem B4956221 : Blo 1545470 4956221 := bstep (se 3 (by rfl) ⟨929291, by rfl⟩ : syracuseStep 4956221 = 1858583) B1858583
theorem B2318471 : Blo 1545470 2318471 := bstep (se 1 (by rfl) ⟨1738853, by rfl⟩ : syracuseStep 2318471 = 3477707) B3477707
theorem B1958023 : Blo 1545470 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2318507 : Blo 1545470 2318507 := bstep (se 1 (by rfl) ⟨1738880, by rfl⟩ : syracuseStep 2318507 = 3477761) B3477761
theorem B2318537 : Blo 1545470 2318537 := bstep (se 2 (by rfl) ⟨869451, by rfl⟩ : syracuseStep 2318537 = 1738903) B1738903
theorem B5218505 : Blo 1545470 5218505 := bstep (se 2 (by rfl) ⟨1956939, by rfl⟩ : syracuseStep 5218505 = 3913879) B3913879
theorem B2318651 : Blo 1545470 2318651 := bstep (se 1 (by rfl) ⟨1738988, by rfl⟩ : syracuseStep 2318651 = 3477977) B3477977
theorem B18817373 : Blo 1545470 18817373 := bstep (se 3 (by rfl) ⟨3528257, by rfl⟩ : syracuseStep 18817373 = 7056515) B7056515
theorem B3916147 : Blo 1545470 3916147 := bstep (se 1 (by rfl) ⟨2937110, by rfl⟩ : syracuseStep 3916147 = 5874221) B5874221
theorem B2318711 : Blo 1545470 2318711 := bstep (se 1 (by rfl) ⟨1739033, by rfl⟩ : syracuseStep 2318711 = 3478067) B3478067
theorem B2318735 : Blo 1545470 2318735 := bstep (se 1 (by rfl) ⟨1739051, by rfl⟩ : syracuseStep 2318735 = 3478103) B3478103
theorem B2318777 : Blo 1545470 2318777 := bstep (se 2 (by rfl) ⟨869541, by rfl⟩ : syracuseStep 2318777 = 1739083) B1739083
theorem B8364491 : Blo 1545470 8364491 := bstep (se 1 (by rfl) ⟨6273368, by rfl⟩ : syracuseStep 8364491 = 12546737) B12546737
theorem B3916289 : Blo 1545470 3916289 := bstep (se 2 (by rfl) ⟨1468608, by rfl⟩ : syracuseStep 3916289 = 2937217) B2937217
theorem B2318855 : Blo 1545470 2318855 := bstep (se 1 (by rfl) ⟨1739141, by rfl⟩ : syracuseStep 2318855 = 3478283) B3478283
theorem B4178461 : Blo 1545470 4178461 := bstep (se 3 (by rfl) ⟨783461, by rfl⟩ : syracuseStep 4178461 = 1566923) B1566923
theorem B2318891 : Blo 1545470 2318891 := bstep (se 1 (by rfl) ⟨1739168, by rfl⟩ : syracuseStep 2318891 = 3478337) B3478337
theorem B2318921 : Blo 1545470 2318921 := bstep (se 2 (by rfl) ⟨869595, by rfl⟩ : syracuseStep 2318921 = 1739191) B1739191
theorem B14099021 : Blo 1545470 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B5653111 : Blo 1545470 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B2319035 : Blo 1545470 2319035 := bstep (se 1 (by rfl) ⟨1739276, by rfl⟩ : syracuseStep 2319035 = 3478553) B3478553
theorem B17605349 : Blo 1545470 17605349 := bstep (se 4 (by rfl) ⟨1650501, by rfl⟩ : syracuseStep 17605349 = 3301003) B3301003
theorem B2319095 : Blo 1545470 2319095 := bstep (se 1 (by rfl) ⟨1739321, by rfl⟩ : syracuseStep 2319095 = 3478643) B3478643
theorem B4178699 : Blo 1545470 4178699 := bstep (se 1 (by rfl) ⟨3134024, by rfl⟩ : syracuseStep 4178699 = 6268049) B6268049
theorem B2319119 : Blo 1545470 2319119 := bstep (se 1 (by rfl) ⟨1739339, by rfl⟩ : syracuseStep 2319119 = 3478679) B3478679
theorem B8364815 : Blo 1545470 8364815 := bstep (se 1 (by rfl) ⟨6273611, by rfl⟩ : syracuseStep 8364815 = 12547223) B12547223
theorem B2319161 : Blo 1545470 2319161 := bstep (se 2 (by rfl) ⟨869685, by rfl⟩ : syracuseStep 2319161 = 1739371) B1739371
theorem B4178807 : Blo 1545470 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B2089847 : Blo 1545470 2089847 := bstep (se 1 (by rfl) ⟨1567385, by rfl⟩ : syracuseStep 2089847 = 3134771) B3134771
theorem B2319239 : Blo 1545470 2319239 := bstep (se 1 (by rfl) ⟨1739429, by rfl⟩ : syracuseStep 2319239 = 3478859) B3478859
theorem B5219207 : Blo 1545470 5219207 := bstep (se 1 (by rfl) ⟨3914405, by rfl⟩ : syracuseStep 5219207 = 7828811) B7828811
theorem B7824275 : Blo 1545470 7824275 := bstep (se 1 (by rfl) ⟨5868206, by rfl⟩ : syracuseStep 7824275 = 11736413) B11736413
theorem B2319275 : Blo 1545470 2319275 := bstep (se 1 (by rfl) ⟨1739456, by rfl⟩ : syracuseStep 2319275 = 3478913) B3478913
theorem B2319305 : Blo 1545470 2319305 := bstep (se 2 (by rfl) ⟨869739, by rfl⟩ : syracuseStep 2319305 = 1739479) B1739479
theorem B3916745 : Blo 1545470 3916745 := bstep (se 2 (by rfl) ⟨1468779, by rfl⟩ : syracuseStep 3916745 = 2937559) B2937559
theorem B4957195 : Blo 1545470 4957195 := bstep (se 1 (by rfl) ⟨3717896, by rfl⟩ : syracuseStep 4957195 = 7435793) B7435793
theorem B2319419 : Blo 1545470 2319419 := bstep (se 1 (by rfl) ⟨1739564, by rfl⟩ : syracuseStep 2319419 = 3479129) B3479129
theorem B2319479 : Blo 1545470 2319479 := bstep (se 1 (by rfl) ⟨1739609, by rfl⟩ : syracuseStep 2319479 = 3479219) B3479219
theorem B2319503 : Blo 1545470 2319503 := bstep (se 1 (by rfl) ⟨1739627, by rfl⟩ : syracuseStep 2319503 = 3479255) B3479255
theorem B2319545 : Blo 1545470 2319545 := bstep (se 2 (by rfl) ⟨869829, by rfl⟩ : syracuseStep 2319545 = 1739659) B1739659
theorem B5874889 : Blo 1545470 5874889 := bstep (se 2 (by rfl) ⟨2203083, by rfl⟩ : syracuseStep 5874889 = 4406167) B4406167
theorem B5219585 : Blo 1545470 5219585 := bstep (se 2 (by rfl) ⟨1957344, by rfl⟩ : syracuseStep 5219585 = 3914689) B3914689
theorem B2319623 : Blo 1545470 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B17614097 : Blo 1545470 17614097 := bstep (se 2 (by rfl) ⟨6605286, by rfl⟩ : syracuseStep 17614097 = 13210573) B13210573
theorem B108660001 : Blo 1545470 108660001 := bstep (se 2 (by rfl) ⟨40747500, by rfl⟩ : syracuseStep 108660001 = 81495001) B81495001
theorem B2319659 : Blo 1545470 2319659 := bstep (se 1 (by rfl) ⟨1739744, by rfl⟩ : syracuseStep 2319659 = 3479489) B3479489
theorem B2319689 : Blo 1545470 2319689 := bstep (se 2 (by rfl) ⟨869883, by rfl⟩ : syracuseStep 2319689 = 1739767) B1739767
theorem B2319803 : Blo 1545470 2319803 := bstep (se 1 (by rfl) ⟨1739852, by rfl⟩ : syracuseStep 2319803 = 3479705) B3479705
theorem B2319863 : Blo 1545470 2319863 := bstep (se 1 (by rfl) ⟨1739897, by rfl⟩ : syracuseStep 2319863 = 3479795) B3479795
theorem B8807939 : Blo 1545470 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B2319887 : Blo 1545470 2319887 := bstep (se 1 (by rfl) ⟨1739915, by rfl⟩ : syracuseStep 2319887 = 3479831) B3479831
theorem B29713949 : Blo 1545470 29713949 := bstep (se 3 (by rfl) ⟨5571365, by rfl⟩ : syracuseStep 29713949 = 11142731) B11142731
theorem B2090539 : Blo 1545470 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B2319929 : Blo 1545470 2319929 := bstep (se 2 (by rfl) ⟨869973, by rfl⟩ : syracuseStep 2319929 = 1739947) B1739947
theorem B254076547 : Blo 1545470 254076547 := bstep (se 1 (by rfl) ⟨190557410, by rfl⟩ : syracuseStep 254076547 = 381114821) B381114821
theorem B2934407 : Blo 1545470 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B2320007 : Blo 1545470 2320007 := bstep (se 1 (by rfl) ⟨1740005, by rfl⟩ : syracuseStep 2320007 = 3480011) B3480011
theorem B2320043 : Blo 1545470 2320043 := bstep (se 1 (by rfl) ⟨1740032, by rfl⟩ : syracuseStep 2320043 = 3480065) B3480065
theorem B2320073 : Blo 1545470 2320073 := bstep (se 2 (by rfl) ⟨870027, by rfl⟩ : syracuseStep 2320073 = 1740055) B1740055
theorem B3221291 : Blo 1545470 3221291 := bstep (se 1 (by rfl) ⟨2415968, by rfl⟩ : syracuseStep 3221291 = 4831937) B4831937
theorem B2320187 : Blo 1545470 2320187 := bstep (se 1 (by rfl) ⟨1740140, by rfl⟩ : syracuseStep 2320187 = 3480281) B3480281
theorem B2320247 : Blo 1545470 2320247 := bstep (se 1 (by rfl) ⟨1740185, by rfl⟩ : syracuseStep 2320247 = 3480371) B3480371
theorem B2320271 : Blo 1545470 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B2320313 : Blo 1545470 2320313 := bstep (se 2 (by rfl) ⟨870117, by rfl⟩ : syracuseStep 2320313 = 1740235) B1740235
theorem B1738759 : Blo 1545470 1738759 := bstep (se 1 (by rfl) ⟨1304069, by rfl⟩ : syracuseStep 1738759 = 2608139) B2608139
theorem B2320391 : Blo 1545470 2320391 := bstep (se 1 (by rfl) ⟨1740293, by rfl⟩ : syracuseStep 2320391 = 3480587) B3480587
theorem B5572637 : Blo 1545470 5572637 := bstep (se 3 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 5572637 = 2089739) B2089739
theorem B5220395 : Blo 1545470 5220395 := bstep (se 1 (by rfl) ⟨3915296, by rfl⟩ : syracuseStep 5220395 = 7830593) B7830593
theorem B2320427 : Blo 1545470 2320427 := bstep (se 1 (by rfl) ⟨1740320, by rfl⟩ : syracuseStep 2320427 = 3480641) B3480641
theorem B6604861 : Blo 1545470 6604861 := bstep (se 3 (by rfl) ⟨1238411, by rfl⟩ : syracuseStep 6604861 = 2476823) B2476823
theorem B2320457 : Blo 1545470 2320457 := bstep (se 2 (by rfl) ⟨870171, by rfl⟩ : syracuseStep 2320457 = 1740343) B1740343
theorem B2975891 : Blo 1545470 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B1738939 : Blo 1545470 1738939 := bstep (se 1 (by rfl) ⟨1304204, by rfl⟩ : syracuseStep 1738939 = 2608409) B2608409
theorem B2320571 : Blo 1545470 2320571 := bstep (se 1 (by rfl) ⟨1740428, by rfl⟩ : syracuseStep 2320571 = 3480857) B3480857
theorem B2320631 : Blo 1545470 2320631 := bstep (se 1 (by rfl) ⟨1740473, by rfl⟩ : syracuseStep 2320631 = 3480947) B3480947
theorem B2320655 : Blo 1545470 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B2320697 : Blo 1545470 2320697 := bstep (se 2 (by rfl) ⟨870261, by rfl⟩ : syracuseStep 2320697 = 1740523) B1740523
theorem B2320775 : Blo 1545470 2320775 := bstep (se 1 (by rfl) ⟨1740581, by rfl⟩ : syracuseStep 2320775 = 3481163) B3481163
theorem B2320811 : Blo 1545470 2320811 := bstep (se 1 (by rfl) ⟨1740608, by rfl⟩ : syracuseStep 2320811 = 3481217) B3481217
theorem B2320841 : Blo 1545470 2320841 := bstep (se 2 (by rfl) ⟨870315, by rfl⟩ : syracuseStep 2320841 = 1740631) B1740631
theorem B2320955 : Blo 1545470 2320955 := bstep (se 1 (by rfl) ⟨1740716, by rfl⟩ : syracuseStep 2320955 = 3481433) B3481433
theorem B13208183 : Blo 1545470 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B2321015 : Blo 1545470 2321015 := bstep (se 1 (by rfl) ⟨1740761, by rfl⟩ : syracuseStep 2321015 = 3481523) B3481523
theorem B1739407 : Blo 1545470 1739407 := bstep (se 1 (by rfl) ⟨1304555, by rfl⟩ : syracuseStep 1739407 = 2609111) B2609111
theorem B2321039 : Blo 1545470 2321039 := bstep (se 1 (by rfl) ⟨1740779, by rfl⟩ : syracuseStep 2321039 = 3481559) B3481559
theorem B2321081 : Blo 1545470 2321081 := bstep (se 2 (by rfl) ⟨870405, by rfl⟩ : syracuseStep 2321081 = 1740811) B1740811
theorem B5573357 : Blo 1545470 5573357 := bstep (se 3 (by rfl) ⟨1045004, by rfl⟩ : syracuseStep 5573357 = 2090009) B2090009
theorem B2321159 : Blo 1545470 2321159 := bstep (se 1 (by rfl) ⟨1740869, by rfl⟩ : syracuseStep 2321159 = 3481739) B3481739
theorem B2321195 : Blo 1545470 2321195 := bstep (se 1 (by rfl) ⟨1740896, by rfl⟩ : syracuseStep 2321195 = 3481793) B3481793
theorem B36211799 : Blo 1545470 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B2608247 : Blo 1545470 2608247 := bstep (se 1 (by rfl) ⟨1956185, by rfl⟩ : syracuseStep 2608247 = 3912371) B3912371
theorem B4402295 : Blo 1545470 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B1739911 : Blo 1545470 1739911 := bstep (se 1 (by rfl) ⟨1304933, by rfl⟩ : syracuseStep 1739911 = 2609867) B2609867
theorem B1740091 : Blo 1545470 1740091 := bstep (se 1 (by rfl) ⟨1305068, by rfl⟩ : syracuseStep 1740091 = 2610137) B2610137
theorem B5221691 : Blo 1545470 5221691 := bstep (se 1 (by rfl) ⟨3916268, by rfl⟩ : syracuseStep 5221691 = 7832537) B7832537
theorem B19819961 : Blo 1545470 19819961 := bstep (se 2 (by rfl) ⟨7432485, by rfl⟩ : syracuseStep 19819961 = 14864971) B14864971
theorem B10587677 : Blo 1545470 10587677 := bstep (se 3 (by rfl) ⟨1985189, by rfl⟩ : syracuseStep 10587677 = 3970379) B3970379
theorem B2608699 : Blo 1545470 2608699 := bstep (se 1 (by rfl) ⟨1956524, by rfl⟩ : syracuseStep 2608699 = 3913049) B3913049
theorem B2977339 : Blo 1545470 2977339 := bstep (se 1 (by rfl) ⟨2233004, by rfl⟩ : syracuseStep 2977339 = 4466009) B4466009
theorem B7433795 : Blo 1545470 7433795 := bstep (se 1 (by rfl) ⟨5575346, by rfl⟩ : syracuseStep 7433795 = 11150693) B11150693
theorem B22285925 : Blo 1545470 22285925 := bstep (se 4 (by rfl) ⟨2089305, by rfl⟩ : syracuseStep 22285925 = 4178611) B4178611
theorem B39628439 : Blo 1545470 39628439 := bstep (se 1 (by rfl) ⟨29721329, by rfl⟩ : syracuseStep 39628439 = 59442659) B59442659
theorem B2608841 : Blo 1545470 2608841 := bstep (se 2 (by rfl) ⟨978315, by rfl⟩ : syracuseStep 2608841 = 1956631) B1956631
theorem B8359625 : Blo 1545470 8359625 := bstep (se 2 (by rfl) ⟨3134859, by rfl⟩ : syracuseStep 8359625 = 6269719) B6269719
theorem B1740559 : Blo 1545470 1740559 := bstep (se 1 (by rfl) ⟨1305419, by rfl⟩ : syracuseStep 1740559 = 2610839) B2610839
theorem B6115105 : Blo 1545470 6115105 := bstep (se 2 (by rfl) ⟨2293164, by rfl⟩ : syracuseStep 6115105 = 4586329) B4586329
theorem B5222177 : Blo 1545470 5222177 := bstep (se 2 (by rfl) ⟨1958316, by rfl⟩ : syracuseStep 5222177 = 3916633) B3916633
theorem B3714859 : Blo 1545470 3714859 := bstep (se 1 (by rfl) ⟨2786144, by rfl⟩ : syracuseStep 3714859 = 5572289) B5572289
theorem B8802107 : Blo 1545470 8802107 := bstep (se 1 (by rfl) ⟨6601580, by rfl⟩ : syracuseStep 8802107 = 13203161) B13203161
theorem B8810329 : Blo 1545470 8810329 := bstep (se 2 (by rfl) ⟨3303873, by rfl⟩ : syracuseStep 8810329 = 6607747) B6607747
theorem B4353907 : Blo 1545470 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B3477383 : Blo 1545470 3477383 := bstep (se 1 (by rfl) ⟨2608037, by rfl⟩ : syracuseStep 3477383 = 5216075) B5216075
theorem B7827353 : Blo 1545470 7827353 := bstep (se 2 (by rfl) ⟨2935257, by rfl⟩ : syracuseStep 7827353 = 5870515) B5870515
theorem B6606859 : Blo 1545470 6606859 := bstep (se 1 (by rfl) ⟨4955144, by rfl⟩ : syracuseStep 6606859 = 9910289) B9910289
theorem B6271019 : Blo 1545470 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B3477563 : Blo 1545470 3477563 := bstep (se 1 (by rfl) ⟨2608172, by rfl⟩ : syracuseStep 3477563 = 5216345) B5216345
theorem B2936891 : Blo 1545470 2936891 := bstep (se 1 (by rfl) ⟨2202668, by rfl⟩ : syracuseStep 2936891 = 4405337) B4405337
theorem B3715159 : Blo 1545470 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B17617013 : Blo 1545470 17617013 := bstep (se 5 (by rfl) ⟨825797, by rfl⟩ : syracuseStep 17617013 = 1651595) B1651595
theorem B3477689 : Blo 1545470 3477689 := bstep (se 2 (by rfl) ⟨1304133, by rfl⟩ : syracuseStep 3477689 = 2608267) B2608267
theorem B6271291 : Blo 1545470 6271291 := bstep (se 1 (by rfl) ⟨4703468, by rfl⟩ : syracuseStep 6271291 = 9406937) B9406937
theorem B2609543 : Blo 1545470 2609543 := bstep (se 1 (by rfl) ⟨1957157, by rfl⟩ : syracuseStep 2609543 = 3914315) B3914315
theorem B2478521 : Blo 1545470 2478521 := bstep (se 2 (by rfl) ⟨929445, by rfl⟩ : syracuseStep 2478521 = 1858891) B1858891
theorem B3478031 : Blo 1545470 3478031 := bstep (se 1 (by rfl) ⟨2608523, by rfl⟩ : syracuseStep 3478031 = 5217047) B5217047
theorem B3478049 : Blo 1545470 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B2937377 : Blo 1545470 2937377 := bstep (se 2 (by rfl) ⟨1101516, by rfl⟩ : syracuseStep 2937377 = 2203033) B2203033
theorem B8360491 : Blo 1545470 8360491 := bstep (se 1 (by rfl) ⟨6270368, by rfl⟩ : syracuseStep 8360491 = 12540737) B12540737
theorem B8360509 : Blo 1545470 8360509 := bstep (se 3 (by rfl) ⟨1567595, by rfl⟩ : syracuseStep 8360509 = 3135191) B3135191
theorem B8925967 : Blo 1545470 8925967 := bstep (se 1 (by rfl) ⟨6694475, by rfl⟩ : syracuseStep 8925967 = 13388951) B13388951
theorem B3912563 : Blo 1545470 3912563 := bstep (se 1 (by rfl) ⟨2934422, by rfl⟩ : syracuseStep 3912563 = 5868845) B5868845
theorem B3478391 : Blo 1545470 3478391 := bstep (se 1 (by rfl) ⟨2608793, by rfl⟩ : syracuseStep 3478391 = 5217587) B5217587
theorem B3912583 : Blo 1545470 3912583 := bstep (se 1 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 3912583 = 5868875) B5868875
theorem B2610191 : Blo 1545470 2610191 := bstep (se 1 (by rfl) ⟨1957643, by rfl⟩ : syracuseStep 2610191 = 3915287) B3915287
theorem B3478571 : Blo 1545470 3478571 := bstep (se 1 (by rfl) ⟨2608928, by rfl⟩ : syracuseStep 3478571 = 5217857) B5217857
theorem B3912857 : Blo 1545470 3912857 := bstep (se 2 (by rfl) ⟨1467321, by rfl⟩ : syracuseStep 3912857 = 2934643) B2934643
theorem B8803565 : Blo 1545470 8803565 := bstep (se 3 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 8803565 = 3301337) B3301337
theorem B1545479 : Blo 1545470 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B1545487 : Blo 1545470 1545487 := bstep (se 1 (by rfl) ⟨1159115, by rfl⟩ : syracuseStep 1545487 = 2318231) B2318231
theorem B1545531 : Blo 1545470 1545531 := bstep (se 1 (by rfl) ⟨1159148, by rfl⟩ : syracuseStep 1545531 = 2318297) B2318297
theorem B3913019 : Blo 1545470 3913019 := bstep (se 1 (by rfl) ⟨2934764, by rfl⟩ : syracuseStep 3913019 = 5869529) B5869529
theorem B1545607 : Blo 1545470 1545607 := bstep (se 1 (by rfl) ⟨1159205, by rfl⟩ : syracuseStep 1545607 = 2318411) B2318411
theorem B1545615 : Blo 1545470 1545615 := bstep (se 1 (by rfl) ⟨1159211, by rfl⟩ : syracuseStep 1545615 = 2318423) B2318423
theorem B3478931 : Blo 1545470 3478931 := bstep (se 1 (by rfl) ⟨2609198, by rfl⟩ : syracuseStep 3478931 = 5218397) B5218397
theorem B5871001 : Blo 1545470 5871001 := bstep (se 2 (by rfl) ⟨2201625, by rfl⟩ : syracuseStep 5871001 = 4403251) B4403251
theorem B5952953 : Blo 1545470 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B1545659 : Blo 1545470 1545659 := bstep (se 1 (by rfl) ⟨1159244, by rfl⟩ : syracuseStep 1545659 = 2318489) B2318489
theorem B3478985 : Blo 1545470 3478985 := bstep (se 2 (by rfl) ⟨1304619, by rfl⟩ : syracuseStep 3478985 = 2609239) B2609239
theorem B1545735 : Blo 1545470 1545735 := bstep (se 1 (by rfl) ⟨1159301, by rfl⟩ : syracuseStep 1545735 = 2318603) B2318603
theorem B1545743 : Blo 1545470 1545743 := bstep (se 1 (by rfl) ⟨1159307, by rfl⟩ : syracuseStep 1545743 = 2318615) B2318615
theorem B3913231 : Blo 1545470 3913231 := bstep (se 1 (by rfl) ⟨2934923, by rfl⟩ : syracuseStep 3913231 = 5869847) B5869847
theorem B8812061 : Blo 1545470 8812061 := bstep (se 3 (by rfl) ⟨1652261, by rfl⟩ : syracuseStep 8812061 = 3304523) B3304523
theorem B2610731 : Blo 1545470 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B1545787 : Blo 1545470 1545787 := bstep (se 1 (by rfl) ⟨1159340, by rfl⟩ : syracuseStep 1545787 = 2318681) B2318681
theorem B7427645 : Blo 1545470 7427645 := bstep (se 3 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 7427645 = 2785367) B2785367
theorem B1545863 : Blo 1545470 1545863 := bstep (se 1 (by rfl) ⟨1159397, by rfl⟩ : syracuseStep 1545863 = 2318795) B2318795
theorem B1545871 : Blo 1545470 1545871 := bstep (se 1 (by rfl) ⟨1159403, by rfl⟩ : syracuseStep 1545871 = 2318807) B2318807
theorem B33453719 : Blo 1545470 33453719 := bstep (se 1 (by rfl) ⟨25090289, by rfl⟩ : syracuseStep 33453719 = 50180579) B50180579
theorem B1545915 : Blo 1545470 1545915 := bstep (se 1 (by rfl) ⟨1159436, by rfl⟩ : syracuseStep 1545915 = 2318873) B2318873
theorem B5871305 : Blo 1545470 5871305 := bstep (se 2 (by rfl) ⟨2201739, by rfl⟩ : syracuseStep 5871305 = 4403479) B4403479
theorem B4404937 : Blo 1545470 4404937 := bstep (se 2 (by rfl) ⟨1651851, by rfl⟩ : syracuseStep 4404937 = 3303703) B3303703
theorem B1545991 : Blo 1545470 1545991 := bstep (se 1 (by rfl) ⟨1159493, by rfl⟩ : syracuseStep 1545991 = 2318987) B2318987
theorem B1545999 : Blo 1545470 1545999 := bstep (se 1 (by rfl) ⟨1159499, by rfl⟩ : syracuseStep 1545999 = 2318999) B2318999
theorem B3913505 : Blo 1545470 3913505 := bstep (se 2 (by rfl) ⟨1467564, by rfl⟩ : syracuseStep 3913505 = 2935129) B2935129
theorem B4953889 : Blo 1545470 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B1546043 : Blo 1545470 1546043 := bstep (se 1 (by rfl) ⟨1159532, by rfl⟩ : syracuseStep 1546043 = 2319065) B2319065
theorem B1546119 : Blo 1545470 1546119 := bstep (se 1 (by rfl) ⟨1159589, by rfl⟩ : syracuseStep 1546119 = 2319179) B2319179
theorem B1546127 : Blo 1545470 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B7436177 : Blo 1545470 7436177 := bstep (se 2 (by rfl) ⟨2788566, by rfl⟩ : syracuseStep 7436177 = 5577133) B5577133
theorem B2611129 : Blo 1545470 2611129 := bstep (se 2 (by rfl) ⟨979173, by rfl⟩ : syracuseStep 2611129 = 1958347) B1958347
theorem B1546171 : Blo 1545470 1546171 := bstep (se 1 (by rfl) ⟨1159628, by rfl⟩ : syracuseStep 1546171 = 2319257) B2319257
theorem B6272977 : Blo 1545470 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B1546247 : Blo 1545470 1546247 := bstep (se 1 (by rfl) ⟨1159685, by rfl⟩ : syracuseStep 1546247 = 2319371) B2319371
theorem B1546255 : Blo 1545470 1546255 := bstep (se 1 (by rfl) ⟨1159691, by rfl⟩ : syracuseStep 1546255 = 2319383) B2319383
theorem B1546299 : Blo 1545470 1546299 := bstep (se 1 (by rfl) ⟨1159724, by rfl⟩ : syracuseStep 1546299 = 2319449) B2319449
theorem B1546375 : Blo 1545470 1546375 := bstep (se 1 (by rfl) ⟨1159781, by rfl⟩ : syracuseStep 1546375 = 2319563) B2319563
theorem B3479687 : Blo 1545470 3479687 := bstep (se 1 (by rfl) ⟨2609765, by rfl⟩ : syracuseStep 3479687 = 5219531) B5219531
theorem B1546383 : Blo 1545470 1546383 := bstep (se 1 (by rfl) ⟨1159787, by rfl⟩ : syracuseStep 1546383 = 2319575) B2319575
theorem B1546427 : Blo 1545470 1546427 := bstep (se 1 (by rfl) ⟨1159820, by rfl⟩ : syracuseStep 1546427 = 2319641) B2319641
theorem B8812745 : Blo 1545470 8812745 := bstep (se 2 (by rfl) ⟨3304779, by rfl⟩ : syracuseStep 8812745 = 6609559) B6609559
theorem B1546503 : Blo 1545470 1546503 := bstep (se 1 (by rfl) ⟨1159877, by rfl⟩ : syracuseStep 1546503 = 2319755) B2319755
theorem B1546511 : Blo 1545470 1546511 := bstep (se 1 (by rfl) ⟨1159883, by rfl⟩ : syracuseStep 1546511 = 2319767) B2319767
theorem B2201899 : Blo 1545470 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B1546555 : Blo 1545470 1546555 := bstep (se 1 (by rfl) ⟨1159916, by rfl⟩ : syracuseStep 1546555 = 2319833) B2319833
theorem B3479867 : Blo 1545470 3479867 := bstep (se 1 (by rfl) ⟨2609900, by rfl⟩ : syracuseStep 3479867 = 5219801) B5219801
theorem B4700551 : Blo 1545470 4700551 := bstep (se 1 (by rfl) ⟨3525413, by rfl⟩ : syracuseStep 4700551 = 7050827) B7050827
theorem B1546631 : Blo 1545470 1546631 := bstep (se 1 (by rfl) ⟨1159973, by rfl⟩ : syracuseStep 1546631 = 2319947) B2319947
theorem B1546639 : Blo 1545470 1546639 := bstep (se 1 (by rfl) ⟨1159979, by rfl⟩ : syracuseStep 1546639 = 2319959) B2319959
theorem B7829945 : Blo 1545470 7829945 := bstep (se 2 (by rfl) ⟨2936229, by rfl⟩ : syracuseStep 7829945 = 5872459) B5872459
theorem B3479993 : Blo 1545470 3479993 := bstep (se 2 (by rfl) ⟨1304997, by rfl⟩ : syracuseStep 3479993 = 2609995) B2609995
theorem B1546683 : Blo 1545470 1546683 := bstep (se 1 (by rfl) ⟨1160012, by rfl⟩ : syracuseStep 1546683 = 2320025) B2320025
theorem B1546759 : Blo 1545470 1546759 := bstep (se 1 (by rfl) ⟨1160069, by rfl⟩ : syracuseStep 1546759 = 2320139) B2320139
theorem B1546767 : Blo 1545470 1546767 := bstep (se 1 (by rfl) ⟨1160075, by rfl⟩ : syracuseStep 1546767 = 2320151) B2320151
theorem B1546811 : Blo 1545470 1546811 := bstep (se 1 (by rfl) ⟨1160108, by rfl⟩ : syracuseStep 1546811 = 2320217) B2320217
theorem B19806839 : Blo 1545470 19806839 := bstep (se 1 (by rfl) ⟨14855129, by rfl⟩ : syracuseStep 19806839 = 29710259) B29710259
theorem B5872247 : Blo 1545470 5872247 := bstep (se 1 (by rfl) ⟨4404185, by rfl⟩ : syracuseStep 5872247 = 8808371) B8808371
theorem B1546887 : Blo 1545470 1546887 := bstep (se 1 (by rfl) ⟨1160165, by rfl⟩ : syracuseStep 1546887 = 2320331) B2320331
theorem B1546895 : Blo 1545470 1546895 := bstep (se 1 (by rfl) ⟨1160171, by rfl⟩ : syracuseStep 1546895 = 2320343) B2320343
theorem B1546939 : Blo 1545470 1546939 := bstep (se 1 (by rfl) ⟨1160204, by rfl⟩ : syracuseStep 1546939 = 2320409) B2320409
theorem B1547015 : Blo 1545470 1547015 := bstep (se 1 (by rfl) ⟨1160261, by rfl⟩ : syracuseStep 1547015 = 2320523) B2320523
theorem B3914507 : Blo 1545470 3914507 := bstep (se 1 (by rfl) ⟨2935880, by rfl⟩ : syracuseStep 3914507 = 5871761) B5871761
theorem B11737871 : Blo 1545470 11737871 := bstep (se 1 (by rfl) ⟨8803403, by rfl⟩ : syracuseStep 11737871 = 17606807) B17606807
theorem B3480335 : Blo 1545470 3480335 := bstep (se 1 (by rfl) ⟨2610251, by rfl⟩ : syracuseStep 3480335 = 5220503) B5220503
theorem B7535375 : Blo 1545470 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B1547023 : Blo 1545470 1547023 := bstep (se 1 (by rfl) ⟨1160267, by rfl⟩ : syracuseStep 1547023 = 2320535) B2320535
theorem B3480353 : Blo 1545470 3480353 := bstep (se 2 (by rfl) ⟨1305132, by rfl⟩ : syracuseStep 3480353 = 2610265) B2610265
theorem B1547067 : Blo 1545470 1547067 := bstep (se 1 (by rfl) ⟨1160300, by rfl⟩ : syracuseStep 1547067 = 2320601) B2320601
theorem B3718003 : Blo 1545470 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B1956727 : Blo 1545470 1956727 := bstep (se 1 (by rfl) ⟨1467545, by rfl⟩ : syracuseStep 1956727 = 2935091) B2935091
theorem B1547143 : Blo 1545470 1547143 := bstep (se 1 (by rfl) ⟨1160357, by rfl⟩ : syracuseStep 1547143 = 2320715) B2320715
theorem B1547151 : Blo 1545470 1547151 := bstep (se 1 (by rfl) ⟨1160363, by rfl⟩ : syracuseStep 1547151 = 2320727) B2320727
theorem B5217209 : Blo 1545470 5217209 := bstep (se 2 (by rfl) ⟨1956453, by rfl⟩ : syracuseStep 5217209 = 3912907) B3912907
theorem B3136441 : Blo 1545470 3136441 := bstep (se 2 (by rfl) ⟨1176165, by rfl⟩ : syracuseStep 3136441 = 2352331) B2352331
theorem B1547195 : Blo 1545470 1547195 := bstep (se 1 (by rfl) ⟨1160396, by rfl⟩ : syracuseStep 1547195 = 2320793) B2320793
theorem B1547271 : Blo 1545470 1547271 := bstep (se 1 (by rfl) ⟨1160453, by rfl⟩ : syracuseStep 1547271 = 2320907) B2320907
theorem B1547279 : Blo 1545470 1547279 := bstep (se 1 (by rfl) ⟨1160459, by rfl⟩ : syracuseStep 1547279 = 2320919) B2320919
theorem B1547323 : Blo 1545470 1547323 := bstep (se 1 (by rfl) ⟨1160492, by rfl⟩ : syracuseStep 1547323 = 2320985) B2320985
theorem B8928317 : Blo 1545470 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B3480695 : Blo 1545470 3480695 := bstep (se 1 (by rfl) ⟨2610521, by rfl⟩ : syracuseStep 3480695 = 5221043) B5221043
theorem B1547399 : Blo 1545470 1547399 := bstep (se 1 (by rfl) ⟨1160549, by rfl⟩ : syracuseStep 1547399 = 2321099) B2321099
theorem B1547407 : Blo 1545470 1547407 := bstep (se 1 (by rfl) ⟨1160555, by rfl⟩ : syracuseStep 1547407 = 2321111) B2321111
theorem B1957051 : Blo 1545470 1957051 := bstep (se 1 (by rfl) ⟨1467788, by rfl⟩ : syracuseStep 1957051 = 2935577) B2935577
theorem B1547451 : Blo 1545470 1547451 := bstep (se 1 (by rfl) ⟨1160588, by rfl⟩ : syracuseStep 1547451 = 2321177) B2321177
theorem B3480875 : Blo 1545470 3480875 := bstep (se 1 (by rfl) ⟨2610656, by rfl⟩ : syracuseStep 3480875 = 5221313) B5221313
theorem B35691835 : Blo 1545470 35691835 := bstep (se 1 (by rfl) ⟨26768876, by rfl⟩ : syracuseStep 35691835 = 53537753) B53537753
theorem B11746619 : Blo 1545470 11746619 := bstep (se 1 (by rfl) ⟨8809964, by rfl⟩ : syracuseStep 11746619 = 17619929) B17619929
theorem B11140487 : Blo 1545470 11140487 := bstep (se 1 (by rfl) ⟨8355365, by rfl⟩ : syracuseStep 11140487 = 16710731) B16710731
theorem B3915155 : Blo 1545470 3915155 := bstep (se 1 (by rfl) ⟨2936366, by rfl⟩ : syracuseStep 3915155 = 5872733) B5872733
theorem B33430961 : Blo 1545470 33430961 := bstep (se 2 (by rfl) ⟨12536610, by rfl⟩ : syracuseStep 33430961 = 25073221) B25073221
theorem B5217803 : Blo 1545470 5217803 := bstep (se 1 (by rfl) ⟨3913352, by rfl⟩ : syracuseStep 5217803 = 7826705) B7826705
theorem B7429643 : Blo 1545470 7429643 := bstep (se 1 (by rfl) ⟨5572232, by rfl⟩ : syracuseStep 7429643 = 11144465) B11144465
theorem B6266429 : Blo 1545470 6266429 := bstep (se 3 (by rfl) ⟨1174955, by rfl⟩ : syracuseStep 6266429 = 2349911) B2349911
theorem B8805955 : Blo 1545470 8805955 := bstep (se 1 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 8805955 = 13208933) B13208933
theorem B5873219 : Blo 1545470 5873219 := bstep (se 1 (by rfl) ⟨4404914, by rfl⟩ : syracuseStep 5873219 = 8809829) B8809829
theorem B4955735 : Blo 1545470 4955735 := bstep (se 1 (by rfl) ⟨3716801, by rfl⟩ : syracuseStep 4955735 = 7433603) B7433603
theorem B114392675 : Blo 1545470 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B5217911 : Blo 1545470 5217911 := bstep (se 1 (by rfl) ⟨3913433, by rfl⟩ : syracuseStep 5217911 = 7826867) B7826867
theorem B3481235 : Blo 1545470 3481235 := bstep (se 1 (by rfl) ⟨2610926, by rfl⟩ : syracuseStep 3481235 = 5221853) B5221853
theorem B1957547 : Blo 1545470 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B3915449 : Blo 1545470 3915449 := bstep (se 2 (by rfl) ⟨1468293, by rfl⟩ : syracuseStep 3915449 = 2936587) B2936587
theorem B7831241 : Blo 1545470 7831241 := bstep (se 2 (by rfl) ⟨2936715, by rfl⟩ : syracuseStep 7831241 = 5873431) B5873431
theorem B3481289 : Blo 1545470 3481289 := bstep (se 2 (by rfl) ⟨1305483, by rfl⟩ : syracuseStep 3481289 = 2610967) B2610967
theorem B2318267 : Blo 1545470 2318267 := bstep (se 1 (by rfl) ⟨1738700, by rfl⟩ : syracuseStep 2318267 = 3477401) B3477401
theorem B2318327 : Blo 1545470 2318327 := bstep (se 1 (by rfl) ⟨1738745, by rfl⟩ : syracuseStep 2318327 = 3477491) B3477491
theorem B6602759 : Blo 1545470 6602759 := bstep (se 1 (by rfl) ⟨4952069, by rfl⟩ : syracuseStep 6602759 = 9904139) B9904139
theorem B2318345 : Blo 1545470 2318345 := bstep (se 2 (by rfl) ⟨869379, by rfl⟩ : syracuseStep 2318345 = 1738759) B1738759
theorem B5292047 : Blo 1545470 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B2318375 : Blo 1545470 2318375 := bstep (se 1 (by rfl) ⟨1738781, by rfl⟩ : syracuseStep 2318375 = 3477563) B3477563
theorem B1957927 : Blo 1545470 1957927 := bstep (se 1 (by rfl) ⟨1468445, by rfl⟩ : syracuseStep 1957927 = 2936891) B2936891
theorem B8806481 : Blo 1545470 8806481 := bstep (se 2 (by rfl) ⟨3302430, by rfl⟩ : syracuseStep 8806481 = 6604861) B6604861
theorem B2318459 : Blo 1545470 2318459 := bstep (se 1 (by rfl) ⟨1738844, by rfl⟩ : syracuseStep 2318459 = 3477689) B3477689
theorem B2318585 : Blo 1545470 2318585 := bstep (se 2 (by rfl) ⟨869469, by rfl⟩ : syracuseStep 2318585 = 1738939) B1738939
theorem B2318687 : Blo 1545470 2318687 := bstep (se 1 (by rfl) ⟨1739015, by rfl⟩ : syracuseStep 2318687 = 3478031) B3478031
theorem B2318699 : Blo 1545470 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1958251 : Blo 1545470 1958251 := bstep (se 1 (by rfl) ⟨1468688, by rfl⟩ : syracuseStep 1958251 = 2937377) B2937377
theorem B2785799 : Blo 1545470 2785799 := bstep (se 1 (by rfl) ⟨2089349, by rfl⟩ : syracuseStep 2785799 = 4178699) B4178699
theorem B6267401 : Blo 1545470 6267401 := bstep (se 2 (by rfl) ⟨2350275, by rfl⟩ : syracuseStep 6267401 = 4700551) B4700551
theorem B2318927 : Blo 1545470 2318927 := bstep (se 1 (by rfl) ⟨1739195, by rfl⟩ : syracuseStep 2318927 = 3478391) B3478391
theorem B2785871 : Blo 1545470 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B2319047 : Blo 1545470 2319047 := bstep (se 1 (by rfl) ⟨1739285, by rfl⟩ : syracuseStep 2319047 = 3478571) B3478571
theorem B5571281 : Blo 1545470 5571281 := bstep (se 2 (by rfl) ⟨2089230, by rfl⟩ : syracuseStep 5571281 = 4178461) B4178461
theorem B7537481 : Blo 1545470 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B2319209 : Blo 1545470 2319209 := bstep (se 2 (by rfl) ⟨869703, by rfl⟩ : syracuseStep 2319209 = 1739407) B1739407
theorem B2319287 : Blo 1545470 2319287 := bstep (se 1 (by rfl) ⟨1739465, by rfl⟩ : syracuseStep 2319287 = 3478931) B3478931
theorem B2319323 : Blo 1545470 2319323 := bstep (se 1 (by rfl) ⟨1739492, by rfl⟩ : syracuseStep 2319323 = 3478985) B3478985
theorem B19809299 : Blo 1545470 19809299 := bstep (se 1 (by rfl) ⟨14856974, by rfl⟩ : syracuseStep 19809299 = 29713949) B29713949
theorem B5874707 : Blo 1545470 5874707 := bstep (se 1 (by rfl) ⟨4406030, by rfl⟩ : syracuseStep 5874707 = 8812061) B8812061
theorem B4957337 : Blo 1545470 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B4957451 : Blo 1545470 4957451 := bstep (se 1 (by rfl) ⟨3718088, by rfl⟩ : syracuseStep 4957451 = 7436177) B7436177
theorem B2319791 : Blo 1545470 2319791 := bstep (se 1 (by rfl) ⟨1739843, by rfl⟩ : syracuseStep 2319791 = 3479687) B3479687
theorem B5875163 : Blo 1545470 5875163 := bstep (se 1 (by rfl) ⟨4406372, by rfl⟩ : syracuseStep 5875163 = 8812745) B8812745
theorem B2319881 : Blo 1545470 2319881 := bstep (se 2 (by rfl) ⟨869955, by rfl⟩ : syracuseStep 2319881 = 1739911) B1739911
theorem B2319911 : Blo 1545470 2319911 := bstep (se 1 (by rfl) ⟨1739933, by rfl⟩ : syracuseStep 2319911 = 3479867) B3479867
theorem B7833185 : Blo 1545470 7833185 := bstep (se 2 (by rfl) ⟨2937444, by rfl⟩ : syracuseStep 7833185 = 5874889) B5874889
theorem B5219963 : Blo 1545470 5219963 := bstep (se 1 (by rfl) ⟨3914972, by rfl⟩ : syracuseStep 5219963 = 7829945) B7829945
theorem B2319995 : Blo 1545470 2319995 := bstep (se 1 (by rfl) ⟨1739996, by rfl⟩ : syracuseStep 2319995 = 3479993) B3479993
theorem B7825085 : Blo 1545470 7825085 := bstep (se 3 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 7825085 = 2934407) B2934407
theorem B47589113 : Blo 1545470 47589113 := bstep (se 2 (by rfl) ⟨17845917, by rfl⟩ : syracuseStep 47589113 = 35691835) B35691835
theorem B2320121 : Blo 1545470 2320121 := bstep (se 2 (by rfl) ⟨870045, by rfl⟩ : syracuseStep 2320121 = 1740091) B1740091
theorem B5220125 : Blo 1545470 5220125 := bstep (se 3 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 5220125 = 1957547) B1957547
theorem B7825247 : Blo 1545470 7825247 := bstep (se 1 (by rfl) ⟨5868935, by rfl⟩ : syracuseStep 7825247 = 11737871) B11737871
theorem B2320223 : Blo 1545470 2320223 := bstep (se 1 (by rfl) ⟨1740167, by rfl⟩ : syracuseStep 2320223 = 3480335) B3480335
theorem B5023583 : Blo 1545470 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B2320235 : Blo 1545470 2320235 := bstep (se 1 (by rfl) ⟨1740176, by rfl⟩ : syracuseStep 2320235 = 3480353) B3480353
theorem B22292333 : Blo 1545470 22292333 := bstep (se 3 (by rfl) ⟨4179812, by rfl⟩ : syracuseStep 22292333 = 8359625) B8359625
theorem B2787385 : Blo 1545470 2787385 := bstep (se 2 (by rfl) ⟨1045269, by rfl⟩ : syracuseStep 2787385 = 2090539) B2090539
theorem B1738831 : Blo 1545470 1738831 := bstep (se 1 (by rfl) ⟨1304123, by rfl⟩ : syracuseStep 1738831 = 2608247) B2608247
theorem B2934863 : Blo 1545470 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B2320463 : Blo 1545470 2320463 := bstep (se 1 (by rfl) ⟨1740347, by rfl⟩ : syracuseStep 2320463 = 3480695) B3480695
theorem B11741273 : Blo 1545470 11741273 := bstep (se 2 (by rfl) ⟨4402977, by rfl⟩ : syracuseStep 11741273 = 8805955) B8805955
theorem B2320583 : Blo 1545470 2320583 := bstep (se 1 (by rfl) ⟨1740437, by rfl⟩ : syracuseStep 2320583 = 3480875) B3480875
theorem B5572925 : Blo 1545470 5572925 := bstep (se 3 (by rfl) ⟨1044923, by rfl⟩ : syracuseStep 5572925 = 2089847) B2089847
theorem B2320745 : Blo 1545470 2320745 := bstep (se 2 (by rfl) ⟨870279, by rfl⟩ : syracuseStep 2320745 = 1740559) B1740559
theorem B6605185 : Blo 1545470 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B8153473 : Blo 1545470 8153473 := bstep (se 2 (by rfl) ⟨3057552, by rfl⟩ : syracuseStep 8153473 = 6115105) B6115105
theorem B3303823 : Blo 1545470 3303823 := bstep (se 1 (by rfl) ⟨2477867, by rfl⟩ : syracuseStep 3303823 = 4955735) B4955735
theorem B76261783 : Blo 1545470 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B2320823 : Blo 1545470 2320823 := bstep (se 1 (by rfl) ⟨1740617, by rfl⟩ : syracuseStep 2320823 = 3481235) B3481235
theorem B1739227 : Blo 1545470 1739227 := bstep (se 1 (by rfl) ⟨1304420, by rfl⟩ : syracuseStep 1739227 = 2608841) B2608841
theorem B5220827 : Blo 1545470 5220827 := bstep (se 1 (by rfl) ⟨3915620, by rfl⟩ : syracuseStep 5220827 = 7831241) B7831241
theorem B2320859 : Blo 1545470 2320859 := bstep (se 1 (by rfl) ⟨1740644, by rfl⟩ : syracuseStep 2320859 = 3481289) B3481289
theorem B5868071 : Blo 1545470 5868071 := bstep (se 1 (by rfl) ⟨4401053, by rfl⟩ : syracuseStep 5868071 = 8802107) B8802107
theorem B8809145 : Blo 1545470 8809145 := bstep (se 2 (by rfl) ⟨3303429, by rfl⟩ : syracuseStep 8809145 = 6606859) B6606859
theorem B4180679 : Blo 1545470 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B44575433 : Blo 1545470 44575433 := bstep (se 2 (by rfl) ⟨16715787, by rfl⟩ : syracuseStep 44575433 = 33431575) B33431575
theorem B10037969 : Blo 1545470 10037969 := bstep (se 2 (by rfl) ⟨3764238, by rfl⟩ : syracuseStep 10037969 = 7528477) B7528477
theorem B12544723 : Blo 1545470 12544723 := bstep (se 1 (by rfl) ⟨9408542, by rfl⟩ : syracuseStep 12544723 = 18817085) B18817085
theorem B3304147 : Blo 1545470 3304147 := bstep (se 1 (by rfl) ⟨2478110, by rfl⟩ : syracuseStep 3304147 = 4956221) B4956221
theorem B12544915 : Blo 1545470 12544915 := bstep (se 1 (by rfl) ⟨9408686, by rfl⟩ : syracuseStep 12544915 = 18817373) B18817373
theorem B1739695 : Blo 1545470 1739695 := bstep (se 1 (by rfl) ⟨1304771, by rfl⟩ : syracuseStep 1739695 = 2609543) B2609543
theorem B9399347 : Blo 1545470 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B2935865 : Blo 1545470 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B5221529 : Blo 1545470 5221529 := bstep (se 2 (by rfl) ⟨1958073, by rfl⟩ : syracuseStep 5221529 = 3916147) B3916147
theorem B2608375 : Blo 1545470 2608375 := bstep (se 1 (by rfl) ⟨1956281, by rfl⟩ : syracuseStep 2608375 = 3912563) B3912563
theorem B1740127 : Blo 1545470 1740127 := bstep (se 1 (by rfl) ⟨1305095, by rfl⟩ : syracuseStep 1740127 = 2610191) B2610191
theorem B2608571 : Blo 1545470 2608571 := bstep (se 1 (by rfl) ⟨1956428, by rfl⟩ : syracuseStep 2608571 = 3912857) B3912857
theorem B5869043 : Blo 1545470 5869043 := bstep (se 1 (by rfl) ⟨4401782, by rfl⟩ : syracuseStep 5869043 = 8803565) B8803565
theorem B11742731 : Blo 1545470 11742731 := bstep (se 1 (by rfl) ⟨8807048, by rfl⟩ : syracuseStep 11742731 = 17614097) B17614097
theorem B2608679 : Blo 1545470 2608679 := bstep (se 1 (by rfl) ⟨1956509, by rfl⟩ : syracuseStep 2608679 = 3913019) B3913019
theorem B3968635 : Blo 1545470 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1740487 : Blo 1545470 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B4951763 : Blo 1545470 4951763 := bstep (se 1 (by rfl) ⟨3713822, by rfl⟩ : syracuseStep 4951763 = 7427645) B7427645
theorem B22302479 : Blo 1545470 22302479 := bstep (se 1 (by rfl) ⟨16726859, by rfl⟩ : syracuseStep 22302479 = 33453719) B33453719
theorem B2608969 : Blo 1545470 2608969 := bstep (se 2 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 2608969 = 1956727) B1956727
theorem B2609003 : Blo 1545470 2609003 := bstep (se 1 (by rfl) ⟨1956752, by rfl⟩ : syracuseStep 2609003 = 3913505) B3913505
theorem B4181921 : Blo 1545470 4181921 := bstep (se 2 (by rfl) ⟨1568220, by rfl⟩ : syracuseStep 4181921 = 3136441) B3136441
theorem B3715091 : Blo 1545470 3715091 := bstep (se 1 (by rfl) ⟨2786318, by rfl⟩ : syracuseStep 3715091 = 5572637) B5572637
theorem B28233805 : Blo 1545470 28233805 := bstep (se 3 (by rfl) ⟨5293838, by rfl⟩ : syracuseStep 28233805 = 10587677) B10587677
theorem B2609401 : Blo 1545470 2609401 := bstep (se 2 (by rfl) ⟨978525, by rfl⟩ : syracuseStep 2609401 = 1957051) B1957051
theorem B144880001 : Blo 1545470 144880001 := bstep (se 2 (by rfl) ⟨54330000, by rfl⟩ : syracuseStep 144880001 = 108660001) B108660001
theorem B3715571 : Blo 1545470 3715571 := bstep (se 1 (by rfl) ⟨2786678, by rfl⟩ : syracuseStep 3715571 = 5573357) B5573357
theorem B2609671 : Blo 1545470 2609671 := bstep (se 1 (by rfl) ⟨1957253, by rfl⟩ : syracuseStep 2609671 = 3914507) B3914507
theorem B7828001 : Blo 1545470 7828001 := bstep (se 2 (by rfl) ⟨2935500, by rfl⟩ : syracuseStep 7828001 = 5871001) B5871001
theorem B3478139 : Blo 1545470 3478139 := bstep (se 1 (by rfl) ⟨2608604, by rfl⟩ : syracuseStep 3478139 = 5217209) B5217209
theorem B5952211 : Blo 1545470 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B3478265 : Blo 1545470 3478265 := bstep (se 2 (by rfl) ⟨1304349, by rfl⟩ : syracuseStep 3478265 = 2608699) B2608699
theorem B3969785 : Blo 1545470 3969785 := bstep (se 2 (by rfl) ⟨1488669, by rfl⟩ : syracuseStep 3969785 = 2977339) B2977339
theorem B8590109 : Blo 1545470 8590109 := bstep (se 3 (by rfl) ⟨1610645, by rfl⟩ : syracuseStep 8590109 = 3221291) B3221291
theorem B338768729 : Blo 1545470 338768729 := bstep (se 2 (by rfl) ⟨127038273, by rfl⟩ : syracuseStep 338768729 = 254076547) B254076547
theorem B7426991 : Blo 1545470 7426991 := bstep (se 1 (by rfl) ⟨5570243, by rfl⟩ : syracuseStep 7426991 = 11140487) B11140487
theorem B2610103 : Blo 1545470 2610103 := bstep (se 1 (by rfl) ⟨1957577, by rfl⟩ : syracuseStep 2610103 = 3915155) B3915155
theorem B22287307 : Blo 1545470 22287307 := bstep (se 1 (by rfl) ⟨16715480, by rfl⟩ : syracuseStep 22287307 = 33430961) B33430961
theorem B3478535 : Blo 1545470 3478535 := bstep (se 1 (by rfl) ⟨2608901, by rfl⟩ : syracuseStep 3478535 = 5217803) B5217803
theorem B4953095 : Blo 1545470 4953095 := bstep (se 1 (by rfl) ⟨3714821, by rfl⟩ : syracuseStep 4953095 = 7429643) B7429643
theorem B4953145 : Blo 1545470 4953145 := bstep (se 2 (by rfl) ⟨1857429, by rfl⟩ : syracuseStep 4953145 = 3714859) B3714859
theorem B14857283 : Blo 1545470 14857283 := bstep (se 1 (by rfl) ⟨11142962, by rfl⟩ : syracuseStep 14857283 = 22285925) B22285925
theorem B3478607 : Blo 1545470 3478607 := bstep (se 1 (by rfl) ⟨2608955, by rfl⟩ : syracuseStep 3478607 = 5217911) B5217911
theorem B2610299 : Blo 1545470 2610299 := bstep (se 1 (by rfl) ⟨1957724, by rfl⟩ : syracuseStep 2610299 = 3915449) B3915449
theorem B5805209 : Blo 1545470 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B1545511 : Blo 1545470 1545511 := bstep (se 1 (by rfl) ⟨1159133, by rfl⟩ : syracuseStep 1545511 = 2318267) B2318267
theorem B1545551 : Blo 1545470 1545551 := bstep (se 1 (by rfl) ⟨1159163, by rfl⟩ : syracuseStep 1545551 = 2318327) B2318327
theorem B1545567 : Blo 1545470 1545567 := bstep (se 1 (by rfl) ⟨1159175, by rfl⟩ : syracuseStep 1545567 = 2318351) B2318351
theorem B1545595 : Blo 1545470 1545595 := bstep (se 1 (by rfl) ⟨1159196, by rfl⟩ : syracuseStep 1545595 = 2318393) B2318393
theorem B11744675 : Blo 1545470 11744675 := bstep (se 1 (by rfl) ⟨8808506, by rfl⟩ : syracuseStep 11744675 = 17617013) B17617013
theorem B1545647 : Blo 1545470 1545647 := bstep (se 1 (by rfl) ⟨1159235, by rfl⟩ : syracuseStep 1545647 = 2318471) B2318471
theorem B1545671 : Blo 1545470 1545671 := bstep (se 1 (by rfl) ⟨1159253, by rfl⟩ : syracuseStep 1545671 = 2318507) B2318507
theorem B4953545 : Blo 1545470 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B1545691 : Blo 1545470 1545691 := bstep (se 1 (by rfl) ⟨1159268, by rfl⟩ : syracuseStep 1545691 = 2318537) B2318537
theorem B3479003 : Blo 1545470 3479003 := bstep (se 1 (by rfl) ⟨2609252, by rfl⟩ : syracuseStep 3479003 = 5218505) B5218505
theorem B2610697 : Blo 1545470 2610697 := bstep (se 2 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 2610697 = 1958023) B1958023
theorem B1545767 : Blo 1545470 1545767 := bstep (se 1 (by rfl) ⟨1159325, by rfl⟩ : syracuseStep 1545767 = 2318651) B2318651
theorem B1545807 : Blo 1545470 1545807 := bstep (se 1 (by rfl) ⟨1159355, by rfl⟩ : syracuseStep 1545807 = 2318711) B2318711
theorem B1545823 : Blo 1545470 1545823 := bstep (se 1 (by rfl) ⟨1159367, by rfl⟩ : syracuseStep 1545823 = 2318735) B2318735
theorem B1545851 : Blo 1545470 1545851 := bstep (se 1 (by rfl) ⟨1159388, by rfl⟩ : syracuseStep 1545851 = 2318777) B2318777
theorem B1652347 : Blo 1545470 1652347 := bstep (se 1 (by rfl) ⟨1239260, by rfl⟩ : syracuseStep 1652347 = 2478521) B2478521
theorem B5576327 : Blo 1545470 5576327 := bstep (se 1 (by rfl) ⟨4182245, by rfl⟩ : syracuseStep 5576327 = 8364491) B8364491
theorem B1545903 : Blo 1545470 1545903 := bstep (se 1 (by rfl) ⟨1159427, by rfl⟩ : syracuseStep 1545903 = 2318855) B2318855
theorem B2610859 : Blo 1545470 2610859 := bstep (se 1 (by rfl) ⟨1958144, by rfl⟩ : syracuseStep 2610859 = 3916289) B3916289
theorem B1545927 : Blo 1545470 1545927 := bstep (se 1 (by rfl) ⟨1159445, by rfl⟩ : syracuseStep 1545927 = 2318891) B2318891
theorem B1545947 : Blo 1545470 1545947 := bstep (se 1 (by rfl) ⟨1159460, by rfl⟩ : syracuseStep 1545947 = 2318921) B2318921
theorem B8361721 : Blo 1545470 8361721 := bstep (se 2 (by rfl) ⟨3135645, by rfl⟩ : syracuseStep 8361721 = 6271291) B6271291
theorem B1546023 : Blo 1545470 1546023 := bstep (se 1 (by rfl) ⟨1159517, by rfl⟩ : syracuseStep 1546023 = 2319035) B2319035
theorem B11736899 : Blo 1545470 11736899 := bstep (se 1 (by rfl) ⟨8802674, by rfl⟩ : syracuseStep 11736899 = 17605349) B17605349
theorem B1546063 : Blo 1545470 1546063 := bstep (se 1 (by rfl) ⟨1159547, by rfl⟩ : syracuseStep 1546063 = 2319095) B2319095
theorem B1546079 : Blo 1545470 1546079 := bstep (se 1 (by rfl) ⟨1159559, by rfl⟩ : syracuseStep 1546079 = 2319119) B2319119
theorem B5576543 : Blo 1545470 5576543 := bstep (se 1 (by rfl) ⟨4182407, by rfl⟩ : syracuseStep 5576543 = 8364815) B8364815
theorem B1546107 : Blo 1545470 1546107 := bstep (se 1 (by rfl) ⟨1159580, by rfl⟩ : syracuseStep 1546107 = 2319161) B2319161
theorem B1546159 : Blo 1545470 1546159 := bstep (se 1 (by rfl) ⟨1159619, by rfl⟩ : syracuseStep 1546159 = 2319239) B2319239
theorem B3479471 : Blo 1545470 3479471 := bstep (se 1 (by rfl) ⟨2609603, by rfl⟩ : syracuseStep 3479471 = 5219207) B5219207
theorem B5216183 : Blo 1545470 5216183 := bstep (se 1 (by rfl) ⟨3912137, by rfl⟩ : syracuseStep 5216183 = 7824275) B7824275
theorem B1546183 : Blo 1545470 1546183 := bstep (se 1 (by rfl) ⟨1159637, by rfl⟩ : syracuseStep 1546183 = 2319275) B2319275
theorem B1546203 : Blo 1545470 1546203 := bstep (se 1 (by rfl) ⟨1159652, by rfl⟩ : syracuseStep 1546203 = 2319305) B2319305
theorem B2611163 : Blo 1545470 2611163 := bstep (se 1 (by rfl) ⟨1958372, by rfl⟩ : syracuseStep 2611163 = 3916745) B3916745
theorem B1546279 : Blo 1545470 1546279 := bstep (se 1 (by rfl) ⟨1159709, by rfl⟩ : syracuseStep 1546279 = 2319419) B2319419
theorem B11147321 : Blo 1545470 11147321 := bstep (se 2 (by rfl) ⟨4180245, by rfl⟩ : syracuseStep 11147321 = 8360491) B8360491
theorem B1546319 : Blo 1545470 1546319 := bstep (se 1 (by rfl) ⟨1159739, by rfl⟩ : syracuseStep 1546319 = 2319479) B2319479
theorem B11147345 : Blo 1545470 11147345 := bstep (se 2 (by rfl) ⟨4180254, by rfl⟩ : syracuseStep 11147345 = 8360509) B8360509
theorem B1546335 : Blo 1545470 1546335 := bstep (se 1 (by rfl) ⟨1159751, by rfl⟩ : syracuseStep 1546335 = 2319503) B2319503
theorem B1546363 : Blo 1545470 1546363 := bstep (se 1 (by rfl) ⟨1159772, by rfl⟩ : syracuseStep 1546363 = 2319545) B2319545
theorem B3479723 : Blo 1545470 3479723 := bstep (se 1 (by rfl) ⟨2609792, by rfl⟩ : syracuseStep 3479723 = 5219585) B5219585
theorem B1546415 : Blo 1545470 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B1546439 : Blo 1545470 1546439 := bstep (se 1 (by rfl) ⟨1159829, by rfl⟩ : syracuseStep 1546439 = 2319659) B2319659
theorem B1546459 : Blo 1545470 1546459 := bstep (se 1 (by rfl) ⟨1159844, by rfl⟩ : syracuseStep 1546459 = 2319689) B2319689
theorem B1546535 : Blo 1545470 1546535 := bstep (se 1 (by rfl) ⟨1159901, by rfl⟩ : syracuseStep 1546535 = 2319803) B2319803
theorem B1546575 : Blo 1545470 1546575 := bstep (se 1 (by rfl) ⟨1159931, by rfl⟩ : syracuseStep 1546575 = 2319863) B2319863
theorem B5871959 : Blo 1545470 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B1546591 : Blo 1545470 1546591 := bstep (se 1 (by rfl) ⟨1159943, by rfl⟩ : syracuseStep 1546591 = 2319887) B2319887
theorem B11901289 : Blo 1545470 11901289 := bstep (se 2 (by rfl) ⟨4462983, by rfl⟩ : syracuseStep 11901289 = 8925967) B8925967
theorem B1546619 : Blo 1545470 1546619 := bstep (se 1 (by rfl) ⟨1159964, by rfl⟩ : syracuseStep 1546619 = 2319929) B2319929
theorem B1546671 : Blo 1545470 1546671 := bstep (se 1 (by rfl) ⟨1160003, by rfl⟩ : syracuseStep 1546671 = 2320007) B2320007
theorem B1546695 : Blo 1545470 1546695 := bstep (se 1 (by rfl) ⟨1160021, by rfl⟩ : syracuseStep 1546695 = 2320043) B2320043
theorem B3914203 : Blo 1545470 3914203 := bstep (se 1 (by rfl) ⟨2935652, by rfl⟩ : syracuseStep 3914203 = 5871305) B5871305
theorem B1546715 : Blo 1545470 1546715 := bstep (se 1 (by rfl) ⟨1160036, by rfl⟩ : syracuseStep 1546715 = 2320073) B2320073
theorem B5216777 : Blo 1545470 5216777 := bstep (se 2 (by rfl) ⟨1956291, by rfl⟩ : syracuseStep 5216777 = 3912583) B3912583
theorem B1546791 : Blo 1545470 1546791 := bstep (se 1 (by rfl) ⟨1160093, by rfl⟩ : syracuseStep 1546791 = 2320187) B2320187
theorem B1546831 : Blo 1545470 1546831 := bstep (se 1 (by rfl) ⟨1160123, by rfl⟩ : syracuseStep 1546831 = 2320247) B2320247
theorem B1546847 : Blo 1545470 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B1546875 : Blo 1545470 1546875 := bstep (se 1 (by rfl) ⟨1160156, by rfl⟩ : syracuseStep 1546875 = 2320313) B2320313
theorem B1546927 : Blo 1545470 1546927 := bstep (se 1 (by rfl) ⟨1160195, by rfl⟩ : syracuseStep 1546927 = 2320391) B2320391
theorem B6609593 : Blo 1545470 6609593 := bstep (se 2 (by rfl) ⟨2478597, by rfl⟩ : syracuseStep 6609593 = 4957195) B4957195
theorem B3480263 : Blo 1545470 3480263 := bstep (se 1 (by rfl) ⟨2610197, by rfl⟩ : syracuseStep 3480263 = 5220395) B5220395
theorem B1546951 : Blo 1545470 1546951 := bstep (se 1 (by rfl) ⟨1160213, by rfl⟩ : syracuseStep 1546951 = 2320427) B2320427
theorem B1546971 : Blo 1545470 1546971 := bstep (se 1 (by rfl) ⟨1160228, by rfl⟩ : syracuseStep 1546971 = 2320457) B2320457
theorem B1547047 : Blo 1545470 1547047 := bstep (se 1 (by rfl) ⟨1160285, by rfl⟩ : syracuseStep 1547047 = 2320571) B2320571
theorem B1547087 : Blo 1545470 1547087 := bstep (se 1 (by rfl) ⟨1160315, by rfl⟩ : syracuseStep 1547087 = 2320631) B2320631
theorem B1547103 : Blo 1545470 1547103 := bstep (se 1 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 1547103 = 2320655) B2320655
theorem B31742837 : Blo 1545470 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B1547131 : Blo 1545470 1547131 := bstep (se 1 (by rfl) ⟨1160348, by rfl⟩ : syracuseStep 1547131 = 2320697) B2320697
theorem B1547183 : Blo 1545470 1547183 := bstep (se 1 (by rfl) ⟨1160387, by rfl⟩ : syracuseStep 1547183 = 2320775) B2320775
theorem B1547207 : Blo 1545470 1547207 := bstep (se 1 (by rfl) ⟨1160405, by rfl⟩ : syracuseStep 1547207 = 2320811) B2320811
theorem B1547227 : Blo 1545470 1547227 := bstep (se 1 (by rfl) ⟨1160420, by rfl⟩ : syracuseStep 1547227 = 2320841) B2320841
theorem B1547303 : Blo 1545470 1547303 := bstep (se 1 (by rfl) ⟨1160477, by rfl⟩ : syracuseStep 1547303 = 2320955) B2320955
theorem B13204559 : Blo 1545470 13204559 := bstep (se 1 (by rfl) ⟨9903419, by rfl⟩ : syracuseStep 13204559 = 19806839) B19806839
theorem B8805455 : Blo 1545470 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B3914831 : Blo 1545470 3914831 := bstep (se 1 (by rfl) ⟨2936123, by rfl⟩ : syracuseStep 3914831 = 5872247) B5872247
theorem B1547343 : Blo 1545470 1547343 := bstep (se 1 (by rfl) ⟨1160507, by rfl⟩ : syracuseStep 1547343 = 2321015) B2321015
theorem B1547359 : Blo 1545470 1547359 := bstep (se 1 (by rfl) ⟨1160519, by rfl⟩ : syracuseStep 1547359 = 2321039) B2321039
theorem B1547387 : Blo 1545470 1547387 := bstep (se 1 (by rfl) ⟨1160540, by rfl⟩ : syracuseStep 1547387 = 2321081) B2321081
theorem B1547439 : Blo 1545470 1547439 := bstep (se 1 (by rfl) ⟨1160579, by rfl⟩ : syracuseStep 1547439 = 2321159) B2321159
theorem B1547463 : Blo 1545470 1547463 := bstep (se 1 (by rfl) ⟨1160597, by rfl⟩ : syracuseStep 1547463 = 2321195) B2321195
theorem B5217641 : Blo 1545470 5217641 := bstep (se 2 (by rfl) ⟨1956615, by rfl⟩ : syracuseStep 5217641 = 3913231) B3913231
theorem B24141199 : Blo 1545470 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B7831079 : Blo 1545470 7831079 := bstep (se 1 (by rfl) ⟨5873309, by rfl⟩ : syracuseStep 7831079 = 11746619) B11746619
theorem B3481127 : Blo 1545470 3481127 := bstep (se 1 (by rfl) ⟨2610845, by rfl⟩ : syracuseStep 3481127 = 5221691) B5221691
theorem B5873249 : Blo 1545470 5873249 := bstep (se 2 (by rfl) ⟨2202468, by rfl⟩ : syracuseStep 5873249 = 4404937) B4404937
theorem B13213307 : Blo 1545470 13213307 := bstep (se 1 (by rfl) ⟨9909980, by rfl⟩ : syracuseStep 13213307 = 19819961) B19819961
theorem B4177619 : Blo 1545470 4177619 := bstep (se 1 (by rfl) ⟨3133214, by rfl⟩ : syracuseStep 4177619 = 6266429) B6266429
theorem B3915479 : Blo 1545470 3915479 := bstep (se 1 (by rfl) ⟨2936609, by rfl⟩ : syracuseStep 3915479 = 5873219) B5873219
theorem B4955863 : Blo 1545470 4955863 := bstep (se 1 (by rfl) ⟨3716897, by rfl⟩ : syracuseStep 4955863 = 7433795) B7433795
theorem B26418959 : Blo 1545470 26418959 := bstep (se 1 (by rfl) ⟨19814219, by rfl⟩ : syracuseStep 26418959 = 39628439) B39628439
theorem B11747105 : Blo 1545470 11747105 := bstep (se 2 (by rfl) ⟨4405164, by rfl⟩ : syracuseStep 11747105 = 8810329) B8810329
theorem B3481451 : Blo 1545470 3481451 := bstep (se 1 (by rfl) ⟨2611088, by rfl⟩ : syracuseStep 3481451 = 5222177) B5222177
theorem B3481505 : Blo 1545470 3481505 := bstep (se 2 (by rfl) ⟨1305564, by rfl⟩ : syracuseStep 3481505 = 2611129) B2611129
theorem B2318255 : Blo 1545470 2318255 := bstep (se 1 (by rfl) ⟨1738691, by rfl⟩ : syracuseStep 2318255 = 3477383) B3477383
theorem B5218235 : Blo 1545470 5218235 := bstep (se 1 (by rfl) ⟨3913676, by rfl⟩ : syracuseStep 5218235 = 7827353) B7827353
theorem B8363969 : Blo 1545470 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B2318441 : Blo 1545470 2318441 := bstep (se 2 (by rfl) ⟨869415, by rfl⟩ : syracuseStep 2318441 = 1738831) B1738831
theorem B4178267 : Blo 1545470 4178267 := bstep (se 1 (by rfl) ⟨3133700, by rfl⟩ : syracuseStep 4178267 = 6267401) B6267401
theorem B5218667 : Blo 1545470 5218667 := bstep (se 1 (by rfl) ⟨3914000, by rfl⟩ : syracuseStep 5218667 = 7828001) B7828001
theorem B2318759 : Blo 1545470 2318759 := bstep (se 1 (by rfl) ⟨1739069, by rfl⟩ : syracuseStep 2318759 = 3478139) B3478139
theorem B15868385 : Blo 1545470 15868385 := bstep (se 2 (by rfl) ⟨5950644, by rfl⟩ : syracuseStep 15868385 = 11901289) B11901289
theorem B2318843 : Blo 1545470 2318843 := bstep (se 1 (by rfl) ⟨1739132, by rfl⟩ : syracuseStep 2318843 = 3478265) B3478265
theorem B2646523 : Blo 1545470 2646523 := bstep (se 1 (by rfl) ⟨1984892, by rfl⟩ : syracuseStep 2646523 = 3969785) B3969785
theorem B8806913 : Blo 1545470 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B10871297 : Blo 1545470 10871297 := bstep (se 2 (by rfl) ⟨4076736, by rfl⟩ : syracuseStep 10871297 = 8153473) B8153473
theorem B225845819 : Blo 1545470 225845819 := bstep (se 1 (by rfl) ⟨169384364, by rfl⟩ : syracuseStep 225845819 = 338768729) B338768729
theorem B2318969 : Blo 1545470 2318969 := bstep (se 2 (by rfl) ⟨869613, by rfl⟩ : syracuseStep 2318969 = 1739227) B1739227
theorem B5218937 : Blo 1545470 5218937 := bstep (se 2 (by rfl) ⟨1957101, by rfl⟩ : syracuseStep 5218937 = 3914203) B3914203
theorem B2319023 : Blo 1545470 2319023 := bstep (se 1 (by rfl) ⟨1739267, by rfl⟩ : syracuseStep 2319023 = 3478535) B3478535
theorem B3302063 : Blo 1545470 3302063 := bstep (se 1 (by rfl) ⟨2476547, by rfl⟩ : syracuseStep 3302063 = 4953095) B4953095
theorem B13206199 : Blo 1545470 13206199 := bstep (se 1 (by rfl) ⟨9904649, by rfl⟩ : syracuseStep 13206199 = 19809299) B19809299
theorem B3916471 : Blo 1545470 3916471 := bstep (se 1 (by rfl) ⟨2937353, by rfl⟩ : syracuseStep 3916471 = 5874707) B5874707
theorem B9904855 : Blo 1545470 9904855 := bstep (se 1 (by rfl) ⟨7428641, by rfl⟩ : syracuseStep 9904855 = 14857283) B14857283
theorem B2319071 : Blo 1545470 2319071 := bstep (se 1 (by rfl) ⟨1739303, by rfl⟩ : syracuseStep 2319071 = 3478607) B3478607
theorem B3302363 : Blo 1545470 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B2319335 : Blo 1545470 2319335 := bstep (se 1 (by rfl) ⟨1739501, by rfl⟩ : syracuseStep 2319335 = 3479003) B3479003
theorem B3916775 : Blo 1545470 3916775 := bstep (se 1 (by rfl) ⟨2937581, by rfl⟩ : syracuseStep 3916775 = 5875163) B5875163
theorem B31745125 : Blo 1545470 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B7824599 : Blo 1545470 7824599 := bstep (se 1 (by rfl) ⟨5868449, by rfl⟩ : syracuseStep 7824599 = 11736899) B11736899
theorem B2319593 : Blo 1545470 2319593 := bstep (se 2 (by rfl) ⟨869847, by rfl⟩ : syracuseStep 2319593 = 1739695) B1739695
theorem B14861555 : Blo 1545470 14861555 := bstep (se 1 (by rfl) ⟨11146166, by rfl⟩ : syracuseStep 14861555 = 22292333) B22292333
theorem B2319647 : Blo 1545470 2319647 := bstep (se 1 (by rfl) ⟨1739735, by rfl⟩ : syracuseStep 2319647 = 3479471) B3479471
theorem B7431547 : Blo 1545470 7431547 := bstep (se 1 (by rfl) ⟨5573660, by rfl⟩ : syracuseStep 7431547 = 11147321) B11147321
theorem B7431563 : Blo 1545470 7431563 := bstep (se 1 (by rfl) ⟨5573672, by rfl⟩ : syracuseStep 7431563 = 11147345) B11147345
theorem B6604193 : Blo 1545470 6604193 := bstep (se 2 (by rfl) ⟨2476572, by rfl⟩ : syracuseStep 6604193 = 4953145) B4953145
theorem B2319815 : Blo 1545470 2319815 := bstep (se 1 (by rfl) ⟨1739861, by rfl⟩ : syracuseStep 2319815 = 3479723) B3479723
theorem B2320169 : Blo 1545470 2320169 := bstep (se 2 (by rfl) ⟨870063, by rfl⟩ : syracuseStep 2320169 = 1740127) B1740127
theorem B2787119 : Blo 1545470 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B2320175 : Blo 1545470 2320175 := bstep (se 1 (by rfl) ⟨1740131, by rfl⟩ : syracuseStep 2320175 = 3480263) B3480263
theorem B32188265 : Blo 1545470 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B21161891 : Blo 1545470 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B22906957 : Blo 1545470 22906957 := bstep (se 3 (by rfl) ⟨4295054, by rfl⟩ : syracuseStep 22906957 = 8590109) B8590109
theorem B2320649 : Blo 1545470 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B1739047 : Blo 1545470 1739047 := bstep (se 1 (by rfl) ⟨1304285, by rfl⟩ : syracuseStep 1739047 = 2608571) B2608571
theorem B1739119 : Blo 1545470 1739119 := bstep (se 1 (by rfl) ⟨1304339, by rfl⟩ : syracuseStep 1739119 = 2608679) B2608679
theorem B5220719 : Blo 1545470 5220719 := bstep (se 1 (by rfl) ⟨3915539, by rfl⟩ : syracuseStep 5220719 = 7831079) B7831079
theorem B2320751 : Blo 1545470 2320751 := bstep (se 1 (by rfl) ⟨1740563, by rfl⟩ : syracuseStep 2320751 = 3481127) B3481127
theorem B8808871 : Blo 1545470 8808871 := bstep (se 1 (by rfl) ⟨6606653, by rfl⟩ : syracuseStep 8808871 = 13213307) B13213307
theorem B1739335 : Blo 1545470 1739335 := bstep (se 1 (by rfl) ⟨1304501, by rfl⟩ : syracuseStep 1739335 = 2609003) B2609003
theorem B2320967 : Blo 1545470 2320967 := bstep (se 1 (by rfl) ⟨1740725, by rfl⟩ : syracuseStep 2320967 = 3481451) B3481451
theorem B2787947 : Blo 1545470 2787947 := bstep (se 1 (by rfl) ⟨2090960, by rfl⟩ : syracuseStep 2787947 = 4181921) B4181921
theorem B2321003 : Blo 1545470 2321003 := bstep (se 1 (by rfl) ⟨1740752, by rfl⟩ : syracuseStep 2321003 = 3481505) B3481505
theorem B4401839 : Blo 1545470 4401839 := bstep (se 1 (by rfl) ⟨3301379, by rfl⟩ : syracuseStep 4401839 = 6602759) B6602759
theorem B2476727 : Blo 1545470 2476727 := bstep (se 1 (by rfl) ⟨1857545, by rfl⟩ : syracuseStep 2476727 = 3715091) B3715091
theorem B37645073 : Blo 1545470 37645073 := bstep (se 2 (by rfl) ⟨14116902, by rfl⟩ : syracuseStep 37645073 = 28233805) B28233805
theorem B96586667 : Blo 1545470 96586667 := bstep (se 1 (by rfl) ⟨72440000, by rfl⟩ : syracuseStep 96586667 = 144880001) B144880001
theorem B3714187 : Blo 1545470 3714187 := bstep (se 1 (by rfl) ⟨2785640, by rfl⟩ : syracuseStep 3714187 = 5571281) B5571281
theorem B101682377 : Blo 1545470 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B5024987 : Blo 1545470 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B4951327 : Blo 1545470 4951327 := bstep (se 1 (by rfl) ⟨3713495, by rfl⟩ : syracuseStep 4951327 = 7426991) B7426991
theorem B1740199 : Blo 1545470 1740199 := bstep (se 1 (by rfl) ⟨1305149, by rfl⟩ : syracuseStep 1740199 = 2610299) B2610299
theorem B3304891 : Blo 1545470 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B3304967 : Blo 1545470 3304967 := bstep (se 1 (by rfl) ⟨2478725, by rfl⟩ : syracuseStep 3304967 = 4957451) B4957451
theorem B5222123 : Blo 1545470 5222123 := bstep (se 1 (by rfl) ⟨3916592, by rfl⟩ : syracuseStep 5222123 = 7833185) B7833185
theorem B29716409 : Blo 1545470 29716409 := bstep (se 2 (by rfl) ⟨11143653, by rfl⟩ : syracuseStep 29716409 = 22287307) B22287307
theorem B3477455 : Blo 1545470 3477455 := bstep (se 1 (by rfl) ⟨2608091, by rfl⟩ : syracuseStep 3477455 = 5216183) B5216183
theorem B9908189 : Blo 1545470 9908189 := bstep (se 3 (by rfl) ⟨1857785, by rfl⟩ : syracuseStep 9908189 = 3715571) B3715571
theorem B1740775 : Blo 1545470 1740775 := bstep (se 1 (by rfl) ⟨1305581, by rfl⟩ : syracuseStep 1740775 = 2611163) B2611163
theorem B7827515 : Blo 1545470 7827515 := bstep (se 1 (by rfl) ⟨5870636, by rfl⟩ : syracuseStep 7827515 = 11741273) B11741273
theorem B3715283 : Blo 1545470 3715283 := bstep (se 1 (by rfl) ⟨2786462, by rfl⟩ : syracuseStep 3715283 = 5572925) B5572925
theorem B3477833 : Blo 1545470 3477833 := bstep (se 2 (by rfl) ⟨1304187, by rfl⟩ : syracuseStep 3477833 = 2608375) B2608375
theorem B3477851 : Blo 1545470 3477851 := bstep (se 1 (by rfl) ⟨2608388, by rfl⟩ : syracuseStep 3477851 = 5216777) B5216777
theorem B3912047 : Blo 1545470 3912047 := bstep (se 1 (by rfl) ⟨2934035, by rfl⟩ : syracuseStep 3912047 = 5868071) B5868071
theorem B29716955 : Blo 1545470 29716955 := bstep (se 1 (by rfl) ⟨22287716, by rfl⟩ : syracuseStep 29716955 = 44575433) B44575433
theorem B8803039 : Blo 1545470 8803039 := bstep (se 1 (by rfl) ⟨6602279, by rfl⟩ : syracuseStep 8803039 = 13204559) B13204559
theorem B5870303 : Blo 1545470 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B2609887 : Blo 1545470 2609887 := bstep (se 1 (by rfl) ⟨1957415, by rfl⟩ : syracuseStep 2609887 = 3914831) B3914831
theorem B3478427 : Blo 1545470 3478427 := bstep (se 1 (by rfl) ⟨2608820, by rfl⟩ : syracuseStep 3478427 = 5217641) B5217641
theorem B6607817 : Blo 1545470 6607817 := bstep (se 2 (by rfl) ⟨2477931, by rfl⟩ : syracuseStep 6607817 = 4955863) B4955863
theorem B3912695 : Blo 1545470 3912695 := bstep (se 1 (by rfl) ⟨2934521, by rfl⟩ : syracuseStep 3912695 = 5869043) B5869043
theorem B7828487 : Blo 1545470 7828487 := bstep (se 1 (by rfl) ⟨5871365, by rfl⟩ : syracuseStep 7828487 = 11742731) B11742731
theorem B3478625 : Blo 1545470 3478625 := bstep (se 2 (by rfl) ⟨1304484, by rfl⟩ : syracuseStep 3478625 = 2608969) B2608969
theorem B2610319 : Blo 1545470 2610319 := bstep (se 1 (by rfl) ⟨1957739, by rfl⟩ : syracuseStep 2610319 = 3915479) B3915479
theorem B1545503 : Blo 1545470 1545503 := bstep (se 1 (by rfl) ⟨1159127, by rfl⟩ : syracuseStep 1545503 = 2318255) B2318255
theorem B3478823 : Blo 1545470 3478823 := bstep (se 1 (by rfl) ⟨2609117, by rfl⟩ : syracuseStep 3478823 = 5218235) B5218235
theorem B5575979 : Blo 1545470 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B1545563 : Blo 1545470 1545563 := bstep (se 1 (by rfl) ⟨1159172, by rfl⟩ : syracuseStep 1545563 = 2318345) B2318345
theorem B3528031 : Blo 1545470 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B1545583 : Blo 1545470 1545583 := bstep (se 1 (by rfl) ⟨1159187, by rfl⟩ : syracuseStep 1545583 = 2318375) B2318375
theorem B2610569 : Blo 1545470 2610569 := bstep (se 2 (by rfl) ⟨978963, by rfl⟩ : syracuseStep 2610569 = 1957927) B1957927
theorem B5870987 : Blo 1545470 5870987 := bstep (se 1 (by rfl) ⟨4403240, by rfl⟩ : syracuseStep 5870987 = 8806481) B8806481
theorem B3716513 : Blo 1545470 3716513 := bstep (se 2 (by rfl) ⟨1393692, by rfl⟩ : syracuseStep 3716513 = 2787385) B2787385
theorem B1545639 : Blo 1545470 1545639 := bstep (se 1 (by rfl) ⟨1159229, by rfl⟩ : syracuseStep 1545639 = 2318459) B2318459
theorem B7828973 : Blo 1545470 7828973 := bstep (se 3 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 7828973 = 2935865) B2935865
theorem B1545723 : Blo 1545470 1545723 := bstep (se 1 (by rfl) ⟨1159292, by rfl⟩ : syracuseStep 1545723 = 2318585) B2318585
theorem B1545791 : Blo 1545470 1545791 := bstep (se 1 (by rfl) ⟨1159343, by rfl⟩ : syracuseStep 1545791 = 2318687) B2318687
theorem B1545799 : Blo 1545470 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B3479201 : Blo 1545470 3479201 := bstep (se 2 (by rfl) ⟨1304700, by rfl⟩ : syracuseStep 3479201 = 2609401) B2609401
theorem B1857199 : Blo 1545470 1857199 := bstep (se 1 (by rfl) ⟨1392899, by rfl⟩ : syracuseStep 1857199 = 2785799) B2785799
theorem B1545951 : Blo 1545470 1545951 := bstep (se 1 (by rfl) ⟨1159463, by rfl⟩ : syracuseStep 1545951 = 2318927) B2318927
theorem B15480557 : Blo 1545470 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B1546031 : Blo 1545470 1546031 := bstep (se 1 (by rfl) ⟨1159523, by rfl⟩ : syracuseStep 1546031 = 2319047) B2319047
theorem B2611001 : Blo 1545470 2611001 := bstep (se 2 (by rfl) ⟨979125, by rfl⟩ : syracuseStep 2611001 = 1958251) B1958251
theorem B4405097 : Blo 1545470 4405097 := bstep (se 2 (by rfl) ⟨1651911, by rfl⟩ : syracuseStep 4405097 = 3303823) B3303823
theorem B1546139 : Blo 1545470 1546139 := bstep (se 1 (by rfl) ⟨1159604, by rfl⟩ : syracuseStep 1546139 = 2319209) B2319209
theorem B1546191 : Blo 1545470 1546191 := bstep (se 1 (by rfl) ⟨1159643, by rfl⟩ : syracuseStep 1546191 = 2319287) B2319287
theorem B1546215 : Blo 1545470 1546215 := bstep (se 1 (by rfl) ⟨1159661, by rfl⟩ : syracuseStep 1546215 = 2319323) B2319323
theorem B3479561 : Blo 1545470 3479561 := bstep (se 2 (by rfl) ⟨1304835, by rfl⟩ : syracuseStep 3479561 = 2609671) B2609671
theorem B7829783 : Blo 1545470 7829783 := bstep (se 1 (by rfl) ⟨5872337, by rfl⟩ : syracuseStep 7829783 = 11744675) B11744675
theorem B16726297 : Blo 1545470 16726297 := bstep (se 2 (by rfl) ⟨6272361, by rfl⟩ : syracuseStep 16726297 = 12544723) B12544723
theorem B4405529 : Blo 1545470 4405529 := bstep (se 2 (by rfl) ⟨1652073, by rfl⟩ : syracuseStep 4405529 = 3304147) B3304147
theorem B1546527 : Blo 1545470 1546527 := bstep (se 1 (by rfl) ⟨1159895, by rfl⟩ : syracuseStep 1546527 = 2319791) B2319791
theorem B1546587 : Blo 1545470 1546587 := bstep (se 1 (by rfl) ⟨1159940, by rfl⟩ : syracuseStep 1546587 = 2319881) B2319881
theorem B1546607 : Blo 1545470 1546607 := bstep (se 1 (by rfl) ⟨1159955, by rfl⟩ : syracuseStep 1546607 = 2319911) B2319911
theorem B3479975 : Blo 1545470 3479975 := bstep (se 1 (by rfl) ⟨2609981, by rfl⟩ : syracuseStep 3479975 = 5219963) B5219963
theorem B1546663 : Blo 1545470 1546663 := bstep (se 1 (by rfl) ⟨1159997, by rfl⟩ : syracuseStep 1546663 = 2319995) B2319995
theorem B3717551 : Blo 1545470 3717551 := bstep (se 1 (by rfl) ⟨2788163, by rfl⟩ : syracuseStep 3717551 = 5576327) B5576327
theorem B5216723 : Blo 1545470 5216723 := bstep (se 1 (by rfl) ⟨3912542, by rfl⟩ : syracuseStep 5216723 = 7825085) B7825085
theorem B31726075 : Blo 1545470 31726075 := bstep (se 1 (by rfl) ⟨23794556, by rfl⟩ : syracuseStep 31726075 = 47589113) B47589113
theorem B1546747 : Blo 1545470 1546747 := bstep (se 1 (by rfl) ⟨1160060, by rfl⟩ : syracuseStep 1546747 = 2320121) B2320121
theorem B3480083 : Blo 1545470 3480083 := bstep (se 1 (by rfl) ⟨2610062, by rfl⟩ : syracuseStep 3480083 = 5220125) B5220125
theorem B16726553 : Blo 1545470 16726553 := bstep (se 2 (by rfl) ⟨6272457, by rfl⟩ : syracuseStep 16726553 = 12544915) B12544915
theorem B5216831 : Blo 1545470 5216831 := bstep (se 1 (by rfl) ⟨3912623, by rfl⟩ : syracuseStep 5216831 = 7825247) B7825247
theorem B1546815 : Blo 1545470 1546815 := bstep (se 1 (by rfl) ⟨1160111, by rfl⟩ : syracuseStep 1546815 = 2320223) B2320223
theorem B3349055 : Blo 1545470 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B3717695 : Blo 1545470 3717695 := bstep (se 1 (by rfl) ⟨2788271, by rfl⟩ : syracuseStep 3717695 = 5576543) B5576543
theorem B1546823 : Blo 1545470 1546823 := bstep (se 1 (by rfl) ⟨1160117, by rfl⟩ : syracuseStep 1546823 = 2320235) B2320235
theorem B3480137 : Blo 1545470 3480137 := bstep (se 2 (by rfl) ⟨1305051, by rfl⟩ : syracuseStep 3480137 = 2610103) B2610103
theorem B1956575 : Blo 1545470 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B1546975 : Blo 1545470 1546975 := bstep (se 1 (by rfl) ⟨1160231, by rfl⟩ : syracuseStep 1546975 = 2320463) B2320463
theorem B1547055 : Blo 1545470 1547055 := bstep (se 1 (by rfl) ⟨1160291, by rfl⟩ : syracuseStep 1547055 = 2320583) B2320583
theorem B7428989 : Blo 1545470 7428989 := bstep (se 3 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 7428989 = 2785871) B2785871
theorem B3914639 : Blo 1545470 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B1547163 : Blo 1545470 1547163 := bstep (se 1 (by rfl) ⟨1160372, by rfl⟩ : syracuseStep 1547163 = 2320745) B2320745
theorem B1547215 : Blo 1545470 1547215 := bstep (se 1 (by rfl) ⟨1160411, by rfl⟩ : syracuseStep 1547215 = 2320823) B2320823
theorem B3480551 : Blo 1545470 3480551 := bstep (se 1 (by rfl) ⟨2610413, by rfl⟩ : syracuseStep 3480551 = 5220827) B5220827
theorem B1547239 : Blo 1545470 1547239 := bstep (se 1 (by rfl) ⟨1160429, by rfl⟩ : syracuseStep 1547239 = 2320859) B2320859
theorem B5872763 : Blo 1545470 5872763 := bstep (se 1 (by rfl) ⟨4404572, by rfl⟩ : syracuseStep 5872763 = 8809145) B8809145
theorem B4406395 : Blo 1545470 4406395 := bstep (se 1 (by rfl) ⟨3304796, by rfl⟩ : syracuseStep 4406395 = 6609593) B6609593
theorem B6691979 : Blo 1545470 6691979 := bstep (se 1 (by rfl) ⟨5018984, by rfl⟩ : syracuseStep 6691979 = 10037969) B10037969
theorem B3480929 : Blo 1545470 3480929 := bstep (se 2 (by rfl) ⟨1305348, by rfl⟩ : syracuseStep 3480929 = 2610697) B2610697
theorem B6266231 : Blo 1545470 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B3481019 : Blo 1545470 3481019 := bstep (se 1 (by rfl) ⟨2610764, by rfl⟩ : syracuseStep 3481019 = 5221529) B5221529
theorem B5291513 : Blo 1545470 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B2203129 : Blo 1545470 2203129 := bstep (se 2 (by rfl) ⟨826173, by rfl⟩ : syracuseStep 2203129 = 1652347) B1652347
theorem B3481145 : Blo 1545470 3481145 := bstep (se 2 (by rfl) ⟨1305429, by rfl⟩ : syracuseStep 3481145 = 2610859) B2610859
theorem B11148961 : Blo 1545470 11148961 := bstep (se 2 (by rfl) ⟨4180860, by rfl⟩ : syracuseStep 11148961 = 8361721) B8361721
theorem B3915499 : Blo 1545470 3915499 := bstep (se 1 (by rfl) ⟨2936624, by rfl⟩ : syracuseStep 3915499 = 5873249) B5873249
theorem B2785079 : Blo 1545470 2785079 := bstep (se 1 (by rfl) ⟨2088809, by rfl⟩ : syracuseStep 2785079 = 4177619) B4177619
theorem B3301175 : Blo 1545470 3301175 := bstep (se 1 (by rfl) ⟨2475881, by rfl⟩ : syracuseStep 3301175 = 4951763) B4951763
theorem B17612639 : Blo 1545470 17612639 := bstep (se 1 (by rfl) ⟨13209479, by rfl⟩ : syracuseStep 17612639 = 26418959) B26418959
theorem B14868319 : Blo 1545470 14868319 := bstep (se 1 (by rfl) ⟨11151239, by rfl⟩ : syracuseStep 14868319 = 22302479) B22302479
theorem B7831403 : Blo 1545470 7831403 := bstep (se 1 (by rfl) ⟨5873552, by rfl⟩ : syracuseStep 7831403 = 11747105) B11747105
theorem B5218343 : Blo 1545470 5218343 := bstep (se 1 (by rfl) ⟨3913757, by rfl⟩ : syracuseStep 5218343 = 7827515) B7827515
theorem B2318555 : Blo 1545470 2318555 := bstep (se 1 (by rfl) ⟨1738916, by rfl⟩ : syracuseStep 2318555 = 3477833) B3477833
theorem B2318567 : Blo 1545470 2318567 := bstep (se 1 (by rfl) ⟨1738925, by rfl⟩ : syracuseStep 2318567 = 3477851) B3477851
theorem B2785511 : Blo 1545470 2785511 := bstep (se 1 (by rfl) ⟨2089133, by rfl⟩ : syracuseStep 2785511 = 4178267) B4178267
theorem B2318729 : Blo 1545470 2318729 := bstep (se 2 (by rfl) ⟨869523, by rfl⟩ : syracuseStep 2318729 = 1739047) B1739047
theorem B2318825 : Blo 1545470 2318825 := bstep (se 2 (by rfl) ⟨869559, by rfl⟩ : syracuseStep 2318825 = 1739119) B1739119
theorem B2318951 : Blo 1545470 2318951 := bstep (se 1 (by rfl) ⟨1739213, by rfl⟩ : syracuseStep 2318951 = 3478427) B3478427
theorem B5218991 : Blo 1545470 5218991 := bstep (se 1 (by rfl) ⟨3914243, by rfl⟩ : syracuseStep 5218991 = 7828487) B7828487
theorem B2319083 : Blo 1545470 2319083 := bstep (se 1 (by rfl) ⟨1739312, by rfl⟩ : syracuseStep 2319083 = 3478625) B3478625
theorem B11748077 : Blo 1545470 11748077 := bstep (se 3 (by rfl) ⟨2202764, by rfl⟩ : syracuseStep 11748077 = 4405529) B4405529
theorem B2319113 : Blo 1545470 2319113 := bstep (se 2 (by rfl) ⟨869667, by rfl⟩ : syracuseStep 2319113 = 1739335) B1739335
theorem B14869277 : Blo 1545470 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B2319215 : Blo 1545470 2319215 := bstep (se 1 (by rfl) ⟨1739411, by rfl⟩ : syracuseStep 2319215 = 3478823) B3478823
theorem B13206473 : Blo 1545470 13206473 := bstep (se 2 (by rfl) ⟨4952427, by rfl⟩ : syracuseStep 13206473 = 9904855) B9904855
theorem B5219315 : Blo 1545470 5219315 := bstep (se 1 (by rfl) ⟨3914486, by rfl⟩ : syracuseStep 5219315 = 7828973) B7828973
theorem B2319467 : Blo 1545470 2319467 := bstep (se 1 (by rfl) ⟨1739600, by rfl⟩ : syracuseStep 2319467 = 3479201) B3479201
theorem B14107927 : Blo 1545470 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B2319707 : Blo 1545470 2319707 := bstep (se 1 (by rfl) ⟨1739780, by rfl⟩ : syracuseStep 2319707 = 3479561) B3479561
theorem B5875193 : Blo 1545470 5875193 := bstep (se 2 (by rfl) ⟨2203197, by rfl⟩ : syracuseStep 5875193 = 4406395) B4406395
theorem B9913853 : Blo 1545470 9913853 := bstep (se 3 (by rfl) ⟨1858847, by rfl⟩ : syracuseStep 9913853 = 3717695) B3717695
theorem B5219855 : Blo 1545470 5219855 := bstep (se 1 (by rfl) ⟨3914891, by rfl⟩ : syracuseStep 5219855 = 7829783) B7829783
theorem B2319983 : Blo 1545470 2319983 := bstep (se 1 (by rfl) ⟨1739987, by rfl⟩ : syracuseStep 2319983 = 3479975) B3479975
theorem B2320055 : Blo 1545470 2320055 := bstep (se 1 (by rfl) ⟨1740041, by rfl⟩ : syracuseStep 2320055 = 3480083) B3480083
theorem B11151035 : Blo 1545470 11151035 := bstep (se 1 (by rfl) ⟨8363276, by rfl⟩ : syracuseStep 11151035 = 16726553) B16726553
theorem B2320091 : Blo 1545470 2320091 := bstep (se 1 (by rfl) ⟨1740068, by rfl⟩ : syracuseStep 2320091 = 3480137) B3480137
theorem B2934559 : Blo 1545470 2934559 := bstep (se 1 (by rfl) ⟨2200919, by rfl⟩ : syracuseStep 2934559 = 4401839) B4401839
theorem B4704041 : Blo 1545470 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B2320265 : Blo 1545470 2320265 := bstep (se 2 (by rfl) ⟨870099, by rfl⟩ : syracuseStep 2320265 = 1740199) B1740199
theorem B64391111 : Blo 1545470 64391111 := bstep (se 1 (by rfl) ⟨48293333, by rfl⟩ : syracuseStep 64391111 = 96586667) B96586667
theorem B2320367 : Blo 1545470 2320367 := bstep (se 1 (by rfl) ⟨1740275, by rfl⟩ : syracuseStep 2320367 = 3480551) B3480551
theorem B2476265 : Blo 1545470 2476265 := bstep (se 2 (by rfl) ⟨928599, by rfl⟩ : syracuseStep 2476265 = 1857199) B1857199
theorem B2320619 : Blo 1545470 2320619 := bstep (se 1 (by rfl) ⟨1740464, by rfl⟩ : syracuseStep 2320619 = 3480929) B3480929
theorem B2320679 : Blo 1545470 2320679 := bstep (se 1 (by rfl) ⟨1740509, by rfl⟩ : syracuseStep 2320679 = 3481019) B3481019
theorem B5220665 : Blo 1545470 5220665 := bstep (se 2 (by rfl) ⟨1957749, by rfl⟩ : syracuseStep 5220665 = 3915499) B3915499
theorem B2320763 : Blo 1545470 2320763 := bstep (se 1 (by rfl) ⟨1740572, by rfl⟩ : syracuseStep 2320763 = 3481145) B3481145
theorem B11741759 : Blo 1545470 11741759 := bstep (se 1 (by rfl) ⟨8806319, by rfl⟩ : syracuseStep 11741759 = 17612639) B17612639
theorem B5220935 : Blo 1545470 5220935 := bstep (se 1 (by rfl) ⟨3915701, by rfl⟩ : syracuseStep 5220935 = 7831403) B7831403
theorem B19810939 : Blo 1545470 19810939 := bstep (se 1 (by rfl) ⟨14858204, by rfl⟩ : syracuseStep 19810939 = 29716409) B29716409
theorem B11750021 : Blo 1545470 11750021 := bstep (se 4 (by rfl) ⟨1101564, by rfl⟩ : syracuseStep 11750021 = 2203129) B2203129
theorem B2321033 : Blo 1545470 2321033 := bstep (se 2 (by rfl) ⟨870387, by rfl⟩ : syracuseStep 2321033 = 1740775) B1740775
theorem B6605459 : Blo 1545470 6605459 := bstep (se 1 (by rfl) ⟨4954094, by rfl⟩ : syracuseStep 6605459 = 9908189) B9908189
theorem B30542609 : Blo 1545470 30542609 := bstep (se 2 (by rfl) ⟨11453478, by rfl⟩ : syracuseStep 30542609 = 22906957) B22906957
theorem B2476855 : Blo 1545470 2476855 := bstep (se 1 (by rfl) ⟨1857641, by rfl⟩ : syracuseStep 2476855 = 3715283) B3715283
theorem B2608031 : Blo 1545470 2608031 := bstep (se 1 (by rfl) ⟨1956023, by rfl⟩ : syracuseStep 2608031 = 3912047) B3912047
theorem B19811303 : Blo 1545470 19811303 := bstep (se 1 (by rfl) ⟨14858477, by rfl⟩ : syracuseStep 19811303 = 29716955) B29716955
theorem B10578923 : Blo 1545470 10578923 := bstep (se 1 (by rfl) ⟨7934192, by rfl⟩ : syracuseStep 10578923 = 15868385) B15868385
theorem B22301729 : Blo 1545470 22301729 := bstep (se 2 (by rfl) ⟨8363148, by rfl⟩ : syracuseStep 22301729 = 16726297) B16726297
theorem B150563879 : Blo 1545470 150563879 := bstep (se 1 (by rfl) ⟨112922909, by rfl⟩ : syracuseStep 150563879 = 225845819) B225845819
theorem B2608463 : Blo 1545470 2608463 := bstep (se 1 (by rfl) ⟨1956347, by rfl⟩ : syracuseStep 2608463 = 3912695) B3912695
theorem B9907703 : Blo 1545470 9907703 := bstep (se 1 (by rfl) ⟨7430777, by rfl⟩ : syracuseStep 9907703 = 14861555) B14861555
theorem B17608265 : Blo 1545470 17608265 := bstep (se 2 (by rfl) ⟨6603099, by rfl⟩ : syracuseStep 17608265 = 13206199) B13206199
theorem B5221961 : Blo 1545470 5221961 := bstep (se 2 (by rfl) ⟨1958235, by rfl⟩ : syracuseStep 5221961 = 3916471) B3916471
theorem B1740379 : Blo 1545470 1740379 := bstep (se 1 (by rfl) ⟨1305284, by rfl⟩ : syracuseStep 1740379 = 2610569) B2610569
theorem B2477675 : Blo 1545470 2477675 := bstep (se 1 (by rfl) ⟨1858256, by rfl⟩ : syracuseStep 2477675 = 3716513) B3716513
theorem B1740667 : Blo 1545470 1740667 := bstep (se 1 (by rfl) ⟨1305500, by rfl⟩ : syracuseStep 1740667 = 2611001) B2611001
theorem B2936731 : Blo 1545470 2936731 := bstep (se 1 (by rfl) ⟨2202548, by rfl⟩ : syracuseStep 2936731 = 4405097) B4405097
theorem B21458843 : Blo 1545470 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B4952249 : Blo 1545470 4952249 := bstep (se 2 (by rfl) ⟨1857093, by rfl⟩ : syracuseStep 4952249 = 3714187) B3714187
theorem B2478367 : Blo 1545470 2478367 := bstep (se 1 (by rfl) ⟨1858775, by rfl⟩ : syracuseStep 2478367 = 3717551) B3717551
theorem B3477815 : Blo 1545470 3477815 := bstep (se 1 (by rfl) ⟨2608361, by rfl⟩ : syracuseStep 3477815 = 5216723) B5216723
theorem B3477887 : Blo 1545470 3477887 := bstep (se 1 (by rfl) ⟨2608415, by rfl⟩ : syracuseStep 3477887 = 5216831) B5216831
theorem B2232703 : Blo 1545470 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B1651151 : Blo 1545470 1651151 := bstep (se 1 (by rfl) ⟨1238363, by rfl⟩ : syracuseStep 1651151 = 2476727) B2476727
theorem B9908729 : Blo 1545470 9908729 := bstep (se 2 (by rfl) ⟨3715773, by rfl⟩ : syracuseStep 9908729 = 7431547) B7431547
theorem B25096715 : Blo 1545470 25096715 := bstep (se 1 (by rfl) ⟨18822536, by rfl⟩ : syracuseStep 25096715 = 37645073) B37645073
theorem B4952659 : Blo 1545470 4952659 := bstep (se 1 (by rfl) ⟨3714494, by rfl⟩ : syracuseStep 4952659 = 7428989) B7428989
theorem B2609759 : Blo 1545470 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B4461319 : Blo 1545470 4461319 := bstep (se 1 (by rfl) ⟨3345989, by rfl⟩ : syracuseStep 4461319 = 6691979) B6691979
theorem B14865281 : Blo 1545470 14865281 := bstep (se 2 (by rfl) ⟨5574480, by rfl⟩ : syracuseStep 14865281 = 11148961) B11148961
theorem B3527675 : Blo 1545470 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B1856719 : Blo 1545470 1856719 := bstep (se 1 (by rfl) ⟨1392539, by rfl⟩ : syracuseStep 1856719 = 2785079) B2785079
theorem B2200783 : Blo 1545470 2200783 := bstep (se 1 (by rfl) ⟨1650587, by rfl⟩ : syracuseStep 2200783 = 3301175) B3301175
theorem B1545627 : Blo 1545470 1545627 := bstep (se 1 (by rfl) ⟨1159220, by rfl⟩ : syracuseStep 1545627 = 2318441) B2318441
theorem B3479111 : Blo 1545470 3479111 := bstep (se 1 (by rfl) ⟨2609333, by rfl⟩ : syracuseStep 3479111 = 5218667) B5218667
theorem B1545839 : Blo 1545470 1545839 := bstep (se 1 (by rfl) ⟨1159379, by rfl⟩ : syracuseStep 1545839 = 2318759) B2318759
theorem B1545895 : Blo 1545470 1545895 := bstep (se 1 (by rfl) ⟨1159421, by rfl⟩ : syracuseStep 1545895 = 2318843) B2318843
theorem B5871275 : Blo 1545470 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B7247531 : Blo 1545470 7247531 := bstep (se 1 (by rfl) ⟨5435648, by rfl⟩ : syracuseStep 7247531 = 10871297) B10871297
theorem B1545979 : Blo 1545470 1545979 := bstep (se 1 (by rfl) ⟨1159484, by rfl⟩ : syracuseStep 1545979 = 2318969) B2318969
theorem B3479291 : Blo 1545470 3479291 := bstep (se 1 (by rfl) ⟨2609468, by rfl⟩ : syracuseStep 3479291 = 5218937) B5218937
theorem B1546015 : Blo 1545470 1546015 := bstep (se 1 (by rfl) ⟨1159511, by rfl⟩ : syracuseStep 1546015 = 2319023) B2319023
theorem B2201375 : Blo 1545470 2201375 := bstep (se 1 (by rfl) ⟨1651031, by rfl⟩ : syracuseStep 2201375 = 3302063) B3302063
theorem B1546047 : Blo 1545470 1546047 := bstep (se 1 (by rfl) ⟨1159535, by rfl⟩ : syracuseStep 1546047 = 2319071) B2319071
theorem B3913535 : Blo 1545470 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B11745161 : Blo 1545470 11745161 := bstep (se 2 (by rfl) ⟨4404435, by rfl⟩ : syracuseStep 11745161 = 8808871) B8808871
theorem B4405211 : Blo 1545470 4405211 := bstep (se 1 (by rfl) ⟨3303908, by rfl⟩ : syracuseStep 4405211 = 6607817) B6607817
theorem B2201575 : Blo 1545470 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B1546223 : Blo 1545470 1546223 := bstep (se 1 (by rfl) ⟨1159667, by rfl⟩ : syracuseStep 1546223 = 2319335) B2319335
theorem B2611183 : Blo 1545470 2611183 := bstep (se 1 (by rfl) ⟨1958387, by rfl⟩ : syracuseStep 2611183 = 3916775) B3916775
theorem B42301433 : Blo 1545470 42301433 := bstep (se 2 (by rfl) ⟨15863037, by rfl⟩ : syracuseStep 42301433 = 31726075) B31726075
theorem B3528697 : Blo 1545470 3528697 := bstep (se 2 (by rfl) ⟨1323261, by rfl⟩ : syracuseStep 3528697 = 2646523) B2646523
theorem B5216399 : Blo 1545470 5216399 := bstep (se 1 (by rfl) ⟨3912299, by rfl⟩ : syracuseStep 5216399 = 7824599) B7824599
theorem B1546395 : Blo 1545470 1546395 := bstep (se 1 (by rfl) ⟨1159796, by rfl⟩ : syracuseStep 1546395 = 2319593) B2319593
theorem B1546431 : Blo 1545470 1546431 := bstep (se 1 (by rfl) ⟨1159823, by rfl⟩ : syracuseStep 1546431 = 2319647) B2319647
theorem B3913991 : Blo 1545470 3913991 := bstep (se 1 (by rfl) ⟨2935493, by rfl⟩ : syracuseStep 3913991 = 5870987) B5870987
theorem B4954375 : Blo 1545470 4954375 := bstep (se 1 (by rfl) ⟨3715781, by rfl⟩ : syracuseStep 4954375 = 7431563) B7431563
theorem B11737385 : Blo 1545470 11737385 := bstep (se 2 (by rfl) ⟨4401519, by rfl⟩ : syracuseStep 11737385 = 8803039) B8803039
theorem B3479849 : Blo 1545470 3479849 := bstep (se 2 (by rfl) ⟨1304943, by rfl⟩ : syracuseStep 3479849 = 2609887) B2609887
theorem B1546543 : Blo 1545470 1546543 := bstep (se 1 (by rfl) ⟨1159907, by rfl⟩ : syracuseStep 1546543 = 2319815) B2319815
theorem B17611181 : Blo 1545470 17611181 := bstep (se 3 (by rfl) ⟨3302096, by rfl⟩ : syracuseStep 17611181 = 6604193) B6604193
theorem B10320371 : Blo 1545470 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B1546779 : Blo 1545470 1546779 := bstep (se 1 (by rfl) ⟨1160084, by rfl⟩ : syracuseStep 1546779 = 2320169) B2320169
theorem B1858079 : Blo 1545470 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B1546783 : Blo 1545470 1546783 := bstep (se 1 (by rfl) ⟨1160087, by rfl⟩ : syracuseStep 1546783 = 2320175) B2320175
theorem B8813245 : Blo 1545470 8813245 := bstep (se 3 (by rfl) ⟨1652483, by rfl⟩ : syracuseStep 8813245 = 3304967) B3304967
theorem B42326833 : Blo 1545470 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B1547099 : Blo 1545470 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B3480425 : Blo 1545470 3480425 := bstep (se 2 (by rfl) ⟨1305159, by rfl⟩ : syracuseStep 3480425 = 2610319) B2610319
theorem B3480479 : Blo 1545470 3480479 := bstep (se 1 (by rfl) ⟨2610359, by rfl⟩ : syracuseStep 3480479 = 5220719) B5220719
theorem B1547167 : Blo 1545470 1547167 := bstep (se 1 (by rfl) ⟨1160375, by rfl⟩ : syracuseStep 1547167 = 2320751) B2320751
theorem B6601769 : Blo 1545470 6601769 := bstep (se 2 (by rfl) ⟨2475663, by rfl⟩ : syracuseStep 6601769 = 4951327) B4951327
theorem B1547311 : Blo 1545470 1547311 := bstep (se 1 (by rfl) ⟨1160483, by rfl⟩ : syracuseStep 1547311 = 2320967) B2320967
theorem B1858631 : Blo 1545470 1858631 := bstep (se 1 (by rfl) ⟨1393973, by rfl⟩ : syracuseStep 1858631 = 2787947) B2787947
theorem B1547335 : Blo 1545470 1547335 := bstep (se 1 (by rfl) ⟨1160501, by rfl⟩ : syracuseStep 1547335 = 2321003) B2321003
theorem B4406521 : Blo 1545470 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B5217533 : Blo 1545470 5217533 := bstep (se 3 (by rfl) ⟨978287, by rfl⟩ : syracuseStep 5217533 = 1956575) B1956575
theorem B3915175 : Blo 1545470 3915175 := bstep (se 1 (by rfl) ⟨2936381, by rfl⟩ : syracuseStep 3915175 = 5872763) B5872763
theorem B67788251 : Blo 1545470 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B3349991 : Blo 1545470 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B4177487 : Blo 1545470 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B19824425 : Blo 1545470 19824425 := bstep (se 2 (by rfl) ⟨7434159, by rfl⟩ : syracuseStep 19824425 = 14868319) B14868319
theorem B3481415 : Blo 1545470 3481415 := bstep (se 1 (by rfl) ⟨2611061, by rfl⟩ : syracuseStep 3481415 = 5222123) B5222123
theorem B2318303 : Blo 1545470 2318303 := bstep (se 1 (by rfl) ⟨1738727, by rfl⟩ : syracuseStep 2318303 = 3477455) B3477455
theorem B3301499 : Blo 1545470 3301499 := bstep (se 1 (by rfl) ⟨2476124, by rfl⟩ : syracuseStep 3301499 = 4952249) B4952249
theorem B2318543 : Blo 1545470 2318543 := bstep (se 1 (by rfl) ⟨1738907, by rfl⟩ : syracuseStep 2318543 = 3477815) B3477815
theorem B2318591 : Blo 1545470 2318591 := bstep (se 1 (by rfl) ⟨1738943, by rfl⟩ : syracuseStep 2318591 = 3477887) B3477887
theorem B7832051 : Blo 1545470 7832051 := bstep (se 1 (by rfl) ⟨5874038, by rfl⟩ : syracuseStep 7832051 = 11748077) B11748077
theorem B9912851 : Blo 1545470 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B6603373 : Blo 1545470 6603373 := bstep (se 3 (by rfl) ⟨1238132, by rfl⟩ : syracuseStep 6603373 = 2476265) B2476265
theorem B2351783 : Blo 1545470 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B19825397 : Blo 1545470 19825397 := bstep (se 5 (by rfl) ⟨929315, by rfl⟩ : syracuseStep 19825397 = 1858631) B1858631
theorem B6603545 : Blo 1545470 6603545 := bstep (se 2 (by rfl) ⟨2476329, by rfl⟩ : syracuseStep 6603545 = 4952659) B4952659
theorem B3916795 : Blo 1545470 3916795 := bstep (se 1 (by rfl) ⟨2937596, by rfl⟩ : syracuseStep 3916795 = 5875193) B5875193
theorem B5948425 : Blo 1545470 5948425 := bstep (se 2 (by rfl) ⟨2230659, by rfl⟩ : syracuseStep 5948425 = 4461319) B4461319
theorem B2319407 : Blo 1545470 2319407 := bstep (se 1 (by rfl) ⟨1739555, by rfl⟩ : syracuseStep 2319407 = 3479111) B3479111
theorem B56435777 : Blo 1545470 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B3302473 : Blo 1545470 3302473 := bstep (se 2 (by rfl) ⟨1238427, by rfl⟩ : syracuseStep 3302473 = 2476855) B2476855
theorem B2319527 : Blo 1545470 2319527 := bstep (se 1 (by rfl) ⟨1739645, by rfl⟩ : syracuseStep 2319527 = 3479291) B3479291
theorem B42927407 : Blo 1545470 42927407 := bstep (se 1 (by rfl) ⟨32195555, by rfl⟩ : syracuseStep 42927407 = 64391111) B64391111
theorem B7824923 : Blo 1545470 7824923 := bstep (se 1 (by rfl) ⟨5868692, by rfl⟩ : syracuseStep 7824923 = 11737385) B11737385
theorem B2319899 : Blo 1545470 2319899 := bstep (se 1 (by rfl) ⟨1739924, by rfl⟩ : syracuseStep 2319899 = 3479849) B3479849
theorem B2475625 : Blo 1545470 2475625 := bstep (se 2 (by rfl) ⟨928359, by rfl⟩ : syracuseStep 2475625 = 1856719) B1856719
theorem B2934377 : Blo 1545470 2934377 := bstep (se 2 (by rfl) ⟨1100391, by rfl⟩ : syracuseStep 2934377 = 2200783) B2200783
theorem B11740787 : Blo 1545470 11740787 := bstep (se 1 (by rfl) ⟨8805590, by rfl⟩ : syracuseStep 11740787 = 17611181) B17611181
theorem B5875361 : Blo 1545470 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B18810569 : Blo 1545470 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B7833347 : Blo 1545470 7833347 := bstep (se 1 (by rfl) ⟨5875010, by rfl⟩ : syracuseStep 7833347 = 11750021) B11750021
theorem B5220233 : Blo 1545470 5220233 := bstep (se 2 (by rfl) ⟨1957587, by rfl⟩ : syracuseStep 5220233 = 3915175) B3915175
theorem B2320283 : Blo 1545470 2320283 := bstep (se 1 (by rfl) ⟨1740212, by rfl⟩ : syracuseStep 2320283 = 3480425) B3480425
theorem B1738687 : Blo 1545470 1738687 := bstep (se 1 (by rfl) ⟨1304015, by rfl⟩ : syracuseStep 1738687 = 2608031) B2608031
theorem B2320319 : Blo 1545470 2320319 := bstep (se 1 (by rfl) ⟨1740239, by rfl⟩ : syracuseStep 2320319 = 3480479) B3480479
theorem B13207535 : Blo 1545470 13207535 := bstep (se 1 (by rfl) ⟨9905651, by rfl⟩ : syracuseStep 13207535 = 19811303) B19811303
theorem B4401179 : Blo 1545470 4401179 := bstep (se 1 (by rfl) ⟨3300884, by rfl⟩ : syracuseStep 4401179 = 6601769) B6601769
theorem B81446957 : Blo 1545470 81446957 := bstep (se 3 (by rfl) ⟨15271304, by rfl⟩ : syracuseStep 81446957 = 30542609) B30542609
theorem B12544109 : Blo 1545470 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B2320505 : Blo 1545470 2320505 := bstep (se 2 (by rfl) ⟨870189, by rfl⟩ : syracuseStep 2320505 = 1740379) B1740379
theorem B1738975 : Blo 1545470 1738975 := bstep (se 1 (by rfl) ⟨1304231, by rfl⟩ : syracuseStep 1738975 = 2608463) B2608463
theorem B6605135 : Blo 1545470 6605135 := bstep (se 1 (by rfl) ⟨4953851, by rfl⟩ : syracuseStep 6605135 = 9907703) B9907703
theorem B2320889 : Blo 1545470 2320889 := bstep (se 2 (by rfl) ⟨870333, by rfl⟩ : syracuseStep 2320889 = 1740667) B1740667
theorem B13216283 : Blo 1545470 13216283 := bstep (se 1 (by rfl) ⟨9912212, by rfl⟩ : syracuseStep 13216283 = 19824425) B19824425
theorem B2320943 : Blo 1545470 2320943 := bstep (se 1 (by rfl) ⟨1740707, by rfl⟩ : syracuseStep 2320943 = 3481415) B3481415
theorem B14305895 : Blo 1545470 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B2935433 : Blo 1545470 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B4704929 : Blo 1545470 4704929 := bstep (se 2 (by rfl) ⟨1764348, by rfl⟩ : syracuseStep 4704929 = 3528697) B3528697
theorem B6605819 : Blo 1545470 6605819 := bstep (se 1 (by rfl) ⟨4954364, by rfl⟩ : syracuseStep 6605819 = 9908729) B9908729
theorem B16731143 : Blo 1545470 16731143 := bstep (se 1 (by rfl) ⟨12548357, by rfl⟩ : syracuseStep 16731143 = 25096715) B25096715
theorem B3304489 : Blo 1545470 3304489 := bstep (se 2 (by rfl) ⟨1239183, by rfl⟩ : syracuseStep 3304489 = 2478367) B2478367
theorem B1739839 : Blo 1545470 1739839 := bstep (se 1 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 1739839 = 2609759) B2609759
theorem B26414585 : Blo 1545470 26414585 := bstep (se 2 (by rfl) ⟨9905469, by rfl⟩ : syracuseStep 26414585 = 19810939) B19810939
theorem B11750993 : Blo 1545470 11750993 := bstep (se 2 (by rfl) ⟨4406622, by rfl⟩ : syracuseStep 11750993 = 8813245) B8813245
theorem B7434023 : Blo 1545470 7434023 := bstep (se 1 (by rfl) ⟨5575517, by rfl⟩ : syracuseStep 7434023 = 11151035) B11151035
theorem B4403069 : Blo 1545470 4403069 := bstep (se 3 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 4403069 = 1651151) B1651151
theorem B2609023 : Blo 1545470 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B2936807 : Blo 1545470 2936807 := bstep (se 1 (by rfl) ⟨2202605, by rfl⟩ : syracuseStep 2936807 = 4405211) B4405211
theorem B28200955 : Blo 1545470 28200955 := bstep (se 1 (by rfl) ⟨21150716, by rfl⟩ : syracuseStep 28200955 = 42301433) B42301433
theorem B26423333 : Blo 1545470 26423333 := bstep (se 4 (by rfl) ⟨2477187, by rfl⟩ : syracuseStep 26423333 = 4954375) B4954375
theorem B3477599 : Blo 1545470 3477599 := bstep (se 1 (by rfl) ⟨2608199, by rfl⟩ : syracuseStep 3477599 = 5216399) B5216399
theorem B2609327 : Blo 1545470 2609327 := bstep (se 1 (by rfl) ⟨1956995, by rfl⟩ : syracuseStep 2609327 = 3913991) B3913991
theorem B6607133 : Blo 1545470 6607133 := bstep (se 3 (by rfl) ⟨1238837, by rfl⟩ : syracuseStep 6607133 = 2477675) B2477675
theorem B7827839 : Blo 1545470 7827839 := bstep (se 1 (by rfl) ⟨5870879, by rfl⟩ : syracuseStep 7827839 = 11741759) B11741759
theorem B4403639 : Blo 1545470 4403639 := bstep (se 1 (by rfl) ⟨3302729, by rfl⟩ : syracuseStep 4403639 = 6605459) B6605459
theorem B11907749 : Blo 1545470 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B5870333 : Blo 1545470 5870333 := bstep (se 3 (by rfl) ⟨1100687, by rfl⟩ : syracuseStep 5870333 = 2201375) B2201375
theorem B3478355 : Blo 1545470 3478355 := bstep (se 1 (by rfl) ⟨2608766, by rfl⟩ : syracuseStep 3478355 = 5217533) B5217533
theorem B45192167 : Blo 1545470 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B2233327 : Blo 1545470 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B3912745 : Blo 1545470 3912745 := bstep (se 2 (by rfl) ⟨1467279, by rfl⟩ : syracuseStep 3912745 = 2934559) B2934559
theorem B1545535 : Blo 1545470 1545535 := bstep (se 1 (by rfl) ⟨1159151, by rfl⟩ : syracuseStep 1545535 = 2318303) B2318303
theorem B3478895 : Blo 1545470 3478895 := bstep (se 1 (by rfl) ⟨2609171, by rfl⟩ : syracuseStep 3478895 = 5218343) B5218343
theorem B1545703 : Blo 1545470 1545703 := bstep (se 1 (by rfl) ⟨1159277, by rfl⟩ : syracuseStep 1545703 = 2318555) B2318555
theorem B1545711 : Blo 1545470 1545711 := bstep (se 1 (by rfl) ⟨1159283, by rfl⟩ : syracuseStep 1545711 = 2318567) B2318567
theorem B1857007 : Blo 1545470 1857007 := bstep (se 1 (by rfl) ⟨1392755, by rfl⟩ : syracuseStep 1857007 = 2785511) B2785511
theorem B1545819 : Blo 1545470 1545819 := bstep (se 1 (by rfl) ⟨1159364, by rfl⟩ : syracuseStep 1545819 = 2318729) B2318729
theorem B1545883 : Blo 1545470 1545883 := bstep (se 1 (by rfl) ⟨1159412, by rfl⟩ : syracuseStep 1545883 = 2318825) B2318825
theorem B1545967 : Blo 1545470 1545967 := bstep (se 1 (by rfl) ⟨1159475, by rfl⟩ : syracuseStep 1545967 = 2318951) B2318951
theorem B3479327 : Blo 1545470 3479327 := bstep (se 1 (by rfl) ⟨2609495, by rfl⟩ : syracuseStep 3479327 = 5218991) B5218991
theorem B1546055 : Blo 1545470 1546055 := bstep (se 1 (by rfl) ⟨1159541, by rfl⟩ : syracuseStep 1546055 = 2319083) B2319083
theorem B1546075 : Blo 1545470 1546075 := bstep (se 1 (by rfl) ⟨1159556, by rfl⟩ : syracuseStep 1546075 = 2319113) B2319113
theorem B1546143 : Blo 1545470 1546143 := bstep (se 1 (by rfl) ⟨1159607, by rfl⟩ : syracuseStep 1546143 = 2319215) B2319215
theorem B9910187 : Blo 1545470 9910187 := bstep (se 1 (by rfl) ⟨7432640, by rfl⟩ : syracuseStep 9910187 = 14865281) B14865281
theorem B8804315 : Blo 1545470 8804315 := bstep (se 1 (by rfl) ⟨6603236, by rfl⟩ : syracuseStep 8804315 = 13206473) B13206473
theorem B3479543 : Blo 1545470 3479543 := bstep (se 1 (by rfl) ⟨2609657, by rfl⟩ : syracuseStep 3479543 = 5219315) B5219315
theorem B1546311 : Blo 1545470 1546311 := bstep (se 1 (by rfl) ⟨1159733, by rfl⟩ : syracuseStep 1546311 = 2319467) B2319467
theorem B1546471 : Blo 1545470 1546471 := bstep (se 1 (by rfl) ⟨1159853, by rfl⟩ : syracuseStep 1546471 = 2319707) B2319707
theorem B6609235 : Blo 1545470 6609235 := bstep (se 1 (by rfl) ⟨4956926, by rfl⟩ : syracuseStep 6609235 = 9913853) B9913853
theorem B3479903 : Blo 1545470 3479903 := bstep (se 1 (by rfl) ⟨2609927, by rfl⟩ : syracuseStep 3479903 = 5219855) B5219855
theorem B1546655 : Blo 1545470 1546655 := bstep (se 1 (by rfl) ⟨1159991, by rfl⟩ : syracuseStep 1546655 = 2319983) B2319983
theorem B3914183 : Blo 1545470 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B4831687 : Blo 1545470 4831687 := bstep (se 1 (by rfl) ⟨3623765, by rfl⟩ : syracuseStep 4831687 = 7247531) B7247531
theorem B1546703 : Blo 1545470 1546703 := bstep (se 1 (by rfl) ⟨1160027, by rfl⟩ : syracuseStep 1546703 = 2320055) B2320055
theorem B1546727 : Blo 1545470 1546727 := bstep (se 1 (by rfl) ⟨1160045, by rfl⟩ : syracuseStep 1546727 = 2320091) B2320091
theorem B7830107 : Blo 1545470 7830107 := bstep (se 1 (by rfl) ⟨5872580, by rfl⟩ : syracuseStep 7830107 = 11745161) B11745161
theorem B1546843 : Blo 1545470 1546843 := bstep (se 1 (by rfl) ⟨1160132, by rfl⟩ : syracuseStep 1546843 = 2320265) B2320265
theorem B1546911 : Blo 1545470 1546911 := bstep (se 1 (by rfl) ⟨1160183, by rfl⟩ : syracuseStep 1546911 = 2320367) B2320367
theorem B4954877 : Blo 1545470 4954877 := bstep (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) B1858079
theorem B1547079 : Blo 1545470 1547079 := bstep (se 1 (by rfl) ⟨1160309, by rfl⟩ : syracuseStep 1547079 = 2320619) B2320619
theorem B1547119 : Blo 1545470 1547119 := bstep (se 1 (by rfl) ⟨1160339, by rfl⟩ : syracuseStep 1547119 = 2320679) B2320679
theorem B3480443 : Blo 1545470 3480443 := bstep (se 1 (by rfl) ⟨2610332, by rfl⟩ : syracuseStep 3480443 = 5220665) B5220665
theorem B1547175 : Blo 1545470 1547175 := bstep (se 1 (by rfl) ⟨1160381, by rfl⟩ : syracuseStep 1547175 = 2320763) B2320763
theorem B6880247 : Blo 1545470 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B3480623 : Blo 1545470 3480623 := bstep (se 1 (by rfl) ⟨2610467, by rfl⟩ : syracuseStep 3480623 = 5220935) B5220935
theorem B1547355 : Blo 1545470 1547355 := bstep (se 1 (by rfl) ⟨1160516, by rfl⟩ : syracuseStep 1547355 = 2321033) B2321033
theorem B7052615 : Blo 1545470 7052615 := bstep (se 1 (by rfl) ⟨5289461, by rfl⟩ : syracuseStep 7052615 = 10578923) B10578923
theorem B14867819 : Blo 1545470 14867819 := bstep (se 1 (by rfl) ⟨11150864, by rfl⟩ : syracuseStep 14867819 = 22301729) B22301729
theorem B100375919 : Blo 1545470 100375919 := bstep (se 1 (by rfl) ⟨75281939, by rfl⟩ : syracuseStep 100375919 = 150563879) B150563879
theorem B11738843 : Blo 1545470 11738843 := bstep (se 1 (by rfl) ⟨8804132, by rfl⟩ : syracuseStep 11738843 = 17608265) B17608265
theorem B3481307 : Blo 1545470 3481307 := bstep (se 1 (by rfl) ⟨2610980, by rfl⟩ : syracuseStep 3481307 = 5221961) B5221961
theorem B2784991 : Blo 1545470 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B3915641 : Blo 1545470 3915641 := bstep (se 2 (by rfl) ⟨1468365, by rfl⟩ : syracuseStep 3915641 = 2936731) B2936731
theorem B3481577 : Blo 1545470 3481577 := bstep (se 2 (by rfl) ⟨1305591, by rfl⟩ : syracuseStep 3481577 = 2611183) B2611183
theorem B2318399 : Blo 1545470 2318399 := bstep (se 1 (by rfl) ⟨1738799, by rfl⟩ : syracuseStep 2318399 = 3477599) B3477599
theorem B5218559 : Blo 1545470 5218559 := bstep (se 1 (by rfl) ⟨3913919, by rfl⟩ : syracuseStep 5218559 = 7827839) B7827839
theorem B2318633 : Blo 1545470 2318633 := bstep (se 2 (by rfl) ⟨869487, by rfl⟩ : syracuseStep 2318633 = 1738975) B1738975
theorem B7938499 : Blo 1545470 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B2318903 : Blo 1545470 2318903 := bstep (se 1 (by rfl) ⟨1739177, by rfl⟩ : syracuseStep 2318903 = 3478355) B3478355
theorem B2319263 : Blo 1545470 2319263 := bstep (se 1 (by rfl) ⟨1739447, by rfl⟩ : syracuseStep 2319263 = 3478895) B3478895
theorem B3916907 : Blo 1545470 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B2319551 : Blo 1545470 2319551 := bstep (se 1 (by rfl) ⟨1739663, by rfl⟩ : syracuseStep 2319551 = 3479327) B3479327
theorem B2319695 : Blo 1545470 2319695 := bstep (se 1 (by rfl) ⟨1739771, by rfl⟩ : syracuseStep 2319695 = 3479543) B3479543
theorem B7931233 : Blo 1545470 7931233 := bstep (se 2 (by rfl) ⟨2974212, by rfl⟩ : syracuseStep 7931233 = 5948425) B5948425
theorem B2934119 : Blo 1545470 2934119 := bstep (se 1 (by rfl) ⟨2200589, by rfl⟩ : syracuseStep 2934119 = 4401179) B4401179
theorem B54297971 : Blo 1545470 54297971 := bstep (se 1 (by rfl) ⟨40723478, by rfl⟩ : syracuseStep 54297971 = 81446957) B81446957
theorem B2319785 : Blo 1545470 2319785 := bstep (se 2 (by rfl) ⟨869919, by rfl⟩ : syracuseStep 2319785 = 1739839) B1739839
theorem B2319935 : Blo 1545470 2319935 := bstep (se 1 (by rfl) ⟨1739951, by rfl⟩ : syracuseStep 2319935 = 3479903) B3479903
theorem B5220071 : Blo 1545470 5220071 := bstep (se 1 (by rfl) ⟨3915053, by rfl⟩ : syracuseStep 5220071 = 7830107) B7830107
theorem B9537263 : Blo 1545470 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B3303251 : Blo 1545470 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B2320295 : Blo 1545470 2320295 := bstep (se 1 (by rfl) ⟨1740221, by rfl⟩ : syracuseStep 2320295 = 3480443) B3480443
theorem B2476009 : Blo 1545470 2476009 := bstep (se 2 (by rfl) ⟨928503, by rfl⟩ : syracuseStep 2476009 = 1857007) B1857007
theorem B2320415 : Blo 1545470 2320415 := bstep (se 1 (by rfl) ⟨1740311, by rfl⟩ : syracuseStep 2320415 = 3480623) B3480623
theorem B3713321 : Blo 1545470 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B7833995 : Blo 1545470 7833995 := bstep (se 1 (by rfl) ⟨5875496, by rfl⟩ : syracuseStep 7833995 = 11750993) B11750993
theorem B7825895 : Blo 1545470 7825895 := bstep (se 1 (by rfl) ⟨5869421, by rfl⟩ : syracuseStep 7825895 = 11738843) B11738843
theorem B2320871 : Blo 1545470 2320871 := bstep (se 1 (by rfl) ⟨1740653, by rfl⟩ : syracuseStep 2320871 = 3481307) B3481307
theorem B2935379 : Blo 1545470 2935379 := bstep (se 1 (by rfl) ⟨2201534, by rfl⟩ : syracuseStep 2935379 = 4403069) B4403069
theorem B2321051 : Blo 1545470 2321051 := bstep (se 1 (by rfl) ⟨1740788, by rfl⟩ : syracuseStep 2321051 = 3481577) B3481577
theorem B17615555 : Blo 1545470 17615555 := bstep (se 1 (by rfl) ⟨13211666, by rfl⟩ : syracuseStep 17615555 = 26423333) B26423333
theorem B1739551 : Blo 1545470 1739551 := bstep (se 1 (by rfl) ⟨1304663, by rfl⟩ : syracuseStep 1739551 = 2609327) B2609327
theorem B2935759 : Blo 1545470 2935759 := bstep (se 1 (by rfl) ⟨2201819, by rfl⟩ : syracuseStep 2935759 = 4403639) B4403639
theorem B5221367 : Blo 1545470 5221367 := bstep (se 1 (by rfl) ⟨3916025, by rfl⟩ : syracuseStep 5221367 = 7832051) B7832051
theorem B1567855 : Blo 1545470 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B13216931 : Blo 1545470 13216931 := bstep (se 1 (by rfl) ⟨9912698, by rfl⟩ : syracuseStep 13216931 = 19825397) B19825397
theorem B4402363 : Blo 1545470 4402363 := bstep (se 1 (by rfl) ⟨3301772, by rfl⟩ : syracuseStep 4402363 = 6603545) B6603545
theorem B6442249 : Blo 1545470 6442249 := bstep (se 2 (by rfl) ⟨2415843, by rfl⟩ : syracuseStep 6442249 = 4831687) B4831687
theorem B28618271 : Blo 1545470 28618271 := bstep (se 1 (by rfl) ⟨21463703, by rfl⟩ : syracuseStep 28618271 = 42927407) B42927407
theorem B7827191 : Blo 1545470 7827191 := bstep (se 1 (by rfl) ⟨5870393, by rfl⟩ : syracuseStep 7827191 = 11740787) B11740787
theorem B5222231 : Blo 1545470 5222231 := bstep (se 1 (by rfl) ⟨3916673, by rfl⟩ : syracuseStep 5222231 = 7833347) B7833347
theorem B6606791 : Blo 1545470 6606791 := bstep (se 1 (by rfl) ⟨4955093, by rfl⟩ : syracuseStep 6606791 = 9910187) B9910187
theorem B5869543 : Blo 1545470 5869543 := bstep (se 1 (by rfl) ⟨4402157, by rfl⟩ : syracuseStep 5869543 = 8804315) B8804315
theorem B2977769 : Blo 1545470 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B5222393 : Blo 1545470 5222393 := bstep (se 2 (by rfl) ⟨1958397, by rfl⟩ : syracuseStep 5222393 = 3916795) B3916795
theorem B4403297 : Blo 1545470 4403297 := bstep (se 2 (by rfl) ⟨1651236, by rfl⟩ : syracuseStep 4403297 = 3302473) B3302473
theorem B4403423 : Blo 1545470 4403423 := bstep (se 1 (by rfl) ⟨3302567, by rfl⟩ : syracuseStep 4403423 = 6605135) B6605135
theorem B2609455 : Blo 1545470 2609455 := bstep (se 1 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 2609455 = 3914183) B3914183
theorem B8810855 : Blo 1545470 8810855 := bstep (se 1 (by rfl) ⟨6608141, by rfl⟩ : syracuseStep 8810855 = 13216283) B13216283
theorem B4403879 : Blo 1545470 4403879 := bstep (se 1 (by rfl) ⟨3302909, by rfl⟩ : syracuseStep 4403879 = 6605819) B6605819
theorem B11154095 : Blo 1545470 11154095 := bstep (se 1 (by rfl) ⟨8365571, by rfl⟩ : syracuseStep 11154095 = 16731143) B16731143
theorem B66917279 : Blo 1545470 66917279 := bstep (se 1 (by rfl) ⟨50187959, by rfl⟩ : syracuseStep 66917279 = 100375919) B100375919
theorem B17609723 : Blo 1545470 17609723 := bstep (se 1 (by rfl) ⟨13207292, by rfl⟩ : syracuseStep 17609723 = 26414585) B26414585
theorem B3478697 : Blo 1545470 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B2610427 : Blo 1545470 2610427 := bstep (se 1 (by rfl) ⟨1957820, by rfl⟩ : syracuseStep 2610427 = 3915641) B3915641
theorem B1545695 : Blo 1545470 1545695 := bstep (se 1 (by rfl) ⟨1159271, by rfl⟩ : syracuseStep 1545695 = 2318543) B2318543
theorem B1545727 : Blo 1545470 1545727 := bstep (se 1 (by rfl) ⟨1159295, by rfl⟩ : syracuseStep 1545727 = 2318591) B2318591
theorem B4404755 : Blo 1545470 4404755 := bstep (se 1 (by rfl) ⟨3303566, by rfl⟩ : syracuseStep 4404755 = 6607133) B6607133
theorem B8803997 : Blo 1545470 8803997 := bstep (se 3 (by rfl) ⟨1650749, by rfl⟩ : syracuseStep 8803997 = 3301499) B3301499
theorem B6608567 : Blo 1545470 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B8812313 : Blo 1545470 8812313 := bstep (se 2 (by rfl) ⟨3304617, by rfl⟩ : syracuseStep 8812313 = 6609235) B6609235
theorem B3913555 : Blo 1545470 3913555 := bstep (se 1 (by rfl) ⟨2935166, by rfl⟩ : syracuseStep 3913555 = 5870333) B5870333
theorem B30128111 : Blo 1545470 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B1546271 : Blo 1545470 1546271 := bstep (se 1 (by rfl) ⟨1159703, by rfl⟩ : syracuseStep 1546271 = 2319407) B2319407
theorem B37623851 : Blo 1545470 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B1546351 : Blo 1545470 1546351 := bstep (se 1 (by rfl) ⟨1159763, by rfl⟩ : syracuseStep 1546351 = 2319527) B2319527
theorem B8804497 : Blo 1545470 8804497 := bstep (se 2 (by rfl) ⟨3301686, by rfl⟩ : syracuseStep 8804497 = 6603373) B6603373
theorem B5216615 : Blo 1545470 5216615 := bstep (se 1 (by rfl) ⟨3912461, by rfl⟩ : syracuseStep 5216615 = 7824923) B7824923
theorem B1546599 : Blo 1545470 1546599 := bstep (se 1 (by rfl) ⟨1159949, by rfl⟩ : syracuseStep 1546599 = 2319899) B2319899
theorem B1956251 : Blo 1545470 1956251 := bstep (se 1 (by rfl) ⟨1467188, by rfl⟩ : syracuseStep 1956251 = 2934377) B2934377
theorem B12540379 : Blo 1545470 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B3480155 : Blo 1545470 3480155 := bstep (se 1 (by rfl) ⟨2610116, by rfl⟩ : syracuseStep 3480155 = 5220233) B5220233
theorem B1546855 : Blo 1545470 1546855 := bstep (se 1 (by rfl) ⟨1160141, by rfl⟩ : syracuseStep 1546855 = 2320283) B2320283
theorem B1546879 : Blo 1545470 1546879 := bstep (se 1 (by rfl) ⟨1160159, by rfl⟩ : syracuseStep 1546879 = 2320319) B2320319
theorem B8805023 : Blo 1545470 8805023 := bstep (se 1 (by rfl) ⟨6603767, by rfl⟩ : syracuseStep 8805023 = 13207535) B13207535
theorem B5216993 : Blo 1545470 5216993 := bstep (se 2 (by rfl) ⟨1956372, by rfl⟩ : syracuseStep 5216993 = 3912745) B3912745
theorem B4405985 : Blo 1545470 4405985 := bstep (se 2 (by rfl) ⟨1652244, by rfl⟩ : syracuseStep 4405985 = 3304489) B3304489
theorem B8362739 : Blo 1545470 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B1547003 : Blo 1545470 1547003 := bstep (se 1 (by rfl) ⟨1160252, by rfl⟩ : syracuseStep 1547003 = 2320505) B2320505
theorem B1547259 : Blo 1545470 1547259 := bstep (se 1 (by rfl) ⟨1160444, by rfl⟩ : syracuseStep 1547259 = 2320889) B2320889
theorem B1547295 : Blo 1545470 1547295 := bstep (se 1 (by rfl) ⟨1160471, by rfl⟩ : syracuseStep 1547295 = 2320943) B2320943
theorem B1956955 : Blo 1545470 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B3136619 : Blo 1545470 3136619 := bstep (se 1 (by rfl) ⟨2352464, by rfl⟩ : syracuseStep 3136619 = 4704929) B4704929
theorem B4586831 : Blo 1545470 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B19824061 : Blo 1545470 19824061 := bstep (se 3 (by rfl) ⟨3717011, by rfl⟩ : syracuseStep 19824061 = 7434023) B7434023
theorem B3300833 : Blo 1545470 3300833 := bstep (se 2 (by rfl) ⟨1237812, by rfl⟩ : syracuseStep 3300833 = 2475625) B2475625
theorem B4701743 : Blo 1545470 4701743 := bstep (se 1 (by rfl) ⟨3526307, by rfl⟩ : syracuseStep 4701743 = 7052615) B7052615
theorem B9911879 : Blo 1545470 9911879 := bstep (se 1 (by rfl) ⟨7433909, by rfl⟩ : syracuseStep 9911879 = 14867819) B14867819
theorem B2318249 : Blo 1545470 2318249 := bstep (se 2 (by rfl) ⟨869343, by rfl⟩ : syracuseStep 2318249 = 1738687) B1738687
theorem B1957871 : Blo 1545470 1957871 := bstep (se 1 (by rfl) ⟨1468403, by rfl⟩ : syracuseStep 1957871 = 2936807) B2936807
theorem B37601273 : Blo 1545470 37601273 := bstep (se 2 (by rfl) ⟨14100477, by rfl⟩ : syracuseStep 37601273 = 28200955) B28200955
theorem B11739329 : Blo 1545470 11739329 := bstep (se 2 (by rfl) ⟨4402248, by rfl⟩ : syracuseStep 11739329 = 8804497) B8804497
theorem B5873903 : Blo 1545470 5873903 := bstep (se 1 (by rfl) ⟨4405427, by rfl⟩ : syracuseStep 5873903 = 8810855) B8810855
theorem B10584665 : Blo 1545470 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B16720505 : Blo 1545470 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B11739815 : Blo 1545470 11739815 := bstep (se 1 (by rfl) ⟨8804861, by rfl⟩ : syracuseStep 11739815 = 17609723) B17609723
theorem B2319131 : Blo 1545470 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B2319401 : Blo 1545470 2319401 := bstep (se 2 (by rfl) ⟨869775, by rfl⟩ : syracuseStep 2319401 = 1739551) B1739551
theorem B6358175 : Blo 1545470 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B5874875 : Blo 1545470 5874875 := bstep (se 1 (by rfl) ⟨4406156, by rfl⟩ : syracuseStep 5874875 = 8812313) B8812313
theorem B2090473 : Blo 1545470 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B2320103 : Blo 1545470 2320103 := bstep (se 1 (by rfl) ⟨1740077, by rfl⟩ : syracuseStep 2320103 = 3480155) B3480155
theorem B17622845 : Blo 1545470 17622845 := bstep (se 3 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 17622845 = 6608567) B6608567
theorem B2091079 : Blo 1545470 2091079 := bstep (se 1 (by rfl) ⟨1568309, by rfl⟩ : syracuseStep 2091079 = 3136619) B3136619
theorem B3057887 : Blo 1545470 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B3481595 : Blo 1545470 3481595 := bstep (se 1 (by rfl) ⟨2611196, by rfl⟩ : syracuseStep 3481595 = 5222393) B5222393
theorem B7940717 : Blo 1545470 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B5220989 : Blo 1545470 5220989 := bstep (se 3 (by rfl) ⟨978935, by rfl⟩ : syracuseStep 5220989 = 1957871) B1957871
theorem B7826057 : Blo 1545470 7826057 := bstep (se 2 (by rfl) ⟨2934771, by rfl⟩ : syracuseStep 7826057 = 5869543) B5869543
theorem B2935531 : Blo 1545470 2935531 := bstep (se 1 (by rfl) ⟨2201648, by rfl⟩ : syracuseStep 2935531 = 4403297) B4403297
theorem B2935615 : Blo 1545470 2935615 := bstep (se 1 (by rfl) ⟨2201711, by rfl⟩ : syracuseStep 2935615 = 4403423) B4403423
theorem B2935919 : Blo 1545470 2935919 := bstep (se 1 (by rfl) ⟨2201939, by rfl⟩ : syracuseStep 2935919 = 4403879) B4403879
theorem B2936503 : Blo 1545470 2936503 := bstep (se 1 (by rfl) ⟨2202377, by rfl⟩ : syracuseStep 2936503 = 4404755) B4404755
theorem B5869331 : Blo 1545470 5869331 := bstep (se 1 (by rfl) ⟨4401998, by rfl⟩ : syracuseStep 5869331 = 8803997) B8803997
theorem B2609273 : Blo 1545470 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B7827677 : Blo 1545470 7827677 := bstep (se 3 (by rfl) ⟨1467689, by rfl⟩ : syracuseStep 7827677 = 2935379) B2935379
theorem B3477743 : Blo 1545470 3477743 := bstep (se 1 (by rfl) ⟨2608307, by rfl⟩ : syracuseStep 3477743 = 5216615) B5216615
theorem B5869817 : Blo 1545470 5869817 := bstep (se 2 (by rfl) ⟨2201181, by rfl⟩ : syracuseStep 5869817 = 4402363) B4402363
theorem B5222663 : Blo 1545470 5222663 := bstep (se 1 (by rfl) ⟨3916997, by rfl⟩ : syracuseStep 5222663 = 7833995) B7833995
theorem B8589665 : Blo 1545470 8589665 := bstep (se 2 (by rfl) ⟨3221124, by rfl⟩ : syracuseStep 8589665 = 6442249) B6442249
theorem B5870015 : Blo 1545470 5870015 := bstep (se 1 (by rfl) ⟨4402511, by rfl⟩ : syracuseStep 5870015 = 8805023) B8805023
theorem B11743703 : Blo 1545470 11743703 := bstep (se 1 (by rfl) ⟨8807777, by rfl⟩ : syracuseStep 11743703 = 17615555) B17615555
theorem B3477995 : Blo 1545470 3477995 := bstep (se 1 (by rfl) ⟨2608496, by rfl⟩ : syracuseStep 3477995 = 5216993) B5216993
theorem B2937323 : Blo 1545470 2937323 := bstep (se 1 (by rfl) ⟨2202992, by rfl⟩ : syracuseStep 2937323 = 4405985) B4405985
theorem B5575159 : Blo 1545470 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B26432081 : Blo 1545470 26432081 := bstep (se 2 (by rfl) ⟨9912030, by rfl⟩ : syracuseStep 26432081 = 19824061) B19824061
theorem B8811287 : Blo 1545470 8811287 := bstep (se 1 (by rfl) ⟨6608465, by rfl⟩ : syracuseStep 8811287 = 13216931) B13216931
theorem B2200555 : Blo 1545470 2200555 := bstep (se 1 (by rfl) ⟨1650416, by rfl⟩ : syracuseStep 2200555 = 3300833) B3300833
theorem B3134495 : Blo 1545470 3134495 := bstep (se 1 (by rfl) ⟨2350871, by rfl⟩ : syracuseStep 3134495 = 4701743) B4701743
theorem B6607919 : Blo 1545470 6607919 := bstep (se 1 (by rfl) ⟨4955939, by rfl⟩ : syracuseStep 6607919 = 9911879) B9911879
theorem B1545499 : Blo 1545470 1545499 := bstep (se 1 (by rfl) ⟨1159124, by rfl⟩ : syracuseStep 1545499 = 2318249) B2318249
theorem B4404527 : Blo 1545470 4404527 := bstep (se 1 (by rfl) ⟨3303395, by rfl⟩ : syracuseStep 4404527 = 6606791) B6606791
theorem B1545599 : Blo 1545470 1545599 := bstep (se 1 (by rfl) ⟨1159199, by rfl⟩ : syracuseStep 1545599 = 2318399) B2318399
theorem B3479039 : Blo 1545470 3479039 := bstep (se 1 (by rfl) ⟨2609279, by rfl⟩ : syracuseStep 3479039 = 5218559) B5218559
theorem B1545755 : Blo 1545470 1545755 := bstep (se 1 (by rfl) ⟨1159316, by rfl⟩ : syracuseStep 1545755 = 2318633) B2318633
theorem B1545935 : Blo 1545470 1545935 := bstep (se 1 (by rfl) ⟨1159451, by rfl⟩ : syracuseStep 1545935 = 2318903) B2318903
theorem B3479273 : Blo 1545470 3479273 := bstep (se 2 (by rfl) ⟨1304727, by rfl⟩ : syracuseStep 3479273 = 2609455) B2609455
theorem B7436063 : Blo 1545470 7436063 := bstep (se 1 (by rfl) ⟨5577047, by rfl⟩ : syracuseStep 7436063 = 11154095) B11154095
theorem B1546175 : Blo 1545470 1546175 := bstep (se 1 (by rfl) ⟨1159631, by rfl⟩ : syracuseStep 1546175 = 2319263) B2319263
theorem B44611519 : Blo 1545470 44611519 := bstep (se 1 (by rfl) ⟨33458639, by rfl⟩ : syracuseStep 44611519 = 66917279) B66917279
theorem B2611271 : Blo 1545470 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B9902189 : Blo 1545470 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B1546367 : Blo 1545470 1546367 := bstep (se 1 (by rfl) ⟨1159775, by rfl⟩ : syracuseStep 1546367 = 2319551) B2319551
theorem B1546463 : Blo 1545470 1546463 := bstep (se 1 (by rfl) ⟨1159847, by rfl⟩ : syracuseStep 1546463 = 2319695) B2319695
theorem B1956079 : Blo 1545470 1956079 := bstep (se 1 (by rfl) ⟨1467059, by rfl⟩ : syracuseStep 1956079 = 2934119) B2934119
theorem B36198647 : Blo 1545470 36198647 := bstep (se 1 (by rfl) ⟨27148985, by rfl⟩ : syracuseStep 36198647 = 54297971) B54297971
theorem B1546523 : Blo 1545470 1546523 := bstep (se 1 (by rfl) ⟨1159892, by rfl⟩ : syracuseStep 1546523 = 2319785) B2319785
theorem B1546623 : Blo 1545470 1546623 := bstep (se 1 (by rfl) ⟨1159967, by rfl⟩ : syracuseStep 1546623 = 2319935) B2319935
theorem B5216669 : Blo 1545470 5216669 := bstep (se 3 (by rfl) ⟨978125, by rfl⟩ : syracuseStep 5216669 = 1956251) B1956251
theorem B3480047 : Blo 1545470 3480047 := bstep (se 1 (by rfl) ⟨2610035, by rfl⟩ : syracuseStep 3480047 = 5220071) B5220071
theorem B2202167 : Blo 1545470 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B3914345 : Blo 1545470 3914345 := bstep (se 2 (by rfl) ⟨1467879, by rfl⟩ : syracuseStep 3914345 = 2935759) B2935759
theorem B1546863 : Blo 1545470 1546863 := bstep (se 1 (by rfl) ⟨1160147, by rfl⟩ : syracuseStep 1546863 = 2320295) B2320295
theorem B20085407 : Blo 1545470 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B1546943 : Blo 1545470 1546943 := bstep (se 1 (by rfl) ⟨1160207, by rfl⟩ : syracuseStep 1546943 = 2320415) B2320415
theorem B25082567 : Blo 1545470 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B5217263 : Blo 1545470 5217263 := bstep (se 1 (by rfl) ⟨3912947, by rfl⟩ : syracuseStep 5217263 = 7825895) B7825895
theorem B1547247 : Blo 1545470 1547247 := bstep (se 1 (by rfl) ⟨1160435, by rfl⟩ : syracuseStep 1547247 = 2320871) B2320871
theorem B3480569 : Blo 1545470 3480569 := bstep (se 2 (by rfl) ⟨1305213, by rfl⟩ : syracuseStep 3480569 = 2610427) B2610427
theorem B1547367 : Blo 1545470 1547367 := bstep (se 1 (by rfl) ⟨1160525, by rfl⟩ : syracuseStep 1547367 = 2321051) B2321051
theorem B10574977 : Blo 1545470 10574977 := bstep (se 2 (by rfl) ⟨3965616, by rfl⟩ : syracuseStep 10574977 = 7931233) B7931233
theorem B3480911 : Blo 1545470 3480911 := bstep (se 1 (by rfl) ⟨2610683, by rfl⟩ : syracuseStep 3480911 = 5221367) B5221367
theorem B19078847 : Blo 1545470 19078847 := bstep (se 1 (by rfl) ⟨14309135, by rfl⟩ : syracuseStep 19078847 = 28618271) B28618271
theorem B5218073 : Blo 1545470 5218073 := bstep (se 2 (by rfl) ⟨1956777, by rfl⟩ : syracuseStep 5218073 = 3913555) B3913555
theorem B5218127 : Blo 1545470 5218127 := bstep (se 1 (by rfl) ⟨3913595, by rfl⟩ : syracuseStep 5218127 = 7827191) B7827191
theorem B3481487 : Blo 1545470 3481487 := bstep (se 1 (by rfl) ⟨2611115, by rfl⟩ : syracuseStep 3481487 = 5222231) B5222231
theorem B3301345 : Blo 1545470 3301345 := bstep (se 2 (by rfl) ⟨1238004, by rfl⟩ : syracuseStep 3301345 = 2476009) B2476009
theorem B25067515 : Blo 1545470 25067515 := bstep (se 1 (by rfl) ⟨18800636, by rfl⟩ : syracuseStep 25067515 = 37601273) B37601273
theorem B5218451 : Blo 1545470 5218451 := bstep (se 1 (by rfl) ⟨3913838, by rfl⟩ : syracuseStep 5218451 = 7827677) B7827677
theorem B2318495 : Blo 1545470 2318495 := bstep (se 1 (by rfl) ⟨1738871, by rfl⟩ : syracuseStep 2318495 = 3477743) B3477743
theorem B3915935 : Blo 1545470 3915935 := bstep (se 1 (by rfl) ⟨2936951, by rfl⟩ : syracuseStep 3915935 = 5873903) B5873903
theorem B3481775 : Blo 1545470 3481775 := bstep (se 1 (by rfl) ⟨2611331, by rfl⟩ : syracuseStep 3481775 = 5222663) B5222663
theorem B2318663 : Blo 1545470 2318663 := bstep (se 1 (by rfl) ⟨1738997, by rfl⟩ : syracuseStep 2318663 = 3477995) B3477995
theorem B17621387 : Blo 1545470 17621387 := bstep (se 1 (by rfl) ⟨13216040, by rfl⟩ : syracuseStep 17621387 = 26432081) B26432081
theorem B5874191 : Blo 1545470 5874191 := bstep (se 1 (by rfl) ⟨4405643, by rfl⟩ : syracuseStep 5874191 = 8811287) B8811287
theorem B3916583 : Blo 1545470 3916583 := bstep (se 1 (by rfl) ⟨2937437, by rfl⟩ : syracuseStep 3916583 = 5874875) B5874875
theorem B22905773 : Blo 1545470 22905773 := bstep (se 3 (by rfl) ⟨4294832, by rfl⟩ : syracuseStep 22905773 = 8589665) B8589665
theorem B2319359 : Blo 1545470 2319359 := bstep (se 1 (by rfl) ⟨1739519, by rfl⟩ : syracuseStep 2319359 = 3479039) B3479039
theorem B2319515 : Blo 1545470 2319515 := bstep (se 1 (by rfl) ⟨1739636, by rfl⟩ : syracuseStep 2319515 = 3479273) B3479273
theorem B4957375 : Blo 1545470 4957375 := bstep (se 1 (by rfl) ⟨3718031, by rfl⟩ : syracuseStep 4957375 = 7436063) B7436063
theorem B11748563 : Blo 1545470 11748563 := bstep (se 1 (by rfl) ⟨8811422, by rfl⟩ : syracuseStep 11748563 = 17622845) B17622845
theorem B7832861 : Blo 1545470 7832861 := bstep (se 3 (by rfl) ⟨1468661, by rfl⟩ : syracuseStep 7832861 = 2937323) B2937323
theorem B2934073 : Blo 1545470 2934073 := bstep (se 2 (by rfl) ⟨1100277, by rfl⟩ : syracuseStep 2934073 = 2200555) B2200555
theorem B14099969 : Blo 1545470 14099969 := bstep (se 2 (by rfl) ⟨5287488, by rfl⟩ : syracuseStep 14099969 = 10574977) B10574977
theorem B2320031 : Blo 1545470 2320031 := bstep (se 1 (by rfl) ⟨1740023, by rfl⟩ : syracuseStep 2320031 = 3480047) B3480047
theorem B5293811 : Blo 1545470 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B16721711 : Blo 1545470 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B2320379 : Blo 1545470 2320379 := bstep (se 1 (by rfl) ⟨1740284, by rfl⟩ : syracuseStep 2320379 = 3480569) B3480569
theorem B2320607 : Blo 1545470 2320607 := bstep (se 1 (by rfl) ⟨1740455, by rfl⟩ : syracuseStep 2320607 = 3480911) B3480911
theorem B2320991 : Blo 1545470 2320991 := bstep (se 1 (by rfl) ⟨1740743, by rfl⟩ : syracuseStep 2320991 = 3481487) B3481487
theorem B4401793 : Blo 1545470 4401793 := bstep (se 2 (by rfl) ⟨1650672, by rfl⟩ : syracuseStep 4401793 = 3301345) B3301345
theorem B2321063 : Blo 1545470 2321063 := bstep (se 1 (by rfl) ⟨1740797, by rfl⟩ : syracuseStep 2321063 = 3481595) B3481595
theorem B1739515 : Blo 1545470 1739515 := bstep (se 1 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 1739515 = 2609273) B2609273
theorem B8358653 : Blo 1545470 8358653 := bstep (se 3 (by rfl) ⟨1567247, by rfl⟩ : syracuseStep 8358653 = 3134495) B3134495
theorem B2788105 : Blo 1545470 2788105 := bstep (se 2 (by rfl) ⟨1045539, by rfl⟩ : syracuseStep 2788105 = 2091079) B2091079
theorem B7826219 : Blo 1545470 7826219 := bstep (se 1 (by rfl) ⟨5869664, by rfl⟩ : syracuseStep 7826219 = 11739329) B11739329
theorem B26405837 : Blo 1545470 26405837 := bstep (se 3 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 26405837 = 9902189) B9902189
theorem B2608105 : Blo 1545470 2608105 := bstep (se 2 (by rfl) ⟨978039, by rfl⟩ : syracuseStep 2608105 = 1956079) B1956079
theorem B7056443 : Blo 1545470 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B7826543 : Blo 1545470 7826543 := bstep (se 1 (by rfl) ⟨5869907, by rfl⟩ : syracuseStep 7826543 = 11739815) B11739815
theorem B7433545 : Blo 1545470 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B4238783 : Blo 1545470 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B2936351 : Blo 1545470 2936351 := bstep (se 1 (by rfl) ⟨2202263, by rfl⟩ : syracuseStep 2936351 = 4404527) B4404527
theorem B33423353 : Blo 1545470 33423353 := bstep (se 2 (by rfl) ⟨12533757, by rfl⟩ : syracuseStep 33423353 = 25067515) B25067515
theorem B1740847 : Blo 1545470 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B3477779 : Blo 1545470 3477779 := bstep (se 1 (by rfl) ⟨2608334, by rfl⟩ : syracuseStep 3477779 = 5216669) B5216669
theorem B2609563 : Blo 1545470 2609563 := bstep (se 1 (by rfl) ⟨1957172, by rfl⟩ : syracuseStep 2609563 = 3914345) B3914345
theorem B13390271 : Blo 1545470 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B3478175 : Blo 1545470 3478175 := bstep (se 1 (by rfl) ⟨2608631, by rfl⟩ : syracuseStep 3478175 = 5217263) B5217263
theorem B12719231 : Blo 1545470 12719231 := bstep (se 1 (by rfl) ⟨9539423, by rfl⟩ : syracuseStep 12719231 = 19078847) B19078847
theorem B3912887 : Blo 1545470 3912887 := bstep (se 1 (by rfl) ⟨2934665, by rfl⟩ : syracuseStep 3912887 = 5869331) B5869331
theorem B3478715 : Blo 1545470 3478715 := bstep (se 1 (by rfl) ⟨2609036, by rfl⟩ : syracuseStep 3478715 = 5218073) B5218073
theorem B3478751 : Blo 1545470 3478751 := bstep (se 1 (by rfl) ⟨2609063, by rfl⟩ : syracuseStep 3478751 = 5218127) B5218127
theorem B3913211 : Blo 1545470 3913211 := bstep (se 1 (by rfl) ⟨2934908, by rfl⟩ : syracuseStep 3913211 = 5869817) B5869817
theorem B3913343 : Blo 1545470 3913343 := bstep (se 1 (by rfl) ⟨2935007, by rfl⟩ : syracuseStep 3913343 = 5870015) B5870015
theorem B7829135 : Blo 1545470 7829135 := bstep (se 1 (by rfl) ⟨5871851, by rfl⟩ : syracuseStep 7829135 = 11743703) B11743703
theorem B11147003 : Blo 1545470 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B1546087 : Blo 1545470 1546087 := bstep (se 1 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 1546087 = 2319131) B2319131
theorem B1546267 : Blo 1545470 1546267 := bstep (se 1 (by rfl) ⟨1159700, by rfl⟩ : syracuseStep 1546267 = 2319401) B2319401
theorem B4405279 : Blo 1545470 4405279 := bstep (se 1 (by rfl) ⟨3303959, by rfl⟩ : syracuseStep 4405279 = 6607919) B6607919
theorem B3914041 : Blo 1545470 3914041 := bstep (se 2 (by rfl) ⟨1467765, by rfl⟩ : syracuseStep 3914041 = 2935531) B2935531
theorem B3914153 : Blo 1545470 3914153 := bstep (se 2 (by rfl) ⟨1467807, by rfl⟩ : syracuseStep 3914153 = 2935615) B2935615
theorem B1546735 : Blo 1545470 1546735 := bstep (se 1 (by rfl) ⟨1160051, by rfl⟩ : syracuseStep 1546735 = 2320103) B2320103
theorem B5872445 : Blo 1545470 5872445 := bstep (se 3 (by rfl) ⟨1101083, by rfl⟩ : syracuseStep 5872445 = 2202167) B2202167
theorem B2038591 : Blo 1545470 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B24132431 : Blo 1545470 24132431 := bstep (se 1 (by rfl) ⟨18099323, by rfl⟩ : syracuseStep 24132431 = 36198647) B36198647
theorem B3480659 : Blo 1545470 3480659 := bstep (se 1 (by rfl) ⟨2610494, by rfl⟩ : syracuseStep 3480659 = 5220989) B5220989
theorem B5217371 : Blo 1545470 5217371 := bstep (se 1 (by rfl) ⟨3913028, by rfl⟩ : syracuseStep 5217371 = 7826057) B7826057
theorem B1957279 : Blo 1545470 1957279 := bstep (se 1 (by rfl) ⟨1467959, by rfl⟩ : syracuseStep 1957279 = 2935919) B2935919
theorem B44596757 : Blo 1545470 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B3915337 : Blo 1545470 3915337 := bstep (se 2 (by rfl) ⟨1468251, by rfl⟩ : syracuseStep 3915337 = 2936503) B2936503
theorem B59482025 : Blo 1545470 59482025 := bstep (se 2 (by rfl) ⟨22305759, by rfl⟩ : syracuseStep 59482025 = 44611519) B44611519
theorem B5873705 : Blo 1545470 5873705 := bstep (se 2 (by rfl) ⟨2202639, by rfl⟩ : syracuseStep 5873705 = 4405279) B4405279
theorem B18817181 : Blo 1545470 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B2318519 : Blo 1545470 2318519 := bstep (se 1 (by rfl) ⟨1738889, by rfl⟩ : syracuseStep 2318519 = 3477779) B3477779
theorem B11747591 : Blo 1545470 11747591 := bstep (se 1 (by rfl) ⟨8810693, by rfl⟩ : syracuseStep 11747591 = 17621387) B17621387
theorem B3916127 : Blo 1545470 3916127 := bstep (se 1 (by rfl) ⟨2937095, by rfl⟩ : syracuseStep 3916127 = 5874191) B5874191
theorem B5218721 : Blo 1545470 5218721 := bstep (se 2 (by rfl) ⟨1957020, by rfl⟩ : syracuseStep 5218721 = 3914041) B3914041
theorem B2318783 : Blo 1545470 2318783 := bstep (se 1 (by rfl) ⟨1739087, by rfl⟩ : syracuseStep 2318783 = 3478175) B3478175
theorem B15270515 : Blo 1545470 15270515 := bstep (se 1 (by rfl) ⟨11452886, by rfl⟩ : syracuseStep 15270515 = 22905773) B22905773
theorem B8479487 : Blo 1545470 8479487 := bstep (se 1 (by rfl) ⟨6359615, by rfl⟩ : syracuseStep 8479487 = 12719231) B12719231
theorem B2319143 : Blo 1545470 2319143 := bstep (se 1 (by rfl) ⟨1739357, by rfl⟩ : syracuseStep 2319143 = 3478715) B3478715
theorem B7832375 : Blo 1545470 7832375 := bstep (se 1 (by rfl) ⟨5874281, by rfl⟩ : syracuseStep 7832375 = 11748563) B11748563
theorem B2319167 : Blo 1545470 2319167 := bstep (se 1 (by rfl) ⟨1739375, by rfl⟩ : syracuseStep 2319167 = 3478751) B3478751
theorem B2319353 : Blo 1545470 2319353 := bstep (se 2 (by rfl) ⟨869757, by rfl⟩ : syracuseStep 2319353 = 1739515) B1739515
theorem B5219423 : Blo 1545470 5219423 := bstep (se 1 (by rfl) ⟨3914567, by rfl⟩ : syracuseStep 5219423 = 7829135) B7829135
theorem B7431335 : Blo 1545470 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B10872485 : Blo 1545470 10872485 := bstep (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) B2038591
theorem B5572435 : Blo 1545470 5572435 := bstep (se 1 (by rfl) ⟨4179326, by rfl⟩ : syracuseStep 5572435 = 8358653) B8358653
theorem B2320439 : Blo 1545470 2320439 := bstep (se 1 (by rfl) ⟨1740329, by rfl⟩ : syracuseStep 2320439 = 3480659) B3480659
theorem B5220449 : Blo 1545470 5220449 := bstep (se 2 (by rfl) ⟨1957668, by rfl⟩ : syracuseStep 5220449 = 3915337) B3915337
theorem B29731171 : Blo 1545470 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B2321129 : Blo 1545470 2321129 := bstep (se 2 (by rfl) ⟨870423, by rfl⟩ : syracuseStep 2321129 = 1740847) B1740847
theorem B2321183 : Blo 1545470 2321183 := bstep (se 1 (by rfl) ⟨1740887, by rfl⟩ : syracuseStep 2321183 = 3481775) B3481775
theorem B2608591 : Blo 1545470 2608591 := bstep (se 1 (by rfl) ⟨1956443, by rfl⟩ : syracuseStep 2608591 = 3912887) B3912887
theorem B5869057 : Blo 1545470 5869057 := bstep (se 2 (by rfl) ⟨2200896, by rfl⟩ : syracuseStep 5869057 = 4401793) B4401793
theorem B5221907 : Blo 1545470 5221907 := bstep (se 1 (by rfl) ⟨3916430, by rfl⟩ : syracuseStep 5221907 = 7832861) B7832861
theorem B2608807 : Blo 1545470 2608807 := bstep (se 1 (by rfl) ⟨1956605, by rfl⟩ : syracuseStep 2608807 = 3913211) B3913211
theorem B9399979 : Blo 1545470 9399979 := bstep (se 1 (by rfl) ⟨7049984, by rfl⟩ : syracuseStep 9399979 = 14099969) B14099969
theorem B2608895 : Blo 1545470 2608895 := bstep (se 1 (by rfl) ⟨1956671, by rfl⟩ : syracuseStep 2608895 = 3913343) B3913343
theorem B3477473 : Blo 1545470 3477473 := bstep (se 2 (by rfl) ⟨1304052, by rfl⟩ : syracuseStep 3477473 = 2608105) B2608105
theorem B2609435 : Blo 1545470 2609435 := bstep (se 1 (by rfl) ⟨1957076, by rfl⟩ : syracuseStep 2609435 = 3914153) B3914153
theorem B3912097 : Blo 1545470 3912097 := bstep (se 2 (by rfl) ⟨1467036, by rfl⟩ : syracuseStep 3912097 = 2934073) B2934073
theorem B2609705 : Blo 1545470 2609705 := bstep (se 2 (by rfl) ⟨978639, by rfl⟩ : syracuseStep 2609705 = 1957279) B1957279
theorem B3478247 : Blo 1545470 3478247 := bstep (se 1 (by rfl) ⟨2608685, by rfl⟩ : syracuseStep 3478247 = 5217371) B5217371
theorem B64353149 : Blo 1545470 64353149 := bstep (se 3 (by rfl) ⟨12066215, by rfl⟩ : syracuseStep 64353149 = 24132431) B24132431
theorem B39654683 : Blo 1545470 39654683 := bstep (se 1 (by rfl) ⟨29741012, by rfl⟩ : syracuseStep 39654683 = 59482025) B59482025
theorem B3478967 : Blo 1545470 3478967 := bstep (se 1 (by rfl) ⟨2609225, by rfl⟩ : syracuseStep 3478967 = 5218451) B5218451
theorem B1545663 : Blo 1545470 1545663 := bstep (se 1 (by rfl) ⟨1159247, by rfl⟩ : syracuseStep 1545663 = 2318495) B2318495
theorem B2610623 : Blo 1545470 2610623 := bstep (se 1 (by rfl) ⟨1957967, by rfl⟩ : syracuseStep 2610623 = 3915935) B3915935
theorem B1545775 : Blo 1545470 1545775 := bstep (se 1 (by rfl) ⟨1159331, by rfl⟩ : syracuseStep 1545775 = 2318663) B2318663
theorem B8926847 : Blo 1545470 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B2611055 : Blo 1545470 2611055 := bstep (se 1 (by rfl) ⟨1958291, by rfl⟩ : syracuseStep 2611055 = 3916583) B3916583
theorem B3479417 : Blo 1545470 3479417 := bstep (se 2 (by rfl) ⟨1304781, by rfl⟩ : syracuseStep 3479417 = 2609563) B2609563
theorem B1546239 : Blo 1545470 1546239 := bstep (se 1 (by rfl) ⟨1159679, by rfl⟩ : syracuseStep 1546239 = 2319359) B2319359
theorem B1546343 : Blo 1545470 1546343 := bstep (se 1 (by rfl) ⟨1159757, by rfl⟩ : syracuseStep 1546343 = 2319515) B2319515
theorem B3717473 : Blo 1545470 3717473 := bstep (se 2 (by rfl) ⟨1394052, by rfl⟩ : syracuseStep 3717473 = 2788105) B2788105
theorem B1546687 : Blo 1545470 1546687 := bstep (se 1 (by rfl) ⟨1160015, by rfl⟩ : syracuseStep 1546687 = 2320031) B2320031
theorem B3529207 : Blo 1545470 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B11147807 : Blo 1545470 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B1546919 : Blo 1545470 1546919 := bstep (se 1 (by rfl) ⟨1160189, by rfl⟩ : syracuseStep 1546919 = 2320379) B2320379
theorem B7830269 : Blo 1545470 7830269 := bstep (se 3 (by rfl) ⟨1468175, by rfl⟩ : syracuseStep 7830269 = 2936351) B2936351
theorem B1547071 : Blo 1545470 1547071 := bstep (se 1 (by rfl) ⟨1160303, by rfl⟩ : syracuseStep 1547071 = 2320607) B2320607
theorem B6609833 : Blo 1545470 6609833 := bstep (se 2 (by rfl) ⟨2478687, by rfl⟩ : syracuseStep 6609833 = 4957375) B4957375
theorem B1547327 : Blo 1545470 1547327 := bstep (se 1 (by rfl) ⟨1160495, by rfl⟩ : syracuseStep 1547327 = 2320991) B2320991
theorem B9911393 : Blo 1545470 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B1547375 : Blo 1545470 1547375 := bstep (se 1 (by rfl) ⟨1160531, by rfl⟩ : syracuseStep 1547375 = 2321063) B2321063
theorem B5217479 : Blo 1545470 5217479 := bstep (se 1 (by rfl) ⟨3913109, by rfl⟩ : syracuseStep 5217479 = 7826219) B7826219
theorem B3914963 : Blo 1545470 3914963 := bstep (se 1 (by rfl) ⟨2936222, by rfl⟩ : syracuseStep 3914963 = 5872445) B5872445
theorem B17603891 : Blo 1545470 17603891 := bstep (se 1 (by rfl) ⟨13202918, by rfl⟩ : syracuseStep 17603891 = 26405837) B26405837
theorem B5217695 : Blo 1545470 5217695 := bstep (se 1 (by rfl) ⟨3913271, by rfl⟩ : syracuseStep 5217695 = 7826543) B7826543
theorem B2825855 : Blo 1545470 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B22282235 : Blo 1545470 22282235 := bstep (se 1 (by rfl) ⟨16711676, by rfl⟩ : syracuseStep 22282235 = 33423353) B33423353
theorem B3915803 : Blo 1545470 3915803 := bstep (se 1 (by rfl) ⟨2936852, by rfl⟩ : syracuseStep 3915803 = 5873705) B5873705
theorem B7831727 : Blo 1545470 7831727 := bstep (se 1 (by rfl) ⟨5873795, by rfl⟩ : syracuseStep 7831727 = 11747591) B11747591
theorem B39641561 : Blo 1545470 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B2318831 : Blo 1545470 2318831 := bstep (se 1 (by rfl) ⟨1739123, by rfl⟩ : syracuseStep 2318831 = 3478247) B3478247
theorem B5652991 : Blo 1545470 5652991 := bstep (se 1 (by rfl) ⟨4239743, by rfl⟩ : syracuseStep 5652991 = 8479487) B8479487
theorem B42902099 : Blo 1545470 42902099 := bstep (se 1 (by rfl) ⟨32176574, by rfl⟩ : syracuseStep 42902099 = 64353149) B64353149
theorem B26436455 : Blo 1545470 26436455 := bstep (se 1 (by rfl) ⟨19827341, by rfl⟩ : syracuseStep 26436455 = 39654683) B39654683
theorem B9913261 : Blo 1545470 9913261 := bstep (se 3 (by rfl) ⟨1858736, by rfl⟩ : syracuseStep 9913261 = 3717473) B3717473
theorem B2319311 : Blo 1545470 2319311 := bstep (se 1 (by rfl) ⟨1739483, by rfl⟩ : syracuseStep 2319311 = 3478967) B3478967
theorem B2319611 : Blo 1545470 2319611 := bstep (se 1 (by rfl) ⟨1739708, by rfl⟩ : syracuseStep 2319611 = 3479417) B3479417
theorem B7431871 : Blo 1545470 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B5220179 : Blo 1545470 5220179 := bstep (se 1 (by rfl) ⟨3915134, by rfl⟩ : syracuseStep 5220179 = 7830269) B7830269
theorem B7825409 : Blo 1545470 7825409 := bstep (se 2 (by rfl) ⟨2934528, by rfl⟩ : syracuseStep 7825409 = 5869057) B5869057
theorem B1739263 : Blo 1545470 1739263 := bstep (se 1 (by rfl) ⟨1304447, by rfl⟩ : syracuseStep 1739263 = 2608895) B2608895
theorem B14854823 : Blo 1545470 14854823 := bstep (se 1 (by rfl) ⟨11141117, by rfl⟩ : syracuseStep 14854823 = 22282235) B22282235
theorem B12544787 : Blo 1545470 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B1739623 : Blo 1545470 1739623 := bstep (se 1 (by rfl) ⟨1304717, by rfl⟩ : syracuseStep 1739623 = 2609435) B2609435
theorem B1739803 : Blo 1545470 1739803 := bstep (se 1 (by rfl) ⟨1304852, by rfl⟩ : syracuseStep 1739803 = 2609705) B2609705
theorem B5221583 : Blo 1545470 5221583 := bstep (se 1 (by rfl) ⟨3916187, by rfl⟩ : syracuseStep 5221583 = 7832375) B7832375
theorem B4705609 : Blo 1545470 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B1740415 : Blo 1545470 1740415 := bstep (se 1 (by rfl) ⟨1305311, by rfl⟩ : syracuseStep 1740415 = 2610623) B2610623
theorem B5951231 : Blo 1545470 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B1740703 : Blo 1545470 1740703 := bstep (se 1 (by rfl) ⟨1305527, by rfl⟩ : syracuseStep 1740703 = 2611055) B2611055
theorem B3478121 : Blo 1545470 3478121 := bstep (se 2 (by rfl) ⟨1304295, by rfl⟩ : syracuseStep 3478121 = 2608591) B2608591
theorem B6607595 : Blo 1545470 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B3478319 : Blo 1545470 3478319 := bstep (se 1 (by rfl) ⟨2608739, by rfl⟩ : syracuseStep 3478319 = 5217479) B5217479
theorem B2609975 : Blo 1545470 2609975 := bstep (se 1 (by rfl) ⟨1957481, by rfl⟩ : syracuseStep 2609975 = 3914963) B3914963
theorem B11735927 : Blo 1545470 11735927 := bstep (se 1 (by rfl) ⟨8801945, by rfl⟩ : syracuseStep 11735927 = 17603891) B17603891
theorem B3478409 : Blo 1545470 3478409 := bstep (se 2 (by rfl) ⟨1304403, by rfl⟩ : syracuseStep 3478409 = 2608807) B2608807
theorem B3478463 : Blo 1545470 3478463 := bstep (se 1 (by rfl) ⟨2608847, by rfl⟩ : syracuseStep 3478463 = 5217695) B5217695
theorem B1545679 : Blo 1545470 1545679 := bstep (se 1 (by rfl) ⟨1159259, by rfl⟩ : syracuseStep 1545679 = 2318519) B2318519
theorem B2610751 : Blo 1545470 2610751 := bstep (se 1 (by rfl) ⟨1958063, by rfl⟩ : syracuseStep 2610751 = 3916127) B3916127
theorem B3479147 : Blo 1545470 3479147 := bstep (se 1 (by rfl) ⟨2609360, by rfl⟩ : syracuseStep 3479147 = 5218721) B5218721
theorem B1545855 : Blo 1545470 1545855 := bstep (se 1 (by rfl) ⟨1159391, by rfl⟩ : syracuseStep 1545855 = 2318783) B2318783
theorem B10180343 : Blo 1545470 10180343 := bstep (se 1 (by rfl) ⟨7635257, by rfl⟩ : syracuseStep 10180343 = 15270515) B15270515
theorem B1546095 : Blo 1545470 1546095 := bstep (se 1 (by rfl) ⟨1159571, by rfl⟩ : syracuseStep 1546095 = 2319143) B2319143
theorem B1546111 : Blo 1545470 1546111 := bstep (se 1 (by rfl) ⟨1159583, by rfl⟩ : syracuseStep 1546111 = 2319167) B2319167
theorem B5216129 : Blo 1545470 5216129 := bstep (se 2 (by rfl) ⟨1956048, by rfl⟩ : syracuseStep 5216129 = 3912097) B3912097
theorem B1546235 : Blo 1545470 1546235 := bstep (se 1 (by rfl) ⟨1159676, by rfl⟩ : syracuseStep 1546235 = 2319353) B2319353
theorem B3479615 : Blo 1545470 3479615 := bstep (se 1 (by rfl) ⟨2609711, by rfl⟩ : syracuseStep 3479615 = 5219423) B5219423
theorem B4954223 : Blo 1545470 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B7248323 : Blo 1545470 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B1546959 : Blo 1545470 1546959 := bstep (se 1 (by rfl) ⟨1160219, by rfl⟩ : syracuseStep 1546959 = 2320439) B2320439
theorem B3480299 : Blo 1545470 3480299 := bstep (se 1 (by rfl) ⟨2610224, by rfl⟩ : syracuseStep 3480299 = 5220449) B5220449
theorem B1547419 : Blo 1545470 1547419 := bstep (se 1 (by rfl) ⟨1160564, by rfl⟩ : syracuseStep 1547419 = 2321129) B2321129
theorem B1547455 : Blo 1545470 1547455 := bstep (se 1 (by rfl) ⟨1160591, by rfl⟩ : syracuseStep 1547455 = 2321183) B2321183
theorem B4406555 : Blo 1545470 4406555 := bstep (se 1 (by rfl) ⟨3304916, by rfl⟩ : syracuseStep 4406555 = 6609833) B6609833
theorem B12533305 : Blo 1545470 12533305 := bstep (se 2 (by rfl) ⟨4699989, by rfl⟩ : syracuseStep 12533305 = 9399979) B9399979
theorem B3481271 : Blo 1545470 3481271 := bstep (se 1 (by rfl) ⟨2610953, by rfl⟩ : syracuseStep 3481271 = 5221907) B5221907
theorem B1883903 : Blo 1545470 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B7429913 : Blo 1545470 7429913 := bstep (se 2 (by rfl) ⟨2786217, by rfl⟩ : syracuseStep 7429913 = 5572435) B5572435
theorem B2318315 : Blo 1545470 2318315 := bstep (se 1 (by rfl) ⟨1738736, by rfl⟩ : syracuseStep 2318315 = 3477473) B3477473
theorem B26427707 : Blo 1545470 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B2318747 : Blo 1545470 2318747 := bstep (se 1 (by rfl) ⟨1739060, by rfl⟩ : syracuseStep 2318747 = 3478121) B3478121
theorem B2318879 : Blo 1545470 2318879 := bstep (se 1 (by rfl) ⟨1739159, by rfl⟩ : syracuseStep 2318879 = 3478319) B3478319
theorem B7823951 : Blo 1545470 7823951 := bstep (se 1 (by rfl) ⟨5867963, by rfl⟩ : syracuseStep 7823951 = 11735927) B11735927
theorem B2318939 : Blo 1545470 2318939 := bstep (se 1 (by rfl) ⟨1739204, by rfl⟩ : syracuseStep 2318939 = 3478409) B3478409
theorem B2318975 : Blo 1545470 2318975 := bstep (se 1 (by rfl) ⟨1739231, by rfl⟩ : syracuseStep 2318975 = 3478463) B3478463
theorem B2319017 : Blo 1545470 2319017 := bstep (se 2 (by rfl) ⟨869631, by rfl⟩ : syracuseStep 2319017 = 1739263) B1739263
theorem B7537321 : Blo 1545470 7537321 := bstep (se 2 (by rfl) ⟨2826495, by rfl⟩ : syracuseStep 7537321 = 5652991) B5652991
theorem B2319431 : Blo 1545470 2319431 := bstep (se 1 (by rfl) ⟨1739573, by rfl⟩ : syracuseStep 2319431 = 3479147) B3479147
theorem B2319497 : Blo 1545470 2319497 := bstep (se 2 (by rfl) ⟨869811, by rfl⟩ : syracuseStep 2319497 = 1739623) B1739623
theorem B2319737 : Blo 1545470 2319737 := bstep (se 2 (by rfl) ⟨869901, by rfl⟩ : syracuseStep 2319737 = 1739803) B1739803
theorem B2319743 : Blo 1545470 2319743 := bstep (se 1 (by rfl) ⟨1739807, by rfl⟩ : syracuseStep 2319743 = 3479615) B3479615
theorem B3302815 : Blo 1545470 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B2320199 : Blo 1545470 2320199 := bstep (se 1 (by rfl) ⟨1740149, by rfl⟩ : syracuseStep 2320199 = 3480299) B3480299
theorem B5023741 : Blo 1545470 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B2320553 : Blo 1545470 2320553 := bstep (se 2 (by rfl) ⟨870207, by rfl⟩ : syracuseStep 2320553 = 1740415) B1740415
theorem B2320847 : Blo 1545470 2320847 := bstep (se 1 (by rfl) ⟨1740635, by rfl⟩ : syracuseStep 2320847 = 3481271) B3481271
theorem B3967487 : Blo 1545470 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B2320937 : Blo 1545470 2320937 := bstep (se 2 (by rfl) ⟨870351, by rfl⟩ : syracuseStep 2320937 = 1740703) B1740703
theorem B5221151 : Blo 1545470 5221151 := bstep (se 1 (by rfl) ⟨3915863, by rfl⟩ : syracuseStep 5221151 = 7831727) B7831727
theorem B28601399 : Blo 1545470 28601399 := bstep (se 1 (by rfl) ⟨21451049, by rfl⟩ : syracuseStep 28601399 = 42902099) B42902099
theorem B1739983 : Blo 1545470 1739983 := bstep (se 1 (by rfl) ⟨1304987, by rfl⟩ : syracuseStep 1739983 = 2609975) B2609975
theorem B17624303 : Blo 1545470 17624303 := bstep (se 1 (by rfl) ⟨13218227, by rfl⟩ : syracuseStep 17624303 = 26436455) B26436455
theorem B19328861 : Blo 1545470 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B13217681 : Blo 1545470 13217681 := bstep (se 2 (by rfl) ⟨4956630, by rfl⟩ : syracuseStep 13217681 = 9913261) B9913261
theorem B3477419 : Blo 1545470 3477419 := bstep (se 1 (by rfl) ⟨2608064, by rfl⟩ : syracuseStep 3477419 = 5216129) B5216129
theorem B2937703 : Blo 1545470 2937703 := bstep (se 1 (by rfl) ⟨2203277, by rfl⟩ : syracuseStep 2937703 = 4406555) B4406555
theorem B9909161 : Blo 1545470 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B4953275 : Blo 1545470 4953275 := bstep (se 1 (by rfl) ⟨3714956, by rfl⟩ : syracuseStep 4953275 = 7429913) B7429913
theorem B1545543 : Blo 1545470 1545543 := bstep (se 1 (by rfl) ⟨1159157, by rfl⟩ : syracuseStep 1545543 = 2318315) B2318315
theorem B2610535 : Blo 1545470 2610535 := bstep (se 1 (by rfl) ⟨1957901, by rfl⟩ : syracuseStep 2610535 = 3915803) B3915803
theorem B1545887 : Blo 1545470 1545887 := bstep (se 1 (by rfl) ⟨1159415, by rfl⟩ : syracuseStep 1545887 = 2318831) B2318831
theorem B4405063 : Blo 1545470 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B1546207 : Blo 1545470 1546207 := bstep (se 1 (by rfl) ⟨1159655, by rfl⟩ : syracuseStep 1546207 = 2319311) B2319311
theorem B1546407 : Blo 1545470 1546407 := bstep (se 1 (by rfl) ⟨1159805, by rfl⟩ : syracuseStep 1546407 = 2319611) B2319611
theorem B3480119 : Blo 1545470 3480119 := bstep (se 1 (by rfl) ⟨2610089, by rfl⟩ : syracuseStep 3480119 = 5220179) B5220179
theorem B5216939 : Blo 1545470 5216939 := bstep (se 1 (by rfl) ⟨3912704, by rfl⟩ : syracuseStep 5216939 = 7825409) B7825409
theorem B6274145 : Blo 1545470 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B9903215 : Blo 1545470 9903215 := bstep (se 1 (by rfl) ⟨7427411, by rfl⟩ : syracuseStep 9903215 = 14854823) B14854823
theorem B8363191 : Blo 1545470 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B27147581 : Blo 1545470 27147581 := bstep (se 3 (by rfl) ⟨5090171, by rfl⟩ : syracuseStep 27147581 = 10180343) B10180343
theorem B16711073 : Blo 1545470 16711073 := bstep (se 2 (by rfl) ⟨6266652, by rfl⟩ : syracuseStep 16711073 = 12533305) B12533305
theorem B3481001 : Blo 1545470 3481001 := bstep (se 2 (by rfl) ⟨1305375, by rfl⟩ : syracuseStep 3481001 = 2610751) B2610751
theorem B3481055 : Blo 1545470 3481055 := bstep (se 1 (by rfl) ⟨2610791, by rfl⟩ : syracuseStep 3481055 = 5221583) B5221583
theorem B3302183 : Blo 1545470 3302183 := bstep (se 1 (by rfl) ⟨2476637, by rfl⟩ : syracuseStep 3302183 = 4953275) B4953275
theorem B3916937 : Blo 1545470 3916937 := bstep (se 2 (by rfl) ⟨1468851, by rfl⟩ : syracuseStep 3916937 = 2937703) B2937703
theorem B11150921 : Blo 1545470 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B2319977 : Blo 1545470 2319977 := bstep (se 2 (by rfl) ⟨869991, by rfl⟩ : syracuseStep 2319977 = 1739983) B1739983
theorem B2320079 : Blo 1545470 2320079 := bstep (se 1 (by rfl) ⟨1740059, by rfl⟩ : syracuseStep 2320079 = 3480119) B3480119
theorem B11749535 : Blo 1545470 11749535 := bstep (se 1 (by rfl) ⟨8812151, by rfl⟩ : syracuseStep 11749535 = 17624303) B17624303
theorem B18098387 : Blo 1545470 18098387 := bstep (se 1 (by rfl) ⟨13573790, by rfl⟩ : syracuseStep 18098387 = 27147581) B27147581
theorem B2320667 : Blo 1545470 2320667 := bstep (se 1 (by rfl) ⟨1740500, by rfl⟩ : syracuseStep 2320667 = 3481001) B3481001
theorem B2320703 : Blo 1545470 2320703 := bstep (se 1 (by rfl) ⟨1740527, by rfl⟩ : syracuseStep 2320703 = 3481055) B3481055
theorem B6606107 : Blo 1545470 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B3477959 : Blo 1545470 3477959 := bstep (se 1 (by rfl) ⟨2608469, by rfl⟩ : syracuseStep 3477959 = 5216939) B5216939
theorem B4403753 : Blo 1545470 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B19067599 : Blo 1545470 19067599 := bstep (se 1 (by rfl) ⟨14300699, by rfl⟩ : syracuseStep 19067599 = 28601399) B28601399
theorem B4182763 : Blo 1545470 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B8811787 : Blo 1545470 8811787 := bstep (se 1 (by rfl) ⟨6608840, by rfl⟩ : syracuseStep 8811787 = 13217681) B13217681
theorem B6698321 : Blo 1545470 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B17618471 : Blo 1545470 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B1545831 : Blo 1545470 1545831 := bstep (se 1 (by rfl) ⟨1159373, by rfl⟩ : syracuseStep 1545831 = 2318747) B2318747
theorem B1545919 : Blo 1545470 1545919 := bstep (se 1 (by rfl) ⟨1159439, by rfl⟩ : syracuseStep 1545919 = 2318879) B2318879
theorem B5215967 : Blo 1545470 5215967 := bstep (se 1 (by rfl) ⟨3911975, by rfl⟩ : syracuseStep 5215967 = 7823951) B7823951
theorem B1545959 : Blo 1545470 1545959 := bstep (se 1 (by rfl) ⟨1159469, by rfl⟩ : syracuseStep 1545959 = 2318939) B2318939
theorem B1545983 : Blo 1545470 1545983 := bstep (se 1 (by rfl) ⟨1159487, by rfl⟩ : syracuseStep 1545983 = 2318975) B2318975
theorem B1546011 : Blo 1545470 1546011 := bstep (se 1 (by rfl) ⟨1159508, by rfl⟩ : syracuseStep 1546011 = 2319017) B2319017
theorem B1546287 : Blo 1545470 1546287 := bstep (se 1 (by rfl) ⟨1159715, by rfl⟩ : syracuseStep 1546287 = 2319431) B2319431
theorem B1546331 : Blo 1545470 1546331 := bstep (se 1 (by rfl) ⟨1159748, by rfl⟩ : syracuseStep 1546331 = 2319497) B2319497
theorem B10049761 : Blo 1545470 10049761 := bstep (se 2 (by rfl) ⟨3768660, by rfl⟩ : syracuseStep 10049761 = 7537321) B7537321
theorem B1546491 : Blo 1545470 1546491 := bstep (se 1 (by rfl) ⟨1159868, by rfl⟩ : syracuseStep 1546491 = 2319737) B2319737
theorem B1546495 : Blo 1545470 1546495 := bstep (se 1 (by rfl) ⟨1159871, by rfl⟩ : syracuseStep 1546495 = 2319743) B2319743
theorem B1546799 : Blo 1545470 1546799 := bstep (se 1 (by rfl) ⟨1160099, by rfl⟩ : syracuseStep 1546799 = 2320199) B2320199
theorem B1547035 : Blo 1545470 1547035 := bstep (se 1 (by rfl) ⟨1160276, by rfl⟩ : syracuseStep 1547035 = 2320553) B2320553
theorem B1547231 : Blo 1545470 1547231 := bstep (se 1 (by rfl) ⟨1160423, by rfl⟩ : syracuseStep 1547231 = 2320847) B2320847
theorem B2644991 : Blo 1545470 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B1547291 : Blo 1545470 1547291 := bstep (se 1 (by rfl) ⟨1160468, by rfl⟩ : syracuseStep 1547291 = 2320937) B2320937
theorem B3480713 : Blo 1545470 3480713 := bstep (se 2 (by rfl) ⟨1305267, by rfl⟩ : syracuseStep 3480713 = 2610535) B2610535
theorem B3480767 : Blo 1545470 3480767 := bstep (se 1 (by rfl) ⟨2610575, by rfl⟩ : syracuseStep 3480767 = 5221151) B5221151
theorem B6602143 : Blo 1545470 6602143 := bstep (se 1 (by rfl) ⟨4951607, by rfl⟩ : syracuseStep 6602143 = 9903215) B9903215
theorem B11140715 : Blo 1545470 11140715 := bstep (se 1 (by rfl) ⟨8355536, by rfl⟩ : syracuseStep 11140715 = 16711073) B16711073
theorem B5873417 : Blo 1545470 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B12885907 : Blo 1545470 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B2318279 : Blo 1545470 2318279 := bstep (se 1 (by rfl) ⟨1738709, by rfl⟩ : syracuseStep 2318279 = 3477419) B3477419
theorem B2318639 : Blo 1545470 2318639 := bstep (se 1 (by rfl) ⟨1738979, by rfl⟩ : syracuseStep 2318639 = 3477959) B3477959
theorem B4465547 : Blo 1545470 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B7833023 : Blo 1545470 7833023 := bstep (se 1 (by rfl) ⟨5874767, by rfl⟩ : syracuseStep 7833023 = 11749535) B11749535
theorem B11749049 : Blo 1545470 11749049 := bstep (se 2 (by rfl) ⟨4405893, by rfl⟩ : syracuseStep 11749049 = 8811787) B8811787
theorem B1763327 : Blo 1545470 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B2320475 : Blo 1545470 2320475 := bstep (se 1 (by rfl) ⟨1740356, by rfl⟩ : syracuseStep 2320475 = 3480713) B3480713
theorem B2320511 : Blo 1545470 2320511 := bstep (se 1 (by rfl) ⟨1740383, by rfl⟩ : syracuseStep 2320511 = 3480767) B3480767
theorem B17181209 : Blo 1545470 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B2935835 : Blo 1545470 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B25423465 : Blo 1545470 25423465 := bstep (se 2 (by rfl) ⟨9533799, by rfl⟩ : syracuseStep 25423465 = 19067599) B19067599
theorem B7433947 : Blo 1545470 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B3477311 : Blo 1545470 3477311 := bstep (se 1 (by rfl) ⟨2607983, by rfl⟩ : syracuseStep 3477311 = 5215967) B5215967
theorem B8802857 : Blo 1545470 8802857 := bstep (se 2 (by rfl) ⟨3301071, by rfl⟩ : syracuseStep 8802857 = 6602143) B6602143
theorem B4404071 : Blo 1545470 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B7427143 : Blo 1545470 7427143 := bstep (se 1 (by rfl) ⟨5570357, by rfl⟩ : syracuseStep 7427143 = 11140715) B11140715
theorem B1545519 : Blo 1545470 1545519 := bstep (se 1 (by rfl) ⟨1159139, by rfl⟩ : syracuseStep 1545519 = 2318279) B2318279
theorem B13399681 : Blo 1545470 13399681 := bstep (se 2 (by rfl) ⟨5024880, by rfl⟩ : syracuseStep 13399681 = 10049761) B10049761
theorem B2201455 : Blo 1545470 2201455 := bstep (se 1 (by rfl) ⟨1651091, by rfl⟩ : syracuseStep 2201455 = 3302183) B3302183
theorem B2611291 : Blo 1545470 2611291 := bstep (se 1 (by rfl) ⟨1958468, by rfl⟩ : syracuseStep 2611291 = 3916937) B3916937
theorem B5577017 : Blo 1545470 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B11745647 : Blo 1545470 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B1546651 : Blo 1545470 1546651 := bstep (se 1 (by rfl) ⟨1159988, by rfl⟩ : syracuseStep 1546651 = 2319977) B2319977
theorem B1546719 : Blo 1545470 1546719 := bstep (se 1 (by rfl) ⟨1160039, by rfl⟩ : syracuseStep 1546719 = 2320079) B2320079
theorem B12065591 : Blo 1545470 12065591 := bstep (se 1 (by rfl) ⟨9049193, by rfl⟩ : syracuseStep 12065591 = 18098387) B18098387
theorem B1547111 : Blo 1545470 1547111 := bstep (se 1 (by rfl) ⟨1160333, by rfl⟩ : syracuseStep 1547111 = 2320667) B2320667
theorem B1547135 : Blo 1545470 1547135 := bstep (se 1 (by rfl) ⟨1160351, by rfl⟩ : syracuseStep 1547135 = 2320703) B2320703
theorem B3915611 : Blo 1545470 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B3481721 : Blo 1545470 3481721 := bstep (se 2 (by rfl) ⟨1305645, by rfl⟩ : syracuseStep 3481721 = 2611291) B2611291
theorem B7832699 : Blo 1545470 7832699 := bstep (se 1 (by rfl) ⟨5874524, by rfl⟩ : syracuseStep 7832699 = 11749049) B11749049
theorem B11454139 : Blo 1545470 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B2935273 : Blo 1545470 2935273 := bstep (se 2 (by rfl) ⟨1100727, by rfl⟩ : syracuseStep 2935273 = 2201455) B2201455
theorem B5868571 : Blo 1545470 5868571 := bstep (se 1 (by rfl) ⟨4401428, by rfl⟩ : syracuseStep 5868571 = 8802857) B8802857
theorem B2977031 : Blo 1545470 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B14872045 : Blo 1545470 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B5222015 : Blo 1545470 5222015 := bstep (se 1 (by rfl) ⟨3916511, by rfl⟩ : syracuseStep 5222015 = 7833023) B7833023
theorem B11744189 : Blo 1545470 11744189 := bstep (se 3 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 11744189 = 4404071) B4404071
theorem B2610407 : Blo 1545470 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B1545759 : Blo 1545470 1545759 := bstep (se 1 (by rfl) ⟨1159319, by rfl⟩ : syracuseStep 1545759 = 2318639) B2318639
theorem B1546983 : Blo 1545470 1546983 := bstep (se 1 (by rfl) ⟨1160237, by rfl⟩ : syracuseStep 1546983 = 2320475) B2320475
theorem B1547007 : Blo 1545470 1547007 := bstep (se 1 (by rfl) ⟨1160255, by rfl⟩ : syracuseStep 1547007 = 2320511) B2320511
theorem B9902857 : Blo 1545470 9902857 := bstep (se 2 (by rfl) ⟨3713571, by rfl⟩ : syracuseStep 9902857 = 7427143) B7427143
theorem B7830431 : Blo 1545470 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B8043727 : Blo 1545470 8043727 := bstep (se 1 (by rfl) ⟨6032795, by rfl⟩ : syracuseStep 8043727 = 12065591) B12065591
theorem B1957223 : Blo 1545470 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B33897953 : Blo 1545470 33897953 := bstep (se 2 (by rfl) ⟨12711732, by rfl⟩ : syracuseStep 33897953 = 25423465) B25423465
theorem B17866241 : Blo 1545470 17866241 := bstep (se 2 (by rfl) ⟨6699840, by rfl⟩ : syracuseStep 17866241 = 13399681) B13399681
theorem B9911929 : Blo 1545470 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B2318207 : Blo 1545470 2318207 := bstep (se 1 (by rfl) ⟨1738655, by rfl⟩ : syracuseStep 2318207 = 3477311) B3477311
theorem B4702205 : Blo 1545470 4702205 := bstep (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) B1763327
theorem B7938749 : Blo 1545470 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B5219261 : Blo 1545470 5219261 := bstep (se 3 (by rfl) ⟨978611, by rfl⟩ : syracuseStep 5219261 = 1957223) B1957223
theorem B7824761 : Blo 1545470 7824761 := bstep (se 2 (by rfl) ⟨2934285, by rfl⟩ : syracuseStep 7824761 = 5868571) B5868571
theorem B10724969 : Blo 1545470 10724969 := bstep (se 2 (by rfl) ⟨4021863, by rfl⟩ : syracuseStep 10724969 = 8043727) B8043727
theorem B5220287 : Blo 1545470 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B13215905 : Blo 1545470 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B15272185 : Blo 1545470 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B2321147 : Blo 1545470 2321147 := bstep (se 1 (by rfl) ⟨1740860, by rfl⟩ : syracuseStep 2321147 = 3481721) B3481721
theorem B5221799 : Blo 1545470 5221799 := bstep (se 1 (by rfl) ⟨3916349, by rfl⟩ : syracuseStep 5221799 = 7832699) B7832699
theorem B1740271 : Blo 1545470 1740271 := bstep (se 1 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 1740271 = 2610407) B2610407
theorem B90394541 : Blo 1545470 90394541 := bstep (se 3 (by rfl) ⟨16948976, by rfl⟩ : syracuseStep 90394541 = 33897953) B33897953
theorem B19829393 : Blo 1545470 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B1545471 : Blo 1545470 1545471 := bstep (se 1 (by rfl) ⟨1159103, by rfl⟩ : syracuseStep 1545471 = 2318207) B2318207
theorem B3134803 : Blo 1545470 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B7829459 : Blo 1545470 7829459 := bstep (se 1 (by rfl) ⟨5872094, by rfl⟩ : syracuseStep 7829459 = 11744189) B11744189
theorem B3913697 : Blo 1545470 3913697 := bstep (se 2 (by rfl) ⟨1467636, by rfl⟩ : syracuseStep 3913697 = 2935273) B2935273
theorem B13203809 : Blo 1545470 13203809 := bstep (se 2 (by rfl) ⟨4951428, by rfl⟩ : syracuseStep 13203809 = 9902857) B9902857
theorem B11910827 : Blo 1545470 11910827 := bstep (se 1 (by rfl) ⟨8933120, by rfl⟩ : syracuseStep 11910827 = 17866241) B17866241
theorem B3481343 : Blo 1545470 3481343 := bstep (se 1 (by rfl) ⟨2611007, by rfl⟩ : syracuseStep 3481343 = 5222015) B5222015
theorem B5292499 : Blo 1545470 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B5219639 : Blo 1545470 5219639 := bstep (se 1 (by rfl) ⟨3914729, by rfl⟩ : syracuseStep 5219639 = 7829459) B7829459
theorem B4179737 : Blo 1545470 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B2320361 : Blo 1545470 2320361 := bstep (se 2 (by rfl) ⟨870135, by rfl⟩ : syracuseStep 2320361 = 1740271) B1740271
theorem B7940551 : Blo 1545470 7940551 := bstep (se 1 (by rfl) ⟨5955413, by rfl⟩ : syracuseStep 7940551 = 11910827) B11910827
theorem B2320895 : Blo 1545470 2320895 := bstep (se 1 (by rfl) ⟨1740671, by rfl⟩ : syracuseStep 2320895 = 3481343) B3481343
theorem B60263027 : Blo 1545470 60263027 := bstep (se 1 (by rfl) ⟨45197270, by rfl⟩ : syracuseStep 60263027 = 90394541) B90394541
theorem B2609131 : Blo 1545470 2609131 := bstep (se 1 (by rfl) ⟨1956848, by rfl⟩ : syracuseStep 2609131 = 3913697) B3913697
theorem B8810603 : Blo 1545470 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B8802539 : Blo 1545470 8802539 := bstep (se 1 (by rfl) ⟨6601904, by rfl⟩ : syracuseStep 8802539 = 13203809) B13203809
theorem B20362913 : Blo 1545470 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B13219595 : Blo 1545470 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B3479507 : Blo 1545470 3479507 := bstep (se 1 (by rfl) ⟨2609630, by rfl⟩ : syracuseStep 3479507 = 5219261) B5219261
theorem B5216507 : Blo 1545470 5216507 := bstep (se 1 (by rfl) ⟨3912380, by rfl⟩ : syracuseStep 5216507 = 7824761) B7824761
theorem B7149979 : Blo 1545470 7149979 := bstep (se 1 (by rfl) ⟨5362484, by rfl⟩ : syracuseStep 7149979 = 10724969) B10724969
theorem B3480191 : Blo 1545470 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B1547431 : Blo 1545470 1547431 := bstep (se 1 (by rfl) ⟨1160573, by rfl⟩ : syracuseStep 1547431 = 2321147) B2321147
theorem B3481199 : Blo 1545470 3481199 := bstep (se 1 (by rfl) ⟨2610899, by rfl⟩ : syracuseStep 3481199 = 5221799) B5221799
theorem B5873735 : Blo 1545470 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B13575275 : Blo 1545470 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B2786491 : Blo 1545470 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B2319671 : Blo 1545470 2319671 := bstep (se 1 (by rfl) ⟨1739753, by rfl⟩ : syracuseStep 2319671 = 3479507) B3479507
theorem B40175351 : Blo 1545470 40175351 := bstep (se 1 (by rfl) ⟨30131513, by rfl⟩ : syracuseStep 40175351 = 60263027) B60263027
theorem B2320127 : Blo 1545470 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B2320799 : Blo 1545470 2320799 := bstep (se 1 (by rfl) ⟨1740599, by rfl⟩ : syracuseStep 2320799 = 3481199) B3481199
theorem B5868359 : Blo 1545470 5868359 := bstep (se 1 (by rfl) ⟨4401269, by rfl⟩ : syracuseStep 5868359 = 8802539) B8802539
theorem B10587401 : Blo 1545470 10587401 := bstep (se 2 (by rfl) ⟨3970275, by rfl⟩ : syracuseStep 10587401 = 7940551) B7940551
theorem B7056665 : Blo 1545470 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B3477671 : Blo 1545470 3477671 := bstep (se 1 (by rfl) ⟨2608253, by rfl⟩ : syracuseStep 3477671 = 5216507) B5216507
theorem B3478841 : Blo 1545470 3478841 := bstep (se 2 (by rfl) ⟨1304565, by rfl⟩ : syracuseStep 3478841 = 2609131) B2609131
theorem B9533305 : Blo 1545470 9533305 := bstep (se 2 (by rfl) ⟨3574989, by rfl⟩ : syracuseStep 9533305 = 7149979) B7149979
theorem B3479759 : Blo 1545470 3479759 := bstep (se 1 (by rfl) ⟨2609819, by rfl⟩ : syracuseStep 3479759 = 5219639) B5219639
theorem B8813063 : Blo 1545470 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B1546907 : Blo 1545470 1546907 := bstep (se 1 (by rfl) ⟨1160180, by rfl⟩ : syracuseStep 1546907 = 2320361) B2320361
theorem B1547263 : Blo 1545470 1547263 := bstep (se 1 (by rfl) ⟨1160447, by rfl⟩ : syracuseStep 1547263 = 2320895) B2320895
theorem B3915823 : Blo 1545470 3915823 := bstep (se 1 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 3915823 = 5873735) B5873735
theorem B2318447 : Blo 1545470 2318447 := bstep (se 1 (by rfl) ⟨1738835, by rfl⟩ : syracuseStep 2318447 = 3477671) B3477671
theorem B2319227 : Blo 1545470 2319227 := bstep (se 1 (by rfl) ⟨1739420, by rfl⟩ : syracuseStep 2319227 = 3478841) B3478841
theorem B2319839 : Blo 1545470 2319839 := bstep (se 1 (by rfl) ⟨1739879, by rfl⟩ : syracuseStep 2319839 = 3479759) B3479759
theorem B5875375 : Blo 1545470 5875375 := bstep (se 1 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 5875375 = 8813063) B8813063
theorem B4704443 : Blo 1545470 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B26783567 : Blo 1545470 26783567 := bstep (se 1 (by rfl) ⟨20087675, by rfl⟩ : syracuseStep 26783567 = 40175351) B40175351
theorem B3715321 : Blo 1545470 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B3912239 : Blo 1545470 3912239 := bstep (se 1 (by rfl) ⟨2934179, by rfl⟩ : syracuseStep 3912239 = 5868359) B5868359
theorem B50844293 : Blo 1545470 50844293 := bstep (se 4 (by rfl) ⟨4766652, by rfl⟩ : syracuseStep 50844293 = 9533305) B9533305
theorem B7058267 : Blo 1545470 7058267 := bstep (se 1 (by rfl) ⟨5293700, by rfl⟩ : syracuseStep 7058267 = 10587401) B10587401
theorem B9050183 : Blo 1545470 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B1546447 : Blo 1545470 1546447 := bstep (se 1 (by rfl) ⟨1159835, by rfl⟩ : syracuseStep 1546447 = 2319671) B2319671
theorem B1546751 : Blo 1545470 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B1547199 : Blo 1545470 1547199 := bstep (se 1 (by rfl) ⟨1160399, by rfl⟩ : syracuseStep 1547199 = 2320799) B2320799
theorem B7833833 : Blo 1545470 7833833 := bstep (se 2 (by rfl) ⟨2937687, by rfl⟩ : syracuseStep 7833833 = 5875375) B5875375
theorem B5221097 : Blo 1545470 5221097 := bstep (se 2 (by rfl) ⟨1957911, by rfl⟩ : syracuseStep 5221097 = 3915823) B3915823
theorem B2608159 : Blo 1545470 2608159 := bstep (se 1 (by rfl) ⟨1956119, by rfl⟩ : syracuseStep 2608159 = 3912239) B3912239
theorem B4705511 : Blo 1545470 4705511 := bstep (se 1 (by rfl) ⟨3529133, by rfl⟩ : syracuseStep 4705511 = 7058267) B7058267
theorem B6033455 : Blo 1545470 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B17855711 : Blo 1545470 17855711 := bstep (se 1 (by rfl) ⟨13391783, by rfl⟩ : syracuseStep 17855711 = 26783567) B26783567
theorem B1545631 : Blo 1545470 1545631 := bstep (se 1 (by rfl) ⟨1159223, by rfl⟩ : syracuseStep 1545631 = 2318447) B2318447
theorem B4953761 : Blo 1545470 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B33896195 : Blo 1545470 33896195 := bstep (se 1 (by rfl) ⟨25422146, by rfl⟩ : syracuseStep 33896195 = 50844293) B50844293
theorem B1546151 : Blo 1545470 1546151 := bstep (se 1 (by rfl) ⟨1159613, by rfl⟩ : syracuseStep 1546151 = 2319227) B2319227
theorem B1546559 : Blo 1545470 1546559 := bstep (se 1 (by rfl) ⟨1159919, by rfl⟩ : syracuseStep 1546559 = 2319839) B2319839
theorem B3136295 : Blo 1545470 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B4022303 : Blo 1545470 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B11903807 : Blo 1545470 11903807 := bstep (se 1 (by rfl) ⟨8927855, by rfl⟩ : syracuseStep 11903807 = 17855711) B17855711
theorem B3302507 : Blo 1545470 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B2090863 : Blo 1545470 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B22597463 : Blo 1545470 22597463 := bstep (se 1 (by rfl) ⟨16948097, by rfl⟩ : syracuseStep 22597463 = 33896195) B33896195
theorem B3477545 : Blo 1545470 3477545 := bstep (se 2 (by rfl) ⟨1304079, by rfl⟩ : syracuseStep 3477545 = 2608159) B2608159
theorem B5222555 : Blo 1545470 5222555 := bstep (se 1 (by rfl) ⟨3916916, by rfl⟩ : syracuseStep 5222555 = 7833833) B7833833
theorem B12548029 : Blo 1545470 12548029 := bstep (se 3 (by rfl) ⟨2352755, by rfl⟩ : syracuseStep 12548029 = 4705511) B4705511
theorem B3480731 : Blo 1545470 3480731 := bstep (se 1 (by rfl) ⟨2610548, by rfl⟩ : syracuseStep 3480731 = 5221097) B5221097
theorem B2318363 : Blo 1545470 2318363 := bstep (se 1 (by rfl) ⟨1738772, by rfl⟩ : syracuseStep 2318363 = 3477545) B3477545
theorem B3481703 : Blo 1545470 3481703 := bstep (se 1 (by rfl) ⟨2611277, by rfl⟩ : syracuseStep 3481703 = 5222555) B5222555
theorem B11151269 : Blo 1545470 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B2320487 : Blo 1545470 2320487 := bstep (se 1 (by rfl) ⟨1740365, by rfl⟩ : syracuseStep 2320487 = 3480731) B3480731
theorem B16730705 : Blo 1545470 16730705 := bstep (se 2 (by rfl) ⟨6274014, by rfl⟩ : syracuseStep 16730705 = 12548029) B12548029
theorem B42904565 : Blo 1545470 42904565 := bstep (se 5 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 42904565 = 4022303) B4022303
theorem B2201671 : Blo 1545470 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B31743485 : Blo 1545470 31743485 := bstep (se 3 (by rfl) ⟨5951903, by rfl⟩ : syracuseStep 31743485 = 11903807) B11903807
theorem B15064975 : Blo 1545470 15064975 := bstep (se 1 (by rfl) ⟨11298731, by rfl⟩ : syracuseStep 15064975 = 22597463) B22597463
theorem B21162323 : Blo 1545470 21162323 := bstep (se 1 (by rfl) ⟨15871742, by rfl⟩ : syracuseStep 21162323 = 31743485) B31743485
theorem B2321135 : Blo 1545470 2321135 := bstep (se 1 (by rfl) ⟨1740851, by rfl⟩ : syracuseStep 2321135 = 3481703) B3481703
theorem B11742245 : Blo 1545470 11742245 := bstep (se 4 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 11742245 = 2201671) B2201671
theorem B7434179 : Blo 1545470 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B11153803 : Blo 1545470 11153803 := bstep (se 1 (by rfl) ⟨8365352, by rfl⟩ : syracuseStep 11153803 = 16730705) B16730705
theorem B28603043 : Blo 1545470 28603043 := bstep (se 1 (by rfl) ⟨21452282, by rfl⟩ : syracuseStep 28603043 = 42904565) B42904565
theorem B1545575 : Blo 1545470 1545575 := bstep (se 1 (by rfl) ⟨1159181, by rfl⟩ : syracuseStep 1545575 = 2318363) B2318363
theorem B1546991 : Blo 1545470 1546991 := bstep (se 1 (by rfl) ⟨1160243, by rfl⟩ : syracuseStep 1546991 = 2320487) B2320487
theorem B20086633 : Blo 1545470 20086633 := bstep (se 2 (by rfl) ⟨7532487, by rfl⟩ : syracuseStep 20086633 = 15064975) B15064975
theorem B14108215 : Blo 1545470 14108215 := bstep (se 1 (by rfl) ⟨10581161, by rfl⟩ : syracuseStep 14108215 = 21162323) B21162323
theorem B26782177 : Blo 1545470 26782177 := bstep (se 2 (by rfl) ⟨10043316, by rfl⟩ : syracuseStep 26782177 = 20086633) B20086633
theorem B14871737 : Blo 1545470 14871737 := bstep (se 2 (by rfl) ⟨5576901, by rfl⟩ : syracuseStep 14871737 = 11153803) B11153803
theorem B7828163 : Blo 1545470 7828163 := bstep (se 1 (by rfl) ⟨5871122, by rfl⟩ : syracuseStep 7828163 = 11742245) B11742245
theorem B19068695 : Blo 1545470 19068695 := bstep (se 1 (by rfl) ⟨14301521, by rfl⟩ : syracuseStep 19068695 = 28603043) B28603043
theorem B1547423 : Blo 1545470 1547423 := bstep (se 1 (by rfl) ⟨1160567, by rfl⟩ : syracuseStep 1547423 = 2321135) B2321135
theorem B4956119 : Blo 1545470 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B5218775 : Blo 1545470 5218775 := bstep (se 1 (by rfl) ⟨3914081, by rfl⟩ : syracuseStep 5218775 = 7828163) B7828163
theorem B35709569 : Blo 1545470 35709569 := bstep (se 2 (by rfl) ⟨13391088, by rfl⟩ : syracuseStep 35709569 = 26782177) B26782177
theorem B18810953 : Blo 1545470 18810953 := bstep (se 2 (by rfl) ⟨7054107, by rfl⟩ : syracuseStep 18810953 = 14108215) B14108215
theorem B9914491 : Blo 1545470 9914491 := bstep (se 1 (by rfl) ⟨7435868, by rfl⟩ : syracuseStep 9914491 = 14871737) B14871737
theorem B3304079 : Blo 1545470 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B12712463 : Blo 1545470 12712463 := bstep (se 1 (by rfl) ⟨9534347, by rfl⟩ : syracuseStep 12712463 = 19068695) B19068695
theorem B23806379 : Blo 1545470 23806379 := bstep (se 1 (by rfl) ⟨17854784, by rfl⟩ : syracuseStep 23806379 = 35709569) B35709569
theorem B8474975 : Blo 1545470 8474975 := bstep (se 1 (by rfl) ⟨6356231, by rfl⟩ : syracuseStep 8474975 = 12712463) B12712463
theorem B13219321 : Blo 1545470 13219321 := bstep (se 2 (by rfl) ⟨4957245, by rfl⟩ : syracuseStep 13219321 = 9914491) B9914491
theorem B3479183 : Blo 1545470 3479183 := bstep (se 1 (by rfl) ⟨2609387, by rfl⟩ : syracuseStep 3479183 = 5218775) B5218775
theorem B12540635 : Blo 1545470 12540635 := bstep (se 1 (by rfl) ⟨9405476, by rfl⟩ : syracuseStep 12540635 = 18810953) B18810953
theorem B2202719 : Blo 1545470 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B5873917 : Blo 1545470 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B2319455 : Blo 1545470 2319455 := bstep (se 1 (by rfl) ⟨1739591, by rfl⟩ : syracuseStep 2319455 = 3479183) B3479183
theorem B15870919 : Blo 1545470 15870919 := bstep (se 1 (by rfl) ⟨11903189, by rfl⟩ : syracuseStep 15870919 = 23806379) B23806379
theorem B8360423 : Blo 1545470 8360423 := bstep (se 1 (by rfl) ⟨6270317, by rfl⟩ : syracuseStep 8360423 = 12540635) B12540635
theorem B17625761 : Blo 1545470 17625761 := bstep (se 2 (by rfl) ⟨6609660, by rfl⟩ : syracuseStep 17625761 = 13219321) B13219321
theorem B5649983 : Blo 1545470 5649983 := bstep (se 1 (by rfl) ⟨4237487, by rfl⟩ : syracuseStep 5649983 = 8474975) B8474975
theorem B7831889 : Blo 1545470 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B21161225 : Blo 1545470 21161225 := bstep (se 2 (by rfl) ⟨7935459, by rfl⟩ : syracuseStep 21161225 = 15870919) B15870919
theorem B5573615 : Blo 1545470 5573615 := bstep (se 1 (by rfl) ⟨4180211, by rfl⟩ : syracuseStep 5573615 = 8360423) B8360423
theorem B11750507 : Blo 1545470 11750507 := bstep (se 1 (by rfl) ⟨8812880, by rfl⟩ : syracuseStep 11750507 = 17625761) B17625761
theorem B1546303 : Blo 1545470 1546303 := bstep (se 1 (by rfl) ⟨1159727, by rfl⟩ : syracuseStep 1546303 = 2319455) B2319455
theorem B3766655 : Blo 1545470 3766655 := bstep (se 1 (by rfl) ⟨2824991, by rfl⟩ : syracuseStep 3766655 = 5649983) B5649983
theorem B14107483 : Blo 1545470 14107483 := bstep (se 1 (by rfl) ⟨10580612, by rfl⟩ : syracuseStep 14107483 = 21161225) B21161225
theorem B7833671 : Blo 1545470 7833671 := bstep (se 1 (by rfl) ⟨5875253, by rfl⟩ : syracuseStep 7833671 = 11750507) B11750507
theorem B14862973 : Blo 1545470 14862973 := bstep (se 3 (by rfl) ⟨2786807, by rfl⟩ : syracuseStep 14862973 = 5573615) B5573615
theorem B5221259 : Blo 1545470 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B2511103 : Blo 1545470 2511103 := bstep (se 1 (by rfl) ⟨1883327, by rfl⟩ : syracuseStep 2511103 = 3766655) B3766655
theorem B19817297 : Blo 1545470 19817297 := bstep (se 2 (by rfl) ⟨7431486, by rfl⟩ : syracuseStep 19817297 = 14862973) B14862973
theorem B18809977 : Blo 1545470 18809977 := bstep (se 2 (by rfl) ⟨7053741, by rfl⟩ : syracuseStep 18809977 = 14107483) B14107483
theorem B5222447 : Blo 1545470 5222447 := bstep (se 1 (by rfl) ⟨3916835, by rfl⟩ : syracuseStep 5222447 = 7833671) B7833671
theorem B3348137 : Blo 1545470 3348137 := bstep (se 2 (by rfl) ⟨1255551, by rfl⟩ : syracuseStep 3348137 = 2511103) B2511103
theorem B3480839 : Blo 1545470 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B3481631 : Blo 1545470 3481631 := bstep (se 1 (by rfl) ⟨2611223, by rfl⟩ : syracuseStep 3481631 = 5222447) B5222447
theorem B2320559 : Blo 1545470 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B25079969 : Blo 1545470 25079969 := bstep (se 2 (by rfl) ⟨9404988, by rfl⟩ : syracuseStep 25079969 = 18809977) B18809977
theorem B13211531 : Blo 1545470 13211531 := bstep (se 1 (by rfl) ⟨9908648, by rfl⟩ : syracuseStep 13211531 = 19817297) B19817297
theorem B8928365 : Blo 1545470 8928365 := bstep (se 3 (by rfl) ⟨1674068, by rfl⟩ : syracuseStep 8928365 = 3348137) B3348137
theorem B66879917 : Blo 1545470 66879917 := bstep (se 3 (by rfl) ⟨12539984, by rfl⟩ : syracuseStep 66879917 = 25079969) B25079969
theorem B8807687 : Blo 1545470 8807687 := bstep (se 1 (by rfl) ⟨6605765, by rfl⟩ : syracuseStep 8807687 = 13211531) B13211531
theorem B2321087 : Blo 1545470 2321087 := bstep (se 1 (by rfl) ⟨1740815, by rfl⟩ : syracuseStep 2321087 = 3481631) B3481631
theorem B23808973 : Blo 1545470 23808973 := bstep (se 3 (by rfl) ⟨4464182, by rfl⟩ : syracuseStep 23808973 = 8928365) B8928365
theorem B1547039 : Blo 1545470 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B31745297 : Blo 1545470 31745297 := bstep (se 2 (by rfl) ⟨11904486, by rfl⟩ : syracuseStep 31745297 = 23808973) B23808973
theorem B44586611 : Blo 1545470 44586611 := bstep (se 1 (by rfl) ⟨33439958, by rfl⟩ : syracuseStep 44586611 = 66879917) B66879917
theorem B5871791 : Blo 1545470 5871791 := bstep (se 1 (by rfl) ⟨4403843, by rfl⟩ : syracuseStep 5871791 = 8807687) B8807687
theorem B1547391 : Blo 1545470 1547391 := bstep (se 1 (by rfl) ⟨1160543, by rfl⟩ : syracuseStep 1547391 = 2321087) B2321087
theorem B21163531 : Blo 1545470 21163531 := bstep (se 1 (by rfl) ⟨15872648, by rfl⟩ : syracuseStep 21163531 = 31745297) B31745297
theorem B29724407 : Blo 1545470 29724407 := bstep (se 1 (by rfl) ⟨22293305, by rfl⟩ : syracuseStep 29724407 = 44586611) B44586611
theorem B3914527 : Blo 1545470 3914527 := bstep (se 1 (by rfl) ⟨2935895, by rfl⟩ : syracuseStep 3914527 = 5871791) B5871791
theorem B5219369 : Blo 1545470 5219369 := bstep (se 2 (by rfl) ⟨1957263, by rfl⟩ : syracuseStep 5219369 = 3914527) B3914527
theorem B28218041 : Blo 1545470 28218041 := bstep (se 2 (by rfl) ⟨10581765, by rfl⟩ : syracuseStep 28218041 = 21163531) B21163531
theorem B19816271 : Blo 1545470 19816271 := bstep (se 1 (by rfl) ⟨14862203, by rfl⟩ : syracuseStep 19816271 = 29724407) B29724407
theorem B18812027 : Blo 1545470 18812027 := bstep (se 1 (by rfl) ⟨14109020, by rfl⟩ : syracuseStep 18812027 = 28218041) B28218041
theorem B13210847 : Blo 1545470 13210847 := bstep (se 1 (by rfl) ⟨9908135, by rfl⟩ : syracuseStep 13210847 = 19816271) B19816271
theorem B3479579 : Blo 1545470 3479579 := bstep (se 1 (by rfl) ⟨2609684, by rfl⟩ : syracuseStep 3479579 = 5219369) B5219369
theorem B8807231 : Blo 1545470 8807231 := bstep (se 1 (by rfl) ⟨6605423, by rfl⟩ : syracuseStep 8807231 = 13210847) B13210847
theorem B2319719 : Blo 1545470 2319719 := bstep (se 1 (by rfl) ⟨1739789, by rfl⟩ : syracuseStep 2319719 = 3479579) B3479579
theorem B50165405 : Blo 1545470 50165405 := bstep (se 3 (by rfl) ⟨9406013, by rfl⟩ : syracuseStep 50165405 = 18812027) B18812027
theorem B33443603 : Blo 1545470 33443603 := bstep (se 1 (by rfl) ⟨25082702, by rfl⟩ : syracuseStep 33443603 = 50165405) B50165405
theorem B5871487 : Blo 1545470 5871487 := bstep (se 1 (by rfl) ⟨4403615, by rfl⟩ : syracuseStep 5871487 = 8807231) B8807231
theorem B1546479 : Blo 1545470 1546479 := bstep (se 1 (by rfl) ⟨1159859, by rfl⟩ : syracuseStep 1546479 = 2319719) B2319719
theorem B7828649 : Blo 1545470 7828649 := bstep (se 2 (by rfl) ⟨2935743, by rfl⟩ : syracuseStep 7828649 = 5871487) B5871487
theorem B22295735 : Blo 1545470 22295735 := bstep (se 1 (by rfl) ⟨16721801, by rfl⟩ : syracuseStep 22295735 = 33443603) B33443603
theorem B5219099 : Blo 1545470 5219099 := bstep (se 1 (by rfl) ⟨3914324, by rfl⟩ : syracuseStep 5219099 = 7828649) B7828649
theorem B14863823 : Blo 1545470 14863823 := bstep (se 1 (by rfl) ⟨11147867, by rfl⟩ : syracuseStep 14863823 = 22295735) B22295735
theorem B9909215 : Blo 1545470 9909215 := bstep (se 1 (by rfl) ⟨7431911, by rfl⟩ : syracuseStep 9909215 = 14863823) B14863823
theorem B3479399 : Blo 1545470 3479399 := bstep (se 1 (by rfl) ⟨2609549, by rfl⟩ : syracuseStep 3479399 = 5219099) B5219099
theorem B2319599 : Blo 1545470 2319599 := bstep (se 1 (by rfl) ⟨1739699, by rfl⟩ : syracuseStep 2319599 = 3479399) B3479399
theorem B6606143 : Blo 1545470 6606143 := bstep (se 1 (by rfl) ⟨4954607, by rfl⟩ : syracuseStep 6606143 = 9909215) B9909215
theorem B4404095 : Blo 1545470 4404095 := bstep (se 1 (by rfl) ⟨3303071, by rfl⟩ : syracuseStep 4404095 = 6606143) B6606143
theorem B1546399 : Blo 1545470 1546399 := bstep (se 1 (by rfl) ⟨1159799, by rfl⟩ : syracuseStep 1546399 = 2319599) B2319599
theorem B2936063 : Blo 1545470 2936063 := bstep (se 1 (by rfl) ⟨2202047, by rfl⟩ : syracuseStep 2936063 = 4404095) B4404095
theorem B1957375 : Blo 1545470 1957375 := bstep (se 1 (by rfl) ⟨1468031, by rfl⟩ : syracuseStep 1957375 = 2936063) B2936063
theorem B2609833 : Blo 1545470 2609833 := bstep (se 2 (by rfl) ⟨978687, by rfl⟩ : syracuseStep 2609833 = 1957375) B1957375
theorem B3479777 : Blo 1545470 3479777 := bstep (se 2 (by rfl) ⟨1304916, by rfl⟩ : syracuseStep 3479777 = 2609833) B2609833
theorem B2319851 : Blo 1545470 2319851 := bstep (se 1 (by rfl) ⟨1739888, by rfl⟩ : syracuseStep 2319851 = 3479777) B3479777
theorem B1546567 : Blo 1545470 1546567 := bstep (se 1 (by rfl) ⟨1159925, by rfl⟩ : syracuseStep 1546567 = 2319851) B2319851

theorem C0 (j : ℕ) (h1 : 386367 ≤ j) (h2 : j ≤ 386866) : Blo 1545470 (4 * j + 3) := by
  interval_cases j
  · exact B1545471
  · exact B1545475
  · exact B1545479
  · exact B1545483
  · exact B1545487
  · exact B1545491
  · exact B1545495
  · exact B1545499
  · exact B1545503
  · exact B1545507
  · exact B1545511
  · exact B1545515
  · exact B1545519
  · exact B1545523
  · exact B1545527
  · exact B1545531
  · exact B1545535
  · exact B1545539
  · exact B1545543
  · exact B1545547
  · exact B1545551
  · exact B1545555
  · exact B1545559
  · exact B1545563
  · exact B1545567
  · exact B1545571
  · exact B1545575
  · exact B1545579
  · exact B1545583
  · exact B1545587
  · exact B1545591
  · exact B1545595
  · exact B1545599
  · exact B1545603
  · exact B1545607
  · exact B1545611
  · exact B1545615
  · exact B1545619
  · exact B1545623
  · exact B1545627
  · exact B1545631
  · exact B1545635
  · exact B1545639
  · exact B1545643
  · exact B1545647
  · exact B1545651
  · exact B1545655
  · exact B1545659
  · exact B1545663
  · exact B1545667
  · exact B1545671
  · exact B1545675
  · exact B1545679
  · exact B1545683
  · exact B1545687
  · exact B1545691
  · exact B1545695
  · exact B1545699
  · exact B1545703
  · exact B1545707
  · exact B1545711
  · exact B1545715
  · exact B1545719
  · exact B1545723
  · exact B1545727
  · exact B1545731
  · exact B1545735
  · exact B1545739
  · exact B1545743
  · exact B1545747
  · exact B1545751
  · exact B1545755
  · exact B1545759
  · exact B1545763
  · exact B1545767
  · exact B1545771
  · exact B1545775
  · exact B1545779
  · exact B1545783
  · exact B1545787
  · exact B1545791
  · exact B1545795
  · exact B1545799
  · exact B1545803
  · exact B1545807
  · exact B1545811
  · exact B1545815
  · exact B1545819
  · exact B1545823
  · exact B1545827
  · exact B1545831
  · exact B1545835
  · exact B1545839
  · exact B1545843
  · exact B1545847
  · exact B1545851
  · exact B1545855
  · exact B1545859
  · exact B1545863
  · exact B1545867
  · exact B1545871
  · exact B1545875
  · exact B1545879
  · exact B1545883
  · exact B1545887
  · exact B1545891
  · exact B1545895
  · exact B1545899
  · exact B1545903
  · exact B1545907
  · exact B1545911
  · exact B1545915
  · exact B1545919
  · exact B1545923
  · exact B1545927
  · exact B1545931
  · exact B1545935
  · exact B1545939
  · exact B1545943
  · exact B1545947
  · exact B1545951
  · exact B1545955
  · exact B1545959
  · exact B1545963
  · exact B1545967
  · exact B1545971
  · exact B1545975
  · exact B1545979
  · exact B1545983
  · exact B1545987
  · exact B1545991
  · exact B1545995
  · exact B1545999
  · exact B1546003
  · exact B1546007
  · exact B1546011
  · exact B1546015
  · exact B1546019
  · exact B1546023
  · exact B1546027
  · exact B1546031
  · exact B1546035
  · exact B1546039
  · exact B1546043
  · exact B1546047
  · exact B1546051
  · exact B1546055
  · exact B1546059
  · exact B1546063
  · exact B1546067
  · exact B1546071
  · exact B1546075
  · exact B1546079
  · exact B1546083
  · exact B1546087
  · exact B1546091
  · exact B1546095
  · exact B1546099
  · exact B1546103
  · exact B1546107
  · exact B1546111
  · exact B1546115
  · exact B1546119
  · exact B1546123
  · exact B1546127
  · exact B1546131
  · exact B1546135
  · exact B1546139
  · exact B1546143
  · exact B1546147
  · exact B1546151
  · exact B1546155
  · exact B1546159
  · exact B1546163
  · exact B1546167
  · exact B1546171
  · exact B1546175
  · exact B1546179
  · exact B1546183
  · exact B1546187
  · exact B1546191
  · exact B1546195
  · exact B1546199
  · exact B1546203
  · exact B1546207
  · exact B1546211
  · exact B1546215
  · exact B1546219
  · exact B1546223
  · exact B1546227
  · exact B1546231
  · exact B1546235
  · exact B1546239
  · exact B1546243
  · exact B1546247
  · exact B1546251
  · exact B1546255
  · exact B1546259
  · exact B1546263
  · exact B1546267
  · exact B1546271
  · exact B1546275
  · exact B1546279
  · exact B1546283
  · exact B1546287
  · exact B1546291
  · exact B1546295
  · exact B1546299
  · exact B1546303
  · exact B1546307
  · exact B1546311
  · exact B1546315
  · exact B1546319
  · exact B1546323
  · exact B1546327
  · exact B1546331
  · exact B1546335
  · exact B1546339
  · exact B1546343
  · exact B1546347
  · exact B1546351
  · exact B1546355
  · exact B1546359
  · exact B1546363
  · exact B1546367
  · exact B1546371
  · exact B1546375
  · exact B1546379
  · exact B1546383
  · exact B1546387
  · exact B1546391
  · exact B1546395
  · exact B1546399
  · exact B1546403
  · exact B1546407
  · exact B1546411
  · exact B1546415
  · exact B1546419
  · exact B1546423
  · exact B1546427
  · exact B1546431
  · exact B1546435
  · exact B1546439
  · exact B1546443
  · exact B1546447
  · exact B1546451
  · exact B1546455
  · exact B1546459
  · exact B1546463
  · exact B1546467
  · exact B1546471
  · exact B1546475
  · exact B1546479
  · exact B1546483
  · exact B1546487
  · exact B1546491
  · exact B1546495
  · exact B1546499
  · exact B1546503
  · exact B1546507
  · exact B1546511
  · exact B1546515
  · exact B1546519
  · exact B1546523
  · exact B1546527
  · exact B1546531
  · exact B1546535
  · exact B1546539
  · exact B1546543
  · exact B1546547
  · exact B1546551
  · exact B1546555
  · exact B1546559
  · exact B1546563
  · exact B1546567
  · exact B1546571
  · exact B1546575
  · exact B1546579
  · exact B1546583
  · exact B1546587
  · exact B1546591
  · exact B1546595
  · exact B1546599
  · exact B1546603
  · exact B1546607
  · exact B1546611
  · exact B1546615
  · exact B1546619
  · exact B1546623
  · exact B1546627
  · exact B1546631
  · exact B1546635
  · exact B1546639
  · exact B1546643
  · exact B1546647
  · exact B1546651
  · exact B1546655
  · exact B1546659
  · exact B1546663
  · exact B1546667
  · exact B1546671
  · exact B1546675
  · exact B1546679
  · exact B1546683
  · exact B1546687
  · exact B1546691
  · exact B1546695
  · exact B1546699
  · exact B1546703
  · exact B1546707
  · exact B1546711
  · exact B1546715
  · exact B1546719
  · exact B1546723
  · exact B1546727
  · exact B1546731
  · exact B1546735
  · exact B1546739
  · exact B1546743
  · exact B1546747
  · exact B1546751
  · exact B1546755
  · exact B1546759
  · exact B1546763
  · exact B1546767
  · exact B1546771
  · exact B1546775
  · exact B1546779
  · exact B1546783
  · exact B1546787
  · exact B1546791
  · exact B1546795
  · exact B1546799
  · exact B1546803
  · exact B1546807
  · exact B1546811
  · exact B1546815
  · exact B1546819
  · exact B1546823
  · exact B1546827
  · exact B1546831
  · exact B1546835
  · exact B1546839
  · exact B1546843
  · exact B1546847
  · exact B1546851
  · exact B1546855
  · exact B1546859
  · exact B1546863
  · exact B1546867
  · exact B1546871
  · exact B1546875
  · exact B1546879
  · exact B1546883
  · exact B1546887
  · exact B1546891
  · exact B1546895
  · exact B1546899
  · exact B1546903
  · exact B1546907
  · exact B1546911
  · exact B1546915
  · exact B1546919
  · exact B1546923
  · exact B1546927
  · exact B1546931
  · exact B1546935
  · exact B1546939
  · exact B1546943
  · exact B1546947
  · exact B1546951
  · exact B1546955
  · exact B1546959
  · exact B1546963
  · exact B1546967
  · exact B1546971
  · exact B1546975
  · exact B1546979
  · exact B1546983
  · exact B1546987
  · exact B1546991
  · exact B1546995
  · exact B1546999
  · exact B1547003
  · exact B1547007
  · exact B1547011
  · exact B1547015
  · exact B1547019
  · exact B1547023
  · exact B1547027
  · exact B1547031
  · exact B1547035
  · exact B1547039
  · exact B1547043
  · exact B1547047
  · exact B1547051
  · exact B1547055
  · exact B1547059
  · exact B1547063
  · exact B1547067
  · exact B1547071
  · exact B1547075
  · exact B1547079
  · exact B1547083
  · exact B1547087
  · exact B1547091
  · exact B1547095
  · exact B1547099
  · exact B1547103
  · exact B1547107
  · exact B1547111
  · exact B1547115
  · exact B1547119
  · exact B1547123
  · exact B1547127
  · exact B1547131
  · exact B1547135
  · exact B1547139
  · exact B1547143
  · exact B1547147
  · exact B1547151
  · exact B1547155
  · exact B1547159
  · exact B1547163
  · exact B1547167
  · exact B1547171
  · exact B1547175
  · exact B1547179
  · exact B1547183
  · exact B1547187
  · exact B1547191
  · exact B1547195
  · exact B1547199
  · exact B1547203
  · exact B1547207
  · exact B1547211
  · exact B1547215
  · exact B1547219
  · exact B1547223
  · exact B1547227
  · exact B1547231
  · exact B1547235
  · exact B1547239
  · exact B1547243
  · exact B1547247
  · exact B1547251
  · exact B1547255
  · exact B1547259
  · exact B1547263
  · exact B1547267
  · exact B1547271
  · exact B1547275
  · exact B1547279
  · exact B1547283
  · exact B1547287
  · exact B1547291
  · exact B1547295
  · exact B1547299
  · exact B1547303
  · exact B1547307
  · exact B1547311
  · exact B1547315
  · exact B1547319
  · exact B1547323
  · exact B1547327
  · exact B1547331
  · exact B1547335
  · exact B1547339
  · exact B1547343
  · exact B1547347
  · exact B1547351
  · exact B1547355
  · exact B1547359
  · exact B1547363
  · exact B1547367
  · exact B1547371
  · exact B1547375
  · exact B1547379
  · exact B1547383
  · exact B1547387
  · exact B1547391
  · exact B1547395
  · exact B1547399
  · exact B1547403
  · exact B1547407
  · exact B1547411
  · exact B1547415
  · exact B1547419
  · exact B1547423
  · exact B1547427
  · exact B1547431
  · exact B1547435
  · exact B1547439
  · exact B1547443
  · exact B1547447
  · exact B1547451
  · exact B1547455
  · exact B1547459
  · exact B1547463
  · exact B1547467

theorem solution (m : ℕ) (hlo : 1545470 ≤ m) (hhi : m ≤ 1547470) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 386367 ≤ j := by omega
    have hj2 : j ≤ 386866 := by omega
    have hb : Blo 1545470 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
