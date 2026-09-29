-- Prove2me | solution 1 for syracuse_descends_range_1865634_1867634
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:12:11.805824+00:00
-- url     : https://prove2.me/submissions/cf31d47f-6377-4827-8807-a37339d4f635

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


theorem B2990125 : Blo 1865634 2990125 := bbase (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) (by norm_num)
theorem B14172245 : Blo 1865634 14172245 := bbase (se 8 (by rfl) ⟨83040, by rfl⟩ : syracuseStep 14172245 = 166081) (by norm_num)
theorem B4726957 : Blo 1865634 4726957 := bbase (se 3 (by rfl) ⟨886304, by rfl⟩ : syracuseStep 4726957 = 1772609) (by norm_num)
theorem B6299909 : Blo 1865634 6299909 := bbase (se 4 (by rfl) ⟨590616, by rfl⟩ : syracuseStep 6299909 = 1181233) (by norm_num)
theorem B4727069 : Blo 1865634 4727069 := bbase (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) (by norm_num)
theorem B9445733 : Blo 1865634 9445733 := bbase (se 4 (by rfl) ⟨885537, by rfl⟩ : syracuseStep 9445733 = 1771075) (by norm_num)
theorem B5390693 : Blo 1865634 5390693 := bbase (se 4 (by rfl) ⟨505377, by rfl⟩ : syracuseStep 5390693 = 1010755) (by norm_num)
theorem B7971205 : Blo 1865634 7971205 := bbase (se 4 (by rfl) ⟨747300, by rfl⟩ : syracuseStep 7971205 = 1494601) (by norm_num)
theorem B4727261 : Blo 1865634 4727261 := bbase (se 3 (by rfl) ⟨886361, by rfl⟩ : syracuseStep 4727261 = 1772723) (by norm_num)
theorem B3785221 : Blo 1865634 3785221 := bbase (se 4 (by rfl) ⟨354864, by rfl⟩ : syracuseStep 3785221 = 709729) (by norm_num)
theorem B5677589 : Blo 1865634 5677589 := bbase (se 6 (by rfl) ⟨133068, by rfl⟩ : syracuseStep 5677589 = 266137) (by norm_num)
theorem B11960885 : Blo 1865634 11960885 := bbase (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) (by norm_num)
theorem B9093701 : Blo 1865634 9093701 := bbase (se 4 (by rfl) ⟨852534, by rfl⟩ : syracuseStep 9093701 = 1705069) (by norm_num)
theorem B7570037 : Blo 1865634 7570037 := bbase (se 5 (by rfl) ⟨354845, by rfl⟩ : syracuseStep 7570037 = 709691) (by norm_num)
theorem B15131285 : Blo 1865634 15131285 := bbase (se 6 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 15131285 = 709279) (by norm_num)
theorem B6300341 : Blo 1865634 6300341 := bbase (se 5 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 6300341 = 590657) (by norm_num)
theorem B5980853 : Blo 1865634 5980853 := bbase (se 5 (by rfl) ⟨280352, by rfl⟩ : syracuseStep 5980853 = 560705) (by norm_num)
theorem B2990837 : Blo 1865634 2990837 := bbase (se 5 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 2990837 = 280391) (by norm_num)
theorem B3031805 : Blo 1865634 3031805 := bbase (se 3 (by rfl) ⟨568463, by rfl⟩ : syracuseStep 3031805 = 1136927) (by norm_num)
theorem B3834629 : Blo 1865634 3834629 := bbase (se 4 (by rfl) ⟨359496, by rfl⟩ : syracuseStep 3834629 = 718993) (by norm_num)
theorem B10625813 : Blo 1865634 10625813 := bbase (se 6 (by rfl) ⟨249042, by rfl⟩ : syracuseStep 10625813 = 498085) (by norm_num)
theorem B5317589 : Blo 1865634 5317589 := bbase (se 7 (by rfl) ⟨62315, by rfl⟩ : syracuseStep 5317589 = 124631) (by norm_num)
theorem B10224629 : Blo 1865634 10224629 := bbase (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) (by norm_num)
theorem B6300773 : Blo 1865634 6300773 := bbase (se 4 (by rfl) ⟨590697, by rfl⟩ : syracuseStep 6300773 = 1181395) (by norm_num)
theorem B3785869 : Blo 1865634 3785869 := bbase (se 3 (by rfl) ⟨709850, by rfl⟩ : syracuseStep 3785869 = 1419701) (by norm_num)
theorem B9454805 : Blo 1865634 9454805 := bbase (se 7 (by rfl) ⟨110798, by rfl⟩ : syracuseStep 9454805 = 221597) (by norm_num)
theorem B5047589 : Blo 1865634 5047589 := bbase (se 4 (by rfl) ⟨473211, by rfl⟩ : syracuseStep 5047589 = 946423) (by norm_num)
theorem B7087445 : Blo 1865634 7087445 := bbase (se 12 (by rfl) ⟨2595, by rfl⟩ : syracuseStep 7087445 = 5191) (by norm_num)
theorem B1918297 : Blo 1865634 1918297 := bbase (se 2 (by rfl) ⟨719361, by rfl⟩ : syracuseStep 1918297 = 1438723) (by norm_num)
theorem B2991509 : Blo 1865634 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B4040189 : Blo 1865634 4040189 := bbase (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) (by norm_num)
theorem B6301205 : Blo 1865634 6301205 := bbase (se 6 (by rfl) ⟨147684, by rfl⟩ : syracuseStep 6301205 = 295369) (by norm_num)
theorem B6727205 : Blo 1865634 6727205 := bbase (se 4 (by rfl) ⟨630675, by rfl⟩ : syracuseStep 6727205 = 1261351) (by norm_num)
theorem B9447029 : Blo 1865634 9447029 := bbase (se 5 (by rfl) ⟨442829, by rfl⟩ : syracuseStep 9447029 = 885659) (by norm_num)
theorem B7087733 : Blo 1865634 7087733 := bbase (se 5 (by rfl) ⟨332237, by rfl⟩ : syracuseStep 7087733 = 664475) (by norm_num)
theorem B5318261 : Blo 1865634 5318261 := bbase (se 5 (by rfl) ⟨249293, by rfl⟩ : syracuseStep 5318261 = 498587) (by norm_num)
theorem B2098849 : Blo 1865634 2098849 := bbase (se 2 (by rfl) ⟨787068, by rfl⟩ : syracuseStep 2098849 = 1574137) (by norm_num)
theorem B6727349 : Blo 1865634 6727349 := bbase (se 5 (by rfl) ⟨315344, by rfl⟩ : syracuseStep 6727349 = 630689) (by norm_num)
theorem B2098885 : Blo 1865634 2098885 := bbase (se 4 (by rfl) ⟨196770, by rfl⟩ : syracuseStep 2098885 = 393541) (by norm_num)
theorem B4548325 : Blo 1865634 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B2098921 : Blo 1865634 2098921 := bbase (se 2 (by rfl) ⟨787095, by rfl⟩ : syracuseStep 2098921 = 1574191) (by norm_num)
theorem B5981941 : Blo 1865634 5981941 := bbase (se 5 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 5981941 = 560807) (by norm_num)
theorem B2098957 : Blo 1865634 2098957 := bbase (se 3 (by rfl) ⟨393554, by rfl⟩ : syracuseStep 2098957 = 787109) (by norm_num)
theorem B7669525 : Blo 1865634 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B2098993 : Blo 1865634 2098993 := bbase (se 2 (by rfl) ⟨787122, by rfl⟩ : syracuseStep 2098993 = 1574245) (by norm_num)
theorem B2099029 : Blo 1865634 2099029 := bbase (se 9 (by rfl) ⟨6149, by rfl⟩ : syracuseStep 2099029 = 12299) (by norm_num)
theorem B2099065 : Blo 1865634 2099065 := bbase (se 2 (by rfl) ⟨787149, by rfl⟩ : syracuseStep 2099065 = 1574299) (by norm_num)
theorem B2361241 : Blo 1865634 2361241 := bbase (se 2 (by rfl) ⟨885465, by rfl⟩ : syracuseStep 2361241 = 1770931) (by norm_num)
theorem B2099101 : Blo 1865634 2099101 := bbase (se 3 (by rfl) ⟨393581, by rfl⟩ : syracuseStep 2099101 = 787163) (by norm_num)
theorem B1992605 : Blo 1865634 1992605 := bbase (se 3 (by rfl) ⟨373613, by rfl⟩ : syracuseStep 1992605 = 747227) (by norm_num)
theorem B10626997 : Blo 1865634 10626997 := bbase (se 5 (by rfl) ⟨498140, by rfl⟩ : syracuseStep 10626997 = 996281) (by norm_num)
theorem B2099137 : Blo 1865634 2099137 := bbase (se 2 (by rfl) ⟨787176, by rfl⟩ : syracuseStep 2099137 = 1574353) (by norm_num)
theorem B6301637 : Blo 1865634 6301637 := bbase (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) (by norm_num)
theorem B2099173 : Blo 1865634 2099173 := bbase (se 4 (by rfl) ⟨196797, by rfl⟩ : syracuseStep 2099173 = 393595) (by norm_num)
theorem B2099209 : Blo 1865634 2099209 := bbase (se 2 (by rfl) ⟨787203, by rfl⟩ : syracuseStep 2099209 = 1574407) (by norm_num)
theorem B2099245 : Blo 1865634 2099245 := bbase (se 3 (by rfl) ⟨393608, by rfl⟩ : syracuseStep 2099245 = 787217) (by norm_num)
theorem B2361413 : Blo 1865634 2361413 := bbase (se 4 (by rfl) ⟨221382, by rfl⟩ : syracuseStep 2361413 = 442765) (by norm_num)
theorem B2099281 : Blo 1865634 2099281 := bbase (se 2 (by rfl) ⟨787230, by rfl⟩ : syracuseStep 2099281 = 1574461) (by norm_num)
theorem B2099317 : Blo 1865634 2099317 := bbase (se 5 (by rfl) ⟨98405, by rfl⟩ : syracuseStep 2099317 = 196811) (by norm_num)
theorem B2361469 : Blo 1865634 2361469 := bbase (se 3 (by rfl) ⟨442775, by rfl⟩ : syracuseStep 2361469 = 885551) (by norm_num)
theorem B1992853 : Blo 1865634 1992853 := bbase (se 6 (by rfl) ⟨46707, by rfl⟩ : syracuseStep 1992853 = 93415) (by norm_num)
theorem B17025173 : Blo 1865634 17025173 := bbase (se 6 (by rfl) ⟨399027, by rfl⟩ : syracuseStep 17025173 = 798055) (by norm_num)
theorem B2099353 : Blo 1865634 2099353 := bbase (se 2 (by rfl) ⟨787257, by rfl⟩ : syracuseStep 2099353 = 1574515) (by norm_num)
theorem B2099389 : Blo 1865634 2099389 := bbase (se 3 (by rfl) ⟨393635, by rfl⟩ : syracuseStep 2099389 = 787271) (by norm_num)
theorem B10774741 : Blo 1865634 10774741 := bbase (se 7 (by rfl) ⟨126266, by rfl⟩ : syracuseStep 10774741 = 252533) (by norm_num)
theorem B2361565 : Blo 1865634 2361565 := bbase (se 3 (by rfl) ⟨442793, by rfl⟩ : syracuseStep 2361565 = 885587) (by norm_num)
theorem B2099425 : Blo 1865634 2099425 := bbase (se 2 (by rfl) ⟨787284, by rfl⟩ : syracuseStep 2099425 = 1574569) (by norm_num)
theorem B2099461 : Blo 1865634 2099461 := bbase (se 4 (by rfl) ⟨196824, by rfl⟩ : syracuseStep 2099461 = 393649) (by norm_num)
theorem B2099497 : Blo 1865634 2099497 := bbase (se 2 (by rfl) ⟨787311, by rfl⟩ : syracuseStep 2099497 = 1574623) (by norm_num)
theorem B2099533 : Blo 1865634 2099533 := bbase (se 3 (by rfl) ⟨393662, by rfl⟩ : syracuseStep 2099533 = 787325) (by norm_num)
theorem B2099569 : Blo 1865634 2099569 := bbase (se 2 (by rfl) ⟨787338, by rfl⟩ : syracuseStep 2099569 = 1574677) (by norm_num)
theorem B6302069 : Blo 1865634 6302069 := bbase (se 5 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 6302069 = 590819) (by norm_num)
theorem B2361737 : Blo 1865634 2361737 := bbase (se 2 (by rfl) ⟨885651, by rfl⟩ : syracuseStep 2361737 = 1771303) (by norm_num)
theorem B2099605 : Blo 1865634 2099605 := bbase (se 6 (by rfl) ⟨49209, by rfl⟩ : syracuseStep 2099605 = 98419) (by norm_num)
theorem B2099641 : Blo 1865634 2099641 := bbase (se 2 (by rfl) ⟨787365, by rfl⟩ : syracuseStep 2099641 = 1574731) (by norm_num)
theorem B2361793 : Blo 1865634 2361793 := bbase (se 2 (by rfl) ⟨885672, by rfl⟩ : syracuseStep 2361793 = 1771345) (by norm_num)
theorem B2099677 : Blo 1865634 2099677 := bbase (se 3 (by rfl) ⟨393689, by rfl⟩ : syracuseStep 2099677 = 787379) (by norm_num)
theorem B2099713 : Blo 1865634 2099713 := bbase (se 2 (by rfl) ⟨787392, by rfl⟩ : syracuseStep 2099713 = 1574785) (by norm_num)
theorem B3148301 : Blo 1865634 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B2361889 : Blo 1865634 2361889 := bbase (se 2 (by rfl) ⟨885708, by rfl⟩ : syracuseStep 2361889 = 1771417) (by norm_num)
theorem B2099749 : Blo 1865634 2099749 := bbase (se 4 (by rfl) ⟨196851, by rfl⟩ : syracuseStep 2099749 = 393703) (by norm_num)
theorem B2099785 : Blo 1865634 2099785 := bbase (se 2 (by rfl) ⟨787419, by rfl⟩ : syracuseStep 2099785 = 1574839) (by norm_num)
theorem B1993297 : Blo 1865634 1993297 := bbase (se 2 (by rfl) ⟨747486, by rfl⟩ : syracuseStep 1993297 = 1494973) (by norm_num)
theorem B4483669 : Blo 1865634 4483669 := bbase (se 8 (by rfl) ⟨26271, by rfl⟩ : syracuseStep 4483669 = 52543) (by norm_num)
theorem B2099821 : Blo 1865634 2099821 := bbase (se 3 (by rfl) ⟨393716, by rfl⟩ : syracuseStep 2099821 = 787433) (by norm_num)
theorem B3148429 : Blo 1865634 3148429 := bbase (se 3 (by rfl) ⟨590330, by rfl⟩ : syracuseStep 3148429 = 1180661) (by norm_num)
theorem B2656909 : Blo 1865634 2656909 := bbase (se 3 (by rfl) ⟨498170, by rfl⟩ : syracuseStep 2656909 = 996341) (by norm_num)
theorem B1993357 : Blo 1865634 1993357 := bbase (se 3 (by rfl) ⟨373754, by rfl⟩ : syracuseStep 1993357 = 747509) (by norm_num)
theorem B2099857 : Blo 1865634 2099857 := bbase (se 2 (by rfl) ⟨787446, by rfl⟩ : syracuseStep 2099857 = 1574893) (by norm_num)
theorem B6728357 : Blo 1865634 6728357 := bbase (se 4 (by rfl) ⟨630783, by rfl⟩ : syracuseStep 6728357 = 1261567) (by norm_num)
theorem B2099893 : Blo 1865634 2099893 := bbase (se 5 (by rfl) ⟨98432, by rfl⟩ : syracuseStep 2099893 = 196865) (by norm_num)
theorem B2362061 : Blo 1865634 2362061 := bbase (se 3 (by rfl) ⟨442886, by rfl⟩ : syracuseStep 2362061 = 885773) (by norm_num)
theorem B2099929 : Blo 1865634 2099929 := bbase (se 2 (by rfl) ⟨787473, by rfl⟩ : syracuseStep 2099929 = 1574947) (by norm_num)
theorem B3148517 : Blo 1865634 3148517 := bbase (se 4 (by rfl) ⟨295173, by rfl⟩ : syracuseStep 3148517 = 590347) (by norm_num)
theorem B2099965 : Blo 1865634 2099965 := bbase (se 3 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 2099965 = 787487) (by norm_num)
theorem B2362117 : Blo 1865634 2362117 := bbase (se 4 (by rfl) ⟨221448, by rfl⟩ : syracuseStep 2362117 = 442897) (by norm_num)
theorem B7088917 : Blo 1865634 7088917 := bbase (se 6 (by rfl) ⟨166146, by rfl⟩ : syracuseStep 7088917 = 332293) (by norm_num)
theorem B2100001 : Blo 1865634 2100001 := bbase (se 2 (by rfl) ⟨787500, by rfl⟩ : syracuseStep 2100001 = 1575001) (by norm_num)
theorem B6302501 : Blo 1865634 6302501 := bbase (se 4 (by rfl) ⟨590859, by rfl⟩ : syracuseStep 6302501 = 1181719) (by norm_num)
theorem B2100037 : Blo 1865634 2100037 := bbase (se 4 (by rfl) ⟨196878, by rfl⟩ : syracuseStep 2100037 = 393757) (by norm_num)
theorem B8973125 : Blo 1865634 8973125 := bbase (se 4 (by rfl) ⟨841230, by rfl⟩ : syracuseStep 8973125 = 1682461) (by norm_num)
theorem B3148645 : Blo 1865634 3148645 := bbase (se 4 (by rfl) ⟨295185, by rfl⟩ : syracuseStep 3148645 = 590371) (by norm_num)
theorem B2362213 : Blo 1865634 2362213 := bbase (se 4 (by rfl) ⟨221457, by rfl⟩ : syracuseStep 2362213 = 442915) (by norm_num)
theorem B2100073 : Blo 1865634 2100073 := bbase (se 2 (by rfl) ⟨787527, by rfl⟩ : syracuseStep 2100073 = 1575055) (by norm_num)
theorem B3541877 : Blo 1865634 3541877 := bbase (se 5 (by rfl) ⟨166025, by rfl⟩ : syracuseStep 3541877 = 332051) (by norm_num)
theorem B9448325 : Blo 1865634 9448325 := bbase (se 4 (by rfl) ⟨885780, by rfl⟩ : syracuseStep 9448325 = 1771561) (by norm_num)
theorem B5983109 : Blo 1865634 5983109 := bbase (se 4 (by rfl) ⟨560916, by rfl⟩ : syracuseStep 5983109 = 1121833) (by norm_num)
theorem B2100109 : Blo 1865634 2100109 := bbase (se 3 (by rfl) ⟨393770, by rfl⟩ : syracuseStep 2100109 = 787541) (by norm_num)
theorem B15944597 : Blo 1865634 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B2272177 : Blo 1865634 2272177 := bbase (se 2 (by rfl) ⟨852066, by rfl⟩ : syracuseStep 2272177 = 1704133) (by norm_num)
theorem B2100145 : Blo 1865634 2100145 := bbase (se 2 (by rfl) ⟨787554, by rfl⟩ : syracuseStep 2100145 = 1575109) (by norm_num)
theorem B3148733 : Blo 1865634 3148733 := bbase (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) (by norm_num)
theorem B1993673 : Blo 1865634 1993673 := bbase (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) (by norm_num)
theorem B2100181 : Blo 1865634 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B2100217 : Blo 1865634 2100217 := bbase (se 2 (by rfl) ⟨787581, by rfl⟩ : syracuseStep 2100217 = 1575163) (by norm_num)
theorem B2362385 : Blo 1865634 2362385 := bbase (se 2 (by rfl) ⟨885894, by rfl⟩ : syracuseStep 2362385 = 1771789) (by norm_num)
theorem B11955221 : Blo 1865634 11955221 := bbase (se 6 (by rfl) ⟨280200, by rfl⟩ : syracuseStep 11955221 = 560401) (by norm_num)
theorem B2100253 : Blo 1865634 2100253 := bbase (se 3 (by rfl) ⟨393797, by rfl⟩ : syracuseStep 2100253 = 787595) (by norm_num)
theorem B3148861 : Blo 1865634 3148861 := bbase (se 3 (by rfl) ⟨590411, by rfl⟩ : syracuseStep 3148861 = 1180823) (by norm_num)
theorem B2100289 : Blo 1865634 2100289 := bbase (se 2 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 2100289 = 1575217) (by norm_num)
theorem B7089221 : Blo 1865634 7089221 := bbase (se 4 (by rfl) ⟨664614, by rfl⟩ : syracuseStep 7089221 = 1329229) (by norm_num)
theorem B2362441 : Blo 1865634 2362441 := bbase (se 2 (by rfl) ⟨885915, by rfl⟩ : syracuseStep 2362441 = 1771831) (by norm_num)
theorem B2100325 : Blo 1865634 2100325 := bbase (se 4 (by rfl) ⟨196905, by rfl⟩ : syracuseStep 2100325 = 393811) (by norm_num)
theorem B2100361 : Blo 1865634 2100361 := bbase (se 2 (by rfl) ⟨787635, by rfl⟩ : syracuseStep 2100361 = 1575271) (by norm_num)
theorem B3148949 : Blo 1865634 3148949 := bbase (se 6 (by rfl) ⟨73803, by rfl⟩ : syracuseStep 3148949 = 147607) (by norm_num)
theorem B2428057 : Blo 1865634 2428057 := bbase (se 2 (by rfl) ⟨910521, by rfl⟩ : syracuseStep 2428057 = 1821043) (by norm_num)
theorem B2362537 : Blo 1865634 2362537 := bbase (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) (by norm_num)
theorem B2100397 : Blo 1865634 2100397 := bbase (se 3 (by rfl) ⟨393824, by rfl⟩ : syracuseStep 2100397 = 787649) (by norm_num)
theorem B4484285 : Blo 1865634 4484285 := bbase (se 3 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 4484285 = 1681607) (by norm_num)
theorem B3591373 : Blo 1865634 3591373 := bbase (se 3 (by rfl) ⟨673382, by rfl⟩ : syracuseStep 3591373 = 1346765) (by norm_num)
theorem B2100433 : Blo 1865634 2100433 := bbase (se 2 (by rfl) ⟨787662, by rfl⟩ : syracuseStep 2100433 = 1575325) (by norm_num)
theorem B6302933 : Blo 1865634 6302933 := bbase (se 7 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 6302933 = 147725) (by norm_num)
theorem B4484341 : Blo 1865634 4484341 := bbase (se 5 (by rfl) ⟨210203, by rfl⟩ : syracuseStep 4484341 = 420407) (by norm_num)
theorem B2100469 : Blo 1865634 2100469 := bbase (se 5 (by rfl) ⟨98459, by rfl⟩ : syracuseStep 2100469 = 196919) (by norm_num)
theorem B3149077 : Blo 1865634 3149077 := bbase (se 6 (by rfl) ⟨73806, by rfl⟩ : syracuseStep 3149077 = 147613) (by norm_num)
theorem B2100505 : Blo 1865634 2100505 := bbase (se 2 (by rfl) ⟨787689, by rfl⟩ : syracuseStep 2100505 = 1575379) (by norm_num)
theorem B2395417 : Blo 1865634 2395417 := bbase (se 2 (by rfl) ⟨898281, by rfl⟩ : syracuseStep 2395417 = 1796563) (by norm_num)
theorem B7974197 : Blo 1865634 7974197 := bbase (se 5 (by rfl) ⟨373790, by rfl⟩ : syracuseStep 7974197 = 747581) (by norm_num)
theorem B2100541 : Blo 1865634 2100541 := bbase (se 3 (by rfl) ⟨393851, by rfl⟩ : syracuseStep 2100541 = 787703) (by norm_num)
theorem B2837845 : Blo 1865634 2837845 := bbase (se 11 (by rfl) ⟨2078, by rfl⟩ : syracuseStep 2837845 = 4157) (by norm_num)
theorem B2362709 : Blo 1865634 2362709 := bbase (se 11 (by rfl) ⟨1730, by rfl⟩ : syracuseStep 2362709 = 3461) (by norm_num)
theorem B4197725 : Blo 1865634 4197725 := bbase (se 3 (by rfl) ⟨787073, by rfl⟩ : syracuseStep 4197725 = 1574147) (by norm_num)
theorem B2100577 : Blo 1865634 2100577 := bbase (se 2 (by rfl) ⟨787716, by rfl⟩ : syracuseStep 2100577 = 1575433) (by norm_num)
theorem B3149165 : Blo 1865634 3149165 := bbase (se 3 (by rfl) ⟨590468, by rfl⟩ : syracuseStep 3149165 = 1180937) (by norm_num)
theorem B2100613 : Blo 1865634 2100613 := bbase (se 4 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 2100613 = 393865) (by norm_num)
theorem B1994117 : Blo 1865634 1994117 := bbase (se 4 (by rfl) ⟨186948, by rfl⟩ : syracuseStep 1994117 = 373897) (by norm_num)
theorem B2362765 : Blo 1865634 2362765 := bbase (se 3 (by rfl) ⟨443018, by rfl⟩ : syracuseStep 2362765 = 886037) (by norm_num)
theorem B38309269 : Blo 1865634 38309269 := bbase (se 6 (by rfl) ⟨897873, by rfl⟩ : syracuseStep 38309269 = 1795747) (by norm_num)
theorem B2395541 : Blo 1865634 2395541 := bbase (se 6 (by rfl) ⟨56145, by rfl⟩ : syracuseStep 2395541 = 112291) (by norm_num)
theorem B4197797 : Blo 1865634 4197797 := bbase (se 4 (by rfl) ⟨393543, by rfl⟩ : syracuseStep 4197797 = 787087) (by norm_num)
theorem B2657701 : Blo 1865634 2657701 := bbase (se 4 (by rfl) ⟨249159, by rfl⟩ : syracuseStep 2657701 = 498319) (by norm_num)
theorem B2100649 : Blo 1865634 2100649 := bbase (se 2 (by rfl) ⟨787743, by rfl⟩ : syracuseStep 2100649 = 1575487) (by norm_num)
theorem B1994177 : Blo 1865634 1994177 := bbase (se 2 (by rfl) ⟨747816, by rfl⟩ : syracuseStep 1994177 = 1495633) (by norm_num)
theorem B2100685 : Blo 1865634 2100685 := bbase (se 3 (by rfl) ⟨393878, by rfl⟩ : syracuseStep 2100685 = 787757) (by norm_num)
theorem B17935829 : Blo 1865634 17935829 := bbase (se 7 (by rfl) ⟨210185, by rfl⟩ : syracuseStep 17935829 = 420371) (by norm_num)
theorem B3984869 : Blo 1865634 3984869 := bbase (se 4 (by rfl) ⟨373581, by rfl⟩ : syracuseStep 3984869 = 747163) (by norm_num)
theorem B4197869 : Blo 1865634 4197869 := bbase (se 3 (by rfl) ⟨787100, by rfl⟩ : syracuseStep 4197869 = 1574201) (by norm_num)
theorem B3149293 : Blo 1865634 3149293 := bbase (se 3 (by rfl) ⟨590492, by rfl⟩ : syracuseStep 3149293 = 1180985) (by norm_num)
theorem B2362861 : Blo 1865634 2362861 := bbase (se 3 (by rfl) ⟨443036, by rfl⟩ : syracuseStep 2362861 = 886073) (by norm_num)
theorem B2100721 : Blo 1865634 2100721 := bbase (se 2 (by rfl) ⟨787770, by rfl⟩ : syracuseStep 2100721 = 1575541) (by norm_num)
theorem B17264117 : Blo 1865634 17264117 := bbase (se 5 (by rfl) ⟨809255, by rfl⟩ : syracuseStep 17264117 = 1618511) (by norm_num)
theorem B13454869 : Blo 1865634 13454869 := bbase (se 6 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 13454869 = 630697) (by norm_num)
theorem B2100757 : Blo 1865634 2100757 := bbase (se 6 (by rfl) ⟨49236, by rfl⟩ : syracuseStep 2100757 = 98473) (by norm_num)
theorem B4197941 : Blo 1865634 4197941 := bbase (se 5 (by rfl) ⟨196778, by rfl⟩ : syracuseStep 4197941 = 393557) (by norm_num)
theorem B2100793 : Blo 1865634 2100793 := bbase (se 2 (by rfl) ⟨787797, by rfl⟩ : syracuseStep 2100793 = 1575595) (by norm_num)
theorem B2395705 : Blo 1865634 2395705 := bbase (se 2 (by rfl) ⟨898389, by rfl⟩ : syracuseStep 2395705 = 1796779) (by norm_num)
theorem B1994305 : Blo 1865634 1994305 := bbase (se 2 (by rfl) ⟨747864, by rfl⟩ : syracuseStep 1994305 = 1495729) (by norm_num)
theorem B3149381 : Blo 1865634 3149381 := bbase (se 4 (by rfl) ⟨295254, by rfl⟩ : syracuseStep 3149381 = 590509) (by norm_num)
theorem B2100829 : Blo 1865634 2100829 := bbase (se 3 (by rfl) ⟨393905, by rfl⟩ : syracuseStep 2100829 = 787811) (by norm_num)
theorem B3542629 : Blo 1865634 3542629 := bbase (se 4 (by rfl) ⟨332121, by rfl⟩ : syracuseStep 3542629 = 664243) (by norm_num)
theorem B4198013 : Blo 1865634 4198013 := bbase (se 3 (by rfl) ⟨787127, by rfl⟩ : syracuseStep 4198013 = 1574255) (by norm_num)
theorem B2100865 : Blo 1865634 2100865 := bbase (se 2 (by rfl) ⟨787824, by rfl⟩ : syracuseStep 2100865 = 1575649) (by norm_num)
theorem B6819461 : Blo 1865634 6819461 := bbase (se 4 (by rfl) ⟨639324, by rfl⟩ : syracuseStep 6819461 = 1278649) (by norm_num)
theorem B2363033 : Blo 1865634 2363033 := bbase (se 2 (by rfl) ⟨886137, by rfl⟩ : syracuseStep 2363033 = 1772275) (by norm_num)
theorem B2100901 : Blo 1865634 2100901 := bbase (se 4 (by rfl) ⟨196959, by rfl⟩ : syracuseStep 2100901 = 393919) (by norm_num)
theorem B4198085 : Blo 1865634 4198085 := bbase (se 4 (by rfl) ⟨393570, by rfl⟩ : syracuseStep 4198085 = 787141) (by norm_num)
theorem B3149509 : Blo 1865634 3149509 := bbase (se 4 (by rfl) ⟨295266, by rfl⟩ : syracuseStep 3149509 = 590533) (by norm_num)
theorem B2100937 : Blo 1865634 2100937 := bbase (se 2 (by rfl) ⟨787851, by rfl⟩ : syracuseStep 2100937 = 1575703) (by norm_num)
theorem B2363089 : Blo 1865634 2363089 := bbase (se 2 (by rfl) ⟨886158, by rfl⟩ : syracuseStep 2363089 = 1772317) (by norm_num)
theorem B2100973 : Blo 1865634 2100973 := bbase (se 3 (by rfl) ⟨393932, by rfl⟩ : syracuseStep 2100973 = 787865) (by norm_num)
theorem B4722421 : Blo 1865634 4722421 := bbase (se 5 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 4722421 = 442727) (by norm_num)
theorem B3542773 : Blo 1865634 3542773 := bbase (se 5 (by rfl) ⟨166067, by rfl⟩ : syracuseStep 3542773 = 332135) (by norm_num)
theorem B2658037 : Blo 1865634 2658037 := bbase (se 5 (by rfl) ⟨124595, by rfl⟩ : syracuseStep 2658037 = 249191) (by norm_num)
theorem B4198157 : Blo 1865634 4198157 := bbase (se 3 (by rfl) ⟨787154, by rfl⟩ : syracuseStep 4198157 = 1574309) (by norm_num)
theorem B2101009 : Blo 1865634 2101009 := bbase (se 2 (by rfl) ⟨787878, by rfl⟩ : syracuseStep 2101009 = 1575757) (by norm_num)
theorem B3149597 : Blo 1865634 3149597 := bbase (se 3 (by rfl) ⟨590549, by rfl⟩ : syracuseStep 3149597 = 1181099) (by norm_num)
theorem B2363185 : Blo 1865634 2363185 := bbase (se 2 (by rfl) ⟨886194, by rfl⟩ : syracuseStep 2363185 = 1772389) (by norm_num)
theorem B2101045 : Blo 1865634 2101045 := bbase (se 5 (by rfl) ⟨98486, by rfl⟩ : syracuseStep 2101045 = 196973) (by norm_num)
theorem B4198229 : Blo 1865634 4198229 := bbase (se 9 (by rfl) ⟨12299, by rfl⟩ : syracuseStep 4198229 = 24599) (by norm_num)
theorem B2101081 : Blo 1865634 2101081 := bbase (se 2 (by rfl) ⟨787905, by rfl⟩ : syracuseStep 2101081 = 1575811) (by norm_num)
theorem B4722533 : Blo 1865634 4722533 := bbase (se 4 (by rfl) ⟨442737, by rfl⟩ : syracuseStep 4722533 = 885475) (by norm_num)
theorem B10628981 : Blo 1865634 10628981 := bbase (se 5 (by rfl) ⟨498233, by rfl⟩ : syracuseStep 10628981 = 996467) (by norm_num)
theorem B5386133 : Blo 1865634 5386133 := bbase (se 6 (by rfl) ⟨126237, by rfl⟩ : syracuseStep 5386133 = 252475) (by norm_num)
theorem B3542933 : Blo 1865634 3542933 := bbase (se 6 (by rfl) ⟨83037, by rfl⟩ : syracuseStep 3542933 = 166075) (by norm_num)
theorem B4198301 : Blo 1865634 4198301 := bbase (se 3 (by rfl) ⟨787181, by rfl⟩ : syracuseStep 4198301 = 1574363) (by norm_num)
theorem B3149725 : Blo 1865634 3149725 := bbase (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) (by norm_num)
theorem B2658253 : Blo 1865634 2658253 := bbase (se 3 (by rfl) ⟨498422, by rfl⟩ : syracuseStep 2658253 = 996845) (by norm_num)
theorem B2363357 : Blo 1865634 2363357 := bbase (se 3 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 2363357 = 886259) (by norm_num)
theorem B4198373 : Blo 1865634 4198373 := bbase (se 4 (by rfl) ⟨393597, by rfl⟩ : syracuseStep 4198373 = 787195) (by norm_num)
theorem B8081381 : Blo 1865634 8081381 := bbase (se 4 (by rfl) ⟨757629, by rfl⟩ : syracuseStep 8081381 = 1515259) (by norm_num)
theorem B3149813 : Blo 1865634 3149813 := bbase (se 5 (by rfl) ⟨147647, by rfl⟩ : syracuseStep 3149813 = 295295) (by norm_num)
theorem B5386261 : Blo 1865634 5386261 := bbase (se 6 (by rfl) ⟨126240, by rfl⟩ : syracuseStep 5386261 = 252481) (by norm_num)
theorem B2363413 : Blo 1865634 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B4722725 : Blo 1865634 4722725 := bbase (se 4 (by rfl) ⟨442755, by rfl⟩ : syracuseStep 4722725 = 885511) (by norm_num)
theorem B3543077 : Blo 1865634 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B4198445 : Blo 1865634 4198445 := bbase (se 3 (by rfl) ⟨787208, by rfl⟩ : syracuseStep 4198445 = 1574417) (by norm_num)
theorem B4198517 : Blo 1865634 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B3149941 : Blo 1865634 3149941 := bbase (se 5 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 3149941 = 295307) (by norm_num)
theorem B2363509 : Blo 1865634 2363509 := bbase (se 5 (by rfl) ⟨110789, by rfl⟩ : syracuseStep 2363509 = 221579) (by norm_num)
theorem B3641477 : Blo 1865634 3641477 := bbase (se 4 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 3641477 = 682777) (by norm_num)
theorem B9449621 : Blo 1865634 9449621 := bbase (se 6 (by rfl) ⟨221475, by rfl⟩ : syracuseStep 9449621 = 442951) (by norm_num)
theorem B4198589 : Blo 1865634 4198589 := bbase (se 3 (by rfl) ⟨787235, by rfl⟩ : syracuseStep 4198589 = 1574471) (by norm_num)
theorem B3150029 : Blo 1865634 3150029 := bbase (se 3 (by rfl) ⟨590630, by rfl⟩ : syracuseStep 3150029 = 1181261) (by norm_num)
theorem B4485341 : Blo 1865634 4485341 := bbase (se 3 (by rfl) ⟨841001, by rfl⟩ : syracuseStep 4485341 = 1682003) (by norm_num)
theorem B4198661 : Blo 1865634 4198661 := bbase (se 4 (by rfl) ⟨393624, by rfl⟩ : syracuseStep 4198661 = 787249) (by norm_num)
theorem B2363681 : Blo 1865634 2363681 := bbase (se 2 (by rfl) ⟨886380, by rfl⟩ : syracuseStep 2363681 = 1772761) (by norm_num)
theorem B7975205 : Blo 1865634 7975205 := bbase (se 4 (by rfl) ⟨747675, by rfl⟩ : syracuseStep 7975205 = 1495351) (by norm_num)
theorem B7278917 : Blo 1865634 7278917 := bbase (se 4 (by rfl) ⟨682398, by rfl⟩ : syracuseStep 7278917 = 1364797) (by norm_num)
theorem B3543365 : Blo 1865634 3543365 := bbase (se 4 (by rfl) ⟨332190, by rfl⟩ : syracuseStep 3543365 = 664381) (by norm_num)
theorem B2658629 : Blo 1865634 2658629 := bbase (se 4 (by rfl) ⟨249246, by rfl⟩ : syracuseStep 2658629 = 498493) (by norm_num)
theorem B4198733 : Blo 1865634 4198733 := bbase (se 3 (by rfl) ⟨787262, by rfl⟩ : syracuseStep 4198733 = 1574525) (by norm_num)
theorem B3150157 : Blo 1865634 3150157 := bbase (se 3 (by rfl) ⟨590654, by rfl⟩ : syracuseStep 3150157 = 1181309) (by norm_num)
theorem B3985757 : Blo 1865634 3985757 := bbase (se 3 (by rfl) ⟨747329, by rfl⟩ : syracuseStep 3985757 = 1494659) (by norm_num)
theorem B4723069 : Blo 1865634 4723069 := bbase (se 3 (by rfl) ⟨885575, by rfl⟩ : syracuseStep 4723069 = 1771151) (by norm_num)
theorem B4198805 : Blo 1865634 4198805 := bbase (se 6 (by rfl) ⟨98409, by rfl⟩ : syracuseStep 4198805 = 196819) (by norm_num)
theorem B3150245 : Blo 1865634 3150245 := bbase (se 4 (by rfl) ⟨295335, by rfl⟩ : syracuseStep 3150245 = 590671) (by norm_num)
theorem B8868293 : Blo 1865634 8868293 := bbase (se 4 (by rfl) ⟨831402, by rfl⟩ : syracuseStep 8868293 = 1662805) (by norm_num)
theorem B4198877 : Blo 1865634 4198877 := bbase (se 3 (by rfl) ⟨787289, by rfl⟩ : syracuseStep 4198877 = 1574579) (by norm_num)
theorem B3543517 : Blo 1865634 3543517 := bbase (se 3 (by rfl) ⟨664409, by rfl⟩ : syracuseStep 3543517 = 1328819) (by norm_num)
theorem B4723181 : Blo 1865634 4723181 := bbase (se 3 (by rfl) ⟨885596, by rfl⟩ : syracuseStep 4723181 = 1771193) (by norm_num)
theorem B4198949 : Blo 1865634 4198949 := bbase (se 4 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 4198949 = 787303) (by norm_num)
theorem B3150373 : Blo 1865634 3150373 := bbase (se 4 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 3150373 = 590695) (by norm_num)
theorem B3986005 : Blo 1865634 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B4199021 : Blo 1865634 4199021 := bbase (se 3 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 4199021 = 1574633) (by norm_num)
theorem B3150461 : Blo 1865634 3150461 := bbase (se 3 (by rfl) ⟨590711, by rfl⟩ : syracuseStep 3150461 = 1181423) (by norm_num)
theorem B8966821 : Blo 1865634 8966821 := bbase (se 4 (by rfl) ⟨840639, by rfl⟩ : syracuseStep 8966821 = 1681279) (by norm_num)
theorem B4723373 : Blo 1865634 4723373 := bbase (se 3 (by rfl) ⟨885632, by rfl⟩ : syracuseStep 4723373 = 1771265) (by norm_num)
theorem B8966837 : Blo 1865634 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B4199093 : Blo 1865634 4199093 := bbase (se 5 (by rfl) ⟨196832, by rfl⟩ : syracuseStep 4199093 = 393665) (by norm_num)
theorem B4199165 : Blo 1865634 4199165 := bbase (se 3 (by rfl) ⟨787343, by rfl⟩ : syracuseStep 4199165 = 1574687) (by norm_num)
theorem B3150589 : Blo 1865634 3150589 := bbase (se 3 (by rfl) ⟨590735, by rfl⟩ : syracuseStep 3150589 = 1181471) (by norm_num)
theorem B3543821 : Blo 1865634 3543821 := bbase (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) (by norm_num)
theorem B2241325 : Blo 1865634 2241325 := bbase (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) (by norm_num)
theorem B2839349 : Blo 1865634 2839349 := bbase (se 5 (by rfl) ⟨133094, by rfl⟩ : syracuseStep 2839349 = 266189) (by norm_num)
theorem B4199237 : Blo 1865634 4199237 := bbase (se 4 (by rfl) ⟨393678, by rfl⟩ : syracuseStep 4199237 = 787357) (by norm_num)
theorem B3150677 : Blo 1865634 3150677 := bbase (se 9 (by rfl) ⟨9230, by rfl⟩ : syracuseStep 3150677 = 18461) (by norm_num)
theorem B2798453 : Blo 1865634 2798453 := bbase (se 5 (by rfl) ⟨131177, by rfl⟩ : syracuseStep 2798453 = 262355) (by norm_num)
theorem B5313397 : Blo 1865634 5313397 := bbase (se 5 (by rfl) ⟨249065, by rfl⟩ : syracuseStep 5313397 = 498131) (by norm_num)
theorem B2798477 : Blo 1865634 2798477 := bbase (se 3 (by rfl) ⟨524714, by rfl⟩ : syracuseStep 2798477 = 1049429) (by norm_num)
theorem B4199309 : Blo 1865634 4199309 := bbase (se 3 (by rfl) ⟨787370, by rfl⟩ : syracuseStep 4199309 = 1574741) (by norm_num)
theorem B2798501 : Blo 1865634 2798501 := bbase (se 4 (by rfl) ⟨262359, by rfl⟩ : syracuseStep 2798501 = 524719) (by norm_num)
theorem B2798525 : Blo 1865634 2798525 := bbase (se 3 (by rfl) ⟨524723, by rfl⟩ : syracuseStep 2798525 = 1049447) (by norm_num)
theorem B2798549 : Blo 1865634 2798549 := bbase (se 7 (by rfl) ⟨32795, by rfl⟩ : syracuseStep 2798549 = 65591) (by norm_num)
theorem B4199381 : Blo 1865634 4199381 := bbase (se 7 (by rfl) ⟨49211, by rfl⟩ : syracuseStep 4199381 = 98423) (by norm_num)
theorem B3150805 : Blo 1865634 3150805 := bbase (se 7 (by rfl) ⟨36923, by rfl⟩ : syracuseStep 3150805 = 73847) (by norm_num)
theorem B5977061 : Blo 1865634 5977061 := bbase (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) (by norm_num)
theorem B2798573 : Blo 1865634 2798573 := bbase (se 3 (by rfl) ⟨524732, by rfl⟩ : syracuseStep 2798573 = 1049465) (by norm_num)
theorem B2798597 : Blo 1865634 2798597 := bbase (se 4 (by rfl) ⟨262368, by rfl⟩ : syracuseStep 2798597 = 524737) (by norm_num)
theorem B4723717 : Blo 1865634 4723717 := bbase (se 4 (by rfl) ⟨442848, by rfl⟩ : syracuseStep 4723717 = 885697) (by norm_num)
theorem B2798621 : Blo 1865634 2798621 := bbase (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) (by norm_num)
theorem B4199453 : Blo 1865634 4199453 := bbase (se 3 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 4199453 = 1574795) (by norm_num)
theorem B3150893 : Blo 1865634 3150893 := bbase (se 3 (by rfl) ⟨590792, by rfl⟩ : syracuseStep 3150893 = 1181585) (by norm_num)
theorem B2798645 : Blo 1865634 2798645 := bbase (se 5 (by rfl) ⟨131186, by rfl⟩ : syracuseStep 2798645 = 262373) (by norm_num)
theorem B2798669 : Blo 1865634 2798669 := bbase (se 3 (by rfl) ⟨524750, by rfl⟩ : syracuseStep 2798669 = 1049501) (by norm_num)
theorem B3986509 : Blo 1865634 3986509 := bbase (se 3 (by rfl) ⟨747470, by rfl⟩ : syracuseStep 3986509 = 1494941) (by norm_num)
theorem B2798693 : Blo 1865634 2798693 := bbase (se 4 (by rfl) ⟨262377, by rfl⟩ : syracuseStep 2798693 = 524755) (by norm_num)
theorem B4199525 : Blo 1865634 4199525 := bbase (se 4 (by rfl) ⟨393705, by rfl⟩ : syracuseStep 4199525 = 787411) (by norm_num)
theorem B4723829 : Blo 1865634 4723829 := bbase (se 5 (by rfl) ⟨221429, by rfl⟩ : syracuseStep 4723829 = 442859) (by norm_num)
theorem B2798717 : Blo 1865634 2798717 := bbase (se 3 (by rfl) ⟨524759, by rfl⟩ : syracuseStep 2798717 = 1049519) (by norm_num)
theorem B2798741 : Blo 1865634 2798741 := bbase (se 6 (by rfl) ⟨65595, by rfl⟩ : syracuseStep 2798741 = 131191) (by norm_num)
theorem B2798765 : Blo 1865634 2798765 := bbase (se 3 (by rfl) ⟨524768, by rfl⟩ : syracuseStep 2798765 = 1049537) (by norm_num)
theorem B4199597 : Blo 1865634 4199597 := bbase (se 3 (by rfl) ⟨787424, by rfl⟩ : syracuseStep 4199597 = 1574849) (by norm_num)
theorem B3151021 : Blo 1865634 3151021 := bbase (se 3 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 3151021 = 1181633) (by norm_num)
theorem B2798789 : Blo 1865634 2798789 := bbase (se 4 (by rfl) ⟨262386, by rfl⟩ : syracuseStep 2798789 = 524773) (by norm_num)
theorem B2798813 : Blo 1865634 2798813 := bbase (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) (by norm_num)
theorem B2798837 : Blo 1865634 2798837 := bbase (se 5 (by rfl) ⟨131195, by rfl⟩ : syracuseStep 2798837 = 262391) (by norm_num)
theorem B4199669 : Blo 1865634 4199669 := bbase (se 5 (by rfl) ⟨196859, by rfl⟩ : syracuseStep 4199669 = 393719) (by norm_num)
theorem B3151109 : Blo 1865634 3151109 := bbase (se 4 (by rfl) ⟨295416, by rfl⟩ : syracuseStep 3151109 = 590833) (by norm_num)
theorem B2798861 : Blo 1865634 2798861 := bbase (se 3 (by rfl) ⟨524786, by rfl⟩ : syracuseStep 2798861 = 1049573) (by norm_num)
theorem B2798885 : Blo 1865634 2798885 := bbase (se 4 (by rfl) ⟨262395, by rfl⟩ : syracuseStep 2798885 = 524791) (by norm_num)
theorem B6296885 : Blo 1865634 6296885 := bbase (se 5 (by rfl) ⟨295166, by rfl⟩ : syracuseStep 6296885 = 590333) (by norm_num)
theorem B4724021 : Blo 1865634 4724021 := bbase (se 5 (by rfl) ⟨221438, by rfl⟩ : syracuseStep 4724021 = 442877) (by norm_num)
theorem B2798909 : Blo 1865634 2798909 := bbase (se 3 (by rfl) ⟨524795, by rfl⟩ : syracuseStep 2798909 = 1049591) (by norm_num)
theorem B4199741 : Blo 1865634 4199741 := bbase (se 3 (by rfl) ⟨787451, by rfl⟩ : syracuseStep 4199741 = 1574903) (by norm_num)
theorem B2798933 : Blo 1865634 2798933 := bbase (se 13 (by rfl) ⟨512, by rfl⟩ : syracuseStep 2798933 = 1025) (by norm_num)
theorem B2798957 : Blo 1865634 2798957 := bbase (se 3 (by rfl) ⟨524804, by rfl⟩ : syracuseStep 2798957 = 1049609) (by norm_num)
theorem B2798981 : Blo 1865634 2798981 := bbase (se 4 (by rfl) ⟨262404, by rfl⟩ : syracuseStep 2798981 = 524809) (by norm_num)
theorem B4199813 : Blo 1865634 4199813 := bbase (se 4 (by rfl) ⟨393732, by rfl⟩ : syracuseStep 4199813 = 787465) (by norm_num)
theorem B3151237 : Blo 1865634 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B2799005 : Blo 1865634 2799005 := bbase (se 3 (by rfl) ⟨524813, by rfl⟩ : syracuseStep 2799005 = 1049627) (by norm_num)
theorem B9450917 : Blo 1865634 9450917 := bbase (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) (by norm_num)
theorem B2799029 : Blo 1865634 2799029 := bbase (se 5 (by rfl) ⟨131204, by rfl⟩ : syracuseStep 2799029 = 262409) (by norm_num)
theorem B2799053 : Blo 1865634 2799053 := bbase (se 3 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 2799053 = 1049645) (by norm_num)
theorem B4199885 : Blo 1865634 4199885 := bbase (se 3 (by rfl) ⟨787478, by rfl⟩ : syracuseStep 4199885 = 1574957) (by norm_num)
theorem B3151325 : Blo 1865634 3151325 := bbase (se 3 (by rfl) ⟨590873, by rfl⟩ : syracuseStep 3151325 = 1181747) (by norm_num)
theorem B2799077 : Blo 1865634 2799077 := bbase (se 4 (by rfl) ⟨262413, by rfl⟩ : syracuseStep 2799077 = 524827) (by norm_num)
theorem B2799101 : Blo 1865634 2799101 := bbase (se 3 (by rfl) ⟨524831, by rfl⟩ : syracuseStep 2799101 = 1049663) (by norm_num)
theorem B3544573 : Blo 1865634 3544573 := bbase (se 3 (by rfl) ⟨664607, by rfl⟩ : syracuseStep 3544573 = 1329215) (by norm_num)
theorem B2799125 : Blo 1865634 2799125 := bbase (se 6 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 2799125 = 131209) (by norm_num)
theorem B4199957 : Blo 1865634 4199957 := bbase (se 6 (by rfl) ⟨98436, by rfl⟩ : syracuseStep 4199957 = 196873) (by norm_num)
theorem B3782189 : Blo 1865634 3782189 := bbase (se 3 (by rfl) ⟨709160, by rfl⟩ : syracuseStep 3782189 = 1418321) (by norm_num)
theorem B2799149 : Blo 1865634 2799149 := bbase (se 3 (by rfl) ⟨524840, by rfl⟩ : syracuseStep 2799149 = 1049681) (by norm_num)
theorem B2799173 : Blo 1865634 2799173 := bbase (se 4 (by rfl) ⟨262422, by rfl⟩ : syracuseStep 2799173 = 524845) (by norm_num)
theorem B2799197 : Blo 1865634 2799197 := bbase (se 3 (by rfl) ⟨524849, by rfl⟩ : syracuseStep 2799197 = 1049699) (by norm_num)
theorem B4200029 : Blo 1865634 4200029 := bbase (se 3 (by rfl) ⟨787505, by rfl⟩ : syracuseStep 4200029 = 1575011) (by norm_num)
theorem B3151453 : Blo 1865634 3151453 := bbase (se 3 (by rfl) ⟨590897, by rfl⟩ : syracuseStep 3151453 = 1181795) (by norm_num)
theorem B2799221 : Blo 1865634 2799221 := bbase (se 5 (by rfl) ⟨131213, by rfl⟩ : syracuseStep 2799221 = 262427) (by norm_num)
theorem B2799245 : Blo 1865634 2799245 := bbase (se 3 (by rfl) ⟨524858, by rfl⟩ : syracuseStep 2799245 = 1049717) (by norm_num)
theorem B4724365 : Blo 1865634 4724365 := bbase (se 3 (by rfl) ⟨885818, by rfl⟩ : syracuseStep 4724365 = 1771637) (by norm_num)
theorem B3544717 : Blo 1865634 3544717 := bbase (se 3 (by rfl) ⟨664634, by rfl⟩ : syracuseStep 3544717 = 1329269) (by norm_num)
theorem B2799269 : Blo 1865634 2799269 := bbase (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) (by norm_num)
theorem B4200101 : Blo 1865634 4200101 := bbase (se 4 (by rfl) ⟨393759, by rfl⟩ : syracuseStep 4200101 = 787519) (by norm_num)
theorem B3364525 : Blo 1865634 3364525 := bbase (se 3 (by rfl) ⟨630848, by rfl⟩ : syracuseStep 3364525 = 1261697) (by norm_num)
theorem B3151541 : Blo 1865634 3151541 := bbase (se 5 (by rfl) ⟨147728, by rfl⟩ : syracuseStep 3151541 = 295457) (by norm_num)
theorem B2799293 : Blo 1865634 2799293 := bbase (se 3 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 2799293 = 1049735) (by norm_num)
theorem B2799317 : Blo 1865634 2799317 := bbase (se 7 (by rfl) ⟨32804, by rfl⟩ : syracuseStep 2799317 = 65609) (by norm_num)
theorem B6297317 : Blo 1865634 6297317 := bbase (se 4 (by rfl) ⟨590373, by rfl⟩ : syracuseStep 6297317 = 1180747) (by norm_num)
theorem B2799341 : Blo 1865634 2799341 := bbase (se 3 (by rfl) ⟨524876, by rfl⟩ : syracuseStep 2799341 = 1049753) (by norm_num)
theorem B4200173 : Blo 1865634 4200173 := bbase (se 3 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 4200173 = 1575065) (by norm_num)
theorem B3364597 : Blo 1865634 3364597 := bbase (se 5 (by rfl) ⟨157715, by rfl⟩ : syracuseStep 3364597 = 315431) (by norm_num)
theorem B4724477 : Blo 1865634 4724477 := bbase (se 3 (by rfl) ⟨885839, by rfl⟩ : syracuseStep 4724477 = 1771679) (by norm_num)
theorem B2799365 : Blo 1865634 2799365 := bbase (se 4 (by rfl) ⟨262440, by rfl⟩ : syracuseStep 2799365 = 524881) (by norm_num)
theorem B2799389 : Blo 1865634 2799389 := bbase (se 3 (by rfl) ⟨524885, by rfl⟩ : syracuseStep 2799389 = 1049771) (by norm_num)
theorem B3192605 : Blo 1865634 3192605 := bbase (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) (by norm_num)
theorem B3544877 : Blo 1865634 3544877 := bbase (se 3 (by rfl) ⟨664664, by rfl⟩ : syracuseStep 3544877 = 1329329) (by norm_num)
theorem B5674805 : Blo 1865634 5674805 := bbase (se 5 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 5674805 = 532013) (by norm_num)
theorem B2799413 : Blo 1865634 2799413 := bbase (se 5 (by rfl) ⟨131222, by rfl⟩ : syracuseStep 2799413 = 262445) (by norm_num)
theorem B4200245 : Blo 1865634 4200245 := bbase (se 5 (by rfl) ⟨196886, by rfl⟩ : syracuseStep 4200245 = 393773) (by norm_num)
theorem B7083845 : Blo 1865634 7083845 := bbase (se 4 (by rfl) ⟨664110, by rfl⟩ : syracuseStep 7083845 = 1328221) (by norm_num)
theorem B2799437 : Blo 1865634 2799437 := bbase (se 3 (by rfl) ⟨524894, by rfl⟩ : syracuseStep 2799437 = 1049789) (by norm_num)
theorem B2799461 : Blo 1865634 2799461 := bbase (se 4 (by rfl) ⟨262449, by rfl⟩ : syracuseStep 2799461 = 524899) (by norm_num)
theorem B4790117 : Blo 1865634 4790117 := bbase (se 4 (by rfl) ⟨449073, by rfl⟩ : syracuseStep 4790117 = 898147) (by norm_num)
theorem B2799485 : Blo 1865634 2799485 := bbase (se 3 (by rfl) ⟨524903, by rfl⟩ : syracuseStep 2799485 = 1049807) (by norm_num)
theorem B4200317 : Blo 1865634 4200317 := bbase (se 3 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 4200317 = 1575119) (by norm_num)
theorem B2799509 : Blo 1865634 2799509 := bbase (se 6 (by rfl) ⟨65613, by rfl⟩ : syracuseStep 2799509 = 131227) (by norm_num)
theorem B2799533 : Blo 1865634 2799533 := bbase (se 3 (by rfl) ⟨524912, by rfl⟩ : syracuseStep 2799533 = 1049825) (by norm_num)
theorem B4724669 : Blo 1865634 4724669 := bbase (se 3 (by rfl) ⟨885875, by rfl⟩ : syracuseStep 4724669 = 1771751) (by norm_num)
theorem B3545021 : Blo 1865634 3545021 := bbase (se 3 (by rfl) ⟨664691, by rfl⟩ : syracuseStep 3545021 = 1329383) (by norm_num)
theorem B5314501 : Blo 1865634 5314501 := bbase (se 4 (by rfl) ⟨498234, by rfl⟩ : syracuseStep 5314501 = 996469) (by norm_num)
theorem B2799557 : Blo 1865634 2799557 := bbase (se 4 (by rfl) ⟨262458, by rfl⟩ : syracuseStep 2799557 = 524917) (by norm_num)
theorem B4200389 : Blo 1865634 4200389 := bbase (se 4 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 4200389 = 787573) (by norm_num)
theorem B3987397 : Blo 1865634 3987397 := bbase (se 4 (by rfl) ⟨373818, by rfl⟩ : syracuseStep 3987397 = 747637) (by norm_num)
theorem B2799581 : Blo 1865634 2799581 := bbase (se 3 (by rfl) ⟨524921, by rfl⟩ : syracuseStep 2799581 = 1049843) (by norm_num)
theorem B2799605 : Blo 1865634 2799605 := bbase (se 5 (by rfl) ⟨131231, by rfl⟩ : syracuseStep 2799605 = 262463) (by norm_num)
theorem B2799629 : Blo 1865634 2799629 := bbase (se 3 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 2799629 = 1049861) (by norm_num)
theorem B4200461 : Blo 1865634 4200461 := bbase (se 3 (by rfl) ⟨787586, by rfl⟩ : syracuseStep 4200461 = 1575173) (by norm_num)
theorem B10631189 : Blo 1865634 10631189 := bbase (se 6 (by rfl) ⟨249168, by rfl⟩ : syracuseStep 10631189 = 498337) (by norm_num)
theorem B7976981 : Blo 1865634 7976981 := bbase (se 6 (by rfl) ⟨186960, by rfl⟩ : syracuseStep 7976981 = 373921) (by norm_num)
theorem B2799653 : Blo 1865634 2799653 := bbase (se 4 (by rfl) ⟨262467, by rfl⟩ : syracuseStep 2799653 = 524935) (by norm_num)
theorem B2242613 : Blo 1865634 2242613 := bbase (se 5 (by rfl) ⟨105122, by rfl⟩ : syracuseStep 2242613 = 210245) (by norm_num)
theorem B2799677 : Blo 1865634 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B4790341 : Blo 1865634 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B2799701 : Blo 1865634 2799701 := bbase (se 8 (by rfl) ⟨16404, by rfl⟩ : syracuseStep 2799701 = 32809) (by norm_num)
theorem B4200533 : Blo 1865634 4200533 := bbase (se 8 (by rfl) ⟨24612, by rfl⟩ : syracuseStep 4200533 = 49225) (by norm_num)
theorem B2799725 : Blo 1865634 2799725 := bbase (se 3 (by rfl) ⟨524948, by rfl⟩ : syracuseStep 2799725 = 1049897) (by norm_num)
theorem B10090613 : Blo 1865634 10090613 := bbase (se 5 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 10090613 = 945995) (by norm_num)
theorem B3782789 : Blo 1865634 3782789 := bbase (se 4 (by rfl) ⟨354636, by rfl⟩ : syracuseStep 3782789 = 709273) (by norm_num)
theorem B2799749 : Blo 1865634 2799749 := bbase (se 4 (by rfl) ⟨262476, by rfl⟩ : syracuseStep 2799749 = 524953) (by norm_num)
theorem B6297749 : Blo 1865634 6297749 := bbase (se 6 (by rfl) ⟨147603, by rfl⟩ : syracuseStep 6297749 = 295207) (by norm_num)
theorem B2799773 : Blo 1865634 2799773 := bbase (se 3 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 2799773 = 1049915) (by norm_num)
theorem B4200605 : Blo 1865634 4200605 := bbase (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) (by norm_num)
theorem B2799797 : Blo 1865634 2799797 := bbase (se 5 (by rfl) ⟨131240, by rfl⟩ : syracuseStep 2799797 = 262481) (by norm_num)
theorem B2799821 : Blo 1865634 2799821 := bbase (se 3 (by rfl) ⟨524966, by rfl⟩ : syracuseStep 2799821 = 1049933) (by norm_num)
theorem B3545309 : Blo 1865634 3545309 := bbase (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) (by norm_num)
theorem B2799845 : Blo 1865634 2799845 := bbase (se 4 (by rfl) ⟨262485, by rfl⟩ : syracuseStep 2799845 = 524971) (by norm_num)
theorem B4200677 : Blo 1865634 4200677 := bbase (se 4 (by rfl) ⟨393813, by rfl⟩ : syracuseStep 4200677 = 787627) (by norm_num)
theorem B2799869 : Blo 1865634 2799869 := bbase (se 3 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 2799869 = 1049951) (by norm_num)
theorem B4258045 : Blo 1865634 4258045 := bbase (se 3 (by rfl) ⟨798383, by rfl⟩ : syracuseStep 4258045 = 1596767) (by norm_num)
theorem B2799893 : Blo 1865634 2799893 := bbase (se 6 (by rfl) ⟨65622, by rfl⟩ : syracuseStep 2799893 = 131245) (by norm_num)
theorem B4725013 : Blo 1865634 4725013 := bbase (se 6 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 4725013 = 221485) (by norm_num)
theorem B2799917 : Blo 1865634 2799917 := bbase (se 3 (by rfl) ⟨524984, by rfl⟩ : syracuseStep 2799917 = 1049969) (by norm_num)
theorem B4200749 : Blo 1865634 4200749 := bbase (se 3 (by rfl) ⟨787640, by rfl⟩ : syracuseStep 4200749 = 1575281) (by norm_num)
theorem B2799941 : Blo 1865634 2799941 := bbase (se 4 (by rfl) ⟨262494, by rfl⟩ : syracuseStep 2799941 = 524989) (by norm_num)
theorem B90863957 : Blo 1865634 90863957 := bbase (se 10 (by rfl) ⟨133101, by rfl⟩ : syracuseStep 90863957 = 266203) (by norm_num)
theorem B2799965 : Blo 1865634 2799965 := bbase (se 3 (by rfl) ⟨524993, by rfl⟩ : syracuseStep 2799965 = 1049987) (by norm_num)
theorem B2799989 : Blo 1865634 2799989 := bbase (se 5 (by rfl) ⟨131249, by rfl⟩ : syracuseStep 2799989 = 262499) (by norm_num)
theorem B4200821 : Blo 1865634 4200821 := bbase (se 5 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 4200821 = 393827) (by norm_num)
theorem B3545461 : Blo 1865634 3545461 := bbase (se 5 (by rfl) ⟨166193, by rfl⟩ : syracuseStep 3545461 = 332387) (by norm_num)
theorem B4725125 : Blo 1865634 4725125 := bbase (se 4 (by rfl) ⟨442980, by rfl⟩ : syracuseStep 4725125 = 885961) (by norm_num)
theorem B2800013 : Blo 1865634 2800013 := bbase (se 3 (by rfl) ⟨525002, by rfl⟩ : syracuseStep 2800013 = 1050005) (by norm_num)
theorem B2800037 : Blo 1865634 2800037 := bbase (se 4 (by rfl) ⟨262503, by rfl⟩ : syracuseStep 2800037 = 525007) (by norm_num)
theorem B3987893 : Blo 1865634 3987893 := bbase (se 5 (by rfl) ⟨186932, by rfl⟩ : syracuseStep 3987893 = 373865) (by norm_num)
theorem B2800061 : Blo 1865634 2800061 := bbase (se 3 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 2800061 = 1050023) (by norm_num)
theorem B4200893 : Blo 1865634 4200893 := bbase (se 3 (by rfl) ⟨787667, by rfl⟩ : syracuseStep 4200893 = 1575335) (by norm_num)
theorem B2988485 : Blo 1865634 2988485 := bbase (se 4 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 2988485 = 560341) (by norm_num)
theorem B2800085 : Blo 1865634 2800085 := bbase (se 7 (by rfl) ⟨32813, by rfl⟩ : syracuseStep 2800085 = 65627) (by norm_num)
theorem B2800109 : Blo 1865634 2800109 := bbase (se 3 (by rfl) ⟨525020, by rfl⟩ : syracuseStep 2800109 = 1050041) (by norm_num)
theorem B2800133 : Blo 1865634 2800133 := bbase (se 4 (by rfl) ⟨262512, by rfl⟩ : syracuseStep 2800133 = 525025) (by norm_num)
theorem B4200965 : Blo 1865634 4200965 := bbase (se 4 (by rfl) ⟨393840, by rfl⟩ : syracuseStep 4200965 = 787681) (by norm_num)
theorem B2521621 : Blo 1865634 2521621 := bbase (se 6 (by rfl) ⟨59100, by rfl⟩ : syracuseStep 2521621 = 118201) (by norm_num)
theorem B2800157 : Blo 1865634 2800157 := bbase (se 3 (by rfl) ⟨525029, by rfl⟩ : syracuseStep 2800157 = 1050059) (by norm_num)
theorem B2988581 : Blo 1865634 2988581 := bbase (se 4 (by rfl) ⟨280179, by rfl⟩ : syracuseStep 2988581 = 560359) (by norm_num)
theorem B2800181 : Blo 1865634 2800181 := bbase (se 5 (by rfl) ⟨131258, by rfl⟩ : syracuseStep 2800181 = 262517) (by norm_num)
theorem B2988613 : Blo 1865634 2988613 := bbase (se 4 (by rfl) ⟨280182, by rfl⟩ : syracuseStep 2988613 = 560365) (by norm_num)
theorem B6298181 : Blo 1865634 6298181 := bbase (se 4 (by rfl) ⟨590454, by rfl⟩ : syracuseStep 6298181 = 1180909) (by norm_num)
theorem B4725317 : Blo 1865634 4725317 := bbase (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) (by norm_num)
theorem B2128457 : Blo 1865634 2128457 := bbase (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) (by norm_num)
theorem B2800205 : Blo 1865634 2800205 := bbase (se 3 (by rfl) ⟨525038, by rfl⟩ : syracuseStep 2800205 = 1050077) (by norm_num)
theorem B4201037 : Blo 1865634 4201037 := bbase (se 3 (by rfl) ⟨787694, by rfl⟩ : syracuseStep 4201037 = 1575389) (by norm_num)
theorem B2800229 : Blo 1865634 2800229 := bbase (se 4 (by rfl) ⟨262521, by rfl⟩ : syracuseStep 2800229 = 525043) (by norm_num)
theorem B2800253 : Blo 1865634 2800253 := bbase (se 3 (by rfl) ⟨525047, by rfl⟩ : syracuseStep 2800253 = 1050095) (by norm_num)
theorem B2243209 : Blo 1865634 2243209 := bbase (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) (by norm_num)
theorem B2800277 : Blo 1865634 2800277 := bbase (se 6 (by rfl) ⟨65631, by rfl⟩ : syracuseStep 2800277 = 131263) (by norm_num)
theorem B4201109 : Blo 1865634 4201109 := bbase (se 6 (by rfl) ⟨98463, by rfl⟩ : syracuseStep 4201109 = 196927) (by norm_num)
theorem B2800301 : Blo 1865634 2800301 := bbase (se 3 (by rfl) ⟨525056, by rfl⟩ : syracuseStep 2800301 = 1050113) (by norm_num)
theorem B9452213 : Blo 1865634 9452213 := bbase (se 5 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 9452213 = 886145) (by norm_num)
theorem B2800325 : Blo 1865634 2800325 := bbase (se 4 (by rfl) ⟨262530, by rfl⟩ : syracuseStep 2800325 = 525061) (by norm_num)
theorem B15350485 : Blo 1865634 15350485 := bbase (se 7 (by rfl) ⟨179888, by rfl⟩ : syracuseStep 15350485 = 359777) (by norm_num)
theorem B2800349 : Blo 1865634 2800349 := bbase (se 3 (by rfl) ⟨525065, by rfl⟩ : syracuseStep 2800349 = 1050131) (by norm_num)
theorem B4201181 : Blo 1865634 4201181 := bbase (se 3 (by rfl) ⟨787721, by rfl⟩ : syracuseStep 4201181 = 1575443) (by norm_num)
theorem B2243305 : Blo 1865634 2243305 := bbase (se 2 (by rfl) ⟨841239, by rfl⟩ : syracuseStep 2243305 = 1682479) (by norm_num)
theorem B2800373 : Blo 1865634 2800373 := bbase (se 5 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 2800373 = 262535) (by norm_num)
theorem B2800397 : Blo 1865634 2800397 := bbase (se 3 (by rfl) ⟨525074, by rfl⟩ : syracuseStep 2800397 = 1050149) (by norm_num)
theorem B2800421 : Blo 1865634 2800421 := bbase (se 4 (by rfl) ⟨262539, by rfl⟩ : syracuseStep 2800421 = 525079) (by norm_num)
theorem B4201253 : Blo 1865634 4201253 := bbase (se 4 (by rfl) ⟨393867, by rfl⟩ : syracuseStep 4201253 = 787735) (by norm_num)
theorem B2800445 : Blo 1865634 2800445 := bbase (se 3 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 2800445 = 1050167) (by norm_num)
theorem B2800469 : Blo 1865634 2800469 := bbase (se 9 (by rfl) ⟨8204, by rfl⟩ : syracuseStep 2800469 = 16409) (by norm_num)
theorem B14375765 : Blo 1865634 14375765 := bbase (se 9 (by rfl) ⟨42116, by rfl⟩ : syracuseStep 14375765 = 84233) (by norm_num)
theorem B2800493 : Blo 1865634 2800493 := bbase (se 3 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 2800493 = 1050185) (by norm_num)
theorem B4201325 : Blo 1865634 4201325 := bbase (se 3 (by rfl) ⟨787748, by rfl⟩ : syracuseStep 4201325 = 1575497) (by norm_num)
theorem B15129461 : Blo 1865634 15129461 := bbase (se 5 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 15129461 = 1418387) (by norm_num)
theorem B2800517 : Blo 1865634 2800517 := bbase (se 4 (by rfl) ⟨262548, by rfl⟩ : syracuseStep 2800517 = 525097) (by norm_num)
theorem B4725661 : Blo 1865634 4725661 := bbase (se 3 (by rfl) ⟨886061, by rfl⟩ : syracuseStep 4725661 = 1772123) (by norm_num)
theorem B2800541 : Blo 1865634 2800541 := bbase (se 3 (by rfl) ⟨525101, by rfl⟩ : syracuseStep 2800541 = 1050203) (by norm_num)
theorem B2522021 : Blo 1865634 2522021 := bbase (se 4 (by rfl) ⟨236439, by rfl⟩ : syracuseStep 2522021 = 472879) (by norm_num)
theorem B2800565 : Blo 1865634 2800565 := bbase (se 5 (by rfl) ⟨131276, by rfl⟩ : syracuseStep 2800565 = 262553) (by norm_num)
theorem B4201397 : Blo 1865634 4201397 := bbase (se 5 (by rfl) ⟨196940, by rfl⟩ : syracuseStep 4201397 = 393881) (by norm_num)
theorem B2800589 : Blo 1865634 2800589 := bbase (se 3 (by rfl) ⟨525110, by rfl⟩ : syracuseStep 2800589 = 1050221) (by norm_num)
theorem B1891289 : Blo 1865634 1891289 := bbase (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) (by norm_num)
theorem B1891297 : Blo 1865634 1891297 := bbase (se 2 (by rfl) ⟨709236, by rfl⟩ : syracuseStep 1891297 = 1418473) (by norm_num)
theorem B7085029 : Blo 1865634 7085029 := bbase (se 4 (by rfl) ⟨664221, by rfl⟩ : syracuseStep 7085029 = 1328443) (by norm_num)
theorem B2800613 : Blo 1865634 2800613 := bbase (se 4 (by rfl) ⟨262557, by rfl⟩ : syracuseStep 2800613 = 525115) (by norm_num)
theorem B17488885 : Blo 1865634 17488885 := bbase (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) (by norm_num)
theorem B6298613 : Blo 1865634 6298613 := bbase (se 5 (by rfl) ⟨295247, by rfl⟩ : syracuseStep 6298613 = 590495) (by norm_num)
theorem B2800637 : Blo 1865634 2800637 := bbase (se 3 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 2800637 = 1050239) (by norm_num)
theorem B4201469 : Blo 1865634 4201469 := bbase (se 3 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 4201469 = 1575551) (by norm_num)
theorem B8969221 : Blo 1865634 8969221 := bbase (se 4 (by rfl) ⟨840864, by rfl⟩ : syracuseStep 8969221 = 1681729) (by norm_num)
theorem B4725773 : Blo 1865634 4725773 := bbase (se 3 (by rfl) ⟨886082, by rfl⟩ : syracuseStep 4725773 = 1772165) (by norm_num)
theorem B2800661 : Blo 1865634 2800661 := bbase (se 6 (by rfl) ⟨65640, by rfl⟩ : syracuseStep 2800661 = 131281) (by norm_num)
theorem B2800685 : Blo 1865634 2800685 := bbase (se 3 (by rfl) ⟨525128, by rfl⟩ : syracuseStep 2800685 = 1050257) (by norm_num)
theorem B2800709 : Blo 1865634 2800709 := bbase (se 4 (by rfl) ⟨262566, by rfl⟩ : syracuseStep 2800709 = 525133) (by norm_num)
theorem B4201541 : Blo 1865634 4201541 := bbase (se 4 (by rfl) ⟨393894, by rfl⟩ : syracuseStep 4201541 = 787789) (by norm_num)
theorem B2800733 : Blo 1865634 2800733 := bbase (se 3 (by rfl) ⟨525137, by rfl⟩ : syracuseStep 2800733 = 1050275) (by norm_num)
theorem B19414133 : Blo 1865634 19414133 := bbase (se 5 (by rfl) ⟨910037, by rfl⟩ : syracuseStep 19414133 = 1820075) (by norm_num)
theorem B2800757 : Blo 1865634 2800757 := bbase (se 5 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 2800757 = 262571) (by norm_num)
theorem B2800781 : Blo 1865634 2800781 := bbase (se 3 (by rfl) ⟨525146, by rfl⟩ : syracuseStep 2800781 = 1050293) (by norm_num)
theorem B4201613 : Blo 1865634 4201613 := bbase (se 3 (by rfl) ⟨787802, by rfl⟩ : syracuseStep 4201613 = 1575605) (by norm_num)
theorem B2800805 : Blo 1865634 2800805 := bbase (se 4 (by rfl) ⟨262575, by rfl⟩ : syracuseStep 2800805 = 525151) (by norm_num)
theorem B2800829 : Blo 1865634 2800829 := bbase (se 3 (by rfl) ⟨525155, by rfl⟩ : syracuseStep 2800829 = 1050311) (by norm_num)
theorem B4725965 : Blo 1865634 4725965 := bbase (se 3 (by rfl) ⟨886118, by rfl⟩ : syracuseStep 4725965 = 1772237) (by norm_num)
theorem B2800853 : Blo 1865634 2800853 := bbase (se 7 (by rfl) ⟨32822, by rfl⟩ : syracuseStep 2800853 = 65645) (by norm_num)
theorem B4201685 : Blo 1865634 4201685 := bbase (se 7 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 4201685 = 98477) (by norm_num)
theorem B3783917 : Blo 1865634 3783917 := bbase (se 3 (by rfl) ⟨709484, by rfl⟩ : syracuseStep 3783917 = 1418969) (by norm_num)
theorem B2800877 : Blo 1865634 2800877 := bbase (se 3 (by rfl) ⟨525164, by rfl⟩ : syracuseStep 2800877 = 1050329) (by norm_num)
theorem B2800901 : Blo 1865634 2800901 := bbase (se 4 (by rfl) ⟨262584, by rfl⟩ : syracuseStep 2800901 = 525169) (by norm_num)
theorem B7085333 : Blo 1865634 7085333 := bbase (se 6 (by rfl) ⟨166062, by rfl⟩ : syracuseStep 7085333 = 332125) (by norm_num)
theorem B2800925 : Blo 1865634 2800925 := bbase (se 3 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 2800925 = 1050347) (by norm_num)
theorem B4201757 : Blo 1865634 4201757 := bbase (se 3 (by rfl) ⟨787829, by rfl⟩ : syracuseStep 4201757 = 1575659) (by norm_num)
theorem B3988781 : Blo 1865634 3988781 := bbase (se 3 (by rfl) ⟨747896, by rfl⟩ : syracuseStep 3988781 = 1495793) (by norm_num)
theorem B3783989 : Blo 1865634 3783989 := bbase (se 5 (by rfl) ⟨177374, by rfl⟩ : syracuseStep 3783989 = 354749) (by norm_num)
theorem B2800949 : Blo 1865634 2800949 := bbase (se 5 (by rfl) ⟨131294, by rfl⟩ : syracuseStep 2800949 = 262589) (by norm_num)
theorem B4259141 : Blo 1865634 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B2800973 : Blo 1865634 2800973 := bbase (se 3 (by rfl) ⟨525182, by rfl⟩ : syracuseStep 2800973 = 1050365) (by norm_num)
theorem B2800997 : Blo 1865634 2800997 := bbase (se 4 (by rfl) ⟨262593, by rfl⟩ : syracuseStep 2800997 = 525187) (by norm_num)
theorem B4201829 : Blo 1865634 4201829 := bbase (se 4 (by rfl) ⟨393921, by rfl⟩ : syracuseStep 4201829 = 787843) (by norm_num)
theorem B2801021 : Blo 1865634 2801021 := bbase (se 3 (by rfl) ⟨525191, by rfl⟩ : syracuseStep 2801021 = 1050383) (by norm_num)
theorem B2801045 : Blo 1865634 2801045 := bbase (se 6 (by rfl) ⟨65649, by rfl⟩ : syracuseStep 2801045 = 131299) (by norm_num)
theorem B6299045 : Blo 1865634 6299045 := bbase (se 4 (by rfl) ⟨590535, by rfl⟩ : syracuseStep 6299045 = 1181071) (by norm_num)
theorem B5316005 : Blo 1865634 5316005 := bbase (se 4 (by rfl) ⟨498375, by rfl⟩ : syracuseStep 5316005 = 996751) (by norm_num)
theorem B2801069 : Blo 1865634 2801069 := bbase (se 3 (by rfl) ⟨525200, by rfl⟩ : syracuseStep 2801069 = 1050401) (by norm_num)
theorem B4201901 : Blo 1865634 4201901 := bbase (se 3 (by rfl) ⟨787856, by rfl⟩ : syracuseStep 4201901 = 1575713) (by norm_num)
theorem B2801093 : Blo 1865634 2801093 := bbase (se 4 (by rfl) ⟨262602, by rfl⟩ : syracuseStep 2801093 = 525205) (by norm_num)
theorem B2801117 : Blo 1865634 2801117 := bbase (se 3 (by rfl) ⟨525209, by rfl⟩ : syracuseStep 2801117 = 1050419) (by norm_num)
theorem B2801141 : Blo 1865634 2801141 := bbase (se 5 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 2801141 = 262607) (by norm_num)
theorem B4201973 : Blo 1865634 4201973 := bbase (se 5 (by rfl) ⟨196967, by rfl⟩ : syracuseStep 4201973 = 393935) (by norm_num)
theorem B2801165 : Blo 1865634 2801165 := bbase (se 3 (by rfl) ⟨525218, by rfl⟩ : syracuseStep 2801165 = 1050437) (by norm_num)
theorem B1891873 : Blo 1865634 1891873 := bbase (se 2 (by rfl) ⟨709452, by rfl⟩ : syracuseStep 1891873 = 1418905) (by norm_num)
theorem B4726309 : Blo 1865634 4726309 := bbase (se 4 (by rfl) ⟨443091, by rfl⟩ : syracuseStep 4726309 = 886183) (by norm_num)
theorem B2801189 : Blo 1865634 2801189 := bbase (se 4 (by rfl) ⟨262611, by rfl⟩ : syracuseStep 2801189 = 525223) (by norm_num)
theorem B2801213 : Blo 1865634 2801213 := bbase (se 3 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 2801213 = 1050455) (by norm_num)
theorem B4202045 : Blo 1865634 4202045 := bbase (se 3 (by rfl) ⟨787883, by rfl⟩ : syracuseStep 4202045 = 1575767) (by norm_num)
theorem B2801237 : Blo 1865634 2801237 := bbase (se 8 (by rfl) ⟨16413, by rfl⟩ : syracuseStep 2801237 = 32827) (by norm_num)
theorem B2801261 : Blo 1865634 2801261 := bbase (se 3 (by rfl) ⟨525236, by rfl⟩ : syracuseStep 2801261 = 1050473) (by norm_num)
theorem B2801285 : Blo 1865634 2801285 := bbase (se 4 (by rfl) ⟨262620, by rfl⟩ : syracuseStep 2801285 = 525241) (by norm_num)
theorem B4202117 : Blo 1865634 4202117 := bbase (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) (by norm_num)
theorem B4726421 : Blo 1865634 4726421 := bbase (se 6 (by rfl) ⟨110775, by rfl⟩ : syracuseStep 4726421 = 221551) (by norm_num)
theorem B2801309 : Blo 1865634 2801309 := bbase (se 3 (by rfl) ⟨525245, by rfl⟩ : syracuseStep 2801309 = 1050491) (by norm_num)
theorem B14180021 : Blo 1865634 14180021 := bbase (se 5 (by rfl) ⟨664688, by rfl⟩ : syracuseStep 14180021 = 1329377) (by norm_num)
theorem B2801333 : Blo 1865634 2801333 := bbase (se 5 (by rfl) ⟨131312, by rfl⟩ : syracuseStep 2801333 = 262625) (by norm_num)
theorem B2801357 : Blo 1865634 2801357 := bbase (se 3 (by rfl) ⟨525254, by rfl⟩ : syracuseStep 2801357 = 1050509) (by norm_num)
theorem B2801381 : Blo 1865634 2801381 := bbase (se 4 (by rfl) ⟨262629, by rfl⟩ : syracuseStep 2801381 = 525259) (by norm_num)
theorem B2801405 : Blo 1865634 2801405 := bbase (se 3 (by rfl) ⟨525263, by rfl⟩ : syracuseStep 2801405 = 1050527) (by norm_num)
theorem B2801429 : Blo 1865634 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B6299477 : Blo 1865634 6299477 := bbase (se 9 (by rfl) ⟨18455, by rfl⟩ : syracuseStep 6299477 = 36911) (by norm_num)
theorem B4726613 : Blo 1865634 4726613 := bbase (se 9 (by rfl) ⟨13847, by rfl⟩ : syracuseStep 4726613 = 27695) (by norm_num)
theorem B15138677 : Blo 1865634 15138677 := bbase (se 5 (by rfl) ⟨709625, by rfl⟩ : syracuseStep 15138677 = 1419251) (by norm_num)
theorem B8085365 : Blo 1865634 8085365 := bbase (se 5 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 8085365 = 758003) (by norm_num)
theorem B3784573 : Blo 1865634 3784573 := bbase (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) (by norm_num)
theorem B4546453 : Blo 1865634 4546453 := bbase (se 6 (by rfl) ⟨106557, by rfl⟩ : syracuseStep 4546453 = 213115) (by norm_num)
theorem B9453509 : Blo 1865634 9453509 := bbase (se 4 (by rfl) ⟨886266, by rfl⟩ : syracuseStep 9453509 = 1772533) (by norm_num)
theorem B6299693 : Blo 1865634 6299693 := bstep (se 3 (by rfl) ⟨1181192, by rfl⟩ : syracuseStep 6299693 = 2362385) B2362385
theorem B6299747 : Blo 1865634 6299747 := bstep (se 1 (by rfl) ⟨4724810, by rfl⟩ : syracuseStep 6299747 = 9449621) B9449621
theorem B5980301 : Blo 1865634 5980301 := bstep (se 3 (by rfl) ⟨1121306, by rfl⟩ : syracuseStep 5980301 = 2242613) B2242613
theorem B5316803 : Blo 1865634 5316803 := bstep (se 1 (by rfl) ⟨3987602, by rfl⟩ : syracuseStep 5316803 = 7975205) B7975205
theorem B5677393 : Blo 1865634 5677393 := bstep (se 2 (by rfl) ⟨2129022, by rfl⟩ : syracuseStep 5677393 = 4258045) B4258045
theorem B3785059 : Blo 1865634 3785059 := bstep (se 1 (by rfl) ⟨2838794, by rfl⟩ : syracuseStep 3785059 = 5677589) B5677589
theorem B6300017 : Blo 1865634 6300017 := bstep (se 2 (by rfl) ⟨2362506, by rfl⟩ : syracuseStep 6300017 = 4725013) B4725013
theorem B6062467 : Blo 1865634 6062467 := bstep (se 1 (by rfl) ⟨4546850, by rfl⟩ : syracuseStep 6062467 = 9093701) B9093701
theorem B5046691 : Blo 1865634 5046691 := bstep (se 1 (by rfl) ⟨3785018, by rfl⟩ : syracuseStep 5046691 = 7570037) B7570037
theorem B4727281 : Blo 1865634 4727281 := bstep (se 2 (by rfl) ⟨1772730, by rfl⟩ : syracuseStep 4727281 = 3545461) B3545461
theorem B2556419 : Blo 1865634 2556419 := bstep (se 1 (by rfl) ⟨1917314, by rfl⟩ : syracuseStep 2556419 = 3834629) B3834629
theorem B1892899 : Blo 1865634 1892899 := bstep (se 1 (by rfl) ⟨1419674, by rfl⟩ : syracuseStep 1892899 = 2839349) B2839349
theorem B11960909 : Blo 1865634 11960909 := bstep (se 3 (by rfl) ⟨2242670, by rfl⟩ : syracuseStep 11960909 = 4485341) B4485341
theorem B9454157 : Blo 1865634 9454157 := bstep (se 3 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 9454157 = 3545309) B3545309
theorem B6816419 : Blo 1865634 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B5046961 : Blo 1865634 5046961 := bstep (se 2 (by rfl) ⟨1892610, by rfl⟩ : syracuseStep 5046961 = 3785221) B3785221
theorem B2990945 : Blo 1865634 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B6300557 : Blo 1865634 6300557 := bstep (se 3 (by rfl) ⟨1181354, by rfl⟩ : syracuseStep 6300557 = 2362709) B2362709
theorem B6300611 : Blo 1865634 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B5317645 : Blo 1865634 5317645 := bstep (se 3 (by rfl) ⟨997058, by rfl⟩ : syracuseStep 5317645 = 1994117) B1994117
theorem B57500725 : Blo 1865634 57500725 := bstep (se 5 (by rfl) ⟨2695346, by rfl⟩ : syracuseStep 57500725 = 5390693) B5390693
theorem B5317805 : Blo 1865634 5317805 := bstep (se 3 (by rfl) ⟨997088, by rfl⟩ : syracuseStep 5317805 = 1994177) B1994177
theorem B6300881 : Blo 1865634 6300881 := bstep (se 2 (by rfl) ⟨2362830, by rfl⟩ : syracuseStep 6300881 = 4725661) B4725661
theorem B9446705 : Blo 1865634 9446705 := bstep (se 2 (by rfl) ⟨3542514, by rfl⟩ : syracuseStep 9446705 = 7085029) B7085029
theorem B7087459 : Blo 1865634 7087459 := bstep (se 1 (by rfl) ⟨5315594, by rfl⟩ : syracuseStep 7087459 = 10631189) B10631189
theorem B5317987 : Blo 1865634 5317987 := bstep (se 1 (by rfl) ⟨3988490, by rfl⟩ : syracuseStep 5317987 = 7976981) B7976981
theorem B3237409 : Blo 1865634 3237409 := bstep (se 2 (by rfl) ⟨1214028, by rfl⟩ : syracuseStep 3237409 = 2428057) B2428057
theorem B1992323 : Blo 1865634 1992323 := bstep (se 1 (by rfl) ⟨1494242, by rfl⟩ : syracuseStep 1992323 = 2988485) B2988485
theorem B2098867 : Blo 1865634 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B6301421 : Blo 1865634 6301421 := bstep (se 3 (by rfl) ⟨1181516, by rfl⟩ : syracuseStep 6301421 = 2363033) B2363033
theorem B17942285 : Blo 1865634 17942285 := bstep (se 3 (by rfl) ⟨3364178, by rfl⟩ : syracuseStep 17942285 = 6728357) B6728357
theorem B6301475 : Blo 1865634 6301475 := bstep (se 1 (by rfl) ⟨4726106, by rfl⟩ : syracuseStep 6301475 = 9452213) B9452213
theorem B2099011 : Blo 1865634 2099011 := bstep (se 1 (by rfl) ⟨1574258, by rfl⟩ : syracuseStep 2099011 = 3148517) B3148517
theorem B51079025 : Blo 1865634 51079025 := bstep (se 2 (by rfl) ⟨19154634, by rfl⟩ : syracuseStep 51079025 = 38309269) B38309269
theorem B5982083 : Blo 1865634 5982083 := bstep (se 1 (by rfl) ⟨4486562, by rfl⟩ : syracuseStep 5982083 = 8973125) B8973125
theorem B2361251 : Blo 1865634 2361251 := bstep (se 1 (by rfl) ⟨1770938, by rfl⟩ : syracuseStep 2361251 = 3541877) B3541877
theorem B2099155 : Blo 1865634 2099155 := bstep (se 1 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 2099155 = 3148733) B3148733
theorem B6301745 : Blo 1865634 6301745 := bstep (se 2 (by rfl) ⟨2363154, by rfl⟩ : syracuseStep 6301745 = 4726309) B4726309
theorem B2099299 : Blo 1865634 2099299 := bstep (se 1 (by rfl) ⟨1574474, by rfl⟩ : syracuseStep 2099299 = 3148949) B3148949
theorem B2099443 : Blo 1865634 2099443 := bstep (se 1 (by rfl) ⟨1574582, by rfl⟩ : syracuseStep 2099443 = 3149165) B3149165
theorem B12773645 : Blo 1865634 12773645 := bstep (se 3 (by rfl) ⟨2395058, by rfl⟩ : syracuseStep 12773645 = 4790117) B4790117
theorem B6064433 : Blo 1865634 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B2656579 : Blo 1865634 2656579 := bstep (se 1 (by rfl) ⟨1992434, by rfl⟩ : syracuseStep 2656579 = 3984869) B3984869
theorem B10226033 : Blo 1865634 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B2099587 : Blo 1865634 2099587 := bstep (se 1 (by rfl) ⟨1574690, by rfl⟩ : syracuseStep 2099587 = 3149381) B3149381
theorem B14363021 : Blo 1865634 14363021 := bstep (se 3 (by rfl) ⟨2693066, by rfl⟩ : syracuseStep 14363021 = 5386133) B5386133
theorem B2099731 : Blo 1865634 2099731 := bstep (se 1 (by rfl) ⟨1574798, by rfl⟩ : syracuseStep 2099731 = 3149597) B3149597
theorem B3148321 : Blo 1865634 3148321 := bstep (se 2 (by rfl) ⟨1180620, by rfl⟩ : syracuseStep 3148321 = 2361241) B2361241
theorem B3148355 : Blo 1865634 3148355 := bstep (se 1 (by rfl) ⟨2361266, by rfl⟩ : syracuseStep 3148355 = 4722533) B4722533
theorem B6302285 : Blo 1865634 6302285 := bstep (se 3 (by rfl) ⟨1181678, by rfl⟩ : syracuseStep 6302285 = 2363357) B2363357
theorem B2361955 : Blo 1865634 2361955 := bstep (se 1 (by rfl) ⟨1771466, by rfl⟩ : syracuseStep 2361955 = 3542933) B3542933
theorem B6302339 : Blo 1865634 6302339 := bstep (se 1 (by rfl) ⟨4726754, by rfl⟩ : syracuseStep 6302339 = 9453509) B9453509
theorem B2099875 : Blo 1865634 2099875 := bstep (se 1 (by rfl) ⟨1574906, by rfl⟩ : syracuseStep 2099875 = 3149813) B3149813
theorem B3148483 : Blo 1865634 3148483 := bstep (se 1 (by rfl) ⟨2361362, by rfl⟩ : syracuseStep 3148483 = 4722725) B4722725
theorem B2362051 : Blo 1865634 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B9448163 : Blo 1865634 9448163 := bstep (se 1 (by rfl) ⟨7086122, by rfl⟩ : syracuseStep 9448163 = 14172245) B14172245
theorem B2100019 : Blo 1865634 2100019 := bstep (se 1 (by rfl) ⟨1575014, by rfl⟩ : syracuseStep 2100019 = 3150029) B3150029
theorem B3148625 : Blo 1865634 3148625 := bstep (se 2 (by rfl) ⟨1180734, by rfl⟩ : syracuseStep 3148625 = 2361469) B2361469
theorem B2657137 : Blo 1865634 2657137 := bstep (se 2 (by rfl) ⟨996426, by rfl⟩ : syracuseStep 2657137 = 1992853) B1992853
theorem B6302609 : Blo 1865634 6302609 := bstep (se 2 (by rfl) ⟨2363478, by rfl⟩ : syracuseStep 6302609 = 4726957) B4726957
theorem B2657171 : Blo 1865634 2657171 := bstep (se 1 (by rfl) ⟨1992878, by rfl⟩ : syracuseStep 2657171 = 3985757) B3985757
theorem B2100163 : Blo 1865634 2100163 := bstep (se 1 (by rfl) ⟨1575122, by rfl⟩ : syracuseStep 2100163 = 3150245) B3150245
theorem B3148753 : Blo 1865634 3148753 := bstep (se 2 (by rfl) ⟨1180782, by rfl⟩ : syracuseStep 3148753 = 2361565) B2361565
theorem B3148787 : Blo 1865634 3148787 := bstep (se 1 (by rfl) ⟨2361590, by rfl⟩ : syracuseStep 3148787 = 4723181) B4723181
theorem B9710605 : Blo 1865634 9710605 := bstep (se 3 (by rfl) ⟨1820738, by rfl⟩ : syracuseStep 9710605 = 3641477) B3641477
theorem B7973923 : Blo 1865634 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B2100307 : Blo 1865634 2100307 := bstep (se 1 (by rfl) ⟨1575230, by rfl⟩ : syracuseStep 2100307 = 3150461) B3150461
theorem B10087523 : Blo 1865634 10087523 := bstep (se 1 (by rfl) ⟨7565642, by rfl⟩ : syracuseStep 10087523 = 15131285) B15131285
theorem B3148915 : Blo 1865634 3148915 := bstep (se 1 (by rfl) ⟨2361686, by rfl⟩ : syracuseStep 3148915 = 4723373) B4723373
theorem B1993891 : Blo 1865634 1993891 := bstep (se 1 (by rfl) ⟨1495418, by rfl⟩ : syracuseStep 1993891 = 2990837) B2990837
theorem B10628273 : Blo 1865634 10628273 := bstep (se 2 (by rfl) ⟨3985602, by rfl⟩ : syracuseStep 10628273 = 7971205) B7971205
theorem B2362547 : Blo 1865634 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B2100451 : Blo 1865634 2100451 := bstep (se 1 (by rfl) ⟨1575338, by rfl⟩ : syracuseStep 2100451 = 3150677) B3150677
theorem B3149057 : Blo 1865634 3149057 := bstep (se 2 (by rfl) ⟨1180896, by rfl⟩ : syracuseStep 3149057 = 2361793) B2361793
theorem B3984707 : Blo 1865634 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B3362161 : Blo 1865634 3362161 := bstep (se 2 (by rfl) ⟨1260810, by rfl⟩ : syracuseStep 3362161 = 2521621) B2521621
theorem B2100595 : Blo 1865634 2100595 := bstep (se 1 (by rfl) ⟨1575446, by rfl⟩ : syracuseStep 2100595 = 3150893) B3150893
theorem B3149185 : Blo 1865634 3149185 := bstep (se 2 (by rfl) ⟨1180944, by rfl⟩ : syracuseStep 3149185 = 2361889) B2361889
theorem B3149219 : Blo 1865634 3149219 := bstep (se 1 (by rfl) ⟨2361914, by rfl⟩ : syracuseStep 3149219 = 4723829) B4723829
theorem B6303149 : Blo 1865634 6303149 := bstep (se 3 (by rfl) ⟨1181840, by rfl⟩ : syracuseStep 6303149 = 2363681) B2363681
theorem B3984817 : Blo 1865634 3984817 := bstep (se 2 (by rfl) ⟨1494306, by rfl⟩ : syracuseStep 3984817 = 2988613) B2988613
theorem B2657729 : Blo 1865634 2657729 := bstep (se 2 (by rfl) ⟨996648, by rfl⟩ : syracuseStep 2657729 = 1993297) B1993297
theorem B6303203 : Blo 1865634 6303203 := bstep (se 1 (by rfl) ⟨4727402, by rfl⟩ : syracuseStep 6303203 = 9454805) B9454805
theorem B2100739 : Blo 1865634 2100739 := bstep (se 1 (by rfl) ⟨1575554, by rfl⟩ : syracuseStep 2100739 = 3151109) B3151109
theorem B19410445 : Blo 1865634 19410445 := bstep (se 3 (by rfl) ⟨3639458, by rfl⟩ : syracuseStep 19410445 = 7278917) B7278917
theorem B9448973 : Blo 1865634 9448973 := bstep (se 3 (by rfl) ⟨1771682, by rfl⟩ : syracuseStep 9448973 = 3543365) B3543365
theorem B7089677 : Blo 1865634 7089677 := bstep (se 3 (by rfl) ⟨1329314, by rfl⟩ : syracuseStep 7089677 = 2658629) B2658629
theorem B4197905 : Blo 1865634 4197905 := bstep (se 2 (by rfl) ⟨1574214, by rfl⟩ : syracuseStep 4197905 = 3148429) B3148429
theorem B3542545 : Blo 1865634 3542545 := bstep (se 2 (by rfl) ⟨1328454, by rfl⟩ : syracuseStep 3542545 = 2656909) B2656909
theorem B2657809 : Blo 1865634 2657809 := bstep (se 2 (by rfl) ⟨996678, by rfl⟩ : syracuseStep 2657809 = 1993357) B1993357
theorem B4197923 : Blo 1865634 4197923 := bstep (se 1 (by rfl) ⟨3148442, by rfl⟩ : syracuseStep 4197923 = 6296885) B6296885
theorem B3149347 : Blo 1865634 3149347 := bstep (se 1 (by rfl) ⟨2362010, by rfl⟩ : syracuseStep 3149347 = 4724021) B4724021
theorem B11955761 : Blo 1865634 11955761 := bstep (se 2 (by rfl) ⟨4483410, by rfl⟩ : syracuseStep 11955761 = 8966821) B8966821
theorem B1994339 : Blo 1865634 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B20467313 : Blo 1865634 20467313 := bstep (se 2 (by rfl) ⟨7675242, by rfl⟩ : syracuseStep 20467313 = 15350485) B15350485
theorem B2100883 : Blo 1865634 2100883 := bstep (se 1 (by rfl) ⟨1575662, by rfl⟩ : syracuseStep 2100883 = 3151325) B3151325
theorem B3149489 : Blo 1865634 3149489 := bstep (se 2 (by rfl) ⟨1181058, by rfl⟩ : syracuseStep 3149489 = 2362117) B2362117
theorem B4484803 : Blo 1865634 4484803 := bstep (se 1 (by rfl) ⟨3363602, by rfl⟩ : syracuseStep 4484803 = 6727205) B6727205
theorem B4484899 : Blo 1865634 4484899 := bstep (se 1 (by rfl) ⟨3363674, by rfl⟩ : syracuseStep 4484899 = 6727349) B6727349
theorem B2101027 : Blo 1865634 2101027 := bstep (se 1 (by rfl) ⟨1575770, by rfl⟩ : syracuseStep 2101027 = 3151541) B3151541
theorem B4198193 : Blo 1865634 4198193 := bstep (se 2 (by rfl) ⟨1574322, by rfl⟩ : syracuseStep 4198193 = 3148645) B3148645
theorem B3149617 : Blo 1865634 3149617 := bstep (se 2 (by rfl) ⟨1181106, by rfl⟩ : syracuseStep 3149617 = 2362213) B2362213
theorem B4198211 : Blo 1865634 4198211 := bstep (se 1 (by rfl) ⟨3148658, by rfl⟩ : syracuseStep 4198211 = 6297317) B6297317
theorem B3149651 : Blo 1865634 3149651 := bstep (se 1 (by rfl) ⟨2362238, by rfl⟩ : syracuseStep 3149651 = 4724477) B4724477
theorem B2363251 : Blo 1865634 2363251 := bstep (se 1 (by rfl) ⟨1772438, by rfl⟩ : syracuseStep 2363251 = 3544877) B3544877
theorem B4722563 : Blo 1865634 4722563 := bstep (se 1 (by rfl) ⟨3541922, by rfl⟩ : syracuseStep 4722563 = 7083845) B7083845
theorem B11964293 : Blo 1865634 11964293 := bstep (se 4 (by rfl) ⟨1121652, by rfl⟩ : syracuseStep 11964293 = 2243305) B2243305
theorem B23916485 : Blo 1865634 23916485 := bstep (se 4 (by rfl) ⟨2242170, by rfl⟩ : syracuseStep 23916485 = 4484341) B4484341
theorem B17944517 : Blo 1865634 17944517 := bstep (se 4 (by rfl) ⟨1682298, by rfl⟩ : syracuseStep 17944517 = 3364597) B3364597
theorem B3149779 : Blo 1865634 3149779 := bstep (se 1 (by rfl) ⟨2362334, by rfl⟩ : syracuseStep 3149779 = 4724669) B4724669
theorem B2363347 : Blo 1865634 2363347 := bstep (se 1 (by rfl) ⟨1772510, by rfl⟩ : syracuseStep 2363347 = 3545021) B3545021
theorem B23318513 : Blo 1865634 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B4198481 : Blo 1865634 4198481 := bstep (se 2 (by rfl) ⟨1574430, by rfl⟩ : syracuseStep 4198481 = 3148861) B3148861
theorem B3149921 : Blo 1865634 3149921 := bstep (se 2 (by rfl) ⟨1181220, by rfl⟩ : syracuseStep 3149921 = 2362441) B2362441
theorem B4198499 : Blo 1865634 4198499 := bstep (se 1 (by rfl) ⟨3148874, by rfl⟩ : syracuseStep 4198499 = 6297749) B6297749
theorem B11350115 : Blo 1865634 11350115 := bstep (se 1 (by rfl) ⟨8512586, by rfl⟩ : syracuseStep 11350115 = 17025173) B17025173
theorem B3150049 : Blo 1865634 3150049 := bstep (se 2 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 3150049 = 2362537) B2362537
theorem B60575971 : Blo 1865634 60575971 := bstep (se 1 (by rfl) ⟨45431978, by rfl⟩ : syracuseStep 60575971 = 90863957) B90863957
theorem B3150083 : Blo 1865634 3150083 := bstep (se 1 (by rfl) ⟨2362562, by rfl⟩ : syracuseStep 3150083 = 4725125) B4725125
theorem B4788497 : Blo 1865634 4788497 := bstep (se 2 (by rfl) ⟨1795686, by rfl⟩ : syracuseStep 4788497 = 3591373) B3591373
theorem B2658595 : Blo 1865634 2658595 := bstep (se 1 (by rfl) ⟨1993946, by rfl⟩ : syracuseStep 2658595 = 3987893) B3987893
theorem B4198769 : Blo 1865634 4198769 := bstep (se 2 (by rfl) ⟨1574538, by rfl⟩ : syracuseStep 4198769 = 3149077) B3149077
theorem B4198787 : Blo 1865634 4198787 := bstep (se 1 (by rfl) ⟨3149090, by rfl⟩ : syracuseStep 4198787 = 6298181) B6298181
theorem B3150211 : Blo 1865634 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B15135173 : Blo 1865634 15135173 := bstep (se 4 (by rfl) ⟨1418922, by rfl⟩ : syracuseStep 15135173 = 2837845) B2837845
theorem B3150353 : Blo 1865634 3150353 := bstep (se 2 (by rfl) ⟨1181382, by rfl⟩ : syracuseStep 3150353 = 2362765) B2362765
theorem B3543601 : Blo 1865634 3543601 := bstep (se 2 (by rfl) ⟨1328850, by rfl⟩ : syracuseStep 3543601 = 2657701) B2657701
theorem B10629731 : Blo 1865634 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B4199057 : Blo 1865634 4199057 := bstep (se 2 (by rfl) ⟨1574646, by rfl⟩ : syracuseStep 4199057 = 3149293) B3149293
theorem B3150481 : Blo 1865634 3150481 := bstep (se 2 (by rfl) ⟨1181430, by rfl⟩ : syracuseStep 3150481 = 2362861) B2362861
theorem B4199075 : Blo 1865634 4199075 := bstep (se 1 (by rfl) ⟨3149306, by rfl⟩ : syracuseStep 4199075 = 6298613) B6298613
theorem B3150515 : Blo 1865634 3150515 := bstep (se 1 (by rfl) ⟨2362886, by rfl⟩ : syracuseStep 3150515 = 4725773) B4725773
theorem B2659073 : Blo 1865634 2659073 := bstep (se 2 (by rfl) ⟨997152, by rfl⟩ : syracuseStep 2659073 = 1994305) B1994305
theorem B4723505 : Blo 1865634 4723505 := bstep (se 2 (by rfl) ⟨1771314, by rfl⟩ : syracuseStep 4723505 = 3542629) B3542629
theorem B3150643 : Blo 1865634 3150643 := bstep (se 1 (by rfl) ⟨2362982, by rfl⟩ : syracuseStep 3150643 = 4725965) B4725965
theorem B4723555 : Blo 1865634 4723555 := bstep (se 1 (by rfl) ⟨3542666, by rfl⟩ : syracuseStep 4723555 = 7085333) B7085333
theorem B2659187 : Blo 1865634 2659187 := bstep (se 1 (by rfl) ⟨1994390, by rfl⟩ : syracuseStep 2659187 = 3988781) B3988781
theorem B2798465 : Blo 1865634 2798465 := bstep (se 2 (by rfl) ⟨1049424, by rfl⟩ : syracuseStep 2798465 = 2098849) B2098849
theorem B2839427 : Blo 1865634 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B38335373 : Blo 1865634 38335373 := bstep (se 3 (by rfl) ⟨7187882, by rfl⟩ : syracuseStep 38335373 = 14375765) B14375765
theorem B4486033 : Blo 1865634 4486033 := bstep (se 2 (by rfl) ⟨1682262, by rfl⟩ : syracuseStep 4486033 = 3364525) B3364525
theorem B2798483 : Blo 1865634 2798483 := bstep (se 1 (by rfl) ⟨2098862, by rfl⟩ : syracuseStep 2798483 = 4197725) B4197725
theorem B2798513 : Blo 1865634 2798513 := bstep (se 2 (by rfl) ⟨1049442, by rfl⟩ : syracuseStep 2798513 = 2098885) B2098885
theorem B4199345 : Blo 1865634 4199345 := bstep (se 2 (by rfl) ⟨1574754, by rfl⟩ : syracuseStep 4199345 = 3149509) B3149509
theorem B3150785 : Blo 1865634 3150785 := bstep (se 2 (by rfl) ⟨1181544, by rfl⟩ : syracuseStep 3150785 = 2363089) B2363089
theorem B2798531 : Blo 1865634 2798531 := bstep (se 1 (by rfl) ⟨2098898, by rfl⟩ : syracuseStep 2798531 = 4197797) B4197797
theorem B4199363 : Blo 1865634 4199363 := bstep (se 1 (by rfl) ⟨3149522, by rfl⟩ : syracuseStep 4199363 = 6299045) B6299045
theorem B3544003 : Blo 1865634 3544003 := bstep (se 1 (by rfl) ⟨2658002, by rfl⟩ : syracuseStep 3544003 = 5316005) B5316005
theorem B2798561 : Blo 1865634 2798561 := bstep (se 2 (by rfl) ⟨1049460, by rfl⟩ : syracuseStep 2798561 = 2098921) B2098921
theorem B11957219 : Blo 1865634 11957219 := bstep (se 1 (by rfl) ⟨8967914, by rfl⟩ : syracuseStep 11957219 = 17935829) B17935829
theorem B6296561 : Blo 1865634 6296561 := bstep (se 2 (by rfl) ⟨2361210, by rfl⟩ : syracuseStep 6296561 = 4722421) B4722421
theorem B4723697 : Blo 1865634 4723697 := bstep (se 2 (by rfl) ⟨1771386, by rfl⟩ : syracuseStep 4723697 = 3542773) B3542773
theorem B2798579 : Blo 1865634 2798579 := bstep (se 1 (by rfl) ⟨2098934, by rfl⟩ : syracuseStep 2798579 = 4197869) B4197869
theorem B3544049 : Blo 1865634 3544049 := bstep (se 2 (by rfl) ⟨1329018, by rfl⟩ : syracuseStep 3544049 = 2658037) B2658037
theorem B7975921 : Blo 1865634 7975921 := bstep (se 2 (by rfl) ⟨2990970, by rfl⟩ : syracuseStep 7975921 = 5981941) B5981941
theorem B2798609 : Blo 1865634 2798609 := bstep (se 2 (by rfl) ⟨1049478, by rfl⟩ : syracuseStep 2798609 = 2098957) B2098957
theorem B2798627 : Blo 1865634 2798627 := bstep (se 1 (by rfl) ⟨2098970, by rfl⟩ : syracuseStep 2798627 = 4197941) B4197941
theorem B2798657 : Blo 1865634 2798657 := bstep (se 2 (by rfl) ⟨1049496, by rfl⟩ : syracuseStep 2798657 = 2098993) B2098993
theorem B3150913 : Blo 1865634 3150913 := bstep (se 2 (by rfl) ⟨1181592, by rfl⟩ : syracuseStep 3150913 = 2363185) B2363185
theorem B5313613 : Blo 1865634 5313613 := bstep (se 3 (by rfl) ⟨996302, by rfl⟩ : syracuseStep 5313613 = 1992605) B1992605
theorem B2798675 : Blo 1865634 2798675 := bstep (se 1 (by rfl) ⟨2099006, by rfl⟩ : syracuseStep 2798675 = 4198013) B4198013
theorem B3150947 : Blo 1865634 3150947 := bstep (se 1 (by rfl) ⟨2363210, by rfl⟩ : syracuseStep 3150947 = 4726421) B4726421
theorem B2798705 : Blo 1865634 2798705 := bstep (se 2 (by rfl) ⟨1049514, by rfl⟩ : syracuseStep 2798705 = 2099029) B2099029
theorem B2798723 : Blo 1865634 2798723 := bstep (se 1 (by rfl) ⟨2099042, by rfl⟩ : syracuseStep 2798723 = 4198085) B4198085
theorem B2798753 : Blo 1865634 2798753 := bstep (se 2 (by rfl) ⟨1049532, by rfl⟩ : syracuseStep 2798753 = 2099065) B2099065
theorem B2798771 : Blo 1865634 2798771 := bstep (se 1 (by rfl) ⟨2099078, by rfl⟩ : syracuseStep 2798771 = 4198157) B4198157
theorem B2798801 : Blo 1865634 2798801 := bstep (se 2 (by rfl) ⟨1049550, by rfl⟩ : syracuseStep 2798801 = 2099101) B2099101
theorem B4199633 : Blo 1865634 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B2798819 : Blo 1865634 2798819 := bstep (se 1 (by rfl) ⟨2099114, by rfl⟩ : syracuseStep 2798819 = 4198229) B4198229
theorem B4199651 : Blo 1865634 4199651 := bstep (se 1 (by rfl) ⟨3149738, by rfl⟩ : syracuseStep 4199651 = 6299477) B6299477
theorem B3151075 : Blo 1865634 3151075 := bstep (se 1 (by rfl) ⟨2363306, by rfl⟩ : syracuseStep 3151075 = 4726613) B4726613
theorem B5043437 : Blo 1865634 5043437 := bstep (se 3 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 5043437 = 1891289) B1891289
theorem B14169329 : Blo 1865634 14169329 := bstep (se 2 (by rfl) ⟨5313498, by rfl⟩ : syracuseStep 14169329 = 10626997) B10626997
theorem B2798849 : Blo 1865634 2798849 := bstep (se 2 (by rfl) ⟨1049568, by rfl⟩ : syracuseStep 2798849 = 2099137) B2099137
theorem B3544337 : Blo 1865634 3544337 := bstep (se 2 (by rfl) ⟨1329126, by rfl⟩ : syracuseStep 3544337 = 2658253) B2658253
theorem B2798867 : Blo 1865634 2798867 := bstep (se 1 (by rfl) ⟨2099150, by rfl⟩ : syracuseStep 2798867 = 4198301) B4198301
theorem B2798897 : Blo 1865634 2798897 := bstep (se 2 (by rfl) ⟨1049586, by rfl⟩ : syracuseStep 2798897 = 2099173) B2099173
theorem B2798915 : Blo 1865634 2798915 := bstep (se 1 (by rfl) ⟨2099186, by rfl⟩ : syracuseStep 2798915 = 4198373) B4198373
theorem B5387587 : Blo 1865634 5387587 := bstep (se 1 (by rfl) ⟨4040690, by rfl⟩ : syracuseStep 5387587 = 8081381) B8081381
theorem B2798945 : Blo 1865634 2798945 := bstep (se 2 (by rfl) ⟨1049604, by rfl⟩ : syracuseStep 2798945 = 2099209) B2099209
theorem B7181681 : Blo 1865634 7181681 := bstep (se 2 (by rfl) ⟨2693130, by rfl⟩ : syracuseStep 7181681 = 5386261) B5386261
theorem B3151217 : Blo 1865634 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B2798963 : Blo 1865634 2798963 := bstep (se 1 (by rfl) ⟨2099222, by rfl⟩ : syracuseStep 2798963 = 4198445) B4198445
theorem B2798993 : Blo 1865634 2798993 := bstep (se 2 (by rfl) ⟨1049622, by rfl⟩ : syracuseStep 2798993 = 2099245) B2099245
theorem B3986833 : Blo 1865634 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B2799011 : Blo 1865634 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B6387121 : Blo 1865634 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B2799041 : Blo 1865634 2799041 := bstep (se 2 (by rfl) ⟨1049640, by rfl⟩ : syracuseStep 2799041 = 2099281) B2099281
theorem B2799059 : Blo 1865634 2799059 := bstep (se 1 (by rfl) ⟨2099294, by rfl⟩ : syracuseStep 2799059 = 4198589) B4198589
theorem B2799089 : Blo 1865634 2799089 := bstep (se 2 (by rfl) ⟨1049658, by rfl⟩ : syracuseStep 2799089 = 2099317) B2099317
theorem B4199921 : Blo 1865634 4199921 := bstep (se 2 (by rfl) ⟨1574970, by rfl⟩ : syracuseStep 4199921 = 3149941) B3149941
theorem B3151345 : Blo 1865634 3151345 := bstep (se 2 (by rfl) ⟨1181754, by rfl⟩ : syracuseStep 3151345 = 2363509) B2363509
theorem B2799107 : Blo 1865634 2799107 := bstep (se 1 (by rfl) ⟨2099330, by rfl⟩ : syracuseStep 2799107 = 4198661) B4198661
theorem B4199939 : Blo 1865634 4199939 := bstep (se 1 (by rfl) ⟨3149954, by rfl⟩ : syracuseStep 4199939 = 6299909) B6299909
theorem B6297101 : Blo 1865634 6297101 := bstep (se 3 (by rfl) ⟨1180706, by rfl⟩ : syracuseStep 6297101 = 2361413) B2361413
theorem B3151379 : Blo 1865634 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B2799137 : Blo 1865634 2799137 := bstep (se 2 (by rfl) ⟨1049676, by rfl⟩ : syracuseStep 2799137 = 2099353) B2099353
theorem B2799155 : Blo 1865634 2799155 := bstep (se 1 (by rfl) ⟨2099366, by rfl⟩ : syracuseStep 2799155 = 4198733) B4198733
theorem B6297155 : Blo 1865634 6297155 := bstep (se 1 (by rfl) ⟨4722866, by rfl⟩ : syracuseStep 6297155 = 9445733) B9445733
theorem B2799185 : Blo 1865634 2799185 := bstep (se 2 (by rfl) ⟨1049694, by rfl⟩ : syracuseStep 2799185 = 2099389) B2099389
theorem B2799203 : Blo 1865634 2799203 := bstep (se 1 (by rfl) ⟨2099402, by rfl⟩ : syracuseStep 2799203 = 4198805) B4198805
theorem B14366321 : Blo 1865634 14366321 := bstep (se 2 (by rfl) ⟨5387370, by rfl⟩ : syracuseStep 14366321 = 10774741) B10774741
theorem B2799233 : Blo 1865634 2799233 := bstep (se 2 (by rfl) ⟨1049712, by rfl⟩ : syracuseStep 2799233 = 2099425) B2099425
theorem B5912195 : Blo 1865634 5912195 := bstep (se 1 (by rfl) ⟨4434146, by rfl⟩ : syracuseStep 5912195 = 8868293) B8868293
theorem B26908301 : Blo 1865634 26908301 := bstep (se 3 (by rfl) ⟨5045306, by rfl⟩ : syracuseStep 26908301 = 10090613) B10090613
theorem B2799251 : Blo 1865634 2799251 := bstep (se 1 (by rfl) ⟨2099438, by rfl⟩ : syracuseStep 2799251 = 4198877) B4198877
theorem B3151507 : Blo 1865634 3151507 := bstep (se 1 (by rfl) ⟨2363630, by rfl⟩ : syracuseStep 3151507 = 4727261) B4727261
theorem B2799281 : Blo 1865634 2799281 := bstep (se 2 (by rfl) ⟨1049730, by rfl⟩ : syracuseStep 2799281 = 2099461) B2099461
theorem B2799299 : Blo 1865634 2799299 := bstep (se 1 (by rfl) ⟨2099474, by rfl⟩ : syracuseStep 2799299 = 4198949) B4198949
theorem B2799329 : Blo 1865634 2799329 := bstep (se 2 (by rfl) ⟨1049748, by rfl⟩ : syracuseStep 2799329 = 2099497) B2099497
theorem B2799347 : Blo 1865634 2799347 := bstep (se 1 (by rfl) ⟨2099510, by rfl⟩ : syracuseStep 2799347 = 4199021) B4199021
theorem B2799377 : Blo 1865634 2799377 := bstep (se 2 (by rfl) ⟨1049766, by rfl⟩ : syracuseStep 2799377 = 2099533) B2099533
theorem B4200209 : Blo 1865634 4200209 := bstep (se 2 (by rfl) ⟨1575078, by rfl⟩ : syracuseStep 4200209 = 3150157) B3150157
theorem B5977891 : Blo 1865634 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B2799395 : Blo 1865634 2799395 := bstep (se 1 (by rfl) ⟨2099546, by rfl⟩ : syracuseStep 2799395 = 4199093) B4199093
theorem B4200227 : Blo 1865634 4200227 := bstep (se 1 (by rfl) ⟨3150170, by rfl⟩ : syracuseStep 4200227 = 6300341) B6300341
theorem B3987235 : Blo 1865634 3987235 := bstep (se 1 (by rfl) ⟨2990426, by rfl⟩ : syracuseStep 3987235 = 5980853) B5980853
theorem B2799425 : Blo 1865634 2799425 := bstep (se 2 (by rfl) ⟨1049784, by rfl⟩ : syracuseStep 2799425 = 2099569) B2099569
theorem B6297425 : Blo 1865634 6297425 := bstep (se 2 (by rfl) ⟨2361534, by rfl⟩ : syracuseStep 6297425 = 4723069) B4723069
theorem B2799443 : Blo 1865634 2799443 := bstep (se 1 (by rfl) ⟨2099582, by rfl⟩ : syracuseStep 2799443 = 4199165) B4199165
theorem B2021203 : Blo 1865634 2021203 := bstep (se 1 (by rfl) ⟨1515902, by rfl⟩ : syracuseStep 2021203 = 3031805) B3031805
theorem B7083875 : Blo 1865634 7083875 := bstep (se 1 (by rfl) ⟨5312906, by rfl⟩ : syracuseStep 7083875 = 10625813) B10625813
theorem B2799473 : Blo 1865634 2799473 := bstep (se 2 (by rfl) ⟨1049802, by rfl⟩ : syracuseStep 2799473 = 2099605) B2099605
theorem B2799491 : Blo 1865634 2799491 := bstep (se 1 (by rfl) ⟨2099618, by rfl⟩ : syracuseStep 2799491 = 4199237) B4199237
theorem B2799521 : Blo 1865634 2799521 := bstep (se 2 (by rfl) ⟨1049820, by rfl⟩ : syracuseStep 2799521 = 2099641) B2099641
theorem B1865635 : Blo 1865634 1865635 := bstep (se 1 (by rfl) ⟨1399226, by rfl⟩ : syracuseStep 1865635 = 2798453) B2798453
theorem B1865651 : Blo 1865634 1865651 := bstep (se 1 (by rfl) ⟨1399238, by rfl⟩ : syracuseStep 1865651 = 2798477) B2798477
theorem B2799539 : Blo 1865634 2799539 := bstep (se 1 (by rfl) ⟨2099654, by rfl⟩ : syracuseStep 2799539 = 4199309) B4199309
theorem B1865667 : Blo 1865634 1865667 := bstep (se 1 (by rfl) ⟨1399250, by rfl⟩ : syracuseStep 1865667 = 2798501) B2798501
theorem B2799569 : Blo 1865634 2799569 := bstep (se 2 (by rfl) ⟨1049838, by rfl⟩ : syracuseStep 2799569 = 2099677) B2099677
theorem B4724689 : Blo 1865634 4724689 := bstep (se 2 (by rfl) ⟨1771758, by rfl⟩ : syracuseStep 4724689 = 3543517) B3543517
theorem B1865683 : Blo 1865634 1865683 := bstep (se 1 (by rfl) ⟨1399262, by rfl⟩ : syracuseStep 1865683 = 2798525) B2798525
theorem B1865699 : Blo 1865634 1865699 := bstep (se 1 (by rfl) ⟨1399274, by rfl⟩ : syracuseStep 1865699 = 2798549) B2798549
theorem B2799587 : Blo 1865634 2799587 := bstep (se 1 (by rfl) ⟨2099690, by rfl⟩ : syracuseStep 2799587 = 4199381) B4199381
theorem B3545059 : Blo 1865634 3545059 := bstep (se 1 (by rfl) ⟨2658794, by rfl⟩ : syracuseStep 3545059 = 5317589) B5317589
theorem B1865715 : Blo 1865634 1865715 := bstep (se 1 (by rfl) ⟨1399286, by rfl⟩ : syracuseStep 1865715 = 2798573) B2798573
theorem B2799617 : Blo 1865634 2799617 := bstep (se 2 (by rfl) ⟨1049856, by rfl⟩ : syracuseStep 2799617 = 2099713) B2099713
theorem B1865731 : Blo 1865634 1865731 := bstep (se 1 (by rfl) ⟨1399298, by rfl⟩ : syracuseStep 1865731 = 2798597) B2798597
theorem B1865747 : Blo 1865634 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B2799635 : Blo 1865634 2799635 := bstep (se 1 (by rfl) ⟨2099726, by rfl⟩ : syracuseStep 2799635 = 4199453) B4199453
theorem B1865763 : Blo 1865634 1865763 := bstep (se 1 (by rfl) ⟨1399322, by rfl⟩ : syracuseStep 1865763 = 2798645) B2798645
theorem B2799665 : Blo 1865634 2799665 := bstep (se 2 (by rfl) ⟨1049874, by rfl⟩ : syracuseStep 2799665 = 2099749) B2099749
theorem B4200497 : Blo 1865634 4200497 := bstep (se 2 (by rfl) ⟨1575186, by rfl⟩ : syracuseStep 4200497 = 3150373) B3150373
theorem B1865779 : Blo 1865634 1865779 := bstep (se 1 (by rfl) ⟨1399334, by rfl⟩ : syracuseStep 1865779 = 2798669) B2798669
theorem B1865795 : Blo 1865634 1865795 := bstep (se 1 (by rfl) ⟨1399346, by rfl⟩ : syracuseStep 1865795 = 2798693) B2798693
theorem B2799683 : Blo 1865634 2799683 := bstep (se 1 (by rfl) ⟨2099762, by rfl⟩ : syracuseStep 2799683 = 4199525) B4199525
theorem B4200515 : Blo 1865634 4200515 := bstep (se 1 (by rfl) ⟨3150386, by rfl⟩ : syracuseStep 4200515 = 6300773) B6300773
theorem B20191301 : Blo 1865634 20191301 := bstep (se 4 (by rfl) ⟨1892934, by rfl⟩ : syracuseStep 20191301 = 3785869) B3785869
theorem B1865811 : Blo 1865634 1865811 := bstep (se 1 (by rfl) ⟨1399358, by rfl⟩ : syracuseStep 1865811 = 2798717) B2798717
theorem B2799713 : Blo 1865634 2799713 := bstep (se 2 (by rfl) ⟨1049892, by rfl⟩ : syracuseStep 2799713 = 2099785) B2099785
theorem B1865827 : Blo 1865634 1865827 := bstep (se 1 (by rfl) ⟨1399370, by rfl⟩ : syracuseStep 1865827 = 2798741) B2798741
theorem B5978225 : Blo 1865634 5978225 := bstep (se 2 (by rfl) ⟨2241834, by rfl⟩ : syracuseStep 5978225 = 4483669) B4483669
theorem B5314673 : Blo 1865634 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B1865843 : Blo 1865634 1865843 := bstep (se 1 (by rfl) ⟨1399382, by rfl⟩ : syracuseStep 1865843 = 2798765) B2798765
theorem B2799731 : Blo 1865634 2799731 := bstep (se 1 (by rfl) ⟨2099798, by rfl⟩ : syracuseStep 2799731 = 4199597) B4199597
theorem B1865859 : Blo 1865634 1865859 := bstep (se 1 (by rfl) ⟨1399394, by rfl⟩ : syracuseStep 1865859 = 2798789) B2798789
theorem B2799761 : Blo 1865634 2799761 := bstep (se 2 (by rfl) ⟨1049910, by rfl⟩ : syracuseStep 2799761 = 2099821) B2099821
theorem B1865875 : Blo 1865634 1865875 := bstep (se 1 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 1865875 = 2798813) B2798813
theorem B1865891 : Blo 1865634 1865891 := bstep (se 1 (by rfl) ⟨1399418, by rfl⟩ : syracuseStep 1865891 = 2798837) B2798837
theorem B2799779 : Blo 1865634 2799779 := bstep (se 1 (by rfl) ⟨2099834, by rfl⟩ : syracuseStep 2799779 = 4199669) B4199669
theorem B1865907 : Blo 1865634 1865907 := bstep (se 1 (by rfl) ⟨1399430, by rfl⟩ : syracuseStep 1865907 = 2798861) B2798861
theorem B2799809 : Blo 1865634 2799809 := bstep (se 2 (by rfl) ⟨1049928, by rfl⟩ : syracuseStep 2799809 = 2099857) B2099857
theorem B1865923 : Blo 1865634 1865923 := bstep (se 1 (by rfl) ⟨1399442, by rfl⟩ : syracuseStep 1865923 = 2798885) B2798885
theorem B3365059 : Blo 1865634 3365059 := bstep (se 1 (by rfl) ⟨2523794, by rfl⟩ : syracuseStep 3365059 = 5047589) B5047589
theorem B1865939 : Blo 1865634 1865939 := bstep (se 1 (by rfl) ⟨1399454, by rfl⟩ : syracuseStep 1865939 = 2798909) B2798909
theorem B2799827 : Blo 1865634 2799827 := bstep (se 1 (by rfl) ⟨2099870, by rfl⟩ : syracuseStep 2799827 = 4199741) B4199741
theorem B1865955 : Blo 1865634 1865955 := bstep (se 1 (by rfl) ⟨1399466, by rfl⟩ : syracuseStep 1865955 = 2798933) B2798933
theorem B4724963 : Blo 1865634 4724963 := bstep (se 1 (by rfl) ⟨3543722, by rfl⟩ : syracuseStep 4724963 = 7087445) B7087445
theorem B2799857 : Blo 1865634 2799857 := bstep (se 2 (by rfl) ⟨1049946, by rfl⟩ : syracuseStep 2799857 = 2099893) B2099893
theorem B1865971 : Blo 1865634 1865971 := bstep (se 1 (by rfl) ⟨1399478, by rfl⟩ : syracuseStep 1865971 = 2798957) B2798957
theorem B1865987 : Blo 1865634 1865987 := bstep (se 1 (by rfl) ⟨1399490, by rfl⟩ : syracuseStep 1865987 = 2798981) B2798981
theorem B2799875 : Blo 1865634 2799875 := bstep (se 1 (by rfl) ⟨2099906, by rfl⟩ : syracuseStep 2799875 = 4199813) B4199813
theorem B1866003 : Blo 1865634 1866003 := bstep (se 1 (by rfl) ⟨1399502, by rfl⟩ : syracuseStep 1866003 = 2799005) B2799005
theorem B2799905 : Blo 1865634 2799905 := bstep (se 2 (by rfl) ⟨1049964, by rfl⟩ : syracuseStep 2799905 = 2099929) B2099929
theorem B1866019 : Blo 1865634 1866019 := bstep (se 1 (by rfl) ⟨1399514, by rfl⟩ : syracuseStep 1866019 = 2799029) B2799029
theorem B1866035 : Blo 1865634 1866035 := bstep (se 1 (by rfl) ⟨1399526, by rfl⟩ : syracuseStep 1866035 = 2799053) B2799053
theorem B2799923 : Blo 1865634 2799923 := bstep (se 1 (by rfl) ⟨2099942, by rfl⟩ : syracuseStep 2799923 = 4199885) B4199885
theorem B1866051 : Blo 1865634 1866051 := bstep (se 1 (by rfl) ⟨1399538, by rfl⟩ : syracuseStep 1866051 = 2799077) B2799077
theorem B2799953 : Blo 1865634 2799953 := bstep (se 2 (by rfl) ⟨1049982, by rfl⟩ : syracuseStep 2799953 = 2099965) B2099965
theorem B4200785 : Blo 1865634 4200785 := bstep (se 2 (by rfl) ⟨1575294, by rfl⟩ : syracuseStep 4200785 = 3150589) B3150589
theorem B1866067 : Blo 1865634 1866067 := bstep (se 1 (by rfl) ⟨1399550, by rfl⟩ : syracuseStep 1866067 = 2799101) B2799101
theorem B2693459 : Blo 1865634 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B1866083 : Blo 1865634 1866083 := bstep (se 1 (by rfl) ⟨1399562, by rfl⟩ : syracuseStep 1866083 = 2799125) B2799125
theorem B2799971 : Blo 1865634 2799971 := bstep (se 1 (by rfl) ⟨2099978, by rfl⟩ : syracuseStep 2799971 = 4199957) B4199957
theorem B4200803 : Blo 1865634 4200803 := bstep (se 1 (by rfl) ⟨3150602, by rfl⟩ : syracuseStep 4200803 = 6301205) B6301205
theorem B6297965 : Blo 1865634 6297965 := bstep (se 3 (by rfl) ⟨1180868, by rfl⟩ : syracuseStep 6297965 = 2361737) B2361737
theorem B9451889 : Blo 1865634 9451889 := bstep (se 2 (by rfl) ⟨3544458, by rfl⟩ : syracuseStep 9451889 = 7088917) B7088917
theorem B2521459 : Blo 1865634 2521459 := bstep (se 1 (by rfl) ⟨1891094, by rfl⟩ : syracuseStep 2521459 = 3782189) B3782189
theorem B1866099 : Blo 1865634 1866099 := bstep (se 1 (by rfl) ⟨1399574, by rfl⟩ : syracuseStep 1866099 = 2799149) B2799149
theorem B2800001 : Blo 1865634 2800001 := bstep (se 2 (by rfl) ⟨1050000, by rfl⟩ : syracuseStep 2800001 = 2100001) B2100001
theorem B1866115 : Blo 1865634 1866115 := bstep (se 1 (by rfl) ⟨1399586, by rfl⟩ : syracuseStep 1866115 = 2799173) B2799173
theorem B6388109 : Blo 1865634 6388109 := bstep (se 3 (by rfl) ⟨1197770, by rfl⟩ : syracuseStep 6388109 = 2395541) B2395541
theorem B2988433 : Blo 1865634 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B1866131 : Blo 1865634 1866131 := bstep (se 1 (by rfl) ⟨1399598, by rfl⟩ : syracuseStep 1866131 = 2799197) B2799197
theorem B2800019 : Blo 1865634 2800019 := bstep (se 1 (by rfl) ⟨2100014, by rfl⟩ : syracuseStep 2800019 = 4200029) B4200029
theorem B6298019 : Blo 1865634 6298019 := bstep (se 1 (by rfl) ⟨4723514, by rfl⟩ : syracuseStep 6298019 = 9447029) B9447029
theorem B1866147 : Blo 1865634 1866147 := bstep (se 1 (by rfl) ⟨1399610, by rfl⟩ : syracuseStep 1866147 = 2799221) B2799221
theorem B4725155 : Blo 1865634 4725155 := bstep (se 1 (by rfl) ⟨3543866, by rfl⟩ : syracuseStep 4725155 = 7087733) B7087733
theorem B3545507 : Blo 1865634 3545507 := bstep (se 1 (by rfl) ⟨2659130, by rfl⟩ : syracuseStep 3545507 = 5318261) B5318261
theorem B2800049 : Blo 1865634 2800049 := bstep (se 2 (by rfl) ⟨1050018, by rfl⟩ : syracuseStep 2800049 = 2100037) B2100037
theorem B1866163 : Blo 1865634 1866163 := bstep (se 1 (by rfl) ⟨1399622, by rfl⟩ : syracuseStep 1866163 = 2799245) B2799245
theorem B1866179 : Blo 1865634 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B2800067 : Blo 1865634 2800067 := bstep (se 1 (by rfl) ⟨2100050, by rfl⟩ : syracuseStep 2800067 = 4200101) B4200101
theorem B1866195 : Blo 1865634 1866195 := bstep (se 1 (by rfl) ⟨1399646, by rfl⟩ : syracuseStep 1866195 = 2799293) B2799293
theorem B2800097 : Blo 1865634 2800097 := bstep (se 2 (by rfl) ⟨1050036, by rfl⟩ : syracuseStep 2800097 = 2100073) B2100073
theorem B1866211 : Blo 1865634 1866211 := bstep (se 1 (by rfl) ⟨1399658, by rfl⟩ : syracuseStep 1866211 = 2799317) B2799317
theorem B7084529 : Blo 1865634 7084529 := bstep (se 2 (by rfl) ⟨2656698, by rfl⟩ : syracuseStep 7084529 = 5313397) B5313397
theorem B1866227 : Blo 1865634 1866227 := bstep (se 1 (by rfl) ⟨1399670, by rfl⟩ : syracuseStep 1866227 = 2799341) B2799341
theorem B2800115 : Blo 1865634 2800115 := bstep (se 1 (by rfl) ⟨2100086, by rfl⟩ : syracuseStep 2800115 = 4200173) B4200173
theorem B1866243 : Blo 1865634 1866243 := bstep (se 1 (by rfl) ⟨1399682, by rfl⟩ : syracuseStep 1866243 = 2799365) B2799365
theorem B2800145 : Blo 1865634 2800145 := bstep (se 2 (by rfl) ⟨1050054, by rfl⟩ : syracuseStep 2800145 = 2100109) B2100109
theorem B1866259 : Blo 1865634 1866259 := bstep (se 1 (by rfl) ⟨1399694, by rfl⟩ : syracuseStep 1866259 = 2799389) B2799389
theorem B2128403 : Blo 1865634 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B3783203 : Blo 1865634 3783203 := bstep (se 1 (by rfl) ⟨2837402, by rfl⟩ : syracuseStep 3783203 = 5674805) B5674805
theorem B1866275 : Blo 1865634 1866275 := bstep (se 1 (by rfl) ⟨1399706, by rfl⟩ : syracuseStep 1866275 = 2799413) B2799413
theorem B2800163 : Blo 1865634 2800163 := bstep (se 1 (by rfl) ⟨2100122, by rfl⟩ : syracuseStep 2800163 = 4200245) B4200245
theorem B1866291 : Blo 1865634 1866291 := bstep (se 1 (by rfl) ⟨1399718, by rfl⟩ : syracuseStep 1866291 = 2799437) B2799437
theorem B3029569 : Blo 1865634 3029569 := bstep (se 2 (by rfl) ⟨1136088, by rfl⟩ : syracuseStep 3029569 = 2272177) B2272177
theorem B2800193 : Blo 1865634 2800193 := bstep (se 2 (by rfl) ⟨1050072, by rfl⟩ : syracuseStep 2800193 = 2100145) B2100145
theorem B1866307 : Blo 1865634 1866307 := bstep (se 1 (by rfl) ⟨1399730, by rfl⟩ : syracuseStep 1866307 = 2799461) B2799461
theorem B1866323 : Blo 1865634 1866323 := bstep (se 1 (by rfl) ⟨1399742, by rfl⟩ : syracuseStep 1866323 = 2799485) B2799485
theorem B2800211 : Blo 1865634 2800211 := bstep (se 1 (by rfl) ⟨2100158, by rfl⟩ : syracuseStep 2800211 = 4200317) B4200317
theorem B1866339 : Blo 1865634 1866339 := bstep (se 1 (by rfl) ⟨1399754, by rfl⟩ : syracuseStep 1866339 = 2799509) B2799509
theorem B2800241 : Blo 1865634 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B4201073 : Blo 1865634 4201073 := bstep (se 2 (by rfl) ⟨1575402, by rfl⟩ : syracuseStep 4201073 = 3150805) B3150805
theorem B1866355 : Blo 1865634 1866355 := bstep (se 1 (by rfl) ⟨1399766, by rfl⟩ : syracuseStep 1866355 = 2799533) B2799533
theorem B2521729 : Blo 1865634 2521729 := bstep (se 2 (by rfl) ⟨945648, by rfl⟩ : syracuseStep 2521729 = 1891297) B1891297
theorem B1866371 : Blo 1865634 1866371 := bstep (se 1 (by rfl) ⟨1399778, by rfl⟩ : syracuseStep 1866371 = 2799557) B2799557
theorem B2800259 : Blo 1865634 2800259 := bstep (se 1 (by rfl) ⟨2100194, by rfl⟩ : syracuseStep 2800259 = 4200389) B4200389
theorem B4201091 : Blo 1865634 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B1866387 : Blo 1865634 1866387 := bstep (se 1 (by rfl) ⟨1399790, by rfl⟩ : syracuseStep 1866387 = 2799581) B2799581
theorem B2800289 : Blo 1865634 2800289 := bstep (se 2 (by rfl) ⟨1050108, by rfl⟩ : syracuseStep 2800289 = 2100217) B2100217
theorem B1866403 : Blo 1865634 1866403 := bstep (se 1 (by rfl) ⟨1399802, by rfl⟩ : syracuseStep 1866403 = 2799605) B2799605
theorem B6298289 : Blo 1865634 6298289 := bstep (se 2 (by rfl) ⟨2361858, by rfl⟩ : syracuseStep 6298289 = 4723717) B4723717
theorem B11958961 : Blo 1865634 11958961 := bstep (se 2 (by rfl) ⟨4484610, by rfl⟩ : syracuseStep 11958961 = 8969221) B8969221
theorem B1866419 : Blo 1865634 1866419 := bstep (se 1 (by rfl) ⟨1399814, by rfl⟩ : syracuseStep 1866419 = 2799629) B2799629
theorem B2800307 : Blo 1865634 2800307 := bstep (se 1 (by rfl) ⟨2100230, by rfl⟩ : syracuseStep 2800307 = 4200461) B4200461
theorem B1866435 : Blo 1865634 1866435 := bstep (se 1 (by rfl) ⟨1399826, by rfl⟩ : syracuseStep 1866435 = 2799653) B2799653
theorem B2800337 : Blo 1865634 2800337 := bstep (se 2 (by rfl) ⟨1050126, by rfl⟩ : syracuseStep 2800337 = 2100253) B2100253
theorem B1866451 : Blo 1865634 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B1866467 : Blo 1865634 1866467 := bstep (se 1 (by rfl) ⟨1399850, by rfl⟩ : syracuseStep 1866467 = 2799701) B2799701
theorem B2800355 : Blo 1865634 2800355 := bstep (se 1 (by rfl) ⟨2100266, by rfl⟩ : syracuseStep 2800355 = 4200533) B4200533
theorem B1866483 : Blo 1865634 1866483 := bstep (se 1 (by rfl) ⟨1399862, by rfl⟩ : syracuseStep 1866483 = 2799725) B2799725
theorem B2800385 : Blo 1865634 2800385 := bstep (se 2 (by rfl) ⟨1050144, by rfl⟩ : syracuseStep 2800385 = 2100289) B2100289
theorem B2521859 : Blo 1865634 2521859 := bstep (se 1 (by rfl) ⟨1891394, by rfl⟩ : syracuseStep 2521859 = 3782789) B3782789
theorem B1866499 : Blo 1865634 1866499 := bstep (se 1 (by rfl) ⟨1399874, by rfl⟩ : syracuseStep 1866499 = 2799749) B2799749
theorem B7969549 : Blo 1865634 7969549 := bstep (se 3 (by rfl) ⟨1494290, by rfl⟩ : syracuseStep 7969549 = 2988581) B2988581
theorem B5315345 : Blo 1865634 5315345 := bstep (se 2 (by rfl) ⟨1993254, by rfl⟩ : syracuseStep 5315345 = 3986509) B3986509
theorem B1866515 : Blo 1865634 1866515 := bstep (se 1 (by rfl) ⟨1399886, by rfl⟩ : syracuseStep 1866515 = 2799773) B2799773
theorem B2800403 : Blo 1865634 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B1866531 : Blo 1865634 1866531 := bstep (se 1 (by rfl) ⟨1399898, by rfl⟩ : syracuseStep 1866531 = 2799797) B2799797
theorem B2800433 : Blo 1865634 2800433 := bstep (se 2 (by rfl) ⟨1050162, by rfl⟩ : syracuseStep 2800433 = 2100325) B2100325
theorem B1866547 : Blo 1865634 1866547 := bstep (se 1 (by rfl) ⟨1399910, by rfl⟩ : syracuseStep 1866547 = 2799821) B2799821
theorem B1866563 : Blo 1865634 1866563 := bstep (se 1 (by rfl) ⟨1399922, by rfl⟩ : syracuseStep 1866563 = 2799845) B2799845
theorem B2800451 : Blo 1865634 2800451 := bstep (se 1 (by rfl) ⟨2100338, by rfl⟩ : syracuseStep 2800451 = 4200677) B4200677
theorem B1866579 : Blo 1865634 1866579 := bstep (se 1 (by rfl) ⟨1399934, by rfl⟩ : syracuseStep 1866579 = 2799869) B2799869
theorem B2800481 : Blo 1865634 2800481 := bstep (se 2 (by rfl) ⟨1050180, by rfl⟩ : syracuseStep 2800481 = 2100361) B2100361
theorem B1866595 : Blo 1865634 1866595 := bstep (se 1 (by rfl) ⟨1399946, by rfl⟩ : syracuseStep 1866595 = 2799893) B2799893
theorem B5675885 : Blo 1865634 5675885 := bstep (se 3 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 5675885 = 2128457) B2128457
theorem B1866611 : Blo 1865634 1866611 := bstep (se 1 (by rfl) ⟨1399958, by rfl⟩ : syracuseStep 1866611 = 2799917) B2799917
theorem B2800499 : Blo 1865634 2800499 := bstep (se 1 (by rfl) ⟨2100374, by rfl⟩ : syracuseStep 2800499 = 4200749) B4200749
theorem B1866627 : Blo 1865634 1866627 := bstep (se 1 (by rfl) ⟨1399970, by rfl⟩ : syracuseStep 1866627 = 2799941) B2799941
theorem B2800529 : Blo 1865634 2800529 := bstep (se 2 (by rfl) ⟨1050198, by rfl⟩ : syracuseStep 2800529 = 2100397) B2100397
theorem B4201361 : Blo 1865634 4201361 := bstep (se 2 (by rfl) ⟨1575510, by rfl⟩ : syracuseStep 4201361 = 3151021) B3151021
theorem B1866643 : Blo 1865634 1866643 := bstep (se 1 (by rfl) ⟨1399982, by rfl⟩ : syracuseStep 1866643 = 2799965) B2799965
theorem B1866659 : Blo 1865634 1866659 := bstep (se 1 (by rfl) ⟨1399994, by rfl⟩ : syracuseStep 1866659 = 2799989) B2799989
theorem B2800547 : Blo 1865634 2800547 := bstep (se 1 (by rfl) ⟨2100410, by rfl⟩ : syracuseStep 2800547 = 4200821) B4200821
theorem B4201379 : Blo 1865634 4201379 := bstep (se 1 (by rfl) ⟨3151034, by rfl⟩ : syracuseStep 4201379 = 6302069) B6302069
theorem B1866675 : Blo 1865634 1866675 := bstep (se 1 (by rfl) ⟨1400006, by rfl⟩ : syracuseStep 1866675 = 2800013) B2800013
theorem B1866691 : Blo 1865634 1866691 := bstep (se 1 (by rfl) ⟨1400018, by rfl⟩ : syracuseStep 1866691 = 2800037) B2800037
theorem B2800577 : Blo 1865634 2800577 := bstep (se 2 (by rfl) ⟨1050216, by rfl⟩ : syracuseStep 2800577 = 2100433) B2100433
theorem B1866707 : Blo 1865634 1866707 := bstep (se 1 (by rfl) ⟨1400030, by rfl⟩ : syracuseStep 1866707 = 2800061) B2800061
theorem B2800595 : Blo 1865634 2800595 := bstep (se 1 (by rfl) ⟨2100446, by rfl⟩ : syracuseStep 2800595 = 4200893) B4200893
theorem B1866723 : Blo 1865634 1866723 := bstep (se 1 (by rfl) ⟨1400042, by rfl⟩ : syracuseStep 1866723 = 2800085) B2800085
theorem B2800625 : Blo 1865634 2800625 := bstep (se 2 (by rfl) ⟨1050234, by rfl⟩ : syracuseStep 2800625 = 2100469) B2100469
theorem B1866739 : Blo 1865634 1866739 := bstep (se 1 (by rfl) ⟨1400054, by rfl⟩ : syracuseStep 1866739 = 2800109) B2800109
theorem B1866755 : Blo 1865634 1866755 := bstep (se 1 (by rfl) ⟨1400066, by rfl⟩ : syracuseStep 1866755 = 2800133) B2800133
theorem B2800643 : Blo 1865634 2800643 := bstep (se 1 (by rfl) ⟨2100482, by rfl⟩ : syracuseStep 2800643 = 4200965) B4200965
theorem B1866771 : Blo 1865634 1866771 := bstep (se 1 (by rfl) ⟨1400078, by rfl⟩ : syracuseStep 1866771 = 2800157) B2800157
theorem B2800673 : Blo 1865634 2800673 := bstep (se 2 (by rfl) ⟨1050252, by rfl⟩ : syracuseStep 2800673 = 2100505) B2100505
theorem B3193889 : Blo 1865634 3193889 := bstep (se 2 (by rfl) ⟨1197708, by rfl⟩ : syracuseStep 3193889 = 2395417) B2395417
theorem B1866787 : Blo 1865634 1866787 := bstep (se 1 (by rfl) ⟨1400090, by rfl⟩ : syracuseStep 1866787 = 2800181) B2800181
theorem B1866803 : Blo 1865634 1866803 := bstep (se 1 (by rfl) ⟨1400102, by rfl⟩ : syracuseStep 1866803 = 2800205) B2800205
theorem B2800691 : Blo 1865634 2800691 := bstep (se 1 (by rfl) ⟨2100518, by rfl⟩ : syracuseStep 2800691 = 4201037) B4201037
theorem B26901557 : Blo 1865634 26901557 := bstep (se 5 (by rfl) ⟨1261010, by rfl⟩ : syracuseStep 26901557 = 2522021) B2522021
theorem B1866819 : Blo 1865634 1866819 := bstep (se 1 (by rfl) ⟨1400114, by rfl⟩ : syracuseStep 1866819 = 2800229) B2800229
theorem B1866835 : Blo 1865634 1866835 := bstep (se 1 (by rfl) ⟨1400126, by rfl⟩ : syracuseStep 1866835 = 2800253) B2800253
theorem B2800721 : Blo 1865634 2800721 := bstep (se 2 (by rfl) ⟨1050270, by rfl⟩ : syracuseStep 2800721 = 2100541) B2100541
theorem B1866851 : Blo 1865634 1866851 := bstep (se 1 (by rfl) ⟨1400138, by rfl⟩ : syracuseStep 1866851 = 2800277) B2800277
theorem B2800739 : Blo 1865634 2800739 := bstep (se 1 (by rfl) ⟨2100554, by rfl⟩ : syracuseStep 2800739 = 4201109) B4201109
theorem B1866867 : Blo 1865634 1866867 := bstep (se 1 (by rfl) ⟨1400150, by rfl⟩ : syracuseStep 1866867 = 2800301) B2800301
theorem B2800769 : Blo 1865634 2800769 := bstep (se 2 (by rfl) ⟨1050288, by rfl⟩ : syracuseStep 2800769 = 2100577) B2100577
theorem B1866883 : Blo 1865634 1866883 := bstep (se 1 (by rfl) ⟨1400162, by rfl⟩ : syracuseStep 1866883 = 2800325) B2800325
theorem B10230917 : Blo 1865634 10230917 := bstep (se 4 (by rfl) ⟨959148, by rfl⟩ : syracuseStep 10230917 = 1918297) B1918297
theorem B1866899 : Blo 1865634 1866899 := bstep (se 1 (by rfl) ⟨1400174, by rfl⟩ : syracuseStep 1866899 = 2800349) B2800349
theorem B2800787 : Blo 1865634 2800787 := bstep (se 1 (by rfl) ⟨2100590, by rfl⟩ : syracuseStep 2800787 = 4201181) B4201181
theorem B1866915 : Blo 1865634 1866915 := bstep (se 1 (by rfl) ⟨1400186, by rfl⟩ : syracuseStep 1866915 = 2800373) B2800373
theorem B2800817 : Blo 1865634 2800817 := bstep (se 2 (by rfl) ⟨1050306, by rfl⟩ : syracuseStep 2800817 = 2100613) B2100613
theorem B1866931 : Blo 1865634 1866931 := bstep (se 1 (by rfl) ⟨1400198, by rfl⟩ : syracuseStep 1866931 = 2800397) B2800397
theorem B4201649 : Blo 1865634 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B1866947 : Blo 1865634 1866947 := bstep (se 1 (by rfl) ⟨1400210, by rfl⟩ : syracuseStep 1866947 = 2800421) B2800421
theorem B2800835 : Blo 1865634 2800835 := bstep (se 1 (by rfl) ⟨2100626, by rfl⟩ : syracuseStep 2800835 = 4201253) B4201253
theorem B4201667 : Blo 1865634 4201667 := bstep (se 1 (by rfl) ⟨3151250, by rfl⟩ : syracuseStep 4201667 = 6302501) B6302501
theorem B6298829 : Blo 1865634 6298829 := bstep (se 3 (by rfl) ⟨1181030, by rfl⟩ : syracuseStep 6298829 = 2362061) B2362061
theorem B1866963 : Blo 1865634 1866963 := bstep (se 1 (by rfl) ⟨1400222, by rfl⟩ : syracuseStep 1866963 = 2800445) B2800445
theorem B2800865 : Blo 1865634 2800865 := bstep (se 2 (by rfl) ⟨1050324, by rfl⟩ : syracuseStep 2800865 = 2100649) B2100649
theorem B1866979 : Blo 1865634 1866979 := bstep (se 1 (by rfl) ⟨1400234, by rfl⟩ : syracuseStep 1866979 = 2800469) B2800469
theorem B1866995 : Blo 1865634 1866995 := bstep (se 1 (by rfl) ⟨1400246, by rfl⟩ : syracuseStep 1866995 = 2800493) B2800493
theorem B2800883 : Blo 1865634 2800883 := bstep (se 1 (by rfl) ⟨2100662, by rfl⟩ : syracuseStep 2800883 = 4201325) B4201325
theorem B6298883 : Blo 1865634 6298883 := bstep (se 1 (by rfl) ⟨4724162, by rfl⟩ : syracuseStep 6298883 = 9448325) B9448325
theorem B1867011 : Blo 1865634 1867011 := bstep (se 1 (by rfl) ⟨1400258, by rfl⟩ : syracuseStep 1867011 = 2800517) B2800517
theorem B3988739 : Blo 1865634 3988739 := bstep (se 1 (by rfl) ⟨2991554, by rfl⟩ : syracuseStep 3988739 = 5983109) B5983109
theorem B2800913 : Blo 1865634 2800913 := bstep (se 2 (by rfl) ⟨1050342, by rfl⟩ : syracuseStep 2800913 = 2100685) B2100685
theorem B1867027 : Blo 1865634 1867027 := bstep (se 1 (by rfl) ⟨1400270, by rfl⟩ : syracuseStep 1867027 = 2800541) B2800541
theorem B1867043 : Blo 1865634 1867043 := bstep (se 1 (by rfl) ⟨1400282, by rfl⟩ : syracuseStep 1867043 = 2800565) B2800565
theorem B2800931 : Blo 1865634 2800931 := bstep (se 1 (by rfl) ⟨2100698, by rfl⟩ : syracuseStep 2800931 = 4201397) B4201397
theorem B1867059 : Blo 1865634 1867059 := bstep (se 1 (by rfl) ⟨1400294, by rfl⟩ : syracuseStep 1867059 = 2800589) B2800589
theorem B2800961 : Blo 1865634 2800961 := bstep (se 2 (by rfl) ⟨1050360, by rfl⟩ : syracuseStep 2800961 = 2100721) B2100721
theorem B1867075 : Blo 1865634 1867075 := bstep (se 1 (by rfl) ⟨1400306, by rfl⟩ : syracuseStep 1867075 = 2800613) B2800613
theorem B4726097 : Blo 1865634 4726097 := bstep (se 2 (by rfl) ⟨1772286, by rfl⟩ : syracuseStep 4726097 = 3544573) B3544573
theorem B1867091 : Blo 1865634 1867091 := bstep (se 1 (by rfl) ⟨1400318, by rfl⟩ : syracuseStep 1867091 = 2800637) B2800637
theorem B2800979 : Blo 1865634 2800979 := bstep (se 1 (by rfl) ⟨2100734, by rfl⟩ : syracuseStep 2800979 = 4201469) B4201469
theorem B7970147 : Blo 1865634 7970147 := bstep (se 1 (by rfl) ⟨5977610, by rfl⟩ : syracuseStep 7970147 = 11955221) B11955221
theorem B1867107 : Blo 1865634 1867107 := bstep (se 1 (by rfl) ⟨1400330, by rfl⟩ : syracuseStep 1867107 = 2800661) B2800661
theorem B17939825 : Blo 1865634 17939825 := bstep (se 2 (by rfl) ⟨6727434, by rfl⟩ : syracuseStep 17939825 = 13454869) B13454869
theorem B1867123 : Blo 1865634 1867123 := bstep (se 1 (by rfl) ⟨1400342, by rfl⟩ : syracuseStep 1867123 = 2800685) B2800685
theorem B2801009 : Blo 1865634 2801009 := bstep (se 2 (by rfl) ⟨1050378, by rfl⟩ : syracuseStep 2801009 = 2100757) B2100757
theorem B2522497 : Blo 1865634 2522497 := bstep (se 2 (by rfl) ⟨945936, by rfl⟩ : syracuseStep 2522497 = 1891873) B1891873
theorem B4726147 : Blo 1865634 4726147 := bstep (se 1 (by rfl) ⟨3544610, by rfl⟩ : syracuseStep 4726147 = 7089221) B7089221
theorem B1867139 : Blo 1865634 1867139 := bstep (se 1 (by rfl) ⟨1400354, by rfl⟩ : syracuseStep 1867139 = 2800709) B2800709
theorem B2801027 : Blo 1865634 2801027 := bstep (se 1 (by rfl) ⟨2100770, by rfl⟩ : syracuseStep 2801027 = 4201541) B4201541
theorem B1867155 : Blo 1865634 1867155 := bstep (se 1 (by rfl) ⟨1400366, by rfl⟩ : syracuseStep 1867155 = 2800733) B2800733
theorem B2801057 : Blo 1865634 2801057 := bstep (se 2 (by rfl) ⟨1050396, by rfl⟩ : syracuseStep 2801057 = 2100793) B2100793
theorem B3194273 : Blo 1865634 3194273 := bstep (se 2 (by rfl) ⟨1197852, by rfl⟩ : syracuseStep 3194273 = 2395705) B2395705
theorem B12942755 : Blo 1865634 12942755 := bstep (se 1 (by rfl) ⟨9707066, by rfl⟩ : syracuseStep 12942755 = 19414133) B19414133
theorem B1867171 : Blo 1865634 1867171 := bstep (se 1 (by rfl) ⟨1400378, by rfl⟩ : syracuseStep 1867171 = 2800757) B2800757
theorem B1867187 : Blo 1865634 1867187 := bstep (se 1 (by rfl) ⟨1400390, by rfl⟩ : syracuseStep 1867187 = 2800781) B2800781
theorem B2801075 : Blo 1865634 2801075 := bstep (se 1 (by rfl) ⟨2100806, by rfl⟩ : syracuseStep 2801075 = 4201613) B4201613
theorem B1867203 : Blo 1865634 1867203 := bstep (se 1 (by rfl) ⟨1400402, by rfl⟩ : syracuseStep 1867203 = 2800805) B2800805
theorem B2801105 : Blo 1865634 2801105 := bstep (se 2 (by rfl) ⟨1050414, by rfl⟩ : syracuseStep 2801105 = 2100829) B2100829
theorem B4201937 : Blo 1865634 4201937 := bstep (se 2 (by rfl) ⟨1575726, by rfl⟩ : syracuseStep 4201937 = 3151453) B3151453
theorem B2989523 : Blo 1865634 2989523 := bstep (se 1 (by rfl) ⟨2242142, by rfl⟩ : syracuseStep 2989523 = 4484285) B4484285
theorem B1867219 : Blo 1865634 1867219 := bstep (se 1 (by rfl) ⟨1400414, by rfl⟩ : syracuseStep 1867219 = 2800829) B2800829
theorem B1867235 : Blo 1865634 1867235 := bstep (se 1 (by rfl) ⟨1400426, by rfl⟩ : syracuseStep 1867235 = 2800853) B2800853
theorem B2801123 : Blo 1865634 2801123 := bstep (se 1 (by rfl) ⟨2100842, by rfl⟩ : syracuseStep 2801123 = 4201685) B4201685
theorem B4201955 : Blo 1865634 4201955 := bstep (se 1 (by rfl) ⟨3151466, by rfl⟩ : syracuseStep 4201955 = 6302933) B6302933
theorem B2522611 : Blo 1865634 2522611 := bstep (se 1 (by rfl) ⟨1891958, by rfl⟩ : syracuseStep 2522611 = 3783917) B3783917
theorem B1867251 : Blo 1865634 1867251 := bstep (se 1 (by rfl) ⟨1400438, by rfl⟩ : syracuseStep 1867251 = 2800877) B2800877
theorem B2801153 : Blo 1865634 2801153 := bstep (se 2 (by rfl) ⟨1050432, by rfl⟩ : syracuseStep 2801153 = 2100865) B2100865
theorem B1867267 : Blo 1865634 1867267 := bstep (se 1 (by rfl) ⟨1400450, by rfl⟩ : syracuseStep 1867267 = 2800901) B2800901
theorem B6299153 : Blo 1865634 6299153 := bstep (se 2 (by rfl) ⟨2362182, by rfl⟩ : syracuseStep 6299153 = 4724365) B4724365
theorem B4726289 : Blo 1865634 4726289 := bstep (se 2 (by rfl) ⟨1772358, by rfl⟩ : syracuseStep 4726289 = 3544717) B3544717
theorem B1867283 : Blo 1865634 1867283 := bstep (se 1 (by rfl) ⟨1400462, by rfl⟩ : syracuseStep 1867283 = 2800925) B2800925
theorem B2801171 : Blo 1865634 2801171 := bstep (se 1 (by rfl) ⟨2100878, by rfl⟩ : syracuseStep 2801171 = 4201757) B4201757
theorem B2522659 : Blo 1865634 2522659 := bstep (se 1 (by rfl) ⟨1891994, by rfl⟩ : syracuseStep 2522659 = 3783989) B3783989
theorem B5316131 : Blo 1865634 5316131 := bstep (se 1 (by rfl) ⟨3987098, by rfl⟩ : syracuseStep 5316131 = 7974197) B7974197
theorem B1867299 : Blo 1865634 1867299 := bstep (se 1 (by rfl) ⟨1400474, by rfl⟩ : syracuseStep 1867299 = 2800949) B2800949
theorem B2801201 : Blo 1865634 2801201 := bstep (se 2 (by rfl) ⟨1050450, by rfl⟩ : syracuseStep 2801201 = 2100901) B2100901
theorem B1867315 : Blo 1865634 1867315 := bstep (se 1 (by rfl) ⟨1400486, by rfl⟩ : syracuseStep 1867315 = 2800973) B2800973
theorem B1867331 : Blo 1865634 1867331 := bstep (se 1 (by rfl) ⟨1400498, by rfl⟩ : syracuseStep 1867331 = 2800997) B2800997
theorem B2801219 : Blo 1865634 2801219 := bstep (se 1 (by rfl) ⟨2100914, by rfl⟩ : syracuseStep 2801219 = 4201829) B4201829
theorem B1867347 : Blo 1865634 1867347 := bstep (se 1 (by rfl) ⟨1400510, by rfl⟩ : syracuseStep 1867347 = 2801021) B2801021
theorem B2801249 : Blo 1865634 2801249 := bstep (se 2 (by rfl) ⟨1050468, by rfl⟩ : syracuseStep 2801249 = 2100937) B2100937
theorem B1867363 : Blo 1865634 1867363 := bstep (se 1 (by rfl) ⟨1400522, by rfl⟩ : syracuseStep 1867363 = 2801045) B2801045
theorem B1867379 : Blo 1865634 1867379 := bstep (se 1 (by rfl) ⟨1400534, by rfl⟩ : syracuseStep 1867379 = 2801069) B2801069
theorem B2801267 : Blo 1865634 2801267 := bstep (se 1 (by rfl) ⟨2100950, by rfl⟩ : syracuseStep 2801267 = 4201901) B4201901
theorem B1867395 : Blo 1865634 1867395 := bstep (se 1 (by rfl) ⟨1400546, by rfl⟩ : syracuseStep 1867395 = 2801093) B2801093
theorem B40345229 : Blo 1865634 40345229 := bstep (se 3 (by rfl) ⟨7564730, by rfl⟩ : syracuseStep 40345229 = 15129461) B15129461
theorem B2801297 : Blo 1865634 2801297 := bstep (se 2 (by rfl) ⟨1050486, by rfl⟩ : syracuseStep 2801297 = 2100973) B2100973
theorem B1867411 : Blo 1865634 1867411 := bstep (se 1 (by rfl) ⟨1400558, by rfl⟩ : syracuseStep 1867411 = 2801117) B2801117
theorem B11509411 : Blo 1865634 11509411 := bstep (se 1 (by rfl) ⟨8632058, by rfl⟩ : syracuseStep 11509411 = 17264117) B17264117
theorem B1867427 : Blo 1865634 1867427 := bstep (se 1 (by rfl) ⟨1400570, by rfl⟩ : syracuseStep 1867427 = 2801141) B2801141
theorem B2801315 : Blo 1865634 2801315 := bstep (se 1 (by rfl) ⟨2100986, by rfl⟩ : syracuseStep 2801315 = 4201973) B4201973
theorem B1867443 : Blo 1865634 1867443 := bstep (se 1 (by rfl) ⟨1400582, by rfl⟩ : syracuseStep 1867443 = 2801165) B2801165
theorem B2801345 : Blo 1865634 2801345 := bstep (se 2 (by rfl) ⟨1050504, by rfl⟩ : syracuseStep 2801345 = 2101009) B2101009
theorem B1867459 : Blo 1865634 1867459 := bstep (se 1 (by rfl) ⟨1400594, by rfl⟩ : syracuseStep 1867459 = 2801189) B2801189
theorem B1867475 : Blo 1865634 1867475 := bstep (se 1 (by rfl) ⟨1400606, by rfl⟩ : syracuseStep 1867475 = 2801213) B2801213
theorem B2801363 : Blo 1865634 2801363 := bstep (se 1 (by rfl) ⟨2101022, by rfl⟩ : syracuseStep 2801363 = 4202045) B4202045
theorem B1867491 : Blo 1865634 1867491 := bstep (se 1 (by rfl) ⟨1400618, by rfl⟩ : syracuseStep 1867491 = 2801237) B2801237
theorem B2801393 : Blo 1865634 2801393 := bstep (se 2 (by rfl) ⟨1050522, by rfl⟩ : syracuseStep 2801393 = 2101045) B2101045
theorem B1867507 : Blo 1865634 1867507 := bstep (se 1 (by rfl) ⟨1400630, by rfl⟩ : syracuseStep 1867507 = 2801261) B2801261
theorem B4546307 : Blo 1865634 4546307 := bstep (se 1 (by rfl) ⟨3409730, by rfl⟩ : syracuseStep 4546307 = 6819461) B6819461
theorem B1867523 : Blo 1865634 1867523 := bstep (se 1 (by rfl) ⟨1400642, by rfl⟩ : syracuseStep 1867523 = 2801285) B2801285
theorem B2801411 : Blo 1865634 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B1867539 : Blo 1865634 1867539 := bstep (se 1 (by rfl) ⟨1400654, by rfl⟩ : syracuseStep 1867539 = 2801309) B2801309
theorem B2801441 : Blo 1865634 2801441 := bstep (se 2 (by rfl) ⟨1050540, by rfl⟩ : syracuseStep 2801441 = 2101081) B2101081
theorem B9453347 : Blo 1865634 9453347 := bstep (se 1 (by rfl) ⟨7090010, by rfl⟩ : syracuseStep 9453347 = 14180021) B14180021
theorem B1867555 : Blo 1865634 1867555 := bstep (se 1 (by rfl) ⟨1400666, by rfl⟩ : syracuseStep 1867555 = 2801333) B2801333
theorem B1867571 : Blo 1865634 1867571 := bstep (se 1 (by rfl) ⟨1400678, by rfl⟩ : syracuseStep 1867571 = 2801357) B2801357
theorem B1867587 : Blo 1865634 1867587 := bstep (se 1 (by rfl) ⟨1400690, by rfl⟩ : syracuseStep 1867587 = 2801381) B2801381
theorem B5046097 : Blo 1865634 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B1867603 : Blo 1865634 1867603 := bstep (se 1 (by rfl) ⟨1400702, by rfl⟩ : syracuseStep 1867603 = 2801405) B2801405
theorem B1867619 : Blo 1865634 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B5316461 : Blo 1865634 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B6061937 : Blo 1865634 6061937 := bstep (se 2 (by rfl) ⟨2273226, by rfl⟩ : syracuseStep 6061937 = 4546453) B4546453
theorem B7085987 : Blo 1865634 7085987 := bstep (se 1 (by rfl) ⟨5314490, by rfl⟩ : syracuseStep 7085987 = 10628981) B10628981
theorem B10092451 : Blo 1865634 10092451 := bstep (se 1 (by rfl) ⟨7569338, by rfl⟩ : syracuseStep 10092451 = 15138677) B15138677
theorem B5390243 : Blo 1865634 5390243 := bstep (se 1 (by rfl) ⟨4042682, by rfl⟩ : syracuseStep 5390243 = 8085365) B8085365
theorem B7086001 : Blo 1865634 7086001 := bstep (se 2 (by rfl) ⟨2657250, by rfl⟩ : syracuseStep 7086001 = 5314501) B5314501
theorem B5316529 : Blo 1865634 5316529 := bstep (se 2 (by rfl) ⟨1993698, by rfl⟩ : syracuseStep 5316529 = 3987397) B3987397
theorem B15941933 : Blo 1865634 15941933 := bstep (se 3 (by rfl) ⟨2989112, by rfl⟩ : syracuseStep 15941933 = 5978225) B5978225
theorem B7086487 : Blo 1865634 7086487 := bstep (se 1 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 7086487 = 10629731) B10629731
theorem B7569857 : Blo 1865634 7569857 := bstep (se 2 (by rfl) ⟨2838696, by rfl⟩ : syracuseStep 7569857 = 5677393) B5677393
theorem B6300125 : Blo 1865634 6300125 := bstep (se 3 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 6300125 = 2362547) B2362547
theorem B1892951 : Blo 1865634 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B7971479 : Blo 1865634 7971479 := bstep (se 1 (by rfl) ⟨5978609, by rfl⟩ : syracuseStep 7971479 = 11957219) B11957219
theorem B2523865 : Blo 1865634 2523865 := bstep (se 2 (by rfl) ⟨946449, by rfl⟩ : syracuseStep 2523865 = 1892899) B1892899
theorem B9446219 : Blo 1865634 9446219 := bstep (se 1 (by rfl) ⟨7084664, by rfl⟩ : syracuseStep 9446219 = 14169329) B14169329
theorem B10626065 : Blo 1865634 10626065 := bstep (se 2 (by rfl) ⟨3984774, by rfl⟩ : syracuseStep 10626065 = 7969549) B7969549
theorem B9577547 : Blo 1865634 9577547 := bstep (se 1 (by rfl) ⟨7183160, by rfl⟩ : syracuseStep 9577547 = 14366321) B14366321
theorem B7087277 : Blo 1865634 7087277 := bstep (se 3 (by rfl) ⟨1328864, by rfl⟩ : syracuseStep 7087277 = 2657729) B2657729
theorem B11961523 : Blo 1865634 11961523 := bstep (se 1 (by rfl) ⟨8971142, by rfl⟩ : syracuseStep 11961523 = 17942285) B17942285
theorem B5981377 : Blo 1865634 5981377 := bstep (se 2 (by rfl) ⟨2243016, by rfl⟩ : syracuseStep 5981377 = 4486033) B4486033
theorem B10634561 : Blo 1865634 10634561 := bstep (se 2 (by rfl) ⟨3987960, by rfl⟩ : syracuseStep 10634561 = 7975921) B7975921
theorem B6817117 : Blo 1865634 6817117 := bstep (se 3 (by rfl) ⟨1278209, by rfl⟩ : syracuseStep 6817117 = 2556419) B2556419
theorem B13460867 : Blo 1865634 13460867 := bstep (se 1 (by rfl) ⟨10095650, by rfl⟩ : syracuseStep 13460867 = 20191301) B20191301
theorem B6817355 : Blo 1865634 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B6301259 : Blo 1865634 6301259 := bstep (se 1 (by rfl) ⟨4725944, by rfl⟩ : syracuseStep 6301259 = 9451889) B9451889
theorem B5318237 : Blo 1865634 5318237 := bstep (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) B1994339
theorem B107587277 : Blo 1865634 107587277 := bstep (se 3 (by rfl) ⟨20172614, by rfl⟩ : syracuseStep 107587277 = 40345229) B40345229
theorem B2098903 : Blo 1865634 2098903 := bstep (se 1 (by rfl) ⟨1574177, by rfl⟩ : syracuseStep 2098903 = 3148355) B3148355
theorem B4482881 : Blo 1865634 4482881 := bstep (se 2 (by rfl) ⟨1681080, by rfl⟩ : syracuseStep 4482881 = 3362161) B3362161
theorem B6301529 : Blo 1865634 6301529 := bstep (se 2 (by rfl) ⟨2363073, by rfl⟩ : syracuseStep 6301529 = 4726147) B4726147
theorem B20186981 : Blo 1865634 20186981 := bstep (se 4 (by rfl) ⟨1892529, by rfl⟩ : syracuseStep 20186981 = 3785059) B3785059
theorem B2099083 : Blo 1865634 2099083 := bstep (se 1 (by rfl) ⟨1574312, by rfl⟩ : syracuseStep 2099083 = 3148625) B3148625
theorem B2099191 : Blo 1865634 2099191 := bstep (se 1 (by rfl) ⟨1574393, by rfl⟩ : syracuseStep 2099191 = 3148787) B3148787
theorem B25880593 : Blo 1865634 25880593 := bstep (se 2 (by rfl) ⟨9705222, by rfl⟩ : syracuseStep 25880593 = 19410445) B19410445
theorem B17934371 : Blo 1865634 17934371 := bstep (se 1 (by rfl) ⟨13450778, by rfl⟩ : syracuseStep 17934371 = 26901557) B26901557
theorem B2099371 : Blo 1865634 2099371 := bstep (se 1 (by rfl) ⟨1574528, by rfl⟩ : syracuseStep 2099371 = 3149057) B3149057
theorem B2656471 : Blo 1865634 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B15345881 : Blo 1865634 15345881 := bstep (se 2 (by rfl) ⟨5754705, by rfl⟩ : syracuseStep 15345881 = 11509411) B11509411
theorem B8628503 : Blo 1865634 8628503 := bstep (se 1 (by rfl) ⟨6471377, by rfl⟩ : syracuseStep 8628503 = 12942755) B12942755
theorem B2099479 : Blo 1865634 2099479 := bstep (se 1 (by rfl) ⟨1574609, by rfl⟩ : syracuseStep 2099479 = 3149219) B3149219
theorem B16165165 : Blo 1865634 16165165 := bstep (se 3 (by rfl) ⟨3030968, by rfl⟩ : syracuseStep 16165165 = 6061937) B6061937
theorem B1993015 : Blo 1865634 1993015 := bstep (se 1 (by rfl) ⟨1494761, by rfl⟩ : syracuseStep 1993015 = 2989523) B2989523
theorem B6728129 : Blo 1865634 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B2099659 : Blo 1865634 2099659 := bstep (se 1 (by rfl) ⟨1574744, by rfl⟩ : syracuseStep 2099659 = 3149489) B3149489
theorem B6302231 : Blo 1865634 6302231 := bstep (se 1 (by rfl) ⟨4726673, by rfl⟩ : syracuseStep 6302231 = 9453347) B9453347
theorem B2099767 : Blo 1865634 2099767 := bstep (se 1 (by rfl) ⟨1574825, by rfl⟩ : syracuseStep 2099767 = 3149651) B3149651
theorem B9448001 : Blo 1865634 9448001 := bstep (se 2 (by rfl) ⟨3543000, by rfl⟩ : syracuseStep 9448001 = 7086001) B7086001
theorem B7088705 : Blo 1865634 7088705 := bstep (se 2 (by rfl) ⟨2658264, by rfl⟩ : syracuseStep 7088705 = 5316529) B5316529
theorem B3148375 : Blo 1865634 3148375 := bstep (se 1 (by rfl) ⟨2361281, by rfl⟩ : syracuseStep 3148375 = 4722563) B4722563
theorem B15944323 : Blo 1865634 15944323 := bstep (se 1 (by rfl) ⟨11958242, by rfl⟩ : syracuseStep 15944323 = 23916485) B23916485
theorem B11963011 : Blo 1865634 11963011 := bstep (se 1 (by rfl) ⟨8972258, by rfl⟩ : syracuseStep 11963011 = 17944517) B17944517
theorem B2099947 : Blo 1865634 2099947 := bstep (se 1 (by rfl) ⟨1574960, by rfl⟩ : syracuseStep 2099947 = 3149921) B3149921
theorem B2100055 : Blo 1865634 2100055 := bstep (se 1 (by rfl) ⟨1575041, by rfl⟩ : syracuseStep 2100055 = 3150083) B3150083
theorem B80767961 : Blo 1865634 80767961 := bstep (se 2 (by rfl) ⟨30287985, by rfl⟩ : syracuseStep 80767961 = 60575971) B60575971
theorem B16157701 : Blo 1865634 16157701 := bstep (se 4 (by rfl) ⟨1514784, by rfl⟩ : syracuseStep 16157701 = 3029569) B3029569
theorem B2100235 : Blo 1865634 2100235 := bstep (se 1 (by rfl) ⟨1575176, by rfl⟩ : syracuseStep 2100235 = 3150353) B3150353
theorem B7973939 : Blo 1865634 7973939 := bstep (se 1 (by rfl) ⟨5980454, by rfl⟩ : syracuseStep 7973939 = 11960909) B11960909
theorem B6302771 : Blo 1865634 6302771 := bstep (se 1 (by rfl) ⟨4727078, by rfl⟩ : syracuseStep 6302771 = 9454157) B9454157
theorem B3542105 : Blo 1865634 3542105 := bstep (se 2 (by rfl) ⟨1328289, by rfl⟩ : syracuseStep 3542105 = 2656579) B2656579
theorem B2100343 : Blo 1865634 2100343 := bstep (se 1 (by rfl) ⟨1575257, by rfl⟩ : syracuseStep 2100343 = 3150515) B3150515
theorem B3149003 : Blo 1865634 3149003 := bstep (se 1 (by rfl) ⟨2361752, by rfl⟩ : syracuseStep 3149003 = 4723505) B4723505
theorem B6728921 : Blo 1865634 6728921 := bstep (se 2 (by rfl) ⟨2523345, by rfl⟩ : syracuseStep 6728921 = 5046691) B5046691
theorem B2100523 : Blo 1865634 2100523 := bstep (se 1 (by rfl) ⟨1575392, by rfl⟩ : syracuseStep 2100523 = 3150785) B3150785
theorem B6303041 : Blo 1865634 6303041 := bstep (se 2 (by rfl) ⟨2363640, by rfl⟩ : syracuseStep 6303041 = 4727281) B4727281
theorem B4197707 : Blo 1865634 4197707 := bstep (se 1 (by rfl) ⟨3148280, by rfl⟩ : syracuseStep 4197707 = 6296561) B6296561
theorem B3149131 : Blo 1865634 3149131 := bstep (se 1 (by rfl) ⟨2361848, by rfl⟩ : syracuseStep 3149131 = 4723697) B4723697
theorem B2362699 : Blo 1865634 2362699 := bstep (se 1 (by rfl) ⟨1772024, by rfl⟩ : syracuseStep 2362699 = 3544049) B3544049
theorem B4197761 : Blo 1865634 4197761 := bstep (se 2 (by rfl) ⟨1574160, by rfl⟩ : syracuseStep 4197761 = 3148321) B3148321
theorem B2100631 : Blo 1865634 2100631 := bstep (se 1 (by rfl) ⟨1575473, by rfl⟩ : syracuseStep 2100631 = 3150947) B3150947
theorem B3149273 : Blo 1865634 3149273 := bstep (se 2 (by rfl) ⟨1180977, by rfl⟩ : syracuseStep 3149273 = 2361955) B2361955
theorem B3362291 : Blo 1865634 3362291 := bstep (se 1 (by rfl) ⟨2521718, by rfl⟩ : syracuseStep 3362291 = 5043437) B5043437
theorem B3362305 : Blo 1865634 3362305 := bstep (se 2 (by rfl) ⟨1260864, by rfl⟩ : syracuseStep 3362305 = 2521729) B2521729
theorem B15945281 : Blo 1865634 15945281 := bstep (se 2 (by rfl) ⟨5979480, by rfl⟩ : syracuseStep 15945281 = 11958961) B11958961
theorem B6729281 : Blo 1865634 6729281 := bstep (se 2 (by rfl) ⟨2523480, by rfl⟩ : syracuseStep 6729281 = 5046961) B5046961
theorem B2100811 : Blo 1865634 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B4197977 : Blo 1865634 4197977 := bstep (se 2 (by rfl) ⟨1574241, by rfl⟩ : syracuseStep 4197977 = 3148483) B3148483
theorem B3149401 : Blo 1865634 3149401 := bstep (se 2 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 3149401 = 2362051) B2362051
theorem B4198067 : Blo 1865634 4198067 := bstep (se 1 (by rfl) ⟨3148550, by rfl⟩ : syracuseStep 4198067 = 6297101) B6297101
theorem B2100919 : Blo 1865634 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B4198103 : Blo 1865634 4198103 := bstep (se 1 (by rfl) ⟨3148577, by rfl⟩ : syracuseStep 4198103 = 6297155) B6297155
theorem B3542849 : Blo 1865634 3542849 := bstep (se 2 (by rfl) ⟨1328568, by rfl⟩ : syracuseStep 3542849 = 2657137) B2657137
theorem B4198283 : Blo 1865634 4198283 := bstep (se 1 (by rfl) ⟨3148712, by rfl⟩ : syracuseStep 4198283 = 6297425) B6297425
theorem B4722583 : Blo 1865634 4722583 := bstep (se 1 (by rfl) ⟨3541937, by rfl⟩ : syracuseStep 4722583 = 7083875) B7083875
theorem B4198337 : Blo 1865634 4198337 := bstep (se 2 (by rfl) ⟨1574376, by rfl⟩ : syracuseStep 4198337 = 3148753) B3148753
theorem B12947473 : Blo 1865634 12947473 := bstep (se 2 (by rfl) ⟨4855302, by rfl⟩ : syracuseStep 12947473 = 9710605) B9710605
theorem B7090193 : Blo 1865634 7090193 := bstep (se 2 (by rfl) ⟨2658822, by rfl⟩ : syracuseStep 7090193 = 5317645) B5317645
theorem B109129781 : Blo 1865634 109129781 := bstep (se 5 (by rfl) ⟨5115458, by rfl⟩ : syracuseStep 109129781 = 10230917) B10230917
theorem B3543115 : Blo 1865634 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B3149975 : Blo 1865634 3149975 := bstep (se 1 (by rfl) ⟨2362481, by rfl⟩ : syracuseStep 3149975 = 4724963) B4724963
theorem B4198553 : Blo 1865634 4198553 := bstep (se 2 (by rfl) ⟨1574457, by rfl⟩ : syracuseStep 4198553 = 3148915) B3148915
theorem B8515763 : Blo 1865634 8515763 := bstep (se 1 (by rfl) ⟨6386822, by rfl⟩ : syracuseStep 8515763 = 12773645) B12773645
theorem B4042955 : Blo 1865634 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B2658521 : Blo 1865634 2658521 := bstep (se 2 (by rfl) ⟨996945, by rfl⟩ : syracuseStep 2658521 = 1993891) B1993891
theorem B4198643 : Blo 1865634 4198643 := bstep (se 1 (by rfl) ⟨3148982, by rfl⟩ : syracuseStep 4198643 = 6297965) B6297965
theorem B4198679 : Blo 1865634 4198679 := bstep (se 1 (by rfl) ⟨3149009, by rfl⟩ : syracuseStep 4198679 = 6298019) B6298019
theorem B3150103 : Blo 1865634 3150103 := bstep (se 1 (by rfl) ⟨2362577, by rfl⟩ : syracuseStep 3150103 = 4725155) B4725155
theorem B2363671 : Blo 1865634 2363671 := bstep (se 1 (by rfl) ⟨1772753, by rfl⟩ : syracuseStep 2363671 = 3545507) B3545507
theorem B4723019 : Blo 1865634 4723019 := bstep (se 1 (by rfl) ⟨3542264, by rfl⟩ : syracuseStep 4723019 = 7084529) B7084529
theorem B5312861 : Blo 1865634 5312861 := bstep (se 3 (by rfl) ⟨996161, by rfl⟩ : syracuseStep 5312861 = 1992323) B1992323
theorem B15765853 : Blo 1865634 15765853 := bstep (se 3 (by rfl) ⟨2956097, by rfl⟩ : syracuseStep 15765853 = 5912195) B5912195
theorem B28733797 : Blo 1865634 28733797 := bstep (se 4 (by rfl) ⟨2693793, by rfl⟩ : syracuseStep 28733797 = 5387587) B5387587
theorem B4198859 : Blo 1865634 4198859 := bstep (se 1 (by rfl) ⟨3149144, by rfl⟩ : syracuseStep 4198859 = 6298289) B6298289
theorem B9449945 : Blo 1865634 9449945 := bstep (se 2 (by rfl) ⟨3543729, by rfl⟩ : syracuseStep 9449945 = 7087459) B7087459
theorem B7090649 : Blo 1865634 7090649 := bstep (se 2 (by rfl) ⟨2658993, by rfl⟩ : syracuseStep 7090649 = 5317987) B5317987
theorem B4198913 : Blo 1865634 4198913 := bstep (se 2 (by rfl) ⟨1574592, by rfl⟩ : syracuseStep 4198913 = 3149185) B3149185
theorem B3363329 : Blo 1865634 3363329 := bstep (se 2 (by rfl) ⟨1261248, by rfl⟩ : syracuseStep 3363329 = 2522497) B2522497
theorem B3543563 : Blo 1865634 3543563 := bstep (se 1 (by rfl) ⟨2657672, by rfl⟩ : syracuseStep 3543563 = 5315345) B5315345
theorem B5313089 : Blo 1865634 5313089 := bstep (se 2 (by rfl) ⟨1992408, by rfl⟩ : syracuseStep 5313089 = 3984817) B3984817
theorem B8516161 : Blo 1865634 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B13447781 : Blo 1865634 13447781 := bstep (se 4 (by rfl) ⟨1260729, by rfl⟩ : syracuseStep 13447781 = 2521459) B2521459
theorem B3363481 : Blo 1865634 3363481 := bstep (se 2 (by rfl) ⟨1261305, by rfl⟩ : syracuseStep 3363481 = 2522611) B2522611
theorem B7090861 : Blo 1865634 7090861 := bstep (se 3 (by rfl) ⟨1329536, by rfl⟩ : syracuseStep 7090861 = 2659073) B2659073
theorem B4723393 : Blo 1865634 4723393 := bstep (se 2 (by rfl) ⟨1771272, by rfl⟩ : syracuseStep 4723393 = 3542545) B3542545
theorem B3543745 : Blo 1865634 3543745 := bstep (se 2 (by rfl) ⟨1328904, by rfl⟩ : syracuseStep 3543745 = 2657809) B2657809
theorem B4199129 : Blo 1865634 4199129 := bstep (se 2 (by rfl) ⟨1574673, by rfl⟩ : syracuseStep 4199129 = 3149347) B3149347
theorem B3363545 : Blo 1865634 3363545 := bstep (se 2 (by rfl) ⟨1261329, by rfl⟩ : syracuseStep 3363545 = 2522659) B2522659
theorem B15938309 : Blo 1865634 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B4199219 : Blo 1865634 4199219 := bstep (se 1 (by rfl) ⟨3149414, by rfl⟩ : syracuseStep 4199219 = 6298829) B6298829
theorem B4199255 : Blo 1865634 4199255 := bstep (se 1 (by rfl) ⟨3149441, by rfl⟩ : syracuseStep 4199255 = 6298883) B6298883
theorem B2659159 : Blo 1865634 2659159 := bstep (se 1 (by rfl) ⟨1994369, by rfl⟩ : syracuseStep 2659159 = 3988739) B3988739
theorem B3150731 : Blo 1865634 3150731 := bstep (se 1 (by rfl) ⟨2363048, by rfl⟩ : syracuseStep 3150731 = 4726097) B4726097
theorem B5313431 : Blo 1865634 5313431 := bstep (se 1 (by rfl) ⟨3985073, by rfl⟩ : syracuseStep 5313431 = 7970147) B7970147
theorem B2798489 : Blo 1865634 2798489 := bstep (se 2 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 2798489 = 2098867) B2098867
theorem B7975853 : Blo 1865634 7975853 := bstep (se 3 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 7975853 = 2990945) B2990945
theorem B7091165 : Blo 1865634 7091165 := bstep (se 3 (by rfl) ⟨1329593, by rfl⟩ : syracuseStep 7091165 = 2659187) B2659187
theorem B2798603 : Blo 1865634 2798603 := bstep (se 1 (by rfl) ⟨2098952, by rfl⟩ : syracuseStep 2798603 = 4197905) B4197905
theorem B4199435 : Blo 1865634 4199435 := bstep (se 1 (by rfl) ⟨3149576, by rfl⟩ : syracuseStep 4199435 = 6299153) B6299153
theorem B3150859 : Blo 1865634 3150859 := bstep (se 1 (by rfl) ⟨2363144, by rfl⟩ : syracuseStep 3150859 = 4726289) B4726289
theorem B2798615 : Blo 1865634 2798615 := bstep (se 1 (by rfl) ⟨2098961, by rfl⟩ : syracuseStep 2798615 = 4197923) B4197923
theorem B3544087 : Blo 1865634 3544087 := bstep (se 1 (by rfl) ⟨2658065, by rfl⟩ : syracuseStep 3544087 = 5316131) B5316131
theorem B4199489 : Blo 1865634 4199489 := bstep (se 2 (by rfl) ⟨1574808, by rfl⟩ : syracuseStep 4199489 = 3149617) B3149617
theorem B13644875 : Blo 1865634 13644875 := bstep (se 1 (by rfl) ⟨10233656, by rfl⟩ : syracuseStep 13644875 = 20467313) B20467313
theorem B2798681 : Blo 1865634 2798681 := bstep (se 2 (by rfl) ⟨1049505, by rfl⟩ : syracuseStep 2798681 = 2099011) B2099011
theorem B6296669 : Blo 1865634 6296669 := bstep (se 3 (by rfl) ⟨1180625, by rfl⟩ : syracuseStep 6296669 = 2361251) B2361251
theorem B3151001 : Blo 1865634 3151001 := bstep (se 2 (by rfl) ⟨1181625, by rfl⟩ : syracuseStep 3151001 = 2363251) B2363251
theorem B2798795 : Blo 1865634 2798795 := bstep (se 1 (by rfl) ⟨2099096, by rfl⟩ : syracuseStep 2798795 = 4198193) B4198193
theorem B2798807 : Blo 1865634 2798807 := bstep (se 1 (by rfl) ⟨2099105, by rfl⟩ : syracuseStep 2798807 = 4198211) B4198211
theorem B13456601 : Blo 1865634 13456601 := bstep (se 2 (by rfl) ⟨5046225, by rfl⟩ : syracuseStep 13456601 = 10092451) B10092451
theorem B3544307 : Blo 1865634 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B7976195 : Blo 1865634 7976195 := bstep (se 1 (by rfl) ⟨5982146, by rfl⟩ : syracuseStep 7976195 = 11964293) B11964293
theorem B4723991 : Blo 1865634 4723991 := bstep (se 1 (by rfl) ⟨3542993, by rfl⟩ : syracuseStep 4723991 = 7085987) B7085987
theorem B3593495 : Blo 1865634 3593495 := bstep (se 1 (by rfl) ⟨2695121, by rfl⟩ : syracuseStep 3593495 = 5390243) B5390243
theorem B2798873 : Blo 1865634 2798873 := bstep (se 2 (by rfl) ⟨1049577, by rfl⟩ : syracuseStep 2798873 = 2099155) B2099155
theorem B4199705 : Blo 1865634 4199705 := bstep (se 2 (by rfl) ⟨1574889, by rfl⟩ : syracuseStep 4199705 = 3149779) B3149779
theorem B3151129 : Blo 1865634 3151129 := bstep (se 2 (by rfl) ⟨1181673, by rfl⟩ : syracuseStep 3151129 = 2363347) B2363347
theorem B15545675 : Blo 1865634 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B4199795 : Blo 1865634 4199795 := bstep (se 1 (by rfl) ⟨3149846, by rfl⟩ : syracuseStep 4199795 = 6299693) B6299693
theorem B2798987 : Blo 1865634 2798987 := bstep (se 1 (by rfl) ⟨2099240, by rfl⟩ : syracuseStep 2798987 = 4198481) B4198481
theorem B2798999 : Blo 1865634 2798999 := bstep (se 1 (by rfl) ⟨2099249, by rfl⟩ : syracuseStep 2798999 = 4198499) B4198499
theorem B7566743 : Blo 1865634 7566743 := bstep (se 1 (by rfl) ⟨5675057, by rfl⟩ : syracuseStep 7566743 = 11350115) B11350115
theorem B4199831 : Blo 1865634 4199831 := bstep (se 1 (by rfl) ⟨3149873, by rfl⟩ : syracuseStep 4199831 = 6299747) B6299747
theorem B8517037 : Blo 1865634 8517037 := bstep (se 3 (by rfl) ⟨1596944, by rfl⟩ : syracuseStep 8517037 = 3193889) B3193889
theorem B3986867 : Blo 1865634 3986867 := bstep (se 1 (by rfl) ⟨2990150, by rfl⟩ : syracuseStep 3986867 = 5980301) B5980301
theorem B2799065 : Blo 1865634 2799065 := bstep (se 2 (by rfl) ⟨1049649, by rfl⟩ : syracuseStep 2799065 = 2099299) B2099299
theorem B3544535 : Blo 1865634 3544535 := bstep (se 1 (by rfl) ⟨2658401, by rfl⟩ : syracuseStep 3544535 = 5316803) B5316803
theorem B17266181 : Blo 1865634 17266181 := bstep (se 4 (by rfl) ⟨1618704, by rfl⟩ : syracuseStep 17266181 = 3237409) B3237409
theorem B2799179 : Blo 1865634 2799179 := bstep (se 1 (by rfl) ⟨2099384, by rfl⟩ : syracuseStep 2799179 = 4198769) B4198769
theorem B4200011 : Blo 1865634 4200011 := bstep (se 1 (by rfl) ⟨3150008, by rfl⟩ : syracuseStep 4200011 = 6300017) B6300017
theorem B2799191 : Blo 1865634 2799191 := bstep (se 1 (by rfl) ⟨2099393, by rfl⟩ : syracuseStep 2799191 = 4198787) B4198787
theorem B4486745 : Blo 1865634 4486745 := bstep (se 2 (by rfl) ⟨1682529, by rfl⟩ : syracuseStep 4486745 = 3365059) B3365059
theorem B4200065 : Blo 1865634 4200065 := bstep (se 2 (by rfl) ⟨1575024, by rfl⟩ : syracuseStep 4200065 = 3150049) B3150049
theorem B10090115 : Blo 1865634 10090115 := bstep (se 1 (by rfl) ⟨7567586, by rfl⟩ : syracuseStep 10090115 = 15135173) B15135173
theorem B2799257 : Blo 1865634 2799257 := bstep (se 2 (by rfl) ⟨1049721, by rfl⟩ : syracuseStep 2799257 = 2099443) B2099443
theorem B3544793 : Blo 1865634 3544793 := bstep (se 2 (by rfl) ⟨1329297, by rfl⟩ : syracuseStep 3544793 = 2658595) B2658595
theorem B2799371 : Blo 1865634 2799371 := bstep (se 1 (by rfl) ⟨2099528, by rfl⟩ : syracuseStep 2799371 = 4199057) B4199057
theorem B4544279 : Blo 1865634 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B2799383 : Blo 1865634 2799383 := bstep (se 1 (by rfl) ⟨2099537, by rfl⟩ : syracuseStep 2799383 = 4199075) B4199075
theorem B2799449 : Blo 1865634 2799449 := bstep (se 2 (by rfl) ⟨1049793, by rfl⟩ : syracuseStep 2799449 = 2099587) B2099587
theorem B4200281 : Blo 1865634 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B8083289 : Blo 1865634 8083289 := bstep (se 2 (by rfl) ⟨3031233, by rfl⟩ : syracuseStep 8083289 = 6062467) B6062467
theorem B1865643 : Blo 1865634 1865643 := bstep (se 1 (by rfl) ⟨1399232, by rfl⟩ : syracuseStep 1865643 = 2798465) B2798465
theorem B4200371 : Blo 1865634 4200371 := bstep (se 1 (by rfl) ⟨3150278, by rfl⟩ : syracuseStep 4200371 = 6300557) B6300557
theorem B25556915 : Blo 1865634 25556915 := bstep (se 1 (by rfl) ⟨19167686, by rfl⟩ : syracuseStep 25556915 = 38335373) B38335373
theorem B1865655 : Blo 1865634 1865655 := bstep (se 1 (by rfl) ⟨1399241, by rfl⟩ : syracuseStep 1865655 = 2798483) B2798483
theorem B1865675 : Blo 1865634 1865675 := bstep (se 1 (by rfl) ⟨1399256, by rfl⟩ : syracuseStep 1865675 = 2798513) B2798513
theorem B2799563 : Blo 1865634 2799563 := bstep (se 1 (by rfl) ⟨2099672, by rfl⟩ : syracuseStep 2799563 = 4199345) B4199345
theorem B1865687 : Blo 1865634 1865687 := bstep (se 1 (by rfl) ⟨1399265, by rfl⟩ : syracuseStep 1865687 = 2798531) B2798531
theorem B2799575 : Blo 1865634 2799575 := bstep (se 1 (by rfl) ⟨2099681, by rfl⟩ : syracuseStep 2799575 = 4199363) B4199363
theorem B4200407 : Blo 1865634 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B1865707 : Blo 1865634 1865707 := bstep (se 1 (by rfl) ⟨1399280, by rfl⟩ : syracuseStep 1865707 = 2798561) B2798561
theorem B1865719 : Blo 1865634 1865719 := bstep (se 1 (by rfl) ⟨1399289, by rfl⟩ : syracuseStep 1865719 = 2798579) B2798579
theorem B1865739 : Blo 1865634 1865739 := bstep (se 1 (by rfl) ⟨1399304, by rfl⟩ : syracuseStep 1865739 = 2798609) B2798609
theorem B1865751 : Blo 1865634 1865751 := bstep (se 1 (by rfl) ⟨1399313, by rfl⟩ : syracuseStep 1865751 = 2798627) B2798627
theorem B2799641 : Blo 1865634 2799641 := bstep (se 2 (by rfl) ⟨1049865, by rfl⟩ : syracuseStep 2799641 = 2099731) B2099731
theorem B1865771 : Blo 1865634 1865771 := bstep (se 1 (by rfl) ⟨1399328, by rfl⟩ : syracuseStep 1865771 = 2798657) B2798657
theorem B12769325 : Blo 1865634 12769325 := bstep (se 3 (by rfl) ⟨2394248, by rfl⟩ : syracuseStep 12769325 = 4788497) B4788497
theorem B9451565 : Blo 1865634 9451565 := bstep (se 3 (by rfl) ⟨1772168, by rfl⟩ : syracuseStep 9451565 = 3544337) B3544337
theorem B1865783 : Blo 1865634 1865783 := bstep (se 1 (by rfl) ⟨1399337, by rfl⟩ : syracuseStep 1865783 = 2798675) B2798675
theorem B4724801 : Blo 1865634 4724801 := bstep (se 2 (by rfl) ⟨1771800, by rfl⟩ : syracuseStep 4724801 = 3543601) B3543601
theorem B1865803 : Blo 1865634 1865803 := bstep (se 1 (by rfl) ⟨1399352, by rfl⟩ : syracuseStep 1865803 = 2798705) B2798705
theorem B1865815 : Blo 1865634 1865815 := bstep (se 1 (by rfl) ⟨1399361, by rfl⟩ : syracuseStep 1865815 = 2798723) B2798723
theorem B1865835 : Blo 1865634 1865835 := bstep (se 1 (by rfl) ⟨1399376, by rfl⟩ : syracuseStep 1865835 = 2798753) B2798753
theorem B1865847 : Blo 1865634 1865847 := bstep (se 1 (by rfl) ⟨1399385, by rfl⟩ : syracuseStep 1865847 = 2798771) B2798771
theorem B3545203 : Blo 1865634 3545203 := bstep (se 1 (by rfl) ⟨2658902, by rfl⟩ : syracuseStep 3545203 = 5317805) B5317805
theorem B1865867 : Blo 1865634 1865867 := bstep (se 1 (by rfl) ⟨1399400, by rfl⟩ : syracuseStep 1865867 = 2798801) B2798801
theorem B2799755 : Blo 1865634 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B4200587 : Blo 1865634 4200587 := bstep (se 1 (by rfl) ⟨3150440, by rfl⟩ : syracuseStep 4200587 = 6300881) B6300881
theorem B1865879 : Blo 1865634 1865879 := bstep (se 1 (by rfl) ⟨1399409, by rfl⟩ : syracuseStep 1865879 = 2798819) B2798819
theorem B2799767 : Blo 1865634 2799767 := bstep (se 1 (by rfl) ⟨2099825, by rfl⟩ : syracuseStep 2799767 = 4199651) B4199651
theorem B1865899 : Blo 1865634 1865899 := bstep (se 1 (by rfl) ⟨1399424, by rfl⟩ : syracuseStep 1865899 = 2798849) B2798849
theorem B1865911 : Blo 1865634 1865911 := bstep (se 1 (by rfl) ⟨1399433, by rfl⟩ : syracuseStep 1865911 = 2798867) B2798867
theorem B4200641 : Blo 1865634 4200641 := bstep (se 2 (by rfl) ⟨1575240, by rfl⟩ : syracuseStep 4200641 = 3150481) B3150481
theorem B1865931 : Blo 1865634 1865931 := bstep (se 1 (by rfl) ⟨1399448, by rfl⟩ : syracuseStep 1865931 = 2798897) B2798897
theorem B6297803 : Blo 1865634 6297803 := bstep (se 1 (by rfl) ⟨4723352, by rfl⟩ : syracuseStep 6297803 = 9446705) B9446705
theorem B1865943 : Blo 1865634 1865943 := bstep (se 1 (by rfl) ⟨1399457, by rfl⟩ : syracuseStep 1865943 = 2798915) B2798915
theorem B2799833 : Blo 1865634 2799833 := bstep (se 2 (by rfl) ⟨1049937, by rfl⟩ : syracuseStep 2799833 = 2099875) B2099875
theorem B7182557 : Blo 1865634 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B1865963 : Blo 1865634 1865963 := bstep (se 1 (by rfl) ⟨1399472, by rfl⟩ : syracuseStep 1865963 = 2798945) B2798945
theorem B1865975 : Blo 1865634 1865975 := bstep (se 1 (by rfl) ⟨1399481, by rfl⟩ : syracuseStep 1865975 = 2798963) B2798963
theorem B1865995 : Blo 1865634 1865995 := bstep (se 1 (by rfl) ⟨1399496, by rfl⟩ : syracuseStep 1865995 = 2798993) B2798993
theorem B1866007 : Blo 1865634 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B1866027 : Blo 1865634 1866027 := bstep (se 1 (by rfl) ⟨1399520, by rfl⟩ : syracuseStep 1866027 = 2799041) B2799041
theorem B19151149 : Blo 1865634 19151149 := bstep (se 3 (by rfl) ⟨3590840, by rfl⟩ : syracuseStep 19151149 = 7181681) B7181681
theorem B1866039 : Blo 1865634 1866039 := bstep (se 1 (by rfl) ⟨1399529, by rfl⟩ : syracuseStep 1866039 = 2799059) B2799059
theorem B1866059 : Blo 1865634 1866059 := bstep (se 1 (by rfl) ⟨1399544, by rfl⟩ : syracuseStep 1866059 = 2799089) B2799089
theorem B2799947 : Blo 1865634 2799947 := bstep (se 1 (by rfl) ⟨2099960, by rfl⟩ : syracuseStep 2799947 = 4199921) B4199921
theorem B1866071 : Blo 1865634 1866071 := bstep (se 1 (by rfl) ⟨1399553, by rfl⟩ : syracuseStep 1866071 = 2799107) B2799107
theorem B2799959 : Blo 1865634 2799959 := bstep (se 1 (by rfl) ⟨2099969, by rfl⟩ : syracuseStep 2799959 = 4199939) B4199939
theorem B1866091 : Blo 1865634 1866091 := bstep (se 1 (by rfl) ⟨1399568, by rfl⟩ : syracuseStep 1866091 = 2799137) B2799137
theorem B1866103 : Blo 1865634 1866103 := bstep (se 1 (by rfl) ⟨1399577, by rfl⟩ : syracuseStep 1866103 = 2799155) B2799155
theorem B1866123 : Blo 1865634 1866123 := bstep (se 1 (by rfl) ⟨1399592, by rfl⟩ : syracuseStep 1866123 = 2799185) B2799185
theorem B1866135 : Blo 1865634 1866135 := bstep (se 1 (by rfl) ⟨1399601, by rfl⟩ : syracuseStep 1866135 = 2799203) B2799203
theorem B2800025 : Blo 1865634 2800025 := bstep (se 2 (by rfl) ⟨1050009, by rfl⟩ : syracuseStep 2800025 = 2100019) B2100019
theorem B4200857 : Blo 1865634 4200857 := bstep (se 2 (by rfl) ⟨1575321, by rfl⟩ : syracuseStep 4200857 = 3150643) B3150643
theorem B1866155 : Blo 1865634 1866155 := bstep (se 1 (by rfl) ⟨1399616, by rfl⟩ : syracuseStep 1866155 = 2799233) B2799233
theorem B8518061 : Blo 1865634 8518061 := bstep (se 3 (by rfl) ⟨1597136, by rfl⟩ : syracuseStep 8518061 = 3194273) B3194273
theorem B17938867 : Blo 1865634 17938867 := bstep (se 1 (by rfl) ⟨13454150, by rfl⟩ : syracuseStep 17938867 = 26908301) B26908301
theorem B1866167 : Blo 1865634 1866167 := bstep (se 1 (by rfl) ⟨1399625, by rfl⟩ : syracuseStep 1866167 = 2799251) B2799251
theorem B1866187 : Blo 1865634 1866187 := bstep (se 1 (by rfl) ⟨1399640, by rfl⟩ : syracuseStep 1866187 = 2799281) B2799281
theorem B1866199 : Blo 1865634 1866199 := bstep (se 1 (by rfl) ⟨1399649, by rfl⟩ : syracuseStep 1866199 = 2799299) B2799299
theorem B6298073 : Blo 1865634 6298073 := bstep (se 2 (by rfl) ⟨2361777, by rfl⟩ : syracuseStep 6298073 = 4723555) B4723555
theorem B1866219 : Blo 1865634 1866219 := bstep (se 1 (by rfl) ⟨1399664, by rfl⟩ : syracuseStep 1866219 = 2799329) B2799329
theorem B4200947 : Blo 1865634 4200947 := bstep (se 1 (by rfl) ⟨3150710, by rfl⟩ : syracuseStep 4200947 = 6301421) B6301421
theorem B1866231 : Blo 1865634 1866231 := bstep (se 1 (by rfl) ⟨1399673, by rfl⟩ : syracuseStep 1866231 = 2799347) B2799347
theorem B1866251 : Blo 1865634 1866251 := bstep (se 1 (by rfl) ⟨1399688, by rfl⟩ : syracuseStep 1866251 = 2799377) B2799377
theorem B2800139 : Blo 1865634 2800139 := bstep (se 1 (by rfl) ⟨2100104, by rfl⟩ : syracuseStep 2800139 = 4200209) B4200209
theorem B1866263 : Blo 1865634 1866263 := bstep (se 1 (by rfl) ⟨1399697, by rfl⟩ : syracuseStep 1866263 = 2799395) B2799395
theorem B2800151 : Blo 1865634 2800151 := bstep (se 1 (by rfl) ⟨2100113, by rfl⟩ : syracuseStep 2800151 = 4200227) B4200227
theorem B4200983 : Blo 1865634 4200983 := bstep (se 1 (by rfl) ⟨3150737, by rfl⟩ : syracuseStep 4200983 = 6301475) B6301475
theorem B1866283 : Blo 1865634 1866283 := bstep (se 1 (by rfl) ⟨1399712, by rfl⟩ : syracuseStep 1866283 = 2799425) B2799425
theorem B1866295 : Blo 1865634 1866295 := bstep (se 1 (by rfl) ⟨1399721, by rfl⟩ : syracuseStep 1866295 = 2799443) B2799443
theorem B1866315 : Blo 1865634 1866315 := bstep (se 1 (by rfl) ⟨1399736, by rfl⟩ : syracuseStep 1866315 = 2799473) B2799473
theorem B34052683 : Blo 1865634 34052683 := bstep (se 1 (by rfl) ⟨25539512, by rfl⟩ : syracuseStep 34052683 = 51079025) B51079025
theorem B1866327 : Blo 1865634 1866327 := bstep (se 1 (by rfl) ⟨1399745, by rfl⟩ : syracuseStep 1866327 = 2799491) B2799491
theorem B3988055 : Blo 1865634 3988055 := bstep (se 1 (by rfl) ⟨2991041, by rfl⟩ : syracuseStep 3988055 = 5982083) B5982083
theorem B4725337 : Blo 1865634 4725337 := bstep (se 2 (by rfl) ⟨1772001, by rfl⟩ : syracuseStep 4725337 = 3544003) B3544003
theorem B2800217 : Blo 1865634 2800217 := bstep (se 2 (by rfl) ⟨1050081, by rfl⟩ : syracuseStep 2800217 = 2100163) B2100163
theorem B1866347 : Blo 1865634 1866347 := bstep (se 1 (by rfl) ⟨1399760, by rfl⟩ : syracuseStep 1866347 = 2799521) B2799521
theorem B1866359 : Blo 1865634 1866359 := bstep (se 1 (by rfl) ⟨1399769, by rfl⟩ : syracuseStep 1866359 = 2799539) B2799539
theorem B1866379 : Blo 1865634 1866379 := bstep (se 1 (by rfl) ⟨1399784, by rfl⟩ : syracuseStep 1866379 = 2799569) B2799569
theorem B1866391 : Blo 1865634 1866391 := bstep (se 1 (by rfl) ⟨1399793, by rfl⟩ : syracuseStep 1866391 = 2799587) B2799587
theorem B1866411 : Blo 1865634 1866411 := bstep (se 1 (by rfl) ⟨1399808, by rfl⟩ : syracuseStep 1866411 = 2799617) B2799617
theorem B1866423 : Blo 1865634 1866423 := bstep (se 1 (by rfl) ⟨1399817, by rfl⟩ : syracuseStep 1866423 = 2799635) B2799635
theorem B1866443 : Blo 1865634 1866443 := bstep (se 1 (by rfl) ⟨1399832, by rfl⟩ : syracuseStep 1866443 = 2799665) B2799665
theorem B2800331 : Blo 1865634 2800331 := bstep (se 1 (by rfl) ⟨2100248, by rfl⟩ : syracuseStep 2800331 = 4200497) B4200497
theorem B4201163 : Blo 1865634 4201163 := bstep (se 1 (by rfl) ⟨3150872, by rfl⟩ : syracuseStep 4201163 = 6301745) B6301745
theorem B1866455 : Blo 1865634 1866455 := bstep (se 1 (by rfl) ⟨1399841, by rfl⟩ : syracuseStep 1866455 = 2799683) B2799683
theorem B2800343 : Blo 1865634 2800343 := bstep (se 1 (by rfl) ⟨2100257, by rfl⟩ : syracuseStep 2800343 = 4200515) B4200515
theorem B10631897 : Blo 1865634 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B5675741 : Blo 1865634 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B1866475 : Blo 1865634 1866475 := bstep (se 1 (by rfl) ⟨1399856, by rfl⟩ : syracuseStep 1866475 = 2799713) B2799713
theorem B76667633 : Blo 1865634 76667633 := bstep (se 2 (by rfl) ⟨28750362, by rfl⟩ : syracuseStep 76667633 = 57500725) B57500725
theorem B1866487 : Blo 1865634 1866487 := bstep (se 1 (by rfl) ⟨1399865, by rfl⟩ : syracuseStep 1866487 = 2799731) B2799731
theorem B4201217 : Blo 1865634 4201217 := bstep (se 2 (by rfl) ⟨1575456, by rfl⟩ : syracuseStep 4201217 = 3150913) B3150913
theorem B1866507 : Blo 1865634 1866507 := bstep (se 1 (by rfl) ⟨1399880, by rfl⟩ : syracuseStep 1866507 = 2799761) B2799761
theorem B7084817 : Blo 1865634 7084817 := bstep (se 2 (by rfl) ⟨2656806, by rfl⟩ : syracuseStep 7084817 = 5313613) B5313613
theorem B1866519 : Blo 1865634 1866519 := bstep (se 1 (by rfl) ⟨1399889, by rfl⟩ : syracuseStep 1866519 = 2799779) B2799779
theorem B2800409 : Blo 1865634 2800409 := bstep (se 2 (by rfl) ⟨1050153, by rfl⟩ : syracuseStep 2800409 = 2100307) B2100307
theorem B1866539 : Blo 1865634 1866539 := bstep (se 1 (by rfl) ⟨1399904, by rfl⟩ : syracuseStep 1866539 = 2799809) B2799809
theorem B1866551 : Blo 1865634 1866551 := bstep (se 1 (by rfl) ⟨1399913, by rfl⟩ : syracuseStep 1866551 = 2799827) B2799827
theorem B1866571 : Blo 1865634 1866571 := bstep (se 1 (by rfl) ⟨1399928, by rfl⟩ : syracuseStep 1866571 = 2799857) B2799857
theorem B1866583 : Blo 1865634 1866583 := bstep (se 1 (by rfl) ⟨1399937, by rfl⟩ : syracuseStep 1866583 = 2799875) B2799875
theorem B31882085 : Blo 1865634 31882085 := bstep (se 4 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 31882085 = 5977891) B5977891
theorem B23919461 : Blo 1865634 23919461 := bstep (se 4 (by rfl) ⟨2242449, by rfl⟩ : syracuseStep 23919461 = 4484899) B4484899
theorem B1866603 : Blo 1865634 1866603 := bstep (se 1 (by rfl) ⟨1399952, by rfl⟩ : syracuseStep 1866603 = 2799905) B2799905
theorem B1866615 : Blo 1865634 1866615 := bstep (se 1 (by rfl) ⟨1399961, by rfl⟩ : syracuseStep 1866615 = 2799923) B2799923
theorem B1866635 : Blo 1865634 1866635 := bstep (se 1 (by rfl) ⟨1399976, by rfl⟩ : syracuseStep 1866635 = 2799953) B2799953
theorem B2800523 : Blo 1865634 2800523 := bstep (se 1 (by rfl) ⟨2100392, by rfl⟩ : syracuseStep 2800523 = 4200785) B4200785
theorem B1866647 : Blo 1865634 1866647 := bstep (se 1 (by rfl) ⟨1399985, by rfl⟩ : syracuseStep 1866647 = 2799971) B2799971
theorem B2800535 : Blo 1865634 2800535 := bstep (se 1 (by rfl) ⟨2100401, by rfl⟩ : syracuseStep 2800535 = 4200803) B4200803
theorem B1866667 : Blo 1865634 1866667 := bstep (se 1 (by rfl) ⟨1400000, by rfl⟩ : syracuseStep 1866667 = 2800001) B2800001
theorem B9575347 : Blo 1865634 9575347 := bstep (se 1 (by rfl) ⟨7181510, by rfl⟩ : syracuseStep 9575347 = 14363021) B14363021
theorem B1866679 : Blo 1865634 1866679 := bstep (se 1 (by rfl) ⟨1400009, by rfl⟩ : syracuseStep 1866679 = 2800019) B2800019
theorem B4258739 : Blo 1865634 4258739 := bstep (se 1 (by rfl) ⟨3194054, by rfl⟩ : syracuseStep 4258739 = 6388109) B6388109
theorem B1866699 : Blo 1865634 1866699 := bstep (se 1 (by rfl) ⟨1400024, by rfl⟩ : syracuseStep 1866699 = 2800049) B2800049
theorem B1866711 : Blo 1865634 1866711 := bstep (se 1 (by rfl) ⟨1400033, by rfl⟩ : syracuseStep 1866711 = 2800067) B2800067
theorem B2800601 : Blo 1865634 2800601 := bstep (se 2 (by rfl) ⟨1050225, by rfl⟩ : syracuseStep 2800601 = 2100451) B2100451
theorem B4201433 : Blo 1865634 4201433 := bstep (se 2 (by rfl) ⟨1575537, by rfl⟩ : syracuseStep 4201433 = 3151075) B3151075
theorem B1866731 : Blo 1865634 1866731 := bstep (se 1 (by rfl) ⟨1400048, by rfl⟩ : syracuseStep 1866731 = 2800097) B2800097
theorem B1866743 : Blo 1865634 1866743 := bstep (se 1 (by rfl) ⟨1400057, by rfl⟩ : syracuseStep 1866743 = 2800115) B2800115
theorem B1866763 : Blo 1865634 1866763 := bstep (se 1 (by rfl) ⟨1400072, by rfl⟩ : syracuseStep 1866763 = 2800145) B2800145
theorem B2522135 : Blo 1865634 2522135 := bstep (se 1 (by rfl) ⟨1891601, by rfl⟩ : syracuseStep 2522135 = 3783203) B3783203
theorem B1866775 : Blo 1865634 1866775 := bstep (se 1 (by rfl) ⟨1400081, by rfl⟩ : syracuseStep 1866775 = 2800163) B2800163
theorem B1866795 : Blo 1865634 1866795 := bstep (se 1 (by rfl) ⟨1400096, by rfl⟩ : syracuseStep 1866795 = 2800193) B2800193
theorem B4201523 : Blo 1865634 4201523 := bstep (se 1 (by rfl) ⟨3151142, by rfl⟩ : syracuseStep 4201523 = 6302285) B6302285
theorem B1866807 : Blo 1865634 1866807 := bstep (se 1 (by rfl) ⟨1400105, by rfl⟩ : syracuseStep 1866807 = 2800211) B2800211
theorem B1866827 : Blo 1865634 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B2800715 : Blo 1865634 2800715 := bstep (se 1 (by rfl) ⟨2100536, by rfl⟩ : syracuseStep 2800715 = 4201073) B4201073
theorem B1866839 : Blo 1865634 1866839 := bstep (se 1 (by rfl) ⟨1400129, by rfl⟩ : syracuseStep 1866839 = 2800259) B2800259
theorem B2800727 : Blo 1865634 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B4201559 : Blo 1865634 4201559 := bstep (se 1 (by rfl) ⟨3151169, by rfl⟩ : syracuseStep 4201559 = 6302339) B6302339
theorem B1866859 : Blo 1865634 1866859 := bstep (se 1 (by rfl) ⟨1400144, by rfl⟩ : syracuseStep 1866859 = 2800289) B2800289
theorem B1866871 : Blo 1865634 1866871 := bstep (se 1 (by rfl) ⟨1400153, by rfl⟩ : syracuseStep 1866871 = 2800307) B2800307
theorem B1866891 : Blo 1865634 1866891 := bstep (se 1 (by rfl) ⟨1400168, by rfl⟩ : syracuseStep 1866891 = 2800337) B2800337
theorem B6298775 : Blo 1865634 6298775 := bstep (se 1 (by rfl) ⟨4724081, by rfl⟩ : syracuseStep 6298775 = 9448163) B9448163
theorem B1866903 : Blo 1865634 1866903 := bstep (se 1 (by rfl) ⟨1400177, by rfl⟩ : syracuseStep 1866903 = 2800355) B2800355
theorem B2800793 : Blo 1865634 2800793 := bstep (se 2 (by rfl) ⟨1050297, by rfl⟩ : syracuseStep 2800793 = 2100595) B2100595
theorem B1866923 : Blo 1865634 1866923 := bstep (se 1 (by rfl) ⟨1400192, by rfl⟩ : syracuseStep 1866923 = 2800385) B2800385
theorem B1866935 : Blo 1865634 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B5315777 : Blo 1865634 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B1866955 : Blo 1865634 1866955 := bstep (se 1 (by rfl) ⟨1400216, by rfl⟩ : syracuseStep 1866955 = 2800433) B2800433
theorem B1866967 : Blo 1865634 1866967 := bstep (se 1 (by rfl) ⟨1400225, by rfl⟩ : syracuseStep 1866967 = 2800451) B2800451
theorem B1866987 : Blo 1865634 1866987 := bstep (se 1 (by rfl) ⟨1400240, by rfl⟩ : syracuseStep 1866987 = 2800481) B2800481
theorem B3783923 : Blo 1865634 3783923 := bstep (se 1 (by rfl) ⟨2837942, by rfl⟩ : syracuseStep 3783923 = 5675885) B5675885
theorem B1866999 : Blo 1865634 1866999 := bstep (se 1 (by rfl) ⟨1400249, by rfl⟩ : syracuseStep 1866999 = 2800499) B2800499
theorem B1867019 : Blo 1865634 1867019 := bstep (se 1 (by rfl) ⟨1400264, by rfl⟩ : syracuseStep 1867019 = 2800529) B2800529
theorem B2800907 : Blo 1865634 2800907 := bstep (se 1 (by rfl) ⟨2100680, by rfl⟩ : syracuseStep 2800907 = 4201361) B4201361
theorem B4201739 : Blo 1865634 4201739 := bstep (se 1 (by rfl) ⟨3151304, by rfl⟩ : syracuseStep 4201739 = 6302609) B6302609
theorem B1867031 : Blo 1865634 1867031 := bstep (se 1 (by rfl) ⟨1400273, by rfl⟩ : syracuseStep 1867031 = 2800547) B2800547
theorem B2800919 : Blo 1865634 2800919 := bstep (se 1 (by rfl) ⟨2100689, by rfl⟩ : syracuseStep 2800919 = 4201379) B4201379
theorem B1867051 : Blo 1865634 1867051 := bstep (se 1 (by rfl) ⟨1400288, by rfl⟩ : syracuseStep 1867051 = 2800577) B2800577
theorem B1867063 : Blo 1865634 1867063 := bstep (se 1 (by rfl) ⟨1400297, by rfl⟩ : syracuseStep 1867063 = 2800595) B2800595
theorem B4201793 : Blo 1865634 4201793 := bstep (se 2 (by rfl) ⟨1575672, by rfl⟩ : syracuseStep 4201793 = 3151345) B3151345
theorem B1867083 : Blo 1865634 1867083 := bstep (se 1 (by rfl) ⟨1400312, by rfl⟩ : syracuseStep 1867083 = 2800625) B2800625
theorem B1867095 : Blo 1865634 1867095 := bstep (se 1 (by rfl) ⟨1400321, by rfl⟩ : syracuseStep 1867095 = 2800643) B2800643
theorem B2800985 : Blo 1865634 2800985 := bstep (se 2 (by rfl) ⟨1050369, by rfl⟩ : syracuseStep 2800985 = 2100739) B2100739
theorem B6724957 : Blo 1865634 6724957 := bstep (se 3 (by rfl) ⟨1260929, by rfl⟩ : syracuseStep 6724957 = 2521859) B2521859
theorem B1867115 : Blo 1865634 1867115 := bstep (se 1 (by rfl) ⟨1400336, by rfl⟩ : syracuseStep 1867115 = 2800673) B2800673
theorem B1867127 : Blo 1865634 1867127 := bstep (se 1 (by rfl) ⟨1400345, by rfl⟩ : syracuseStep 1867127 = 2800691) B2800691
theorem B1867147 : Blo 1865634 1867147 := bstep (se 1 (by rfl) ⟨1400360, by rfl⟩ : syracuseStep 1867147 = 2800721) B2800721
theorem B6725015 : Blo 1865634 6725015 := bstep (se 1 (by rfl) ⟨5043761, by rfl⟩ : syracuseStep 6725015 = 10087523) B10087523
theorem B1867159 : Blo 1865634 1867159 := bstep (se 1 (by rfl) ⟨1400369, by rfl⟩ : syracuseStep 1867159 = 2800739) B2800739
theorem B1867179 : Blo 1865634 1867179 := bstep (se 1 (by rfl) ⟨1400384, by rfl⟩ : syracuseStep 1867179 = 2800769) B2800769
theorem B1867191 : Blo 1865634 1867191 := bstep (se 1 (by rfl) ⟨1400393, by rfl⟩ : syracuseStep 1867191 = 2800787) B2800787
theorem B7085515 : Blo 1865634 7085515 := bstep (se 1 (by rfl) ⟨5314136, by rfl⟩ : syracuseStep 7085515 = 10628273) B10628273
theorem B1867211 : Blo 1865634 1867211 := bstep (se 1 (by rfl) ⟨1400408, by rfl⟩ : syracuseStep 1867211 = 2800817) B2800817
theorem B2801099 : Blo 1865634 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B1867223 : Blo 1865634 1867223 := bstep (se 1 (by rfl) ⟨1400417, by rfl⟩ : syracuseStep 1867223 = 2800835) B2800835
theorem B2801111 : Blo 1865634 2801111 := bstep (se 1 (by rfl) ⟨2100833, by rfl⟩ : syracuseStep 2801111 = 4201667) B4201667
theorem B1867243 : Blo 1865634 1867243 := bstep (se 1 (by rfl) ⟨1400432, by rfl⟩ : syracuseStep 1867243 = 2800865) B2800865
theorem B1867255 : Blo 1865634 1867255 := bstep (se 1 (by rfl) ⟨1400441, by rfl⟩ : syracuseStep 1867255 = 2800883) B2800883
theorem B1867275 : Blo 1865634 1867275 := bstep (se 1 (by rfl) ⟨1400456, by rfl⟩ : syracuseStep 1867275 = 2800913) B2800913
theorem B1867287 : Blo 1865634 1867287 := bstep (se 1 (by rfl) ⟨1400465, by rfl⟩ : syracuseStep 1867287 = 2800931) B2800931
theorem B2801177 : Blo 1865634 2801177 := bstep (se 2 (by rfl) ⟨1050441, by rfl⟩ : syracuseStep 2801177 = 2100883) B2100883
theorem B4202009 : Blo 1865634 4202009 := bstep (se 2 (by rfl) ⟨1575753, by rfl⟩ : syracuseStep 4202009 = 3151507) B3151507
theorem B1867307 : Blo 1865634 1867307 := bstep (se 1 (by rfl) ⟨1400480, by rfl⟩ : syracuseStep 1867307 = 2800961) B2800961
theorem B1867319 : Blo 1865634 1867319 := bstep (se 1 (by rfl) ⟨1400489, by rfl⟩ : syracuseStep 1867319 = 2800979) B2800979
theorem B11959883 : Blo 1865634 11959883 := bstep (se 1 (by rfl) ⟨8969912, by rfl⟩ : syracuseStep 11959883 = 17939825) B17939825
theorem B1867339 : Blo 1865634 1867339 := bstep (se 1 (by rfl) ⟨1400504, by rfl⟩ : syracuseStep 1867339 = 2801009) B2801009
theorem B1867351 : Blo 1865634 1867351 := bstep (se 1 (by rfl) ⟨1400513, by rfl⟩ : syracuseStep 1867351 = 2801027) B2801027
theorem B5979737 : Blo 1865634 5979737 := bstep (se 2 (by rfl) ⟨2242401, by rfl⟩ : syracuseStep 5979737 = 4484803) B4484803
theorem B1867371 : Blo 1865634 1867371 := bstep (se 1 (by rfl) ⟨1400528, by rfl⟩ : syracuseStep 1867371 = 2801057) B2801057
theorem B4202099 : Blo 1865634 4202099 := bstep (se 1 (by rfl) ⟨3151574, by rfl⟩ : syracuseStep 4202099 = 6303149) B6303149
theorem B1867383 : Blo 1865634 1867383 := bstep (se 1 (by rfl) ⟨1400537, by rfl⟩ : syracuseStep 1867383 = 2801075) B2801075
theorem B1867403 : Blo 1865634 1867403 := bstep (se 1 (by rfl) ⟨1400552, by rfl⟩ : syracuseStep 1867403 = 2801105) B2801105
theorem B2801291 : Blo 1865634 2801291 := bstep (se 1 (by rfl) ⟨2100968, by rfl⟩ : syracuseStep 2801291 = 4201937) B4201937
theorem B1867415 : Blo 1865634 1867415 := bstep (se 1 (by rfl) ⟨1400561, by rfl⟩ : syracuseStep 1867415 = 2801123) B2801123
theorem B2801303 : Blo 1865634 2801303 := bstep (se 1 (by rfl) ⟨2100977, by rfl⟩ : syracuseStep 2801303 = 4201955) B4201955
theorem B4202135 : Blo 1865634 4202135 := bstep (se 1 (by rfl) ⟨3151601, by rfl⟩ : syracuseStep 4202135 = 6303203) B6303203
theorem B1867435 : Blo 1865634 1867435 := bstep (se 1 (by rfl) ⟨1400576, by rfl⟩ : syracuseStep 1867435 = 2801153) B2801153
theorem B6299315 : Blo 1865634 6299315 := bstep (se 1 (by rfl) ⟨4724486, by rfl⟩ : syracuseStep 6299315 = 9448973) B9448973
theorem B4726451 : Blo 1865634 4726451 := bstep (se 1 (by rfl) ⟨3544838, by rfl⟩ : syracuseStep 4726451 = 7089677) B7089677
theorem B1867447 : Blo 1865634 1867447 := bstep (se 1 (by rfl) ⟨1400585, by rfl⟩ : syracuseStep 1867447 = 2801171) B2801171
theorem B7970507 : Blo 1865634 7970507 := bstep (se 1 (by rfl) ⟨5977880, by rfl⟩ : syracuseStep 7970507 = 11955761) B11955761
theorem B1867467 : Blo 1865634 1867467 := bstep (se 1 (by rfl) ⟨1400600, by rfl⟩ : syracuseStep 1867467 = 2801201) B2801201
theorem B1867479 : Blo 1865634 1867479 := bstep (se 1 (by rfl) ⟨1400609, by rfl⟩ : syracuseStep 1867479 = 2801219) B2801219
theorem B5316313 : Blo 1865634 5316313 := bstep (se 2 (by rfl) ⟨1993617, by rfl⟩ : syracuseStep 5316313 = 3987235) B3987235
theorem B2801369 : Blo 1865634 2801369 := bstep (se 2 (by rfl) ⟨1050513, by rfl⟩ : syracuseStep 2801369 = 2101027) B2101027
theorem B7085789 : Blo 1865634 7085789 := bstep (se 3 (by rfl) ⟨1328585, by rfl⟩ : syracuseStep 7085789 = 2657171) B2657171
theorem B1867499 : Blo 1865634 1867499 := bstep (se 1 (by rfl) ⟨1400624, by rfl⟩ : syracuseStep 1867499 = 2801249) B2801249
theorem B1867511 : Blo 1865634 1867511 := bstep (se 1 (by rfl) ⟨1400633, by rfl⟩ : syracuseStep 1867511 = 2801267) B2801267
theorem B1867531 : Blo 1865634 1867531 := bstep (se 1 (by rfl) ⟨1400648, by rfl⟩ : syracuseStep 1867531 = 2801297) B2801297
theorem B1867543 : Blo 1865634 1867543 := bstep (se 1 (by rfl) ⟨1400657, by rfl⟩ : syracuseStep 1867543 = 2801315) B2801315
theorem B2694937 : Blo 1865634 2694937 := bstep (se 2 (by rfl) ⟨1010601, by rfl⟩ : syracuseStep 2694937 = 2021203) B2021203
theorem B1867563 : Blo 1865634 1867563 := bstep (se 1 (by rfl) ⟨1400672, by rfl⟩ : syracuseStep 1867563 = 2801345) B2801345
theorem B1867575 : Blo 1865634 1867575 := bstep (se 1 (by rfl) ⟨1400681, by rfl⟩ : syracuseStep 1867575 = 2801363) B2801363
theorem B1867595 : Blo 1865634 1867595 := bstep (se 1 (by rfl) ⟨1400696, by rfl⟩ : syracuseStep 1867595 = 2801393) B2801393
theorem B3030871 : Blo 1865634 3030871 := bstep (se 1 (by rfl) ⟨2273153, by rfl⟩ : syracuseStep 3030871 = 4546307) B4546307
theorem B1867607 : Blo 1865634 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B1867627 : Blo 1865634 1867627 := bstep (se 1 (by rfl) ⟨1400720, by rfl⟩ : syracuseStep 1867627 = 2801441) B2801441
theorem B6299585 : Blo 1865634 6299585 := bstep (se 2 (by rfl) ⟨2362344, by rfl⟩ : syracuseStep 6299585 = 4724689) B4724689
theorem B4726745 : Blo 1865634 4726745 := bstep (se 2 (by rfl) ⟨1772529, by rfl⟩ : syracuseStep 4726745 = 3545059) B3545059
theorem B4726795 : Blo 1865634 4726795 := bstep (se 1 (by rfl) ⟨3545096, by rfl⟩ : syracuseStep 4726795 = 7090193) B7090193
theorem B72753187 : Blo 1865634 72753187 := bstep (se 1 (by rfl) ⟨54564890, by rfl⟩ : syracuseStep 72753187 = 109129781) B109129781
theorem B6725693 : Blo 1865634 6725693 := bstep (se 3 (by rfl) ⟨1261067, by rfl⟩ : syracuseStep 6725693 = 2522135) B2522135
theorem B5677175 : Blo 1865634 5677175 := bstep (se 1 (by rfl) ⟨4257881, by rfl⟩ : syracuseStep 5677175 = 8515763) B8515763
theorem B2695303 : Blo 1865634 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B4726937 : Blo 1865634 4726937 := bstep (se 2 (by rfl) ⟨1772601, by rfl⟩ : syracuseStep 4726937 = 3545203) B3545203
theorem B5046571 : Blo 1865634 5046571 := bstep (se 1 (by rfl) ⟨3784928, by rfl⟩ : syracuseStep 5046571 = 7569857) B7569857
theorem B6299963 : Blo 1865634 6299963 := bstep (se 1 (by rfl) ⟨4724972, by rfl⟩ : syracuseStep 6299963 = 9449945) B9449945
theorem B4727099 : Blo 1865634 4727099 := bstep (se 1 (by rfl) ⟨3545324, by rfl⟩ : syracuseStep 4727099 = 7090649) B7090649
theorem B25534865 : Blo 1865634 25534865 := bstep (se 2 (by rfl) ⟨9575574, by rfl⟩ : syracuseStep 25534865 = 19151149) B19151149
theorem B21553553 : Blo 1865634 21553553 := bstep (se 2 (by rfl) ⟨8082582, by rfl⟩ : syracuseStep 21553553 = 16165165) B16165165
theorem B21021137 : Blo 1865634 21021137 := bstep (se 2 (by rfl) ⟨7882926, by rfl⟩ : syracuseStep 21021137 = 15765853) B15765853
theorem B10625539 : Blo 1865634 10625539 := bstep (se 1 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 10625539 = 15938309) B15938309
theorem B5317235 : Blo 1865634 5317235 := bstep (se 1 (by rfl) ⟨3987926, by rfl⟩ : syracuseStep 5317235 = 7975853) B7975853
theorem B4727443 : Blo 1865634 4727443 := bstep (se 1 (by rfl) ⟨3545582, by rfl⟩ : syracuseStep 4727443 = 7091165) B7091165
theorem B6300449 : Blo 1865634 6300449 := bstep (se 2 (by rfl) ⟨2362668, by rfl⟩ : syracuseStep 6300449 = 4725337) B4725337
theorem B8971067 : Blo 1865634 8971067 := bstep (se 1 (by rfl) ⟨6728300, by rfl⟩ : syracuseStep 8971067 = 13456601) B13456601
theorem B5317463 : Blo 1865634 5317463 := bstep (se 1 (by rfl) ⟨3988097, by rfl⟩ : syracuseStep 5317463 = 7976195) B7976195
theorem B21259097 : Blo 1865634 21259097 := bstep (se 2 (by rfl) ⟨7972161, by rfl⟩ : syracuseStep 21259097 = 15944323) B15944323
theorem B15950681 : Blo 1865634 15950681 := bstep (se 2 (by rfl) ⟨5981505, by rfl⟩ : syracuseStep 15950681 = 11963011) B11963011
theorem B10363783 : Blo 1865634 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B9454481 : Blo 1865634 9454481 := bstep (se 2 (by rfl) ⟨3545430, by rfl⟩ : syracuseStep 9454481 = 7090861) B7090861
theorem B2991163 : Blo 1865634 2991163 := bstep (se 1 (by rfl) ⟨2243372, by rfl⟩ : syracuseStep 2991163 = 4486745) B4486745
theorem B20177981 : Blo 1865634 20177981 := bstep (se 3 (by rfl) ⟨3783371, by rfl⟩ : syracuseStep 20177981 = 7566743) B7566743
theorem B6726743 : Blo 1865634 6726743 := bstep (se 1 (by rfl) ⟨5045057, by rfl⟩ : syracuseStep 6726743 = 10090115) B10090115
theorem B8512883 : Blo 1865634 8512883 := bstep (se 1 (by rfl) ⟨6384662, by rfl⟩ : syracuseStep 8512883 = 12769325) B12769325
theorem B6301043 : Blo 1865634 6301043 := bstep (se 1 (by rfl) ⟨4725782, by rfl⟩ : syracuseStep 6301043 = 9451565) B9451565
theorem B10634813 : Blo 1865634 10634813 := bstep (se 3 (by rfl) ⟨1994027, by rfl⟩ : syracuseStep 10634813 = 3988055) B3988055
theorem B14181965 : Blo 1865634 14181965 := bstep (se 3 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 14181965 = 5318237) B5318237
theorem B5678707 : Blo 1865634 5678707 := bstep (se 1 (by rfl) ⟨4259030, by rfl⟩ : syracuseStep 5678707 = 8518061) B8518061
theorem B7087931 : Blo 1865634 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B51111755 : Blo 1865634 51111755 := bstep (se 1 (by rfl) ⟨38333816, by rfl⟩ : syracuseStep 51111755 = 76667633) B76667633
theorem B11356049 : Blo 1865634 11356049 := bstep (se 2 (by rfl) ⟨4258518, by rfl⟩ : syracuseStep 11356049 = 8517037) B8517037
theorem B9447353 : Blo 1865634 9447353 := bstep (se 2 (by rfl) ⟨3542757, by rfl⟩ : syracuseStep 9447353 = 7085515) B7085515
theorem B4483073 : Blo 1865634 4483073 := bstep (se 2 (by rfl) ⟨1681152, by rfl⟩ : syracuseStep 4483073 = 3362305) B3362305
theorem B2361403 : Blo 1865634 2361403 := bstep (se 1 (by rfl) ⟨1771052, by rfl⟩ : syracuseStep 2361403 = 3542105) B3542105
theorem B2099335 : Blo 1865634 2099335 := bstep (se 1 (by rfl) ⟨1574501, by rfl⟩ : syracuseStep 2099335 = 3149003) B3149003
theorem B4483343 : Blo 1865634 4483343 := bstep (se 1 (by rfl) ⟨3362507, by rfl⟩ : syracuseStep 4483343 = 6725015) B6725015
theorem B7088417 : Blo 1865634 7088417 := bstep (se 2 (by rfl) ⟨2658156, by rfl⟩ : syracuseStep 7088417 = 5316313) B5316313
theorem B2099515 : Blo 1865634 2099515 := bstep (se 1 (by rfl) ⟨1574636, by rfl⟩ : syracuseStep 2099515 = 3149273) B3149273
theorem B7973255 : Blo 1865634 7973255 := bstep (se 1 (by rfl) ⟨5979941, by rfl⟩ : syracuseStep 7973255 = 11959883) B11959883
theorem B4041161 : Blo 1865634 4041161 := bstep (se 2 (by rfl) ⟨1515435, by rfl⟩ : syracuseStep 4041161 = 3030871) B3030871
theorem B68151773 : Blo 1865634 68151773 := bstep (se 3 (by rfl) ⟨12778457, by rfl⟩ : syracuseStep 68151773 = 25556915) B25556915
theorem B2361899 : Blo 1865634 2361899 := bstep (se 1 (by rfl) ⟨1771424, by rfl⟩ : syracuseStep 2361899 = 3542849) B3542849
theorem B34507457 : Blo 1865634 34507457 := bstep (se 2 (by rfl) ⟨12940296, by rfl⟩ : syracuseStep 34507457 = 25880593) B25880593
theorem B17263297 : Blo 1865634 17263297 := bstep (se 2 (by rfl) ⟨6473736, by rfl⟩ : syracuseStep 17263297 = 12947473) B12947473
theorem B86174405 : Blo 1865634 86174405 := bstep (se 4 (by rfl) ⟨8078850, by rfl⟩ : syracuseStep 86174405 = 16157701) B16157701
theorem B2099983 : Blo 1865634 2099983 := bstep (se 1 (by rfl) ⟨1574987, by rfl⟩ : syracuseStep 2099983 = 3149975) B3149975
theorem B10627955 : Blo 1865634 10627955 := bstep (se 1 (by rfl) ⟨7970966, by rfl⟩ : syracuseStep 10627955 = 15941933) B15941933
theorem B3148679 : Blo 1865634 3148679 := bstep (se 1 (by rfl) ⟨2361509, by rfl⟩ : syracuseStep 3148679 = 4723019) B4723019
theorem B3541907 : Blo 1865634 3541907 := bstep (se 1 (by rfl) ⟨2656430, by rfl⟩ : syracuseStep 3541907 = 5312861) B5312861
theorem B3541961 : Blo 1865634 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B45419525 : Blo 1865634 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B2362375 : Blo 1865634 2362375 := bstep (se 1 (by rfl) ⟨1771781, by rfl⟩ : syracuseStep 2362375 = 3543563) B3543563
theorem B3542059 : Blo 1865634 3542059 := bstep (se 1 (by rfl) ⟨2656544, by rfl⟩ : syracuseStep 3542059 = 5313089) B5313089
theorem B8965187 : Blo 1865634 8965187 := bstep (se 1 (by rfl) ⟨6723890, by rfl⟩ : syracuseStep 8965187 = 13447781) B13447781
theorem B9448649 : Blo 1865634 9448649 := bstep (se 2 (by rfl) ⟨3543243, by rfl⟩ : syracuseStep 9448649 = 7086487) B7086487
theorem B7089389 : Blo 1865634 7089389 := bstep (se 3 (by rfl) ⟨1329260, by rfl⟩ : syracuseStep 7089389 = 2658521) B2658521
theorem B2100487 : Blo 1865634 2100487 := bstep (se 1 (by rfl) ⟨1575365, by rfl⟩ : syracuseStep 2100487 = 3150731) B3150731
theorem B3542287 : Blo 1865634 3542287 := bstep (se 1 (by rfl) ⟨2656715, by rfl⟩ : syracuseStep 3542287 = 5313431) B5313431
theorem B6385031 : Blo 1865634 6385031 := bstep (se 1 (by rfl) ⟨4788773, by rfl⟩ : syracuseStep 6385031 = 9577547) B9577547
theorem B9096583 : Blo 1865634 9096583 := bstep (se 1 (by rfl) ⟨6822437, by rfl⟩ : syracuseStep 9096583 = 13644875) B13644875
theorem B4197779 : Blo 1865634 4197779 := bstep (se 1 (by rfl) ⟨3148334, by rfl⟩ : syracuseStep 4197779 = 6296669) B6296669
theorem B45403577 : Blo 1865634 45403577 := bstep (se 2 (by rfl) ⟨17026341, by rfl⟩ : syracuseStep 45403577 = 34052683) B34052683
theorem B2100667 : Blo 1865634 2100667 := bstep (se 1 (by rfl) ⟨1575500, by rfl⟩ : syracuseStep 2100667 = 3151001) B3151001
theorem B4197833 : Blo 1865634 4197833 := bstep (se 2 (by rfl) ⟨1574187, by rfl⟩ : syracuseStep 4197833 = 3148375) B3148375
theorem B2362871 : Blo 1865634 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B3149327 : Blo 1865634 3149327 := bstep (se 1 (by rfl) ⟨2361995, by rfl⟩ : syracuseStep 3149327 = 4723991) B4723991
theorem B2395663 : Blo 1865634 2395663 := bstep (se 1 (by rfl) ⟨1796747, by rfl⟩ : syracuseStep 2395663 = 3593495) B3593495
theorem B4484641 : Blo 1865634 4484641 := bstep (se 2 (by rfl) ⟨1681740, by rfl⟩ : syracuseStep 4484641 = 3363481) B3363481
theorem B7089707 : Blo 1865634 7089707 := bstep (se 1 (by rfl) ⟨5317280, by rfl⟩ : syracuseStep 7089707 = 10634561) B10634561
theorem B8973911 : Blo 1865634 8973911 := bstep (se 1 (by rfl) ⟨6730433, by rfl⟩ : syracuseStep 8973911 = 13460867) B13460867
theorem B2363023 : Blo 1865634 2363023 := bstep (se 1 (by rfl) ⟨1772267, by rfl⟩ : syracuseStep 2363023 = 3544535) B3544535
theorem B71724851 : Blo 1865634 71724851 := bstep (se 1 (by rfl) ⟨53793638, by rfl⟩ : syracuseStep 71724851 = 107587277) B107587277
theorem B2363195 : Blo 1865634 2363195 := bstep (se 1 (by rfl) ⟨1772396, by rfl⟩ : syracuseStep 2363195 = 3544793) B3544793
theorem B12767129 : Blo 1865634 12767129 := bstep (se 2 (by rfl) ⟨4787673, by rfl⟩ : syracuseStep 12767129 = 9575347) B9575347
theorem B46043149 : Blo 1865634 46043149 := bstep (se 3 (by rfl) ⟨8633090, by rfl⟩ : syracuseStep 46043149 = 17266181) B17266181
theorem B11956247 : Blo 1865634 11956247 := bstep (se 1 (by rfl) ⟨8967185, by rfl⟩ : syracuseStep 11956247 = 17934371) B17934371
theorem B3149867 : Blo 1865634 3149867 := bstep (se 1 (by rfl) ⟨2362400, by rfl⟩ : syracuseStep 3149867 = 4724801) B4724801
theorem B4198535 : Blo 1865634 4198535 := bstep (se 1 (by rfl) ⟨3148901, by rfl⟩ : syracuseStep 4198535 = 6297803) B6297803
theorem B4788371 : Blo 1865634 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B7975169 : Blo 1865634 7975169 := bstep (se 2 (by rfl) ⟨2990688, by rfl⟩ : syracuseStep 7975169 = 5981377) B5981377
theorem B10629413 : Blo 1865634 10629413 := bstep (se 4 (by rfl) ⟨996507, by rfl⟩ : syracuseStep 10629413 = 1993015) B1993015
theorem B4485419 : Blo 1865634 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B4198715 : Blo 1865634 4198715 := bstep (se 1 (by rfl) ⟨3149036, by rfl⟩ : syracuseStep 4198715 = 6298073) B6298073
theorem B4198841 : Blo 1865634 4198841 := bstep (se 2 (by rfl) ⟨1574565, by rfl⟩ : syracuseStep 4198841 = 3149131) B3149131
theorem B3150265 : Blo 1865634 3150265 := bstep (se 2 (by rfl) ⟨1181349, by rfl⟩ : syracuseStep 3150265 = 2362699) B2362699
theorem B8966609 : Blo 1865634 8966609 := bstep (se 2 (by rfl) ⟨3362478, by rfl⟩ : syracuseStep 8966609 = 6724957) B6724957
theorem B9089489 : Blo 1865634 9089489 := bstep (se 2 (by rfl) ⟨3408558, by rfl⟩ : syracuseStep 9089489 = 6817117) B6817117
theorem B4723211 : Blo 1865634 4723211 := bstep (se 1 (by rfl) ⟨3542408, by rfl⟩ : syracuseStep 4723211 = 7084817) B7084817
theorem B21254723 : Blo 1865634 21254723 := bstep (se 1 (by rfl) ⟨15941042, by rfl⟩ : syracuseStep 21254723 = 31882085) B31882085
theorem B15946307 : Blo 1865634 15946307 := bstep (se 1 (by rfl) ⟨11959730, by rfl⟩ : syracuseStep 15946307 = 23919461) B23919461
theorem B2839159 : Blo 1865634 2839159 := bstep (se 1 (by rfl) ⟨2129369, by rfl⟩ : syracuseStep 2839159 = 4258739) B4258739
theorem B4199183 : Blo 1865634 4199183 := bstep (se 1 (by rfl) ⟨3149387, by rfl⟩ : syracuseStep 4199183 = 6298775) B6298775
theorem B4199201 : Blo 1865634 4199201 := bstep (se 2 (by rfl) ⟨1574700, by rfl⟩ : syracuseStep 4199201 = 3149401) B3149401
theorem B3543851 : Blo 1865634 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B4485947 : Blo 1865634 4485947 := bstep (se 1 (by rfl) ⟨3364460, by rfl⟩ : syracuseStep 4485947 = 6728921) B6728921
theorem B2798471 : Blo 1865634 2798471 := bstep (se 1 (by rfl) ⟨2098853, by rfl⟩ : syracuseStep 2798471 = 4197707) B4197707
theorem B2798507 : Blo 1865634 2798507 := bstep (se 1 (by rfl) ⟨2098880, by rfl⟩ : syracuseStep 2798507 = 4197761) B4197761
theorem B2798537 : Blo 1865634 2798537 := bstep (se 2 (by rfl) ⟨1049451, by rfl⟩ : syracuseStep 2798537 = 2098903) B2098903
theorem B2241527 : Blo 1865634 2241527 := bstep (se 1 (by rfl) ⟨1681145, by rfl⟩ : syracuseStep 2241527 = 3362291) B3362291
theorem B3593249 : Blo 1865634 3593249 := bstep (se 2 (by rfl) ⟨1347468, by rfl⟩ : syracuseStep 3593249 = 2694937) B2694937
theorem B10630187 : Blo 1865634 10630187 := bstep (se 1 (by rfl) ⟨7972640, by rfl⟩ : syracuseStep 10630187 = 15945281) B15945281
theorem B4486187 : Blo 1865634 4486187 := bstep (se 1 (by rfl) ⟨3364640, by rfl⟩ : syracuseStep 4486187 = 6729281) B6729281
theorem B2798651 : Blo 1865634 2798651 := bstep (se 1 (by rfl) ⟨2098988, by rfl⟩ : syracuseStep 2798651 = 4197977) B4197977
theorem B3986491 : Blo 1865634 3986491 := bstep (se 1 (by rfl) ⟨2989868, by rfl⟩ : syracuseStep 3986491 = 5979737) B5979737
theorem B2798711 : Blo 1865634 2798711 := bstep (se 1 (by rfl) ⟨2099033, by rfl⟩ : syracuseStep 2798711 = 4198067) B4198067
theorem B4199543 : Blo 1865634 4199543 := bstep (se 1 (by rfl) ⟨3149657, by rfl⟩ : syracuseStep 4199543 = 6299315) B6299315
theorem B3150967 : Blo 1865634 3150967 := bstep (se 1 (by rfl) ⟨2363225, by rfl⟩ : syracuseStep 3150967 = 4726451) B4726451
theorem B5313671 : Blo 1865634 5313671 := bstep (se 1 (by rfl) ⟨3985253, by rfl⟩ : syracuseStep 5313671 = 7970507) B7970507
theorem B2798735 : Blo 1865634 2798735 := bstep (se 1 (by rfl) ⟨2099051, by rfl⟩ : syracuseStep 2798735 = 4198103) B4198103
theorem B4723859 : Blo 1865634 4723859 := bstep (se 1 (by rfl) ⟨3542894, by rfl⟩ : syracuseStep 4723859 = 7085789) B7085789
theorem B2798777 : Blo 1865634 2798777 := bstep (se 2 (by rfl) ⟨1049541, by rfl⟩ : syracuseStep 2798777 = 2099083) B2099083
theorem B6296777 : Blo 1865634 6296777 := bstep (se 2 (by rfl) ⟨2361291, by rfl⟩ : syracuseStep 6296777 = 4722583) B4722583
theorem B2798855 : Blo 1865634 2798855 := bstep (se 1 (by rfl) ⟨2099141, by rfl⟩ : syracuseStep 2798855 = 4198283) B4198283
theorem B2798891 : Blo 1865634 2798891 := bstep (se 1 (by rfl) ⟨2099168, by rfl⟩ : syracuseStep 2798891 = 4198337) B4198337
theorem B4199723 : Blo 1865634 4199723 := bstep (se 1 (by rfl) ⟨3149792, by rfl⟩ : syracuseStep 4199723 = 6299585) B6299585
theorem B3151163 : Blo 1865634 3151163 := bstep (se 1 (by rfl) ⟨2363372, by rfl⟩ : syracuseStep 3151163 = 4726745) B4726745
theorem B2798921 : Blo 1865634 2798921 := bstep (se 2 (by rfl) ⟨1049595, by rfl⟩ : syracuseStep 2798921 = 2099191) B2099191
theorem B4724153 : Blo 1865634 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B2799035 : Blo 1865634 2799035 := bstep (se 1 (by rfl) ⟨2099276, by rfl⟩ : syracuseStep 2799035 = 4198553) B4198553
theorem B2799095 : Blo 1865634 2799095 := bstep (se 1 (by rfl) ⟨2099321, by rfl⟩ : syracuseStep 2799095 = 4198643) B4198643
theorem B2799119 : Blo 1865634 2799119 := bstep (se 1 (by rfl) ⟨2099339, by rfl⟩ : syracuseStep 2799119 = 4198679) B4198679
theorem B2799161 : Blo 1865634 2799161 := bstep (se 2 (by rfl) ⟨1049685, by rfl⟩ : syracuseStep 2799161 = 2099371) B2099371
theorem B2799239 : Blo 1865634 2799239 := bstep (se 1 (by rfl) ⟨2099429, by rfl⟩ : syracuseStep 2799239 = 4198859) B4198859
theorem B4200083 : Blo 1865634 4200083 := bstep (se 1 (by rfl) ⟨3150062, by rfl⟩ : syracuseStep 4200083 = 6300125) B6300125
theorem B2799275 : Blo 1865634 2799275 := bstep (se 1 (by rfl) ⟨2099456, by rfl⟩ : syracuseStep 2799275 = 4198913) B4198913
theorem B2799305 : Blo 1865634 2799305 := bstep (se 2 (by rfl) ⟨1049739, by rfl⟩ : syracuseStep 2799305 = 2099479) B2099479
theorem B4200137 : Blo 1865634 4200137 := bstep (se 2 (by rfl) ⟨1575051, by rfl⟩ : syracuseStep 4200137 = 3150103) B3150103
theorem B3151561 : Blo 1865634 3151561 := bstep (se 2 (by rfl) ⟨1181835, by rfl⟩ : syracuseStep 3151561 = 2363671) B2363671
theorem B5314319 : Blo 1865634 5314319 := bstep (se 1 (by rfl) ⟨3985739, by rfl⟩ : syracuseStep 5314319 = 7971479) B7971479
theorem B2799419 : Blo 1865634 2799419 := bstep (se 1 (by rfl) ⟨2099564, by rfl⟩ : syracuseStep 2799419 = 4199129) B4199129
theorem B2799479 : Blo 1865634 2799479 := bstep (se 1 (by rfl) ⟨2099609, by rfl⟩ : syracuseStep 2799479 = 4199219) B4199219
theorem B6297479 : Blo 1865634 6297479 := bstep (se 1 (by rfl) ⟨4723109, by rfl⟩ : syracuseStep 6297479 = 9446219) B9446219
theorem B2799503 : Blo 1865634 2799503 := bstep (se 1 (by rfl) ⟨2099627, by rfl⟩ : syracuseStep 2799503 = 4199255) B4199255
theorem B23918489 : Blo 1865634 23918489 := bstep (se 2 (by rfl) ⟨8969433, by rfl⟩ : syracuseStep 23918489 = 17938867) B17938867
theorem B2799545 : Blo 1865634 2799545 := bstep (se 2 (by rfl) ⟨1049829, by rfl⟩ : syracuseStep 2799545 = 2099659) B2099659
theorem B1865659 : Blo 1865634 1865659 := bstep (se 1 (by rfl) ⟨1399244, by rfl⟩ : syracuseStep 1865659 = 2798489) B2798489
theorem B1865735 : Blo 1865634 1865735 := bstep (se 1 (by rfl) ⟨1399301, by rfl⟩ : syracuseStep 1865735 = 2798603) B2798603
theorem B2799623 : Blo 1865634 2799623 := bstep (se 1 (by rfl) ⟨2099717, by rfl⟩ : syracuseStep 2799623 = 4199435) B4199435
theorem B7084043 : Blo 1865634 7084043 := bstep (se 1 (by rfl) ⟨5313032, by rfl⟩ : syracuseStep 7084043 = 10626065) B10626065
theorem B1865743 : Blo 1865634 1865743 := bstep (se 1 (by rfl) ⟨1399307, by rfl⟩ : syracuseStep 1865743 = 2798615) B2798615
theorem B2799659 : Blo 1865634 2799659 := bstep (se 1 (by rfl) ⟨2099744, by rfl⟩ : syracuseStep 2799659 = 4199489) B4199489
theorem B1865787 : Blo 1865634 1865787 := bstep (se 1 (by rfl) ⟨1399340, by rfl⟩ : syracuseStep 1865787 = 2798681) B2798681
theorem B23009341 : Blo 1865634 23009341 := bstep (se 3 (by rfl) ⟨4314251, by rfl⟩ : syracuseStep 23009341 = 8628503) B8628503
theorem B2799689 : Blo 1865634 2799689 := bstep (se 2 (by rfl) ⟨1049883, by rfl⟩ : syracuseStep 2799689 = 2099767) B2099767
theorem B4724851 : Blo 1865634 4724851 := bstep (se 1 (by rfl) ⟨3543638, by rfl⟩ : syracuseStep 4724851 = 7087277) B7087277
theorem B1865863 : Blo 1865634 1865863 := bstep (se 1 (by rfl) ⟨1399397, by rfl⟩ : syracuseStep 1865863 = 2798795) B2798795
theorem B1865871 : Blo 1865634 1865871 := bstep (se 1 (by rfl) ⟨1399403, by rfl⟩ : syracuseStep 1865871 = 2798807) B2798807
theorem B1865915 : Blo 1865634 1865915 := bstep (se 1 (by rfl) ⟨1399436, by rfl⟩ : syracuseStep 1865915 = 2798873) B2798873
theorem B2799803 : Blo 1865634 2799803 := bstep (se 1 (by rfl) ⟨2099852, by rfl⟩ : syracuseStep 2799803 = 4199705) B4199705
theorem B20191477 : Blo 1865634 20191477 := bstep (se 5 (by rfl) ⟨946475, by rfl⟩ : syracuseStep 20191477 = 1892951) B1892951
theorem B2799863 : Blo 1865634 2799863 := bstep (se 1 (by rfl) ⟨2099897, by rfl⟩ : syracuseStep 2799863 = 4199795) B4199795
theorem B6297857 : Blo 1865634 6297857 := bstep (se 2 (by rfl) ⟨2361696, by rfl⟩ : syracuseStep 6297857 = 4723393) B4723393
theorem B4724993 : Blo 1865634 4724993 := bstep (se 2 (by rfl) ⟨1771872, by rfl⟩ : syracuseStep 4724993 = 3543745) B3543745
theorem B1865991 : Blo 1865634 1865991 := bstep (se 1 (by rfl) ⟨1399493, by rfl⟩ : syracuseStep 1865991 = 2798987) B2798987
theorem B1865999 : Blo 1865634 1865999 := bstep (se 1 (by rfl) ⟨1399499, by rfl⟩ : syracuseStep 1865999 = 2798999) B2798999
theorem B2799887 : Blo 1865634 2799887 := bstep (se 1 (by rfl) ⟨2099915, by rfl⟩ : syracuseStep 2799887 = 4199831) B4199831
theorem B3365153 : Blo 1865634 3365153 := bstep (se 2 (by rfl) ⟨1261932, by rfl⟩ : syracuseStep 3365153 = 2523865) B2523865
theorem B2799929 : Blo 1865634 2799929 := bstep (se 2 (by rfl) ⟨1049973, by rfl⟩ : syracuseStep 2799929 = 2099947) B2099947
theorem B1866043 : Blo 1865634 1866043 := bstep (se 1 (by rfl) ⟨1399532, by rfl⟩ : syracuseStep 1866043 = 2799065) B2799065
theorem B4544903 : Blo 1865634 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B1866119 : Blo 1865634 1866119 := bstep (se 1 (by rfl) ⟨1399589, by rfl⟩ : syracuseStep 1866119 = 2799179) B2799179
theorem B2800007 : Blo 1865634 2800007 := bstep (se 1 (by rfl) ⟨2100005, by rfl⟩ : syracuseStep 2800007 = 4200011) B4200011
theorem B4200839 : Blo 1865634 4200839 := bstep (se 1 (by rfl) ⟨3150629, by rfl⟩ : syracuseStep 4200839 = 6301259) B6301259
theorem B1866127 : Blo 1865634 1866127 := bstep (se 1 (by rfl) ⟨1399595, by rfl⟩ : syracuseStep 1866127 = 2799191) B2799191
theorem B2800043 : Blo 1865634 2800043 := bstep (se 1 (by rfl) ⟨2100032, by rfl⟩ : syracuseStep 2800043 = 4200065) B4200065
theorem B1866171 : Blo 1865634 1866171 := bstep (se 1 (by rfl) ⟨1399628, by rfl⟩ : syracuseStep 1866171 = 2799257) B2799257
theorem B2800073 : Blo 1865634 2800073 := bstep (se 2 (by rfl) ⟨1050027, by rfl⟩ : syracuseStep 2800073 = 2100055) B2100055
theorem B3545545 : Blo 1865634 3545545 := bstep (se 2 (by rfl) ⟨1329579, by rfl⟩ : syracuseStep 3545545 = 2659159) B2659159
theorem B10631645 : Blo 1865634 10631645 := bstep (se 3 (by rfl) ⟨1993433, by rfl⟩ : syracuseStep 10631645 = 3986867) B3986867
theorem B1866247 : Blo 1865634 1866247 := bstep (se 1 (by rfl) ⟨1399685, by rfl⟩ : syracuseStep 1866247 = 2799371) B2799371
theorem B3029519 : Blo 1865634 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B1866255 : Blo 1865634 1866255 := bstep (se 1 (by rfl) ⟨1399691, by rfl⟩ : syracuseStep 1866255 = 2799383) B2799383
theorem B2988587 : Blo 1865634 2988587 := bstep (se 1 (by rfl) ⟨2241440, by rfl⟩ : syracuseStep 2988587 = 4482881) B4482881
theorem B1866299 : Blo 1865634 1866299 := bstep (se 1 (by rfl) ⟨1399724, by rfl⟩ : syracuseStep 1866299 = 2799449) B2799449
theorem B2800187 : Blo 1865634 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B5388859 : Blo 1865634 5388859 := bstep (se 1 (by rfl) ⟨4041644, by rfl⟩ : syracuseStep 5388859 = 8083289) B8083289
theorem B4201019 : Blo 1865634 4201019 := bstep (se 1 (by rfl) ⟨3150764, by rfl⟩ : syracuseStep 4201019 = 6301529) B6301529
theorem B13457987 : Blo 1865634 13457987 := bstep (se 1 (by rfl) ⟨10093490, by rfl⟩ : syracuseStep 13457987 = 20186981) B20186981
theorem B2800247 : Blo 1865634 2800247 := bstep (se 1 (by rfl) ⟨2100185, by rfl⟩ : syracuseStep 2800247 = 4200371) B4200371
theorem B1866375 : Blo 1865634 1866375 := bstep (se 1 (by rfl) ⟨1399781, by rfl⟩ : syracuseStep 1866375 = 2799563) B2799563
theorem B1866383 : Blo 1865634 1866383 := bstep (se 1 (by rfl) ⟨1399787, by rfl⟩ : syracuseStep 1866383 = 2799575) B2799575
theorem B2800271 : Blo 1865634 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B8968877 : Blo 1865634 8968877 := bstep (se 3 (by rfl) ⟨1681664, by rfl⟩ : syracuseStep 8968877 = 3363329) B3363329
theorem B2800313 : Blo 1865634 2800313 := bstep (se 2 (by rfl) ⟨1050117, by rfl⟩ : syracuseStep 2800313 = 2100235) B2100235
theorem B4201145 : Blo 1865634 4201145 := bstep (se 2 (by rfl) ⟨1575429, by rfl⟩ : syracuseStep 4201145 = 3150859) B3150859
theorem B1866427 : Blo 1865634 1866427 := bstep (se 1 (by rfl) ⟨1399820, by rfl⟩ : syracuseStep 1866427 = 2799641) B2799641
theorem B4725449 : Blo 1865634 4725449 := bstep (se 2 (by rfl) ⟨1772043, by rfl⟩ : syracuseStep 4725449 = 3544087) B3544087
theorem B1866503 : Blo 1865634 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B2800391 : Blo 1865634 2800391 := bstep (se 1 (by rfl) ⟨2100293, by rfl⟩ : syracuseStep 2800391 = 4200587) B4200587
theorem B1866511 : Blo 1865634 1866511 := bstep (se 1 (by rfl) ⟨1399883, by rfl⟩ : syracuseStep 1866511 = 2799767) B2799767
theorem B2800427 : Blo 1865634 2800427 := bstep (se 1 (by rfl) ⟨2100320, by rfl⟩ : syracuseStep 2800427 = 4200641) B4200641
theorem B1866555 : Blo 1865634 1866555 := bstep (se 1 (by rfl) ⟨1399916, by rfl⟩ : syracuseStep 1866555 = 2799833) B2799833
theorem B10230587 : Blo 1865634 10230587 := bstep (se 1 (by rfl) ⟨7672940, by rfl⟩ : syracuseStep 10230587 = 15345881) B15345881
theorem B2800457 : Blo 1865634 2800457 := bstep (se 2 (by rfl) ⟨1050171, by rfl⟩ : syracuseStep 2800457 = 2100343) B2100343
theorem B1866631 : Blo 1865634 1866631 := bstep (se 1 (by rfl) ⟨1399973, by rfl⟩ : syracuseStep 1866631 = 2799947) B2799947
theorem B1866639 : Blo 1865634 1866639 := bstep (se 1 (by rfl) ⟨1399979, by rfl⟩ : syracuseStep 1866639 = 2799959) B2799959
theorem B15948697 : Blo 1865634 15948697 := bstep (se 2 (by rfl) ⟨5980761, by rfl⟩ : syracuseStep 15948697 = 11961523) B11961523
theorem B1866683 : Blo 1865634 1866683 := bstep (se 1 (by rfl) ⟨1400012, by rfl⟩ : syracuseStep 1866683 = 2800025) B2800025
theorem B2800571 : Blo 1865634 2800571 := bstep (se 1 (by rfl) ⟨2100428, by rfl⟩ : syracuseStep 2800571 = 4200857) B4200857
theorem B2800631 : Blo 1865634 2800631 := bstep (se 1 (by rfl) ⟨2100473, by rfl⟩ : syracuseStep 2800631 = 4200947) B4200947
theorem B1866759 : Blo 1865634 1866759 := bstep (se 1 (by rfl) ⟨1400069, by rfl⟩ : syracuseStep 1866759 = 2800139) B2800139
theorem B1866767 : Blo 1865634 1866767 := bstep (se 1 (by rfl) ⟨1400075, by rfl⟩ : syracuseStep 1866767 = 2800151) B2800151
theorem B2800655 : Blo 1865634 2800655 := bstep (se 1 (by rfl) ⟨2100491, by rfl⟩ : syracuseStep 2800655 = 4200983) B4200983
theorem B4201487 : Blo 1865634 4201487 := bstep (se 1 (by rfl) ⟨3151115, by rfl⟩ : syracuseStep 4201487 = 6302231) B6302231
theorem B4201505 : Blo 1865634 4201505 := bstep (se 2 (by rfl) ⟨1575564, by rfl⟩ : syracuseStep 4201505 = 3151129) B3151129
theorem B6298667 : Blo 1865634 6298667 := bstep (se 1 (by rfl) ⟨4724000, by rfl⟩ : syracuseStep 6298667 = 9448001) B9448001
theorem B4725803 : Blo 1865634 4725803 := bstep (se 1 (by rfl) ⟨3544352, by rfl⟩ : syracuseStep 4725803 = 7088705) B7088705
theorem B2800697 : Blo 1865634 2800697 := bstep (se 2 (by rfl) ⟨1050261, by rfl⟩ : syracuseStep 2800697 = 2100523) B2100523
theorem B1866811 : Blo 1865634 1866811 := bstep (se 1 (by rfl) ⟨1400108, by rfl⟩ : syracuseStep 1866811 = 2800217) B2800217
theorem B1866887 : Blo 1865634 1866887 := bstep (se 1 (by rfl) ⟨1400165, by rfl⟩ : syracuseStep 1866887 = 2800331) B2800331
theorem B2800775 : Blo 1865634 2800775 := bstep (se 1 (by rfl) ⟨2100581, by rfl⟩ : syracuseStep 2800775 = 4201163) B4201163
theorem B1866895 : Blo 1865634 1866895 := bstep (se 1 (by rfl) ⟨1400171, by rfl⟩ : syracuseStep 1866895 = 2800343) B2800343
theorem B3783827 : Blo 1865634 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B2800811 : Blo 1865634 2800811 := bstep (se 1 (by rfl) ⟨2100608, by rfl⟩ : syracuseStep 2800811 = 4201217) B4201217
theorem B1866939 : Blo 1865634 1866939 := bstep (se 1 (by rfl) ⟨1400204, by rfl⟩ : syracuseStep 1866939 = 2800409) B2800409
theorem B153246917 : Blo 1865634 153246917 := bstep (se 4 (by rfl) ⟨14366898, by rfl⟩ : syracuseStep 153246917 = 28733797) B28733797
theorem B2800841 : Blo 1865634 2800841 := bstep (se 2 (by rfl) ⟨1050315, by rfl⟩ : syracuseStep 2800841 = 2100631) B2100631
theorem B8969453 : Blo 1865634 8969453 := bstep (se 3 (by rfl) ⟨1681772, by rfl⟩ : syracuseStep 8969453 = 3363545) B3363545
theorem B1867015 : Blo 1865634 1867015 := bstep (se 1 (by rfl) ⟨1400261, by rfl⟩ : syracuseStep 1867015 = 2800523) B2800523
theorem B1867023 : Blo 1865634 1867023 := bstep (se 1 (by rfl) ⟨1400267, by rfl⟩ : syracuseStep 1867023 = 2800535) B2800535
theorem B1867067 : Blo 1865634 1867067 := bstep (se 1 (by rfl) ⟨1400300, by rfl⟩ : syracuseStep 1867067 = 2800601) B2800601
theorem B2800955 : Blo 1865634 2800955 := bstep (se 1 (by rfl) ⟨2100716, by rfl⟩ : syracuseStep 2800955 = 4201433) B4201433
theorem B53845307 : Blo 1865634 53845307 := bstep (se 1 (by rfl) ⟨40383980, by rfl⟩ : syracuseStep 53845307 = 80767961) B80767961
theorem B5315959 : Blo 1865634 5315959 := bstep (se 1 (by rfl) ⟨3986969, by rfl⟩ : syracuseStep 5315959 = 7973939) B7973939
theorem B2801015 : Blo 1865634 2801015 := bstep (se 1 (by rfl) ⟨2100761, by rfl⟩ : syracuseStep 2801015 = 4201523) B4201523
theorem B4201847 : Blo 1865634 4201847 := bstep (se 1 (by rfl) ⟨3151385, by rfl⟩ : syracuseStep 4201847 = 6302771) B6302771
theorem B1867143 : Blo 1865634 1867143 := bstep (se 1 (by rfl) ⟨1400357, by rfl⟩ : syracuseStep 1867143 = 2800715) B2800715
theorem B1867151 : Blo 1865634 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B2801039 : Blo 1865634 2801039 := bstep (se 1 (by rfl) ⟨2100779, by rfl⟩ : syracuseStep 2801039 = 4201559) B4201559
theorem B2801081 : Blo 1865634 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B1867195 : Blo 1865634 1867195 := bstep (se 1 (by rfl) ⟨1400396, by rfl⟩ : syracuseStep 1867195 = 2800793) B2800793
theorem B2522615 : Blo 1865634 2522615 := bstep (se 1 (by rfl) ⟨1891961, by rfl⟩ : syracuseStep 2522615 = 3783923) B3783923
theorem B1867271 : Blo 1865634 1867271 := bstep (se 1 (by rfl) ⟨1400453, by rfl⟩ : syracuseStep 1867271 = 2800907) B2800907
theorem B2801159 : Blo 1865634 2801159 := bstep (se 1 (by rfl) ⟨2100869, by rfl⟩ : syracuseStep 2801159 = 4201739) B4201739
theorem B1867279 : Blo 1865634 1867279 := bstep (se 1 (by rfl) ⟨1400459, by rfl⟩ : syracuseStep 1867279 = 2800919) B2800919
theorem B2801195 : Blo 1865634 2801195 := bstep (se 1 (by rfl) ⟨2100896, by rfl⟩ : syracuseStep 2801195 = 4201793) B4201793
theorem B4202027 : Blo 1865634 4202027 := bstep (se 1 (by rfl) ⟨3151520, by rfl⟩ : syracuseStep 4202027 = 6303041) B6303041
theorem B1867323 : Blo 1865634 1867323 := bstep (se 1 (by rfl) ⟨1400492, by rfl⟩ : syracuseStep 1867323 = 2800985) B2800985
theorem B2801225 : Blo 1865634 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B1867399 : Blo 1865634 1867399 := bstep (se 1 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 1867399 = 2801099) B2801099
theorem B1867407 : Blo 1865634 1867407 := bstep (se 1 (by rfl) ⟨1400555, by rfl⟩ : syracuseStep 1867407 = 2801111) B2801111
theorem B1867451 : Blo 1865634 1867451 := bstep (se 1 (by rfl) ⟨1400588, by rfl⟩ : syracuseStep 1867451 = 2801177) B2801177
theorem B2801339 : Blo 1865634 2801339 := bstep (se 1 (by rfl) ⟨2101004, by rfl⟩ : syracuseStep 2801339 = 4202009) B4202009
theorem B2801399 : Blo 1865634 2801399 := bstep (se 1 (by rfl) ⟨2101049, by rfl⟩ : syracuseStep 2801399 = 4202099) B4202099
theorem B1867527 : Blo 1865634 1867527 := bstep (se 1 (by rfl) ⟨1400645, by rfl⟩ : syracuseStep 1867527 = 2801291) B2801291
theorem B1867535 : Blo 1865634 1867535 := bstep (se 1 (by rfl) ⟨1400651, by rfl⟩ : syracuseStep 1867535 = 2801303) B2801303
theorem B2801423 : Blo 1865634 2801423 := bstep (se 1 (by rfl) ⟨2101067, by rfl⟩ : syracuseStep 2801423 = 4202135) B4202135
theorem B1867579 : Blo 1865634 1867579 := bstep (se 1 (by rfl) ⟨1400684, by rfl⟩ : syracuseStep 1867579 = 2801369) B2801369
theorem B7970831 : Blo 1865634 7970831 := bstep (se 1 (by rfl) ⟨5978123, by rfl⟩ : syracuseStep 7970831 = 11956247) B11956247
theorem B61390865 : Blo 1865634 61390865 := bstep (se 2 (by rfl) ⟨23021574, by rfl⟩ : syracuseStep 61390865 = 46043149) B46043149
theorem B30679121 : Blo 1865634 30679121 := bstep (se 2 (by rfl) ⟨11504670, by rfl⟩ : syracuseStep 30679121 = 23009341) B23009341
theorem B6299801 : Blo 1865634 6299801 := bstep (se 2 (by rfl) ⟨2362425, by rfl⟩ : syracuseStep 6299801 = 4724851) B4724851
theorem B5316779 : Blo 1865634 5316779 := bstep (se 1 (by rfl) ⟨3987584, by rfl⟩ : syracuseStep 5316779 = 7975169) B7975169
theorem B7086275 : Blo 1865634 7086275 := bstep (se 1 (by rfl) ⟨5314706, by rfl⟩ : syracuseStep 7086275 = 10629413) B10629413
theorem B2990279 : Blo 1865634 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B17023243 : Blo 1865634 17023243 := bstep (se 1 (by rfl) ⟨12767432, by rfl⟩ : syracuseStep 17023243 = 25534865) B25534865
theorem B14369035 : Blo 1865634 14369035 := bstep (se 1 (by rfl) ⟨10776776, by rfl⟩ : syracuseStep 14369035 = 21553553) B21553553
theorem B15139133 : Blo 1865634 15139133 := bstep (se 3 (by rfl) ⟨2838587, by rfl⟩ : syracuseStep 15139133 = 5677175) B5677175
theorem B5980711 : Blo 1865634 5980711 := bstep (se 1 (by rfl) ⟨4485533, by rfl⟩ : syracuseStep 5980711 = 8971067) B8971067
theorem B14172731 : Blo 1865634 14172731 := bstep (se 1 (by rfl) ⟨10629548, by rfl⟩ : syracuseStep 14172731 = 21259097) B21259097
theorem B10633787 : Blo 1865634 10633787 := bstep (se 1 (by rfl) ⟨7975340, by rfl⟩ : syracuseStep 10633787 = 15950681) B15950681
theorem B4727393 : Blo 1865634 4727393 := bstep (se 2 (by rfl) ⟨1772772, by rfl⟩ : syracuseStep 4727393 = 3545545) B3545545
theorem B7086791 : Blo 1865634 7086791 := bstep (se 1 (by rfl) ⟨5315093, by rfl⟩ : syracuseStep 7086791 = 10630187) B10630187
theorem B2990791 : Blo 1865634 2990791 := bstep (se 1 (by rfl) ⟨2243093, by rfl⟩ : syracuseStep 2990791 = 4486187) B4486187
theorem B13451987 : Blo 1865634 13451987 := bstep (se 1 (by rfl) ⟨10088990, by rfl⟩ : syracuseStep 13451987 = 20177981) B20177981
theorem B7185145 : Blo 1865634 7185145 := bstep (se 2 (by rfl) ⟨2694429, by rfl⟩ : syracuseStep 7185145 = 5388859) B5388859
theorem B3785545 : Blo 1865634 3785545 := bstep (se 2 (by rfl) ⟨1419579, by rfl⟩ : syracuseStep 3785545 = 2839159) B2839159
theorem B92070917 : Blo 1865634 92070917 := bstep (se 4 (by rfl) ⟨8631648, by rfl⟩ : syracuseStep 92070917 = 17263297) B17263297
theorem B9454643 : Blo 1865634 9454643 := bstep (se 1 (by rfl) ⟨7090982, by rfl⟩ : syracuseStep 9454643 = 14181965) B14181965
theorem B6726973 : Blo 1865634 6726973 := bstep (se 3 (by rfl) ⟨1261307, by rfl⟩ : syracuseStep 6726973 = 2522615) B2522615
theorem B6300989 : Blo 1865634 6300989 := bstep (se 3 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 6300989 = 2362871) B2362871
theorem B8078717 : Blo 1865634 8078717 := bstep (se 3 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 8078717 = 3029519) B3029519
theorem B7087763 : Blo 1865634 7087763 := bstep (se 1 (by rfl) ⟨5315822, by rfl⟩ : syracuseStep 7087763 = 10631645) B10631645
theorem B45434515 : Blo 1865634 45434515 := bstep (se 1 (by rfl) ⟨34075886, by rfl⟩ : syracuseStep 45434515 = 68151773) B68151773
theorem B8971991 : Blo 1865634 8971991 := bstep (se 1 (by rfl) ⟨6728993, by rfl⟩ : syracuseStep 8971991 = 13457987) B13457987
theorem B23004971 : Blo 1865634 23004971 := bstep (se 1 (by rfl) ⟨17253728, by rfl⟩ : syracuseStep 23004971 = 34507457) B34507457
theorem B7087945 : Blo 1865634 7087945 := bstep (se 2 (by rfl) ⟨2657979, by rfl⟩ : syracuseStep 7087945 = 5315959) B5315959
theorem B2099119 : Blo 1865634 2099119 := bstep (se 1 (by rfl) ⟨1574339, by rfl⟩ : syracuseStep 2099119 = 3148679) B3148679
theorem B2361307 : Blo 1865634 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B30279683 : Blo 1865634 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B102164611 : Blo 1865634 102164611 := bstep (se 1 (by rfl) ⟨76623458, by rfl⟩ : syracuseStep 102164611 = 153246917) B153246917
theorem B7571609 : Blo 1865634 7571609 := bstep (se 2 (by rfl) ⟨2839353, by rfl⟩ : syracuseStep 7571609 = 5678707) B5678707
theorem B11962525 : Blo 1865634 11962525 := bstep (se 3 (by rfl) ⟨2242973, by rfl⟩ : syracuseStep 11962525 = 4485947) B4485947
theorem B6301853 : Blo 1865634 6301853 := bstep (se 3 (by rfl) ⟨1181597, by rfl⟩ : syracuseStep 6301853 = 2363195) B2363195
theorem B2099551 : Blo 1865634 2099551 := bstep (se 1 (by rfl) ⟨1574663, by rfl⟩ : syracuseStep 2099551 = 3149327) B3149327
theorem B5982607 : Blo 1865634 5982607 := bstep (se 1 (by rfl) ⟨4486955, by rfl⟩ : syracuseStep 5982607 = 8973911) B8973911
theorem B11954861 : Blo 1865634 11954861 := bstep (se 3 (by rfl) ⟨2241536, by rfl⟩ : syracuseStep 11954861 = 4483073) B4483073
theorem B6302393 : Blo 1865634 6302393 := bstep (se 2 (by rfl) ⟨2363397, by rfl⟩ : syracuseStep 6302393 = 4726795) B4726795
theorem B2099911 : Blo 1865634 2099911 := bstep (se 1 (by rfl) ⟨1574933, by rfl⟩ : syracuseStep 2099911 = 3149867) B3149867
theorem B4483795 : Blo 1865634 4483795 := bstep (se 1 (by rfl) ⟨3362846, by rfl⟩ : syracuseStep 4483795 = 6725693) B6725693
theorem B97004249 : Blo 1865634 97004249 := bstep (se 2 (by rfl) ⟨36376593, by rfl⟩ : syracuseStep 97004249 = 72753187) B72753187
theorem B3148537 : Blo 1865634 3148537 := bstep (se 2 (by rfl) ⟨1180701, by rfl⟩ : syracuseStep 3148537 = 2361403) B2361403
theorem B26921969 : Blo 1865634 26921969 := bstep (se 2 (by rfl) ⟨10095738, by rfl⟩ : syracuseStep 26921969 = 20191477) B20191477
theorem B3148807 : Blo 1865634 3148807 := bstep (se 1 (by rfl) ⟨2361605, by rfl⟩ : syracuseStep 3148807 = 4723211) B4723211
theorem B6728761 : Blo 1865634 6728761 := bstep (se 2 (by rfl) ⟨2523285, by rfl⟩ : syracuseStep 6728761 = 5046571) B5046571
theorem B6302987 : Blo 1865634 6302987 := bstep (se 1 (by rfl) ⟨4727240, by rfl⟩ : syracuseStep 6302987 = 9454481) B9454481
theorem B14167385 : Blo 1865634 14167385 := bstep (se 2 (by rfl) ⟨5312769, by rfl⟩ : syracuseStep 14167385 = 10625539) B10625539
theorem B2395499 : Blo 1865634 2395499 := bstep (se 1 (by rfl) ⟨1796624, by rfl⟩ : syracuseStep 2395499 = 3593249) B3593249
theorem B4484495 : Blo 1865634 4484495 := bstep (se 1 (by rfl) ⟨3363371, by rfl⟩ : syracuseStep 4484495 = 6726743) B6726743
theorem B3542447 : Blo 1865634 3542447 := bstep (se 1 (by rfl) ⟨2656835, by rfl⟩ : syracuseStep 3542447 = 5313671) B5313671
theorem B3149239 : Blo 1865634 3149239 := bstep (se 1 (by rfl) ⟨2361929, by rfl⟩ : syracuseStep 3149239 = 4723859) B4723859
theorem B4197851 : Blo 1865634 4197851 := bstep (se 1 (by rfl) ⟨3148388, by rfl⟩ : syracuseStep 4197851 = 6296777) B6296777
theorem B6303257 : Blo 1865634 6303257 := bstep (se 2 (by rfl) ⟨2363721, by rfl⟩ : syracuseStep 6303257 = 4727443) B4727443
theorem B2100775 : Blo 1865634 2100775 := bstep (se 1 (by rfl) ⟨1575581, by rfl⟩ : syracuseStep 2100775 = 3151163) B3151163
theorem B3149435 : Blo 1865634 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B21262013 : Blo 1865634 21262013 := bstep (se 3 (by rfl) ⟨3986627, by rfl⟩ : syracuseStep 21262013 = 7973255) B7973255
theorem B7089875 : Blo 1865634 7089875 := bstep (se 1 (by rfl) ⟨5317406, by rfl⟩ : syracuseStep 7089875 = 10634813) B10634813
theorem B3542879 : Blo 1865634 3542879 := bstep (se 1 (by rfl) ⟨2657159, by rfl⟩ : syracuseStep 3542879 = 5314319) B5314319
theorem B34074503 : Blo 1865634 34074503 := bstep (se 1 (by rfl) ⟨25555877, by rfl⟩ : syracuseStep 34074503 = 51111755) B51111755
theorem B4198319 : Blo 1865634 4198319 := bstep (se 1 (by rfl) ⟨3148739, by rfl⟩ : syracuseStep 4198319 = 6297479) B6297479
theorem B15945659 : Blo 1865634 15945659 := bstep (se 1 (by rfl) ⟨11959244, by rfl⟩ : syracuseStep 15945659 = 23918489) B23918489
theorem B4722695 : Blo 1865634 4722695 := bstep (se 1 (by rfl) ⟨3542021, by rfl⟩ : syracuseStep 4722695 = 7084043) B7084043
theorem B3149833 : Blo 1865634 3149833 := bstep (se 2 (by rfl) ⟨1181187, by rfl⟩ : syracuseStep 3149833 = 2362375) B2362375
theorem B4722745 : Blo 1865634 4722745 := bstep (se 2 (by rfl) ⟨1771029, by rfl⟩ : syracuseStep 4722745 = 3542059) B3542059
theorem B4198571 : Blo 1865634 4198571 := bstep (se 1 (by rfl) ⟨3148928, by rfl⟩ : syracuseStep 4198571 = 6297857) B6297857
theorem B3149995 : Blo 1865634 3149995 := bstep (se 1 (by rfl) ⟨2362496, by rfl⟩ : syracuseStep 3149995 = 4724993) B4724993
theorem B4723049 : Blo 1865634 4723049 := bstep (se 2 (by rfl) ⟨1771143, by rfl⟩ : syracuseStep 4723049 = 3542287) B3542287
theorem B3150299 : Blo 1865634 3150299 := bstep (se 1 (by rfl) ⟨2362724, by rfl⟩ : syracuseStep 3150299 = 4725449) B4725449
theorem B12128777 : Blo 1865634 12128777 := bstep (se 2 (by rfl) ⟨4548291, by rfl⟩ : syracuseStep 12128777 = 9096583) B9096583
theorem B6820391 : Blo 1865634 6820391 := bstep (se 1 (by rfl) ⟨5115293, by rfl⟩ : syracuseStep 6820391 = 10230587) B10230587
theorem B4199111 : Blo 1865634 4199111 := bstep (se 1 (by rfl) ⟨3149333, by rfl⟩ : syracuseStep 4199111 = 6298667) B6298667
theorem B3150535 : Blo 1865634 3150535 := bstep (se 1 (by rfl) ⟨2362901, by rfl⟩ : syracuseStep 3150535 = 4725803) B4725803
theorem B5976791 : Blo 1865634 5976791 := bstep (se 1 (by rfl) ⟨4482593, by rfl⟩ : syracuseStep 5976791 = 8965187) B8965187
theorem B9450269 : Blo 1865634 9450269 := bstep (se 3 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 9450269 = 3543851) B3543851
theorem B3150697 : Blo 1865634 3150697 := bstep (se 2 (by rfl) ⟨1181511, by rfl⟩ : syracuseStep 3150697 = 2363023) B2363023
theorem B4256687 : Blo 1865634 4256687 := bstep (se 1 (by rfl) ⟨3192515, by rfl⟩ : syracuseStep 4256687 = 6385031) B6385031
theorem B2798519 : Blo 1865634 2798519 := bstep (se 1 (by rfl) ⟨2098889, by rfl⟩ : syracuseStep 2798519 = 4197779) B4197779
theorem B2798555 : Blo 1865634 2798555 := bstep (se 1 (by rfl) ⟨2098916, by rfl⟩ : syracuseStep 2798555 = 4197833) B4197833
theorem B30282797 : Blo 1865634 30282797 := bstep (se 3 (by rfl) ⟨5678024, by rfl⟩ : syracuseStep 30282797 = 11356049) B11356049
theorem B5977405 : Blo 1865634 5977405 := bstep (se 3 (by rfl) ⟨1120763, by rfl⟩ : syracuseStep 5977405 = 2241527) B2241527
theorem B12776869 : Blo 1865634 12776869 := bstep (se 4 (by rfl) ⟨1197831, by rfl⟩ : syracuseStep 12776869 = 2395663) B2395663
theorem B2799023 : Blo 1865634 2799023 := bstep (se 1 (by rfl) ⟨2099267, by rfl⟩ : syracuseStep 2799023 = 4198535) B4198535
theorem B3192247 : Blo 1865634 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B3151291 : Blo 1865634 3151291 := bstep (se 1 (by rfl) ⟨2363468, by rfl⟩ : syracuseStep 3151291 = 4726937) B4726937
theorem B2799113 : Blo 1865634 2799113 := bstep (se 2 (by rfl) ⟨1049667, by rfl⟩ : syracuseStep 2799113 = 2099335) B2099335
theorem B3593737 : Blo 1865634 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B2799143 : Blo 1865634 2799143 := bstep (se 1 (by rfl) ⟨2099357, by rfl⟩ : syracuseStep 2799143 = 4198715) B4198715
theorem B4199975 : Blo 1865634 4199975 := bstep (se 1 (by rfl) ⟨3149981, by rfl⟩ : syracuseStep 4199975 = 6299963) B6299963
theorem B3151399 : Blo 1865634 3151399 := bstep (se 1 (by rfl) ⟨2363549, by rfl⟩ : syracuseStep 3151399 = 4727099) B4727099
theorem B2799227 : Blo 1865634 2799227 := bstep (se 1 (by rfl) ⟨2099420, by rfl⟩ : syracuseStep 2799227 = 4198841) B4198841
theorem B5977739 : Blo 1865634 5977739 := bstep (se 1 (by rfl) ⟨4483304, by rfl⟩ : syracuseStep 5977739 = 8966609) B8966609
theorem B6059659 : Blo 1865634 6059659 := bstep (se 1 (by rfl) ⟨4544744, by rfl⟩ : syracuseStep 6059659 = 9089489) B9089489
theorem B14014091 : Blo 1865634 14014091 := bstep (se 1 (by rfl) ⟨10510568, by rfl⟩ : syracuseStep 14014091 = 21021137) B21021137
theorem B14169815 : Blo 1865634 14169815 := bstep (se 1 (by rfl) ⟨10627361, by rfl⟩ : syracuseStep 14169815 = 21254723) B21254723
theorem B10630871 : Blo 1865634 10630871 := bstep (se 1 (by rfl) ⟨7973153, by rfl⟩ : syracuseStep 10630871 = 15946307) B15946307
theorem B3544823 : Blo 1865634 3544823 := bstep (se 1 (by rfl) ⟨2658617, by rfl⟩ : syracuseStep 3544823 = 5317235) B5317235
theorem B2799353 : Blo 1865634 2799353 := bstep (se 2 (by rfl) ⟨1049757, by rfl⟩ : syracuseStep 2799353 = 2099515) B2099515
theorem B2799455 : Blo 1865634 2799455 := bstep (se 1 (by rfl) ⟨2099591, by rfl⟩ : syracuseStep 2799455 = 4199183) B4199183
theorem B2799467 : Blo 1865634 2799467 := bstep (se 1 (by rfl) ⟨2099600, by rfl⟩ : syracuseStep 2799467 = 4199201) B4199201
theorem B4200299 : Blo 1865634 4200299 := bstep (se 1 (by rfl) ⟨3150224, by rfl⟩ : syracuseStep 4200299 = 6300449) B6300449
theorem B3544975 : Blo 1865634 3544975 := bstep (se 1 (by rfl) ⟨2658731, by rfl⟩ : syracuseStep 3544975 = 5317463) B5317463
theorem B4200353 : Blo 1865634 4200353 := bstep (se 2 (by rfl) ⟨1575132, by rfl⟩ : syracuseStep 4200353 = 3150265) B3150265
theorem B1865647 : Blo 1865634 1865647 := bstep (se 1 (by rfl) ⟨1399235, by rfl⟩ : syracuseStep 1865647 = 2798471) B2798471
theorem B1865671 : Blo 1865634 1865671 := bstep (se 1 (by rfl) ⟨1399253, by rfl⟩ : syracuseStep 1865671 = 2798507) B2798507
theorem B1865691 : Blo 1865634 1865691 := bstep (se 1 (by rfl) ⟨1399268, by rfl⟩ : syracuseStep 1865691 = 2798537) B2798537
theorem B1865767 : Blo 1865634 1865767 := bstep (se 1 (by rfl) ⟨1399325, by rfl⟩ : syracuseStep 1865767 = 2798651) B2798651
theorem B1865807 : Blo 1865634 1865807 := bstep (se 1 (by rfl) ⟨1399355, by rfl⟩ : syracuseStep 1865807 = 2798711) B2798711
theorem B2799695 : Blo 1865634 2799695 := bstep (se 1 (by rfl) ⟨2099771, by rfl⟩ : syracuseStep 2799695 = 4199543) B4199543
theorem B1865823 : Blo 1865634 1865823 := bstep (se 1 (by rfl) ⟨1399367, by rfl⟩ : syracuseStep 1865823 = 2798735) B2798735
theorem B1865851 : Blo 1865634 1865851 := bstep (se 1 (by rfl) ⟨1399388, by rfl⟩ : syracuseStep 1865851 = 2798777) B2798777
theorem B1865903 : Blo 1865634 1865903 := bstep (se 1 (by rfl) ⟨1399427, by rfl⟩ : syracuseStep 1865903 = 2798855) B2798855
theorem B1865927 : Blo 1865634 1865927 := bstep (se 1 (by rfl) ⟨1399445, by rfl⟩ : syracuseStep 1865927 = 2798891) B2798891
theorem B2799815 : Blo 1865634 2799815 := bstep (se 1 (by rfl) ⟨2099861, by rfl⟩ : syracuseStep 2799815 = 4199723) B4199723
theorem B1865947 : Blo 1865634 1865947 := bstep (se 1 (by rfl) ⟨1399460, by rfl⟩ : syracuseStep 1865947 = 2798921) B2798921
theorem B5675255 : Blo 1865634 5675255 := bstep (se 1 (by rfl) ⟨4256441, by rfl⟩ : syracuseStep 5675255 = 8512883) B8512883
theorem B4200695 : Blo 1865634 4200695 := bstep (se 1 (by rfl) ⟨3150521, by rfl⟩ : syracuseStep 4200695 = 6301043) B6301043
theorem B1866023 : Blo 1865634 1866023 := bstep (se 1 (by rfl) ⟨1399517, by rfl⟩ : syracuseStep 1866023 = 2799035) B2799035
theorem B1866063 : Blo 1865634 1866063 := bstep (se 1 (by rfl) ⟨1399547, by rfl⟩ : syracuseStep 1866063 = 2799095) B2799095
theorem B1866079 : Blo 1865634 1866079 := bstep (se 1 (by rfl) ⟨1399559, by rfl⟩ : syracuseStep 1866079 = 2799119) B2799119
theorem B2799977 : Blo 1865634 2799977 := bstep (se 2 (by rfl) ⟨1049991, by rfl⟩ : syracuseStep 2799977 = 2099983) B2099983
theorem B1866107 : Blo 1865634 1866107 := bstep (se 1 (by rfl) ⟨1399580, by rfl⟩ : syracuseStep 1866107 = 2799161) B2799161
theorem B1866159 : Blo 1865634 1866159 := bstep (se 1 (by rfl) ⟨1399619, by rfl⟩ : syracuseStep 1866159 = 2799239) B2799239
theorem B2800055 : Blo 1865634 2800055 := bstep (se 1 (by rfl) ⟨2100041, by rfl⟩ : syracuseStep 2800055 = 4200083) B4200083
theorem B1866183 : Blo 1865634 1866183 := bstep (se 1 (by rfl) ⟨1399637, by rfl⟩ : syracuseStep 1866183 = 2799275) B2799275
theorem B1866203 : Blo 1865634 1866203 := bstep (se 1 (by rfl) ⟨1399652, by rfl⟩ : syracuseStep 1866203 = 2799305) B2799305
theorem B2800091 : Blo 1865634 2800091 := bstep (se 1 (by rfl) ⟨2100068, by rfl⟩ : syracuseStep 2800091 = 4200137) B4200137
theorem B13818377 : Blo 1865634 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B21264929 : Blo 1865634 21264929 := bstep (se 2 (by rfl) ⟨7974348, by rfl⟩ : syracuseStep 21264929 = 15948697) B15948697
theorem B1866279 : Blo 1865634 1866279 := bstep (se 1 (by rfl) ⟨1399709, by rfl⟩ : syracuseStep 1866279 = 2799419) B2799419
theorem B4725287 : Blo 1865634 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B1866319 : Blo 1865634 1866319 := bstep (se 1 (by rfl) ⟨1399739, by rfl⟩ : syracuseStep 1866319 = 2799479) B2799479
theorem B1866335 : Blo 1865634 1866335 := bstep (se 1 (by rfl) ⟨1399751, by rfl⟩ : syracuseStep 1866335 = 2799503) B2799503
theorem B6298235 : Blo 1865634 6298235 := bstep (se 1 (by rfl) ⟨4723676, by rfl⟩ : syracuseStep 6298235 = 9447353) B9447353
theorem B1866363 : Blo 1865634 1866363 := bstep (se 1 (by rfl) ⟨1399772, by rfl⟩ : syracuseStep 1866363 = 2799545) B2799545
theorem B1866415 : Blo 1865634 1866415 := bstep (se 1 (by rfl) ⟨1399811, by rfl⟩ : syracuseStep 1866415 = 2799623) B2799623
theorem B1866439 : Blo 1865634 1866439 := bstep (se 1 (by rfl) ⟨1399829, by rfl⟩ : syracuseStep 1866439 = 2799659) B2799659
theorem B1866459 : Blo 1865634 1866459 := bstep (se 1 (by rfl) ⟨1399844, by rfl⟩ : syracuseStep 1866459 = 2799689) B2799689
theorem B2243435 : Blo 1865634 2243435 := bstep (se 1 (by rfl) ⟨1682576, by rfl⟩ : syracuseStep 2243435 = 3365153) B3365153
theorem B5315321 : Blo 1865634 5315321 := bstep (se 2 (by rfl) ⟨1993245, by rfl⟩ : syracuseStep 5315321 = 3986491) B3986491
theorem B3988217 : Blo 1865634 3988217 := bstep (se 2 (by rfl) ⟨1495581, by rfl⟩ : syracuseStep 3988217 = 2991163) B2991163
theorem B7969565 : Blo 1865634 7969565 := bstep (se 3 (by rfl) ⟨1494293, by rfl⟩ : syracuseStep 7969565 = 2988587) B2988587
theorem B6298397 : Blo 1865634 6298397 := bstep (se 3 (by rfl) ⟨1180949, by rfl⟩ : syracuseStep 6298397 = 2361899) B2361899
theorem B1866535 : Blo 1865634 1866535 := bstep (se 1 (by rfl) ⟨1399901, by rfl⟩ : syracuseStep 1866535 = 2799803) B2799803
theorem B4201289 : Blo 1865634 4201289 := bstep (se 2 (by rfl) ⟨1575483, by rfl⟩ : syracuseStep 4201289 = 3150967) B3150967
theorem B1866575 : Blo 1865634 1866575 := bstep (se 1 (by rfl) ⟨1399931, by rfl⟩ : syracuseStep 1866575 = 2799863) B2799863
theorem B2988895 : Blo 1865634 2988895 := bstep (se 1 (by rfl) ⟨2241671, by rfl⟩ : syracuseStep 2988895 = 4483343) B4483343
theorem B1866591 : Blo 1865634 1866591 := bstep (se 1 (by rfl) ⟨1399943, by rfl⟩ : syracuseStep 1866591 = 2799887) B2799887
theorem B4725611 : Blo 1865634 4725611 := bstep (se 1 (by rfl) ⟨3544208, by rfl⟩ : syracuseStep 4725611 = 7088417) B7088417
theorem B1866619 : Blo 1865634 1866619 := bstep (se 1 (by rfl) ⟨1399964, by rfl⟩ : syracuseStep 1866619 = 2799929) B2799929
theorem B3029935 : Blo 1865634 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B1866671 : Blo 1865634 1866671 := bstep (se 1 (by rfl) ⟨1400003, by rfl⟩ : syracuseStep 1866671 = 2800007) B2800007
theorem B2800559 : Blo 1865634 2800559 := bstep (se 1 (by rfl) ⟨2100419, by rfl⟩ : syracuseStep 2800559 = 4200839) B4200839
theorem B1866695 : Blo 1865634 1866695 := bstep (se 1 (by rfl) ⟨1400021, by rfl⟩ : syracuseStep 1866695 = 2800043) B2800043
theorem B2694107 : Blo 1865634 2694107 := bstep (se 1 (by rfl) ⟨2020580, by rfl⟩ : syracuseStep 2694107 = 4041161) B4041161
theorem B1866715 : Blo 1865634 1866715 := bstep (se 1 (by rfl) ⟨1400036, by rfl⟩ : syracuseStep 1866715 = 2800073) B2800073
theorem B2800649 : Blo 1865634 2800649 := bstep (se 2 (by rfl) ⟨1050243, by rfl⟩ : syracuseStep 2800649 = 2100487) B2100487
theorem B1866791 : Blo 1865634 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B2800679 : Blo 1865634 2800679 := bstep (se 1 (by rfl) ⟨2100509, by rfl⟩ : syracuseStep 2800679 = 4201019) B4201019
theorem B1866831 : Blo 1865634 1866831 := bstep (se 1 (by rfl) ⟨1400123, by rfl⟩ : syracuseStep 1866831 = 2800247) B2800247
theorem B1866847 : Blo 1865634 1866847 := bstep (se 1 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 1866847 = 2800271) B2800271
theorem B5979251 : Blo 1865634 5979251 := bstep (se 1 (by rfl) ⟨4484438, by rfl⟩ : syracuseStep 5979251 = 8968877) B8968877
theorem B1866875 : Blo 1865634 1866875 := bstep (se 1 (by rfl) ⟨1400156, by rfl⟩ : syracuseStep 1866875 = 2800313) B2800313
theorem B2800763 : Blo 1865634 2800763 := bstep (se 1 (by rfl) ⟨2100572, by rfl⟩ : syracuseStep 2800763 = 4201145) B4201145
theorem B57449603 : Blo 1865634 57449603 := bstep (se 1 (by rfl) ⟨43087202, by rfl⟩ : syracuseStep 57449603 = 86174405) B86174405
theorem B1866927 : Blo 1865634 1866927 := bstep (se 1 (by rfl) ⟨1400195, by rfl⟩ : syracuseStep 1866927 = 2800391) B2800391
theorem B1866951 : Blo 1865634 1866951 := bstep (se 1 (by rfl) ⟨1400213, by rfl⟩ : syracuseStep 1866951 = 2800427) B2800427
theorem B1866971 : Blo 1865634 1866971 := bstep (se 1 (by rfl) ⟨1400228, by rfl⟩ : syracuseStep 1866971 = 2800457) B2800457
theorem B7085303 : Blo 1865634 7085303 := bstep (se 1 (by rfl) ⟨5313977, by rfl⟩ : syracuseStep 7085303 = 10627955) B10627955
theorem B2800889 : Blo 1865634 2800889 := bstep (se 2 (by rfl) ⟨1050333, by rfl⟩ : syracuseStep 2800889 = 2100667) B2100667
theorem B1867047 : Blo 1865634 1867047 := bstep (se 1 (by rfl) ⟨1400285, by rfl⟩ : syracuseStep 1867047 = 2800571) B2800571
theorem B1867087 : Blo 1865634 1867087 := bstep (se 1 (by rfl) ⟨1400315, by rfl⟩ : syracuseStep 1867087 = 2800631) B2800631
theorem B1867103 : Blo 1865634 1867103 := bstep (se 1 (by rfl) ⟨1400327, by rfl⟩ : syracuseStep 1867103 = 2800655) B2800655
theorem B2800991 : Blo 1865634 2800991 := bstep (se 1 (by rfl) ⟨2100743, by rfl⟩ : syracuseStep 2800991 = 4201487) B4201487
theorem B2801003 : Blo 1865634 2801003 := bstep (se 1 (by rfl) ⟨2100752, by rfl⟩ : syracuseStep 2801003 = 4201505) B4201505
theorem B1867131 : Blo 1865634 1867131 := bstep (se 1 (by rfl) ⟨1400348, by rfl⟩ : syracuseStep 1867131 = 2800697) B2800697
theorem B5979521 : Blo 1865634 5979521 := bstep (se 2 (by rfl) ⟨2242320, by rfl⟩ : syracuseStep 5979521 = 4484641) B4484641
theorem B1867183 : Blo 1865634 1867183 := bstep (se 1 (by rfl) ⟨1400387, by rfl⟩ : syracuseStep 1867183 = 2800775) B2800775
theorem B2522551 : Blo 1865634 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B1867207 : Blo 1865634 1867207 := bstep (se 1 (by rfl) ⟨1400405, by rfl⟩ : syracuseStep 1867207 = 2800811) B2800811
theorem B6299099 : Blo 1865634 6299099 := bstep (se 1 (by rfl) ⟨4724324, by rfl⟩ : syracuseStep 6299099 = 9448649) B9448649
theorem B1867227 : Blo 1865634 1867227 := bstep (se 1 (by rfl) ⟨1400420, by rfl⟩ : syracuseStep 1867227 = 2800841) B2800841
theorem B5979635 : Blo 1865634 5979635 := bstep (se 1 (by rfl) ⟨4484726, by rfl⟩ : syracuseStep 5979635 = 8969453) B8969453
theorem B4726259 : Blo 1865634 4726259 := bstep (se 1 (by rfl) ⟨3544694, by rfl⟩ : syracuseStep 4726259 = 7089389) B7089389
theorem B1867303 : Blo 1865634 1867303 := bstep (se 1 (by rfl) ⟨1400477, by rfl⟩ : syracuseStep 1867303 = 2800955) B2800955
theorem B35896871 : Blo 1865634 35896871 := bstep (se 1 (by rfl) ⟨26922653, by rfl⟩ : syracuseStep 35896871 = 53845307) B53845307
theorem B1867343 : Blo 1865634 1867343 := bstep (se 1 (by rfl) ⟨1400507, by rfl⟩ : syracuseStep 1867343 = 2801015) B2801015
theorem B2801231 : Blo 1865634 2801231 := bstep (se 1 (by rfl) ⟨2100923, by rfl⟩ : syracuseStep 2801231 = 4201847) B4201847
theorem B1867359 : Blo 1865634 1867359 := bstep (se 1 (by rfl) ⟨1400519, by rfl⟩ : syracuseStep 1867359 = 2801039) B2801039
theorem B4202081 : Blo 1865634 4202081 := bstep (se 2 (by rfl) ⟨1575780, by rfl⟩ : syracuseStep 4202081 = 3151561) B3151561
theorem B30269051 : Blo 1865634 30269051 := bstep (se 1 (by rfl) ⟨22701788, by rfl⟩ : syracuseStep 30269051 = 45403577) B45403577
theorem B1867387 : Blo 1865634 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B1867439 : Blo 1865634 1867439 := bstep (se 1 (by rfl) ⟨1400579, by rfl⟩ : syracuseStep 1867439 = 2801159) B2801159
theorem B4726471 : Blo 1865634 4726471 := bstep (se 1 (by rfl) ⟨3544853, by rfl⟩ : syracuseStep 4726471 = 7089707) B7089707
theorem B1867463 : Blo 1865634 1867463 := bstep (se 1 (by rfl) ⟨1400597, by rfl⟩ : syracuseStep 1867463 = 2801195) B2801195
theorem B2801351 : Blo 1865634 2801351 := bstep (se 1 (by rfl) ⟨2101013, by rfl⟩ : syracuseStep 2801351 = 4202027) B4202027
theorem B1867483 : Blo 1865634 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B9445085 : Blo 1865634 9445085 := bstep (se 3 (by rfl) ⟨1770953, by rfl⟩ : syracuseStep 9445085 = 3541907) B3541907
theorem B1867559 : Blo 1865634 1867559 := bstep (se 1 (by rfl) ⟨1400669, by rfl⟩ : syracuseStep 1867559 = 2801339) B2801339
theorem B1867599 : Blo 1865634 1867599 := bstep (se 1 (by rfl) ⟨1400699, by rfl⟩ : syracuseStep 1867599 = 2801399) B2801399
theorem B1867615 : Blo 1865634 1867615 := bstep (se 1 (by rfl) ⟨1400711, by rfl⟩ : syracuseStep 1867615 = 2801423) B2801423
theorem B47816567 : Blo 1865634 47816567 := bstep (se 1 (by rfl) ⟨35862425, by rfl⟩ : syracuseStep 47816567 = 71724851) B71724851
theorem B8511419 : Blo 1865634 8511419 := bstep (se 1 (by rfl) ⟨6383564, by rfl⟩ : syracuseStep 8511419 = 12767129) B12767129
theorem B40927243 : Blo 1865634 40927243 := bstep (se 1 (by rfl) ⟨30695432, by rfl⟩ : syracuseStep 40927243 = 61390865) B61390865
theorem B15950033 : Blo 1865634 15950033 := bstep (se 2 (by rfl) ⟨5981262, by rfl⟩ : syracuseStep 15950033 = 11962525) B11962525
theorem B10092755 : Blo 1865634 10092755 := bstep (se 1 (by rfl) ⟨7569566, by rfl⟩ : syracuseStep 10092755 = 15139133) B15139133
theorem B8085851 : Blo 1865634 8085851 := bstep (se 1 (by rfl) ⟨6064388, by rfl⟩ : syracuseStep 8085851 = 12128777) B12128777
theorem B4546927 : Blo 1865634 4546927 := bstep (se 1 (by rfl) ⟨3410195, by rfl⟩ : syracuseStep 4546927 = 6820391) B6820391
theorem B6300179 : Blo 1865634 6300179 := bstep (se 1 (by rfl) ⟨4725134, by rfl⟩ : syracuseStep 6300179 = 9450269) B9450269
theorem B9446543 : Blo 1865634 9446543 := bstep (se 1 (by rfl) ⟨7084907, by rfl⟩ : syracuseStep 9446543 = 14169815) B14169815
theorem B7087247 : Blo 1865634 7087247 := bstep (se 1 (by rfl) ⟨5315435, by rfl⟩ : syracuseStep 7087247 = 10630871) B10630871
theorem B5981327 : Blo 1865634 5981327 := bstep (se 1 (by rfl) ⟨4485995, by rfl⟩ : syracuseStep 5981327 = 8971991) B8971991
theorem B15336647 : Blo 1865634 15336647 := bstep (se 1 (by rfl) ⟨11502485, by rfl⟩ : syracuseStep 15336647 = 23004971) B23004971
theorem B4039913 : Blo 1865634 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B20186455 : Blo 1865634 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B36849005 : Blo 1865634 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B5047739 : Blo 1865634 5047739 := bstep (se 1 (by rfl) ⟨3785804, by rfl⟩ : syracuseStep 5047739 = 7571609) B7571609
theorem B64669499 : Blo 1865634 64669499 := bstep (se 1 (by rfl) ⟨48502124, by rfl⟩ : syracuseStep 64669499 = 97004249) B97004249
theorem B14174189 : Blo 1865634 14174189 := bstep (se 3 (by rfl) ⟨2657660, by rfl⟩ : syracuseStep 14174189 = 5315321) B5315321
theorem B10635245 : Blo 1865634 10635245 := bstep (se 3 (by rfl) ⟨1994108, by rfl⟩ : syracuseStep 10635245 = 3988217) B3988217
theorem B38299735 : Blo 1865634 38299735 := bstep (se 1 (by rfl) ⟨28724801, by rfl⟩ : syracuseStep 38299735 = 57449603) B57449603
theorem B8079545 : Blo 1865634 8079545 := bstep (se 2 (by rfl) ⟨3029829, by rfl⟩ : syracuseStep 8079545 = 6059659) B6059659
theorem B9447677 : Blo 1865634 9447677 := bstep (se 3 (by rfl) ⟨1771439, by rfl⟩ : syracuseStep 9447677 = 3542879) B3542879
theorem B6301961 : Blo 1865634 6301961 := bstep (se 2 (by rfl) ⟨2363235, by rfl⟩ : syracuseStep 6301961 = 4726471) B4726471
theorem B5982493 : Blo 1865634 5982493 := bstep (se 3 (by rfl) ⟨1121717, by rfl⟩ : syracuseStep 5982493 = 2243435) B2243435
theorem B2361631 : Blo 1865634 2361631 := bstep (se 1 (by rfl) ⟨1771223, by rfl⟩ : syracuseStep 2361631 = 3542447) B3542447
theorem B23931247 : Blo 1865634 23931247 := bstep (se 1 (by rfl) ⟨17948435, by rfl⟩ : syracuseStep 23931247 = 35896871) B35896871
theorem B2099623 : Blo 1865634 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B20179367 : Blo 1865634 20179367 := bstep (se 1 (by rfl) ⟨15134525, by rfl⟩ : syracuseStep 20179367 = 30269051) B30269051
theorem B14174675 : Blo 1865634 14174675 := bstep (se 1 (by rfl) ⟨10631006, by rfl⟩ : syracuseStep 14174675 = 21262013) B21262013
theorem B31877711 : Blo 1865634 31877711 := bstep (se 1 (by rfl) ⟨23908283, by rfl⟩ : syracuseStep 31877711 = 47816567) B47816567
theorem B3148409 : Blo 1865634 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B3148463 : Blo 1865634 3148463 := bstep (se 1 (by rfl) ⟨2361347, by rfl⟩ : syracuseStep 3148463 = 4722695) B4722695
theorem B1993519 : Blo 1865634 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B136219481 : Blo 1865634 136219481 := bstep (se 2 (by rfl) ⟨51082305, by rfl⟩ : syracuseStep 136219481 = 102164611) B102164611
theorem B3148699 : Blo 1865634 3148699 := bstep (se 1 (by rfl) ⟨2361524, by rfl⟩ : syracuseStep 3148699 = 4723049) B4723049
theorem B2100199 : Blo 1865634 2100199 := bstep (se 1 (by rfl) ⟨1575149, by rfl⟩ : syracuseStep 2100199 = 3150299) B3150299
theorem B9448487 : Blo 1865634 9448487 := bstep (se 1 (by rfl) ⟨7086365, by rfl⟩ : syracuseStep 9448487 = 14172731) B14172731
theorem B7089191 : Blo 1865634 7089191 := bstep (se 1 (by rfl) ⟨5316893, by rfl⟩ : syracuseStep 7089191 = 10633787) B10633787
theorem B3984527 : Blo 1865634 3984527 := bstep (se 1 (by rfl) ⟨2988395, by rfl⟩ : syracuseStep 3984527 = 5976791) B5976791
theorem B2837791 : Blo 1865634 2837791 := bstep (se 1 (by rfl) ⟨2128343, by rfl⟩ : syracuseStep 2837791 = 4256687) B4256687
theorem B20188531 : Blo 1865634 20188531 := bstep (se 1 (by rfl) ⟨15141398, by rfl⟩ : syracuseStep 20188531 = 30282797) B30282797
theorem B6303095 : Blo 1865634 6303095 := bstep (se 1 (by rfl) ⟨4727321, by rfl⟩ : syracuseStep 6303095 = 9454643) B9454643
theorem B7974281 : Blo 1865634 7974281 := bstep (se 2 (by rfl) ⟨2990355, by rfl⟩ : syracuseStep 7974281 = 5980711) B5980711
theorem B5385811 : Blo 1865634 5385811 := bstep (se 1 (by rfl) ⟨4039358, by rfl⟩ : syracuseStep 5385811 = 8078717) B8078717
theorem B4198049 : Blo 1865634 4198049 := bstep (se 2 (by rfl) ⟨1574268, by rfl⟩ : syracuseStep 4198049 = 3148537) B3148537
theorem B9580193 : Blo 1865634 9580193 := bstep (se 2 (by rfl) ⟨3592572, by rfl⟩ : syracuseStep 9580193 = 7185145) B7185145
theorem B3985159 : Blo 1865634 3985159 := bstep (se 1 (by rfl) ⟨2988869, by rfl⟩ : syracuseStep 3985159 = 5977739) B5977739
theorem B3985193 : Blo 1865634 3985193 := bstep (se 2 (by rfl) ⟨1494447, by rfl⟩ : syracuseStep 3985193 = 2988895) B2988895
theorem B4198409 : Blo 1865634 4198409 := bstep (se 2 (by rfl) ⟨1574403, by rfl⟩ : syracuseStep 4198409 = 3148807) B3148807
theorem B14176619 : Blo 1865634 14176619 := bstep (se 1 (by rfl) ⟨10632464, by rfl⟩ : syracuseStep 14176619 = 21264929) B21264929
theorem B3150191 : Blo 1865634 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B20189573 : Blo 1865634 20189573 := bstep (se 4 (by rfl) ⟨1892772, by rfl⟩ : syracuseStep 20189573 = 3785545) B3785545
theorem B4198823 : Blo 1865634 4198823 := bstep (se 1 (by rfl) ⟨3149117, by rfl⟩ : syracuseStep 4198823 = 6298235) B6298235
theorem B5313043 : Blo 1865634 5313043 := bstep (se 1 (by rfl) ⟨3984782, by rfl⟩ : syracuseStep 5313043 = 7969565) B7969565
theorem B4198931 : Blo 1865634 4198931 := bstep (se 1 (by rfl) ⟨3149198, by rfl⟩ : syracuseStep 4198931 = 6298397) B6298397
theorem B17035825 : Blo 1865634 17035825 := bstep (se 2 (by rfl) ⟨6388434, by rfl⟩ : syracuseStep 17035825 = 12776869) B12776869
theorem B3150407 : Blo 1865634 3150407 := bstep (se 1 (by rfl) ⟨2362805, by rfl⟩ : syracuseStep 3150407 = 4725611) B4725611
theorem B4198985 : Blo 1865634 4198985 := bstep (se 2 (by rfl) ⟨1574619, by rfl⟩ : syracuseStep 4198985 = 3149239) B3149239
theorem B4256329 : Blo 1865634 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B3363401 : Blo 1865634 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B3986167 : Blo 1865634 3986167 := bstep (se 1 (by rfl) ⟨2989625, by rfl⟩ : syracuseStep 3986167 = 5979251) B5979251
theorem B4723535 : Blo 1865634 4723535 := bstep (se 1 (by rfl) ⟨3542651, by rfl⟩ : syracuseStep 4723535 = 7085303) B7085303
theorem B3986347 : Blo 1865634 3986347 := bstep (se 1 (by rfl) ⟨2989760, by rfl⟩ : syracuseStep 3986347 = 5979521) B5979521
theorem B2798567 : Blo 1865634 2798567 := bstep (se 1 (by rfl) ⟨2098925, by rfl⟩ : syracuseStep 2798567 = 4197851) B4197851
theorem B4199399 : Blo 1865634 4199399 := bstep (se 1 (by rfl) ⟨3149549, by rfl⟩ : syracuseStep 4199399 = 6299099) B6299099
theorem B3986423 : Blo 1865634 3986423 := bstep (se 1 (by rfl) ⟨2989817, by rfl⟩ : syracuseStep 3986423 = 5979635) B5979635
theorem B3150839 : Blo 1865634 3150839 := bstep (se 1 (by rfl) ⟨2363129, by rfl⟩ : syracuseStep 3150839 = 4726259) B4726259
theorem B9450593 : Blo 1865634 9450593 := bstep (se 2 (by rfl) ⟨3543972, by rfl⟩ : syracuseStep 9450593 = 7087945) B7087945
theorem B6296723 : Blo 1865634 6296723 := bstep (se 1 (by rfl) ⟨4722542, by rfl⟩ : syracuseStep 6296723 = 9445085) B9445085
theorem B2798825 : Blo 1865634 2798825 := bstep (se 2 (by rfl) ⟨1049559, by rfl⟩ : syracuseStep 2798825 = 2099119) B2099119
theorem B2798879 : Blo 1865634 2798879 := bstep (se 1 (by rfl) ⟨2099159, by rfl⟩ : syracuseStep 2798879 = 4198319) B4198319
theorem B5674279 : Blo 1865634 5674279 := bstep (se 1 (by rfl) ⟨4255709, by rfl⟩ : syracuseStep 5674279 = 8511419) B8511419
theorem B10630439 : Blo 1865634 10630439 := bstep (se 1 (by rfl) ⟨7972829, by rfl⟩ : syracuseStep 10630439 = 15945659) B15945659
theorem B5313887 : Blo 1865634 5313887 := bstep (se 1 (by rfl) ⟨3985415, by rfl⟩ : syracuseStep 5313887 = 7970831) B7970831
theorem B4199777 : Blo 1865634 4199777 := bstep (se 2 (by rfl) ⟨1574916, by rfl⟩ : syracuseStep 4199777 = 3149833) B3149833
theorem B20452747 : Blo 1865634 20452747 := bstep (se 1 (by rfl) ⟨15339560, by rfl⟩ : syracuseStep 20452747 = 30679121) B30679121
theorem B6296993 : Blo 1865634 6296993 := bstep (se 2 (by rfl) ⟨2361372, by rfl⟩ : syracuseStep 6296993 = 4722745) B4722745
theorem B4199867 : Blo 1865634 4199867 := bstep (se 1 (by rfl) ⟨3149900, by rfl⟩ : syracuseStep 4199867 = 6299801) B6299801
theorem B2799047 : Blo 1865634 2799047 := bstep (se 1 (by rfl) ⟨2099285, by rfl⟩ : syracuseStep 2799047 = 4198571) B4198571
theorem B4724183 : Blo 1865634 4724183 := bstep (se 1 (by rfl) ⟨3543137, by rfl⟩ : syracuseStep 4724183 = 7086275) B7086275
theorem B4199993 : Blo 1865634 4199993 := bstep (se 2 (by rfl) ⟨1574997, by rfl⟩ : syracuseStep 4199993 = 3149995) B3149995
theorem B35886725 : Blo 1865634 35886725 := bstep (se 4 (by rfl) ⟨3364380, by rfl⟩ : syracuseStep 35886725 = 6728761) B6728761
theorem B22697657 : Blo 1865634 22697657 := bstep (se 2 (by rfl) ⟨8511621, by rfl⟩ : syracuseStep 22697657 = 17023243) B17023243
theorem B19158713 : Blo 1865634 19158713 := bstep (se 2 (by rfl) ⟨7184517, by rfl⟩ : syracuseStep 19158713 = 14369035) B14369035
theorem B3151595 : Blo 1865634 3151595 := bstep (se 1 (by rfl) ⟨2363696, by rfl⟩ : syracuseStep 3151595 = 4727393) B4727393
theorem B14178077 : Blo 1865634 14178077 := bstep (se 3 (by rfl) ⟨2658389, by rfl⟩ : syracuseStep 14178077 = 5316779) B5316779
theorem B2799401 : Blo 1865634 2799401 := bstep (se 2 (by rfl) ⟨1049775, by rfl⟩ : syracuseStep 2799401 = 2099551) B2099551
theorem B2799407 : Blo 1865634 2799407 := bstep (se 1 (by rfl) ⟨2099555, by rfl⟩ : syracuseStep 2799407 = 4199111) B4199111
theorem B4724527 : Blo 1865634 4724527 := bstep (se 1 (by rfl) ⟨3543395, by rfl⟩ : syracuseStep 4724527 = 7086791) B7086791
theorem B8967991 : Blo 1865634 8967991 := bstep (se 1 (by rfl) ⟨6725993, by rfl⟩ : syracuseStep 8967991 = 13451987) B13451987
theorem B7976809 : Blo 1865634 7976809 := bstep (se 2 (by rfl) ⟨2991303, by rfl⟩ : syracuseStep 7976809 = 5982607) B5982607
theorem B1865679 : Blo 1865634 1865679 := bstep (se 1 (by rfl) ⟨1399259, by rfl⟩ : syracuseStep 1865679 = 2798519) B2798519
theorem B1865703 : Blo 1865634 1865703 := bstep (se 1 (by rfl) ⟨1399277, by rfl⟩ : syracuseStep 1865703 = 2798555) B2798555
theorem B61380611 : Blo 1865634 61380611 := bstep (se 1 (by rfl) ⟨46035458, by rfl⟩ : syracuseStep 61380611 = 92070917) B92070917
theorem B4200659 : Blo 1865634 4200659 := bstep (se 1 (by rfl) ⟨3150494, by rfl⟩ : syracuseStep 4200659 = 6300989) B6300989
theorem B2799881 : Blo 1865634 2799881 := bstep (se 2 (by rfl) ⟨1049955, by rfl⟩ : syracuseStep 2799881 = 2099911) B2099911
theorem B4200713 : Blo 1865634 4200713 := bstep (se 2 (by rfl) ⟨1575267, by rfl⟩ : syracuseStep 4200713 = 3150535) B3150535
theorem B3987721 : Blo 1865634 3987721 := bstep (se 2 (by rfl) ⟨1495395, by rfl⟩ : syracuseStep 3987721 = 2990791) B2990791
theorem B5978393 : Blo 1865634 5978393 := bstep (se 2 (by rfl) ⟨2241897, by rfl⟩ : syracuseStep 5978393 = 4483795) B4483795
theorem B6387997 : Blo 1865634 6387997 := bstep (se 3 (by rfl) ⟨1197749, by rfl⟩ : syracuseStep 6387997 = 2395499) B2395499
theorem B1866015 : Blo 1865634 1866015 := bstep (se 1 (by rfl) ⟨1399511, by rfl⟩ : syracuseStep 1866015 = 2799023) B2799023
theorem B1866075 : Blo 1865634 1866075 := bstep (se 1 (by rfl) ⟨1399556, by rfl⟩ : syracuseStep 1866075 = 2799113) B2799113
theorem B1866095 : Blo 1865634 1866095 := bstep (se 1 (by rfl) ⟨1399571, by rfl⟩ : syracuseStep 1866095 = 2799143) B2799143
theorem B2799983 : Blo 1865634 2799983 := bstep (se 1 (by rfl) ⟨2099987, by rfl⟩ : syracuseStep 2799983 = 4199975) B4199975
theorem B11958653 : Blo 1865634 11958653 := bstep (se 3 (by rfl) ⟨2242247, by rfl⟩ : syracuseStep 11958653 = 4484495) B4484495
theorem B1866151 : Blo 1865634 1866151 := bstep (se 1 (by rfl) ⟨1399613, by rfl⟩ : syracuseStep 1866151 = 2799227) B2799227
theorem B4725175 : Blo 1865634 4725175 := bstep (se 1 (by rfl) ⟨3543881, by rfl⟩ : syracuseStep 4725175 = 7087763) B7087763
theorem B4200929 : Blo 1865634 4200929 := bstep (se 2 (by rfl) ⟨1575348, by rfl⟩ : syracuseStep 4200929 = 3150697) B3150697
theorem B1866235 : Blo 1865634 1866235 := bstep (se 1 (by rfl) ⟨1399676, by rfl⟩ : syracuseStep 1866235 = 2799353) B2799353
theorem B1866303 : Blo 1865634 1866303 := bstep (se 1 (by rfl) ⟨1399727, by rfl⟩ : syracuseStep 1866303 = 2799455) B2799455
theorem B1866311 : Blo 1865634 1866311 := bstep (se 1 (by rfl) ⟨1399733, by rfl⟩ : syracuseStep 1866311 = 2799467) B2799467
theorem B2800199 : Blo 1865634 2800199 := bstep (se 1 (by rfl) ⟨2100149, by rfl⟩ : syracuseStep 2800199 = 4200299) B4200299
theorem B2800235 : Blo 1865634 2800235 := bstep (se 1 (by rfl) ⟨2100176, by rfl⟩ : syracuseStep 2800235 = 4200353) B4200353
theorem B1866463 : Blo 1865634 1866463 := bstep (se 1 (by rfl) ⟨1399847, by rfl⟩ : syracuseStep 1866463 = 2799695) B2799695
theorem B4201235 : Blo 1865634 4201235 := bstep (se 1 (by rfl) ⟨3150926, by rfl⟩ : syracuseStep 4201235 = 6301853) B6301853
theorem B1866543 : Blo 1865634 1866543 := bstep (se 1 (by rfl) ⟨1399907, by rfl⟩ : syracuseStep 1866543 = 2799815) B2799815
theorem B3783503 : Blo 1865634 3783503 := bstep (se 1 (by rfl) ⟨2837627, by rfl⟩ : syracuseStep 3783503 = 5675255) B5675255
theorem B2800463 : Blo 1865634 2800463 := bstep (se 1 (by rfl) ⟨2100347, by rfl⟩ : syracuseStep 2800463 = 4200695) B4200695
theorem B1866651 : Blo 1865634 1866651 := bstep (se 1 (by rfl) ⟨1399988, by rfl⟩ : syracuseStep 1866651 = 2799977) B2799977
theorem B1866703 : Blo 1865634 1866703 := bstep (se 1 (by rfl) ⟨1400027, by rfl⟩ : syracuseStep 1866703 = 2800055) B2800055
theorem B1866727 : Blo 1865634 1866727 := bstep (se 1 (by rfl) ⟨1400045, by rfl⟩ : syracuseStep 1866727 = 2800091) B2800091
theorem B37370909 : Blo 1865634 37370909 := bstep (se 3 (by rfl) ⟨7007045, by rfl⟩ : syracuseStep 37370909 = 14014091) B14014091
theorem B7969873 : Blo 1865634 7969873 := bstep (se 2 (by rfl) ⟨2988702, by rfl⟩ : syracuseStep 7969873 = 5977405) B5977405
theorem B8969297 : Blo 1865634 8969297 := bstep (se 2 (by rfl) ⟨3363486, by rfl⟩ : syracuseStep 8969297 = 6726973) B6726973
theorem B7969907 : Blo 1865634 7969907 := bstep (se 1 (by rfl) ⟨5977430, by rfl⟩ : syracuseStep 7969907 = 11954861) B11954861
theorem B4201595 : Blo 1865634 4201595 := bstep (se 1 (by rfl) ⟨3151196, by rfl⟩ : syracuseStep 4201595 = 6302393) B6302393
theorem B2800859 : Blo 1865634 2800859 := bstep (se 1 (by rfl) ⟨2100644, by rfl⟩ : syracuseStep 2800859 = 4201289) B4201289
theorem B4201721 : Blo 1865634 4201721 := bstep (se 2 (by rfl) ⟨1575645, by rfl⟩ : syracuseStep 4201721 = 3151291) B3151291
theorem B1867039 : Blo 1865634 1867039 := bstep (se 1 (by rfl) ⟨1400279, by rfl⟩ : syracuseStep 1867039 = 2800559) B2800559
theorem B9452861 : Blo 1865634 9452861 := bstep (se 3 (by rfl) ⟨1772411, by rfl⟩ : syracuseStep 9452861 = 3544823) B3544823
theorem B17947979 : Blo 1865634 17947979 := bstep (se 1 (by rfl) ⟨13460984, by rfl⟩ : syracuseStep 17947979 = 26921969) B26921969
theorem B1867099 : Blo 1865634 1867099 := bstep (se 1 (by rfl) ⟨1400324, by rfl⟩ : syracuseStep 1867099 = 2800649) B2800649
theorem B4791649 : Blo 1865634 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B1867119 : Blo 1865634 1867119 := bstep (se 1 (by rfl) ⟨1400339, by rfl⟩ : syracuseStep 1867119 = 2800679) B2800679
theorem B2801033 : Blo 1865634 2801033 := bstep (se 2 (by rfl) ⟨1050387, by rfl⟩ : syracuseStep 2801033 = 2100775) B2100775
theorem B4201865 : Blo 1865634 4201865 := bstep (se 2 (by rfl) ⟨1575699, by rfl⟩ : syracuseStep 4201865 = 3151399) B3151399
theorem B1867175 : Blo 1865634 1867175 := bstep (se 1 (by rfl) ⟨1400381, by rfl⟩ : syracuseStep 1867175 = 2800763) B2800763
theorem B1867259 : Blo 1865634 1867259 := bstep (se 1 (by rfl) ⟨1400444, by rfl⟩ : syracuseStep 1867259 = 2800889) B2800889
theorem B4201991 : Blo 1865634 4201991 := bstep (se 1 (by rfl) ⟨3151493, by rfl⟩ : syracuseStep 4201991 = 6302987) B6302987
theorem B60579353 : Blo 1865634 60579353 := bstep (se 2 (by rfl) ⟨22717257, by rfl⟩ : syracuseStep 60579353 = 45434515) B45434515
theorem B9444923 : Blo 1865634 9444923 := bstep (se 1 (by rfl) ⟨7083692, by rfl⟩ : syracuseStep 9444923 = 14167385) B14167385
theorem B1867327 : Blo 1865634 1867327 := bstep (se 1 (by rfl) ⟨1400495, by rfl⟩ : syracuseStep 1867327 = 2800991) B2800991
theorem B1867335 : Blo 1865634 1867335 := bstep (se 1 (by rfl) ⟨1400501, by rfl⟩ : syracuseStep 1867335 = 2801003) B2801003
theorem B4202171 : Blo 1865634 4202171 := bstep (se 1 (by rfl) ⟨3151628, by rfl⟩ : syracuseStep 4202171 = 6303257) B6303257
theorem B1867487 : Blo 1865634 1867487 := bstep (se 1 (by rfl) ⟨1400615, by rfl⟩ : syracuseStep 1867487 = 2801231) B2801231
theorem B2801387 : Blo 1865634 2801387 := bstep (se 1 (by rfl) ⟨2101040, by rfl⟩ : syracuseStep 2801387 = 4202081) B4202081
theorem B1867567 : Blo 1865634 1867567 := bstep (se 1 (by rfl) ⟨1400675, by rfl⟩ : syracuseStep 1867567 = 2801351) B2801351
theorem B4726583 : Blo 1865634 4726583 := bstep (se 1 (by rfl) ⟨3544937, by rfl⟩ : syracuseStep 4726583 = 7089875) B7089875
theorem B4726633 : Blo 1865634 4726633 := bstep (se 2 (by rfl) ⟨1772487, by rfl⟩ : syracuseStep 4726633 = 3544975) B3544975
theorem B7184285 : Blo 1865634 7184285 := bstep (se 3 (by rfl) ⟨1347053, by rfl⟩ : syracuseStep 7184285 = 2694107) B2694107
theorem B22716335 : Blo 1865634 22716335 := bstep (se 1 (by rfl) ⟨17037251, by rfl⟩ : syracuseStep 22716335 = 34074503) B34074503
theorem B10633355 : Blo 1865634 10633355 := bstep (se 1 (by rfl) ⟨7975016, by rfl⟩ : syracuseStep 10633355 = 15950033) B15950033
theorem B5390567 : Blo 1865634 5390567 := bstep (se 1 (by rfl) ⟨4042925, by rfl⟩ : syracuseStep 5390567 = 8085851) B8085851
theorem B13459715 : Blo 1865634 13459715 := bstep (se 1 (by rfl) ⟨10094786, by rfl⟩ : syracuseStep 13459715 = 20189573) B20189573
theorem B6062569 : Blo 1865634 6062569 := bstep (se 2 (by rfl) ⟨2273463, by rfl⟩ : syracuseStep 6062569 = 4546927) B4546927
theorem B31908329 : Blo 1865634 31908329 := bstep (se 2 (by rfl) ⟨11965623, by rfl⟩ : syracuseStep 31908329 = 23931247) B23931247
theorem B21545453 : Blo 1865634 21545453 := bstep (se 3 (by rfl) ⟨4039772, by rfl⟩ : syracuseStep 21545453 = 8079545) B8079545
theorem B6300233 : Blo 1865634 6300233 := bstep (se 2 (by rfl) ⟨2362587, by rfl⟩ : syracuseStep 6300233 = 4725175) B4725175
theorem B10773101 : Blo 1865634 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B6300395 : Blo 1865634 6300395 := bstep (se 1 (by rfl) ⟨4725296, by rfl⟩ : syracuseStep 6300395 = 9450593) B9450593
theorem B10224431 : Blo 1865634 10224431 := bstep (se 1 (by rfl) ⟨7668323, by rfl⟩ : syracuseStep 10224431 = 15336647) B15336647
theorem B7086959 : Blo 1865634 7086959 := bstep (se 1 (by rfl) ⟨5315219, by rfl⟩ : syracuseStep 7086959 = 10630439) B10630439
theorem B15131771 : Blo 1865634 15131771 := bstep (se 1 (by rfl) ⟨11348828, by rfl⟩ : syracuseStep 15131771 = 22697657) B22697657
theorem B12772475 : Blo 1865634 12772475 := bstep (se 1 (by rfl) ⟨9579356, by rfl⟩ : syracuseStep 12772475 = 19158713) B19158713
theorem B40920407 : Blo 1865634 40920407 := bstep (se 1 (by rfl) ⟨30690305, by rfl⟩ : syracuseStep 40920407 = 61380611) B61380611
theorem B21267845 : Blo 1865634 21267845 := bstep (se 4 (by rfl) ⟨1993860, by rfl⟩ : syracuseStep 21267845 = 3987721) B3987721
theorem B10626497 : Blo 1865634 10626497 := bstep (se 2 (by rfl) ⟨3984936, by rfl⟩ : syracuseStep 10626497 = 7969873) B7969873
theorem B7972435 : Blo 1865634 7972435 := bstep (se 1 (by rfl) ⟨5979326, by rfl⟩ : syracuseStep 7972435 = 11958653) B11958653
theorem B13452911 : Blo 1865634 13452911 := bstep (se 1 (by rfl) ⟨10089683, by rfl⟩ : syracuseStep 13452911 = 20179367) B20179367
theorem B21251807 : Blo 1865634 21251807 := bstep (se 1 (by rfl) ⟨15938855, by rfl⟩ : syracuseStep 21251807 = 31877711) B31877711
theorem B2098939 : Blo 1865634 2098939 := bstep (se 1 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 2098939 = 3148409) B3148409
theorem B2098975 : Blo 1865634 2098975 := bstep (se 1 (by rfl) ⟨1574231, by rfl⟩ : syracuseStep 2098975 = 3148463) B3148463
theorem B24913939 : Blo 1865634 24913939 := bstep (se 1 (by rfl) ⟨18685454, by rfl⟩ : syracuseStep 24913939 = 37370909) B37370909
theorem B2656351 : Blo 1865634 2656351 := bstep (se 1 (by rfl) ⟨1992263, by rfl⟩ : syracuseStep 2656351 = 3984527) B3984527
theorem B6301907 : Blo 1865634 6301907 := bstep (se 1 (by rfl) ⟨4726430, by rfl⟩ : syracuseStep 6301907 = 9452861) B9452861
theorem B6302177 : Blo 1865634 6302177 := bstep (se 2 (by rfl) ⟨2363316, by rfl⟩ : syracuseStep 6302177 = 4726633) B4726633
theorem B10635745 : Blo 1865634 10635745 := bstep (se 2 (by rfl) ⟨3988404, by rfl⟩ : syracuseStep 10635745 = 7976809) B7976809
theorem B2656795 : Blo 1865634 2656795 := bstep (se 1 (by rfl) ⟨1992596, by rfl⟩ : syracuseStep 2656795 = 3985193) B3985193
theorem B54569657 : Blo 1865634 54569657 := bstep (se 2 (by rfl) ⟨20463621, by rfl⟩ : syracuseStep 54569657 = 40927243) B40927243
theorem B6728503 : Blo 1865634 6728503 := bstep (se 1 (by rfl) ⟨5046377, by rfl⟩ : syracuseStep 6728503 = 10092755) B10092755
theorem B2100127 : Blo 1865634 2100127 := bstep (se 1 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 2100127 = 3150191) B3150191
theorem B3148841 : Blo 1865634 3148841 := bstep (se 2 (by rfl) ⟨1180815, by rfl⟩ : syracuseStep 3148841 = 2361631) B2361631
theorem B2100271 : Blo 1865634 2100271 := bstep (se 1 (by rfl) ⟨1575203, by rfl⟩ : syracuseStep 2100271 = 3150407) B3150407
theorem B3149023 : Blo 1865634 3149023 := bstep (se 1 (by rfl) ⟨2361767, by rfl⟩ : syracuseStep 3149023 = 4723535) B4723535
theorem B2657615 : Blo 1865634 2657615 := bstep (se 1 (by rfl) ⟨1993211, by rfl⟩ : syracuseStep 2657615 = 3986423) B3986423
theorem B2100559 : Blo 1865634 2100559 := bstep (se 1 (by rfl) ⟨1575419, by rfl⟩ : syracuseStep 2100559 = 3150839) B3150839
theorem B4197815 : Blo 1865634 4197815 := bstep (se 1 (by rfl) ⟨3148361, by rfl⟩ : syracuseStep 4197815 = 6296723) B6296723
theorem B3542591 : Blo 1865634 3542591 := bstep (se 1 (by rfl) ⟨2656943, by rfl⟩ : syracuseStep 3542591 = 5313887) B5313887
theorem B4197995 : Blo 1865634 4197995 := bstep (se 1 (by rfl) ⟨3148496, by rfl⟩ : syracuseStep 4197995 = 6296993) B6296993
theorem B3149455 : Blo 1865634 3149455 := bstep (se 1 (by rfl) ⟨2362091, by rfl⟩ : syracuseStep 3149455 = 4724183) B4724183
theorem B2658025 : Blo 1865634 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B23924483 : Blo 1865634 23924483 := bstep (se 1 (by rfl) ⟨17943362, by rfl⟩ : syracuseStep 23924483 = 35886725) B35886725
theorem B2101063 : Blo 1865634 2101063 := bstep (se 1 (by rfl) ⟨1575797, by rfl⟩ : syracuseStep 2101063 = 3151595) B3151595
theorem B4198265 : Blo 1865634 4198265 := bstep (se 2 (by rfl) ⟨1574349, by rfl⟩ : syracuseStep 4198265 = 3148699) B3148699
theorem B9449459 : Blo 1865634 9449459 := bstep (se 1 (by rfl) ⟨7087094, by rfl⟩ : syracuseStep 9449459 = 14174189) B14174189
theorem B7090163 : Blo 1865634 7090163 := bstep (se 1 (by rfl) ⟨5317622, by rfl⟩ : syracuseStep 7090163 = 10635245) B10635245
theorem B3985595 : Blo 1865634 3985595 := bstep (se 1 (by rfl) ⟨2989196, by rfl⟩ : syracuseStep 3985595 = 5978393) B5978393
theorem B9449783 : Blo 1865634 9449783 := bstep (se 1 (by rfl) ⟨7087337, by rfl⟩ : syracuseStep 9449783 = 14174675) B14174675
theorem B7565705 : Blo 1865634 7565705 := bstep (se 2 (by rfl) ⟨2837139, by rfl⟩ : syracuseStep 7565705 = 5674279) B5674279
theorem B26915273 : Blo 1865634 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B90812987 : Blo 1865634 90812987 := bstep (se 1 (by rfl) ⟨68109740, by rfl⟩ : syracuseStep 90812987 = 136219481) B136219481
theorem B5313271 : Blo 1865634 5313271 := bstep (se 1 (by rfl) ⟨3984953, by rfl⟩ : syracuseStep 5313271 = 7969907) B7969907
theorem B7181081 : Blo 1865634 7181081 := bstep (se 2 (by rfl) ⟨2692905, by rfl⟩ : syracuseStep 7181081 = 5385811) B5385811
theorem B11965319 : Blo 1865634 11965319 := bstep (se 1 (by rfl) ⟨8973989, by rfl⟩ : syracuseStep 11965319 = 17947979) B17947979
theorem B5313545 : Blo 1865634 5313545 := bstep (se 2 (by rfl) ⟨1992579, by rfl⟩ : syracuseStep 5313545 = 3985159) B3985159
theorem B6296615 : Blo 1865634 6296615 := bstep (se 1 (by rfl) ⟨4722461, by rfl⟩ : syracuseStep 6296615 = 9444923) B9444923
theorem B11957321 : Blo 1865634 11957321 := bstep (se 2 (by rfl) ⟨4483995, by rfl⟩ : syracuseStep 11957321 = 8967991) B8967991
theorem B2798699 : Blo 1865634 2798699 := bstep (se 1 (by rfl) ⟨2099024, by rfl⟩ : syracuseStep 2798699 = 4198049) B4198049
theorem B6386795 : Blo 1865634 6386795 := bstep (se 1 (by rfl) ⟨4790096, by rfl⟩ : syracuseStep 6386795 = 9580193) B9580193
theorem B60576893 : Blo 1865634 60576893 := bstep (se 3 (by rfl) ⟨11358167, by rfl⟩ : syracuseStep 60576893 = 22716335) B22716335
theorem B3151055 : Blo 1865634 3151055 := bstep (se 1 (by rfl) ⟨2363291, by rfl⟩ : syracuseStep 3151055 = 4726583) B4726583
theorem B4789523 : Blo 1865634 4789523 := bstep (se 1 (by rfl) ⟨3592142, by rfl⟩ : syracuseStep 4789523 = 7184285) B7184285
theorem B2798939 : Blo 1865634 2798939 := bstep (se 1 (by rfl) ⟨2099204, by rfl⟩ : syracuseStep 2798939 = 4198409) B4198409
theorem B23918125 : Blo 1865634 23918125 := bstep (se 3 (by rfl) ⟨4484648, by rfl⟩ : syracuseStep 23918125 = 8969297) B8969297
theorem B9451079 : Blo 1865634 9451079 := bstep (se 1 (by rfl) ⟨7088309, by rfl⟩ : syracuseStep 9451079 = 14176619) B14176619
theorem B2799215 : Blo 1865634 2799215 := bstep (se 1 (by rfl) ⟨2099411, by rfl⟩ : syracuseStep 2799215 = 4198823) B4198823
theorem B2799287 : Blo 1865634 2799287 := bstep (se 1 (by rfl) ⟨2099465, by rfl⟩ : syracuseStep 2799287 = 4198931) B4198931
theorem B4200119 : Blo 1865634 4200119 := bstep (se 1 (by rfl) ⟨3150089, by rfl⟩ : syracuseStep 4200119 = 6300179) B6300179
theorem B8517329 : Blo 1865634 8517329 := bstep (se 2 (by rfl) ⟨3193998, by rfl⟩ : syracuseStep 8517329 = 6387997) B6387997
theorem B7976657 : Blo 1865634 7976657 := bstep (se 2 (by rfl) ⟨2991246, by rfl⟩ : syracuseStep 7976657 = 5982493) B5982493
theorem B2799323 : Blo 1865634 2799323 := bstep (se 1 (by rfl) ⟨2099492, by rfl⟩ : syracuseStep 2799323 = 4198985) B4198985
theorem B204265253 : Blo 1865634 204265253 := bstep (se 4 (by rfl) ⟨19149867, by rfl⟩ : syracuseStep 204265253 = 38299735) B38299735
theorem B2799497 : Blo 1865634 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B1865711 : Blo 1865634 1865711 := bstep (se 1 (by rfl) ⟨1399283, by rfl⟩ : syracuseStep 1865711 = 2798567) B2798567
theorem B2799599 : Blo 1865634 2799599 := bstep (se 1 (by rfl) ⟨2099699, by rfl⟩ : syracuseStep 2799599 = 4199399) B4199399
theorem B7084057 : Blo 1865634 7084057 := bstep (se 2 (by rfl) ⟨2656521, by rfl⟩ : syracuseStep 7084057 = 5313043) B5313043
theorem B22714433 : Blo 1865634 22714433 := bstep (se 2 (by rfl) ⟨8517912, by rfl⟩ : syracuseStep 22714433 = 17035825) B17035825
theorem B6297695 : Blo 1865634 6297695 := bstep (se 1 (by rfl) ⟨4723271, by rfl⟩ : syracuseStep 6297695 = 9446543) B9446543
theorem B5675105 : Blo 1865634 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B4724831 : Blo 1865634 4724831 := bstep (se 1 (by rfl) ⟨3543623, by rfl⟩ : syracuseStep 4724831 = 7087247) B7087247
theorem B3987551 : Blo 1865634 3987551 := bstep (se 1 (by rfl) ⟨2990663, by rfl⟩ : syracuseStep 3987551 = 5981327) B5981327
theorem B1865883 : Blo 1865634 1865883 := bstep (se 1 (by rfl) ⟨1399412, by rfl⟩ : syracuseStep 1865883 = 2798825) B2798825
theorem B1865919 : Blo 1865634 1865919 := bstep (se 1 (by rfl) ⟨1399439, by rfl⟩ : syracuseStep 1865919 = 2798879) B2798879
theorem B2799851 : Blo 1865634 2799851 := bstep (se 1 (by rfl) ⟨2099888, by rfl⟩ : syracuseStep 2799851 = 4199777) B4199777
theorem B24566003 : Blo 1865634 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B2799911 : Blo 1865634 2799911 := bstep (se 1 (by rfl) ⟨2099933, by rfl⟩ : syracuseStep 2799911 = 4199867) B4199867
theorem B3365159 : Blo 1865634 3365159 := bstep (se 1 (by rfl) ⟨2523869, by rfl⟩ : syracuseStep 3365159 = 5047739) B5047739
theorem B1866031 : Blo 1865634 1866031 := bstep (se 1 (by rfl) ⟨1399523, by rfl⟩ : syracuseStep 1866031 = 2799047) B2799047
theorem B5314889 : Blo 1865634 5314889 := bstep (se 2 (by rfl) ⟨1993083, by rfl⟩ : syracuseStep 5314889 = 3986167) B3986167
theorem B2799995 : Blo 1865634 2799995 := bstep (se 1 (by rfl) ⟨2099996, by rfl⟩ : syracuseStep 2799995 = 4199993) B4199993
theorem B9452051 : Blo 1865634 9452051 := bstep (se 1 (by rfl) ⟨7089038, by rfl⟩ : syracuseStep 9452051 = 14178077) B14178077
theorem B1866267 : Blo 1865634 1866267 := bstep (se 1 (by rfl) ⟨1399700, by rfl⟩ : syracuseStep 1866267 = 2799401) B2799401
theorem B1866271 : Blo 1865634 1866271 := bstep (se 1 (by rfl) ⟨1399703, by rfl⟩ : syracuseStep 1866271 = 2799407) B2799407
theorem B43112999 : Blo 1865634 43112999 := bstep (se 1 (by rfl) ⟨32334749, by rfl⟩ : syracuseStep 43112999 = 64669499) B64669499
theorem B5315129 : Blo 1865634 5315129 := bstep (se 2 (by rfl) ⟨1993173, by rfl⟩ : syracuseStep 5315129 = 3986347) B3986347
theorem B2800265 : Blo 1865634 2800265 := bstep (se 2 (by rfl) ⟨1050099, by rfl⟩ : syracuseStep 2800265 = 2100199) B2100199
theorem B2800439 : Blo 1865634 2800439 := bstep (se 1 (by rfl) ⟨2100329, by rfl⟩ : syracuseStep 2800439 = 4200659) B4200659
theorem B6298451 : Blo 1865634 6298451 := bstep (se 1 (by rfl) ⟨4723838, by rfl⟩ : syracuseStep 6298451 = 9447677) B9447677
theorem B1866587 : Blo 1865634 1866587 := bstep (se 1 (by rfl) ⟨1399940, by rfl⟩ : syracuseStep 1866587 = 2799881) B2799881
theorem B2800475 : Blo 1865634 2800475 := bstep (se 1 (by rfl) ⟨2100356, by rfl⟩ : syracuseStep 2800475 = 4200713) B4200713
theorem B4201307 : Blo 1865634 4201307 := bstep (se 1 (by rfl) ⟨3150980, by rfl⟩ : syracuseStep 4201307 = 6301961) B6301961
theorem B8969069 : Blo 1865634 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B1866655 : Blo 1865634 1866655 := bstep (se 1 (by rfl) ⟨1399991, by rfl⟩ : syracuseStep 1866655 = 2799983) B2799983
theorem B2800619 : Blo 1865634 2800619 := bstep (se 1 (by rfl) ⟨2100464, by rfl⟩ : syracuseStep 2800619 = 4200929) B4200929
theorem B3783721 : Blo 1865634 3783721 := bstep (se 2 (by rfl) ⟨1418895, by rfl⟩ : syracuseStep 3783721 = 2837791) B2837791
theorem B1866799 : Blo 1865634 1866799 := bstep (se 1 (by rfl) ⟨1400099, by rfl⟩ : syracuseStep 1866799 = 2800199) B2800199
theorem B1866823 : Blo 1865634 1866823 := bstep (se 1 (by rfl) ⟨1400117, by rfl⟩ : syracuseStep 1866823 = 2800235) B2800235
theorem B6388865 : Blo 1865634 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B26918041 : Blo 1865634 26918041 := bstep (se 2 (by rfl) ⟨10094265, by rfl⟩ : syracuseStep 26918041 = 20188531) B20188531
theorem B2800823 : Blo 1865634 2800823 := bstep (se 1 (by rfl) ⟨2100617, by rfl⟩ : syracuseStep 2800823 = 4201235) B4201235
theorem B27270329 : Blo 1865634 27270329 := bstep (se 2 (by rfl) ⟨10226373, by rfl⟩ : syracuseStep 27270329 = 20452747) B20452747
theorem B2522335 : Blo 1865634 2522335 := bstep (se 1 (by rfl) ⟨1891751, by rfl⟩ : syracuseStep 2522335 = 3783503) B3783503
theorem B1866975 : Blo 1865634 1866975 := bstep (se 1 (by rfl) ⟨1400231, by rfl⟩ : syracuseStep 1866975 = 2800463) B2800463
theorem B6298991 : Blo 1865634 6298991 := bstep (se 1 (by rfl) ⟨4724243, by rfl⟩ : syracuseStep 6298991 = 9448487) B9448487
theorem B4726127 : Blo 1865634 4726127 := bstep (se 1 (by rfl) ⟨3544595, by rfl⟩ : syracuseStep 4726127 = 7089191) B7089191
theorem B2801063 : Blo 1865634 2801063 := bstep (se 1 (by rfl) ⟨2100797, by rfl⟩ : syracuseStep 2801063 = 4201595) B4201595
theorem B1867239 : Blo 1865634 1867239 := bstep (se 1 (by rfl) ⟨1400429, by rfl⟩ : syracuseStep 1867239 = 2800859) B2800859
theorem B2801147 : Blo 1865634 2801147 := bstep (se 1 (by rfl) ⟨2100860, by rfl⟩ : syracuseStep 2801147 = 4201721) B4201721
theorem B4202063 : Blo 1865634 4202063 := bstep (se 1 (by rfl) ⟨3151547, by rfl⟩ : syracuseStep 4202063 = 6303095) B6303095
theorem B5316187 : Blo 1865634 5316187 := bstep (se 1 (by rfl) ⟨3987140, by rfl⟩ : syracuseStep 5316187 = 7974281) B7974281
theorem B1867355 : Blo 1865634 1867355 := bstep (se 1 (by rfl) ⟨1400516, by rfl⟩ : syracuseStep 1867355 = 2801033) B2801033
theorem B2801243 : Blo 1865634 2801243 := bstep (se 1 (by rfl) ⟨2100932, by rfl⟩ : syracuseStep 2801243 = 4201865) B4201865
theorem B2801327 : Blo 1865634 2801327 := bstep (se 1 (by rfl) ⟨2100995, by rfl⟩ : syracuseStep 2801327 = 4201991) B4201991
theorem B40386235 : Blo 1865634 40386235 := bstep (se 1 (by rfl) ⟨30289676, by rfl⟩ : syracuseStep 40386235 = 60579353) B60579353
theorem B6299369 : Blo 1865634 6299369 := bstep (se 2 (by rfl) ⟨2362263, by rfl⟩ : syracuseStep 6299369 = 4724527) B4724527
theorem B2801447 : Blo 1865634 2801447 := bstep (se 1 (by rfl) ⟨2101085, by rfl⟩ : syracuseStep 2801447 = 4202171) B4202171
theorem B1867591 : Blo 1865634 1867591 := bstep (se 1 (by rfl) ⟨1400693, by rfl⟩ : syracuseStep 1867591 = 2801387) B2801387
theorem B33218585 : Blo 1865634 33218585 := bstep (se 2 (by rfl) ⟨12456969, by rfl⟩ : syracuseStep 33218585 = 24913939) B24913939
theorem B9445409 : Blo 1865634 9445409 := bstep (se 2 (by rfl) ⟨3542028, by rfl⟩ : syracuseStep 9445409 = 7084057) B7084057
theorem B6299855 : Blo 1865634 6299855 := bstep (se 1 (by rfl) ⟨4724891, by rfl⟩ : syracuseStep 6299855 = 9449783) B9449783
theorem B4726775 : Blo 1865634 4726775 := bstep (se 1 (by rfl) ⟨3545081, by rfl⟩ : syracuseStep 4726775 = 7090163) B7090163
theorem B72720877 : Blo 1865634 72720877 := bstep (se 3 (by rfl) ⟨13635164, by rfl⟩ : syracuseStep 72720877 = 27270329) B27270329
theorem B6816287 : Blo 1865634 6816287 := bstep (se 1 (by rfl) ⟨5112215, by rfl⟩ : syracuseStep 6816287 = 10224431) B10224431
theorem B14180993 : Blo 1865634 14180993 := bstep (se 2 (by rfl) ⟨5317872, by rfl⟩ : syracuseStep 14180993 = 10635745) B10635745
theorem B7971547 : Blo 1865634 7971547 := bstep (se 1 (by rfl) ⟨5978660, by rfl⟩ : syracuseStep 7971547 = 11957321) B11957321
theorem B7086973 : Blo 1865634 7086973 := bstep (se 3 (by rfl) ⟨1328807, by rfl⟩ : syracuseStep 7086973 = 2657615) B2657615
theorem B27280271 : Blo 1865634 27280271 := bstep (se 1 (by rfl) ⟨20460203, by rfl⟩ : syracuseStep 27280271 = 40920407) B40920407
theorem B6300719 : Blo 1865634 6300719 := bstep (se 1 (by rfl) ⟨4725539, by rfl⟩ : syracuseStep 6300719 = 9451079) B9451079
theorem B8971337 : Blo 1865634 8971337 := bstep (se 2 (by rfl) ⟨3364251, by rfl⟩ : syracuseStep 8971337 = 6728503) B6728503
theorem B5678219 : Blo 1865634 5678219 := bstep (se 1 (by rfl) ⟨4258664, by rfl⟩ : syracuseStep 5678219 = 8517329) B8517329
theorem B5317771 : Blo 1865634 5317771 := bstep (se 1 (by rfl) ⟨3988328, by rfl⟩ : syracuseStep 5317771 = 7976657) B7976657
theorem B136176835 : Blo 1865634 136176835 := bstep (se 1 (by rfl) ⟨102132626, by rfl⟩ : syracuseStep 136176835 = 204265253) B204265253
theorem B16377335 : Blo 1865634 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B35890721 : Blo 1865634 35890721 := bstep (se 2 (by rfl) ⟨13459020, by rfl⟩ : syracuseStep 35890721 = 26918041) B26918041
theorem B6301367 : Blo 1865634 6301367 := bstep (se 1 (by rfl) ⟨4726025, by rfl⟩ : syracuseStep 6301367 = 9452051) B9452051
theorem B2099227 : Blo 1865634 2099227 := bstep (se 1 (by rfl) ⟨1574420, by rfl⟩ : syracuseStep 2099227 = 3148841) B3148841
theorem B7088249 : Blo 1865634 7088249 := bstep (se 2 (by rfl) ⟨2658093, by rfl⟩ : syracuseStep 7088249 = 5316187) B5316187
theorem B53848313 : Blo 1865634 53848313 := bstep (se 2 (by rfl) ⟨20193117, by rfl⟩ : syracuseStep 53848313 = 40386235) B40386235
theorem B2361727 : Blo 1865634 2361727 := bstep (se 1 (by rfl) ⟨1771295, by rfl⟩ : syracuseStep 2361727 = 3542591) B3542591
theorem B7088903 : Blo 1865634 7088903 := bstep (se 1 (by rfl) ⟨5316677, by rfl⟩ : syracuseStep 7088903 = 10633355) B10633355
theorem B2657063 : Blo 1865634 2657063 := bstep (se 1 (by rfl) ⟨1992797, by rfl⟩ : syracuseStep 2657063 = 3985595) B3985595
theorem B3541801 : Blo 1865634 3541801 := bstep (se 2 (by rfl) ⟨1328175, by rfl⟩ : syracuseStep 3541801 = 2656351) B2656351
theorem B8973143 : Blo 1865634 8973143 := bstep (se 1 (by rfl) ⟨6729857, by rfl⟩ : syracuseStep 8973143 = 13459715) B13459715
theorem B15133613 : Blo 1865634 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B17943515 : Blo 1865634 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B60541991 : Blo 1865634 60541991 := bstep (se 1 (by rfl) ⟨45406493, by rfl⟩ : syracuseStep 60541991 = 90812987) B90812987
theorem B4787387 : Blo 1865634 4787387 := bstep (se 1 (by rfl) ⟨3590540, by rfl⟩ : syracuseStep 4787387 = 7181081) B7181081
theorem B3542363 : Blo 1865634 3542363 := bstep (se 1 (by rfl) ⟨2656772, by rfl⟩ : syracuseStep 3542363 = 5313545) B5313545
theorem B4197743 : Blo 1865634 4197743 := bstep (se 1 (by rfl) ⟨3148307, by rfl⟩ : syracuseStep 4197743 = 6296615) B6296615
theorem B3542393 : Blo 1865634 3542393 := bstep (se 2 (by rfl) ⟨1328397, by rfl⟩ : syracuseStep 3542393 = 2656795) B2656795
theorem B10087847 : Blo 1865634 10087847 := bstep (se 1 (by rfl) ⟨7565885, by rfl⟩ : syracuseStep 10087847 = 15131771) B15131771
theorem B8514983 : Blo 1865634 8514983 := bstep (se 1 (by rfl) ⟨6386237, by rfl⟩ : syracuseStep 8514983 = 12772475) B12772475
theorem B8973757 : Blo 1865634 8973757 := bstep (se 3 (by rfl) ⟨1682579, by rfl⟩ : syracuseStep 8973757 = 3365159) B3365159
theorem B2100703 : Blo 1865634 2100703 := bstep (se 1 (by rfl) ⟨1575527, by rfl⟩ : syracuseStep 2100703 = 3151055) B3151055
theorem B14167871 : Blo 1865634 14167871 := bstep (se 1 (by rfl) ⟨10625903, by rfl⟩ : syracuseStep 14167871 = 21251807) B21251807
theorem B14176133 : Blo 1865634 14176133 := bstep (se 4 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 14176133 = 2658025) B2658025
theorem B57454541 : Blo 1865634 57454541 := bstep (se 3 (by rfl) ⟨10772726, by rfl⟩ : syracuseStep 57454541 = 21545453) B21545453
theorem B15142955 : Blo 1865634 15142955 := bstep (se 1 (by rfl) ⟨11357216, by rfl⟩ : syracuseStep 15142955 = 22714433) B22714433
theorem B4198463 : Blo 1865634 4198463 := bstep (se 1 (by rfl) ⟨3148847, by rfl⟩ : syracuseStep 4198463 = 6297695) B6297695
theorem B3149887 : Blo 1865634 3149887 := bstep (se 1 (by rfl) ⟨2362415, by rfl⟩ : syracuseStep 3149887 = 4724831) B4724831
theorem B2658367 : Blo 1865634 2658367 := bstep (se 1 (by rfl) ⟨1993775, by rfl⟩ : syracuseStep 2658367 = 3987551) B3987551
theorem B3543259 : Blo 1865634 3543259 := bstep (se 1 (by rfl) ⟨2657444, by rfl⟩ : syracuseStep 3543259 = 5314889) B5314889
theorem B4198697 : Blo 1865634 4198697 := bstep (se 2 (by rfl) ⟨1574511, by rfl⟩ : syracuseStep 4198697 = 3149023) B3149023
theorem B3363113 : Blo 1865634 3363113 := bstep (se 2 (by rfl) ⟨1261167, by rfl⟩ : syracuseStep 3363113 = 2522335) B2522335
theorem B28741999 : Blo 1865634 28741999 := bstep (se 1 (by rfl) ⟨21556499, by rfl⟩ : syracuseStep 28741999 = 43112999) B43112999
theorem B3543419 : Blo 1865634 3543419 := bstep (se 1 (by rfl) ⟨2657564, by rfl⟩ : syracuseStep 3543419 = 5315129) B5315129
theorem B145519085 : Blo 1865634 145519085 := bstep (se 3 (by rfl) ⟨27284828, by rfl⟩ : syracuseStep 145519085 = 54569657) B54569657
theorem B4198967 : Blo 1865634 4198967 := bstep (se 1 (by rfl) ⟨3149225, by rfl⟩ : syracuseStep 4198967 = 6298451) B6298451
theorem B10629913 : Blo 1865634 10629913 := bstep (se 2 (by rfl) ⟨3986217, by rfl⟩ : syracuseStep 10629913 = 7972435) B7972435
theorem B4199273 : Blo 1865634 4199273 := bstep (se 2 (by rfl) ⟨1574727, by rfl⟩ : syracuseStep 4199273 = 3149455) B3149455
theorem B4199327 : Blo 1865634 4199327 := bstep (se 1 (by rfl) ⟨3149495, by rfl⟩ : syracuseStep 4199327 = 6298991) B6298991
theorem B3150751 : Blo 1865634 3150751 := bstep (se 1 (by rfl) ⟨2363063, by rfl⟩ : syracuseStep 3150751 = 4726127) B4726127
theorem B2798543 : Blo 1865634 2798543 := bstep (se 1 (by rfl) ⟨2098907, by rfl⟩ : syracuseStep 2798543 = 4197815) B4197815
theorem B2798585 : Blo 1865634 2798585 := bstep (se 2 (by rfl) ⟨1049469, by rfl⟩ : syracuseStep 2798585 = 2098939) B2098939
theorem B2798633 : Blo 1865634 2798633 := bstep (se 2 (by rfl) ⟨1049487, by rfl⟩ : syracuseStep 2798633 = 2098975) B2098975
theorem B2798663 : Blo 1865634 2798663 := bstep (se 1 (by rfl) ⟨2098997, by rfl⟩ : syracuseStep 2798663 = 4197995) B4197995
theorem B4199579 : Blo 1865634 4199579 := bstep (se 1 (by rfl) ⟨3149684, by rfl⟩ : syracuseStep 4199579 = 6299369) B6299369
theorem B2798843 : Blo 1865634 2798843 := bstep (se 1 (by rfl) ⟨2099132, by rfl⟩ : syracuseStep 2798843 = 4198265) B4198265
theorem B3593711 : Blo 1865634 3593711 := bstep (se 1 (by rfl) ⟨2695283, by rfl⟩ : syracuseStep 3593711 = 5390567) B5390567
theorem B5043803 : Blo 1865634 5043803 := bstep (se 1 (by rfl) ⟨3782852, by rfl⟩ : syracuseStep 5043803 = 7565705) B7565705
theorem B21272219 : Blo 1865634 21272219 := bstep (se 1 (by rfl) ⟨15954164, by rfl⟩ : syracuseStep 21272219 = 31908329) B31908329
theorem B4200155 : Blo 1865634 4200155 := bstep (se 1 (by rfl) ⟨3150116, by rfl⟩ : syracuseStep 4200155 = 6300233) B6300233
theorem B7182067 : Blo 1865634 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B4200263 : Blo 1865634 4200263 := bstep (se 1 (by rfl) ⟨3150197, by rfl⟩ : syracuseStep 4200263 = 6300395) B6300395
theorem B4724639 : Blo 1865634 4724639 := bstep (se 1 (by rfl) ⟨3543479, by rfl⟩ : syracuseStep 4724639 = 7086959) B7086959
theorem B7976879 : Blo 1865634 7976879 := bstep (se 1 (by rfl) ⟨5982659, by rfl⟩ : syracuseStep 7976879 = 11965319) B11965319
theorem B1865799 : Blo 1865634 1865799 := bstep (se 1 (by rfl) ⟨1399349, by rfl⟩ : syracuseStep 1865799 = 2798699) B2798699
theorem B4257863 : Blo 1865634 4257863 := bstep (se 1 (by rfl) ⟨3193397, by rfl⟩ : syracuseStep 4257863 = 6386795) B6386795
theorem B40384595 : Blo 1865634 40384595 := bstep (se 1 (by rfl) ⟨30288446, by rfl⟩ : syracuseStep 40384595 = 60576893) B60576893
theorem B3193015 : Blo 1865634 3193015 := bstep (se 1 (by rfl) ⟨2394761, by rfl⟩ : syracuseStep 3193015 = 4789523) B4789523
theorem B1865959 : Blo 1865634 1865959 := bstep (se 1 (by rfl) ⟨1399469, by rfl⟩ : syracuseStep 1865959 = 2798939) B2798939
theorem B14178563 : Blo 1865634 14178563 := bstep (se 1 (by rfl) ⟨10633922, by rfl⟩ : syracuseStep 14178563 = 21267845) B21267845
theorem B7084331 : Blo 1865634 7084331 := bstep (se 1 (by rfl) ⟨5313248, by rfl⟩ : syracuseStep 7084331 = 10626497) B10626497
theorem B7084361 : Blo 1865634 7084361 := bstep (se 2 (by rfl) ⟨2656635, by rfl⟩ : syracuseStep 7084361 = 5313271) B5313271
theorem B1866143 : Blo 1865634 1866143 := bstep (se 1 (by rfl) ⟨1399607, by rfl⟩ : syracuseStep 1866143 = 2799215) B2799215
theorem B8968607 : Blo 1865634 8968607 := bstep (se 1 (by rfl) ⟨6726455, by rfl⟩ : syracuseStep 8968607 = 13452911) B13452911
theorem B1866191 : Blo 1865634 1866191 := bstep (se 1 (by rfl) ⟨1399643, by rfl⟩ : syracuseStep 1866191 = 2799287) B2799287
theorem B2800079 : Blo 1865634 2800079 := bstep (se 1 (by rfl) ⟨2100059, by rfl⟩ : syracuseStep 2800079 = 4200119) B4200119
theorem B1866215 : Blo 1865634 1866215 := bstep (se 1 (by rfl) ⟨1399661, by rfl⟩ : syracuseStep 1866215 = 2799323) B2799323
theorem B2800169 : Blo 1865634 2800169 := bstep (se 2 (by rfl) ⟨1050063, by rfl⟩ : syracuseStep 2800169 = 2100127) B2100127
theorem B1866331 : Blo 1865634 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B1866399 : Blo 1865634 1866399 := bstep (se 1 (by rfl) ⟨1399799, by rfl⟩ : syracuseStep 1866399 = 2799599) B2799599
theorem B5044961 : Blo 1865634 5044961 := bstep (se 2 (by rfl) ⟨1891860, by rfl⟩ : syracuseStep 5044961 = 3783721) B3783721
theorem B2800361 : Blo 1865634 2800361 := bstep (se 2 (by rfl) ⟨1050135, by rfl⟩ : syracuseStep 2800361 = 2100271) B2100271
theorem B4201271 : Blo 1865634 4201271 := bstep (se 1 (by rfl) ⟨3150953, by rfl⟩ : syracuseStep 4201271 = 6301907) B6301907
theorem B1866567 : Blo 1865634 1866567 := bstep (se 1 (by rfl) ⟨1399925, by rfl⟩ : syracuseStep 1866567 = 2799851) B2799851
theorem B1866607 : Blo 1865634 1866607 := bstep (se 1 (by rfl) ⟨1399955, by rfl⟩ : syracuseStep 1866607 = 2799911) B2799911
theorem B1866663 : Blo 1865634 1866663 := bstep (se 1 (by rfl) ⟨1399997, by rfl⟩ : syracuseStep 1866663 = 2799995) B2799995
theorem B4201451 : Blo 1865634 4201451 := bstep (se 1 (by rfl) ⟨3151088, by rfl⟩ : syracuseStep 4201451 = 6302177) B6302177
theorem B1866843 : Blo 1865634 1866843 := bstep (se 1 (by rfl) ⟨1400132, by rfl⟩ : syracuseStep 1866843 = 2800265) B2800265
theorem B2800745 : Blo 1865634 2800745 := bstep (se 2 (by rfl) ⟨1050279, by rfl⟩ : syracuseStep 2800745 = 2100559) B2100559
theorem B1866959 : Blo 1865634 1866959 := bstep (se 1 (by rfl) ⟨1400219, by rfl⟩ : syracuseStep 1866959 = 2800439) B2800439
theorem B1866983 : Blo 1865634 1866983 := bstep (se 1 (by rfl) ⟨1400237, by rfl⟩ : syracuseStep 1866983 = 2800475) B2800475
theorem B2800871 : Blo 1865634 2800871 := bstep (se 1 (by rfl) ⟨2100653, by rfl⟩ : syracuseStep 2800871 = 4201307) B4201307
theorem B5979379 : Blo 1865634 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B1867079 : Blo 1865634 1867079 := bstep (se 1 (by rfl) ⟨1400309, by rfl⟩ : syracuseStep 1867079 = 2800619) B2800619
theorem B31890833 : Blo 1865634 31890833 := bstep (se 2 (by rfl) ⟨11959062, by rfl⟩ : syracuseStep 31890833 = 23918125) B23918125
theorem B4259243 : Blo 1865634 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B1867215 : Blo 1865634 1867215 := bstep (se 1 (by rfl) ⟨1400411, by rfl⟩ : syracuseStep 1867215 = 2800823) B2800823
theorem B1867375 : Blo 1865634 1867375 := bstep (se 1 (by rfl) ⟨1400531, by rfl⟩ : syracuseStep 1867375 = 2801063) B2801063
theorem B1867431 : Blo 1865634 1867431 := bstep (se 1 (by rfl) ⟨1400573, by rfl⟩ : syracuseStep 1867431 = 2801147) B2801147
theorem B2801375 : Blo 1865634 2801375 := bstep (se 1 (by rfl) ⟨2101031, by rfl⟩ : syracuseStep 2801375 = 4202063) B4202063
theorem B1867495 : Blo 1865634 1867495 := bstep (se 1 (by rfl) ⟨1400621, by rfl⟩ : syracuseStep 1867495 = 2801243) B2801243
theorem B2801417 : Blo 1865634 2801417 := bstep (se 2 (by rfl) ⟨1050531, by rfl⟩ : syracuseStep 2801417 = 2101063) B2101063
theorem B1867551 : Blo 1865634 1867551 := bstep (se 1 (by rfl) ⟨1400663, by rfl⟩ : syracuseStep 1867551 = 2801327) B2801327
theorem B15949655 : Blo 1865634 15949655 := bstep (se 1 (by rfl) ⟨11962241, by rfl⟩ : syracuseStep 15949655 = 23924483) B23924483
theorem B1867631 : Blo 1865634 1867631 := bstep (se 1 (by rfl) ⟨1400723, by rfl⟩ : syracuseStep 1867631 = 2801447) B2801447
theorem B32333701 : Blo 1865634 32333701 := bstep (se 4 (by rfl) ⟨3031284, by rfl⟩ : syracuseStep 32333701 = 6062569) B6062569
theorem B6299639 : Blo 1865634 6299639 := bstep (se 1 (by rfl) ⟨4724729, by rfl⟩ : syracuseStep 6299639 = 9449459) B9449459
theorem B9453995 : Blo 1865634 9453995 := bstep (se 1 (by rfl) ⟨7090496, by rfl⟩ : syracuseStep 9453995 = 14180993) B14180993
theorem B38322665 : Blo 1865634 38322665 := bstep (se 2 (by rfl) ⟨14370999, by rfl⟩ : syracuseStep 38322665 = 28741999) B28741999
theorem B96961169 : Blo 1865634 96961169 := bstep (se 2 (by rfl) ⟨36360438, by rfl⟩ : syracuseStep 96961169 = 72720877) B72720877
theorem B5980891 : Blo 1865634 5980891 := bstep (se 1 (by rfl) ⟨4485668, by rfl⟩ : syracuseStep 5980891 = 8971337) B8971337
theorem B9446381 : Blo 1865634 9446381 := bstep (se 3 (by rfl) ⟨1771196, by rfl⟩ : syracuseStep 9446381 = 3542393) B3542393
theorem B14173217 : Blo 1865634 14173217 := bstep (se 2 (by rfl) ⟨5314956, by rfl⟩ : syracuseStep 14173217 = 10629913) B10629913
theorem B14181479 : Blo 1865634 14181479 := bstep (se 1 (by rfl) ⟨10636109, by rfl⟩ : syracuseStep 14181479 = 21272219) B21272219
theorem B5317919 : Blo 1865634 5317919 := bstep (se 1 (by rfl) ⟨3988439, by rfl⟩ : syracuseStep 5317919 = 7976879) B7976879
theorem B35898875 : Blo 1865634 35898875 := bstep (se 1 (by rfl) ⟨26924156, by rfl⟩ : syracuseStep 35898875 = 53848313) B53848313
theorem B181569113 : Blo 1865634 181569113 := bstep (se 2 (by rfl) ⟨68088417, by rfl⟩ : syracuseStep 181569113 = 136176835) B136176835
theorem B7972505 : Blo 1865634 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B5982095 : Blo 1865634 5982095 := bstep (se 1 (by rfl) ⟨4486571, by rfl⟩ : syracuseStep 5982095 = 8973143) B8973143
theorem B13453229 : Blo 1865634 13453229 := bstep (se 3 (by rfl) ⟨2522480, by rfl⟩ : syracuseStep 13453229 = 5044961) B5044961
theorem B11962343 : Blo 1865634 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B2361575 : Blo 1865634 2361575 := bstep (se 1 (by rfl) ⟨1771181, by rfl⟩ : syracuseStep 2361575 = 3542363) B3542363
theorem B21260555 : Blo 1865634 21260555 := bstep (se 1 (by rfl) ⟨15945416, by rfl⟩ : syracuseStep 21260555 = 31890833) B31890833
theorem B72747389 : Blo 1865634 72747389 := bstep (se 3 (by rfl) ⟨13640135, by rfl⟩ : syracuseStep 72747389 = 27280271) B27280271
theorem B40356301 : Blo 1865634 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B22145723 : Blo 1865634 22145723 := bstep (se 1 (by rfl) ⟨16609292, by rfl⟩ : syracuseStep 22145723 = 33218585) B33218585
theorem B40381213 : Blo 1865634 40381213 := bstep (se 3 (by rfl) ⟨7571477, by rfl⟩ : syracuseStep 40381213 = 15142955) B15142955
theorem B2362279 : Blo 1865634 2362279 := bstep (se 1 (by rfl) ⟨1771709, by rfl⟩ : syracuseStep 2362279 = 3543419) B3543419
theorem B97012723 : Blo 1865634 97012723 := bstep (se 1 (by rfl) ⟨72759542, by rfl⟩ : syracuseStep 97012723 = 145519085) B145519085
theorem B15141917 : Blo 1865634 15141917 := bstep (se 3 (by rfl) ⟨2839109, by rfl⟩ : syracuseStep 15141917 = 5678219) B5678219
theorem B3148969 : Blo 1865634 3148969 := bstep (se 2 (by rfl) ⟨1180863, by rfl⟩ : syracuseStep 3148969 = 2361727) B2361727
theorem B10628729 : Blo 1865634 10628729 := bstep (se 2 (by rfl) ⟨3985773, by rfl⟩ : syracuseStep 10628729 = 7971547) B7971547
theorem B4722401 : Blo 1865634 4722401 := bstep (se 2 (by rfl) ⟨1770900, by rfl⟩ : syracuseStep 4722401 = 3541801) B3541801
theorem B11357981 : Blo 1865634 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B9449297 : Blo 1865634 9449297 := bstep (se 2 (by rfl) ⟨3543486, by rfl⟩ : syracuseStep 9449297 = 7086973) B7086973
theorem B3149759 : Blo 1865634 3149759 := bstep (se 1 (by rfl) ⟨2362319, by rfl⟩ : syracuseStep 3149759 = 4724639) B4724639
theorem B2838575 : Blo 1865634 2838575 := bstep (se 1 (by rfl) ⟨2128931, by rfl⟩ : syracuseStep 2838575 = 4257863) B4257863
theorem B26923063 : Blo 1865634 26923063 := bstep (se 1 (by rfl) ⟨20192297, by rfl⟩ : syracuseStep 26923063 = 40384595) B40384595
theorem B7090361 : Blo 1865634 7090361 := bstep (se 2 (by rfl) ⟨2658885, by rfl⟩ : syracuseStep 7090361 = 5317771) B5317771
theorem B4722887 : Blo 1865634 4722887 := bstep (se 1 (by rfl) ⟨3542165, by rfl⟩ : syracuseStep 4722887 = 7084331) B7084331
theorem B4722907 : Blo 1865634 4722907 := bstep (se 1 (by rfl) ⟨3542180, by rfl⟩ : syracuseStep 4722907 = 7084361) B7084361
theorem B11965009 : Blo 1865634 11965009 := bstep (se 2 (by rfl) ⟨4486878, by rfl⟩ : syracuseStep 11965009 = 8973757) B8973757
theorem B3191591 : Blo 1865634 3191591 := bstep (se 1 (by rfl) ⟨2393693, by rfl⟩ : syracuseStep 3191591 = 4787387) B4787387
theorem B2798495 : Blo 1865634 2798495 := bstep (se 1 (by rfl) ⟨2098871, by rfl⟩ : syracuseStep 2798495 = 4197743) B4197743
theorem B43111601 : Blo 1865634 43111601 := bstep (se 2 (by rfl) ⟨16166850, by rfl⟩ : syracuseStep 43111601 = 32333701) B32333701
theorem B9450755 : Blo 1865634 9450755 := bstep (se 1 (by rfl) ⟨7088066, by rfl⟩ : syracuseStep 9450755 = 14176133) B14176133
theorem B38303027 : Blo 1865634 38303027 := bstep (se 1 (by rfl) ⟨28727270, by rfl⟩ : syracuseStep 38303027 = 57454541) B57454541
theorem B4199759 : Blo 1865634 4199759 := bstep (se 1 (by rfl) ⟨3149819, by rfl⟩ : syracuseStep 4199759 = 6299639) B6299639
theorem B3151183 : Blo 1865634 3151183 := bstep (se 1 (by rfl) ⟨2363387, by rfl⟩ : syracuseStep 3151183 = 4726775) B4726775
theorem B6296939 : Blo 1865634 6296939 := bstep (se 1 (by rfl) ⟨4722704, by rfl⟩ : syracuseStep 6296939 = 9445409) B9445409
theorem B2798969 : Blo 1865634 2798969 := bstep (se 2 (by rfl) ⟨1049613, by rfl⟩ : syracuseStep 2798969 = 2099227) B2099227
theorem B2798975 : Blo 1865634 2798975 := bstep (se 1 (by rfl) ⟨2099231, by rfl⟩ : syracuseStep 2798975 = 4198463) B4198463
theorem B4199849 : Blo 1865634 4199849 := bstep (se 2 (by rfl) ⟨1574943, by rfl⟩ : syracuseStep 4199849 = 3149887) B3149887
theorem B3544489 : Blo 1865634 3544489 := bstep (se 2 (by rfl) ⟨1329183, by rfl⟩ : syracuseStep 3544489 = 2658367) B2658367
theorem B4199903 : Blo 1865634 4199903 := bstep (se 1 (by rfl) ⟨3149927, by rfl⟩ : syracuseStep 4199903 = 6299855) B6299855
theorem B2799131 : Blo 1865634 2799131 := bstep (se 1 (by rfl) ⟨2099348, by rfl⟩ : syracuseStep 2799131 = 4198697) B4198697
theorem B2242075 : Blo 1865634 2242075 := bstep (se 1 (by rfl) ⟨1681556, by rfl⟩ : syracuseStep 2242075 = 3363113) B3363113
theorem B4257353 : Blo 1865634 4257353 := bstep (se 2 (by rfl) ⟨1596507, by rfl⟩ : syracuseStep 4257353 = 3193015) B3193015
theorem B4724345 : Blo 1865634 4724345 := bstep (se 2 (by rfl) ⟨1771629, by rfl⟩ : syracuseStep 4724345 = 3543259) B3543259
theorem B4544191 : Blo 1865634 4544191 := bstep (se 1 (by rfl) ⟨3408143, by rfl⟩ : syracuseStep 4544191 = 6816287) B6816287
theorem B2799311 : Blo 1865634 2799311 := bstep (se 1 (by rfl) ⟨2099483, by rfl⟩ : syracuseStep 2799311 = 4198967) B4198967
theorem B2799515 : Blo 1865634 2799515 := bstep (se 1 (by rfl) ⟨2099636, by rfl⟩ : syracuseStep 2799515 = 4199273) B4199273
theorem B2799551 : Blo 1865634 2799551 := bstep (se 1 (by rfl) ⟨2099663, by rfl⟩ : syracuseStep 2799551 = 4199327) B4199327
theorem B1865695 : Blo 1865634 1865695 := bstep (se 1 (by rfl) ⟨1399271, by rfl⟩ : syracuseStep 1865695 = 2798543) B2798543
theorem B1865723 : Blo 1865634 1865723 := bstep (se 1 (by rfl) ⟨1399292, by rfl⟩ : syracuseStep 1865723 = 2798585) B2798585
theorem B1865755 : Blo 1865634 1865755 := bstep (se 1 (by rfl) ⟨1399316, by rfl⟩ : syracuseStep 1865755 = 2798633) B2798633
theorem B4200479 : Blo 1865634 4200479 := bstep (se 1 (by rfl) ⟨3150359, by rfl⟩ : syracuseStep 4200479 = 6300719) B6300719
theorem B1865775 : Blo 1865634 1865775 := bstep (se 1 (by rfl) ⟨1399331, by rfl⟩ : syracuseStep 1865775 = 2798663) B2798663
theorem B2799719 : Blo 1865634 2799719 := bstep (se 1 (by rfl) ⟨2099789, by rfl⟩ : syracuseStep 2799719 = 4199579) B4199579
theorem B1865895 : Blo 1865634 1865895 := bstep (se 1 (by rfl) ⟨1399421, by rfl⟩ : syracuseStep 1865895 = 2798843) B2798843
theorem B10918223 : Blo 1865634 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B23927147 : Blo 1865634 23927147 := bstep (se 1 (by rfl) ⟨17945360, by rfl⟩ : syracuseStep 23927147 = 35890721) B35890721
theorem B4200911 : Blo 1865634 4200911 := bstep (se 1 (by rfl) ⟨3150683, by rfl⟩ : syracuseStep 4200911 = 6301367) B6301367
theorem B2800103 : Blo 1865634 2800103 := bstep (se 1 (by rfl) ⟨2100077, by rfl⟩ : syracuseStep 2800103 = 4200155) B4200155
theorem B4201001 : Blo 1865634 4201001 := bstep (se 2 (by rfl) ⟨1575375, by rfl⟩ : syracuseStep 4201001 = 3150751) B3150751
theorem B2800175 : Blo 1865634 2800175 := bstep (se 1 (by rfl) ⟨2100131, by rfl⟩ : syracuseStep 2800175 = 4200263) B4200263
theorem B9583229 : Blo 1865634 9583229 := bstep (se 3 (by rfl) ⟨1796855, by rfl⟩ : syracuseStep 9583229 = 3593711) B3593711
theorem B4725499 : Blo 1865634 4725499 := bstep (se 1 (by rfl) ⟨3544124, by rfl⟩ : syracuseStep 4725499 = 7088249) B7088249
theorem B9452375 : Blo 1865634 9452375 := bstep (se 1 (by rfl) ⟨7089281, by rfl⟩ : syracuseStep 9452375 = 14178563) B14178563
theorem B13450141 : Blo 1865634 13450141 := bstep (se 3 (by rfl) ⟨2521901, by rfl⟩ : syracuseStep 13450141 = 5043803) B5043803
theorem B5979071 : Blo 1865634 5979071 := bstep (se 1 (by rfl) ⟨4484303, by rfl⟩ : syracuseStep 5979071 = 8968607) B8968607
theorem B1866719 : Blo 1865634 1866719 := bstep (se 1 (by rfl) ⟨1400039, by rfl⟩ : syracuseStep 1866719 = 2800079) B2800079
theorem B1866779 : Blo 1865634 1866779 := bstep (se 1 (by rfl) ⟨1400084, by rfl⟩ : syracuseStep 1866779 = 2800169) B2800169
theorem B1866907 : Blo 1865634 1866907 := bstep (se 1 (by rfl) ⟨1400180, by rfl⟩ : syracuseStep 1866907 = 2800361) B2800361
theorem B4725935 : Blo 1865634 4725935 := bstep (se 1 (by rfl) ⟨3544451, by rfl⟩ : syracuseStep 4725935 = 7088903) B7088903
theorem B2800847 : Blo 1865634 2800847 := bstep (se 1 (by rfl) ⟨2100635, by rfl⟩ : syracuseStep 2800847 = 4201271) B4201271
theorem B2800937 : Blo 1865634 2800937 := bstep (se 2 (by rfl) ⟨1050351, by rfl⟩ : syracuseStep 2800937 = 2100703) B2100703
theorem B2800967 : Blo 1865634 2800967 := bstep (se 1 (by rfl) ⟨2100725, by rfl⟩ : syracuseStep 2800967 = 4201451) B4201451
theorem B40361327 : Blo 1865634 40361327 := bstep (se 1 (by rfl) ⟨30270995, by rfl⟩ : syracuseStep 40361327 = 60541991) B60541991
theorem B1867163 : Blo 1865634 1867163 := bstep (se 1 (by rfl) ⟨1400372, by rfl⟩ : syracuseStep 1867163 = 2800745) B2800745
theorem B7085501 : Blo 1865634 7085501 := bstep (se 3 (by rfl) ⟨1328531, by rfl⟩ : syracuseStep 7085501 = 2657063) B2657063
theorem B1867247 : Blo 1865634 1867247 := bstep (se 1 (by rfl) ⟨1400435, by rfl⟩ : syracuseStep 1867247 = 2800871) B2800871
theorem B6725231 : Blo 1865634 6725231 := bstep (se 1 (by rfl) ⟨5043923, by rfl⟩ : syracuseStep 6725231 = 10087847) B10087847
theorem B5676655 : Blo 1865634 5676655 := bstep (se 1 (by rfl) ⟨4257491, by rfl⟩ : syracuseStep 5676655 = 8514983) B8514983
theorem B9576089 : Blo 1865634 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B1867583 : Blo 1865634 1867583 := bstep (se 1 (by rfl) ⟨1400687, by rfl⟩ : syracuseStep 1867583 = 2801375) B2801375
theorem B1867611 : Blo 1865634 1867611 := bstep (se 1 (by rfl) ⟨1400708, by rfl⟩ : syracuseStep 1867611 = 2801417) B2801417
theorem B9445247 : Blo 1865634 9445247 := bstep (se 1 (by rfl) ⟨7083935, by rfl⟩ : syracuseStep 9445247 = 14167871) B14167871
theorem B10633103 : Blo 1865634 10633103 := bstep (se 1 (by rfl) ⟨7974827, by rfl⟩ : syracuseStep 10633103 = 15949655) B15949655
theorem B1892383 : Blo 1865634 1892383 := bstep (se 1 (by rfl) ⟨1419287, by rfl⟩ : syracuseStep 1892383 = 2838575) B2838575
theorem B35897417 : Blo 1865634 35897417 := bstep (se 2 (by rfl) ⟨13461531, by rfl⟩ : syracuseStep 35897417 = 26923063) B26923063
theorem B40378445 : Blo 1865634 40378445 := bstep (se 3 (by rfl) ⟨7570958, by rfl⟩ : syracuseStep 40378445 = 15141917) B15141917
theorem B4726907 : Blo 1865634 4726907 := bstep (se 1 (by rfl) ⟨3545180, by rfl⟩ : syracuseStep 4726907 = 7090361) B7090361
theorem B9454319 : Blo 1865634 9454319 := bstep (se 1 (by rfl) ⟨7090739, by rfl⟩ : syracuseStep 9454319 = 14181479) B14181479
theorem B6300503 : Blo 1865634 6300503 := bstep (se 1 (by rfl) ⟨4725377, by rfl⟩ : syracuseStep 6300503 = 9450755) B9450755
theorem B25535351 : Blo 1865634 25535351 := bstep (se 1 (by rfl) ⟨19151513, by rfl⟩ : syracuseStep 25535351 = 38303027) B38303027
theorem B6300665 : Blo 1865634 6300665 := bstep (se 2 (by rfl) ⟨2362749, by rfl⟩ : syracuseStep 6300665 = 4725499) B4725499
theorem B121046075 : Blo 1865634 121046075 := bstep (se 1 (by rfl) ⟨90784556, by rfl⟩ : syracuseStep 121046075 = 181569113) B181569113
theorem B17933521 : Blo 1865634 17933521 := bstep (se 2 (by rfl) ⟨6725070, by rfl⟩ : syracuseStep 17933521 = 13450141) B13450141
theorem B14173703 : Blo 1865634 14173703 := bstep (se 1 (by rfl) ⟨10630277, by rfl⟩ : syracuseStep 14173703 = 21260555) B21260555
theorem B15951431 : Blo 1865634 15951431 := bstep (se 1 (by rfl) ⟨11963573, by rfl⟩ : syracuseStep 15951431 = 23927147) B23927147
theorem B48498259 : Blo 1865634 48498259 := bstep (se 1 (by rfl) ⟨36373694, by rfl⟩ : syracuseStep 48498259 = 72747389) B72747389
theorem B14763815 : Blo 1865634 14763815 := bstep (se 1 (by rfl) ⟨11072861, by rfl⟩ : syracuseStep 14763815 = 22145723) B22145723
theorem B6301583 : Blo 1865634 6301583 := bstep (se 1 (by rfl) ⟨4726187, by rfl⟩ : syracuseStep 6301583 = 9452375) B9452375
theorem B4483487 : Blo 1865634 4483487 := bstep (se 1 (by rfl) ⟨3362615, by rfl⟩ : syracuseStep 4483487 = 6725231) B6725231
theorem B6384059 : Blo 1865634 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B3148267 : Blo 1865634 3148267 := bstep (se 1 (by rfl) ⟨2361200, by rfl⟩ : syracuseStep 3148267 = 4722401) B4722401
theorem B7571987 : Blo 1865634 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B7088735 : Blo 1865634 7088735 := bstep (se 1 (by rfl) ⟨5316551, by rfl⟩ : syracuseStep 7088735 = 10633103) B10633103
theorem B2099839 : Blo 1865634 2099839 := bstep (se 1 (by rfl) ⟨1574879, by rfl⟩ : syracuseStep 2099839 = 3149759) B3149759
theorem B3148591 : Blo 1865634 3148591 := bstep (se 1 (by rfl) ⟨2361443, by rfl⟩ : syracuseStep 3148591 = 4722887) B4722887
theorem B6302663 : Blo 1865634 6302663 := bstep (se 1 (by rfl) ⟨4726997, by rfl⟩ : syracuseStep 6302663 = 9453995) B9453995
theorem B53808401 : Blo 1865634 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B9448811 : Blo 1865634 9448811 := bstep (se 1 (by rfl) ⟨7086608, by rfl⟩ : syracuseStep 9448811 = 14173217) B14173217
theorem B15953345 : Blo 1865634 15953345 := bstep (se 2 (by rfl) ⟨5982504, by rfl⟩ : syracuseStep 15953345 = 11965009) B11965009
theorem B28741067 : Blo 1865634 28741067 := bstep (se 1 (by rfl) ⟨21555800, by rfl⟩ : syracuseStep 28741067 = 43111601) B43111601
theorem B4197959 : Blo 1865634 4197959 := bstep (se 1 (by rfl) ⟨3148469, by rfl⟩ : syracuseStep 4197959 = 6296939) B6296939
theorem B7974521 : Blo 1865634 7974521 := bstep (se 2 (by rfl) ⟨2990445, by rfl⟩ : syracuseStep 7974521 = 5980891) B5980891
theorem B23932583 : Blo 1865634 23932583 := bstep (se 1 (by rfl) ⟨17949437, by rfl⟩ : syracuseStep 23932583 = 35898875) B35898875
theorem B53841617 : Blo 1865634 53841617 := bstep (se 2 (by rfl) ⟨20190606, by rfl⟩ : syracuseStep 53841617 = 40381213) B40381213
theorem B2838235 : Blo 1865634 2838235 := bstep (se 1 (by rfl) ⟨2128676, by rfl⟩ : syracuseStep 2838235 = 4257353) B4257353
theorem B3149563 : Blo 1865634 3149563 := bstep (se 1 (by rfl) ⟨2362172, by rfl⟩ : syracuseStep 3149563 = 4724345) B4724345
theorem B3149705 : Blo 1865634 3149705 := bstep (se 2 (by rfl) ⟨1181139, by rfl⟩ : syracuseStep 3149705 = 2362279) B2362279
theorem B7278815 : Blo 1865634 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B4198625 : Blo 1865634 4198625 := bstep (se 2 (by rfl) ⟨1574484, by rfl⟩ : syracuseStep 4198625 = 3148969) B3148969
theorem B25555277 : Blo 1865634 25555277 := bstep (se 3 (by rfl) ⟨4791614, by rfl⟩ : syracuseStep 25555277 = 9583229) B9583229
theorem B3986047 : Blo 1865634 3986047 := bstep (se 1 (by rfl) ⟨2989535, by rfl⟩ : syracuseStep 3986047 = 5979071) B5979071
theorem B3150623 : Blo 1865634 3150623 := bstep (se 1 (by rfl) ⟨2362967, by rfl⟩ : syracuseStep 3150623 = 4725935) B4725935
theorem B26907551 : Blo 1865634 26907551 := bstep (se 1 (by rfl) ⟨20180663, by rfl⟩ : syracuseStep 26907551 = 40361327) B40361327
theorem B6058921 : Blo 1865634 6058921 := bstep (se 2 (by rfl) ⟨2272095, by rfl⟩ : syracuseStep 6058921 = 4544191) B4544191
theorem B4723667 : Blo 1865634 4723667 := bstep (se 1 (by rfl) ⟨3542750, by rfl⟩ : syracuseStep 4723667 = 7085501) B7085501
theorem B6296831 : Blo 1865634 6296831 := bstep (se 1 (by rfl) ⟨4722623, by rfl⟩ : syracuseStep 6296831 = 9445247) B9445247
theorem B6297209 : Blo 1865634 6297209 := bstep (se 2 (by rfl) ⟨2361453, by rfl⟩ : syracuseStep 6297209 = 4722907) B4722907
theorem B25548443 : Blo 1865634 25548443 := bstep (se 1 (by rfl) ⟨19161332, by rfl⟩ : syracuseStep 25548443 = 38322665) B38322665
theorem B2127727 : Blo 1865634 2127727 := bstep (se 1 (by rfl) ⟨1595795, by rfl⟩ : syracuseStep 2127727 = 3191591) B3191591
theorem B6297533 : Blo 1865634 6297533 := bstep (se 3 (by rfl) ⟨1180787, by rfl⟩ : syracuseStep 6297533 = 2361575) B2361575
theorem B1865663 : Blo 1865634 1865663 := bstep (se 1 (by rfl) ⟨1399247, by rfl⟩ : syracuseStep 1865663 = 2798495) B2798495
theorem B6297587 : Blo 1865634 6297587 := bstep (se 1 (by rfl) ⟨4723190, by rfl⟩ : syracuseStep 6297587 = 9446381) B9446381
theorem B3545279 : Blo 1865634 3545279 := bstep (se 1 (by rfl) ⟨2658959, by rfl⟩ : syracuseStep 3545279 = 5317919) B5317919
theorem B2799839 : Blo 1865634 2799839 := bstep (se 1 (by rfl) ⟨2099879, by rfl⟩ : syracuseStep 2799839 = 4199759) B4199759
theorem B1865979 : Blo 1865634 1865979 := bstep (se 1 (by rfl) ⟨1399484, by rfl⟩ : syracuseStep 1865979 = 2798969) B2798969
theorem B1865983 : Blo 1865634 1865983 := bstep (se 1 (by rfl) ⟨1399487, by rfl⟩ : syracuseStep 1865983 = 2798975) B2798975
theorem B2799899 : Blo 1865634 2799899 := bstep (se 1 (by rfl) ⟨2099924, by rfl⟩ : syracuseStep 2799899 = 4199849) B4199849
theorem B2799935 : Blo 1865634 2799935 := bstep (se 1 (by rfl) ⟨2099951, by rfl⟩ : syracuseStep 2799935 = 4199903) B4199903
theorem B1866087 : Blo 1865634 1866087 := bstep (se 1 (by rfl) ⟨1399565, by rfl⟩ : syracuseStep 1866087 = 2799131) B2799131
theorem B5315003 : Blo 1865634 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B1866207 : Blo 1865634 1866207 := bstep (se 1 (by rfl) ⟨1399655, by rfl⟩ : syracuseStep 1866207 = 2799311) B2799311
theorem B3988063 : Blo 1865634 3988063 := bstep (se 1 (by rfl) ⟨2991047, by rfl⟩ : syracuseStep 3988063 = 5982095) B5982095
theorem B1866343 : Blo 1865634 1866343 := bstep (se 1 (by rfl) ⟨1399757, by rfl⟩ : syracuseStep 1866343 = 2799515) B2799515
theorem B8968819 : Blo 1865634 8968819 := bstep (se 1 (by rfl) ⟨6726614, by rfl⟩ : syracuseStep 8968819 = 13453229) B13453229
theorem B1866367 : Blo 1865634 1866367 := bstep (se 1 (by rfl) ⟨1399775, by rfl⟩ : syracuseStep 1866367 = 2799551) B2799551
theorem B129350297 : Blo 1865634 129350297 := bstep (se 2 (by rfl) ⟨48506361, by rfl⟩ : syracuseStep 129350297 = 97012723) B97012723
theorem B2800319 : Blo 1865634 2800319 := bstep (se 1 (by rfl) ⟨2100239, by rfl⟩ : syracuseStep 2800319 = 4200479) B4200479
theorem B1866479 : Blo 1865634 1866479 := bstep (se 1 (by rfl) ⟨1399859, by rfl⟩ : syracuseStep 1866479 = 2799719) B2799719
theorem B2800607 : Blo 1865634 2800607 := bstep (se 1 (by rfl) ⟨2100455, by rfl⟩ : syracuseStep 2800607 = 4200911) B4200911
theorem B1866735 : Blo 1865634 1866735 := bstep (se 1 (by rfl) ⟨1400051, by rfl⟩ : syracuseStep 1866735 = 2800103) B2800103
theorem B2800667 : Blo 1865634 2800667 := bstep (se 1 (by rfl) ⟨2100500, by rfl⟩ : syracuseStep 2800667 = 4201001) B4201001
theorem B1866783 : Blo 1865634 1866783 := bstep (se 1 (by rfl) ⟨1400087, by rfl⟩ : syracuseStep 1866783 = 2800175) B2800175
theorem B258563117 : Blo 1865634 258563117 := bstep (se 3 (by rfl) ⟨48480584, by rfl⟩ : syracuseStep 258563117 = 96961169) B96961169
theorem B4201577 : Blo 1865634 4201577 := bstep (se 2 (by rfl) ⟨1575591, by rfl⟩ : syracuseStep 4201577 = 3151183) B3151183
theorem B4725985 : Blo 1865634 4725985 := bstep (se 2 (by rfl) ⟨1772244, by rfl⟩ : syracuseStep 4725985 = 3544489) B3544489
theorem B2989433 : Blo 1865634 2989433 := bstep (se 2 (by rfl) ⟨1121037, by rfl⟩ : syracuseStep 2989433 = 2242075) B2242075
theorem B1867231 : Blo 1865634 1867231 := bstep (se 1 (by rfl) ⟨1400423, by rfl⟩ : syracuseStep 1867231 = 2800847) B2800847
theorem B7568873 : Blo 1865634 7568873 := bstep (se 2 (by rfl) ⟨2838327, by rfl⟩ : syracuseStep 7568873 = 5676655) B5676655
theorem B1867291 : Blo 1865634 1867291 := bstep (se 1 (by rfl) ⟨1400468, by rfl⟩ : syracuseStep 1867291 = 2800937) B2800937
theorem B1867311 : Blo 1865634 1867311 := bstep (se 1 (by rfl) ⟨1400483, by rfl⟩ : syracuseStep 1867311 = 2800967) B2800967
theorem B7085819 : Blo 1865634 7085819 := bstep (se 1 (by rfl) ⟨5314364, by rfl⟩ : syracuseStep 7085819 = 10628729) B10628729
theorem B6299531 : Blo 1865634 6299531 := bstep (se 1 (by rfl) ⟨4724648, by rfl⟩ : syracuseStep 6299531 = 9449297) B9449297
theorem B31899581 : Blo 1865634 31899581 := bstep (se 3 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 31899581 = 11962343) B11962343
theorem B26918963 : Blo 1865634 26918963 := bstep (se 1 (by rfl) ⟨20189222, by rfl⟩ : syracuseStep 26918963 = 40378445) B40378445
theorem B10092709 : Blo 1865634 10092709 := bstep (se 4 (by rfl) ⟨946191, by rfl⟩ : syracuseStep 10092709 = 1892383) B1892383
theorem B17023567 : Blo 1865634 17023567 := bstep (se 1 (by rfl) ⟨12767675, by rfl⟩ : syracuseStep 17023567 = 25535351) B25535351
theorem B5317417 : Blo 1865634 5317417 := bstep (se 2 (by rfl) ⟨1994031, by rfl⟩ : syracuseStep 5317417 = 3988063) B3988063
theorem B7971821 : Blo 1865634 7971821 := bstep (se 3 (by rfl) ⟨1494716, by rfl⟩ : syracuseStep 7971821 = 2989433) B2989433
theorem B10634287 : Blo 1865634 10634287 := bstep (se 1 (by rfl) ⟨7975715, by rfl⟩ : syracuseStep 10634287 = 15951431) B15951431
theorem B17032295 : Blo 1865634 17032295 := bstep (se 1 (by rfl) ⟨12774221, by rfl⟩ : syracuseStep 17032295 = 25548443) B25548443
theorem B8078561 : Blo 1865634 8078561 := bstep (se 2 (by rfl) ⟨3029460, by rfl⟩ : syracuseStep 8078561 = 6058921) B6058921
theorem B6301313 : Blo 1865634 6301313 := bstep (se 2 (by rfl) ⟨2362992, by rfl⟩ : syracuseStep 6301313 = 4725985) B4725985
theorem B5047991 : Blo 1865634 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B11347877 : Blo 1865634 11347877 := bstep (se 4 (by rfl) ⟨1063863, by rfl⟩ : syracuseStep 11347877 = 2127727) B2127727
theorem B10635563 : Blo 1865634 10635563 := bstep (se 1 (by rfl) ⟨7976672, by rfl⟩ : syracuseStep 10635563 = 15953345) B15953345
theorem B2099803 : Blo 1865634 2099803 := bstep (se 1 (by rfl) ⟨1574852, by rfl⟩ : syracuseStep 2099803 = 3149705) B3149705
theorem B23931611 : Blo 1865634 23931611 := bstep (se 1 (by rfl) ⟨17948708, by rfl⟩ : syracuseStep 23931611 = 35897417) B35897417
theorem B4852543 : Blo 1865634 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B6302879 : Blo 1865634 6302879 := bstep (se 1 (by rfl) ⟨4727159, by rfl⟩ : syracuseStep 6302879 = 9454319) B9454319
theorem B2100415 : Blo 1865634 2100415 := bstep (se 1 (by rfl) ⟨1575311, by rfl⟩ : syracuseStep 2100415 = 3150623) B3150623
theorem B3149111 : Blo 1865634 3149111 := bstep (se 1 (by rfl) ⟨2361833, by rfl⟩ : syracuseStep 3149111 = 4723667) B4723667
theorem B4197689 : Blo 1865634 4197689 := bstep (se 2 (by rfl) ⟨1574133, by rfl⟩ : syracuseStep 4197689 = 3148267) B3148267
theorem B4197887 : Blo 1865634 4197887 := bstep (se 1 (by rfl) ⟨3148415, by rfl⟩ : syracuseStep 4197887 = 6296831) B6296831
theorem B9449135 : Blo 1865634 9449135 := bstep (se 1 (by rfl) ⟨7086851, by rfl⟩ : syracuseStep 9449135 = 14173703) B14173703
theorem B4198121 : Blo 1865634 4198121 := bstep (se 2 (by rfl) ⟨1574295, by rfl⟩ : syracuseStep 4198121 = 3148591) B3148591
theorem B4198139 : Blo 1865634 4198139 := bstep (se 1 (by rfl) ⟨3148604, by rfl⟩ : syracuseStep 4198139 = 6297209) B6297209
theorem B9842543 : Blo 1865634 9842543 := bstep (se 1 (by rfl) ⟨7381907, by rfl⟩ : syracuseStep 9842543 = 14763815) B14763815
theorem B4198355 : Blo 1865634 4198355 := bstep (se 1 (by rfl) ⟨3148766, by rfl⟩ : syracuseStep 4198355 = 6297533) B6297533
theorem B4198391 : Blo 1865634 4198391 := bstep (se 1 (by rfl) ⟨3148793, by rfl⟩ : syracuseStep 4198391 = 6297587) B6297587
theorem B2363519 : Blo 1865634 2363519 := bstep (se 1 (by rfl) ⟨1772639, by rfl⟩ : syracuseStep 2363519 = 3545279) B3545279
theorem B4256039 : Blo 1865634 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B3543335 : Blo 1865634 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B86233531 : Blo 1865634 86233531 := bstep (se 1 (by rfl) ⟨64675148, by rfl⟩ : syracuseStep 86233531 = 129350297) B129350297
theorem B64664345 : Blo 1865634 64664345 := bstep (se 2 (by rfl) ⟨24249129, by rfl⟩ : syracuseStep 64664345 = 48498259) B48498259
theorem B4199417 : Blo 1865634 4199417 := bstep (se 2 (by rfl) ⟨1574781, by rfl⟩ : syracuseStep 4199417 = 3149563) B3149563
theorem B2798639 : Blo 1865634 2798639 := bstep (se 1 (by rfl) ⟨2098979, by rfl⟩ : syracuseStep 2798639 = 4197959) B4197959
theorem B15955055 : Blo 1865634 15955055 := bstep (se 1 (by rfl) ⟨11966291, by rfl⟩ : syracuseStep 15955055 = 23932583) B23932583
theorem B35894411 : Blo 1865634 35894411 := bstep (se 1 (by rfl) ⟨26920808, by rfl⟩ : syracuseStep 35894411 = 53841617) B53841617
theorem B4723879 : Blo 1865634 4723879 := bstep (se 1 (by rfl) ⟨3542909, by rfl⟩ : syracuseStep 4723879 = 7085819) B7085819
theorem B4199687 : Blo 1865634 4199687 := bstep (se 1 (by rfl) ⟨3149765, by rfl⟩ : syracuseStep 4199687 = 6299531) B6299531
theorem B3151271 : Blo 1865634 3151271 := bstep (se 1 (by rfl) ⟨2363453, by rfl⟩ : syracuseStep 3151271 = 4726907) B4726907
theorem B2799083 : Blo 1865634 2799083 := bstep (se 1 (by rfl) ⟨2099312, by rfl⟩ : syracuseStep 2799083 = 4198625) B4198625
theorem B17036851 : Blo 1865634 17036851 := bstep (se 1 (by rfl) ⟨12777638, by rfl⟩ : syracuseStep 17036851 = 25555277) B25555277
theorem B4200335 : Blo 1865634 4200335 := bstep (se 1 (by rfl) ⟨3150251, by rfl⟩ : syracuseStep 4200335 = 6300503) B6300503
theorem B17938367 : Blo 1865634 17938367 := bstep (se 1 (by rfl) ⟨13453775, by rfl⟩ : syracuseStep 17938367 = 26907551) B26907551
theorem B4200443 : Blo 1865634 4200443 := bstep (se 1 (by rfl) ⟨3150332, by rfl⟩ : syracuseStep 4200443 = 6300665) B6300665
theorem B80697383 : Blo 1865634 80697383 := bstep (se 1 (by rfl) ⟨60523037, by rfl⟩ : syracuseStep 80697383 = 121046075) B121046075
theorem B11958425 : Blo 1865634 11958425 := bstep (se 2 (by rfl) ⟨4484409, by rfl⟩ : syracuseStep 11958425 = 8968819) B8968819
theorem B5314729 : Blo 1865634 5314729 := bstep (se 2 (by rfl) ⟨1993023, by rfl⟩ : syracuseStep 5314729 = 3986047) B3986047
theorem B2799785 : Blo 1865634 2799785 := bstep (se 2 (by rfl) ⟨1049919, by rfl⟩ : syracuseStep 2799785 = 2099839) B2099839
theorem B4201055 : Blo 1865634 4201055 := bstep (se 1 (by rfl) ⟨3150791, by rfl⟩ : syracuseStep 4201055 = 6301583) B6301583
theorem B1866559 : Blo 1865634 1866559 := bstep (se 1 (by rfl) ⟨1399919, by rfl⟩ : syracuseStep 1866559 = 2799839) B2799839
theorem B1866599 : Blo 1865634 1866599 := bstep (se 1 (by rfl) ⟨1399949, by rfl⟩ : syracuseStep 1866599 = 2799899) B2799899
theorem B1866623 : Blo 1865634 1866623 := bstep (se 1 (by rfl) ⟨1399967, by rfl⟩ : syracuseStep 1866623 = 2799935) B2799935
theorem B2988991 : Blo 1865634 2988991 := bstep (se 1 (by rfl) ⟨2241743, by rfl⟩ : syracuseStep 2988991 = 4483487) B4483487
theorem B23911361 : Blo 1865634 23911361 := bstep (se 2 (by rfl) ⟨8966760, by rfl⟩ : syracuseStep 23911361 = 17933521) B17933521
theorem B4725823 : Blo 1865634 4725823 := bstep (se 1 (by rfl) ⟨3544367, by rfl⟩ : syracuseStep 4725823 = 7088735) B7088735
theorem B1866879 : Blo 1865634 1866879 := bstep (se 1 (by rfl) ⟨1400159, by rfl⟩ : syracuseStep 1866879 = 2800319) B2800319
theorem B4201775 : Blo 1865634 4201775 := bstep (se 1 (by rfl) ⟨3151331, by rfl⟩ : syracuseStep 4201775 = 6302663) B6302663
theorem B1867071 : Blo 1865634 1867071 := bstep (se 1 (by rfl) ⟨1400303, by rfl⟩ : syracuseStep 1867071 = 2800607) B2800607
theorem B1867111 : Blo 1865634 1867111 := bstep (se 1 (by rfl) ⟨1400333, by rfl⟩ : syracuseStep 1867111 = 2800667) B2800667
theorem B172375411 : Blo 1865634 172375411 := bstep (se 1 (by rfl) ⟨129281558, by rfl⟩ : syracuseStep 172375411 = 258563117) B258563117
theorem B2801051 : Blo 1865634 2801051 := bstep (se 1 (by rfl) ⟨2100788, by rfl⟩ : syracuseStep 2801051 = 4201577) B4201577
theorem B35872267 : Blo 1865634 35872267 := bstep (se 1 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 35872267 = 53808401) B53808401
theorem B6299207 : Blo 1865634 6299207 := bstep (se 1 (by rfl) ⟨4724405, by rfl⟩ : syracuseStep 6299207 = 9448811) B9448811
theorem B3784313 : Blo 1865634 3784313 := bstep (se 2 (by rfl) ⟨1419117, by rfl⟩ : syracuseStep 3784313 = 2838235) B2838235
theorem B19160711 : Blo 1865634 19160711 := bstep (se 1 (by rfl) ⟨14370533, by rfl⟩ : syracuseStep 19160711 = 28741067) B28741067
theorem B5045915 : Blo 1865634 5045915 := bstep (se 1 (by rfl) ⟨3784436, by rfl⟩ : syracuseStep 5045915 = 7568873) B7568873
theorem B5316347 : Blo 1865634 5316347 := bstep (se 1 (by rfl) ⟨3987260, by rfl⟩ : syracuseStep 5316347 = 7974521) B7974521
theorem B21266387 : Blo 1865634 21266387 := bstep (se 1 (by rfl) ⟨15949790, by rfl⟩ : syracuseStep 21266387 = 31899581) B31899581
theorem B7086305 : Blo 1865634 7086305 := bstep (se 2 (by rfl) ⟨2657364, by rfl⟩ : syracuseStep 7086305 = 5314729) B5314729
theorem B11354863 : Blo 1865634 11354863 := bstep (se 1 (by rfl) ⟨8516147, by rfl⟩ : syracuseStep 11354863 = 17032295) B17032295
theorem B23929607 : Blo 1865634 23929607 := bstep (se 1 (by rfl) ⟨17947205, by rfl⟩ : syracuseStep 23929607 = 35894411) B35894411
theorem B53798255 : Blo 1865634 53798255 := bstep (se 1 (by rfl) ⟨40348691, by rfl⟩ : syracuseStep 53798255 = 80697383) B80697383
theorem B6301097 : Blo 1865634 6301097 := bstep (se 2 (by rfl) ⟨2362911, by rfl⟩ : syracuseStep 6301097 = 4725823) B4725823
theorem B7972283 : Blo 1865634 7972283 := bstep (se 1 (by rfl) ⟨5979212, by rfl⟩ : syracuseStep 7972283 = 11958425) B11958425
theorem B2099407 : Blo 1865634 2099407 := bstep (se 1 (by rfl) ⟨1574555, by rfl⟩ : syracuseStep 2099407 = 3149111) B3149111
theorem B12773807 : Blo 1865634 12773807 := bstep (se 1 (by rfl) ⟨9580355, by rfl⟩ : syracuseStep 12773807 = 19160711) B19160711
theorem B2837359 : Blo 1865634 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B2362223 : Blo 1865634 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B6302717 : Blo 1865634 6302717 := bstep (se 3 (by rfl) ⟨1181759, by rfl⟩ : syracuseStep 6302717 = 2363519) B2363519
theorem B114978041 : Blo 1865634 114978041 := bstep (se 2 (by rfl) ⟨43116765, by rfl⟩ : syracuseStep 114978041 = 86233531) B86233531
theorem B10636703 : Blo 1865634 10636703 := bstep (se 1 (by rfl) ⟨7977527, by rfl⟩ : syracuseStep 10636703 = 15955055) B15955055
theorem B5385707 : Blo 1865634 5385707 := bstep (se 1 (by rfl) ⟨4039280, by rfl⟩ : syracuseStep 5385707 = 8078561) B8078561
theorem B2100847 : Blo 1865634 2100847 := bstep (se 1 (by rfl) ⟨1575635, by rfl⟩ : syracuseStep 2100847 = 3151271) B3151271
theorem B7089889 : Blo 1865634 7089889 := bstep (se 2 (by rfl) ⟨2658708, by rfl⟩ : syracuseStep 7089889 = 5317417) B5317417
theorem B7565251 : Blo 1865634 7565251 := bstep (se 1 (by rfl) ⟨5673938, by rfl⟩ : syracuseStep 7565251 = 11347877) B11347877
theorem B7090375 : Blo 1865634 7090375 := bstep (se 1 (by rfl) ⟨5317781, by rfl⟩ : syracuseStep 7090375 = 10635563) B10635563
theorem B15954407 : Blo 1865634 15954407 := bstep (se 1 (by rfl) ⟨11965805, by rfl⟩ : syracuseStep 15954407 = 23931611) B23931611
theorem B47829689 : Blo 1865634 47829689 := bstep (se 2 (by rfl) ⟨17936133, by rfl⟩ : syracuseStep 47829689 = 35872267) B35872267
theorem B172438253 : Blo 1865634 172438253 := bstep (se 3 (by rfl) ⟨32332172, by rfl⟩ : syracuseStep 172438253 = 64664345) B64664345
theorem B2798459 : Blo 1865634 2798459 := bstep (se 1 (by rfl) ⟨2098844, by rfl⟩ : syracuseStep 2798459 = 4197689) B4197689
theorem B2798591 : Blo 1865634 2798591 := bstep (se 1 (by rfl) ⟨2098943, by rfl⟩ : syracuseStep 2798591 = 4197887) B4197887
theorem B4199471 : Blo 1865634 4199471 := bstep (se 1 (by rfl) ⟨3149603, by rfl⟩ : syracuseStep 4199471 = 6299207) B6299207
theorem B3363943 : Blo 1865634 3363943 := bstep (se 1 (by rfl) ⟨2522957, by rfl⟩ : syracuseStep 3363943 = 5045915) B5045915
theorem B2798747 : Blo 1865634 2798747 := bstep (se 1 (by rfl) ⟨2099060, by rfl⟩ : syracuseStep 2798747 = 4198121) B4198121
theorem B2798759 : Blo 1865634 2798759 := bstep (se 1 (by rfl) ⟨2099069, by rfl⟩ : syracuseStep 2798759 = 4198139) B4198139
theorem B3544231 : Blo 1865634 3544231 := bstep (se 1 (by rfl) ⟨2658173, by rfl⟩ : syracuseStep 3544231 = 5316347) B5316347
theorem B2798903 : Blo 1865634 2798903 := bstep (se 1 (by rfl) ⟨2099177, by rfl⟩ : syracuseStep 2798903 = 4198355) B4198355
theorem B14177591 : Blo 1865634 14177591 := bstep (se 1 (by rfl) ⟨10633193, by rfl⟩ : syracuseStep 14177591 = 21266387) B21266387
theorem B2798927 : Blo 1865634 2798927 := bstep (se 1 (by rfl) ⟨2099195, by rfl⟩ : syracuseStep 2798927 = 4198391) B4198391
theorem B17945975 : Blo 1865634 17945975 := bstep (se 1 (by rfl) ⟨13459481, by rfl⟩ : syracuseStep 17945975 = 26918963) B26918963
theorem B13456945 : Blo 1865634 13456945 := bstep (se 2 (by rfl) ⟨5046354, by rfl⟩ : syracuseStep 13456945 = 10092709) B10092709
theorem B5314547 : Blo 1865634 5314547 := bstep (se 1 (by rfl) ⟨3985910, by rfl⟩ : syracuseStep 5314547 = 7971821) B7971821
theorem B2799611 : Blo 1865634 2799611 := bstep (se 1 (by rfl) ⟨2099708, by rfl⟩ : syracuseStep 2799611 = 4199417) B4199417
theorem B1865759 : Blo 1865634 1865759 := bstep (se 1 (by rfl) ⟨1399319, by rfl⟩ : syracuseStep 1865759 = 2798639) B2798639
theorem B22698089 : Blo 1865634 22698089 := bstep (se 2 (by rfl) ⟨8511783, by rfl⟩ : syracuseStep 22698089 = 17023567) B17023567
theorem B2799737 : Blo 1865634 2799737 := bstep (se 2 (by rfl) ⟨1049901, by rfl⟩ : syracuseStep 2799737 = 2099803) B2099803
theorem B2799791 : Blo 1865634 2799791 := bstep (se 1 (by rfl) ⟨2099843, by rfl⟩ : syracuseStep 2799791 = 4199687) B4199687
theorem B1866055 : Blo 1865634 1866055 := bstep (se 1 (by rfl) ⟨1399541, by rfl⟩ : syracuseStep 1866055 = 2799083) B2799083
theorem B6470057 : Blo 1865634 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B4200875 : Blo 1865634 4200875 := bstep (se 1 (by rfl) ⟨3150656, by rfl⟩ : syracuseStep 4200875 = 6301313) B6301313
theorem B3365327 : Blo 1865634 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2800223 : Blo 1865634 2800223 := bstep (se 1 (by rfl) ⟨2100167, by rfl⟩ : syracuseStep 2800223 = 4200335) B4200335
theorem B11958911 : Blo 1865634 11958911 := bstep (se 1 (by rfl) ⟨8969183, by rfl⟩ : syracuseStep 11958911 = 17938367) B17938367
theorem B2800295 : Blo 1865634 2800295 := bstep (se 1 (by rfl) ⟨2100221, by rfl⟩ : syracuseStep 2800295 = 4200443) B4200443
theorem B14179049 : Blo 1865634 14179049 := bstep (se 2 (by rfl) ⟨5317143, by rfl⟩ : syracuseStep 14179049 = 10634287) B10634287
theorem B1866523 : Blo 1865634 1866523 := bstep (se 1 (by rfl) ⟨1399892, by rfl⟩ : syracuseStep 1866523 = 2799785) B2799785
theorem B6298505 : Blo 1865634 6298505 := bstep (se 2 (by rfl) ⟨2361939, by rfl⟩ : syracuseStep 6298505 = 4723879) B4723879
theorem B2800553 : Blo 1865634 2800553 := bstep (se 2 (by rfl) ⟨1050207, by rfl⟩ : syracuseStep 2800553 = 2100415) B2100415
theorem B2800703 : Blo 1865634 2800703 := bstep (se 1 (by rfl) ⟨2100527, by rfl⟩ : syracuseStep 2800703 = 4201055) B4201055
theorem B229833881 : Blo 1865634 229833881 := bstep (se 2 (by rfl) ⟨86187705, by rfl⟩ : syracuseStep 229833881 = 172375411) B172375411
theorem B15940907 : Blo 1865634 15940907 := bstep (se 1 (by rfl) ⟨11955680, by rfl⟩ : syracuseStep 15940907 = 23911361) B23911361
theorem B22715801 : Blo 1865634 22715801 := bstep (se 2 (by rfl) ⟨8518425, by rfl⟩ : syracuseStep 22715801 = 17036851) B17036851
theorem B4201919 : Blo 1865634 4201919 := bstep (se 1 (by rfl) ⟨3151439, by rfl⟩ : syracuseStep 4201919 = 6302879) B6302879
theorem B2801183 : Blo 1865634 2801183 := bstep (se 1 (by rfl) ⟨2100887, by rfl⟩ : syracuseStep 2801183 = 4201775) B4201775
theorem B1867367 : Blo 1865634 1867367 := bstep (se 1 (by rfl) ⟨1400525, by rfl⟩ : syracuseStep 1867367 = 2801051) B2801051
theorem B15941285 : Blo 1865634 15941285 := bstep (se 4 (by rfl) ⟨1494495, by rfl⟩ : syracuseStep 15941285 = 2988991) B2988991
theorem B2522875 : Blo 1865634 2522875 := bstep (se 1 (by rfl) ⟨1892156, by rfl⟩ : syracuseStep 2522875 = 3784313) B3784313
theorem B6299423 : Blo 1865634 6299423 := bstep (se 1 (by rfl) ⟨4724567, by rfl⟩ : syracuseStep 6299423 = 9449135) B9449135
theorem B6561695 : Blo 1865634 6561695 := bstep (se 1 (by rfl) ⟨4921271, by rfl⟩ : syracuseStep 6561695 = 9842543) B9842543
theorem B9453833 : Blo 1865634 9453833 := bstep (se 2 (by rfl) ⟨3545187, by rfl⟩ : syracuseStep 9453833 = 7090375) B7090375
theorem B114958835 : Blo 1865634 114958835 := bstep (se 1 (by rfl) ⟨86219126, by rfl⟩ : syracuseStep 114958835 = 172438253) B172438253
theorem B35865503 : Blo 1865634 35865503 := bstep (se 1 (by rfl) ⟨26899127, by rfl⟩ : syracuseStep 35865503 = 53798255) B53798255
theorem B15139817 : Blo 1865634 15139817 := bstep (se 2 (by rfl) ⟨5677431, by rfl⟩ : syracuseStep 15139817 = 11354863) B11354863
theorem B17253485 : Blo 1865634 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B15132059 : Blo 1865634 15132059 := bstep (se 1 (by rfl) ⟨11349044, by rfl⟩ : syracuseStep 15132059 = 22698089) B22698089
theorem B7972607 : Blo 1865634 7972607 := bstep (se 1 (by rfl) ⟨5979455, by rfl⟩ : syracuseStep 7972607 = 11958911) B11958911
theorem B15132581 : Blo 1865634 15132581 := bstep (se 4 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 15132581 = 2837359) B2837359
theorem B17942593 : Blo 1865634 17942593 := bstep (se 2 (by rfl) ⟨6728472, by rfl⟩ : syracuseStep 17942593 = 13456945) B13456945
theorem B10627271 : Blo 1865634 10627271 := bstep (se 1 (by rfl) ⟨7970453, by rfl⟩ : syracuseStep 10627271 = 15940907) B15940907
theorem B3590471 : Blo 1865634 3590471 := bstep (se 1 (by rfl) ⟨2692853, by rfl⟩ : syracuseStep 3590471 = 5385707) B5385707
theorem B10627523 : Blo 1865634 10627523 := bstep (se 1 (by rfl) ⟨7970642, by rfl⟩ : syracuseStep 10627523 = 15941285) B15941285
theorem B10087001 : Blo 1865634 10087001 := bstep (se 2 (by rfl) ⟨3782625, by rfl⟩ : syracuseStep 10087001 = 7565251) B7565251
theorem B10636271 : Blo 1865634 10636271 := bstep (se 1 (by rfl) ⟨7977203, by rfl⟩ : syracuseStep 10636271 = 15954407) B15954407
theorem B31886459 : Blo 1865634 31886459 := bstep (se 1 (by rfl) ⟨23914844, by rfl⟩ : syracuseStep 31886459 = 47829689) B47829689
theorem B15953071 : Blo 1865634 15953071 := bstep (se 1 (by rfl) ⟨11964803, by rfl⟩ : syracuseStep 15953071 = 23929607) B23929607
theorem B3543031 : Blo 1865634 3543031 := bstep (se 1 (by rfl) ⟨2657273, by rfl⟩ : syracuseStep 3543031 = 5314547) B5314547
theorem B4485257 : Blo 1865634 4485257 := bstep (se 2 (by rfl) ⟨1681971, by rfl⟩ : syracuseStep 4485257 = 3363943) B3363943
theorem B8515871 : Blo 1865634 8515871 := bstep (se 1 (by rfl) ⟨6386903, by rfl⟩ : syracuseStep 8515871 = 12773807) B12773807
theorem B4199003 : Blo 1865634 4199003 := bstep (se 1 (by rfl) ⟨3149252, by rfl⟩ : syracuseStep 4199003 = 6298505) B6298505
theorem B15143867 : Blo 1865634 15143867 := bstep (se 1 (by rfl) ⟨11357900, by rfl⟩ : syracuseStep 15143867 = 22715801) B22715801
theorem B7091135 : Blo 1865634 7091135 := bstep (se 1 (by rfl) ⟨5318351, by rfl⟩ : syracuseStep 7091135 = 10636703) B10636703
theorem B3363833 : Blo 1865634 3363833 := bstep (se 2 (by rfl) ⟨1261437, by rfl⟩ : syracuseStep 3363833 = 2522875) B2522875
theorem B4199615 : Blo 1865634 4199615 := bstep (se 1 (by rfl) ⟨3149711, by rfl⟩ : syracuseStep 4199615 = 6299423) B6299423
theorem B4724203 : Blo 1865634 4724203 := bstep (se 1 (by rfl) ⟨3543152, by rfl⟩ : syracuseStep 4724203 = 7086305) B7086305
theorem B2799209 : Blo 1865634 2799209 := bstep (se 2 (by rfl) ⟨1049703, by rfl⟩ : syracuseStep 2799209 = 2099407) B2099407
theorem B1865639 : Blo 1865634 1865639 := bstep (se 1 (by rfl) ⟨1399229, by rfl⟩ : syracuseStep 1865639 = 2798459) B2798459
theorem B1865727 : Blo 1865634 1865727 := bstep (se 1 (by rfl) ⟨1399295, by rfl⟩ : syracuseStep 1865727 = 2798591) B2798591
theorem B2799647 : Blo 1865634 2799647 := bstep (se 1 (by rfl) ⟨2099735, by rfl⟩ : syracuseStep 2799647 = 4199471) B4199471
theorem B1865831 : Blo 1865634 1865831 := bstep (se 1 (by rfl) ⟨1399373, by rfl⟩ : syracuseStep 1865831 = 2798747) B2798747
theorem B1865839 : Blo 1865634 1865839 := bstep (se 1 (by rfl) ⟨1399379, by rfl⟩ : syracuseStep 1865839 = 2798759) B2798759
theorem B1865935 : Blo 1865634 1865935 := bstep (se 1 (by rfl) ⟨1399451, by rfl⟩ : syracuseStep 1865935 = 2798903) B2798903
theorem B9451727 : Blo 1865634 9451727 := bstep (se 1 (by rfl) ⟨7088795, by rfl⟩ : syracuseStep 9451727 = 14177591) B14177591
theorem B1865951 : Blo 1865634 1865951 := bstep (se 1 (by rfl) ⟨1399463, by rfl⟩ : syracuseStep 1865951 = 2798927) B2798927
theorem B4200731 : Blo 1865634 4200731 := bstep (se 1 (by rfl) ⟨3150548, by rfl⟩ : syracuseStep 4200731 = 6301097) B6301097
theorem B5314855 : Blo 1865634 5314855 := bstep (se 1 (by rfl) ⟨3986141, by rfl⟩ : syracuseStep 5314855 = 7972283) B7972283
theorem B47855933 : Blo 1865634 47855933 := bstep (se 3 (by rfl) ⟨8972987, by rfl⟩ : syracuseStep 47855933 = 17945975) B17945975
theorem B1866407 : Blo 1865634 1866407 := bstep (se 1 (by rfl) ⟨1399805, by rfl⟩ : syracuseStep 1866407 = 2799611) B2799611
theorem B1866491 : Blo 1865634 1866491 := bstep (se 1 (by rfl) ⟨1399868, by rfl⟩ : syracuseStep 1866491 = 2799737) B2799737
theorem B1866527 : Blo 1865634 1866527 := bstep (se 1 (by rfl) ⟨1399895, by rfl⟩ : syracuseStep 1866527 = 2799791) B2799791
theorem B4725641 : Blo 1865634 4725641 := bstep (se 2 (by rfl) ⟨1772115, by rfl⟩ : syracuseStep 4725641 = 3544231) B3544231
theorem B2800583 : Blo 1865634 2800583 := bstep (se 1 (by rfl) ⟨2100437, by rfl⟩ : syracuseStep 2800583 = 4200875) B4200875
theorem B2243551 : Blo 1865634 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B1866815 : Blo 1865634 1866815 := bstep (se 1 (by rfl) ⟨1400111, by rfl⟩ : syracuseStep 1866815 = 2800223) B2800223
theorem B1866863 : Blo 1865634 1866863 := bstep (se 1 (by rfl) ⟨1400147, by rfl⟩ : syracuseStep 1866863 = 2800295) B2800295
theorem B9452699 : Blo 1865634 9452699 := bstep (se 1 (by rfl) ⟨7089524, by rfl⟩ : syracuseStep 9452699 = 14179049) B14179049
theorem B1867035 : Blo 1865634 1867035 := bstep (se 1 (by rfl) ⟨1400276, by rfl⟩ : syracuseStep 1867035 = 2800553) B2800553
theorem B4201811 : Blo 1865634 4201811 := bstep (se 1 (by rfl) ⟨3151358, by rfl⟩ : syracuseStep 4201811 = 6302717) B6302717
theorem B1867135 : Blo 1865634 1867135 := bstep (se 1 (by rfl) ⟨1400351, by rfl⟩ : syracuseStep 1867135 = 2800703) B2800703
theorem B153222587 : Blo 1865634 153222587 := bstep (se 1 (by rfl) ⟨114916940, by rfl⟩ : syracuseStep 153222587 = 229833881) B229833881
theorem B2801129 : Blo 1865634 2801129 := bstep (se 2 (by rfl) ⟨1050423, by rfl⟩ : syracuseStep 2801129 = 2100847) B2100847
theorem B76652027 : Blo 1865634 76652027 := bstep (se 1 (by rfl) ⟨57489020, by rfl⟩ : syracuseStep 76652027 = 114978041) B114978041
theorem B6299261 : Blo 1865634 6299261 := bstep (se 3 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 6299261 = 2362223) B2362223
theorem B2801279 : Blo 1865634 2801279 := bstep (se 1 (by rfl) ⟨2100959, by rfl⟩ : syracuseStep 2801279 = 4201919) B4201919
theorem B9453185 : Blo 1865634 9453185 := bstep (se 2 (by rfl) ⟨3544944, by rfl⟩ : syracuseStep 9453185 = 7089889) B7089889
theorem B1867455 : Blo 1865634 1867455 := bstep (se 1 (by rfl) ⟨1400591, by rfl⟩ : syracuseStep 1867455 = 2801183) B2801183
theorem B17497853 : Blo 1865634 17497853 := bstep (se 3 (by rfl) ⟨3280847, by rfl⟩ : syracuseStep 17497853 = 6561695) B6561695
theorem B2990171 : Blo 1865634 2990171 := bstep (se 1 (by rfl) ⟨2242628, by rfl⟩ : syracuseStep 2990171 = 4485257) B4485257
theorem B5677247 : Blo 1865634 5677247 := bstep (se 1 (by rfl) ⟨4257935, by rfl⟩ : syracuseStep 5677247 = 8515871) B8515871
theorem B7086473 : Blo 1865634 7086473 := bstep (se 2 (by rfl) ⟨2657427, by rfl⟩ : syracuseStep 7086473 = 5314855) B5314855
theorem B4727423 : Blo 1865634 4727423 := bstep (se 1 (by rfl) ⟨3545567, by rfl⟩ : syracuseStep 4727423 = 7091135) B7091135
theorem B10093211 : Blo 1865634 10093211 := bstep (se 1 (by rfl) ⟨7569908, by rfl⟩ : syracuseStep 10093211 = 15139817) B15139817
theorem B11502323 : Blo 1865634 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B2991401 : Blo 1865634 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B6301151 : Blo 1865634 6301151 := bstep (se 1 (by rfl) ⟨4725863, by rfl⟩ : syracuseStep 6301151 = 9451727) B9451727
theorem B2393647 : Blo 1865634 2393647 := bstep (se 1 (by rfl) ⟨1795235, by rfl⟩ : syracuseStep 2393647 = 3590471) B3590471
theorem B6301799 : Blo 1865634 6301799 := bstep (se 1 (by rfl) ⟨4726349, by rfl⟩ : syracuseStep 6301799 = 9452699) B9452699
theorem B102148391 : Blo 1865634 102148391 := bstep (se 1 (by rfl) ⟨76611293, by rfl⟩ : syracuseStep 102148391 = 153222587) B153222587
theorem B6302123 : Blo 1865634 6302123 := bstep (se 1 (by rfl) ⟨4726592, by rfl⟩ : syracuseStep 6302123 = 9453185) B9453185
theorem B23923457 : Blo 1865634 23923457 := bstep (se 2 (by rfl) ⟨8971296, by rfl⟩ : syracuseStep 23923457 = 17942593) B17942593
theorem B6302555 : Blo 1865634 6302555 := bstep (se 1 (by rfl) ⟨4726916, by rfl⟩ : syracuseStep 6302555 = 9453833) B9453833
theorem B76639223 : Blo 1865634 76639223 := bstep (se 1 (by rfl) ⟨57479417, by rfl⟩ : syracuseStep 76639223 = 114958835) B114958835
theorem B10095911 : Blo 1865634 10095911 := bstep (se 1 (by rfl) ⟨7571933, by rfl⟩ : syracuseStep 10095911 = 15143867) B15143867
theorem B10088039 : Blo 1865634 10088039 := bstep (se 1 (by rfl) ⟨7566029, by rfl⟩ : syracuseStep 10088039 = 15132059) B15132059
theorem B10088387 : Blo 1865634 10088387 := bstep (se 1 (by rfl) ⟨7566290, by rfl⟩ : syracuseStep 10088387 = 15132581) B15132581
theorem B31903955 : Blo 1865634 31903955 := bstep (se 1 (by rfl) ⟨23927966, by rfl⟩ : syracuseStep 31903955 = 47855933) B47855933
theorem B21270761 : Blo 1865634 21270761 := bstep (se 2 (by rfl) ⟨7976535, by rfl⟩ : syracuseStep 21270761 = 15953071) B15953071
theorem B3150427 : Blo 1865634 3150427 := bstep (se 1 (by rfl) ⟨2362820, by rfl⟩ : syracuseStep 3150427 = 4725641) B4725641
theorem B7090847 : Blo 1865634 7090847 := bstep (se 1 (by rfl) ⟨5318135, by rfl⟩ : syracuseStep 7090847 = 10636271) B10636271
theorem B4199507 : Blo 1865634 4199507 := bstep (se 1 (by rfl) ⟨3149630, by rfl⟩ : syracuseStep 4199507 = 6299261) B6299261
theorem B4724041 : Blo 1865634 4724041 := bstep (se 2 (by rfl) ⟨1771515, by rfl⟩ : syracuseStep 4724041 = 3543031) B3543031
theorem B2799335 : Blo 1865634 2799335 := bstep (se 1 (by rfl) ⟨2099501, by rfl⟩ : syracuseStep 2799335 = 4199003) B4199003
theorem B23910335 : Blo 1865634 23910335 := bstep (se 1 (by rfl) ⟨17932751, by rfl⟩ : syracuseStep 23910335 = 35865503) B35865503
theorem B2242555 : Blo 1865634 2242555 := bstep (se 1 (by rfl) ⟨1681916, by rfl⟩ : syracuseStep 2242555 = 3363833) B3363833
theorem B2799743 : Blo 1865634 2799743 := bstep (se 1 (by rfl) ⟨2099807, by rfl⟩ : syracuseStep 2799743 = 4199615) B4199615
theorem B1866139 : Blo 1865634 1866139 := bstep (se 1 (by rfl) ⟨1399604, by rfl⟩ : syracuseStep 1866139 = 2799209) B2799209
theorem B5315071 : Blo 1865634 5315071 := bstep (se 1 (by rfl) ⟨3986303, by rfl⟩ : syracuseStep 5315071 = 7972607) B7972607
theorem B1866431 : Blo 1865634 1866431 := bstep (se 1 (by rfl) ⟨1399823, by rfl⟩ : syracuseStep 1866431 = 2799647) B2799647
theorem B7084847 : Blo 1865634 7084847 := bstep (se 1 (by rfl) ⟨5313635, by rfl⟩ : syracuseStep 7084847 = 10627271) B10627271
theorem B2800487 : Blo 1865634 2800487 := bstep (se 1 (by rfl) ⟨2100365, by rfl⟩ : syracuseStep 2800487 = 4200731) B4200731
theorem B7085015 : Blo 1865634 7085015 := bstep (se 1 (by rfl) ⟨5313761, by rfl⟩ : syracuseStep 7085015 = 10627523) B10627523
theorem B6724667 : Blo 1865634 6724667 := bstep (se 1 (by rfl) ⟨5043500, by rfl⟩ : syracuseStep 6724667 = 10087001) B10087001
theorem B1867055 : Blo 1865634 1867055 := bstep (se 1 (by rfl) ⟨1400291, by rfl⟩ : syracuseStep 1867055 = 2800583) B2800583
theorem B6298937 : Blo 1865634 6298937 := bstep (se 2 (by rfl) ⟨2362101, by rfl⟩ : syracuseStep 6298937 = 4724203) B4724203
theorem B21257639 : Blo 1865634 21257639 := bstep (se 1 (by rfl) ⟨15943229, by rfl⟩ : syracuseStep 21257639 = 31886459) B31886459
theorem B2801207 : Blo 1865634 2801207 := bstep (se 1 (by rfl) ⟨2100905, by rfl⟩ : syracuseStep 2801207 = 4201811) B4201811
theorem B1867419 : Blo 1865634 1867419 := bstep (se 1 (by rfl) ⟨1400564, by rfl⟩ : syracuseStep 1867419 = 2801129) B2801129
theorem B51101351 : Blo 1865634 51101351 := bstep (se 1 (by rfl) ⟨38326013, by rfl⟩ : syracuseStep 51101351 = 76652027) B76652027
theorem B1867519 : Blo 1865634 1867519 := bstep (se 1 (by rfl) ⟨1400639, by rfl⟩ : syracuseStep 1867519 = 2801279) B2801279
theorem B11665235 : Blo 1865634 11665235 := bstep (se 1 (by rfl) ⟨8748926, by rfl⟩ : syracuseStep 11665235 = 17497853) B17497853
theorem B14180507 : Blo 1865634 14180507 := bstep (se 1 (by rfl) ⟨10635380, by rfl⟩ : syracuseStep 14180507 = 21270761) B21270761
theorem B4727231 : Blo 1865634 4727231 := bstep (se 1 (by rfl) ⟨3545423, by rfl⟩ : syracuseStep 4727231 = 7090847) B7090847
theorem B7668215 : Blo 1865634 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B15139325 : Blo 1865634 15139325 := bstep (se 3 (by rfl) ⟨2838623, by rfl⟩ : syracuseStep 15139325 = 5677247) B5677247
theorem B7086761 : Blo 1865634 7086761 := bstep (se 2 (by rfl) ⟨2657535, by rfl⟩ : syracuseStep 7086761 = 5315071) B5315071
theorem B4483111 : Blo 1865634 4483111 := bstep (se 1 (by rfl) ⟨3362333, by rfl⟩ : syracuseStep 4483111 = 6724667) B6724667
theorem B7776823 : Blo 1865634 7776823 := bstep (se 1 (by rfl) ⟨5832617, by rfl⟩ : syracuseStep 7776823 = 11665235) B11665235
theorem B1993447 : Blo 1865634 1993447 := bstep (se 1 (by rfl) ⟨1495085, by rfl⟩ : syracuseStep 1993447 = 2990171) B2990171
theorem B21269303 : Blo 1865634 21269303 := bstep (se 1 (by rfl) ⟨15951977, by rfl⟩ : syracuseStep 21269303 = 31903955) B31903955
theorem B6728807 : Blo 1865634 6728807 := bstep (se 1 (by rfl) ⟨5046605, by rfl⟩ : syracuseStep 6728807 = 10093211) B10093211
theorem B1994267 : Blo 1865634 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B51064469 : Blo 1865634 51064469 := bstep (se 6 (by rfl) ⟨1196823, by rfl⟩ : syracuseStep 51064469 = 2393647) B2393647
theorem B4723231 : Blo 1865634 4723231 := bstep (se 1 (by rfl) ⟨3542423, by rfl⟩ : syracuseStep 4723231 = 7084847) B7084847
theorem B4723343 : Blo 1865634 4723343 := bstep (se 1 (by rfl) ⟨3542507, by rfl⟩ : syracuseStep 4723343 = 7085015) B7085015
theorem B6730607 : Blo 1865634 6730607 := bstep (se 1 (by rfl) ⟨5047955, by rfl⟩ : syracuseStep 6730607 = 10095911) B10095911
theorem B4199291 : Blo 1865634 4199291 := bstep (se 1 (by rfl) ⟨3149468, by rfl⟩ : syracuseStep 4199291 = 6298937) B6298937
theorem B34067567 : Blo 1865634 34067567 := bstep (se 1 (by rfl) ⟨25550675, by rfl⟩ : syracuseStep 34067567 = 51101351) B51101351
theorem B4724315 : Blo 1865634 4724315 := bstep (se 1 (by rfl) ⟨3543236, by rfl⟩ : syracuseStep 4724315 = 7086473) B7086473
theorem B3151615 : Blo 1865634 3151615 := bstep (se 1 (by rfl) ⟨2363711, by rfl⟩ : syracuseStep 3151615 = 4727423) B4727423
theorem B2799671 : Blo 1865634 2799671 := bstep (se 1 (by rfl) ⟨2099753, by rfl⟩ : syracuseStep 2799671 = 4199507) B4199507
theorem B4200569 : Blo 1865634 4200569 := bstep (se 2 (by rfl) ⟨1575213, by rfl⟩ : syracuseStep 4200569 = 3150427) B3150427
theorem B4200767 : Blo 1865634 4200767 := bstep (se 1 (by rfl) ⟨3150575, by rfl⟩ : syracuseStep 4200767 = 6301151) B6301151
theorem B1866223 : Blo 1865634 1866223 := bstep (se 1 (by rfl) ⟨1399667, by rfl⟩ : syracuseStep 1866223 = 2799335) B2799335
theorem B15940223 : Blo 1865634 15940223 := bstep (se 1 (by rfl) ⟨11955167, by rfl⟩ : syracuseStep 15940223 = 23910335) B23910335
theorem B4201199 : Blo 1865634 4201199 := bstep (se 1 (by rfl) ⟨3150899, by rfl⟩ : syracuseStep 4201199 = 6301799) B6301799
theorem B1866495 : Blo 1865634 1866495 := bstep (se 1 (by rfl) ⟨1399871, by rfl⟩ : syracuseStep 1866495 = 2799743) B2799743
theorem B68098927 : Blo 1865634 68098927 := bstep (se 1 (by rfl) ⟨51074195, by rfl⟩ : syracuseStep 68098927 = 102148391) B102148391
theorem B4201415 : Blo 1865634 4201415 := bstep (se 1 (by rfl) ⟨3151061, by rfl⟩ : syracuseStep 4201415 = 6302123) B6302123
theorem B6298721 : Blo 1865634 6298721 := bstep (se 2 (by rfl) ⟨2362020, by rfl⟩ : syracuseStep 6298721 = 4724041) B4724041
theorem B15948971 : Blo 1865634 15948971 := bstep (se 1 (by rfl) ⟨11961728, by rfl⟩ : syracuseStep 15948971 = 23923457) B23923457
theorem B4201703 : Blo 1865634 4201703 := bstep (se 1 (by rfl) ⟨3151277, by rfl⟩ : syracuseStep 4201703 = 6302555) B6302555
theorem B1866991 : Blo 1865634 1866991 := bstep (se 1 (by rfl) ⟨1400243, by rfl⟩ : syracuseStep 1866991 = 2800487) B2800487
theorem B51092815 : Blo 1865634 51092815 := bstep (se 1 (by rfl) ⟨38319611, by rfl⟩ : syracuseStep 51092815 = 76639223) B76639223
theorem B14171759 : Blo 1865634 14171759 := bstep (se 1 (by rfl) ⟨10628819, by rfl⟩ : syracuseStep 14171759 = 21257639) B21257639
theorem B1867471 : Blo 1865634 1867471 := bstep (se 1 (by rfl) ⟨1400603, by rfl⟩ : syracuseStep 1867471 = 2801207) B2801207
theorem B6725359 : Blo 1865634 6725359 := bstep (se 1 (by rfl) ⟨5044019, by rfl⟩ : syracuseStep 6725359 = 10088039) B10088039
theorem B6725591 : Blo 1865634 6725591 := bstep (se 1 (by rfl) ⟨5044193, by rfl⟩ : syracuseStep 6725591 = 10088387) B10088387
theorem B11960293 : Blo 1865634 11960293 := bstep (se 4 (by rfl) ⟨1121277, by rfl⟩ : syracuseStep 11960293 = 2242555) B2242555
theorem B9453671 : Blo 1865634 9453671 := bstep (se 1 (by rfl) ⟨7090253, by rfl⟩ : syracuseStep 9453671 = 14180507) B14180507
theorem B5112143 : Blo 1865634 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B10092883 : Blo 1865634 10092883 := bstep (se 1 (by rfl) ⟨7569662, by rfl⟩ : syracuseStep 10092883 = 15139325) B15139325
theorem B5318045 : Blo 1865634 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B10626815 : Blo 1865634 10626815 := bstep (se 1 (by rfl) ⟨7970111, by rfl⟩ : syracuseStep 10626815 = 15940223) B15940223
theorem B9447839 : Blo 1865634 9447839 := bstep (se 1 (by rfl) ⟨7085879, by rfl⟩ : syracuseStep 9447839 = 14171759) B14171759
theorem B4483727 : Blo 1865634 4483727 := bstep (se 1 (by rfl) ⟨3362795, by rfl⟩ : syracuseStep 4483727 = 6725591) B6725591
theorem B3148895 : Blo 1865634 3148895 := bstep (se 1 (by rfl) ⟨2361671, by rfl⟩ : syracuseStep 3148895 = 4723343) B4723343
theorem B22711711 : Blo 1865634 22711711 := bstep (se 1 (by rfl) ⟨17033783, by rfl⟩ : syracuseStep 22711711 = 34067567) B34067567
theorem B2657929 : Blo 1865634 2657929 := bstep (se 2 (by rfl) ⟨996723, by rfl⟩ : syracuseStep 2657929 = 1993447) B1993447
theorem B3149543 : Blo 1865634 3149543 := bstep (se 1 (by rfl) ⟨2362157, by rfl⟩ : syracuseStep 3149543 = 4724315) B4724315
theorem B4199147 : Blo 1865634 4199147 := bstep (se 1 (by rfl) ⟨3149360, by rfl⟩ : syracuseStep 4199147 = 6298721) B6298721
theorem B4485871 : Blo 1865634 4485871 := bstep (se 1 (by rfl) ⟨3364403, by rfl⟩ : syracuseStep 4485871 = 6728807) B6728807
theorem B8967145 : Blo 1865634 8967145 := bstep (se 2 (by rfl) ⟨3362679, by rfl⟩ : syracuseStep 8967145 = 6725359) B6725359
theorem B34042979 : Blo 1865634 34042979 := bstep (se 1 (by rfl) ⟨25532234, by rfl⟩ : syracuseStep 34042979 = 51064469) B51064469
theorem B15947057 : Blo 1865634 15947057 := bstep (se 2 (by rfl) ⟨5980146, by rfl⟩ : syracuseStep 15947057 = 11960293) B11960293
theorem B5977481 : Blo 1865634 5977481 := bstep (se 2 (by rfl) ⟨2241555, by rfl⟩ : syracuseStep 5977481 = 4483111) B4483111
theorem B3151487 : Blo 1865634 3151487 := bstep (se 1 (by rfl) ⟨2363615, by rfl⟩ : syracuseStep 3151487 = 4727231) B4727231
theorem B4724507 : Blo 1865634 4724507 := bstep (se 1 (by rfl) ⟨3543380, by rfl⟩ : syracuseStep 4724507 = 7086761) B7086761
theorem B4487071 : Blo 1865634 4487071 := bstep (se 1 (by rfl) ⟨3365303, by rfl⟩ : syracuseStep 4487071 = 6730607) B6730607
theorem B2799527 : Blo 1865634 2799527 := bstep (se 1 (by rfl) ⟨2099645, by rfl⟩ : syracuseStep 2799527 = 4199291) B4199291
theorem B6297641 : Blo 1865634 6297641 := bstep (se 2 (by rfl) ⟨2361615, by rfl⟩ : syracuseStep 6297641 = 4723231) B4723231
theorem B10369097 : Blo 1865634 10369097 := bstep (se 2 (by rfl) ⟨3888411, by rfl⟩ : syracuseStep 10369097 = 7776823) B7776823
theorem B90798569 : Blo 1865634 90798569 := bstep (se 2 (by rfl) ⟨34049463, by rfl⟩ : syracuseStep 90798569 = 68098927) B68098927
theorem B1866447 : Blo 1865634 1866447 := bstep (se 1 (by rfl) ⟨1399835, by rfl⟩ : syracuseStep 1866447 = 2799671) B2799671
theorem B2800379 : Blo 1865634 2800379 := bstep (se 1 (by rfl) ⟨2100284, by rfl⟩ : syracuseStep 2800379 = 4200569) B4200569
theorem B2800511 : Blo 1865634 2800511 := bstep (se 1 (by rfl) ⟨2100383, by rfl⟩ : syracuseStep 2800511 = 4200767) B4200767
theorem B68123753 : Blo 1865634 68123753 := bstep (se 2 (by rfl) ⟨25546407, by rfl⟩ : syracuseStep 68123753 = 51092815) B51092815
theorem B2800799 : Blo 1865634 2800799 := bstep (se 1 (by rfl) ⟨2100599, by rfl⟩ : syracuseStep 2800799 = 4201199) B4201199
theorem B14179535 : Blo 1865634 14179535 := bstep (se 1 (by rfl) ⟨10634651, by rfl⟩ : syracuseStep 14179535 = 21269303) B21269303
theorem B2800943 : Blo 1865634 2800943 := bstep (se 1 (by rfl) ⟨2100707, by rfl⟩ : syracuseStep 2800943 = 4201415) B4201415
theorem B10632647 : Blo 1865634 10632647 := bstep (se 1 (by rfl) ⟨7974485, by rfl⟩ : syracuseStep 10632647 = 15948971) B15948971
theorem B2801135 : Blo 1865634 2801135 := bstep (se 1 (by rfl) ⟨2100851, by rfl⟩ : syracuseStep 2801135 = 4201703) B4201703
theorem B4202153 : Blo 1865634 4202153 := bstep (se 2 (by rfl) ⟨1575807, by rfl⟩ : syracuseStep 4202153 = 3151615) B3151615
theorem B3408095 : Blo 1865634 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B5981161 : Blo 1865634 5981161 := bstep (se 2 (by rfl) ⟨2242935, by rfl⟩ : syracuseStep 5981161 = 4485871) B4485871
theorem B60532379 : Blo 1865634 60532379 := bstep (se 1 (by rfl) ⟨45399284, by rfl⟩ : syracuseStep 60532379 = 90798569) B90798569
theorem B2099263 : Blo 1865634 2099263 := bstep (se 1 (by rfl) ⟨1574447, by rfl⟩ : syracuseStep 2099263 = 3148895) B3148895
theorem B7088431 : Blo 1865634 7088431 := bstep (se 1 (by rfl) ⟨5316323, by rfl⟩ : syracuseStep 7088431 = 10632647) B10632647
theorem B2099695 : Blo 1865634 2099695 := bstep (se 1 (by rfl) ⟨1574771, by rfl⟩ : syracuseStep 2099695 = 3149543) B3149543
theorem B5982761 : Blo 1865634 5982761 := bstep (se 2 (by rfl) ⟨2243535, by rfl⟩ : syracuseStep 5982761 = 4487071) B4487071
theorem B6302447 : Blo 1865634 6302447 := bstep (se 1 (by rfl) ⟨4726835, by rfl⟩ : syracuseStep 6302447 = 9453671) B9453671
theorem B22695319 : Blo 1865634 22695319 := bstep (se 1 (by rfl) ⟨17021489, by rfl⟩ : syracuseStep 22695319 = 34042979) B34042979
theorem B2100991 : Blo 1865634 2100991 := bstep (se 1 (by rfl) ⟨1575743, by rfl⟩ : syracuseStep 2100991 = 3151487) B3151487
theorem B3149671 : Blo 1865634 3149671 := bstep (se 1 (by rfl) ⟨2362253, by rfl⟩ : syracuseStep 3149671 = 4724507) B4724507
theorem B11956193 : Blo 1865634 11956193 := bstep (se 2 (by rfl) ⟨4483572, by rfl⟩ : syracuseStep 11956193 = 8967145) B8967145
theorem B4198427 : Blo 1865634 4198427 := bstep (se 1 (by rfl) ⟨3148820, by rfl⟩ : syracuseStep 4198427 = 6297641) B6297641
theorem B30282281 : Blo 1865634 30282281 := bstep (se 2 (by rfl) ⟨11355855, by rfl⟩ : syracuseStep 30282281 = 22711711) B22711711
theorem B3543905 : Blo 1865634 3543905 := bstep (se 2 (by rfl) ⟨1328964, by rfl⟩ : syracuseStep 3543905 = 2657929) B2657929
theorem B13457177 : Blo 1865634 13457177 := bstep (se 2 (by rfl) ⟨5046441, by rfl⟩ : syracuseStep 13457177 = 10092883) B10092883
theorem B2799431 : Blo 1865634 2799431 := bstep (se 1 (by rfl) ⟨2099573, by rfl⟩ : syracuseStep 2799431 = 4199147) B4199147
theorem B10631371 : Blo 1865634 10631371 := bstep (se 1 (by rfl) ⟨7973528, by rfl⟩ : syracuseStep 10631371 = 15947057) B15947057
theorem B3545363 : Blo 1865634 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B15939949 : Blo 1865634 15939949 := bstep (se 3 (by rfl) ⟨2988740, by rfl⟩ : syracuseStep 15939949 = 5977481) B5977481
theorem B7084543 : Blo 1865634 7084543 := bstep (se 1 (by rfl) ⟨5313407, by rfl⟩ : syracuseStep 7084543 = 10626815) B10626815
theorem B1866351 : Blo 1865634 1866351 := bstep (se 1 (by rfl) ⟨1399763, by rfl⟩ : syracuseStep 1866351 = 2799527) B2799527
theorem B6912731 : Blo 1865634 6912731 := bstep (se 1 (by rfl) ⟨5184548, by rfl⟩ : syracuseStep 6912731 = 10369097) B10369097
theorem B6298559 : Blo 1865634 6298559 := bstep (se 1 (by rfl) ⟨4723919, by rfl⟩ : syracuseStep 6298559 = 9447839) B9447839
theorem B2989151 : Blo 1865634 2989151 := bstep (se 1 (by rfl) ⟨2241863, by rfl⟩ : syracuseStep 2989151 = 4483727) B4483727
theorem B1866919 : Blo 1865634 1866919 := bstep (se 1 (by rfl) ⟨1400189, by rfl⟩ : syracuseStep 1866919 = 2800379) B2800379
theorem B1867007 : Blo 1865634 1867007 := bstep (se 1 (by rfl) ⟨1400255, by rfl⟩ : syracuseStep 1867007 = 2800511) B2800511
theorem B45415835 : Blo 1865634 45415835 := bstep (se 1 (by rfl) ⟨34061876, by rfl⟩ : syracuseStep 45415835 = 68123753) B68123753
theorem B1867199 : Blo 1865634 1867199 := bstep (se 1 (by rfl) ⟨1400399, by rfl⟩ : syracuseStep 1867199 = 2800799) B2800799
theorem B9453023 : Blo 1865634 9453023 := bstep (se 1 (by rfl) ⟨7089767, by rfl⟩ : syracuseStep 9453023 = 14179535) B14179535
theorem B1867295 : Blo 1865634 1867295 := bstep (se 1 (by rfl) ⟨1400471, by rfl⟩ : syracuseStep 1867295 = 2800943) B2800943
theorem B1867423 : Blo 1865634 1867423 := bstep (se 1 (by rfl) ⟨1400567, by rfl⟩ : syracuseStep 1867423 = 2801135) B2801135
theorem B2801435 : Blo 1865634 2801435 := bstep (se 1 (by rfl) ⟨2101076, by rfl⟩ : syracuseStep 2801435 = 4202153) B4202153
theorem B9446057 : Blo 1865634 9446057 := bstep (se 2 (by rfl) ⟨3542271, by rfl⟩ : syracuseStep 9446057 = 7084543) B7084543
theorem B40354919 : Blo 1865634 40354919 := bstep (se 1 (by rfl) ⟨30266189, by rfl⟩ : syracuseStep 40354919 = 60532379) B60532379
theorem B8971451 : Blo 1865634 8971451 := bstep (se 1 (by rfl) ⟨6728588, by rfl⟩ : syracuseStep 8971451 = 13457177) B13457177
theorem B1992767 : Blo 1865634 1992767 := bstep (se 1 (by rfl) ⟨1494575, by rfl⟩ : syracuseStep 1992767 = 2989151) B2989151
theorem B6302015 : Blo 1865634 6302015 := bstep (se 1 (by rfl) ⟨4726511, by rfl⟩ : syracuseStep 6302015 = 9453023) B9453023
theorem B2272063 : Blo 1865634 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B14175161 : Blo 1865634 14175161 := bstep (se 2 (by rfl) ⟨5315685, by rfl⟩ : syracuseStep 14175161 = 10631371) B10631371
theorem B20188187 : Blo 1865634 20188187 := bstep (se 1 (by rfl) ⟨15141140, by rfl⟩ : syracuseStep 20188187 = 30282281) B30282281
theorem B21253265 : Blo 1865634 21253265 := bstep (se 2 (by rfl) ⟨7969974, by rfl⟩ : syracuseStep 21253265 = 15939949) B15939949
theorem B2362603 : Blo 1865634 2362603 := bstep (se 1 (by rfl) ⟨1771952, by rfl⟩ : syracuseStep 2362603 = 3543905) B3543905
theorem B7974881 : Blo 1865634 7974881 := bstep (se 2 (by rfl) ⟨2990580, by rfl⟩ : syracuseStep 7974881 = 5981161) B5981161
theorem B15954029 : Blo 1865634 15954029 := bstep (se 3 (by rfl) ⟨2991380, by rfl⟩ : syracuseStep 15954029 = 5982761) B5982761
theorem B2363575 : Blo 1865634 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B4608487 : Blo 1865634 4608487 := bstep (se 1 (by rfl) ⟨3456365, by rfl⟩ : syracuseStep 4608487 = 6912731) B6912731
theorem B4199039 : Blo 1865634 4199039 := bstep (se 1 (by rfl) ⟨3149279, by rfl⟩ : syracuseStep 4199039 = 6298559) B6298559
theorem B4199561 : Blo 1865634 4199561 := bstep (se 2 (by rfl) ⟨1574835, by rfl⟩ : syracuseStep 4199561 = 3149671) B3149671
theorem B2798951 : Blo 1865634 2798951 := bstep (se 1 (by rfl) ⟨2099213, by rfl⟩ : syracuseStep 2798951 = 4198427) B4198427
theorem B2799017 : Blo 1865634 2799017 := bstep (se 2 (by rfl) ⟨1049631, by rfl⟩ : syracuseStep 2799017 = 2099263) B2099263
theorem B9451241 : Blo 1865634 9451241 := bstep (se 2 (by rfl) ⟨3544215, by rfl⟩ : syracuseStep 9451241 = 7088431) B7088431
theorem B2799593 : Blo 1865634 2799593 := bstep (se 2 (by rfl) ⟨1049847, by rfl⟩ : syracuseStep 2799593 = 2099695) B2099695
theorem B1866287 : Blo 1865634 1866287 := bstep (se 1 (by rfl) ⟨1399715, by rfl⟩ : syracuseStep 1866287 = 2799431) B2799431
theorem B4201631 : Blo 1865634 4201631 := bstep (se 1 (by rfl) ⟨3151223, by rfl⟩ : syracuseStep 4201631 = 6302447) B6302447
theorem B30260425 : Blo 1865634 30260425 := bstep (se 2 (by rfl) ⟨11347659, by rfl⟩ : syracuseStep 30260425 = 22695319) B22695319
theorem B30277223 : Blo 1865634 30277223 := bstep (se 1 (by rfl) ⟨22707917, by rfl⟩ : syracuseStep 30277223 = 45415835) B45415835
theorem B2801321 : Blo 1865634 2801321 := bstep (se 2 (by rfl) ⟨1050495, by rfl⟩ : syracuseStep 2801321 = 2100991) B2100991
theorem B1867623 : Blo 1865634 1867623 := bstep (se 1 (by rfl) ⟨1400717, by rfl⟩ : syracuseStep 1867623 = 2801435) B2801435
theorem B7970795 : Blo 1865634 7970795 := bstep (se 1 (by rfl) ⟨5978096, by rfl⟩ : syracuseStep 7970795 = 11956193) B11956193
theorem B6144649 : Blo 1865634 6144649 := bstep (se 2 (by rfl) ⟨2304243, by rfl⟩ : syracuseStep 6144649 = 4608487) B4608487
theorem B26903279 : Blo 1865634 26903279 := bstep (se 1 (by rfl) ⟨20177459, by rfl⟩ : syracuseStep 26903279 = 40354919) B40354919
theorem B5980967 : Blo 1865634 5980967 := bstep (se 1 (by rfl) ⟨4485725, by rfl⟩ : syracuseStep 5980967 = 8971451) B8971451
theorem B6300827 : Blo 1865634 6300827 := bstep (se 1 (by rfl) ⟨4725620, by rfl⟩ : syracuseStep 6300827 = 9451241) B9451241
theorem B40347233 : Blo 1865634 40347233 := bstep (se 2 (by rfl) ⟨15130212, by rfl⟩ : syracuseStep 40347233 = 30260425) B30260425
theorem B10636019 : Blo 1865634 10636019 := bstep (se 1 (by rfl) ⟨7977014, by rfl⟩ : syracuseStep 10636019 = 15954029) B15954029
theorem B3150137 : Blo 1865634 3150137 := bstep (se 2 (by rfl) ⟨1181301, by rfl⟩ : syracuseStep 3150137 = 2362603) B2362603
theorem B9450107 : Blo 1865634 9450107 := bstep (se 1 (by rfl) ⟨7087580, by rfl⟩ : syracuseStep 9450107 = 14175161) B14175161
theorem B14168843 : Blo 1865634 14168843 := bstep (se 1 (by rfl) ⟨10626632, by rfl⟩ : syracuseStep 14168843 = 21253265) B21253265
theorem B5313863 : Blo 1865634 5313863 := bstep (se 1 (by rfl) ⟨3985397, by rfl⟩ : syracuseStep 5313863 = 7970795) B7970795
theorem B3151433 : Blo 1865634 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B2799359 : Blo 1865634 2799359 := bstep (se 1 (by rfl) ⟨2099519, by rfl⟩ : syracuseStep 2799359 = 4199039) B4199039
theorem B6297371 : Blo 1865634 6297371 := bstep (se 1 (by rfl) ⟨4723028, by rfl⟩ : syracuseStep 6297371 = 9446057) B9446057
theorem B21256181 : Blo 1865634 21256181 := bstep (se 5 (by rfl) ⟨996383, by rfl⟩ : syracuseStep 21256181 = 1992767) B1992767
theorem B2799707 : Blo 1865634 2799707 := bstep (se 1 (by rfl) ⟨2099780, by rfl⟩ : syracuseStep 2799707 = 4199561) B4199561
theorem B1865967 : Blo 1865634 1865967 := bstep (se 1 (by rfl) ⟨1399475, by rfl⟩ : syracuseStep 1865967 = 2798951) B2798951
theorem B1866011 : Blo 1865634 1866011 := bstep (se 1 (by rfl) ⟨1399508, by rfl⟩ : syracuseStep 1866011 = 2799017) B2799017
theorem B3029417 : Blo 1865634 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B1866395 : Blo 1865634 1866395 := bstep (se 1 (by rfl) ⟨1399796, by rfl⟩ : syracuseStep 1866395 = 2799593) B2799593
theorem B4201343 : Blo 1865634 4201343 := bstep (se 1 (by rfl) ⟨3151007, by rfl⟩ : syracuseStep 4201343 = 6302015) B6302015
theorem B13458791 : Blo 1865634 13458791 := bstep (se 1 (by rfl) ⟨10094093, by rfl⟩ : syracuseStep 13458791 = 20188187) B20188187
theorem B2801087 : Blo 1865634 2801087 := bstep (se 1 (by rfl) ⟨2100815, by rfl⟩ : syracuseStep 2801087 = 4201631) B4201631
theorem B20184815 : Blo 1865634 20184815 := bstep (se 1 (by rfl) ⟨15138611, by rfl⟩ : syracuseStep 20184815 = 30277223) B30277223
theorem B1867547 : Blo 1865634 1867547 := bstep (se 1 (by rfl) ⟨1400660, by rfl⟩ : syracuseStep 1867547 = 2801321) B2801321
theorem B5316587 : Blo 1865634 5316587 := bstep (se 1 (by rfl) ⟨3987440, by rfl⟩ : syracuseStep 5316587 = 7974881) B7974881
theorem B6300071 : Blo 1865634 6300071 := bstep (se 1 (by rfl) ⟨4725053, by rfl⟩ : syracuseStep 6300071 = 9450107) B9450107
theorem B9445895 : Blo 1865634 9445895 := bstep (se 1 (by rfl) ⟨7084421, by rfl⟩ : syracuseStep 9445895 = 14168843) B14168843
theorem B8972527 : Blo 1865634 8972527 := bstep (se 1 (by rfl) ⟨6729395, by rfl⟩ : syracuseStep 8972527 = 13458791) B13458791
theorem B2100091 : Blo 1865634 2100091 := bstep (se 1 (by rfl) ⟨1575068, by rfl⟩ : syracuseStep 2100091 = 3150137) B3150137
theorem B17935519 : Blo 1865634 17935519 := bstep (se 1 (by rfl) ⟨13451639, by rfl⟩ : syracuseStep 17935519 = 26903279) B26903279
theorem B32771461 : Blo 1865634 32771461 := bstep (se 4 (by rfl) ⟨3072324, by rfl⟩ : syracuseStep 32771461 = 6144649) B6144649
theorem B2100955 : Blo 1865634 2100955 := bstep (se 1 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 2100955 = 3151433) B3151433
theorem B26898155 : Blo 1865634 26898155 := bstep (se 1 (by rfl) ⟨20173616, by rfl⟩ : syracuseStep 26898155 = 40347233) B40347233
theorem B4198247 : Blo 1865634 4198247 := bstep (se 1 (by rfl) ⟨3148685, by rfl⟩ : syracuseStep 4198247 = 6297371) B6297371
theorem B2019611 : Blo 1865634 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B7090679 : Blo 1865634 7090679 := bstep (se 1 (by rfl) ⟨5318009, by rfl⟩ : syracuseStep 7090679 = 10636019) B10636019
theorem B13456543 : Blo 1865634 13456543 := bstep (se 1 (by rfl) ⟨10092407, by rfl⟩ : syracuseStep 13456543 = 20184815) B20184815
theorem B3544391 : Blo 1865634 3544391 := bstep (se 1 (by rfl) ⟨2658293, by rfl⟩ : syracuseStep 3544391 = 5316587) B5316587
theorem B3987311 : Blo 1865634 3987311 := bstep (se 1 (by rfl) ⟨2990483, by rfl⟩ : syracuseStep 3987311 = 5980967) B5980967
theorem B4200551 : Blo 1865634 4200551 := bstep (se 1 (by rfl) ⟨3150413, by rfl⟩ : syracuseStep 4200551 = 6300827) B6300827
theorem B14170301 : Blo 1865634 14170301 := bstep (se 3 (by rfl) ⟨2656931, by rfl⟩ : syracuseStep 14170301 = 5313863) B5313863
theorem B1866239 : Blo 1865634 1866239 := bstep (se 1 (by rfl) ⟨1399679, by rfl⟩ : syracuseStep 1866239 = 2799359) B2799359
theorem B14170787 : Blo 1865634 14170787 := bstep (se 1 (by rfl) ⟨10628090, by rfl⟩ : syracuseStep 14170787 = 21256181) B21256181
theorem B1866471 : Blo 1865634 1866471 := bstep (se 1 (by rfl) ⟨1399853, by rfl⟩ : syracuseStep 1866471 = 2799707) B2799707
theorem B2800895 : Blo 1865634 2800895 := bstep (se 1 (by rfl) ⟨2100671, by rfl⟩ : syracuseStep 2800895 = 4201343) B4201343
theorem B1867391 : Blo 1865634 1867391 := bstep (se 1 (by rfl) ⟨1400543, by rfl⟩ : syracuseStep 1867391 = 2801087) B2801087
theorem B4727119 : Blo 1865634 4727119 := bstep (se 1 (by rfl) ⟨3545339, by rfl⟩ : syracuseStep 4727119 = 7090679) B7090679
theorem B9446867 : Blo 1865634 9446867 := bstep (se 1 (by rfl) ⟨7085150, by rfl⟩ : syracuseStep 9446867 = 14170301) B14170301
theorem B23914025 : Blo 1865634 23914025 := bstep (se 2 (by rfl) ⟨8967759, by rfl⟩ : syracuseStep 23914025 = 17935519) B17935519
theorem B17942057 : Blo 1865634 17942057 := bstep (se 2 (by rfl) ⟨6728271, by rfl⟩ : syracuseStep 17942057 = 13456543) B13456543
theorem B9447191 : Blo 1865634 9447191 := bstep (se 1 (by rfl) ⟨7085393, by rfl⟩ : syracuseStep 9447191 = 14170787) B14170787
theorem B11963369 : Blo 1865634 11963369 := bstep (se 2 (by rfl) ⟨4486263, by rfl⟩ : syracuseStep 11963369 = 8972527) B8972527
theorem B5385629 : Blo 1865634 5385629 := bstep (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) B2019611
theorem B2362927 : Blo 1865634 2362927 := bstep (se 1 (by rfl) ⟨1772195, by rfl⟩ : syracuseStep 2362927 = 3544391) B3544391
theorem B2798831 : Blo 1865634 2798831 := bstep (se 1 (by rfl) ⟨2099123, by rfl⟩ : syracuseStep 2798831 = 4198247) B4198247
theorem B4200047 : Blo 1865634 4200047 := bstep (se 1 (by rfl) ⟨3150035, by rfl⟩ : syracuseStep 4200047 = 6300071) B6300071
theorem B6297263 : Blo 1865634 6297263 := bstep (se 1 (by rfl) ⟨4722947, by rfl⟩ : syracuseStep 6297263 = 9445895) B9445895
theorem B2800121 : Blo 1865634 2800121 := bstep (se 2 (by rfl) ⟨1050045, by rfl⟩ : syracuseStep 2800121 = 2100091) B2100091
theorem B2800367 : Blo 1865634 2800367 := bstep (se 1 (by rfl) ⟨2100275, by rfl⟩ : syracuseStep 2800367 = 4200551) B4200551
theorem B43695281 : Blo 1865634 43695281 := bstep (se 2 (by rfl) ⟨16385730, by rfl⟩ : syracuseStep 43695281 = 32771461) B32771461
theorem B1867263 : Blo 1865634 1867263 := bstep (se 1 (by rfl) ⟨1400447, by rfl⟩ : syracuseStep 1867263 = 2800895) B2800895
theorem B2801273 : Blo 1865634 2801273 := bstep (se 2 (by rfl) ⟨1050477, by rfl⟩ : syracuseStep 2801273 = 2100955) B2100955
theorem B10632829 : Blo 1865634 10632829 := bstep (se 3 (by rfl) ⟨1993655, by rfl⟩ : syracuseStep 10632829 = 3987311) B3987311
theorem B17932103 : Blo 1865634 17932103 := bstep (se 1 (by rfl) ⟨13449077, by rfl⟩ : syracuseStep 17932103 = 26898155) B26898155
theorem B15942683 : Blo 1865634 15942683 := bstep (se 1 (by rfl) ⟨11957012, by rfl⟩ : syracuseStep 15942683 = 23914025) B23914025
theorem B11961371 : Blo 1865634 11961371 := bstep (se 1 (by rfl) ⟨8971028, by rfl⟩ : syracuseStep 11961371 = 17942057) B17942057
theorem B3590419 : Blo 1865634 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B11954735 : Blo 1865634 11954735 := bstep (se 1 (by rfl) ⟨8966051, by rfl⟩ : syracuseStep 11954735 = 17932103) B17932103
theorem B6302825 : Blo 1865634 6302825 := bstep (se 2 (by rfl) ⟨2363559, by rfl⟩ : syracuseStep 6302825 = 4727119) B4727119
theorem B4198175 : Blo 1865634 4198175 := bstep (se 1 (by rfl) ⟨3148631, by rfl⟩ : syracuseStep 4198175 = 6297263) B6297263
theorem B7975579 : Blo 1865634 7975579 := bstep (se 1 (by rfl) ⟨5981684, by rfl⟩ : syracuseStep 7975579 = 11963369) B11963369
theorem B3150569 : Blo 1865634 3150569 := bstep (se 2 (by rfl) ⟨1181463, by rfl⟩ : syracuseStep 3150569 = 2362927) B2362927
theorem B14177105 : Blo 1865634 14177105 := bstep (se 2 (by rfl) ⟨5316414, by rfl⟩ : syracuseStep 14177105 = 10632829) B10632829
theorem B1865887 : Blo 1865634 1865887 := bstep (se 1 (by rfl) ⟨1399415, by rfl⟩ : syracuseStep 1865887 = 2798831) B2798831
theorem B6297911 : Blo 1865634 6297911 := bstep (se 1 (by rfl) ⟨4723433, by rfl⟩ : syracuseStep 6297911 = 9446867) B9446867
theorem B2800031 : Blo 1865634 2800031 := bstep (se 1 (by rfl) ⟨2100023, by rfl⟩ : syracuseStep 2800031 = 4200047) B4200047
theorem B6298127 : Blo 1865634 6298127 := bstep (se 1 (by rfl) ⟨4723595, by rfl⟩ : syracuseStep 6298127 = 9447191) B9447191
theorem B1866747 : Blo 1865634 1866747 := bstep (se 1 (by rfl) ⟨1400060, by rfl⟩ : syracuseStep 1866747 = 2800121) B2800121
theorem B1866911 : Blo 1865634 1866911 := bstep (se 1 (by rfl) ⟨1400183, by rfl⟩ : syracuseStep 1866911 = 2800367) B2800367
theorem B29130187 : Blo 1865634 29130187 := bstep (se 1 (by rfl) ⟨21847640, by rfl⟩ : syracuseStep 29130187 = 43695281) B43695281
theorem B1867515 : Blo 1865634 1867515 := bstep (se 1 (by rfl) ⟨1400636, by rfl⟩ : syracuseStep 1867515 = 2801273) B2801273
theorem B10634105 : Blo 1865634 10634105 := bstep (se 2 (by rfl) ⟨3987789, by rfl⟩ : syracuseStep 10634105 = 7975579) B7975579
theorem B38840249 : Blo 1865634 38840249 := bstep (se 2 (by rfl) ⟨14565093, by rfl⟩ : syracuseStep 38840249 = 29130187) B29130187
theorem B4787225 : Blo 1865634 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B2100379 : Blo 1865634 2100379 := bstep (se 1 (by rfl) ⟨1575284, by rfl⟩ : syracuseStep 2100379 = 3150569) B3150569
theorem B10628455 : Blo 1865634 10628455 := bstep (se 1 (by rfl) ⟨7971341, by rfl⟩ : syracuseStep 10628455 = 15942683) B15942683
theorem B7974247 : Blo 1865634 7974247 := bstep (se 1 (by rfl) ⟨5980685, by rfl⟩ : syracuseStep 7974247 = 11961371) B11961371
theorem B4198607 : Blo 1865634 4198607 := bstep (se 1 (by rfl) ⟨3148955, by rfl⟩ : syracuseStep 4198607 = 6297911) B6297911
theorem B4198751 : Blo 1865634 4198751 := bstep (se 1 (by rfl) ⟨3149063, by rfl⟩ : syracuseStep 4198751 = 6298127) B6298127
theorem B2798783 : Blo 1865634 2798783 := bstep (se 1 (by rfl) ⟨2099087, by rfl⟩ : syracuseStep 2798783 = 4198175) B4198175
theorem B9451403 : Blo 1865634 9451403 := bstep (se 1 (by rfl) ⟨7088552, by rfl⟩ : syracuseStep 9451403 = 14177105) B14177105
theorem B1866687 : Blo 1865634 1866687 := bstep (se 1 (by rfl) ⟨1400015, by rfl⟩ : syracuseStep 1866687 = 2800031) B2800031
theorem B7969823 : Blo 1865634 7969823 := bstep (se 1 (by rfl) ⟨5977367, by rfl⟩ : syracuseStep 7969823 = 11954735) B11954735
theorem B4201883 : Blo 1865634 4201883 := bstep (se 1 (by rfl) ⟨3151412, by rfl⟩ : syracuseStep 4201883 = 6302825) B6302825
theorem B6300935 : Blo 1865634 6300935 := bstep (se 1 (by rfl) ⟨4725701, by rfl⟩ : syracuseStep 6300935 = 9451403) B9451403
theorem B103573997 : Blo 1865634 103573997 := bstep (se 3 (by rfl) ⟨19420124, by rfl⟩ : syracuseStep 103573997 = 38840249) B38840249
theorem B7089403 : Blo 1865634 7089403 := bstep (se 1 (by rfl) ⟨5317052, by rfl⟩ : syracuseStep 7089403 = 10634105) B10634105
theorem B3191483 : Blo 1865634 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B5313215 : Blo 1865634 5313215 := bstep (se 1 (by rfl) ⟨3984911, by rfl⟩ : syracuseStep 5313215 = 7969823) B7969823
theorem B2799071 : Blo 1865634 2799071 := bstep (se 1 (by rfl) ⟨2099303, by rfl⟩ : syracuseStep 2799071 = 4198607) B4198607
theorem B2799167 : Blo 1865634 2799167 := bstep (se 1 (by rfl) ⟨2099375, by rfl⟩ : syracuseStep 2799167 = 4198751) B4198751
theorem B1865855 : Blo 1865634 1865855 := bstep (se 1 (by rfl) ⟨1399391, by rfl⟩ : syracuseStep 1865855 = 2798783) B2798783
theorem B2800505 : Blo 1865634 2800505 := bstep (se 2 (by rfl) ⟨1050189, by rfl⟩ : syracuseStep 2800505 = 2100379) B2100379
theorem B14171273 : Blo 1865634 14171273 := bstep (se 2 (by rfl) ⟨5314227, by rfl⟩ : syracuseStep 14171273 = 10628455) B10628455
theorem B10632329 : Blo 1865634 10632329 := bstep (se 2 (by rfl) ⟨3987123, by rfl⟩ : syracuseStep 10632329 = 7974247) B7974247
theorem B2801255 : Blo 1865634 2801255 := bstep (se 1 (by rfl) ⟨2100941, by rfl⟩ : syracuseStep 2801255 = 4201883) B4201883
theorem B9447515 : Blo 1865634 9447515 := bstep (se 1 (by rfl) ⟨7085636, by rfl⟩ : syracuseStep 9447515 = 14171273) B14171273
theorem B7088219 : Blo 1865634 7088219 := bstep (se 1 (by rfl) ⟨5316164, by rfl⟩ : syracuseStep 7088219 = 10632329) B10632329
theorem B3542143 : Blo 1865634 3542143 := bstep (se 1 (by rfl) ⟨2656607, by rfl⟩ : syracuseStep 3542143 = 5313215) B5313215
theorem B2127655 : Blo 1865634 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B4200623 : Blo 1865634 4200623 := bstep (se 1 (by rfl) ⟨3150467, by rfl⟩ : syracuseStep 4200623 = 6300935) B6300935
theorem B1866047 : Blo 1865634 1866047 := bstep (se 1 (by rfl) ⟨1399535, by rfl⟩ : syracuseStep 1866047 = 2799071) B2799071
theorem B1866111 : Blo 1865634 1866111 := bstep (se 1 (by rfl) ⟨1399583, by rfl⟩ : syracuseStep 1866111 = 2799167) B2799167
theorem B69049331 : Blo 1865634 69049331 := bstep (se 1 (by rfl) ⟨51786998, by rfl⟩ : syracuseStep 69049331 = 103573997) B103573997
theorem B9452537 : Blo 1865634 9452537 := bstep (se 2 (by rfl) ⟨3544701, by rfl⟩ : syracuseStep 9452537 = 7089403) B7089403
theorem B1867003 : Blo 1865634 1867003 := bstep (se 1 (by rfl) ⟨1400252, by rfl⟩ : syracuseStep 1867003 = 2800505) B2800505
theorem B1867503 : Blo 1865634 1867503 := bstep (se 1 (by rfl) ⟨1400627, by rfl⟩ : syracuseStep 1867503 = 2801255) B2801255
theorem B46032887 : Blo 1865634 46032887 := bstep (se 1 (by rfl) ⟨34524665, by rfl⟩ : syracuseStep 46032887 = 69049331) B69049331
theorem B6301691 : Blo 1865634 6301691 := bstep (se 1 (by rfl) ⟨4726268, by rfl⟩ : syracuseStep 6301691 = 9452537) B9452537
theorem B2836873 : Blo 1865634 2836873 := bstep (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) B2127655
theorem B4722857 : Blo 1865634 4722857 := bstep (se 2 (by rfl) ⟨1771071, by rfl⟩ : syracuseStep 4722857 = 3542143) B3542143
theorem B6298343 : Blo 1865634 6298343 := bstep (se 1 (by rfl) ⟨4723757, by rfl⟩ : syracuseStep 6298343 = 9447515) B9447515
theorem B4725479 : Blo 1865634 4725479 := bstep (se 1 (by rfl) ⟨3544109, by rfl⟩ : syracuseStep 4725479 = 7088219) B7088219
theorem B2800415 : Blo 1865634 2800415 := bstep (se 1 (by rfl) ⟨2100311, by rfl⟩ : syracuseStep 2800415 = 4200623) B4200623
theorem B3148571 : Blo 1865634 3148571 := bstep (se 1 (by rfl) ⟨2361428, by rfl⟩ : syracuseStep 3148571 = 4722857) B4722857
theorem B4198895 : Blo 1865634 4198895 := bstep (se 1 (by rfl) ⟨3149171, by rfl⟩ : syracuseStep 4198895 = 6298343) B6298343
theorem B3150319 : Blo 1865634 3150319 := bstep (se 1 (by rfl) ⟨2362739, by rfl⟩ : syracuseStep 3150319 = 4725479) B4725479
theorem B122754365 : Blo 1865634 122754365 := bstep (se 3 (by rfl) ⟨23016443, by rfl⟩ : syracuseStep 122754365 = 46032887) B46032887
theorem B3782497 : Blo 1865634 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B4201127 : Blo 1865634 4201127 := bstep (se 1 (by rfl) ⟨3150845, by rfl⟩ : syracuseStep 4201127 = 6301691) B6301691
theorem B1866943 : Blo 1865634 1866943 := bstep (se 1 (by rfl) ⟨1400207, by rfl⟩ : syracuseStep 1866943 = 2800415) B2800415
theorem B2099047 : Blo 1865634 2099047 := bstep (se 1 (by rfl) ⟨1574285, by rfl⟩ : syracuseStep 2099047 = 3148571) B3148571
theorem B5043329 : Blo 1865634 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B2799263 : Blo 1865634 2799263 := bstep (se 1 (by rfl) ⟨2099447, by rfl⟩ : syracuseStep 2799263 = 4198895) B4198895
theorem B4200425 : Blo 1865634 4200425 := bstep (se 2 (by rfl) ⟨1575159, by rfl⟩ : syracuseStep 4200425 = 3150319) B3150319
theorem B81836243 : Blo 1865634 81836243 := bstep (se 1 (by rfl) ⟨61377182, by rfl⟩ : syracuseStep 81836243 = 122754365) B122754365
theorem B2800751 : Blo 1865634 2800751 := bstep (se 1 (by rfl) ⟨2100563, by rfl⟩ : syracuseStep 2800751 = 4201127) B4201127
theorem B3362219 : Blo 1865634 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B2798729 : Blo 1865634 2798729 := bstep (se 2 (by rfl) ⟨1049523, by rfl⟩ : syracuseStep 2798729 = 2099047) B2099047
theorem B1866175 : Blo 1865634 1866175 := bstep (se 1 (by rfl) ⟨1399631, by rfl⟩ : syracuseStep 1866175 = 2799263) B2799263
theorem B2800283 : Blo 1865634 2800283 := bstep (se 1 (by rfl) ⟨2100212, by rfl⟩ : syracuseStep 2800283 = 4200425) B4200425
theorem B54557495 : Blo 1865634 54557495 := bstep (se 1 (by rfl) ⟨40918121, by rfl⟩ : syracuseStep 54557495 = 81836243) B81836243
theorem B1867167 : Blo 1865634 1867167 := bstep (se 1 (by rfl) ⟨1400375, by rfl⟩ : syracuseStep 1867167 = 2800751) B2800751
theorem B2241479 : Blo 1865634 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B1865819 : Blo 1865634 1865819 := bstep (se 1 (by rfl) ⟨1399364, by rfl⟩ : syracuseStep 1865819 = 2798729) B2798729
theorem B1866855 : Blo 1865634 1866855 := bstep (se 1 (by rfl) ⟨1400141, by rfl⟩ : syracuseStep 1866855 = 2800283) B2800283
theorem B36371663 : Blo 1865634 36371663 := bstep (se 1 (by rfl) ⟨27278747, by rfl⟩ : syracuseStep 36371663 = 54557495) B54557495
theorem B5977277 : Blo 1865634 5977277 := bstep (se 3 (by rfl) ⟨1120739, by rfl⟩ : syracuseStep 5977277 = 2241479) B2241479
theorem B24247775 : Blo 1865634 24247775 := bstep (se 1 (by rfl) ⟨18185831, by rfl⟩ : syracuseStep 24247775 = 36371663) B36371663
theorem B16165183 : Blo 1865634 16165183 := bstep (se 1 (by rfl) ⟨12123887, by rfl⟩ : syracuseStep 16165183 = 24247775) B24247775
theorem B3984851 : Blo 1865634 3984851 := bstep (se 1 (by rfl) ⟨2988638, by rfl⟩ : syracuseStep 3984851 = 5977277) B5977277
theorem B21553577 : Blo 1865634 21553577 := bstep (se 2 (by rfl) ⟨8082591, by rfl⟩ : syracuseStep 21553577 = 16165183) B16165183
theorem B2656567 : Blo 1865634 2656567 := bstep (se 1 (by rfl) ⟨1992425, by rfl⟩ : syracuseStep 2656567 = 3984851) B3984851
theorem B14369051 : Blo 1865634 14369051 := bstep (se 1 (by rfl) ⟨10776788, by rfl⟩ : syracuseStep 14369051 = 21553577) B21553577
theorem B14168357 : Blo 1865634 14168357 := bstep (se 4 (by rfl) ⟨1328283, by rfl⟩ : syracuseStep 14168357 = 2656567) B2656567
theorem B9445571 : Blo 1865634 9445571 := bstep (se 1 (by rfl) ⟨7084178, by rfl⟩ : syracuseStep 9445571 = 14168357) B14168357
theorem B9579367 : Blo 1865634 9579367 := bstep (se 1 (by rfl) ⟨7184525, by rfl⟩ : syracuseStep 9579367 = 14369051) B14369051
theorem B51089957 : Blo 1865634 51089957 := bstep (se 4 (by rfl) ⟨4789683, by rfl⟩ : syracuseStep 51089957 = 9579367) B9579367
theorem B6297047 : Blo 1865634 6297047 := bstep (se 1 (by rfl) ⟨4722785, by rfl⟩ : syracuseStep 6297047 = 9445571) B9445571
theorem B4198031 : Blo 1865634 4198031 := bstep (se 1 (by rfl) ⟨3148523, by rfl⟩ : syracuseStep 4198031 = 6297047) B6297047
theorem B34059971 : Blo 1865634 34059971 := bstep (se 1 (by rfl) ⟨25544978, by rfl⟩ : syracuseStep 34059971 = 51089957) B51089957
theorem B90826589 : Blo 1865634 90826589 := bstep (se 3 (by rfl) ⟨17029985, by rfl⟩ : syracuseStep 90826589 = 34059971) B34059971
theorem B2798687 : Blo 1865634 2798687 := bstep (se 1 (by rfl) ⟨2099015, by rfl⟩ : syracuseStep 2798687 = 4198031) B4198031
theorem B60551059 : Blo 1865634 60551059 := bstep (se 1 (by rfl) ⟨45413294, by rfl⟩ : syracuseStep 60551059 = 90826589) B90826589
theorem B1865791 : Blo 1865634 1865791 := bstep (se 1 (by rfl) ⟨1399343, by rfl⟩ : syracuseStep 1865791 = 2798687) B2798687
theorem B80734745 : Blo 1865634 80734745 := bstep (se 2 (by rfl) ⟨30275529, by rfl⟩ : syracuseStep 80734745 = 60551059) B60551059
theorem B53823163 : Blo 1865634 53823163 := bstep (se 1 (by rfl) ⟨40367372, by rfl⟩ : syracuseStep 53823163 = 80734745) B80734745
theorem B71764217 : Blo 1865634 71764217 := bstep (se 2 (by rfl) ⟨26911581, by rfl⟩ : syracuseStep 71764217 = 53823163) B53823163
theorem B47842811 : Blo 1865634 47842811 := bstep (se 1 (by rfl) ⟨35882108, by rfl⟩ : syracuseStep 47842811 = 71764217) B71764217
theorem B31895207 : Blo 1865634 31895207 := bstep (se 1 (by rfl) ⟨23921405, by rfl⟩ : syracuseStep 31895207 = 47842811) B47842811
theorem B21263471 : Blo 1865634 21263471 := bstep (se 1 (by rfl) ⟨15947603, by rfl⟩ : syracuseStep 21263471 = 31895207) B31895207
theorem B14175647 : Blo 1865634 14175647 := bstep (se 1 (by rfl) ⟨10631735, by rfl⟩ : syracuseStep 14175647 = 21263471) B21263471
theorem B9450431 : Blo 1865634 9450431 := bstep (se 1 (by rfl) ⟨7087823, by rfl⟩ : syracuseStep 9450431 = 14175647) B14175647
theorem B6300287 : Blo 1865634 6300287 := bstep (se 1 (by rfl) ⟨4725215, by rfl⟩ : syracuseStep 6300287 = 9450431) B9450431
theorem B4200191 : Blo 1865634 4200191 := bstep (se 1 (by rfl) ⟨3150143, by rfl⟩ : syracuseStep 4200191 = 6300287) B6300287
theorem B2800127 : Blo 1865634 2800127 := bstep (se 1 (by rfl) ⟨2100095, by rfl⟩ : syracuseStep 2800127 = 4200191) B4200191
theorem B1866751 : Blo 1865634 1866751 := bstep (se 1 (by rfl) ⟨1400063, by rfl⟩ : syracuseStep 1866751 = 2800127) B2800127

theorem C0 (j : ℕ) (h1 : 466408 ≤ j) (h2 : j ≤ 466907) : Blo 1865634 (4 * j + 3) := by
  interval_cases j
  · exact B1865635
  · exact B1865639
  · exact B1865643
  · exact B1865647
  · exact B1865651
  · exact B1865655
  · exact B1865659
  · exact B1865663
  · exact B1865667
  · exact B1865671
  · exact B1865675
  · exact B1865679
  · exact B1865683
  · exact B1865687
  · exact B1865691
  · exact B1865695
  · exact B1865699
  · exact B1865703
  · exact B1865707
  · exact B1865711
  · exact B1865715
  · exact B1865719
  · exact B1865723
  · exact B1865727
  · exact B1865731
  · exact B1865735
  · exact B1865739
  · exact B1865743
  · exact B1865747
  · exact B1865751
  · exact B1865755
  · exact B1865759
  · exact B1865763
  · exact B1865767
  · exact B1865771
  · exact B1865775
  · exact B1865779
  · exact B1865783
  · exact B1865787
  · exact B1865791
  · exact B1865795
  · exact B1865799
  · exact B1865803
  · exact B1865807
  · exact B1865811
  · exact B1865815
  · exact B1865819
  · exact B1865823
  · exact B1865827
  · exact B1865831
  · exact B1865835
  · exact B1865839
  · exact B1865843
  · exact B1865847
  · exact B1865851
  · exact B1865855
  · exact B1865859
  · exact B1865863
  · exact B1865867
  · exact B1865871
  · exact B1865875
  · exact B1865879
  · exact B1865883
  · exact B1865887
  · exact B1865891
  · exact B1865895
  · exact B1865899
  · exact B1865903
  · exact B1865907
  · exact B1865911
  · exact B1865915
  · exact B1865919
  · exact B1865923
  · exact B1865927
  · exact B1865931
  · exact B1865935
  · exact B1865939
  · exact B1865943
  · exact B1865947
  · exact B1865951
  · exact B1865955
  · exact B1865959
  · exact B1865963
  · exact B1865967
  · exact B1865971
  · exact B1865975
  · exact B1865979
  · exact B1865983
  · exact B1865987
  · exact B1865991
  · exact B1865995
  · exact B1865999
  · exact B1866003
  · exact B1866007
  · exact B1866011
  · exact B1866015
  · exact B1866019
  · exact B1866023
  · exact B1866027
  · exact B1866031
  · exact B1866035
  · exact B1866039
  · exact B1866043
  · exact B1866047
  · exact B1866051
  · exact B1866055
  · exact B1866059
  · exact B1866063
  · exact B1866067
  · exact B1866071
  · exact B1866075
  · exact B1866079
  · exact B1866083
  · exact B1866087
  · exact B1866091
  · exact B1866095
  · exact B1866099
  · exact B1866103
  · exact B1866107
  · exact B1866111
  · exact B1866115
  · exact B1866119
  · exact B1866123
  · exact B1866127
  · exact B1866131
  · exact B1866135
  · exact B1866139
  · exact B1866143
  · exact B1866147
  · exact B1866151
  · exact B1866155
  · exact B1866159
  · exact B1866163
  · exact B1866167
  · exact B1866171
  · exact B1866175
  · exact B1866179
  · exact B1866183
  · exact B1866187
  · exact B1866191
  · exact B1866195
  · exact B1866199
  · exact B1866203
  · exact B1866207
  · exact B1866211
  · exact B1866215
  · exact B1866219
  · exact B1866223
  · exact B1866227
  · exact B1866231
  · exact B1866235
  · exact B1866239
  · exact B1866243
  · exact B1866247
  · exact B1866251
  · exact B1866255
  · exact B1866259
  · exact B1866263
  · exact B1866267
  · exact B1866271
  · exact B1866275
  · exact B1866279
  · exact B1866283
  · exact B1866287
  · exact B1866291
  · exact B1866295
  · exact B1866299
  · exact B1866303
  · exact B1866307
  · exact B1866311
  · exact B1866315
  · exact B1866319
  · exact B1866323
  · exact B1866327
  · exact B1866331
  · exact B1866335
  · exact B1866339
  · exact B1866343
  · exact B1866347
  · exact B1866351
  · exact B1866355
  · exact B1866359
  · exact B1866363
  · exact B1866367
  · exact B1866371
  · exact B1866375
  · exact B1866379
  · exact B1866383
  · exact B1866387
  · exact B1866391
  · exact B1866395
  · exact B1866399
  · exact B1866403
  · exact B1866407
  · exact B1866411
  · exact B1866415
  · exact B1866419
  · exact B1866423
  · exact B1866427
  · exact B1866431
  · exact B1866435
  · exact B1866439
  · exact B1866443
  · exact B1866447
  · exact B1866451
  · exact B1866455
  · exact B1866459
  · exact B1866463
  · exact B1866467
  · exact B1866471
  · exact B1866475
  · exact B1866479
  · exact B1866483
  · exact B1866487
  · exact B1866491
  · exact B1866495
  · exact B1866499
  · exact B1866503
  · exact B1866507
  · exact B1866511
  · exact B1866515
  · exact B1866519
  · exact B1866523
  · exact B1866527
  · exact B1866531
  · exact B1866535
  · exact B1866539
  · exact B1866543
  · exact B1866547
  · exact B1866551
  · exact B1866555
  · exact B1866559
  · exact B1866563
  · exact B1866567
  · exact B1866571
  · exact B1866575
  · exact B1866579
  · exact B1866583
  · exact B1866587
  · exact B1866591
  · exact B1866595
  · exact B1866599
  · exact B1866603
  · exact B1866607
  · exact B1866611
  · exact B1866615
  · exact B1866619
  · exact B1866623
  · exact B1866627
  · exact B1866631
  · exact B1866635
  · exact B1866639
  · exact B1866643
  · exact B1866647
  · exact B1866651
  · exact B1866655
  · exact B1866659
  · exact B1866663
  · exact B1866667
  · exact B1866671
  · exact B1866675
  · exact B1866679
  · exact B1866683
  · exact B1866687
  · exact B1866691
  · exact B1866695
  · exact B1866699
  · exact B1866703
  · exact B1866707
  · exact B1866711
  · exact B1866715
  · exact B1866719
  · exact B1866723
  · exact B1866727
  · exact B1866731
  · exact B1866735
  · exact B1866739
  · exact B1866743
  · exact B1866747
  · exact B1866751
  · exact B1866755
  · exact B1866759
  · exact B1866763
  · exact B1866767
  · exact B1866771
  · exact B1866775
  · exact B1866779
  · exact B1866783
  · exact B1866787
  · exact B1866791
  · exact B1866795
  · exact B1866799
  · exact B1866803
  · exact B1866807
  · exact B1866811
  · exact B1866815
  · exact B1866819
  · exact B1866823
  · exact B1866827
  · exact B1866831
  · exact B1866835
  · exact B1866839
  · exact B1866843
  · exact B1866847
  · exact B1866851
  · exact B1866855
  · exact B1866859
  · exact B1866863
  · exact B1866867
  · exact B1866871
  · exact B1866875
  · exact B1866879
  · exact B1866883
  · exact B1866887
  · exact B1866891
  · exact B1866895
  · exact B1866899
  · exact B1866903
  · exact B1866907
  · exact B1866911
  · exact B1866915
  · exact B1866919
  · exact B1866923
  · exact B1866927
  · exact B1866931
  · exact B1866935
  · exact B1866939
  · exact B1866943
  · exact B1866947
  · exact B1866951
  · exact B1866955
  · exact B1866959
  · exact B1866963
  · exact B1866967
  · exact B1866971
  · exact B1866975
  · exact B1866979
  · exact B1866983
  · exact B1866987
  · exact B1866991
  · exact B1866995
  · exact B1866999
  · exact B1867003
  · exact B1867007
  · exact B1867011
  · exact B1867015
  · exact B1867019
  · exact B1867023
  · exact B1867027
  · exact B1867031
  · exact B1867035
  · exact B1867039
  · exact B1867043
  · exact B1867047
  · exact B1867051
  · exact B1867055
  · exact B1867059
  · exact B1867063
  · exact B1867067
  · exact B1867071
  · exact B1867075
  · exact B1867079
  · exact B1867083
  · exact B1867087
  · exact B1867091
  · exact B1867095
  · exact B1867099
  · exact B1867103
  · exact B1867107
  · exact B1867111
  · exact B1867115
  · exact B1867119
  · exact B1867123
  · exact B1867127
  · exact B1867131
  · exact B1867135
  · exact B1867139
  · exact B1867143
  · exact B1867147
  · exact B1867151
  · exact B1867155
  · exact B1867159
  · exact B1867163
  · exact B1867167
  · exact B1867171
  · exact B1867175
  · exact B1867179
  · exact B1867183
  · exact B1867187
  · exact B1867191
  · exact B1867195
  · exact B1867199
  · exact B1867203
  · exact B1867207
  · exact B1867211
  · exact B1867215
  · exact B1867219
  · exact B1867223
  · exact B1867227
  · exact B1867231
  · exact B1867235
  · exact B1867239
  · exact B1867243
  · exact B1867247
  · exact B1867251
  · exact B1867255
  · exact B1867259
  · exact B1867263
  · exact B1867267
  · exact B1867271
  · exact B1867275
  · exact B1867279
  · exact B1867283
  · exact B1867287
  · exact B1867291
  · exact B1867295
  · exact B1867299
  · exact B1867303
  · exact B1867307
  · exact B1867311
  · exact B1867315
  · exact B1867319
  · exact B1867323
  · exact B1867327
  · exact B1867331
  · exact B1867335
  · exact B1867339
  · exact B1867343
  · exact B1867347
  · exact B1867351
  · exact B1867355
  · exact B1867359
  · exact B1867363
  · exact B1867367
  · exact B1867371
  · exact B1867375
  · exact B1867379
  · exact B1867383
  · exact B1867387
  · exact B1867391
  · exact B1867395
  · exact B1867399
  · exact B1867403
  · exact B1867407
  · exact B1867411
  · exact B1867415
  · exact B1867419
  · exact B1867423
  · exact B1867427
  · exact B1867431
  · exact B1867435
  · exact B1867439
  · exact B1867443
  · exact B1867447
  · exact B1867451
  · exact B1867455
  · exact B1867459
  · exact B1867463
  · exact B1867467
  · exact B1867471
  · exact B1867475
  · exact B1867479
  · exact B1867483
  · exact B1867487
  · exact B1867491
  · exact B1867495
  · exact B1867499
  · exact B1867503
  · exact B1867507
  · exact B1867511
  · exact B1867515
  · exact B1867519
  · exact B1867523
  · exact B1867527
  · exact B1867531
  · exact B1867535
  · exact B1867539
  · exact B1867543
  · exact B1867547
  · exact B1867551
  · exact B1867555
  · exact B1867559
  · exact B1867563
  · exact B1867567
  · exact B1867571
  · exact B1867575
  · exact B1867579
  · exact B1867583
  · exact B1867587
  · exact B1867591
  · exact B1867595
  · exact B1867599
  · exact B1867603
  · exact B1867607
  · exact B1867611
  · exact B1867615
  · exact B1867619
  · exact B1867623
  · exact B1867627
  · exact B1867631

theorem solution (m : ℕ) (hlo : 1865634 ≤ m) (hhi : m ≤ 1867634) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 466408 ≤ j := by omega
    have hj2 : j ≤ 466907 := by omega
    have hb : Blo 1865634 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
