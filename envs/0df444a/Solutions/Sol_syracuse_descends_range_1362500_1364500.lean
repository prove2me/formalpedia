-- Prove2me | solution 1 for syracuse_descends_range_1362500_1364500
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:56.664865+00:00
-- url     : https://prove2.me/submissions/8506f644-d950-4279-b312-1e79e5c20a53

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


theorem B2302013 : Blo 1362500 2302013 := bbase (se 3 (by rfl) ⟨431627, by rfl⟩ : syracuseStep 2302013 = 863255) (by norm_num)
theorem B39297109 : Blo 1362500 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B3686485 : Blo 1362500 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B1638505 : Blo 1362500 1638505 := bbase (se 2 (by rfl) ⟨614439, by rfl⟩ : syracuseStep 1638505 = 1228879) (by norm_num)
theorem B6897797 : Blo 1362500 6897797 := bbase (se 4 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 6897797 = 1293337) (by norm_num)
theorem B1638533 : Blo 1362500 1638533 := bbase (se 4 (by rfl) ⟨153612, by rfl⟩ : syracuseStep 1638533 = 307225) (by norm_num)
theorem B2588861 : Blo 1362500 2588861 := bbase (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) (by norm_num)
theorem B2302141 : Blo 1362500 2302141 := bbase (se 3 (by rfl) ⟨431651, by rfl⟩ : syracuseStep 2302141 = 863303) (by norm_num)
theorem B3449101 : Blo 1362500 3449101 := bbase (se 3 (by rfl) ⟨646706, by rfl⟩ : syracuseStep 3449101 = 1293413) (by norm_num)
theorem B2302229 : Blo 1362500 2302229 := bbase (se 6 (by rfl) ⟨53958, by rfl⟩ : syracuseStep 2302229 = 107917) (by norm_num)
theorem B1638721 : Blo 1362500 1638721 := bbase (se 2 (by rfl) ⟨614520, by rfl⟩ : syracuseStep 1638721 = 1229041) (by norm_num)
theorem B2589013 : Blo 1362500 2589013 := bbase (se 10 (by rfl) ⟨3792, by rfl⟩ : syracuseStep 2589013 = 7585) (by norm_num)
theorem B2457973 : Blo 1362500 2457973 := bbase (se 5 (by rfl) ⟨115217, by rfl⟩ : syracuseStep 2457973 = 230435) (by norm_num)
theorem B3449213 : Blo 1362500 3449213 := bbase (se 3 (by rfl) ⟨646727, by rfl⟩ : syracuseStep 3449213 = 1293455) (by norm_num)
theorem B4604309 : Blo 1362500 4604309 := bbase (se 6 (by rfl) ⟨107913, by rfl⟩ : syracuseStep 4604309 = 215827) (by norm_num)
theorem B2302357 : Blo 1362500 2302357 := bbase (se 6 (by rfl) ⟨53961, by rfl⟩ : syracuseStep 2302357 = 107923) (by norm_num)
theorem B1638841 : Blo 1362500 1638841 := bbase (se 2 (by rfl) ⟨614565, by rfl⟩ : syracuseStep 1638841 = 1229131) (by norm_num)
theorem B3498461 : Blo 1362500 3498461 := bbase (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) (by norm_num)
theorem B2302445 : Blo 1362500 2302445 := bbase (se 3 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 2302445 = 863417) (by norm_num)
theorem B2458117 : Blo 1362500 2458117 := bbase (se 4 (by rfl) ⟨230448, by rfl⟩ : syracuseStep 2458117 = 460897) (by norm_num)
theorem B4366885 : Blo 1362500 4366885 := bbase (se 4 (by rfl) ⟨409395, by rfl⟩ : syracuseStep 4366885 = 818791) (by norm_num)
theorem B3449405 : Blo 1362500 3449405 := bbase (se 3 (by rfl) ⟨646763, by rfl⟩ : syracuseStep 3449405 = 1293527) (by norm_num)
theorem B3883589 : Blo 1362500 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B15540821 : Blo 1362500 15540821 := bbase (se 8 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 15540821 = 182119) (by norm_num)
theorem B2302573 : Blo 1362500 2302573 := bbase (se 3 (by rfl) ⟨431732, by rfl⟩ : syracuseStep 2302573 = 863465) (by norm_num)
theorem B2589317 : Blo 1362500 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B1475237 : Blo 1362500 1475237 := bbase (se 4 (by rfl) ⟨138303, by rfl⟩ : syracuseStep 1475237 = 276607) (by norm_num)
theorem B4604741 : Blo 1362500 4604741 := bbase (se 4 (by rfl) ⟨431694, by rfl⟩ : syracuseStep 4604741 = 863389) (by norm_num)
theorem B1532821 : Blo 1362500 1532821 := bbase (se 6 (by rfl) ⟨35925, by rfl⟩ : syracuseStep 1532821 = 71851) (by norm_num)
theorem B3449749 : Blo 1362500 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B1532857 : Blo 1362500 1532857 := bbase (se 2 (by rfl) ⟨574821, by rfl⟩ : syracuseStep 1532857 = 1149643) (by norm_num)
theorem B1967053 : Blo 1362500 1967053 := bbase (se 3 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 1967053 = 737645) (by norm_num)
theorem B1532893 : Blo 1362500 1532893 := bbase (se 3 (by rfl) ⟨287417, by rfl⟩ : syracuseStep 1532893 = 574835) (by norm_num)
theorem B3884021 : Blo 1362500 3884021 := bbase (se 5 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 3884021 = 364127) (by norm_num)
theorem B6906869 : Blo 1362500 6906869 := bbase (se 5 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 6906869 = 647519) (by norm_num)
theorem B1532929 : Blo 1362500 1532929 := bbase (se 2 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 1532929 = 1149697) (by norm_num)
theorem B3449861 : Blo 1362500 3449861 := bbase (se 4 (by rfl) ⟨323424, by rfl⟩ : syracuseStep 3449861 = 646849) (by norm_num)
theorem B1532965 : Blo 1362500 1532965 := bbase (se 4 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 1532965 = 287431) (by norm_num)
theorem B5178437 : Blo 1362500 5178437 := bbase (se 4 (by rfl) ⟨485478, by rfl⟩ : syracuseStep 5178437 = 970957) (by norm_num)
theorem B1533001 : Blo 1362500 1533001 := bbase (se 2 (by rfl) ⟨574875, by rfl⟩ : syracuseStep 1533001 = 1149751) (by norm_num)
theorem B5825621 : Blo 1362500 5825621 := bbase (se 8 (by rfl) ⟨34134, by rfl⟩ : syracuseStep 5825621 = 68269) (by norm_num)
theorem B1533037 : Blo 1362500 1533037 := bbase (se 3 (by rfl) ⟨287444, by rfl⟩ : syracuseStep 1533037 = 574889) (by norm_num)
theorem B1533073 : Blo 1362500 1533073 := bbase (se 2 (by rfl) ⟨574902, by rfl⟩ : syracuseStep 1533073 = 1149805) (by norm_num)
theorem B6554789 : Blo 1362500 6554789 := bbase (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) (by norm_num)
theorem B1533109 : Blo 1362500 1533109 := bbase (se 5 (by rfl) ⟨71864, by rfl⟩ : syracuseStep 1533109 = 143729) (by norm_num)
theorem B1942717 : Blo 1362500 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B3450053 : Blo 1362500 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B1533145 : Blo 1362500 1533145 := bbase (se 2 (by rfl) ⟨574929, by rfl⟩ : syracuseStep 1533145 = 1149859) (by norm_num)
theorem B4605173 : Blo 1362500 4605173 := bbase (se 5 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 4605173 = 431735) (by norm_num)
theorem B1533181 : Blo 1362500 1533181 := bbase (se 3 (by rfl) ⟨287471, by rfl⟩ : syracuseStep 1533181 = 574943) (by norm_num)
theorem B1533217 : Blo 1362500 1533217 := bbase (se 2 (by rfl) ⟨574956, by rfl⟩ : syracuseStep 1533217 = 1149913) (by norm_num)
theorem B1533253 : Blo 1362500 1533253 := bbase (se 4 (by rfl) ⟨143742, by rfl⟩ : syracuseStep 1533253 = 287485) (by norm_num)
theorem B5178725 : Blo 1362500 5178725 := bbase (se 4 (by rfl) ⟨485505, by rfl⟩ : syracuseStep 5178725 = 971011) (by norm_num)
theorem B1533289 : Blo 1362500 1533289 := bbase (se 2 (by rfl) ⟨574983, by rfl⟩ : syracuseStep 1533289 = 1149967) (by norm_num)
theorem B2590069 : Blo 1362500 2590069 := bbase (se 5 (by rfl) ⟨121409, by rfl⟩ : syracuseStep 2590069 = 242819) (by norm_num)
theorem B1533325 : Blo 1362500 1533325 := bbase (se 3 (by rfl) ⟨287498, by rfl⟩ : syracuseStep 1533325 = 574997) (by norm_num)
theorem B6899093 : Blo 1362500 6899093 := bbase (se 6 (by rfl) ⟨161697, by rfl⟩ : syracuseStep 6899093 = 323395) (by norm_num)
theorem B1533361 : Blo 1362500 1533361 := bbase (se 2 (by rfl) ⟨575010, by rfl⟩ : syracuseStep 1533361 = 1150021) (by norm_num)
theorem B1533397 : Blo 1362500 1533397 := bbase (se 7 (by rfl) ⟨17969, by rfl⟩ : syracuseStep 1533397 = 35939) (by norm_num)
theorem B7366133 : Blo 1362500 7366133 := bbase (se 5 (by rfl) ⟨345287, by rfl⟩ : syracuseStep 7366133 = 690575) (by norm_num)
theorem B1533433 : Blo 1362500 1533433 := bbase (se 2 (by rfl) ⟨575037, by rfl⟩ : syracuseStep 1533433 = 1150075) (by norm_num)
theorem B2074109 : Blo 1362500 2074109 := bbase (se 3 (by rfl) ⟨388895, by rfl⟩ : syracuseStep 2074109 = 777791) (by norm_num)
theorem B2590213 : Blo 1362500 2590213 := bbase (se 4 (by rfl) ⟨242832, by rfl⟩ : syracuseStep 2590213 = 485665) (by norm_num)
theorem B1533469 : Blo 1362500 1533469 := bbase (se 3 (by rfl) ⟨287525, by rfl⟩ : syracuseStep 1533469 = 575051) (by norm_num)
theorem B3450397 : Blo 1362500 3450397 := bbase (se 3 (by rfl) ⟨646949, by rfl⟩ : syracuseStep 3450397 = 1293899) (by norm_num)
theorem B5678629 : Blo 1362500 5678629 := bbase (se 4 (by rfl) ⟨532371, by rfl⟩ : syracuseStep 5678629 = 1064743) (by norm_num)
theorem B1533505 : Blo 1362500 1533505 := bbase (se 2 (by rfl) ⟨575064, by rfl⟩ : syracuseStep 1533505 = 1150129) (by norm_num)
theorem B1533541 : Blo 1362500 1533541 := bbase (se 4 (by rfl) ⟨143769, by rfl⟩ : syracuseStep 1533541 = 287539) (by norm_num)
theorem B1533577 : Blo 1362500 1533577 := bbase (se 2 (by rfl) ⟨575091, by rfl⟩ : syracuseStep 1533577 = 1150183) (by norm_num)
theorem B3450509 : Blo 1362500 3450509 := bbase (se 3 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 3450509 = 1293941) (by norm_num)
theorem B2590373 : Blo 1362500 2590373 := bbase (se 4 (by rfl) ⟨242847, by rfl⟩ : syracuseStep 2590373 = 485695) (by norm_num)
theorem B1533613 : Blo 1362500 1533613 := bbase (se 3 (by rfl) ⟨287552, by rfl⟩ : syracuseStep 1533613 = 575105) (by norm_num)
theorem B5531333 : Blo 1362500 5531333 := bbase (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) (by norm_num)
theorem B1533649 : Blo 1362500 1533649 := bbase (se 2 (by rfl) ⟨575118, by rfl⟩ : syracuseStep 1533649 = 1150237) (by norm_num)
theorem B3319517 : Blo 1362500 3319517 := bbase (se 3 (by rfl) ⟨622409, by rfl⟩ : syracuseStep 3319517 = 1244819) (by norm_num)
theorem B3884773 : Blo 1362500 3884773 := bbase (se 4 (by rfl) ⟨364197, by rfl⟩ : syracuseStep 3884773 = 728395) (by norm_num)
theorem B1533685 : Blo 1362500 1533685 := bbase (se 5 (by rfl) ⟨71891, by rfl⟩ : syracuseStep 1533685 = 143783) (by norm_num)
theorem B8406773 : Blo 1362500 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B1533721 : Blo 1362500 1533721 := bbase (se 2 (by rfl) ⟨575145, by rfl⟩ : syracuseStep 1533721 = 1150291) (by norm_num)
theorem B1533757 : Blo 1362500 1533757 := bbase (se 3 (by rfl) ⟨287579, by rfl⟩ : syracuseStep 1533757 = 575159) (by norm_num)
theorem B3065669 : Blo 1362500 3065669 := bbase (se 4 (by rfl) ⟨287406, by rfl⟩ : syracuseStep 3065669 = 574813) (by norm_num)
theorem B3450701 : Blo 1362500 3450701 := bbase (se 3 (by rfl) ⟨647006, by rfl⟩ : syracuseStep 3450701 = 1294013) (by norm_num)
theorem B1533793 : Blo 1362500 1533793 := bbase (se 2 (by rfl) ⟨575172, by rfl⟩ : syracuseStep 1533793 = 1150345) (by norm_num)
theorem B1533829 : Blo 1362500 1533829 := bbase (se 4 (by rfl) ⟨143796, by rfl⟩ : syracuseStep 1533829 = 287593) (by norm_num)
theorem B3065741 : Blo 1362500 3065741 := bbase (se 3 (by rfl) ⟨574826, by rfl⟩ : syracuseStep 3065741 = 1149653) (by norm_num)
theorem B1533865 : Blo 1362500 1533865 := bbase (se 2 (by rfl) ⟨575199, by rfl⟩ : syracuseStep 1533865 = 1150399) (by norm_num)
theorem B1533901 : Blo 1362500 1533901 := bbase (se 3 (by rfl) ⟨287606, by rfl⟩ : syracuseStep 1533901 = 575213) (by norm_num)
theorem B3065813 : Blo 1362500 3065813 := bbase (se 7 (by rfl) ⟨35927, by rfl⟩ : syracuseStep 3065813 = 71855) (by norm_num)
theorem B1533937 : Blo 1362500 1533937 := bbase (se 2 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 1533937 = 1150453) (by norm_num)
theorem B1533973 : Blo 1362500 1533973 := bbase (se 6 (by rfl) ⟨35952, by rfl⟩ : syracuseStep 1533973 = 71905) (by norm_num)
theorem B3065885 : Blo 1362500 3065885 := bbase (se 3 (by rfl) ⟨574853, by rfl⟩ : syracuseStep 3065885 = 1149707) (by norm_num)
theorem B5826613 : Blo 1362500 5826613 := bbase (se 5 (by rfl) ⟨273122, by rfl⟩ : syracuseStep 5826613 = 546245) (by norm_num)
theorem B1534009 : Blo 1362500 1534009 := bbase (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) (by norm_num)
theorem B1534045 : Blo 1362500 1534045 := bbase (se 3 (by rfl) ⟨287633, by rfl⟩ : syracuseStep 1534045 = 575267) (by norm_num)
theorem B3065957 : Blo 1362500 3065957 := bbase (se 4 (by rfl) ⟨287433, by rfl⟩ : syracuseStep 3065957 = 574867) (by norm_num)
theorem B1534081 : Blo 1362500 1534081 := bbase (se 2 (by rfl) ⟨575280, by rfl⟩ : syracuseStep 1534081 = 1150561) (by norm_num)
theorem B3451045 : Blo 1362500 3451045 := bbase (se 4 (by rfl) ⟨323535, by rfl⟩ : syracuseStep 3451045 = 647071) (by norm_num)
theorem B1534117 : Blo 1362500 1534117 := bbase (se 4 (by rfl) ⟨143823, by rfl⟩ : syracuseStep 1534117 = 287647) (by norm_num)
theorem B3066029 : Blo 1362500 3066029 := bbase (se 3 (by rfl) ⟨574880, by rfl⟩ : syracuseStep 3066029 = 1149761) (by norm_num)
theorem B2803901 : Blo 1362500 2803901 := bbase (se 3 (by rfl) ⟨525731, by rfl⟩ : syracuseStep 2803901 = 1051463) (by norm_num)
theorem B1534153 : Blo 1362500 1534153 := bbase (se 2 (by rfl) ⟨575307, by rfl⟩ : syracuseStep 1534153 = 1150615) (by norm_num)
theorem B1534189 : Blo 1362500 1534189 := bbase (se 3 (by rfl) ⟨287660, by rfl⟩ : syracuseStep 1534189 = 575321) (by norm_num)
theorem B3066101 : Blo 1362500 3066101 := bbase (se 5 (by rfl) ⟨143723, by rfl⟩ : syracuseStep 3066101 = 287447) (by norm_num)
theorem B1534225 : Blo 1362500 1534225 := bbase (se 2 (by rfl) ⟨575334, by rfl⟩ : syracuseStep 1534225 = 1150669) (by norm_num)
theorem B3451157 : Blo 1362500 3451157 := bbase (se 6 (by rfl) ⟨80886, by rfl⟩ : syracuseStep 3451157 = 161773) (by norm_num)
theorem B1534261 : Blo 1362500 1534261 := bbase (se 5 (by rfl) ⟨71918, by rfl⟩ : syracuseStep 1534261 = 143837) (by norm_num)
theorem B3066173 : Blo 1362500 3066173 := bbase (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) (by norm_num)
theorem B4262213 : Blo 1362500 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B1534297 : Blo 1362500 1534297 := bbase (se 2 (by rfl) ⟨575361, by rfl⟩ : syracuseStep 1534297 = 1150723) (by norm_num)
theorem B1534333 : Blo 1362500 1534333 := bbase (se 3 (by rfl) ⟨287687, by rfl⟩ : syracuseStep 1534333 = 575375) (by norm_num)
theorem B3066245 : Blo 1362500 3066245 := bbase (se 4 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 3066245 = 574921) (by norm_num)
theorem B1534369 : Blo 1362500 1534369 := bbase (se 2 (by rfl) ⟨575388, by rfl⟩ : syracuseStep 1534369 = 1150777) (by norm_num)
theorem B1534405 : Blo 1362500 1534405 := bbase (se 4 (by rfl) ⟨143850, by rfl⟩ : syracuseStep 1534405 = 287701) (by norm_num)
theorem B3066317 : Blo 1362500 3066317 := bbase (se 3 (by rfl) ⟨574934, by rfl⟩ : syracuseStep 3066317 = 1149869) (by norm_num)
theorem B3451349 : Blo 1362500 3451349 := bbase (se 7 (by rfl) ⟨40445, by rfl⟩ : syracuseStep 3451349 = 80891) (by norm_num)
theorem B17484245 : Blo 1362500 17484245 := bbase (se 7 (by rfl) ⟨204893, by rfl⟩ : syracuseStep 17484245 = 409787) (by norm_num)
theorem B1534441 : Blo 1362500 1534441 := bbase (se 2 (by rfl) ⟨575415, by rfl⟩ : syracuseStep 1534441 = 1150831) (by norm_num)
theorem B5179909 : Blo 1362500 5179909 := bbase (se 4 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 5179909 = 971233) (by norm_num)
theorem B1534477 : Blo 1362500 1534477 := bbase (se 3 (by rfl) ⟨287714, by rfl⟩ : syracuseStep 1534477 = 575429) (by norm_num)
theorem B3066389 : Blo 1362500 3066389 := bbase (se 6 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 3066389 = 143737) (by norm_num)
theorem B1534513 : Blo 1362500 1534513 := bbase (se 2 (by rfl) ⟨575442, by rfl⟩ : syracuseStep 1534513 = 1150885) (by norm_num)
theorem B7088725 : Blo 1362500 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B1534549 : Blo 1362500 1534549 := bbase (se 8 (by rfl) ⟨8991, by rfl⟩ : syracuseStep 1534549 = 17983) (by norm_num)
theorem B3066461 : Blo 1362500 3066461 := bbase (se 3 (by rfl) ⟨574961, by rfl⟩ : syracuseStep 3066461 = 1149923) (by norm_num)
theorem B2910829 : Blo 1362500 2910829 := bbase (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) (by norm_num)
theorem B1534585 : Blo 1362500 1534585 := bbase (se 2 (by rfl) ⟨575469, by rfl⟩ : syracuseStep 1534585 = 1150939) (by norm_num)
theorem B3320453 : Blo 1362500 3320453 := bbase (se 4 (by rfl) ⟨311292, by rfl⟩ : syracuseStep 3320453 = 622585) (by norm_num)
theorem B1534621 : Blo 1362500 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B3066533 : Blo 1362500 3066533 := bbase (se 4 (by rfl) ⟨287487, by rfl⟩ : syracuseStep 3066533 = 574975) (by norm_num)
theorem B6900389 : Blo 1362500 6900389 := bbase (se 4 (by rfl) ⟨646911, by rfl⟩ : syracuseStep 6900389 = 1293823) (by norm_num)
theorem B1534657 : Blo 1362500 1534657 := bbase (se 2 (by rfl) ⟨575496, by rfl⟩ : syracuseStep 1534657 = 1150993) (by norm_num)
theorem B1534693 : Blo 1362500 1534693 := bbase (se 4 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 1534693 = 287755) (by norm_num)
theorem B3066605 : Blo 1362500 3066605 := bbase (se 3 (by rfl) ⟨574988, by rfl⟩ : syracuseStep 3066605 = 1149977) (by norm_num)
theorem B1534729 : Blo 1362500 1534729 := bbase (se 2 (by rfl) ⟨575523, by rfl⟩ : syracuseStep 1534729 = 1151047) (by norm_num)
theorem B17705749 : Blo 1362500 17705749 := bbase (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) (by norm_num)
theorem B2763565 : Blo 1362500 2763565 := bbase (se 3 (by rfl) ⟨518168, by rfl⟩ : syracuseStep 2763565 = 1036337) (by norm_num)
theorem B3451693 : Blo 1362500 3451693 := bbase (se 3 (by rfl) ⟨647192, by rfl⟩ : syracuseStep 3451693 = 1294385) (by norm_num)
theorem B1534765 : Blo 1362500 1534765 := bbase (se 3 (by rfl) ⟨287768, by rfl⟩ : syracuseStep 1534765 = 575537) (by norm_num)
theorem B3066677 : Blo 1362500 3066677 := bbase (se 5 (by rfl) ⟨143750, by rfl⟩ : syracuseStep 3066677 = 287501) (by norm_num)
theorem B2624309 : Blo 1362500 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B5180213 : Blo 1362500 5180213 := bbase (se 5 (by rfl) ⟨242822, by rfl⟩ : syracuseStep 5180213 = 485645) (by norm_num)
theorem B1534801 : Blo 1362500 1534801 := bbase (se 2 (by rfl) ⟨575550, by rfl⟩ : syracuseStep 1534801 = 1151101) (by norm_num)
theorem B1534837 : Blo 1362500 1534837 := bbase (se 5 (by rfl) ⟨71945, by rfl⟩ : syracuseStep 1534837 = 143891) (by norm_num)
theorem B3066749 : Blo 1362500 3066749 := bbase (se 3 (by rfl) ⟨575015, by rfl⟩ : syracuseStep 3066749 = 1150031) (by norm_num)
theorem B1534873 : Blo 1362500 1534873 := bbase (se 2 (by rfl) ⟨575577, by rfl⟩ : syracuseStep 1534873 = 1151155) (by norm_num)
theorem B3451805 : Blo 1362500 3451805 := bbase (se 3 (by rfl) ⟨647213, by rfl⟩ : syracuseStep 3451805 = 1294427) (by norm_num)
theorem B4598693 : Blo 1362500 4598693 := bbase (se 4 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 4598693 = 862255) (by norm_num)
theorem B1534909 : Blo 1362500 1534909 := bbase (se 3 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 1534909 = 575591) (by norm_num)
theorem B3066821 : Blo 1362500 3066821 := bbase (se 4 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 3066821 = 575029) (by norm_num)
theorem B1534945 : Blo 1362500 1534945 := bbase (se 2 (by rfl) ⟨575604, by rfl⟩ : syracuseStep 1534945 = 1151209) (by norm_num)
theorem B7187429 : Blo 1362500 7187429 := bbase (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) (by norm_num)
theorem B1534981 : Blo 1362500 1534981 := bbase (se 4 (by rfl) ⟨143904, by rfl⟩ : syracuseStep 1534981 = 287809) (by norm_num)
theorem B3066893 : Blo 1362500 3066893 := bbase (se 3 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 3066893 = 1150085) (by norm_num)
theorem B1535017 : Blo 1362500 1535017 := bbase (se 2 (by rfl) ⟨575631, by rfl⟩ : syracuseStep 1535017 = 1151263) (by norm_num)
theorem B1535053 : Blo 1362500 1535053 := bbase (se 3 (by rfl) ⟨287822, by rfl⟩ : syracuseStep 1535053 = 575645) (by norm_num)
theorem B3066965 : Blo 1362500 3066965 := bbase (se 8 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 3066965 = 35941) (by norm_num)
theorem B3451997 : Blo 1362500 3451997 := bbase (se 3 (by rfl) ⟨647249, by rfl⟩ : syracuseStep 3451997 = 1294499) (by norm_num)
theorem B6548597 : Blo 1362500 6548597 := bbase (se 5 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 6548597 = 613931) (by norm_num)
theorem B5049461 : Blo 1362500 5049461 := bbase (se 5 (by rfl) ⟨236693, by rfl⟩ : syracuseStep 5049461 = 473387) (by norm_num)
theorem B3067037 : Blo 1362500 3067037 := bbase (se 3 (by rfl) ⟨575069, by rfl⟩ : syracuseStep 3067037 = 1150139) (by norm_num)
theorem B5115109 : Blo 1362500 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B3067109 : Blo 1362500 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B3067181 : Blo 1362500 3067181 := bbase (se 3 (by rfl) ⟨575096, by rfl⟩ : syracuseStep 3067181 = 1150193) (by norm_num)
theorem B6548789 : Blo 1362500 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B11054389 : Blo 1362500 11054389 := bbase (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) (by norm_num)
theorem B5918005 : Blo 1362500 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B4369717 : Blo 1362500 4369717 := bbase (se 5 (by rfl) ⟨204830, by rfl⟩ : syracuseStep 4369717 = 409661) (by norm_num)
theorem B4599125 : Blo 1362500 4599125 := bbase (se 11 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 4599125 = 6737) (by norm_num)
theorem B2182501 : Blo 1362500 2182501 := bbase (se 4 (by rfl) ⟨204609, by rfl⟩ : syracuseStep 2182501 = 409219) (by norm_num)
theorem B3067253 : Blo 1362500 3067253 := bbase (se 5 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 3067253 = 287555) (by norm_num)
theorem B4369781 : Blo 1362500 4369781 := bbase (se 5 (by rfl) ⟨204833, by rfl⟩ : syracuseStep 4369781 = 409667) (by norm_num)
theorem B4148597 : Blo 1362500 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B3452341 : Blo 1362500 3452341 := bbase (se 5 (by rfl) ⟨161828, by rfl⟩ : syracuseStep 3452341 = 323657) (by norm_num)
theorem B3067325 : Blo 1362500 3067325 := bbase (se 3 (by rfl) ⟨575123, by rfl⟩ : syracuseStep 3067325 = 1150247) (by norm_num)
theorem B7376341 : Blo 1362500 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B2911717 : Blo 1362500 2911717 := bbase (se 4 (by rfl) ⟨272973, by rfl⟩ : syracuseStep 2911717 = 545947) (by norm_num)
theorem B3067397 : Blo 1362500 3067397 := bbase (se 4 (by rfl) ⟨287568, by rfl⟩ : syracuseStep 3067397 = 575137) (by norm_num)
theorem B3452453 : Blo 1362500 3452453 := bbase (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) (by norm_num)
theorem B3067469 : Blo 1362500 3067469 := bbase (se 3 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 3067469 = 1150301) (by norm_num)
theorem B3067541 : Blo 1362500 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B3067613 : Blo 1362500 3067613 := bbase (se 3 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 3067613 = 1150355) (by norm_num)
theorem B3452645 : Blo 1362500 3452645 := bbase (se 4 (by rfl) ⟨323685, by rfl⟩ : syracuseStep 3452645 = 647371) (by norm_num)
theorem B2838277 : Blo 1362500 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B4599557 : Blo 1362500 4599557 := bbase (se 4 (by rfl) ⟨431208, by rfl⟩ : syracuseStep 4599557 = 862417) (by norm_num)
theorem B3067685 : Blo 1362500 3067685 := bbase (se 4 (by rfl) ⟨287595, by rfl⟩ : syracuseStep 3067685 = 575191) (by norm_num)
theorem B3108701 : Blo 1362500 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B3321701 : Blo 1362500 3321701 := bbase (se 4 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 3321701 = 622819) (by norm_num)
theorem B3067757 : Blo 1362500 3067757 := bbase (se 3 (by rfl) ⟨575204, by rfl⟩ : syracuseStep 3067757 = 1150409) (by norm_num)
theorem B2043773 : Blo 1362500 2043773 := bbase (se 3 (by rfl) ⟨383207, by rfl⟩ : syracuseStep 2043773 = 766415) (by norm_num)
theorem B2043797 : Blo 1362500 2043797 := bbase (se 6 (by rfl) ⟨47901, by rfl⟩ : syracuseStep 2043797 = 95803) (by norm_num)
theorem B2658197 : Blo 1362500 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2764693 : Blo 1362500 2764693 := bbase (se 6 (by rfl) ⟨64797, by rfl⟩ : syracuseStep 2764693 = 129595) (by norm_num)
theorem B2043821 : Blo 1362500 2043821 := bbase (se 3 (by rfl) ⟨383216, by rfl⟩ : syracuseStep 2043821 = 766433) (by norm_num)
theorem B7761845 : Blo 1362500 7761845 := bbase (se 5 (by rfl) ⟨363836, by rfl⟩ : syracuseStep 7761845 = 727673) (by norm_num)
theorem B6901685 : Blo 1362500 6901685 := bbase (se 5 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 6901685 = 647033) (by norm_num)
theorem B3067829 : Blo 1362500 3067829 := bbase (se 5 (by rfl) ⟨143804, by rfl⟩ : syracuseStep 3067829 = 287609) (by norm_num)
theorem B2043845 : Blo 1362500 2043845 := bbase (se 4 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 2043845 = 383221) (by norm_num)
theorem B2912213 : Blo 1362500 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B5050325 : Blo 1362500 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B2043869 : Blo 1362500 2043869 := bbase (se 3 (by rfl) ⟨383225, by rfl⟩ : syracuseStep 2043869 = 766451) (by norm_num)
theorem B2043893 : Blo 1362500 2043893 := bbase (se 5 (by rfl) ⟨95807, by rfl⟩ : syracuseStep 2043893 = 191615) (by norm_num)
theorem B3067901 : Blo 1362500 3067901 := bbase (se 3 (by rfl) ⟨575231, by rfl⟩ : syracuseStep 3067901 = 1150463) (by norm_num)
theorem B1724429 : Blo 1362500 1724429 := bbase (se 3 (by rfl) ⟨323330, by rfl⟩ : syracuseStep 1724429 = 646661) (by norm_num)
theorem B2043917 : Blo 1362500 2043917 := bbase (se 3 (by rfl) ⟨383234, by rfl⟩ : syracuseStep 2043917 = 766469) (by norm_num)
theorem B2043941 : Blo 1362500 2043941 := bbase (se 4 (by rfl) ⟨191619, by rfl⟩ : syracuseStep 2043941 = 383239) (by norm_num)
theorem B2043965 : Blo 1362500 2043965 := bbase (se 3 (by rfl) ⟨383243, by rfl⟩ : syracuseStep 2043965 = 766487) (by norm_num)
theorem B3452989 : Blo 1362500 3452989 := bbase (se 3 (by rfl) ⟨647435, by rfl⟩ : syracuseStep 3452989 = 1294871) (by norm_num)
theorem B1724485 : Blo 1362500 1724485 := bbase (se 4 (by rfl) ⟨161670, by rfl⟩ : syracuseStep 1724485 = 323341) (by norm_num)
theorem B3067973 : Blo 1362500 3067973 := bbase (se 4 (by rfl) ⟨287622, by rfl⟩ : syracuseStep 3067973 = 575245) (by norm_num)
theorem B2043989 : Blo 1362500 2043989 := bbase (se 8 (by rfl) ⟨11976, by rfl⟩ : syracuseStep 2043989 = 23953) (by norm_num)
theorem B4911205 : Blo 1362500 4911205 := bbase (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) (by norm_num)
theorem B2101349 : Blo 1362500 2101349 := bbase (se 4 (by rfl) ⟨197001, by rfl⟩ : syracuseStep 2101349 = 394003) (by norm_num)
theorem B2044013 : Blo 1362500 2044013 := bbase (se 3 (by rfl) ⟨383252, by rfl⟩ : syracuseStep 2044013 = 766505) (by norm_num)
theorem B2044037 : Blo 1362500 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B3068045 : Blo 1362500 3068045 := bbase (se 3 (by rfl) ⟨575258, by rfl⟩ : syracuseStep 3068045 = 1150517) (by norm_num)
theorem B2044061 : Blo 1362500 2044061 := bbase (se 3 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 2044061 = 766523) (by norm_num)
theorem B1724581 : Blo 1362500 1724581 := bbase (se 4 (by rfl) ⟨161679, by rfl⟩ : syracuseStep 1724581 = 323359) (by norm_num)
theorem B3453101 : Blo 1362500 3453101 := bbase (se 3 (by rfl) ⟨647456, by rfl⟩ : syracuseStep 3453101 = 1294913) (by norm_num)
theorem B2044085 : Blo 1362500 2044085 := bbase (se 5 (by rfl) ⟨95816, by rfl⟩ : syracuseStep 2044085 = 191633) (by norm_num)
theorem B4599989 : Blo 1362500 4599989 := bbase (se 5 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 4599989 = 431249) (by norm_num)
theorem B2044109 : Blo 1362500 2044109 := bbase (se 3 (by rfl) ⟨383270, by rfl⟩ : syracuseStep 2044109 = 766541) (by norm_num)
theorem B3068117 : Blo 1362500 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B2044133 : Blo 1362500 2044133 := bbase (se 4 (by rfl) ⟨191637, by rfl⟩ : syracuseStep 2044133 = 383275) (by norm_num)
theorem B2044157 : Blo 1362500 2044157 := bbase (se 3 (by rfl) ⟨383279, by rfl⟩ : syracuseStep 2044157 = 766559) (by norm_num)
theorem B2044181 : Blo 1362500 2044181 := bbase (se 6 (by rfl) ⟨47910, by rfl⟩ : syracuseStep 2044181 = 95821) (by norm_num)
theorem B3068189 : Blo 1362500 3068189 := bbase (se 3 (by rfl) ⟨575285, by rfl⟩ : syracuseStep 3068189 = 1150571) (by norm_num)
theorem B2044205 : Blo 1362500 2044205 := bbase (se 3 (by rfl) ⟨383288, by rfl⟩ : syracuseStep 2044205 = 766577) (by norm_num)
theorem B11653429 : Blo 1362500 11653429 := bbase (se 5 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 11653429 = 1092509) (by norm_num)
theorem B2044229 : Blo 1362500 2044229 := bbase (se 4 (by rfl) ⟨191646, by rfl⟩ : syracuseStep 2044229 = 383293) (by norm_num)
theorem B1724753 : Blo 1362500 1724753 := bbase (se 2 (by rfl) ⟨646782, by rfl⟩ : syracuseStep 1724753 = 1293565) (by norm_num)
theorem B2044253 : Blo 1362500 2044253 := bbase (se 3 (by rfl) ⟨383297, by rfl⟩ : syracuseStep 2044253 = 766595) (by norm_num)
theorem B3068261 : Blo 1362500 3068261 := bbase (se 4 (by rfl) ⟨287649, by rfl⟩ : syracuseStep 3068261 = 575299) (by norm_num)
theorem B3453293 : Blo 1362500 3453293 := bbase (se 3 (by rfl) ⟨647492, by rfl⟩ : syracuseStep 3453293 = 1294985) (by norm_num)
theorem B2044277 : Blo 1362500 2044277 := bbase (se 5 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 2044277 = 191651) (by norm_num)
theorem B1724809 : Blo 1362500 1724809 := bbase (se 2 (by rfl) ⟨646803, by rfl⟩ : syracuseStep 1724809 = 1293607) (by norm_num)
theorem B1749385 : Blo 1362500 1749385 := bbase (se 2 (by rfl) ⟨656019, by rfl⟩ : syracuseStep 1749385 = 1312039) (by norm_num)
theorem B2044301 : Blo 1362500 2044301 := bbase (se 3 (by rfl) ⟨383306, by rfl⟩ : syracuseStep 2044301 = 766613) (by norm_num)
theorem B2044325 : Blo 1362500 2044325 := bbase (se 4 (by rfl) ⟨191655, by rfl⟩ : syracuseStep 2044325 = 383311) (by norm_num)
theorem B3068333 : Blo 1362500 3068333 := bbase (se 3 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 3068333 = 1150625) (by norm_num)
theorem B2044349 : Blo 1362500 2044349 := bbase (se 3 (by rfl) ⟨383315, by rfl⟩ : syracuseStep 2044349 = 766631) (by norm_num)
theorem B2044373 : Blo 1362500 2044373 := bbase (se 7 (by rfl) ⟨23957, by rfl⟩ : syracuseStep 2044373 = 47915) (by norm_num)
theorem B1724905 : Blo 1362500 1724905 := bbase (se 2 (by rfl) ⟨646839, by rfl⟩ : syracuseStep 1724905 = 1293679) (by norm_num)
theorem B2044397 : Blo 1362500 2044397 := bbase (se 3 (by rfl) ⟨383324, by rfl⟩ : syracuseStep 2044397 = 766649) (by norm_num)
theorem B3068405 : Blo 1362500 3068405 := bbase (se 5 (by rfl) ⟨143831, by rfl⟩ : syracuseStep 3068405 = 287663) (by norm_num)
theorem B2044421 : Blo 1362500 2044421 := bbase (se 4 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 2044421 = 383329) (by norm_num)
theorem B2044445 : Blo 1362500 2044445 := bbase (se 3 (by rfl) ⟨383333, by rfl⟩ : syracuseStep 2044445 = 766667) (by norm_num)
theorem B2044469 : Blo 1362500 2044469 := bbase (se 5 (by rfl) ⟨95834, by rfl⟩ : syracuseStep 2044469 = 191669) (by norm_num)
theorem B3068477 : Blo 1362500 3068477 := bbase (se 3 (by rfl) ⟨575339, by rfl⟩ : syracuseStep 3068477 = 1150679) (by norm_num)
theorem B2044493 : Blo 1362500 2044493 := bbase (se 3 (by rfl) ⟨383342, by rfl⟩ : syracuseStep 2044493 = 766685) (by norm_num)
theorem B2044517 : Blo 1362500 2044517 := bbase (se 4 (by rfl) ⟨191673, by rfl⟩ : syracuseStep 2044517 = 383347) (by norm_num)
theorem B4600421 : Blo 1362500 4600421 := bbase (se 4 (by rfl) ⟨431289, by rfl⟩ : syracuseStep 4600421 = 862579) (by norm_num)
theorem B2044541 : Blo 1362500 2044541 := bbase (se 3 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 2044541 = 766703) (by norm_num)
theorem B3068549 : Blo 1362500 3068549 := bbase (se 4 (by rfl) ⟨287676, by rfl⟩ : syracuseStep 3068549 = 575353) (by norm_num)
theorem B1725077 : Blo 1362500 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B2044565 : Blo 1362500 2044565 := bbase (se 6 (by rfl) ⟨47919, by rfl⟩ : syracuseStep 2044565 = 95839) (by norm_num)
theorem B2044589 : Blo 1362500 2044589 := bbase (se 3 (by rfl) ⟨383360, by rfl⟩ : syracuseStep 2044589 = 766721) (by norm_num)
theorem B2044613 : Blo 1362500 2044613 := bbase (se 4 (by rfl) ⟨191682, by rfl⟩ : syracuseStep 2044613 = 383365) (by norm_num)
theorem B3453637 : Blo 1362500 3453637 := bbase (se 4 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 3453637 = 647557) (by norm_num)
theorem B1725133 : Blo 1362500 1725133 := bbase (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) (by norm_num)
theorem B3068621 : Blo 1362500 3068621 := bbase (se 3 (by rfl) ⟨575366, by rfl⟩ : syracuseStep 3068621 = 1150733) (by norm_num)
theorem B2044637 : Blo 1362500 2044637 := bbase (se 3 (by rfl) ⟨383369, by rfl⟩ : syracuseStep 2044637 = 766739) (by norm_num)
theorem B2183917 : Blo 1362500 2183917 := bbase (se 3 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 2183917 = 818969) (by norm_num)
theorem B2044661 : Blo 1362500 2044661 := bbase (se 5 (by rfl) ⟨95843, by rfl⟩ : syracuseStep 2044661 = 191687) (by norm_num)
theorem B2044685 : Blo 1362500 2044685 := bbase (se 3 (by rfl) ⟨383378, by rfl⟩ : syracuseStep 2044685 = 766757) (by norm_num)
theorem B3068693 : Blo 1362500 3068693 := bbase (se 6 (by rfl) ⟨71922, by rfl⟩ : syracuseStep 3068693 = 143845) (by norm_num)
theorem B2044709 : Blo 1362500 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B1725229 : Blo 1362500 1725229 := bbase (se 3 (by rfl) ⟨323480, by rfl⟩ : syracuseStep 1725229 = 646961) (by norm_num)
theorem B2913077 : Blo 1362500 2913077 := bbase (se 5 (by rfl) ⟨136550, by rfl⟩ : syracuseStep 2913077 = 273101) (by norm_num)
theorem B3453749 : Blo 1362500 3453749 := bbase (se 5 (by rfl) ⟨161894, by rfl⟩ : syracuseStep 3453749 = 323789) (by norm_num)
theorem B2044733 : Blo 1362500 2044733 := bbase (se 3 (by rfl) ⟨383387, by rfl⟩ : syracuseStep 2044733 = 766775) (by norm_num)
theorem B17462101 : Blo 1362500 17462101 := bbase (se 9 (by rfl) ⟨51158, by rfl⟩ : syracuseStep 17462101 = 102317) (by norm_num)
theorem B2044757 : Blo 1362500 2044757 := bbase (se 9 (by rfl) ⟨5990, by rfl⟩ : syracuseStep 2044757 = 11981) (by norm_num)
theorem B13103957 : Blo 1362500 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B9835349 : Blo 1362500 9835349 := bbase (se 9 (by rfl) ⟨28814, by rfl⟩ : syracuseStep 9835349 = 57629) (by norm_num)
theorem B3068765 : Blo 1362500 3068765 := bbase (se 3 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 3068765 = 1150787) (by norm_num)
theorem B2044781 : Blo 1362500 2044781 := bbase (se 3 (by rfl) ⟨383396, by rfl⟩ : syracuseStep 2044781 = 766793) (by norm_num)
theorem B2044805 : Blo 1362500 2044805 := bbase (se 4 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 2044805 = 383401) (by norm_num)
theorem B2044829 : Blo 1362500 2044829 := bbase (se 3 (by rfl) ⟨383405, by rfl⟩ : syracuseStep 2044829 = 766811) (by norm_num)
theorem B1455013 : Blo 1362500 1455013 := bbase (se 4 (by rfl) ⟨136407, by rfl⟩ : syracuseStep 1455013 = 272815) (by norm_num)
theorem B3068837 : Blo 1362500 3068837 := bbase (se 4 (by rfl) ⟨287703, by rfl⟩ : syracuseStep 3068837 = 575407) (by norm_num)
theorem B2044853 : Blo 1362500 2044853 := bbase (se 5 (by rfl) ⟨95852, by rfl⟩ : syracuseStep 2044853 = 191705) (by norm_num)
theorem B1381313 : Blo 1362500 1381313 := bbase (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) (by norm_num)
theorem B2913221 : Blo 1362500 2913221 := bbase (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) (by norm_num)
theorem B2044877 : Blo 1362500 2044877 := bbase (se 3 (by rfl) ⟨383414, by rfl⟩ : syracuseStep 2044877 = 766829) (by norm_num)
theorem B3683285 : Blo 1362500 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B1725401 : Blo 1362500 1725401 := bbase (se 2 (by rfl) ⟨647025, by rfl⟩ : syracuseStep 1725401 = 1294051) (by norm_num)
theorem B2044901 : Blo 1362500 2044901 := bbase (se 4 (by rfl) ⟨191709, by rfl⟩ : syracuseStep 2044901 = 383419) (by norm_num)
theorem B2184173 : Blo 1362500 2184173 := bbase (se 3 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 2184173 = 819065) (by norm_num)
theorem B3068909 : Blo 1362500 3068909 := bbase (se 3 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 3068909 = 1150841) (by norm_num)
theorem B2044925 : Blo 1362500 2044925 := bbase (se 3 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 2044925 = 766847) (by norm_num)
theorem B2765821 : Blo 1362500 2765821 := bbase (se 3 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 2765821 = 1037183) (by norm_num)
theorem B1725457 : Blo 1362500 1725457 := bbase (se 2 (by rfl) ⟨647046, by rfl⟩ : syracuseStep 1725457 = 1294093) (by norm_num)
theorem B4600853 : Blo 1362500 4600853 := bbase (se 6 (by rfl) ⟨107832, by rfl⟩ : syracuseStep 4600853 = 215665) (by norm_num)
theorem B2044949 : Blo 1362500 2044949 := bbase (se 6 (by rfl) ⟨47928, by rfl⟩ : syracuseStep 2044949 = 95857) (by norm_num)
theorem B2044973 : Blo 1362500 2044973 := bbase (se 3 (by rfl) ⟨383432, by rfl⟩ : syracuseStep 2044973 = 766865) (by norm_num)
theorem B3068981 : Blo 1362500 3068981 := bbase (se 5 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 3068981 = 287717) (by norm_num)
theorem B2044997 : Blo 1362500 2044997 := bbase (se 4 (by rfl) ⟨191718, by rfl⟩ : syracuseStep 2044997 = 383437) (by norm_num)
theorem B2045021 : Blo 1362500 2045021 := bbase (se 3 (by rfl) ⟨383441, by rfl⟩ : syracuseStep 2045021 = 766883) (by norm_num)
theorem B1725553 : Blo 1362500 1725553 := bbase (se 2 (by rfl) ⟨647082, by rfl⟩ : syracuseStep 1725553 = 1294165) (by norm_num)
theorem B2045045 : Blo 1362500 2045045 := bbase (se 5 (by rfl) ⟨95861, by rfl⟩ : syracuseStep 2045045 = 191723) (by norm_num)
theorem B1750133 : Blo 1362500 1750133 := bbase (se 5 (by rfl) ⟨82037, by rfl⟩ : syracuseStep 1750133 = 164075) (by norm_num)
theorem B3069053 : Blo 1362500 3069053 := bbase (se 3 (by rfl) ⟨575447, by rfl⟩ : syracuseStep 3069053 = 1150895) (by norm_num)
theorem B2045069 : Blo 1362500 2045069 := bbase (se 3 (by rfl) ⟨383450, by rfl⟩ : syracuseStep 2045069 = 766901) (by norm_num)
theorem B2045093 : Blo 1362500 2045093 := bbase (se 4 (by rfl) ⟨191727, by rfl⟩ : syracuseStep 2045093 = 383455) (by norm_num)
theorem B2184365 : Blo 1362500 2184365 := bbase (se 3 (by rfl) ⟨409568, by rfl⟩ : syracuseStep 2184365 = 819137) (by norm_num)
theorem B2045117 : Blo 1362500 2045117 := bbase (se 3 (by rfl) ⟨383459, by rfl⟩ : syracuseStep 2045117 = 766919) (by norm_num)
theorem B6902981 : Blo 1362500 6902981 := bbase (se 4 (by rfl) ⟨647154, by rfl⟩ : syracuseStep 6902981 = 1294309) (by norm_num)
theorem B3069125 : Blo 1362500 3069125 := bbase (se 4 (by rfl) ⟨287730, by rfl⟩ : syracuseStep 3069125 = 575461) (by norm_num)
theorem B2045141 : Blo 1362500 2045141 := bbase (se 7 (by rfl) ⟨23966, by rfl⟩ : syracuseStep 2045141 = 47933) (by norm_num)
theorem B2045165 : Blo 1362500 2045165 := bbase (se 3 (by rfl) ⟨383468, by rfl⟩ : syracuseStep 2045165 = 766937) (by norm_num)
theorem B2045189 : Blo 1362500 2045189 := bbase (se 4 (by rfl) ⟨191736, by rfl⟩ : syracuseStep 2045189 = 383473) (by norm_num)
theorem B3069197 : Blo 1362500 3069197 := bbase (se 3 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 3069197 = 1150949) (by norm_num)
theorem B5174549 : Blo 1362500 5174549 := bbase (se 6 (by rfl) ⟨121278, by rfl⟩ : syracuseStep 5174549 = 242557) (by norm_num)
theorem B2045213 : Blo 1362500 2045213 := bbase (se 3 (by rfl) ⟨383477, by rfl⟩ : syracuseStep 2045213 = 766955) (by norm_num)
theorem B1725725 : Blo 1362500 1725725 := bbase (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) (by norm_num)
theorem B2045237 : Blo 1362500 2045237 := bbase (se 5 (by rfl) ⟨95870, by rfl⟩ : syracuseStep 2045237 = 191741) (by norm_num)
theorem B2331965 : Blo 1362500 2331965 := bbase (se 3 (by rfl) ⟨437243, by rfl⟩ : syracuseStep 2331965 = 874487) (by norm_num)
theorem B5051717 : Blo 1362500 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B2045261 : Blo 1362500 2045261 := bbase (se 3 (by rfl) ⟨383486, by rfl⟩ : syracuseStep 2045261 = 766973) (by norm_num)
theorem B1455445 : Blo 1362500 1455445 := bbase (se 13 (by rfl) ⟨266, by rfl⟩ : syracuseStep 1455445 = 533) (by norm_num)
theorem B1725781 : Blo 1362500 1725781 := bbase (se 16 (by rfl) ⟨39, by rfl⟩ : syracuseStep 1725781 = 79) (by norm_num)
theorem B3069269 : Blo 1362500 3069269 := bbase (se 15 (by rfl) ⟨140, by rfl⟩ : syracuseStep 3069269 = 281) (by norm_num)
theorem B6550885 : Blo 1362500 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B2045285 : Blo 1362500 2045285 := bbase (se 4 (by rfl) ⟨191745, by rfl⟩ : syracuseStep 2045285 = 383491) (by norm_num)
theorem B2045309 : Blo 1362500 2045309 := bbase (se 3 (by rfl) ⟨383495, by rfl⟩ : syracuseStep 2045309 = 766991) (by norm_num)
theorem B2045333 : Blo 1362500 2045333 := bbase (se 6 (by rfl) ⟨47937, by rfl⟩ : syracuseStep 2045333 = 95875) (by norm_num)
theorem B1455517 : Blo 1362500 1455517 := bbase (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) (by norm_num)
theorem B3069341 : Blo 1362500 3069341 := bbase (se 3 (by rfl) ⟨575501, by rfl⟩ : syracuseStep 3069341 = 1151003) (by norm_num)
theorem B2045357 : Blo 1362500 2045357 := bbase (se 3 (by rfl) ⟨383504, by rfl⟩ : syracuseStep 2045357 = 767009) (by norm_num)
theorem B1725877 : Blo 1362500 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B2299333 : Blo 1362500 2299333 := bbase (se 4 (by rfl) ⟨215562, by rfl⟩ : syracuseStep 2299333 = 431125) (by norm_num)
theorem B4601285 : Blo 1362500 4601285 := bbase (se 4 (by rfl) ⟨431370, by rfl⟩ : syracuseStep 4601285 = 862741) (by norm_num)
theorem B2045381 : Blo 1362500 2045381 := bbase (se 4 (by rfl) ⟨191754, by rfl⟩ : syracuseStep 2045381 = 383509) (by norm_num)
theorem B2045405 : Blo 1362500 2045405 := bbase (se 3 (by rfl) ⟨383513, by rfl⟩ : syracuseStep 2045405 = 767027) (by norm_num)
theorem B3069413 : Blo 1362500 3069413 := bbase (se 4 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 3069413 = 575515) (by norm_num)
theorem B2045429 : Blo 1362500 2045429 := bbase (se 5 (by rfl) ⟨95879, by rfl⟩ : syracuseStep 2045429 = 191759) (by norm_num)
theorem B2045453 : Blo 1362500 2045453 := bbase (se 3 (by rfl) ⟨383522, by rfl⟩ : syracuseStep 2045453 = 767045) (by norm_num)
theorem B2299421 : Blo 1362500 2299421 := bbase (se 3 (by rfl) ⟨431141, by rfl⟩ : syracuseStep 2299421 = 862283) (by norm_num)
theorem B2045477 : Blo 1362500 2045477 := bbase (se 4 (by rfl) ⟨191763, by rfl⟩ : syracuseStep 2045477 = 383527) (by norm_num)
theorem B3069485 : Blo 1362500 3069485 := bbase (se 3 (by rfl) ⟨575528, by rfl⟩ : syracuseStep 3069485 = 1151057) (by norm_num)
theorem B5174837 : Blo 1362500 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B2045501 : Blo 1362500 2045501 := bbase (se 3 (by rfl) ⟨383531, by rfl⟩ : syracuseStep 2045501 = 767063) (by norm_num)
theorem B2045525 : Blo 1362500 2045525 := bbase (se 8 (by rfl) ⟨11985, by rfl⟩ : syracuseStep 2045525 = 23971) (by norm_num)
theorem B1726049 : Blo 1362500 1726049 := bbase (se 2 (by rfl) ⟨647268, by rfl⟩ : syracuseStep 1726049 = 1294537) (by norm_num)
theorem B2045549 : Blo 1362500 2045549 := bbase (se 3 (by rfl) ⟨383540, by rfl⟩ : syracuseStep 2045549 = 767081) (by norm_num)
theorem B3069557 : Blo 1362500 3069557 := bbase (se 5 (by rfl) ⟨143885, by rfl⟩ : syracuseStep 3069557 = 287771) (by norm_num)
theorem B2045573 : Blo 1362500 2045573 := bbase (se 4 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 2045573 = 383545) (by norm_num)
theorem B1726105 : Blo 1362500 1726105 := bbase (se 2 (by rfl) ⟨647289, by rfl⟩ : syracuseStep 1726105 = 1294579) (by norm_num)
theorem B2299549 : Blo 1362500 2299549 := bbase (se 3 (by rfl) ⟨431165, by rfl⟩ : syracuseStep 2299549 = 862331) (by norm_num)
theorem B2045597 : Blo 1362500 2045597 := bbase (se 3 (by rfl) ⟨383549, by rfl⟩ : syracuseStep 2045597 = 767099) (by norm_num)
theorem B2913965 : Blo 1362500 2913965 := bbase (se 3 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 2913965 = 1092737) (by norm_num)
theorem B2045621 : Blo 1362500 2045621 := bbase (se 5 (by rfl) ⟨95888, by rfl⟩ : syracuseStep 2045621 = 191777) (by norm_num)
theorem B3069629 : Blo 1362500 3069629 := bbase (se 3 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 3069629 = 1151111) (by norm_num)
theorem B2045645 : Blo 1362500 2045645 := bbase (se 3 (by rfl) ⟨383558, by rfl⟩ : syracuseStep 2045645 = 767117) (by norm_num)
theorem B39319253 : Blo 1362500 39319253 := bbase (se 7 (by rfl) ⟨460772, by rfl⟩ : syracuseStep 39319253 = 921545) (by norm_num)
theorem B2045669 : Blo 1362500 2045669 := bbase (se 4 (by rfl) ⟨191781, by rfl⟩ : syracuseStep 2045669 = 383563) (by norm_num)
theorem B2299637 : Blo 1362500 2299637 := bbase (se 5 (by rfl) ⟨107795, by rfl⟩ : syracuseStep 2299637 = 215591) (by norm_num)
theorem B1726201 : Blo 1362500 1726201 := bbase (se 2 (by rfl) ⟨647325, by rfl⟩ : syracuseStep 1726201 = 1294651) (by norm_num)
theorem B2045693 : Blo 1362500 2045693 := bbase (se 3 (by rfl) ⟨383567, by rfl⟩ : syracuseStep 2045693 = 767135) (by norm_num)
theorem B3069701 : Blo 1362500 3069701 := bbase (se 4 (by rfl) ⟨287784, by rfl⟩ : syracuseStep 3069701 = 575569) (by norm_num)
theorem B1455889 : Blo 1362500 1455889 := bbase (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) (by norm_num)
theorem B2045717 : Blo 1362500 2045717 := bbase (se 6 (by rfl) ⟨47946, by rfl⟩ : syracuseStep 2045717 = 95893) (by norm_num)
theorem B2045741 : Blo 1362500 2045741 := bbase (se 3 (by rfl) ⟨383576, by rfl⟩ : syracuseStep 2045741 = 767153) (by norm_num)
theorem B2045765 : Blo 1362500 2045765 := bbase (se 4 (by rfl) ⟨191790, by rfl⟩ : syracuseStep 2045765 = 383581) (by norm_num)
theorem B1382221 : Blo 1362500 1382221 := bbase (se 3 (by rfl) ⟨259166, by rfl⟩ : syracuseStep 1382221 = 518333) (by norm_num)
theorem B3069773 : Blo 1362500 3069773 := bbase (se 3 (by rfl) ⟨575582, by rfl⟩ : syracuseStep 3069773 = 1151165) (by norm_num)
theorem B2045789 : Blo 1362500 2045789 := bbase (se 3 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 2045789 = 767171) (by norm_num)
theorem B2299765 : Blo 1362500 2299765 := bbase (se 5 (by rfl) ⟨107801, by rfl⟩ : syracuseStep 2299765 = 215603) (by norm_num)
theorem B4601717 : Blo 1362500 4601717 := bbase (se 5 (by rfl) ⟨215705, by rfl⟩ : syracuseStep 4601717 = 431411) (by norm_num)
theorem B2045813 : Blo 1362500 2045813 := bbase (se 5 (by rfl) ⟨95897, by rfl⟩ : syracuseStep 2045813 = 191795) (by norm_num)
theorem B2455429 : Blo 1362500 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B2045837 : Blo 1362500 2045837 := bbase (se 3 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 2045837 = 767189) (by norm_num)
theorem B3069845 : Blo 1362500 3069845 := bbase (se 6 (by rfl) ⟨71949, by rfl⟩ : syracuseStep 3069845 = 143899) (by norm_num)
theorem B2045861 : Blo 1362500 2045861 := bbase (se 4 (by rfl) ⟨191799, by rfl⟩ : syracuseStep 2045861 = 383599) (by norm_num)
theorem B1726373 : Blo 1362500 1726373 := bbase (se 4 (by rfl) ⟨161847, by rfl⟩ : syracuseStep 1726373 = 323695) (by norm_num)
theorem B2045885 : Blo 1362500 2045885 := bbase (se 3 (by rfl) ⟨383603, by rfl⟩ : syracuseStep 2045885 = 767207) (by norm_num)
theorem B2455493 : Blo 1362500 2455493 := bbase (se 4 (by rfl) ⟨230202, by rfl⟩ : syracuseStep 2455493 = 460405) (by norm_num)
theorem B2299853 : Blo 1362500 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B2045909 : Blo 1362500 2045909 := bbase (se 7 (by rfl) ⟨23975, by rfl⟩ : syracuseStep 2045909 = 47951) (by norm_num)
theorem B1726429 : Blo 1362500 1726429 := bbase (se 3 (by rfl) ⟨323705, by rfl⟩ : syracuseStep 1726429 = 647411) (by norm_num)
theorem B3069917 : Blo 1362500 3069917 := bbase (se 3 (by rfl) ⟨575609, by rfl⟩ : syracuseStep 3069917 = 1151219) (by norm_num)
theorem B2045933 : Blo 1362500 2045933 := bbase (se 3 (by rfl) ⟨383612, by rfl⟩ : syracuseStep 2045933 = 767225) (by norm_num)
theorem B2586629 : Blo 1362500 2586629 := bbase (se 4 (by rfl) ⟨242496, by rfl⟩ : syracuseStep 2586629 = 484993) (by norm_num)
theorem B2045957 : Blo 1362500 2045957 := bbase (se 4 (by rfl) ⟨191808, by rfl⟩ : syracuseStep 2045957 = 383617) (by norm_num)
theorem B2045981 : Blo 1362500 2045981 := bbase (se 3 (by rfl) ⟨383621, by rfl⟩ : syracuseStep 2045981 = 767243) (by norm_num)
theorem B3069989 : Blo 1362500 3069989 := bbase (se 4 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 3069989 = 575623) (by norm_num)
theorem B2046005 : Blo 1362500 2046005 := bbase (se 5 (by rfl) ⟨95906, by rfl⟩ : syracuseStep 2046005 = 191813) (by norm_num)
theorem B3495997 : Blo 1362500 3495997 := bbase (se 3 (by rfl) ⟨655499, by rfl⟩ : syracuseStep 3495997 = 1310999) (by norm_num)
theorem B1726525 : Blo 1362500 1726525 := bbase (se 3 (by rfl) ⟨323723, by rfl⟩ : syracuseStep 1726525 = 647447) (by norm_num)
theorem B2299981 : Blo 1362500 2299981 := bbase (se 3 (by rfl) ⟨431246, by rfl⟩ : syracuseStep 2299981 = 862493) (by norm_num)
theorem B2046029 : Blo 1362500 2046029 := bbase (se 3 (by rfl) ⟨383630, by rfl⟩ : syracuseStep 2046029 = 767261) (by norm_num)
theorem B4913237 : Blo 1362500 4913237 := bbase (se 8 (by rfl) ⟨28788, by rfl⟩ : syracuseStep 4913237 = 57577) (by norm_num)
theorem B2185301 : Blo 1362500 2185301 := bbase (se 8 (by rfl) ⟨12804, by rfl⟩ : syracuseStep 2185301 = 25609) (by norm_num)
theorem B2046053 : Blo 1362500 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B3070061 : Blo 1362500 3070061 := bbase (se 3 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 3070061 = 1151273) (by norm_num)
theorem B2046077 : Blo 1362500 2046077 := bbase (se 3 (by rfl) ⟨383639, by rfl⟩ : syracuseStep 2046077 = 767279) (by norm_num)
theorem B1456265 : Blo 1362500 1456265 := bbase (se 2 (by rfl) ⟨546099, by rfl⟩ : syracuseStep 1456265 = 1092199) (by norm_num)
theorem B2046101 : Blo 1362500 2046101 := bbase (se 6 (by rfl) ⟨47955, by rfl⟩ : syracuseStep 2046101 = 95911) (by norm_num)
theorem B2300069 : Blo 1362500 2300069 := bbase (se 4 (by rfl) ⟨215631, by rfl⟩ : syracuseStep 2300069 = 431263) (by norm_num)
theorem B2046125 : Blo 1362500 2046125 := bbase (se 3 (by rfl) ⟨383648, by rfl⟩ : syracuseStep 2046125 = 767297) (by norm_num)
theorem B2046149 : Blo 1362500 2046149 := bbase (se 4 (by rfl) ⟨191826, by rfl⟩ : syracuseStep 2046149 = 383653) (by norm_num)
theorem B1456337 : Blo 1362500 1456337 := bbase (se 2 (by rfl) ⟨546126, by rfl⟩ : syracuseStep 1456337 = 1092253) (by norm_num)
theorem B2046173 : Blo 1362500 2046173 := bbase (se 3 (by rfl) ⟨383657, by rfl⟩ : syracuseStep 2046173 = 767315) (by norm_num)
theorem B1726697 : Blo 1362500 1726697 := bbase (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) (by norm_num)
theorem B12957941 : Blo 1362500 12957941 := bbase (se 5 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 12957941 = 1214807) (by norm_num)
theorem B2046197 : Blo 1362500 2046197 := bbase (se 5 (by rfl) ⟨95915, by rfl⟩ : syracuseStep 2046197 = 191831) (by norm_num)
theorem B11655413 : Blo 1362500 11655413 := bbase (se 5 (by rfl) ⟨546347, by rfl⟩ : syracuseStep 11655413 = 1092695) (by norm_num)
theorem B2046221 : Blo 1362500 2046221 := bbase (se 3 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 2046221 = 767333) (by norm_num)
theorem B3275029 : Blo 1362500 3275029 := bbase (se 6 (by rfl) ⟨76758, by rfl⟩ : syracuseStep 3275029 = 153517) (by norm_num)
theorem B1726753 : Blo 1362500 1726753 := bbase (se 2 (by rfl) ⟨647532, by rfl⟩ : syracuseStep 1726753 = 1295065) (by norm_num)
theorem B2586917 : Blo 1362500 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B2300197 : Blo 1362500 2300197 := bbase (se 4 (by rfl) ⟨215643, by rfl⟩ : syracuseStep 2300197 = 431287) (by norm_num)
theorem B4602149 : Blo 1362500 4602149 := bbase (se 4 (by rfl) ⟨431451, by rfl⟩ : syracuseStep 4602149 = 862903) (by norm_num)
theorem B2046245 : Blo 1362500 2046245 := bbase (se 4 (by rfl) ⟨191835, by rfl⟩ : syracuseStep 2046245 = 383671) (by norm_num)
theorem B2046269 : Blo 1362500 2046269 := bbase (se 3 (by rfl) ⟨383675, by rfl⟩ : syracuseStep 2046269 = 767351) (by norm_num)
theorem B2046293 : Blo 1362500 2046293 := bbase (se 10 (by rfl) ⟨2997, by rfl⟩ : syracuseStep 2046293 = 5995) (by norm_num)
theorem B2046317 : Blo 1362500 2046317 := bbase (se 3 (by rfl) ⟨383684, by rfl⟩ : syracuseStep 2046317 = 767369) (by norm_num)
theorem B3881333 : Blo 1362500 3881333 := bbase (se 5 (by rfl) ⟨181937, by rfl⟩ : syracuseStep 3881333 = 363875) (by norm_num)
theorem B2300285 : Blo 1362500 2300285 := bbase (se 3 (by rfl) ⟨431303, by rfl⟩ : syracuseStep 2300285 = 862607) (by norm_num)
theorem B1726849 : Blo 1362500 1726849 := bbase (se 2 (by rfl) ⟨647568, by rfl⟩ : syracuseStep 1726849 = 1295137) (by norm_num)
theorem B1382789 : Blo 1362500 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B2046341 : Blo 1362500 2046341 := bbase (se 4 (by rfl) ⟨191844, by rfl⟩ : syracuseStep 2046341 = 383689) (by norm_num)
theorem B1456525 : Blo 1362500 1456525 := bbase (se 3 (by rfl) ⟨273098, by rfl⟩ : syracuseStep 1456525 = 546197) (by norm_num)
theorem B2046365 : Blo 1362500 2046365 := bbase (se 3 (by rfl) ⟨383693, by rfl⟩ : syracuseStep 2046365 = 767387) (by norm_num)
theorem B5527973 : Blo 1362500 5527973 := bbase (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) (by norm_num)
theorem B1661357 : Blo 1362500 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B1382837 : Blo 1362500 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B2046389 : Blo 1362500 2046389 := bbase (se 5 (by rfl) ⟨95924, by rfl⟩ : syracuseStep 2046389 = 191849) (by norm_num)
theorem B2587069 : Blo 1362500 2587069 := bbase (se 3 (by rfl) ⟨485075, by rfl⟩ : syracuseStep 2587069 = 970151) (by norm_num)
theorem B2046413 : Blo 1362500 2046413 := bbase (se 3 (by rfl) ⟨383702, by rfl⟩ : syracuseStep 2046413 = 767405) (by norm_num)
theorem B3275221 : Blo 1362500 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B6904277 : Blo 1362500 6904277 := bbase (se 7 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 6904277 = 161819) (by norm_num)
theorem B2046437 : Blo 1362500 2046437 := bbase (se 4 (by rfl) ⟨191853, by rfl⟩ : syracuseStep 2046437 = 383707) (by norm_num)
theorem B3275261 : Blo 1362500 3275261 := bbase (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) (by norm_num)
theorem B2300413 : Blo 1362500 2300413 := bbase (se 3 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 2300413 = 862655) (by norm_num)
theorem B2046461 : Blo 1362500 2046461 := bbase (se 3 (by rfl) ⟨383711, by rfl⟩ : syracuseStep 2046461 = 767423) (by norm_num)
theorem B2046485 : Blo 1362500 2046485 := bbase (se 6 (by rfl) ⟨47964, by rfl⟩ : syracuseStep 2046485 = 95929) (by norm_num)
theorem B2046509 : Blo 1362500 2046509 := bbase (se 3 (by rfl) ⟨383720, by rfl⟩ : syracuseStep 2046509 = 767441) (by norm_num)
theorem B1456709 : Blo 1362500 1456709 := bbase (se 4 (by rfl) ⟨136566, by rfl⟩ : syracuseStep 1456709 = 273133) (by norm_num)
theorem B2046533 : Blo 1362500 2046533 := bbase (se 4 (by rfl) ⟨191862, by rfl⟩ : syracuseStep 2046533 = 383725) (by norm_num)
theorem B2300501 : Blo 1362500 2300501 := bbase (se 8 (by rfl) ⟨13479, by rfl⟩ : syracuseStep 2300501 = 26959) (by norm_num)
theorem B1636957 : Blo 1362500 1636957 := bbase (se 3 (by rfl) ⟨306929, by rfl⟩ : syracuseStep 1636957 = 613859) (by norm_num)
theorem B2046557 : Blo 1362500 2046557 := bbase (se 3 (by rfl) ⟨383729, by rfl⟩ : syracuseStep 2046557 = 767459) (by norm_num)
theorem B8977013 : Blo 1362500 8977013 := bbase (se 5 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 8977013 = 841595) (by norm_num)
theorem B2046581 : Blo 1362500 2046581 := bbase (se 5 (by rfl) ⟨95933, by rfl⟩ : syracuseStep 2046581 = 191867) (by norm_num)
theorem B2046605 : Blo 1362500 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B2046629 : Blo 1362500 2046629 := bbase (se 4 (by rfl) ⟨191871, by rfl⟩ : syracuseStep 2046629 = 383743) (by norm_num)
theorem B2456237 : Blo 1362500 2456237 := bbase (se 3 (by rfl) ⟨460544, by rfl⟩ : syracuseStep 2456237 = 921089) (by norm_num)
theorem B1637053 : Blo 1362500 1637053 := bbase (se 3 (by rfl) ⟨306947, by rfl⟩ : syracuseStep 1637053 = 613895) (by norm_num)
theorem B2046653 : Blo 1362500 2046653 := bbase (se 3 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 2046653 = 767495) (by norm_num)
theorem B5176021 : Blo 1362500 5176021 := bbase (se 7 (by rfl) ⟨60656, by rfl⟩ : syracuseStep 5176021 = 121313) (by norm_num)
theorem B2300629 : Blo 1362500 2300629 := bbase (se 7 (by rfl) ⟨26960, by rfl⟩ : syracuseStep 2300629 = 53921) (by norm_num)
theorem B4602581 : Blo 1362500 4602581 := bbase (se 7 (by rfl) ⟨53936, by rfl⟩ : syracuseStep 4602581 = 107873) (by norm_num)
theorem B2046677 : Blo 1362500 2046677 := bbase (se 7 (by rfl) ⟨23984, by rfl⟩ : syracuseStep 2046677 = 47969) (by norm_num)
theorem B2587373 : Blo 1362500 2587373 := bbase (se 3 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 2587373 = 970265) (by norm_num)
theorem B2046701 : Blo 1362500 2046701 := bbase (se 3 (by rfl) ⟨383756, by rfl⟩ : syracuseStep 2046701 = 767513) (by norm_num)
theorem B3496693 : Blo 1362500 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B2046725 : Blo 1362500 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B3275549 : Blo 1362500 3275549 := bbase (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) (by norm_num)
theorem B2046749 : Blo 1362500 2046749 := bbase (se 3 (by rfl) ⟨383765, by rfl⟩ : syracuseStep 2046749 = 767531) (by norm_num)
theorem B2300717 : Blo 1362500 2300717 := bbase (se 3 (by rfl) ⟨431384, by rfl⟩ : syracuseStep 2300717 = 862769) (by norm_num)
theorem B3111749 : Blo 1362500 3111749 := bbase (se 4 (by rfl) ⟨291726, by rfl⟩ : syracuseStep 3111749 = 583453) (by norm_num)
theorem B6216533 : Blo 1362500 6216533 := bbase (se 9 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 6216533 = 36425) (by norm_num)
theorem B1940365 : Blo 1362500 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B2300845 : Blo 1362500 2300845 := bbase (se 3 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 2300845 = 862817) (by norm_num)
theorem B4914101 : Blo 1362500 4914101 := bbase (se 5 (by rfl) ⟨230348, by rfl⟩ : syracuseStep 4914101 = 460697) (by norm_num)
theorem B2456525 : Blo 1362500 2456525 := bbase (se 3 (by rfl) ⟨460598, by rfl⟩ : syracuseStep 2456525 = 921197) (by norm_num)
theorem B5176325 : Blo 1362500 5176325 := bbase (se 4 (by rfl) ⟨485280, by rfl⟩ : syracuseStep 5176325 = 970561) (by norm_num)
theorem B2300933 : Blo 1362500 2300933 := bbase (se 4 (by rfl) ⟨215712, by rfl⟩ : syracuseStep 2300933 = 431425) (by norm_num)
theorem B2301061 : Blo 1362500 2301061 := bbase (se 4 (by rfl) ⟨215724, by rfl⟩ : syracuseStep 2301061 = 431449) (by norm_num)
theorem B4603013 : Blo 1362500 4603013 := bbase (se 4 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 4603013 = 863065) (by norm_num)
theorem B1940701 : Blo 1362500 1940701 := bbase (se 3 (by rfl) ⟨363881, by rfl⟩ : syracuseStep 1940701 = 727763) (by norm_num)
theorem B2301149 : Blo 1362500 2301149 := bbase (se 3 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 2301149 = 862931) (by norm_num)
theorem B1400101 : Blo 1362500 1400101 := bbase (se 4 (by rfl) ⟨131259, by rfl⟩ : syracuseStep 1400101 = 262519) (by norm_num)
theorem B1842485 : Blo 1362500 1842485 := bbase (se 5 (by rfl) ⟨86366, by rfl⟩ : syracuseStep 1842485 = 172733) (by norm_num)
theorem B14736725 : Blo 1362500 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B2301277 : Blo 1362500 2301277 := bbase (se 3 (by rfl) ⟨431489, by rfl⟩ : syracuseStep 2301277 = 862979) (by norm_num)
theorem B5823845 : Blo 1362500 5823845 := bbase (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) (by norm_num)
theorem B1940917 : Blo 1362500 1940917 := bbase (se 5 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 1940917 = 181961) (by norm_num)
theorem B2301365 : Blo 1362500 2301365 := bbase (se 5 (by rfl) ⟨107876, by rfl⟩ : syracuseStep 2301365 = 215753) (by norm_num)
theorem B2588125 : Blo 1362500 2588125 := bbase (se 3 (by rfl) ⟨485273, by rfl⟩ : syracuseStep 2588125 = 970547) (by norm_num)
theorem B4914677 : Blo 1362500 4914677 := bbase (se 5 (by rfl) ⟨230375, by rfl⟩ : syracuseStep 4914677 = 460751) (by norm_num)
theorem B1555957 : Blo 1362500 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B10354229 : Blo 1362500 10354229 := bbase (se 5 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 10354229 = 970709) (by norm_num)
theorem B2301493 : Blo 1362500 2301493 := bbase (se 5 (by rfl) ⟨107882, by rfl⟩ : syracuseStep 2301493 = 215765) (by norm_num)
theorem B4603445 : Blo 1362500 4603445 := bbase (se 5 (by rfl) ⟨215786, by rfl⟩ : syracuseStep 4603445 = 431573) (by norm_num)
theorem B2588269 : Blo 1362500 2588269 := bbase (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) (by norm_num)
theorem B1638029 : Blo 1362500 1638029 := bbase (se 3 (by rfl) ⟨307130, by rfl⟩ : syracuseStep 1638029 = 614261) (by norm_num)
theorem B2301581 : Blo 1362500 2301581 := bbase (se 3 (by rfl) ⟨431546, by rfl⟩ : syracuseStep 2301581 = 863093) (by norm_num)
theorem B6905573 : Blo 1362500 6905573 := bbase (se 4 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 6905573 = 1294795) (by norm_num)
theorem B2588429 : Blo 1362500 2588429 := bbase (se 3 (by rfl) ⟨485330, by rfl⟩ : syracuseStep 2588429 = 970661) (by norm_num)
theorem B2301709 : Blo 1362500 2301709 := bbase (se 3 (by rfl) ⟨431570, by rfl⟩ : syracuseStep 2301709 = 863141) (by norm_num)
theorem B1941293 : Blo 1362500 1941293 := bbase (se 3 (by rfl) ⟨363992, by rfl⟩ : syracuseStep 1941293 = 727985) (by norm_num)
theorem B2301797 : Blo 1362500 2301797 := bbase (se 4 (by rfl) ⟨215793, by rfl⟩ : syracuseStep 2301797 = 431587) (by norm_num)
theorem B1843069 : Blo 1362500 1843069 := bbase (se 3 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 1843069 = 691151) (by norm_num)
theorem B2588573 : Blo 1362500 2588573 := bbase (se 3 (by rfl) ⟨485357, by rfl⟩ : syracuseStep 2588573 = 970715) (by norm_num)
theorem B3882917 : Blo 1362500 3882917 := bbase (se 4 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 3882917 = 728047) (by norm_num)
theorem B4726757 : Blo 1362500 4726757 := bbase (se 4 (by rfl) ⟨443133, by rfl⟩ : syracuseStep 4726757 = 886267) (by norm_num)
theorem B2301925 : Blo 1362500 2301925 := bbase (se 4 (by rfl) ⟨215805, by rfl⟩ : syracuseStep 2301925 = 431611) (by norm_num)
theorem B4603877 : Blo 1362500 4603877 := bbase (se 4 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 4603877 = 863227) (by norm_num)
theorem B1400899 : Blo 1362500 1400899 := bstep (se 1 (by rfl) ⟨1050674, by rfl⟩ : syracuseStep 1400899 = 2101349) B2101349
theorem B4661329 : Blo 1362500 4661329 := bstep (se 2 (by rfl) ⟨1747998, by rfl⟩ : syracuseStep 4661329 = 3495997) B3495997
theorem B4603985 : Blo 1362500 4603985 := bstep (se 2 (by rfl) ⟨1726494, by rfl⟩ : syracuseStep 4603985 = 3452989) B3452989
theorem B2302033 : Blo 1362500 2302033 := bstep (se 2 (by rfl) ⟨863262, by rfl⟩ : syracuseStep 2302033 = 1726525) B1726525
theorem B52396145 : Blo 1362500 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B4915313 : Blo 1362500 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B2302067 : Blo 1362500 2302067 := bstep (se 1 (by rfl) ⟨1726550, by rfl⟩ : syracuseStep 2302067 = 3453101) B3453101
theorem B30286021 : Blo 1362500 30286021 := bstep (se 4 (by rfl) ⟨2839314, by rfl⟩ : syracuseStep 30286021 = 5678629) B5678629
theorem B2302195 : Blo 1362500 2302195 := bstep (se 1 (by rfl) ⟨1726646, by rfl⟩ : syracuseStep 2302195 = 3453293) B3453293
theorem B3883373 : Blo 1362500 3883373 := bstep (se 3 (by rfl) ⟨728132, by rfl⟩ : syracuseStep 3883373 = 1456265) B1456265
theorem B4366705 : Blo 1362500 4366705 := bstep (se 2 (by rfl) ⟨1637514, by rfl⟩ : syracuseStep 4366705 = 3275029) B3275029
theorem B2589059 : Blo 1362500 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B2302337 : Blo 1362500 2302337 := bstep (se 2 (by rfl) ⟨863376, by rfl⟩ : syracuseStep 2302337 = 1726753) B1726753
theorem B37806533 : Blo 1362500 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B5824973 : Blo 1362500 5824973 := bstep (se 3 (by rfl) ⟨1092182, by rfl⟩ : syracuseStep 5824973 = 2184365) B2184365
theorem B3277297 : Blo 1362500 3277297 := bstep (se 2 (by rfl) ⟨1228986, by rfl⟩ : syracuseStep 3277297 = 2457973) B2457973
theorem B2302465 : Blo 1362500 2302465 := bstep (se 2 (by rfl) ⟨863424, by rfl⟩ : syracuseStep 2302465 = 1726849) B1726849
theorem B1942051 : Blo 1362500 1942051 := bstep (se 1 (by rfl) ⟨1456538, by rfl⟩ : syracuseStep 1942051 = 2913077) B2913077
theorem B2302499 : Blo 1362500 2302499 := bstep (se 1 (by rfl) ⟨1726874, by rfl⟩ : syracuseStep 2302499 = 3453749) B3453749
theorem B3883565 : Blo 1362500 3883565 := bstep (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) B1456337
theorem B3449425 : Blo 1362500 3449425 := bstep (se 2 (by rfl) ⟨1293534, by rfl⟩ : syracuseStep 3449425 = 2587069) B2587069
theorem B4604525 : Blo 1362500 4604525 := bstep (se 3 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 4604525 = 1726697) B1726697
theorem B4366961 : Blo 1362500 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B1942147 : Blo 1362500 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B34554509 : Blo 1362500 34554509 := bstep (se 3 (by rfl) ⟨6478970, by rfl⟩ : syracuseStep 34554509 = 12957941) B12957941
theorem B2589347 : Blo 1362500 2589347 := bstep (se 1 (by rfl) ⟨1942010, by rfl⟩ : syracuseStep 2589347 = 3884021) B3884021
theorem B4604579 : Blo 1362500 4604579 := bstep (se 1 (by rfl) ⟨3453434, by rfl⟩ : syracuseStep 4604579 = 6906869) B6906869
theorem B6906545 : Blo 1362500 6906545 := bstep (se 2 (by rfl) ⟨2589954, by rfl⟩ : syracuseStep 6906545 = 5179909) B5179909
theorem B6898445 : Blo 1362500 6898445 := bstep (se 3 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 6898445 = 2586917) B2586917
theorem B29868821 : Blo 1362500 29868821 := bstep (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) B1400101
theorem B3449699 : Blo 1362500 3449699 := bstep (se 1 (by rfl) ⟨2587274, by rfl⟩ : syracuseStep 3449699 = 5174549) B5174549
theorem B3367811 : Blo 1362500 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B4604849 : Blo 1362500 4604849 := bstep (se 2 (by rfl) ⟨1726818, by rfl⟩ : syracuseStep 4604849 = 3453637) B3453637
theorem B4662257 : Blo 1362500 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B3687437 : Blo 1362500 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B1532947 : Blo 1362500 1532947 := bstep (se 1 (by rfl) ⟨1149710, by rfl⟩ : syracuseStep 1532947 = 2299421) B2299421
theorem B3449891 : Blo 1362500 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B23282801 : Blo 1362500 23282801 := bstep (se 2 (by rfl) ⟨8731050, by rfl⟩ : syracuseStep 23282801 = 17462101) B17462101
theorem B1942643 : Blo 1362500 1942643 := bstep (se 1 (by rfl) ⟨1456982, by rfl⟩ : syracuseStep 1942643 = 2913965) B2913965
theorem B3687565 : Blo 1362500 3687565 := bstep (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) B1382837
theorem B1533091 : Blo 1362500 1533091 := bstep (se 1 (by rfl) ⟨1149818, by rfl⟩ : syracuseStep 1533091 = 2299637) B2299637
theorem B5604515 : Blo 1362500 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B2622737 : Blo 1362500 2622737 := bstep (se 2 (by rfl) ⟨983526, by rfl⟩ : syracuseStep 2622737 = 1967053) B1967053
theorem B1533235 : Blo 1362500 1533235 := bstep (se 1 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 1533235 = 2299853) B2299853
theorem B3687761 : Blo 1362500 3687761 := bstep (se 2 (by rfl) ⟨1382910, by rfl⟩ : syracuseStep 3687761 = 2765821) B2765821
theorem B1533379 : Blo 1362500 1533379 := bstep (se 1 (by rfl) ⟨1150034, by rfl⟩ : syracuseStep 1533379 = 2300069) B2300069
theorem B3884557 : Blo 1362500 3884557 := bstep (se 3 (by rfl) ⟨728354, by rfl⟩ : syracuseStep 3884557 = 1456709) B1456709
theorem B14739013 : Blo 1362500 14739013 := bstep (se 4 (by rfl) ⟨1381782, by rfl⟩ : syracuseStep 14739013 = 2763565) B2763565
theorem B2590289 : Blo 1362500 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B1533523 : Blo 1362500 1533523 := bstep (se 1 (by rfl) ⟨1150142, by rfl⟩ : syracuseStep 1533523 = 2300285) B2300285
theorem B4368077 : Blo 1362500 4368077 := bstep (se 3 (by rfl) ⟨819014, by rfl⟩ : syracuseStep 4368077 = 1638029) B1638029
theorem B1533667 : Blo 1362500 1533667 := bstep (se 1 (by rfl) ⟨1150250, by rfl⟩ : syracuseStep 1533667 = 2300501) B2300501
theorem B14739185 : Blo 1362500 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B5826289 : Blo 1362500 5826289 := bstep (se 2 (by rfl) ⟨2184858, by rfl⟩ : syracuseStep 5826289 = 4369717) B4369717
theorem B3933965 : Blo 1362500 3933965 := bstep (se 3 (by rfl) ⟨737618, by rfl⟩ : syracuseStep 3933965 = 1475237) B1475237
theorem B2910001 : Blo 1362500 2910001 := bstep (se 2 (by rfl) ⟨1091250, by rfl⟩ : syracuseStep 2910001 = 2182501) B2182501
theorem B8734513 : Blo 1362500 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B1533811 : Blo 1362500 1533811 := bstep (se 1 (by rfl) ⟨1150358, by rfl⟩ : syracuseStep 1533811 = 2300717) B2300717
theorem B2074499 : Blo 1362500 2074499 := bstep (se 1 (by rfl) ⟨1555874, by rfl⟩ : syracuseStep 2074499 = 3111749) B3111749
theorem B3065777 : Blo 1362500 3065777 := bstep (se 2 (by rfl) ⟨1149666, by rfl⟩ : syracuseStep 3065777 = 2299333) B2299333
theorem B3065795 : Blo 1362500 3065795 := bstep (se 1 (by rfl) ⟨2299346, by rfl⟩ : syracuseStep 3065795 = 4598693) B4598693
theorem B3450833 : Blo 1362500 3450833 := bstep (se 2 (by rfl) ⟨1294062, by rfl⟩ : syracuseStep 3450833 = 2588125) B2588125
theorem B2074609 : Blo 1362500 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B3450883 : Blo 1362500 3450883 := bstep (se 1 (by rfl) ⟨2588162, by rfl⟩ : syracuseStep 3450883 = 5176325) B5176325
theorem B1533955 : Blo 1362500 1533955 := bstep (se 1 (by rfl) ⟨1150466, by rfl⟩ : syracuseStep 1533955 = 2300933) B2300933
theorem B7768133 : Blo 1362500 7768133 := bstep (se 4 (by rfl) ⟨728262, by rfl⟩ : syracuseStep 7768133 = 1456525) B1456525
theorem B3451025 : Blo 1362500 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B1534099 : Blo 1362500 1534099 := bstep (se 1 (by rfl) ⟨1150574, by rfl⟩ : syracuseStep 1534099 = 2301149) B2301149
theorem B7760069 : Blo 1362500 7760069 := bstep (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) B1455013
theorem B3066065 : Blo 1362500 3066065 := bstep (se 2 (by rfl) ⟨1149774, by rfl⟩ : syracuseStep 3066065 = 2299549) B2299549
theorem B3066083 : Blo 1362500 3066083 := bstep (se 1 (by rfl) ⟨2299562, by rfl⟩ : syracuseStep 3066083 = 4599125) B4599125
theorem B9824483 : Blo 1362500 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B1534243 : Blo 1362500 1534243 := bstep (se 1 (by rfl) ⟨1150682, by rfl⟩ : syracuseStep 1534243 = 2301365) B2301365
theorem B5179697 : Blo 1362500 5179697 := bstep (se 2 (by rfl) ⟨1942386, by rfl⟩ : syracuseStep 5179697 = 3884773) B3884773
theorem B1534387 : Blo 1362500 1534387 := bstep (se 1 (by rfl) ⟨1150790, by rfl⟩ : syracuseStep 1534387 = 2301581) B2301581
theorem B3066353 : Blo 1362500 3066353 := bstep (se 2 (by rfl) ⟨1149882, by rfl⟩ : syracuseStep 3066353 = 2299765) B2299765
theorem B3066371 : Blo 1362500 3066371 := bstep (se 1 (by rfl) ⟨2299778, by rfl⟩ : syracuseStep 3066371 = 4599557) B4599557
theorem B6547981 : Blo 1362500 6547981 := bstep (se 3 (by rfl) ⟨1227746, by rfl⟩ : syracuseStep 6547981 = 2455493) B2455493
theorem B2214467 : Blo 1362500 2214467 := bstep (se 1 (by rfl) ⟨1660850, by rfl⟩ : syracuseStep 2214467 = 3321701) B3321701
theorem B1534531 : Blo 1362500 1534531 := bstep (se 1 (by rfl) ⟨1150898, by rfl⟩ : syracuseStep 1534531 = 2301797) B2301797
theorem B1362515 : Blo 1362500 1362515 := bstep (se 1 (by rfl) ⟨1021886, by rfl⟩ : syracuseStep 1362515 = 2043773) B2043773
theorem B1362531 : Blo 1362500 1362531 := bstep (se 1 (by rfl) ⟨1021898, by rfl⟩ : syracuseStep 1362531 = 2043797) B2043797
theorem B1772131 : Blo 1362500 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B1362547 : Blo 1362500 1362547 := bstep (se 1 (by rfl) ⟨1021910, by rfl⟩ : syracuseStep 1362547 = 2043821) B2043821
theorem B1362563 : Blo 1362500 1362563 := bstep (se 1 (by rfl) ⟨1021922, by rfl⟩ : syracuseStep 1362563 = 2043845) B2043845
theorem B1362579 : Blo 1362500 1362579 := bstep (se 1 (by rfl) ⟨1021934, by rfl⟩ : syracuseStep 1362579 = 2043869) B2043869
theorem B1362595 : Blo 1362500 1362595 := bstep (se 1 (by rfl) ⟨1021946, by rfl⟩ : syracuseStep 1362595 = 2043893) B2043893
theorem B1362611 : Blo 1362500 1362611 := bstep (se 1 (by rfl) ⟨1021958, by rfl⟩ : syracuseStep 1362611 = 2043917) B2043917
theorem B1362627 : Blo 1362500 1362627 := bstep (se 1 (by rfl) ⟨1021970, by rfl⟩ : syracuseStep 1362627 = 2043941) B2043941
theorem B13109957 : Blo 1362500 13109957 := bstep (se 4 (by rfl) ⟨1229058, by rfl⟩ : syracuseStep 13109957 = 2458117) B2458117
theorem B4598477 : Blo 1362500 4598477 := bstep (se 3 (by rfl) ⟨862214, by rfl⟩ : syracuseStep 4598477 = 1724429) B1724429
theorem B1362643 : Blo 1362500 1362643 := bstep (se 1 (by rfl) ⟨1021982, by rfl⟩ : syracuseStep 1362643 = 2043965) B2043965
theorem B1534675 : Blo 1362500 1534675 := bstep (se 1 (by rfl) ⟨1151006, by rfl⟩ : syracuseStep 1534675 = 2302013) B2302013
theorem B1362659 : Blo 1362500 1362659 := bstep (se 1 (by rfl) ⟨1021994, by rfl⟩ : syracuseStep 1362659 = 2043989) B2043989
theorem B7768817 : Blo 1362500 7768817 := bstep (se 2 (by rfl) ⟨2913306, by rfl⟩ : syracuseStep 7768817 = 5826613) B5826613
theorem B1362675 : Blo 1362500 1362675 := bstep (se 1 (by rfl) ⟨1022006, by rfl⟩ : syracuseStep 1362675 = 2044013) B2044013
theorem B4598531 : Blo 1362500 4598531 := bstep (se 1 (by rfl) ⟨3448898, by rfl⟩ : syracuseStep 4598531 = 6897797) B6897797
theorem B1362691 : Blo 1362500 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B3066641 : Blo 1362500 3066641 := bstep (se 2 (by rfl) ⟨1149990, by rfl⟩ : syracuseStep 3066641 = 2299981) B2299981
theorem B1362707 : Blo 1362500 1362707 := bstep (se 1 (by rfl) ⟨1022030, by rfl⟩ : syracuseStep 1362707 = 2044061) B2044061
theorem B1362723 : Blo 1362500 1362723 := bstep (se 1 (by rfl) ⟨1022042, by rfl⟩ : syracuseStep 1362723 = 2044085) B2044085
theorem B3066659 : Blo 1362500 3066659 := bstep (se 1 (by rfl) ⟨2299994, by rfl⟩ : syracuseStep 3066659 = 4599989) B4599989
theorem B6548273 : Blo 1362500 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B1362739 : Blo 1362500 1362739 := bstep (se 1 (by rfl) ⟨1022054, by rfl⟩ : syracuseStep 1362739 = 2044109) B2044109
theorem B1362755 : Blo 1362500 1362755 := bstep (se 1 (by rfl) ⟨1022066, by rfl⟩ : syracuseStep 1362755 = 2044133) B2044133
theorem B1362771 : Blo 1362500 1362771 := bstep (se 1 (by rfl) ⟨1022078, by rfl⟩ : syracuseStep 1362771 = 2044157) B2044157
theorem B1362787 : Blo 1362500 1362787 := bstep (se 1 (by rfl) ⟨1022090, by rfl⟩ : syracuseStep 1362787 = 2044181) B2044181
theorem B1534819 : Blo 1362500 1534819 := bstep (se 1 (by rfl) ⟨1151114, by rfl⟩ : syracuseStep 1534819 = 2302229) B2302229
theorem B1362803 : Blo 1362500 1362803 := bstep (se 1 (by rfl) ⟨1022102, by rfl⟩ : syracuseStep 1362803 = 2044205) B2044205
theorem B1362819 : Blo 1362500 1362819 := bstep (se 1 (by rfl) ⟨1022114, by rfl⟩ : syracuseStep 1362819 = 2044229) B2044229
theorem B15534989 : Blo 1362500 15534989 := bstep (se 3 (by rfl) ⟨2912810, by rfl⟩ : syracuseStep 15534989 = 5825621) B5825621
theorem B1362835 : Blo 1362500 1362835 := bstep (se 1 (by rfl) ⟨1022126, by rfl⟩ : syracuseStep 1362835 = 2044253) B2044253
theorem B1362851 : Blo 1362500 1362851 := bstep (se 1 (by rfl) ⟨1022138, by rfl⟩ : syracuseStep 1362851 = 2044277) B2044277
theorem B1362867 : Blo 1362500 1362867 := bstep (se 1 (by rfl) ⟨1022150, by rfl⟩ : syracuseStep 1362867 = 2044301) B2044301
theorem B1362883 : Blo 1362500 1362883 := bstep (se 1 (by rfl) ⟨1022162, by rfl⟩ : syracuseStep 1362883 = 2044325) B2044325
theorem B1362899 : Blo 1362500 1362899 := bstep (se 1 (by rfl) ⟨1022174, by rfl⟩ : syracuseStep 1362899 = 2044349) B2044349
theorem B1362915 : Blo 1362500 1362915 := bstep (se 1 (by rfl) ⟨1022186, by rfl⟩ : syracuseStep 1362915 = 2044373) B2044373
theorem B1362931 : Blo 1362500 1362931 := bstep (se 1 (by rfl) ⟨1022198, by rfl⟩ : syracuseStep 1362931 = 2044397) B2044397
theorem B1534963 : Blo 1362500 1534963 := bstep (se 1 (by rfl) ⟨1151222, by rfl⟩ : syracuseStep 1534963 = 2302445) B2302445
theorem B1362947 : Blo 1362500 1362947 := bstep (se 1 (by rfl) ⟨1022210, by rfl⟩ : syracuseStep 1362947 = 2044421) B2044421
theorem B4369421 : Blo 1362500 4369421 := bstep (se 3 (by rfl) ⟨819266, by rfl⟩ : syracuseStep 4369421 = 1638533) B1638533
theorem B4598801 : Blo 1362500 4598801 := bstep (se 2 (by rfl) ⟨1724550, by rfl⟩ : syracuseStep 4598801 = 3449101) B3449101
theorem B1362963 : Blo 1362500 1362963 := bstep (se 1 (by rfl) ⟨1022222, by rfl⟩ : syracuseStep 1362963 = 2044445) B2044445
theorem B1362979 : Blo 1362500 1362979 := bstep (se 1 (by rfl) ⟨1022234, by rfl⟩ : syracuseStep 1362979 = 2044469) B2044469
theorem B3066929 : Blo 1362500 3066929 := bstep (se 2 (by rfl) ⟨1150098, by rfl⟩ : syracuseStep 3066929 = 2300197) B2300197
theorem B1362995 : Blo 1362500 1362995 := bstep (se 1 (by rfl) ⟨1022246, by rfl⟩ : syracuseStep 1362995 = 2044493) B2044493
theorem B1363011 : Blo 1362500 1363011 := bstep (se 1 (by rfl) ⟨1022258, by rfl⟩ : syracuseStep 1363011 = 2044517) B2044517
theorem B3066947 : Blo 1362500 3066947 := bstep (se 1 (by rfl) ⟨2300210, by rfl⟩ : syracuseStep 3066947 = 4600421) B4600421
theorem B1363027 : Blo 1362500 1363027 := bstep (se 1 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 1363027 = 2044541) B2044541
theorem B1363043 : Blo 1362500 1363043 := bstep (se 1 (by rfl) ⟨1022282, by rfl⟩ : syracuseStep 1363043 = 2044565) B2044565
theorem B3452017 : Blo 1362500 3452017 := bstep (se 2 (by rfl) ⟨1294506, by rfl⟩ : syracuseStep 3452017 = 2589013) B2589013
theorem B1363059 : Blo 1362500 1363059 := bstep (se 1 (by rfl) ⟨1022294, by rfl⟩ : syracuseStep 1363059 = 2044589) B2044589
theorem B1363075 : Blo 1362500 1363075 := bstep (se 1 (by rfl) ⟨1022306, by rfl⟩ : syracuseStep 1363075 = 2044613) B2044613
theorem B1363091 : Blo 1362500 1363091 := bstep (se 1 (by rfl) ⟨1022318, by rfl⟩ : syracuseStep 1363091 = 2044637) B2044637
theorem B1363107 : Blo 1362500 1363107 := bstep (se 1 (by rfl) ⟨1022330, by rfl⟩ : syracuseStep 1363107 = 2044661) B2044661
theorem B1363123 : Blo 1362500 1363123 := bstep (se 1 (by rfl) ⟨1022342, by rfl⟩ : syracuseStep 1363123 = 2044685) B2044685
theorem B1363139 : Blo 1362500 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B1363155 : Blo 1362500 1363155 := bstep (se 1 (by rfl) ⟨1022366, by rfl⟩ : syracuseStep 1363155 = 2044733) B2044733
theorem B1363171 : Blo 1362500 1363171 := bstep (se 1 (by rfl) ⟨1022378, by rfl⟩ : syracuseStep 1363171 = 2044757) B2044757
theorem B1363187 : Blo 1362500 1363187 := bstep (se 1 (by rfl) ⟨1022390, by rfl⟩ : syracuseStep 1363187 = 2044781) B2044781
theorem B1363203 : Blo 1362500 1363203 := bstep (se 1 (by rfl) ⟨1022402, by rfl⟩ : syracuseStep 1363203 = 2044805) B2044805
theorem B1363219 : Blo 1362500 1363219 := bstep (se 1 (by rfl) ⟨1022414, by rfl⟩ : syracuseStep 1363219 = 2044829) B2044829
theorem B1363235 : Blo 1362500 1363235 := bstep (se 1 (by rfl) ⟨1022426, by rfl⟩ : syracuseStep 1363235 = 2044853) B2044853
theorem B1363251 : Blo 1362500 1363251 := bstep (se 1 (by rfl) ⟨1022438, by rfl⟩ : syracuseStep 1363251 = 2044877) B2044877
theorem B1363267 : Blo 1362500 1363267 := bstep (se 1 (by rfl) ⟨1022450, by rfl⟩ : syracuseStep 1363267 = 2044901) B2044901
theorem B3067217 : Blo 1362500 3067217 := bstep (se 2 (by rfl) ⟨1150206, by rfl⟩ : syracuseStep 3067217 = 2300413) B2300413
theorem B1363283 : Blo 1362500 1363283 := bstep (se 1 (by rfl) ⟨1022462, by rfl⟩ : syracuseStep 1363283 = 2044925) B2044925
theorem B3067235 : Blo 1362500 3067235 := bstep (se 1 (by rfl) ⟨2300426, by rfl⟩ : syracuseStep 3067235 = 4600853) B4600853
theorem B1363299 : Blo 1362500 1363299 := bstep (se 1 (by rfl) ⟨1022474, by rfl⟩ : syracuseStep 1363299 = 2044949) B2044949
theorem B1363315 : Blo 1362500 1363315 := bstep (se 1 (by rfl) ⟨1022486, by rfl⟩ : syracuseStep 1363315 = 2044973) B2044973
theorem B1363331 : Blo 1362500 1363331 := bstep (se 1 (by rfl) ⟨1022498, by rfl⟩ : syracuseStep 1363331 = 2044997) B2044997
theorem B3452291 : Blo 1362500 3452291 := bstep (se 1 (by rfl) ⟨2589218, by rfl⟩ : syracuseStep 3452291 = 5178437) B5178437
theorem B1363347 : Blo 1362500 1363347 := bstep (se 1 (by rfl) ⟨1022510, by rfl⟩ : syracuseStep 1363347 = 2045021) B2045021
theorem B1363363 : Blo 1362500 1363363 := bstep (se 1 (by rfl) ⟨1022522, by rfl⟩ : syracuseStep 1363363 = 2045045) B2045045
theorem B1363379 : Blo 1362500 1363379 := bstep (se 1 (by rfl) ⟨1022534, by rfl⟩ : syracuseStep 1363379 = 2045069) B2045069
theorem B1363395 : Blo 1362500 1363395 := bstep (se 1 (by rfl) ⟨1022546, by rfl⟩ : syracuseStep 1363395 = 2045093) B2045093
theorem B4369859 : Blo 1362500 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B2182609 : Blo 1362500 2182609 := bstep (se 2 (by rfl) ⟨818478, by rfl⟩ : syracuseStep 2182609 = 1636957) B1636957
theorem B1363411 : Blo 1362500 1363411 := bstep (se 1 (by rfl) ⟨1022558, by rfl⟩ : syracuseStep 1363411 = 2045117) B2045117
theorem B1363427 : Blo 1362500 1363427 := bstep (se 1 (by rfl) ⟨1022570, by rfl⟩ : syracuseStep 1363427 = 2045141) B2045141
theorem B1363443 : Blo 1362500 1363443 := bstep (se 1 (by rfl) ⟨1022582, by rfl⟩ : syracuseStep 1363443 = 2045165) B2045165
theorem B1363459 : Blo 1362500 1363459 := bstep (se 1 (by rfl) ⟨1022594, by rfl⟩ : syracuseStep 1363459 = 2045189) B2045189
theorem B1363475 : Blo 1362500 1363475 := bstep (se 1 (by rfl) ⟨1022606, by rfl⟩ : syracuseStep 1363475 = 2045213) B2045213
theorem B1363491 : Blo 1362500 1363491 := bstep (se 1 (by rfl) ⟨1022618, by rfl⟩ : syracuseStep 1363491 = 2045237) B2045237
theorem B4599341 : Blo 1362500 4599341 := bstep (se 3 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 4599341 = 1724753) B1724753
theorem B1363507 : Blo 1362500 1363507 := bstep (se 1 (by rfl) ⟨1022630, by rfl⟩ : syracuseStep 1363507 = 2045261) B2045261
theorem B1363523 : Blo 1362500 1363523 := bstep (se 1 (by rfl) ⟨1022642, by rfl⟩ : syracuseStep 1363523 = 2045285) B2045285
theorem B3452483 : Blo 1362500 3452483 := bstep (se 1 (by rfl) ⟨2589362, by rfl⟩ : syracuseStep 3452483 = 5178725) B5178725
theorem B1363539 : Blo 1362500 1363539 := bstep (se 1 (by rfl) ⟨1022654, by rfl⟩ : syracuseStep 1363539 = 2045309) B2045309
theorem B4599395 : Blo 1362500 4599395 := bstep (se 1 (by rfl) ⟨3449546, by rfl⟩ : syracuseStep 4599395 = 6899093) B6899093
theorem B1363555 : Blo 1362500 1363555 := bstep (se 1 (by rfl) ⟨1022666, by rfl⟩ : syracuseStep 1363555 = 2045333) B2045333
theorem B6901361 : Blo 1362500 6901361 := bstep (se 2 (by rfl) ⟨2588010, by rfl⟩ : syracuseStep 6901361 = 5176021) B5176021
theorem B3067505 : Blo 1362500 3067505 := bstep (se 2 (by rfl) ⟨1150314, by rfl⟩ : syracuseStep 3067505 = 2300629) B2300629
theorem B1363571 : Blo 1362500 1363571 := bstep (se 1 (by rfl) ⟨1022678, by rfl⟩ : syracuseStep 1363571 = 2045357) B2045357
theorem B3067523 : Blo 1362500 3067523 := bstep (se 1 (by rfl) ⟨2300642, by rfl⟩ : syracuseStep 3067523 = 4601285) B4601285
theorem B1363587 : Blo 1362500 1363587 := bstep (se 1 (by rfl) ⟨1022690, by rfl⟩ : syracuseStep 1363587 = 2045381) B2045381
theorem B11062925 : Blo 1362500 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B2911889 : Blo 1362500 2911889 := bstep (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) B2183917
theorem B1363603 : Blo 1362500 1363603 := bstep (se 1 (by rfl) ⟨1022702, by rfl⟩ : syracuseStep 1363603 = 2045405) B2045405
theorem B4910755 : Blo 1362500 4910755 := bstep (se 1 (by rfl) ⟨3683066, by rfl⟩ : syracuseStep 4910755 = 7366133) B7366133
theorem B1363619 : Blo 1362500 1363619 := bstep (se 1 (by rfl) ⟨1022714, by rfl⟩ : syracuseStep 1363619 = 2045429) B2045429
theorem B1363635 : Blo 1362500 1363635 := bstep (se 1 (by rfl) ⟨1022726, by rfl⟩ : syracuseStep 1363635 = 2045453) B2045453
theorem B1363651 : Blo 1362500 1363651 := bstep (se 1 (by rfl) ⟨1022738, by rfl⟩ : syracuseStep 1363651 = 2045477) B2045477
theorem B1363667 : Blo 1362500 1363667 := bstep (se 1 (by rfl) ⟨1022750, by rfl⟩ : syracuseStep 1363667 = 2045501) B2045501
theorem B1363683 : Blo 1362500 1363683 := bstep (se 1 (by rfl) ⟨1022762, by rfl⟩ : syracuseStep 1363683 = 2045525) B2045525
theorem B1363699 : Blo 1362500 1363699 := bstep (se 1 (by rfl) ⟨1022774, by rfl⟩ : syracuseStep 1363699 = 2045549) B2045549
theorem B1363715 : Blo 1362500 1363715 := bstep (se 1 (by rfl) ⟨1022786, by rfl⟩ : syracuseStep 1363715 = 2045573) B2045573
theorem B14741261 : Blo 1362500 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B1363731 : Blo 1362500 1363731 := bstep (se 1 (by rfl) ⟨1022798, by rfl⟩ : syracuseStep 1363731 = 2045597) B2045597
theorem B1363747 : Blo 1362500 1363747 := bstep (se 1 (by rfl) ⟨1022810, by rfl⟩ : syracuseStep 1363747 = 2045621) B2045621
theorem B1363763 : Blo 1362500 1363763 := bstep (se 1 (by rfl) ⟨1022822, by rfl⟩ : syracuseStep 1363763 = 2045645) B2045645
theorem B1363779 : Blo 1362500 1363779 := bstep (se 1 (by rfl) ⟨1022834, by rfl⟩ : syracuseStep 1363779 = 2045669) B2045669
theorem B1363795 : Blo 1362500 1363795 := bstep (se 1 (by rfl) ⟨1022846, by rfl⟩ : syracuseStep 1363795 = 2045693) B2045693
theorem B1363811 : Blo 1362500 1363811 := bstep (se 1 (by rfl) ⟨1022858, by rfl⟩ : syracuseStep 1363811 = 2045717) B2045717
theorem B2043761 : Blo 1362500 2043761 := bstep (se 2 (by rfl) ⟨766410, by rfl⟩ : syracuseStep 2043761 = 1532821) B1532821
theorem B4599665 : Blo 1362500 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B1363827 : Blo 1362500 1363827 := bstep (se 1 (by rfl) ⟨1022870, by rfl⟩ : syracuseStep 1363827 = 2045741) B2045741
theorem B2043779 : Blo 1362500 2043779 := bstep (se 1 (by rfl) ⟨1532834, by rfl⟩ : syracuseStep 2043779 = 3065669) B3065669
theorem B1363843 : Blo 1362500 1363843 := bstep (se 1 (by rfl) ⟨1022882, by rfl⟩ : syracuseStep 1363843 = 2045765) B2045765
theorem B3067793 : Blo 1362500 3067793 := bstep (se 2 (by rfl) ⟨1150422, by rfl⟩ : syracuseStep 3067793 = 2300845) B2300845
theorem B1363859 : Blo 1362500 1363859 := bstep (se 1 (by rfl) ⟨1022894, by rfl⟩ : syracuseStep 1363859 = 2045789) B2045789
theorem B2043809 : Blo 1362500 2043809 := bstep (se 2 (by rfl) ⟨766428, by rfl⟩ : syracuseStep 2043809 = 1532857) B1532857
theorem B3067811 : Blo 1362500 3067811 := bstep (se 1 (by rfl) ⟨2300858, by rfl⟩ : syracuseStep 3067811 = 4601717) B4601717
theorem B1363875 : Blo 1362500 1363875 := bstep (se 1 (by rfl) ⟨1022906, by rfl⟩ : syracuseStep 1363875 = 2045813) B2045813
theorem B2043827 : Blo 1362500 2043827 := bstep (se 1 (by rfl) ⟨1532870, by rfl⟩ : syracuseStep 2043827 = 3065741) B3065741
theorem B1363891 : Blo 1362500 1363891 := bstep (se 1 (by rfl) ⟨1022918, by rfl⟩ : syracuseStep 1363891 = 2045837) B2045837
theorem B1363907 : Blo 1362500 1363907 := bstep (se 1 (by rfl) ⟨1022930, by rfl⟩ : syracuseStep 1363907 = 2045861) B2045861
theorem B2043857 : Blo 1362500 2043857 := bstep (se 2 (by rfl) ⟨766446, by rfl⟩ : syracuseStep 2043857 = 1532893) B1532893
theorem B1363923 : Blo 1362500 1363923 := bstep (se 1 (by rfl) ⟨1022942, by rfl⟩ : syracuseStep 1363923 = 2045885) B2045885
theorem B2043875 : Blo 1362500 2043875 := bstep (se 1 (by rfl) ⟨1532906, by rfl⟩ : syracuseStep 2043875 = 3065813) B3065813
theorem B1363939 : Blo 1362500 1363939 := bstep (se 1 (by rfl) ⟨1022954, by rfl⟩ : syracuseStep 1363939 = 2045909) B2045909
theorem B1363955 : Blo 1362500 1363955 := bstep (se 1 (by rfl) ⟨1022966, by rfl⟩ : syracuseStep 1363955 = 2045933) B2045933
theorem B2043905 : Blo 1362500 2043905 := bstep (se 2 (by rfl) ⟨766464, by rfl⟩ : syracuseStep 2043905 = 1532929) B1532929
theorem B1724419 : Blo 1362500 1724419 := bstep (se 1 (by rfl) ⟨1293314, by rfl⟩ : syracuseStep 1724419 = 2586629) B2586629
theorem B1363971 : Blo 1362500 1363971 := bstep (se 1 (by rfl) ⟨1022978, by rfl⟩ : syracuseStep 1363971 = 2045957) B2045957
theorem B2043923 : Blo 1362500 2043923 := bstep (se 1 (by rfl) ⟨1532942, by rfl⟩ : syracuseStep 2043923 = 3065885) B3065885
theorem B1363987 : Blo 1362500 1363987 := bstep (se 1 (by rfl) ⟨1022990, by rfl⟩ : syracuseStep 1363987 = 2045981) B2045981
theorem B1364003 : Blo 1362500 1364003 := bstep (se 1 (by rfl) ⟨1023002, by rfl⟩ : syracuseStep 1364003 = 2046005) B2046005
theorem B2043953 : Blo 1362500 2043953 := bstep (se 2 (by rfl) ⟨766482, by rfl⟩ : syracuseStep 2043953 = 1532965) B1532965
theorem B1364019 : Blo 1362500 1364019 := bstep (se 1 (by rfl) ⟨1023014, by rfl⟩ : syracuseStep 1364019 = 2046029) B2046029
theorem B2043971 : Blo 1362500 2043971 := bstep (se 1 (by rfl) ⟨1532978, by rfl⟩ : syracuseStep 2043971 = 3065957) B3065957
theorem B1364035 : Blo 1362500 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B1364051 : Blo 1362500 1364051 := bstep (se 1 (by rfl) ⟨1023038, by rfl⟩ : syracuseStep 1364051 = 2046077) B2046077
theorem B2044001 : Blo 1362500 2044001 := bstep (se 2 (by rfl) ⟨766500, by rfl⟩ : syracuseStep 2044001 = 1533001) B1533001
theorem B1364067 : Blo 1362500 1364067 := bstep (se 1 (by rfl) ⟨1023050, by rfl⟩ : syracuseStep 1364067 = 2046101) B2046101
theorem B2044019 : Blo 1362500 2044019 := bstep (se 1 (by rfl) ⟨1533014, by rfl⟩ : syracuseStep 2044019 = 3066029) B3066029
theorem B1364083 : Blo 1362500 1364083 := bstep (se 1 (by rfl) ⟨1023062, by rfl⟩ : syracuseStep 1364083 = 2046125) B2046125
theorem B1364099 : Blo 1362500 1364099 := bstep (se 1 (by rfl) ⟨1023074, by rfl⟩ : syracuseStep 1364099 = 2046149) B2046149
theorem B2044049 : Blo 1362500 2044049 := bstep (se 2 (by rfl) ⟨766518, by rfl⟩ : syracuseStep 2044049 = 1533037) B1533037
theorem B1364115 : Blo 1362500 1364115 := bstep (se 1 (by rfl) ⟨1023086, by rfl⟩ : syracuseStep 1364115 = 2046173) B2046173
theorem B2044067 : Blo 1362500 2044067 := bstep (se 1 (by rfl) ⟨1533050, by rfl⟩ : syracuseStep 2044067 = 3066101) B3066101
theorem B1364131 : Blo 1362500 1364131 := bstep (se 1 (by rfl) ⟨1023098, by rfl⟩ : syracuseStep 1364131 = 2046197) B2046197
theorem B7770275 : Blo 1362500 7770275 := bstep (se 1 (by rfl) ⟨5827706, by rfl⟩ : syracuseStep 7770275 = 11655413) B11655413
theorem B3068081 : Blo 1362500 3068081 := bstep (se 2 (by rfl) ⟨1150530, by rfl⟩ : syracuseStep 3068081 = 2301061) B2301061
theorem B1364147 : Blo 1362500 1364147 := bstep (se 1 (by rfl) ⟨1023110, by rfl⟩ : syracuseStep 1364147 = 2046221) B2046221
theorem B2044097 : Blo 1362500 2044097 := bstep (se 2 (by rfl) ⟨766536, by rfl⟩ : syracuseStep 2044097 = 1533073) B1533073
theorem B3068099 : Blo 1362500 3068099 := bstep (se 1 (by rfl) ⟨2301074, by rfl⟩ : syracuseStep 3068099 = 4602149) B4602149
theorem B1364163 : Blo 1362500 1364163 := bstep (se 1 (by rfl) ⟨1023122, by rfl⟩ : syracuseStep 1364163 = 2046245) B2046245
theorem B2044115 : Blo 1362500 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B1364179 : Blo 1362500 1364179 := bstep (se 1 (by rfl) ⟨1023134, by rfl⟩ : syracuseStep 1364179 = 2046269) B2046269
theorem B1364195 : Blo 1362500 1364195 := bstep (se 1 (by rfl) ⟨1023146, by rfl⟩ : syracuseStep 1364195 = 2046293) B2046293
theorem B2044145 : Blo 1362500 2044145 := bstep (se 2 (by rfl) ⟨766554, by rfl⟩ : syracuseStep 2044145 = 1533109) B1533109
theorem B1364211 : Blo 1362500 1364211 := bstep (se 1 (by rfl) ⟨1023158, by rfl⟩ : syracuseStep 1364211 = 2046317) B2046317
theorem B2044163 : Blo 1362500 2044163 := bstep (se 1 (by rfl) ⟨1533122, by rfl⟩ : syracuseStep 2044163 = 3066245) B3066245
theorem B1364227 : Blo 1362500 1364227 := bstep (se 1 (by rfl) ⟨1023170, by rfl⟩ : syracuseStep 1364227 = 2046341) B2046341
theorem B1364243 : Blo 1362500 1364243 := bstep (se 1 (by rfl) ⟨1023182, by rfl⟩ : syracuseStep 1364243 = 2046365) B2046365
theorem B2044193 : Blo 1362500 2044193 := bstep (se 2 (by rfl) ⟨766572, by rfl⟩ : syracuseStep 2044193 = 1533145) B1533145
theorem B1364259 : Blo 1362500 1364259 := bstep (se 1 (by rfl) ⟨1023194, by rfl⟩ : syracuseStep 1364259 = 2046389) B2046389
theorem B6820145 : Blo 1362500 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B2044211 : Blo 1362500 2044211 := bstep (se 1 (by rfl) ⟨1533158, by rfl⟩ : syracuseStep 2044211 = 3066317) B3066317
theorem B1364275 : Blo 1362500 1364275 := bstep (se 1 (by rfl) ⟨1023206, by rfl⟩ : syracuseStep 1364275 = 2046413) B2046413
theorem B1364291 : Blo 1362500 1364291 := bstep (se 1 (by rfl) ⟨1023218, by rfl⟩ : syracuseStep 1364291 = 2046437) B2046437
theorem B2044241 : Blo 1362500 2044241 := bstep (se 2 (by rfl) ⟨766590, by rfl⟩ : syracuseStep 2044241 = 1533181) B1533181
theorem B2183507 : Blo 1362500 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B1364307 : Blo 1362500 1364307 := bstep (se 1 (by rfl) ⟨1023230, by rfl⟩ : syracuseStep 1364307 = 2046461) B2046461
theorem B2044259 : Blo 1362500 2044259 := bstep (se 1 (by rfl) ⟨1533194, by rfl⟩ : syracuseStep 2044259 = 3066389) B3066389
theorem B1364323 : Blo 1362500 1364323 := bstep (se 1 (by rfl) ⟨1023242, by rfl⟩ : syracuseStep 1364323 = 2046485) B2046485
theorem B1364339 : Blo 1362500 1364339 := bstep (se 1 (by rfl) ⟨1023254, by rfl⟩ : syracuseStep 1364339 = 2046509) B2046509
theorem B2044289 : Blo 1362500 2044289 := bstep (se 2 (by rfl) ⟨766608, by rfl⟩ : syracuseStep 2044289 = 1533217) B1533217
theorem B1364355 : Blo 1362500 1364355 := bstep (se 1 (by rfl) ⟨1023266, by rfl⟩ : syracuseStep 1364355 = 2046533) B2046533
theorem B4600205 : Blo 1362500 4600205 := bstep (se 3 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 4600205 = 1725077) B1725077
theorem B2044307 : Blo 1362500 2044307 := bstep (se 1 (by rfl) ⟨1533230, by rfl⟩ : syracuseStep 2044307 = 3066461) B3066461
theorem B1364371 : Blo 1362500 1364371 := bstep (se 1 (by rfl) ⟨1023278, by rfl⟩ : syracuseStep 1364371 = 2046557) B2046557
theorem B5984675 : Blo 1362500 5984675 := bstep (se 1 (by rfl) ⟨4488506, by rfl⟩ : syracuseStep 5984675 = 8977013) B8977013
theorem B1364387 : Blo 1362500 1364387 := bstep (se 1 (by rfl) ⟨1023290, by rfl⟩ : syracuseStep 1364387 = 2046581) B2046581
theorem B2044337 : Blo 1362500 2044337 := bstep (se 2 (by rfl) ⟨766626, by rfl⟩ : syracuseStep 2044337 = 1533253) B1533253
theorem B1364403 : Blo 1362500 1364403 := bstep (se 1 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 1364403 = 2046605) B2046605
theorem B2044355 : Blo 1362500 2044355 := bstep (se 1 (by rfl) ⟨1533266, by rfl⟩ : syracuseStep 2044355 = 3066533) B3066533
theorem B4600259 : Blo 1362500 4600259 := bstep (se 1 (by rfl) ⟨3450194, by rfl⟩ : syracuseStep 4600259 = 6900389) B6900389
theorem B1364419 : Blo 1362500 1364419 := bstep (se 1 (by rfl) ⟨1023314, by rfl⟩ : syracuseStep 1364419 = 2046629) B2046629
theorem B3068369 : Blo 1362500 3068369 := bstep (se 2 (by rfl) ⟨1150638, by rfl⟩ : syracuseStep 3068369 = 2301277) B2301277
theorem B1364435 : Blo 1362500 1364435 := bstep (se 1 (by rfl) ⟨1023326, by rfl⟩ : syracuseStep 1364435 = 2046653) B2046653
theorem B2044385 : Blo 1362500 2044385 := bstep (se 2 (by rfl) ⟨766644, by rfl⟩ : syracuseStep 2044385 = 1533289) B1533289
theorem B3068387 : Blo 1362500 3068387 := bstep (se 1 (by rfl) ⟨2301290, by rfl⟩ : syracuseStep 3068387 = 4602581) B4602581
theorem B1364451 : Blo 1362500 1364451 := bstep (se 1 (by rfl) ⟨1023338, by rfl⟩ : syracuseStep 1364451 = 2046677) B2046677
theorem B3453425 : Blo 1362500 3453425 := bstep (se 2 (by rfl) ⟨1295034, by rfl⟩ : syracuseStep 3453425 = 2590069) B2590069
theorem B1724915 : Blo 1362500 1724915 := bstep (se 1 (by rfl) ⟨1293686, by rfl⟩ : syracuseStep 1724915 = 2587373) B2587373
theorem B2044403 : Blo 1362500 2044403 := bstep (se 1 (by rfl) ⟨1533302, by rfl⟩ : syracuseStep 2044403 = 3066605) B3066605
theorem B1364467 : Blo 1362500 1364467 := bstep (se 1 (by rfl) ⟨1023350, by rfl⟩ : syracuseStep 1364467 = 2046701) B2046701
theorem B1364483 : Blo 1362500 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B14750221 : Blo 1362500 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B2044433 : Blo 1362500 2044433 := bstep (se 2 (by rfl) ⟨766662, by rfl⟩ : syracuseStep 2044433 = 1533325) B1533325
theorem B2183699 : Blo 1362500 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B1364499 : Blo 1362500 1364499 := bstep (se 1 (by rfl) ⟨1023374, by rfl⟩ : syracuseStep 1364499 = 2046749) B2046749
theorem B2044451 : Blo 1362500 2044451 := bstep (se 1 (by rfl) ⟨1533338, by rfl⟩ : syracuseStep 2044451 = 3066677) B3066677
theorem B1749539 : Blo 1362500 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B3453475 : Blo 1362500 3453475 := bstep (se 1 (by rfl) ⟨2590106, by rfl⟩ : syracuseStep 3453475 = 5180213) B5180213
theorem B2044481 : Blo 1362500 2044481 := bstep (se 2 (by rfl) ⟨766680, by rfl⟩ : syracuseStep 2044481 = 1533361) B1533361
theorem B8852045 : Blo 1362500 8852045 := bstep (se 3 (by rfl) ⟨1659758, by rfl⟩ : syracuseStep 8852045 = 3319517) B3319517
theorem B2044499 : Blo 1362500 2044499 := bstep (se 1 (by rfl) ⟨1533374, by rfl⟩ : syracuseStep 2044499 = 3066749) B3066749
theorem B2044529 : Blo 1362500 2044529 := bstep (se 2 (by rfl) ⟨766698, by rfl⟩ : syracuseStep 2044529 = 1533397) B1533397
theorem B9835121 : Blo 1362500 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B2044547 : Blo 1362500 2044547 := bstep (se 1 (by rfl) ⟨1533410, by rfl⟩ : syracuseStep 2044547 = 3066821) B3066821
theorem B2044577 : Blo 1362500 2044577 := bstep (se 2 (by rfl) ⟨766716, by rfl⟩ : syracuseStep 2044577 = 1533433) B1533433
theorem B3453617 : Blo 1362500 3453617 := bstep (se 2 (by rfl) ⟨1295106, by rfl⟩ : syracuseStep 3453617 = 2590213) B2590213
theorem B2044595 : Blo 1362500 2044595 := bstep (se 1 (by rfl) ⟨1533446, by rfl⟩ : syracuseStep 2044595 = 3066893) B3066893
theorem B2044625 : Blo 1362500 2044625 := bstep (se 2 (by rfl) ⟨766734, by rfl⟩ : syracuseStep 2044625 = 1533469) B1533469
theorem B4600529 : Blo 1362500 4600529 := bstep (se 2 (by rfl) ⟨1725198, by rfl⟩ : syracuseStep 4600529 = 3450397) B3450397
theorem B2044643 : Blo 1362500 2044643 := bstep (se 1 (by rfl) ⟨1533482, by rfl⟩ : syracuseStep 2044643 = 3066965) B3066965
theorem B3068657 : Blo 1362500 3068657 := bstep (se 2 (by rfl) ⟨1150746, by rfl⟩ : syracuseStep 3068657 = 2301493) B2301493
theorem B2044673 : Blo 1362500 2044673 := bstep (se 2 (by rfl) ⟨766752, by rfl⟩ : syracuseStep 2044673 = 1533505) B1533505
theorem B3068675 : Blo 1362500 3068675 := bstep (se 1 (by rfl) ⟨2301506, by rfl⟩ : syracuseStep 3068675 = 4603013) B4603013
theorem B2044691 : Blo 1362500 2044691 := bstep (se 1 (by rfl) ⟨1533518, by rfl⟩ : syracuseStep 2044691 = 3067037) B3067037
theorem B2044721 : Blo 1362500 2044721 := bstep (se 2 (by rfl) ⟨766770, by rfl⟩ : syracuseStep 2044721 = 1533541) B1533541
theorem B2044739 : Blo 1362500 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B2044769 : Blo 1362500 2044769 := bstep (se 2 (by rfl) ⟨766788, by rfl⟩ : syracuseStep 2044769 = 1533577) B1533577
theorem B2044787 : Blo 1362500 2044787 := bstep (se 1 (by rfl) ⟨1533590, by rfl⟩ : syracuseStep 2044787 = 3067181) B3067181
theorem B34943885 : Blo 1362500 34943885 := bstep (se 3 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 34943885 = 13103957) B13103957
theorem B26227597 : Blo 1362500 26227597 := bstep (se 3 (by rfl) ⟨4917674, by rfl⟩ : syracuseStep 26227597 = 9835349) B9835349
theorem B2044817 : Blo 1362500 2044817 := bstep (se 2 (by rfl) ⟨766806, by rfl⟩ : syracuseStep 2044817 = 1533613) B1533613
theorem B2044835 : Blo 1362500 2044835 := bstep (se 1 (by rfl) ⟨1533626, by rfl⟩ : syracuseStep 2044835 = 3067253) B3067253
theorem B2913187 : Blo 1362500 2913187 := bstep (se 1 (by rfl) ⟨2184890, by rfl⟩ : syracuseStep 2913187 = 4369781) B4369781
theorem B2044865 : Blo 1362500 2044865 := bstep (se 2 (by rfl) ⟨766824, by rfl⟩ : syracuseStep 2044865 = 1533649) B1533649
theorem B2044883 : Blo 1362500 2044883 := bstep (se 1 (by rfl) ⟨1533662, by rfl⟩ : syracuseStep 2044883 = 3067325) B3067325
theorem B2044913 : Blo 1362500 2044913 := bstep (se 2 (by rfl) ⟨766842, by rfl⟩ : syracuseStep 2044913 = 1533685) B1533685
theorem B2044931 : Blo 1362500 2044931 := bstep (se 1 (by rfl) ⟨1533698, by rfl⟩ : syracuseStep 2044931 = 3067397) B3067397
theorem B3068945 : Blo 1362500 3068945 := bstep (se 2 (by rfl) ⟨1150854, by rfl⟩ : syracuseStep 3068945 = 2301709) B2301709
theorem B2044961 : Blo 1362500 2044961 := bstep (se 2 (by rfl) ⟨766860, by rfl⟩ : syracuseStep 2044961 = 1533721) B1533721
theorem B6902819 : Blo 1362500 6902819 := bstep (se 1 (by rfl) ⟨5177114, by rfl⟩ : syracuseStep 6902819 = 10354229) B10354229
theorem B3068963 : Blo 1362500 3068963 := bstep (se 1 (by rfl) ⟨2301722, by rfl⟩ : syracuseStep 3068963 = 4603445) B4603445
theorem B2044979 : Blo 1362500 2044979 := bstep (se 1 (by rfl) ⟨1533734, by rfl⟩ : syracuseStep 2044979 = 3067469) B3067469
theorem B2045009 : Blo 1362500 2045009 := bstep (se 2 (by rfl) ⟨766878, by rfl⟩ : syracuseStep 2045009 = 1533757) B1533757
theorem B2045027 : Blo 1362500 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B2045057 : Blo 1362500 2045057 := bstep (se 2 (by rfl) ⟨766896, by rfl⟩ : syracuseStep 2045057 = 1533793) B1533793
theorem B2045075 : Blo 1362500 2045075 := bstep (se 1 (by rfl) ⟨1533806, by rfl⟩ : syracuseStep 2045075 = 3067613) B3067613
theorem B3683501 : Blo 1362500 3683501 := bstep (se 3 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 3683501 = 1381313) B1381313
theorem B3273905 : Blo 1362500 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B2045105 : Blo 1362500 2045105 := bstep (se 2 (by rfl) ⟨766914, by rfl⟩ : syracuseStep 2045105 = 1533829) B1533829
theorem B1725619 : Blo 1362500 1725619 := bstep (se 1 (by rfl) ⟨1294214, by rfl⟩ : syracuseStep 1725619 = 2588429) B2588429
theorem B2045123 : Blo 1362500 2045123 := bstep (se 1 (by rfl) ⟨1533842, by rfl⟩ : syracuseStep 2045123 = 3067685) B3067685
theorem B15529157 : Blo 1362500 15529157 := bstep (se 4 (by rfl) ⟨1455858, by rfl⟩ : syracuseStep 15529157 = 2911717) B2911717
theorem B6550733 : Blo 1362500 6550733 := bstep (se 3 (by rfl) ⟨1228262, by rfl⟩ : syracuseStep 6550733 = 2456525) B2456525
theorem B2045153 : Blo 1362500 2045153 := bstep (se 2 (by rfl) ⟨766932, by rfl⟩ : syracuseStep 2045153 = 1533865) B1533865
theorem B4601069 : Blo 1362500 4601069 := bstep (se 3 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 4601069 = 1725401) B1725401
theorem B2045171 : Blo 1362500 2045171 := bstep (se 1 (by rfl) ⟨1533878, by rfl⟩ : syracuseStep 2045171 = 3067757) B3067757
theorem B2045201 : Blo 1362500 2045201 := bstep (se 2 (by rfl) ⟨766950, by rfl⟩ : syracuseStep 2045201 = 1533901) B1533901
theorem B1725715 : Blo 1362500 1725715 := bstep (se 1 (by rfl) ⟨1294286, by rfl⟩ : syracuseStep 1725715 = 2588573) B2588573
theorem B5174563 : Blo 1362500 5174563 := bstep (se 1 (by rfl) ⟨3880922, by rfl⟩ : syracuseStep 5174563 = 7761845) B7761845
theorem B4601123 : Blo 1362500 4601123 := bstep (se 1 (by rfl) ⟨3450842, by rfl⟩ : syracuseStep 4601123 = 6901685) B6901685
theorem B2045219 : Blo 1362500 2045219 := bstep (se 1 (by rfl) ⟨1533914, by rfl⟩ : syracuseStep 2045219 = 3067829) B3067829
theorem B3069233 : Blo 1362500 3069233 := bstep (se 2 (by rfl) ⟨1150962, by rfl⟩ : syracuseStep 3069233 = 2301925) B2301925
theorem B22123829 : Blo 1362500 22123829 := bstep (se 5 (by rfl) ⟨1037054, by rfl⟩ : syracuseStep 22123829 = 2074109) B2074109
theorem B2045249 : Blo 1362500 2045249 := bstep (se 2 (by rfl) ⟨766968, by rfl⟩ : syracuseStep 2045249 = 1533937) B1533937
theorem B3151171 : Blo 1362500 3151171 := bstep (se 1 (by rfl) ⟨2363378, by rfl⟩ : syracuseStep 3151171 = 4726757) B4726757
theorem B3069251 : Blo 1362500 3069251 := bstep (se 1 (by rfl) ⟨2301938, by rfl⟩ : syracuseStep 3069251 = 4603877) B4603877
theorem B2045267 : Blo 1362500 2045267 := bstep (se 1 (by rfl) ⟨1533950, by rfl⟩ : syracuseStep 2045267 = 3067901) B3067901
theorem B2045297 : Blo 1362500 2045297 := bstep (se 2 (by rfl) ⟨766986, by rfl⟩ : syracuseStep 2045297 = 1533973) B1533973
theorem B2045315 : Blo 1362500 2045315 := bstep (se 1 (by rfl) ⟨1533986, by rfl⟩ : syracuseStep 2045315 = 3067973) B3067973
theorem B2045345 : Blo 1362500 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B2299313 : Blo 1362500 2299313 := bstep (se 2 (by rfl) ⟨862242, by rfl⟩ : syracuseStep 2299313 = 1724485) B1724485
theorem B2045363 : Blo 1362500 2045363 := bstep (se 1 (by rfl) ⟨1534022, by rfl⟩ : syracuseStep 2045363 = 3068045) B3068045
theorem B2045393 : Blo 1362500 2045393 := bstep (se 2 (by rfl) ⟨767022, by rfl⟩ : syracuseStep 2045393 = 1534045) B1534045
theorem B2184673 : Blo 1362500 2184673 := bstep (se 2 (by rfl) ⟨819252, by rfl⟩ : syracuseStep 2184673 = 1638505) B1638505
theorem B2045411 : Blo 1362500 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B2045441 : Blo 1362500 2045441 := bstep (se 2 (by rfl) ⟨767040, by rfl⟩ : syracuseStep 2045441 = 1534081) B1534081
theorem B2045459 : Blo 1362500 2045459 := bstep (se 1 (by rfl) ⟨1534094, by rfl⟩ : syracuseStep 2045459 = 3068189) B3068189
theorem B2299441 : Blo 1362500 2299441 := bstep (se 2 (by rfl) ⟨862290, by rfl⟩ : syracuseStep 2299441 = 1724581) B1724581
theorem B4601393 : Blo 1362500 4601393 := bstep (se 2 (by rfl) ⟨1725522, by rfl⟩ : syracuseStep 4601393 = 3451045) B3451045
theorem B2045489 : Blo 1362500 2045489 := bstep (se 2 (by rfl) ⟨767058, by rfl⟩ : syracuseStep 2045489 = 1534117) B1534117
theorem B2045507 : Blo 1362500 2045507 := bstep (se 1 (by rfl) ⟨1534130, by rfl⟩ : syracuseStep 2045507 = 3068261) B3068261
theorem B3069521 : Blo 1362500 3069521 := bstep (se 2 (by rfl) ⟨1151070, by rfl⟩ : syracuseStep 3069521 = 2302141) B2302141
theorem B2299475 : Blo 1362500 2299475 := bstep (se 1 (by rfl) ⟨1724606, by rfl⟩ : syracuseStep 2299475 = 3449213) B3449213
theorem B2045537 : Blo 1362500 2045537 := bstep (se 2 (by rfl) ⟨767076, by rfl⟩ : syracuseStep 2045537 = 1534153) B1534153
theorem B3069539 : Blo 1362500 3069539 := bstep (se 1 (by rfl) ⟨2302154, by rfl⟩ : syracuseStep 3069539 = 4604309) B4604309
theorem B2045555 : Blo 1362500 2045555 := bstep (se 1 (by rfl) ⟨1534166, by rfl⟩ : syracuseStep 2045555 = 3068333) B3068333
theorem B4667021 : Blo 1362500 4667021 := bstep (se 3 (by rfl) ⟨875066, by rfl⟩ : syracuseStep 4667021 = 1750133) B1750133
theorem B2045585 : Blo 1362500 2045585 := bstep (se 2 (by rfl) ⟨767094, by rfl⟩ : syracuseStep 2045585 = 1534189) B1534189
theorem B2332307 : Blo 1362500 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B2045603 : Blo 1362500 2045603 := bstep (se 1 (by rfl) ⟨1534202, by rfl⟩ : syracuseStep 2045603 = 3068405) B3068405
theorem B2045633 : Blo 1362500 2045633 := bstep (se 2 (by rfl) ⟨767112, by rfl⟩ : syracuseStep 2045633 = 1534225) B1534225
theorem B2299603 : Blo 1362500 2299603 := bstep (se 1 (by rfl) ⟨1724702, by rfl⟩ : syracuseStep 2299603 = 3449405) B3449405
theorem B2045651 : Blo 1362500 2045651 := bstep (se 1 (by rfl) ⟨1534238, by rfl⟩ : syracuseStep 2045651 = 3068477) B3068477
theorem B10360547 : Blo 1362500 10360547 := bstep (se 1 (by rfl) ⟨7770410, by rfl⟩ : syracuseStep 10360547 = 15540821) B15540821
theorem B2045681 : Blo 1362500 2045681 := bstep (se 2 (by rfl) ⟨767130, by rfl⟩ : syracuseStep 2045681 = 1534261) B1534261
theorem B15537905 : Blo 1362500 15537905 := bstep (se 2 (by rfl) ⟨5826714, by rfl⟩ : syracuseStep 15537905 = 11653429) B11653429
theorem B2045699 : Blo 1362500 2045699 := bstep (se 1 (by rfl) ⟨1534274, by rfl⟩ : syracuseStep 2045699 = 3068549) B3068549
theorem B1726211 : Blo 1362500 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B2045729 : Blo 1362500 2045729 := bstep (se 2 (by rfl) ⟨767148, by rfl⟩ : syracuseStep 2045729 = 1534297) B1534297
theorem B2045747 : Blo 1362500 2045747 := bstep (se 1 (by rfl) ⟨1534310, by rfl⟩ : syracuseStep 2045747 = 3068621) B3068621
theorem B6903629 : Blo 1362500 6903629 := bstep (se 3 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 6903629 = 2588861) B2588861
theorem B2045777 : Blo 1362500 2045777 := bstep (se 2 (by rfl) ⟨767166, by rfl⟩ : syracuseStep 2045777 = 1534333) B1534333
theorem B7477069 : Blo 1362500 7477069 := bstep (se 3 (by rfl) ⟨1401950, by rfl⟩ : syracuseStep 7477069 = 2803901) B2803901
theorem B2299745 : Blo 1362500 2299745 := bstep (se 2 (by rfl) ⟨862404, by rfl⟩ : syracuseStep 2299745 = 1724809) B1724809
theorem B2332513 : Blo 1362500 2332513 := bstep (se 2 (by rfl) ⟨874692, by rfl⟩ : syracuseStep 2332513 = 1749385) B1749385
theorem B2045795 : Blo 1362500 2045795 := bstep (se 1 (by rfl) ⟨1534346, by rfl⟩ : syracuseStep 2045795 = 3068693) B3068693
theorem B3069809 : Blo 1362500 3069809 := bstep (se 2 (by rfl) ⟨1151178, by rfl⟩ : syracuseStep 3069809 = 2302357) B2302357
theorem B2045825 : Blo 1362500 2045825 := bstep (se 2 (by rfl) ⟨767184, by rfl⟩ : syracuseStep 2045825 = 1534369) B1534369
theorem B3069827 : Blo 1362500 3069827 := bstep (se 1 (by rfl) ⟨2302370, by rfl⟩ : syracuseStep 3069827 = 4604741) B4604741
theorem B2045843 : Blo 1362500 2045843 := bstep (se 1 (by rfl) ⟨1534382, by rfl⟩ : syracuseStep 2045843 = 3068765) B3068765
theorem B2185121 : Blo 1362500 2185121 := bstep (se 2 (by rfl) ⟨819420, by rfl⟩ : syracuseStep 2185121 = 1638841) B1638841
theorem B2045873 : Blo 1362500 2045873 := bstep (se 2 (by rfl) ⟨767202, by rfl⟩ : syracuseStep 2045873 = 1534405) B1534405
theorem B2045891 : Blo 1362500 2045891 := bstep (se 1 (by rfl) ⟨1534418, by rfl⟩ : syracuseStep 2045891 = 3068837) B3068837
theorem B2299873 : Blo 1362500 2299873 := bstep (se 2 (by rfl) ⟨862452, by rfl⟩ : syracuseStep 2299873 = 1724905) B1724905
theorem B2455523 : Blo 1362500 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B2045921 : Blo 1362500 2045921 := bstep (se 2 (by rfl) ⟨767220, by rfl⟩ : syracuseStep 2045921 = 1534441) B1534441
theorem B1456115 : Blo 1362500 1456115 := bstep (se 1 (by rfl) ⟨1092086, by rfl⟩ : syracuseStep 1456115 = 2184173) B2184173
theorem B2045939 : Blo 1362500 2045939 := bstep (se 1 (by rfl) ⟨1534454, by rfl⟩ : syracuseStep 2045939 = 3068909) B3068909
theorem B2299907 : Blo 1362500 2299907 := bstep (se 1 (by rfl) ⟨1724930, by rfl⟩ : syracuseStep 2299907 = 3449861) B3449861
theorem B2045969 : Blo 1362500 2045969 := bstep (se 2 (by rfl) ⟨767238, by rfl⟩ : syracuseStep 2045969 = 1534477) B1534477
theorem B2045987 : Blo 1362500 2045987 := bstep (se 1 (by rfl) ⟨1534490, by rfl⟩ : syracuseStep 2045987 = 3068981) B3068981
theorem B5822513 : Blo 1362500 5822513 := bstep (se 2 (by rfl) ⟨2183442, by rfl⟩ : syracuseStep 5822513 = 4366885) B4366885
theorem B2046017 : Blo 1362500 2046017 := bstep (se 2 (by rfl) ⟨767256, by rfl⟩ : syracuseStep 2046017 = 1534513) B1534513
theorem B4601933 : Blo 1362500 4601933 := bstep (se 3 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 4601933 = 1725725) B1725725
theorem B2046035 : Blo 1362500 2046035 := bstep (se 1 (by rfl) ⟨1534526, by rfl⟩ : syracuseStep 2046035 = 3069053) B3069053
theorem B2046065 : Blo 1362500 2046065 := bstep (se 2 (by rfl) ⟨767274, by rfl⟩ : syracuseStep 2046065 = 1534549) B1534549
theorem B2300035 : Blo 1362500 2300035 := bstep (se 1 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 2300035 = 3450053) B3450053
theorem B4601987 : Blo 1362500 4601987 := bstep (se 1 (by rfl) ⟨3451490, by rfl⟩ : syracuseStep 4601987 = 6902981) B6902981
theorem B2046083 : Blo 1362500 2046083 := bstep (se 1 (by rfl) ⟨1534562, by rfl⟩ : syracuseStep 2046083 = 3069125) B3069125
theorem B17463437 : Blo 1362500 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B4913293 : Blo 1362500 4913293 := bstep (se 3 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 4913293 = 1842485) B1842485
theorem B3881105 : Blo 1362500 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B3070097 : Blo 1362500 3070097 := bstep (se 2 (by rfl) ⟨1151286, by rfl⟩ : syracuseStep 3070097 = 2302573) B2302573
theorem B2046113 : Blo 1362500 2046113 := bstep (se 2 (by rfl) ⟨767292, by rfl⟩ : syracuseStep 2046113 = 1534585) B1534585
theorem B3070115 : Blo 1362500 3070115 := bstep (se 1 (by rfl) ⟨2302586, by rfl⟩ : syracuseStep 3070115 = 4605173) B4605173
theorem B2046131 : Blo 1362500 2046131 := bstep (se 1 (by rfl) ⟨1534598, by rfl⟩ : syracuseStep 2046131 = 3069197) B3069197
theorem B1554643 : Blo 1362500 1554643 := bstep (se 1 (by rfl) ⟨1165982, by rfl⟩ : syracuseStep 1554643 = 2331965) B2331965
theorem B2046161 : Blo 1362500 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B2046179 : Blo 1362500 2046179 := bstep (se 1 (by rfl) ⟨1534634, by rfl⟩ : syracuseStep 2046179 = 3069269) B3069269
theorem B2046209 : Blo 1362500 2046209 := bstep (se 2 (by rfl) ⟨767328, by rfl⟩ : syracuseStep 2046209 = 1534657) B1534657
theorem B2300177 : Blo 1362500 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B2046227 : Blo 1362500 2046227 := bstep (se 1 (by rfl) ⟨1534670, by rfl⟩ : syracuseStep 2046227 = 3069341) B3069341
theorem B2046257 : Blo 1362500 2046257 := bstep (se 2 (by rfl) ⟨767346, by rfl⟩ : syracuseStep 2046257 = 1534693) B1534693
theorem B2046275 : Blo 1362500 2046275 := bstep (se 1 (by rfl) ⟨1534706, by rfl⟩ : syracuseStep 2046275 = 3069413) B3069413
theorem B8730949 : Blo 1362500 8730949 := bstep (se 4 (by rfl) ⟨818526, by rfl⟩ : syracuseStep 8730949 = 1637053) B1637053
theorem B2046305 : Blo 1362500 2046305 := bstep (se 2 (by rfl) ⟨767364, by rfl⟩ : syracuseStep 2046305 = 1534729) B1534729
theorem B23607665 : Blo 1362500 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B2046323 : Blo 1362500 2046323 := bstep (se 1 (by rfl) ⟨1534742, by rfl⟩ : syracuseStep 2046323 = 3069485) B3069485
theorem B2300305 : Blo 1362500 2300305 := bstep (se 2 (by rfl) ⟨862614, by rfl⟩ : syracuseStep 2300305 = 1725229) B1725229
theorem B4602257 : Blo 1362500 4602257 := bstep (se 2 (by rfl) ⟨1725846, by rfl⟩ : syracuseStep 4602257 = 3451693) B3451693
theorem B2046353 : Blo 1362500 2046353 := bstep (se 2 (by rfl) ⟨767382, by rfl⟩ : syracuseStep 2046353 = 1534765) B1534765
theorem B2046371 : Blo 1362500 2046371 := bstep (se 1 (by rfl) ⟨1534778, by rfl⟩ : syracuseStep 2046371 = 3069557) B3069557
theorem B2300339 : Blo 1362500 2300339 := bstep (se 1 (by rfl) ⟨1725254, by rfl⟩ : syracuseStep 2300339 = 3450509) B3450509
theorem B2046401 : Blo 1362500 2046401 := bstep (se 2 (by rfl) ⟨767400, by rfl⟩ : syracuseStep 2046401 = 1534801) B1534801
theorem B1726915 : Blo 1362500 1726915 := bstep (se 1 (by rfl) ⟨1295186, by rfl⟩ : syracuseStep 1726915 = 2590373) B2590373
theorem B4430285 : Blo 1362500 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B2046419 : Blo 1362500 2046419 := bstep (se 1 (by rfl) ⟨1534814, by rfl⟩ : syracuseStep 2046419 = 3069629) B3069629
theorem B26212835 : Blo 1362500 26212835 := bstep (se 1 (by rfl) ⟨19659626, by rfl⟩ : syracuseStep 26212835 = 39319253) B39319253
theorem B2046449 : Blo 1362500 2046449 := bstep (se 2 (by rfl) ⟨767418, by rfl⟩ : syracuseStep 2046449 = 1534837) B1534837
theorem B2046467 : Blo 1362500 2046467 := bstep (se 1 (by rfl) ⟨1534850, by rfl⟩ : syracuseStep 2046467 = 3069701) B3069701
theorem B2587153 : Blo 1362500 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B2046497 : Blo 1362500 2046497 := bstep (se 2 (by rfl) ⟨767436, by rfl⟩ : syracuseStep 2046497 = 1534873) B1534873
theorem B2300467 : Blo 1362500 2300467 := bstep (se 1 (by rfl) ⟨1725350, by rfl⟩ : syracuseStep 2300467 = 3450701) B3450701
theorem B2046515 : Blo 1362500 2046515 := bstep (se 1 (by rfl) ⟨1534886, by rfl⟩ : syracuseStep 2046515 = 3069773) B3069773
theorem B2046545 : Blo 1362500 2046545 := bstep (se 2 (by rfl) ⟨767454, by rfl⟩ : syracuseStep 2046545 = 1534909) B1534909
theorem B2046563 : Blo 1362500 2046563 := bstep (se 1 (by rfl) ⟨1534922, by rfl⟩ : syracuseStep 2046563 = 3069845) B3069845
theorem B2046593 : Blo 1362500 2046593 := bstep (se 2 (by rfl) ⟨767472, by rfl⟩ : syracuseStep 2046593 = 1534945) B1534945
theorem B2046611 : Blo 1362500 2046611 := bstep (se 1 (by rfl) ⟨1534958, by rfl⟩ : syracuseStep 2046611 = 3069917) B3069917
theorem B2046641 : Blo 1362500 2046641 := bstep (se 2 (by rfl) ⟨767490, by rfl⟩ : syracuseStep 2046641 = 1534981) B1534981
theorem B2300609 : Blo 1362500 2300609 := bstep (se 2 (by rfl) ⟨862728, by rfl⟩ : syracuseStep 2300609 = 1725457) B1725457
theorem B2046659 : Blo 1362500 2046659 := bstep (se 1 (by rfl) ⟨1534994, by rfl⟩ : syracuseStep 2046659 = 3069989) B3069989
theorem B2046689 : Blo 1362500 2046689 := bstep (se 2 (by rfl) ⟨767508, by rfl⟩ : syracuseStep 2046689 = 1535017) B1535017
theorem B3275491 : Blo 1362500 3275491 := bstep (se 1 (by rfl) ⟨2456618, by rfl⟩ : syracuseStep 3275491 = 4913237) B4913237
theorem B1456867 : Blo 1362500 1456867 := bstep (se 1 (by rfl) ⟨1092650, by rfl⟩ : syracuseStep 1456867 = 2185301) B2185301
theorem B2046707 : Blo 1362500 2046707 := bstep (se 1 (by rfl) ⟨1535030, by rfl⟩ : syracuseStep 2046707 = 3070061) B3070061
theorem B2046737 : Blo 1362500 2046737 := bstep (se 2 (by rfl) ⟨767526, by rfl⟩ : syracuseStep 2046737 = 1535053) B1535053
theorem B2300737 : Blo 1362500 2300737 := bstep (se 2 (by rfl) ⟨862776, by rfl⟩ : syracuseStep 2300737 = 1725553) B1725553
theorem B2300771 : Blo 1362500 2300771 := bstep (se 1 (by rfl) ⟨1725578, by rfl⟩ : syracuseStep 2300771 = 3451157) B3451157
theorem B2841475 : Blo 1362500 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B2587555 : Blo 1362500 2587555 := bstep (se 1 (by rfl) ⟨1940666, by rfl⟩ : syracuseStep 2587555 = 3881333) B3881333
theorem B4602797 : Blo 1362500 4602797 := bstep (se 3 (by rfl) ⟨863024, by rfl⟩ : syracuseStep 4602797 = 1726049) B1726049
theorem B31562693 : Blo 1362500 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B2587601 : Blo 1362500 2587601 := bstep (se 2 (by rfl) ⟨970350, by rfl⟩ : syracuseStep 2587601 = 1940701) B1940701
theorem B2300899 : Blo 1362500 2300899 := bstep (se 1 (by rfl) ⟨1725674, by rfl⟩ : syracuseStep 2300899 = 3451349) B3451349
theorem B4602851 : Blo 1362500 4602851 := bstep (se 1 (by rfl) ⟨3452138, by rfl⟩ : syracuseStep 4602851 = 6904277) B6904277
theorem B11656163 : Blo 1362500 11656163 := bstep (se 1 (by rfl) ⟨8742122, by rfl⟩ : syracuseStep 11656163 = 17484245) B17484245
theorem B8739845 : Blo 1362500 8739845 := bstep (se 4 (by rfl) ⟨819360, by rfl⟩ : syracuseStep 8739845 = 1638721) B1638721
theorem B8854541 : Blo 1362500 8854541 := bstep (se 3 (by rfl) ⟨1660226, by rfl⟩ : syracuseStep 8854541 = 3320453) B3320453
theorem B1940593 : Blo 1362500 1940593 := bstep (se 2 (by rfl) ⟨727722, by rfl⟩ : syracuseStep 1940593 = 1455445) B1455445
theorem B2301041 : Blo 1362500 2301041 := bstep (se 2 (by rfl) ⟨862890, by rfl⟩ : syracuseStep 2301041 = 1725781) B1725781
theorem B1637491 : Blo 1362500 1637491 := bstep (se 1 (by rfl) ⟨1228118, by rfl⟩ : syracuseStep 1637491 = 2456237) B2456237
theorem B1940689 : Blo 1362500 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B4144355 : Blo 1362500 4144355 := bstep (se 1 (by rfl) ⟨3108266, by rfl⟩ : syracuseStep 4144355 = 6216533) B6216533
theorem B2587889 : Blo 1362500 2587889 := bstep (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) B1940917
theorem B2301169 : Blo 1362500 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B4603121 : Blo 1362500 4603121 := bstep (se 2 (by rfl) ⟨1726170, by rfl⟩ : syracuseStep 4603121 = 3452341) B3452341
theorem B2301203 : Blo 1362500 2301203 := bstep (se 1 (by rfl) ⟨1725902, by rfl⟩ : syracuseStep 2301203 = 3451805) B3451805
theorem B3276067 : Blo 1362500 3276067 := bstep (se 1 (by rfl) ⟨2457050, by rfl⟩ : syracuseStep 3276067 = 4914101) B4914101
theorem B4791619 : Blo 1362500 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B2301331 : Blo 1362500 2301331 := bstep (se 1 (by rfl) ⟨1725998, by rfl⟩ : syracuseStep 2301331 = 3451997) B3451997
theorem B4365731 : Blo 1362500 4365731 := bstep (se 1 (by rfl) ⟨3274298, by rfl⟩ : syracuseStep 4365731 = 6548597) B6548597
theorem B3366307 : Blo 1362500 3366307 := bstep (se 1 (by rfl) ⟨2524730, by rfl⟩ : syracuseStep 3366307 = 5049461) B5049461
theorem B5176781 : Blo 1362500 5176781 := bstep (se 3 (by rfl) ⟨970646, by rfl⟩ : syracuseStep 5176781 = 1941293) B1941293
theorem B2301473 : Blo 1362500 2301473 := bstep (se 2 (by rfl) ⟨863052, by rfl⟩ : syracuseStep 2301473 = 1726105) B1726105
theorem B3882563 : Blo 1362500 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B8289869 : Blo 1362500 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B2301601 : Blo 1362500 2301601 := bstep (se 2 (by rfl) ⟨863100, by rfl⟩ : syracuseStep 2301601 = 1726201) B1726201
theorem B3276451 : Blo 1362500 3276451 := bstep (se 1 (by rfl) ⟨2457338, by rfl⟩ : syracuseStep 3276451 = 4914677) B4914677
theorem B3784369 : Blo 1362500 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B1941185 : Blo 1362500 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B2301635 : Blo 1362500 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B4603661 : Blo 1362500 4603661 := bstep (se 3 (by rfl) ⟨863186, by rfl⟩ : syracuseStep 4603661 = 1726373) B1726373
theorem B1842961 : Blo 1362500 1842961 := bstep (se 2 (by rfl) ⟨691110, by rfl⟩ : syracuseStep 1842961 = 1382221) B1382221
theorem B2301763 : Blo 1362500 2301763 := bstep (se 1 (by rfl) ⟨1726322, by rfl⟩ : syracuseStep 2301763 = 3452645) B3452645
theorem B4603715 : Blo 1362500 4603715 := bstep (se 1 (by rfl) ⟨3452786, by rfl⟩ : syracuseStep 4603715 = 6905573) B6905573
theorem B2457425 : Blo 1362500 2457425 := bstep (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) B1843069
theorem B3686257 : Blo 1362500 3686257 := bstep (se 2 (by rfl) ⟨1382346, by rfl⟩ : syracuseStep 3686257 = 2764693) B2764693
theorem B7765901 : Blo 1362500 7765901 := bstep (se 3 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 7765901 = 2912213) B2912213
theorem B2588611 : Blo 1362500 2588611 := bstep (se 1 (by rfl) ⟨1941458, by rfl⟩ : syracuseStep 2588611 = 3882917) B3882917
theorem B2301905 : Blo 1362500 2301905 := bstep (se 2 (by rfl) ⟨863214, by rfl⟩ : syracuseStep 2301905 = 1726429) B1726429
theorem B3366883 : Blo 1362500 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B34930763 : Blo 1362500 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B3276875 : Blo 1362500 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B1867865 : Blo 1362500 1867865 := bstep (se 2 (by rfl) ⟨700449, by rfl⟩ : syracuseStep 1867865 = 1400899) B1400899
theorem B4546763 : Blo 1362500 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B2588915 : Blo 1362500 2588915 := bstep (se 1 (by rfl) ⟨1941686, by rfl⟩ : syracuseStep 2588915 = 3883373) B3883373
theorem B3989783 : Blo 1362500 3989783 := bstep (se 1 (by rfl) ⟨2992337, by rfl⟩ : syracuseStep 3989783 = 5984675) B5984675
theorem B2072857 : Blo 1362500 2072857 := bstep (se 2 (by rfl) ⟨777321, by rfl⟩ : syracuseStep 2072857 = 1554643) B1554643
theorem B3883315 : Blo 1362500 3883315 := bstep (se 1 (by rfl) ⟨2912486, by rfl⟩ : syracuseStep 3883315 = 5824973) B5824973
theorem B2302283 : Blo 1362500 2302283 := bstep (se 1 (by rfl) ⟨1726712, by rfl⟩ : syracuseStep 2302283 = 3453425) B3453425
theorem B11641265 : Blo 1362500 11641265 := bstep (se 2 (by rfl) ⟨4365474, by rfl⟩ : syracuseStep 11641265 = 8730949) B8730949
theorem B23036339 : Blo 1362500 23036339 := bstep (se 1 (by rfl) ⟨17277254, by rfl⟩ : syracuseStep 23036339 = 34554509) B34554509
theorem B4604363 : Blo 1362500 4604363 := bstep (se 1 (by rfl) ⟨3453272, by rfl⟩ : syracuseStep 4604363 = 6906545) B6906545
theorem B2302411 : Blo 1362500 2302411 := bstep (se 1 (by rfl) ⟨1726808, by rfl⟩ : syracuseStep 2302411 = 3453617) B3453617
theorem B2245207 : Blo 1362500 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B2302553 : Blo 1362500 2302553 := bstep (se 2 (by rfl) ⟨863457, by rfl⟩ : syracuseStep 2302553 = 1726915) B1726915
theorem B2458291 : Blo 1362500 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B3449537 : Blo 1362500 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B2589401 : Blo 1362500 2589401 := bstep (se 2 (by rfl) ⟨971025, by rfl⟩ : syracuseStep 2589401 = 1942051) B1942051
theorem B4604633 : Blo 1362500 4604633 := bstep (se 2 (by rfl) ⟨1726737, by rfl⟩ : syracuseStep 4604633 = 3453475) B3453475
theorem B3736343 : Blo 1362500 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B4367155 : Blo 1362500 4367155 := bstep (se 1 (by rfl) ⟨3275366, by rfl⟩ : syracuseStep 4367155 = 6550733) B6550733
theorem B2458507 : Blo 1362500 2458507 := bstep (se 1 (by rfl) ⟨1843880, by rfl⟩ : syracuseStep 2458507 = 3687761) B3687761
theorem B1532875 : Blo 1362500 1532875 := bstep (se 1 (by rfl) ⟨1149656, by rfl⟩ : syracuseStep 1532875 = 2299313) B2299313
theorem B4367321 : Blo 1362500 4367321 := bstep (se 2 (by rfl) ⟨1637745, by rfl⟩ : syracuseStep 4367321 = 3275491) B3275491
theorem B1942489 : Blo 1362500 1942489 := bstep (se 2 (by rfl) ⟨728433, by rfl⟩ : syracuseStep 1942489 = 1456867) B1456867
theorem B1532983 : Blo 1362500 1532983 := bstep (se 1 (by rfl) ⟨1149737, by rfl⟩ : syracuseStep 1532983 = 2299475) B2299475
theorem B6907031 : Blo 1362500 6907031 := bstep (se 1 (by rfl) ⟨5180273, by rfl⟩ : syracuseStep 6907031 = 10360547) B10360547
theorem B3450073 : Blo 1362500 3450073 := bstep (se 2 (by rfl) ⟨1293777, by rfl⟩ : syracuseStep 3450073 = 2587555) B2587555
theorem B3884249 : Blo 1362500 3884249 := bstep (se 2 (by rfl) ⟨1456593, by rfl⟩ : syracuseStep 3884249 = 2913187) B2913187
theorem B1533163 : Blo 1362500 1533163 := bstep (se 1 (by rfl) ⟨1149872, by rfl⟩ : syracuseStep 1533163 = 2299745) B2299745
theorem B1533271 : Blo 1362500 1533271 := bstep (se 1 (by rfl) ⟨1149953, by rfl⟩ : syracuseStep 1533271 = 2299907) B2299907
theorem B5178755 : Blo 1362500 5178755 := bstep (se 1 (by rfl) ⟨3884066, by rfl⟩ : syracuseStep 5178755 = 7768133) B7768133
theorem B11642291 : Blo 1362500 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B10356173 : Blo 1362500 10356173 := bstep (se 3 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 10356173 = 3883565) B3883565
theorem B1533451 : Blo 1362500 1533451 := bstep (se 1 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 1533451 = 2300177) B2300177
theorem B4916753 : Blo 1362500 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B15738443 : Blo 1362500 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B1533559 : Blo 1362500 1533559 := bstep (se 1 (by rfl) ⟨1150169, by rfl⟩ : syracuseStep 1533559 = 2300339) B2300339
theorem B17475223 : Blo 1362500 17475223 := bstep (se 1 (by rfl) ⟨13106417, by rfl⟩ : syracuseStep 17475223 = 26212835) B26212835
theorem B1476311 : Blo 1362500 1476311 := bstep (se 1 (by rfl) ⟨1107233, by rfl⟩ : syracuseStep 1476311 = 2214467) B2214467
theorem B6899417 : Blo 1362500 6899417 := bstep (se 2 (by rfl) ⟨2587281, by rfl⟩ : syracuseStep 6899417 = 5174563) B5174563
theorem B4368089 : Blo 1362500 4368089 := bstep (se 2 (by rfl) ⟨1638033, by rfl⟩ : syracuseStep 4368089 = 3276067) B3276067
theorem B1533739 : Blo 1362500 1533739 := bstep (se 1 (by rfl) ⟨1150304, by rfl⟩ : syracuseStep 1533739 = 2300609) B2300609
theorem B3065651 : Blo 1362500 3065651 := bstep (se 1 (by rfl) ⟨2299238, by rfl⟩ : syracuseStep 3065651 = 4598477) B4598477
theorem B5179211 : Blo 1362500 5179211 := bstep (se 1 (by rfl) ⟨3884408, by rfl⟩ : syracuseStep 5179211 = 7768817) B7768817
theorem B3065687 : Blo 1362500 3065687 := bstep (se 1 (by rfl) ⟨2299265, by rfl⟩ : syracuseStep 3065687 = 4598531) B4598531
theorem B1533847 : Blo 1362500 1533847 := bstep (se 1 (by rfl) ⟨1150385, by rfl⟩ : syracuseStep 1533847 = 2300771) B2300771
theorem B10356659 : Blo 1362500 10356659 := bstep (se 1 (by rfl) ⟨7767494, by rfl⟩ : syracuseStep 10356659 = 15534989) B15534989
theorem B5826563 : Blo 1362500 5826563 := bstep (se 1 (by rfl) ⟨4369922, by rfl⟩ : syracuseStep 5826563 = 8739845) B8739845
theorem B3065867 : Blo 1362500 3065867 := bstep (se 1 (by rfl) ⟨2299400, by rfl⟩ : syracuseStep 3065867 = 4598801) B4598801
theorem B5179409 : Blo 1362500 5179409 := bstep (se 2 (by rfl) ⟨1942278, by rfl⟩ : syracuseStep 5179409 = 3884557) B3884557
theorem B3065921 : Blo 1362500 3065921 := bstep (se 2 (by rfl) ⟨1149720, by rfl⟩ : syracuseStep 3065921 = 2299441) B2299441
theorem B1534027 : Blo 1362500 1534027 := bstep (se 1 (by rfl) ⟨1150520, by rfl⟩ : syracuseStep 1534027 = 2301041) B2301041
theorem B2762903 : Blo 1362500 2762903 := bstep (se 1 (by rfl) ⟨2072177, by rfl⟩ : syracuseStep 2762903 = 4144355) B4144355
theorem B1534135 : Blo 1362500 1534135 := bstep (se 1 (by rfl) ⟨1150601, by rfl⟩ : syracuseStep 1534135 = 2301203) B2301203
theorem B6547673 : Blo 1362500 6547673 := bstep (se 2 (by rfl) ⟨2455377, by rfl⟩ : syracuseStep 6547673 = 4910755) B4910755
theorem B4368601 : Blo 1362500 4368601 := bstep (se 2 (by rfl) ⟨1638225, by rfl⟩ : syracuseStep 4368601 = 3276451) B3276451
theorem B2910487 : Blo 1362500 2910487 := bstep (se 1 (by rfl) ⟨2182865, by rfl⟩ : syracuseStep 2910487 = 4365731) B4365731
theorem B3066137 : Blo 1362500 3066137 := bstep (se 2 (by rfl) ⟨1149801, by rfl⟩ : syracuseStep 3066137 = 2299603) B2299603
theorem B3451187 : Blo 1362500 3451187 := bstep (se 1 (by rfl) ⟨2588390, by rfl⟩ : syracuseStep 3451187 = 5176781) B5176781
theorem B7768385 : Blo 1362500 7768385 := bstep (se 2 (by rfl) ⟨2913144, by rfl⟩ : syracuseStep 7768385 = 5826289) B5826289
theorem B1534315 : Blo 1362500 1534315 := bstep (se 1 (by rfl) ⟨1150736, by rfl⟩ : syracuseStep 1534315 = 2301473) B2301473
theorem B3066227 : Blo 1362500 3066227 := bstep (se 1 (by rfl) ⟨2299670, by rfl⟩ : syracuseStep 3066227 = 4599341) B4599341
theorem B3066263 : Blo 1362500 3066263 := bstep (se 1 (by rfl) ⟨2299697, by rfl⟩ : syracuseStep 3066263 = 4599395) B4599395
theorem B7375283 : Blo 1362500 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B1534423 : Blo 1362500 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B1362507 : Blo 1362500 1362507 := bstep (se 1 (by rfl) ⟨1021880, by rfl⟩ : syracuseStep 1362507 = 2043761) B2043761
theorem B3066443 : Blo 1362500 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B1362519 : Blo 1362500 1362519 := bstep (se 1 (by rfl) ⟨1021889, by rfl⟩ : syracuseStep 1362519 = 2043779) B2043779
theorem B3451481 : Blo 1362500 3451481 := bstep (se 2 (by rfl) ⟨1294305, by rfl⟩ : syracuseStep 3451481 = 2588611) B2588611
theorem B1362539 : Blo 1362500 1362539 := bstep (se 1 (by rfl) ⟨1021904, by rfl⟩ : syracuseStep 1362539 = 2043809) B2043809
theorem B1362551 : Blo 1362500 1362551 := bstep (se 1 (by rfl) ⟨1021913, by rfl⟩ : syracuseStep 1362551 = 2043827) B2043827
theorem B3066497 : Blo 1362500 3066497 := bstep (se 2 (by rfl) ⟨1149936, by rfl⟩ : syracuseStep 3066497 = 2299873) B2299873
theorem B1362571 : Blo 1362500 1362571 := bstep (se 1 (by rfl) ⟨1021928, by rfl⟩ : syracuseStep 1362571 = 2043857) B2043857
theorem B1534603 : Blo 1362500 1534603 := bstep (se 1 (by rfl) ⟨1150952, by rfl⟩ : syracuseStep 1534603 = 2301905) B2301905
theorem B1362583 : Blo 1362500 1362583 := bstep (se 1 (by rfl) ⟨1021937, by rfl⟩ : syracuseStep 1362583 = 2043875) B2043875
theorem B1362603 : Blo 1362500 1362603 := bstep (se 1 (by rfl) ⟨1021952, by rfl⟩ : syracuseStep 1362603 = 2043905) B2043905
theorem B1362615 : Blo 1362500 1362615 := bstep (se 1 (by rfl) ⟨1021961, by rfl⟩ : syracuseStep 1362615 = 2043923) B2043923
theorem B1362635 : Blo 1362500 1362635 := bstep (se 1 (by rfl) ⟨1021976, by rfl⟩ : syracuseStep 1362635 = 2043953) B2043953
theorem B11651789 : Blo 1362500 11651789 := bstep (se 3 (by rfl) ⟨2184710, by rfl⟩ : syracuseStep 11651789 = 4369421) B4369421
theorem B1362647 : Blo 1362500 1362647 := bstep (se 1 (by rfl) ⟨1021985, by rfl⟩ : syracuseStep 1362647 = 2043971) B2043971
theorem B1362667 : Blo 1362500 1362667 := bstep (se 1 (by rfl) ⟨1022000, by rfl⟩ : syracuseStep 1362667 = 2044001) B2044001
theorem B1362679 : Blo 1362500 1362679 := bstep (se 1 (by rfl) ⟨1022009, by rfl⟩ : syracuseStep 1362679 = 2044019) B2044019
theorem B1534711 : Blo 1362500 1534711 := bstep (se 1 (by rfl) ⟨1151033, by rfl⟩ : syracuseStep 1534711 = 2302067) B2302067
theorem B1362699 : Blo 1362500 1362699 := bstep (se 1 (by rfl) ⟨1022024, by rfl⟩ : syracuseStep 1362699 = 2044049) B2044049
theorem B1362711 : Blo 1362500 1362711 := bstep (se 1 (by rfl) ⟨1022033, by rfl⟩ : syracuseStep 1362711 = 2044067) B2044067
theorem B5180183 : Blo 1362500 5180183 := bstep (se 1 (by rfl) ⟨3885137, by rfl⟩ : syracuseStep 5180183 = 7770275) B7770275
theorem B1362731 : Blo 1362500 1362731 := bstep (se 1 (by rfl) ⟨1022048, by rfl⟩ : syracuseStep 1362731 = 2044097) B2044097
theorem B1362743 : Blo 1362500 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B1362763 : Blo 1362500 1362763 := bstep (se 1 (by rfl) ⟨1022072, by rfl⟩ : syracuseStep 1362763 = 2044145) B2044145
theorem B1362775 : Blo 1362500 1362775 := bstep (se 1 (by rfl) ⟨1022081, by rfl⟩ : syracuseStep 1362775 = 2044163) B2044163
theorem B3066713 : Blo 1362500 3066713 := bstep (se 2 (by rfl) ⟨1150017, by rfl⟩ : syracuseStep 3066713 = 2300035) B2300035
theorem B1362795 : Blo 1362500 1362795 := bstep (se 1 (by rfl) ⟨1022096, by rfl⟩ : syracuseStep 1362795 = 2044193) B2044193
theorem B1362807 : Blo 1362500 1362807 := bstep (se 1 (by rfl) ⟨1022105, by rfl⟩ : syracuseStep 1362807 = 2044211) B2044211
theorem B1362827 : Blo 1362500 1362827 := bstep (se 1 (by rfl) ⟨1022120, by rfl⟩ : syracuseStep 1362827 = 2044241) B2044241
theorem B1362839 : Blo 1362500 1362839 := bstep (se 1 (by rfl) ⟨1022129, by rfl⟩ : syracuseStep 1362839 = 2044259) B2044259
theorem B1362859 : Blo 1362500 1362859 := bstep (se 1 (by rfl) ⟨1022144, by rfl⟩ : syracuseStep 1362859 = 2044289) B2044289
theorem B1534891 : Blo 1362500 1534891 := bstep (se 1 (by rfl) ⟨1151168, by rfl⟩ : syracuseStep 1534891 = 2302337) B2302337
theorem B40381361 : Blo 1362500 40381361 := bstep (se 2 (by rfl) ⟨15143010, by rfl⟩ : syracuseStep 40381361 = 30286021) B30286021
theorem B3066803 : Blo 1362500 3066803 := bstep (se 1 (by rfl) ⟨2300102, by rfl⟩ : syracuseStep 3066803 = 4600205) B4600205
theorem B1362871 : Blo 1362500 1362871 := bstep (se 1 (by rfl) ⟨1022153, by rfl⟩ : syracuseStep 1362871 = 2044307) B2044307
theorem B1362891 : Blo 1362500 1362891 := bstep (se 1 (by rfl) ⟨1022168, by rfl⟩ : syracuseStep 1362891 = 2044337) B2044337
theorem B1362903 : Blo 1362500 1362903 := bstep (se 1 (by rfl) ⟨1022177, by rfl⟩ : syracuseStep 1362903 = 2044355) B2044355
theorem B3066839 : Blo 1362500 3066839 := bstep (se 1 (by rfl) ⟨2300129, by rfl⟩ : syracuseStep 3066839 = 4600259) B4600259
theorem B5180381 : Blo 1362500 5180381 := bstep (se 3 (by rfl) ⟨971321, by rfl⟩ : syracuseStep 5180381 = 1942643) B1942643
theorem B1362923 : Blo 1362500 1362923 := bstep (se 1 (by rfl) ⟨1022192, by rfl⟩ : syracuseStep 1362923 = 2044385) B2044385
theorem B1362935 : Blo 1362500 1362935 := bstep (se 1 (by rfl) ⟨1022201, by rfl⟩ : syracuseStep 1362935 = 2044403) B2044403
theorem B1362955 : Blo 1362500 1362955 := bstep (se 1 (by rfl) ⟨1022216, by rfl⟩ : syracuseStep 1362955 = 2044433) B2044433
theorem B1362967 : Blo 1362500 1362967 := bstep (se 1 (by rfl) ⟨1022225, by rfl⟩ : syracuseStep 1362967 = 2044451) B2044451
theorem B1534999 : Blo 1362500 1534999 := bstep (se 1 (by rfl) ⟨1151249, by rfl⟩ : syracuseStep 1534999 = 2302499) B2302499
theorem B1362987 : Blo 1362500 1362987 := bstep (se 1 (by rfl) ⟨1022240, by rfl⟩ : syracuseStep 1362987 = 2044481) B2044481
theorem B1362999 : Blo 1362500 1362999 := bstep (se 1 (by rfl) ⟨1022249, by rfl⟩ : syracuseStep 1362999 = 2044499) B2044499
theorem B1363019 : Blo 1362500 1363019 := bstep (se 1 (by rfl) ⟨1022264, by rfl⟩ : syracuseStep 1363019 = 2044529) B2044529
theorem B2911307 : Blo 1362500 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B6556747 : Blo 1362500 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B1363031 : Blo 1362500 1363031 := bstep (se 1 (by rfl) ⟨1022273, by rfl⟩ : syracuseStep 1363031 = 2044547) B2044547
theorem B1363051 : Blo 1362500 1363051 := bstep (se 1 (by rfl) ⟨1022288, by rfl⟩ : syracuseStep 1363051 = 2044577) B2044577
theorem B1363063 : Blo 1362500 1363063 := bstep (se 1 (by rfl) ⟨1022297, by rfl⟩ : syracuseStep 1363063 = 2044595) B2044595
theorem B1363083 : Blo 1362500 1363083 := bstep (se 1 (by rfl) ⟨1022312, by rfl⟩ : syracuseStep 1363083 = 2044625) B2044625
theorem B3067019 : Blo 1362500 3067019 := bstep (se 1 (by rfl) ⟨2300264, by rfl⟩ : syracuseStep 3067019 = 4600529) B4600529
theorem B1363095 : Blo 1362500 1363095 := bstep (se 1 (by rfl) ⟨1022321, by rfl⟩ : syracuseStep 1363095 = 2044643) B2044643
theorem B1363115 : Blo 1362500 1363115 := bstep (se 1 (by rfl) ⟨1022336, by rfl⟩ : syracuseStep 1363115 = 2044673) B2044673
theorem B4598963 : Blo 1362500 4598963 := bstep (se 1 (by rfl) ⟨3449222, by rfl⟩ : syracuseStep 4598963 = 6898445) B6898445
theorem B1363127 : Blo 1362500 1363127 := bstep (se 1 (by rfl) ⟨1022345, by rfl⟩ : syracuseStep 1363127 = 2044691) B2044691
theorem B3067073 : Blo 1362500 3067073 := bstep (se 2 (by rfl) ⟨1150152, by rfl⟩ : syracuseStep 3067073 = 2300305) B2300305
theorem B1363147 : Blo 1362500 1363147 := bstep (se 1 (by rfl) ⟨1022360, by rfl⟩ : syracuseStep 1363147 = 2044721) B2044721
theorem B1363159 : Blo 1362500 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B1363179 : Blo 1362500 1363179 := bstep (se 1 (by rfl) ⟨1022384, by rfl⟩ : syracuseStep 1363179 = 2044769) B2044769
theorem B1363191 : Blo 1362500 1363191 := bstep (se 1 (by rfl) ⟨1022393, by rfl⟩ : syracuseStep 1363191 = 2044787) B2044787
theorem B1363211 : Blo 1362500 1363211 := bstep (se 1 (by rfl) ⟨1022408, by rfl⟩ : syracuseStep 1363211 = 2044817) B2044817
theorem B1363223 : Blo 1362500 1363223 := bstep (se 1 (by rfl) ⟨1022417, by rfl⟩ : syracuseStep 1363223 = 2044835) B2044835
theorem B1363243 : Blo 1362500 1363243 := bstep (se 1 (by rfl) ⟨1022432, by rfl⟩ : syracuseStep 1363243 = 2044865) B2044865
theorem B6901037 : Blo 1362500 6901037 := bstep (se 3 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 6901037 = 2587889) B2587889
theorem B1363255 : Blo 1362500 1363255 := bstep (se 1 (by rfl) ⟨1022441, by rfl⟩ : syracuseStep 1363255 = 2044883) B2044883
theorem B4369729 : Blo 1362500 4369729 := bstep (se 2 (by rfl) ⟨1638648, by rfl⟩ : syracuseStep 4369729 = 3277297) B3277297
theorem B1363275 : Blo 1362500 1363275 := bstep (se 1 (by rfl) ⟨1022456, by rfl⟩ : syracuseStep 1363275 = 2044913) B2044913
theorem B1363287 : Blo 1362500 1363287 := bstep (se 1 (by rfl) ⟨1022465, by rfl⟩ : syracuseStep 1363287 = 2044931) B2044931
theorem B10358117 : Blo 1362500 10358117 := bstep (se 4 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 10358117 = 1942147) B1942147
theorem B1363307 : Blo 1362500 1363307 := bstep (se 1 (by rfl) ⟨1022480, by rfl⟩ : syracuseStep 1363307 = 2044961) B2044961
theorem B1363319 : Blo 1362500 1363319 := bstep (se 1 (by rfl) ⟨1022489, by rfl⟩ : syracuseStep 1363319 = 2044979) B2044979
theorem B1363339 : Blo 1362500 1363339 := bstep (se 1 (by rfl) ⟨1022504, by rfl⟩ : syracuseStep 1363339 = 2045009) B2045009
theorem B1363351 : Blo 1362500 1363351 := bstep (se 1 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 1363351 = 2045027) B2045027
theorem B3067289 : Blo 1362500 3067289 := bstep (se 2 (by rfl) ⟨1150233, by rfl⟩ : syracuseStep 3067289 = 2300467) B2300467
theorem B1363371 : Blo 1362500 1363371 := bstep (se 1 (by rfl) ⟨1022528, by rfl⟩ : syracuseStep 1363371 = 2045057) B2045057
theorem B1363383 : Blo 1362500 1363383 := bstep (se 1 (by rfl) ⟨1022537, by rfl⟩ : syracuseStep 1363383 = 2045075) B2045075
theorem B4599233 : Blo 1362500 4599233 := bstep (se 2 (by rfl) ⟨1724712, by rfl⟩ : syracuseStep 4599233 = 3449425) B3449425
theorem B1363403 : Blo 1362500 1363403 := bstep (se 1 (by rfl) ⟨1022552, by rfl⟩ : syracuseStep 1363403 = 2045105) B2045105
theorem B1363415 : Blo 1362500 1363415 := bstep (se 1 (by rfl) ⟨1022561, by rfl⟩ : syracuseStep 1363415 = 2045123) B2045123
theorem B2362841 : Blo 1362500 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B1363435 : Blo 1362500 1363435 := bstep (se 1 (by rfl) ⟨1022576, by rfl⟩ : syracuseStep 1363435 = 2045153) B2045153
theorem B3067379 : Blo 1362500 3067379 := bstep (se 1 (by rfl) ⟨2300534, by rfl⟩ : syracuseStep 3067379 = 4601069) B4601069
theorem B1363447 : Blo 1362500 1363447 := bstep (se 1 (by rfl) ⟨1022585, by rfl⟩ : syracuseStep 1363447 = 2045171) B2045171
theorem B1363467 : Blo 1362500 1363467 := bstep (se 1 (by rfl) ⟨1022600, by rfl⟩ : syracuseStep 1363467 = 2045201) B2045201
theorem B3067415 : Blo 1362500 3067415 := bstep (se 1 (by rfl) ⟨2300561, by rfl⟩ : syracuseStep 3067415 = 4601123) B4601123
theorem B1363479 : Blo 1362500 1363479 := bstep (se 1 (by rfl) ⟨1022609, by rfl⟩ : syracuseStep 1363479 = 2045219) B2045219
theorem B14749219 : Blo 1362500 14749219 := bstep (se 1 (by rfl) ⟨11061914, by rfl⟩ : syracuseStep 14749219 = 22123829) B22123829
theorem B1363499 : Blo 1362500 1363499 := bstep (se 1 (by rfl) ⟨1022624, by rfl⟩ : syracuseStep 1363499 = 2045249) B2045249
theorem B1363511 : Blo 1362500 1363511 := bstep (se 1 (by rfl) ⟨1022633, by rfl⟩ : syracuseStep 1363511 = 2045267) B2045267
theorem B1363531 : Blo 1362500 1363531 := bstep (se 1 (by rfl) ⟨1022648, by rfl⟩ : syracuseStep 1363531 = 2045297) B2045297
theorem B1363543 : Blo 1362500 1363543 := bstep (se 1 (by rfl) ⟨1022657, by rfl⟩ : syracuseStep 1363543 = 2045315) B2045315
theorem B1363563 : Blo 1362500 1363563 := bstep (se 1 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 1363563 = 2045345) B2045345
theorem B1363575 : Blo 1362500 1363575 := bstep (se 1 (by rfl) ⟨1022681, by rfl⟩ : syracuseStep 1363575 = 2045363) B2045363
theorem B1363595 : Blo 1362500 1363595 := bstep (se 1 (by rfl) ⟨1022696, by rfl⟩ : syracuseStep 1363595 = 2045393) B2045393
theorem B1363607 : Blo 1362500 1363607 := bstep (se 1 (by rfl) ⟨1022705, by rfl⟩ : syracuseStep 1363607 = 2045411) B2045411
theorem B1363627 : Blo 1362500 1363627 := bstep (se 1 (by rfl) ⟨1022720, by rfl⟩ : syracuseStep 1363627 = 2045441) B2045441
theorem B1363639 : Blo 1362500 1363639 := bstep (se 1 (by rfl) ⟨1022729, by rfl⟩ : syracuseStep 1363639 = 2045459) B2045459
theorem B3067595 : Blo 1362500 3067595 := bstep (se 1 (by rfl) ⟨2300696, by rfl⟩ : syracuseStep 3067595 = 4601393) B4601393
theorem B1363659 : Blo 1362500 1363659 := bstep (se 1 (by rfl) ⟨1022744, by rfl⟩ : syracuseStep 1363659 = 2045489) B2045489
theorem B1363671 : Blo 1362500 1363671 := bstep (se 1 (by rfl) ⟨1022753, by rfl⟩ : syracuseStep 1363671 = 2045507) B2045507
theorem B1363691 : Blo 1362500 1363691 := bstep (se 1 (by rfl) ⟨1022768, by rfl⟩ : syracuseStep 1363691 = 2045537) B2045537
theorem B1363703 : Blo 1362500 1363703 := bstep (se 1 (by rfl) ⟨1022777, by rfl⟩ : syracuseStep 1363703 = 2045555) B2045555
theorem B3067649 : Blo 1362500 3067649 := bstep (se 2 (by rfl) ⟨1150368, by rfl⟩ : syracuseStep 3067649 = 2300737) B2300737
theorem B10350341 : Blo 1362500 10350341 := bstep (se 4 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 10350341 = 1940689) B1940689
theorem B1363723 : Blo 1362500 1363723 := bstep (se 1 (by rfl) ⟨1022792, by rfl⟩ : syracuseStep 1363723 = 2045585) B2045585
theorem B1363735 : Blo 1362500 1363735 := bstep (se 1 (by rfl) ⟨1022801, by rfl⟩ : syracuseStep 1363735 = 2045603) B2045603
theorem B1363755 : Blo 1362500 1363755 := bstep (se 1 (by rfl) ⟨1022816, by rfl⟩ : syracuseStep 1363755 = 2045633) B2045633
theorem B2912051 : Blo 1362500 2912051 := bstep (se 1 (by rfl) ⟨2184038, by rfl⟩ : syracuseStep 2912051 = 4368077) B4368077
theorem B1363767 : Blo 1362500 1363767 := bstep (se 1 (by rfl) ⟨1022825, by rfl⟩ : syracuseStep 1363767 = 2045651) B2045651
theorem B9826123 : Blo 1362500 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B1363787 : Blo 1362500 1363787 := bstep (se 1 (by rfl) ⟨1022840, by rfl⟩ : syracuseStep 1363787 = 2045681) B2045681
theorem B10358603 : Blo 1362500 10358603 := bstep (se 1 (by rfl) ⟨7768952, by rfl⟩ : syracuseStep 10358603 = 15537905) B15537905
theorem B1363799 : Blo 1362500 1363799 := bstep (se 1 (by rfl) ⟨1022849, by rfl⟩ : syracuseStep 1363799 = 2045699) B2045699
theorem B3788633 : Blo 1362500 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B1363819 : Blo 1362500 1363819 := bstep (se 1 (by rfl) ⟨1022864, by rfl⟩ : syracuseStep 1363819 = 2045729) B2045729
theorem B1363831 : Blo 1362500 1363831 := bstep (se 1 (by rfl) ⟨1022873, by rfl⟩ : syracuseStep 1363831 = 2045747) B2045747
theorem B1363851 : Blo 1362500 1363851 := bstep (se 1 (by rfl) ⟨1022888, by rfl⟩ : syracuseStep 1363851 = 2045777) B2045777
theorem B1363863 : Blo 1362500 1363863 := bstep (se 1 (by rfl) ⟨1022897, by rfl⟩ : syracuseStep 1363863 = 2045795) B2045795
theorem B1363883 : Blo 1362500 1363883 := bstep (se 1 (by rfl) ⟨1022912, by rfl⟩ : syracuseStep 1363883 = 2045825) B2045825
theorem B1363895 : Blo 1362500 1363895 := bstep (se 1 (by rfl) ⟨1022921, by rfl⟩ : syracuseStep 1363895 = 2045843) B2045843
theorem B2043851 : Blo 1362500 2043851 := bstep (se 1 (by rfl) ⟨1532888, by rfl⟩ : syracuseStep 2043851 = 3065777) B3065777
theorem B1363915 : Blo 1362500 1363915 := bstep (se 1 (by rfl) ⟨1022936, by rfl⟩ : syracuseStep 1363915 = 2045873) B2045873
theorem B2043863 : Blo 1362500 2043863 := bstep (se 1 (by rfl) ⟨1532897, by rfl⟩ : syracuseStep 2043863 = 3065795) B3065795
theorem B1363927 : Blo 1362500 1363927 := bstep (se 1 (by rfl) ⟨1022945, by rfl⟩ : syracuseStep 1363927 = 2045891) B2045891
theorem B3067865 : Blo 1362500 3067865 := bstep (se 2 (by rfl) ⟨1150449, by rfl⟩ : syracuseStep 3067865 = 2300899) B2300899
theorem B4599773 : Blo 1362500 4599773 := bstep (se 3 (by rfl) ⟨862457, by rfl⟩ : syracuseStep 4599773 = 1724915) B1724915
theorem B1363947 : Blo 1362500 1363947 := bstep (se 1 (by rfl) ⟨1022960, by rfl⟩ : syracuseStep 1363947 = 2045921) B2045921
theorem B1363959 : Blo 1362500 1363959 := bstep (se 1 (by rfl) ⟨1022969, by rfl⟩ : syracuseStep 1363959 = 2045939) B2045939
theorem B1363979 : Blo 1362500 1363979 := bstep (se 1 (by rfl) ⟨1022984, by rfl⟩ : syracuseStep 1363979 = 2045969) B2045969
theorem B1363991 : Blo 1362500 1363991 := bstep (se 1 (by rfl) ⟨1022993, by rfl⟩ : syracuseStep 1363991 = 2045987) B2045987
theorem B2043929 : Blo 1362500 2043929 := bstep (se 2 (by rfl) ⟨766473, by rfl⟩ : syracuseStep 2043929 = 1532947) B1532947
theorem B1364011 : Blo 1362500 1364011 := bstep (se 1 (by rfl) ⟨1023008, by rfl⟩ : syracuseStep 1364011 = 2046017) B2046017
theorem B3067955 : Blo 1362500 3067955 := bstep (se 1 (by rfl) ⟨2300966, by rfl⟩ : syracuseStep 3067955 = 4601933) B4601933
theorem B1364023 : Blo 1362500 1364023 := bstep (se 1 (by rfl) ⟨1023017, by rfl⟩ : syracuseStep 1364023 = 2046035) B2046035
theorem B1364043 : Blo 1362500 1364043 := bstep (se 1 (by rfl) ⟨1023032, by rfl⟩ : syracuseStep 1364043 = 2046065) B2046065
theorem B3067991 : Blo 1362500 3067991 := bstep (se 1 (by rfl) ⟨2300993, by rfl⟩ : syracuseStep 3067991 = 4601987) B4601987
theorem B1364055 : Blo 1362500 1364055 := bstep (se 1 (by rfl) ⟨1023041, by rfl⟩ : syracuseStep 1364055 = 2046083) B2046083
theorem B4665437 : Blo 1362500 4665437 := bstep (se 3 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 4665437 = 1749539) B1749539
theorem B1364075 : Blo 1362500 1364075 := bstep (se 1 (by rfl) ⟨1023056, by rfl⟩ : syracuseStep 1364075 = 2046113) B2046113
theorem B1364087 : Blo 1362500 1364087 := bstep (se 1 (by rfl) ⟨1023065, by rfl⟩ : syracuseStep 1364087 = 2046131) B2046131
theorem B5173379 : Blo 1362500 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B2044043 : Blo 1362500 2044043 := bstep (se 1 (by rfl) ⟨1533032, by rfl⟩ : syracuseStep 2044043 = 3066065) B3066065
theorem B1364107 : Blo 1362500 1364107 := bstep (se 1 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 1364107 = 2046161) B2046161
theorem B2044055 : Blo 1362500 2044055 := bstep (se 1 (by rfl) ⟨1533041, by rfl⟩ : syracuseStep 2044055 = 3066083) B3066083
theorem B6549655 : Blo 1362500 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B2183321 : Blo 1362500 2183321 := bstep (se 2 (by rfl) ⟨818745, by rfl⟩ : syracuseStep 2183321 = 1637491) B1637491
theorem B1364119 : Blo 1362500 1364119 := bstep (se 1 (by rfl) ⟨1023089, by rfl⟩ : syracuseStep 1364119 = 2046179) B2046179
theorem B1364139 : Blo 1362500 1364139 := bstep (se 1 (by rfl) ⟨1023104, by rfl⟩ : syracuseStep 1364139 = 2046209) B2046209
theorem B1364151 : Blo 1362500 1364151 := bstep (se 1 (by rfl) ⟨1023113, by rfl⟩ : syracuseStep 1364151 = 2046227) B2046227
theorem B1364171 : Blo 1362500 1364171 := bstep (se 1 (by rfl) ⟨1023128, by rfl⟩ : syracuseStep 1364171 = 2046257) B2046257
theorem B3453131 : Blo 1362500 3453131 := bstep (se 1 (by rfl) ⟨2589848, by rfl⟩ : syracuseStep 3453131 = 5179697) B5179697
theorem B23605453 : Blo 1362500 23605453 := bstep (se 3 (by rfl) ⟨4426022, by rfl⟩ : syracuseStep 23605453 = 8852045) B8852045
theorem B22106317 : Blo 1362500 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B1364183 : Blo 1362500 1364183 := bstep (se 1 (by rfl) ⟨1023137, by rfl⟩ : syracuseStep 1364183 = 2046275) B2046275
theorem B2044121 : Blo 1362500 2044121 := bstep (se 2 (by rfl) ⟨766545, by rfl⟩ : syracuseStep 2044121 = 1533091) B1533091
theorem B1364203 : Blo 1362500 1364203 := bstep (se 1 (by rfl) ⟨1023152, by rfl⟩ : syracuseStep 1364203 = 2046305) B2046305
theorem B1364215 : Blo 1362500 1364215 := bstep (se 1 (by rfl) ⟨1023161, by rfl⟩ : syracuseStep 1364215 = 2046323) B2046323
theorem B3068171 : Blo 1362500 3068171 := bstep (se 1 (by rfl) ⟨2301128, by rfl⟩ : syracuseStep 3068171 = 4602257) B4602257
theorem B1364235 : Blo 1362500 1364235 := bstep (se 1 (by rfl) ⟨1023176, by rfl⟩ : syracuseStep 1364235 = 2046353) B2046353
theorem B1364247 : Blo 1362500 1364247 := bstep (se 1 (by rfl) ⟨1023185, by rfl⟩ : syracuseStep 1364247 = 2046371) B2046371
theorem B1364267 : Blo 1362500 1364267 := bstep (se 1 (by rfl) ⟨1023200, by rfl⟩ : syracuseStep 1364267 = 2046401) B2046401
theorem B2953523 : Blo 1362500 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1364279 : Blo 1362500 1364279 := bstep (se 1 (by rfl) ⟨1023209, by rfl⟩ : syracuseStep 1364279 = 2046419) B2046419
theorem B3068225 : Blo 1362500 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B2044235 : Blo 1362500 2044235 := bstep (se 1 (by rfl) ⟨1533176, by rfl⟩ : syracuseStep 2044235 = 3066353) B3066353
theorem B1364299 : Blo 1362500 1364299 := bstep (se 1 (by rfl) ⟨1023224, by rfl⟩ : syracuseStep 1364299 = 2046449) B2046449
theorem B2044247 : Blo 1362500 2044247 := bstep (se 1 (by rfl) ⟨1533185, by rfl⟩ : syracuseStep 2044247 = 3066371) B3066371
theorem B1364311 : Blo 1362500 1364311 := bstep (se 1 (by rfl) ⟨1023233, by rfl⟩ : syracuseStep 1364311 = 2046467) B2046467
theorem B25555301 : Blo 1362500 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B1364331 : Blo 1362500 1364331 := bstep (se 1 (by rfl) ⟨1023248, by rfl⟩ : syracuseStep 1364331 = 2046497) B2046497
theorem B1364343 : Blo 1362500 1364343 := bstep (se 1 (by rfl) ⟨1023257, by rfl⟩ : syracuseStep 1364343 = 2046515) B2046515
theorem B1364363 : Blo 1362500 1364363 := bstep (se 1 (by rfl) ⟨1023272, by rfl⟩ : syracuseStep 1364363 = 2046545) B2046545
theorem B1364375 : Blo 1362500 1364375 := bstep (se 1 (by rfl) ⟨1023281, by rfl⟩ : syracuseStep 1364375 = 2046563) B2046563
theorem B2044313 : Blo 1362500 2044313 := bstep (se 2 (by rfl) ⟨766617, by rfl⟩ : syracuseStep 2044313 = 1533235) B1533235
theorem B1364395 : Blo 1362500 1364395 := bstep (se 1 (by rfl) ⟨1023296, by rfl⟩ : syracuseStep 1364395 = 2046593) B2046593
theorem B1364407 : Blo 1362500 1364407 := bstep (se 1 (by rfl) ⟨1023305, by rfl⟩ : syracuseStep 1364407 = 2046611) B2046611
theorem B1364427 : Blo 1362500 1364427 := bstep (se 1 (by rfl) ⟨1023320, by rfl⟩ : syracuseStep 1364427 = 2046641) B2046641
theorem B1364439 : Blo 1362500 1364439 := bstep (se 1 (by rfl) ⟨1023329, by rfl⟩ : syracuseStep 1364439 = 2046659) B2046659
theorem B1364459 : Blo 1362500 1364459 := bstep (se 1 (by rfl) ⟨1023344, by rfl⟩ : syracuseStep 1364459 = 2046689) B2046689
theorem B1364471 : Blo 1362500 1364471 := bstep (se 1 (by rfl) ⟨1023353, by rfl⟩ : syracuseStep 1364471 = 2046707) B2046707
theorem B2044427 : Blo 1362500 2044427 := bstep (se 1 (by rfl) ⟨1533320, by rfl⟩ : syracuseStep 2044427 = 3066641) B3066641
theorem B1364491 : Blo 1362500 1364491 := bstep (se 1 (by rfl) ⟨1023368, by rfl⟩ : syracuseStep 1364491 = 2046737) B2046737
theorem B2044439 : Blo 1362500 2044439 := bstep (se 1 (by rfl) ⟨1533329, by rfl⟩ : syracuseStep 2044439 = 3066659) B3066659
theorem B3068441 : Blo 1362500 3068441 := bstep (se 2 (by rfl) ⟨1150665, by rfl⟩ : syracuseStep 3068441 = 2301331) B2301331
theorem B2044505 : Blo 1362500 2044505 := bstep (se 2 (by rfl) ⟨766689, by rfl⟩ : syracuseStep 2044505 = 1533379) B1533379
theorem B3068531 : Blo 1362500 3068531 := bstep (se 1 (by rfl) ⟨2301398, by rfl⟩ : syracuseStep 3068531 = 4602797) B4602797
theorem B2912897 : Blo 1362500 2912897 := bstep (se 2 (by rfl) ⟨1092336, by rfl⟩ : syracuseStep 2912897 = 2184673) B2184673
theorem B21041795 : Blo 1362500 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B1725067 : Blo 1362500 1725067 := bstep (se 1 (by rfl) ⟨1293800, by rfl⟩ : syracuseStep 1725067 = 2587601) B2587601
theorem B3068567 : Blo 1362500 3068567 := bstep (se 1 (by rfl) ⟨2301425, by rfl⟩ : syracuseStep 3068567 = 4602851) B4602851
theorem B7770775 : Blo 1362500 7770775 := bstep (se 1 (by rfl) ⟨5828081, by rfl⟩ : syracuseStep 7770775 = 11656163) B11656163
theorem B5903027 : Blo 1362500 5903027 := bstep (se 1 (by rfl) ⟨4427270, by rfl⟩ : syracuseStep 5903027 = 8854541) B8854541
theorem B2044619 : Blo 1362500 2044619 := bstep (se 1 (by rfl) ⟨1533464, by rfl⟩ : syracuseStep 2044619 = 3066929) B3066929
theorem B10490573 : Blo 1362500 10490573 := bstep (se 3 (by rfl) ⟨1966982, by rfl⟩ : syracuseStep 10490573 = 3933965) B3933965
theorem B2044631 : Blo 1362500 2044631 := bstep (se 1 (by rfl) ⟨1533473, by rfl⟩ : syracuseStep 2044631 = 3066947) B3066947
theorem B2044697 : Blo 1362500 2044697 := bstep (se 2 (by rfl) ⟨766761, by rfl⟩ : syracuseStep 2044697 = 1533523) B1533523
theorem B3068747 : Blo 1362500 3068747 := bstep (se 1 (by rfl) ⟨2301560, by rfl⟩ : syracuseStep 3068747 = 4603121) B4603121
theorem B3068801 : Blo 1362500 3068801 := bstep (se 2 (by rfl) ⟨1150800, by rfl⟩ : syracuseStep 3068801 = 2301601) B2301601
theorem B2044811 : Blo 1362500 2044811 := bstep (se 1 (by rfl) ⟨1533608, by rfl⟩ : syracuseStep 2044811 = 3067217) B3067217
theorem B2044823 : Blo 1362500 2044823 := bstep (se 1 (by rfl) ⟨1533617, by rfl⟩ : syracuseStep 2044823 = 3067235) B3067235
theorem B2913239 : Blo 1362500 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B2044889 : Blo 1362500 2044889 := bstep (se 2 (by rfl) ⟨766833, by rfl⟩ : syracuseStep 2044889 = 1533667) B1533667
theorem B3880001 : Blo 1362500 3880001 := bstep (se 2 (by rfl) ⟨1455000, by rfl⟩ : syracuseStep 3880001 = 2910001) B2910001
theorem B11646017 : Blo 1362500 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B4600907 : Blo 1362500 4600907 := bstep (se 1 (by rfl) ⟨3450680, by rfl⟩ : syracuseStep 4600907 = 6901361) B6901361
theorem B2045003 : Blo 1362500 2045003 := bstep (se 1 (by rfl) ⟨1533752, by rfl⟩ : syracuseStep 2045003 = 3067505) B3067505
theorem B2045015 : Blo 1362500 2045015 := bstep (se 1 (by rfl) ⟨1533761, by rfl⟩ : syracuseStep 2045015 = 3067523) B3067523
theorem B3069017 : Blo 1362500 3069017 := bstep (se 2 (by rfl) ⟨1150881, by rfl⟩ : syracuseStep 3069017 = 2301763) B2301763
theorem B3110017 : Blo 1362500 3110017 := bstep (se 2 (by rfl) ⟨1166256, by rfl⟩ : syracuseStep 3110017 = 2332513) B2332513
theorem B2045081 : Blo 1362500 2045081 := bstep (se 2 (by rfl) ⟨766905, by rfl⟩ : syracuseStep 2045081 = 1533811) B1533811
theorem B9827507 : Blo 1362500 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B3069107 : Blo 1362500 3069107 := bstep (se 1 (by rfl) ⟨2301830, by rfl⟩ : syracuseStep 3069107 = 4603661) B4603661
theorem B3069143 : Blo 1362500 3069143 := bstep (se 1 (by rfl) ⟨2301857, by rfl⟩ : syracuseStep 3069143 = 4603715) B4603715
theorem B2045195 : Blo 1362500 2045195 := bstep (se 1 (by rfl) ⟨1533896, by rfl⟩ : syracuseStep 2045195 = 3067793) B3067793
theorem B2045207 : Blo 1362500 2045207 := bstep (se 1 (by rfl) ⟨1533905, by rfl⟩ : syracuseStep 2045207 = 3067811) B3067811
theorem B12432685 : Blo 1362500 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B2766145 : Blo 1362500 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B2299225 : Blo 1362500 2299225 := bstep (se 2 (by rfl) ⟨862209, by rfl⟩ : syracuseStep 2299225 = 1724419) B1724419
theorem B4601177 : Blo 1362500 4601177 := bstep (se 2 (by rfl) ⟨1725441, by rfl⟩ : syracuseStep 4601177 = 3450883) B3450883
theorem B2045273 : Blo 1362500 2045273 := bstep (se 2 (by rfl) ⟨766977, by rfl⟩ : syracuseStep 2045273 = 1533955) B1533955
theorem B3069323 : Blo 1362500 3069323 := bstep (se 1 (by rfl) ⟨2301992, by rfl⟩ : syracuseStep 3069323 = 4603985) B4603985
theorem B6215105 : Blo 1362500 6215105 := bstep (se 2 (by rfl) ⟨2330664, by rfl⟩ : syracuseStep 6215105 = 4661329) B4661329
theorem B3069377 : Blo 1362500 3069377 := bstep (se 2 (by rfl) ⟨1151016, by rfl⟩ : syracuseStep 3069377 = 2302033) B2302033
theorem B2045387 : Blo 1362500 2045387 := bstep (se 1 (by rfl) ⟨1534040, by rfl⟩ : syracuseStep 2045387 = 3068081) B3068081
theorem B2045399 : Blo 1362500 2045399 := bstep (se 1 (by rfl) ⟨1534049, by rfl⟩ : syracuseStep 2045399 = 3068099) B3068099
theorem B6551057 : Blo 1362500 6551057 := bstep (se 2 (by rfl) ⟨2456646, by rfl⟩ : syracuseStep 6551057 = 4913293) B4913293
theorem B2045465 : Blo 1362500 2045465 := bstep (se 2 (by rfl) ⟨767049, by rfl⟩ : syracuseStep 2045465 = 1534099) B1534099
theorem B1455671 : Blo 1362500 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B1726039 : Blo 1362500 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B25204355 : Blo 1362500 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B2045579 : Blo 1362500 2045579 := bstep (se 1 (by rfl) ⟨1534184, by rfl⟩ : syracuseStep 2045579 = 3068369) B3068369
theorem B2045591 : Blo 1362500 2045591 := bstep (se 1 (by rfl) ⟨1534193, by rfl⟩ : syracuseStep 2045591 = 3068387) B3068387
theorem B3069593 : Blo 1362500 3069593 := bstep (se 2 (by rfl) ⟨1151097, by rfl⟩ : syracuseStep 3069593 = 2302195) B2302195
theorem B2045657 : Blo 1362500 2045657 := bstep (se 2 (by rfl) ⟨767121, by rfl⟩ : syracuseStep 2045657 = 1534243) B1534243
theorem B3069683 : Blo 1362500 3069683 := bstep (se 1 (by rfl) ⟨2302262, by rfl⟩ : syracuseStep 3069683 = 4604525) B4604525
theorem B3069719 : Blo 1362500 3069719 := bstep (se 1 (by rfl) ⟨2302289, by rfl⟩ : syracuseStep 3069719 = 4604579) B4604579
theorem B8730413 : Blo 1362500 8730413 := bstep (se 3 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 8730413 = 3273905) B3273905
theorem B5822273 : Blo 1362500 5822273 := bstep (se 2 (by rfl) ⟨2183352, by rfl⟩ : syracuseStep 5822273 = 4366705) B4366705
theorem B2045771 : Blo 1362500 2045771 := bstep (se 1 (by rfl) ⟨1534328, by rfl⟩ : syracuseStep 2045771 = 3068657) B3068657
theorem B2045783 : Blo 1362500 2045783 := bstep (se 1 (by rfl) ⟨1534337, by rfl⟩ : syracuseStep 2045783 = 3068675) B3068675
theorem B19912547 : Blo 1362500 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B2299799 : Blo 1362500 2299799 := bstep (se 1 (by rfl) ⟨1724849, by rfl⟩ : syracuseStep 2299799 = 3449699) B3449699
theorem B2045849 : Blo 1362500 2045849 := bstep (se 2 (by rfl) ⟨767193, by rfl⟩ : syracuseStep 2045849 = 1534387) B1534387
theorem B23295923 : Blo 1362500 23295923 := bstep (se 1 (by rfl) ⟨17471942, by rfl⟩ : syracuseStep 23295923 = 34943885) B34943885
theorem B3069899 : Blo 1362500 3069899 := bstep (se 1 (by rfl) ⟨2302424, by rfl⟩ : syracuseStep 3069899 = 4604849) B4604849
theorem B3069953 : Blo 1362500 3069953 := bstep (se 2 (by rfl) ⟨1151232, by rfl⟩ : syracuseStep 3069953 = 2302465) B2302465
theorem B2045963 : Blo 1362500 2045963 := bstep (se 1 (by rfl) ⟨1534472, by rfl⟩ : syracuseStep 2045963 = 3068945) B3068945
theorem B8730641 : Blo 1362500 8730641 := bstep (se 2 (by rfl) ⟨3273990, by rfl⟩ : syracuseStep 8730641 = 6547981) B6547981
theorem B19666961 : Blo 1362500 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B2299927 : Blo 1362500 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B4601879 : Blo 1362500 4601879 := bstep (se 1 (by rfl) ⟨3451409, by rfl⟩ : syracuseStep 4601879 = 6902819) B6902819
theorem B2045975 : Blo 1362500 2045975 := bstep (se 1 (by rfl) ⟨1534481, by rfl⟩ : syracuseStep 2045975 = 3068963) B3068963
theorem B6993965 : Blo 1362500 6993965 := bstep (se 3 (by rfl) ⟨1311368, by rfl⟩ : syracuseStep 6993965 = 2622737) B2622737
theorem B15521867 : Blo 1362500 15521867 := bstep (se 1 (by rfl) ⟨11641400, by rfl⟩ : syracuseStep 15521867 = 23282801) B23282801
theorem B2046041 : Blo 1362500 2046041 := bstep (se 2 (by rfl) ⟨767265, by rfl⟩ : syracuseStep 2046041 = 1534531) B1534531
theorem B2455667 : Blo 1362500 2455667 := bstep (se 1 (by rfl) ⟨1841750, by rfl⟩ : syracuseStep 2455667 = 3683501) B3683501
theorem B10352771 : Blo 1362500 10352771 := bstep (se 1 (by rfl) ⟨7764578, by rfl⟩ : syracuseStep 10352771 = 15529157) B15529157
theorem B2046155 : Blo 1362500 2046155 := bstep (se 1 (by rfl) ⟨1534616, by rfl⟩ : syracuseStep 2046155 = 3069233) B3069233
theorem B2046167 : Blo 1362500 2046167 := bstep (se 1 (by rfl) ⟨1534625, by rfl⟩ : syracuseStep 2046167 = 3069251) B3069251
theorem B2046233 : Blo 1362500 2046233 := bstep (se 2 (by rfl) ⟨767337, by rfl⟩ : syracuseStep 2046233 = 1534675) B1534675
theorem B2046347 : Blo 1362500 2046347 := bstep (se 1 (by rfl) ⟨1534760, by rfl⟩ : syracuseStep 2046347 = 3069521) B3069521
theorem B1726859 : Blo 1362500 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B2046359 : Blo 1362500 2046359 := bstep (se 1 (by rfl) ⟨1534769, by rfl⟩ : syracuseStep 2046359 = 3069539) B3069539
theorem B3111347 : Blo 1362500 3111347 := bstep (se 1 (by rfl) ⟨2333510, by rfl⟩ : syracuseStep 3111347 = 4667021) B4667021
theorem B1554871 : Blo 1362500 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B2046425 : Blo 1362500 2046425 := bstep (se 2 (by rfl) ⟨767409, by rfl⟩ : syracuseStep 2046425 = 1534819) B1534819
theorem B34970129 : Blo 1362500 34970129 := bstep (se 2 (by rfl) ⟨13113798, by rfl⟩ : syracuseStep 34970129 = 26227597) B26227597
theorem B4602419 : Blo 1362500 4602419 := bstep (se 1 (by rfl) ⟨3451814, by rfl⟩ : syracuseStep 4602419 = 6903629) B6903629
theorem B2046539 : Blo 1362500 2046539 := bstep (se 1 (by rfl) ⟨1534904, by rfl⟩ : syracuseStep 2046539 = 3069809) B3069809
theorem B2046551 : Blo 1362500 2046551 := bstep (se 1 (by rfl) ⟨1534913, by rfl⟩ : syracuseStep 2046551 = 3069827) B3069827
theorem B1382999 : Blo 1362500 1382999 := bstep (se 1 (by rfl) ⟨1037249, by rfl⟩ : syracuseStep 1382999 = 2074499) B2074499
theorem B1456747 : Blo 1362500 1456747 := bstep (se 1 (by rfl) ⟨1092560, by rfl⟩ : syracuseStep 1456747 = 2185121) B2185121
theorem B2300555 : Blo 1362500 2300555 := bstep (se 1 (by rfl) ⟨1725416, by rfl⟩ : syracuseStep 2300555 = 3450833) B3450833
theorem B1637015 : Blo 1362500 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B2046617 : Blo 1362500 2046617 := bstep (se 2 (by rfl) ⟨767481, by rfl⟩ : syracuseStep 2046617 = 1534963) B1534963
theorem B3881675 : Blo 1362500 3881675 := bstep (se 1 (by rfl) ⟨2911256, by rfl⟩ : syracuseStep 3881675 = 5822513) B5822513
theorem B5823197 : Blo 1362500 5823197 := bstep (se 3 (by rfl) ⟨1091849, by rfl⟩ : syracuseStep 5823197 = 2183699) B2183699
theorem B2587403 : Blo 1362500 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B2300683 : Blo 1362500 2300683 := bstep (se 1 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 2300683 = 3451025) B3451025
theorem B2046731 : Blo 1362500 2046731 := bstep (se 1 (by rfl) ⟨1535048, by rfl⟩ : syracuseStep 2046731 = 3070097) B3070097
theorem B2046743 : Blo 1362500 2046743 := bstep (se 1 (by rfl) ⟨1535057, by rfl⟩ : syracuseStep 2046743 = 3070115) B3070115
theorem B2587457 : Blo 1362500 2587457 := bstep (se 2 (by rfl) ⟨970296, by rfl⟩ : syracuseStep 2587457 = 1940593) B1940593
theorem B4602689 : Blo 1362500 4602689 := bstep (se 2 (by rfl) ⟨1726008, by rfl⟩ : syracuseStep 4602689 = 3452017) B3452017
theorem B2300825 : Blo 1362500 2300825 := bstep (se 2 (by rfl) ⟨862809, by rfl⟩ : syracuseStep 2300825 = 1725619) B1725619
theorem B2300953 : Blo 1362500 2300953 := bstep (se 2 (by rfl) ⟨862857, by rfl⟩ : syracuseStep 2300953 = 1725715) B1725715
theorem B4201561 : Blo 1362500 4201561 := bstep (se 2 (by rfl) ⟨1575585, by rfl⟩ : syracuseStep 4201561 = 3151171) B3151171
theorem B6904925 : Blo 1362500 6904925 := bstep (se 3 (by rfl) ⟨1294673, by rfl⟩ : syracuseStep 6904925 = 2589347) B2589347
theorem B8739971 : Blo 1362500 8739971 := bstep (se 1 (by rfl) ⟨6554978, by rfl⟩ : syracuseStep 8739971 = 13109957) B13109957
theorem B5176493 : Blo 1362500 5176493 := bstep (se 3 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 5176493 = 1941185) B1941185
theorem B4365515 : Blo 1362500 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B4488409 : Blo 1362500 4488409 := bstep (se 2 (by rfl) ⟨1683153, by rfl⟩ : syracuseStep 4488409 = 3366307) B3366307
theorem B4603229 : Blo 1362500 4603229 := bstep (se 3 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 4603229 = 1726211) B1726211
theorem B19652017 : Blo 1362500 19652017 := bstep (se 2 (by rfl) ⟨7369506, by rfl⟩ : syracuseStep 19652017 = 14739013) B14739013
theorem B6553133 : Blo 1362500 6553133 := bstep (se 3 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 6553133 = 2457425) B2457425
theorem B5045825 : Blo 1362500 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B2301527 : Blo 1362500 2301527 := bstep (se 1 (by rfl) ⟨1726145, by rfl⟩ : syracuseStep 2301527 = 3452291) B3452291
theorem B2457281 : Blo 1362500 2457281 := bstep (se 2 (by rfl) ⟨921480, by rfl⟩ : syracuseStep 2457281 = 1842961) B1842961
theorem B2588375 : Blo 1362500 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B2301655 : Blo 1362500 2301655 := bstep (se 1 (by rfl) ⟨1726241, by rfl⟩ : syracuseStep 2301655 = 3452483) B3452483
theorem B11640581 : Blo 1362500 11640581 := bstep (se 4 (by rfl) ⟨1091304, by rfl⟩ : syracuseStep 11640581 = 2182609) B2182609
theorem B1941259 : Blo 1362500 1941259 := bstep (se 1 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 1941259 = 2911889) B2911889
theorem B9969425 : Blo 1362500 9969425 := bstep (se 2 (by rfl) ⟨3738534, by rfl⟩ : syracuseStep 9969425 = 7477069) B7477069
theorem B4915009 : Blo 1362500 4915009 := bstep (se 2 (by rfl) ⟨1843128, by rfl⟩ : syracuseStep 4915009 = 3686257) B3686257
theorem B5177267 : Blo 1362500 5177267 := bstep (se 1 (by rfl) ⟨3882950, by rfl⟩ : syracuseStep 5177267 = 7765901) B7765901
theorem B4489177 : Blo 1362500 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B3882973 : Blo 1362500 3882973 := bstep (se 3 (by rfl) ⟨728057, by rfl⟩ : syracuseStep 3882973 = 1456115) B1456115
theorem B3448919 : Blo 1362500 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B3031175 : Blo 1362500 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B2302087 : Blo 1362500 2302087 := bstep (se 1 (by rfl) ⟨1726565, by rfl⟩ : syracuseStep 2302087 = 3453131) B3453131
theorem B8732873 : Blo 1362500 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B4980973 : Blo 1362500 4980973 := bstep (se 3 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 4980973 = 1867865) B1867865
theorem B31473937 : Blo 1362500 31473937 := bstep (se 2 (by rfl) ⟨11802726, by rfl⟩ : syracuseStep 31473937 = 23605453) B23605453
theorem B29475089 : Blo 1362500 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B5824801 : Blo 1362500 5824801 := bstep (se 2 (by rfl) ⟨2184300, by rfl⟩ : syracuseStep 5824801 = 4368601) B4368601
theorem B5177753 : Blo 1362500 5177753 := bstep (se 2 (by rfl) ⟨1941657, by rfl⟩ : syracuseStep 5177753 = 3883315) B3883315
theorem B1941931 : Blo 1362500 1941931 := bstep (se 1 (by rfl) ⟨1456448, by rfl⟩ : syracuseStep 1941931 = 2912897) B2912897
theorem B26206685 : Blo 1362500 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B2490895 : Blo 1362500 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B2073161 : Blo 1362500 2073161 := bstep (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) B1554871
theorem B1942159 : Blo 1362500 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B4604687 : Blo 1362500 4604687 := bstep (se 1 (by rfl) ⟨3453515, by rfl⟩ : syracuseStep 4604687 = 6907031) B6907031
theorem B2589499 : Blo 1362500 2589499 := bstep (se 1 (by rfl) ⟨1942124, by rfl⟩ : syracuseStep 2589499 = 3884249) B3884249
theorem B3277721 : Blo 1362500 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B4367371 : Blo 1362500 4367371 := bstep (se 1 (by rfl) ⟨3275528, by rfl⟩ : syracuseStep 4367371 = 6551057) B6551057
theorem B3277835 : Blo 1362500 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B4604957 : Blo 1362500 4604957 := bstep (se 3 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 4604957 = 1726859) B1726859
theorem B16802903 : Blo 1362500 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B3278009 : Blo 1362500 3278009 := bstep (se 2 (by rfl) ⟨1229253, by rfl⟩ : syracuseStep 3278009 = 2458507) B2458507
theorem B1533199 : Blo 1362500 1533199 := bstep (se 1 (by rfl) ⟨1149899, by rfl⟩ : syracuseStep 1533199 = 2299799) B2299799
theorem B2589985 : Blo 1362500 2589985 := bstep (se 2 (by rfl) ⟨971244, by rfl⟩ : syracuseStep 2589985 = 1942489) B1942489
theorem B3884375 : Blo 1362500 3884375 := bstep (se 1 (by rfl) ⟨2913281, by rfl⟩ : syracuseStep 3884375 = 5826563) B5826563
theorem B4662643 : Blo 1362500 4662643 := bstep (se 1 (by rfl) ⟨3496982, by rfl⟩ : syracuseStep 4662643 = 6993965) B6993965
theorem B10347911 : Blo 1362500 10347911 := bstep (se 1 (by rfl) ⟨7760933, by rfl⟩ : syracuseStep 10347911 = 15521867) B15521867
theorem B8742329 : Blo 1362500 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B4146689 : Blo 1362500 4146689 := bstep (se 2 (by rfl) ⟨1555008, by rfl⟩ : syracuseStep 4146689 = 3110017) B3110017
theorem B5178923 : Blo 1362500 5178923 := bstep (se 1 (by rfl) ⟨3884192, by rfl⟩ : syracuseStep 5178923 = 7768385) B7768385
theorem B2074231 : Blo 1362500 2074231 := bstep (se 1 (by rfl) ⟨1555673, by rfl⟩ : syracuseStep 2074231 = 3111347) B3111347
theorem B4916855 : Blo 1362500 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B5826305 : Blo 1362500 5826305 := bstep (se 2 (by rfl) ⟨2184864, by rfl⟩ : syracuseStep 5826305 = 4369729) B4369729
theorem B3688193 : Blo 1362500 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B1533703 : Blo 1362500 1533703 := bstep (se 1 (by rfl) ⟨1150277, by rfl⟩ : syracuseStep 1533703 = 2300555) B2300555
theorem B3065633 : Blo 1362500 3065633 := bstep (se 2 (by rfl) ⟨1149612, by rfl⟩ : syracuseStep 3065633 = 2299225) B2299225
theorem B7767859 : Blo 1362500 7767859 := bstep (se 1 (by rfl) ⟨5825894, by rfl⟩ : syracuseStep 7767859 = 11651789) B11651789
theorem B1533883 : Blo 1362500 1533883 := bstep (se 1 (by rfl) ⟨1150412, by rfl⟩ : syracuseStep 1533883 = 2300825) B2300825
theorem B26920907 : Blo 1362500 26920907 := bstep (se 1 (by rfl) ⟨20190680, by rfl⟩ : syracuseStep 26920907 = 40381361) B40381361
theorem B6899741 : Blo 1362500 6899741 := bstep (se 3 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 6899741 = 2587403) B2587403
theorem B5826647 : Blo 1362500 5826647 := bstep (se 1 (by rfl) ⟨4369985, by rfl⟩ : syracuseStep 5826647 = 8739971) B8739971
theorem B3450995 : Blo 1362500 3450995 := bstep (se 1 (by rfl) ⟨2588246, by rfl⟩ : syracuseStep 3450995 = 5176493) B5176493
theorem B3065975 : Blo 1362500 3065975 := bstep (se 1 (by rfl) ⟨2299481, by rfl⟩ : syracuseStep 3065975 = 4598963) B4598963
theorem B2910343 : Blo 1362500 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B23300297 : Blo 1362500 23300297 := bstep (se 2 (by rfl) ⟨8737611, by rfl⟩ : syracuseStep 23300297 = 17475223) B17475223
theorem B15747317 : Blo 1362500 15747317 := bstep (se 5 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 15747317 = 1476311) B1476311
theorem B3066155 : Blo 1362500 3066155 := bstep (se 1 (by rfl) ⟨2299616, by rfl⟩ : syracuseStep 3066155 = 4599233) B4599233
theorem B1575227 : Blo 1362500 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B4368755 : Blo 1362500 4368755 := bstep (se 1 (by rfl) ⟨3276566, by rfl⟩ : syracuseStep 4368755 = 6553133) B6553133
theorem B1534351 : Blo 1362500 1534351 := bstep (se 1 (by rfl) ⟨1150763, by rfl⟩ : syracuseStep 1534351 = 2301527) B2301527
theorem B13101497 : Blo 1362500 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B7760387 : Blo 1362500 7760387 := bstep (se 1 (by rfl) ⟨5820290, by rfl⟩ : syracuseStep 7760387 = 11640581) B11640581
theorem B6900227 : Blo 1362500 6900227 := bstep (se 1 (by rfl) ⟨5175170, by rfl⟩ : syracuseStep 6900227 = 10350341) B10350341
theorem B6646283 : Blo 1362500 6646283 := bstep (se 1 (by rfl) ⟨4984712, by rfl⟩ : syracuseStep 6646283 = 9969425) B9969425
theorem B2525755 : Blo 1362500 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3451511 : Blo 1362500 3451511 := bstep (se 1 (by rfl) ⟨2588633, by rfl⟩ : syracuseStep 3451511 = 5177267) B5177267
theorem B1362567 : Blo 1362500 1362567 := bstep (se 1 (by rfl) ⟨1021925, by rfl⟩ : syracuseStep 1362567 = 2043851) B2043851
theorem B1362575 : Blo 1362500 1362575 := bstep (se 1 (by rfl) ⟨1021931, by rfl⟩ : syracuseStep 1362575 = 2043863) B2043863
theorem B3066515 : Blo 1362500 3066515 := bstep (se 1 (by rfl) ⟨2299886, by rfl⟩ : syracuseStep 3066515 = 4599773) B4599773
theorem B1362619 : Blo 1362500 1362619 := bstep (se 1 (by rfl) ⟨1021964, by rfl⟩ : syracuseStep 1362619 = 2043929) B2043929
theorem B3066569 : Blo 1362500 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B1362695 : Blo 1362500 1362695 := bstep (se 1 (by rfl) ⟨1022021, by rfl⟩ : syracuseStep 1362695 = 2044043) B2044043
theorem B1362703 : Blo 1362500 1362703 := bstep (se 1 (by rfl) ⟨1022027, by rfl⟩ : syracuseStep 1362703 = 2044055) B2044055
theorem B1362747 : Blo 1362500 1362747 := bstep (se 1 (by rfl) ⟨1022060, by rfl⟩ : syracuseStep 1362747 = 2044121) B2044121
theorem B1362823 : Blo 1362500 1362823 := bstep (se 1 (by rfl) ⟨1022117, by rfl⟩ : syracuseStep 1362823 = 2044235) B2044235
theorem B1534855 : Blo 1362500 1534855 := bstep (se 1 (by rfl) ⟨1151141, by rfl⟩ : syracuseStep 1534855 = 2302283) B2302283
theorem B1362831 : Blo 1362500 1362831 := bstep (se 1 (by rfl) ⟨1022123, by rfl⟩ : syracuseStep 1362831 = 2044247) B2044247
theorem B1362875 : Blo 1362500 1362875 := bstep (se 1 (by rfl) ⟨1022156, by rfl⟩ : syracuseStep 1362875 = 2044313) B2044313
theorem B7760843 : Blo 1362500 7760843 := bstep (se 1 (by rfl) ⟨5820632, by rfl⟩ : syracuseStep 7760843 = 11641265) B11641265
theorem B1362951 : Blo 1362500 1362951 := bstep (se 1 (by rfl) ⟨1022213, by rfl⟩ : syracuseStep 1362951 = 2044427) B2044427
theorem B1362959 : Blo 1362500 1362959 := bstep (se 1 (by rfl) ⟨1022219, by rfl⟩ : syracuseStep 1362959 = 2044439) B2044439
theorem B2763809 : Blo 1362500 2763809 := bstep (se 2 (by rfl) ⟨1036428, by rfl⟩ : syracuseStep 2763809 = 2072857) B2072857
theorem B1363003 : Blo 1362500 1363003 := bstep (se 1 (by rfl) ⟨1022252, by rfl⟩ : syracuseStep 1363003 = 2044505) B2044505
theorem B1535035 : Blo 1362500 1535035 := bstep (se 1 (by rfl) ⟨1151276, by rfl⟩ : syracuseStep 1535035 = 2302553) B2302553
theorem B14027863 : Blo 1362500 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B3935351 : Blo 1362500 3935351 := bstep (se 1 (by rfl) ⟨2951513, by rfl⟩ : syracuseStep 3935351 = 5903027) B5903027
theorem B1363079 : Blo 1362500 1363079 := bstep (se 1 (by rfl) ⟨1022309, by rfl⟩ : syracuseStep 1363079 = 2044619) B2044619
theorem B1363087 : Blo 1362500 1363087 := bstep (se 1 (by rfl) ⟨1022315, by rfl⟩ : syracuseStep 1363087 = 2044631) B2044631
theorem B1363131 : Blo 1362500 1363131 := bstep (se 1 (by rfl) ⟨1022348, by rfl⟩ : syracuseStep 1363131 = 2044697) B2044697
theorem B7769317 : Blo 1362500 7769317 := bstep (se 4 (by rfl) ⟨728373, by rfl⟩ : syracuseStep 7769317 = 1456747) B1456747
theorem B17460461 : Blo 1362500 17460461 := bstep (se 3 (by rfl) ⟨3273836, by rfl⟩ : syracuseStep 17460461 = 6547673) B6547673
theorem B1363207 : Blo 1362500 1363207 := bstep (se 1 (by rfl) ⟨1022405, by rfl⟩ : syracuseStep 1363207 = 2044811) B2044811
theorem B1363215 : Blo 1362500 1363215 := bstep (se 1 (by rfl) ⟨1022411, by rfl⟩ : syracuseStep 1363215 = 2044823) B2044823
theorem B2911547 : Blo 1362500 2911547 := bstep (se 1 (by rfl) ⟨2183660, by rfl⟩ : syracuseStep 2911547 = 4367321) B4367321
theorem B1363259 : Blo 1362500 1363259 := bstep (se 1 (by rfl) ⟨1022444, by rfl⟩ : syracuseStep 1363259 = 2044889) B2044889
theorem B3067271 : Blo 1362500 3067271 := bstep (se 1 (by rfl) ⟨2300453, by rfl⟩ : syracuseStep 3067271 = 4600907) B4600907
theorem B1363335 : Blo 1362500 1363335 := bstep (se 1 (by rfl) ⟨1022501, by rfl⟩ : syracuseStep 1363335 = 2045003) B2045003
theorem B1363343 : Blo 1362500 1363343 := bstep (se 1 (by rfl) ⟨1022507, by rfl⟩ : syracuseStep 1363343 = 2045015) B2045015
theorem B1363387 : Blo 1362500 1363387 := bstep (se 1 (by rfl) ⟨1022540, by rfl⟩ : syracuseStep 1363387 = 2045081) B2045081
theorem B2993609 : Blo 1362500 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B7876061 : Blo 1362500 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B1363463 : Blo 1362500 1363463 := bstep (se 1 (by rfl) ⟨1022597, by rfl⟩ : syracuseStep 1363463 = 2045195) B2045195
theorem B1363471 : Blo 1362500 1363471 := bstep (se 1 (by rfl) ⟨1022603, by rfl⟩ : syracuseStep 1363471 = 2045207) B2045207
theorem B3067451 : Blo 1362500 3067451 := bstep (se 1 (by rfl) ⟨2300588, by rfl⟩ : syracuseStep 3067451 = 4601177) B4601177
theorem B1363515 : Blo 1362500 1363515 := bstep (se 1 (by rfl) ⟨1022636, by rfl⟩ : syracuseStep 1363515 = 2045273) B2045273
theorem B3452503 : Blo 1362500 3452503 := bstep (se 1 (by rfl) ⟨2589377, by rfl⟩ : syracuseStep 3452503 = 5178755) B5178755
theorem B7761527 : Blo 1362500 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B1363591 : Blo 1362500 1363591 := bstep (se 1 (by rfl) ⟨1022693, by rfl⟩ : syracuseStep 1363591 = 2045387) B2045387
theorem B1363599 : Blo 1362500 1363599 := bstep (se 1 (by rfl) ⟨1022699, by rfl⟩ : syracuseStep 1363599 = 2045399) B2045399
theorem B3067577 : Blo 1362500 3067577 := bstep (se 2 (by rfl) ⟨1150341, by rfl⟩ : syracuseStep 3067577 = 2300683) B2300683
theorem B1363643 : Blo 1362500 1363643 := bstep (se 1 (by rfl) ⟨1022732, by rfl⟩ : syracuseStep 1363643 = 2045465) B2045465
theorem B1363719 : Blo 1362500 1363719 := bstep (se 1 (by rfl) ⟨1022789, by rfl⟩ : syracuseStep 1363719 = 2045579) B2045579
theorem B1363727 : Blo 1362500 1363727 := bstep (se 1 (by rfl) ⟨1022795, by rfl⟩ : syracuseStep 1363727 = 2045591) B2045591
theorem B4599611 : Blo 1362500 4599611 := bstep (se 1 (by rfl) ⟨3449708, by rfl⟩ : syracuseStep 4599611 = 6899417) B6899417
theorem B2912059 : Blo 1362500 2912059 := bstep (se 1 (by rfl) ⟨2184044, by rfl⟩ : syracuseStep 2912059 = 4368089) B4368089
theorem B1363771 : Blo 1362500 1363771 := bstep (se 1 (by rfl) ⟨1022828, by rfl⟩ : syracuseStep 1363771 = 2045657) B2045657
theorem B5820275 : Blo 1362500 5820275 := bstep (se 1 (by rfl) ⟨4365206, by rfl⟩ : syracuseStep 5820275 = 8730413) B8730413
theorem B2043767 : Blo 1362500 2043767 := bstep (se 1 (by rfl) ⟨1532825, by rfl⟩ : syracuseStep 2043767 = 3065651) B3065651
theorem B1363847 : Blo 1362500 1363847 := bstep (se 1 (by rfl) ⟨1022885, by rfl⟩ : syracuseStep 1363847 = 2045771) B2045771
theorem B3452807 : Blo 1362500 3452807 := bstep (se 1 (by rfl) ⟨2589605, by rfl⟩ : syracuseStep 3452807 = 5179211) B5179211
theorem B2043791 : Blo 1362500 2043791 := bstep (se 1 (by rfl) ⟨1532843, by rfl⟩ : syracuseStep 2043791 = 3065687) B3065687
theorem B1363855 : Blo 1362500 1363855 := bstep (se 1 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 1363855 = 2045783) B2045783
theorem B13275031 : Blo 1362500 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B2043833 : Blo 1362500 2043833 := bstep (se 2 (by rfl) ⟨766437, by rfl⟩ : syracuseStep 2043833 = 1532875) B1532875
theorem B1363899 : Blo 1362500 1363899 := bstep (se 1 (by rfl) ⟨1022924, by rfl⟩ : syracuseStep 1363899 = 2045849) B2045849
theorem B2043911 : Blo 1362500 2043911 := bstep (se 1 (by rfl) ⟨1532933, by rfl⟩ : syracuseStep 2043911 = 3065867) B3065867
theorem B1363975 : Blo 1362500 1363975 := bstep (se 1 (by rfl) ⟨1022981, by rfl⟩ : syracuseStep 1363975 = 2045963) B2045963
theorem B5820427 : Blo 1362500 5820427 := bstep (se 1 (by rfl) ⟨4365320, by rfl⟩ : syracuseStep 5820427 = 8730641) B8730641
theorem B3067919 : Blo 1362500 3067919 := bstep (se 1 (by rfl) ⟨2300939, by rfl⟩ : syracuseStep 3067919 = 4601879) B4601879
theorem B1363983 : Blo 1362500 1363983 := bstep (se 1 (by rfl) ⟨1022987, by rfl⟩ : syracuseStep 1363983 = 2045975) B2045975
theorem B3452939 : Blo 1362500 3452939 := bstep (se 1 (by rfl) ⟨2589704, by rfl⟩ : syracuseStep 3452939 = 5179409) B5179409
theorem B13111307 : Blo 1362500 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B3067937 : Blo 1362500 3067937 := bstep (se 2 (by rfl) ⟨1150476, by rfl⟩ : syracuseStep 3067937 = 2300953) B2300953
theorem B2043947 : Blo 1362500 2043947 := bstep (se 1 (by rfl) ⟨1532960, by rfl⟩ : syracuseStep 2043947 = 3065921) B3065921
theorem B1364027 : Blo 1362500 1364027 := bstep (se 1 (by rfl) ⟨1023020, by rfl⟩ : syracuseStep 1364027 = 2046041) B2046041
theorem B2043977 : Blo 1362500 2043977 := bstep (se 2 (by rfl) ⟨766491, by rfl⟩ : syracuseStep 2043977 = 1532983) B1532983
theorem B6901847 : Blo 1362500 6901847 := bstep (se 1 (by rfl) ⟨5176385, by rfl⟩ : syracuseStep 6901847 = 10352771) B10352771
theorem B1364103 : Blo 1362500 1364103 := bstep (se 1 (by rfl) ⟨1023077, by rfl⟩ : syracuseStep 1364103 = 2046155) B2046155
theorem B1364111 : Blo 1362500 1364111 := bstep (se 1 (by rfl) ⟨1023083, by rfl⟩ : syracuseStep 1364111 = 2046167) B2046167
theorem B13455533 : Blo 1362500 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B2044091 : Blo 1362500 2044091 := bstep (se 1 (by rfl) ⟨1533068, by rfl⟩ : syracuseStep 2044091 = 3066137) B3066137
theorem B1364155 : Blo 1362500 1364155 := bstep (se 1 (by rfl) ⟨1023116, by rfl⟩ : syracuseStep 1364155 = 2046233) B2046233
theorem B2044151 : Blo 1362500 2044151 := bstep (se 1 (by rfl) ⟨1533113, by rfl⟩ : syracuseStep 2044151 = 3066227) B3066227
theorem B1364231 : Blo 1362500 1364231 := bstep (se 1 (by rfl) ⟨1023173, by rfl⟩ : syracuseStep 1364231 = 2046347) B2046347
theorem B2044175 : Blo 1362500 2044175 := bstep (se 1 (by rfl) ⟨1533131, by rfl⟩ : syracuseStep 2044175 = 3066263) B3066263
theorem B1364239 : Blo 1362500 1364239 := bstep (se 1 (by rfl) ⟨1023179, by rfl⟩ : syracuseStep 1364239 = 2046359) B2046359
theorem B4600097 : Blo 1362500 4600097 := bstep (se 2 (by rfl) ⟨1725036, by rfl⟩ : syracuseStep 4600097 = 3450073) B3450073
theorem B5984545 : Blo 1362500 5984545 := bstep (se 2 (by rfl) ⟨2244204, by rfl⟩ : syracuseStep 5984545 = 4488409) B4488409
theorem B2044217 : Blo 1362500 2044217 := bstep (se 2 (by rfl) ⟨766581, by rfl⟩ : syracuseStep 2044217 = 1533163) B1533163
theorem B1364283 : Blo 1362500 1364283 := bstep (se 1 (by rfl) ⟨1023212, by rfl⟩ : syracuseStep 1364283 = 2046425) B2046425
theorem B3068279 : Blo 1362500 3068279 := bstep (se 1 (by rfl) ⟨2301209, by rfl⟩ : syracuseStep 3068279 = 4602419) B4602419
theorem B2044295 : Blo 1362500 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B1364359 : Blo 1362500 1364359 := bstep (se 1 (by rfl) ⟨1023269, by rfl⟩ : syracuseStep 1364359 = 2046539) B2046539
theorem B16576913 : Blo 1362500 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B1364367 : Blo 1362500 1364367 := bstep (se 1 (by rfl) ⟨1023275, by rfl⟩ : syracuseStep 1364367 = 2046551) B2046551
theorem B2044331 : Blo 1362500 2044331 := bstep (se 1 (by rfl) ⟨1533248, by rfl⟩ : syracuseStep 2044331 = 3066497) B3066497
theorem B1364411 : Blo 1362500 1364411 := bstep (se 1 (by rfl) ⟨1023308, by rfl⟩ : syracuseStep 1364411 = 2046617) B2046617
theorem B2044361 : Blo 1362500 2044361 := bstep (se 2 (by rfl) ⟨766635, by rfl⟩ : syracuseStep 2044361 = 1533271) B1533271
theorem B1364487 : Blo 1362500 1364487 := bstep (se 1 (by rfl) ⟨1023365, by rfl⟩ : syracuseStep 1364487 = 2046731) B2046731
theorem B3453455 : Blo 1362500 3453455 := bstep (se 1 (by rfl) ⟨2590091, by rfl⟩ : syracuseStep 3453455 = 5180183) B5180183
theorem B1364495 : Blo 1362500 1364495 := bstep (se 1 (by rfl) ⟨1023371, by rfl⟩ : syracuseStep 1364495 = 2046743) B2046743
theorem B1724971 : Blo 1362500 1724971 := bstep (se 1 (by rfl) ⟨1293728, by rfl⟩ : syracuseStep 1724971 = 2587457) B2587457
theorem B3068459 : Blo 1362500 3068459 := bstep (se 1 (by rfl) ⟨2301344, by rfl⟩ : syracuseStep 3068459 = 4602689) B4602689
theorem B2044475 : Blo 1362500 2044475 := bstep (se 1 (by rfl) ⟨1533356, by rfl⟩ : syracuseStep 2044475 = 3066713) B3066713
theorem B6902333 : Blo 1362500 6902333 := bstep (se 3 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 6902333 = 2588375) B2588375
theorem B26202689 : Blo 1362500 26202689 := bstep (se 2 (by rfl) ⟨9826008, by rfl⟩ : syracuseStep 26202689 = 19652017) B19652017
theorem B2044535 : Blo 1362500 2044535 := bstep (se 1 (by rfl) ⟨1533401, by rfl⟩ : syracuseStep 2044535 = 3066803) B3066803
theorem B2044559 : Blo 1362500 2044559 := bstep (se 1 (by rfl) ⟨1533419, by rfl⟩ : syracuseStep 2044559 = 3066839) B3066839
theorem B3453587 : Blo 1362500 3453587 := bstep (se 1 (by rfl) ⟨2590190, by rfl⟩ : syracuseStep 3453587 = 5180381) B5180381
theorem B2044601 : Blo 1362500 2044601 := bstep (se 2 (by rfl) ⟨766725, by rfl⟩ : syracuseStep 2044601 = 1533451) B1533451
theorem B19665625 : Blo 1362500 19665625 := bstep (se 2 (by rfl) ⟨7374609, by rfl⟩ : syracuseStep 19665625 = 14749219) B14749219
theorem B2044679 : Blo 1362500 2044679 := bstep (se 1 (by rfl) ⟨1533509, by rfl⟩ : syracuseStep 2044679 = 3067019) B3067019
theorem B2044715 : Blo 1362500 2044715 := bstep (se 1 (by rfl) ⟨1533536, by rfl⟩ : syracuseStep 2044715 = 3067073) B3067073
theorem B2044745 : Blo 1362500 2044745 := bstep (se 2 (by rfl) ⟨766779, by rfl⟩ : syracuseStep 2044745 = 1533559) B1533559
theorem B4600691 : Blo 1362500 4600691 := bstep (se 1 (by rfl) ⟨3450518, by rfl⟩ : syracuseStep 4600691 = 6901037) B6901037
theorem B3068819 : Blo 1362500 3068819 := bstep (se 1 (by rfl) ⟨2301614, by rfl⟩ : syracuseStep 3068819 = 4603229) B4603229
theorem B2044859 : Blo 1362500 2044859 := bstep (se 1 (by rfl) ⟨1533644, by rfl⟩ : syracuseStep 2044859 = 3067289) B3067289
theorem B3068873 : Blo 1362500 3068873 := bstep (se 2 (by rfl) ⟨1150827, by rfl⟩ : syracuseStep 3068873 = 2301655) B2301655
theorem B2044919 : Blo 1362500 2044919 := bstep (se 1 (by rfl) ⟨1533689, by rfl⟩ : syracuseStep 2044919 = 3067379) B3067379
theorem B2044943 : Blo 1362500 2044943 := bstep (se 1 (by rfl) ⟨1533707, by rfl⟩ : syracuseStep 2044943 = 3067415) B3067415
theorem B2044985 : Blo 1362500 2044985 := bstep (se 2 (by rfl) ⟨766869, by rfl⟩ : syracuseStep 2044985 = 1533739) B1533739
theorem B2045063 : Blo 1362500 2045063 := bstep (se 1 (by rfl) ⟨1533797, by rfl⟩ : syracuseStep 2045063 = 3067595) B3067595
theorem B2045099 : Blo 1362500 2045099 := bstep (se 1 (by rfl) ⟨1533824, by rfl⟩ : syracuseStep 2045099 = 3067649) B3067649
theorem B2045129 : Blo 1362500 2045129 := bstep (se 2 (by rfl) ⟨766923, by rfl⟩ : syracuseStep 2045129 = 1533847) B1533847
theorem B5985569 : Blo 1362500 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B2045243 : Blo 1362500 2045243 := bstep (se 1 (by rfl) ⟨1533932, by rfl⟩ : syracuseStep 2045243 = 3067865) B3067865
theorem B2045303 : Blo 1362500 2045303 := bstep (se 1 (by rfl) ⟨1533977, by rfl⟩ : syracuseStep 2045303 = 3067955) B3067955
theorem B23287175 : Blo 1362500 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B2184583 : Blo 1362500 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B2045327 : Blo 1362500 2045327 := bstep (se 1 (by rfl) ⟨1533995, by rfl⟩ : syracuseStep 2045327 = 3067991) B3067991
theorem B3110291 : Blo 1362500 3110291 := bstep (se 1 (by rfl) ⟨2332718, by rfl⟩ : syracuseStep 3110291 = 4665437) B4665437
theorem B2045369 : Blo 1362500 2045369 := bstep (se 2 (by rfl) ⟨767013, by rfl⟩ : syracuseStep 2045369 = 1534027) B1534027
theorem B1725943 : Blo 1362500 1725943 := bstep (se 1 (by rfl) ⟨1294457, by rfl⟩ : syracuseStep 1725943 = 2588915) B2588915
theorem B2045447 : Blo 1362500 2045447 := bstep (se 1 (by rfl) ⟨1534085, by rfl⟩ : syracuseStep 2045447 = 3068171) B3068171
theorem B7763485 : Blo 1362500 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B2045483 : Blo 1362500 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B17036867 : Blo 1362500 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B2045513 : Blo 1362500 2045513 := bstep (se 2 (by rfl) ⟨767067, by rfl⟩ : syracuseStep 2045513 = 1534135) B1534135
theorem B15357559 : Blo 1362500 15357559 := bstep (se 1 (by rfl) ⟨11518169, by rfl⟩ : syracuseStep 15357559 = 23036339) B23036339
theorem B3069575 : Blo 1362500 3069575 := bstep (se 1 (by rfl) ⟨2302181, by rfl⟩ : syracuseStep 3069575 = 4604363) B4604363
theorem B2045627 : Blo 1362500 2045627 := bstep (se 1 (by rfl) ⟨1534220, by rfl⟩ : syracuseStep 2045627 = 3068441) B3068441
theorem B3880649 : Blo 1362500 3880649 := bstep (se 2 (by rfl) ⟨1455243, by rfl⟩ : syracuseStep 3880649 = 2910487) B2910487
theorem B5822189 : Blo 1362500 5822189 := bstep (se 3 (by rfl) ⟨1091660, by rfl⟩ : syracuseStep 5822189 = 2183321) B2183321
theorem B2045687 : Blo 1362500 2045687 := bstep (se 1 (by rfl) ⟨1534265, by rfl⟩ : syracuseStep 2045687 = 3068531) B3068531
theorem B2045711 : Blo 1362500 2045711 := bstep (se 1 (by rfl) ⟨1534283, by rfl⟩ : syracuseStep 2045711 = 3068567) B3068567
theorem B2299691 : Blo 1362500 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B6993715 : Blo 1362500 6993715 := bstep (se 1 (by rfl) ⟨5245286, by rfl⟩ : syracuseStep 6993715 = 10490573) B10490573
theorem B2045753 : Blo 1362500 2045753 := bstep (se 2 (by rfl) ⟨767157, by rfl⟩ : syracuseStep 2045753 = 1534315) B1534315
theorem B1726267 : Blo 1362500 1726267 := bstep (se 1 (by rfl) ⟨1294700, by rfl⟩ : syracuseStep 1726267 = 2589401) B2589401
theorem B3069755 : Blo 1362500 3069755 := bstep (se 1 (by rfl) ⟨2302316, by rfl⟩ : syracuseStep 3069755 = 4604633) B4604633
theorem B2045831 : Blo 1362500 2045831 := bstep (se 1 (by rfl) ⟨1534373, by rfl⟩ : syracuseStep 2045831 = 3068747) B3068747
theorem B2045867 : Blo 1362500 2045867 := bstep (se 1 (by rfl) ⟨1534400, by rfl⟩ : syracuseStep 2045867 = 3068801) B3068801
theorem B3069881 : Blo 1362500 3069881 := bstep (se 2 (by rfl) ⟨1151205, by rfl⟩ : syracuseStep 3069881 = 2302411) B2302411
theorem B2045897 : Blo 1362500 2045897 := bstep (se 2 (by rfl) ⟨767211, by rfl⟩ : syracuseStep 2045897 = 1534423) B1534423
theorem B2586667 : Blo 1362500 2586667 := bstep (se 1 (by rfl) ⟨1940000, by rfl⟩ : syracuseStep 2586667 = 3880001) B3880001
theorem B7764011 : Blo 1362500 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B2046011 : Blo 1362500 2046011 := bstep (se 1 (by rfl) ⟨1534508, by rfl⟩ : syracuseStep 2046011 = 3069017) B3069017
theorem B10639421 : Blo 1362500 10639421 := bstep (se 3 (by rfl) ⟨1994891, by rfl⟩ : syracuseStep 10639421 = 3989783) B3989783
theorem B2046071 : Blo 1362500 2046071 := bstep (se 1 (by rfl) ⟨1534553, by rfl⟩ : syracuseStep 2046071 = 3069107) B3069107
theorem B2046095 : Blo 1362500 2046095 := bstep (se 1 (by rfl) ⟨1534571, by rfl⟩ : syracuseStep 2046095 = 3069143) B3069143
theorem B2300089 : Blo 1362500 2300089 := bstep (se 2 (by rfl) ⟨862533, by rfl⟩ : syracuseStep 2300089 = 1725067) B1725067
theorem B2046137 : Blo 1362500 2046137 := bstep (se 2 (by rfl) ⟨767301, by rfl⟩ : syracuseStep 2046137 = 1534603) B1534603
theorem B10361033 : Blo 1362500 10361033 := bstep (se 2 (by rfl) ⟨3885387, by rfl⟩ : syracuseStep 10361033 = 7770775) B7770775
theorem B14751989 : Blo 1362500 14751989 := bstep (se 5 (by rfl) ⟨691499, by rfl⟩ : syracuseStep 14751989 = 1382999) B1382999
theorem B2046215 : Blo 1362500 2046215 := bstep (se 1 (by rfl) ⟨1534661, by rfl⟩ : syracuseStep 2046215 = 3069323) B3069323
theorem B4143403 : Blo 1362500 4143403 := bstep (se 1 (by rfl) ⟨3107552, by rfl⟩ : syracuseStep 4143403 = 6215105) B6215105
theorem B2046251 : Blo 1362500 2046251 := bstep (se 1 (by rfl) ⟨1534688, by rfl⟩ : syracuseStep 2046251 = 3069377) B3069377
theorem B6904115 : Blo 1362500 6904115 := bstep (se 1 (by rfl) ⟨5178086, by rfl⟩ : syracuseStep 6904115 = 10356173) B10356173
theorem B2046281 : Blo 1362500 2046281 := bstep (se 2 (by rfl) ⟨767355, by rfl⟩ : syracuseStep 2046281 = 1534711) B1534711
theorem B10492295 : Blo 1362500 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B5822873 : Blo 1362500 5822873 := bstep (se 2 (by rfl) ⟨2183577, by rfl⟩ : syracuseStep 5822873 = 4367155) B4367155
theorem B2046395 : Blo 1362500 2046395 := bstep (se 1 (by rfl) ⟨1534796, by rfl⟩ : syracuseStep 2046395 = 3069593) B3069593
theorem B2046455 : Blo 1362500 2046455 := bstep (se 1 (by rfl) ⟨1534841, by rfl⟩ : syracuseStep 2046455 = 3069683) B3069683
theorem B2046479 : Blo 1362500 2046479 := bstep (se 1 (by rfl) ⟨1534859, by rfl⟩ : syracuseStep 2046479 = 3069719) B3069719
theorem B3881515 : Blo 1362500 3881515 := bstep (se 1 (by rfl) ⟨2911136, by rfl⟩ : syracuseStep 3881515 = 5822273) B5822273
theorem B2046521 : Blo 1362500 2046521 := bstep (se 2 (by rfl) ⟨767445, by rfl⟩ : syracuseStep 2046521 = 1534891) B1534891
theorem B15530615 : Blo 1362500 15530615 := bstep (se 1 (by rfl) ⟨11647961, by rfl⟩ : syracuseStep 15530615 = 23295923) B23295923
theorem B6904439 : Blo 1362500 6904439 := bstep (se 1 (by rfl) ⟨5178329, by rfl⟩ : syracuseStep 6904439 = 10356659) B10356659
theorem B2046599 : Blo 1362500 2046599 := bstep (se 1 (by rfl) ⟨1534949, by rfl⟩ : syracuseStep 2046599 = 3069899) B3069899
theorem B2046635 : Blo 1362500 2046635 := bstep (se 1 (by rfl) ⟨1534976, by rfl⟩ : syracuseStep 2046635 = 3069953) B3069953
theorem B2046665 : Blo 1362500 2046665 := bstep (se 2 (by rfl) ⟨767499, by rfl⟩ : syracuseStep 2046665 = 1534999) B1534999
theorem B1637111 : Blo 1362500 1637111 := bstep (se 1 (by rfl) ⟨1227833, by rfl⟩ : syracuseStep 1637111 = 2455667) B2455667
theorem B1841935 : Blo 1362500 1841935 := bstep (se 1 (by rfl) ⟨1381451, by rfl⟩ : syracuseStep 1841935 = 2762903) B2762903
theorem B5602081 : Blo 1362500 5602081 := bstep (se 2 (by rfl) ⟨2100780, by rfl⟩ : syracuseStep 5602081 = 4201561) B4201561
theorem B3881789 : Blo 1362500 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B2300791 : Blo 1362500 2300791 := bstep (se 1 (by rfl) ⟨1725593, by rfl⟩ : syracuseStep 2300791 = 3451187) B3451187
theorem B26213381 : Blo 1362500 26213381 := bstep (se 4 (by rfl) ⟨2457504, by rfl⟩ : syracuseStep 26213381 = 4915009) B4915009
theorem B23313419 : Blo 1362500 23313419 := bstep (se 1 (by rfl) ⟨17485064, by rfl⟩ : syracuseStep 23313419 = 34970129) B34970129
theorem B2300987 : Blo 1362500 2300987 := bstep (se 1 (by rfl) ⟨1725740, by rfl⟩ : syracuseStep 2300987 = 3451481) B3451481
theorem B4365373 : Blo 1362500 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B2587783 : Blo 1362500 2587783 := bstep (se 1 (by rfl) ⟨1940837, by rfl⟩ : syracuseStep 2587783 = 3881675) B3881675
theorem B3882131 : Blo 1362500 3882131 := bstep (se 1 (by rfl) ⟨2911598, by rfl⟩ : syracuseStep 3882131 = 5823197) B5823197
theorem B4603283 : Blo 1362500 4603283 := bstep (se 1 (by rfl) ⟨3452462, by rfl⟩ : syracuseStep 4603283 = 6904925) B6904925
theorem B2301385 : Blo 1362500 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B7765469 : Blo 1362500 7765469 := bstep (se 3 (by rfl) ⟨1456025, by rfl⟩ : syracuseStep 7765469 = 2912051) B2912051
theorem B6905411 : Blo 1362500 6905411 := bstep (se 1 (by rfl) ⟨5179058, by rfl⟩ : syracuseStep 6905411 = 10358117) B10358117
theorem B2588345 : Blo 1362500 2588345 := bstep (se 2 (by rfl) ⟨970629, by rfl⟩ : syracuseStep 2588345 = 1941259) B1941259
theorem B1638187 : Blo 1362500 1638187 := bstep (se 1 (by rfl) ⟨1228640, by rfl⟩ : syracuseStep 1638187 = 2457281) B2457281
theorem B6905735 : Blo 1362500 6905735 := bstep (se 1 (by rfl) ⟨5179301, by rfl⟩ : syracuseStep 6905735 = 10358603) B10358603
theorem B5177297 : Blo 1362500 5177297 := bstep (se 2 (by rfl) ⟨1941486, by rfl⟩ : syracuseStep 5177297 = 3882973) B3882973
theorem B2301959 : Blo 1362500 2301959 := bstep (se 1 (by rfl) ⟨1726469, by rfl⟩ : syracuseStep 2301959 = 3452939) B3452939
theorem B8740871 : Blo 1362500 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B3448889 : Blo 1362500 3448889 := bstep (se 2 (by rfl) ⟨1293333, by rfl⟩ : syracuseStep 3448889 = 2586667) B2586667
theorem B8970355 : Blo 1362500 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B10494269 : Blo 1362500 10494269 := bstep (se 3 (by rfl) ⟨1967675, by rfl⟩ : syracuseStep 10494269 = 3935351) B3935351
theorem B2302303 : Blo 1362500 2302303 := bstep (se 1 (by rfl) ⟨1726727, by rfl⟩ : syracuseStep 2302303 = 3453455) B3453455
theorem B7979393 : Blo 1362500 7979393 := bstep (se 2 (by rfl) ⟨2992272, by rfl⟩ : syracuseStep 7979393 = 5984545) B5984545
theorem B7766401 : Blo 1362500 7766401 := bstep (se 2 (by rfl) ⟨2912400, by rfl⟩ : syracuseStep 7766401 = 5824801) B5824801
theorem B2302391 : Blo 1362500 2302391 := bstep (se 1 (by rfl) ⟨1726793, by rfl⟩ : syracuseStep 2302391 = 3453587) B3453587
theorem B8741357 : Blo 1362500 8741357 := bstep (se 3 (by rfl) ⟨1639004, by rfl⟩ : syracuseStep 8741357 = 3278009) B3278009
theorem B2589241 : Blo 1362500 2589241 := bstep (se 2 (by rfl) ⟨970965, by rfl⟩ : syracuseStep 2589241 = 1941931) B1941931
theorem B3367673 : Blo 1362500 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2589545 : Blo 1362500 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B3990379 : Blo 1362500 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B2589583 : Blo 1362500 2589583 := bstep (se 1 (by rfl) ⟨1942187, by rfl⟩ : syracuseStep 2589583 = 3884375) B3884375
theorem B6898607 : Blo 1362500 6898607 := bstep (se 1 (by rfl) ⟨5173955, by rfl⟩ : syracuseStep 6898607 = 10347911) B10347911
theorem B15524783 : Blo 1362500 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B9834659 : Blo 1362500 9834659 := bstep (se 1 (by rfl) ⟨7375994, by rfl⟩ : syracuseStep 9834659 = 14751989) B14751989
theorem B2073527 : Blo 1362500 2073527 := bstep (se 1 (by rfl) ⟨1555145, by rfl⟩ : syracuseStep 2073527 = 3110291) B3110291
theorem B11650013 : Blo 1362500 11650013 := bstep (se 3 (by rfl) ⟨2184377, by rfl⟩ : syracuseStep 11650013 = 4368755) B4368755
theorem B44205101 : Blo 1362500 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B3277903 : Blo 1362500 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B3884203 : Blo 1362500 3884203 := bstep (se 1 (by rfl) ⟨2913152, by rfl⟩ : syracuseStep 3884203 = 5826305) B5826305
theorem B1533127 : Blo 1362500 1533127 := bstep (se 1 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 1533127 = 2299691) B2299691
theorem B3884431 : Blo 1362500 3884431 := bstep (se 1 (by rfl) ⟨2913323, by rfl⟩ : syracuseStep 3884431 = 5826647) B5826647
theorem B18703817 : Blo 1362500 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B15533531 : Blo 1362500 15533531 := bstep (se 1 (by rfl) ⟨11650148, by rfl⟩ : syracuseStep 15533531 = 23300297) B23300297
theorem B6907355 : Blo 1362500 6907355 := bstep (se 1 (by rfl) ⟨5180516, by rfl⟩ : syracuseStep 6907355 = 10361033) B10361033
theorem B3450377 : Blo 1362500 3450377 := bstep (se 2 (by rfl) ⟨1293891, by rfl⟩ : syracuseStep 3450377 = 2587783) B2587783
theorem B8734331 : Blo 1362500 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B10348397 : Blo 1362500 10348397 := bstep (se 3 (by rfl) ⟨1940324, by rfl⟩ : syracuseStep 10348397 = 3880649) B3880649
theorem B17475587 : Blo 1362500 17475587 := bstep (se 1 (by rfl) ⟨13106690, by rfl⟩ : syracuseStep 17475587 = 26213381) B26213381
theorem B15542279 : Blo 1362500 15542279 := bstep (se 1 (by rfl) ⟨11656709, by rfl⟩ : syracuseStep 15542279 = 23313419) B23313419
theorem B1533991 : Blo 1362500 1533991 := bstep (se 1 (by rfl) ⟨1150493, by rfl⟩ : syracuseStep 1533991 = 2300987) B2300987
theorem B9324953 : Blo 1362500 9324953 := bstep (se 2 (by rfl) ⟨3496857, by rfl⟩ : syracuseStep 9324953 = 6993715) B6993715
theorem B10357145 : Blo 1362500 10357145 := bstep (se 2 (by rfl) ⟨3883929, by rfl⟩ : syracuseStep 10357145 = 7767859) B7767859
theorem B3066407 : Blo 1362500 3066407 := bstep (se 1 (by rfl) ⟨2299805, by rfl⟩ : syracuseStep 3066407 = 4599611) B4599611
theorem B1362511 : Blo 1362500 1362511 := bstep (se 1 (by rfl) ⟨1021883, by rfl⟩ : syracuseStep 1362511 = 2043767) B2043767
theorem B1362527 : Blo 1362500 1362527 := bstep (se 1 (by rfl) ⟨1021895, by rfl⟩ : syracuseStep 1362527 = 2043791) B2043791
theorem B1362555 : Blo 1362500 1362555 := bstep (se 1 (by rfl) ⟨1021916, by rfl⟩ : syracuseStep 1362555 = 2043833) B2043833
theorem B3451531 : Blo 1362500 3451531 := bstep (se 1 (by rfl) ⟨2588648, by rfl⟩ : syracuseStep 3451531 = 5177297) B5177297
theorem B1362607 : Blo 1362500 1362607 := bstep (se 1 (by rfl) ⟨1021955, by rfl⟩ : syracuseStep 1362607 = 2043911) B2043911
theorem B7760569 : Blo 1362500 7760569 := bstep (se 2 (by rfl) ⟨2910213, by rfl⟩ : syracuseStep 7760569 = 5820427) B5820427
theorem B1362631 : Blo 1362500 1362631 := bstep (se 1 (by rfl) ⟨1021973, by rfl⟩ : syracuseStep 1362631 = 2043947) B2043947
theorem B1362651 : Blo 1362500 1362651 := bstep (se 1 (by rfl) ⟨1021988, by rfl⟩ : syracuseStep 1362651 = 2043977) B2043977
theorem B1362727 : Blo 1362500 1362727 := bstep (se 1 (by rfl) ⟨1022045, by rfl⟩ : syracuseStep 1362727 = 2044091) B2044091
theorem B1362767 : Blo 1362500 1362767 := bstep (se 1 (by rfl) ⟨1022075, by rfl⟩ : syracuseStep 1362767 = 2044151) B2044151
theorem B1362783 : Blo 1362500 1362783 := bstep (se 1 (by rfl) ⟨1022087, by rfl⟩ : syracuseStep 1362783 = 2044175) B2044175
theorem B3066731 : Blo 1362500 3066731 := bstep (se 1 (by rfl) ⟨2300048, by rfl⟩ : syracuseStep 3066731 = 4600097) B4600097
theorem B1362811 : Blo 1362500 1362811 := bstep (se 1 (by rfl) ⟨1022108, by rfl⟩ : syracuseStep 1362811 = 2044217) B2044217
theorem B3066785 : Blo 1362500 3066785 := bstep (se 2 (by rfl) ⟨1150044, by rfl⟩ : syracuseStep 3066785 = 2300089) B2300089
theorem B1362863 : Blo 1362500 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B3451835 : Blo 1362500 3451835 := bstep (se 1 (by rfl) ⟨2588876, by rfl⟩ : syracuseStep 3451835 = 5177753) B5177753
theorem B1362887 : Blo 1362500 1362887 := bstep (se 1 (by rfl) ⟨1022165, by rfl⟩ : syracuseStep 1362887 = 2044331) B2044331
theorem B1362907 : Blo 1362500 1362907 := bstep (se 1 (by rfl) ⟨1022180, by rfl⟩ : syracuseStep 1362907 = 2044361) B2044361
theorem B1362983 : Blo 1362500 1362983 := bstep (se 1 (by rfl) ⟨1022237, by rfl⟩ : syracuseStep 1362983 = 2044475) B2044475
theorem B17468459 : Blo 1362500 17468459 := bstep (se 1 (by rfl) ⟨13101344, by rfl⟩ : syracuseStep 17468459 = 26202689) B26202689
theorem B5524537 : Blo 1362500 5524537 := bstep (se 2 (by rfl) ⟨2071701, by rfl⟩ : syracuseStep 5524537 = 4143403) B4143403
theorem B1363023 : Blo 1362500 1363023 := bstep (se 1 (by rfl) ⟨1022267, by rfl⟩ : syracuseStep 1363023 = 2044535) B2044535
theorem B1363039 : Blo 1362500 1363039 := bstep (se 1 (by rfl) ⟨1022279, by rfl⟩ : syracuseStep 1363039 = 2044559) B2044559
theorem B1363067 : Blo 1362500 1363067 := bstep (se 1 (by rfl) ⟨1022300, by rfl⟩ : syracuseStep 1363067 = 2044601) B2044601
theorem B1363119 : Blo 1362500 1363119 := bstep (se 1 (by rfl) ⟨1022339, by rfl⟩ : syracuseStep 1363119 = 2044679) B2044679
theorem B1363143 : Blo 1362500 1363143 := bstep (se 1 (by rfl) ⟨1022357, by rfl⟩ : syracuseStep 1363143 = 2044715) B2044715
theorem B1363163 : Blo 1362500 1363163 := bstep (se 1 (by rfl) ⟨1022372, by rfl⟩ : syracuseStep 1363163 = 2044745) B2044745
theorem B3067127 : Blo 1362500 3067127 := bstep (se 1 (by rfl) ⟨2300345, by rfl⟩ : syracuseStep 3067127 = 4600691) B4600691
theorem B11062565 : Blo 1362500 11062565 := bstep (se 4 (by rfl) ⟨1037115, by rfl⟩ : syracuseStep 11062565 = 2074231) B2074231
theorem B1363239 : Blo 1362500 1363239 := bstep (se 1 (by rfl) ⟨1022429, by rfl⟩ : syracuseStep 1363239 = 2044859) B2044859
theorem B1363279 : Blo 1362500 1363279 := bstep (se 1 (by rfl) ⟨1022459, by rfl⟩ : syracuseStep 1363279 = 2044919) B2044919
theorem B1363295 : Blo 1362500 1363295 := bstep (se 1 (by rfl) ⟨1022471, by rfl⟩ : syracuseStep 1363295 = 2044943) B2044943
theorem B1363323 : Blo 1362500 1363323 := bstep (se 1 (by rfl) ⟨1022492, by rfl⟩ : syracuseStep 1363323 = 2044985) B2044985
theorem B11201935 : Blo 1362500 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B1363375 : Blo 1362500 1363375 := bstep (se 1 (by rfl) ⟨1022531, by rfl⟩ : syracuseStep 1363375 = 2045063) B2045063
theorem B1363399 : Blo 1362500 1363399 := bstep (se 1 (by rfl) ⟨1022549, by rfl⟩ : syracuseStep 1363399 = 2045099) B2045099
theorem B1363419 : Blo 1362500 1363419 := bstep (se 1 (by rfl) ⟨1022564, by rfl⟩ : syracuseStep 1363419 = 2045129) B2045129
theorem B1363495 : Blo 1362500 1363495 := bstep (se 1 (by rfl) ⟨1022621, by rfl⟩ : syracuseStep 1363495 = 2045243) B2045243
theorem B1363535 : Blo 1362500 1363535 := bstep (se 1 (by rfl) ⟨1022651, by rfl⟩ : syracuseStep 1363535 = 2045303) B2045303
theorem B1363551 : Blo 1362500 1363551 := bstep (se 1 (by rfl) ⟨1022663, by rfl⟩ : syracuseStep 1363551 = 2045327) B2045327
theorem B1363579 : Blo 1362500 1363579 := bstep (se 1 (by rfl) ⟨1022684, by rfl⟩ : syracuseStep 1363579 = 2045369) B2045369
theorem B5828219 : Blo 1362500 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B2764459 : Blo 1362500 2764459 := bstep (se 1 (by rfl) ⟨2073344, by rfl⟩ : syracuseStep 2764459 = 4146689) B4146689
theorem B1363631 : Blo 1362500 1363631 := bstep (se 1 (by rfl) ⟨1022723, by rfl⟩ : syracuseStep 1363631 = 2045447) B2045447
theorem B27979453 : Blo 1362500 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B1363655 : Blo 1362500 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B3452615 : Blo 1362500 3452615 := bstep (se 1 (by rfl) ⟨2589461, by rfl⟩ : syracuseStep 3452615 = 5178923) B5178923
theorem B11357911 : Blo 1362500 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B1363675 : Blo 1362500 1363675 := bstep (se 1 (by rfl) ⟨1022756, by rfl⟩ : syracuseStep 1363675 = 2045513) B2045513
theorem B3452665 : Blo 1362500 3452665 := bstep (se 2 (by rfl) ⟨1294749, by rfl⟩ : syracuseStep 3452665 = 2589499) B2589499
theorem B1363751 : Blo 1362500 1363751 := bstep (se 1 (by rfl) ⟨1022813, by rfl⟩ : syracuseStep 1363751 = 2045627) B2045627
theorem B3067721 : Blo 1362500 3067721 := bstep (se 2 (by rfl) ⟨1150395, by rfl⟩ : syracuseStep 3067721 = 2300791) B2300791
theorem B1363791 : Blo 1362500 1363791 := bstep (se 1 (by rfl) ⟨1022843, by rfl⟩ : syracuseStep 1363791 = 2045687) B2045687
theorem B1363807 : Blo 1362500 1363807 := bstep (se 1 (by rfl) ⟨1022855, by rfl⟩ : syracuseStep 1363807 = 2045711) B2045711
theorem B2043755 : Blo 1362500 2043755 := bstep (se 1 (by rfl) ⟨1532816, by rfl⟩ : syracuseStep 2043755 = 3065633) B3065633
theorem B7982957 : Blo 1362500 7982957 := bstep (se 3 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 7982957 = 2993609) B2993609
theorem B1363835 : Blo 1362500 1363835 := bstep (se 1 (by rfl) ⟨1022876, by rfl⟩ : syracuseStep 1363835 = 2045753) B2045753
theorem B1363887 : Blo 1362500 1363887 := bstep (se 1 (by rfl) ⟨1022915, by rfl⟩ : syracuseStep 1363887 = 2045831) B2045831
theorem B1363911 : Blo 1362500 1363911 := bstep (se 1 (by rfl) ⟨1022933, by rfl⟩ : syracuseStep 1363911 = 2045867) B2045867
theorem B1363931 : Blo 1362500 1363931 := bstep (se 1 (by rfl) ⟨1022948, by rfl⟩ : syracuseStep 1363931 = 2045897) B2045897
theorem B4599827 : Blo 1362500 4599827 := bstep (se 1 (by rfl) ⟨3449870, by rfl⟩ : syracuseStep 4599827 = 6899741) B6899741
theorem B1364007 : Blo 1362500 1364007 := bstep (se 1 (by rfl) ⟨1023005, by rfl⟩ : syracuseStep 1364007 = 2046011) B2046011
theorem B2043983 : Blo 1362500 2043983 := bstep (se 1 (by rfl) ⟨1532987, by rfl⟩ : syracuseStep 2043983 = 3065975) B3065975
theorem B1364047 : Blo 1362500 1364047 := bstep (se 1 (by rfl) ⟨1023035, by rfl⟩ : syracuseStep 1364047 = 2046071) B2046071
theorem B5820497 : Blo 1362500 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B1364063 : Blo 1362500 1364063 := bstep (se 1 (by rfl) ⟨1023047, by rfl⟩ : syracuseStep 1364063 = 2046095) B2046095
theorem B1364091 : Blo 1362500 1364091 := bstep (se 1 (by rfl) ⟨1023068, by rfl⟩ : syracuseStep 1364091 = 2046137) B2046137
theorem B10498211 : Blo 1362500 10498211 := bstep (se 1 (by rfl) ⟨7873658, by rfl⟩ : syracuseStep 10498211 = 15747317) B15747317
theorem B1364143 : Blo 1362500 1364143 := bstep (se 1 (by rfl) ⟨1023107, by rfl⟩ : syracuseStep 1364143 = 2046215) B2046215
theorem B2044103 : Blo 1362500 2044103 := bstep (se 1 (by rfl) ⟨1533077, by rfl⟩ : syracuseStep 2044103 = 3066155) B3066155
theorem B1364167 : Blo 1362500 1364167 := bstep (se 1 (by rfl) ⟨1023125, by rfl⟩ : syracuseStep 1364167 = 2046251) B2046251
theorem B1364187 : Blo 1362500 1364187 := bstep (se 1 (by rfl) ⟨1023140, by rfl⟩ : syracuseStep 1364187 = 2046281) B2046281
theorem B8736997 : Blo 1362500 8736997 := bstep (se 4 (by rfl) ⟨819093, by rfl⟩ : syracuseStep 8736997 = 1638187) B1638187
theorem B1364263 : Blo 1362500 1364263 := bstep (se 1 (by rfl) ⟨1023197, by rfl⟩ : syracuseStep 1364263 = 2046395) B2046395
theorem B10359089 : Blo 1362500 10359089 := bstep (se 2 (by rfl) ⟨3884658, by rfl⟩ : syracuseStep 10359089 = 7769317) B7769317
theorem B1364303 : Blo 1362500 1364303 := bstep (se 1 (by rfl) ⟨1023227, by rfl⟩ : syracuseStep 1364303 = 2046455) B2046455
theorem B5173591 : Blo 1362500 5173591 := bstep (se 1 (by rfl) ⟨3880193, by rfl⟩ : syracuseStep 5173591 = 7760387) B7760387
theorem B4600151 : Blo 1362500 4600151 := bstep (se 1 (by rfl) ⟨3450113, by rfl⟩ : syracuseStep 4600151 = 6900227) B6900227
theorem B1364319 : Blo 1362500 1364319 := bstep (se 1 (by rfl) ⟨1023239, by rfl⟩ : syracuseStep 1364319 = 2046479) B2046479
theorem B2044265 : Blo 1362500 2044265 := bstep (se 2 (by rfl) ⟨766599, by rfl⟩ : syracuseStep 2044265 = 1533199) B1533199
theorem B1364347 : Blo 1362500 1364347 := bstep (se 1 (by rfl) ⟨1023260, by rfl⟩ : syracuseStep 1364347 = 2046521) B2046521
theorem B3453313 : Blo 1362500 3453313 := bstep (se 2 (by rfl) ⟨1294992, by rfl⟩ : syracuseStep 3453313 = 2589985) B2589985
theorem B1364399 : Blo 1362500 1364399 := bstep (se 1 (by rfl) ⟨1023299, by rfl⟩ : syracuseStep 1364399 = 2046599) B2046599
theorem B2044343 : Blo 1362500 2044343 := bstep (se 1 (by rfl) ⟨1533257, by rfl⟩ : syracuseStep 2044343 = 3066515) B3066515
theorem B1364423 : Blo 1362500 1364423 := bstep (se 1 (by rfl) ⟨1023317, by rfl⟩ : syracuseStep 1364423 = 2046635) B2046635
theorem B2044379 : Blo 1362500 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B1364443 : Blo 1362500 1364443 := bstep (se 1 (by rfl) ⟨1023332, by rfl⟩ : syracuseStep 1364443 = 2046665) B2046665
theorem B2912777 : Blo 1362500 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B3068513 : Blo 1362500 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B5173895 : Blo 1362500 5173895 := bstep (se 1 (by rfl) ⟨3880421, by rfl⟩ : syracuseStep 5173895 = 7760843) B7760843
theorem B9835181 : Blo 1362500 9835181 := bstep (se 3 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 9835181 = 3688193) B3688193
theorem B10351313 : Blo 1362500 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B20476745 : Blo 1362500 20476745 := bstep (se 2 (by rfl) ⟨7678779, by rfl⟩ : syracuseStep 20476745 = 15357559) B15357559
theorem B2044847 : Blo 1362500 2044847 := bstep (se 1 (by rfl) ⟨1533635, by rfl⟩ : syracuseStep 2044847 = 3067271) B3067271
theorem B3068855 : Blo 1362500 3068855 := bstep (se 1 (by rfl) ⟨2301641, by rfl⟩ : syracuseStep 3068855 = 4603283) B4603283
theorem B2044937 : Blo 1362500 2044937 := bstep (se 2 (by rfl) ⟨766851, by rfl⟩ : syracuseStep 2044937 = 1533703) B1533703
theorem B2044967 : Blo 1362500 2044967 := bstep (se 1 (by rfl) ⟨1533725, by rfl⟩ : syracuseStep 2044967 = 3067451) B3067451
theorem B5174351 : Blo 1362500 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B2045051 : Blo 1362500 2045051 := bstep (se 1 (by rfl) ⟨1533788, by rfl⟩ : syracuseStep 2045051 = 3067577) B3067577
theorem B1725563 : Blo 1362500 1725563 := bstep (se 1 (by rfl) ⟨1294172, by rfl⟩ : syracuseStep 1725563 = 2588345) B2588345
theorem B17700041 : Blo 1362500 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B3880183 : Blo 1362500 3880183 := bstep (se 1 (by rfl) ⟨2910137, by rfl⟩ : syracuseStep 3880183 = 5820275) B5820275
theorem B2045177 : Blo 1362500 2045177 := bstep (se 2 (by rfl) ⟨766941, by rfl⟩ : syracuseStep 2045177 = 1533883) B1533883
theorem B2045279 : Blo 1362500 2045279 := bstep (se 1 (by rfl) ⟨1533959, by rfl⟩ : syracuseStep 2045279 = 3067919) B3067919
theorem B2045291 : Blo 1362500 2045291 := bstep (se 1 (by rfl) ⟨1533968, by rfl⟩ : syracuseStep 2045291 = 3067937) B3067937
theorem B2299279 : Blo 1362500 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B4601231 : Blo 1362500 4601231 := bstep (se 1 (by rfl) ⟨3450923, by rfl⟩ : syracuseStep 4601231 = 6901847) B6901847
theorem B13284773 : Blo 1362500 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B2020783 : Blo 1362500 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B5821915 : Blo 1362500 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B3880457 : Blo 1362500 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B19650059 : Blo 1362500 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B3069449 : Blo 1362500 3069449 := bstep (se 2 (by rfl) ⟨1151043, by rfl⟩ : syracuseStep 3069449 = 2302087) B2302087
theorem B2045519 : Blo 1362500 2045519 := bstep (se 1 (by rfl) ⟨1534139, by rfl⟩ : syracuseStep 2045519 = 3068279) B3068279
theorem B6641297 : Blo 1362500 6641297 := bstep (se 2 (by rfl) ⟨2490486, by rfl⟩ : syracuseStep 6641297 = 4980973) B4980973
theorem B17471123 : Blo 1362500 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B41965249 : Blo 1362500 41965249 := bstep (se 2 (by rfl) ⟨15736968, by rfl⟩ : syracuseStep 41965249 = 31473937) B31473937
theorem B2045639 : Blo 1362500 2045639 := bstep (se 1 (by rfl) ⟨1534229, by rfl⟩ : syracuseStep 2045639 = 3068459) B3068459
theorem B4601555 : Blo 1362500 4601555 := bstep (se 1 (by rfl) ⟨3451166, by rfl⟩ : syracuseStep 4601555 = 6902333) B6902333
theorem B3069791 : Blo 1362500 3069791 := bstep (se 1 (by rfl) ⟨2302343, by rfl⟩ : syracuseStep 3069791 = 4604687) B4604687
theorem B2045801 : Blo 1362500 2045801 := bstep (se 2 (by rfl) ⟨767175, by rfl⟩ : syracuseStep 2045801 = 1534351) B1534351
theorem B2045879 : Blo 1362500 2045879 := bstep (se 1 (by rfl) ⟨1534409, by rfl⟩ : syracuseStep 2045879 = 3068819) B3068819
theorem B2185147 : Blo 1362500 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B2045915 : Blo 1362500 2045915 := bstep (se 1 (by rfl) ⟨1534436, by rfl⟩ : syracuseStep 2045915 = 3068873) B3068873
theorem B2185223 : Blo 1362500 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B3069971 : Blo 1362500 3069971 := bstep (se 1 (by rfl) ⟨2302478, by rfl⟩ : syracuseStep 3069971 = 4604957) B4604957
theorem B2299961 : Blo 1362500 2299961 := bstep (se 2 (by rfl) ⟨862485, by rfl⟩ : syracuseStep 2299961 = 1724971) B1724971
theorem B5175353 : Blo 1362500 5175353 := bstep (se 2 (by rfl) ⟨1940757, by rfl⟩ : syracuseStep 5175353 = 3881515) B3881515
theorem B4200605 : Blo 1362500 4200605 := bstep (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) B1575227
theorem B26220833 : Blo 1362500 26220833 := bstep (se 2 (by rfl) ⟨9832812, by rfl⟩ : syracuseStep 26220833 = 19665625) B19665625
theorem B2455913 : Blo 1362500 2455913 := bstep (se 2 (by rfl) ⟨920967, by rfl⟩ : syracuseStep 2455913 = 1841935) B1841935
theorem B7469441 : Blo 1362500 7469441 := bstep (se 2 (by rfl) ⟨2801040, by rfl⟩ : syracuseStep 7469441 = 5602081) B5602081
theorem B2046383 : Blo 1362500 2046383 := bstep (se 1 (by rfl) ⟨1534787, by rfl⟩ : syracuseStep 2046383 = 3069575) B3069575
theorem B3881459 : Blo 1362500 3881459 := bstep (se 1 (by rfl) ⟨2911094, by rfl⟩ : syracuseStep 3881459 = 5822189) B5822189
theorem B2046473 : Blo 1362500 2046473 := bstep (se 2 (by rfl) ⟨767427, by rfl⟩ : syracuseStep 2046473 = 1534855) B1534855
theorem B2046503 : Blo 1362500 2046503 := bstep (se 1 (by rfl) ⟨1534877, by rfl⟩ : syracuseStep 2046503 = 3069755) B3069755
theorem B2046587 : Blo 1362500 2046587 := bstep (se 1 (by rfl) ⟨1534940, by rfl⟩ : syracuseStep 2046587 = 3069881) B3069881
theorem B17947271 : Blo 1362500 17947271 := bstep (se 1 (by rfl) ⟨13460453, by rfl⟩ : syracuseStep 17947271 = 26920907) B26920907
theorem B5823161 : Blo 1362500 5823161 := bstep (se 2 (by rfl) ⟨2183685, by rfl⟩ : syracuseStep 5823161 = 4367371) B4367371
theorem B5176007 : Blo 1362500 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B7092947 : Blo 1362500 7092947 := bstep (se 1 (by rfl) ⟨5319710, by rfl⟩ : syracuseStep 7092947 = 10639421) B10639421
theorem B2300663 : Blo 1362500 2300663 := bstep (se 1 (by rfl) ⟨1725497, by rfl⟩ : syracuseStep 2300663 = 3450995) B3450995
theorem B2046713 : Blo 1362500 2046713 := bstep (se 2 (by rfl) ⟨767517, by rfl⟩ : syracuseStep 2046713 = 1535035) B1535035
theorem B5528429 : Blo 1362500 5528429 := bstep (se 3 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 5528429 = 2073161) B2073161
theorem B4602743 : Blo 1362500 4602743 := bstep (se 1 (by rfl) ⟨3452057, by rfl⟩ : syracuseStep 4602743 = 6904115) B6904115
theorem B3881915 : Blo 1362500 3881915 := bstep (se 1 (by rfl) ⟨2911436, by rfl⟩ : syracuseStep 3881915 = 5822873) B5822873
theorem B4430855 : Blo 1362500 4430855 := bstep (se 1 (by rfl) ⟨3323141, by rfl⟩ : syracuseStep 4430855 = 6646283) B6646283
theorem B10353743 : Blo 1362500 10353743 := bstep (se 1 (by rfl) ⟨7765307, by rfl⟩ : syracuseStep 10353743 = 15530615) B15530615
theorem B2301007 : Blo 1362500 2301007 := bstep (se 1 (by rfl) ⟨1725755, by rfl⟩ : syracuseStep 2301007 = 3451511) B3451511
theorem B4602959 : Blo 1362500 4602959 := bstep (se 1 (by rfl) ⟨3452219, by rfl⟩ : syracuseStep 4602959 = 6904439) B6904439
theorem B6216857 : Blo 1362500 6216857 := bstep (se 2 (by rfl) ⟨2331321, by rfl⟩ : syracuseStep 6216857 = 4662643) B4662643
theorem B2587859 : Blo 1362500 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B4365629 : Blo 1362500 4365629 := bstep (se 3 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 4365629 = 1637111) B1637111
theorem B2301257 : Blo 1362500 2301257 := bstep (se 2 (by rfl) ⟨862971, by rfl⟩ : syracuseStep 2301257 = 1725943) B1725943
theorem B1842539 : Blo 1362500 1842539 := bstep (se 1 (by rfl) ⟨1381904, by rfl⟩ : syracuseStep 1842539 = 2763809) B2763809
theorem B2588087 : Blo 1362500 2588087 := bstep (se 1 (by rfl) ⟨1941065, by rfl⟩ : syracuseStep 2588087 = 3882131) B3882131
theorem B4603337 : Blo 1362500 4603337 := bstep (se 2 (by rfl) ⟨1726251, by rfl⟩ : syracuseStep 4603337 = 3452503) B3452503
theorem B11640307 : Blo 1362500 11640307 := bstep (se 1 (by rfl) ⟨8730230, by rfl⟩ : syracuseStep 11640307 = 17460461) B17460461
theorem B1941031 : Blo 1362500 1941031 := bstep (se 1 (by rfl) ⟨1455773, by rfl⟩ : syracuseStep 1941031 = 2911547) B2911547
theorem B5176979 : Blo 1362500 5176979 := bstep (se 1 (by rfl) ⟨3882734, by rfl⟩ : syracuseStep 5176979 = 7765469) B7765469
theorem B5250707 : Blo 1362500 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B4603607 : Blo 1362500 4603607 := bstep (se 1 (by rfl) ⟨3452705, by rfl⟩ : syracuseStep 4603607 = 6905411) B6905411
theorem B3882745 : Blo 1362500 3882745 := bstep (se 2 (by rfl) ⟨1456029, by rfl⟩ : syracuseStep 3882745 = 2912059) B2912059
theorem B2301689 : Blo 1362500 2301689 := bstep (se 2 (by rfl) ⟨863133, by rfl⟩ : syracuseStep 2301689 = 1726267) B1726267
theorem B2301871 : Blo 1362500 2301871 := bstep (se 1 (by rfl) ⟨1726403, by rfl⟩ : syracuseStep 2301871 = 3452807) B3452807
theorem B4603823 : Blo 1362500 4603823 := bstep (se 1 (by rfl) ⟨3452867, by rfl⟩ : syracuseStep 4603823 = 6905735) B6905735
theorem B11960473 : Blo 1362500 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B6906059 : Blo 1362500 6906059 := bstep (se 1 (by rfl) ⟨5179544, by rfl⟩ : syracuseStep 6906059 = 10359089) B10359089
theorem B6996179 : Blo 1362500 6996179 := bstep (se 1 (by rfl) ⟨5247134, by rfl⟩ : syracuseStep 6996179 = 10494269) B10494269
theorem B11649329 : Blo 1362500 11649329 := bstep (se 2 (by rfl) ⟨4368498, by rfl⟩ : syracuseStep 11649329 = 8736997) B8736997
theorem B1941851 : Blo 1362500 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B3449263 : Blo 1362500 3449263 := bstep (se 1 (by rfl) ⟨2586947, by rfl⟩ : syracuseStep 3449263 = 5173895) B5173895
theorem B6898121 : Blo 1362500 6898121 := bstep (se 2 (by rfl) ⟨2586795, by rfl⟩ : syracuseStep 6898121 = 5173591) B5173591
theorem B2245115 : Blo 1362500 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B10355201 : Blo 1362500 10355201 := bstep (se 2 (by rfl) ⟨3883200, by rfl⟩ : syracuseStep 10355201 = 7766401) B7766401
theorem B4604417 : Blo 1362500 4604417 := bstep (se 2 (by rfl) ⟨1726656, by rfl⟩ : syracuseStep 4604417 = 3453313) B3453313
theorem B7766675 : Blo 1362500 7766675 := bstep (se 1 (by rfl) ⟨5825006, by rfl⟩ : syracuseStep 7766675 = 11650013) B11650013
theorem B3449567 : Blo 1362500 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B10347425 : Blo 1362500 10347425 := bstep (se 2 (by rfl) ⟨3880284, by rfl⟩ : syracuseStep 10347425 = 7760569) B7760569
theorem B8856515 : Blo 1362500 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B12469211 : Blo 1362500 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B10355687 : Blo 1362500 10355687 := bstep (se 1 (by rfl) ⟨7766765, by rfl⟩ : syracuseStep 10355687 = 15533531) B15533531
theorem B4604903 : Blo 1362500 4604903 := bstep (se 1 (by rfl) ⟨3453677, by rfl⟩ : syracuseStep 4604903 = 6907355) B6907355
theorem B13100039 : Blo 1362500 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B19653749 : Blo 1362500 19653749 := bstep (se 5 (by rfl) ⟨921269, by rfl⟩ : syracuseStep 19653749 = 1842539) B1842539
theorem B6898931 : Blo 1362500 6898931 := bstep (se 1 (by rfl) ⟨5174198, by rfl⟩ : syracuseStep 6898931 = 10348397) B10348397
theorem B11650391 : Blo 1362500 11650391 := bstep (se 1 (by rfl) ⟨8737793, by rfl⟩ : syracuseStep 11650391 = 17475587) B17475587
theorem B1533307 : Blo 1362500 1533307 := bstep (se 1 (by rfl) ⟨1149980, by rfl⟩ : syracuseStep 1533307 = 2299961) B2299961
theorem B3450235 : Blo 1362500 3450235 := bstep (se 1 (by rfl) ⟨2587676, by rfl⟩ : syracuseStep 3450235 = 5175353) B5175353
theorem B7366049 : Blo 1362500 7366049 := bstep (se 2 (by rfl) ⟨2762268, by rfl⟩ : syracuseStep 7366049 = 5524537) B5524537
theorem B5178937 : Blo 1362500 5178937 := bstep (se 2 (by rfl) ⟨1942101, by rfl⟩ : syracuseStep 5178937 = 3884203) B3884203
theorem B23291549 : Blo 1362500 23291549 := bstep (se 3 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 23291549 = 8734331) B8734331
theorem B3450671 : Blo 1362500 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B4728631 : Blo 1362500 4728631 := bstep (se 1 (by rfl) ⟨3546473, by rfl⟩ : syracuseStep 4728631 = 7092947) B7092947
theorem B1533775 : Blo 1362500 1533775 := bstep (se 1 (by rfl) ⟨1150331, by rfl⟩ : syracuseStep 1533775 = 2300663) B2300663
theorem B3065705 : Blo 1362500 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B14935913 : Blo 1362500 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B5179241 : Blo 1362500 5179241 := bstep (se 2 (by rfl) ⟨1942215, by rfl⟩ : syracuseStep 5179241 = 3884431) B3884431
theorem B7375043 : Blo 1362500 7375043 := bstep (se 1 (by rfl) ⟨5531282, by rfl⟩ : syracuseStep 7375043 = 11062565) B11062565
theorem B2910419 : Blo 1362500 2910419 := bstep (se 1 (by rfl) ⟨2182814, by rfl⟩ : syracuseStep 2910419 = 4365629) B4365629
theorem B1534171 : Blo 1362500 1534171 := bstep (se 1 (by rfl) ⟨1150628, by rfl⟩ : syracuseStep 1534171 = 2301257) B2301257
theorem B55953665 : Blo 1362500 55953665 := bstep (se 2 (by rfl) ⟨20982624, by rfl⟩ : syracuseStep 55953665 = 41965249) B41965249
theorem B3885479 : Blo 1362500 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B3451319 : Blo 1362500 3451319 := bstep (se 1 (by rfl) ⟨2588489, by rfl⟩ : syracuseStep 3451319 = 5176979) B5176979
theorem B3500471 : Blo 1362500 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B1534459 : Blo 1362500 1534459 := bstep (se 1 (by rfl) ⟨1150844, by rfl⟩ : syracuseStep 1534459 = 2301689) B2301689
theorem B1362503 : Blo 1362500 1362503 := bstep (se 1 (by rfl) ⟨1021877, by rfl⟩ : syracuseStep 1362503 = 2043755) B2043755
theorem B1534639 : Blo 1362500 1534639 := bstep (se 1 (by rfl) ⟨1150979, by rfl⟩ : syracuseStep 1534639 = 2301959) B2301959
theorem B5827247 : Blo 1362500 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B3066551 : Blo 1362500 3066551 := bstep (se 1 (by rfl) ⟨2299913, by rfl⟩ : syracuseStep 3066551 = 4599827) B4599827
theorem B1362655 : Blo 1362500 1362655 := bstep (se 1 (by rfl) ⟨1021991, by rfl⟩ : syracuseStep 1362655 = 2043983) B2043983
theorem B23309045 : Blo 1362500 23309045 := bstep (se 5 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 23309045 = 2185223) B2185223
theorem B6998807 : Blo 1362500 6998807 := bstep (se 1 (by rfl) ⟨5249105, by rfl⟩ : syracuseStep 6998807 = 10498211) B10498211
theorem B6556439 : Blo 1362500 6556439 := bstep (se 1 (by rfl) ⟨4917329, by rfl⟩ : syracuseStep 6556439 = 9834659) B9834659
theorem B1362735 : Blo 1362500 1362735 := bstep (se 1 (by rfl) ⟨1022051, by rfl⟩ : syracuseStep 1362735 = 2044103) B2044103
theorem B3066767 : Blo 1362500 3066767 := bstep (se 1 (by rfl) ⟨2300075, by rfl⟩ : syracuseStep 3066767 = 4600151) B4600151
theorem B1362843 : Blo 1362500 1362843 := bstep (se 1 (by rfl) ⟨1022132, by rfl⟩ : syracuseStep 1362843 = 2044265) B2044265
theorem B5319595 : Blo 1362500 5319595 := bstep (se 1 (by rfl) ⟨3989696, by rfl⟩ : syracuseStep 5319595 = 7979393) B7979393
theorem B1362895 : Blo 1362500 1362895 := bstep (se 1 (by rfl) ⟨1022171, by rfl⟩ : syracuseStep 1362895 = 2044343) B2044343
theorem B1534927 : Blo 1362500 1534927 := bstep (se 1 (by rfl) ⟨1151195, by rfl⟩ : syracuseStep 1534927 = 2302391) B2302391
theorem B1362919 : Blo 1362500 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B5827571 : Blo 1362500 5827571 := bstep (se 1 (by rfl) ⟨4370678, by rfl⟩ : syracuseStep 5827571 = 8741357) B8741357
theorem B6556787 : Blo 1362500 6556787 := bstep (se 1 (by rfl) ⟨4917590, by rfl⟩ : syracuseStep 6556787 = 9835181) B9835181
theorem B6900875 : Blo 1362500 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B13651163 : Blo 1362500 13651163 := bstep (se 1 (by rfl) ⟨10238372, by rfl⟩ : syracuseStep 13651163 = 20476745) B20476745
theorem B4599071 : Blo 1362500 4599071 := bstep (se 1 (by rfl) ⟨3449303, by rfl⟩ : syracuseStep 4599071 = 6898607) B6898607
theorem B10349855 : Blo 1362500 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B1363231 : Blo 1362500 1363231 := bstep (se 1 (by rfl) ⟨1022423, by rfl⟩ : syracuseStep 1363231 = 2044847) B2044847
theorem B1363291 : Blo 1362500 1363291 := bstep (se 1 (by rfl) ⟨1022468, by rfl⟩ : syracuseStep 1363291 = 2044937) B2044937
theorem B1363311 : Blo 1362500 1363311 := bstep (se 1 (by rfl) ⟨1022483, by rfl⟩ : syracuseStep 1363311 = 2044967) B2044967
theorem B29470067 : Blo 1362500 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B3452321 : Blo 1362500 3452321 := bstep (se 2 (by rfl) ⟨1294620, by rfl⟩ : syracuseStep 3452321 = 2589241) B2589241
theorem B1363367 : Blo 1362500 1363367 := bstep (se 1 (by rfl) ⟨1022525, by rfl⟩ : syracuseStep 1363367 = 2045051) B2045051
theorem B11800027 : Blo 1362500 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B1363451 : Blo 1362500 1363451 := bstep (se 1 (by rfl) ⟨1022588, by rfl⟩ : syracuseStep 1363451 = 2045177) B2045177
theorem B1363519 : Blo 1362500 1363519 := bstep (se 1 (by rfl) ⟨1022639, by rfl⟩ : syracuseStep 1363519 = 2045279) B2045279
theorem B1363527 : Blo 1362500 1363527 := bstep (se 1 (by rfl) ⟨1022645, by rfl⟩ : syracuseStep 1363527 = 2045291) B2045291
theorem B3067487 : Blo 1362500 3067487 := bstep (se 1 (by rfl) ⟨2300615, by rfl⟩ : syracuseStep 3067487 = 4601231) B4601231
theorem B1363679 : Blo 1362500 1363679 := bstep (se 1 (by rfl) ⟨1022759, by rfl⟩ : syracuseStep 1363679 = 2045519) B2045519
theorem B4427531 : Blo 1362500 4427531 := bstep (se 1 (by rfl) ⟨3320648, by rfl⟩ : syracuseStep 4427531 = 6641297) B6641297
theorem B1363759 : Blo 1362500 1363759 := bstep (se 1 (by rfl) ⟨1022819, by rfl⟩ : syracuseStep 1363759 = 2045639) B2045639
theorem B3067703 : Blo 1362500 3067703 := bstep (se 1 (by rfl) ⟨2300777, by rfl⟩ : syracuseStep 3067703 = 4601555) B4601555
theorem B5320505 : Blo 1362500 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B3452777 : Blo 1362500 3452777 := bstep (se 2 (by rfl) ⟨1294791, by rfl⟩ : syracuseStep 3452777 = 2589583) B2589583
theorem B1363867 : Blo 1362500 1363867 := bstep (se 1 (by rfl) ⟨1022900, by rfl⟩ : syracuseStep 1363867 = 2045801) B2045801
theorem B1363919 : Blo 1362500 1363919 := bstep (se 1 (by rfl) ⟨1022939, by rfl⟩ : syracuseStep 1363919 = 2045879) B2045879
theorem B1363943 : Blo 1362500 1363943 := bstep (se 1 (by rfl) ⟨1022957, by rfl⟩ : syracuseStep 1363943 = 2045915) B2045915
theorem B3068009 : Blo 1362500 3068009 := bstep (se 2 (by rfl) ⟨1150503, by rfl⟩ : syracuseStep 3068009 = 2301007) B2301007
theorem B4370537 : Blo 1362500 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B2044169 : Blo 1362500 2044169 := bstep (se 2 (by rfl) ⟨766563, by rfl⟩ : syracuseStep 2044169 = 1533127) B1533127
theorem B1364255 : Blo 1362500 1364255 := bstep (se 1 (by rfl) ⟨1023191, by rfl⟩ : syracuseStep 1364255 = 2046383) B2046383
theorem B5173577 : Blo 1362500 5173577 := bstep (se 2 (by rfl) ⟨1940091, by rfl⟩ : syracuseStep 5173577 = 3880183) B3880183
theorem B1364315 : Blo 1362500 1364315 := bstep (se 1 (by rfl) ⟨1023236, by rfl⟩ : syracuseStep 1364315 = 2046473) B2046473
theorem B2044271 : Blo 1362500 2044271 := bstep (se 1 (by rfl) ⟨1533203, by rfl⟩ : syracuseStep 2044271 = 3066407) B3066407
theorem B1364335 : Blo 1362500 1364335 := bstep (se 1 (by rfl) ⟨1023251, by rfl⟩ : syracuseStep 1364335 = 2046503) B2046503
theorem B1364391 : Blo 1362500 1364391 := bstep (se 1 (by rfl) ⟨1023293, by rfl⟩ : syracuseStep 1364391 = 2046587) B2046587
theorem B11964847 : Blo 1362500 11964847 := bstep (se 1 (by rfl) ⟨8973635, by rfl⟩ : syracuseStep 11964847 = 17947271) B17947271
theorem B1364475 : Blo 1362500 1364475 := bstep (se 1 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 1364475 = 2046713) B2046713
theorem B2044487 : Blo 1362500 2044487 := bstep (se 1 (by rfl) ⟨1533365, by rfl⟩ : syracuseStep 2044487 = 3066731) B3066731
theorem B3068495 : Blo 1362500 3068495 := bstep (se 1 (by rfl) ⟨2301371, by rfl⟩ : syracuseStep 3068495 = 4602743) B4602743
theorem B2044523 : Blo 1362500 2044523 := bstep (se 1 (by rfl) ⟨1533392, by rfl⟩ : syracuseStep 2044523 = 3066785) B3066785
theorem B7762553 : Blo 1362500 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B15520409 : Blo 1362500 15520409 := bstep (se 2 (by rfl) ⟨5820153, by rfl⟩ : syracuseStep 15520409 = 11640307) B11640307
theorem B2953903 : Blo 1362500 2953903 := bstep (se 1 (by rfl) ⟨2215427, by rfl⟩ : syracuseStep 2953903 = 4430855) B4430855
theorem B11645639 : Blo 1362500 11645639 := bstep (se 1 (by rfl) ⟨8734229, by rfl⟩ : syracuseStep 11645639 = 17468459) B17468459
theorem B6902495 : Blo 1362500 6902495 := bstep (se 1 (by rfl) ⟨5176871, by rfl⟩ : syracuseStep 6902495 = 10353743) B10353743
theorem B3068639 : Blo 1362500 3068639 := bstep (se 1 (by rfl) ⟨2301479, by rfl⟩ : syracuseStep 3068639 = 4602959) B4602959
theorem B1725239 : Blo 1362500 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B2044751 : Blo 1362500 2044751 := bstep (se 1 (by rfl) ⟨1533563, by rfl⟩ : syracuseStep 2044751 = 3067127) B3067127
theorem B15143881 : Blo 1362500 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B1725391 : Blo 1362500 1725391 := bstep (se 1 (by rfl) ⟨1294043, by rfl⟩ : syracuseStep 1725391 = 2588087) B2588087
theorem B3068891 : Blo 1362500 3068891 := bstep (se 1 (by rfl) ⟨2301668, by rfl⟩ : syracuseStep 3068891 = 4603337) B4603337
theorem B3069071 : Blo 1362500 3069071 := bstep (se 1 (by rfl) ⟨2301803, by rfl⟩ : syracuseStep 3069071 = 4603607) B4603607
theorem B2045147 : Blo 1362500 2045147 := bstep (se 1 (by rfl) ⟨1533860, by rfl⟩ : syracuseStep 2045147 = 3067721) B3067721
theorem B3069161 : Blo 1362500 3069161 := bstep (se 2 (by rfl) ⟨1150935, by rfl⟩ : syracuseStep 3069161 = 2301871) B2301871
theorem B5321971 : Blo 1362500 5321971 := bstep (se 1 (by rfl) ⟨3991478, by rfl⟩ : syracuseStep 5321971 = 7982957) B7982957
theorem B2913529 : Blo 1362500 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B3069215 : Blo 1362500 3069215 := bstep (se 1 (by rfl) ⟨2301911, by rfl⟩ : syracuseStep 3069215 = 4603823) B4603823
theorem B2299259 : Blo 1362500 2299259 := bstep (se 1 (by rfl) ⟨1724444, by rfl⟩ : syracuseStep 2299259 = 3448889) B3448889
theorem B2045321 : Blo 1362500 2045321 := bstep (se 2 (by rfl) ⟨766995, by rfl⟩ : syracuseStep 2045321 = 1533991) B1533991
theorem B3880331 : Blo 1362500 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B4601501 : Blo 1362500 4601501 := bstep (se 3 (by rfl) ⟨862781, by rfl⟩ : syracuseStep 4601501 = 1725563) B1725563
theorem B2045675 : Blo 1362500 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B3069737 : Blo 1362500 3069737 := bstep (se 2 (by rfl) ⟨1151151, by rfl⟩ : syracuseStep 3069737 = 2302303) B2302303
theorem B1726363 : Blo 1362500 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1382351 : Blo 1362500 1382351 := bstep (se 1 (by rfl) ⟨1036763, by rfl⟩ : syracuseStep 1382351 = 2073527) B2073527
theorem B2045903 : Blo 1362500 2045903 := bstep (se 1 (by rfl) ⟨1534427, by rfl⟩ : syracuseStep 2045903 = 3068855) B3068855
theorem B4602041 : Blo 1362500 4602041 := bstep (se 2 (by rfl) ⟨1725765, by rfl⟩ : syracuseStep 4602041 = 3451531) B3451531
theorem B2586971 : Blo 1362500 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B2300251 : Blo 1362500 2300251 := bstep (se 1 (by rfl) ⟨1725188, by rfl⟩ : syracuseStep 2300251 = 3450377) B3450377
theorem B2046299 : Blo 1362500 2046299 := bstep (se 1 (by rfl) ⟨1534724, by rfl⟩ : syracuseStep 2046299 = 3069449) B3069449
theorem B11647415 : Blo 1362500 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B2046527 : Blo 1362500 2046527 := bstep (se 1 (by rfl) ⟨1534895, by rfl⟩ : syracuseStep 2046527 = 3069791) B3069791
theorem B10361519 : Blo 1362500 10361519 := bstep (se 1 (by rfl) ⟨7771139, by rfl⟩ : syracuseStep 10361519 = 15542279) B15542279
theorem B2046647 : Blo 1362500 2046647 := bstep (se 1 (by rfl) ⟨1534985, by rfl⟩ : syracuseStep 2046647 = 3069971) B3069971
theorem B2800403 : Blo 1362500 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B17480555 : Blo 1362500 17480555 := bstep (se 1 (by rfl) ⟨13110416, by rfl⟩ : syracuseStep 17480555 = 26220833) B26220833
theorem B1637275 : Blo 1362500 1637275 := bstep (se 1 (by rfl) ⟨1227956, by rfl⟩ : syracuseStep 1637275 = 2455913) B2455913
theorem B4979627 : Blo 1362500 4979627 := bstep (se 1 (by rfl) ⟨3734720, by rfl⟩ : syracuseStep 4979627 = 7469441) B7469441
theorem B6216635 : Blo 1362500 6216635 := bstep (se 1 (by rfl) ⟨4662476, by rfl⟩ : syracuseStep 6216635 = 9324953) B9324953
theorem B6904763 : Blo 1362500 6904763 := bstep (se 1 (by rfl) ⟨5178572, by rfl⟩ : syracuseStep 6904763 = 10357145) B10357145
theorem B2587639 : Blo 1362500 2587639 := bstep (se 1 (by rfl) ⟨1940729, by rfl⟩ : syracuseStep 2587639 = 3881459) B3881459
theorem B3882107 : Blo 1362500 3882107 := bstep (se 1 (by rfl) ⟨2911580, by rfl⟩ : syracuseStep 3882107 = 5823161) B5823161
theorem B2694377 : Blo 1362500 2694377 := bstep (se 2 (by rfl) ⟨1010391, by rfl⟩ : syracuseStep 2694377 = 2020783) B2020783
theorem B3685619 : Blo 1362500 3685619 := bstep (se 1 (by rfl) ⟨2764214, by rfl⟩ : syracuseStep 3685619 = 5528429) B5528429
theorem B2587943 : Blo 1362500 2587943 := bstep (se 1 (by rfl) ⟨1940957, by rfl⟩ : syracuseStep 2587943 = 3881915) B3881915
theorem B2301223 : Blo 1362500 2301223 := bstep (se 1 (by rfl) ⟨1725917, by rfl⟩ : syracuseStep 2301223 = 3451835) B3451835
theorem B2588041 : Blo 1362500 2588041 := bstep (se 2 (by rfl) ⟨970515, by rfl⟩ : syracuseStep 2588041 = 1941031) B1941031
theorem B4144571 : Blo 1362500 4144571 := bstep (se 1 (by rfl) ⟨3108428, by rfl⟩ : syracuseStep 4144571 = 6216857) B6216857
theorem B3685945 : Blo 1362500 3685945 := bstep (se 2 (by rfl) ⟨1382229, by rfl⟩ : syracuseStep 3685945 = 2764459) B2764459
theorem B37305937 : Blo 1362500 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B5176993 : Blo 1362500 5176993 := bstep (se 2 (by rfl) ⟨1941372, by rfl⟩ : syracuseStep 5176993 = 3882745) B3882745
theorem B4603553 : Blo 1362500 4603553 := bstep (se 2 (by rfl) ⟨1726332, by rfl⟩ : syracuseStep 4603553 = 3452665) B3452665
theorem B2301743 : Blo 1362500 2301743 := bstep (se 1 (by rfl) ⟨1726307, by rfl⟩ : syracuseStep 2301743 = 3452615) B3452615
theorem B4604039 : Blo 1362500 4604039 := bstep (se 1 (by rfl) ⟨3453029, by rfl⟩ : syracuseStep 4604039 = 6906059) B6906059
theorem B7766219 : Blo 1362500 7766219 := bstep (se 1 (by rfl) ⟨5824664, by rfl⟩ : syracuseStep 7766219 = 11649329) B11649329
theorem B3449051 : Blo 1362500 3449051 := bstep (se 1 (by rfl) ⟨2586788, by rfl⟩ : syracuseStep 3449051 = 5173577) B5173577
theorem B5177783 : Blo 1362500 5177783 := bstep (se 1 (by rfl) ⟨3883337, by rfl⟩ : syracuseStep 5177783 = 7766675) B7766675
theorem B10346939 : Blo 1362500 10346939 := bstep (se 1 (by rfl) ⟨7760204, by rfl⟩ : syracuseStep 10346939 = 15520409) B15520409
theorem B6898283 : Blo 1362500 6898283 := bstep (se 1 (by rfl) ⟨5173712, by rfl⟩ : syracuseStep 6898283 = 10347425) B10347425
theorem B8733359 : Blo 1362500 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B7766927 : Blo 1362500 7766927 := bstep (se 1 (by rfl) ⟨5825195, by rfl⟩ : syracuseStep 7766927 = 11650391) B11650391
theorem B5178269 : Blo 1362500 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B1532839 : Blo 1362500 1532839 := bstep (se 1 (by rfl) ⟨1149629, by rfl⟩ : syracuseStep 1532839 = 2299259) B2299259
theorem B3450185 : Blo 1362500 3450185 := bstep (se 2 (by rfl) ⟨1293819, by rfl⟩ : syracuseStep 3450185 = 2587639) B2587639
theorem B4916695 : Blo 1362500 4916695 := bstep (se 1 (by rfl) ⟨3687521, by rfl⟩ : syracuseStep 4916695 = 7375043) B7375043
theorem B2590319 : Blo 1362500 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B7095961 : Blo 1362500 7095961 := bstep (se 2 (by rfl) ⟨2660985, by rfl⟩ : syracuseStep 7095961 = 5321971) B5321971
theorem B3884705 : Blo 1362500 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B3884831 : Blo 1362500 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B6907679 : Blo 1362500 6907679 := bstep (se 1 (by rfl) ⟨5180759, by rfl⟩ : syracuseStep 6907679 = 10361519) B10361519
theorem B3450721 : Blo 1362500 3450721 := bstep (se 2 (by rfl) ⟨1294020, by rfl⟩ : syracuseStep 3450721 = 2588041) B2588041
theorem B3319751 : Blo 1362500 3319751 := bstep (se 1 (by rfl) ⟨2489813, by rfl⟩ : syracuseStep 3319751 = 4979627) B4979627
theorem B3885047 : Blo 1362500 3885047 := bstep (se 1 (by rfl) ⟨2913785, by rfl⟩ : syracuseStep 3885047 = 5827571) B5827571
theorem B1796251 : Blo 1362500 1796251 := bstep (se 1 (by rfl) ⟨1347188, by rfl⟩ : syracuseStep 1796251 = 2694377) B2694377
theorem B3066047 : Blo 1362500 3066047 := bstep (se 1 (by rfl) ⟨2299535, by rfl⟩ : syracuseStep 3066047 = 4599071) B4599071
theorem B6899903 : Blo 1362500 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B19646711 : Blo 1362500 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B2763047 : Blo 1362500 2763047 := bstep (se 1 (by rfl) ⟨2072285, by rfl⟩ : syracuseStep 2763047 = 4144571) B4144571
theorem B2951687 : Blo 1362500 2951687 := bstep (se 1 (by rfl) ⟨2213765, by rfl⟩ : syracuseStep 2951687 = 4427531) B4427531
theorem B1534495 : Blo 1362500 1534495 := bstep (se 1 (by rfl) ⟨1150871, by rfl⟩ : syracuseStep 1534495 = 2301743) B2301743
theorem B1362779 : Blo 1362500 1362779 := bstep (se 1 (by rfl) ⟨1022084, by rfl⟩ : syracuseStep 1362779 = 2044169) B2044169
theorem B1362847 : Blo 1362500 1362847 := bstep (se 1 (by rfl) ⟨1022135, by rfl⟩ : syracuseStep 1362847 = 2044271) B2044271
theorem B4598747 : Blo 1362500 4598747 := bstep (se 1 (by rfl) ⟨3449060, by rfl⟩ : syracuseStep 4598747 = 6898121) B6898121
theorem B1362991 : Blo 1362500 1362991 := bstep (se 1 (by rfl) ⟨1022243, by rfl⟩ : syracuseStep 1362991 = 2044487) B2044487
theorem B1363015 : Blo 1362500 1363015 := bstep (se 1 (by rfl) ⟨1022261, by rfl⟩ : syracuseStep 1363015 = 2044523) B2044523
theorem B3067001 : Blo 1362500 3067001 := bstep (se 2 (by rfl) ⟨1150125, by rfl⟩ : syracuseStep 3067001 = 2300251) B2300251
theorem B18656477 : Blo 1362500 18656477 := bstep (se 3 (by rfl) ⟨3498089, by rfl⟩ : syracuseStep 18656477 = 6996179) B6996179
theorem B1363167 : Blo 1362500 1363167 := bstep (se 1 (by rfl) ⟨1022375, by rfl⟩ : syracuseStep 1363167 = 2044751) B2044751
theorem B4599017 : Blo 1362500 4599017 := bstep (se 2 (by rfl) ⟨1724631, by rfl⟩ : syracuseStep 4599017 = 3449263) B3449263
theorem B15953129 : Blo 1362500 15953129 := bstep (se 2 (by rfl) ⟨5982423, by rfl⟩ : syracuseStep 15953129 = 11964847) B11964847
theorem B13102499 : Blo 1362500 13102499 := bstep (se 1 (by rfl) ⟨9826874, by rfl⟩ : syracuseStep 13102499 = 19653749) B19653749
theorem B1363431 : Blo 1362500 1363431 := bstep (se 1 (by rfl) ⟨1022573, by rfl⟩ : syracuseStep 1363431 = 2045147) B2045147
theorem B4599287 : Blo 1362500 4599287 := bstep (se 1 (by rfl) ⟨3449465, by rfl⟩ : syracuseStep 4599287 = 6898931) B6898931
theorem B1363547 : Blo 1362500 1363547 := bstep (se 1 (by rfl) ⟨1022660, by rfl⟩ : syracuseStep 1363547 = 2045321) B2045321
theorem B4910699 : Blo 1362500 4910699 := bstep (se 1 (by rfl) ⟨3683024, by rfl⟩ : syracuseStep 4910699 = 7366049) B7366049
theorem B15527699 : Blo 1362500 15527699 := bstep (se 1 (by rfl) ⟨11645774, by rfl⟩ : syracuseStep 15527699 = 23291549) B23291549
theorem B3067667 : Blo 1362500 3067667 := bstep (se 1 (by rfl) ⟨2300750, by rfl⟩ : syracuseStep 3067667 = 4601501) B4601501
theorem B1363783 : Blo 1362500 1363783 := bstep (se 1 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 1363783 = 2045675) B2045675
theorem B2183033 : Blo 1362500 2183033 := bstep (se 2 (by rfl) ⟨818637, by rfl⟩ : syracuseStep 2183033 = 1637275) B1637275
theorem B2043803 : Blo 1362500 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B9957275 : Blo 1362500 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B3452827 : Blo 1362500 3452827 := bstep (se 1 (by rfl) ⟨2589620, by rfl⟩ : syracuseStep 3452827 = 5179241) B5179241
theorem B1363935 : Blo 1362500 1363935 := bstep (se 1 (by rfl) ⟨1022951, by rfl⟩ : syracuseStep 1363935 = 2045903) B2045903
theorem B3068027 : Blo 1362500 3068027 := bstep (se 1 (by rfl) ⟨2301020, by rfl⟩ : syracuseStep 3068027 = 4602041) B4602041
theorem B37302443 : Blo 1362500 37302443 := bstep (se 1 (by rfl) ⟨27976832, by rfl⟩ : syracuseStep 37302443 = 55953665) B55953665
theorem B1724647 : Blo 1362500 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B1364199 : Blo 1362500 1364199 := bstep (se 1 (by rfl) ⟨1023149, by rfl⟩ : syracuseStep 1364199 = 2046299) B2046299
theorem B1364351 : Blo 1362500 1364351 := bstep (se 1 (by rfl) ⟨1023263, by rfl⟩ : syracuseStep 1364351 = 2046527) B2046527
theorem B3068297 : Blo 1362500 3068297 := bstep (se 2 (by rfl) ⟨1150611, by rfl⟩ : syracuseStep 3068297 = 2301223) B2301223
theorem B2044367 : Blo 1362500 2044367 := bstep (se 1 (by rfl) ⟨1533275, by rfl⟩ : syracuseStep 2044367 = 3066551) B3066551
theorem B1364431 : Blo 1362500 1364431 := bstep (se 1 (by rfl) ⟨1023323, by rfl⟩ : syracuseStep 1364431 = 2046647) B2046647
theorem B2044409 : Blo 1362500 2044409 := bstep (se 2 (by rfl) ⟨766653, by rfl⟩ : syracuseStep 2044409 = 1533307) B1533307
theorem B4600313 : Blo 1362500 4600313 := bstep (se 2 (by rfl) ⟨1725117, by rfl⟩ : syracuseStep 4600313 = 3450235) B3450235
theorem B4665871 : Blo 1362500 4665871 := bstep (se 1 (by rfl) ⟨3499403, by rfl⟩ : syracuseStep 4665871 = 6998807) B6998807
theorem B4370959 : Blo 1362500 4370959 := bstep (se 1 (by rfl) ⟨3278219, by rfl⟩ : syracuseStep 4370959 = 6556439) B6556439
theorem B11653703 : Blo 1362500 11653703 := bstep (se 1 (by rfl) ⟨8740277, by rfl⟩ : syracuseStep 11653703 = 17480555) B17480555
theorem B2044511 : Blo 1362500 2044511 := bstep (se 1 (by rfl) ⟨1533383, by rfl⟩ : syracuseStep 2044511 = 3066767) B3066767
theorem B15733369 : Blo 1362500 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B4371191 : Blo 1362500 4371191 := bstep (se 1 (by rfl) ⟨3278393, by rfl⟩ : syracuseStep 4371191 = 6556787) B6556787
theorem B4600583 : Blo 1362500 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B4600637 : Blo 1362500 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B1725295 : Blo 1362500 1725295 := bstep (se 1 (by rfl) ⟨1293971, by rfl⟩ : syracuseStep 1725295 = 2587943) B2587943
theorem B6902657 : Blo 1362500 6902657 := bstep (se 2 (by rfl) ⟨2588496, by rfl⟩ : syracuseStep 6902657 = 5176993) B5176993
theorem B2044991 : Blo 1362500 2044991 := bstep (se 1 (by rfl) ⟨1533743, by rfl⟩ : syracuseStep 2044991 = 3067487) B3067487
theorem B6304841 : Blo 1362500 6304841 := bstep (se 2 (by rfl) ⟨2364315, by rfl⟩ : syracuseStep 6304841 = 4728631) B4728631
theorem B2045033 : Blo 1362500 2045033 := bstep (se 2 (by rfl) ⟨766887, by rfl⟩ : syracuseStep 2045033 = 1533775) B1533775
theorem B3069035 : Blo 1362500 3069035 := bstep (se 1 (by rfl) ⟨2301776, by rfl⟩ : syracuseStep 3069035 = 4603553) B4603553
theorem B16577693 : Blo 1362500 16577693 := bstep (se 3 (by rfl) ⟨3108317, by rfl⟩ : syracuseStep 16577693 = 6216635) B6216635
theorem B2045135 : Blo 1362500 2045135 := bstep (se 1 (by rfl) ⟨1533851, by rfl⟩ : syracuseStep 2045135 = 3067703) B3067703
theorem B2045339 : Blo 1362500 2045339 := bstep (se 1 (by rfl) ⟨1534004, by rfl⟩ : syracuseStep 2045339 = 3068009) B3068009
theorem B15947297 : Blo 1362500 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B11654765 : Blo 1362500 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B2045561 : Blo 1362500 2045561 := bstep (se 2 (by rfl) ⟨767085, by rfl⟩ : syracuseStep 2045561 = 1534171) B1534171
theorem B10352285 : Blo 1362500 10352285 := bstep (se 3 (by rfl) ⟨1941053, by rfl⟩ : syracuseStep 10352285 = 3882107) B3882107
theorem B6903467 : Blo 1362500 6903467 := bstep (se 1 (by rfl) ⟨5177600, by rfl⟩ : syracuseStep 6903467 = 10355201) B10355201
theorem B3069611 : Blo 1362500 3069611 := bstep (se 1 (by rfl) ⟨2302208, by rfl⟩ : syracuseStep 3069611 = 4604417) B4604417
theorem B2045663 : Blo 1362500 2045663 := bstep (se 1 (by rfl) ⟨1534247, by rfl⟩ : syracuseStep 2045663 = 3068495) B3068495
theorem B5175035 : Blo 1362500 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B7763759 : Blo 1362500 7763759 := bstep (se 1 (by rfl) ⟨5822819, by rfl⟩ : syracuseStep 7763759 = 11645639) B11645639
theorem B2299711 : Blo 1362500 2299711 := bstep (se 1 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 2299711 = 3449567) B3449567
theorem B4601663 : Blo 1362500 4601663 := bstep (se 1 (by rfl) ⟨3451247, by rfl⟩ : syracuseStep 4601663 = 6902495) B6902495
theorem B2045759 : Blo 1362500 2045759 := bstep (se 1 (by rfl) ⟨1534319, by rfl⟩ : syracuseStep 2045759 = 3068639) B3068639
theorem B5904343 : Blo 1362500 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B9828317 : Blo 1362500 9828317 := bstep (se 3 (by rfl) ⟨1842809, by rfl⟩ : syracuseStep 9828317 = 3685619) B3685619
theorem B2045927 : Blo 1362500 2045927 := bstep (se 1 (by rfl) ⟨1534445, by rfl⟩ : syracuseStep 2045927 = 3068891) B3068891
theorem B8312807 : Blo 1362500 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B6903791 : Blo 1362500 6903791 := bstep (se 1 (by rfl) ⟨5177843, by rfl⟩ : syracuseStep 6903791 = 10355687) B10355687
theorem B3069935 : Blo 1362500 3069935 := bstep (se 1 (by rfl) ⟨2302451, by rfl⟩ : syracuseStep 3069935 = 4604903) B4604903
theorem B2045945 : Blo 1362500 2045945 := bstep (se 2 (by rfl) ⟨767229, by rfl⟩ : syracuseStep 2045945 = 1534459) B1534459
theorem B2046047 : Blo 1362500 2046047 := bstep (se 1 (by rfl) ⟨1534535, by rfl⟩ : syracuseStep 2046047 = 3069071) B3069071
theorem B2046107 : Blo 1362500 2046107 := bstep (se 1 (by rfl) ⟨1534580, by rfl⟩ : syracuseStep 2046107 = 3069161) B3069161
theorem B2046143 : Blo 1362500 2046143 := bstep (se 1 (by rfl) ⟨1534607, by rfl⟩ : syracuseStep 2046143 = 3069215) B3069215
theorem B2046185 : Blo 1362500 2046185 := bstep (se 2 (by rfl) ⟨767319, by rfl⟩ : syracuseStep 2046185 = 1534639) B1534639
theorem B3938537 : Blo 1362500 3938537 := bstep (se 2 (by rfl) ⟨1476951, by rfl⟩ : syracuseStep 3938537 = 2953903) B2953903
theorem B2586887 : Blo 1362500 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B2046491 : Blo 1362500 2046491 := bstep (se 1 (by rfl) ⟨1534868, by rfl⟩ : syracuseStep 2046491 = 3069737) B3069737
theorem B2300447 : Blo 1362500 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B7092793 : Blo 1362500 7092793 := bstep (se 2 (by rfl) ⟨2659797, by rfl⟩ : syracuseStep 7092793 = 5319595) B5319595
theorem B20191841 : Blo 1362500 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B2300521 : Blo 1362500 2300521 := bstep (se 2 (by rfl) ⟨862695, by rfl⟩ : syracuseStep 2300521 = 1725391) B1725391
theorem B2046569 : Blo 1362500 2046569 := bstep (se 2 (by rfl) ⟨767463, by rfl⟩ : syracuseStep 2046569 = 1534927) B1534927
theorem B5986973 : Blo 1362500 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B1940279 : Blo 1362500 1940279 := bstep (se 1 (by rfl) ⟨1455209, by rfl⟩ : syracuseStep 1940279 = 2910419) B2910419
theorem B7764943 : Blo 1362500 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B2300879 : Blo 1362500 2300879 := bstep (se 1 (by rfl) ⟨1725659, by rfl⟩ : syracuseStep 2300879 = 3451319) B3451319
theorem B2333647 : Blo 1362500 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B15539363 : Blo 1362500 15539363 := bstep (se 1 (by rfl) ⟨11654522, by rfl⟩ : syracuseStep 15539363 = 23309045) B23309045
theorem B1866935 : Blo 1362500 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B4603175 : Blo 1362500 4603175 := bstep (se 1 (by rfl) ⟨3452381, by rfl⟩ : syracuseStep 4603175 = 6904763) B6904763
theorem B4914593 : Blo 1362500 4914593 := bstep (se 2 (by rfl) ⟨1842972, by rfl⟩ : syracuseStep 4914593 = 3685945) B3685945
theorem B6905249 : Blo 1362500 6905249 := bstep (se 2 (by rfl) ⟨2589468, by rfl⟩ : syracuseStep 6905249 = 5178937) B5178937
theorem B49741249 : Blo 1362500 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B9100775 : Blo 1362500 9100775 := bstep (se 1 (by rfl) ⟨6825581, by rfl⟩ : syracuseStep 9100775 = 13651163) B13651163
theorem B2301547 : Blo 1362500 2301547 := bstep (se 1 (by rfl) ⟨1726160, by rfl⟩ : syracuseStep 2301547 = 3452321) B3452321
theorem B2301817 : Blo 1362500 2301817 := bstep (se 2 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 2301817 = 1726363) B1726363
theorem B3547003 : Blo 1362500 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B3686269 : Blo 1362500 3686269 := bstep (se 3 (by rfl) ⟨691175, by rfl⟩ : syracuseStep 3686269 = 1382351) B1382351
theorem B2301851 : Blo 1362500 2301851 := bstep (se 1 (by rfl) ⟨1726388, by rfl⟩ : syracuseStep 2301851 = 3452777) B3452777
theorem B5177479 : Blo 1362500 5177479 := bstep (se 1 (by rfl) ⟨3883109, by rfl⟩ : syracuseStep 5177479 = 7766219) B7766219
theorem B6897959 : Blo 1362500 6897959 := bstep (se 1 (by rfl) ⟨5173469, by rfl⟩ : syracuseStep 6897959 = 10346939) B10346939
theorem B5177951 : Blo 1362500 5177951 := bstep (se 1 (by rfl) ⟨3883463, by rfl⟩ : syracuseStep 5177951 = 7766927) B7766927
theorem B10502765 : Blo 1362500 10502765 := bstep (se 3 (by rfl) ⟨1969268, by rfl⟩ : syracuseStep 10502765 = 3938537) B3938537
theorem B4203227 : Blo 1362500 4203227 := bstep (se 1 (by rfl) ⟨3152420, by rfl⟩ : syracuseStep 4203227 = 6304841) B6304841
theorem B11051795 : Blo 1362500 11051795 := bstep (se 1 (by rfl) ⟨8288846, by rfl⟩ : syracuseStep 11051795 = 16577693) B16577693
theorem B2589803 : Blo 1362500 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B3450023 : Blo 1362500 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B2589887 : Blo 1362500 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B4605119 : Blo 1362500 4605119 := bstep (se 1 (by rfl) ⟨3453839, by rfl⟩ : syracuseStep 4605119 = 6907679) B6907679
theorem B2213167 : Blo 1362500 2213167 := bstep (se 1 (by rfl) ⟨1659875, by rfl⟩ : syracuseStep 2213167 = 3319751) B3319751
theorem B2590031 : Blo 1362500 2590031 := bstep (se 1 (by rfl) ⟨1942523, by rfl⟩ : syracuseStep 2590031 = 3885047) B3885047
theorem B6907517 : Blo 1362500 6907517 := bstep (se 3 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 6907517 = 2590319) B2590319
theorem B1533631 : Blo 1362500 1533631 := bstep (se 1 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 1533631 = 2300447) B2300447
theorem B13461227 : Blo 1362500 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B6555593 : Blo 1362500 6555593 := bstep (se 2 (by rfl) ⟨2458347, by rfl⟩ : syracuseStep 6555593 = 4916695) B4916695
theorem B1533919 : Blo 1362500 1533919 := bstep (se 1 (by rfl) ⟨1150439, by rfl⟩ : syracuseStep 1533919 = 2300879) B2300879
theorem B3065831 : Blo 1362500 3065831 := bstep (se 1 (by rfl) ⟨2299373, by rfl⟩ : syracuseStep 3065831 = 4598747) B4598747
theorem B12437651 : Blo 1362500 12437651 := bstep (se 1 (by rfl) ⟨9328238, by rfl⟩ : syracuseStep 12437651 = 18656477) B18656477
theorem B3066011 : Blo 1362500 3066011 := bstep (se 1 (by rfl) ⟨2299508, by rfl⟩ : syracuseStep 3066011 = 4599017) B4599017
theorem B10635419 : Blo 1362500 10635419 := bstep (se 1 (by rfl) ⟨7976564, by rfl⟩ : syracuseStep 10635419 = 15953129) B15953129
theorem B8734999 : Blo 1362500 8734999 := bstep (se 1 (by rfl) ⟨6551249, by rfl⟩ : syracuseStep 8734999 = 13102499) B13102499
theorem B3066191 : Blo 1362500 3066191 := bstep (se 1 (by rfl) ⟨2299643, by rfl⟩ : syracuseStep 3066191 = 4599287) B4599287
theorem B3066281 : Blo 1362500 3066281 := bstep (se 2 (by rfl) ⟨1149855, by rfl⟩ : syracuseStep 3066281 = 2299711) B2299711
theorem B4729337 : Blo 1362500 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B1362535 : Blo 1362500 1362535 := bstep (se 1 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 1362535 = 2043803) B2043803
theorem B6638183 : Blo 1362500 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B1534567 : Blo 1362500 1534567 := bstep (se 1 (by rfl) ⟨1150925, by rfl⟩ : syracuseStep 1534567 = 2301851) B2301851
theorem B2395001 : Blo 1362500 2395001 := bstep (se 2 (by rfl) ⟨898125, by rfl⟩ : syracuseStep 2395001 = 1796251) B1796251
theorem B3451855 : Blo 1362500 3451855 := bstep (se 1 (by rfl) ⟨2588891, by rfl⟩ : syracuseStep 3451855 = 5177783) B5177783
theorem B1362911 : Blo 1362500 1362911 := bstep (se 1 (by rfl) ⟨1022183, by rfl⟩ : syracuseStep 1362911 = 2044367) B2044367
theorem B1362939 : Blo 1362500 1362939 := bstep (se 1 (by rfl) ⟨1022204, by rfl⟩ : syracuseStep 1362939 = 2044409) B2044409
theorem B3066875 : Blo 1362500 3066875 := bstep (se 1 (by rfl) ⟨2300156, by rfl⟩ : syracuseStep 3066875 = 4600313) B4600313
theorem B7769135 : Blo 1362500 7769135 := bstep (se 1 (by rfl) ⟨5826851, by rfl⟩ : syracuseStep 7769135 = 11653703) B11653703
theorem B1363007 : Blo 1362500 1363007 := bstep (se 1 (by rfl) ⟨1022255, by rfl⟩ : syracuseStep 1363007 = 2044511) B2044511
theorem B4598855 : Blo 1362500 4598855 := bstep (se 1 (by rfl) ⟨3449141, by rfl⟩ : syracuseStep 4598855 = 6898283) B6898283
theorem B3067055 : Blo 1362500 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B3067091 : Blo 1362500 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B3452179 : Blo 1362500 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B6221161 : Blo 1362500 6221161 := bstep (se 2 (by rfl) ⟨2332935, by rfl⟩ : syracuseStep 6221161 = 4665871) B4665871
theorem B5827945 : Blo 1362500 5827945 := bstep (se 2 (by rfl) ⟨2185479, by rfl⟩ : syracuseStep 5827945 = 4370959) B4370959
theorem B1363327 : Blo 1362500 1363327 := bstep (se 1 (by rfl) ⟨1022495, by rfl⟩ : syracuseStep 1363327 = 2044991) B2044991
theorem B1363355 : Blo 1362500 1363355 := bstep (se 1 (by rfl) ⟨1022516, by rfl⟩ : syracuseStep 1363355 = 2045033) B2045033
theorem B9457057 : Blo 1362500 9457057 := bstep (se 2 (by rfl) ⟨3546396, by rfl⟩ : syracuseStep 9457057 = 7092793) B7092793
theorem B1363423 : Blo 1362500 1363423 := bstep (se 1 (by rfl) ⟨1022567, by rfl⟩ : syracuseStep 1363423 = 2045135) B2045135
theorem B3067361 : Blo 1362500 3067361 := bstep (se 2 (by rfl) ⟨1150260, by rfl⟩ : syracuseStep 3067361 = 2300521) B2300521
theorem B1363559 : Blo 1362500 1363559 := bstep (se 1 (by rfl) ⟨1022669, by rfl⟩ : syracuseStep 1363559 = 2045339) B2045339
theorem B7769843 : Blo 1362500 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B1363707 : Blo 1362500 1363707 := bstep (se 1 (by rfl) ⟨1022780, by rfl⟩ : syracuseStep 1363707 = 2045561) B2045561
theorem B6901523 : Blo 1362500 6901523 := bstep (se 1 (by rfl) ⟨5176142, by rfl⟩ : syracuseStep 6901523 = 10352285) B10352285
theorem B1363775 : Blo 1362500 1363775 := bstep (se 1 (by rfl) ⟨1022831, by rfl⟩ : syracuseStep 1363775 = 2045663) B2045663
theorem B3067775 : Blo 1362500 3067775 := bstep (se 1 (by rfl) ⟨2300831, by rfl⟩ : syracuseStep 3067775 = 4601663) B4601663
theorem B1363839 : Blo 1362500 1363839 := bstep (se 1 (by rfl) ⟨1022879, by rfl⟩ : syracuseStep 1363839 = 2045759) B2045759
theorem B2043785 : Blo 1362500 2043785 := bstep (se 2 (by rfl) ⟨766419, by rfl⟩ : syracuseStep 2043785 = 1532839) B1532839
theorem B1363951 : Blo 1362500 1363951 := bstep (se 1 (by rfl) ⟨1022963, by rfl⟩ : syracuseStep 1363951 = 2045927) B2045927
theorem B5541871 : Blo 1362500 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B1363963 : Blo 1362500 1363963 := bstep (se 1 (by rfl) ⟨1022972, by rfl⟩ : syracuseStep 1363963 = 2045945) B2045945
theorem B1364031 : Blo 1362500 1364031 := bstep (se 1 (by rfl) ⟨1023023, by rfl⟩ : syracuseStep 1364031 = 2046047) B2046047
theorem B1364071 : Blo 1362500 1364071 := bstep (se 1 (by rfl) ⟨1023053, by rfl⟩ : syracuseStep 1364071 = 2046107) B2046107
theorem B2044031 : Blo 1362500 2044031 := bstep (se 1 (by rfl) ⟨1533023, by rfl⟩ : syracuseStep 2044031 = 3066047) B3066047
theorem B4599935 : Blo 1362500 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B1364095 : Blo 1362500 1364095 := bstep (se 1 (by rfl) ⟨1023071, by rfl⟩ : syracuseStep 1364095 = 2046143) B2046143
theorem B1364123 : Blo 1362500 1364123 := bstep (se 1 (by rfl) ⟨1023092, by rfl⟩ : syracuseStep 1364123 = 2046185) B2046185
theorem B1724591 : Blo 1362500 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B1364327 : Blo 1362500 1364327 := bstep (se 1 (by rfl) ⟨1023245, by rfl⟩ : syracuseStep 1364327 = 2046491) B2046491
theorem B1364379 : Blo 1362500 1364379 := bstep (se 1 (by rfl) ⟨1023284, by rfl⟩ : syracuseStep 1364379 = 2046569) B2046569
theorem B2044667 : Blo 1362500 2044667 := bstep (se 1 (by rfl) ⟨1533500, by rfl⟩ : syracuseStep 2044667 = 3067001) B3067001
theorem B10359575 : Blo 1362500 10359575 := bstep (se 1 (by rfl) ⟨7769681, by rfl⟩ : syracuseStep 10359575 = 15539363) B15539363
theorem B3068729 : Blo 1362500 3068729 := bstep (se 2 (by rfl) ⟨1150773, by rfl⟩ : syracuseStep 3068729 = 2301547) B2301547
theorem B5174077 : Blo 1362500 5174077 := bstep (se 3 (by rfl) ⟨970139, by rfl⟩ : syracuseStep 5174077 = 1940279) B1940279
theorem B3068783 : Blo 1362500 3068783 := bstep (se 1 (by rfl) ⟨2301587, by rfl⟩ : syracuseStep 3068783 = 4603175) B4603175
theorem B6067183 : Blo 1362500 6067183 := bstep (se 1 (by rfl) ⟨4550387, by rfl⟩ : syracuseStep 6067183 = 9100775) B9100775
theorem B3273799 : Blo 1362500 3273799 := bstep (se 1 (by rfl) ⟨2455349, by rfl⟩ : syracuseStep 3273799 = 4910699) B4910699
theorem B4600961 : Blo 1362500 4600961 := bstep (se 2 (by rfl) ⟨1725360, by rfl⟩ : syracuseStep 4600961 = 3450721) B3450721
theorem B3069089 : Blo 1362500 3069089 := bstep (se 2 (by rfl) ⟨1150908, by rfl⟩ : syracuseStep 3069089 = 2301817) B2301817
theorem B10351799 : Blo 1362500 10351799 := bstep (se 1 (by rfl) ⟨7763849, by rfl⟩ : syracuseStep 10351799 = 15527699) B15527699
theorem B2045111 : Blo 1362500 2045111 := bstep (se 1 (by rfl) ⟨1533833, by rfl⟩ : syracuseStep 2045111 = 3067667) B3067667
theorem B1455355 : Blo 1362500 1455355 := bstep (se 1 (by rfl) ⟨1091516, by rfl⟩ : syracuseStep 1455355 = 2183033) B2183033
theorem B2045351 : Blo 1362500 2045351 := bstep (se 1 (by rfl) ⟨1534013, by rfl⟩ : syracuseStep 2045351 = 3068027) B3068027
theorem B3069359 : Blo 1362500 3069359 := bstep (se 1 (by rfl) ⟨2302019, by rfl⟩ : syracuseStep 3069359 = 4604039) B4604039
theorem B24868295 : Blo 1362500 24868295 := bstep (se 1 (by rfl) ⟨18651221, by rfl⟩ : syracuseStep 24868295 = 37302443) B37302443
theorem B2299367 : Blo 1362500 2299367 := bstep (se 1 (by rfl) ⟨1724525, by rfl⟩ : syracuseStep 2299367 = 3449051) B3449051
theorem B2045531 : Blo 1362500 2045531 := bstep (se 1 (by rfl) ⟨1534148, by rfl⟩ : syracuseStep 2045531 = 3068297) B3068297
theorem B2299529 : Blo 1362500 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B5822239 : Blo 1362500 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B4978493 : Blo 1362500 4978493 := bstep (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) B1866935
theorem B2914127 : Blo 1362500 2914127 := bstep (se 1 (by rfl) ⟨2185595, by rfl⟩ : syracuseStep 2914127 = 4371191) B4371191
theorem B4601771 : Blo 1362500 4601771 := bstep (se 1 (by rfl) ⟨3451328, by rfl⟩ : syracuseStep 4601771 = 6902657) B6902657
theorem B2045993 : Blo 1362500 2045993 := bstep (se 2 (by rfl) ⟨767247, by rfl⟩ : syracuseStep 2045993 = 1534495) B1534495
theorem B2046023 : Blo 1362500 2046023 := bstep (se 1 (by rfl) ⟨1534517, by rfl⟩ : syracuseStep 2046023 = 3069035) B3069035
theorem B20977825 : Blo 1362500 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B2300123 : Blo 1362500 2300123 := bstep (se 1 (by rfl) ⟨1725092, by rfl⟩ : syracuseStep 2300123 = 3450185) B3450185
theorem B10631531 : Blo 1362500 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B4602311 : Blo 1362500 4602311 := bstep (se 1 (by rfl) ⟨3451733, by rfl⟩ : syracuseStep 4602311 = 6903467) B6903467
theorem B2046407 : Blo 1362500 2046407 := bstep (se 1 (by rfl) ⟨1534805, by rfl⟩ : syracuseStep 2046407 = 3069611) B3069611
theorem B2300393 : Blo 1362500 2300393 := bstep (se 2 (by rfl) ⟨862647, by rfl⟩ : syracuseStep 2300393 = 1725295) B1725295
theorem B5175839 : Blo 1362500 5175839 := bstep (se 1 (by rfl) ⟨3881879, by rfl⟩ : syracuseStep 5175839 = 7763759) B7763759
theorem B10353257 : Blo 1362500 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B3111529 : Blo 1362500 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B6552211 : Blo 1362500 6552211 := bstep (se 1 (by rfl) ⟨4914158, by rfl⟩ : syracuseStep 6552211 = 9828317) B9828317
theorem B4602527 : Blo 1362500 4602527 := bstep (se 1 (by rfl) ⟨3451895, by rfl⟩ : syracuseStep 4602527 = 6903791) B6903791
theorem B2046623 : Blo 1362500 2046623 := bstep (se 1 (by rfl) ⟨1534967, by rfl⟩ : syracuseStep 2046623 = 3069935) B3069935
theorem B7871165 : Blo 1362500 7871165 := bstep (se 3 (by rfl) ⟨1475843, by rfl⟩ : syracuseStep 7871165 = 2951687) B2951687
theorem B13097807 : Blo 1362500 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B1842031 : Blo 1362500 1842031 := bstep (se 1 (by rfl) ⟨1381523, by rfl⟩ : syracuseStep 1842031 = 2763047) B2763047
theorem B15965261 : Blo 1362500 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B66321665 : Blo 1362500 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B9461281 : Blo 1362500 9461281 := bstep (se 2 (by rfl) ⟨3547980, by rfl⟩ : syracuseStep 9461281 = 7095961) B7095961
theorem B3276395 : Blo 1362500 3276395 := bstep (se 1 (by rfl) ⟨2457296, by rfl⟩ : syracuseStep 3276395 = 4914593) B4914593
theorem B4603499 : Blo 1362500 4603499 := bstep (se 1 (by rfl) ⟨3452624, by rfl⟩ : syracuseStep 4603499 = 6905249) B6905249
theorem B31489829 : Blo 1362500 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B4915025 : Blo 1362500 4915025 := bstep (se 2 (by rfl) ⟨1843134, by rfl⟩ : syracuseStep 4915025 = 3686269) B3686269
theorem B4603769 : Blo 1362500 4603769 := bstep (se 2 (by rfl) ⟨1726413, by rfl⟩ : syracuseStep 4603769 = 3452827) B3452827
theorem B28361117 : Blo 1362500 28361117 := bstep (se 3 (by rfl) ⟨5317709, by rfl⟩ : syracuseStep 28361117 = 10635419) B10635419
theorem B2802151 : Blo 1362500 2802151 := bstep (se 1 (by rfl) ⟨2101613, by rfl⟩ : syracuseStep 2802151 = 4203227) B4203227
theorem B6906383 : Blo 1362500 6906383 := bstep (se 1 (by rfl) ⟨5179787, by rfl⟩ : syracuseStep 6906383 = 10359575) B10359575
theorem B1532911 : Blo 1362500 1532911 := bstep (se 1 (by rfl) ⟨1149683, by rfl⟩ : syracuseStep 1532911 = 2299367) B2299367
theorem B6898769 : Blo 1362500 6898769 := bstep (se 2 (by rfl) ⟨2587038, by rfl⟩ : syracuseStep 6898769 = 5174077) B5174077
theorem B4605011 : Blo 1362500 4605011 := bstep (se 1 (by rfl) ⟨3453758, by rfl⟩ : syracuseStep 4605011 = 6907517) B6907517
theorem B1533019 : Blo 1362500 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B3318995 : Blo 1362500 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B1942751 : Blo 1362500 1942751 := bstep (se 1 (by rfl) ⟨1457063, by rfl⟩ : syracuseStep 1942751 = 2914127) B2914127
theorem B8291767 : Blo 1362500 8291767 := bstep (se 1 (by rfl) ⟨6218825, by rfl⟩ : syracuseStep 8291767 = 12437651) B12437651
theorem B1533415 : Blo 1362500 1533415 := bstep (se 1 (by rfl) ⟨1150061, by rfl⟩ : syracuseStep 1533415 = 2300123) B2300123
theorem B1533595 : Blo 1362500 1533595 := bstep (se 1 (by rfl) ⟨1150196, by rfl⟩ : syracuseStep 1533595 = 2300393) B2300393
theorem B3450559 : Blo 1362500 3450559 := bstep (se 1 (by rfl) ⟨2587919, by rfl⟩ : syracuseStep 3450559 = 5175839) B5175839
theorem B2950889 : Blo 1362500 2950889 := bstep (se 2 (by rfl) ⟨1106583, by rfl⟩ : syracuseStep 2950889 = 2213167) B2213167
theorem B4425455 : Blo 1362500 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B12609409 : Blo 1362500 12609409 := bstep (se 2 (by rfl) ⟨4728528, by rfl⟩ : syracuseStep 12609409 = 9457057) B9457057
theorem B9824165 : Blo 1362500 9824165 := bstep (se 4 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 9824165 = 1842031) B1842031
theorem B5179423 : Blo 1362500 5179423 := bstep (se 1 (by rfl) ⟨3884567, by rfl⟩ : syracuseStep 5179423 = 7769135) B7769135
theorem B3065903 : Blo 1362500 3065903 := bstep (se 1 (by rfl) ⟨2299427, by rfl⟩ : syracuseStep 3065903 = 4598855) B4598855
theorem B10643507 : Blo 1362500 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B44214443 : Blo 1362500 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B5179895 : Blo 1362500 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B1362523 : Blo 1362500 1362523 := bstep (se 1 (by rfl) ⟨1021892, by rfl⟩ : syracuseStep 1362523 = 2043785) B2043785
theorem B1362687 : Blo 1362500 1362687 := bstep (se 1 (by rfl) ⟨1022015, by rfl⟩ : syracuseStep 1362687 = 2044031) B2044031
theorem B3066623 : Blo 1362500 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B4598639 : Blo 1362500 4598639 := bstep (se 1 (by rfl) ⟨3448979, by rfl⟩ : syracuseStep 4598639 = 6897959) B6897959
theorem B27970433 : Blo 1362500 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B3451967 : Blo 1362500 3451967 := bstep (se 1 (by rfl) ⟨2588975, by rfl⟩ : syracuseStep 3451967 = 5177951) B5177951
theorem B4598909 : Blo 1362500 4598909 := bstep (se 3 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 4598909 = 1724591) B1724591
theorem B1363111 : Blo 1362500 1363111 := bstep (se 1 (by rfl) ⟨1022333, by rfl⟩ : syracuseStep 1363111 = 2044667) B2044667
theorem B7367863 : Blo 1362500 7367863 := bstep (se 1 (by rfl) ⟨5525897, by rfl⟩ : syracuseStep 7367863 = 11051795) B11051795
theorem B3067307 : Blo 1362500 3067307 := bstep (se 1 (by rfl) ⟨2300480, by rfl⟩ : syracuseStep 3067307 = 4600961) B4600961
theorem B6901199 : Blo 1362500 6901199 := bstep (se 1 (by rfl) ⟨5175899, by rfl⟩ : syracuseStep 6901199 = 10351799) B10351799
theorem B1363407 : Blo 1362500 1363407 := bstep (se 1 (by rfl) ⟨1022555, by rfl⟩ : syracuseStep 1363407 = 2045111) B2045111
theorem B4148705 : Blo 1362500 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B8736281 : Blo 1362500 8736281 := bstep (se 2 (by rfl) ⟨3276105, by rfl⟩ : syracuseStep 8736281 = 6552211) B6552211
theorem B1363567 : Blo 1362500 1363567 := bstep (se 1 (by rfl) ⟨1022675, by rfl⟩ : syracuseStep 1363567 = 2045351) B2045351
theorem B1363687 : Blo 1362500 1363687 := bstep (se 1 (by rfl) ⟨1022765, by rfl⟩ : syracuseStep 1363687 = 2045531) B2045531
theorem B8974151 : Blo 1362500 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B3067847 : Blo 1362500 3067847 := bstep (se 1 (by rfl) ⟨2300885, by rfl⟩ : syracuseStep 3067847 = 4601771) B4601771
theorem B8089577 : Blo 1362500 8089577 := bstep (se 2 (by rfl) ⟨3033591, by rfl⟩ : syracuseStep 8089577 = 6067183) B6067183
theorem B2043887 : Blo 1362500 2043887 := bstep (se 1 (by rfl) ⟨1532915, by rfl⟩ : syracuseStep 2043887 = 3065831) B3065831
theorem B1363995 : Blo 1362500 1363995 := bstep (se 1 (by rfl) ⟨1022996, by rfl⟩ : syracuseStep 1363995 = 2045993) B2045993
theorem B1364015 : Blo 1362500 1364015 := bstep (se 1 (by rfl) ⟨1023011, by rfl⟩ : syracuseStep 1364015 = 2046023) B2046023
theorem B2044007 : Blo 1362500 2044007 := bstep (se 1 (by rfl) ⟨1533005, by rfl⟩ : syracuseStep 2044007 = 3066011) B3066011
theorem B2044127 : Blo 1362500 2044127 := bstep (se 1 (by rfl) ⟨1533095, by rfl⟩ : syracuseStep 2044127 = 3066191) B3066191
theorem B2044187 : Blo 1362500 2044187 := bstep (se 1 (by rfl) ⟨1533140, by rfl⟩ : syracuseStep 2044187 = 3066281) B3066281
theorem B3068207 : Blo 1362500 3068207 := bstep (se 1 (by rfl) ⟨2301155, by rfl⟩ : syracuseStep 3068207 = 4602311) B4602311
theorem B1364271 : Blo 1362500 1364271 := bstep (se 1 (by rfl) ⟨1023203, by rfl⟩ : syracuseStep 1364271 = 2046407) B2046407
theorem B6902171 : Blo 1362500 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B3068351 : Blo 1362500 3068351 := bstep (se 1 (by rfl) ⟨2301263, by rfl⟩ : syracuseStep 3068351 = 4602527) B4602527
theorem B1364415 : Blo 1362500 1364415 := bstep (se 1 (by rfl) ⟨1023311, by rfl⟩ : syracuseStep 1364415 = 2046623) B2046623
theorem B5247443 : Blo 1362500 5247443 := bstep (se 1 (by rfl) ⟨3935582, by rfl⟩ : syracuseStep 5247443 = 7871165) B7871165
theorem B8294881 : Blo 1362500 8294881 := bstep (se 2 (by rfl) ⟨3110580, by rfl⟩ : syracuseStep 8294881 = 6221161) B6221161
theorem B7770593 : Blo 1362500 7770593 := bstep (se 2 (by rfl) ⟨2913972, by rfl⟩ : syracuseStep 7770593 = 5827945) B5827945
theorem B2044583 : Blo 1362500 2044583 := bstep (se 1 (by rfl) ⟨1533437, by rfl⟩ : syracuseStep 2044583 = 3066875) B3066875
theorem B2044703 : Blo 1362500 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B2044727 : Blo 1362500 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B2044841 : Blo 1362500 2044841 := bstep (se 2 (by rfl) ⟨766815, by rfl⟩ : syracuseStep 2044841 = 1533631) B1533631
theorem B2044907 : Blo 1362500 2044907 := bstep (se 1 (by rfl) ⟨1533680, by rfl⟩ : syracuseStep 2044907 = 3067361) B3067361
theorem B7762985 : Blo 1362500 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B2184263 : Blo 1362500 2184263 := bstep (se 1 (by rfl) ⟨1638197, by rfl⟩ : syracuseStep 2184263 = 3276395) B3276395
theorem B3068999 : Blo 1362500 3068999 := bstep (se 1 (by rfl) ⟨2301749, by rfl⟩ : syracuseStep 3068999 = 4603499) B4603499
theorem B4601015 : Blo 1362500 4601015 := bstep (se 1 (by rfl) ⟨3450761, by rfl⟩ : syracuseStep 4601015 = 6901523) B6901523
theorem B20993219 : Blo 1362500 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B3069179 : Blo 1362500 3069179 := bstep (se 1 (by rfl) ⟨2301884, by rfl⟩ : syracuseStep 3069179 = 4603769) B4603769
theorem B2045183 : Blo 1362500 2045183 := bstep (se 1 (by rfl) ⟨1533887, by rfl⟩ : syracuseStep 2045183 = 3067775) B3067775
theorem B2045225 : Blo 1362500 2045225 := bstep (se 2 (by rfl) ⟨766959, by rfl⟩ : syracuseStep 2045225 = 1533919) B1533919
theorem B6903305 : Blo 1362500 6903305 := bstep (se 2 (by rfl) ⟨2588739, by rfl⟩ : syracuseStep 6903305 = 5177479) B5177479
theorem B11646665 : Blo 1362500 11646665 := bstep (se 2 (by rfl) ⟨4367499, by rfl⟩ : syracuseStep 11646665 = 8734999) B8734999
theorem B7001843 : Blo 1362500 7001843 := bstep (se 1 (by rfl) ⟨5251382, by rfl⟩ : syracuseStep 7001843 = 10502765) B10502765
theorem B2045819 : Blo 1362500 2045819 := bstep (se 1 (by rfl) ⟨1534364, by rfl⟩ : syracuseStep 2045819 = 3068729) B3068729
theorem B2045855 : Blo 1362500 2045855 := bstep (se 1 (by rfl) ⟨1534391, by rfl⟩ : syracuseStep 2045855 = 3068783) B3068783
theorem B1726535 : Blo 1362500 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B2046059 : Blo 1362500 2046059 := bstep (se 1 (by rfl) ⟨1534544, by rfl⟩ : syracuseStep 2046059 = 3069089) B3069089
theorem B2300015 : Blo 1362500 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B1726591 : Blo 1362500 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B3070079 : Blo 1362500 3070079 := bstep (se 1 (by rfl) ⟨2302559, by rfl⟩ : syracuseStep 3070079 = 4605119) B4605119
theorem B2046089 : Blo 1362500 2046089 := bstep (se 2 (by rfl) ⟨767283, by rfl⟩ : syracuseStep 2046089 = 1534567) B1534567
theorem B1726687 : Blo 1362500 1726687 := bstep (se 1 (by rfl) ⟨1295015, by rfl⟩ : syracuseStep 1726687 = 2590031) B2590031
theorem B28350749 : Blo 1362500 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B2046239 : Blo 1362500 2046239 := bstep (se 1 (by rfl) ⟨1534679, by rfl⟩ : syracuseStep 2046239 = 3069359) B3069359
theorem B16578863 : Blo 1362500 16578863 := bstep (se 1 (by rfl) ⟨12434147, by rfl⟩ : syracuseStep 16578863 = 24868295) B24868295
theorem B4602473 : Blo 1362500 4602473 := bstep (se 2 (by rfl) ⟨1725927, by rfl⟩ : syracuseStep 4602473 = 3451855) B3451855
theorem B4365065 : Blo 1362500 4365065 := bstep (se 2 (by rfl) ⟨1636899, by rfl⟩ : syracuseStep 4365065 = 3273799) B3273799
theorem B1940473 : Blo 1362500 1940473 := bstep (se 2 (by rfl) ⟨727677, by rfl⟩ : syracuseStep 1940473 = 1455355) B1455355
theorem B3152891 : Blo 1362500 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B4602905 : Blo 1362500 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B8731871 : Blo 1362500 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B1596667 : Blo 1362500 1596667 := bstep (se 1 (by rfl) ⟨1197500, by rfl⟩ : syracuseStep 1596667 = 2395001) B2395001
theorem B12615041 : Blo 1362500 12615041 := bstep (se 2 (by rfl) ⟨4730640, by rfl⟩ : syracuseStep 12615041 = 9461281) B9461281
theorem B17481581 : Blo 1362500 17481581 := bstep (se 3 (by rfl) ⟨3277796, by rfl⟩ : syracuseStep 17481581 = 6555593) B6555593
theorem B3276683 : Blo 1362500 3276683 := bstep (se 1 (by rfl) ⟨2457512, by rfl⟩ : syracuseStep 3276683 = 4915025) B4915025
theorem B7389161 : Blo 1362500 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B6905897 : Blo 1362500 6905897 := bstep (se 2 (by rfl) ⟨2589711, by rfl⟩ : syracuseStep 6905897 = 5179423) B5179423
theorem B2302121 : Blo 1362500 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B4604093 : Blo 1362500 4604093 := bstep (se 3 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 4604093 = 1726535) B1726535
theorem B18907411 : Blo 1362500 18907411 := bstep (se 1 (by rfl) ⟨14180558, by rfl⟩ : syracuseStep 18907411 = 28361117) B28361117
theorem B2302249 : Blo 1362500 2302249 := bstep (se 2 (by rfl) ⟨863343, by rfl⟩ : syracuseStep 2302249 = 1726687) B1726687
theorem B3498295 : Blo 1362500 3498295 := bstep (se 1 (by rfl) ⟨2623721, by rfl⟩ : syracuseStep 3498295 = 5247443) B5247443
theorem B4604255 : Blo 1362500 4604255 := bstep (se 1 (by rfl) ⟨3453191, by rfl⟩ : syracuseStep 4604255 = 6906383) B6906383
theorem B11059841 : Blo 1362500 11059841 := bstep (se 2 (by rfl) ⟨4147440, by rfl⟩ : syracuseStep 11059841 = 8294881) B8294881
theorem B3736201 : Blo 1362500 3736201 := bstep (se 2 (by rfl) ⟨1401075, by rfl⟩ : syracuseStep 3736201 = 2802151) B2802151
theorem B7095671 : Blo 1362500 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B1533343 : Blo 1362500 1533343 := bstep (se 1 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 1533343 = 2300015) B2300015
theorem B29476295 : Blo 1362500 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B18900499 : Blo 1362500 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B11052575 : Blo 1362500 11052575 := bstep (se 1 (by rfl) ⟨8289431, by rfl⟩ : syracuseStep 11052575 = 16578863) B16578863
theorem B9823817 : Blo 1362500 9823817 := bstep (se 2 (by rfl) ⟨3683931, by rfl⟩ : syracuseStep 9823817 = 7367863) B7367863
theorem B2910043 : Blo 1362500 2910043 := bstep (se 1 (by rfl) ⟨2182532, by rfl⟩ : syracuseStep 2910043 = 4365065) B4365065
theorem B3065759 : Blo 1362500 3065759 := bstep (se 1 (by rfl) ⟨2299319, by rfl⟩ : syracuseStep 3065759 = 4598639) B4598639
theorem B18646955 : Blo 1362500 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B18671581 : Blo 1362500 18671581 := bstep (se 3 (by rfl) ⟨3500921, by rfl⟩ : syracuseStep 18671581 = 7001843) B7001843
theorem B3065939 : Blo 1362500 3065939 := bstep (se 1 (by rfl) ⟨2299454, by rfl⟩ : syracuseStep 3065939 = 4598909) B4598909
theorem B16812545 : Blo 1362500 16812545 := bstep (se 2 (by rfl) ⟨6304704, by rfl⟩ : syracuseStep 16812545 = 12609409) B12609409
theorem B5982767 : Blo 1362500 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B5393051 : Blo 1362500 5393051 := bstep (se 1 (by rfl) ⟨4044788, by rfl⟩ : syracuseStep 5393051 = 8089577) B8089577
theorem B8407709 : Blo 1362500 8407709 := bstep (se 3 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 8407709 = 3152891) B3152891
theorem B4926107 : Blo 1362500 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B1362591 : Blo 1362500 1362591 := bstep (se 1 (by rfl) ⟨1021943, by rfl⟩ : syracuseStep 1362591 = 2043887) B2043887
theorem B1362671 : Blo 1362500 1362671 := bstep (se 1 (by rfl) ⟨1022003, by rfl⟩ : syracuseStep 1362671 = 2044007) B2044007
theorem B1362751 : Blo 1362500 1362751 := bstep (se 1 (by rfl) ⟨1022063, by rfl⟩ : syracuseStep 1362751 = 2044127) B2044127
theorem B1362791 : Blo 1362500 1362791 := bstep (se 1 (by rfl) ⟨1022093, by rfl⟩ : syracuseStep 1362791 = 2044187) B2044187
theorem B5180395 : Blo 1362500 5180395 := bstep (se 1 (by rfl) ⟨3885296, by rfl⟩ : syracuseStep 5180395 = 7770593) B7770593
theorem B1363055 : Blo 1362500 1363055 := bstep (se 1 (by rfl) ⟨1022291, by rfl⟩ : syracuseStep 1363055 = 2044583) B2044583
theorem B1363135 : Blo 1362500 1363135 := bstep (se 1 (by rfl) ⟨1022351, by rfl⟩ : syracuseStep 1363135 = 2044703) B2044703
theorem B1363151 : Blo 1362500 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B8850653 : Blo 1362500 8850653 := bstep (se 3 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 8850653 = 3318995) B3318995
theorem B5180669 : Blo 1362500 5180669 := bstep (se 3 (by rfl) ⟨971375, by rfl⟩ : syracuseStep 5180669 = 1942751) B1942751
theorem B1363227 : Blo 1362500 1363227 := bstep (se 1 (by rfl) ⟨1022420, by rfl⟩ : syracuseStep 1363227 = 2044841) B2044841
theorem B1363271 : Blo 1362500 1363271 := bstep (se 1 (by rfl) ⟨1022453, by rfl⟩ : syracuseStep 1363271 = 2044907) B2044907
theorem B4599179 : Blo 1362500 4599179 := bstep (se 1 (by rfl) ⟨3449384, by rfl⟩ : syracuseStep 4599179 = 6898769) B6898769
theorem B3067343 : Blo 1362500 3067343 := bstep (se 1 (by rfl) ⟨2300507, by rfl⟩ : syracuseStep 3067343 = 4601015) B4601015
theorem B13995479 : Blo 1362500 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B1363455 : Blo 1362500 1363455 := bstep (se 1 (by rfl) ⟨1022591, by rfl⟩ : syracuseStep 1363455 = 2045183) B2045183
theorem B1363483 : Blo 1362500 1363483 := bstep (se 1 (by rfl) ⟨1022612, by rfl⟩ : syracuseStep 1363483 = 2045225) B2045225
theorem B33640109 : Blo 1362500 33640109 := bstep (se 3 (by rfl) ⟨6307520, by rfl⟩ : syracuseStep 33640109 = 12615041) B12615041
theorem B1363879 : Blo 1362500 1363879 := bstep (se 1 (by rfl) ⟨1022909, by rfl⟩ : syracuseStep 1363879 = 2045819) B2045819
theorem B11063213 : Blo 1362500 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B1363903 : Blo 1362500 1363903 := bstep (se 1 (by rfl) ⟨1022927, by rfl⟩ : syracuseStep 1363903 = 2045855) B2045855
theorem B6549443 : Blo 1362500 6549443 := bstep (se 1 (by rfl) ⟨4912082, by rfl⟩ : syracuseStep 6549443 = 9824165) B9824165
theorem B2043881 : Blo 1362500 2043881 := bstep (se 2 (by rfl) ⟨766455, by rfl⟩ : syracuseStep 2043881 = 1532911) B1532911
theorem B2043935 : Blo 1362500 2043935 := bstep (se 1 (by rfl) ⟨1532951, by rfl⟩ : syracuseStep 2043935 = 3065903) B3065903
theorem B1364039 : Blo 1362500 1364039 := bstep (se 1 (by rfl) ⟨1023029, by rfl⟩ : syracuseStep 1364039 = 2046059) B2046059
theorem B1364059 : Blo 1362500 1364059 := bstep (se 1 (by rfl) ⟨1023044, by rfl⟩ : syracuseStep 1364059 = 2046089) B2046089
theorem B2044025 : Blo 1362500 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B1364159 : Blo 1362500 1364159 := bstep (se 1 (by rfl) ⟨1023119, by rfl⟩ : syracuseStep 1364159 = 2046239) B2046239
theorem B3453263 : Blo 1362500 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B3068315 : Blo 1362500 3068315 := bstep (se 1 (by rfl) ⟨2301236, by rfl⟩ : syracuseStep 3068315 = 4602473) B4602473
theorem B2044415 : Blo 1362500 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B11055689 : Blo 1362500 11055689 := bstep (se 2 (by rfl) ⟨4145883, by rfl⟩ : syracuseStep 11055689 = 8291767) B8291767
theorem B7869037 : Blo 1362500 7869037 := bstep (se 3 (by rfl) ⟨1475444, by rfl⟩ : syracuseStep 7869037 = 2950889) B2950889
theorem B11801213 : Blo 1362500 11801213 := bstep (se 3 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 11801213 = 4425455) B4425455
theorem B2044553 : Blo 1362500 2044553 := bstep (se 2 (by rfl) ⟨766707, by rfl⟩ : syracuseStep 2044553 = 1533415) B1533415
theorem B3068603 : Blo 1362500 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B5821247 : Blo 1362500 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B2044793 : Blo 1362500 2044793 := bstep (se 2 (by rfl) ⟨766797, by rfl⟩ : syracuseStep 2044793 = 1533595) B1533595
theorem B4600745 : Blo 1362500 4600745 := bstep (se 2 (by rfl) ⟨1725279, by rfl⟩ : syracuseStep 4600745 = 3450559) B3450559
theorem B2044871 : Blo 1362500 2044871 := bstep (se 1 (by rfl) ⟨1533653, by rfl⟩ : syracuseStep 2044871 = 3067307) B3067307
theorem B4600799 : Blo 1362500 4600799 := bstep (se 1 (by rfl) ⟨3450599, by rfl⟩ : syracuseStep 4600799 = 6901199) B6901199
theorem B11654387 : Blo 1362500 11654387 := bstep (se 1 (by rfl) ⟨8740790, by rfl⟩ : syracuseStep 11654387 = 17481581) B17481581
theorem B2184455 : Blo 1362500 2184455 := bstep (se 1 (by rfl) ⟨1638341, by rfl⟩ : syracuseStep 2184455 = 3276683) B3276683
theorem B2045231 : Blo 1362500 2045231 := bstep (se 1 (by rfl) ⟨1533923, by rfl⟩ : syracuseStep 2045231 = 3067847) B3067847
theorem B2045471 : Blo 1362500 2045471 := bstep (se 1 (by rfl) ⟨1534103, by rfl⟩ : syracuseStep 2045471 = 3068207) B3068207
theorem B4601447 : Blo 1362500 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B2045567 : Blo 1362500 2045567 := bstep (se 1 (by rfl) ⟨1534175, by rfl⟩ : syracuseStep 2045567 = 3068351) B3068351
theorem B5175323 : Blo 1362500 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B1456175 : Blo 1362500 1456175 := bstep (se 1 (by rfl) ⟨1092131, by rfl⟩ : syracuseStep 1456175 = 2184263) B2184263
theorem B2045999 : Blo 1362500 2045999 := bstep (se 1 (by rfl) ⟨1534499, by rfl⟩ : syracuseStep 2045999 = 3068999) B3068999
theorem B3070007 : Blo 1362500 3070007 := bstep (se 1 (by rfl) ⟨2302505, by rfl⟩ : syracuseStep 3070007 = 4605011) B4605011
theorem B2046119 : Blo 1362500 2046119 := bstep (se 1 (by rfl) ⟨1534589, by rfl⟩ : syracuseStep 2046119 = 3069179) B3069179
theorem B4602203 : Blo 1362500 4602203 := bstep (se 1 (by rfl) ⟨3451652, by rfl⟩ : syracuseStep 4602203 = 6903305) B6903305
theorem B7764443 : Blo 1362500 7764443 := bstep (se 1 (by rfl) ⟨5823332, by rfl⟩ : syracuseStep 7764443 = 11646665) B11646665
theorem B2587297 : Blo 1362500 2587297 := bstep (se 2 (by rfl) ⟨970236, by rfl⟩ : syracuseStep 2587297 = 1940473) B1940473
theorem B2046719 : Blo 1362500 2046719 := bstep (se 1 (by rfl) ⟨1535039, by rfl⟩ : syracuseStep 2046719 = 3070079) B3070079
theorem B2128889 : Blo 1362500 2128889 := bstep (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) B1596667
theorem B2301311 : Blo 1362500 2301311 := bstep (se 1 (by rfl) ⟨1725983, by rfl⟩ : syracuseStep 2301311 = 3451967) B3451967
theorem B5824187 : Blo 1362500 5824187 := bstep (se 1 (by rfl) ⟨4368140, by rfl⟩ : syracuseStep 5824187 = 8736281) B8736281
theorem B4603931 : Blo 1362500 4603931 := bstep (se 1 (by rfl) ⟨3452948, by rfl⟩ : syracuseStep 4603931 = 6905897) B6905897
theorem B3883133 : Blo 1362500 3883133 := bstep (se 3 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 3883133 = 1456175) B1456175
theorem B2302175 : Blo 1362500 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B7373227 : Blo 1362500 7373227 := bstep (se 1 (by rfl) ⟨5529920, by rfl⟩ : syracuseStep 7373227 = 11059841) B11059841
theorem B4981601 : Blo 1362500 4981601 := bstep (se 2 (by rfl) ⟨1868100, by rfl⟩ : syracuseStep 4981601 = 3736201) B3736201
theorem B3449729 : Blo 1362500 3449729 := bstep (se 2 (by rfl) ⟨1293648, by rfl⟩ : syracuseStep 3449729 = 2587297) B2587297
theorem B6907193 : Blo 1362500 6907193 := bstep (se 2 (by rfl) ⟨2590197, by rfl⟩ : syracuseStep 6907193 = 5180395) B5180395
theorem B3450215 : Blo 1362500 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B5605139 : Blo 1362500 5605139 := bstep (se 1 (by rfl) ⟨4203854, by rfl⟩ : syracuseStep 5605139 = 8407709) B8407709
theorem B25200665 : Blo 1362500 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B5900435 : Blo 1362500 5900435 := bstep (se 1 (by rfl) ⟨4425326, by rfl⟩ : syracuseStep 5900435 = 8850653) B8850653
theorem B1534207 : Blo 1362500 1534207 := bstep (se 1 (by rfl) ⟨1150655, by rfl⟩ : syracuseStep 1534207 = 2301311) B2301311
theorem B3066119 : Blo 1362500 3066119 := bstep (se 1 (by rfl) ⟨2299589, by rfl⟩ : syracuseStep 3066119 = 4599179) B4599179
theorem B7375475 : Blo 1362500 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B1362587 : Blo 1362500 1362587 := bstep (se 1 (by rfl) ⟨1021940, by rfl⟩ : syracuseStep 1362587 = 2043881) B2043881
theorem B179333813 : Blo 1362500 179333813 := bstep (se 5 (by rfl) ⟨8406272, by rfl⟩ : syracuseStep 179333813 = 16812545) B16812545
theorem B1362623 : Blo 1362500 1362623 := bstep (se 1 (by rfl) ⟨1021967, by rfl⟩ : syracuseStep 1362623 = 2043935) B2043935
theorem B1362683 : Blo 1362500 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B1534747 : Blo 1362500 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B1362943 : Blo 1362500 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B25209881 : Blo 1362500 25209881 := bstep (se 2 (by rfl) ⟨9453705, by rfl⟩ : syracuseStep 25209881 = 18907411) B18907411
theorem B4664393 : Blo 1362500 4664393 := bstep (se 2 (by rfl) ⟨1749147, by rfl⟩ : syracuseStep 4664393 = 3498295) B3498295
theorem B7867475 : Blo 1362500 7867475 := bstep (se 1 (by rfl) ⟨5900606, by rfl⟩ : syracuseStep 7867475 = 11801213) B11801213
theorem B1363035 : Blo 1362500 1363035 := bstep (se 1 (by rfl) ⟨1022276, by rfl⟩ : syracuseStep 1363035 = 2044553) B2044553
theorem B1363195 : Blo 1362500 1363195 := bstep (se 1 (by rfl) ⟨1022396, by rfl⟩ : syracuseStep 1363195 = 2044793) B2044793
theorem B3067163 : Blo 1362500 3067163 := bstep (se 1 (by rfl) ⟨2300372, by rfl⟩ : syracuseStep 3067163 = 4600745) B4600745
theorem B1363247 : Blo 1362500 1363247 := bstep (se 1 (by rfl) ⟨1022435, by rfl⟩ : syracuseStep 1363247 = 2044871) B2044871
theorem B3067199 : Blo 1362500 3067199 := bstep (se 1 (by rfl) ⟨2300399, by rfl⟩ : syracuseStep 3067199 = 4600799) B4600799
theorem B7769591 : Blo 1362500 7769591 := bstep (se 1 (by rfl) ⟨5827193, by rfl⟩ : syracuseStep 7769591 = 11654387) B11654387
theorem B1363487 : Blo 1362500 1363487 := bstep (se 1 (by rfl) ⟨1022615, by rfl⟩ : syracuseStep 1363487 = 2045231) B2045231
theorem B4730447 : Blo 1362500 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B7368383 : Blo 1362500 7368383 := bstep (se 1 (by rfl) ⟨5526287, by rfl⟩ : syracuseStep 7368383 = 11052575) B11052575
theorem B1363647 : Blo 1362500 1363647 := bstep (se 1 (by rfl) ⟨1022735, by rfl⟩ : syracuseStep 1363647 = 2045471) B2045471
theorem B6549211 : Blo 1362500 6549211 := bstep (se 1 (by rfl) ⟨4911908, by rfl⟩ : syracuseStep 6549211 = 9823817) B9823817
theorem B3067631 : Blo 1362500 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B1363711 : Blo 1362500 1363711 := bstep (se 1 (by rfl) ⟨1022783, by rfl⟩ : syracuseStep 1363711 = 2045567) B2045567
theorem B2043839 : Blo 1362500 2043839 := bstep (se 1 (by rfl) ⟨1532879, by rfl⟩ : syracuseStep 2043839 = 3065759) B3065759
theorem B12431303 : Blo 1362500 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B1363999 : Blo 1362500 1363999 := bstep (se 1 (by rfl) ⟨1022999, by rfl⟩ : syracuseStep 1363999 = 2045999) B2045999
theorem B2043959 : Blo 1362500 2043959 := bstep (se 1 (by rfl) ⟨1532969, by rfl⟩ : syracuseStep 2043959 = 3065939) B3065939
theorem B1364079 : Blo 1362500 1364079 := bstep (se 1 (by rfl) ⟨1023059, by rfl⟩ : syracuseStep 1364079 = 2046119) B2046119
theorem B3068135 : Blo 1362500 3068135 := bstep (se 1 (by rfl) ⟨2301101, by rfl⟩ : syracuseStep 3068135 = 4602203) B4602203
theorem B1364479 : Blo 1362500 1364479 := bstep (se 1 (by rfl) ⟨1023359, by rfl⟩ : syracuseStep 1364479 = 2046719) B2046719
theorem B2044457 : Blo 1362500 2044457 := bstep (se 2 (by rfl) ⟨766671, by rfl⟩ : syracuseStep 2044457 = 1533343) B1533343
theorem B3453779 : Blo 1362500 3453779 := bstep (se 1 (by rfl) ⟨2590334, by rfl⟩ : syracuseStep 3453779 = 5180669) B5180669
theorem B2044895 : Blo 1362500 2044895 := bstep (se 1 (by rfl) ⟨1533671, by rfl⟩ : syracuseStep 2044895 = 3067343) B3067343
theorem B22426739 : Blo 1362500 22426739 := bstep (se 1 (by rfl) ⟨16820054, by rfl⟩ : syracuseStep 22426739 = 33640109) B33640109
theorem B3880057 : Blo 1362500 3880057 := bstep (se 2 (by rfl) ⟨1455021, by rfl⟩ : syracuseStep 3880057 = 2910043) B2910043
theorem B3069395 : Blo 1362500 3069395 := bstep (se 1 (by rfl) ⟨2302046, by rfl⟩ : syracuseStep 3069395 = 4604093) B4604093
theorem B3069503 : Blo 1362500 3069503 := bstep (se 1 (by rfl) ⟨2302127, by rfl⟩ : syracuseStep 3069503 = 4604255) B4604255
theorem B2045543 : Blo 1362500 2045543 := bstep (se 1 (by rfl) ⟨1534157, by rfl⟩ : syracuseStep 2045543 = 3068315) B3068315
theorem B7370459 : Blo 1362500 7370459 := bstep (se 1 (by rfl) ⟨5527844, by rfl⟩ : syracuseStep 7370459 = 11055689) B11055689
theorem B3069665 : Blo 1362500 3069665 := bstep (se 2 (by rfl) ⟨1151124, by rfl⟩ : syracuseStep 3069665 = 2302249) B2302249
theorem B2045735 : Blo 1362500 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B10492049 : Blo 1362500 10492049 := bstep (se 2 (by rfl) ⟨3934518, by rfl⟩ : syracuseStep 10492049 = 7869037) B7869037
theorem B1456303 : Blo 1362500 1456303 := bstep (se 1 (by rfl) ⟨1092227, by rfl⟩ : syracuseStep 1456303 = 2184455) B2184455
theorem B19650863 : Blo 1362500 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B2046671 : Blo 1362500 2046671 := bstep (se 1 (by rfl) ⟨1535003, by rfl⟩ : syracuseStep 2046671 = 3070007) B3070007
theorem B5176295 : Blo 1362500 5176295 := bstep (se 1 (by rfl) ⟨3882221, by rfl⟩ : syracuseStep 5176295 = 7764443) B7764443
theorem B3988511 : Blo 1362500 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B3595367 : Blo 1362500 3595367 := bstep (se 1 (by rfl) ⟨2696525, by rfl⟩ : syracuseStep 3595367 = 5393051) B5393051
theorem B3284071 : Blo 1362500 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B15523325 : Blo 1362500 15523325 := bstep (se 3 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 15523325 = 5821247) B5821247
theorem B9330319 : Blo 1362500 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B3882791 : Blo 1362500 3882791 := bstep (se 1 (by rfl) ⟨2912093, by rfl⟩ : syracuseStep 3882791 = 5824187) B5824187
theorem B24895441 : Blo 1362500 24895441 := bstep (se 2 (by rfl) ⟨9335790, by rfl⟩ : syracuseStep 24895441 = 18671581) B18671581
theorem B4366295 : Blo 1362500 4366295 := bstep (se 1 (by rfl) ⟨3274721, by rfl⟩ : syracuseStep 4366295 = 6549443) B6549443
theorem B5677037 : Blo 1362500 5677037 := bstep (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) B2128889
theorem B2588755 : Blo 1362500 2588755 := bstep (se 1 (by rfl) ⟨1941566, by rfl⟩ : syracuseStep 2588755 = 3883133) B3883133
theorem B1941737 : Blo 1362500 1941737 := bstep (se 2 (by rfl) ⟨728151, by rfl⟩ : syracuseStep 1941737 = 1456303) B1456303
theorem B17515045 : Blo 1362500 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B2302519 : Blo 1362500 2302519 := bstep (se 1 (by rfl) ⟨1726889, by rfl⟩ : syracuseStep 2302519 = 3453779) B3453779
theorem B9830969 : Blo 1362500 9830969 := bstep (se 2 (by rfl) ⟨3686613, by rfl⟩ : syracuseStep 9830969 = 7373227) B7373227
theorem B14951159 : Blo 1362500 14951159 := bstep (se 1 (by rfl) ⟨11213369, by rfl⟩ : syracuseStep 14951159 = 22426739) B22426739
theorem B4604795 : Blo 1362500 4604795 := bstep (se 1 (by rfl) ⟨3453596, by rfl⟩ : syracuseStep 4604795 = 6907193) B6907193
theorem B3933623 : Blo 1362500 3933623 := bstep (se 1 (by rfl) ⟨2950217, by rfl⟩ : syracuseStep 3933623 = 5900435) B5900435
theorem B13100575 : Blo 1362500 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B119555875 : Blo 1362500 119555875 := bstep (se 1 (by rfl) ⟨89666906, by rfl⟩ : syracuseStep 119555875 = 179333813) B179333813
theorem B3450863 : Blo 1362500 3450863 := bstep (se 1 (by rfl) ⟨2588147, by rfl⟩ : syracuseStep 3450863 = 5176295) B5176295
theorem B5244983 : Blo 1362500 5244983 := bstep (se 1 (by rfl) ⟨3933737, by rfl⟩ : syracuseStep 5244983 = 7867475) B7867475
theorem B5179727 : Blo 1362500 5179727 := bstep (se 1 (by rfl) ⟨3884795, by rfl⟩ : syracuseStep 5179727 = 7769591) B7769591
theorem B10348883 : Blo 1362500 10348883 := bstep (se 1 (by rfl) ⟨7761662, by rfl⟩ : syracuseStep 10348883 = 15523325) B15523325
theorem B1362559 : Blo 1362500 1362559 := bstep (se 1 (by rfl) ⟨1021919, by rfl⟩ : syracuseStep 1362559 = 2043839) B2043839
theorem B2910863 : Blo 1362500 2910863 := bstep (se 1 (by rfl) ⟨2183147, by rfl⟩ : syracuseStep 2910863 = 4366295) B4366295
theorem B1362639 : Blo 1362500 1362639 := bstep (se 1 (by rfl) ⟨1021979, by rfl⟩ : syracuseStep 1362639 = 2043959) B2043959
theorem B1534783 : Blo 1362500 1534783 := bstep (se 1 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 1534783 = 2302175) B2302175
theorem B1362971 : Blo 1362500 1362971 := bstep (se 1 (by rfl) ⟨1022228, by rfl⟩ : syracuseStep 1362971 = 2044457) B2044457
theorem B27978797 : Blo 1362500 27978797 := bstep (se 3 (by rfl) ⟨5246024, by rfl⟩ : syracuseStep 27978797 = 10492049) B10492049
theorem B1363263 : Blo 1362500 1363263 := bstep (se 1 (by rfl) ⟨1022447, by rfl⟩ : syracuseStep 1363263 = 2044895) B2044895
theorem B49761701 : Blo 1362500 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B1363695 : Blo 1362500 1363695 := bstep (se 1 (by rfl) ⟨1022771, by rfl⟩ : syracuseStep 1363695 = 2045543) B2045543
theorem B1363823 : Blo 1362500 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B5173409 : Blo 1362500 5173409 := bstep (se 2 (by rfl) ⟨1940028, by rfl⟩ : syracuseStep 5173409 = 3880057) B3880057
theorem B2044079 : Blo 1362500 2044079 := bstep (se 1 (by rfl) ⟨1533059, by rfl⟩ : syracuseStep 2044079 = 3066119) B3066119
theorem B1364447 : Blo 1362500 1364447 := bstep (se 1 (by rfl) ⟨1023335, by rfl⟩ : syracuseStep 1364447 = 2046671) B2046671
theorem B16806587 : Blo 1362500 16806587 := bstep (se 1 (by rfl) ⟨12604940, by rfl⟩ : syracuseStep 16806587 = 25209881) B25209881
theorem B2659007 : Blo 1362500 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B3109595 : Blo 1362500 3109595 := bstep (se 1 (by rfl) ⟨2332196, by rfl⟩ : syracuseStep 3109595 = 4664393) B4664393
theorem B14947037 : Blo 1362500 14947037 := bstep (se 3 (by rfl) ⟨2802569, by rfl⟩ : syracuseStep 14947037 = 5605139) B5605139
theorem B2396911 : Blo 1362500 2396911 := bstep (se 1 (by rfl) ⟨1797683, by rfl⟩ : syracuseStep 2396911 = 3595367) B3595367
theorem B2044775 : Blo 1362500 2044775 := bstep (se 1 (by rfl) ⟨1533581, by rfl⟩ : syracuseStep 2044775 = 3067163) B3067163
theorem B2044799 : Blo 1362500 2044799 := bstep (se 1 (by rfl) ⟨1533599, by rfl⟩ : syracuseStep 2044799 = 3067199) B3067199
theorem B13284269 : Blo 1362500 13284269 := bstep (se 3 (by rfl) ⟨2490800, by rfl⟩ : syracuseStep 13284269 = 4981601) B4981601
theorem B4912255 : Blo 1362500 4912255 := bstep (se 1 (by rfl) ⟨3684191, by rfl⟩ : syracuseStep 4912255 = 7368383) B7368383
theorem B2045087 : Blo 1362500 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B8287535 : Blo 1362500 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B3069287 : Blo 1362500 3069287 := bstep (se 1 (by rfl) ⟨2301965, by rfl⟩ : syracuseStep 3069287 = 4603931) B4603931
theorem B2045423 : Blo 1362500 2045423 := bstep (se 1 (by rfl) ⟨1534067, by rfl⟩ : syracuseStep 2045423 = 3068135) B3068135
theorem B2045609 : Blo 1362500 2045609 := bstep (se 2 (by rfl) ⟨767103, by rfl⟩ : syracuseStep 2045609 = 1534207) B1534207
theorem B2299819 : Blo 1362500 2299819 := bstep (se 1 (by rfl) ⟨1724864, by rfl⟩ : syracuseStep 2299819 = 3449729) B3449729
theorem B2300143 : Blo 1362500 2300143 := bstep (se 1 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 2300143 = 3450215) B3450215
theorem B2046263 : Blo 1362500 2046263 := bstep (se 1 (by rfl) ⟨1534697, by rfl⟩ : syracuseStep 2046263 = 3069395) B3069395
theorem B2046329 : Blo 1362500 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B2046335 : Blo 1362500 2046335 := bstep (se 1 (by rfl) ⟨1534751, by rfl⟩ : syracuseStep 2046335 = 3069503) B3069503
theorem B4913639 : Blo 1362500 4913639 := bstep (se 1 (by rfl) ⟨3685229, by rfl⟩ : syracuseStep 4913639 = 7370459) B7370459
theorem B2046443 : Blo 1362500 2046443 := bstep (se 1 (by rfl) ⟨1534832, by rfl⟩ : syracuseStep 2046443 = 3069665) B3069665
theorem B16800443 : Blo 1362500 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B12614525 : Blo 1362500 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B19667933 : Blo 1362500 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B8732281 : Blo 1362500 8732281 := bstep (se 2 (by rfl) ⟨3274605, by rfl⟩ : syracuseStep 8732281 = 6549211) B6549211
theorem B2588527 : Blo 1362500 2588527 := bstep (se 1 (by rfl) ⟨1941395, by rfl⟩ : syracuseStep 2588527 = 3882791) B3882791
theorem B33193921 : Blo 1362500 33193921 := bstep (se 2 (by rfl) ⟨12447720, by rfl⟩ : syracuseStep 33193921 = 24895441) B24895441
theorem B3784691 : Blo 1362500 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B3448939 : Blo 1362500 3448939 := bstep (se 1 (by rfl) ⟨2586704, by rfl⟩ : syracuseStep 3448939 = 5173409) B5173409
theorem B93413573 : Blo 1362500 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B6553979 : Blo 1362500 6553979 := bstep (se 1 (by rfl) ⟨4915484, by rfl⟩ : syracuseStep 6553979 = 9830969) B9830969
theorem B5177965 : Blo 1362500 5177965 := bstep (se 3 (by rfl) ⟨970868, by rfl⟩ : syracuseStep 5177965 = 1941737) B1941737
theorem B8856179 : Blo 1362500 8856179 := bstep (se 1 (by rfl) ⟨6642134, by rfl⟩ : syracuseStep 8856179 = 13284269) B13284269
theorem B2622415 : Blo 1362500 2622415 := bstep (se 1 (by rfl) ⟨1966811, by rfl⟩ : syracuseStep 2622415 = 3933623) B3933623
theorem B3195881 : Blo 1362500 3195881 := bstep (se 2 (by rfl) ⟨1198455, by rfl⟩ : syracuseStep 3195881 = 2396911) B2396911
theorem B6899255 : Blo 1362500 6899255 := bstep (se 1 (by rfl) ⟨5174441, by rfl⟩ : syracuseStep 6899255 = 10348883) B10348883
theorem B11200295 : Blo 1362500 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B17467433 : Blo 1362500 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B11643041 : Blo 1362500 11643041 := bstep (se 2 (by rfl) ⟨4366140, by rfl⟩ : syracuseStep 11643041 = 8732281) B8732281
theorem B3451369 : Blo 1362500 3451369 := bstep (se 2 (by rfl) ⟨1294263, by rfl⟩ : syracuseStep 3451369 = 2588527) B2588527
theorem B3066425 : Blo 1362500 3066425 := bstep (se 2 (by rfl) ⟨1149909, by rfl⟩ : syracuseStep 3066425 = 2299819) B2299819
theorem B3451673 : Blo 1362500 3451673 := bstep (se 2 (by rfl) ⟨1294377, by rfl⟩ : syracuseStep 3451673 = 2588755) B2588755
theorem B1362719 : Blo 1362500 1362719 := bstep (se 1 (by rfl) ⟨1022039, by rfl⟩ : syracuseStep 1362719 = 2044079) B2044079
theorem B3066857 : Blo 1362500 3066857 := bstep (se 2 (by rfl) ⟨1150071, by rfl⟩ : syracuseStep 3066857 = 2300143) B2300143
theorem B1772671 : Blo 1362500 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B9964691 : Blo 1362500 9964691 := bstep (se 1 (by rfl) ⟨7473518, by rfl⟩ : syracuseStep 9964691 = 14947037) B14947037
theorem B1363183 : Blo 1362500 1363183 := bstep (se 1 (by rfl) ⟨1022387, by rfl⟩ : syracuseStep 1363183 = 2044775) B2044775
theorem B1363199 : Blo 1362500 1363199 := bstep (se 1 (by rfl) ⟨1022399, by rfl⟩ : syracuseStep 1363199 = 2044799) B2044799
theorem B1363391 : Blo 1362500 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B5525023 : Blo 1362500 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B1363615 : Blo 1362500 1363615 := bstep (se 1 (by rfl) ⟨1022711, by rfl⟩ : syracuseStep 1363615 = 2045423) B2045423
theorem B1363739 : Blo 1362500 1363739 := bstep (se 1 (by rfl) ⟨1022804, by rfl⟩ : syracuseStep 1363739 = 2045609) B2045609
theorem B6549673 : Blo 1362500 6549673 := bstep (se 2 (by rfl) ⟨2456127, by rfl⟩ : syracuseStep 6549673 = 4912255) B4912255
theorem B1364175 : Blo 1362500 1364175 := bstep (se 1 (by rfl) ⟨1023131, by rfl⟩ : syracuseStep 1364175 = 2046263) B2046263
theorem B3453151 : Blo 1362500 3453151 := bstep (se 1 (by rfl) ⟨2589863, by rfl⟩ : syracuseStep 3453151 = 5179727) B5179727
theorem B1364219 : Blo 1362500 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B1364223 : Blo 1362500 1364223 := bstep (se 1 (by rfl) ⟨1023167, by rfl⟩ : syracuseStep 1364223 = 2046335) B2046335
theorem B1364295 : Blo 1362500 1364295 := bstep (se 1 (by rfl) ⟨1023221, by rfl⟩ : syracuseStep 1364295 = 2046443) B2046443
theorem B7762301 : Blo 1362500 7762301 := bstep (se 3 (by rfl) ⟨1455431, by rfl⟩ : syracuseStep 7762301 = 2910863) B2910863
theorem B8409683 : Blo 1362500 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B13111955 : Blo 1362500 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B33174467 : Blo 1362500 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B44258561 : Blo 1362500 44258561 := bstep (se 2 (by rfl) ⟨16596960, by rfl⟩ : syracuseStep 44258561 = 33193921) B33193921
theorem B9967439 : Blo 1362500 9967439 := bstep (se 1 (by rfl) ⟨7475579, by rfl⟩ : syracuseStep 9967439 = 14951159) B14951159
theorem B3069863 : Blo 1362500 3069863 := bstep (se 1 (by rfl) ⟨2302397, by rfl⟩ : syracuseStep 3069863 = 4604795) B4604795
theorem B3070025 : Blo 1362500 3070025 := bstep (se 2 (by rfl) ⟨1151259, by rfl⟩ : syracuseStep 3070025 = 2302519) B2302519
theorem B2046191 : Blo 1362500 2046191 := bstep (se 1 (by rfl) ⟨1534643, by rfl⟩ : syracuseStep 2046191 = 3069287) B3069287
theorem B2046377 : Blo 1362500 2046377 := bstep (se 2 (by rfl) ⟨767391, by rfl⟩ : syracuseStep 2046377 = 1534783) B1534783
theorem B2300575 : Blo 1362500 2300575 := bstep (se 1 (by rfl) ⟨1725431, by rfl⟩ : syracuseStep 2300575 = 3450863) B3450863
theorem B3496655 : Blo 1362500 3496655 := bstep (se 1 (by rfl) ⟨2622491, by rfl⟩ : syracuseStep 3496655 = 5244983) B5244983
theorem B3275759 : Blo 1362500 3275759 := bstep (se 1 (by rfl) ⟨2456819, by rfl⟩ : syracuseStep 3275759 = 4913639) B4913639
theorem B44817565 : Blo 1362500 44817565 := bstep (se 3 (by rfl) ⟨8403293, by rfl⟩ : syracuseStep 44817565 = 16806587) B16806587
theorem B18652531 : Blo 1362500 18652531 := bstep (se 1 (by rfl) ⟨13989398, by rfl⟩ : syracuseStep 18652531 = 27978797) B27978797
theorem B33169013 : Blo 1362500 33169013 := bstep (se 5 (by rfl) ⟨1554797, by rfl⟩ : syracuseStep 33169013 = 3109595) B3109595
theorem B159407833 : Blo 1362500 159407833 := bstep (se 2 (by rfl) ⟨59777937, by rfl⟩ : syracuseStep 159407833 = 119555875) B119555875
theorem B10092509 : Blo 1362500 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B62275715 : Blo 1362500 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B8732897 : Blo 1362500 8732897 := bstep (se 2 (by rfl) ⟨3274836, by rfl⟩ : syracuseStep 8732897 = 6549673) B6549673
theorem B4604201 : Blo 1362500 4604201 := bstep (se 2 (by rfl) ⟨1726575, by rfl⟩ : syracuseStep 4604201 = 3453151) B3453151
theorem B8741303 : Blo 1362500 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B2130587 : Blo 1362500 2130587 := bstep (se 1 (by rfl) ⟨1597940, by rfl⟩ : syracuseStep 2130587 = 3195881) B3195881
theorem B6644959 : Blo 1362500 6644959 := bstep (se 1 (by rfl) ⟨4983719, by rfl⟩ : syracuseStep 6644959 = 9967439) B9967439
theorem B7366697 : Blo 1362500 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B212543777 : Blo 1362500 212543777 := bstep (se 2 (by rfl) ⟨79703916, by rfl⟩ : syracuseStep 212543777 = 159407833) B159407833
theorem B22112675 : Blo 1362500 22112675 := bstep (se 1 (by rfl) ⟨16584506, by rfl⟩ : syracuseStep 22112675 = 33169013) B33169013
theorem B8735357 : Blo 1362500 8735357 := bstep (se 3 (by rfl) ⟨1637879, by rfl⟩ : syracuseStep 8735357 = 3275759) B3275759
theorem B6728339 : Blo 1362500 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B4598585 : Blo 1362500 4598585 := bstep (se 2 (by rfl) ⟨1724469, by rfl⟩ : syracuseStep 4598585 = 3448939) B3448939
theorem B4369319 : Blo 1362500 4369319 := bstep (se 1 (by rfl) ⟨3276989, by rfl⟩ : syracuseStep 4369319 = 6553979) B6553979
theorem B5606455 : Blo 1362500 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B3067433 : Blo 1362500 3067433 := bstep (se 2 (by rfl) ⟨1150287, by rfl⟩ : syracuseStep 3067433 = 2300575) B2300575
theorem B4599503 : Blo 1362500 4599503 := bstep (se 1 (by rfl) ⟨3449627, by rfl⟩ : syracuseStep 4599503 = 6899255) B6899255
theorem B7466863 : Blo 1362500 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B11644955 : Blo 1362500 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B7762027 : Blo 1362500 7762027 := bstep (se 1 (by rfl) ⟨5821520, by rfl⟩ : syracuseStep 7762027 = 11643041) B11643041
theorem B1364127 : Blo 1362500 1364127 := bstep (se 1 (by rfl) ⟨1023095, by rfl⟩ : syracuseStep 1364127 = 2046191) B2046191
theorem B2363561 : Blo 1362500 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B59756753 : Blo 1362500 59756753 := bstep (se 2 (by rfl) ⟨22408782, by rfl⟩ : syracuseStep 59756753 = 44817565) B44817565
theorem B1364251 : Blo 1362500 1364251 := bstep (se 1 (by rfl) ⟨1023188, by rfl⟩ : syracuseStep 1364251 = 2046377) B2046377
theorem B2044283 : Blo 1362500 2044283 := bstep (se 1 (by rfl) ⟨1533212, by rfl⟩ : syracuseStep 2044283 = 3066425) B3066425
theorem B2331103 : Blo 1362500 2331103 := bstep (se 1 (by rfl) ⟨1748327, by rfl⟩ : syracuseStep 2331103 = 3496655) B3496655
theorem B2044571 : Blo 1362500 2044571 := bstep (se 1 (by rfl) ⟨1533428, by rfl⟩ : syracuseStep 2044571 = 3066857) B3066857
theorem B5174867 : Blo 1362500 5174867 := bstep (se 1 (by rfl) ⟨3881150, by rfl⟩ : syracuseStep 5174867 = 7762301) B7762301
theorem B5904119 : Blo 1362500 5904119 := bstep (se 1 (by rfl) ⟨4428089, by rfl⟩ : syracuseStep 5904119 = 8856179) B8856179
theorem B22116311 : Blo 1362500 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B4601825 : Blo 1362500 4601825 := bstep (se 2 (by rfl) ⟨1725684, by rfl⟩ : syracuseStep 4601825 = 3451369) B3451369
theorem B6903953 : Blo 1362500 6903953 := bstep (se 2 (by rfl) ⟨2588982, by rfl⟩ : syracuseStep 6903953 = 5177965) B5177965
theorem B29505707 : Blo 1362500 29505707 := bstep (se 1 (by rfl) ⟨22129280, by rfl⟩ : syracuseStep 29505707 = 44258561) B44258561
theorem B3496553 : Blo 1362500 3496553 := bstep (se 2 (by rfl) ⟨1311207, by rfl⟩ : syracuseStep 3496553 = 2622415) B2622415
theorem B2046575 : Blo 1362500 2046575 := bstep (se 1 (by rfl) ⟨1534931, by rfl⟩ : syracuseStep 2046575 = 3069863) B3069863
theorem B2046683 : Blo 1362500 2046683 := bstep (se 1 (by rfl) ⟨1535012, by rfl⟩ : syracuseStep 2046683 = 3070025) B3070025
theorem B24870041 : Blo 1362500 24870041 := bstep (se 2 (by rfl) ⟨9326265, by rfl⟩ : syracuseStep 24870041 = 18652531) B18652531
theorem B2301115 : Blo 1362500 2301115 := bstep (se 1 (by rfl) ⟨1725836, by rfl⟩ : syracuseStep 2301115 = 3451673) B3451673
theorem B6643127 : Blo 1362500 6643127 := bstep (se 1 (by rfl) ⟨4982345, by rfl⟩ : syracuseStep 6643127 = 9964691) B9964691
theorem B41517143 : Blo 1362500 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B39837835 : Blo 1362500 39837835 := bstep (se 1 (by rfl) ⟨29878376, by rfl⟩ : syracuseStep 39837835 = 59756753) B59756753
theorem B3449911 : Blo 1362500 3449911 := bstep (se 1 (by rfl) ⟨2587433, by rfl⟩ : syracuseStep 3449911 = 5174867) B5174867
theorem B35439781 : Blo 1362500 35439781 := bstep (se 4 (by rfl) ⟨3322479, by rfl⟩ : syracuseStep 35439781 = 6644959) B6644959
theorem B19670471 : Blo 1362500 19670471 := bstep (se 1 (by rfl) ⟨14752853, by rfl⟩ : syracuseStep 19670471 = 29505707) B29505707
theorem B3065723 : Blo 1362500 3065723 := bstep (se 1 (by rfl) ⟨2299292, by rfl⟩ : syracuseStep 3065723 = 4598585) B4598585
theorem B3066335 : Blo 1362500 3066335 := bstep (se 1 (by rfl) ⟨2299751, by rfl⟩ : syracuseStep 3066335 = 4599503) B4599503
theorem B9955817 : Blo 1362500 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B1575707 : Blo 1362500 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B10349369 : Blo 1362500 10349369 := bstep (se 2 (by rfl) ⟨3881013, by rfl⟩ : syracuseStep 10349369 = 7762027) B7762027
theorem B1362855 : Blo 1362500 1362855 := bstep (se 1 (by rfl) ⟨1022141, by rfl⟩ : syracuseStep 1362855 = 2044283) B2044283
theorem B5827535 : Blo 1362500 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B1363047 : Blo 1362500 1363047 := bstep (se 1 (by rfl) ⟨1022285, by rfl⟩ : syracuseStep 1363047 = 2044571) B2044571
theorem B1420391 : Blo 1362500 1420391 := bstep (se 1 (by rfl) ⟨1065293, by rfl⟩ : syracuseStep 1420391 = 2130587) B2130587
theorem B3108137 : Blo 1362500 3108137 := bstep (se 2 (by rfl) ⟨1165551, by rfl⟩ : syracuseStep 3108137 = 2331103) B2331103
theorem B3936079 : Blo 1362500 3936079 := bstep (se 1 (by rfl) ⟨2952059, by rfl⟩ : syracuseStep 3936079 = 5904119) B5904119
theorem B3067883 : Blo 1362500 3067883 := bstep (se 1 (by rfl) ⟨2300912, by rfl⟩ : syracuseStep 3067883 = 4601825) B4601825
theorem B4911131 : Blo 1362500 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B7475273 : Blo 1362500 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B3068153 : Blo 1362500 3068153 := bstep (se 2 (by rfl) ⟨1150557, by rfl⟩ : syracuseStep 3068153 = 2301115) B2301115
theorem B14741783 : Blo 1362500 14741783 := bstep (se 1 (by rfl) ⟨11056337, by rfl⟩ : syracuseStep 14741783 = 22112675) B22112675
theorem B2331035 : Blo 1362500 2331035 := bstep (se 1 (by rfl) ⟨1748276, by rfl⟩ : syracuseStep 2331035 = 3496553) B3496553
theorem B1364383 : Blo 1362500 1364383 := bstep (se 1 (by rfl) ⟨1023287, by rfl⟩ : syracuseStep 1364383 = 2046575) B2046575
theorem B4485559 : Blo 1362500 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B1364455 : Blo 1362500 1364455 := bstep (se 1 (by rfl) ⟨1023341, by rfl⟩ : syracuseStep 1364455 = 2046683) B2046683
theorem B2912879 : Blo 1362500 2912879 := bstep (se 1 (by rfl) ⟨2184659, by rfl⟩ : syracuseStep 2912879 = 4369319) B4369319
theorem B4428751 : Blo 1362500 4428751 := bstep (se 1 (by rfl) ⟨3321563, by rfl⟩ : syracuseStep 4428751 = 6643127) B6643127
theorem B2044955 : Blo 1362500 2044955 := bstep (se 1 (by rfl) ⟨1533716, by rfl⟩ : syracuseStep 2044955 = 3067433) B3067433
theorem B7763303 : Blo 1362500 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B5821931 : Blo 1362500 5821931 := bstep (se 1 (by rfl) ⟨4366448, by rfl⟩ : syracuseStep 5821931 = 8732897) B8732897
theorem B3069467 : Blo 1362500 3069467 := bstep (se 1 (by rfl) ⟨2302100, by rfl⟩ : syracuseStep 3069467 = 4604201) B4604201
theorem B14744207 : Blo 1362500 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B4602635 : Blo 1362500 4602635 := bstep (se 1 (by rfl) ⟨3451976, by rfl⟩ : syracuseStep 4602635 = 6903953) B6903953
theorem B141695851 : Blo 1362500 141695851 := bstep (se 1 (by rfl) ⟨106271888, by rfl⟩ : syracuseStep 141695851 = 212543777) B212543777
theorem B5823571 : Blo 1362500 5823571 := bstep (se 1 (by rfl) ⟨4367678, by rfl⟩ : syracuseStep 5823571 = 8735357) B8735357
theorem B16580027 : Blo 1362500 16580027 := bstep (se 1 (by rfl) ⟨12435020, by rfl⟩ : syracuseStep 16580027 = 24870041) B24870041
theorem B5980745 : Blo 1362500 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B212468453 : Blo 1362500 212468453 := bstep (se 4 (by rfl) ⟨19918917, by rfl⟩ : syracuseStep 212468453 = 39837835) B39837835
theorem B47253041 : Blo 1362500 47253041 := bstep (se 2 (by rfl) ⟨17719890, by rfl⟩ : syracuseStep 47253041 = 35439781) B35439781
theorem B7767677 : Blo 1362500 7767677 := bstep (se 3 (by rfl) ⟨1456439, by rfl⟩ : syracuseStep 7767677 = 2912879) B2912879
theorem B6637211 : Blo 1362500 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B6899579 : Blo 1362500 6899579 := bstep (se 1 (by rfl) ⟨5174684, by rfl⟩ : syracuseStep 6899579 = 10349369) B10349369
theorem B3885023 : Blo 1362500 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B11053351 : Blo 1362500 11053351 := bstep (se 1 (by rfl) ⟨8290013, by rfl⟩ : syracuseStep 11053351 = 16580027) B16580027
theorem B4983515 : Blo 1362500 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B3787709 : Blo 1362500 3787709 := bstep (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) B1420391
theorem B1363303 : Blo 1362500 1363303 := bstep (se 1 (by rfl) ⟨1022477, by rfl⟩ : syracuseStep 1363303 = 2044955) B2044955
theorem B188927801 : Blo 1362500 188927801 := bstep (se 2 (by rfl) ⟨70847925, by rfl⟩ : syracuseStep 188927801 = 141695851) B141695851
theorem B2043815 : Blo 1362500 2043815 := bstep (se 1 (by rfl) ⟨1532861, by rfl⟩ : syracuseStep 2043815 = 3065723) B3065723
theorem B4599881 : Blo 1362500 4599881 := bstep (se 2 (by rfl) ⟨1724955, by rfl⟩ : syracuseStep 4599881 = 3449911) B3449911
theorem B2044223 : Blo 1362500 2044223 := bstep (se 1 (by rfl) ⟨1533167, by rfl⟩ : syracuseStep 2044223 = 3066335) B3066335
theorem B20992421 : Blo 1362500 20992421 := bstep (se 4 (by rfl) ⟨1968039, by rfl⟩ : syracuseStep 20992421 = 3936079) B3936079
theorem B3068423 : Blo 1362500 3068423 := bstep (se 1 (by rfl) ⟨2301317, by rfl⟩ : syracuseStep 3068423 = 4602635) B4602635
theorem B2045255 : Blo 1362500 2045255 := bstep (se 1 (by rfl) ⟨1533941, by rfl⟩ : syracuseStep 2045255 = 3067883) B3067883
theorem B27678095 : Blo 1362500 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B13096349 : Blo 1362500 13096349 := bstep (se 3 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 13096349 = 4911131) B4911131
theorem B2045435 : Blo 1362500 2045435 := bstep (se 1 (by rfl) ⟨1534076, by rfl⟩ : syracuseStep 2045435 = 3068153) B3068153
theorem B9827855 : Blo 1362500 9827855 := bstep (se 1 (by rfl) ⟨7370891, by rfl⟩ : syracuseStep 9827855 = 14741783) B14741783
theorem B1554023 : Blo 1362500 1554023 := bstep (se 1 (by rfl) ⟨1165517, by rfl⟩ : syracuseStep 1554023 = 2331035) B2331035
theorem B8288365 : Blo 1362500 8288365 := bstep (se 3 (by rfl) ⟨1554068, by rfl⟩ : syracuseStep 8288365 = 3108137) B3108137
theorem B5175535 : Blo 1362500 5175535 := bstep (se 1 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 5175535 = 7763303) B7763303
theorem B13113647 : Blo 1362500 13113647 := bstep (se 1 (by rfl) ⟨9835235, by rfl⟩ : syracuseStep 13113647 = 19670471) B19670471
theorem B3881287 : Blo 1362500 3881287 := bstep (se 1 (by rfl) ⟨2910965, by rfl⟩ : syracuseStep 3881287 = 5821931) B5821931
theorem B2046311 : Blo 1362500 2046311 := bstep (se 1 (by rfl) ⟨1534733, by rfl⟩ : syracuseStep 2046311 = 3069467) B3069467
theorem B5905001 : Blo 1362500 5905001 := bstep (se 2 (by rfl) ⟨2214375, by rfl⟩ : syracuseStep 5905001 = 4428751) B4428751
theorem B7764761 : Blo 1362500 7764761 := bstep (se 2 (by rfl) ⟨2911785, by rfl⟩ : syracuseStep 7764761 = 5823571) B5823571
theorem B9829471 : Blo 1362500 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B4201885 : Blo 1362500 4201885 := bstep (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) B1575707
theorem B11051153 : Blo 1362500 11051153 := bstep (se 2 (by rfl) ⟨4144182, by rfl⟩ : syracuseStep 11051153 = 8288365) B8288365
theorem B14737801 : Blo 1362500 14737801 := bstep (se 2 (by rfl) ⟨5526675, by rfl⟩ : syracuseStep 14737801 = 11053351) B11053351
theorem B5178451 : Blo 1362500 5178451 := bstep (se 1 (by rfl) ⟨3883838, by rfl⟩ : syracuseStep 5178451 = 7767677) B7767677
theorem B4424807 : Blo 1362500 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B8742431 : Blo 1362500 8742431 := bstep (se 1 (by rfl) ⟨6556823, by rfl⟩ : syracuseStep 8742431 = 13113647) B13113647
theorem B1362543 : Blo 1362500 1362543 := bstep (se 1 (by rfl) ⟨1021907, by rfl⟩ : syracuseStep 1362543 = 2043815) B2043815
theorem B3066587 : Blo 1362500 3066587 := bstep (se 1 (by rfl) ⟨2299940, by rfl⟩ : syracuseStep 3066587 = 4599881) B4599881
theorem B1362815 : Blo 1362500 1362815 := bstep (se 1 (by rfl) ⟨1022111, by rfl⟩ : syracuseStep 1362815 = 2044223) B2044223
theorem B13994947 : Blo 1362500 13994947 := bstep (se 1 (by rfl) ⟨10496210, by rfl⟩ : syracuseStep 13994947 = 20992421) B20992421
theorem B6900713 : Blo 1362500 6900713 := bstep (se 2 (by rfl) ⟨2587767, by rfl⟩ : syracuseStep 6900713 = 5175535) B5175535
theorem B1363503 : Blo 1362500 1363503 := bstep (se 1 (by rfl) ⟨1022627, by rfl⟩ : syracuseStep 1363503 = 2045255) B2045255
theorem B18452063 : Blo 1362500 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B1363623 : Blo 1362500 1363623 := bstep (se 1 (by rfl) ⟨1022717, by rfl⟩ : syracuseStep 1363623 = 2045435) B2045435
theorem B31502027 : Blo 1362500 31502027 := bstep (se 1 (by rfl) ⟨23626520, by rfl⟩ : syracuseStep 31502027 = 47253041) B47253041
theorem B4599719 : Blo 1362500 4599719 := bstep (se 1 (by rfl) ⟨3449789, by rfl⟩ : syracuseStep 4599719 = 6899579) B6899579
theorem B1364207 : Blo 1362500 1364207 := bstep (se 1 (by rfl) ⟨1023155, by rfl⟩ : syracuseStep 1364207 = 2046311) B2046311
theorem B3936667 : Blo 1362500 3936667 := bstep (se 1 (by rfl) ⟨2952500, by rfl⟩ : syracuseStep 3936667 = 5905001) B5905001
theorem B3322343 : Blo 1362500 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B22410053 : Blo 1362500 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B10360061 : Blo 1362500 10360061 := bstep (se 3 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 10360061 = 3885023) B3885023
theorem B2045615 : Blo 1362500 2045615 := bstep (se 1 (by rfl) ⟨1534211, by rfl⟩ : syracuseStep 2045615 = 3068423) B3068423
theorem B3987163 : Blo 1362500 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B5175049 : Blo 1362500 5175049 := bstep (se 2 (by rfl) ⟨1940643, by rfl⟩ : syracuseStep 5175049 = 3881287) B3881287
theorem B141645635 : Blo 1362500 141645635 := bstep (se 1 (by rfl) ⟨106234226, by rfl⟩ : syracuseStep 141645635 = 212468453) B212468453
theorem B8730899 : Blo 1362500 8730899 := bstep (se 1 (by rfl) ⟨6548174, by rfl⟩ : syracuseStep 8730899 = 13096349) B13096349
theorem B6551903 : Blo 1362500 6551903 := bstep (se 1 (by rfl) ⟨4913927, by rfl⟩ : syracuseStep 6551903 = 9827855) B9827855
theorem B13105961 : Blo 1362500 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B4144061 : Blo 1362500 4144061 := bstep (se 3 (by rfl) ⟨777011, by rfl⟩ : syracuseStep 4144061 = 1554023) B1554023
theorem B5176507 : Blo 1362500 5176507 := bstep (se 1 (by rfl) ⟨3882380, by rfl⟩ : syracuseStep 5176507 = 7764761) B7764761
theorem B10100557 : Blo 1362500 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B125951867 : Blo 1362500 125951867 := bstep (se 1 (by rfl) ⟨94463900, by rfl⟩ : syracuseStep 125951867 = 188927801) B188927801
theorem B2949871 : Blo 1362500 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B6906707 : Blo 1362500 6906707 := bstep (se 1 (by rfl) ⟨5180030, by rfl⟩ : syracuseStep 6906707 = 10360061) B10360061
theorem B94430423 : Blo 1362500 94430423 := bstep (se 1 (by rfl) ⟨70822817, by rfl⟩ : syracuseStep 94430423 = 141645635) B141645635
theorem B4367935 : Blo 1362500 4367935 := bstep (se 1 (by rfl) ⟨3275951, by rfl⟩ : syracuseStep 4367935 = 6551903) B6551903
theorem B6900065 : Blo 1362500 6900065 := bstep (se 2 (by rfl) ⟨2587524, by rfl⟩ : syracuseStep 6900065 = 5175049) B5175049
theorem B3066479 : Blo 1362500 3066479 := bstep (se 1 (by rfl) ⟨2299859, by rfl⟩ : syracuseStep 3066479 = 4599719) B4599719
theorem B7367435 : Blo 1362500 7367435 := bstep (se 1 (by rfl) ⟨5525576, by rfl⟩ : syracuseStep 7367435 = 11051153) B11051153
theorem B5828287 : Blo 1362500 5828287 := bstep (se 1 (by rfl) ⟨4371215, by rfl⟩ : syracuseStep 5828287 = 8742431) B8742431
theorem B1363743 : Blo 1362500 1363743 := bstep (se 1 (by rfl) ⟨1022807, by rfl⟩ : syracuseStep 1363743 = 2045615) B2045615
theorem B8859581 : Blo 1362500 8859581 := bstep (se 3 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 8859581 = 3322343) B3322343
theorem B5820599 : Blo 1362500 5820599 := bstep (se 1 (by rfl) ⟨4365449, by rfl⟩ : syracuseStep 5820599 = 8730899) B8730899
theorem B6902009 : Blo 1362500 6902009 := bstep (se 2 (by rfl) ⟨2588253, by rfl⟩ : syracuseStep 6902009 = 5176507) B5176507
theorem B2044391 : Blo 1362500 2044391 := bstep (se 1 (by rfl) ⟨1533293, by rfl⟩ : syracuseStep 2044391 = 3066587) B3066587
theorem B8737307 : Blo 1362500 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B4600475 : Blo 1362500 4600475 := bstep (se 1 (by rfl) ⟨3450356, by rfl⟩ : syracuseStep 4600475 = 6900713) B6900713
theorem B12301375 : Blo 1362500 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B21001351 : Blo 1362500 21001351 := bstep (se 1 (by rfl) ⟨15751013, by rfl⟩ : syracuseStep 21001351 = 31502027) B31502027
theorem B19650401 : Blo 1362500 19650401 := bstep (se 2 (by rfl) ⟨7368900, by rfl⟩ : syracuseStep 19650401 = 14737801) B14737801
theorem B5248889 : Blo 1362500 5248889 := bstep (se 2 (by rfl) ⟨1968333, by rfl⟩ : syracuseStep 5248889 = 3936667) B3936667
theorem B14940035 : Blo 1362500 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B21264869 : Blo 1362500 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B18659929 : Blo 1362500 18659929 := bstep (se 2 (by rfl) ⟨6997473, by rfl⟩ : syracuseStep 18659929 = 13994947) B13994947
theorem B6904601 : Blo 1362500 6904601 := bstep (se 2 (by rfl) ⟨2589225, by rfl⟩ : syracuseStep 6904601 = 5178451) B5178451
theorem B53869637 : Blo 1362500 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B11050829 : Blo 1362500 11050829 := bstep (se 3 (by rfl) ⟨2072030, by rfl⟩ : syracuseStep 11050829 = 4144061) B4144061
theorem B83967911 : Blo 1362500 83967911 := bstep (se 1 (by rfl) ⟨62975933, by rfl⟩ : syracuseStep 83967911 = 125951867) B125951867
theorem B5824871 : Blo 1362500 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B4604471 : Blo 1362500 4604471 := bstep (se 1 (by rfl) ⟨3453353, by rfl⟩ : syracuseStep 4604471 = 6906707) B6906707
theorem B24879905 : Blo 1362500 24879905 := bstep (se 2 (by rfl) ⟨9329964, by rfl⟩ : syracuseStep 24879905 = 18659929) B18659929
theorem B3933161 : Blo 1362500 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B13100267 : Blo 1362500 13100267 := bstep (se 1 (by rfl) ⟨9825200, by rfl⟩ : syracuseStep 13100267 = 19650401) B19650401
theorem B3499259 : Blo 1362500 3499259 := bstep (se 1 (by rfl) ⟨2624444, by rfl⟩ : syracuseStep 3499259 = 5248889) B5248889
theorem B16401833 : Blo 1362500 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B28001801 : Blo 1362500 28001801 := bstep (se 2 (by rfl) ⟨10500675, by rfl⟩ : syracuseStep 28001801 = 21001351) B21001351
theorem B7367219 : Blo 1362500 7367219 := bstep (se 1 (by rfl) ⟨5525414, by rfl⟩ : syracuseStep 7367219 = 11050829) B11050829
theorem B55978607 : Blo 1362500 55978607 := bstep (se 1 (by rfl) ⟨41983955, by rfl⟩ : syracuseStep 55978607 = 83967911) B83967911
theorem B1362927 : Blo 1362500 1362927 := bstep (se 1 (by rfl) ⟨1022195, by rfl⟩ : syracuseStep 1362927 = 2044391) B2044391
theorem B3066983 : Blo 1362500 3066983 := bstep (se 1 (by rfl) ⟨2300237, by rfl⟩ : syracuseStep 3066983 = 4600475) B4600475
theorem B4600043 : Blo 1362500 4600043 := bstep (se 1 (by rfl) ⟨3450032, by rfl⟩ : syracuseStep 4600043 = 6900065) B6900065
theorem B14176579 : Blo 1362500 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B2044319 : Blo 1362500 2044319 := bstep (se 1 (by rfl) ⟨1533239, by rfl⟩ : syracuseStep 2044319 = 3066479) B3066479
theorem B4911623 : Blo 1362500 4911623 := bstep (se 1 (by rfl) ⟨3683717, by rfl⟩ : syracuseStep 4911623 = 7367435) B7367435
theorem B7771049 : Blo 1362500 7771049 := bstep (se 2 (by rfl) ⟨2914143, by rfl⟩ : syracuseStep 7771049 = 5828287) B5828287
theorem B3880399 : Blo 1362500 3880399 := bstep (se 1 (by rfl) ⟨2910299, by rfl⟩ : syracuseStep 3880399 = 5820599) B5820599
theorem B4601339 : Blo 1362500 4601339 := bstep (se 1 (by rfl) ⟨3451004, by rfl⟩ : syracuseStep 4601339 = 6902009) B6902009
theorem B143652365 : Blo 1362500 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B62953615 : Blo 1362500 62953615 := bstep (se 1 (by rfl) ⟨47215211, by rfl⟩ : syracuseStep 62953615 = 94430423) B94430423
theorem B9960023 : Blo 1362500 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B4603067 : Blo 1362500 4603067 := bstep (se 1 (by rfl) ⟨3452300, by rfl⟩ : syracuseStep 4603067 = 6904601) B6904601
theorem B5823913 : Blo 1362500 5823913 := bstep (se 2 (by rfl) ⟨2183967, by rfl⟩ : syracuseStep 5823913 = 4367935) B4367935
theorem B5906387 : Blo 1362500 5906387 := bstep (se 1 (by rfl) ⟨4429790, by rfl⟩ : syracuseStep 5906387 = 8859581) B8859581
theorem B3883247 : Blo 1362500 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B2622107 : Blo 1362500 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B9331357 : Blo 1362500 9331357 := bstep (se 3 (by rfl) ⟨1749629, by rfl⟩ : syracuseStep 9331357 = 3499259) B3499259
theorem B8733511 : Blo 1362500 8733511 := bstep (se 1 (by rfl) ⟨6550133, by rfl⟩ : syracuseStep 8733511 = 13100267) B13100267
theorem B3066695 : Blo 1362500 3066695 := bstep (se 1 (by rfl) ⟨2300021, by rfl⟩ : syracuseStep 3066695 = 4600043) B4600043
theorem B83938153 : Blo 1362500 83938153 := bstep (se 2 (by rfl) ⟨31476807, by rfl⟩ : syracuseStep 83938153 = 62953615) B62953615
theorem B1362879 : Blo 1362500 1362879 := bstep (se 1 (by rfl) ⟨1022159, by rfl⟩ : syracuseStep 1362879 = 2044319) B2044319
theorem B18902105 : Blo 1362500 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B5180699 : Blo 1362500 5180699 := bstep (se 1 (by rfl) ⟨3885524, by rfl⟩ : syracuseStep 5180699 = 7771049) B7771049
theorem B3067559 : Blo 1362500 3067559 := bstep (se 1 (by rfl) ⟨2300669, by rfl⟩ : syracuseStep 3067559 = 4601339) B4601339
theorem B95768243 : Blo 1362500 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B4911479 : Blo 1362500 4911479 := bstep (se 1 (by rfl) ⟨3683609, by rfl⟩ : syracuseStep 4911479 = 7367219) B7367219
theorem B6640015 : Blo 1362500 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B37319071 : Blo 1362500 37319071 := bstep (se 1 (by rfl) ⟨27989303, by rfl⟩ : syracuseStep 37319071 = 55978607) B55978607
theorem B174952885 : Blo 1362500 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B5173865 : Blo 1362500 5173865 := bstep (se 2 (by rfl) ⟨1940199, by rfl⟩ : syracuseStep 5173865 = 3880399) B3880399
theorem B2044655 : Blo 1362500 2044655 := bstep (se 1 (by rfl) ⟨1533491, by rfl⟩ : syracuseStep 2044655 = 3066983) B3066983
theorem B3068711 : Blo 1362500 3068711 := bstep (se 1 (by rfl) ⟨2301533, by rfl⟩ : syracuseStep 3068711 = 4603067) B4603067
theorem B3937591 : Blo 1362500 3937591 := bstep (se 1 (by rfl) ⟨2953193, by rfl⟩ : syracuseStep 3937591 = 5906387) B5906387
theorem B3274415 : Blo 1362500 3274415 := bstep (se 1 (by rfl) ⟨2455811, by rfl⟩ : syracuseStep 3274415 = 4911623) B4911623
theorem B3069647 : Blo 1362500 3069647 := bstep (se 1 (by rfl) ⟨2302235, by rfl⟩ : syracuseStep 3069647 = 4604471) B4604471
theorem B16586603 : Blo 1362500 16586603 := bstep (se 1 (by rfl) ⟨12439952, by rfl⟩ : syracuseStep 16586603 = 24879905) B24879905
theorem B18667867 : Blo 1362500 18667867 := bstep (se 1 (by rfl) ⟨14000900, by rfl⟩ : syracuseStep 18667867 = 28001801) B28001801
theorem B7765217 : Blo 1362500 7765217 := bstep (se 2 (by rfl) ⟨2911956, by rfl⟩ : syracuseStep 7765217 = 5823913) B5823913
theorem B2588831 : Blo 1362500 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B3449243 : Blo 1362500 3449243 := bstep (se 1 (by rfl) ⟨2586932, by rfl⟩ : syracuseStep 3449243 = 5173865) B5173865
theorem B49758761 : Blo 1362500 49758761 := bstep (se 2 (by rfl) ⟨18659535, by rfl⟩ : syracuseStep 49758761 = 37319071) B37319071
theorem B12601403 : Blo 1362500 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B1748071 : Blo 1362500 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B24890489 : Blo 1362500 24890489 := bstep (se 2 (by rfl) ⟨9333933, by rfl⟩ : syracuseStep 24890489 = 18667867) B18667867
theorem B1363103 : Blo 1362500 1363103 := bstep (se 1 (by rfl) ⟨1022327, by rfl⟩ : syracuseStep 1363103 = 2044655) B2044655
theorem B233270513 : Blo 1362500 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B11644681 : Blo 1362500 11644681 := bstep (se 2 (by rfl) ⟨4366755, by rfl⟩ : syracuseStep 11644681 = 8733511) B8733511
theorem B2182943 : Blo 1362500 2182943 := bstep (se 1 (by rfl) ⟨1637207, by rfl⟩ : syracuseStep 2182943 = 3274415) B3274415
theorem B21000485 : Blo 1362500 21000485 := bstep (se 4 (by rfl) ⟨1968795, by rfl⟩ : syracuseStep 21000485 = 3937591) B3937591
theorem B2044463 : Blo 1362500 2044463 := bstep (se 1 (by rfl) ⟨1533347, by rfl⟩ : syracuseStep 2044463 = 3066695) B3066695
theorem B3453799 : Blo 1362500 3453799 := bstep (se 1 (by rfl) ⟨2590349, by rfl⟩ : syracuseStep 3453799 = 5180699) B5180699
theorem B2045039 : Blo 1362500 2045039 := bstep (se 1 (by rfl) ⟨1533779, by rfl⟩ : syracuseStep 2045039 = 3067559) B3067559
theorem B63845495 : Blo 1362500 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B3274319 : Blo 1362500 3274319 := bstep (se 1 (by rfl) ⟨2455739, by rfl⟩ : syracuseStep 3274319 = 4911479) B4911479
theorem B8853353 : Blo 1362500 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B2045807 : Blo 1362500 2045807 := bstep (se 1 (by rfl) ⟨1534355, by rfl⟩ : syracuseStep 2045807 = 3068711) B3068711
theorem B12441809 : Blo 1362500 12441809 := bstep (se 2 (by rfl) ⟨4665678, by rfl⟩ : syracuseStep 12441809 = 9331357) B9331357
theorem B2046431 : Blo 1362500 2046431 := bstep (se 1 (by rfl) ⟨1534823, by rfl⟩ : syracuseStep 2046431 = 3069647) B3069647
theorem B111917537 : Blo 1362500 111917537 := bstep (se 2 (by rfl) ⟨41969076, by rfl⟩ : syracuseStep 111917537 = 83938153) B83938153
theorem B11057735 : Blo 1362500 11057735 := bstep (se 1 (by rfl) ⟨8293301, by rfl⟩ : syracuseStep 11057735 = 16586603) B16586603
theorem B5176811 : Blo 1362500 5176811 := bstep (se 1 (by rfl) ⟨3882608, by rfl⟩ : syracuseStep 5176811 = 7765217) B7765217
theorem B9323045 : Blo 1362500 9323045 := bstep (se 4 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 9323045 = 1748071) B1748071
theorem B33178157 : Blo 1362500 33178157 := bstep (se 3 (by rfl) ⟨6220904, by rfl⟩ : syracuseStep 33178157 = 12441809) B12441809
theorem B56001293 : Blo 1362500 56001293 := bstep (se 3 (by rfl) ⟨10500242, by rfl⟩ : syracuseStep 56001293 = 21000485) B21000485
theorem B4605065 : Blo 1362500 4605065 := bstep (se 2 (by rfl) ⟨1726899, by rfl⟩ : syracuseStep 4605065 = 3453799) B3453799
theorem B3451207 : Blo 1362500 3451207 := bstep (se 1 (by rfl) ⟨2588405, by rfl⟩ : syracuseStep 3451207 = 5176811) B5176811
theorem B15526241 : Blo 1362500 15526241 := bstep (se 2 (by rfl) ⟨5822340, by rfl⟩ : syracuseStep 15526241 = 11644681) B11644681
theorem B33172507 : Blo 1362500 33172507 := bstep (se 1 (by rfl) ⟨24879380, by rfl⟩ : syracuseStep 33172507 = 49758761) B49758761
theorem B1362975 : Blo 1362500 1362975 := bstep (se 1 (by rfl) ⟨1022231, by rfl⟩ : syracuseStep 1362975 = 2044463) B2044463
theorem B1363359 : Blo 1362500 1363359 := bstep (se 1 (by rfl) ⟨1022519, by rfl⟩ : syracuseStep 1363359 = 2045039) B2045039
theorem B2182879 : Blo 1362500 2182879 := bstep (se 1 (by rfl) ⟨1637159, by rfl⟩ : syracuseStep 2182879 = 3274319) B3274319
theorem B5902235 : Blo 1362500 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B1363871 : Blo 1362500 1363871 := bstep (se 1 (by rfl) ⟨1022903, by rfl⟩ : syracuseStep 1363871 = 2045807) B2045807
theorem B8400935 : Blo 1362500 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B1364287 : Blo 1362500 1364287 := bstep (se 1 (by rfl) ⟨1023215, by rfl⟩ : syracuseStep 1364287 = 2046431) B2046431
theorem B16593659 : Blo 1362500 16593659 := bstep (se 1 (by rfl) ⟨12445244, by rfl⟩ : syracuseStep 16593659 = 24890489) B24890489
theorem B155513675 : Blo 1362500 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B1455295 : Blo 1362500 1455295 := bstep (se 1 (by rfl) ⟨1091471, by rfl⟩ : syracuseStep 1455295 = 2182943) B2182943
theorem B1725887 : Blo 1362500 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B2299495 : Blo 1362500 2299495 := bstep (se 1 (by rfl) ⟨1724621, by rfl⟩ : syracuseStep 2299495 = 3449243) B3449243
theorem B42563663 : Blo 1362500 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B74611691 : Blo 1362500 74611691 := bstep (se 1 (by rfl) ⟨55958768, by rfl⟩ : syracuseStep 74611691 = 111917537) B111917537
theorem B7371823 : Blo 1362500 7371823 := bstep (se 1 (by rfl) ⟨5528867, by rfl⟩ : syracuseStep 7371823 = 11057735) B11057735
theorem B22118771 : Blo 1362500 22118771 := bstep (se 1 (by rfl) ⟨16589078, by rfl⟩ : syracuseStep 22118771 = 33178157) B33178157
theorem B44230009 : Blo 1362500 44230009 := bstep (se 2 (by rfl) ⟨16586253, by rfl⟩ : syracuseStep 44230009 = 33172507) B33172507
theorem B3065993 : Blo 1362500 3065993 := bstep (se 2 (by rfl) ⟨1149747, by rfl⟩ : syracuseStep 3065993 = 2299495) B2299495
theorem B2910505 : Blo 1362500 2910505 := bstep (se 2 (by rfl) ⟨1091439, by rfl⟩ : syracuseStep 2910505 = 2182879) B2182879
theorem B3934823 : Blo 1362500 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B11062439 : Blo 1362500 11062439 := bstep (se 1 (by rfl) ⟨8296829, by rfl⟩ : syracuseStep 11062439 = 16593659) B16593659
theorem B37334195 : Blo 1362500 37334195 := bstep (se 1 (by rfl) ⟨28000646, by rfl⟩ : syracuseStep 37334195 = 56001293) B56001293
theorem B10350827 : Blo 1362500 10350827 := bstep (se 1 (by rfl) ⟨7763120, by rfl⟩ : syracuseStep 10350827 = 15526241) B15526241
theorem B5600623 : Blo 1362500 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B6215363 : Blo 1362500 6215363 := bstep (se 1 (by rfl) ⟨4661522, by rfl⟩ : syracuseStep 6215363 = 9323045) B9323045
theorem B4601609 : Blo 1362500 4601609 := bstep (se 2 (by rfl) ⟨1725603, by rfl⟩ : syracuseStep 4601609 = 3451207) B3451207
theorem B103675783 : Blo 1362500 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B3070043 : Blo 1362500 3070043 := bstep (se 1 (by rfl) ⟨2302532, by rfl⟩ : syracuseStep 3070043 = 4605065) B4605065
theorem B4602365 : Blo 1362500 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B28375775 : Blo 1362500 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B9829097 : Blo 1362500 9829097 := bstep (se 2 (by rfl) ⟨3685911, by rfl⟩ : syracuseStep 9829097 = 7371823) B7371823
theorem B1940393 : Blo 1362500 1940393 := bstep (se 2 (by rfl) ⟨727647, by rfl⟩ : syracuseStep 1940393 = 1455295) B1455295
theorem B49741127 : Blo 1362500 49741127 := bstep (se 1 (by rfl) ⟨37305845, by rfl⟩ : syracuseStep 49741127 = 74611691) B74611691
theorem B58983389 : Blo 1362500 58983389 := bstep (se 3 (by rfl) ⟨11059385, by rfl⟩ : syracuseStep 58983389 = 22118771) B22118771
theorem B18917183 : Blo 1362500 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B7374959 : Blo 1362500 7374959 := bstep (se 1 (by rfl) ⟨5531219, by rfl⟩ : syracuseStep 7374959 = 11062439) B11062439
theorem B24889463 : Blo 1362500 24889463 := bstep (se 1 (by rfl) ⟨18667097, by rfl⟩ : syracuseStep 24889463 = 37334195) B37334195
theorem B138234377 : Blo 1362500 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B6900551 : Blo 1362500 6900551 := bstep (se 1 (by rfl) ⟨5175413, by rfl⟩ : syracuseStep 6900551 = 10350827) B10350827
theorem B3067739 : Blo 1362500 3067739 := bstep (se 1 (by rfl) ⟨2300804, by rfl⟩ : syracuseStep 3067739 = 4601609) B4601609
theorem B2043995 : Blo 1362500 2043995 := bstep (se 1 (by rfl) ⟨1532996, by rfl⟩ : syracuseStep 2043995 = 3065993) B3065993
theorem B3068243 : Blo 1362500 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B7467497 : Blo 1362500 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B5174381 : Blo 1362500 5174381 := bstep (se 3 (by rfl) ⟨970196, by rfl⟩ : syracuseStep 5174381 = 1940393) B1940393
theorem B3880673 : Blo 1362500 3880673 := bstep (se 2 (by rfl) ⟨1455252, by rfl⟩ : syracuseStep 3880673 = 2910505) B2910505
theorem B4143575 : Blo 1362500 4143575 := bstep (se 1 (by rfl) ⟨3107681, by rfl⟩ : syracuseStep 4143575 = 6215363) B6215363
theorem B2046695 : Blo 1362500 2046695 := bstep (se 1 (by rfl) ⟨1535021, by rfl⟩ : syracuseStep 2046695 = 3070043) B3070043
theorem B10492861 : Blo 1362500 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B6552731 : Blo 1362500 6552731 := bstep (se 1 (by rfl) ⟨4914548, by rfl⟩ : syracuseStep 6552731 = 9829097) B9829097
theorem B58973345 : Blo 1362500 58973345 := bstep (se 2 (by rfl) ⟨22115004, by rfl⟩ : syracuseStep 58973345 = 44230009) B44230009
theorem B33160751 : Blo 1362500 33160751 := bstep (se 1 (by rfl) ⟨24870563, by rfl⟩ : syracuseStep 33160751 = 49741127) B49741127
theorem B39322259 : Blo 1362500 39322259 := bstep (se 1 (by rfl) ⟨29491694, by rfl⟩ : syracuseStep 39322259 = 58983389) B58983389
theorem B3449587 : Blo 1362500 3449587 := bstep (se 1 (by rfl) ⟨2587190, by rfl⟩ : syracuseStep 3449587 = 5174381) B5174381
theorem B4916639 : Blo 1362500 4916639 := bstep (se 1 (by rfl) ⟨3687479, by rfl⟩ : syracuseStep 4916639 = 7374959) B7374959
theorem B2762383 : Blo 1362500 2762383 := bstep (se 1 (by rfl) ⟨2071787, by rfl⟩ : syracuseStep 2762383 = 4143575) B4143575
theorem B4368487 : Blo 1362500 4368487 := bstep (se 1 (by rfl) ⟨3276365, by rfl⟩ : syracuseStep 4368487 = 6552731) B6552731
theorem B39315563 : Blo 1362500 39315563 := bstep (se 1 (by rfl) ⟨29486672, by rfl⟩ : syracuseStep 39315563 = 58973345) B58973345
theorem B1362663 : Blo 1362500 1362663 := bstep (se 1 (by rfl) ⟨1021997, by rfl⟩ : syracuseStep 1362663 = 2043995) B2043995
theorem B16592975 : Blo 1362500 16592975 := bstep (se 1 (by rfl) ⟨12444731, by rfl⟩ : syracuseStep 16592975 = 24889463) B24889463
theorem B92156251 : Blo 1362500 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B1364463 : Blo 1362500 1364463 := bstep (se 1 (by rfl) ⟨1023347, by rfl⟩ : syracuseStep 1364463 = 2046695) B2046695
theorem B4600367 : Blo 1362500 4600367 := bstep (se 1 (by rfl) ⟨3450275, by rfl⟩ : syracuseStep 4600367 = 6900551) B6900551
theorem B22107167 : Blo 1362500 22107167 := bstep (se 1 (by rfl) ⟨16580375, by rfl⟩ : syracuseStep 22107167 = 33160751) B33160751
theorem B2045159 : Blo 1362500 2045159 := bstep (se 1 (by rfl) ⟨1533869, by rfl⟩ : syracuseStep 2045159 = 3067739) B3067739
theorem B2045495 : Blo 1362500 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B4978331 : Blo 1362500 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B2587115 : Blo 1362500 2587115 := bstep (se 1 (by rfl) ⟨1940336, by rfl⟩ : syracuseStep 2587115 = 3880673) B3880673
theorem B13990481 : Blo 1362500 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B50445821 : Blo 1362500 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B5824649 : Blo 1362500 5824649 := bstep (se 2 (by rfl) ⟨2184243, by rfl⟩ : syracuseStep 5824649 = 4368487) B4368487
theorem B26214839 : Blo 1362500 26214839 := bstep (se 1 (by rfl) ⟨19661129, by rfl⟩ : syracuseStep 26214839 = 39322259) B39322259
theorem B14738111 : Blo 1362500 14738111 := bstep (se 1 (by rfl) ⟨11053583, by rfl⟩ : syracuseStep 14738111 = 22107167) B22107167
theorem B3277759 : Blo 1362500 3277759 := bstep (se 1 (by rfl) ⟨2458319, by rfl⟩ : syracuseStep 3277759 = 4916639) B4916639
theorem B3318887 : Blo 1362500 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B33630547 : Blo 1362500 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B11061983 : Blo 1362500 11061983 := bstep (se 1 (by rfl) ⟨8296487, by rfl⟩ : syracuseStep 11061983 = 16592975) B16592975
theorem B3066911 : Blo 1362500 3066911 := bstep (se 1 (by rfl) ⟨2300183, by rfl⟩ : syracuseStep 3066911 = 4600367) B4600367
theorem B122875001 : Blo 1362500 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B1363439 : Blo 1362500 1363439 := bstep (se 1 (by rfl) ⟨1022579, by rfl⟩ : syracuseStep 1363439 = 2045159) B2045159
theorem B4599449 : Blo 1362500 4599449 := bstep (se 2 (by rfl) ⟨1724793, by rfl⟩ : syracuseStep 4599449 = 3449587) B3449587
theorem B1363663 : Blo 1362500 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B26210375 : Blo 1362500 26210375 := bstep (se 1 (by rfl) ⟨19657781, by rfl⟩ : syracuseStep 26210375 = 39315563) B39315563
theorem B1724743 : Blo 1362500 1724743 := bstep (se 1 (by rfl) ⟨1293557, by rfl⟩ : syracuseStep 1724743 = 2587115) B2587115
theorem B9326987 : Blo 1362500 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B3683177 : Blo 1362500 3683177 := bstep (se 2 (by rfl) ⟨1381191, by rfl⟩ : syracuseStep 3683177 = 2762383) B2762383
theorem B17473583 : Blo 1362500 17473583 := bstep (se 1 (by rfl) ⟨13105187, by rfl⟩ : syracuseStep 17473583 = 26210375) B26210375
theorem B3883099 : Blo 1362500 3883099 := bstep (se 1 (by rfl) ⟨2912324, by rfl⟩ : syracuseStep 3883099 = 5824649) B5824649
theorem B6217991 : Blo 1362500 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B2212591 : Blo 1362500 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B7374655 : Blo 1362500 7374655 := bstep (se 1 (by rfl) ⟨5530991, by rfl⟩ : syracuseStep 7374655 = 11061983) B11061983
theorem B3066299 : Blo 1362500 3066299 := bstep (se 1 (by rfl) ⟨2299724, by rfl⟩ : syracuseStep 3066299 = 4599449) B4599449
theorem B17476559 : Blo 1362500 17476559 := bstep (se 1 (by rfl) ⟨13107419, by rfl⟩ : syracuseStep 17476559 = 26214839) B26214839
theorem B9825407 : Blo 1362500 9825407 := bstep (se 1 (by rfl) ⟨7369055, by rfl⟩ : syracuseStep 9825407 = 14738111) B14738111
theorem B4370345 : Blo 1362500 4370345 := bstep (se 2 (by rfl) ⟨1638879, by rfl⟩ : syracuseStep 4370345 = 3277759) B3277759
theorem B2044607 : Blo 1362500 2044607 := bstep (se 1 (by rfl) ⟨1533455, by rfl⟩ : syracuseStep 2044607 = 3066911) B3066911
theorem B81916667 : Blo 1362500 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B2299657 : Blo 1362500 2299657 := bstep (se 2 (by rfl) ⟨862371, by rfl⟩ : syracuseStep 2299657 = 1724743) B1724743
theorem B44840729 : Blo 1362500 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B2455451 : Blo 1362500 2455451 := bstep (se 1 (by rfl) ⟨1841588, by rfl⟩ : syracuseStep 2455451 = 3683177) B3683177
theorem B11649055 : Blo 1362500 11649055 := bstep (se 1 (by rfl) ⟨8736791, by rfl⟩ : syracuseStep 11649055 = 17473583) B17473583
theorem B5177465 : Blo 1362500 5177465 := bstep (se 2 (by rfl) ⟨1941549, by rfl⟩ : syracuseStep 5177465 = 3883099) B3883099
theorem B4145327 : Blo 1362500 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B2950121 : Blo 1362500 2950121 := bstep (se 2 (by rfl) ⟨1106295, by rfl⟩ : syracuseStep 2950121 = 2212591) B2212591
theorem B29893819 : Blo 1362500 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B11651039 : Blo 1362500 11651039 := bstep (se 1 (by rfl) ⟨8738279, by rfl⟩ : syracuseStep 11651039 = 17476559) B17476559
theorem B3066209 : Blo 1362500 3066209 := bstep (se 2 (by rfl) ⟨1149828, by rfl⟩ : syracuseStep 3066209 = 2299657) B2299657
theorem B9832873 : Blo 1362500 9832873 := bstep (se 2 (by rfl) ⟨3687327, by rfl⟩ : syracuseStep 9832873 = 7374655) B7374655
theorem B1363071 : Blo 1362500 1363071 := bstep (se 1 (by rfl) ⟨1022303, by rfl⟩ : syracuseStep 1363071 = 2044607) B2044607
theorem B54611111 : Blo 1362500 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B2044199 : Blo 1362500 2044199 := bstep (se 1 (by rfl) ⟨1533149, by rfl⟩ : syracuseStep 2044199 = 3066299) B3066299
theorem B6550271 : Blo 1362500 6550271 := bstep (se 1 (by rfl) ⟨4912703, by rfl⟩ : syracuseStep 6550271 = 9825407) B9825407
theorem B2913563 : Blo 1362500 2913563 := bstep (se 1 (by rfl) ⟨2185172, by rfl⟩ : syracuseStep 2913563 = 4370345) B4370345
theorem B1636967 : Blo 1362500 1636967 := bstep (se 1 (by rfl) ⟨1227725, by rfl⟩ : syracuseStep 1636967 = 2455451) B2455451
theorem B15532073 : Blo 1362500 15532073 := bstep (se 2 (by rfl) ⟨5824527, by rfl⟩ : syracuseStep 15532073 = 11649055) B11649055
theorem B4366847 : Blo 1362500 4366847 := bstep (se 1 (by rfl) ⟨3275135, by rfl⟩ : syracuseStep 4366847 = 6550271) B6550271
theorem B1942375 : Blo 1362500 1942375 := bstep (se 1 (by rfl) ⟨1456781, by rfl⟩ : syracuseStep 1942375 = 2913563) B2913563
theorem B7767359 : Blo 1362500 7767359 := bstep (se 1 (by rfl) ⟨5825519, by rfl⟩ : syracuseStep 7767359 = 11651039) B11651039
theorem B36407407 : Blo 1362500 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B7866989 : Blo 1362500 7866989 := bstep (se 3 (by rfl) ⟨1475060, by rfl⟩ : syracuseStep 7866989 = 2950121) B2950121
theorem B3451643 : Blo 1362500 3451643 := bstep (se 1 (by rfl) ⟨2588732, by rfl⟩ : syracuseStep 3451643 = 5177465) B5177465
theorem B2763551 : Blo 1362500 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B1362799 : Blo 1362500 1362799 := bstep (se 1 (by rfl) ⟨1022099, by rfl⟩ : syracuseStep 1362799 = 2044199) B2044199
theorem B13110497 : Blo 1362500 13110497 := bstep (se 2 (by rfl) ⟨4916436, by rfl⟩ : syracuseStep 13110497 = 9832873) B9832873
theorem B2044139 : Blo 1362500 2044139 := bstep (se 1 (by rfl) ⟨1533104, by rfl⟩ : syracuseStep 2044139 = 3066209) B3066209
theorem B39858425 : Blo 1362500 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B4365245 : Blo 1362500 4365245 := bstep (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) B1636967
theorem B10354715 : Blo 1362500 10354715 := bstep (se 1 (by rfl) ⟨7766036, by rfl⟩ : syracuseStep 10354715 = 15532073) B15532073
theorem B5178239 : Blo 1362500 5178239 := bstep (se 1 (by rfl) ⟨3883679, by rfl⟩ : syracuseStep 5178239 = 7767359) B7767359
theorem B2589833 : Blo 1362500 2589833 := bstep (se 2 (by rfl) ⟨971187, by rfl⟩ : syracuseStep 2589833 = 1942375) B1942375
theorem B5244659 : Blo 1362500 5244659 := bstep (se 1 (by rfl) ⟨3933494, by rfl⟩ : syracuseStep 5244659 = 7866989) B7866989
theorem B2910163 : Blo 1362500 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B1362759 : Blo 1362500 1362759 := bstep (se 1 (by rfl) ⟨1022069, by rfl⟩ : syracuseStep 1362759 = 2044139) B2044139
theorem B2911231 : Blo 1362500 2911231 := bstep (se 1 (by rfl) ⟨2183423, by rfl⟩ : syracuseStep 2911231 = 4366847) B4366847
theorem B48543209 : Blo 1362500 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B26572283 : Blo 1362500 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B2301095 : Blo 1362500 2301095 := bstep (se 1 (by rfl) ⟨1725821, by rfl⟩ : syracuseStep 2301095 = 3451643) B3451643
theorem B1842367 : Blo 1362500 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B8740331 : Blo 1362500 8740331 := bstep (se 1 (by rfl) ⟨6555248, by rfl⟩ : syracuseStep 8740331 = 13110497) B13110497
theorem B6906221 : Blo 1362500 6906221 := bstep (se 3 (by rfl) ⟨1294916, by rfl⟩ : syracuseStep 6906221 = 2589833) B2589833
theorem B1534063 : Blo 1362500 1534063 := bstep (se 1 (by rfl) ⟨1150547, by rfl⟩ : syracuseStep 1534063 = 2301095) B2301095
theorem B5826887 : Blo 1362500 5826887 := bstep (se 1 (by rfl) ⟨4370165, by rfl⟩ : syracuseStep 5826887 = 8740331) B8740331
theorem B3452159 : Blo 1362500 3452159 := bstep (se 1 (by rfl) ⟨2589119, by rfl⟩ : syracuseStep 3452159 = 5178239) B5178239
theorem B32362139 : Blo 1362500 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B17714855 : Blo 1362500 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B3880217 : Blo 1362500 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B6903143 : Blo 1362500 6903143 := bstep (se 1 (by rfl) ⟨5177357, by rfl⟩ : syracuseStep 6903143 = 10354715) B10354715
theorem B3496439 : Blo 1362500 3496439 := bstep (se 1 (by rfl) ⟨2622329, by rfl⟩ : syracuseStep 3496439 = 5244659) B5244659
theorem B3881641 : Blo 1362500 3881641 := bstep (se 2 (by rfl) ⟨1455615, by rfl⟩ : syracuseStep 3881641 = 2911231) B2911231
theorem B2456489 : Blo 1362500 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B4604147 : Blo 1362500 4604147 := bstep (se 1 (by rfl) ⟨3453110, by rfl⟩ : syracuseStep 4604147 = 6906221) B6906221
theorem B3884591 : Blo 1362500 3884591 := bstep (se 1 (by rfl) ⟨2913443, by rfl⟩ : syracuseStep 3884591 = 5826887) B5826887
theorem B2330959 : Blo 1362500 2330959 := bstep (se 1 (by rfl) ⟨1748219, by rfl⟩ : syracuseStep 2330959 = 3496439) B3496439
theorem B21574759 : Blo 1362500 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B11809903 : Blo 1362500 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B2045417 : Blo 1362500 2045417 := bstep (se 2 (by rfl) ⟨767031, by rfl⟩ : syracuseStep 2045417 = 1534063) B1534063
theorem B2586811 : Blo 1362500 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B5175521 : Blo 1362500 5175521 := bstep (se 2 (by rfl) ⟨1940820, by rfl⟩ : syracuseStep 5175521 = 3881641) B3881641
theorem B4602095 : Blo 1362500 4602095 := bstep (se 1 (by rfl) ⟨3451571, by rfl⟩ : syracuseStep 4602095 = 6903143) B6903143
theorem B1637659 : Blo 1362500 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B2301439 : Blo 1362500 2301439 := bstep (se 1 (by rfl) ⟨1726079, by rfl⟩ : syracuseStep 2301439 = 3452159) B3452159
theorem B3449081 : Blo 1362500 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B2589727 : Blo 1362500 2589727 := bstep (se 1 (by rfl) ⟨1942295, by rfl⟩ : syracuseStep 2589727 = 3884591) B3884591
theorem B15746537 : Blo 1362500 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B3450347 : Blo 1362500 3450347 := bstep (se 1 (by rfl) ⟨2587760, by rfl⟩ : syracuseStep 3450347 = 5175521) B5175521
theorem B3107945 : Blo 1362500 3107945 := bstep (se 2 (by rfl) ⟨1165479, by rfl⟩ : syracuseStep 3107945 = 2330959) B2330959
theorem B1363611 : Blo 1362500 1363611 := bstep (se 1 (by rfl) ⟨1022708, by rfl⟩ : syracuseStep 1363611 = 2045417) B2045417
theorem B28766345 : Blo 1362500 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B3068063 : Blo 1362500 3068063 := bstep (se 1 (by rfl) ⟨2301047, by rfl⟩ : syracuseStep 3068063 = 4602095) B4602095
theorem B2183545 : Blo 1362500 2183545 := bstep (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) B1637659
theorem B3068585 : Blo 1362500 3068585 := bstep (se 2 (by rfl) ⟨1150719, by rfl⟩ : syracuseStep 3068585 = 2301439) B2301439
theorem B3069431 : Blo 1362500 3069431 := bstep (se 1 (by rfl) ⟨2302073, by rfl⟩ : syracuseStep 3069431 = 4604147) B4604147
theorem B76710253 : Blo 1362500 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B2911393 : Blo 1362500 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B10497691 : Blo 1362500 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B3452969 : Blo 1362500 3452969 := bstep (se 2 (by rfl) ⟨1294863, by rfl⟩ : syracuseStep 3452969 = 2589727) B2589727
theorem B2045375 : Blo 1362500 2045375 := bstep (se 1 (by rfl) ⟨1534031, by rfl⟩ : syracuseStep 2045375 = 3068063) B3068063
theorem B2299387 : Blo 1362500 2299387 := bstep (se 1 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 2299387 = 3449081) B3449081
theorem B2045723 : Blo 1362500 2045723 := bstep (se 1 (by rfl) ⟨1534292, by rfl⟩ : syracuseStep 2045723 = 3068585) B3068585
theorem B2300231 : Blo 1362500 2300231 := bstep (se 1 (by rfl) ⟨1725173, by rfl⟩ : syracuseStep 2300231 = 3450347) B3450347
theorem B2046287 : Blo 1362500 2046287 := bstep (se 1 (by rfl) ⟨1534715, by rfl⟩ : syracuseStep 2046287 = 3069431) B3069431
theorem B2071963 : Blo 1362500 2071963 := bstep (se 1 (by rfl) ⟨1553972, by rfl⟩ : syracuseStep 2071963 = 3107945) B3107945
theorem B2301979 : Blo 1362500 2301979 := bstep (se 1 (by rfl) ⟨1726484, by rfl⟩ : syracuseStep 2301979 = 3452969) B3452969
theorem B1533487 : Blo 1362500 1533487 := bstep (se 1 (by rfl) ⟨1150115, by rfl⟩ : syracuseStep 1533487 = 2300231) B2300231
theorem B2762617 : Blo 1362500 2762617 := bstep (se 2 (by rfl) ⟨1035981, by rfl⟩ : syracuseStep 2762617 = 2071963) B2071963
theorem B3065849 : Blo 1362500 3065849 := bstep (se 2 (by rfl) ⟨1149693, by rfl⟩ : syracuseStep 3065849 = 2299387) B2299387
theorem B102280337 : Blo 1362500 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B1363583 : Blo 1362500 1363583 := bstep (se 1 (by rfl) ⟨1022687, by rfl⟩ : syracuseStep 1363583 = 2045375) B2045375
theorem B1363815 : Blo 1362500 1363815 := bstep (se 1 (by rfl) ⟨1022861, by rfl⟩ : syracuseStep 1363815 = 2045723) B2045723
theorem B1364191 : Blo 1362500 1364191 := bstep (se 1 (by rfl) ⟨1023143, by rfl⟩ : syracuseStep 1364191 = 2046287) B2046287
theorem B13996921 : Blo 1362500 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B3881857 : Blo 1362500 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B18662561 : Blo 1362500 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B2043899 : Blo 1362500 2043899 := bstep (se 1 (by rfl) ⟨1532924, by rfl⟩ : syracuseStep 2043899 = 3065849) B3065849
theorem B2044649 : Blo 1362500 2044649 := bstep (se 2 (by rfl) ⟨766743, by rfl⟩ : syracuseStep 2044649 = 1533487) B1533487
theorem B68186891 : Blo 1362500 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B3683489 : Blo 1362500 3683489 := bstep (se 2 (by rfl) ⟨1381308, by rfl⟩ : syracuseStep 3683489 = 2762617) B2762617
theorem B3069305 : Blo 1362500 3069305 := bstep (se 2 (by rfl) ⟨1150989, by rfl⟩ : syracuseStep 3069305 = 2301979) B2301979
theorem B5175809 : Blo 1362500 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B9822637 : Blo 1362500 9822637 := bstep (se 3 (by rfl) ⟨1841744, by rfl⟩ : syracuseStep 9822637 = 3683489) B3683489
theorem B3450539 : Blo 1362500 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B181831709 : Blo 1362500 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B1362599 : Blo 1362500 1362599 := bstep (se 1 (by rfl) ⟨1021949, by rfl⟩ : syracuseStep 1362599 = 2043899) B2043899
theorem B1363099 : Blo 1362500 1363099 := bstep (se 1 (by rfl) ⟨1022324, by rfl⟩ : syracuseStep 1363099 = 2044649) B2044649
theorem B12441707 : Blo 1362500 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B2046203 : Blo 1362500 2046203 := bstep (se 1 (by rfl) ⟨1534652, by rfl⟩ : syracuseStep 2046203 = 3069305) B3069305
theorem B121221139 : Blo 1362500 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B8294471 : Blo 1362500 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B1364135 : Blo 1362500 1364135 := bstep (se 1 (by rfl) ⟨1023101, by rfl⟩ : syracuseStep 1364135 = 2046203) B2046203
theorem B13096849 : Blo 1362500 13096849 := bstep (se 2 (by rfl) ⟨4911318, by rfl⟩ : syracuseStep 13096849 = 9822637) B9822637
theorem B2300359 : Blo 1362500 2300359 := bstep (se 1 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 2300359 = 3450539) B3450539
theorem B161628185 : Blo 1362500 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B5529647 : Blo 1362500 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B3067145 : Blo 1362500 3067145 := bstep (se 2 (by rfl) ⟨1150179, by rfl⟩ : syracuseStep 3067145 = 2300359) B2300359
theorem B17462465 : Blo 1362500 17462465 := bstep (se 2 (by rfl) ⟨6548424, by rfl⟩ : syracuseStep 17462465 = 13096849) B13096849
theorem B14745725 : Blo 1362500 14745725 := bstep (se 3 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 14745725 = 5529647) B5529647
theorem B11641643 : Blo 1362500 11641643 := bstep (se 1 (by rfl) ⟨8731232, by rfl⟩ : syracuseStep 11641643 = 17462465) B17462465
theorem B107752123 : Blo 1362500 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B2044763 : Blo 1362500 2044763 := bstep (se 1 (by rfl) ⟨1533572, by rfl⟩ : syracuseStep 2044763 = 3067145) B3067145
theorem B9830483 : Blo 1362500 9830483 := bstep (se 1 (by rfl) ⟨7372862, by rfl⟩ : syracuseStep 9830483 = 14745725) B14745725
theorem B7761095 : Blo 1362500 7761095 := bstep (se 1 (by rfl) ⟨5820821, by rfl⟩ : syracuseStep 7761095 = 11641643) B11641643
theorem B1363175 : Blo 1362500 1363175 := bstep (se 1 (by rfl) ⟨1022381, by rfl⟩ : syracuseStep 1363175 = 2044763) B2044763
theorem B143669497 : Blo 1362500 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B6553655 : Blo 1362500 6553655 := bstep (se 1 (by rfl) ⟨4915241, by rfl⟩ : syracuseStep 6553655 = 9830483) B9830483
theorem B5174063 : Blo 1362500 5174063 := bstep (se 1 (by rfl) ⟨3880547, by rfl⟩ : syracuseStep 5174063 = 7761095) B7761095
theorem B191559329 : Blo 1362500 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B3449375 : Blo 1362500 3449375 := bstep (se 1 (by rfl) ⟨2587031, by rfl⟩ : syracuseStep 3449375 = 5174063) B5174063
theorem B127706219 : Blo 1362500 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B4369103 : Blo 1362500 4369103 := bstep (se 1 (by rfl) ⟨3276827, by rfl⟩ : syracuseStep 4369103 = 6553655) B6553655
theorem B2912735 : Blo 1362500 2912735 := bstep (se 1 (by rfl) ⟨2184551, by rfl⟩ : syracuseStep 2912735 = 4369103) B4369103
theorem B2299583 : Blo 1362500 2299583 := bstep (se 1 (by rfl) ⟨1724687, by rfl⟩ : syracuseStep 2299583 = 3449375) B3449375
theorem B85137479 : Blo 1362500 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B1941823 : Blo 1362500 1941823 := bstep (se 1 (by rfl) ⟨1456367, by rfl⟩ : syracuseStep 1941823 = 2912735) B2912735
theorem B1533055 : Blo 1362500 1533055 := bstep (se 1 (by rfl) ⟨1149791, by rfl⟩ : syracuseStep 1533055 = 2299583) B2299583
theorem B56758319 : Blo 1362500 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B37838879 : Blo 1362500 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B2589097 : Blo 1362500 2589097 := bstep (se 2 (by rfl) ⟨970911, by rfl⟩ : syracuseStep 2589097 = 1941823) B1941823
theorem B2044073 : Blo 1362500 2044073 := bstep (se 2 (by rfl) ⟨766527, by rfl⟩ : syracuseStep 2044073 = 1533055) B1533055
theorem B25225919 : Blo 1362500 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B1362715 : Blo 1362500 1362715 := bstep (se 1 (by rfl) ⟨1022036, by rfl⟩ : syracuseStep 1362715 = 2044073) B2044073
theorem B3452129 : Blo 1362500 3452129 := bstep (se 2 (by rfl) ⟨1294548, by rfl⟩ : syracuseStep 3452129 = 2589097) B2589097
theorem B16817279 : Blo 1362500 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B2301419 : Blo 1362500 2301419 := bstep (se 1 (by rfl) ⟨1726064, by rfl⟩ : syracuseStep 2301419 = 3452129) B3452129
theorem B1534279 : Blo 1362500 1534279 := bstep (se 1 (by rfl) ⟨1150709, by rfl⟩ : syracuseStep 1534279 = 2301419) B2301419
theorem B44846077 : Blo 1362500 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 1362500 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B2045705 : Blo 1362500 2045705 := bstep (se 2 (by rfl) ⟨767139, by rfl⟩ : syracuseStep 2045705 = 1534279) B1534279
theorem B39863179 : Blo 1362500 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B1363803 : Blo 1362500 1363803 := bstep (se 1 (by rfl) ⟨1022852, by rfl⟩ : syracuseStep 1363803 = 2045705) B2045705
theorem B53150905 : Blo 1362500 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B70867873 : Blo 1362500 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 1362500 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 1362500 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 1362500 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 1362500 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 1362500 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 1362500 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 1362500 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 1362500 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B117979901 : Blo 1362500 117979901 := bstep (se 3 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 117979901 = 44242463) B44242463
theorem B78653267 : Blo 1362500 78653267 := bstep (se 1 (by rfl) ⟨58989950, by rfl⟩ : syracuseStep 78653267 = 117979901) B117979901
theorem B52435511 : Blo 1362500 52435511 := bstep (se 1 (by rfl) ⟨39326633, by rfl⟩ : syracuseStep 52435511 = 78653267) B78653267
theorem B34957007 : Blo 1362500 34957007 := bstep (se 1 (by rfl) ⟨26217755, by rfl⟩ : syracuseStep 34957007 = 52435511) B52435511
theorem B23304671 : Blo 1362500 23304671 := bstep (se 1 (by rfl) ⟨17478503, by rfl⟩ : syracuseStep 23304671 = 34957007) B34957007
theorem B15536447 : Blo 1362500 15536447 := bstep (se 1 (by rfl) ⟨11652335, by rfl⟩ : syracuseStep 15536447 = 23304671) B23304671
theorem B10357631 : Blo 1362500 10357631 := bstep (se 1 (by rfl) ⟨7768223, by rfl⟩ : syracuseStep 10357631 = 15536447) B15536447
theorem B6905087 : Blo 1362500 6905087 := bstep (se 1 (by rfl) ⟨5178815, by rfl⟩ : syracuseStep 6905087 = 10357631) B10357631
theorem B4603391 : Blo 1362500 4603391 := bstep (se 1 (by rfl) ⟨3452543, by rfl⟩ : syracuseStep 4603391 = 6905087) B6905087
theorem B3068927 : Blo 1362500 3068927 := bstep (se 1 (by rfl) ⟨2301695, by rfl⟩ : syracuseStep 3068927 = 4603391) B4603391
theorem B2045951 : Blo 1362500 2045951 := bstep (se 1 (by rfl) ⟨1534463, by rfl⟩ : syracuseStep 2045951 = 3068927) B3068927
theorem B1363967 : Blo 1362500 1363967 := bstep (se 1 (by rfl) ⟨1022975, by rfl⟩ : syracuseStep 1363967 = 2045951) B2045951

theorem C0 (j : ℕ) (h1 : 340625 ≤ j) (h2 : j ≤ 341124) : Blo 1362500 (4 * j + 3) := by
  interval_cases j
  · exact B1362503
  · exact B1362507
  · exact B1362511
  · exact B1362515
  · exact B1362519
  · exact B1362523
  · exact B1362527
  · exact B1362531
  · exact B1362535
  · exact B1362539
  · exact B1362543
  · exact B1362547
  · exact B1362551
  · exact B1362555
  · exact B1362559
  · exact B1362563
  · exact B1362567
  · exact B1362571
  · exact B1362575
  · exact B1362579
  · exact B1362583
  · exact B1362587
  · exact B1362591
  · exact B1362595
  · exact B1362599
  · exact B1362603
  · exact B1362607
  · exact B1362611
  · exact B1362615
  · exact B1362619
  · exact B1362623
  · exact B1362627
  · exact B1362631
  · exact B1362635
  · exact B1362639
  · exact B1362643
  · exact B1362647
  · exact B1362651
  · exact B1362655
  · exact B1362659
  · exact B1362663
  · exact B1362667
  · exact B1362671
  · exact B1362675
  · exact B1362679
  · exact B1362683
  · exact B1362687
  · exact B1362691
  · exact B1362695
  · exact B1362699
  · exact B1362703
  · exact B1362707
  · exact B1362711
  · exact B1362715
  · exact B1362719
  · exact B1362723
  · exact B1362727
  · exact B1362731
  · exact B1362735
  · exact B1362739
  · exact B1362743
  · exact B1362747
  · exact B1362751
  · exact B1362755
  · exact B1362759
  · exact B1362763
  · exact B1362767
  · exact B1362771
  · exact B1362775
  · exact B1362779
  · exact B1362783
  · exact B1362787
  · exact B1362791
  · exact B1362795
  · exact B1362799
  · exact B1362803
  · exact B1362807
  · exact B1362811
  · exact B1362815
  · exact B1362819
  · exact B1362823
  · exact B1362827
  · exact B1362831
  · exact B1362835
  · exact B1362839
  · exact B1362843
  · exact B1362847
  · exact B1362851
  · exact B1362855
  · exact B1362859
  · exact B1362863
  · exact B1362867
  · exact B1362871
  · exact B1362875
  · exact B1362879
  · exact B1362883
  · exact B1362887
  · exact B1362891
  · exact B1362895
  · exact B1362899
  · exact B1362903
  · exact B1362907
  · exact B1362911
  · exact B1362915
  · exact B1362919
  · exact B1362923
  · exact B1362927
  · exact B1362931
  · exact B1362935
  · exact B1362939
  · exact B1362943
  · exact B1362947
  · exact B1362951
  · exact B1362955
  · exact B1362959
  · exact B1362963
  · exact B1362967
  · exact B1362971
  · exact B1362975
  · exact B1362979
  · exact B1362983
  · exact B1362987
  · exact B1362991
  · exact B1362995
  · exact B1362999
  · exact B1363003
  · exact B1363007
  · exact B1363011
  · exact B1363015
  · exact B1363019
  · exact B1363023
  · exact B1363027
  · exact B1363031
  · exact B1363035
  · exact B1363039
  · exact B1363043
  · exact B1363047
  · exact B1363051
  · exact B1363055
  · exact B1363059
  · exact B1363063
  · exact B1363067
  · exact B1363071
  · exact B1363075
  · exact B1363079
  · exact B1363083
  · exact B1363087
  · exact B1363091
  · exact B1363095
  · exact B1363099
  · exact B1363103
  · exact B1363107
  · exact B1363111
  · exact B1363115
  · exact B1363119
  · exact B1363123
  · exact B1363127
  · exact B1363131
  · exact B1363135
  · exact B1363139
  · exact B1363143
  · exact B1363147
  · exact B1363151
  · exact B1363155
  · exact B1363159
  · exact B1363163
  · exact B1363167
  · exact B1363171
  · exact B1363175
  · exact B1363179
  · exact B1363183
  · exact B1363187
  · exact B1363191
  · exact B1363195
  · exact B1363199
  · exact B1363203
  · exact B1363207
  · exact B1363211
  · exact B1363215
  · exact B1363219
  · exact B1363223
  · exact B1363227
  · exact B1363231
  · exact B1363235
  · exact B1363239
  · exact B1363243
  · exact B1363247
  · exact B1363251
  · exact B1363255
  · exact B1363259
  · exact B1363263
  · exact B1363267
  · exact B1363271
  · exact B1363275
  · exact B1363279
  · exact B1363283
  · exact B1363287
  · exact B1363291
  · exact B1363295
  · exact B1363299
  · exact B1363303
  · exact B1363307
  · exact B1363311
  · exact B1363315
  · exact B1363319
  · exact B1363323
  · exact B1363327
  · exact B1363331
  · exact B1363335
  · exact B1363339
  · exact B1363343
  · exact B1363347
  · exact B1363351
  · exact B1363355
  · exact B1363359
  · exact B1363363
  · exact B1363367
  · exact B1363371
  · exact B1363375
  · exact B1363379
  · exact B1363383
  · exact B1363387
  · exact B1363391
  · exact B1363395
  · exact B1363399
  · exact B1363403
  · exact B1363407
  · exact B1363411
  · exact B1363415
  · exact B1363419
  · exact B1363423
  · exact B1363427
  · exact B1363431
  · exact B1363435
  · exact B1363439
  · exact B1363443
  · exact B1363447
  · exact B1363451
  · exact B1363455
  · exact B1363459
  · exact B1363463
  · exact B1363467
  · exact B1363471
  · exact B1363475
  · exact B1363479
  · exact B1363483
  · exact B1363487
  · exact B1363491
  · exact B1363495
  · exact B1363499
  · exact B1363503
  · exact B1363507
  · exact B1363511
  · exact B1363515
  · exact B1363519
  · exact B1363523
  · exact B1363527
  · exact B1363531
  · exact B1363535
  · exact B1363539
  · exact B1363543
  · exact B1363547
  · exact B1363551
  · exact B1363555
  · exact B1363559
  · exact B1363563
  · exact B1363567
  · exact B1363571
  · exact B1363575
  · exact B1363579
  · exact B1363583
  · exact B1363587
  · exact B1363591
  · exact B1363595
  · exact B1363599
  · exact B1363603
  · exact B1363607
  · exact B1363611
  · exact B1363615
  · exact B1363619
  · exact B1363623
  · exact B1363627
  · exact B1363631
  · exact B1363635
  · exact B1363639
  · exact B1363643
  · exact B1363647
  · exact B1363651
  · exact B1363655
  · exact B1363659
  · exact B1363663
  · exact B1363667
  · exact B1363671
  · exact B1363675
  · exact B1363679
  · exact B1363683
  · exact B1363687
  · exact B1363691
  · exact B1363695
  · exact B1363699
  · exact B1363703
  · exact B1363707
  · exact B1363711
  · exact B1363715
  · exact B1363719
  · exact B1363723
  · exact B1363727
  · exact B1363731
  · exact B1363735
  · exact B1363739
  · exact B1363743
  · exact B1363747
  · exact B1363751
  · exact B1363755
  · exact B1363759
  · exact B1363763
  · exact B1363767
  · exact B1363771
  · exact B1363775
  · exact B1363779
  · exact B1363783
  · exact B1363787
  · exact B1363791
  · exact B1363795
  · exact B1363799
  · exact B1363803
  · exact B1363807
  · exact B1363811
  · exact B1363815
  · exact B1363819
  · exact B1363823
  · exact B1363827
  · exact B1363831
  · exact B1363835
  · exact B1363839
  · exact B1363843
  · exact B1363847
  · exact B1363851
  · exact B1363855
  · exact B1363859
  · exact B1363863
  · exact B1363867
  · exact B1363871
  · exact B1363875
  · exact B1363879
  · exact B1363883
  · exact B1363887
  · exact B1363891
  · exact B1363895
  · exact B1363899
  · exact B1363903
  · exact B1363907
  · exact B1363911
  · exact B1363915
  · exact B1363919
  · exact B1363923
  · exact B1363927
  · exact B1363931
  · exact B1363935
  · exact B1363939
  · exact B1363943
  · exact B1363947
  · exact B1363951
  · exact B1363955
  · exact B1363959
  · exact B1363963
  · exact B1363967
  · exact B1363971
  · exact B1363975
  · exact B1363979
  · exact B1363983
  · exact B1363987
  · exact B1363991
  · exact B1363995
  · exact B1363999
  · exact B1364003
  · exact B1364007
  · exact B1364011
  · exact B1364015
  · exact B1364019
  · exact B1364023
  · exact B1364027
  · exact B1364031
  · exact B1364035
  · exact B1364039
  · exact B1364043
  · exact B1364047
  · exact B1364051
  · exact B1364055
  · exact B1364059
  · exact B1364063
  · exact B1364067
  · exact B1364071
  · exact B1364075
  · exact B1364079
  · exact B1364083
  · exact B1364087
  · exact B1364091
  · exact B1364095
  · exact B1364099
  · exact B1364103
  · exact B1364107
  · exact B1364111
  · exact B1364115
  · exact B1364119
  · exact B1364123
  · exact B1364127
  · exact B1364131
  · exact B1364135
  · exact B1364139
  · exact B1364143
  · exact B1364147
  · exact B1364151
  · exact B1364155
  · exact B1364159
  · exact B1364163
  · exact B1364167
  · exact B1364171
  · exact B1364175
  · exact B1364179
  · exact B1364183
  · exact B1364187
  · exact B1364191
  · exact B1364195
  · exact B1364199
  · exact B1364203
  · exact B1364207
  · exact B1364211
  · exact B1364215
  · exact B1364219
  · exact B1364223
  · exact B1364227
  · exact B1364231
  · exact B1364235
  · exact B1364239
  · exact B1364243
  · exact B1364247
  · exact B1364251
  · exact B1364255
  · exact B1364259
  · exact B1364263
  · exact B1364267
  · exact B1364271
  · exact B1364275
  · exact B1364279
  · exact B1364283
  · exact B1364287
  · exact B1364291
  · exact B1364295
  · exact B1364299
  · exact B1364303
  · exact B1364307
  · exact B1364311
  · exact B1364315
  · exact B1364319
  · exact B1364323
  · exact B1364327
  · exact B1364331
  · exact B1364335
  · exact B1364339
  · exact B1364343
  · exact B1364347
  · exact B1364351
  · exact B1364355
  · exact B1364359
  · exact B1364363
  · exact B1364367
  · exact B1364371
  · exact B1364375
  · exact B1364379
  · exact B1364383
  · exact B1364387
  · exact B1364391
  · exact B1364395
  · exact B1364399
  · exact B1364403
  · exact B1364407
  · exact B1364411
  · exact B1364415
  · exact B1364419
  · exact B1364423
  · exact B1364427
  · exact B1364431
  · exact B1364435
  · exact B1364439
  · exact B1364443
  · exact B1364447
  · exact B1364451
  · exact B1364455
  · exact B1364459
  · exact B1364463
  · exact B1364467
  · exact B1364471
  · exact B1364475
  · exact B1364479
  · exact B1364483
  · exact B1364487
  · exact B1364491
  · exact B1364495
  · exact B1364499

theorem solution (m : ℕ) (hlo : 1362500 ≤ m) (hhi : m ≤ 1364500) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 340625 ≤ j := by omega
    have hj2 : j ≤ 341124 := by omega
    have hb : Blo 1362500 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
