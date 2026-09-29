-- Prove2me | solution 1 for syracuse_descends_range_1168401_1170401
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:19.61652+00:00
-- url     : https://prove2.me/submissions/f168149a-4ad9-419e-a6d6-258e05adb113

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


theorem B2629637 : Blo 1168401 2629637 := bbase (se 4 (by rfl) ⟨246528, by rfl⟩ : syracuseStep 2629637 = 493057) (by norm_num)
theorem B1753109 : Blo 1168401 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B2498597 : Blo 1168401 2498597 := bbase (se 4 (by rfl) ⟨234243, by rfl⟩ : syracuseStep 2498597 = 468487) (by norm_num)
theorem B1753133 : Blo 1168401 1753133 := bbase (se 3 (by rfl) ⟨328712, by rfl⟩ : syracuseStep 1753133 = 657425) (by norm_num)
theorem B1753157 : Blo 1168401 1753157 := bbase (se 4 (by rfl) ⟨164358, by rfl⟩ : syracuseStep 1753157 = 328717) (by norm_num)
theorem B1974341 : Blo 1168401 1974341 := bbase (se 4 (by rfl) ⟨185094, by rfl⟩ : syracuseStep 1974341 = 370189) (by norm_num)
theorem B2629709 : Blo 1168401 2629709 := bbase (se 3 (by rfl) ⟨493070, by rfl⟩ : syracuseStep 2629709 = 986141) (by norm_num)
theorem B1753181 : Blo 1168401 1753181 := bbase (se 3 (by rfl) ⟨328721, by rfl⟩ : syracuseStep 1753181 = 657443) (by norm_num)
theorem B1753205 : Blo 1168401 1753205 := bbase (se 5 (by rfl) ⟨82181, by rfl⟩ : syracuseStep 1753205 = 164363) (by norm_num)
theorem B1753229 : Blo 1168401 1753229 := bbase (se 3 (by rfl) ⟨328730, by rfl⟩ : syracuseStep 1753229 = 657461) (by norm_num)
theorem B2629781 : Blo 1168401 2629781 := bbase (se 6 (by rfl) ⟨61635, by rfl⟩ : syracuseStep 2629781 = 123271) (by norm_num)
theorem B1753253 : Blo 1168401 1753253 := bbase (se 4 (by rfl) ⟨164367, by rfl⟩ : syracuseStep 1753253 = 328735) (by norm_num)
theorem B1753277 : Blo 1168401 1753277 := bbase (se 3 (by rfl) ⟨328739, by rfl⟩ : syracuseStep 1753277 = 657479) (by norm_num)
theorem B1974469 : Blo 1168401 1974469 := bbase (se 4 (by rfl) ⟨185106, by rfl⟩ : syracuseStep 1974469 = 370213) (by norm_num)
theorem B1753301 : Blo 1168401 1753301 := bbase (se 7 (by rfl) ⟨20546, by rfl⟩ : syracuseStep 1753301 = 41093) (by norm_num)
theorem B2629853 : Blo 1168401 2629853 := bbase (se 3 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 2629853 = 986195) (by norm_num)
theorem B1753325 : Blo 1168401 1753325 := bbase (se 3 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 1753325 = 657497) (by norm_num)
theorem B2957573 : Blo 1168401 2957573 := bbase (se 4 (by rfl) ⟨277272, by rfl⟩ : syracuseStep 2957573 = 554545) (by norm_num)
theorem B1753349 : Blo 1168401 1753349 := bbase (se 4 (by rfl) ⟨164376, by rfl⟩ : syracuseStep 1753349 = 328753) (by norm_num)
theorem B6086917 : Blo 1168401 6086917 := bbase (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) (by norm_num)
theorem B3997973 : Blo 1168401 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B1753373 : Blo 1168401 1753373 := bbase (se 3 (by rfl) ⟨328757, by rfl⟩ : syracuseStep 1753373 = 657515) (by norm_num)
theorem B2498845 : Blo 1168401 2498845 := bbase (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) (by norm_num)
theorem B1974557 : Blo 1168401 1974557 := bbase (se 3 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 1974557 = 740459) (by norm_num)
theorem B2629925 : Blo 1168401 2629925 := bbase (se 4 (by rfl) ⟨246555, by rfl⟩ : syracuseStep 2629925 = 493111) (by norm_num)
theorem B1581349 : Blo 1168401 1581349 := bbase (se 4 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 1581349 = 296503) (by norm_num)
theorem B1753397 : Blo 1168401 1753397 := bbase (se 5 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 1753397 = 164381) (by norm_num)
theorem B1802549 : Blo 1168401 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B2105669 : Blo 1168401 2105669 := bbase (se 4 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 2105669 = 394813) (by norm_num)
theorem B1753421 : Blo 1168401 1753421 := bbase (se 3 (by rfl) ⟨328766, by rfl⟩ : syracuseStep 1753421 = 657533) (by norm_num)
theorem B1777997 : Blo 1168401 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B3039581 : Blo 1168401 3039581 := bbase (se 3 (by rfl) ⟨569921, by rfl⟩ : syracuseStep 3039581 = 1139843) (by norm_num)
theorem B1753445 : Blo 1168401 1753445 := bbase (se 4 (by rfl) ⟨164385, by rfl⟩ : syracuseStep 1753445 = 328771) (by norm_num)
theorem B2629997 : Blo 1168401 2629997 := bbase (se 3 (by rfl) ⟨493124, by rfl⟩ : syracuseStep 2629997 = 986249) (by norm_num)
theorem B3555701 : Blo 1168401 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B1753469 : Blo 1168401 1753469 := bbase (se 3 (by rfl) ⟨328775, by rfl⟩ : syracuseStep 1753469 = 657551) (by norm_num)
theorem B5923205 : Blo 1168401 5923205 := bbase (se 4 (by rfl) ⟨555300, by rfl⟩ : syracuseStep 5923205 = 1110601) (by norm_num)
theorem B1753493 : Blo 1168401 1753493 := bbase (se 6 (by rfl) ⟨41097, by rfl⟩ : syracuseStep 1753493 = 82195) (by norm_num)
theorem B1974685 : Blo 1168401 1974685 := bbase (se 3 (by rfl) ⟨370253, by rfl⟩ : syracuseStep 1974685 = 740507) (by norm_num)
theorem B3948965 : Blo 1168401 3948965 := bbase (se 4 (by rfl) ⟨370215, by rfl⟩ : syracuseStep 3948965 = 740431) (by norm_num)
theorem B1753517 : Blo 1168401 1753517 := bbase (se 3 (by rfl) ⟨328784, by rfl⟩ : syracuseStep 1753517 = 657569) (by norm_num)
theorem B2630069 : Blo 1168401 2630069 := bbase (se 5 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 2630069 = 246569) (by norm_num)
theorem B1687997 : Blo 1168401 1687997 := bbase (se 3 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 1687997 = 632999) (by norm_num)
theorem B1753541 : Blo 1168401 1753541 := bbase (se 4 (by rfl) ⟨164394, by rfl⟩ : syracuseStep 1753541 = 328789) (by norm_num)
theorem B2105813 : Blo 1168401 2105813 := bbase (se 7 (by rfl) ⟨24677, by rfl⟩ : syracuseStep 2105813 = 49355) (by norm_num)
theorem B10961365 : Blo 1168401 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B1753565 : Blo 1168401 1753565 := bbase (se 3 (by rfl) ⟨328793, by rfl⟩ : syracuseStep 1753565 = 657587) (by norm_num)
theorem B1753589 : Blo 1168401 1753589 := bbase (se 5 (by rfl) ⟨82199, by rfl⟩ : syracuseStep 1753589 = 164399) (by norm_num)
theorem B1974773 : Blo 1168401 1974773 := bbase (se 5 (by rfl) ⟨92567, by rfl⟩ : syracuseStep 1974773 = 185135) (by norm_num)
theorem B2630141 : Blo 1168401 2630141 := bbase (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) (by norm_num)
theorem B1753613 : Blo 1168401 1753613 := bbase (se 3 (by rfl) ⟨328802, by rfl⟩ : syracuseStep 1753613 = 657605) (by norm_num)
theorem B2105885 : Blo 1168401 2105885 := bbase (se 3 (by rfl) ⟨394853, by rfl⟩ : syracuseStep 2105885 = 789707) (by norm_num)
theorem B1753637 : Blo 1168401 1753637 := bbase (se 4 (by rfl) ⟨164403, by rfl⟩ : syracuseStep 1753637 = 328807) (by norm_num)
theorem B1753661 : Blo 1168401 1753661 := bbase (se 3 (by rfl) ⟨328811, by rfl⟩ : syracuseStep 1753661 = 657623) (by norm_num)
theorem B2630213 : Blo 1168401 2630213 := bbase (se 4 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 2630213 = 493165) (by norm_num)
theorem B1753685 : Blo 1168401 1753685 := bbase (se 8 (by rfl) ⟨10275, by rfl⟩ : syracuseStep 1753685 = 20551) (by norm_num)
theorem B7111253 : Blo 1168401 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B2957917 : Blo 1168401 2957917 := bbase (se 3 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 2957917 = 1109219) (by norm_num)
theorem B1753709 : Blo 1168401 1753709 := bbase (se 3 (by rfl) ⟨328820, by rfl⟩ : syracuseStep 1753709 = 657641) (by norm_num)
theorem B1974901 : Blo 1168401 1974901 := bbase (se 5 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 1974901 = 185147) (by norm_num)
theorem B1753733 : Blo 1168401 1753733 := bbase (se 4 (by rfl) ⟨164412, by rfl⟩ : syracuseStep 1753733 = 328825) (by norm_num)
theorem B2630285 : Blo 1168401 2630285 := bbase (se 3 (by rfl) ⟨493178, by rfl⟩ : syracuseStep 2630285 = 986357) (by norm_num)
theorem B1753757 : Blo 1168401 1753757 := bbase (se 3 (by rfl) ⟨328829, by rfl⟩ : syracuseStep 1753757 = 657659) (by norm_num)
theorem B2220709 : Blo 1168401 2220709 := bbase (se 4 (by rfl) ⟨208191, by rfl⟩ : syracuseStep 2220709 = 416383) (by norm_num)
theorem B8422069 : Blo 1168401 8422069 := bbase (se 5 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 8422069 = 789569) (by norm_num)
theorem B1663669 : Blo 1168401 1663669 := bbase (se 5 (by rfl) ⟨77984, by rfl⟩ : syracuseStep 1663669 = 155969) (by norm_num)
theorem B1753781 : Blo 1168401 1753781 := bbase (se 5 (by rfl) ⟨82208, by rfl⟩ : syracuseStep 1753781 = 164417) (by norm_num)
theorem B2958029 : Blo 1168401 2958029 := bbase (se 3 (by rfl) ⟨554630, by rfl⟩ : syracuseStep 2958029 = 1109261) (by norm_num)
theorem B1753805 : Blo 1168401 1753805 := bbase (se 3 (by rfl) ⟨328838, by rfl⟩ : syracuseStep 1753805 = 657677) (by norm_num)
theorem B1974989 : Blo 1168401 1974989 := bbase (se 3 (by rfl) ⟨370310, by rfl⟩ : syracuseStep 1974989 = 740621) (by norm_num)
theorem B2630357 : Blo 1168401 2630357 := bbase (se 7 (by rfl) ⟨30824, by rfl⟩ : syracuseStep 2630357 = 61649) (by norm_num)
theorem B1753829 : Blo 1168401 1753829 := bbase (se 4 (by rfl) ⟨164421, by rfl⟩ : syracuseStep 1753829 = 328843) (by norm_num)
theorem B1753853 : Blo 1168401 1753853 := bbase (se 3 (by rfl) ⟨328847, by rfl⟩ : syracuseStep 1753853 = 657695) (by norm_num)
theorem B1753877 : Blo 1168401 1753877 := bbase (se 6 (by rfl) ⟨41106, by rfl⟩ : syracuseStep 1753877 = 82213) (by norm_num)
theorem B2499349 : Blo 1168401 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B2630429 : Blo 1168401 2630429 := bbase (se 3 (by rfl) ⟨493205, by rfl⟩ : syracuseStep 2630429 = 986411) (by norm_num)
theorem B5915429 : Blo 1168401 5915429 := bbase (se 4 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 5915429 = 1109143) (by norm_num)
theorem B1753901 : Blo 1168401 1753901 := bbase (se 3 (by rfl) ⟨328856, by rfl⟩ : syracuseStep 1753901 = 657713) (by norm_num)
theorem B4211509 : Blo 1168401 4211509 := bbase (se 5 (by rfl) ⟨197414, by rfl⟩ : syracuseStep 4211509 = 394829) (by norm_num)
theorem B2220853 : Blo 1168401 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B1753925 : Blo 1168401 1753925 := bbase (se 4 (by rfl) ⟨164430, by rfl⟩ : syracuseStep 1753925 = 328861) (by norm_num)
theorem B3949397 : Blo 1168401 3949397 := bbase (se 9 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 3949397 = 23141) (by norm_num)
theorem B1753949 : Blo 1168401 1753949 := bbase (se 3 (by rfl) ⟨328865, by rfl⟩ : syracuseStep 1753949 = 657731) (by norm_num)
theorem B2630501 : Blo 1168401 2630501 := bbase (se 4 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 2630501 = 493219) (by norm_num)
theorem B1753973 : Blo 1168401 1753973 := bbase (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) (by norm_num)
theorem B2958221 : Blo 1168401 2958221 := bbase (se 3 (by rfl) ⟨554666, by rfl⟩ : syracuseStep 2958221 = 1109333) (by norm_num)
theorem B1753997 : Blo 1168401 1753997 := bbase (se 3 (by rfl) ⟨328874, by rfl⟩ : syracuseStep 1753997 = 657749) (by norm_num)
theorem B1754021 : Blo 1168401 1754021 := bbase (se 4 (by rfl) ⟨164439, by rfl⟩ : syracuseStep 1754021 = 328879) (by norm_num)
theorem B2630573 : Blo 1168401 2630573 := bbase (se 3 (by rfl) ⟨493232, by rfl⟩ : syracuseStep 2630573 = 986465) (by norm_num)
theorem B1754045 : Blo 1168401 1754045 := bbase (se 3 (by rfl) ⟨328883, by rfl⟩ : syracuseStep 1754045 = 657767) (by norm_num)
theorem B1754069 : Blo 1168401 1754069 := bbase (se 7 (by rfl) ⟨20555, by rfl⟩ : syracuseStep 1754069 = 41111) (by norm_num)
theorem B21341141 : Blo 1168401 21341141 := bbase (se 7 (by rfl) ⟨250091, by rfl⟩ : syracuseStep 21341141 = 500183) (by norm_num)
theorem B2221013 : Blo 1168401 2221013 := bbase (se 7 (by rfl) ⟨26027, by rfl⟩ : syracuseStep 2221013 = 52055) (by norm_num)
theorem B1754093 : Blo 1168401 1754093 := bbase (se 3 (by rfl) ⟨328892, by rfl⟩ : syracuseStep 1754093 = 657785) (by norm_num)
theorem B2630645 : Blo 1168401 2630645 := bbase (se 5 (by rfl) ⟨123311, by rfl⟩ : syracuseStep 2630645 = 246623) (by norm_num)
theorem B2532341 : Blo 1168401 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B1754117 : Blo 1168401 1754117 := bbase (se 4 (by rfl) ⟨164448, by rfl⟩ : syracuseStep 1754117 = 328897) (by norm_num)
theorem B2106389 : Blo 1168401 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B1754141 : Blo 1168401 1754141 := bbase (se 3 (by rfl) ⟨328901, by rfl⟩ : syracuseStep 1754141 = 657803) (by norm_num)
theorem B1754165 : Blo 1168401 1754165 := bbase (se 5 (by rfl) ⟨82226, by rfl⟩ : syracuseStep 1754165 = 164453) (by norm_num)
theorem B2630717 : Blo 1168401 2630717 := bbase (se 3 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 2630717 = 986519) (by norm_num)
theorem B1754189 : Blo 1168401 1754189 := bbase (se 3 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 1754189 = 657821) (by norm_num)
theorem B1754213 : Blo 1168401 1754213 := bbase (se 4 (by rfl) ⟨164457, by rfl⟩ : syracuseStep 1754213 = 328915) (by norm_num)
theorem B4441189 : Blo 1168401 4441189 := bbase (se 4 (by rfl) ⟨416361, by rfl⟩ : syracuseStep 4441189 = 832723) (by norm_num)
theorem B2221157 : Blo 1168401 2221157 := bbase (se 4 (by rfl) ⟨208233, by rfl⟩ : syracuseStep 2221157 = 416467) (by norm_num)
theorem B6661237 : Blo 1168401 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B1754237 : Blo 1168401 1754237 := bbase (se 3 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 1754237 = 657839) (by norm_num)
theorem B2630789 : Blo 1168401 2630789 := bbase (se 4 (by rfl) ⟨246636, by rfl⟩ : syracuseStep 2630789 = 493273) (by norm_num)
theorem B1754261 : Blo 1168401 1754261 := bbase (se 6 (by rfl) ⟨41115, by rfl⟩ : syracuseStep 1754261 = 82231) (by norm_num)
theorem B1664165 : Blo 1168401 1664165 := bbase (se 4 (by rfl) ⟨156015, by rfl⟩ : syracuseStep 1664165 = 312031) (by norm_num)
theorem B1754285 : Blo 1168401 1754285 := bbase (se 3 (by rfl) ⟨328928, by rfl⟩ : syracuseStep 1754285 = 657857) (by norm_num)
theorem B1754309 : Blo 1168401 1754309 := bbase (se 4 (by rfl) ⟨164466, by rfl⟩ : syracuseStep 1754309 = 328933) (by norm_num)
theorem B2630861 : Blo 1168401 2630861 := bbase (se 3 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 2630861 = 986573) (by norm_num)
theorem B1443037 : Blo 1168401 1443037 := bbase (se 3 (by rfl) ⟨270569, by rfl⟩ : syracuseStep 1443037 = 541139) (by norm_num)
theorem B1754333 : Blo 1168401 1754333 := bbase (se 3 (by rfl) ⟨328937, by rfl⟩ : syracuseStep 1754333 = 657875) (by norm_num)
theorem B2958565 : Blo 1168401 2958565 := bbase (se 4 (by rfl) ⟨277365, by rfl⟩ : syracuseStep 2958565 = 554731) (by norm_num)
theorem B4211957 : Blo 1168401 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B1754357 : Blo 1168401 1754357 := bbase (se 5 (by rfl) ⟨82235, by rfl⟩ : syracuseStep 1754357 = 164471) (by norm_num)
theorem B3949829 : Blo 1168401 3949829 := bbase (se 4 (by rfl) ⟨370296, by rfl⟩ : syracuseStep 3949829 = 740593) (by norm_num)
theorem B1754381 : Blo 1168401 1754381 := bbase (se 3 (by rfl) ⟨328946, by rfl⟩ : syracuseStep 1754381 = 657893) (by norm_num)
theorem B2630933 : Blo 1168401 2630933 := bbase (se 6 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 2630933 = 123325) (by norm_num)
theorem B4744469 : Blo 1168401 4744469 := bbase (se 6 (by rfl) ⟨111198, by rfl⟩ : syracuseStep 4744469 = 222397) (by norm_num)
theorem B3999013 : Blo 1168401 3999013 := bbase (se 4 (by rfl) ⟨374907, by rfl⟩ : syracuseStep 3999013 = 749815) (by norm_num)
theorem B1754405 : Blo 1168401 1754405 := bbase (se 4 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 1754405 = 328951) (by norm_num)
theorem B1754429 : Blo 1168401 1754429 := bbase (se 3 (by rfl) ⟨328955, by rfl⟩ : syracuseStep 1754429 = 657911) (by norm_num)
theorem B1500493 : Blo 1168401 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B2958677 : Blo 1168401 2958677 := bbase (se 12 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 2958677 = 2167) (by norm_num)
theorem B1754453 : Blo 1168401 1754453 := bbase (se 12 (by rfl) ⟨642, by rfl⟩ : syracuseStep 1754453 = 1285) (by norm_num)
theorem B2631005 : Blo 1168401 2631005 := bbase (se 3 (by rfl) ⟨493313, by rfl⟩ : syracuseStep 2631005 = 986627) (by norm_num)
theorem B1754477 : Blo 1168401 1754477 := bbase (se 3 (by rfl) ⟨328964, by rfl⟩ : syracuseStep 1754477 = 657929) (by norm_num)
theorem B4744565 : Blo 1168401 4744565 := bbase (se 5 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 4744565 = 444803) (by norm_num)
theorem B1754501 : Blo 1168401 1754501 := bbase (se 4 (by rfl) ⟨164484, by rfl⟩ : syracuseStep 1754501 = 328969) (by norm_num)
theorem B2221445 : Blo 1168401 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B2368909 : Blo 1168401 2368909 := bbase (se 3 (by rfl) ⟨444170, by rfl⟩ : syracuseStep 2368909 = 888341) (by norm_num)
theorem B4441493 : Blo 1168401 4441493 := bbase (se 6 (by rfl) ⟨104097, by rfl⟩ : syracuseStep 4441493 = 208195) (by norm_num)
theorem B1754525 : Blo 1168401 1754525 := bbase (se 3 (by rfl) ⟨328973, by rfl⟩ : syracuseStep 1754525 = 657947) (by norm_num)
theorem B2631077 : Blo 1168401 2631077 := bbase (se 4 (by rfl) ⟨246663, by rfl⟩ : syracuseStep 2631077 = 493327) (by norm_num)
theorem B1754549 : Blo 1168401 1754549 := bbase (se 5 (by rfl) ⟨82244, by rfl⟩ : syracuseStep 1754549 = 164489) (by norm_num)
theorem B1754573 : Blo 1168401 1754573 := bbase (se 3 (by rfl) ⟨328982, by rfl⟩ : syracuseStep 1754573 = 657965) (by norm_num)
theorem B7497173 : Blo 1168401 7497173 := bbase (se 7 (by rfl) ⟨87857, by rfl⟩ : syracuseStep 7497173 = 175715) (by norm_num)
theorem B1754597 : Blo 1168401 1754597 := bbase (se 4 (by rfl) ⟨164493, by rfl⟩ : syracuseStep 1754597 = 328987) (by norm_num)
theorem B2631149 : Blo 1168401 2631149 := bbase (se 3 (by rfl) ⟨493340, by rfl⟩ : syracuseStep 2631149 = 986681) (by norm_num)
theorem B1754621 : Blo 1168401 1754621 := bbase (se 3 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 1754621 = 657983) (by norm_num)
theorem B2958869 : Blo 1168401 2958869 := bbase (se 6 (by rfl) ⟨69348, by rfl⟩ : syracuseStep 2958869 = 138697) (by norm_num)
theorem B1754645 : Blo 1168401 1754645 := bbase (se 6 (by rfl) ⟨41124, by rfl⟩ : syracuseStep 1754645 = 82249) (by norm_num)
theorem B2221597 : Blo 1168401 2221597 := bbase (se 3 (by rfl) ⟨416549, by rfl⟩ : syracuseStep 2221597 = 833099) (by norm_num)
theorem B1754669 : Blo 1168401 1754669 := bbase (se 3 (by rfl) ⟨329000, by rfl⟩ : syracuseStep 1754669 = 658001) (by norm_num)
theorem B2631221 : Blo 1168401 2631221 := bbase (se 5 (by rfl) ⟨123338, by rfl⟩ : syracuseStep 2631221 = 246677) (by norm_num)
theorem B1754693 : Blo 1168401 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B1754717 : Blo 1168401 1754717 := bbase (se 3 (by rfl) ⟨329009, by rfl⟩ : syracuseStep 1754717 = 658019) (by norm_num)
theorem B1754741 : Blo 1168401 1754741 := bbase (se 5 (by rfl) ⟨82253, by rfl⟩ : syracuseStep 1754741 = 164507) (by norm_num)
theorem B2631293 : Blo 1168401 2631293 := bbase (se 3 (by rfl) ⟨493367, by rfl⟩ : syracuseStep 2631293 = 986735) (by norm_num)
theorem B1754765 : Blo 1168401 1754765 := bbase (se 3 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 1754765 = 658037) (by norm_num)
theorem B5924501 : Blo 1168401 5924501 := bbase (se 6 (by rfl) ⟨138855, by rfl⟩ : syracuseStep 5924501 = 277711) (by norm_num)
theorem B1754789 : Blo 1168401 1754789 := bbase (se 4 (by rfl) ⟨164511, by rfl⟩ : syracuseStep 1754789 = 329023) (by norm_num)
theorem B9995957 : Blo 1168401 9995957 := bbase (se 5 (by rfl) ⟨468560, by rfl⟩ : syracuseStep 9995957 = 937121) (by norm_num)
theorem B1754813 : Blo 1168401 1754813 := bbase (se 3 (by rfl) ⟨329027, by rfl⟩ : syracuseStep 1754813 = 658055) (by norm_num)
theorem B2631365 : Blo 1168401 2631365 := bbase (se 4 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 2631365 = 493381) (by norm_num)
theorem B1664717 : Blo 1168401 1664717 := bbase (se 3 (by rfl) ⟨312134, by rfl⟩ : syracuseStep 1664717 = 624269) (by norm_num)
theorem B1754837 : Blo 1168401 1754837 := bbase (se 7 (by rfl) ⟨20564, by rfl⟩ : syracuseStep 1754837 = 41129) (by norm_num)
theorem B1754861 : Blo 1168401 1754861 := bbase (se 3 (by rfl) ⟨329036, by rfl⟩ : syracuseStep 1754861 = 658073) (by norm_num)
theorem B3327749 : Blo 1168401 3327749 := bbase (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) (by norm_num)
theorem B1754885 : Blo 1168401 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B2631437 : Blo 1168401 2631437 := bbase (se 3 (by rfl) ⟨493394, by rfl⟩ : syracuseStep 2631437 = 986789) (by norm_num)
theorem B1754909 : Blo 1168401 1754909 := bbase (se 3 (by rfl) ⟨329045, by rfl⟩ : syracuseStep 1754909 = 658091) (by norm_num)
theorem B9987893 : Blo 1168401 9987893 := bbase (se 5 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 9987893 = 936365) (by norm_num)
theorem B1754933 : Blo 1168401 1754933 := bbase (se 5 (by rfl) ⟨82262, by rfl⟩ : syracuseStep 1754933 = 164525) (by norm_num)
theorem B1754957 : Blo 1168401 1754957 := bbase (se 3 (by rfl) ⟨329054, by rfl⟩ : syracuseStep 1754957 = 658109) (by norm_num)
theorem B2221901 : Blo 1168401 2221901 := bbase (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) (by norm_num)
theorem B2631509 : Blo 1168401 2631509 := bbase (se 9 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 2631509 = 15419) (by norm_num)
theorem B11241301 : Blo 1168401 11241301 := bbase (se 9 (by rfl) ⟨32933, by rfl⟩ : syracuseStep 11241301 = 65867) (by norm_num)
theorem B1754981 : Blo 1168401 1754981 := bbase (se 4 (by rfl) ⟨164529, by rfl⟩ : syracuseStep 1754981 = 329059) (by norm_num)
theorem B2959213 : Blo 1168401 2959213 := bbase (se 3 (by rfl) ⟨554852, by rfl⟩ : syracuseStep 2959213 = 1109705) (by norm_num)
theorem B1755005 : Blo 1168401 1755005 := bbase (se 3 (by rfl) ⟨329063, by rfl⟩ : syracuseStep 1755005 = 658127) (by norm_num)
theorem B2369429 : Blo 1168401 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B1755029 : Blo 1168401 1755029 := bbase (se 6 (by rfl) ⟨41133, by rfl⟩ : syracuseStep 1755029 = 82267) (by norm_num)
theorem B2631581 : Blo 1168401 2631581 := bbase (se 3 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 2631581 = 986843) (by norm_num)
theorem B1755053 : Blo 1168401 1755053 := bbase (se 3 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 1755053 = 658145) (by norm_num)
theorem B1755077 : Blo 1168401 1755077 := bbase (se 4 (by rfl) ⟨164538, by rfl⟩ : syracuseStep 1755077 = 329077) (by norm_num)
theorem B2959325 : Blo 1168401 2959325 := bbase (se 3 (by rfl) ⟨554873, by rfl⟩ : syracuseStep 2959325 = 1109747) (by norm_num)
theorem B1755101 : Blo 1168401 1755101 := bbase (se 3 (by rfl) ⟨329081, by rfl⟩ : syracuseStep 1755101 = 658163) (by norm_num)
theorem B2631653 : Blo 1168401 2631653 := bbase (se 4 (by rfl) ⟨246717, by rfl⟩ : syracuseStep 2631653 = 493435) (by norm_num)
theorem B1755125 : Blo 1168401 1755125 := bbase (se 5 (by rfl) ⟨82271, by rfl⟩ : syracuseStep 1755125 = 164543) (by norm_num)
theorem B1755149 : Blo 1168401 1755149 := bbase (se 3 (by rfl) ⟨329090, by rfl⟩ : syracuseStep 1755149 = 658181) (by norm_num)
theorem B1755173 : Blo 1168401 1755173 := bbase (se 4 (by rfl) ⟨164547, by rfl⟩ : syracuseStep 1755173 = 329095) (by norm_num)
theorem B2631725 : Blo 1168401 2631725 := bbase (se 3 (by rfl) ⟨493448, by rfl⟩ : syracuseStep 2631725 = 986897) (by norm_num)
theorem B5916725 : Blo 1168401 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B4499509 : Blo 1168401 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B1755197 : Blo 1168401 1755197 := bbase (se 3 (by rfl) ⟨329099, by rfl⟩ : syracuseStep 1755197 = 658199) (by norm_num)
theorem B1755221 : Blo 1168401 1755221 := bbase (se 8 (by rfl) ⟨10284, by rfl⟩ : syracuseStep 1755221 = 20569) (by norm_num)
theorem B1755245 : Blo 1168401 1755245 := bbase (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) (by norm_num)
theorem B2631797 : Blo 1168401 2631797 := bbase (se 5 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 2631797 = 246731) (by norm_num)
theorem B1755269 : Blo 1168401 1755269 := bbase (se 4 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 1755269 = 329113) (by norm_num)
theorem B2959517 : Blo 1168401 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B1755293 : Blo 1168401 1755293 := bbase (se 3 (by rfl) ⟨329117, by rfl⟩ : syracuseStep 1755293 = 658235) (by norm_num)
theorem B1755317 : Blo 1168401 1755317 := bbase (se 5 (by rfl) ⟨82280, by rfl⟩ : syracuseStep 1755317 = 164561) (by norm_num)
theorem B2631869 : Blo 1168401 2631869 := bbase (se 3 (by rfl) ⟨493475, by rfl⟩ : syracuseStep 2631869 = 986951) (by norm_num)
theorem B1755341 : Blo 1168401 1755341 := bbase (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) (by norm_num)
theorem B1755365 : Blo 1168401 1755365 := bbase (se 4 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 1755365 = 329131) (by norm_num)
theorem B2812133 : Blo 1168401 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B1755389 : Blo 1168401 1755389 := bbase (se 3 (by rfl) ⟨329135, by rfl⟩ : syracuseStep 1755389 = 658271) (by norm_num)
theorem B5335301 : Blo 1168401 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B2631941 : Blo 1168401 2631941 := bbase (se 4 (by rfl) ⟨246744, by rfl⟩ : syracuseStep 2631941 = 493489) (by norm_num)
theorem B1755413 : Blo 1168401 1755413 := bbase (se 6 (by rfl) ⟨41142, by rfl⟩ : syracuseStep 1755413 = 82285) (by norm_num)
theorem B1755437 : Blo 1168401 1755437 := bbase (se 3 (by rfl) ⟨329144, by rfl⟩ : syracuseStep 1755437 = 658289) (by norm_num)
theorem B1755461 : Blo 1168401 1755461 := bbase (se 4 (by rfl) ⟨164574, by rfl⟩ : syracuseStep 1755461 = 329149) (by norm_num)
theorem B2632013 : Blo 1168401 2632013 := bbase (se 3 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 2632013 = 987005) (by norm_num)
theorem B1755485 : Blo 1168401 1755485 := bbase (se 3 (by rfl) ⟨329153, by rfl⟩ : syracuseStep 1755485 = 658307) (by norm_num)
theorem B1755509 : Blo 1168401 1755509 := bbase (se 5 (by rfl) ⟨82289, by rfl⟩ : syracuseStep 1755509 = 164579) (by norm_num)
theorem B1755533 : Blo 1168401 1755533 := bbase (se 3 (by rfl) ⟨329162, by rfl⟩ : syracuseStep 1755533 = 658325) (by norm_num)
theorem B2632085 : Blo 1168401 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B1755557 : Blo 1168401 1755557 := bbase (se 4 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 1755557 = 329167) (by norm_num)
theorem B1665469 : Blo 1168401 1665469 := bbase (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) (by norm_num)
theorem B1755581 : Blo 1168401 1755581 := bbase (se 3 (by rfl) ⟨329171, by rfl⟩ : syracuseStep 1755581 = 658343) (by norm_num)
theorem B2632157 : Blo 1168401 2632157 := bbase (se 3 (by rfl) ⟨493529, by rfl⟩ : syracuseStep 2632157 = 987059) (by norm_num)
theorem B2959861 : Blo 1168401 2959861 := bbase (se 5 (by rfl) ⟨138743, by rfl⟩ : syracuseStep 2959861 = 277487) (by norm_num)
theorem B1247761 : Blo 1168401 1247761 := bbase (se 2 (by rfl) ⟨467910, by rfl⟩ : syracuseStep 1247761 = 935821) (by norm_num)
theorem B2632229 : Blo 1168401 2632229 := bbase (se 4 (by rfl) ⟨246771, by rfl⟩ : syracuseStep 2632229 = 493543) (by norm_num)
theorem B2959973 : Blo 1168401 2959973 := bbase (se 4 (by rfl) ⟨277497, by rfl⟩ : syracuseStep 2959973 = 554995) (by norm_num)
theorem B2632301 : Blo 1168401 2632301 := bbase (se 3 (by rfl) ⟨493556, by rfl⟩ : syracuseStep 2632301 = 987113) (by norm_num)
theorem B2402941 : Blo 1168401 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B2632373 : Blo 1168401 2632373 := bbase (se 5 (by rfl) ⟨123392, by rfl⟩ : syracuseStep 2632373 = 246785) (by norm_num)
theorem B2632445 : Blo 1168401 2632445 := bbase (se 3 (by rfl) ⟨493583, by rfl⟩ : syracuseStep 2632445 = 987167) (by norm_num)
theorem B2960165 : Blo 1168401 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B4991813 : Blo 1168401 4991813 := bbase (se 4 (by rfl) ⟨467982, by rfl⟩ : syracuseStep 4991813 = 935965) (by norm_num)
theorem B2632517 : Blo 1168401 2632517 := bbase (se 4 (by rfl) ⟨246798, by rfl⟩ : syracuseStep 2632517 = 493597) (by norm_num)
theorem B6327125 : Blo 1168401 6327125 := bbase (se 9 (by rfl) ⟨18536, by rfl⟩ : syracuseStep 6327125 = 37073) (by norm_num)
theorem B2632589 : Blo 1168401 2632589 := bbase (se 3 (by rfl) ⟨493610, by rfl⟩ : syracuseStep 2632589 = 987221) (by norm_num)
theorem B3328933 : Blo 1168401 3328933 := bbase (se 4 (by rfl) ⟨312087, by rfl⟩ : syracuseStep 3328933 = 624175) (by norm_num)
theorem B3746741 : Blo 1168401 3746741 := bbase (se 5 (by rfl) ⟨175628, by rfl⟩ : syracuseStep 3746741 = 351257) (by norm_num)
theorem B5622709 : Blo 1168401 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B1248205 : Blo 1168401 1248205 := bbase (se 3 (by rfl) ⟨234038, by rfl⟩ : syracuseStep 1248205 = 468077) (by norm_num)
theorem B2632661 : Blo 1168401 2632661 := bbase (se 7 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 2632661 = 61703) (by norm_num)
theorem B2632733 : Blo 1168401 2632733 := bbase (se 3 (by rfl) ⟨493637, by rfl⟩ : syracuseStep 2632733 = 987275) (by norm_num)
theorem B6663221 : Blo 1168401 6663221 := bbase (se 5 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 6663221 = 624677) (by norm_num)
theorem B3329093 : Blo 1168401 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B1248329 : Blo 1168401 1248329 := bbase (se 2 (by rfl) ⟨468123, by rfl⟩ : syracuseStep 1248329 = 936247) (by norm_num)
theorem B4992101 : Blo 1168401 4992101 := bbase (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) (by norm_num)
theorem B2632805 : Blo 1168401 2632805 := bbase (se 4 (by rfl) ⟨246825, by rfl⟩ : syracuseStep 2632805 = 493651) (by norm_num)
theorem B2960509 : Blo 1168401 2960509 := bbase (se 3 (by rfl) ⟨555095, by rfl⟩ : syracuseStep 2960509 = 1110191) (by norm_num)
theorem B2632877 : Blo 1168401 2632877 := bbase (se 3 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 2632877 = 987329) (by norm_num)
theorem B1666261 : Blo 1168401 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B2960621 : Blo 1168401 2960621 := bbase (se 3 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 2960621 = 1110233) (by norm_num)
theorem B2632949 : Blo 1168401 2632949 := bbase (se 5 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 2632949 = 246839) (by norm_num)
theorem B3329333 : Blo 1168401 3329333 := bbase (se 5 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 3329333 = 312125) (by norm_num)
theorem B1404221 : Blo 1168401 1404221 := bbase (se 3 (by rfl) ⟨263291, by rfl⟩ : syracuseStep 1404221 = 526583) (by norm_num)
theorem B2633021 : Blo 1168401 2633021 := bbase (se 3 (by rfl) ⟨493691, by rfl⟩ : syracuseStep 2633021 = 987383) (by norm_num)
theorem B5918021 : Blo 1168401 5918021 := bbase (se 4 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 5918021 = 1109629) (by norm_num)
theorem B1248581 : Blo 1168401 1248581 := bbase (se 4 (by rfl) ⟨117054, by rfl⟩ : syracuseStep 1248581 = 234109) (by norm_num)
theorem B3943781 : Blo 1168401 3943781 := bbase (se 4 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 3943781 = 739459) (by norm_num)
theorem B2633093 : Blo 1168401 2633093 := bbase (se 4 (by rfl) ⟨246852, by rfl⟩ : syracuseStep 2633093 = 493705) (by norm_num)
theorem B2960813 : Blo 1168401 2960813 := bbase (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) (by norm_num)
theorem B2633165 : Blo 1168401 2633165 := bbase (se 3 (by rfl) ⟨493718, by rfl⟩ : syracuseStep 2633165 = 987437) (by norm_num)
theorem B4443605 : Blo 1168401 4443605 := bbase (se 7 (by rfl) ⟨52073, by rfl⟩ : syracuseStep 4443605 = 104147) (by norm_num)
theorem B5615077 : Blo 1168401 5615077 := bbase (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) (by norm_num)
theorem B3329525 : Blo 1168401 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B2633237 : Blo 1168401 2633237 := bbase (se 6 (by rfl) ⟨61716, by rfl⟩ : syracuseStep 2633237 = 123433) (by norm_num)
theorem B2633309 : Blo 1168401 2633309 := bbase (se 3 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 2633309 = 987491) (by norm_num)
theorem B2633381 : Blo 1168401 2633381 := bbase (se 4 (by rfl) ⟨246879, by rfl⟩ : syracuseStep 2633381 = 493759) (by norm_num)
theorem B1314481 : Blo 1168401 1314481 := bbase (se 2 (by rfl) ⟨492930, by rfl⟩ : syracuseStep 1314481 = 985861) (by norm_num)
theorem B1314517 : Blo 1168401 1314517 := bbase (se 7 (by rfl) ⟨15404, by rfl⟩ : syracuseStep 1314517 = 30809) (by norm_num)
theorem B1314553 : Blo 1168401 1314553 := bbase (se 2 (by rfl) ⟨492957, by rfl⟩ : syracuseStep 1314553 = 985915) (by norm_num)
theorem B1249025 : Blo 1168401 1249025 := bbase (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) (by norm_num)
theorem B2961157 : Blo 1168401 2961157 := bbase (se 4 (by rfl) ⟨277608, by rfl⟩ : syracuseStep 2961157 = 555217) (by norm_num)
theorem B3944213 : Blo 1168401 3944213 := bbase (se 6 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 3944213 = 184885) (by norm_num)
theorem B1314589 : Blo 1168401 1314589 := bbase (se 3 (by rfl) ⟨246485, by rfl⟩ : syracuseStep 1314589 = 492971) (by norm_num)
theorem B1314625 : Blo 1168401 1314625 := bbase (se 2 (by rfl) ⟨492984, by rfl⟩ : syracuseStep 1314625 = 985969) (by norm_num)
theorem B3747653 : Blo 1168401 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B4992853 : Blo 1168401 4992853 := bbase (se 9 (by rfl) ⟨14627, by rfl⟩ : syracuseStep 4992853 = 29255) (by norm_num)
theorem B1314661 : Blo 1168401 1314661 := bbase (se 4 (by rfl) ⟨123249, by rfl⟩ : syracuseStep 1314661 = 246499) (by norm_num)
theorem B2961269 : Blo 1168401 2961269 := bbase (se 5 (by rfl) ⟨138809, by rfl⟩ : syracuseStep 2961269 = 277619) (by norm_num)
theorem B1314697 : Blo 1168401 1314697 := bbase (se 2 (by rfl) ⟨493011, by rfl⟩ : syracuseStep 1314697 = 986023) (by norm_num)
theorem B1314733 : Blo 1168401 1314733 := bbase (se 3 (by rfl) ⟨246512, by rfl⟩ : syracuseStep 1314733 = 493025) (by norm_num)
theorem B1314769 : Blo 1168401 1314769 := bbase (se 2 (by rfl) ⟨493038, by rfl⟩ : syracuseStep 1314769 = 986077) (by norm_num)
theorem B1404913 : Blo 1168401 1404913 := bbase (se 2 (by rfl) ⟨526842, by rfl⟩ : syracuseStep 1404913 = 1053685) (by norm_num)
theorem B1314805 : Blo 1168401 1314805 := bbase (se 5 (by rfl) ⟨61631, by rfl⟩ : syracuseStep 1314805 = 123263) (by norm_num)
theorem B1249273 : Blo 1168401 1249273 := bbase (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) (by norm_num)
theorem B1871885 : Blo 1168401 1871885 := bbase (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) (by norm_num)
theorem B1314841 : Blo 1168401 1314841 := bbase (se 2 (by rfl) ⟨493065, by rfl⟩ : syracuseStep 1314841 = 986131) (by norm_num)
theorem B2961461 : Blo 1168401 2961461 := bbase (se 5 (by rfl) ⟨138818, by rfl⟩ : syracuseStep 2961461 = 277637) (by norm_num)
theorem B1314877 : Blo 1168401 1314877 := bbase (se 3 (by rfl) ⟨246539, by rfl⟩ : syracuseStep 1314877 = 493079) (by norm_num)
theorem B1405009 : Blo 1168401 1405009 := bbase (se 2 (by rfl) ⟨526878, by rfl⟩ : syracuseStep 1405009 = 1053757) (by norm_num)
theorem B1314913 : Blo 1168401 1314913 := bbase (se 2 (by rfl) ⟨493092, by rfl⟩ : syracuseStep 1314913 = 986185) (by norm_num)
theorem B2404469 : Blo 1168401 2404469 := bbase (se 5 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 2404469 = 225419) (by norm_num)
theorem B2248829 : Blo 1168401 2248829 := bbase (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) (by norm_num)
theorem B1314949 : Blo 1168401 1314949 := bbase (se 4 (by rfl) ⟨123276, by rfl⟩ : syracuseStep 1314949 = 246553) (by norm_num)
theorem B1872013 : Blo 1168401 1872013 := bbase (se 3 (by rfl) ⟨351002, by rfl⟩ : syracuseStep 1872013 = 702005) (by norm_num)
theorem B3043469 : Blo 1168401 3043469 := bbase (se 3 (by rfl) ⟨570650, by rfl⟩ : syracuseStep 3043469 = 1141301) (by norm_num)
theorem B1314985 : Blo 1168401 1314985 := bbase (se 2 (by rfl) ⟨493119, by rfl⟩ : syracuseStep 1314985 = 986239) (by norm_num)
theorem B1478837 : Blo 1168401 1478837 := bbase (se 5 (by rfl) ⟨69320, by rfl⟩ : syracuseStep 1478837 = 138641) (by norm_num)
theorem B3944645 : Blo 1168401 3944645 := bbase (se 4 (by rfl) ⟨369810, by rfl⟩ : syracuseStep 3944645 = 739621) (by norm_num)
theorem B1315021 : Blo 1168401 1315021 := bbase (se 3 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 1315021 = 493133) (by norm_num)
theorem B1478893 : Blo 1168401 1478893 := bbase (se 3 (by rfl) ⟨277292, by rfl⟩ : syracuseStep 1478893 = 554585) (by norm_num)
theorem B1315057 : Blo 1168401 1315057 := bbase (se 2 (by rfl) ⟨493146, by rfl⟩ : syracuseStep 1315057 = 986293) (by norm_num)
theorem B1315093 : Blo 1168401 1315093 := bbase (se 6 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 1315093 = 61645) (by norm_num)
theorem B1315129 : Blo 1168401 1315129 := bbase (se 2 (by rfl) ⟨493173, by rfl⟩ : syracuseStep 1315129 = 986347) (by norm_num)
theorem B1478989 : Blo 1168401 1478989 := bbase (se 3 (by rfl) ⟨277310, by rfl⟩ : syracuseStep 1478989 = 554621) (by norm_num)
theorem B8884565 : Blo 1168401 8884565 := bbase (se 10 (by rfl) ⟨13014, by rfl⟩ : syracuseStep 8884565 = 26029) (by norm_num)
theorem B1315165 : Blo 1168401 1315165 := bbase (se 3 (by rfl) ⟨246593, by rfl⟩ : syracuseStep 1315165 = 493187) (by norm_num)
theorem B1315201 : Blo 1168401 1315201 := bbase (se 2 (by rfl) ⟨493200, by rfl⟩ : syracuseStep 1315201 = 986401) (by norm_num)
theorem B2961805 : Blo 1168401 2961805 := bbase (se 3 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 2961805 = 1110677) (by norm_num)
theorem B1315237 : Blo 1168401 1315237 := bbase (se 4 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 1315237 = 246607) (by norm_num)
theorem B1249717 : Blo 1168401 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B1315273 : Blo 1168401 1315273 := bbase (se 2 (by rfl) ⟨493227, by rfl⟩ : syracuseStep 1315273 = 986455) (by norm_num)
theorem B3330517 : Blo 1168401 3330517 := bbase (se 7 (by rfl) ⟨39029, by rfl⟩ : syracuseStep 3330517 = 78059) (by norm_num)
theorem B1315309 : Blo 1168401 1315309 := bbase (se 3 (by rfl) ⟨246620, by rfl⟩ : syracuseStep 1315309 = 493241) (by norm_num)
theorem B1249777 : Blo 1168401 1249777 := bbase (se 2 (by rfl) ⟨468666, by rfl⟩ : syracuseStep 1249777 = 937333) (by norm_num)
theorem B1479161 : Blo 1168401 1479161 := bbase (se 2 (by rfl) ⟨554685, by rfl⟩ : syracuseStep 1479161 = 1109371) (by norm_num)
theorem B2961917 : Blo 1168401 2961917 := bbase (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) (by norm_num)
theorem B1872397 : Blo 1168401 1872397 := bbase (se 3 (by rfl) ⟨351074, by rfl⟩ : syracuseStep 1872397 = 702149) (by norm_num)
theorem B1315345 : Blo 1168401 1315345 := bbase (se 2 (by rfl) ⟨493254, by rfl⟩ : syracuseStep 1315345 = 986509) (by norm_num)
theorem B1479217 : Blo 1168401 1479217 := bbase (se 2 (by rfl) ⟨554706, by rfl⟩ : syracuseStep 1479217 = 1109413) (by norm_num)
theorem B4993589 : Blo 1168401 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B1315381 : Blo 1168401 1315381 := bbase (se 5 (by rfl) ⟨61658, by rfl⟩ : syracuseStep 1315381 = 123317) (by norm_num)
theorem B5919317 : Blo 1168401 5919317 := bbase (se 8 (by rfl) ⟨34683, by rfl⟩ : syracuseStep 5919317 = 69367) (by norm_num)
theorem B1315417 : Blo 1168401 1315417 := bbase (se 2 (by rfl) ⟨493281, by rfl⟩ : syracuseStep 1315417 = 986563) (by norm_num)
theorem B3945077 : Blo 1168401 3945077 := bbase (se 5 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 3945077 = 369851) (by norm_num)
theorem B1315453 : Blo 1168401 1315453 := bbase (se 3 (by rfl) ⟨246647, by rfl⟩ : syracuseStep 1315453 = 493295) (by norm_num)
theorem B1479313 : Blo 1168401 1479313 := bbase (se 2 (by rfl) ⟨554742, by rfl⟩ : syracuseStep 1479313 = 1109485) (by norm_num)
theorem B1315489 : Blo 1168401 1315489 := bbase (se 2 (by rfl) ⟨493308, by rfl⟩ : syracuseStep 1315489 = 986617) (by norm_num)
theorem B2962109 : Blo 1168401 2962109 := bbase (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) (by norm_num)
theorem B1315525 : Blo 1168401 1315525 := bbase (se 4 (by rfl) ⟨123330, by rfl⟩ : syracuseStep 1315525 = 246661) (by norm_num)
theorem B1315561 : Blo 1168401 1315561 := bbase (se 2 (by rfl) ⟨493335, by rfl⟩ : syracuseStep 1315561 = 986671) (by norm_num)
theorem B8876789 : Blo 1168401 8876789 := bbase (se 5 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 8876789 = 832199) (by norm_num)
theorem B1872653 : Blo 1168401 1872653 := bbase (se 3 (by rfl) ⟨351122, by rfl⟩ : syracuseStep 1872653 = 702245) (by norm_num)
theorem B1315597 : Blo 1168401 1315597 := bbase (se 3 (by rfl) ⟨246674, by rfl⟩ : syracuseStep 1315597 = 493349) (by norm_num)
theorem B1315633 : Blo 1168401 1315633 := bbase (se 2 (by rfl) ⟨493362, by rfl⟩ : syracuseStep 1315633 = 986725) (by norm_num)
theorem B1479485 : Blo 1168401 1479485 := bbase (se 3 (by rfl) ⟨277403, by rfl⟩ : syracuseStep 1479485 = 554807) (by norm_num)
theorem B1200961 : Blo 1168401 1200961 := bbase (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) (by norm_num)
theorem B1315669 : Blo 1168401 1315669 := bbase (se 9 (by rfl) ⟨3854, by rfl⟩ : syracuseStep 1315669 = 7709) (by norm_num)
theorem B1405793 : Blo 1168401 1405793 := bbase (se 2 (by rfl) ⟨527172, by rfl⟩ : syracuseStep 1405793 = 1054345) (by norm_num)
theorem B1479541 : Blo 1168401 1479541 := bbase (se 5 (by rfl) ⟨69353, by rfl⟩ : syracuseStep 1479541 = 138707) (by norm_num)
theorem B1315705 : Blo 1168401 1315705 := bbase (se 2 (by rfl) ⟨493389, by rfl⟩ : syracuseStep 1315705 = 986779) (by norm_num)
theorem B1315741 : Blo 1168401 1315741 := bbase (se 3 (by rfl) ⟨246701, by rfl⟩ : syracuseStep 1315741 = 493403) (by norm_num)
theorem B1315777 : Blo 1168401 1315777 := bbase (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) (by norm_num)
theorem B1266629 : Blo 1168401 1266629 := bbase (se 4 (by rfl) ⟨118746, by rfl⟩ : syracuseStep 1266629 = 237493) (by norm_num)
theorem B1479637 : Blo 1168401 1479637 := bbase (se 7 (by rfl) ⟨17339, by rfl⟩ : syracuseStep 1479637 = 34679) (by norm_num)
theorem B1315813 : Blo 1168401 1315813 := bbase (se 4 (by rfl) ⟨123357, by rfl⟩ : syracuseStep 1315813 = 246715) (by norm_num)
theorem B1315849 : Blo 1168401 1315849 := bbase (se 2 (by rfl) ⟨493443, by rfl⟩ : syracuseStep 1315849 = 986887) (by norm_num)
theorem B14996501 : Blo 1168401 14996501 := bbase (se 6 (by rfl) ⟨351480, by rfl⟩ : syracuseStep 14996501 = 702961) (by norm_num)
theorem B2962453 : Blo 1168401 2962453 := bbase (se 6 (by rfl) ⟨69432, by rfl⟩ : syracuseStep 2962453 = 138865) (by norm_num)
theorem B3945509 : Blo 1168401 3945509 := bbase (se 4 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 3945509 = 739783) (by norm_num)
theorem B1315885 : Blo 1168401 1315885 := bbase (se 3 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 1315885 = 493457) (by norm_num)
theorem B1315921 : Blo 1168401 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B3847253 : Blo 1168401 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B1184873 : Blo 1168401 1184873 := bbase (se 2 (by rfl) ⟨444327, by rfl⟩ : syracuseStep 1184873 = 888655) (by norm_num)
theorem B1315957 : Blo 1168401 1315957 := bbase (se 5 (by rfl) ⟨61685, by rfl⟩ : syracuseStep 1315957 = 123371) (by norm_num)
theorem B4502645 : Blo 1168401 4502645 := bbase (se 5 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 4502645 = 422123) (by norm_num)
theorem B1479809 : Blo 1168401 1479809 := bbase (se 2 (by rfl) ⟨554928, by rfl⟩ : syracuseStep 1479809 = 1109857) (by norm_num)
theorem B3159173 : Blo 1168401 3159173 := bbase (se 4 (by rfl) ⟨296172, by rfl⟩ : syracuseStep 3159173 = 592345) (by norm_num)
theorem B3748997 : Blo 1168401 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B2962565 : Blo 1168401 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B1315993 : Blo 1168401 1315993 := bbase (se 2 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 1315993 = 986995) (by norm_num)
theorem B1479865 : Blo 1168401 1479865 := bbase (se 2 (by rfl) ⟨554949, by rfl⟩ : syracuseStep 1479865 = 1109899) (by norm_num)
theorem B1316029 : Blo 1168401 1316029 := bbase (se 3 (by rfl) ⟨246755, by rfl⟩ : syracuseStep 1316029 = 493511) (by norm_num)
theorem B2495701 : Blo 1168401 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B6665429 : Blo 1168401 6665429 := bbase (se 7 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 6665429 = 156221) (by norm_num)
theorem B1316065 : Blo 1168401 1316065 := bbase (se 2 (by rfl) ⟨493524, by rfl⟩ : syracuseStep 1316065 = 987049) (by norm_num)
theorem B1316101 : Blo 1168401 1316101 := bbase (se 4 (by rfl) ⟨123384, by rfl⟩ : syracuseStep 1316101 = 246769) (by norm_num)
theorem B2667797 : Blo 1168401 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B1479961 : Blo 1168401 1479961 := bbase (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) (by norm_num)
theorem B1316137 : Blo 1168401 1316137 := bbase (se 2 (by rfl) ⟨493551, by rfl⟩ : syracuseStep 1316137 = 987103) (by norm_num)
theorem B4437301 : Blo 1168401 4437301 := bbase (se 5 (by rfl) ⟨207998, by rfl⟩ : syracuseStep 4437301 = 415997) (by norm_num)
theorem B1316173 : Blo 1168401 1316173 := bbase (se 3 (by rfl) ⟨246782, by rfl⟩ : syracuseStep 1316173 = 493565) (by norm_num)
theorem B1316209 : Blo 1168401 1316209 := bbase (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) (by norm_num)
theorem B1316245 : Blo 1168401 1316245 := bbase (se 6 (by rfl) ⟨30849, by rfl⟩ : syracuseStep 1316245 = 61699) (by norm_num)
theorem B1316281 : Blo 1168401 1316281 := bbase (se 2 (by rfl) ⟨493605, by rfl⟩ : syracuseStep 1316281 = 987211) (by norm_num)
theorem B1480133 : Blo 1168401 1480133 := bbase (se 4 (by rfl) ⟨138762, by rfl⟩ : syracuseStep 1480133 = 277525) (by norm_num)
theorem B3945941 : Blo 1168401 3945941 := bbase (se 7 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 3945941 = 92483) (by norm_num)
theorem B1316317 : Blo 1168401 1316317 := bbase (se 3 (by rfl) ⟨246809, by rfl⟩ : syracuseStep 1316317 = 493619) (by norm_num)
theorem B1480189 : Blo 1168401 1480189 := bbase (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) (by norm_num)
theorem B1316353 : Blo 1168401 1316353 := bbase (se 2 (by rfl) ⟨493632, by rfl⟩ : syracuseStep 1316353 = 987265) (by norm_num)
theorem B1971749 : Blo 1168401 1971749 := bbase (se 4 (by rfl) ⟨184851, by rfl⟩ : syracuseStep 1971749 = 369703) (by norm_num)
theorem B3331621 : Blo 1168401 3331621 := bbase (se 4 (by rfl) ⟨312339, by rfl⟩ : syracuseStep 3331621 = 624679) (by norm_num)
theorem B1316389 : Blo 1168401 1316389 := bbase (se 4 (by rfl) ⟨123411, by rfl⟩ : syracuseStep 1316389 = 246823) (by norm_num)
theorem B1316425 : Blo 1168401 1316425 := bbase (se 2 (by rfl) ⟨493659, by rfl⟩ : syracuseStep 1316425 = 987319) (by norm_num)
theorem B1480285 : Blo 1168401 1480285 := bbase (se 3 (by rfl) ⟨277553, by rfl⟩ : syracuseStep 1480285 = 555107) (by norm_num)
theorem B4437605 : Blo 1168401 4437605 := bbase (se 4 (by rfl) ⟨416025, by rfl⟩ : syracuseStep 4437605 = 832051) (by norm_num)
theorem B2807405 : Blo 1168401 2807405 := bbase (se 3 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 2807405 = 1052777) (by norm_num)
theorem B1316461 : Blo 1168401 1316461 := bbase (se 3 (by rfl) ⟨246836, by rfl⟩ : syracuseStep 1316461 = 493673) (by norm_num)
theorem B1873525 : Blo 1168401 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B1332877 : Blo 1168401 1332877 := bbase (se 3 (by rfl) ⟨249914, by rfl⟩ : syracuseStep 1332877 = 499829) (by norm_num)
theorem B1316497 : Blo 1168401 1316497 := bbase (se 2 (by rfl) ⟨493686, by rfl⟩ : syracuseStep 1316497 = 987373) (by norm_num)
theorem B1971877 : Blo 1168401 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B1316533 : Blo 1168401 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B1873621 : Blo 1168401 1873621 := bbase (se 7 (by rfl) ⟨21956, by rfl⟩ : syracuseStep 1873621 = 43913) (by norm_num)
theorem B1316569 : Blo 1168401 1316569 := bbase (se 2 (by rfl) ⟨493713, by rfl⟩ : syracuseStep 1316569 = 987427) (by norm_num)
theorem B1971965 : Blo 1168401 1971965 := bbase (se 3 (by rfl) ⟨369743, by rfl⟩ : syracuseStep 1971965 = 739487) (by norm_num)
theorem B1316605 : Blo 1168401 1316605 := bbase (se 3 (by rfl) ⟨246863, by rfl⟩ : syracuseStep 1316605 = 493727) (by norm_num)
theorem B4740869 : Blo 1168401 4740869 := bbase (se 4 (by rfl) ⟨444456, by rfl⟩ : syracuseStep 4740869 = 888913) (by norm_num)
theorem B1480457 : Blo 1168401 1480457 := bbase (se 2 (by rfl) ⟨555171, by rfl⟩ : syracuseStep 1480457 = 1110343) (by norm_num)
theorem B2250517 : Blo 1168401 2250517 := bbase (se 6 (by rfl) ⟨52746, by rfl⟩ : syracuseStep 2250517 = 105493) (by norm_num)
theorem B1316641 : Blo 1168401 1316641 := bbase (se 2 (by rfl) ⟨493740, by rfl⟩ : syracuseStep 1316641 = 987481) (by norm_num)
theorem B1480513 : Blo 1168401 1480513 := bbase (se 2 (by rfl) ⟨555192, by rfl⟩ : syracuseStep 1480513 = 1110385) (by norm_num)
theorem B1316677 : Blo 1168401 1316677 := bbase (se 4 (by rfl) ⟨123438, by rfl⟩ : syracuseStep 1316677 = 246877) (by norm_num)
theorem B5920613 : Blo 1168401 5920613 := bbase (se 4 (by rfl) ⟨555057, by rfl⟩ : syracuseStep 5920613 = 1110115) (by norm_num)
theorem B1873781 : Blo 1168401 1873781 := bbase (se 5 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 1873781 = 175667) (by norm_num)
theorem B1972093 : Blo 1168401 1972093 := bbase (se 3 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 1972093 = 739535) (by norm_num)
theorem B3946373 : Blo 1168401 3946373 := bbase (se 4 (by rfl) ⟨369972, by rfl⟩ : syracuseStep 3946373 = 739945) (by norm_num)
theorem B2807693 : Blo 1168401 2807693 := bbase (se 3 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 2807693 = 1052885) (by norm_num)
theorem B1480609 : Blo 1168401 1480609 := bbase (se 2 (by rfl) ⟨555228, by rfl⟩ : syracuseStep 1480609 = 1110457) (by norm_num)
theorem B1972181 : Blo 1168401 1972181 := bbase (se 7 (by rfl) ⟨23111, by rfl⟩ : syracuseStep 1972181 = 46223) (by norm_num)
theorem B1333241 : Blo 1168401 1333241 := bbase (se 2 (by rfl) ⟨499965, by rfl⟩ : syracuseStep 1333241 = 999931) (by norm_num)
theorem B1185817 : Blo 1168401 1185817 := bbase (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) (by norm_num)
theorem B1480781 : Blo 1168401 1480781 := bbase (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) (by norm_num)
theorem B1972309 : Blo 1168401 1972309 := bbase (se 8 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 1972309 = 23113) (by norm_num)
theorem B2136181 : Blo 1168401 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B1480837 : Blo 1168401 1480837 := bbase (se 4 (by rfl) ⟨138828, by rfl⟩ : syracuseStep 1480837 = 277657) (by norm_num)
theorem B1972397 : Blo 1168401 1972397 := bbase (se 3 (by rfl) ⟨369824, by rfl⟩ : syracuseStep 1972397 = 739649) (by norm_num)
theorem B1480933 : Blo 1168401 1480933 := bbase (se 4 (by rfl) ⟨138837, by rfl⟩ : syracuseStep 1480933 = 277675) (by norm_num)
theorem B11229461 : Blo 1168401 11229461 := bbase (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) (by norm_num)
theorem B1972525 : Blo 1168401 1972525 := bbase (se 3 (by rfl) ⟨369848, by rfl⟩ : syracuseStep 1972525 = 739697) (by norm_num)
theorem B3946805 : Blo 1168401 3946805 := bbase (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) (by norm_num)
theorem B1333589 : Blo 1168401 1333589 := bbase (se 10 (by rfl) ⟨1953, by rfl⟩ : syracuseStep 1333589 = 3907) (by norm_num)
theorem B1972613 : Blo 1168401 1972613 := bbase (se 4 (by rfl) ⟨184932, by rfl⟩ : syracuseStep 1972613 = 369865) (by norm_num)
theorem B1898893 : Blo 1168401 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B1481105 : Blo 1168401 1481105 := bbase (se 2 (by rfl) ⟨555414, by rfl⟩ : syracuseStep 1481105 = 1110829) (by norm_num)
theorem B1423765 : Blo 1168401 1423765 := bbase (se 6 (by rfl) ⟨33369, by rfl⟩ : syracuseStep 1423765 = 66739) (by norm_num)
theorem B1481161 : Blo 1168401 1481161 := bbase (se 2 (by rfl) ⟨555435, by rfl⟩ : syracuseStep 1481161 = 1110871) (by norm_num)
theorem B1972741 : Blo 1168401 1972741 := bbase (se 4 (by rfl) ⟨184944, by rfl⟩ : syracuseStep 1972741 = 369889) (by norm_num)
theorem B2849293 : Blo 1168401 2849293 := bbase (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) (by norm_num)
theorem B1481257 : Blo 1168401 1481257 := bbase (se 2 (by rfl) ⟨555471, by rfl⟩ : syracuseStep 1481257 = 1110943) (by norm_num)
theorem B1972829 : Blo 1168401 1972829 := bbase (se 3 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 1972829 = 739811) (by norm_num)
theorem B2497205 : Blo 1168401 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B1333945 : Blo 1168401 1333945 := bbase (se 2 (by rfl) ⟨500229, by rfl⟩ : syracuseStep 1333945 = 1000459) (by norm_num)
theorem B1972957 : Blo 1168401 1972957 := bbase (se 3 (by rfl) ⟨369929, by rfl⟩ : syracuseStep 1972957 = 739859) (by norm_num)
theorem B3947237 : Blo 1168401 3947237 := bbase (se 4 (by rfl) ⟨370053, by rfl⟩ : syracuseStep 3947237 = 740107) (by norm_num)
theorem B2218765 : Blo 1168401 2218765 := bbase (se 3 (by rfl) ⟨416018, by rfl⟩ : syracuseStep 2218765 = 832037) (by norm_num)
theorem B1973045 : Blo 1168401 1973045 := bbase (se 5 (by rfl) ⟨92486, by rfl⟩ : syracuseStep 1973045 = 184973) (by norm_num)
theorem B1334081 : Blo 1168401 1334081 := bbase (se 2 (by rfl) ⟨500280, by rfl⟩ : syracuseStep 1334081 = 1000561) (by norm_num)
theorem B2497349 : Blo 1168401 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B2218909 : Blo 1168401 2218909 := bbase (se 3 (by rfl) ⟨416045, by rfl⟩ : syracuseStep 2218909 = 832091) (by norm_num)
theorem B1579933 : Blo 1168401 1579933 := bbase (se 3 (by rfl) ⟨296237, by rfl⟩ : syracuseStep 1579933 = 592475) (by norm_num)
theorem B1923997 : Blo 1168401 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B1334173 : Blo 1168401 1334173 := bbase (se 3 (by rfl) ⟨250157, by rfl⟩ : syracuseStep 1334173 = 500315) (by norm_num)
theorem B1973173 : Blo 1168401 1973173 := bbase (se 5 (by rfl) ⟨92492, by rfl⟩ : syracuseStep 1973173 = 184985) (by norm_num)
theorem B3161045 : Blo 1168401 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B1334237 : Blo 1168401 1334237 := bbase (se 3 (by rfl) ⟨250169, by rfl⟩ : syracuseStep 1334237 = 500339) (by norm_num)
theorem B1776629 : Blo 1168401 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B1973261 : Blo 1168401 1973261 := bbase (se 3 (by rfl) ⟨369986, by rfl⟩ : syracuseStep 1973261 = 739973) (by norm_num)
theorem B2219069 : Blo 1168401 2219069 := bbase (se 3 (by rfl) ⟨416075, by rfl⟩ : syracuseStep 2219069 = 832151) (by norm_num)
theorem B5921909 : Blo 1168401 5921909 := bbase (se 5 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 5921909 = 555179) (by norm_num)
theorem B2137205 : Blo 1168401 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B1973389 : Blo 1168401 1973389 := bbase (se 3 (by rfl) ⟨370010, by rfl⟩ : syracuseStep 1973389 = 740021) (by norm_num)
theorem B3947669 : Blo 1168401 3947669 := bbase (se 6 (by rfl) ⟨92523, by rfl⟩ : syracuseStep 3947669 = 185047) (by norm_num)
theorem B2497709 : Blo 1168401 2497709 := bbase (se 3 (by rfl) ⟨468320, by rfl⟩ : syracuseStep 2497709 = 936641) (by norm_num)
theorem B2219213 : Blo 1168401 2219213 := bbase (se 3 (by rfl) ⟨416102, by rfl⟩ : syracuseStep 2219213 = 832205) (by norm_num)
theorem B1973477 : Blo 1168401 1973477 := bbase (se 4 (by rfl) ⟨185013, by rfl⟩ : syracuseStep 1973477 = 370027) (by norm_num)
theorem B2628917 : Blo 1168401 2628917 := bbase (se 5 (by rfl) ⟨123230, by rfl⟩ : syracuseStep 2628917 = 246461) (by norm_num)
theorem B1973605 : Blo 1168401 1973605 := bbase (se 4 (by rfl) ⟨185025, by rfl⟩ : syracuseStep 1973605 = 370051) (by norm_num)
theorem B2628989 : Blo 1168401 2628989 := bbase (se 3 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 2628989 = 985871) (by norm_num)
theorem B5619077 : Blo 1168401 5619077 := bbase (se 4 (by rfl) ⟨526788, by rfl⟩ : syracuseStep 5619077 = 1053577) (by norm_num)
theorem B1973693 : Blo 1168401 1973693 := bbase (se 3 (by rfl) ⟨370067, by rfl⟩ : syracuseStep 1973693 = 740135) (by norm_num)
theorem B2629061 : Blo 1168401 2629061 := bbase (se 4 (by rfl) ⟨246474, by rfl⟩ : syracuseStep 2629061 = 492949) (by norm_num)
theorem B2219501 : Blo 1168401 2219501 := bbase (se 3 (by rfl) ⟨416156, by rfl⟩ : syracuseStep 2219501 = 832313) (by norm_num)
theorem B2629133 : Blo 1168401 2629133 := bbase (se 3 (by rfl) ⟨492962, by rfl⟩ : syracuseStep 2629133 = 985925) (by norm_num)
theorem B1752605 : Blo 1168401 1752605 := bbase (se 3 (by rfl) ⟨328613, by rfl⟩ : syracuseStep 1752605 = 657227) (by norm_num)
theorem B1752629 : Blo 1168401 1752629 := bbase (se 5 (by rfl) ⟨82154, by rfl⟩ : syracuseStep 1752629 = 164309) (by norm_num)
theorem B1973821 : Blo 1168401 1973821 := bbase (se 3 (by rfl) ⟨370091, by rfl⟩ : syracuseStep 1973821 = 740183) (by norm_num)
theorem B3948101 : Blo 1168401 3948101 := bbase (se 4 (by rfl) ⟨370134, by rfl⟩ : syracuseStep 3948101 = 740269) (by norm_num)
theorem B1752653 : Blo 1168401 1752653 := bbase (se 3 (by rfl) ⟨328622, by rfl⟩ : syracuseStep 1752653 = 657245) (by norm_num)
theorem B2629205 : Blo 1168401 2629205 := bbase (se 8 (by rfl) ⟨15405, by rfl⟩ : syracuseStep 2629205 = 30811) (by norm_num)
theorem B1752677 : Blo 1168401 1752677 := bbase (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) (by norm_num)
theorem B1752701 : Blo 1168401 1752701 := bbase (se 3 (by rfl) ⟨328631, by rfl⟩ : syracuseStep 1752701 = 657263) (by norm_num)
theorem B2219653 : Blo 1168401 2219653 := bbase (se 4 (by rfl) ⟨208092, by rfl⟩ : syracuseStep 2219653 = 416185) (by norm_num)
theorem B1752725 : Blo 1168401 1752725 := bbase (se 6 (by rfl) ⟨41079, by rfl⟩ : syracuseStep 1752725 = 82159) (by norm_num)
theorem B1973909 : Blo 1168401 1973909 := bbase (se 6 (by rfl) ⟨46263, by rfl⟩ : syracuseStep 1973909 = 92527) (by norm_num)
theorem B2629277 : Blo 1168401 2629277 := bbase (se 3 (by rfl) ⟨492989, by rfl⟩ : syracuseStep 2629277 = 985979) (by norm_num)
theorem B4439717 : Blo 1168401 4439717 := bbase (se 4 (by rfl) ⟨416223, by rfl⟩ : syracuseStep 4439717 = 832447) (by norm_num)
theorem B1752749 : Blo 1168401 1752749 := bbase (se 3 (by rfl) ⟨328640, by rfl⟩ : syracuseStep 1752749 = 657281) (by norm_num)
theorem B1752773 : Blo 1168401 1752773 := bbase (se 4 (by rfl) ⟨164322, by rfl⟩ : syracuseStep 1752773 = 328645) (by norm_num)
theorem B1752797 : Blo 1168401 1752797 := bbase (se 3 (by rfl) ⟨328649, by rfl⟩ : syracuseStep 1752797 = 657299) (by norm_num)
theorem B2629349 : Blo 1168401 2629349 := bbase (se 4 (by rfl) ⟨246501, by rfl⟩ : syracuseStep 2629349 = 493003) (by norm_num)
theorem B1351405 : Blo 1168401 1351405 := bbase (se 3 (by rfl) ⟨253388, by rfl⟩ : syracuseStep 1351405 = 506777) (by norm_num)
theorem B1752821 : Blo 1168401 1752821 := bbase (se 5 (by rfl) ⟨82163, by rfl⟩ : syracuseStep 1752821 = 164327) (by norm_num)
theorem B1752845 : Blo 1168401 1752845 := bbase (se 3 (by rfl) ⟨328658, by rfl⟩ : syracuseStep 1752845 = 657317) (by norm_num)
theorem B1974037 : Blo 1168401 1974037 := bbase (se 6 (by rfl) ⟨46266, by rfl⟩ : syracuseStep 1974037 = 92533) (by norm_num)
theorem B4996885 : Blo 1168401 4996885 := bbase (se 6 (by rfl) ⟨117114, by rfl⟩ : syracuseStep 4996885 = 234229) (by norm_num)
theorem B1752869 : Blo 1168401 1752869 := bbase (se 4 (by rfl) ⟨164331, by rfl⟩ : syracuseStep 1752869 = 328663) (by norm_num)
theorem B2629421 : Blo 1168401 2629421 := bbase (se 3 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 2629421 = 986033) (by norm_num)
theorem B1752893 : Blo 1168401 1752893 := bbase (se 3 (by rfl) ⟨328667, by rfl⟩ : syracuseStep 1752893 = 657335) (by norm_num)
theorem B1752917 : Blo 1168401 1752917 := bbase (se 9 (by rfl) ⟨5135, by rfl⟩ : syracuseStep 1752917 = 10271) (by norm_num)
theorem B1752941 : Blo 1168401 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B1974125 : Blo 1168401 1974125 := bbase (se 3 (by rfl) ⟨370148, by rfl⟩ : syracuseStep 1974125 = 740297) (by norm_num)
theorem B2629493 : Blo 1168401 2629493 := bbase (se 5 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 2629493 = 246515) (by norm_num)
theorem B6004597 : Blo 1168401 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B1752965 : Blo 1168401 1752965 := bbase (se 4 (by rfl) ⟨164340, by rfl⟩ : syracuseStep 1752965 = 328681) (by norm_num)
theorem B2809741 : Blo 1168401 2809741 := bbase (se 3 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 2809741 = 1053653) (by norm_num)
theorem B1752989 : Blo 1168401 1752989 := bbase (se 3 (by rfl) ⟨328685, by rfl⟩ : syracuseStep 1752989 = 657371) (by norm_num)
theorem B1753013 : Blo 1168401 1753013 := bbase (se 5 (by rfl) ⟨82172, by rfl⟩ : syracuseStep 1753013 = 164345) (by norm_num)
theorem B2219957 : Blo 1168401 2219957 := bbase (se 5 (by rfl) ⟨104060, by rfl⟩ : syracuseStep 2219957 = 208121) (by norm_num)
theorem B2629565 : Blo 1168401 2629565 := bbase (se 3 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 2629565 = 986087) (by norm_num)
theorem B4440005 : Blo 1168401 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B1753037 : Blo 1168401 1753037 := bbase (se 3 (by rfl) ⟨328694, by rfl⟩ : syracuseStep 1753037 = 657389) (by norm_num)
theorem B6660053 : Blo 1168401 6660053 := bbase (se 7 (by rfl) ⟨78047, by rfl⟩ : syracuseStep 6660053 = 156095) (by norm_num)
theorem B1753061 : Blo 1168401 1753061 := bbase (se 4 (by rfl) ⟨164349, by rfl⟩ : syracuseStep 1753061 = 328699) (by norm_num)
theorem B1974253 : Blo 1168401 1974253 := bbase (se 3 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 1974253 = 740345) (by norm_num)
theorem B3948533 : Blo 1168401 3948533 := bbase (se 5 (by rfl) ⟨185087, by rfl⟩ : syracuseStep 3948533 = 370175) (by norm_num)
theorem B11247605 : Blo 1168401 11247605 := bbase (se 5 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 11247605 = 1054463) (by norm_num)
theorem B1753085 : Blo 1168401 1753085 := bbase (se 3 (by rfl) ⟨328703, by rfl⟩ : syracuseStep 1753085 = 657407) (by norm_num)
theorem B1753091 : Blo 1168401 1753091 := bstep (se 1 (by rfl) ⟨1314818, by rfl⟩ : syracuseStep 1753091 = 2629637) B2629637
theorem B1753121 : Blo 1168401 1753121 := bstep (se 2 (by rfl) ⟨657420, by rfl⟩ : syracuseStep 1753121 = 1314841) B1314841
theorem B1581089 : Blo 1168401 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B1974307 : Blo 1168401 1974307 := bstep (se 1 (by rfl) ⟨1480730, by rfl⟩ : syracuseStep 1974307 = 2961461) B2961461
theorem B1753139 : Blo 1168401 1753139 := bstep (se 1 (by rfl) ⟨1314854, by rfl⟩ : syracuseStep 1753139 = 2629709) B2629709
theorem B1753169 : Blo 1168401 1753169 := bstep (se 2 (by rfl) ⟨657438, by rfl⟩ : syracuseStep 1753169 = 1314877) B1314877
theorem B1499219 : Blo 1168401 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B1753187 : Blo 1168401 1753187 := bstep (se 1 (by rfl) ⟨1314890, by rfl⟩ : syracuseStep 1753187 = 2629781) B2629781
theorem B2629745 : Blo 1168401 2629745 := bstep (se 2 (by rfl) ⟨986154, by rfl⟩ : syracuseStep 2629745 = 1972309) B1972309
theorem B1753217 : Blo 1168401 1753217 := bstep (se 2 (by rfl) ⟨657456, by rfl⟩ : syracuseStep 1753217 = 1314913) B1314913
theorem B2629763 : Blo 1168401 2629763 := bstep (se 1 (by rfl) ⟨1972322, by rfl⟩ : syracuseStep 2629763 = 3944645) B3944645
theorem B1753235 : Blo 1168401 1753235 := bstep (se 1 (by rfl) ⟨1314926, by rfl⟩ : syracuseStep 1753235 = 2629853) B2629853
theorem B1753265 : Blo 1168401 1753265 := bstep (se 2 (by rfl) ⟨657474, by rfl⟩ : syracuseStep 1753265 = 1314949) B1314949
theorem B1974449 : Blo 1168401 1974449 := bstep (se 2 (by rfl) ⟨740418, by rfl⟩ : syracuseStep 1974449 = 1480837) B1480837
theorem B1753283 : Blo 1168401 1753283 := bstep (se 1 (by rfl) ⟨1314962, by rfl⟩ : syracuseStep 1753283 = 2629925) B2629925
theorem B3948749 : Blo 1168401 3948749 := bstep (se 3 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 3948749 = 1480781) B1480781
theorem B1753313 : Blo 1168401 1753313 := bstep (se 2 (by rfl) ⟨657492, by rfl⟩ : syracuseStep 1753313 = 1314985) B1314985
theorem B5923043 : Blo 1168401 5923043 := bstep (se 1 (by rfl) ⟨4442282, by rfl⟩ : syracuseStep 5923043 = 8884565) B8884565
theorem B1753331 : Blo 1168401 1753331 := bstep (se 1 (by rfl) ⟨1314998, by rfl⟩ : syracuseStep 1753331 = 2629997) B2629997
theorem B3948803 : Blo 1168401 3948803 := bstep (se 1 (by rfl) ⟨2961602, by rfl⟩ : syracuseStep 3948803 = 5923205) B5923205
theorem B1753361 : Blo 1168401 1753361 := bstep (se 2 (by rfl) ⟨657510, by rfl⟩ : syracuseStep 1753361 = 1315021) B1315021
theorem B1753379 : Blo 1168401 1753379 := bstep (se 1 (by rfl) ⟨1315034, by rfl⟩ : syracuseStep 1753379 = 2630069) B2630069
theorem B1974577 : Blo 1168401 1974577 := bstep (se 2 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 1974577 = 1480933) B1480933
theorem B1753409 : Blo 1168401 1753409 := bstep (se 2 (by rfl) ⟨657528, by rfl⟩ : syracuseStep 1753409 = 1315057) B1315057
theorem B1753427 : Blo 1168401 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B1974611 : Blo 1168401 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B1753457 : Blo 1168401 1753457 := bstep (se 2 (by rfl) ⟨657546, by rfl⟩ : syracuseStep 1753457 = 1315093) B1315093
theorem B1753475 : Blo 1168401 1753475 := bstep (se 1 (by rfl) ⟨1315106, by rfl⟩ : syracuseStep 1753475 = 2630213) B2630213
theorem B2630033 : Blo 1168401 2630033 := bstep (se 2 (by rfl) ⟨986262, by rfl⟩ : syracuseStep 2630033 = 1972525) B1972525
theorem B1753505 : Blo 1168401 1753505 := bstep (se 2 (by rfl) ⟨657564, by rfl⟩ : syracuseStep 1753505 = 1315129) B1315129
theorem B2630051 : Blo 1168401 2630051 := bstep (se 1 (by rfl) ⟨1972538, by rfl⟩ : syracuseStep 2630051 = 3945077) B3945077
theorem B1753523 : Blo 1168401 1753523 := bstep (se 1 (by rfl) ⟨1315142, by rfl⟩ : syracuseStep 1753523 = 2630285) B2630285
theorem B1753553 : Blo 1168401 1753553 := bstep (se 2 (by rfl) ⟨657582, by rfl⟩ : syracuseStep 1753553 = 1315165) B1315165
theorem B1974739 : Blo 1168401 1974739 := bstep (se 1 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 1974739 = 2962109) B2962109
theorem B1753571 : Blo 1168401 1753571 := bstep (se 1 (by rfl) ⟨1315178, by rfl⟩ : syracuseStep 1753571 = 2630357) B2630357
theorem B1753601 : Blo 1168401 1753601 := bstep (se 2 (by rfl) ⟨657600, by rfl⟩ : syracuseStep 1753601 = 1315201) B1315201
theorem B3949073 : Blo 1168401 3949073 := bstep (se 2 (by rfl) ⟨1480902, by rfl⟩ : syracuseStep 3949073 = 2961805) B2961805
theorem B1753619 : Blo 1168401 1753619 := bstep (se 1 (by rfl) ⟨1315214, by rfl⟩ : syracuseStep 1753619 = 2630429) B2630429
theorem B1753649 : Blo 1168401 1753649 := bstep (se 2 (by rfl) ⟨657618, by rfl⟩ : syracuseStep 1753649 = 1315237) B1315237
theorem B1753667 : Blo 1168401 1753667 := bstep (se 1 (by rfl) ⟨1315250, by rfl⟩ : syracuseStep 1753667 = 2630501) B2630501
theorem B2220625 : Blo 1168401 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B1753697 : Blo 1168401 1753697 := bstep (se 2 (by rfl) ⟨657636, by rfl⟩ : syracuseStep 1753697 = 1315273) B1315273
theorem B1974881 : Blo 1168401 1974881 := bstep (se 2 (by rfl) ⟨740580, by rfl⟩ : syracuseStep 1974881 = 1481161) B1481161
theorem B14615153 : Blo 1168401 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B4440689 : Blo 1168401 4440689 := bstep (se 2 (by rfl) ⟨1665258, by rfl⟩ : syracuseStep 4440689 = 3330517) B3330517
theorem B1753715 : Blo 1168401 1753715 := bstep (se 1 (by rfl) ⟨1315286, by rfl⟩ : syracuseStep 1753715 = 2630573) B2630573
theorem B11231885 : Blo 1168401 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B1753745 : Blo 1168401 1753745 := bstep (se 2 (by rfl) ⟨657654, by rfl⟩ : syracuseStep 1753745 = 1315309) B1315309
theorem B1753763 : Blo 1168401 1753763 := bstep (se 1 (by rfl) ⟨1315322, by rfl⟩ : syracuseStep 1753763 = 2630645) B2630645
theorem B1688227 : Blo 1168401 1688227 := bstep (se 1 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 1688227 = 2532341) B2532341
theorem B2630321 : Blo 1168401 2630321 := bstep (se 2 (by rfl) ⟨986370, by rfl⟩ : syracuseStep 2630321 = 1972741) B1972741
theorem B1663681 : Blo 1168401 1663681 := bstep (se 2 (by rfl) ⟨623880, by rfl⟩ : syracuseStep 1663681 = 1247761) B1247761
theorem B1753793 : Blo 1168401 1753793 := bstep (se 2 (by rfl) ⟨657672, by rfl⟩ : syracuseStep 1753793 = 1315345) B1315345
theorem B2630339 : Blo 1168401 2630339 := bstep (se 1 (by rfl) ⟨1972754, by rfl⟩ : syracuseStep 2630339 = 3945509) B3945509
theorem B1753811 : Blo 1168401 1753811 := bstep (se 1 (by rfl) ⟨1315358, by rfl⟩ : syracuseStep 1753811 = 2630717) B2630717
theorem B1975009 : Blo 1168401 1975009 := bstep (se 2 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 1975009 = 1481257) B1481257
theorem B1753841 : Blo 1168401 1753841 := bstep (se 2 (by rfl) ⟨657690, by rfl⟩ : syracuseStep 1753841 = 1315381) B1315381
theorem B1753859 : Blo 1168401 1753859 := bstep (se 1 (by rfl) ⟨1315394, by rfl⟩ : syracuseStep 1753859 = 2630789) B2630789
theorem B2499331 : Blo 1168401 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B1975043 : Blo 1168401 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B1753889 : Blo 1168401 1753889 := bstep (se 2 (by rfl) ⟨657708, by rfl⟩ : syracuseStep 1753889 = 1315417) B1315417
theorem B1753907 : Blo 1168401 1753907 := bstep (se 1 (by rfl) ⟨1315430, by rfl⟩ : syracuseStep 1753907 = 2630861) B2630861
theorem B3744589 : Blo 1168401 3744589 := bstep (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) B1404221
theorem B1753937 : Blo 1168401 1753937 := bstep (se 2 (by rfl) ⟨657726, by rfl⟩ : syracuseStep 1753937 = 1315453) B1315453
theorem B3203921 : Blo 1168401 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B307635029 : Blo 1168401 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B1753955 : Blo 1168401 1753955 := bstep (se 1 (by rfl) ⟨1315466, by rfl⟩ : syracuseStep 1753955 = 2630933) B2630933
theorem B1778531 : Blo 1168401 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B3162979 : Blo 1168401 3162979 := bstep (se 1 (by rfl) ⟨2372234, by rfl⟩ : syracuseStep 3162979 = 4744469) B4744469
theorem B1753985 : Blo 1168401 1753985 := bstep (se 2 (by rfl) ⟨657744, by rfl⟩ : syracuseStep 1753985 = 1315489) B1315489
theorem B3556237 : Blo 1168401 3556237 := bstep (se 3 (by rfl) ⟨666794, by rfl⟩ : syracuseStep 3556237 = 1333589) B1333589
theorem B1754003 : Blo 1168401 1754003 := bstep (se 1 (by rfl) ⟨1315502, by rfl⟩ : syracuseStep 1754003 = 2631005) B2631005
theorem B1778593 : Blo 1168401 1778593 := bstep (se 2 (by rfl) ⟨666972, by rfl⟩ : syracuseStep 1778593 = 1333945) B1333945
theorem B3163043 : Blo 1168401 3163043 := bstep (se 1 (by rfl) ⟨2372282, by rfl⟩ : syracuseStep 3163043 = 4744565) B4744565
theorem B1754033 : Blo 1168401 1754033 := bstep (se 2 (by rfl) ⟨657762, by rfl⟩ : syracuseStep 1754033 = 1315525) B1315525
theorem B1754051 : Blo 1168401 1754051 := bstep (se 1 (by rfl) ⟨1315538, by rfl⟩ : syracuseStep 1754051 = 2631077) B2631077
theorem B8872901 : Blo 1168401 8872901 := bstep (se 4 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 8872901 = 1663669) B1663669
theorem B2630609 : Blo 1168401 2630609 := bstep (se 2 (by rfl) ⟨986478, by rfl⟩ : syracuseStep 2630609 = 1972957) B1972957
theorem B1754081 : Blo 1168401 1754081 := bstep (se 2 (by rfl) ⟨657780, by rfl⟩ : syracuseStep 1754081 = 1315561) B1315561
theorem B2630627 : Blo 1168401 2630627 := bstep (se 1 (by rfl) ⟨1972970, by rfl⟩ : syracuseStep 2630627 = 3945941) B3945941
theorem B4998115 : Blo 1168401 4998115 := bstep (se 1 (by rfl) ⟨3748586, by rfl⟩ : syracuseStep 4998115 = 7497173) B7497173
theorem B1754099 : Blo 1168401 1754099 := bstep (se 1 (by rfl) ⟨1315574, by rfl⟩ : syracuseStep 1754099 = 2631149) B2631149
theorem B5923853 : Blo 1168401 5923853 := bstep (se 3 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 5923853 = 2221445) B2221445
theorem B2958353 : Blo 1168401 2958353 := bstep (se 2 (by rfl) ⟨1109382, by rfl⟩ : syracuseStep 2958353 = 2218765) B2218765
theorem B1754129 : Blo 1168401 1754129 := bstep (se 2 (by rfl) ⟨657798, by rfl⟩ : syracuseStep 1754129 = 1315597) B1315597
theorem B1754147 : Blo 1168401 1754147 := bstep (se 1 (by rfl) ⟨1315610, by rfl⟩ : syracuseStep 1754147 = 2631221) B2631221
theorem B3949613 : Blo 1168401 3949613 := bstep (se 3 (by rfl) ⟨740552, by rfl⟩ : syracuseStep 3949613 = 1481105) B1481105
theorem B1754177 : Blo 1168401 1754177 := bstep (se 2 (by rfl) ⟨657816, by rfl⟩ : syracuseStep 1754177 = 1315633) B1315633
theorem B2958403 : Blo 1168401 2958403 := bstep (se 1 (by rfl) ⟨2218802, by rfl⟩ : syracuseStep 2958403 = 4437605) B4437605
theorem B1754195 : Blo 1168401 1754195 := bstep (se 1 (by rfl) ⟨1315646, by rfl⟩ : syracuseStep 1754195 = 2631293) B2631293
theorem B3949667 : Blo 1168401 3949667 := bstep (se 1 (by rfl) ⟨2962250, by rfl⟩ : syracuseStep 3949667 = 5924501) B5924501
theorem B1754225 : Blo 1168401 1754225 := bstep (se 2 (by rfl) ⟨657834, by rfl⟩ : syracuseStep 1754225 = 1315669) B1315669
theorem B1754243 : Blo 1168401 1754243 := bstep (se 1 (by rfl) ⟨1315682, by rfl⟩ : syracuseStep 1754243 = 2631365) B2631365
theorem B1754273 : Blo 1168401 1754273 := bstep (se 2 (by rfl) ⟨657852, by rfl⟩ : syracuseStep 1754273 = 1315705) B1315705
theorem B1754291 : Blo 1168401 1754291 := bstep (se 1 (by rfl) ⟨1315718, by rfl⟩ : syracuseStep 1754291 = 2631437) B2631437
theorem B2958545 : Blo 1168401 2958545 := bstep (se 2 (by rfl) ⟨1109454, by rfl⟩ : syracuseStep 2958545 = 2218909) B2218909
theorem B2106577 : Blo 1168401 2106577 := bstep (se 2 (by rfl) ⟨789966, by rfl⟩ : syracuseStep 2106577 = 1579933) B1579933
theorem B2565329 : Blo 1168401 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B1754321 : Blo 1168401 1754321 := bstep (se 2 (by rfl) ⟨657870, by rfl⟩ : syracuseStep 1754321 = 1315741) B1315741
theorem B1778897 : Blo 1168401 1778897 := bstep (se 2 (by rfl) ⟨667086, by rfl⟩ : syracuseStep 1778897 = 1334173) B1334173
theorem B1754339 : Blo 1168401 1754339 := bstep (se 1 (by rfl) ⟨1315754, by rfl⟩ : syracuseStep 1754339 = 2631509) B2631509
theorem B2630897 : Blo 1168401 2630897 := bstep (se 2 (by rfl) ⟨986586, by rfl⟩ : syracuseStep 2630897 = 1973173) B1973173
theorem B7496945 : Blo 1168401 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B1754369 : Blo 1168401 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B2630915 : Blo 1168401 2630915 := bstep (se 1 (by rfl) ⟨1973186, by rfl⟩ : syracuseStep 2630915 = 3946373) B3946373
theorem B1664273 : Blo 1168401 1664273 := bstep (se 2 (by rfl) ⟨624102, by rfl⟩ : syracuseStep 1664273 = 1248205) B1248205
theorem B1754387 : Blo 1168401 1754387 := bstep (se 1 (by rfl) ⟨1315790, by rfl⟩ : syracuseStep 1754387 = 2631581) B2631581
theorem B1754417 : Blo 1168401 1754417 := bstep (se 2 (by rfl) ⟨657906, by rfl⟩ : syracuseStep 1754417 = 1315813) B1315813
theorem B1754435 : Blo 1168401 1754435 := bstep (se 1 (by rfl) ⟨1315826, by rfl⟩ : syracuseStep 1754435 = 2631653) B2631653
theorem B1754465 : Blo 1168401 1754465 := bstep (se 2 (by rfl) ⟨657924, by rfl⟩ : syracuseStep 1754465 = 1315849) B1315849
theorem B3949937 : Blo 1168401 3949937 := bstep (se 2 (by rfl) ⟨1481226, by rfl⟩ : syracuseStep 3949937 = 2962453) B2962453
theorem B1754483 : Blo 1168401 1754483 := bstep (se 1 (by rfl) ⟨1315862, by rfl⟩ : syracuseStep 1754483 = 2631725) B2631725
theorem B1754513 : Blo 1168401 1754513 := bstep (se 2 (by rfl) ⟨657942, by rfl⟩ : syracuseStep 1754513 = 1315885) B1315885
theorem B1754531 : Blo 1168401 1754531 := bstep (se 1 (by rfl) ⟨1315898, by rfl⟩ : syracuseStep 1754531 = 2631797) B2631797
theorem B1754561 : Blo 1168401 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1754579 : Blo 1168401 1754579 := bstep (se 1 (by rfl) ⟨1315934, by rfl⟩ : syracuseStep 1754579 = 2631869) B2631869
theorem B8881649 : Blo 1168401 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B1754609 : Blo 1168401 1754609 := bstep (se 2 (by rfl) ⟨657978, by rfl⟩ : syracuseStep 1754609 = 1315957) B1315957
theorem B3556867 : Blo 1168401 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B1754627 : Blo 1168401 1754627 := bstep (se 1 (by rfl) ⟨1315970, by rfl⟩ : syracuseStep 1754627 = 2631941) B2631941
theorem B2631185 : Blo 1168401 2631185 := bstep (se 2 (by rfl) ⟨986694, by rfl⟩ : syracuseStep 2631185 = 1973389) B1973389
theorem B1754657 : Blo 1168401 1754657 := bstep (se 2 (by rfl) ⟨657996, by rfl⟩ : syracuseStep 1754657 = 1315993) B1315993
theorem B2631203 : Blo 1168401 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B1754675 : Blo 1168401 1754675 := bstep (se 1 (by rfl) ⟨1316006, by rfl⟩ : syracuseStep 1754675 = 2632013) B2632013
theorem B1754705 : Blo 1168401 1754705 := bstep (se 2 (by rfl) ⟨658014, by rfl⟩ : syracuseStep 1754705 = 1316029) B1316029
theorem B1754723 : Blo 1168401 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B3327601 : Blo 1168401 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B2221681 : Blo 1168401 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B1754753 : Blo 1168401 1754753 := bstep (se 2 (by rfl) ⟨658032, by rfl⟩ : syracuseStep 1754753 = 1316065) B1316065
theorem B1754771 : Blo 1168401 1754771 := bstep (se 1 (by rfl) ⟨1316078, by rfl⟩ : syracuseStep 1754771 = 2632157) B2632157
theorem B1754801 : Blo 1168401 1754801 := bstep (se 2 (by rfl) ⟨658050, by rfl⟩ : syracuseStep 1754801 = 1316101) B1316101
theorem B1754819 : Blo 1168401 1754819 := bstep (se 1 (by rfl) ⟨1316114, by rfl⟩ : syracuseStep 1754819 = 2632229) B2632229
theorem B1754849 : Blo 1168401 1754849 := bstep (se 2 (by rfl) ⟨658068, by rfl⟩ : syracuseStep 1754849 = 1316137) B1316137
theorem B5916401 : Blo 1168401 5916401 := bstep (se 2 (by rfl) ⟨2218650, by rfl⟩ : syracuseStep 5916401 = 4437301) B4437301
theorem B1754867 : Blo 1168401 1754867 := bstep (se 1 (by rfl) ⟨1316150, by rfl⟩ : syracuseStep 1754867 = 2632301) B2632301
theorem B2000657 : Blo 1168401 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B1754897 : Blo 1168401 1754897 := bstep (se 2 (by rfl) ⟨658086, by rfl⟩ : syracuseStep 1754897 = 1316173) B1316173
theorem B1664803 : Blo 1168401 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B1754915 : Blo 1168401 1754915 := bstep (se 1 (by rfl) ⟨1316186, by rfl⟩ : syracuseStep 1754915 = 2632373) B2632373
theorem B2631473 : Blo 1168401 2631473 := bstep (se 2 (by rfl) ⟨986802, by rfl⟩ : syracuseStep 2631473 = 1973605) B1973605
theorem B1754945 : Blo 1168401 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B2631491 : Blo 1168401 2631491 := bstep (se 1 (by rfl) ⟨1973618, by rfl⟩ : syracuseStep 2631491 = 3947237) B3947237
theorem B1754963 : Blo 1168401 1754963 := bstep (se 1 (by rfl) ⟨1316222, by rfl⟩ : syracuseStep 1754963 = 2632445) B2632445
theorem B1754993 : Blo 1168401 1754993 := bstep (se 2 (by rfl) ⟨658122, by rfl⟩ : syracuseStep 1754993 = 1316245) B1316245
theorem B3327875 : Blo 1168401 3327875 := bstep (se 1 (by rfl) ⟨2495906, by rfl⟩ : syracuseStep 3327875 = 4991813) B4991813
theorem B1755011 : Blo 1168401 1755011 := bstep (se 1 (by rfl) ⟨1316258, by rfl⟩ : syracuseStep 1755011 = 2632517) B2632517
theorem B1755041 : Blo 1168401 1755041 := bstep (se 2 (by rfl) ⟨658140, by rfl⟩ : syracuseStep 1755041 = 1316281) B1316281
theorem B1755059 : Blo 1168401 1755059 := bstep (se 1 (by rfl) ⟨1316294, by rfl⟩ : syracuseStep 1755059 = 2632589) B2632589
theorem B1755089 : Blo 1168401 1755089 := bstep (se 2 (by rfl) ⟨658158, by rfl⟩ : syracuseStep 1755089 = 1316317) B1316317
theorem B2107363 : Blo 1168401 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B1755107 : Blo 1168401 1755107 := bstep (se 1 (by rfl) ⟨1316330, by rfl⟩ : syracuseStep 1755107 = 2632661) B2632661
theorem B1755137 : Blo 1168401 1755137 := bstep (se 2 (by rfl) ⟨658176, by rfl⟩ : syracuseStep 1755137 = 1316353) B1316353
theorem B12642317 : Blo 1168401 12642317 := bstep (se 3 (by rfl) ⟨2370434, by rfl⟩ : syracuseStep 12642317 = 4740869) B4740869
theorem B1755155 : Blo 1168401 1755155 := bstep (se 1 (by rfl) ⟨1316366, by rfl⟩ : syracuseStep 1755155 = 2632733) B2632733
theorem B4442147 : Blo 1168401 4442147 := bstep (se 1 (by rfl) ⟨3331610, by rfl⟩ : syracuseStep 4442147 = 6663221) B6663221
theorem B4442161 : Blo 1168401 4442161 := bstep (se 2 (by rfl) ⟨1665810, by rfl⟩ : syracuseStep 4442161 = 3331621) B3331621
theorem B1755185 : Blo 1168401 1755185 := bstep (se 2 (by rfl) ⟨658194, by rfl⟩ : syracuseStep 1755185 = 1316389) B1316389
theorem B13510709 : Blo 1168401 13510709 := bstep (se 5 (by rfl) ⟨633314, by rfl⟩ : syracuseStep 13510709 = 1266629) B1266629
theorem B3328067 : Blo 1168401 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B1755203 : Blo 1168401 1755203 := bstep (se 1 (by rfl) ⟨1316402, by rfl⟩ : syracuseStep 1755203 = 2632805) B2632805
theorem B12634181 : Blo 1168401 12634181 := bstep (se 4 (by rfl) ⟨1184454, by rfl⟩ : syracuseStep 12634181 = 2368909) B2368909
theorem B10127429 : Blo 1168401 10127429 := bstep (se 4 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 10127429 = 1898893) B1898893
theorem B2631761 : Blo 1168401 2631761 := bstep (se 2 (by rfl) ⟨986910, by rfl⟩ : syracuseStep 2631761 = 1973821) B1973821
theorem B1755233 : Blo 1168401 1755233 := bstep (se 2 (by rfl) ⟨658212, by rfl⟩ : syracuseStep 1755233 = 1316425) B1316425
theorem B2631779 : Blo 1168401 2631779 := bstep (se 1 (by rfl) ⟨1973834, by rfl⟩ : syracuseStep 2631779 = 3947669) B3947669
theorem B1665139 : Blo 1168401 1665139 := bstep (se 1 (by rfl) ⟨1248854, by rfl⟩ : syracuseStep 1665139 = 2497709) B2497709
theorem B1755251 : Blo 1168401 1755251 := bstep (se 1 (by rfl) ⟨1316438, by rfl⟩ : syracuseStep 1755251 = 2632877) B2632877
theorem B1755281 : Blo 1168401 1755281 := bstep (se 2 (by rfl) ⟨658230, by rfl⟩ : syracuseStep 1755281 = 1316461) B1316461
theorem B1755299 : Blo 1168401 1755299 := bstep (se 1 (by rfl) ⟨1316474, by rfl⟩ : syracuseStep 1755299 = 2632949) B2632949
theorem B3557549 : Blo 1168401 3557549 := bstep (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) B1334081
theorem B2959537 : Blo 1168401 2959537 := bstep (se 2 (by rfl) ⟨1109826, by rfl⟩ : syracuseStep 2959537 = 2219653) B2219653
theorem B1755329 : Blo 1168401 1755329 := bstep (se 2 (by rfl) ⟨658248, by rfl⟩ : syracuseStep 1755329 = 1316497) B1316497
theorem B1755347 : Blo 1168401 1755347 := bstep (se 1 (by rfl) ⟨1316510, by rfl⟩ : syracuseStep 1755347 = 2633021) B2633021
theorem B1755377 : Blo 1168401 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B3746051 : Blo 1168401 3746051 := bstep (se 1 (by rfl) ⟨2809538, by rfl⟩ : syracuseStep 3746051 = 5619077) B5619077
theorem B1755395 : Blo 1168401 1755395 := bstep (se 1 (by rfl) ⟨1316546, by rfl⟩ : syracuseStep 1755395 = 2633093) B2633093
theorem B1755425 : Blo 1168401 1755425 := bstep (se 2 (by rfl) ⟨658284, by rfl⟩ : syracuseStep 1755425 = 1316569) B1316569
theorem B1755443 : Blo 1168401 1755443 := bstep (se 1 (by rfl) ⟨1316582, by rfl⟩ : syracuseStep 1755443 = 2633165) B2633165
theorem B1755473 : Blo 1168401 1755473 := bstep (se 2 (by rfl) ⟨658302, by rfl⟩ : syracuseStep 1755473 = 1316605) B1316605
theorem B1755491 : Blo 1168401 1755491 := bstep (se 1 (by rfl) ⟨1316618, by rfl⟩ : syracuseStep 1755491 = 2633237) B2633237
theorem B3000689 : Blo 1168401 3000689 := bstep (se 2 (by rfl) ⟨1125258, by rfl⟩ : syracuseStep 3000689 = 2250517) B2250517
theorem B2632049 : Blo 1168401 2632049 := bstep (se 2 (by rfl) ⟨987018, by rfl⟩ : syracuseStep 2632049 = 1974037) B1974037
theorem B6662513 : Blo 1168401 6662513 := bstep (se 2 (by rfl) ⟨2498442, by rfl⟩ : syracuseStep 6662513 = 4996885) B4996885
theorem B1755521 : Blo 1168401 1755521 := bstep (se 2 (by rfl) ⟨658320, by rfl⟩ : syracuseStep 1755521 = 1316641) B1316641
theorem B2632067 : Blo 1168401 2632067 := bstep (se 1 (by rfl) ⟨1974050, by rfl⟩ : syracuseStep 2632067 = 3948101) B3948101
theorem B1755539 : Blo 1168401 1755539 := bstep (se 1 (by rfl) ⟨1316654, by rfl⟩ : syracuseStep 1755539 = 2633309) B2633309
theorem B1755569 : Blo 1168401 1755569 := bstep (se 2 (by rfl) ⟨658338, by rfl⟩ : syracuseStep 1755569 = 1316677) B1316677
theorem B2959811 : Blo 1168401 2959811 := bstep (se 1 (by rfl) ⟨2219858, by rfl⟩ : syracuseStep 2959811 = 4439717) B4439717
theorem B1755587 : Blo 1168401 1755587 := bstep (se 1 (by rfl) ⟨1316690, by rfl⟩ : syracuseStep 1755587 = 2633381) B2633381
theorem B8006129 : Blo 1168401 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B3746321 : Blo 1168401 3746321 := bstep (se 2 (by rfl) ⟨1404870, by rfl⟩ : syracuseStep 3746321 = 2809741) B2809741
theorem B3557965 : Blo 1168401 3557965 := bstep (se 3 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 3557965 = 1334237) B1334237
theorem B2960003 : Blo 1168401 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B2632337 : Blo 1168401 2632337 := bstep (se 2 (by rfl) ⟨987126, by rfl⟩ : syracuseStep 2632337 = 1974253) B1974253
theorem B1665697 : Blo 1168401 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B2632355 : Blo 1168401 2632355 := bstep (se 1 (by rfl) ⟨1974266, by rfl⟩ : syracuseStep 2632355 = 3948533) B3948533
theorem B7498403 : Blo 1168401 7498403 := bstep (se 1 (by rfl) ⟨5623802, by rfl⟩ : syracuseStep 7498403 = 11247605) B11247605
theorem B1247923 : Blo 1168401 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1665731 : Blo 1168401 1665731 := bstep (se 1 (by rfl) ⟨1249298, by rfl⟩ : syracuseStep 1665731 = 2498597) B2498597
theorem B5999345 : Blo 1168401 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B2665315 : Blo 1168401 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B3328877 : Blo 1168401 3328877 := bstep (se 3 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 3328877 = 1248329) B1248329
theorem B1403779 : Blo 1168401 1403779 := bstep (se 1 (by rfl) ⟨1052834, by rfl⟩ : syracuseStep 1403779 = 2105669) B2105669
theorem B10259341 : Blo 1168401 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B2026387 : Blo 1168401 2026387 := bstep (se 1 (by rfl) ⟨1519790, by rfl⟩ : syracuseStep 2026387 = 3039581) B3039581
theorem B2370467 : Blo 1168401 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B2632625 : Blo 1168401 2632625 := bstep (se 2 (by rfl) ⟨987234, by rfl⟩ : syracuseStep 2632625 = 1974469) B1974469
theorem B2632643 : Blo 1168401 2632643 := bstep (se 1 (by rfl) ⟨1974482, by rfl⟩ : syracuseStep 2632643 = 3948965) B3948965
theorem B1403875 : Blo 1168401 1403875 := bstep (se 1 (by rfl) ⟨1052906, by rfl⟩ : syracuseStep 1403875 = 2105813) B2105813
theorem B8424461 : Blo 1168401 8424461 := bstep (se 3 (by rfl) ⟨1579586, by rfl⟩ : syracuseStep 8424461 = 3159173) B3159173
theorem B3329059 : Blo 1168401 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B2108465 : Blo 1168401 2108465 := bstep (se 2 (by rfl) ⟨790674, by rfl⟩ : syracuseStep 2108465 = 1581349) B1581349
theorem B3943565 : Blo 1168401 3943565 := bstep (se 3 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 3943565 = 1478837) B1478837
theorem B5917859 : Blo 1168401 5917859 := bstep (se 1 (by rfl) ⟨4438394, by rfl⟩ : syracuseStep 5917859 = 8876789) B8876789
theorem B3943619 : Blo 1168401 3943619 := bstep (se 1 (by rfl) ⟨2957714, by rfl⟩ : syracuseStep 3943619 = 5915429) B5915429
theorem B2632913 : Blo 1168401 2632913 := bstep (se 2 (by rfl) ⟨987342, by rfl⟩ : syracuseStep 2632913 = 1974685) B1974685
theorem B2632931 : Blo 1168401 2632931 := bstep (se 1 (by rfl) ⟨1974698, by rfl⟩ : syracuseStep 2632931 = 3949397) B3949397
theorem B1666289 : Blo 1168401 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B1666369 : Blo 1168401 1666369 := bstep (se 2 (by rfl) ⟨624888, by rfl⟩ : syracuseStep 1666369 = 1249777) B1249777
theorem B1404259 : Blo 1168401 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B9997667 : Blo 1168401 9997667 := bstep (se 1 (by rfl) ⟨7498250, by rfl⟩ : syracuseStep 9997667 = 14996501) B14996501
theorem B3001763 : Blo 1168401 3001763 := bstep (se 1 (by rfl) ⟨2251322, by rfl⟩ : syracuseStep 3001763 = 4502645) B4502645
theorem B3943889 : Blo 1168401 3943889 := bstep (se 2 (by rfl) ⟨1478958, by rfl⟩ : syracuseStep 3943889 = 2957917) B2957917
theorem B4443619 : Blo 1168401 4443619 := bstep (se 1 (by rfl) ⟨3332714, by rfl⟩ : syracuseStep 4443619 = 6665429) B6665429
theorem B2633201 : Blo 1168401 2633201 := bstep (se 2 (by rfl) ⟨987450, by rfl⟩ : syracuseStep 2633201 = 1974901) B1974901
theorem B2633219 : Blo 1168401 2633219 := bstep (se 1 (by rfl) ⟨1974914, by rfl⟩ : syracuseStep 2633219 = 3949829) B3949829
theorem B3329549 : Blo 1168401 3329549 := bstep (se 3 (by rfl) ⟨624290, by rfl⟩ : syracuseStep 3329549 = 1248581) B1248581
theorem B2960945 : Blo 1168401 2960945 := bstep (se 2 (by rfl) ⟨1110354, by rfl⟩ : syracuseStep 2960945 = 2220709) B2220709
theorem B2960995 : Blo 1168401 2960995 := bstep (se 1 (by rfl) ⟨2220746, by rfl⟩ : syracuseStep 2960995 = 4441493) B4441493
theorem B1314499 : Blo 1168401 1314499 := bstep (se 1 (by rfl) ⟨985874, by rfl⟩ : syracuseStep 1314499 = 1971749) B1971749
theorem B5615345 : Blo 1168401 5615345 := bstep (se 2 (by rfl) ⟨2105754, by rfl⟩ : syracuseStep 5615345 = 4211509) B4211509
theorem B2961137 : Blo 1168401 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B1871603 : Blo 1168401 1871603 := bstep (se 1 (by rfl) ⟨1403702, by rfl⟩ : syracuseStep 1871603 = 2807405) B2807405
theorem B1601281 : Blo 1168401 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B6663971 : Blo 1168401 6663971 := bstep (se 1 (by rfl) ⟨4997978, by rfl⟩ : syracuseStep 6663971 = 9995957) B9995957
theorem B4501325 : Blo 1168401 4501325 := bstep (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) B1687997
theorem B1314643 : Blo 1168401 1314643 := bstep (se 1 (by rfl) ⟨985982, by rfl⟩ : syracuseStep 1314643 = 1971965) B1971965
theorem B1249187 : Blo 1168401 1249187 := bstep (se 1 (by rfl) ⟨936890, by rfl⟩ : syracuseStep 1249187 = 1873781) B1873781
theorem B1871795 : Blo 1168401 1871795 := bstep (se 1 (by rfl) ⟨1403846, by rfl⟩ : syracuseStep 1871795 = 2807693) B2807693
theorem B5918669 : Blo 1168401 5918669 := bstep (se 3 (by rfl) ⟨1109750, by rfl⟩ : syracuseStep 5918669 = 2219501) B2219501
theorem B1314787 : Blo 1168401 1314787 := bstep (se 1 (by rfl) ⟨986090, by rfl⟩ : syracuseStep 1314787 = 1972181) B1972181
theorem B3944429 : Blo 1168401 3944429 := bstep (se 3 (by rfl) ⟨739580, by rfl⟩ : syracuseStep 3944429 = 1479161) B1479161
theorem B3944483 : Blo 1168401 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B5615693 : Blo 1168401 5615693 := bstep (se 3 (by rfl) ⟨1052942, by rfl⟩ : syracuseStep 5615693 = 2105885) B2105885
theorem B1314931 : Blo 1168401 1314931 := bstep (se 1 (by rfl) ⟨986198, by rfl⟩ : syracuseStep 1314931 = 1972397) B1972397
theorem B21328069 : Blo 1168401 21328069 := bstep (se 4 (by rfl) ⟨1999506, by rfl⟩ : syracuseStep 21328069 = 3999013) B3999013
theorem B1315075 : Blo 1168401 1315075 := bstep (se 1 (by rfl) ⟨986306, by rfl⟩ : syracuseStep 1315075 = 1972613) B1972613
theorem B3944753 : Blo 1168401 3944753 := bstep (se 2 (by rfl) ⟨1479282, by rfl⟩ : syracuseStep 3944753 = 2958565) B2958565
theorem B1315219 : Blo 1168401 1315219 := bstep (se 1 (by rfl) ⟨986414, by rfl⟩ : syracuseStep 1315219 = 1972829) B1972829
theorem B1315363 : Blo 1168401 1315363 := bstep (se 1 (by rfl) ⟨986522, by rfl⟩ : syracuseStep 1315363 = 1973045) B1973045
theorem B1184419 : Blo 1168401 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B3330733 : Blo 1168401 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B1315507 : Blo 1168401 1315507 := bstep (se 1 (by rfl) ⟨986630, by rfl⟩ : syracuseStep 1315507 = 1973261) B1973261
theorem B4993741 : Blo 1168401 4993741 := bstep (se 3 (by rfl) ⟨936326, by rfl⟩ : syracuseStep 4993741 = 1872653) B1872653
theorem B1479379 : Blo 1168401 1479379 := bstep (se 1 (by rfl) ⟨1109534, by rfl⟩ : syracuseStep 1479379 = 2219069) B2219069
theorem B2962129 : Blo 1168401 2962129 := bstep (se 2 (by rfl) ⟨1110798, by rfl⟩ : syracuseStep 2962129 = 2221597) B2221597
theorem B1479475 : Blo 1168401 1479475 := bstep (se 1 (by rfl) ⟨1109606, by rfl⟩ : syracuseStep 1479475 = 2219213) B2219213
theorem B1315651 : Blo 1168401 1315651 := bstep (se 1 (by rfl) ⟨986738, by rfl⟩ : syracuseStep 1315651 = 1973477) B1973477
theorem B3945293 : Blo 1168401 3945293 := bstep (se 3 (by rfl) ⟨739742, by rfl⟩ : syracuseStep 3945293 = 1479485) B1479485
theorem B3945347 : Blo 1168401 3945347 := bstep (se 1 (by rfl) ⟨2959010, by rfl⟩ : syracuseStep 3945347 = 5918021) B5918021
theorem B3748781 : Blo 1168401 3748781 := bstep (se 3 (by rfl) ⟨702896, by rfl⟩ : syracuseStep 3748781 = 1405793) B1405793
theorem B1315795 : Blo 1168401 1315795 := bstep (se 1 (by rfl) ⟨986846, by rfl⟩ : syracuseStep 1315795 = 1973693) B1973693
theorem B2962403 : Blo 1168401 2962403 := bstep (se 1 (by rfl) ⟨2221802, by rfl⟩ : syracuseStep 2962403 = 4443605) B4443605
theorem B1168403 : Blo 1168401 1168403 := bstep (se 1 (by rfl) ⟨876302, by rfl⟩ : syracuseStep 1168403 = 1752605) B1752605
theorem B1168419 : Blo 1168401 1168419 := bstep (se 1 (by rfl) ⟨876314, by rfl⟩ : syracuseStep 1168419 = 1752629) B1752629
theorem B1168435 : Blo 1168401 1168435 := bstep (se 1 (by rfl) ⟨876326, by rfl⟩ : syracuseStep 1168435 = 1752653) B1752653
theorem B1168451 : Blo 1168401 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B1168467 : Blo 1168401 1168467 := bstep (se 1 (by rfl) ⟨876350, by rfl⟩ : syracuseStep 1168467 = 1752701) B1752701
theorem B1168483 : Blo 1168401 1168483 := bstep (se 1 (by rfl) ⟨876362, by rfl⟩ : syracuseStep 1168483 = 1752725) B1752725
theorem B1315939 : Blo 1168401 1315939 := bstep (se 1 (by rfl) ⟨986954, by rfl⟩ : syracuseStep 1315939 = 1973909) B1973909
theorem B6657137 : Blo 1168401 6657137 := bstep (se 2 (by rfl) ⟨2496426, by rfl⟩ : syracuseStep 6657137 = 4992853) B4992853
theorem B14988401 : Blo 1168401 14988401 := bstep (se 2 (by rfl) ⟨5620650, by rfl⟩ : syracuseStep 14988401 = 11241301) B11241301
theorem B1168499 : Blo 1168401 1168499 := bstep (se 1 (by rfl) ⟨876374, by rfl⟩ : syracuseStep 1168499 = 1752749) B1752749
theorem B1168515 : Blo 1168401 1168515 := bstep (se 1 (by rfl) ⟨876386, by rfl⟩ : syracuseStep 1168515 = 1752773) B1752773
theorem B9991309 : Blo 1168401 9991309 := bstep (se 3 (by rfl) ⟨1873370, by rfl⟩ : syracuseStep 9991309 = 3746741) B3746741
theorem B3945617 : Blo 1168401 3945617 := bstep (se 2 (by rfl) ⟨1479606, by rfl⟩ : syracuseStep 3945617 = 2959213) B2959213
theorem B1168531 : Blo 1168401 1168531 := bstep (se 1 (by rfl) ⟨876398, by rfl⟩ : syracuseStep 1168531 = 1752797) B1752797
theorem B1168547 : Blo 1168401 1168547 := bstep (se 1 (by rfl) ⟨876410, by rfl⟩ : syracuseStep 1168547 = 1752821) B1752821
theorem B1168563 : Blo 1168401 1168563 := bstep (se 1 (by rfl) ⟨876422, by rfl⟩ : syracuseStep 1168563 = 1752845) B1752845
theorem B1168579 : Blo 1168401 1168579 := bstep (se 1 (by rfl) ⟨876434, by rfl⟩ : syracuseStep 1168579 = 1752869) B1752869
theorem B1168595 : Blo 1168401 1168595 := bstep (se 1 (by rfl) ⟨876446, by rfl⟩ : syracuseStep 1168595 = 1752893) B1752893
theorem B1168611 : Blo 1168401 1168611 := bstep (se 1 (by rfl) ⟨876458, by rfl⟩ : syracuseStep 1168611 = 1752917) B1752917
theorem B1168627 : Blo 1168401 1168627 := bstep (se 1 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 1168627 = 1752941) B1752941
theorem B1316083 : Blo 1168401 1316083 := bstep (se 1 (by rfl) ⟨987062, by rfl⟩ : syracuseStep 1316083 = 1974125) B1974125
theorem B1168643 : Blo 1168401 1168643 := bstep (se 1 (by rfl) ⟨876482, by rfl⟩ : syracuseStep 1168643 = 1752965) B1752965
theorem B1168659 : Blo 1168401 1168659 := bstep (se 1 (by rfl) ⟨876494, by rfl⟩ : syracuseStep 1168659 = 1752989) B1752989
theorem B1168675 : Blo 1168401 1168675 := bstep (se 1 (by rfl) ⟨876506, by rfl⟩ : syracuseStep 1168675 = 1753013) B1753013
theorem B1479971 : Blo 1168401 1479971 := bstep (se 1 (by rfl) ⟨1109978, by rfl⟩ : syracuseStep 1479971 = 2219957) B2219957
theorem B1168691 : Blo 1168401 1168691 := bstep (se 1 (by rfl) ⟨876518, by rfl⟩ : syracuseStep 1168691 = 1753037) B1753037
theorem B1873217 : Blo 1168401 1873217 := bstep (se 2 (by rfl) ⟨702456, by rfl⟩ : syracuseStep 1873217 = 1404913) B1404913
theorem B1168707 : Blo 1168401 1168707 := bstep (se 1 (by rfl) ⟨876530, by rfl⟩ : syracuseStep 1168707 = 1753061) B1753061
theorem B1168723 : Blo 1168401 1168723 := bstep (se 1 (by rfl) ⟨876542, by rfl⟩ : syracuseStep 1168723 = 1753085) B1753085
theorem B1168739 : Blo 1168401 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B1168755 : Blo 1168401 1168755 := bstep (se 1 (by rfl) ⟨876566, by rfl⟩ : syracuseStep 1168755 = 1753133) B1753133
theorem B1168771 : Blo 1168401 1168771 := bstep (se 1 (by rfl) ⟨876578, by rfl⟩ : syracuseStep 1168771 = 1753157) B1753157
theorem B1316227 : Blo 1168401 1316227 := bstep (se 1 (by rfl) ⟨987170, by rfl⟩ : syracuseStep 1316227 = 1974341) B1974341
theorem B1168787 : Blo 1168401 1168787 := bstep (se 1 (by rfl) ⟨876590, by rfl⟩ : syracuseStep 1168787 = 1753181) B1753181
theorem B1168803 : Blo 1168401 1168803 := bstep (se 1 (by rfl) ⟨876602, by rfl⟩ : syracuseStep 1168803 = 1753205) B1753205
theorem B1168819 : Blo 1168401 1168819 := bstep (se 1 (by rfl) ⟨876614, by rfl⟩ : syracuseStep 1168819 = 1753229) B1753229
theorem B2028979 : Blo 1168401 2028979 := bstep (se 1 (by rfl) ⟨1521734, by rfl⟩ : syracuseStep 2028979 = 3043469) B3043469
theorem B1168835 : Blo 1168401 1168835 := bstep (se 1 (by rfl) ⟨876626, by rfl⟩ : syracuseStep 1168835 = 1753253) B1753253
theorem B1168851 : Blo 1168401 1168851 := bstep (se 1 (by rfl) ⟨876638, by rfl⟩ : syracuseStep 1168851 = 1753277) B1753277
theorem B1168867 : Blo 1168401 1168867 := bstep (se 1 (by rfl) ⟨876650, by rfl⟩ : syracuseStep 1168867 = 1753301) B1753301
theorem B2848241 : Blo 1168401 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B1168883 : Blo 1168401 1168883 := bstep (se 1 (by rfl) ⟨876662, by rfl⟩ : syracuseStep 1168883 = 1753325) B1753325
theorem B1971715 : Blo 1168401 1971715 := bstep (se 1 (by rfl) ⟨1478786, by rfl⟩ : syracuseStep 1971715 = 2957573) B2957573
theorem B1168899 : Blo 1168401 1168899 := bstep (se 1 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 1168899 = 1753349) B1753349
theorem B2496017 : Blo 1168401 2496017 := bstep (se 2 (by rfl) ⟨936006, by rfl⟩ : syracuseStep 2496017 = 1872013) B1872013
theorem B1168915 : Blo 1168401 1168915 := bstep (se 1 (by rfl) ⟨876686, by rfl⟩ : syracuseStep 1168915 = 1753373) B1753373
theorem B1316371 : Blo 1168401 1316371 := bstep (se 1 (by rfl) ⟨987278, by rfl⟩ : syracuseStep 1316371 = 1974557) B1974557
theorem B1168931 : Blo 1168401 1168931 := bstep (se 1 (by rfl) ⟨876698, by rfl⟩ : syracuseStep 1168931 = 1753397) B1753397
theorem B1168947 : Blo 1168401 1168947 := bstep (se 1 (by rfl) ⟨876710, by rfl⟩ : syracuseStep 1168947 = 1753421) B1753421
theorem B1168963 : Blo 1168401 1168963 := bstep (se 1 (by rfl) ⟨876722, by rfl⟩ : syracuseStep 1168963 = 1753445) B1753445
theorem B1168979 : Blo 1168401 1168979 := bstep (se 1 (by rfl) ⟨876734, by rfl⟩ : syracuseStep 1168979 = 1753469) B1753469
theorem B1168995 : Blo 1168401 1168995 := bstep (se 1 (by rfl) ⟨876746, by rfl⟩ : syracuseStep 1168995 = 1753493) B1753493
theorem B3159661 : Blo 1168401 3159661 := bstep (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) B1184873
theorem B1169011 : Blo 1168401 1169011 := bstep (se 1 (by rfl) ⟨876758, by rfl⟩ : syracuseStep 1169011 = 1753517) B1753517
theorem B1169027 : Blo 1168401 1169027 := bstep (se 1 (by rfl) ⟨876770, by rfl⟩ : syracuseStep 1169027 = 1753541) B1753541
theorem B6411917 : Blo 1168401 6411917 := bstep (se 3 (by rfl) ⟨1202234, by rfl⟩ : syracuseStep 6411917 = 2404469) B2404469
theorem B1971857 : Blo 1168401 1971857 := bstep (se 2 (by rfl) ⟨739446, by rfl⟩ : syracuseStep 1971857 = 1478893) B1478893
theorem B1169043 : Blo 1168401 1169043 := bstep (se 1 (by rfl) ⟨876782, by rfl⟩ : syracuseStep 1169043 = 1753565) B1753565
theorem B1169059 : Blo 1168401 1169059 := bstep (se 1 (by rfl) ⟨876794, by rfl⟩ : syracuseStep 1169059 = 1753589) B1753589
theorem B1316515 : Blo 1168401 1316515 := bstep (se 1 (by rfl) ⟨987386, by rfl⟩ : syracuseStep 1316515 = 1974773) B1974773
theorem B3946157 : Blo 1168401 3946157 := bstep (se 3 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 3946157 = 1479809) B1479809
theorem B8115889 : Blo 1168401 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B1169075 : Blo 1168401 1169075 := bstep (se 1 (by rfl) ⟨876806, by rfl⟩ : syracuseStep 1169075 = 1753613) B1753613
theorem B1169091 : Blo 1168401 1169091 := bstep (se 1 (by rfl) ⟨876818, by rfl⟩ : syracuseStep 1169091 = 1753637) B1753637
theorem B3331793 : Blo 1168401 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1169107 : Blo 1168401 1169107 := bstep (se 1 (by rfl) ⟨876830, by rfl⟩ : syracuseStep 1169107 = 1753661) B1753661
theorem B1169123 : Blo 1168401 1169123 := bstep (se 1 (by rfl) ⟨876842, by rfl⟩ : syracuseStep 1169123 = 1753685) B1753685
theorem B3946211 : Blo 1168401 3946211 := bstep (se 1 (by rfl) ⟨2959658, by rfl⟩ : syracuseStep 3946211 = 5919317) B5919317
theorem B1169139 : Blo 1168401 1169139 := bstep (se 1 (by rfl) ⟨876854, by rfl⟩ : syracuseStep 1169139 = 1753709) B1753709
theorem B1169155 : Blo 1168401 1169155 := bstep (se 1 (by rfl) ⟨876866, by rfl⟩ : syracuseStep 1169155 = 1753733) B1753733
theorem B7493381 : Blo 1168401 7493381 := bstep (se 4 (by rfl) ⟨702504, by rfl⟩ : syracuseStep 7493381 = 1405009) B1405009
theorem B4437773 : Blo 1168401 4437773 := bstep (se 3 (by rfl) ⟨832082, by rfl⟩ : syracuseStep 4437773 = 1664165) B1664165
theorem B1971985 : Blo 1168401 1971985 := bstep (se 2 (by rfl) ⟨739494, by rfl⟩ : syracuseStep 1971985 = 1478989) B1478989
theorem B1169171 : Blo 1168401 1169171 := bstep (se 1 (by rfl) ⟨876878, by rfl⟩ : syracuseStep 1169171 = 1753757) B1753757
theorem B1169187 : Blo 1168401 1169187 := bstep (se 1 (by rfl) ⟨876890, by rfl⟩ : syracuseStep 1169187 = 1753781) B1753781
theorem B1972019 : Blo 1168401 1972019 := bstep (se 1 (by rfl) ⟨1479014, by rfl⟩ : syracuseStep 1972019 = 2958029) B2958029
theorem B1169203 : Blo 1168401 1169203 := bstep (se 1 (by rfl) ⟨876902, by rfl⟩ : syracuseStep 1169203 = 1753805) B1753805
theorem B1316659 : Blo 1168401 1316659 := bstep (se 1 (by rfl) ⟨987494, by rfl⟩ : syracuseStep 1316659 = 1974989) B1974989
theorem B1169219 : Blo 1168401 1169219 := bstep (se 1 (by rfl) ⟨876914, by rfl⟩ : syracuseStep 1169219 = 1753829) B1753829
theorem B1169235 : Blo 1168401 1169235 := bstep (se 1 (by rfl) ⟨876926, by rfl⟩ : syracuseStep 1169235 = 1753853) B1753853
theorem B1169251 : Blo 1168401 1169251 := bstep (se 1 (by rfl) ⟨876938, by rfl⟩ : syracuseStep 1169251 = 1753877) B1753877
theorem B1898353 : Blo 1168401 1898353 := bstep (se 2 (by rfl) ⟨711882, by rfl⟩ : syracuseStep 1898353 = 1423765) B1423765
theorem B1169267 : Blo 1168401 1169267 := bstep (se 1 (by rfl) ⟨876950, by rfl⟩ : syracuseStep 1169267 = 1753901) B1753901
theorem B1169283 : Blo 1168401 1169283 := bstep (se 1 (by rfl) ⟨876962, by rfl⟩ : syracuseStep 1169283 = 1753925) B1753925
theorem B1169299 : Blo 1168401 1169299 := bstep (se 1 (by rfl) ⟨876974, by rfl⟩ : syracuseStep 1169299 = 1753949) B1753949
theorem B1169315 : Blo 1168401 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B1972147 : Blo 1168401 1972147 := bstep (se 1 (by rfl) ⟨1479110, by rfl⟩ : syracuseStep 1972147 = 2958221) B2958221
theorem B1169331 : Blo 1168401 1169331 := bstep (se 1 (by rfl) ⟨876998, by rfl⟩ : syracuseStep 1169331 = 1753997) B1753997
theorem B1169347 : Blo 1168401 1169347 := bstep (se 1 (by rfl) ⟨877010, by rfl⟩ : syracuseStep 1169347 = 1754021) B1754021
theorem B1169363 : Blo 1168401 1169363 := bstep (se 1 (by rfl) ⟨877022, by rfl⟩ : syracuseStep 1169363 = 1754045) B1754045
theorem B1169379 : Blo 1168401 1169379 := bstep (se 1 (by rfl) ⟨877034, by rfl⟩ : syracuseStep 1169379 = 1754069) B1754069
theorem B14227427 : Blo 1168401 14227427 := bstep (se 1 (by rfl) ⟨10670570, by rfl⟩ : syracuseStep 14227427 = 21341141) B21341141
theorem B1480675 : Blo 1168401 1480675 := bstep (se 1 (by rfl) ⟨1110506, by rfl⟩ : syracuseStep 1480675 = 2221013) B2221013
theorem B3946481 : Blo 1168401 3946481 := bstep (se 2 (by rfl) ⟨1479930, by rfl⟩ : syracuseStep 3946481 = 2959861) B2959861
theorem B1169395 : Blo 1168401 1169395 := bstep (se 1 (by rfl) ⟨877046, by rfl⟩ : syracuseStep 1169395 = 1754093) B1754093
theorem B1169411 : Blo 1168401 1169411 := bstep (se 1 (by rfl) ⟨877058, by rfl⟩ : syracuseStep 1169411 = 1754117) B1754117
theorem B2496529 : Blo 1168401 2496529 := bstep (se 2 (by rfl) ⟨936198, by rfl⟩ : syracuseStep 2496529 = 1872397) B1872397
theorem B3799057 : Blo 1168401 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B1169427 : Blo 1168401 1169427 := bstep (se 1 (by rfl) ⟨877070, by rfl⟩ : syracuseStep 1169427 = 1754141) B1754141
theorem B1169443 : Blo 1168401 1169443 := bstep (se 1 (by rfl) ⟨877082, by rfl⟩ : syracuseStep 1169443 = 1754165) B1754165
theorem B1169459 : Blo 1168401 1169459 := bstep (se 1 (by rfl) ⟨877094, by rfl⟩ : syracuseStep 1169459 = 1754189) B1754189
theorem B1972289 : Blo 1168401 1972289 := bstep (se 2 (by rfl) ⟨739608, by rfl⟩ : syracuseStep 1972289 = 1479217) B1479217
theorem B1169475 : Blo 1168401 1169475 := bstep (se 1 (by rfl) ⟨877106, by rfl⟩ : syracuseStep 1169475 = 1754213) B1754213
theorem B1480771 : Blo 1168401 1480771 := bstep (se 1 (by rfl) ⟨1110578, by rfl⟩ : syracuseStep 1480771 = 2221157) B2221157
theorem B1169491 : Blo 1168401 1169491 := bstep (se 1 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 1169491 = 1754237) B1754237
theorem B1169507 : Blo 1168401 1169507 := bstep (se 1 (by rfl) ⟨877130, by rfl⟩ : syracuseStep 1169507 = 1754261) B1754261
theorem B1169523 : Blo 1168401 1169523 := bstep (se 1 (by rfl) ⟨877142, by rfl⟩ : syracuseStep 1169523 = 1754285) B1754285
theorem B1169539 : Blo 1168401 1169539 := bstep (se 1 (by rfl) ⟨877154, by rfl⟩ : syracuseStep 1169539 = 1754309) B1754309
theorem B1169555 : Blo 1168401 1169555 := bstep (se 1 (by rfl) ⟨877166, by rfl⟩ : syracuseStep 1169555 = 1754333) B1754333
theorem B1169571 : Blo 1168401 1169571 := bstep (se 1 (by rfl) ⟨877178, by rfl⟩ : syracuseStep 1169571 = 1754357) B1754357
theorem B1169587 : Blo 1168401 1169587 := bstep (se 1 (by rfl) ⟨877190, by rfl⟩ : syracuseStep 1169587 = 1754381) B1754381
theorem B1972417 : Blo 1168401 1972417 := bstep (se 2 (by rfl) ⟨739656, by rfl⟩ : syracuseStep 1972417 = 1479313) B1479313
theorem B1169603 : Blo 1168401 1169603 := bstep (se 1 (by rfl) ⟨877202, by rfl⟩ : syracuseStep 1169603 = 1754405) B1754405
theorem B4741325 : Blo 1168401 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B1169619 : Blo 1168401 1169619 := bstep (se 1 (by rfl) ⟨877214, by rfl⟩ : syracuseStep 1169619 = 1754429) B1754429
theorem B1972451 : Blo 1168401 1972451 := bstep (se 1 (by rfl) ⟨1479338, by rfl⟩ : syracuseStep 1972451 = 2958677) B2958677
theorem B1169635 : Blo 1168401 1169635 := bstep (se 1 (by rfl) ⟨877226, by rfl⟩ : syracuseStep 1169635 = 1754453) B1754453
theorem B11229425 : Blo 1168401 11229425 := bstep (se 2 (by rfl) ⟨4211034, by rfl⟩ : syracuseStep 11229425 = 8422069) B8422069
theorem B1169651 : Blo 1168401 1169651 := bstep (se 1 (by rfl) ⟨877238, by rfl⟩ : syracuseStep 1169651 = 1754477) B1754477
theorem B1169667 : Blo 1168401 1169667 := bstep (se 1 (by rfl) ⟨877250, by rfl⟩ : syracuseStep 1169667 = 1754501) B1754501
theorem B1169683 : Blo 1168401 1169683 := bstep (se 1 (by rfl) ⟨877262, by rfl⟩ : syracuseStep 1169683 = 1754525) B1754525
theorem B1169699 : Blo 1168401 1169699 := bstep (se 1 (by rfl) ⟨877274, by rfl⟩ : syracuseStep 1169699 = 1754549) B1754549
theorem B1169715 : Blo 1168401 1169715 := bstep (se 1 (by rfl) ⟨877286, by rfl⟩ : syracuseStep 1169715 = 1754573) B1754573
theorem B1169731 : Blo 1168401 1169731 := bstep (se 1 (by rfl) ⟨877298, by rfl⟩ : syracuseStep 1169731 = 1754597) B1754597
theorem B1169747 : Blo 1168401 1169747 := bstep (se 1 (by rfl) ⟨877310, by rfl⟩ : syracuseStep 1169747 = 1754621) B1754621
theorem B1972579 : Blo 1168401 1972579 := bstep (se 1 (by rfl) ⟨1479434, by rfl⟩ : syracuseStep 1972579 = 2958869) B2958869
theorem B1169763 : Blo 1168401 1169763 := bstep (se 1 (by rfl) ⟨877322, by rfl⟩ : syracuseStep 1169763 = 1754645) B1754645
theorem B3332465 : Blo 1168401 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B1169779 : Blo 1168401 1169779 := bstep (se 1 (by rfl) ⟨877334, by rfl⟩ : syracuseStep 1169779 = 1754669) B1754669
theorem B1169795 : Blo 1168401 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B1169811 : Blo 1168401 1169811 := bstep (se 1 (by rfl) ⟨877358, by rfl⟩ : syracuseStep 1169811 = 1754717) B1754717
theorem B1169827 : Blo 1168401 1169827 := bstep (se 1 (by rfl) ⟨877370, by rfl⟩ : syracuseStep 1169827 = 1754741) B1754741
theorem B1169843 : Blo 1168401 1169843 := bstep (se 1 (by rfl) ⟨877382, by rfl⟩ : syracuseStep 1169843 = 1754765) B1754765
theorem B1169859 : Blo 1168401 1169859 := bstep (se 1 (by rfl) ⟨877394, by rfl⟩ : syracuseStep 1169859 = 1754789) B1754789
theorem B9992645 : Blo 1168401 9992645 := bstep (se 4 (by rfl) ⟨936810, by rfl⟩ : syracuseStep 9992645 = 1873621) B1873621
theorem B1169875 : Blo 1168401 1169875 := bstep (se 1 (by rfl) ⟨877406, by rfl⟩ : syracuseStep 1169875 = 1754813) B1754813
theorem B1169891 : Blo 1168401 1169891 := bstep (se 1 (by rfl) ⟨877418, by rfl⟩ : syracuseStep 1169891 = 1754837) B1754837
theorem B1972721 : Blo 1168401 1972721 := bstep (se 2 (by rfl) ⟨739770, by rfl⟩ : syracuseStep 1972721 = 1479541) B1479541
theorem B1169907 : Blo 1168401 1169907 := bstep (se 1 (by rfl) ⟨877430, by rfl⟩ : syracuseStep 1169907 = 1754861) B1754861
theorem B2218499 : Blo 1168401 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B1169923 : Blo 1168401 1169923 := bstep (se 1 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 1169923 = 1754885) B1754885
theorem B3947021 : Blo 1168401 3947021 := bstep (se 3 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 3947021 = 1480133) B1480133
theorem B1169939 : Blo 1168401 1169939 := bstep (se 1 (by rfl) ⟨877454, by rfl⟩ : syracuseStep 1169939 = 1754909) B1754909
theorem B6658595 : Blo 1168401 6658595 := bstep (se 1 (by rfl) ⟨4993946, by rfl⟩ : syracuseStep 6658595 = 9987893) B9987893
theorem B1169955 : Blo 1168401 1169955 := bstep (se 1 (by rfl) ⟨877466, by rfl⟩ : syracuseStep 1169955 = 1754933) B1754933
theorem B4438577 : Blo 1168401 4438577 := bstep (se 2 (by rfl) ⟨1664466, by rfl⟩ : syracuseStep 4438577 = 3328933) B3328933
theorem B1169971 : Blo 1168401 1169971 := bstep (se 1 (by rfl) ⟨877478, by rfl⟩ : syracuseStep 1169971 = 1754957) B1754957
theorem B1481267 : Blo 1168401 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B3947075 : Blo 1168401 3947075 := bstep (se 1 (by rfl) ⟨2960306, by rfl⟩ : syracuseStep 3947075 = 5920613) B5920613
theorem B1169987 : Blo 1168401 1169987 := bstep (se 1 (by rfl) ⟨877490, by rfl⟩ : syracuseStep 1169987 = 1754981) B1754981
theorem B1170003 : Blo 1168401 1170003 := bstep (se 1 (by rfl) ⟨877502, by rfl⟩ : syracuseStep 1170003 = 1755005) B1755005
theorem B1579619 : Blo 1168401 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1170019 : Blo 1168401 1170019 := bstep (se 1 (by rfl) ⟨877514, by rfl⟩ : syracuseStep 1170019 = 1755029) B1755029
theorem B1972849 : Blo 1168401 1972849 := bstep (se 2 (by rfl) ⟨739818, by rfl⟩ : syracuseStep 1972849 = 1479637) B1479637
theorem B1170035 : Blo 1168401 1170035 := bstep (se 1 (by rfl) ⟨877526, by rfl⟩ : syracuseStep 1170035 = 1755053) B1755053
theorem B1170051 : Blo 1168401 1170051 := bstep (se 1 (by rfl) ⟨877538, by rfl⟩ : syracuseStep 1170051 = 1755077) B1755077
theorem B8878733 : Blo 1168401 8878733 := bstep (se 3 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 8878733 = 3329525) B3329525
theorem B1972883 : Blo 1168401 1972883 := bstep (se 1 (by rfl) ⟨1479662, by rfl⟩ : syracuseStep 1972883 = 2959325) B2959325
theorem B1170067 : Blo 1168401 1170067 := bstep (se 1 (by rfl) ⟨877550, by rfl⟩ : syracuseStep 1170067 = 1755101) B1755101
theorem B1170083 : Blo 1168401 1170083 := bstep (se 1 (by rfl) ⟨877562, by rfl⟩ : syracuseStep 1170083 = 1755125) B1755125
theorem B1170099 : Blo 1168401 1170099 := bstep (se 1 (by rfl) ⟨877574, by rfl⟩ : syracuseStep 1170099 = 1755149) B1755149
theorem B1170115 : Blo 1168401 1170115 := bstep (se 1 (by rfl) ⟨877586, by rfl⟩ : syracuseStep 1170115 = 1755173) B1755173
theorem B1170131 : Blo 1168401 1170131 := bstep (se 1 (by rfl) ⟨877598, by rfl⟩ : syracuseStep 1170131 = 1755197) B1755197
theorem B1170147 : Blo 1168401 1170147 := bstep (se 1 (by rfl) ⟨877610, by rfl⟩ : syracuseStep 1170147 = 1755221) B1755221
theorem B1170163 : Blo 1168401 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B1170179 : Blo 1168401 1170179 := bstep (se 1 (by rfl) ⟨877634, by rfl⟩ : syracuseStep 1170179 = 1755269) B1755269
theorem B1973011 : Blo 1168401 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B1170195 : Blo 1168401 1170195 := bstep (se 1 (by rfl) ⟨877646, by rfl⟩ : syracuseStep 1170195 = 1755293) B1755293
theorem B1170211 : Blo 1168401 1170211 := bstep (se 1 (by rfl) ⟨877658, by rfl⟩ : syracuseStep 1170211 = 1755317) B1755317
theorem B5921585 : Blo 1168401 5921585 := bstep (se 2 (by rfl) ⟨2220594, by rfl⟩ : syracuseStep 5921585 = 4441189) B4441189
theorem B1170227 : Blo 1168401 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B1170243 : Blo 1168401 1170243 := bstep (se 1 (by rfl) ⟨877682, by rfl⟩ : syracuseStep 1170243 = 1755365) B1755365
theorem B1874755 : Blo 1168401 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B3947345 : Blo 1168401 3947345 := bstep (se 2 (by rfl) ⟨1480254, by rfl⟩ : syracuseStep 3947345 = 2960509) B2960509
theorem B1170259 : Blo 1168401 1170259 := bstep (se 1 (by rfl) ⟨877694, by rfl⟩ : syracuseStep 1170259 = 1755389) B1755389
theorem B7486307 : Blo 1168401 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B1170275 : Blo 1168401 1170275 := bstep (se 1 (by rfl) ⟨877706, by rfl⟩ : syracuseStep 1170275 = 1755413) B1755413
theorem B1170291 : Blo 1168401 1170291 := bstep (se 1 (by rfl) ⟨877718, by rfl⟩ : syracuseStep 1170291 = 1755437) B1755437
theorem B1170307 : Blo 1168401 1170307 := bstep (se 1 (by rfl) ⟨877730, by rfl⟩ : syracuseStep 1170307 = 1755461) B1755461
theorem B18963341 : Blo 1168401 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B1170323 : Blo 1168401 1170323 := bstep (se 1 (by rfl) ⟨877742, by rfl⟩ : syracuseStep 1170323 = 1755485) B1755485
theorem B1973153 : Blo 1168401 1973153 := bstep (se 2 (by rfl) ⟨739932, by rfl⟩ : syracuseStep 1973153 = 1479865) B1479865
theorem B1170339 : Blo 1168401 1170339 := bstep (se 1 (by rfl) ⟨877754, by rfl⟩ : syracuseStep 1170339 = 1755509) B1755509
theorem B1170355 : Blo 1168401 1170355 := bstep (se 1 (by rfl) ⟨877766, by rfl⟩ : syracuseStep 1170355 = 1755533) B1755533
theorem B1170371 : Blo 1168401 1170371 := bstep (se 1 (by rfl) ⟨877778, by rfl⟩ : syracuseStep 1170371 = 1755557) B1755557
theorem B1924049 : Blo 1168401 1924049 := bstep (se 2 (by rfl) ⟨721518, by rfl⟩ : syracuseStep 1924049 = 1443037) B1443037
theorem B1170387 : Blo 1168401 1170387 := bstep (se 1 (by rfl) ⟨877790, by rfl⟩ : syracuseStep 1170387 = 1755581) B1755581
theorem B1973281 : Blo 1168401 1973281 := bstep (se 2 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 1973281 = 1479961) B1479961
theorem B1973315 : Blo 1168401 1973315 := bstep (se 1 (by rfl) ⟨1479986, by rfl⟩ : syracuseStep 1973315 = 2959973) B2959973
theorem B1973443 : Blo 1168401 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B4439245 : Blo 1168401 4439245 := bstep (se 3 (by rfl) ⟨832358, by rfl⟩ : syracuseStep 4439245 = 1664717) B1664717
theorem B4218083 : Blo 1168401 4218083 := bstep (se 1 (by rfl) ⟨3163562, by rfl⟩ : syracuseStep 4218083 = 6327125) B6327125
theorem B7486769 : Blo 1168401 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B1973585 : Blo 1168401 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B3947885 : Blo 1168401 3947885 := bstep (se 3 (by rfl) ⟨740228, by rfl⟩ : syracuseStep 3947885 = 1480457) B1480457
theorem B2219395 : Blo 1168401 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B3947939 : Blo 1168401 3947939 := bstep (se 1 (by rfl) ⟨2960954, by rfl⟩ : syracuseStep 3947939 = 5921909) B5921909
theorem B1424803 : Blo 1168401 1424803 := bstep (se 1 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 1424803 = 2137205) B2137205
theorem B1973713 : Blo 1168401 1973713 := bstep (se 2 (by rfl) ⟨740142, by rfl⟩ : syracuseStep 1973713 = 1480285) B1480285
theorem B2498033 : Blo 1168401 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B1973747 : Blo 1168401 1973747 := bstep (se 1 (by rfl) ⟨1480310, by rfl⟩ : syracuseStep 1973747 = 2960621) B2960621
theorem B6659597 : Blo 1168401 6659597 := bstep (se 3 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 6659597 = 2497349) B2497349
theorem B1777169 : Blo 1168401 1777169 := bstep (se 2 (by rfl) ⟨666438, by rfl⟩ : syracuseStep 1777169 = 1332877) B1332877
theorem B1752611 : Blo 1168401 1752611 := bstep (se 1 (by rfl) ⟨1314458, by rfl⟩ : syracuseStep 1752611 = 2628917) B2628917
theorem B2219555 : Blo 1168401 2219555 := bstep (se 1 (by rfl) ⟨1664666, by rfl⟩ : syracuseStep 2219555 = 3329333) B3329333
theorem B2629169 : Blo 1168401 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B1752641 : Blo 1168401 1752641 := bstep (se 2 (by rfl) ⟨657240, by rfl⟩ : syracuseStep 1752641 = 1314481) B1314481
theorem B2629187 : Blo 1168401 2629187 := bstep (se 1 (by rfl) ⟨1971890, by rfl⟩ : syracuseStep 2629187 = 3943781) B3943781
theorem B1752659 : Blo 1168401 1752659 := bstep (se 1 (by rfl) ⟨1314494, by rfl⟩ : syracuseStep 1752659 = 2628989) B2628989
theorem B1752689 : Blo 1168401 1752689 := bstep (se 2 (by rfl) ⟨657258, by rfl⟩ : syracuseStep 1752689 = 1314517) B1314517
theorem B1973875 : Blo 1168401 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B1752707 : Blo 1168401 1752707 := bstep (se 1 (by rfl) ⟨1314530, by rfl⟩ : syracuseStep 1752707 = 2629061) B2629061
theorem B1801873 : Blo 1168401 1801873 := bstep (se 2 (by rfl) ⟨675702, by rfl⟩ : syracuseStep 1801873 = 1351405) B1351405
theorem B1752737 : Blo 1168401 1752737 := bstep (se 2 (by rfl) ⟨657276, by rfl⟩ : syracuseStep 1752737 = 1314553) B1314553
theorem B3948209 : Blo 1168401 3948209 := bstep (se 2 (by rfl) ⟨1480578, by rfl⟩ : syracuseStep 3948209 = 2961157) B2961157
theorem B1752755 : Blo 1168401 1752755 := bstep (se 1 (by rfl) ⟨1314566, by rfl⟩ : syracuseStep 1752755 = 2629133) B2629133
theorem B1752785 : Blo 1168401 1752785 := bstep (se 2 (by rfl) ⟨657294, by rfl⟩ : syracuseStep 1752785 = 1314589) B1314589
theorem B56884949 : Blo 1168401 56884949 := bstep (se 7 (by rfl) ⟨666620, by rfl⟩ : syracuseStep 56884949 = 1333241) B1333241
theorem B1752803 : Blo 1168401 1752803 := bstep (se 1 (by rfl) ⟨1314602, by rfl⟩ : syracuseStep 1752803 = 2629205) B2629205
theorem B1752833 : Blo 1168401 1752833 := bstep (se 2 (by rfl) ⟨657312, by rfl⟩ : syracuseStep 1752833 = 1314625) B1314625
theorem B1974017 : Blo 1168401 1974017 := bstep (se 2 (by rfl) ⟨740256, by rfl⟩ : syracuseStep 1974017 = 1480513) B1480513
theorem B1752851 : Blo 1168401 1752851 := bstep (se 1 (by rfl) ⟨1314638, by rfl⟩ : syracuseStep 1752851 = 2629277) B2629277
theorem B1752881 : Blo 1168401 1752881 := bstep (se 2 (by rfl) ⟨657330, by rfl⟩ : syracuseStep 1752881 = 1314661) B1314661
theorem B1752899 : Blo 1168401 1752899 := bstep (se 1 (by rfl) ⟨1314674, by rfl⟩ : syracuseStep 1752899 = 2629349) B2629349
theorem B2629457 : Blo 1168401 2629457 := bstep (se 2 (by rfl) ⟨986046, by rfl⟩ : syracuseStep 2629457 = 1972093) B1972093
theorem B1752929 : Blo 1168401 1752929 := bstep (se 2 (by rfl) ⟨657348, by rfl⟩ : syracuseStep 1752929 = 1314697) B1314697
theorem B2629475 : Blo 1168401 2629475 := bstep (se 1 (by rfl) ⟨1972106, by rfl⟩ : syracuseStep 2629475 = 3944213) B3944213
theorem B1752947 : Blo 1168401 1752947 := bstep (se 1 (by rfl) ⟨1314710, by rfl⟩ : syracuseStep 1752947 = 2629421) B2629421
theorem B1974145 : Blo 1168401 1974145 := bstep (se 2 (by rfl) ⟨740304, by rfl⟩ : syracuseStep 1974145 = 1480609) B1480609
theorem B2498435 : Blo 1168401 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B1752977 : Blo 1168401 1752977 := bstep (se 2 (by rfl) ⟨657366, by rfl⟩ : syracuseStep 1752977 = 1314733) B1314733
theorem B1752995 : Blo 1168401 1752995 := bstep (se 1 (by rfl) ⟨1314746, by rfl⟩ : syracuseStep 1752995 = 2629493) B2629493
theorem B1974179 : Blo 1168401 1974179 := bstep (se 1 (by rfl) ⟨1480634, by rfl⟩ : syracuseStep 1974179 = 2961269) B2961269
theorem B1753025 : Blo 1168401 1753025 := bstep (se 2 (by rfl) ⟨657384, by rfl⟩ : syracuseStep 1753025 = 1314769) B1314769
theorem B1753043 : Blo 1168401 1753043 := bstep (se 1 (by rfl) ⟨1314782, by rfl⟩ : syracuseStep 1753043 = 2629565) B2629565
theorem B4440035 : Blo 1168401 4440035 := bstep (se 1 (by rfl) ⟨3330026, by rfl⟩ : syracuseStep 4440035 = 6660053) B6660053
theorem B1753073 : Blo 1168401 1753073 := bstep (se 2 (by rfl) ⟨657402, by rfl⟩ : syracuseStep 1753073 = 1314805) B1314805
theorem B2629655 : Blo 1168401 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B3743795 : Blo 1168401 3743795 := bstep (se 1 (by rfl) ⟨2807846, by rfl⟩ : syracuseStep 3743795 = 5615693) B5615693
theorem B5922881 : Blo 1168401 5922881 := bstep (se 2 (by rfl) ⟨2221080, by rfl⟩ : syracuseStep 5922881 = 4442161) B4442161
theorem B1753163 : Blo 1168401 1753163 := bstep (se 1 (by rfl) ⟨1314872, by rfl⟩ : syracuseStep 1753163 = 2629745) B2629745
theorem B1753175 : Blo 1168401 1753175 := bstep (se 1 (by rfl) ⟨1314881, by rfl⟩ : syracuseStep 1753175 = 2629763) B2629763
theorem B1974361 : Blo 1168401 1974361 := bstep (se 2 (by rfl) ⟨740385, by rfl⟩ : syracuseStep 1974361 = 1480771) B1480771
theorem B3948695 : Blo 1168401 3948695 := bstep (se 1 (by rfl) ⟨2961521, by rfl⟩ : syracuseStep 3948695 = 5923043) B5923043
theorem B1753241 : Blo 1168401 1753241 := bstep (se 2 (by rfl) ⟨657465, by rfl⟩ : syracuseStep 1753241 = 1314931) B1314931
theorem B2220185 : Blo 1168401 2220185 := bstep (se 2 (by rfl) ⟨832569, by rfl⟩ : syracuseStep 2220185 = 1665139) B1665139
theorem B2629835 : Blo 1168401 2629835 := bstep (se 1 (by rfl) ⟨1972376, by rfl⟩ : syracuseStep 2629835 = 3944753) B3944753
theorem B2629889 : Blo 1168401 2629889 := bstep (se 2 (by rfl) ⟨986208, by rfl⟩ : syracuseStep 2629889 = 1972417) B1972417
theorem B1753355 : Blo 1168401 1753355 := bstep (se 1 (by rfl) ⟨1315016, by rfl⟩ : syracuseStep 1753355 = 2630033) B2630033
theorem B1753367 : Blo 1168401 1753367 := bstep (se 1 (by rfl) ⟨1315025, by rfl⟩ : syracuseStep 1753367 = 2630051) B2630051
theorem B1753433 : Blo 1168401 1753433 := bstep (se 2 (by rfl) ⟨657537, by rfl⟩ : syracuseStep 1753433 = 1315075) B1315075
theorem B7487923 : Blo 1168401 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B1753547 : Blo 1168401 1753547 := bstep (se 1 (by rfl) ⟨1315160, by rfl⟩ : syracuseStep 1753547 = 2630321) B2630321
theorem B1753559 : Blo 1168401 1753559 := bstep (se 1 (by rfl) ⟨1315169, by rfl⟩ : syracuseStep 1753559 = 2630339) B2630339
theorem B2630105 : Blo 1168401 2630105 := bstep (se 2 (by rfl) ⟨986289, by rfl⟩ : syracuseStep 2630105 = 1972579) B1972579
theorem B1753625 : Blo 1168401 1753625 := bstep (se 2 (by rfl) ⟨657609, by rfl⟩ : syracuseStep 1753625 = 1315219) B1315219
theorem B6840877 : Blo 1168401 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B2630195 : Blo 1168401 2630195 := bstep (se 1 (by rfl) ⟨1972646, by rfl⟩ : syracuseStep 2630195 = 3945293) B3945293
theorem B2630231 : Blo 1168401 2630231 := bstep (se 1 (by rfl) ⟨1972673, by rfl⟩ : syracuseStep 2630231 = 3945347) B3945347
theorem B2499187 : Blo 1168401 2499187 := bstep (se 1 (by rfl) ⟨1874390, by rfl⟩ : syracuseStep 2499187 = 3748781) B3748781
theorem B5915267 : Blo 1168401 5915267 := bstep (se 1 (by rfl) ⟨4436450, by rfl⟩ : syracuseStep 5915267 = 8872901) B8872901
theorem B1753739 : Blo 1168401 1753739 := bstep (se 1 (by rfl) ⟨1315304, by rfl⟩ : syracuseStep 1753739 = 2630609) B2630609
theorem B1753751 : Blo 1168401 1753751 := bstep (se 1 (by rfl) ⟨1315313, by rfl⟩ : syracuseStep 1753751 = 2630627) B2630627
theorem B1974935 : Blo 1168401 1974935 := bstep (se 1 (by rfl) ⟨1481201, by rfl⟩ : syracuseStep 1974935 = 2962403) B2962403
theorem B3949235 : Blo 1168401 3949235 := bstep (se 1 (by rfl) ⟨2961926, by rfl⟩ : syracuseStep 3949235 = 5923853) B5923853
theorem B1753817 : Blo 1168401 1753817 := bstep (se 2 (by rfl) ⟨657681, by rfl⟩ : syracuseStep 1753817 = 1315363) B1315363
theorem B2630411 : Blo 1168401 2630411 := bstep (se 1 (by rfl) ⟨1972808, by rfl⟩ : syracuseStep 2630411 = 3945617) B3945617
theorem B4743953 : Blo 1168401 4743953 := bstep (se 2 (by rfl) ⟨1778982, by rfl⟩ : syracuseStep 4743953 = 3557965) B3557965
theorem B2630465 : Blo 1168401 2630465 := bstep (se 2 (by rfl) ⟨986424, by rfl⟩ : syracuseStep 2630465 = 1972849) B1972849
theorem B1753931 : Blo 1168401 1753931 := bstep (se 1 (by rfl) ⟨1315448, by rfl⟩ : syracuseStep 1753931 = 2630897) B2630897
theorem B4997963 : Blo 1168401 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B1753943 : Blo 1168401 1753943 := bstep (se 1 (by rfl) ⟨1315457, by rfl⟩ : syracuseStep 1753943 = 2630915) B2630915
theorem B15991669 : Blo 1168401 15991669 := bstep (se 5 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 15991669 = 1499219) B1499219
theorem B2220929 : Blo 1168401 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B4440977 : Blo 1168401 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1663897 : Blo 1168401 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B1754009 : Blo 1168401 1754009 := bstep (se 2 (by rfl) ⟨657753, by rfl⟩ : syracuseStep 1754009 = 1315507) B1315507
theorem B3949505 : Blo 1168401 3949505 := bstep (se 2 (by rfl) ⟨1481064, by rfl⟩ : syracuseStep 3949505 = 2962129) B2962129
theorem B1664011 : Blo 1168401 1664011 := bstep (se 1 (by rfl) ⟨1248008, by rfl⟩ : syracuseStep 1664011 = 2496017) B2496017
theorem B1754123 : Blo 1168401 1754123 := bstep (se 1 (by rfl) ⟨1315592, by rfl⟩ : syracuseStep 1754123 = 2631185) B2631185
theorem B1754135 : Blo 1168401 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B2630681 : Blo 1168401 2630681 := bstep (se 2 (by rfl) ⟨986505, by rfl⟩ : syracuseStep 2630681 = 1973011) B1973011
theorem B1754201 : Blo 1168401 1754201 := bstep (se 2 (by rfl) ⟨657825, by rfl⟩ : syracuseStep 1754201 = 1315651) B1315651
theorem B2499673 : Blo 1168401 2499673 := bstep (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) B1874755
theorem B8004701 : Blo 1168401 8004701 := bstep (se 3 (by rfl) ⟨1500881, by rfl⟩ : syracuseStep 8004701 = 3001763) B3001763
theorem B2630771 : Blo 1168401 2630771 := bstep (se 1 (by rfl) ⟨1973078, by rfl⟩ : syracuseStep 2630771 = 3946157) B3946157
theorem B2221195 : Blo 1168401 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B2630807 : Blo 1168401 2630807 := bstep (se 1 (by rfl) ⟨1973105, by rfl⟩ : syracuseStep 2630807 = 3946211) B3946211
theorem B2958515 : Blo 1168401 2958515 := bstep (se 1 (by rfl) ⟨2218886, by rfl⟩ : syracuseStep 2958515 = 4437773) B4437773
theorem B1754315 : Blo 1168401 1754315 := bstep (se 1 (by rfl) ⟨1315736, by rfl⟩ : syracuseStep 1754315 = 2631473) B2631473
theorem B1754327 : Blo 1168401 1754327 := bstep (se 1 (by rfl) ⟨1315745, by rfl⟩ : syracuseStep 1754327 = 2631491) B2631491
theorem B1754393 : Blo 1168401 1754393 := bstep (se 2 (by rfl) ⟨657897, by rfl⟩ : syracuseStep 1754393 = 1315795) B1315795
theorem B7595309 : Blo 1168401 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B2630987 : Blo 1168401 2630987 := bstep (se 1 (by rfl) ⟨1973240, by rfl⟩ : syracuseStep 2630987 = 3946481) B3946481
theorem B2631041 : Blo 1168401 2631041 := bstep (se 2 (by rfl) ⟨986640, by rfl⟩ : syracuseStep 2631041 = 1973281) B1973281
theorem B8422787 : Blo 1168401 8422787 := bstep (se 1 (by rfl) ⟨6317090, by rfl⟩ : syracuseStep 8422787 = 12634181) B12634181
theorem B6751619 : Blo 1168401 6751619 := bstep (se 1 (by rfl) ⟨5063714, by rfl⟩ : syracuseStep 6751619 = 10127429) B10127429
theorem B1754507 : Blo 1168401 1754507 := bstep (se 1 (by rfl) ⟨1315880, by rfl⟩ : syracuseStep 1754507 = 2631761) B2631761
theorem B1754519 : Blo 1168401 1754519 := bstep (se 1 (by rfl) ⟨1315889, by rfl⟩ : syracuseStep 1754519 = 2631779) B2631779
theorem B1754585 : Blo 1168401 1754585 := bstep (se 2 (by rfl) ⟨657969, by rfl⟩ : syracuseStep 1754585 = 1315939) B1315939
theorem B3950045 : Blo 1168401 3950045 := bstep (se 3 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 3950045 = 1481267) B1481267
theorem B13321745 : Blo 1168401 13321745 := bstep (se 2 (by rfl) ⟨4995654, by rfl⟩ : syracuseStep 13321745 = 9991309) B9991309
theorem B2000459 : Blo 1168401 2000459 := bstep (se 1 (by rfl) ⟨1500344, by rfl⟩ : syracuseStep 2000459 = 3000689) B3000689
theorem B1754699 : Blo 1168401 1754699 := bstep (se 1 (by rfl) ⟨1316024, by rfl⟩ : syracuseStep 1754699 = 2632049) B2632049
theorem B4441675 : Blo 1168401 4441675 := bstep (se 1 (by rfl) ⟨3331256, by rfl⟩ : syracuseStep 4441675 = 6662513) B6662513
theorem B2221643 : Blo 1168401 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B1754711 : Blo 1168401 1754711 := bstep (se 1 (by rfl) ⟨1316033, by rfl⟩ : syracuseStep 1754711 = 2632067) B2632067
theorem B2631257 : Blo 1168401 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B4212317 : Blo 1168401 4212317 := bstep (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) B1579619
theorem B6661763 : Blo 1168401 6661763 := bstep (se 1 (by rfl) ⟨4996322, by rfl⟩ : syracuseStep 6661763 = 9992645) B9992645
theorem B1754777 : Blo 1168401 1754777 := bstep (se 2 (by rfl) ⟨658041, by rfl⟩ : syracuseStep 1754777 = 1316083) B1316083
theorem B2631347 : Blo 1168401 2631347 := bstep (se 1 (by rfl) ⟨1973510, by rfl⟩ : syracuseStep 2631347 = 3947021) B3947021
theorem B2959051 : Blo 1168401 2959051 := bstep (se 1 (by rfl) ⟨2219288, by rfl⟩ : syracuseStep 2959051 = 4438577) B4438577
theorem B17098445 : Blo 1168401 17098445 := bstep (se 3 (by rfl) ⟨3205958, by rfl⟩ : syracuseStep 17098445 = 6411917) B6411917
theorem B2631383 : Blo 1168401 2631383 := bstep (se 1 (by rfl) ⟨1973537, by rfl⟩ : syracuseStep 2631383 = 3947075) B3947075
theorem B2221825 : Blo 1168401 2221825 := bstep (se 2 (by rfl) ⟨833184, by rfl⟩ : syracuseStep 2221825 = 1666369) B1666369
theorem B1754891 : Blo 1168401 1754891 := bstep (se 1 (by rfl) ⟨1316168, by rfl⟩ : syracuseStep 1754891 = 2632337) B2632337
theorem B1754903 : Blo 1168401 1754903 := bstep (se 1 (by rfl) ⟨1316177, by rfl⟩ : syracuseStep 1754903 = 2632355) B2632355
theorem B4998935 : Blo 1168401 4998935 := bstep (se 1 (by rfl) ⟨3749201, by rfl⟩ : syracuseStep 4998935 = 7498403) B7498403
theorem B3999563 : Blo 1168401 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B2959193 : Blo 1168401 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B1754969 : Blo 1168401 1754969 := bstep (se 2 (by rfl) ⟨658113, by rfl⟩ : syracuseStep 1754969 = 1316227) B1316227
theorem B4441949 : Blo 1168401 4441949 := bstep (se 3 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 4441949 = 1665731) B1665731
theorem B14215013 : Blo 1168401 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B16869221 : Blo 1168401 16869221 := bstep (se 4 (by rfl) ⟨1581489, by rfl⟩ : syracuseStep 16869221 = 3162979) B3162979
theorem B2631563 : Blo 1168401 2631563 := bstep (se 1 (by rfl) ⟨1973672, by rfl⟩ : syracuseStep 2631563 = 3947345) B3947345
theorem B4990871 : Blo 1168401 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B12642227 : Blo 1168401 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B2631617 : Blo 1168401 2631617 := bstep (se 2 (by rfl) ⟨986856, by rfl⟩ : syracuseStep 2631617 = 1973713) B1973713
theorem B1755083 : Blo 1168401 1755083 := bstep (se 1 (by rfl) ⟨1316312, by rfl⟩ : syracuseStep 1755083 = 2632625) B2632625
theorem B1755095 : Blo 1168401 1755095 := bstep (se 1 (by rfl) ⟨1316321, by rfl⟩ : syracuseStep 1755095 = 2632643) B2632643
theorem B5924825 : Blo 1168401 5924825 := bstep (se 2 (by rfl) ⟨2221809, by rfl⟩ : syracuseStep 5924825 = 4443619) B4443619
theorem B1755161 : Blo 1168401 1755161 := bstep (se 2 (by rfl) ⟨658185, by rfl⟩ : syracuseStep 1755161 = 1316371) B1316371
theorem B5335085 : Blo 1168401 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B54716485 : Blo 1168401 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B1755275 : Blo 1168401 1755275 := bstep (se 1 (by rfl) ⟨1316456, by rfl⟩ : syracuseStep 1755275 = 2632913) B2632913
theorem B4212881 : Blo 1168401 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B1755287 : Blo 1168401 1755287 := bstep (se 1 (by rfl) ⟨1316465, by rfl⟩ : syracuseStep 1755287 = 2632931) B2632931
theorem B2631833 : Blo 1168401 2631833 := bstep (se 2 (by rfl) ⟨986937, by rfl⟩ : syracuseStep 2631833 = 1973875) B1973875
theorem B2812055 : Blo 1168401 2812055 := bstep (se 1 (by rfl) ⟨2109041, by rfl⟩ : syracuseStep 2812055 = 4218083) B4218083
theorem B2402497 : Blo 1168401 2402497 := bstep (se 2 (by rfl) ⟨900936, by rfl⟩ : syracuseStep 2402497 = 1801873) B1801873
theorem B4991179 : Blo 1168401 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B1755353 : Blo 1168401 1755353 := bstep (se 2 (by rfl) ⟨658257, by rfl⟩ : syracuseStep 1755353 = 1316515) B1316515
theorem B2631923 : Blo 1168401 2631923 := bstep (se 1 (by rfl) ⟨1973942, by rfl⟩ : syracuseStep 2631923 = 3947885) B3947885
theorem B2631959 : Blo 1168401 2631959 := bstep (se 1 (by rfl) ⟨1973969, by rfl⟩ : syracuseStep 2631959 = 3947939) B3947939
theorem B1665355 : Blo 1168401 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B1755467 : Blo 1168401 1755467 := bstep (se 1 (by rfl) ⟨1316600, by rfl⟩ : syracuseStep 1755467 = 2633201) B2633201
theorem B1755479 : Blo 1168401 1755479 := bstep (se 1 (by rfl) ⟨1316609, by rfl⟩ : syracuseStep 1755479 = 2633219) B2633219
theorem B1755545 : Blo 1168401 1755545 := bstep (se 2 (by rfl) ⟨658329, by rfl⟩ : syracuseStep 1755545 = 1316659) B1316659
theorem B2632139 : Blo 1168401 2632139 := bstep (se 1 (by rfl) ⟨1974104, by rfl⟩ : syracuseStep 2632139 = 3948209) B3948209
theorem B4991453 : Blo 1168401 4991453 := bstep (se 3 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 4991453 = 1871795) B1871795
theorem B37923299 : Blo 1168401 37923299 := bstep (se 1 (by rfl) ⟨28442474, by rfl⟩ : syracuseStep 37923299 = 56884949) B56884949
theorem B1247735 : Blo 1168401 1247735 := bstep (se 1 (by rfl) ⟨935801, by rfl⟩ : syracuseStep 1247735 = 1871603) B1871603
theorem B2632193 : Blo 1168401 2632193 := bstep (se 2 (by rfl) ⟨987072, by rfl⟩ : syracuseStep 2632193 = 1974145) B1974145
theorem B4442647 : Blo 1168401 4442647 := bstep (se 1 (by rfl) ⟨3331985, by rfl⟩ : syracuseStep 4442647 = 6663971) B6663971
theorem B3000883 : Blo 1168401 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B1665623 : Blo 1168401 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B2960023 : Blo 1168401 2960023 := bstep (se 1 (by rfl) ⟨2220017, by rfl⟩ : syracuseStep 2960023 = 4440035) B4440035
theorem B3328705 : Blo 1168401 3328705 := bstep (se 2 (by rfl) ⟨1248264, by rfl⟩ : syracuseStep 3328705 = 2496529) B2496529
theorem B5065409 : Blo 1168401 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B2632409 : Blo 1168401 2632409 := bstep (se 2 (by rfl) ⟨987153, by rfl⟩ : syracuseStep 2632409 = 1974307) B1974307
theorem B2632499 : Blo 1168401 2632499 := bstep (se 1 (by rfl) ⟨1974374, by rfl⟩ : syracuseStep 2632499 = 3948749) B3948749
theorem B2632535 : Blo 1168401 2632535 := bstep (se 1 (by rfl) ⟨1974401, by rfl⟩ : syracuseStep 2632535 = 3948803) B3948803
theorem B8874845 : Blo 1168401 8874845 := bstep (se 3 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 8874845 = 3328067) B3328067
theorem B28437425 : Blo 1168401 28437425 := bstep (se 2 (by rfl) ⟨10664034, by rfl⟩ : syracuseStep 28437425 = 21328069) B21328069
theorem B2632715 : Blo 1168401 2632715 := bstep (se 1 (by rfl) ⟨1974536, by rfl⟩ : syracuseStep 2632715 = 3949073) B3949073
theorem B2632769 : Blo 1168401 2632769 := bstep (se 2 (by rfl) ⟨987288, by rfl⟩ : syracuseStep 2632769 = 1974577) B1974577
theorem B9743435 : Blo 1168401 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B2960459 : Blo 1168401 2960459 := bstep (se 1 (by rfl) ⟨2220344, by rfl⟩ : syracuseStep 2960459 = 4440689) B4440689
theorem B205090019 : Blo 1168401 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B2632985 : Blo 1168401 2632985 := bstep (se 2 (by rfl) ⟨987369, by rfl⟩ : syracuseStep 2632985 = 1974739) B1974739
theorem B4443437 : Blo 1168401 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B2633075 : Blo 1168401 2633075 := bstep (se 1 (by rfl) ⟨1974806, by rfl⟩ : syracuseStep 2633075 = 3949613) B3949613
theorem B36015509 : Blo 1168401 36015509 := bstep (se 6 (by rfl) ⟨844113, by rfl⟩ : syracuseStep 36015509 = 1688227) B1688227
theorem B2633111 : Blo 1168401 2633111 := bstep (se 1 (by rfl) ⟨1974833, by rfl⟩ : syracuseStep 2633111 = 3949667) B3949667
theorem B2960833 : Blo 1168401 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B2633291 : Blo 1168401 2633291 := bstep (se 1 (by rfl) ⟨1974968, by rfl⟩ : syracuseStep 2633291 = 3949937) B3949937
theorem B2633345 : Blo 1168401 2633345 := bstep (se 2 (by rfl) ⟨987504, by rfl⟩ : syracuseStep 2633345 = 1975009) B1975009
theorem B1314571 : Blo 1168401 1314571 := bstep (se 1 (by rfl) ⟨985928, by rfl⟩ : syracuseStep 1314571 = 1971857) B1971857
theorem B4992785 : Blo 1168401 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B3944267 : Blo 1168401 3944267 := bstep (se 1 (by rfl) ⟨2958200, by rfl⟩ : syracuseStep 3944267 = 5916401) B5916401
theorem B1871705 : Blo 1168401 1871705 := bstep (se 2 (by rfl) ⟨701889, by rfl⟩ : syracuseStep 1871705 = 1403779) B1403779
theorem B1314679 : Blo 1168401 1314679 := bstep (se 1 (by rfl) ⟨986009, by rfl⟩ : syracuseStep 1314679 = 1972019) B1972019
theorem B2371457 : Blo 1168401 2371457 := bstep (se 2 (by rfl) ⟨889296, by rfl⟩ : syracuseStep 2371457 = 1778593) B1778593
theorem B1871833 : Blo 1168401 1871833 := bstep (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) B1403875
theorem B6664153 : Blo 1168401 6664153 := bstep (se 2 (by rfl) ⟨2499057, by rfl⟩ : syracuseStep 6664153 = 4998115) B4998115
theorem B2961431 : Blo 1168401 2961431 := bstep (se 1 (by rfl) ⟨2221073, by rfl⟩ : syracuseStep 2961431 = 4442147) B4442147
theorem B9007139 : Blo 1168401 9007139 := bstep (se 1 (by rfl) ⟨6755354, by rfl⟩ : syracuseStep 9007139 = 13510709) B13510709
theorem B1314859 : Blo 1168401 1314859 := bstep (se 1 (by rfl) ⟨986144, by rfl⟩ : syracuseStep 1314859 = 1972289) B1972289
theorem B3944537 : Blo 1168401 3944537 := bstep (se 2 (by rfl) ⟨1479201, by rfl⟩ : syracuseStep 3944537 = 2958403) B2958403
theorem B2371699 : Blo 1168401 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B1314967 : Blo 1168401 1314967 := bstep (se 1 (by rfl) ⟨986225, by rfl⟩ : syracuseStep 1314967 = 1972451) B1972451
theorem B5918993 : Blo 1168401 5918993 := bstep (se 2 (by rfl) ⟨2219622, by rfl⟩ : syracuseStep 5918993 = 4439245) B4439245
theorem B1315147 : Blo 1168401 1315147 := bstep (se 1 (by rfl) ⟨986360, by rfl⟩ : syracuseStep 1315147 = 1972721) B1972721
theorem B5337419 : Blo 1168401 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B1478999 : Blo 1168401 1478999 := bstep (se 1 (by rfl) ⟨1109249, by rfl⟩ : syracuseStep 1478999 = 2218499) B2218499
theorem B13324661 : Blo 1168401 13324661 := bstep (se 5 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 13324661 = 1249187) B1249187
theorem B5919155 : Blo 1168401 5919155 := bstep (se 1 (by rfl) ⟨4439366, by rfl⟩ : syracuseStep 5919155 = 8878733) B8878733
theorem B1315255 : Blo 1168401 1315255 := bstep (se 1 (by rfl) ⟨986441, by rfl⟩ : syracuseStep 1315255 = 1972883) B1972883
theorem B1315435 : Blo 1168401 1315435 := bstep (se 1 (by rfl) ⟨986576, by rfl⟩ : syracuseStep 1315435 = 1973153) B1973153
theorem B1282699 : Blo 1168401 1282699 := bstep (se 1 (by rfl) ⟨962024, by rfl⟩ : syracuseStep 1282699 = 1924049) B1924049
theorem B5616307 : Blo 1168401 5616307 := bstep (se 1 (by rfl) ⟨4212230, by rfl⟩ : syracuseStep 5616307 = 8424461) B8424461
theorem B1405643 : Blo 1168401 1405643 := bstep (se 1 (by rfl) ⟨1054232, by rfl⟩ : syracuseStep 1405643 = 2108465) B2108465
theorem B1315543 : Blo 1168401 1315543 := bstep (se 1 (by rfl) ⟨986657, by rfl⟩ : syracuseStep 1315543 = 1973315) B1973315
theorem B3945239 : Blo 1168401 3945239 := bstep (se 1 (by rfl) ⟨2958929, by rfl⟩ : syracuseStep 3945239 = 5917859) B5917859
theorem B4436801 : Blo 1168401 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B2962241 : Blo 1168401 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B1315723 : Blo 1168401 1315723 := bstep (se 1 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 1315723 = 1973585) B1973585
theorem B6665111 : Blo 1168401 6665111 := bstep (se 1 (by rfl) ⟨4998833, by rfl⟩ : syracuseStep 6665111 = 9997667) B9997667
theorem B1315831 : Blo 1168401 1315831 := bstep (se 1 (by rfl) ⟨986873, by rfl⟩ : syracuseStep 1315831 = 1973747) B1973747
theorem B2135041 : Blo 1168401 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1184779 : Blo 1168401 1184779 := bstep (se 1 (by rfl) ⟨888584, by rfl⟩ : syracuseStep 1184779 = 1777169) B1777169
theorem B1168407 : Blo 1168401 1168407 := bstep (se 1 (by rfl) ⟨876305, by rfl⟩ : syracuseStep 1168407 = 1752611) B1752611
theorem B1479703 : Blo 1168401 1479703 := bstep (se 1 (by rfl) ⟨1109777, by rfl⟩ : syracuseStep 1479703 = 2219555) B2219555
theorem B1168427 : Blo 1168401 1168427 := bstep (se 1 (by rfl) ⟨876320, by rfl⟩ : syracuseStep 1168427 = 1752641) B1752641
theorem B1168439 : Blo 1168401 1168439 := bstep (se 1 (by rfl) ⟨876329, by rfl⟩ : syracuseStep 1168439 = 1752659) B1752659
theorem B1168459 : Blo 1168401 1168459 := bstep (se 1 (by rfl) ⟨876344, by rfl⟩ : syracuseStep 1168459 = 1752689) B1752689
theorem B1168471 : Blo 1168401 1168471 := bstep (se 1 (by rfl) ⟨876353, by rfl⟩ : syracuseStep 1168471 = 1752707) B1752707
theorem B8434781 : Blo 1168401 8434781 := bstep (se 3 (by rfl) ⟨1581521, by rfl⟩ : syracuseStep 8434781 = 3163043) B3163043
theorem B1168491 : Blo 1168401 1168491 := bstep (se 1 (by rfl) ⟨876368, by rfl⟩ : syracuseStep 1168491 = 1752737) B1752737
theorem B1168503 : Blo 1168401 1168503 := bstep (se 1 (by rfl) ⟨876377, by rfl⟩ : syracuseStep 1168503 = 1752755) B1752755
theorem B1168523 : Blo 1168401 1168523 := bstep (se 1 (by rfl) ⟨876392, by rfl⟩ : syracuseStep 1168523 = 1752785) B1752785
theorem B1168535 : Blo 1168401 1168535 := bstep (se 1 (by rfl) ⟨876401, by rfl⟩ : syracuseStep 1168535 = 1752803) B1752803
theorem B1168555 : Blo 1168401 1168555 := bstep (se 1 (by rfl) ⟨876416, by rfl⟩ : syracuseStep 1168555 = 1752833) B1752833
theorem B1316011 : Blo 1168401 1316011 := bstep (se 1 (by rfl) ⟨987008, by rfl⟩ : syracuseStep 1316011 = 1974017) B1974017
theorem B1168567 : Blo 1168401 1168567 := bstep (se 1 (by rfl) ⟨876425, by rfl⟩ : syracuseStep 1168567 = 1752851) B1752851
theorem B1168587 : Blo 1168401 1168587 := bstep (se 1 (by rfl) ⟨876440, by rfl⟩ : syracuseStep 1168587 = 1752881) B1752881
theorem B1168599 : Blo 1168401 1168599 := bstep (se 1 (by rfl) ⟨876449, by rfl⟩ : syracuseStep 1168599 = 1752899) B1752899
theorem B1168619 : Blo 1168401 1168619 := bstep (se 1 (by rfl) ⟨876464, by rfl⟩ : syracuseStep 1168619 = 1752929) B1752929
theorem B1168631 : Blo 1168401 1168631 := bstep (se 1 (by rfl) ⟨876473, by rfl⟩ : syracuseStep 1168631 = 1752947) B1752947
theorem B1168651 : Blo 1168401 1168651 := bstep (se 1 (by rfl) ⟨876488, by rfl⟩ : syracuseStep 1168651 = 1752977) B1752977
theorem B1168663 : Blo 1168401 1168663 := bstep (se 1 (by rfl) ⟨876497, by rfl⟩ : syracuseStep 1168663 = 1752995) B1752995
theorem B1316119 : Blo 1168401 1316119 := bstep (se 1 (by rfl) ⟨987089, by rfl⟩ : syracuseStep 1316119 = 1974179) B1974179
theorem B1168683 : Blo 1168401 1168683 := bstep (se 1 (by rfl) ⟨876512, by rfl⟩ : syracuseStep 1168683 = 1753025) B1753025
theorem B3945779 : Blo 1168401 3945779 := bstep (se 1 (by rfl) ⟨2959334, by rfl⟩ : syracuseStep 3945779 = 5918669) B5918669
theorem B1168695 : Blo 1168401 1168695 := bstep (se 1 (by rfl) ⟨876521, by rfl⟩ : syracuseStep 1168695 = 1753043) B1753043
theorem B1168715 : Blo 1168401 1168715 := bstep (se 1 (by rfl) ⟨876536, by rfl⟩ : syracuseStep 1168715 = 1753073) B1753073
theorem B1168727 : Blo 1168401 1168727 := bstep (se 1 (by rfl) ⟨876545, by rfl⟩ : syracuseStep 1168727 = 1753091) B1753091
theorem B1168747 : Blo 1168401 1168747 := bstep (se 1 (by rfl) ⟨876560, by rfl⟩ : syracuseStep 1168747 = 1753121) B1753121
theorem B1168759 : Blo 1168401 1168759 := bstep (se 1 (by rfl) ⟨876569, by rfl⟩ : syracuseStep 1168759 = 1753139) B1753139
theorem B1168779 : Blo 1168401 1168779 := bstep (se 1 (by rfl) ⟨876584, by rfl⟩ : syracuseStep 1168779 = 1753169) B1753169
theorem B1168791 : Blo 1168401 1168791 := bstep (se 1 (by rfl) ⟨876593, by rfl⟩ : syracuseStep 1168791 = 1753187) B1753187
theorem B1168811 : Blo 1168401 1168811 := bstep (se 1 (by rfl) ⟨876608, by rfl⟩ : syracuseStep 1168811 = 1753217) B1753217
theorem B1168823 : Blo 1168401 1168823 := bstep (se 1 (by rfl) ⟨876617, by rfl⟩ : syracuseStep 1168823 = 1753235) B1753235
theorem B1168843 : Blo 1168401 1168843 := bstep (se 1 (by rfl) ⟨876632, by rfl⟩ : syracuseStep 1168843 = 1753265) B1753265
theorem B1316299 : Blo 1168401 1316299 := bstep (se 1 (by rfl) ⟨987224, by rfl⟩ : syracuseStep 1316299 = 1974449) B1974449
theorem B1168855 : Blo 1168401 1168855 := bstep (se 1 (by rfl) ⟨876641, by rfl⟩ : syracuseStep 1168855 = 1753283) B1753283
theorem B1168875 : Blo 1168401 1168875 := bstep (se 1 (by rfl) ⟨876656, by rfl⟩ : syracuseStep 1168875 = 1753313) B1753313
theorem B1168887 : Blo 1168401 1168887 := bstep (se 1 (by rfl) ⟨876665, by rfl⟩ : syracuseStep 1168887 = 1753331) B1753331
theorem B1168907 : Blo 1168401 1168907 := bstep (se 1 (by rfl) ⟨876680, by rfl⟩ : syracuseStep 1168907 = 1753361) B1753361
theorem B1168919 : Blo 1168401 1168919 := bstep (se 1 (by rfl) ⟨876689, by rfl⟩ : syracuseStep 1168919 = 1753379) B1753379
theorem B1168939 : Blo 1168401 1168939 := bstep (se 1 (by rfl) ⟨876704, by rfl⟩ : syracuseStep 1168939 = 1753409) B1753409
theorem B1168951 : Blo 1168401 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B1316407 : Blo 1168401 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B3946049 : Blo 1168401 3946049 := bstep (se 2 (by rfl) ⟨1479768, by rfl⟩ : syracuseStep 3946049 = 2959537) B2959537
theorem B1168971 : Blo 1168401 1168971 := bstep (se 1 (by rfl) ⟨876728, by rfl⟩ : syracuseStep 1168971 = 1753457) B1753457
theorem B1168983 : Blo 1168401 1168983 := bstep (se 1 (by rfl) ⟨876737, by rfl⟩ : syracuseStep 1168983 = 1753475) B1753475
theorem B1169003 : Blo 1168401 1169003 := bstep (se 1 (by rfl) ⟨876752, by rfl⟩ : syracuseStep 1169003 = 1753505) B1753505
theorem B1169015 : Blo 1168401 1169015 := bstep (se 1 (by rfl) ⟨876761, by rfl⟩ : syracuseStep 1169015 = 1753523) B1753523
theorem B1169035 : Blo 1168401 1169035 := bstep (se 1 (by rfl) ⟨876776, by rfl⟩ : syracuseStep 1169035 = 1753553) B1753553
theorem B1169047 : Blo 1168401 1169047 := bstep (se 1 (by rfl) ⟨876785, by rfl⟩ : syracuseStep 1169047 = 1753571) B1753571
theorem B1169067 : Blo 1168401 1169067 := bstep (se 1 (by rfl) ⟨876800, by rfl⟩ : syracuseStep 1169067 = 1753601) B1753601
theorem B16864949 : Blo 1168401 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B1169079 : Blo 1168401 1169079 := bstep (se 1 (by rfl) ⟨876809, by rfl⟩ : syracuseStep 1169079 = 1753619) B1753619
theorem B1169099 : Blo 1168401 1169099 := bstep (se 1 (by rfl) ⟨876824, by rfl⟩ : syracuseStep 1169099 = 1753649) B1753649
theorem B1169111 : Blo 1168401 1169111 := bstep (se 1 (by rfl) ⟨876833, by rfl⟩ : syracuseStep 1169111 = 1753667) B1753667
theorem B1169131 : Blo 1168401 1169131 := bstep (se 1 (by rfl) ⟨876848, by rfl⟩ : syracuseStep 1169131 = 1753697) B1753697
theorem B1316587 : Blo 1168401 1316587 := bstep (se 1 (by rfl) ⟨987440, by rfl⟩ : syracuseStep 1316587 = 1974881) B1974881
theorem B1169143 : Blo 1168401 1169143 := bstep (se 1 (by rfl) ⟨876857, by rfl⟩ : syracuseStep 1169143 = 1753715) B1753715
theorem B1169163 : Blo 1168401 1169163 := bstep (se 1 (by rfl) ⟨876872, by rfl⟩ : syracuseStep 1169163 = 1753745) B1753745
theorem B1169175 : Blo 1168401 1169175 := bstep (se 1 (by rfl) ⟨876881, by rfl⟩ : syracuseStep 1169175 = 1753763) B1753763
theorem B1169195 : Blo 1168401 1169195 := bstep (se 1 (by rfl) ⟨876896, by rfl⟩ : syracuseStep 1169195 = 1753793) B1753793
theorem B1169207 : Blo 1168401 1169207 := bstep (se 1 (by rfl) ⟨876905, by rfl⟩ : syracuseStep 1169207 = 1753811) B1753811
theorem B1169227 : Blo 1168401 1169227 := bstep (se 1 (by rfl) ⟨876920, by rfl⟩ : syracuseStep 1169227 = 1753841) B1753841
theorem B1169239 : Blo 1168401 1169239 := bstep (se 1 (by rfl) ⟨876929, by rfl⟩ : syracuseStep 1169239 = 1753859) B1753859
theorem B1316695 : Blo 1168401 1316695 := bstep (se 1 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 1316695 = 1975043) B1975043
theorem B1169259 : Blo 1168401 1169259 := bstep (se 1 (by rfl) ⟨876944, by rfl⟩ : syracuseStep 1169259 = 1753889) B1753889
theorem B1169271 : Blo 1168401 1169271 := bstep (se 1 (by rfl) ⟨876953, by rfl⟩ : syracuseStep 1169271 = 1753907) B1753907
theorem B1169291 : Blo 1168401 1169291 := bstep (se 1 (by rfl) ⟨876968, by rfl⟩ : syracuseStep 1169291 = 1753937) B1753937
theorem B1169303 : Blo 1168401 1169303 := bstep (se 1 (by rfl) ⟨876977, by rfl⟩ : syracuseStep 1169303 = 1753955) B1753955
theorem B1169323 : Blo 1168401 1169323 := bstep (se 1 (by rfl) ⟨876992, by rfl⟩ : syracuseStep 1169323 = 1753985) B1753985
theorem B1169335 : Blo 1168401 1169335 := bstep (se 1 (by rfl) ⟨877001, by rfl⟩ : syracuseStep 1169335 = 1754003) B1754003
theorem B1169355 : Blo 1168401 1169355 := bstep (se 1 (by rfl) ⟨877016, by rfl⟩ : syracuseStep 1169355 = 1754033) B1754033
theorem B1169367 : Blo 1168401 1169367 := bstep (se 1 (by rfl) ⟨877025, by rfl⟩ : syracuseStep 1169367 = 1754051) B1754051
theorem B1169387 : Blo 1168401 1169387 := bstep (se 1 (by rfl) ⟨877040, by rfl⟩ : syracuseStep 1169387 = 1754081) B1754081
theorem B1169399 : Blo 1168401 1169399 := bstep (se 1 (by rfl) ⟨877049, by rfl⟩ : syracuseStep 1169399 = 1754099) B1754099
theorem B1972235 : Blo 1168401 1972235 := bstep (se 1 (by rfl) ⟨1479176, by rfl⟩ : syracuseStep 1972235 = 2958353) B2958353
theorem B1169419 : Blo 1168401 1169419 := bstep (se 1 (by rfl) ⟨877064, by rfl⟩ : syracuseStep 1169419 = 1754129) B1754129
theorem B1169431 : Blo 1168401 1169431 := bstep (se 1 (by rfl) ⟨877073, by rfl⟩ : syracuseStep 1169431 = 1754147) B1754147
theorem B1169451 : Blo 1168401 1169451 := bstep (se 1 (by rfl) ⟨877088, by rfl⟩ : syracuseStep 1169451 = 1754177) B1754177
theorem B4438061 : Blo 1168401 4438061 := bstep (se 3 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 4438061 = 1664273) B1664273
theorem B1169463 : Blo 1168401 1169463 := bstep (se 1 (by rfl) ⟨877097, by rfl⟩ : syracuseStep 1169463 = 1754195) B1754195
theorem B4438091 : Blo 1168401 4438091 := bstep (se 1 (by rfl) ⟨3328568, by rfl⟩ : syracuseStep 4438091 = 6657137) B6657137
theorem B1169483 : Blo 1168401 1169483 := bstep (se 1 (by rfl) ⟨877112, by rfl⟩ : syracuseStep 1169483 = 1754225) B1754225
theorem B9992267 : Blo 1168401 9992267 := bstep (se 1 (by rfl) ⟨7494200, by rfl⟩ : syracuseStep 9992267 = 14988401) B14988401
theorem B1169495 : Blo 1168401 1169495 := bstep (se 1 (by rfl) ⟨877121, by rfl⟩ : syracuseStep 1169495 = 1754243) B1754243
theorem B3946589 : Blo 1168401 3946589 := bstep (se 3 (by rfl) ⟨739985, by rfl⟩ : syracuseStep 3946589 = 1479971) B1479971
theorem B1169515 : Blo 1168401 1169515 := bstep (se 1 (by rfl) ⟨877136, by rfl⟩ : syracuseStep 1169515 = 1754273) B1754273
theorem B1169527 : Blo 1168401 1169527 := bstep (se 1 (by rfl) ⟨877145, by rfl⟩ : syracuseStep 1169527 = 1754291) B1754291
theorem B1972363 : Blo 1168401 1972363 := bstep (se 1 (by rfl) ⟨1479272, by rfl⟩ : syracuseStep 1972363 = 2958545) B2958545
theorem B1169547 : Blo 1168401 1169547 := bstep (se 1 (by rfl) ⟨877160, by rfl⟩ : syracuseStep 1169547 = 1754321) B1754321
theorem B1185931 : Blo 1168401 1185931 := bstep (se 1 (by rfl) ⟨889448, by rfl⟩ : syracuseStep 1185931 = 1778897) B1778897
theorem B1169559 : Blo 1168401 1169559 := bstep (se 1 (by rfl) ⟨877169, by rfl⟩ : syracuseStep 1169559 = 1754339) B1754339
theorem B1169579 : Blo 1168401 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B4995245 : Blo 1168401 4995245 := bstep (se 3 (by rfl) ⟨936608, by rfl⟩ : syracuseStep 4995245 = 1873217) B1873217
theorem B1169591 : Blo 1168401 1169591 := bstep (se 1 (by rfl) ⟨877193, by rfl⟩ : syracuseStep 1169591 = 1754387) B1754387
theorem B1169611 : Blo 1168401 1169611 := bstep (se 1 (by rfl) ⟨877208, by rfl⟩ : syracuseStep 1169611 = 1754417) B1754417
theorem B1169623 : Blo 1168401 1169623 := bstep (se 1 (by rfl) ⟨877217, by rfl⟩ : syracuseStep 1169623 = 1754435) B1754435
theorem B1579225 : Blo 1168401 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B1169643 : Blo 1168401 1169643 := bstep (se 1 (by rfl) ⟨877232, by rfl⟩ : syracuseStep 1169643 = 1754465) B1754465
theorem B1169655 : Blo 1168401 1169655 := bstep (se 1 (by rfl) ⟨877241, by rfl⟩ : syracuseStep 1169655 = 1754483) B1754483
theorem B2218241 : Blo 1168401 2218241 := bstep (se 2 (by rfl) ⟨831840, by rfl⟩ : syracuseStep 2218241 = 1663681) B1663681
theorem B1169675 : Blo 1168401 1169675 := bstep (se 1 (by rfl) ⟨877256, by rfl⟩ : syracuseStep 1169675 = 1754513) B1754513
theorem B6658321 : Blo 1168401 6658321 := bstep (se 2 (by rfl) ⟨2496870, by rfl⟩ : syracuseStep 6658321 = 4993741) B4993741
theorem B1169687 : Blo 1168401 1169687 := bstep (se 1 (by rfl) ⟨877265, by rfl⟩ : syracuseStep 1169687 = 1754531) B1754531
theorem B1972505 : Blo 1168401 1972505 := bstep (se 2 (by rfl) ⟨739689, by rfl⟩ : syracuseStep 1972505 = 1479379) B1479379
theorem B1169707 : Blo 1168401 1169707 := bstep (se 1 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 1169707 = 1754561) B1754561
theorem B1169719 : Blo 1168401 1169719 := bstep (se 1 (by rfl) ⟨877289, by rfl⟩ : syracuseStep 1169719 = 1754579) B1754579
theorem B5921099 : Blo 1168401 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B1169739 : Blo 1168401 1169739 := bstep (se 1 (by rfl) ⟨877304, by rfl⟩ : syracuseStep 1169739 = 1754609) B1754609
theorem B1169751 : Blo 1168401 1169751 := bstep (se 1 (by rfl) ⟨877313, by rfl⟩ : syracuseStep 1169751 = 1754627) B1754627
theorem B3332441 : Blo 1168401 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B1169771 : Blo 1168401 1169771 := bstep (se 1 (by rfl) ⟨877328, by rfl⟩ : syracuseStep 1169771 = 1754657) B1754657
theorem B1169783 : Blo 1168401 1169783 := bstep (se 1 (by rfl) ⟨877337, by rfl⟩ : syracuseStep 1169783 = 1754675) B1754675
theorem B1169803 : Blo 1168401 1169803 := bstep (se 1 (by rfl) ⟨877352, by rfl⟩ : syracuseStep 1169803 = 1754705) B1754705
theorem B1169815 : Blo 1168401 1169815 := bstep (se 1 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 1169815 = 1754723) B1754723
theorem B1972633 : Blo 1168401 1972633 := bstep (se 2 (by rfl) ⟨739737, by rfl⟩ : syracuseStep 1972633 = 1479475) B1479475
theorem B1169835 : Blo 1168401 1169835 := bstep (se 1 (by rfl) ⟨877376, by rfl⟩ : syracuseStep 1169835 = 1754753) B1754753
theorem B1169847 : Blo 1168401 1169847 := bstep (se 1 (by rfl) ⟨877385, by rfl⟩ : syracuseStep 1169847 = 1754771) B1754771
theorem B1169867 : Blo 1168401 1169867 := bstep (se 1 (by rfl) ⟨877400, by rfl⟩ : syracuseStep 1169867 = 1754801) B1754801
theorem B1169879 : Blo 1168401 1169879 := bstep (se 1 (by rfl) ⟨877409, by rfl⟩ : syracuseStep 1169879 = 1754819) B1754819
theorem B1169899 : Blo 1168401 1169899 := bstep (se 1 (by rfl) ⟨877424, by rfl⟩ : syracuseStep 1169899 = 1754849) B1754849
theorem B1169911 : Blo 1168401 1169911 := bstep (se 1 (by rfl) ⟨877433, by rfl⟩ : syracuseStep 1169911 = 1754867) B1754867
theorem B4995587 : Blo 1168401 4995587 := bstep (se 1 (by rfl) ⟨3746690, by rfl⟩ : syracuseStep 4995587 = 7493381) B7493381
theorem B1169931 : Blo 1168401 1169931 := bstep (se 1 (by rfl) ⟨877448, by rfl⟩ : syracuseStep 1169931 = 1754897) B1754897
theorem B4741649 : Blo 1168401 4741649 := bstep (se 2 (by rfl) ⟨1778118, by rfl⟩ : syracuseStep 4741649 = 3556237) B3556237
theorem B1169943 : Blo 1168401 1169943 := bstep (se 1 (by rfl) ⟨877457, by rfl⟩ : syracuseStep 1169943 = 1754915) B1754915
theorem B2701849 : Blo 1168401 2701849 := bstep (se 2 (by rfl) ⟨1013193, by rfl⟩ : syracuseStep 2701849 = 2026387) B2026387
theorem B1169963 : Blo 1168401 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B1169975 : Blo 1168401 1169975 := bstep (se 1 (by rfl) ⟨877481, by rfl⟩ : syracuseStep 1169975 = 1754963) B1754963
theorem B1169995 : Blo 1168401 1169995 := bstep (se 1 (by rfl) ⟨877496, by rfl⟩ : syracuseStep 1169995 = 1754993) B1754993
theorem B2218583 : Blo 1168401 2218583 := bstep (se 1 (by rfl) ⟨1663937, by rfl⟩ : syracuseStep 2218583 = 3327875) B3327875
theorem B1170007 : Blo 1168401 1170007 := bstep (se 1 (by rfl) ⟨877505, by rfl⟩ : syracuseStep 1170007 = 1755011) B1755011
theorem B1170027 : Blo 1168401 1170027 := bstep (se 1 (by rfl) ⟨877520, by rfl⟩ : syracuseStep 1170027 = 1755041) B1755041
theorem B1170039 : Blo 1168401 1170039 := bstep (se 1 (by rfl) ⟨877529, by rfl⟩ : syracuseStep 1170039 = 1755059) B1755059
theorem B1170059 : Blo 1168401 1170059 := bstep (se 1 (by rfl) ⟨877544, by rfl⟩ : syracuseStep 1170059 = 1755089) B1755089
theorem B9484951 : Blo 1168401 9484951 := bstep (se 1 (by rfl) ⟨7113713, by rfl⟩ : syracuseStep 9484951 = 14227427) B14227427
theorem B1170071 : Blo 1168401 1170071 := bstep (se 1 (by rfl) ⟨877553, by rfl⟩ : syracuseStep 1170071 = 1755107) B1755107
theorem B1170091 : Blo 1168401 1170091 := bstep (se 1 (by rfl) ⟨877568, by rfl⟩ : syracuseStep 1170091 = 1755137) B1755137
theorem B8428211 : Blo 1168401 8428211 := bstep (se 1 (by rfl) ⟨6321158, by rfl⟩ : syracuseStep 8428211 = 12642317) B12642317
theorem B1170103 : Blo 1168401 1170103 := bstep (se 1 (by rfl) ⟨877577, by rfl⟩ : syracuseStep 1170103 = 1755155) B1755155
theorem B1170123 : Blo 1168401 1170123 := bstep (se 1 (by rfl) ⟨877592, by rfl⟩ : syracuseStep 1170123 = 1755185) B1755185
theorem B1170135 : Blo 1168401 1170135 := bstep (se 1 (by rfl) ⟨877601, by rfl⟩ : syracuseStep 1170135 = 1755203) B1755203
theorem B4438745 : Blo 1168401 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B1170155 : Blo 1168401 1170155 := bstep (se 1 (by rfl) ⟨877616, by rfl⟩ : syracuseStep 1170155 = 1755233) B1755233
theorem B1170167 : Blo 1168401 1170167 := bstep (se 1 (by rfl) ⟨877625, by rfl⟩ : syracuseStep 1170167 = 1755251) B1755251
theorem B1170187 : Blo 1168401 1170187 := bstep (se 1 (by rfl) ⟨877640, by rfl⟩ : syracuseStep 1170187 = 1755281) B1755281
theorem B1170199 : Blo 1168401 1170199 := bstep (se 1 (by rfl) ⟨877649, by rfl⟩ : syracuseStep 1170199 = 1755299) B1755299
theorem B1170219 : Blo 1168401 1170219 := bstep (se 1 (by rfl) ⟨877664, by rfl⟩ : syracuseStep 1170219 = 1755329) B1755329
theorem B3160883 : Blo 1168401 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B1170231 : Blo 1168401 1170231 := bstep (se 1 (by rfl) ⟨877673, by rfl⟩ : syracuseStep 1170231 = 1755347) B1755347
theorem B7486283 : Blo 1168401 7486283 := bstep (se 1 (by rfl) ⟨5614712, by rfl⟩ : syracuseStep 7486283 = 11229425) B11229425
theorem B1170251 : Blo 1168401 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B2497367 : Blo 1168401 2497367 := bstep (se 1 (by rfl) ⟨1873025, by rfl⟩ : syracuseStep 2497367 = 3746051) B3746051
theorem B1170263 : Blo 1168401 1170263 := bstep (se 1 (by rfl) ⟨877697, by rfl⟩ : syracuseStep 1170263 = 1755395) B1755395
theorem B1170283 : Blo 1168401 1170283 := bstep (se 1 (by rfl) ⟨877712, by rfl⟩ : syracuseStep 1170283 = 1755425) B1755425
theorem B1170295 : Blo 1168401 1170295 := bstep (se 1 (by rfl) ⟨877721, by rfl⟩ : syracuseStep 1170295 = 1755443) B1755443
theorem B1170315 : Blo 1168401 1170315 := bstep (se 1 (by rfl) ⟨877736, by rfl⟩ : syracuseStep 1170315 = 1755473) B1755473
theorem B1170327 : Blo 1168401 1170327 := bstep (se 1 (by rfl) ⟨877745, by rfl⟩ : syracuseStep 1170327 = 1755491) B1755491
theorem B1170347 : Blo 1168401 1170347 := bstep (se 1 (by rfl) ⟨877760, by rfl⟩ : syracuseStep 1170347 = 1755521) B1755521
theorem B1170359 : Blo 1168401 1170359 := bstep (se 1 (by rfl) ⟨877769, by rfl⟩ : syracuseStep 1170359 = 1755539) B1755539
theorem B2808769 : Blo 1168401 2808769 := bstep (se 2 (by rfl) ⟨1053288, by rfl⟩ : syracuseStep 2808769 = 2106577) B2106577
theorem B1170379 : Blo 1168401 1170379 := bstep (se 1 (by rfl) ⟨877784, by rfl⟩ : syracuseStep 1170379 = 1755569) B1755569
theorem B1973207 : Blo 1168401 1973207 := bstep (se 1 (by rfl) ⟨1479905, by rfl⟩ : syracuseStep 1973207 = 2959811) B2959811
theorem B1170391 : Blo 1168401 1170391 := bstep (se 1 (by rfl) ⟨877793, by rfl⟩ : syracuseStep 1170391 = 1755587) B1755587
theorem B2497547 : Blo 1168401 2497547 := bstep (se 1 (by rfl) ⟨1873160, by rfl⟩ : syracuseStep 2497547 = 3746321) B3746321
theorem B4439063 : Blo 1168401 4439063 := bstep (se 1 (by rfl) ⟨3329297, by rfl⟩ : syracuseStep 4439063 = 6658595) B6658595
theorem B1973335 : Blo 1168401 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B3947723 : Blo 1168401 3947723 := bstep (se 1 (by rfl) ⟨2960792, by rfl⟩ : syracuseStep 3947723 = 5921585) B5921585
theorem B1899737 : Blo 1168401 1899737 := bstep (se 2 (by rfl) ⟨712401, by rfl⟩ : syracuseStep 1899737 = 1424803) B1424803
theorem B2219251 : Blo 1168401 2219251 := bstep (se 1 (by rfl) ⟨1664438, by rfl⟩ : syracuseStep 2219251 = 3328877) B3328877
theorem B1580311 : Blo 1168401 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B14974253 : Blo 1168401 14974253 := bstep (se 3 (by rfl) ⟨2807672, by rfl⟩ : syracuseStep 14974253 = 5615345) B5615345
theorem B2628953 : Blo 1168401 2628953 := bstep (se 2 (by rfl) ⟨985857, by rfl⟩ : syracuseStep 2628953 = 1971715) B1971715
theorem B4742489 : Blo 1168401 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B29957525 : Blo 1168401 29957525 := bstep (se 6 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 29957525 = 1404259) B1404259
theorem B2629043 : Blo 1168401 2629043 := bstep (se 1 (by rfl) ⟨1971782, by rfl⟩ : syracuseStep 2629043 = 3943565) B3943565
theorem B2629079 : Blo 1168401 2629079 := bstep (se 1 (by rfl) ⟨1971809, by rfl⟩ : syracuseStep 2629079 = 3943619) B3943619
theorem B3947993 : Blo 1168401 3947993 := bstep (se 2 (by rfl) ⟨1480497, by rfl⟩ : syracuseStep 3947993 = 2960995) B2960995
theorem B8543789 : Blo 1168401 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B10821185 : Blo 1168401 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B1752665 : Blo 1168401 1752665 := bstep (se 2 (by rfl) ⟨657249, by rfl⟩ : syracuseStep 1752665 = 1314499) B1314499
theorem B4742749 : Blo 1168401 4742749 := bstep (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) B1778531
theorem B10821221 : Blo 1168401 10821221 := bstep (se 4 (by rfl) ⟨1014489, by rfl⟩ : syracuseStep 10821221 = 2028979) B2028979
theorem B2629259 : Blo 1168401 2629259 := bstep (se 1 (by rfl) ⟨1971944, by rfl⟩ : syracuseStep 2629259 = 3943889) B3943889
theorem B2219699 : Blo 1168401 2219699 := bstep (se 1 (by rfl) ⟨1664774, by rfl⟩ : syracuseStep 2219699 = 3329549) B3329549
theorem B4439731 : Blo 1168401 4439731 := bstep (se 1 (by rfl) ⟨3329798, by rfl⟩ : syracuseStep 4439731 = 6659597) B6659597
theorem B2629313 : Blo 1168401 2629313 := bstep (se 2 (by rfl) ⟨985992, by rfl⟩ : syracuseStep 2629313 = 1971985) B1971985
theorem B1752779 : Blo 1168401 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1973963 : Blo 1168401 1973963 := bstep (se 1 (by rfl) ⟨1480472, by rfl⟩ : syracuseStep 1973963 = 2960945) B2960945
theorem B1752791 : Blo 1168401 1752791 := bstep (se 1 (by rfl) ⟨1314593, by rfl⟩ : syracuseStep 1752791 = 2629187) B2629187
theorem B2219737 : Blo 1168401 2219737 := bstep (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) B1664803
theorem B1752857 : Blo 1168401 1752857 := bstep (se 2 (by rfl) ⟨657321, by rfl⟩ : syracuseStep 1752857 = 1314643) B1314643
theorem B2531137 : Blo 1168401 2531137 := bstep (se 2 (by rfl) ⟨949176, by rfl⟩ : syracuseStep 2531137 = 1898353) B1898353
theorem B1974091 : Blo 1168401 1974091 := bstep (se 1 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 1974091 = 2961137) B2961137
theorem B1752971 : Blo 1168401 1752971 := bstep (se 1 (by rfl) ⟨1314728, by rfl⟩ : syracuseStep 1752971 = 2629457) B2629457
theorem B1752983 : Blo 1168401 1752983 := bstep (se 1 (by rfl) ⟨1314737, by rfl⟩ : syracuseStep 1752983 = 2629475) B2629475
theorem B2629529 : Blo 1168401 2629529 := bstep (se 2 (by rfl) ⟨986073, by rfl⟩ : syracuseStep 2629529 = 1972147) B1972147
theorem B1753049 : Blo 1168401 1753049 := bstep (se 2 (by rfl) ⟨657393, by rfl⟩ : syracuseStep 1753049 = 1314787) B1314787
theorem B2809817 : Blo 1168401 2809817 := bstep (se 2 (by rfl) ⟨1053681, by rfl⟩ : syracuseStep 2809817 = 2107363) B2107363
theorem B1974233 : Blo 1168401 1974233 := bstep (se 2 (by rfl) ⟨740337, by rfl⟩ : syracuseStep 1974233 = 1480675) B1480675
theorem B2629619 : Blo 1168401 2629619 := bstep (se 1 (by rfl) ⟨1972214, by rfl⟩ : syracuseStep 2629619 = 3944429) B3944429
theorem B1753103 : Blo 1168401 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B1974287 : Blo 1168401 1974287 := bstep (se 1 (by rfl) ⟨1480715, by rfl⟩ : syracuseStep 1974287 = 2961431) B2961431
theorem B45547541 : Blo 1168401 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B3948587 : Blo 1168401 3948587 := bstep (se 1 (by rfl) ⟨2961440, by rfl⟩ : syracuseStep 3948587 = 5922881) B5922881
theorem B1753145 : Blo 1168401 1753145 := bstep (se 2 (by rfl) ⟨657429, by rfl⟩ : syracuseStep 1753145 = 1314859) B1314859
theorem B2629691 : Blo 1168401 2629691 := bstep (se 1 (by rfl) ⟨1972268, by rfl⟩ : syracuseStep 2629691 = 3944537) B3944537
theorem B24019037 : Blo 1168401 24019037 := bstep (se 3 (by rfl) ⟨4503569, by rfl⟩ : syracuseStep 24019037 = 9007139) B9007139
theorem B1753223 : Blo 1168401 1753223 := bstep (se 1 (by rfl) ⟨1314917, by rfl⟩ : syracuseStep 1753223 = 2629835) B2629835
theorem B1753259 : Blo 1168401 1753259 := bstep (se 1 (by rfl) ⟨1314944, by rfl⟩ : syracuseStep 1753259 = 2629889) B2629889
theorem B2629817 : Blo 1168401 2629817 := bstep (se 2 (by rfl) ⟨986181, by rfl⟩ : syracuseStep 2629817 = 1972363) B1972363
theorem B1753289 : Blo 1168401 1753289 := bstep (se 2 (by rfl) ⟨657483, by rfl⟩ : syracuseStep 1753289 = 1314967) B1314967
theorem B3203329 : Blo 1168401 3203329 := bstep (se 2 (by rfl) ⟨1201248, by rfl⟩ : syracuseStep 3203329 = 2402497) B2402497
theorem B2105633 : Blo 1168401 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B1753403 : Blo 1168401 1753403 := bstep (se 1 (by rfl) ⟨1315052, by rfl⟩ : syracuseStep 1753403 = 2630105) B2630105
theorem B1753463 : Blo 1168401 1753463 := bstep (se 1 (by rfl) ⟨1315097, by rfl⟩ : syracuseStep 1753463 = 2630195) B2630195
theorem B1753487 : Blo 1168401 1753487 := bstep (se 1 (by rfl) ⟨1315115, by rfl⟩ : syracuseStep 1753487 = 2630231) B2630231
theorem B1753529 : Blo 1168401 1753529 := bstep (se 2 (by rfl) ⟨657573, by rfl⟩ : syracuseStep 1753529 = 1315147) B1315147
theorem B2220473 : Blo 1168401 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B1753607 : Blo 1168401 1753607 := bstep (se 1 (by rfl) ⟨1315205, by rfl⟩ : syracuseStep 1753607 = 2630411) B2630411
theorem B3162635 : Blo 1168401 3162635 := bstep (se 1 (by rfl) ⟨2371976, by rfl⟩ : syracuseStep 3162635 = 4743953) B4743953
theorem B2630159 : Blo 1168401 2630159 := bstep (se 1 (by rfl) ⟨1972619, by rfl⟩ : syracuseStep 2630159 = 3945239) B3945239
theorem B2630177 : Blo 1168401 2630177 := bstep (se 2 (by rfl) ⟨986316, by rfl⟩ : syracuseStep 2630177 = 1972633) B1972633
theorem B2957867 : Blo 1168401 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B1753643 : Blo 1168401 1753643 := bstep (se 1 (by rfl) ⟨1315232, by rfl⟩ : syracuseStep 1753643 = 2630465) B2630465
theorem B1974827 : Blo 1168401 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B1753673 : Blo 1168401 1753673 := bstep (se 2 (by rfl) ⟨657627, by rfl⟩ : syracuseStep 1753673 = 1315255) B1315255
theorem B12649061 : Blo 1168401 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B1753787 : Blo 1168401 1753787 := bstep (se 1 (by rfl) ⟨1315340, by rfl⟩ : syracuseStep 1753787 = 2630681) B2630681
theorem B5923529 : Blo 1168401 5923529 := bstep (se 2 (by rfl) ⟨2221323, by rfl⟩ : syracuseStep 5923529 = 4442647) B4442647
theorem B6324965 : Blo 1168401 6324965 := bstep (se 4 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 6324965 = 1185931) B1185931
theorem B1753847 : Blo 1168401 1753847 := bstep (se 1 (by rfl) ⟨1315385, by rfl⟩ : syracuseStep 1753847 = 2630771) B2630771
theorem B1753871 : Blo 1168401 1753871 := bstep (se 1 (by rfl) ⟨1315403, by rfl⟩ : syracuseStep 1753871 = 2630807) B2630807
theorem B1753913 : Blo 1168401 1753913 := bstep (se 2 (by rfl) ⟨657717, by rfl⟩ : syracuseStep 1753913 = 1315435) B1315435
theorem B2630519 : Blo 1168401 2630519 := bstep (se 1 (by rfl) ⟨1972889, by rfl⟩ : syracuseStep 2630519 = 3945779) B3945779
theorem B1753991 : Blo 1168401 1753991 := bstep (se 1 (by rfl) ⟨1315493, by rfl⟩ : syracuseStep 1753991 = 2630987) B2630987
theorem B7488409 : Blo 1168401 7488409 := bstep (se 2 (by rfl) ⟨2808153, by rfl⟩ : syracuseStep 7488409 = 5616307) B5616307
theorem B1754027 : Blo 1168401 1754027 := bstep (se 1 (by rfl) ⟨1315520, by rfl⟩ : syracuseStep 1754027 = 2631041) B2631041
theorem B1754057 : Blo 1168401 1754057 := bstep (se 2 (by rfl) ⟨657771, by rfl⟩ : syracuseStep 1754057 = 1315543) B1315543
theorem B8881163 : Blo 1168401 8881163 := bstep (se 1 (by rfl) ⟨6660872, by rfl⟩ : syracuseStep 8881163 = 13321745) B13321745
theorem B2630699 : Blo 1168401 2630699 := bstep (se 1 (by rfl) ⟨1973024, by rfl⟩ : syracuseStep 2630699 = 3946049) B3946049
theorem B1754171 : Blo 1168401 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B4441175 : Blo 1168401 4441175 := bstep (se 1 (by rfl) ⟨3330881, by rfl⟩ : syracuseStep 4441175 = 6661763) B6661763
theorem B1754231 : Blo 1168401 1754231 := bstep (se 1 (by rfl) ⟨1315673, by rfl⟩ : syracuseStep 1754231 = 2631347) B2631347
theorem B1754255 : Blo 1168401 1754255 := bstep (se 1 (by rfl) ⟨1315691, by rfl⟩ : syracuseStep 1754255 = 2631383) B2631383
theorem B1754297 : Blo 1168401 1754297 := bstep (se 2 (by rfl) ⟨657861, by rfl⟩ : syracuseStep 1754297 = 1315723) B1315723
theorem B3745025 : Blo 1168401 3745025 := bstep (se 2 (by rfl) ⟨1404384, by rfl⟩ : syracuseStep 3745025 = 2808769) B2808769
theorem B1754375 : Blo 1168401 1754375 := bstep (se 1 (by rfl) ⟨1315781, by rfl⟩ : syracuseStep 1754375 = 2631563) B2631563
theorem B3327247 : Blo 1168401 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B1754411 : Blo 1168401 1754411 := bstep (se 1 (by rfl) ⟨1315808, by rfl⟩ : syracuseStep 1754411 = 2631617) B2631617
theorem B3949883 : Blo 1168401 3949883 := bstep (se 1 (by rfl) ⟨2962412, by rfl⟩ : syracuseStep 3949883 = 5924825) B5924825
theorem B3327293 : Blo 1168401 3327293 := bstep (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) B1247735
theorem B1754441 : Blo 1168401 1754441 := bstep (se 2 (by rfl) ⟨657915, by rfl⟩ : syracuseStep 1754441 = 1315831) B1315831
theorem B2958707 : Blo 1168401 2958707 := bstep (se 1 (by rfl) ⟨2219030, by rfl⟩ : syracuseStep 2958707 = 4438061) B4438061
theorem B3556723 : Blo 1168401 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B2958727 : Blo 1168401 2958727 := bstep (se 1 (by rfl) ⟨2219045, by rfl⟩ : syracuseStep 2958727 = 4438091) B4438091
theorem B6661511 : Blo 1168401 6661511 := bstep (se 1 (by rfl) ⟨4996133, by rfl⟩ : syracuseStep 6661511 = 9992267) B9992267
theorem B2631059 : Blo 1168401 2631059 := bstep (se 1 (by rfl) ⟨1973294, by rfl⟩ : syracuseStep 2631059 = 3946589) B3946589
theorem B1754555 : Blo 1168401 1754555 := bstep (se 1 (by rfl) ⟨1315916, by rfl⟩ : syracuseStep 1754555 = 2631833) B2631833
theorem B2631113 : Blo 1168401 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B1754615 : Blo 1168401 1754615 := bstep (se 1 (by rfl) ⟨1315961, by rfl⟩ : syracuseStep 1754615 = 2631923) B2631923
theorem B1754639 : Blo 1168401 1754639 := bstep (se 1 (by rfl) ⟨1315979, by rfl⟩ : syracuseStep 1754639 = 2631959) B2631959
theorem B1754681 : Blo 1168401 1754681 := bstep (se 2 (by rfl) ⟨658005, by rfl⟩ : syracuseStep 1754681 = 1316011) B1316011
theorem B4441661 : Blo 1168401 4441661 := bstep (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) B1665623
theorem B1754759 : Blo 1168401 1754759 := bstep (se 1 (by rfl) ⟨1316069, by rfl⟩ : syracuseStep 1754759 = 2632139) B2632139
theorem B3327635 : Blo 1168401 3327635 := bstep (se 1 (by rfl) ⟨2495726, by rfl⟩ : syracuseStep 3327635 = 4991453) B4991453
theorem B25282199 : Blo 1168401 25282199 := bstep (se 1 (by rfl) ⟨18961649, by rfl⟩ : syracuseStep 25282199 = 37923299) B37923299
theorem B2959001 : Blo 1168401 2959001 := bstep (se 2 (by rfl) ⟨1109625, by rfl⟩ : syracuseStep 2959001 = 2219251) B2219251
theorem B1754795 : Blo 1168401 1754795 := bstep (se 1 (by rfl) ⟨1316096, by rfl⟩ : syracuseStep 1754795 = 2632193) B2632193
theorem B2107081 : Blo 1168401 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B1754825 : Blo 1168401 1754825 := bstep (se 2 (by rfl) ⟨658059, by rfl⟩ : syracuseStep 1754825 = 1316119) B1316119
theorem B3376939 : Blo 1168401 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B2959163 : Blo 1168401 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B1754939 : Blo 1168401 1754939 := bstep (se 1 (by rfl) ⟨1316204, by rfl⟩ : syracuseStep 1754939 = 2632409) B2632409
theorem B2107255 : Blo 1168401 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B1754999 : Blo 1168401 1754999 := bstep (se 1 (by rfl) ⟨1316249, by rfl⟩ : syracuseStep 1754999 = 2632499) B2632499
theorem B4990855 : Blo 1168401 4990855 := bstep (se 1 (by rfl) ⟨3743141, by rfl⟩ : syracuseStep 4990855 = 7486283) B7486283
theorem B1664911 : Blo 1168401 1664911 := bstep (se 1 (by rfl) ⟨1248683, by rfl⟩ : syracuseStep 1664911 = 2497367) B2497367
theorem B1755023 : Blo 1168401 1755023 := bstep (se 1 (by rfl) ⟨1316267, by rfl⟩ : syracuseStep 1755023 = 2632535) B2632535
theorem B5916563 : Blo 1168401 5916563 := bstep (se 1 (by rfl) ⟨4437422, by rfl⟩ : syracuseStep 5916563 = 8874845) B8874845
theorem B1755065 : Blo 1168401 1755065 := bstep (se 2 (by rfl) ⟨658149, by rfl⟩ : syracuseStep 1755065 = 1316299) B1316299
theorem B18958283 : Blo 1168401 18958283 := bstep (se 1 (by rfl) ⟨14218712, by rfl⟩ : syracuseStep 18958283 = 28437425) B28437425
theorem B1665031 : Blo 1168401 1665031 := bstep (se 1 (by rfl) ⟨1248773, by rfl⟩ : syracuseStep 1665031 = 2497547) B2497547
theorem B1755143 : Blo 1168401 1755143 := bstep (se 1 (by rfl) ⟨1316357, by rfl⟩ : syracuseStep 1755143 = 2632715) B2632715
theorem B2959375 : Blo 1168401 2959375 := bstep (se 1 (by rfl) ⟨2219531, by rfl⟩ : syracuseStep 2959375 = 4439063) B4439063
theorem B1755179 : Blo 1168401 1755179 := bstep (se 1 (by rfl) ⟨1316384, by rfl⟩ : syracuseStep 1755179 = 2632769) B2632769
theorem B13330493 : Blo 1168401 13330493 := bstep (se 3 (by rfl) ⟨2499467, by rfl⟩ : syracuseStep 13330493 = 4998935) B4998935
theorem B1755209 : Blo 1168401 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B14993525 : Blo 1168401 14993525 := bstep (se 5 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 14993525 = 1405643) B1405643
theorem B2631815 : Blo 1168401 2631815 := bstep (se 1 (by rfl) ⟨1973861, by rfl⟩ : syracuseStep 2631815 = 3947723) B3947723
theorem B136726679 : Blo 1168401 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B1755323 : Blo 1168401 1755323 := bstep (se 1 (by rfl) ⟨1316492, by rfl⟩ : syracuseStep 1755323 = 2632985) B2632985
theorem B4991213 : Blo 1168401 4991213 := bstep (se 3 (by rfl) ⟨935852, by rfl⟩ : syracuseStep 4991213 = 1871705) B1871705
theorem B1755383 : Blo 1168401 1755383 := bstep (se 1 (by rfl) ⟨1316537, by rfl⟩ : syracuseStep 1755383 = 2633075) B2633075
theorem B1755407 : Blo 1168401 1755407 := bstep (se 1 (by rfl) ⟨1316555, by rfl⟩ : syracuseStep 1755407 = 2633111) B2633111
theorem B2959649 : Blo 1168401 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B1755449 : Blo 1168401 1755449 := bstep (se 2 (by rfl) ⟨658293, by rfl⟩ : syracuseStep 1755449 = 1316587) B1316587
theorem B2631995 : Blo 1168401 2631995 := bstep (se 1 (by rfl) ⟨1973996, by rfl⟩ : syracuseStep 2631995 = 3947993) B3947993
theorem B5695859 : Blo 1168401 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B1755527 : Blo 1168401 1755527 := bstep (se 1 (by rfl) ⟨1316645, by rfl⟩ : syracuseStep 1755527 = 2633291) B2633291
theorem B1755563 : Blo 1168401 1755563 := bstep (se 1 (by rfl) ⟨1316672, by rfl⟩ : syracuseStep 1755563 = 2633345) B2633345
theorem B2632121 : Blo 1168401 2632121 := bstep (se 2 (by rfl) ⟨987045, by rfl⟩ : syracuseStep 2632121 = 1974091) B1974091
theorem B1755593 : Blo 1168401 1755593 := bstep (se 2 (by rfl) ⟨658347, by rfl⟩ : syracuseStep 1755593 = 1316695) B1316695
theorem B3328523 : Blo 1168401 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B2632463 : Blo 1168401 2632463 := bstep (se 1 (by rfl) ⟨1974347, by rfl⟩ : syracuseStep 2632463 = 3948695) B3948695
theorem B2632481 : Blo 1168401 2632481 := bstep (se 2 (by rfl) ⟨987180, by rfl⟩ : syracuseStep 2632481 = 1974361) B1974361
theorem B8883107 : Blo 1168401 8883107 := bstep (se 1 (by rfl) ⟨6662330, by rfl⟩ : syracuseStep 8883107 = 13324661) B13324661
theorem B6654905 : Blo 1168401 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B7498813 : Blo 1168401 7498813 := bstep (se 3 (by rfl) ⟨1406027, by rfl⟩ : syracuseStep 7498813 = 2812055) B2812055
theorem B3943511 : Blo 1168401 3943511 := bstep (se 1 (by rfl) ⟨2957633, by rfl⟩ : syracuseStep 3943511 = 5915267) B5915267
theorem B2632823 : Blo 1168401 2632823 := bstep (se 1 (by rfl) ⟨1974617, by rfl⟩ : syracuseStep 2632823 = 3949235) B3949235
theorem B2960651 : Blo 1168401 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B4443407 : Blo 1168401 4443407 := bstep (se 1 (by rfl) ⟨3332555, by rfl⟩ : syracuseStep 4443407 = 6665111) B6665111
theorem B2633003 : Blo 1168401 2633003 := bstep (se 1 (by rfl) ⟨1974752, by rfl⟩ : syracuseStep 2633003 = 3949505) B3949505
theorem B9121169 : Blo 1168401 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B5623187 : Blo 1168401 5623187 := bstep (se 1 (by rfl) ⟨4217390, by rfl⟩ : syracuseStep 5623187 = 8434781) B8434781
theorem B4001177 : Blo 1168401 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B20254157 : Blo 1168401 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B14233117 : Blo 1168401 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B3943997 : Blo 1168401 3943997 := bstep (se 3 (by rfl) ⟨739499, by rfl⟩ : syracuseStep 3943997 = 1478999) B1478999
theorem B5615191 : Blo 1168401 5615191 := bstep (se 1 (by rfl) ⟨4211393, by rfl⟩ : syracuseStep 5615191 = 8422787) B8422787
theorem B4501079 : Blo 1168401 4501079 := bstep (se 1 (by rfl) ⟨3375809, by rfl⟩ : syracuseStep 4501079 = 6751619) B6751619
theorem B2633363 : Blo 1168401 2633363 := bstep (se 1 (by rfl) ⟨1975022, by rfl⟩ : syracuseStep 2633363 = 3950045) B3950045
theorem B11243299 : Blo 1168401 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B11398963 : Blo 1168401 11398963 := bstep (se 1 (by rfl) ⟨8549222, by rfl⟩ : syracuseStep 11398963 = 17098445) B17098445
theorem B2666375 : Blo 1168401 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B2961299 : Blo 1168401 2961299 := bstep (se 1 (by rfl) ⟨2220974, by rfl⟩ : syracuseStep 2961299 = 4441949) B4441949
theorem B1314823 : Blo 1168401 1314823 := bstep (se 1 (by rfl) ⟨986117, by rfl⟩ : syracuseStep 1314823 = 1972235) B1972235
theorem B3330163 : Blo 1168401 3330163 := bstep (se 1 (by rfl) ⟨2497622, by rfl⟩ : syracuseStep 3330163 = 4995245) B4995245
theorem B1478827 : Blo 1168401 1478827 := bstep (se 1 (by rfl) ⟨1109120, by rfl⟩ : syracuseStep 1478827 = 2218241) B2218241
theorem B2961593 : Blo 1168401 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B1315003 : Blo 1168401 1315003 := bstep (se 1 (by rfl) ⟨986252, by rfl⟩ : syracuseStep 1315003 = 1972505) B1972505
theorem B3330391 : Blo 1168401 3330391 := bstep (se 1 (by rfl) ⟨2497793, by rfl⟩ : syracuseStep 3330391 = 4995587) B4995587
theorem B1479055 : Blo 1168401 1479055 := bstep (se 1 (by rfl) ⟨1109291, by rfl⟩ : syracuseStep 1479055 = 2218583) B2218583
theorem B1315471 : Blo 1168401 1315471 := bstep (se 1 (by rfl) ⟨986603, by rfl⟩ : syracuseStep 1315471 = 1973207) B1973207
theorem B1266491 : Blo 1168401 1266491 := bstep (se 1 (by rfl) ⟨949868, by rfl⟩ : syracuseStep 1266491 = 1899737) B1899737
theorem B9982835 : Blo 1168401 9982835 := bstep (se 1 (by rfl) ⟨7487126, by rfl⟩ : syracuseStep 9982835 = 14974253) B14974253
theorem B2962291 : Blo 1168401 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B5919641 : Blo 1168401 5919641 := bstep (se 2 (by rfl) ⟨2219865, by rfl⟩ : syracuseStep 5919641 = 4439731) B4439731
theorem B3945401 : Blo 1168401 3945401 := bstep (se 2 (by rfl) ⟨1479525, by rfl⟩ : syracuseStep 3945401 = 2959051) B2959051
theorem B2962433 : Blo 1168401 2962433 := bstep (se 2 (by rfl) ⟨1110912, by rfl⟩ : syracuseStep 2962433 = 2221825) B2221825
theorem B7214123 : Blo 1168401 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B1168443 : Blo 1168401 1168443 := bstep (se 1 (by rfl) ⟨876332, by rfl⟩ : syracuseStep 1168443 = 1752665) B1752665
theorem B7214147 : Blo 1168401 7214147 := bstep (se 1 (by rfl) ⟨5410610, by rfl⟩ : syracuseStep 7214147 = 10821221) B10821221
theorem B1479799 : Blo 1168401 1479799 := bstep (se 1 (by rfl) ⟨1109849, by rfl⟩ : syracuseStep 1479799 = 2219699) B2219699
theorem B1168519 : Blo 1168401 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B1315975 : Blo 1168401 1315975 := bstep (se 1 (by rfl) ⟨986981, by rfl⟩ : syracuseStep 1315975 = 1973963) B1973963
theorem B1168527 : Blo 1168401 1168527 := bstep (se 1 (by rfl) ⟨876395, by rfl⟩ : syracuseStep 1168527 = 1752791) B1752791
theorem B1168571 : Blo 1168401 1168571 := bstep (se 1 (by rfl) ⟨876428, by rfl⟩ : syracuseStep 1168571 = 1752857) B1752857
theorem B1168647 : Blo 1168401 1168647 := bstep (se 1 (by rfl) ⟨876485, by rfl⟩ : syracuseStep 1168647 = 1752971) B1752971
theorem B1168655 : Blo 1168401 1168655 := bstep (se 1 (by rfl) ⟨876491, by rfl⟩ : syracuseStep 1168655 = 1752983) B1752983
theorem B2495777 : Blo 1168401 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B8885537 : Blo 1168401 8885537 := bstep (se 2 (by rfl) ⟨3332076, by rfl⟩ : syracuseStep 8885537 = 6664153) B6664153
theorem B1168699 : Blo 1168401 1168699 := bstep (se 1 (by rfl) ⟨876524, by rfl⟩ : syracuseStep 1168699 = 1753049) B1753049
theorem B1873211 : Blo 1168401 1873211 := bstep (se 1 (by rfl) ⟨1404908, by rfl⟩ : syracuseStep 1873211 = 2809817) B2809817
theorem B1316155 : Blo 1168401 1316155 := bstep (se 1 (by rfl) ⟨987116, by rfl⟩ : syracuseStep 1316155 = 1974233) B1974233
theorem B2495863 : Blo 1168401 2495863 := bstep (se 1 (by rfl) ⟨1871897, by rfl⟩ : syracuseStep 2495863 = 3743795) B3743795
theorem B1168775 : Blo 1168401 1168775 := bstep (se 1 (by rfl) ⟨876581, by rfl⟩ : syracuseStep 1168775 = 1753163) B1753163
theorem B1168783 : Blo 1168401 1168783 := bstep (se 1 (by rfl) ⟨876587, by rfl⟩ : syracuseStep 1168783 = 1753175) B1753175
theorem B72955313 : Blo 1168401 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B1168827 : Blo 1168401 1168827 := bstep (se 1 (by rfl) ⟨876620, by rfl⟩ : syracuseStep 1168827 = 1753241) B1753241
theorem B1480123 : Blo 1168401 1480123 := bstep (se 1 (by rfl) ⟨1110092, by rfl⟩ : syracuseStep 1480123 = 2220185) B2220185
theorem B1168903 : Blo 1168401 1168903 := bstep (se 1 (by rfl) ⟨876677, by rfl⟩ : syracuseStep 1168903 = 1753355) B1753355
theorem B3945995 : Blo 1168401 3945995 := bstep (se 1 (by rfl) ⟨2959496, by rfl⟩ : syracuseStep 3945995 = 5918993) B5918993
theorem B1168911 : Blo 1168401 1168911 := bstep (se 1 (by rfl) ⟨876683, by rfl⟩ : syracuseStep 1168911 = 1753367) B1753367
theorem B1168955 : Blo 1168401 1168955 := bstep (se 1 (by rfl) ⟨876716, by rfl⟩ : syracuseStep 1168955 = 1753433) B1753433
theorem B21345869 : Blo 1168401 21345869 := bstep (se 3 (by rfl) ⟨4002350, by rfl⟩ : syracuseStep 21345869 = 8004701) B8004701
theorem B3946103 : Blo 1168401 3946103 := bstep (se 1 (by rfl) ⟨2959577, by rfl⟩ : syracuseStep 3946103 = 5919155) B5919155
theorem B1169031 : Blo 1168401 1169031 := bstep (se 1 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 1169031 = 1753547) B1753547
theorem B1169039 : Blo 1168401 1169039 := bstep (se 1 (by rfl) ⟨876779, by rfl⟩ : syracuseStep 1169039 = 1753559) B1753559
theorem B1169083 : Blo 1168401 1169083 := bstep (se 1 (by rfl) ⟨876812, by rfl⟩ : syracuseStep 1169083 = 1753625) B1753625
theorem B8877761 : Blo 1168401 8877761 := bstep (se 2 (by rfl) ⟨3329160, by rfl⟩ : syracuseStep 8877761 = 6658321) B6658321
theorem B1169159 : Blo 1168401 1169159 := bstep (se 1 (by rfl) ⟨876869, by rfl⟩ : syracuseStep 1169159 = 1753739) B1753739
theorem B1169167 : Blo 1168401 1169167 := bstep (se 1 (by rfl) ⟨876875, by rfl⟩ : syracuseStep 1169167 = 1753751) B1753751
theorem B1316623 : Blo 1168401 1316623 := bstep (se 1 (by rfl) ⟨987467, by rfl⟩ : syracuseStep 1316623 = 1974935) B1974935
theorem B1169211 : Blo 1168401 1169211 := bstep (se 1 (by rfl) ⟨876908, by rfl⟩ : syracuseStep 1169211 = 1753817) B1753817
theorem B1169287 : Blo 1168401 1169287 := bstep (se 1 (by rfl) ⟨876965, by rfl⟩ : syracuseStep 1169287 = 1753931) B1753931
theorem B3331975 : Blo 1168401 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B1169295 : Blo 1168401 1169295 := bstep (se 1 (by rfl) ⟨876971, by rfl⟩ : syracuseStep 1169295 = 1753943) B1753943
theorem B9983897 : Blo 1168401 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B1480619 : Blo 1168401 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B1169339 : Blo 1168401 1169339 := bstep (se 1 (by rfl) ⟨877004, by rfl⟩ : syracuseStep 1169339 = 1754009) B1754009
theorem B1169415 : Blo 1168401 1169415 := bstep (se 1 (by rfl) ⟨877061, by rfl⟩ : syracuseStep 1169415 = 1754123) B1754123
theorem B1169423 : Blo 1168401 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B3602465 : Blo 1168401 3602465 := bstep (se 2 (by rfl) ⟨1350924, by rfl⟩ : syracuseStep 3602465 = 2701849) B2701849
theorem B1169467 : Blo 1168401 1169467 := bstep (se 1 (by rfl) ⟨877100, by rfl⟩ : syracuseStep 1169467 = 1754201) B1754201
theorem B1972343 : Blo 1168401 1972343 := bstep (se 1 (by rfl) ⟨1479257, by rfl⟩ : syracuseStep 1972343 = 2958515) B2958515
theorem B1169543 : Blo 1168401 1169543 := bstep (se 1 (by rfl) ⟨877157, by rfl⟩ : syracuseStep 1169543 = 1754315) B1754315
theorem B1169551 : Blo 1168401 1169551 := bstep (se 1 (by rfl) ⟨877163, by rfl⟩ : syracuseStep 1169551 = 1754327) B1754327
theorem B3332249 : Blo 1168401 3332249 := bstep (se 2 (by rfl) ⟨1249593, by rfl⟩ : syracuseStep 3332249 = 2499187) B2499187
theorem B1710265 : Blo 1168401 1710265 := bstep (se 2 (by rfl) ⟨641349, by rfl⟩ : syracuseStep 1710265 = 1282699) B1282699
theorem B1169595 : Blo 1168401 1169595 := bstep (se 1 (by rfl) ⟨877196, by rfl⟩ : syracuseStep 1169595 = 1754393) B1754393
theorem B3946697 : Blo 1168401 3946697 := bstep (se 2 (by rfl) ⟨1480011, by rfl⟩ : syracuseStep 3946697 = 2960023) B2960023
theorem B12646601 : Blo 1168401 12646601 := bstep (se 2 (by rfl) ⟨4742475, by rfl⟩ : syracuseStep 12646601 = 9484951) B9484951
theorem B12646637 : Blo 1168401 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B8886509 : Blo 1168401 8886509 := bstep (se 3 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 8886509 = 3332441) B3332441
theorem B4438273 : Blo 1168401 4438273 := bstep (se 2 (by rfl) ⟨1664352, by rfl⟩ : syracuseStep 4438273 = 3328705) B3328705
theorem B1169671 : Blo 1168401 1169671 := bstep (se 1 (by rfl) ⟨877253, by rfl⟩ : syracuseStep 1169671 = 1754507) B1754507
theorem B1169679 : Blo 1168401 1169679 := bstep (se 1 (by rfl) ⟨877259, by rfl⟩ : syracuseStep 1169679 = 1754519) B1754519
theorem B1169723 : Blo 1168401 1169723 := bstep (se 1 (by rfl) ⟨877292, by rfl⟩ : syracuseStep 1169723 = 1754585) B1754585
theorem B1333639 : Blo 1168401 1333639 := bstep (se 1 (by rfl) ⟨1000229, by rfl⟩ : syracuseStep 1333639 = 2000459) B2000459
theorem B1169799 : Blo 1168401 1169799 := bstep (se 1 (by rfl) ⟨877349, by rfl⟩ : syracuseStep 1169799 = 1754699) B1754699
theorem B1481095 : Blo 1168401 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B1169807 : Blo 1168401 1169807 := bstep (se 1 (by rfl) ⟨877355, by rfl⟩ : syracuseStep 1169807 = 1754711) B1754711
theorem B2808211 : Blo 1168401 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B1169851 : Blo 1168401 1169851 := bstep (se 1 (by rfl) ⟨877388, by rfl⟩ : syracuseStep 1169851 = 1754777) B1754777
theorem B21322225 : Blo 1168401 21322225 := bstep (se 2 (by rfl) ⟨7995834, by rfl⟩ : syracuseStep 21322225 = 15991669) B15991669
theorem B1169927 : Blo 1168401 1169927 := bstep (se 1 (by rfl) ⟨877445, by rfl⟩ : syracuseStep 1169927 = 1754891) B1754891
theorem B1169935 : Blo 1168401 1169935 := bstep (se 1 (by rfl) ⟨877451, by rfl⟩ : syracuseStep 1169935 = 1754903) B1754903
theorem B2218529 : Blo 1168401 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B1972795 : Blo 1168401 1972795 := bstep (se 1 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 1972795 = 2959193) B2959193
theorem B1169979 : Blo 1168401 1169979 := bstep (se 1 (by rfl) ⟨877484, by rfl⟩ : syracuseStep 1169979 = 1754969) B1754969
theorem B9476675 : Blo 1168401 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B11246147 : Blo 1168401 11246147 := bstep (se 1 (by rfl) ⟨8434610, by rfl⟩ : syracuseStep 11246147 = 16869221) B16869221
theorem B8428151 : Blo 1168401 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B1170055 : Blo 1168401 1170055 := bstep (se 1 (by rfl) ⟨877541, by rfl⟩ : syracuseStep 1170055 = 1755083) B1755083
theorem B1170063 : Blo 1168401 1170063 := bstep (se 1 (by rfl) ⟨877547, by rfl⟩ : syracuseStep 1170063 = 1755095) B1755095
theorem B2218681 : Blo 1168401 2218681 := bstep (se 2 (by rfl) ⟨832005, by rfl⟩ : syracuseStep 2218681 = 1664011) B1664011
theorem B1579705 : Blo 1168401 1579705 := bstep (se 2 (by rfl) ⟨592389, by rfl⟩ : syracuseStep 1579705 = 1184779) B1184779
theorem B1170107 : Blo 1168401 1170107 := bstep (se 1 (by rfl) ⟨877580, by rfl⟩ : syracuseStep 1170107 = 1755161) B1755161
theorem B1972937 : Blo 1168401 1972937 := bstep (se 2 (by rfl) ⟨739851, by rfl⟩ : syracuseStep 1972937 = 1479703) B1479703
theorem B1170183 : Blo 1168401 1170183 := bstep (se 1 (by rfl) ⟨877637, by rfl⟩ : syracuseStep 1170183 = 1755275) B1755275
theorem B2808587 : Blo 1168401 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B1170191 : Blo 1168401 1170191 := bstep (se 1 (by rfl) ⟨877643, by rfl⟩ : syracuseStep 1170191 = 1755287) B1755287
theorem B3332897 : Blo 1168401 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B1170235 : Blo 1168401 1170235 := bstep (se 1 (by rfl) ⟨877676, by rfl⟩ : syracuseStep 1170235 = 1755353) B1755353
theorem B3947399 : Blo 1168401 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B1170311 : Blo 1168401 1170311 := bstep (se 1 (by rfl) ⟨877733, by rfl⟩ : syracuseStep 1170311 = 1755467) B1755467
theorem B1170319 : Blo 1168401 1170319 := bstep (se 1 (by rfl) ⟨877739, by rfl⟩ : syracuseStep 1170319 = 1755479) B1755479
theorem B1170363 : Blo 1168401 1170363 := bstep (se 1 (by rfl) ⟨877772, by rfl⟩ : syracuseStep 1170363 = 1755545) B1755545
theorem B3161099 : Blo 1168401 3161099 := bstep (se 1 (by rfl) ⟨2370824, by rfl⟩ : syracuseStep 3161099 = 4741649) B4741649
theorem B5618807 : Blo 1168401 5618807 := bstep (se 1 (by rfl) ⟨4214105, by rfl⟩ : syracuseStep 5618807 = 8428211) B8428211
theorem B3947777 : Blo 1168401 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B6495623 : Blo 1168401 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1973639 : Blo 1168401 1973639 := bstep (se 1 (by rfl) ⟨1480229, by rfl⟩ : syracuseStep 1973639 = 2960459) B2960459
theorem B5922233 : Blo 1168401 5922233 := bstep (se 2 (by rfl) ⟨2220837, by rfl⟩ : syracuseStep 5922233 = 4441675) B4441675
theorem B6323665 : Blo 1168401 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B1752635 : Blo 1168401 1752635 := bstep (se 1 (by rfl) ⟨1314476, by rfl⟩ : syracuseStep 1752635 = 2628953) B2628953
theorem B19971683 : Blo 1168401 19971683 := bstep (se 1 (by rfl) ⟨14978762, by rfl⟩ : syracuseStep 19971683 = 29957525) B29957525
theorem B24010339 : Blo 1168401 24010339 := bstep (se 1 (by rfl) ⟨18007754, by rfl⟩ : syracuseStep 24010339 = 36015509) B36015509
theorem B1752695 : Blo 1168401 1752695 := bstep (se 1 (by rfl) ⟨1314521, by rfl⟩ : syracuseStep 1752695 = 2629043) B2629043
theorem B1752719 : Blo 1168401 1752719 := bstep (se 1 (by rfl) ⟨1314539, by rfl⟩ : syracuseStep 1752719 = 2629079) B2629079
theorem B1752761 : Blo 1168401 1752761 := bstep (se 2 (by rfl) ⟨657285, by rfl⟩ : syracuseStep 1752761 = 1314571) B1314571
theorem B3374849 : Blo 1168401 3374849 := bstep (se 2 (by rfl) ⟨1265568, by rfl⟩ : syracuseStep 3374849 = 2531137) B2531137
theorem B1752839 : Blo 1168401 1752839 := bstep (se 1 (by rfl) ⟨1314629, by rfl⟩ : syracuseStep 1752839 = 2629259) B2629259
theorem B1752875 : Blo 1168401 1752875 := bstep (se 1 (by rfl) ⟨1314656, by rfl⟩ : syracuseStep 1752875 = 2629313) B2629313
theorem B1752905 : Blo 1168401 1752905 := bstep (se 2 (by rfl) ⟨657339, by rfl⟩ : syracuseStep 1752905 = 1314679) B1314679
theorem B2629511 : Blo 1168401 2629511 := bstep (se 1 (by rfl) ⟨1972133, by rfl⟩ : syracuseStep 2629511 = 3944267) B3944267
theorem B1580971 : Blo 1168401 1580971 := bstep (se 1 (by rfl) ⟨1185728, by rfl⟩ : syracuseStep 1580971 = 2371457) B2371457
theorem B1753019 : Blo 1168401 1753019 := bstep (se 1 (by rfl) ⟨1314764, by rfl⟩ : syracuseStep 1753019 = 2629529) B2629529
theorem B1753079 : Blo 1168401 1753079 := bstep (se 1 (by rfl) ⟨1314809, by rfl⟩ : syracuseStep 1753079 = 2629619) B2629619
theorem B1753097 : Blo 1168401 1753097 := bstep (se 2 (by rfl) ⟨657411, by rfl⟩ : syracuseStep 1753097 = 1314823) B1314823
theorem B2220041 : Blo 1168401 2220041 := bstep (se 2 (by rfl) ⟨832515, by rfl⟩ : syracuseStep 2220041 = 1665031) B1665031
theorem B1753127 : Blo 1168401 1753127 := bstep (se 1 (by rfl) ⟨1314845, by rfl⟩ : syracuseStep 1753127 = 2629691) B2629691
theorem B1753211 : Blo 1168401 1753211 := bstep (se 1 (by rfl) ⟨1314908, by rfl⟩ : syracuseStep 1753211 = 2629817) B2629817
theorem B1974395 : Blo 1168401 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B4440217 : Blo 1168401 4440217 := bstep (se 2 (by rfl) ⟨1665081, by rfl⟩ : syracuseStep 4440217 = 3330163) B3330163
theorem B1753337 : Blo 1168401 1753337 := bstep (se 2 (by rfl) ⟨657501, by rfl⟩ : syracuseStep 1753337 = 1315003) B1315003
theorem B1753439 : Blo 1168401 1753439 := bstep (se 1 (by rfl) ⟨1315079, by rfl⟩ : syracuseStep 1753439 = 2630159) B2630159
theorem B1753451 : Blo 1168401 1753451 := bstep (se 1 (by rfl) ⟨1315088, by rfl⟩ : syracuseStep 1753451 = 2630177) B2630177
theorem B4440521 : Blo 1168401 4440521 := bstep (se 2 (by rfl) ⟨1665195, by rfl⟩ : syracuseStep 4440521 = 3330391) B3330391
theorem B3949019 : Blo 1168401 3949019 := bstep (se 1 (by rfl) ⟨2961764, by rfl⟩ : syracuseStep 3949019 = 5923529) B5923529
theorem B1778185 : Blo 1168401 1778185 := bstep (se 2 (by rfl) ⟨666819, by rfl⟩ : syracuseStep 1778185 = 1333639) B1333639
theorem B1974793 : Blo 1168401 1974793 := bstep (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) B1481095
theorem B3744281 : Blo 1168401 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B1753679 : Blo 1168401 1753679 := bstep (se 1 (by rfl) ⟨1315259, by rfl⟩ : syracuseStep 1753679 = 2630519) B2630519
theorem B2630267 : Blo 1168401 2630267 := bstep (se 1 (by rfl) ⟨1972700, by rfl⟩ : syracuseStep 2630267 = 3945401) B3945401
theorem B1974955 : Blo 1168401 1974955 := bstep (se 1 (by rfl) ⟨1481216, by rfl⟩ : syracuseStep 1974955 = 2962433) B2962433
theorem B1753799 : Blo 1168401 1753799 := bstep (se 1 (by rfl) ⟨1315349, by rfl⟩ : syracuseStep 1753799 = 2630699) B2630699
theorem B4809415 : Blo 1168401 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B4809431 : Blo 1168401 4809431 := bstep (se 1 (by rfl) ⟨3607073, by rfl⟩ : syracuseStep 4809431 = 7214147) B7214147
theorem B2630393 : Blo 1168401 2630393 := bstep (se 2 (by rfl) ⟨986397, by rfl⟩ : syracuseStep 2630393 = 1972795) B1972795
theorem B1753961 : Blo 1168401 1753961 := bstep (se 2 (by rfl) ⟨657735, by rfl⟩ : syracuseStep 1753961 = 1315471) B1315471
theorem B5923691 : Blo 1168401 5923691 := bstep (se 1 (by rfl) ⟨4442768, by rfl⟩ : syracuseStep 5923691 = 8885537) B8885537
theorem B2958241 : Blo 1168401 2958241 := bstep (se 2 (by rfl) ⟨1109340, by rfl⟩ : syracuseStep 2958241 = 2218681) B2218681
theorem B4441007 : Blo 1168401 4441007 := bstep (se 1 (by rfl) ⟨3330755, by rfl⟩ : syracuseStep 4441007 = 6661511) B6661511
theorem B1754039 : Blo 1168401 1754039 := bstep (se 1 (by rfl) ⟨1315529, by rfl⟩ : syracuseStep 1754039 = 2631059) B2631059
theorem B48636875 : Blo 1168401 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B1754075 : Blo 1168401 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B15188957 : Blo 1168401 15188957 := bstep (se 3 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 15188957 = 5695859) B5695859
theorem B2630663 : Blo 1168401 2630663 := bstep (se 1 (by rfl) ⟨1972997, by rfl⟩ : syracuseStep 2630663 = 3945995) B3945995
theorem B14230579 : Blo 1168401 14230579 := bstep (se 1 (by rfl) ⟨10672934, by rfl⟩ : syracuseStep 14230579 = 21345869) B21345869
theorem B2630735 : Blo 1168401 2630735 := bstep (se 1 (by rfl) ⟨1973051, by rfl⟩ : syracuseStep 2630735 = 3946103) B3946103
theorem B3949721 : Blo 1168401 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B2401643 : Blo 1168401 2401643 := bstep (se 1 (by rfl) ⟨1801232, by rfl⟩ : syracuseStep 2401643 = 3602465) B3602465
theorem B9995683 : Blo 1168401 9995683 := bstep (se 1 (by rfl) ⟨7496762, by rfl⟩ : syracuseStep 9995683 = 14993525) B14993525
theorem B5916077 : Blo 1168401 5916077 := bstep (se 3 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 5916077 = 2218529) B2218529
theorem B1754543 : Blo 1168401 1754543 := bstep (se 1 (by rfl) ⟨1315907, by rfl⟩ : syracuseStep 1754543 = 2631815) B2631815
theorem B2221499 : Blo 1168401 2221499 := bstep (se 1 (by rfl) ⟨1666124, by rfl⟩ : syracuseStep 2221499 = 3332249) B3332249
theorem B2631131 : Blo 1168401 2631131 := bstep (se 1 (by rfl) ⟨1973348, by rfl⟩ : syracuseStep 2631131 = 3946697) B3946697
theorem B8431067 : Blo 1168401 8431067 := bstep (se 1 (by rfl) ⟨6323300, by rfl⟩ : syracuseStep 8431067 = 12646601) B12646601
theorem B3327475 : Blo 1168401 3327475 := bstep (se 1 (by rfl) ⟨2495606, by rfl⟩ : syracuseStep 3327475 = 4991213) B4991213
theorem B8431091 : Blo 1168401 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B5924339 : Blo 1168401 5924339 := bstep (se 1 (by rfl) ⟨4443254, by rfl⟩ : syracuseStep 5924339 = 8886509) B8886509
theorem B1754633 : Blo 1168401 1754633 := bstep (se 2 (by rfl) ⟨657987, by rfl⟩ : syracuseStep 1754633 = 1315975) B1315975
theorem B1754663 : Blo 1168401 1754663 := bstep (se 1 (by rfl) ⟨1315997, by rfl⟩ : syracuseStep 1754663 = 2631995) B2631995
theorem B1754747 : Blo 1168401 1754747 := bstep (se 1 (by rfl) ⟨1316060, by rfl⟩ : syracuseStep 1754747 = 2632121) B2632121
theorem B6317783 : Blo 1168401 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B7497431 : Blo 1168401 7497431 := bstep (se 1 (by rfl) ⟨5623073, by rfl⟩ : syracuseStep 7497431 = 11246147) B11246147
theorem B1754873 : Blo 1168401 1754873 := bstep (se 2 (by rfl) ⟨658077, by rfl⟩ : syracuseStep 1754873 = 1316155) B1316155
theorem B3327817 : Blo 1168401 3327817 := bstep (se 2 (by rfl) ⟨1247931, by rfl⟩ : syracuseStep 3327817 = 2495863) B2495863
theorem B1754975 : Blo 1168401 1754975 := bstep (se 1 (by rfl) ⟨1316231, by rfl⟩ : syracuseStep 1754975 = 2632463) B2632463
theorem B1754987 : Blo 1168401 1754987 := bstep (se 1 (by rfl) ⟨1316240, by rfl⟩ : syracuseStep 1754987 = 2632481) B2632481
theorem B2221931 : Blo 1168401 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B2631599 : Blo 1168401 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B8431553 : Blo 1168401 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B2107399 : Blo 1168401 2107399 := bstep (se 1 (by rfl) ⟨1580549, by rfl⟩ : syracuseStep 2107399 = 3161099) B3161099
theorem B3745871 : Blo 1168401 3745871 := bstep (se 1 (by rfl) ⟨2809403, by rfl⟩ : syracuseStep 3745871 = 5618807) B5618807
theorem B1755215 : Blo 1168401 1755215 := bstep (se 1 (by rfl) ⟨1316411, by rfl⟩ : syracuseStep 1755215 = 2632823) B2632823
theorem B3377309 : Blo 1168401 3377309 := bstep (se 3 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 3377309 = 1266491) B1266491
theorem B2631851 : Blo 1168401 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B1755335 : Blo 1168401 1755335 := bstep (se 1 (by rfl) ⟨1316501, by rfl⟩ : syracuseStep 1755335 = 2633003) B2633003
theorem B6080779 : Blo 1168401 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B13502771 : Blo 1168401 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B1755497 : Blo 1168401 1755497 := bstep (se 2 (by rfl) ⟨658311, by rfl⟩ : syracuseStep 1755497 = 1316623) B1316623
theorem B3000719 : Blo 1168401 3000719 := bstep (se 1 (by rfl) ⟨2250539, by rfl⟩ : syracuseStep 3000719 = 4501079) B4501079
theorem B13314455 : Blo 1168401 13314455 := bstep (se 1 (by rfl) ⟨9985841, by rfl⟩ : syracuseStep 13314455 = 19971683) B19971683
theorem B15198617 : Blo 1168401 15198617 := bstep (se 2 (by rfl) ⟨5699481, by rfl⟩ : syracuseStep 15198617 = 11398963) B11398963
theorem B1755575 : Blo 1168401 1755575 := bstep (se 1 (by rfl) ⟨1316681, by rfl⟩ : syracuseStep 1755575 = 2633363) B2633363
theorem B6654473 : Blo 1168401 6654473 := bstep (se 2 (by rfl) ⟨2495427, by rfl⟩ : syracuseStep 6654473 = 4990855) B4990855
theorem B4442633 : Blo 1168401 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B2107961 : Blo 1168401 2107961 := bstep (se 2 (by rfl) ⟨790485, by rfl⟩ : syracuseStep 2107961 = 1580971) B1580971
theorem B2632391 : Blo 1168401 2632391 := bstep (se 1 (by rfl) ⟨1974293, by rfl⟩ : syracuseStep 2632391 = 3948587) B3948587
theorem B2280353 : Blo 1168401 2280353 := bstep (se 2 (by rfl) ⟨855132, by rfl⟩ : syracuseStep 2280353 = 1710265) B1710265
theorem B5917697 : Blo 1168401 5917697 := bstep (se 2 (by rfl) ⟨2219136, by rfl⟩ : syracuseStep 5917697 = 4438273) B4438273
theorem B4271105 : Blo 1168401 4271105 := bstep (se 2 (by rfl) ⟨1601664, by rfl⟩ : syracuseStep 4271105 = 3203329) B3203329
theorem B2108423 : Blo 1168401 2108423 := bstep (se 1 (by rfl) ⟨1581317, by rfl⟩ : syracuseStep 2108423 = 3162635) B3162635
theorem B8432707 : Blo 1168401 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B6655223 : Blo 1168401 6655223 := bstep (se 1 (by rfl) ⟨4991417, by rfl⟩ : syracuseStep 6655223 = 9982835) B9982835
theorem B28429633 : Blo 1168401 28429633 := bstep (se 2 (by rfl) ⟨10661112, by rfl⟩ : syracuseStep 28429633 = 21322225) B21322225
theorem B2960783 : Blo 1168401 2960783 := bstep (se 1 (by rfl) ⟨2220587, by rfl⟩ : syracuseStep 2960783 = 4441175) B4441175
theorem B5615021 : Blo 1168401 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B6655405 : Blo 1168401 6655405 := bstep (se 3 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 6655405 = 2495777) B2495777
theorem B2633255 : Blo 1168401 2633255 := bstep (se 1 (by rfl) ⟨1974941, by rfl⟩ : syracuseStep 2633255 = 3949883) B3949883
theorem B2961107 : Blo 1168401 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B14995165 : Blo 1168401 14995165 := bstep (se 3 (by rfl) ⟨2811593, by rfl⟩ : syracuseStep 14995165 = 5623187) B5623187
theorem B10669805 : Blo 1168401 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B16854799 : Blo 1168401 16854799 := bstep (se 1 (by rfl) ⟨12641099, by rfl⟩ : syracuseStep 16854799 = 25282199) B25282199
theorem B5918507 : Blo 1168401 5918507 := bstep (se 1 (by rfl) ⟨4438880, by rfl⟩ : syracuseStep 5918507 = 8877761) B8877761
theorem B3944375 : Blo 1168401 3944375 := bstep (se 1 (by rfl) ⟨2958281, by rfl⟩ : syracuseStep 3944375 = 5916563) B5916563
theorem B6655931 : Blo 1168401 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B1314895 : Blo 1168401 1314895 := bstep (se 1 (by rfl) ⟨986171, by rfl⟩ : syracuseStep 1314895 = 1972343) B1972343
theorem B9998417 : Blo 1168401 9998417 := bstep (se 2 (by rfl) ⟨3749406, by rfl⟩ : syracuseStep 9998417 = 7498813) B7498813
theorem B22475069 : Blo 1168401 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B4436329 : Blo 1168401 4436329 := bstep (se 2 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 4436329 = 3327247) B3327247
theorem B1315291 : Blo 1168401 1315291 := bstep (se 1 (by rfl) ⟨986468, by rfl⟩ : syracuseStep 1315291 = 1972937) B1972937
theorem B1872391 : Blo 1168401 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B3944969 : Blo 1168401 3944969 := bstep (se 2 (by rfl) ⟨1479363, by rfl⟩ : syracuseStep 3944969 = 2958727) B2958727
theorem B4436603 : Blo 1168401 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B18977489 : Blo 1168401 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B2962271 : Blo 1168401 2962271 := bstep (se 1 (by rfl) ⟨2221703, by rfl⟩ : syracuseStep 2962271 = 4443407) B4443407
theorem B4330415 : Blo 1168401 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B1315759 : Blo 1168401 1315759 := bstep (se 1 (by rfl) ⟨986819, by rfl⟩ : syracuseStep 1315759 = 1973639) B1973639
theorem B1168423 : Blo 1168401 1168423 := bstep (se 1 (by rfl) ⟨876317, by rfl⟩ : syracuseStep 1168423 = 1752635) B1752635
theorem B4502585 : Blo 1168401 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B1168463 : Blo 1168401 1168463 := bstep (se 1 (by rfl) ⟨876347, by rfl⟩ : syracuseStep 1168463 = 1752695) B1752695
theorem B1168479 : Blo 1168401 1168479 := bstep (se 1 (by rfl) ⟨876359, by rfl⟩ : syracuseStep 1168479 = 1752719) B1752719
theorem B1168507 : Blo 1168401 1168507 := bstep (se 1 (by rfl) ⟨876380, by rfl⟩ : syracuseStep 1168507 = 1752761) B1752761
theorem B2249899 : Blo 1168401 2249899 := bstep (se 1 (by rfl) ⟨1687424, by rfl⟩ : syracuseStep 2249899 = 3374849) B3374849
theorem B1168559 : Blo 1168401 1168559 := bstep (se 1 (by rfl) ⟨876419, by rfl⟩ : syracuseStep 1168559 = 1752839) B1752839
theorem B1168583 : Blo 1168401 1168583 := bstep (se 1 (by rfl) ⟨876437, by rfl⟩ : syracuseStep 1168583 = 1752875) B1752875
theorem B1168603 : Blo 1168401 1168603 := bstep (se 1 (by rfl) ⟨876452, by rfl⟩ : syracuseStep 1168603 = 1752905) B1752905
theorem B1168679 : Blo 1168401 1168679 := bstep (se 1 (by rfl) ⟨876509, by rfl⟩ : syracuseStep 1168679 = 1753019) B1753019
theorem B1168719 : Blo 1168401 1168719 := bstep (se 1 (by rfl) ⟨876539, by rfl⟩ : syracuseStep 1168719 = 1753079) B1753079
theorem B1168735 : Blo 1168401 1168735 := bstep (se 1 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 1168735 = 1753103) B1753103
theorem B1316191 : Blo 1168401 1316191 := bstep (se 1 (by rfl) ⟨987143, by rfl⟩ : syracuseStep 1316191 = 1974287) B1974287
theorem B30365027 : Blo 1168401 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B3945833 : Blo 1168401 3945833 := bstep (se 2 (by rfl) ⟨1479687, by rfl⟩ : syracuseStep 3945833 = 2959375) B2959375
theorem B1168763 : Blo 1168401 1168763 := bstep (se 1 (by rfl) ⟨876572, by rfl⟩ : syracuseStep 1168763 = 1753145) B1753145
theorem B16012691 : Blo 1168401 16012691 := bstep (se 1 (by rfl) ⟨12009518, by rfl⟩ : syracuseStep 16012691 = 24019037) B24019037
theorem B1168815 : Blo 1168401 1168815 := bstep (se 1 (by rfl) ⟨876611, by rfl⟩ : syracuseStep 1168815 = 1753223) B1753223
theorem B1168839 : Blo 1168401 1168839 := bstep (se 1 (by rfl) ⟨876629, by rfl⟩ : syracuseStep 1168839 = 1753259) B1753259
theorem B1168859 : Blo 1168401 1168859 := bstep (se 1 (by rfl) ⟨876644, by rfl⟩ : syracuseStep 1168859 = 1753289) B1753289
theorem B1168935 : Blo 1168401 1168935 := bstep (se 1 (by rfl) ⟨876701, by rfl⟩ : syracuseStep 1168935 = 1753403) B1753403
theorem B1971769 : Blo 1168401 1971769 := bstep (se 2 (by rfl) ⟨739413, by rfl⟩ : syracuseStep 1971769 = 1478827) B1478827
theorem B1168975 : Blo 1168401 1168975 := bstep (se 1 (by rfl) ⟨876731, by rfl⟩ : syracuseStep 1168975 = 1753463) B1753463
theorem B1168991 : Blo 1168401 1168991 := bstep (se 1 (by rfl) ⟨876743, by rfl⟩ : syracuseStep 1168991 = 1753487) B1753487
theorem B1169019 : Blo 1168401 1169019 := bstep (se 1 (by rfl) ⟨876764, by rfl⟩ : syracuseStep 1169019 = 1753529) B1753529
theorem B1169071 : Blo 1168401 1169071 := bstep (se 1 (by rfl) ⟨876803, by rfl⟩ : syracuseStep 1169071 = 1753607) B1753607
theorem B1971911 : Blo 1168401 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B1169095 : Blo 1168401 1169095 := bstep (se 1 (by rfl) ⟨876821, by rfl⟩ : syracuseStep 1169095 = 1753643) B1753643
theorem B1316551 : Blo 1168401 1316551 := bstep (se 1 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 1316551 = 1974827) B1974827
theorem B1169115 : Blo 1168401 1169115 := bstep (se 1 (by rfl) ⟨876836, by rfl⟩ : syracuseStep 1169115 = 1753673) B1753673
theorem B1169191 : Blo 1168401 1169191 := bstep (se 1 (by rfl) ⟨876893, by rfl⟩ : syracuseStep 1169191 = 1753787) B1753787
theorem B4216643 : Blo 1168401 4216643 := bstep (se 1 (by rfl) ⟨3162482, by rfl⟩ : syracuseStep 4216643 = 6324965) B6324965
theorem B1169231 : Blo 1168401 1169231 := bstep (se 1 (by rfl) ⟨876923, by rfl⟩ : syracuseStep 1169231 = 1753847) B1753847
theorem B1169247 : Blo 1168401 1169247 := bstep (se 1 (by rfl) ⟨876935, by rfl⟩ : syracuseStep 1169247 = 1753871) B1753871
theorem B1972073 : Blo 1168401 1972073 := bstep (se 2 (by rfl) ⟨739527, by rfl⟩ : syracuseStep 1972073 = 1479055) B1479055
theorem B1169275 : Blo 1168401 1169275 := bstep (se 1 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 1169275 = 1753913) B1753913
theorem B1169327 : Blo 1168401 1169327 := bstep (se 1 (by rfl) ⟨876995, by rfl⟩ : syracuseStep 1169327 = 1753991) B1753991
theorem B3946427 : Blo 1168401 3946427 := bstep (se 1 (by rfl) ⟨2959820, by rfl⟩ : syracuseStep 3946427 = 5919641) B5919641
theorem B1169351 : Blo 1168401 1169351 := bstep (se 1 (by rfl) ⟨877013, by rfl⟩ : syracuseStep 1169351 = 1754027) B1754027
theorem B1169371 : Blo 1168401 1169371 := bstep (se 1 (by rfl) ⟨877028, by rfl⟩ : syracuseStep 1169371 = 1754057) B1754057
theorem B5920775 : Blo 1168401 5920775 := bstep (se 1 (by rfl) ⟨4440581, by rfl⟩ : syracuseStep 5920775 = 8881163) B8881163
theorem B1169447 : Blo 1168401 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B1169487 : Blo 1168401 1169487 := bstep (se 1 (by rfl) ⟨877115, by rfl⟩ : syracuseStep 1169487 = 1754231) B1754231
theorem B1169503 : Blo 1168401 1169503 := bstep (se 1 (by rfl) ⟨877127, by rfl⟩ : syracuseStep 1169503 = 1754255) B1754255
theorem B1169531 : Blo 1168401 1169531 := bstep (se 1 (by rfl) ⟨877148, by rfl⟩ : syracuseStep 1169531 = 1754297) B1754297
theorem B4995229 : Blo 1168401 4995229 := bstep (se 3 (by rfl) ⟨936605, by rfl⟩ : syracuseStep 4995229 = 1873211) B1873211
theorem B2496683 : Blo 1168401 2496683 := bstep (se 1 (by rfl) ⟨1872512, by rfl⟩ : syracuseStep 2496683 = 3745025) B3745025
theorem B1169583 : Blo 1168401 1169583 := bstep (se 1 (by rfl) ⟨877187, by rfl⟩ : syracuseStep 1169583 = 1754375) B1754375
theorem B1169607 : Blo 1168401 1169607 := bstep (se 1 (by rfl) ⟨877205, by rfl⟩ : syracuseStep 1169607 = 1754411) B1754411
theorem B2218195 : Blo 1168401 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B1169627 : Blo 1168401 1169627 := bstep (se 1 (by rfl) ⟨877220, by rfl⟩ : syracuseStep 1169627 = 1754441) B1754441
theorem B1972471 : Blo 1168401 1972471 := bstep (se 1 (by rfl) ⟨1479353, by rfl⟩ : syracuseStep 1972471 = 2958707) B2958707
theorem B1169703 : Blo 1168401 1169703 := bstep (se 1 (by rfl) ⟨877277, by rfl⟩ : syracuseStep 1169703 = 1754555) B1754555
theorem B1169743 : Blo 1168401 1169743 := bstep (se 1 (by rfl) ⟨877307, by rfl⟩ : syracuseStep 1169743 = 1754615) B1754615
theorem B1169759 : Blo 1168401 1169759 := bstep (se 1 (by rfl) ⟨877319, by rfl⟩ : syracuseStep 1169759 = 1754639) B1754639
theorem B1169787 : Blo 1168401 1169787 := bstep (se 1 (by rfl) ⟨877340, by rfl⟩ : syracuseStep 1169787 = 1754681) B1754681
theorem B1169839 : Blo 1168401 1169839 := bstep (se 1 (by rfl) ⟨877379, by rfl⟩ : syracuseStep 1169839 = 1754759) B1754759
theorem B2218423 : Blo 1168401 2218423 := bstep (se 1 (by rfl) ⟨1663817, by rfl⟩ : syracuseStep 2218423 = 3327635) B3327635
theorem B1972667 : Blo 1168401 1972667 := bstep (se 1 (by rfl) ⟨1479500, by rfl⟩ : syracuseStep 1972667 = 2959001) B2959001
theorem B1169863 : Blo 1168401 1169863 := bstep (se 1 (by rfl) ⟨877397, by rfl⟩ : syracuseStep 1169863 = 1754795) B1754795
theorem B1169883 : Blo 1168401 1169883 := bstep (se 1 (by rfl) ⟨877412, by rfl⟩ : syracuseStep 1169883 = 1754825) B1754825
theorem B5921261 : Blo 1168401 5921261 := bstep (se 3 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 5921261 = 2220473) B2220473
theorem B33700373 : Blo 1168401 33700373 := bstep (se 6 (by rfl) ⟨789852, by rfl⟩ : syracuseStep 33700373 = 1579705) B1579705
theorem B9984545 : Blo 1168401 9984545 := bstep (se 2 (by rfl) ⟨3744204, by rfl⟩ : syracuseStep 9984545 = 7488409) B7488409
theorem B1972775 : Blo 1168401 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B1169959 : Blo 1168401 1169959 := bstep (se 1 (by rfl) ⟨877469, by rfl⟩ : syracuseStep 1169959 = 1754939) B1754939
theorem B1169999 : Blo 1168401 1169999 := bstep (se 1 (by rfl) ⟨877499, by rfl⟩ : syracuseStep 1169999 = 1754999) B1754999
theorem B1170015 : Blo 1168401 1170015 := bstep (se 1 (by rfl) ⟨877511, by rfl⟩ : syracuseStep 1170015 = 1755023) B1755023
theorem B1170043 : Blo 1168401 1170043 := bstep (se 1 (by rfl) ⟨877532, by rfl⟩ : syracuseStep 1170043 = 1755065) B1755065
theorem B12638855 : Blo 1168401 12638855 := bstep (se 1 (by rfl) ⟨9479141, by rfl⟩ : syracuseStep 12638855 = 18958283) B18958283
theorem B1170095 : Blo 1168401 1170095 := bstep (se 1 (by rfl) ⟨877571, by rfl⟩ : syracuseStep 1170095 = 1755143) B1755143
theorem B1170119 : Blo 1168401 1170119 := bstep (se 1 (by rfl) ⟨877589, by rfl⟩ : syracuseStep 1170119 = 1755179) B1755179
theorem B8886995 : Blo 1168401 8886995 := bstep (se 1 (by rfl) ⟨6665246, by rfl⟩ : syracuseStep 8886995 = 13330493) B13330493
theorem B1170139 : Blo 1168401 1170139 := bstep (se 1 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 1170139 = 1755209) B1755209
theorem B91151119 : Blo 1168401 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B1170215 : Blo 1168401 1170215 := bstep (se 1 (by rfl) ⟨877661, by rfl⟩ : syracuseStep 1170215 = 1755323) B1755323
theorem B1973065 : Blo 1168401 1973065 := bstep (se 2 (by rfl) ⟨739899, by rfl⟩ : syracuseStep 1973065 = 1479799) B1479799
theorem B1170255 : Blo 1168401 1170255 := bstep (se 1 (by rfl) ⟨877691, by rfl⟩ : syracuseStep 1170255 = 1755383) B1755383
theorem B1170271 : Blo 1168401 1170271 := bstep (se 1 (by rfl) ⟨877703, by rfl⟩ : syracuseStep 1170271 = 1755407) B1755407
theorem B1973099 : Blo 1168401 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B1170299 : Blo 1168401 1170299 := bstep (se 1 (by rfl) ⟨877724, by rfl⟩ : syracuseStep 1170299 = 1755449) B1755449
theorem B1170351 : Blo 1168401 1170351 := bstep (se 1 (by rfl) ⟨877763, by rfl⟩ : syracuseStep 1170351 = 1755527) B1755527
theorem B1170375 : Blo 1168401 1170375 := bstep (se 1 (by rfl) ⟨877781, by rfl⟩ : syracuseStep 1170375 = 1755563) B1755563
theorem B1170395 : Blo 1168401 1170395 := bstep (se 1 (by rfl) ⟨877796, by rfl⟩ : syracuseStep 1170395 = 1755593) B1755593
theorem B2219015 : Blo 1168401 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B4742297 : Blo 1168401 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B1973497 : Blo 1168401 1973497 := bstep (se 2 (by rfl) ⟨740061, by rfl⟩ : syracuseStep 1973497 = 1480123) B1480123
theorem B5922071 : Blo 1168401 5922071 := bstep (se 1 (by rfl) ⟨4441553, by rfl⟩ : syracuseStep 5922071 = 8883107) B8883107
theorem B2629007 : Blo 1168401 2629007 := bstep (se 1 (by rfl) ⟨1971755, by rfl⟩ : syracuseStep 2629007 = 3943511) B3943511
theorem B7486921 : Blo 1168401 7486921 := bstep (se 2 (by rfl) ⟨2807595, by rfl⟩ : syracuseStep 7486921 = 5615191) B5615191
theorem B32013785 : Blo 1168401 32013785 := bstep (se 2 (by rfl) ⟨12005169, by rfl⟩ : syracuseStep 32013785 = 24010339) B24010339
theorem B1973767 : Blo 1168401 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B2809441 : Blo 1168401 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B3948155 : Blo 1168401 3948155 := bstep (se 1 (by rfl) ⟨2961116, by rfl⟩ : syracuseStep 3948155 = 5922233) B5922233
theorem B2629331 : Blo 1168401 2629331 := bstep (se 1 (by rfl) ⟨1971998, by rfl⟩ : syracuseStep 2629331 = 3943997) B3943997
theorem B14991065 : Blo 1168401 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B3948317 : Blo 1168401 3948317 := bstep (se 3 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 3948317 = 1480619) B1480619
theorem B2809673 : Blo 1168401 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B2219881 : Blo 1168401 2219881 := bstep (se 2 (by rfl) ⟨832455, by rfl⟩ : syracuseStep 2219881 = 1664911) B1664911
theorem B1753007 : Blo 1168401 1753007 := bstep (se 1 (by rfl) ⟨1314755, by rfl⟩ : syracuseStep 1753007 = 2629511) B2629511
theorem B1777583 : Blo 1168401 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1974199 : Blo 1168401 1974199 := bstep (se 1 (by rfl) ⟨1480649, by rfl⟩ : syracuseStep 1974199 = 2961299) B2961299
theorem B2809865 : Blo 1168401 2809865 := bstep (se 2 (by rfl) ⟨1053699, by rfl⟩ : syracuseStep 2809865 = 2107399) B2107399
theorem B1753193 : Blo 1168401 1753193 := bstep (se 2 (by rfl) ⟨657447, by rfl⟩ : syracuseStep 1753193 = 1314895) B1314895
theorem B6660305 : Blo 1168401 6660305 := bstep (se 2 (by rfl) ⟨2497614, by rfl⟩ : syracuseStep 6660305 = 4995229) B4995229
theorem B14983379 : Blo 1168401 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B2957593 : Blo 1168401 2957593 := bstep (se 2 (by rfl) ⟨1109097, by rfl⟩ : syracuseStep 2957593 = 2218195) B2218195
theorem B2629961 : Blo 1168401 2629961 := bstep (se 2 (by rfl) ⟨986235, by rfl⟩ : syracuseStep 2629961 = 1972471) B1972471
theorem B2629979 : Blo 1168401 2629979 := bstep (se 1 (by rfl) ⟨1972484, by rfl⟩ : syracuseStep 2629979 = 3944969) B3944969
theorem B2957735 : Blo 1168401 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B1753511 : Blo 1168401 1753511 := bstep (se 1 (by rfl) ⟨1315133, by rfl⟩ : syracuseStep 1753511 = 2630267) B2630267
theorem B5915105 : Blo 1168401 5915105 := bstep (se 2 (by rfl) ⟨2218164, by rfl⟩ : syracuseStep 5915105 = 4436329) B4436329
theorem B1753595 : Blo 1168401 1753595 := bstep (se 1 (by rfl) ⟨1315196, by rfl⟩ : syracuseStep 1753595 = 2630393) B2630393
theorem B1974847 : Blo 1168401 1974847 := bstep (se 1 (by rfl) ⟨1481135, by rfl⟩ : syracuseStep 1974847 = 2962271) B2962271
theorem B3949127 : Blo 1168401 3949127 := bstep (se 1 (by rfl) ⟨2961845, by rfl⟩ : syracuseStep 3949127 = 5923691) B5923691
theorem B2957897 : Blo 1168401 2957897 := bstep (se 2 (by rfl) ⟨1109211, by rfl⟩ : syracuseStep 2957897 = 2218423) B2218423
theorem B1753721 : Blo 1168401 1753721 := bstep (se 2 (by rfl) ⟨657645, by rfl⟩ : syracuseStep 1753721 = 1315291) B1315291
theorem B32424583 : Blo 1168401 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B10125971 : Blo 1168401 10125971 := bstep (se 1 (by rfl) ⟨7594478, by rfl⟩ : syracuseStep 10125971 = 15188957) B15188957
theorem B1753775 : Blo 1168401 1753775 := bstep (se 1 (by rfl) ⟨1315331, by rfl⟩ : syracuseStep 1753775 = 2630663) B2630663
theorem B1753823 : Blo 1168401 1753823 := bstep (se 1 (by rfl) ⟨1315367, by rfl⟩ : syracuseStep 1753823 = 2630735) B2630735
theorem B47997845 : Blo 1168401 47997845 := bstep (se 6 (by rfl) ⟨1124949, by rfl⟩ : syracuseStep 47997845 = 2249899) B2249899
theorem B20243351 : Blo 1168401 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B2630555 : Blo 1168401 2630555 := bstep (se 1 (by rfl) ⟨1972916, by rfl⟩ : syracuseStep 2630555 = 3945833) B3945833
theorem B10675127 : Blo 1168401 10675127 := bstep (se 1 (by rfl) ⟨8006345, by rfl⟩ : syracuseStep 10675127 = 16012691) B16012691
theorem B1754087 : Blo 1168401 1754087 := bstep (se 1 (by rfl) ⟨1315565, by rfl⟩ : syracuseStep 1754087 = 2631131) B2631131
theorem B5620711 : Blo 1168401 5620711 := bstep (se 1 (by rfl) ⟨4215533, by rfl⟩ : syracuseStep 5620711 = 8431067) B8431067
theorem B5620727 : Blo 1168401 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B3949559 : Blo 1168401 3949559 := bstep (se 1 (by rfl) ⟨2962169, by rfl⟩ : syracuseStep 3949559 = 5924339) B5924339
theorem B2630753 : Blo 1168401 2630753 := bstep (se 2 (by rfl) ⟨986532, by rfl⟩ : syracuseStep 2630753 = 1973065) B1973065
theorem B4211855 : Blo 1168401 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B4998287 : Blo 1168401 4998287 := bstep (se 1 (by rfl) ⟨3748715, by rfl⟩ : syracuseStep 4998287 = 7497431) B7497431
theorem B2811095 : Blo 1168401 2811095 := bstep (se 1 (by rfl) ⟨2108321, by rfl⟩ : syracuseStep 2811095 = 4216643) B4216643
theorem B1754345 : Blo 1168401 1754345 := bstep (se 2 (by rfl) ⟨657879, by rfl⟩ : syracuseStep 1754345 = 1315759) B1315759
theorem B1754399 : Blo 1168401 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B2630951 : Blo 1168401 2630951 := bstep (se 1 (by rfl) ⟨1973213, by rfl⟩ : syracuseStep 2630951 = 3946427) B3946427
theorem B5621035 : Blo 1168401 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B18974105 : Blo 1168401 18974105 := bstep (se 2 (by rfl) ⟨7115289, by rfl⟩ : syracuseStep 18974105 = 14230579) B14230579
theorem B1754567 : Blo 1168401 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B2000479 : Blo 1168401 2000479 := bstep (se 1 (by rfl) ⟨1500359, by rfl⟩ : syracuseStep 2000479 = 3000719) B3000719
theorem B2631329 : Blo 1168401 2631329 := bstep (se 2 (by rfl) ⟨986748, by rfl⟩ : syracuseStep 2631329 = 1973497) B1973497
theorem B37906177 : Blo 1168401 37906177 := bstep (se 2 (by rfl) ⟨14214816, by rfl⟩ : syracuseStep 37906177 = 28429633) B28429633
theorem B1754921 : Blo 1168401 1754921 := bstep (se 2 (by rfl) ⟨658095, by rfl⟩ : syracuseStep 1754921 = 1316191) B1316191
theorem B1754927 : Blo 1168401 1754927 := bstep (se 1 (by rfl) ⟨1316195, by rfl⟩ : syracuseStep 1754927 = 2632391) B2632391
theorem B5924663 : Blo 1168401 5924663 := bstep (se 1 (by rfl) ⟨4443497, by rfl⟩ : syracuseStep 5924663 = 8886995) B8886995
theorem B8873873 : Blo 1168401 8873873 := bstep (se 2 (by rfl) ⟨3327702, by rfl⟩ : syracuseStep 8873873 = 6655405) B6655405
theorem B2631689 : Blo 1168401 2631689 := bstep (se 2 (by rfl) ⟨986883, by rfl⟩ : syracuseStep 2631689 = 1973767) B1973767
theorem B3745921 : Blo 1168401 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B1755401 : Blo 1168401 1755401 := bstep (se 2 (by rfl) ⟨658275, by rfl⟩ : syracuseStep 1755401 = 1316551) B1316551
theorem B5925149 : Blo 1168401 5925149 := bstep (se 3 (by rfl) ⟨1110965, by rfl⟩ : syracuseStep 5925149 = 2221931) B2221931
theorem B21342523 : Blo 1168401 21342523 := bstep (se 1 (by rfl) ⟨16006892, by rfl⟩ : syracuseStep 21342523 = 32013785) B32013785
theorem B22473065 : Blo 1168401 22473065 := bstep (se 2 (by rfl) ⟨8427399, by rfl⟩ : syracuseStep 22473065 = 16854799) B16854799
theorem B1755503 : Blo 1168401 1755503 := bstep (se 1 (by rfl) ⟨1316627, by rfl⟩ : syracuseStep 1755503 = 2633255) B2633255
theorem B2632103 : Blo 1168401 2632103 := bstep (se 1 (by rfl) ⟨1974077, by rfl⟩ : syracuseStep 2632103 = 3948155) B3948155
theorem B6080941 : Blo 1168401 6080941 := bstep (se 3 (by rfl) ⟨1140176, by rfl⟩ : syracuseStep 6080941 = 2280353) B2280353
theorem B2959841 : Blo 1168401 2959841 := bstep (se 2 (by rfl) ⟨1109940, by rfl⟩ : syracuseStep 2959841 = 2219881) B2219881
theorem B7113203 : Blo 1168401 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B2632211 : Blo 1168401 2632211 := bstep (se 1 (by rfl) ⟨1974158, by rfl⟩ : syracuseStep 2632211 = 3948317) B3948317
theorem B2632265 : Blo 1168401 2632265 := bstep (se 2 (by rfl) ⟨987099, by rfl⟩ : syracuseStep 2632265 = 1974199) B1974199
theorem B5917373 : Blo 1168401 5917373 := bstep (se 3 (by rfl) ⟨1109507, by rfl⟩ : syracuseStep 5917373 = 2219015) B2219015
theorem B2960347 : Blo 1168401 2960347 := bstep (se 1 (by rfl) ⟨2220260, by rfl⟩ : syracuseStep 2960347 = 4440521) B4440521
theorem B2632679 : Blo 1168401 2632679 := bstep (se 1 (by rfl) ⟨1974509, by rfl⟩ : syracuseStep 2632679 = 3949019) B3949019
theorem B9006157 : Blo 1168401 9006157 := bstep (se 3 (by rfl) ⟨1688654, by rfl⟩ : syracuseStep 9006157 = 3377309) B3377309
theorem B12651659 : Blo 1168401 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B3206287 : Blo 1168401 3206287 := bstep (se 1 (by rfl) ⟨2404715, by rfl⟩ : syracuseStep 3206287 = 4809431) B4809431
theorem B2886943 : Blo 1168401 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B2960671 : Blo 1168401 2960671 := bstep (se 1 (by rfl) ⟨2220503, by rfl⟩ : syracuseStep 2960671 = 4441007) B4441007
theorem B2370913 : Blo 1168401 2370913 := bstep (se 2 (by rfl) ⟨889092, by rfl⟩ : syracuseStep 2370913 = 1778185) B1778185
theorem B2633057 : Blo 1168401 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B2633147 : Blo 1168401 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B2633273 : Blo 1168401 2633273 := bstep (se 2 (by rfl) ⟨987477, by rfl⟩ : syracuseStep 2633273 = 1974955) B1974955
theorem B1601095 : Blo 1168401 1601095 := bstep (se 1 (by rfl) ⟨1200821, by rfl⟩ : syracuseStep 1601095 = 2401643) B2401643
theorem B3944051 : Blo 1168401 3944051 := bstep (se 1 (by rfl) ⟨2958038, by rfl⟩ : syracuseStep 3944051 = 5916077) B5916077
theorem B40529645 : Blo 1168401 40529645 := bstep (se 3 (by rfl) ⟨7599308, by rfl⟩ : syracuseStep 40529645 = 15198617) B15198617
theorem B1314607 : Blo 1168401 1314607 := bstep (se 1 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 1314607 = 1971911) B1971911
theorem B3944321 : Blo 1168401 3944321 := bstep (se 2 (by rfl) ⟨1479120, by rfl⟩ : syracuseStep 3944321 = 2958241) B2958241
theorem B1314715 : Blo 1168401 1314715 := bstep (se 1 (by rfl) ⟨986036, by rfl⟩ : syracuseStep 1314715 = 1972073) B1972073
theorem B11243609 : Blo 1168401 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B8876303 : Blo 1168401 8876303 := bstep (se 1 (by rfl) ⟨6657227, by rfl⟩ : syracuseStep 8876303 = 13314455) B13314455
theorem B1315111 : Blo 1168401 1315111 := bstep (se 1 (by rfl) ⟨986333, by rfl⟩ : syracuseStep 1315111 = 1972667) B1972667
theorem B4436315 : Blo 1168401 4436315 := bstep (se 1 (by rfl) ⟨3327236, by rfl⟩ : syracuseStep 4436315 = 6654473) B6654473
theorem B2961755 : Blo 1168401 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B22466915 : Blo 1168401 22466915 := bstep (se 1 (by rfl) ⟨16850186, by rfl⟩ : syracuseStep 22466915 = 33700373) B33700373
theorem B6656363 : Blo 1168401 6656363 := bstep (se 1 (by rfl) ⟨4992272, by rfl⟩ : syracuseStep 6656363 = 9984545) B9984545
theorem B1315183 : Blo 1168401 1315183 := bstep (se 1 (by rfl) ⟨986387, by rfl⟩ : syracuseStep 1315183 = 1972775) B1972775
theorem B1405307 : Blo 1168401 1405307 := bstep (se 1 (by rfl) ⟨1053980, by rfl⟩ : syracuseStep 1405307 = 2107961) B2107961
theorem B8425903 : Blo 1168401 8425903 := bstep (se 1 (by rfl) ⟨6319427, by rfl⟩ : syracuseStep 8425903 = 12638855) B12638855
theorem B1315399 : Blo 1168401 1315399 := bstep (se 1 (by rfl) ⟨986549, by rfl⟩ : syracuseStep 1315399 = 1973099) B1973099
theorem B9982561 : Blo 1168401 9982561 := bstep (se 2 (by rfl) ⟨3743460, by rfl⟩ : syracuseStep 9982561 = 7486921) B7486921
theorem B4436633 : Blo 1168401 4436633 := bstep (se 2 (by rfl) ⟨1663737, by rfl⟩ : syracuseStep 4436633 = 3327475) B3327475
theorem B3945131 : Blo 1168401 3945131 := bstep (se 1 (by rfl) ⟨2958848, by rfl⟩ : syracuseStep 3945131 = 5917697) B5917697
theorem B2847403 : Blo 1168401 2847403 := bstep (se 1 (by rfl) ⟨2135552, by rfl⟩ : syracuseStep 2847403 = 4271105) B4271105
theorem B1405615 : Blo 1168401 1405615 := bstep (se 1 (by rfl) ⟨1054211, by rfl⟩ : syracuseStep 1405615 = 2108423) B2108423
theorem B4436815 : Blo 1168401 4436815 := bstep (se 1 (by rfl) ⟨3327611, by rfl⟩ : syracuseStep 4436815 = 6655223) B6655223
theorem B19993553 : Blo 1168401 19993553 := bstep (se 2 (by rfl) ⟨7497582, by rfl⟩ : syracuseStep 19993553 = 14995165) B14995165
theorem B4437089 : Blo 1168401 4437089 := bstep (se 2 (by rfl) ⟨1663908, by rfl⟩ : syracuseStep 4437089 = 3327817) B3327817
theorem B4740221 : Blo 1168401 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B3945671 : Blo 1168401 3945671 := bstep (se 1 (by rfl) ⟨2959253, by rfl⟩ : syracuseStep 3945671 = 5918507) B5918507
theorem B1873115 : Blo 1168401 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B1168671 : Blo 1168401 1168671 := bstep (se 1 (by rfl) ⟨876503, by rfl⟩ : syracuseStep 1168671 = 1753007) B1753007
theorem B4437287 : Blo 1168401 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B1168731 : Blo 1168401 1168731 := bstep (se 1 (by rfl) ⟨876548, by rfl⟩ : syracuseStep 1168731 = 1753097) B1753097
theorem B1480027 : Blo 1168401 1480027 := bstep (se 1 (by rfl) ⟨1110020, by rfl⟩ : syracuseStep 1480027 = 2220041) B2220041
theorem B1168751 : Blo 1168401 1168751 := bstep (se 1 (by rfl) ⟨876563, by rfl⟩ : syracuseStep 1168751 = 1753127) B1753127
theorem B6665611 : Blo 1168401 6665611 := bstep (se 1 (by rfl) ⟨4999208, by rfl⟩ : syracuseStep 6665611 = 9998417) B9998417
theorem B1168807 : Blo 1168401 1168807 := bstep (se 1 (by rfl) ⟨876605, by rfl⟩ : syracuseStep 1168807 = 1753211) B1753211
theorem B1316263 : Blo 1168401 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B12006893 : Blo 1168401 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B1168891 : Blo 1168401 1168891 := bstep (se 1 (by rfl) ⟨876668, by rfl⟩ : syracuseStep 1168891 = 1753337) B1753337
theorem B5920289 : Blo 1168401 5920289 := bstep (se 2 (by rfl) ⟨2220108, by rfl⟩ : syracuseStep 5920289 = 4440217) B4440217
theorem B1168959 : Blo 1168401 1168959 := bstep (se 1 (by rfl) ⟨876719, by rfl⟩ : syracuseStep 1168959 = 1753439) B1753439
theorem B1168967 : Blo 1168401 1168967 := bstep (se 1 (by rfl) ⟨876725, by rfl⟩ : syracuseStep 1168967 = 1753451) B1753451
theorem B8107705 : Blo 1168401 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B2496187 : Blo 1168401 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B1169119 : Blo 1168401 1169119 := bstep (se 1 (by rfl) ⟨876839, by rfl⟩ : syracuseStep 1169119 = 1753679) B1753679
theorem B6657821 : Blo 1168401 6657821 := bstep (se 3 (by rfl) ⟨1248341, by rfl⟩ : syracuseStep 6657821 = 2496683) B2496683
theorem B1169199 : Blo 1168401 1169199 := bstep (se 1 (by rfl) ⟨876899, by rfl⟩ : syracuseStep 1169199 = 1753799) B1753799
theorem B1169307 : Blo 1168401 1169307 := bstep (se 1 (by rfl) ⟨876980, by rfl⟩ : syracuseStep 1169307 = 1753961) B1753961
theorem B1169359 : Blo 1168401 1169359 := bstep (se 1 (by rfl) ⟨877019, by rfl⟩ : syracuseStep 1169359 = 1754039) B1754039
theorem B1169383 : Blo 1168401 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B2496521 : Blo 1168401 2496521 := bstep (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) B1872391
theorem B6412553 : Blo 1168401 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B1169695 : Blo 1168401 1169695 := bstep (se 1 (by rfl) ⟨877271, by rfl⟩ : syracuseStep 1169695 = 1754543) B1754543
theorem B1480999 : Blo 1168401 1480999 := bstep (se 1 (by rfl) ⟨1110749, by rfl⟩ : syracuseStep 1480999 = 2221499) B2221499
theorem B1169755 : Blo 1168401 1169755 := bstep (se 1 (by rfl) ⟨877316, by rfl⟩ : syracuseStep 1169755 = 1754633) B1754633
theorem B121534825 : Blo 1168401 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B1169775 : Blo 1168401 1169775 := bstep (se 1 (by rfl) ⟨877331, by rfl⟩ : syracuseStep 1169775 = 1754663) B1754663
theorem B1169831 : Blo 1168401 1169831 := bstep (se 1 (by rfl) ⟨877373, by rfl⟩ : syracuseStep 1169831 = 1754747) B1754747
theorem B1169915 : Blo 1168401 1169915 := bstep (se 1 (by rfl) ⟨877436, by rfl⟩ : syracuseStep 1169915 = 1754873) B1754873
theorem B1169983 : Blo 1168401 1169983 := bstep (se 1 (by rfl) ⟨877487, by rfl⟩ : syracuseStep 1169983 = 1754975) B1754975
theorem B1169991 : Blo 1168401 1169991 := bstep (se 1 (by rfl) ⟨877493, by rfl⟩ : syracuseStep 1169991 = 1754987) B1754987
theorem B3947183 : Blo 1168401 3947183 := bstep (se 1 (by rfl) ⟨2960387, by rfl⟩ : syracuseStep 3947183 = 5920775) B5920775
theorem B2497247 : Blo 1168401 2497247 := bstep (se 1 (by rfl) ⟨1872935, by rfl⟩ : syracuseStep 2497247 = 3745871) B3745871
theorem B1170143 : Blo 1168401 1170143 := bstep (se 1 (by rfl) ⟨877607, by rfl⟩ : syracuseStep 1170143 = 1755215) B1755215
theorem B1170223 : Blo 1168401 1170223 := bstep (se 1 (by rfl) ⟨877667, by rfl⟩ : syracuseStep 1170223 = 1755335) B1755335
theorem B9001847 : Blo 1168401 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B1170331 : Blo 1168401 1170331 := bstep (se 1 (by rfl) ⟨877748, by rfl⟩ : syracuseStep 1170331 = 1755497) B1755497
theorem B1170383 : Blo 1168401 1170383 := bstep (se 1 (by rfl) ⟨877787, by rfl⟩ : syracuseStep 1170383 = 1755575) B1755575
theorem B3947507 : Blo 1168401 3947507 := bstep (se 1 (by rfl) ⟨2960630, by rfl⟩ : syracuseStep 3947507 = 5921261) B5921261
theorem B13327577 : Blo 1168401 13327577 := bstep (se 2 (by rfl) ⟨4997841, by rfl⟩ : syracuseStep 13327577 = 9995683) B9995683
theorem B2629025 : Blo 1168401 2629025 := bstep (se 2 (by rfl) ⟨985884, by rfl⟩ : syracuseStep 2629025 = 1971769) B1971769
theorem B3161531 : Blo 1168401 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B3948047 : Blo 1168401 3948047 := bstep (se 1 (by rfl) ⟨2961035, by rfl⟩ : syracuseStep 3948047 = 5922071) B5922071
theorem B1752671 : Blo 1168401 1752671 := bstep (se 1 (by rfl) ⟨1314503, by rfl⟩ : syracuseStep 1752671 = 2629007) B2629007
theorem B1973855 : Blo 1168401 1973855 := bstep (se 1 (by rfl) ⟨1480391, by rfl⟩ : syracuseStep 1973855 = 2960783) B2960783
theorem B3743347 : Blo 1168401 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1752887 : Blo 1168401 1752887 := bstep (se 1 (by rfl) ⟨1314665, by rfl⟩ : syracuseStep 1752887 = 2629331) B2629331
theorem B1974071 : Blo 1168401 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B9994043 : Blo 1168401 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B2629583 : Blo 1168401 2629583 := bstep (se 1 (by rfl) ⟨1972187, by rfl⟩ : syracuseStep 2629583 = 3944375) B3944375
theorem B7495739 : Blo 1168401 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B4440203 : Blo 1168401 4440203 := bstep (se 1 (by rfl) ⟨3330152, by rfl⟩ : syracuseStep 4440203 = 6660305) B6660305
theorem B1753307 : Blo 1168401 1753307 := bstep (se 1 (by rfl) ⟨1314980, by rfl⟩ : syracuseStep 1753307 = 2629961) B2629961
theorem B2957543 : Blo 1168401 2957543 := bstep (se 1 (by rfl) ⟨2218157, by rfl⟩ : syracuseStep 2957543 = 4436315) B4436315
theorem B1753319 : Blo 1168401 1753319 := bstep (se 1 (by rfl) ⟨1314989, by rfl⟩ : syracuseStep 1753319 = 2629979) B2629979
theorem B1974503 : Blo 1168401 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B1753481 : Blo 1168401 1753481 := bstep (se 2 (by rfl) ⟨657555, by rfl⟩ : syracuseStep 1753481 = 1315111) B1315111
theorem B1974665 : Blo 1168401 1974665 := bstep (se 2 (by rfl) ⟨740499, by rfl⟩ : syracuseStep 1974665 = 1480999) B1480999
theorem B6750647 : Blo 1168401 6750647 := bstep (se 1 (by rfl) ⟨5062985, by rfl⟩ : syracuseStep 6750647 = 10125971) B10125971
theorem B2957755 : Blo 1168401 2957755 := bstep (se 1 (by rfl) ⟨2218316, by rfl⟩ : syracuseStep 2957755 = 4436633) B4436633
theorem B2630087 : Blo 1168401 2630087 := bstep (se 1 (by rfl) ⟨1972565, by rfl⟩ : syracuseStep 2630087 = 3945131) B3945131
theorem B162046433 : Blo 1168401 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B1753577 : Blo 1168401 1753577 := bstep (se 2 (by rfl) ⟨657591, by rfl⟩ : syracuseStep 1753577 = 1315183) B1315183
theorem B31998563 : Blo 1168401 31998563 := bstep (se 1 (by rfl) ⟨23998922, by rfl⟩ : syracuseStep 31998563 = 47997845) B47997845
theorem B1753703 : Blo 1168401 1753703 := bstep (se 1 (by rfl) ⟨1315277, by rfl⟩ : syracuseStep 1753703 = 2630555) B2630555
theorem B13329035 : Blo 1168401 13329035 := bstep (se 1 (by rfl) ⟨9996776, by rfl⟩ : syracuseStep 13329035 = 19993553) B19993553
theorem B2958059 : Blo 1168401 2958059 := bstep (se 1 (by rfl) ⟨2218544, by rfl⟩ : syracuseStep 2958059 = 4437089) B4437089
theorem B1753835 : Blo 1168401 1753835 := bstep (se 1 (by rfl) ⟨1315376, by rfl⟩ : syracuseStep 1753835 = 2630753) B2630753
theorem B1753865 : Blo 1168401 1753865 := bstep (se 2 (by rfl) ⟨657699, by rfl⟩ : syracuseStep 1753865 = 1315399) B1315399
theorem B2630447 : Blo 1168401 2630447 := bstep (se 1 (by rfl) ⟨1972835, by rfl⟩ : syracuseStep 2630447 = 3945671) B3945671
theorem B2958191 : Blo 1168401 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B1753967 : Blo 1168401 1753967 := bstep (se 1 (by rfl) ⟨1315475, by rfl⟩ : syracuseStep 1753967 = 2630951) B2630951
theorem B12649403 : Blo 1168401 12649403 := bstep (se 1 (by rfl) ⟨9487052, by rfl⟩ : syracuseStep 12649403 = 18974105) B18974105
theorem B13312997 : Blo 1168401 13312997 := bstep (se 4 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 13312997 = 2496187) B2496187
theorem B8004595 : Blo 1168401 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B5915753 : Blo 1168401 5915753 := bstep (se 2 (by rfl) ⟨2218407, by rfl⟩ : syracuseStep 5915753 = 4436815) B4436815
theorem B1754219 : Blo 1168401 1754219 := bstep (se 1 (by rfl) ⟨1315664, by rfl⟩ : syracuseStep 1754219 = 2631329) B2631329
theorem B8430749 : Blo 1168401 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B3949775 : Blo 1168401 3949775 := bstep (se 1 (by rfl) ⟨2962331, by rfl⟩ : syracuseStep 3949775 = 5924663) B5924663
theorem B5915915 : Blo 1168401 5915915 := bstep (se 1 (by rfl) ⟨4436936, by rfl⟩ : syracuseStep 5915915 = 8873873) B8873873
theorem B1754459 : Blo 1168401 1754459 := bstep (se 1 (by rfl) ⟨1315844, by rfl⟩ : syracuseStep 1754459 = 2631689) B2631689
theorem B3950099 : Blo 1168401 3950099 := bstep (se 1 (by rfl) ⟨2962574, by rfl⟩ : syracuseStep 3950099 = 5925149) B5925149
theorem B1754735 : Blo 1168401 1754735 := bstep (se 1 (by rfl) ⟨1316051, by rfl⟩ : syracuseStep 1754735 = 2632103) B2632103
theorem B1754807 : Blo 1168401 1754807 := bstep (se 1 (by rfl) ⟨1316105, by rfl⟩ : syracuseStep 1754807 = 2632211) B2632211
theorem B1754843 : Blo 1168401 1754843 := bstep (se 1 (by rfl) ⟨1316132, by rfl⟩ : syracuseStep 1754843 = 2632265) B2632265
theorem B2631455 : Blo 1168401 2631455 := bstep (se 1 (by rfl) ⟨1973591, by rfl⟩ : syracuseStep 2631455 = 3947183) B3947183
theorem B1664831 : Blo 1168401 1664831 := bstep (se 1 (by rfl) ⟨1248623, by rfl⟩ : syracuseStep 1664831 = 2497247) B2497247
theorem B1755017 : Blo 1168401 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B1755119 : Blo 1168401 1755119 := bstep (se 1 (by rfl) ⟨1316339, by rfl⟩ : syracuseStep 1755119 = 2632679) B2632679
theorem B2631671 : Blo 1168401 2631671 := bstep (se 1 (by rfl) ⟨1973753, by rfl⟩ : syracuseStep 2631671 = 3947507) B3947507
theorem B4991129 : Blo 1168401 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B1755371 : Blo 1168401 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B1755431 : Blo 1168401 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B2632031 : Blo 1168401 2632031 := bstep (se 1 (by rfl) ⟨1974023, by rfl⟩ : syracuseStep 2632031 = 3948047) B3948047
theorem B1755515 : Blo 1168401 1755515 := bstep (se 1 (by rfl) ⟨1316636, by rfl⟩ : syracuseStep 1755515 = 2633273) B2633273
theorem B27019763 : Blo 1168401 27019763 := bstep (se 1 (by rfl) ⟨20264822, by rfl⟩ : syracuseStep 27019763 = 40529645) B40529645
theorem B6662695 : Blo 1168401 6662695 := bstep (se 1 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 6662695 = 9994043) B9994043
theorem B9988919 : Blo 1168401 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B5917535 : Blo 1168401 5917535 := bstep (se 1 (by rfl) ⟨4438151, by rfl⟩ : syracuseStep 5917535 = 8876303) B8876303
theorem B14977943 : Blo 1168401 14977943 := bstep (se 1 (by rfl) ⟨11233457, by rfl⟩ : syracuseStep 14977943 = 22466915) B22466915
theorem B3943403 : Blo 1168401 3943403 := bstep (se 1 (by rfl) ⟨2957552, by rfl⟩ : syracuseStep 3943403 = 5915105) B5915105
theorem B3943457 : Blo 1168401 3943457 := bstep (se 2 (by rfl) ⟨1478796, by rfl⟩ : syracuseStep 3943457 = 2957593) B2957593
theorem B2632751 : Blo 1168401 2632751 := bstep (se 1 (by rfl) ⟨1974563, by rfl⟩ : syracuseStep 2632751 = 3949127) B3949127
theorem B11234537 : Blo 1168401 11234537 := bstep (se 2 (by rfl) ⟨4212951, by rfl⟩ : syracuseStep 11234537 = 8425903) B8425903
theorem B13495567 : Blo 1168401 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B3747151 : Blo 1168401 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B2633039 : Blo 1168401 2633039 := bstep (se 1 (by rfl) ⟨1974779, by rfl⟩ : syracuseStep 2633039 = 3949559) B3949559
theorem B17100197 : Blo 1168401 17100197 := bstep (se 4 (by rfl) ⟨1603143, by rfl⟩ : syracuseStep 17100197 = 3206287) B3206287
theorem B2633129 : Blo 1168401 2633129 := bstep (se 2 (by rfl) ⟨987423, by rfl⟩ : syracuseStep 2633129 = 1974847) B1974847
theorem B1248743 : Blo 1168401 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B43232777 : Blo 1168401 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B3747485 : Blo 1168401 3747485 := bstep (se 3 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 3747485 = 1405307) B1405307
theorem B3944915 : Blo 1168401 3944915 := bstep (se 1 (by rfl) ⟨2958686, by rfl⟩ : syracuseStep 3944915 = 5917373) B5917373
theorem B12644869 : Blo 1168401 12644869 := bstep (se 4 (by rfl) ⟨1185456, by rfl⟩ : syracuseStep 12644869 = 2370913) B2370913
theorem B6001231 : Blo 1168401 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B8434439 : Blo 1168401 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B2134793 : Blo 1168401 2134793 := bstep (se 2 (by rfl) ⟨800547, by rfl⟩ : syracuseStep 2134793 = 1601095) B1601095
theorem B2667305 : Blo 1168401 2667305 := bstep (se 2 (by rfl) ⟨1000239, by rfl⟩ : syracuseStep 2667305 = 2000479) B2000479
theorem B8885051 : Blo 1168401 8885051 := bstep (se 1 (by rfl) ⟨6663788, by rfl⟩ : syracuseStep 8885051 = 13327577) B13327577
theorem B10810273 : Blo 1168401 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B50541569 : Blo 1168401 50541569 := bstep (se 2 (by rfl) ⟨18953088, by rfl⟩ : syracuseStep 50541569 = 37906177) B37906177
theorem B1168447 : Blo 1168401 1168447 := bstep (se 1 (by rfl) ⟨876335, by rfl⟩ : syracuseStep 1168447 = 1752671) B1752671
theorem B1315903 : Blo 1168401 1315903 := bstep (se 1 (by rfl) ⟨986927, by rfl⟩ : syracuseStep 1315903 = 1973855) B1973855
theorem B1168591 : Blo 1168401 1168591 := bstep (se 1 (by rfl) ⟨876443, by rfl⟩ : syracuseStep 1168591 = 1752887) B1752887
theorem B1316047 : Blo 1168401 1316047 := bstep (se 1 (by rfl) ⟨987035, by rfl⟩ : syracuseStep 1316047 = 1974071) B1974071
theorem B1873243 : Blo 1168401 1873243 := bstep (se 1 (by rfl) ⟨1404932, by rfl⟩ : syracuseStep 1873243 = 2809865) B2809865
theorem B6657389 : Blo 1168401 6657389 := bstep (se 3 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 6657389 = 2496521) B2496521
theorem B1168795 : Blo 1168401 1168795 := bstep (se 1 (by rfl) ⟨876596, by rfl⟩ : syracuseStep 1168795 = 1753193) B1753193
theorem B4994561 : Blo 1168401 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B4437575 : Blo 1168401 4437575 := bstep (se 1 (by rfl) ⟨3328181, by rfl⟩ : syracuseStep 4437575 = 6656363) B6656363
theorem B1971823 : Blo 1168401 1971823 := bstep (se 1 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 1971823 = 2957735) B2957735
theorem B1169007 : Blo 1168401 1169007 := bstep (se 1 (by rfl) ⟨876755, by rfl⟩ : syracuseStep 1169007 = 1753511) B1753511
theorem B1169063 : Blo 1168401 1169063 := bstep (se 1 (by rfl) ⟨876797, by rfl⟩ : syracuseStep 1169063 = 1753595) B1753595
theorem B1971931 : Blo 1168401 1971931 := bstep (se 1 (by rfl) ⟨1478948, by rfl⟩ : syracuseStep 1971931 = 2957897) B2957897
theorem B28456697 : Blo 1168401 28456697 := bstep (se 2 (by rfl) ⟨10671261, by rfl⟩ : syracuseStep 28456697 = 21342523) B21342523
theorem B1169147 : Blo 1168401 1169147 := bstep (se 1 (by rfl) ⟨876860, by rfl⟩ : syracuseStep 1169147 = 1753721) B1753721
theorem B1169183 : Blo 1168401 1169183 := bstep (se 1 (by rfl) ⟨876887, by rfl⟩ : syracuseStep 1169183 = 1753775) B1753775
theorem B1169215 : Blo 1168401 1169215 := bstep (se 1 (by rfl) ⟨876911, by rfl⟩ : syracuseStep 1169215 = 1753823) B1753823
theorem B8107921 : Blo 1168401 8107921 := bstep (se 2 (by rfl) ⟨3040470, by rfl⟩ : syracuseStep 8107921 = 6080941) B6080941
theorem B7116751 : Blo 1168401 7116751 := bstep (se 1 (by rfl) ⟨5337563, by rfl⟩ : syracuseStep 7116751 = 10675127) B10675127
theorem B1169391 : Blo 1168401 1169391 := bstep (se 1 (by rfl) ⟨877043, by rfl⟩ : syracuseStep 1169391 = 1754087) B1754087
theorem B3160147 : Blo 1168401 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B2807903 : Blo 1168401 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B3332191 : Blo 1168401 3332191 := bstep (se 1 (by rfl) ⟨2499143, by rfl⟩ : syracuseStep 3332191 = 4998287) B4998287
theorem B13310081 : Blo 1168401 13310081 := bstep (se 2 (by rfl) ⟨4991280, by rfl⟩ : syracuseStep 13310081 = 9982561) B9982561
theorem B1874063 : Blo 1168401 1874063 := bstep (se 1 (by rfl) ⟨1405547, by rfl⟩ : syracuseStep 1874063 = 2811095) B2811095
theorem B1169563 : Blo 1168401 1169563 := bstep (se 1 (by rfl) ⟨877172, by rfl⟩ : syracuseStep 1169563 = 1754345) B1754345
theorem B1169599 : Blo 1168401 1169599 := bstep (se 1 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 1169599 = 1754399) B1754399
theorem B15186149 : Blo 1168401 15186149 := bstep (se 4 (by rfl) ⟨1423701, by rfl⟩ : syracuseStep 15186149 = 2847403) B2847403
theorem B1874153 : Blo 1168401 1874153 := bstep (se 2 (by rfl) ⟨702807, by rfl⟩ : syracuseStep 1874153 = 1405615) B1405615
theorem B1169711 : Blo 1168401 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B3946859 : Blo 1168401 3946859 := bstep (se 1 (by rfl) ⟨2960144, by rfl⟩ : syracuseStep 3946859 = 5920289) B5920289
theorem B4438547 : Blo 1168401 4438547 := bstep (se 1 (by rfl) ⟨3328910, by rfl⟩ : syracuseStep 4438547 = 6657821) B6657821
theorem B1169947 : Blo 1168401 1169947 := bstep (se 1 (by rfl) ⟨877460, by rfl⟩ : syracuseStep 1169947 = 1754921) B1754921
theorem B1169951 : Blo 1168401 1169951 := bstep (se 1 (by rfl) ⟨877463, by rfl⟩ : syracuseStep 1169951 = 1754927) B1754927
theorem B3947129 : Blo 1168401 3947129 := bstep (se 2 (by rfl) ⟨1480173, by rfl⟩ : syracuseStep 3947129 = 2960347) B2960347
theorem B7494281 : Blo 1168401 7494281 := bstep (se 2 (by rfl) ⟨2810355, by rfl⟩ : syracuseStep 7494281 = 5620711) B5620711
theorem B12008209 : Blo 1168401 12008209 := bstep (se 2 (by rfl) ⟨4503078, by rfl⟩ : syracuseStep 12008209 = 9006157) B9006157
theorem B4275035 : Blo 1168401 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B1170267 : Blo 1168401 1170267 := bstep (se 1 (by rfl) ⟨877700, by rfl⟩ : syracuseStep 1170267 = 1755401) B1755401
theorem B14982043 : Blo 1168401 14982043 := bstep (se 1 (by rfl) ⟨11236532, by rfl⟩ : syracuseStep 14982043 = 22473065) B22473065
theorem B1170335 : Blo 1168401 1170335 := bstep (se 1 (by rfl) ⟨877751, by rfl⟩ : syracuseStep 1170335 = 1755503) B1755503
theorem B1973227 : Blo 1168401 1973227 := bstep (se 1 (by rfl) ⟨1479920, by rfl⟩ : syracuseStep 1973227 = 2959841) B2959841
theorem B4742135 : Blo 1168401 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B3849257 : Blo 1168401 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B3947561 : Blo 1168401 3947561 := bstep (se 2 (by rfl) ⟨1480335, by rfl⟩ : syracuseStep 3947561 = 2960671) B2960671
theorem B7494713 : Blo 1168401 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B1973369 : Blo 1168401 1973369 := bstep (se 2 (by rfl) ⟨740013, by rfl⟩ : syracuseStep 1973369 = 1480027) B1480027
theorem B8887481 : Blo 1168401 8887481 := bstep (se 2 (by rfl) ⟨3332805, by rfl⟩ : syracuseStep 8887481 = 6665611) B6665611
theorem B1752683 : Blo 1168401 1752683 := bstep (se 1 (by rfl) ⟨1314512, by rfl⟩ : syracuseStep 1752683 = 2629025) B2629025
theorem B1752809 : Blo 1168401 1752809 := bstep (se 2 (by rfl) ⟨657303, by rfl⟩ : syracuseStep 1752809 = 1314607) B1314607
theorem B2629367 : Blo 1168401 2629367 := bstep (se 1 (by rfl) ⟨1972025, by rfl⟩ : syracuseStep 2629367 = 3944051) B3944051
theorem B1752953 : Blo 1168401 1752953 := bstep (se 2 (by rfl) ⟨657357, by rfl⟩ : syracuseStep 1752953 = 1314715) B1314715
theorem B2629547 : Blo 1168401 2629547 := bstep (se 1 (by rfl) ⟨1972160, by rfl⟩ : syracuseStep 2629547 = 3944321) B3944321
theorem B1753055 : Blo 1168401 1753055 := bstep (se 1 (by rfl) ⟨1314791, by rfl⟩ : syracuseStep 1753055 = 2629583) B2629583
theorem B4997159 : Blo 1168401 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B7487741 : Blo 1168401 7487741 := bstep (se 3 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 7487741 = 2807903) B2807903
theorem B1753391 : Blo 1168401 1753391 := bstep (se 1 (by rfl) ⟨1315043, by rfl⟩ : syracuseStep 1753391 = 2630087) B2630087
theorem B2629943 : Blo 1168401 2629943 := bstep (se 1 (by rfl) ⟨1972457, by rfl⟩ : syracuseStep 2629943 = 3944915) B3944915
theorem B4997501 : Blo 1168401 4997501 := bstep (se 3 (by rfl) ⟨937031, by rfl⟩ : syracuseStep 4997501 = 1874063) B1874063
theorem B21332375 : Blo 1168401 21332375 := bstep (se 1 (by rfl) ⟨15999281, by rfl⟩ : syracuseStep 21332375 = 31998563) B31998563
theorem B1778203 : Blo 1168401 1778203 := bstep (se 1 (by rfl) ⟨1333652, by rfl⟩ : syracuseStep 1778203 = 2667305) B2667305
theorem B1753631 : Blo 1168401 1753631 := bstep (se 1 (by rfl) ⟨1315223, by rfl⟩ : syracuseStep 1753631 = 2630447) B2630447
theorem B5923367 : Blo 1168401 5923367 := bstep (se 1 (by rfl) ⟨4442525, by rfl⟩ : syracuseStep 5923367 = 8885051) B8885051
theorem B33694379 : Blo 1168401 33694379 := bstep (se 1 (by rfl) ⟨25270784, by rfl⟩ : syracuseStep 33694379 = 50541569) B50541569
theorem B16859825 : Blo 1168401 16859825 := bstep (se 2 (by rfl) ⟨6322434, by rfl⟩ : syracuseStep 16859825 = 12644869) B12644869
theorem B5620499 : Blo 1168401 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B2958383 : Blo 1168401 2958383 := bstep (se 1 (by rfl) ⟨2218787, by rfl⟩ : syracuseStep 2958383 = 4437575) B4437575
theorem B1754303 : Blo 1168401 1754303 := bstep (se 1 (by rfl) ⟨1315727, by rfl⟩ : syracuseStep 1754303 = 2631455) B2631455
theorem B2630969 : Blo 1168401 2630969 := bstep (se 2 (by rfl) ⟨986613, by rfl⟩ : syracuseStep 2630969 = 1973227) B1973227
theorem B1754447 : Blo 1168401 1754447 := bstep (se 1 (by rfl) ⟨1315835, by rfl⟩ : syracuseStep 1754447 = 2631671) B2631671
theorem B1754537 : Blo 1168401 1754537 := bstep (se 2 (by rfl) ⟨657951, by rfl⟩ : syracuseStep 1754537 = 1315903) B1315903
theorem B8873387 : Blo 1168401 8873387 := bstep (se 1 (by rfl) ⟨6655040, by rfl⟩ : syracuseStep 8873387 = 13310081) B13310081
theorem B3327419 : Blo 1168401 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B1754687 : Blo 1168401 1754687 := bstep (se 1 (by rfl) ⟨1316015, by rfl⟩ : syracuseStep 1754687 = 2632031) B2632031
theorem B2631239 : Blo 1168401 2631239 := bstep (se 1 (by rfl) ⟨1973429, by rfl⟩ : syracuseStep 2631239 = 3946859) B3946859
theorem B1754729 : Blo 1168401 1754729 := bstep (se 2 (by rfl) ⟨658023, by rfl⟩ : syracuseStep 1754729 = 1316047) B1316047
theorem B2959031 : Blo 1168401 2959031 := bstep (se 1 (by rfl) ⟨2219273, by rfl⟩ : syracuseStep 2959031 = 4438547) B4438547
theorem B2631419 : Blo 1168401 2631419 := bstep (se 1 (by rfl) ⟨1973564, by rfl⟩ : syracuseStep 2631419 = 3947129) B3947129
theorem B2566171 : Blo 1168401 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B2631707 : Blo 1168401 2631707 := bstep (se 1 (by rfl) ⟨1973780, by rfl⟩ : syracuseStep 2631707 = 3947561) B3947561
theorem B1755167 : Blo 1168401 1755167 := bstep (se 1 (by rfl) ⟨1316375, by rfl⟩ : syracuseStep 1755167 = 2632751) B2632751
theorem B5924987 : Blo 1168401 5924987 := bstep (se 1 (by rfl) ⟨4443740, by rfl⟩ : syracuseStep 5924987 = 8887481) B8887481
theorem B7489691 : Blo 1168401 7489691 := bstep (se 1 (by rfl) ⟨5617268, by rfl⟩ : syracuseStep 7489691 = 11234537) B11234537
theorem B1755359 : Blo 1168401 1755359 := bstep (se 1 (by rfl) ⟨1316519, by rfl⟩ : syracuseStep 1755359 = 2633039) B2633039
theorem B1755419 : Blo 1168401 1755419 := bstep (se 1 (by rfl) ⟨1316564, by rfl⟩ : syracuseStep 1755419 = 2633129) B2633129
theorem B28821851 : Blo 1168401 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B9489001 : Blo 1168401 9489001 := bstep (se 2 (by rfl) ⟨3558375, by rfl⟩ : syracuseStep 9489001 = 7116751) B7116751
theorem B2960135 : Blo 1168401 2960135 := bstep (se 1 (by rfl) ⟨2220101, by rfl⟩ : syracuseStep 2960135 = 4440203) B4440203
theorem B4213529 : Blo 1168401 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B4442921 : Blo 1168401 4442921 := bstep (se 2 (by rfl) ⟨1666095, by rfl⟩ : syracuseStep 4442921 = 3332191) B3332191
theorem B4500431 : Blo 1168401 4500431 := bstep (se 1 (by rfl) ⟨3375323, by rfl⟩ : syracuseStep 4500431 = 6750647) B6750647
theorem B108030955 : Blo 1168401 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B5622959 : Blo 1168401 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B3943673 : Blo 1168401 3943673 := bstep (se 2 (by rfl) ⟨1478877, by rfl⟩ : syracuseStep 3943673 = 2957755) B2957755
theorem B8875331 : Blo 1168401 8875331 := bstep (se 1 (by rfl) ⟨6656498, by rfl⟩ : syracuseStep 8875331 = 13312997) B13312997
theorem B8883593 : Blo 1168401 8883593 := bstep (se 2 (by rfl) ⟨3331347, by rfl⟩ : syracuseStep 8883593 = 6662695) B6662695
theorem B3943835 : Blo 1168401 3943835 := bstep (se 1 (by rfl) ⟨2957876, by rfl⟩ : syracuseStep 3943835 = 5915753) B5915753
theorem B2633183 : Blo 1168401 2633183 := bstep (se 1 (by rfl) ⟨1974887, by rfl⟩ : syracuseStep 2633183 = 3949775) B3949775
theorem B3943943 : Blo 1168401 3943943 := bstep (se 1 (by rfl) ⟨2957957, by rfl⟩ : syracuseStep 3943943 = 5915915) B5915915
theorem B2633399 : Blo 1168401 2633399 := bstep (se 1 (by rfl) ⟨1975049, by rfl⟩ : syracuseStep 2633399 = 3950099) B3950099
theorem B16010945 : Blo 1168401 16010945 := bstep (se 2 (by rfl) ⟨6004104, by rfl⟩ : syracuseStep 16010945 = 12008209) B12008209
theorem B19976057 : Blo 1168401 19976057 := bstep (se 2 (by rfl) ⟨7491021, by rfl⟩ : syracuseStep 19976057 = 14982043) B14982043
theorem B14413697 : Blo 1168401 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B3329981 : Blo 1168401 3329981 := bstep (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) B1248743
theorem B1249435 : Blo 1168401 1249435 := bstep (se 1 (by rfl) ⟨937076, by rfl⟩ : syracuseStep 1249435 = 1874153) B1874153
theorem B17994089 : Blo 1168401 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B19984805 : Blo 1168401 19984805 := bstep (se 4 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 19984805 = 3747151) B3747151
theorem B3945023 : Blo 1168401 3945023 := bstep (se 1 (by rfl) ⟨2958767, by rfl⟩ : syracuseStep 3945023 = 5917535) B5917535
theorem B1315579 : Blo 1168401 1315579 := bstep (se 1 (by rfl) ⟨986684, by rfl⟩ : syracuseStep 1315579 = 1973369) B1973369
theorem B43242245 : Blo 1168401 43242245 := bstep (se 4 (by rfl) ⟨4053960, by rfl⟩ : syracuseStep 43242245 = 8107921) B8107921
theorem B11400131 : Blo 1168401 11400131 := bstep (se 1 (by rfl) ⟨8550098, by rfl⟩ : syracuseStep 11400131 = 17100197) B17100197
theorem B1168455 : Blo 1168401 1168455 := bstep (se 1 (by rfl) ⟨876341, by rfl⟩ : syracuseStep 1168455 = 1752683) B1752683
theorem B1168539 : Blo 1168401 1168539 := bstep (se 1 (by rfl) ⟨876404, by rfl⟩ : syracuseStep 1168539 = 1752809) B1752809
theorem B33731741 : Blo 1168401 33731741 := bstep (se 3 (by rfl) ⟨6324701, by rfl⟩ : syracuseStep 33731741 = 12649403) B12649403
theorem B1168635 : Blo 1168401 1168635 := bstep (se 1 (by rfl) ⟨876476, by rfl⟩ : syracuseStep 1168635 = 1752953) B1752953
theorem B1168703 : Blo 1168401 1168703 := bstep (se 1 (by rfl) ⟨876527, by rfl⟩ : syracuseStep 1168703 = 1753055) B1753055
theorem B1168871 : Blo 1168401 1168871 := bstep (se 1 (by rfl) ⟨876653, by rfl⟩ : syracuseStep 1168871 = 1753307) B1753307
theorem B1971695 : Blo 1168401 1971695 := bstep (se 1 (by rfl) ⟨1478771, by rfl⟩ : syracuseStep 1971695 = 2957543) B2957543
theorem B1168879 : Blo 1168401 1168879 := bstep (se 1 (by rfl) ⟨876659, by rfl⟩ : syracuseStep 1168879 = 1753319) B1753319
theorem B1316335 : Blo 1168401 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B1168987 : Blo 1168401 1168987 := bstep (se 1 (by rfl) ⟨876740, by rfl⟩ : syracuseStep 1168987 = 1753481) B1753481
theorem B1316443 : Blo 1168401 1316443 := bstep (se 1 (by rfl) ⟨987332, by rfl⟩ : syracuseStep 1316443 = 1974665) B1974665
theorem B1169051 : Blo 1168401 1169051 := bstep (se 1 (by rfl) ⟨876788, by rfl⟩ : syracuseStep 1169051 = 1753577) B1753577
theorem B1169135 : Blo 1168401 1169135 := bstep (se 1 (by rfl) ⟨876851, by rfl⟩ : syracuseStep 1169135 = 1753703) B1753703
theorem B8886023 : Blo 1168401 8886023 := bstep (se 1 (by rfl) ⟨6664517, by rfl⟩ : syracuseStep 8886023 = 13329035) B13329035
theorem B1972039 : Blo 1168401 1972039 := bstep (se 1 (by rfl) ⟨1479029, by rfl⟩ : syracuseStep 1972039 = 2958059) B2958059
theorem B1169223 : Blo 1168401 1169223 := bstep (se 1 (by rfl) ⟨876917, by rfl⟩ : syracuseStep 1169223 = 1753835) B1753835
theorem B1169243 : Blo 1168401 1169243 := bstep (se 1 (by rfl) ⟨876932, by rfl⟩ : syracuseStep 1169243 = 1753865) B1753865
theorem B1972127 : Blo 1168401 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B1169311 : Blo 1168401 1169311 := bstep (se 1 (by rfl) ⟨876983, by rfl⟩ : syracuseStep 1169311 = 1753967) B1753967
theorem B1169479 : Blo 1168401 1169479 := bstep (se 1 (by rfl) ⟨877109, by rfl⟩ : syracuseStep 1169479 = 1754219) B1754219
theorem B8001641 : Blo 1168401 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B1169639 : Blo 1168401 1169639 := bstep (se 1 (by rfl) ⟨877229, by rfl⟩ : syracuseStep 1169639 = 1754459) B1754459
theorem B4438259 : Blo 1168401 4438259 := bstep (se 1 (by rfl) ⟨3328694, by rfl⟩ : syracuseStep 4438259 = 6657389) B6657389
theorem B1169823 : Blo 1168401 1169823 := bstep (se 1 (by rfl) ⟨877367, by rfl⟩ : syracuseStep 1169823 = 1754735) B1754735
theorem B1169871 : Blo 1168401 1169871 := bstep (se 1 (by rfl) ⟨877403, by rfl⟩ : syracuseStep 1169871 = 1754807) B1754807
theorem B1169895 : Blo 1168401 1169895 := bstep (se 1 (by rfl) ⟨877421, by rfl⟩ : syracuseStep 1169895 = 1754843) B1754843
theorem B18971131 : Blo 1168401 18971131 := bstep (se 1 (by rfl) ⟨14228348, by rfl⟩ : syracuseStep 18971131 = 28456697) B28456697
theorem B1170011 : Blo 1168401 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B10672793 : Blo 1168401 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B1170079 : Blo 1168401 1170079 := bstep (se 1 (by rfl) ⟨877559, by rfl⟩ : syracuseStep 1170079 = 1755119) B1755119
theorem B13318829 : Blo 1168401 13318829 := bstep (se 3 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 13318829 = 4994561) B4994561
theorem B10124099 : Blo 1168401 10124099 := bstep (se 1 (by rfl) ⟨7593074, by rfl⟩ : syracuseStep 10124099 = 15186149) B15186149
theorem B1170247 : Blo 1168401 1170247 := bstep (se 1 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 1170247 = 1755371) B1755371
theorem B1170287 : Blo 1168401 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B1170343 : Blo 1168401 1170343 := bstep (se 1 (by rfl) ⟨877757, by rfl⟩ : syracuseStep 1170343 = 1755515) B1755515
theorem B18013175 : Blo 1168401 18013175 := bstep (se 1 (by rfl) ⟨13509881, by rfl⟩ : syracuseStep 18013175 = 27019763) B27019763
theorem B9993293 : Blo 1168401 9993293 := bstep (se 3 (by rfl) ⟨1873742, by rfl⟩ : syracuseStep 9993293 = 3747485) B3747485
theorem B4996187 : Blo 1168401 4996187 := bstep (se 1 (by rfl) ⟨3747140, by rfl⟩ : syracuseStep 4996187 = 7494281) B7494281
theorem B2497657 : Blo 1168401 2497657 := bstep (se 2 (by rfl) ⟨936621, by rfl⟩ : syracuseStep 2497657 = 1873243) B1873243
theorem B6659279 : Blo 1168401 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B2850023 : Blo 1168401 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B9985295 : Blo 1168401 9985295 := bstep (se 1 (by rfl) ⟨7488971, by rfl⟩ : syracuseStep 9985295 = 14977943) B14977943
theorem B2628935 : Blo 1168401 2628935 := bstep (se 1 (by rfl) ⟨1971701, by rfl⟩ : syracuseStep 2628935 = 3943403) B3943403
theorem B3161423 : Blo 1168401 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B2628971 : Blo 1168401 2628971 := bstep (se 1 (by rfl) ⟨1971728, by rfl⟩ : syracuseStep 2628971 = 3943457) B3943457
theorem B5692781 : Blo 1168401 5692781 := bstep (se 3 (by rfl) ⟨1067396, by rfl⟩ : syracuseStep 5692781 = 2134793) B2134793
theorem B4996475 : Blo 1168401 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B2629097 : Blo 1168401 2629097 := bstep (se 2 (by rfl) ⟨985911, by rfl⟩ : syracuseStep 2629097 = 1971823) B1971823
theorem B4439549 : Blo 1168401 4439549 := bstep (se 3 (by rfl) ⟨832415, by rfl⟩ : syracuseStep 4439549 = 1664831) B1664831
theorem B2629241 : Blo 1168401 2629241 := bstep (se 2 (by rfl) ⟨985965, by rfl⟩ : syracuseStep 2629241 = 1971931) B1971931
theorem B1752911 : Blo 1168401 1752911 := bstep (se 1 (by rfl) ⟨1314683, by rfl⟩ : syracuseStep 1752911 = 2629367) B2629367
theorem B1753031 : Blo 1168401 1753031 := bstep (se 1 (by rfl) ⟨1314773, by rfl⟩ : syracuseStep 1753031 = 2629547) B2629547
theorem B1753295 : Blo 1168401 1753295 := bstep (se 1 (by rfl) ⟨1314971, by rfl⟩ : syracuseStep 1753295 = 2629943) B2629943
theorem B14221583 : Blo 1168401 14221583 := bstep (se 1 (by rfl) ⟨10666187, by rfl⟩ : syracuseStep 14221583 = 21332375) B21332375
theorem B3948911 : Blo 1168401 3948911 := bstep (se 1 (by rfl) ⟨2961683, by rfl⟩ : syracuseStep 3948911 = 5923367) B5923367
theorem B2630015 : Blo 1168401 2630015 := bstep (se 1 (by rfl) ⟨1972511, by rfl⟩ : syracuseStep 2630015 = 3945023) B3945023
theorem B22462919 : Blo 1168401 22462919 := bstep (se 1 (by rfl) ⟨16847189, by rfl⟩ : syracuseStep 22462919 = 33694379) B33694379
theorem B11239883 : Blo 1168401 11239883 := bstep (se 1 (by rfl) ⟨8429912, by rfl⟩ : syracuseStep 11239883 = 16859825) B16859825
theorem B28828163 : Blo 1168401 28828163 := bstep (se 1 (by rfl) ⟨21621122, by rfl⟩ : syracuseStep 28828163 = 43242245) B43242245
theorem B22487827 : Blo 1168401 22487827 := bstep (se 1 (by rfl) ⟨16865870, by rfl⟩ : syracuseStep 22487827 = 33731741) B33731741
theorem B1753979 : Blo 1168401 1753979 := bstep (se 1 (by rfl) ⟨1315484, by rfl⟩ : syracuseStep 1753979 = 2630969) B2630969
theorem B5915591 : Blo 1168401 5915591 := bstep (se 1 (by rfl) ⟨4436693, by rfl⟩ : syracuseStep 5915591 = 8873387) B8873387
theorem B1754105 : Blo 1168401 1754105 := bstep (se 2 (by rfl) ⟨657789, by rfl⟩ : syracuseStep 1754105 = 1315579) B1315579
theorem B1754159 : Blo 1168401 1754159 := bstep (se 1 (by rfl) ⟨1315619, by rfl⟩ : syracuseStep 1754159 = 2631239) B2631239
theorem B1754279 : Blo 1168401 1754279 := bstep (se 1 (by rfl) ⟨1315709, by rfl⟩ : syracuseStep 1754279 = 2631419) B2631419
theorem B5924015 : Blo 1168401 5924015 := bstep (se 1 (by rfl) ⟨4443011, by rfl⟩ : syracuseStep 5924015 = 8886023) B8886023
theorem B144041273 : Blo 1168401 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B1754471 : Blo 1168401 1754471 := bstep (se 1 (by rfl) ⟨1315853, by rfl⟩ : syracuseStep 1754471 = 2631707) B2631707
theorem B5334427 : Blo 1168401 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B3949991 : Blo 1168401 3949991 := bstep (se 1 (by rfl) ⟨2962493, by rfl⟩ : syracuseStep 3949991 = 5924987) B5924987
theorem B2958839 : Blo 1168401 2958839 := bstep (se 1 (by rfl) ⟨2219129, by rfl⟩ : syracuseStep 2958839 = 4438259) B4438259
theorem B3000287 : Blo 1168401 3000287 := bstep (se 1 (by rfl) ⟨2250215, by rfl⟩ : syracuseStep 3000287 = 4500431) B4500431
theorem B1755113 : Blo 1168401 1755113 := bstep (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) B1316335
theorem B6662195 : Blo 1168401 6662195 := bstep (se 1 (by rfl) ⟨4996646, by rfl⟩ : syracuseStep 6662195 = 9993293) B9993293
theorem B1755257 : Blo 1168401 1755257 := bstep (se 2 (by rfl) ⟨658221, by rfl⟩ : syracuseStep 1755257 = 1316443) B1316443
theorem B5916887 : Blo 1168401 5916887 := bstep (se 1 (by rfl) ⟨4437665, by rfl⟩ : syracuseStep 5916887 = 8875331) B8875331
theorem B2107615 : Blo 1168401 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B3795187 : Blo 1168401 3795187 := bstep (se 1 (by rfl) ⟨2846390, by rfl⟩ : syracuseStep 3795187 = 5692781) B5692781
theorem B1755455 : Blo 1168401 1755455 := bstep (se 1 (by rfl) ⟨1316591, by rfl⟩ : syracuseStep 1755455 = 2633183) B2633183
theorem B2959699 : Blo 1168401 2959699 := bstep (se 1 (by rfl) ⟨2219774, by rfl⟩ : syracuseStep 2959699 = 4439549) B4439549
theorem B1755599 : Blo 1168401 1755599 := bstep (se 1 (by rfl) ⟨1316699, by rfl⟩ : syracuseStep 1755599 = 2633399) B2633399
theorem B13323203 : Blo 1168401 13323203 := bstep (se 1 (by rfl) ⟨9992402, by rfl⟩ : syracuseStep 13323203 = 19984805) B19984805
theorem B3746999 : Blo 1168401 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B19967309 : Blo 1168401 19967309 := bstep (se 3 (by rfl) ⟨3743870, by rfl⟩ : syracuseStep 19967309 = 7487741) B7487741
theorem B12652001 : Blo 1168401 12652001 := bstep (se 2 (by rfl) ⟨4744500, by rfl⟩ : syracuseStep 12652001 = 9489001) B9489001
theorem B6663653 : Blo 1168401 6663653 := bstep (se 4 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 6663653 = 1249435) B1249435
theorem B47984237 : Blo 1168401 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B1314463 : Blo 1168401 1314463 := bstep (se 1 (by rfl) ⟨985847, by rfl⟩ : syracuseStep 1314463 = 1971695) B1971695
theorem B1314751 : Blo 1168401 1314751 := bstep (se 1 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 1314751 = 1972127) B1972127
theorem B4993127 : Blo 1168401 4993127 := bstep (se 1 (by rfl) ⟨3744845, by rfl⟩ : syracuseStep 4993127 = 7489691) B7489691
theorem B3330209 : Blo 1168401 3330209 := bstep (se 2 (by rfl) ⟨1248828, by rfl⟩ : syracuseStep 3330209 = 2497657) B2497657
theorem B19214567 : Blo 1168401 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B7115195 : Blo 1168401 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B2961947 : Blo 1168401 2961947 := bstep (se 1 (by rfl) ⟨2221460, by rfl⟩ : syracuseStep 2961947 = 4442921) B4442921
theorem B3330791 : Blo 1168401 3330791 := bstep (se 1 (by rfl) ⟨2498093, by rfl⟩ : syracuseStep 3330791 = 4996187) B4996187
theorem B3748639 : Blo 1168401 3748639 := bstep (se 1 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 3748639 = 5622959) B5622959
theorem B6656863 : Blo 1168401 6656863 := bstep (se 1 (by rfl) ⟨4992647, by rfl⟩ : syracuseStep 6656863 = 9985295) B9985295
theorem B3330983 : Blo 1168401 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B1168607 : Blo 1168401 1168607 := bstep (se 1 (by rfl) ⟨876455, by rfl⟩ : syracuseStep 1168607 = 1752911) B1752911
theorem B13317371 : Blo 1168401 13317371 := bstep (se 1 (by rfl) ⟨9988028, by rfl⟩ : syracuseStep 13317371 = 19976057) B19976057
theorem B1168687 : Blo 1168401 1168687 := bstep (se 1 (by rfl) ⟨876515, by rfl⟩ : syracuseStep 1168687 = 1753031) B1753031
theorem B3331439 : Blo 1168401 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B13686245 : Blo 1168401 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B9483749 : Blo 1168401 9483749 := bstep (se 4 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 9483749 = 1778203) B1778203
theorem B1168927 : Blo 1168401 1168927 := bstep (se 1 (by rfl) ⟨876695, by rfl⟩ : syracuseStep 1168927 = 1753391) B1753391
theorem B3331667 : Blo 1168401 3331667 := bstep (se 1 (by rfl) ⟨2498750, by rfl⟩ : syracuseStep 3331667 = 4997501) B4997501
theorem B1169087 : Blo 1168401 1169087 := bstep (se 1 (by rfl) ⟨876815, by rfl⟩ : syracuseStep 1169087 = 1753631) B1753631
theorem B7600061 : Blo 1168401 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B7600087 : Blo 1168401 7600087 := bstep (se 1 (by rfl) ⟨5700065, by rfl⟩ : syracuseStep 7600087 = 11400131) B11400131
theorem B25294841 : Blo 1168401 25294841 := bstep (se 2 (by rfl) ⟨9485565, by rfl⟩ : syracuseStep 25294841 = 18971131) B18971131
theorem B1972255 : Blo 1168401 1972255 := bstep (se 1 (by rfl) ⟨1479191, by rfl⟩ : syracuseStep 1972255 = 2958383) B2958383
theorem B1169535 : Blo 1168401 1169535 := bstep (se 1 (by rfl) ⟨877151, by rfl⟩ : syracuseStep 1169535 = 1754303) B1754303
theorem B1169631 : Blo 1168401 1169631 := bstep (se 1 (by rfl) ⟨877223, by rfl⟩ : syracuseStep 1169631 = 1754447) B1754447
theorem B1169691 : Blo 1168401 1169691 := bstep (se 1 (by rfl) ⟨877268, by rfl⟩ : syracuseStep 1169691 = 1754537) B1754537
theorem B2218279 : Blo 1168401 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B1169791 : Blo 1168401 1169791 := bstep (se 1 (by rfl) ⟨877343, by rfl⟩ : syracuseStep 1169791 = 1754687) B1754687
theorem B1169819 : Blo 1168401 1169819 := bstep (se 1 (by rfl) ⟨877364, by rfl⟩ : syracuseStep 1169819 = 1754729) B1754729
theorem B1972687 : Blo 1168401 1972687 := bstep (se 1 (by rfl) ⟨1479515, by rfl⟩ : syracuseStep 1972687 = 2959031) B2959031
theorem B1170111 : Blo 1168401 1170111 := bstep (se 1 (by rfl) ⟨877583, by rfl⟩ : syracuseStep 1170111 = 1755167) B1755167
theorem B1170239 : Blo 1168401 1170239 := bstep (se 1 (by rfl) ⟨877679, by rfl⟩ : syracuseStep 1170239 = 1755359) B1755359
theorem B1170279 : Blo 1168401 1170279 := bstep (se 1 (by rfl) ⟨877709, by rfl⟩ : syracuseStep 1170279 = 1755419) B1755419
theorem B8879219 : Blo 1168401 8879219 := bstep (se 1 (by rfl) ⟨6659414, by rfl⟩ : syracuseStep 8879219 = 13318829) B13318829
theorem B1973423 : Blo 1168401 1973423 := bstep (se 1 (by rfl) ⟨1480067, by rfl⟩ : syracuseStep 1973423 = 2960135) B2960135
theorem B2809019 : Blo 1168401 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B6749399 : Blo 1168401 6749399 := bstep (se 1 (by rfl) ⟨5062049, by rfl⟩ : syracuseStep 6749399 = 10124099) B10124099
theorem B12008783 : Blo 1168401 12008783 := bstep (se 1 (by rfl) ⟨9006587, by rfl⟩ : syracuseStep 12008783 = 18013175) B18013175
theorem B4439519 : Blo 1168401 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B2629115 : Blo 1168401 2629115 := bstep (se 1 (by rfl) ⟨1971836, by rfl⟩ : syracuseStep 2629115 = 3943673) B3943673
theorem B1752623 : Blo 1168401 1752623 := bstep (se 1 (by rfl) ⟨1314467, by rfl⟩ : syracuseStep 1752623 = 2628935) B2628935
theorem B1752647 : Blo 1168401 1752647 := bstep (se 1 (by rfl) ⟨1314485, by rfl⟩ : syracuseStep 1752647 = 2628971) B2628971
theorem B5922395 : Blo 1168401 5922395 := bstep (se 1 (by rfl) ⟨4441796, by rfl⟩ : syracuseStep 5922395 = 8883593) B8883593
theorem B2629223 : Blo 1168401 2629223 := bstep (se 1 (by rfl) ⟨1971917, by rfl⟩ : syracuseStep 2629223 = 3943835) B3943835
theorem B1752731 : Blo 1168401 1752731 := bstep (se 1 (by rfl) ⟨1314548, by rfl⟩ : syracuseStep 1752731 = 2629097) B2629097
theorem B2629295 : Blo 1168401 2629295 := bstep (se 1 (by rfl) ⟨1971971, by rfl⟩ : syracuseStep 2629295 = 3943943) B3943943
theorem B1752827 : Blo 1168401 1752827 := bstep (se 1 (by rfl) ⟨1314620, by rfl⟩ : syracuseStep 1752827 = 2629241) B2629241
theorem B2629385 : Blo 1168401 2629385 := bstep (se 2 (by rfl) ⟨986019, by rfl⟩ : syracuseStep 2629385 = 1972039) B1972039
theorem B10673963 : Blo 1168401 10673963 := bstep (se 1 (by rfl) ⟨8005472, by rfl⟩ : syracuseStep 10673963 = 16010945) B16010945
theorem B9609131 : Blo 1168401 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B2219987 : Blo 1168401 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B2629673 : Blo 1168401 2629673 := bstep (se 2 (by rfl) ⟨986127, by rfl⟩ : syracuseStep 2629673 = 1972255) B1972255
theorem B2220139 : Blo 1168401 2220139 := bstep (se 1 (by rfl) ⟨1665104, by rfl⟩ : syracuseStep 2220139 = 3330209) B3330209
theorem B1753343 : Blo 1168401 1753343 := bstep (se 1 (by rfl) ⟨1315007, by rfl⟩ : syracuseStep 1753343 = 2630015) B2630015
theorem B4743463 : Blo 1168401 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B2810153 : Blo 1168401 2810153 := bstep (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) B2107615
theorem B14975279 : Blo 1168401 14975279 := bstep (se 1 (by rfl) ⟨11231459, by rfl⟩ : syracuseStep 14975279 = 22462919) B22462919
theorem B1974631 : Blo 1168401 1974631 := bstep (se 1 (by rfl) ⟨1480973, by rfl⟩ : syracuseStep 1974631 = 2961947) B2961947
theorem B2957705 : Blo 1168401 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B2220527 : Blo 1168401 2220527 := bstep (se 1 (by rfl) ⟨1665395, by rfl⟩ : syracuseStep 2220527 = 3330791) B3330791
theorem B2630249 : Blo 1168401 2630249 := bstep (se 2 (by rfl) ⟨986343, by rfl⟩ : syracuseStep 2630249 = 1972687) B1972687
theorem B3949343 : Blo 1168401 3949343 := bstep (se 1 (by rfl) ⟨2962007, by rfl⟩ : syracuseStep 3949343 = 5924015) B5924015
theorem B96027515 : Blo 1168401 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B32023421 : Blo 1168401 32023421 := bstep (se 3 (by rfl) ⟨6004391, by rfl⟩ : syracuseStep 32023421 = 12008783) B12008783
theorem B2220959 : Blo 1168401 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B29983769 : Blo 1168401 29983769 := bstep (se 2 (by rfl) ⟨11243913, by rfl⟩ : syracuseStep 29983769 = 22487827) B22487827
theorem B4998185 : Blo 1168401 4998185 := bstep (se 2 (by rfl) ⟨1874319, by rfl⟩ : syracuseStep 4998185 = 3748639) B3748639
theorem B2221111 : Blo 1168401 2221111 := bstep (se 1 (by rfl) ⟨1665833, by rfl⟩ : syracuseStep 2221111 = 3331667) B3331667
theorem B76875101 : Blo 1168401 76875101 := bstep (se 3 (by rfl) ⟨14414081, by rfl⟩ : syracuseStep 76875101 = 28828163) B28828163
theorem B4441463 : Blo 1168401 4441463 := bstep (se 1 (by rfl) ⟨3331097, by rfl⟩ : syracuseStep 4441463 = 6662195) B6662195
theorem B7112569 : Blo 1168401 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B8882135 : Blo 1168401 8882135 := bstep (se 1 (by rfl) ⟨6661601, by rfl⟩ : syracuseStep 8882135 = 13323203) B13323203
theorem B4499599 : Blo 1168401 4499599 := bstep (se 1 (by rfl) ⟨3374699, by rfl⟩ : syracuseStep 4499599 = 6749399) B6749399
theorem B2959679 : Blo 1168401 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B4442435 : Blo 1168401 4442435 := bstep (se 1 (by rfl) ⟨3331826, by rfl⟩ : syracuseStep 4442435 = 6663653) B6663653
theorem B8882621 : Blo 1168401 8882621 := bstep (se 3 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 8882621 = 3330983) B3330983
theorem B3328751 : Blo 1168401 3328751 := bstep (se 1 (by rfl) ⟨2496563, by rfl⟩ : syracuseStep 3328751 = 4993127) B4993127
theorem B9481055 : Blo 1168401 9481055 := bstep (se 1 (by rfl) ⟨7110791, by rfl⟩ : syracuseStep 9481055 = 14221583) B14221583
theorem B2632607 : Blo 1168401 2632607 := bstep (se 1 (by rfl) ⟨1974455, by rfl⟩ : syracuseStep 2632607 = 3948911) B3948911
theorem B7490717 : Blo 1168401 7490717 := bstep (se 3 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 7490717 = 2809019) B2809019
theorem B3943727 : Blo 1168401 3943727 := bstep (se 1 (by rfl) ⟨2957795, by rfl⟩ : syracuseStep 3943727 = 5915591) B5915591
theorem B2633327 : Blo 1168401 2633327 := bstep (se 1 (by rfl) ⟨1974995, by rfl⟩ : syracuseStep 2633327 = 3949991) B3949991
theorem B8875817 : Blo 1168401 8875817 := bstep (se 2 (by rfl) ⟨3328431, by rfl⟩ : syracuseStep 8875817 = 6656863) B6656863
theorem B5066707 : Blo 1168401 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B16863227 : Blo 1168401 16863227 := bstep (se 1 (by rfl) ⟨12647420, by rfl⟩ : syracuseStep 16863227 = 25294841) B25294841
theorem B3944591 : Blo 1168401 3944591 := bstep (se 1 (by rfl) ⟨2958443, by rfl⟩ : syracuseStep 3944591 = 5916887) B5916887
theorem B5919479 : Blo 1168401 5919479 := bstep (se 1 (by rfl) ⟨4439609, by rfl⟩ : syracuseStep 5919479 = 8879219) B8879219
theorem B1315615 : Blo 1168401 1315615 := bstep (se 1 (by rfl) ⟨986711, by rfl⟩ : syracuseStep 1315615 = 1973423) B1973423
theorem B8434667 : Blo 1168401 8434667 := bstep (se 1 (by rfl) ⟨6326000, by rfl⟩ : syracuseStep 8434667 = 12652001) B12652001
theorem B1168415 : Blo 1168401 1168415 := bstep (se 1 (by rfl) ⟨876311, by rfl⟩ : syracuseStep 1168415 = 1752623) B1752623
theorem B1168431 : Blo 1168401 1168431 := bstep (se 1 (by rfl) ⟨876323, by rfl⟩ : syracuseStep 1168431 = 1752647) B1752647
theorem B1168487 : Blo 1168401 1168487 := bstep (se 1 (by rfl) ⟨876365, by rfl⟩ : syracuseStep 1168487 = 1752731) B1752731
theorem B1168551 : Blo 1168401 1168551 := bstep (se 1 (by rfl) ⟨876413, by rfl⟩ : syracuseStep 1168551 = 1752827) B1752827
theorem B7115975 : Blo 1168401 7115975 := bstep (se 1 (by rfl) ⟨5336981, by rfl⟩ : syracuseStep 7115975 = 10673963) B10673963
theorem B5919965 : Blo 1168401 5919965 := bstep (se 3 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 5919965 = 2219987) B2219987
theorem B8000765 : Blo 1168401 8000765 := bstep (se 3 (by rfl) ⟨1500143, by rfl⟩ : syracuseStep 8000765 = 3000287) B3000287
theorem B1168863 : Blo 1168401 1168863 := bstep (se 1 (by rfl) ⟨876647, by rfl⟩ : syracuseStep 1168863 = 1753295) B1753295
theorem B12809711 : Blo 1168401 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B7493255 : Blo 1168401 7493255 := bstep (se 1 (by rfl) ⟨5619941, by rfl⟩ : syracuseStep 7493255 = 11239883) B11239883
theorem B5060249 : Blo 1168401 5060249 := bstep (se 2 (by rfl) ⟨1897593, by rfl⟩ : syracuseStep 5060249 = 3795187) B3795187
theorem B3946265 : Blo 1168401 3946265 := bstep (se 2 (by rfl) ⟨1479849, by rfl⟩ : syracuseStep 3946265 = 2959699) B2959699
theorem B1169319 : Blo 1168401 1169319 := bstep (se 1 (by rfl) ⟨876989, by rfl⟩ : syracuseStep 1169319 = 1753979) B1753979
theorem B1169403 : Blo 1168401 1169403 := bstep (se 1 (by rfl) ⟨877052, by rfl⟩ : syracuseStep 1169403 = 1754105) B1754105
theorem B1169439 : Blo 1168401 1169439 := bstep (se 1 (by rfl) ⟨877079, by rfl⟩ : syracuseStep 1169439 = 1754159) B1754159
theorem B1169519 : Blo 1168401 1169519 := bstep (se 1 (by rfl) ⟨877139, by rfl⟩ : syracuseStep 1169519 = 1754279) B1754279
theorem B8878247 : Blo 1168401 8878247 := bstep (se 1 (by rfl) ⟨6658685, by rfl⟩ : syracuseStep 8878247 = 13317371) B13317371
theorem B1169647 : Blo 1168401 1169647 := bstep (se 1 (by rfl) ⟨877235, by rfl⟩ : syracuseStep 1169647 = 1754471) B1754471
theorem B9124163 : Blo 1168401 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B6322499 : Blo 1168401 6322499 := bstep (se 1 (by rfl) ⟨4741874, by rfl⟩ : syracuseStep 6322499 = 9483749) B9483749
theorem B1972559 : Blo 1168401 1972559 := bstep (se 1 (by rfl) ⟨1479419, by rfl⟩ : syracuseStep 1972559 = 2958839) B2958839
theorem B1170075 : Blo 1168401 1170075 := bstep (se 1 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 1170075 = 1755113) B1755113
theorem B1170171 : Blo 1168401 1170171 := bstep (se 1 (by rfl) ⟨877628, by rfl⟩ : syracuseStep 1170171 = 1755257) B1755257
theorem B1170303 : Blo 1168401 1170303 := bstep (se 1 (by rfl) ⟨877727, by rfl⟩ : syracuseStep 1170303 = 1755455) B1755455
theorem B1170399 : Blo 1168401 1170399 := bstep (se 1 (by rfl) ⟨877799, by rfl⟩ : syracuseStep 1170399 = 1755599) B1755599
theorem B2497999 : Blo 1168401 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B1752617 : Blo 1168401 1752617 := bstep (se 2 (by rfl) ⟨657231, by rfl⟩ : syracuseStep 1752617 = 1314463) B1314463
theorem B13311539 : Blo 1168401 13311539 := bstep (se 1 (by rfl) ⟨9983654, by rfl⟩ : syracuseStep 13311539 = 19967309) B19967309
theorem B1752743 : Blo 1168401 1752743 := bstep (se 1 (by rfl) ⟨1314557, by rfl⟩ : syracuseStep 1752743 = 2629115) B2629115
theorem B3948263 : Blo 1168401 3948263 := bstep (se 1 (by rfl) ⟨2961197, by rfl⟩ : syracuseStep 3948263 = 5922395) B5922395
theorem B1752815 : Blo 1168401 1752815 := bstep (se 1 (by rfl) ⟨1314611, by rfl⟩ : syracuseStep 1752815 = 2629223) B2629223
theorem B31989491 : Blo 1168401 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B25624349 : Blo 1168401 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B1752863 : Blo 1168401 1752863 := bstep (se 1 (by rfl) ⟨1314647, by rfl⟩ : syracuseStep 1752863 = 2629295) B2629295
theorem B40533797 : Blo 1168401 40533797 := bstep (se 4 (by rfl) ⟨3800043, by rfl⟩ : syracuseStep 40533797 = 7600087) B7600087
theorem B1752923 : Blo 1168401 1752923 := bstep (se 1 (by rfl) ⟨1314692, by rfl⟩ : syracuseStep 1752923 = 2629385) B2629385
theorem B1753001 : Blo 1168401 1753001 := bstep (se 2 (by rfl) ⟨657375, by rfl⟩ : syracuseStep 1753001 = 1314751) B1314751
theorem B1753115 : Blo 1168401 1753115 := bstep (se 1 (by rfl) ⟨1314836, by rfl⟩ : syracuseStep 1753115 = 2629673) B2629673
theorem B2629727 : Blo 1168401 2629727 := bstep (se 1 (by rfl) ⟨1972295, by rfl⟩ : syracuseStep 2629727 = 3944591) B3944591
theorem B6324617 : Blo 1168401 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B1753499 : Blo 1168401 1753499 := bstep (se 1 (by rfl) ⟨1315124, by rfl⟩ : syracuseStep 1753499 = 2630249) B2630249
theorem B21348947 : Blo 1168401 21348947 := bstep (se 1 (by rfl) ⟨16011710, by rfl⟩ : syracuseStep 21348947 = 32023421) B32023421
theorem B19989179 : Blo 1168401 19989179 := bstep (se 1 (by rfl) ⟨14991884, by rfl⟩ : syracuseStep 19989179 = 29983769) B29983769
theorem B4743983 : Blo 1168401 4743983 := bstep (se 1 (by rfl) ⟨3557987, by rfl⟩ : syracuseStep 4743983 = 7115975) B7115975
theorem B5333843 : Blo 1168401 5333843 := bstep (se 1 (by rfl) ⟨4000382, by rfl⟩ : syracuseStep 5333843 = 8000765) B8000765
theorem B51250067 : Blo 1168401 51250067 := bstep (se 1 (by rfl) ⟨38437550, by rfl⟩ : syracuseStep 51250067 = 76875101) B76875101
theorem B1754153 : Blo 1168401 1754153 := bstep (se 2 (by rfl) ⟨657807, by rfl⟩ : syracuseStep 1754153 = 1315615) B1315615
theorem B2630843 : Blo 1168401 2630843 := bstep (se 1 (by rfl) ⟨1973132, by rfl⟩ : syracuseStep 2630843 = 3946265) B3946265
theorem B1755071 : Blo 1168401 1755071 := bstep (se 1 (by rfl) ⟨1316303, by rfl⟩ : syracuseStep 1755071 = 2632607) B2632607
theorem B25282813 : Blo 1168401 25282813 := bstep (se 3 (by rfl) ⟨4740527, by rfl⟩ : syracuseStep 25282813 = 9481055) B9481055
theorem B8874359 : Blo 1168401 8874359 := bstep (se 1 (by rfl) ⟨6655769, by rfl⟩ : syracuseStep 8874359 = 13311539) B13311539
theorem B1755551 : Blo 1168401 1755551 := bstep (se 1 (by rfl) ⟨1316663, by rfl⟩ : syracuseStep 1755551 = 2633327) B2633327
theorem B2632175 : Blo 1168401 2632175 := bstep (se 1 (by rfl) ⟨1974131, by rfl⟩ : syracuseStep 2632175 = 3948263) B3948263
theorem B21326327 : Blo 1168401 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B17082899 : Blo 1168401 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B5917211 : Blo 1168401 5917211 := bstep (se 1 (by rfl) ⟨4437908, by rfl⟩ : syracuseStep 5917211 = 8875817) B8875817
theorem B11242151 : Blo 1168401 11242151 := bstep (se 1 (by rfl) ⟨8431613, by rfl⟩ : syracuseStep 11242151 = 16863227) B16863227
theorem B2960185 : Blo 1168401 2960185 := bstep (se 2 (by rfl) ⟨1110069, by rfl⟩ : syracuseStep 2960185 = 2220139) B2220139
theorem B5999465 : Blo 1168401 5999465 := bstep (se 2 (by rfl) ⟨2249799, by rfl⟩ : syracuseStep 5999465 = 4499599) B4499599
theorem B2632841 : Blo 1168401 2632841 := bstep (se 2 (by rfl) ⟨987315, by rfl⟩ : syracuseStep 2632841 = 1974631) B1974631
theorem B2632895 : Blo 1168401 2632895 := bstep (se 1 (by rfl) ⟨1974671, by rfl⟩ : syracuseStep 2632895 = 3949343) B3949343
theorem B5623111 : Blo 1168401 5623111 := bstep (se 1 (by rfl) ⟨4217333, by rfl⟩ : syracuseStep 5623111 = 8434667) B8434667
theorem B2960975 : Blo 1168401 2960975 := bstep (se 1 (by rfl) ⟨2220731, by rfl⟩ : syracuseStep 2960975 = 4441463) B4441463
theorem B2961481 : Blo 1168401 2961481 := bstep (se 2 (by rfl) ⟨1110555, by rfl⟩ : syracuseStep 2961481 = 2221111) B2221111
theorem B5918831 : Blo 1168401 5918831 := bstep (se 1 (by rfl) ⟨4439123, by rfl⟩ : syracuseStep 5918831 = 8878247) B8878247
theorem B6082775 : Blo 1168401 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B4214999 : Blo 1168401 4214999 := bstep (se 1 (by rfl) ⟨3161249, by rfl⟩ : syracuseStep 4214999 = 6322499) B6322499
theorem B2961623 : Blo 1168401 2961623 := bstep (se 1 (by rfl) ⟨2221217, by rfl⟩ : syracuseStep 2961623 = 4442435) B4442435
theorem B1315039 : Blo 1168401 1315039 := bstep (se 1 (by rfl) ⟨986279, by rfl⟩ : syracuseStep 1315039 = 1972559) B1972559
theorem B3330665 : Blo 1168401 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B4993811 : Blo 1168401 4993811 := bstep (se 1 (by rfl) ⟨3745358, by rfl⟩ : syracuseStep 4993811 = 7490717) B7490717
theorem B1168411 : Blo 1168401 1168411 := bstep (se 1 (by rfl) ⟨876308, by rfl⟩ : syracuseStep 1168411 = 1752617) B1752617
theorem B1168495 : Blo 1168401 1168495 := bstep (se 1 (by rfl) ⟨876371, by rfl⟩ : syracuseStep 1168495 = 1752743) B1752743
theorem B1168543 : Blo 1168401 1168543 := bstep (se 1 (by rfl) ⟨876407, by rfl⟩ : syracuseStep 1168543 = 1752815) B1752815
theorem B9483425 : Blo 1168401 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B1168575 : Blo 1168401 1168575 := bstep (se 1 (by rfl) ⟨876431, by rfl⟩ : syracuseStep 1168575 = 1752863) B1752863
theorem B27022531 : Blo 1168401 27022531 := bstep (se 1 (by rfl) ⟨20266898, by rfl⟩ : syracuseStep 27022531 = 40533797) B40533797
theorem B1168615 : Blo 1168401 1168615 := bstep (se 1 (by rfl) ⟨876461, by rfl⟩ : syracuseStep 1168615 = 1752923) B1752923
theorem B6755609 : Blo 1168401 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B1168667 : Blo 1168401 1168667 := bstep (se 1 (by rfl) ⟨876500, by rfl⟩ : syracuseStep 1168667 = 1753001) B1753001
theorem B1168895 : Blo 1168401 1168895 := bstep (se 1 (by rfl) ⟨876671, by rfl⟩ : syracuseStep 1168895 = 1753343) B1753343
theorem B9983519 : Blo 1168401 9983519 := bstep (se 1 (by rfl) ⟨7487639, by rfl⟩ : syracuseStep 9983519 = 14975279) B14975279
theorem B1971803 : Blo 1168401 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B1480351 : Blo 1168401 1480351 := bstep (se 1 (by rfl) ⟨1110263, by rfl⟩ : syracuseStep 1480351 = 2220527) B2220527
theorem B3946319 : Blo 1168401 3946319 := bstep (se 1 (by rfl) ⟨2959739, by rfl⟩ : syracuseStep 3946319 = 5919479) B5919479
theorem B64018343 : Blo 1168401 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B3332123 : Blo 1168401 3332123 := bstep (se 1 (by rfl) ⟨2499092, by rfl⟩ : syracuseStep 3332123 = 4998185) B4998185
theorem B7493741 : Blo 1168401 7493741 := bstep (se 3 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 7493741 = 2810153) B2810153
theorem B3946643 : Blo 1168401 3946643 := bstep (se 1 (by rfl) ⟨2959982, by rfl⟩ : syracuseStep 3946643 = 5919965) B5919965
theorem B4995503 : Blo 1168401 4995503 := bstep (se 1 (by rfl) ⟨3746627, by rfl⟩ : syracuseStep 4995503 = 7493255) B7493255
theorem B3373499 : Blo 1168401 3373499 := bstep (se 1 (by rfl) ⟨2530124, by rfl⟩ : syracuseStep 3373499 = 5060249) B5060249
theorem B34159229 : Blo 1168401 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B5921423 : Blo 1168401 5921423 := bstep (se 1 (by rfl) ⟨4441067, by rfl⟩ : syracuseStep 5921423 = 8882135) B8882135
theorem B1973119 : Blo 1168401 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B5921747 : Blo 1168401 5921747 := bstep (se 1 (by rfl) ⟨4441310, by rfl⟩ : syracuseStep 5921747 = 8882621) B8882621
theorem B2219167 : Blo 1168401 2219167 := bstep (se 1 (by rfl) ⟨1664375, by rfl⟩ : syracuseStep 2219167 = 3328751) B3328751
theorem B2629151 : Blo 1168401 2629151 := bstep (se 1 (by rfl) ⟨1971863, by rfl⟩ : syracuseStep 2629151 = 3943727) B3943727
theorem B5922557 : Blo 1168401 5922557 := bstep (se 3 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 5922557 = 2220959) B2220959
theorem B1753151 : Blo 1168401 1753151 := bstep (se 1 (by rfl) ⟨1314863, by rfl⟩ : syracuseStep 1753151 = 2629727) B2629727
theorem B3948641 : Blo 1168401 3948641 := bstep (se 2 (by rfl) ⟨1480740, by rfl⟩ : syracuseStep 3948641 = 2961481) B2961481
theorem B4055183 : Blo 1168401 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B2809999 : Blo 1168401 2809999 := bstep (se 1 (by rfl) ⟨2107499, by rfl⟩ : syracuseStep 2809999 = 4214999) B4214999
theorem B1974415 : Blo 1168401 1974415 := bstep (se 1 (by rfl) ⟨1480811, by rfl⟩ : syracuseStep 1974415 = 2961623) B2961623
theorem B1753385 : Blo 1168401 1753385 := bstep (se 2 (by rfl) ⟨657519, by rfl⟩ : syracuseStep 1753385 = 1315039) B1315039
theorem B33710417 : Blo 1168401 33710417 := bstep (se 2 (by rfl) ⟨12641406, by rfl⟩ : syracuseStep 33710417 = 25282813) B25282813
theorem B2220443 : Blo 1168401 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B3162655 : Blo 1168401 3162655 := bstep (se 1 (by rfl) ⟨2371991, by rfl⟩ : syracuseStep 3162655 = 4743983) B4743983
theorem B3555895 : Blo 1168401 3555895 := bstep (se 1 (by rfl) ⟨2666921, by rfl⟩ : syracuseStep 3555895 = 5333843) B5333843
theorem B18014957 : Blo 1168401 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B1753895 : Blo 1168401 1753895 := bstep (se 1 (by rfl) ⟨1315421, by rfl⟩ : syracuseStep 1753895 = 2630843) B2630843
theorem B8995997 : Blo 1168401 8995997 := bstep (se 3 (by rfl) ⟨1686749, by rfl⟩ : syracuseStep 8995997 = 3373499) B3373499
theorem B2630825 : Blo 1168401 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B2630879 : Blo 1168401 2630879 := bstep (se 1 (by rfl) ⟨1973159, by rfl⟩ : syracuseStep 2630879 = 3946319) B3946319
theorem B2221415 : Blo 1168401 2221415 := bstep (se 1 (by rfl) ⟨1666061, by rfl⟩ : syracuseStep 2221415 = 3332123) B3332123
theorem B2631095 : Blo 1168401 2631095 := bstep (se 1 (by rfl) ⟨1973321, by rfl⟩ : syracuseStep 2631095 = 3946643) B3946643
theorem B2958889 : Blo 1168401 2958889 := bstep (se 2 (by rfl) ⟨1109583, by rfl⟩ : syracuseStep 2958889 = 2219167) B2219167
theorem B5916239 : Blo 1168401 5916239 := bstep (se 1 (by rfl) ⟨4437179, by rfl⟩ : syracuseStep 5916239 = 8874359) B8874359
theorem B36030041 : Blo 1168401 36030041 := bstep (se 2 (by rfl) ⟨13511265, by rfl⟩ : syracuseStep 36030041 = 27022531) B27022531
theorem B1754783 : Blo 1168401 1754783 := bstep (se 1 (by rfl) ⟨1316087, by rfl⟩ : syracuseStep 1754783 = 2632175) B2632175
theorem B11388599 : Blo 1168401 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B7497481 : Blo 1168401 7497481 := bstep (se 2 (by rfl) ⟨2811555, by rfl⟩ : syracuseStep 7497481 = 5623111) B5623111
theorem B1755227 : Blo 1168401 1755227 := bstep (se 1 (by rfl) ⟨1316420, by rfl⟩ : syracuseStep 1755227 = 2632841) B2632841
theorem B1755263 : Blo 1168401 1755263 := bstep (se 1 (by rfl) ⟨1316447, by rfl⟩ : syracuseStep 1755263 = 2632895) B2632895
theorem B14232631 : Blo 1168401 14232631 := bstep (se 1 (by rfl) ⟨10674473, by rfl⟩ : syracuseStep 14232631 = 21348947) B21348947
theorem B3329207 : Blo 1168401 3329207 := bstep (se 1 (by rfl) ⟨2496905, by rfl⟩ : syracuseStep 3329207 = 4993811) B4993811
theorem B6655679 : Blo 1168401 6655679 := bstep (se 1 (by rfl) ⟨4991759, by rfl⟩ : syracuseStep 6655679 = 9983519) B9983519
theorem B1314535 : Blo 1168401 1314535 := bstep (se 1 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 1314535 = 1971803) B1971803
theorem B3330335 : Blo 1168401 3330335 := bstep (se 1 (by rfl) ⟨2497751, by rfl⟩ : syracuseStep 3330335 = 4995503) B4995503
theorem B14217551 : Blo 1168401 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B3944807 : Blo 1168401 3944807 := bstep (se 1 (by rfl) ⟨2958605, by rfl⟩ : syracuseStep 3944807 = 5917211) B5917211
theorem B1168743 : Blo 1168401 1168743 := bstep (se 1 (by rfl) ⟨876557, by rfl⟩ : syracuseStep 1168743 = 1753115) B1753115
theorem B3945887 : Blo 1168401 3945887 := bstep (se 1 (by rfl) ⟨2959415, by rfl⟩ : syracuseStep 3945887 = 5918831) B5918831
theorem B4216411 : Blo 1168401 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1168999 : Blo 1168401 1168999 := bstep (se 1 (by rfl) ⟨876749, by rfl⟩ : syracuseStep 1168999 = 1753499) B1753499
theorem B13326119 : Blo 1168401 13326119 := bstep (se 1 (by rfl) ⟨9994589, by rfl⟩ : syracuseStep 13326119 = 19989179) B19989179
theorem B34166711 : Blo 1168401 34166711 := bstep (se 1 (by rfl) ⟨25625033, by rfl⟩ : syracuseStep 34166711 = 51250067) B51250067
theorem B1169435 : Blo 1168401 1169435 := bstep (se 1 (by rfl) ⟨877076, by rfl⟩ : syracuseStep 1169435 = 1754153) B1754153
theorem B6322283 : Blo 1168401 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B3946913 : Blo 1168401 3946913 := bstep (se 2 (by rfl) ⟨1480092, by rfl⟩ : syracuseStep 3946913 = 2960185) B2960185
theorem B42678895 : Blo 1168401 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B1170047 : Blo 1168401 1170047 := bstep (se 1 (by rfl) ⟨877535, by rfl⟩ : syracuseStep 1170047 = 1755071) B1755071
theorem B4995827 : Blo 1168401 4995827 := bstep (se 1 (by rfl) ⟨3746870, by rfl⟩ : syracuseStep 4995827 = 7493741) B7493741
theorem B1170367 : Blo 1168401 1170367 := bstep (se 1 (by rfl) ⟨877775, by rfl⟩ : syracuseStep 1170367 = 1755551) B1755551
theorem B22772819 : Blo 1168401 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B3947615 : Blo 1168401 3947615 := bstep (se 1 (by rfl) ⟨2960711, by rfl⟩ : syracuseStep 3947615 = 5921423) B5921423
theorem B7494767 : Blo 1168401 7494767 := bstep (se 1 (by rfl) ⟨5621075, by rfl⟩ : syracuseStep 7494767 = 11242151) B11242151
theorem B3947831 : Blo 1168401 3947831 := bstep (se 1 (by rfl) ⟨2960873, by rfl⟩ : syracuseStep 3947831 = 5921747) B5921747
theorem B1973801 : Blo 1168401 1973801 := bstep (se 2 (by rfl) ⟨740175, by rfl⟩ : syracuseStep 1973801 = 1480351) B1480351
theorem B15998573 : Blo 1168401 15998573 := bstep (se 3 (by rfl) ⟨2999732, by rfl⟩ : syracuseStep 15998573 = 5999465) B5999465
theorem B1752767 : Blo 1168401 1752767 := bstep (se 1 (by rfl) ⟨1314575, by rfl⟩ : syracuseStep 1752767 = 2629151) B2629151
theorem B1973983 : Blo 1168401 1973983 := bstep (se 1 (by rfl) ⟨1480487, by rfl⟩ : syracuseStep 1973983 = 2960975) B2960975
theorem B3948371 : Blo 1168401 3948371 := bstep (se 1 (by rfl) ⟨2961278, by rfl⟩ : syracuseStep 3948371 = 5922557) B5922557
theorem B2703455 : Blo 1168401 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B2220223 : Blo 1168401 2220223 := bstep (se 1 (by rfl) ⟨1665167, by rfl⟩ : syracuseStep 2220223 = 3330335) B3330335
theorem B9478367 : Blo 1168401 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B2629871 : Blo 1168401 2629871 := bstep (se 1 (by rfl) ⟨1972403, by rfl⟩ : syracuseStep 2629871 = 3944807) B3944807
theorem B12009971 : Blo 1168401 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B5997331 : Blo 1168401 5997331 := bstep (se 1 (by rfl) ⟨4497998, by rfl⟩ : syracuseStep 5997331 = 8995997) B8995997
theorem B1753883 : Blo 1168401 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B1753919 : Blo 1168401 1753919 := bstep (se 1 (by rfl) ⟨1315439, by rfl⟩ : syracuseStep 1753919 = 2630879) B2630879
theorem B2630591 : Blo 1168401 2630591 := bstep (se 1 (by rfl) ⟨1972943, by rfl⟩ : syracuseStep 2630591 = 3945887) B3945887
theorem B1754063 : Blo 1168401 1754063 := bstep (se 1 (by rfl) ⟨1315547, by rfl⟩ : syracuseStep 1754063 = 2631095) B2631095
theorem B24020027 : Blo 1168401 24020027 := bstep (se 1 (by rfl) ⟨18015020, by rfl⟩ : syracuseStep 24020027 = 36030041) B36030041
theorem B2631275 : Blo 1168401 2631275 := bstep (se 1 (by rfl) ⟨1973456, by rfl⟩ : syracuseStep 2631275 = 3946913) B3946913
theorem B15181879 : Blo 1168401 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B2631743 : Blo 1168401 2631743 := bstep (se 1 (by rfl) ⟨1973807, by rfl⟩ : syracuseStep 2631743 = 3947615) B3947615
theorem B5621881 : Blo 1168401 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B2631887 : Blo 1168401 2631887 := bstep (se 1 (by rfl) ⟨1973915, by rfl⟩ : syracuseStep 2631887 = 3947831) B3947831
theorem B2631977 : Blo 1168401 2631977 := bstep (se 2 (by rfl) ⟨986991, by rfl⟩ : syracuseStep 2631977 = 1973983) B1973983
theorem B9996641 : Blo 1168401 9996641 := bstep (se 2 (by rfl) ⟨3748740, by rfl⟩ : syracuseStep 9996641 = 7497481) B7497481
theorem B2632247 : Blo 1168401 2632247 := bstep (se 1 (by rfl) ⟨1974185, by rfl⟩ : syracuseStep 2632247 = 3948371) B3948371
theorem B2632427 : Blo 1168401 2632427 := bstep (se 1 (by rfl) ⟨1974320, by rfl⟩ : syracuseStep 2632427 = 3948641) B3948641
theorem B3746665 : Blo 1168401 3746665 := bstep (se 2 (by rfl) ⟨1404999, by rfl⟩ : syracuseStep 3746665 = 2809999) B2809999
theorem B2632553 : Blo 1168401 2632553 := bstep (se 2 (by rfl) ⟨987207, by rfl⟩ : syracuseStep 2632553 = 1974415) B1974415
theorem B22473611 : Blo 1168401 22473611 := bstep (se 1 (by rfl) ⟨16855208, by rfl⟩ : syracuseStep 22473611 = 33710417) B33710417
theorem B56905193 : Blo 1168401 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B3944159 : Blo 1168401 3944159 := bstep (se 1 (by rfl) ⟨2958119, by rfl⟩ : syracuseStep 3944159 = 5916239) B5916239
theorem B8884079 : Blo 1168401 8884079 := bstep (se 1 (by rfl) ⟨6663059, by rfl⟩ : syracuseStep 8884079 = 13326119) B13326119
theorem B22777807 : Blo 1168401 22777807 := bstep (se 1 (by rfl) ⟨17083355, by rfl⟩ : syracuseStep 22777807 = 34166711) B34166711
theorem B4214855 : Blo 1168401 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B18976841 : Blo 1168401 18976841 := bstep (se 2 (by rfl) ⟨7116315, by rfl⟩ : syracuseStep 18976841 = 14232631) B14232631
theorem B3330551 : Blo 1168401 3330551 := bstep (se 1 (by rfl) ⟨2497913, by rfl⟩ : syracuseStep 3330551 = 4995827) B4995827
theorem B3945185 : Blo 1168401 3945185 := bstep (se 2 (by rfl) ⟨1479444, by rfl⟩ : syracuseStep 3945185 = 2958889) B2958889
theorem B1315867 : Blo 1168401 1315867 := bstep (se 1 (by rfl) ⟨986900, by rfl⟩ : syracuseStep 1315867 = 1973801) B1973801
theorem B1168511 : Blo 1168401 1168511 := bstep (se 1 (by rfl) ⟨876383, by rfl⟩ : syracuseStep 1168511 = 1752767) B1752767
theorem B4437119 : Blo 1168401 4437119 := bstep (se 1 (by rfl) ⟨3327839, by rfl⟩ : syracuseStep 4437119 = 6655679) B6655679
theorem B1168767 : Blo 1168401 1168767 := bstep (se 1 (by rfl) ⟨876575, by rfl⟩ : syracuseStep 1168767 = 1753151) B1753151
theorem B1168923 : Blo 1168401 1168923 := bstep (se 1 (by rfl) ⟨876692, by rfl⟩ : syracuseStep 1168923 = 1753385) B1753385
theorem B1480295 : Blo 1168401 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B1169263 : Blo 1168401 1169263 := bstep (se 1 (by rfl) ⟨876947, by rfl⟩ : syracuseStep 1169263 = 1753895) B1753895
theorem B4216873 : Blo 1168401 4216873 := bstep (se 2 (by rfl) ⟨1581327, by rfl⟩ : syracuseStep 4216873 = 3162655) B3162655
theorem B4741193 : Blo 1168401 4741193 := bstep (se 2 (by rfl) ⟨1777947, by rfl⟩ : syracuseStep 4741193 = 3555895) B3555895
theorem B1480943 : Blo 1168401 1480943 := bstep (se 1 (by rfl) ⟨1110707, by rfl⟩ : syracuseStep 1480943 = 2221415) B2221415
theorem B1169855 : Blo 1168401 1169855 := bstep (se 1 (by rfl) ⟨877391, by rfl⟩ : syracuseStep 1169855 = 1754783) B1754783
theorem B7592399 : Blo 1168401 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B1170151 : Blo 1168401 1170151 := bstep (se 1 (by rfl) ⟨877613, by rfl⟩ : syracuseStep 1170151 = 1755227) B1755227
theorem B1170175 : Blo 1168401 1170175 := bstep (se 1 (by rfl) ⟨877631, by rfl⟩ : syracuseStep 1170175 = 1755263) B1755263
theorem B4996511 : Blo 1168401 4996511 := bstep (se 1 (by rfl) ⟨3747383, by rfl⟩ : syracuseStep 4996511 = 7494767) B7494767
theorem B2219471 : Blo 1168401 2219471 := bstep (se 1 (by rfl) ⟨1664603, by rfl⟩ : syracuseStep 2219471 = 3329207) B3329207
theorem B1752713 : Blo 1168401 1752713 := bstep (se 2 (by rfl) ⟨657267, by rfl⟩ : syracuseStep 1752713 = 1314535) B1314535
theorem B10665715 : Blo 1168401 10665715 := bstep (se 1 (by rfl) ⟨7999286, by rfl⟩ : syracuseStep 10665715 = 15998573) B15998573
theorem B2809903 : Blo 1168401 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B1802303 : Blo 1168401 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B20242505 : Blo 1168401 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B1753247 : Blo 1168401 1753247 := bstep (se 1 (by rfl) ⟨1314935, by rfl⟩ : syracuseStep 1753247 = 2629871) B2629871
theorem B7495841 : Blo 1168401 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B2220367 : Blo 1168401 2220367 := bstep (se 1 (by rfl) ⟨1665275, by rfl⟩ : syracuseStep 2220367 = 3330551) B3330551
theorem B2630123 : Blo 1168401 2630123 := bstep (se 1 (by rfl) ⟨1972592, by rfl⟩ : syracuseStep 2630123 = 3945185) B3945185
theorem B3949181 : Blo 1168401 3949181 := bstep (se 3 (by rfl) ⟨740471, by rfl⟩ : syracuseStep 3949181 = 1480943) B1480943
theorem B1753727 : Blo 1168401 1753727 := bstep (se 1 (by rfl) ⟨1315295, by rfl⟩ : syracuseStep 1753727 = 2630591) B2630591
theorem B2958079 : Blo 1168401 2958079 := bstep (se 1 (by rfl) ⟨2218559, by rfl⟩ : syracuseStep 2958079 = 4437119) B4437119
theorem B1754183 : Blo 1168401 1754183 := bstep (se 1 (by rfl) ⟨1315637, by rfl⟩ : syracuseStep 1754183 = 2631275) B2631275
theorem B1754489 : Blo 1168401 1754489 := bstep (se 2 (by rfl) ⟨657933, by rfl⟩ : syracuseStep 1754489 = 1315867) B1315867
theorem B1754495 : Blo 1168401 1754495 := bstep (se 1 (by rfl) ⟨1315871, by rfl⟩ : syracuseStep 1754495 = 2631743) B2631743
theorem B1754591 : Blo 1168401 1754591 := bstep (se 1 (by rfl) ⟨1315943, by rfl⟩ : syracuseStep 1754591 = 2631887) B2631887
theorem B1754651 : Blo 1168401 1754651 := bstep (se 1 (by rfl) ⟨1315988, by rfl⟩ : syracuseStep 1754651 = 2631977) B2631977
theorem B1754831 : Blo 1168401 1754831 := bstep (se 1 (by rfl) ⟨1316123, by rfl⟩ : syracuseStep 1754831 = 2632247) B2632247
theorem B1754951 : Blo 1168401 1754951 := bstep (se 1 (by rfl) ⟨1316213, by rfl⟩ : syracuseStep 1754951 = 2632427) B2632427
theorem B1755035 : Blo 1168401 1755035 := bstep (se 1 (by rfl) ⟨1316276, by rfl⟩ : syracuseStep 1755035 = 2632553) B2632553
theorem B30370409 : Blo 1168401 30370409 := bstep (se 2 (by rfl) ⟨11388903, by rfl⟩ : syracuseStep 30370409 = 22777807) B22777807
theorem B12651227 : Blo 1168401 12651227 := bstep (se 1 (by rfl) ⟨9488420, by rfl⟩ : syracuseStep 12651227 = 18976841) B18976841
theorem B5622497 : Blo 1168401 5622497 := bstep (se 2 (by rfl) ⟨2108436, by rfl⟩ : syracuseStep 5622497 = 4216873) B4216873
theorem B6318911 : Blo 1168401 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B2960297 : Blo 1168401 2960297 := bstep (se 2 (by rfl) ⟨1110111, by rfl⟩ : syracuseStep 2960297 = 2220223) B2220223
theorem B32026589 : Blo 1168401 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B31985765 : Blo 1168401 31985765 := bstep (se 4 (by rfl) ⟨2998665, by rfl⟩ : syracuseStep 31985765 = 5997331) B5997331
theorem B6664427 : Blo 1168401 6664427 := bstep (se 1 (by rfl) ⟨4998320, by rfl⟩ : syracuseStep 6664427 = 9996641) B9996641
theorem B3331007 : Blo 1168401 3331007 := bstep (se 1 (by rfl) ⟨2498255, by rfl⟩ : syracuseStep 3331007 = 4996511) B4996511
theorem B1479647 : Blo 1168401 1479647 := bstep (se 1 (by rfl) ⟨1109735, by rfl⟩ : syracuseStep 1479647 = 2219471) B2219471
theorem B1168475 : Blo 1168401 1168475 := bstep (se 1 (by rfl) ⟨876356, by rfl⟩ : syracuseStep 1168475 = 1752713) B1752713
theorem B1169255 : Blo 1168401 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B1169279 : Blo 1168401 1169279 := bstep (se 1 (by rfl) ⟨876959, by rfl⟩ : syracuseStep 1169279 = 1753919) B1753919
theorem B1169375 : Blo 1168401 1169375 := bstep (se 1 (by rfl) ⟨877031, by rfl⟩ : syracuseStep 1169375 = 1754063) B1754063
theorem B16013351 : Blo 1168401 16013351 := bstep (se 1 (by rfl) ⟨12010013, by rfl⟩ : syracuseStep 16013351 = 24020027) B24020027
theorem B4995553 : Blo 1168401 4995553 := bstep (se 2 (by rfl) ⟨1873332, by rfl⟩ : syracuseStep 4995553 = 3746665) B3746665
theorem B3160795 : Blo 1168401 3160795 := bstep (se 1 (by rfl) ⟨2370596, by rfl⟩ : syracuseStep 3160795 = 4741193) B4741193
theorem B3947453 : Blo 1168401 3947453 := bstep (se 3 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 3947453 = 1480295) B1480295
theorem B5061599 : Blo 1168401 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B14982407 : Blo 1168401 14982407 := bstep (se 1 (by rfl) ⟨11236805, by rfl⟩ : syracuseStep 14982407 = 22473611) B22473611
theorem B14220953 : Blo 1168401 14220953 := bstep (se 2 (by rfl) ⟨5332857, by rfl⟩ : syracuseStep 14220953 = 10665715) B10665715
theorem B37936795 : Blo 1168401 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B2629439 : Blo 1168401 2629439 := bstep (se 1 (by rfl) ⟨1972079, by rfl⟩ : syracuseStep 2629439 = 3944159) B3944159
theorem B5922719 : Blo 1168401 5922719 := bstep (se 1 (by rfl) ⟨4442039, by rfl⟩ : syracuseStep 5922719 = 8884079) B8884079
theorem B21323843 : Blo 1168401 21323843 := bstep (se 1 (by rfl) ⟨15992882, by rfl⟩ : syracuseStep 21323843 = 31985765) B31985765
theorem B4997227 : Blo 1168401 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B1753415 : Blo 1168401 1753415 := bstep (se 1 (by rfl) ⟨1315061, by rfl⟩ : syracuseStep 1753415 = 2630123) B2630123
theorem B6660737 : Blo 1168401 6660737 := bstep (se 2 (by rfl) ⟨2497776, by rfl⟩ : syracuseStep 6660737 = 4995553) B4995553
theorem B2220671 : Blo 1168401 2220671 := bstep (se 1 (by rfl) ⟨1665503, by rfl⟩ : syracuseStep 2220671 = 3331007) B3331007
theorem B10675567 : Blo 1168401 10675567 := bstep (se 1 (by rfl) ⟨8006675, by rfl⟩ : syracuseStep 10675567 = 16013351) B16013351
theorem B4212607 : Blo 1168401 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B2631635 : Blo 1168401 2631635 := bstep (se 1 (by rfl) ⟨1973726, by rfl⟩ : syracuseStep 2631635 = 3947453) B3947453
theorem B9988271 : Blo 1168401 9988271 := bstep (se 1 (by rfl) ⟨7491203, by rfl⟩ : syracuseStep 9988271 = 14982407) B14982407
theorem B9480635 : Blo 1168401 9480635 := bstep (se 1 (by rfl) ⟨7110476, by rfl⟩ : syracuseStep 9480635 = 14220953) B14220953
theorem B21351059 : Blo 1168401 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B3746537 : Blo 1168401 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B4442951 : Blo 1168401 4442951 := bstep (se 1 (by rfl) ⟨3332213, by rfl⟩ : syracuseStep 4442951 = 6664427) B6664427
theorem B53980013 : Blo 1168401 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B2632787 : Blo 1168401 2632787 := bstep (se 1 (by rfl) ⟨1974590, by rfl⟩ : syracuseStep 2632787 = 3949181) B3949181
theorem B2960489 : Blo 1168401 2960489 := bstep (se 2 (by rfl) ⟨1110183, by rfl⟩ : syracuseStep 2960489 = 2220367) B2220367
theorem B4214393 : Blo 1168401 4214393 := bstep (se 2 (by rfl) ⟨1580397, by rfl⟩ : syracuseStep 4214393 = 3160795) B3160795
theorem B3944105 : Blo 1168401 3944105 := bstep (se 2 (by rfl) ⟨1479039, by rfl⟩ : syracuseStep 3944105 = 2958079) B2958079
theorem B20246939 : Blo 1168401 20246939 := bstep (se 1 (by rfl) ⟨15185204, by rfl⟩ : syracuseStep 20246939 = 30370409) B30370409
theorem B8434151 : Blo 1168401 8434151 := bstep (se 1 (by rfl) ⟨6325613, by rfl⟩ : syracuseStep 8434151 = 12651227) B12651227
theorem B3748331 : Blo 1168401 3748331 := bstep (se 1 (by rfl) ⟨2811248, by rfl⟩ : syracuseStep 3748331 = 5622497) B5622497
theorem B50582393 : Blo 1168401 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B3945725 : Blo 1168401 3945725 := bstep (se 3 (by rfl) ⟨739823, by rfl⟩ : syracuseStep 3945725 = 1479647) B1479647
theorem B1201535 : Blo 1168401 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1168831 : Blo 1168401 1168831 := bstep (se 1 (by rfl) ⟨876623, by rfl⟩ : syracuseStep 1168831 = 1753247) B1753247
theorem B1169151 : Blo 1168401 1169151 := bstep (se 1 (by rfl) ⟨876863, by rfl⟩ : syracuseStep 1169151 = 1753727) B1753727
theorem B1169455 : Blo 1168401 1169455 := bstep (se 1 (by rfl) ⟨877091, by rfl⟩ : syracuseStep 1169455 = 1754183) B1754183
theorem B1169659 : Blo 1168401 1169659 := bstep (se 1 (by rfl) ⟨877244, by rfl⟩ : syracuseStep 1169659 = 1754489) B1754489
theorem B1169663 : Blo 1168401 1169663 := bstep (se 1 (by rfl) ⟨877247, by rfl⟩ : syracuseStep 1169663 = 1754495) B1754495
theorem B1169727 : Blo 1168401 1169727 := bstep (se 1 (by rfl) ⟨877295, by rfl⟩ : syracuseStep 1169727 = 1754591) B1754591
theorem B1169767 : Blo 1168401 1169767 := bstep (se 1 (by rfl) ⟨877325, by rfl⟩ : syracuseStep 1169767 = 1754651) B1754651
theorem B1169887 : Blo 1168401 1169887 := bstep (se 1 (by rfl) ⟨877415, by rfl⟩ : syracuseStep 1169887 = 1754831) B1754831
theorem B1169967 : Blo 1168401 1169967 := bstep (se 1 (by rfl) ⟨877475, by rfl⟩ : syracuseStep 1169967 = 1754951) B1754951
theorem B1170023 : Blo 1168401 1170023 := bstep (se 1 (by rfl) ⟨877517, by rfl⟩ : syracuseStep 1170023 = 1755035) B1755035
theorem B1973531 : Blo 1168401 1973531 := bstep (se 1 (by rfl) ⟨1480148, by rfl⟩ : syracuseStep 1973531 = 2960297) B2960297
theorem B3374399 : Blo 1168401 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B1752959 : Blo 1168401 1752959 := bstep (se 1 (by rfl) ⟨1314719, by rfl⟩ : syracuseStep 1752959 = 2629439) B2629439
theorem B3948479 : Blo 1168401 3948479 := bstep (se 1 (by rfl) ⟨2961359, by rfl⟩ : syracuseStep 3948479 = 5922719) B5922719
theorem B2498887 : Blo 1168401 2498887 := bstep (se 1 (by rfl) ⟨1874165, by rfl⟩ : syracuseStep 2498887 = 3748331) B3748331
theorem B4440491 : Blo 1168401 4440491 := bstep (se 1 (by rfl) ⟨3330368, by rfl⟩ : syracuseStep 4440491 = 6660737) B6660737
theorem B2630483 : Blo 1168401 2630483 := bstep (se 1 (by rfl) ⟨1972862, by rfl⟩ : syracuseStep 2630483 = 3945725) B3945725
theorem B1754423 : Blo 1168401 1754423 := bstep (se 1 (by rfl) ⟨1315817, by rfl⟩ : syracuseStep 1754423 = 2631635) B2631635
theorem B1755191 : Blo 1168401 1755191 := bstep (se 1 (by rfl) ⟨1316393, by rfl⟩ : syracuseStep 1755191 = 2632787) B2632787
theorem B2632319 : Blo 1168401 2632319 := bstep (se 1 (by rfl) ⟨1974239, by rfl⟩ : syracuseStep 2632319 = 3948479) B3948479
theorem B14215895 : Blo 1168401 14215895 := bstep (se 1 (by rfl) ⟨10661921, by rfl⟩ : syracuseStep 14215895 = 21323843) B21323843
theorem B6662969 : Blo 1168401 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B5622767 : Blo 1168401 5622767 := bstep (se 1 (by rfl) ⟨4217075, by rfl⟩ : syracuseStep 5622767 = 8434151) B8434151
theorem B33721595 : Blo 1168401 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B8998397 : Blo 1168401 8998397 := bstep (se 3 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 8998397 = 3374399) B3374399
theorem B12816373 : Blo 1168401 12816373 := bstep (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) B1201535
theorem B6320423 : Blo 1168401 6320423 := bstep (se 1 (by rfl) ⟨4740317, by rfl⟩ : syracuseStep 6320423 = 9480635) B9480635
theorem B14234039 : Blo 1168401 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B14234089 : Blo 1168401 14234089 := bstep (se 2 (by rfl) ⟨5337783, by rfl⟩ : syracuseStep 14234089 = 10675567) B10675567
theorem B2961967 : Blo 1168401 2961967 := bstep (se 1 (by rfl) ⟨2221475, by rfl⟩ : syracuseStep 2961967 = 4442951) B4442951
theorem B1315687 : Blo 1168401 1315687 := bstep (se 1 (by rfl) ⟨986765, by rfl⟩ : syracuseStep 1315687 = 1973531) B1973531
theorem B5616809 : Blo 1168401 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B1168639 : Blo 1168401 1168639 := bstep (se 1 (by rfl) ⟨876479, by rfl⟩ : syracuseStep 1168639 = 1752959) B1752959
theorem B1168943 : Blo 1168401 1168943 := bstep (se 1 (by rfl) ⟨876707, by rfl⟩ : syracuseStep 1168943 = 1753415) B1753415
theorem B13497959 : Blo 1168401 13497959 := bstep (se 1 (by rfl) ⟨10123469, by rfl⟩ : syracuseStep 13497959 = 20246939) B20246939
theorem B1480447 : Blo 1168401 1480447 := bstep (se 1 (by rfl) ⟨1110335, by rfl⟩ : syracuseStep 1480447 = 2220671) B2220671
theorem B6658847 : Blo 1168401 6658847 := bstep (se 1 (by rfl) ⟨4994135, by rfl⟩ : syracuseStep 6658847 = 9988271) B9988271
theorem B2497691 : Blo 1168401 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B35986675 : Blo 1168401 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B1973659 : Blo 1168401 1973659 := bstep (se 1 (by rfl) ⟨1480244, by rfl⟩ : syracuseStep 1973659 = 2960489) B2960489
theorem B2809595 : Blo 1168401 2809595 := bstep (se 1 (by rfl) ⟨2107196, by rfl⟩ : syracuseStep 2809595 = 4214393) B4214393
theorem B2629403 : Blo 1168401 2629403 := bstep (se 1 (by rfl) ⟨1972052, by rfl⟩ : syracuseStep 2629403 = 3944105) B3944105
theorem B1753655 : Blo 1168401 1753655 := bstep (se 1 (by rfl) ⟨1315241, by rfl⟩ : syracuseStep 1753655 = 2630483) B2630483
theorem B3949289 : Blo 1168401 3949289 := bstep (se 2 (by rfl) ⟨1480983, by rfl⟩ : syracuseStep 3949289 = 2961967) B2961967
theorem B3744539 : Blo 1168401 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B1754249 : Blo 1168401 1754249 := bstep (se 2 (by rfl) ⟨657843, by rfl⟩ : syracuseStep 1754249 = 1315687) B1315687
theorem B47982233 : Blo 1168401 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B1754879 : Blo 1168401 1754879 := bstep (se 1 (by rfl) ⟨1316159, by rfl⟩ : syracuseStep 1754879 = 2632319) B2632319
theorem B2631545 : Blo 1168401 2631545 := bstep (se 2 (by rfl) ⟨986829, by rfl⟩ : syracuseStep 2631545 = 1973659) B1973659
theorem B4441979 : Blo 1168401 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1665127 : Blo 1168401 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B22481063 : Blo 1168401 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B5998931 : Blo 1168401 5998931 := bstep (se 1 (by rfl) ⟨4499198, by rfl⟩ : syracuseStep 5998931 = 8998397) B8998397
theorem B4213615 : Blo 1168401 4213615 := bstep (se 1 (by rfl) ⟨3160211, by rfl⟩ : syracuseStep 4213615 = 6320423) B6320423
theorem B2960327 : Blo 1168401 2960327 := bstep (se 1 (by rfl) ⟨2220245, by rfl⟩ : syracuseStep 2960327 = 4440491) B4440491
theorem B9489359 : Blo 1168401 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B3748511 : Blo 1168401 3748511 := bstep (se 1 (by rfl) ⟨2811383, by rfl⟩ : syracuseStep 3748511 = 5622767) B5622767
theorem B1873063 : Blo 1168401 1873063 := bstep (se 1 (by rfl) ⟨1404797, by rfl⟩ : syracuseStep 1873063 = 2809595) B2809595
theorem B3331849 : Blo 1168401 3331849 := bstep (se 2 (by rfl) ⟨1249443, by rfl⟩ : syracuseStep 3331849 = 2498887) B2498887
theorem B18978785 : Blo 1168401 18978785 := bstep (se 2 (by rfl) ⟨7117044, by rfl⟩ : syracuseStep 18978785 = 14234089) B14234089
theorem B1169615 : Blo 1168401 1169615 := bstep (se 1 (by rfl) ⟨877211, by rfl⟩ : syracuseStep 1169615 = 1754423) B1754423
theorem B1170127 : Blo 1168401 1170127 := bstep (se 1 (by rfl) ⟨877595, by rfl⟩ : syracuseStep 1170127 = 1755191) B1755191
theorem B35994557 : Blo 1168401 35994557 := bstep (se 3 (by rfl) ⟨6748979, by rfl⟩ : syracuseStep 35994557 = 13497959) B13497959
theorem B9477263 : Blo 1168401 9477263 := bstep (se 1 (by rfl) ⟨7107947, by rfl⟩ : syracuseStep 9477263 = 14215895) B14215895
theorem B4439231 : Blo 1168401 4439231 := bstep (se 1 (by rfl) ⟨3329423, by rfl⟩ : syracuseStep 4439231 = 6658847) B6658847
theorem B1973929 : Blo 1168401 1973929 := bstep (se 2 (by rfl) ⟨740223, by rfl⟩ : syracuseStep 1973929 = 1480447) B1480447
theorem B1752935 : Blo 1168401 1752935 := bstep (se 1 (by rfl) ⟨1314701, by rfl⟩ : syracuseStep 1752935 = 2629403) B2629403
theorem B17088497 : Blo 1168401 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B2499007 : Blo 1168401 2499007 := bstep (se 1 (by rfl) ⟨1874255, by rfl⟩ : syracuseStep 2499007 = 3748511) B3748511
theorem B8880677 : Blo 1168401 8880677 := bstep (se 4 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 8880677 = 1665127) B1665127
theorem B1754363 : Blo 1168401 1754363 := bstep (se 1 (by rfl) ⟨1315772, by rfl⟩ : syracuseStep 1754363 = 2631545) B2631545
theorem B3999287 : Blo 1168401 3999287 := bstep (se 1 (by rfl) ⟨2999465, by rfl⟩ : syracuseStep 3999287 = 5998931) B5998931
theorem B127952621 : Blo 1168401 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B6318175 : Blo 1168401 6318175 := bstep (se 1 (by rfl) ⟨4738631, by rfl⟩ : syracuseStep 6318175 = 9477263) B9477263
theorem B2959487 : Blo 1168401 2959487 := bstep (se 1 (by rfl) ⟨2219615, by rfl⟩ : syracuseStep 2959487 = 4439231) B4439231
theorem B2631905 : Blo 1168401 2631905 := bstep (se 2 (by rfl) ⟨986964, by rfl⟩ : syracuseStep 2631905 = 1973929) B1973929
theorem B4442465 : Blo 1168401 4442465 := bstep (se 2 (by rfl) ⟨1665924, by rfl⟩ : syracuseStep 4442465 = 3331849) B3331849
theorem B2632859 : Blo 1168401 2632859 := bstep (se 1 (by rfl) ⟨1974644, by rfl⟩ : syracuseStep 2632859 = 3949289) B3949289
theorem B9989669 : Blo 1168401 9989669 := bstep (se 4 (by rfl) ⟨936531, by rfl⟩ : syracuseStep 9989669 = 1873063) B1873063
theorem B2961319 : Blo 1168401 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B12652523 : Blo 1168401 12652523 := bstep (se 1 (by rfl) ⟨9489392, by rfl⟩ : syracuseStep 12652523 = 18978785) B18978785
theorem B14987375 : Blo 1168401 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B1168623 : Blo 1168401 1168623 := bstep (se 1 (by rfl) ⟨876467, by rfl⟩ : syracuseStep 1168623 = 1752935) B1752935
theorem B11392331 : Blo 1168401 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B1169103 : Blo 1168401 1169103 := bstep (se 1 (by rfl) ⟨876827, by rfl⟩ : syracuseStep 1169103 = 1753655) B1753655
theorem B2496359 : Blo 1168401 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B1169499 : Blo 1168401 1169499 := bstep (se 1 (by rfl) ⟨877124, by rfl⟩ : syracuseStep 1169499 = 1754249) B1754249
theorem B5618153 : Blo 1168401 5618153 := bstep (se 2 (by rfl) ⟨2106807, by rfl⟩ : syracuseStep 5618153 = 4213615) B4213615
theorem B1169919 : Blo 1168401 1169919 := bstep (se 1 (by rfl) ⟨877439, by rfl⟩ : syracuseStep 1169919 = 1754879) B1754879
theorem B1973551 : Blo 1168401 1973551 := bstep (se 1 (by rfl) ⟨1480163, by rfl⟩ : syracuseStep 1973551 = 2960327) B2960327
theorem B95985485 : Blo 1168401 95985485 := bstep (se 3 (by rfl) ⟨17997278, by rfl⟩ : syracuseStep 95985485 = 35994557) B35994557
theorem B25304957 : Blo 1168401 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B1664239 : Blo 1168401 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B1754603 : Blo 1168401 1754603 := bstep (se 1 (by rfl) ⟨1315952, by rfl⟩ : syracuseStep 1754603 = 2631905) B2631905
theorem B3745435 : Blo 1168401 3745435 := bstep (se 1 (by rfl) ⟨2809076, by rfl⟩ : syracuseStep 3745435 = 5618153) B5618153
theorem B2631401 : Blo 1168401 2631401 := bstep (se 2 (by rfl) ⟨986775, by rfl⟩ : syracuseStep 2631401 = 1973551) B1973551
theorem B1755239 : Blo 1168401 1755239 := bstep (se 1 (by rfl) ⟨1316429, by rfl⟩ : syracuseStep 1755239 = 2632859) B2632859
theorem B63990323 : Blo 1168401 63990323 := bstep (se 1 (by rfl) ⟨47992742, by rfl⟩ : syracuseStep 63990323 = 95985485) B95985485
theorem B16869971 : Blo 1168401 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B8424233 : Blo 1168401 8424233 := bstep (se 2 (by rfl) ⟨3159087, by rfl⟩ : syracuseStep 8424233 = 6318175) B6318175
theorem B30379549 : Blo 1168401 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B2666191 : Blo 1168401 2666191 := bstep (se 1 (by rfl) ⟨1999643, by rfl⟩ : syracuseStep 2666191 = 3999287) B3999287
theorem B2961643 : Blo 1168401 2961643 := bstep (se 1 (by rfl) ⟨2221232, by rfl⟩ : syracuseStep 2961643 = 4442465) B4442465
theorem B8435015 : Blo 1168401 8435015 := bstep (se 1 (by rfl) ⟨6326261, by rfl⟩ : syracuseStep 8435015 = 12652523) B12652523
theorem B9991583 : Blo 1168401 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B5920451 : Blo 1168401 5920451 := bstep (se 1 (by rfl) ⟨4440338, by rfl⟩ : syracuseStep 5920451 = 8880677) B8880677
theorem B3332009 : Blo 1168401 3332009 := bstep (se 2 (by rfl) ⟨1249503, by rfl⟩ : syracuseStep 3332009 = 2499007) B2499007
theorem B1169575 : Blo 1168401 1169575 := bstep (se 1 (by rfl) ⟨877181, by rfl⟩ : syracuseStep 1169575 = 1754363) B1754363
theorem B85301747 : Blo 1168401 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B1972991 : Blo 1168401 1972991 := bstep (se 1 (by rfl) ⟨1479743, by rfl⟩ : syracuseStep 1972991 = 2959487) B2959487
theorem B6659779 : Blo 1168401 6659779 := bstep (se 1 (by rfl) ⟨4994834, by rfl⟩ : syracuseStep 6659779 = 9989669) B9989669
theorem B3948425 : Blo 1168401 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B3948857 : Blo 1168401 3948857 := bstep (se 2 (by rfl) ⟨1480821, by rfl⟩ : syracuseStep 3948857 = 2961643) B2961643
theorem B6661055 : Blo 1168401 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B1754267 : Blo 1168401 1754267 := bstep (se 1 (by rfl) ⟨1315700, by rfl⟩ : syracuseStep 1754267 = 2631401) B2631401
theorem B2221339 : Blo 1168401 2221339 := bstep (se 1 (by rfl) ⟨1666004, by rfl⟩ : syracuseStep 2221339 = 3332009) B3332009
theorem B2632283 : Blo 1168401 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B5623343 : Blo 1168401 5623343 := bstep (se 1 (by rfl) ⟨4217507, by rfl⟩ : syracuseStep 5623343 = 8435015) B8435015
theorem B42660215 : Blo 1168401 42660215 := bstep (se 1 (by rfl) ⟨31995161, by rfl⟩ : syracuseStep 42660215 = 63990323) B63990323
theorem B1315327 : Blo 1168401 1315327 := bstep (se 1 (by rfl) ⟨986495, by rfl⟩ : syracuseStep 1315327 = 1972991) B1972991
theorem B5616155 : Blo 1168401 5616155 := bstep (se 1 (by rfl) ⟨4212116, by rfl⟩ : syracuseStep 5616155 = 8424233) B8424233
theorem B40506065 : Blo 1168401 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B4993913 : Blo 1168401 4993913 := bstep (se 2 (by rfl) ⟨1872717, by rfl⟩ : syracuseStep 4993913 = 3745435) B3745435
theorem B1169735 : Blo 1168401 1169735 := bstep (se 1 (by rfl) ⟨877301, by rfl⟩ : syracuseStep 1169735 = 1754603) B1754603
theorem B3946967 : Blo 1168401 3946967 := bstep (se 1 (by rfl) ⟨2960225, by rfl⟩ : syracuseStep 3946967 = 5920451) B5920451
theorem B1170159 : Blo 1168401 1170159 := bstep (se 1 (by rfl) ⟨877619, by rfl⟩ : syracuseStep 1170159 = 1755239) B1755239
theorem B2218985 : Blo 1168401 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B56867831 : Blo 1168401 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B11246647 : Blo 1168401 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B8879705 : Blo 1168401 8879705 := bstep (se 2 (by rfl) ⟨3329889, by rfl⟩ : syracuseStep 8879705 = 6659779) B6659779
theorem B3554921 : Blo 1168401 3554921 := bstep (se 2 (by rfl) ⟨1333095, by rfl⟩ : syracuseStep 3554921 = 2666191) B2666191
theorem B3744103 : Blo 1168401 3744103 := bstep (se 1 (by rfl) ⟨2808077, by rfl⟩ : syracuseStep 3744103 = 5616155) B5616155
theorem B4440703 : Blo 1168401 4440703 := bstep (se 1 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 4440703 = 6661055) B6661055
theorem B1753769 : Blo 1168401 1753769 := bstep (se 2 (by rfl) ⟨657663, by rfl⟩ : syracuseStep 1753769 = 1315327) B1315327
theorem B2631311 : Blo 1168401 2631311 := bstep (se 1 (by rfl) ⟨1973483, by rfl⟩ : syracuseStep 2631311 = 3946967) B3946967
theorem B1754855 : Blo 1168401 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B2369947 : Blo 1168401 2369947 := bstep (se 1 (by rfl) ⟨1777460, by rfl⟩ : syracuseStep 2369947 = 3554921) B3554921
theorem B2632571 : Blo 1168401 2632571 := bstep (se 1 (by rfl) ⟨1974428, by rfl⟩ : syracuseStep 2632571 = 3948857) B3948857
theorem B27004043 : Blo 1168401 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B3329275 : Blo 1168401 3329275 := bstep (se 1 (by rfl) ⟨2496956, by rfl⟩ : syracuseStep 3329275 = 4993913) B4993913
theorem B14995529 : Blo 1168401 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B2961785 : Blo 1168401 2961785 := bstep (se 2 (by rfl) ⟨1110669, by rfl⟩ : syracuseStep 2961785 = 2221339) B2221339
theorem B1479323 : Blo 1168401 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B3748895 : Blo 1168401 3748895 := bstep (se 1 (by rfl) ⟨2811671, by rfl⟩ : syracuseStep 3748895 = 5623343) B5623343
theorem B5919803 : Blo 1168401 5919803 := bstep (se 1 (by rfl) ⟨4439852, by rfl⟩ : syracuseStep 5919803 = 8879705) B8879705
theorem B28440143 : Blo 1168401 28440143 := bstep (se 1 (by rfl) ⟨21330107, by rfl⟩ : syracuseStep 28440143 = 42660215) B42660215
theorem B1169511 : Blo 1168401 1169511 := bstep (se 1 (by rfl) ⟨877133, by rfl⟩ : syracuseStep 1169511 = 1754267) B1754267
theorem B37911887 : Blo 1168401 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B1974523 : Blo 1168401 1974523 := bstep (se 1 (by rfl) ⟨1480892, by rfl⟩ : syracuseStep 1974523 = 2961785) B2961785
theorem B2499263 : Blo 1168401 2499263 := bstep (se 1 (by rfl) ⟨1874447, by rfl⟩ : syracuseStep 2499263 = 3748895) B3748895
theorem B1754207 : Blo 1168401 1754207 := bstep (se 1 (by rfl) ⟨1315655, by rfl⟩ : syracuseStep 1754207 = 2631311) B2631311
theorem B1755047 : Blo 1168401 1755047 := bstep (se 1 (by rfl) ⟨1316285, by rfl⟩ : syracuseStep 1755047 = 2632571) B2632571
theorem B25274591 : Blo 1168401 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B9997019 : Blo 1168401 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B72010781 : Blo 1168401 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B4992137 : Blo 1168401 4992137 := bstep (se 2 (by rfl) ⟨1872051, by rfl⟩ : syracuseStep 4992137 = 3744103) B3744103
theorem B18960095 : Blo 1168401 18960095 := bstep (se 1 (by rfl) ⟨14220071, by rfl⟩ : syracuseStep 18960095 = 28440143) B28440143
theorem B3944861 : Blo 1168401 3944861 := bstep (se 3 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 3944861 = 1479323) B1479323
theorem B1169179 : Blo 1168401 1169179 := bstep (se 1 (by rfl) ⟨876884, by rfl⟩ : syracuseStep 1169179 = 1753769) B1753769
theorem B3159929 : Blo 1168401 3159929 := bstep (se 2 (by rfl) ⟨1184973, by rfl⟩ : syracuseStep 3159929 = 2369947) B2369947
theorem B3946535 : Blo 1168401 3946535 := bstep (se 1 (by rfl) ⟨2959901, by rfl⟩ : syracuseStep 3946535 = 5919803) B5919803
theorem B5920937 : Blo 1168401 5920937 := bstep (se 2 (by rfl) ⟨2220351, by rfl⟩ : syracuseStep 5920937 = 4440703) B4440703
theorem B1169903 : Blo 1168401 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B4439033 : Blo 1168401 4439033 := bstep (se 2 (by rfl) ⟨1664637, by rfl⟩ : syracuseStep 4439033 = 3329275) B3329275
theorem B2629907 : Blo 1168401 2629907 := bstep (se 1 (by rfl) ⟨1972430, by rfl⟩ : syracuseStep 2629907 = 3944861) B3944861
theorem B2631023 : Blo 1168401 2631023 := bstep (se 1 (by rfl) ⟨1973267, by rfl⟩ : syracuseStep 2631023 = 3946535) B3946535
theorem B2959355 : Blo 1168401 2959355 := bstep (se 1 (by rfl) ⟨2219516, by rfl⟩ : syracuseStep 2959355 = 4439033) B4439033
theorem B48007187 : Blo 1168401 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B3328091 : Blo 1168401 3328091 := bstep (se 1 (by rfl) ⟨2496068, by rfl⟩ : syracuseStep 3328091 = 4992137) B4992137
theorem B2632697 : Blo 1168401 2632697 := bstep (se 2 (by rfl) ⟨987261, by rfl⟩ : syracuseStep 2632697 = 1974523) B1974523
theorem B1666175 : Blo 1168401 1666175 := bstep (se 1 (by rfl) ⟨1249631, by rfl⟩ : syracuseStep 1666175 = 2499263) B2499263
theorem B6664679 : Blo 1168401 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B8426477 : Blo 1168401 8426477 := bstep (se 3 (by rfl) ⟨1579964, by rfl⟩ : syracuseStep 8426477 = 3159929) B3159929
theorem B1169471 : Blo 1168401 1169471 := bstep (se 1 (by rfl) ⟨877103, by rfl⟩ : syracuseStep 1169471 = 1754207) B1754207
theorem B1170031 : Blo 1168401 1170031 := bstep (se 1 (by rfl) ⟨877523, by rfl⟩ : syracuseStep 1170031 = 1755047) B1755047
theorem B3947291 : Blo 1168401 3947291 := bstep (se 1 (by rfl) ⟨2960468, by rfl⟩ : syracuseStep 3947291 = 5920937) B5920937
theorem B16849727 : Blo 1168401 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B12640063 : Blo 1168401 12640063 := bstep (se 1 (by rfl) ⟨9480047, by rfl⟩ : syracuseStep 12640063 = 18960095) B18960095
theorem B1753271 : Blo 1168401 1753271 := bstep (se 1 (by rfl) ⟨1314953, by rfl⟩ : syracuseStep 1753271 = 2629907) B2629907
theorem B1754015 : Blo 1168401 1754015 := bstep (se 1 (by rfl) ⟨1315511, by rfl⟩ : syracuseStep 1754015 = 2631023) B2631023
theorem B2631527 : Blo 1168401 2631527 := bstep (se 1 (by rfl) ⟨1973645, by rfl⟩ : syracuseStep 2631527 = 3947291) B3947291
theorem B11233151 : Blo 1168401 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B1755131 : Blo 1168401 1755131 := bstep (se 1 (by rfl) ⟨1316348, by rfl⟩ : syracuseStep 1755131 = 2632697) B2632697
theorem B16853417 : Blo 1168401 16853417 := bstep (se 2 (by rfl) ⟨6320031, by rfl⟩ : syracuseStep 16853417 = 12640063) B12640063
theorem B4443119 : Blo 1168401 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B4443133 : Blo 1168401 4443133 := bstep (se 3 (by rfl) ⟨833087, by rfl⟩ : syracuseStep 4443133 = 1666175) B1666175
theorem B1972903 : Blo 1168401 1972903 := bstep (se 1 (by rfl) ⟨1479677, by rfl⟩ : syracuseStep 1972903 = 2959355) B2959355
theorem B32004791 : Blo 1168401 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B2218727 : Blo 1168401 2218727 := bstep (se 1 (by rfl) ⟨1664045, by rfl⟩ : syracuseStep 2218727 = 3328091) B3328091
theorem B22470605 : Blo 1168401 22470605 := bstep (se 3 (by rfl) ⟨4213238, by rfl⟩ : syracuseStep 22470605 = 8426477) B8426477
theorem B2630537 : Blo 1168401 2630537 := bstep (se 2 (by rfl) ⟨986451, by rfl⟩ : syracuseStep 2630537 = 1972903) B1972903
theorem B1754351 : Blo 1168401 1754351 := bstep (se 1 (by rfl) ⟨1315763, by rfl⟩ : syracuseStep 1754351 = 2631527) B2631527
theorem B7488767 : Blo 1168401 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B5924177 : Blo 1168401 5924177 := bstep (se 2 (by rfl) ⟨2221566, by rfl⟩ : syracuseStep 5924177 = 4443133) B4443133
theorem B11235611 : Blo 1168401 11235611 := bstep (se 1 (by rfl) ⟨8426708, by rfl⟩ : syracuseStep 11235611 = 16853417) B16853417
theorem B21336527 : Blo 1168401 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B1479151 : Blo 1168401 1479151 := bstep (se 1 (by rfl) ⟨1109363, by rfl⟩ : syracuseStep 1479151 = 2218727) B2218727
theorem B2962079 : Blo 1168401 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B14980403 : Blo 1168401 14980403 := bstep (se 1 (by rfl) ⟨11235302, by rfl⟩ : syracuseStep 14980403 = 22470605) B22470605
theorem B1168847 : Blo 1168401 1168847 := bstep (se 1 (by rfl) ⟨876635, by rfl⟩ : syracuseStep 1168847 = 1753271) B1753271
theorem B1169343 : Blo 1168401 1169343 := bstep (se 1 (by rfl) ⟨877007, by rfl⟩ : syracuseStep 1169343 = 1754015) B1754015
theorem B1170087 : Blo 1168401 1170087 := bstep (se 1 (by rfl) ⟨877565, by rfl⟩ : syracuseStep 1170087 = 1755131) B1755131
theorem B1974719 : Blo 1168401 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B1753691 : Blo 1168401 1753691 := bstep (se 1 (by rfl) ⟨1315268, by rfl⟩ : syracuseStep 1753691 = 2630537) B2630537
theorem B9986935 : Blo 1168401 9986935 := bstep (se 1 (by rfl) ⟨7490201, by rfl⟩ : syracuseStep 9986935 = 14980403) B14980403
theorem B3949451 : Blo 1168401 3949451 := bstep (se 1 (by rfl) ⟨2962088, by rfl⟩ : syracuseStep 3949451 = 5924177) B5924177
theorem B7490407 : Blo 1168401 7490407 := bstep (se 1 (by rfl) ⟨5617805, by rfl⟩ : syracuseStep 7490407 = 11235611) B11235611
theorem B14224351 : Blo 1168401 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B4992511 : Blo 1168401 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B1972201 : Blo 1168401 1972201 := bstep (se 2 (by rfl) ⟨739575, by rfl⟩ : syracuseStep 1972201 = 1479151) B1479151
theorem B1169567 : Blo 1168401 1169567 := bstep (se 1 (by rfl) ⟨877175, by rfl⟩ : syracuseStep 1169567 = 1754351) B1754351
theorem B9987209 : Blo 1168401 9987209 := bstep (se 2 (by rfl) ⟨3745203, by rfl⟩ : syracuseStep 9987209 = 7490407) B7490407
theorem B18965801 : Blo 1168401 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B2632967 : Blo 1168401 2632967 := bstep (se 1 (by rfl) ⟨1974725, by rfl⟩ : syracuseStep 2632967 = 3949451) B3949451
theorem B13315913 : Blo 1168401 13315913 := bstep (se 2 (by rfl) ⟨4993467, by rfl⟩ : syracuseStep 13315913 = 9986935) B9986935
theorem B6656681 : Blo 1168401 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B1316479 : Blo 1168401 1316479 := bstep (se 1 (by rfl) ⟨987359, by rfl⟩ : syracuseStep 1316479 = 1974719) B1974719
theorem B1169127 : Blo 1168401 1169127 := bstep (se 1 (by rfl) ⟨876845, by rfl⟩ : syracuseStep 1169127 = 1753691) B1753691
theorem B2629601 : Blo 1168401 2629601 := bstep (se 2 (by rfl) ⟨986100, by rfl⟩ : syracuseStep 2629601 = 1972201) B1972201
theorem B1755305 : Blo 1168401 1755305 := bstep (se 2 (by rfl) ⟨658239, by rfl⟩ : syracuseStep 1755305 = 1316479) B1316479
theorem B1755311 : Blo 1168401 1755311 := bstep (se 1 (by rfl) ⟨1316483, by rfl⟩ : syracuseStep 1755311 = 2632967) B2632967
theorem B12643867 : Blo 1168401 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B8877275 : Blo 1168401 8877275 := bstep (se 1 (by rfl) ⟨6657956, by rfl⟩ : syracuseStep 8877275 = 13315913) B13315913
theorem B4437787 : Blo 1168401 4437787 := bstep (se 1 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 4437787 = 6656681) B6656681
theorem B6658139 : Blo 1168401 6658139 := bstep (se 1 (by rfl) ⟨4993604, by rfl⟩ : syracuseStep 6658139 = 9987209) B9987209
theorem B1753067 : Blo 1168401 1753067 := bstep (se 1 (by rfl) ⟨1314800, by rfl⟩ : syracuseStep 1753067 = 2629601) B2629601
theorem B5917049 : Blo 1168401 5917049 := bstep (se 2 (by rfl) ⟨2218893, by rfl⟩ : syracuseStep 5917049 = 4437787) B4437787
theorem B5918183 : Blo 1168401 5918183 := bstep (se 1 (by rfl) ⟨4438637, by rfl⟩ : syracuseStep 5918183 = 8877275) B8877275
theorem B1168711 : Blo 1168401 1168711 := bstep (se 1 (by rfl) ⟨876533, by rfl⟩ : syracuseStep 1168711 = 1753067) B1753067
theorem B67433957 : Blo 1168401 67433957 := bstep (se 4 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 67433957 = 12643867) B12643867
theorem B4438759 : Blo 1168401 4438759 := bstep (se 1 (by rfl) ⟨3329069, by rfl⟩ : syracuseStep 4438759 = 6658139) B6658139
theorem B1170203 : Blo 1168401 1170203 := bstep (se 1 (by rfl) ⟨877652, by rfl⟩ : syracuseStep 1170203 = 1755305) B1755305
theorem B1170207 : Blo 1168401 1170207 := bstep (se 1 (by rfl) ⟨877655, by rfl⟩ : syracuseStep 1170207 = 1755311) B1755311
theorem B5918345 : Blo 1168401 5918345 := bstep (se 2 (by rfl) ⟨2219379, by rfl⟩ : syracuseStep 5918345 = 4438759) B4438759
theorem B3944699 : Blo 1168401 3944699 := bstep (se 1 (by rfl) ⟨2958524, by rfl⟩ : syracuseStep 3944699 = 5917049) B5917049
theorem B3945455 : Blo 1168401 3945455 := bstep (se 1 (by rfl) ⟨2959091, by rfl⟩ : syracuseStep 3945455 = 5918183) B5918183
theorem B44955971 : Blo 1168401 44955971 := bstep (se 1 (by rfl) ⟨33716978, by rfl⟩ : syracuseStep 44955971 = 67433957) B67433957
theorem B2629799 : Blo 1168401 2629799 := bstep (se 1 (by rfl) ⟨1972349, by rfl⟩ : syracuseStep 2629799 = 3944699) B3944699
theorem B2630303 : Blo 1168401 2630303 := bstep (se 1 (by rfl) ⟨1972727, by rfl⟩ : syracuseStep 2630303 = 3945455) B3945455
theorem B29970647 : Blo 1168401 29970647 := bstep (se 1 (by rfl) ⟨22477985, by rfl⟩ : syracuseStep 29970647 = 44955971) B44955971
theorem B3945563 : Blo 1168401 3945563 := bstep (se 1 (by rfl) ⟨2959172, by rfl⟩ : syracuseStep 3945563 = 5918345) B5918345
theorem B1753199 : Blo 1168401 1753199 := bstep (se 1 (by rfl) ⟨1314899, by rfl⟩ : syracuseStep 1753199 = 2629799) B2629799
theorem B19980431 : Blo 1168401 19980431 := bstep (se 1 (by rfl) ⟨14985323, by rfl⟩ : syracuseStep 19980431 = 29970647) B29970647
theorem B1753535 : Blo 1168401 1753535 := bstep (se 1 (by rfl) ⟨1315151, by rfl⟩ : syracuseStep 1753535 = 2630303) B2630303
theorem B2630375 : Blo 1168401 2630375 := bstep (se 1 (by rfl) ⟨1972781, by rfl⟩ : syracuseStep 2630375 = 3945563) B3945563
theorem B13320287 : Blo 1168401 13320287 := bstep (se 1 (by rfl) ⟨9990215, by rfl⟩ : syracuseStep 13320287 = 19980431) B19980431
theorem B1753583 : Blo 1168401 1753583 := bstep (se 1 (by rfl) ⟨1315187, by rfl⟩ : syracuseStep 1753583 = 2630375) B2630375
theorem B1168799 : Blo 1168401 1168799 := bstep (se 1 (by rfl) ⟨876599, by rfl⟩ : syracuseStep 1168799 = 1753199) B1753199
theorem B1169023 : Blo 1168401 1169023 := bstep (se 1 (by rfl) ⟨876767, by rfl⟩ : syracuseStep 1169023 = 1753535) B1753535
theorem B8880191 : Blo 1168401 8880191 := bstep (se 1 (by rfl) ⟨6660143, by rfl⟩ : syracuseStep 8880191 = 13320287) B13320287
theorem B1169055 : Blo 1168401 1169055 := bstep (se 1 (by rfl) ⟨876791, by rfl⟩ : syracuseStep 1169055 = 1753583) B1753583
theorem B5920127 : Blo 1168401 5920127 := bstep (se 1 (by rfl) ⟨4440095, by rfl⟩ : syracuseStep 5920127 = 8880191) B8880191
theorem B3946751 : Blo 1168401 3946751 := bstep (se 1 (by rfl) ⟨2960063, by rfl⟩ : syracuseStep 3946751 = 5920127) B5920127
theorem B2631167 : Blo 1168401 2631167 := bstep (se 1 (by rfl) ⟨1973375, by rfl⟩ : syracuseStep 2631167 = 3946751) B3946751
theorem B1754111 : Blo 1168401 1754111 := bstep (se 1 (by rfl) ⟨1315583, by rfl⟩ : syracuseStep 1754111 = 2631167) B2631167
theorem B1169407 : Blo 1168401 1169407 := bstep (se 1 (by rfl) ⟨877055, by rfl⟩ : syracuseStep 1169407 = 1754111) B1754111

theorem C0 (j : ℕ) (h1 : 292100 ≤ j) (h2 : j ≤ 292599) : Blo 1168401 (4 * j + 3) := by
  interval_cases j
  · exact B1168403
  · exact B1168407
  · exact B1168411
  · exact B1168415
  · exact B1168419
  · exact B1168423
  · exact B1168427
  · exact B1168431
  · exact B1168435
  · exact B1168439
  · exact B1168443
  · exact B1168447
  · exact B1168451
  · exact B1168455
  · exact B1168459
  · exact B1168463
  · exact B1168467
  · exact B1168471
  · exact B1168475
  · exact B1168479
  · exact B1168483
  · exact B1168487
  · exact B1168491
  · exact B1168495
  · exact B1168499
  · exact B1168503
  · exact B1168507
  · exact B1168511
  · exact B1168515
  · exact B1168519
  · exact B1168523
  · exact B1168527
  · exact B1168531
  · exact B1168535
  · exact B1168539
  · exact B1168543
  · exact B1168547
  · exact B1168551
  · exact B1168555
  · exact B1168559
  · exact B1168563
  · exact B1168567
  · exact B1168571
  · exact B1168575
  · exact B1168579
  · exact B1168583
  · exact B1168587
  · exact B1168591
  · exact B1168595
  · exact B1168599
  · exact B1168603
  · exact B1168607
  · exact B1168611
  · exact B1168615
  · exact B1168619
  · exact B1168623
  · exact B1168627
  · exact B1168631
  · exact B1168635
  · exact B1168639
  · exact B1168643
  · exact B1168647
  · exact B1168651
  · exact B1168655
  · exact B1168659
  · exact B1168663
  · exact B1168667
  · exact B1168671
  · exact B1168675
  · exact B1168679
  · exact B1168683
  · exact B1168687
  · exact B1168691
  · exact B1168695
  · exact B1168699
  · exact B1168703
  · exact B1168707
  · exact B1168711
  · exact B1168715
  · exact B1168719
  · exact B1168723
  · exact B1168727
  · exact B1168731
  · exact B1168735
  · exact B1168739
  · exact B1168743
  · exact B1168747
  · exact B1168751
  · exact B1168755
  · exact B1168759
  · exact B1168763
  · exact B1168767
  · exact B1168771
  · exact B1168775
  · exact B1168779
  · exact B1168783
  · exact B1168787
  · exact B1168791
  · exact B1168795
  · exact B1168799
  · exact B1168803
  · exact B1168807
  · exact B1168811
  · exact B1168815
  · exact B1168819
  · exact B1168823
  · exact B1168827
  · exact B1168831
  · exact B1168835
  · exact B1168839
  · exact B1168843
  · exact B1168847
  · exact B1168851
  · exact B1168855
  · exact B1168859
  · exact B1168863
  · exact B1168867
  · exact B1168871
  · exact B1168875
  · exact B1168879
  · exact B1168883
  · exact B1168887
  · exact B1168891
  · exact B1168895
  · exact B1168899
  · exact B1168903
  · exact B1168907
  · exact B1168911
  · exact B1168915
  · exact B1168919
  · exact B1168923
  · exact B1168927
  · exact B1168931
  · exact B1168935
  · exact B1168939
  · exact B1168943
  · exact B1168947
  · exact B1168951
  · exact B1168955
  · exact B1168959
  · exact B1168963
  · exact B1168967
  · exact B1168971
  · exact B1168975
  · exact B1168979
  · exact B1168983
  · exact B1168987
  · exact B1168991
  · exact B1168995
  · exact B1168999
  · exact B1169003
  · exact B1169007
  · exact B1169011
  · exact B1169015
  · exact B1169019
  · exact B1169023
  · exact B1169027
  · exact B1169031
  · exact B1169035
  · exact B1169039
  · exact B1169043
  · exact B1169047
  · exact B1169051
  · exact B1169055
  · exact B1169059
  · exact B1169063
  · exact B1169067
  · exact B1169071
  · exact B1169075
  · exact B1169079
  · exact B1169083
  · exact B1169087
  · exact B1169091
  · exact B1169095
  · exact B1169099
  · exact B1169103
  · exact B1169107
  · exact B1169111
  · exact B1169115
  · exact B1169119
  · exact B1169123
  · exact B1169127
  · exact B1169131
  · exact B1169135
  · exact B1169139
  · exact B1169143
  · exact B1169147
  · exact B1169151
  · exact B1169155
  · exact B1169159
  · exact B1169163
  · exact B1169167
  · exact B1169171
  · exact B1169175
  · exact B1169179
  · exact B1169183
  · exact B1169187
  · exact B1169191
  · exact B1169195
  · exact B1169199
  · exact B1169203
  · exact B1169207
  · exact B1169211
  · exact B1169215
  · exact B1169219
  · exact B1169223
  · exact B1169227
  · exact B1169231
  · exact B1169235
  · exact B1169239
  · exact B1169243
  · exact B1169247
  · exact B1169251
  · exact B1169255
  · exact B1169259
  · exact B1169263
  · exact B1169267
  · exact B1169271
  · exact B1169275
  · exact B1169279
  · exact B1169283
  · exact B1169287
  · exact B1169291
  · exact B1169295
  · exact B1169299
  · exact B1169303
  · exact B1169307
  · exact B1169311
  · exact B1169315
  · exact B1169319
  · exact B1169323
  · exact B1169327
  · exact B1169331
  · exact B1169335
  · exact B1169339
  · exact B1169343
  · exact B1169347
  · exact B1169351
  · exact B1169355
  · exact B1169359
  · exact B1169363
  · exact B1169367
  · exact B1169371
  · exact B1169375
  · exact B1169379
  · exact B1169383
  · exact B1169387
  · exact B1169391
  · exact B1169395
  · exact B1169399
  · exact B1169403
  · exact B1169407
  · exact B1169411
  · exact B1169415
  · exact B1169419
  · exact B1169423
  · exact B1169427
  · exact B1169431
  · exact B1169435
  · exact B1169439
  · exact B1169443
  · exact B1169447
  · exact B1169451
  · exact B1169455
  · exact B1169459
  · exact B1169463
  · exact B1169467
  · exact B1169471
  · exact B1169475
  · exact B1169479
  · exact B1169483
  · exact B1169487
  · exact B1169491
  · exact B1169495
  · exact B1169499
  · exact B1169503
  · exact B1169507
  · exact B1169511
  · exact B1169515
  · exact B1169519
  · exact B1169523
  · exact B1169527
  · exact B1169531
  · exact B1169535
  · exact B1169539
  · exact B1169543
  · exact B1169547
  · exact B1169551
  · exact B1169555
  · exact B1169559
  · exact B1169563
  · exact B1169567
  · exact B1169571
  · exact B1169575
  · exact B1169579
  · exact B1169583
  · exact B1169587
  · exact B1169591
  · exact B1169595
  · exact B1169599
  · exact B1169603
  · exact B1169607
  · exact B1169611
  · exact B1169615
  · exact B1169619
  · exact B1169623
  · exact B1169627
  · exact B1169631
  · exact B1169635
  · exact B1169639
  · exact B1169643
  · exact B1169647
  · exact B1169651
  · exact B1169655
  · exact B1169659
  · exact B1169663
  · exact B1169667
  · exact B1169671
  · exact B1169675
  · exact B1169679
  · exact B1169683
  · exact B1169687
  · exact B1169691
  · exact B1169695
  · exact B1169699
  · exact B1169703
  · exact B1169707
  · exact B1169711
  · exact B1169715
  · exact B1169719
  · exact B1169723
  · exact B1169727
  · exact B1169731
  · exact B1169735
  · exact B1169739
  · exact B1169743
  · exact B1169747
  · exact B1169751
  · exact B1169755
  · exact B1169759
  · exact B1169763
  · exact B1169767
  · exact B1169771
  · exact B1169775
  · exact B1169779
  · exact B1169783
  · exact B1169787
  · exact B1169791
  · exact B1169795
  · exact B1169799
  · exact B1169803
  · exact B1169807
  · exact B1169811
  · exact B1169815
  · exact B1169819
  · exact B1169823
  · exact B1169827
  · exact B1169831
  · exact B1169835
  · exact B1169839
  · exact B1169843
  · exact B1169847
  · exact B1169851
  · exact B1169855
  · exact B1169859
  · exact B1169863
  · exact B1169867
  · exact B1169871
  · exact B1169875
  · exact B1169879
  · exact B1169883
  · exact B1169887
  · exact B1169891
  · exact B1169895
  · exact B1169899
  · exact B1169903
  · exact B1169907
  · exact B1169911
  · exact B1169915
  · exact B1169919
  · exact B1169923
  · exact B1169927
  · exact B1169931
  · exact B1169935
  · exact B1169939
  · exact B1169943
  · exact B1169947
  · exact B1169951
  · exact B1169955
  · exact B1169959
  · exact B1169963
  · exact B1169967
  · exact B1169971
  · exact B1169975
  · exact B1169979
  · exact B1169983
  · exact B1169987
  · exact B1169991
  · exact B1169995
  · exact B1169999
  · exact B1170003
  · exact B1170007
  · exact B1170011
  · exact B1170015
  · exact B1170019
  · exact B1170023
  · exact B1170027
  · exact B1170031
  · exact B1170035
  · exact B1170039
  · exact B1170043
  · exact B1170047
  · exact B1170051
  · exact B1170055
  · exact B1170059
  · exact B1170063
  · exact B1170067
  · exact B1170071
  · exact B1170075
  · exact B1170079
  · exact B1170083
  · exact B1170087
  · exact B1170091
  · exact B1170095
  · exact B1170099
  · exact B1170103
  · exact B1170107
  · exact B1170111
  · exact B1170115
  · exact B1170119
  · exact B1170123
  · exact B1170127
  · exact B1170131
  · exact B1170135
  · exact B1170139
  · exact B1170143
  · exact B1170147
  · exact B1170151
  · exact B1170155
  · exact B1170159
  · exact B1170163
  · exact B1170167
  · exact B1170171
  · exact B1170175
  · exact B1170179
  · exact B1170183
  · exact B1170187
  · exact B1170191
  · exact B1170195
  · exact B1170199
  · exact B1170203
  · exact B1170207
  · exact B1170211
  · exact B1170215
  · exact B1170219
  · exact B1170223
  · exact B1170227
  · exact B1170231
  · exact B1170235
  · exact B1170239
  · exact B1170243
  · exact B1170247
  · exact B1170251
  · exact B1170255
  · exact B1170259
  · exact B1170263
  · exact B1170267
  · exact B1170271
  · exact B1170275
  · exact B1170279
  · exact B1170283
  · exact B1170287
  · exact B1170291
  · exact B1170295
  · exact B1170299
  · exact B1170303
  · exact B1170307
  · exact B1170311
  · exact B1170315
  · exact B1170319
  · exact B1170323
  · exact B1170327
  · exact B1170331
  · exact B1170335
  · exact B1170339
  · exact B1170343
  · exact B1170347
  · exact B1170351
  · exact B1170355
  · exact B1170359
  · exact B1170363
  · exact B1170367
  · exact B1170371
  · exact B1170375
  · exact B1170379
  · exact B1170383
  · exact B1170387
  · exact B1170391
  · exact B1170395
  · exact B1170399

theorem solution (m : ℕ) (hlo : 1168401 ≤ m) (hhi : m ≤ 1170401) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 292100 ≤ j := by omega
    have hj2 : j ≤ 292599 := by omega
    have hb : Blo 1168401 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
