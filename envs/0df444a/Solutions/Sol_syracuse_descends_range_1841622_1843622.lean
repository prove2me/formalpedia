-- Prove2me | solution 1 for syracuse_descends_range_1841622_1843622
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:03:59.957329+00:00
-- url     : https://prove2.me/submissions/3a3b5382-4279-4668-b331-448e8ab013c2

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


theorem B4145165 : Blo 1841622 4145165 := bbase (se 3 (by rfl) ⟨777218, by rfl⟩ : syracuseStep 4145165 = 1554437) (by norm_num)
theorem B2072605 : Blo 1841622 2072605 := bbase (se 3 (by rfl) ⟨388613, by rfl⟩ : syracuseStep 2072605 = 777227) (by norm_num)
theorem B3547189 : Blo 1841622 3547189 := bbase (se 5 (by rfl) ⟨166274, by rfl⟩ : syracuseStep 3547189 = 332549) (by norm_num)
theorem B2072641 : Blo 1841622 2072641 := bbase (se 2 (by rfl) ⟨777240, by rfl⟩ : syracuseStep 2072641 = 1554481) (by norm_num)
theorem B3498061 : Blo 1841622 3498061 := bbase (se 3 (by rfl) ⟨655886, by rfl⟩ : syracuseStep 3498061 = 1311773) (by norm_num)
theorem B4145237 : Blo 1841622 4145237 := bbase (se 8 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 4145237 = 48577) (by norm_num)
theorem B6217829 : Blo 1841622 6217829 := bbase (se 4 (by rfl) ⟨582921, by rfl⟩ : syracuseStep 6217829 = 1165843) (by norm_num)
theorem B2072677 : Blo 1841622 2072677 := bbase (se 4 (by rfl) ⟨194313, by rfl⟩ : syracuseStep 2072677 = 388627) (by norm_num)
theorem B2072713 : Blo 1841622 2072713 := bbase (se 2 (by rfl) ⟨777267, by rfl⟩ : syracuseStep 2072713 = 1554535) (by norm_num)
theorem B4145309 : Blo 1841622 4145309 := bbase (se 3 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 4145309 = 1554491) (by norm_num)
theorem B2072749 : Blo 1841622 2072749 := bbase (se 3 (by rfl) ⟨388640, by rfl⟩ : syracuseStep 2072749 = 777281) (by norm_num)
theorem B2072785 : Blo 1841622 2072785 := bbase (se 2 (by rfl) ⟨777294, by rfl⟩ : syracuseStep 2072785 = 1554589) (by norm_num)
theorem B4145381 : Blo 1841622 4145381 := bbase (se 4 (by rfl) ⟨388629, by rfl⟩ : syracuseStep 4145381 = 777259) (by norm_num)
theorem B3498221 : Blo 1841622 3498221 := bbase (se 3 (by rfl) ⟨655916, by rfl⟩ : syracuseStep 3498221 = 1311833) (by norm_num)
theorem B2072821 : Blo 1841622 2072821 := bbase (se 5 (by rfl) ⟨97163, by rfl⟩ : syracuseStep 2072821 = 194327) (by norm_num)
theorem B5603573 : Blo 1841622 5603573 := bbase (se 5 (by rfl) ⟨262667, by rfl⟩ : syracuseStep 5603573 = 525335) (by norm_num)
theorem B8855813 : Blo 1841622 8855813 := bbase (se 4 (by rfl) ⟨830232, by rfl⟩ : syracuseStep 8855813 = 1660465) (by norm_num)
theorem B2072857 : Blo 1841622 2072857 := bbase (se 2 (by rfl) ⟨777321, by rfl⟩ : syracuseStep 2072857 = 1554643) (by norm_num)
theorem B2105633 : Blo 1841622 2105633 := bbase (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) (by norm_num)
theorem B4145453 : Blo 1841622 4145453 := bbase (se 3 (by rfl) ⟨777272, by rfl⟩ : syracuseStep 4145453 = 1554545) (by norm_num)
theorem B2072893 : Blo 1841622 2072893 := bbase (se 3 (by rfl) ⟨388667, by rfl⟩ : syracuseStep 2072893 = 777335) (by norm_num)
theorem B2072929 : Blo 1841622 2072929 := bbase (se 2 (by rfl) ⟨777348, by rfl⟩ : syracuseStep 2072929 = 1554697) (by norm_num)
theorem B4661621 : Blo 1841622 4661621 := bbase (se 5 (by rfl) ⟨218513, by rfl⟩ : syracuseStep 4661621 = 437027) (by norm_num)
theorem B4145525 : Blo 1841622 4145525 := bbase (se 5 (by rfl) ⟨194321, by rfl⟩ : syracuseStep 4145525 = 388643) (by norm_num)
theorem B3498365 : Blo 1841622 3498365 := bbase (se 3 (by rfl) ⟨655943, by rfl⟩ : syracuseStep 3498365 = 1311887) (by norm_num)
theorem B2072965 : Blo 1841622 2072965 := bbase (se 4 (by rfl) ⟨194340, by rfl⟩ : syracuseStep 2072965 = 388681) (by norm_num)
theorem B23601557 : Blo 1841622 23601557 := bbase (se 6 (by rfl) ⟨553161, by rfl⟩ : syracuseStep 23601557 = 1106323) (by norm_num)
theorem B2073001 : Blo 1841622 2073001 := bbase (se 2 (by rfl) ⟨777375, by rfl⟩ : syracuseStep 2073001 = 1554751) (by norm_num)
theorem B4145597 : Blo 1841622 4145597 := bbase (se 3 (by rfl) ⟨777299, by rfl⟩ : syracuseStep 4145597 = 1554599) (by norm_num)
theorem B2802109 : Blo 1841622 2802109 := bbase (se 3 (by rfl) ⟨525395, by rfl⟩ : syracuseStep 2802109 = 1050791) (by norm_num)
theorem B2073037 : Blo 1841622 2073037 := bbase (se 3 (by rfl) ⟨388694, by rfl⟩ : syracuseStep 2073037 = 777389) (by norm_num)
theorem B6644197 : Blo 1841622 6644197 := bbase (se 4 (by rfl) ⟨622893, by rfl⟩ : syracuseStep 6644197 = 1245787) (by norm_num)
theorem B2073073 : Blo 1841622 2073073 := bbase (se 2 (by rfl) ⟨777402, by rfl⟩ : syracuseStep 2073073 = 1554805) (by norm_num)
theorem B4145669 : Blo 1841622 4145669 := bbase (se 4 (by rfl) ⟨388656, by rfl⟩ : syracuseStep 4145669 = 777313) (by norm_num)
theorem B6218261 : Blo 1841622 6218261 := bbase (se 6 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 6218261 = 291481) (by norm_num)
theorem B2073109 : Blo 1841622 2073109 := bbase (se 6 (by rfl) ⟨48588, by rfl⟩ : syracuseStep 2073109 = 97177) (by norm_num)
theorem B4661813 : Blo 1841622 4661813 := bbase (se 5 (by rfl) ⟨218522, by rfl⟩ : syracuseStep 4661813 = 437045) (by norm_num)
theorem B2073145 : Blo 1841622 2073145 := bbase (se 2 (by rfl) ⟨777429, by rfl⟩ : syracuseStep 2073145 = 1554859) (by norm_num)
theorem B4145741 : Blo 1841622 4145741 := bbase (se 3 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 4145741 = 1554653) (by norm_num)
theorem B2073181 : Blo 1841622 2073181 := bbase (se 3 (by rfl) ⟨388721, by rfl⟩ : syracuseStep 2073181 = 777443) (by norm_num)
theorem B2073217 : Blo 1841622 2073217 := bbase (se 2 (by rfl) ⟨777456, by rfl⟩ : syracuseStep 2073217 = 1554913) (by norm_num)
theorem B4145813 : Blo 1841622 4145813 := bbase (se 6 (by rfl) ⟨97167, by rfl⟩ : syracuseStep 4145813 = 194335) (by norm_num)
theorem B3498653 : Blo 1841622 3498653 := bbase (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) (by norm_num)
theorem B2073253 : Blo 1841622 2073253 := bbase (se 4 (by rfl) ⟨194367, by rfl⟩ : syracuseStep 2073253 = 388735) (by norm_num)
theorem B2073289 : Blo 1841622 2073289 := bbase (se 2 (by rfl) ⟨777483, by rfl⟩ : syracuseStep 2073289 = 1554967) (by norm_num)
theorem B4145885 : Blo 1841622 4145885 := bbase (se 3 (by rfl) ⟨777353, by rfl⟩ : syracuseStep 4145885 = 1554707) (by norm_num)
theorem B2073325 : Blo 1841622 2073325 := bbase (se 3 (by rfl) ⟨388748, by rfl⟩ : syracuseStep 2073325 = 777497) (by norm_num)
theorem B2073361 : Blo 1841622 2073361 := bbase (se 2 (by rfl) ⟨777510, by rfl⟩ : syracuseStep 2073361 = 1555021) (by norm_num)
theorem B6644501 : Blo 1841622 6644501 := bbase (se 6 (by rfl) ⟨155730, by rfl⟩ : syracuseStep 6644501 = 311461) (by norm_num)
theorem B4145957 : Blo 1841622 4145957 := bbase (se 4 (by rfl) ⟨388683, by rfl⟩ : syracuseStep 4145957 = 777367) (by norm_num)
theorem B3498805 : Blo 1841622 3498805 := bbase (se 5 (by rfl) ⟨164006, by rfl⟩ : syracuseStep 3498805 = 328013) (by norm_num)
theorem B2073397 : Blo 1841622 2073397 := bbase (se 5 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 2073397 = 194381) (by norm_num)
theorem B2073433 : Blo 1841622 2073433 := bbase (se 2 (by rfl) ⟨777537, by rfl⟩ : syracuseStep 2073433 = 1555075) (by norm_num)
theorem B4146029 : Blo 1841622 4146029 := bbase (se 3 (by rfl) ⟨777380, by rfl⟩ : syracuseStep 4146029 = 1554761) (by norm_num)
theorem B2073469 : Blo 1841622 2073469 := bbase (se 3 (by rfl) ⟨388775, by rfl⟩ : syracuseStep 2073469 = 777551) (by norm_num)
theorem B4662157 : Blo 1841622 4662157 := bbase (se 3 (by rfl) ⟨874154, by rfl⟩ : syracuseStep 4662157 = 1748309) (by norm_num)
theorem B16810901 : Blo 1841622 16810901 := bbase (se 6 (by rfl) ⟨394005, by rfl⟩ : syracuseStep 16810901 = 788011) (by norm_num)
theorem B2073505 : Blo 1841622 2073505 := bbase (se 2 (by rfl) ⟨777564, by rfl⟩ : syracuseStep 2073505 = 1555129) (by norm_num)
theorem B7283621 : Blo 1841622 7283621 := bbase (se 4 (by rfl) ⟨682839, by rfl⟩ : syracuseStep 7283621 = 1365679) (by norm_num)
theorem B4146101 : Blo 1841622 4146101 := bbase (se 5 (by rfl) ⟨194348, by rfl⟩ : syracuseStep 4146101 = 388697) (by norm_num)
theorem B6218693 : Blo 1841622 6218693 := bbase (se 4 (by rfl) ⟨583002, by rfl⟩ : syracuseStep 6218693 = 1166005) (by norm_num)
theorem B2073541 : Blo 1841622 2073541 := bbase (se 4 (by rfl) ⟨194394, by rfl⟩ : syracuseStep 2073541 = 388789) (by norm_num)
theorem B1967053 : Blo 1841622 1967053 := bbase (se 3 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 1967053 = 737645) (by norm_num)
theorem B9331685 : Blo 1841622 9331685 := bbase (se 4 (by rfl) ⟨874845, by rfl⟩ : syracuseStep 9331685 = 1749691) (by norm_num)
theorem B2073577 : Blo 1841622 2073577 := bbase (se 2 (by rfl) ⟨777591, by rfl⟩ : syracuseStep 2073577 = 1555183) (by norm_num)
theorem B4662269 : Blo 1841622 4662269 := bbase (se 3 (by rfl) ⟨874175, by rfl⟩ : syracuseStep 4662269 = 1748351) (by norm_num)
theorem B4146173 : Blo 1841622 4146173 := bbase (se 3 (by rfl) ⟨777407, by rfl⟩ : syracuseStep 4146173 = 1554815) (by norm_num)
theorem B1967113 : Blo 1841622 1967113 := bbase (se 2 (by rfl) ⟨737667, by rfl⟩ : syracuseStep 1967113 = 1475335) (by norm_num)
theorem B2950157 : Blo 1841622 2950157 := bbase (se 3 (by rfl) ⟨553154, by rfl⟩ : syracuseStep 2950157 = 1106309) (by norm_num)
theorem B2212877 : Blo 1841622 2212877 := bbase (se 3 (by rfl) ⟨414914, by rfl⟩ : syracuseStep 2212877 = 829829) (by norm_num)
theorem B2073613 : Blo 1841622 2073613 := bbase (se 3 (by rfl) ⟨388802, by rfl⟩ : syracuseStep 2073613 = 777605) (by norm_num)
theorem B2073649 : Blo 1841622 2073649 := bbase (se 2 (by rfl) ⟨777618, by rfl⟩ : syracuseStep 2073649 = 1555237) (by norm_num)
theorem B2212925 : Blo 1841622 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B4146245 : Blo 1841622 4146245 := bbase (se 4 (by rfl) ⟨388710, by rfl⟩ : syracuseStep 4146245 = 777421) (by norm_num)
theorem B3933269 : Blo 1841622 3933269 := bbase (se 8 (by rfl) ⟨23046, by rfl⟩ : syracuseStep 3933269 = 46093) (by norm_num)
theorem B2073685 : Blo 1841622 2073685 := bbase (se 8 (by rfl) ⟨12150, by rfl⟩ : syracuseStep 2073685 = 24301) (by norm_num)
theorem B3499109 : Blo 1841622 3499109 := bbase (se 4 (by rfl) ⟨328041, by rfl⟩ : syracuseStep 3499109 = 656083) (by norm_num)
theorem B2073721 : Blo 1841622 2073721 := bbase (se 2 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 2073721 = 1555291) (by norm_num)
theorem B5047429 : Blo 1841622 5047429 := bbase (se 4 (by rfl) ⟨473196, by rfl⟩ : syracuseStep 5047429 = 946393) (by norm_num)
theorem B4146317 : Blo 1841622 4146317 := bbase (se 3 (by rfl) ⟨777434, by rfl⟩ : syracuseStep 4146317 = 1554869) (by norm_num)
theorem B3318941 : Blo 1841622 3318941 := bbase (se 3 (by rfl) ⟨622301, by rfl⟩ : syracuseStep 3318941 = 1244603) (by norm_num)
theorem B2073757 : Blo 1841622 2073757 := bbase (se 3 (by rfl) ⟨388829, by rfl⟩ : syracuseStep 2073757 = 777659) (by norm_num)
theorem B8520869 : Blo 1841622 8520869 := bbase (se 4 (by rfl) ⟨798831, by rfl⟩ : syracuseStep 8520869 = 1597663) (by norm_num)
theorem B4662461 : Blo 1841622 4662461 := bbase (se 3 (by rfl) ⟨874211, by rfl⟩ : syracuseStep 4662461 = 1748423) (by norm_num)
theorem B2073793 : Blo 1841622 2073793 := bbase (se 2 (by rfl) ⟨777672, by rfl⟩ : syracuseStep 2073793 = 1555345) (by norm_num)
theorem B4146389 : Blo 1841622 4146389 := bbase (se 7 (by rfl) ⟨48590, by rfl⟩ : syracuseStep 4146389 = 97181) (by norm_num)
theorem B5604581 : Blo 1841622 5604581 := bbase (se 4 (by rfl) ⟨525429, by rfl⟩ : syracuseStep 5604581 = 1050859) (by norm_num)
theorem B2073829 : Blo 1841622 2073829 := bbase (se 4 (by rfl) ⟨194421, by rfl⟩ : syracuseStep 2073829 = 388843) (by norm_num)
theorem B2622709 : Blo 1841622 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B2073865 : Blo 1841622 2073865 := bbase (se 2 (by rfl) ⟨777699, by rfl⟩ : syracuseStep 2073865 = 1555399) (by norm_num)
theorem B3990797 : Blo 1841622 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B4146461 : Blo 1841622 4146461 := bbase (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) (by norm_num)
theorem B3319085 : Blo 1841622 3319085 := bbase (se 3 (by rfl) ⟨622328, by rfl⟩ : syracuseStep 3319085 = 1244657) (by norm_num)
theorem B2073901 : Blo 1841622 2073901 := bbase (se 3 (by rfl) ⟨388856, by rfl⟩ : syracuseStep 2073901 = 777713) (by norm_num)
theorem B2213185 : Blo 1841622 2213185 := bbase (se 2 (by rfl) ⟨829944, by rfl⟩ : syracuseStep 2213185 = 1659889) (by norm_num)
theorem B1967429 : Blo 1841622 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B3933517 : Blo 1841622 3933517 := bbase (se 3 (by rfl) ⟨737534, by rfl⟩ : syracuseStep 3933517 = 1475069) (by norm_num)
theorem B2073937 : Blo 1841622 2073937 := bbase (se 2 (by rfl) ⟨777726, by rfl⟩ : syracuseStep 2073937 = 1555453) (by norm_num)
theorem B4146533 : Blo 1841622 4146533 := bbase (se 4 (by rfl) ⟨388737, by rfl⟩ : syracuseStep 4146533 = 777475) (by norm_num)
theorem B6219125 : Blo 1841622 6219125 := bbase (se 5 (by rfl) ⟨291521, by rfl⟩ : syracuseStep 6219125 = 583043) (by norm_num)
theorem B2073973 : Blo 1841622 2073973 := bbase (se 5 (by rfl) ⟨97217, by rfl⟩ : syracuseStep 2073973 = 194435) (by norm_num)
theorem B9323909 : Blo 1841622 9323909 := bbase (se 4 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 9323909 = 1748233) (by norm_num)
theorem B4425101 : Blo 1841622 4425101 := bbase (se 3 (by rfl) ⟨829706, by rfl⟩ : syracuseStep 4425101 = 1659413) (by norm_num)
theorem B2074009 : Blo 1841622 2074009 := bbase (se 2 (by rfl) ⟨777753, by rfl⟩ : syracuseStep 2074009 = 1555507) (by norm_num)
theorem B4146605 : Blo 1841622 4146605 := bbase (se 3 (by rfl) ⟨777488, by rfl⟩ : syracuseStep 4146605 = 1554977) (by norm_num)
theorem B13993397 : Blo 1841622 13993397 := bbase (se 5 (by rfl) ⟨655940, by rfl⟩ : syracuseStep 13993397 = 1311881) (by norm_num)
theorem B2074045 : Blo 1841622 2074045 := bbase (se 3 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 2074045 = 777767) (by norm_num)
theorem B13469141 : Blo 1841622 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B4146677 : Blo 1841622 4146677 := bbase (se 5 (by rfl) ⟨194375, by rfl⟩ : syracuseStep 4146677 = 388751) (by norm_num)
theorem B4662805 : Blo 1841622 4662805 := bbase (se 6 (by rfl) ⟨109284, by rfl⟩ : syracuseStep 4662805 = 218569) (by norm_num)
theorem B4146749 : Blo 1841622 4146749 := bbase (se 3 (by rfl) ⟨777515, by rfl⟩ : syracuseStep 4146749 = 1555031) (by norm_num)
theorem B2623045 : Blo 1841622 2623045 := bbase (se 4 (by rfl) ⟨245910, by rfl⟩ : syracuseStep 2623045 = 491821) (by norm_num)
theorem B2213449 : Blo 1841622 2213449 := bbase (se 2 (by rfl) ⟨830043, by rfl⟩ : syracuseStep 2213449 = 1660087) (by norm_num)
theorem B5244517 : Blo 1841622 5244517 := bbase (se 4 (by rfl) ⟨491673, by rfl⟩ : syracuseStep 5244517 = 983347) (by norm_num)
theorem B4662917 : Blo 1841622 4662917 := bbase (se 4 (by rfl) ⟨437148, by rfl⟩ : syracuseStep 4662917 = 874297) (by norm_num)
theorem B4146821 : Blo 1841622 4146821 := bbase (se 4 (by rfl) ⟨388764, by rfl⟩ : syracuseStep 4146821 = 777529) (by norm_num)
theorem B5604997 : Blo 1841622 5604997 := bbase (se 4 (by rfl) ⟨525468, by rfl⟩ : syracuseStep 5604997 = 1050937) (by norm_num)
theorem B2950805 : Blo 1841622 2950805 := bbase (se 6 (by rfl) ⟨69159, by rfl⟩ : syracuseStep 2950805 = 138319) (by norm_num)
theorem B2213569 : Blo 1841622 2213569 := bbase (se 2 (by rfl) ⟨830088, by rfl⟩ : syracuseStep 2213569 = 1660177) (by norm_num)
theorem B4146893 : Blo 1841622 4146893 := bbase (se 3 (by rfl) ⟨777542, by rfl⟩ : syracuseStep 4146893 = 1555085) (by norm_num)
theorem B2762453 : Blo 1841622 2762453 := bbase (se 7 (by rfl) ⟨32372, by rfl⟩ : syracuseStep 2762453 = 64745) (by norm_num)
theorem B2762477 : Blo 1841622 2762477 := bbase (se 3 (by rfl) ⟨517964, by rfl⟩ : syracuseStep 2762477 = 1035929) (by norm_num)
theorem B1967873 : Blo 1841622 1967873 := bbase (se 2 (by rfl) ⟨737952, by rfl⟩ : syracuseStep 1967873 = 1475905) (by norm_num)
theorem B2762501 : Blo 1841622 2762501 := bbase (se 4 (by rfl) ⟨258984, by rfl⟩ : syracuseStep 2762501 = 517969) (by norm_num)
theorem B4146965 : Blo 1841622 4146965 := bbase (se 6 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 4146965 = 194389) (by norm_num)
theorem B5605141 : Blo 1841622 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B2762525 : Blo 1841622 2762525 := bbase (se 3 (by rfl) ⟨517973, by rfl⟩ : syracuseStep 2762525 = 1035947) (by norm_num)
theorem B2623261 : Blo 1841622 2623261 := bbase (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) (by norm_num)
theorem B6219557 : Blo 1841622 6219557 := bbase (se 4 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 6219557 = 1166167) (by norm_num)
theorem B8406821 : Blo 1841622 8406821 := bbase (se 4 (by rfl) ⟨788139, by rfl⟩ : syracuseStep 8406821 = 1576279) (by norm_num)
theorem B2762549 : Blo 1841622 2762549 := bbase (se 5 (by rfl) ⟨129494, by rfl⟩ : syracuseStep 2762549 = 258989) (by norm_num)
theorem B1967933 : Blo 1841622 1967933 := bbase (se 3 (by rfl) ⟨368987, by rfl⟩ : syracuseStep 1967933 = 737975) (by norm_num)
theorem B3934021 : Blo 1841622 3934021 := bbase (se 4 (by rfl) ⟨368814, by rfl⟩ : syracuseStep 3934021 = 737629) (by norm_num)
theorem B4663109 : Blo 1841622 4663109 := bbase (se 4 (by rfl) ⟨437166, by rfl⟩ : syracuseStep 4663109 = 874333) (by norm_num)
theorem B2762573 : Blo 1841622 2762573 := bbase (se 3 (by rfl) ⟨517982, by rfl⟩ : syracuseStep 2762573 = 1035965) (by norm_num)
theorem B13985621 : Blo 1841622 13985621 := bbase (se 9 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 13985621 = 81947) (by norm_num)
theorem B3499861 : Blo 1841622 3499861 := bbase (se 9 (by rfl) ⟨10253, by rfl⟩ : syracuseStep 3499861 = 20507) (by norm_num)
theorem B4147037 : Blo 1841622 4147037 := bbase (se 3 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 4147037 = 1555139) (by norm_num)
theorem B2762597 : Blo 1841622 2762597 := bbase (se 4 (by rfl) ⟨258993, by rfl⟩ : syracuseStep 2762597 = 517987) (by norm_num)
theorem B2762621 : Blo 1841622 2762621 := bbase (se 3 (by rfl) ⟨517991, by rfl⟩ : syracuseStep 2762621 = 1035983) (by norm_num)
theorem B2762645 : Blo 1841622 2762645 := bbase (se 6 (by rfl) ⟨64749, by rfl⟩ : syracuseStep 2762645 = 129499) (by norm_num)
theorem B4147109 : Blo 1841622 4147109 := bbase (se 4 (by rfl) ⟨388791, by rfl⟩ : syracuseStep 4147109 = 777583) (by norm_num)
theorem B2762669 : Blo 1841622 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B1968061 : Blo 1841622 1968061 := bbase (se 3 (by rfl) ⟨369011, by rfl⟩ : syracuseStep 1968061 = 738023) (by norm_num)
theorem B2525117 : Blo 1841622 2525117 := bbase (se 3 (by rfl) ⟨473459, by rfl⟩ : syracuseStep 2525117 = 946919) (by norm_num)
theorem B2762693 : Blo 1841622 2762693 := bbase (se 4 (by rfl) ⟨259002, by rfl⟩ : syracuseStep 2762693 = 518005) (by norm_num)
theorem B2762717 : Blo 1841622 2762717 := bbase (se 3 (by rfl) ⟨518009, by rfl⟩ : syracuseStep 2762717 = 1036019) (by norm_num)
theorem B4147181 : Blo 1841622 4147181 := bbase (se 3 (by rfl) ⟨777596, by rfl⟩ : syracuseStep 4147181 = 1555193) (by norm_num)
theorem B2762741 : Blo 1841622 2762741 := bbase (se 5 (by rfl) ⟨129503, by rfl⟩ : syracuseStep 2762741 = 259007) (by norm_num)
theorem B6998021 : Blo 1841622 6998021 := bbase (se 4 (by rfl) ⟨656064, by rfl⟩ : syracuseStep 6998021 = 1312129) (by norm_num)
theorem B2762765 : Blo 1841622 2762765 := bbase (se 3 (by rfl) ⟨518018, by rfl⟩ : syracuseStep 2762765 = 1036037) (by norm_num)
theorem B2762789 : Blo 1841622 2762789 := bbase (se 4 (by rfl) ⟨259011, by rfl⟩ : syracuseStep 2762789 = 518023) (by norm_num)
theorem B4147253 : Blo 1841622 4147253 := bbase (se 5 (by rfl) ⟨194402, by rfl⟩ : syracuseStep 4147253 = 388805) (by norm_num)
theorem B2762813 : Blo 1841622 2762813 := bbase (se 3 (by rfl) ⟨518027, by rfl⟩ : syracuseStep 2762813 = 1036055) (by norm_num)
theorem B2762837 : Blo 1841622 2762837 := bbase (se 8 (by rfl) ⟨16188, by rfl⟩ : syracuseStep 2762837 = 32377) (by norm_num)
theorem B2762861 : Blo 1841622 2762861 := bbase (se 3 (by rfl) ⟨518036, by rfl⟩ : syracuseStep 2762861 = 1036073) (by norm_num)
theorem B4147325 : Blo 1841622 4147325 := bbase (se 3 (by rfl) ⟨777623, by rfl⟩ : syracuseStep 4147325 = 1555247) (by norm_num)
theorem B2762885 : Blo 1841622 2762885 := bbase (se 4 (by rfl) ⟨259020, by rfl⟩ : syracuseStep 2762885 = 518041) (by norm_num)
theorem B2623637 : Blo 1841622 2623637 := bbase (se 6 (by rfl) ⟨61491, by rfl⟩ : syracuseStep 2623637 = 122983) (by norm_num)
theorem B2762909 : Blo 1841622 2762909 := bbase (se 3 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 2762909 = 1036091) (by norm_num)
theorem B4663453 : Blo 1841622 4663453 := bbase (se 3 (by rfl) ⟨874397, by rfl⟩ : syracuseStep 4663453 = 1748795) (by norm_num)
theorem B2762933 : Blo 1841622 2762933 := bbase (se 5 (by rfl) ⟨129512, by rfl⟩ : syracuseStep 2762933 = 259025) (by norm_num)
theorem B4147397 : Blo 1841622 4147397 := bbase (se 4 (by rfl) ⟨388818, by rfl⟩ : syracuseStep 4147397 = 777637) (by norm_num)
theorem B2762957 : Blo 1841622 2762957 := bbase (se 3 (by rfl) ⟨518054, by rfl⟩ : syracuseStep 2762957 = 1036109) (by norm_num)
theorem B59746517 : Blo 1841622 59746517 := bbase (se 7 (by rfl) ⟨700154, by rfl⟩ : syracuseStep 59746517 = 1400309) (by norm_num)
theorem B6219989 : Blo 1841622 6219989 := bbase (se 7 (by rfl) ⟨72890, by rfl⟩ : syracuseStep 6219989 = 145781) (by norm_num)
theorem B2762981 : Blo 1841622 2762981 := bbase (se 4 (by rfl) ⟨259029, by rfl⟩ : syracuseStep 2762981 = 518059) (by norm_num)
theorem B4983029 : Blo 1841622 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B9332981 : Blo 1841622 9332981 := bbase (se 5 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 9332981 = 874967) (by norm_num)
theorem B2763005 : Blo 1841622 2763005 := bbase (se 3 (by rfl) ⟨518063, by rfl⟩ : syracuseStep 2763005 = 1036127) (by norm_num)
theorem B4663565 : Blo 1841622 4663565 := bbase (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) (by norm_num)
theorem B4147469 : Blo 1841622 4147469 := bbase (se 3 (by rfl) ⟨777650, by rfl⟩ : syracuseStep 4147469 = 1555301) (by norm_num)
theorem B2763029 : Blo 1841622 2763029 := bbase (se 6 (by rfl) ⟨64758, by rfl⟩ : syracuseStep 2763029 = 129517) (by norm_num)
theorem B6998309 : Blo 1841622 6998309 := bbase (se 4 (by rfl) ⟨656091, by rfl⟩ : syracuseStep 6998309 = 1312183) (by norm_num)
theorem B2763053 : Blo 1841622 2763053 := bbase (se 3 (by rfl) ⟨518072, by rfl⟩ : syracuseStep 2763053 = 1036145) (by norm_num)
theorem B3320117 : Blo 1841622 3320117 := bbase (se 5 (by rfl) ⟨155630, by rfl⟩ : syracuseStep 3320117 = 311261) (by norm_num)
theorem B2763077 : Blo 1841622 2763077 := bbase (se 4 (by rfl) ⟨259038, by rfl⟩ : syracuseStep 2763077 = 518077) (by norm_num)
theorem B4426061 : Blo 1841622 4426061 := bbase (se 3 (by rfl) ⟨829886, by rfl⟩ : syracuseStep 4426061 = 1659773) (by norm_num)
theorem B4147541 : Blo 1841622 4147541 := bbase (se 10 (by rfl) ⟨6075, by rfl⟩ : syracuseStep 4147541 = 12151) (by norm_num)
theorem B4983125 : Blo 1841622 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B2763101 : Blo 1841622 2763101 := bbase (se 3 (by rfl) ⟨518081, by rfl⟩ : syracuseStep 2763101 = 1036163) (by norm_num)
theorem B2763125 : Blo 1841622 2763125 := bbase (se 5 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 2763125 = 259043) (by norm_num)
theorem B1968505 : Blo 1841622 1968505 := bbase (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) (by norm_num)
theorem B2763149 : Blo 1841622 2763149 := bbase (se 3 (by rfl) ⟨518090, by rfl⟩ : syracuseStep 2763149 = 1036181) (by norm_num)
theorem B12954005 : Blo 1841622 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B4147613 : Blo 1841622 4147613 := bbase (se 3 (by rfl) ⟨777677, by rfl⟩ : syracuseStep 4147613 = 1555355) (by norm_num)
theorem B2763173 : Blo 1841622 2763173 := bbase (se 4 (by rfl) ⟨259047, by rfl⟩ : syracuseStep 2763173 = 518095) (by norm_num)
theorem B2763197 : Blo 1841622 2763197 := bbase (se 3 (by rfl) ⟨518099, by rfl⟩ : syracuseStep 2763197 = 1036199) (by norm_num)
theorem B4663757 : Blo 1841622 4663757 := bbase (se 3 (by rfl) ⟨874454, by rfl⟩ : syracuseStep 4663757 = 1748909) (by norm_num)
theorem B2763221 : Blo 1841622 2763221 := bbase (se 7 (by rfl) ⟨32381, by rfl⟩ : syracuseStep 2763221 = 64763) (by norm_num)
theorem B8849893 : Blo 1841622 8849893 := bbase (se 4 (by rfl) ⟨829677, by rfl⟩ : syracuseStep 8849893 = 1659355) (by norm_num)
theorem B4147685 : Blo 1841622 4147685 := bbase (se 4 (by rfl) ⟨388845, by rfl⟩ : syracuseStep 4147685 = 777691) (by norm_num)
theorem B2763245 : Blo 1841622 2763245 := bbase (se 3 (by rfl) ⟨518108, by rfl⟩ : syracuseStep 2763245 = 1036217) (by norm_num)
theorem B1968625 : Blo 1841622 1968625 := bbase (se 2 (by rfl) ⟨738234, by rfl⟩ : syracuseStep 1968625 = 1476469) (by norm_num)
theorem B5900789 : Blo 1841622 5900789 := bbase (se 5 (by rfl) ⟨276599, by rfl⟩ : syracuseStep 5900789 = 553199) (by norm_num)
theorem B7473653 : Blo 1841622 7473653 := bbase (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) (by norm_num)
theorem B2763269 : Blo 1841622 2763269 := bbase (se 4 (by rfl) ⟨259056, by rfl⟩ : syracuseStep 2763269 = 518113) (by norm_num)
theorem B28355093 : Blo 1841622 28355093 := bbase (se 6 (by rfl) ⟨664572, by rfl⟩ : syracuseStep 28355093 = 1329145) (by norm_num)
theorem B2214425 : Blo 1841622 2214425 := bbase (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) (by norm_num)
theorem B2763293 : Blo 1841622 2763293 := bbase (se 3 (by rfl) ⟨518117, by rfl⟩ : syracuseStep 2763293 = 1036235) (by norm_num)
theorem B4147757 : Blo 1841622 4147757 := bbase (se 3 (by rfl) ⟨777704, by rfl⟩ : syracuseStep 4147757 = 1555409) (by norm_num)
theorem B2763317 : Blo 1841622 2763317 := bbase (se 5 (by rfl) ⟨129530, by rfl⟩ : syracuseStep 2763317 = 259061) (by norm_num)
theorem B2763341 : Blo 1841622 2763341 := bbase (se 3 (by rfl) ⟨518126, by rfl⟩ : syracuseStep 2763341 = 1036253) (by norm_num)
theorem B2763365 : Blo 1841622 2763365 := bbase (se 4 (by rfl) ⟨259065, by rfl⟩ : syracuseStep 2763365 = 518131) (by norm_num)
theorem B2951797 : Blo 1841622 2951797 := bbase (se 5 (by rfl) ⟨138365, by rfl⟩ : syracuseStep 2951797 = 276731) (by norm_num)
theorem B4147829 : Blo 1841622 4147829 := bbase (se 5 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 4147829 = 388859) (by norm_num)
theorem B2763389 : Blo 1841622 2763389 := bbase (se 3 (by rfl) ⟨518135, by rfl⟩ : syracuseStep 2763389 = 1036271) (by norm_num)
theorem B6220421 : Blo 1841622 6220421 := bbase (se 4 (by rfl) ⟨583164, by rfl⟩ : syracuseStep 6220421 = 1166329) (by norm_num)
theorem B9325205 : Blo 1841622 9325205 := bbase (se 6 (by rfl) ⟨218559, by rfl⟩ : syracuseStep 9325205 = 437119) (by norm_num)
theorem B2763413 : Blo 1841622 2763413 := bbase (se 6 (by rfl) ⟨64767, by rfl⟩ : syracuseStep 2763413 = 129535) (by norm_num)
theorem B2763437 : Blo 1841622 2763437 := bbase (se 3 (by rfl) ⟨518144, by rfl⟩ : syracuseStep 2763437 = 1036289) (by norm_num)
theorem B7473845 : Blo 1841622 7473845 := bbase (se 5 (by rfl) ⟨350336, by rfl⟩ : syracuseStep 7473845 = 700673) (by norm_num)
theorem B3934909 : Blo 1841622 3934909 := bbase (se 3 (by rfl) ⟨737795, by rfl⟩ : syracuseStep 3934909 = 1475591) (by norm_num)
theorem B4147901 : Blo 1841622 4147901 := bbase (se 3 (by rfl) ⟨777731, by rfl⟩ : syracuseStep 4147901 = 1555463) (by norm_num)
theorem B2763461 : Blo 1841622 2763461 := bbase (se 4 (by rfl) ⟨259074, by rfl⟩ : syracuseStep 2763461 = 518149) (by norm_num)
theorem B2763485 : Blo 1841622 2763485 := bbase (se 3 (by rfl) ⟨518153, by rfl⟩ : syracuseStep 2763485 = 1036307) (by norm_num)
theorem B2763509 : Blo 1841622 2763509 := bbase (se 5 (by rfl) ⟨129539, by rfl⟩ : syracuseStep 2763509 = 259079) (by norm_num)
theorem B4147973 : Blo 1841622 4147973 := bbase (se 4 (by rfl) ⟨388872, by rfl⟩ : syracuseStep 4147973 = 777745) (by norm_num)
theorem B2763533 : Blo 1841622 2763533 := bbase (se 3 (by rfl) ⟨518162, by rfl⟩ : syracuseStep 2763533 = 1036325) (by norm_num)
theorem B2763557 : Blo 1841622 2763557 := bbase (se 4 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 2763557 = 518167) (by norm_num)
theorem B4664101 : Blo 1841622 4664101 := bbase (se 4 (by rfl) ⟨437259, by rfl⟩ : syracuseStep 4664101 = 874519) (by norm_num)
theorem B2763581 : Blo 1841622 2763581 := bbase (se 3 (by rfl) ⟨518171, by rfl⟩ : syracuseStep 2763581 = 1036343) (by norm_num)
theorem B4148045 : Blo 1841622 4148045 := bbase (se 3 (by rfl) ⟨777758, by rfl⟩ : syracuseStep 4148045 = 1555517) (by norm_num)
theorem B2763605 : Blo 1841622 2763605 := bbase (se 9 (by rfl) ⟨8096, by rfl⟩ : syracuseStep 2763605 = 16193) (by norm_num)
theorem B2763629 : Blo 1841622 2763629 := bbase (se 3 (by rfl) ⟨518180, by rfl⟩ : syracuseStep 2763629 = 1036361) (by norm_num)
theorem B2763653 : Blo 1841622 2763653 := bbase (se 4 (by rfl) ⟨259092, by rfl⟩ : syracuseStep 2763653 = 518185) (by norm_num)
theorem B4664213 : Blo 1841622 4664213 := bbase (se 6 (by rfl) ⟨109317, by rfl⟩ : syracuseStep 4664213 = 218635) (by norm_num)
theorem B4148117 : Blo 1841622 4148117 := bbase (se 6 (by rfl) ⟨97221, by rfl⟩ : syracuseStep 4148117 = 194443) (by norm_num)
theorem B2763677 : Blo 1841622 2763677 := bbase (se 3 (by rfl) ⟨518189, by rfl⟩ : syracuseStep 2763677 = 1036379) (by norm_num)
theorem B5606309 : Blo 1841622 5606309 := bbase (se 4 (by rfl) ⟨525591, by rfl⟩ : syracuseStep 5606309 = 1051183) (by norm_num)
theorem B2763701 : Blo 1841622 2763701 := bbase (se 5 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 2763701 = 259097) (by norm_num)
theorem B2763725 : Blo 1841622 2763725 := bbase (se 3 (by rfl) ⟨518198, by rfl⟩ : syracuseStep 2763725 = 1036397) (by norm_num)
theorem B2763749 : Blo 1841622 2763749 := bbase (se 4 (by rfl) ⟨259101, by rfl⟩ : syracuseStep 2763749 = 518203) (by norm_num)
theorem B3107821 : Blo 1841622 3107821 := bbase (se 3 (by rfl) ⟨582716, by rfl⟩ : syracuseStep 3107821 = 1165433) (by norm_num)
theorem B2763773 : Blo 1841622 2763773 := bbase (se 3 (by rfl) ⟨518207, by rfl⟩ : syracuseStep 2763773 = 1036415) (by norm_num)
theorem B2763797 : Blo 1841622 2763797 := bbase (se 6 (by rfl) ⟨64776, by rfl⟩ : syracuseStep 2763797 = 129553) (by norm_num)
theorem B2763821 : Blo 1841622 2763821 := bbase (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) (by norm_num)
theorem B2952245 : Blo 1841622 2952245 := bbase (se 5 (by rfl) ⟨138386, by rfl⟩ : syracuseStep 2952245 = 276773) (by norm_num)
theorem B6220853 : Blo 1841622 6220853 := bbase (se 5 (by rfl) ⟨291602, by rfl⟩ : syracuseStep 6220853 = 583205) (by norm_num)
theorem B3107909 : Blo 1841622 3107909 := bbase (se 4 (by rfl) ⟨291366, by rfl⟩ : syracuseStep 3107909 = 582733) (by norm_num)
theorem B5246021 : Blo 1841622 5246021 := bbase (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) (by norm_num)
theorem B2763845 : Blo 1841622 2763845 := bbase (se 4 (by rfl) ⟨259110, by rfl⟩ : syracuseStep 2763845 = 518221) (by norm_num)
theorem B4664405 : Blo 1841622 4664405 := bbase (se 8 (by rfl) ⟨27330, by rfl⟩ : syracuseStep 4664405 = 54661) (by norm_num)
theorem B2763869 : Blo 1841622 2763869 := bbase (se 3 (by rfl) ⟨518225, by rfl⟩ : syracuseStep 2763869 = 1036451) (by norm_num)
theorem B2763893 : Blo 1841622 2763893 := bbase (se 5 (by rfl) ⟨129557, by rfl⟩ : syracuseStep 2763893 = 259115) (by norm_num)
theorem B2763917 : Blo 1841622 2763917 := bbase (se 3 (by rfl) ⟨518234, by rfl⟩ : syracuseStep 2763917 = 1036469) (by norm_num)
theorem B2763941 : Blo 1841622 2763941 := bbase (se 4 (by rfl) ⟨259119, by rfl⟩ : syracuseStep 2763941 = 518239) (by norm_num)
theorem B3935405 : Blo 1841622 3935405 := bbase (se 3 (by rfl) ⟨737888, by rfl⟩ : syracuseStep 3935405 = 1475777) (by norm_num)
theorem B10489013 : Blo 1841622 10489013 := bbase (se 5 (by rfl) ⟨491672, by rfl⟩ : syracuseStep 10489013 = 983345) (by norm_num)
theorem B2763965 : Blo 1841622 2763965 := bbase (se 3 (by rfl) ⟨518243, by rfl⟩ : syracuseStep 2763965 = 1036487) (by norm_num)
theorem B3108037 : Blo 1841622 3108037 := bbase (se 4 (by rfl) ⟨291378, by rfl⟩ : syracuseStep 3108037 = 582757) (by norm_num)
theorem B2763989 : Blo 1841622 2763989 := bbase (se 7 (by rfl) ⟨32390, by rfl⟩ : syracuseStep 2763989 = 64781) (by norm_num)
theorem B2764013 : Blo 1841622 2764013 := bbase (se 3 (by rfl) ⟨518252, by rfl⟩ : syracuseStep 2764013 = 1036505) (by norm_num)
theorem B2952445 : Blo 1841622 2952445 := bbase (se 3 (by rfl) ⟨553583, by rfl⟩ : syracuseStep 2952445 = 1107167) (by norm_num)
theorem B2764037 : Blo 1841622 2764037 := bbase (se 4 (by rfl) ⟨259128, by rfl⟩ : syracuseStep 2764037 = 518257) (by norm_num)
theorem B3108125 : Blo 1841622 3108125 := bbase (se 3 (by rfl) ⟨582773, by rfl⟩ : syracuseStep 3108125 = 1165547) (by norm_num)
theorem B2764061 : Blo 1841622 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B2362657 : Blo 1841622 2362657 := bbase (se 2 (by rfl) ⟨885996, by rfl⟩ : syracuseStep 2362657 = 1771993) (by norm_num)
theorem B2764085 : Blo 1841622 2764085 := bbase (se 5 (by rfl) ⟨129566, by rfl⟩ : syracuseStep 2764085 = 259133) (by norm_num)
theorem B2764109 : Blo 1841622 2764109 := bbase (se 3 (by rfl) ⟨518270, by rfl⟩ : syracuseStep 2764109 = 1036541) (by norm_num)
theorem B2764133 : Blo 1841622 2764133 := bbase (se 4 (by rfl) ⟨259137, by rfl⟩ : syracuseStep 2764133 = 518275) (by norm_num)
theorem B2764157 : Blo 1841622 2764157 := bbase (se 3 (by rfl) ⟨518279, by rfl⟩ : syracuseStep 2764157 = 1036559) (by norm_num)
theorem B2764181 : Blo 1841622 2764181 := bbase (se 6 (by rfl) ⟨64785, by rfl⟩ : syracuseStep 2764181 = 129571) (by norm_num)
theorem B20999573 : Blo 1841622 20999573 := bbase (se 6 (by rfl) ⟨492177, by rfl⟩ : syracuseStep 20999573 = 984355) (by norm_num)
theorem B3108253 : Blo 1841622 3108253 := bbase (se 3 (by rfl) ⟨582797, by rfl⟩ : syracuseStep 3108253 = 1165595) (by norm_num)
theorem B2764205 : Blo 1841622 2764205 := bbase (se 3 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 2764205 = 1036577) (by norm_num)
theorem B4664749 : Blo 1841622 4664749 := bbase (se 3 (by rfl) ⟨874640, by rfl⟩ : syracuseStep 4664749 = 1749281) (by norm_num)
theorem B2764229 : Blo 1841622 2764229 := bbase (se 4 (by rfl) ⟨259146, by rfl⟩ : syracuseStep 2764229 = 518293) (by norm_num)
theorem B6999493 : Blo 1841622 6999493 := bbase (se 4 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 6999493 = 1312405) (by norm_num)
theorem B2764253 : Blo 1841622 2764253 := bbase (se 3 (by rfl) ⟨518297, by rfl⟩ : syracuseStep 2764253 = 1036595) (by norm_num)
theorem B6221285 : Blo 1841622 6221285 := bbase (se 4 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 6221285 = 1166491) (by norm_num)
theorem B3108341 : Blo 1841622 3108341 := bbase (se 5 (by rfl) ⟨145703, by rfl⟩ : syracuseStep 3108341 = 291407) (by norm_num)
theorem B2764277 : Blo 1841622 2764277 := bbase (se 5 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 2764277 = 259151) (by norm_num)
theorem B2952701 : Blo 1841622 2952701 := bbase (se 3 (by rfl) ⟨553631, by rfl⟩ : syracuseStep 2952701 = 1107263) (by norm_num)
theorem B2764301 : Blo 1841622 2764301 := bbase (se 3 (by rfl) ⟨518306, by rfl⟩ : syracuseStep 2764301 = 1036613) (by norm_num)
theorem B4664861 : Blo 1841622 4664861 := bbase (se 3 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 4664861 = 1749323) (by norm_num)
theorem B2428453 : Blo 1841622 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B2764325 : Blo 1841622 2764325 := bbase (se 4 (by rfl) ⟨259155, by rfl⟩ : syracuseStep 2764325 = 518311) (by norm_num)
theorem B2764349 : Blo 1841622 2764349 := bbase (se 3 (by rfl) ⟨518315, by rfl⟩ : syracuseStep 2764349 = 1036631) (by norm_num)
theorem B2764373 : Blo 1841622 2764373 := bbase (se 8 (by rfl) ⟨16197, by rfl⟩ : syracuseStep 2764373 = 32395) (by norm_num)
theorem B2764397 : Blo 1841622 2764397 := bbase (se 3 (by rfl) ⟨518324, by rfl⟩ : syracuseStep 2764397 = 1036649) (by norm_num)
theorem B3108469 : Blo 1841622 3108469 := bbase (se 5 (by rfl) ⟨145709, by rfl⟩ : syracuseStep 3108469 = 291419) (by norm_num)
theorem B2764421 : Blo 1841622 2764421 := bbase (se 4 (by rfl) ⟨259164, by rfl⟩ : syracuseStep 2764421 = 518329) (by norm_num)
theorem B2764445 : Blo 1841622 2764445 := bbase (se 3 (by rfl) ⟨518333, by rfl⟩ : syracuseStep 2764445 = 1036667) (by norm_num)
theorem B2764469 : Blo 1841622 2764469 := bbase (se 5 (by rfl) ⟨129584, by rfl⟩ : syracuseStep 2764469 = 259169) (by norm_num)
theorem B7573189 : Blo 1841622 7573189 := bbase (se 4 (by rfl) ⟨709986, by rfl⟩ : syracuseStep 7573189 = 1419973) (by norm_num)
theorem B3108557 : Blo 1841622 3108557 := bbase (se 3 (by rfl) ⟨582854, by rfl⟩ : syracuseStep 3108557 = 1165709) (by norm_num)
theorem B2764493 : Blo 1841622 2764493 := bbase (se 3 (by rfl) ⟨518342, by rfl⟩ : syracuseStep 2764493 = 1036685) (by norm_num)
theorem B4665053 : Blo 1841622 4665053 := bbase (se 3 (by rfl) ⟨874697, by rfl⟩ : syracuseStep 4665053 = 1749395) (by norm_num)
theorem B2764517 : Blo 1841622 2764517 := bbase (se 4 (by rfl) ⟨259173, by rfl⟩ : syracuseStep 2764517 = 518347) (by norm_num)
theorem B6999797 : Blo 1841622 6999797 := bbase (se 5 (by rfl) ⟨328115, by rfl⟩ : syracuseStep 6999797 = 656231) (by norm_num)
theorem B2764541 : Blo 1841622 2764541 := bbase (se 3 (by rfl) ⟨518351, by rfl⟩ : syracuseStep 2764541 = 1036703) (by norm_num)
theorem B2100997 : Blo 1841622 2100997 := bbase (se 4 (by rfl) ⟨196968, by rfl⟩ : syracuseStep 2100997 = 393937) (by norm_num)
theorem B2764565 : Blo 1841622 2764565 := bbase (se 6 (by rfl) ⟨64794, by rfl⟩ : syracuseStep 2764565 = 129589) (by norm_num)
theorem B2764589 : Blo 1841622 2764589 := bbase (se 3 (by rfl) ⟨518360, by rfl⟩ : syracuseStep 2764589 = 1036721) (by norm_num)
theorem B2764613 : Blo 1841622 2764613 := bbase (se 4 (by rfl) ⟨259182, by rfl⟩ : syracuseStep 2764613 = 518365) (by norm_num)
theorem B3108685 : Blo 1841622 3108685 := bbase (se 3 (by rfl) ⟨582878, by rfl⟩ : syracuseStep 3108685 = 1165757) (by norm_num)
theorem B2764637 : Blo 1841622 2764637 := bbase (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) (by norm_num)
theorem B2764661 : Blo 1841622 2764661 := bbase (se 5 (by rfl) ⟨129593, by rfl⟩ : syracuseStep 2764661 = 259187) (by norm_num)
theorem B2764685 : Blo 1841622 2764685 := bbase (se 3 (by rfl) ⟨518378, by rfl⟩ : syracuseStep 2764685 = 1036757) (by norm_num)
theorem B6221717 : Blo 1841622 6221717 := bbase (se 6 (by rfl) ⟨145821, by rfl⟩ : syracuseStep 6221717 = 291643) (by norm_num)
theorem B3108773 : Blo 1841622 3108773 := bbase (se 4 (by rfl) ⟨291447, by rfl⟩ : syracuseStep 3108773 = 582895) (by norm_num)
theorem B9326501 : Blo 1841622 9326501 := bbase (se 4 (by rfl) ⟨874359, by rfl⟩ : syracuseStep 9326501 = 1748719) (by norm_num)
theorem B2764709 : Blo 1841622 2764709 := bbase (se 4 (by rfl) ⟨259191, by rfl⟩ : syracuseStep 2764709 = 518383) (by norm_num)
theorem B2764733 : Blo 1841622 2764733 := bbase (se 3 (by rfl) ⟨518387, by rfl⟩ : syracuseStep 2764733 = 1036775) (by norm_num)
theorem B2764757 : Blo 1841622 2764757 := bbase (se 7 (by rfl) ⟨32399, by rfl⟩ : syracuseStep 2764757 = 64799) (by norm_num)
theorem B2764781 : Blo 1841622 2764781 := bbase (se 3 (by rfl) ⟨518396, by rfl⟩ : syracuseStep 2764781 = 1036793) (by norm_num)
theorem B2764805 : Blo 1841622 2764805 := bbase (se 4 (by rfl) ⟨259200, by rfl⟩ : syracuseStep 2764805 = 518401) (by norm_num)
theorem B2764829 : Blo 1841622 2764829 := bbase (se 3 (by rfl) ⟨518405, by rfl⟩ : syracuseStep 2764829 = 1036811) (by norm_num)
theorem B3108901 : Blo 1841622 3108901 := bbase (se 4 (by rfl) ⟨291459, by rfl⟩ : syracuseStep 3108901 = 582919) (by norm_num)
theorem B3936293 : Blo 1841622 3936293 := bbase (se 4 (by rfl) ⟨369027, by rfl⟩ : syracuseStep 3936293 = 738055) (by norm_num)
theorem B4427821 : Blo 1841622 4427821 := bbase (se 3 (by rfl) ⟨830216, by rfl⟩ : syracuseStep 4427821 = 1660433) (by norm_num)
theorem B4665397 : Blo 1841622 4665397 := bbase (se 5 (by rfl) ⟨218690, by rfl⟩ : syracuseStep 4665397 = 437381) (by norm_num)
theorem B2764853 : Blo 1841622 2764853 := bbase (se 5 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 2764853 = 259205) (by norm_num)
theorem B2764877 : Blo 1841622 2764877 := bbase (se 3 (by rfl) ⟨518414, by rfl⟩ : syracuseStep 2764877 = 1036829) (by norm_num)
theorem B2764901 : Blo 1841622 2764901 := bbase (se 4 (by rfl) ⟨259209, by rfl⟩ : syracuseStep 2764901 = 518419) (by norm_num)
theorem B3108989 : Blo 1841622 3108989 := bbase (se 3 (by rfl) ⟨582935, by rfl⟩ : syracuseStep 3108989 = 1165871) (by norm_num)
theorem B2764925 : Blo 1841622 2764925 := bbase (se 3 (by rfl) ⟨518423, by rfl⟩ : syracuseStep 2764925 = 1036847) (by norm_num)
theorem B2764949 : Blo 1841622 2764949 := bbase (se 6 (by rfl) ⟨64803, by rfl⟩ : syracuseStep 2764949 = 129607) (by norm_num)
theorem B3936413 : Blo 1841622 3936413 := bbase (se 3 (by rfl) ⟨738077, by rfl⟩ : syracuseStep 3936413 = 1476155) (by norm_num)
theorem B4665509 : Blo 1841622 4665509 := bbase (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) (by norm_num)
theorem B2764973 : Blo 1841622 2764973 := bbase (se 3 (by rfl) ⟨518432, by rfl⟩ : syracuseStep 2764973 = 1036865) (by norm_num)
theorem B2764997 : Blo 1841622 2764997 := bbase (se 4 (by rfl) ⟨259218, by rfl⟩ : syracuseStep 2764997 = 518437) (by norm_num)
theorem B2101453 : Blo 1841622 2101453 := bbase (se 3 (by rfl) ⟨394022, by rfl⟩ : syracuseStep 2101453 = 788045) (by norm_num)
theorem B2765021 : Blo 1841622 2765021 := bbase (se 3 (by rfl) ⟨518441, by rfl⟩ : syracuseStep 2765021 = 1036883) (by norm_num)
theorem B2765045 : Blo 1841622 2765045 := bbase (se 5 (by rfl) ⟨129611, by rfl⟩ : syracuseStep 2765045 = 259223) (by norm_num)
theorem B3109117 : Blo 1841622 3109117 := bbase (se 3 (by rfl) ⟨582959, by rfl⟩ : syracuseStep 3109117 = 1165919) (by norm_num)
theorem B2765069 : Blo 1841622 2765069 := bbase (se 3 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 2765069 = 1036901) (by norm_num)
theorem B4428053 : Blo 1841622 4428053 := bbase (se 6 (by rfl) ⟨103782, by rfl⟩ : syracuseStep 4428053 = 207565) (by norm_num)
theorem B2765093 : Blo 1841622 2765093 := bbase (se 4 (by rfl) ⟨259227, by rfl⟩ : syracuseStep 2765093 = 518455) (by norm_num)
theorem B5902645 : Blo 1841622 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B2765117 : Blo 1841622 2765117 := bbase (se 3 (by rfl) ⟨518459, by rfl⟩ : syracuseStep 2765117 = 1036919) (by norm_num)
theorem B6222149 : Blo 1841622 6222149 := bbase (se 4 (by rfl) ⟨583326, by rfl⟩ : syracuseStep 6222149 = 1166653) (by norm_num)
theorem B2330957 : Blo 1841622 2330957 := bbase (se 3 (by rfl) ⟨437054, by rfl⟩ : syracuseStep 2330957 = 874109) (by norm_num)
theorem B3109205 : Blo 1841622 3109205 := bbase (se 10 (by rfl) ⟨4554, by rfl⟩ : syracuseStep 3109205 = 9109) (by norm_num)
theorem B75657557 : Blo 1841622 75657557 := bbase (se 10 (by rfl) ⟨110826, by rfl⟩ : syracuseStep 75657557 = 221653) (by norm_num)
theorem B2765141 : Blo 1841622 2765141 := bbase (se 10 (by rfl) ⟨4050, by rfl⟩ : syracuseStep 2765141 = 8101) (by norm_num)
theorem B4665701 : Blo 1841622 4665701 := bbase (se 4 (by rfl) ⟨437409, by rfl⟩ : syracuseStep 4665701 = 874819) (by norm_num)
theorem B2765165 : Blo 1841622 2765165 := bbase (se 3 (by rfl) ⟨518468, by rfl⟩ : syracuseStep 2765165 = 1036937) (by norm_num)
theorem B2331013 : Blo 1841622 2331013 := bbase (se 4 (by rfl) ⟨218532, by rfl⟩ : syracuseStep 2331013 = 437065) (by norm_num)
theorem B2765189 : Blo 1841622 2765189 := bbase (se 4 (by rfl) ⟨259236, by rfl⟩ : syracuseStep 2765189 = 518473) (by norm_num)
theorem B22409621 : Blo 1841622 22409621 := bbase (se 6 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 22409621 = 1050451) (by norm_num)
theorem B2765213 : Blo 1841622 2765213 := bbase (se 3 (by rfl) ⟨518477, by rfl⟩ : syracuseStep 2765213 = 1036955) (by norm_num)
theorem B2101673 : Blo 1841622 2101673 := bbase (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) (by norm_num)
theorem B2765237 : Blo 1841622 2765237 := bbase (se 5 (by rfl) ⟨129620, by rfl⟩ : syracuseStep 2765237 = 259241) (by norm_num)
theorem B2765261 : Blo 1841622 2765261 := bbase (se 3 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 2765261 = 1036973) (by norm_num)
theorem B3109333 : Blo 1841622 3109333 := bbase (se 7 (by rfl) ⟨36437, by rfl⟩ : syracuseStep 3109333 = 72875) (by norm_num)
theorem B2331109 : Blo 1841622 2331109 := bbase (se 4 (by rfl) ⟨218541, by rfl⟩ : syracuseStep 2331109 = 437083) (by norm_num)
theorem B2765285 : Blo 1841622 2765285 := bbase (se 4 (by rfl) ⟨259245, by rfl⟩ : syracuseStep 2765285 = 518491) (by norm_num)
theorem B2765309 : Blo 1841622 2765309 := bbase (se 3 (by rfl) ⟨518495, by rfl⟩ : syracuseStep 2765309 = 1036991) (by norm_num)
theorem B2765333 : Blo 1841622 2765333 := bbase (se 6 (by rfl) ⟨64812, by rfl⟩ : syracuseStep 2765333 = 129625) (by norm_num)
theorem B3109421 : Blo 1841622 3109421 := bbase (se 3 (by rfl) ⟨583016, by rfl⟩ : syracuseStep 3109421 = 1166033) (by norm_num)
theorem B2765357 : Blo 1841622 2765357 := bbase (se 3 (by rfl) ⟨518504, by rfl⟩ : syracuseStep 2765357 = 1037009) (by norm_num)
theorem B2429509 : Blo 1841622 2429509 := bbase (se 4 (by rfl) ⟨227766, by rfl⟩ : syracuseStep 2429509 = 455533) (by norm_num)
theorem B2765381 : Blo 1841622 2765381 := bbase (se 4 (by rfl) ⟨259254, by rfl⟩ : syracuseStep 2765381 = 518509) (by norm_num)
theorem B1995337 : Blo 1841622 1995337 := bbase (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) (by norm_num)
theorem B2765405 : Blo 1841622 2765405 := bbase (se 3 (by rfl) ⟨518513, by rfl⟩ : syracuseStep 2765405 = 1037027) (by norm_num)
theorem B5247605 : Blo 1841622 5247605 := bbase (se 5 (by rfl) ⟨245981, by rfl⟩ : syracuseStep 5247605 = 491963) (by norm_num)
theorem B2765429 : Blo 1841622 2765429 := bbase (se 5 (by rfl) ⟨129629, by rfl⟩ : syracuseStep 2765429 = 259259) (by norm_num)
theorem B3592837 : Blo 1841622 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B6730373 : Blo 1841622 6730373 := bbase (se 4 (by rfl) ⟨630972, by rfl⟩ : syracuseStep 6730373 = 1261945) (by norm_num)
theorem B2331281 : Blo 1841622 2331281 := bbase (se 2 (by rfl) ⟨874230, by rfl⟩ : syracuseStep 2331281 = 1748461) (by norm_num)
theorem B4428445 : Blo 1841622 4428445 := bbase (se 3 (by rfl) ⟨830333, by rfl⟩ : syracuseStep 4428445 = 1660667) (by norm_num)
theorem B3109549 : Blo 1841622 3109549 := bbase (se 3 (by rfl) ⟨583040, by rfl⟩ : syracuseStep 3109549 = 1166081) (by norm_num)
theorem B4666045 : Blo 1841622 4666045 := bbase (se 3 (by rfl) ⟨874883, by rfl⟩ : syracuseStep 4666045 = 1749767) (by norm_num)
theorem B2331337 : Blo 1841622 2331337 := bbase (se 2 (by rfl) ⟨874251, by rfl⟩ : syracuseStep 2331337 = 1748503) (by norm_num)
theorem B2101997 : Blo 1841622 2101997 := bbase (se 3 (by rfl) ⟨394124, by rfl⟩ : syracuseStep 2101997 = 788249) (by norm_num)
theorem B3109637 : Blo 1841622 3109637 := bbase (se 4 (by rfl) ⟨291528, by rfl⟩ : syracuseStep 3109637 = 583057) (by norm_num)
theorem B7467797 : Blo 1841622 7467797 := bbase (se 6 (by rfl) ⟨175026, by rfl⟩ : syracuseStep 7467797 = 350053) (by norm_num)
theorem B3937045 : Blo 1841622 3937045 := bbase (se 6 (by rfl) ⟨92274, by rfl⟩ : syracuseStep 3937045 = 184549) (by norm_num)
theorem B7869221 : Blo 1841622 7869221 := bbase (se 4 (by rfl) ⟨737739, by rfl⟩ : syracuseStep 7869221 = 1475479) (by norm_num)
theorem B2331433 : Blo 1841622 2331433 := bbase (se 2 (by rfl) ⟨874287, by rfl⟩ : syracuseStep 2331433 = 1748575) (by norm_num)
theorem B4666157 : Blo 1841622 4666157 := bbase (se 3 (by rfl) ⟨874904, by rfl⟩ : syracuseStep 4666157 = 1749809) (by norm_num)
theorem B3109765 : Blo 1841622 3109765 := bbase (se 4 (by rfl) ⟨291540, by rfl⟩ : syracuseStep 3109765 = 583081) (by norm_num)
theorem B2331605 : Blo 1841622 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B3109853 : Blo 1841622 3109853 := bbase (se 3 (by rfl) ⟨583097, by rfl⟩ : syracuseStep 3109853 = 1166195) (by norm_num)
theorem B4666349 : Blo 1841622 4666349 := bbase (se 3 (by rfl) ⟨874940, by rfl⟩ : syracuseStep 4666349 = 1749881) (by norm_num)
theorem B2331661 : Blo 1841622 2331661 := bbase (se 3 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 2331661 = 874373) (by norm_num)
theorem B23622677 : Blo 1841622 23622677 := bbase (se 6 (by rfl) ⟨553656, by rfl⟩ : syracuseStep 23622677 = 1107313) (by norm_num)
theorem B10237013 : Blo 1841622 10237013 := bbase (se 8 (by rfl) ⟨59982, by rfl⟩ : syracuseStep 10237013 = 119965) (by norm_num)
theorem B3109981 : Blo 1841622 3109981 := bbase (se 3 (by rfl) ⟨583121, by rfl⟩ : syracuseStep 3109981 = 1166243) (by norm_num)
theorem B2331757 : Blo 1841622 2331757 := bbase (se 3 (by rfl) ⟨437204, by rfl⟩ : syracuseStep 2331757 = 874409) (by norm_num)
theorem B9327797 : Blo 1841622 9327797 := bbase (se 5 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 9327797 = 874481) (by norm_num)
theorem B3110069 : Blo 1841622 3110069 := bbase (se 5 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 3110069 = 291569) (by norm_num)
theorem B14374165 : Blo 1841622 14374165 := bbase (se 6 (by rfl) ⟨336894, by rfl⟩ : syracuseStep 14374165 = 673789) (by norm_num)
theorem B25212181 : Blo 1841622 25212181 := bbase (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) (by norm_num)
theorem B5248277 : Blo 1841622 5248277 := bbase (se 6 (by rfl) ⟨123006, by rfl⟩ : syracuseStep 5248277 = 246013) (by norm_num)
theorem B2331929 : Blo 1841622 2331929 := bbase (se 2 (by rfl) ⟨874473, by rfl⟩ : syracuseStep 2331929 = 1748947) (by norm_num)
theorem B3110197 : Blo 1841622 3110197 := bbase (se 5 (by rfl) ⟨145790, by rfl⟩ : syracuseStep 3110197 = 291581) (by norm_num)
theorem B2331985 : Blo 1841622 2331985 := bbase (se 2 (by rfl) ⟨874494, by rfl⟩ : syracuseStep 2331985 = 1748989) (by norm_num)
theorem B10491221 : Blo 1841622 10491221 := bbase (se 14 (by rfl) ⟨960, by rfl⟩ : syracuseStep 10491221 = 1921) (by norm_num)
theorem B3110285 : Blo 1841622 3110285 := bbase (se 3 (by rfl) ⟨583178, by rfl⟩ : syracuseStep 3110285 = 1166357) (by norm_num)
theorem B2364833 : Blo 1841622 2364833 := bbase (se 2 (by rfl) ⟨886812, by rfl⟩ : syracuseStep 2364833 = 1773625) (by norm_num)
theorem B2332081 : Blo 1841622 2332081 := bbase (se 2 (by rfl) ⟨874530, by rfl⟩ : syracuseStep 2332081 = 1749061) (by norm_num)
theorem B3544541 : Blo 1841622 3544541 := bbase (se 3 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 3544541 = 1329203) (by norm_num)
theorem B3110413 : Blo 1841622 3110413 := bbase (se 3 (by rfl) ⟨583202, by rfl⟩ : syracuseStep 3110413 = 1166405) (by norm_num)
theorem B2332253 : Blo 1841622 2332253 := bbase (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) (by norm_num)
theorem B3110501 : Blo 1841622 3110501 := bbase (se 4 (by rfl) ⟨291609, by rfl⟩ : syracuseStep 3110501 = 583219) (by norm_num)
theorem B2332309 : Blo 1841622 2332309 := bbase (se 6 (by rfl) ⟨54663, by rfl⟩ : syracuseStep 2332309 = 109327) (by norm_num)
theorem B5248709 : Blo 1841622 5248709 := bbase (se 4 (by rfl) ⟨492066, by rfl⟩ : syracuseStep 5248709 = 984133) (by norm_num)
theorem B3110629 : Blo 1841622 3110629 := bbase (se 4 (by rfl) ⟨291621, by rfl⟩ : syracuseStep 3110629 = 583243) (by norm_num)
theorem B4429541 : Blo 1841622 4429541 := bbase (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) (by norm_num)
theorem B2332405 : Blo 1841622 2332405 := bbase (se 5 (by rfl) ⟨109331, by rfl⟩ : syracuseStep 2332405 = 218663) (by norm_num)
theorem B7870229 : Blo 1841622 7870229 := bbase (se 6 (by rfl) ⟨184458, by rfl⟩ : syracuseStep 7870229 = 368917) (by norm_num)
theorem B3110717 : Blo 1841622 3110717 := bbase (se 3 (by rfl) ⟨583259, by rfl⟩ : syracuseStep 3110717 = 1166519) (by norm_num)
theorem B15734645 : Blo 1841622 15734645 := bbase (se 5 (by rfl) ⟨737561, by rfl⟩ : syracuseStep 15734645 = 1475123) (by norm_num)
theorem B2332577 : Blo 1841622 2332577 := bbase (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) (by norm_num)
theorem B3110845 : Blo 1841622 3110845 := bbase (se 3 (by rfl) ⟨583283, by rfl⟩ : syracuseStep 3110845 = 1166567) (by norm_num)
theorem B16816085 : Blo 1841622 16816085 := bbase (se 7 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 16816085 = 394127) (by norm_num)
theorem B2332633 : Blo 1841622 2332633 := bbase (se 2 (by rfl) ⟨874737, by rfl⟩ : syracuseStep 2332633 = 1749475) (by norm_num)
theorem B9451493 : Blo 1841622 9451493 := bbase (se 4 (by rfl) ⟨886077, by rfl⟩ : syracuseStep 9451493 = 1772155) (by norm_num)
theorem B6215669 : Blo 1841622 6215669 := bbase (se 5 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 6215669 = 582719) (by norm_num)
theorem B3733517 : Blo 1841622 3733517 := bbase (se 3 (by rfl) ⟨700034, by rfl⟩ : syracuseStep 3733517 = 1400069) (by norm_num)
theorem B3110933 : Blo 1841622 3110933 := bbase (se 6 (by rfl) ⟨72912, by rfl⟩ : syracuseStep 3110933 = 145825) (by norm_num)
theorem B2332729 : Blo 1841622 2332729 := bbase (se 2 (by rfl) ⟨874773, by rfl⟩ : syracuseStep 2332729 = 1749547) (by norm_num)
theorem B2021437 : Blo 1841622 2021437 := bbase (se 3 (by rfl) ⟨379019, by rfl⟩ : syracuseStep 2021437 = 758039) (by norm_num)
theorem B4978757 : Blo 1841622 4978757 := bbase (se 4 (by rfl) ⟨466758, by rfl⟩ : syracuseStep 4978757 = 933517) (by norm_num)
theorem B3111061 : Blo 1841622 3111061 := bbase (se 6 (by rfl) ⟨72915, by rfl⟩ : syracuseStep 3111061 = 145831) (by norm_num)
theorem B6994133 : Blo 1841622 6994133 := bbase (se 7 (by rfl) ⟨81962, by rfl⟩ : syracuseStep 6994133 = 163925) (by norm_num)
theorem B2332901 : Blo 1841622 2332901 := bbase (se 4 (by rfl) ⟨218709, by rfl⟩ : syracuseStep 2332901 = 437419) (by norm_num)
theorem B2332957 : Blo 1841622 2332957 := bbase (se 3 (by rfl) ⟨437429, by rfl⟩ : syracuseStep 2332957 = 874859) (by norm_num)
theorem B3496277 : Blo 1841622 3496277 := bbase (se 10 (by rfl) ⟨5121, by rfl⟩ : syracuseStep 3496277 = 10243) (by norm_num)
theorem B2333053 : Blo 1841622 2333053 := bbase (se 3 (by rfl) ⟨437447, by rfl⟩ : syracuseStep 2333053 = 874895) (by norm_num)
theorem B8853893 : Blo 1841622 8853893 := bbase (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) (by norm_num)
theorem B6216101 : Blo 1841622 6216101 := bbase (se 4 (by rfl) ⟨582759, by rfl⟩ : syracuseStep 6216101 = 1165519) (by norm_num)
theorem B5249461 : Blo 1841622 5249461 := bbase (se 5 (by rfl) ⟨246068, by rfl⟩ : syracuseStep 5249461 = 492137) (by norm_num)
theorem B9329093 : Blo 1841622 9329093 := bbase (se 4 (by rfl) ⟨874602, by rfl⟩ : syracuseStep 9329093 = 1749205) (by norm_num)
theorem B3496421 : Blo 1841622 3496421 := bbase (se 4 (by rfl) ⟨327789, by rfl⟩ : syracuseStep 3496421 = 655579) (by norm_num)
theorem B6994421 : Blo 1841622 6994421 := bbase (se 5 (by rfl) ⟨327863, by rfl⟩ : syracuseStep 6994421 = 655727) (by norm_num)
theorem B4143653 : Blo 1841622 4143653 := bbase (se 4 (by rfl) ⟨388467, by rfl⟩ : syracuseStep 4143653 = 776935) (by norm_num)
theorem B2333225 : Blo 1841622 2333225 := bbase (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) (by norm_num)
theorem B2333281 : Blo 1841622 2333281 := bbase (se 2 (by rfl) ⟨874980, by rfl⟩ : syracuseStep 2333281 = 1749961) (by norm_num)
theorem B4143725 : Blo 1841622 4143725 := bbase (se 3 (by rfl) ⟨776948, by rfl⟩ : syracuseStep 4143725 = 1553897) (by norm_num)
theorem B4143797 : Blo 1841622 4143797 := bbase (se 5 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 4143797 = 388481) (by norm_num)
theorem B4143869 : Blo 1841622 4143869 := bbase (se 3 (by rfl) ⟨776975, by rfl⟩ : syracuseStep 4143869 = 1553951) (by norm_num)
theorem B3496709 : Blo 1841622 3496709 := bbase (se 4 (by rfl) ⟨327816, by rfl⟩ : syracuseStep 3496709 = 655633) (by norm_num)
theorem B11803445 : Blo 1841622 11803445 := bbase (se 5 (by rfl) ⟨553286, by rfl⟩ : syracuseStep 11803445 = 1106573) (by norm_num)
theorem B4143941 : Blo 1841622 4143941 := bbase (se 4 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 4143941 = 776989) (by norm_num)
theorem B6216533 : Blo 1841622 6216533 := bbase (se 9 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 6216533 = 36425) (by norm_num)
theorem B3545957 : Blo 1841622 3545957 := bbase (se 4 (by rfl) ⟨332433, by rfl⟩ : syracuseStep 3545957 = 664867) (by norm_num)
theorem B4144013 : Blo 1841622 4144013 := bbase (se 3 (by rfl) ⟨777002, by rfl⟩ : syracuseStep 4144013 = 1554005) (by norm_num)
theorem B3496861 : Blo 1841622 3496861 := bbase (se 3 (by rfl) ⟨655661, by rfl⟩ : syracuseStep 3496861 = 1311323) (by norm_num)
theorem B4144085 : Blo 1841622 4144085 := bbase (se 7 (by rfl) ⟨48563, by rfl⟩ : syracuseStep 4144085 = 97127) (by norm_num)
theorem B31497173 : Blo 1841622 31497173 := bbase (se 7 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 31497173 = 738215) (by norm_num)
theorem B7977989 : Blo 1841622 7977989 := bbase (se 4 (by rfl) ⟨747936, by rfl⟩ : syracuseStep 7977989 = 1495873) (by norm_num)
theorem B4144157 : Blo 1841622 4144157 := bbase (se 3 (by rfl) ⟨777029, by rfl⟩ : syracuseStep 4144157 = 1554059) (by norm_num)
theorem B4144229 : Blo 1841622 4144229 := bbase (se 4 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 4144229 = 777043) (by norm_num)
theorem B3734677 : Blo 1841622 3734677 := bbase (se 6 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 3734677 = 175063) (by norm_num)
theorem B4144301 : Blo 1841622 4144301 := bbase (se 3 (by rfl) ⟨777056, by rfl⟩ : syracuseStep 4144301 = 1554113) (by norm_num)
theorem B3497165 : Blo 1841622 3497165 := bbase (se 3 (by rfl) ⟨655718, by rfl⟩ : syracuseStep 3497165 = 1311437) (by norm_num)
theorem B4259029 : Blo 1841622 4259029 := bbase (se 7 (by rfl) ⟨49910, by rfl⟩ : syracuseStep 4259029 = 99821) (by norm_num)
theorem B14941397 : Blo 1841622 14941397 := bbase (se 7 (by rfl) ⟨175094, by rfl⟩ : syracuseStep 14941397 = 350189) (by norm_num)
theorem B2072569 : Blo 1841622 2072569 := bbase (se 2 (by rfl) ⟨777213, by rfl⟩ : syracuseStep 2072569 = 1554427) (by norm_num)
theorem B2489573 : Blo 1841622 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B4144373 : Blo 1841622 4144373 := bbase (se 5 (by rfl) ⟨194267, by rfl⟩ : syracuseStep 4144373 = 388535) (by norm_num)
theorem B6216965 : Blo 1841622 6216965 := bbase (se 4 (by rfl) ⟨582840, by rfl⟩ : syracuseStep 6216965 = 1165681) (by norm_num)
theorem B3366181 : Blo 1841622 3366181 := bbase (se 4 (by rfl) ⟨315579, by rfl⟩ : syracuseStep 3366181 = 631159) (by norm_num)
theorem B2071849 : Blo 1841622 2071849 := bbase (se 2 (by rfl) ⟨776943, by rfl⟩ : syracuseStep 2071849 = 1553887) (by norm_num)
theorem B4144445 : Blo 1841622 4144445 := bbase (se 3 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 4144445 = 1554167) (by norm_num)
theorem B2071885 : Blo 1841622 2071885 := bbase (se 3 (by rfl) ⟨388478, by rfl⟩ : syracuseStep 2071885 = 776957) (by norm_num)
theorem B23928149 : Blo 1841622 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B2071921 : Blo 1841622 2071921 := bbase (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) (by norm_num)
theorem B2489725 : Blo 1841622 2489725 := bbase (se 3 (by rfl) ⟨466823, by rfl⟩ : syracuseStep 2489725 = 933647) (by norm_num)
theorem B4144517 : Blo 1841622 4144517 := bbase (se 4 (by rfl) ⟨388548, by rfl⟩ : syracuseStep 4144517 = 777097) (by norm_num)
theorem B2071957 : Blo 1841622 2071957 := bbase (se 6 (by rfl) ⟨48561, by rfl⟩ : syracuseStep 2071957 = 97123) (by norm_num)
theorem B4201885 : Blo 1841622 4201885 := bbase (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) (by norm_num)
theorem B2071993 : Blo 1841622 2071993 := bbase (se 2 (by rfl) ⟨776997, by rfl⟩ : syracuseStep 2071993 = 1553995) (by norm_num)
theorem B4144589 : Blo 1841622 4144589 := bbase (se 3 (by rfl) ⟨777110, by rfl⟩ : syracuseStep 4144589 = 1554221) (by norm_num)
theorem B2072029 : Blo 1841622 2072029 := bbase (se 3 (by rfl) ⟨388505, by rfl⟩ : syracuseStep 2072029 = 777011) (by norm_num)
theorem B2072065 : Blo 1841622 2072065 := bbase (se 2 (by rfl) ⟨777024, by rfl⟩ : syracuseStep 2072065 = 1554049) (by norm_num)
theorem B8855045 : Blo 1841622 8855045 := bbase (se 4 (by rfl) ⟨830160, by rfl⟩ : syracuseStep 8855045 = 1660321) (by norm_num)
theorem B7872005 : Blo 1841622 7872005 := bbase (se 4 (by rfl) ⟨738000, by rfl⟩ : syracuseStep 7872005 = 1476001) (by norm_num)
theorem B4144661 : Blo 1841622 4144661 := bbase (se 6 (by rfl) ⟨97140, by rfl⟩ : syracuseStep 4144661 = 194281) (by norm_num)
theorem B2072101 : Blo 1841622 2072101 := bbase (se 4 (by rfl) ⟨194259, by rfl⟩ : syracuseStep 2072101 = 388519) (by norm_num)
theorem B2072137 : Blo 1841622 2072137 := bbase (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) (by norm_num)
theorem B4144733 : Blo 1841622 4144733 := bbase (se 3 (by rfl) ⟨777137, by rfl⟩ : syracuseStep 4144733 = 1554275) (by norm_num)
theorem B2072173 : Blo 1841622 2072173 := bbase (se 3 (by rfl) ⟨388532, by rfl⟩ : syracuseStep 2072173 = 777065) (by norm_num)
theorem B2072209 : Blo 1841622 2072209 := bbase (se 2 (by rfl) ⟨777078, by rfl⟩ : syracuseStep 2072209 = 1554157) (by norm_num)
theorem B6995605 : Blo 1841622 6995605 := bbase (se 6 (by rfl) ⟨163959, by rfl⟩ : syracuseStep 6995605 = 327919) (by norm_num)
theorem B4144805 : Blo 1841622 4144805 := bbase (se 4 (by rfl) ⟨388575, by rfl⟩ : syracuseStep 4144805 = 777151) (by norm_num)
theorem B2072245 : Blo 1841622 2072245 := bbase (se 5 (by rfl) ⟨97136, by rfl⟩ : syracuseStep 2072245 = 194273) (by norm_num)
theorem B6217397 : Blo 1841622 6217397 := bbase (se 5 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 6217397 = 582881) (by norm_num)
theorem B9330389 : Blo 1841622 9330389 := bbase (se 7 (by rfl) ⟨109340, by rfl⟩ : syracuseStep 9330389 = 218681) (by norm_num)
theorem B2072281 : Blo 1841622 2072281 := bbase (se 2 (by rfl) ⟨777105, by rfl⟩ : syracuseStep 2072281 = 1554211) (by norm_num)
theorem B4144877 : Blo 1841622 4144877 := bbase (se 3 (by rfl) ⟨777164, by rfl⟩ : syracuseStep 4144877 = 1554329) (by norm_num)
theorem B2072317 : Blo 1841622 2072317 := bbase (se 3 (by rfl) ⟨388559, by rfl⟩ : syracuseStep 2072317 = 777119) (by norm_num)
theorem B2072353 : Blo 1841622 2072353 := bbase (se 2 (by rfl) ⟨777132, by rfl⟩ : syracuseStep 2072353 = 1554265) (by norm_num)
theorem B4144949 : Blo 1841622 4144949 := bbase (se 5 (by rfl) ⟨194294, by rfl⟩ : syracuseStep 4144949 = 388589) (by norm_num)
theorem B7094069 : Blo 1841622 7094069 := bbase (se 5 (by rfl) ⟨332534, by rfl⟩ : syracuseStep 7094069 = 665069) (by norm_num)
theorem B2072389 : Blo 1841622 2072389 := bbase (se 4 (by rfl) ⟨194286, by rfl⟩ : syracuseStep 2072389 = 388573) (by norm_num)
theorem B2072425 : Blo 1841622 2072425 := bbase (se 2 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 2072425 = 1554319) (by norm_num)
theorem B4145021 : Blo 1841622 4145021 := bbase (se 3 (by rfl) ⟨777191, by rfl⟩ : syracuseStep 4145021 = 1554383) (by norm_num)
theorem B2072461 : Blo 1841622 2072461 := bbase (se 3 (by rfl) ⟨388586, by rfl⟩ : syracuseStep 2072461 = 777173) (by norm_num)
theorem B4202389 : Blo 1841622 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B10100629 : Blo 1841622 10100629 := bbase (se 6 (by rfl) ⟨236733, by rfl⟩ : syracuseStep 10100629 = 473467) (by norm_num)
theorem B2072497 : Blo 1841622 2072497 := bbase (se 2 (by rfl) ⟨777186, by rfl⟩ : syracuseStep 2072497 = 1554373) (by norm_num)
theorem B3497917 : Blo 1841622 3497917 := bbase (se 3 (by rfl) ⟨655859, by rfl⟩ : syracuseStep 3497917 = 1311719) (by norm_num)
theorem B4145093 : Blo 1841622 4145093 := bbase (se 4 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 4145093 = 777205) (by norm_num)
theorem B6995909 : Blo 1841622 6995909 := bbase (se 4 (by rfl) ⟨655866, by rfl⟩ : syracuseStep 6995909 = 1311733) (by norm_num)
theorem B2072533 : Blo 1841622 2072533 := bbase (se 7 (by rfl) ⟨24287, by rfl⟩ : syracuseStep 2072533 = 48575) (by norm_num)
theorem B1843203 : Blo 1841622 1843203 := bstep (se 1 (by rfl) ⟨1382402, by rfl⟩ : syracuseStep 1843203 = 2764805) B2764805
theorem B1843219 : Blo 1841622 1843219 := bstep (se 1 (by rfl) ⟨1382414, by rfl⟩ : syracuseStep 1843219 = 2764829) B2764829
theorem B1843235 : Blo 1841622 1843235 := bstep (se 1 (by rfl) ⟨1382426, by rfl⟩ : syracuseStep 1843235 = 2764853) B2764853
theorem B4145201 : Blo 1841622 4145201 := bstep (se 2 (by rfl) ⟨1554450, by rfl⟩ : syracuseStep 4145201 = 3108901) B3108901
theorem B1843251 : Blo 1841622 1843251 := bstep (se 1 (by rfl) ⟨1382438, by rfl⟩ : syracuseStep 1843251 = 2764877) B2764877
theorem B4145219 : Blo 1841622 4145219 := bstep (se 1 (by rfl) ⟨3108914, by rfl⟩ : syracuseStep 4145219 = 6217829) B6217829
theorem B1843267 : Blo 1841622 1843267 := bstep (se 1 (by rfl) ⟨1382450, by rfl⟩ : syracuseStep 1843267 = 2764901) B2764901
theorem B2072659 : Blo 1841622 2072659 := bstep (se 1 (by rfl) ⟨1554494, by rfl⟩ : syracuseStep 2072659 = 3108989) B3108989
theorem B1843283 : Blo 1841622 1843283 := bstep (se 1 (by rfl) ⟨1382462, by rfl⟩ : syracuseStep 1843283 = 2764925) B2764925
theorem B1843299 : Blo 1841622 1843299 := bstep (se 1 (by rfl) ⟨1382474, by rfl⟩ : syracuseStep 1843299 = 2764949) B2764949
theorem B1843315 : Blo 1841622 1843315 := bstep (se 1 (by rfl) ⟨1382486, by rfl⟩ : syracuseStep 1843315 = 2764973) B2764973
theorem B1843331 : Blo 1841622 1843331 := bstep (se 1 (by rfl) ⟨1382498, by rfl⟩ : syracuseStep 1843331 = 2764997) B2764997
theorem B7872653 : Blo 1841622 7872653 := bstep (se 3 (by rfl) ⟨1476122, by rfl⟩ : syracuseStep 7872653 = 2952245) B2952245
theorem B1843347 : Blo 1841622 1843347 := bstep (se 1 (by rfl) ⟨1382510, by rfl⟩ : syracuseStep 1843347 = 2765021) B2765021
theorem B3735715 : Blo 1841622 3735715 := bstep (se 1 (by rfl) ⟨2801786, by rfl⟩ : syracuseStep 3735715 = 5603573) B5603573
theorem B1843363 : Blo 1841622 1843363 := bstep (se 1 (by rfl) ⟨1382522, by rfl⟩ : syracuseStep 1843363 = 2765045) B2765045
theorem B1843379 : Blo 1841622 1843379 := bstep (se 1 (by rfl) ⟨1382534, by rfl⟩ : syracuseStep 1843379 = 2765069) B2765069
theorem B1843395 : Blo 1841622 1843395 := bstep (se 1 (by rfl) ⟨1382546, by rfl⟩ : syracuseStep 1843395 = 2765093) B2765093
theorem B6217937 : Blo 1841622 6217937 := bstep (se 2 (by rfl) ⟨2331726, by rfl⟩ : syracuseStep 6217937 = 4663453) B4663453
theorem B1843411 : Blo 1841622 1843411 := bstep (se 1 (by rfl) ⟨1382558, by rfl⟩ : syracuseStep 1843411 = 2765117) B2765117
theorem B2072803 : Blo 1841622 2072803 := bstep (se 1 (by rfl) ⟨1554602, by rfl⟩ : syracuseStep 2072803 = 3109205) B3109205
theorem B50438371 : Blo 1841622 50438371 := bstep (se 1 (by rfl) ⟨37828778, by rfl⟩ : syracuseStep 50438371 = 75657557) B75657557
theorem B1843427 : Blo 1841622 1843427 := bstep (se 1 (by rfl) ⟨1382570, by rfl⟩ : syracuseStep 1843427 = 2765141) B2765141
theorem B1843443 : Blo 1841622 1843443 := bstep (se 1 (by rfl) ⟨1382582, by rfl⟩ : syracuseStep 1843443 = 2765165) B2765165
theorem B1843459 : Blo 1841622 1843459 := bstep (se 1 (by rfl) ⟨1382594, by rfl⟩ : syracuseStep 1843459 = 2765189) B2765189
theorem B1843475 : Blo 1841622 1843475 := bstep (se 1 (by rfl) ⟨1382606, by rfl⟩ : syracuseStep 1843475 = 2765213) B2765213
theorem B1843491 : Blo 1841622 1843491 := bstep (se 1 (by rfl) ⟨1382618, by rfl⟩ : syracuseStep 1843491 = 2765237) B2765237
theorem B1843507 : Blo 1841622 1843507 := bstep (se 1 (by rfl) ⟨1382630, by rfl⟩ : syracuseStep 1843507 = 2765261) B2765261
theorem B1843523 : Blo 1841622 1843523 := bstep (se 1 (by rfl) ⟨1382642, by rfl⟩ : syracuseStep 1843523 = 2765285) B2765285
theorem B10780997 : Blo 1841622 10780997 := bstep (se 4 (by rfl) ⟨1010718, by rfl⟩ : syracuseStep 10780997 = 2021437) B2021437
theorem B4145489 : Blo 1841622 4145489 := bstep (se 2 (by rfl) ⟨1554558, by rfl⟩ : syracuseStep 4145489 = 3109117) B3109117
theorem B1843539 : Blo 1841622 1843539 := bstep (se 1 (by rfl) ⟨1382654, by rfl⟩ : syracuseStep 1843539 = 2765309) B2765309
theorem B4145507 : Blo 1841622 4145507 := bstep (se 1 (by rfl) ⟨3109130, by rfl⟩ : syracuseStep 4145507 = 6218261) B6218261
theorem B1843555 : Blo 1841622 1843555 := bstep (se 1 (by rfl) ⟨1382666, by rfl⟩ : syracuseStep 1843555 = 2765333) B2765333
theorem B2072947 : Blo 1841622 2072947 := bstep (se 1 (by rfl) ⟨1554710, by rfl⟩ : syracuseStep 2072947 = 3109421) B3109421
theorem B1843571 : Blo 1841622 1843571 := bstep (se 1 (by rfl) ⟨1382678, by rfl⟩ : syracuseStep 1843571 = 2765357) B2765357
theorem B1843587 : Blo 1841622 1843587 := bstep (se 1 (by rfl) ⟨1382690, by rfl⟩ : syracuseStep 1843587 = 2765381) B2765381
theorem B11805061 : Blo 1841622 11805061 := bstep (se 4 (by rfl) ⟨1106724, by rfl⟩ : syracuseStep 11805061 = 2213449) B2213449
theorem B6996365 : Blo 1841622 6996365 := bstep (se 3 (by rfl) ⟨1311818, by rfl⟩ : syracuseStep 6996365 = 2623637) B2623637
theorem B1843603 : Blo 1841622 1843603 := bstep (se 1 (by rfl) ⟨1382702, by rfl⟩ : syracuseStep 1843603 = 2765405) B2765405
theorem B3498403 : Blo 1841622 3498403 := bstep (se 1 (by rfl) ⟨2623802, by rfl⟩ : syracuseStep 3498403 = 5247605) B5247605
theorem B1843619 : Blo 1841622 1843619 := bstep (se 1 (by rfl) ⟨1382714, by rfl⟩ : syracuseStep 1843619 = 2765429) B2765429
theorem B2073091 : Blo 1841622 2073091 := bstep (se 1 (by rfl) ⟨1554818, by rfl⟩ : syracuseStep 2073091 = 3109637) B3109637
theorem B3736145 : Blo 1841622 3736145 := bstep (se 2 (by rfl) ⟨1401054, by rfl⟩ : syracuseStep 3736145 = 2802109) B2802109
theorem B11207267 : Blo 1841622 11207267 := bstep (se 1 (by rfl) ⟨8405450, by rfl⟩ : syracuseStep 11207267 = 16810901) B16810901
theorem B4145777 : Blo 1841622 4145777 := bstep (se 2 (by rfl) ⟨1554666, by rfl⟩ : syracuseStep 4145777 = 3109333) B3109333
theorem B4145795 : Blo 1841622 4145795 := bstep (se 1 (by rfl) ⟨3109346, by rfl⟩ : syracuseStep 4145795 = 6218693) B6218693
theorem B2073235 : Blo 1841622 2073235 := bstep (se 1 (by rfl) ⟨1554926, by rfl⟩ : syracuseStep 2073235 = 3109853) B3109853
theorem B1966771 : Blo 1841622 1966771 := bstep (se 1 (by rfl) ⟨1475078, by rfl⟩ : syracuseStep 1966771 = 2950157) B2950157
theorem B2622179 : Blo 1841622 2622179 := bstep (se 1 (by rfl) ⟨1966634, by rfl⟩ : syracuseStep 2622179 = 3933269) B3933269
theorem B6824675 : Blo 1841622 6824675 := bstep (se 1 (by rfl) ⟨5118506, by rfl⟩ : syracuseStep 6824675 = 10237013) B10237013
theorem B6218477 : Blo 1841622 6218477 := bstep (se 3 (by rfl) ⟨1165964, by rfl⟩ : syracuseStep 6218477 = 2331929) B2331929
theorem B6218531 : Blo 1841622 6218531 := bstep (se 1 (by rfl) ⟨4663898, by rfl⟩ : syracuseStep 6218531 = 9327797) B9327797
theorem B2073379 : Blo 1841622 2073379 := bstep (se 1 (by rfl) ⟨1555034, by rfl⟩ : syracuseStep 2073379 = 3110069) B3110069
theorem B3736387 : Blo 1841622 3736387 := bstep (se 1 (by rfl) ⟨2802290, by rfl⟩ : syracuseStep 3736387 = 5604581) B5604581
theorem B3498851 : Blo 1841622 3498851 := bstep (se 1 (by rfl) ⟨2624138, by rfl⟩ : syracuseStep 3498851 = 5248277) B5248277
theorem B2212723 : Blo 1841622 2212723 := bstep (se 1 (by rfl) ⟨1659542, by rfl⟩ : syracuseStep 2212723 = 3319085) B3319085
theorem B13288333 : Blo 1841622 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B4146065 : Blo 1841622 4146065 := bstep (se 2 (by rfl) ⟨1554774, by rfl⟩ : syracuseStep 4146065 = 3109549) B3109549
theorem B4146083 : Blo 1841622 4146083 := bstep (se 1 (by rfl) ⟨3109562, by rfl⟩ : syracuseStep 4146083 = 6219125) B6219125
theorem B2950067 : Blo 1841622 2950067 := bstep (se 1 (by rfl) ⟨2212550, by rfl⟩ : syracuseStep 2950067 = 4425101) B4425101
theorem B2073523 : Blo 1841622 2073523 := bstep (se 1 (by rfl) ⟨1555142, by rfl⟩ : syracuseStep 2073523 = 3110285) B3110285
theorem B8979427 : Blo 1841622 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B6218801 : Blo 1841622 6218801 := bstep (se 2 (by rfl) ⟨2332050, by rfl⟩ : syracuseStep 6218801 = 4664101) B4664101
theorem B2073667 : Blo 1841622 2073667 := bstep (se 1 (by rfl) ⟨1555250, by rfl⟩ : syracuseStep 2073667 = 3110501) B3110501
theorem B11207749 : Blo 1841622 11207749 := bstep (se 4 (by rfl) ⟨1050726, by rfl⟩ : syracuseStep 11207749 = 2101453) B2101453
theorem B1967203 : Blo 1841622 1967203 := bstep (se 1 (by rfl) ⟨1475402, by rfl⟩ : syracuseStep 1967203 = 2950805) B2950805
theorem B5604461 : Blo 1841622 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B3499139 : Blo 1841622 3499139 := bstep (se 1 (by rfl) ⟨2624354, by rfl⟩ : syracuseStep 3499139 = 5248709) B5248709
theorem B4146353 : Blo 1841622 4146353 := bstep (se 2 (by rfl) ⟨1554882, by rfl⟩ : syracuseStep 4146353 = 3109765) B3109765
theorem B4146371 : Blo 1841622 4146371 := bstep (se 1 (by rfl) ⟨3109778, by rfl⟩ : syracuseStep 4146371 = 6219557) B6219557
theorem B5604547 : Blo 1841622 5604547 := bstep (se 1 (by rfl) ⟨4203410, by rfl⟩ : syracuseStep 5604547 = 8406821) B8406821
theorem B4662481 : Blo 1841622 4662481 := bstep (se 2 (by rfl) ⟨1748430, by rfl⟩ : syracuseStep 4662481 = 3496861) B3496861
theorem B2073811 : Blo 1841622 2073811 := bstep (se 1 (by rfl) ⟨1555358, by rfl⟩ : syracuseStep 2073811 = 3110717) B3110717
theorem B9323747 : Blo 1841622 9323747 := bstep (se 1 (by rfl) ⟨6992810, by rfl⟩ : syracuseStep 9323747 = 13985621) B13985621
theorem B2622737 : Blo 1841622 2622737 := bstep (se 2 (by rfl) ⟨983526, by rfl⟩ : syracuseStep 2622737 = 1967053) B1967053
theorem B6300995 : Blo 1841622 6300995 := bstep (se 1 (by rfl) ⟨4725746, by rfl⟩ : syracuseStep 6300995 = 9451493) B9451493
theorem B2622817 : Blo 1841622 2622817 := bstep (se 2 (by rfl) ⟨983556, by rfl⟩ : syracuseStep 2622817 = 1967113) B1967113
theorem B2073955 : Blo 1841622 2073955 := bstep (se 1 (by rfl) ⟨1555466, by rfl⟩ : syracuseStep 2073955 = 3110933) B3110933
theorem B4146641 : Blo 1841622 4146641 := bstep (se 2 (by rfl) ⟨1554990, by rfl⟩ : syracuseStep 4146641 = 3109981) B3109981
theorem B39831011 : Blo 1841622 39831011 := bstep (se 1 (by rfl) ⟨29873258, by rfl⟩ : syracuseStep 39831011 = 59746517) B59746517
theorem B4662755 : Blo 1841622 4662755 := bstep (se 1 (by rfl) ⟨3497066, by rfl⟩ : syracuseStep 4662755 = 6994133) B6994133
theorem B4146659 : Blo 1841622 4146659 := bstep (se 1 (by rfl) ⟨3109994, by rfl⟩ : syracuseStep 4146659 = 6219989) B6219989
theorem B2213411 : Blo 1841622 2213411 := bstep (se 1 (by rfl) ⟨1660058, by rfl⟩ : syracuseStep 2213411 = 3320117) B3320117
theorem B6219341 : Blo 1841622 6219341 := bstep (se 3 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 6219341 = 2332253) B2332253
theorem B8636003 : Blo 1841622 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B5678705 : Blo 1841622 5678705 := bstep (se 2 (by rfl) ⟨2129514, by rfl⟩ : syracuseStep 5678705 = 4259029) B4259029
theorem B6219395 : Blo 1841622 6219395 := bstep (se 1 (by rfl) ⟨4664546, by rfl⟩ : syracuseStep 6219395 = 9329093) B9329093
theorem B3933859 : Blo 1841622 3933859 := bstep (se 1 (by rfl) ⟨2950394, by rfl⟩ : syracuseStep 3933859 = 5900789) B5900789
theorem B4662947 : Blo 1841622 4662947 := bstep (se 1 (by rfl) ⟨3497210, by rfl⟩ : syracuseStep 4662947 = 6994421) B6994421
theorem B4982435 : Blo 1841622 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B2762435 : Blo 1841622 2762435 := bstep (se 1 (by rfl) ⟨2071826, by rfl⟩ : syracuseStep 2762435 = 4143653) B4143653
theorem B2762465 : Blo 1841622 2762465 := bstep (se 2 (by rfl) ⟨1035924, by rfl⟩ : syracuseStep 2762465 = 2071849) B2071849
theorem B4146929 : Blo 1841622 4146929 := bstep (se 2 (by rfl) ⟨1555098, by rfl⟩ : syracuseStep 4146929 = 3110197) B3110197
theorem B2762483 : Blo 1841622 2762483 := bstep (se 1 (by rfl) ⟨2071862, by rfl⟩ : syracuseStep 2762483 = 4143725) B4143725
theorem B2950913 : Blo 1841622 2950913 := bstep (se 2 (by rfl) ⟨1106592, by rfl⟩ : syracuseStep 2950913 = 2213185) B2213185
theorem B4146947 : Blo 1841622 4146947 := bstep (se 1 (by rfl) ⟨3110210, by rfl⟩ : syracuseStep 4146947 = 6220421) B6220421
theorem B2762513 : Blo 1841622 2762513 := bstep (se 2 (by rfl) ⟨1035942, by rfl⟩ : syracuseStep 2762513 = 2071885) B2071885
theorem B5244689 : Blo 1841622 5244689 := bstep (se 2 (by rfl) ⟨1966758, by rfl⟩ : syracuseStep 5244689 = 3933517) B3933517
theorem B2762531 : Blo 1841622 2762531 := bstep (se 1 (by rfl) ⟨2071898, by rfl⟩ : syracuseStep 2762531 = 4143797) B4143797
theorem B4982563 : Blo 1841622 4982563 := bstep (se 1 (by rfl) ⟨3736922, by rfl⟩ : syracuseStep 4982563 = 7473845) B7473845
theorem B2762561 : Blo 1841622 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B3319633 : Blo 1841622 3319633 := bstep (se 2 (by rfl) ⟨1244862, by rfl⟩ : syracuseStep 3319633 = 2489725) B2489725
theorem B2762579 : Blo 1841622 2762579 := bstep (se 1 (by rfl) ⟨2071934, by rfl⟩ : syracuseStep 2762579 = 4143869) B4143869
theorem B2762609 : Blo 1841622 2762609 := bstep (se 2 (by rfl) ⟨1035978, by rfl⟩ : syracuseStep 2762609 = 2071957) B2071957
theorem B2762627 : Blo 1841622 2762627 := bstep (se 1 (by rfl) ⟨2071970, by rfl⟩ : syracuseStep 2762627 = 4143941) B4143941
theorem B6219665 : Blo 1841622 6219665 := bstep (se 2 (by rfl) ⟨2332374, by rfl⟩ : syracuseStep 6219665 = 4664749) B4664749
theorem B2762657 : Blo 1841622 2762657 := bstep (se 2 (by rfl) ⟨1035996, by rfl⟩ : syracuseStep 2762657 = 2071993) B2071993
theorem B9332657 : Blo 1841622 9332657 := bstep (se 2 (by rfl) ⟨3499746, by rfl⟩ : syracuseStep 9332657 = 6999493) B6999493
theorem B2762675 : Blo 1841622 2762675 := bstep (se 1 (by rfl) ⟨2072006, by rfl⟩ : syracuseStep 2762675 = 4144013) B4144013
theorem B3737539 : Blo 1841622 3737539 := bstep (se 1 (by rfl) ⟨2803154, by rfl⟩ : syracuseStep 3737539 = 5606309) B5606309
theorem B5605325 : Blo 1841622 5605325 := bstep (se 3 (by rfl) ⟨1050998, by rfl⟩ : syracuseStep 5605325 = 2101997) B2101997
theorem B2762705 : Blo 1841622 2762705 := bstep (se 2 (by rfl) ⟨1036014, by rfl⟩ : syracuseStep 2762705 = 2072029) B2072029
theorem B2762723 : Blo 1841622 2762723 := bstep (se 1 (by rfl) ⟨2072042, by rfl⟩ : syracuseStep 2762723 = 4144085) B4144085
theorem B20998115 : Blo 1841622 20998115 := bstep (se 1 (by rfl) ⟨15748586, by rfl⟩ : syracuseStep 20998115 = 31497173) B31497173
theorem B2762753 : Blo 1841622 2762753 := bstep (se 2 (by rfl) ⟨1036032, by rfl⟩ : syracuseStep 2762753 = 2072065) B2072065
theorem B5318659 : Blo 1841622 5318659 := bstep (se 1 (by rfl) ⟨3988994, by rfl⟩ : syracuseStep 5318659 = 7977989) B7977989
theorem B9324557 : Blo 1841622 9324557 := bstep (se 3 (by rfl) ⟨1748354, by rfl⟩ : syracuseStep 9324557 = 3496709) B3496709
theorem B4147217 : Blo 1841622 4147217 := bstep (se 2 (by rfl) ⟨1555206, by rfl⟩ : syracuseStep 4147217 = 3110413) B3110413
theorem B2762771 : Blo 1841622 2762771 := bstep (se 1 (by rfl) ⟨2072078, by rfl⟩ : syracuseStep 2762771 = 4144157) B4144157
theorem B4147235 : Blo 1841622 4147235 := bstep (se 1 (by rfl) ⟨3110426, by rfl⟩ : syracuseStep 4147235 = 6220853) B6220853
theorem B2762801 : Blo 1841622 2762801 := bstep (se 2 (by rfl) ⟨1036050, by rfl⟩ : syracuseStep 2762801 = 2072101) B2072101
theorem B3237937 : Blo 1841622 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B2762819 : Blo 1841622 2762819 := bstep (se 1 (by rfl) ⟨2072114, by rfl⟩ : syracuseStep 2762819 = 4144229) B4144229
theorem B2762849 : Blo 1841622 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B2762867 : Blo 1841622 2762867 := bstep (se 1 (by rfl) ⟨2072150, by rfl⟩ : syracuseStep 2762867 = 4144301) B4144301
theorem B2623603 : Blo 1841622 2623603 := bstep (se 1 (by rfl) ⟨1967702, by rfl⟩ : syracuseStep 2623603 = 3935405) B3935405
theorem B2762897 : Blo 1841622 2762897 := bstep (se 2 (by rfl) ⟨1036086, by rfl⟩ : syracuseStep 2762897 = 2072173) B2072173
theorem B2762915 : Blo 1841622 2762915 := bstep (se 1 (by rfl) ⟨2072186, by rfl⟩ : syracuseStep 2762915 = 4144373) B4144373
theorem B7473329 : Blo 1841622 7473329 := bstep (se 2 (by rfl) ⟨2802498, by rfl⟩ : syracuseStep 7473329 = 5604997) B5604997
theorem B2762945 : Blo 1841622 2762945 := bstep (se 2 (by rfl) ⟨1036104, by rfl⟩ : syracuseStep 2762945 = 2072209) B2072209
theorem B2762963 : Blo 1841622 2762963 := bstep (se 1 (by rfl) ⟨2072222, by rfl⟩ : syracuseStep 2762963 = 4144445) B4144445
theorem B15952099 : Blo 1841622 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B2762993 : Blo 1841622 2762993 := bstep (se 2 (by rfl) ⟨1036122, by rfl⟩ : syracuseStep 2762993 = 2072245) B2072245
theorem B2951425 : Blo 1841622 2951425 := bstep (se 2 (by rfl) ⟨1106784, by rfl⟩ : syracuseStep 2951425 = 2213569) B2213569
theorem B2763011 : Blo 1841622 2763011 := bstep (se 1 (by rfl) ⟨2072258, by rfl⟩ : syracuseStep 2763011 = 4144517) B4144517
theorem B2763041 : Blo 1841622 2763041 := bstep (se 2 (by rfl) ⟨1036140, by rfl⟩ : syracuseStep 2763041 = 2072281) B2072281
theorem B4147505 : Blo 1841622 4147505 := bstep (se 2 (by rfl) ⟨1555314, by rfl⟩ : syracuseStep 4147505 = 3110629) B3110629
theorem B2763059 : Blo 1841622 2763059 := bstep (se 1 (by rfl) ⟨2072294, by rfl⟩ : syracuseStep 2763059 = 4144589) B4144589
theorem B4147523 : Blo 1841622 4147523 := bstep (se 1 (by rfl) ⟨3110642, by rfl⟩ : syracuseStep 4147523 = 6221285) B6221285
theorem B2763089 : Blo 1841622 2763089 := bstep (se 2 (by rfl) ⟨1036158, by rfl⟩ : syracuseStep 2763089 = 2072317) B2072317
theorem B1968467 : Blo 1841622 1968467 := bstep (se 1 (by rfl) ⟨1476350, by rfl⟩ : syracuseStep 1968467 = 2952701) B2952701
theorem B2763107 : Blo 1841622 2763107 := bstep (se 1 (by rfl) ⟨2072330, by rfl⟩ : syracuseStep 2763107 = 4144661) B4144661
theorem B7473521 : Blo 1841622 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B2763137 : Blo 1841622 2763137 := bstep (se 2 (by rfl) ⟨1036176, by rfl⟩ : syracuseStep 2763137 = 2072353) B2072353
theorem B2763155 : Blo 1841622 2763155 := bstep (se 1 (by rfl) ⟨2072366, by rfl⟩ : syracuseStep 2763155 = 4144733) B4144733
theorem B6220205 : Blo 1841622 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B5245361 : Blo 1841622 5245361 := bstep (se 2 (by rfl) ⟨1967010, by rfl⟩ : syracuseStep 5245361 = 3934021) B3934021
theorem B2763185 : Blo 1841622 2763185 := bstep (se 2 (by rfl) ⟨1036194, by rfl⟩ : syracuseStep 2763185 = 2072389) B2072389
theorem B2763203 : Blo 1841622 2763203 := bstep (se 1 (by rfl) ⟨2072402, by rfl⟩ : syracuseStep 2763203 = 4144805) B4144805
theorem B2763233 : Blo 1841622 2763233 := bstep (se 2 (by rfl) ⟨1036212, by rfl⟩ : syracuseStep 2763233 = 2072425) B2072425
theorem B6220259 : Blo 1841622 6220259 := bstep (se 1 (by rfl) ⟨4665194, by rfl⟩ : syracuseStep 6220259 = 9330389) B9330389
theorem B2763251 : Blo 1841622 2763251 := bstep (se 1 (by rfl) ⟨2072438, by rfl⟩ : syracuseStep 2763251 = 4144877) B4144877
theorem B2763281 : Blo 1841622 2763281 := bstep (se 2 (by rfl) ⟨1036230, by rfl⟩ : syracuseStep 2763281 = 2072461) B2072461
theorem B2763299 : Blo 1841622 2763299 := bstep (se 1 (by rfl) ⟨2072474, by rfl⟩ : syracuseStep 2763299 = 4144949) B4144949
theorem B4729379 : Blo 1841622 4729379 := bstep (se 1 (by rfl) ⟨3547034, by rfl⟩ : syracuseStep 4729379 = 7094069) B7094069
theorem B2763329 : Blo 1841622 2763329 := bstep (se 2 (by rfl) ⟨1036248, by rfl⟩ : syracuseStep 2763329 = 2072497) B2072497
theorem B4663889 : Blo 1841622 4663889 := bstep (se 2 (by rfl) ⟨1748958, by rfl⟩ : syracuseStep 4663889 = 3497917) B3497917
theorem B2624081 : Blo 1841622 2624081 := bstep (se 2 (by rfl) ⟨984030, by rfl⟩ : syracuseStep 2624081 = 1968061) B1968061
theorem B2763347 : Blo 1841622 2763347 := bstep (se 1 (by rfl) ⟨2072510, by rfl⟩ : syracuseStep 2763347 = 4145021) B4145021
theorem B4147793 : Blo 1841622 4147793 := bstep (se 2 (by rfl) ⟨1555422, by rfl⟩ : syracuseStep 4147793 = 3110845) B3110845
theorem B4147811 : Blo 1841622 4147811 := bstep (se 1 (by rfl) ⟨3110858, by rfl⟩ : syracuseStep 4147811 = 6221717) B6221717
theorem B2763377 : Blo 1841622 2763377 := bstep (se 2 (by rfl) ⟨1036266, by rfl⟩ : syracuseStep 2763377 = 2072533) B2072533
theorem B2763395 : Blo 1841622 2763395 := bstep (se 1 (by rfl) ⟨2072546, by rfl⟩ : syracuseStep 2763395 = 4145093) B4145093
theorem B4663939 : Blo 1841622 4663939 := bstep (se 1 (by rfl) ⟨3497954, by rfl⟩ : syracuseStep 4663939 = 6995909) B6995909
theorem B2763425 : Blo 1841622 2763425 := bstep (se 2 (by rfl) ⟨1036284, by rfl⟩ : syracuseStep 2763425 = 2072569) B2072569
theorem B2763443 : Blo 1841622 2763443 := bstep (se 1 (by rfl) ⟨2072582, by rfl⟩ : syracuseStep 2763443 = 4145165) B4145165
theorem B2624195 : Blo 1841622 2624195 := bstep (se 1 (by rfl) ⟨1968146, by rfl⟩ : syracuseStep 2624195 = 3936293) B3936293
theorem B5901005 : Blo 1841622 5901005 := bstep (se 3 (by rfl) ⟨1106438, by rfl⟩ : syracuseStep 5901005 = 2212877) B2212877
theorem B2763473 : Blo 1841622 2763473 := bstep (se 2 (by rfl) ⟨1036302, by rfl⟩ : syracuseStep 2763473 = 2072605) B2072605
theorem B2763491 : Blo 1841622 2763491 := bstep (se 1 (by rfl) ⟨2072618, by rfl⟩ : syracuseStep 2763491 = 4145237) B4145237
theorem B6220529 : Blo 1841622 6220529 := bstep (se 2 (by rfl) ⟨2332698, by rfl⟩ : syracuseStep 6220529 = 4665397) B4665397
theorem B4729585 : Blo 1841622 4729585 := bstep (se 2 (by rfl) ⟨1773594, by rfl⟩ : syracuseStep 4729585 = 3547189) B3547189
theorem B2763521 : Blo 1841622 2763521 := bstep (se 2 (by rfl) ⟨1036320, by rfl⟩ : syracuseStep 2763521 = 2072641) B2072641
theorem B4664081 : Blo 1841622 4664081 := bstep (se 2 (by rfl) ⟨1749030, by rfl⟩ : syracuseStep 4664081 = 3498061) B3498061
theorem B2763539 : Blo 1841622 2763539 := bstep (se 1 (by rfl) ⟨2072654, by rfl⟩ : syracuseStep 2763539 = 4145309) B4145309
theorem B2624275 : Blo 1841622 2624275 := bstep (se 1 (by rfl) ⟨1968206, by rfl⟩ : syracuseStep 2624275 = 3936413) B3936413
theorem B2763569 : Blo 1841622 2763569 := bstep (se 2 (by rfl) ⟨1036338, by rfl⟩ : syracuseStep 2763569 = 2072677) B2072677
theorem B2763587 : Blo 1841622 2763587 := bstep (se 1 (by rfl) ⟨2072690, by rfl⟩ : syracuseStep 2763587 = 4145381) B4145381
theorem B2763617 : Blo 1841622 2763617 := bstep (se 2 (by rfl) ⟨1036356, by rfl⟩ : syracuseStep 2763617 = 2072713) B2072713
theorem B2952035 : Blo 1841622 2952035 := bstep (se 1 (by rfl) ⟨2214026, by rfl⟩ : syracuseStep 2952035 = 4428053) B4428053
theorem B4148081 : Blo 1841622 4148081 := bstep (se 2 (by rfl) ⟨1555530, by rfl⟩ : syracuseStep 4148081 = 3111061) B3111061
theorem B2763635 : Blo 1841622 2763635 := bstep (se 1 (by rfl) ⟨2072726, by rfl⟩ : syracuseStep 2763635 = 4145453) B4145453
theorem B4148099 : Blo 1841622 4148099 := bstep (se 1 (by rfl) ⟨3111074, by rfl⟩ : syracuseStep 4148099 = 6222149) B6222149
theorem B2763665 : Blo 1841622 2763665 := bstep (se 2 (by rfl) ⟨1036374, by rfl⟩ : syracuseStep 2763665 = 2072749) B2072749
theorem B3107747 : Blo 1841622 3107747 := bstep (se 1 (by rfl) ⟨2330810, by rfl⟩ : syracuseStep 3107747 = 4661621) B4661621
theorem B2763683 : Blo 1841622 2763683 := bstep (se 1 (by rfl) ⟨2072762, by rfl⟩ : syracuseStep 2763683 = 4145525) B4145525
theorem B2763713 : Blo 1841622 2763713 := bstep (se 2 (by rfl) ⟨1036392, by rfl⟩ : syracuseStep 2763713 = 2072785) B2072785
theorem B2763731 : Blo 1841622 2763731 := bstep (se 1 (by rfl) ⟨2072798, by rfl⟩ : syracuseStep 2763731 = 4145597) B4145597
theorem B2763761 : Blo 1841622 2763761 := bstep (se 2 (by rfl) ⟨1036410, by rfl⟩ : syracuseStep 2763761 = 2072821) B2072821
theorem B2763779 : Blo 1841622 2763779 := bstep (se 1 (by rfl) ⟨2072834, by rfl⟩ : syracuseStep 2763779 = 4145669) B4145669
theorem B2763809 : Blo 1841622 2763809 := bstep (se 2 (by rfl) ⟨1036428, by rfl⟩ : syracuseStep 2763809 = 2072857) B2072857
theorem B3107875 : Blo 1841622 3107875 := bstep (se 1 (by rfl) ⟨2330906, by rfl⟩ : syracuseStep 3107875 = 4661813) B4661813
theorem B2763827 : Blo 1841622 2763827 := bstep (se 1 (by rfl) ⟨2072870, by rfl⟩ : syracuseStep 2763827 = 4145741) B4145741
theorem B8850509 : Blo 1841622 8850509 := bstep (se 3 (by rfl) ⟨1659470, by rfl⟩ : syracuseStep 8850509 = 3318941) B3318941
theorem B2763857 : Blo 1841622 2763857 := bstep (se 2 (by rfl) ⟨1036446, by rfl⟩ : syracuseStep 2763857 = 2072893) B2072893
theorem B2763875 : Blo 1841622 2763875 := bstep (se 1 (by rfl) ⟨2072906, by rfl⟩ : syracuseStep 2763875 = 4145813) B4145813
theorem B2763905 : Blo 1841622 2763905 := bstep (se 2 (by rfl) ⟨1036464, by rfl⟩ : syracuseStep 2763905 = 2072929) B2072929
theorem B2763923 : Blo 1841622 2763923 := bstep (se 1 (by rfl) ⟨2072942, by rfl⟩ : syracuseStep 2763923 = 4145885) B4145885
theorem B3108017 : Blo 1841622 3108017 := bstep (se 2 (by rfl) ⟨1165506, by rfl⟩ : syracuseStep 3108017 = 2331013) B2331013
theorem B2763953 : Blo 1841622 2763953 := bstep (se 2 (by rfl) ⟨1036482, by rfl⟩ : syracuseStep 2763953 = 2072965) B2072965
theorem B5246147 : Blo 1841622 5246147 := bstep (se 1 (by rfl) ⟨3934610, by rfl⟩ : syracuseStep 5246147 = 7869221) B7869221
theorem B2763971 : Blo 1841622 2763971 := bstep (se 1 (by rfl) ⟨2072978, by rfl⟩ : syracuseStep 2763971 = 4145957) B4145957
theorem B2764001 : Blo 1841622 2764001 := bstep (se 2 (by rfl) ⟨1036500, by rfl⟩ : syracuseStep 2764001 = 2073001) B2073001
theorem B6999281 : Blo 1841622 6999281 := bstep (se 2 (by rfl) ⟨2624730, by rfl⟩ : syracuseStep 6999281 = 5249461) B5249461
theorem B2764019 : Blo 1841622 2764019 := bstep (se 1 (by rfl) ⟨2073014, by rfl⟩ : syracuseStep 2764019 = 4146029) B4146029
theorem B6638861 : Blo 1841622 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B6221069 : Blo 1841622 6221069 := bstep (se 3 (by rfl) ⟨1166450, by rfl⟩ : syracuseStep 6221069 = 2332901) B2332901
theorem B2764049 : Blo 1841622 2764049 := bstep (se 2 (by rfl) ⟨1036518, by rfl⟩ : syracuseStep 2764049 = 2073037) B2073037
theorem B2764067 : Blo 1841622 2764067 := bstep (se 1 (by rfl) ⟨2073050, by rfl⟩ : syracuseStep 2764067 = 4146101) B4146101
theorem B11799857 : Blo 1841622 11799857 := bstep (se 2 (by rfl) ⟨4424946, by rfl⟩ : syracuseStep 11799857 = 8849893) B8849893
theorem B3108145 : Blo 1841622 3108145 := bstep (se 2 (by rfl) ⟨1165554, by rfl⟩ : syracuseStep 3108145 = 2331109) B2331109
theorem B8858929 : Blo 1841622 8858929 := bstep (se 2 (by rfl) ⟨3322098, by rfl⟩ : syracuseStep 8858929 = 6644197) B6644197
theorem B23604533 : Blo 1841622 23604533 := bstep (se 5 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 23604533 = 2212925) B2212925
theorem B2764097 : Blo 1841622 2764097 := bstep (se 2 (by rfl) ⟨1036536, by rfl⟩ : syracuseStep 2764097 = 2073073) B2073073
theorem B2624833 : Blo 1841622 2624833 := bstep (se 2 (by rfl) ⟨984312, by rfl⟩ : syracuseStep 2624833 = 1968625) B1968625
theorem B6221123 : Blo 1841622 6221123 := bstep (se 1 (by rfl) ⟨4665842, by rfl⟩ : syracuseStep 6221123 = 9331685) B9331685
theorem B3108179 : Blo 1841622 3108179 := bstep (se 1 (by rfl) ⟨2331134, by rfl⟩ : syracuseStep 3108179 = 4662269) B4662269
theorem B2764115 : Blo 1841622 2764115 := bstep (se 1 (by rfl) ⟨2073086, by rfl⟩ : syracuseStep 2764115 = 4146173) B4146173
theorem B15748451 : Blo 1841622 15748451 := bstep (se 1 (by rfl) ⟨11811338, by rfl⟩ : syracuseStep 15748451 = 23622677) B23622677
theorem B2764145 : Blo 1841622 2764145 := bstep (se 2 (by rfl) ⟨1036554, by rfl⟩ : syracuseStep 2764145 = 2073109) B2073109
theorem B2764163 : Blo 1841622 2764163 := bstep (se 1 (by rfl) ⟨2073122, by rfl⟩ : syracuseStep 2764163 = 4146245) B4146245
theorem B2764193 : Blo 1841622 2764193 := bstep (se 2 (by rfl) ⟨1036572, by rfl⟩ : syracuseStep 2764193 = 2073145) B2073145
theorem B5615021 : Blo 1841622 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B3239345 : Blo 1841622 3239345 := bstep (se 2 (by rfl) ⟨1214754, by rfl⟩ : syracuseStep 3239345 = 2429509) B2429509
theorem B2764211 : Blo 1841622 2764211 := bstep (se 1 (by rfl) ⟨2073158, by rfl⟩ : syracuseStep 2764211 = 4146317) B4146317
theorem B5680579 : Blo 1841622 5680579 := bstep (se 1 (by rfl) ⟨4260434, by rfl⟩ : syracuseStep 5680579 = 8520869) B8520869
theorem B2764241 : Blo 1841622 2764241 := bstep (se 2 (by rfl) ⟨1036590, by rfl⟩ : syracuseStep 2764241 = 2073181) B2073181
theorem B3108307 : Blo 1841622 3108307 := bstep (se 1 (by rfl) ⟨2331230, by rfl⟩ : syracuseStep 3108307 = 4662461) B4662461
theorem B2764259 : Blo 1841622 2764259 := bstep (se 1 (by rfl) ⟨2073194, by rfl⟩ : syracuseStep 2764259 = 4146389) B4146389
theorem B3935729 : Blo 1841622 3935729 := bstep (se 2 (by rfl) ⟨1475898, by rfl⟩ : syracuseStep 3935729 = 2951797) B2951797
theorem B2764289 : Blo 1841622 2764289 := bstep (se 2 (by rfl) ⟨1036608, by rfl⟩ : syracuseStep 2764289 = 2073217) B2073217
theorem B5246477 : Blo 1841622 5246477 := bstep (se 3 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 5246477 = 1967429) B1967429
theorem B2764307 : Blo 1841622 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B2764337 : Blo 1841622 2764337 := bstep (se 2 (by rfl) ⟨1036626, by rfl⟩ : syracuseStep 2764337 = 2073253) B2073253
theorem B2764355 : Blo 1841622 2764355 := bstep (se 1 (by rfl) ⟨2073266, by rfl⟩ : syracuseStep 2764355 = 4146533) B4146533
theorem B5246545 : Blo 1841622 5246545 := bstep (se 2 (by rfl) ⟨1967454, by rfl⟩ : syracuseStep 5246545 = 3934909) B3934909
theorem B6221393 : Blo 1841622 6221393 := bstep (se 2 (by rfl) ⟨2333022, by rfl⟩ : syracuseStep 6221393 = 4666045) B4666045
theorem B3108449 : Blo 1841622 3108449 := bstep (se 2 (by rfl) ⟨1165668, by rfl⟩ : syracuseStep 3108449 = 2331337) B2331337
theorem B2764385 : Blo 1841622 2764385 := bstep (se 2 (by rfl) ⟨1036644, by rfl⟩ : syracuseStep 2764385 = 2073289) B2073289
theorem B2764403 : Blo 1841622 2764403 := bstep (se 1 (by rfl) ⟨2073302, by rfl⟩ : syracuseStep 2764403 = 4146605) B4146605
theorem B2764433 : Blo 1841622 2764433 := bstep (se 2 (by rfl) ⟨1036662, by rfl⟩ : syracuseStep 2764433 = 2073325) B2073325
theorem B2363027 : Blo 1841622 2363027 := bstep (se 1 (by rfl) ⟨1772270, by rfl⟩ : syracuseStep 2363027 = 3544541) B3544541
theorem B2764451 : Blo 1841622 2764451 := bstep (se 1 (by rfl) ⟨2073338, by rfl⟩ : syracuseStep 2764451 = 4146677) B4146677
theorem B2764481 : Blo 1841622 2764481 := bstep (se 2 (by rfl) ⟨1036680, by rfl⟩ : syracuseStep 2764481 = 2073361) B2073361
theorem B2764499 : Blo 1841622 2764499 := bstep (se 1 (by rfl) ⟨2073374, by rfl⟩ : syracuseStep 2764499 = 4146749) B4146749
theorem B3108577 : Blo 1841622 3108577 := bstep (se 2 (by rfl) ⟨1165716, by rfl⟩ : syracuseStep 3108577 = 2331433) B2331433
theorem B4665073 : Blo 1841622 4665073 := bstep (se 2 (by rfl) ⟨1749402, by rfl⟩ : syracuseStep 4665073 = 3498805) B3498805
theorem B2764529 : Blo 1841622 2764529 := bstep (se 2 (by rfl) ⟨1036698, by rfl⟩ : syracuseStep 2764529 = 2073397) B2073397
theorem B3108611 : Blo 1841622 3108611 := bstep (se 1 (by rfl) ⟨2331458, by rfl⟩ : syracuseStep 3108611 = 4662917) B4662917
theorem B2764547 : Blo 1841622 2764547 := bstep (se 1 (by rfl) ⟨2073410, by rfl⟩ : syracuseStep 2764547 = 4146821) B4146821
theorem B2764577 : Blo 1841622 2764577 := bstep (se 2 (by rfl) ⟨1036716, by rfl⟩ : syracuseStep 2764577 = 2073433) B2073433
theorem B2764595 : Blo 1841622 2764595 := bstep (se 1 (by rfl) ⟨2073446, by rfl⟩ : syracuseStep 2764595 = 4146893) B4146893
theorem B2953027 : Blo 1841622 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B2764625 : Blo 1841622 2764625 := bstep (se 2 (by rfl) ⟨1036734, by rfl⟩ : syracuseStep 2764625 = 2073469) B2073469
theorem B5246819 : Blo 1841622 5246819 := bstep (se 1 (by rfl) ⟨3935114, by rfl⟩ : syracuseStep 5246819 = 7870229) B7870229
theorem B2764643 : Blo 1841622 2764643 := bstep (se 1 (by rfl) ⟨2073482, by rfl⟩ : syracuseStep 2764643 = 4146965) B4146965
theorem B2764673 : Blo 1841622 2764673 := bstep (se 2 (by rfl) ⟨1036752, by rfl⟩ : syracuseStep 2764673 = 2073505) B2073505
theorem B3108739 : Blo 1841622 3108739 := bstep (se 1 (by rfl) ⟨2331554, by rfl⟩ : syracuseStep 3108739 = 4663109) B4663109
theorem B2764691 : Blo 1841622 2764691 := bstep (se 1 (by rfl) ⟨2073518, by rfl⟩ : syracuseStep 2764691 = 4147037) B4147037
theorem B10489763 : Blo 1841622 10489763 := bstep (se 1 (by rfl) ⟨7867322, by rfl⟩ : syracuseStep 10489763 = 15734645) B15734645
theorem B2764721 : Blo 1841622 2764721 := bstep (se 2 (by rfl) ⟨1036770, by rfl⟩ : syracuseStep 2764721 = 2073541) B2073541
theorem B2764739 : Blo 1841622 2764739 := bstep (se 1 (by rfl) ⟨2073554, by rfl⟩ : syracuseStep 2764739 = 4147109) B4147109
theorem B2764769 : Blo 1841622 2764769 := bstep (se 2 (by rfl) ⟨1036788, by rfl⟩ : syracuseStep 2764769 = 2073577) B2073577
theorem B11210723 : Blo 1841622 11210723 := bstep (se 1 (by rfl) ⟨8408042, by rfl⟩ : syracuseStep 11210723 = 16816085) B16816085
theorem B2764787 : Blo 1841622 2764787 := bstep (se 1 (by rfl) ⟨2073590, by rfl⟩ : syracuseStep 2764787 = 4147181) B4147181
theorem B4665347 : Blo 1841622 4665347 := bstep (se 1 (by rfl) ⟨3499010, by rfl⟩ : syracuseStep 4665347 = 6998021) B6998021
theorem B3108881 : Blo 1841622 3108881 := bstep (se 2 (by rfl) ⟨1165830, by rfl⟩ : syracuseStep 3108881 = 2331661) B2331661
theorem B2764817 : Blo 1841622 2764817 := bstep (se 2 (by rfl) ⟨1036806, by rfl⟩ : syracuseStep 2764817 = 2073613) B2073613
theorem B2764835 : Blo 1841622 2764835 := bstep (se 1 (by rfl) ⟨2073626, by rfl⟩ : syracuseStep 2764835 = 4147253) B4147253
theorem B2764865 : Blo 1841622 2764865 := bstep (se 2 (by rfl) ⟨1036824, by rfl⟩ : syracuseStep 2764865 = 2073649) B2073649
theorem B2764883 : Blo 1841622 2764883 := bstep (se 1 (by rfl) ⟨2073662, by rfl⟩ : syracuseStep 2764883 = 4147325) B4147325
theorem B6221933 : Blo 1841622 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B2764913 : Blo 1841622 2764913 := bstep (se 2 (by rfl) ⟨1036842, by rfl⟩ : syracuseStep 2764913 = 2073685) B2073685
theorem B2764931 : Blo 1841622 2764931 := bstep (se 1 (by rfl) ⟨2073698, by rfl⟩ : syracuseStep 2764931 = 4147397) B4147397
theorem B3109009 : Blo 1841622 3109009 := bstep (se 2 (by rfl) ⟨1165878, by rfl⟩ : syracuseStep 3109009 = 2331757) B2331757
theorem B2764961 : Blo 1841622 2764961 := bstep (se 2 (by rfl) ⟨1036860, by rfl⟩ : syracuseStep 2764961 = 2073721) B2073721
theorem B3322019 : Blo 1841622 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B6221987 : Blo 1841622 6221987 := bstep (se 1 (by rfl) ⟨4666490, by rfl⟩ : syracuseStep 6221987 = 9332981) B9332981
theorem B6729905 : Blo 1841622 6729905 := bstep (se 2 (by rfl) ⟨2523714, by rfl⟩ : syracuseStep 6729905 = 5047429) B5047429
theorem B3109043 : Blo 1841622 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B2764979 : Blo 1841622 2764979 := bstep (se 1 (by rfl) ⟨2073734, by rfl⟩ : syracuseStep 2764979 = 4147469) B4147469
theorem B4665539 : Blo 1841622 4665539 := bstep (se 1 (by rfl) ⟨3499154, by rfl⟩ : syracuseStep 4665539 = 6998309) B6998309
theorem B17952965 : Blo 1841622 17952965 := bstep (se 4 (by rfl) ⟨1683090, by rfl⟩ : syracuseStep 17952965 = 3366181) B3366181
theorem B2765009 : Blo 1841622 2765009 := bstep (se 2 (by rfl) ⟨1036878, by rfl⟩ : syracuseStep 2765009 = 2073757) B2073757
theorem B2330851 : Blo 1841622 2330851 := bstep (se 1 (by rfl) ⟨1748138, by rfl⟩ : syracuseStep 2330851 = 3496277) B3496277
theorem B2765027 : Blo 1841622 2765027 := bstep (se 1 (by rfl) ⟨2073770, by rfl⟩ : syracuseStep 2765027 = 4147541) B4147541
theorem B2765057 : Blo 1841622 2765057 := bstep (se 2 (by rfl) ⟨1036896, by rfl⟩ : syracuseStep 2765057 = 2073793) B2073793
theorem B5902595 : Blo 1841622 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B2765075 : Blo 1841622 2765075 := bstep (se 1 (by rfl) ⟨2073806, by rfl⟩ : syracuseStep 2765075 = 4147613) B4147613
theorem B2765105 : Blo 1841622 2765105 := bstep (se 2 (by rfl) ⟨1036914, by rfl⟩ : syracuseStep 2765105 = 2073829) B2073829
theorem B3109171 : Blo 1841622 3109171 := bstep (se 1 (by rfl) ⟨2331878, by rfl⟩ : syracuseStep 3109171 = 4663757) B4663757
theorem B2330947 : Blo 1841622 2330947 := bstep (se 1 (by rfl) ⟨1748210, by rfl⟩ : syracuseStep 2330947 = 3496421) B3496421
theorem B2765123 : Blo 1841622 2765123 := bstep (se 1 (by rfl) ⟨2073842, by rfl⟩ : syracuseStep 2765123 = 4147685) B4147685
theorem B3936593 : Blo 1841622 3936593 := bstep (se 2 (by rfl) ⟨1476222, by rfl⟩ : syracuseStep 3936593 = 2952445) B2952445
theorem B2765153 : Blo 1841622 2765153 := bstep (se 2 (by rfl) ⟨1036932, by rfl⟩ : syracuseStep 2765153 = 2073865) B2073865
theorem B18903395 : Blo 1841622 18903395 := bstep (se 1 (by rfl) ⟨14177546, by rfl⟩ : syracuseStep 18903395 = 28355093) B28355093
theorem B19165553 : Blo 1841622 19165553 := bstep (se 2 (by rfl) ⟨7187082, by rfl⟩ : syracuseStep 19165553 = 14374165) B14374165
theorem B33616241 : Blo 1841622 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B2765171 : Blo 1841622 2765171 := bstep (se 1 (by rfl) ⟨2073878, by rfl⟩ : syracuseStep 2765171 = 4147757) B4147757
theorem B3150209 : Blo 1841622 3150209 := bstep (se 2 (by rfl) ⟨1181328, by rfl⟩ : syracuseStep 3150209 = 2362657) B2362657
theorem B2765201 : Blo 1841622 2765201 := bstep (se 2 (by rfl) ⟨1036950, by rfl⟩ : syracuseStep 2765201 = 2073901) B2073901
theorem B2765219 : Blo 1841622 2765219 := bstep (se 1 (by rfl) ⟨2073914, by rfl⟩ : syracuseStep 2765219 = 4147829) B4147829
theorem B3109313 : Blo 1841622 3109313 := bstep (se 2 (by rfl) ⟨1165992, by rfl⟩ : syracuseStep 3109313 = 2331985) B2331985
theorem B2765249 : Blo 1841622 2765249 := bstep (se 2 (by rfl) ⟨1036968, by rfl⟩ : syracuseStep 2765249 = 2073937) B2073937
theorem B2765267 : Blo 1841622 2765267 := bstep (se 1 (by rfl) ⟨2073950, by rfl⟩ : syracuseStep 2765267 = 4147901) B4147901
theorem B2765297 : Blo 1841622 2765297 := bstep (se 2 (by rfl) ⟨1036986, by rfl⟩ : syracuseStep 2765297 = 2073973) B2073973
theorem B2765315 : Blo 1841622 2765315 := bstep (se 1 (by rfl) ⟨2073986, by rfl⟩ : syracuseStep 2765315 = 4147973) B4147973
theorem B2765345 : Blo 1841622 2765345 := bstep (se 2 (by rfl) ⟨1037004, by rfl⟩ : syracuseStep 2765345 = 2074009) B2074009
theorem B7868963 : Blo 1841622 7868963 := bstep (se 1 (by rfl) ⟨5901722, by rfl⟩ : syracuseStep 7868963 = 11803445) B11803445
theorem B2765363 : Blo 1841622 2765363 := bstep (se 1 (by rfl) ⟨2074022, by rfl⟩ : syracuseStep 2765363 = 4148045) B4148045
theorem B3109441 : Blo 1841622 3109441 := bstep (se 2 (by rfl) ⟨1166040, by rfl⟩ : syracuseStep 3109441 = 2332081) B2332081
theorem B2363971 : Blo 1841622 2363971 := bstep (se 1 (by rfl) ⟨1772978, by rfl⟩ : syracuseStep 2363971 = 3545957) B3545957
theorem B2765393 : Blo 1841622 2765393 := bstep (se 2 (by rfl) ⟨1037022, by rfl⟩ : syracuseStep 2765393 = 2074045) B2074045
theorem B3109475 : Blo 1841622 3109475 := bstep (se 1 (by rfl) ⟨2332106, by rfl⟩ : syracuseStep 3109475 = 4664213) B4664213
theorem B2765411 : Blo 1841622 2765411 := bstep (se 1 (by rfl) ⟨2074058, by rfl⟩ : syracuseStep 2765411 = 4148117) B4148117
theorem B10498693 : Blo 1841622 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B5247661 : Blo 1841622 5247661 := bstep (se 3 (by rfl) ⟨983936, by rfl⟩ : syracuseStep 5247661 = 1967873) B1967873
theorem B3109603 : Blo 1841622 3109603 := bstep (se 1 (by rfl) ⟨2332202, by rfl⟩ : syracuseStep 3109603 = 4664405) B4664405
theorem B6992675 : Blo 1841622 6992675 := bstep (se 1 (by rfl) ⟨5244506, by rfl⟩ : syracuseStep 6992675 = 10489013) B10489013
theorem B6992689 : Blo 1841622 6992689 := bstep (se 2 (by rfl) ⟨2622258, by rfl⟩ : syracuseStep 6992689 = 5244517) B5244517
theorem B2331443 : Blo 1841622 2331443 := bstep (se 1 (by rfl) ⟨1748582, by rfl⟩ : syracuseStep 2331443 = 3497165) B3497165
theorem B22410053 : Blo 1841622 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B5247821 : Blo 1841622 5247821 := bstep (se 3 (by rfl) ⟨983966, by rfl⟩ : syracuseStep 5247821 = 1967933) B1967933
theorem B9327473 : Blo 1841622 9327473 := bstep (se 2 (by rfl) ⟨3497802, by rfl⟩ : syracuseStep 9327473 = 6995605) B6995605
theorem B3109745 : Blo 1841622 3109745 := bstep (se 2 (by rfl) ⟨1166154, by rfl⟩ : syracuseStep 3109745 = 2332309) B2332309
theorem B10097585 : Blo 1841622 10097585 := bstep (se 2 (by rfl) ⟨3786594, by rfl⟩ : syracuseStep 10097585 = 7573189) B7573189
theorem B3109873 : Blo 1841622 3109873 := bstep (se 2 (by rfl) ⟨1166202, by rfl⟩ : syracuseStep 3109873 = 2332405) B2332405
theorem B5903363 : Blo 1841622 5903363 := bstep (se 1 (by rfl) ⟨4427522, by rfl⟩ : syracuseStep 5903363 = 8855045) B8855045
theorem B5248003 : Blo 1841622 5248003 := bstep (se 1 (by rfl) ⟨3936002, by rfl⟩ : syracuseStep 5248003 = 7872005) B7872005
theorem B3109907 : Blo 1841622 3109907 := bstep (se 1 (by rfl) ⟨2332430, by rfl⟩ : syracuseStep 3109907 = 4664861) B4664861
theorem B4666481 : Blo 1841622 4666481 := bstep (se 2 (by rfl) ⟨1749930, by rfl⟩ : syracuseStep 4666481 = 3499861) B3499861
theorem B3110035 : Blo 1841622 3110035 := bstep (se 1 (by rfl) ⟨2332526, by rfl⟩ : syracuseStep 3110035 = 4665053) B4665053
theorem B4666531 : Blo 1841622 4666531 := bstep (se 1 (by rfl) ⟨3499898, by rfl⟩ : syracuseStep 4666531 = 6999797) B6999797
theorem B3110177 : Blo 1841622 3110177 := bstep (se 2 (by rfl) ⟨1166316, by rfl⟩ : syracuseStep 3110177 = 2332633) B2332633
theorem B5903761 : Blo 1841622 5903761 := bstep (se 2 (by rfl) ⟨2213910, by rfl⟩ : syracuseStep 5903761 = 4427821) B4427821
theorem B3110305 : Blo 1841622 3110305 := bstep (se 2 (by rfl) ⟨1166364, by rfl⟩ : syracuseStep 3110305 = 2332729) B2332729
theorem B3110339 : Blo 1841622 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B2332147 : Blo 1841622 2332147 := bstep (se 1 (by rfl) ⟨1749110, by rfl⟩ : syracuseStep 2332147 = 3498221) B3498221
theorem B5903875 : Blo 1841622 5903875 := bstep (se 1 (by rfl) ⟨4427906, by rfl⟩ : syracuseStep 5903875 = 8855813) B8855813
theorem B13276685 : Blo 1841622 13276685 := bstep (se 3 (by rfl) ⟨2489378, by rfl⟩ : syracuseStep 13276685 = 4978757) B4978757
theorem B3110467 : Blo 1841622 3110467 := bstep (se 1 (by rfl) ⟨2332850, by rfl⟩ : syracuseStep 3110467 = 4665701) B4665701
theorem B2332243 : Blo 1841622 2332243 := bstep (se 1 (by rfl) ⟨1749182, by rfl⟩ : syracuseStep 2332243 = 3498365) B3498365
theorem B15734371 : Blo 1841622 15734371 := bstep (se 1 (by rfl) ⟨11800778, by rfl⟩ : syracuseStep 15734371 = 23601557) B23601557
theorem B14939747 : Blo 1841622 14939747 := bstep (se 1 (by rfl) ⟨11204810, by rfl⟩ : syracuseStep 14939747 = 22409621) B22409621
theorem B3110609 : Blo 1841622 3110609 := bstep (se 2 (by rfl) ⟨1166478, by rfl⟩ : syracuseStep 3110609 = 2332957) B2332957
theorem B7870193 : Blo 1841622 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B3110737 : Blo 1841622 3110737 := bstep (se 2 (by rfl) ⟨1166526, by rfl⟩ : syracuseStep 3110737 = 2333053) B2333053
theorem B4978531 : Blo 1841622 4978531 := bstep (se 1 (by rfl) ⟨3733898, by rfl⟩ : syracuseStep 4978531 = 7467797) B7467797
theorem B4429667 : Blo 1841622 4429667 := bstep (se 1 (by rfl) ⟨3322250, by rfl⟩ : syracuseStep 4429667 = 6644501) B6644501
theorem B3110771 : Blo 1841622 3110771 := bstep (se 1 (by rfl) ⟨2333078, by rfl⟩ : syracuseStep 3110771 = 4666157) B4666157
theorem B3110899 : Blo 1841622 3110899 := bstep (se 1 (by rfl) ⟨2333174, by rfl⟩ : syracuseStep 3110899 = 4666349) B4666349
theorem B2332739 : Blo 1841622 2332739 := bstep (se 1 (by rfl) ⟨1749554, by rfl⟩ : syracuseStep 2332739 = 3499109) B3499109
theorem B2660449 : Blo 1841622 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B3111041 : Blo 1841622 3111041 := bstep (se 2 (by rfl) ⟨1166640, by rfl⟩ : syracuseStep 3111041 = 2333281) B2333281
theorem B4790449 : Blo 1841622 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B2660531 : Blo 1841622 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B6215885 : Blo 1841622 6215885 := bstep (se 3 (by rfl) ⟨1165478, by rfl⟩ : syracuseStep 6215885 = 2330957) B2330957
theorem B11802829 : Blo 1841622 11802829 := bstep (se 3 (by rfl) ⟨2213030, by rfl⟩ : syracuseStep 11802829 = 4426061) B4426061
theorem B5904593 : Blo 1841622 5904593 := bstep (se 2 (by rfl) ⟨2214222, by rfl⟩ : syracuseStep 5904593 = 4428445) B4428445
theorem B6994147 : Blo 1841622 6994147 := bstep (se 1 (by rfl) ⟨5245610, by rfl⟩ : syracuseStep 6994147 = 10491221) B10491221
theorem B6215939 : Blo 1841622 6215939 := bstep (se 1 (by rfl) ⟨4661954, by rfl⟩ : syracuseStep 6215939 = 9323909) B9323909
theorem B9328931 : Blo 1841622 9328931 := bstep (se 1 (by rfl) ⟨6996698, by rfl⟩ : syracuseStep 9328931 = 13993397) B13993397
theorem B5249393 : Blo 1841622 5249393 := bstep (se 2 (by rfl) ⟨1968522, by rfl⟩ : syracuseStep 5249393 = 3937045) B3937045
theorem B6306221 : Blo 1841622 6306221 := bstep (se 3 (by rfl) ⟨1182416, by rfl⟩ : syracuseStep 6306221 = 2364833) B2364833
theorem B1841635 : Blo 1841622 1841635 := bstep (se 1 (by rfl) ⟨1381226, by rfl⟩ : syracuseStep 1841635 = 2762453) B2762453
theorem B1841651 : Blo 1841622 1841651 := bstep (se 1 (by rfl) ⟨1381238, by rfl⟩ : syracuseStep 1841651 = 2762477) B2762477
theorem B1841667 : Blo 1841622 1841667 := bstep (se 1 (by rfl) ⟨1381250, by rfl⟩ : syracuseStep 1841667 = 2762501) B2762501
theorem B6216209 : Blo 1841622 6216209 := bstep (se 2 (by rfl) ⟨2331078, by rfl⟩ : syracuseStep 6216209 = 4662157) B4662157
theorem B1841683 : Blo 1841622 1841683 := bstep (se 1 (by rfl) ⟨1381262, by rfl⟩ : syracuseStep 1841683 = 2762525) B2762525
theorem B1841699 : Blo 1841622 1841699 := bstep (se 1 (by rfl) ⟨1381274, by rfl⟩ : syracuseStep 1841699 = 2762549) B2762549
theorem B1841715 : Blo 1841622 1841715 := bstep (se 1 (by rfl) ⟨1381286, by rfl⟩ : syracuseStep 1841715 = 2762573) B2762573
theorem B1841731 : Blo 1841622 1841731 := bstep (se 1 (by rfl) ⟨1381298, by rfl⟩ : syracuseStep 1841731 = 2762597) B2762597
theorem B1841747 : Blo 1841622 1841747 := bstep (se 1 (by rfl) ⟨1381310, by rfl⟩ : syracuseStep 1841747 = 2762621) B2762621
theorem B1841763 : Blo 1841622 1841763 := bstep (se 1 (by rfl) ⟨1381322, by rfl⟩ : syracuseStep 1841763 = 2762645) B2762645
theorem B1841779 : Blo 1841622 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B1841795 : Blo 1841622 1841795 := bstep (se 1 (by rfl) ⟨1381346, by rfl⟩ : syracuseStep 1841795 = 2762693) B2762693
theorem B4143761 : Blo 1841622 4143761 := bstep (se 2 (by rfl) ⟨1553910, by rfl⟩ : syracuseStep 4143761 = 3107821) B3107821
theorem B1841811 : Blo 1841622 1841811 := bstep (se 1 (by rfl) ⟨1381358, by rfl⟩ : syracuseStep 1841811 = 2762717) B2762717
theorem B4143779 : Blo 1841622 4143779 := bstep (se 1 (by rfl) ⟨3107834, by rfl⟩ : syracuseStep 4143779 = 6215669) B6215669
theorem B1841827 : Blo 1841622 1841827 := bstep (se 1 (by rfl) ⟨1381370, by rfl⟩ : syracuseStep 1841827 = 2762741) B2762741
theorem B2489011 : Blo 1841622 2489011 := bstep (se 1 (by rfl) ⟨1866758, by rfl⟩ : syracuseStep 2489011 = 3733517) B3733517
theorem B1841843 : Blo 1841622 1841843 := bstep (se 1 (by rfl) ⟨1381382, by rfl⟩ : syracuseStep 1841843 = 2762765) B2762765
theorem B1841859 : Blo 1841622 1841859 := bstep (se 1 (by rfl) ⟨1381394, by rfl⟩ : syracuseStep 1841859 = 2762789) B2762789
theorem B11205317 : Blo 1841622 11205317 := bstep (se 4 (by rfl) ⟨1050498, by rfl⟩ : syracuseStep 11205317 = 2100997) B2100997
theorem B1841875 : Blo 1841622 1841875 := bstep (se 1 (by rfl) ⟨1381406, by rfl⟩ : syracuseStep 1841875 = 2762813) B2762813
theorem B1841891 : Blo 1841622 1841891 := bstep (se 1 (by rfl) ⟨1381418, by rfl⟩ : syracuseStep 1841891 = 2762837) B2762837
theorem B5905133 : Blo 1841622 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B1841907 : Blo 1841622 1841907 := bstep (se 1 (by rfl) ⟨1381430, by rfl⟩ : syracuseStep 1841907 = 2762861) B2762861
theorem B1841923 : Blo 1841622 1841923 := bstep (se 1 (by rfl) ⟨1381442, by rfl⟩ : syracuseStep 1841923 = 2762885) B2762885
theorem B1841939 : Blo 1841622 1841939 := bstep (se 1 (by rfl) ⟨1381454, by rfl⟩ : syracuseStep 1841939 = 2762909) B2762909
theorem B1841955 : Blo 1841622 1841955 := bstep (se 1 (by rfl) ⟨1381466, by rfl⟩ : syracuseStep 1841955 = 2762933) B2762933
theorem B1841971 : Blo 1841622 1841971 := bstep (se 1 (by rfl) ⟨1381478, by rfl⟩ : syracuseStep 1841971 = 2762957) B2762957
theorem B1841987 : Blo 1841622 1841987 := bstep (se 1 (by rfl) ⟨1381490, by rfl⟩ : syracuseStep 1841987 = 2762981) B2762981
theorem B1842003 : Blo 1841622 1842003 := bstep (se 1 (by rfl) ⟨1381502, by rfl⟩ : syracuseStep 1842003 = 2763005) B2763005
theorem B1842019 : Blo 1841622 1842019 := bstep (se 1 (by rfl) ⟨1381514, by rfl⟩ : syracuseStep 1842019 = 2763029) B2763029
theorem B4979569 : Blo 1841622 4979569 := bstep (se 2 (by rfl) ⟨1867338, by rfl⟩ : syracuseStep 4979569 = 3734677) B3734677
theorem B1842035 : Blo 1841622 1842035 := bstep (se 1 (by rfl) ⟨1381526, by rfl⟩ : syracuseStep 1842035 = 2763053) B2763053
theorem B1842051 : Blo 1841622 1842051 := bstep (se 1 (by rfl) ⟨1381538, by rfl⟩ : syracuseStep 1842051 = 2763077) B2763077
theorem B1842067 : Blo 1841622 1842067 := bstep (se 1 (by rfl) ⟨1381550, by rfl⟩ : syracuseStep 1842067 = 2763101) B2763101
theorem B1842083 : Blo 1841622 1842083 := bstep (se 1 (by rfl) ⟨1381562, by rfl⟩ : syracuseStep 1842083 = 2763125) B2763125
theorem B4144049 : Blo 1841622 4144049 := bstep (se 2 (by rfl) ⟨1554018, by rfl⟩ : syracuseStep 4144049 = 3108037) B3108037
theorem B1842099 : Blo 1841622 1842099 := bstep (se 1 (by rfl) ⟨1381574, by rfl⟩ : syracuseStep 1842099 = 2763149) B2763149
theorem B4144067 : Blo 1841622 4144067 := bstep (se 1 (by rfl) ⟨3108050, by rfl⟩ : syracuseStep 4144067 = 6216101) B6216101
theorem B1842115 : Blo 1841622 1842115 := bstep (se 1 (by rfl) ⟨1381586, by rfl⟩ : syracuseStep 1842115 = 2763173) B2763173
theorem B1842131 : Blo 1841622 1842131 := bstep (se 1 (by rfl) ⟨1381598, by rfl⟩ : syracuseStep 1842131 = 2763197) B2763197
theorem B1842147 : Blo 1841622 1842147 := bstep (se 1 (by rfl) ⟨1381610, by rfl⟩ : syracuseStep 1842147 = 2763221) B2763221
theorem B3496945 : Blo 1841622 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B1842163 : Blo 1841622 1842163 := bstep (se 1 (by rfl) ⟨1381622, by rfl⟩ : syracuseStep 1842163 = 2763245) B2763245
theorem B1842179 : Blo 1841622 1842179 := bstep (se 1 (by rfl) ⟨1381634, by rfl⟩ : syracuseStep 1842179 = 2763269) B2763269
theorem B17947661 : Blo 1841622 17947661 := bstep (se 3 (by rfl) ⟨3365186, by rfl⟩ : syracuseStep 17947661 = 6730373) B6730373
theorem B1842195 : Blo 1841622 1842195 := bstep (se 1 (by rfl) ⟨1381646, by rfl⟩ : syracuseStep 1842195 = 2763293) B2763293
theorem B1842211 : Blo 1841622 1842211 := bstep (se 1 (by rfl) ⟨1381658, by rfl⟩ : syracuseStep 1842211 = 2763317) B2763317
theorem B6216749 : Blo 1841622 6216749 := bstep (se 3 (by rfl) ⟨1165640, by rfl⟩ : syracuseStep 6216749 = 2331281) B2331281
theorem B1842227 : Blo 1841622 1842227 := bstep (se 1 (by rfl) ⟨1381670, by rfl⟩ : syracuseStep 1842227 = 2763341) B2763341
theorem B1842243 : Blo 1841622 1842243 := bstep (se 1 (by rfl) ⟨1381682, by rfl⟩ : syracuseStep 1842243 = 2763365) B2763365
theorem B9329741 : Blo 1841622 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B1842259 : Blo 1841622 1842259 := bstep (se 1 (by rfl) ⟨1381694, by rfl⟩ : syracuseStep 1842259 = 2763389) B2763389
theorem B6216803 : Blo 1841622 6216803 := bstep (se 1 (by rfl) ⟨4662602, by rfl⟩ : syracuseStep 6216803 = 9325205) B9325205
theorem B1842275 : Blo 1841622 1842275 := bstep (se 1 (by rfl) ⟨1381706, by rfl⟩ : syracuseStep 1842275 = 2763413) B2763413
theorem B1842291 : Blo 1841622 1842291 := bstep (se 1 (by rfl) ⟨1381718, by rfl⟩ : syracuseStep 1842291 = 2763437) B2763437
theorem B1842307 : Blo 1841622 1842307 := bstep (se 1 (by rfl) ⟨1381730, by rfl⟩ : syracuseStep 1842307 = 2763461) B2763461
theorem B1842323 : Blo 1841622 1842323 := bstep (se 1 (by rfl) ⟨1381742, by rfl⟩ : syracuseStep 1842323 = 2763485) B2763485
theorem B1842339 : Blo 1841622 1842339 := bstep (se 1 (by rfl) ⟨1381754, by rfl⟩ : syracuseStep 1842339 = 2763509) B2763509
theorem B1842355 : Blo 1841622 1842355 := bstep (se 1 (by rfl) ⟨1381766, by rfl⟩ : syracuseStep 1842355 = 2763533) B2763533
theorem B1842371 : Blo 1841622 1842371 := bstep (se 1 (by rfl) ⟨1381778, by rfl⟩ : syracuseStep 1842371 = 2763557) B2763557
theorem B4144337 : Blo 1841622 4144337 := bstep (se 2 (by rfl) ⟨1554126, by rfl⟩ : syracuseStep 4144337 = 3108253) B3108253
theorem B1842387 : Blo 1841622 1842387 := bstep (se 1 (by rfl) ⟨1381790, by rfl⟩ : syracuseStep 1842387 = 2763581) B2763581
theorem B4144355 : Blo 1841622 4144355 := bstep (se 1 (by rfl) ⟨3108266, by rfl⟩ : syracuseStep 4144355 = 6216533) B6216533
theorem B1842403 : Blo 1841622 1842403 := bstep (se 1 (by rfl) ⟨1381802, by rfl⟩ : syracuseStep 1842403 = 2763605) B2763605
theorem B1842419 : Blo 1841622 1842419 := bstep (se 1 (by rfl) ⟨1381814, by rfl⟩ : syracuseStep 1842419 = 2763629) B2763629
theorem B1842435 : Blo 1841622 1842435 := bstep (se 1 (by rfl) ⟨1381826, by rfl⟩ : syracuseStep 1842435 = 2763653) B2763653
theorem B1842451 : Blo 1841622 1842451 := bstep (se 1 (by rfl) ⟨1381838, by rfl⟩ : syracuseStep 1842451 = 2763677) B2763677
theorem B1842467 : Blo 1841622 1842467 := bstep (se 1 (by rfl) ⟨1381850, by rfl⟩ : syracuseStep 1842467 = 2763701) B2763701
theorem B1842483 : Blo 1841622 1842483 := bstep (se 1 (by rfl) ⟨1381862, by rfl⟩ : syracuseStep 1842483 = 2763725) B2763725
theorem B26934581 : Blo 1841622 26934581 := bstep (se 5 (by rfl) ⟨1262558, by rfl⟩ : syracuseStep 26934581 = 2525117) B2525117
theorem B1842499 : Blo 1841622 1842499 := bstep (se 1 (by rfl) ⟨1381874, by rfl⟩ : syracuseStep 1842499 = 2763749) B2763749
theorem B1842515 : Blo 1841622 1842515 := bstep (se 1 (by rfl) ⟨1381886, by rfl⟩ : syracuseStep 1842515 = 2763773) B2763773
theorem B1842531 : Blo 1841622 1842531 := bstep (se 1 (by rfl) ⟨1381898, by rfl⟩ : syracuseStep 1842531 = 2763797) B2763797
theorem B6217073 : Blo 1841622 6217073 := bstep (se 2 (by rfl) ⟨2331402, by rfl⟩ : syracuseStep 6217073 = 4662805) B4662805
theorem B1842547 : Blo 1841622 1842547 := bstep (se 1 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 1842547 = 2763821) B2763821
theorem B2071939 : Blo 1841622 2071939 := bstep (se 1 (by rfl) ⟨1553954, by rfl⟩ : syracuseStep 2071939 = 3107909) B3107909
theorem B3497347 : Blo 1841622 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B1842563 : Blo 1841622 1842563 := bstep (se 1 (by rfl) ⟨1381922, by rfl⟩ : syracuseStep 1842563 = 2763845) B2763845
theorem B1842579 : Blo 1841622 1842579 := bstep (se 1 (by rfl) ⟨1381934, by rfl⟩ : syracuseStep 1842579 = 2763869) B2763869
theorem B1842595 : Blo 1841622 1842595 := bstep (se 1 (by rfl) ⟨1381946, by rfl⟩ : syracuseStep 1842595 = 2763893) B2763893
theorem B3497393 : Blo 1841622 3497393 := bstep (se 2 (by rfl) ⟨1311522, by rfl⟩ : syracuseStep 3497393 = 2623045) B2623045
theorem B1842611 : Blo 1841622 1842611 := bstep (se 1 (by rfl) ⟨1381958, by rfl⟩ : syracuseStep 1842611 = 2763917) B2763917
theorem B1842627 : Blo 1841622 1842627 := bstep (se 1 (by rfl) ⟨1381970, by rfl⟩ : syracuseStep 1842627 = 2763941) B2763941
theorem B1842643 : Blo 1841622 1842643 := bstep (se 1 (by rfl) ⟨1381982, by rfl⟩ : syracuseStep 1842643 = 2763965) B2763965
theorem B9960931 : Blo 1841622 9960931 := bstep (se 1 (by rfl) ⟨7470698, by rfl⟩ : syracuseStep 9960931 = 14941397) B14941397
theorem B1842659 : Blo 1841622 1842659 := bstep (se 1 (by rfl) ⟨1381994, by rfl⟩ : syracuseStep 1842659 = 2763989) B2763989
theorem B4144625 : Blo 1841622 4144625 := bstep (se 2 (by rfl) ⟨1554234, by rfl⟩ : syracuseStep 4144625 = 3108469) B3108469
theorem B1842675 : Blo 1841622 1842675 := bstep (se 1 (by rfl) ⟨1382006, by rfl⟩ : syracuseStep 1842675 = 2764013) B2764013
theorem B4144643 : Blo 1841622 4144643 := bstep (se 1 (by rfl) ⟨3108482, by rfl⟩ : syracuseStep 4144643 = 6216965) B6216965
theorem B1842691 : Blo 1841622 1842691 := bstep (se 1 (by rfl) ⟨1382018, by rfl⟩ : syracuseStep 1842691 = 2764037) B2764037
theorem B2072083 : Blo 1841622 2072083 := bstep (se 1 (by rfl) ⟨1554062, by rfl⟩ : syracuseStep 2072083 = 3108125) B3108125
theorem B1842707 : Blo 1841622 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B1842723 : Blo 1841622 1842723 := bstep (se 1 (by rfl) ⟨1382042, by rfl⟩ : syracuseStep 1842723 = 2764085) B2764085
theorem B1842739 : Blo 1841622 1842739 := bstep (se 1 (by rfl) ⟨1382054, by rfl⟩ : syracuseStep 1842739 = 2764109) B2764109
theorem B1842755 : Blo 1841622 1842755 := bstep (se 1 (by rfl) ⟨1382066, by rfl⟩ : syracuseStep 1842755 = 2764133) B2764133
theorem B1842771 : Blo 1841622 1842771 := bstep (se 1 (by rfl) ⟨1382078, by rfl⟩ : syracuseStep 1842771 = 2764157) B2764157
theorem B1842787 : Blo 1841622 1842787 := bstep (se 1 (by rfl) ⟨1382090, by rfl⟩ : syracuseStep 1842787 = 2764181) B2764181
theorem B13999715 : Blo 1841622 13999715 := bstep (se 1 (by rfl) ⟨10499786, by rfl⟩ : syracuseStep 13999715 = 20999573) B20999573
theorem B1842803 : Blo 1841622 1842803 := bstep (se 1 (by rfl) ⟨1382102, by rfl⟩ : syracuseStep 1842803 = 2764205) B2764205
theorem B1842819 : Blo 1841622 1842819 := bstep (se 1 (by rfl) ⟨1382114, by rfl⟩ : syracuseStep 1842819 = 2764229) B2764229
theorem B1842835 : Blo 1841622 1842835 := bstep (se 1 (by rfl) ⟨1382126, by rfl⟩ : syracuseStep 1842835 = 2764253) B2764253
theorem B2072227 : Blo 1841622 2072227 := bstep (se 1 (by rfl) ⟨1554170, by rfl⟩ : syracuseStep 2072227 = 3108341) B3108341
theorem B1842851 : Blo 1841622 1842851 := bstep (se 1 (by rfl) ⟨1382138, by rfl⟩ : syracuseStep 1842851 = 2764277) B2764277
theorem B1842867 : Blo 1841622 1842867 := bstep (se 1 (by rfl) ⟨1382150, by rfl⟩ : syracuseStep 1842867 = 2764301) B2764301
theorem B1842883 : Blo 1841622 1842883 := bstep (se 1 (by rfl) ⟨1382162, by rfl⟩ : syracuseStep 1842883 = 2764325) B2764325
theorem B3497681 : Blo 1841622 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B1842899 : Blo 1841622 1842899 := bstep (se 1 (by rfl) ⟨1382174, by rfl⟩ : syracuseStep 1842899 = 2764349) B2764349
theorem B1842915 : Blo 1841622 1842915 := bstep (se 1 (by rfl) ⟨1382186, by rfl⟩ : syracuseStep 1842915 = 2764373) B2764373
theorem B1842931 : Blo 1841622 1842931 := bstep (se 1 (by rfl) ⟨1382198, by rfl⟩ : syracuseStep 1842931 = 2764397) B2764397
theorem B1842947 : Blo 1841622 1842947 := bstep (se 1 (by rfl) ⟨1382210, by rfl⟩ : syracuseStep 1842947 = 2764421) B2764421
theorem B19422989 : Blo 1841622 19422989 := bstep (se 3 (by rfl) ⟨3641810, by rfl⟩ : syracuseStep 19422989 = 7283621) B7283621
theorem B4144913 : Blo 1841622 4144913 := bstep (se 2 (by rfl) ⟨1554342, by rfl⟩ : syracuseStep 4144913 = 3108685) B3108685
theorem B1842963 : Blo 1841622 1842963 := bstep (se 1 (by rfl) ⟨1382222, by rfl⟩ : syracuseStep 1842963 = 2764445) B2764445
theorem B4144931 : Blo 1841622 4144931 := bstep (se 1 (by rfl) ⟨3108698, by rfl⟩ : syracuseStep 4144931 = 6217397) B6217397
theorem B1842979 : Blo 1841622 1842979 := bstep (se 1 (by rfl) ⟨1382234, by rfl⟩ : syracuseStep 1842979 = 2764469) B2764469
theorem B2072371 : Blo 1841622 2072371 := bstep (se 1 (by rfl) ⟨1554278, by rfl⟩ : syracuseStep 2072371 = 3108557) B3108557
theorem B1842995 : Blo 1841622 1842995 := bstep (se 1 (by rfl) ⟨1382246, by rfl⟩ : syracuseStep 1842995 = 2764493) B2764493
theorem B1843011 : Blo 1841622 1843011 := bstep (se 1 (by rfl) ⟨1382258, by rfl⟩ : syracuseStep 1843011 = 2764517) B2764517
theorem B1843027 : Blo 1841622 1843027 := bstep (se 1 (by rfl) ⟨1382270, by rfl⟩ : syracuseStep 1843027 = 2764541) B2764541
theorem B1843043 : Blo 1841622 1843043 := bstep (se 1 (by rfl) ⟨1382282, by rfl⟩ : syracuseStep 1843043 = 2764565) B2764565
theorem B5603185 : Blo 1841622 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B13467505 : Blo 1841622 13467505 := bstep (se 2 (by rfl) ⟨5050314, by rfl⟩ : syracuseStep 13467505 = 10100629) B10100629
theorem B1843059 : Blo 1841622 1843059 := bstep (se 1 (by rfl) ⟨1382294, by rfl⟩ : syracuseStep 1843059 = 2764589) B2764589
theorem B1843075 : Blo 1841622 1843075 := bstep (se 1 (by rfl) ⟨1382306, by rfl⟩ : syracuseStep 1843075 = 2764613) B2764613
theorem B6217613 : Blo 1841622 6217613 := bstep (se 3 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 6217613 = 2331605) B2331605
theorem B1843091 : Blo 1841622 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1843107 : Blo 1841622 1843107 := bstep (se 1 (by rfl) ⟨1382330, by rfl⟩ : syracuseStep 1843107 = 2764661) B2764661
theorem B1843123 : Blo 1841622 1843123 := bstep (se 1 (by rfl) ⟨1382342, by rfl⟩ : syracuseStep 1843123 = 2764685) B2764685
theorem B2072515 : Blo 1841622 2072515 := bstep (se 1 (by rfl) ⟨1554386, by rfl⟩ : syracuseStep 2072515 = 3108773) B3108773
theorem B6217667 : Blo 1841622 6217667 := bstep (se 1 (by rfl) ⟨4663250, by rfl⟩ : syracuseStep 6217667 = 9326501) B9326501
theorem B1843139 : Blo 1841622 1843139 := bstep (se 1 (by rfl) ⟨1382354, by rfl⟩ : syracuseStep 1843139 = 2764709) B2764709
theorem B1843155 : Blo 1841622 1843155 := bstep (se 1 (by rfl) ⟨1382366, by rfl⟩ : syracuseStep 1843155 = 2764733) B2764733
theorem B1843171 : Blo 1841622 1843171 := bstep (se 1 (by rfl) ⟨1382378, by rfl⟩ : syracuseStep 1843171 = 2764757) B2764757
theorem B1843187 : Blo 1841622 1843187 := bstep (se 1 (by rfl) ⟨1382390, by rfl⟩ : syracuseStep 1843187 = 2764781) B2764781
theorem B2072587 : Blo 1841622 2072587 := bstep (se 1 (by rfl) ⟨1554440, by rfl⟩ : syracuseStep 2072587 = 3108881) B3108881
theorem B1843211 : Blo 1841622 1843211 := bstep (se 1 (by rfl) ⟨1382408, by rfl⟩ : syracuseStep 1843211 = 2764817) B2764817
theorem B1843223 : Blo 1841622 1843223 := bstep (se 1 (by rfl) ⟨1382417, by rfl⟩ : syracuseStep 1843223 = 2764835) B2764835
theorem B1843243 : Blo 1841622 1843243 := bstep (se 1 (by rfl) ⟨1382432, by rfl⟩ : syracuseStep 1843243 = 2764865) B2764865
theorem B1843255 : Blo 1841622 1843255 := bstep (se 1 (by rfl) ⟨1382441, by rfl⟩ : syracuseStep 1843255 = 2764883) B2764883
theorem B1843275 : Blo 1841622 1843275 := bstep (se 1 (by rfl) ⟨1382456, by rfl⟩ : syracuseStep 1843275 = 2764913) B2764913
theorem B1843287 : Blo 1841622 1843287 := bstep (se 1 (by rfl) ⟨1382465, by rfl⟩ : syracuseStep 1843287 = 2764931) B2764931
theorem B1843307 : Blo 1841622 1843307 := bstep (se 1 (by rfl) ⟨1382480, by rfl⟩ : syracuseStep 1843307 = 2764961) B2764961
theorem B2072695 : Blo 1841622 2072695 := bstep (se 1 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 2072695 = 3109043) B3109043
theorem B1843319 : Blo 1841622 1843319 := bstep (se 1 (by rfl) ⟨1382489, by rfl⟩ : syracuseStep 1843319 = 2764979) B2764979
theorem B3547265 : Blo 1841622 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B11968643 : Blo 1841622 11968643 := bstep (se 1 (by rfl) ⟨8976482, by rfl⟩ : syracuseStep 11968643 = 17952965) B17952965
theorem B4145291 : Blo 1841622 4145291 := bstep (se 1 (by rfl) ⟨3108968, by rfl⟩ : syracuseStep 4145291 = 6217937) B6217937
theorem B1843339 : Blo 1841622 1843339 := bstep (se 1 (by rfl) ⟨1382504, by rfl⟩ : syracuseStep 1843339 = 2765009) B2765009
theorem B1843351 : Blo 1841622 1843351 := bstep (se 1 (by rfl) ⟨1382513, by rfl⟩ : syracuseStep 1843351 = 2765027) B2765027
theorem B3498137 : Blo 1841622 3498137 := bstep (se 2 (by rfl) ⟨1311801, by rfl⟩ : syracuseStep 3498137 = 2623603) B2623603
theorem B1843371 : Blo 1841622 1843371 := bstep (se 1 (by rfl) ⟨1382528, by rfl⟩ : syracuseStep 1843371 = 2765057) B2765057
theorem B1843383 : Blo 1841622 1843383 := bstep (se 1 (by rfl) ⟨1382537, by rfl⟩ : syracuseStep 1843383 = 2765075) B2765075
theorem B4145345 : Blo 1841622 4145345 := bstep (se 2 (by rfl) ⟨1554504, by rfl⟩ : syracuseStep 4145345 = 3109009) B3109009
theorem B1843403 : Blo 1841622 1843403 := bstep (se 1 (by rfl) ⟨1382552, by rfl⟩ : syracuseStep 1843403 = 2765105) B2765105
theorem B1843415 : Blo 1841622 1843415 := bstep (se 1 (by rfl) ⟨1382561, by rfl⟩ : syracuseStep 1843415 = 2765123) B2765123
theorem B4980953 : Blo 1841622 4980953 := bstep (se 2 (by rfl) ⟨1867857, by rfl⟩ : syracuseStep 4980953 = 3735715) B3735715
theorem B1843435 : Blo 1841622 1843435 := bstep (se 1 (by rfl) ⟨1382576, by rfl⟩ : syracuseStep 1843435 = 2765153) B2765153
theorem B1843447 : Blo 1841622 1843447 := bstep (se 1 (by rfl) ⟨1382585, by rfl⟩ : syracuseStep 1843447 = 2765171) B2765171
theorem B17268997 : Blo 1841622 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B1843467 : Blo 1841622 1843467 := bstep (se 1 (by rfl) ⟨1382600, by rfl⟩ : syracuseStep 1843467 = 2765201) B2765201
theorem B15737105 : Blo 1841622 15737105 := bstep (se 2 (by rfl) ⟨5901414, by rfl⟩ : syracuseStep 15737105 = 11802829) B11802829
theorem B1843479 : Blo 1841622 1843479 := bstep (se 1 (by rfl) ⟨1382609, by rfl⟩ : syracuseStep 1843479 = 2765219) B2765219
theorem B2072875 : Blo 1841622 2072875 := bstep (se 1 (by rfl) ⟨1554656, by rfl⟩ : syracuseStep 2072875 = 3109313) B3109313
theorem B1843499 : Blo 1841622 1843499 := bstep (se 1 (by rfl) ⟨1382624, by rfl⟩ : syracuseStep 1843499 = 2765249) B2765249
theorem B1843511 : Blo 1841622 1843511 := bstep (se 1 (by rfl) ⟨1382633, by rfl⟩ : syracuseStep 1843511 = 2765267) B2765267
theorem B1843531 : Blo 1841622 1843531 := bstep (se 1 (by rfl) ⟨1382648, by rfl⟩ : syracuseStep 1843531 = 2765297) B2765297
theorem B1843543 : Blo 1841622 1843543 := bstep (se 1 (by rfl) ⟨1382657, by rfl⟩ : syracuseStep 1843543 = 2765315) B2765315
theorem B9331037 : Blo 1841622 9331037 := bstep (se 3 (by rfl) ⟨1749569, by rfl⟩ : syracuseStep 9331037 = 3499139) B3499139
theorem B1843563 : Blo 1841622 1843563 := bstep (se 1 (by rfl) ⟨1382672, by rfl⟩ : syracuseStep 1843563 = 2765345) B2765345
theorem B50446709 : Blo 1841622 50446709 := bstep (se 5 (by rfl) ⟨2364689, by rfl⟩ : syracuseStep 50446709 = 4729379) B4729379
theorem B1843575 : Blo 1841622 1843575 := bstep (se 1 (by rfl) ⟨1382681, by rfl⟩ : syracuseStep 1843575 = 2765363) B2765363
theorem B2490763 : Blo 1841622 2490763 := bstep (se 1 (by rfl) ⟨1868072, by rfl⟩ : syracuseStep 2490763 = 3736145) B3736145
theorem B1843595 : Blo 1841622 1843595 := bstep (se 1 (by rfl) ⟨1382696, by rfl⟩ : syracuseStep 1843595 = 2765393) B2765393
theorem B2072983 : Blo 1841622 2072983 := bstep (se 1 (by rfl) ⟨1554737, by rfl⟩ : syracuseStep 2072983 = 3109475) B3109475
theorem B7471511 : Blo 1841622 7471511 := bstep (se 1 (by rfl) ⟨5603633, by rfl⟩ : syracuseStep 7471511 = 11207267) B11207267
theorem B4145561 : Blo 1841622 4145561 := bstep (se 2 (by rfl) ⟨1554585, by rfl⟩ : syracuseStep 4145561 = 3109171) B3109171
theorem B1843607 : Blo 1841622 1843607 := bstep (se 1 (by rfl) ⟨1382705, by rfl⟩ : syracuseStep 1843607 = 2765411) B2765411
theorem B7094749 : Blo 1841622 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B4145651 : Blo 1841622 4145651 := bstep (se 1 (by rfl) ⟨3109238, by rfl⟩ : syracuseStep 4145651 = 6218477) B6218477
theorem B4661783 : Blo 1841622 4661783 := bstep (se 1 (by rfl) ⟨3496337, by rfl⟩ : syracuseStep 4661783 = 6992675) B6992675
theorem B4145687 : Blo 1841622 4145687 := bstep (se 1 (by rfl) ⟨3109265, by rfl⟩ : syracuseStep 4145687 = 6218531) B6218531
theorem B3498547 : Blo 1841622 3498547 := bstep (se 1 (by rfl) ⟨2623910, by rfl⟩ : syracuseStep 3498547 = 5247821) B5247821
theorem B6218315 : Blo 1841622 6218315 := bstep (se 1 (by rfl) ⟨4663736, by rfl⟩ : syracuseStep 6218315 = 9327473) B9327473
theorem B2073163 : Blo 1841622 2073163 := bstep (se 1 (by rfl) ⟨1554872, by rfl⟩ : syracuseStep 2073163 = 3109745) B3109745
theorem B2073271 : Blo 1841622 2073271 := bstep (se 1 (by rfl) ⟨1554953, by rfl⟩ : syracuseStep 2073271 = 3109907) B3109907
theorem B4145867 : Blo 1841622 4145867 := bstep (se 1 (by rfl) ⟨3109400, by rfl⟩ : syracuseStep 4145867 = 6218801) B6218801
theorem B17703629 : Blo 1841622 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B3736307 : Blo 1841622 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B4145921 : Blo 1841622 4145921 := bstep (se 2 (by rfl) ⟨1554720, by rfl⟩ : syracuseStep 4145921 = 3109441) B3109441
theorem B6218585 : Blo 1841622 6218585 := bstep (se 2 (by rfl) ⟨2331969, by rfl⟩ : syracuseStep 6218585 = 4663939) B4663939
theorem B16802653 : Blo 1841622 16802653 := bstep (se 3 (by rfl) ⟨3150497, by rfl⟩ : syracuseStep 16802653 = 6300995) B6300995
theorem B2073451 : Blo 1841622 2073451 := bstep (se 1 (by rfl) ⟨1555088, by rfl⟩ : syracuseStep 2073451 = 3110177) B3110177
theorem B6996881 : Blo 1841622 6996881 := bstep (se 2 (by rfl) ⟨2623830, by rfl⟩ : syracuseStep 6996881 = 5247661) B5247661
theorem B2073559 : Blo 1841622 2073559 := bstep (se 1 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 2073559 = 3110339) B3110339
theorem B4146137 : Blo 1841622 4146137 := bstep (se 2 (by rfl) ⟨1554801, by rfl⟩ : syracuseStep 4146137 = 3109603) B3109603
theorem B3499033 : Blo 1841622 3499033 := bstep (se 2 (by rfl) ⟨1312137, by rfl⟩ : syracuseStep 3499033 = 2624275) B2624275
theorem B4146227 : Blo 1841622 4146227 := bstep (se 1 (by rfl) ⟨3109670, by rfl⟩ : syracuseStep 4146227 = 6219341) B6219341
theorem B9323585 : Blo 1841622 9323585 := bstep (se 2 (by rfl) ⟨3496344, by rfl⟩ : syracuseStep 9323585 = 6992689) B6992689
theorem B4146263 : Blo 1841622 4146263 := bstep (se 1 (by rfl) ⟨3109697, by rfl⟩ : syracuseStep 4146263 = 6219395) B6219395
theorem B2073739 : Blo 1841622 2073739 := bstep (se 1 (by rfl) ⟨1555304, by rfl⟩ : syracuseStep 2073739 = 3110609) B3110609
theorem B1967275 : Blo 1841622 1967275 := bstep (se 1 (by rfl) ⟨1475456, by rfl⟩ : syracuseStep 1967275 = 2950913) B2950913
theorem B2073847 : Blo 1841622 2073847 := bstep (se 1 (by rfl) ⟨1555385, by rfl⟩ : syracuseStep 2073847 = 3110771) B3110771
theorem B4146443 : Blo 1841622 4146443 := bstep (se 1 (by rfl) ⟨3109832, by rfl⟩ : syracuseStep 4146443 = 6219665) B6219665
theorem B10495277 : Blo 1841622 10495277 := bstep (se 3 (by rfl) ⟨1967864, by rfl⟩ : syracuseStep 10495277 = 3935729) B3935729
theorem B3736883 : Blo 1841622 3736883 := bstep (se 1 (by rfl) ⟨2802662, by rfl⟩ : syracuseStep 3736883 = 5605325) B5605325
theorem B4662593 : Blo 1841622 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B4146497 : Blo 1841622 4146497 := bstep (se 2 (by rfl) ⟨1554936, by rfl⟩ : syracuseStep 4146497 = 3109873) B3109873
theorem B6997337 : Blo 1841622 6997337 := bstep (se 2 (by rfl) ⟨2624001, by rfl⟩ : syracuseStep 6997337 = 5248003) B5248003
theorem B2074027 : Blo 1841622 2074027 := bstep (se 1 (by rfl) ⟨1555520, by rfl⟩ : syracuseStep 2074027 = 3111041) B3111041
theorem B14943665 : Blo 1841622 14943665 := bstep (se 2 (by rfl) ⟨5603874, by rfl⟩ : syracuseStep 14943665 = 11207749) B11207749
theorem B4982219 : Blo 1841622 4982219 := bstep (se 1 (by rfl) ⟨3736664, by rfl⟩ : syracuseStep 4982219 = 7473329) B7473329
theorem B2622937 : Blo 1841622 2622937 := bstep (se 2 (by rfl) ⟨983601, by rfl⟩ : syracuseStep 2622937 = 1967203) B1967203
theorem B6219287 : Blo 1841622 6219287 := bstep (se 1 (by rfl) ⟨4664465, by rfl⟩ : syracuseStep 6219287 = 9328931) B9328931
theorem B4146713 : Blo 1841622 4146713 := bstep (se 2 (by rfl) ⟨1555017, by rfl⟩ : syracuseStep 4146713 = 3110035) B3110035
theorem B6997549 : Blo 1841622 6997549 := bstep (se 3 (by rfl) ⟨1312040, by rfl⟩ : syracuseStep 6997549 = 2624081) B2624081
theorem B4982347 : Blo 1841622 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B3499595 : Blo 1841622 3499595 := bstep (se 1 (by rfl) ⟨2624696, by rfl⟩ : syracuseStep 3499595 = 5249393) B5249393
theorem B7472729 : Blo 1841622 7472729 := bstep (se 2 (by rfl) ⟨2802273, by rfl⟩ : syracuseStep 7472729 = 5604547) B5604547
theorem B4146803 : Blo 1841622 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B4204147 : Blo 1841622 4204147 := bstep (se 1 (by rfl) ⟨3153110, by rfl⟩ : syracuseStep 4204147 = 6306221) B6306221
theorem B4146839 : Blo 1841622 4146839 := bstep (se 1 (by rfl) ⟨3110129, by rfl⟩ : syracuseStep 4146839 = 6220259) B6220259
theorem B6301405 : Blo 1841622 6301405 := bstep (se 3 (by rfl) ⟨1181513, by rfl⟩ : syracuseStep 6301405 = 2363027) B2363027
theorem B3499777 : Blo 1841622 3499777 := bstep (se 2 (by rfl) ⟨1312416, by rfl⟩ : syracuseStep 3499777 = 2624833) B2624833
theorem B2762507 : Blo 1841622 2762507 := bstep (se 1 (by rfl) ⟨2071880, by rfl⟩ : syracuseStep 2762507 = 4143761) B4143761
theorem B2762519 : Blo 1841622 2762519 := bstep (se 1 (by rfl) ⟨2071889, by rfl⟩ : syracuseStep 2762519 = 4143779) B4143779
theorem B3934003 : Blo 1841622 3934003 := bstep (se 1 (by rfl) ⟨2950502, by rfl⟩ : syracuseStep 3934003 = 5901005) B5901005
theorem B4147019 : Blo 1841622 4147019 := bstep (se 1 (by rfl) ⟨3110264, by rfl⟩ : syracuseStep 4147019 = 6220529) B6220529
theorem B2762585 : Blo 1841622 2762585 := bstep (se 2 (by rfl) ⟨1035969, by rfl⟩ : syracuseStep 2762585 = 2071939) B2071939
theorem B4663129 : Blo 1841622 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B6997853 : Blo 1841622 6997853 := bstep (se 3 (by rfl) ⟨1312097, by rfl⟩ : syracuseStep 6997853 = 2624195) B2624195
theorem B4147073 : Blo 1841622 4147073 := bstep (se 2 (by rfl) ⟨1555152, by rfl⟩ : syracuseStep 4147073 = 3110305) B3110305
theorem B1968023 : Blo 1841622 1968023 := bstep (se 1 (by rfl) ⟨1476017, by rfl⟩ : syracuseStep 1968023 = 2952035) B2952035
theorem B2762699 : Blo 1841622 2762699 := bstep (se 1 (by rfl) ⟨2072024, by rfl⟩ : syracuseStep 2762699 = 4144049) B4144049
theorem B2762711 : Blo 1841622 2762711 := bstep (se 1 (by rfl) ⟨2072033, by rfl⟩ : syracuseStep 2762711 = 4144067) B4144067
theorem B13281241 : Blo 1841622 13281241 := bstep (se 2 (by rfl) ⟨4980465, by rfl⟩ : syracuseStep 13281241 = 9960931) B9960931
theorem B2762777 : Blo 1841622 2762777 := bstep (se 2 (by rfl) ⟨1036041, by rfl⟩ : syracuseStep 2762777 = 2072083) B2072083
theorem B5900339 : Blo 1841622 5900339 := bstep (se 1 (by rfl) ⟨4425254, by rfl⟩ : syracuseStep 5900339 = 8850509) B8850509
theorem B6219827 : Blo 1841622 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B4147289 : Blo 1841622 4147289 := bstep (se 2 (by rfl) ⟨1555233, by rfl⟩ : syracuseStep 4147289 = 3110467) B3110467
theorem B2762891 : Blo 1841622 2762891 := bstep (se 1 (by rfl) ⟨2072168, by rfl⟩ : syracuseStep 2762891 = 4144337) B4144337
theorem B2762903 : Blo 1841622 2762903 := bstep (se 1 (by rfl) ⟨2072177, by rfl⟩ : syracuseStep 2762903 = 4144355) B4144355
theorem B4147379 : Blo 1841622 4147379 := bstep (se 1 (by rfl) ⟨3110534, by rfl⟩ : syracuseStep 4147379 = 6221069) B6221069
theorem B7866571 : Blo 1841622 7866571 := bstep (se 1 (by rfl) ⟨5899928, by rfl⟩ : syracuseStep 7866571 = 11799857) B11799857
theorem B4147415 : Blo 1841622 4147415 := bstep (se 1 (by rfl) ⟨3110561, by rfl⟩ : syracuseStep 4147415 = 6221123) B6221123
theorem B5245145 : Blo 1841622 5245145 := bstep (se 2 (by rfl) ⟨1966929, by rfl⟩ : syracuseStep 5245145 = 3933859) B3933859
theorem B2762969 : Blo 1841622 2762969 := bstep (se 2 (by rfl) ⟨1036113, by rfl⟩ : syracuseStep 2762969 = 2072227) B2072227
theorem B6220097 : Blo 1841622 6220097 := bstep (se 2 (by rfl) ⟨2332536, by rfl⟩ : syracuseStep 6220097 = 4665073) B4665073
theorem B2763083 : Blo 1841622 2763083 := bstep (se 1 (by rfl) ⟨2072312, by rfl⟩ : syracuseStep 2763083 = 4144625) B4144625
theorem B2763095 : Blo 1841622 2763095 := bstep (se 1 (by rfl) ⟨2072321, by rfl⟩ : syracuseStep 2763095 = 4144643) B4144643
theorem B4147595 : Blo 1841622 4147595 := bstep (se 1 (by rfl) ⟨3110696, by rfl⟩ : syracuseStep 4147595 = 6221393) B6221393
theorem B9333143 : Blo 1841622 9333143 := bstep (se 1 (by rfl) ⟨6999857, by rfl⟩ : syracuseStep 9333143 = 13999715) B13999715
theorem B2763161 : Blo 1841622 2763161 := bstep (se 2 (by rfl) ⟨1036185, by rfl⟩ : syracuseStep 2763161 = 2072371) B2072371
theorem B4426177 : Blo 1841622 4426177 := bstep (se 2 (by rfl) ⟨1659816, by rfl⟩ : syracuseStep 4426177 = 3319633) B3319633
theorem B4147649 : Blo 1841622 4147649 := bstep (se 2 (by rfl) ⟨1555368, by rfl⟩ : syracuseStep 4147649 = 3110737) B3110737
theorem B6638041 : Blo 1841622 6638041 := bstep (se 2 (by rfl) ⟨2489265, by rfl⟩ : syracuseStep 6638041 = 4978531) B4978531
theorem B7866845 : Blo 1841622 7866845 := bstep (se 3 (by rfl) ⟨1475033, by rfl⟩ : syracuseStep 7866845 = 2950067) B2950067
theorem B2763275 : Blo 1841622 2763275 := bstep (se 1 (by rfl) ⟨2072456, by rfl⟩ : syracuseStep 2763275 = 4144913) B4144913
theorem B2763287 : Blo 1841622 2763287 := bstep (se 1 (by rfl) ⟨2072465, by rfl⟩ : syracuseStep 2763287 = 4144931) B4144931
theorem B2763353 : Blo 1841622 2763353 := bstep (se 2 (by rfl) ⟨1036257, by rfl⟩ : syracuseStep 2763353 = 2072515) B2072515
theorem B4983385 : Blo 1841622 4983385 := bstep (se 2 (by rfl) ⟨1868769, by rfl⟩ : syracuseStep 4983385 = 3737539) B3737539
theorem B7473815 : Blo 1841622 7473815 := bstep (se 1 (by rfl) ⟨5605361, by rfl⟩ : syracuseStep 7473815 = 11210723) B11210723
theorem B4147865 : Blo 1841622 4147865 := bstep (se 2 (by rfl) ⟨1555449, by rfl⟩ : syracuseStep 4147865 = 3110899) B3110899
theorem B2763467 : Blo 1841622 2763467 := bstep (se 1 (by rfl) ⟨2072600, by rfl⟩ : syracuseStep 2763467 = 4145201) B4145201
theorem B47860429 : Blo 1841622 47860429 := bstep (se 3 (by rfl) ⟨8973830, by rfl⟩ : syracuseStep 47860429 = 17947661) B17947661
theorem B2763479 : Blo 1841622 2763479 := bstep (se 1 (by rfl) ⟨2072609, by rfl⟩ : syracuseStep 2763479 = 4145219) B4145219
theorem B4147955 : Blo 1841622 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B4147991 : Blo 1841622 4147991 := bstep (se 1 (by rfl) ⟨3110993, by rfl⟩ : syracuseStep 4147991 = 6221987) B6221987
theorem B2763545 : Blo 1841622 2763545 := bstep (se 2 (by rfl) ⟨1036329, by rfl⟩ : syracuseStep 2763545 = 2072659) B2072659
theorem B3935063 : Blo 1841622 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B6220637 : Blo 1841622 6220637 := bstep (se 3 (by rfl) ⟨1166369, by rfl⟩ : syracuseStep 6220637 = 2332739) B2332739
theorem B2763659 : Blo 1841622 2763659 := bstep (se 1 (by rfl) ⟨2072744, by rfl⟩ : syracuseStep 2763659 = 4145489) B4145489
theorem B2624395 : Blo 1841622 2624395 := bstep (se 1 (by rfl) ⟨1968296, by rfl⟩ : syracuseStep 2624395 = 3936593) B3936593
theorem B2763671 : Blo 1841622 2763671 := bstep (se 1 (by rfl) ⟨2072753, by rfl⟩ : syracuseStep 2763671 = 4145507) B4145507
theorem B4664243 : Blo 1841622 4664243 := bstep (se 1 (by rfl) ⟨3498182, by rfl⟩ : syracuseStep 4664243 = 6996365) B6996365
theorem B3107801 : Blo 1841622 3107801 := bstep (se 2 (by rfl) ⟨1165425, by rfl⟩ : syracuseStep 3107801 = 2330851) B2330851
theorem B9325529 : Blo 1841622 9325529 := bstep (se 2 (by rfl) ⟨3497073, by rfl⟩ : syracuseStep 9325529 = 6994147) B6994147
theorem B21269465 : Blo 1841622 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B2763737 : Blo 1841622 2763737 := bstep (se 2 (by rfl) ⟨1036401, by rfl⟩ : syracuseStep 2763737 = 2072803) B2072803
theorem B67251161 : Blo 1841622 67251161 := bstep (se 2 (by rfl) ⟨25219185, by rfl⟩ : syracuseStep 67251161 = 50438371) B50438371
theorem B3935233 : Blo 1841622 3935233 := bstep (se 2 (by rfl) ⟨1475712, by rfl⟩ : syracuseStep 3935233 = 2951425) B2951425
theorem B5245975 : Blo 1841622 5245975 := bstep (se 1 (by rfl) ⟨3934481, by rfl⟩ : syracuseStep 5245975 = 7868963) B7868963
theorem B2763851 : Blo 1841622 2763851 := bstep (se 1 (by rfl) ⟨2072888, by rfl⟩ : syracuseStep 2763851 = 4145777) B4145777
theorem B2763863 : Blo 1841622 2763863 := bstep (se 1 (by rfl) ⟨2072897, by rfl⟩ : syracuseStep 2763863 = 4145795) B4145795
theorem B3107929 : Blo 1841622 3107929 := bstep (se 2 (by rfl) ⟨1165473, by rfl⟩ : syracuseStep 3107929 = 2330947) B2330947
theorem B8858717 : Blo 1841622 8858717 := bstep (se 3 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 8858717 = 3322019) B3322019
theorem B2763929 : Blo 1841622 2763929 := bstep (se 2 (by rfl) ⟨1036473, by rfl⟩ : syracuseStep 2763929 = 2072947) B2072947
theorem B15740081 : Blo 1841622 15740081 := bstep (se 2 (by rfl) ⟨5902530, by rfl⟩ : syracuseStep 15740081 = 11805061) B11805061
theorem B4664537 : Blo 1841622 4664537 := bstep (se 2 (by rfl) ⟨1749201, by rfl⟩ : syracuseStep 4664537 = 3498403) B3498403
theorem B2764043 : Blo 1841622 2764043 := bstep (se 1 (by rfl) ⟨2073032, by rfl⟩ : syracuseStep 2764043 = 4146065) B4146065
theorem B2764055 : Blo 1841622 2764055 := bstep (se 1 (by rfl) ⟨2073041, by rfl⟩ : syracuseStep 2764055 = 4146083) B4146083
theorem B3935575 : Blo 1841622 3935575 := bstep (se 1 (by rfl) ⟨2951681, by rfl⟩ : syracuseStep 3935575 = 5903363) B5903363
theorem B2764121 : Blo 1841622 2764121 := bstep (se 2 (by rfl) ⟨1036545, by rfl⟩ : syracuseStep 2764121 = 2073091) B2073091
theorem B2764235 : Blo 1841622 2764235 := bstep (se 1 (by rfl) ⟨2073176, by rfl⟩ : syracuseStep 2764235 = 4146353) B4146353
theorem B2764247 : Blo 1841622 2764247 := bstep (se 1 (by rfl) ⟨2073185, by rfl⟩ : syracuseStep 2764247 = 4146371) B4146371
theorem B28749325 : Blo 1841622 28749325 := bstep (se 3 (by rfl) ⟨5390498, by rfl⟩ : syracuseStep 28749325 = 10780997) B10780997
theorem B2764313 : Blo 1841622 2764313 := bstep (se 2 (by rfl) ⟨1036617, by rfl⟩ : syracuseStep 2764313 = 2073235) B2073235
theorem B50409053 : Blo 1841622 50409053 := bstep (se 3 (by rfl) ⟨9451697, by rfl⟩ : syracuseStep 50409053 = 18903395) B18903395
theorem B13274725 : Blo 1841622 13274725 := bstep (se 4 (by rfl) ⟨1244505, by rfl⟩ : syracuseStep 13274725 = 2489011) B2489011
theorem B10489445 : Blo 1841622 10489445 := bstep (se 4 (by rfl) ⟨983385, by rfl⟩ : syracuseStep 10489445 = 1966771) B1966771
theorem B2764427 : Blo 1841622 2764427 := bstep (se 1 (by rfl) ⟨2073320, by rfl⟩ : syracuseStep 2764427 = 4146641) B4146641
theorem B26554007 : Blo 1841622 26554007 := bstep (se 1 (by rfl) ⟨19915505, by rfl⟩ : syracuseStep 26554007 = 39831011) B39831011
theorem B3108503 : Blo 1841622 3108503 := bstep (se 1 (by rfl) ⟨2331377, by rfl⟩ : syracuseStep 3108503 = 4662755) B4662755
theorem B2764439 : Blo 1841622 2764439 := bstep (se 1 (by rfl) ⟨2073329, by rfl⟩ : syracuseStep 2764439 = 4146659) B4146659
theorem B8400557 : Blo 1841622 8400557 := bstep (se 3 (by rfl) ⟨1575104, by rfl⟩ : syracuseStep 8400557 = 3150209) B3150209
theorem B8851123 : Blo 1841622 8851123 := bstep (se 1 (by rfl) ⟨6638342, by rfl⟩ : syracuseStep 8851123 = 13276685) B13276685
theorem B2764505 : Blo 1841622 2764505 := bstep (se 2 (by rfl) ⟨1036689, by rfl⟩ : syracuseStep 2764505 = 2073379) B2073379
theorem B3108631 : Blo 1841622 3108631 := bstep (se 1 (by rfl) ⟨2331473, by rfl⟩ : syracuseStep 3108631 = 4662947) B4662947
theorem B3321623 : Blo 1841622 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B6639425 : Blo 1841622 6639425 := bstep (se 2 (by rfl) ⟨2489784, by rfl⟩ : syracuseStep 6639425 = 4979569) B4979569
theorem B5246795 : Blo 1841622 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B2764619 : Blo 1841622 2764619 := bstep (se 1 (by rfl) ⟨2073464, by rfl⟩ : syracuseStep 2764619 = 4146929) B4146929
theorem B2764631 : Blo 1841622 2764631 := bstep (se 1 (by rfl) ⟨2073473, by rfl⟩ : syracuseStep 2764631 = 4146947) B4146947
theorem B2953111 : Blo 1841622 2953111 := bstep (se 1 (by rfl) ⟨2214833, by rfl⟩ : syracuseStep 2953111 = 4429667) B4429667
theorem B2764697 : Blo 1841622 2764697 := bstep (se 2 (by rfl) ⟨1036761, by rfl⟩ : syracuseStep 2764697 = 2073523) B2073523
theorem B6221771 : Blo 1841622 6221771 := bstep (se 1 (by rfl) ⟨4666328, by rfl⟩ : syracuseStep 6221771 = 9332657) B9332657
theorem B11972569 : Blo 1841622 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B2764811 : Blo 1841622 2764811 := bstep (se 1 (by rfl) ⟨2073608, by rfl⟩ : syracuseStep 2764811 = 4147217) B4147217
theorem B2764823 : Blo 1841622 2764823 := bstep (se 1 (by rfl) ⟨2073617, by rfl⟩ : syracuseStep 2764823 = 4147235) B4147235
theorem B2764889 : Blo 1841622 2764889 := bstep (se 2 (by rfl) ⟨1036833, by rfl⟩ : syracuseStep 2764889 = 2073667) B2073667
theorem B5902429 : Blo 1841622 5902429 := bstep (se 3 (by rfl) ⟨1106705, by rfl⟩ : syracuseStep 5902429 = 2213411) B2213411
theorem B3936395 : Blo 1841622 3936395 := bstep (se 1 (by rfl) ⟨2952296, by rfl⟩ : syracuseStep 3936395 = 5904593) B5904593
theorem B2765003 : Blo 1841622 2765003 := bstep (se 1 (by rfl) ⟨2073752, by rfl⟩ : syracuseStep 2765003 = 4147505) B4147505
theorem B2765015 : Blo 1841622 2765015 := bstep (se 1 (by rfl) ⟨2073761, by rfl⟩ : syracuseStep 2765015 = 4147523) B4147523
theorem B6222041 : Blo 1841622 6222041 := bstep (se 2 (by rfl) ⟨2333265, by rfl⟩ : syracuseStep 6222041 = 4666531) B4666531
theorem B2765081 : Blo 1841622 2765081 := bstep (se 2 (by rfl) ⟨1036905, by rfl⟩ : syracuseStep 2765081 = 2073811) B2073811
theorem B15143213 : Blo 1841622 15143213 := bstep (se 3 (by rfl) ⟨2839352, by rfl⟩ : syracuseStep 15143213 = 5678705) B5678705
theorem B19927397 : Blo 1841622 19927397 := bstep (se 4 (by rfl) ⟨1868193, by rfl⟩ : syracuseStep 19927397 = 3736387) B3736387
theorem B15749477 : Blo 1841622 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B3109259 : Blo 1841622 3109259 := bstep (se 1 (by rfl) ⟨2331944, by rfl⟩ : syracuseStep 3109259 = 4663889) B4663889
theorem B2765195 : Blo 1841622 2765195 := bstep (se 1 (by rfl) ⟨2073896, by rfl⟩ : syracuseStep 2765195 = 4147793) B4147793
theorem B2765207 : Blo 1841622 2765207 := bstep (se 1 (by rfl) ⟨2073905, by rfl⟩ : syracuseStep 2765207 = 4147811) B4147811
theorem B2765273 : Blo 1841622 2765273 := bstep (se 2 (by rfl) ⟨1036977, by rfl⟩ : syracuseStep 2765273 = 2073955) B2073955
theorem B3936755 : Blo 1841622 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B3109387 : Blo 1841622 3109387 := bstep (se 1 (by rfl) ⟨2332040, by rfl⟩ : syracuseStep 3109387 = 4664081) B4664081
theorem B29880845 : Blo 1841622 29880845 := bstep (se 3 (by rfl) ⟨5602658, by rfl⟩ : syracuseStep 29880845 = 11205317) B11205317
theorem B9327149 : Blo 1841622 9327149 := bstep (se 3 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 9327149 = 3497681) B3497681
theorem B2765387 : Blo 1841622 2765387 := bstep (se 1 (by rfl) ⟨2074040, by rfl⟩ : syracuseStep 2765387 = 4148081) B4148081
theorem B2765399 : Blo 1841622 2765399 := bstep (se 1 (by rfl) ⟨2074049, by rfl⟩ : syracuseStep 2765399 = 4148099) B4148099
theorem B7574105 : Blo 1841622 7574105 := bstep (se 2 (by rfl) ⟨2840289, by rfl⟩ : syracuseStep 7574105 = 5680579) B5680579
theorem B6992477 : Blo 1841622 6992477 := bstep (se 3 (by rfl) ⟨1311089, by rfl⟩ : syracuseStep 6992477 = 2622179) B2622179
theorem B18199133 : Blo 1841622 18199133 := bstep (se 3 (by rfl) ⟨3412337, by rfl⟩ : syracuseStep 18199133 = 6824675) B6824675
theorem B11801189 : Blo 1841622 11801189 := bstep (se 4 (by rfl) ⟨1106361, by rfl⟩ : syracuseStep 11801189 = 2212723) B2212723
theorem B3109529 : Blo 1841622 3109529 := bstep (se 2 (by rfl) ⟨1166073, by rfl⟩ : syracuseStep 3109529 = 2332147) B2332147
theorem B3109657 : Blo 1841622 3109657 := bstep (se 2 (by rfl) ⟨1166121, by rfl⟩ : syracuseStep 3109657 = 2332243) B2332243
theorem B4666187 : Blo 1841622 4666187 := bstep (se 1 (by rfl) ⟨3499640, by rfl⟩ : syracuseStep 4666187 = 6999281) B6999281
theorem B10498967 : Blo 1841622 10498967 := bstep (se 1 (by rfl) ⟨7874225, by rfl⟩ : syracuseStep 10498967 = 15748451) B15748451
theorem B2331595 : Blo 1841622 2331595 := bstep (se 1 (by rfl) ⟨1748696, by rfl⟩ : syracuseStep 2331595 = 3497393) B3497393
theorem B2159563 : Blo 1841622 2159563 := bstep (se 1 (by rfl) ⟨1619672, by rfl⟩ : syracuseStep 2159563 = 3239345) B3239345
theorem B12948659 : Blo 1841622 12948659 := bstep (se 1 (by rfl) ⟨9711494, by rfl⟩ : syracuseStep 12948659 = 19422989) B19422989
theorem B6993175 : Blo 1841622 6993175 := bstep (se 1 (by rfl) ⟨5244881, by rfl⟩ : syracuseStep 6993175 = 10489763) B10489763
theorem B3110231 : Blo 1841622 3110231 := bstep (se 1 (by rfl) ⟨2332673, by rfl⟩ : syracuseStep 3110231 = 4665347) B4665347
theorem B7091545 : Blo 1841622 7091545 := bstep (se 2 (by rfl) ⟨2659329, by rfl⟩ : syracuseStep 7091545 = 5318659) B5318659
theorem B4486603 : Blo 1841622 4486603 := bstep (se 1 (by rfl) ⟨3364952, by rfl⟩ : syracuseStep 4486603 = 6729905) B6729905
theorem B3110359 : Blo 1841622 3110359 := bstep (se 1 (by rfl) ⟨2332769, by rfl⟩ : syracuseStep 3110359 = 4665539) B4665539
theorem B6387265 : Blo 1841622 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B12777035 : Blo 1841622 12777035 := bstep (se 1 (by rfl) ⟨9582776, by rfl⟩ : syracuseStep 12777035 = 19165553) B19165553
theorem B22410827 : Blo 1841622 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B20993741 : Blo 1841622 20993741 := bstep (se 3 (by rfl) ⟨3936326, by rfl⟩ : syracuseStep 20993741 = 7872653) B7872653
theorem B14940035 : Blo 1841622 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B2332567 : Blo 1841622 2332567 := bstep (se 1 (by rfl) ⟨1749425, by rfl⟩ : syracuseStep 2332567 = 3498851) B3498851
theorem B6731723 : Blo 1841622 6731723 := bstep (se 1 (by rfl) ⟨5048792, by rfl⟩ : syracuseStep 6731723 = 10097585) B10097585
theorem B6993965 : Blo 1841622 6993965 := bstep (se 3 (by rfl) ⟨1311368, by rfl⟩ : syracuseStep 6993965 = 2622737) B2622737
theorem B3110987 : Blo 1841622 3110987 := bstep (se 1 (by rfl) ⟨2333240, by rfl⟩ : syracuseStep 3110987 = 4666481) B4666481
theorem B3151961 : Blo 1841622 3151961 := bstep (se 2 (by rfl) ⟨1181985, by rfl⟩ : syracuseStep 3151961 = 2363971) B2363971
theorem B6215831 : Blo 1841622 6215831 := bstep (se 1 (by rfl) ⟨4661873, by rfl⟩ : syracuseStep 6215831 = 9323747) B9323747
theorem B13998257 : Blo 1841622 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B5249245 : Blo 1841622 5249245 := bstep (se 3 (by rfl) ⟨984233, by rfl⟩ : syracuseStep 5249245 = 1968467) B1968467
theorem B6306113 : Blo 1841622 6306113 := bstep (se 2 (by rfl) ⟨2364792, by rfl⟩ : syracuseStep 6306113 = 4729585) B4729585
theorem B9959831 : Blo 1841622 9959831 := bstep (se 1 (by rfl) ⟨7469873, by rfl⟩ : syracuseStep 9959831 = 14939747) B14939747
theorem B5757335 : Blo 1841622 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B1841623 : Blo 1841622 1841623 := bstep (se 1 (by rfl) ⟨1381217, by rfl⟩ : syracuseStep 1841623 = 2762435) B2762435
theorem B1841643 : Blo 1841622 1841643 := bstep (se 1 (by rfl) ⟨1381232, by rfl⟩ : syracuseStep 1841643 = 2762465) B2762465
theorem B1841655 : Blo 1841622 1841655 := bstep (se 1 (by rfl) ⟨1381241, by rfl⟩ : syracuseStep 1841655 = 2762483) B2762483
theorem B1841675 : Blo 1841622 1841675 := bstep (se 1 (by rfl) ⟨1381256, by rfl⟩ : syracuseStep 1841675 = 2762513) B2762513
theorem B3496459 : Blo 1841622 3496459 := bstep (se 1 (by rfl) ⟨2622344, by rfl⟩ : syracuseStep 3496459 = 5244689) B5244689
theorem B17717777 : Blo 1841622 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B1841687 : Blo 1841622 1841687 := bstep (se 1 (by rfl) ⟨1381265, by rfl⟩ : syracuseStep 1841687 = 2762531) B2762531
theorem B1841707 : Blo 1841622 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B1841719 : Blo 1841622 1841719 := bstep (se 1 (by rfl) ⟨1381289, by rfl⟩ : syracuseStep 1841719 = 2762579) B2762579
theorem B1841739 : Blo 1841622 1841739 := bstep (se 1 (by rfl) ⟨1381304, by rfl⟩ : syracuseStep 1841739 = 2762609) B2762609
theorem B1841751 : Blo 1841622 1841751 := bstep (se 1 (by rfl) ⟨1381313, by rfl⟩ : syracuseStep 1841751 = 2762627) B2762627
theorem B1841771 : Blo 1841622 1841771 := bstep (se 1 (by rfl) ⟨1381328, by rfl⟩ : syracuseStep 1841771 = 2762657) B2762657
theorem B1841783 : Blo 1841622 1841783 := bstep (se 1 (by rfl) ⟨1381337, by rfl⟩ : syracuseStep 1841783 = 2762675) B2762675
theorem B1841803 : Blo 1841622 1841803 := bstep (se 1 (by rfl) ⟨1381352, by rfl⟩ : syracuseStep 1841803 = 2762705) B2762705
theorem B1841815 : Blo 1841622 1841815 := bstep (se 1 (by rfl) ⟨1381361, by rfl⟩ : syracuseStep 1841815 = 2762723) B2762723
theorem B13998743 : Blo 1841622 13998743 := bstep (se 1 (by rfl) ⟨10499057, by rfl⟩ : syracuseStep 13998743 = 20998115) B20998115
theorem B1841835 : Blo 1841622 1841835 := bstep (se 1 (by rfl) ⟨1381376, by rfl⟩ : syracuseStep 1841835 = 2762753) B2762753
theorem B6216371 : Blo 1841622 6216371 := bstep (se 1 (by rfl) ⟨4662278, by rfl⟩ : syracuseStep 6216371 = 9324557) B9324557
theorem B1841847 : Blo 1841622 1841847 := bstep (se 1 (by rfl) ⟨1381385, by rfl⟩ : syracuseStep 1841847 = 2762771) B2762771
theorem B1841867 : Blo 1841622 1841867 := bstep (se 1 (by rfl) ⟨1381400, by rfl⟩ : syracuseStep 1841867 = 2762801) B2762801
theorem B1841879 : Blo 1841622 1841879 := bstep (se 1 (by rfl) ⟨1381409, by rfl⟩ : syracuseStep 1841879 = 2762819) B2762819
theorem B4143833 : Blo 1841622 4143833 := bstep (se 2 (by rfl) ⟨1553937, by rfl⟩ : syracuseStep 4143833 = 3107875) B3107875
theorem B1841899 : Blo 1841622 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B1841911 : Blo 1841622 1841911 := bstep (se 1 (by rfl) ⟨1381433, by rfl⟩ : syracuseStep 1841911 = 2762867) B2762867
theorem B1841931 : Blo 1841622 1841931 := bstep (se 1 (by rfl) ⟨1381448, by rfl⟩ : syracuseStep 1841931 = 2762897) B2762897
theorem B1841943 : Blo 1841622 1841943 := bstep (se 1 (by rfl) ⟨1381457, by rfl⟩ : syracuseStep 1841943 = 2762915) B2762915
theorem B1841963 : Blo 1841622 1841963 := bstep (se 1 (by rfl) ⟨1381472, by rfl⟩ : syracuseStep 1841963 = 2762945) B2762945
theorem B4143923 : Blo 1841622 4143923 := bstep (se 1 (by rfl) ⟨3107942, by rfl⟩ : syracuseStep 4143923 = 6215885) B6215885
theorem B1841975 : Blo 1841622 1841975 := bstep (se 1 (by rfl) ⟨1381481, by rfl⟩ : syracuseStep 1841975 = 2762963) B2762963
theorem B1841995 : Blo 1841622 1841995 := bstep (se 1 (by rfl) ⟨1381496, by rfl⟩ : syracuseStep 1841995 = 2762993) B2762993
theorem B4143959 : Blo 1841622 4143959 := bstep (se 1 (by rfl) ⟨3107969, by rfl⟩ : syracuseStep 4143959 = 6215939) B6215939
theorem B1842007 : Blo 1841622 1842007 := bstep (se 1 (by rfl) ⟨1381505, by rfl⟩ : syracuseStep 1842007 = 2763011) B2763011
theorem B26573669 : Blo 1841622 26573669 := bstep (se 4 (by rfl) ⟨2491281, by rfl⟩ : syracuseStep 26573669 = 4982563) B4982563
theorem B1842027 : Blo 1841622 1842027 := bstep (se 1 (by rfl) ⟨1381520, by rfl⟩ : syracuseStep 1842027 = 2763041) B2763041
theorem B1842039 : Blo 1841622 1842039 := bstep (se 1 (by rfl) ⟨1381529, by rfl⟩ : syracuseStep 1842039 = 2763059) B2763059
theorem B1842059 : Blo 1841622 1842059 := bstep (se 1 (by rfl) ⟨1381544, by rfl⟩ : syracuseStep 1842059 = 2763089) B2763089
theorem B1842071 : Blo 1841622 1842071 := bstep (se 1 (by rfl) ⟨1381553, by rfl⟩ : syracuseStep 1842071 = 2763107) B2763107
theorem B1842091 : Blo 1841622 1842091 := bstep (se 1 (by rfl) ⟨1381568, by rfl⟩ : syracuseStep 1842091 = 2763137) B2763137
theorem B1842103 : Blo 1841622 1842103 := bstep (se 1 (by rfl) ⟨1381577, by rfl⟩ : syracuseStep 1842103 = 2763155) B2763155
theorem B6216641 : Blo 1841622 6216641 := bstep (se 2 (by rfl) ⟨2331240, by rfl⟩ : syracuseStep 6216641 = 4662481) B4662481
theorem B3496907 : Blo 1841622 3496907 := bstep (se 1 (by rfl) ⟨2622680, by rfl⟩ : syracuseStep 3496907 = 5245361) B5245361
theorem B1842123 : Blo 1841622 1842123 := bstep (se 1 (by rfl) ⟨1381592, by rfl⟩ : syracuseStep 1842123 = 2763185) B2763185
theorem B1842135 : Blo 1841622 1842135 := bstep (se 1 (by rfl) ⟨1381601, by rfl⟩ : syracuseStep 1842135 = 2763203) B2763203
theorem B1842155 : Blo 1841622 1842155 := bstep (se 1 (by rfl) ⟨1381616, by rfl⟩ : syracuseStep 1842155 = 2763233) B2763233
theorem B1842167 : Blo 1841622 1842167 := bstep (se 1 (by rfl) ⟨1381625, by rfl⟩ : syracuseStep 1842167 = 2763251) B2763251
theorem B4144139 : Blo 1841622 4144139 := bstep (se 1 (by rfl) ⟨3108104, by rfl⟩ : syracuseStep 4144139 = 6216209) B6216209
theorem B1842187 : Blo 1841622 1842187 := bstep (se 1 (by rfl) ⟨1381640, by rfl⟩ : syracuseStep 1842187 = 2763281) B2763281
theorem B1842199 : Blo 1841622 1842199 := bstep (se 1 (by rfl) ⟨1381649, by rfl⟩ : syracuseStep 1842199 = 2763299) B2763299
theorem B1842219 : Blo 1841622 1842219 := bstep (se 1 (by rfl) ⟨1381664, by rfl⟩ : syracuseStep 1842219 = 2763329) B2763329
theorem B1842231 : Blo 1841622 1842231 := bstep (se 1 (by rfl) ⟨1381673, by rfl⟩ : syracuseStep 1842231 = 2763347) B2763347
theorem B4144193 : Blo 1841622 4144193 := bstep (se 2 (by rfl) ⟨1554072, by rfl⟩ : syracuseStep 4144193 = 3108145) B3108145
theorem B11811905 : Blo 1841622 11811905 := bstep (se 2 (by rfl) ⟨4429464, by rfl⟩ : syracuseStep 11811905 = 8858929) B8858929
theorem B1842251 : Blo 1841622 1842251 := bstep (se 1 (by rfl) ⟨1381688, by rfl⟩ : syracuseStep 1842251 = 2763377) B2763377
theorem B1842263 : Blo 1841622 1842263 := bstep (se 1 (by rfl) ⟨1381697, by rfl⟩ : syracuseStep 1842263 = 2763395) B2763395
theorem B1842283 : Blo 1841622 1842283 := bstep (se 1 (by rfl) ⟨1381712, by rfl⟩ : syracuseStep 1842283 = 2763425) B2763425
theorem B1842295 : Blo 1841622 1842295 := bstep (se 1 (by rfl) ⟨1381721, by rfl⟩ : syracuseStep 1842295 = 2763443) B2763443
theorem B3497089 : Blo 1841622 3497089 := bstep (se 2 (by rfl) ⟨1311408, by rfl⟩ : syracuseStep 3497089 = 2622817) B2622817
theorem B1842315 : Blo 1841622 1842315 := bstep (se 1 (by rfl) ⟨1381736, by rfl⟩ : syracuseStep 1842315 = 2763473) B2763473
theorem B1842327 : Blo 1841622 1842327 := bstep (se 1 (by rfl) ⟨1381745, by rfl⟩ : syracuseStep 1842327 = 2763491) B2763491
theorem B1842347 : Blo 1841622 1842347 := bstep (se 1 (by rfl) ⟨1381760, by rfl⟩ : syracuseStep 1842347 = 2763521) B2763521
theorem B1842359 : Blo 1841622 1842359 := bstep (se 1 (by rfl) ⟨1381769, by rfl⟩ : syracuseStep 1842359 = 2763539) B2763539
theorem B7871681 : Blo 1841622 7871681 := bstep (se 2 (by rfl) ⟨2951880, by rfl⟩ : syracuseStep 7871681 = 5903761) B5903761
theorem B1842379 : Blo 1841622 1842379 := bstep (se 1 (by rfl) ⟨1381784, by rfl⟩ : syracuseStep 1842379 = 2763569) B2763569
theorem B1842391 : Blo 1841622 1842391 := bstep (se 1 (by rfl) ⟨1381793, by rfl⟩ : syracuseStep 1842391 = 2763587) B2763587
theorem B1842411 : Blo 1841622 1842411 := bstep (se 1 (by rfl) ⟨1381808, by rfl⟩ : syracuseStep 1842411 = 2763617) B2763617
theorem B1842423 : Blo 1841622 1842423 := bstep (se 1 (by rfl) ⟨1381817, by rfl⟩ : syracuseStep 1842423 = 2763635) B2763635
theorem B1842443 : Blo 1841622 1842443 := bstep (se 1 (by rfl) ⟨1381832, by rfl⟩ : syracuseStep 1842443 = 2763665) B2763665
theorem B2071831 : Blo 1841622 2071831 := bstep (se 1 (by rfl) ⟨1553873, by rfl⟩ : syracuseStep 2071831 = 3107747) B3107747
theorem B1842455 : Blo 1841622 1842455 := bstep (se 1 (by rfl) ⟨1381841, by rfl⟩ : syracuseStep 1842455 = 2763683) B2763683
theorem B4144409 : Blo 1841622 4144409 := bstep (se 2 (by rfl) ⟨1554153, by rfl⟩ : syracuseStep 4144409 = 3108307) B3108307
theorem B1842475 : Blo 1841622 1842475 := bstep (se 1 (by rfl) ⟨1381856, by rfl⟩ : syracuseStep 1842475 = 2763713) B2763713
theorem B1842487 : Blo 1841622 1842487 := bstep (se 1 (by rfl) ⟨1381865, by rfl⟩ : syracuseStep 1842487 = 2763731) B2763731
theorem B1842507 : Blo 1841622 1842507 := bstep (se 1 (by rfl) ⟨1381880, by rfl⟩ : syracuseStep 1842507 = 2763761) B2763761
theorem B1842519 : Blo 1841622 1842519 := bstep (se 1 (by rfl) ⟨1381889, by rfl⟩ : syracuseStep 1842519 = 2763779) B2763779
theorem B7871833 : Blo 1841622 7871833 := bstep (se 2 (by rfl) ⟨2951937, by rfl⟩ : syracuseStep 7871833 = 5903875) B5903875
theorem B1842539 : Blo 1841622 1842539 := bstep (se 1 (by rfl) ⟨1381904, by rfl⟩ : syracuseStep 1842539 = 2763809) B2763809
theorem B4144499 : Blo 1841622 4144499 := bstep (se 1 (by rfl) ⟨3108374, by rfl⟩ : syracuseStep 4144499 = 6216749) B6216749
theorem B1842551 : Blo 1841622 1842551 := bstep (se 1 (by rfl) ⟨1381913, by rfl⟩ : syracuseStep 1842551 = 2763827) B2763827
theorem B1842571 : Blo 1841622 1842571 := bstep (se 1 (by rfl) ⟨1381928, by rfl⟩ : syracuseStep 1842571 = 2763857) B2763857
theorem B4144535 : Blo 1841622 4144535 := bstep (se 1 (by rfl) ⟨3108401, by rfl⟩ : syracuseStep 4144535 = 6216803) B6216803
theorem B1842583 : Blo 1841622 1842583 := bstep (se 1 (by rfl) ⟨1381937, by rfl⟩ : syracuseStep 1842583 = 2763875) B2763875
theorem B1842603 : Blo 1841622 1842603 := bstep (se 1 (by rfl) ⟨1381952, by rfl⟩ : syracuseStep 1842603 = 2763905) B2763905
theorem B1842615 : Blo 1841622 1842615 := bstep (se 1 (by rfl) ⟨1381961, by rfl⟩ : syracuseStep 1842615 = 2763923) B2763923
theorem B6995393 : Blo 1841622 6995393 := bstep (se 2 (by rfl) ⟨2623272, by rfl⟩ : syracuseStep 6995393 = 5246545) B5246545
theorem B2072011 : Blo 1841622 2072011 := bstep (se 1 (by rfl) ⟨1554008, by rfl⟩ : syracuseStep 2072011 = 3108017) B3108017
theorem B1842635 : Blo 1841622 1842635 := bstep (se 1 (by rfl) ⟨1381976, by rfl⟩ : syracuseStep 1842635 = 2763953) B2763953
theorem B3497431 : Blo 1841622 3497431 := bstep (se 1 (by rfl) ⟨2623073, by rfl⟩ : syracuseStep 3497431 = 5246147) B5246147
theorem B1842647 : Blo 1841622 1842647 := bstep (se 1 (by rfl) ⟨1381985, by rfl⟩ : syracuseStep 1842647 = 2763971) B2763971
theorem B20979161 : Blo 1841622 20979161 := bstep (se 2 (by rfl) ⟨7867185, by rfl⟩ : syracuseStep 20979161 = 15734371) B15734371
theorem B6217181 : Blo 1841622 6217181 := bstep (se 3 (by rfl) ⟨1165721, by rfl⟩ : syracuseStep 6217181 = 2331443) B2331443
theorem B1842667 : Blo 1841622 1842667 := bstep (se 1 (by rfl) ⟨1382000, by rfl⟩ : syracuseStep 1842667 = 2764001) B2764001
theorem B1842679 : Blo 1841622 1842679 := bstep (se 1 (by rfl) ⟨1382009, by rfl⟩ : syracuseStep 1842679 = 2764019) B2764019
theorem B1842699 : Blo 1841622 1842699 := bstep (se 1 (by rfl) ⟨1382024, by rfl⟩ : syracuseStep 1842699 = 2764049) B2764049
theorem B1842711 : Blo 1841622 1842711 := bstep (se 1 (by rfl) ⟨1382033, by rfl⟩ : syracuseStep 1842711 = 2764067) B2764067
theorem B15736355 : Blo 1841622 15736355 := bstep (se 1 (by rfl) ⟨11802266, by rfl⟩ : syracuseStep 15736355 = 23604533) B23604533
theorem B17956387 : Blo 1841622 17956387 := bstep (se 1 (by rfl) ⟨13467290, by rfl⟩ : syracuseStep 17956387 = 26934581) B26934581
theorem B1842731 : Blo 1841622 1842731 := bstep (se 1 (by rfl) ⟨1382048, by rfl⟩ : syracuseStep 1842731 = 2764097) B2764097
theorem B2072119 : Blo 1841622 2072119 := bstep (se 1 (by rfl) ⟨1554089, by rfl⟩ : syracuseStep 2072119 = 3108179) B3108179
theorem B1842743 : Blo 1841622 1842743 := bstep (se 1 (by rfl) ⟨1382057, by rfl⟩ : syracuseStep 1842743 = 2764115) B2764115
theorem B4144715 : Blo 1841622 4144715 := bstep (se 1 (by rfl) ⟨3108536, by rfl⟩ : syracuseStep 4144715 = 6217073) B6217073
theorem B1842763 : Blo 1841622 1842763 := bstep (se 1 (by rfl) ⟨1382072, by rfl⟩ : syracuseStep 1842763 = 2764145) B2764145
theorem B1842775 : Blo 1841622 1842775 := bstep (se 1 (by rfl) ⟨1382081, by rfl⟩ : syracuseStep 1842775 = 2764163) B2764163
theorem B1842795 : Blo 1841622 1842795 := bstep (se 1 (by rfl) ⟨1382096, by rfl⟩ : syracuseStep 1842795 = 2764193) B2764193
theorem B3743347 : Blo 1841622 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1842807 : Blo 1841622 1842807 := bstep (se 1 (by rfl) ⟨1382105, by rfl⟩ : syracuseStep 1842807 = 2764211) B2764211
theorem B4144769 : Blo 1841622 4144769 := bstep (se 2 (by rfl) ⟨1554288, by rfl⟩ : syracuseStep 4144769 = 3108577) B3108577
theorem B1842827 : Blo 1841622 1842827 := bstep (se 1 (by rfl) ⟨1382120, by rfl⟩ : syracuseStep 1842827 = 2764241) B2764241
theorem B1842839 : Blo 1841622 1842839 := bstep (se 1 (by rfl) ⟨1382129, by rfl⟩ : syracuseStep 1842839 = 2764259) B2764259
theorem B1842859 : Blo 1841622 1842859 := bstep (se 1 (by rfl) ⟨1382144, by rfl⟩ : syracuseStep 1842859 = 2764289) B2764289
theorem B3497651 : Blo 1841622 3497651 := bstep (se 1 (by rfl) ⟨2623238, by rfl⟩ : syracuseStep 3497651 = 5246477) B5246477
theorem B1842871 : Blo 1841622 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B1842891 : Blo 1841622 1842891 := bstep (se 1 (by rfl) ⟨1382168, by rfl⟩ : syracuseStep 1842891 = 2764337) B2764337
theorem B1842903 : Blo 1841622 1842903 := bstep (se 1 (by rfl) ⟨1382177, by rfl⟩ : syracuseStep 1842903 = 2764355) B2764355
theorem B2072299 : Blo 1841622 2072299 := bstep (se 1 (by rfl) ⟨1554224, by rfl⟩ : syracuseStep 2072299 = 3108449) B3108449
theorem B1842923 : Blo 1841622 1842923 := bstep (se 1 (by rfl) ⟨1382192, by rfl⟩ : syracuseStep 1842923 = 2764385) B2764385
theorem B1842935 : Blo 1841622 1842935 := bstep (se 1 (by rfl) ⟨1382201, by rfl⟩ : syracuseStep 1842935 = 2764403) B2764403
theorem B1842955 : Blo 1841622 1842955 := bstep (se 1 (by rfl) ⟨1382216, by rfl⟩ : syracuseStep 1842955 = 2764433) B2764433
theorem B1842967 : Blo 1841622 1842967 := bstep (se 1 (by rfl) ⟨1382225, by rfl⟩ : syracuseStep 1842967 = 2764451) B2764451
theorem B1842987 : Blo 1841622 1842987 := bstep (se 1 (by rfl) ⟨1382240, by rfl⟩ : syracuseStep 1842987 = 2764481) B2764481
theorem B1842999 : Blo 1841622 1842999 := bstep (se 1 (by rfl) ⟨1382249, by rfl⟩ : syracuseStep 1842999 = 2764499) B2764499
theorem B7470913 : Blo 1841622 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B17956673 : Blo 1841622 17956673 := bstep (se 2 (by rfl) ⟨6733752, by rfl⟩ : syracuseStep 17956673 = 13467505) B13467505
theorem B1843019 : Blo 1841622 1843019 := bstep (se 1 (by rfl) ⟨1382264, by rfl⟩ : syracuseStep 1843019 = 2764529) B2764529
theorem B2072407 : Blo 1841622 2072407 := bstep (se 1 (by rfl) ⟨1554305, by rfl⟩ : syracuseStep 2072407 = 3108611) B3108611
theorem B4144985 : Blo 1841622 4144985 := bstep (se 2 (by rfl) ⟨1554369, by rfl⟩ : syracuseStep 4144985 = 3108739) B3108739
theorem B1843031 : Blo 1841622 1843031 := bstep (se 1 (by rfl) ⟨1382273, by rfl⟩ : syracuseStep 1843031 = 2764547) B2764547
theorem B1843051 : Blo 1841622 1843051 := bstep (se 1 (by rfl) ⟨1382288, by rfl⟩ : syracuseStep 1843051 = 2764577) B2764577
theorem B1843063 : Blo 1841622 1843063 := bstep (se 1 (by rfl) ⟨1382297, by rfl⟩ : syracuseStep 1843063 = 2764595) B2764595
theorem B1843083 : Blo 1841622 1843083 := bstep (se 1 (by rfl) ⟨1382312, by rfl⟩ : syracuseStep 1843083 = 2764625) B2764625
theorem B3497879 : Blo 1841622 3497879 := bstep (se 1 (by rfl) ⟨2623409, by rfl⟩ : syracuseStep 3497879 = 5246819) B5246819
theorem B1843095 : Blo 1841622 1843095 := bstep (se 1 (by rfl) ⟨1382321, by rfl⟩ : syracuseStep 1843095 = 2764643) B2764643
theorem B1843115 : Blo 1841622 1843115 := bstep (se 1 (by rfl) ⟨1382336, by rfl⟩ : syracuseStep 1843115 = 2764673) B2764673
theorem B4145075 : Blo 1841622 4145075 := bstep (se 1 (by rfl) ⟨3108806, by rfl⟩ : syracuseStep 4145075 = 6217613) B6217613
theorem B1843127 : Blo 1841622 1843127 := bstep (se 1 (by rfl) ⟨1382345, by rfl⟩ : syracuseStep 1843127 = 2764691) B2764691
theorem B1843147 : Blo 1841622 1843147 := bstep (se 1 (by rfl) ⟨1382360, by rfl⟩ : syracuseStep 1843147 = 2764721) B2764721
theorem B4145111 : Blo 1841622 4145111 := bstep (se 1 (by rfl) ⟨3108833, by rfl⟩ : syracuseStep 4145111 = 6217667) B6217667
theorem B1843159 : Blo 1841622 1843159 := bstep (se 1 (by rfl) ⟨1382369, by rfl⟩ : syracuseStep 1843159 = 2764739) B2764739
theorem B1843179 : Blo 1841622 1843179 := bstep (se 1 (by rfl) ⟨1382384, by rfl⟩ : syracuseStep 1843179 = 2764769) B2764769
theorem B1843191 : Blo 1841622 1843191 := bstep (se 1 (by rfl) ⟨1382393, by rfl⟩ : syracuseStep 1843191 = 2764787) B2764787
theorem B20987909 : Blo 1841622 20987909 := bstep (se 4 (by rfl) ⟨1967616, by rfl⟩ : syracuseStep 20987909 = 3935233) B3935233
theorem B1843207 : Blo 1841622 1843207 := bstep (se 1 (by rfl) ⟨1382405, by rfl⟩ : syracuseStep 1843207 = 2764811) B2764811
theorem B1843215 : Blo 1841622 1843215 := bstep (se 1 (by rfl) ⟨1382411, by rfl⟩ : syracuseStep 1843215 = 2764823) B2764823
theorem B1843259 : Blo 1841622 1843259 := bstep (se 1 (by rfl) ⟨1382444, by rfl⟩ : syracuseStep 1843259 = 2764889) B2764889
theorem B7979095 : Blo 1841622 7979095 := bstep (se 1 (by rfl) ⟨5984321, by rfl⟩ : syracuseStep 7979095 = 11968643) B11968643
theorem B1843335 : Blo 1841622 1843335 := bstep (se 1 (by rfl) ⟨1382501, by rfl⟩ : syracuseStep 1843335 = 2765003) B2765003
theorem B1843343 : Blo 1841622 1843343 := bstep (se 1 (by rfl) ⟨1382507, by rfl⟩ : syracuseStep 1843343 = 2765015) B2765015
theorem B1843387 : Blo 1841622 1843387 := bstep (se 1 (by rfl) ⟨1382540, by rfl⟩ : syracuseStep 1843387 = 2765081) B2765081
theorem B2072839 : Blo 1841622 2072839 := bstep (se 1 (by rfl) ⟨1554629, by rfl⟩ : syracuseStep 2072839 = 3109259) B3109259
theorem B1843463 : Blo 1841622 1843463 := bstep (se 1 (by rfl) ⟨1382597, by rfl⟩ : syracuseStep 1843463 = 2765195) B2765195
theorem B4981007 : Blo 1841622 4981007 := bstep (se 1 (by rfl) ⟨3735755, by rfl⟩ : syracuseStep 4981007 = 7471511) B7471511
theorem B1843471 : Blo 1841622 1843471 := bstep (se 1 (by rfl) ⟨1382603, by rfl⟩ : syracuseStep 1843471 = 2765207) B2765207
theorem B1843515 : Blo 1841622 1843515 := bstep (se 1 (by rfl) ⟨1382636, by rfl⟩ : syracuseStep 1843515 = 2765273) B2765273
theorem B6218099 : Blo 1841622 6218099 := bstep (se 1 (by rfl) ⟨4663574, by rfl⟩ : syracuseStep 6218099 = 9327149) B9327149
theorem B4145543 : Blo 1841622 4145543 := bstep (se 1 (by rfl) ⟨3109157, by rfl⟩ : syracuseStep 4145543 = 6218315) B6218315
theorem B1843591 : Blo 1841622 1843591 := bstep (se 1 (by rfl) ⟨1382693, by rfl⟩ : syracuseStep 1843591 = 2765387) B2765387
theorem B1843599 : Blo 1841622 1843599 := bstep (se 1 (by rfl) ⟨1382699, by rfl⟩ : syracuseStep 1843599 = 2765399) B2765399
theorem B4661651 : Blo 1841622 4661651 := bstep (se 1 (by rfl) ⟨3496238, by rfl⟩ : syracuseStep 4661651 = 6992477) B6992477
theorem B12132755 : Blo 1841622 12132755 := bstep (se 1 (by rfl) ⟨9099566, by rfl⟩ : syracuseStep 12132755 = 18199133) B18199133
theorem B2073019 : Blo 1841622 2073019 := bstep (se 1 (by rfl) ⟨1554764, by rfl⟩ : syracuseStep 2073019 = 3109529) B3109529
theorem B4145723 : Blo 1841622 4145723 := bstep (se 1 (by rfl) ⟨3109292, by rfl⟩ : syracuseStep 4145723 = 6218585) B6218585
theorem B4661945 : Blo 1841622 4661945 := bstep (se 2 (by rfl) ⟨1748229, by rfl⟩ : syracuseStep 4661945 = 3496459) B3496459
theorem B4145849 : Blo 1841622 4145849 := bstep (se 2 (by rfl) ⟨1554693, by rfl⟩ : syracuseStep 4145849 = 3109387) B3109387
theorem B6644513 : Blo 1841622 6644513 := bstep (se 2 (by rfl) ⟨2491692, by rfl⟩ : syracuseStep 6644513 = 4983385) B4983385
theorem B6996851 : Blo 1841622 6996851 := bstep (se 1 (by rfl) ⟨5247638, by rfl⟩ : syracuseStep 6996851 = 10495277) B10495277
theorem B2491255 : Blo 1841622 2491255 := bstep (se 1 (by rfl) ⟨1868441, by rfl⟩ : syracuseStep 2491255 = 3736883) B3736883
theorem B2073487 : Blo 1841622 2073487 := bstep (se 1 (by rfl) ⟨1555115, by rfl⟩ : syracuseStep 2073487 = 3110231) B3110231
theorem B9962443 : Blo 1841622 9962443 := bstep (se 1 (by rfl) ⟨7471832, by rfl⟩ : syracuseStep 9962443 = 14943665) B14943665
theorem B4146191 : Blo 1841622 4146191 := bstep (se 1 (by rfl) ⟨3109643, by rfl⟩ : syracuseStep 4146191 = 6219287) B6219287
theorem B4146209 : Blo 1841622 4146209 := bstep (se 2 (by rfl) ⟨1554828, by rfl⟩ : syracuseStep 4146209 = 3109657) B3109657
theorem B4981819 : Blo 1841622 4981819 := bstep (se 1 (by rfl) ⟨3736364, by rfl⟩ : syracuseStep 4981819 = 7472729) B7472729
theorem B3499193 : Blo 1841622 3499193 := bstep (se 2 (by rfl) ⟨1312197, by rfl⟩ : syracuseStep 3499193 = 2624395) B2624395
theorem B4662643 : Blo 1841622 4662643 := bstep (se 1 (by rfl) ⟨3496982, by rfl⟩ : syracuseStep 4662643 = 6993965) B6993965
theorem B3933559 : Blo 1841622 3933559 := bstep (se 1 (by rfl) ⟨2950169, by rfl⟩ : syracuseStep 3933559 = 5900339) B5900339
theorem B4146551 : Blo 1841622 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B2073991 : Blo 1841622 2073991 := bstep (se 1 (by rfl) ⟨1555493, by rfl⟩ : syracuseStep 2073991 = 3110987) B3110987
theorem B9332171 : Blo 1841622 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B4662785 : Blo 1841622 4662785 := bstep (se 2 (by rfl) ⟨1748544, by rfl⟩ : syracuseStep 4662785 = 3497089) B3497089
theorem B34072093 : Blo 1841622 34072093 := bstep (se 3 (by rfl) ⟨6388517, by rfl⟩ : syracuseStep 34072093 = 12777035) B12777035
theorem B4146731 : Blo 1841622 4146731 := bstep (se 1 (by rfl) ⟨3110048, by rfl⟩ : syracuseStep 4146731 = 6220097) B6220097
theorem B4204075 : Blo 1841622 4204075 := bstep (se 1 (by rfl) ⟨3153056, by rfl⟩ : syracuseStep 4204075 = 6306113) B6306113
theorem B2623033 : Blo 1841622 2623033 := bstep (se 2 (by rfl) ⟨983637, by rfl⟩ : syracuseStep 2623033 = 1967275) B1967275
theorem B5244563 : Blo 1841622 5244563 := bstep (se 1 (by rfl) ⟨3933422, by rfl⟩ : syracuseStep 5244563 = 7866845) B7866845
theorem B2762441 : Blo 1841622 2762441 := bstep (se 2 (by rfl) ⟨1035915, by rfl⟩ : syracuseStep 2762441 = 2071831) B2071831
theorem B9324233 : Blo 1841622 9324233 := bstep (se 2 (by rfl) ⟨3496587, by rfl⟩ : syracuseStep 9324233 = 6993175) B6993175
theorem B4982543 : Blo 1841622 4982543 := bstep (se 1 (by rfl) ⟨3736907, by rfl⟩ : syracuseStep 4982543 = 7473815) B7473815
theorem B9332495 : Blo 1841622 9332495 := bstep (se 1 (by rfl) ⟨6999371, by rfl⟩ : syracuseStep 9332495 = 13998743) B13998743
theorem B9455393 : Blo 1841622 9455393 := bstep (se 2 (by rfl) ⟨3545772, by rfl⟩ : syracuseStep 9455393 = 7091545) B7091545
theorem B10495777 : Blo 1841622 10495777 := bstep (se 2 (by rfl) ⟨3935916, by rfl⟩ : syracuseStep 10495777 = 7871833) B7871833
theorem B2762555 : Blo 1841622 2762555 := bstep (se 1 (by rfl) ⟨2071916, by rfl⟩ : syracuseStep 2762555 = 4143833) B4143833
theorem B2762615 : Blo 1841622 2762615 := bstep (se 1 (by rfl) ⟨2071961, by rfl⟩ : syracuseStep 2762615 = 4143923) B4143923
theorem B2762639 : Blo 1841622 2762639 := bstep (se 1 (by rfl) ⟨2071979, by rfl⟩ : syracuseStep 2762639 = 4143959) B4143959
theorem B2623375 : Blo 1841622 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B4147091 : Blo 1841622 4147091 := bstep (se 1 (by rfl) ⟨3110318, by rfl⟩ : syracuseStep 4147091 = 6220637) B6220637
theorem B2762681 : Blo 1841622 2762681 := bstep (se 2 (by rfl) ⟨1036005, by rfl⟩ : syracuseStep 2762681 = 2072011) B2072011
theorem B5982137 : Blo 1841622 5982137 := bstep (se 2 (by rfl) ⟨2243301, by rfl⟩ : syracuseStep 5982137 = 4486603) B4486603
theorem B4663241 : Blo 1841622 4663241 := bstep (se 2 (by rfl) ⟨1748715, by rfl⟩ : syracuseStep 4663241 = 3497431) B3497431
theorem B4147145 : Blo 1841622 4147145 := bstep (se 2 (by rfl) ⟨1555179, by rfl⟩ : syracuseStep 4147145 = 3110359) B3110359
theorem B9963485 : Blo 1841622 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B2762759 : Blo 1841622 2762759 := bstep (se 1 (by rfl) ⟨2072069, by rfl⟩ : syracuseStep 2762759 = 4144139) B4144139
theorem B38332433 : Blo 1841622 38332433 := bstep (se 2 (by rfl) ⟨14374662, by rfl⟩ : syracuseStep 38332433 = 28749325) B28749325
theorem B2762795 : Blo 1841622 2762795 := bstep (se 1 (by rfl) ⟨2072096, by rfl⟩ : syracuseStep 2762795 = 4144193) B4144193
theorem B7874603 : Blo 1841622 7874603 := bstep (se 1 (by rfl) ⟨5905952, by rfl⟩ : syracuseStep 7874603 = 11811905) B11811905
theorem B2762825 : Blo 1841622 2762825 := bstep (se 2 (by rfl) ⟨1036059, by rfl⟩ : syracuseStep 2762825 = 2072119) B2072119
theorem B4991129 : Blo 1841622 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B5605529 : Blo 1841622 5605529 := bstep (se 2 (by rfl) ⟨2102073, by rfl⟩ : syracuseStep 5605529 = 4204147) B4204147
theorem B2762939 : Blo 1841622 2762939 := bstep (se 1 (by rfl) ⟨2072204, by rfl⟩ : syracuseStep 2762939 = 4144409) B4144409
theorem B2762999 : Blo 1841622 2762999 := bstep (se 1 (by rfl) ⟨2072249, by rfl⟩ : syracuseStep 2762999 = 4144499) B4144499
theorem B2763023 : Blo 1841622 2763023 := bstep (se 1 (by rfl) ⟨2072267, by rfl⟩ : syracuseStep 2763023 = 4144535) B4144535
theorem B4663595 : Blo 1841622 4663595 := bstep (se 1 (by rfl) ⟨3497696, by rfl⟩ : syracuseStep 4663595 = 6995393) B6995393
theorem B2763065 : Blo 1841622 2763065 := bstep (se 2 (by rfl) ⟨1036149, by rfl⟩ : syracuseStep 2763065 = 2072299) B2072299
theorem B13986107 : Blo 1841622 13986107 := bstep (se 1 (by rfl) ⟨10489580, by rfl⟩ : syracuseStep 13986107 = 20979161) B20979161
theorem B2763143 : Blo 1841622 2763143 := bstep (se 1 (by rfl) ⟨2072357, by rfl⟩ : syracuseStep 2763143 = 4144715) B4144715
theorem B33606035 : Blo 1841622 33606035 := bstep (se 1 (by rfl) ⟨25204526, by rfl⟩ : syracuseStep 33606035 = 50409053) B50409053
theorem B5245337 : Blo 1841622 5245337 := bstep (se 2 (by rfl) ⟨1967001, by rfl⟩ : syracuseStep 5245337 = 3934003) B3934003
theorem B2763179 : Blo 1841622 2763179 := bstep (se 1 (by rfl) ⟨2072384, by rfl⟩ : syracuseStep 2763179 = 4144769) B4144769
theorem B2763209 : Blo 1841622 2763209 := bstep (se 2 (by rfl) ⟨1036203, by rfl⟩ : syracuseStep 2763209 = 2072407) B2072407
theorem B2214415 : Blo 1841622 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B4426283 : Blo 1841622 4426283 := bstep (se 1 (by rfl) ⟨3319712, by rfl⟩ : syracuseStep 4426283 = 6639425) B6639425
theorem B11971115 : Blo 1841622 11971115 := bstep (se 1 (by rfl) ⟨8978336, by rfl⟩ : syracuseStep 11971115 = 17956673) B17956673
theorem B2763323 : Blo 1841622 2763323 := bstep (se 1 (by rfl) ⟨2072492, by rfl⟩ : syracuseStep 2763323 = 4144985) B4144985
theorem B2763383 : Blo 1841622 2763383 := bstep (se 1 (by rfl) ⟨2072537, by rfl⟩ : syracuseStep 2763383 = 4145075) B4145075
theorem B4147847 : Blo 1841622 4147847 := bstep (se 1 (by rfl) ⟨3110885, by rfl⟩ : syracuseStep 4147847 = 6221771) B6221771
theorem B2763407 : Blo 1841622 2763407 := bstep (se 1 (by rfl) ⟨2072555, by rfl⟩ : syracuseStep 2763407 = 4145111) B4145111
theorem B2763449 : Blo 1841622 2763449 := bstep (se 2 (by rfl) ⟨1036293, by rfl⟩ : syracuseStep 2763449 = 2072587) B2072587
theorem B2763527 : Blo 1841622 2763527 := bstep (se 1 (by rfl) ⟨2072645, by rfl⟩ : syracuseStep 2763527 = 4145291) B4145291
theorem B2763563 : Blo 1841622 2763563 := bstep (se 1 (by rfl) ⟨2072672, by rfl⟩ : syracuseStep 2763563 = 4145345) B4145345
theorem B4148027 : Blo 1841622 4148027 := bstep (se 1 (by rfl) ⟨3111020, by rfl⟩ : syracuseStep 4148027 = 6222041) B6222041
theorem B2763593 : Blo 1841622 2763593 := bstep (se 2 (by rfl) ⟨1036347, by rfl⟩ : syracuseStep 2763593 = 2072695) B2072695
theorem B10095475 : Blo 1841622 10095475 := bstep (se 1 (by rfl) ⟨7571606, by rfl⟩ : syracuseStep 10095475 = 15143213) B15143213
theorem B6220691 : Blo 1841622 6220691 := bstep (se 1 (by rfl) ⟨4665518, by rfl⟩ : syracuseStep 6220691 = 9331037) B9331037
theorem B33631139 : Blo 1841622 33631139 := bstep (se 1 (by rfl) ⟨25223354, by rfl⟩ : syracuseStep 33631139 = 50446709) B50446709
theorem B10488761 : Blo 1841622 10488761 := bstep (se 2 (by rfl) ⟨3933285, by rfl⟩ : syracuseStep 10488761 = 7866571) B7866571
theorem B2763707 : Blo 1841622 2763707 := bstep (se 1 (by rfl) ⟨2072780, by rfl⟩ : syracuseStep 2763707 = 4145561) B4145561
theorem B6998993 : Blo 1841622 6998993 := bstep (se 2 (by rfl) ⟨2624622, by rfl⟩ : syracuseStep 6998993 = 5249245) B5249245
theorem B2763767 : Blo 1841622 2763767 := bstep (se 1 (by rfl) ⟨2072825, by rfl⟩ : syracuseStep 2763767 = 4145651) B4145651
theorem B2624503 : Blo 1841622 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B3107855 : Blo 1841622 3107855 := bstep (se 1 (by rfl) ⟨2330891, by rfl⟩ : syracuseStep 3107855 = 4661783) B4661783
theorem B2763791 : Blo 1841622 2763791 := bstep (se 1 (by rfl) ⟨2072843, by rfl⟩ : syracuseStep 2763791 = 4145687) B4145687
theorem B10497053 : Blo 1841622 10497053 := bstep (se 3 (by rfl) ⟨1968197, by rfl⟩ : syracuseStep 10497053 = 3936395) B3936395
theorem B2763833 : Blo 1841622 2763833 := bstep (se 2 (by rfl) ⟨1036437, by rfl⟩ : syracuseStep 2763833 = 2072875) B2072875
theorem B7867459 : Blo 1841622 7867459 := bstep (se 1 (by rfl) ⟨5900594, by rfl⟩ : syracuseStep 7867459 = 11801189) B11801189
theorem B2763911 : Blo 1841622 2763911 := bstep (se 1 (by rfl) ⟨2072933, by rfl⟩ : syracuseStep 2763911 = 4145867) B4145867
theorem B2763947 : Blo 1841622 2763947 := bstep (se 1 (by rfl) ⟨2072960, by rfl⟩ : syracuseStep 2763947 = 4145921) B4145921
theorem B3321017 : Blo 1841622 3321017 := bstep (se 2 (by rfl) ⟨1245381, by rfl⟩ : syracuseStep 3321017 = 2490763) B2490763
theorem B2763977 : Blo 1841622 2763977 := bstep (se 2 (by rfl) ⟨1036491, by rfl⟩ : syracuseStep 2763977 = 2072983) B2072983
theorem B13282541 : Blo 1841622 13282541 := bstep (se 3 (by rfl) ⟨2490476, by rfl⟩ : syracuseStep 13282541 = 4980953) B4980953
theorem B5901569 : Blo 1841622 5901569 := bstep (se 2 (by rfl) ⟨2213088, by rfl⟩ : syracuseStep 5901569 = 4426177) B4426177
theorem B4664587 : Blo 1841622 4664587 := bstep (se 1 (by rfl) ⟨3498440, by rfl⟩ : syracuseStep 4664587 = 6996881) B6996881
theorem B6999311 : Blo 1841622 6999311 := bstep (se 1 (by rfl) ⟨5249483, by rfl⟩ : syracuseStep 6999311 = 10498967) B10498967
theorem B8850721 : Blo 1841622 8850721 := bstep (se 2 (by rfl) ⟨3319020, by rfl⟩ : syracuseStep 8850721 = 6638041) B6638041
theorem B2764091 : Blo 1841622 2764091 := bstep (se 1 (by rfl) ⟨2073068, by rfl⟩ : syracuseStep 2764091 = 4146137) B4146137
theorem B2764151 : Blo 1841622 2764151 := bstep (se 1 (by rfl) ⟨2073113, by rfl⟩ : syracuseStep 2764151 = 4146227) B4146227
theorem B2764175 : Blo 1841622 2764175 := bstep (se 1 (by rfl) ⟨2073131, by rfl⟩ : syracuseStep 2764175 = 4146263) B4146263
theorem B4664729 : Blo 1841622 4664729 := bstep (se 2 (by rfl) ⟨1749273, by rfl⟩ : syracuseStep 4664729 = 3498547) B3498547
theorem B2764217 : Blo 1841622 2764217 := bstep (se 2 (by rfl) ⟨1036581, by rfl⟩ : syracuseStep 2764217 = 2073163) B2073163
theorem B2764295 : Blo 1841622 2764295 := bstep (se 1 (by rfl) ⟨2073221, by rfl⟩ : syracuseStep 2764295 = 4146443) B4146443
theorem B3108395 : Blo 1841622 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B2764331 : Blo 1841622 2764331 := bstep (se 1 (by rfl) ⟨2073248, by rfl⟩ : syracuseStep 2764331 = 4146497) B4146497
theorem B4664891 : Blo 1841622 4664891 := bstep (se 1 (by rfl) ⟨3498668, by rfl⟩ : syracuseStep 4664891 = 6997337) B6997337
theorem B2764361 : Blo 1841622 2764361 := bstep (se 2 (by rfl) ⟨1036635, by rfl⟩ : syracuseStep 2764361 = 2073271) B2073271
theorem B3321479 : Blo 1841622 3321479 := bstep (se 1 (by rfl) ⟨2491109, by rfl⟩ : syracuseStep 3321479 = 4982219) B4982219
theorem B2764475 : Blo 1841622 2764475 := bstep (se 1 (by rfl) ⟨2073356, by rfl⟩ : syracuseStep 2764475 = 4146713) B4146713
theorem B2764535 : Blo 1841622 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B2764559 : Blo 1841622 2764559 := bstep (se 1 (by rfl) ⟨2073419, by rfl⟩ : syracuseStep 2764559 = 4146839) B4146839
theorem B13995827 : Blo 1841622 13995827 := bstep (se 1 (by rfl) ⟨10496870, by rfl⟩ : syracuseStep 13995827 = 20993741) B20993741
theorem B2764601 : Blo 1841622 2764601 := bstep (se 2 (by rfl) ⟨1036725, by rfl⟩ : syracuseStep 2764601 = 2073451) B2073451
theorem B33607493 : Blo 1841622 33607493 := bstep (se 4 (by rfl) ⟨3150702, by rfl⟩ : syracuseStep 33607493 = 6301405) B6301405
theorem B2764679 : Blo 1841622 2764679 := bstep (se 1 (by rfl) ⟨2073509, by rfl⟩ : syracuseStep 2764679 = 4147019) B4147019
theorem B4665235 : Blo 1841622 4665235 := bstep (se 1 (by rfl) ⟨3498926, by rfl⟩ : syracuseStep 4665235 = 6997853) B6997853
theorem B2764715 : Blo 1841622 2764715 := bstep (se 1 (by rfl) ⟨2073536, by rfl⟩ : syracuseStep 2764715 = 4147073) B4147073
theorem B3108793 : Blo 1841622 3108793 := bstep (se 2 (by rfl) ⟨1165797, by rfl⟩ : syracuseStep 3108793 = 2331595) B2331595
theorem B2879417 : Blo 1841622 2879417 := bstep (se 2 (by rfl) ⟨1079781, by rfl⟩ : syracuseStep 2879417 = 2159563) B2159563
theorem B2764745 : Blo 1841622 2764745 := bstep (se 2 (by rfl) ⟨1036779, by rfl⟩ : syracuseStep 2764745 = 2073559) B2073559
theorem B4665377 : Blo 1841622 4665377 := bstep (se 2 (by rfl) ⟨1749516, by rfl⟩ : syracuseStep 4665377 = 3499033) B3499033
theorem B2101307 : Blo 1841622 2101307 := bstep (se 1 (by rfl) ⟨1575980, by rfl⟩ : syracuseStep 2101307 = 3151961) B3151961
theorem B2764859 : Blo 1841622 2764859 := bstep (se 1 (by rfl) ⟨2073644, by rfl⟩ : syracuseStep 2764859 = 4147289) B4147289
theorem B2764919 : Blo 1841622 2764919 := bstep (se 1 (by rfl) ⟨2073689, by rfl⟩ : syracuseStep 2764919 = 4147379) B4147379
theorem B2764943 : Blo 1841622 2764943 := bstep (se 1 (by rfl) ⟨2073707, by rfl⟩ : syracuseStep 2764943 = 4147415) B4147415
theorem B2764985 : Blo 1841622 2764985 := bstep (se 2 (by rfl) ⟨1036869, by rfl⟩ : syracuseStep 2764985 = 2073739) B2073739
theorem B20197613 : Blo 1841622 20197613 := bstep (se 3 (by rfl) ⟨3787052, by rfl⟩ : syracuseStep 20197613 = 7574105) B7574105
theorem B2765063 : Blo 1841622 2765063 := bstep (se 1 (by rfl) ⟨2073797, by rfl⟩ : syracuseStep 2765063 = 4147595) B4147595
theorem B6639887 : Blo 1841622 6639887 := bstep (se 1 (by rfl) ⟨4979915, by rfl⟩ : syracuseStep 6639887 = 9959831) B9959831
theorem B3838223 : Blo 1841622 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B6222095 : Blo 1841622 6222095 := bstep (se 1 (by rfl) ⟨4666571, by rfl⟩ : syracuseStep 6222095 = 9333143) B9333143
theorem B2765099 : Blo 1841622 2765099 := bstep (se 1 (by rfl) ⟨2073824, by rfl⟩ : syracuseStep 2765099 = 4147649) B4147649
theorem B2765129 : Blo 1841622 2765129 := bstep (se 2 (by rfl) ⟨1036923, by rfl⟩ : syracuseStep 2765129 = 2073847) B2073847
theorem B2765243 : Blo 1841622 2765243 := bstep (se 1 (by rfl) ⟨2073932, by rfl⟩ : syracuseStep 2765243 = 4147865) B4147865
theorem B5247433 : Blo 1841622 5247433 := bstep (se 2 (by rfl) ⟨1967787, by rfl⟩ : syracuseStep 5247433 = 3935575) B3935575
theorem B22401485 : Blo 1841622 22401485 := bstep (se 3 (by rfl) ⟨4200278, by rfl⟩ : syracuseStep 22401485 = 8400557) B8400557
theorem B2765303 : Blo 1841622 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B2765327 : Blo 1841622 2765327 := bstep (se 1 (by rfl) ⟨2073995, by rfl⟩ : syracuseStep 2765327 = 4147991) B4147991
theorem B2765369 : Blo 1841622 2765369 := bstep (se 2 (by rfl) ⟨1037013, by rfl⟩ : syracuseStep 2765369 = 2074027) B2074027
theorem B17715779 : Blo 1841622 17715779 := bstep (se 1 (by rfl) ⟨13286834, by rfl⟩ : syracuseStep 17715779 = 26573669) B26573669
theorem B3109495 : Blo 1841622 3109495 := bstep (se 1 (by rfl) ⟨2332121, by rfl⟩ : syracuseStep 3109495 = 4664243) B4664243
theorem B2331271 : Blo 1841622 2331271 := bstep (se 1 (by rfl) ⟨1748453, by rfl⟩ : syracuseStep 2331271 = 3496907) B3496907
theorem B23941849 : Blo 1841622 23941849 := bstep (se 2 (by rfl) ⟨8978193, by rfl⟩ : syracuseStep 23941849 = 17956387) B17956387
theorem B8516353 : Blo 1841622 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B5247787 : Blo 1841622 5247787 := bstep (se 1 (by rfl) ⟨3935840, by rfl⟩ : syracuseStep 5247787 = 7871681) B7871681
theorem B17699633 : Blo 1841622 17699633 := bstep (se 2 (by rfl) ⟨6637362, by rfl⟩ : syracuseStep 17699633 = 13274725) B13274725
theorem B3109691 : Blo 1841622 3109691 := bstep (se 1 (by rfl) ⟨2332268, by rfl⟩ : syracuseStep 3109691 = 4664537) B4664537
theorem B11801497 : Blo 1841622 11801497 := bstep (se 2 (by rfl) ⟨4425561, by rfl⟩ : syracuseStep 11801497 = 8851123) B8851123
theorem B4666369 : Blo 1841622 4666369 := bstep (se 2 (by rfl) ⟨1749888, by rfl⟩ : syracuseStep 4666369 = 3499777) B3499777
theorem B10490903 : Blo 1841622 10490903 := bstep (se 1 (by rfl) ⟨7868177, by rfl⟩ : syracuseStep 10490903 = 15736355) B15736355
theorem B5248061 : Blo 1841622 5248061 := bstep (se 3 (by rfl) ⟨984011, by rfl⟩ : syracuseStep 5248061 = 1968023) B1968023
theorem B6992963 : Blo 1841622 6992963 := bstep (se 1 (by rfl) ⟨5244722, by rfl⟩ : syracuseStep 6992963 = 10489445) B10489445
theorem B2331767 : Blo 1841622 2331767 := bstep (se 1 (by rfl) ⟨1748825, by rfl⟩ : syracuseStep 2331767 = 3497651) B3497651
theorem B3110089 : Blo 1841622 3110089 := bstep (se 2 (by rfl) ⟨1166283, by rfl⟩ : syracuseStep 3110089 = 2332567) B2332567
theorem B3937481 : Blo 1841622 3937481 := bstep (se 2 (by rfl) ⟨1476555, by rfl⟩ : syracuseStep 3937481 = 2953111) B2953111
theorem B179336429 : Blo 1841622 179336429 := bstep (se 3 (by rfl) ⟨33625580, by rfl⟩ : syracuseStep 179336429 = 67251161) B67251161
theorem B2331919 : Blo 1841622 2331919 := bstep (se 1 (by rfl) ⟨1748939, by rfl⟩ : syracuseStep 2331919 = 3497879) B3497879
theorem B17708321 : Blo 1841622 17708321 := bstep (se 2 (by rfl) ⟨6640620, by rfl⟩ : syracuseStep 17708321 = 13281241) B13281241
theorem B15963425 : Blo 1841622 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B2332091 : Blo 1841622 2332091 := bstep (se 1 (by rfl) ⟨1749068, by rfl⟩ : syracuseStep 2332091 = 3498137) B3498137
theorem B7869905 : Blo 1841622 7869905 := bstep (se 2 (by rfl) ⟨2951214, by rfl⟩ : syracuseStep 7869905 = 5902429) B5902429
theorem B10491403 : Blo 1841622 10491403 := bstep (se 1 (by rfl) ⟨7868552, by rfl⟩ : syracuseStep 10491403 = 15737105) B15737105
theorem B10499651 : Blo 1841622 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B23025329 : Blo 1841622 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B19920563 : Blo 1841622 19920563 := bstep (se 1 (by rfl) ⟨14940422, by rfl⟩ : syracuseStep 19920563 = 29880845) B29880845
theorem B11802419 : Blo 1841622 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B3110791 : Blo 1841622 3110791 := bstep (se 1 (by rfl) ⟨2333093, by rfl⟩ : syracuseStep 3110791 = 4666187) B4666187
theorem B9459665 : Blo 1841622 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B6215723 : Blo 1841622 6215723 := bstep (se 1 (by rfl) ⟨4661792, by rfl⟩ : syracuseStep 6215723 = 9323585) B9323585
theorem B8632439 : Blo 1841622 8632439 := bstep (se 1 (by rfl) ⟨6474329, by rfl⟩ : syracuseStep 8632439 = 12948659) B12948659
theorem B53139725 : Blo 1841622 53139725 := bstep (se 3 (by rfl) ⟨9963698, by rfl⟩ : syracuseStep 53139725 = 19927397) B19927397
theorem B63813905 : Blo 1841622 63813905 := bstep (se 2 (by rfl) ⟨23930214, by rfl⟩ : syracuseStep 63813905 = 47860429) B47860429
theorem B14940551 : Blo 1841622 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B2333063 : Blo 1841622 2333063 := bstep (se 1 (by rfl) ⟨1749797, by rfl⟩ : syracuseStep 2333063 = 3499595) B3499595
theorem B22403537 : Blo 1841622 22403537 := bstep (se 2 (by rfl) ⟨8401326, by rfl⟩ : syracuseStep 22403537 = 16802653) B16802653
theorem B1841671 : Blo 1841622 1841671 := bstep (se 1 (by rfl) ⟨1381253, by rfl⟩ : syracuseStep 1841671 = 2762507) B2762507
theorem B1841679 : Blo 1841622 1841679 := bstep (se 1 (by rfl) ⟨1381259, by rfl⟩ : syracuseStep 1841679 = 2762519) B2762519
theorem B1841723 : Blo 1841622 1841723 := bstep (se 1 (by rfl) ⟨1381292, by rfl⟩ : syracuseStep 1841723 = 2762585) B2762585
theorem B9960023 : Blo 1841622 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B1841799 : Blo 1841622 1841799 := bstep (se 1 (by rfl) ⟨1381349, by rfl⟩ : syracuseStep 1841799 = 2762699) B2762699
theorem B4487815 : Blo 1841622 4487815 := bstep (se 1 (by rfl) ⟨3365861, by rfl⟩ : syracuseStep 4487815 = 6731723) B6731723
theorem B1841807 : Blo 1841622 1841807 := bstep (se 1 (by rfl) ⟨1381355, by rfl⟩ : syracuseStep 1841807 = 2762711) B2762711
theorem B37837493 : Blo 1841622 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B1841851 : Blo 1841622 1841851 := bstep (se 1 (by rfl) ⟨1381388, by rfl⟩ : syracuseStep 1841851 = 2762777) B2762777
theorem B6994633 : Blo 1841622 6994633 := bstep (se 2 (by rfl) ⟨2622987, by rfl⟩ : syracuseStep 6994633 = 5245975) B5245975
theorem B1841927 : Blo 1841622 1841927 := bstep (se 1 (by rfl) ⟨1381445, by rfl⟩ : syracuseStep 1841927 = 2762891) B2762891
theorem B4143887 : Blo 1841622 4143887 := bstep (se 1 (by rfl) ⟨3107915, by rfl⟩ : syracuseStep 4143887 = 6215831) B6215831
theorem B1841935 : Blo 1841622 1841935 := bstep (se 1 (by rfl) ⟨1381451, by rfl⟩ : syracuseStep 1841935 = 2762903) B2762903
theorem B4143905 : Blo 1841622 4143905 := bstep (se 2 (by rfl) ⟨1553964, by rfl⟩ : syracuseStep 4143905 = 3107929) B3107929
theorem B3496763 : Blo 1841622 3496763 := bstep (se 1 (by rfl) ⟨2622572, by rfl⟩ : syracuseStep 3496763 = 5245145) B5245145
theorem B1841979 : Blo 1841622 1841979 := bstep (se 1 (by rfl) ⟨1381484, by rfl⟩ : syracuseStep 1841979 = 2762969) B2762969
theorem B1842055 : Blo 1841622 1842055 := bstep (se 1 (by rfl) ⟨1381541, by rfl⟩ : syracuseStep 1842055 = 2763083) B2763083
theorem B1842063 : Blo 1841622 1842063 := bstep (se 1 (by rfl) ⟨1381547, by rfl⟩ : syracuseStep 1842063 = 2763095) B2763095
theorem B1842107 : Blo 1841622 1842107 := bstep (se 1 (by rfl) ⟨1381580, by rfl⟩ : syracuseStep 1842107 = 2763161) B2763161
theorem B1842183 : Blo 1841622 1842183 := bstep (se 1 (by rfl) ⟨1381637, by rfl⟩ : syracuseStep 1842183 = 2763275) B2763275
theorem B1842191 : Blo 1841622 1842191 := bstep (se 1 (by rfl) ⟨1381643, by rfl⟩ : syracuseStep 1842191 = 2763287) B2763287
theorem B11811851 : Blo 1841622 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B1842235 : Blo 1841622 1842235 := bstep (se 1 (by rfl) ⟨1381676, by rfl⟩ : syracuseStep 1842235 = 2763353) B2763353
theorem B4144247 : Blo 1841622 4144247 := bstep (se 1 (by rfl) ⟨3108185, by rfl⟩ : syracuseStep 4144247 = 6216371) B6216371
theorem B1842311 : Blo 1841622 1842311 := bstep (se 1 (by rfl) ⟨1381733, by rfl⟩ : syracuseStep 1842311 = 2763467) B2763467
theorem B1842319 : Blo 1841622 1842319 := bstep (se 1 (by rfl) ⟨1381739, by rfl⟩ : syracuseStep 1842319 = 2763479) B2763479
theorem B1842363 : Blo 1841622 1842363 := bstep (se 1 (by rfl) ⟨1381772, by rfl⟩ : syracuseStep 1842363 = 2763545) B2763545
theorem B1842439 : Blo 1841622 1842439 := bstep (se 1 (by rfl) ⟨1381829, by rfl⟩ : syracuseStep 1842439 = 2763659) B2763659
theorem B1842447 : Blo 1841622 1842447 := bstep (se 1 (by rfl) ⟨1381835, by rfl⟩ : syracuseStep 1842447 = 2763671) B2763671
theorem B3497249 : Blo 1841622 3497249 := bstep (se 2 (by rfl) ⟨1311468, by rfl⟩ : syracuseStep 3497249 = 2622937) B2622937
theorem B4144427 : Blo 1841622 4144427 := bstep (se 1 (by rfl) ⟨3108320, by rfl⟩ : syracuseStep 4144427 = 6216641) B6216641
theorem B2071867 : Blo 1841622 2071867 := bstep (se 1 (by rfl) ⟨1553900, by rfl⟩ : syracuseStep 2071867 = 3107801) B3107801
theorem B6217019 : Blo 1841622 6217019 := bstep (se 1 (by rfl) ⟨4662764, by rfl⟩ : syracuseStep 6217019 = 9325529) B9325529
theorem B14179643 : Blo 1841622 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B1842491 : Blo 1841622 1842491 := bstep (se 1 (by rfl) ⟨1381868, by rfl⟩ : syracuseStep 1842491 = 2763737) B2763737
theorem B1842567 : Blo 1841622 1842567 := bstep (se 1 (by rfl) ⟨1381925, by rfl⟩ : syracuseStep 1842567 = 2763851) B2763851
theorem B1842575 : Blo 1841622 1842575 := bstep (se 1 (by rfl) ⟨1381931, by rfl⟩ : syracuseStep 1842575 = 2763863) B2763863
theorem B9330065 : Blo 1841622 9330065 := bstep (se 2 (by rfl) ⟨3498774, by rfl⟩ : syracuseStep 9330065 = 6997549) B6997549
theorem B5905811 : Blo 1841622 5905811 := bstep (se 1 (by rfl) ⟨4429358, by rfl⟩ : syracuseStep 5905811 = 8858717) B8858717
theorem B6643129 : Blo 1841622 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B1842619 : Blo 1841622 1842619 := bstep (se 1 (by rfl) ⟨1381964, by rfl⟩ : syracuseStep 1842619 = 2763929) B2763929
theorem B10493387 : Blo 1841622 10493387 := bstep (se 1 (by rfl) ⟨7870040, by rfl⟩ : syracuseStep 10493387 = 15740081) B15740081
theorem B1842695 : Blo 1841622 1842695 := bstep (se 1 (by rfl) ⟨1382021, by rfl⟩ : syracuseStep 1842695 = 2764043) B2764043
theorem B1842703 : Blo 1841622 1842703 := bstep (se 1 (by rfl) ⟨1382027, by rfl⟩ : syracuseStep 1842703 = 2764055) B2764055
theorem B13991453 : Blo 1841622 13991453 := bstep (se 3 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 13991453 = 5246795) B5246795
theorem B1842747 : Blo 1841622 1842747 := bstep (se 1 (by rfl) ⟨1382060, by rfl⟩ : syracuseStep 1842747 = 2764121) B2764121
theorem B1842823 : Blo 1841622 1842823 := bstep (se 1 (by rfl) ⟨1382117, by rfl⟩ : syracuseStep 1842823 = 2764235) B2764235
theorem B1842831 : Blo 1841622 1842831 := bstep (se 1 (by rfl) ⟨1382123, by rfl⟩ : syracuseStep 1842831 = 2764247) B2764247
theorem B4144787 : Blo 1841622 4144787 := bstep (se 1 (by rfl) ⟨3108590, by rfl⟩ : syracuseStep 4144787 = 6217181) B6217181
theorem B1842875 : Blo 1841622 1842875 := bstep (se 1 (by rfl) ⟨1382156, by rfl⟩ : syracuseStep 1842875 = 2764313) B2764313
theorem B4144841 : Blo 1841622 4144841 := bstep (se 2 (by rfl) ⟨1554315, by rfl⟩ : syracuseStep 4144841 = 3108631) B3108631
theorem B9961217 : Blo 1841622 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B1842951 : Blo 1841622 1842951 := bstep (se 1 (by rfl) ⟨1382213, by rfl⟩ : syracuseStep 1842951 = 2764427) B2764427
theorem B17702671 : Blo 1841622 17702671 := bstep (se 1 (by rfl) ⟨13277003, by rfl⟩ : syracuseStep 17702671 = 26554007) B26554007
theorem B2072335 : Blo 1841622 2072335 := bstep (se 1 (by rfl) ⟨1554251, by rfl⟩ : syracuseStep 2072335 = 3108503) B3108503
theorem B1842959 : Blo 1841622 1842959 := bstep (se 1 (by rfl) ⟨1382219, by rfl⟩ : syracuseStep 1842959 = 2764439) B2764439
theorem B6217505 : Blo 1841622 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B1843003 : Blo 1841622 1843003 := bstep (se 1 (by rfl) ⟨1382252, by rfl⟩ : syracuseStep 1843003 = 2764505) B2764505
theorem B1843079 : Blo 1841622 1843079 := bstep (se 1 (by rfl) ⟨1382309, by rfl⟩ : syracuseStep 1843079 = 2764619) B2764619
theorem B1843087 : Blo 1841622 1843087 := bstep (se 1 (by rfl) ⟨1382315, by rfl⟩ : syracuseStep 1843087 = 2764631) B2764631
theorem B1843131 : Blo 1841622 1843131 := bstep (se 1 (by rfl) ⟨1382348, by rfl⟩ : syracuseStep 1843131 = 2764697) B2764697
theorem B13991939 : Blo 1841622 13991939 := bstep (se 1 (by rfl) ⟨10493954, by rfl⟩ : syracuseStep 13991939 = 20987909) B20987909
theorem B1843239 : Blo 1841622 1843239 := bstep (se 1 (by rfl) ⟨1382429, by rfl⟩ : syracuseStep 1843239 = 2764859) B2764859
theorem B1843279 : Blo 1841622 1843279 := bstep (se 1 (by rfl) ⟨1382459, by rfl⟩ : syracuseStep 1843279 = 2764919) B2764919
theorem B1843295 : Blo 1841622 1843295 := bstep (se 1 (by rfl) ⟨1382471, by rfl⟩ : syracuseStep 1843295 = 2764943) B2764943
theorem B1843323 : Blo 1841622 1843323 := bstep (se 1 (by rfl) ⟨1382492, by rfl⟩ : syracuseStep 1843323 = 2764985) B2764985
theorem B1843375 : Blo 1841622 1843375 := bstep (se 1 (by rfl) ⟨1382531, by rfl⟩ : syracuseStep 1843375 = 2765063) B2765063
theorem B1843399 : Blo 1841622 1843399 := bstep (se 1 (by rfl) ⟨1382549, by rfl⟩ : syracuseStep 1843399 = 2765099) B2765099
theorem B1843419 : Blo 1841622 1843419 := bstep (se 1 (by rfl) ⟨1382564, by rfl⟩ : syracuseStep 1843419 = 2765129) B2765129
theorem B4145399 : Blo 1841622 4145399 := bstep (se 1 (by rfl) ⟨3109049, by rfl⟩ : syracuseStep 4145399 = 6218099) B6218099
theorem B1843495 : Blo 1841622 1843495 := bstep (se 1 (by rfl) ⟨1382621, by rfl⟩ : syracuseStep 1843495 = 2765243) B2765243
theorem B14934323 : Blo 1841622 14934323 := bstep (se 1 (by rfl) ⟨11200742, by rfl⟩ : syracuseStep 14934323 = 22401485) B22401485
theorem B6218045 : Blo 1841622 6218045 := bstep (se 3 (by rfl) ⟨1165883, by rfl⟩ : syracuseStep 6218045 = 2331767) B2331767
theorem B1843535 : Blo 1841622 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1843551 : Blo 1841622 1843551 := bstep (se 1 (by rfl) ⟨1382663, by rfl⟩ : syracuseStep 1843551 = 2765327) B2765327
theorem B1843579 : Blo 1841622 1843579 := bstep (se 1 (by rfl) ⟨1382684, by rfl⟩ : syracuseStep 1843579 = 2765369) B2765369
theorem B2073127 : Blo 1841622 2073127 := bstep (se 1 (by rfl) ⟨1554845, by rfl⟩ : syracuseStep 2073127 = 3109691) B3109691
theorem B6996577 : Blo 1841622 6996577 := bstep (se 2 (by rfl) ⟨2623716, by rfl⟩ : syracuseStep 6996577 = 5247433) B5247433
theorem B22413941 : Blo 1841622 22413941 := bstep (se 5 (by rfl) ⟨1050653, by rfl⟩ : syracuseStep 22413941 = 2101307) B2101307
theorem B3498707 : Blo 1841622 3498707 := bstep (se 1 (by rfl) ⟨2624030, by rfl⟩ : syracuseStep 3498707 = 5248061) B5248061
theorem B4661975 : Blo 1841622 4661975 := bstep (se 1 (by rfl) ⟨3496481, by rfl⟩ : syracuseStep 4661975 = 6992963) B6992963
theorem B4145993 : Blo 1841622 4145993 := bstep (se 2 (by rfl) ⟨1554747, by rfl⟩ : syracuseStep 4145993 = 3109495) B3109495
theorem B11805547 : Blo 1841622 11805547 := bstep (se 1 (by rfl) ⟨8854160, by rfl⟩ : syracuseStep 11805547 = 17708321) B17708321
theorem B10642283 : Blo 1841622 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B11355137 : Blo 1841622 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B6997049 : Blo 1841622 6997049 := bstep (se 2 (by rfl) ⟨2623893, by rfl⟩ : syracuseStep 6997049 = 5247787) B5247787
theorem B13280375 : Blo 1841622 13280375 := bstep (se 1 (by rfl) ⟨9960281, by rfl⟩ : syracuseStep 13280375 = 19920563) B19920563
theorem B13460633 : Blo 1841622 13460633 := bstep (se 2 (by rfl) ⟨5047737, by rfl⟩ : syracuseStep 13460633 = 10095475) B10095475
theorem B6218909 : Blo 1841622 6218909 := bstep (se 3 (by rfl) ⟨1166045, by rfl⟩ : syracuseStep 6218909 = 2332091) B2332091
theorem B3499337 : Blo 1841622 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B3327419 : Blo 1841622 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B42542603 : Blo 1841622 42542603 := bstep (se 1 (by rfl) ⟨31906952, by rfl⟩ : syracuseStep 42542603 = 63813905) B63813905
theorem B9324071 : Blo 1841622 9324071 := bstep (se 1 (by rfl) ⟨6993053, by rfl⟩ : syracuseStep 9324071 = 13986107) B13986107
theorem B4146785 : Blo 1841622 4146785 := bstep (se 2 (by rfl) ⟨1555044, by rfl⟩ : syracuseStep 4146785 = 3110089) B3110089
theorem B14935691 : Blo 1841622 14935691 := bstep (se 1 (by rfl) ⟨11201768, by rfl⟩ : syracuseStep 14935691 = 22403537) B22403537
theorem B6219449 : Blo 1841622 6219449 := bstep (se 2 (by rfl) ⟨2332293, by rfl⟩ : syracuseStep 6219449 = 4664587) B4664587
theorem B7980743 : Blo 1841622 7980743 := bstep (se 1 (by rfl) ⟨5985557, by rfl⟩ : syracuseStep 7980743 = 11971115) B11971115
theorem B2762489 : Blo 1841622 2762489 := bstep (se 2 (by rfl) ⟨1035933, by rfl⟩ : syracuseStep 2762489 = 2071867) B2071867
theorem B25224995 : Blo 1841622 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B5244745 : Blo 1841622 5244745 := bstep (se 2 (by rfl) ⟨1966779, by rfl⟩ : syracuseStep 5244745 = 3933559) B3933559
theorem B2762591 : Blo 1841622 2762591 := bstep (se 1 (by rfl) ⟨2071943, by rfl⟩ : syracuseStep 2762591 = 4143887) B4143887
theorem B2762603 : Blo 1841622 2762603 := bstep (se 1 (by rfl) ⟨2071952, by rfl⟩ : syracuseStep 2762603 = 4143905) B4143905
theorem B8857505 : Blo 1841622 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B63809461 : Blo 1841622 63809461 := bstep (se 5 (by rfl) ⟨2991068, by rfl⟩ : syracuseStep 63809461 = 5982137) B5982137
theorem B4147127 : Blo 1841622 4147127 := bstep (se 1 (by rfl) ⟨3110345, by rfl⟩ : syracuseStep 4147127 = 6220691) B6220691
theorem B7874567 : Blo 1841622 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B6998035 : Blo 1841622 6998035 := bstep (se 1 (by rfl) ⟨5248526, by rfl⟩ : syracuseStep 6998035 = 10497053) B10497053
theorem B5605433 : Blo 1841622 5605433 := bstep (se 2 (by rfl) ⟨2102037, by rfl⟩ : syracuseStep 5605433 = 4204075) B4204075
theorem B2762831 : Blo 1841622 2762831 := bstep (se 1 (by rfl) ⟨2072123, by rfl⟩ : syracuseStep 2762831 = 4144247) B4144247
theorem B2214011 : Blo 1841622 2214011 := bstep (se 1 (by rfl) ⟨1660508, by rfl⟩ : syracuseStep 2214011 = 3321017) B3321017
theorem B3934379 : Blo 1841622 3934379 := bstep (se 1 (by rfl) ⟨2950784, by rfl⟩ : syracuseStep 3934379 = 5901569) B5901569
theorem B2762951 : Blo 1841622 2762951 := bstep (se 1 (by rfl) ⟨2072213, by rfl⟩ : syracuseStep 2762951 = 4144427) B4144427
theorem B6220043 : Blo 1841622 6220043 := bstep (se 1 (by rfl) ⟨4665032, by rfl⟩ : syracuseStep 6220043 = 9330065) B9330065
theorem B23603561 : Blo 1841622 23603561 := bstep (se 2 (by rfl) ⟨8851335, by rfl⟩ : syracuseStep 23603561 = 17702671) B17702671
theorem B2763113 : Blo 1841622 2763113 := bstep (se 2 (by rfl) ⟨1036167, by rfl⟩ : syracuseStep 2763113 = 2072335) B2072335
theorem B13994369 : Blo 1841622 13994369 := bstep (se 2 (by rfl) ⟨5247888, by rfl⟩ : syracuseStep 13994369 = 10495777) B10495777
theorem B2214319 : Blo 1841622 2214319 := bstep (se 1 (by rfl) ⟨1660739, by rfl⟩ : syracuseStep 2214319 = 3321479) B3321479
theorem B2763191 : Blo 1841622 2763191 := bstep (se 1 (by rfl) ⟨2072393, by rfl⟩ : syracuseStep 2763191 = 4144787) B4144787
theorem B2763227 : Blo 1841622 2763227 := bstep (se 1 (by rfl) ⟨2072420, by rfl⟩ : syracuseStep 2763227 = 4144841) B4144841
theorem B4147721 : Blo 1841622 4147721 := bstep (se 2 (by rfl) ⟨1555395, by rfl⟩ : syracuseStep 4147721 = 3110791) B3110791
theorem B6220313 : Blo 1841622 6220313 := bstep (se 2 (by rfl) ⟨2332617, by rfl⟩ : syracuseStep 6220313 = 4665235) B4665235
theorem B1919611 : Blo 1841622 1919611 := bstep (se 1 (by rfl) ⟨1439708, by rfl⟩ : syracuseStep 1919611 = 2879417) B2879417
theorem B4426591 : Blo 1841622 4426591 := bstep (se 1 (by rfl) ⟨3319943, by rfl⟩ : syracuseStep 4426591 = 6639887) B6639887
theorem B3320671 : Blo 1841622 3320671 := bstep (se 1 (by rfl) ⟨2490503, by rfl⟩ : syracuseStep 3320671 = 4981007) B4981007
theorem B4148063 : Blo 1841622 4148063 := bstep (se 1 (by rfl) ⟨3111047, by rfl⟩ : syracuseStep 4148063 = 6222095) B6222095
theorem B2763695 : Blo 1841622 2763695 := bstep (se 1 (by rfl) ⟨2072771, by rfl⟩ : syracuseStep 2763695 = 4145543) B4145543
theorem B3107767 : Blo 1841622 3107767 := bstep (se 1 (by rfl) ⟨2330825, by rfl⟩ : syracuseStep 3107767 = 4661651) B4661651
theorem B8088503 : Blo 1841622 8088503 := bstep (se 1 (by rfl) ⟨6066377, by rfl⟩ : syracuseStep 8088503 = 12132755) B12132755
theorem B2763785 : Blo 1841622 2763785 := bstep (se 2 (by rfl) ⟨1036419, by rfl⟩ : syracuseStep 2763785 = 2072839) B2072839
theorem B2763815 : Blo 1841622 2763815 := bstep (se 1 (by rfl) ⟨2072861, by rfl⟩ : syracuseStep 2763815 = 4145723) B4145723
theorem B3107963 : Blo 1841622 3107963 := bstep (se 1 (by rfl) ⟨2330972, by rfl⟩ : syracuseStep 3107963 = 4661945) B4661945
theorem B2763899 : Blo 1841622 2763899 := bstep (se 1 (by rfl) ⟨2072924, by rfl⟩ : syracuseStep 2763899 = 4145849) B4145849
theorem B11799755 : Blo 1841622 11799755 := bstep (se 1 (by rfl) ⟨8849816, by rfl⟩ : syracuseStep 11799755 = 17699633) B17699633
theorem B4664567 : Blo 1841622 4664567 := bstep (se 1 (by rfl) ⟨3498425, by rfl⟩ : syracuseStep 4664567 = 6996851) B6996851
theorem B2764025 : Blo 1841622 2764025 := bstep (se 2 (by rfl) ⟨1036509, by rfl⟩ : syracuseStep 2764025 = 2073019) B2073019
theorem B2764127 : Blo 1841622 2764127 := bstep (se 1 (by rfl) ⟨2073095, by rfl⟩ : syracuseStep 2764127 = 4146191) B4146191
theorem B2952553 : Blo 1841622 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B2764139 : Blo 1841622 2764139 := bstep (se 1 (by rfl) ⟨2073104, by rfl⟩ : syracuseStep 2764139 = 4146209) B4146209
theorem B10235261 : Blo 1841622 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B2624987 : Blo 1841622 2624987 := bstep (se 1 (by rfl) ⟨1968740, by rfl⟩ : syracuseStep 2624987 = 3937481) B3937481
theorem B119557619 : Blo 1841622 119557619 := bstep (se 1 (by rfl) ⟨89668214, by rfl⟩ : syracuseStep 119557619 = 179336429) B179336429
theorem B3108361 : Blo 1841622 3108361 := bstep (se 2 (by rfl) ⟨1165635, by rfl⟩ : syracuseStep 3108361 = 2331271) B2331271
theorem B5983753 : Blo 1841622 5983753 := bstep (se 2 (by rfl) ⟨2243907, by rfl⟩ : syracuseStep 5983753 = 4487815) B4487815
theorem B2764367 : Blo 1841622 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B9326177 : Blo 1841622 9326177 := bstep (se 2 (by rfl) ⟨3497316, by rfl⟩ : syracuseStep 9326177 = 6994633) B6994633
theorem B6221447 : Blo 1841622 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B5246603 : Blo 1841622 5246603 := bstep (se 1 (by rfl) ⟨3934952, by rfl⟩ : syracuseStep 5246603 = 7869905) B7869905
theorem B3108523 : Blo 1841622 3108523 := bstep (se 1 (by rfl) ⟨2331392, by rfl⟩ : syracuseStep 3108523 = 4662785) B4662785
theorem B39841469 : Blo 1841622 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B6221501 : Blo 1841622 6221501 := bstep (se 3 (by rfl) ⟨1166531, by rfl⟩ : syracuseStep 6221501 = 2333063) B2333063
theorem B2764487 : Blo 1841622 2764487 := bstep (se 1 (by rfl) ⟨2073365, by rfl⟩ : syracuseStep 2764487 = 4146731) B4146731
theorem B6999767 : Blo 1841622 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B15748829 : Blo 1841622 15748829 := bstep (se 3 (by rfl) ⟨2952905, by rfl⟩ : syracuseStep 15748829 = 5905811) B5905811
theorem B13987565 : Blo 1841622 13987565 := bstep (se 3 (by rfl) ⟨2622668, by rfl⟩ : syracuseStep 13987565 = 5245337) B5245337
theorem B3321695 : Blo 1841622 3321695 := bstep (se 1 (by rfl) ⟨2491271, by rfl⟩ : syracuseStep 3321695 = 4982543) B4982543
theorem B6221663 : Blo 1841622 6221663 := bstep (se 1 (by rfl) ⟨4666247, by rfl⟩ : syracuseStep 6221663 = 9332495) B9332495
theorem B2764649 : Blo 1841622 2764649 := bstep (se 2 (by rfl) ⟨1036743, by rfl⟩ : syracuseStep 2764649 = 2073487) B2073487
theorem B6303595 : Blo 1841622 6303595 := bstep (se 1 (by rfl) ⟨4727696, by rfl⟩ : syracuseStep 6303595 = 9455393) B9455393
theorem B7868279 : Blo 1841622 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B2764727 : Blo 1841622 2764727 := bstep (se 1 (by rfl) ⟨2073545, by rfl⟩ : syracuseStep 2764727 = 4147091) B4147091
theorem B3108827 : Blo 1841622 3108827 := bstep (se 1 (by rfl) ⟨2331620, by rfl⟩ : syracuseStep 3108827 = 4663241) B4663241
theorem B2764763 : Blo 1841622 2764763 := bstep (se 1 (by rfl) ⟨2073572, by rfl⟩ : syracuseStep 2764763 = 4147145) B4147145
theorem B6221825 : Blo 1841622 6221825 := bstep (se 2 (by rfl) ⟨2333184, by rfl⟩ : syracuseStep 6221825 = 4666369) B4666369
theorem B25554955 : Blo 1841622 25554955 := bstep (se 1 (by rfl) ⟨19166216, by rfl⟩ : syracuseStep 25554955 = 38332433) B38332433
theorem B5754959 : Blo 1841622 5754959 := bstep (se 1 (by rfl) ⟨4316219, by rfl⟩ : syracuseStep 5754959 = 8632439) B8632439
theorem B10489945 : Blo 1841622 10489945 := bstep (se 2 (by rfl) ⟨3933729, by rfl⟩ : syracuseStep 10489945 = 7867459) B7867459
theorem B35426483 : Blo 1841622 35426483 := bstep (se 1 (by rfl) ⟨26569862, by rfl⟩ : syracuseStep 35426483 = 53139725) B53139725
theorem B3109063 : Blo 1841622 3109063 := bstep (se 1 (by rfl) ⟨2331797, by rfl⟩ : syracuseStep 3109063 = 4663595) B4663595
theorem B3109225 : Blo 1841622 3109225 := bstep (se 2 (by rfl) ⟨1165959, by rfl⟩ : syracuseStep 3109225 = 2331919) B2331919
theorem B11800961 : Blo 1841622 11800961 := bstep (se 2 (by rfl) ⟨4425360, by rfl⟩ : syracuseStep 11800961 = 8850721) B8850721
theorem B6640015 : Blo 1841622 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B2765231 : Blo 1841622 2765231 := bstep (se 1 (by rfl) ⟨2073923, by rfl⟩ : syracuseStep 2765231 = 4147847) B4147847
theorem B2765321 : Blo 1841622 2765321 := bstep (se 2 (by rfl) ⟨1036995, by rfl⟩ : syracuseStep 2765321 = 2073991) B2073991
theorem B2331175 : Blo 1841622 2331175 := bstep (se 1 (by rfl) ⟨1748381, by rfl⟩ : syracuseStep 2331175 = 3496763) B3496763
theorem B2765351 : Blo 1841622 2765351 := bstep (se 1 (by rfl) ⟨2074013, by rfl⟩ : syracuseStep 2765351 = 4148027) B4148027
theorem B6992507 : Blo 1841622 6992507 := bstep (se 1 (by rfl) ⟨5244380, by rfl⟩ : syracuseStep 6992507 = 10488761) B10488761
theorem B4665995 : Blo 1841622 4665995 := bstep (se 1 (by rfl) ⟨3499496, by rfl⟩ : syracuseStep 4665995 = 6998993) B6998993
theorem B13988537 : Blo 1841622 13988537 := bstep (se 2 (by rfl) ⟨5245701, by rfl⟩ : syracuseStep 13988537 = 10491403) B10491403
theorem B45429457 : Blo 1841622 45429457 := bstep (se 2 (by rfl) ⟨17036046, by rfl⟩ : syracuseStep 45429457 = 34072093) B34072093
theorem B4666207 : Blo 1841622 4666207 := bstep (se 1 (by rfl) ⟨3499655, by rfl⟩ : syracuseStep 4666207 = 6999311) B6999311
theorem B2331499 : Blo 1841622 2331499 := bstep (se 1 (by rfl) ⟨1748624, by rfl⟩ : syracuseStep 2331499 = 3497249) B3497249
theorem B3109819 : Blo 1841622 3109819 := bstep (se 1 (by rfl) ⟨2332364, by rfl⟩ : syracuseStep 3109819 = 4664729) B4664729
theorem B9327635 : Blo 1841622 9327635 := bstep (se 1 (by rfl) ⟨6995726, by rfl⟩ : syracuseStep 9327635 = 13991453) B13991453
theorem B3109927 : Blo 1841622 3109927 := bstep (se 1 (by rfl) ⟨2332445, by rfl⟩ : syracuseStep 3109927 = 4664891) B4664891
theorem B6640811 : Blo 1841622 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B3110251 : Blo 1841622 3110251 := bstep (se 1 (by rfl) ⟨2332688, by rfl⟩ : syracuseStep 3110251 = 4665377) B4665377
theorem B10638793 : Blo 1841622 10638793 := bstep (se 2 (by rfl) ⟨3989547, by rfl⟩ : syracuseStep 10638793 = 7979095) B7979095
theorem B13465075 : Blo 1841622 13465075 := bstep (se 1 (by rfl) ⟨10098806, by rfl⟩ : syracuseStep 13465075 = 20197613) B20197613
theorem B13989509 : Blo 1841622 13989509 := bstep (se 4 (by rfl) ⟨1311516, by rfl⟩ : syracuseStep 13989509 = 2623033) B2623033
theorem B11810519 : Blo 1841622 11810519 := bstep (se 1 (by rfl) ⟨8857889, by rfl⟩ : syracuseStep 11810519 = 17715779) B17715779
theorem B14948077 : Blo 1841622 14948077 := bstep (se 3 (by rfl) ⟨2802764, by rfl⟩ : syracuseStep 14948077 = 5605529) B5605529
theorem B4429675 : Blo 1841622 4429675 := bstep (se 1 (by rfl) ⟨3322256, by rfl⟩ : syracuseStep 4429675 = 6644513) B6644513
theorem B6993935 : Blo 1841622 6993935 := bstep (se 1 (by rfl) ⟨5245451, by rfl⟩ : syracuseStep 6993935 = 10490903) B10490903
theorem B2332795 : Blo 1841622 2332795 := bstep (se 1 (by rfl) ⟨1749596, by rfl⟩ : syracuseStep 2332795 = 3499193) B3499193
theorem B31922465 : Blo 1841622 31922465 := bstep (se 2 (by rfl) ⟨11970924, by rfl⟩ : syracuseStep 31922465 = 23941849) B23941849
theorem B3496375 : Blo 1841622 3496375 := bstep (se 1 (by rfl) ⟨2622281, by rfl⟩ : syracuseStep 3496375 = 5244563) B5244563
theorem B15350219 : Blo 1841622 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1841627 : Blo 1841622 1841627 := bstep (se 1 (by rfl) ⟨1381220, by rfl⟩ : syracuseStep 1841627 = 2762441) B2762441
theorem B6216155 : Blo 1841622 6216155 := bstep (se 1 (by rfl) ⟨4662116, by rfl⟩ : syracuseStep 6216155 = 9324233) B9324233
theorem B15735329 : Blo 1841622 15735329 := bstep (se 2 (by rfl) ⟨5900748, by rfl⟩ : syracuseStep 15735329 = 11801497) B11801497
theorem B1841703 : Blo 1841622 1841703 := bstep (se 1 (by rfl) ⟨1381277, by rfl⟩ : syracuseStep 1841703 = 2762555) B2762555
theorem B1841743 : Blo 1841622 1841743 := bstep (se 1 (by rfl) ⟨1381307, by rfl⟩ : syracuseStep 1841743 = 2762615) B2762615
theorem B1841759 : Blo 1841622 1841759 := bstep (se 1 (by rfl) ⟨1381319, by rfl⟩ : syracuseStep 1841759 = 2762639) B2762639
theorem B1841787 : Blo 1841622 1841787 := bstep (se 1 (by rfl) ⟨1381340, by rfl⟩ : syracuseStep 1841787 = 2762681) B2762681
theorem B6306443 : Blo 1841622 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B6642323 : Blo 1841622 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B1841839 : Blo 1841622 1841839 := bstep (se 1 (by rfl) ⟨1381379, by rfl⟩ : syracuseStep 1841839 = 2762759) B2762759
theorem B4143815 : Blo 1841622 4143815 := bstep (se 1 (by rfl) ⟨3107861, by rfl⟩ : syracuseStep 4143815 = 6215723) B6215723
theorem B1841863 : Blo 1841622 1841863 := bstep (se 1 (by rfl) ⟨1381397, by rfl⟩ : syracuseStep 1841863 = 2762795) B2762795
theorem B5249735 : Blo 1841622 5249735 := bstep (se 1 (by rfl) ⟨3937301, by rfl⟩ : syracuseStep 5249735 = 7874603) B7874603
theorem B1841883 : Blo 1841622 1841883 := bstep (se 1 (by rfl) ⟨1381412, by rfl⟩ : syracuseStep 1841883 = 2762825) B2762825
theorem B6642425 : Blo 1841622 6642425 := bstep (se 2 (by rfl) ⟨2490909, by rfl⟩ : syracuseStep 6642425 = 4981819) B4981819
theorem B11803421 : Blo 1841622 11803421 := bstep (se 3 (by rfl) ⟨2213141, by rfl⟩ : syracuseStep 11803421 = 4426283) B4426283
theorem B1841959 : Blo 1841622 1841959 := bstep (se 1 (by rfl) ⟨1381469, by rfl⟩ : syracuseStep 1841959 = 2762939) B2762939
theorem B1841999 : Blo 1841622 1841999 := bstep (se 1 (by rfl) ⟨1381499, by rfl⟩ : syracuseStep 1841999 = 2762999) B2762999
theorem B1842015 : Blo 1841622 1842015 := bstep (se 1 (by rfl) ⟨1381511, by rfl⟩ : syracuseStep 1842015 = 2763023) B2763023
theorem B1842043 : Blo 1841622 1842043 := bstep (se 1 (by rfl) ⟨1381532, by rfl⟩ : syracuseStep 1842043 = 2763065) B2763065
theorem B1842095 : Blo 1841622 1842095 := bstep (se 1 (by rfl) ⟨1381571, by rfl⟩ : syracuseStep 1842095 = 2763143) B2763143
theorem B22404023 : Blo 1841622 22404023 := bstep (se 1 (by rfl) ⟨16803017, by rfl⟩ : syracuseStep 22404023 = 33606035) B33606035
theorem B1842119 : Blo 1841622 1842119 := bstep (se 1 (by rfl) ⟨1381589, by rfl⟩ : syracuseStep 1842119 = 2763179) B2763179
theorem B1842139 : Blo 1841622 1842139 := bstep (se 1 (by rfl) ⟨1381604, by rfl⟩ : syracuseStep 1842139 = 2763209) B2763209
theorem B1842215 : Blo 1841622 1842215 := bstep (se 1 (by rfl) ⟨1381661, by rfl⟩ : syracuseStep 1842215 = 2763323) B2763323
theorem B1842255 : Blo 1841622 1842255 := bstep (se 1 (by rfl) ⟨1381691, by rfl⟩ : syracuseStep 1842255 = 2763383) B2763383
theorem B1842271 : Blo 1841622 1842271 := bstep (se 1 (by rfl) ⟨1381703, by rfl⟩ : syracuseStep 1842271 = 2763407) B2763407
theorem B1842299 : Blo 1841622 1842299 := bstep (se 1 (by rfl) ⟨1381724, by rfl⟩ : syracuseStep 1842299 = 2763449) B2763449
theorem B6216857 : Blo 1841622 6216857 := bstep (se 2 (by rfl) ⟨2331321, by rfl⟩ : syracuseStep 6216857 = 4662643) B4662643
theorem B1842351 : Blo 1841622 1842351 := bstep (se 1 (by rfl) ⟨1381763, by rfl⟩ : syracuseStep 1842351 = 2763527) B2763527
theorem B1842375 : Blo 1841622 1842375 := bstep (se 1 (by rfl) ⟨1381781, by rfl⟩ : syracuseStep 1842375 = 2763563) B2763563
theorem B1842395 : Blo 1841622 1842395 := bstep (se 1 (by rfl) ⟨1381796, by rfl⟩ : syracuseStep 1842395 = 2763593) B2763593
theorem B22420759 : Blo 1841622 22420759 := bstep (se 1 (by rfl) ⟨16815569, by rfl⟩ : syracuseStep 22420759 = 33631139) B33631139
theorem B1842471 : Blo 1841622 1842471 := bstep (se 1 (by rfl) ⟨1381853, by rfl⟩ : syracuseStep 1842471 = 2763707) B2763707
theorem B13286693 : Blo 1841622 13286693 := bstep (se 4 (by rfl) ⟨1245627, by rfl⟩ : syracuseStep 13286693 = 2491255) B2491255
theorem B1842511 : Blo 1841622 1842511 := bstep (se 1 (by rfl) ⟨1381883, by rfl⟩ : syracuseStep 1842511 = 2763767) B2763767
theorem B2071903 : Blo 1841622 2071903 := bstep (se 1 (by rfl) ⟨1553927, by rfl⟩ : syracuseStep 2071903 = 3107855) B3107855
theorem B1842527 : Blo 1841622 1842527 := bstep (se 1 (by rfl) ⟨1381895, by rfl⟩ : syracuseStep 1842527 = 2763791) B2763791
theorem B1842555 : Blo 1841622 1842555 := bstep (se 1 (by rfl) ⟨1381916, by rfl⟩ : syracuseStep 1842555 = 2763833) B2763833
theorem B1842607 : Blo 1841622 1842607 := bstep (se 1 (by rfl) ⟨1381955, by rfl⟩ : syracuseStep 1842607 = 2763911) B2763911
theorem B1842631 : Blo 1841622 1842631 := bstep (se 1 (by rfl) ⟨1381973, by rfl⟩ : syracuseStep 1842631 = 2763947) B2763947
theorem B1842651 : Blo 1841622 1842651 := bstep (se 1 (by rfl) ⟨1381988, by rfl⟩ : syracuseStep 1842651 = 2763977) B2763977
theorem B8855027 : Blo 1841622 8855027 := bstep (se 1 (by rfl) ⟨6641270, by rfl⟩ : syracuseStep 8855027 = 13282541) B13282541
theorem B4144679 : Blo 1841622 4144679 := bstep (se 1 (by rfl) ⟨3108509, by rfl⟩ : syracuseStep 4144679 = 6217019) B6217019
theorem B9453095 : Blo 1841622 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B1842727 : Blo 1841622 1842727 := bstep (se 1 (by rfl) ⟨1382045, by rfl⟩ : syracuseStep 1842727 = 2764091) B2764091
theorem B1842767 : Blo 1841622 1842767 := bstep (se 1 (by rfl) ⟨1382075, by rfl⟩ : syracuseStep 1842767 = 2764151) B2764151
theorem B1842783 : Blo 1841622 1842783 := bstep (se 1 (by rfl) ⟨1382087, by rfl⟩ : syracuseStep 1842783 = 2764175) B2764175
theorem B1842811 : Blo 1841622 1842811 := bstep (se 1 (by rfl) ⟨1382108, by rfl⟩ : syracuseStep 1842811 = 2764217) B2764217
theorem B6995591 : Blo 1841622 6995591 := bstep (se 1 (by rfl) ⟨5246693, by rfl⟩ : syracuseStep 6995591 = 10493387) B10493387
theorem B1842863 : Blo 1841622 1842863 := bstep (se 1 (by rfl) ⟨1382147, by rfl⟩ : syracuseStep 1842863 = 2764295) B2764295
theorem B2072263 : Blo 1841622 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B1842887 : Blo 1841622 1842887 := bstep (se 1 (by rfl) ⟨1382165, by rfl⟩ : syracuseStep 1842887 = 2764331) B2764331
theorem B1842907 : Blo 1841622 1842907 := bstep (se 1 (by rfl) ⟨1382180, by rfl⟩ : syracuseStep 1842907 = 2764361) B2764361
theorem B53133029 : Blo 1841622 53133029 := bstep (se 4 (by rfl) ⟨4981221, by rfl⟩ : syracuseStep 53133029 = 9962443) B9962443
theorem B1842983 : Blo 1841622 1842983 := bstep (se 1 (by rfl) ⟨1382237, by rfl⟩ : syracuseStep 1842983 = 2764475) B2764475
theorem B1843023 : Blo 1841622 1843023 := bstep (se 1 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 1843023 = 2764535) B2764535
theorem B1843039 : Blo 1841622 1843039 := bstep (se 1 (by rfl) ⟨1382279, by rfl⟩ : syracuseStep 1843039 = 2764559) B2764559
theorem B3497833 : Blo 1841622 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B4145003 : Blo 1841622 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B9330551 : Blo 1841622 9330551 := bstep (se 1 (by rfl) ⟨6997913, by rfl⟩ : syracuseStep 9330551 = 13995827) B13995827
theorem B1843067 : Blo 1841622 1843067 := bstep (se 1 (by rfl) ⟨1382300, by rfl⟩ : syracuseStep 1843067 = 2764601) B2764601
theorem B22404995 : Blo 1841622 22404995 := bstep (se 1 (by rfl) ⟨16803746, by rfl⟩ : syracuseStep 22404995 = 33607493) B33607493
theorem B4145057 : Blo 1841622 4145057 := bstep (se 2 (by rfl) ⟨1554396, by rfl⟩ : syracuseStep 4145057 = 3108793) B3108793
theorem B1843119 : Blo 1841622 1843119 := bstep (se 1 (by rfl) ⟨1382339, by rfl⟩ : syracuseStep 1843119 = 2764679) B2764679
theorem B1843143 : Blo 1841622 1843143 := bstep (se 1 (by rfl) ⟨1382357, by rfl⟩ : syracuseStep 1843143 = 2764715) B2764715
theorem B1843163 : Blo 1841622 1843163 := bstep (se 1 (by rfl) ⟨1382372, by rfl⟩ : syracuseStep 1843163 = 2764745) B2764745
theorem B9330713 : Blo 1841622 9330713 := bstep (se 2 (by rfl) ⟨3499017, by rfl⟩ : syracuseStep 9330713 = 6998035) B6998035
theorem B23617655 : Blo 1841622 23617655 := bstep (se 1 (by rfl) ⟨17713241, by rfl⟩ : syracuseStep 23617655 = 35426483) B35426483
theorem B4145363 : Blo 1841622 4145363 := bstep (se 1 (by rfl) ⟨3109022, by rfl⟩ : syracuseStep 4145363 = 6218045) B6218045
theorem B4145417 : Blo 1841622 4145417 := bstep (se 2 (by rfl) ⟨1554531, by rfl⟩ : syracuseStep 4145417 = 3109063) B3109063
theorem B1843487 : Blo 1841622 1843487 := bstep (se 1 (by rfl) ⟨1382615, by rfl⟩ : syracuseStep 1843487 = 2765231) B2765231
theorem B35414333 : Blo 1841622 35414333 := bstep (se 3 (by rfl) ⟨6640187, by rfl⟩ : syracuseStep 35414333 = 13280375) B13280375
theorem B1843547 : Blo 1841622 1843547 := bstep (se 1 (by rfl) ⟨1382660, by rfl⟩ : syracuseStep 1843547 = 2765321) B2765321
theorem B1843567 : Blo 1841622 1843567 := bstep (se 1 (by rfl) ⟨1382675, by rfl⟩ : syracuseStep 1843567 = 2765351) B2765351
theorem B14942627 : Blo 1841622 14942627 := bstep (se 1 (by rfl) ⟨11206970, by rfl⟩ : syracuseStep 14942627 = 22413941) B22413941
theorem B4661671 : Blo 1841622 4661671 := bstep (se 1 (by rfl) ⟨3496253, by rfl⟩ : syracuseStep 4661671 = 6992507) B6992507
theorem B4145633 : Blo 1841622 4145633 := bstep (se 2 (by rfl) ⟨1554612, by rfl⟩ : syracuseStep 4145633 = 3109225) B3109225
theorem B7094855 : Blo 1841622 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B4661833 : Blo 1841622 4661833 := bstep (se 2 (by rfl) ⟨1748187, by rfl⟩ : syracuseStep 4661833 = 3496375) B3496375
theorem B7570091 : Blo 1841622 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B6218423 : Blo 1841622 6218423 := bstep (se 1 (by rfl) ⟨4663817, by rfl⟩ : syracuseStep 6218423 = 9327635) B9327635
theorem B4145939 : Blo 1841622 4145939 := bstep (se 1 (by rfl) ⟨3109454, by rfl⟩ : syracuseStep 4145939 = 6218909) B6218909
theorem B60572609 : Blo 1841622 60572609 := bstep (se 2 (by rfl) ⟨22714728, by rfl⟩ : syracuseStep 60572609 = 45429457) B45429457
theorem B28361735 : Blo 1841622 28361735 := bstep (se 1 (by rfl) ⟨21271301, by rfl⟩ : syracuseStep 28361735 = 42542603) B42542603
theorem B4146299 : Blo 1841622 4146299 := bstep (se 1 (by rfl) ⟨3109724, by rfl⟩ : syracuseStep 4146299 = 6219449) B6219449
theorem B7873679 : Blo 1841622 7873679 := bstep (se 1 (by rfl) ⟨5905259, by rfl⟩ : syracuseStep 7873679 = 11810519) B11810519
theorem B4146425 : Blo 1841622 4146425 := bstep (se 2 (by rfl) ⟨1554909, by rfl⟩ : syracuseStep 4146425 = 3109819) B3109819
theorem B4662623 : Blo 1841622 4662623 := bstep (se 1 (by rfl) ⟨3496967, by rfl⟩ : syracuseStep 4662623 = 6993935) B6993935
theorem B3736955 : Blo 1841622 3736955 := bstep (se 1 (by rfl) ⟨2802716, by rfl⟩ : syracuseStep 3736955 = 5605433) B5605433
theorem B4146569 : Blo 1841622 4146569 := bstep (se 2 (by rfl) ⟨1554963, by rfl⟩ : syracuseStep 4146569 = 3109927) B3109927
theorem B4146695 : Blo 1841622 4146695 := bstep (se 1 (by rfl) ⟨3110021, by rfl⟩ : syracuseStep 4146695 = 6220043) B6220043
theorem B10233479 : Blo 1841622 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B4146875 : Blo 1841622 4146875 := bstep (se 1 (by rfl) ⟨3110156, by rfl⟩ : syracuseStep 4146875 = 6220313) B6220313
theorem B29894345 : Blo 1841622 29894345 := bstep (se 2 (by rfl) ⟨11210379, by rfl⟩ : syracuseStep 29894345 = 22420759) B22420759
theorem B4204295 : Blo 1841622 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2762537 : Blo 1841622 2762537 := bstep (se 2 (by rfl) ⟨1035951, by rfl⟩ : syracuseStep 2762537 = 2071903) B2071903
theorem B2762543 : Blo 1841622 2762543 := bstep (se 1 (by rfl) ⟨2071907, by rfl⟩ : syracuseStep 2762543 = 4143815) B4143815
theorem B3499823 : Blo 1841622 3499823 := bstep (se 1 (by rfl) ⟨2624867, by rfl⟩ : syracuseStep 3499823 = 5249735) B5249735
theorem B4147001 : Blo 1841622 4147001 := bstep (se 2 (by rfl) ⟨1555125, by rfl⟩ : syracuseStep 4147001 = 3110251) B3110251
theorem B14936015 : Blo 1841622 14936015 := bstep (se 1 (by rfl) ⟨11202011, by rfl⟩ : syracuseStep 14936015 = 22404023) B22404023
theorem B7866503 : Blo 1841622 7866503 := bstep (se 1 (by rfl) ⟨5899877, by rfl⟩ : syracuseStep 7866503 = 11799755) B11799755
theorem B8857795 : Blo 1841622 8857795 := bstep (se 1 (by rfl) ⟨6643346, by rfl⟩ : syracuseStep 8857795 = 13286693) B13286693
theorem B2763017 : Blo 1841622 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B20982077 : Blo 1841622 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B2763119 : Blo 1841622 2763119 := bstep (se 1 (by rfl) ⟨2072339, by rfl⟩ : syracuseStep 2763119 = 4144679) B4144679
theorem B6302063 : Blo 1841622 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B4663727 : Blo 1841622 4663727 := bstep (se 1 (by rfl) ⟨3497795, by rfl⟩ : syracuseStep 4663727 = 6995591) B6995591
theorem B4147631 : Blo 1841622 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B26560979 : Blo 1841622 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B4147667 : Blo 1841622 4147667 := bstep (se 1 (by rfl) ⟨3110750, by rfl⟩ : syracuseStep 4147667 = 6221501) B6221501
theorem B4663777 : Blo 1841622 4663777 := bstep (se 2 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 4663777 = 3497833) B3497833
theorem B9325043 : Blo 1841622 9325043 := bstep (se 1 (by rfl) ⟨6993782, by rfl⟩ : syracuseStep 9325043 = 13987565) B13987565
theorem B2214463 : Blo 1841622 2214463 := bstep (se 1 (by rfl) ⟨1660847, by rfl⟩ : syracuseStep 2214463 = 3321695) B3321695
theorem B4147775 : Blo 1841622 4147775 := bstep (se 1 (by rfl) ⟨3110831, by rfl⟩ : syracuseStep 4147775 = 6221663) B6221663
theorem B2763335 : Blo 1841622 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B6220367 : Blo 1841622 6220367 := bstep (se 1 (by rfl) ⟨4665275, by rfl⟩ : syracuseStep 6220367 = 9330551) B9330551
theorem B14936663 : Blo 1841622 14936663 := bstep (se 1 (by rfl) ⟨11202497, by rfl⟩ : syracuseStep 14936663 = 22404995) B22404995
theorem B2763371 : Blo 1841622 2763371 := bstep (se 1 (by rfl) ⟨2072528, by rfl⟩ : syracuseStep 2763371 = 4145057) B4145057
theorem B4147883 : Blo 1841622 4147883 := bstep (se 1 (by rfl) ⟨3110912, by rfl⟩ : syracuseStep 4147883 = 6221825) B6221825
theorem B34073273 : Blo 1841622 34073273 := bstep (se 2 (by rfl) ⟨12777477, by rfl⟩ : syracuseStep 34073273 = 25554955) B25554955
theorem B3836639 : Blo 1841622 3836639 := bstep (se 1 (by rfl) ⟨2877479, by rfl⟩ : syracuseStep 3836639 = 5754959) B5754959
theorem B13986593 : Blo 1841622 13986593 := bstep (se 2 (by rfl) ⟨5244972, by rfl⟩ : syracuseStep 13986593 = 10489945) B10489945
theorem B2763599 : Blo 1841622 2763599 := bstep (se 1 (by rfl) ⟨2072699, by rfl⟩ : syracuseStep 2763599 = 4145399) B4145399
theorem B9956215 : Blo 1841622 9956215 := bstep (se 1 (by rfl) ⟨7467161, by rfl⟩ : syracuseStep 9956215 = 14934323) B14934323
theorem B7867307 : Blo 1841622 7867307 := bstep (se 1 (by rfl) ⟨5900480, by rfl⟩ : syracuseStep 7867307 = 11800961) B11800961
theorem B9325691 : Blo 1841622 9325691 := bstep (se 1 (by rfl) ⟨6994268, by rfl⟩ : syracuseStep 9325691 = 13988537) B13988537
theorem B3107983 : Blo 1841622 3107983 := bstep (se 1 (by rfl) ⟨2330987, by rfl⟩ : syracuseStep 3107983 = 4661975) B4661975
theorem B2763995 : Blo 1841622 2763995 := bstep (se 1 (by rfl) ⟨2072996, by rfl⟩ : syracuseStep 2763995 = 4145993) B4145993
theorem B2952425 : Blo 1841622 2952425 := bstep (se 2 (by rfl) ⟨1107159, by rfl⟩ : syracuseStep 2952425 = 2214319) B2214319
theorem B4664699 : Blo 1841622 4664699 := bstep (se 1 (by rfl) ⟨3498524, by rfl⟩ : syracuseStep 4664699 = 6997049) B6997049
theorem B3108233 : Blo 1841622 3108233 := bstep (se 2 (by rfl) ⟨1165587, by rfl⟩ : syracuseStep 3108233 = 2331175) B2331175
theorem B2764169 : Blo 1841622 2764169 := bstep (se 2 (by rfl) ⟨1036563, by rfl⟩ : syracuseStep 2764169 = 2073127) B2073127
theorem B85126573 : Blo 1841622 85126573 := bstep (se 3 (by rfl) ⟨15961232, by rfl⟩ : syracuseStep 85126573 = 31922465) B31922465
theorem B8973755 : Blo 1841622 8973755 := bstep (se 1 (by rfl) ⟨6730316, by rfl⟩ : syracuseStep 8973755 = 13460633) B13460633
theorem B4427207 : Blo 1841622 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B2559481 : Blo 1841622 2559481 := bstep (se 2 (by rfl) ⟨959805, by rfl⟩ : syracuseStep 2559481 = 1919611) B1919611
theorem B2764523 : Blo 1841622 2764523 := bstep (se 1 (by rfl) ⟨2073392, by rfl⟩ : syracuseStep 2764523 = 4146785) B4146785
theorem B9326339 : Blo 1841622 9326339 := bstep (se 1 (by rfl) ⟨6994754, by rfl⟩ : syracuseStep 9326339 = 13989509) B13989509
theorem B9957127 : Blo 1841622 9957127 := bstep (se 1 (by rfl) ⟨7467845, by rfl⟩ : syracuseStep 9957127 = 14935691) B14935691
theorem B5902121 : Blo 1841622 5902121 := bstep (se 2 (by rfl) ⟨2213295, by rfl⟩ : syracuseStep 5902121 = 4426591) B4426591
theorem B4427561 : Blo 1841622 4427561 := bstep (se 2 (by rfl) ⟨1660335, by rfl⟩ : syracuseStep 4427561 = 3320671) B3320671
theorem B6221609 : Blo 1841622 6221609 := bstep (se 2 (by rfl) ⟨2333103, by rfl⟩ : syracuseStep 6221609 = 4666207) B4666207
theorem B5320495 : Blo 1841622 5320495 := bstep (se 1 (by rfl) ⟨3990371, by rfl⟩ : syracuseStep 5320495 = 7980743) B7980743
theorem B3108665 : Blo 1841622 3108665 := bstep (se 2 (by rfl) ⟨1165749, by rfl⟩ : syracuseStep 3108665 = 2331499) B2331499
theorem B15740729 : Blo 1841622 15740729 := bstep (se 2 (by rfl) ⟨5902773, by rfl⟩ : syracuseStep 15740729 = 11805547) B11805547
theorem B6999965 : Blo 1841622 6999965 := bstep (se 3 (by rfl) ⟨1312493, by rfl⟩ : syracuseStep 6999965 = 2624987) B2624987
theorem B2764751 : Blo 1841622 2764751 := bstep (se 1 (by rfl) ⟨2073563, by rfl⟩ : syracuseStep 2764751 = 4147127) B4147127
theorem B2765147 : Blo 1841622 2765147 := bstep (se 1 (by rfl) ⟨2073860, by rfl⟩ : syracuseStep 2765147 = 4147721) B4147721
theorem B10490219 : Blo 1841622 10490219 := bstep (se 1 (by rfl) ⟨7867664, by rfl⟩ : syracuseStep 10490219 = 15735329) B15735329
theorem B4428215 : Blo 1841622 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B3936737 : Blo 1841622 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B4428283 : Blo 1841622 4428283 := bstep (se 1 (by rfl) ⟨3321212, by rfl⟩ : syracuseStep 4428283 = 6642425) B6642425
theorem B7868947 : Blo 1841622 7868947 := bstep (se 1 (by rfl) ⟨5901710, by rfl⟩ : syracuseStep 7868947 = 11803421) B11803421
theorem B2765375 : Blo 1841622 2765375 := bstep (se 1 (by rfl) ⟨2074031, by rfl⟩ : syracuseStep 2765375 = 4148063) B4148063
theorem B14185057 : Blo 1841622 14185057 := bstep (se 2 (by rfl) ⟨5319396, by rfl⟩ : syracuseStep 14185057 = 10638793) B10638793
theorem B17953433 : Blo 1841622 17953433 := bstep (se 2 (by rfl) ⟨6732537, by rfl⟩ : syracuseStep 17953433 = 13465075) B13465075
theorem B3109711 : Blo 1841622 3109711 := bstep (se 1 (by rfl) ⟨2332283, by rfl⟩ : syracuseStep 3109711 = 4664567) B4664567
theorem B340317125 : Blo 1841622 340317125 := bstep (se 4 (by rfl) ⟨31904730, by rfl⟩ : syracuseStep 340317125 = 63809461) B63809461
theorem B5903351 : Blo 1841622 5903351 := bstep (se 1 (by rfl) ⟨4427513, by rfl⟩ : syracuseStep 5903351 = 8855027) B8855027
theorem B79705079 : Blo 1841622 79705079 := bstep (se 1 (by rfl) ⟨59778809, by rfl⟩ : syracuseStep 79705079 = 119557619) B119557619
theorem B6992993 : Blo 1841622 6992993 := bstep (se 2 (by rfl) ⟨2622372, by rfl⟩ : syracuseStep 6992993 = 5244745) B5244745
theorem B4666511 : Blo 1841622 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B10499219 : Blo 1841622 10499219 := bstep (se 1 (by rfl) ⟨7874414, by rfl⟩ : syracuseStep 10499219 = 15748829) B15748829
theorem B9327959 : Blo 1841622 9327959 := bstep (se 1 (by rfl) ⟨6995969, by rfl⟩ : syracuseStep 9327959 = 13991939) B13991939
theorem B3110393 : Blo 1841622 3110393 := bstep (se 2 (by rfl) ⟨1166397, by rfl⟩ : syracuseStep 3110393 = 2332795) B2332795
theorem B5904029 : Blo 1841622 5904029 := bstep (se 3 (by rfl) ⟨1107005, by rfl⟩ : syracuseStep 5904029 = 2214011) B2214011
theorem B3110663 : Blo 1841622 3110663 := bstep (se 1 (by rfl) ⟨2332997, by rfl⟩ : syracuseStep 3110663 = 4665995) B4665995
theorem B10491677 : Blo 1841622 10491677 := bstep (se 3 (by rfl) ⟨1967189, by rfl⟩ : syracuseStep 10491677 = 3934379) B3934379
theorem B2332471 : Blo 1841622 2332471 := bstep (se 1 (by rfl) ⟨1749353, by rfl⟩ : syracuseStep 2332471 = 3498707) B3498707
theorem B8853353 : Blo 1841622 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B9328769 : Blo 1841622 9328769 := bstep (se 2 (by rfl) ⟨3498288, by rfl⟩ : syracuseStep 9328769 = 6996577) B6996577
theorem B2332891 : Blo 1841622 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B2218279 : Blo 1841622 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B6216047 : Blo 1841622 6216047 := bstep (se 1 (by rfl) ⟨4662035, by rfl⟩ : syracuseStep 6216047 = 9324071) B9324071
theorem B1841659 : Blo 1841622 1841659 := bstep (se 1 (by rfl) ⟨1381244, by rfl⟩ : syracuseStep 1841659 = 2762489) B2762489
theorem B16816663 : Blo 1841622 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B1841727 : Blo 1841622 1841727 := bstep (se 1 (by rfl) ⟨1381295, by rfl⟩ : syracuseStep 1841727 = 2762591) B2762591
theorem B1841735 : Blo 1841622 1841735 := bstep (se 1 (by rfl) ⟨1381301, by rfl⟩ : syracuseStep 1841735 = 2762603) B2762603
theorem B4143689 : Blo 1841622 4143689 := bstep (se 2 (by rfl) ⟨1553883, by rfl⟩ : syracuseStep 4143689 = 3107767) B3107767
theorem B5905003 : Blo 1841622 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B5249711 : Blo 1841622 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B1841887 : Blo 1841622 1841887 := bstep (se 1 (by rfl) ⟨1381415, by rfl⟩ : syracuseStep 1841887 = 2762831) B2762831
theorem B1841967 : Blo 1841622 1841967 := bstep (se 1 (by rfl) ⟨1381475, by rfl⟩ : syracuseStep 1841967 = 2762951) B2762951
theorem B15735707 : Blo 1841622 15735707 := bstep (se 1 (by rfl) ⟨11801780, by rfl⟩ : syracuseStep 15735707 = 23603561) B23603561
theorem B1842075 : Blo 1841622 1842075 := bstep (se 1 (by rfl) ⟨1381556, by rfl⟩ : syracuseStep 1842075 = 2763113) B2763113
theorem B9329579 : Blo 1841622 9329579 := bstep (se 1 (by rfl) ⟨6997184, by rfl⟩ : syracuseStep 9329579 = 13994369) B13994369
theorem B1842127 : Blo 1841622 1842127 := bstep (se 1 (by rfl) ⟨1381595, by rfl⟩ : syracuseStep 1842127 = 2763191) B2763191
theorem B4144103 : Blo 1841622 4144103 := bstep (se 1 (by rfl) ⟨3108077, by rfl⟩ : syracuseStep 4144103 = 6216155) B6216155
theorem B1842151 : Blo 1841622 1842151 := bstep (se 1 (by rfl) ⟨1381613, by rfl⟩ : syracuseStep 1842151 = 2763227) B2763227
theorem B1842463 : Blo 1841622 1842463 := bstep (se 1 (by rfl) ⟨1381847, by rfl⟩ : syracuseStep 1842463 = 2763695) B2763695
theorem B1842523 : Blo 1841622 1842523 := bstep (se 1 (by rfl) ⟨1381892, by rfl⟩ : syracuseStep 1842523 = 2763785) B2763785
theorem B4144481 : Blo 1841622 4144481 := bstep (se 2 (by rfl) ⟨1554180, by rfl⟩ : syracuseStep 4144481 = 3108361) B3108361
theorem B7978337 : Blo 1841622 7978337 := bstep (se 2 (by rfl) ⟨2991876, by rfl⟩ : syracuseStep 7978337 = 5983753) B5983753
theorem B1842543 : Blo 1841622 1842543 := bstep (se 1 (by rfl) ⟨1381907, by rfl⟩ : syracuseStep 1842543 = 2763815) B2763815
theorem B2071975 : Blo 1841622 2071975 := bstep (se 1 (by rfl) ⟨1553981, by rfl⟩ : syracuseStep 2071975 = 3107963) B3107963
theorem B1842599 : Blo 1841622 1842599 := bstep (se 1 (by rfl) ⟨1381949, by rfl⟩ : syracuseStep 1842599 = 2763899) B2763899
theorem B4144571 : Blo 1841622 4144571 := bstep (se 1 (by rfl) ⟨3108428, by rfl⟩ : syracuseStep 4144571 = 6216857) B6216857
theorem B1842683 : Blo 1841622 1842683 := bstep (se 1 (by rfl) ⟨1382012, by rfl⟩ : syracuseStep 1842683 = 2764025) B2764025
theorem B4144697 : Blo 1841622 4144697 := bstep (se 2 (by rfl) ⟨1554261, by rfl⟩ : syracuseStep 4144697 = 3108523) B3108523
theorem B1842751 : Blo 1841622 1842751 := bstep (se 1 (by rfl) ⟨1382063, by rfl⟩ : syracuseStep 1842751 = 2764127) B2764127
theorem B1842759 : Blo 1841622 1842759 := bstep (se 1 (by rfl) ⟨1382069, by rfl⟩ : syracuseStep 1842759 = 2764139) B2764139
theorem B6823507 : Blo 1841622 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B19930769 : Blo 1841622 19930769 := bstep (se 2 (by rfl) ⟨7474038, by rfl⟩ : syracuseStep 19930769 = 14948077) B14948077
theorem B1842911 : Blo 1841622 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B6217451 : Blo 1841622 6217451 := bstep (se 1 (by rfl) ⟨4663088, by rfl⟩ : syracuseStep 6217451 = 9326177) B9326177
theorem B3497735 : Blo 1841622 3497735 := bstep (se 1 (by rfl) ⟨2623301, by rfl⟩ : syracuseStep 3497735 = 5246603) B5246603
theorem B1842991 : Blo 1841622 1842991 := bstep (se 1 (by rfl) ⟨1382243, by rfl⟩ : syracuseStep 1842991 = 2764487) B2764487
theorem B8404793 : Blo 1841622 8404793 := bstep (se 2 (by rfl) ⟨3151797, by rfl⟩ : syracuseStep 8404793 = 6303595) B6303595
theorem B5906233 : Blo 1841622 5906233 := bstep (se 2 (by rfl) ⟨2214837, by rfl⟩ : syracuseStep 5906233 = 4429675) B4429675
theorem B21569341 : Blo 1841622 21569341 := bstep (se 3 (by rfl) ⟨4044251, by rfl⟩ : syracuseStep 21569341 = 8088503) B8088503
theorem B35422019 : Blo 1841622 35422019 := bstep (se 1 (by rfl) ⟨26566514, by rfl⟩ : syracuseStep 35422019 = 53133029) B53133029
theorem B1843099 : Blo 1841622 1843099 := bstep (se 1 (by rfl) ⟨1382324, by rfl⟩ : syracuseStep 1843099 = 2764649) B2764649
theorem B1843151 : Blo 1841622 1843151 := bstep (se 1 (by rfl) ⟨1382363, by rfl⟩ : syracuseStep 1843151 = 2764727) B2764727
theorem B2072551 : Blo 1841622 2072551 := bstep (se 1 (by rfl) ⟨1554413, by rfl⟩ : syracuseStep 2072551 = 3108827) B3108827
theorem B1843175 : Blo 1841622 1843175 := bstep (se 1 (by rfl) ⟨1382381, by rfl⟩ : syracuseStep 1843175 = 2764763) B2764763
theorem B15745103 : Blo 1841622 15745103 := bstep (se 1 (by rfl) ⟨11808827, by rfl⟩ : syracuseStep 15745103 = 23617655) B23617655
theorem B23609555 : Blo 1841622 23609555 := bstep (se 1 (by rfl) ⟨17707166, by rfl⟩ : syracuseStep 23609555 = 35414333) B35414333
theorem B1843431 : Blo 1841622 1843431 := bstep (se 1 (by rfl) ⟨1382573, by rfl⟩ : syracuseStep 1843431 = 2765147) B2765147
theorem B9961751 : Blo 1841622 9961751 := bstep (se 1 (by rfl) ⟨7471313, by rfl⟩ : syracuseStep 9961751 = 14942627) B14942627
theorem B1843583 : Blo 1841622 1843583 := bstep (se 1 (by rfl) ⟨1382687, by rfl⟩ : syracuseStep 1843583 = 2765375) B2765375
theorem B2957705 : Blo 1841622 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B11968955 : Blo 1841622 11968955 := bstep (se 1 (by rfl) ⟨8976716, by rfl⟩ : syracuseStep 11968955 = 17953433) B17953433
theorem B4145615 : Blo 1841622 4145615 := bstep (se 1 (by rfl) ⟨3109211, by rfl⟩ : syracuseStep 4145615 = 6218423) B6218423
theorem B6218369 : Blo 1841622 6218369 := bstep (se 2 (by rfl) ⟨2331888, by rfl⟩ : syracuseStep 6218369 = 4663777) B4663777
theorem B226878083 : Blo 1841622 226878083 := bstep (se 1 (by rfl) ⟨170158562, by rfl⟩ : syracuseStep 226878083 = 340317125) B340317125
theorem B18907823 : Blo 1841622 18907823 := bstep (se 1 (by rfl) ⟨14180867, by rfl⟩ : syracuseStep 18907823 = 28361735) B28361735
theorem B4661995 : Blo 1841622 4661995 := bstep (se 1 (by rfl) ⟨3496496, by rfl⟩ : syracuseStep 4661995 = 6992993) B6992993
theorem B7873337 : Blo 1841622 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B6218639 : Blo 1841622 6218639 := bstep (se 1 (by rfl) ⟨4663979, by rfl⟩ : syracuseStep 6218639 = 9327959) B9327959
theorem B2073595 : Blo 1841622 2073595 := bstep (se 1 (by rfl) ⟨1555196, by rfl⟩ : syracuseStep 2073595 = 3110393) B3110393
theorem B4146281 : Blo 1841622 4146281 := bstep (se 2 (by rfl) ⟨1554855, by rfl⟩ : syracuseStep 4146281 = 3109711) B3109711
theorem B2073775 : Blo 1841622 2073775 := bstep (se 1 (by rfl) ⟨1555331, by rfl⟩ : syracuseStep 2073775 = 3110663) B3110663
theorem B2802863 : Blo 1841622 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B6219179 : Blo 1841622 6219179 := bstep (se 1 (by rfl) ⟨4664384, by rfl⟩ : syracuseStep 6219179 = 9328769) B9328769
theorem B5244335 : Blo 1841622 5244335 := bstep (se 1 (by rfl) ⟨3933251, by rfl⟩ : syracuseStep 5244335 = 7866503) B7866503
theorem B2762459 : Blo 1841622 2762459 := bstep (se 1 (by rfl) ⟨2071844, by rfl⟩ : syracuseStep 2762459 = 4143689) B4143689
theorem B4146911 : Blo 1841622 4146911 := bstep (se 1 (by rfl) ⟨3110183, by rfl⟩ : syracuseStep 4146911 = 6220367) B6220367
theorem B20186909 : Blo 1841622 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B2557759 : Blo 1841622 2557759 := bstep (se 1 (by rfl) ⟨1918319, by rfl⟩ : syracuseStep 2557759 = 3836639) B3836639
theorem B9324395 : Blo 1841622 9324395 := bstep (se 1 (by rfl) ⟨6993296, by rfl⟩ : syracuseStep 9324395 = 13986593) B13986593
theorem B2762633 : Blo 1841622 2762633 := bstep (se 2 (by rfl) ⟨1035987, by rfl⟩ : syracuseStep 2762633 = 2071975) B2071975
theorem B113502097 : Blo 1841622 113502097 := bstep (se 2 (by rfl) ⟨42563286, by rfl⟩ : syracuseStep 113502097 = 85126573) B85126573
theorem B5244871 : Blo 1841622 5244871 := bstep (se 1 (by rfl) ⟨3933653, by rfl⟩ : syracuseStep 5244871 = 7867307) B7867307
theorem B6219719 : Blo 1841622 6219719 := bstep (se 1 (by rfl) ⟨4664789, by rfl⟩ : syracuseStep 6219719 = 9329579) B9329579
theorem B2762735 : Blo 1841622 2762735 := bstep (se 1 (by rfl) ⟨2072051, by rfl⟩ : syracuseStep 2762735 = 4144103) B4144103
theorem B11806829 : Blo 1841622 11806829 := bstep (se 3 (by rfl) ⟨2213780, by rfl⟩ : syracuseStep 11806829 = 4427561) B4427561
theorem B1968283 : Blo 1841622 1968283 := bstep (se 1 (by rfl) ⟨1476212, by rfl⟩ : syracuseStep 1968283 = 2952425) B2952425
theorem B2762987 : Blo 1841622 2762987 := bstep (se 1 (by rfl) ⟨2072240, by rfl⟩ : syracuseStep 2762987 = 4144481) B4144481
theorem B5318891 : Blo 1841622 5318891 := bstep (se 1 (by rfl) ⟨3989168, by rfl⟩ : syracuseStep 5318891 = 7978337) B7978337
theorem B2763047 : Blo 1841622 2763047 := bstep (se 1 (by rfl) ⟨2072285, by rfl⟩ : syracuseStep 2763047 = 4144571) B4144571
theorem B5982503 : Blo 1841622 5982503 := bstep (se 1 (by rfl) ⟨4486877, by rfl⟩ : syracuseStep 5982503 = 8973755) B8973755
theorem B2951471 : Blo 1841622 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B2763131 : Blo 1841622 2763131 := bstep (se 1 (by rfl) ⟨2072348, by rfl⟩ : syracuseStep 2763131 = 4144697) B4144697
theorem B7874977 : Blo 1841622 7874977 := bstep (se 2 (by rfl) ⟨2953116, by rfl⟩ : syracuseStep 7874977 = 5906233) B5906233
theorem B54602261 : Blo 1841622 54602261 := bstep (se 6 (by rfl) ⟨1279740, by rfl⟩ : syracuseStep 54602261 = 2559481) B2559481
theorem B3934747 : Blo 1841622 3934747 := bstep (se 1 (by rfl) ⟨2951060, by rfl⟩ : syracuseStep 3934747 = 5902121) B5902121
theorem B4147739 : Blo 1841622 4147739 := bstep (se 1 (by rfl) ⟨3110804, by rfl⟩ : syracuseStep 4147739 = 6221609) B6221609
theorem B2763401 : Blo 1841622 2763401 := bstep (se 2 (by rfl) ⟨1036275, by rfl⟩ : syracuseStep 2763401 = 2072551) B2072551
theorem B6220475 : Blo 1841622 6220475 := bstep (se 1 (by rfl) ⟨4665356, by rfl⟩ : syracuseStep 6220475 = 9330713) B9330713
theorem B89688869 : Blo 1841622 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B2763575 : Blo 1841622 2763575 := bstep (se 1 (by rfl) ⟨2072681, by rfl⟩ : syracuseStep 2763575 = 4145363) B4145363
theorem B2763611 : Blo 1841622 2763611 := bstep (se 1 (by rfl) ⟨2072708, by rfl⟩ : syracuseStep 2763611 = 4145417) B4145417
theorem B2952143 : Blo 1841622 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B2763755 : Blo 1841622 2763755 := bstep (se 1 (by rfl) ⟨2072816, by rfl⟩ : syracuseStep 2763755 = 4145633) B4145633
theorem B2624491 : Blo 1841622 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B4729903 : Blo 1841622 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B2763959 : Blo 1841622 2763959 := bstep (se 1 (by rfl) ⟨2072969, by rfl⟩ : syracuseStep 2763959 = 4145939) B4145939
theorem B40381739 : Blo 1841622 40381739 := bstep (se 1 (by rfl) ⟨30286304, by rfl⟩ : syracuseStep 40381739 = 60572609) B60572609
theorem B3935567 : Blo 1841622 3935567 := bstep (se 1 (by rfl) ⟨2951675, by rfl⟩ : syracuseStep 3935567 = 5903351) B5903351
theorem B53136719 : Blo 1841622 53136719 := bstep (se 1 (by rfl) ⟨39852539, by rfl⟩ : syracuseStep 53136719 = 79705079) B79705079
theorem B2764199 : Blo 1841622 2764199 := bstep (se 1 (by rfl) ⟨2073149, by rfl⟩ : syracuseStep 2764199 = 4146299) B4146299
theorem B2952617 : Blo 1841622 2952617 := bstep (se 2 (by rfl) ⟨1107231, by rfl⟩ : syracuseStep 2952617 = 2214463) B2214463
theorem B6999479 : Blo 1841622 6999479 := bstep (se 1 (by rfl) ⟨5249609, by rfl⟩ : syracuseStep 6999479 = 10499219) B10499219
theorem B2764283 : Blo 1841622 2764283 := bstep (se 1 (by rfl) ⟨2073212, by rfl⟩ : syracuseStep 2764283 = 4146425) B4146425
theorem B3108415 : Blo 1841622 3108415 := bstep (se 1 (by rfl) ⟨2331311, by rfl⟩ : syracuseStep 3108415 = 4662623) B4662623
theorem B2764379 : Blo 1841622 2764379 := bstep (se 1 (by rfl) ⟨2073284, by rfl⟩ : syracuseStep 2764379 = 4146569) B4146569
theorem B16805501 : Blo 1841622 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B9965213 : Blo 1841622 9965213 := bstep (se 3 (by rfl) ⟨1868477, by rfl⟩ : syracuseStep 9965213 = 3736955) B3736955
theorem B2764463 : Blo 1841622 2764463 := bstep (se 1 (by rfl) ⟨2073347, by rfl⟩ : syracuseStep 2764463 = 4146695) B4146695
theorem B2764583 : Blo 1841622 2764583 := bstep (se 1 (by rfl) ⟨2073437, by rfl⟩ : syracuseStep 2764583 = 4146875) B4146875
theorem B2764667 : Blo 1841622 2764667 := bstep (se 1 (by rfl) ⟨2073500, by rfl⟩ : syracuseStep 2764667 = 4147001) B4147001
theorem B5902235 : Blo 1841622 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B9957343 : Blo 1841622 9957343 := bstep (se 1 (by rfl) ⟨7468007, by rfl⟩ : syracuseStep 9957343 = 14936015) B14936015
theorem B13988051 : Blo 1841622 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B3109151 : Blo 1841622 3109151 := bstep (se 1 (by rfl) ⟨2331863, by rfl⟩ : syracuseStep 3109151 = 4663727) B4663727
theorem B2765087 : Blo 1841622 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B17707319 : Blo 1841622 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B2765111 : Blo 1841622 2765111 := bstep (se 1 (by rfl) ⟨2073833, by rfl⟩ : syracuseStep 2765111 = 4147667) B4147667
theorem B2765183 : Blo 1841622 2765183 := bstep (se 1 (by rfl) ⟨2073887, by rfl⟩ : syracuseStep 2765183 = 4147775) B4147775
theorem B9957775 : Blo 1841622 9957775 := bstep (se 1 (by rfl) ⟨7468331, by rfl⟩ : syracuseStep 9957775 = 14936663) B14936663
theorem B2765255 : Blo 1841622 2765255 := bstep (se 1 (by rfl) ⟨2073941, by rfl⟩ : syracuseStep 2765255 = 4147883) B4147883
theorem B10490471 : Blo 1841622 10490471 := bstep (se 1 (by rfl) ⟨7867853, by rfl⟩ : syracuseStep 10490471 = 15735707) B15735707
theorem B9098009 : Blo 1841622 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B3109799 : Blo 1841622 3109799 := bstep (se 1 (by rfl) ⟨2332349, by rfl⟩ : syracuseStep 3109799 = 4664699) B4664699
theorem B13276169 : Blo 1841622 13276169 := bstep (se 2 (by rfl) ⟨4978563, by rfl⟩ : syracuseStep 13276169 = 9957127) B9957127
theorem B3109961 : Blo 1841622 3109961 := bstep (se 2 (by rfl) ⟨1166235, by rfl⟩ : syracuseStep 3109961 = 2332471) B2332471
theorem B28759121 : Blo 1841622 28759121 := bstep (se 2 (by rfl) ⟨10784670, by rfl⟩ : syracuseStep 28759121 = 21569341) B21569341
theorem B2331823 : Blo 1841622 2331823 := bstep (se 1 (by rfl) ⟨1748867, by rfl⟩ : syracuseStep 2331823 = 3497735) B3497735
theorem B23614679 : Blo 1841622 23614679 := bstep (se 1 (by rfl) ⟨17711009, by rfl⟩ : syracuseStep 23614679 = 35422019) B35422019
theorem B4666643 : Blo 1841622 4666643 := bstep (se 1 (by rfl) ⟨3499982, by rfl⟩ : syracuseStep 4666643 = 6999965) B6999965
theorem B6993479 : Blo 1841622 6993479 := bstep (se 1 (by rfl) ⟨5245109, by rfl⟩ : syracuseStep 6993479 = 10490219) B10490219
theorem B11810393 : Blo 1841622 11810393 := bstep (se 2 (by rfl) ⟨4428897, by rfl⟩ : syracuseStep 11810393 = 8857795) B8857795
theorem B3110521 : Blo 1841622 3110521 := bstep (se 2 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 3110521 = 2332891) B2332891
theorem B6215561 : Blo 1841622 6215561 := bstep (se 2 (by rfl) ⟨2330835, by rfl⟩ : syracuseStep 6215561 = 4661671) B4661671
theorem B5904377 : Blo 1841622 5904377 := bstep (se 2 (by rfl) ⟨2214141, by rfl⟩ : syracuseStep 5904377 = 4428283) B4428283
theorem B10491929 : Blo 1841622 10491929 := bstep (se 2 (by rfl) ⟨3934473, by rfl⟩ : syracuseStep 10491929 = 7868947) B7868947
theorem B5249119 : Blo 1841622 5249119 := bstep (se 1 (by rfl) ⟨3936839, by rfl⟩ : syracuseStep 5249119 = 7873679) B7873679
theorem B3111007 : Blo 1841622 3111007 := bstep (se 1 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 3111007 = 4666511) B4666511
theorem B6215777 : Blo 1841622 6215777 := bstep (se 2 (by rfl) ⟨2330916, by rfl⟩ : syracuseStep 6215777 = 4661833) B4661833
theorem B18913409 : Blo 1841622 18913409 := bstep (se 2 (by rfl) ⟨7092528, by rfl⟩ : syracuseStep 18913409 = 14185057) B14185057
theorem B6822319 : Blo 1841622 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B19929563 : Blo 1841622 19929563 := bstep (se 1 (by rfl) ⟨14947172, by rfl⟩ : syracuseStep 19929563 = 29894345) B29894345
theorem B6994451 : Blo 1841622 6994451 := bstep (se 1 (by rfl) ⟨5245838, by rfl⟩ : syracuseStep 6994451 = 10491677) B10491677
theorem B1841691 : Blo 1841622 1841691 := bstep (se 1 (by rfl) ⟨1381268, by rfl⟩ : syracuseStep 1841691 = 2762537) B2762537
theorem B1841695 : Blo 1841622 1841695 := bstep (se 1 (by rfl) ⟨1381271, by rfl⟩ : syracuseStep 1841695 = 2762543) B2762543
theorem B2333215 : Blo 1841622 2333215 := bstep (se 1 (by rfl) ⟨1749911, by rfl⟩ : syracuseStep 2333215 = 3499823) B3499823
theorem B1842011 : Blo 1841622 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B4143977 : Blo 1841622 4143977 := bstep (se 2 (by rfl) ⟨1553991, by rfl⟩ : syracuseStep 4143977 = 3107983) B3107983
theorem B4144031 : Blo 1841622 4144031 := bstep (se 1 (by rfl) ⟨3108023, by rfl⟩ : syracuseStep 4144031 = 6216047) B6216047
theorem B1842079 : Blo 1841622 1842079 := bstep (se 1 (by rfl) ⟨1381559, by rfl⟩ : syracuseStep 1842079 = 2763119) B2763119
theorem B6216695 : Blo 1841622 6216695 := bstep (se 1 (by rfl) ⟨4662521, by rfl⟩ : syracuseStep 6216695 = 9325043) B9325043
theorem B1842223 : Blo 1841622 1842223 := bstep (se 1 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 1842223 = 2763335) B2763335
theorem B1842247 : Blo 1841622 1842247 := bstep (se 1 (by rfl) ⟨1381685, by rfl⟩ : syracuseStep 1842247 = 2763371) B2763371
theorem B15744077 : Blo 1841622 15744077 := bstep (se 3 (by rfl) ⟨2952014, by rfl⟩ : syracuseStep 15744077 = 5904029) B5904029
theorem B22715515 : Blo 1841622 22715515 := bstep (se 1 (by rfl) ⟨17036636, by rfl⟩ : syracuseStep 22715515 = 34073273) B34073273
theorem B13999229 : Blo 1841622 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B1842399 : Blo 1841622 1842399 := bstep (se 1 (by rfl) ⟨1381799, by rfl⟩ : syracuseStep 1842399 = 2763599) B2763599
theorem B53099813 : Blo 1841622 53099813 := bstep (se 4 (by rfl) ⟨4978107, by rfl⟩ : syracuseStep 53099813 = 9956215) B9956215
theorem B6217127 : Blo 1841622 6217127 := bstep (se 1 (by rfl) ⟨4662845, by rfl⟩ : syracuseStep 6217127 = 9325691) B9325691
theorem B1842663 : Blo 1841622 1842663 := bstep (se 1 (by rfl) ⟨1381997, by rfl⟩ : syracuseStep 1842663 = 2763995) B2763995
theorem B2072155 : Blo 1841622 2072155 := bstep (se 1 (by rfl) ⟨1554116, by rfl⟩ : syracuseStep 2072155 = 3108233) B3108233
theorem B1842779 : Blo 1841622 1842779 := bstep (se 1 (by rfl) ⟨1382084, by rfl⟩ : syracuseStep 1842779 = 2764169) B2764169
theorem B7093993 : Blo 1841622 7093993 := bstep (se 2 (by rfl) ⟨2660247, by rfl⟩ : syracuseStep 7093993 = 5320495) B5320495
theorem B13287179 : Blo 1841622 13287179 := bstep (se 1 (by rfl) ⟨9965384, by rfl⟩ : syracuseStep 13287179 = 19930769) B19930769
theorem B4144967 : Blo 1841622 4144967 := bstep (se 1 (by rfl) ⟨3108725, by rfl⟩ : syracuseStep 4144967 = 6217451) B6217451
theorem B1843015 : Blo 1841622 1843015 := bstep (se 1 (by rfl) ⟨1382261, by rfl⟩ : syracuseStep 1843015 = 2764523) B2764523
theorem B6217559 : Blo 1841622 6217559 := bstep (se 1 (by rfl) ⟨4663169, by rfl⟩ : syracuseStep 6217559 = 9326339) B9326339
theorem B2072443 : Blo 1841622 2072443 := bstep (se 1 (by rfl) ⟨1554332, by rfl⟩ : syracuseStep 2072443 = 3108665) B3108665
theorem B10493819 : Blo 1841622 10493819 := bstep (se 1 (by rfl) ⟨7870364, by rfl⟩ : syracuseStep 10493819 = 15740729) B15740729
theorem B5603195 : Blo 1841622 5603195 := bstep (se 1 (by rfl) ⟨4202396, by rfl⟩ : syracuseStep 5603195 = 8404793) B8404793
theorem B1843167 : Blo 1841622 1843167 := bstep (se 1 (by rfl) ⟨1382375, by rfl⟩ : syracuseStep 1843167 = 2764751) B2764751
theorem B2072767 : Blo 1841622 2072767 := bstep (se 1 (by rfl) ⟨1554575, by rfl⟩ : syracuseStep 2072767 = 3109151) B3109151
theorem B1843391 : Blo 1841622 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B11804879 : Blo 1841622 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B1843407 : Blo 1841622 1843407 := bstep (se 1 (by rfl) ⟨1382555, by rfl⟩ : syracuseStep 1843407 = 2765111) B2765111
theorem B1843455 : Blo 1841622 1843455 := bstep (se 1 (by rfl) ⟨1382591, by rfl⟩ : syracuseStep 1843455 = 2765183) B2765183
theorem B7979303 : Blo 1841622 7979303 := bstep (se 1 (by rfl) ⟨5984477, by rfl⟩ : syracuseStep 7979303 = 11968955) B11968955
theorem B1843503 : Blo 1841622 1843503 := bstep (se 1 (by rfl) ⟨1382627, by rfl⟩ : syracuseStep 1843503 = 2765255) B2765255
theorem B4145579 : Blo 1841622 4145579 := bstep (se 1 (by rfl) ⟨3109184, by rfl⟩ : syracuseStep 4145579 = 6218369) B6218369
theorem B4145759 : Blo 1841622 4145759 := bstep (se 1 (by rfl) ⟨3109319, by rfl⟩ : syracuseStep 4145759 = 6218639) B6218639
theorem B2073199 : Blo 1841622 2073199 := bstep (se 1 (by rfl) ⟨1554899, by rfl⟩ : syracuseStep 2073199 = 3109799) B3109799
theorem B2073307 : Blo 1841622 2073307 := bstep (se 1 (by rfl) ⟨1554980, by rfl⟩ : syracuseStep 2073307 = 3109961) B3109961
theorem B10494845 : Blo 1841622 10494845 := bstep (se 3 (by rfl) ⟨1967783, by rfl⟩ : syracuseStep 10494845 = 3935567) B3935567
theorem B4146119 : Blo 1841622 4146119 := bstep (se 1 (by rfl) ⟨3109589, by rfl⟩ : syracuseStep 4146119 = 6219179) B6219179
theorem B4662319 : Blo 1841622 4662319 := bstep (se 1 (by rfl) ⟨3496739, by rfl⟩ : syracuseStep 4662319 = 6993479) B6993479
theorem B7873595 : Blo 1841622 7873595 := bstep (se 1 (by rfl) ⟨5905196, by rfl⟩ : syracuseStep 7873595 = 11810393) B11810393
theorem B7873645 : Blo 1841622 7873645 := bstep (se 3 (by rfl) ⟨1476308, by rfl⟩ : syracuseStep 7873645 = 2952617) B2952617
theorem B4146479 : Blo 1841622 4146479 := bstep (se 1 (by rfl) ⟨3109859, by rfl⟩ : syracuseStep 4146479 = 6219719) B6219719
theorem B12608939 : Blo 1841622 12608939 := bstep (se 1 (by rfl) ⟨9456704, by rfl⟩ : syracuseStep 12608939 = 18913409) B18913409
theorem B30287353 : Blo 1841622 30287353 := bstep (se 2 (by rfl) ⟨11357757, by rfl⟩ : syracuseStep 30287353 = 22715515) B22715515
theorem B1967647 : Blo 1841622 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B4662967 : Blo 1841622 4662967 := bstep (se 1 (by rfl) ⟨3497225, by rfl⟩ : syracuseStep 4662967 = 6994451) B6994451
theorem B4146983 : Blo 1841622 4146983 := bstep (se 1 (by rfl) ⟨3110237, by rfl⟩ : syracuseStep 4146983 = 6220475) B6220475
theorem B2762651 : Blo 1841622 2762651 := bstep (se 1 (by rfl) ⟨2071988, by rfl⟩ : syracuseStep 2762651 = 4143977) B4143977
theorem B2762687 : Blo 1841622 2762687 := bstep (se 1 (by rfl) ⟨2072015, by rfl⟩ : syracuseStep 2762687 = 4144031) B4144031
theorem B1968095 : Blo 1841622 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B35432477 : Blo 1841622 35432477 := bstep (se 3 (by rfl) ⟨6643589, by rfl⟩ : syracuseStep 35432477 = 13287179) B13287179
theorem B10496051 : Blo 1841622 10496051 := bstep (se 1 (by rfl) ⟨7872038, by rfl⟩ : syracuseStep 10496051 = 15744077) B15744077
theorem B9332819 : Blo 1841622 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B2762873 : Blo 1841622 2762873 := bstep (se 2 (by rfl) ⟨1036077, by rfl⟩ : syracuseStep 2762873 = 2072155) B2072155
theorem B4147361 : Blo 1841622 4147361 := bstep (se 2 (by rfl) ⟨1555260, by rfl⟩ : syracuseStep 4147361 = 3110521) B3110521
theorem B35399875 : Blo 1841622 35399875 := bstep (se 1 (by rfl) ⟨26549906, by rfl⟩ : syracuseStep 35399875 = 53099813) B53099813
theorem B26921159 : Blo 1841622 26921159 := bstep (se 1 (by rfl) ⟨20190869, by rfl⟩ : syracuseStep 26921159 = 40381739) B40381739
theorem B35424479 : Blo 1841622 35424479 := bstep (se 1 (by rfl) ⟨26568359, by rfl⟩ : syracuseStep 35424479 = 53136719) B53136719
theorem B3410345 : Blo 1841622 3410345 := bstep (se 2 (by rfl) ⟨1278879, by rfl⟩ : syracuseStep 3410345 = 2557759) B2557759
theorem B2763257 : Blo 1841622 2763257 := bstep (se 2 (by rfl) ⟨1036221, by rfl⟩ : syracuseStep 2763257 = 2072443) B2072443
theorem B2763311 : Blo 1841622 2763311 := bstep (se 1 (by rfl) ⟨2072483, by rfl⟩ : syracuseStep 2763311 = 4144967) B4144967
theorem B3934823 : Blo 1841622 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B10496735 : Blo 1841622 10496735 := bstep (se 1 (by rfl) ⟨7872551, by rfl⟩ : syracuseStep 10496735 = 15745103) B15745103
theorem B6998825 : Blo 1841622 6998825 := bstep (se 2 (by rfl) ⟨2624559, by rfl⟩ : syracuseStep 6998825 = 5249119) B5249119
theorem B4148009 : Blo 1841622 4148009 := bstep (se 2 (by rfl) ⟨1555503, by rfl⟩ : syracuseStep 4148009 = 3111007) B3111007
theorem B15739703 : Blo 1841622 15739703 := bstep (se 1 (by rfl) ⟨11804777, by rfl⟩ : syracuseStep 15739703 = 23609555) B23609555
theorem B9325367 : Blo 1841622 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B25226149 : Blo 1841622 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B2763743 : Blo 1841622 2763743 := bstep (se 1 (by rfl) ⟨2072807, by rfl⟩ : syracuseStep 2763743 = 4145615) B4145615
theorem B151252055 : Blo 1841622 151252055 := bstep (se 1 (by rfl) ⟨113439041, by rfl⟩ : syracuseStep 151252055 = 226878083) B226878083
theorem B7474301 : Blo 1841622 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B6065339 : Blo 1841622 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B9096425 : Blo 1841622 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B8850779 : Blo 1841622 8850779 := bstep (se 1 (by rfl) ⟨6638084, by rfl⟩ : syracuseStep 8850779 = 13276169) B13276169
theorem B5246329 : Blo 1841622 5246329 := bstep (se 2 (by rfl) ⟨1967373, by rfl⟩ : syracuseStep 5246329 = 3934747) B3934747
theorem B19172747 : Blo 1841622 19172747 := bstep (se 1 (by rfl) ⟨14379560, by rfl⟩ : syracuseStep 19172747 = 28759121) B28759121
theorem B2764187 : Blo 1841622 2764187 := bstep (se 1 (by rfl) ⟨2073140, by rfl⟩ : syracuseStep 2764187 = 4146281) B4146281
theorem B10497509 : Blo 1841622 10497509 := bstep (se 4 (by rfl) ⟨984141, by rfl⟩ : syracuseStep 10497509 = 1968283) B1968283
theorem B2764607 : Blo 1841622 2764607 := bstep (se 1 (by rfl) ⟨2073455, by rfl⟩ : syracuseStep 2764607 = 4146911) B4146911
theorem B2764793 : Blo 1841622 2764793 := bstep (se 2 (by rfl) ⟨1036797, by rfl⟩ : syracuseStep 2764793 = 2073595) B2073595
theorem B3936251 : Blo 1841622 3936251 := bstep (se 1 (by rfl) ⟨2952188, by rfl⟩ : syracuseStep 3936251 = 5904377) B5904377
theorem B3109097 : Blo 1841622 3109097 := bstep (se 2 (by rfl) ⟨1165911, by rfl⟩ : syracuseStep 3109097 = 2331823) B2331823
theorem B2765033 : Blo 1841622 2765033 := bstep (se 2 (by rfl) ⟨1036887, by rfl⟩ : syracuseStep 2765033 = 2073775) B2073775
theorem B36401507 : Blo 1841622 36401507 := bstep (se 1 (by rfl) ⟨27301130, by rfl⟩ : syracuseStep 36401507 = 54602261) B54602261
theorem B2765159 : Blo 1841622 2765159 := bstep (se 1 (by rfl) ⟨2073869, by rfl⟩ : syracuseStep 2765159 = 4147739) B4147739
theorem B4666319 : Blo 1841622 4666319 := bstep (se 1 (by rfl) ⟨3499739, by rfl⟩ : syracuseStep 4666319 = 6999479) B6999479
theorem B9458657 : Blo 1841622 9458657 := bstep (se 2 (by rfl) ⟨3546996, by rfl⟩ : syracuseStep 9458657 = 7093993) B7093993
theorem B11203667 : Blo 1841622 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B151336129 : Blo 1841622 151336129 := bstep (se 2 (by rfl) ⟨56751048, by rfl⟩ : syracuseStep 151336129 = 113502097) B113502097
theorem B13997285 : Blo 1841622 13997285 := bstep (se 4 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 13997285 = 2624491) B2624491
theorem B6993161 : Blo 1841622 6993161 := bstep (se 2 (by rfl) ⟨2622435, by rfl⟩ : syracuseStep 6993161 = 5244871) B5244871
theorem B13276457 : Blo 1841622 13276457 := bstep (se 2 (by rfl) ⟨4978671, by rfl⟩ : syracuseStep 13276457 = 9957343) B9957343
theorem B1971803 : Blo 1841622 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B6993647 : Blo 1841622 6993647 := bstep (se 1 (by rfl) ⟨5245235, by rfl⟩ : syracuseStep 6993647 = 10490471) B10490471
theorem B63813365 : Blo 1841622 63813365 := bstep (se 5 (by rfl) ⟨2991251, by rfl⟩ : syracuseStep 63813365 = 5982503) B5982503
theorem B12605215 : Blo 1841622 12605215 := bstep (se 1 (by rfl) ⟨9453911, by rfl⟩ : syracuseStep 12605215 = 18907823) B18907823
theorem B13277033 : Blo 1841622 13277033 := bstep (se 2 (by rfl) ⟨4978887, by rfl⟩ : syracuseStep 13277033 = 9957775) B9957775
theorem B5248891 : Blo 1841622 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B10499969 : Blo 1841622 10499969 := bstep (se 2 (by rfl) ⟨3937488, by rfl⟩ : syracuseStep 10499969 = 7874977) B7874977
theorem B3110953 : Blo 1841622 3110953 := bstep (se 2 (by rfl) ⟨1166607, by rfl⟩ : syracuseStep 3110953 = 2333215) B2333215
theorem B26564669 : Blo 1841622 26564669 := bstep (se 3 (by rfl) ⟨4980875, by rfl⟩ : syracuseStep 26564669 = 9961751) B9961751
theorem B15743119 : Blo 1841622 15743119 := bstep (se 1 (by rfl) ⟨11807339, by rfl⟩ : syracuseStep 15743119 = 23614679) B23614679
theorem B3111095 : Blo 1841622 3111095 := bstep (se 1 (by rfl) ⟨2333321, by rfl⟩ : syracuseStep 3111095 = 4666643) B4666643
theorem B3496223 : Blo 1841622 3496223 := bstep (se 1 (by rfl) ⟨2622167, by rfl⟩ : syracuseStep 3496223 = 5244335) B5244335
theorem B6215993 : Blo 1841622 6215993 := bstep (se 2 (by rfl) ⟨2330997, by rfl⟩ : syracuseStep 6215993 = 4661995) B4661995
theorem B1841639 : Blo 1841622 1841639 := bstep (se 1 (by rfl) ⟨1381229, by rfl⟩ : syracuseStep 1841639 = 2762459) B2762459
theorem B13457939 : Blo 1841622 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B6216263 : Blo 1841622 6216263 := bstep (se 1 (by rfl) ⟨4662197, by rfl⟩ : syracuseStep 6216263 = 9324395) B9324395
theorem B4143707 : Blo 1841622 4143707 := bstep (se 1 (by rfl) ⟨3107780, by rfl⟩ : syracuseStep 4143707 = 6215561) B6215561
theorem B1841755 : Blo 1841622 1841755 := bstep (se 1 (by rfl) ⟨1381316, by rfl⟩ : syracuseStep 1841755 = 2762633) B2762633
theorem B1841823 : Blo 1841622 1841823 := bstep (se 1 (by rfl) ⟨1381367, by rfl⟩ : syracuseStep 1841823 = 2762735) B2762735
theorem B6994619 : Blo 1841622 6994619 := bstep (se 1 (by rfl) ⟨5245964, by rfl⟩ : syracuseStep 6994619 = 10491929) B10491929
theorem B4143851 : Blo 1841622 4143851 := bstep (se 1 (by rfl) ⟨3107888, by rfl⟩ : syracuseStep 4143851 = 6215777) B6215777
theorem B7871219 : Blo 1841622 7871219 := bstep (se 1 (by rfl) ⟨5903414, by rfl⟩ : syracuseStep 7871219 = 11806829) B11806829
theorem B1841991 : Blo 1841622 1841991 := bstep (se 1 (by rfl) ⟨1381493, by rfl⟩ : syracuseStep 1841991 = 2762987) B2762987
theorem B3545927 : Blo 1841622 3545927 := bstep (se 1 (by rfl) ⟨2659445, by rfl⟩ : syracuseStep 3545927 = 5318891) B5318891
theorem B1842031 : Blo 1841622 1842031 := bstep (se 1 (by rfl) ⟨1381523, by rfl⟩ : syracuseStep 1842031 = 2763047) B2763047
theorem B1842087 : Blo 1841622 1842087 := bstep (se 1 (by rfl) ⟨1381565, by rfl⟩ : syracuseStep 1842087 = 2763131) B2763131
theorem B13286375 : Blo 1841622 13286375 := bstep (se 1 (by rfl) ⟨9964781, by rfl⟩ : syracuseStep 13286375 = 19929563) B19929563
theorem B1842267 : Blo 1841622 1842267 := bstep (se 1 (by rfl) ⟨1381700, by rfl⟩ : syracuseStep 1842267 = 2763401) B2763401
theorem B59792579 : Blo 1841622 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B1842383 : Blo 1841622 1842383 := bstep (se 1 (by rfl) ⟨1381787, by rfl⟩ : syracuseStep 1842383 = 2763575) B2763575
theorem B1842407 : Blo 1841622 1842407 := bstep (se 1 (by rfl) ⟨1381805, by rfl⟩ : syracuseStep 1842407 = 2763611) B2763611
theorem B1842503 : Blo 1841622 1842503 := bstep (se 1 (by rfl) ⟨1381877, by rfl⟩ : syracuseStep 1842503 = 2763755) B2763755
theorem B4144463 : Blo 1841622 4144463 := bstep (se 1 (by rfl) ⟨3108347, by rfl⟩ : syracuseStep 4144463 = 6216695) B6216695
theorem B4144553 : Blo 1841622 4144553 := bstep (se 2 (by rfl) ⟨1554207, by rfl⟩ : syracuseStep 4144553 = 3108415) B3108415
theorem B1842639 : Blo 1841622 1842639 := bstep (se 1 (by rfl) ⟨1381979, by rfl⟩ : syracuseStep 1842639 = 2763959) B2763959
theorem B4144751 : Blo 1841622 4144751 := bstep (se 1 (by rfl) ⟨3108563, by rfl⟩ : syracuseStep 4144751 = 6217127) B6217127
theorem B1842799 : Blo 1841622 1842799 := bstep (se 1 (by rfl) ⟨1382099, by rfl⟩ : syracuseStep 1842799 = 2764199) B2764199
theorem B1842855 : Blo 1841622 1842855 := bstep (se 1 (by rfl) ⟨1382141, by rfl⟩ : syracuseStep 1842855 = 2764283) B2764283
theorem B1842919 : Blo 1841622 1842919 := bstep (se 1 (by rfl) ⟨1382189, by rfl⟩ : syracuseStep 1842919 = 2764379) B2764379
theorem B6643475 : Blo 1841622 6643475 := bstep (se 1 (by rfl) ⟨4982606, by rfl⟩ : syracuseStep 6643475 = 9965213) B9965213
theorem B1842975 : Blo 1841622 1842975 := bstep (se 1 (by rfl) ⟨1382231, by rfl⟩ : syracuseStep 1842975 = 2764463) B2764463
theorem B1843055 : Blo 1841622 1843055 := bstep (se 1 (by rfl) ⟨1382291, by rfl⟩ : syracuseStep 1843055 = 2764583) B2764583
theorem B4145039 : Blo 1841622 4145039 := bstep (se 1 (by rfl) ⟨3108779, by rfl⟩ : syracuseStep 4145039 = 6217559) B6217559
theorem B6995879 : Blo 1841622 6995879 := bstep (se 1 (by rfl) ⟨5246909, by rfl⟩ : syracuseStep 6995879 = 10493819) B10493819
theorem B3735463 : Blo 1841622 3735463 := bstep (se 1 (by rfl) ⟨2801597, by rfl⟩ : syracuseStep 3735463 = 5603195) B5603195
theorem B1843111 : Blo 1841622 1843111 := bstep (se 1 (by rfl) ⟨1382333, by rfl⟩ : syracuseStep 1843111 = 2764667) B2764667
theorem B2072731 : Blo 1841622 2072731 := bstep (se 1 (by rfl) ⟨1554548, by rfl⟩ : syracuseStep 2072731 = 3109097) B3109097
theorem B1843355 : Blo 1841622 1843355 := bstep (se 1 (by rfl) ⟨1382516, by rfl⟩ : syracuseStep 1843355 = 2765033) B2765033
theorem B1843195 : Blo 1841622 1843195 := bstep (se 1 (by rfl) ⟨1382396, by rfl⟩ : syracuseStep 1843195 = 2764793) B2764793
theorem B1843439 : Blo 1841622 1843439 := bstep (se 1 (by rfl) ⟨1382579, by rfl⟩ : syracuseStep 1843439 = 2765159) B2765159
theorem B6996563 : Blo 1841622 6996563 := bstep (se 1 (by rfl) ⟨5247422, by rfl⟩ : syracuseStep 6996563 = 10494845) B10494845
theorem B9323261 : Blo 1841622 9323261 := bstep (se 3 (by rfl) ⟨1748111, by rfl⟩ : syracuseStep 9323261 = 3496223) B3496223
theorem B9331523 : Blo 1841622 9331523 := bstep (se 1 (by rfl) ⟨6998642, by rfl⟩ : syracuseStep 9331523 = 13997285) B13997285
theorem B4662107 : Blo 1841622 4662107 := bstep (se 1 (by rfl) ⟨3496580, by rfl⟩ : syracuseStep 4662107 = 6993161) B6993161
theorem B8405959 : Blo 1841622 8405959 := bstep (se 1 (by rfl) ⟨6304469, by rfl⟩ : syracuseStep 8405959 = 12608939) B12608939
theorem B51127325 : Blo 1841622 51127325 := bstep (se 3 (by rfl) ⟨9586373, by rfl⟩ : syracuseStep 51127325 = 19172747) B19172747
theorem B4662431 : Blo 1841622 4662431 := bstep (se 1 (by rfl) ⟨3496823, by rfl⟩ : syracuseStep 4662431 = 6993647) B6993647
theorem B42542243 : Blo 1841622 42542243 := bstep (se 1 (by rfl) ⟨31906682, by rfl⟩ : syracuseStep 42542243 = 63813365) B63813365
theorem B6997367 : Blo 1841622 6997367 := bstep (se 1 (by rfl) ⟨5248025, by rfl⟩ : syracuseStep 6997367 = 10496051) B10496051
theorem B2074063 : Blo 1841622 2074063 := bstep (se 1 (by rfl) ⟨1555547, by rfl⟩ : syracuseStep 2074063 = 3111095) B3111095
theorem B2762471 : Blo 1841622 2762471 := bstep (se 1 (by rfl) ⟨2071853, by rfl⟩ : syracuseStep 2762471 = 4143707) B4143707
theorem B4663079 : Blo 1841622 4663079 := bstep (se 1 (by rfl) ⟨3497309, by rfl⟩ : syracuseStep 4663079 = 6994619) B6994619
theorem B6997823 : Blo 1841622 6997823 := bstep (se 1 (by rfl) ⟨5248367, by rfl⟩ : syracuseStep 6997823 = 10496735) B10496735
theorem B2762567 : Blo 1841622 2762567 := bstep (se 1 (by rfl) ⟨2071925, by rfl⟩ : syracuseStep 2762567 = 4143851) B4143851
theorem B8857583 : Blo 1841622 8857583 := bstep (se 1 (by rfl) ⟨6643187, by rfl⟩ : syracuseStep 8857583 = 13286375) B13286375
theorem B2623529 : Blo 1841622 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B4982867 : Blo 1841622 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B6064283 : Blo 1841622 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B2762975 : Blo 1841622 2762975 := bstep (se 1 (by rfl) ⟨2072231, by rfl⟩ : syracuseStep 2762975 = 4144463) B4144463
theorem B5900519 : Blo 1841622 5900519 := bstep (se 1 (by rfl) ⟨4425389, by rfl⟩ : syracuseStep 5900519 = 8850779) B8850779
theorem B2763035 : Blo 1841622 2763035 := bstep (se 1 (by rfl) ⟨2072276, by rfl⟩ : syracuseStep 2763035 = 4144553) B4144553
theorem B6998339 : Blo 1841622 6998339 := bstep (se 1 (by rfl) ⟨5248754, by rfl⟩ : syracuseStep 6998339 = 10497509) B10497509
theorem B2763167 : Blo 1841622 2763167 := bstep (se 1 (by rfl) ⟨2072375, by rfl⟩ : syracuseStep 2763167 = 4144751) B4144751
theorem B6998521 : Blo 1841622 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B2763359 : Blo 1841622 2763359 := bstep (se 1 (by rfl) ⟨2072519, by rfl⟩ : syracuseStep 2763359 = 4145039) B4145039
theorem B4663919 : Blo 1841622 4663919 := bstep (se 1 (by rfl) ⟨3497939, by rfl⟩ : syracuseStep 4663919 = 6995879) B6995879
theorem B2624167 : Blo 1841622 2624167 := bstep (se 1 (by rfl) ⟨1968125, by rfl⟩ : syracuseStep 2624167 = 3936251) B3936251
theorem B4147937 : Blo 1841622 4147937 := bstep (se 2 (by rfl) ⟨1555476, by rfl⟩ : syracuseStep 4147937 = 3110953) B3110953
theorem B20990825 : Blo 1841622 20990825 := bstep (se 2 (by rfl) ⟨7871559, by rfl⟩ : syracuseStep 20990825 = 15743119) B15743119
theorem B143551349 : Blo 1841622 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B24267671 : Blo 1841622 24267671 := bstep (se 1 (by rfl) ⟨18200753, by rfl⟩ : syracuseStep 24267671 = 36401507) B36401507
theorem B2763689 : Blo 1841622 2763689 := bstep (se 2 (by rfl) ⟨1036383, by rfl⟩ : syracuseStep 2763689 = 2072767) B2072767
theorem B2763719 : Blo 1841622 2763719 := bstep (se 1 (by rfl) ⟨2072789, by rfl⟩ : syracuseStep 2763719 = 4145579) B4145579
theorem B2763839 : Blo 1841622 2763839 := bstep (se 1 (by rfl) ⟨2072879, by rfl⟩ : syracuseStep 2763839 = 4145759) B4145759
theorem B16174237 : Blo 1841622 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B2764079 : Blo 1841622 2764079 := bstep (se 1 (by rfl) ⟨2073059, by rfl⟩ : syracuseStep 2764079 = 4146119) B4146119
theorem B21278141 : Blo 1841622 21278141 := bstep (se 3 (by rfl) ⟨3989651, by rfl⟩ : syracuseStep 21278141 = 7979303) B7979303
theorem B2764265 : Blo 1841622 2764265 := bstep (se 2 (by rfl) ⟨1036599, by rfl⟩ : syracuseStep 2764265 = 2073199) B2073199
theorem B8850971 : Blo 1841622 8850971 := bstep (se 1 (by rfl) ⟨6638228, by rfl⟩ : syracuseStep 8850971 = 13276457) B13276457
theorem B2764319 : Blo 1841622 2764319 := bstep (se 1 (by rfl) ⟨2073239, by rfl⟩ : syracuseStep 2764319 = 4146479) B4146479
theorem B2764409 : Blo 1841622 2764409 := bstep (se 2 (by rfl) ⟨1036653, by rfl⟩ : syracuseStep 2764409 = 2073307) B2073307
theorem B2764655 : Blo 1841622 2764655 := bstep (se 1 (by rfl) ⟨2073491, by rfl⟩ : syracuseStep 2764655 = 4146983) B4146983
theorem B8851355 : Blo 1841622 8851355 := bstep (se 1 (by rfl) ⟨6638516, by rfl⟩ : syracuseStep 8851355 = 13277033) B13277033
theorem B6999979 : Blo 1841622 6999979 := bstep (se 1 (by rfl) ⟨5249984, by rfl⟩ : syracuseStep 6999979 = 10499969) B10499969
theorem B23621651 : Blo 1841622 23621651 := bstep (se 1 (by rfl) ⟨17716238, by rfl⟩ : syracuseStep 23621651 = 35432477) B35432477
theorem B6221879 : Blo 1841622 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B2764907 : Blo 1841622 2764907 := bstep (se 1 (by rfl) ⟨2073680, by rfl⟩ : syracuseStep 2764907 = 4147361) B4147361
theorem B10498193 : Blo 1841622 10498193 := bstep (se 2 (by rfl) ⟨3936822, by rfl⟩ : syracuseStep 10498193 = 7873645) B7873645
theorem B201781505 : Blo 1841622 201781505 := bstep (se 2 (by rfl) ⟨75668064, by rfl⟩ : syracuseStep 201781505 = 151336129) B151336129
theorem B2273563 : Blo 1841622 2273563 := bstep (se 1 (by rfl) ⟨1705172, by rfl⟩ : syracuseStep 2273563 = 3410345) B3410345
theorem B5247479 : Blo 1841622 5247479 := bstep (se 1 (by rfl) ⟨3935609, by rfl⟩ : syracuseStep 5247479 = 7871219) B7871219
theorem B4665883 : Blo 1841622 4665883 := bstep (se 1 (by rfl) ⟨3499412, by rfl⟩ : syracuseStep 4665883 = 6998825) B6998825
theorem B2765339 : Blo 1841622 2765339 := bstep (se 1 (by rfl) ⟨2074004, by rfl⟩ : syracuseStep 2765339 = 4148009) B4148009
theorem B2363951 : Blo 1841622 2363951 := bstep (se 1 (by rfl) ⟨1772963, by rfl⟩ : syracuseStep 2363951 = 3545927) B3545927
theorem B40383137 : Blo 1841622 40383137 := bstep (se 2 (by rfl) ⟨15143676, by rfl⟩ : syracuseStep 40383137 = 30287353) B30287353
theorem B16806953 : Blo 1841622 16806953 := bstep (se 2 (by rfl) ⟨6302607, by rfl⟩ : syracuseStep 16806953 = 12605215) B12605215
theorem B4428983 : Blo 1841622 4428983 := bstep (se 1 (by rfl) ⟨3321737, by rfl⟩ : syracuseStep 4428983 = 6643475) B6643475
theorem B5248253 : Blo 1841622 5248253 := bstep (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) B1968095
theorem B47199833 : Blo 1841622 47199833 := bstep (se 2 (by rfl) ⟨17699937, by rfl⟩ : syracuseStep 47199833 = 35399875) B35399875
theorem B31479677 : Blo 1841622 31479677 := bstep (se 3 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 31479677 = 11804879) B11804879
theorem B3110879 : Blo 1841622 3110879 := bstep (se 1 (by rfl) ⟨2333159, by rfl⟩ : syracuseStep 3110879 = 4666319) B4666319
theorem B6305771 : Blo 1841622 6305771 := bstep (se 1 (by rfl) ⟨4729328, by rfl⟩ : syracuseStep 6305771 = 9458657) B9458657
theorem B5249063 : Blo 1841622 5249063 := bstep (se 1 (by rfl) ⟨3936797, by rfl⟩ : syracuseStep 5249063 = 7873595) B7873595
theorem B7469111 : Blo 1841622 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B33634865 : Blo 1841622 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B1841767 : Blo 1841622 1841767 := bstep (se 1 (by rfl) ⟨1381325, by rfl⟩ : syracuseStep 1841767 = 2762651) B2762651
theorem B1841791 : Blo 1841622 1841791 := bstep (se 1 (by rfl) ⟨1381343, by rfl⟩ : syracuseStep 1841791 = 2762687) B2762687
theorem B17709779 : Blo 1841622 17709779 := bstep (se 1 (by rfl) ⟨13282334, by rfl⟩ : syracuseStep 17709779 = 26564669) B26564669
theorem B6216425 : Blo 1841622 6216425 := bstep (se 2 (by rfl) ⟨2331159, by rfl⟩ : syracuseStep 6216425 = 4662319) B4662319
theorem B1841915 : Blo 1841622 1841915 := bstep (se 1 (by rfl) ⟨1381436, by rfl⟩ : syracuseStep 1841915 = 2762873) B2762873
theorem B17947439 : Blo 1841622 17947439 := bstep (se 1 (by rfl) ⟨13460579, by rfl⟩ : syracuseStep 17947439 = 26921159) B26921159
theorem B23616319 : Blo 1841622 23616319 := bstep (se 1 (by rfl) ⟨17712239, by rfl⟩ : syracuseStep 23616319 = 35424479) B35424479
theorem B4143995 : Blo 1841622 4143995 := bstep (se 1 (by rfl) ⟨3107996, by rfl⟩ : syracuseStep 4143995 = 6215993) B6215993
theorem B5258141 : Blo 1841622 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B10492861 : Blo 1841622 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B1842171 : Blo 1841622 1842171 := bstep (se 1 (by rfl) ⟨1381628, by rfl⟩ : syracuseStep 1842171 = 2763257) B2763257
theorem B1842207 : Blo 1841622 1842207 := bstep (se 1 (by rfl) ⟨1381655, by rfl⟩ : syracuseStep 1842207 = 2763311) B2763311
theorem B4144175 : Blo 1841622 4144175 := bstep (se 1 (by rfl) ⟨3108131, by rfl⟩ : syracuseStep 4144175 = 6216263) B6216263
theorem B6995105 : Blo 1841622 6995105 := bstep (se 2 (by rfl) ⟨2623164, by rfl⟩ : syracuseStep 6995105 = 5246329) B5246329
theorem B6216911 : Blo 1841622 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B10493135 : Blo 1841622 10493135 := bstep (se 1 (by rfl) ⟨7869851, by rfl⟩ : syracuseStep 10493135 = 15739703) B15739703
theorem B1842495 : Blo 1841622 1842495 := bstep (se 1 (by rfl) ⟨1381871, by rfl⟩ : syracuseStep 1842495 = 2763743) B2763743
theorem B100834703 : Blo 1841622 100834703 := bstep (se 1 (by rfl) ⟨75626027, by rfl⟩ : syracuseStep 100834703 = 151252055) B151252055
theorem B39861719 : Blo 1841622 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B6217289 : Blo 1841622 6217289 := bstep (se 2 (by rfl) ⟨2331483, by rfl⟩ : syracuseStep 6217289 = 4662967) B4662967
theorem B1842791 : Blo 1841622 1842791 := bstep (se 1 (by rfl) ⟨1382093, by rfl⟩ : syracuseStep 1842791 = 2764187) B2764187
theorem B1843071 : Blo 1841622 1843071 := bstep (se 1 (by rfl) ⟨1382303, by rfl⟩ : syracuseStep 1843071 = 2764607) B2764607
theorem B4980617 : Blo 1841622 4980617 := bstep (se 2 (by rfl) ⟨1867731, by rfl⟩ : syracuseStep 4980617 = 3735463) B3735463
theorem B1843271 : Blo 1841622 1843271 := bstep (se 1 (by rfl) ⟨1382453, by rfl⟩ : syracuseStep 1843271 = 2764907) B2764907
theorem B44818541 : Blo 1841622 44818541 := bstep (se 3 (by rfl) ⟨8403476, by rfl⟩ : syracuseStep 44818541 = 16806953) B16806953
theorem B6996077 : Blo 1841622 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B134521003 : Blo 1841622 134521003 := bstep (se 1 (by rfl) ⟨100890752, by rfl⟩ : syracuseStep 134521003 = 201781505) B201781505
theorem B3498319 : Blo 1841622 3498319 := bstep (se 1 (by rfl) ⟨2623739, by rfl⟩ : syracuseStep 3498319 = 5247479) B5247479
theorem B1843559 : Blo 1841622 1843559 := bstep (se 1 (by rfl) ⟨1382669, by rfl⟩ : syracuseStep 1843559 = 2765339) B2765339
theorem B3031417 : Blo 1841622 3031417 := bstep (se 2 (by rfl) ⟨1136781, by rfl⟩ : syracuseStep 3031417 = 2273563) B2273563
theorem B9331361 : Blo 1841622 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B28361495 : Blo 1841622 28361495 := bstep (se 1 (by rfl) ⟨21271121, by rfl⟩ : syracuseStep 28361495 = 42542243) B42542243
theorem B3498889 : Blo 1841622 3498889 := bstep (se 2 (by rfl) ⟨1312083, by rfl⟩ : syracuseStep 3498889 = 2624167) B2624167
theorem B31466555 : Blo 1841622 31466555 := bstep (se 1 (by rfl) ⟨23599916, by rfl⟩ : syracuseStep 31466555 = 47199833) B47199833
theorem B11207945 : Blo 1841622 11207945 := bstep (se 2 (by rfl) ⟨4202979, by rfl⟩ : syracuseStep 11207945 = 8405959) B8405959
theorem B2073919 : Blo 1841622 2073919 := bstep (se 1 (by rfl) ⟨1555439, by rfl⟩ : syracuseStep 2073919 = 3110879) B3110879
theorem B4203847 : Blo 1841622 4203847 := bstep (se 1 (by rfl) ⟨3152885, by rfl⟩ : syracuseStep 4203847 = 6305771) B6305771
theorem B3499375 : Blo 1841622 3499375 := bstep (se 1 (by rfl) ⟨2624531, by rfl⟩ : syracuseStep 3499375 = 5249063) B5249063
theorem B3933679 : Blo 1841622 3933679 := bstep (se 1 (by rfl) ⟨2950259, by rfl⟩ : syracuseStep 3933679 = 5900519) B5900519
theorem B22423243 : Blo 1841622 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B13993883 : Blo 1841622 13993883 := bstep (se 1 (by rfl) ⟨10495412, by rfl⟩ : syracuseStep 13993883 = 20990825) B20990825
theorem B95700899 : Blo 1841622 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B2762663 : Blo 1841622 2762663 := bstep (se 1 (by rfl) ⟨2071997, by rfl⟩ : syracuseStep 2762663 = 4143995) B4143995
theorem B2762783 : Blo 1841622 2762783 := bstep (se 1 (by rfl) ⟨2072087, by rfl⟩ : syracuseStep 2762783 = 4144175) B4144175
theorem B4663403 : Blo 1841622 4663403 := bstep (se 1 (by rfl) ⟨3497552, by rfl⟩ : syracuseStep 4663403 = 6995105) B6995105
theorem B5900647 : Blo 1841622 5900647 := bstep (se 1 (by rfl) ⟨4425485, by rfl⟩ : syracuseStep 5900647 = 8850971) B8850971
theorem B9333305 : Blo 1841622 9333305 := bstep (se 2 (by rfl) ⟨3499989, by rfl⟩ : syracuseStep 9333305 = 6999979) B6999979
theorem B3320411 : Blo 1841622 3320411 := bstep (se 1 (by rfl) ⟨2490308, by rfl⟩ : syracuseStep 3320411 = 4980617) B4980617
theorem B5900903 : Blo 1841622 5900903 := bstep (se 1 (by rfl) ⟨4425677, by rfl⟩ : syracuseStep 5900903 = 8851355) B8851355
theorem B15747767 : Blo 1841622 15747767 := bstep (se 1 (by rfl) ⟨11810825, by rfl⟩ : syracuseStep 15747767 = 23621651) B23621651
theorem B4147919 : Blo 1841622 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B6998795 : Blo 1841622 6998795 := bstep (se 1 (by rfl) ⟨5249096, by rfl⟩ : syracuseStep 6998795 = 10498193) B10498193
theorem B2763641 : Blo 1841622 2763641 := bstep (se 2 (by rfl) ⟨1036365, by rfl⟩ : syracuseStep 2763641 = 2072731) B2072731
theorem B4664375 : Blo 1841622 4664375 := bstep (se 1 (by rfl) ⟨3498281, by rfl⟩ : syracuseStep 4664375 = 6996563) B6996563
theorem B26922091 : Blo 1841622 26922091 := bstep (se 1 (by rfl) ⟨20191568, by rfl⟩ : syracuseStep 26922091 = 40383137) B40383137
theorem B6221015 : Blo 1841622 6221015 := bstep (se 1 (by rfl) ⟨4665761, by rfl⟩ : syracuseStep 6221015 = 9331523) B9331523
theorem B3108071 : Blo 1841622 3108071 := bstep (se 1 (by rfl) ⟨2331053, by rfl⟩ : syracuseStep 3108071 = 4662107) B4662107
theorem B13995341 : Blo 1841622 13995341 := bstep (se 3 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 13995341 = 5248253) B5248253
theorem B6221177 : Blo 1841622 6221177 := bstep (se 2 (by rfl) ⟨2332941, by rfl⟩ : syracuseStep 6221177 = 4665883) B4665883
theorem B3108287 : Blo 1841622 3108287 := bstep (se 1 (by rfl) ⟨2331215, by rfl⟩ : syracuseStep 3108287 = 4662431) B4662431
theorem B2952655 : Blo 1841622 2952655 := bstep (se 1 (by rfl) ⟨2214491, by rfl⟩ : syracuseStep 2952655 = 4428983) B4428983
theorem B4664911 : Blo 1841622 4664911 := bstep (se 1 (by rfl) ⟨3498683, by rfl⟩ : syracuseStep 4664911 = 6997367) B6997367
theorem B3108719 : Blo 1841622 3108719 := bstep (se 1 (by rfl) ⟨2331539, by rfl⟩ : syracuseStep 3108719 = 4663079) B4663079
theorem B4665215 : Blo 1841622 4665215 := bstep (se 1 (by rfl) ⟨3498911, by rfl⟩ : syracuseStep 4665215 = 6997823) B6997823
theorem B3321911 : Blo 1841622 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B4042855 : Blo 1841622 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B6303869 : Blo 1841622 6303869 := bstep (se 3 (by rfl) ⟨1181975, by rfl⟩ : syracuseStep 6303869 = 2363951) B2363951
theorem B21565649 : Blo 1841622 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B4665559 : Blo 1841622 4665559 := bstep (se 1 (by rfl) ⟨3499169, by rfl⟩ : syracuseStep 4665559 = 6998339) B6998339
theorem B3109279 : Blo 1841622 3109279 := bstep (se 1 (by rfl) ⟨2331959, by rfl⟩ : syracuseStep 3109279 = 4663919) B4663919
theorem B2765291 : Blo 1841622 2765291 := bstep (se 1 (by rfl) ⟨2073968, by rfl⟩ : syracuseStep 2765291 = 4147937) B4147937
theorem B11964959 : Blo 1841622 11964959 := bstep (se 1 (by rfl) ⟨8973719, by rfl⟩ : syracuseStep 11964959 = 17947439) B17947439
theorem B2765417 : Blo 1841622 2765417 := bstep (se 2 (by rfl) ⟨1037031, by rfl⟩ : syracuseStep 2765417 = 2074063) B2074063
theorem B14185427 : Blo 1841622 14185427 := bstep (se 1 (by rfl) ⟨10639070, by rfl⟩ : syracuseStep 14185427 = 21278141) B21278141
theorem B6215507 : Blo 1841622 6215507 := bstep (se 1 (by rfl) ⟨4661630, by rfl⟩ : syracuseStep 6215507 = 9323261) B9323261
theorem B34084883 : Blo 1841622 34084883 := bstep (se 1 (by rfl) ⟨25563662, by rfl⟩ : syracuseStep 34084883 = 51127325) B51127325
theorem B31488425 : Blo 1841622 31488425 := bstep (se 2 (by rfl) ⟨11808159, by rfl⟩ : syracuseStep 31488425 = 23616319) B23616319
theorem B1841647 : Blo 1841622 1841647 := bstep (se 1 (by rfl) ⟨1381235, by rfl⟩ : syracuseStep 1841647 = 2762471) B2762471
theorem B1841711 : Blo 1841622 1841711 := bstep (se 1 (by rfl) ⟨1381283, by rfl⟩ : syracuseStep 1841711 = 2762567) B2762567
theorem B13990481 : Blo 1841622 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B20986451 : Blo 1841622 20986451 := bstep (se 1 (by rfl) ⟨15739838, by rfl⟩ : syracuseStep 20986451 = 31479677) B31479677
theorem B5905055 : Blo 1841622 5905055 := bstep (se 1 (by rfl) ⟨4428791, by rfl⟩ : syracuseStep 5905055 = 8857583) B8857583
theorem B4979407 : Blo 1841622 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B1841983 : Blo 1841622 1841983 := bstep (se 1 (by rfl) ⟨1381487, by rfl⟩ : syracuseStep 1841983 = 2762975) B2762975
theorem B1842023 : Blo 1841622 1842023 := bstep (se 1 (by rfl) ⟨1381517, by rfl⟩ : syracuseStep 1842023 = 2763035) B2763035
theorem B1842111 : Blo 1841622 1842111 := bstep (se 1 (by rfl) ⟨1381583, by rfl⟩ : syracuseStep 1842111 = 2763167) B2763167
theorem B1842239 : Blo 1841622 1842239 := bstep (se 1 (by rfl) ⟨1381679, by rfl⟩ : syracuseStep 1842239 = 2763359) B2763359
theorem B4144283 : Blo 1841622 4144283 := bstep (se 1 (by rfl) ⟨3108212, by rfl⟩ : syracuseStep 4144283 = 6216425) B6216425
theorem B47226077 : Blo 1841622 47226077 := bstep (se 3 (by rfl) ⟨8854889, by rfl⟩ : syracuseStep 47226077 = 17709779) B17709779
theorem B16178447 : Blo 1841622 16178447 := bstep (se 1 (by rfl) ⟨12133835, by rfl⟩ : syracuseStep 16178447 = 24267671) B24267671
theorem B3505427 : Blo 1841622 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B1842459 : Blo 1841622 1842459 := bstep (se 1 (by rfl) ⟨1381844, by rfl⟩ : syracuseStep 1842459 = 2763689) B2763689
theorem B1842479 : Blo 1841622 1842479 := bstep (se 1 (by rfl) ⟨1381859, by rfl⟩ : syracuseStep 1842479 = 2763719) B2763719
theorem B1842559 : Blo 1841622 1842559 := bstep (se 1 (by rfl) ⟨1381919, by rfl⟩ : syracuseStep 1842559 = 2763839) B2763839
theorem B4144607 : Blo 1841622 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B6995423 : Blo 1841622 6995423 := bstep (se 1 (by rfl) ⟨5246567, by rfl⟩ : syracuseStep 6995423 = 10493135) B10493135
theorem B1842719 : Blo 1841622 1842719 := bstep (se 1 (by rfl) ⟨1382039, by rfl⟩ : syracuseStep 1842719 = 2764079) B2764079
theorem B67223135 : Blo 1841622 67223135 := bstep (se 1 (by rfl) ⟨50417351, by rfl⟩ : syracuseStep 67223135 = 100834703) B100834703
theorem B26574479 : Blo 1841622 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B1842843 : Blo 1841622 1842843 := bstep (se 1 (by rfl) ⟨1382132, by rfl⟩ : syracuseStep 1842843 = 2764265) B2764265
theorem B1842879 : Blo 1841622 1842879 := bstep (se 1 (by rfl) ⟨1382159, by rfl⟩ : syracuseStep 1842879 = 2764319) B2764319
theorem B4144859 : Blo 1841622 4144859 := bstep (se 1 (by rfl) ⟨3108644, by rfl⟩ : syracuseStep 4144859 = 6217289) B6217289
theorem B1842939 : Blo 1841622 1842939 := bstep (se 1 (by rfl) ⟨1382204, by rfl⟩ : syracuseStep 1842939 = 2764409) B2764409
theorem B1843103 : Blo 1841622 1843103 := bstep (se 1 (by rfl) ⟨1382327, by rfl⟩ : syracuseStep 1843103 = 2764655) B2764655
theorem B4202579 : Blo 1841622 4202579 := bstep (se 1 (by rfl) ⟨3151934, by rfl⟩ : syracuseStep 4202579 = 6303869) B6303869
theorem B5390473 : Blo 1841622 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B14377099 : Blo 1841622 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B1843527 : Blo 1841622 1843527 := bstep (se 1 (by rfl) ⟨1382645, by rfl⟩ : syracuseStep 1843527 = 2765291) B2765291
theorem B1843611 : Blo 1841622 1843611 := bstep (se 1 (by rfl) ⟨1382708, by rfl⟩ : syracuseStep 1843611 = 2765417) B2765417
theorem B18907663 : Blo 1841622 18907663 := bstep (se 1 (by rfl) ⟨14180747, by rfl⟩ : syracuseStep 18907663 = 28361495) B28361495
theorem B4145705 : Blo 1841622 4145705 := bstep (se 2 (by rfl) ⟨1554639, by rfl⟩ : syracuseStep 4145705 = 3109279) B3109279
theorem B7471963 : Blo 1841622 7471963 := bstep (se 1 (by rfl) ⟨5603972, by rfl⟩ : syracuseStep 7471963 = 11207945) B11207945
theorem B3933935 : Blo 1841622 3933935 := bstep (se 1 (by rfl) ⟨2950451, by rfl⟩ : syracuseStep 3933935 = 5900903) B5900903
theorem B5605129 : Blo 1841622 5605129 := bstep (se 2 (by rfl) ⟨2101923, by rfl⟩ : syracuseStep 5605129 = 4203847) B4203847
theorem B5244905 : Blo 1841622 5244905 := bstep (se 2 (by rfl) ⟨1966839, by rfl⟩ : syracuseStep 5244905 = 3933679) B3933679
theorem B2762855 : Blo 1841622 2762855 := bstep (se 1 (by rfl) ⟨2072141, by rfl⟩ : syracuseStep 2762855 = 4144283) B4144283
theorem B6219881 : Blo 1841622 6219881 := bstep (se 2 (by rfl) ⟨2332455, by rfl⟩ : syracuseStep 6219881 = 4664911) B4664911
theorem B4147343 : Blo 1841622 4147343 := bstep (se 1 (by rfl) ⟨3110507, by rfl⟩ : syracuseStep 4147343 = 6221015) B6221015
theorem B31484051 : Blo 1841622 31484051 := bstep (se 1 (by rfl) ⟨23613038, by rfl⟩ : syracuseStep 31484051 = 47226077) B47226077
theorem B2336951 : Blo 1841622 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B4147451 : Blo 1841622 4147451 := bstep (se 1 (by rfl) ⟨3110588, by rfl⟩ : syracuseStep 4147451 = 6221177) B6221177
theorem B2763071 : Blo 1841622 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B4663615 : Blo 1841622 4663615 := bstep (se 1 (by rfl) ⟨3497711, by rfl⟩ : syracuseStep 4663615 = 6995423) B6995423
theorem B15747493 : Blo 1841622 15747493 := bstep (se 4 (by rfl) ⟨1476327, by rfl⟩ : syracuseStep 15747493 = 2952655) B2952655
theorem B2763239 : Blo 1841622 2763239 := bstep (se 1 (by rfl) ⟨2072429, by rfl⟩ : syracuseStep 2763239 = 4144859) B4144859
theorem B29879027 : Blo 1841622 29879027 := bstep (se 1 (by rfl) ⟨22409270, by rfl⟩ : syracuseStep 29879027 = 44818541) B44818541
theorem B4664051 : Blo 1841622 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B8858429 : Blo 1841622 8858429 := bstep (se 3 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 8858429 = 3321911) B3321911
theorem B6220745 : Blo 1841622 6220745 := bstep (se 2 (by rfl) ⟨2332779, by rfl⟩ : syracuseStep 6220745 = 4665559) B4665559
theorem B4664425 : Blo 1841622 4664425 := bstep (se 2 (by rfl) ⟨1749159, by rfl⟩ : syracuseStep 4664425 = 3498319) B3498319
theorem B6220907 : Blo 1841622 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B7867529 : Blo 1841622 7867529 := bstep (se 2 (by rfl) ⟨2950323, by rfl⟩ : syracuseStep 7867529 = 5900647) B5900647
theorem B6639209 : Blo 1841622 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B4665185 : Blo 1841622 4665185 := bstep (se 2 (by rfl) ⟨1749444, by rfl⟩ : syracuseStep 4665185 = 3498889) B3498889
theorem B3108935 : Blo 1841622 3108935 := bstep (se 1 (by rfl) ⟨2331701, by rfl⟩ : syracuseStep 3108935 = 4663403) B4663403
theorem B179261693 : Blo 1841622 179261693 := bstep (se 3 (by rfl) ⟨33611567, by rfl⟩ : syracuseStep 179261693 = 67223135) B67223135
theorem B20992283 : Blo 1841622 20992283 := bstep (se 1 (by rfl) ⟨15744212, by rfl⟩ : syracuseStep 20992283 = 31488425) B31488425
theorem B6222203 : Blo 1841622 6222203 := bstep (se 1 (by rfl) ⟨4666652, by rfl⟩ : syracuseStep 6222203 = 9333305) B9333305
theorem B9326987 : Blo 1841622 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B2765225 : Blo 1841622 2765225 := bstep (se 2 (by rfl) ⟨1036959, by rfl⟩ : syracuseStep 2765225 = 2073919) B2073919
theorem B3936703 : Blo 1841622 3936703 := bstep (se 1 (by rfl) ⟨2952527, by rfl⟩ : syracuseStep 3936703 = 5905055) B5905055
theorem B10498511 : Blo 1841622 10498511 := bstep (se 1 (by rfl) ⟨7873883, by rfl⟩ : syracuseStep 10498511 = 15747767) B15747767
theorem B2765279 : Blo 1841622 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B4665833 : Blo 1841622 4665833 := bstep (se 2 (by rfl) ⟨1749687, by rfl⟩ : syracuseStep 4665833 = 3499375) B3499375
theorem B4665863 : Blo 1841622 4665863 := bstep (se 1 (by rfl) ⟨3499397, by rfl⟩ : syracuseStep 4665863 = 6998795) B6998795
theorem B16167557 : Blo 1841622 16167557 := bstep (se 4 (by rfl) ⟨1515708, by rfl⟩ : syracuseStep 16167557 = 3031417) B3031417
theorem B3109583 : Blo 1841622 3109583 := bstep (se 1 (by rfl) ⟨2332187, by rfl⟩ : syracuseStep 3109583 = 4664375) B4664375
theorem B10785631 : Blo 1841622 10785631 := bstep (se 1 (by rfl) ⟨8089223, by rfl⟩ : syracuseStep 10785631 = 16178447) B16178447
theorem B29897657 : Blo 1841622 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B255202397 : Blo 1841622 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B17716319 : Blo 1841622 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B37827805 : Blo 1841622 37827805 := bstep (se 3 (by rfl) ⟨7092713, by rfl⟩ : syracuseStep 37827805 = 14185427) B14185427
theorem B3110143 : Blo 1841622 3110143 := bstep (se 1 (by rfl) ⟨2332607, by rfl⟩ : syracuseStep 3110143 = 4665215) B4665215
theorem B179361337 : Blo 1841622 179361337 := bstep (se 2 (by rfl) ⟨67260501, by rfl⟩ : syracuseStep 179361337 = 134521003) B134521003
theorem B7976639 : Blo 1841622 7976639 := bstep (se 1 (by rfl) ⟨5982479, by rfl⟩ : syracuseStep 7976639 = 11964959) B11964959
theorem B20977703 : Blo 1841622 20977703 := bstep (se 1 (by rfl) ⟨15733277, by rfl⟩ : syracuseStep 20977703 = 31466555) B31466555
theorem B4143671 : Blo 1841622 4143671 := bstep (se 1 (by rfl) ⟨3107753, by rfl⟩ : syracuseStep 4143671 = 6215507) B6215507
theorem B9329255 : Blo 1841622 9329255 := bstep (se 1 (by rfl) ⟨6996941, by rfl⟩ : syracuseStep 9329255 = 13993883) B13993883
theorem B1841775 : Blo 1841622 1841775 := bstep (se 1 (by rfl) ⟨1381331, by rfl⟩ : syracuseStep 1841775 = 2762663) B2762663
theorem B22723255 : Blo 1841622 22723255 := bstep (se 1 (by rfl) ⟨17042441, by rfl⟩ : syracuseStep 22723255 = 34084883) B34084883
theorem B1841855 : Blo 1841622 1841855 := bstep (se 1 (by rfl) ⟨1381391, by rfl⟩ : syracuseStep 1841855 = 2762783) B2762783
theorem B35896121 : Blo 1841622 35896121 := bstep (se 2 (by rfl) ⟨13461045, by rfl⟩ : syracuseStep 35896121 = 26922091) B26922091
theorem B8854429 : Blo 1841622 8854429 := bstep (se 3 (by rfl) ⟨1660205, by rfl⟩ : syracuseStep 8854429 = 3320411) B3320411
theorem B13990967 : Blo 1841622 13990967 := bstep (se 1 (by rfl) ⟨10493225, by rfl⟩ : syracuseStep 13990967 = 20986451) B20986451
theorem B1842427 : Blo 1841622 1842427 := bstep (se 1 (by rfl) ⟨1381820, by rfl⟩ : syracuseStep 1842427 = 2763641) B2763641
theorem B2072047 : Blo 1841622 2072047 := bstep (se 1 (by rfl) ⟨1554035, by rfl⟩ : syracuseStep 2072047 = 3108071) B3108071
theorem B9330227 : Blo 1841622 9330227 := bstep (se 1 (by rfl) ⟨6997670, by rfl⟩ : syracuseStep 9330227 = 13995341) B13995341
theorem B2072191 : Blo 1841622 2072191 := bstep (se 1 (by rfl) ⟨1554143, by rfl⟩ : syracuseStep 2072191 = 3108287) B3108287
theorem B2072479 : Blo 1841622 2072479 := bstep (se 1 (by rfl) ⟨1554359, by rfl⟩ : syracuseStep 2072479 = 3108719) B3108719
theorem B2072623 : Blo 1841622 2072623 := bstep (se 1 (by rfl) ⟨1554467, by rfl⟩ : syracuseStep 2072623 = 3108935) B3108935
theorem B2801719 : Blo 1841622 2801719 := bstep (se 1 (by rfl) ⟨2101289, by rfl⟩ : syracuseStep 2801719 = 4202579) B4202579
theorem B19169465 : Blo 1841622 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B6217991 : Blo 1841622 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B1843483 : Blo 1841622 1843483 := bstep (se 1 (by rfl) ⟨1382612, by rfl⟩ : syracuseStep 1843483 = 2765225) B2765225
theorem B1843519 : Blo 1841622 1843519 := bstep (se 1 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 1843519 = 2765279) B2765279
theorem B6218153 : Blo 1841622 6218153 := bstep (se 2 (by rfl) ⟨2331807, by rfl⟩ : syracuseStep 6218153 = 4663615) B4663615
theorem B2073055 : Blo 1841622 2073055 := bstep (se 1 (by rfl) ⟨1554791, by rfl⟩ : syracuseStep 2073055 = 3109583) B3109583
theorem B20996657 : Blo 1841622 20996657 := bstep (se 2 (by rfl) ⟨7873746, by rfl⟩ : syracuseStep 20996657 = 15747493) B15747493
theorem B19931771 : Blo 1841622 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B9962617 : Blo 1841622 9962617 := bstep (se 2 (by rfl) ⟨3735981, by rfl⟩ : syracuseStep 9962617 = 7471963) B7471963
theorem B5317759 : Blo 1841622 5317759 := bstep (se 1 (by rfl) ⟨3988319, by rfl⟩ : syracuseStep 5317759 = 7976639) B7976639
theorem B2622623 : Blo 1841622 2622623 := bstep (se 1 (by rfl) ⟨1966967, by rfl⟩ : syracuseStep 2622623 = 3933935) B3933935
theorem B11805905 : Blo 1841622 11805905 := bstep (se 2 (by rfl) ⟨4427214, by rfl⟩ : syracuseStep 11805905 = 8854429) B8854429
theorem B13985135 : Blo 1841622 13985135 := bstep (se 1 (by rfl) ⟨10488851, by rfl⟩ : syracuseStep 13985135 = 20977703) B20977703
theorem B29894021 : Blo 1841622 29894021 := bstep (se 4 (by rfl) ⟨2802564, by rfl⟩ : syracuseStep 29894021 = 5605129) B5605129
theorem B4146587 : Blo 1841622 4146587 := bstep (se 1 (by rfl) ⟨3109940, by rfl⟩ : syracuseStep 4146587 = 6219881) B6219881
theorem B20989367 : Blo 1841622 20989367 := bstep (se 1 (by rfl) ⟨15742025, by rfl⟩ : syracuseStep 20989367 = 31484051) B31484051
theorem B6219233 : Blo 1841622 6219233 := bstep (se 2 (by rfl) ⟨2332212, by rfl⟩ : syracuseStep 6219233 = 4664425) B4664425
theorem B4146857 : Blo 1841622 4146857 := bstep (se 2 (by rfl) ⟨1555071, by rfl⟩ : syracuseStep 4146857 = 3110143) B3110143
theorem B2762447 : Blo 1841622 2762447 := bstep (se 1 (by rfl) ⟨2071835, by rfl⟩ : syracuseStep 2762447 = 4143671) B4143671
theorem B6219503 : Blo 1841622 6219503 := bstep (se 1 (by rfl) ⟨4664627, by rfl⟩ : syracuseStep 6219503 = 9329255) B9329255
theorem B23930747 : Blo 1841622 23930747 := bstep (se 1 (by rfl) ⟨17948060, by rfl⟩ : syracuseStep 23930747 = 35896121) B35896121
theorem B4147163 : Blo 1841622 4147163 := bstep (se 1 (by rfl) ⟨3110372, by rfl⟩ : syracuseStep 4147163 = 6220745) B6220745
theorem B2762729 : Blo 1841622 2762729 := bstep (se 2 (by rfl) ⟨1036023, by rfl⟩ : syracuseStep 2762729 = 2072047) B2072047
theorem B4147271 : Blo 1841622 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B5245019 : Blo 1841622 5245019 := bstep (se 1 (by rfl) ⟨3933764, by rfl⟩ : syracuseStep 5245019 = 7867529) B7867529
theorem B2762921 : Blo 1841622 2762921 := bstep (se 2 (by rfl) ⟨1036095, by rfl⟩ : syracuseStep 2762921 = 2072191) B2072191
theorem B6220151 : Blo 1841622 6220151 := bstep (se 1 (by rfl) ⟨4665113, by rfl⟩ : syracuseStep 6220151 = 9330227) B9330227
theorem B4426139 : Blo 1841622 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B2763305 : Blo 1841622 2763305 := bstep (se 2 (by rfl) ⟨1036239, by rfl⟩ : syracuseStep 2763305 = 2072479) B2072479
theorem B119507795 : Blo 1841622 119507795 := bstep (se 1 (by rfl) ⟨89630846, by rfl⟩ : syracuseStep 119507795 = 179261693) B179261693
theorem B7187297 : Blo 1841622 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B13994855 : Blo 1841622 13994855 := bstep (se 1 (by rfl) ⟨10496141, by rfl⟩ : syracuseStep 13994855 = 20992283) B20992283
theorem B4148135 : Blo 1841622 4148135 := bstep (se 1 (by rfl) ⟨3111101, by rfl⟩ : syracuseStep 4148135 = 6222203) B6222203
theorem B6999007 : Blo 1841622 6999007 := bstep (se 1 (by rfl) ⟨5249255, by rfl⟩ : syracuseStep 6999007 = 10498511) B10498511
theorem B2763803 : Blo 1841622 2763803 := bstep (se 1 (by rfl) ⟨2072852, by rfl⟩ : syracuseStep 2763803 = 4145705) B4145705
theorem B25210217 : Blo 1841622 25210217 := bstep (se 2 (by rfl) ⟨9453831, by rfl⟩ : syracuseStep 25210217 = 18907663) B18907663
theorem B170134931 : Blo 1841622 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B30297673 : Blo 1841622 30297673 := bstep (se 2 (by rfl) ⟨11361627, by rfl⟩ : syracuseStep 30297673 = 22723255) B22723255
theorem B14380841 : Blo 1841622 14380841 := bstep (se 2 (by rfl) ⟨5392815, by rfl⟩ : syracuseStep 14380841 = 10785631) B10785631
theorem B2764895 : Blo 1841622 2764895 := bstep (se 1 (by rfl) ⟨2073671, by rfl⟩ : syracuseStep 2764895 = 4147343) B4147343
theorem B2764967 : Blo 1841622 2764967 := bstep (se 1 (by rfl) ⟨2073725, by rfl⟩ : syracuseStep 2764967 = 4147451) B4147451
theorem B19919351 : Blo 1841622 19919351 := bstep (se 1 (by rfl) ⟨14939513, by rfl⟩ : syracuseStep 19919351 = 29879027) B29879027
theorem B3109367 : Blo 1841622 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B9327311 : Blo 1841622 9327311 := bstep (se 1 (by rfl) ⟨6995483, by rfl⟩ : syracuseStep 9327311 = 13990967) B13990967
theorem B3110123 : Blo 1841622 3110123 := bstep (se 1 (by rfl) ⟨2332592, by rfl⟩ : syracuseStep 3110123 = 4665185) B4665185
theorem B3110555 : Blo 1841622 3110555 := bstep (se 1 (by rfl) ⟨2332916, by rfl⟩ : syracuseStep 3110555 = 4665833) B4665833
theorem B3110575 : Blo 1841622 3110575 := bstep (se 1 (by rfl) ⟨2332931, by rfl⟩ : syracuseStep 3110575 = 4665863) B4665863
theorem B6231869 : Blo 1841622 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B5248937 : Blo 1841622 5248937 := bstep (se 2 (by rfl) ⟨1968351, by rfl⟩ : syracuseStep 5248937 = 3936703) B3936703
theorem B11810879 : Blo 1841622 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B3496603 : Blo 1841622 3496603 := bstep (se 1 (by rfl) ⟨2622452, by rfl⟩ : syracuseStep 3496603 = 5244905) B5244905
theorem B1841903 : Blo 1841622 1841903 := bstep (se 1 (by rfl) ⟨1381427, by rfl⟩ : syracuseStep 1841903 = 2762855) B2762855
theorem B1842047 : Blo 1841622 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B50437073 : Blo 1841622 50437073 := bstep (se 2 (by rfl) ⟨18913902, by rfl⟩ : syracuseStep 50437073 = 37827805) B37827805
theorem B1842159 : Blo 1841622 1842159 := bstep (se 1 (by rfl) ⟨1381619, by rfl⟩ : syracuseStep 1842159 = 2763239) B2763239
theorem B43113485 : Blo 1841622 43113485 := bstep (se 3 (by rfl) ⟨8083778, by rfl⟩ : syracuseStep 43113485 = 16167557) B16167557
theorem B5905619 : Blo 1841622 5905619 := bstep (se 1 (by rfl) ⟨4429214, by rfl⟩ : syracuseStep 5905619 = 8858429) B8858429
theorem B239148449 : Blo 1841622 239148449 := bstep (se 2 (by rfl) ⟨89680668, by rfl⟩ : syracuseStep 239148449 = 179361337) B179361337
theorem B1843263 : Blo 1841622 1843263 := bstep (se 1 (by rfl) ⟨1382447, by rfl⟩ : syracuseStep 1843263 = 2764895) B2764895
theorem B1843311 : Blo 1841622 1843311 := bstep (se 1 (by rfl) ⟨1382483, by rfl⟩ : syracuseStep 1843311 = 2764967) B2764967
theorem B4145327 : Blo 1841622 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B4145435 : Blo 1841622 4145435 := bstep (se 1 (by rfl) ⟨3109076, by rfl⟩ : syracuseStep 4145435 = 6218153) B6218153
theorem B14942501 : Blo 1841622 14942501 := bstep (se 4 (by rfl) ⟨1400859, by rfl⟩ : syracuseStep 14942501 = 2801719) B2801719
theorem B13279567 : Blo 1841622 13279567 := bstep (se 1 (by rfl) ⟨9959675, by rfl⟩ : syracuseStep 13279567 = 19919351) B19919351
theorem B2072911 : Blo 1841622 2072911 := bstep (se 1 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 2072911 = 3109367) B3109367
theorem B13287847 : Blo 1841622 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B6218207 : Blo 1841622 6218207 := bstep (se 1 (by rfl) ⟨4663655, by rfl⟩ : syracuseStep 6218207 = 9327311) B9327311
theorem B51118573 : Blo 1841622 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B2073415 : Blo 1841622 2073415 := bstep (se 1 (by rfl) ⟨1555061, by rfl⟩ : syracuseStep 2073415 = 3110123) B3110123
theorem B4662137 : Blo 1841622 4662137 := bstep (se 2 (by rfl) ⟨1748301, by rfl⟩ : syracuseStep 4662137 = 3496603) B3496603
theorem B9323423 : Blo 1841622 9323423 := bstep (se 1 (by rfl) ⟨6992567, by rfl⟩ : syracuseStep 9323423 = 13985135) B13985135
theorem B13992911 : Blo 1841622 13992911 := bstep (se 1 (by rfl) ⟨10494683, by rfl⟩ : syracuseStep 13992911 = 20989367) B20989367
theorem B4146155 : Blo 1841622 4146155 := bstep (se 1 (by rfl) ⟨3109616, by rfl⟩ : syracuseStep 4146155 = 6219233) B6219233
theorem B2073703 : Blo 1841622 2073703 := bstep (se 1 (by rfl) ⟨1555277, by rfl⟩ : syracuseStep 2073703 = 3110555) B3110555
theorem B4146335 : Blo 1841622 4146335 := bstep (se 1 (by rfl) ⟨3109751, by rfl⟩ : syracuseStep 4146335 = 6219503) B6219503
theorem B4154579 : Blo 1841622 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B3499291 : Blo 1841622 3499291 := bstep (se 1 (by rfl) ⟨2624468, by rfl⟩ : syracuseStep 3499291 = 5248937) B5248937
theorem B9332009 : Blo 1841622 9332009 := bstep (se 2 (by rfl) ⟨3499503, by rfl⟩ : syracuseStep 9332009 = 6999007) B6999007
theorem B7873919 : Blo 1841622 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B4146767 : Blo 1841622 4146767 := bstep (se 1 (by rfl) ⟨3110075, by rfl⟩ : syracuseStep 4146767 = 6220151) B6220151
theorem B2950759 : Blo 1841622 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B40396897 : Blo 1841622 40396897 := bstep (se 2 (by rfl) ⟨15148836, by rfl⟩ : syracuseStep 40396897 = 30297673) B30297673
theorem B38348909 : Blo 1841622 38348909 := bstep (se 3 (by rfl) ⟨7190420, by rfl⟩ : syracuseStep 38348909 = 14380841) B14380841
theorem B4147433 : Blo 1841622 4147433 := bstep (se 2 (by rfl) ⟨1555287, by rfl⟩ : syracuseStep 4147433 = 3110575) B3110575
theorem B114969293 : Blo 1841622 114969293 := bstep (se 3 (by rfl) ⟨21556742, by rfl⟩ : syracuseStep 114969293 = 43113485) B43113485
theorem B2763497 : Blo 1841622 2763497 := bstep (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) B2072623
theorem B2764073 : Blo 1841622 2764073 := bstep (se 2 (by rfl) ⟨1036527, by rfl⟩ : syracuseStep 2764073 = 2073055) B2073055
theorem B2764391 : Blo 1841622 2764391 := bstep (se 1 (by rfl) ⟨2073293, by rfl⟩ : syracuseStep 2764391 = 4146587) B4146587
theorem B76664501 : Blo 1841622 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B2764571 : Blo 1841622 2764571 := bstep (se 1 (by rfl) ⟨2073428, by rfl⟩ : syracuseStep 2764571 = 4146857) B4146857
theorem B15953831 : Blo 1841622 15953831 := bstep (se 1 (by rfl) ⟨11965373, by rfl⟩ : syracuseStep 15953831 = 23930747) B23930747
theorem B2764775 : Blo 1841622 2764775 := bstep (se 1 (by rfl) ⟨2073581, by rfl⟩ : syracuseStep 2764775 = 4147163) B4147163
theorem B2764847 : Blo 1841622 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B13283489 : Blo 1841622 13283489 := bstep (se 2 (by rfl) ⟨4981308, by rfl⟩ : syracuseStep 13283489 = 9962617) B9962617
theorem B7090345 : Blo 1841622 7090345 := bstep (se 2 (by rfl) ⟨2658879, by rfl⟩ : syracuseStep 7090345 = 5317759) B5317759
theorem B79671863 : Blo 1841622 79671863 := bstep (se 1 (by rfl) ⟨59753897, by rfl⟩ : syracuseStep 79671863 = 119507795) B119507795
theorem B2765423 : Blo 1841622 2765423 := bstep (se 1 (by rfl) ⟨2074067, by rfl⟩ : syracuseStep 2765423 = 4148135) B4148135
theorem B33624715 : Blo 1841622 33624715 := bstep (se 1 (by rfl) ⟨25218536, by rfl⟩ : syracuseStep 33624715 = 50437073) B50437073
theorem B3937079 : Blo 1841622 3937079 := bstep (se 1 (by rfl) ⟨2952809, by rfl⟩ : syracuseStep 3937079 = 5905619) B5905619
theorem B16806811 : Blo 1841622 16806811 := bstep (se 1 (by rfl) ⟨12605108, by rfl⟩ : syracuseStep 16806811 = 25210217) B25210217
theorem B113423287 : Blo 1841622 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B13997771 : Blo 1841622 13997771 := bstep (se 1 (by rfl) ⟨10498328, by rfl⟩ : syracuseStep 13997771 = 20996657) B20996657
theorem B6993661 : Blo 1841622 6993661 := bstep (se 3 (by rfl) ⟨1311311, by rfl⟩ : syracuseStep 6993661 = 2622623) B2622623
theorem B7870603 : Blo 1841622 7870603 := bstep (se 1 (by rfl) ⟨5902952, by rfl⟩ : syracuseStep 7870603 = 11805905) B11805905
theorem B19929347 : Blo 1841622 19929347 := bstep (se 1 (by rfl) ⟨14947010, by rfl⟩ : syracuseStep 19929347 = 29894021) B29894021
theorem B1841631 : Blo 1841622 1841631 := bstep (se 1 (by rfl) ⟨1381223, by rfl⟩ : syracuseStep 1841631 = 2762447) B2762447
theorem B1841819 : Blo 1841622 1841819 := bstep (se 1 (by rfl) ⟨1381364, by rfl⟩ : syracuseStep 1841819 = 2762729) B2762729
theorem B3496679 : Blo 1841622 3496679 := bstep (se 1 (by rfl) ⟨2622509, by rfl⟩ : syracuseStep 3496679 = 5245019) B5245019
theorem B1841947 : Blo 1841622 1841947 := bstep (se 1 (by rfl) ⟨1381460, by rfl⟩ : syracuseStep 1841947 = 2762921) B2762921
theorem B1842203 : Blo 1841622 1842203 := bstep (se 1 (by rfl) ⟨1381652, by rfl⟩ : syracuseStep 1842203 = 2763305) B2763305
theorem B9329903 : Blo 1841622 9329903 := bstep (se 1 (by rfl) ⟨6997427, by rfl⟩ : syracuseStep 9329903 = 13994855) B13994855
theorem B1842535 : Blo 1841622 1842535 := bstep (se 1 (by rfl) ⟨1381901, by rfl⟩ : syracuseStep 1842535 = 2763803) B2763803
theorem B159432299 : Blo 1841622 159432299 := bstep (se 1 (by rfl) ⟨119574224, by rfl⟩ : syracuseStep 159432299 = 239148449) B239148449
theorem B1843231 : Blo 1841622 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B8855659 : Blo 1841622 8855659 := bstep (se 1 (by rfl) ⟨6641744, by rfl⟩ : syracuseStep 8855659 = 13283489) B13283489
theorem B53862529 : Blo 1841622 53862529 := bstep (se 2 (by rfl) ⟨20198448, by rfl⟩ : syracuseStep 53862529 = 40396897) B40396897
theorem B10494137 : Blo 1841622 10494137 := bstep (se 2 (by rfl) ⟨3935301, by rfl⟩ : syracuseStep 10494137 = 7870603) B7870603
theorem B9961667 : Blo 1841622 9961667 := bstep (se 1 (by rfl) ⟨7471250, by rfl⟩ : syracuseStep 9961667 = 14942501) B14942501
theorem B9453793 : Blo 1841622 9453793 := bstep (se 2 (by rfl) ⟨3545172, by rfl⟩ : syracuseStep 9453793 = 7090345) B7090345
theorem B4145471 : Blo 1841622 4145471 := bstep (se 1 (by rfl) ⟨3109103, by rfl⟩ : syracuseStep 4145471 = 6218207) B6218207
theorem B1843615 : Blo 1841622 1843615 := bstep (se 1 (by rfl) ⟨1382711, by rfl⟩ : syracuseStep 1843615 = 2765423) B2765423
theorem B68158097 : Blo 1841622 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B2769719 : Blo 1841622 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B9331847 : Blo 1841622 9331847 := bstep (se 1 (by rfl) ⟨6998885, by rfl⟩ : syracuseStep 9331847 = 13997771) B13997771
theorem B76646195 : Blo 1841622 76646195 := bstep (se 1 (by rfl) ⟨57484646, by rfl⟩ : syracuseStep 76646195 = 114969293) B114969293
theorem B3934345 : Blo 1841622 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B6219935 : Blo 1841622 6219935 := bstep (se 1 (by rfl) ⟨4664951, by rfl⟩ : syracuseStep 6219935 = 9329903) B9329903
theorem B9324881 : Blo 1841622 9324881 := bstep (se 2 (by rfl) ⟨3496830, by rfl⟩ : syracuseStep 9324881 = 6993661) B6993661
theorem B10635887 : Blo 1841622 10635887 := bstep (se 1 (by rfl) ⟨7976915, by rfl⟩ : syracuseStep 10635887 = 15953831) B15953831
theorem B2763551 : Blo 1841622 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B2763623 : Blo 1841622 2763623 := bstep (se 1 (by rfl) ⟨2072717, by rfl⟩ : syracuseStep 2763623 = 4145435) B4145435
theorem B17706089 : Blo 1841622 17706089 := bstep (se 2 (by rfl) ⟨6639783, by rfl⟩ : syracuseStep 17706089 = 13279567) B13279567
theorem B2763881 : Blo 1841622 2763881 := bstep (se 2 (by rfl) ⟨1036455, by rfl⟩ : syracuseStep 2763881 = 2072911) B2072911
theorem B2624719 : Blo 1841622 2624719 := bstep (se 1 (by rfl) ⟨1968539, by rfl⟩ : syracuseStep 2624719 = 3937079) B3937079
theorem B3108091 : Blo 1841622 3108091 := bstep (se 1 (by rfl) ⟨2331068, by rfl⟩ : syracuseStep 3108091 = 4662137) B4662137
theorem B2764103 : Blo 1841622 2764103 := bstep (se 1 (by rfl) ⟨2073077, by rfl⟩ : syracuseStep 2764103 = 4146155) B4146155
theorem B2764223 : Blo 1841622 2764223 := bstep (se 1 (by rfl) ⟨2073167, by rfl⟩ : syracuseStep 2764223 = 4146335) B4146335
theorem B6221339 : Blo 1841622 6221339 := bstep (se 1 (by rfl) ⟨4666004, by rfl⟩ : syracuseStep 6221339 = 9332009) B9332009
theorem B2764511 : Blo 1841622 2764511 := bstep (se 1 (by rfl) ⟨2073383, by rfl⟩ : syracuseStep 2764511 = 4146767) B4146767
theorem B2764553 : Blo 1841622 2764553 := bstep (se 2 (by rfl) ⟨1036707, by rfl⟩ : syracuseStep 2764553 = 2073415) B2073415
theorem B22409081 : Blo 1841622 22409081 := bstep (se 2 (by rfl) ⟨8403405, by rfl⟩ : syracuseStep 22409081 = 16806811) B16806811
theorem B2764937 : Blo 1841622 2764937 := bstep (se 2 (by rfl) ⟨1036851, by rfl⟩ : syracuseStep 2764937 = 2073703) B2073703
theorem B2764955 : Blo 1841622 2764955 := bstep (se 1 (by rfl) ⟨2073716, by rfl⟩ : syracuseStep 2764955 = 4147433) B4147433
theorem B4665721 : Blo 1841622 4665721 := bstep (se 2 (by rfl) ⟨1749645, by rfl⟩ : syracuseStep 4665721 = 3499291) B3499291
theorem B2331119 : Blo 1841622 2331119 := bstep (se 1 (by rfl) ⟨1748339, by rfl⟩ : syracuseStep 2331119 = 3496679) B3496679
theorem B106288199 : Blo 1841622 106288199 := bstep (se 1 (by rfl) ⟨79716149, by rfl⟩ : syracuseStep 106288199 = 159432299) B159432299
theorem B53114575 : Blo 1841622 53114575 := bstep (se 1 (by rfl) ⟨39835931, by rfl⟩ : syracuseStep 53114575 = 79671863) B79671863
theorem B17717129 : Blo 1841622 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B6215615 : Blo 1841622 6215615 := bstep (se 1 (by rfl) ⟨4661711, by rfl⟩ : syracuseStep 6215615 = 9323423) B9323423
theorem B9328607 : Blo 1841622 9328607 := bstep (se 1 (by rfl) ⟨6996455, by rfl⟩ : syracuseStep 9328607 = 13992911) B13992911
theorem B44832953 : Blo 1841622 44832953 := bstep (se 2 (by rfl) ⟨16812357, by rfl⟩ : syracuseStep 44832953 = 33624715) B33624715
theorem B5249279 : Blo 1841622 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B151231049 : Blo 1841622 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B25565939 : Blo 1841622 25565939 := bstep (se 1 (by rfl) ⟨19174454, by rfl⟩ : syracuseStep 25565939 = 38348909) B38348909
theorem B13286231 : Blo 1841622 13286231 := bstep (se 1 (by rfl) ⟨9964673, by rfl⟩ : syracuseStep 13286231 = 19929347) B19929347
theorem B1842331 : Blo 1841622 1842331 := bstep (se 1 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 1842331 = 2763497) B2763497
theorem B1842715 : Blo 1841622 1842715 := bstep (se 1 (by rfl) ⟨1382036, by rfl⟩ : syracuseStep 1842715 = 2764073) B2764073
theorem B1842927 : Blo 1841622 1842927 := bstep (se 1 (by rfl) ⟨1382195, by rfl⟩ : syracuseStep 1842927 = 2764391) B2764391
theorem B51109667 : Blo 1841622 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B1843047 : Blo 1841622 1843047 := bstep (se 1 (by rfl) ⟨1382285, by rfl⟩ : syracuseStep 1843047 = 2764571) B2764571
theorem B1843183 : Blo 1841622 1843183 := bstep (se 1 (by rfl) ⟨1382387, by rfl⟩ : syracuseStep 1843183 = 2764775) B2764775
theorem B1843291 : Blo 1841622 1843291 := bstep (se 1 (by rfl) ⟨1382468, by rfl⟩ : syracuseStep 1843291 = 2764937) B2764937
theorem B1843303 : Blo 1841622 1843303 := bstep (se 1 (by rfl) ⟨1382477, by rfl⟩ : syracuseStep 1843303 = 2764955) B2764955
theorem B6996091 : Blo 1841622 6996091 := bstep (se 1 (by rfl) ⟨5247068, by rfl⟩ : syracuseStep 6996091 = 10494137) B10494137
theorem B6219071 : Blo 1841622 6219071 := bstep (se 1 (by rfl) ⟨4664303, by rfl⟩ : syracuseStep 6219071 = 9328607) B9328607
theorem B4146623 : Blo 1841622 4146623 := bstep (se 1 (by rfl) ⟨3109967, by rfl⟩ : syracuseStep 4146623 = 6219935) B6219935
theorem B3499519 : Blo 1841622 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B3499625 : Blo 1841622 3499625 := bstep (se 2 (by rfl) ⟨1312359, by rfl⟩ : syracuseStep 3499625 = 2624719) B2624719
theorem B100820699 : Blo 1841622 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B8857487 : Blo 1841622 8857487 := bstep (se 1 (by rfl) ⟨6643115, by rfl⟩ : syracuseStep 8857487 = 13286231) B13286231
theorem B4147559 : Blo 1841622 4147559 := bstep (se 1 (by rfl) ⟨3110669, by rfl⟩ : syracuseStep 4147559 = 6221339) B6221339
theorem B34073111 : Blo 1841622 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B11807545 : Blo 1841622 11807545 := bstep (se 2 (by rfl) ⟨4427829, by rfl⟩ : syracuseStep 11807545 = 8855659) B8855659
theorem B5245793 : Blo 1841622 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B2763647 : Blo 1841622 2763647 := bstep (se 1 (by rfl) ⟨2072735, by rfl⟩ : syracuseStep 2763647 = 4145471) B4145471
theorem B6220961 : Blo 1841622 6220961 := bstep (se 2 (by rfl) ⟨2332860, by rfl⟩ : syracuseStep 6220961 = 4665721) B4665721
theorem B6221231 : Blo 1841622 6221231 := bstep (se 1 (by rfl) ⟨4665923, by rfl⟩ : syracuseStep 6221231 = 9331847) B9331847
theorem B51097463 : Blo 1841622 51097463 := bstep (se 1 (by rfl) ⟨38323097, by rfl⟩ : syracuseStep 51097463 = 76646195) B76646195
theorem B29888635 : Blo 1841622 29888635 := bstep (se 1 (by rfl) ⟨22416476, by rfl⟩ : syracuseStep 29888635 = 44832953) B44832953
theorem B7090591 : Blo 1841622 7090591 := bstep (se 1 (by rfl) ⟨5317943, by rfl⟩ : syracuseStep 7090591 = 10635887) B10635887
theorem B17043959 : Blo 1841622 17043959 := bstep (se 1 (by rfl) ⟨12782969, by rfl⟩ : syracuseStep 17043959 = 25565939) B25565939
theorem B7385917 : Blo 1841622 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B14939387 : Blo 1841622 14939387 := bstep (se 1 (by rfl) ⟨11204540, by rfl⟩ : syracuseStep 14939387 = 22409081) B22409081
theorem B6641111 : Blo 1841622 6641111 := bstep (se 1 (by rfl) ⟨4980833, by rfl⟩ : syracuseStep 6641111 = 9961667) B9961667
theorem B71816705 : Blo 1841622 71816705 := bstep (se 2 (by rfl) ⟨26931264, by rfl⟩ : syracuseStep 71816705 = 53862529) B53862529
theorem B12605057 : Blo 1841622 12605057 := bstep (se 2 (by rfl) ⟨4726896, by rfl⟩ : syracuseStep 12605057 = 9453793) B9453793
theorem B45438731 : Blo 1841622 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B70858799 : Blo 1841622 70858799 := bstep (se 1 (by rfl) ⟨53144099, by rfl⟩ : syracuseStep 70858799 = 106288199) B106288199
theorem B11811419 : Blo 1841622 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B6216317 : Blo 1841622 6216317 := bstep (se 3 (by rfl) ⟨1165559, by rfl⟩ : syracuseStep 6216317 = 2331119) B2331119
theorem B4143743 : Blo 1841622 4143743 := bstep (se 1 (by rfl) ⟨3107807, by rfl⟩ : syracuseStep 4143743 = 6215615) B6215615
theorem B6216587 : Blo 1841622 6216587 := bstep (se 1 (by rfl) ⟨4662440, by rfl⟩ : syracuseStep 6216587 = 9324881) B9324881
theorem B4144121 : Blo 1841622 4144121 := bstep (se 2 (by rfl) ⟨1554045, by rfl⟩ : syracuseStep 4144121 = 3108091) B3108091
theorem B1842367 : Blo 1841622 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B1842415 : Blo 1841622 1842415 := bstep (se 1 (by rfl) ⟨1381811, by rfl⟩ : syracuseStep 1842415 = 2763623) B2763623
theorem B11804059 : Blo 1841622 11804059 := bstep (se 1 (by rfl) ⟨8853044, by rfl⟩ : syracuseStep 11804059 = 17706089) B17706089
theorem B1842587 : Blo 1841622 1842587 := bstep (se 1 (by rfl) ⟨1381940, by rfl⟩ : syracuseStep 1842587 = 2763881) B2763881
theorem B1842735 : Blo 1841622 1842735 := bstep (se 1 (by rfl) ⟨1382051, by rfl⟩ : syracuseStep 1842735 = 2764103) B2764103
theorem B70819433 : Blo 1841622 70819433 := bstep (se 2 (by rfl) ⟨26557287, by rfl⟩ : syracuseStep 70819433 = 53114575) B53114575
theorem B1842815 : Blo 1841622 1842815 := bstep (se 1 (by rfl) ⟨1382111, by rfl⟩ : syracuseStep 1842815 = 2764223) B2764223
theorem B1843007 : Blo 1841622 1843007 := bstep (se 1 (by rfl) ⟨1382255, by rfl⟩ : syracuseStep 1843007 = 2764511) B2764511
theorem B1843035 : Blo 1841622 1843035 := bstep (se 1 (by rfl) ⟨1382276, by rfl⟩ : syracuseStep 1843035 = 2764553) B2764553
theorem B11362639 : Blo 1841622 11362639 := bstep (se 1 (by rfl) ⟨8521979, by rfl⟩ : syracuseStep 11362639 = 17043959) B17043959
theorem B9454121 : Blo 1841622 9454121 := bstep (se 2 (by rfl) ⟨3545295, by rfl⟩ : syracuseStep 9454121 = 7090591) B7090591
theorem B4146047 : Blo 1841622 4146047 := bstep (se 1 (by rfl) ⟨3109535, by rfl⟩ : syracuseStep 4146047 = 6219071) B6219071
theorem B9847889 : Blo 1841622 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B9332333 : Blo 1841622 9332333 := bstep (se 3 (by rfl) ⟨1749812, by rfl⟩ : syracuseStep 9332333 = 3499625) B3499625
theorem B7874279 : Blo 1841622 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B2762495 : Blo 1841622 2762495 := bstep (se 1 (by rfl) ⟨2071871, by rfl⟩ : syracuseStep 2762495 = 4143743) B4143743
theorem B15738745 : Blo 1841622 15738745 := bstep (se 2 (by rfl) ⟨5902029, by rfl⟩ : syracuseStep 15738745 = 11804059) B11804059
theorem B2762747 : Blo 1841622 2762747 := bstep (se 1 (by rfl) ⟨2072060, by rfl⟩ : syracuseStep 2762747 = 4144121) B4144121
theorem B4147307 : Blo 1841622 4147307 := bstep (se 1 (by rfl) ⟨3110480, by rfl⟩ : syracuseStep 4147307 = 6220961) B6220961
theorem B4147487 : Blo 1841622 4147487 := bstep (se 1 (by rfl) ⟨3110615, by rfl⟩ : syracuseStep 4147487 = 6221231) B6221231
theorem B47212955 : Blo 1841622 47212955 := bstep (se 1 (by rfl) ⟨35409716, by rfl⟩ : syracuseStep 47212955 = 70819433) B70819433
theorem B34064975 : Blo 1841622 34064975 := bstep (se 1 (by rfl) ⟨25548731, by rfl⟩ : syracuseStep 34064975 = 51097463) B51097463
theorem B2764415 : Blo 1841622 2764415 := bstep (se 1 (by rfl) ⟨2073311, by rfl⟩ : syracuseStep 2764415 = 4146623) B4146623
theorem B4427407 : Blo 1841622 4427407 := bstep (se 1 (by rfl) ⟨3320555, by rfl⟩ : syracuseStep 4427407 = 6641111) B6641111
theorem B47877803 : Blo 1841622 47877803 := bstep (se 1 (by rfl) ⟨35908352, by rfl⟩ : syracuseStep 47877803 = 71816705) B71816705
theorem B47239199 : Blo 1841622 47239199 := bstep (se 1 (by rfl) ⟨35429399, by rfl⟩ : syracuseStep 47239199 = 70858799) B70858799
theorem B2765039 : Blo 1841622 2765039 := bstep (se 1 (by rfl) ⟨2073779, by rfl⟩ : syracuseStep 2765039 = 4147559) B4147559
theorem B4666025 : Blo 1841622 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B9328121 : Blo 1841622 9328121 := bstep (se 2 (by rfl) ⟨3498045, by rfl⟩ : syracuseStep 9328121 = 6996091) B6996091
theorem B39851513 : Blo 1841622 39851513 := bstep (se 2 (by rfl) ⟨14944317, by rfl⟩ : syracuseStep 39851513 = 29888635) B29888635
theorem B9959591 : Blo 1841622 9959591 := bstep (se 1 (by rfl) ⟨7469693, by rfl⟩ : syracuseStep 9959591 = 14939387) B14939387
theorem B15743393 : Blo 1841622 15743393 := bstep (se 2 (by rfl) ⟨5903772, by rfl⟩ : syracuseStep 15743393 = 11807545) B11807545
theorem B8403371 : Blo 1841622 8403371 := bstep (se 1 (by rfl) ⟨6302528, by rfl⟩ : syracuseStep 8403371 = 12605057) B12605057
theorem B67213799 : Blo 1841622 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B30292487 : Blo 1841622 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B5904991 : Blo 1841622 5904991 := bstep (se 1 (by rfl) ⟨4428743, by rfl⟩ : syracuseStep 5904991 = 8857487) B8857487
theorem B22715407 : Blo 1841622 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B4144211 : Blo 1841622 4144211 := bstep (se 1 (by rfl) ⟨3108158, by rfl⟩ : syracuseStep 4144211 = 6216317) B6216317
theorem B3497195 : Blo 1841622 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B1842431 : Blo 1841622 1842431 := bstep (se 1 (by rfl) ⟨1381823, by rfl⟩ : syracuseStep 1842431 = 2763647) B2763647
theorem B4144391 : Blo 1841622 4144391 := bstep (se 1 (by rfl) ⟨3108293, by rfl⟩ : syracuseStep 4144391 = 6216587) B6216587
theorem B1843359 : Blo 1841622 1843359 := bstep (se 1 (by rfl) ⟨1382519, by rfl⟩ : syracuseStep 1843359 = 2765039) B2765039
theorem B7873321 : Blo 1841622 7873321 := bstep (se 2 (by rfl) ⟨2952495, by rfl⟩ : syracuseStep 7873321 = 5904991) B5904991
theorem B6218747 : Blo 1841622 6218747 := bstep (se 1 (by rfl) ⟨4664060, by rfl⟩ : syracuseStep 6218747 = 9328121) B9328121
theorem B26567675 : Blo 1841622 26567675 := bstep (se 1 (by rfl) ⟨19925756, by rfl⟩ : syracuseStep 26567675 = 39851513) B39851513
theorem B30287209 : Blo 1841622 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B31475303 : Blo 1841622 31475303 := bstep (se 1 (by rfl) ⟨23606477, by rfl⟩ : syracuseStep 31475303 = 47212955) B47212955
theorem B10495595 : Blo 1841622 10495595 := bstep (se 1 (by rfl) ⟨7871696, by rfl⟩ : syracuseStep 10495595 = 15743393) B15743393
theorem B20194991 : Blo 1841622 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B22709983 : Blo 1841622 22709983 := bstep (se 1 (by rfl) ⟨17032487, by rfl⟩ : syracuseStep 22709983 = 34064975) B34064975
theorem B2762807 : Blo 1841622 2762807 := bstep (se 1 (by rfl) ⟨2072105, by rfl⟩ : syracuseStep 2762807 = 4144211) B4144211
theorem B2762927 : Blo 1841622 2762927 := bstep (se 1 (by rfl) ⟨2072195, by rfl⟩ : syracuseStep 2762927 = 4144391) B4144391
theorem B31918535 : Blo 1841622 31918535 := bstep (se 1 (by rfl) ⟨23938901, by rfl⟩ : syracuseStep 31918535 = 47877803) B47877803
theorem B31492799 : Blo 1841622 31492799 := bstep (se 1 (by rfl) ⟨23619599, by rfl⟩ : syracuseStep 31492799 = 47239199) B47239199
theorem B6302747 : Blo 1841622 6302747 := bstep (se 1 (by rfl) ⟨4727060, by rfl⟩ : syracuseStep 6302747 = 9454121) B9454121
theorem B15150185 : Blo 1841622 15150185 := bstep (se 2 (by rfl) ⟨5681319, by rfl⟩ : syracuseStep 15150185 = 11362639) B11362639
theorem B2764031 : Blo 1841622 2764031 := bstep (se 1 (by rfl) ⟨2073023, by rfl⟩ : syracuseStep 2764031 = 4146047) B4146047
theorem B9325853 : Blo 1841622 9325853 := bstep (se 3 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 9325853 = 3497195) B3497195
theorem B6565259 : Blo 1841622 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B6221555 : Blo 1841622 6221555 := bstep (se 1 (by rfl) ⟨4666166, by rfl⟩ : syracuseStep 6221555 = 9332333) B9332333
theorem B2764871 : Blo 1841622 2764871 := bstep (se 1 (by rfl) ⟨2073653, by rfl⟩ : syracuseStep 2764871 = 4147307) B4147307
theorem B6639727 : Blo 1841622 6639727 := bstep (se 1 (by rfl) ⟨4979795, by rfl⟩ : syracuseStep 6639727 = 9959591) B9959591
theorem B2764991 : Blo 1841622 2764991 := bstep (se 1 (by rfl) ⟨2073743, by rfl⟩ : syracuseStep 2764991 = 4147487) B4147487
theorem B5903209 : Blo 1841622 5903209 := bstep (se 2 (by rfl) ⟨2213703, by rfl⟩ : syracuseStep 5903209 = 4427407) B4427407
theorem B20984993 : Blo 1841622 20984993 := bstep (se 2 (by rfl) ⟨7869372, by rfl⟩ : syracuseStep 20984993 = 15738745) B15738745
theorem B3110683 : Blo 1841622 3110683 := bstep (se 1 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 3110683 = 4666025) B4666025
theorem B5249519 : Blo 1841622 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B1841663 : Blo 1841622 1841663 := bstep (se 1 (by rfl) ⟨1381247, by rfl⟩ : syracuseStep 1841663 = 2762495) B2762495
theorem B1841831 : Blo 1841622 1841831 := bstep (se 1 (by rfl) ⟨1381373, by rfl⟩ : syracuseStep 1841831 = 2762747) B2762747
theorem B5602247 : Blo 1841622 5602247 := bstep (se 1 (by rfl) ⟨4201685, by rfl⟩ : syracuseStep 5602247 = 8403371) B8403371
theorem B44809199 : Blo 1841622 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B1842943 : Blo 1841622 1842943 := bstep (se 1 (by rfl) ⟨1382207, by rfl⟩ : syracuseStep 1842943 = 2764415) B2764415
theorem B1843247 : Blo 1841622 1843247 := bstep (se 1 (by rfl) ⟨1382435, by rfl⟩ : syracuseStep 1843247 = 2764871) B2764871
theorem B1843327 : Blo 1841622 1843327 := bstep (se 1 (by rfl) ⟨1382495, by rfl⟩ : syracuseStep 1843327 = 2764991) B2764991
theorem B4145831 : Blo 1841622 4145831 := bstep (se 1 (by rfl) ⟨3109373, by rfl⟩ : syracuseStep 4145831 = 6218747) B6218747
theorem B17711783 : Blo 1841622 17711783 := bstep (se 1 (by rfl) ⟨13283837, by rfl⟩ : syracuseStep 17711783 = 26567675) B26567675
theorem B17507357 : Blo 1841622 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B6997063 : Blo 1841622 6997063 := bstep (se 1 (by rfl) ⟨5247797, by rfl⟩ : syracuseStep 6997063 = 10495595) B10495595
theorem B3499679 : Blo 1841622 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B30279977 : Blo 1841622 30279977 := bstep (se 2 (by rfl) ⟨11354991, by rfl⟩ : syracuseStep 30279977 = 22709983) B22709983
theorem B4147577 : Blo 1841622 4147577 := bstep (se 2 (by rfl) ⟨1555341, by rfl⟩ : syracuseStep 4147577 = 3110683) B3110683
theorem B4147703 : Blo 1841622 4147703 := bstep (se 1 (by rfl) ⟨3110777, by rfl⟩ : syracuseStep 4147703 = 6221555) B6221555
theorem B10497761 : Blo 1841622 10497761 := bstep (se 2 (by rfl) ⟨3936660, by rfl⟩ : syracuseStep 10497761 = 7873321) B7873321
theorem B20983535 : Blo 1841622 20983535 := bstep (se 1 (by rfl) ⟨15737651, by rfl⟩ : syracuseStep 20983535 = 31475303) B31475303
theorem B13463327 : Blo 1841622 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B21279023 : Blo 1841622 21279023 := bstep (se 1 (by rfl) ⟨15959267, by rfl⟩ : syracuseStep 21279023 = 31918535) B31918535
theorem B40382945 : Blo 1841622 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B29872799 : Blo 1841622 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B8852969 : Blo 1841622 8852969 := bstep (se 2 (by rfl) ⟨3319863, by rfl⟩ : syracuseStep 8852969 = 6639727) B6639727
theorem B13989995 : Blo 1841622 13989995 := bstep (se 1 (by rfl) ⟨10492496, by rfl⟩ : syracuseStep 13989995 = 20984993) B20984993
theorem B7870945 : Blo 1841622 7870945 := bstep (se 2 (by rfl) ⟨2951604, by rfl⟩ : syracuseStep 7870945 = 5903209) B5903209
theorem B1841871 : Blo 1841622 1841871 := bstep (se 1 (by rfl) ⟨1381403, by rfl⟩ : syracuseStep 1841871 = 2762807) B2762807
theorem B1841951 : Blo 1841622 1841951 := bstep (se 1 (by rfl) ⟨1381463, by rfl⟩ : syracuseStep 1841951 = 2762927) B2762927
theorem B20995199 : Blo 1841622 20995199 := bstep (se 1 (by rfl) ⟨15746399, by rfl⟩ : syracuseStep 20995199 = 31492799) B31492799
theorem B3734831 : Blo 1841622 3734831 := bstep (se 1 (by rfl) ⟨2801123, by rfl⟩ : syracuseStep 3734831 = 5602247) B5602247
theorem B4201831 : Blo 1841622 4201831 := bstep (se 1 (by rfl) ⟨3151373, by rfl⟩ : syracuseStep 4201831 = 6302747) B6302747
theorem B10100123 : Blo 1841622 10100123 := bstep (se 1 (by rfl) ⟨7575092, by rfl⟩ : syracuseStep 10100123 = 15150185) B15150185
theorem B1842687 : Blo 1841622 1842687 := bstep (se 1 (by rfl) ⟨1382015, by rfl⟩ : syracuseStep 1842687 = 2764031) B2764031
theorem B6217235 : Blo 1841622 6217235 := bstep (se 1 (by rfl) ⟨4662926, by rfl⟩ : syracuseStep 6217235 = 9325853) B9325853
theorem B19915199 : Blo 1841622 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B10494593 : Blo 1841622 10494593 := bstep (se 2 (by rfl) ⟨3935472, by rfl⟩ : syracuseStep 10494593 = 7870945) B7870945
theorem B20186651 : Blo 1841622 20186651 := bstep (se 1 (by rfl) ⟨15139988, by rfl⟩ : syracuseStep 20186651 = 30279977) B30279977
theorem B6998507 : Blo 1841622 6998507 := bstep (se 1 (by rfl) ⟨5248880, by rfl⟩ : syracuseStep 6998507 = 10497761) B10497761
theorem B26921963 : Blo 1841622 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B2763887 : Blo 1841622 2763887 := bstep (se 1 (by rfl) ⟨2072915, by rfl⟩ : syracuseStep 2763887 = 4145831) B4145831
theorem B11807855 : Blo 1841622 11807855 := bstep (se 1 (by rfl) ⟨8855891, by rfl⟩ : syracuseStep 11807855 = 17711783) B17711783
theorem B5901979 : Blo 1841622 5901979 := bstep (se 1 (by rfl) ⟨4426484, by rfl⟩ : syracuseStep 5901979 = 8852969) B8852969
theorem B9326663 : Blo 1841622 9326663 := bstep (se 1 (by rfl) ⟨6994997, by rfl⟩ : syracuseStep 9326663 = 13989995) B13989995
theorem B2765051 : Blo 1841622 2765051 := bstep (se 1 (by rfl) ⟨2073788, by rfl⟩ : syracuseStep 2765051 = 4147577) B4147577
theorem B2765135 : Blo 1841622 2765135 := bstep (se 1 (by rfl) ⟨2073851, by rfl⟩ : syracuseStep 2765135 = 4147703) B4147703
theorem B13996799 : Blo 1841622 13996799 := bstep (se 1 (by rfl) ⟨10497599, by rfl⟩ : syracuseStep 13996799 = 20995199) B20995199
theorem B13989023 : Blo 1841622 13989023 := bstep (se 1 (by rfl) ⟨10491767, by rfl⟩ : syracuseStep 13989023 = 20983535) B20983535
theorem B8975551 : Blo 1841622 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B14186015 : Blo 1841622 14186015 := bstep (se 1 (by rfl) ⟨10639511, by rfl⟩ : syracuseStep 14186015 = 21279023) B21279023
theorem B11671571 : Blo 1841622 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B2333119 : Blo 1841622 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B9329417 : Blo 1841622 9329417 := bstep (se 2 (by rfl) ⟨3498531, by rfl⟩ : syracuseStep 9329417 = 6997063) B6997063
theorem B5602441 : Blo 1841622 5602441 := bstep (se 2 (by rfl) ⟨2100915, by rfl⟩ : syracuseStep 5602441 = 4201831) B4201831
theorem B2489887 : Blo 1841622 2489887 := bstep (se 1 (by rfl) ⟨1867415, by rfl⟩ : syracuseStep 2489887 = 3734831) B3734831
theorem B6733415 : Blo 1841622 6733415 := bstep (se 1 (by rfl) ⟨5050061, by rfl⟩ : syracuseStep 6733415 = 10100123) B10100123
theorem B4144823 : Blo 1841622 4144823 := bstep (se 1 (by rfl) ⟨3108617, by rfl⟩ : syracuseStep 4144823 = 6217235) B6217235
theorem B6217775 : Blo 1841622 6217775 := bstep (se 1 (by rfl) ⟨4663331, by rfl⟩ : syracuseStep 6217775 = 9326663) B9326663
theorem B1843367 : Blo 1841622 1843367 := bstep (se 1 (by rfl) ⟨1382525, by rfl⟩ : syracuseStep 1843367 = 2765051) B2765051
theorem B1843423 : Blo 1841622 1843423 := bstep (se 1 (by rfl) ⟨1382567, by rfl⟩ : syracuseStep 1843423 = 2765135) B2765135
theorem B6996395 : Blo 1841622 6996395 := bstep (se 1 (by rfl) ⟨5247296, by rfl⟩ : syracuseStep 6996395 = 10494593) B10494593
theorem B9331199 : Blo 1841622 9331199 := bstep (se 1 (by rfl) ⟨6998399, by rfl⟩ : syracuseStep 9331199 = 13996799) B13996799
theorem B6219611 : Blo 1841622 6219611 := bstep (se 1 (by rfl) ⟨4664708, by rfl⟩ : syracuseStep 6219611 = 9329417) B9329417
theorem B3319849 : Blo 1841622 3319849 := bstep (se 2 (by rfl) ⟨1244943, by rfl⟩ : syracuseStep 3319849 = 2489887) B2489887
theorem B2763215 : Blo 1841622 2763215 := bstep (se 1 (by rfl) ⟨2072411, by rfl⟩ : syracuseStep 2763215 = 4144823) B4144823
theorem B31124189 : Blo 1841622 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B9326015 : Blo 1841622 9326015 := bstep (se 1 (by rfl) ⟨6994511, by rfl⟩ : syracuseStep 9326015 = 13989023) B13989023
theorem B9457343 : Blo 1841622 9457343 := bstep (se 1 (by rfl) ⟨7093007, by rfl⟩ : syracuseStep 9457343 = 14186015) B14186015
theorem B4665671 : Blo 1841622 4665671 := bstep (se 1 (by rfl) ⟨3499253, by rfl⟩ : syracuseStep 4665671 = 6998507) B6998507
theorem B7869305 : Blo 1841622 7869305 := bstep (se 2 (by rfl) ⟨2950989, by rfl⟩ : syracuseStep 7869305 = 5901979) B5901979
theorem B13276799 : Blo 1841622 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B3110825 : Blo 1841622 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B13457767 : Blo 1841622 13457767 := bstep (se 1 (by rfl) ⟨10093325, by rfl⟩ : syracuseStep 13457767 = 20186651) B20186651
theorem B7469921 : Blo 1841622 7469921 := bstep (se 2 (by rfl) ⟨2801220, by rfl⟩ : syracuseStep 7469921 = 5602441) B5602441
theorem B11967401 : Blo 1841622 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B17947975 : Blo 1841622 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1842591 : Blo 1841622 1842591 := bstep (se 1 (by rfl) ⟨1381943, by rfl⟩ : syracuseStep 1842591 = 2763887) B2763887
theorem B7871903 : Blo 1841622 7871903 := bstep (se 1 (by rfl) ⟨5903927, by rfl⟩ : syracuseStep 7871903 = 11807855) B11807855
theorem B4488943 : Blo 1841622 4488943 := bstep (se 1 (by rfl) ⟨3366707, by rfl⟩ : syracuseStep 4488943 = 6733415) B6733415
theorem B4145183 : Blo 1841622 4145183 := bstep (se 1 (by rfl) ⟨3108887, by rfl⟩ : syracuseStep 4145183 = 6217775) B6217775
theorem B4146407 : Blo 1841622 4146407 := bstep (se 1 (by rfl) ⟨3109805, by rfl⟩ : syracuseStep 4146407 = 6219611) B6219611
theorem B2073883 : Blo 1841622 2073883 := bstep (se 1 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 2073883 = 3110825) B3110825
theorem B23930633 : Blo 1841622 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B17705861 : Blo 1841622 17705861 := bstep (se 4 (by rfl) ⟨1659924, by rfl⟩ : syracuseStep 17705861 = 3319849) B3319849
theorem B4664263 : Blo 1841622 4664263 := bstep (se 1 (by rfl) ⟨3498197, by rfl⟩ : syracuseStep 4664263 = 6996395) B6996395
theorem B6220799 : Blo 1841622 6220799 := bstep (se 1 (by rfl) ⟨4665599, by rfl⟩ : syracuseStep 6220799 = 9331199) B9331199
theorem B17943689 : Blo 1841622 17943689 := bstep (se 2 (by rfl) ⟨6728883, by rfl⟩ : syracuseStep 17943689 = 13457767) B13457767
theorem B5246203 : Blo 1841622 5246203 := bstep (se 1 (by rfl) ⟨3934652, by rfl⟩ : syracuseStep 5246203 = 7869305) B7869305
theorem B8851199 : Blo 1841622 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B19919789 : Blo 1841622 19919789 := bstep (se 3 (by rfl) ⟨3734960, by rfl⟩ : syracuseStep 19919789 = 7469921) B7469921
theorem B5247935 : Blo 1841622 5247935 := bstep (se 1 (by rfl) ⟨3935951, by rfl⟩ : syracuseStep 5247935 = 7871903) B7871903
theorem B5985257 : Blo 1841622 5985257 := bstep (se 2 (by rfl) ⟨2244471, by rfl⟩ : syracuseStep 5985257 = 4488943) B4488943
theorem B6304895 : Blo 1841622 6304895 := bstep (se 1 (by rfl) ⟨4728671, by rfl⟩ : syracuseStep 6304895 = 9457343) B9457343
theorem B3110447 : Blo 1841622 3110447 := bstep (se 1 (by rfl) ⟨2332835, by rfl⟩ : syracuseStep 3110447 = 4665671) B4665671
theorem B1842143 : Blo 1841622 1842143 := bstep (se 1 (by rfl) ⟨1381607, by rfl⟩ : syracuseStep 1842143 = 2763215) B2763215
theorem B20749459 : Blo 1841622 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B7978267 : Blo 1841622 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B6217343 : Blo 1841622 6217343 := bstep (se 1 (by rfl) ⟨4663007, by rfl⟩ : syracuseStep 6217343 = 9326015) B9326015
theorem B13279859 : Blo 1841622 13279859 := bstep (se 1 (by rfl) ⟨9959894, by rfl⟩ : syracuseStep 13279859 = 19919789) B19919789
theorem B3498623 : Blo 1841622 3498623 := bstep (se 1 (by rfl) ⟨2623967, by rfl⟩ : syracuseStep 3498623 = 5247935) B5247935
theorem B4203263 : Blo 1841622 4203263 := bstep (se 1 (by rfl) ⟨3152447, by rfl⟩ : syracuseStep 4203263 = 6304895) B6304895
theorem B2073631 : Blo 1841622 2073631 := bstep (se 1 (by rfl) ⟨1555223, by rfl⟩ : syracuseStep 2073631 = 3110447) B3110447
theorem B6219017 : Blo 1841622 6219017 := bstep (se 2 (by rfl) ⟨2332131, by rfl⟩ : syracuseStep 6219017 = 4664263) B4664263
theorem B27665945 : Blo 1841622 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B23603197 : Blo 1841622 23603197 := bstep (se 3 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 23603197 = 8851199) B8851199
theorem B4147199 : Blo 1841622 4147199 := bstep (se 1 (by rfl) ⟨3110399, by rfl⟩ : syracuseStep 4147199 = 6220799) B6220799
theorem B11962459 : Blo 1841622 11962459 := bstep (se 1 (by rfl) ⟨8971844, by rfl⟩ : syracuseStep 11962459 = 17943689) B17943689
theorem B15960685 : Blo 1841622 15960685 := bstep (se 3 (by rfl) ⟨2992628, by rfl⟩ : syracuseStep 15960685 = 5985257) B5985257
theorem B2763455 : Blo 1841622 2763455 := bstep (se 1 (by rfl) ⟨2072591, by rfl⟩ : syracuseStep 2763455 = 4145183) B4145183
theorem B2764271 : Blo 1841622 2764271 := bstep (se 1 (by rfl) ⟨2073203, by rfl⟩ : syracuseStep 2764271 = 4146407) B4146407
theorem B15953755 : Blo 1841622 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B10637689 : Blo 1841622 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B2765177 : Blo 1841622 2765177 := bstep (se 2 (by rfl) ⟨1036941, by rfl⟩ : syracuseStep 2765177 = 2073883) B2073883
theorem B6994937 : Blo 1841622 6994937 := bstep (se 2 (by rfl) ⟨2623101, by rfl⟩ : syracuseStep 6994937 = 5246203) B5246203
theorem B11803907 : Blo 1841622 11803907 := bstep (se 1 (by rfl) ⟨8852930, by rfl⟩ : syracuseStep 11803907 = 17705861) B17705861
theorem B4144895 : Blo 1841622 4144895 := bstep (se 1 (by rfl) ⟨3108671, by rfl⟩ : syracuseStep 4144895 = 6217343) B6217343
theorem B15949945 : Blo 1841622 15949945 := bstep (se 2 (by rfl) ⟨5981229, by rfl⟩ : syracuseStep 15949945 = 11962459) B11962459
theorem B1843451 : Blo 1841622 1843451 := bstep (se 1 (by rfl) ⟨1382588, by rfl⟩ : syracuseStep 1843451 = 2765177) B2765177
theorem B2802175 : Blo 1841622 2802175 := bstep (se 1 (by rfl) ⟨2101631, by rfl⟩ : syracuseStep 2802175 = 4203263) B4203263
theorem B4146011 : Blo 1841622 4146011 := bstep (se 1 (by rfl) ⟨3109508, by rfl⟩ : syracuseStep 4146011 = 6219017) B6219017
theorem B4663291 : Blo 1841622 4663291 := bstep (se 1 (by rfl) ⟨3497468, by rfl⟩ : syracuseStep 4663291 = 6994937) B6994937
theorem B2763263 : Blo 1841622 2763263 := bstep (se 1 (by rfl) ⟨2072447, by rfl⟩ : syracuseStep 2763263 = 4144895) B4144895
theorem B14183585 : Blo 1841622 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B18443963 : Blo 1841622 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B2764799 : Blo 1841622 2764799 := bstep (se 1 (by rfl) ⟨2073599, by rfl⟩ : syracuseStep 2764799 = 4147199) B4147199
theorem B2764841 : Blo 1841622 2764841 := bstep (se 2 (by rfl) ⟨1036815, by rfl⟩ : syracuseStep 2764841 = 2073631) B2073631
theorem B7869271 : Blo 1841622 7869271 := bstep (se 1 (by rfl) ⟨5901953, by rfl⟩ : syracuseStep 7869271 = 11803907) B11803907
theorem B21271673 : Blo 1841622 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B31470929 : Blo 1841622 31470929 := bstep (se 2 (by rfl) ⟨11801598, by rfl⟩ : syracuseStep 31470929 = 23603197) B23603197
theorem B8853239 : Blo 1841622 8853239 := bstep (se 1 (by rfl) ⟨6639929, by rfl⟩ : syracuseStep 8853239 = 13279859) B13279859
theorem B2332415 : Blo 1841622 2332415 := bstep (se 1 (by rfl) ⟨1749311, by rfl⟩ : syracuseStep 2332415 = 3498623) B3498623
theorem B21280913 : Blo 1841622 21280913 := bstep (se 2 (by rfl) ⟨7980342, by rfl⟩ : syracuseStep 21280913 = 15960685) B15960685
theorem B1842303 : Blo 1841622 1842303 := bstep (se 1 (by rfl) ⟨1381727, by rfl⟩ : syracuseStep 1842303 = 2763455) B2763455
theorem B1842847 : Blo 1841622 1842847 := bstep (se 1 (by rfl) ⟨1382135, by rfl⟩ : syracuseStep 1842847 = 2764271) B2764271
theorem B1843227 : Blo 1841622 1843227 := bstep (se 1 (by rfl) ⟨1382420, by rfl⟩ : syracuseStep 1843227 = 2764841) B2764841
theorem B21266593 : Blo 1841622 21266593 := bstep (se 2 (by rfl) ⟨7974972, by rfl⟩ : syracuseStep 21266593 = 15949945) B15949945
theorem B20980619 : Blo 1841622 20980619 := bstep (se 1 (by rfl) ⟨15735464, by rfl⟩ : syracuseStep 20980619 = 31470929) B31470929
theorem B6219773 : Blo 1841622 6219773 := bstep (se 3 (by rfl) ⟨1166207, by rfl⟩ : syracuseStep 6219773 = 2332415) B2332415
theorem B9455723 : Blo 1841622 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B14944933 : Blo 1841622 14944933 := bstep (se 4 (by rfl) ⟨1401087, by rfl⟩ : syracuseStep 14944933 = 2802175) B2802175
theorem B56724461 : Blo 1841622 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B2764007 : Blo 1841622 2764007 := bstep (se 1 (by rfl) ⟨2073005, by rfl⟩ : syracuseStep 2764007 = 4146011) B4146011
theorem B5902159 : Blo 1841622 5902159 := bstep (se 1 (by rfl) ⟨4426619, by rfl⟩ : syracuseStep 5902159 = 8853239) B8853239
theorem B10492361 : Blo 1841622 10492361 := bstep (se 2 (by rfl) ⟨3934635, by rfl⟩ : syracuseStep 10492361 = 7869271) B7869271
theorem B14187275 : Blo 1841622 14187275 := bstep (se 1 (by rfl) ⟨10640456, by rfl⟩ : syracuseStep 14187275 = 21280913) B21280913
theorem B1842175 : Blo 1841622 1842175 := bstep (se 1 (by rfl) ⟨1381631, by rfl⟩ : syracuseStep 1842175 = 2763263) B2763263
theorem B12295975 : Blo 1841622 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B6217721 : Blo 1841622 6217721 := bstep (se 2 (by rfl) ⟨2331645, by rfl⟩ : syracuseStep 6217721 = 4663291) B4663291
theorem B1843199 : Blo 1841622 1843199 := bstep (se 1 (by rfl) ⟨1382399, by rfl⟩ : syracuseStep 1843199 = 2764799) B2764799
theorem B4146515 : Blo 1841622 4146515 := bstep (se 1 (by rfl) ⟨3109886, by rfl⟩ : syracuseStep 4146515 = 6219773) B6219773
theorem B37816307 : Blo 1841622 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B16394633 : Blo 1841622 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B13987079 : Blo 1841622 13987079 := bstep (se 1 (by rfl) ⟨10490309, by rfl⟩ : syracuseStep 13987079 = 20980619) B20980619
theorem B113421829 : Blo 1841622 113421829 := bstep (se 4 (by rfl) ⟨10633296, by rfl⟩ : syracuseStep 113421829 = 21266593) B21266593
theorem B19926577 : Blo 1841622 19926577 := bstep (se 2 (by rfl) ⟨7472466, by rfl⟩ : syracuseStep 19926577 = 14944933) B14944933
theorem B6303815 : Blo 1841622 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B9458183 : Blo 1841622 9458183 := bstep (se 1 (by rfl) ⟨7093637, by rfl⟩ : syracuseStep 9458183 = 14187275) B14187275
theorem B7869545 : Blo 1841622 7869545 := bstep (se 2 (by rfl) ⟨2951079, by rfl⟩ : syracuseStep 7869545 = 5902159) B5902159
theorem B6994907 : Blo 1841622 6994907 := bstep (se 1 (by rfl) ⟨5246180, by rfl⟩ : syracuseStep 6994907 = 10492361) B10492361
theorem B1842671 : Blo 1841622 1842671 := bstep (se 1 (by rfl) ⟨1382003, by rfl⟩ : syracuseStep 1842671 = 2764007) B2764007
theorem B4145147 : Blo 1841622 4145147 := bstep (se 1 (by rfl) ⟨3108860, by rfl⟩ : syracuseStep 4145147 = 6217721) B6217721
theorem B4202543 : Blo 1841622 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B10929755 : Blo 1841622 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B4663271 : Blo 1841622 4663271 := bstep (se 1 (by rfl) ⟨3497453, by rfl⟩ : syracuseStep 4663271 = 6994907) B6994907
theorem B26568769 : Blo 1841622 26568769 := bstep (se 2 (by rfl) ⟨9963288, by rfl⟩ : syracuseStep 26568769 = 19926577) B19926577
theorem B9324719 : Blo 1841622 9324719 := bstep (se 1 (by rfl) ⟨6993539, by rfl⟩ : syracuseStep 9324719 = 13987079) B13987079
theorem B2763431 : Blo 1841622 2763431 := bstep (se 1 (by rfl) ⟨2072573, by rfl⟩ : syracuseStep 2763431 = 4145147) B4145147
theorem B5246363 : Blo 1841622 5246363 := bstep (se 1 (by rfl) ⟨3934772, by rfl⟩ : syracuseStep 5246363 = 7869545) B7869545
theorem B2764343 : Blo 1841622 2764343 := bstep (se 1 (by rfl) ⟨2073257, by rfl⟩ : syracuseStep 2764343 = 4146515) B4146515
theorem B25210871 : Blo 1841622 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B151229105 : Blo 1841622 151229105 := bstep (se 2 (by rfl) ⟨56710914, by rfl⟩ : syracuseStep 151229105 = 113421829) B113421829
theorem B6305455 : Blo 1841622 6305455 := bstep (se 1 (by rfl) ⟨4729091, by rfl⟩ : syracuseStep 6305455 = 9458183) B9458183
theorem B11206781 : Blo 1841622 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B100819403 : Blo 1841622 100819403 := bstep (se 1 (by rfl) ⟨75614552, by rfl⟩ : syracuseStep 100819403 = 151229105) B151229105
theorem B8407273 : Blo 1841622 8407273 := bstep (se 2 (by rfl) ⟨3152727, by rfl⟩ : syracuseStep 8407273 = 6305455) B6305455
theorem B35425025 : Blo 1841622 35425025 := bstep (se 2 (by rfl) ⟨13284384, by rfl⟩ : syracuseStep 35425025 = 26568769) B26568769
theorem B3108847 : Blo 1841622 3108847 := bstep (se 1 (by rfl) ⟨2331635, by rfl⟩ : syracuseStep 3108847 = 4663271) B4663271
theorem B16807247 : Blo 1841622 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B6216479 : Blo 1841622 6216479 := bstep (se 1 (by rfl) ⟨4662359, by rfl⟩ : syracuseStep 6216479 = 9324719) B9324719
theorem B29146013 : Blo 1841622 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B1842287 : Blo 1841622 1842287 := bstep (se 1 (by rfl) ⟨1381715, by rfl⟩ : syracuseStep 1842287 = 2763431) B2763431
theorem B3497575 : Blo 1841622 3497575 := bstep (se 1 (by rfl) ⟨2623181, by rfl⟩ : syracuseStep 3497575 = 5246363) B5246363
theorem B1842895 : Blo 1841622 1842895 := bstep (se 1 (by rfl) ⟨1382171, by rfl⟩ : syracuseStep 1842895 = 2764343) B2764343
theorem B7471187 : Blo 1841622 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B4663433 : Blo 1841622 4663433 := bstep (se 2 (by rfl) ⟨1748787, by rfl⟩ : syracuseStep 4663433 = 3497575) B3497575
theorem B11209697 : Blo 1841622 11209697 := bstep (se 2 (by rfl) ⟨4203636, by rfl⟩ : syracuseStep 11209697 = 8407273) B8407273
theorem B67212935 : Blo 1841622 67212935 := bstep (se 1 (by rfl) ⟨50409701, by rfl⟩ : syracuseStep 67212935 = 100819403) B100819403
theorem B11204831 : Blo 1841622 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B23616683 : Blo 1841622 23616683 := bstep (se 1 (by rfl) ⟨17712512, by rfl⟩ : syracuseStep 23616683 = 35425025) B35425025
theorem B4144319 : Blo 1841622 4144319 := bstep (se 1 (by rfl) ⟨3108239, by rfl⟩ : syracuseStep 4144319 = 6216479) B6216479
theorem B19430675 : Blo 1841622 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B4145129 : Blo 1841622 4145129 := bstep (se 2 (by rfl) ⟨1554423, by rfl⟩ : syracuseStep 4145129 = 3108847) B3108847
theorem B4980791 : Blo 1841622 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B7473131 : Blo 1841622 7473131 := bstep (se 1 (by rfl) ⟨5604848, by rfl⟩ : syracuseStep 7473131 = 11209697) B11209697
theorem B2762879 : Blo 1841622 2762879 := bstep (se 1 (by rfl) ⟨2072159, by rfl⟩ : syracuseStep 2762879 = 4144319) B4144319
theorem B12953783 : Blo 1841622 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B2763419 : Blo 1841622 2763419 := bstep (se 1 (by rfl) ⟨2072564, by rfl⟩ : syracuseStep 2763419 = 4145129) B4145129
theorem B3108955 : Blo 1841622 3108955 := bstep (se 1 (by rfl) ⟨2331716, by rfl⟩ : syracuseStep 3108955 = 4663433) B4663433
theorem B44808623 : Blo 1841622 44808623 := bstep (se 1 (by rfl) ⟨33606467, by rfl⟩ : syracuseStep 44808623 = 67212935) B67212935
theorem B7469887 : Blo 1841622 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B15744455 : Blo 1841622 15744455 := bstep (se 1 (by rfl) ⟨11808341, by rfl⟩ : syracuseStep 15744455 = 23616683) B23616683
theorem B4145273 : Blo 1841622 4145273 := bstep (se 2 (by rfl) ⟨1554477, by rfl⟩ : syracuseStep 4145273 = 3108955) B3108955
theorem B4982087 : Blo 1841622 4982087 := bstep (se 1 (by rfl) ⟨3736565, by rfl⟩ : syracuseStep 4982087 = 7473131) B7473131
theorem B8635855 : Blo 1841622 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B10496303 : Blo 1841622 10496303 := bstep (se 1 (by rfl) ⟨7872227, by rfl⟩ : syracuseStep 10496303 = 15744455) B15744455
theorem B3320527 : Blo 1841622 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B29872415 : Blo 1841622 29872415 := bstep (se 1 (by rfl) ⟨22404311, by rfl⟩ : syracuseStep 29872415 = 44808623) B44808623
theorem B9959849 : Blo 1841622 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B1841919 : Blo 1841622 1841919 := bstep (se 1 (by rfl) ⟨1381439, by rfl⟩ : syracuseStep 1841919 = 2762879) B2762879
theorem B1842279 : Blo 1841622 1842279 := bstep (se 1 (by rfl) ⟨1381709, by rfl⟩ : syracuseStep 1842279 = 2763419) B2763419
theorem B19914943 : Blo 1841622 19914943 := bstep (se 1 (by rfl) ⟨14936207, by rfl⟩ : syracuseStep 19914943 = 29872415) B29872415
theorem B6997535 : Blo 1841622 6997535 := bstep (se 1 (by rfl) ⟨5248151, by rfl⟩ : syracuseStep 6997535 = 10496303) B10496303
theorem B2763515 : Blo 1841622 2763515 := bstep (se 1 (by rfl) ⟨2072636, by rfl⟩ : syracuseStep 2763515 = 4145273) B4145273
theorem B4427369 : Blo 1841622 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B6639899 : Blo 1841622 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B11514473 : Blo 1841622 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B13285565 : Blo 1841622 13285565 := bstep (se 3 (by rfl) ⟨2491043, by rfl⟩ : syracuseStep 13285565 = 4982087) B4982087
theorem B7676315 : Blo 1841622 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B8857043 : Blo 1841622 8857043 := bstep (se 1 (by rfl) ⟨6642782, by rfl⟩ : syracuseStep 8857043 = 13285565) B13285565
theorem B2951579 : Blo 1841622 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B26553257 : Blo 1841622 26553257 := bstep (se 2 (by rfl) ⟨9957471, by rfl⟩ : syracuseStep 26553257 = 19914943) B19914943
theorem B17706397 : Blo 1841622 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B4665023 : Blo 1841622 4665023 := bstep (se 1 (by rfl) ⟨3498767, by rfl⟩ : syracuseStep 4665023 = 6997535) B6997535
theorem B1842343 : Blo 1841622 1842343 := bstep (se 1 (by rfl) ⟨1381757, by rfl⟩ : syracuseStep 1842343 = 2763515) B2763515
theorem B3110015 : Blo 1841622 3110015 := bstep (se 1 (by rfl) ⟨2332511, by rfl⟩ : syracuseStep 3110015 = 4665023) B4665023
theorem B5117543 : Blo 1841622 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B5904695 : Blo 1841622 5904695 := bstep (se 1 (by rfl) ⟨4428521, by rfl⟩ : syracuseStep 5904695 = 8857043) B8857043
theorem B7870877 : Blo 1841622 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B23608529 : Blo 1841622 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B17702171 : Blo 1841622 17702171 := bstep (se 1 (by rfl) ⟨13276628, by rfl⟩ : syracuseStep 17702171 = 26553257) B26553257
theorem B2073343 : Blo 1841622 2073343 := bstep (se 1 (by rfl) ⟨1555007, by rfl⟩ : syracuseStep 2073343 = 3110015) B3110015
theorem B15745853 : Blo 1841622 15745853 := bstep (se 3 (by rfl) ⟨2952347, by rfl⟩ : syracuseStep 15745853 = 5904695) B5904695
theorem B15739019 : Blo 1841622 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B3411695 : Blo 1841622 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B5247251 : Blo 1841622 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B11801447 : Blo 1841622 11801447 := bstep (se 1 (by rfl) ⟨8851085, by rfl⟩ : syracuseStep 11801447 = 17702171) B17702171
theorem B3498167 : Blo 1841622 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B10497235 : Blo 1841622 10497235 := bstep (se 1 (by rfl) ⟨7872926, by rfl⟩ : syracuseStep 10497235 = 15745853) B15745853
theorem B7867631 : Blo 1841622 7867631 := bstep (se 1 (by rfl) ⟨5900723, by rfl⟩ : syracuseStep 7867631 = 11801447) B11801447
theorem B2764457 : Blo 1841622 2764457 := bstep (se 2 (by rfl) ⟨1036671, by rfl⟩ : syracuseStep 2764457 = 2073343) B2073343
theorem B2274463 : Blo 1841622 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B10492679 : Blo 1841622 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B5245087 : Blo 1841622 5245087 := bstep (se 1 (by rfl) ⟨3933815, by rfl⟩ : syracuseStep 5245087 = 7867631) B7867631
theorem B13996313 : Blo 1841622 13996313 := bstep (se 2 (by rfl) ⟨5248617, by rfl⟩ : syracuseStep 13996313 = 10497235) B10497235
theorem B9328445 : Blo 1841622 9328445 := bstep (se 3 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 9328445 = 3498167) B3498167
theorem B12130469 : Blo 1841622 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B6995119 : Blo 1841622 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B1842971 : Blo 1841622 1842971 := bstep (se 1 (by rfl) ⟨1382228, by rfl⟩ : syracuseStep 1842971 = 2764457) B2764457
theorem B9330875 : Blo 1841622 9330875 := bstep (se 1 (by rfl) ⟨6998156, by rfl⟩ : syracuseStep 9330875 = 13996313) B13996313
theorem B6218963 : Blo 1841622 6218963 := bstep (se 1 (by rfl) ⟨4664222, by rfl⟩ : syracuseStep 6218963 = 9328445) B9328445
theorem B8086979 : Blo 1841622 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B9326825 : Blo 1841622 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B6993449 : Blo 1841622 6993449 := bstep (se 2 (by rfl) ⟨2622543, by rfl⟩ : syracuseStep 6993449 = 5245087) B5245087
theorem B6217883 : Blo 1841622 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B4145975 : Blo 1841622 4145975 := bstep (se 1 (by rfl) ⟨3109481, by rfl⟩ : syracuseStep 4145975 = 6218963) B6218963
theorem B4662299 : Blo 1841622 4662299 := bstep (se 1 (by rfl) ⟨3496724, by rfl⟩ : syracuseStep 4662299 = 6993449) B6993449
theorem B6220583 : Blo 1841622 6220583 := bstep (se 1 (by rfl) ⟨4665437, by rfl⟩ : syracuseStep 6220583 = 9330875) B9330875
theorem B21565277 : Blo 1841622 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B4145255 : Blo 1841622 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B4147055 : Blo 1841622 4147055 := bstep (se 1 (by rfl) ⟨3110291, by rfl⟩ : syracuseStep 4147055 = 6220583) B6220583
theorem B2763983 : Blo 1841622 2763983 := bstep (se 1 (by rfl) ⟨2072987, by rfl⟩ : syracuseStep 2763983 = 4145975) B4145975
theorem B3108199 : Blo 1841622 3108199 := bstep (se 1 (by rfl) ⟨2331149, by rfl⟩ : syracuseStep 3108199 = 4662299) B4662299
theorem B14376851 : Blo 1841622 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B2763503 : Blo 1841622 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B2764703 : Blo 1841622 2764703 := bstep (se 1 (by rfl) ⟨2073527, by rfl⟩ : syracuseStep 2764703 = 4147055) B4147055
theorem B4144265 : Blo 1841622 4144265 := bstep (se 2 (by rfl) ⟨1554099, by rfl⟩ : syracuseStep 4144265 = 3108199) B3108199
theorem B1842655 : Blo 1841622 1842655 := bstep (se 1 (by rfl) ⟨1381991, by rfl⟩ : syracuseStep 1842655 = 2763983) B2763983
theorem B9584567 : Blo 1841622 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B2762843 : Blo 1841622 2762843 := bstep (se 1 (by rfl) ⟨2072132, by rfl⟩ : syracuseStep 2762843 = 4144265) B4144265
theorem B1842335 : Blo 1841622 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B1843135 : Blo 1841622 1843135 := bstep (se 1 (by rfl) ⟨1382351, by rfl⟩ : syracuseStep 1843135 = 2764703) B2764703
theorem B6389711 : Blo 1841622 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B1841895 : Blo 1841622 1841895 := bstep (se 1 (by rfl) ⟨1381421, by rfl⟩ : syracuseStep 1841895 = 2762843) B2762843
theorem B4259807 : Blo 1841622 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B2839871 : Blo 1841622 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B7572989 : Blo 1841622 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B5048659 : Blo 1841622 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B6731545 : Blo 1841622 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B8975393 : Blo 1841622 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B5983595 : Blo 1841622 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B3989063 : Blo 1841622 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B2659375 : Blo 1841622 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B14183333 : Blo 1841622 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B9455555 : Blo 1841622 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B6303703 : Blo 1841622 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B8404937 : Blo 1841622 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B5603291 : Blo 1841622 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B3735527 : Blo 1841622 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B39845621 : Blo 1841622 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B26563747 : Blo 1841622 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B35418329 : Blo 1841622 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B23612219 : Blo 1841622 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B15741479 : Blo 1841622 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B10494319 : Blo 1841622 10494319 := bstep (se 1 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 10494319 = 15741479) B15741479
theorem B13992425 : Blo 1841622 13992425 := bstep (se 2 (by rfl) ⟨5247159, by rfl⟩ : syracuseStep 13992425 = 10494319) B10494319
theorem B9328283 : Blo 1841622 9328283 := bstep (se 1 (by rfl) ⟨6996212, by rfl⟩ : syracuseStep 9328283 = 13992425) B13992425
theorem B6218855 : Blo 1841622 6218855 := bstep (se 1 (by rfl) ⟨4664141, by rfl⟩ : syracuseStep 6218855 = 9328283) B9328283
theorem B4145903 : Blo 1841622 4145903 := bstep (se 1 (by rfl) ⟨3109427, by rfl⟩ : syracuseStep 4145903 = 6218855) B6218855
theorem B2763935 : Blo 1841622 2763935 := bstep (se 1 (by rfl) ⟨2072951, by rfl⟩ : syracuseStep 2763935 = 4145903) B4145903
theorem B1842623 : Blo 1841622 1842623 := bstep (se 1 (by rfl) ⟨1381967, by rfl⟩ : syracuseStep 1842623 = 2763935) B2763935

theorem C0 (j : ℕ) (h1 : 460405 ≤ j) (h2 : j ≤ 460904) : Blo 1841622 (4 * j + 3) := by
  interval_cases j
  · exact B1841623
  · exact B1841627
  · exact B1841631
  · exact B1841635
  · exact B1841639
  · exact B1841643
  · exact B1841647
  · exact B1841651
  · exact B1841655
  · exact B1841659
  · exact B1841663
  · exact B1841667
  · exact B1841671
  · exact B1841675
  · exact B1841679
  · exact B1841683
  · exact B1841687
  · exact B1841691
  · exact B1841695
  · exact B1841699
  · exact B1841703
  · exact B1841707
  · exact B1841711
  · exact B1841715
  · exact B1841719
  · exact B1841723
  · exact B1841727
  · exact B1841731
  · exact B1841735
  · exact B1841739
  · exact B1841743
  · exact B1841747
  · exact B1841751
  · exact B1841755
  · exact B1841759
  · exact B1841763
  · exact B1841767
  · exact B1841771
  · exact B1841775
  · exact B1841779
  · exact B1841783
  · exact B1841787
  · exact B1841791
  · exact B1841795
  · exact B1841799
  · exact B1841803
  · exact B1841807
  · exact B1841811
  · exact B1841815
  · exact B1841819
  · exact B1841823
  · exact B1841827
  · exact B1841831
  · exact B1841835
  · exact B1841839
  · exact B1841843
  · exact B1841847
  · exact B1841851
  · exact B1841855
  · exact B1841859
  · exact B1841863
  · exact B1841867
  · exact B1841871
  · exact B1841875
  · exact B1841879
  · exact B1841883
  · exact B1841887
  · exact B1841891
  · exact B1841895
  · exact B1841899
  · exact B1841903
  · exact B1841907
  · exact B1841911
  · exact B1841915
  · exact B1841919
  · exact B1841923
  · exact B1841927
  · exact B1841931
  · exact B1841935
  · exact B1841939
  · exact B1841943
  · exact B1841947
  · exact B1841951
  · exact B1841955
  · exact B1841959
  · exact B1841963
  · exact B1841967
  · exact B1841971
  · exact B1841975
  · exact B1841979
  · exact B1841983
  · exact B1841987
  · exact B1841991
  · exact B1841995
  · exact B1841999
  · exact B1842003
  · exact B1842007
  · exact B1842011
  · exact B1842015
  · exact B1842019
  · exact B1842023
  · exact B1842027
  · exact B1842031
  · exact B1842035
  · exact B1842039
  · exact B1842043
  · exact B1842047
  · exact B1842051
  · exact B1842055
  · exact B1842059
  · exact B1842063
  · exact B1842067
  · exact B1842071
  · exact B1842075
  · exact B1842079
  · exact B1842083
  · exact B1842087
  · exact B1842091
  · exact B1842095
  · exact B1842099
  · exact B1842103
  · exact B1842107
  · exact B1842111
  · exact B1842115
  · exact B1842119
  · exact B1842123
  · exact B1842127
  · exact B1842131
  · exact B1842135
  · exact B1842139
  · exact B1842143
  · exact B1842147
  · exact B1842151
  · exact B1842155
  · exact B1842159
  · exact B1842163
  · exact B1842167
  · exact B1842171
  · exact B1842175
  · exact B1842179
  · exact B1842183
  · exact B1842187
  · exact B1842191
  · exact B1842195
  · exact B1842199
  · exact B1842203
  · exact B1842207
  · exact B1842211
  · exact B1842215
  · exact B1842219
  · exact B1842223
  · exact B1842227
  · exact B1842231
  · exact B1842235
  · exact B1842239
  · exact B1842243
  · exact B1842247
  · exact B1842251
  · exact B1842255
  · exact B1842259
  · exact B1842263
  · exact B1842267
  · exact B1842271
  · exact B1842275
  · exact B1842279
  · exact B1842283
  · exact B1842287
  · exact B1842291
  · exact B1842295
  · exact B1842299
  · exact B1842303
  · exact B1842307
  · exact B1842311
  · exact B1842315
  · exact B1842319
  · exact B1842323
  · exact B1842327
  · exact B1842331
  · exact B1842335
  · exact B1842339
  · exact B1842343
  · exact B1842347
  · exact B1842351
  · exact B1842355
  · exact B1842359
  · exact B1842363
  · exact B1842367
  · exact B1842371
  · exact B1842375
  · exact B1842379
  · exact B1842383
  · exact B1842387
  · exact B1842391
  · exact B1842395
  · exact B1842399
  · exact B1842403
  · exact B1842407
  · exact B1842411
  · exact B1842415
  · exact B1842419
  · exact B1842423
  · exact B1842427
  · exact B1842431
  · exact B1842435
  · exact B1842439
  · exact B1842443
  · exact B1842447
  · exact B1842451
  · exact B1842455
  · exact B1842459
  · exact B1842463
  · exact B1842467
  · exact B1842471
  · exact B1842475
  · exact B1842479
  · exact B1842483
  · exact B1842487
  · exact B1842491
  · exact B1842495
  · exact B1842499
  · exact B1842503
  · exact B1842507
  · exact B1842511
  · exact B1842515
  · exact B1842519
  · exact B1842523
  · exact B1842527
  · exact B1842531
  · exact B1842535
  · exact B1842539
  · exact B1842543
  · exact B1842547
  · exact B1842551
  · exact B1842555
  · exact B1842559
  · exact B1842563
  · exact B1842567
  · exact B1842571
  · exact B1842575
  · exact B1842579
  · exact B1842583
  · exact B1842587
  · exact B1842591
  · exact B1842595
  · exact B1842599
  · exact B1842603
  · exact B1842607
  · exact B1842611
  · exact B1842615
  · exact B1842619
  · exact B1842623
  · exact B1842627
  · exact B1842631
  · exact B1842635
  · exact B1842639
  · exact B1842643
  · exact B1842647
  · exact B1842651
  · exact B1842655
  · exact B1842659
  · exact B1842663
  · exact B1842667
  · exact B1842671
  · exact B1842675
  · exact B1842679
  · exact B1842683
  · exact B1842687
  · exact B1842691
  · exact B1842695
  · exact B1842699
  · exact B1842703
  · exact B1842707
  · exact B1842711
  · exact B1842715
  · exact B1842719
  · exact B1842723
  · exact B1842727
  · exact B1842731
  · exact B1842735
  · exact B1842739
  · exact B1842743
  · exact B1842747
  · exact B1842751
  · exact B1842755
  · exact B1842759
  · exact B1842763
  · exact B1842767
  · exact B1842771
  · exact B1842775
  · exact B1842779
  · exact B1842783
  · exact B1842787
  · exact B1842791
  · exact B1842795
  · exact B1842799
  · exact B1842803
  · exact B1842807
  · exact B1842811
  · exact B1842815
  · exact B1842819
  · exact B1842823
  · exact B1842827
  · exact B1842831
  · exact B1842835
  · exact B1842839
  · exact B1842843
  · exact B1842847
  · exact B1842851
  · exact B1842855
  · exact B1842859
  · exact B1842863
  · exact B1842867
  · exact B1842871
  · exact B1842875
  · exact B1842879
  · exact B1842883
  · exact B1842887
  · exact B1842891
  · exact B1842895
  · exact B1842899
  · exact B1842903
  · exact B1842907
  · exact B1842911
  · exact B1842915
  · exact B1842919
  · exact B1842923
  · exact B1842927
  · exact B1842931
  · exact B1842935
  · exact B1842939
  · exact B1842943
  · exact B1842947
  · exact B1842951
  · exact B1842955
  · exact B1842959
  · exact B1842963
  · exact B1842967
  · exact B1842971
  · exact B1842975
  · exact B1842979
  · exact B1842983
  · exact B1842987
  · exact B1842991
  · exact B1842995
  · exact B1842999
  · exact B1843003
  · exact B1843007
  · exact B1843011
  · exact B1843015
  · exact B1843019
  · exact B1843023
  · exact B1843027
  · exact B1843031
  · exact B1843035
  · exact B1843039
  · exact B1843043
  · exact B1843047
  · exact B1843051
  · exact B1843055
  · exact B1843059
  · exact B1843063
  · exact B1843067
  · exact B1843071
  · exact B1843075
  · exact B1843079
  · exact B1843083
  · exact B1843087
  · exact B1843091
  · exact B1843095
  · exact B1843099
  · exact B1843103
  · exact B1843107
  · exact B1843111
  · exact B1843115
  · exact B1843119
  · exact B1843123
  · exact B1843127
  · exact B1843131
  · exact B1843135
  · exact B1843139
  · exact B1843143
  · exact B1843147
  · exact B1843151
  · exact B1843155
  · exact B1843159
  · exact B1843163
  · exact B1843167
  · exact B1843171
  · exact B1843175
  · exact B1843179
  · exact B1843183
  · exact B1843187
  · exact B1843191
  · exact B1843195
  · exact B1843199
  · exact B1843203
  · exact B1843207
  · exact B1843211
  · exact B1843215
  · exact B1843219
  · exact B1843223
  · exact B1843227
  · exact B1843231
  · exact B1843235
  · exact B1843239
  · exact B1843243
  · exact B1843247
  · exact B1843251
  · exact B1843255
  · exact B1843259
  · exact B1843263
  · exact B1843267
  · exact B1843271
  · exact B1843275
  · exact B1843279
  · exact B1843283
  · exact B1843287
  · exact B1843291
  · exact B1843295
  · exact B1843299
  · exact B1843303
  · exact B1843307
  · exact B1843311
  · exact B1843315
  · exact B1843319
  · exact B1843323
  · exact B1843327
  · exact B1843331
  · exact B1843335
  · exact B1843339
  · exact B1843343
  · exact B1843347
  · exact B1843351
  · exact B1843355
  · exact B1843359
  · exact B1843363
  · exact B1843367
  · exact B1843371
  · exact B1843375
  · exact B1843379
  · exact B1843383
  · exact B1843387
  · exact B1843391
  · exact B1843395
  · exact B1843399
  · exact B1843403
  · exact B1843407
  · exact B1843411
  · exact B1843415
  · exact B1843419
  · exact B1843423
  · exact B1843427
  · exact B1843431
  · exact B1843435
  · exact B1843439
  · exact B1843443
  · exact B1843447
  · exact B1843451
  · exact B1843455
  · exact B1843459
  · exact B1843463
  · exact B1843467
  · exact B1843471
  · exact B1843475
  · exact B1843479
  · exact B1843483
  · exact B1843487
  · exact B1843491
  · exact B1843495
  · exact B1843499
  · exact B1843503
  · exact B1843507
  · exact B1843511
  · exact B1843515
  · exact B1843519
  · exact B1843523
  · exact B1843527
  · exact B1843531
  · exact B1843535
  · exact B1843539
  · exact B1843543
  · exact B1843547
  · exact B1843551
  · exact B1843555
  · exact B1843559
  · exact B1843563
  · exact B1843567
  · exact B1843571
  · exact B1843575
  · exact B1843579
  · exact B1843583
  · exact B1843587
  · exact B1843591
  · exact B1843595
  · exact B1843599
  · exact B1843603
  · exact B1843607
  · exact B1843611
  · exact B1843615
  · exact B1843619

theorem solution (m : ℕ) (hlo : 1841622 ≤ m) (hhi : m ≤ 1843622) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 460405 ≤ j := by omega
    have hj2 : j ≤ 460904 := by omega
    have hb : Blo 1841622 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
