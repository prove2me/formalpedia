-- Prove2me | solution 1 for syracuse_descends_range_1752577_1754577
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:37:03.124967+00:00
-- url     : https://prove2.me/submissions/d2e7c4d7-ad66-4177-848a-7b00cd6b9fbd

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


theorem B2629637 : Blo 1752577 2629637 := bbase (se 4 (by rfl) ⟨246528, by rfl⟩ : syracuseStep 2629637 = 493057) (by norm_num)
theorem B2629661 : Blo 1752577 2629661 := bbase (se 3 (by rfl) ⟨493061, by rfl⟩ : syracuseStep 2629661 = 986123) (by norm_num)
theorem B2629685 : Blo 1752577 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B2629709 : Blo 1752577 2629709 := bbase (se 3 (by rfl) ⟨493070, by rfl⟩ : syracuseStep 2629709 = 986141) (by norm_num)
theorem B75882581 : Blo 1752577 75882581 := bbase (se 8 (by rfl) ⟨444624, by rfl⟩ : syracuseStep 75882581 = 889249) (by norm_num)
theorem B3743837 : Blo 1752577 3743837 := bbase (se 3 (by rfl) ⟨701969, by rfl⟩ : syracuseStep 3743837 = 1403939) (by norm_num)
theorem B2629733 : Blo 1752577 2629733 := bbase (se 4 (by rfl) ⟨246537, by rfl⟩ : syracuseStep 2629733 = 493075) (by norm_num)
theorem B2220149 : Blo 1752577 2220149 := bbase (se 5 (by rfl) ⟨104069, by rfl⟩ : syracuseStep 2220149 = 208139) (by norm_num)
theorem B2629757 : Blo 1752577 2629757 := bbase (se 3 (by rfl) ⟨493079, by rfl⟩ : syracuseStep 2629757 = 986159) (by norm_num)
theorem B3997829 : Blo 1752577 3997829 := bbase (se 4 (by rfl) ⟨374796, by rfl⟩ : syracuseStep 3997829 = 749593) (by norm_num)
theorem B4440197 : Blo 1752577 4440197 := bbase (se 4 (by rfl) ⟨416268, by rfl⟩ : syracuseStep 4440197 = 832537) (by norm_num)
theorem B2629781 : Blo 1752577 2629781 := bbase (se 6 (by rfl) ⟨61635, by rfl⟩ : syracuseStep 2629781 = 123271) (by norm_num)
theorem B2957485 : Blo 1752577 2957485 := bbase (se 3 (by rfl) ⟨554528, by rfl⟩ : syracuseStep 2957485 = 1109057) (by norm_num)
theorem B2629805 : Blo 1752577 2629805 := bbase (se 3 (by rfl) ⟨493088, by rfl⟩ : syracuseStep 2629805 = 986177) (by norm_num)
theorem B2220205 : Blo 1752577 2220205 := bbase (se 3 (by rfl) ⟨416288, by rfl⟩ : syracuseStep 2220205 = 832577) (by norm_num)
theorem B2629829 : Blo 1752577 2629829 := bbase (se 4 (by rfl) ⟨246546, by rfl⟩ : syracuseStep 2629829 = 493093) (by norm_num)
theorem B3743957 : Blo 1752577 3743957 := bbase (se 7 (by rfl) ⟨43874, by rfl⟩ : syracuseStep 3743957 = 87749) (by norm_num)
theorem B2629853 : Blo 1752577 2629853 := bbase (se 3 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 2629853 = 986195) (by norm_num)
theorem B2629877 : Blo 1752577 2629877 := bbase (se 5 (by rfl) ⟨123275, by rfl⟩ : syracuseStep 2629877 = 246551) (by norm_num)
theorem B2957573 : Blo 1752577 2957573 := bbase (se 4 (by rfl) ⟨277272, by rfl⟩ : syracuseStep 2957573 = 554545) (by norm_num)
theorem B2629901 : Blo 1752577 2629901 := bbase (se 3 (by rfl) ⟨493106, by rfl⟩ : syracuseStep 2629901 = 986213) (by norm_num)
theorem B2220301 : Blo 1752577 2220301 := bbase (se 3 (by rfl) ⟨416306, by rfl⟩ : syracuseStep 2220301 = 832613) (by norm_num)
theorem B3997973 : Blo 1752577 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B1999129 : Blo 1752577 1999129 := bbase (se 2 (by rfl) ⟨749673, by rfl⟩ : syracuseStep 1999129 = 1499347) (by norm_num)
theorem B2629925 : Blo 1752577 2629925 := bbase (se 4 (by rfl) ⟨246555, by rfl⟩ : syracuseStep 2629925 = 493111) (by norm_num)
theorem B1802549 : Blo 1752577 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B2629949 : Blo 1752577 2629949 := bbase (se 3 (by rfl) ⟨493115, by rfl⟩ : syracuseStep 2629949 = 986231) (by norm_num)
theorem B2629973 : Blo 1752577 2629973 := bbase (se 10 (by rfl) ⟨3852, by rfl⟩ : syracuseStep 2629973 = 7705) (by norm_num)
theorem B2629997 : Blo 1752577 2629997 := bbase (se 3 (by rfl) ⟨493124, by rfl⟩ : syracuseStep 2629997 = 986249) (by norm_num)
theorem B5914997 : Blo 1752577 5914997 := bbase (se 5 (by rfl) ⟨277265, by rfl⟩ : syracuseStep 5914997 = 554531) (by norm_num)
theorem B2957701 : Blo 1752577 2957701 := bbase (se 4 (by rfl) ⟨277284, by rfl⟩ : syracuseStep 2957701 = 554569) (by norm_num)
theorem B2630021 : Blo 1752577 2630021 := bbase (se 4 (by rfl) ⟨246564, by rfl⟩ : syracuseStep 2630021 = 493129) (by norm_num)
theorem B2810261 : Blo 1752577 2810261 := bbase (se 6 (by rfl) ⟨65865, by rfl⟩ : syracuseStep 2810261 = 131731) (by norm_num)
theorem B2630045 : Blo 1752577 2630045 := bbase (se 3 (by rfl) ⟨493133, by rfl⟩ : syracuseStep 2630045 = 986267) (by norm_num)
theorem B2630069 : Blo 1752577 2630069 := bbase (se 5 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 2630069 = 246569) (by norm_num)
theorem B2220473 : Blo 1752577 2220473 := bbase (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) (by norm_num)
theorem B2630093 : Blo 1752577 2630093 := bbase (se 3 (by rfl) ⟨493142, by rfl⟩ : syracuseStep 2630093 = 986285) (by norm_num)
theorem B6316501 : Blo 1752577 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B2957789 : Blo 1752577 2957789 := bbase (se 3 (by rfl) ⟨554585, by rfl⟩ : syracuseStep 2957789 = 1109171) (by norm_num)
theorem B4440541 : Blo 1752577 4440541 := bbase (se 3 (by rfl) ⟨832601, by rfl⟩ : syracuseStep 4440541 = 1665203) (by norm_num)
theorem B2630117 : Blo 1752577 2630117 := bbase (se 4 (by rfl) ⟨246573, by rfl⟩ : syracuseStep 2630117 = 493147) (by norm_num)
theorem B2220529 : Blo 1752577 2220529 := bbase (se 2 (by rfl) ⟨832698, by rfl⟩ : syracuseStep 2220529 = 1665397) (by norm_num)
theorem B3555829 : Blo 1752577 3555829 := bbase (se 5 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 3555829 = 333359) (by norm_num)
theorem B2630141 : Blo 1752577 2630141 := bbase (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) (by norm_num)
theorem B2630165 : Blo 1752577 2630165 := bbase (se 6 (by rfl) ⟨61644, by rfl⟩ : syracuseStep 2630165 = 123289) (by norm_num)
theorem B2105885 : Blo 1752577 2105885 := bbase (se 3 (by rfl) ⟨394853, by rfl⟩ : syracuseStep 2105885 = 789707) (by norm_num)
theorem B8880677 : Blo 1752577 8880677 := bbase (se 4 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 8880677 = 1665127) (by norm_num)
theorem B2630189 : Blo 1752577 2630189 := bbase (se 3 (by rfl) ⟨493160, by rfl⟩ : syracuseStep 2630189 = 986321) (by norm_num)
theorem B2630213 : Blo 1752577 2630213 := bbase (se 4 (by rfl) ⟨246582, by rfl⟩ : syracuseStep 2630213 = 493165) (by norm_num)
theorem B4440653 : Blo 1752577 4440653 := bbase (se 3 (by rfl) ⟨832622, by rfl⟩ : syracuseStep 4440653 = 1665245) (by norm_num)
theorem B2220625 : Blo 1752577 2220625 := bbase (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) (by norm_num)
theorem B7111253 : Blo 1752577 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B2957917 : Blo 1752577 2957917 := bbase (se 3 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 2957917 = 1109219) (by norm_num)
theorem B2630237 : Blo 1752577 2630237 := bbase (se 3 (by rfl) ⟨493169, by rfl⟩ : syracuseStep 2630237 = 986339) (by norm_num)
theorem B2630261 : Blo 1752577 2630261 := bbase (se 5 (by rfl) ⟨123293, by rfl⟩ : syracuseStep 2630261 = 246587) (by norm_num)
theorem B2630285 : Blo 1752577 2630285 := bbase (se 3 (by rfl) ⟨493178, by rfl⟩ : syracuseStep 2630285 = 986357) (by norm_num)
theorem B2630309 : Blo 1752577 2630309 := bbase (se 4 (by rfl) ⟨246591, by rfl⟩ : syracuseStep 2630309 = 493183) (by norm_num)
theorem B2958005 : Blo 1752577 2958005 := bbase (se 5 (by rfl) ⟨138656, by rfl⟩ : syracuseStep 2958005 = 277313) (by norm_num)
theorem B2630333 : Blo 1752577 2630333 := bbase (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) (by norm_num)
theorem B2630357 : Blo 1752577 2630357 := bbase (se 7 (by rfl) ⟨30824, by rfl⟩ : syracuseStep 2630357 = 61649) (by norm_num)
theorem B2630381 : Blo 1752577 2630381 := bbase (se 3 (by rfl) ⟨493196, by rfl⟩ : syracuseStep 2630381 = 986393) (by norm_num)
theorem B2630405 : Blo 1752577 2630405 := bbase (se 4 (by rfl) ⟨246600, by rfl⟩ : syracuseStep 2630405 = 493201) (by norm_num)
theorem B4440845 : Blo 1752577 4440845 := bbase (se 3 (by rfl) ⟨832658, by rfl⟩ : syracuseStep 4440845 = 1665317) (by norm_num)
theorem B2630429 : Blo 1752577 2630429 := bbase (se 3 (by rfl) ⟨493205, by rfl⟩ : syracuseStep 2630429 = 986411) (by norm_num)
theorem B5915429 : Blo 1752577 5915429 := bbase (se 4 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 5915429 = 1109143) (by norm_num)
theorem B4211509 : Blo 1752577 4211509 := bbase (se 5 (by rfl) ⟨197414, by rfl⟩ : syracuseStep 4211509 = 394829) (by norm_num)
theorem B2958133 : Blo 1752577 2958133 := bbase (se 5 (by rfl) ⟨138662, by rfl⟩ : syracuseStep 2958133 = 277325) (by norm_num)
theorem B2630453 : Blo 1752577 2630453 := bbase (se 5 (by rfl) ⟨123302, by rfl⟩ : syracuseStep 2630453 = 246605) (by norm_num)
theorem B5620549 : Blo 1752577 5620549 := bbase (se 4 (by rfl) ⟨526926, by rfl⟩ : syracuseStep 5620549 = 1053853) (by norm_num)
theorem B3744589 : Blo 1752577 3744589 := bbase (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) (by norm_num)
theorem B2630477 : Blo 1752577 2630477 := bbase (se 3 (by rfl) ⟨493214, by rfl⟩ : syracuseStep 2630477 = 986429) (by norm_num)
theorem B2630501 : Blo 1752577 2630501 := bbase (se 4 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 2630501 = 493219) (by norm_num)
theorem B15991669 : Blo 1752577 15991669 := bbase (se 5 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 15991669 = 1499219) (by norm_num)
theorem B2630525 : Blo 1752577 2630525 := bbase (se 3 (by rfl) ⟨493223, by rfl⟩ : syracuseStep 2630525 = 986447) (by norm_num)
theorem B2958221 : Blo 1752577 2958221 := bbase (se 3 (by rfl) ⟨554666, by rfl⟩ : syracuseStep 2958221 = 1109333) (by norm_num)
theorem B3556237 : Blo 1752577 3556237 := bbase (se 3 (by rfl) ⟨666794, by rfl⟩ : syracuseStep 3556237 = 1333589) (by norm_num)
theorem B2630549 : Blo 1752577 2630549 := bbase (se 6 (by rfl) ⟨61653, by rfl⟩ : syracuseStep 2630549 = 123307) (by norm_num)
theorem B2630573 : Blo 1752577 2630573 := bbase (se 3 (by rfl) ⟨493232, by rfl⟩ : syracuseStep 2630573 = 986465) (by norm_num)
theorem B8872901 : Blo 1752577 8872901 := bbase (se 4 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 8872901 = 1663669) (by norm_num)
theorem B2630597 : Blo 1752577 2630597 := bbase (se 4 (by rfl) ⟨246618, by rfl⟩ : syracuseStep 2630597 = 493237) (by norm_num)
theorem B2630621 : Blo 1752577 2630621 := bbase (se 3 (by rfl) ⟨493241, by rfl⟩ : syracuseStep 2630621 = 986483) (by norm_num)
theorem B2630645 : Blo 1752577 2630645 := bbase (se 5 (by rfl) ⟨123311, by rfl⟩ : syracuseStep 2630645 = 246623) (by norm_num)
theorem B2958349 : Blo 1752577 2958349 := bbase (se 3 (by rfl) ⟨554690, by rfl⟩ : syracuseStep 2958349 = 1109381) (by norm_num)
theorem B2630669 : Blo 1752577 2630669 := bbase (se 3 (by rfl) ⟨493250, by rfl⟩ : syracuseStep 2630669 = 986501) (by norm_num)
theorem B19973141 : Blo 1752577 19973141 := bbase (se 6 (by rfl) ⟨468120, by rfl⟩ : syracuseStep 19973141 = 936241) (by norm_num)
theorem B2630693 : Blo 1752577 2630693 := bbase (se 4 (by rfl) ⟨246627, by rfl⟩ : syracuseStep 2630693 = 493255) (by norm_num)
theorem B2630717 : Blo 1752577 2630717 := bbase (se 3 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 2630717 = 986519) (by norm_num)
theorem B2630741 : Blo 1752577 2630741 := bbase (se 8 (by rfl) ⟨15414, by rfl⟩ : syracuseStep 2630741 = 30829) (by norm_num)
theorem B2958437 : Blo 1752577 2958437 := bbase (se 4 (by rfl) ⟨277353, by rfl⟩ : syracuseStep 2958437 = 554707) (by norm_num)
theorem B4441189 : Blo 1752577 4441189 := bbase (se 4 (by rfl) ⟨416361, by rfl⟩ : syracuseStep 4441189 = 832723) (by norm_num)
theorem B1999981 : Blo 1752577 1999981 := bbase (se 3 (by rfl) ⟨374996, by rfl⟩ : syracuseStep 1999981 = 749993) (by norm_num)
theorem B2630765 : Blo 1752577 2630765 := bbase (se 3 (by rfl) ⟨493268, by rfl⟩ : syracuseStep 2630765 = 986537) (by norm_num)
theorem B6661237 : Blo 1752577 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B2630789 : Blo 1752577 2630789 := bbase (se 4 (by rfl) ⟨246636, by rfl⟩ : syracuseStep 2630789 = 493273) (by norm_num)
theorem B2630813 : Blo 1752577 2630813 := bbase (se 3 (by rfl) ⟨493277, by rfl⟩ : syracuseStep 2630813 = 986555) (by norm_num)
theorem B2368693 : Blo 1752577 2368693 := bbase (se 5 (by rfl) ⟨111032, by rfl⟩ : syracuseStep 2368693 = 222065) (by norm_num)
theorem B2630837 : Blo 1752577 2630837 := bbase (se 5 (by rfl) ⟨123320, by rfl⟩ : syracuseStep 2630837 = 246641) (by norm_num)
theorem B2630861 : Blo 1752577 2630861 := bbase (se 3 (by rfl) ⟨493286, by rfl⟩ : syracuseStep 2630861 = 986573) (by norm_num)
theorem B2106577 : Blo 1752577 2106577 := bbase (se 2 (by rfl) ⟨789966, by rfl⟩ : syracuseStep 2106577 = 1579933) (by norm_num)
theorem B5915861 : Blo 1752577 5915861 := bbase (se 7 (by rfl) ⟨69326, by rfl⟩ : syracuseStep 5915861 = 138653) (by norm_num)
theorem B2106581 : Blo 1752577 2106581 := bbase (se 7 (by rfl) ⟨24686, by rfl⟩ : syracuseStep 2106581 = 49373) (by norm_num)
theorem B2958565 : Blo 1752577 2958565 := bbase (se 4 (by rfl) ⟨277365, by rfl⟩ : syracuseStep 2958565 = 554731) (by norm_num)
theorem B2630885 : Blo 1752577 2630885 := bbase (se 4 (by rfl) ⟨246645, by rfl⟩ : syracuseStep 2630885 = 493291) (by norm_num)
theorem B2630909 : Blo 1752577 2630909 := bbase (se 3 (by rfl) ⟨493295, by rfl⟩ : syracuseStep 2630909 = 986591) (by norm_num)
theorem B2630933 : Blo 1752577 2630933 := bbase (se 6 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 2630933 = 123325) (by norm_num)
theorem B3999013 : Blo 1752577 3999013 := bbase (se 4 (by rfl) ⟨374907, by rfl⟩ : syracuseStep 3999013 = 749815) (by norm_num)
theorem B2630957 : Blo 1752577 2630957 := bbase (se 3 (by rfl) ⟨493304, by rfl⟩ : syracuseStep 2630957 = 986609) (by norm_num)
theorem B3327293 : Blo 1752577 3327293 := bbase (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) (by norm_num)
theorem B2958653 : Blo 1752577 2958653 := bbase (se 3 (by rfl) ⟨554747, by rfl⟩ : syracuseStep 2958653 = 1109495) (by norm_num)
theorem B2630981 : Blo 1752577 2630981 := bbase (se 4 (by rfl) ⟨246654, by rfl⟩ : syracuseStep 2630981 = 493309) (by norm_num)
theorem B2631005 : Blo 1752577 2631005 := bbase (se 3 (by rfl) ⟨493313, by rfl⟩ : syracuseStep 2631005 = 986627) (by norm_num)
theorem B2631029 : Blo 1752577 2631029 := bbase (se 5 (by rfl) ⟨123329, by rfl⟩ : syracuseStep 2631029 = 246659) (by norm_num)
theorem B2368909 : Blo 1752577 2368909 := bbase (se 3 (by rfl) ⟨444170, by rfl⟩ : syracuseStep 2368909 = 888341) (by norm_num)
theorem B2631053 : Blo 1752577 2631053 := bbase (se 3 (by rfl) ⟨493322, by rfl⟩ : syracuseStep 2631053 = 986645) (by norm_num)
theorem B4212125 : Blo 1752577 4212125 := bbase (se 3 (by rfl) ⟨789773, by rfl⟩ : syracuseStep 4212125 = 1579547) (by norm_num)
theorem B2631077 : Blo 1752577 2631077 := bbase (se 4 (by rfl) ⟨246663, by rfl⟩ : syracuseStep 2631077 = 493327) (by norm_num)
theorem B6661541 : Blo 1752577 6661541 := bbase (se 4 (by rfl) ⟨624519, by rfl⟩ : syracuseStep 6661541 = 1249039) (by norm_num)
theorem B2958781 : Blo 1752577 2958781 := bbase (se 3 (by rfl) ⟨554771, by rfl⟩ : syracuseStep 2958781 = 1109543) (by norm_num)
theorem B2631101 : Blo 1752577 2631101 := bbase (se 3 (by rfl) ⟨493331, by rfl⟩ : syracuseStep 2631101 = 986663) (by norm_num)
theorem B2631125 : Blo 1752577 2631125 := bbase (se 7 (by rfl) ⟨30833, by rfl⟩ : syracuseStep 2631125 = 61667) (by norm_num)
theorem B2631149 : Blo 1752577 2631149 := bbase (se 3 (by rfl) ⟨493340, by rfl⟩ : syracuseStep 2631149 = 986681) (by norm_num)
theorem B2631173 : Blo 1752577 2631173 := bbase (se 4 (by rfl) ⟨246672, by rfl⟩ : syracuseStep 2631173 = 493345) (by norm_num)
theorem B2958869 : Blo 1752577 2958869 := bbase (se 6 (by rfl) ⟨69348, by rfl⟩ : syracuseStep 2958869 = 138697) (by norm_num)
theorem B2631197 : Blo 1752577 2631197 := bbase (se 3 (by rfl) ⟨493349, by rfl⟩ : syracuseStep 2631197 = 986699) (by norm_num)
theorem B2631221 : Blo 1752577 2631221 := bbase (se 5 (by rfl) ⟨123338, by rfl⟩ : syracuseStep 2631221 = 246677) (by norm_num)
theorem B2631245 : Blo 1752577 2631245 := bbase (se 3 (by rfl) ⟨493358, by rfl⟩ : syracuseStep 2631245 = 986717) (by norm_num)
theorem B3327581 : Blo 1752577 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B4212317 : Blo 1752577 4212317 := bbase (se 3 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 4212317 = 1579619) (by norm_num)
theorem B2631269 : Blo 1752577 2631269 := bbase (se 4 (by rfl) ⟨246681, by rfl⟩ : syracuseStep 2631269 = 493363) (by norm_num)
theorem B2631293 : Blo 1752577 2631293 := bbase (se 3 (by rfl) ⟨493367, by rfl⟩ : syracuseStep 2631293 = 986735) (by norm_num)
theorem B5916293 : Blo 1752577 5916293 := bbase (se 4 (by rfl) ⟨554652, by rfl⟩ : syracuseStep 5916293 = 1109305) (by norm_num)
theorem B4269709 : Blo 1752577 4269709 := bbase (se 3 (by rfl) ⟨800570, by rfl⟩ : syracuseStep 4269709 = 1601141) (by norm_num)
theorem B2958997 : Blo 1752577 2958997 := bbase (se 6 (by rfl) ⟨69351, by rfl⟩ : syracuseStep 2958997 = 138703) (by norm_num)
theorem B2631317 : Blo 1752577 2631317 := bbase (se 6 (by rfl) ⟨61671, by rfl⟩ : syracuseStep 2631317 = 123343) (by norm_num)
theorem B2631341 : Blo 1752577 2631341 := bbase (se 3 (by rfl) ⟨493376, by rfl⟩ : syracuseStep 2631341 = 986753) (by norm_num)
theorem B4212413 : Blo 1752577 4212413 := bbase (se 3 (by rfl) ⟨789827, by rfl⟩ : syracuseStep 4212413 = 1579655) (by norm_num)
theorem B3745477 : Blo 1752577 3745477 := bbase (se 4 (by rfl) ⟨351138, by rfl⟩ : syracuseStep 3745477 = 702277) (by norm_num)
theorem B2631365 : Blo 1752577 2631365 := bbase (se 4 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 2631365 = 493381) (by norm_num)
theorem B2107081 : Blo 1752577 2107081 := bbase (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) (by norm_num)
theorem B2631389 : Blo 1752577 2631389 := bbase (se 3 (by rfl) ⟨493385, by rfl⟩ : syracuseStep 2631389 = 986771) (by norm_num)
theorem B2959085 : Blo 1752577 2959085 := bbase (se 3 (by rfl) ⟨554828, by rfl⟩ : syracuseStep 2959085 = 1109657) (by norm_num)
theorem B3327733 : Blo 1752577 3327733 := bbase (se 5 (by rfl) ⟨155987, by rfl⟩ : syracuseStep 3327733 = 311975) (by norm_num)
theorem B2631413 : Blo 1752577 2631413 := bbase (se 5 (by rfl) ⟨123347, by rfl⟩ : syracuseStep 2631413 = 246695) (by norm_num)
theorem B2631437 : Blo 1752577 2631437 := bbase (se 3 (by rfl) ⟨493394, by rfl⟩ : syracuseStep 2631437 = 986789) (by norm_num)
theorem B2631461 : Blo 1752577 2631461 := bbase (se 4 (by rfl) ⟨246699, by rfl⟩ : syracuseStep 2631461 = 493399) (by norm_num)
theorem B9987893 : Blo 1752577 9987893 := bbase (se 5 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 9987893 = 936365) (by norm_num)
theorem B8881973 : Blo 1752577 8881973 := bbase (se 5 (by rfl) ⟨416342, by rfl⟩ : syracuseStep 8881973 = 832685) (by norm_num)
theorem B3745597 : Blo 1752577 3745597 := bbase (se 3 (by rfl) ⟨702299, by rfl⟩ : syracuseStep 3745597 = 1404599) (by norm_num)
theorem B2631485 : Blo 1752577 2631485 := bbase (se 3 (by rfl) ⟨493403, by rfl⟩ : syracuseStep 2631485 = 986807) (by norm_num)
theorem B2631509 : Blo 1752577 2631509 := bbase (se 9 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 2631509 = 15419) (by norm_num)
theorem B11241301 : Blo 1752577 11241301 := bbase (se 9 (by rfl) ⟨32933, by rfl⟩ : syracuseStep 11241301 = 65867) (by norm_num)
theorem B2959213 : Blo 1752577 2959213 := bbase (se 3 (by rfl) ⟨554852, by rfl⟩ : syracuseStep 2959213 = 1109705) (by norm_num)
theorem B2631533 : Blo 1752577 2631533 := bbase (se 3 (by rfl) ⟨493412, by rfl⟩ : syracuseStep 2631533 = 986825) (by norm_num)
theorem B2631557 : Blo 1752577 2631557 := bbase (se 4 (by rfl) ⟨246708, by rfl⟩ : syracuseStep 2631557 = 493417) (by norm_num)
theorem B2631581 : Blo 1752577 2631581 := bbase (se 3 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 2631581 = 986843) (by norm_num)
theorem B2631605 : Blo 1752577 2631605 := bbase (se 5 (by rfl) ⟨123356, by rfl⟩ : syracuseStep 2631605 = 246713) (by norm_num)
theorem B2959301 : Blo 1752577 2959301 := bbase (se 4 (by rfl) ⟨277434, by rfl⟩ : syracuseStep 2959301 = 554869) (by norm_num)
theorem B2631629 : Blo 1752577 2631629 := bbase (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) (by norm_num)
theorem B2631653 : Blo 1752577 2631653 := bbase (se 4 (by rfl) ⟨246717, by rfl⟩ : syracuseStep 2631653 = 493435) (by norm_num)
theorem B2631677 : Blo 1752577 2631677 := bbase (se 3 (by rfl) ⟨493439, by rfl⟩ : syracuseStep 2631677 = 986879) (by norm_num)
theorem B4990997 : Blo 1752577 4990997 := bbase (se 6 (by rfl) ⟨116976, by rfl⟩ : syracuseStep 4990997 = 233953) (by norm_num)
theorem B2631701 : Blo 1752577 2631701 := bbase (se 6 (by rfl) ⟨61680, by rfl⟩ : syracuseStep 2631701 = 123361) (by norm_num)
theorem B3328037 : Blo 1752577 3328037 := bbase (se 4 (by rfl) ⟨312003, by rfl⟩ : syracuseStep 3328037 = 624007) (by norm_num)
theorem B2631725 : Blo 1752577 2631725 := bbase (se 3 (by rfl) ⟨493448, by rfl⟩ : syracuseStep 2631725 = 986897) (by norm_num)
theorem B5916725 : Blo 1752577 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B3745853 : Blo 1752577 3745853 := bbase (se 3 (by rfl) ⟨702347, by rfl⟩ : syracuseStep 3745853 = 1404695) (by norm_num)
theorem B2959429 : Blo 1752577 2959429 := bbase (se 4 (by rfl) ⟨277446, by rfl⟩ : syracuseStep 2959429 = 554893) (by norm_num)
theorem B2107465 : Blo 1752577 2107465 := bbase (se 2 (by rfl) ⟨790299, by rfl⟩ : syracuseStep 2107465 = 1580599) (by norm_num)
theorem B2631749 : Blo 1752577 2631749 := bbase (se 4 (by rfl) ⟨246726, by rfl⟩ : syracuseStep 2631749 = 493453) (by norm_num)
theorem B2631773 : Blo 1752577 2631773 := bbase (se 3 (by rfl) ⟨493457, by rfl⟩ : syracuseStep 2631773 = 986915) (by norm_num)
theorem B2631797 : Blo 1752577 2631797 := bbase (se 5 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 2631797 = 246731) (by norm_num)
theorem B2631821 : Blo 1752577 2631821 := bbase (se 3 (by rfl) ⟨493466, by rfl⟩ : syracuseStep 2631821 = 986933) (by norm_num)
theorem B2959517 : Blo 1752577 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B2631845 : Blo 1752577 2631845 := bbase (se 4 (by rfl) ⟨246735, by rfl⟩ : syracuseStep 2631845 = 493471) (by norm_num)
theorem B8874197 : Blo 1752577 8874197 := bbase (se 7 (by rfl) ⟨103994, by rfl⟩ : syracuseStep 8874197 = 207989) (by norm_num)
theorem B2566405 : Blo 1752577 2566405 := bbase (se 4 (by rfl) ⟨240600, by rfl⟩ : syracuseStep 2566405 = 481201) (by norm_num)
theorem B5335301 : Blo 1752577 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B2959645 : Blo 1752577 2959645 := bbase (se 3 (by rfl) ⟨554933, by rfl⟩ : syracuseStep 2959645 = 1109867) (by norm_num)
theorem B2279773 : Blo 1752577 2279773 := bbase (se 3 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 2279773 = 854915) (by norm_num)
theorem B2959733 : Blo 1752577 2959733 := bbase (se 5 (by rfl) ⟨138737, by rfl⟩ : syracuseStep 2959733 = 277475) (by norm_num)
theorem B10668437 : Blo 1752577 10668437 := bbase (se 6 (by rfl) ⟨250041, by rfl⟩ : syracuseStep 10668437 = 500083) (by norm_num)
theorem B2664925 : Blo 1752577 2664925 := bbase (se 3 (by rfl) ⟨499673, by rfl⟩ : syracuseStep 2664925 = 999347) (by norm_num)
theorem B5917157 : Blo 1752577 5917157 := bbase (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) (by norm_num)
theorem B4000229 : Blo 1752577 4000229 := bbase (se 4 (by rfl) ⟨375021, by rfl⟩ : syracuseStep 4000229 = 750043) (by norm_num)
theorem B2959861 : Blo 1752577 2959861 := bbase (se 5 (by rfl) ⟨138743, by rfl⟩ : syracuseStep 2959861 = 277487) (by norm_num)
theorem B2959949 : Blo 1752577 2959949 := bbase (se 3 (by rfl) ⟨554990, by rfl⟩ : syracuseStep 2959949 = 1109981) (by norm_num)
theorem B2402941 : Blo 1752577 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B4991669 : Blo 1752577 4991669 := bbase (se 5 (by rfl) ⟨233984, by rfl⟩ : syracuseStep 4991669 = 467969) (by norm_num)
theorem B2960077 : Blo 1752577 2960077 := bbase (se 3 (by rfl) ⟨555014, by rfl⟩ : syracuseStep 2960077 = 1110029) (by norm_num)
theorem B3328789 : Blo 1752577 3328789 := bbase (se 6 (by rfl) ⟨78018, by rfl⟩ : syracuseStep 3328789 = 156037) (by norm_num)
theorem B16001813 : Blo 1752577 16001813 := bbase (se 6 (by rfl) ⟨375042, by rfl⟩ : syracuseStep 16001813 = 750085) (by norm_num)
theorem B2960165 : Blo 1752577 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B4000565 : Blo 1752577 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B5917589 : Blo 1752577 5917589 := bbase (se 6 (by rfl) ⟨138693, by rfl⟩ : syracuseStep 5917589 = 277387) (by norm_num)
theorem B2280353 : Blo 1752577 2280353 := bbase (se 2 (by rfl) ⟨855132, by rfl⟩ : syracuseStep 2280353 = 1710265) (by norm_num)
theorem B3328933 : Blo 1752577 3328933 := bbase (se 4 (by rfl) ⟨312087, by rfl⟩ : syracuseStep 3328933 = 624175) (by norm_num)
theorem B2960293 : Blo 1752577 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B3943349 : Blo 1752577 3943349 := bbase (se 5 (by rfl) ⟨184844, by rfl⟩ : syracuseStep 3943349 = 369689) (by norm_num)
theorem B3746741 : Blo 1752577 3746741 := bbase (se 5 (by rfl) ⟨175628, by rfl⟩ : syracuseStep 3746741 = 351257) (by norm_num)
theorem B3943421 : Blo 1752577 3943421 := bbase (se 3 (by rfl) ⟨739391, by rfl⟩ : syracuseStep 3943421 = 1478783) (by norm_num)
theorem B2960381 : Blo 1752577 2960381 := bbase (se 3 (by rfl) ⟨555071, by rfl⟩ : syracuseStep 2960381 = 1110143) (by norm_num)
theorem B6319109 : Blo 1752577 6319109 := bbase (se 4 (by rfl) ⟨592416, by rfl⟩ : syracuseStep 6319109 = 1184833) (by norm_num)
theorem B3943493 : Blo 1752577 3943493 := bbase (se 4 (by rfl) ⟨369702, by rfl⟩ : syracuseStep 3943493 = 739405) (by norm_num)
theorem B3329093 : Blo 1752577 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B4992101 : Blo 1752577 4992101 := bbase (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) (by norm_num)
theorem B2960509 : Blo 1752577 2960509 := bbase (se 3 (by rfl) ⟨555095, by rfl⟩ : syracuseStep 2960509 = 1110191) (by norm_num)
theorem B3943565 : Blo 1752577 3943565 := bbase (se 3 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 3943565 = 1478837) (by norm_num)
theorem B3124373 : Blo 1752577 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B3746981 : Blo 1752577 3746981 := bbase (se 4 (by rfl) ⟨351279, by rfl⟩ : syracuseStep 3746981 = 702559) (by norm_num)
theorem B3943637 : Blo 1752577 3943637 := bbase (se 7 (by rfl) ⟨46214, by rfl⟩ : syracuseStep 3943637 = 92429) (by norm_num)
theorem B3329237 : Blo 1752577 3329237 := bbase (se 7 (by rfl) ⟨39014, by rfl⟩ : syracuseStep 3329237 = 78029) (by norm_num)
theorem B2960597 : Blo 1752577 2960597 := bbase (se 7 (by rfl) ⟨34694, by rfl⟩ : syracuseStep 2960597 = 69389) (by norm_num)
theorem B7204069 : Blo 1752577 7204069 := bbase (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) (by norm_num)
theorem B3943709 : Blo 1752577 3943709 := bbase (se 3 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 3943709 = 1478891) (by norm_num)
theorem B6319397 : Blo 1752577 6319397 := bbase (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) (by norm_num)
theorem B5918021 : Blo 1752577 5918021 := bbase (se 4 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 5918021 = 1109629) (by norm_num)
theorem B2960725 : Blo 1752577 2960725 := bbase (se 11 (by rfl) ⟨2168, by rfl⟩ : syracuseStep 2960725 = 4337) (by norm_num)
theorem B3943781 : Blo 1752577 3943781 := bbase (se 4 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 3943781 = 739459) (by norm_num)
theorem B3943853 : Blo 1752577 3943853 := bbase (se 3 (by rfl) ⟨739472, by rfl⟩ : syracuseStep 3943853 = 1478945) (by norm_num)
theorem B2960813 : Blo 1752577 2960813 := bbase (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) (by norm_num)
theorem B5615077 : Blo 1752577 5615077 := bbase (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) (by norm_num)
theorem B8875493 : Blo 1752577 8875493 := bbase (se 4 (by rfl) ⟨832077, by rfl⟩ : syracuseStep 8875493 = 1664155) (by norm_num)
theorem B3943925 : Blo 1752577 3943925 := bbase (se 5 (by rfl) ⟨184871, by rfl⟩ : syracuseStep 3943925 = 369743) (by norm_num)
theorem B3329525 : Blo 1752577 3329525 := bbase (se 5 (by rfl) ⟨156071, by rfl⟩ : syracuseStep 3329525 = 312143) (by norm_num)
theorem B3943997 : Blo 1752577 3943997 := bbase (se 3 (by rfl) ⟨739499, by rfl⟩ : syracuseStep 3943997 = 1478999) (by norm_num)
theorem B3944069 : Blo 1752577 3944069 := bbase (se 4 (by rfl) ⟨369756, by rfl⟩ : syracuseStep 3944069 = 739513) (by norm_num)
theorem B3329677 : Blo 1752577 3329677 := bbase (se 3 (by rfl) ⟨624314, by rfl⟩ : syracuseStep 3329677 = 1248629) (by norm_num)
theorem B3944141 : Blo 1752577 3944141 := bbase (se 3 (by rfl) ⟨739526, by rfl⟩ : syracuseStep 3944141 = 1479053) (by norm_num)
theorem B5918453 : Blo 1752577 5918453 := bbase (se 5 (by rfl) ⟨277427, by rfl⟩ : syracuseStep 5918453 = 554855) (by norm_num)
theorem B3944213 : Blo 1752577 3944213 := bbase (se 6 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 3944213 = 184885) (by norm_num)
theorem B25620245 : Blo 1752577 25620245 := bbase (se 6 (by rfl) ⟨600474, by rfl⟩ : syracuseStep 25620245 = 1200949) (by norm_num)
theorem B1871645 : Blo 1752577 1871645 := bbase (se 3 (by rfl) ⟨350933, by rfl⟩ : syracuseStep 1871645 = 701867) (by norm_num)
theorem B7491365 : Blo 1752577 7491365 := bbase (se 4 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 7491365 = 1404631) (by norm_num)
theorem B6844229 : Blo 1752577 6844229 := bbase (se 4 (by rfl) ⟨641646, by rfl⟩ : syracuseStep 6844229 = 1283293) (by norm_num)
theorem B4501325 : Blo 1752577 4501325 := bbase (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) (by norm_num)
theorem B4992853 : Blo 1752577 4992853 := bbase (se 9 (by rfl) ⟨14627, by rfl⟩ : syracuseStep 4992853 = 29255) (by norm_num)
theorem B1871705 : Blo 1752577 1871705 := bbase (se 2 (by rfl) ⟨701889, by rfl⟩ : syracuseStep 1871705 = 1403779) (by norm_num)
theorem B3944285 : Blo 1752577 3944285 := bbase (se 3 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 3944285 = 1479107) (by norm_num)
theorem B4738933 : Blo 1752577 4738933 := bbase (se 5 (by rfl) ⟨222137, by rfl⟩ : syracuseStep 4738933 = 444275) (by norm_num)
theorem B6655877 : Blo 1752577 6655877 := bbase (se 4 (by rfl) ⟨623988, by rfl⟩ : syracuseStep 6655877 = 1247977) (by norm_num)
theorem B3944357 : Blo 1752577 3944357 := bbase (se 4 (by rfl) ⟨369783, by rfl⟩ : syracuseStep 3944357 = 739567) (by norm_num)
theorem B3329981 : Blo 1752577 3329981 := bbase (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) (by norm_num)
theorem B1871833 : Blo 1752577 1871833 := bbase (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) (by norm_num)
theorem B3944429 : Blo 1752577 3944429 := bbase (se 3 (by rfl) ⟨739580, by rfl⟩ : syracuseStep 3944429 = 1479161) (by norm_num)
theorem B12816373 : Blo 1752577 12816373 := bbase (se 5 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 12816373 = 1201535) (by norm_num)
theorem B3944501 : Blo 1752577 3944501 := bbase (se 5 (by rfl) ⟨184898, by rfl⟩ : syracuseStep 3944501 = 369797) (by norm_num)
theorem B4214845 : Blo 1752577 4214845 := bbase (se 3 (by rfl) ⟨790283, by rfl⟩ : syracuseStep 4214845 = 1580567) (by norm_num)
theorem B3944573 : Blo 1752577 3944573 := bbase (se 3 (by rfl) ⟨739607, by rfl⟩ : syracuseStep 3944573 = 1479215) (by norm_num)
theorem B6656165 : Blo 1752577 6656165 := bbase (se 4 (by rfl) ⟨624015, by rfl⟩ : syracuseStep 6656165 = 1248031) (by norm_num)
theorem B5918885 : Blo 1752577 5918885 := bbase (se 4 (by rfl) ⟨554895, by rfl⟩ : syracuseStep 5918885 = 1109791) (by norm_num)
theorem B11235509 : Blo 1752577 11235509 := bbase (se 5 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 11235509 = 1053329) (by norm_num)
theorem B2666677 : Blo 1752577 2666677 := bbase (se 5 (by rfl) ⟨125000, by rfl⟩ : syracuseStep 2666677 = 250001) (by norm_num)
theorem B3944645 : Blo 1752577 3944645 := bbase (se 4 (by rfl) ⟨369810, by rfl⟩ : syracuseStep 3944645 = 739621) (by norm_num)
theorem B3944717 : Blo 1752577 3944717 := bbase (se 3 (by rfl) ⟨739634, by rfl⟩ : syracuseStep 3944717 = 1479269) (by norm_num)
theorem B5615909 : Blo 1752577 5615909 := bbase (se 4 (by rfl) ⟨526491, by rfl⟩ : syracuseStep 5615909 = 1052983) (by norm_num)
theorem B7590181 : Blo 1752577 7590181 := bbase (se 4 (by rfl) ⟨711579, by rfl⟩ : syracuseStep 7590181 = 1423159) (by norm_num)
theorem B4436309 : Blo 1752577 4436309 := bbase (se 10 (by rfl) ⟨6498, by rfl⟩ : syracuseStep 4436309 = 12997) (by norm_num)
theorem B3944789 : Blo 1752577 3944789 := bbase (se 10 (by rfl) ⟨5778, by rfl⟩ : syracuseStep 3944789 = 11557) (by norm_num)
theorem B9613685 : Blo 1752577 9613685 := bbase (se 5 (by rfl) ⟨450641, by rfl⟩ : syracuseStep 9613685 = 901283) (by norm_num)
theorem B4215181 : Blo 1752577 4215181 := bbase (se 3 (by rfl) ⟨790346, by rfl⟩ : syracuseStep 4215181 = 1580693) (by norm_num)
theorem B1872277 : Blo 1752577 1872277 := bbase (se 6 (by rfl) ⟨43881, by rfl⟩ : syracuseStep 1872277 = 87763) (by norm_num)
theorem B3944861 : Blo 1752577 3944861 := bbase (se 3 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 3944861 = 1479323) (by norm_num)
theorem B3944933 : Blo 1752577 3944933 := bbase (se 4 (by rfl) ⟨369837, by rfl⟩ : syracuseStep 3944933 = 739675) (by norm_num)
theorem B1872397 : Blo 1752577 1872397 := bbase (se 3 (by rfl) ⟨351074, by rfl⟩ : syracuseStep 1872397 = 702149) (by norm_num)
theorem B3945005 : Blo 1752577 3945005 := bbase (se 3 (by rfl) ⟨739688, by rfl⟩ : syracuseStep 3945005 = 1479377) (by norm_num)
theorem B5919317 : Blo 1752577 5919317 := bbase (se 8 (by rfl) ⟨34683, by rfl⟩ : syracuseStep 5919317 = 69367) (by norm_num)
theorem B8999525 : Blo 1752577 8999525 := bbase (se 4 (by rfl) ⟨843705, by rfl⟩ : syracuseStep 8999525 = 1687411) (by norm_num)
theorem B3945077 : Blo 1752577 3945077 := bbase (se 5 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 3945077 = 369851) (by norm_num)
theorem B4436653 : Blo 1752577 4436653 := bbase (se 3 (by rfl) ⟨831872, by rfl⟩ : syracuseStep 4436653 = 1663745) (by norm_num)
theorem B3330733 : Blo 1752577 3330733 := bbase (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) (by norm_num)
theorem B3945149 : Blo 1752577 3945149 := bbase (se 3 (by rfl) ⟨739715, by rfl⟩ : syracuseStep 3945149 = 1479431) (by norm_num)
theorem B8876789 : Blo 1752577 8876789 := bbase (se 5 (by rfl) ⟨416099, by rfl⟩ : syracuseStep 8876789 = 832199) (by norm_num)
theorem B3945221 : Blo 1752577 3945221 := bbase (se 4 (by rfl) ⟨369864, by rfl⟩ : syracuseStep 3945221 = 739729) (by norm_num)
theorem B1872649 : Blo 1752577 1872649 := bbase (se 2 (by rfl) ⟨702243, by rfl⟩ : syracuseStep 1872649 = 1404487) (by norm_num)
theorem B1872653 : Blo 1752577 1872653 := bbase (se 3 (by rfl) ⟨351122, by rfl⟩ : syracuseStep 1872653 = 702245) (by norm_num)
theorem B13316885 : Blo 1752577 13316885 := bbase (se 6 (by rfl) ⟨312114, by rfl⟩ : syracuseStep 13316885 = 624229) (by norm_num)
theorem B4436765 : Blo 1752577 4436765 := bbase (se 3 (by rfl) ⟨831893, by rfl⟩ : syracuseStep 4436765 = 1663787) (by norm_num)
theorem B3330877 : Blo 1752577 3330877 := bbase (se 3 (by rfl) ⟨624539, by rfl⟩ : syracuseStep 3330877 = 1249079) (by norm_num)
theorem B3945293 : Blo 1752577 3945293 := bbase (se 3 (by rfl) ⟨739742, by rfl⟩ : syracuseStep 3945293 = 1479485) (by norm_num)
theorem B3945365 : Blo 1752577 3945365 := bbase (se 6 (by rfl) ⟨92469, by rfl⟩ : syracuseStep 3945365 = 184939) (by norm_num)
theorem B4436957 : Blo 1752577 4436957 := bbase (se 3 (by rfl) ⟨831929, by rfl⟩ : syracuseStep 4436957 = 1663859) (by norm_num)
theorem B3945437 : Blo 1752577 3945437 := bbase (se 3 (by rfl) ⟨739769, by rfl⟩ : syracuseStep 3945437 = 1479539) (by norm_num)
theorem B5919749 : Blo 1752577 5919749 := bbase (se 4 (by rfl) ⟨554976, by rfl⟩ : syracuseStep 5919749 = 1109953) (by norm_num)
theorem B3945509 : Blo 1752577 3945509 := bbase (se 4 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 3945509 = 739783) (by norm_num)
theorem B3847253 : Blo 1752577 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B3945581 : Blo 1752577 3945581 := bbase (se 3 (by rfl) ⟨739796, by rfl⟩ : syracuseStep 3945581 = 1479593) (by norm_num)
theorem B3159173 : Blo 1752577 3159173 := bbase (se 4 (by rfl) ⟨296172, by rfl⟩ : syracuseStep 3159173 = 592345) (by norm_num)
theorem B13309109 : Blo 1752577 13309109 := bbase (se 5 (by rfl) ⟨623864, by rfl⟩ : syracuseStep 13309109 = 1247729) (by norm_num)
theorem B3945653 : Blo 1752577 3945653 := bbase (se 5 (by rfl) ⟨184952, by rfl⟩ : syracuseStep 3945653 = 369905) (by norm_num)
theorem B3159253 : Blo 1752577 3159253 := bbase (se 7 (by rfl) ⟨37022, by rfl⟩ : syracuseStep 3159253 = 74045) (by norm_num)
theorem B3945725 : Blo 1752577 3945725 := bbase (se 3 (by rfl) ⟨739823, by rfl⟩ : syracuseStep 3945725 = 1479647) (by norm_num)
theorem B2667773 : Blo 1752577 2667773 := bbase (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) (by norm_num)
theorem B4437301 : Blo 1752577 4437301 := bbase (se 5 (by rfl) ⟨207998, by rfl⟩ : syracuseStep 4437301 = 415997) (by norm_num)
theorem B1873217 : Blo 1752577 1873217 := bbase (se 2 (by rfl) ⟨702456, by rfl⟩ : syracuseStep 1873217 = 1404913) (by norm_num)
theorem B6657349 : Blo 1752577 6657349 := bbase (se 4 (by rfl) ⟨624126, by rfl⟩ : syracuseStep 6657349 = 1248253) (by norm_num)
theorem B3945797 : Blo 1752577 3945797 := bbase (se 4 (by rfl) ⟨369918, by rfl⟩ : syracuseStep 3945797 = 739837) (by norm_num)
theorem B3945869 : Blo 1752577 3945869 := bbase (se 3 (by rfl) ⟨739850, by rfl⟩ : syracuseStep 3945869 = 1479701) (by norm_num)
theorem B4437413 : Blo 1752577 4437413 := bbase (se 4 (by rfl) ⟨416007, by rfl⟩ : syracuseStep 4437413 = 832015) (by norm_num)
theorem B5920181 : Blo 1752577 5920181 := bbase (se 5 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 5920181 = 555017) (by norm_num)
theorem B1971661 : Blo 1752577 1971661 := bbase (se 3 (by rfl) ⟨369686, by rfl⟩ : syracuseStep 1971661 = 739373) (by norm_num)
theorem B3945941 : Blo 1752577 3945941 := bbase (se 7 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 3945941 = 92483) (by norm_num)
theorem B1971697 : Blo 1752577 1971697 := bbase (se 2 (by rfl) ⟨739386, by rfl⟩ : syracuseStep 1971697 = 1478773) (by norm_num)
theorem B1873405 : Blo 1752577 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B1971733 : Blo 1752577 1971733 := bbase (se 6 (by rfl) ⟨46212, by rfl⟩ : syracuseStep 1971733 = 92425) (by norm_num)
theorem B7493141 : Blo 1752577 7493141 := bbase (se 6 (by rfl) ⟨175620, by rfl⟩ : syracuseStep 7493141 = 351241) (by norm_num)
theorem B3946013 : Blo 1752577 3946013 := bbase (se 3 (by rfl) ⟨739877, by rfl⟩ : syracuseStep 3946013 = 1479755) (by norm_num)
theorem B1971769 : Blo 1752577 1971769 := bbase (se 2 (by rfl) ⟨739413, by rfl⟩ : syracuseStep 1971769 = 1478827) (by norm_num)
theorem B1971805 : Blo 1752577 1971805 := bbase (se 3 (by rfl) ⟨369713, by rfl⟩ : syracuseStep 1971805 = 739427) (by norm_num)
theorem B4437605 : Blo 1752577 4437605 := bbase (se 4 (by rfl) ⟨416025, by rfl⟩ : syracuseStep 4437605 = 832051) (by norm_num)
theorem B3946085 : Blo 1752577 3946085 := bbase (se 4 (by rfl) ⟨369945, by rfl⟩ : syracuseStep 3946085 = 739891) (by norm_num)
theorem B6657653 : Blo 1752577 6657653 := bbase (se 5 (by rfl) ⟨312077, by rfl⟩ : syracuseStep 6657653 = 624155) (by norm_num)
theorem B1971841 : Blo 1752577 1971841 := bbase (se 2 (by rfl) ⟨739440, by rfl⟩ : syracuseStep 1971841 = 1478881) (by norm_num)
theorem B1971877 : Blo 1752577 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B3946157 : Blo 1752577 3946157 := bbase (se 3 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 3946157 = 1479809) (by norm_num)
theorem B1971913 : Blo 1752577 1971913 := bbase (se 2 (by rfl) ⟨739467, by rfl⟩ : syracuseStep 1971913 = 1478935) (by norm_num)
theorem B1971949 : Blo 1752577 1971949 := bbase (se 3 (by rfl) ⟨369740, by rfl⟩ : syracuseStep 1971949 = 739481) (by norm_num)
theorem B3946229 : Blo 1752577 3946229 := bbase (se 5 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 3946229 = 369959) (by norm_num)
theorem B7493381 : Blo 1752577 7493381 := bbase (se 4 (by rfl) ⟨702504, by rfl⟩ : syracuseStep 7493381 = 1405009) (by norm_num)
theorem B1971985 : Blo 1752577 1971985 := bbase (se 2 (by rfl) ⟨739494, by rfl⟩ : syracuseStep 1971985 = 1478989) (by norm_num)
theorem B1972021 : Blo 1752577 1972021 := bbase (se 5 (by rfl) ⟨92438, by rfl⟩ : syracuseStep 1972021 = 184877) (by norm_num)
theorem B3946301 : Blo 1752577 3946301 := bbase (se 3 (by rfl) ⟨739931, by rfl⟩ : syracuseStep 3946301 = 1479863) (by norm_num)
theorem B4052813 : Blo 1752577 4052813 := bbase (se 3 (by rfl) ⟨759902, by rfl⟩ : syracuseStep 4052813 = 1519805) (by norm_num)
theorem B1972057 : Blo 1752577 1972057 := bbase (se 2 (by rfl) ⟨739521, by rfl⟩ : syracuseStep 1972057 = 1479043) (by norm_num)
theorem B5920613 : Blo 1752577 5920613 := bbase (se 4 (by rfl) ⟨555057, by rfl⟩ : syracuseStep 5920613 = 1110115) (by norm_num)
theorem B4560749 : Blo 1752577 4560749 := bbase (se 3 (by rfl) ⟨855140, by rfl⟩ : syracuseStep 4560749 = 1710281) (by norm_num)
theorem B1972093 : Blo 1752577 1972093 := bbase (se 3 (by rfl) ⟨369767, by rfl⟩ : syracuseStep 1972093 = 739535) (by norm_num)
theorem B3946373 : Blo 1752577 3946373 := bbase (se 4 (by rfl) ⟨369972, by rfl⟩ : syracuseStep 3946373 = 739945) (by norm_num)
theorem B2807693 : Blo 1752577 2807693 := bbase (se 3 (by rfl) ⟨526442, by rfl⟩ : syracuseStep 2807693 = 1052885) (by norm_num)
theorem B1972129 : Blo 1752577 1972129 := bbase (se 2 (by rfl) ⟨739548, by rfl⟩ : syracuseStep 1972129 = 1479097) (by norm_num)
theorem B4437949 : Blo 1752577 4437949 := bbase (se 3 (by rfl) ⟨832115, by rfl⟩ : syracuseStep 4437949 = 1664231) (by norm_num)
theorem B1972165 : Blo 1752577 1972165 := bbase (se 4 (by rfl) ⟨184890, by rfl⟩ : syracuseStep 1972165 = 369781) (by norm_num)
theorem B3946445 : Blo 1752577 3946445 := bbase (se 3 (by rfl) ⟨739958, by rfl⟩ : syracuseStep 3946445 = 1479917) (by norm_num)
theorem B1972201 : Blo 1752577 1972201 := bbase (se 2 (by rfl) ⟨739575, by rfl⟩ : syracuseStep 1972201 = 1479151) (by norm_num)
theorem B8878085 : Blo 1752577 8878085 := bbase (se 4 (by rfl) ⟨832320, by rfl⟩ : syracuseStep 8878085 = 1664641) (by norm_num)
theorem B1972237 : Blo 1752577 1972237 := bbase (se 3 (by rfl) ⟨369794, by rfl⟩ : syracuseStep 1972237 = 739589) (by norm_num)
theorem B3946517 : Blo 1752577 3946517 := bbase (se 6 (by rfl) ⟨92496, by rfl⟩ : syracuseStep 3946517 = 184993) (by norm_num)
theorem B4438061 : Blo 1752577 4438061 := bbase (se 3 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 4438061 = 1664273) (by norm_num)
theorem B1972273 : Blo 1752577 1972273 := bbase (se 2 (by rfl) ⟨739602, by rfl⟩ : syracuseStep 1972273 = 1479205) (by norm_num)
theorem B7108661 : Blo 1752577 7108661 := bbase (se 5 (by rfl) ⟨333218, by rfl⟩ : syracuseStep 7108661 = 666437) (by norm_num)
theorem B5060677 : Blo 1752577 5060677 := bbase (se 4 (by rfl) ⟨474438, by rfl⟩ : syracuseStep 5060677 = 948877) (by norm_num)
theorem B1972309 : Blo 1752577 1972309 := bbase (se 8 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 1972309 = 23113) (by norm_num)
theorem B3946589 : Blo 1752577 3946589 := bbase (se 3 (by rfl) ⟨739985, by rfl⟩ : syracuseStep 3946589 = 1479971) (by norm_num)
theorem B3553397 : Blo 1752577 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B5617781 : Blo 1752577 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B1972345 : Blo 1752577 1972345 := bbase (se 2 (by rfl) ⟨739629, by rfl⟩ : syracuseStep 1972345 = 1479259) (by norm_num)
theorem B1972381 : Blo 1752577 1972381 := bbase (se 3 (by rfl) ⟨369821, by rfl⟩ : syracuseStep 1972381 = 739643) (by norm_num)
theorem B3946661 : Blo 1752577 3946661 := bbase (se 4 (by rfl) ⟨369999, by rfl⟩ : syracuseStep 3946661 = 739999) (by norm_num)
theorem B1972417 : Blo 1752577 1972417 := bbase (se 2 (by rfl) ⟨739656, by rfl⟩ : syracuseStep 1972417 = 1479313) (by norm_num)
theorem B2218205 : Blo 1752577 2218205 := bbase (se 3 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 2218205 = 831827) (by norm_num)
theorem B1972453 : Blo 1752577 1972453 := bbase (se 4 (by rfl) ⟨184917, by rfl⟩ : syracuseStep 1972453 = 369835) (by norm_num)
theorem B4438253 : Blo 1752577 4438253 := bbase (se 3 (by rfl) ⟨832172, by rfl⟩ : syracuseStep 4438253 = 1664345) (by norm_num)
theorem B3946733 : Blo 1752577 3946733 := bbase (se 3 (by rfl) ⟨740012, by rfl⟩ : syracuseStep 3946733 = 1480025) (by norm_num)
theorem B2496757 : Blo 1752577 2496757 := bbase (se 5 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 2496757 = 234071) (by norm_num)
theorem B1972489 : Blo 1752577 1972489 := bbase (se 2 (by rfl) ⟨739683, by rfl⟩ : syracuseStep 1972489 = 1479367) (by norm_num)
theorem B3160333 : Blo 1752577 3160333 := bbase (se 3 (by rfl) ⟨592562, by rfl⟩ : syracuseStep 3160333 = 1185125) (by norm_num)
theorem B11229461 : Blo 1752577 11229461 := bbase (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) (by norm_num)
theorem B2218261 : Blo 1752577 2218261 := bbase (se 6 (by rfl) ⟨51990, by rfl⟩ : syracuseStep 2218261 = 103981) (by norm_num)
theorem B5921045 : Blo 1752577 5921045 := bbase (se 6 (by rfl) ⟨138774, by rfl⟩ : syracuseStep 5921045 = 277549) (by norm_num)
theorem B1972525 : Blo 1752577 1972525 := bbase (se 3 (by rfl) ⟨369848, by rfl⟩ : syracuseStep 1972525 = 739697) (by norm_num)
theorem B3946805 : Blo 1752577 3946805 := bbase (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) (by norm_num)
theorem B1972561 : Blo 1752577 1972561 := bbase (se 2 (by rfl) ⟨739710, by rfl⟩ : syracuseStep 1972561 = 1479421) (by norm_num)
theorem B2218357 : Blo 1752577 2218357 := bbase (se 5 (by rfl) ⟨103985, by rfl⟩ : syracuseStep 2218357 = 207971) (by norm_num)
theorem B1972597 : Blo 1752577 1972597 := bbase (se 5 (by rfl) ⟨92465, by rfl⟩ : syracuseStep 1972597 = 184931) (by norm_num)
theorem B3946877 : Blo 1752577 3946877 := bbase (se 3 (by rfl) ⟨740039, by rfl⟩ : syracuseStep 3946877 = 1480079) (by norm_num)
theorem B1898893 : Blo 1752577 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B1972633 : Blo 1752577 1972633 := bbase (se 2 (by rfl) ⟨739737, by rfl⟩ : syracuseStep 1972633 = 1479475) (by norm_num)
theorem B3160477 : Blo 1752577 3160477 := bbase (se 3 (by rfl) ⟨592589, by rfl⟩ : syracuseStep 3160477 = 1185179) (by norm_num)
theorem B1972669 : Blo 1752577 1972669 := bbase (se 3 (by rfl) ⟨369875, by rfl⟩ : syracuseStep 1972669 = 739751) (by norm_num)
theorem B3946949 : Blo 1752577 3946949 := bbase (se 4 (by rfl) ⟨370026, by rfl⟩ : syracuseStep 3946949 = 740053) (by norm_num)
theorem B1972705 : Blo 1752577 1972705 := bbase (se 2 (by rfl) ⟨739764, by rfl⟩ : syracuseStep 1972705 = 1479529) (by norm_num)
theorem B5061125 : Blo 1752577 5061125 := bbase (se 4 (by rfl) ⟨474480, by rfl⟩ : syracuseStep 5061125 = 948961) (by norm_num)
theorem B1972741 : Blo 1752577 1972741 := bbase (se 4 (by rfl) ⟨184944, by rfl⟩ : syracuseStep 1972741 = 369889) (by norm_num)
theorem B3947021 : Blo 1752577 3947021 := bbase (se 3 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 3947021 = 1480133) (by norm_num)
theorem B33700373 : Blo 1752577 33700373 := bbase (se 6 (by rfl) ⟨789852, by rfl⟩ : syracuseStep 33700373 = 1579705) (by norm_num)
theorem B2218529 : Blo 1752577 2218529 := bbase (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) (by norm_num)
theorem B1972777 : Blo 1752577 1972777 := bbase (se 2 (by rfl) ⟨739791, by rfl⟩ : syracuseStep 1972777 = 1479583) (by norm_num)
theorem B3160637 : Blo 1752577 3160637 := bbase (se 3 (by rfl) ⟨592619, by rfl⟩ : syracuseStep 3160637 = 1185239) (by norm_num)
theorem B4438597 : Blo 1752577 4438597 := bbase (se 4 (by rfl) ⟨416118, by rfl⟩ : syracuseStep 4438597 = 832237) (by norm_num)
theorem B1972813 : Blo 1752577 1972813 := bbase (se 3 (by rfl) ⟨369902, by rfl⟩ : syracuseStep 1972813 = 739805) (by norm_num)
theorem B3947093 : Blo 1752577 3947093 := bbase (se 8 (by rfl) ⟨23127, by rfl⟩ : syracuseStep 3947093 = 46255) (by norm_num)
theorem B2218585 : Blo 1752577 2218585 := bbase (se 2 (by rfl) ⟨831969, by rfl⟩ : syracuseStep 2218585 = 1663939) (by norm_num)
theorem B4741733 : Blo 1752577 4741733 := bbase (se 4 (by rfl) ⟨444537, by rfl⟩ : syracuseStep 4741733 = 889075) (by norm_num)
theorem B1972849 : Blo 1752577 1972849 := bbase (se 2 (by rfl) ⟨739818, by rfl⟩ : syracuseStep 1972849 = 1479637) (by norm_num)
theorem B4995701 : Blo 1752577 4995701 := bbase (se 5 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 4995701 = 468347) (by norm_num)
theorem B1972885 : Blo 1752577 1972885 := bbase (se 6 (by rfl) ⟨46239, by rfl⟩ : syracuseStep 1972885 = 92479) (by norm_num)
theorem B3947165 : Blo 1752577 3947165 := bbase (se 3 (by rfl) ⟨740093, by rfl⟩ : syracuseStep 3947165 = 1480187) (by norm_num)
theorem B1899173 : Blo 1752577 1899173 := bbase (se 4 (by rfl) ⟨178047, by rfl⟩ : syracuseStep 1899173 = 356095) (by norm_num)
theorem B4438709 : Blo 1752577 4438709 := bbase (se 5 (by rfl) ⟨208064, by rfl⟩ : syracuseStep 4438709 = 416129) (by norm_num)
theorem B2218681 : Blo 1752577 2218681 := bbase (se 2 (by rfl) ⟨832005, by rfl⟩ : syracuseStep 2218681 = 1664011) (by norm_num)
theorem B1972921 : Blo 1752577 1972921 := bbase (se 2 (by rfl) ⟨739845, by rfl⟩ : syracuseStep 1972921 = 1479691) (by norm_num)
theorem B5921477 : Blo 1752577 5921477 := bbase (se 4 (by rfl) ⟨555138, by rfl⟩ : syracuseStep 5921477 = 1110277) (by norm_num)
theorem B1972957 : Blo 1752577 1972957 := bbase (se 3 (by rfl) ⟨369929, by rfl⟩ : syracuseStep 1972957 = 739859) (by norm_num)
theorem B3947237 : Blo 1752577 3947237 := bbase (se 4 (by rfl) ⟨370053, by rfl⟩ : syracuseStep 3947237 = 740107) (by norm_num)
theorem B5331701 : Blo 1752577 5331701 := bbase (se 5 (by rfl) ⟨249923, by rfl⟩ : syracuseStep 5331701 = 499847) (by norm_num)
theorem B1972993 : Blo 1752577 1972993 := bbase (se 2 (by rfl) ⟨739872, by rfl⟩ : syracuseStep 1972993 = 1479745) (by norm_num)
theorem B1973029 : Blo 1752577 1973029 := bbase (se 4 (by rfl) ⟨184971, by rfl⟩ : syracuseStep 1973029 = 369943) (by norm_num)
theorem B3947309 : Blo 1752577 3947309 := bbase (se 3 (by rfl) ⟨740120, by rfl⟩ : syracuseStep 3947309 = 1480241) (by norm_num)
theorem B2497349 : Blo 1752577 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B1973065 : Blo 1752577 1973065 := bbase (se 2 (by rfl) ⟨739899, by rfl⟩ : syracuseStep 1973065 = 1479799) (by norm_num)
theorem B2218853 : Blo 1752577 2218853 := bbase (se 4 (by rfl) ⟨208017, by rfl⟩ : syracuseStep 2218853 = 416035) (by norm_num)
theorem B2808685 : Blo 1752577 2808685 := bbase (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) (by norm_num)
theorem B1973101 : Blo 1752577 1973101 := bbase (se 3 (by rfl) ⟨369956, by rfl⟩ : syracuseStep 1973101 = 739913) (by norm_num)
theorem B4438901 : Blo 1752577 4438901 := bbase (se 5 (by rfl) ⟨208073, by rfl⟩ : syracuseStep 4438901 = 416147) (by norm_num)
theorem B3947381 : Blo 1752577 3947381 := bbase (se 5 (by rfl) ⟨185033, by rfl⟩ : syracuseStep 3947381 = 370067) (by norm_num)
theorem B1973137 : Blo 1752577 1973137 := bbase (se 2 (by rfl) ⟨739926, by rfl⟩ : syracuseStep 1973137 = 1479853) (by norm_num)
theorem B2497429 : Blo 1752577 2497429 := bbase (se 6 (by rfl) ⟨58533, by rfl⟩ : syracuseStep 2497429 = 117067) (by norm_num)
theorem B2218909 : Blo 1752577 2218909 := bbase (se 3 (by rfl) ⟨416045, by rfl⟩ : syracuseStep 2218909 = 832091) (by norm_num)
theorem B1923997 : Blo 1752577 1923997 := bbase (se 3 (by rfl) ⟨360749, by rfl⟩ : syracuseStep 1923997 = 721499) (by norm_num)
theorem B7592885 : Blo 1752577 7592885 := bbase (se 5 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 7592885 = 711833) (by norm_num)
theorem B1973173 : Blo 1752577 1973173 := bbase (se 5 (by rfl) ⟨92492, by rfl⟩ : syracuseStep 1973173 = 184985) (by norm_num)
theorem B3947453 : Blo 1752577 3947453 := bbase (se 3 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 3947453 = 1480295) (by norm_num)
theorem B1973209 : Blo 1752577 1973209 := bbase (se 2 (by rfl) ⟨739953, by rfl⟩ : syracuseStep 1973209 = 1479907) (by norm_num)
theorem B2219005 : Blo 1752577 2219005 := bbase (se 3 (by rfl) ⟨416063, by rfl⟩ : syracuseStep 2219005 = 832127) (by norm_num)
theorem B1973245 : Blo 1752577 1973245 := bbase (se 3 (by rfl) ⟨369983, by rfl⟩ : syracuseStep 1973245 = 739967) (by norm_num)
theorem B3947525 : Blo 1752577 3947525 := bbase (se 4 (by rfl) ⟨370080, by rfl⟩ : syracuseStep 3947525 = 740161) (by norm_num)
theorem B2497549 : Blo 1752577 2497549 := bbase (se 3 (by rfl) ⟨468290, by rfl⟩ : syracuseStep 2497549 = 936581) (by norm_num)
theorem B1973281 : Blo 1752577 1973281 := bbase (se 2 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 1973281 = 1479961) (by norm_num)
theorem B1973317 : Blo 1752577 1973317 := bbase (se 4 (by rfl) ⟨184998, by rfl⟩ : syracuseStep 1973317 = 369997) (by norm_num)
theorem B3947597 : Blo 1752577 3947597 := bbase (se 3 (by rfl) ⟨740174, by rfl⟩ : syracuseStep 3947597 = 1480349) (by norm_num)
theorem B15989845 : Blo 1752577 15989845 := bbase (se 8 (by rfl) ⟨93690, by rfl⟩ : syracuseStep 15989845 = 187381) (by norm_num)
theorem B1973353 : Blo 1752577 1973353 := bbase (se 2 (by rfl) ⟨740007, by rfl⟩ : syracuseStep 1973353 = 1480015) (by norm_num)
theorem B3849325 : Blo 1752577 3849325 := bbase (se 3 (by rfl) ⟨721748, by rfl⟩ : syracuseStep 3849325 = 1443497) (by norm_num)
theorem B2497645 : Blo 1752577 2497645 := bbase (se 3 (by rfl) ⟨468308, by rfl⟩ : syracuseStep 2497645 = 936617) (by norm_num)
theorem B1973389 : Blo 1752577 1973389 := bbase (se 3 (by rfl) ⟨370010, by rfl⟩ : syracuseStep 1973389 = 740021) (by norm_num)
theorem B3947669 : Blo 1752577 3947669 := bbase (se 6 (by rfl) ⟨92523, by rfl⟩ : syracuseStep 3947669 = 185047) (by norm_num)
theorem B2219177 : Blo 1752577 2219177 := bbase (se 2 (by rfl) ⟨832191, by rfl⟩ : syracuseStep 2219177 = 1664383) (by norm_num)
theorem B1973425 : Blo 1752577 1973425 := bbase (se 2 (by rfl) ⟨740034, by rfl⟩ : syracuseStep 1973425 = 1480069) (by norm_num)
theorem B4439245 : Blo 1752577 4439245 := bbase (se 3 (by rfl) ⟨832358, by rfl⟩ : syracuseStep 4439245 = 1664717) (by norm_num)
theorem B1973461 : Blo 1752577 1973461 := bbase (se 7 (by rfl) ⟨23126, by rfl⟩ : syracuseStep 1973461 = 46253) (by norm_num)
theorem B3554525 : Blo 1752577 3554525 := bbase (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) (by norm_num)
theorem B3947741 : Blo 1752577 3947741 := bbase (se 3 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 3947741 = 1480403) (by norm_num)
theorem B2219233 : Blo 1752577 2219233 := bbase (se 2 (by rfl) ⟨832212, by rfl⟩ : syracuseStep 2219233 = 1664425) (by norm_num)
theorem B1973497 : Blo 1752577 1973497 := bbase (se 2 (by rfl) ⟨740061, by rfl⟩ : syracuseStep 1973497 = 1480123) (by norm_num)
theorem B2628869 : Blo 1752577 2628869 := bbase (se 4 (by rfl) ⟨246456, by rfl⟩ : syracuseStep 2628869 = 492913) (by norm_num)
theorem B8879381 : Blo 1752577 8879381 := bbase (se 6 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 8879381 = 416221) (by norm_num)
theorem B2628893 : Blo 1752577 2628893 := bbase (se 3 (by rfl) ⟨492917, by rfl⟩ : syracuseStep 2628893 = 985835) (by norm_num)
theorem B1973533 : Blo 1752577 1973533 := bbase (se 3 (by rfl) ⟨370037, by rfl⟩ : syracuseStep 1973533 = 740075) (by norm_num)
theorem B2628917 : Blo 1752577 2628917 := bbase (se 5 (by rfl) ⟨123230, by rfl⟩ : syracuseStep 2628917 = 246461) (by norm_num)
theorem B4439357 : Blo 1752577 4439357 := bbase (se 3 (by rfl) ⟨832379, by rfl⟩ : syracuseStep 4439357 = 1664759) (by norm_num)
theorem B2219329 : Blo 1752577 2219329 := bbase (se 2 (by rfl) ⟨832248, by rfl⟩ : syracuseStep 2219329 = 1664497) (by norm_num)
theorem B1973569 : Blo 1752577 1973569 := bbase (se 2 (by rfl) ⟨740088, by rfl⟩ : syracuseStep 1973569 = 1480177) (by norm_num)
theorem B2628941 : Blo 1752577 2628941 := bbase (se 3 (by rfl) ⟨492926, by rfl⟩ : syracuseStep 2628941 = 985853) (by norm_num)
theorem B2628965 : Blo 1752577 2628965 := bbase (se 4 (by rfl) ⟨246465, by rfl⟩ : syracuseStep 2628965 = 492931) (by norm_num)
theorem B1973605 : Blo 1752577 1973605 := bbase (se 4 (by rfl) ⟨185025, by rfl⟩ : syracuseStep 1973605 = 370051) (by norm_num)
theorem B2628989 : Blo 1752577 2628989 := bbase (se 3 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 2628989 = 985871) (by norm_num)
theorem B1973641 : Blo 1752577 1973641 := bbase (se 2 (by rfl) ⟨740115, by rfl⟩ : syracuseStep 1973641 = 1480231) (by norm_num)
theorem B2629013 : Blo 1752577 2629013 := bbase (se 6 (by rfl) ⟨61617, by rfl⟩ : syracuseStep 2629013 = 123235) (by norm_num)
theorem B29957525 : Blo 1752577 29957525 := bbase (se 6 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 29957525 = 1404259) (by norm_num)
theorem B2629037 : Blo 1752577 2629037 := bbase (se 3 (by rfl) ⟨492944, by rfl⟩ : syracuseStep 2629037 = 985889) (by norm_num)
theorem B1973677 : Blo 1752577 1973677 := bbase (se 3 (by rfl) ⟨370064, by rfl⟩ : syracuseStep 1973677 = 740129) (by norm_num)
theorem B2629061 : Blo 1752577 2629061 := bbase (se 4 (by rfl) ⟨246474, by rfl⟩ : syracuseStep 2629061 = 492949) (by norm_num)
theorem B1973713 : Blo 1752577 1973713 := bbase (se 2 (by rfl) ⟨740142, by rfl⟩ : syracuseStep 1973713 = 1480285) (by norm_num)
theorem B2629085 : Blo 1752577 2629085 := bbase (se 3 (by rfl) ⟨492953, by rfl⟩ : syracuseStep 2629085 = 985907) (by norm_num)
theorem B2219501 : Blo 1752577 2219501 := bbase (se 3 (by rfl) ⟨416156, by rfl⟩ : syracuseStep 2219501 = 832313) (by norm_num)
theorem B2629109 : Blo 1752577 2629109 := bbase (se 5 (by rfl) ⟨123239, by rfl⟩ : syracuseStep 2629109 = 246479) (by norm_num)
theorem B2809333 : Blo 1752577 2809333 := bbase (se 5 (by rfl) ⟨131687, by rfl⟩ : syracuseStep 2809333 = 263375) (by norm_num)
theorem B1973749 : Blo 1752577 1973749 := bbase (se 5 (by rfl) ⟨92519, by rfl⟩ : syracuseStep 1973749 = 185039) (by norm_num)
theorem B4439549 : Blo 1752577 4439549 := bbase (se 3 (by rfl) ⟨832415, by rfl⟩ : syracuseStep 4439549 = 1664831) (by norm_num)
theorem B3751429 : Blo 1752577 3751429 := bbase (se 4 (by rfl) ⟨351696, by rfl⟩ : syracuseStep 3751429 = 703393) (by norm_num)
theorem B2629133 : Blo 1752577 2629133 := bbase (se 3 (by rfl) ⟨492962, by rfl⟩ : syracuseStep 2629133 = 985925) (by norm_num)
theorem B1973785 : Blo 1752577 1973785 := bbase (se 2 (by rfl) ⟨740169, by rfl⟩ : syracuseStep 1973785 = 1480339) (by norm_num)
theorem B2629157 : Blo 1752577 2629157 := bbase (se 4 (by rfl) ⟨246483, by rfl⟩ : syracuseStep 2629157 = 492967) (by norm_num)
theorem B2219557 : Blo 1752577 2219557 := bbase (se 4 (by rfl) ⟨208083, by rfl⟩ : syracuseStep 2219557 = 416167) (by norm_num)
theorem B8429093 : Blo 1752577 8429093 := bbase (se 4 (by rfl) ⟨790227, by rfl⟩ : syracuseStep 8429093 = 1580455) (by norm_num)
theorem B2629181 : Blo 1752577 2629181 := bbase (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) (by norm_num)
theorem B1973821 : Blo 1752577 1973821 := bbase (se 3 (by rfl) ⟨370091, by rfl⟩ : syracuseStep 1973821 = 740183) (by norm_num)
theorem B2629205 : Blo 1752577 2629205 := bbase (se 8 (by rfl) ⟨15405, by rfl⟩ : syracuseStep 2629205 = 30811) (by norm_num)
theorem B2498141 : Blo 1752577 2498141 := bbase (se 3 (by rfl) ⟨468401, by rfl⟩ : syracuseStep 2498141 = 936803) (by norm_num)
theorem B1973857 : Blo 1752577 1973857 := bbase (se 2 (by rfl) ⟨740196, by rfl⟩ : syracuseStep 1973857 = 1480393) (by norm_num)
theorem B2629229 : Blo 1752577 2629229 := bbase (se 3 (by rfl) ⟨492980, by rfl⟩ : syracuseStep 2629229 = 985961) (by norm_num)
theorem B7487093 : Blo 1752577 7487093 := bbase (se 5 (by rfl) ⟨350957, by rfl⟩ : syracuseStep 7487093 = 701915) (by norm_num)
theorem B2629253 : Blo 1752577 2629253 := bbase (se 4 (by rfl) ⟨246492, by rfl⟩ : syracuseStep 2629253 = 492985) (by norm_num)
theorem B2219653 : Blo 1752577 2219653 := bbase (se 4 (by rfl) ⟨208092, by rfl⟩ : syracuseStep 2219653 = 416185) (by norm_num)
theorem B1973893 : Blo 1752577 1973893 := bbase (se 4 (by rfl) ⟨185052, by rfl⟩ : syracuseStep 1973893 = 370105) (by norm_num)
theorem B1801873 : Blo 1752577 1801873 := bbase (se 2 (by rfl) ⟨675702, by rfl⟩ : syracuseStep 1801873 = 1351405) (by norm_num)
theorem B2629277 : Blo 1752577 2629277 := bbase (se 3 (by rfl) ⟨492989, by rfl⟩ : syracuseStep 2629277 = 985979) (by norm_num)
theorem B2629301 : Blo 1752577 2629301 := bbase (se 5 (by rfl) ⟨123248, by rfl⟩ : syracuseStep 2629301 = 246497) (by norm_num)
theorem B6659765 : Blo 1752577 6659765 := bbase (se 5 (by rfl) ⟨312176, by rfl⟩ : syracuseStep 6659765 = 624353) (by norm_num)
theorem B2629325 : Blo 1752577 2629325 := bbase (se 3 (by rfl) ⟨492998, by rfl⟩ : syracuseStep 2629325 = 985997) (by norm_num)
theorem B56884949 : Blo 1752577 56884949 := bbase (se 7 (by rfl) ⟨666620, by rfl⟩ : syracuseStep 56884949 = 1333241) (by norm_num)
theorem B2629349 : Blo 1752577 2629349 := bbase (se 4 (by rfl) ⟨246501, by rfl⟩ : syracuseStep 2629349 = 493003) (by norm_num)
theorem B2629373 : Blo 1752577 2629373 := bbase (se 3 (by rfl) ⟨493007, by rfl⟩ : syracuseStep 2629373 = 986015) (by norm_num)
theorem B2629397 : Blo 1752577 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B2629421 : Blo 1752577 2629421 := bbase (se 3 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 2629421 = 986033) (by norm_num)
theorem B2219825 : Blo 1752577 2219825 := bbase (se 2 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 2219825 = 1664869) (by norm_num)
theorem B2629445 : Blo 1752577 2629445 := bbase (se 4 (by rfl) ⟨246510, by rfl⟩ : syracuseStep 2629445 = 493021) (by norm_num)
theorem B4439893 : Blo 1752577 4439893 := bbase (se 9 (by rfl) ⟨13007, by rfl⟩ : syracuseStep 4439893 = 26015) (by norm_num)
theorem B2629469 : Blo 1752577 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B2219881 : Blo 1752577 2219881 := bbase (se 2 (by rfl) ⟨832455, by rfl⟩ : syracuseStep 2219881 = 1664911) (by norm_num)
theorem B2629493 : Blo 1752577 2629493 := bbase (se 5 (by rfl) ⟨123257, by rfl⟩ : syracuseStep 2629493 = 246515) (by norm_num)
theorem B2703221 : Blo 1752577 2703221 := bbase (se 5 (by rfl) ⟨126713, by rfl⟩ : syracuseStep 2703221 = 253427) (by norm_num)
theorem B2629517 : Blo 1752577 2629517 := bbase (se 3 (by rfl) ⟨493034, by rfl⟩ : syracuseStep 2629517 = 986069) (by norm_num)
theorem B2629541 : Blo 1752577 2629541 := bbase (se 4 (by rfl) ⟨246519, by rfl⟩ : syracuseStep 2629541 = 493039) (by norm_num)
theorem B2629565 : Blo 1752577 2629565 := bbase (se 3 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 2629565 = 986087) (by norm_num)
theorem B4440005 : Blo 1752577 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B2219977 : Blo 1752577 2219977 := bbase (se 2 (by rfl) ⟨832491, by rfl⟩ : syracuseStep 2219977 = 1664983) (by norm_num)
theorem B2629589 : Blo 1752577 2629589 := bbase (se 7 (by rfl) ⟨30815, by rfl⟩ : syracuseStep 2629589 = 61631) (by norm_num)
theorem B6660053 : Blo 1752577 6660053 := bbase (se 7 (by rfl) ⟨78047, by rfl⟩ : syracuseStep 6660053 = 156095) (by norm_num)
theorem B2564077 : Blo 1752577 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B2629613 : Blo 1752577 2629613 := bbase (se 3 (by rfl) ⟨493052, by rfl⟩ : syracuseStep 2629613 = 986105) (by norm_num)
theorem B1753091 : Blo 1752577 1753091 := bstep (se 1 (by rfl) ⟨1314818, by rfl⟩ : syracuseStep 1753091 = 2629637) B2629637
theorem B2629649 : Blo 1752577 2629649 := bstep (se 2 (by rfl) ⟨986118, by rfl⟩ : syracuseStep 2629649 = 1972237) B1972237
theorem B1753107 : Blo 1752577 1753107 := bstep (se 1 (by rfl) ⟨1314830, by rfl⟩ : syracuseStep 1753107 = 2629661) B2629661
theorem B2629667 : Blo 1752577 2629667 := bstep (se 1 (by rfl) ⟨1972250, by rfl⟩ : syracuseStep 2629667 = 3944501) B3944501
theorem B1753123 : Blo 1752577 1753123 := bstep (se 1 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 1753123 = 2629685) B2629685
theorem B1753139 : Blo 1752577 1753139 := bstep (se 1 (by rfl) ⟨1314854, by rfl⟩ : syracuseStep 1753139 = 2629709) B2629709
theorem B2629697 : Blo 1752577 2629697 := bstep (se 2 (by rfl) ⟨986136, by rfl⟩ : syracuseStep 2629697 = 1972273) B1972273
theorem B1753155 : Blo 1752577 1753155 := bstep (se 1 (by rfl) ⟨1314866, by rfl⟩ : syracuseStep 1753155 = 2629733) B2629733
theorem B5619793 : Blo 1752577 5619793 := bstep (se 2 (by rfl) ⟨2107422, by rfl⟩ : syracuseStep 5619793 = 4214845) B4214845
theorem B2629715 : Blo 1752577 2629715 := bstep (se 1 (by rfl) ⟨1972286, by rfl⟩ : syracuseStep 2629715 = 3944573) B3944573
theorem B1753171 : Blo 1752577 1753171 := bstep (se 1 (by rfl) ⟨1314878, by rfl⟩ : syracuseStep 1753171 = 2629757) B2629757
theorem B1753187 : Blo 1752577 1753187 := bstep (se 1 (by rfl) ⟨1314890, by rfl⟩ : syracuseStep 1753187 = 2629781) B2629781
theorem B2629745 : Blo 1752577 2629745 := bstep (se 2 (by rfl) ⟨986154, by rfl⟩ : syracuseStep 2629745 = 1972309) B1972309
theorem B1753203 : Blo 1752577 1753203 := bstep (se 1 (by rfl) ⟨1314902, by rfl⟩ : syracuseStep 1753203 = 2629805) B2629805
theorem B2629763 : Blo 1752577 2629763 := bstep (se 1 (by rfl) ⟨1972322, by rfl⟩ : syracuseStep 2629763 = 3944645) B3944645
theorem B1753219 : Blo 1752577 1753219 := bstep (se 1 (by rfl) ⟨1314914, by rfl⟩ : syracuseStep 1753219 = 2629829) B2629829
theorem B1753235 : Blo 1752577 1753235 := bstep (se 1 (by rfl) ⟨1314926, by rfl⟩ : syracuseStep 1753235 = 2629853) B2629853
theorem B2629793 : Blo 1752577 2629793 := bstep (se 2 (by rfl) ⟨986172, by rfl⟩ : syracuseStep 2629793 = 1972345) B1972345
theorem B1753251 : Blo 1752577 1753251 := bstep (se 1 (by rfl) ⟨1314938, by rfl⟩ : syracuseStep 1753251 = 2629877) B2629877
theorem B2629811 : Blo 1752577 2629811 := bstep (se 1 (by rfl) ⟨1972358, by rfl⟩ : syracuseStep 2629811 = 3944717) B3944717
theorem B1753267 : Blo 1752577 1753267 := bstep (se 1 (by rfl) ⟨1314950, by rfl⟩ : syracuseStep 1753267 = 2629901) B2629901
theorem B3743939 : Blo 1752577 3743939 := bstep (se 1 (by rfl) ⟨2807954, by rfl⟩ : syracuseStep 3743939 = 5615909) B5615909
theorem B1753283 : Blo 1752577 1753283 := bstep (se 1 (by rfl) ⟨1314962, by rfl⟩ : syracuseStep 1753283 = 2629925) B2629925
theorem B2629841 : Blo 1752577 2629841 := bstep (se 2 (by rfl) ⟨986190, by rfl⟩ : syracuseStep 2629841 = 1972381) B1972381
theorem B1753299 : Blo 1752577 1753299 := bstep (se 1 (by rfl) ⟨1314974, by rfl⟩ : syracuseStep 1753299 = 2629949) B2629949
theorem B2957539 : Blo 1752577 2957539 := bstep (se 1 (by rfl) ⟨2218154, by rfl⟩ : syracuseStep 2957539 = 4436309) B4436309
theorem B2629859 : Blo 1752577 2629859 := bstep (se 1 (by rfl) ⟨1972394, by rfl⟩ : syracuseStep 2629859 = 3944789) B3944789
theorem B1753315 : Blo 1752577 1753315 := bstep (se 1 (by rfl) ⟨1314986, by rfl⟩ : syracuseStep 1753315 = 2629973) B2629973
theorem B3555569 : Blo 1752577 3555569 := bstep (se 2 (by rfl) ⟨1333338, by rfl⟩ : syracuseStep 3555569 = 2666677) B2666677
theorem B1753331 : Blo 1752577 1753331 := bstep (se 1 (by rfl) ⟨1314998, by rfl⟩ : syracuseStep 1753331 = 2629997) B2629997
theorem B2629889 : Blo 1752577 2629889 := bstep (se 2 (by rfl) ⟨986208, by rfl⟩ : syracuseStep 2629889 = 1972417) B1972417
theorem B1753347 : Blo 1752577 1753347 := bstep (se 1 (by rfl) ⟨1315010, by rfl⟩ : syracuseStep 1753347 = 2630021) B2630021
theorem B2629907 : Blo 1752577 2629907 := bstep (se 1 (by rfl) ⟨1972430, by rfl⟩ : syracuseStep 2629907 = 3944861) B3944861
theorem B1753363 : Blo 1752577 1753363 := bstep (se 1 (by rfl) ⟨1315022, by rfl⟩ : syracuseStep 1753363 = 2630045) B2630045
theorem B1753379 : Blo 1752577 1753379 := bstep (se 1 (by rfl) ⟨1315034, by rfl⟩ : syracuseStep 1753379 = 2630069) B2630069
theorem B2629937 : Blo 1752577 2629937 := bstep (se 2 (by rfl) ⟨986226, by rfl⟩ : syracuseStep 2629937 = 1972453) B1972453
theorem B1753395 : Blo 1752577 1753395 := bstep (se 1 (by rfl) ⟨1315046, by rfl⟩ : syracuseStep 1753395 = 2630093) B2630093
theorem B2629955 : Blo 1752577 2629955 := bstep (se 1 (by rfl) ⟨1972466, by rfl⟩ : syracuseStep 2629955 = 3944933) B3944933
theorem B1753411 : Blo 1752577 1753411 := bstep (se 1 (by rfl) ⟨1315058, by rfl⟩ : syracuseStep 1753411 = 2630117) B2630117
theorem B1753427 : Blo 1752577 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B2629985 : Blo 1752577 2629985 := bstep (se 2 (by rfl) ⟨986244, by rfl⟩ : syracuseStep 2629985 = 1972489) B1972489
theorem B1753443 : Blo 1752577 1753443 := bstep (se 1 (by rfl) ⟨1315082, by rfl⟩ : syracuseStep 1753443 = 2630165) B2630165
theorem B2957681 : Blo 1752577 2957681 := bstep (se 2 (by rfl) ⟨1109130, by rfl⟩ : syracuseStep 2957681 = 2218261) B2218261
theorem B2630003 : Blo 1752577 2630003 := bstep (se 1 (by rfl) ⟨1972502, by rfl⟩ : syracuseStep 2630003 = 3945005) B3945005
theorem B1753459 : Blo 1752577 1753459 := bstep (se 1 (by rfl) ⟨1315094, by rfl⟩ : syracuseStep 1753459 = 2630189) B2630189
theorem B1753475 : Blo 1752577 1753475 := bstep (se 1 (by rfl) ⟨1315106, by rfl⟩ : syracuseStep 1753475 = 2630213) B2630213
theorem B11239813 : Blo 1752577 11239813 := bstep (se 4 (by rfl) ⟨1053732, by rfl⟩ : syracuseStep 11239813 = 2107465) B2107465
theorem B2630033 : Blo 1752577 2630033 := bstep (se 2 (by rfl) ⟨986262, by rfl⟩ : syracuseStep 2630033 = 1972525) B1972525
theorem B1753491 : Blo 1752577 1753491 := bstep (se 1 (by rfl) ⟨1315118, by rfl⟩ : syracuseStep 1753491 = 2630237) B2630237
theorem B2630051 : Blo 1752577 2630051 := bstep (se 1 (by rfl) ⟨1972538, by rfl⟩ : syracuseStep 2630051 = 3945077) B3945077
theorem B1753507 : Blo 1752577 1753507 := bstep (se 1 (by rfl) ⟨1315130, by rfl⟩ : syracuseStep 1753507 = 2630261) B2630261
theorem B1753523 : Blo 1752577 1753523 := bstep (se 1 (by rfl) ⟨1315142, by rfl⟩ : syracuseStep 1753523 = 2630285) B2630285
theorem B2630081 : Blo 1752577 2630081 := bstep (se 2 (by rfl) ⟨986280, by rfl⟩ : syracuseStep 2630081 = 1972561) B1972561
theorem B1753539 : Blo 1752577 1753539 := bstep (se 1 (by rfl) ⟨1315154, by rfl⟩ : syracuseStep 1753539 = 2630309) B2630309
theorem B3039697 : Blo 1752577 3039697 := bstep (se 2 (by rfl) ⟨1139886, by rfl⟩ : syracuseStep 3039697 = 2279773) B2279773
theorem B2630099 : Blo 1752577 2630099 := bstep (se 1 (by rfl) ⟨1972574, by rfl⟩ : syracuseStep 2630099 = 3945149) B3945149
theorem B1753555 : Blo 1752577 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B1753571 : Blo 1752577 1753571 := bstep (se 1 (by rfl) ⟨1315178, by rfl⟩ : syracuseStep 1753571 = 2630357) B2630357
theorem B2957809 : Blo 1752577 2957809 := bstep (se 2 (by rfl) ⟨1109178, by rfl⟩ : syracuseStep 2957809 = 2218357) B2218357
theorem B2630129 : Blo 1752577 2630129 := bstep (se 2 (by rfl) ⟨986298, by rfl⟩ : syracuseStep 2630129 = 1972597) B1972597
theorem B1753587 : Blo 1752577 1753587 := bstep (se 1 (by rfl) ⟨1315190, by rfl⟩ : syracuseStep 1753587 = 2630381) B2630381
theorem B2630147 : Blo 1752577 2630147 := bstep (se 1 (by rfl) ⟨1972610, by rfl⟩ : syracuseStep 2630147 = 3945221) B3945221
theorem B1753603 : Blo 1752577 1753603 := bstep (se 1 (by rfl) ⟨1315202, by rfl⟩ : syracuseStep 1753603 = 2630405) B2630405
theorem B5620241 : Blo 1752577 5620241 := bstep (se 2 (by rfl) ⟨2107590, by rfl⟩ : syracuseStep 5620241 = 4215181) B4215181
theorem B2957843 : Blo 1752577 2957843 := bstep (se 1 (by rfl) ⟨2218382, by rfl⟩ : syracuseStep 2957843 = 4436765) B4436765
theorem B1753619 : Blo 1752577 1753619 := bstep (se 1 (by rfl) ⟨1315214, by rfl⟩ : syracuseStep 1753619 = 2630429) B2630429
theorem B2630177 : Blo 1752577 2630177 := bstep (se 2 (by rfl) ⟨986316, by rfl⟩ : syracuseStep 2630177 = 1972633) B1972633
theorem B1753635 : Blo 1752577 1753635 := bstep (se 1 (by rfl) ⟨1315226, by rfl⟩ : syracuseStep 1753635 = 2630453) B2630453
theorem B2630195 : Blo 1752577 2630195 := bstep (se 1 (by rfl) ⟨1972646, by rfl⟩ : syracuseStep 2630195 = 3945293) B3945293
theorem B1753651 : Blo 1752577 1753651 := bstep (se 1 (by rfl) ⟨1315238, by rfl⟩ : syracuseStep 1753651 = 2630477) B2630477
theorem B1753667 : Blo 1752577 1753667 := bstep (se 1 (by rfl) ⟨1315250, by rfl⟩ : syracuseStep 1753667 = 2630501) B2630501
theorem B10666565 : Blo 1752577 10666565 := bstep (se 4 (by rfl) ⟨999990, by rfl⟩ : syracuseStep 10666565 = 1999981) B1999981
theorem B13320773 : Blo 1752577 13320773 := bstep (se 4 (by rfl) ⟨1248822, by rfl⟩ : syracuseStep 13320773 = 2497645) B2497645
theorem B5915213 : Blo 1752577 5915213 := bstep (se 3 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 5915213 = 2218205) B2218205
theorem B2630225 : Blo 1752577 2630225 := bstep (se 2 (by rfl) ⟨986334, by rfl⟩ : syracuseStep 2630225 = 1972669) B1972669
theorem B1753683 : Blo 1752577 1753683 := bstep (se 1 (by rfl) ⟨1315262, by rfl⟩ : syracuseStep 1753683 = 2630525) B2630525
theorem B2630243 : Blo 1752577 2630243 := bstep (se 1 (by rfl) ⟨1972682, by rfl⟩ : syracuseStep 2630243 = 3945365) B3945365
theorem B1753699 : Blo 1752577 1753699 := bstep (se 1 (by rfl) ⟨1315274, by rfl⟩ : syracuseStep 1753699 = 2630549) B2630549
theorem B8422001 : Blo 1752577 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B1753715 : Blo 1752577 1753715 := bstep (se 1 (by rfl) ⟨1315286, by rfl⟩ : syracuseStep 1753715 = 2630573) B2630573
theorem B2630273 : Blo 1752577 2630273 := bstep (se 2 (by rfl) ⟨986352, by rfl⟩ : syracuseStep 2630273 = 1972705) B1972705
theorem B5915267 : Blo 1752577 5915267 := bstep (se 1 (by rfl) ⟨4436450, by rfl⟩ : syracuseStep 5915267 = 8872901) B8872901
theorem B1753731 : Blo 1752577 1753731 := bstep (se 1 (by rfl) ⟨1315298, by rfl⟩ : syracuseStep 1753731 = 2630597) B2630597
theorem B2957971 : Blo 1752577 2957971 := bstep (se 1 (by rfl) ⟨2218478, by rfl⟩ : syracuseStep 2957971 = 4436957) B4436957
theorem B2630291 : Blo 1752577 2630291 := bstep (se 1 (by rfl) ⟨1972718, by rfl⟩ : syracuseStep 2630291 = 3945437) B3945437
theorem B1753747 : Blo 1752577 1753747 := bstep (se 1 (by rfl) ⟨1315310, by rfl⟩ : syracuseStep 1753747 = 2630621) B2630621
theorem B1753763 : Blo 1752577 1753763 := bstep (se 1 (by rfl) ⟨1315322, by rfl⟩ : syracuseStep 1753763 = 2630645) B2630645
theorem B2630321 : Blo 1752577 2630321 := bstep (se 2 (by rfl) ⟨986370, by rfl⟩ : syracuseStep 2630321 = 1972741) B1972741
theorem B1753779 : Blo 1752577 1753779 := bstep (se 1 (by rfl) ⟨1315334, by rfl⟩ : syracuseStep 1753779 = 2630669) B2630669
theorem B2630339 : Blo 1752577 2630339 := bstep (se 1 (by rfl) ⟨1972754, by rfl⟩ : syracuseStep 2630339 = 3945509) B3945509
theorem B1753795 : Blo 1752577 1753795 := bstep (se 1 (by rfl) ⟨1315346, by rfl⟩ : syracuseStep 1753795 = 2630693) B2630693
theorem B1753811 : Blo 1752577 1753811 := bstep (se 1 (by rfl) ⟨1315358, by rfl⟩ : syracuseStep 1753811 = 2630717) B2630717
theorem B2630369 : Blo 1752577 2630369 := bstep (se 2 (by rfl) ⟨986388, by rfl⟩ : syracuseStep 2630369 = 1972777) B1972777
theorem B1753827 : Blo 1752577 1753827 := bstep (se 1 (by rfl) ⟨1315370, by rfl⟩ : syracuseStep 1753827 = 2630741) B2630741
theorem B2630387 : Blo 1752577 2630387 := bstep (se 1 (by rfl) ⟨1972790, by rfl⟩ : syracuseStep 2630387 = 3945581) B3945581
theorem B1753843 : Blo 1752577 1753843 := bstep (se 1 (by rfl) ⟨1315382, by rfl⟩ : syracuseStep 1753843 = 2630765) B2630765
theorem B1753859 : Blo 1752577 1753859 := bstep (se 1 (by rfl) ⟨1315394, by rfl⟩ : syracuseStep 1753859 = 2630789) B2630789
theorem B16851725 : Blo 1752577 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B2630417 : Blo 1752577 2630417 := bstep (se 2 (by rfl) ⟨986406, by rfl⟩ : syracuseStep 2630417 = 1972813) B1972813
theorem B1753875 : Blo 1752577 1753875 := bstep (se 1 (by rfl) ⟨1315406, by rfl⟩ : syracuseStep 1753875 = 2630813) B2630813
theorem B2958113 : Blo 1752577 2958113 := bstep (se 2 (by rfl) ⟨1109292, by rfl⟩ : syracuseStep 2958113 = 2218585) B2218585
theorem B8872739 : Blo 1752577 8872739 := bstep (se 1 (by rfl) ⟨6654554, by rfl⟩ : syracuseStep 8872739 = 13309109) B13309109
theorem B2630435 : Blo 1752577 2630435 := bstep (se 1 (by rfl) ⟨1972826, by rfl⟩ : syracuseStep 2630435 = 3945653) B3945653
theorem B1753891 : Blo 1752577 1753891 := bstep (se 1 (by rfl) ⟨1315418, by rfl⟩ : syracuseStep 1753891 = 2630837) B2630837
theorem B1753907 : Blo 1752577 1753907 := bstep (se 1 (by rfl) ⟨1315430, by rfl⟩ : syracuseStep 1753907 = 2630861) B2630861
theorem B2630465 : Blo 1752577 2630465 := bstep (se 2 (by rfl) ⟨986424, by rfl⟩ : syracuseStep 2630465 = 1972849) B1972849
theorem B1753923 : Blo 1752577 1753923 := bstep (se 1 (by rfl) ⟨1315442, by rfl⟩ : syracuseStep 1753923 = 2630885) B2630885
theorem B3203921 : Blo 1752577 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B2630483 : Blo 1752577 2630483 := bstep (se 1 (by rfl) ⟨1972862, by rfl⟩ : syracuseStep 2630483 = 3945725) B3945725
theorem B1753939 : Blo 1752577 1753939 := bstep (se 1 (by rfl) ⟨1315454, by rfl⟩ : syracuseStep 1753939 = 2630909) B2630909
theorem B307635029 : Blo 1752577 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B1753955 : Blo 1752577 1753955 := bstep (se 1 (by rfl) ⟨1315466, by rfl⟩ : syracuseStep 1753955 = 2630933) B2630933
theorem B2630513 : Blo 1752577 2630513 := bstep (se 2 (by rfl) ⟨986442, by rfl⟩ : syracuseStep 2630513 = 1972885) B1972885
theorem B1753971 : Blo 1752577 1753971 := bstep (se 1 (by rfl) ⟨1315478, by rfl⟩ : syracuseStep 1753971 = 2630957) B2630957
theorem B2630531 : Blo 1752577 2630531 := bstep (se 1 (by rfl) ⟨1972898, by rfl⟩ : syracuseStep 2630531 = 3945797) B3945797
theorem B1753987 : Blo 1752577 1753987 := bstep (se 1 (by rfl) ⟨1315490, by rfl⟩ : syracuseStep 1753987 = 2630981) B2630981
theorem B5915537 : Blo 1752577 5915537 := bstep (se 2 (by rfl) ⟨2218326, by rfl⟩ : syracuseStep 5915537 = 4436653) B4436653
theorem B4440977 : Blo 1752577 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1754003 : Blo 1752577 1754003 := bstep (se 1 (by rfl) ⟨1315502, by rfl⟩ : syracuseStep 1754003 = 2631005) B2631005
theorem B2958241 : Blo 1752577 2958241 := bstep (se 2 (by rfl) ⟨1109340, by rfl⟩ : syracuseStep 2958241 = 2218681) B2218681
theorem B2630561 : Blo 1752577 2630561 := bstep (se 2 (by rfl) ⟨986460, by rfl⟩ : syracuseStep 2630561 = 1972921) B1972921
theorem B1754019 : Blo 1752577 1754019 := bstep (se 1 (by rfl) ⟨1315514, by rfl⟩ : syracuseStep 1754019 = 2631029) B2631029
theorem B2630579 : Blo 1752577 2630579 := bstep (se 1 (by rfl) ⟨1972934, by rfl⟩ : syracuseStep 2630579 = 3945869) B3945869
theorem B1754035 : Blo 1752577 1754035 := bstep (se 1 (by rfl) ⟨1315526, by rfl⟩ : syracuseStep 1754035 = 2631053) B2631053
theorem B2958275 : Blo 1752577 2958275 := bstep (se 1 (by rfl) ⟨2218706, by rfl⟩ : syracuseStep 2958275 = 4437413) B4437413
theorem B1754051 : Blo 1752577 1754051 := bstep (se 1 (by rfl) ⟨1315538, by rfl⟩ : syracuseStep 1754051 = 2631077) B2631077
theorem B12633029 : Blo 1752577 12633029 := bstep (se 4 (by rfl) ⟨1184346, by rfl⟩ : syracuseStep 12633029 = 2368693) B2368693
theorem B4441027 : Blo 1752577 4441027 := bstep (se 1 (by rfl) ⟨3330770, by rfl⟩ : syracuseStep 4441027 = 6661541) B6661541
theorem B2630609 : Blo 1752577 2630609 := bstep (se 2 (by rfl) ⟨986478, by rfl⟩ : syracuseStep 2630609 = 1972957) B1972957
theorem B1754067 : Blo 1752577 1754067 := bstep (se 1 (by rfl) ⟨1315550, by rfl⟩ : syracuseStep 1754067 = 2631101) B2631101
theorem B2630627 : Blo 1752577 2630627 := bstep (se 1 (by rfl) ⟨1972970, by rfl⟩ : syracuseStep 2630627 = 3945941) B3945941
theorem B1754083 : Blo 1752577 1754083 := bstep (se 1 (by rfl) ⟨1315562, by rfl⟩ : syracuseStep 1754083 = 2631125) B2631125
theorem B1754099 : Blo 1752577 1754099 := bstep (se 1 (by rfl) ⟨1315574, by rfl⟩ : syracuseStep 1754099 = 2631149) B2631149
theorem B2630657 : Blo 1752577 2630657 := bstep (se 2 (by rfl) ⟨986496, by rfl⟩ : syracuseStep 2630657 = 1972993) B1972993
theorem B1754115 : Blo 1752577 1754115 := bstep (se 1 (by rfl) ⟨1315586, by rfl⟩ : syracuseStep 1754115 = 2631173) B2631173
theorem B2630675 : Blo 1752577 2630675 := bstep (se 1 (by rfl) ⟨1973006, by rfl⟩ : syracuseStep 2630675 = 3946013) B3946013
theorem B1754131 : Blo 1752577 1754131 := bstep (se 1 (by rfl) ⟨1315598, by rfl⟩ : syracuseStep 1754131 = 2631197) B2631197
theorem B1754147 : Blo 1752577 1754147 := bstep (se 1 (by rfl) ⟨1315610, by rfl⟩ : syracuseStep 1754147 = 2631221) B2631221
theorem B2630705 : Blo 1752577 2630705 := bstep (se 2 (by rfl) ⟨986514, by rfl⟩ : syracuseStep 2630705 = 1973029) B1973029
theorem B1754163 : Blo 1752577 1754163 := bstep (se 1 (by rfl) ⟨1315622, by rfl⟩ : syracuseStep 1754163 = 2631245) B2631245
theorem B2958403 : Blo 1752577 2958403 := bstep (se 1 (by rfl) ⟨2218802, by rfl⟩ : syracuseStep 2958403 = 4437605) B4437605
theorem B2630723 : Blo 1752577 2630723 := bstep (se 1 (by rfl) ⟨1973042, by rfl⟩ : syracuseStep 2630723 = 3946085) B3946085
theorem B1754179 : Blo 1752577 1754179 := bstep (se 1 (by rfl) ⟨1315634, by rfl⟩ : syracuseStep 1754179 = 2631269) B2631269
theorem B4441169 : Blo 1752577 4441169 := bstep (se 2 (by rfl) ⟨1665438, by rfl⟩ : syracuseStep 4441169 = 3330877) B3330877
theorem B1754195 : Blo 1752577 1754195 := bstep (se 1 (by rfl) ⟨1315646, by rfl⟩ : syracuseStep 1754195 = 2631293) B2631293
theorem B2630753 : Blo 1752577 2630753 := bstep (se 2 (by rfl) ⟨986532, by rfl⟩ : syracuseStep 2630753 = 1973065) B1973065
theorem B1754211 : Blo 1752577 1754211 := bstep (se 1 (by rfl) ⟨1315658, by rfl⟩ : syracuseStep 1754211 = 2631317) B2631317
theorem B2630771 : Blo 1752577 2630771 := bstep (se 1 (by rfl) ⟨1973078, by rfl⟩ : syracuseStep 2630771 = 3946157) B3946157
theorem B1754227 : Blo 1752577 1754227 := bstep (se 1 (by rfl) ⟨1315670, by rfl⟩ : syracuseStep 1754227 = 2631341) B2631341
theorem B1754243 : Blo 1752577 1754243 := bstep (se 1 (by rfl) ⟨1315682, by rfl⟩ : syracuseStep 1754243 = 2631365) B2631365
theorem B2630801 : Blo 1752577 2630801 := bstep (se 2 (by rfl) ⟨986550, by rfl⟩ : syracuseStep 2630801 = 1973101) B1973101
theorem B1754259 : Blo 1752577 1754259 := bstep (se 1 (by rfl) ⟨1315694, by rfl⟩ : syracuseStep 1754259 = 2631389) B2631389
theorem B2630819 : Blo 1752577 2630819 := bstep (se 1 (by rfl) ⟨1973114, by rfl⟩ : syracuseStep 2630819 = 3946229) B3946229
theorem B1754275 : Blo 1752577 1754275 := bstep (se 1 (by rfl) ⟨1315706, by rfl⟩ : syracuseStep 1754275 = 2631413) B2631413
theorem B1754291 : Blo 1752577 1754291 := bstep (se 1 (by rfl) ⟨1315718, by rfl⟩ : syracuseStep 1754291 = 2631437) B2631437
theorem B2630849 : Blo 1752577 2630849 := bstep (se 2 (by rfl) ⟨986568, by rfl⟩ : syracuseStep 2630849 = 1973137) B1973137
theorem B1754307 : Blo 1752577 1754307 := bstep (se 1 (by rfl) ⟨1315730, by rfl⟩ : syracuseStep 1754307 = 2631461) B2631461
theorem B2958545 : Blo 1752577 2958545 := bstep (se 2 (by rfl) ⟨1109454, by rfl⟩ : syracuseStep 2958545 = 2218909) B2218909
theorem B2565329 : Blo 1752577 2565329 := bstep (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) B1923997
theorem B2630867 : Blo 1752577 2630867 := bstep (se 1 (by rfl) ⟨1973150, by rfl⟩ : syracuseStep 2630867 = 3946301) B3946301
theorem B1754323 : Blo 1752577 1754323 := bstep (se 1 (by rfl) ⟨1315742, by rfl⟩ : syracuseStep 1754323 = 2631485) B2631485
theorem B1754339 : Blo 1752577 1754339 := bstep (se 1 (by rfl) ⟨1315754, by rfl⟩ : syracuseStep 1754339 = 2631509) B2631509
theorem B2630897 : Blo 1752577 2630897 := bstep (se 2 (by rfl) ⟨986586, by rfl⟩ : syracuseStep 2630897 = 1973173) B1973173
theorem B3040499 : Blo 1752577 3040499 := bstep (se 1 (by rfl) ⟨2280374, by rfl⟩ : syracuseStep 3040499 = 4560749) B4560749
theorem B1754355 : Blo 1752577 1754355 := bstep (se 1 (by rfl) ⟨1315766, by rfl⟩ : syracuseStep 1754355 = 2631533) B2631533
theorem B2630915 : Blo 1752577 2630915 := bstep (se 1 (by rfl) ⟨1973186, by rfl⟩ : syracuseStep 2630915 = 3946373) B3946373
theorem B1754371 : Blo 1752577 1754371 := bstep (se 1 (by rfl) ⟨1315778, by rfl⟩ : syracuseStep 1754371 = 2631557) B2631557
theorem B1754387 : Blo 1752577 1754387 := bstep (se 1 (by rfl) ⟨1315790, by rfl⟩ : syracuseStep 1754387 = 2631581) B2631581
theorem B2630945 : Blo 1752577 2630945 := bstep (se 2 (by rfl) ⟨986604, by rfl⟩ : syracuseStep 2630945 = 1973209) B1973209
theorem B1754403 : Blo 1752577 1754403 := bstep (se 1 (by rfl) ⟨1315802, by rfl⟩ : syracuseStep 1754403 = 2631605) B2631605
theorem B2630963 : Blo 1752577 2630963 := bstep (se 1 (by rfl) ⟨1973222, by rfl⟩ : syracuseStep 2630963 = 3946445) B3946445
theorem B1754419 : Blo 1752577 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B1754435 : Blo 1752577 1754435 := bstep (se 1 (by rfl) ⟨1315826, by rfl⟩ : syracuseStep 1754435 = 2631653) B2631653
theorem B2958673 : Blo 1752577 2958673 := bstep (se 2 (by rfl) ⟨1109502, by rfl⟩ : syracuseStep 2958673 = 2219005) B2219005
theorem B2630993 : Blo 1752577 2630993 := bstep (se 2 (by rfl) ⟨986622, by rfl⟩ : syracuseStep 2630993 = 1973245) B1973245
theorem B1754451 : Blo 1752577 1754451 := bstep (se 1 (by rfl) ⟨1315838, by rfl⟩ : syracuseStep 1754451 = 2631677) B2631677
theorem B3327331 : Blo 1752577 3327331 := bstep (se 1 (by rfl) ⟨2495498, by rfl⟩ : syracuseStep 3327331 = 4990997) B4990997
theorem B2631011 : Blo 1752577 2631011 := bstep (se 1 (by rfl) ⟨1973258, by rfl⟩ : syracuseStep 2631011 = 3946517) B3946517
theorem B1754467 : Blo 1752577 1754467 := bstep (se 1 (by rfl) ⟨1315850, by rfl⟩ : syracuseStep 1754467 = 2631701) B2631701
theorem B2958707 : Blo 1752577 2958707 := bstep (se 1 (by rfl) ⟨2219030, by rfl⟩ : syracuseStep 2958707 = 4438061) B4438061
theorem B1754483 : Blo 1752577 1754483 := bstep (se 1 (by rfl) ⟨1315862, by rfl⟩ : syracuseStep 1754483 = 2631725) B2631725
theorem B2631041 : Blo 1752577 2631041 := bstep (se 2 (by rfl) ⟨986640, by rfl⟩ : syracuseStep 2631041 = 1973281) B1973281
theorem B9987461 : Blo 1752577 9987461 := bstep (se 4 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 9987461 = 1872649) B1872649
theorem B1754499 : Blo 1752577 1754499 := bstep (se 1 (by rfl) ⟨1315874, by rfl⟩ : syracuseStep 1754499 = 2631749) B2631749
theorem B2631059 : Blo 1752577 2631059 := bstep (se 1 (by rfl) ⟨1973294, by rfl⟩ : syracuseStep 2631059 = 3946589) B3946589
theorem B1754515 : Blo 1752577 1754515 := bstep (se 1 (by rfl) ⟨1315886, by rfl⟩ : syracuseStep 1754515 = 2631773) B2631773
theorem B2368931 : Blo 1752577 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B3745187 : Blo 1752577 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B1754531 : Blo 1752577 1754531 := bstep (se 1 (by rfl) ⟨1315898, by rfl⟩ : syracuseStep 1754531 = 2631797) B2631797
theorem B5916077 : Blo 1752577 5916077 := bstep (se 3 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 5916077 = 2218529) B2218529
theorem B2631089 : Blo 1752577 2631089 := bstep (se 2 (by rfl) ⟨986658, by rfl⟩ : syracuseStep 2631089 = 1973317) B1973317
theorem B1754547 : Blo 1752577 1754547 := bstep (se 1 (by rfl) ⟨1315910, by rfl⟩ : syracuseStep 1754547 = 2631821) B2631821
theorem B2631107 : Blo 1752577 2631107 := bstep (se 1 (by rfl) ⟨1973330, by rfl⟩ : syracuseStep 2631107 = 3946661) B3946661
theorem B1754563 : Blo 1752577 1754563 := bstep (se 1 (by rfl) ⟨1315922, by rfl⟩ : syracuseStep 1754563 = 2631845) B2631845
theorem B2631137 : Blo 1752577 2631137 := bstep (se 2 (by rfl) ⟨986676, by rfl⟩ : syracuseStep 2631137 = 1973353) B1973353
theorem B5916131 : Blo 1752577 5916131 := bstep (se 1 (by rfl) ⟨4437098, by rfl⟩ : syracuseStep 5916131 = 8874197) B8874197
theorem B8881649 : Blo 1752577 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B2958835 : Blo 1752577 2958835 := bstep (se 1 (by rfl) ⟨2219126, by rfl⟩ : syracuseStep 2958835 = 4438253) B4438253
theorem B2631155 : Blo 1752577 2631155 := bstep (se 1 (by rfl) ⟨1973366, by rfl⟩ : syracuseStep 2631155 = 3946733) B3946733
theorem B3556867 : Blo 1752577 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B2631185 : Blo 1752577 2631185 := bstep (se 2 (by rfl) ⟨986694, by rfl⟩ : syracuseStep 2631185 = 1973389) B1973389
theorem B2631203 : Blo 1752577 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B33326645 : Blo 1752577 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B2631233 : Blo 1752577 2631233 := bstep (se 2 (by rfl) ⟨986712, by rfl⟩ : syracuseStep 2631233 = 1973425) B1973425
theorem B8873549 : Blo 1752577 8873549 := bstep (se 3 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 8873549 = 3327581) B3327581
theorem B6661709 : Blo 1752577 6661709 := bstep (se 3 (by rfl) ⟨1249070, by rfl⟩ : syracuseStep 6661709 = 2498141) B2498141
theorem B2631251 : Blo 1752577 2631251 := bstep (se 1 (by rfl) ⟨1973438, by rfl⟩ : syracuseStep 2631251 = 3946877) B3946877
theorem B7112291 : Blo 1752577 7112291 := bstep (se 1 (by rfl) ⟨5334218, by rfl⟩ : syracuseStep 7112291 = 10668437) B10668437
theorem B4212337 : Blo 1752577 4212337 := bstep (se 2 (by rfl) ⟨1579626, by rfl⟩ : syracuseStep 4212337 = 3159253) B3159253
theorem B2631281 : Blo 1752577 2631281 := bstep (se 2 (by rfl) ⟨986730, by rfl⟩ : syracuseStep 2631281 = 1973461) B1973461
theorem B2958977 : Blo 1752577 2958977 := bstep (se 2 (by rfl) ⟨1109616, by rfl⟩ : syracuseStep 2958977 = 2219233) B2219233
theorem B2631299 : Blo 1752577 2631299 := bstep (se 1 (by rfl) ⟨1973474, by rfl⟩ : syracuseStep 2631299 = 3946949) B3946949
theorem B2631329 : Blo 1752577 2631329 := bstep (se 2 (by rfl) ⟨986748, by rfl⟩ : syracuseStep 2631329 = 1973497) B1973497
theorem B2631347 : Blo 1752577 2631347 := bstep (se 1 (by rfl) ⟨1973510, by rfl⟩ : syracuseStep 2631347 = 3947021) B3947021
theorem B2631377 : Blo 1752577 2631377 := bstep (se 2 (by rfl) ⟨986766, by rfl⟩ : syracuseStep 2631377 = 1973533) B1973533
theorem B2107091 : Blo 1752577 2107091 := bstep (se 1 (by rfl) ⟨1580318, by rfl⟩ : syracuseStep 2107091 = 3160637) B3160637
theorem B2631395 : Blo 1752577 2631395 := bstep (se 1 (by rfl) ⟨1973546, by rfl⟩ : syracuseStep 2631395 = 3947093) B3947093
theorem B5916401 : Blo 1752577 5916401 := bstep (se 2 (by rfl) ⟨2218650, by rfl⟩ : syracuseStep 5916401 = 4437301) B4437301
theorem B2959105 : Blo 1752577 2959105 := bstep (se 2 (by rfl) ⟨1109664, by rfl⟩ : syracuseStep 2959105 = 2219329) B2219329
theorem B2631425 : Blo 1752577 2631425 := bstep (se 2 (by rfl) ⟨986784, by rfl⟩ : syracuseStep 2631425 = 1973569) B1973569
theorem B5064461 : Blo 1752577 5064461 := bstep (se 3 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 5064461 = 1899173) B1899173
theorem B2631443 : Blo 1752577 2631443 := bstep (se 1 (by rfl) ⟨1973582, by rfl⟩ : syracuseStep 2631443 = 3947165) B3947165
theorem B3327779 : Blo 1752577 3327779 := bstep (se 1 (by rfl) ⟨2495834, by rfl⟩ : syracuseStep 3327779 = 4991669) B4991669
theorem B2959139 : Blo 1752577 2959139 := bstep (se 1 (by rfl) ⟨2219354, by rfl⟩ : syracuseStep 2959139 = 4438709) B4438709
theorem B2631473 : Blo 1752577 2631473 := bstep (se 2 (by rfl) ⟨986802, by rfl⟩ : syracuseStep 2631473 = 1973605) B1973605
theorem B2631491 : Blo 1752577 2631491 := bstep (se 1 (by rfl) ⟨1973618, by rfl⟩ : syracuseStep 2631491 = 3947237) B3947237
theorem B2631521 : Blo 1752577 2631521 := bstep (se 2 (by rfl) ⟨986820, by rfl⟩ : syracuseStep 2631521 = 1973641) B1973641
theorem B10667875 : Blo 1752577 10667875 := bstep (se 1 (by rfl) ⟨8000906, by rfl⟩ : syracuseStep 10667875 = 16001813) B16001813
theorem B2631539 : Blo 1752577 2631539 := bstep (se 1 (by rfl) ⟨1973654, by rfl⟩ : syracuseStep 2631539 = 3947309) B3947309
theorem B2631569 : Blo 1752577 2631569 := bstep (se 2 (by rfl) ⟨986838, by rfl⟩ : syracuseStep 2631569 = 1973677) B1973677
theorem B2959267 : Blo 1752577 2959267 := bstep (se 1 (by rfl) ⟨2219450, by rfl⟩ : syracuseStep 2959267 = 4438901) B4438901
theorem B2631587 : Blo 1752577 2631587 := bstep (se 1 (by rfl) ⟨1973690, by rfl⟩ : syracuseStep 2631587 = 3947381) B3947381
theorem B2631617 : Blo 1752577 2631617 := bstep (se 2 (by rfl) ⟨986856, by rfl⟩ : syracuseStep 2631617 = 1973713) B1973713
theorem B2631635 : Blo 1752577 2631635 := bstep (se 1 (by rfl) ⟨1973726, by rfl⟩ : syracuseStep 2631635 = 3947453) B3947453
theorem B3745777 : Blo 1752577 3745777 := bstep (se 2 (by rfl) ⟨1404666, by rfl⟩ : syracuseStep 3745777 = 2809333) B2809333
theorem B2631665 : Blo 1752577 2631665 := bstep (se 2 (by rfl) ⟨986874, by rfl⟩ : syracuseStep 2631665 = 1973749) B1973749
theorem B4212739 : Blo 1752577 4212739 := bstep (se 1 (by rfl) ⟨3159554, by rfl⟩ : syracuseStep 4212739 = 6319109) B6319109
theorem B2631683 : Blo 1752577 2631683 := bstep (se 1 (by rfl) ⟨1973762, by rfl⟩ : syracuseStep 2631683 = 3947525) B3947525
theorem B2631713 : Blo 1752577 2631713 := bstep (se 2 (by rfl) ⟨986892, by rfl⟩ : syracuseStep 2631713 = 1973785) B1973785
theorem B2959409 : Blo 1752577 2959409 := bstep (se 2 (by rfl) ⟨1109778, by rfl⟩ : syracuseStep 2959409 = 2219557) B2219557
theorem B2631731 : Blo 1752577 2631731 := bstep (se 1 (by rfl) ⟨1973798, by rfl⟩ : syracuseStep 2631731 = 3947597) B3947597
theorem B3328067 : Blo 1752577 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B12634181 : Blo 1752577 12634181 := bstep (se 4 (by rfl) ⟨1184454, by rfl⟩ : syracuseStep 12634181 = 2368909) B2368909
theorem B10127429 : Blo 1752577 10127429 := bstep (se 4 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 10127429 = 1898893) B1898893
theorem B4991053 : Blo 1752577 4991053 := bstep (se 3 (by rfl) ⟨935822, by rfl⟩ : syracuseStep 4991053 = 1871645) B1871645
theorem B2631761 : Blo 1752577 2631761 := bstep (se 2 (by rfl) ⟨986910, by rfl⟩ : syracuseStep 2631761 = 1973821) B1973821
theorem B2631779 : Blo 1752577 2631779 := bstep (se 1 (by rfl) ⟨1973834, by rfl⟩ : syracuseStep 2631779 = 3947669) B3947669
theorem B2631809 : Blo 1752577 2631809 := bstep (se 2 (by rfl) ⟨986928, by rfl⟩ : syracuseStep 2631809 = 1973857) B1973857
theorem B2369683 : Blo 1752577 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B2631827 : Blo 1752577 2631827 := bstep (se 1 (by rfl) ⟨1973870, by rfl⟩ : syracuseStep 2631827 = 3947741) B3947741
theorem B2959537 : Blo 1752577 2959537 := bstep (se 2 (by rfl) ⟨1109826, by rfl⟩ : syracuseStep 2959537 = 2219653) B2219653
theorem B2631857 : Blo 1752577 2631857 := bstep (se 2 (by rfl) ⟨986946, by rfl⟩ : syracuseStep 2631857 = 1973893) B1973893
theorem B2402497 : Blo 1752577 2402497 := bstep (se 2 (by rfl) ⟨900936, by rfl⟩ : syracuseStep 2402497 = 1801873) B1801873
theorem B10807501 : Blo 1752577 10807501 := bstep (se 3 (by rfl) ⟨2026406, by rfl⟩ : syracuseStep 10807501 = 4052813) B4052813
theorem B2959571 : Blo 1752577 2959571 := bstep (se 1 (by rfl) ⟨2219678, by rfl⟩ : syracuseStep 2959571 = 4439357) B4439357
theorem B4991213 : Blo 1752577 4991213 := bstep (se 3 (by rfl) ⟨935852, by rfl⟩ : syracuseStep 4991213 = 1871705) B1871705
theorem B5916941 : Blo 1752577 5916941 := bstep (se 3 (by rfl) ⟨1109426, by rfl⟩ : syracuseStep 5916941 = 2218853) B2218853
theorem B82118933 : Blo 1752577 82118933 := bstep (se 6 (by rfl) ⟨1924662, by rfl⟩ : syracuseStep 82118933 = 3849325) B3849325
theorem B5916995 : Blo 1752577 5916995 := bstep (se 1 (by rfl) ⟨4437746, by rfl⟩ : syracuseStep 5916995 = 8875493) B8875493
theorem B2959699 : Blo 1752577 2959699 := bstep (se 1 (by rfl) ⟨2219774, by rfl⟩ : syracuseStep 2959699 = 4439549) B4439549
theorem B4991395 : Blo 1752577 4991395 := bstep (se 1 (by rfl) ⟨3743546, by rfl⟩ : syracuseStep 4991395 = 7487093) B7487093
theorem B6080941 : Blo 1752577 6080941 := bstep (se 3 (by rfl) ⟨1140176, by rfl⟩ : syracuseStep 6080941 = 2280353) B2280353
theorem B2959841 : Blo 1752577 2959841 := bstep (se 2 (by rfl) ⟨1109940, by rfl⟩ : syracuseStep 2959841 = 2219881) B2219881
theorem B37923299 : Blo 1752577 37923299 := bstep (se 1 (by rfl) ⟨28442474, by rfl⟩ : syracuseStep 37923299 = 56884949) B56884949
theorem B6318577 : Blo 1752577 6318577 := bstep (se 2 (by rfl) ⟨2369466, by rfl⟩ : syracuseStep 6318577 = 4738933) B4738933
theorem B3000883 : Blo 1752577 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B5917265 : Blo 1752577 5917265 := bstep (se 2 (by rfl) ⟨2218974, by rfl⟩ : syracuseStep 5917265 = 4437949) B4437949
theorem B2959969 : Blo 1752577 2959969 := bstep (se 2 (by rfl) ⟨1109988, by rfl⟩ : syracuseStep 2959969 = 2219977) B2219977
theorem B2960003 : Blo 1752577 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B3418769 : Blo 1752577 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B50588387 : Blo 1752577 50588387 := bstep (se 1 (by rfl) ⟨37941290, by rfl⟩ : syracuseStep 50588387 = 75882581) B75882581
theorem B2665219 : Blo 1752577 2665219 := bstep (se 1 (by rfl) ⟨1998914, by rfl⟩ : syracuseStep 2665219 = 3997829) B3997829
theorem B2960131 : Blo 1752577 2960131 := bstep (se 1 (by rfl) ⟨2220098, by rfl⟩ : syracuseStep 2960131 = 4440197) B4440197
theorem B7490339 : Blo 1752577 7490339 := bstep (se 1 (by rfl) ⟨5617754, by rfl⟩ : syracuseStep 7490339 = 11235509) B11235509
theorem B2665315 : Blo 1752577 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B10259341 : Blo 1752577 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B3943313 : Blo 1752577 3943313 := bstep (se 2 (by rfl) ⟨1478742, by rfl⟩ : syracuseStep 3943313 = 2957485) B2957485
theorem B2960273 : Blo 1752577 2960273 := bstep (se 2 (by rfl) ⟨1110102, by rfl⟩ : syracuseStep 2960273 = 2220205) B2220205
theorem B3943331 : Blo 1752577 3943331 := bstep (se 1 (by rfl) ⟨2957498, by rfl⟩ : syracuseStep 3943331 = 5914997) B5914997
theorem B3329009 : Blo 1752577 3329009 := bstep (se 2 (by rfl) ⟨1248378, by rfl⟩ : syracuseStep 3329009 = 2496757) B2496757
theorem B8424461 : Blo 1752577 8424461 := bstep (se 3 (by rfl) ⟨1579586, by rfl⟩ : syracuseStep 8424461 = 3159173) B3159173
theorem B4213777 : Blo 1752577 4213777 := bstep (se 2 (by rfl) ⟨1580166, by rfl⟩ : syracuseStep 4213777 = 3160333) B3160333
theorem B2960401 : Blo 1752577 2960401 := bstep (se 2 (by rfl) ⟨1110150, by rfl⟩ : syracuseStep 2960401 = 2220301) B2220301
theorem B2665505 : Blo 1752577 2665505 := bstep (se 2 (by rfl) ⟨999564, by rfl⟩ : syracuseStep 2665505 = 1999129) B1999129
theorem B10120241 : Blo 1752577 10120241 := bstep (se 2 (by rfl) ⟨3795090, by rfl⟩ : syracuseStep 10120241 = 7590181) B7590181
theorem B2960435 : Blo 1752577 2960435 := bstep (se 1 (by rfl) ⟨2220326, by rfl⟩ : syracuseStep 2960435 = 4440653) B4440653
theorem B5999683 : Blo 1752577 5999683 := bstep (se 1 (by rfl) ⟨4499762, by rfl⟩ : syracuseStep 5999683 = 8999525) B8999525
theorem B5917805 : Blo 1752577 5917805 := bstep (se 3 (by rfl) ⟨1109588, by rfl⟩ : syracuseStep 5917805 = 2219177) B2219177
theorem B5917859 : Blo 1752577 5917859 := bstep (se 1 (by rfl) ⟨4438394, by rfl⟩ : syracuseStep 5917859 = 8876789) B8876789
theorem B3943601 : Blo 1752577 3943601 := bstep (se 2 (by rfl) ⟨1478850, by rfl⟩ : syracuseStep 3943601 = 2957701) B2957701
theorem B2960563 : Blo 1752577 2960563 := bstep (se 1 (by rfl) ⟨2220422, by rfl⟩ : syracuseStep 2960563 = 4440845) B4440845
theorem B3943619 : Blo 1752577 3943619 := bstep (se 1 (by rfl) ⟨2957714, by rfl⟩ : syracuseStep 3943619 = 5915429) B5915429
theorem B2960705 : Blo 1752577 2960705 := bstep (se 2 (by rfl) ⟨1110264, by rfl⟩ : syracuseStep 2960705 = 2220529) B2220529
theorem B7114061 : Blo 1752577 7114061 := bstep (se 3 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 7114061 = 2667773) B2667773
theorem B13315427 : Blo 1752577 13315427 := bstep (se 1 (by rfl) ⟨9986570, by rfl⟩ : syracuseStep 13315427 = 19973141) B19973141
theorem B5918129 : Blo 1752577 5918129 := bstep (se 2 (by rfl) ⟨2219298, by rfl⟩ : syracuseStep 5918129 = 4438597) B4438597
theorem B2960833 : Blo 1752577 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B3943889 : Blo 1752577 3943889 := bstep (se 2 (by rfl) ⟨1478958, by rfl⟩ : syracuseStep 3943889 = 2957917) B2957917
theorem B3943907 : Blo 1752577 3943907 := bstep (se 1 (by rfl) ⟨2957930, by rfl⟩ : syracuseStep 3943907 = 5915861) B5915861
theorem B25636493 : Blo 1752577 25636493 := bstep (se 3 (by rfl) ⟨4806842, by rfl⟩ : syracuseStep 25636493 = 9613685) B9613685
theorem B5615345 : Blo 1752577 5615345 := bstep (se 2 (by rfl) ⟨2105754, by rfl⟩ : syracuseStep 5615345 = 4211509) B4211509
theorem B3944177 : Blo 1752577 3944177 := bstep (se 2 (by rfl) ⟨1479066, by rfl⟩ : syracuseStep 3944177 = 2958133) B2958133
theorem B3944195 : Blo 1752577 3944195 := bstep (se 1 (by rfl) ⟨2958146, by rfl⟩ : syracuseStep 3944195 = 5916293) B5916293
theorem B4992785 : Blo 1752577 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B3329905 : Blo 1752577 3329905 := bstep (se 2 (by rfl) ⟨1248714, by rfl⟩ : syracuseStep 3329905 = 2497429) B2497429
theorem B1871795 : Blo 1752577 1871795 := bstep (se 1 (by rfl) ⟨1403846, by rfl⟩ : syracuseStep 1871795 = 2807693) B2807693
theorem B5918669 : Blo 1752577 5918669 := bstep (se 3 (by rfl) ⟨1109750, by rfl⟩ : syracuseStep 5918669 = 2219501) B2219501
theorem B5918723 : Blo 1752577 5918723 := bstep (se 1 (by rfl) ⟨4439042, by rfl⟩ : syracuseStep 5918723 = 8878085) B8878085
theorem B3944465 : Blo 1752577 3944465 := bstep (se 2 (by rfl) ⟨1479174, by rfl⟩ : syracuseStep 3944465 = 2958349) B2958349
theorem B3330065 : Blo 1752577 3330065 := bstep (se 2 (by rfl) ⟨1248774, by rfl⟩ : syracuseStep 3330065 = 2497549) B2497549
theorem B3944483 : Blo 1752577 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B4739107 : Blo 1752577 4739107 := bstep (se 1 (by rfl) ⟨3554330, by rfl⟩ : syracuseStep 4739107 = 7108661) B7108661
theorem B5615693 : Blo 1752577 5615693 := bstep (se 3 (by rfl) ⟨1052942, by rfl⟩ : syracuseStep 5615693 = 2105885) B2105885
theorem B21319793 : Blo 1752577 21319793 := bstep (se 2 (by rfl) ⟨7994922, by rfl⟩ : syracuseStep 21319793 = 15989845) B15989845
theorem B21328069 : Blo 1752577 21328069 := bstep (se 4 (by rfl) ⟨1999506, by rfl⟩ : syracuseStep 21328069 = 3999013) B3999013
theorem B5918993 : Blo 1752577 5918993 := bstep (se 2 (by rfl) ⟨2219622, by rfl⟩ : syracuseStep 5918993 = 4439245) B4439245
theorem B9605425 : Blo 1752577 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B3944753 : Blo 1752577 3944753 := bstep (se 2 (by rfl) ⟨1479282, by rfl⟩ : syracuseStep 3944753 = 2958565) B2958565
theorem B3944771 : Blo 1752577 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B2666819 : Blo 1752577 2666819 := bstep (se 1 (by rfl) ⟨2000114, by rfl⟩ : syracuseStep 2666819 = 4000229) B4000229
theorem B22466915 : Blo 1752577 22466915 := bstep (se 1 (by rfl) ⟨16850186, by rfl⟩ : syracuseStep 22466915 = 33700373) B33700373
theorem B3330467 : Blo 1752577 3330467 := bstep (se 1 (by rfl) ⟨2497850, by rfl⟩ : syracuseStep 3330467 = 4995701) B4995701
theorem B8876465 : Blo 1752577 8876465 := bstep (se 2 (by rfl) ⟨3328674, by rfl⟩ : syracuseStep 8876465 = 6657349) B6657349
theorem B2667043 : Blo 1752577 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B14979653 : Blo 1752577 14979653 := bstep (se 4 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 14979653 = 2808685) B2808685
theorem B3945041 : Blo 1752577 3945041 := bstep (se 2 (by rfl) ⟨1479390, by rfl⟩ : syracuseStep 3945041 = 2958781) B2958781
theorem B3945059 : Blo 1752577 3945059 := bstep (se 1 (by rfl) ⟨2958794, by rfl⟩ : syracuseStep 3945059 = 5917589) B5917589
theorem B14217869 : Blo 1752577 14217869 := bstep (se 3 (by rfl) ⟨2665850, by rfl⟩ : syracuseStep 14217869 = 5331701) B5331701
theorem B5001905 : Blo 1752577 5001905 := bstep (se 2 (by rfl) ⟨1875714, by rfl⟩ : syracuseStep 5001905 = 3751429) B3751429
theorem B4993741 : Blo 1752577 4993741 := bstep (se 3 (by rfl) ⟨936326, by rfl⟩ : syracuseStep 4993741 = 1872653) B1872653
theorem B5919533 : Blo 1752577 5919533 := bstep (se 3 (by rfl) ⟨1109912, by rfl⟩ : syracuseStep 5919533 = 2219825) B2219825
theorem B16855877 : Blo 1752577 16855877 := bstep (se 4 (by rfl) ⟨1580238, by rfl⟩ : syracuseStep 16855877 = 3160477) B3160477
theorem B5919587 : Blo 1752577 5919587 := bstep (se 1 (by rfl) ⟨4439690, by rfl⟩ : syracuseStep 5919587 = 8879381) B8879381
theorem B3945329 : Blo 1752577 3945329 := bstep (se 2 (by rfl) ⟨1479498, by rfl⟩ : syracuseStep 3945329 = 2958997) B2958997
theorem B3945347 : Blo 1752577 3945347 := bstep (se 1 (by rfl) ⟨2959010, by rfl⟩ : syracuseStep 3945347 = 5918021) B5918021
theorem B4993969 : Blo 1752577 4993969 := bstep (se 2 (by rfl) ⟨1872738, by rfl⟩ : syracuseStep 4993969 = 3745477) B3745477
theorem B4436977 : Blo 1752577 4436977 := bstep (se 2 (by rfl) ⟨1663866, by rfl⟩ : syracuseStep 4436977 = 3327733) B3327733
theorem B4994129 : Blo 1752577 4994129 := bstep (se 2 (by rfl) ⟨1872798, by rfl⟩ : syracuseStep 4994129 = 3745597) B3745597
theorem B6657137 : Blo 1752577 6657137 := bstep (se 2 (by rfl) ⟨2496426, by rfl⟩ : syracuseStep 6657137 = 4992853) B4992853
theorem B5919857 : Blo 1752577 5919857 := bstep (se 2 (by rfl) ⟨2219946, by rfl⟩ : syracuseStep 5919857 = 4439893) B4439893
theorem B14988401 : Blo 1752577 14988401 := bstep (se 2 (by rfl) ⟨5620650, by rfl⟩ : syracuseStep 14988401 = 11241301) B11241301
theorem B9991309 : Blo 1752577 9991309 := bstep (se 3 (by rfl) ⟨1873370, by rfl⟩ : syracuseStep 9991309 = 3746741) B3746741
theorem B3945617 : Blo 1752577 3945617 := bstep (se 2 (by rfl) ⟨1479606, by rfl⟩ : syracuseStep 3945617 = 2959213) B2959213
theorem B3945635 : Blo 1752577 3945635 := bstep (se 1 (by rfl) ⟨2959226, by rfl⟩ : syracuseStep 3945635 = 5918453) B5918453
theorem B4994243 : Blo 1752577 4994243 := bstep (se 1 (by rfl) ⟨3745682, by rfl⟩ : syracuseStep 4994243 = 7491365) B7491365
theorem B4437251 : Blo 1752577 4437251 := bstep (se 1 (by rfl) ⟨3327938, by rfl⟩ : syracuseStep 4437251 = 6655877) B6655877
theorem B2495777 : Blo 1752577 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B2495891 : Blo 1752577 2495891 := bstep (se 1 (by rfl) ⟨1871918, by rfl⟩ : syracuseStep 2495891 = 3743837) B3743837
theorem B6747569 : Blo 1752577 6747569 := bstep (se 2 (by rfl) ⟨2530338, by rfl⟩ : syracuseStep 6747569 = 5060677) B5060677
theorem B3945905 : Blo 1752577 3945905 := bstep (se 2 (by rfl) ⟨1479714, by rfl⟩ : syracuseStep 3945905 = 2959429) B2959429
theorem B4437443 : Blo 1752577 4437443 := bstep (se 1 (by rfl) ⟨3328082, by rfl⟩ : syracuseStep 4437443 = 6656165) B6656165
theorem B3945923 : Blo 1752577 3945923 := bstep (se 1 (by rfl) ⟨2959442, by rfl⟩ : syracuseStep 3945923 = 5918885) B5918885
theorem B2495971 : Blo 1752577 2495971 := bstep (se 1 (by rfl) ⟨1871978, by rfl⟩ : syracuseStep 2495971 = 3743957) B3743957
theorem B1971715 : Blo 1752577 1971715 := bstep (se 1 (by rfl) ⟨1478786, by rfl⟩ : syracuseStep 1971715 = 2957573) B2957573
theorem B5920397 : Blo 1752577 5920397 := bstep (se 3 (by rfl) ⟨1110074, by rfl⟩ : syracuseStep 5920397 = 2220149) B2220149
theorem B1971859 : Blo 1752577 1971859 := bstep (se 1 (by rfl) ⟨1478894, by rfl⟩ : syracuseStep 1971859 = 2957789) B2957789
theorem B3421873 : Blo 1752577 3421873 := bstep (se 2 (by rfl) ⟨1283202, by rfl⟩ : syracuseStep 3421873 = 2566405) B2566405
theorem B5920451 : Blo 1752577 5920451 := bstep (se 1 (by rfl) ⟨4440338, by rfl⟩ : syracuseStep 5920451 = 8880677) B8880677
theorem B3946193 : Blo 1752577 3946193 := bstep (se 2 (by rfl) ⟨1479822, by rfl⟩ : syracuseStep 3946193 = 2959645) B2959645
theorem B3946211 : Blo 1752577 3946211 := bstep (se 1 (by rfl) ⟨2959658, by rfl⟩ : syracuseStep 3946211 = 5919317) B5919317
theorem B1972003 : Blo 1752577 1972003 := bstep (se 1 (by rfl) ⟨1479002, by rfl⟩ : syracuseStep 1972003 = 2958005) B2958005
theorem B8877923 : Blo 1752577 8877923 := bstep (se 1 (by rfl) ⟨6658442, by rfl⟩ : syracuseStep 8877923 = 13316885) B13316885
theorem B5617549 : Blo 1752577 5617549 := bstep (se 3 (by rfl) ⟨1053290, by rfl⟩ : syracuseStep 5617549 = 2106581) B2106581
theorem B1972147 : Blo 1752577 1972147 := bstep (se 1 (by rfl) ⟨1479110, by rfl⟩ : syracuseStep 1972147 = 2958221) B2958221
theorem B5920721 : Blo 1752577 5920721 := bstep (se 2 (by rfl) ⟨2220270, by rfl⟩ : syracuseStep 5920721 = 4440541) B4440541
theorem B4741105 : Blo 1752577 4741105 := bstep (se 2 (by rfl) ⟨1777914, by rfl⟩ : syracuseStep 4741105 = 3555829) B3555829
theorem B3946481 : Blo 1752577 3946481 := bstep (se 2 (by rfl) ⟨1479930, by rfl⟩ : syracuseStep 3946481 = 2959861) B2959861
theorem B3946499 : Blo 1752577 3946499 := bstep (se 1 (by rfl) ⟨2959874, by rfl⟩ : syracuseStep 3946499 = 5919749) B5919749
theorem B2496529 : Blo 1752577 2496529 := bstep (se 2 (by rfl) ⟨936198, by rfl⟩ : syracuseStep 2496529 = 1872397) B1872397
theorem B1972291 : Blo 1752577 1972291 := bstep (se 1 (by rfl) ⟨1479218, by rfl⟩ : syracuseStep 1972291 = 2958437) B2958437
theorem B22771781 : Blo 1752577 22771781 := bstep (se 4 (by rfl) ⟨2134854, by rfl⟩ : syracuseStep 22771781 = 4269709) B4269709
theorem B4995245 : Blo 1752577 4995245 := bstep (se 3 (by rfl) ⟨936608, by rfl⟩ : syracuseStep 4995245 = 1873217) B1873217
theorem B2218195 : Blo 1752577 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B1972435 : Blo 1752577 1972435 := bstep (se 1 (by rfl) ⟨1479326, by rfl⟩ : syracuseStep 1972435 = 2958653) B2958653
theorem B3946769 : Blo 1752577 3946769 := bstep (se 2 (by rfl) ⟨1480038, by rfl⟩ : syracuseStep 3946769 = 2960077) B2960077
theorem B2808083 : Blo 1752577 2808083 := bstep (se 1 (by rfl) ⟨2106062, by rfl⟩ : syracuseStep 2808083 = 4212125) B4212125
theorem B3946787 : Blo 1752577 3946787 := bstep (se 1 (by rfl) ⟨2960090, by rfl⟩ : syracuseStep 3946787 = 5920181) B5920181
theorem B1972579 : Blo 1752577 1972579 := bstep (se 1 (by rfl) ⟨1479434, by rfl⟩ : syracuseStep 1972579 = 2958869) B2958869
theorem B4995427 : Blo 1752577 4995427 := bstep (se 1 (by rfl) ⟨3746570, by rfl⟩ : syracuseStep 4995427 = 7493141) B7493141
theorem B4438385 : Blo 1752577 4438385 := bstep (se 2 (by rfl) ⟨1664394, by rfl⟩ : syracuseStep 4438385 = 3328789) B3328789
theorem B7494029 : Blo 1752577 7494029 := bstep (se 3 (by rfl) ⟨1405130, by rfl⟩ : syracuseStep 7494029 = 2810261) B2810261
theorem B2808211 : Blo 1752577 2808211 := bstep (se 1 (by rfl) ⟨2106158, by rfl⟩ : syracuseStep 2808211 = 4212317) B4212317
theorem B4438435 : Blo 1752577 4438435 := bstep (se 1 (by rfl) ⟨3328826, by rfl⟩ : syracuseStep 4438435 = 6657653) B6657653
theorem B7494065 : Blo 1752577 7494065 := bstep (se 2 (by rfl) ⟨2810274, by rfl⟩ : syracuseStep 7494065 = 5620549) B5620549
theorem B2808275 : Blo 1752577 2808275 := bstep (se 1 (by rfl) ⟨2106206, by rfl⟩ : syracuseStep 2808275 = 4212413) B4212413
theorem B5921261 : Blo 1752577 5921261 := bstep (se 3 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 5921261 = 2220473) B2220473
theorem B21322225 : Blo 1752577 21322225 := bstep (se 2 (by rfl) ⟨7995834, by rfl⟩ : syracuseStep 21322225 = 15991669) B15991669
theorem B1972723 : Blo 1752577 1972723 := bstep (se 1 (by rfl) ⟨1479542, by rfl⟩ : syracuseStep 1972723 = 2959085) B2959085
theorem B4995587 : Blo 1752577 4995587 := bstep (se 1 (by rfl) ⟨3746690, by rfl⟩ : syracuseStep 4995587 = 7493381) B7493381
theorem B4741649 : Blo 1752577 4741649 := bstep (se 2 (by rfl) ⟨1778118, by rfl⟩ : syracuseStep 4741649 = 3556237) B3556237
theorem B6658595 : Blo 1752577 6658595 := bstep (se 1 (by rfl) ⟨4993946, by rfl⟩ : syracuseStep 6658595 = 9987893) B9987893
theorem B5921315 : Blo 1752577 5921315 := bstep (se 1 (by rfl) ⟨4440986, by rfl⟩ : syracuseStep 5921315 = 8881973) B8881973
theorem B4438577 : Blo 1752577 4438577 := bstep (se 2 (by rfl) ⟨1664466, by rfl⟩ : syracuseStep 4438577 = 3328933) B3328933
theorem B3947057 : Blo 1752577 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B3947075 : Blo 1752577 3947075 := bstep (se 1 (by rfl) ⟨2960306, by rfl⟩ : syracuseStep 3947075 = 5920613) B5920613
theorem B1972867 : Blo 1752577 1972867 := bstep (se 1 (by rfl) ⟨1479650, by rfl⟩ : syracuseStep 1972867 = 2959301) B2959301
theorem B8878733 : Blo 1752577 8878733 := bstep (se 3 (by rfl) ⟨1664762, by rfl⟩ : syracuseStep 8878733 = 3329525) B3329525
theorem B2218691 : Blo 1752577 2218691 := bstep (se 1 (by rfl) ⟨1664018, by rfl⟩ : syracuseStep 2218691 = 3328037) B3328037
theorem B2497235 : Blo 1752577 2497235 := bstep (se 1 (by rfl) ⟨1872926, by rfl⟩ : syracuseStep 2497235 = 3745853) B3745853
theorem B1973011 : Blo 1752577 1973011 := bstep (se 1 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 1973011 = 2959517) B2959517
theorem B5921585 : Blo 1752577 5921585 := bstep (se 2 (by rfl) ⟨2220594, by rfl⟩ : syracuseStep 5921585 = 4441189) B4441189
theorem B3947345 : Blo 1752577 3947345 := bstep (se 2 (by rfl) ⟨1480254, by rfl⟩ : syracuseStep 3947345 = 2960509) B2960509
theorem B7486307 : Blo 1752577 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B3947363 : Blo 1752577 3947363 := bstep (se 1 (by rfl) ⟨2960522, by rfl⟩ : syracuseStep 3947363 = 5921045) B5921045
theorem B18963341 : Blo 1752577 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B1973155 : Blo 1752577 1973155 := bstep (se 1 (by rfl) ⟨1479866, by rfl⟩ : syracuseStep 1973155 = 2959733) B2959733
theorem B2808769 : Blo 1752577 2808769 := bstep (se 2 (by rfl) ⟨1053288, by rfl⟩ : syracuseStep 2808769 = 2106577) B2106577
theorem B3374083 : Blo 1752577 3374083 := bstep (se 1 (by rfl) ⟨2530562, by rfl⟩ : syracuseStep 3374083 = 5061125) B5061125
theorem B1973299 : Blo 1752577 1973299 := bstep (se 1 (by rfl) ⟨1479974, by rfl⟩ : syracuseStep 1973299 = 2959949) B2959949
theorem B3161155 : Blo 1752577 3161155 := bstep (se 1 (by rfl) ⟨2370866, by rfl⟩ : syracuseStep 3161155 = 4741733) B4741733
theorem B3947633 : Blo 1752577 3947633 := bstep (se 2 (by rfl) ⟨1480362, by rfl⟩ : syracuseStep 3947633 = 2960725) B2960725
theorem B3947651 : Blo 1752577 3947651 := bstep (se 1 (by rfl) ⟨2960738, by rfl⟩ : syracuseStep 3947651 = 5921477) B5921477
theorem B1973443 : Blo 1752577 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B2628881 : Blo 1752577 2628881 := bstep (se 2 (by rfl) ⟨985830, by rfl⟩ : syracuseStep 2628881 = 1971661) B1971661
theorem B56851733 : Blo 1752577 56851733 := bstep (se 6 (by rfl) ⟨1332462, by rfl⟩ : syracuseStep 56851733 = 2664925) B2664925
theorem B2628899 : Blo 1752577 2628899 := bstep (se 1 (by rfl) ⟨1971674, by rfl⟩ : syracuseStep 2628899 = 3943349) B3943349
theorem B5061923 : Blo 1752577 5061923 := bstep (se 1 (by rfl) ⟨3796442, by rfl⟩ : syracuseStep 5061923 = 7592885) B7592885
theorem B7486769 : Blo 1752577 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B2628929 : Blo 1752577 2628929 := bstep (se 2 (by rfl) ⟨985848, by rfl⟩ : syracuseStep 2628929 = 1971697) B1971697
theorem B2497873 : Blo 1752577 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B2628947 : Blo 1752577 2628947 := bstep (se 1 (by rfl) ⟨1971710, by rfl⟩ : syracuseStep 2628947 = 3943421) B3943421
theorem B1973587 : Blo 1752577 1973587 := bstep (se 1 (by rfl) ⟨1480190, by rfl⟩ : syracuseStep 1973587 = 2960381) B2960381
theorem B2628977 : Blo 1752577 2628977 := bstep (se 2 (by rfl) ⟨985866, by rfl⟩ : syracuseStep 2628977 = 1971733) B1971733
theorem B2628995 : Blo 1752577 2628995 := bstep (se 1 (by rfl) ⟨1971746, by rfl⟩ : syracuseStep 2628995 = 3943493) B3943493
theorem B2219395 : Blo 1752577 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B2629025 : Blo 1752577 2629025 := bstep (se 2 (by rfl) ⟨985884, by rfl⟩ : syracuseStep 2629025 = 1971769) B1971769
theorem B2629043 : Blo 1752577 2629043 := bstep (se 1 (by rfl) ⟨1971782, by rfl⟩ : syracuseStep 2629043 = 3943565) B3943565
theorem B2497987 : Blo 1752577 2497987 := bstep (se 1 (by rfl) ⟨1873490, by rfl⟩ : syracuseStep 2497987 = 3746981) B3746981
theorem B9985477 : Blo 1752577 9985477 := bstep (se 4 (by rfl) ⟨936138, by rfl⟩ : syracuseStep 9985477 = 1872277) B1872277
theorem B2629073 : Blo 1752577 2629073 := bstep (se 2 (by rfl) ⟨985902, by rfl⟩ : syracuseStep 2629073 = 1971805) B1971805
theorem B2629091 : Blo 1752577 2629091 := bstep (se 1 (by rfl) ⟨1971818, by rfl⟩ : syracuseStep 2629091 = 3943637) B3943637
theorem B2219491 : Blo 1752577 2219491 := bstep (se 1 (by rfl) ⟨1664618, by rfl⟩ : syracuseStep 2219491 = 3329237) B3329237
theorem B1973731 : Blo 1752577 1973731 := bstep (se 1 (by rfl) ⟨1480298, by rfl⟩ : syracuseStep 1973731 = 2960597) B2960597
theorem B2629121 : Blo 1752577 2629121 := bstep (se 2 (by rfl) ⟨985920, by rfl⟩ : syracuseStep 2629121 = 1971841) B1971841
theorem B1752579 : Blo 1752577 1752579 := bstep (se 1 (by rfl) ⟨1314434, by rfl⟩ : syracuseStep 1752579 = 2628869) B2628869
theorem B6659597 : Blo 1752577 6659597 := bstep (se 3 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 6659597 = 2497349) B2497349
theorem B4439569 : Blo 1752577 4439569 := bstep (se 2 (by rfl) ⟨1664838, by rfl⟩ : syracuseStep 4439569 = 3329677) B3329677
theorem B1752595 : Blo 1752577 1752595 := bstep (se 1 (by rfl) ⟨1314446, by rfl⟩ : syracuseStep 1752595 = 2628893) B2628893
theorem B2629139 : Blo 1752577 2629139 := bstep (se 1 (by rfl) ⟨1971854, by rfl⟩ : syracuseStep 2629139 = 3943709) B3943709
theorem B1752611 : Blo 1752577 1752611 := bstep (se 1 (by rfl) ⟨1314458, by rfl⟩ : syracuseStep 1752611 = 2628917) B2628917
theorem B2629169 : Blo 1752577 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B1752627 : Blo 1752577 1752627 := bstep (se 1 (by rfl) ⟨1314470, by rfl⟩ : syracuseStep 1752627 = 2628941) B2628941
theorem B1752643 : Blo 1752577 1752643 := bstep (se 1 (by rfl) ⟨1314482, by rfl⟩ : syracuseStep 1752643 = 2628965) B2628965
theorem B2629187 : Blo 1752577 2629187 := bstep (se 1 (by rfl) ⟨1971890, by rfl⟩ : syracuseStep 2629187 = 3943781) B3943781
theorem B1752659 : Blo 1752577 1752659 := bstep (se 1 (by rfl) ⟨1314494, by rfl⟩ : syracuseStep 1752659 = 2628989) B2628989
theorem B2629217 : Blo 1752577 2629217 := bstep (se 2 (by rfl) ⟨985956, by rfl⟩ : syracuseStep 2629217 = 1971913) B1971913
theorem B2809441 : Blo 1752577 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B1752675 : Blo 1752577 1752675 := bstep (se 1 (by rfl) ⟨1314506, by rfl⟩ : syracuseStep 1752675 = 2629013) B2629013
theorem B19971683 : Blo 1752577 19971683 := bstep (se 1 (by rfl) ⟨14978762, by rfl⟩ : syracuseStep 19971683 = 29957525) B29957525
theorem B1752691 : Blo 1752577 1752691 := bstep (se 1 (by rfl) ⟨1314518, by rfl⟩ : syracuseStep 1752691 = 2629037) B2629037
theorem B2629235 : Blo 1752577 2629235 := bstep (se 1 (by rfl) ⟨1971926, by rfl⟩ : syracuseStep 2629235 = 3943853) B3943853
theorem B1973875 : Blo 1752577 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B1752707 : Blo 1752577 1752707 := bstep (se 1 (by rfl) ⟨1314530, by rfl⟩ : syracuseStep 1752707 = 2629061) B2629061
theorem B2629265 : Blo 1752577 2629265 := bstep (se 2 (by rfl) ⟨985974, by rfl⟩ : syracuseStep 2629265 = 1971949) B1971949
theorem B1752723 : Blo 1752577 1752723 := bstep (se 1 (by rfl) ⟨1314542, by rfl⟩ : syracuseStep 1752723 = 2629085) B2629085
theorem B1752739 : Blo 1752577 1752739 := bstep (se 1 (by rfl) ⟨1314554, by rfl⟩ : syracuseStep 1752739 = 2629109) B2629109
theorem B2629283 : Blo 1752577 2629283 := bstep (se 1 (by rfl) ⟨1971962, by rfl⟩ : syracuseStep 2629283 = 3943925) B3943925
theorem B1752755 : Blo 1752577 1752755 := bstep (se 1 (by rfl) ⟨1314566, by rfl⟩ : syracuseStep 1752755 = 2629133) B2629133
theorem B2629313 : Blo 1752577 2629313 := bstep (se 2 (by rfl) ⟨985992, by rfl⟩ : syracuseStep 2629313 = 1971985) B1971985
theorem B1752771 : Blo 1752577 1752771 := bstep (se 1 (by rfl) ⟨1314578, by rfl⟩ : syracuseStep 1752771 = 2629157) B2629157
theorem B5619395 : Blo 1752577 5619395 := bstep (se 1 (by rfl) ⟨4214546, by rfl⟩ : syracuseStep 5619395 = 8429093) B8429093
theorem B1752787 : Blo 1752577 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B2629331 : Blo 1752577 2629331 := bstep (se 1 (by rfl) ⟨1971998, by rfl⟩ : syracuseStep 2629331 = 3943997) B3943997
theorem B1752803 : Blo 1752577 1752803 := bstep (se 1 (by rfl) ⟨1314602, by rfl⟩ : syracuseStep 1752803 = 2629205) B2629205
theorem B2629361 : Blo 1752577 2629361 := bstep (se 2 (by rfl) ⟨986010, by rfl⟩ : syracuseStep 2629361 = 1972021) B1972021
theorem B1752819 : Blo 1752577 1752819 := bstep (se 1 (by rfl) ⟨1314614, by rfl⟩ : syracuseStep 1752819 = 2629229) B2629229
theorem B1752835 : Blo 1752577 1752835 := bstep (se 1 (by rfl) ⟨1314626, by rfl⟩ : syracuseStep 1752835 = 2629253) B2629253
theorem B2629379 : Blo 1752577 2629379 := bstep (se 1 (by rfl) ⟨1972034, by rfl⟩ : syracuseStep 2629379 = 3944069) B3944069
theorem B1752851 : Blo 1752577 1752851 := bstep (se 1 (by rfl) ⟨1314638, by rfl⟩ : syracuseStep 1752851 = 2629277) B2629277
theorem B2629409 : Blo 1752577 2629409 := bstep (se 2 (by rfl) ⟨986028, by rfl⟩ : syracuseStep 2629409 = 1972057) B1972057
theorem B1752867 : Blo 1752577 1752867 := bstep (se 1 (by rfl) ⟨1314650, by rfl⟩ : syracuseStep 1752867 = 2629301) B2629301
theorem B4439843 : Blo 1752577 4439843 := bstep (se 1 (by rfl) ⟨3329882, by rfl⟩ : syracuseStep 4439843 = 6659765) B6659765
theorem B1752883 : Blo 1752577 1752883 := bstep (se 1 (by rfl) ⟨1314662, by rfl⟩ : syracuseStep 1752883 = 2629325) B2629325
theorem B2629427 : Blo 1752577 2629427 := bstep (se 1 (by rfl) ⟨1972070, by rfl⟩ : syracuseStep 2629427 = 3944141) B3944141
theorem B1752899 : Blo 1752577 1752899 := bstep (se 1 (by rfl) ⟨1314674, by rfl⟩ : syracuseStep 1752899 = 2629349) B2629349
theorem B2629457 : Blo 1752577 2629457 := bstep (se 2 (by rfl) ⟨986046, by rfl⟩ : syracuseStep 2629457 = 1972093) B1972093
theorem B1752915 : Blo 1752577 1752915 := bstep (se 1 (by rfl) ⟨1314686, by rfl⟩ : syracuseStep 1752915 = 2629373) B2629373
theorem B1752931 : Blo 1752577 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B2629475 : Blo 1752577 2629475 := bstep (se 1 (by rfl) ⟨1972106, by rfl⟩ : syracuseStep 2629475 = 3944213) B3944213
theorem B17080163 : Blo 1752577 17080163 := bstep (se 1 (by rfl) ⟨12810122, by rfl⟩ : syracuseStep 17080163 = 25620245) B25620245
theorem B1752947 : Blo 1752577 1752947 := bstep (se 1 (by rfl) ⟨1314710, by rfl⟩ : syracuseStep 1752947 = 2629421) B2629421
theorem B2629505 : Blo 1752577 2629505 := bstep (se 2 (by rfl) ⟨986064, by rfl⟩ : syracuseStep 2629505 = 1972129) B1972129
theorem B1752963 : Blo 1752577 1752963 := bstep (se 1 (by rfl) ⟨1314722, by rfl⟩ : syracuseStep 1752963 = 2629445) B2629445
theorem B4562819 : Blo 1752577 4562819 := bstep (se 1 (by rfl) ⟨3422114, by rfl⟩ : syracuseStep 4562819 = 6844229) B6844229
theorem B1752979 : Blo 1752577 1752979 := bstep (se 1 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 1752979 = 2629469) B2629469
theorem B2629523 : Blo 1752577 2629523 := bstep (se 1 (by rfl) ⟨1972142, by rfl⟩ : syracuseStep 2629523 = 3944285) B3944285
theorem B1752995 : Blo 1752577 1752995 := bstep (se 1 (by rfl) ⟨1314746, by rfl⟩ : syracuseStep 1752995 = 2629493) B2629493
theorem B1802147 : Blo 1752577 1802147 := bstep (se 1 (by rfl) ⟨1351610, by rfl⟩ : syracuseStep 1802147 = 2703221) B2703221
theorem B2629553 : Blo 1752577 2629553 := bstep (se 2 (by rfl) ⟨986082, by rfl⟩ : syracuseStep 2629553 = 1972165) B1972165
theorem B1753011 : Blo 1752577 1753011 := bstep (se 1 (by rfl) ⟨1314758, by rfl⟩ : syracuseStep 1753011 = 2629517) B2629517
theorem B1753027 : Blo 1752577 1753027 := bstep (se 1 (by rfl) ⟨1314770, by rfl⟩ : syracuseStep 1753027 = 2629541) B2629541
theorem B2629571 : Blo 1752577 2629571 := bstep (se 1 (by rfl) ⟨1972178, by rfl⟩ : syracuseStep 2629571 = 3944357) B3944357
theorem B1753043 : Blo 1752577 1753043 := bstep (se 1 (by rfl) ⟨1314782, by rfl⟩ : syracuseStep 1753043 = 2629565) B2629565
theorem B2219987 : Blo 1752577 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B2629601 : Blo 1752577 2629601 := bstep (se 2 (by rfl) ⟨986100, by rfl⟩ : syracuseStep 2629601 = 1972201) B1972201
theorem B1753059 : Blo 1752577 1753059 := bstep (se 1 (by rfl) ⟨1314794, by rfl⟩ : syracuseStep 1753059 = 2629589) B2629589
theorem B4440035 : Blo 1752577 4440035 := bstep (se 1 (by rfl) ⟨3330026, by rfl⟩ : syracuseStep 4440035 = 6660053) B6660053
theorem B17088497 : Blo 1752577 17088497 := bstep (se 2 (by rfl) ⟨6408186, by rfl⟩ : syracuseStep 17088497 = 12816373) B12816373
theorem B1753075 : Blo 1752577 1753075 := bstep (se 1 (by rfl) ⟨1314806, by rfl⟩ : syracuseStep 1753075 = 2629613) B2629613
theorem B2629619 : Blo 1752577 2629619 := bstep (se 1 (by rfl) ⟨1972214, by rfl⟩ : syracuseStep 2629619 = 3944429) B3944429
theorem B2629643 : Blo 1752577 2629643 := bstep (se 1 (by rfl) ⟨1972232, by rfl⟩ : syracuseStep 2629643 = 3944465) B3944465
theorem B1753099 : Blo 1752577 1753099 := bstep (se 1 (by rfl) ⟨1314824, by rfl⟩ : syracuseStep 1753099 = 2629649) B2629649
theorem B2220043 : Blo 1752577 2220043 := bstep (se 1 (by rfl) ⟨1665032, by rfl⟩ : syracuseStep 2220043 = 3330065) B3330065
theorem B2629655 : Blo 1752577 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B1753111 : Blo 1752577 1753111 := bstep (se 1 (by rfl) ⟨1314833, by rfl⟩ : syracuseStep 1753111 = 2629667) B2629667
theorem B1753131 : Blo 1752577 1753131 := bstep (se 1 (by rfl) ⟨1314848, by rfl⟩ : syracuseStep 1753131 = 2629697) B2629697
theorem B3743795 : Blo 1752577 3743795 := bstep (se 1 (by rfl) ⟨2807846, by rfl⟩ : syracuseStep 3743795 = 5615693) B5615693
theorem B1753143 : Blo 1752577 1753143 := bstep (se 1 (by rfl) ⟨1314857, by rfl⟩ : syracuseStep 1753143 = 2629715) B2629715
theorem B14213195 : Blo 1752577 14213195 := bstep (se 1 (by rfl) ⟨10659896, by rfl⟩ : syracuseStep 14213195 = 21319793) B21319793
theorem B1753163 : Blo 1752577 1753163 := bstep (se 1 (by rfl) ⟨1314872, by rfl⟩ : syracuseStep 1753163 = 2629745) B2629745
theorem B1753175 : Blo 1752577 1753175 := bstep (se 1 (by rfl) ⟨1314881, by rfl⟩ : syracuseStep 1753175 = 2629763) B2629763
theorem B2629721 : Blo 1752577 2629721 := bstep (se 2 (by rfl) ⟨986145, by rfl⟩ : syracuseStep 2629721 = 1972291) B1972291
theorem B1753195 : Blo 1752577 1753195 := bstep (se 1 (by rfl) ⟨1314896, by rfl⟩ : syracuseStep 1753195 = 2629793) B2629793
theorem B1753207 : Blo 1752577 1753207 := bstep (se 1 (by rfl) ⟨1314905, by rfl⟩ : syracuseStep 1753207 = 2629811) B2629811
theorem B1753227 : Blo 1752577 1753227 := bstep (se 1 (by rfl) ⟨1314920, by rfl⟩ : syracuseStep 1753227 = 2629841) B2629841
theorem B1753239 : Blo 1752577 1753239 := bstep (se 1 (by rfl) ⟨1314929, by rfl⟩ : syracuseStep 1753239 = 2629859) B2629859
theorem B1753259 : Blo 1752577 1753259 := bstep (se 1 (by rfl) ⟨1314944, by rfl⟩ : syracuseStep 1753259 = 2629889) B2629889
theorem B1753271 : Blo 1752577 1753271 := bstep (se 1 (by rfl) ⟨1314953, by rfl⟩ : syracuseStep 1753271 = 2629907) B2629907
theorem B2629835 : Blo 1752577 2629835 := bstep (se 1 (by rfl) ⟨1972376, by rfl⟩ : syracuseStep 2629835 = 3944753) B3944753
theorem B1753291 : Blo 1752577 1753291 := bstep (se 1 (by rfl) ⟨1314968, by rfl⟩ : syracuseStep 1753291 = 2629937) B2629937
theorem B2629847 : Blo 1752577 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B1753303 : Blo 1752577 1753303 := bstep (se 1 (by rfl) ⟨1314977, by rfl⟩ : syracuseStep 1753303 = 2629955) B2629955
theorem B1777879 : Blo 1752577 1777879 := bstep (se 1 (by rfl) ⟨1333409, by rfl⟩ : syracuseStep 1777879 = 2666819) B2666819
theorem B1753323 : Blo 1752577 1753323 := bstep (se 1 (by rfl) ⟨1314992, by rfl⟩ : syracuseStep 1753323 = 2629985) B2629985
theorem B1753335 : Blo 1752577 1753335 := bstep (se 1 (by rfl) ⟨1315001, by rfl⟩ : syracuseStep 1753335 = 2630003) B2630003
theorem B3203329 : Blo 1752577 3203329 := bstep (se 2 (by rfl) ⟨1201248, by rfl⟩ : syracuseStep 3203329 = 2402497) B2402497
theorem B1753355 : Blo 1752577 1753355 := bstep (se 1 (by rfl) ⟨1315016, by rfl⟩ : syracuseStep 1753355 = 2630033) B2630033
theorem B14410001 : Blo 1752577 14410001 := bstep (se 2 (by rfl) ⟨5403750, by rfl⟩ : syracuseStep 14410001 = 10807501) B10807501
theorem B1753367 : Blo 1752577 1753367 := bstep (se 1 (by rfl) ⟨1315025, by rfl⟩ : syracuseStep 1753367 = 2630051) B2630051
theorem B2220311 : Blo 1752577 2220311 := bstep (se 1 (by rfl) ⟨1665233, by rfl⟩ : syracuseStep 2220311 = 3330467) B3330467
theorem B2957593 : Blo 1752577 2957593 := bstep (se 2 (by rfl) ⟨1109097, by rfl⟩ : syracuseStep 2957593 = 2218195) B2218195
theorem B2629913 : Blo 1752577 2629913 := bstep (se 2 (by rfl) ⟨986217, by rfl⟩ : syracuseStep 2629913 = 1972435) B1972435
theorem B1753387 : Blo 1752577 1753387 := bstep (se 1 (by rfl) ⟨1315040, by rfl⟩ : syracuseStep 1753387 = 2630081) B2630081
theorem B1753399 : Blo 1752577 1753399 := bstep (se 1 (by rfl) ⟨1315049, by rfl⟩ : syracuseStep 1753399 = 2630099) B2630099
theorem B1753419 : Blo 1752577 1753419 := bstep (se 1 (by rfl) ⟨1315064, by rfl⟩ : syracuseStep 1753419 = 2630129) B2630129
theorem B1753431 : Blo 1752577 1753431 := bstep (se 1 (by rfl) ⟨1315073, by rfl⟩ : syracuseStep 1753431 = 2630147) B2630147
theorem B1753451 : Blo 1752577 1753451 := bstep (se 1 (by rfl) ⟨1315088, by rfl⟩ : syracuseStep 1753451 = 2630177) B2630177
theorem B1753463 : Blo 1752577 1753463 := bstep (se 1 (by rfl) ⟨1315097, by rfl⟩ : syracuseStep 1753463 = 2630195) B2630195
theorem B9986435 : Blo 1752577 9986435 := bstep (se 1 (by rfl) ⟨7489826, by rfl⟩ : syracuseStep 9986435 = 14979653) B14979653
theorem B7111043 : Blo 1752577 7111043 := bstep (se 1 (by rfl) ⟨5333282, by rfl⟩ : syracuseStep 7111043 = 10666565) B10666565
theorem B8880515 : Blo 1752577 8880515 := bstep (se 1 (by rfl) ⟨6660386, by rfl⟩ : syracuseStep 8880515 = 13320773) B13320773
theorem B2630027 : Blo 1752577 2630027 := bstep (se 1 (by rfl) ⟨1972520, by rfl⟩ : syracuseStep 2630027 = 3945041) B3945041
theorem B1753483 : Blo 1752577 1753483 := bstep (se 1 (by rfl) ⟨1315112, by rfl⟩ : syracuseStep 1753483 = 2630225) B2630225
theorem B2630039 : Blo 1752577 2630039 := bstep (se 1 (by rfl) ⟨1972529, by rfl⟩ : syracuseStep 2630039 = 3945059) B3945059
theorem B1753495 : Blo 1752577 1753495 := bstep (se 1 (by rfl) ⟨1315121, by rfl⟩ : syracuseStep 1753495 = 2630243) B2630243
theorem B1753515 : Blo 1752577 1753515 := bstep (se 1 (by rfl) ⟨1315136, by rfl⟩ : syracuseStep 1753515 = 2630273) B2630273
theorem B9478579 : Blo 1752577 9478579 := bstep (se 1 (by rfl) ⟨7108934, by rfl⟩ : syracuseStep 9478579 = 14217869) B14217869
theorem B1753527 : Blo 1752577 1753527 := bstep (se 1 (by rfl) ⟨1315145, by rfl⟩ : syracuseStep 1753527 = 2630291) B2630291
theorem B3334603 : Blo 1752577 3334603 := bstep (se 1 (by rfl) ⟨2500952, by rfl⟩ : syracuseStep 3334603 = 5001905) B5001905
theorem B1753547 : Blo 1752577 1753547 := bstep (se 1 (by rfl) ⟨1315160, by rfl⟩ : syracuseStep 1753547 = 2630321) B2630321
theorem B1753559 : Blo 1752577 1753559 := bstep (se 1 (by rfl) ⟨1315169, by rfl⟩ : syracuseStep 1753559 = 2630339) B2630339
theorem B2630105 : Blo 1752577 2630105 := bstep (se 2 (by rfl) ⟨986289, by rfl⟩ : syracuseStep 2630105 = 1972579) B1972579
theorem B6660569 : Blo 1752577 6660569 := bstep (se 2 (by rfl) ⟨2497713, by rfl⟩ : syracuseStep 6660569 = 4995427) B4995427
theorem B1753579 : Blo 1752577 1753579 := bstep (se 1 (by rfl) ⟨1315184, by rfl⟩ : syracuseStep 1753579 = 2630369) B2630369
theorem B1753591 : Blo 1752577 1753591 := bstep (se 1 (by rfl) ⟨1315193, by rfl⟩ : syracuseStep 1753591 = 2630387) B2630387
theorem B1753611 : Blo 1752577 1753611 := bstep (se 1 (by rfl) ⟨1315208, by rfl⟩ : syracuseStep 1753611 = 2630417) B2630417
theorem B5915159 : Blo 1752577 5915159 := bstep (se 1 (by rfl) ⟨4436369, by rfl⟩ : syracuseStep 5915159 = 8872739) B8872739
theorem B1753623 : Blo 1752577 1753623 := bstep (se 1 (by rfl) ⟨1315217, by rfl⟩ : syracuseStep 1753623 = 2630435) B2630435
theorem B3744281 : Blo 1752577 3744281 := bstep (se 2 (by rfl) ⟨1404105, by rfl⟩ : syracuseStep 3744281 = 2808211) B2808211
theorem B1753643 : Blo 1752577 1753643 := bstep (se 1 (by rfl) ⟨1315232, by rfl⟩ : syracuseStep 1753643 = 2630465) B2630465
theorem B6840877 : Blo 1752577 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B1753655 : Blo 1752577 1753655 := bstep (se 1 (by rfl) ⟨1315241, by rfl⟩ : syracuseStep 1753655 = 2630483) B2630483
theorem B2630219 : Blo 1752577 2630219 := bstep (se 1 (by rfl) ⟨1972664, by rfl⟩ : syracuseStep 2630219 = 3945329) B3945329
theorem B1753675 : Blo 1752577 1753675 := bstep (se 1 (by rfl) ⟨1315256, by rfl⟩ : syracuseStep 1753675 = 2630513) B2630513
theorem B2630231 : Blo 1752577 2630231 := bstep (se 1 (by rfl) ⟨1972673, by rfl⟩ : syracuseStep 2630231 = 3945347) B3945347
theorem B1753687 : Blo 1752577 1753687 := bstep (se 1 (by rfl) ⟨1315265, by rfl⟩ : syracuseStep 1753687 = 2630531) B2630531
theorem B1753707 : Blo 1752577 1753707 := bstep (se 1 (by rfl) ⟨1315280, by rfl⟩ : syracuseStep 1753707 = 2630561) B2630561
theorem B1753719 : Blo 1752577 1753719 := bstep (se 1 (by rfl) ⟨1315289, by rfl⟩ : syracuseStep 1753719 = 2630579) B2630579
theorem B8422019 : Blo 1752577 8422019 := bstep (se 1 (by rfl) ⟨6316514, by rfl⟩ : syracuseStep 8422019 = 12633029) B12633029
theorem B1753739 : Blo 1752577 1753739 := bstep (se 1 (by rfl) ⟨1315304, by rfl⟩ : syracuseStep 1753739 = 2630609) B2630609
theorem B1753751 : Blo 1752577 1753751 := bstep (se 1 (by rfl) ⟨1315313, by rfl⟩ : syracuseStep 1753751 = 2630627) B2630627
theorem B2630297 : Blo 1752577 2630297 := bstep (se 2 (by rfl) ⟨986361, by rfl⟩ : syracuseStep 2630297 = 1972723) B1972723
theorem B1753771 : Blo 1752577 1753771 := bstep (se 1 (by rfl) ⟨1315328, by rfl⟩ : syracuseStep 1753771 = 2630657) B2630657
theorem B1753783 : Blo 1752577 1753783 := bstep (se 1 (by rfl) ⟨1315337, by rfl⟩ : syracuseStep 1753783 = 2630675) B2630675
theorem B1753803 : Blo 1752577 1753803 := bstep (se 1 (by rfl) ⟨1315352, by rfl⟩ : syracuseStep 1753803 = 2630705) B2630705
theorem B1753815 : Blo 1752577 1753815 := bstep (se 1 (by rfl) ⟨1315361, by rfl⟩ : syracuseStep 1753815 = 2630723) B2630723
theorem B3556057 : Blo 1752577 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B1753835 : Blo 1752577 1753835 := bstep (se 1 (by rfl) ⟨1315376, by rfl⟩ : syracuseStep 1753835 = 2630753) B2630753
theorem B1753847 : Blo 1752577 1753847 := bstep (se 1 (by rfl) ⟨1315385, by rfl⟩ : syracuseStep 1753847 = 2630771) B2630771
theorem B2630411 : Blo 1752577 2630411 := bstep (se 1 (by rfl) ⟨1972808, by rfl⟩ : syracuseStep 2630411 = 3945617) B3945617
theorem B1753867 : Blo 1752577 1753867 := bstep (se 1 (by rfl) ⟨1315400, by rfl⟩ : syracuseStep 1753867 = 2630801) B2630801
theorem B2630423 : Blo 1752577 2630423 := bstep (se 1 (by rfl) ⟨1972817, by rfl⟩ : syracuseStep 2630423 = 3945635) B3945635
theorem B1753879 : Blo 1752577 1753879 := bstep (se 1 (by rfl) ⟨1315409, by rfl⟩ : syracuseStep 1753879 = 2630819) B2630819
theorem B1753899 : Blo 1752577 1753899 := bstep (se 1 (by rfl) ⟨1315424, by rfl⟩ : syracuseStep 1753899 = 2630849) B2630849
theorem B1753911 : Blo 1752577 1753911 := bstep (se 1 (by rfl) ⟨1315433, by rfl⟩ : syracuseStep 1753911 = 2630867) B2630867
theorem B1753931 : Blo 1752577 1753931 := bstep (se 1 (by rfl) ⟨1315448, by rfl⟩ : syracuseStep 1753931 = 2630897) B2630897
theorem B2958167 : Blo 1752577 2958167 := bstep (se 1 (by rfl) ⟨2218625, by rfl⟩ : syracuseStep 2958167 = 4437251) B4437251
theorem B1753943 : Blo 1752577 1753943 := bstep (se 1 (by rfl) ⟨1315457, by rfl⟩ : syracuseStep 1753943 = 2630915) B2630915
theorem B2630489 : Blo 1752577 2630489 := bstep (se 2 (by rfl) ⟨986433, by rfl⟩ : syracuseStep 2630489 = 1972867) B1972867
theorem B1753963 : Blo 1752577 1753963 := bstep (se 1 (by rfl) ⟨1315472, by rfl⟩ : syracuseStep 1753963 = 2630945) B2630945
theorem B1753975 : Blo 1752577 1753975 := bstep (se 1 (by rfl) ⟨1315481, by rfl⟩ : syracuseStep 1753975 = 2630963) B2630963
theorem B1753995 : Blo 1752577 1753995 := bstep (se 1 (by rfl) ⟨1315496, by rfl⟩ : syracuseStep 1753995 = 2630993) B2630993
theorem B1754007 : Blo 1752577 1754007 := bstep (se 1 (by rfl) ⟨1315505, by rfl⟩ : syracuseStep 1754007 = 2631011) B2631011
theorem B1754027 : Blo 1752577 1754027 := bstep (se 1 (by rfl) ⟨1315520, by rfl⟩ : syracuseStep 1754027 = 2631041) B2631041
theorem B1754039 : Blo 1752577 1754039 := bstep (se 1 (by rfl) ⟨1315529, by rfl⟩ : syracuseStep 1754039 = 2631059) B2631059
theorem B4498379 : Blo 1752577 4498379 := bstep (se 1 (by rfl) ⟨3373784, by rfl⟩ : syracuseStep 4498379 = 6747569) B6747569
theorem B2630603 : Blo 1752577 2630603 := bstep (se 1 (by rfl) ⟨1972952, by rfl⟩ : syracuseStep 2630603 = 3945905) B3945905
theorem B1754059 : Blo 1752577 1754059 := bstep (se 1 (by rfl) ⟨1315544, by rfl⟩ : syracuseStep 1754059 = 2631089) B2631089
theorem B2958295 : Blo 1752577 2958295 := bstep (se 1 (by rfl) ⟨2218721, by rfl⟩ : syracuseStep 2958295 = 4437443) B4437443
theorem B2630615 : Blo 1752577 2630615 := bstep (se 1 (by rfl) ⟨1972961, by rfl⟩ : syracuseStep 2630615 = 3945923) B3945923
theorem B1754071 : Blo 1752577 1754071 := bstep (se 1 (by rfl) ⟨1315553, by rfl⟩ : syracuseStep 1754071 = 2631107) B2631107
theorem B1754091 : Blo 1752577 1754091 := bstep (se 1 (by rfl) ⟨1315568, by rfl⟩ : syracuseStep 1754091 = 2631137) B2631137
theorem B1754103 : Blo 1752577 1754103 := bstep (se 1 (by rfl) ⟨1315577, by rfl⟩ : syracuseStep 1754103 = 2631155) B2631155
theorem B1754123 : Blo 1752577 1754123 := bstep (se 1 (by rfl) ⟨1315592, by rfl⟩ : syracuseStep 1754123 = 2631185) B2631185
theorem B1754135 : Blo 1752577 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B2630681 : Blo 1752577 2630681 := bstep (se 2 (by rfl) ⟨986505, by rfl⟩ : syracuseStep 2630681 = 1973011) B1973011
theorem B1754155 : Blo 1752577 1754155 := bstep (se 1 (by rfl) ⟨1315616, by rfl⟩ : syracuseStep 1754155 = 2631233) B2631233
theorem B5915699 : Blo 1752577 5915699 := bstep (se 1 (by rfl) ⟨4436774, by rfl⟩ : syracuseStep 5915699 = 8873549) B8873549
theorem B4441139 : Blo 1752577 4441139 := bstep (se 1 (by rfl) ⟨3330854, by rfl⟩ : syracuseStep 4441139 = 6661709) B6661709
theorem B1754167 : Blo 1752577 1754167 := bstep (se 1 (by rfl) ⟨1315625, by rfl⟩ : syracuseStep 1754167 = 2631251) B2631251
theorem B1754187 : Blo 1752577 1754187 := bstep (se 1 (by rfl) ⟨1315640, by rfl⟩ : syracuseStep 1754187 = 2631281) B2631281
theorem B1754199 : Blo 1752577 1754199 := bstep (se 1 (by rfl) ⟨1315649, by rfl⟩ : syracuseStep 1754199 = 2631299) B2631299
theorem B1754219 : Blo 1752577 1754219 := bstep (se 1 (by rfl) ⟨1315664, by rfl⟩ : syracuseStep 1754219 = 2631329) B2631329
theorem B1754231 : Blo 1752577 1754231 := bstep (se 1 (by rfl) ⟨1315673, by rfl⟩ : syracuseStep 1754231 = 2631347) B2631347
theorem B2630795 : Blo 1752577 2630795 := bstep (se 1 (by rfl) ⟨1973096, by rfl⟩ : syracuseStep 2630795 = 3946193) B3946193
theorem B1754251 : Blo 1752577 1754251 := bstep (se 1 (by rfl) ⟨1315688, by rfl⟩ : syracuseStep 1754251 = 2631377) B2631377
theorem B2630807 : Blo 1752577 2630807 := bstep (se 1 (by rfl) ⟨1973105, by rfl⟩ : syracuseStep 2630807 = 3946211) B3946211
theorem B1754263 : Blo 1752577 1754263 := bstep (se 1 (by rfl) ⟨1315697, by rfl⟩ : syracuseStep 1754263 = 2631395) B2631395
theorem B1754283 : Blo 1752577 1754283 := bstep (se 1 (by rfl) ⟨1315712, by rfl⟩ : syracuseStep 1754283 = 2631425) B2631425
theorem B3376307 : Blo 1752577 3376307 := bstep (se 1 (by rfl) ⟨2532230, by rfl⟩ : syracuseStep 3376307 = 5064461) B5064461
theorem B1754295 : Blo 1752577 1754295 := bstep (se 1 (by rfl) ⟨1315721, by rfl⟩ : syracuseStep 1754295 = 2631443) B2631443
theorem B1754315 : Blo 1752577 1754315 := bstep (se 1 (by rfl) ⟨1315736, by rfl⟩ : syracuseStep 1754315 = 2631473) B2631473
theorem B1754327 : Blo 1752577 1754327 := bstep (se 1 (by rfl) ⟨1315745, by rfl⟩ : syracuseStep 1754327 = 2631491) B2631491
theorem B2630873 : Blo 1752577 2630873 := bstep (se 2 (by rfl) ⟨986577, by rfl⟩ : syracuseStep 2630873 = 1973155) B1973155
theorem B7488733 : Blo 1752577 7488733 := bstep (se 3 (by rfl) ⟨1404137, by rfl⟩ : syracuseStep 7488733 = 2808275) B2808275
theorem B1754347 : Blo 1752577 1754347 := bstep (se 1 (by rfl) ⟨1315760, by rfl⟩ : syracuseStep 1754347 = 2631521) B2631521
theorem B1754359 : Blo 1752577 1754359 := bstep (se 1 (by rfl) ⟨1315769, by rfl⟩ : syracuseStep 1754359 = 2631539) B2631539
theorem B3745025 : Blo 1752577 3745025 := bstep (se 2 (by rfl) ⟨1404384, by rfl⟩ : syracuseStep 3745025 = 2808769) B2808769
theorem B1754379 : Blo 1752577 1754379 := bstep (se 1 (by rfl) ⟨1315784, by rfl⟩ : syracuseStep 1754379 = 2631569) B2631569
theorem B1754391 : Blo 1752577 1754391 := bstep (se 1 (by rfl) ⟨1315793, by rfl⟩ : syracuseStep 1754391 = 2631587) B2631587
theorem B1754411 : Blo 1752577 1754411 := bstep (se 1 (by rfl) ⟨1315808, by rfl⟩ : syracuseStep 1754411 = 2631617) B2631617
theorem B1754423 : Blo 1752577 1754423 := bstep (se 1 (by rfl) ⟨1315817, by rfl⟩ : syracuseStep 1754423 = 2631635) B2631635
theorem B5915969 : Blo 1752577 5915969 := bstep (se 2 (by rfl) ⟨2218488, by rfl⟩ : syracuseStep 5915969 = 4436977) B4436977
theorem B2630987 : Blo 1752577 2630987 := bstep (se 1 (by rfl) ⟨1973240, by rfl⟩ : syracuseStep 2630987 = 3946481) B3946481
theorem B1754443 : Blo 1752577 1754443 := bstep (se 1 (by rfl) ⟨1315832, by rfl⟩ : syracuseStep 1754443 = 2631665) B2631665
theorem B2630999 : Blo 1752577 2630999 := bstep (se 1 (by rfl) ⟨1973249, by rfl⟩ : syracuseStep 2630999 = 3946499) B3946499
theorem B1754455 : Blo 1752577 1754455 := bstep (se 1 (by rfl) ⟨1315841, by rfl⟩ : syracuseStep 1754455 = 2631683) B2631683
theorem B4498777 : Blo 1752577 4498777 := bstep (se 2 (by rfl) ⟨1687041, by rfl⟩ : syracuseStep 4498777 = 3374083) B3374083
theorem B1754475 : Blo 1752577 1754475 := bstep (se 1 (by rfl) ⟨1315856, by rfl⟩ : syracuseStep 1754475 = 2631713) B2631713
theorem B1754487 : Blo 1752577 1754487 := bstep (se 1 (by rfl) ⟨1315865, by rfl⟩ : syracuseStep 1754487 = 2631731) B2631731
theorem B8422787 : Blo 1752577 8422787 := bstep (se 1 (by rfl) ⟨6317090, by rfl⟩ : syracuseStep 8422787 = 12634181) B12634181
theorem B15181187 : Blo 1752577 15181187 := bstep (se 1 (by rfl) ⟨11385890, by rfl⟩ : syracuseStep 15181187 = 22771781) B22771781
theorem B6751619 : Blo 1752577 6751619 := bstep (se 1 (by rfl) ⟨5063714, by rfl⟩ : syracuseStep 6751619 = 10127429) B10127429
theorem B1754507 : Blo 1752577 1754507 := bstep (se 1 (by rfl) ⟨1315880, by rfl⟩ : syracuseStep 1754507 = 2631761) B2631761
theorem B1754519 : Blo 1752577 1754519 := bstep (se 1 (by rfl) ⟨1315889, by rfl⟩ : syracuseStep 1754519 = 2631779) B2631779
theorem B2631065 : Blo 1752577 2631065 := bstep (se 2 (by rfl) ⟨986649, by rfl⟩ : syracuseStep 2631065 = 1973299) B1973299
theorem B1754539 : Blo 1752577 1754539 := bstep (se 1 (by rfl) ⟨1315904, by rfl⟩ : syracuseStep 1754539 = 2631809) B2631809
theorem B1754551 : Blo 1752577 1754551 := bstep (se 1 (by rfl) ⟨1315913, by rfl⟩ : syracuseStep 1754551 = 2631827) B2631827
theorem B1754571 : Blo 1752577 1754571 := bstep (se 1 (by rfl) ⟨1315928, by rfl⟩ : syracuseStep 1754571 = 2631857) B2631857
theorem B3327475 : Blo 1752577 3327475 := bstep (se 1 (by rfl) ⟨2495606, by rfl⟩ : syracuseStep 3327475 = 4991213) B4991213
theorem B2631179 : Blo 1752577 2631179 := bstep (se 1 (by rfl) ⟨1973384, by rfl⟩ : syracuseStep 2631179 = 3946769) B3946769
theorem B13321745 : Blo 1752577 13321745 := bstep (se 2 (by rfl) ⟨4995654, by rfl⟩ : syracuseStep 13321745 = 9991309) B9991309
theorem B2631191 : Blo 1752577 2631191 := bstep (se 1 (by rfl) ⟨1973393, by rfl⟩ : syracuseStep 2631191 = 3946787) B3946787
theorem B2958923 : Blo 1752577 2958923 := bstep (se 1 (by rfl) ⟨2219192, by rfl⟩ : syracuseStep 2958923 = 4438385) B4438385
theorem B2631257 : Blo 1752577 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B18966109 : Blo 1752577 18966109 := bstep (se 3 (by rfl) ⟨3556145, by rfl⟩ : syracuseStep 18966109 = 7112291) B7112291
theorem B25282199 : Blo 1752577 25282199 := bstep (se 1 (by rfl) ⟨18961649, by rfl⟩ : syracuseStep 25282199 = 37923299) B37923299
theorem B2959051 : Blo 1752577 2959051 := bstep (se 1 (by rfl) ⟨2219288, by rfl⟩ : syracuseStep 2959051 = 4438577) B4438577
theorem B2631371 : Blo 1752577 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B2631383 : Blo 1752577 2631383 := bstep (se 1 (by rfl) ⟨1973537, by rfl⟩ : syracuseStep 2631383 = 3947075) B3947075
theorem B2279179 : Blo 1752577 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B2631449 : Blo 1752577 2631449 := bstep (se 2 (by rfl) ⟨986793, by rfl⟩ : syracuseStep 2631449 = 1973587) B1973587
theorem B2959193 : Blo 1752577 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B5916509 : Blo 1752577 5916509 := bstep (se 3 (by rfl) ⟨1109345, by rfl⟩ : syracuseStep 5916509 = 2218691) B2218691
theorem B14215013 : Blo 1752577 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B2631563 : Blo 1752577 2631563 := bstep (se 1 (by rfl) ⟨1973672, by rfl⟩ : syracuseStep 2631563 = 3947345) B3947345
theorem B4990871 : Blo 1752577 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B2631575 : Blo 1752577 2631575 := bstep (se 1 (by rfl) ⟨1973681, by rfl⟩ : syracuseStep 2631575 = 3947363) B3947363
theorem B13313969 : Blo 1752577 13313969 := bstep (se 2 (by rfl) ⟨4992738, by rfl⟩ : syracuseStep 13313969 = 9985477) B9985477
theorem B12642227 : Blo 1752577 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B3327961 : Blo 1752577 3327961 := bstep (se 2 (by rfl) ⟨1247985, by rfl⟩ : syracuseStep 3327961 = 2495971) B2495971
theorem B2959321 : Blo 1752577 2959321 := bstep (se 2 (by rfl) ⟨1109745, by rfl⟩ : syracuseStep 2959321 = 2219491) B2219491
theorem B2631641 : Blo 1752577 2631641 := bstep (se 2 (by rfl) ⟨986865, by rfl⟩ : syracuseStep 2631641 = 1973731) B1973731
theorem B54716485 : Blo 1752577 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B2631755 : Blo 1752577 2631755 := bstep (se 1 (by rfl) ⟨1973816, by rfl⟩ : syracuseStep 2631755 = 3947633) B3947633
theorem B2631767 : Blo 1752577 2631767 := bstep (se 1 (by rfl) ⟨1973825, by rfl⟩ : syracuseStep 2631767 = 3947651) B3947651
theorem B3745921 : Blo 1752577 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B2631833 : Blo 1752577 2631833 := bstep (se 2 (by rfl) ⟨986937, by rfl⟩ : syracuseStep 2631833 = 1973875) B1973875
theorem B4991179 : Blo 1752577 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B13314455 : Blo 1752577 13314455 := bstep (se 1 (by rfl) ⟨9985841, by rfl⟩ : syracuseStep 13314455 = 19971683) B19971683
theorem B17090995 : Blo 1752577 17090995 := bstep (se 1 (by rfl) ⟨12818246, by rfl⟩ : syracuseStep 17090995 = 25636493) B25636493
theorem B3746263 : Blo 1752577 3746263 := bstep (se 1 (by rfl) ⟨2809697, by rfl⟩ : syracuseStep 3746263 = 5619395) B5619395
theorem B14223833 : Blo 1752577 14223833 := bstep (se 2 (by rfl) ⟨5333937, by rfl⟩ : syracuseStep 14223833 = 10667875) B10667875
theorem B4991453 : Blo 1752577 4991453 := bstep (se 3 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 4991453 = 1871795) B1871795
theorem B3328523 : Blo 1752577 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B7490065 : Blo 1752577 7490065 := bstep (se 2 (by rfl) ⟨2808774, by rfl⟩ : syracuseStep 7490065 = 5617549) B5617549
theorem B2959895 : Blo 1752577 2959895 := bstep (se 1 (by rfl) ⟨2219921, by rfl⟩ : syracuseStep 2959895 = 4439843) B4439843
theorem B3041879 : Blo 1752577 3041879 := bstep (se 1 (by rfl) ⟨2281409, by rfl⟩ : syracuseStep 3041879 = 4562819) B4562819
theorem B2960023 : Blo 1752577 2960023 := bstep (se 1 (by rfl) ⟨2220017, by rfl⟩ : syracuseStep 2960023 = 4440035) B4440035
theorem B3328705 : Blo 1752577 3328705 := bstep (se 2 (by rfl) ⟨1248264, by rfl⟩ : syracuseStep 3328705 = 2496529) B2496529
theorem B6318809 : Blo 1752577 6318809 := bstep (se 2 (by rfl) ⟨2369553, by rfl⟩ : syracuseStep 6318809 = 4739107) B4739107
theorem B6654737 : Blo 1752577 6654737 := bstep (se 2 (by rfl) ⟨2495526, by rfl⟩ : syracuseStep 6654737 = 4991053) B4991053
theorem B8874845 : Blo 1752577 8874845 := bstep (se 3 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 8874845 = 3328067) B3328067
theorem B14977943 : Blo 1752577 14977943 := bstep (se 1 (by rfl) ⟨11233457, by rfl⟩ : syracuseStep 14977943 = 22466915) B22466915
theorem B28437425 : Blo 1752577 28437425 := bstep (se 2 (by rfl) ⟨10664034, by rfl⟩ : syracuseStep 28437425 = 21328069) B21328069
theorem B5917643 : Blo 1752577 5917643 := bstep (se 1 (by rfl) ⟨4438232, by rfl⟩ : syracuseStep 5917643 = 8876465) B8876465
theorem B3943385 : Blo 1752577 3943385 := bstep (se 2 (by rfl) ⟨1478769, by rfl⟩ : syracuseStep 3943385 = 2957539) B2957539
theorem B3746827 : Blo 1752577 3746827 := bstep (se 1 (by rfl) ⟨2810120, by rfl⟩ : syracuseStep 3746827 = 5620241) B5620241
theorem B3943475 : Blo 1752577 3943475 := bstep (se 1 (by rfl) ⟨2957606, by rfl⟩ : syracuseStep 3943475 = 5915213) B5915213
theorem B12807233 : Blo 1752577 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B5614667 : Blo 1752577 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B3943511 : Blo 1752577 3943511 := bstep (se 1 (by rfl) ⟨2957633, by rfl⟩ : syracuseStep 3943511 = 5915267) B5915267
theorem B14986417 : Blo 1752577 14986417 := bstep (se 2 (by rfl) ⟨5619906, by rfl⟩ : syracuseStep 14986417 = 11239813) B11239813
theorem B11234483 : Blo 1752577 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B6655193 : Blo 1752577 6655193 := bstep (se 2 (by rfl) ⟨2495697, by rfl⟩ : syracuseStep 6655193 = 4991395) B4991395
theorem B5917913 : Blo 1752577 5917913 := bstep (se 2 (by rfl) ⟨2219217, by rfl⟩ : syracuseStep 5917913 = 4438435) B4438435
theorem B205090019 : Blo 1752577 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B3943691 : Blo 1752577 3943691 := bstep (se 1 (by rfl) ⟨2957768, by rfl⟩ : syracuseStep 3943691 = 5915537) B5915537
theorem B2960651 : Blo 1752577 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B9481517 : Blo 1752577 9481517 := bstep (se 3 (by rfl) ⟨1777784, by rfl⟩ : syracuseStep 9481517 = 3555569) B3555569
theorem B3943745 : Blo 1752577 3943745 := bstep (se 2 (by rfl) ⟨1478904, by rfl⟩ : syracuseStep 3943745 = 2957809) B2957809
theorem B28429633 : Blo 1752577 28429633 := bstep (se 2 (by rfl) ⟨10661112, by rfl⟩ : syracuseStep 28429633 = 21322225) B21322225
theorem B8424769 : Blo 1752577 8424769 := bstep (se 2 (by rfl) ⟨3159288, by rfl⟩ : syracuseStep 8424769 = 6318577) B6318577
theorem B3329419 : Blo 1752577 3329419 := bstep (se 1 (by rfl) ⟨2497064, by rfl⟩ : syracuseStep 3329419 = 4994129) B4994129
theorem B2960779 : Blo 1752577 2960779 := bstep (se 1 (by rfl) ⟨2220584, by rfl⟩ : syracuseStep 2960779 = 4441169) B4441169
theorem B4001177 : Blo 1752577 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B6655405 : Blo 1752577 6655405 := bstep (se 3 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 6655405 = 2495777) B2495777
theorem B3329495 : Blo 1752577 3329495 := bstep (se 1 (by rfl) ⟨2497121, by rfl⟩ : syracuseStep 3329495 = 4994243) B4994243
theorem B2026999 : Blo 1752577 2026999 := bstep (se 1 (by rfl) ⟨1520249, by rfl⟩ : syracuseStep 2026999 = 3040499) B3040499
theorem B3943961 : Blo 1752577 3943961 := bstep (se 2 (by rfl) ⟨1478985, by rfl⟩ : syracuseStep 3943961 = 2957971) B2957971
theorem B3944051 : Blo 1752577 3944051 := bstep (se 1 (by rfl) ⟨2958038, by rfl⟩ : syracuseStep 3944051 = 5916077) B5916077
theorem B3944087 : Blo 1752577 3944087 := bstep (se 1 (by rfl) ⟨2958065, by rfl⟩ : syracuseStep 3944087 = 5916131) B5916131
theorem B6655709 : Blo 1752577 6655709 := bstep (se 3 (by rfl) ⟨1247945, by rfl⟩ : syracuseStep 6655709 = 2495891) B2495891
theorem B3944267 : Blo 1752577 3944267 := bstep (se 1 (by rfl) ⟨2958200, by rfl⟩ : syracuseStep 3944267 = 5916401) B5916401
theorem B3944321 : Blo 1752577 3944321 := bstep (se 2 (by rfl) ⟨1479120, by rfl⟩ : syracuseStep 3944321 = 2958241) B2958241
theorem B5918615 : Blo 1752577 5918615 := bstep (se 1 (by rfl) ⟨4438961, by rfl⟩ : syracuseStep 5918615 = 8877923) B8877923
theorem B3944537 : Blo 1752577 3944537 := bstep (se 2 (by rfl) ⟨1479201, by rfl⟩ : syracuseStep 3944537 = 2958403) B2958403
theorem B7999577 : Blo 1752577 7999577 := bstep (se 2 (by rfl) ⟨2999841, by rfl⟩ : syracuseStep 7999577 = 5999683) B5999683
theorem B4214873 : Blo 1752577 4214873 := bstep (se 2 (by rfl) ⟨1580577, by rfl⟩ : syracuseStep 4214873 = 3161155) B3161155
theorem B3330163 : Blo 1752577 3330163 := bstep (se 1 (by rfl) ⟨2497622, by rfl⟩ : syracuseStep 3330163 = 4995245) B4995245
theorem B88871053 : Blo 1752577 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B3944627 : Blo 1752577 3944627 := bstep (se 1 (by rfl) ⟨2958470, by rfl⟩ : syracuseStep 3944627 = 5916941) B5916941
theorem B1872055 : Blo 1752577 1872055 := bstep (se 1 (by rfl) ⟨1404041, by rfl⟩ : syracuseStep 1872055 = 2808083) B2808083
theorem B3944663 : Blo 1752577 3944663 := bstep (se 1 (by rfl) ⟨2958497, by rfl⟩ : syracuseStep 3944663 = 5916995) B5916995
theorem B3330391 : Blo 1752577 3330391 := bstep (se 1 (by rfl) ⟨2497793, by rfl⟩ : syracuseStep 3330391 = 4995587) B4995587
theorem B25268597 : Blo 1752577 25268597 := bstep (se 5 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 25268597 = 2368931) B2368931
theorem B3944843 : Blo 1752577 3944843 := bstep (se 1 (by rfl) ⟨2958632, by rfl⟩ : syracuseStep 3944843 = 5917265) B5917265
theorem B5919155 : Blo 1752577 5919155 := bstep (se 1 (by rfl) ⟨4439366, by rfl⟩ : syracuseStep 5919155 = 8878733) B8878733
theorem B3944897 : Blo 1752577 3944897 := bstep (se 2 (by rfl) ⟨1479336, by rfl⟩ : syracuseStep 3944897 = 2958673) B2958673
theorem B3330497 : Blo 1752577 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B4436441 : Blo 1752577 4436441 := bstep (se 2 (by rfl) ⟨1663665, by rfl⟩ : syracuseStep 4436441 = 3327331) B3327331
theorem B4993559 : Blo 1752577 4993559 := bstep (se 1 (by rfl) ⟨3745169, by rfl⟩ : syracuseStep 4993559 = 7490339) B7490339
theorem B3330649 : Blo 1752577 3330649 := bstep (se 2 (by rfl) ⟨1248993, by rfl⟩ : syracuseStep 3330649 = 2497987) B2497987
theorem B3945113 : Blo 1752577 3945113 := bstep (se 2 (by rfl) ⟨1479417, by rfl⟩ : syracuseStep 3945113 = 2958835) B2958835
theorem B5616307 : Blo 1752577 5616307 := bstep (se 1 (by rfl) ⟨4212230, by rfl⟩ : syracuseStep 5616307 = 8424461) B8424461
theorem B5919425 : Blo 1752577 5919425 := bstep (se 2 (by rfl) ⟨2219784, by rfl⟩ : syracuseStep 5919425 = 4439569) B4439569
theorem B6746827 : Blo 1752577 6746827 := bstep (se 1 (by rfl) ⟨5060120, by rfl⟩ : syracuseStep 6746827 = 10120241) B10120241
theorem B3945203 : Blo 1752577 3945203 := bstep (se 1 (by rfl) ⟨2958902, by rfl⟩ : syracuseStep 3945203 = 5917805) B5917805
theorem B3945239 : Blo 1752577 3945239 := bstep (se 1 (by rfl) ⟨2958929, by rfl⟩ : syracuseStep 3945239 = 5917859) B5917859
theorem B5616449 : Blo 1752577 5616449 := bstep (se 2 (by rfl) ⟨2106168, by rfl⟩ : syracuseStep 5616449 = 4212337) B4212337
theorem B37901155 : Blo 1752577 37901155 := bstep (se 1 (by rfl) ⟨28425866, by rfl⟩ : syracuseStep 37901155 = 56851733) B56851733
theorem B8876951 : Blo 1752577 8876951 := bstep (se 1 (by rfl) ⟨6657713, by rfl⟩ : syracuseStep 8876951 = 13315427) B13315427
theorem B3945419 : Blo 1752577 3945419 := bstep (se 1 (by rfl) ⟨2959064, by rfl⟩ : syracuseStep 3945419 = 5918129) B5918129
theorem B3945473 : Blo 1752577 3945473 := bstep (se 2 (by rfl) ⟨1479552, by rfl⟩ : syracuseStep 3945473 = 2959105) B2959105
theorem B4805725 : Blo 1752577 4805725 := bstep (se 3 (by rfl) ⟨901073, by rfl⟩ : syracuseStep 4805725 = 1802147) B1802147
theorem B3945689 : Blo 1752577 3945689 := bstep (se 2 (by rfl) ⟨1479633, by rfl⟩ : syracuseStep 3945689 = 2959267) B2959267
theorem B5919965 : Blo 1752577 5919965 := bstep (se 3 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 5919965 = 2219987) B2219987
theorem B3945779 : Blo 1752577 3945779 := bstep (se 1 (by rfl) ⟨2959334, by rfl⟩ : syracuseStep 3945779 = 5918669) B5918669
theorem B4994369 : Blo 1752577 4994369 := bstep (se 2 (by rfl) ⟨1872888, by rfl⟩ : syracuseStep 4994369 = 3745777) B3745777
theorem B6321473 : Blo 1752577 6321473 := bstep (se 2 (by rfl) ⟨2370552, by rfl⟩ : syracuseStep 6321473 = 4741105) B4741105
theorem B11392331 : Blo 1752577 11392331 := bstep (se 1 (by rfl) ⟨8544248, by rfl⟩ : syracuseStep 11392331 = 17088497) B17088497
theorem B3945815 : Blo 1752577 3945815 := bstep (se 1 (by rfl) ⟨2959361, by rfl⟩ : syracuseStep 3945815 = 5918723) B5918723
theorem B22467941 : Blo 1752577 22467941 := bstep (se 4 (by rfl) ⟨2106369, by rfl⟩ : syracuseStep 22467941 = 4212739) B4212739
theorem B7108013 : Blo 1752577 7108013 := bstep (se 3 (by rfl) ⟨1332752, by rfl⟩ : syracuseStep 7108013 = 2665505) B2665505
theorem B7493057 : Blo 1752577 7493057 := bstep (se 2 (by rfl) ⟨2809896, by rfl⟩ : syracuseStep 7493057 = 5619793) B5619793
theorem B3945995 : Blo 1752577 3945995 := bstep (se 1 (by rfl) ⟨2959496, by rfl⟩ : syracuseStep 3945995 = 5918993) B5918993
theorem B3159577 : Blo 1752577 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B3946049 : Blo 1752577 3946049 := bstep (se 2 (by rfl) ⟨1479768, by rfl⟩ : syracuseStep 3946049 = 2959537) B2959537
theorem B1971787 : Blo 1752577 1971787 := bstep (se 1 (by rfl) ⟨1478840, by rfl⟩ : syracuseStep 1971787 = 2957681) B2957681
theorem B1971895 : Blo 1752577 1971895 := bstep (se 1 (by rfl) ⟨1478921, by rfl⟩ : syracuseStep 1971895 = 2957843) B2957843
theorem B3946265 : Blo 1752577 3946265 := bstep (se 2 (by rfl) ⟨1479849, by rfl⟩ : syracuseStep 3946265 = 2959699) B2959699
theorem B9983837 : Blo 1752577 9983837 := bstep (se 3 (by rfl) ⟨1871969, by rfl⟩ : syracuseStep 9983837 = 3743939) B3743939
theorem B1972075 : Blo 1752577 1972075 := bstep (se 1 (by rfl) ⟨1479056, by rfl⟩ : syracuseStep 1972075 = 2958113) B2958113
theorem B3946355 : Blo 1752577 3946355 := bstep (se 1 (by rfl) ⟨2959766, by rfl⟩ : syracuseStep 3946355 = 5919533) B5919533
theorem B11237251 : Blo 1752577 11237251 := bstep (se 1 (by rfl) ⟨8427938, by rfl⟩ : syracuseStep 11237251 = 16855877) B16855877
theorem B8107921 : Blo 1752577 8107921 := bstep (se 2 (by rfl) ⟨3040470, by rfl⟩ : syracuseStep 8107921 = 6080941) B6080941
theorem B3946391 : Blo 1752577 3946391 := bstep (se 1 (by rfl) ⟨2959793, by rfl⟩ : syracuseStep 3946391 = 5919587) B5919587
theorem B4052929 : Blo 1752577 4052929 := bstep (se 2 (by rfl) ⟨1519848, by rfl⟩ : syracuseStep 4052929 = 3039697) B3039697
theorem B1972183 : Blo 1752577 1972183 := bstep (se 1 (by rfl) ⟨1479137, by rfl⟩ : syracuseStep 1972183 = 2958275) B2958275
theorem B4438091 : Blo 1752577 4438091 := bstep (se 1 (by rfl) ⟨3328568, by rfl⟩ : syracuseStep 4438091 = 6657137) B6657137
theorem B3946571 : Blo 1752577 3946571 := bstep (se 1 (by rfl) ⟨2959928, by rfl⟩ : syracuseStep 3946571 = 5919857) B5919857
theorem B9992267 : Blo 1752577 9992267 := bstep (se 1 (by rfl) ⟨7494200, by rfl⟩ : syracuseStep 9992267 = 14988401) B14988401
theorem B3946625 : Blo 1752577 3946625 := bstep (se 2 (by rfl) ⟨1479984, by rfl⟩ : syracuseStep 3946625 = 2959969) B2959969
theorem B1972363 : Blo 1752577 1972363 := bstep (se 1 (by rfl) ⟨1479272, by rfl⟩ : syracuseStep 1972363 = 2958545) B2958545
theorem B1972471 : Blo 1752577 1972471 := bstep (se 1 (by rfl) ⟨1479353, by rfl⟩ : syracuseStep 1972471 = 2958707) B2958707
theorem B6658307 : Blo 1752577 6658307 := bstep (se 1 (by rfl) ⟨4993730, by rfl⟩ : syracuseStep 6658307 = 9987461) B9987461
theorem B6658321 : Blo 1752577 6658321 := bstep (se 2 (by rfl) ⟨2496870, by rfl⟩ : syracuseStep 6658321 = 4993741) B4993741
theorem B2496791 : Blo 1752577 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B5921099 : Blo 1752577 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B3553625 : Blo 1752577 3553625 := bstep (se 2 (by rfl) ⟨1332609, by rfl⟩ : syracuseStep 3553625 = 2665219) B2665219
theorem B3946841 : Blo 1752577 3946841 := bstep (se 2 (by rfl) ⟨1480065, by rfl⟩ : syracuseStep 3946841 = 2960131) B2960131
theorem B1972651 : Blo 1752577 1972651 := bstep (se 1 (by rfl) ⟨1479488, by rfl⟩ : syracuseStep 1972651 = 2958977) B2958977
theorem B3946931 : Blo 1752577 3946931 := bstep (se 1 (by rfl) ⟨2960198, by rfl⟩ : syracuseStep 3946931 = 5920397) B5920397
theorem B3946967 : Blo 1752577 3946967 := bstep (se 1 (by rfl) ⟨2960225, by rfl⟩ : syracuseStep 3946967 = 5920451) B5920451
theorem B2218519 : Blo 1752577 2218519 := bstep (se 1 (by rfl) ⟨1663889, by rfl⟩ : syracuseStep 2218519 = 3327779) B3327779
theorem B1972759 : Blo 1752577 1972759 := bstep (se 1 (by rfl) ⟨1479569, by rfl⟩ : syracuseStep 1972759 = 2959139) B2959139
theorem B6658625 : Blo 1752577 6658625 := bstep (se 2 (by rfl) ⟨2496984, by rfl⟩ : syracuseStep 6658625 = 4993969) B4993969
theorem B5921369 : Blo 1752577 5921369 := bstep (se 2 (by rfl) ⟨2220513, by rfl⟩ : syracuseStep 5921369 = 4441027) B4441027
theorem B3947147 : Blo 1752577 3947147 := bstep (se 1 (by rfl) ⟨2960360, by rfl⟩ : syracuseStep 3947147 = 5920721) B5920721
theorem B5618369 : Blo 1752577 5618369 := bstep (se 2 (by rfl) ⟨2106888, by rfl⟩ : syracuseStep 5618369 = 4213777) B4213777
theorem B3947201 : Blo 1752577 3947201 := bstep (se 2 (by rfl) ⟨1480200, by rfl⟩ : syracuseStep 3947201 = 2960401) B2960401
theorem B1972939 : Blo 1752577 1972939 := bstep (se 1 (by rfl) ⟨1479704, by rfl⟩ : syracuseStep 1972939 = 2959409) B2959409
theorem B1973047 : Blo 1752577 1973047 := bstep (se 1 (by rfl) ⟨1479785, by rfl⟩ : syracuseStep 1973047 = 2959571) B2959571
theorem B54745955 : Blo 1752577 54745955 := bstep (se 1 (by rfl) ⟨41059466, by rfl⟩ : syracuseStep 54745955 = 82118933) B82118933
theorem B3947417 : Blo 1752577 3947417 := bstep (se 2 (by rfl) ⟨1480281, by rfl⟩ : syracuseStep 3947417 = 2960563) B2960563
theorem B4996019 : Blo 1752577 4996019 := bstep (se 1 (by rfl) ⟨3747014, by rfl⟩ : syracuseStep 4996019 = 7494029) B7494029
theorem B4996043 : Blo 1752577 4996043 := bstep (se 1 (by rfl) ⟨3747032, by rfl⟩ : syracuseStep 4996043 = 7494065) B7494065
theorem B1973227 : Blo 1752577 1973227 := bstep (se 1 (by rfl) ⟨1479920, by rfl⟩ : syracuseStep 1973227 = 2959841) B2959841
theorem B3947507 : Blo 1752577 3947507 := bstep (se 1 (by rfl) ⟨2960630, by rfl⟩ : syracuseStep 3947507 = 5921261) B5921261
theorem B3161099 : Blo 1752577 3161099 := bstep (se 1 (by rfl) ⟨2370824, by rfl⟩ : syracuseStep 3161099 = 4741649) B4741649
theorem B4439063 : Blo 1752577 4439063 := bstep (se 1 (by rfl) ⟨3329297, by rfl⟩ : syracuseStep 4439063 = 6658595) B6658595
theorem B3947543 : Blo 1752577 3947543 := bstep (se 1 (by rfl) ⟨2960657, by rfl⟩ : syracuseStep 3947543 = 5921315) B5921315
theorem B1973335 : Blo 1752577 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B33725591 : Blo 1752577 33725591 := bstep (se 1 (by rfl) ⟨25294193, by rfl⟩ : syracuseStep 33725591 = 50588387) B50588387
theorem B3947723 : Blo 1752577 3947723 := bstep (se 1 (by rfl) ⟨2960792, by rfl⟩ : syracuseStep 3947723 = 5921585) B5921585
theorem B6659293 : Blo 1752577 6659293 := bstep (se 3 (by rfl) ⟨1248617, by rfl⟩ : syracuseStep 6659293 = 2497235) B2497235
theorem B5618909 : Blo 1752577 5618909 := bstep (se 3 (by rfl) ⟨1053545, by rfl⟩ : syracuseStep 5618909 = 2107091) B2107091
theorem B3947777 : Blo 1752577 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B2628875 : Blo 1752577 2628875 := bstep (se 1 (by rfl) ⟨1971656, by rfl⟩ : syracuseStep 2628875 = 3943313) B3943313
theorem B1973515 : Blo 1752577 1973515 := bstep (se 1 (by rfl) ⟨1480136, by rfl⟩ : syracuseStep 1973515 = 2960273) B2960273
theorem B2628887 : Blo 1752577 2628887 := bstep (se 1 (by rfl) ⟨1971665, by rfl⟩ : syracuseStep 2628887 = 3943331) B3943331
theorem B14974253 : Blo 1752577 14974253 := bstep (se 3 (by rfl) ⟨2807672, by rfl⟩ : syracuseStep 14974253 = 5615345) B5615345
theorem B2219339 : Blo 1752577 2219339 := bstep (se 1 (by rfl) ⟨1664504, by rfl⟩ : syracuseStep 2219339 = 3329009) B3329009
theorem B2628953 : Blo 1752577 2628953 := bstep (se 2 (by rfl) ⟨985857, by rfl⟩ : syracuseStep 2628953 = 1971715) B1971715
theorem B4742489 : Blo 1752577 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B1973623 : Blo 1752577 1973623 := bstep (se 1 (by rfl) ⟨1480217, by rfl⟩ : syracuseStep 1973623 = 2960435) B2960435
theorem B2629067 : Blo 1752577 2629067 := bstep (se 1 (by rfl) ⟨1971800, by rfl⟩ : syracuseStep 2629067 = 3943601) B3943601
theorem B2629079 : Blo 1752577 2629079 := bstep (se 1 (by rfl) ⟨1971809, by rfl⟩ : syracuseStep 2629079 = 3943619) B3943619
theorem B1752587 : Blo 1752577 1752587 := bstep (se 1 (by rfl) ⟨1314440, by rfl⟩ : syracuseStep 1752587 = 2628881) B2628881
theorem B1752599 : Blo 1752577 1752599 := bstep (se 1 (by rfl) ⟨1314449, by rfl⟩ : syracuseStep 1752599 = 2628899) B2628899
theorem B3374615 : Blo 1752577 3374615 := bstep (se 1 (by rfl) ⟨2530961, by rfl⟩ : syracuseStep 3374615 = 5061923) B5061923
theorem B2629145 : Blo 1752577 2629145 := bstep (se 2 (by rfl) ⟨985929, by rfl⟩ : syracuseStep 2629145 = 1971859) B1971859
theorem B1752619 : Blo 1752577 1752619 := bstep (se 1 (by rfl) ⟨1314464, by rfl⟩ : syracuseStep 1752619 = 2628929) B2628929
theorem B8543789 : Blo 1752577 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B1973803 : Blo 1752577 1973803 := bstep (se 1 (by rfl) ⟨1480352, by rfl⟩ : syracuseStep 1973803 = 2960705) B2960705
theorem B4742707 : Blo 1752577 4742707 := bstep (se 1 (by rfl) ⟨3557030, by rfl⟩ : syracuseStep 4742707 = 7114061) B7114061
theorem B1752631 : Blo 1752577 1752631 := bstep (se 1 (by rfl) ⟨1314473, by rfl⟩ : syracuseStep 1752631 = 2628947) B2628947
theorem B4562497 : Blo 1752577 4562497 := bstep (se 2 (by rfl) ⟨1710936, by rfl⟩ : syracuseStep 4562497 = 3421873) B3421873
theorem B1752651 : Blo 1752577 1752651 := bstep (se 1 (by rfl) ⟨1314488, by rfl⟩ : syracuseStep 1752651 = 2628977) B2628977
theorem B1752663 : Blo 1752577 1752663 := bstep (se 1 (by rfl) ⟨1314497, by rfl⟩ : syracuseStep 1752663 = 2628995) B2628995
theorem B1752683 : Blo 1752577 1752683 := bstep (se 1 (by rfl) ⟨1314512, by rfl⟩ : syracuseStep 1752683 = 2629025) B2629025
theorem B1752695 : Blo 1752577 1752695 := bstep (se 1 (by rfl) ⟨1314521, by rfl⟩ : syracuseStep 1752695 = 2629043) B2629043
theorem B1752715 : Blo 1752577 1752715 := bstep (se 1 (by rfl) ⟨1314536, by rfl⟩ : syracuseStep 1752715 = 2629073) B2629073
theorem B2629259 : Blo 1752577 2629259 := bstep (se 1 (by rfl) ⟨1971944, by rfl⟩ : syracuseStep 2629259 = 3943889) B3943889
theorem B1752727 : Blo 1752577 1752727 := bstep (se 1 (by rfl) ⟨1314545, by rfl⟩ : syracuseStep 1752727 = 2629091) B2629091
theorem B2629271 : Blo 1752577 2629271 := bstep (se 1 (by rfl) ⟨1971953, by rfl⟩ : syracuseStep 2629271 = 3943907) B3943907
theorem B1752747 : Blo 1752577 1752747 := bstep (se 1 (by rfl) ⟨1314560, by rfl⟩ : syracuseStep 1752747 = 2629121) B2629121
theorem B4439731 : Blo 1752577 4439731 := bstep (se 1 (by rfl) ⟨3329798, by rfl⟩ : syracuseStep 4439731 = 6659597) B6659597
theorem B1752759 : Blo 1752577 1752759 := bstep (se 1 (by rfl) ⟨1314569, by rfl⟩ : syracuseStep 1752759 = 2629139) B2629139
theorem B1752779 : Blo 1752577 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1752791 : Blo 1752577 1752791 := bstep (se 1 (by rfl) ⟨1314593, by rfl⟩ : syracuseStep 1752791 = 2629187) B2629187
theorem B2629337 : Blo 1752577 2629337 := bstep (se 2 (by rfl) ⟨986001, by rfl⟩ : syracuseStep 2629337 = 1972003) B1972003
theorem B1752811 : Blo 1752577 1752811 := bstep (se 1 (by rfl) ⟨1314608, by rfl⟩ : syracuseStep 1752811 = 2629217) B2629217
theorem B1752823 : Blo 1752577 1752823 := bstep (se 1 (by rfl) ⟨1314617, by rfl⟩ : syracuseStep 1752823 = 2629235) B2629235
theorem B1752843 : Blo 1752577 1752843 := bstep (se 1 (by rfl) ⟨1314632, by rfl⟩ : syracuseStep 1752843 = 2629265) B2629265
theorem B1752855 : Blo 1752577 1752855 := bstep (se 1 (by rfl) ⟨1314641, by rfl⟩ : syracuseStep 1752855 = 2629283) B2629283
theorem B1752875 : Blo 1752577 1752875 := bstep (se 1 (by rfl) ⟨1314656, by rfl⟩ : syracuseStep 1752875 = 2629313) B2629313
theorem B1752887 : Blo 1752577 1752887 := bstep (se 1 (by rfl) ⟨1314665, by rfl⟩ : syracuseStep 1752887 = 2629331) B2629331
theorem B4439873 : Blo 1752577 4439873 := bstep (se 2 (by rfl) ⟨1664952, by rfl⟩ : syracuseStep 4439873 = 3329905) B3329905
theorem B1752907 : Blo 1752577 1752907 := bstep (se 1 (by rfl) ⟨1314680, by rfl⟩ : syracuseStep 1752907 = 2629361) B2629361
theorem B2629451 : Blo 1752577 2629451 := bstep (se 1 (by rfl) ⟨1972088, by rfl⟩ : syracuseStep 2629451 = 3944177) B3944177
theorem B1752919 : Blo 1752577 1752919 := bstep (se 1 (by rfl) ⟨1314689, by rfl⟩ : syracuseStep 1752919 = 2629379) B2629379
theorem B2629463 : Blo 1752577 2629463 := bstep (se 1 (by rfl) ⟨1972097, by rfl⟩ : syracuseStep 2629463 = 3944195) B3944195
theorem B1752939 : Blo 1752577 1752939 := bstep (se 1 (by rfl) ⟨1314704, by rfl⟩ : syracuseStep 1752939 = 2629409) B2629409
theorem B1752951 : Blo 1752577 1752951 := bstep (se 1 (by rfl) ⟨1314713, by rfl⟩ : syracuseStep 1752951 = 2629427) B2629427
theorem B1752971 : Blo 1752577 1752971 := bstep (se 1 (by rfl) ⟨1314728, by rfl⟩ : syracuseStep 1752971 = 2629457) B2629457
theorem B1752983 : Blo 1752577 1752983 := bstep (se 1 (by rfl) ⟨1314737, by rfl⟩ : syracuseStep 1752983 = 2629475) B2629475
theorem B11386775 : Blo 1752577 11386775 := bstep (se 1 (by rfl) ⟨8540081, by rfl⟩ : syracuseStep 11386775 = 17080163) B17080163
theorem B2629529 : Blo 1752577 2629529 := bstep (se 2 (by rfl) ⟨986073, by rfl⟩ : syracuseStep 2629529 = 1972147) B1972147
theorem B1753003 : Blo 1752577 1753003 := bstep (se 1 (by rfl) ⟨1314752, by rfl⟩ : syracuseStep 1753003 = 2629505) B2629505
theorem B1753015 : Blo 1752577 1753015 := bstep (se 1 (by rfl) ⟨1314761, by rfl⟩ : syracuseStep 1753015 = 2629523) B2629523
theorem B1753035 : Blo 1752577 1753035 := bstep (se 1 (by rfl) ⟨1314776, by rfl⟩ : syracuseStep 1753035 = 2629553) B2629553
theorem B1753047 : Blo 1752577 1753047 := bstep (se 1 (by rfl) ⟨1314785, by rfl⟩ : syracuseStep 1753047 = 2629571) B2629571
theorem B1753067 : Blo 1752577 1753067 := bstep (se 1 (by rfl) ⟨1314800, by rfl⟩ : syracuseStep 1753067 = 2629601) B2629601
theorem B1753079 : Blo 1752577 1753079 := bstep (se 1 (by rfl) ⟨1314809, by rfl⟩ : syracuseStep 1753079 = 2629619) B2629619
theorem B1753095 : Blo 1752577 1753095 := bstep (se 1 (by rfl) ⟨1314821, by rfl⟩ : syracuseStep 1753095 = 2629643) B2629643
theorem B1753103 : Blo 1752577 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B2629691 : Blo 1752577 2629691 := bstep (se 1 (by rfl) ⟨1972268, by rfl⟩ : syracuseStep 2629691 = 3944537) B3944537
theorem B1753147 : Blo 1752577 1753147 := bstep (se 1 (by rfl) ⟨1314860, by rfl⟩ : syracuseStep 1753147 = 2629721) B2629721
theorem B5333051 : Blo 1752577 5333051 := bstep (se 1 (by rfl) ⟨3999788, by rfl⟩ : syracuseStep 5333051 = 7999577) B7999577
theorem B2629751 : Blo 1752577 2629751 := bstep (se 1 (by rfl) ⟨1972313, by rfl⟩ : syracuseStep 2629751 = 3944627) B3944627
theorem B16851077 : Blo 1752577 16851077 := bstep (se 4 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 16851077 = 3159577) B3159577
theorem B1753223 : Blo 1752577 1753223 := bstep (se 1 (by rfl) ⟨1314917, by rfl⟩ : syracuseStep 1753223 = 2629835) B2629835
theorem B2629775 : Blo 1752577 2629775 := bstep (se 1 (by rfl) ⟨1972331, by rfl⟩ : syracuseStep 2629775 = 3944663) B3944663
theorem B1753231 : Blo 1752577 1753231 := bstep (se 1 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 1753231 = 2629847) B2629847
theorem B4440217 : Blo 1752577 4440217 := bstep (se 2 (by rfl) ⟨1665081, by rfl⟩ : syracuseStep 4440217 = 3330163) B3330163
theorem B2629817 : Blo 1752577 2629817 := bstep (se 2 (by rfl) ⟨986181, by rfl⟩ : syracuseStep 2629817 = 1972363) B1972363
theorem B1753275 : Blo 1752577 1753275 := bstep (se 1 (by rfl) ⟨1314956, by rfl⟩ : syracuseStep 1753275 = 2629913) B2629913
theorem B11239661 : Blo 1752577 11239661 := bstep (se 3 (by rfl) ⟨2107436, by rfl⟩ : syracuseStep 11239661 = 4214873) B4214873
theorem B2629895 : Blo 1752577 2629895 := bstep (se 1 (by rfl) ⟨1972421, by rfl⟩ : syracuseStep 2629895 = 3944843) B3944843
theorem B1753351 : Blo 1752577 1753351 := bstep (se 1 (by rfl) ⟨1315013, by rfl⟩ : syracuseStep 1753351 = 2630027) B2630027
theorem B1753359 : Blo 1752577 1753359 := bstep (se 1 (by rfl) ⟨1315019, by rfl⟩ : syracuseStep 1753359 = 2630039) B2630039
theorem B2629931 : Blo 1752577 2629931 := bstep (se 1 (by rfl) ⟨1972448, by rfl⟩ : syracuseStep 2629931 = 3944897) B3944897
theorem B2957627 : Blo 1752577 2957627 := bstep (se 1 (by rfl) ⟨2218220, by rfl⟩ : syracuseStep 2957627 = 4436441) B4436441
theorem B1753403 : Blo 1752577 1753403 := bstep (se 1 (by rfl) ⟨1315052, by rfl⟩ : syracuseStep 1753403 = 2630105) B2630105
theorem B4440379 : Blo 1752577 4440379 := bstep (se 1 (by rfl) ⟨3330284, by rfl⟩ : syracuseStep 4440379 = 6660569) B6660569
theorem B2629961 : Blo 1752577 2629961 := bstep (se 2 (by rfl) ⟨986235, by rfl⟩ : syracuseStep 2629961 = 1972471) B1972471
theorem B1753479 : Blo 1752577 1753479 := bstep (se 1 (by rfl) ⟨1315109, by rfl⟩ : syracuseStep 1753479 = 2630219) B2630219
theorem B1753487 : Blo 1752577 1753487 := bstep (se 1 (by rfl) ⟨1315115, by rfl⟩ : syracuseStep 1753487 = 2630231) B2630231
theorem B2630075 : Blo 1752577 2630075 := bstep (se 1 (by rfl) ⟨1972556, by rfl⟩ : syracuseStep 2630075 = 3945113) B3945113
theorem B1753531 : Blo 1752577 1753531 := bstep (se 1 (by rfl) ⟨1315148, by rfl⟩ : syracuseStep 1753531 = 2630297) B2630297
theorem B4440521 : Blo 1752577 4440521 := bstep (se 2 (by rfl) ⟨1665195, by rfl⟩ : syracuseStep 4440521 = 3330391) B3330391
theorem B2630135 : Blo 1752577 2630135 := bstep (se 1 (by rfl) ⟨1972601, by rfl⟩ : syracuseStep 2630135 = 3945203) B3945203
theorem B1753607 : Blo 1752577 1753607 := bstep (se 1 (by rfl) ⟨1315205, by rfl⟩ : syracuseStep 1753607 = 2630411) B2630411
theorem B2630159 : Blo 1752577 2630159 := bstep (se 1 (by rfl) ⟨1972619, by rfl⟩ : syracuseStep 2630159 = 3945239) B3945239
theorem B1753615 : Blo 1752577 1753615 := bstep (se 1 (by rfl) ⟨1315211, by rfl⟩ : syracuseStep 1753615 = 2630423) B2630423
theorem B3744299 : Blo 1752577 3744299 := bstep (se 1 (by rfl) ⟨2808224, by rfl⟩ : syracuseStep 3744299 = 5616449) B5616449
theorem B2630201 : Blo 1752577 2630201 := bstep (se 2 (by rfl) ⟨986325, by rfl⟩ : syracuseStep 2630201 = 1972651) B1972651
theorem B1753659 : Blo 1752577 1753659 := bstep (se 1 (by rfl) ⟨1315244, by rfl⟩ : syracuseStep 1753659 = 2630489) B2630489
theorem B2998919 : Blo 1752577 2998919 := bstep (se 1 (by rfl) ⟨2249189, by rfl⟩ : syracuseStep 2998919 = 4498379) B4498379
theorem B2630279 : Blo 1752577 2630279 := bstep (se 1 (by rfl) ⟨1972709, by rfl⟩ : syracuseStep 2630279 = 3945419) B3945419
theorem B1753735 : Blo 1752577 1753735 := bstep (se 1 (by rfl) ⟨1315301, by rfl⟩ : syracuseStep 1753735 = 2630603) B2630603
theorem B1753743 : Blo 1752577 1753743 := bstep (se 1 (by rfl) ⟨1315307, by rfl⟩ : syracuseStep 1753743 = 2630615) B2630615
theorem B2630315 : Blo 1752577 2630315 := bstep (se 1 (by rfl) ⟨1972736, by rfl⟩ : syracuseStep 2630315 = 3945473) B3945473
theorem B1753787 : Blo 1752577 1753787 := bstep (se 1 (by rfl) ⟨1315340, by rfl⟩ : syracuseStep 1753787 = 2630681) B2630681
theorem B9986753 : Blo 1752577 9986753 := bstep (se 2 (by rfl) ⟨3745032, by rfl⟩ : syracuseStep 9986753 = 7490065) B7490065
theorem B2958025 : Blo 1752577 2958025 := bstep (se 2 (by rfl) ⟨1109259, by rfl⟩ : syracuseStep 2958025 = 2218519) B2218519
theorem B2630345 : Blo 1752577 2630345 := bstep (se 2 (by rfl) ⟨986379, by rfl⟩ : syracuseStep 2630345 = 1972759) B1972759
theorem B1753863 : Blo 1752577 1753863 := bstep (se 1 (by rfl) ⟨1315397, by rfl⟩ : syracuseStep 1753863 = 2630795) B2630795
theorem B1753871 : Blo 1752577 1753871 := bstep (se 1 (by rfl) ⟨1315403, by rfl⟩ : syracuseStep 1753871 = 2630807) B2630807
theorem B4440865 : Blo 1752577 4440865 := bstep (se 2 (by rfl) ⟨1665324, by rfl⟩ : syracuseStep 4440865 = 3330649) B3330649
theorem B2630459 : Blo 1752577 2630459 := bstep (se 1 (by rfl) ⟨1972844, by rfl⟩ : syracuseStep 2630459 = 3945689) B3945689
theorem B1753915 : Blo 1752577 1753915 := bstep (se 1 (by rfl) ⟨1315436, by rfl⟩ : syracuseStep 1753915 = 2630873) B2630873
theorem B2630519 : Blo 1752577 2630519 := bstep (se 1 (by rfl) ⟨1972889, by rfl⟩ : syracuseStep 2630519 = 3945779) B3945779
theorem B1753991 : Blo 1752577 1753991 := bstep (se 1 (by rfl) ⟨1315493, by rfl⟩ : syracuseStep 1753991 = 2630987) B2630987
theorem B2630543 : Blo 1752577 2630543 := bstep (se 1 (by rfl) ⟨1972907, by rfl⟩ : syracuseStep 2630543 = 3945815) B3945815
theorem B1753999 : Blo 1752577 1753999 := bstep (se 1 (by rfl) ⟨1315499, by rfl⟩ : syracuseStep 1753999 = 2630999) B2630999
theorem B7488409 : Blo 1752577 7488409 := bstep (se 2 (by rfl) ⟨2808153, by rfl⟩ : syracuseStep 7488409 = 5616307) B5616307
theorem B8995769 : Blo 1752577 8995769 := bstep (se 2 (by rfl) ⟨3373413, by rfl⟩ : syracuseStep 8995769 = 6746827) B6746827
theorem B2630585 : Blo 1752577 2630585 := bstep (se 2 (by rfl) ⟨986469, by rfl⟩ : syracuseStep 2630585 = 1972939) B1972939
theorem B1754043 : Blo 1752577 1754043 := bstep (se 1 (by rfl) ⟨1315532, by rfl⟩ : syracuseStep 1754043 = 2631065) B2631065
theorem B2630663 : Blo 1752577 2630663 := bstep (se 1 (by rfl) ⟨1972997, by rfl⟩ : syracuseStep 2630663 = 3945995) B3945995
theorem B1754119 : Blo 1752577 1754119 := bstep (se 1 (by rfl) ⟨1315589, by rfl⟩ : syracuseStep 1754119 = 2631179) B2631179
theorem B1754127 : Blo 1752577 1754127 := bstep (se 1 (by rfl) ⟨1315595, by rfl⟩ : syracuseStep 1754127 = 2631191) B2631191
theorem B8881163 : Blo 1752577 8881163 := bstep (se 1 (by rfl) ⟨6660872, by rfl⟩ : syracuseStep 8881163 = 13321745) B13321745
theorem B2630699 : Blo 1752577 2630699 := bstep (se 1 (by rfl) ⟨1973024, by rfl⟩ : syracuseStep 2630699 = 3946049) B3946049
theorem B1754171 : Blo 1752577 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B2630729 : Blo 1752577 2630729 := bstep (se 2 (by rfl) ⟨986523, by rfl⟩ : syracuseStep 2630729 = 1973047) B1973047
theorem B1754247 : Blo 1752577 1754247 := bstep (se 1 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 1754247 = 2631371) B2631371
theorem B1754255 : Blo 1752577 1754255 := bstep (se 1 (by rfl) ⟨1315691, by rfl⟩ : syracuseStep 1754255 = 2631383) B2631383
theorem B8881325 : Blo 1752577 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B2630843 : Blo 1752577 2630843 := bstep (se 1 (by rfl) ⟨1973132, by rfl⟩ : syracuseStep 2630843 = 3946265) B3946265
theorem B1754299 : Blo 1752577 1754299 := bstep (se 1 (by rfl) ⟨1315724, by rfl⟩ : syracuseStep 1754299 = 2631449) B2631449
theorem B2630903 : Blo 1752577 2630903 := bstep (se 1 (by rfl) ⟨1973177, by rfl⟩ : syracuseStep 2630903 = 3946355) B3946355
theorem B1754375 : Blo 1752577 1754375 := bstep (se 1 (by rfl) ⟨1315781, by rfl⟩ : syracuseStep 1754375 = 2631563) B2631563
theorem B3327247 : Blo 1752577 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B2630927 : Blo 1752577 2630927 := bstep (se 1 (by rfl) ⟨1973195, by rfl⟩ : syracuseStep 2630927 = 3946391) B3946391
theorem B1754383 : Blo 1752577 1754383 := bstep (se 1 (by rfl) ⟨1315787, by rfl⟩ : syracuseStep 1754383 = 2631575) B2631575
theorem B2630969 : Blo 1752577 2630969 := bstep (se 2 (by rfl) ⟨986613, by rfl⟩ : syracuseStep 2630969 = 1973227) B1973227
theorem B1754427 : Blo 1752577 1754427 := bstep (se 1 (by rfl) ⟨1315820, by rfl⟩ : syracuseStep 1754427 = 2631641) B2631641
theorem B2958727 : Blo 1752577 2958727 := bstep (se 1 (by rfl) ⟨2219045, by rfl⟩ : syracuseStep 2958727 = 4438091) B4438091
theorem B2631047 : Blo 1752577 2631047 := bstep (se 1 (by rfl) ⟨1973285, by rfl⟩ : syracuseStep 2631047 = 3946571) B3946571
theorem B6661511 : Blo 1752577 6661511 := bstep (se 1 (by rfl) ⟨4996133, by rfl⟩ : syracuseStep 6661511 = 9992267) B9992267
theorem B1754503 : Blo 1752577 1754503 := bstep (se 1 (by rfl) ⟨1315877, by rfl⟩ : syracuseStep 1754503 = 2631755) B2631755
theorem B1754511 : Blo 1752577 1754511 := bstep (se 1 (by rfl) ⟨1315883, by rfl⟩ : syracuseStep 1754511 = 2631767) B2631767
theorem B2631083 : Blo 1752577 2631083 := bstep (se 1 (by rfl) ⟨1973312, by rfl⟩ : syracuseStep 2631083 = 3946625) B3946625
theorem B1754555 : Blo 1752577 1754555 := bstep (se 1 (by rfl) ⟨1315916, by rfl⟩ : syracuseStep 1754555 = 2631833) B2631833
theorem B2631113 : Blo 1752577 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B6407633 : Blo 1752577 6407633 := bstep (se 2 (by rfl) ⟨2402862, by rfl⟩ : syracuseStep 6407633 = 4805725) B4805725
theorem B2369083 : Blo 1752577 2369083 := bstep (se 1 (by rfl) ⟨1776812, by rfl⟩ : syracuseStep 2369083 = 3553625) B3553625
theorem B2631227 : Blo 1752577 2631227 := bstep (se 1 (by rfl) ⟨1973420, by rfl⟩ : syracuseStep 2631227 = 3946841) B3946841
theorem B8111677 : Blo 1752577 8111677 := bstep (se 3 (by rfl) ⟨1520939, by rfl⟩ : syracuseStep 8111677 = 3041879) B3041879
theorem B19981889 : Blo 1752577 19981889 := bstep (se 2 (by rfl) ⟨7493208, by rfl⟩ : syracuseStep 19981889 = 14986417) B14986417
theorem B2631287 : Blo 1752577 2631287 := bstep (se 1 (by rfl) ⟨1973465, by rfl⟩ : syracuseStep 2631287 = 3946931) B3946931
theorem B2631311 : Blo 1752577 2631311 := bstep (se 1 (by rfl) ⟨1973483, by rfl⟩ : syracuseStep 2631311 = 3946967) B3946967
theorem B3327635 : Blo 1752577 3327635 := bstep (se 1 (by rfl) ⟨2495726, by rfl⟩ : syracuseStep 3327635 = 4991453) B4991453
theorem B2631353 : Blo 1752577 2631353 := bstep (se 2 (by rfl) ⟨986757, by rfl⟩ : syracuseStep 2631353 = 1973515) B1973515
theorem B37906177 : Blo 1752577 37906177 := bstep (se 2 (by rfl) ⟨14214816, by rfl⟩ : syracuseStep 37906177 = 28429633) B28429633
theorem B11233025 : Blo 1752577 11233025 := bstep (se 2 (by rfl) ⟨4212384, by rfl⟩ : syracuseStep 11233025 = 8424769) B8424769
theorem B2631431 : Blo 1752577 2631431 := bstep (se 1 (by rfl) ⟨1973573, by rfl⟩ : syracuseStep 2631431 = 3947147) B3947147
theorem B5998369 : Blo 1752577 5998369 := bstep (se 2 (by rfl) ⟨2249388, by rfl⟩ : syracuseStep 5998369 = 4498777) B4498777
theorem B2631467 : Blo 1752577 2631467 := bstep (se 1 (by rfl) ⟨1973600, by rfl⟩ : syracuseStep 2631467 = 3947201) B3947201
theorem B4212539 : Blo 1752577 4212539 := bstep (se 1 (by rfl) ⟨3159404, by rfl⟩ : syracuseStep 4212539 = 6318809) B6318809
theorem B2631497 : Blo 1752577 2631497 := bstep (se 2 (by rfl) ⟨986811, by rfl⟩ : syracuseStep 2631497 = 1973623) B1973623
theorem B8873873 : Blo 1752577 8873873 := bstep (se 2 (by rfl) ⟨3327702, by rfl⟩ : syracuseStep 8873873 = 6655405) B6655405
theorem B5916563 : Blo 1752577 5916563 := bstep (se 1 (by rfl) ⟨4437422, by rfl⟩ : syracuseStep 5916563 = 8874845) B8874845
theorem B36497303 : Blo 1752577 36497303 := bstep (se 1 (by rfl) ⟨27372977, by rfl⟩ : syracuseStep 36497303 = 54745955) B54745955
theorem B2631611 : Blo 1752577 2631611 := bstep (se 1 (by rfl) ⟨1973708, by rfl⟩ : syracuseStep 2631611 = 3947417) B3947417
theorem B18958283 : Blo 1752577 18958283 := bstep (se 1 (by rfl) ⟨14218712, by rfl⟩ : syracuseStep 18958283 = 28437425) B28437425
theorem B2631671 : Blo 1752577 2631671 := bstep (se 1 (by rfl) ⟨1973753, by rfl⟩ : syracuseStep 2631671 = 3947507) B3947507
theorem B2107399 : Blo 1752577 2107399 := bstep (se 1 (by rfl) ⟨1580549, by rfl⟩ : syracuseStep 2107399 = 3161099) B3161099
theorem B2959375 : Blo 1752577 2959375 := bstep (se 1 (by rfl) ⟨2219531, by rfl⟩ : syracuseStep 2959375 = 4439063) B4439063
theorem B2631695 : Blo 1752577 2631695 := bstep (se 1 (by rfl) ⟨1973771, by rfl⟩ : syracuseStep 2631695 = 3947543) B3947543
theorem B8538155 : Blo 1752577 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B2631737 : Blo 1752577 2631737 := bstep (se 2 (by rfl) ⟨986901, by rfl⟩ : syracuseStep 2631737 = 1973803) B1973803
theorem B7489655 : Blo 1752577 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B2631815 : Blo 1752577 2631815 := bstep (se 1 (by rfl) ⟨1973861, by rfl⟩ : syracuseStep 2631815 = 3947723) B3947723
theorem B3745939 : Blo 1752577 3745939 := bstep (se 1 (by rfl) ⟨2809454, by rfl⟩ : syracuseStep 3745939 = 5618909) B5618909
theorem B136726679 : Blo 1752577 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B2631851 : Blo 1752577 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B5695859 : Blo 1752577 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B13322717 : Blo 1752577 13322717 := bstep (se 3 (by rfl) ⟨2498009, by rfl⟩ : syracuseStep 13322717 = 4996019) B4996019
theorem B2959915 : Blo 1752577 2959915 := bstep (se 1 (by rfl) ⟨2219936, by rfl⟩ : syracuseStep 2959915 = 4439873) B4439873
theorem B2960057 : Blo 1752577 2960057 := bstep (se 2 (by rfl) ⟨1110021, by rfl⟩ : syracuseStep 2960057 = 2220043) B2220043
theorem B16845731 : Blo 1752577 16845731 := bstep (se 1 (by rfl) ⟨12634298, by rfl⟩ : syracuseStep 16845731 = 25268597) B25268597
theorem B6654905 : Blo 1752577 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B4271105 : Blo 1752577 4271105 := bstep (se 2 (by rfl) ⟨1601664, by rfl⟩ : syracuseStep 4271105 = 3203329) B3203329
theorem B3943439 : Blo 1752577 3943439 := bstep (se 1 (by rfl) ⟨2957579, by rfl⟩ : syracuseStep 3943439 = 5915159) B5915159
theorem B3329039 : Blo 1752577 3329039 := bstep (se 1 (by rfl) ⟨2496779, by rfl⟩ : syracuseStep 3329039 = 4993559) B4993559
theorem B3943457 : Blo 1752577 3943457 := bstep (se 2 (by rfl) ⟨1478796, by rfl⟩ : syracuseStep 3943457 = 2957593) B2957593
theorem B5614679 : Blo 1752577 5614679 := bstep (se 1 (by rfl) ⟨4211009, by rfl⟩ : syracuseStep 5614679 = 8422019) B8422019
theorem B5917967 : Blo 1752577 5917967 := bstep (se 1 (by rfl) ⟨4438475, by rfl⟩ : syracuseStep 5917967 = 8876951) B8876951
theorem B3943799 : Blo 1752577 3943799 := bstep (se 1 (by rfl) ⟨2957849, by rfl⟩ : syracuseStep 3943799 = 5915699) B5915699
theorem B2960759 : Blo 1752577 2960759 := bstep (se 1 (by rfl) ⟨2220569, by rfl⟩ : syracuseStep 2960759 = 4441139) B4441139
theorem B9121169 : Blo 1752577 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B5918237 : Blo 1752577 5918237 := bstep (se 3 (by rfl) ⟨1109669, by rfl⟩ : syracuseStep 5918237 = 2219339) B2219339
theorem B30379549 : Blo 1752577 30379549 := bstep (se 3 (by rfl) ⟨5696165, by rfl⟩ : syracuseStep 30379549 = 11392331) B11392331
theorem B3943979 : Blo 1752577 3943979 := bstep (se 1 (by rfl) ⟨2957984, by rfl⟩ : syracuseStep 3943979 = 5915969) B5915969
theorem B3329579 : Blo 1752577 3329579 := bstep (se 1 (by rfl) ⟨2497184, by rfl⟩ : syracuseStep 3329579 = 4994369) B4994369
theorem B4214315 : Blo 1752577 4214315 := bstep (se 1 (by rfl) ⟨3160736, by rfl⟩ : syracuseStep 4214315 = 6321473) B6321473
theorem B14978627 : Blo 1752577 14978627 := bstep (se 1 (by rfl) ⟨11233970, by rfl⟩ : syracuseStep 14978627 = 22467941) B22467941
theorem B5615191 : Blo 1752577 5615191 := bstep (se 1 (by rfl) ⟨4211393, by rfl⟩ : syracuseStep 5615191 = 8422787) B8422787
theorem B4501079 : Blo 1752577 4501079 := bstep (se 1 (by rfl) ⟨3375809, by rfl⟩ : syracuseStep 4501079 = 6751619) B6751619
theorem B4738675 : Blo 1752577 4738675 := bstep (se 1 (by rfl) ⟨3554006, by rfl⟩ : syracuseStep 4738675 = 7108013) B7108013
theorem B10669805 : Blo 1752577 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B16854799 : Blo 1752577 16854799 := bstep (se 1 (by rfl) ⟨12641099, by rfl⟩ : syracuseStep 16854799 = 25282199) B25282199
theorem B9482021 : Blo 1752577 9482021 := bstep (se 4 (by rfl) ⟨888939, by rfl⟩ : syracuseStep 9482021 = 1777879) B1777879
theorem B6655891 : Blo 1752577 6655891 := bstep (se 1 (by rfl) ⟨4991918, by rfl⟩ : syracuseStep 6655891 = 9983837) B9983837
theorem B3944339 : Blo 1752577 3944339 := bstep (se 1 (by rfl) ⟨2958254, by rfl⟩ : syracuseStep 3944339 = 5916509) B5916509
theorem B3944393 : Blo 1752577 3944393 := bstep (se 2 (by rfl) ⟨1479147, by rfl⟩ : syracuseStep 3944393 = 2958295) B2958295
theorem B8875979 : Blo 1752577 8875979 := bstep (se 1 (by rfl) ⟨6656984, by rfl⟩ : syracuseStep 8875979 = 13313969) B13313969
theorem B8876303 : Blo 1752577 8876303 := bstep (se 1 (by rfl) ⟨6657227, by rfl⟩ : syracuseStep 8876303 = 13314455) B13314455
theorem B9482555 : Blo 1752577 9482555 := bstep (se 1 (by rfl) ⟨7111916, by rfl⟩ : syracuseStep 9482555 = 14223833) B14223833
theorem B4436491 : Blo 1752577 4436491 := bstep (se 1 (by rfl) ⟨3327368, by rfl⟩ : syracuseStep 4436491 = 6654737) B6654737
theorem B3945095 : Blo 1752577 3945095 := bstep (se 1 (by rfl) ⟨2958821, by rfl⟩ : syracuseStep 3945095 = 5917643) B5917643
theorem B3330695 : Blo 1752577 3330695 := bstep (se 1 (by rfl) ⟨2498021, by rfl⟩ : syracuseStep 3330695 = 4996043) B4996043
theorem B4436633 : Blo 1752577 4436633 := bstep (se 2 (by rfl) ⟨1663737, by rfl⟩ : syracuseStep 4436633 = 3327475) B3327475
theorem B6083329 : Blo 1752577 6083329 := bstep (se 2 (by rfl) ⟨2281248, by rfl⟩ : syracuseStep 6083329 = 4562497) B4562497
theorem B43242245 : Blo 1752577 43242245 := bstep (se 4 (by rfl) ⟨4053960, by rfl⟩ : syracuseStep 43242245 = 8107921) B8107921
theorem B22483727 : Blo 1752577 22483727 := bstep (se 1 (by rfl) ⟨16862795, by rfl⟩ : syracuseStep 22483727 = 33725591) B33725591
theorem B4436795 : Blo 1752577 4436795 := bstep (se 1 (by rfl) ⟨3327596, by rfl⟩ : syracuseStep 4436795 = 6655193) B6655193
theorem B3945275 : Blo 1752577 3945275 := bstep (se 1 (by rfl) ⟨2958956, by rfl⟩ : syracuseStep 3945275 = 5917913) B5917913
theorem B9982835 : Blo 1752577 9982835 := bstep (se 1 (by rfl) ⟨7487126, by rfl⟩ : syracuseStep 9982835 = 14974253) B14974253
theorem B6321011 : Blo 1752577 6321011 := bstep (se 1 (by rfl) ⟨4740758, by rfl⟩ : syracuseStep 6321011 = 9481517) B9481517
theorem B5919641 : Blo 1752577 5919641 := bstep (se 2 (by rfl) ⟨2219865, by rfl⟩ : syracuseStep 5919641 = 4439731) B4439731
theorem B3945401 : Blo 1752577 3945401 := bstep (se 2 (by rfl) ⟨1479525, by rfl⟩ : syracuseStep 3945401 = 2959051) B2959051
theorem B2249743 : Blo 1752577 2249743 := bstep (se 1 (by rfl) ⟨1687307, by rfl⟩ : syracuseStep 2249743 = 3374615) B3374615
theorem B30364733 : Blo 1752577 30364733 := bstep (se 3 (by rfl) ⟨5693387, by rfl⟩ : syracuseStep 30364733 = 11386775) B11386775
theorem B4437139 : Blo 1752577 4437139 := bstep (se 1 (by rfl) ⟨3327854, by rfl⟩ : syracuseStep 4437139 = 6655709) B6655709
theorem B5403905 : Blo 1752577 5403905 := bstep (se 2 (by rfl) ⟨2026464, by rfl⟩ : syracuseStep 5403905 = 4052929) B4052929
theorem B3945743 : Blo 1752577 3945743 := bstep (se 1 (by rfl) ⟨2959307, by rfl⟩ : syracuseStep 3945743 = 5918615) B5918615
theorem B4437281 : Blo 1752577 4437281 := bstep (se 2 (by rfl) ⟨1663980, by rfl⟩ : syracuseStep 4437281 = 3327961) B3327961
theorem B3945761 : Blo 1752577 3945761 := bstep (se 2 (by rfl) ⟨1479660, by rfl⟩ : syracuseStep 3945761 = 2959321) B2959321
theorem B2495863 : Blo 1752577 2495863 := bstep (se 1 (by rfl) ⟨1871897, by rfl⟩ : syracuseStep 2495863 = 3743795) B3743795
theorem B9475463 : Blo 1752577 9475463 := bstep (se 1 (by rfl) ⟨7106597, by rfl⟩ : syracuseStep 9475463 = 14213195) B14213195
theorem B72955313 : Blo 1752577 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B4994561 : Blo 1752577 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B118494737 : Blo 1752577 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B6657623 : Blo 1752577 6657623 := bstep (se 1 (by rfl) ⟨4993217, by rfl⟩ : syracuseStep 6657623 = 9986435) B9986435
theorem B4740695 : Blo 1752577 4740695 := bstep (se 1 (by rfl) ⟨3555521, by rfl⟩ : syracuseStep 4740695 = 7111043) B7111043
theorem B5920343 : Blo 1752577 5920343 := bstep (se 1 (by rfl) ⟨4440257, by rfl⟩ : syracuseStep 5920343 = 8880515) B8880515
theorem B3946103 : Blo 1752577 3946103 := bstep (se 1 (by rfl) ⟨2959577, by rfl⟩ : syracuseStep 3946103 = 5919155) B5919155
theorem B2496187 : Blo 1752577 2496187 := bstep (se 1 (by rfl) ⟨1872140, by rfl⟩ : syracuseStep 2496187 = 3744281) B3744281
theorem B8877761 : Blo 1752577 8877761 := bstep (se 2 (by rfl) ⟨3329160, by rfl⟩ : syracuseStep 8877761 = 6658321) B6658321
theorem B3946283 : Blo 1752577 3946283 := bstep (se 1 (by rfl) ⟨2959712, by rfl⟩ : syracuseStep 3946283 = 5919425) B5919425
theorem B1972111 : Blo 1752577 1972111 := bstep (se 1 (by rfl) ⟨1479083, by rfl⟩ : syracuseStep 1972111 = 2958167) B2958167
theorem B12638105 : Blo 1752577 12638105 := bstep (se 2 (by rfl) ⟨4739289, by rfl⟩ : syracuseStep 12638105 = 9478579) B9478579
theorem B22787993 : Blo 1752577 22787993 := bstep (se 2 (by rfl) ⟨8545497, by rfl⟩ : syracuseStep 22787993 = 17090995) B17090995
theorem B4446137 : Blo 1752577 4446137 := bstep (se 2 (by rfl) ⟨1667301, by rfl⟩ : syracuseStep 4446137 = 3334603) B3334603
theorem B4995017 : Blo 1752577 4995017 := bstep (se 2 (by rfl) ⟨1873131, by rfl⟩ : syracuseStep 4995017 = 3746263) B3746263
theorem B38426669 : Blo 1752577 38426669 := bstep (se 3 (by rfl) ⟨7205000, by rfl⟩ : syracuseStep 38426669 = 14410001) B14410001
theorem B6658109 : Blo 1752577 6658109 := bstep (se 3 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 6658109 = 2496791) B2496791
theorem B5920829 : Blo 1752577 5920829 := bstep (se 3 (by rfl) ⟨1110155, by rfl⟩ : syracuseStep 5920829 = 2220311) B2220311
theorem B2250871 : Blo 1752577 2250871 := bstep (se 1 (by rfl) ⟨1688153, by rfl⟩ : syracuseStep 2250871 = 3376307) B3376307
theorem B3946643 : Blo 1752577 3946643 := bstep (se 1 (by rfl) ⟨2959982, by rfl⟩ : syracuseStep 3946643 = 5919965) B5919965
theorem B2496683 : Blo 1752577 2496683 := bstep (se 1 (by rfl) ⟨1872512, by rfl⟩ : syracuseStep 2496683 = 3745025) B3745025
theorem B3946697 : Blo 1752577 3946697 := bstep (se 2 (by rfl) ⟨1480011, by rfl⟩ : syracuseStep 3946697 = 2960023) B2960023
theorem B12646637 : Blo 1752577 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B4438273 : Blo 1752577 4438273 := bstep (se 2 (by rfl) ⟨1664352, by rfl⟩ : syracuseStep 4438273 = 3328705) B3328705
theorem B4741409 : Blo 1752577 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B9984293 : Blo 1752577 9984293 := bstep (se 4 (by rfl) ⟨936027, by rfl⟩ : syracuseStep 9984293 = 1872055) B1872055
theorem B4995371 : Blo 1752577 4995371 := bstep (se 1 (by rfl) ⟨3746528, by rfl⟩ : syracuseStep 4995371 = 7493057) B7493057
theorem B40483165 : Blo 1752577 40483165 := bstep (se 3 (by rfl) ⟨7590593, by rfl⟩ : syracuseStep 40483165 = 15181187) B15181187
theorem B1972615 : Blo 1752577 1972615 := bstep (se 1 (by rfl) ⟨1479461, by rfl⟩ : syracuseStep 1972615 = 2958923) B2958923
theorem B50534873 : Blo 1752577 50534873 := bstep (se 2 (by rfl) ⟨18950577, by rfl⟩ : syracuseStep 50534873 = 37901155) B37901155
theorem B1972795 : Blo 1752577 1972795 := bstep (se 1 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 1972795 = 2959193) B2959193
theorem B9476675 : Blo 1752577 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B8428151 : Blo 1752577 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B4995769 : Blo 1752577 4995769 := bstep (se 2 (by rfl) ⟨1873413, by rfl⟩ : syracuseStep 4995769 = 3746827) B3746827
theorem B4438871 : Blo 1752577 4438871 := bstep (se 1 (by rfl) ⟨3329153, by rfl⟩ : syracuseStep 4438871 = 6658307) B6658307
theorem B3947399 : Blo 1752577 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B9984977 : Blo 1752577 9984977 := bstep (se 2 (by rfl) ⟨3744366, by rfl⟩ : syracuseStep 9984977 = 7488733) B7488733
theorem B8879057 : Blo 1752577 8879057 := bstep (se 2 (by rfl) ⟨3329646, by rfl⟩ : syracuseStep 8879057 = 6659293) B6659293
theorem B2219015 : Blo 1752577 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B1973263 : Blo 1752577 1973263 := bstep (se 1 (by rfl) ⟨1479947, by rfl⟩ : syracuseStep 1973263 = 2959895) B2959895
theorem B4439083 : Blo 1752577 4439083 := bstep (se 1 (by rfl) ⟨3329312, by rfl⟩ : syracuseStep 4439083 = 6658625) B6658625
theorem B3947579 : Blo 1752577 3947579 := bstep (se 1 (by rfl) ⟨2960684, by rfl⟩ : syracuseStep 3947579 = 5921369) B5921369
theorem B14982317 : Blo 1752577 14982317 := bstep (se 3 (by rfl) ⟨2809184, by rfl⟩ : syracuseStep 14982317 = 5618369) B5618369
theorem B4439225 : Blo 1752577 4439225 := bstep (se 2 (by rfl) ⟨1664709, by rfl⟩ : syracuseStep 4439225 = 3329419) B3329419
theorem B3947705 : Blo 1752577 3947705 := bstep (se 2 (by rfl) ⟨1480389, by rfl⟩ : syracuseStep 3947705 = 2960779) B2960779
theorem B9985295 : Blo 1752577 9985295 := bstep (se 1 (by rfl) ⟨7488971, by rfl⟩ : syracuseStep 9985295 = 14977943) B14977943
theorem B2628923 : Blo 1752577 2628923 := bstep (se 1 (by rfl) ⟨1971692, by rfl⟩ : syracuseStep 2628923 = 3943385) B3943385
theorem B2702665 : Blo 1752577 2702665 := bstep (se 2 (by rfl) ⟨1013499, by rfl⟩ : syracuseStep 2702665 = 2026999) B2026999
theorem B2628983 : Blo 1752577 2628983 := bstep (se 1 (by rfl) ⟨1971737, by rfl⟩ : syracuseStep 2628983 = 3943475) B3943475
theorem B3743111 : Blo 1752577 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B2629007 : Blo 1752577 2629007 := bstep (se 1 (by rfl) ⟨1971755, by rfl⟩ : syracuseStep 2629007 = 3943511) B3943511
theorem B6323609 : Blo 1752577 6323609 := bstep (se 2 (by rfl) ⟨2371353, by rfl⟩ : syracuseStep 6323609 = 4742707) B4742707
theorem B2629049 : Blo 1752577 2629049 := bstep (se 2 (by rfl) ⟨985893, by rfl⟩ : syracuseStep 2629049 = 1971787) B1971787
theorem B25288145 : Blo 1752577 25288145 := bstep (se 2 (by rfl) ⟨9483054, by rfl⟩ : syracuseStep 25288145 = 18966109) B18966109
theorem B1752583 : Blo 1752577 1752583 := bstep (se 1 (by rfl) ⟨1314437, by rfl⟩ : syracuseStep 1752583 = 2628875) B2628875
theorem B2629127 : Blo 1752577 2629127 := bstep (se 1 (by rfl) ⟨1971845, by rfl⟩ : syracuseStep 2629127 = 3943691) B3943691
theorem B1973767 : Blo 1752577 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B1752591 : Blo 1752577 1752591 := bstep (se 1 (by rfl) ⟨1314443, by rfl⟩ : syracuseStep 1752591 = 2628887) B2628887
theorem B2629163 : Blo 1752577 2629163 := bstep (se 1 (by rfl) ⟨1971872, by rfl⟩ : syracuseStep 2629163 = 3943745) B3943745
theorem B1752635 : Blo 1752577 1752635 := bstep (se 1 (by rfl) ⟨1314476, by rfl⟩ : syracuseStep 1752635 = 2628953) B2628953
theorem B2629193 : Blo 1752577 2629193 := bstep (se 2 (by rfl) ⟨985947, by rfl⟩ : syracuseStep 2629193 = 1971895) B1971895
theorem B1752711 : Blo 1752577 1752711 := bstep (se 1 (by rfl) ⟨1314533, by rfl⟩ : syracuseStep 1752711 = 2629067) B2629067
theorem B1752719 : Blo 1752577 1752719 := bstep (se 1 (by rfl) ⟨1314539, by rfl⟩ : syracuseStep 1752719 = 2629079) B2629079
theorem B2219663 : Blo 1752577 2219663 := bstep (se 1 (by rfl) ⟨1664747, by rfl⟩ : syracuseStep 2219663 = 3329495) B3329495
theorem B3038905 : Blo 1752577 3038905 := bstep (se 2 (by rfl) ⟨1139589, by rfl⟩ : syracuseStep 3038905 = 2279179) B2279179
theorem B1752763 : Blo 1752577 1752763 := bstep (se 1 (by rfl) ⟨1314572, by rfl⟩ : syracuseStep 1752763 = 2629145) B2629145
theorem B2629307 : Blo 1752577 2629307 := bstep (se 1 (by rfl) ⟨1971980, by rfl⟩ : syracuseStep 2629307 = 3943961) B3943961
theorem B2629367 : Blo 1752577 2629367 := bstep (se 1 (by rfl) ⟨1972025, by rfl⟩ : syracuseStep 2629367 = 3944051) B3944051
theorem B1752839 : Blo 1752577 1752839 := bstep (se 1 (by rfl) ⟨1314629, by rfl⟩ : syracuseStep 1752839 = 2629259) B2629259
theorem B1752847 : Blo 1752577 1752847 := bstep (se 1 (by rfl) ⟨1314635, by rfl⟩ : syracuseStep 1752847 = 2629271) B2629271
theorem B2629391 : Blo 1752577 2629391 := bstep (se 1 (by rfl) ⟨1972043, by rfl⟩ : syracuseStep 2629391 = 3944087) B3944087
theorem B2629433 : Blo 1752577 2629433 := bstep (se 2 (by rfl) ⟨986037, by rfl⟩ : syracuseStep 2629433 = 1972075) B1972075
theorem B1752891 : Blo 1752577 1752891 := bstep (se 1 (by rfl) ⟨1314668, by rfl⟩ : syracuseStep 1752891 = 2629337) B2629337
theorem B14983001 : Blo 1752577 14983001 := bstep (se 2 (by rfl) ⟨5618625, by rfl⟩ : syracuseStep 14983001 = 11237251) B11237251
theorem B1752967 : Blo 1752577 1752967 := bstep (se 1 (by rfl) ⟨1314725, by rfl⟩ : syracuseStep 1752967 = 2629451) B2629451
theorem B2629511 : Blo 1752577 2629511 := bstep (se 1 (by rfl) ⟨1972133, by rfl⟩ : syracuseStep 2629511 = 3944267) B3944267
theorem B1752975 : Blo 1752577 1752975 := bstep (se 1 (by rfl) ⟨1314731, by rfl⟩ : syracuseStep 1752975 = 2629463) B2629463
theorem B2629547 : Blo 1752577 2629547 := bstep (se 1 (by rfl) ⟨1972160, by rfl⟩ : syracuseStep 2629547 = 3944321) B3944321
theorem B1753019 : Blo 1752577 1753019 := bstep (se 1 (by rfl) ⟨1314764, by rfl⟩ : syracuseStep 1753019 = 2629529) B2629529
theorem B2629577 : Blo 1752577 2629577 := bstep (se 2 (by rfl) ⟨986091, by rfl⟩ : syracuseStep 2629577 = 1972183) B1972183
theorem B2809865 : Blo 1752577 2809865 := bstep (se 2 (by rfl) ⟨1053699, by rfl⟩ : syracuseStep 2809865 = 2107399) B2107399
theorem B1753127 : Blo 1752577 1753127 := bstep (se 1 (by rfl) ⟨1314845, by rfl⟩ : syracuseStep 1753127 = 2629691) B2629691
theorem B1753167 : Blo 1752577 1753167 := bstep (se 1 (by rfl) ⟨1314875, by rfl⟩ : syracuseStep 1753167 = 2629751) B2629751
theorem B1753183 : Blo 1752577 1753183 := bstep (se 1 (by rfl) ⟨1314887, by rfl⟩ : syracuseStep 1753183 = 2629775) B2629775
theorem B1753211 : Blo 1752577 1753211 := bstep (se 1 (by rfl) ⟨1314908, by rfl⟩ : syracuseStep 1753211 = 2629817) B2629817
theorem B14221469 : Blo 1752577 14221469 := bstep (se 3 (by rfl) ⟨2666525, by rfl⟩ : syracuseStep 14221469 = 5333051) B5333051
theorem B1753263 : Blo 1752577 1753263 := bstep (se 1 (by rfl) ⟨1314947, by rfl⟩ : syracuseStep 1753263 = 2629895) B2629895
theorem B1753287 : Blo 1752577 1753287 := bstep (se 1 (by rfl) ⟨1314965, by rfl⟩ : syracuseStep 1753287 = 2629931) B2629931
theorem B1753307 : Blo 1752577 1753307 := bstep (se 1 (by rfl) ⟨1314980, by rfl⟩ : syracuseStep 1753307 = 2629961) B2629961
theorem B1753383 : Blo 1752577 1753383 := bstep (se 1 (by rfl) ⟨1315037, by rfl⟩ : syracuseStep 1753383 = 2630075) B2630075
theorem B1753423 : Blo 1752577 1753423 := bstep (se 1 (by rfl) ⟨1315067, by rfl⟩ : syracuseStep 1753423 = 2630135) B2630135
theorem B1753439 : Blo 1752577 1753439 := bstep (se 1 (by rfl) ⟨1315079, by rfl⟩ : syracuseStep 1753439 = 2630159) B2630159
theorem B1753467 : Blo 1752577 1753467 := bstep (se 1 (by rfl) ⟨1315100, by rfl⟩ : syracuseStep 1753467 = 2630201) B2630201
theorem B1999279 : Blo 1752577 1999279 := bstep (se 1 (by rfl) ⟨1499459, by rfl⟩ : syracuseStep 1999279 = 2998919) B2998919
theorem B2630063 : Blo 1752577 2630063 := bstep (se 1 (by rfl) ⟨1972547, by rfl⟩ : syracuseStep 2630063 = 3945095) B3945095
theorem B1753519 : Blo 1752577 1753519 := bstep (se 1 (by rfl) ⟨1315139, by rfl⟩ : syracuseStep 1753519 = 2630279) B2630279
theorem B2220463 : Blo 1752577 2220463 := bstep (se 1 (by rfl) ⟨1665347, by rfl⟩ : syracuseStep 2220463 = 3330695) B3330695
theorem B2957755 : Blo 1752577 2957755 := bstep (se 1 (by rfl) ⟨2218316, by rfl⟩ : syracuseStep 2957755 = 4436633) B4436633
theorem B1753543 : Blo 1752577 1753543 := bstep (se 1 (by rfl) ⟨1315157, by rfl⟩ : syracuseStep 1753543 = 2630315) B2630315
theorem B53977553 : Blo 1752577 53977553 := bstep (se 2 (by rfl) ⟨20241582, by rfl⟩ : syracuseStep 53977553 = 40483165) B40483165
theorem B1753563 : Blo 1752577 1753563 := bstep (se 1 (by rfl) ⟨1315172, by rfl⟩ : syracuseStep 1753563 = 2630345) B2630345
theorem B28828163 : Blo 1752577 28828163 := bstep (se 1 (by rfl) ⟨21621122, by rfl⟩ : syracuseStep 28828163 = 43242245) B43242245
theorem B2630153 : Blo 1752577 2630153 := bstep (se 2 (by rfl) ⟨986307, by rfl⟩ : syracuseStep 2630153 = 1972615) B1972615
theorem B2957863 : Blo 1752577 2957863 := bstep (se 1 (by rfl) ⟨2218397, by rfl⟩ : syracuseStep 2957863 = 4436795) B4436795
theorem B2630183 : Blo 1752577 2630183 := bstep (se 1 (by rfl) ⟨1972637, by rfl⟩ : syracuseStep 2630183 = 3945275) B3945275
theorem B1753639 : Blo 1752577 1753639 := bstep (se 1 (by rfl) ⟨1315229, by rfl⟩ : syracuseStep 1753639 = 2630459) B2630459
theorem B1753679 : Blo 1752577 1753679 := bstep (se 1 (by rfl) ⟨1315259, by rfl⟩ : syracuseStep 1753679 = 2630519) B2630519
theorem B1753695 : Blo 1752577 1753695 := bstep (se 1 (by rfl) ⟨1315271, by rfl⟩ : syracuseStep 1753695 = 2630543) B2630543
theorem B5997179 : Blo 1752577 5997179 := bstep (se 1 (by rfl) ⟨4497884, by rfl⟩ : syracuseStep 5997179 = 8995769) B8995769
theorem B2630267 : Blo 1752577 2630267 := bstep (se 1 (by rfl) ⟨1972700, by rfl⟩ : syracuseStep 2630267 = 3945401) B3945401
theorem B1753723 : Blo 1752577 1753723 := bstep (se 1 (by rfl) ⟨1315292, by rfl⟩ : syracuseStep 1753723 = 2630585) B2630585
theorem B1753775 : Blo 1752577 1753775 := bstep (se 1 (by rfl) ⟨1315331, by rfl⟩ : syracuseStep 1753775 = 2630663) B2630663
theorem B5915321 : Blo 1752577 5915321 := bstep (se 2 (by rfl) ⟨2218245, by rfl⟩ : syracuseStep 5915321 = 4436491) B4436491
theorem B1753799 : Blo 1752577 1753799 := bstep (se 1 (by rfl) ⟨1315349, by rfl⟩ : syracuseStep 1753799 = 2630699) B2630699
theorem B20243155 : Blo 1752577 20243155 := bstep (se 1 (by rfl) ⟨15182366, by rfl⟩ : syracuseStep 20243155 = 30364733) B30364733
theorem B1753819 : Blo 1752577 1753819 := bstep (se 1 (by rfl) ⟨1315364, by rfl⟩ : syracuseStep 1753819 = 2630729) B2630729
theorem B2630393 : Blo 1752577 2630393 := bstep (se 2 (by rfl) ⟨986397, by rfl⟩ : syracuseStep 2630393 = 1972795) B1972795
theorem B1753895 : Blo 1752577 1753895 := bstep (se 1 (by rfl) ⟨1315421, by rfl⟩ : syracuseStep 1753895 = 2630843) B2630843
theorem B1753935 : Blo 1752577 1753935 := bstep (se 1 (by rfl) ⟨1315451, by rfl⟩ : syracuseStep 1753935 = 2630903) B2630903
theorem B2630495 : Blo 1752577 2630495 := bstep (se 1 (by rfl) ⟨1972871, by rfl⟩ : syracuseStep 2630495 = 3945743) B3945743
theorem B1753951 : Blo 1752577 1753951 := bstep (se 1 (by rfl) ⟨1315463, by rfl⟩ : syracuseStep 1753951 = 2630927) B2630927
theorem B2958187 : Blo 1752577 2958187 := bstep (se 1 (by rfl) ⟨2218640, by rfl⟩ : syracuseStep 2958187 = 4437281) B4437281
theorem B2630507 : Blo 1752577 2630507 := bstep (se 1 (by rfl) ⟨1972880, by rfl⟩ : syracuseStep 2630507 = 3945761) B3945761
theorem B1753979 : Blo 1752577 1753979 := bstep (se 1 (by rfl) ⟨1315484, by rfl⟩ : syracuseStep 1753979 = 2630969) B2630969
theorem B6661025 : Blo 1752577 6661025 := bstep (se 2 (by rfl) ⟨2497884, by rfl⟩ : syracuseStep 6661025 = 4995769) B4995769
theorem B6316975 : Blo 1752577 6316975 := bstep (se 1 (by rfl) ⟨4737731, by rfl⟩ : syracuseStep 6316975 = 9475463) B9475463
theorem B1754031 : Blo 1752577 1754031 := bstep (se 1 (by rfl) ⟨1315523, by rfl⟩ : syracuseStep 1754031 = 2631047) B2631047
theorem B4441007 : Blo 1752577 4441007 := bstep (se 1 (by rfl) ⟨3330755, by rfl⟩ : syracuseStep 4441007 = 6661511) B6661511
theorem B1754055 : Blo 1752577 1754055 := bstep (se 1 (by rfl) ⟨1315541, by rfl⟩ : syracuseStep 1754055 = 2631083) B2631083
theorem B48636875 : Blo 1752577 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B1754075 : Blo 1752577 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B15188957 : Blo 1752577 15188957 := bstep (se 3 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 15188957 = 5695859) B5695859
theorem B13312997 : Blo 1752577 13312997 := bstep (se 4 (by rfl) ⟨1248093, by rfl⟩ : syracuseStep 13312997 = 2496187) B2496187
theorem B8111105 : Blo 1752577 8111105 := bstep (se 2 (by rfl) ⟨3041664, by rfl⟩ : syracuseStep 8111105 = 6083329) B6083329
theorem B78996491 : Blo 1752577 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B1754151 : Blo 1752577 1754151 := bstep (se 1 (by rfl) ⟨1315613, by rfl⟩ : syracuseStep 1754151 = 2631227) B2631227
theorem B13321259 : Blo 1752577 13321259 := bstep (se 1 (by rfl) ⟨9990944, by rfl⟩ : syracuseStep 13321259 = 19981889) B19981889
theorem B2630735 : Blo 1752577 2630735 := bstep (se 1 (by rfl) ⟨1973051, by rfl⟩ : syracuseStep 2630735 = 3946103) B3946103
theorem B1754191 : Blo 1752577 1754191 := bstep (se 1 (by rfl) ⟨1315643, by rfl⟩ : syracuseStep 1754191 = 2631287) B2631287
theorem B1754207 : Blo 1752577 1754207 := bstep (se 1 (by rfl) ⟨1315655, by rfl⟩ : syracuseStep 1754207 = 2631311) B2631311
theorem B1754235 : Blo 1752577 1754235 := bstep (se 1 (by rfl) ⟨1315676, by rfl⟩ : syracuseStep 1754235 = 2631353) B2631353
theorem B7488683 : Blo 1752577 7488683 := bstep (se 1 (by rfl) ⟨5616512, by rfl⟩ : syracuseStep 7488683 = 11233025) B11233025
theorem B1754287 : Blo 1752577 1754287 := bstep (se 1 (by rfl) ⟨1315715, by rfl⟩ : syracuseStep 1754287 = 2631431) B2631431
theorem B2630855 : Blo 1752577 2630855 := bstep (se 1 (by rfl) ⟨1973141, by rfl⟩ : syracuseStep 2630855 = 3946283) B3946283
theorem B1754311 : Blo 1752577 1754311 := bstep (se 1 (by rfl) ⟨1315733, by rfl⟩ : syracuseStep 1754311 = 2631467) B2631467
theorem B1754331 : Blo 1752577 1754331 := bstep (se 1 (by rfl) ⟨1315748, by rfl⟩ : syracuseStep 1754331 = 2631497) B2631497
theorem B5915915 : Blo 1752577 5915915 := bstep (se 1 (by rfl) ⟨4436936, by rfl⟩ : syracuseStep 5915915 = 8873873) B8873873
theorem B24331535 : Blo 1752577 24331535 := bstep (se 1 (by rfl) ⟨18248651, by rfl⟩ : syracuseStep 24331535 = 36497303) B36497303
theorem B1754407 : Blo 1752577 1754407 := bstep (se 1 (by rfl) ⟨1315805, by rfl⟩ : syracuseStep 1754407 = 2631611) B2631611
theorem B1754447 : Blo 1752577 1754447 := bstep (se 1 (by rfl) ⟨1315835, by rfl⟩ : syracuseStep 1754447 = 2631671) B2631671
theorem B1754463 : Blo 1752577 1754463 := bstep (se 1 (by rfl) ⟨1315847, by rfl⟩ : syracuseStep 1754463 = 2631695) B2631695
theorem B2999657 : Blo 1752577 2999657 := bstep (se 2 (by rfl) ⟨1124871, by rfl⟩ : syracuseStep 2999657 = 2249743) B2249743
theorem B2631017 : Blo 1752577 2631017 := bstep (se 2 (by rfl) ⟨986631, by rfl⟩ : syracuseStep 2631017 = 1973263) B1973263
theorem B25617779 : Blo 1752577 25617779 := bstep (se 1 (by rfl) ⟨19213334, by rfl⟩ : syracuseStep 25617779 = 38426669) B38426669
theorem B1754491 : Blo 1752577 1754491 := bstep (se 1 (by rfl) ⟨1315868, by rfl⟩ : syracuseStep 1754491 = 2631737) B2631737
theorem B1754543 : Blo 1752577 1754543 := bstep (se 1 (by rfl) ⟨1315907, by rfl⟩ : syracuseStep 1754543 = 2631815) B2631815
theorem B2631095 : Blo 1752577 2631095 := bstep (se 1 (by rfl) ⟨1973321, by rfl⟩ : syracuseStep 2631095 = 3946643) B3946643
theorem B1754567 : Blo 1752577 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B2631131 : Blo 1752577 2631131 := bstep (se 1 (by rfl) ⟨1973348, by rfl⟩ : syracuseStep 2631131 = 3946697) B3946697
theorem B8431091 : Blo 1752577 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B5916185 : Blo 1752577 5916185 := bstep (se 2 (by rfl) ⟨2218569, by rfl⟩ : syracuseStep 5916185 = 4437139) B4437139
theorem B8881811 : Blo 1752577 8881811 := bstep (se 1 (by rfl) ⟨6661358, by rfl⟩ : syracuseStep 8881811 = 13322717) B13322717
theorem B6317783 : Blo 1752577 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B3327817 : Blo 1752577 3327817 := bstep (se 2 (by rfl) ⟨1247931, by rfl⟩ : syracuseStep 3327817 = 2495863) B2495863
theorem B2959247 : Blo 1752577 2959247 := bstep (se 1 (by rfl) ⟨2219435, by rfl⟩ : syracuseStep 2959247 = 4438871) B4438871
theorem B2631599 : Blo 1752577 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B2631689 : Blo 1752577 2631689 := bstep (se 2 (by rfl) ⟨986883, by rfl⟩ : syracuseStep 2631689 = 1973767) B1973767
theorem B2631719 : Blo 1752577 2631719 := bstep (se 1 (by rfl) ⟨1973789, by rfl⟩ : syracuseStep 2631719 = 3947579) B3947579
theorem B10815569 : Blo 1752577 10815569 := bstep (se 2 (by rfl) ⟨4055838, by rfl⟩ : syracuseStep 10815569 = 8111677) B8111677
theorem B9988211 : Blo 1752577 9988211 := bstep (se 1 (by rfl) ⟨7491158, by rfl⟩ : syracuseStep 9988211 = 14982317) B14982317
theorem B2959483 : Blo 1752577 2959483 := bstep (se 1 (by rfl) ⟨2219612, by rfl⟩ : syracuseStep 2959483 = 4439225) B4439225
theorem B2631803 : Blo 1752577 2631803 := bstep (se 1 (by rfl) ⟨1973852, by rfl⟩ : syracuseStep 2631803 = 3947705) B3947705
theorem B6318233 : Blo 1752577 6318233 := bstep (se 2 (by rfl) ⟨2369337, by rfl⟩ : syracuseStep 6318233 = 4738675) B4738675
theorem B6080779 : Blo 1752577 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B22473065 : Blo 1752577 22473065 := bstep (se 2 (by rfl) ⟨8427399, by rfl⟩ : syracuseStep 22473065 = 16854799) B16854799
theorem B7997825 : Blo 1752577 7997825 := bstep (se 2 (by rfl) ⟨2999184, by rfl⟩ : syracuseStep 7997825 = 5998369) B5998369
theorem B3000719 : Blo 1752577 3000719 := bstep (se 1 (by rfl) ⟨2250539, by rfl⟩ : syracuseStep 3000719 = 4501079) B4501079
theorem B11856365 : Blo 1752577 11856365 := bstep (se 3 (by rfl) ⟨2223068, by rfl⟩ : syracuseStep 11856365 = 4446137) B4446137
theorem B7113203 : Blo 1752577 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B8874521 : Blo 1752577 8874521 := bstep (se 2 (by rfl) ⟨3327945, by rfl⟩ : syracuseStep 8874521 = 6655891) B6655891
theorem B9988667 : Blo 1752577 9988667 := bstep (se 1 (by rfl) ⟨7491500, by rfl⟩ : syracuseStep 9988667 = 14983001) B14983001
theorem B5917319 : Blo 1752577 5917319 := bstep (se 1 (by rfl) ⟨4437989, by rfl⟩ : syracuseStep 5917319 = 8875979) B8875979
theorem B5917373 : Blo 1752577 5917373 := bstep (se 3 (by rfl) ⟨1109507, by rfl⟩ : syracuseStep 5917373 = 2219015) B2219015
theorem B11234051 : Blo 1752577 11234051 := bstep (se 1 (by rfl) ⟨8425538, by rfl⟩ : syracuseStep 11234051 = 16851077) B16851077
theorem B5917535 : Blo 1752577 5917535 := bstep (se 1 (by rfl) ⟨4438151, by rfl⟩ : syracuseStep 5917535 = 8876303) B8876303
theorem B2960347 : Blo 1752577 2960347 := bstep (se 1 (by rfl) ⟨2220260, by rfl⟩ : syracuseStep 2960347 = 4440521) B4440521
theorem B5917697 : Blo 1752577 5917697 := bstep (se 2 (by rfl) ⟨2219136, by rfl⟩ : syracuseStep 5917697 = 4438273) B4438273
theorem B6655223 : Blo 1752577 6655223 := bstep (se 1 (by rfl) ⟨4991417, by rfl⟩ : syracuseStep 6655223 = 9982835) B9982835
theorem B12004645 : Blo 1752577 12004645 := bstep (se 4 (by rfl) ⟨1125435, by rfl⟩ : syracuseStep 12004645 = 2250871) B2250871
theorem B3944033 : Blo 1752577 3944033 := bstep (se 2 (by rfl) ⟨1479012, by rfl⟩ : syracuseStep 3944033 = 2958025) B2958025
theorem B9981629 : Blo 1752577 9981629 := bstep (se 3 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 9981629 = 3743111) B3743111
theorem B5918507 : Blo 1752577 5918507 := bstep (se 1 (by rfl) ⟨4438880, by rfl⟩ : syracuseStep 5918507 = 8877761) B8877761
theorem B3944375 : Blo 1752577 3944375 := bstep (se 1 (by rfl) ⟨2958281, by rfl⟩ : syracuseStep 3944375 = 5916563) B5916563
theorem B8425403 : Blo 1752577 8425403 := bstep (se 1 (by rfl) ⟨6319052, by rfl⟩ : syracuseStep 8425403 = 12638105) B12638105
theorem B3330011 : Blo 1752577 3330011 := bstep (se 1 (by rfl) ⟨2497508, by rfl⟩ : syracuseStep 3330011 = 4995017) B4995017
theorem B5918777 : Blo 1752577 5918777 := bstep (se 2 (by rfl) ⟨2219541, by rfl⟩ : syracuseStep 5918777 = 4439083) B4439083
theorem B4993103 : Blo 1752577 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B6656195 : Blo 1752577 6656195 := bstep (se 1 (by rfl) ⟨4992146, by rfl⟩ : syracuseStep 6656195 = 9984293) B9984293
theorem B3330247 : Blo 1752577 3330247 := bstep (se 1 (by rfl) ⟨2497685, by rfl⟩ : syracuseStep 3330247 = 4995371) B4995371
theorem B33689915 : Blo 1752577 33689915 := bstep (se 1 (by rfl) ⟨25267436, by rfl⟩ : syracuseStep 33689915 = 50534873) B50534873
theorem B22475069 : Blo 1752577 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B4436329 : Blo 1752577 4436329 := bstep (se 2 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 4436329 = 3327247) B3327247
theorem B5919101 : Blo 1752577 5919101 := bstep (se 3 (by rfl) ⟨1109831, by rfl⟩ : syracuseStep 5919101 = 2219663) B2219663
theorem B14414213 : Blo 1752577 14414213 := bstep (se 4 (by rfl) ⟨1351332, by rfl⟩ : syracuseStep 14414213 = 2702665) B2702665
theorem B3944969 : Blo 1752577 3944969 := bstep (se 2 (by rfl) ⟨1479363, by rfl⟩ : syracuseStep 3944969 = 2958727) B2958727
theorem B4436603 : Blo 1752577 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B6656651 : Blo 1752577 6656651 := bstep (se 1 (by rfl) ⟨4992488, by rfl⟩ : syracuseStep 6656651 = 9984977) B9984977
theorem B5919371 : Blo 1752577 5919371 := bstep (se 1 (by rfl) ⟨4439528, by rfl⟩ : syracuseStep 5919371 = 8879057) B8879057
theorem B2847403 : Blo 1752577 2847403 := bstep (se 1 (by rfl) ⟨2135552, by rfl⟩ : syracuseStep 2847403 = 4271105) B4271105
theorem B40506065 : Blo 1752577 40506065 := bstep (se 2 (by rfl) ⟨15189774, by rfl⟩ : syracuseStep 40506065 = 30379549) B30379549
theorem B3158777 : Blo 1752577 3158777 := bstep (se 2 (by rfl) ⟨1184541, by rfl⟩ : syracuseStep 3158777 = 2369083) B2369083
theorem B6656863 : Blo 1752577 6656863 := bstep (se 1 (by rfl) ⟨4992647, by rfl⟩ : syracuseStep 6656863 = 9985295) B9985295
theorem B3945311 : Blo 1752577 3945311 := bstep (se 1 (by rfl) ⟨2958983, by rfl⟩ : syracuseStep 3945311 = 5917967) B5917967
theorem B4051873 : Blo 1752577 4051873 := bstep (se 2 (by rfl) ⟨1519452, by rfl⟩ : syracuseStep 4051873 = 3038905) B3038905
theorem B4215739 : Blo 1752577 4215739 := bstep (se 1 (by rfl) ⟨3161804, by rfl⟩ : syracuseStep 4215739 = 6323609) B6323609
theorem B16856029 : Blo 1752577 16856029 := bstep (se 3 (by rfl) ⟨3160505, by rfl⟩ : syracuseStep 16856029 = 6321011) B6321011
theorem B50541569 : Blo 1752577 50541569 := bstep (se 2 (by rfl) ⟨18953088, by rfl⟩ : syracuseStep 50541569 = 37906177) B37906177
theorem B3945491 : Blo 1752577 3945491 := bstep (se 1 (by rfl) ⟨2959118, by rfl⟩ : syracuseStep 3945491 = 5918237) B5918237
theorem B6321347 : Blo 1752577 6321347 := bstep (se 1 (by rfl) ⟨4741010, by rfl⟩ : syracuseStep 6321347 = 9482021) B9482021
theorem B3945833 : Blo 1752577 3945833 := bstep (se 2 (by rfl) ⟨1479687, by rfl⟩ : syracuseStep 3945833 = 2959375) B2959375
theorem B8877437 : Blo 1752577 8877437 := bstep (se 3 (by rfl) ⟨1664519, by rfl⟩ : syracuseStep 8877437 = 3329039) B3329039
theorem B7493107 : Blo 1752577 7493107 := bstep (se 1 (by rfl) ⟨5619830, by rfl⟩ : syracuseStep 7493107 = 11239661) B11239661
theorem B4994585 : Blo 1752577 4994585 := bstep (se 2 (by rfl) ⟨1872969, by rfl⟩ : syracuseStep 4994585 = 3745939) B3745939
theorem B5920289 : Blo 1752577 5920289 := bstep (se 2 (by rfl) ⟨2220108, by rfl⟩ : syracuseStep 5920289 = 4440217) B4440217
theorem B1971751 : Blo 1752577 1971751 := bstep (se 1 (by rfl) ⟨1478813, by rfl⟩ : syracuseStep 1971751 = 2957627) B2957627
theorem B2496199 : Blo 1752577 2496199 := bstep (se 1 (by rfl) ⟨1872149, by rfl⟩ : syracuseStep 2496199 = 3744299) B3744299
theorem B5920505 : Blo 1752577 5920505 := bstep (se 2 (by rfl) ⟨2220189, by rfl⟩ : syracuseStep 5920505 = 4440379) B4440379
theorem B6657821 : Blo 1752577 6657821 := bstep (se 3 (by rfl) ⟨1248341, by rfl⟩ : syracuseStep 6657821 = 2496683) B2496683
theorem B6657835 : Blo 1752577 6657835 := bstep (se 1 (by rfl) ⟨4993376, by rfl⟩ : syracuseStep 6657835 = 9986753) B9986753
theorem B14989151 : Blo 1752577 14989151 := bstep (se 1 (by rfl) ⟨11241863, by rfl⟩ : syracuseStep 14989151 = 22483727) B22483727
theorem B3946427 : Blo 1752577 3946427 := bstep (se 1 (by rfl) ⟨2959820, by rfl⟩ : syracuseStep 3946427 = 5919641) B5919641
theorem B5920775 : Blo 1752577 5920775 := bstep (se 1 (by rfl) ⟨4440581, by rfl⟩ : syracuseStep 5920775 = 8881163) B8881163
theorem B3946553 : Blo 1752577 3946553 := bstep (se 2 (by rfl) ⟨1479957, by rfl⟩ : syracuseStep 3946553 = 2959915) B2959915
theorem B5920883 : Blo 1752577 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B25286813 : Blo 1752577 25286813 := bstep (se 3 (by rfl) ⟨4741277, by rfl⟩ : syracuseStep 25286813 = 9482555) B9482555
theorem B3602603 : Blo 1752577 3602603 := bstep (se 1 (by rfl) ⟨2701952, by rfl⟩ : syracuseStep 3602603 = 5403905) B5403905
theorem B5921153 : Blo 1752577 5921153 := bstep (se 2 (by rfl) ⟨2220432, by rfl⟩ : syracuseStep 5921153 = 4440865) B4440865
theorem B4438415 : Blo 1752577 4438415 := bstep (se 1 (by rfl) ⟨3328811, by rfl⟩ : syracuseStep 4438415 = 6657623) B6657623
theorem B3160463 : Blo 1752577 3160463 := bstep (se 1 (by rfl) ⟨2370347, by rfl⟩ : syracuseStep 3160463 = 4740695) B4740695
theorem B3946895 : Blo 1752577 3946895 := bstep (se 1 (by rfl) ⟨2960171, by rfl⟩ : syracuseStep 3946895 = 5920343) B5920343
theorem B2218423 : Blo 1752577 2218423 := bstep (se 1 (by rfl) ⟨1663817, by rfl⟩ : syracuseStep 2218423 = 3327635) B3327635
theorem B9984545 : Blo 1752577 9984545 := bstep (se 2 (by rfl) ⟨3744204, by rfl⟩ : syracuseStep 9984545 = 7488409) B7488409
theorem B2808359 : Blo 1752577 2808359 := bstep (se 1 (by rfl) ⟨2106269, by rfl⟩ : syracuseStep 2808359 = 4212539) B4212539
theorem B17087021 : Blo 1752577 17087021 := bstep (se 3 (by rfl) ⟨3203816, by rfl⟩ : syracuseStep 17087021 = 6407633) B6407633
theorem B12638855 : Blo 1752577 12638855 := bstep (se 1 (by rfl) ⟨9479141, by rfl⟩ : syracuseStep 12638855 = 18958283) B18958283
theorem B13318829 : Blo 1752577 13318829 := bstep (se 3 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 13318829 = 4994561) B4994561
theorem B5692103 : Blo 1752577 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B4438739 : Blo 1752577 4438739 := bstep (se 1 (by rfl) ⟨3329054, by rfl⟩ : syracuseStep 4438739 = 6658109) B6658109
theorem B3947219 : Blo 1752577 3947219 := bstep (se 1 (by rfl) ⟨2960414, by rfl⟩ : syracuseStep 3947219 = 5920829) B5920829
theorem B91151119 : Blo 1752577 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B11238173 : Blo 1752577 11238173 := bstep (se 3 (by rfl) ⟨2107157, by rfl⟩ : syracuseStep 11238173 = 4214315) B4214315
theorem B3160939 : Blo 1752577 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B1973371 : Blo 1752577 1973371 := bstep (se 1 (by rfl) ⟨1480028, by rfl⟩ : syracuseStep 1973371 = 2960057) B2960057
theorem B11230487 : Blo 1752577 11230487 := bstep (se 1 (by rfl) ⟨8422865, by rfl⟩ : syracuseStep 11230487 = 16845731) B16845731
theorem B2628959 : Blo 1752577 2628959 := bstep (se 1 (by rfl) ⟨1971719, by rfl⟩ : syracuseStep 2628959 = 3943439) B3943439
theorem B2628971 : Blo 1752577 2628971 := bstep (se 1 (by rfl) ⟨1971728, by rfl⟩ : syracuseStep 2628971 = 3943457) B3943457
theorem B3743119 : Blo 1752577 3743119 := bstep (se 1 (by rfl) ⟨2807339, by rfl⟩ : syracuseStep 3743119 = 5614679) B5614679
theorem B7486921 : Blo 1752577 7486921 := bstep (se 2 (by rfl) ⟨2807595, by rfl⟩ : syracuseStep 7486921 = 5615191) B5615191
theorem B1752615 : Blo 1752577 1752615 := bstep (se 1 (by rfl) ⟨1314461, by rfl⟩ : syracuseStep 1752615 = 2628923) B2628923
theorem B1752655 : Blo 1752577 1752655 := bstep (se 1 (by rfl) ⟨1314491, by rfl⟩ : syracuseStep 1752655 = 2628983) B2628983
theorem B2629199 : Blo 1752577 2629199 := bstep (se 1 (by rfl) ⟨1971899, by rfl⟩ : syracuseStep 2629199 = 3943799) B3943799
theorem B1973839 : Blo 1752577 1973839 := bstep (se 1 (by rfl) ⟨1480379, by rfl⟩ : syracuseStep 1973839 = 2960759) B2960759
theorem B1752671 : Blo 1752577 1752671 := bstep (se 1 (by rfl) ⟨1314503, by rfl⟩ : syracuseStep 1752671 = 2629007) B2629007
theorem B1752699 : Blo 1752577 1752699 := bstep (se 1 (by rfl) ⟨1314524, by rfl⟩ : syracuseStep 1752699 = 2629049) B2629049
theorem B16858763 : Blo 1752577 16858763 := bstep (se 1 (by rfl) ⟨12644072, by rfl⟩ : syracuseStep 16858763 = 25288145) B25288145
theorem B1752751 : Blo 1752577 1752751 := bstep (se 1 (by rfl) ⟨1314563, by rfl⟩ : syracuseStep 1752751 = 2629127) B2629127
theorem B1752775 : Blo 1752577 1752775 := bstep (se 1 (by rfl) ⟨1314581, by rfl⟩ : syracuseStep 1752775 = 2629163) B2629163
theorem B2629319 : Blo 1752577 2629319 := bstep (se 1 (by rfl) ⟨1971989, by rfl⟩ : syracuseStep 2629319 = 3943979) B3943979
theorem B2219719 : Blo 1752577 2219719 := bstep (se 1 (by rfl) ⟨1664789, by rfl⟩ : syracuseStep 2219719 = 3329579) B3329579
theorem B9985751 : Blo 1752577 9985751 := bstep (se 1 (by rfl) ⟨7489313, by rfl⟩ : syracuseStep 9985751 = 14978627) B14978627
theorem B1752795 : Blo 1752577 1752795 := bstep (se 1 (by rfl) ⟨1314596, by rfl⟩ : syracuseStep 1752795 = 2629193) B2629193
theorem B60767981 : Blo 1752577 60767981 := bstep (se 3 (by rfl) ⟨11393996, by rfl⟩ : syracuseStep 60767981 = 22787993) B22787993
theorem B1752871 : Blo 1752577 1752871 := bstep (se 1 (by rfl) ⟨1314653, by rfl⟩ : syracuseStep 1752871 = 2629307) B2629307
theorem B1752911 : Blo 1752577 1752911 := bstep (se 1 (by rfl) ⟨1314683, by rfl⟩ : syracuseStep 1752911 = 2629367) B2629367
theorem B1752927 : Blo 1752577 1752927 := bstep (se 1 (by rfl) ⟨1314695, by rfl⟩ : syracuseStep 1752927 = 2629391) B2629391
theorem B2629481 : Blo 1752577 2629481 := bstep (se 2 (by rfl) ⟨986055, by rfl⟩ : syracuseStep 2629481 = 1972111) B1972111
theorem B1752955 : Blo 1752577 1752955 := bstep (se 1 (by rfl) ⟨1314716, by rfl⟩ : syracuseStep 1752955 = 2629433) B2629433
theorem B1753007 : Blo 1752577 1753007 := bstep (se 1 (by rfl) ⟨1314755, by rfl⟩ : syracuseStep 1753007 = 2629511) B2629511
theorem B2629559 : Blo 1752577 2629559 := bstep (se 1 (by rfl) ⟨1972169, by rfl⟩ : syracuseStep 2629559 = 3944339) B3944339
theorem B1753031 : Blo 1752577 1753031 := bstep (se 1 (by rfl) ⟨1314773, by rfl⟩ : syracuseStep 1753031 = 2629547) B2629547
theorem B1753051 : Blo 1752577 1753051 := bstep (se 1 (by rfl) ⟨1314788, by rfl⟩ : syracuseStep 1753051 = 2629577) B2629577
theorem B2629595 : Blo 1752577 2629595 := bstep (se 1 (by rfl) ⟨1972196, by rfl⟩ : syracuseStep 2629595 = 3944393) B3944393
theorem B14983379 : Blo 1752577 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B9609475 : Blo 1752577 9609475 := bstep (se 1 (by rfl) ⟨7207106, by rfl⟩ : syracuseStep 9609475 = 14414213) B14414213
theorem B4440329 : Blo 1752577 4440329 := bstep (se 2 (by rfl) ⟨1665123, by rfl⟩ : syracuseStep 4440329 = 3330247) B3330247
theorem B1753375 : Blo 1752577 1753375 := bstep (se 1 (by rfl) ⟨1315031, by rfl⟩ : syracuseStep 1753375 = 2630063) B2630063
theorem B2629979 : Blo 1752577 2629979 := bstep (se 1 (by rfl) ⟨1972484, by rfl⟩ : syracuseStep 2629979 = 3944969) B3944969
theorem B1753435 : Blo 1752577 1753435 := bstep (se 1 (by rfl) ⟨1315076, by rfl⟩ : syracuseStep 1753435 = 2630153) B2630153
theorem B1753455 : Blo 1752577 1753455 := bstep (se 1 (by rfl) ⟨1315091, by rfl⟩ : syracuseStep 1753455 = 2630183) B2630183
theorem B2957735 : Blo 1752577 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B3998119 : Blo 1752577 3998119 := bstep (se 1 (by rfl) ⟨2998589, by rfl⟩ : syracuseStep 3998119 = 5997179) B5997179
theorem B1753511 : Blo 1752577 1753511 := bstep (se 1 (by rfl) ⟨1315133, by rfl⟩ : syracuseStep 1753511 = 2630267) B2630267
theorem B5915105 : Blo 1752577 5915105 := bstep (se 2 (by rfl) ⟨2218164, by rfl⟩ : syracuseStep 5915105 = 4436329) B4436329
theorem B2105851 : Blo 1752577 2105851 := bstep (se 1 (by rfl) ⟨1579388, by rfl⟩ : syracuseStep 2105851 = 3158777) B3158777
theorem B1753595 : Blo 1752577 1753595 := bstep (se 1 (by rfl) ⟨1315196, by rfl⟩ : syracuseStep 1753595 = 2630393) B2630393
theorem B2630207 : Blo 1752577 2630207 := bstep (se 1 (by rfl) ⟨1972655, by rfl⟩ : syracuseStep 2630207 = 3945311) B3945311
theorem B1753663 : Blo 1752577 1753663 := bstep (se 1 (by rfl) ⟨1315247, by rfl⟩ : syracuseStep 1753663 = 2630495) B2630495
theorem B1753671 : Blo 1752577 1753671 := bstep (se 1 (by rfl) ⟨1315253, by rfl⟩ : syracuseStep 1753671 = 2630507) B2630507
theorem B2957897 : Blo 1752577 2957897 := bstep (se 2 (by rfl) ⟨1109211, by rfl⟩ : syracuseStep 2957897 = 2218423) B2218423
theorem B4440683 : Blo 1752577 4440683 := bstep (se 1 (by rfl) ⟨3330512, by rfl⟩ : syracuseStep 4440683 = 6661025) B6661025
theorem B32424583 : Blo 1752577 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B10125971 : Blo 1752577 10125971 := bstep (se 1 (by rfl) ⟨7594478, by rfl⟩ : syracuseStep 10125971 = 15188957) B15188957
theorem B33694379 : Blo 1752577 33694379 := bstep (se 1 (by rfl) ⟨25270784, by rfl⟩ : syracuseStep 33694379 = 50541569) B50541569
theorem B5407403 : Blo 1752577 5407403 := bstep (se 1 (by rfl) ⟨4055552, by rfl⟩ : syracuseStep 5407403 = 8111105) B8111105
theorem B2630327 : Blo 1752577 2630327 := bstep (se 1 (by rfl) ⟨1972745, by rfl⟩ : syracuseStep 2630327 = 3945491) B3945491
theorem B8880839 : Blo 1752577 8880839 := bstep (se 1 (by rfl) ⟨6660629, by rfl⟩ : syracuseStep 8880839 = 13321259) B13321259
theorem B1753823 : Blo 1752577 1753823 := bstep (se 1 (by rfl) ⟨1315367, by rfl⟩ : syracuseStep 1753823 = 2630735) B2630735
theorem B1753903 : Blo 1752577 1753903 := bstep (se 1 (by rfl) ⟨1315427, by rfl⟩ : syracuseStep 1753903 = 2630855) B2630855
theorem B16221023 : Blo 1752577 16221023 := bstep (se 1 (by rfl) ⟨12165767, by rfl⟩ : syracuseStep 16221023 = 24331535) B24331535
theorem B1999771 : Blo 1752577 1999771 := bstep (se 1 (by rfl) ⟨1499828, by rfl⟩ : syracuseStep 1999771 = 2999657) B2999657
theorem B2630555 : Blo 1752577 2630555 := bstep (se 1 (by rfl) ⟨1972916, by rfl⟩ : syracuseStep 2630555 = 3945833) B3945833
theorem B1754011 : Blo 1752577 1754011 := bstep (se 1 (by rfl) ⟨1315508, by rfl⟩ : syracuseStep 1754011 = 2631017) B2631017
theorem B1754063 : Blo 1752577 1754063 := bstep (se 1 (by rfl) ⟨1315547, by rfl⟩ : syracuseStep 1754063 = 2631095) B2631095
theorem B1754087 : Blo 1752577 1754087 := bstep (se 1 (by rfl) ⟨1315565, by rfl⟩ : syracuseStep 1754087 = 2631131) B2631131
theorem B5620727 : Blo 1752577 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B4211855 : Blo 1752577 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B8422633 : Blo 1752577 8422633 := bstep (se 2 (by rfl) ⟨3158487, by rfl⟩ : syracuseStep 8422633 = 6316975) B6316975
theorem B5620985 : Blo 1752577 5620985 := bstep (se 2 (by rfl) ⟨2107869, by rfl⟩ : syracuseStep 5620985 = 4215739) B4215739
theorem B1754399 : Blo 1752577 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B2630951 : Blo 1752577 2630951 := bstep (se 1 (by rfl) ⟨1973213, by rfl⟩ : syracuseStep 2630951 = 3946427) B3946427
theorem B1754459 : Blo 1752577 1754459 := bstep (se 1 (by rfl) ⟨1315844, by rfl⟩ : syracuseStep 1754459 = 2631689) B2631689
theorem B76875101 : Blo 1752577 76875101 := bstep (se 3 (by rfl) ⟨14414081, by rfl⟩ : syracuseStep 76875101 = 28828163) B28828163
theorem B1754479 : Blo 1752577 1754479 := bstep (se 1 (by rfl) ⟨1315859, by rfl⟩ : syracuseStep 1754479 = 2631719) B2631719
theorem B2631035 : Blo 1752577 2631035 := bstep (se 1 (by rfl) ⟨1973276, by rfl⟩ : syracuseStep 2631035 = 3946553) B3946553
theorem B7210379 : Blo 1752577 7210379 := bstep (se 1 (by rfl) ⟨5407784, by rfl⟩ : syracuseStep 7210379 = 10815569) B10815569
theorem B1754535 : Blo 1752577 1754535 := bstep (se 1 (by rfl) ⟨1315901, by rfl⟩ : syracuseStep 1754535 = 2631803) B2631803
theorem B4212155 : Blo 1752577 4212155 := bstep (se 1 (by rfl) ⟨3159116, by rfl⟩ : syracuseStep 4212155 = 6318233) B6318233
theorem B2401735 : Blo 1752577 2401735 := bstep (se 1 (by rfl) ⟨1801301, by rfl⟩ : syracuseStep 2401735 = 3602603) B3602603
theorem B2631161 : Blo 1752577 2631161 := bstep (se 2 (by rfl) ⟨986685, by rfl⟩ : syracuseStep 2631161 = 1973371) B1973371
theorem B2958943 : Blo 1752577 2958943 := bstep (se 1 (by rfl) ⟨2219207, by rfl⟩ : syracuseStep 2958943 = 4438415) B4438415
theorem B2631263 : Blo 1752577 2631263 := bstep (se 1 (by rfl) ⟨1973447, by rfl⟩ : syracuseStep 2631263 = 3946895) B3946895
theorem B2000479 : Blo 1752577 2000479 := bstep (se 1 (by rfl) ⟨1500359, by rfl⟩ : syracuseStep 2000479 = 3000719) B3000719
theorem B5916347 : Blo 1752577 5916347 := bstep (se 1 (by rfl) ⟨4437260, by rfl⟩ : syracuseStep 5916347 = 8874521) B8874521
theorem B3794735 : Blo 1752577 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B2959159 : Blo 1752577 2959159 := bstep (se 1 (by rfl) ⟨2219369, by rfl⟩ : syracuseStep 2959159 = 4438739) B4438739
theorem B2631479 : Blo 1752577 2631479 := bstep (se 1 (by rfl) ⟨1973609, by rfl⟩ : syracuseStep 2631479 = 3947219) B3947219
theorem B7489367 : Blo 1752577 7489367 := bstep (se 1 (by rfl) ⟨5617025, by rfl⟩ : syracuseStep 7489367 = 11234051) B11234051
theorem B4990825 : Blo 1752577 4990825 := bstep (se 2 (by rfl) ⟨1871559, by rfl⟩ : syracuseStep 4990825 = 3743119) B3743119
theorem B2631785 : Blo 1752577 2631785 := bstep (se 2 (by rfl) ⟨986919, by rfl⟩ : syracuseStep 2631785 = 1973839) B1973839
theorem B3328265 : Blo 1752577 3328265 := bstep (se 2 (by rfl) ⟨1248099, by rfl⟩ : syracuseStep 3328265 = 2496199) B2496199
theorem B2959625 : Blo 1752577 2959625 := bstep (se 2 (by rfl) ⟨1109859, by rfl⟩ : syracuseStep 2959625 = 2219719) B2219719
theorem B6654419 : Blo 1752577 6654419 := bstep (se 1 (by rfl) ⟨4990814, by rfl⟩ : syracuseStep 6654419 = 9981629) B9981629
theorem B40511987 : Blo 1752577 40511987 := bstep (se 1 (by rfl) ⟨30383990, by rfl⟩ : syracuseStep 40511987 = 60767981) B60767981
theorem B9480979 : Blo 1752577 9480979 := bstep (se 1 (by rfl) ⟨7110734, by rfl⟩ : syracuseStep 9480979 = 14221469) B14221469
theorem B13314941 : Blo 1752577 13314941 := bstep (se 3 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 13314941 = 4993103) B4993103
theorem B3943547 : Blo 1752577 3943547 := bstep (se 1 (by rfl) ⟨2957660, by rfl⟩ : syracuseStep 3943547 = 5915321) B5915321
theorem B27004043 : Blo 1752577 27004043 := bstep (se 1 (by rfl) ⟨20253032, by rfl⟩ : syracuseStep 27004043 = 40506065) B40506065
theorem B2665705 : Blo 1752577 2665705 := bstep (se 2 (by rfl) ⟨999639, by rfl⟩ : syracuseStep 2665705 = 1999279) B1999279
theorem B2960617 : Blo 1752577 2960617 := bstep (se 2 (by rfl) ⟨1110231, by rfl⟩ : syracuseStep 2960617 = 2220463) B2220463
theorem B3943673 : Blo 1752577 3943673 := bstep (se 2 (by rfl) ⟨1478877, by rfl⟩ : syracuseStep 3943673 = 2957755) B2957755
theorem B2960671 : Blo 1752577 2960671 := bstep (se 1 (by rfl) ⟨2220503, by rfl⟩ : syracuseStep 2960671 = 4441007) B4441007
theorem B8875331 : Blo 1752577 8875331 := bstep (se 1 (by rfl) ⟨6656498, by rfl⟩ : syracuseStep 8875331 = 13312997) B13312997
theorem B3943817 : Blo 1752577 3943817 := bstep (se 2 (by rfl) ⟨1478931, by rfl⟩ : syracuseStep 3943817 = 2957863) B2957863
theorem B4992455 : Blo 1752577 4992455 := bstep (se 1 (by rfl) ⟨3744341, by rfl⟩ : syracuseStep 4992455 = 7488683) B7488683
theorem B4214231 : Blo 1752577 4214231 := bstep (se 1 (by rfl) ⟨3160673, by rfl⟩ : syracuseStep 4214231 = 6321347) B6321347
theorem B3943943 : Blo 1752577 3943943 := bstep (se 1 (by rfl) ⟨2957957, by rfl⟩ : syracuseStep 3943943 = 5915915) B5915915
theorem B5918291 : Blo 1752577 5918291 := bstep (se 1 (by rfl) ⟨4438718, by rfl⟩ : syracuseStep 5918291 = 8877437) B8877437
theorem B21327533 : Blo 1752577 21327533 := bstep (se 3 (by rfl) ⟨3998912, by rfl⟩ : syracuseStep 21327533 = 7997825) B7997825
theorem B3944123 : Blo 1752577 3944123 := bstep (se 1 (by rfl) ⟨2958092, by rfl⟩ : syracuseStep 3944123 = 5916185) B5916185
theorem B3329723 : Blo 1752577 3329723 := bstep (se 1 (by rfl) ⟨2497292, by rfl⟩ : syracuseStep 3329723 = 4994585) B4994585
theorem B8875817 : Blo 1752577 8875817 := bstep (se 2 (by rfl) ⟨3328431, by rfl⟩ : syracuseStep 8875817 = 6656863) B6656863
theorem B3944249 : Blo 1752577 3944249 := bstep (se 2 (by rfl) ⟨1479093, by rfl⟩ : syracuseStep 3944249 = 2958187) B2958187
theorem B4214585 : Blo 1752577 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B5402497 : Blo 1752577 5402497 := bstep (se 2 (by rfl) ⟨2025936, by rfl⟩ : syracuseStep 5402497 = 4051873) B4051873
theorem B22474705 : Blo 1752577 22474705 := bstep (se 2 (by rfl) ⟨8428014, by rfl⟩ : syracuseStep 22474705 = 16856029) B16856029
theorem B6656363 : Blo 1752577 6656363 := bstep (se 1 (by rfl) ⟨4992272, by rfl⟩ : syracuseStep 6656363 = 9984545) B9984545
theorem B1872239 : Blo 1752577 1872239 := bstep (se 1 (by rfl) ⟨1404179, by rfl⟩ : syracuseStep 1872239 = 2808359) B2808359
theorem B11391347 : Blo 1752577 11391347 := bstep (se 1 (by rfl) ⟨8543510, by rfl⟩ : syracuseStep 11391347 = 17087021) B17087021
theorem B3944879 : Blo 1752577 3944879 := bstep (se 1 (by rfl) ⟨2958659, by rfl⟩ : syracuseStep 3944879 = 5917319) B5917319
theorem B8425903 : Blo 1752577 8425903 := bstep (se 1 (by rfl) ⟨6319427, by rfl⟩ : syracuseStep 8425903 = 12638855) B12638855
theorem B3944915 : Blo 1752577 3944915 := bstep (se 1 (by rfl) ⟨2958686, by rfl⟩ : syracuseStep 3944915 = 5917373) B5917373
theorem B7492115 : Blo 1752577 7492115 := bstep (se 1 (by rfl) ⟨5619086, by rfl⟩ : syracuseStep 7492115 = 11238173) B11238173
theorem B3945023 : Blo 1752577 3945023 := bstep (se 1 (by rfl) ⟨2958767, by rfl⟩ : syracuseStep 3945023 = 5917535) B5917535
theorem B9982561 : Blo 1752577 9982561 := bstep (se 2 (by rfl) ⟨3743460, by rfl⟩ : syracuseStep 9982561 = 7486921) B7486921
theorem B9990809 : Blo 1752577 9990809 := bstep (se 2 (by rfl) ⟨3746553, by rfl⟩ : syracuseStep 9990809 = 7493107) B7493107
theorem B3945131 : Blo 1752577 3945131 := bstep (se 1 (by rfl) ⟨2958848, by rfl⟩ : syracuseStep 3945131 = 5917697) B5917697
theorem B4436815 : Blo 1752577 4436815 := bstep (se 1 (by rfl) ⟨3327611, by rfl⟩ : syracuseStep 4436815 = 6655223) B6655223
theorem B8877113 : Blo 1752577 8877113 := bstep (se 2 (by rfl) ⟨3328917, by rfl⟩ : syracuseStep 8877113 = 6657835) B6657835
theorem B4437089 : Blo 1752577 4437089 := bstep (se 2 (by rfl) ⟨1663908, by rfl⟩ : syracuseStep 4437089 = 3327817) B3327817
theorem B6657167 : Blo 1752577 6657167 := bstep (se 1 (by rfl) ⟨4992875, by rfl⟩ : syracuseStep 6657167 = 9985751) B9985751
theorem B3945671 : Blo 1752577 3945671 := bstep (se 1 (by rfl) ⟨2959253, by rfl⟩ : syracuseStep 3945671 = 5918507) B5918507
theorem B5616935 : Blo 1752577 5616935 := bstep (se 1 (by rfl) ⟨4212701, by rfl⟩ : syracuseStep 5616935 = 8425403) B8425403
theorem B1873243 : Blo 1752577 1873243 := bstep (se 1 (by rfl) ⟨1404932, by rfl⟩ : syracuseStep 1873243 = 2809865) B2809865
theorem B3945851 : Blo 1752577 3945851 := bstep (se 1 (by rfl) ⟨2959388, by rfl⟩ : syracuseStep 3945851 = 5918777) B5918777
theorem B4437463 : Blo 1752577 4437463 := bstep (se 1 (by rfl) ⟨3328097, by rfl⟩ : syracuseStep 4437463 = 6656195) B6656195
theorem B3945977 : Blo 1752577 3945977 := bstep (se 2 (by rfl) ⟨1479741, by rfl⟩ : syracuseStep 3945977 = 2959483) B2959483
theorem B22459943 : Blo 1752577 22459943 := bstep (se 1 (by rfl) ⟨16844957, by rfl⟩ : syracuseStep 22459943 = 33689915) B33689915
theorem B3946067 : Blo 1752577 3946067 := bstep (se 1 (by rfl) ⟨2959550, by rfl⟩ : syracuseStep 3946067 = 5919101) B5919101
theorem B35985035 : Blo 1752577 35985035 := bstep (se 1 (by rfl) ⟨26988776, by rfl⟩ : syracuseStep 35985035 = 53977553) B53977553
theorem B8107705 : Blo 1752577 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B4437767 : Blo 1752577 4437767 := bstep (se 1 (by rfl) ⟨3328325, by rfl⟩ : syracuseStep 4437767 = 6656651) B6656651
theorem B3946247 : Blo 1752577 3946247 := bstep (se 1 (by rfl) ⟨2959685, by rfl⟩ : syracuseStep 3946247 = 5919371) B5919371
theorem B52664327 : Blo 1752577 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B15186149 : Blo 1752577 15186149 := bstep (se 4 (by rfl) ⟨1423701, by rfl⟩ : syracuseStep 15186149 = 2847403) B2847403
theorem B17078519 : Blo 1752577 17078519 := bstep (se 1 (by rfl) ⟨12808889, by rfl⟩ : syracuseStep 17078519 = 25617779) B25617779
theorem B26990873 : Blo 1752577 26990873 := bstep (se 2 (by rfl) ⟨10121577, by rfl⟩ : syracuseStep 26990873 = 20243155) B20243155
theorem B121534825 : Blo 1752577 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B3946859 : Blo 1752577 3946859 := bstep (se 1 (by rfl) ⟨2960144, by rfl⟩ : syracuseStep 3946859 = 5920289) B5920289
theorem B8427901 : Blo 1752577 8427901 := bstep (se 3 (by rfl) ⟨1580231, by rfl⟩ : syracuseStep 8427901 = 3160463) B3160463
theorem B5921207 : Blo 1752577 5921207 := bstep (se 1 (by rfl) ⟨4440905, by rfl⟩ : syracuseStep 5921207 = 8881811) B8881811
theorem B3947003 : Blo 1752577 3947003 := bstep (se 1 (by rfl) ⟨2960252, by rfl⟩ : syracuseStep 3947003 = 5920505) B5920505
theorem B4438547 : Blo 1752577 4438547 := bstep (se 1 (by rfl) ⟨3328910, by rfl⟩ : syracuseStep 4438547 = 6657821) B6657821
theorem B9992767 : Blo 1752577 9992767 := bstep (se 1 (by rfl) ⟨7494575, by rfl⟩ : syracuseStep 9992767 = 14989151) B14989151
theorem B1972831 : Blo 1752577 1972831 := bstep (se 1 (by rfl) ⟨1479623, by rfl⟩ : syracuseStep 1972831 = 2959247) B2959247
theorem B3947129 : Blo 1752577 3947129 := bstep (se 2 (by rfl) ⟨1480173, by rfl⟩ : syracuseStep 3947129 = 2960347) B2960347
theorem B3947183 : Blo 1752577 3947183 := bstep (se 1 (by rfl) ⟨2960387, by rfl⟩ : syracuseStep 3947183 = 5920775) B5920775
theorem B6658807 : Blo 1752577 6658807 := bstep (se 1 (by rfl) ⟨4994105, by rfl⟩ : syracuseStep 6658807 = 9988211) B9988211
theorem B3947255 : Blo 1752577 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B16857875 : Blo 1752577 16857875 := bstep (se 1 (by rfl) ⟨12643406, by rfl⟩ : syracuseStep 16857875 = 25286813) B25286813
theorem B14982043 : Blo 1752577 14982043 := bstep (se 1 (by rfl) ⟨11236532, by rfl⟩ : syracuseStep 14982043 = 22473065) B22473065
theorem B3947435 : Blo 1752577 3947435 := bstep (se 1 (by rfl) ⟨2960576, by rfl⟩ : syracuseStep 3947435 = 5921153) B5921153
theorem B7904243 : Blo 1752577 7904243 := bstep (se 1 (by rfl) ⟨5928182, by rfl⟩ : syracuseStep 7904243 = 11856365) B11856365
theorem B4742135 : Blo 1752577 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B6659111 : Blo 1752577 6659111 := bstep (se 1 (by rfl) ⟨4994333, by rfl⟩ : syracuseStep 6659111 = 9988667) B9988667
theorem B16006193 : Blo 1752577 16006193 := bstep (se 2 (by rfl) ⟨6002322, by rfl⟩ : syracuseStep 16006193 = 12004645) B12004645
theorem B8879219 : Blo 1752577 8879219 := bstep (se 1 (by rfl) ⟨6659414, by rfl⟩ : syracuseStep 8879219 = 13318829) B13318829
theorem B2629001 : Blo 1752577 2629001 := bstep (se 2 (by rfl) ⟨985875, by rfl⟩ : syracuseStep 2629001 = 1971751) B1971751
theorem B7486991 : Blo 1752577 7486991 := bstep (se 1 (by rfl) ⟨5615243, by rfl⟩ : syracuseStep 7486991 = 11230487) B11230487
theorem B1752639 : Blo 1752577 1752639 := bstep (se 1 (by rfl) ⟨1314479, by rfl⟩ : syracuseStep 1752639 = 2628959) B2628959
theorem B1752647 : Blo 1752577 1752647 := bstep (se 1 (by rfl) ⟨1314485, by rfl⟩ : syracuseStep 1752647 = 2628971) B2628971
theorem B1752799 : Blo 1752577 1752799 := bstep (se 1 (by rfl) ⟨1314599, by rfl⟩ : syracuseStep 1752799 = 2629199) B2629199
theorem B2629355 : Blo 1752577 2629355 := bstep (se 1 (by rfl) ⟨1972016, by rfl⟩ : syracuseStep 2629355 = 3944033) B3944033
theorem B11239175 : Blo 1752577 11239175 := bstep (se 1 (by rfl) ⟨8429381, by rfl⟩ : syracuseStep 11239175 = 16858763) B16858763
theorem B1752879 : Blo 1752577 1752879 := bstep (se 1 (by rfl) ⟨1314659, by rfl⟩ : syracuseStep 1752879 = 2629319) B2629319
theorem B1752987 : Blo 1752577 1752987 := bstep (se 1 (by rfl) ⟨1314740, by rfl⟩ : syracuseStep 1752987 = 2629481) B2629481
theorem B8880029 : Blo 1752577 8880029 := bstep (se 3 (by rfl) ⟨1665005, by rfl⟩ : syracuseStep 8880029 = 3330011) B3330011
theorem B1753039 : Blo 1752577 1753039 := bstep (se 1 (by rfl) ⟨1314779, by rfl⟩ : syracuseStep 1753039 = 2629559) B2629559
theorem B2629583 : Blo 1752577 2629583 := bstep (se 1 (by rfl) ⟨1972187, by rfl⟩ : syracuseStep 2629583 = 3944375) B3944375
theorem B1753063 : Blo 1752577 1753063 := bstep (se 1 (by rfl) ⟨1314797, by rfl⟩ : syracuseStep 1753063 = 2629595) B2629595
theorem B1753319 : Blo 1752577 1753319 := bstep (se 1 (by rfl) ⟨1314989, by rfl⟩ : syracuseStep 1753319 = 2629979) B2629979
theorem B7594231 : Blo 1752577 7594231 := bstep (se 1 (by rfl) ⟨5695673, by rfl⟩ : syracuseStep 7594231 = 11391347) B11391347
theorem B2629919 : Blo 1752577 2629919 := bstep (se 1 (by rfl) ⟨1972439, by rfl⟩ : syracuseStep 2629919 = 3944879) B3944879
theorem B2629943 : Blo 1752577 2629943 := bstep (se 1 (by rfl) ⟨1972457, by rfl⟩ : syracuseStep 2629943 = 3944915) B3944915
theorem B12812633 : Blo 1752577 12812633 := bstep (se 2 (by rfl) ⟨4804737, by rfl⟩ : syracuseStep 12812633 = 9609475) B9609475
theorem B2630015 : Blo 1752577 2630015 := bstep (se 1 (by rfl) ⟨1972511, by rfl⟩ : syracuseStep 2630015 = 3945023) B3945023
theorem B1753471 : Blo 1752577 1753471 := bstep (se 1 (by rfl) ⟨1315103, by rfl⟩ : syracuseStep 1753471 = 2630207) B2630207
theorem B6750647 : Blo 1752577 6750647 := bstep (se 1 (by rfl) ⟨5062985, by rfl⟩ : syracuseStep 6750647 = 10125971) B10125971
theorem B6660539 : Blo 1752577 6660539 := bstep (se 1 (by rfl) ⟨4995404, by rfl⟩ : syracuseStep 6660539 = 9990809) B9990809
theorem B22462919 : Blo 1752577 22462919 := bstep (se 1 (by rfl) ⟨16847189, by rfl⟩ : syracuseStep 22462919 = 33694379) B33694379
theorem B2630087 : Blo 1752577 2630087 := bstep (se 1 (by rfl) ⟨1972565, by rfl⟩ : syracuseStep 2630087 = 3945131) B3945131
theorem B1753551 : Blo 1752577 1753551 := bstep (se 1 (by rfl) ⟨1315163, by rfl⟩ : syracuseStep 1753551 = 2630327) B2630327
theorem B162046433 : Blo 1752577 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B10814015 : Blo 1752577 10814015 := bstep (se 1 (by rfl) ⟨8110511, by rfl⟩ : syracuseStep 10814015 = 16221023) B16221023
theorem B1753703 : Blo 1752577 1753703 := bstep (se 1 (by rfl) ⟨1315277, by rfl⟩ : syracuseStep 1753703 = 2630555) B2630555
theorem B2958059 : Blo 1752577 2958059 := bstep (se 1 (by rfl) ⟨2218544, by rfl⟩ : syracuseStep 2958059 = 4437089) B4437089
theorem B2630441 : Blo 1752577 2630441 := bstep (se 2 (by rfl) ⟨986415, by rfl⟩ : syracuseStep 2630441 = 1972831) B1972831
theorem B2630447 : Blo 1752577 2630447 := bstep (se 1 (by rfl) ⟨1972835, by rfl⟩ : syracuseStep 2630447 = 3945671) B3945671
theorem B3744623 : Blo 1752577 3744623 := bstep (se 1 (by rfl) ⟨2808467, by rfl⟩ : syracuseStep 3744623 = 5616935) B5616935
theorem B1753967 : Blo 1752577 1753967 := bstep (se 1 (by rfl) ⟨1315475, by rfl⟩ : syracuseStep 1753967 = 2630951) B2630951
theorem B51250067 : Blo 1752577 51250067 := bstep (se 1 (by rfl) ⟨38437550, by rfl⟩ : syracuseStep 51250067 = 76875101) B76875101
theorem B2630567 : Blo 1752577 2630567 := bstep (se 1 (by rfl) ⟨1972925, by rfl⟩ : syracuseStep 2630567 = 3945851) B3945851
theorem B1754023 : Blo 1752577 1754023 := bstep (se 1 (by rfl) ⟨1315517, by rfl⟩ : syracuseStep 1754023 = 2631035) B2631035
theorem B2630651 : Blo 1752577 2630651 := bstep (se 1 (by rfl) ⟨1972988, by rfl⟩ : syracuseStep 2630651 = 3945977) B3945977
theorem B1754107 : Blo 1752577 1754107 := bstep (se 1 (by rfl) ⟨1315580, by rfl⟩ : syracuseStep 1754107 = 2631161) B2631161
theorem B12641305 : Blo 1752577 12641305 := bstep (se 2 (by rfl) ⟨4740489, by rfl⟩ : syracuseStep 12641305 = 9480979) B9480979
theorem B19227677 : Blo 1752577 19227677 := bstep (se 3 (by rfl) ⟨3605189, by rfl⟩ : syracuseStep 19227677 = 7210379) B7210379
theorem B2630711 : Blo 1752577 2630711 := bstep (se 1 (by rfl) ⟨1973033, by rfl⟩ : syracuseStep 2630711 = 3946067) B3946067
theorem B1754175 : Blo 1752577 1754175 := bstep (se 1 (by rfl) ⟨1315631, by rfl⟩ : syracuseStep 1754175 = 2631263) B2631263
theorem B5915753 : Blo 1752577 5915753 := bstep (se 2 (by rfl) ⟨2218407, by rfl⟩ : syracuseStep 5915753 = 4436815) B4436815
theorem B2958511 : Blo 1752577 2958511 := bstep (se 1 (by rfl) ⟨2218883, by rfl⟩ : syracuseStep 2958511 = 4437767) B4437767
theorem B2630831 : Blo 1752577 2630831 := bstep (se 1 (by rfl) ⟨1973123, by rfl⟩ : syracuseStep 2630831 = 3946247) B3946247
theorem B1754319 : Blo 1752577 1754319 := bstep (se 1 (by rfl) ⟨1315739, by rfl⟩ : syracuseStep 1754319 = 2631479) B2631479
theorem B1754523 : Blo 1752577 1754523 := bstep (se 1 (by rfl) ⟨1315892, by rfl⟩ : syracuseStep 1754523 = 2631785) B2631785
theorem B2631239 : Blo 1752577 2631239 := bstep (se 1 (by rfl) ⟨1973429, by rfl⟩ : syracuseStep 2631239 = 3946859) B3946859
theorem B2631335 : Blo 1752577 2631335 := bstep (se 1 (by rfl) ⟨1973501, by rfl⟩ : syracuseStep 2631335 = 3947003) B3947003
theorem B2959031 : Blo 1752577 2959031 := bstep (se 1 (by rfl) ⟨2219273, by rfl⟩ : syracuseStep 2959031 = 4438547) B4438547
theorem B2631419 : Blo 1752577 2631419 := bstep (se 1 (by rfl) ⟨1973564, by rfl⟩ : syracuseStep 2631419 = 3947129) B3947129
theorem B14419741 : Blo 1752577 14419741 := bstep (se 3 (by rfl) ⟨2703701, by rfl⟩ : syracuseStep 14419741 = 5407403) B5407403
theorem B2631455 : Blo 1752577 2631455 := bstep (se 1 (by rfl) ⟨1973591, by rfl⟩ : syracuseStep 2631455 = 3947183) B3947183
theorem B2631503 : Blo 1752577 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B2631623 : Blo 1752577 2631623 := bstep (se 1 (by rfl) ⟨1973717, by rfl⟩ : syracuseStep 2631623 = 3947435) B3947435
theorem B5916617 : Blo 1752577 5916617 := bstep (se 2 (by rfl) ⟨2218731, by rfl⟩ : syracuseStep 5916617 = 4437463) B4437463
theorem B5269495 : Blo 1752577 5269495 := bstep (se 1 (by rfl) ⟨3952121, by rfl⟩ : syracuseStep 5269495 = 7904243) B7904243
theorem B5916887 : Blo 1752577 5916887 := bstep (se 1 (by rfl) ⟨4437665, by rfl⟩ : syracuseStep 5916887 = 8875331) B8875331
theorem B3328303 : Blo 1752577 3328303 := bstep (se 1 (by rfl) ⟨2496227, by rfl⟩ : syracuseStep 3328303 = 4992455) B4992455
theorem B4991327 : Blo 1752577 4991327 := bstep (se 1 (by rfl) ⟨3743495, by rfl⟩ : syracuseStep 4991327 = 7486991) B7486991
theorem B6654433 : Blo 1752577 6654433 := bstep (se 2 (by rfl) ⟨2495412, by rfl⟩ : syracuseStep 6654433 = 4990825) B4990825
theorem B7203329 : Blo 1752577 7203329 := bstep (se 2 (by rfl) ⟨2701248, by rfl⟩ : syracuseStep 7203329 = 5402497) B5402497
theorem B5917211 : Blo 1752577 5917211 := bstep (se 1 (by rfl) ⟨4437908, by rfl⟩ : syracuseStep 5917211 = 8875817) B8875817
theorem B9988919 : Blo 1752577 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B2960219 : Blo 1752577 2960219 := bstep (se 1 (by rfl) ⟨2220164, by rfl⟩ : syracuseStep 2960219 = 4440329) B4440329
theorem B3943403 : Blo 1752577 3943403 := bstep (se 1 (by rfl) ⟨2957552, by rfl⟩ : syracuseStep 3943403 = 5915105) B5915105
theorem B72010781 : Blo 1752577 72010781 := bstep (se 3 (by rfl) ⟨13502021, by rfl⟩ : syracuseStep 72010781 = 27004043) B27004043
theorem B2960455 : Blo 1752577 2960455 := bstep (se 1 (by rfl) ⟨2220341, by rfl⟩ : syracuseStep 2960455 = 4440683) B4440683
theorem B11234537 : Blo 1752577 11234537 := bstep (se 2 (by rfl) ⟨4212951, by rfl⟩ : syracuseStep 11234537 = 8425903) B8425903
theorem B45542717 : Blo 1752577 45542717 := bstep (se 3 (by rfl) ⟨8539259, by rfl⟩ : syracuseStep 45542717 = 17078519) B17078519
theorem B3747151 : Blo 1752577 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B5918075 : Blo 1752577 5918075 := bstep (se 1 (by rfl) ⟨4438556, by rfl⟩ : syracuseStep 5918075 = 8877113) B8877113
theorem B13323689 : Blo 1752577 13323689 := bstep (se 2 (by rfl) ⟨4996383, by rfl⟩ : syracuseStep 13323689 = 9992767) B9992767
theorem B3747323 : Blo 1752577 3747323 := bstep (se 1 (by rfl) ⟨2810492, by rfl⟩ : syracuseStep 3747323 = 5620985) B5620985
theorem B43232777 : Blo 1752577 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B4992637 : Blo 1752577 4992637 := bstep (se 3 (by rfl) ⟨936119, by rfl⟩ : syracuseStep 4992637 = 1872239) B1872239
theorem B23990023 : Blo 1752577 23990023 := bstep (se 1 (by rfl) ⟨17992517, by rfl⟩ : syracuseStep 23990023 = 35985035) B35985035
theorem B3944231 : Blo 1752577 3944231 := bstep (se 1 (by rfl) ⟨2958173, by rfl⟩ : syracuseStep 3944231 = 5916347) B5916347
theorem B19976057 : Blo 1752577 19976057 := bstep (se 2 (by rfl) ⟨7491021, by rfl⟩ : syracuseStep 19976057 = 14982043) B14982043
theorem B4992911 : Blo 1752577 4992911 := bstep (se 1 (by rfl) ⟨3744683, by rfl⟩ : syracuseStep 4992911 = 7489367) B7489367
theorem B17993915 : Blo 1752577 17993915 := bstep (se 1 (by rfl) ⟨13495436, by rfl⟩ : syracuseStep 17993915 = 26990873) B26990873
theorem B4436279 : Blo 1752577 4436279 := bstep (se 1 (by rfl) ⟨3327209, by rfl⟩ : syracuseStep 4436279 = 6654419) B6654419
theorem B8876627 : Blo 1752577 8876627 := bstep (se 1 (by rfl) ⟨6657470, by rfl⟩ : syracuseStep 8876627 = 13314941) B13314941
theorem B10670795 : Blo 1752577 10670795 := bstep (se 1 (by rfl) ⟨8003096, by rfl⟩ : syracuseStep 10670795 = 16006193) B16006193
theorem B5919479 : Blo 1752577 5919479 := bstep (se 1 (by rfl) ⟨4439609, by rfl⟩ : syracuseStep 5919479 = 8879219) B8879219
theorem B3945257 : Blo 1752577 3945257 := bstep (se 2 (by rfl) ⟨1479471, by rfl⟩ : syracuseStep 3945257 = 2958943) B2958943
theorem B2667305 : Blo 1752577 2667305 := bstep (se 2 (by rfl) ⟨1000239, by rfl⟩ : syracuseStep 2667305 = 2000479) B2000479
theorem B10810273 : Blo 1752577 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B3945527 : Blo 1752577 3945527 := bstep (se 1 (by rfl) ⟨2959145, by rfl⟩ : syracuseStep 3945527 = 5918291) B5918291
theorem B3945545 : Blo 1752577 3945545 := bstep (se 2 (by rfl) ⟨1479579, by rfl⟩ : syracuseStep 3945545 = 2959159) B2959159
theorem B14218355 : Blo 1752577 14218355 := bstep (se 1 (by rfl) ⟨10663766, by rfl⟩ : syracuseStep 14218355 = 21327533) B21327533
theorem B7492783 : Blo 1752577 7492783 := bstep (se 1 (by rfl) ⟨5619587, by rfl⟩ : syracuseStep 7492783 = 11239175) B11239175
theorem B5920019 : Blo 1752577 5920019 := bstep (se 1 (by rfl) ⟨4440014, by rfl⟩ : syracuseStep 5920019 = 8880029) B8880029
theorem B4437575 : Blo 1752577 4437575 := bstep (se 1 (by rfl) ⟨3328181, by rfl⟩ : syracuseStep 4437575 = 6656363) B6656363
theorem B1971823 : Blo 1752577 1971823 := bstep (se 1 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 1971823 = 2957735) B2957735
theorem B1971931 : Blo 1752577 1971931 := bstep (se 1 (by rfl) ⟨1478948, by rfl⟩ : syracuseStep 1971931 = 2957897) B2957897
theorem B5920559 : Blo 1752577 5920559 := bstep (se 1 (by rfl) ⟨4440419, by rfl⟩ : syracuseStep 5920559 = 8880839) B8880839
theorem B11237201 : Blo 1752577 11237201 := bstep (se 2 (by rfl) ⟨4213950, by rfl⟩ : syracuseStep 11237201 = 8427901) B8427901
theorem B5330825 : Blo 1752577 5330825 := bstep (se 2 (by rfl) ⟨1999059, by rfl⟩ : syracuseStep 5330825 = 3998119) B3998119
theorem B2807801 : Blo 1752577 2807801 := bstep (se 2 (by rfl) ⟨1052925, by rfl⟩ : syracuseStep 2807801 = 2105851) B2105851
theorem B2807903 : Blo 1752577 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B4438111 : Blo 1752577 4438111 := bstep (se 1 (by rfl) ⟨3328583, by rfl⟩ : syracuseStep 4438111 = 6657167) B6657167
theorem B13310081 : Blo 1752577 13310081 := bstep (se 2 (by rfl) ⟨4991280, by rfl⟩ : syracuseStep 13310081 = 9982561) B9982561
theorem B2808103 : Blo 1752577 2808103 := bstep (se 1 (by rfl) ⟨2106077, by rfl⟩ : syracuseStep 2808103 = 4212155) B4212155
theorem B8878409 : Blo 1752577 8878409 := bstep (se 2 (by rfl) ⟨3329403, by rfl⟩ : syracuseStep 8878409 = 6658807) B6658807
theorem B14973295 : Blo 1752577 14973295 := bstep (se 1 (by rfl) ⟨11229971, by rfl⟩ : syracuseStep 14973295 = 22459943) B22459943
theorem B2529823 : Blo 1752577 2529823 := bstep (se 1 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 2529823 = 3794735) B3794735
theorem B35109551 : Blo 1752577 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B19978973 : Blo 1752577 19978973 := bstep (se 3 (by rfl) ⟨3746057, by rfl⟩ : syracuseStep 19978973 = 7492115) B7492115
theorem B10124099 : Blo 1752577 10124099 := bstep (se 1 (by rfl) ⟨7593074, by rfl⟩ : syracuseStep 10124099 = 15186149) B15186149
theorem B2218843 : Blo 1752577 2218843 := bstep (se 1 (by rfl) ⟨1664132, by rfl⟩ : syracuseStep 2218843 = 3328265) B3328265
theorem B1973083 : Blo 1752577 1973083 := bstep (se 1 (by rfl) ⟨1479812, by rfl⟩ : syracuseStep 1973083 = 2959625) B2959625
theorem B3947471 : Blo 1752577 3947471 := bstep (se 1 (by rfl) ⟨2960603, by rfl⟩ : syracuseStep 3947471 = 5921207) B5921207
theorem B11230177 : Blo 1752577 11230177 := bstep (se 2 (by rfl) ⟨4211316, by rfl⟩ : syracuseStep 11230177 = 8422633) B8422633
theorem B3554273 : Blo 1752577 3554273 := bstep (se 2 (by rfl) ⟨1332852, by rfl⟩ : syracuseStep 3554273 = 2665705) B2665705
theorem B3947489 : Blo 1752577 3947489 := bstep (se 2 (by rfl) ⟨1480308, by rfl⟩ : syracuseStep 3947489 = 2960617) B2960617
theorem B27007991 : Blo 1752577 27007991 := bstep (se 1 (by rfl) ⟨20255993, by rfl⟩ : syracuseStep 27007991 = 40511987) B40511987
theorem B3947561 : Blo 1752577 3947561 := bstep (se 2 (by rfl) ⟨1480335, by rfl⟩ : syracuseStep 3947561 = 2960671) B2960671
theorem B2497657 : Blo 1752577 2497657 := bstep (se 2 (by rfl) ⟨936621, by rfl⟩ : syracuseStep 2497657 = 1873243) B1873243
theorem B11238583 : Blo 1752577 11238583 := bstep (se 1 (by rfl) ⟨8428937, by rfl⟩ : syracuseStep 11238583 = 16857875) B16857875
theorem B3202313 : Blo 1752577 3202313 := bstep (se 2 (by rfl) ⟨1200867, by rfl⟩ : syracuseStep 3202313 = 2401735) B2401735
theorem B3161423 : Blo 1752577 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B4439407 : Blo 1752577 4439407 := bstep (se 1 (by rfl) ⟨3329555, by rfl⟩ : syracuseStep 4439407 = 6659111) B6659111
theorem B2629031 : Blo 1752577 2629031 := bstep (se 1 (by rfl) ⟨1971773, by rfl⟩ : syracuseStep 2629031 = 3943547) B3943547
theorem B10665445 : Blo 1752577 10665445 := bstep (se 4 (by rfl) ⟨999885, by rfl⟩ : syracuseStep 10665445 = 1999771) B1999771
theorem B2629115 : Blo 1752577 2629115 := bstep (se 1 (by rfl) ⟨1971836, by rfl⟩ : syracuseStep 2629115 = 3943673) B3943673
theorem B1752667 : Blo 1752577 1752667 := bstep (se 1 (by rfl) ⟨1314500, by rfl⟩ : syracuseStep 1752667 = 2629001) B2629001
theorem B2629211 : Blo 1752577 2629211 := bstep (se 1 (by rfl) ⟨1971908, by rfl⟩ : syracuseStep 2629211 = 3943817) B3943817
theorem B2809487 : Blo 1752577 2809487 := bstep (se 1 (by rfl) ⟨2107115, by rfl⟩ : syracuseStep 2809487 = 4214231) B4214231
theorem B2629295 : Blo 1752577 2629295 := bstep (se 1 (by rfl) ⟨1971971, by rfl⟩ : syracuseStep 2629295 = 3943943) B3943943
theorem B2629415 : Blo 1752577 2629415 := bstep (se 1 (by rfl) ⟨1972061, by rfl⟩ : syracuseStep 2629415 = 3944123) B3944123
theorem B2219815 : Blo 1752577 2219815 := bstep (se 1 (by rfl) ⟨1664861, by rfl⟩ : syracuseStep 2219815 = 3329723) B3329723
theorem B1752903 : Blo 1752577 1752903 := bstep (se 1 (by rfl) ⟨1314677, by rfl⟩ : syracuseStep 1752903 = 2629355) B2629355
theorem B2629499 : Blo 1752577 2629499 := bstep (se 1 (by rfl) ⟨1972124, by rfl⟩ : syracuseStep 2629499 = 3944249) B3944249
theorem B2809723 : Blo 1752577 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B29966273 : Blo 1752577 29966273 := bstep (se 2 (by rfl) ⟨11237352, by rfl⟩ : syracuseStep 29966273 = 22474705) B22474705
theorem B1753055 : Blo 1752577 1753055 := bstep (se 1 (by rfl) ⟨1314791, by rfl⟩ : syracuseStep 1753055 = 2629583) B2629583
theorem B51273805 : Blo 1752577 51273805 := bstep (se 3 (by rfl) ⟨9613838, by rfl⟩ : syracuseStep 51273805 = 19227677) B19227677
theorem B1753279 : Blo 1752577 1753279 := bstep (se 1 (by rfl) ⟨1314959, by rfl⟩ : syracuseStep 1753279 = 2629919) B2629919
theorem B2957519 : Blo 1752577 2957519 := bstep (se 1 (by rfl) ⟨2218139, by rfl⟩ : syracuseStep 2957519 = 4436279) B4436279
theorem B1753295 : Blo 1752577 1753295 := bstep (se 1 (by rfl) ⟨1314971, by rfl⟩ : syracuseStep 1753295 = 2629943) B2629943
theorem B7487741 : Blo 1752577 7487741 := bstep (se 3 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 7487741 = 2807903) B2807903
theorem B1753343 : Blo 1752577 1753343 := bstep (se 1 (by rfl) ⟨1315007, by rfl⟩ : syracuseStep 1753343 = 2630015) B2630015
theorem B4440359 : Blo 1752577 4440359 := bstep (se 1 (by rfl) ⟨3330269, by rfl⟩ : syracuseStep 4440359 = 6660539) B6660539
theorem B14975279 : Blo 1752577 14975279 := bstep (se 1 (by rfl) ⟨11231459, by rfl⟩ : syracuseStep 14975279 = 22462919) B22462919
theorem B1753391 : Blo 1752577 1753391 := bstep (se 1 (by rfl) ⟨1315043, by rfl⟩ : syracuseStep 1753391 = 2630087) B2630087
theorem B10125641 : Blo 1752577 10125641 := bstep (se 2 (by rfl) ⟨3797115, by rfl⟩ : syracuseStep 10125641 = 7594231) B7594231
theorem B7209343 : Blo 1752577 7209343 := bstep (se 1 (by rfl) ⟨5407007, by rfl⟩ : syracuseStep 7209343 = 10814015) B10814015
theorem B3744137 : Blo 1752577 3744137 := bstep (se 2 (by rfl) ⟨1404051, by rfl⟩ : syracuseStep 3744137 = 2808103) B2808103
theorem B19964393 : Blo 1752577 19964393 := bstep (se 2 (by rfl) ⟨7486647, by rfl⟩ : syracuseStep 19964393 = 14973295) B14973295
theorem B2630171 : Blo 1752577 2630171 := bstep (se 1 (by rfl) ⟨1972628, by rfl⟩ : syracuseStep 2630171 = 3945257) B3945257
theorem B1753627 : Blo 1752577 1753627 := bstep (se 1 (by rfl) ⟨1315220, by rfl⟩ : syracuseStep 1753627 = 2630441) B2630441
theorem B1778203 : Blo 1752577 1778203 := bstep (se 1 (by rfl) ⟨1333652, by rfl⟩ : syracuseStep 1778203 = 2667305) B2667305
theorem B1753631 : Blo 1752577 1753631 := bstep (se 1 (by rfl) ⟨1315223, by rfl⟩ : syracuseStep 1753631 = 2630447) B2630447
theorem B1753711 : Blo 1752577 1753711 := bstep (se 1 (by rfl) ⟨1315283, by rfl⟩ : syracuseStep 1753711 = 2630567) B2630567
theorem B8872577 : Blo 1752577 8872577 := bstep (se 2 (by rfl) ⟨3327216, by rfl⟩ : syracuseStep 8872577 = 6654433) B6654433
theorem B1753767 : Blo 1752577 1753767 := bstep (se 1 (by rfl) ⟨1315325, by rfl⟩ : syracuseStep 1753767 = 2630651) B2630651
theorem B2630351 : Blo 1752577 2630351 := bstep (se 1 (by rfl) ⟨1972763, by rfl⟩ : syracuseStep 2630351 = 3945527) B3945527
theorem B1753807 : Blo 1752577 1753807 := bstep (se 1 (by rfl) ⟨1315355, by rfl⟩ : syracuseStep 1753807 = 2630711) B2630711
theorem B2630363 : Blo 1752577 2630363 := bstep (se 1 (by rfl) ⟨1972772, by rfl⟩ : syracuseStep 2630363 = 3945545) B3945545
theorem B9478903 : Blo 1752577 9478903 := bstep (se 1 (by rfl) ⟨7109177, by rfl⟩ : syracuseStep 9478903 = 14218355) B14218355
theorem B1753887 : Blo 1752577 1753887 := bstep (se 1 (by rfl) ⟨1315415, by rfl⟩ : syracuseStep 1753887 = 2630831) B2630831
theorem B2958383 : Blo 1752577 2958383 := bstep (se 1 (by rfl) ⟨2218787, by rfl⟩ : syracuseStep 2958383 = 4437575) B4437575
theorem B1754159 : Blo 1752577 1754159 := bstep (se 1 (by rfl) ⟨1315619, by rfl⟩ : syracuseStep 1754159 = 2631239) B2631239
theorem B1754223 : Blo 1752577 1754223 := bstep (se 1 (by rfl) ⟨1315667, by rfl⟩ : syracuseStep 1754223 = 2631335) B2631335
theorem B2958457 : Blo 1752577 2958457 := bstep (se 2 (by rfl) ⟨1109421, by rfl⟩ : syracuseStep 2958457 = 2218843) B2218843
theorem B2630777 : Blo 1752577 2630777 := bstep (se 2 (by rfl) ⟨986541, by rfl⟩ : syracuseStep 2630777 = 1973083) B1973083
theorem B1754279 : Blo 1752577 1754279 := bstep (se 1 (by rfl) ⟨1315709, by rfl⟩ : syracuseStep 1754279 = 2631419) B2631419
theorem B1754303 : Blo 1752577 1754303 := bstep (se 1 (by rfl) ⟨1315727, by rfl⟩ : syracuseStep 1754303 = 2631455) B2631455
theorem B1754335 : Blo 1752577 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B1754415 : Blo 1752577 1754415 := bstep (se 1 (by rfl) ⟨1315811, by rfl⟩ : syracuseStep 1754415 = 2631623) B2631623
theorem B8873387 : Blo 1752577 8873387 := bstep (se 1 (by rfl) ⟨6655040, by rfl⟩ : syracuseStep 8873387 = 13310081) B13310081
theorem B3327551 : Blo 1752577 3327551 := bstep (se 1 (by rfl) ⟨2495663, by rfl⟩ : syracuseStep 3327551 = 4991327) B4991327
theorem B14984777 : Blo 1752577 14984777 := bstep (se 2 (by rfl) ⟨5619291, by rfl⟩ : syracuseStep 14984777 = 11238583) B11238583
theorem B4802219 : Blo 1752577 4802219 := bstep (se 1 (by rfl) ⟨3601664, by rfl⟩ : syracuseStep 4802219 = 7203329) B7203329
theorem B23406367 : Blo 1752577 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B2631647 : Blo 1752577 2631647 := bstep (se 1 (by rfl) ⟨1973735, by rfl⟩ : syracuseStep 2631647 = 3947471) B3947471
theorem B2369515 : Blo 1752577 2369515 := bstep (se 1 (by rfl) ⟨1777136, by rfl⟩ : syracuseStep 2369515 = 3554273) B3554273
theorem B2631659 : Blo 1752577 2631659 := bstep (se 1 (by rfl) ⟨1973744, by rfl⟩ : syracuseStep 2631659 = 3947489) B3947489
theorem B48007187 : Blo 1752577 48007187 := bstep (se 1 (by rfl) ⟨36005390, by rfl⟩ : syracuseStep 48007187 = 72010781) B72010781
theorem B2631707 : Blo 1752577 2631707 := bstep (se 1 (by rfl) ⟨1973780, by rfl⟩ : syracuseStep 2631707 = 3947561) B3947561
theorem B7489691 : Blo 1752577 7489691 := bstep (se 1 (by rfl) ⟨5617268, by rfl⟩ : syracuseStep 7489691 = 11234537) B11234537
theorem B30361811 : Blo 1752577 30361811 := bstep (se 1 (by rfl) ⟨22771358, by rfl⟩ : syracuseStep 30361811 = 45542717) B45542717
theorem B2107615 : Blo 1752577 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B8882459 : Blo 1752577 8882459 := bstep (se 1 (by rfl) ⟨6661844, by rfl⟩ : syracuseStep 8882459 = 13323689) B13323689
theorem B28821851 : Blo 1752577 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B2959753 : Blo 1752577 2959753 := bstep (se 2 (by rfl) ⟨1109907, by rfl⟩ : syracuseStep 2959753 = 2219815) B2219815
theorem B3746297 : Blo 1752577 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B3328607 : Blo 1752577 3328607 := bstep (se 1 (by rfl) ⟨2496455, by rfl⟩ : syracuseStep 3328607 = 4992911) B4992911
theorem B11995943 : Blo 1752577 11995943 := bstep (se 1 (by rfl) ⟨8996957, by rfl⟩ : syracuseStep 11995943 = 17993915) B17993915
theorem B5917481 : Blo 1752577 5917481 := bstep (se 2 (by rfl) ⟨2219055, by rfl⟩ : syracuseStep 5917481 = 4438111) B4438111
theorem B4500431 : Blo 1752577 4500431 := bstep (se 1 (by rfl) ⟨3375323, by rfl⟩ : syracuseStep 4500431 = 6750647) B6750647
theorem B108030955 : Blo 1752577 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B5917751 : Blo 1752577 5917751 := bstep (se 1 (by rfl) ⟨4438313, by rfl⟩ : syracuseStep 5917751 = 8876627) B8876627
theorem B7113863 : Blo 1752577 7113863 := bstep (se 1 (by rfl) ⟨5335397, by rfl⟩ : syracuseStep 7113863 = 10670795) B10670795
theorem B8539501 : Blo 1752577 8539501 := bstep (se 3 (by rfl) ⟨1601156, by rfl⟩ : syracuseStep 8539501 = 3202313) B3202313
theorem B3943835 : Blo 1752577 3943835 := bstep (se 1 (by rfl) ⟨2957876, by rfl⟩ : syracuseStep 3943835 = 5915753) B5915753
theorem B14413697 : Blo 1752577 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B7491467 : Blo 1752577 7491467 := bstep (se 1 (by rfl) ⟨5618600, by rfl⟩ : syracuseStep 7491467 = 11237201) B11237201
theorem B3944411 : Blo 1752577 3944411 := bstep (se 1 (by rfl) ⟨2958308, by rfl⟩ : syracuseStep 3944411 = 5916617) B5916617
theorem B1871867 : Blo 1752577 1871867 := bstep (se 1 (by rfl) ⟨1403900, by rfl⟩ : syracuseStep 1871867 = 2807801) B2807801
theorem B16855073 : Blo 1752577 16855073 := bstep (se 2 (by rfl) ⟨6320652, by rfl⟩ : syracuseStep 16855073 = 12641305) B12641305
theorem B3944591 : Blo 1752577 3944591 := bstep (se 1 (by rfl) ⟨2958443, by rfl⟩ : syracuseStep 3944591 = 5916887) B5916887
theorem B3330209 : Blo 1752577 3330209 := bstep (se 2 (by rfl) ⟨1248828, by rfl⟩ : syracuseStep 3330209 = 2497657) B2497657
theorem B5918939 : Blo 1752577 5918939 := bstep (se 1 (by rfl) ⟨4439204, by rfl⟩ : syracuseStep 5918939 = 8878409) B8878409
theorem B3944681 : Blo 1752577 3944681 := bstep (se 2 (by rfl) ⟨1479255, by rfl⟩ : syracuseStep 3944681 = 2958511) B2958511
theorem B9990377 : Blo 1752577 9990377 := bstep (se 2 (by rfl) ⟨3746391, by rfl⟩ : syracuseStep 9990377 = 7492783) B7492783
theorem B3944807 : Blo 1752577 3944807 := bstep (se 1 (by rfl) ⟨2958605, by rfl⟩ : syracuseStep 3944807 = 5917211) B5917211
theorem B19984805 : Blo 1752577 19984805 := bstep (se 4 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 19984805 = 3747151) B3747151
theorem B5919209 : Blo 1752577 5919209 := bstep (se 2 (by rfl) ⟨2219703, by rfl⟩ : syracuseStep 5919209 = 4439407) B4439407
theorem B6656849 : Blo 1752577 6656849 := bstep (se 2 (by rfl) ⟨2496318, by rfl⟩ : syracuseStep 6656849 = 4992637) B4992637
theorem B3945383 : Blo 1752577 3945383 := bstep (se 1 (by rfl) ⟨2959037, by rfl⟩ : syracuseStep 3945383 = 5918075) B5918075
theorem B31986697 : Blo 1752577 31986697 := bstep (se 2 (by rfl) ⟨11995011, by rfl⟩ : syracuseStep 31986697 = 23990023) B23990023
theorem B1872991 : Blo 1752577 1872991 := bstep (se 1 (by rfl) ⟨1404743, by rfl⟩ : syracuseStep 1872991 = 2809487) B2809487
theorem B13317371 : Blo 1752577 13317371 := bstep (se 1 (by rfl) ⟨9988028, by rfl⟩ : syracuseStep 13317371 = 19976057) B19976057
theorem B19977515 : Blo 1752577 19977515 := bstep (se 1 (by rfl) ⟨14983136, by rfl⟩ : syracuseStep 19977515 = 29966273) B29966273
theorem B7025993 : Blo 1752577 7025993 := bstep (se 2 (by rfl) ⟨2634747, by rfl⟩ : syracuseStep 7025993 = 5269495) B5269495
theorem B8541755 : Blo 1752577 8541755 := bstep (se 1 (by rfl) ⟨6406316, by rfl⟩ : syracuseStep 8541755 = 12812633) B12812633
theorem B4437737 : Blo 1752577 4437737 := bstep (se 2 (by rfl) ⟨1664151, by rfl⟩ : syracuseStep 4437737 = 3328303) B3328303
theorem B1972039 : Blo 1752577 1972039 := bstep (se 1 (by rfl) ⟨1479029, by rfl⟩ : syracuseStep 1972039 = 2958059) B2958059
theorem B3946319 : Blo 1752577 3946319 := bstep (se 1 (by rfl) ⟨2959739, by rfl⟩ : syracuseStep 3946319 = 5919479) B5919479
theorem B2496415 : Blo 1752577 2496415 := bstep (se 1 (by rfl) ⟨1872311, by rfl⟩ : syracuseStep 2496415 = 3744623) B3744623
theorem B34166711 : Blo 1752577 34166711 := bstep (se 1 (by rfl) ⟨25625033, by rfl⟩ : syracuseStep 34166711 = 51250067) B51250067
theorem B3373097 : Blo 1752577 3373097 := bstep (se 2 (by rfl) ⟨1264911, by rfl⟩ : syracuseStep 3373097 = 2529823) B2529823
theorem B3946679 : Blo 1752577 3946679 := bstep (se 1 (by rfl) ⟨2960009, by rfl⟩ : syracuseStep 3946679 = 5920019) B5920019
theorem B1972687 : Blo 1752577 1972687 := bstep (se 1 (by rfl) ⟨1479515, by rfl⟩ : syracuseStep 1972687 = 2959031) B2959031
theorem B3947039 : Blo 1752577 3947039 := bstep (se 1 (by rfl) ⟨2960279, by rfl⟩ : syracuseStep 3947039 = 5920559) B5920559
theorem B3553883 : Blo 1752577 3553883 := bstep (se 1 (by rfl) ⟨2665412, by rfl⟩ : syracuseStep 3553883 = 5330825) B5330825
theorem B14973569 : Blo 1752577 14973569 := bstep (se 2 (by rfl) ⟨5615088, by rfl⟩ : syracuseStep 14973569 = 11230177) B11230177
theorem B3947273 : Blo 1752577 3947273 := bstep (se 2 (by rfl) ⟨1480227, by rfl⟩ : syracuseStep 3947273 = 2960455) B2960455
theorem B13319315 : Blo 1752577 13319315 := bstep (se 1 (by rfl) ⟨9989486, by rfl⟩ : syracuseStep 13319315 = 19978973) B19978973
theorem B6659279 : Blo 1752577 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B6749399 : Blo 1752577 6749399 := bstep (se 1 (by rfl) ⟨5062049, by rfl⟩ : syracuseStep 6749399 = 10124099) B10124099
theorem B1973479 : Blo 1752577 1973479 := bstep (se 1 (by rfl) ⟨1480109, by rfl⟩ : syracuseStep 1973479 = 2960219) B2960219
theorem B14220593 : Blo 1752577 14220593 := bstep (se 2 (by rfl) ⟨5332722, by rfl⟩ : syracuseStep 14220593 = 10665445) B10665445
theorem B2628935 : Blo 1752577 2628935 := bstep (se 1 (by rfl) ⟨1971701, by rfl⟩ : syracuseStep 2628935 = 3943403) B3943403
theorem B18005327 : Blo 1752577 18005327 := bstep (se 1 (by rfl) ⟨13503995, by rfl⟩ : syracuseStep 18005327 = 27007991) B27007991
theorem B2629097 : Blo 1752577 2629097 := bstep (se 2 (by rfl) ⟨985911, by rfl⟩ : syracuseStep 2629097 = 1971823) B1971823
theorem B1752687 : Blo 1752577 1752687 := bstep (se 1 (by rfl) ⟨1314515, by rfl⟩ : syracuseStep 1752687 = 2629031) B2629031
theorem B2629241 : Blo 1752577 2629241 := bstep (se 2 (by rfl) ⟨985965, by rfl⟩ : syracuseStep 2629241 = 1971931) B1971931
theorem B1752743 : Blo 1752577 1752743 := bstep (se 1 (by rfl) ⟨1314557, by rfl⟩ : syracuseStep 1752743 = 2629115) B2629115
theorem B2498215 : Blo 1752577 2498215 := bstep (se 1 (by rfl) ⟨1873661, by rfl⟩ : syracuseStep 2498215 = 3747323) B3747323
theorem B19226321 : Blo 1752577 19226321 := bstep (se 2 (by rfl) ⟨7209870, by rfl⟩ : syracuseStep 19226321 = 14419741) B14419741
theorem B1752807 : Blo 1752577 1752807 := bstep (se 1 (by rfl) ⟨1314605, by rfl⟩ : syracuseStep 1752807 = 2629211) B2629211
theorem B1752863 : Blo 1752577 1752863 := bstep (se 1 (by rfl) ⟨1314647, by rfl⟩ : syracuseStep 1752863 = 2629295) B2629295
theorem B1752943 : Blo 1752577 1752943 := bstep (se 1 (by rfl) ⟨1314707, by rfl⟩ : syracuseStep 1752943 = 2629415) B2629415
theorem B2629487 : Blo 1752577 2629487 := bstep (se 1 (by rfl) ⟨1972115, by rfl⟩ : syracuseStep 2629487 = 3944231) B3944231
theorem B1752999 : Blo 1752577 1752999 := bstep (se 1 (by rfl) ⟨1314749, by rfl⟩ : syracuseStep 1752999 = 2629499) B2629499
theorem B2629727 : Blo 1752577 2629727 := bstep (se 1 (by rfl) ⟨1972295, by rfl⟩ : syracuseStep 2629727 = 3944591) B3944591
theorem B8994925 : Blo 1752577 8994925 := bstep (se 3 (by rfl) ⟨1686548, by rfl⟩ : syracuseStep 8994925 = 3373097) B3373097
theorem B2220139 : Blo 1752577 2220139 := bstep (se 1 (by rfl) ⟨1665104, by rfl⟩ : syracuseStep 2220139 = 3330209) B3330209
theorem B2629787 : Blo 1752577 2629787 := bstep (se 1 (by rfl) ⟨1972340, by rfl⟩ : syracuseStep 2629787 = 3944681) B3944681
theorem B6660251 : Blo 1752577 6660251 := bstep (se 1 (by rfl) ⟨4995188, by rfl⟩ : syracuseStep 6660251 = 9990377) B9990377
theorem B6750427 : Blo 1752577 6750427 := bstep (se 1 (by rfl) ⟨5062820, by rfl⟩ : syracuseStep 6750427 = 10125641) B10125641
theorem B2629871 : Blo 1752577 2629871 := bstep (se 1 (by rfl) ⟨1972403, by rfl⟩ : syracuseStep 2629871 = 3944807) B3944807
theorem B2810153 : Blo 1752577 2810153 := bstep (se 2 (by rfl) ⟨1053807, by rfl⟩ : syracuseStep 2810153 = 2107615) B2107615
theorem B1753447 : Blo 1752577 1753447 := bstep (se 1 (by rfl) ⟨1315085, by rfl⟩ : syracuseStep 1753447 = 2630171) B2630171
theorem B5915051 : Blo 1752577 5915051 := bstep (se 1 (by rfl) ⟨4436288, by rfl⟩ : syracuseStep 5915051 = 8872577) B8872577
theorem B1753567 : Blo 1752577 1753567 := bstep (se 1 (by rfl) ⟨1315175, by rfl⟩ : syracuseStep 1753567 = 2630351) B2630351
theorem B1753575 : Blo 1752577 1753575 := bstep (se 1 (by rfl) ⟨1315181, by rfl⟩ : syracuseStep 1753575 = 2630363) B2630363
theorem B2630249 : Blo 1752577 2630249 := bstep (se 2 (by rfl) ⟨986343, by rfl⟩ : syracuseStep 2630249 = 1972687) B1972687
theorem B2630255 : Blo 1752577 2630255 := bstep (se 1 (by rfl) ⟨1972691, by rfl⟩ : syracuseStep 2630255 = 3945383) B3945383
theorem B1753851 : Blo 1752577 1753851 := bstep (se 1 (by rfl) ⟨1315388, by rfl⟩ : syracuseStep 1753851 = 2630777) B2630777
theorem B5915591 : Blo 1752577 5915591 := bstep (se 1 (by rfl) ⟨4436693, by rfl⟩ : syracuseStep 5915591 = 8873387) B8873387
theorem B5694503 : Blo 1752577 5694503 := bstep (se 1 (by rfl) ⟨4270877, by rfl⟩ : syracuseStep 5694503 = 8541755) B8541755
theorem B2958491 : Blo 1752577 2958491 := bstep (se 1 (by rfl) ⟨2218868, by rfl⟩ : syracuseStep 2958491 = 4437737) B4437737
theorem B2630879 : Blo 1752577 2630879 := bstep (se 1 (by rfl) ⟨1973159, by rfl⟩ : syracuseStep 2630879 = 3946319) B3946319
theorem B144041273 : Blo 1752577 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B1754431 : Blo 1752577 1754431 := bstep (se 1 (by rfl) ⟨1315823, by rfl⟩ : syracuseStep 1754431 = 2631647) B2631647
theorem B1754439 : Blo 1752577 1754439 := bstep (se 1 (by rfl) ⟨1315829, by rfl⟩ : syracuseStep 1754439 = 2631659) B2631659
theorem B42648929 : Blo 1752577 42648929 := bstep (se 2 (by rfl) ⟨15993348, by rfl⟩ : syracuseStep 42648929 = 31986697) B31986697
theorem B1754471 : Blo 1752577 1754471 := bstep (se 1 (by rfl) ⟨1315853, by rfl⟩ : syracuseStep 1754471 = 2631707) B2631707
theorem B2631119 : Blo 1752577 2631119 := bstep (se 1 (by rfl) ⟨1973339, by rfl⟩ : syracuseStep 2631119 = 3946679) B3946679
theorem B2631305 : Blo 1752577 2631305 := bstep (se 2 (by rfl) ⟨986739, by rfl⟩ : syracuseStep 2631305 = 1973479) B1973479
theorem B2631359 : Blo 1752577 2631359 := bstep (se 1 (by rfl) ⟨1973519, by rfl⟩ : syracuseStep 2631359 = 3947039) B3947039
theorem B2369255 : Blo 1752577 2369255 := bstep (se 1 (by rfl) ⟨1776941, by rfl⟩ : syracuseStep 2369255 = 3553883) B3553883
theorem B2631515 : Blo 1752577 2631515 := bstep (se 1 (by rfl) ⟨1973636, by rfl⟩ : syracuseStep 2631515 = 3947273) B3947273
theorem B3000287 : Blo 1752577 3000287 := bstep (se 1 (by rfl) ⟨2250215, by rfl⟩ : syracuseStep 3000287 = 4500431) B4500431
theorem B4499599 : Blo 1752577 4499599 := bstep (se 1 (by rfl) ⟨3374699, by rfl⟩ : syracuseStep 4499599 = 6749399) B6749399
theorem B9480395 : Blo 1752577 9480395 := bstep (se 1 (by rfl) ⟨7110296, by rfl⟩ : syracuseStep 9480395 = 14220593) B14220593
theorem B12003551 : Blo 1752577 12003551 := bstep (se 1 (by rfl) ⟨9002663, by rfl⟩ : syracuseStep 12003551 = 18005327) B18005327
theorem B3328553 : Blo 1752577 3328553 := bstep (se 2 (by rfl) ⟨1248207, by rfl⟩ : syracuseStep 3328553 = 2496415) B2496415
theorem B4991645 : Blo 1752577 4991645 := bstep (se 3 (by rfl) ⟨935933, by rfl⟩ : syracuseStep 4991645 = 1871867) B1871867
theorem B68365073 : Blo 1752577 68365073 := bstep (se 2 (by rfl) ⟨25636902, by rfl⟩ : syracuseStep 68365073 = 51273805) B51273805
theorem B2960239 : Blo 1752577 2960239 := bstep (se 1 (by rfl) ⟨2220179, by rfl⟩ : syracuseStep 2960239 = 4440359) B4440359
theorem B13323203 : Blo 1752577 13323203 := bstep (se 1 (by rfl) ⟨9992402, by rfl⟩ : syracuseStep 13323203 = 19984805) B19984805
theorem B80964829 : Blo 1752577 80964829 := bstep (se 3 (by rfl) ⟨15180905, by rfl⟩ : syracuseStep 80964829 = 30361811) B30361811
theorem B19967309 : Blo 1752577 19967309 := bstep (se 3 (by rfl) ⟨3743870, by rfl⟩ : syracuseStep 19967309 = 7487741) B7487741
theorem B9989851 : Blo 1752577 9989851 := bstep (se 1 (by rfl) ⟨7492388, by rfl⟩ : syracuseStep 9989851 = 14984777) B14984777
theorem B22777807 : Blo 1752577 22777807 := bstep (se 1 (by rfl) ⟨17083355, by rfl⟩ : syracuseStep 22777807 = 34166711) B34166711
theorem B9990125 : Blo 1752577 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B4993127 : Blo 1752577 4993127 := bstep (se 1 (by rfl) ⟨3744845, by rfl⟩ : syracuseStep 4993127 = 7489691) B7489691
theorem B3944609 : Blo 1752577 3944609 := bstep (se 2 (by rfl) ⟨1479228, by rfl⟩ : syracuseStep 3944609 = 2958457) B2958457
theorem B19214567 : Blo 1752577 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B9982379 : Blo 1752577 9982379 := bstep (se 1 (by rfl) ⟨7486784, by rfl⟩ : syracuseStep 9982379 = 14973569) B14973569
theorem B3944987 : Blo 1752577 3944987 := bstep (se 1 (by rfl) ⟨2958740, by rfl⟩ : syracuseStep 3944987 = 5917481) B5917481
theorem B38449829 : Blo 1752577 38449829 := bstep (se 4 (by rfl) ⟨3604671, by rfl⟩ : syracuseStep 38449829 = 7209343) B7209343
theorem B3945167 : Blo 1752577 3945167 := bstep (se 1 (by rfl) ⟨2958875, by rfl⟩ : syracuseStep 3945167 = 5917751) B5917751
theorem B3330953 : Blo 1752577 3330953 := bstep (se 2 (by rfl) ⟨1249107, by rfl⟩ : syracuseStep 3330953 = 2498215) B2498215
theorem B31208489 : Blo 1752577 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B12817547 : Blo 1752577 12817547 := bstep (se 1 (by rfl) ⟨9613160, by rfl⟩ : syracuseStep 12817547 = 19226321) B19226321
theorem B4994311 : Blo 1752577 4994311 := bstep (se 1 (by rfl) ⟨3745733, by rfl⟩ : syracuseStep 4994311 = 7491467) B7491467
theorem B3159353 : Blo 1752577 3159353 := bstep (se 2 (by rfl) ⟨1184757, by rfl⟩ : syracuseStep 3159353 = 2369515) B2369515
theorem B11236715 : Blo 1752577 11236715 := bstep (se 1 (by rfl) ⟨8427536, by rfl⟩ : syracuseStep 11236715 = 16855073) B16855073
theorem B1971679 : Blo 1752577 1971679 := bstep (se 1 (by rfl) ⟨1478759, by rfl⟩ : syracuseStep 1971679 = 2957519) B2957519
theorem B9483749 : Blo 1752577 9483749 := bstep (se 4 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 9483749 = 1778203) B1778203
theorem B3945959 : Blo 1752577 3945959 := bstep (se 1 (by rfl) ⟨2959469, by rfl⟩ : syracuseStep 3945959 = 5918939) B5918939
theorem B9983519 : Blo 1752577 9983519 := bstep (se 1 (by rfl) ⟨7487639, by rfl⟩ : syracuseStep 9983519 = 14975279) B14975279
theorem B2496091 : Blo 1752577 2496091 := bstep (se 1 (by rfl) ⟨1872068, by rfl⟩ : syracuseStep 2496091 = 3744137) B3744137
theorem B13309595 : Blo 1752577 13309595 := bstep (se 1 (by rfl) ⟨9982196, by rfl⟩ : syracuseStep 13309595 = 19964393) B19964393
theorem B3946139 : Blo 1752577 3946139 := bstep (se 1 (by rfl) ⟨2959604, by rfl⟩ : syracuseStep 3946139 = 5919209) B5919209
theorem B18970301 : Blo 1752577 18970301 := bstep (se 3 (by rfl) ⟨3556931, by rfl⟩ : syracuseStep 18970301 = 7113863) B7113863
theorem B3946337 : Blo 1752577 3946337 := bstep (se 2 (by rfl) ⟨1479876, by rfl⟩ : syracuseStep 3946337 = 2959753) B2959753
theorem B4437899 : Blo 1752577 4437899 := bstep (se 1 (by rfl) ⟨3328424, by rfl⟩ : syracuseStep 4437899 = 6656849) B6656849
theorem B1972255 : Blo 1752577 1972255 := bstep (se 1 (by rfl) ⟨1479191, by rfl⟩ : syracuseStep 1972255 = 2958383) B2958383
theorem B8878247 : Blo 1752577 8878247 := bstep (se 1 (by rfl) ⟨6658685, by rfl⟩ : syracuseStep 8878247 = 13317371) B13317371
theorem B13318343 : Blo 1752577 13318343 := bstep (se 1 (by rfl) ⟨9988757, by rfl⟩ : syracuseStep 13318343 = 19977515) B19977515
theorem B4683995 : Blo 1752577 4683995 := bstep (se 1 (by rfl) ⟨3512996, by rfl⟩ : syracuseStep 4683995 = 7025993) B7025993
theorem B12638537 : Blo 1752577 12638537 := bstep (se 2 (by rfl) ⟨4739451, by rfl⟩ : syracuseStep 12638537 = 9478903) B9478903
theorem B2218367 : Blo 1752577 2218367 := bstep (se 1 (by rfl) ⟨1663775, by rfl⟩ : syracuseStep 2218367 = 3327551) B3327551
theorem B3201479 : Blo 1752577 3201479 := bstep (se 1 (by rfl) ⟨2401109, by rfl⟩ : syracuseStep 3201479 = 4802219) B4802219
theorem B32004791 : Blo 1752577 32004791 := bstep (se 1 (by rfl) ⟨24003593, by rfl⟩ : syracuseStep 32004791 = 48007187) B48007187
theorem B2497321 : Blo 1752577 2497321 := bstep (se 2 (by rfl) ⟨936495, by rfl⟩ : syracuseStep 2497321 = 1872991) B1872991
theorem B5921639 : Blo 1752577 5921639 := bstep (se 1 (by rfl) ⟨4441229, by rfl⟩ : syracuseStep 5921639 = 8882459) B8882459
theorem B2219071 : Blo 1752577 2219071 := bstep (se 1 (by rfl) ⟨1664303, by rfl⟩ : syracuseStep 2219071 = 3328607) B3328607
theorem B11386001 : Blo 1752577 11386001 := bstep (se 2 (by rfl) ⟨4269750, by rfl⟩ : syracuseStep 11386001 = 8539501) B8539501
theorem B8879543 : Blo 1752577 8879543 := bstep (se 1 (by rfl) ⟨6659657, by rfl⟩ : syracuseStep 8879543 = 13319315) B13319315
theorem B31989181 : Blo 1752577 31989181 := bstep (se 3 (by rfl) ⟨5997971, by rfl⟩ : syracuseStep 31989181 = 11995943) B11995943
theorem B4439519 : Blo 1752577 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B1752623 : Blo 1752577 1752623 := bstep (se 1 (by rfl) ⟨1314467, by rfl⟩ : syracuseStep 1752623 = 2628935) B2628935
theorem B2629223 : Blo 1752577 2629223 := bstep (se 1 (by rfl) ⟨1971917, by rfl⟩ : syracuseStep 2629223 = 3943835) B3943835
theorem B1752731 : Blo 1752577 1752731 := bstep (se 1 (by rfl) ⟨1314548, by rfl⟩ : syracuseStep 1752731 = 2629097) B2629097
theorem B1752827 : Blo 1752577 1752827 := bstep (se 1 (by rfl) ⟨1314620, by rfl⟩ : syracuseStep 1752827 = 2629241) B2629241
theorem B2629385 : Blo 1752577 2629385 := bstep (se 2 (by rfl) ⟨986019, by rfl⟩ : syracuseStep 2629385 = 1972039) B1972039
theorem B1752991 : Blo 1752577 1752991 := bstep (se 1 (by rfl) ⟨1314743, by rfl⟩ : syracuseStep 1752991 = 2629487) B2629487
theorem B9609131 : Blo 1752577 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B2629607 : Blo 1752577 2629607 := bstep (se 1 (by rfl) ⟨1972205, by rfl⟩ : syracuseStep 2629607 = 3944411) B3944411
theorem B2629673 : Blo 1752577 2629673 := bstep (se 2 (by rfl) ⟨986127, by rfl⟩ : syracuseStep 2629673 = 1972255) B1972255
theorem B1753151 : Blo 1752577 1753151 := bstep (se 1 (by rfl) ⟨1314863, by rfl⟩ : syracuseStep 1753151 = 2629727) B2629727
theorem B1753191 : Blo 1752577 1753191 := bstep (se 1 (by rfl) ⟨1314893, by rfl⟩ : syracuseStep 1753191 = 2629787) B2629787
theorem B4440167 : Blo 1752577 4440167 := bstep (se 1 (by rfl) ⟨3330125, by rfl⟩ : syracuseStep 4440167 = 6660251) B6660251
theorem B2629739 : Blo 1752577 2629739 := bstep (se 1 (by rfl) ⟨1972304, by rfl⟩ : syracuseStep 2629739 = 3944609) B3944609
theorem B11993233 : Blo 1752577 11993233 := bstep (se 2 (by rfl) ⟨4497462, by rfl⟩ : syracuseStep 11993233 = 8994925) B8994925
theorem B1753247 : Blo 1752577 1753247 := bstep (se 1 (by rfl) ⟨1314935, by rfl⟩ : syracuseStep 1753247 = 2629871) B2629871
theorem B2629991 : Blo 1752577 2629991 := bstep (se 1 (by rfl) ⟨1972493, by rfl⟩ : syracuseStep 2629991 = 3944987) B3944987
theorem B1753499 : Blo 1752577 1753499 := bstep (se 1 (by rfl) ⟨1315124, by rfl⟩ : syracuseStep 1753499 = 2630249) B2630249
theorem B1753503 : Blo 1752577 1753503 := bstep (se 1 (by rfl) ⟨1315127, by rfl⟩ : syracuseStep 1753503 = 2630255) B2630255
theorem B25633219 : Blo 1752577 25633219 := bstep (se 1 (by rfl) ⟨19224914, by rfl⟩ : syracuseStep 25633219 = 38449829) B38449829
theorem B2630111 : Blo 1752577 2630111 := bstep (se 1 (by rfl) ⟨1972583, by rfl⟩ : syracuseStep 2630111 = 3945167) B3945167
theorem B2220635 : Blo 1752577 2220635 := bstep (se 1 (by rfl) ⟨1665476, by rfl⟩ : syracuseStep 2220635 = 3330953) B3330953
theorem B8545031 : Blo 1752577 8545031 := bstep (se 1 (by rfl) ⟨6408773, by rfl⟩ : syracuseStep 8545031 = 12817547) B12817547
theorem B1753919 : Blo 1752577 1753919 := bstep (se 1 (by rfl) ⟨1315439, by rfl⟩ : syracuseStep 1753919 = 2630879) B2630879
theorem B2106235 : Blo 1752577 2106235 := bstep (se 1 (by rfl) ⟨1579676, by rfl⟩ : syracuseStep 2106235 = 3159353) B3159353
theorem B96027515 : Blo 1752577 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B1754079 : Blo 1752577 1754079 := bstep (se 1 (by rfl) ⟨1315559, by rfl⟩ : syracuseStep 1754079 = 2631119) B2631119
theorem B2630639 : Blo 1752577 2630639 := bstep (se 1 (by rfl) ⟨1972979, by rfl⟩ : syracuseStep 2630639 = 3945959) B3945959
theorem B5915645 : Blo 1752577 5915645 := bstep (se 3 (by rfl) ⟨1109183, by rfl⟩ : syracuseStep 5915645 = 2218367) B2218367
theorem B1754203 : Blo 1752577 1754203 := bstep (se 1 (by rfl) ⟨1315652, by rfl⟩ : syracuseStep 1754203 = 2631305) B2631305
theorem B8873063 : Blo 1752577 8873063 := bstep (se 1 (by rfl) ⟨6654797, by rfl⟩ : syracuseStep 8873063 = 13309595) B13309595
theorem B2630759 : Blo 1752577 2630759 := bstep (se 1 (by rfl) ⟨1973069, by rfl⟩ : syracuseStep 2630759 = 3946139) B3946139
theorem B1754239 : Blo 1752577 1754239 := bstep (se 1 (by rfl) ⟨1315679, by rfl⟩ : syracuseStep 1754239 = 2631359) B2631359
theorem B1754343 : Blo 1752577 1754343 := bstep (se 1 (by rfl) ⟨1315757, by rfl⟩ : syracuseStep 1754343 = 2631515) B2631515
theorem B2630891 : Blo 1752577 2630891 := bstep (se 1 (by rfl) ⟨1973168, by rfl⟩ : syracuseStep 2630891 = 3946337) B3946337
theorem B2958599 : Blo 1752577 2958599 := bstep (se 1 (by rfl) ⟨2218949, by rfl⟩ : syracuseStep 2958599 = 4437899) B4437899
theorem B2958761 : Blo 1752577 2958761 := bstep (se 2 (by rfl) ⟨1109535, by rfl⟩ : syracuseStep 2958761 = 2219071) B2219071
theorem B3122663 : Blo 1752577 3122663 := bstep (se 1 (by rfl) ⟨2341997, by rfl⟩ : syracuseStep 3122663 = 4683995) B4683995
theorem B6318013 : Blo 1752577 6318013 := bstep (se 3 (by rfl) ⟨1184627, by rfl⟩ : syracuseStep 6318013 = 2369255) B2369255
theorem B8882135 : Blo 1752577 8882135 := bstep (se 1 (by rfl) ⟨6661601, by rfl⟩ : syracuseStep 8882135 = 13323203) B13323203
theorem B3328121 : Blo 1752577 3328121 := bstep (se 2 (by rfl) ⟨1248045, by rfl⟩ : syracuseStep 3328121 = 2496091) B2496091
theorem B2959679 : Blo 1752577 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B30370409 : Blo 1752577 30370409 := bstep (se 2 (by rfl) ⟨11388903, by rfl⟩ : syracuseStep 30370409 = 22777807) B22777807
theorem B3328751 : Blo 1752577 3328751 := bstep (se 1 (by rfl) ⟨2496563, by rfl⟩ : syracuseStep 3328751 = 4993127) B4993127
theorem B2960185 : Blo 1752577 2960185 := bstep (se 2 (by rfl) ⟨1110069, by rfl⟩ : syracuseStep 2960185 = 2220139) B2220139
theorem B5999465 : Blo 1752577 5999465 := bstep (se 2 (by rfl) ⟨2249799, by rfl⟩ : syracuseStep 5999465 = 4499599) B4499599
theorem B3943367 : Blo 1752577 3943367 := bstep (se 1 (by rfl) ⟨2957525, by rfl⟩ : syracuseStep 3943367 = 5915051) B5915051
theorem B6654919 : Blo 1752577 6654919 := bstep (se 1 (by rfl) ⟨4991189, by rfl⟩ : syracuseStep 6654919 = 9982379) B9982379
theorem B3943727 : Blo 1752577 3943727 := bstep (se 1 (by rfl) ⟨2957795, by rfl⟩ : syracuseStep 3943727 = 5915591) B5915591
theorem B7491143 : Blo 1752577 7491143 := bstep (se 1 (by rfl) ⟨5618357, by rfl⟩ : syracuseStep 7491143 = 11236715) B11236715
theorem B6655679 : Blo 1752577 6655679 := bstep (se 1 (by rfl) ⟨4991759, by rfl⟩ : syracuseStep 6655679 = 9983519) B9983519
theorem B3329761 : Blo 1752577 3329761 := bstep (se 2 (by rfl) ⟨1248660, by rfl⟩ : syracuseStep 3329761 = 2497321) B2497321
theorem B431812421 : Blo 1752577 431812421 := bstep (se 4 (by rfl) ⟨40482414, by rfl⟩ : syracuseStep 431812421 = 80964829) B80964829
theorem B8876141 : Blo 1752577 8876141 := bstep (se 3 (by rfl) ⟨1664276, by rfl⟩ : syracuseStep 8876141 = 3328553) B3328553
theorem B5918831 : Blo 1752577 5918831 := bstep (se 1 (by rfl) ⟨4439123, by rfl⟩ : syracuseStep 5918831 = 8878247) B8878247
theorem B6320263 : Blo 1752577 6320263 := bstep (se 1 (by rfl) ⟨4740197, by rfl⟩ : syracuseStep 6320263 = 9480395) B9480395
theorem B8425691 : Blo 1752577 8425691 := bstep (se 1 (by rfl) ⟨6319268, by rfl⟩ : syracuseStep 8425691 = 12638537) B12638537
theorem B21336527 : Blo 1752577 21336527 := bstep (se 1 (by rfl) ⟨16002395, by rfl⟩ : syracuseStep 21336527 = 32004791) B32004791
theorem B45576715 : Blo 1752577 45576715 := bstep (se 1 (by rfl) ⟨34182536, by rfl⟩ : syracuseStep 45576715 = 68365073) B68365073
theorem B42652241 : Blo 1752577 42652241 := bstep (se 2 (by rfl) ⟨15994590, by rfl⟩ : syracuseStep 42652241 = 31989181) B31989181
theorem B34149109 : Blo 1752577 34149109 := bstep (se 5 (by rfl) ⟨1600739, by rfl⟩ : syracuseStep 34149109 = 3201479) B3201479
theorem B7590667 : Blo 1752577 7590667 := bstep (se 1 (by rfl) ⟨5693000, by rfl⟩ : syracuseStep 7590667 = 11386001) B11386001
theorem B5919695 : Blo 1752577 5919695 := bstep (se 1 (by rfl) ⟨4439771, by rfl⟩ : syracuseStep 5919695 = 8879543) B8879543
theorem B8000765 : Blo 1752577 8000765 := bstep (se 3 (by rfl) ⟨1500143, by rfl⟩ : syracuseStep 8000765 = 3000287) B3000287
theorem B15185341 : Blo 1752577 15185341 := bstep (se 3 (by rfl) ⟨2847251, by rfl⟩ : syracuseStep 15185341 = 5694503) B5694503
theorem B12809711 : Blo 1752577 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B9000569 : Blo 1752577 9000569 := bstep (se 2 (by rfl) ⟨3375213, by rfl⟩ : syracuseStep 9000569 = 6750427) B6750427
theorem B20805659 : Blo 1752577 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B1972327 : Blo 1752577 1972327 := bstep (se 1 (by rfl) ⟨1479245, by rfl⟩ : syracuseStep 1972327 = 2958491) B2958491
theorem B7493741 : Blo 1752577 7493741 := bstep (se 3 (by rfl) ⟨1405076, by rfl⟩ : syracuseStep 7493741 = 2810153) B2810153
theorem B28432619 : Blo 1752577 28432619 := bstep (se 1 (by rfl) ⟨21324464, by rfl⟩ : syracuseStep 28432619 = 42648929) B42648929
theorem B6322499 : Blo 1752577 6322499 := bstep (se 1 (by rfl) ⟨4741874, by rfl⟩ : syracuseStep 6322499 = 9483749) B9483749
theorem B12646867 : Blo 1752577 12646867 := bstep (se 1 (by rfl) ⟨9485150, by rfl⟩ : syracuseStep 12646867 = 18970301) B18970301
theorem B3946985 : Blo 1752577 3946985 := bstep (se 2 (by rfl) ⟨1480119, by rfl⟩ : syracuseStep 3946985 = 2960239) B2960239
theorem B8878895 : Blo 1752577 8878895 := bstep (se 1 (by rfl) ⟨6659171, by rfl⟩ : syracuseStep 8878895 = 13318343) B13318343
theorem B8002367 : Blo 1752577 8002367 := bstep (se 1 (by rfl) ⟨6001775, by rfl⟩ : syracuseStep 8002367 = 12003551) B12003551
theorem B6659081 : Blo 1752577 6659081 := bstep (se 2 (by rfl) ⟨2497155, by rfl⟩ : syracuseStep 6659081 = 4994311) B4994311
theorem B13311053 : Blo 1752577 13311053 := bstep (se 3 (by rfl) ⟨2495822, by rfl⟩ : syracuseStep 13311053 = 4991645) B4991645
theorem B3947759 : Blo 1752577 3947759 := bstep (se 1 (by rfl) ⟨2960819, by rfl⟩ : syracuseStep 3947759 = 5921639) B5921639
theorem B2628905 : Blo 1752577 2628905 := bstep (se 2 (by rfl) ⟨985839, by rfl⟩ : syracuseStep 2628905 = 1971679) B1971679
theorem B13311539 : Blo 1752577 13311539 := bstep (se 1 (by rfl) ⟨9983654, by rfl⟩ : syracuseStep 13311539 = 19967309) B19967309
theorem B13319801 : Blo 1752577 13319801 := bstep (se 2 (by rfl) ⟨4994925, by rfl⟩ : syracuseStep 13319801 = 9989851) B9989851
theorem B1752815 : Blo 1752577 1752815 := bstep (se 1 (by rfl) ⟨1314611, by rfl⟩ : syracuseStep 1752815 = 2629223) B2629223
theorem B25624349 : Blo 1752577 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B1752923 : Blo 1752577 1752923 := bstep (se 1 (by rfl) ⟨1314692, by rfl⟩ : syracuseStep 1752923 = 2629385) B2629385
theorem B1753071 : Blo 1752577 1753071 := bstep (se 1 (by rfl) ⟨1314803, by rfl⟩ : syracuseStep 1753071 = 2629607) B2629607
theorem B6660083 : Blo 1752577 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B1753115 : Blo 1752577 1753115 := bstep (se 1 (by rfl) ⟨1314836, by rfl⟩ : syracuseStep 1753115 = 2629673) B2629673
theorem B1753159 : Blo 1752577 1753159 := bstep (se 1 (by rfl) ⟨1314869, by rfl⟩ : syracuseStep 1753159 = 2629739) B2629739
theorem B2629769 : Blo 1752577 2629769 := bstep (se 2 (by rfl) ⟨986163, by rfl⟩ : syracuseStep 2629769 = 1972327) B1972327
theorem B15990977 : Blo 1752577 15990977 := bstep (se 2 (by rfl) ⟨5996616, by rfl⟩ : syracuseStep 15990977 = 11993233) B11993233
theorem B1753327 : Blo 1752577 1753327 := bstep (se 1 (by rfl) ⟨1314995, by rfl⟩ : syracuseStep 1753327 = 2629991) B2629991
theorem B1753407 : Blo 1752577 1753407 := bstep (se 1 (by rfl) ⟨1315055, by rfl⟩ : syracuseStep 1753407 = 2630111) B2630111
theorem B28434827 : Blo 1752577 28434827 := bstep (se 1 (by rfl) ⟨21326120, by rfl⟩ : syracuseStep 28434827 = 42652241) B42652241
theorem B34177625 : Blo 1752577 34177625 := bstep (se 2 (by rfl) ⟨12816609, by rfl⟩ : syracuseStep 34177625 = 25633219) B25633219
theorem B1753759 : Blo 1752577 1753759 := bstep (se 1 (by rfl) ⟨1315319, by rfl⟩ : syracuseStep 1753759 = 2630639) B2630639
theorem B60768953 : Blo 1752577 60768953 := bstep (se 2 (by rfl) ⟨22788357, by rfl⟩ : syracuseStep 60768953 = 45576715) B45576715
theorem B5915375 : Blo 1752577 5915375 := bstep (se 1 (by rfl) ⟨4436531, by rfl⟩ : syracuseStep 5915375 = 8873063) B8873063
theorem B1753839 : Blo 1752577 1753839 := bstep (se 1 (by rfl) ⟨1315379, by rfl⟩ : syracuseStep 1753839 = 2630759) B2630759
theorem B1753927 : Blo 1752577 1753927 := bstep (se 1 (by rfl) ⟨1315445, by rfl⟩ : syracuseStep 1753927 = 2630891) B2630891
theorem B5333843 : Blo 1752577 5333843 := bstep (se 1 (by rfl) ⟨4000382, by rfl⟩ : syracuseStep 5333843 = 8000765) B8000765
theorem B45532145 : Blo 1752577 45532145 := bstep (se 2 (by rfl) ⟨17074554, by rfl⟩ : syracuseStep 45532145 = 34149109) B34149109
theorem B8873225 : Blo 1752577 8873225 := bstep (se 2 (by rfl) ⟨3327459, by rfl⟩ : syracuseStep 8873225 = 6654919) B6654919
theorem B13870439 : Blo 1752577 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B2631323 : Blo 1752577 2631323 := bstep (se 1 (by rfl) ⟨1973492, by rfl⟩ : syracuseStep 2631323 = 3946985) B3946985
theorem B5334911 : Blo 1752577 5334911 := bstep (se 1 (by rfl) ⟨4001183, by rfl⟩ : syracuseStep 5334911 = 8002367) B8002367
theorem B8874035 : Blo 1752577 8874035 := bstep (se 1 (by rfl) ⟨6655526, by rfl⟩ : syracuseStep 8874035 = 13311053) B13311053
theorem B2631839 : Blo 1752577 2631839 := bstep (se 1 (by rfl) ⟨1973879, by rfl⟩ : syracuseStep 2631839 = 3947759) B3947759
theorem B8874359 : Blo 1752577 8874359 := bstep (se 1 (by rfl) ⟨6655769, by rfl⟩ : syracuseStep 8874359 = 13311539) B13311539
theorem B17082899 : Blo 1752577 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B8424017 : Blo 1752577 8424017 := bstep (se 2 (by rfl) ⟨3159006, by rfl⟩ : syracuseStep 8424017 = 6318013) B6318013
theorem B2960111 : Blo 1752577 2960111 := bstep (se 1 (by rfl) ⟨2220083, by rfl⟩ : syracuseStep 2960111 = 4440167) B4440167
theorem B5917427 : Blo 1752577 5917427 := bstep (se 1 (by rfl) ⟨4438070, by rfl⟩ : syracuseStep 5917427 = 8876141) B8876141
theorem B14224351 : Blo 1752577 14224351 := bstep (se 1 (by rfl) ⟨10668263, by rfl⟩ : syracuseStep 14224351 = 21336527) B21336527
theorem B5696687 : Blo 1752577 5696687 := bstep (se 1 (by rfl) ⟨4272515, by rfl⟩ : syracuseStep 5696687 = 8545031) B8545031
theorem B16862489 : Blo 1752577 16862489 := bstep (se 2 (by rfl) ⟨6323433, by rfl⟩ : syracuseStep 16862489 = 12646867) B12646867
theorem B3943763 : Blo 1752577 3943763 := bstep (se 1 (by rfl) ⟨2957822, by rfl⟩ : syracuseStep 3943763 = 5915645) B5915645
theorem B10120889 : Blo 1752577 10120889 := bstep (se 2 (by rfl) ⟨3795333, by rfl⟩ : syracuseStep 10120889 = 7590667) B7590667
theorem B4214999 : Blo 1752577 4214999 := bstep (se 1 (by rfl) ⟨3161249, by rfl⟩ : syracuseStep 4214999 = 6322499) B6322499
theorem B20246939 : Blo 1752577 20246939 := bstep (se 1 (by rfl) ⟨15185204, by rfl⟩ : syracuseStep 20246939 = 30370409) B30370409
theorem B5919263 : Blo 1752577 5919263 := bstep (se 1 (by rfl) ⟨4439447, by rfl⟩ : syracuseStep 5919263 = 8878895) B8878895
theorem B20247121 : Blo 1752577 20247121 := bstep (se 2 (by rfl) ⟨7592670, by rfl⟩ : syracuseStep 20247121 = 15185341) B15185341
theorem B4994095 : Blo 1752577 4994095 := bstep (se 1 (by rfl) ⟨3745571, by rfl⟩ : syracuseStep 4994095 = 7491143) B7491143
theorem B4437119 : Blo 1752577 4437119 := bstep (se 1 (by rfl) ⟨3327839, by rfl⟩ : syracuseStep 4437119 = 6655679) B6655679
theorem B3945887 : Blo 1752577 3945887 := bstep (se 1 (by rfl) ⟨2959415, by rfl⟩ : syracuseStep 3945887 = 5918831) B5918831
theorem B5617127 : Blo 1752577 5617127 := bstep (se 1 (by rfl) ⟨4212845, by rfl⟩ : syracuseStep 5617127 = 8425691) B8425691
theorem B8427017 : Blo 1752577 8427017 := bstep (se 2 (by rfl) ⟨3160131, by rfl⟩ : syracuseStep 8427017 = 6320263) B6320263
theorem B64018343 : Blo 1752577 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B3946463 : Blo 1752577 3946463 := bstep (se 1 (by rfl) ⟨2959847, by rfl⟩ : syracuseStep 3946463 = 5919695) B5919695
theorem B1972399 : Blo 1752577 1972399 := bstep (se 1 (by rfl) ⟨1479299, by rfl⟩ : syracuseStep 1972399 = 2958599) B2958599
theorem B1972507 : Blo 1752577 1972507 := bstep (se 1 (by rfl) ⟨1479380, by rfl⟩ : syracuseStep 1972507 = 2958761) B2958761
theorem B3946913 : Blo 1752577 3946913 := bstep (se 2 (by rfl) ⟨1480092, by rfl⟩ : syracuseStep 3946913 = 2960185) B2960185
theorem B2808313 : Blo 1752577 2808313 := bstep (se 2 (by rfl) ⟨1053117, by rfl⟩ : syracuseStep 2808313 = 2106235) B2106235
theorem B34159229 : Blo 1752577 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B5921423 : Blo 1752577 5921423 := bstep (se 1 (by rfl) ⟨4441067, by rfl⟩ : syracuseStep 5921423 = 8882135) B8882135
theorem B4995827 : Blo 1752577 4995827 := bstep (se 1 (by rfl) ⟨3746870, by rfl⟩ : syracuseStep 4995827 = 7493741) B7493741
theorem B2218747 : Blo 1752577 2218747 := bstep (se 1 (by rfl) ⟨1664060, by rfl⟩ : syracuseStep 2218747 = 3328121) B3328121
theorem B18955079 : Blo 1752577 18955079 := bstep (se 1 (by rfl) ⟨14216309, by rfl⟩ : syracuseStep 18955079 = 28432619) B28432619
theorem B1973119 : Blo 1752577 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B5921693 : Blo 1752577 5921693 := bstep (se 3 (by rfl) ⟨1110317, by rfl⟩ : syracuseStep 5921693 = 2220635) B2220635
theorem B24001517 : Blo 1752577 24001517 := bstep (se 3 (by rfl) ⟨4500284, by rfl⟩ : syracuseStep 24001517 = 9000569) B9000569
theorem B2219167 : Blo 1752577 2219167 := bstep (se 1 (by rfl) ⟨1664375, by rfl⟩ : syracuseStep 2219167 = 3328751) B3328751
theorem B2628911 : Blo 1752577 2628911 := bstep (se 1 (by rfl) ⟨1971683, by rfl⟩ : syracuseStep 2628911 = 3943367) B3943367
theorem B4439387 : Blo 1752577 4439387 := bstep (se 1 (by rfl) ⟨3329540, by rfl⟩ : syracuseStep 4439387 = 6659081) B6659081
theorem B4440055 : Blo 1752577 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B1752603 : Blo 1752577 1752603 := bstep (se 1 (by rfl) ⟨1314452, by rfl⟩ : syracuseStep 1752603 = 2628905) B2628905
theorem B2629151 : Blo 1752577 2629151 := bstep (se 1 (by rfl) ⟨1971863, by rfl⟩ : syracuseStep 2629151 = 3943727) B3943727
theorem B15998573 : Blo 1752577 15998573 := bstep (se 3 (by rfl) ⟨2999732, by rfl⟩ : syracuseStep 15998573 = 5999465) B5999465
theorem B4439681 : Blo 1752577 4439681 := bstep (se 2 (by rfl) ⟨1664880, by rfl⟩ : syracuseStep 4439681 = 3329761) B3329761
theorem B33308405 : Blo 1752577 33308405 := bstep (se 5 (by rfl) ⟨1561331, by rfl⟩ : syracuseStep 33308405 = 3122663) B3122663
theorem B8879867 : Blo 1752577 8879867 := bstep (se 1 (by rfl) ⟨6659900, by rfl⟩ : syracuseStep 8879867 = 13319801) B13319801
theorem B287874947 : Blo 1752577 287874947 := bstep (se 1 (by rfl) ⟨215906210, by rfl⟩ : syracuseStep 287874947 = 431812421) B431812421
theorem B1753179 : Blo 1752577 1753179 := bstep (se 1 (by rfl) ⟨1314884, by rfl⟩ : syracuseStep 1753179 = 2629769) B2629769
theorem B2809999 : Blo 1752577 2809999 := bstep (se 1 (by rfl) ⟨2107499, by rfl⟩ : syracuseStep 2809999 = 4214999) B4214999
theorem B2629865 : Blo 1752577 2629865 := bstep (se 2 (by rfl) ⟨986199, by rfl⟩ : syracuseStep 2629865 = 1972399) B1972399
theorem B18956551 : Blo 1752577 18956551 := bstep (se 1 (by rfl) ⟨14217413, by rfl⟩ : syracuseStep 18956551 = 28434827) B28434827
theorem B2630009 : Blo 1752577 2630009 := bstep (se 2 (by rfl) ⟨986253, by rfl⟩ : syracuseStep 2630009 = 1972507) B1972507
theorem B3555895 : Blo 1752577 3555895 := bstep (se 1 (by rfl) ⟨2666921, by rfl⟩ : syracuseStep 3555895 = 5333843) B5333843
theorem B2958079 : Blo 1752577 2958079 := bstep (se 1 (by rfl) ⟨2218559, by rfl⟩ : syracuseStep 2958079 = 4437119) B4437119
theorem B5915483 : Blo 1752577 5915483 := bstep (se 1 (by rfl) ⟨4436612, by rfl⟩ : syracuseStep 5915483 = 8873225) B8873225
theorem B2630591 : Blo 1752577 2630591 := bstep (se 1 (by rfl) ⟨1972943, by rfl⟩ : syracuseStep 2630591 = 3945887) B3945887
theorem B2958329 : Blo 1752577 2958329 := bstep (se 2 (by rfl) ⟨1109373, by rfl⟩ : syracuseStep 2958329 = 2218747) B2218747
theorem B1754215 : Blo 1752577 1754215 := bstep (se 1 (by rfl) ⟨1315661, by rfl⟩ : syracuseStep 1754215 = 2631323) B2631323
theorem B2630825 : Blo 1752577 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B3556607 : Blo 1752577 3556607 := bstep (se 1 (by rfl) ⟨2667455, by rfl⟩ : syracuseStep 3556607 = 5334911) B5334911
theorem B18965801 : Blo 1752577 18965801 := bstep (se 2 (by rfl) ⟨7112175, by rfl⟩ : syracuseStep 18965801 = 14224351) B14224351
theorem B2630975 : Blo 1752577 2630975 := bstep (se 1 (by rfl) ⟨1973231, by rfl⟩ : syracuseStep 2630975 = 3946463) B3946463
theorem B5916023 : Blo 1752577 5916023 := bstep (se 1 (by rfl) ⟨4437017, by rfl⟩ : syracuseStep 5916023 = 8874035) B8874035
theorem B1754559 : Blo 1752577 1754559 := bstep (se 1 (by rfl) ⟨1315919, by rfl⟩ : syracuseStep 1754559 = 2631839) B2631839
theorem B2958889 : Blo 1752577 2958889 := bstep (se 2 (by rfl) ⟨1109583, by rfl⟩ : syracuseStep 2958889 = 2219167) B2219167
theorem B5916239 : Blo 1752577 5916239 := bstep (se 1 (by rfl) ⟨4437179, by rfl⟩ : syracuseStep 5916239 = 8874359) B8874359
theorem B2631275 : Blo 1752577 2631275 := bstep (se 1 (by rfl) ⟨1973456, by rfl⟩ : syracuseStep 2631275 = 3946913) B3946913
theorem B11388599 : Blo 1752577 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B16001011 : Blo 1752577 16001011 := bstep (se 1 (by rfl) ⟨12000758, by rfl⟩ : syracuseStep 16001011 = 24001517) B24001517
theorem B11241659 : Blo 1752577 11241659 := bstep (se 1 (by rfl) ⟨8431244, by rfl⟩ : syracuseStep 11241659 = 16862489) B16862489
theorem B2959591 : Blo 1752577 2959591 := bstep (se 1 (by rfl) ⟨2219693, by rfl⟩ : syracuseStep 2959591 = 4439387) B4439387
theorem B2959787 : Blo 1752577 2959787 := bstep (se 1 (by rfl) ⟨2219840, by rfl⟩ : syracuseStep 2959787 = 4439681) B4439681
theorem B191916631 : Blo 1752577 191916631 := bstep (se 1 (by rfl) ⟨143937473, by rfl⟩ : syracuseStep 191916631 = 287874947) B287874947
theorem B14977669 : Blo 1752577 14977669 := bstep (se 4 (by rfl) ⟨1404156, by rfl⟩ : syracuseStep 14977669 = 2808313) B2808313
theorem B22785083 : Blo 1752577 22785083 := bstep (se 1 (by rfl) ⟨17088812, by rfl⟩ : syracuseStep 22785083 = 34177625) B34177625
theorem B40512635 : Blo 1752577 40512635 := bstep (se 1 (by rfl) ⟨30384476, by rfl⟩ : syracuseStep 40512635 = 60768953) B60768953
theorem B15191165 : Blo 1752577 15191165 := bstep (se 3 (by rfl) ⟨2848343, by rfl⟩ : syracuseStep 15191165 = 5696687) B5696687
theorem B3943583 : Blo 1752577 3943583 := bstep (se 1 (by rfl) ⟨2957687, by rfl⟩ : syracuseStep 3943583 = 5915375) B5915375
theorem B42642605 : Blo 1752577 42642605 := bstep (se 3 (by rfl) ⟨7995488, by rfl⟩ : syracuseStep 42642605 = 15990977) B15990977
theorem B30354763 : Blo 1752577 30354763 := bstep (se 1 (by rfl) ⟨22766072, by rfl⟩ : syracuseStep 30354763 = 45532145) B45532145
theorem B26996161 : Blo 1752577 26996161 := bstep (se 2 (by rfl) ⟨10123560, by rfl⟩ : syracuseStep 26996161 = 20247121) B20247121
theorem B14979005 : Blo 1752577 14979005 := bstep (se 3 (by rfl) ⟨2808563, by rfl⟩ : syracuseStep 14979005 = 5617127) B5617127
theorem B5616011 : Blo 1752577 5616011 := bstep (se 1 (by rfl) ⟨4212008, by rfl⟩ : syracuseStep 5616011 = 8424017) B8424017
theorem B26989037 : Blo 1752577 26989037 := bstep (se 3 (by rfl) ⟨5060444, by rfl⟩ : syracuseStep 26989037 = 10120889) B10120889
theorem B3944951 : Blo 1752577 3944951 := bstep (se 1 (by rfl) ⟨2958713, by rfl⟩ : syracuseStep 3944951 = 5917427) B5917427
theorem B3330551 : Blo 1752577 3330551 := bstep (se 1 (by rfl) ⟨2497913, by rfl⟩ : syracuseStep 3330551 = 4995827) B4995827
theorem B12636719 : Blo 1752577 12636719 := bstep (se 1 (by rfl) ⟨9477539, by rfl⟩ : syracuseStep 12636719 = 18955079) B18955079
theorem B22205603 : Blo 1752577 22205603 := bstep (se 1 (by rfl) ⟨16654202, by rfl⟩ : syracuseStep 22205603 = 33308405) B33308405
theorem B5919911 : Blo 1752577 5919911 := bstep (se 1 (by rfl) ⟨4439933, by rfl⟩ : syracuseStep 5919911 = 8879867) B8879867
theorem B5920073 : Blo 1752577 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B13497959 : Blo 1752577 13497959 := bstep (se 1 (by rfl) ⟨10123469, by rfl⟩ : syracuseStep 13497959 = 20246939) B20246939
theorem B3946175 : Blo 1752577 3946175 := bstep (se 1 (by rfl) ⟨2959631, by rfl⟩ : syracuseStep 3946175 = 5919263) B5919263
theorem B9246959 : Blo 1752577 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B5618011 : Blo 1752577 5618011 := bstep (se 1 (by rfl) ⟨4213508, by rfl⟩ : syracuseStep 5618011 = 8427017) B8427017
theorem B42678895 : Blo 1752577 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B6658793 : Blo 1752577 6658793 := bstep (se 2 (by rfl) ⟨2497047, by rfl⟩ : syracuseStep 6658793 = 4994095) B4994095
theorem B22772819 : Blo 1752577 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B3947615 : Blo 1752577 3947615 := bstep (se 1 (by rfl) ⟨2960711, by rfl⟩ : syracuseStep 3947615 = 5921423) B5921423
theorem B1973407 : Blo 1752577 1973407 := bstep (se 1 (by rfl) ⟨1480055, by rfl⟩ : syracuseStep 1973407 = 2960111) B2960111
theorem B3947795 : Blo 1752577 3947795 := bstep (se 1 (by rfl) ⟨2960846, by rfl⟩ : syracuseStep 3947795 = 5921693) B5921693
theorem B1752607 : Blo 1752577 1752607 := bstep (se 1 (by rfl) ⟨1314455, by rfl⟩ : syracuseStep 1752607 = 2628911) B2628911
theorem B2629175 : Blo 1752577 2629175 := bstep (se 1 (by rfl) ⟨1971881, by rfl⟩ : syracuseStep 2629175 = 3943763) B3943763
theorem B1752767 : Blo 1752577 1752767 := bstep (se 1 (by rfl) ⟨1314575, by rfl⟩ : syracuseStep 1752767 = 2629151) B2629151
theorem B10665715 : Blo 1752577 10665715 := bstep (se 1 (by rfl) ⟨7999286, by rfl⟩ : syracuseStep 10665715 = 15998573) B15998573
theorem B1753243 : Blo 1752577 1753243 := bstep (se 1 (by rfl) ⟨1314932, by rfl⟩ : syracuseStep 1753243 = 2629865) B2629865
theorem B1753339 : Blo 1752577 1753339 := bstep (se 1 (by rfl) ⟨1315004, by rfl⟩ : syracuseStep 1753339 = 2630009) B2630009
theorem B2629967 : Blo 1752577 2629967 := bstep (se 1 (by rfl) ⟨1972475, by rfl⟩ : syracuseStep 2629967 = 3944951) B3944951
theorem B2220367 : Blo 1752577 2220367 := bstep (se 1 (by rfl) ⟨1665275, by rfl⟩ : syracuseStep 2220367 = 3330551) B3330551
theorem B1753727 : Blo 1752577 1753727 := bstep (se 1 (by rfl) ⟨1315295, by rfl⟩ : syracuseStep 1753727 = 2630591) B2630591
theorem B14803735 : Blo 1752577 14803735 := bstep (se 1 (by rfl) ⟨11102801, by rfl⟩ : syracuseStep 14803735 = 22205603) B22205603
theorem B1753883 : Blo 1752577 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B1753983 : Blo 1752577 1753983 := bstep (se 1 (by rfl) ⟨1315487, by rfl⟩ : syracuseStep 1753983 = 2630975) B2630975
theorem B14976029 : Blo 1752577 14976029 := bstep (se 3 (by rfl) ⟨2808005, by rfl⟩ : syracuseStep 14976029 = 5616011) B5616011
theorem B1754183 : Blo 1752577 1754183 := bstep (se 1 (by rfl) ⟨1315637, by rfl⟩ : syracuseStep 1754183 = 2631275) B2631275
theorem B2630783 : Blo 1752577 2630783 := bstep (se 1 (by rfl) ⟨1973087, by rfl⟩ : syracuseStep 2630783 = 3946175) B3946175
theorem B2631209 : Blo 1752577 2631209 := bstep (se 2 (by rfl) ⟨986703, by rfl⟩ : syracuseStep 2631209 = 1973407) B1973407
theorem B15190055 : Blo 1752577 15190055 := bstep (se 1 (by rfl) ⟨11392541, by rfl⟩ : syracuseStep 15190055 = 22785083) B22785083
theorem B15181879 : Blo 1752577 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B2631743 : Blo 1752577 2631743 := bstep (se 1 (by rfl) ⟨1973807, by rfl⟩ : syracuseStep 2631743 = 3947615) B3947615
theorem B10127443 : Blo 1752577 10127443 := bstep (se 1 (by rfl) ⟨7595582, by rfl⟩ : syracuseStep 10127443 = 15191165) B15191165
theorem B28428403 : Blo 1752577 28428403 := bstep (se 1 (by rfl) ⟨21321302, by rfl⟩ : syracuseStep 28428403 = 42642605) B42642605
theorem B2631863 : Blo 1752577 2631863 := bstep (se 1 (by rfl) ⟨1973897, by rfl⟩ : syracuseStep 2631863 = 3947795) B3947795
theorem B21334681 : Blo 1752577 21334681 := bstep (se 2 (by rfl) ⟨8000505, by rfl⟩ : syracuseStep 21334681 = 16001011) B16001011
theorem B3746665 : Blo 1752577 3746665 := bstep (se 2 (by rfl) ⟨1404999, by rfl⟩ : syracuseStep 3746665 = 2809999) B2809999
theorem B17992691 : Blo 1752577 17992691 := bstep (se 1 (by rfl) ⟨13494518, by rfl⟩ : syracuseStep 17992691 = 26989037) B26989037
theorem B25275401 : Blo 1752577 25275401 := bstep (se 2 (by rfl) ⟨9478275, by rfl⟩ : syracuseStep 25275401 = 18956551) B18956551
theorem B8424479 : Blo 1752577 8424479 := bstep (se 1 (by rfl) ⟨6318359, by rfl⟩ : syracuseStep 8424479 = 12636719) B12636719
theorem B7490681 : Blo 1752577 7490681 := bstep (se 2 (by rfl) ⟨2809005, by rfl⟩ : syracuseStep 7490681 = 5618011) B5618011
theorem B3943655 : Blo 1752577 3943655 := bstep (se 1 (by rfl) ⟨2957741, by rfl⟩ : syracuseStep 3943655 = 5915483) B5915483
theorem B255888841 : Blo 1752577 255888841 := bstep (se 2 (by rfl) ⟨95958315, by rfl⟩ : syracuseStep 255888841 = 191916631) B191916631
theorem B56905193 : Blo 1752577 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B12643867 : Blo 1752577 12643867 := bstep (se 1 (by rfl) ⟨9482900, by rfl⟩ : syracuseStep 12643867 = 18965801) B18965801
theorem B3944015 : Blo 1752577 3944015 := bstep (se 1 (by rfl) ⟨2958011, by rfl⟩ : syracuseStep 3944015 = 5916023) B5916023
theorem B3944105 : Blo 1752577 3944105 := bstep (se 2 (by rfl) ⟨1479039, by rfl⟩ : syracuseStep 3944105 = 2958079) B2958079
theorem B3944159 : Blo 1752577 3944159 := bstep (se 1 (by rfl) ⟨2958119, by rfl⟩ : syracuseStep 3944159 = 5916239) B5916239
theorem B6164639 : Blo 1752577 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B40473017 : Blo 1752577 40473017 := bstep (se 2 (by rfl) ⟨15177381, by rfl⟩ : syracuseStep 40473017 = 30354763) B30354763
theorem B3945185 : Blo 1752577 3945185 := bstep (se 2 (by rfl) ⟨1479444, by rfl⟩ : syracuseStep 3945185 = 2958889) B2958889
theorem B3946121 : Blo 1752577 3946121 := bstep (se 2 (by rfl) ⟨1479795, by rfl⟩ : syracuseStep 3946121 = 2959591) B2959591
theorem B1972219 : Blo 1752577 1972219 := bstep (se 1 (by rfl) ⟨1479164, by rfl⟩ : syracuseStep 1972219 = 2958329) B2958329
theorem B9484285 : Blo 1752577 9484285 := bstep (se 3 (by rfl) ⟨1778303, by rfl⟩ : syracuseStep 9484285 = 3556607) B3556607
theorem B4741193 : Blo 1752577 4741193 := bstep (se 2 (by rfl) ⟨1777947, by rfl⟩ : syracuseStep 4741193 = 3555895) B3555895
theorem B3946607 : Blo 1752577 3946607 := bstep (se 1 (by rfl) ⟨2959955, by rfl⟩ : syracuseStep 3946607 = 5919911) B5919911
theorem B19970225 : Blo 1752577 19970225 := bstep (se 2 (by rfl) ⟨7488834, by rfl⟩ : syracuseStep 19970225 = 14977669) B14977669
theorem B3946715 : Blo 1752577 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B7592399 : Blo 1752577 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B7494439 : Blo 1752577 7494439 := bstep (se 1 (by rfl) ⟨5620829, by rfl⟩ : syracuseStep 7494439 = 11241659) B11241659
theorem B35994557 : Blo 1752577 35994557 := bstep (se 3 (by rfl) ⟨6748979, by rfl⟩ : syracuseStep 35994557 = 13497959) B13497959
theorem B1973191 : Blo 1752577 1973191 := bstep (se 1 (by rfl) ⟨1479893, by rfl⟩ : syracuseStep 1973191 = 2959787) B2959787
theorem B4439195 : Blo 1752577 4439195 := bstep (se 1 (by rfl) ⟨3329396, by rfl⟩ : syracuseStep 4439195 = 6658793) B6658793
theorem B35994881 : Blo 1752577 35994881 := bstep (se 2 (by rfl) ⟨13498080, by rfl⟩ : syracuseStep 35994881 = 26996161) B26996161
theorem B27008423 : Blo 1752577 27008423 := bstep (se 1 (by rfl) ⟨20256317, by rfl⟩ : syracuseStep 27008423 = 40512635) B40512635
theorem B2629055 : Blo 1752577 2629055 := bstep (se 1 (by rfl) ⟨1971791, by rfl⟩ : syracuseStep 2629055 = 3943583) B3943583
theorem B14220953 : Blo 1752577 14220953 := bstep (se 2 (by rfl) ⟨5332857, by rfl⟩ : syracuseStep 14220953 = 10665715) B10665715
theorem B1752783 : Blo 1752577 1752783 := bstep (se 1 (by rfl) ⟨1314587, by rfl⟩ : syracuseStep 1752783 = 2629175) B2629175
theorem B9986003 : Blo 1752577 9986003 := bstep (se 1 (by rfl) ⟨7489502, by rfl⟩ : syracuseStep 9986003 = 14979005) B14979005
theorem B20242505 : Blo 1752577 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B37904537 : Blo 1752577 37904537 := bstep (se 2 (by rfl) ⟨14214201, by rfl⟩ : syracuseStep 37904537 = 28428403) B28428403
theorem B1753311 : Blo 1752577 1753311 := bstep (se 1 (by rfl) ⟨1314983, by rfl⟩ : syracuseStep 1753311 = 2629967) B2629967
theorem B2630123 : Blo 1752577 2630123 := bstep (se 1 (by rfl) ⟨1972592, by rfl⟩ : syracuseStep 2630123 = 3945185) B3945185
theorem B1753855 : Blo 1752577 1753855 := bstep (se 1 (by rfl) ⟨1315391, by rfl⟩ : syracuseStep 1753855 = 2630783) B2630783
theorem B1754139 : Blo 1752577 1754139 := bstep (se 1 (by rfl) ⟨1315604, by rfl⟩ : syracuseStep 1754139 = 2631209) B2631209
theorem B2630747 : Blo 1752577 2630747 := bstep (se 1 (by rfl) ⟨1973060, by rfl⟩ : syracuseStep 2630747 = 3946121) B3946121
theorem B2630921 : Blo 1752577 2630921 := bstep (se 2 (by rfl) ⟨986595, by rfl⟩ : syracuseStep 2630921 = 1973191) B1973191
theorem B10126703 : Blo 1752577 10126703 := bstep (se 1 (by rfl) ⟨7595027, by rfl⟩ : syracuseStep 10126703 = 15190055) B15190055
theorem B1754495 : Blo 1752577 1754495 := bstep (se 1 (by rfl) ⟨1315871, by rfl⟩ : syracuseStep 1754495 = 2631743) B2631743
theorem B2631071 : Blo 1752577 2631071 := bstep (se 1 (by rfl) ⟨1973303, by rfl⟩ : syracuseStep 2631071 = 3946607) B3946607
theorem B13313483 : Blo 1752577 13313483 := bstep (se 1 (by rfl) ⟨9985112, by rfl⟩ : syracuseStep 13313483 = 19970225) B19970225
theorem B1754575 : Blo 1752577 1754575 := bstep (se 1 (by rfl) ⟨1315931, by rfl⟩ : syracuseStep 1754575 = 2631863) B2631863
theorem B2631143 : Blo 1752577 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B11995127 : Blo 1752577 11995127 := bstep (se 1 (by rfl) ⟨8996345, by rfl⟩ : syracuseStep 11995127 = 17992691) B17992691
theorem B2959463 : Blo 1752577 2959463 := bstep (se 1 (by rfl) ⟨2219597, by rfl⟩ : syracuseStep 2959463 = 4439195) B4439195
theorem B23996587 : Blo 1752577 23996587 := bstep (se 1 (by rfl) ⟨17997440, by rfl⟩ : syracuseStep 23996587 = 35994881) B35994881
theorem B9480635 : Blo 1752577 9480635 := bstep (se 1 (by rfl) ⟨7110476, by rfl⟩ : syracuseStep 9480635 = 14220953) B14220953
theorem B13503257 : Blo 1752577 13503257 := bstep (se 2 (by rfl) ⟨5063721, by rfl⟩ : syracuseStep 13503257 = 10127443) B10127443
theorem B2960489 : Blo 1752577 2960489 := bstep (se 2 (by rfl) ⟨1110183, by rfl⟩ : syracuseStep 2960489 = 2220367) B2220367
theorem B28446241 : Blo 1752577 28446241 := bstep (se 2 (by rfl) ⟨10667340, by rfl⟩ : syracuseStep 28446241 = 21334681) B21334681
theorem B19738313 : Blo 1752577 19738313 := bstep (se 2 (by rfl) ⟨7401867, by rfl⟩ : syracuseStep 19738313 = 14803735) B14803735
theorem B341185121 : Blo 1752577 341185121 := bstep (se 2 (by rfl) ⟨127944420, by rfl⟩ : syracuseStep 341185121 = 255888841) B255888841
theorem B5616319 : Blo 1752577 5616319 := bstep (se 1 (by rfl) ⟨4212239, by rfl⟩ : syracuseStep 5616319 = 8424479) B8424479
theorem B4993787 : Blo 1752577 4993787 := bstep (se 1 (by rfl) ⟨3745340, by rfl⟩ : syracuseStep 4993787 = 7490681) B7490681
theorem B6657335 : Blo 1752577 6657335 := bstep (se 1 (by rfl) ⟨4993001, by rfl⟩ : syracuseStep 6657335 = 9986003) B9986003
theorem B12645713 : Blo 1752577 12645713 := bstep (se 2 (by rfl) ⟨4742142, by rfl⟩ : syracuseStep 12645713 = 9484285) B9484285
theorem B4109759 : Blo 1752577 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B67433957 : Blo 1752577 67433957 := bstep (se 4 (by rfl) ⟨6321933, by rfl⟩ : syracuseStep 67433957 = 12643867) B12643867
theorem B26982011 : Blo 1752577 26982011 := bstep (se 1 (by rfl) ⟨20236508, by rfl⟩ : syracuseStep 26982011 = 40473017) B40473017
theorem B9984019 : Blo 1752577 9984019 := bstep (se 1 (by rfl) ⟨7488014, by rfl⟩ : syracuseStep 9984019 = 14976029) B14976029
theorem B9992585 : Blo 1752577 9992585 := bstep (se 2 (by rfl) ⟨3747219, by rfl⟩ : syracuseStep 9992585 = 7494439) B7494439
theorem B4995553 : Blo 1752577 4995553 := bstep (se 2 (by rfl) ⟨1873332, by rfl⟩ : syracuseStep 4995553 = 3746665) B3746665
theorem B3160795 : Blo 1752577 3160795 := bstep (se 1 (by rfl) ⟨2370596, by rfl⟩ : syracuseStep 3160795 = 4741193) B4741193
theorem B5061599 : Blo 1752577 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B16850267 : Blo 1752577 16850267 := bstep (se 1 (by rfl) ⟨12637700, by rfl⟩ : syracuseStep 16850267 = 25275401) B25275401
theorem B2629103 : Blo 1752577 2629103 := bstep (se 1 (by rfl) ⟨1971827, by rfl⟩ : syracuseStep 2629103 = 3943655) B3943655
theorem B18005615 : Blo 1752577 18005615 := bstep (se 1 (by rfl) ⟨13504211, by rfl⟩ : syracuseStep 18005615 = 27008423) B27008423
theorem B1752703 : Blo 1752577 1752703 := bstep (se 1 (by rfl) ⟨1314527, by rfl⟩ : syracuseStep 1752703 = 2629055) B2629055
theorem B37936795 : Blo 1752577 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B2629343 : Blo 1752577 2629343 := bstep (se 1 (by rfl) ⟨1972007, by rfl⟩ : syracuseStep 2629343 = 3944015) B3944015
theorem B2629403 : Blo 1752577 2629403 := bstep (se 1 (by rfl) ⟨1972052, by rfl⟩ : syracuseStep 2629403 = 3944105) B3944105
theorem B2629439 : Blo 1752577 2629439 := bstep (se 1 (by rfl) ⟨1972079, by rfl⟩ : syracuseStep 2629439 = 3944159) B3944159
theorem B95985485 : Blo 1752577 95985485 := bstep (se 3 (by rfl) ⟨17997278, by rfl⟩ : syracuseStep 95985485 = 35994557) B35994557
theorem B2629625 : Blo 1752577 2629625 := bstep (se 2 (by rfl) ⟨986109, by rfl⟩ : syracuseStep 2629625 = 1972219) B1972219
theorem B13312025 : Blo 1752577 13312025 := bstep (se 2 (by rfl) ⟨4992009, by rfl⟩ : syracuseStep 13312025 = 9984019) B9984019
theorem B1753415 : Blo 1752577 1753415 := bstep (se 1 (by rfl) ⟨1315061, by rfl⟩ : syracuseStep 1753415 = 2630123) B2630123
theorem B6660737 : Blo 1752577 6660737 := bstep (se 2 (by rfl) ⟨2497776, by rfl⟩ : syracuseStep 6660737 = 4995553) B4995553
theorem B1753831 : Blo 1752577 1753831 := bstep (se 1 (by rfl) ⟨1315373, by rfl⟩ : syracuseStep 1753831 = 2630747) B2630747
theorem B1753947 : Blo 1752577 1753947 := bstep (se 1 (by rfl) ⟨1315460, by rfl⟩ : syracuseStep 1753947 = 2630921) B2630921
theorem B8430475 : Blo 1752577 8430475 := bstep (se 1 (by rfl) ⟨6322856, by rfl⟩ : syracuseStep 8430475 = 12645713) B12645713
theorem B6751135 : Blo 1752577 6751135 := bstep (se 1 (by rfl) ⟨5063351, by rfl⟩ : syracuseStep 6751135 = 10126703) B10126703
theorem B7488425 : Blo 1752577 7488425 := bstep (se 2 (by rfl) ⟨2808159, by rfl⟩ : syracuseStep 7488425 = 5616319) B5616319
theorem B1754047 : Blo 1752577 1754047 := bstep (se 1 (by rfl) ⟨1315535, by rfl⟩ : syracuseStep 1754047 = 2631071) B2631071
theorem B1754095 : Blo 1752577 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B7996751 : Blo 1752577 7996751 := bstep (se 1 (by rfl) ⟨5997563, by rfl⟩ : syracuseStep 7996751 = 11995127) B11995127
theorem B6661723 : Blo 1752577 6661723 := bstep (se 1 (by rfl) ⟨4996292, by rfl⟩ : syracuseStep 6661723 = 9992585) B9992585
theorem B11233511 : Blo 1752577 11233511 := bstep (se 1 (by rfl) ⟨8425133, by rfl⟩ : syracuseStep 11233511 = 16850267) B16850267
theorem B12003743 : Blo 1752577 12003743 := bstep (se 1 (by rfl) ⟨9002807, by rfl⟩ : syracuseStep 12003743 = 18005615) B18005615
theorem B13158875 : Blo 1752577 13158875 := bstep (se 1 (by rfl) ⟨9869156, by rfl⟩ : syracuseStep 13158875 = 19738313) B19738313
theorem B63990323 : Blo 1752577 63990323 := bstep (se 1 (by rfl) ⟨47992742, by rfl⟩ : syracuseStep 63990323 = 95985485) B95985485
theorem B53980013 : Blo 1752577 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B3329191 : Blo 1752577 3329191 := bstep (se 1 (by rfl) ⟨2496893, by rfl⟩ : syracuseStep 3329191 = 4993787) B4993787
theorem B4214393 : Blo 1752577 4214393 := bstep (se 2 (by rfl) ⟨1580397, by rfl⟩ : syracuseStep 4214393 = 3160795) B3160795
theorem B2739839 : Blo 1752577 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B8875655 : Blo 1752577 8875655 := bstep (se 1 (by rfl) ⟨6656741, by rfl⟩ : syracuseStep 8875655 = 13313483) B13313483
theorem B6320423 : Blo 1752577 6320423 := bstep (se 1 (by rfl) ⟨4740317, by rfl⟩ : syracuseStep 6320423 = 9480635) B9480635
theorem B50582393 : Blo 1752577 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B25269691 : Blo 1752577 25269691 := bstep (se 1 (by rfl) ⟨18952268, by rfl⟩ : syracuseStep 25269691 = 37904537) B37904537
theorem B31995449 : Blo 1752577 31995449 := bstep (se 2 (by rfl) ⟨11998293, by rfl⟩ : syracuseStep 31995449 = 23996587) B23996587
theorem B227456747 : Blo 1752577 227456747 := bstep (se 1 (by rfl) ⟨170592560, by rfl⟩ : syracuseStep 227456747 = 341185121) B341185121
theorem B4438223 : Blo 1752577 4438223 := bstep (se 1 (by rfl) ⟨3328667, by rfl⟩ : syracuseStep 4438223 = 6657335) B6657335
theorem B44955971 : Blo 1752577 44955971 := bstep (se 1 (by rfl) ⟨33716978, by rfl⟩ : syracuseStep 44955971 = 67433957) B67433957
theorem B17988007 : Blo 1752577 17988007 := bstep (se 1 (by rfl) ⟨13491005, by rfl⟩ : syracuseStep 17988007 = 26982011) B26982011
theorem B1972975 : Blo 1752577 1972975 := bstep (se 1 (by rfl) ⟨1479731, by rfl⟩ : syracuseStep 1972975 = 2959463) B2959463
theorem B9002171 : Blo 1752577 9002171 := bstep (se 1 (by rfl) ⟨6751628, by rfl⟩ : syracuseStep 9002171 = 13503257) B13503257
theorem B3374399 : Blo 1752577 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B37928321 : Blo 1752577 37928321 := bstep (se 2 (by rfl) ⟨14223120, by rfl⟩ : syracuseStep 37928321 = 28446241) B28446241
theorem B1973659 : Blo 1752577 1973659 := bstep (se 1 (by rfl) ⟨1480244, by rfl⟩ : syracuseStep 1973659 = 2960489) B2960489
theorem B1752735 : Blo 1752577 1752735 := bstep (se 1 (by rfl) ⟨1314551, by rfl⟩ : syracuseStep 1752735 = 2629103) B2629103
theorem B1752895 : Blo 1752577 1752895 := bstep (se 1 (by rfl) ⟨1314671, by rfl⟩ : syracuseStep 1752895 = 2629343) B2629343
theorem B1752935 : Blo 1752577 1752935 := bstep (se 1 (by rfl) ⟨1314701, by rfl⟩ : syracuseStep 1752935 = 2629403) B2629403
theorem B1752959 : Blo 1752577 1752959 := bstep (se 1 (by rfl) ⟨1314719, by rfl⟩ : syracuseStep 1752959 = 2629439) B2629439
theorem B1753083 : Blo 1752577 1753083 := bstep (se 1 (by rfl) ⟨1314812, by rfl⟩ : syracuseStep 1753083 = 2629625) B2629625
theorem B4440491 : Blo 1752577 4440491 := bstep (se 1 (by rfl) ⟨3330368, by rfl⟩ : syracuseStep 4440491 = 6660737) B6660737
theorem B2630633 : Blo 1752577 2630633 := bstep (se 2 (by rfl) ⟨986487, by rfl⟩ : syracuseStep 2630633 = 1972975) B1972975
theorem B11240633 : Blo 1752577 11240633 := bstep (se 2 (by rfl) ⟨4215237, by rfl⟩ : syracuseStep 11240633 = 8430475) B8430475
theorem B2958815 : Blo 1752577 2958815 := bstep (se 1 (by rfl) ⟨2219111, by rfl⟩ : syracuseStep 2958815 = 4438223) B4438223
theorem B7489007 : Blo 1752577 7489007 := bstep (se 1 (by rfl) ⟨5616755, by rfl⟩ : syracuseStep 7489007 = 11233511) B11233511
theorem B2631545 : Blo 1752577 2631545 := bstep (se 2 (by rfl) ⟨986829, by rfl⟩ : syracuseStep 2631545 = 1973659) B1973659
theorem B8882297 : Blo 1752577 8882297 := bstep (se 2 (by rfl) ⟨3330861, by rfl⟩ : syracuseStep 8882297 = 6661723) B6661723
theorem B5917103 : Blo 1752577 5917103 := bstep (se 1 (by rfl) ⟨4437827, by rfl⟩ : syracuseStep 5917103 = 8875655) B8875655
theorem B8874683 : Blo 1752577 8874683 := bstep (se 1 (by rfl) ⟨6656012, by rfl⟩ : syracuseStep 8874683 = 13312025) B13312025
theorem B4213615 : Blo 1752577 4213615 := bstep (se 1 (by rfl) ⟨3160211, by rfl⟩ : syracuseStep 4213615 = 6320423) B6320423
theorem B33721595 : Blo 1752577 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B4992283 : Blo 1752577 4992283 := bstep (se 1 (by rfl) ⟨3744212, by rfl⟩ : syracuseStep 4992283 = 7488425) B7488425
theorem B8998397 : Blo 1752577 8998397 := bstep (se 3 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 8998397 = 3374399) B3374399
theorem B151637831 : Blo 1752577 151637831 := bstep (se 1 (by rfl) ⟨113728373, by rfl⟩ : syracuseStep 151637831 = 227456747) B227456747
theorem B29970647 : Blo 1752577 29970647 := bstep (se 1 (by rfl) ⟨22477985, by rfl⟩ : syracuseStep 29970647 = 44955971) B44955971
theorem B42660215 : Blo 1752577 42660215 := bstep (se 1 (by rfl) ⟨31995161, by rfl⟩ : syracuseStep 42660215 = 63990323) B63990323
theorem B6001447 : Blo 1752577 6001447 := bstep (se 1 (by rfl) ⟨4501085, by rfl⟩ : syracuseStep 6001447 = 9002171) B9002171
theorem B25285547 : Blo 1752577 25285547 := bstep (se 1 (by rfl) ⟨18964160, by rfl⟩ : syracuseStep 25285547 = 37928321) B37928321
theorem B23984009 : Blo 1752577 23984009 := bstep (se 2 (by rfl) ⟨8994003, by rfl⟩ : syracuseStep 23984009 = 17988007) B17988007
theorem B5331167 : Blo 1752577 5331167 := bstep (se 1 (by rfl) ⟨3998375, by rfl⟩ : syracuseStep 5331167 = 7996751) B7996751
theorem B21330299 : Blo 1752577 21330299 := bstep (se 1 (by rfl) ⟨15997724, by rfl⟩ : syracuseStep 21330299 = 31995449) B31995449
theorem B9001513 : Blo 1752577 9001513 := bstep (se 2 (by rfl) ⟨3375567, by rfl⟩ : syracuseStep 9001513 = 6751135) B6751135
theorem B4438921 : Blo 1752577 4438921 := bstep (se 2 (by rfl) ⟨1664595, by rfl⟩ : syracuseStep 4438921 = 3329191) B3329191
theorem B8002495 : Blo 1752577 8002495 := bstep (se 1 (by rfl) ⟨6001871, by rfl⟩ : syracuseStep 8002495 = 12003743) B12003743
theorem B8772583 : Blo 1752577 8772583 := bstep (se 1 (by rfl) ⟨6579437, by rfl⟩ : syracuseStep 8772583 = 13158875) B13158875
theorem B7306237 : Blo 1752577 7306237 := bstep (se 3 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 7306237 = 2739839) B2739839
theorem B35986675 : Blo 1752577 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B33692921 : Blo 1752577 33692921 := bstep (se 2 (by rfl) ⟨12634845, by rfl⟩ : syracuseStep 33692921 = 25269691) B25269691
theorem B2809595 : Blo 1752577 2809595 := bstep (se 1 (by rfl) ⟨2107196, by rfl⟩ : syracuseStep 2809595 = 4214393) B4214393
theorem B19980431 : Blo 1752577 19980431 := bstep (se 1 (by rfl) ⟨14985323, by rfl⟩ : syracuseStep 19980431 = 29970647) B29970647
theorem B29975021 : Blo 1752577 29975021 := bstep (se 3 (by rfl) ⟨5620316, by rfl⟩ : syracuseStep 29975021 = 11240633) B11240633
theorem B1753755 : Blo 1752577 1753755 := bstep (se 1 (by rfl) ⟨1315316, by rfl⟩ : syracuseStep 1753755 = 2630633) B2630633
theorem B12002017 : Blo 1752577 12002017 := bstep (se 2 (by rfl) ⟨4500756, by rfl⟩ : syracuseStep 12002017 = 9001513) B9001513
theorem B1754363 : Blo 1752577 1754363 := bstep (se 1 (by rfl) ⟨1315772, by rfl⟩ : syracuseStep 1754363 = 2631545) B2631545
theorem B9741649 : Blo 1752577 9741649 := bstep (se 2 (by rfl) ⟨3653118, by rfl⟩ : syracuseStep 9741649 = 7306237) B7306237
theorem B47982233 : Blo 1752577 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B5916455 : Blo 1752577 5916455 := bstep (se 1 (by rfl) ⟨4437341, by rfl⟩ : syracuseStep 5916455 = 8874683) B8874683
theorem B22481063 : Blo 1752577 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B5998931 : Blo 1752577 5998931 := bstep (se 1 (by rfl) ⟨4499198, by rfl⟩ : syracuseStep 5998931 = 8998397) B8998397
theorem B101091887 : Blo 1752577 101091887 := bstep (se 1 (by rfl) ⟨75818915, by rfl⟩ : syracuseStep 101091887 = 151637831) B151637831
theorem B2960327 : Blo 1752577 2960327 := bstep (se 1 (by rfl) ⟨2220245, by rfl⟩ : syracuseStep 2960327 = 4440491) B4440491
theorem B4992671 : Blo 1752577 4992671 := bstep (se 1 (by rfl) ⟨3744503, by rfl⟩ : syracuseStep 4992671 = 7489007) B7489007
theorem B5918561 : Blo 1752577 5918561 := bstep (se 2 (by rfl) ⟨2219460, by rfl⟩ : syracuseStep 5918561 = 4438921) B4438921
theorem B3944735 : Blo 1752577 3944735 := bstep (se 1 (by rfl) ⟨2958551, by rfl⟩ : syracuseStep 3944735 = 5917103) B5917103
theorem B6656377 : Blo 1752577 6656377 := bstep (se 2 (by rfl) ⟨2496141, by rfl⟩ : syracuseStep 6656377 = 4992283) B4992283
theorem B1873063 : Blo 1752577 1873063 := bstep (se 1 (by rfl) ⟨1404797, by rfl⟩ : syracuseStep 1873063 = 2809595) B2809595
theorem B28440143 : Blo 1752577 28440143 := bstep (se 1 (by rfl) ⟨21330107, by rfl⟩ : syracuseStep 28440143 = 42660215) B42660215
theorem B16857031 : Blo 1752577 16857031 := bstep (se 1 (by rfl) ⟨12642773, by rfl⟩ : syracuseStep 16857031 = 25285547) B25285547
theorem B1972543 : Blo 1752577 1972543 := bstep (se 1 (by rfl) ⟨1479407, by rfl⟩ : syracuseStep 1972543 = 2958815) B2958815
theorem B8001929 : Blo 1752577 8001929 := bstep (se 2 (by rfl) ⟨3000723, by rfl⟩ : syracuseStep 8001929 = 6001447) B6001447
theorem B5618153 : Blo 1752577 5618153 := bstep (se 2 (by rfl) ⟨2106807, by rfl⟩ : syracuseStep 5618153 = 4213615) B4213615
theorem B15989339 : Blo 1752577 15989339 := bstep (se 1 (by rfl) ⟨11992004, by rfl⟩ : syracuseStep 15989339 = 23984009) B23984009
theorem B11696777 : Blo 1752577 11696777 := bstep (se 2 (by rfl) ⟨4386291, by rfl⟩ : syracuseStep 11696777 = 8772583) B8772583
theorem B5921531 : Blo 1752577 5921531 := bstep (se 1 (by rfl) ⟨4441148, by rfl⟩ : syracuseStep 5921531 = 8882297) B8882297
theorem B3554111 : Blo 1752577 3554111 := bstep (se 1 (by rfl) ⟨2665583, by rfl⟩ : syracuseStep 3554111 = 5331167) B5331167
theorem B14220199 : Blo 1752577 14220199 := bstep (se 1 (by rfl) ⟨10665149, by rfl⟩ : syracuseStep 14220199 = 21330299) B21330299
theorem B22461947 : Blo 1752577 22461947 := bstep (se 1 (by rfl) ⟨16846460, by rfl⟩ : syracuseStep 22461947 = 33692921) B33692921
theorem B42679973 : Blo 1752577 42679973 := bstep (se 4 (by rfl) ⟨4001247, by rfl⟩ : syracuseStep 42679973 = 8002495) B8002495
theorem B13320287 : Blo 1752577 13320287 := bstep (se 1 (by rfl) ⟨9990215, by rfl⟩ : syracuseStep 13320287 = 19980431) B19980431
theorem B2629823 : Blo 1752577 2629823 := bstep (se 1 (by rfl) ⟨1972367, by rfl⟩ : syracuseStep 2629823 = 3944735) B3944735
theorem B2630057 : Blo 1752577 2630057 := bstep (se 2 (by rfl) ⟨986271, by rfl⟩ : syracuseStep 2630057 = 1972543) B1972543
theorem B3999287 : Blo 1752577 3999287 := bstep (se 1 (by rfl) ⟨2999465, by rfl⟩ : syracuseStep 3999287 = 5998931) B5998931
theorem B3745435 : Blo 1752577 3745435 := bstep (se 1 (by rfl) ⟨2809076, by rfl⟩ : syracuseStep 3745435 = 5618153) B5618153
theorem B10659559 : Blo 1752577 10659559 := bstep (se 1 (by rfl) ⟨7994669, by rfl⟩ : syracuseStep 10659559 = 15989339) B15989339
theorem B127952621 : Blo 1752577 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B2369407 : Blo 1752577 2369407 := bstep (se 1 (by rfl) ⟨1777055, by rfl⟩ : syracuseStep 2369407 = 3554111) B3554111
theorem B3328447 : Blo 1752577 3328447 := bstep (se 1 (by rfl) ⟨2496335, by rfl⟩ : syracuseStep 3328447 = 4992671) B4992671
theorem B28453315 : Blo 1752577 28453315 := bstep (se 1 (by rfl) ⟨21339986, by rfl⟩ : syracuseStep 28453315 = 42679973) B42679973
theorem B19983347 : Blo 1752577 19983347 := bstep (se 1 (by rfl) ⟨14987510, by rfl⟩ : syracuseStep 19983347 = 29975021) B29975021
theorem B8875169 : Blo 1752577 8875169 := bstep (se 2 (by rfl) ⟨3328188, by rfl⟩ : syracuseStep 8875169 = 6656377) B6656377
theorem B9989669 : Blo 1752577 9989669 := bstep (se 4 (by rfl) ⟨936531, by rfl⟩ : syracuseStep 9989669 = 1873063) B1873063
theorem B16002689 : Blo 1752577 16002689 := bstep (se 2 (by rfl) ⟨6001008, by rfl⟩ : syracuseStep 16002689 = 12002017) B12002017
theorem B18960095 : Blo 1752577 18960095 := bstep (se 1 (by rfl) ⟨14220071, by rfl⟩ : syracuseStep 18960095 = 28440143) B28440143
theorem B3944303 : Blo 1752577 3944303 := bstep (se 1 (by rfl) ⟨2958227, by rfl⟩ : syracuseStep 3944303 = 5916455) B5916455
theorem B18960265 : Blo 1752577 18960265 := bstep (se 2 (by rfl) ⟨7110099, by rfl⟩ : syracuseStep 18960265 = 14220199) B14220199
theorem B14987375 : Blo 1752577 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B12988865 : Blo 1752577 12988865 := bstep (se 2 (by rfl) ⟨4870824, by rfl⟩ : syracuseStep 12988865 = 9741649) B9741649
theorem B3945707 : Blo 1752577 3945707 := bstep (se 1 (by rfl) ⟨2959280, by rfl⟩ : syracuseStep 3945707 = 5918561) B5918561
theorem B22476041 : Blo 1752577 22476041 := bstep (se 2 (by rfl) ⟨8428515, by rfl⟩ : syracuseStep 22476041 = 16857031) B16857031
theorem B21338477 : Blo 1752577 21338477 := bstep (se 3 (by rfl) ⟨4000964, by rfl⟩ : syracuseStep 21338477 = 8001929) B8001929
theorem B67394591 : Blo 1752577 67394591 := bstep (se 1 (by rfl) ⟨50545943, by rfl⟩ : syracuseStep 67394591 = 101091887) B101091887
theorem B7797851 : Blo 1752577 7797851 := bstep (se 1 (by rfl) ⟨5848388, by rfl⟩ : syracuseStep 7797851 = 11696777) B11696777
theorem B3947687 : Blo 1752577 3947687 := bstep (se 1 (by rfl) ⟨2960765, by rfl⟩ : syracuseStep 3947687 = 5921531) B5921531
theorem B1973551 : Blo 1752577 1973551 := bstep (se 1 (by rfl) ⟨1480163, by rfl⟩ : syracuseStep 1973551 = 2960327) B2960327
theorem B14974631 : Blo 1752577 14974631 := bstep (se 1 (by rfl) ⟨11230973, by rfl⟩ : syracuseStep 14974631 = 22461947) B22461947
theorem B8880191 : Blo 1752577 8880191 := bstep (se 1 (by rfl) ⟨6660143, by rfl⟩ : syracuseStep 8880191 = 13320287) B13320287
theorem B1753215 : Blo 1752577 1753215 := bstep (se 1 (by rfl) ⟨1314911, by rfl⟩ : syracuseStep 1753215 = 2629823) B2629823
theorem B1753371 : Blo 1752577 1753371 := bstep (se 1 (by rfl) ⟨1315028, by rfl⟩ : syracuseStep 1753371 = 2630057) B2630057
theorem B8659243 : Blo 1752577 8659243 := bstep (se 1 (by rfl) ⟨6494432, by rfl⟩ : syracuseStep 8659243 = 12988865) B12988865
theorem B37937753 : Blo 1752577 37937753 := bstep (se 2 (by rfl) ⟨14226657, by rfl⟩ : syracuseStep 37937753 = 28453315) B28453315
theorem B2630471 : Blo 1752577 2630471 := bstep (se 1 (by rfl) ⟨1972853, by rfl⟩ : syracuseStep 2630471 = 3945707) B3945707
theorem B14984027 : Blo 1752577 14984027 := bstep (se 1 (by rfl) ⟨11238020, by rfl⟩ : syracuseStep 14984027 = 22476041) B22476041
theorem B42673837 : Blo 1752577 42673837 := bstep (se 3 (by rfl) ⟨8001344, by rfl⟩ : syracuseStep 42673837 = 16002689) B16002689
theorem B2631401 : Blo 1752577 2631401 := bstep (se 2 (by rfl) ⟨986775, by rfl⟩ : syracuseStep 2631401 = 1973551) B1973551
theorem B13322231 : Blo 1752577 13322231 := bstep (se 1 (by rfl) ⟨9991673, by rfl⟩ : syracuseStep 13322231 = 19983347) B19983347
theorem B5916779 : Blo 1752577 5916779 := bstep (se 1 (by rfl) ⟨4437584, by rfl⟩ : syracuseStep 5916779 = 8875169) B8875169
theorem B2631791 : Blo 1752577 2631791 := bstep (se 1 (by rfl) ⟨1973843, by rfl⟩ : syracuseStep 2631791 = 3947687) B3947687
theorem B83177077 : Blo 1752577 83177077 := bstep (se 5 (by rfl) ⟨3898925, by rfl⟩ : syracuseStep 83177077 = 7797851) B7797851
theorem B2666191 : Blo 1752577 2666191 := bstep (se 1 (by rfl) ⟨1999643, by rfl⟩ : syracuseStep 2666191 = 3999287) B3999287
theorem B14225651 : Blo 1752577 14225651 := bstep (se 1 (by rfl) ⟨10669238, by rfl⟩ : syracuseStep 14225651 = 21338477) B21338477
theorem B44929727 : Blo 1752577 44929727 := bstep (se 1 (by rfl) ⟨33697295, by rfl⟩ : syracuseStep 44929727 = 67394591) B67394591
theorem B4993913 : Blo 1752577 4993913 := bstep (se 2 (by rfl) ⟨1872717, by rfl⟩ : syracuseStep 4993913 = 3745435) B3745435
theorem B9983087 : Blo 1752577 9983087 := bstep (se 1 (by rfl) ⟨7487315, by rfl⟩ : syracuseStep 9983087 = 14974631) B14974631
theorem B3159209 : Blo 1752577 3159209 := bstep (se 2 (by rfl) ⟨1184703, by rfl⟩ : syracuseStep 3159209 = 2369407) B2369407
theorem B9991583 : Blo 1752577 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B4437929 : Blo 1752577 4437929 := bstep (se 2 (by rfl) ⟨1664223, by rfl⟩ : syracuseStep 4437929 = 3328447) B3328447
theorem B85301747 : Blo 1752577 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B14212745 : Blo 1752577 14212745 := bstep (se 2 (by rfl) ⟨5329779, by rfl⟩ : syracuseStep 14212745 = 10659559) B10659559
theorem B6659779 : Blo 1752577 6659779 := bstep (se 1 (by rfl) ⟨4994834, by rfl⟩ : syracuseStep 6659779 = 9989669) B9989669
theorem B12640063 : Blo 1752577 12640063 := bstep (se 1 (by rfl) ⟨9480047, by rfl⟩ : syracuseStep 12640063 = 18960095) B18960095
theorem B25280353 : Blo 1752577 25280353 := bstep (se 2 (by rfl) ⟨9480132, by rfl⟩ : syracuseStep 25280353 = 18960265) B18960265
theorem B2629535 : Blo 1752577 2629535 := bstep (se 1 (by rfl) ⟨1972151, by rfl⟩ : syracuseStep 2629535 = 3944303) B3944303
theorem B1753647 : Blo 1752577 1753647 := bstep (se 1 (by rfl) ⟨1315235, by rfl⟩ : syracuseStep 1753647 = 2630471) B2630471
theorem B6661055 : Blo 1752577 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B1754267 : Blo 1752577 1754267 := bstep (se 1 (by rfl) ⟨1315700, by rfl⟩ : syracuseStep 1754267 = 2631401) B2631401
theorem B2958619 : Blo 1752577 2958619 := bstep (se 1 (by rfl) ⟨2218964, by rfl⟩ : syracuseStep 2958619 = 4437929) B4437929
theorem B8881487 : Blo 1752577 8881487 := bstep (se 1 (by rfl) ⟨6661115, by rfl⟩ : syracuseStep 8881487 = 13322231) B13322231
theorem B1754527 : Blo 1752577 1754527 := bstep (se 1 (by rfl) ⟨1315895, by rfl⟩ : syracuseStep 1754527 = 2631791) B2631791
theorem B16853417 : Blo 1752577 16853417 := bstep (se 2 (by rfl) ⟨6320031, by rfl⟩ : syracuseStep 16853417 = 12640063) B12640063
theorem B25291835 : Blo 1752577 25291835 := bstep (se 1 (by rfl) ⟨18968876, by rfl⟩ : syracuseStep 25291835 = 37937753) B37937753
theorem B8424557 : Blo 1752577 8424557 := bstep (se 3 (by rfl) ⟨1579604, by rfl⟩ : syracuseStep 8424557 = 3159209) B3159209
theorem B29953151 : Blo 1752577 29953151 := bstep (se 1 (by rfl) ⟨22464863, by rfl⟩ : syracuseStep 29953151 = 44929727) B44929727
theorem B9989351 : Blo 1752577 9989351 := bstep (se 1 (by rfl) ⟨7492013, by rfl⟩ : syracuseStep 9989351 = 14984027) B14984027
theorem B3329275 : Blo 1752577 3329275 := bstep (se 1 (by rfl) ⟨2496956, by rfl⟩ : syracuseStep 3329275 = 4993913) B4993913
theorem B6655391 : Blo 1752577 6655391 := bstep (se 1 (by rfl) ⟨4991543, by rfl⟩ : syracuseStep 6655391 = 9983087) B9983087
theorem B3944519 : Blo 1752577 3944519 := bstep (se 1 (by rfl) ⟨2958389, by rfl⟩ : syracuseStep 3944519 = 5916779) B5916779
theorem B46182629 : Blo 1752577 46182629 := bstep (se 4 (by rfl) ⟨4329621, by rfl⟩ : syracuseStep 46182629 = 8659243) B8659243
theorem B56898449 : Blo 1752577 56898449 := bstep (se 2 (by rfl) ⟨21336918, by rfl⟩ : syracuseStep 56898449 = 42673837) B42673837
theorem B9475163 : Blo 1752577 9475163 := bstep (se 1 (by rfl) ⟨7106372, by rfl⟩ : syracuseStep 9475163 = 14212745) B14212745
theorem B33707137 : Blo 1752577 33707137 := bstep (se 2 (by rfl) ⟨12640176, by rfl⟩ : syracuseStep 33707137 = 25280353) B25280353
theorem B5920127 : Blo 1752577 5920127 := bstep (se 1 (by rfl) ⟨4440095, by rfl⟩ : syracuseStep 5920127 = 8880191) B8880191
theorem B9483767 : Blo 1752577 9483767 := bstep (se 1 (by rfl) ⟨7112825, by rfl⟩ : syracuseStep 9483767 = 14225651) B14225651
theorem B56867831 : Blo 1752577 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B110902769 : Blo 1752577 110902769 := bstep (se 2 (by rfl) ⟨41588538, by rfl⟩ : syracuseStep 110902769 = 83177077) B83177077
theorem B8879705 : Blo 1752577 8879705 := bstep (se 2 (by rfl) ⟨3329889, by rfl⟩ : syracuseStep 8879705 = 6659779) B6659779
theorem B3554921 : Blo 1752577 3554921 := bstep (se 2 (by rfl) ⟨1333095, by rfl⟩ : syracuseStep 3554921 = 2666191) B2666191
theorem B1753023 : Blo 1752577 1753023 := bstep (se 1 (by rfl) ⟨1314767, by rfl⟩ : syracuseStep 1753023 = 2629535) B2629535
theorem B2629679 : Blo 1752577 2629679 := bstep (se 1 (by rfl) ⟨1972259, by rfl⟩ : syracuseStep 2629679 = 3944519) B3944519
theorem B6316775 : Blo 1752577 6316775 := bstep (se 1 (by rfl) ⟨4737581, by rfl⟩ : syracuseStep 6316775 = 9475163) B9475163
theorem B44942849 : Blo 1752577 44942849 := bstep (se 2 (by rfl) ⟨16853568, by rfl⟩ : syracuseStep 44942849 = 33707137) B33707137
theorem B16861223 : Blo 1752577 16861223 := bstep (se 1 (by rfl) ⟨12645917, by rfl⟩ : syracuseStep 16861223 = 25291835) B25291835
theorem B73935179 : Blo 1752577 73935179 := bstep (se 1 (by rfl) ⟨55451384, by rfl⟩ : syracuseStep 73935179 = 110902769) B110902769
theorem B2369947 : Blo 1752577 2369947 := bstep (se 1 (by rfl) ⟨1777460, by rfl⟩ : syracuseStep 2369947 = 3554921) B3554921
theorem B4440703 : Blo 1752577 4440703 := bstep (se 1 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 4440703 = 6661055) B6661055
theorem B30788419 : Blo 1752577 30788419 := bstep (se 1 (by rfl) ⟨23091314, by rfl⟩ : syracuseStep 30788419 = 46182629) B46182629
theorem B37932299 : Blo 1752577 37932299 := bstep (se 1 (by rfl) ⟨28449224, by rfl⟩ : syracuseStep 37932299 = 56898449) B56898449
theorem B11235611 : Blo 1752577 11235611 := bstep (se 1 (by rfl) ⟨8426708, by rfl⟩ : syracuseStep 11235611 = 16853417) B16853417
theorem B3944825 : Blo 1752577 3944825 := bstep (se 2 (by rfl) ⟨1479309, by rfl⟩ : syracuseStep 3944825 = 2958619) B2958619
theorem B5616371 : Blo 1752577 5616371 := bstep (se 1 (by rfl) ⟨4212278, by rfl⟩ : syracuseStep 5616371 = 8424557) B8424557
theorem B19968767 : Blo 1752577 19968767 := bstep (se 1 (by rfl) ⟨14976575, by rfl⟩ : syracuseStep 19968767 = 29953151) B29953151
theorem B4436927 : Blo 1752577 4436927 := bstep (se 1 (by rfl) ⟨3327695, by rfl⟩ : syracuseStep 4436927 = 6655391) B6655391
theorem B5919803 : Blo 1752577 5919803 := bstep (se 1 (by rfl) ⟨4439852, by rfl⟩ : syracuseStep 5919803 = 8879705) B8879705
theorem B5920991 : Blo 1752577 5920991 := bstep (se 1 (by rfl) ⟨4440743, by rfl⟩ : syracuseStep 5920991 = 8881487) B8881487
theorem B3946751 : Blo 1752577 3946751 := bstep (se 1 (by rfl) ⟨2960063, by rfl⟩ : syracuseStep 3946751 = 5920127) B5920127
theorem B6322511 : Blo 1752577 6322511 := bstep (se 1 (by rfl) ⟨4741883, by rfl⟩ : syracuseStep 6322511 = 9483767) B9483767
theorem B4439033 : Blo 1752577 4439033 := bstep (se 2 (by rfl) ⟨1664637, by rfl⟩ : syracuseStep 4439033 = 3329275) B3329275
theorem B37911887 : Blo 1752577 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B6659567 : Blo 1752577 6659567 := bstep (se 1 (by rfl) ⟨4994675, by rfl⟩ : syracuseStep 6659567 = 9989351) B9989351
theorem B1753119 : Blo 1752577 1753119 := bstep (se 1 (by rfl) ⟨1314839, by rfl⟩ : syracuseStep 1753119 = 2629679) B2629679
theorem B2629883 : Blo 1752577 2629883 := bstep (se 1 (by rfl) ⟨1972412, by rfl⟩ : syracuseStep 2629883 = 3944825) B3944825
theorem B4211183 : Blo 1752577 4211183 := bstep (se 1 (by rfl) ⟨3158387, by rfl⟩ : syracuseStep 4211183 = 6316775) B6316775
theorem B3744247 : Blo 1752577 3744247 := bstep (se 1 (by rfl) ⟨2808185, by rfl⟩ : syracuseStep 3744247 = 5616371) B5616371
theorem B13312511 : Blo 1752577 13312511 := bstep (se 1 (by rfl) ⟨9984383, by rfl⟩ : syracuseStep 13312511 = 19968767) B19968767
theorem B2957951 : Blo 1752577 2957951 := bstep (se 1 (by rfl) ⟨2218463, by rfl⟩ : syracuseStep 2957951 = 4436927) B4436927
theorem B41051225 : Blo 1752577 41051225 := bstep (se 2 (by rfl) ⟨15394209, by rfl⟩ : syracuseStep 41051225 = 30788419) B30788419
theorem B11240815 : Blo 1752577 11240815 := bstep (se 1 (by rfl) ⟨8430611, by rfl⟩ : syracuseStep 11240815 = 16861223) B16861223
theorem B2631167 : Blo 1752577 2631167 := bstep (se 1 (by rfl) ⟨1973375, by rfl⟩ : syracuseStep 2631167 = 3946751) B3946751
theorem B2959355 : Blo 1752577 2959355 := bstep (se 1 (by rfl) ⟨2219516, by rfl⟩ : syracuseStep 2959355 = 4439033) B4439033
theorem B25274591 : Blo 1752577 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B7490407 : Blo 1752577 7490407 := bstep (se 1 (by rfl) ⟨5617805, by rfl⟩ : syracuseStep 7490407 = 11235611) B11235611
theorem B29961899 : Blo 1752577 29961899 := bstep (se 1 (by rfl) ⟨22471424, by rfl⟩ : syracuseStep 29961899 = 44942849) B44942849
theorem B4215007 : Blo 1752577 4215007 := bstep (se 1 (by rfl) ⟨3161255, by rfl⟩ : syracuseStep 4215007 = 6322511) B6322511
theorem B3159929 : Blo 1752577 3159929 := bstep (se 2 (by rfl) ⟨1184973, by rfl⟩ : syracuseStep 3159929 = 2369947) B2369947
theorem B3946535 : Blo 1752577 3946535 := bstep (se 1 (by rfl) ⟨2959901, by rfl⟩ : syracuseStep 3946535 = 5919803) B5919803
theorem B5920937 : Blo 1752577 5920937 := bstep (se 2 (by rfl) ⟨2220351, by rfl⟩ : syracuseStep 5920937 = 4440703) B4440703
theorem B3947327 : Blo 1752577 3947327 := bstep (se 1 (by rfl) ⟨2960495, by rfl⟩ : syracuseStep 3947327 = 5920991) B5920991
theorem B49290119 : Blo 1752577 49290119 := bstep (se 1 (by rfl) ⟨36967589, by rfl⟩ : syracuseStep 49290119 = 73935179) B73935179
theorem B25288199 : Blo 1752577 25288199 := bstep (se 1 (by rfl) ⟨18966149, by rfl⟩ : syracuseStep 25288199 = 37932299) B37932299
theorem B4439711 : Blo 1752577 4439711 := bstep (se 1 (by rfl) ⟨3329783, by rfl⟩ : syracuseStep 4439711 = 6659567) B6659567
theorem B1753255 : Blo 1752577 1753255 := bstep (se 1 (by rfl) ⟨1314941, by rfl⟩ : syracuseStep 1753255 = 2629883) B2629883
theorem B1754111 : Blo 1752577 1754111 := bstep (se 1 (by rfl) ⟨1315583, by rfl⟩ : syracuseStep 1754111 = 2631167) B2631167
theorem B9987209 : Blo 1752577 9987209 := bstep (se 2 (by rfl) ⟨3745203, by rfl⟩ : syracuseStep 9987209 = 7490407) B7490407
theorem B22480037 : Blo 1752577 22480037 := bstep (se 4 (by rfl) ⟨2107503, by rfl⟩ : syracuseStep 22480037 = 4215007) B4215007
theorem B2631023 : Blo 1752577 2631023 := bstep (se 1 (by rfl) ⟨1973267, by rfl⟩ : syracuseStep 2631023 = 3946535) B3946535
theorem B2631551 : Blo 1752577 2631551 := bstep (se 1 (by rfl) ⟨1973663, by rfl⟩ : syracuseStep 2631551 = 3947327) B3947327
theorem B32860079 : Blo 1752577 32860079 := bstep (se 1 (by rfl) ⟨24645059, by rfl⟩ : syracuseStep 32860079 = 49290119) B49290119
theorem B2959807 : Blo 1752577 2959807 := bstep (se 1 (by rfl) ⟨2219855, by rfl⟩ : syracuseStep 2959807 = 4439711) B4439711
theorem B19974599 : Blo 1752577 19974599 := bstep (se 1 (by rfl) ⟨14980949, by rfl⟩ : syracuseStep 19974599 = 29961899) B29961899
theorem B8875007 : Blo 1752577 8875007 := bstep (se 1 (by rfl) ⟨6656255, by rfl⟩ : syracuseStep 8875007 = 13312511) B13312511
theorem B4992329 : Blo 1752577 4992329 := bstep (se 2 (by rfl) ⟨1872123, by rfl⟩ : syracuseStep 4992329 = 3744247) B3744247
theorem B14987753 : Blo 1752577 14987753 := bstep (se 2 (by rfl) ⟨5620407, by rfl⟩ : syracuseStep 14987753 = 11240815) B11240815
theorem B8426477 : Blo 1752577 8426477 := bstep (se 3 (by rfl) ⟨1579964, by rfl⟩ : syracuseStep 8426477 = 3159929) B3159929
theorem B2807455 : Blo 1752577 2807455 := bstep (se 1 (by rfl) ⟨2105591, by rfl⟩ : syracuseStep 2807455 = 4211183) B4211183
theorem B1971967 : Blo 1752577 1971967 := bstep (se 1 (by rfl) ⟨1478975, by rfl⟩ : syracuseStep 1971967 = 2957951) B2957951
theorem B27367483 : Blo 1752577 27367483 := bstep (se 1 (by rfl) ⟨20525612, by rfl⟩ : syracuseStep 27367483 = 41051225) B41051225
theorem B1972903 : Blo 1752577 1972903 := bstep (se 1 (by rfl) ⟨1479677, by rfl⟩ : syracuseStep 1972903 = 2959355) B2959355
theorem B3947291 : Blo 1752577 3947291 := bstep (se 1 (by rfl) ⟨2960468, by rfl⟩ : syracuseStep 3947291 = 5920937) B5920937
theorem B16849727 : Blo 1752577 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B16858799 : Blo 1752577 16858799 := bstep (se 1 (by rfl) ⟨12644099, by rfl⟩ : syracuseStep 16858799 = 25288199) B25288199
theorem B2630537 : Blo 1752577 2630537 := bstep (se 2 (by rfl) ⟨986451, by rfl⟩ : syracuseStep 2630537 = 1972903) B1972903
theorem B1754015 : Blo 1752577 1754015 := bstep (se 1 (by rfl) ⟨1315511, by rfl⟩ : syracuseStep 1754015 = 2631023) B2631023
theorem B1754367 : Blo 1752577 1754367 := bstep (se 1 (by rfl) ⟨1315775, by rfl⟩ : syracuseStep 1754367 = 2631551) B2631551
theorem B21906719 : Blo 1752577 21906719 := bstep (se 1 (by rfl) ⟨16430039, by rfl⟩ : syracuseStep 21906719 = 32860079) B32860079
theorem B2631527 : Blo 1752577 2631527 := bstep (se 1 (by rfl) ⟨1973645, by rfl⟩ : syracuseStep 2631527 = 3947291) B3947291
theorem B11233151 : Blo 1752577 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B5916671 : Blo 1752577 5916671 := bstep (se 1 (by rfl) ⟨4437503, by rfl⟩ : syracuseStep 5916671 = 8875007) B8875007
theorem B3328219 : Blo 1752577 3328219 := bstep (se 1 (by rfl) ⟨2496164, by rfl⟩ : syracuseStep 3328219 = 4992329) B4992329
theorem B36489977 : Blo 1752577 36489977 := bstep (se 2 (by rfl) ⟨13683741, by rfl⟩ : syracuseStep 36489977 = 27367483) B27367483
theorem B14986691 : Blo 1752577 14986691 := bstep (se 1 (by rfl) ⟨11240018, by rfl⟩ : syracuseStep 14986691 = 22480037) B22480037
theorem B13316399 : Blo 1752577 13316399 := bstep (se 1 (by rfl) ⟨9987299, by rfl⟩ : syracuseStep 13316399 = 19974599) B19974599
theorem B9991835 : Blo 1752577 9991835 := bstep (se 1 (by rfl) ⟨7493876, by rfl⟩ : syracuseStep 9991835 = 14987753) B14987753
theorem B3946409 : Blo 1752577 3946409 := bstep (se 2 (by rfl) ⟨1479903, by rfl⟩ : syracuseStep 3946409 = 2959807) B2959807
theorem B6658139 : Blo 1752577 6658139 := bstep (se 1 (by rfl) ⟨4993604, by rfl⟩ : syracuseStep 6658139 = 9987209) B9987209
theorem B3743273 : Blo 1752577 3743273 := bstep (se 2 (by rfl) ⟨1403727, by rfl⟩ : syracuseStep 3743273 = 2807455) B2807455
theorem B2629289 : Blo 1752577 2629289 := bstep (se 2 (by rfl) ⟨985983, by rfl⟩ : syracuseStep 2629289 = 1971967) B1971967
theorem B11239199 : Blo 1752577 11239199 := bstep (se 1 (by rfl) ⟨8429399, by rfl⟩ : syracuseStep 11239199 = 16858799) B16858799
theorem B22470605 : Blo 1752577 22470605 := bstep (se 3 (by rfl) ⟨4213238, by rfl⟩ : syracuseStep 22470605 = 8426477) B8426477
theorem B1753691 : Blo 1752577 1753691 := bstep (se 1 (by rfl) ⟨1315268, by rfl⟩ : syracuseStep 1753691 = 2630537) B2630537
theorem B6661223 : Blo 1752577 6661223 := bstep (se 1 (by rfl) ⟨4995917, by rfl⟩ : syracuseStep 6661223 = 9991835) B9991835
theorem B1754351 : Blo 1752577 1754351 := bstep (se 1 (by rfl) ⟨1315763, by rfl⟩ : syracuseStep 1754351 = 2631527) B2631527
theorem B7488767 : Blo 1752577 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B2630939 : Blo 1752577 2630939 := bstep (se 1 (by rfl) ⟨1973204, by rfl⟩ : syracuseStep 2630939 = 3946409) B3946409
theorem B3944447 : Blo 1752577 3944447 := bstep (se 1 (by rfl) ⟨2958335, by rfl⟩ : syracuseStep 3944447 = 5916671) B5916671
theorem B9982061 : Blo 1752577 9982061 := bstep (se 3 (by rfl) ⟨1871636, by rfl⟩ : syracuseStep 9982061 = 3743273) B3743273
theorem B24326651 : Blo 1752577 24326651 := bstep (se 1 (by rfl) ⟨18244988, by rfl⟩ : syracuseStep 24326651 = 36489977) B36489977
theorem B9991127 : Blo 1752577 9991127 := bstep (se 1 (by rfl) ⟨7493345, by rfl⟩ : syracuseStep 9991127 = 14986691) B14986691
theorem B7492799 : Blo 1752577 7492799 := bstep (se 1 (by rfl) ⟨5619599, by rfl⟩ : syracuseStep 7492799 = 11239199) B11239199
theorem B14980403 : Blo 1752577 14980403 := bstep (se 1 (by rfl) ⟨11235302, by rfl⟩ : syracuseStep 14980403 = 22470605) B22470605
theorem B8877599 : Blo 1752577 8877599 := bstep (se 1 (by rfl) ⟨6658199, by rfl⟩ : syracuseStep 8877599 = 13316399) B13316399
theorem B4437625 : Blo 1752577 4437625 := bstep (se 2 (by rfl) ⟨1664109, by rfl⟩ : syracuseStep 4437625 = 3328219) B3328219
theorem B14604479 : Blo 1752577 14604479 := bstep (se 1 (by rfl) ⟨10953359, by rfl⟩ : syracuseStep 14604479 = 21906719) B21906719
theorem B4438759 : Blo 1752577 4438759 := bstep (se 1 (by rfl) ⟨3329069, by rfl⟩ : syracuseStep 4438759 = 6658139) B6658139
theorem B1752859 : Blo 1752577 1752859 := bstep (se 1 (by rfl) ⟨1314644, by rfl⟩ : syracuseStep 1752859 = 2629289) B2629289
theorem B6660751 : Blo 1752577 6660751 := bstep (se 1 (by rfl) ⟨4995563, by rfl⟩ : syracuseStep 6660751 = 9991127) B9991127
theorem B4440815 : Blo 1752577 4440815 := bstep (se 1 (by rfl) ⟨3330611, by rfl⟩ : syracuseStep 4440815 = 6661223) B6661223
theorem B1753959 : Blo 1752577 1753959 := bstep (se 1 (by rfl) ⟨1315469, by rfl⟩ : syracuseStep 1753959 = 2630939) B2630939
theorem B9986935 : Blo 1752577 9986935 := bstep (se 1 (by rfl) ⟨7490201, by rfl⟩ : syracuseStep 9986935 = 14980403) B14980403
theorem B5916833 : Blo 1752577 5916833 := bstep (se 2 (by rfl) ⟨2218812, by rfl⟩ : syracuseStep 5916833 = 4437625) B4437625
theorem B6654707 : Blo 1752577 6654707 := bstep (se 1 (by rfl) ⟨4991030, by rfl⟩ : syracuseStep 6654707 = 9982061) B9982061
theorem B4992511 : Blo 1752577 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B5918345 : Blo 1752577 5918345 := bstep (se 2 (by rfl) ⟨2219379, by rfl⟩ : syracuseStep 5918345 = 4438759) B4438759
theorem B5918399 : Blo 1752577 5918399 := bstep (se 1 (by rfl) ⟨4438799, by rfl⟩ : syracuseStep 5918399 = 8877599) B8877599
theorem B9736319 : Blo 1752577 9736319 := bstep (se 1 (by rfl) ⟨7302239, by rfl⟩ : syracuseStep 9736319 = 14604479) B14604479
theorem B16217767 : Blo 1752577 16217767 := bstep (se 1 (by rfl) ⟨12163325, by rfl⟩ : syracuseStep 16217767 = 24326651) B24326651
theorem B4995199 : Blo 1752577 4995199 := bstep (se 1 (by rfl) ⟨3746399, by rfl⟩ : syracuseStep 4995199 = 7492799) B7492799
theorem B2629631 : Blo 1752577 2629631 := bstep (se 1 (by rfl) ⟨1972223, by rfl⟩ : syracuseStep 2629631 = 3944447) B3944447
theorem B6660265 : Blo 1752577 6660265 := bstep (se 2 (by rfl) ⟨2497599, by rfl⟩ : syracuseStep 6660265 = 4995199) B4995199
theorem B8881001 : Blo 1752577 8881001 := bstep (se 2 (by rfl) ⟨3330375, by rfl⟩ : syracuseStep 8881001 = 6660751) B6660751
theorem B25963517 : Blo 1752577 25963517 := bstep (se 3 (by rfl) ⟨4868159, by rfl⟩ : syracuseStep 25963517 = 9736319) B9736319
theorem B2960543 : Blo 1752577 2960543 := bstep (se 1 (by rfl) ⟨2220407, by rfl⟩ : syracuseStep 2960543 = 4440815) B4440815
theorem B13315913 : Blo 1752577 13315913 := bstep (se 2 (by rfl) ⟨4993467, by rfl⟩ : syracuseStep 13315913 = 9986935) B9986935
theorem B3944555 : Blo 1752577 3944555 := bstep (se 1 (by rfl) ⟨2958416, by rfl⟩ : syracuseStep 3944555 = 5916833) B5916833
theorem B4436471 : Blo 1752577 4436471 := bstep (se 1 (by rfl) ⟨3327353, by rfl⟩ : syracuseStep 4436471 = 6654707) B6654707
theorem B6656681 : Blo 1752577 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B21623689 : Blo 1752577 21623689 := bstep (se 2 (by rfl) ⟨8108883, by rfl⟩ : syracuseStep 21623689 = 16217767) B16217767
theorem B3945563 : Blo 1752577 3945563 := bstep (se 1 (by rfl) ⟨2959172, by rfl⟩ : syracuseStep 3945563 = 5918345) B5918345
theorem B3945599 : Blo 1752577 3945599 := bstep (se 1 (by rfl) ⟨2959199, by rfl⟩ : syracuseStep 3945599 = 5918399) B5918399
theorem B1753087 : Blo 1752577 1753087 := bstep (se 1 (by rfl) ⟨1314815, by rfl⟩ : syracuseStep 1753087 = 2629631) B2629631
theorem B2629703 : Blo 1752577 2629703 := bstep (se 1 (by rfl) ⟨1972277, by rfl⟩ : syracuseStep 2629703 = 3944555) B3944555
theorem B8880353 : Blo 1752577 8880353 := bstep (se 2 (by rfl) ⟨3330132, by rfl⟩ : syracuseStep 8880353 = 6660265) B6660265
theorem B2957647 : Blo 1752577 2957647 := bstep (se 1 (by rfl) ⟨2218235, by rfl⟩ : syracuseStep 2957647 = 4436471) B4436471
theorem B2630375 : Blo 1752577 2630375 := bstep (se 1 (by rfl) ⟨1972781, by rfl⟩ : syracuseStep 2630375 = 3945563) B3945563
theorem B2630399 : Blo 1752577 2630399 := bstep (se 1 (by rfl) ⟨1972799, by rfl⟩ : syracuseStep 2630399 = 3945599) B3945599
theorem B8877275 : Blo 1752577 8877275 := bstep (se 1 (by rfl) ⟨6657956, by rfl⟩ : syracuseStep 8877275 = 13315913) B13315913
theorem B4437787 : Blo 1752577 4437787 := bstep (se 1 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 4437787 = 6656681) B6656681
theorem B5920667 : Blo 1752577 5920667 := bstep (se 1 (by rfl) ⟨4440500, by rfl⟩ : syracuseStep 5920667 = 8881001) B8881001
theorem B17309011 : Blo 1752577 17309011 := bstep (se 1 (by rfl) ⟨12981758, by rfl⟩ : syracuseStep 17309011 = 25963517) B25963517
theorem B115326341 : Blo 1752577 115326341 := bstep (se 4 (by rfl) ⟨10811844, by rfl⟩ : syracuseStep 115326341 = 21623689) B21623689
theorem B1973695 : Blo 1752577 1973695 := bstep (se 1 (by rfl) ⟨1480271, by rfl⟩ : syracuseStep 1973695 = 2960543) B2960543
theorem B1753135 : Blo 1752577 1753135 := bstep (se 1 (by rfl) ⟨1314851, by rfl⟩ : syracuseStep 1753135 = 2629703) B2629703
theorem B1753583 : Blo 1752577 1753583 := bstep (se 1 (by rfl) ⟨1315187, by rfl⟩ : syracuseStep 1753583 = 2630375) B2630375
theorem B1753599 : Blo 1752577 1753599 := bstep (se 1 (by rfl) ⟨1315199, by rfl⟩ : syracuseStep 1753599 = 2630399) B2630399
theorem B23078681 : Blo 1752577 23078681 := bstep (se 2 (by rfl) ⟨8654505, by rfl⟩ : syracuseStep 23078681 = 17309011) B17309011
theorem B2631593 : Blo 1752577 2631593 := bstep (se 2 (by rfl) ⟨986847, by rfl⟩ : syracuseStep 2631593 = 1973695) B1973695
theorem B76884227 : Blo 1752577 76884227 := bstep (se 1 (by rfl) ⟨57663170, by rfl⟩ : syracuseStep 76884227 = 115326341) B115326341
theorem B5917049 : Blo 1752577 5917049 := bstep (se 2 (by rfl) ⟨2218893, by rfl⟩ : syracuseStep 5917049 = 4437787) B4437787
theorem B3943529 : Blo 1752577 3943529 := bstep (se 2 (by rfl) ⟨1478823, by rfl⟩ : syracuseStep 3943529 = 2957647) B2957647
theorem B5918183 : Blo 1752577 5918183 := bstep (se 1 (by rfl) ⟨4438637, by rfl⟩ : syracuseStep 5918183 = 8877275) B8877275
theorem B5920235 : Blo 1752577 5920235 := bstep (se 1 (by rfl) ⟨4440176, by rfl⟩ : syracuseStep 5920235 = 8880353) B8880353
theorem B3947111 : Blo 1752577 3947111 := bstep (se 1 (by rfl) ⟨2960333, by rfl⟩ : syracuseStep 3947111 = 5920667) B5920667
theorem B15385787 : Blo 1752577 15385787 := bstep (se 1 (by rfl) ⟨11539340, by rfl⟩ : syracuseStep 15385787 = 23078681) B23078681
theorem B1754395 : Blo 1752577 1754395 := bstep (se 1 (by rfl) ⟨1315796, by rfl⟩ : syracuseStep 1754395 = 2631593) B2631593
theorem B2631407 : Blo 1752577 2631407 := bstep (se 1 (by rfl) ⟨1973555, by rfl⟩ : syracuseStep 2631407 = 3947111) B3947111
theorem B3944699 : Blo 1752577 3944699 := bstep (se 1 (by rfl) ⟨2958524, by rfl⟩ : syracuseStep 3944699 = 5917049) B5917049
theorem B3945455 : Blo 1752577 3945455 := bstep (se 1 (by rfl) ⟨2959091, by rfl⟩ : syracuseStep 3945455 = 5918183) B5918183
theorem B3946823 : Blo 1752577 3946823 := bstep (se 1 (by rfl) ⟨2960117, by rfl⟩ : syracuseStep 3946823 = 5920235) B5920235
theorem B51256151 : Blo 1752577 51256151 := bstep (se 1 (by rfl) ⟨38442113, by rfl⟩ : syracuseStep 51256151 = 76884227) B76884227
theorem B2629019 : Blo 1752577 2629019 := bstep (se 1 (by rfl) ⟨1971764, by rfl⟩ : syracuseStep 2629019 = 3943529) B3943529
theorem B2629799 : Blo 1752577 2629799 := bstep (se 1 (by rfl) ⟨1972349, by rfl⟩ : syracuseStep 2629799 = 3944699) B3944699
theorem B2630303 : Blo 1752577 2630303 := bstep (se 1 (by rfl) ⟨1972727, by rfl⟩ : syracuseStep 2630303 = 3945455) B3945455
theorem B10257191 : Blo 1752577 10257191 := bstep (se 1 (by rfl) ⟨7692893, by rfl⟩ : syracuseStep 10257191 = 15385787) B15385787
theorem B1754271 : Blo 1752577 1754271 := bstep (se 1 (by rfl) ⟨1315703, by rfl⟩ : syracuseStep 1754271 = 2631407) B2631407
theorem B2631215 : Blo 1752577 2631215 := bstep (se 1 (by rfl) ⟨1973411, by rfl⟩ : syracuseStep 2631215 = 3946823) B3946823
theorem B34170767 : Blo 1752577 34170767 := bstep (se 1 (by rfl) ⟨25628075, by rfl⟩ : syracuseStep 34170767 = 51256151) B51256151
theorem B1752679 : Blo 1752577 1752679 := bstep (se 1 (by rfl) ⟨1314509, by rfl⟩ : syracuseStep 1752679 = 2629019) B2629019
theorem B1753199 : Blo 1752577 1753199 := bstep (se 1 (by rfl) ⟨1314899, by rfl⟩ : syracuseStep 1753199 = 2629799) B2629799
theorem B1753535 : Blo 1752577 1753535 := bstep (se 1 (by rfl) ⟨1315151, by rfl⟩ : syracuseStep 1753535 = 2630303) B2630303
theorem B1754143 : Blo 1752577 1754143 := bstep (se 1 (by rfl) ⟨1315607, by rfl⟩ : syracuseStep 1754143 = 2631215) B2631215
theorem B6838127 : Blo 1752577 6838127 := bstep (se 1 (by rfl) ⟨5128595, by rfl⟩ : syracuseStep 6838127 = 10257191) B10257191
theorem B22780511 : Blo 1752577 22780511 := bstep (se 1 (by rfl) ⟨17085383, by rfl⟩ : syracuseStep 22780511 = 34170767) B34170767
theorem B4558751 : Blo 1752577 4558751 := bstep (se 1 (by rfl) ⟨3419063, by rfl⟩ : syracuseStep 4558751 = 6838127) B6838127
theorem B15187007 : Blo 1752577 15187007 := bstep (se 1 (by rfl) ⟨11390255, by rfl⟩ : syracuseStep 15187007 = 22780511) B22780511
theorem B10124671 : Blo 1752577 10124671 := bstep (se 1 (by rfl) ⟨7593503, by rfl⟩ : syracuseStep 10124671 = 15187007) B15187007
theorem B3039167 : Blo 1752577 3039167 := bstep (se 1 (by rfl) ⟨2279375, by rfl⟩ : syracuseStep 3039167 = 4558751) B4558751
theorem B8104445 : Blo 1752577 8104445 := bstep (se 3 (by rfl) ⟨1519583, by rfl⟩ : syracuseStep 8104445 = 3039167) B3039167
theorem B13499561 : Blo 1752577 13499561 := bstep (se 2 (by rfl) ⟨5062335, by rfl⟩ : syracuseStep 13499561 = 10124671) B10124671
theorem B5402963 : Blo 1752577 5402963 := bstep (se 1 (by rfl) ⟨4052222, by rfl⟩ : syracuseStep 5402963 = 8104445) B8104445
theorem B8999707 : Blo 1752577 8999707 := bstep (se 1 (by rfl) ⟨6749780, by rfl⟩ : syracuseStep 8999707 = 13499561) B13499561
theorem B14407901 : Blo 1752577 14407901 := bstep (se 3 (by rfl) ⟨2701481, by rfl⟩ : syracuseStep 14407901 = 5402963) B5402963
theorem B11999609 : Blo 1752577 11999609 := bstep (se 2 (by rfl) ⟨4499853, by rfl⟩ : syracuseStep 11999609 = 8999707) B8999707
theorem B9605267 : Blo 1752577 9605267 := bstep (se 1 (by rfl) ⟨7203950, by rfl⟩ : syracuseStep 9605267 = 14407901) B14407901
theorem B7999739 : Blo 1752577 7999739 := bstep (se 1 (by rfl) ⟨5999804, by rfl⟩ : syracuseStep 7999739 = 11999609) B11999609
theorem B5333159 : Blo 1752577 5333159 := bstep (se 1 (by rfl) ⟨3999869, by rfl⟩ : syracuseStep 5333159 = 7999739) B7999739
theorem B6403511 : Blo 1752577 6403511 := bstep (se 1 (by rfl) ⟨4802633, by rfl⟩ : syracuseStep 6403511 = 9605267) B9605267
theorem B14221757 : Blo 1752577 14221757 := bstep (se 3 (by rfl) ⟨2666579, by rfl⟩ : syracuseStep 14221757 = 5333159) B5333159
theorem B4269007 : Blo 1752577 4269007 := bstep (se 1 (by rfl) ⟨3201755, by rfl⟩ : syracuseStep 4269007 = 6403511) B6403511
theorem B22768037 : Blo 1752577 22768037 := bstep (se 4 (by rfl) ⟨2134503, by rfl⟩ : syracuseStep 22768037 = 4269007) B4269007
theorem B37924685 : Blo 1752577 37924685 := bstep (se 3 (by rfl) ⟨7110878, by rfl⟩ : syracuseStep 37924685 = 14221757) B14221757
theorem B25283123 : Blo 1752577 25283123 := bstep (se 1 (by rfl) ⟨18962342, by rfl⟩ : syracuseStep 25283123 = 37924685) B37924685
theorem B15178691 : Blo 1752577 15178691 := bstep (se 1 (by rfl) ⟨11384018, by rfl⟩ : syracuseStep 15178691 = 22768037) B22768037
theorem B16855415 : Blo 1752577 16855415 := bstep (se 1 (by rfl) ⟨12641561, by rfl⟩ : syracuseStep 16855415 = 25283123) B25283123
theorem B40476509 : Blo 1752577 40476509 := bstep (se 3 (by rfl) ⟨7589345, by rfl⟩ : syracuseStep 40476509 = 15178691) B15178691
theorem B11236943 : Blo 1752577 11236943 := bstep (se 1 (by rfl) ⟨8427707, by rfl⟩ : syracuseStep 11236943 = 16855415) B16855415
theorem B26984339 : Blo 1752577 26984339 := bstep (se 1 (by rfl) ⟨20238254, by rfl⟩ : syracuseStep 26984339 = 40476509) B40476509
theorem B7491295 : Blo 1752577 7491295 := bstep (se 1 (by rfl) ⟨5618471, by rfl⟩ : syracuseStep 7491295 = 11236943) B11236943
theorem B17989559 : Blo 1752577 17989559 := bstep (se 1 (by rfl) ⟨13492169, by rfl⟩ : syracuseStep 17989559 = 26984339) B26984339
theorem B9988393 : Blo 1752577 9988393 := bstep (se 2 (by rfl) ⟨3745647, by rfl⟩ : syracuseStep 9988393 = 7491295) B7491295
theorem B11993039 : Blo 1752577 11993039 := bstep (se 1 (by rfl) ⟨8994779, by rfl⟩ : syracuseStep 11993039 = 17989559) B17989559
theorem B13317857 : Blo 1752577 13317857 := bstep (se 2 (by rfl) ⟨4994196, by rfl⟩ : syracuseStep 13317857 = 9988393) B9988393
theorem B7995359 : Blo 1752577 7995359 := bstep (se 1 (by rfl) ⟨5996519, by rfl⟩ : syracuseStep 7995359 = 11993039) B11993039
theorem B21320957 : Blo 1752577 21320957 := bstep (se 3 (by rfl) ⟨3997679, by rfl⟩ : syracuseStep 21320957 = 7995359) B7995359
theorem B8878571 : Blo 1752577 8878571 := bstep (se 1 (by rfl) ⟨6658928, by rfl⟩ : syracuseStep 8878571 = 13317857) B13317857
theorem B14213971 : Blo 1752577 14213971 := bstep (se 1 (by rfl) ⟨10660478, by rfl⟩ : syracuseStep 14213971 = 21320957) B21320957
theorem B5919047 : Blo 1752577 5919047 := bstep (se 1 (by rfl) ⟨4439285, by rfl⟩ : syracuseStep 5919047 = 8878571) B8878571
theorem B3946031 : Blo 1752577 3946031 := bstep (se 1 (by rfl) ⟨2959523, by rfl⟩ : syracuseStep 3946031 = 5919047) B5919047
theorem B75807845 : Blo 1752577 75807845 := bstep (se 4 (by rfl) ⟨7106985, by rfl⟩ : syracuseStep 75807845 = 14213971) B14213971
theorem B2630687 : Blo 1752577 2630687 := bstep (se 1 (by rfl) ⟨1973015, by rfl⟩ : syracuseStep 2630687 = 3946031) B3946031
theorem B50538563 : Blo 1752577 50538563 := bstep (se 1 (by rfl) ⟨37903922, by rfl⟩ : syracuseStep 50538563 = 75807845) B75807845
theorem B1753791 : Blo 1752577 1753791 := bstep (se 1 (by rfl) ⟨1315343, by rfl⟩ : syracuseStep 1753791 = 2630687) B2630687
theorem B33692375 : Blo 1752577 33692375 := bstep (se 1 (by rfl) ⟨25269281, by rfl⟩ : syracuseStep 33692375 = 50538563) B50538563
theorem B22461583 : Blo 1752577 22461583 := bstep (se 1 (by rfl) ⟨16846187, by rfl⟩ : syracuseStep 22461583 = 33692375) B33692375
theorem B29948777 : Blo 1752577 29948777 := bstep (se 2 (by rfl) ⟨11230791, by rfl⟩ : syracuseStep 29948777 = 22461583) B22461583
theorem B19965851 : Blo 1752577 19965851 := bstep (se 1 (by rfl) ⟨14974388, by rfl⟩ : syracuseStep 19965851 = 29948777) B29948777
theorem B13310567 : Blo 1752577 13310567 := bstep (se 1 (by rfl) ⟨9982925, by rfl⟩ : syracuseStep 13310567 = 19965851) B19965851
theorem B8873711 : Blo 1752577 8873711 := bstep (se 1 (by rfl) ⟨6655283, by rfl⟩ : syracuseStep 8873711 = 13310567) B13310567
theorem B5915807 : Blo 1752577 5915807 := bstep (se 1 (by rfl) ⟨4436855, by rfl⟩ : syracuseStep 5915807 = 8873711) B8873711
theorem B3943871 : Blo 1752577 3943871 := bstep (se 1 (by rfl) ⟨2957903, by rfl⟩ : syracuseStep 3943871 = 5915807) B5915807
theorem B2629247 : Blo 1752577 2629247 := bstep (se 1 (by rfl) ⟨1971935, by rfl⟩ : syracuseStep 2629247 = 3943871) B3943871
theorem B1752831 : Blo 1752577 1752831 := bstep (se 1 (by rfl) ⟨1314623, by rfl⟩ : syracuseStep 1752831 = 2629247) B2629247

theorem C0 (j : ℕ) (h1 : 438144 ≤ j) (h2 : j ≤ 438643) : Blo 1752577 (4 * j + 3) := by
  interval_cases j
  · exact B1752579
  · exact B1752583
  · exact B1752587
  · exact B1752591
  · exact B1752595
  · exact B1752599
  · exact B1752603
  · exact B1752607
  · exact B1752611
  · exact B1752615
  · exact B1752619
  · exact B1752623
  · exact B1752627
  · exact B1752631
  · exact B1752635
  · exact B1752639
  · exact B1752643
  · exact B1752647
  · exact B1752651
  · exact B1752655
  · exact B1752659
  · exact B1752663
  · exact B1752667
  · exact B1752671
  · exact B1752675
  · exact B1752679
  · exact B1752683
  · exact B1752687
  · exact B1752691
  · exact B1752695
  · exact B1752699
  · exact B1752703
  · exact B1752707
  · exact B1752711
  · exact B1752715
  · exact B1752719
  · exact B1752723
  · exact B1752727
  · exact B1752731
  · exact B1752735
  · exact B1752739
  · exact B1752743
  · exact B1752747
  · exact B1752751
  · exact B1752755
  · exact B1752759
  · exact B1752763
  · exact B1752767
  · exact B1752771
  · exact B1752775
  · exact B1752779
  · exact B1752783
  · exact B1752787
  · exact B1752791
  · exact B1752795
  · exact B1752799
  · exact B1752803
  · exact B1752807
  · exact B1752811
  · exact B1752815
  · exact B1752819
  · exact B1752823
  · exact B1752827
  · exact B1752831
  · exact B1752835
  · exact B1752839
  · exact B1752843
  · exact B1752847
  · exact B1752851
  · exact B1752855
  · exact B1752859
  · exact B1752863
  · exact B1752867
  · exact B1752871
  · exact B1752875
  · exact B1752879
  · exact B1752883
  · exact B1752887
  · exact B1752891
  · exact B1752895
  · exact B1752899
  · exact B1752903
  · exact B1752907
  · exact B1752911
  · exact B1752915
  · exact B1752919
  · exact B1752923
  · exact B1752927
  · exact B1752931
  · exact B1752935
  · exact B1752939
  · exact B1752943
  · exact B1752947
  · exact B1752951
  · exact B1752955
  · exact B1752959
  · exact B1752963
  · exact B1752967
  · exact B1752971
  · exact B1752975
  · exact B1752979
  · exact B1752983
  · exact B1752987
  · exact B1752991
  · exact B1752995
  · exact B1752999
  · exact B1753003
  · exact B1753007
  · exact B1753011
  · exact B1753015
  · exact B1753019
  · exact B1753023
  · exact B1753027
  · exact B1753031
  · exact B1753035
  · exact B1753039
  · exact B1753043
  · exact B1753047
  · exact B1753051
  · exact B1753055
  · exact B1753059
  · exact B1753063
  · exact B1753067
  · exact B1753071
  · exact B1753075
  · exact B1753079
  · exact B1753083
  · exact B1753087
  · exact B1753091
  · exact B1753095
  · exact B1753099
  · exact B1753103
  · exact B1753107
  · exact B1753111
  · exact B1753115
  · exact B1753119
  · exact B1753123
  · exact B1753127
  · exact B1753131
  · exact B1753135
  · exact B1753139
  · exact B1753143
  · exact B1753147
  · exact B1753151
  · exact B1753155
  · exact B1753159
  · exact B1753163
  · exact B1753167
  · exact B1753171
  · exact B1753175
  · exact B1753179
  · exact B1753183
  · exact B1753187
  · exact B1753191
  · exact B1753195
  · exact B1753199
  · exact B1753203
  · exact B1753207
  · exact B1753211
  · exact B1753215
  · exact B1753219
  · exact B1753223
  · exact B1753227
  · exact B1753231
  · exact B1753235
  · exact B1753239
  · exact B1753243
  · exact B1753247
  · exact B1753251
  · exact B1753255
  · exact B1753259
  · exact B1753263
  · exact B1753267
  · exact B1753271
  · exact B1753275
  · exact B1753279
  · exact B1753283
  · exact B1753287
  · exact B1753291
  · exact B1753295
  · exact B1753299
  · exact B1753303
  · exact B1753307
  · exact B1753311
  · exact B1753315
  · exact B1753319
  · exact B1753323
  · exact B1753327
  · exact B1753331
  · exact B1753335
  · exact B1753339
  · exact B1753343
  · exact B1753347
  · exact B1753351
  · exact B1753355
  · exact B1753359
  · exact B1753363
  · exact B1753367
  · exact B1753371
  · exact B1753375
  · exact B1753379
  · exact B1753383
  · exact B1753387
  · exact B1753391
  · exact B1753395
  · exact B1753399
  · exact B1753403
  · exact B1753407
  · exact B1753411
  · exact B1753415
  · exact B1753419
  · exact B1753423
  · exact B1753427
  · exact B1753431
  · exact B1753435
  · exact B1753439
  · exact B1753443
  · exact B1753447
  · exact B1753451
  · exact B1753455
  · exact B1753459
  · exact B1753463
  · exact B1753467
  · exact B1753471
  · exact B1753475
  · exact B1753479
  · exact B1753483
  · exact B1753487
  · exact B1753491
  · exact B1753495
  · exact B1753499
  · exact B1753503
  · exact B1753507
  · exact B1753511
  · exact B1753515
  · exact B1753519
  · exact B1753523
  · exact B1753527
  · exact B1753531
  · exact B1753535
  · exact B1753539
  · exact B1753543
  · exact B1753547
  · exact B1753551
  · exact B1753555
  · exact B1753559
  · exact B1753563
  · exact B1753567
  · exact B1753571
  · exact B1753575
  · exact B1753579
  · exact B1753583
  · exact B1753587
  · exact B1753591
  · exact B1753595
  · exact B1753599
  · exact B1753603
  · exact B1753607
  · exact B1753611
  · exact B1753615
  · exact B1753619
  · exact B1753623
  · exact B1753627
  · exact B1753631
  · exact B1753635
  · exact B1753639
  · exact B1753643
  · exact B1753647
  · exact B1753651
  · exact B1753655
  · exact B1753659
  · exact B1753663
  · exact B1753667
  · exact B1753671
  · exact B1753675
  · exact B1753679
  · exact B1753683
  · exact B1753687
  · exact B1753691
  · exact B1753695
  · exact B1753699
  · exact B1753703
  · exact B1753707
  · exact B1753711
  · exact B1753715
  · exact B1753719
  · exact B1753723
  · exact B1753727
  · exact B1753731
  · exact B1753735
  · exact B1753739
  · exact B1753743
  · exact B1753747
  · exact B1753751
  · exact B1753755
  · exact B1753759
  · exact B1753763
  · exact B1753767
  · exact B1753771
  · exact B1753775
  · exact B1753779
  · exact B1753783
  · exact B1753787
  · exact B1753791
  · exact B1753795
  · exact B1753799
  · exact B1753803
  · exact B1753807
  · exact B1753811
  · exact B1753815
  · exact B1753819
  · exact B1753823
  · exact B1753827
  · exact B1753831
  · exact B1753835
  · exact B1753839
  · exact B1753843
  · exact B1753847
  · exact B1753851
  · exact B1753855
  · exact B1753859
  · exact B1753863
  · exact B1753867
  · exact B1753871
  · exact B1753875
  · exact B1753879
  · exact B1753883
  · exact B1753887
  · exact B1753891
  · exact B1753895
  · exact B1753899
  · exact B1753903
  · exact B1753907
  · exact B1753911
  · exact B1753915
  · exact B1753919
  · exact B1753923
  · exact B1753927
  · exact B1753931
  · exact B1753935
  · exact B1753939
  · exact B1753943
  · exact B1753947
  · exact B1753951
  · exact B1753955
  · exact B1753959
  · exact B1753963
  · exact B1753967
  · exact B1753971
  · exact B1753975
  · exact B1753979
  · exact B1753983
  · exact B1753987
  · exact B1753991
  · exact B1753995
  · exact B1753999
  · exact B1754003
  · exact B1754007
  · exact B1754011
  · exact B1754015
  · exact B1754019
  · exact B1754023
  · exact B1754027
  · exact B1754031
  · exact B1754035
  · exact B1754039
  · exact B1754043
  · exact B1754047
  · exact B1754051
  · exact B1754055
  · exact B1754059
  · exact B1754063
  · exact B1754067
  · exact B1754071
  · exact B1754075
  · exact B1754079
  · exact B1754083
  · exact B1754087
  · exact B1754091
  · exact B1754095
  · exact B1754099
  · exact B1754103
  · exact B1754107
  · exact B1754111
  · exact B1754115
  · exact B1754119
  · exact B1754123
  · exact B1754127
  · exact B1754131
  · exact B1754135
  · exact B1754139
  · exact B1754143
  · exact B1754147
  · exact B1754151
  · exact B1754155
  · exact B1754159
  · exact B1754163
  · exact B1754167
  · exact B1754171
  · exact B1754175
  · exact B1754179
  · exact B1754183
  · exact B1754187
  · exact B1754191
  · exact B1754195
  · exact B1754199
  · exact B1754203
  · exact B1754207
  · exact B1754211
  · exact B1754215
  · exact B1754219
  · exact B1754223
  · exact B1754227
  · exact B1754231
  · exact B1754235
  · exact B1754239
  · exact B1754243
  · exact B1754247
  · exact B1754251
  · exact B1754255
  · exact B1754259
  · exact B1754263
  · exact B1754267
  · exact B1754271
  · exact B1754275
  · exact B1754279
  · exact B1754283
  · exact B1754287
  · exact B1754291
  · exact B1754295
  · exact B1754299
  · exact B1754303
  · exact B1754307
  · exact B1754311
  · exact B1754315
  · exact B1754319
  · exact B1754323
  · exact B1754327
  · exact B1754331
  · exact B1754335
  · exact B1754339
  · exact B1754343
  · exact B1754347
  · exact B1754351
  · exact B1754355
  · exact B1754359
  · exact B1754363
  · exact B1754367
  · exact B1754371
  · exact B1754375
  · exact B1754379
  · exact B1754383
  · exact B1754387
  · exact B1754391
  · exact B1754395
  · exact B1754399
  · exact B1754403
  · exact B1754407
  · exact B1754411
  · exact B1754415
  · exact B1754419
  · exact B1754423
  · exact B1754427
  · exact B1754431
  · exact B1754435
  · exact B1754439
  · exact B1754443
  · exact B1754447
  · exact B1754451
  · exact B1754455
  · exact B1754459
  · exact B1754463
  · exact B1754467
  · exact B1754471
  · exact B1754475
  · exact B1754479
  · exact B1754483
  · exact B1754487
  · exact B1754491
  · exact B1754495
  · exact B1754499
  · exact B1754503
  · exact B1754507
  · exact B1754511
  · exact B1754515
  · exact B1754519
  · exact B1754523
  · exact B1754527
  · exact B1754531
  · exact B1754535
  · exact B1754539
  · exact B1754543
  · exact B1754547
  · exact B1754551
  · exact B1754555
  · exact B1754559
  · exact B1754563
  · exact B1754567
  · exact B1754571
  · exact B1754575

theorem solution (m : ℕ) (hlo : 1752577 ≤ m) (hhi : m ≤ 1754577) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 438144 ≤ j := by omega
    have hj2 : j ≤ 438643 := by omega
    have hb : Blo 1752577 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
