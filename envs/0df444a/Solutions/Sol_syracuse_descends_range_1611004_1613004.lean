-- Prove2me | solution 1 for syracuse_descends_range_1611004_1613004
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:12:03.137384+00:00
-- url     : https://prove2.me/submissions/20a7f7ea-2c0b-4e01-b06d-01df5783f69d

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


theorem B2719757 : Blo 1611004 2719757 := bbase (se 3 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 2719757 = 1019909) (by norm_num)
theorem B3629069 : Blo 1611004 3629069 := bbase (se 3 (by rfl) ⟨680450, by rfl⟩ : syracuseStep 3629069 = 1360901) (by norm_num)
theorem B2416661 : Blo 1611004 2416661 := bbase (se 6 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 2416661 = 113281) (by norm_num)
theorem B2039833 : Blo 1611004 2039833 := bbase (se 2 (by rfl) ⟨764937, by rfl⟩ : syracuseStep 2039833 = 1529875) (by norm_num)
theorem B2416685 : Blo 1611004 2416685 := bbase (se 3 (by rfl) ⟨453128, by rfl⟩ : syracuseStep 2416685 = 906257) (by norm_num)
theorem B2326573 : Blo 1611004 2326573 := bbase (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) (by norm_num)
theorem B3268669 : Blo 1611004 3268669 := bbase (se 3 (by rfl) ⟨612875, by rfl⟩ : syracuseStep 3268669 = 1225751) (by norm_num)
theorem B2416709 : Blo 1611004 2416709 := bbase (se 4 (by rfl) ⟨226566, by rfl⟩ : syracuseStep 2416709 = 453133) (by norm_num)
theorem B3629141 : Blo 1611004 3629141 := bbase (se 8 (by rfl) ⟨21264, by rfl⟩ : syracuseStep 3629141 = 42529) (by norm_num)
theorem B2416733 : Blo 1611004 2416733 := bbase (se 3 (by rfl) ⟨453137, by rfl⟩ : syracuseStep 2416733 = 906275) (by norm_num)
theorem B4079717 : Blo 1611004 4079717 := bbase (se 4 (by rfl) ⟨382473, by rfl⟩ : syracuseStep 4079717 = 764947) (by norm_num)
theorem B2416757 : Blo 1611004 2416757 := bbase (se 5 (by rfl) ⟨113285, by rfl⟩ : syracuseStep 2416757 = 226571) (by norm_num)
theorem B2416781 : Blo 1611004 2416781 := bbase (se 3 (by rfl) ⟨453146, by rfl⟩ : syracuseStep 2416781 = 906293) (by norm_num)
theorem B2719885 : Blo 1611004 2719885 := bbase (se 3 (by rfl) ⟨509978, by rfl⟩ : syracuseStep 2719885 = 1019957) (by norm_num)
theorem B3629213 : Blo 1611004 3629213 := bbase (se 3 (by rfl) ⟨680477, by rfl⟩ : syracuseStep 3629213 = 1360955) (by norm_num)
theorem B2416805 : Blo 1611004 2416805 := bbase (se 4 (by rfl) ⟨226575, by rfl⟩ : syracuseStep 2416805 = 453151) (by norm_num)
theorem B2416829 : Blo 1611004 2416829 := bbase (se 3 (by rfl) ⟨453155, by rfl⟩ : syracuseStep 2416829 = 906311) (by norm_num)
theorem B6119621 : Blo 1611004 6119621 := bbase (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) (by norm_num)
theorem B2040005 : Blo 1611004 2040005 := bbase (se 4 (by rfl) ⟨191250, by rfl⟩ : syracuseStep 2040005 = 382501) (by norm_num)
theorem B2416853 : Blo 1611004 2416853 := bbase (se 7 (by rfl) ⟨28322, by rfl⟩ : syracuseStep 2416853 = 56645) (by norm_num)
theorem B2719973 : Blo 1611004 2719973 := bbase (se 4 (by rfl) ⟨254997, by rfl⟩ : syracuseStep 2719973 = 509995) (by norm_num)
theorem B2416877 : Blo 1611004 2416877 := bbase (se 3 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 2416877 = 906329) (by norm_num)
theorem B3875053 : Blo 1611004 3875053 := bbase (se 3 (by rfl) ⟨726572, by rfl⟩ : syracuseStep 3875053 = 1453145) (by norm_num)
theorem B1745137 : Blo 1611004 1745137 := bbase (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) (by norm_num)
theorem B2040061 : Blo 1611004 2040061 := bbase (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) (by norm_num)
theorem B2294021 : Blo 1611004 2294021 := bbase (se 4 (by rfl) ⟨215064, by rfl⟩ : syracuseStep 2294021 = 430129) (by norm_num)
theorem B2416901 : Blo 1611004 2416901 := bbase (se 4 (by rfl) ⟨226584, by rfl⟩ : syracuseStep 2416901 = 453169) (by norm_num)
theorem B1720597 : Blo 1611004 1720597 := bbase (se 6 (by rfl) ⟨40326, by rfl⟩ : syracuseStep 1720597 = 80653) (by norm_num)
theorem B2416925 : Blo 1611004 2416925 := bbase (se 3 (by rfl) ⟨453173, by rfl⟩ : syracuseStep 2416925 = 906347) (by norm_num)
theorem B4079909 : Blo 1611004 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B2416949 : Blo 1611004 2416949 := bbase (se 5 (by rfl) ⟨113294, by rfl⟩ : syracuseStep 2416949 = 226589) (by norm_num)
theorem B5439797 : Blo 1611004 5439797 := bbase (se 5 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 5439797 = 509981) (by norm_num)
theorem B2416973 : Blo 1611004 2416973 := bbase (se 3 (by rfl) ⟨453182, by rfl⟩ : syracuseStep 2416973 = 906365) (by norm_num)
theorem B39739733 : Blo 1611004 39739733 := bbase (se 10 (by rfl) ⟨58212, by rfl⟩ : syracuseStep 39739733 = 116425) (by norm_num)
theorem B2040157 : Blo 1611004 2040157 := bbase (se 3 (by rfl) ⟨382529, by rfl⟩ : syracuseStep 2040157 = 765059) (by norm_num)
theorem B2416997 : Blo 1611004 2416997 := bbase (se 4 (by rfl) ⟨226593, by rfl⟩ : syracuseStep 2416997 = 453187) (by norm_num)
theorem B5808485 : Blo 1611004 5808485 := bbase (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) (by norm_num)
theorem B2720101 : Blo 1611004 2720101 := bbase (se 4 (by rfl) ⟨255009, by rfl⟩ : syracuseStep 2720101 = 510019) (by norm_num)
theorem B2417021 : Blo 1611004 2417021 := bbase (se 3 (by rfl) ⟨453191, by rfl⟩ : syracuseStep 2417021 = 906383) (by norm_num)
theorem B6881669 : Blo 1611004 6881669 := bbase (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) (by norm_num)
theorem B1720721 : Blo 1611004 1720721 := bbase (se 2 (by rfl) ⟨645270, by rfl⟩ : syracuseStep 1720721 = 1290541) (by norm_num)
theorem B2417045 : Blo 1611004 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B4358549 : Blo 1611004 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B2417069 : Blo 1611004 2417069 := bbase (se 3 (by rfl) ⟨453200, by rfl⟩ : syracuseStep 2417069 = 906401) (by norm_num)
theorem B2720189 : Blo 1611004 2720189 := bbase (se 3 (by rfl) ⟨510035, by rfl⟩ : syracuseStep 2720189 = 1020071) (by norm_num)
theorem B2417093 : Blo 1611004 2417093 := bbase (se 4 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 2417093 = 453205) (by norm_num)
theorem B2417117 : Blo 1611004 2417117 := bbase (se 3 (by rfl) ⟨453209, by rfl⟩ : syracuseStep 2417117 = 906419) (by norm_num)
theorem B2417141 : Blo 1611004 2417141 := bbase (se 5 (by rfl) ⟨113303, by rfl⟩ : syracuseStep 2417141 = 226607) (by norm_num)
theorem B2040329 : Blo 1611004 2040329 := bbase (se 2 (by rfl) ⟨765123, by rfl⟩ : syracuseStep 2040329 = 1530247) (by norm_num)
theorem B2417165 : Blo 1611004 2417165 := bbase (se 3 (by rfl) ⟨453218, by rfl⟩ : syracuseStep 2417165 = 906437) (by norm_num)
theorem B15483413 : Blo 1611004 15483413 := bbase (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) (by norm_num)
theorem B3678749 : Blo 1611004 3678749 := bbase (se 3 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 3678749 = 1379531) (by norm_num)
theorem B2417189 : Blo 1611004 2417189 := bbase (se 4 (by rfl) ⟨226611, by rfl⟩ : syracuseStep 2417189 = 453223) (by norm_num)
theorem B2417213 : Blo 1611004 2417213 := bbase (se 3 (by rfl) ⟨453227, by rfl⟩ : syracuseStep 2417213 = 906455) (by norm_num)
theorem B2720317 : Blo 1611004 2720317 := bbase (se 3 (by rfl) ⟨510059, by rfl⟩ : syracuseStep 2720317 = 1020119) (by norm_num)
theorem B2040385 : Blo 1611004 2040385 := bbase (se 2 (by rfl) ⟨765144, by rfl⟩ : syracuseStep 2040385 = 1530289) (by norm_num)
theorem B2417237 : Blo 1611004 2417237 := bbase (se 8 (by rfl) ⟨14163, by rfl⟩ : syracuseStep 2417237 = 28327) (by norm_num)
theorem B2417261 : Blo 1611004 2417261 := bbase (se 3 (by rfl) ⟨453236, by rfl⟩ : syracuseStep 2417261 = 906473) (by norm_num)
theorem B4080253 : Blo 1611004 4080253 := bbase (se 3 (by rfl) ⟨765047, by rfl⟩ : syracuseStep 4080253 = 1530095) (by norm_num)
theorem B2417285 : Blo 1611004 2417285 := bbase (se 4 (by rfl) ⟨226620, by rfl⟩ : syracuseStep 2417285 = 453241) (by norm_num)
theorem B1720973 : Blo 1611004 1720973 := bbase (se 3 (by rfl) ⟨322682, by rfl⟩ : syracuseStep 1720973 = 645365) (by norm_num)
theorem B2720405 : Blo 1611004 2720405 := bbase (se 6 (by rfl) ⟨63759, by rfl⟩ : syracuseStep 2720405 = 127519) (by norm_num)
theorem B2417309 : Blo 1611004 2417309 := bbase (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) (by norm_num)
theorem B2040481 : Blo 1611004 2040481 := bbase (se 2 (by rfl) ⟨765180, by rfl⟩ : syracuseStep 2040481 = 1530361) (by norm_num)
theorem B2417333 : Blo 1611004 2417333 := bbase (se 5 (by rfl) ⟨113312, by rfl⟩ : syracuseStep 2417333 = 226625) (by norm_num)
theorem B2417357 : Blo 1611004 2417357 := bbase (se 3 (by rfl) ⟨453254, by rfl⟩ : syracuseStep 2417357 = 906509) (by norm_num)
theorem B2417381 : Blo 1611004 2417381 := bbase (se 4 (by rfl) ⟨226629, by rfl⟩ : syracuseStep 2417381 = 453259) (by norm_num)
theorem B5440229 : Blo 1611004 5440229 := bbase (se 4 (by rfl) ⟨510021, by rfl⟩ : syracuseStep 5440229 = 1020043) (by norm_num)
theorem B4080365 : Blo 1611004 4080365 := bbase (se 3 (by rfl) ⟨765068, by rfl⟩ : syracuseStep 4080365 = 1530137) (by norm_num)
theorem B2417405 : Blo 1611004 2417405 := bbase (se 3 (by rfl) ⟨453263, by rfl⟩ : syracuseStep 2417405 = 906527) (by norm_num)
theorem B2417429 : Blo 1611004 2417429 := bbase (se 6 (by rfl) ⟨56658, by rfl⟩ : syracuseStep 2417429 = 113317) (by norm_num)
theorem B2720533 : Blo 1611004 2720533 := bbase (se 6 (by rfl) ⟨63762, by rfl⟩ : syracuseStep 2720533 = 127525) (by norm_num)
theorem B5161765 : Blo 1611004 5161765 := bbase (se 4 (by rfl) ⟨483915, by rfl⟩ : syracuseStep 5161765 = 967831) (by norm_num)
theorem B2294573 : Blo 1611004 2294573 := bbase (se 3 (by rfl) ⟨430232, by rfl⟩ : syracuseStep 2294573 = 860465) (by norm_num)
theorem B2417453 : Blo 1611004 2417453 := bbase (se 3 (by rfl) ⟨453272, by rfl⟩ : syracuseStep 2417453 = 906545) (by norm_num)
theorem B2417477 : Blo 1611004 2417477 := bbase (se 4 (by rfl) ⟨226638, by rfl⟩ : syracuseStep 2417477 = 453277) (by norm_num)
theorem B2040653 : Blo 1611004 2040653 := bbase (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) (by norm_num)
theorem B2417501 : Blo 1611004 2417501 := bbase (se 3 (by rfl) ⟨453281, by rfl⟩ : syracuseStep 2417501 = 906563) (by norm_num)
theorem B8160101 : Blo 1611004 8160101 := bbase (se 4 (by rfl) ⟨765009, by rfl⟩ : syracuseStep 8160101 = 1530019) (by norm_num)
theorem B2720621 : Blo 1611004 2720621 := bbase (se 3 (by rfl) ⟨510116, by rfl⟩ : syracuseStep 2720621 = 1020233) (by norm_num)
theorem B2417525 : Blo 1611004 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B2040709 : Blo 1611004 2040709 := bbase (se 4 (by rfl) ⟨191316, by rfl⟩ : syracuseStep 2040709 = 382633) (by norm_num)
theorem B2417549 : Blo 1611004 2417549 := bbase (se 3 (by rfl) ⟨453290, by rfl⟩ : syracuseStep 2417549 = 906581) (by norm_num)
theorem B2417573 : Blo 1611004 2417573 := bbase (se 4 (by rfl) ⟨226647, by rfl⟩ : syracuseStep 2417573 = 453295) (by norm_num)
theorem B4080557 : Blo 1611004 4080557 := bbase (se 3 (by rfl) ⟨765104, by rfl⟩ : syracuseStep 4080557 = 1530209) (by norm_num)
theorem B2417597 : Blo 1611004 2417597 := bbase (se 3 (by rfl) ⟨453299, by rfl⟩ : syracuseStep 2417597 = 906599) (by norm_num)
theorem B2417621 : Blo 1611004 2417621 := bbase (se 7 (by rfl) ⟨28331, by rfl⟩ : syracuseStep 2417621 = 56663) (by norm_num)
theorem B2040805 : Blo 1611004 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B2417645 : Blo 1611004 2417645 := bbase (se 3 (by rfl) ⟨453308, by rfl⟩ : syracuseStep 2417645 = 906617) (by norm_num)
theorem B2720749 : Blo 1611004 2720749 := bbase (se 3 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 2720749 = 1020281) (by norm_num)
theorem B2417669 : Blo 1611004 2417669 := bbase (se 4 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 2417669 = 453313) (by norm_num)
theorem B2417693 : Blo 1611004 2417693 := bbase (se 3 (by rfl) ⟨453317, by rfl⟩ : syracuseStep 2417693 = 906635) (by norm_num)
theorem B3310637 : Blo 1611004 3310637 := bbase (se 3 (by rfl) ⟨620744, by rfl⟩ : syracuseStep 3310637 = 1241489) (by norm_num)
theorem B7070773 : Blo 1611004 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B2417717 : Blo 1611004 2417717 := bbase (se 5 (by rfl) ⟨113330, by rfl⟩ : syracuseStep 2417717 = 226661) (by norm_num)
theorem B2720837 : Blo 1611004 2720837 := bbase (se 4 (by rfl) ⟨255078, by rfl⟩ : syracuseStep 2720837 = 510157) (by norm_num)
theorem B1721417 : Blo 1611004 1721417 := bbase (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) (by norm_num)
theorem B2417741 : Blo 1611004 2417741 := bbase (se 3 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 2417741 = 906653) (by norm_num)
theorem B4588645 : Blo 1611004 4588645 := bbase (se 4 (by rfl) ⟨430185, by rfl⟩ : syracuseStep 4588645 = 860371) (by norm_num)
theorem B2417765 : Blo 1611004 2417765 := bbase (se 4 (by rfl) ⟨226665, by rfl⟩ : syracuseStep 2417765 = 453331) (by norm_num)
theorem B6882421 : Blo 1611004 6882421 := bbase (se 5 (by rfl) ⟨322613, by rfl⟩ : syracuseStep 6882421 = 645227) (by norm_num)
theorem B2417789 : Blo 1611004 2417789 := bbase (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) (by norm_num)
theorem B2040977 : Blo 1611004 2040977 := bbase (se 2 (by rfl) ⟨765366, by rfl⟩ : syracuseStep 2040977 = 1530733) (by norm_num)
theorem B2417813 : Blo 1611004 2417813 := bbase (se 6 (by rfl) ⟨56667, by rfl⟩ : syracuseStep 2417813 = 113335) (by norm_num)
theorem B5440661 : Blo 1611004 5440661 := bbase (se 6 (by rfl) ⟨127515, by rfl⟩ : syracuseStep 5440661 = 255031) (by norm_num)
theorem B2417837 : Blo 1611004 2417837 := bbase (se 3 (by rfl) ⟨453344, by rfl⟩ : syracuseStep 2417837 = 906689) (by norm_num)
theorem B2417861 : Blo 1611004 2417861 := bbase (se 4 (by rfl) ⟨226674, by rfl⟩ : syracuseStep 2417861 = 453349) (by norm_num)
theorem B2720965 : Blo 1611004 2720965 := bbase (se 4 (by rfl) ⟨255090, by rfl⟩ : syracuseStep 2720965 = 510181) (by norm_num)
theorem B2041033 : Blo 1611004 2041033 := bbase (se 2 (by rfl) ⟨765387, by rfl⟩ : syracuseStep 2041033 = 1530775) (by norm_num)
theorem B2417885 : Blo 1611004 2417885 := bbase (se 3 (by rfl) ⟨453353, by rfl⟩ : syracuseStep 2417885 = 906707) (by norm_num)
theorem B2417909 : Blo 1611004 2417909 := bbase (se 5 (by rfl) ⟨113339, by rfl⟩ : syracuseStep 2417909 = 226679) (by norm_num)
theorem B4588805 : Blo 1611004 4588805 := bbase (se 4 (by rfl) ⟨430200, by rfl⟩ : syracuseStep 4588805 = 860401) (by norm_num)
theorem B2450693 : Blo 1611004 2450693 := bbase (se 4 (by rfl) ⟨229752, by rfl⟩ : syracuseStep 2450693 = 459505) (by norm_num)
theorem B4080901 : Blo 1611004 4080901 := bbase (se 4 (by rfl) ⟨382584, by rfl⟩ : syracuseStep 4080901 = 765169) (by norm_num)
theorem B2417933 : Blo 1611004 2417933 := bbase (se 3 (by rfl) ⟨453362, by rfl⟩ : syracuseStep 2417933 = 906725) (by norm_num)
theorem B2721053 : Blo 1611004 2721053 := bbase (se 3 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 2721053 = 1020395) (by norm_num)
theorem B2417957 : Blo 1611004 2417957 := bbase (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) (by norm_num)
theorem B2041129 : Blo 1611004 2041129 := bbase (se 2 (by rfl) ⟨765423, by rfl⟩ : syracuseStep 2041129 = 1530847) (by norm_num)
theorem B2581805 : Blo 1611004 2581805 := bbase (se 3 (by rfl) ⟨484088, by rfl⟩ : syracuseStep 2581805 = 968177) (by norm_num)
theorem B3269933 : Blo 1611004 3269933 := bbase (se 3 (by rfl) ⟨613112, by rfl⟩ : syracuseStep 3269933 = 1226225) (by norm_num)
theorem B2417981 : Blo 1611004 2417981 := bbase (se 3 (by rfl) ⟨453371, by rfl⟩ : syracuseStep 2417981 = 906743) (by norm_num)
theorem B1721665 : Blo 1611004 1721665 := bbase (se 2 (by rfl) ⟨645624, by rfl⟩ : syracuseStep 1721665 = 1291249) (by norm_num)
theorem B3441989 : Blo 1611004 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B2418005 : Blo 1611004 2418005 := bbase (se 12 (by rfl) ⟨885, by rfl⟩ : syracuseStep 2418005 = 1771) (by norm_num)
theorem B6120805 : Blo 1611004 6120805 := bbase (se 4 (by rfl) ⟨573825, by rfl⟩ : syracuseStep 6120805 = 1147651) (by norm_num)
theorem B2418029 : Blo 1611004 2418029 := bbase (se 3 (by rfl) ⟨453380, by rfl⟩ : syracuseStep 2418029 = 906761) (by norm_num)
theorem B4081013 : Blo 1611004 4081013 := bbase (se 5 (by rfl) ⟨191297, by rfl⟩ : syracuseStep 4081013 = 382595) (by norm_num)
theorem B4900229 : Blo 1611004 4900229 := bbase (se 4 (by rfl) ⟨459396, by rfl⟩ : syracuseStep 4900229 = 918793) (by norm_num)
theorem B2418053 : Blo 1611004 2418053 := bbase (se 4 (by rfl) ⟨226692, by rfl⟩ : syracuseStep 2418053 = 453385) (by norm_num)
theorem B2418077 : Blo 1611004 2418077 := bbase (se 3 (by rfl) ⟨453389, by rfl⟩ : syracuseStep 2418077 = 906779) (by norm_num)
theorem B2721181 : Blo 1611004 2721181 := bbase (se 3 (by rfl) ⟨510221, by rfl⟩ : syracuseStep 2721181 = 1020443) (by norm_num)
theorem B9799093 : Blo 1611004 9799093 := bbase (se 5 (by rfl) ⟨459332, by rfl⟩ : syracuseStep 9799093 = 918665) (by norm_num)
theorem B2418101 : Blo 1611004 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B2418125 : Blo 1611004 2418125 := bbase (se 3 (by rfl) ⟨453398, by rfl⟩ : syracuseStep 2418125 = 906797) (by norm_num)
theorem B3442133 : Blo 1611004 3442133 := bbase (se 7 (by rfl) ⟨40337, by rfl⟩ : syracuseStep 3442133 = 80675) (by norm_num)
theorem B2041301 : Blo 1611004 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B2418149 : Blo 1611004 2418149 := bbase (se 4 (by rfl) ⟨226701, by rfl⟩ : syracuseStep 2418149 = 453403) (by norm_num)
theorem B4359653 : Blo 1611004 4359653 := bbase (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) (by norm_num)
theorem B4589045 : Blo 1611004 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B2721269 : Blo 1611004 2721269 := bbase (se 5 (by rfl) ⟨127559, by rfl⟩ : syracuseStep 2721269 = 255119) (by norm_num)
theorem B2418173 : Blo 1611004 2418173 := bbase (se 3 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 2418173 = 906815) (by norm_num)
theorem B2041357 : Blo 1611004 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B2418197 : Blo 1611004 2418197 := bbase (se 6 (by rfl) ⟨56676, by rfl⟩ : syracuseStep 2418197 = 113353) (by norm_num)
theorem B2295325 : Blo 1611004 2295325 := bbase (se 3 (by rfl) ⟨430373, by rfl⟩ : syracuseStep 2295325 = 860747) (by norm_num)
theorem B2418221 : Blo 1611004 2418221 := bbase (se 3 (by rfl) ⟨453416, by rfl⟩ : syracuseStep 2418221 = 906833) (by norm_num)
theorem B4081205 : Blo 1611004 4081205 := bbase (se 5 (by rfl) ⟨191306, by rfl⟩ : syracuseStep 4081205 = 382613) (by norm_num)
theorem B2418245 : Blo 1611004 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B5441093 : Blo 1611004 5441093 := bbase (se 4 (by rfl) ⟨510102, by rfl⟩ : syracuseStep 5441093 = 1020205) (by norm_num)
theorem B9184853 : Blo 1611004 9184853 := bbase (se 8 (by rfl) ⟨53817, by rfl⟩ : syracuseStep 9184853 = 107635) (by norm_num)
theorem B2418269 : Blo 1611004 2418269 := bbase (se 3 (by rfl) ⟨453425, by rfl⟩ : syracuseStep 2418269 = 906851) (by norm_num)
theorem B4359781 : Blo 1611004 4359781 := bbase (se 4 (by rfl) ⟨408729, by rfl⟩ : syracuseStep 4359781 = 817459) (by norm_num)
theorem B2041453 : Blo 1611004 2041453 := bbase (se 3 (by rfl) ⟨382772, by rfl⟩ : syracuseStep 2041453 = 765545) (by norm_num)
theorem B2418293 : Blo 1611004 2418293 := bbase (se 5 (by rfl) ⟨113357, by rfl⟩ : syracuseStep 2418293 = 226715) (by norm_num)
theorem B2721397 : Blo 1611004 2721397 := bbase (se 5 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 2721397 = 255131) (by norm_num)
theorem B2418317 : Blo 1611004 2418317 := bbase (se 3 (by rfl) ⟨453434, by rfl⟩ : syracuseStep 2418317 = 906869) (by norm_num)
theorem B6121109 : Blo 1611004 6121109 := bbase (se 6 (by rfl) ⟨143463, by rfl⟩ : syracuseStep 6121109 = 286927) (by norm_num)
theorem B2418341 : Blo 1611004 2418341 := bbase (se 4 (by rfl) ⟨226719, by rfl⟩ : syracuseStep 2418341 = 453439) (by norm_num)
theorem B4589237 : Blo 1611004 4589237 := bbase (se 5 (by rfl) ⟨215120, by rfl⟩ : syracuseStep 4589237 = 430241) (by norm_num)
theorem B2418365 : Blo 1611004 2418365 := bbase (se 3 (by rfl) ⟨453443, by rfl⟩ : syracuseStep 2418365 = 906887) (by norm_num)
theorem B2721485 : Blo 1611004 2721485 := bbase (se 3 (by rfl) ⟨510278, by rfl⟩ : syracuseStep 2721485 = 1020557) (by norm_num)
theorem B2418389 : Blo 1611004 2418389 := bbase (se 7 (by rfl) ⟨28340, by rfl⟩ : syracuseStep 2418389 = 56681) (by norm_num)
theorem B2418413 : Blo 1611004 2418413 := bbase (se 3 (by rfl) ⟨453452, by rfl⟩ : syracuseStep 2418413 = 906905) (by norm_num)
theorem B1722109 : Blo 1611004 1722109 := bbase (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) (by norm_num)
theorem B2418437 : Blo 1611004 2418437 := bbase (se 4 (by rfl) ⟨226728, by rfl⟩ : syracuseStep 2418437 = 453457) (by norm_num)
theorem B2418461 : Blo 1611004 2418461 := bbase (se 3 (by rfl) ⟨453461, by rfl⟩ : syracuseStep 2418461 = 906923) (by norm_num)
theorem B2418485 : Blo 1611004 2418485 := bbase (se 5 (by rfl) ⟨113366, by rfl⟩ : syracuseStep 2418485 = 226733) (by norm_num)
theorem B1722169 : Blo 1611004 1722169 := bbase (se 2 (by rfl) ⟨645813, by rfl⟩ : syracuseStep 1722169 = 1291627) (by norm_num)
theorem B3442493 : Blo 1611004 3442493 := bbase (se 3 (by rfl) ⟨645467, by rfl⟩ : syracuseStep 3442493 = 1290935) (by norm_num)
theorem B2418509 : Blo 1611004 2418509 := bbase (se 3 (by rfl) ⟨453470, by rfl⟩ : syracuseStep 2418509 = 906941) (by norm_num)
theorem B2721613 : Blo 1611004 2721613 := bbase (se 3 (by rfl) ⟨510302, by rfl⟩ : syracuseStep 2721613 = 1020605) (by norm_num)
theorem B6883157 : Blo 1611004 6883157 := bbase (se 9 (by rfl) ⟨20165, by rfl⟩ : syracuseStep 6883157 = 40331) (by norm_num)
theorem B2418533 : Blo 1611004 2418533 := bbase (se 4 (by rfl) ⟨226737, by rfl⟩ : syracuseStep 2418533 = 453475) (by norm_num)
theorem B2418557 : Blo 1611004 2418557 := bbase (se 3 (by rfl) ⟨453479, by rfl⟩ : syracuseStep 2418557 = 906959) (by norm_num)
theorem B4081549 : Blo 1611004 4081549 := bbase (se 3 (by rfl) ⟨765290, by rfl⟩ : syracuseStep 4081549 = 1530581) (by norm_num)
theorem B2418581 : Blo 1611004 2418581 := bbase (se 6 (by rfl) ⟨56685, by rfl⟩ : syracuseStep 2418581 = 113371) (by norm_num)
theorem B2721701 : Blo 1611004 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B1812397 : Blo 1611004 1812397 := bbase (se 3 (by rfl) ⟨339824, by rfl⟩ : syracuseStep 1812397 = 679649) (by norm_num)
theorem B2418605 : Blo 1611004 2418605 := bbase (se 3 (by rfl) ⟨453488, by rfl⟩ : syracuseStep 2418605 = 906977) (by norm_num)
theorem B2418629 : Blo 1611004 2418629 := bbase (se 4 (by rfl) ⟨226746, by rfl⟩ : syracuseStep 2418629 = 453493) (by norm_num)
theorem B1812433 : Blo 1611004 1812433 := bbase (se 2 (by rfl) ⟨679662, by rfl⟩ : syracuseStep 1812433 = 1359325) (by norm_num)
theorem B20662229 : Blo 1611004 20662229 := bbase (se 7 (by rfl) ⟨242135, by rfl⟩ : syracuseStep 20662229 = 484271) (by norm_num)
theorem B2418653 : Blo 1611004 2418653 := bbase (se 3 (by rfl) ⟨453497, by rfl⟩ : syracuseStep 2418653 = 906995) (by norm_num)
theorem B4900837 : Blo 1611004 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B1812469 : Blo 1611004 1812469 := bbase (se 5 (by rfl) ⟨84959, by rfl⟩ : syracuseStep 1812469 = 169919) (by norm_num)
theorem B5441525 : Blo 1611004 5441525 := bbase (se 5 (by rfl) ⟨255071, by rfl⟩ : syracuseStep 5441525 = 510143) (by norm_num)
theorem B2418677 : Blo 1611004 2418677 := bbase (se 5 (by rfl) ⟨113375, by rfl⟩ : syracuseStep 2418677 = 226751) (by norm_num)
theorem B7661557 : Blo 1611004 7661557 := bbase (se 5 (by rfl) ⟨359135, by rfl⟩ : syracuseStep 7661557 = 718271) (by norm_num)
theorem B4081661 : Blo 1611004 4081661 := bbase (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) (by norm_num)
theorem B2418701 : Blo 1611004 2418701 := bbase (se 3 (by rfl) ⟨453506, by rfl⟩ : syracuseStep 2418701 = 907013) (by norm_num)
theorem B1812505 : Blo 1611004 1812505 := bbase (se 2 (by rfl) ⟨679689, by rfl⟩ : syracuseStep 1812505 = 1359379) (by norm_num)
theorem B2418725 : Blo 1611004 2418725 := bbase (se 4 (by rfl) ⟨226755, by rfl⟩ : syracuseStep 2418725 = 453511) (by norm_num)
theorem B2721829 : Blo 1611004 2721829 := bbase (se 4 (by rfl) ⟨255171, by rfl⟩ : syracuseStep 2721829 = 510343) (by norm_num)
theorem B15501365 : Blo 1611004 15501365 := bbase (se 5 (by rfl) ⟨726626, by rfl⟩ : syracuseStep 15501365 = 1453253) (by norm_num)
theorem B1812541 : Blo 1611004 1812541 := bbase (se 3 (by rfl) ⟨339851, by rfl⟩ : syracuseStep 1812541 = 679703) (by norm_num)
theorem B2418749 : Blo 1611004 2418749 := bbase (se 3 (by rfl) ⟨453515, by rfl⟩ : syracuseStep 2418749 = 907031) (by norm_num)
theorem B2418773 : Blo 1611004 2418773 := bbase (se 8 (by rfl) ⟨14172, by rfl⟩ : syracuseStep 2418773 = 28345) (by norm_num)
theorem B1812577 : Blo 1611004 1812577 := bbase (se 2 (by rfl) ⟨679716, by rfl⟩ : syracuseStep 1812577 = 1359433) (by norm_num)
theorem B2418797 : Blo 1611004 2418797 := bbase (se 3 (by rfl) ⟨453524, by rfl⟩ : syracuseStep 2418797 = 907049) (by norm_num)
theorem B8161397 : Blo 1611004 8161397 := bbase (se 5 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 8161397 = 765131) (by norm_num)
theorem B2721917 : Blo 1611004 2721917 := bbase (se 3 (by rfl) ⟨510359, by rfl⟩ : syracuseStep 2721917 = 1020719) (by norm_num)
theorem B1812613 : Blo 1611004 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B2418821 : Blo 1611004 2418821 := bbase (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) (by norm_num)
theorem B6637717 : Blo 1611004 6637717 := bbase (se 6 (by rfl) ⟨155571, by rfl⟩ : syracuseStep 6637717 = 311143) (by norm_num)
theorem B2418845 : Blo 1611004 2418845 := bbase (se 3 (by rfl) ⟨453533, by rfl⟩ : syracuseStep 2418845 = 907067) (by norm_num)
theorem B1812649 : Blo 1611004 1812649 := bbase (se 2 (by rfl) ⟨679743, by rfl⟩ : syracuseStep 1812649 = 1359487) (by norm_num)
theorem B2418869 : Blo 1611004 2418869 := bbase (se 5 (by rfl) ⟨113384, by rfl⟩ : syracuseStep 2418869 = 226769) (by norm_num)
theorem B4081853 : Blo 1611004 4081853 := bbase (se 3 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 4081853 = 1530695) (by norm_num)
theorem B1812685 : Blo 1611004 1812685 := bbase (se 3 (by rfl) ⟨339878, by rfl⟩ : syracuseStep 1812685 = 679757) (by norm_num)
theorem B2418893 : Blo 1611004 2418893 := bbase (se 3 (by rfl) ⟨453542, by rfl⟩ : syracuseStep 2418893 = 907085) (by norm_num)
theorem B2582741 : Blo 1611004 2582741 := bbase (se 7 (by rfl) ⟨30266, by rfl⟩ : syracuseStep 2582741 = 60533) (by norm_num)
theorem B2418917 : Blo 1611004 2418917 := bbase (se 4 (by rfl) ⟨226773, by rfl⟩ : syracuseStep 2418917 = 453547) (by norm_num)
theorem B1812721 : Blo 1611004 1812721 := bbase (se 2 (by rfl) ⟨679770, by rfl⟩ : syracuseStep 1812721 = 1359541) (by norm_num)
theorem B2418941 : Blo 1611004 2418941 := bbase (se 3 (by rfl) ⟨453551, by rfl⟩ : syracuseStep 2418941 = 907103) (by norm_num)
theorem B1812757 : Blo 1611004 1812757 := bbase (se 6 (by rfl) ⟨42486, by rfl⟩ : syracuseStep 1812757 = 84973) (by norm_num)
theorem B2418965 : Blo 1611004 2418965 := bbase (se 6 (by rfl) ⟨56694, by rfl⟩ : syracuseStep 2418965 = 113389) (by norm_num)
theorem B2418989 : Blo 1611004 2418989 := bbase (se 3 (by rfl) ⟨453560, by rfl⟩ : syracuseStep 2418989 = 907121) (by norm_num)
theorem B2296117 : Blo 1611004 2296117 := bbase (se 5 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 2296117 = 215261) (by norm_num)
theorem B1812793 : Blo 1611004 1812793 := bbase (se 2 (by rfl) ⟨679797, by rfl⟩ : syracuseStep 1812793 = 1359595) (by norm_num)
theorem B2451781 : Blo 1611004 2451781 := bbase (se 4 (by rfl) ⟨229854, by rfl⟩ : syracuseStep 2451781 = 459709) (by norm_num)
theorem B2419013 : Blo 1611004 2419013 := bbase (se 4 (by rfl) ⟨226782, by rfl⟩ : syracuseStep 2419013 = 453565) (by norm_num)
theorem B1812829 : Blo 1611004 1812829 := bbase (se 3 (by rfl) ⟨339905, by rfl⟩ : syracuseStep 1812829 = 679811) (by norm_num)
theorem B2419037 : Blo 1611004 2419037 := bbase (se 3 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 2419037 = 907139) (by norm_num)
theorem B2419061 : Blo 1611004 2419061 := bbase (se 5 (by rfl) ⟨113393, by rfl⟩ : syracuseStep 2419061 = 226787) (by norm_num)
theorem B1837441 : Blo 1611004 1837441 := bbase (se 2 (by rfl) ⟨689040, by rfl⟩ : syracuseStep 1837441 = 1378081) (by norm_num)
theorem B1812865 : Blo 1611004 1812865 := bbase (se 2 (by rfl) ⟨679824, by rfl⟩ : syracuseStep 1812865 = 1359649) (by norm_num)
theorem B2419085 : Blo 1611004 2419085 := bbase (se 3 (by rfl) ⟨453578, by rfl⟩ : syracuseStep 2419085 = 907157) (by norm_num)
theorem B1812901 : Blo 1611004 1812901 := bbase (se 4 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 1812901 = 339919) (by norm_num)
theorem B5441957 : Blo 1611004 5441957 := bbase (se 4 (by rfl) ⟨510183, by rfl⟩ : syracuseStep 5441957 = 1020367) (by norm_num)
theorem B2419109 : Blo 1611004 2419109 := bbase (se 4 (by rfl) ⟨226791, by rfl⟩ : syracuseStep 2419109 = 453583) (by norm_num)
theorem B2419133 : Blo 1611004 2419133 := bbase (se 3 (by rfl) ⟨453587, by rfl⟩ : syracuseStep 2419133 = 907175) (by norm_num)
theorem B1812937 : Blo 1611004 1812937 := bbase (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) (by norm_num)
theorem B2419157 : Blo 1611004 2419157 := bbase (se 7 (by rfl) ⟨28349, by rfl⟩ : syracuseStep 2419157 = 56699) (by norm_num)
theorem B1837549 : Blo 1611004 1837549 := bbase (se 3 (by rfl) ⟨344540, by rfl⟩ : syracuseStep 1837549 = 689081) (by norm_num)
theorem B1812973 : Blo 1611004 1812973 := bbase (se 3 (by rfl) ⟨339932, by rfl⟩ : syracuseStep 1812973 = 679865) (by norm_num)
theorem B2419181 : Blo 1611004 2419181 := bbase (se 3 (by rfl) ⟨453596, by rfl⟩ : syracuseStep 2419181 = 907193) (by norm_num)
theorem B2419205 : Blo 1611004 2419205 := bbase (se 4 (by rfl) ⟨226800, by rfl⟩ : syracuseStep 2419205 = 453601) (by norm_num)
theorem B1813009 : Blo 1611004 1813009 := bbase (se 2 (by rfl) ⟨679878, by rfl⟩ : syracuseStep 1813009 = 1359757) (by norm_num)
theorem B4082197 : Blo 1611004 4082197 := bbase (se 6 (by rfl) ⟨95676, by rfl⟩ : syracuseStep 4082197 = 191353) (by norm_num)
theorem B2419229 : Blo 1611004 2419229 := bbase (se 3 (by rfl) ⟨453605, by rfl⟩ : syracuseStep 2419229 = 907211) (by norm_num)
theorem B1813045 : Blo 1611004 1813045 := bbase (se 5 (by rfl) ⟨84986, by rfl⟩ : syracuseStep 1813045 = 169973) (by norm_num)
theorem B2419253 : Blo 1611004 2419253 := bbase (se 5 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 2419253 = 226805) (by norm_num)
theorem B2419277 : Blo 1611004 2419277 := bbase (se 3 (by rfl) ⟨453614, by rfl⟩ : syracuseStep 2419277 = 907229) (by norm_num)
theorem B1813081 : Blo 1611004 1813081 := bbase (se 2 (by rfl) ⟨679905, by rfl⟩ : syracuseStep 1813081 = 1359811) (by norm_num)
theorem B1837669 : Blo 1611004 1837669 := bbase (se 4 (by rfl) ⟨172281, by rfl⟩ : syracuseStep 1837669 = 344563) (by norm_num)
theorem B2419301 : Blo 1611004 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B1813117 : Blo 1611004 1813117 := bbase (se 3 (by rfl) ⟨339959, by rfl⟩ : syracuseStep 1813117 = 679919) (by norm_num)
theorem B2419325 : Blo 1611004 2419325 := bbase (se 3 (by rfl) ⟨453623, by rfl⟩ : syracuseStep 2419325 = 907247) (by norm_num)
theorem B4082309 : Blo 1611004 4082309 := bbase (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) (by norm_num)
theorem B2296453 : Blo 1611004 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B4590229 : Blo 1611004 4590229 := bbase (se 6 (by rfl) ⟨107583, by rfl⟩ : syracuseStep 4590229 = 215167) (by norm_num)
theorem B2419349 : Blo 1611004 2419349 := bbase (se 6 (by rfl) ⟨56703, by rfl⟩ : syracuseStep 2419349 = 113407) (by norm_num)
theorem B1813153 : Blo 1611004 1813153 := bbase (se 2 (by rfl) ⟨679932, by rfl⟩ : syracuseStep 1813153 = 1359865) (by norm_num)
theorem B2419373 : Blo 1611004 2419373 := bbase (se 3 (by rfl) ⟨453632, by rfl⟩ : syracuseStep 2419373 = 907265) (by norm_num)
theorem B3443381 : Blo 1611004 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B1813189 : Blo 1611004 1813189 := bbase (se 4 (by rfl) ⟨169986, by rfl⟩ : syracuseStep 1813189 = 339973) (by norm_num)
theorem B2419397 : Blo 1611004 2419397 := bbase (se 4 (by rfl) ⟨226818, by rfl⟩ : syracuseStep 2419397 = 453637) (by norm_num)
theorem B2419421 : Blo 1611004 2419421 := bbase (se 3 (by rfl) ⟨453641, by rfl⟩ : syracuseStep 2419421 = 907283) (by norm_num)
theorem B1813225 : Blo 1611004 1813225 := bbase (se 2 (by rfl) ⟨679959, by rfl⟩ : syracuseStep 1813225 = 1359919) (by norm_num)
theorem B2419445 : Blo 1611004 2419445 := bbase (se 5 (by rfl) ⟨113411, by rfl⟩ : syracuseStep 2419445 = 226823) (by norm_num)
theorem B1813261 : Blo 1611004 1813261 := bbase (se 3 (by rfl) ⟨339986, by rfl⟩ : syracuseStep 1813261 = 679973) (by norm_num)
theorem B2419469 : Blo 1611004 2419469 := bbase (se 3 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 2419469 = 907301) (by norm_num)
theorem B2419493 : Blo 1611004 2419493 := bbase (se 4 (by rfl) ⟨226827, by rfl⟩ : syracuseStep 2419493 = 453655) (by norm_num)
theorem B1813297 : Blo 1611004 1813297 := bbase (se 2 (by rfl) ⟨679986, by rfl⟩ : syracuseStep 1813297 = 1359973) (by norm_num)
theorem B4082501 : Blo 1611004 4082501 := bbase (se 4 (by rfl) ⟨382734, by rfl⟩ : syracuseStep 4082501 = 765469) (by norm_num)
theorem B1813333 : Blo 1611004 1813333 := bbase (se 9 (by rfl) ⟨5312, by rfl⟩ : syracuseStep 1813333 = 10625) (by norm_num)
theorem B5442389 : Blo 1611004 5442389 := bbase (se 9 (by rfl) ⟨15944, by rfl⟩ : syracuseStep 5442389 = 31889) (by norm_num)
theorem B2583389 : Blo 1611004 2583389 := bbase (se 3 (by rfl) ⟨484385, by rfl⟩ : syracuseStep 2583389 = 968771) (by norm_num)
theorem B1813369 : Blo 1611004 1813369 := bbase (se 2 (by rfl) ⟨680013, by rfl⟩ : syracuseStep 1813369 = 1360027) (by norm_num)
theorem B3058573 : Blo 1611004 3058573 := bbase (se 3 (by rfl) ⟨573482, by rfl⟩ : syracuseStep 3058573 = 1146965) (by norm_num)
theorem B1813405 : Blo 1611004 1813405 := bbase (se 3 (by rfl) ⟨340013, by rfl⟩ : syracuseStep 1813405 = 680027) (by norm_num)
theorem B3443629 : Blo 1611004 3443629 := bbase (se 3 (by rfl) ⟨645680, by rfl⟩ : syracuseStep 3443629 = 1291361) (by norm_num)
theorem B1813441 : Blo 1611004 1813441 := bbase (se 2 (by rfl) ⟨680040, by rfl⟩ : syracuseStep 1813441 = 1360081) (by norm_num)
theorem B2452445 : Blo 1611004 2452445 := bbase (se 3 (by rfl) ⟨459833, by rfl⟩ : syracuseStep 2452445 = 919667) (by norm_num)
theorem B1813477 : Blo 1611004 1813477 := bbase (se 4 (by rfl) ⟨170013, by rfl⟩ : syracuseStep 1813477 = 340027) (by norm_num)
theorem B1813513 : Blo 1611004 1813513 := bbase (se 2 (by rfl) ⟨680067, by rfl⟩ : syracuseStep 1813513 = 1360135) (by norm_num)
theorem B3058717 : Blo 1611004 3058717 := bbase (se 3 (by rfl) ⟨573509, by rfl⟩ : syracuseStep 3058717 = 1147019) (by norm_num)
theorem B1813549 : Blo 1611004 1813549 := bbase (se 3 (by rfl) ⟨340040, by rfl⟩ : syracuseStep 1813549 = 680081) (by norm_num)
theorem B8277061 : Blo 1611004 8277061 := bbase (se 4 (by rfl) ⟨775974, by rfl⟩ : syracuseStep 8277061 = 1551949) (by norm_num)
theorem B1813585 : Blo 1611004 1813585 := bbase (se 2 (by rfl) ⟨680094, by rfl⟩ : syracuseStep 1813585 = 1360189) (by norm_num)
theorem B1936469 : Blo 1611004 1936469 := bbase (se 8 (by rfl) ⟨11346, by rfl⟩ : syracuseStep 1936469 = 22693) (by norm_num)
theorem B1813621 : Blo 1611004 1813621 := bbase (se 5 (by rfl) ⟨85013, by rfl⟩ : syracuseStep 1813621 = 170027) (by norm_num)
theorem B1838225 : Blo 1611004 1838225 := bbase (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) (by norm_num)
theorem B1813657 : Blo 1611004 1813657 := bbase (se 2 (by rfl) ⟨680121, by rfl⟩ : syracuseStep 1813657 = 1360243) (by norm_num)
theorem B4082845 : Blo 1611004 4082845 := bbase (se 3 (by rfl) ⟨765533, by rfl⟩ : syracuseStep 4082845 = 1531067) (by norm_num)
theorem B1838261 : Blo 1611004 1838261 := bbase (se 5 (by rfl) ⟨86168, by rfl⟩ : syracuseStep 1838261 = 172337) (by norm_num)
theorem B3058877 : Blo 1611004 3058877 := bbase (se 3 (by rfl) ⟨573539, by rfl⟩ : syracuseStep 3058877 = 1147079) (by norm_num)
theorem B1813693 : Blo 1611004 1813693 := bbase (se 3 (by rfl) ⟨340067, by rfl⟩ : syracuseStep 1813693 = 680135) (by norm_num)
theorem B2985157 : Blo 1611004 2985157 := bbase (se 4 (by rfl) ⟨279858, by rfl⟩ : syracuseStep 2985157 = 559717) (by norm_num)
theorem B1936585 : Blo 1611004 1936585 := bbase (se 2 (by rfl) ⟨726219, by rfl⟩ : syracuseStep 1936585 = 1452439) (by norm_num)
theorem B1813729 : Blo 1611004 1813729 := bbase (se 2 (by rfl) ⟨680148, by rfl⟩ : syracuseStep 1813729 = 1360297) (by norm_num)
theorem B1813765 : Blo 1611004 1813765 := bbase (se 4 (by rfl) ⟨170040, by rfl⟩ : syracuseStep 1813765 = 340081) (by norm_num)
theorem B5442821 : Blo 1611004 5442821 := bbase (se 4 (by rfl) ⟨510264, by rfl⟩ : syracuseStep 5442821 = 1020529) (by norm_num)
theorem B1936657 : Blo 1611004 1936657 := bbase (se 2 (by rfl) ⟨726246, by rfl⟩ : syracuseStep 1936657 = 1452493) (by norm_num)
theorem B6532373 : Blo 1611004 6532373 := bbase (se 6 (by rfl) ⟨153102, by rfl⟩ : syracuseStep 6532373 = 306205) (by norm_num)
theorem B1813801 : Blo 1611004 1813801 := bbase (se 2 (by rfl) ⟨680175, by rfl⟩ : syracuseStep 1813801 = 1360351) (by norm_num)
theorem B9301301 : Blo 1611004 9301301 := bbase (se 5 (by rfl) ⟨435998, by rfl⟩ : syracuseStep 9301301 = 871997) (by norm_num)
theorem B3059021 : Blo 1611004 3059021 := bbase (se 3 (by rfl) ⟨573566, by rfl⟩ : syracuseStep 3059021 = 1147133) (by norm_num)
theorem B1813837 : Blo 1611004 1813837 := bbase (se 3 (by rfl) ⟨340094, by rfl⟩ : syracuseStep 1813837 = 680189) (by norm_num)
theorem B1813873 : Blo 1611004 1813873 := bbase (se 2 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 1813873 = 1360405) (by norm_num)
theorem B8162693 : Blo 1611004 8162693 := bbase (se 4 (by rfl) ⟨765252, by rfl⟩ : syracuseStep 8162693 = 1530505) (by norm_num)
theorem B1936777 : Blo 1611004 1936777 := bbase (se 2 (by rfl) ⟨726291, by rfl⟩ : syracuseStep 1936777 = 1452583) (by norm_num)
theorem B1813909 : Blo 1611004 1813909 := bbase (se 6 (by rfl) ⟨42513, by rfl⟩ : syracuseStep 1813909 = 85027) (by norm_num)
theorem B3444133 : Blo 1611004 3444133 := bbase (se 4 (by rfl) ⟨322887, by rfl⟩ : syracuseStep 3444133 = 645775) (by norm_num)
theorem B1813945 : Blo 1611004 1813945 := bbase (se 2 (by rfl) ⟨680229, by rfl⟩ : syracuseStep 1813945 = 1360459) (by norm_num)
theorem B1813981 : Blo 1611004 1813981 := bbase (se 3 (by rfl) ⟨340121, by rfl⟩ : syracuseStep 1813981 = 680243) (by norm_num)
theorem B1814017 : Blo 1611004 1814017 := bbase (se 2 (by rfl) ⟨680256, by rfl⟩ : syracuseStep 1814017 = 1360513) (by norm_num)
theorem B3403301 : Blo 1611004 3403301 := bbase (se 4 (by rfl) ⟨319059, by rfl⟩ : syracuseStep 3403301 = 638119) (by norm_num)
theorem B1814053 : Blo 1611004 1814053 := bbase (se 4 (by rfl) ⟨170067, by rfl⟩ : syracuseStep 1814053 = 340135) (by norm_num)
theorem B1814089 : Blo 1611004 1814089 := bbase (se 2 (by rfl) ⟨680283, by rfl⟩ : syracuseStep 1814089 = 1360567) (by norm_num)
theorem B10333781 : Blo 1611004 10333781 := bbase (se 8 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 10333781 = 121099) (by norm_num)
theorem B3059309 : Blo 1611004 3059309 := bbase (se 3 (by rfl) ⟨573620, by rfl⟩ : syracuseStep 3059309 = 1147241) (by norm_num)
theorem B1814125 : Blo 1611004 1814125 := bbase (se 3 (by rfl) ⟨340148, by rfl⟩ : syracuseStep 1814125 = 680297) (by norm_num)
theorem B5164661 : Blo 1611004 5164661 := bbase (se 5 (by rfl) ⟨242093, by rfl⟩ : syracuseStep 5164661 = 484187) (by norm_num)
theorem B1633937 : Blo 1611004 1633937 := bbase (se 2 (by rfl) ⟨612726, by rfl⟩ : syracuseStep 1633937 = 1225453) (by norm_num)
theorem B1814161 : Blo 1611004 1814161 := bbase (se 2 (by rfl) ⟨680310, by rfl⟩ : syracuseStep 1814161 = 1360621) (by norm_num)
theorem B1814197 : Blo 1611004 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B5443253 : Blo 1611004 5443253 := bbase (se 5 (by rfl) ⟨255152, by rfl⟩ : syracuseStep 5443253 = 510305) (by norm_num)
theorem B6123221 : Blo 1611004 6123221 := bbase (se 7 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 6123221 = 143513) (by norm_num)
theorem B1838809 : Blo 1611004 1838809 := bbase (se 2 (by rfl) ⟨689553, by rfl⟩ : syracuseStep 1838809 = 1379107) (by norm_num)
theorem B1814233 : Blo 1611004 1814233 := bbase (se 2 (by rfl) ⟨680337, by rfl⟩ : syracuseStep 1814233 = 1360675) (by norm_num)
theorem B4591333 : Blo 1611004 4591333 := bbase (se 4 (by rfl) ⟨430437, by rfl⟩ : syracuseStep 4591333 = 860875) (by norm_num)
theorem B1838845 : Blo 1611004 1838845 := bbase (se 3 (by rfl) ⟨344783, by rfl⟩ : syracuseStep 1838845 = 689567) (by norm_num)
theorem B1814269 : Blo 1611004 1814269 := bbase (se 3 (by rfl) ⟨340175, by rfl⟩ : syracuseStep 1814269 = 680351) (by norm_num)
theorem B3059461 : Blo 1611004 3059461 := bbase (se 4 (by rfl) ⟨286824, by rfl⟩ : syracuseStep 3059461 = 573649) (by norm_num)
theorem B1937161 : Blo 1611004 1937161 := bbase (se 2 (by rfl) ⟨726435, by rfl⟩ : syracuseStep 1937161 = 1452871) (by norm_num)
theorem B1814305 : Blo 1611004 1814305 := bbase (se 2 (by rfl) ⟨680364, by rfl⟩ : syracuseStep 1814305 = 1360729) (by norm_num)
theorem B1814341 : Blo 1611004 1814341 := bbase (se 4 (by rfl) ⟨170094, by rfl⟩ : syracuseStep 1814341 = 340189) (by norm_num)
theorem B1814377 : Blo 1611004 1814377 := bbase (se 2 (by rfl) ⟨680391, by rfl⟩ : syracuseStep 1814377 = 1360783) (by norm_num)
theorem B3624821 : Blo 1611004 3624821 := bbase (se 5 (by rfl) ⟨169913, by rfl⟩ : syracuseStep 3624821 = 339827) (by norm_num)
theorem B1634185 : Blo 1611004 1634185 := bbase (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) (by norm_num)
theorem B1814413 : Blo 1611004 1814413 := bbase (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) (by norm_num)
theorem B1814449 : Blo 1611004 1814449 := bbase (se 2 (by rfl) ⟨680418, by rfl⟩ : syracuseStep 1814449 = 1360837) (by norm_num)
theorem B3624893 : Blo 1611004 3624893 := bbase (se 3 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 3624893 = 1359335) (by norm_num)
theorem B1814485 : Blo 1611004 1814485 := bbase (se 7 (by rfl) ⟨21263, by rfl⟩ : syracuseStep 1814485 = 42527) (by norm_num)
theorem B1634285 : Blo 1611004 1634285 := bbase (se 3 (by rfl) ⟨306428, by rfl⟩ : syracuseStep 1634285 = 612857) (by norm_num)
theorem B6123509 : Blo 1611004 6123509 := bbase (se 5 (by rfl) ⟨287039, by rfl⟩ : syracuseStep 6123509 = 574079) (by norm_num)
theorem B1814521 : Blo 1611004 1814521 := bbase (se 2 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 1814521 = 1360891) (by norm_num)
theorem B3624965 : Blo 1611004 3624965 := bbase (se 4 (by rfl) ⟨339840, by rfl⟩ : syracuseStep 3624965 = 679681) (by norm_num)
theorem B1814557 : Blo 1611004 1814557 := bbase (se 3 (by rfl) ⟨340229, by rfl⟩ : syracuseStep 1814557 = 680459) (by norm_num)
theorem B3059765 : Blo 1611004 3059765 := bbase (se 5 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 3059765 = 286853) (by norm_num)
theorem B1814593 : Blo 1611004 1814593 := bbase (se 2 (by rfl) ⟨680472, by rfl⟩ : syracuseStep 1814593 = 1360945) (by norm_num)
theorem B3625037 : Blo 1611004 3625037 := bbase (se 3 (by rfl) ⟨679694, by rfl⟩ : syracuseStep 3625037 = 1359389) (by norm_num)
theorem B5443685 : Blo 1611004 5443685 := bbase (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) (by norm_num)
theorem B1814629 : Blo 1611004 1814629 := bbase (se 4 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 1814629 = 340243) (by norm_num)
theorem B3625109 : Blo 1611004 3625109 := bbase (se 6 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 3625109 = 169927) (by norm_num)
theorem B3625181 : Blo 1611004 3625181 := bbase (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) (by norm_num)
theorem B13775093 : Blo 1611004 13775093 := bbase (se 5 (by rfl) ⟨645707, by rfl⟩ : syracuseStep 13775093 = 1291415) (by norm_num)
theorem B3625253 : Blo 1611004 3625253 := bbase (se 4 (by rfl) ⟨339867, by rfl⟩ : syracuseStep 3625253 = 679735) (by norm_num)
theorem B9179477 : Blo 1611004 9179477 := bbase (se 10 (by rfl) ⟨13446, by rfl⟩ : syracuseStep 9179477 = 26893) (by norm_num)
theorem B7352677 : Blo 1611004 7352677 := bbase (se 4 (by rfl) ⟨689313, by rfl⟩ : syracuseStep 7352677 = 1378627) (by norm_num)
theorem B3625325 : Blo 1611004 3625325 := bbase (se 3 (by rfl) ⟨679748, by rfl⟩ : syracuseStep 3625325 = 1359497) (by norm_num)
theorem B3871093 : Blo 1611004 3871093 := bbase (se 5 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 3871093 = 362915) (by norm_num)
theorem B13767029 : Blo 1611004 13767029 := bbase (se 5 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 13767029 = 1290659) (by norm_num)
theorem B2068885 : Blo 1611004 2068885 := bbase (se 6 (by rfl) ⟨48489, by rfl⟩ : syracuseStep 2068885 = 96979) (by norm_num)
theorem B3625397 : Blo 1611004 3625397 := bbase (se 5 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 3625397 = 339881) (by norm_num)
theorem B3625469 : Blo 1611004 3625469 := bbase (se 3 (by rfl) ⟨679775, by rfl⟩ : syracuseStep 3625469 = 1359551) (by norm_num)
theorem B2904589 : Blo 1611004 2904589 := bbase (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) (by norm_num)
theorem B1634833 : Blo 1611004 1634833 := bbase (se 2 (by rfl) ⟨613062, by rfl⟩ : syracuseStep 1634833 = 1226125) (by norm_num)
theorem B3625541 : Blo 1611004 3625541 := bbase (se 4 (by rfl) ⟨339894, by rfl⟩ : syracuseStep 3625541 = 679789) (by norm_num)
theorem B16536149 : Blo 1611004 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B2904661 : Blo 1611004 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B9433685 : Blo 1611004 9433685 := bbase (se 8 (by rfl) ⟨55275, by rfl⟩ : syracuseStep 9433685 = 110551) (by norm_num)
theorem B3625613 : Blo 1611004 3625613 := bbase (se 3 (by rfl) ⟨679802, by rfl⟩ : syracuseStep 3625613 = 1359605) (by norm_num)
theorem B8163989 : Blo 1611004 8163989 := bbase (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) (by norm_num)
theorem B3625685 : Blo 1611004 3625685 := bbase (se 7 (by rfl) ⟨42488, by rfl⟩ : syracuseStep 3625685 = 84977) (by norm_num)
theorem B6206165 : Blo 1611004 6206165 := bbase (se 7 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 6206165 = 145457) (by norm_num)
theorem B3871469 : Blo 1611004 3871469 := bbase (se 3 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 3871469 = 1451801) (by norm_num)
theorem B3625757 : Blo 1611004 3625757 := bbase (se 3 (by rfl) ⟨679829, by rfl⟩ : syracuseStep 3625757 = 1359659) (by norm_num)
theorem B2757413 : Blo 1611004 2757413 := bbase (se 4 (by rfl) ⟨258507, by rfl⟩ : syracuseStep 2757413 = 517015) (by norm_num)
theorem B3060517 : Blo 1611004 3060517 := bbase (se 4 (by rfl) ⟨286923, by rfl⟩ : syracuseStep 3060517 = 573847) (by norm_num)
theorem B4903733 : Blo 1611004 4903733 := bbase (se 5 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 4903733 = 459725) (by norm_num)
theorem B12243797 : Blo 1611004 12243797 := bbase (se 9 (by rfl) ⟨35870, by rfl⟩ : syracuseStep 12243797 = 71741) (by norm_num)
theorem B3625829 : Blo 1611004 3625829 := bbase (se 4 (by rfl) ⟨339921, by rfl⟩ : syracuseStep 3625829 = 679843) (by norm_num)
theorem B5165957 : Blo 1611004 5165957 := bbase (se 4 (by rfl) ⟨484308, by rfl⟩ : syracuseStep 5165957 = 968617) (by norm_num)
theorem B3625901 : Blo 1611004 3625901 := bbase (se 3 (by rfl) ⟨679856, by rfl⟩ : syracuseStep 3625901 = 1359713) (by norm_num)
theorem B3060661 : Blo 1611004 3060661 := bbase (se 5 (by rfl) ⟨143468, by rfl⟩ : syracuseStep 3060661 = 286937) (by norm_num)
theorem B3625973 : Blo 1611004 3625973 := bbase (se 5 (by rfl) ⟨169967, by rfl⟩ : syracuseStep 3625973 = 339935) (by norm_num)
theorem B8156213 : Blo 1611004 8156213 := bbase (se 5 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 8156213 = 764645) (by norm_num)
theorem B6886453 : Blo 1611004 6886453 := bbase (se 5 (by rfl) ⟨322802, by rfl⟩ : syracuseStep 6886453 = 645605) (by norm_num)
theorem B3626045 : Blo 1611004 3626045 := bbase (se 3 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 3626045 = 1359767) (by norm_num)
theorem B3060821 : Blo 1611004 3060821 := bbase (se 8 (by rfl) ⟨17934, by rfl⟩ : syracuseStep 3060821 = 35869) (by norm_num)
theorem B3626117 : Blo 1611004 3626117 := bbase (se 4 (by rfl) ⟨339948, by rfl⟩ : syracuseStep 3626117 = 679897) (by norm_num)
theorem B3871901 : Blo 1611004 3871901 := bbase (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) (by norm_num)
theorem B4592837 : Blo 1611004 4592837 := bbase (se 4 (by rfl) ⟨430578, by rfl⟩ : syracuseStep 4592837 = 861157) (by norm_num)
theorem B3626189 : Blo 1611004 3626189 := bbase (se 3 (by rfl) ⟨679910, by rfl⟩ : syracuseStep 3626189 = 1359821) (by norm_num)
theorem B3060965 : Blo 1611004 3060965 := bbase (se 4 (by rfl) ⟨286965, by rfl⟩ : syracuseStep 3060965 = 573931) (by norm_num)
theorem B12236021 : Blo 1611004 12236021 := bbase (se 5 (by rfl) ⟨573563, by rfl⟩ : syracuseStep 12236021 = 1147127) (by norm_num)
theorem B3626261 : Blo 1611004 3626261 := bbase (se 6 (by rfl) ⟨84990, by rfl⟩ : syracuseStep 3626261 = 169981) (by norm_num)
theorem B3626333 : Blo 1611004 3626333 := bbase (se 3 (by rfl) ⟨679937, by rfl⟩ : syracuseStep 3626333 = 1359875) (by norm_num)
theorem B3626405 : Blo 1611004 3626405 := bbase (se 4 (by rfl) ⟨339975, by rfl⟩ : syracuseStep 3626405 = 679951) (by norm_num)
theorem B3626477 : Blo 1611004 3626477 := bbase (se 3 (by rfl) ⟨679964, by rfl⟩ : syracuseStep 3626477 = 1359929) (by norm_num)
theorem B9180661 : Blo 1611004 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B3061253 : Blo 1611004 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B6116917 : Blo 1611004 6116917 := bbase (se 5 (by rfl) ⟨286730, by rfl⟩ : syracuseStep 6116917 = 573461) (by norm_num)
theorem B3626549 : Blo 1611004 3626549 := bbase (se 5 (by rfl) ⟨169994, by rfl⟩ : syracuseStep 3626549 = 339989) (by norm_num)
theorem B6207029 : Blo 1611004 6207029 := bbase (se 5 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 6207029 = 581909) (by norm_num)
theorem B3626621 : Blo 1611004 3626621 := bbase (se 3 (by rfl) ⟨679991, by rfl⟩ : syracuseStep 3626621 = 1359983) (by norm_num)
theorem B3061405 : Blo 1611004 3061405 := bbase (se 3 (by rfl) ⟨574013, by rfl⟩ : syracuseStep 3061405 = 1148027) (by norm_num)
theorem B10327733 : Blo 1611004 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B3626693 : Blo 1611004 3626693 := bbase (se 4 (by rfl) ⟨340002, by rfl⟩ : syracuseStep 3626693 = 680005) (by norm_num)
theorem B3872477 : Blo 1611004 3872477 := bbase (se 3 (by rfl) ⟨726089, by rfl⟩ : syracuseStep 3872477 = 1452179) (by norm_num)
theorem B3626765 : Blo 1611004 3626765 := bbase (se 3 (by rfl) ⟨680018, by rfl⟩ : syracuseStep 3626765 = 1360037) (by norm_num)
theorem B5437205 : Blo 1611004 5437205 := bbase (se 6 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 5437205 = 254869) (by norm_num)
theorem B3626837 : Blo 1611004 3626837 := bbase (se 9 (by rfl) ⟨10625, by rfl⟩ : syracuseStep 3626837 = 21251) (by norm_num)
theorem B3585877 : Blo 1611004 3585877 := bbase (se 9 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 3585877 = 21011) (by norm_num)
theorem B6117221 : Blo 1611004 6117221 := bbase (se 4 (by rfl) ⟨573489, by rfl⟩ : syracuseStep 6117221 = 1146979) (by norm_num)
theorem B2905973 : Blo 1611004 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B3626909 : Blo 1611004 3626909 := bbase (se 3 (by rfl) ⟨680045, by rfl⟩ : syracuseStep 3626909 = 1360091) (by norm_num)
theorem B8165285 : Blo 1611004 8165285 := bbase (se 4 (by rfl) ⟨765495, by rfl⟩ : syracuseStep 8165285 = 1530991) (by norm_num)
theorem B2906045 : Blo 1611004 2906045 := bbase (se 3 (by rfl) ⟨544883, by rfl⟩ : syracuseStep 2906045 = 1089767) (by norm_num)
theorem B3061709 : Blo 1611004 3061709 := bbase (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) (by norm_num)
theorem B3626981 : Blo 1611004 3626981 := bbase (se 4 (by rfl) ⟨340029, by rfl⟩ : syracuseStep 3626981 = 680059) (by norm_num)
theorem B3627053 : Blo 1611004 3627053 := bbase (se 3 (by rfl) ⟨680072, by rfl⟩ : syracuseStep 3627053 = 1360145) (by norm_num)
theorem B1964137 : Blo 1611004 1964137 := bbase (se 2 (by rfl) ⟨736551, by rfl⟩ : syracuseStep 1964137 = 1473103) (by norm_num)
theorem B3627125 : Blo 1611004 3627125 := bbase (se 5 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 3627125 = 340043) (by norm_num)
theorem B3627197 : Blo 1611004 3627197 := bbase (se 3 (by rfl) ⟨680099, by rfl⟩ : syracuseStep 3627197 = 1360199) (by norm_num)
theorem B5437637 : Blo 1611004 5437637 := bbase (se 4 (by rfl) ⟨509778, by rfl⟩ : syracuseStep 5437637 = 1019557) (by norm_num)
theorem B3627269 : Blo 1611004 3627269 := bbase (se 4 (by rfl) ⟨340056, by rfl⟩ : syracuseStep 3627269 = 680113) (by norm_num)
theorem B2177317 : Blo 1611004 2177317 := bbase (se 4 (by rfl) ⟨204123, by rfl⟩ : syracuseStep 2177317 = 408247) (by norm_num)
theorem B8157509 : Blo 1611004 8157509 := bbase (se 4 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 8157509 = 1529533) (by norm_num)
theorem B3266885 : Blo 1611004 3266885 := bbase (se 4 (by rfl) ⟨306270, by rfl⟩ : syracuseStep 3266885 = 612541) (by norm_num)
theorem B3627341 : Blo 1611004 3627341 := bbase (se 3 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 3627341 = 1360253) (by norm_num)
theorem B11614549 : Blo 1611004 11614549 := bbase (se 10 (by rfl) ⟨17013, by rfl⟩ : syracuseStep 11614549 = 34027) (by norm_num)
theorem B4077965 : Blo 1611004 4077965 := bbase (se 3 (by rfl) ⟨764618, by rfl⟩ : syracuseStep 4077965 = 1529237) (by norm_num)
theorem B3627413 : Blo 1611004 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B66157013 : Blo 1611004 66157013 := bbase (se 7 (by rfl) ⟨775277, by rfl⟩ : syracuseStep 66157013 = 1550555) (by norm_num)
theorem B3627485 : Blo 1611004 3627485 := bbase (se 3 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 3627485 = 1360307) (by norm_num)
theorem B3725797 : Blo 1611004 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B3627557 : Blo 1611004 3627557 := bbase (se 4 (by rfl) ⟨340083, by rfl⟩ : syracuseStep 3627557 = 680167) (by norm_num)
theorem B10467893 : Blo 1611004 10467893 := bbase (se 5 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 10467893 = 981365) (by norm_num)
theorem B4356709 : Blo 1611004 4356709 := bbase (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) (by norm_num)
theorem B3627629 : Blo 1611004 3627629 := bbase (se 3 (by rfl) ⟨680180, by rfl⟩ : syracuseStep 3627629 = 1360361) (by norm_num)
theorem B5438069 : Blo 1611004 5438069 := bbase (se 5 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 5438069 = 509819) (by norm_num)
theorem B7748261 : Blo 1611004 7748261 := bbase (se 4 (by rfl) ⟨726399, by rfl⟩ : syracuseStep 7748261 = 1452799) (by norm_num)
theorem B3627701 : Blo 1611004 3627701 := bbase (se 5 (by rfl) ⟨170048, by rfl⟩ : syracuseStep 3627701 = 340097) (by norm_num)
theorem B4078309 : Blo 1611004 4078309 := bbase (se 4 (by rfl) ⟨382341, by rfl⟩ : syracuseStep 4078309 = 764683) (by norm_num)
theorem B15923957 : Blo 1611004 15923957 := bbase (se 5 (by rfl) ⟨746435, by rfl⟩ : syracuseStep 15923957 = 1492871) (by norm_num)
theorem B3627773 : Blo 1611004 3627773 := bbase (se 3 (by rfl) ⟨680207, by rfl⟩ : syracuseStep 3627773 = 1360415) (by norm_num)
theorem B3627845 : Blo 1611004 3627845 := bbase (se 4 (by rfl) ⟨340110, by rfl⟩ : syracuseStep 3627845 = 680221) (by norm_num)
theorem B4078421 : Blo 1611004 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B3103573 : Blo 1611004 3103573 := bbase (se 9 (by rfl) ⟨9092, by rfl⟩ : syracuseStep 3103573 = 18185) (by norm_num)
theorem B2718589 : Blo 1611004 2718589 := bbase (se 3 (by rfl) ⟨509735, by rfl⟩ : syracuseStep 2718589 = 1019471) (by norm_num)
theorem B3267469 : Blo 1611004 3267469 := bbase (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) (by norm_num)
theorem B3627917 : Blo 1611004 3627917 := bbase (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) (by norm_num)
theorem B2718677 : Blo 1611004 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B3627989 : Blo 1611004 3627989 := bbase (se 7 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 3627989 = 85031) (by norm_num)
theorem B4078613 : Blo 1611004 4078613 := bbase (se 6 (by rfl) ⟨95592, by rfl⟩ : syracuseStep 4078613 = 191185) (by norm_num)
theorem B3628061 : Blo 1611004 3628061 := bbase (se 3 (by rfl) ⟨680261, by rfl⟩ : syracuseStep 3628061 = 1360523) (by norm_num)
theorem B5438501 : Blo 1611004 5438501 := bbase (se 4 (by rfl) ⟨509859, by rfl⟩ : syracuseStep 5438501 = 1019719) (by norm_num)
theorem B2718805 : Blo 1611004 2718805 := bbase (se 8 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 2718805 = 31861) (by norm_num)
theorem B41294933 : Blo 1611004 41294933 := bbase (se 8 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 41294933 = 483925) (by norm_num)
theorem B3628133 : Blo 1611004 3628133 := bbase (se 4 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 3628133 = 680275) (by norm_num)
theorem B2718893 : Blo 1611004 2718893 := bbase (se 3 (by rfl) ⟨509792, by rfl⟩ : syracuseStep 2718893 = 1019585) (by norm_num)
theorem B3628205 : Blo 1611004 3628205 := bbase (se 3 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 3628205 = 1360577) (by norm_num)
theorem B3628277 : Blo 1611004 3628277 := bbase (se 5 (by rfl) ⟨170075, by rfl⟩ : syracuseStep 3628277 = 340151) (by norm_num)
theorem B2039033 : Blo 1611004 2039033 := bbase (se 2 (by rfl) ⟨764637, by rfl⟩ : syracuseStep 2039033 = 1529275) (by norm_num)
theorem B2719021 : Blo 1611004 2719021 := bbase (se 3 (by rfl) ⟨509816, by rfl⟩ : syracuseStep 2719021 = 1019633) (by norm_num)
theorem B2039089 : Blo 1611004 2039089 := bbase (se 2 (by rfl) ⟨764658, by rfl⟩ : syracuseStep 2039089 = 1529317) (by norm_num)
theorem B3628349 : Blo 1611004 3628349 := bbase (se 3 (by rfl) ⟨680315, by rfl⟩ : syracuseStep 3628349 = 1360631) (by norm_num)
theorem B4078957 : Blo 1611004 4078957 := bbase (se 3 (by rfl) ⟨764804, by rfl⟩ : syracuseStep 4078957 = 1529609) (by norm_num)
theorem B5807477 : Blo 1611004 5807477 := bbase (se 5 (by rfl) ⟨272225, by rfl⟩ : syracuseStep 5807477 = 544451) (by norm_num)
theorem B2719109 : Blo 1611004 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B3980677 : Blo 1611004 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B3628421 : Blo 1611004 3628421 := bbase (se 4 (by rfl) ⟨340164, by rfl⟩ : syracuseStep 3628421 = 680329) (by norm_num)
theorem B2039185 : Blo 1611004 2039185 := bbase (se 2 (by rfl) ⟨764694, by rfl⟩ : syracuseStep 2039185 = 1529389) (by norm_num)
theorem B9182645 : Blo 1611004 9182645 := bbase (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) (by norm_num)
theorem B3628493 : Blo 1611004 3628493 := bbase (se 3 (by rfl) ⟨680342, by rfl⟩ : syracuseStep 3628493 = 1360685) (by norm_num)
theorem B5438933 : Blo 1611004 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B4079069 : Blo 1611004 4079069 := bbase (se 3 (by rfl) ⟨764825, by rfl⟩ : syracuseStep 4079069 = 1529651) (by norm_num)
theorem B2719237 : Blo 1611004 2719237 := bbase (se 4 (by rfl) ⟨254928, by rfl⟩ : syracuseStep 2719237 = 509857) (by norm_num)
theorem B3628565 : Blo 1611004 3628565 := bbase (se 6 (by rfl) ⟨85044, by rfl⟩ : syracuseStep 3628565 = 170089) (by norm_num)
theorem B2039357 : Blo 1611004 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B8158805 : Blo 1611004 8158805 := bbase (se 8 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 8158805 = 95611) (by norm_num)
theorem B2719325 : Blo 1611004 2719325 := bbase (se 3 (by rfl) ⟨509873, by rfl⟩ : syracuseStep 2719325 = 1019747) (by norm_num)
theorem B3628637 : Blo 1611004 3628637 := bbase (se 3 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 3628637 = 1360739) (by norm_num)
theorem B2039413 : Blo 1611004 2039413 := bbase (se 5 (by rfl) ⟨95597, by rfl⟩ : syracuseStep 2039413 = 191195) (by norm_num)
theorem B4079261 : Blo 1611004 4079261 := bbase (se 3 (by rfl) ⟨764861, by rfl⟩ : syracuseStep 4079261 = 1529723) (by norm_num)
theorem B3628709 : Blo 1611004 3628709 := bbase (se 4 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 3628709 = 680383) (by norm_num)
theorem B2039509 : Blo 1611004 2039509 := bbase (se 7 (by rfl) ⟨23900, by rfl⟩ : syracuseStep 2039509 = 47801) (by norm_num)
theorem B2719453 : Blo 1611004 2719453 := bbase (se 3 (by rfl) ⟨509897, by rfl⟩ : syracuseStep 2719453 = 1019795) (by norm_num)
theorem B3628781 : Blo 1611004 3628781 := bbase (se 3 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 3628781 = 1360793) (by norm_num)
theorem B2719541 : Blo 1611004 2719541 := bbase (se 5 (by rfl) ⟨127478, by rfl⟩ : syracuseStep 2719541 = 254957) (by norm_num)
theorem B3628853 : Blo 1611004 3628853 := bbase (se 5 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 3628853 = 340205) (by norm_num)
theorem B1744705 : Blo 1611004 1744705 := bbase (se 2 (by rfl) ⟨654264, by rfl⟩ : syracuseStep 1744705 = 1308529) (by norm_num)
theorem B6537077 : Blo 1611004 6537077 := bbase (se 5 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 6537077 = 612851) (by norm_num)
theorem B3628925 : Blo 1611004 3628925 := bbase (se 3 (by rfl) ⟨680423, by rfl⟩ : syracuseStep 3628925 = 1360847) (by norm_num)
theorem B2039681 : Blo 1611004 2039681 := bbase (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) (by norm_num)
theorem B2416517 : Blo 1611004 2416517 := bbase (se 4 (by rfl) ⟨226548, by rfl⟩ : syracuseStep 2416517 = 453097) (by norm_num)
theorem B5439365 : Blo 1611004 5439365 := bbase (se 4 (by rfl) ⟨509940, by rfl⟩ : syracuseStep 5439365 = 1019881) (by norm_num)
theorem B2416541 : Blo 1611004 2416541 := bbase (se 3 (by rfl) ⟨453101, by rfl⟩ : syracuseStep 2416541 = 906203) (by norm_num)
theorem B6119333 : Blo 1611004 6119333 := bbase (se 4 (by rfl) ⟨573687, by rfl⟩ : syracuseStep 6119333 = 1147375) (by norm_num)
theorem B2416565 : Blo 1611004 2416565 := bbase (se 5 (by rfl) ⟨113276, by rfl⟩ : syracuseStep 2416565 = 226553) (by norm_num)
theorem B2719669 : Blo 1611004 2719669 := bbase (se 5 (by rfl) ⟨127484, by rfl⟩ : syracuseStep 2719669 = 254969) (by norm_num)
theorem B2039737 : Blo 1611004 2039737 := bbase (se 2 (by rfl) ⟨764901, by rfl⟩ : syracuseStep 2039737 = 1529803) (by norm_num)
theorem B3628997 : Blo 1611004 3628997 := bbase (se 4 (by rfl) ⟨340218, by rfl⟩ : syracuseStep 3628997 = 680437) (by norm_num)
theorem B2416589 : Blo 1611004 2416589 := bbase (se 3 (by rfl) ⟨453110, by rfl⟩ : syracuseStep 2416589 = 906221) (by norm_num)
theorem B2416613 : Blo 1611004 2416613 := bbase (se 4 (by rfl) ⟨226557, by rfl⟩ : syracuseStep 2416613 = 453115) (by norm_num)
theorem B6889445 : Blo 1611004 6889445 := bbase (se 4 (by rfl) ⟨645885, by rfl⟩ : syracuseStep 6889445 = 1291771) (by norm_num)
theorem B4079605 : Blo 1611004 4079605 := bbase (se 5 (by rfl) ⟨191231, by rfl⟩ : syracuseStep 4079605 = 382463) (by norm_num)
theorem B2416637 : Blo 1611004 2416637 := bbase (se 3 (by rfl) ⟨453119, by rfl⟩ : syracuseStep 2416637 = 906239) (by norm_num)
theorem B2416643 : Blo 1611004 2416643 := bstep (se 1 (by rfl) ⟨1812482, by rfl⟩ : syracuseStep 2416643 = 3624965) B3624965
theorem B2416673 : Blo 1611004 2416673 := bstep (se 2 (by rfl) ⟨906252, by rfl⟩ : syracuseStep 2416673 = 1812505) B1812505
theorem B2719777 : Blo 1611004 2719777 := bstep (se 2 (by rfl) ⟨1019916, by rfl⟩ : syracuseStep 2719777 = 2039833) B2039833
theorem B2039843 : Blo 1611004 2039843 := bstep (se 1 (by rfl) ⟨1529882, by rfl⟩ : syracuseStep 2039843 = 3059765) B3059765
theorem B3629105 : Blo 1611004 3629105 := bstep (se 2 (by rfl) ⟨1360914, by rfl⟩ : syracuseStep 3629105 = 2721829) B2721829
theorem B2416691 : Blo 1611004 2416691 := bstep (se 1 (by rfl) ⟨1812518, by rfl⟩ : syracuseStep 2416691 = 3625037) B3625037
theorem B2719811 : Blo 1611004 2719811 := bstep (se 1 (by rfl) ⟨2039858, by rfl⟩ : syracuseStep 2719811 = 4079717) B4079717
theorem B3629123 : Blo 1611004 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B2416721 : Blo 1611004 2416721 := bstep (se 2 (by rfl) ⟨906270, by rfl⟩ : syracuseStep 2416721 = 1812541) B1812541
theorem B4358225 : Blo 1611004 4358225 := bstep (se 2 (by rfl) ⟨1634334, by rfl⟩ : syracuseStep 4358225 = 3268669) B3268669
theorem B2416739 : Blo 1611004 2416739 := bstep (se 1 (by rfl) ⟨1812554, by rfl⟩ : syracuseStep 2416739 = 3625109) B3625109
theorem B2416769 : Blo 1611004 2416769 := bstep (se 2 (by rfl) ⟨906288, by rfl⟩ : syracuseStep 2416769 = 1812577) B1812577
theorem B4079747 : Blo 1611004 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B2416787 : Blo 1611004 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B9183395 : Blo 1611004 9183395 := bstep (se 1 (by rfl) ⟨6887546, by rfl⟩ : syracuseStep 9183395 = 13775093) B13775093
theorem B2416817 : Blo 1611004 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B2416835 : Blo 1611004 2416835 := bstep (se 1 (by rfl) ⟨1812626, by rfl⟩ : syracuseStep 2416835 = 3625253) B3625253
theorem B2719939 : Blo 1611004 2719939 := bstep (se 1 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 2719939 = 4079909) B4079909
theorem B2416865 : Blo 1611004 2416865 := bstep (se 2 (by rfl) ⟨906324, by rfl⟩ : syracuseStep 2416865 = 1812649) B1812649
theorem B26493155 : Blo 1611004 26493155 := bstep (se 1 (by rfl) ⟨19869866, by rfl⟩ : syracuseStep 26493155 = 39739733) B39739733
theorem B6119651 : Blo 1611004 6119651 := bstep (se 1 (by rfl) ⟨4589738, by rfl⟩ : syracuseStep 6119651 = 9179477) B9179477
theorem B2416883 : Blo 1611004 2416883 := bstep (se 1 (by rfl) ⟨1812662, by rfl⟩ : syracuseStep 2416883 = 3625325) B3625325
theorem B4587779 : Blo 1611004 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B2416913 : Blo 1611004 2416913 := bstep (se 2 (by rfl) ⟨906342, by rfl⟩ : syracuseStep 2416913 = 1812685) B1812685
theorem B2416931 : Blo 1611004 2416931 := bstep (se 1 (by rfl) ⟨1812698, by rfl⟩ : syracuseStep 2416931 = 3625397) B3625397
theorem B2416961 : Blo 1611004 2416961 := bstep (se 2 (by rfl) ⟨906360, by rfl⟩ : syracuseStep 2416961 = 1812721) B1812721
theorem B2326849 : Blo 1611004 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B2720081 : Blo 1611004 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B2416979 : Blo 1611004 2416979 := bstep (se 1 (by rfl) ⟨1812734, by rfl⟩ : syracuseStep 2416979 = 3625469) B3625469
theorem B10322275 : Blo 1611004 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B2294129 : Blo 1611004 2294129 := bstep (se 2 (by rfl) ⟨860298, by rfl⟩ : syracuseStep 2294129 = 1720597) B1720597
theorem B2417009 : Blo 1611004 2417009 := bstep (se 2 (by rfl) ⟨906378, by rfl⟩ : syracuseStep 2417009 = 1812757) B1812757
theorem B2417027 : Blo 1611004 2417027 := bstep (se 1 (by rfl) ⟨1812770, by rfl⟩ : syracuseStep 2417027 = 3625541) B3625541
theorem B2417057 : Blo 1611004 2417057 := bstep (se 2 (by rfl) ⟨906396, by rfl⟩ : syracuseStep 2417057 = 1812793) B1812793
theorem B3269041 : Blo 1611004 3269041 := bstep (se 2 (by rfl) ⟨1225890, by rfl⟩ : syracuseStep 3269041 = 2451781) B2451781
theorem B2417075 : Blo 1611004 2417075 := bstep (se 1 (by rfl) ⟨1812806, by rfl⟩ : syracuseStep 2417075 = 3625613) B3625613
theorem B2417105 : Blo 1611004 2417105 := bstep (se 2 (by rfl) ⟨906414, by rfl⟩ : syracuseStep 2417105 = 1812829) B1812829
theorem B2720209 : Blo 1611004 2720209 := bstep (se 2 (by rfl) ⟨1020078, by rfl⟩ : syracuseStep 2720209 = 2040157) B2040157
theorem B2417123 : Blo 1611004 2417123 := bstep (se 1 (by rfl) ⟨1812842, by rfl⟩ : syracuseStep 2417123 = 3625685) B3625685
theorem B4137443 : Blo 1611004 4137443 := bstep (se 1 (by rfl) ⟨3103082, by rfl⟩ : syracuseStep 4137443 = 6206165) B6206165
theorem B5161457 : Blo 1611004 5161457 := bstep (se 2 (by rfl) ⟨1935546, by rfl⟩ : syracuseStep 5161457 = 3871093) B3871093
theorem B2580979 : Blo 1611004 2580979 := bstep (se 1 (by rfl) ⟨1935734, by rfl⟩ : syracuseStep 2580979 = 3871469) B3871469
theorem B2720243 : Blo 1611004 2720243 := bstep (se 1 (by rfl) ⟨2040182, by rfl⟩ : syracuseStep 2720243 = 4080365) B4080365
theorem B2449921 : Blo 1611004 2449921 := bstep (se 2 (by rfl) ⟨918720, by rfl⟩ : syracuseStep 2449921 = 1837441) B1837441
theorem B2417153 : Blo 1611004 2417153 := bstep (se 2 (by rfl) ⟨906432, by rfl⟩ : syracuseStep 2417153 = 1812865) B1812865
theorem B5440013 : Blo 1611004 5440013 := bstep (se 3 (by rfl) ⟨1020002, by rfl⟩ : syracuseStep 5440013 = 2040005) B2040005
theorem B2417171 : Blo 1611004 2417171 := bstep (se 1 (by rfl) ⟨1812878, by rfl⟩ : syracuseStep 2417171 = 3625757) B3625757
theorem B3269155 : Blo 1611004 3269155 := bstep (se 1 (by rfl) ⟨2451866, by rfl⟩ : syracuseStep 3269155 = 4903733) B4903733
theorem B2417201 : Blo 1611004 2417201 := bstep (se 2 (by rfl) ⟨906450, by rfl⟩ : syracuseStep 2417201 = 1812901) B1812901
theorem B2417219 : Blo 1611004 2417219 := bstep (se 1 (by rfl) ⟨1812914, by rfl⟩ : syracuseStep 2417219 = 3625829) B3625829
theorem B5440067 : Blo 1611004 5440067 := bstep (se 1 (by rfl) ⟨4080050, by rfl⟩ : syracuseStep 5440067 = 8160101) B8160101
theorem B2417249 : Blo 1611004 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B2417267 : Blo 1611004 2417267 := bstep (se 1 (by rfl) ⟨1812950, by rfl⟩ : syracuseStep 2417267 = 3625901) B3625901
theorem B2720371 : Blo 1611004 2720371 := bstep (se 1 (by rfl) ⟨2040278, by rfl⟩ : syracuseStep 2720371 = 4080557) B4080557
theorem B2417297 : Blo 1611004 2417297 := bstep (se 2 (by rfl) ⟨906486, by rfl⟩ : syracuseStep 2417297 = 1812973) B1812973
theorem B2417315 : Blo 1611004 2417315 := bstep (se 1 (by rfl) ⟨1812986, by rfl⟩ : syracuseStep 2417315 = 3625973) B3625973
theorem B2417345 : Blo 1611004 2417345 := bstep (se 2 (by rfl) ⟨906504, by rfl⟩ : syracuseStep 2417345 = 1813009) B1813009
theorem B2417363 : Blo 1611004 2417363 := bstep (se 1 (by rfl) ⟨1813022, by rfl⟩ : syracuseStep 2417363 = 3626045) B3626045
theorem B2040547 : Blo 1611004 2040547 := bstep (se 1 (by rfl) ⟨1530410, by rfl⟩ : syracuseStep 2040547 = 3060821) B3060821
theorem B2417393 : Blo 1611004 2417393 := bstep (se 2 (by rfl) ⟨906522, by rfl⟩ : syracuseStep 2417393 = 1813045) B1813045
theorem B2720513 : Blo 1611004 2720513 := bstep (se 2 (by rfl) ⟨1020192, by rfl⟩ : syracuseStep 2720513 = 2040385) B2040385
theorem B2417411 : Blo 1611004 2417411 := bstep (se 1 (by rfl) ⟨1813058, by rfl⟩ : syracuseStep 2417411 = 3626117) B3626117
theorem B2417441 : Blo 1611004 2417441 := bstep (se 2 (by rfl) ⟨906540, by rfl⟩ : syracuseStep 2417441 = 1813081) B1813081
theorem B2450225 : Blo 1611004 2450225 := bstep (se 2 (by rfl) ⟨918834, by rfl⟩ : syracuseStep 2450225 = 1837669) B1837669
theorem B2417459 : Blo 1611004 2417459 := bstep (se 1 (by rfl) ⟨1813094, by rfl⟩ : syracuseStep 2417459 = 3626189) B3626189
theorem B2040643 : Blo 1611004 2040643 := bstep (se 1 (by rfl) ⟨1530482, by rfl⟩ : syracuseStep 2040643 = 3060965) B3060965
theorem B2417489 : Blo 1611004 2417489 := bstep (se 2 (by rfl) ⟨906558, by rfl⟩ : syracuseStep 2417489 = 1813117) B1813117
theorem B5440337 : Blo 1611004 5440337 := bstep (se 2 (by rfl) ⟨2040126, by rfl⟩ : syracuseStep 5440337 = 4080253) B4080253
theorem B2417507 : Blo 1611004 2417507 := bstep (se 1 (by rfl) ⟨1813130, by rfl⟩ : syracuseStep 2417507 = 3626261) B3626261
theorem B6120305 : Blo 1611004 6120305 := bstep (se 2 (by rfl) ⟨2295114, by rfl⟩ : syracuseStep 6120305 = 4590229) B4590229
theorem B2179955 : Blo 1611004 2179955 := bstep (se 1 (by rfl) ⟨1634966, by rfl⟩ : syracuseStep 2179955 = 3269933) B3269933
theorem B2417537 : Blo 1611004 2417537 := bstep (se 2 (by rfl) ⟨906576, by rfl⟩ : syracuseStep 2417537 = 1813153) B1813153
theorem B2294659 : Blo 1611004 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B2720641 : Blo 1611004 2720641 := bstep (se 2 (by rfl) ⟨1020240, by rfl⟩ : syracuseStep 2720641 = 2040481) B2040481
theorem B2417555 : Blo 1611004 2417555 := bstep (se 1 (by rfl) ⟨1813166, by rfl⟩ : syracuseStep 2417555 = 3626333) B3626333
theorem B2720675 : Blo 1611004 2720675 := bstep (se 1 (by rfl) ⟨2040506, by rfl⟩ : syracuseStep 2720675 = 4081013) B4081013
theorem B2417585 : Blo 1611004 2417585 := bstep (se 2 (by rfl) ⟨906594, by rfl⟩ : syracuseStep 2417585 = 1813189) B1813189
theorem B2417603 : Blo 1611004 2417603 := bstep (se 1 (by rfl) ⟨1813202, by rfl⟩ : syracuseStep 2417603 = 3626405) B3626405
theorem B2417633 : Blo 1611004 2417633 := bstep (se 2 (by rfl) ⟨906612, by rfl⟩ : syracuseStep 2417633 = 1813225) B1813225
theorem B2417651 : Blo 1611004 2417651 := bstep (se 1 (by rfl) ⟨1813238, by rfl⟩ : syracuseStep 2417651 = 3626477) B3626477
theorem B2417681 : Blo 1611004 2417681 := bstep (se 2 (by rfl) ⟨906630, by rfl⟩ : syracuseStep 2417681 = 1813261) B1813261
theorem B2417699 : Blo 1611004 2417699 := bstep (se 1 (by rfl) ⟨1813274, by rfl⟩ : syracuseStep 2417699 = 3626549) B3626549
theorem B2720803 : Blo 1611004 2720803 := bstep (se 1 (by rfl) ⟨2040602, by rfl⟩ : syracuseStep 2720803 = 4081205) B4081205
theorem B4138019 : Blo 1611004 4138019 := bstep (se 1 (by rfl) ⟨3103514, by rfl⟩ : syracuseStep 4138019 = 6207029) B6207029
theorem B4588589 : Blo 1611004 4588589 := bstep (se 3 (by rfl) ⟨860360, by rfl⟩ : syracuseStep 4588589 = 1720721) B1720721
theorem B6882353 : Blo 1611004 6882353 := bstep (se 2 (by rfl) ⟨2580882, by rfl⟩ : syracuseStep 6882353 = 5161765) B5161765
theorem B4080689 : Blo 1611004 4080689 := bstep (se 2 (by rfl) ⟨1530258, by rfl⟩ : syracuseStep 4080689 = 3060517) B3060517
theorem B2417729 : Blo 1611004 2417729 := bstep (se 2 (by rfl) ⟨906648, by rfl⟩ : syracuseStep 2417729 = 1813297) B1813297
theorem B2417747 : Blo 1611004 2417747 := bstep (se 1 (by rfl) ⟨1813310, by rfl⟩ : syracuseStep 2417747 = 3626621) B3626621
theorem B4080739 : Blo 1611004 4080739 := bstep (se 1 (by rfl) ⟨3060554, by rfl⟩ : syracuseStep 4080739 = 6121109) B6121109
theorem B2417777 : Blo 1611004 2417777 := bstep (se 2 (by rfl) ⟨906666, by rfl⟩ : syracuseStep 2417777 = 1813333) B1813333
theorem B2417795 : Blo 1611004 2417795 := bstep (se 1 (by rfl) ⟨1813346, by rfl⟩ : syracuseStep 2417795 = 3626693) B3626693
theorem B2581651 : Blo 1611004 2581651 := bstep (se 1 (by rfl) ⟨1936238, by rfl⟩ : syracuseStep 2581651 = 3872477) B3872477
theorem B2417825 : Blo 1611004 2417825 := bstep (se 2 (by rfl) ⟨906684, by rfl⟩ : syracuseStep 2417825 = 1813369) B1813369
theorem B2720945 : Blo 1611004 2720945 := bstep (se 2 (by rfl) ⟨1020354, by rfl⟩ : syracuseStep 2720945 = 2040709) B2040709
theorem B2417843 : Blo 1611004 2417843 := bstep (se 1 (by rfl) ⟨1813382, by rfl⟩ : syracuseStep 2417843 = 3626765) B3626765
theorem B2417873 : Blo 1611004 2417873 := bstep (se 2 (by rfl) ⟨906702, by rfl⟩ : syracuseStep 2417873 = 1813405) B1813405
theorem B2294995 : Blo 1611004 2294995 := bstep (se 1 (by rfl) ⟨1721246, by rfl⟩ : syracuseStep 2294995 = 3442493) B3442493
theorem B4588771 : Blo 1611004 4588771 := bstep (se 1 (by rfl) ⟨3441578, by rfl⟩ : syracuseStep 4588771 = 6883157) B6883157
theorem B2417891 : Blo 1611004 2417891 := bstep (se 1 (by rfl) ⟨1813418, by rfl⟩ : syracuseStep 2417891 = 3626837) B3626837
theorem B4080881 : Blo 1611004 4080881 := bstep (se 2 (by rfl) ⟨1530330, by rfl⟩ : syracuseStep 4080881 = 3060661) B3060661
theorem B2417921 : Blo 1611004 2417921 := bstep (se 2 (by rfl) ⟨906720, by rfl⟩ : syracuseStep 2417921 = 1813441) B1813441
theorem B2417939 : Blo 1611004 2417939 := bstep (se 1 (by rfl) ⟨1813454, by rfl⟩ : syracuseStep 2417939 = 3626909) B3626909
theorem B2417969 : Blo 1611004 2417969 := bstep (se 2 (by rfl) ⟨906738, by rfl⟩ : syracuseStep 2417969 = 1813477) B1813477
theorem B2721073 : Blo 1611004 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B2041139 : Blo 1611004 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B2417987 : Blo 1611004 2417987 := bstep (se 1 (by rfl) ⟨1813490, by rfl⟩ : syracuseStep 2417987 = 3626981) B3626981
theorem B2721107 : Blo 1611004 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B2418017 : Blo 1611004 2418017 := bstep (se 2 (by rfl) ⟨906756, by rfl⟩ : syracuseStep 2418017 = 1813513) B1813513
theorem B5440877 : Blo 1611004 5440877 := bstep (se 3 (by rfl) ⟨1020164, by rfl⟩ : syracuseStep 5440877 = 2040329) B2040329
theorem B2418035 : Blo 1611004 2418035 := bstep (se 1 (by rfl) ⟨1813526, by rfl⟩ : syracuseStep 2418035 = 3627053) B3627053
theorem B10331525 : Blo 1611004 10331525 := bstep (se 4 (by rfl) ⟨968580, by rfl⟩ : syracuseStep 10331525 = 1937161) B1937161
theorem B2418065 : Blo 1611004 2418065 := bstep (se 2 (by rfl) ⟨906774, by rfl⟩ : syracuseStep 2418065 = 1813549) B1813549
theorem B2418083 : Blo 1611004 2418083 := bstep (se 1 (by rfl) ⟨1813562, by rfl⟩ : syracuseStep 2418083 = 3627125) B3627125
theorem B5440931 : Blo 1611004 5440931 := bstep (se 1 (by rfl) ⟨4080698, by rfl⟩ : syracuseStep 5440931 = 8161397) B8161397
theorem B11036081 : Blo 1611004 11036081 := bstep (se 2 (by rfl) ⟨4138530, by rfl⟩ : syracuseStep 11036081 = 8277061) B8277061
theorem B2418113 : Blo 1611004 2418113 := bstep (se 2 (by rfl) ⟨906792, by rfl⟩ : syracuseStep 2418113 = 1813585) B1813585
theorem B2418131 : Blo 1611004 2418131 := bstep (se 1 (by rfl) ⟨1813598, by rfl⟩ : syracuseStep 2418131 = 3627197) B3627197
theorem B2721235 : Blo 1611004 2721235 := bstep (se 1 (by rfl) ⟨2040926, by rfl⟩ : syracuseStep 2721235 = 4081853) B4081853
theorem B1721827 : Blo 1611004 1721827 := bstep (se 1 (by rfl) ⟨1291370, by rfl⟩ : syracuseStep 1721827 = 2582741) B2582741
theorem B9176561 : Blo 1611004 9176561 := bstep (se 2 (by rfl) ⟨3441210, by rfl⟩ : syracuseStep 9176561 = 6882421) B6882421
theorem B2418161 : Blo 1611004 2418161 := bstep (se 2 (by rfl) ⟨906810, by rfl⟩ : syracuseStep 2418161 = 1813621) B1813621
theorem B2418179 : Blo 1611004 2418179 := bstep (se 1 (by rfl) ⟨1813634, by rfl⟩ : syracuseStep 2418179 = 3627269) B3627269
theorem B2418209 : Blo 1611004 2418209 := bstep (se 2 (by rfl) ⟨906828, by rfl⟩ : syracuseStep 2418209 = 1813657) B1813657
theorem B2418227 : Blo 1611004 2418227 := bstep (se 1 (by rfl) ⟨1813670, by rfl⟩ : syracuseStep 2418227 = 3627341) B3627341
theorem B2418257 : Blo 1611004 2418257 := bstep (se 2 (by rfl) ⟨906846, by rfl⟩ : syracuseStep 2418257 = 1813693) B1813693
theorem B2582113 : Blo 1611004 2582113 := bstep (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) B1936585
theorem B2418275 : Blo 1611004 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B2721377 : Blo 1611004 2721377 := bstep (se 2 (by rfl) ⟨1020516, by rfl⟩ : syracuseStep 2721377 = 2041033) B2041033
theorem B2418305 : Blo 1611004 2418305 := bstep (se 2 (by rfl) ⟨906864, by rfl⟩ : syracuseStep 2418305 = 1813729) B1813729
theorem B13772429 : Blo 1611004 13772429 := bstep (se 3 (by rfl) ⟨2582330, by rfl⟩ : syracuseStep 13772429 = 5164661) B5164661
theorem B2418323 : Blo 1611004 2418323 := bstep (se 1 (by rfl) ⟨1813742, by rfl⟩ : syracuseStep 2418323 = 3627485) B3627485
theorem B5441201 : Blo 1611004 5441201 := bstep (se 2 (by rfl) ⟨2040450, by rfl⟩ : syracuseStep 5441201 = 4080901) B4080901
theorem B2418353 : Blo 1611004 2418353 := bstep (se 2 (by rfl) ⟨906882, by rfl⟩ : syracuseStep 2418353 = 1813765) B1813765
theorem B2582209 : Blo 1611004 2582209 := bstep (se 2 (by rfl) ⟨968328, by rfl⟩ : syracuseStep 2582209 = 1936657) B1936657
theorem B2418371 : Blo 1611004 2418371 := bstep (se 1 (by rfl) ⟨1813778, by rfl⟩ : syracuseStep 2418371 = 3627557) B3627557
theorem B4589261 : Blo 1611004 4589261 := bstep (se 3 (by rfl) ⟨860486, by rfl⟩ : syracuseStep 4589261 = 1720973) B1720973
theorem B2418401 : Blo 1611004 2418401 := bstep (se 2 (by rfl) ⟨906900, by rfl⟩ : syracuseStep 2418401 = 1813801) B1813801
theorem B2721505 : Blo 1611004 2721505 := bstep (se 2 (by rfl) ⟨1020564, by rfl⟩ : syracuseStep 2721505 = 2041129) B2041129
theorem B2418419 : Blo 1611004 2418419 := bstep (se 1 (by rfl) ⟨1813814, by rfl⟩ : syracuseStep 2418419 = 3627629) B3627629
theorem B2295553 : Blo 1611004 2295553 := bstep (se 2 (by rfl) ⟨860832, by rfl⟩ : syracuseStep 2295553 = 1721665) B1721665
theorem B2721539 : Blo 1611004 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B2418449 : Blo 1611004 2418449 := bstep (se 2 (by rfl) ⟨906918, by rfl⟩ : syracuseStep 2418449 = 1813837) B1813837
theorem B66209557 : Blo 1611004 66209557 := bstep (se 6 (by rfl) ⟨1551786, by rfl⟩ : syracuseStep 66209557 = 3103573) B3103573
theorem B2295587 : Blo 1611004 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B2418467 : Blo 1611004 2418467 := bstep (se 1 (by rfl) ⟨1813850, by rfl⟩ : syracuseStep 2418467 = 3627701) B3627701
theorem B8161073 : Blo 1611004 8161073 := bstep (se 2 (by rfl) ⟨3060402, by rfl⟩ : syracuseStep 8161073 = 6120805) B6120805
theorem B2418497 : Blo 1611004 2418497 := bstep (se 2 (by rfl) ⟨906936, by rfl⟩ : syracuseStep 2418497 = 1813873) B1813873
theorem B2418515 : Blo 1611004 2418515 := bstep (se 1 (by rfl) ⟨1813886, by rfl⟩ : syracuseStep 2418515 = 3627773) B3627773
theorem B2582369 : Blo 1611004 2582369 := bstep (se 2 (by rfl) ⟨968388, by rfl⟩ : syracuseStep 2582369 = 1936777) B1936777
theorem B2418545 : Blo 1611004 2418545 := bstep (se 2 (by rfl) ⟨906954, by rfl⟩ : syracuseStep 2418545 = 1813909) B1813909
theorem B2418563 : Blo 1611004 2418563 := bstep (se 1 (by rfl) ⟨1813922, by rfl⟩ : syracuseStep 2418563 = 3627845) B3627845
theorem B2721667 : Blo 1611004 2721667 := bstep (se 1 (by rfl) ⟨2041250, by rfl⟩ : syracuseStep 2721667 = 4082501) B4082501
theorem B1722259 : Blo 1611004 1722259 := bstep (se 1 (by rfl) ⟨1291694, by rfl⟩ : syracuseStep 1722259 = 2583389) B2583389
theorem B2418593 : Blo 1611004 2418593 := bstep (se 2 (by rfl) ⟨906972, by rfl⟩ : syracuseStep 2418593 = 1813945) B1813945
theorem B2418611 : Blo 1611004 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B2418641 : Blo 1611004 2418641 := bstep (se 2 (by rfl) ⟨906990, by rfl⟩ : syracuseStep 2418641 = 1813981) B1813981
theorem B1812451 : Blo 1611004 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B2418659 : Blo 1611004 2418659 := bstep (se 1 (by rfl) ⟨1813994, by rfl⟩ : syracuseStep 2418659 = 3627989) B3627989
theorem B12240881 : Blo 1611004 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B2418689 : Blo 1611004 2418689 := bstep (se 2 (by rfl) ⟨907008, by rfl⟩ : syracuseStep 2418689 = 1814017) B1814017
theorem B2721809 : Blo 1611004 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B2418707 : Blo 1611004 2418707 := bstep (se 1 (by rfl) ⟨1814030, by rfl⟩ : syracuseStep 2418707 = 3628061) B3628061
theorem B2418737 : Blo 1611004 2418737 := bstep (se 2 (by rfl) ⟨907026, by rfl⟩ : syracuseStep 2418737 = 1814053) B1814053
theorem B2418755 : Blo 1611004 2418755 := bstep (se 1 (by rfl) ⟨1814066, by rfl⟩ : syracuseStep 2418755 = 3628133) B3628133
theorem B2418785 : Blo 1611004 2418785 := bstep (se 2 (by rfl) ⟨907044, by rfl⟩ : syracuseStep 2418785 = 1814089) B1814089
theorem B1812595 : Blo 1611004 1812595 := bstep (se 1 (by rfl) ⟨1359446, by rfl⟩ : syracuseStep 1812595 = 2718893) B2718893
theorem B2418803 : Blo 1611004 2418803 := bstep (se 1 (by rfl) ⟨1814102, by rfl⟩ : syracuseStep 2418803 = 3628205) B3628205
theorem B2418833 : Blo 1611004 2418833 := bstep (se 2 (by rfl) ⟨907062, by rfl⟩ : syracuseStep 2418833 = 1814125) B1814125
theorem B2721937 : Blo 1611004 2721937 := bstep (se 2 (by rfl) ⟨1020726, by rfl⟩ : syracuseStep 2721937 = 2041453) B2041453
theorem B2418851 : Blo 1611004 2418851 := bstep (se 1 (by rfl) ⟨1814138, by rfl⟩ : syracuseStep 2418851 = 3628277) B3628277
theorem B2418881 : Blo 1611004 2418881 := bstep (se 2 (by rfl) ⟨907080, by rfl⟩ : syracuseStep 2418881 = 1814161) B1814161
theorem B5441741 : Blo 1611004 5441741 := bstep (se 3 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 5441741 = 2040653) B2040653
theorem B4081873 : Blo 1611004 4081873 := bstep (se 2 (by rfl) ⟨1530702, by rfl⟩ : syracuseStep 4081873 = 3061405) B3061405
theorem B2418899 : Blo 1611004 2418899 := bstep (se 1 (by rfl) ⟨1814174, by rfl⟩ : syracuseStep 2418899 = 3628349) B3628349
theorem B2418929 : Blo 1611004 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1812739 : Blo 1611004 1812739 := bstep (se 1 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 1812739 = 2719109) B2719109
theorem B5441795 : Blo 1611004 5441795 := bstep (se 1 (by rfl) ⟨4081346, by rfl⟩ : syracuseStep 5441795 = 8162693) B8162693
theorem B2418947 : Blo 1611004 2418947 := bstep (se 1 (by rfl) ⟨1814210, by rfl⟩ : syracuseStep 2418947 = 3628421) B3628421
theorem B2451745 : Blo 1611004 2451745 := bstep (se 2 (by rfl) ⟨919404, by rfl⟩ : syracuseStep 2451745 = 1838809) B1838809
theorem B2418977 : Blo 1611004 2418977 := bstep (se 2 (by rfl) ⟨907116, by rfl⟩ : syracuseStep 2418977 = 1814233) B1814233
theorem B6121763 : Blo 1611004 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B6121777 : Blo 1611004 6121777 := bstep (se 2 (by rfl) ⟨2295666, by rfl⟩ : syracuseStep 6121777 = 4591333) B4591333
theorem B2418995 : Blo 1611004 2418995 := bstep (se 1 (by rfl) ⟨1814246, by rfl⟩ : syracuseStep 2418995 = 3628493) B3628493
theorem B2451793 : Blo 1611004 2451793 := bstep (se 2 (by rfl) ⟨919422, by rfl⟩ : syracuseStep 2451793 = 1838845) B1838845
theorem B2296145 : Blo 1611004 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B2419025 : Blo 1611004 2419025 := bstep (se 2 (by rfl) ⟨907134, by rfl⟩ : syracuseStep 2419025 = 1814269) B1814269
theorem B2419043 : Blo 1611004 2419043 := bstep (se 1 (by rfl) ⟨1814282, by rfl⟩ : syracuseStep 2419043 = 3628565) B3628565
theorem B2419073 : Blo 1611004 2419073 := bstep (se 2 (by rfl) ⟨907152, by rfl⟩ : syracuseStep 2419073 = 1814305) B1814305
theorem B1812883 : Blo 1611004 1812883 := bstep (se 1 (by rfl) ⟨1359662, by rfl⟩ : syracuseStep 1812883 = 2719325) B2719325
theorem B2419091 : Blo 1611004 2419091 := bstep (se 1 (by rfl) ⟨1814318, by rfl⟩ : syracuseStep 2419091 = 3628637) B3628637
theorem B2296225 : Blo 1611004 2296225 := bstep (se 2 (by rfl) ⟨861084, by rfl⟩ : syracuseStep 2296225 = 1722169) B1722169
theorem B2419121 : Blo 1611004 2419121 := bstep (se 2 (by rfl) ⟨907170, by rfl⟩ : syracuseStep 2419121 = 1814341) B1814341
theorem B2419139 : Blo 1611004 2419139 := bstep (se 1 (by rfl) ⟨1814354, by rfl⟩ : syracuseStep 2419139 = 3628709) B3628709
theorem B2419169 : Blo 1611004 2419169 := bstep (se 2 (by rfl) ⟨907188, by rfl⟩ : syracuseStep 2419169 = 1814377) B1814377
theorem B4082147 : Blo 1611004 4082147 := bstep (se 1 (by rfl) ⟨3061610, by rfl⟩ : syracuseStep 4082147 = 6123221) B6123221
theorem B2419187 : Blo 1611004 2419187 := bstep (se 1 (by rfl) ⟨1814390, by rfl⟩ : syracuseStep 2419187 = 3628781) B3628781
theorem B5442065 : Blo 1611004 5442065 := bstep (se 2 (by rfl) ⟨2040774, by rfl⟩ : syracuseStep 5442065 = 4081549) B4081549
theorem B2419217 : Blo 1611004 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B1813027 : Blo 1611004 1813027 := bstep (se 1 (by rfl) ⟨1359770, by rfl⟩ : syracuseStep 1813027 = 2719541) B2719541
theorem B2419235 : Blo 1611004 2419235 := bstep (se 1 (by rfl) ⟨1814426, by rfl⟩ : syracuseStep 2419235 = 3628853) B3628853
theorem B2419265 : Blo 1611004 2419265 := bstep (se 2 (by rfl) ⟨907224, by rfl⟩ : syracuseStep 2419265 = 1814449) B1814449
theorem B9800261 : Blo 1611004 9800261 := bstep (se 4 (by rfl) ⟨918774, by rfl⟩ : syracuseStep 9800261 = 1837549) B1837549
theorem B2419283 : Blo 1611004 2419283 := bstep (se 1 (by rfl) ⟨1814462, by rfl⟩ : syracuseStep 2419283 = 3628925) B3628925
theorem B2419313 : Blo 1611004 2419313 := bstep (se 2 (by rfl) ⟨907242, by rfl⟩ : syracuseStep 2419313 = 1814485) B1814485
theorem B2419331 : Blo 1611004 2419331 := bstep (se 1 (by rfl) ⟨1814498, by rfl⟩ : syracuseStep 2419331 = 3628997) B3628997
theorem B2419361 : Blo 1611004 2419361 := bstep (se 2 (by rfl) ⟨907260, by rfl⟩ : syracuseStep 2419361 = 1814521) B1814521
theorem B4082339 : Blo 1611004 4082339 := bstep (se 1 (by rfl) ⟨3061754, by rfl⟩ : syracuseStep 4082339 = 6123509) B6123509
theorem B1813171 : Blo 1611004 1813171 := bstep (se 1 (by rfl) ⟨1359878, by rfl⟩ : syracuseStep 1813171 = 2719757) B2719757
theorem B2419379 : Blo 1611004 2419379 := bstep (se 1 (by rfl) ⟨1814534, by rfl⟩ : syracuseStep 2419379 = 3629069) B3629069
theorem B2419409 : Blo 1611004 2419409 := bstep (se 2 (by rfl) ⟨907278, by rfl⟩ : syracuseStep 2419409 = 1814557) B1814557
theorem B2419427 : Blo 1611004 2419427 := bstep (se 1 (by rfl) ⟨1814570, by rfl⟩ : syracuseStep 2419427 = 3629141) B3629141
theorem B2419457 : Blo 1611004 2419457 := bstep (se 2 (by rfl) ⟨907296, by rfl⟩ : syracuseStep 2419457 = 1814593) B1814593
theorem B8719109 : Blo 1611004 8719109 := bstep (se 4 (by rfl) ⟨817416, by rfl⟩ : syracuseStep 8719109 = 1634833) B1634833
theorem B2419475 : Blo 1611004 2419475 := bstep (se 1 (by rfl) ⟨1814606, by rfl⟩ : syracuseStep 2419475 = 3629213) B3629213
theorem B2419505 : Blo 1611004 2419505 := bstep (se 2 (by rfl) ⟨907314, by rfl⟩ : syracuseStep 2419505 = 1814629) B1814629
theorem B1813315 : Blo 1611004 1813315 := bstep (se 1 (by rfl) ⟨1359986, by rfl⟩ : syracuseStep 1813315 = 2719973) B2719973
theorem B4590445 : Blo 1611004 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B5163917 : Blo 1611004 5163917 := bstep (se 3 (by rfl) ⟨968234, by rfl⟩ : syracuseStep 5163917 = 1936469) B1936469
theorem B9178019 : Blo 1611004 9178019 := bstep (se 1 (by rfl) ⟨6883514, by rfl⟩ : syracuseStep 9178019 = 13767029) B13767029
theorem B1813459 : Blo 1611004 1813459 := bstep (se 1 (by rfl) ⟨1360094, by rfl⟩ : syracuseStep 1813459 = 2720189) B2720189
theorem B2452499 : Blo 1611004 2452499 := bstep (se 1 (by rfl) ⟨1839374, by rfl⟩ : syracuseStep 2452499 = 3678749) B3678749
theorem B4901933 : Blo 1611004 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B5442605 : Blo 1611004 5442605 := bstep (se 3 (by rfl) ⟨1020488, by rfl⟩ : syracuseStep 5442605 = 2040977) B2040977
theorem B2903089 : Blo 1611004 2903089 := bstep (se 2 (by rfl) ⟨1088658, by rfl⟩ : syracuseStep 2903089 = 2177317) B2177317
theorem B10325069 : Blo 1611004 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B1813603 : Blo 1611004 1813603 := bstep (se 1 (by rfl) ⟨1360202, by rfl⟩ : syracuseStep 1813603 = 2720405) B2720405
theorem B5442659 : Blo 1611004 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B15486065 : Blo 1611004 15486065 := bstep (se 2 (by rfl) ⟨5807274, by rfl⟩ : syracuseStep 15486065 = 11614549) B11614549
theorem B4902029 : Blo 1611004 4902029 := bstep (se 3 (by rfl) ⟨919130, by rfl⟩ : syracuseStep 4902029 = 1838261) B1838261
theorem B8162531 : Blo 1611004 8162531 := bstep (se 1 (by rfl) ⟨6121898, by rfl⟩ : syracuseStep 8162531 = 12243797) B12243797
theorem B1813747 : Blo 1611004 1813747 := bstep (se 1 (by rfl) ⟨1360310, by rfl⟩ : syracuseStep 1813747 = 2720621) B2720621
theorem B3443971 : Blo 1611004 3443971 := bstep (se 1 (by rfl) ⟨2582978, by rfl⟩ : syracuseStep 3443971 = 5165957) B5165957
theorem B4967729 : Blo 1611004 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B5442929 : Blo 1611004 5442929 := bstep (se 2 (by rfl) ⟨2041098, by rfl⟩ : syracuseStep 5442929 = 4082197) B4082197
theorem B1813891 : Blo 1611004 1813891 := bstep (se 1 (by rfl) ⟨1360418, by rfl⟩ : syracuseStep 1813891 = 2720837) B2720837
theorem B17419661 : Blo 1611004 17419661 := bstep (se 3 (by rfl) ⟨3266186, by rfl⟩ : syracuseStep 17419661 = 6532373) B6532373
theorem B35401157 : Blo 1611004 35401157 := bstep (se 4 (by rfl) ⟨3318858, by rfl⟩ : syracuseStep 35401157 = 6637717) B6637717
theorem B6884813 : Blo 1611004 6884813 := bstep (se 3 (by rfl) ⟨1290902, by rfl⟩ : syracuseStep 6884813 = 2581805) B2581805
theorem B3059203 : Blo 1611004 3059203 := bstep (se 1 (by rfl) ⟨2294402, by rfl⟩ : syracuseStep 3059203 = 4588805) B4588805
theorem B1814035 : Blo 1611004 1814035 := bstep (se 1 (by rfl) ⟨1360526, by rfl⟩ : syracuseStep 1814035 = 2721053) B2721053
theorem B3059363 : Blo 1611004 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B1814179 : Blo 1611004 1814179 := bstep (se 1 (by rfl) ⟨1360634, by rfl⟩ : syracuseStep 1814179 = 2721269) B2721269
theorem B6123235 : Blo 1611004 6123235 := bstep (se 1 (by rfl) ⟨4592426, by rfl⟩ : syracuseStep 6123235 = 9184853) B9184853
theorem B6885155 : Blo 1611004 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B1814323 : Blo 1611004 1814323 := bstep (se 1 (by rfl) ⟨1360742, by rfl⟩ : syracuseStep 1814323 = 2721485) B2721485
theorem B3624785 : Blo 1611004 3624785 := bstep (se 2 (by rfl) ⟨1359294, by rfl⟩ : syracuseStep 3624785 = 2718589) B2718589
theorem B3624803 : Blo 1611004 3624803 := bstep (se 1 (by rfl) ⟨2718602, by rfl⟩ : syracuseStep 3624803 = 5437205) B5437205
theorem B9179021 : Blo 1611004 9179021 := bstep (se 3 (by rfl) ⟨1721066, by rfl⟩ : syracuseStep 9179021 = 3442133) B3442133
theorem B5443469 : Blo 1611004 5443469 := bstep (se 3 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 5443469 = 2041301) B2041301
theorem B4591505 : Blo 1611004 4591505 := bstep (se 2 (by rfl) ⟨1721814, by rfl⟩ : syracuseStep 4591505 = 3443629) B3443629
theorem B1937315 : Blo 1611004 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B1814467 : Blo 1611004 1814467 := bstep (se 1 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 1814467 = 2721701) B2721701
theorem B5443523 : Blo 1611004 5443523 := bstep (se 1 (by rfl) ⟨4082642, by rfl⟩ : syracuseStep 5443523 = 8165285) B8165285
theorem B1937363 : Blo 1611004 1937363 := bstep (se 1 (by rfl) ⟨1453022, by rfl⟩ : syracuseStep 1937363 = 2906045) B2906045
theorem B13774819 : Blo 1611004 13774819 := bstep (se 1 (by rfl) ⟨10331114, by rfl⟩ : syracuseStep 13774819 = 20662229) B20662229
theorem B8163341 : Blo 1611004 8163341 := bstep (se 3 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 8163341 = 3061253) B3061253
theorem B10334243 : Blo 1611004 10334243 := bstep (se 1 (by rfl) ⟨7750682, by rfl⟩ : syracuseStep 10334243 = 15501365) B15501365
theorem B1814611 : Blo 1611004 1814611 := bstep (se 1 (by rfl) ⟨1360958, by rfl⟩ : syracuseStep 1814611 = 2721917) B2721917
theorem B3625073 : Blo 1611004 3625073 := bstep (se 2 (by rfl) ⟨1359402, by rfl⟩ : syracuseStep 3625073 = 2718805) B2718805
theorem B3625091 : Blo 1611004 3625091 := bstep (se 1 (by rfl) ⟨2718818, by rfl⟩ : syracuseStep 3625091 = 5437637) B5437637
theorem B27914381 : Blo 1611004 27914381 := bstep (se 3 (by rfl) ⟨5233946, by rfl⟩ : syracuseStep 27914381 = 10467893) B10467893
theorem B5443793 : Blo 1611004 5443793 := bstep (se 2 (by rfl) ⟨2041422, by rfl⟩ : syracuseStep 5443793 = 4082845) B4082845
theorem B3625361 : Blo 1611004 3625361 := bstep (se 2 (by rfl) ⟨1359510, by rfl⟩ : syracuseStep 3625361 = 2719021) B2719021
theorem B3625379 : Blo 1611004 3625379 := bstep (se 1 (by rfl) ⟨2719034, by rfl⟩ : syracuseStep 3625379 = 5438069) B5438069
theorem B5165507 : Blo 1611004 5165507 := bstep (se 1 (by rfl) ⟨3874130, by rfl⟩ : syracuseStep 5165507 = 7748261) B7748261
theorem B19124677 : Blo 1611004 19124677 := bstep (se 4 (by rfl) ⟨1792938, by rfl⟩ : syracuseStep 19124677 = 3585877) B3585877
theorem B4592177 : Blo 1611004 4592177 := bstep (se 2 (by rfl) ⟨1722066, by rfl⟩ : syracuseStep 4592177 = 3444133) B3444133
theorem B42463885 : Blo 1611004 42463885 := bstep (se 3 (by rfl) ⟨7961978, by rfl⟩ : syracuseStep 42463885 = 15923957) B15923957
theorem B1634963 : Blo 1611004 1634963 := bstep (se 1 (by rfl) ⟨1226222, by rfl⟩ : syracuseStep 1634963 = 2452445) B2452445
theorem B3625649 : Blo 1611004 3625649 := bstep (se 2 (by rfl) ⟨1359618, by rfl⟩ : syracuseStep 3625649 = 2719237) B2719237
theorem B3625667 : Blo 1611004 3625667 := bstep (se 1 (by rfl) ⟨2719250, by rfl⟩ : syracuseStep 3625667 = 5438501) B5438501
theorem B3060433 : Blo 1611004 3060433 := bstep (se 2 (by rfl) ⟨1147662, by rfl⟩ : syracuseStep 3060433 = 2295325) B2295325
theorem B27529955 : Blo 1611004 27529955 := bstep (se 1 (by rfl) ⟨20647466, by rfl⟩ : syracuseStep 27529955 = 41294933) B41294933
theorem B8155889 : Blo 1611004 8155889 := bstep (se 2 (by rfl) ⟨3058458, by rfl⟩ : syracuseStep 8155889 = 6116917) B6116917
theorem B7353101 : Blo 1611004 7353101 := bstep (se 3 (by rfl) ⟨1378706, by rfl⟩ : syracuseStep 7353101 = 2757413) B2757413
theorem B92943125 : Blo 1611004 92943125 := bstep (se 6 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 92943125 = 4356709) B4356709
theorem B5813041 : Blo 1611004 5813041 := bstep (se 2 (by rfl) ⟨2179890, by rfl⟩ : syracuseStep 5813041 = 4359781) B4359781
theorem B3871651 : Blo 1611004 3871651 := bstep (se 1 (by rfl) ⟨2903738, by rfl⟩ : syracuseStep 3871651 = 5807477) B5807477
theorem B3625937 : Blo 1611004 3625937 := bstep (se 2 (by rfl) ⟨1359726, by rfl⟩ : syracuseStep 3625937 = 2719453) B2719453
theorem B3625955 : Blo 1611004 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B3626225 : Blo 1611004 3626225 := bstep (se 2 (by rfl) ⟨1359834, by rfl⟩ : syracuseStep 3626225 = 2719669) B2719669
theorem B1611011 : Blo 1611004 1611011 := bstep (se 1 (by rfl) ⟨1208258, by rfl⟩ : syracuseStep 1611011 = 2416517) B2416517
theorem B3626243 : Blo 1611004 3626243 := bstep (se 1 (by rfl) ⟨2719682, by rfl⟩ : syracuseStep 3626243 = 5439365) B5439365
theorem B1611027 : Blo 1611004 1611027 := bstep (se 1 (by rfl) ⟨1208270, by rfl⟩ : syracuseStep 1611027 = 2416541) B2416541
theorem B1611043 : Blo 1611004 1611043 := bstep (se 1 (by rfl) ⟨1208282, by rfl⟩ : syracuseStep 1611043 = 2416565) B2416565
theorem B6534449 : Blo 1611004 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B1611059 : Blo 1611004 1611059 := bstep (se 1 (by rfl) ⟨1208294, by rfl⟩ : syracuseStep 1611059 = 2416589) B2416589
theorem B1611075 : Blo 1611004 1611075 := bstep (se 1 (by rfl) ⟨1208306, by rfl⟩ : syracuseStep 1611075 = 2416613) B2416613
theorem B4592963 : Blo 1611004 4592963 := bstep (se 1 (by rfl) ⟨3444722, by rfl⟩ : syracuseStep 4592963 = 6889445) B6889445
theorem B1611091 : Blo 1611004 1611091 := bstep (se 1 (by rfl) ⟨1208318, by rfl⟩ : syracuseStep 1611091 = 2416637) B2416637
theorem B1611107 : Blo 1611004 1611107 := bstep (se 1 (by rfl) ⟨1208330, by rfl⟩ : syracuseStep 1611107 = 2416661) B2416661
theorem B1611123 : Blo 1611004 1611123 := bstep (se 1 (by rfl) ⟨1208342, by rfl⟩ : syracuseStep 1611123 = 2416685) B2416685
theorem B1611139 : Blo 1611004 1611139 := bstep (se 1 (by rfl) ⟨1208354, by rfl⟩ : syracuseStep 1611139 = 2416709) B2416709
theorem B3102097 : Blo 1611004 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B1611155 : Blo 1611004 1611155 := bstep (se 1 (by rfl) ⟨1208366, by rfl⟩ : syracuseStep 1611155 = 2416733) B2416733
theorem B1611171 : Blo 1611004 1611171 := bstep (se 1 (by rfl) ⟨1208378, by rfl⟩ : syracuseStep 1611171 = 2416757) B2416757
theorem B1611187 : Blo 1611004 1611187 := bstep (se 1 (by rfl) ⟨1208390, by rfl⟩ : syracuseStep 1611187 = 2416781) B2416781
theorem B1611203 : Blo 1611004 1611203 := bstep (se 1 (by rfl) ⟨1208402, by rfl⟩ : syracuseStep 1611203 = 2416805) B2416805
theorem B8828365 : Blo 1611004 8828365 := bstep (se 3 (by rfl) ⟨1655318, by rfl⟩ : syracuseStep 8828365 = 3310637) B3310637
theorem B1611219 : Blo 1611004 1611219 := bstep (se 1 (by rfl) ⟨1208414, by rfl⟩ : syracuseStep 1611219 = 2416829) B2416829
theorem B2618849 : Blo 1611004 2618849 := bstep (se 2 (by rfl) ⟨982068, by rfl⟩ : syracuseStep 2618849 = 1964137) B1964137
theorem B1611235 : Blo 1611004 1611235 := bstep (se 1 (by rfl) ⟨1208426, by rfl⟩ : syracuseStep 1611235 = 2416853) B2416853
theorem B1611251 : Blo 1611004 1611251 := bstep (se 1 (by rfl) ⟨1208438, by rfl⟩ : syracuseStep 1611251 = 2416877) B2416877
theorem B1611267 : Blo 1611004 1611267 := bstep (se 1 (by rfl) ⟨1208450, by rfl⟩ : syracuseStep 1611267 = 2416901) B2416901
theorem B3626513 : Blo 1611004 3626513 := bstep (se 2 (by rfl) ⟨1359942, by rfl⟩ : syracuseStep 3626513 = 2719885) B2719885
theorem B1611283 : Blo 1611004 1611283 := bstep (se 1 (by rfl) ⟨1208462, by rfl⟩ : syracuseStep 1611283 = 2416925) B2416925
theorem B1611299 : Blo 1611004 1611299 := bstep (se 1 (by rfl) ⟨1208474, by rfl⟩ : syracuseStep 1611299 = 2416949) B2416949
theorem B3626531 : Blo 1611004 3626531 := bstep (se 1 (by rfl) ⟨2719898, by rfl⟩ : syracuseStep 3626531 = 5439797) B5439797
theorem B1611315 : Blo 1611004 1611315 := bstep (se 1 (by rfl) ⟨1208486, by rfl⟩ : syracuseStep 1611315 = 2416973) B2416973
theorem B1611331 : Blo 1611004 1611331 := bstep (se 1 (by rfl) ⟨1208498, by rfl⟩ : syracuseStep 1611331 = 2416997) B2416997
theorem B3872323 : Blo 1611004 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B1611347 : Blo 1611004 1611347 := bstep (se 1 (by rfl) ⟨1208510, by rfl⟩ : syracuseStep 1611347 = 2417021) B2417021
theorem B1611363 : Blo 1611004 1611363 := bstep (se 1 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 1611363 = 2417045) B2417045
theorem B1611379 : Blo 1611004 1611379 := bstep (se 1 (by rfl) ⟨1208534, by rfl⟩ : syracuseStep 1611379 = 2417069) B2417069
theorem B1611395 : Blo 1611004 1611395 := bstep (se 1 (by rfl) ⟨1208546, by rfl⟩ : syracuseStep 1611395 = 2417093) B2417093
theorem B5166737 : Blo 1611004 5166737 := bstep (se 2 (by rfl) ⟨1937526, by rfl⟩ : syracuseStep 5166737 = 3875053) B3875053
theorem B1611411 : Blo 1611004 1611411 := bstep (se 1 (by rfl) ⟨1208558, by rfl⟩ : syracuseStep 1611411 = 2417117) B2417117
theorem B1611427 : Blo 1611004 1611427 := bstep (se 1 (by rfl) ⟨1208570, by rfl⟩ : syracuseStep 1611427 = 2417141) B2417141
theorem B1611443 : Blo 1611004 1611443 := bstep (se 1 (by rfl) ⟨1208582, by rfl⟩ : syracuseStep 1611443 = 2417165) B2417165
theorem B1611459 : Blo 1611004 1611459 := bstep (se 1 (by rfl) ⟨1208594, by rfl⟩ : syracuseStep 1611459 = 2417189) B2417189
theorem B1611475 : Blo 1611004 1611475 := bstep (se 1 (by rfl) ⟨1208606, by rfl⟩ : syracuseStep 1611475 = 2417213) B2417213
theorem B11024099 : Blo 1611004 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B1611491 : Blo 1611004 1611491 := bstep (se 1 (by rfl) ⟨1208618, by rfl⟩ : syracuseStep 1611491 = 2417237) B2417237
theorem B3061489 : Blo 1611004 3061489 := bstep (se 2 (by rfl) ⟨1148058, by rfl⟩ : syracuseStep 3061489 = 2296117) B2296117
theorem B1611507 : Blo 1611004 1611507 := bstep (se 1 (by rfl) ⟨1208630, by rfl⟩ : syracuseStep 1611507 = 2417261) B2417261
theorem B1611523 : Blo 1611004 1611523 := bstep (se 1 (by rfl) ⟨1208642, by rfl⟩ : syracuseStep 1611523 = 2417285) B2417285
theorem B1611539 : Blo 1611004 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B1611555 : Blo 1611004 1611555 := bstep (se 1 (by rfl) ⟨1208666, by rfl⟩ : syracuseStep 1611555 = 2417333) B2417333
theorem B3626801 : Blo 1611004 3626801 := bstep (se 2 (by rfl) ⟨1360050, by rfl⟩ : syracuseStep 3626801 = 2720101) B2720101
theorem B1611571 : Blo 1611004 1611571 := bstep (se 1 (by rfl) ⟨1208678, by rfl⟩ : syracuseStep 1611571 = 2417357) B2417357
theorem B1611587 : Blo 1611004 1611587 := bstep (se 1 (by rfl) ⟨1208690, by rfl⟩ : syracuseStep 1611587 = 2417381) B2417381
theorem B3626819 : Blo 1611004 3626819 := bstep (se 1 (by rfl) ⟨2720114, by rfl⟩ : syracuseStep 3626819 = 5440229) B5440229
theorem B1611603 : Blo 1611004 1611603 := bstep (se 1 (by rfl) ⟨1208702, by rfl⟩ : syracuseStep 1611603 = 2417405) B2417405
theorem B1611619 : Blo 1611004 1611619 := bstep (se 1 (by rfl) ⟨1208714, by rfl⟩ : syracuseStep 1611619 = 2417429) B2417429
theorem B1611635 : Blo 1611004 1611635 := bstep (se 1 (by rfl) ⟨1208726, by rfl⟩ : syracuseStep 1611635 = 2417453) B2417453
theorem B1611651 : Blo 1611004 1611651 := bstep (se 1 (by rfl) ⟨1208738, by rfl⟩ : syracuseStep 1611651 = 2417477) B2417477
theorem B1611667 : Blo 1611004 1611667 := bstep (se 1 (by rfl) ⟨1208750, by rfl⟩ : syracuseStep 1611667 = 2417501) B2417501
theorem B1611683 : Blo 1611004 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B1611699 : Blo 1611004 1611699 := bstep (se 1 (by rfl) ⟨1208774, by rfl⟩ : syracuseStep 1611699 = 2417549) B2417549
theorem B1611715 : Blo 1611004 1611715 := bstep (se 1 (by rfl) ⟨1208786, by rfl⟩ : syracuseStep 1611715 = 2417573) B2417573
theorem B1611731 : Blo 1611004 1611731 := bstep (se 1 (by rfl) ⟨1208798, by rfl⟩ : syracuseStep 1611731 = 2417597) B2417597
theorem B1611747 : Blo 1611004 1611747 := bstep (se 1 (by rfl) ⟨1208810, by rfl⟩ : syracuseStep 1611747 = 2417621) B2417621
theorem B5437421 : Blo 1611004 5437421 := bstep (se 3 (by rfl) ⟨1019516, by rfl⟩ : syracuseStep 5437421 = 2039033) B2039033
theorem B1611763 : Blo 1611004 1611763 := bstep (se 1 (by rfl) ⟨1208822, by rfl⟩ : syracuseStep 1611763 = 2417645) B2417645
theorem B1611779 : Blo 1611004 1611779 := bstep (se 1 (by rfl) ⟨1208834, by rfl⟩ : syracuseStep 1611779 = 2417669) B2417669
theorem B6117389 : Blo 1611004 6117389 := bstep (se 3 (by rfl) ⟨1147010, by rfl⟩ : syracuseStep 6117389 = 2294021) B2294021
theorem B6535181 : Blo 1611004 6535181 := bstep (se 3 (by rfl) ⟨1225346, by rfl⟩ : syracuseStep 6535181 = 2450693) B2450693
theorem B3872785 : Blo 1611004 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B1611795 : Blo 1611004 1611795 := bstep (se 1 (by rfl) ⟨1208846, by rfl⟩ : syracuseStep 1611795 = 2417693) B2417693
theorem B5437475 : Blo 1611004 5437475 := bstep (se 1 (by rfl) ⟨4078106, by rfl⟩ : syracuseStep 5437475 = 8156213) B8156213
theorem B1611811 : Blo 1611004 1611811 := bstep (se 1 (by rfl) ⟨1208858, by rfl⟩ : syracuseStep 1611811 = 2417717) B2417717
theorem B1611827 : Blo 1611004 1611827 := bstep (se 1 (by rfl) ⟨1208870, by rfl⟩ : syracuseStep 1611827 = 2417741) B2417741
theorem B1611843 : Blo 1611004 1611843 := bstep (se 1 (by rfl) ⟨1208882, by rfl⟩ : syracuseStep 1611843 = 2417765) B2417765
theorem B3627089 : Blo 1611004 3627089 := bstep (se 2 (by rfl) ⟨1360158, by rfl⟩ : syracuseStep 3627089 = 2720317) B2720317
theorem B1611859 : Blo 1611004 1611859 := bstep (se 1 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 1611859 = 2417789) B2417789
theorem B1611875 : Blo 1611004 1611875 := bstep (se 1 (by rfl) ⟨1208906, by rfl⟩ : syracuseStep 1611875 = 2417813) B2417813
theorem B3627107 : Blo 1611004 3627107 := bstep (se 1 (by rfl) ⟨2720330, by rfl⟩ : syracuseStep 3627107 = 5440661) B5440661
theorem B3872881 : Blo 1611004 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B1611891 : Blo 1611004 1611891 := bstep (se 1 (by rfl) ⟨1208918, by rfl⟩ : syracuseStep 1611891 = 2417837) B2417837
theorem B1611907 : Blo 1611004 1611907 := bstep (se 1 (by rfl) ⟨1208930, by rfl⟩ : syracuseStep 1611907 = 2417861) B2417861
theorem B3061891 : Blo 1611004 3061891 := bstep (se 1 (by rfl) ⟨2296418, by rfl⟩ : syracuseStep 3061891 = 4592837) B4592837
theorem B1611923 : Blo 1611004 1611923 := bstep (se 1 (by rfl) ⟨1208942, by rfl⟩ : syracuseStep 1611923 = 2417885) B2417885
theorem B8157347 : Blo 1611004 8157347 := bstep (se 1 (by rfl) ⟨6118010, by rfl⟩ : syracuseStep 8157347 = 12236021) B12236021
theorem B1611939 : Blo 1611004 1611939 := bstep (se 1 (by rfl) ⟨1208954, by rfl⟩ : syracuseStep 1611939 = 2417909) B2417909
theorem B3061937 : Blo 1611004 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B1611955 : Blo 1611004 1611955 := bstep (se 1 (by rfl) ⟨1208966, by rfl⟩ : syracuseStep 1611955 = 2417933) B2417933
theorem B1611971 : Blo 1611004 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B1611987 : Blo 1611004 1611987 := bstep (se 1 (by rfl) ⟨1208990, by rfl⟩ : syracuseStep 1611987 = 2417981) B2417981
theorem B1612003 : Blo 1611004 1612003 := bstep (se 1 (by rfl) ⟨1209002, by rfl⟩ : syracuseStep 1612003 = 2418005) B2418005
theorem B1612019 : Blo 1611004 1612019 := bstep (se 1 (by rfl) ⟨1209014, by rfl⟩ : syracuseStep 1612019 = 2418029) B2418029
theorem B3266819 : Blo 1611004 3266819 := bstep (se 1 (by rfl) ⟨2450114, by rfl⟩ : syracuseStep 3266819 = 4900229) B4900229
theorem B1612035 : Blo 1611004 1612035 := bstep (se 1 (by rfl) ⟨1209026, by rfl⟩ : syracuseStep 1612035 = 2418053) B2418053
theorem B1612051 : Blo 1611004 1612051 := bstep (se 1 (by rfl) ⟨1209038, by rfl⟩ : syracuseStep 1612051 = 2418077) B2418077
theorem B1612067 : Blo 1611004 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B5437745 : Blo 1611004 5437745 := bstep (se 2 (by rfl) ⟨2039154, by rfl⟩ : syracuseStep 5437745 = 4078309) B4078309
theorem B1612083 : Blo 1611004 1612083 := bstep (se 1 (by rfl) ⟨1209062, by rfl⟩ : syracuseStep 1612083 = 2418125) B2418125
theorem B1612099 : Blo 1611004 1612099 := bstep (se 1 (by rfl) ⟨1209074, by rfl⟩ : syracuseStep 1612099 = 2418149) B2418149
theorem B2906435 : Blo 1611004 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B1612115 : Blo 1611004 1612115 := bstep (se 1 (by rfl) ⟨1209086, by rfl⟩ : syracuseStep 1612115 = 2418173) B2418173
theorem B1612131 : Blo 1611004 1612131 := bstep (se 1 (by rfl) ⟨1209098, by rfl⟩ : syracuseStep 1612131 = 2418197) B2418197
theorem B3627377 : Blo 1611004 3627377 := bstep (se 2 (by rfl) ⟨1360266, by rfl⟩ : syracuseStep 3627377 = 2720533) B2720533
theorem B1612147 : Blo 1611004 1612147 := bstep (se 1 (by rfl) ⟨1209110, by rfl⟩ : syracuseStep 1612147 = 2418221) B2418221
theorem B1612163 : Blo 1611004 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B3627395 : Blo 1611004 3627395 := bstep (se 1 (by rfl) ⟨2720546, by rfl⟩ : syracuseStep 3627395 = 5441093) B5441093
theorem B11622797 : Blo 1611004 11622797 := bstep (se 3 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 11622797 = 4358549) B4358549
theorem B1612179 : Blo 1611004 1612179 := bstep (se 1 (by rfl) ⟨1209134, by rfl⟩ : syracuseStep 1612179 = 2418269) B2418269
theorem B1612195 : Blo 1611004 1612195 := bstep (se 1 (by rfl) ⟨1209146, by rfl⟩ : syracuseStep 1612195 = 2418293) B2418293
theorem B1612211 : Blo 1611004 1612211 := bstep (se 1 (by rfl) ⟨1209158, by rfl⟩ : syracuseStep 1612211 = 2418317) B2418317
theorem B1612227 : Blo 1611004 1612227 := bstep (se 1 (by rfl) ⟨1209170, by rfl⟩ : syracuseStep 1612227 = 2418341) B2418341
theorem B1612243 : Blo 1611004 1612243 := bstep (se 1 (by rfl) ⟨1209182, by rfl⟩ : syracuseStep 1612243 = 2418365) B2418365
theorem B1612259 : Blo 1611004 1612259 := bstep (se 1 (by rfl) ⟨1209194, by rfl⟩ : syracuseStep 1612259 = 2418389) B2418389
theorem B1612275 : Blo 1611004 1612275 := bstep (se 1 (by rfl) ⟨1209206, by rfl⟩ : syracuseStep 1612275 = 2418413) B2418413
theorem B1612291 : Blo 1611004 1612291 := bstep (se 1 (by rfl) ⟨1209218, by rfl⟩ : syracuseStep 1612291 = 2418437) B2418437
theorem B4078097 : Blo 1611004 4078097 := bstep (se 2 (by rfl) ⟨1529286, by rfl⟩ : syracuseStep 4078097 = 3058573) B3058573
theorem B4356625 : Blo 1611004 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B1612307 : Blo 1611004 1612307 := bstep (se 1 (by rfl) ⟨1209230, by rfl⟩ : syracuseStep 1612307 = 2418461) B2418461
theorem B1612323 : Blo 1611004 1612323 := bstep (se 1 (by rfl) ⟨1209242, by rfl⟩ : syracuseStep 1612323 = 2418485) B2418485
theorem B1612339 : Blo 1611004 1612339 := bstep (se 1 (by rfl) ⟨1209254, by rfl⟩ : syracuseStep 1612339 = 2418509) B2418509
theorem B4078147 : Blo 1611004 4078147 := bstep (se 1 (by rfl) ⟨3058610, by rfl⟩ : syracuseStep 4078147 = 6117221) B6117221
theorem B1612355 : Blo 1611004 1612355 := bstep (se 1 (by rfl) ⟨1209266, by rfl⟩ : syracuseStep 1612355 = 2418533) B2418533
theorem B1612371 : Blo 1611004 1612371 := bstep (se 1 (by rfl) ⟨1209278, by rfl⟩ : syracuseStep 1612371 = 2418557) B2418557
theorem B1612387 : Blo 1611004 1612387 := bstep (se 1 (by rfl) ⟨1209290, by rfl⟩ : syracuseStep 1612387 = 2418581) B2418581
theorem B1612403 : Blo 1611004 1612403 := bstep (se 1 (by rfl) ⟨1209302, by rfl⟩ : syracuseStep 1612403 = 2418605) B2418605
theorem B1612419 : Blo 1611004 1612419 := bstep (se 1 (by rfl) ⟨1209314, by rfl⟩ : syracuseStep 1612419 = 2418629) B2418629
theorem B3627665 : Blo 1611004 3627665 := bstep (se 2 (by rfl) ⟨1360374, by rfl⟩ : syracuseStep 3627665 = 2720749) B2720749
theorem B1612435 : Blo 1611004 1612435 := bstep (se 1 (by rfl) ⟨1209326, by rfl⟩ : syracuseStep 1612435 = 2418653) B2418653
theorem B3627683 : Blo 1611004 3627683 := bstep (se 1 (by rfl) ⟨2720762, by rfl⟩ : syracuseStep 3627683 = 5441525) B5441525
theorem B1612451 : Blo 1611004 1612451 := bstep (se 1 (by rfl) ⟨1209338, by rfl⟩ : syracuseStep 1612451 = 2418677) B2418677
theorem B1612467 : Blo 1611004 1612467 := bstep (se 1 (by rfl) ⟨1209350, by rfl⟩ : syracuseStep 1612467 = 2418701) B2418701
theorem B1612483 : Blo 1611004 1612483 := bstep (se 1 (by rfl) ⟨1209362, by rfl⟩ : syracuseStep 1612483 = 2418725) B2418725
theorem B4078289 : Blo 1611004 4078289 := bstep (se 2 (by rfl) ⟨1529358, by rfl⟩ : syracuseStep 4078289 = 3058717) B3058717
theorem B1612499 : Blo 1611004 1612499 := bstep (se 1 (by rfl) ⟨1209374, by rfl⟩ : syracuseStep 1612499 = 2418749) B2418749
theorem B1612515 : Blo 1611004 1612515 := bstep (se 1 (by rfl) ⟨1209386, by rfl⟩ : syracuseStep 1612515 = 2418773) B2418773
theorem B9427697 : Blo 1611004 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B9181937 : Blo 1611004 9181937 := bstep (se 2 (by rfl) ⟨3443226, by rfl⟩ : syracuseStep 9181937 = 6886453) B6886453
theorem B1612531 : Blo 1611004 1612531 := bstep (se 1 (by rfl) ⟨1209398, by rfl⟩ : syracuseStep 1612531 = 2418797) B2418797
theorem B1612547 : Blo 1611004 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B9075469 : Blo 1611004 9075469 := bstep (se 3 (by rfl) ⟨1701650, by rfl⟩ : syracuseStep 9075469 = 3403301) B3403301
theorem B1612563 : Blo 1611004 1612563 := bstep (se 1 (by rfl) ⟨1209422, by rfl⟩ : syracuseStep 1612563 = 2418845) B2418845
theorem B1612579 : Blo 1611004 1612579 := bstep (se 1 (by rfl) ⟨1209434, by rfl⟩ : syracuseStep 1612579 = 2418869) B2418869
theorem B6118193 : Blo 1611004 6118193 := bstep (se 2 (by rfl) ⟨2294322, by rfl⟩ : syracuseStep 6118193 = 4588645) B4588645
theorem B1612595 : Blo 1611004 1612595 := bstep (se 1 (by rfl) ⟨1209446, by rfl⟩ : syracuseStep 1612595 = 2418893) B2418893
theorem B1612611 : Blo 1611004 1612611 := bstep (se 1 (by rfl) ⟨1209458, by rfl⟩ : syracuseStep 1612611 = 2418917) B2418917
theorem B5438285 : Blo 1611004 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B1612627 : Blo 1611004 1612627 := bstep (se 1 (by rfl) ⟨1209470, by rfl⟩ : syracuseStep 1612627 = 2418941) B2418941
theorem B1612643 : Blo 1611004 1612643 := bstep (se 1 (by rfl) ⟨1209482, by rfl⟩ : syracuseStep 1612643 = 2418965) B2418965
theorem B1612659 : Blo 1611004 1612659 := bstep (se 1 (by rfl) ⟨1209494, by rfl⟩ : syracuseStep 1612659 = 2418989) B2418989
theorem B5438339 : Blo 1611004 5438339 := bstep (se 1 (by rfl) ⟨4078754, by rfl⟩ : syracuseStep 5438339 = 8157509) B8157509
theorem B2177923 : Blo 1611004 2177923 := bstep (se 1 (by rfl) ⟨1633442, by rfl⟩ : syracuseStep 2177923 = 3266885) B3266885
theorem B1612675 : Blo 1611004 1612675 := bstep (se 1 (by rfl) ⟨1209506, by rfl⟩ : syracuseStep 1612675 = 2419013) B2419013
theorem B25156493 : Blo 1611004 25156493 := bstep (se 3 (by rfl) ⟨4716842, by rfl⟩ : syracuseStep 25156493 = 9433685) B9433685
theorem B1612691 : Blo 1611004 1612691 := bstep (se 1 (by rfl) ⟨1209518, by rfl⟩ : syracuseStep 1612691 = 2419037) B2419037
theorem B1612707 : Blo 1611004 1612707 := bstep (se 1 (by rfl) ⟨1209530, by rfl⟩ : syracuseStep 1612707 = 2419061) B2419061
theorem B3980209 : Blo 1611004 3980209 := bstep (se 2 (by rfl) ⟨1492578, by rfl⟩ : syracuseStep 3980209 = 2985157) B2985157
theorem B3627953 : Blo 1611004 3627953 := bstep (se 2 (by rfl) ⟨1360482, by rfl⟩ : syracuseStep 3627953 = 2720965) B2720965
theorem B2718643 : Blo 1611004 2718643 := bstep (se 1 (by rfl) ⟨2038982, by rfl⟩ : syracuseStep 2718643 = 4077965) B4077965
theorem B1612723 : Blo 1611004 1612723 := bstep (se 1 (by rfl) ⟨1209542, by rfl⟩ : syracuseStep 1612723 = 2419085) B2419085
theorem B3627971 : Blo 1611004 3627971 := bstep (se 1 (by rfl) ⟨2720978, by rfl⟩ : syracuseStep 3627971 = 5441957) B5441957
theorem B1612739 : Blo 1611004 1612739 := bstep (se 1 (by rfl) ⟨1209554, by rfl⟩ : syracuseStep 1612739 = 2419109) B2419109
theorem B8158157 : Blo 1611004 8158157 := bstep (se 3 (by rfl) ⟨1529654, by rfl⟩ : syracuseStep 8158157 = 3059309) B3059309
theorem B1612755 : Blo 1611004 1612755 := bstep (se 1 (by rfl) ⟨1209566, by rfl⟩ : syracuseStep 1612755 = 2419133) B2419133
theorem B44104675 : Blo 1611004 44104675 := bstep (se 1 (by rfl) ⟨33078506, by rfl⟩ : syracuseStep 44104675 = 66157013) B66157013
theorem B1612771 : Blo 1611004 1612771 := bstep (se 1 (by rfl) ⟨1209578, by rfl⟩ : syracuseStep 1612771 = 2419157) B2419157
theorem B1612787 : Blo 1611004 1612787 := bstep (se 1 (by rfl) ⟨1209590, by rfl⟩ : syracuseStep 1612787 = 2419181) B2419181
theorem B1612803 : Blo 1611004 1612803 := bstep (se 1 (by rfl) ⟨1209602, by rfl⟩ : syracuseStep 1612803 = 2419205) B2419205
theorem B9305093 : Blo 1611004 9305093 := bstep (se 4 (by rfl) ⟨872352, by rfl⟩ : syracuseStep 9305093 = 1744705) B1744705
theorem B1612819 : Blo 1611004 1612819 := bstep (se 1 (by rfl) ⟨1209614, by rfl⟩ : syracuseStep 1612819 = 2419229) B2419229
theorem B1612835 : Blo 1611004 1612835 := bstep (se 1 (by rfl) ⟨1209626, by rfl⟩ : syracuseStep 1612835 = 2419253) B2419253
theorem B4357165 : Blo 1611004 4357165 := bstep (se 3 (by rfl) ⟨816968, by rfl⟩ : syracuseStep 4357165 = 1633937) B1633937
theorem B1612851 : Blo 1611004 1612851 := bstep (se 1 (by rfl) ⟨1209638, by rfl⟩ : syracuseStep 1612851 = 2419277) B2419277
theorem B2718785 : Blo 1611004 2718785 := bstep (se 2 (by rfl) ⟨1019544, by rfl⟩ : syracuseStep 2718785 = 2039089) B2039089
theorem B1612867 : Blo 1611004 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B1612883 : Blo 1611004 1612883 := bstep (se 1 (by rfl) ⟨1209662, by rfl⟩ : syracuseStep 1612883 = 2419325) B2419325
theorem B1612899 : Blo 1611004 1612899 := bstep (se 1 (by rfl) ⟨1209674, by rfl⟩ : syracuseStep 1612899 = 2419349) B2419349
theorem B1612915 : Blo 1611004 1612915 := bstep (se 1 (by rfl) ⟨1209686, by rfl⟩ : syracuseStep 1612915 = 2419373) B2419373
theorem B1612931 : Blo 1611004 1612931 := bstep (se 1 (by rfl) ⟨1209698, by rfl⟩ : syracuseStep 1612931 = 2419397) B2419397
theorem B12237965 : Blo 1611004 12237965 := bstep (se 3 (by rfl) ⟨2294618, by rfl⟩ : syracuseStep 12237965 = 4589237) B4589237
theorem B5438609 : Blo 1611004 5438609 := bstep (se 2 (by rfl) ⟨2039478, by rfl⟩ : syracuseStep 5438609 = 4078957) B4078957
theorem B1612947 : Blo 1611004 1612947 := bstep (se 1 (by rfl) ⟨1209710, by rfl⟩ : syracuseStep 1612947 = 2419421) B2419421
theorem B1612963 : Blo 1611004 1612963 := bstep (se 1 (by rfl) ⟨1209722, by rfl⟩ : syracuseStep 1612963 = 2419445) B2419445
theorem B5307569 : Blo 1611004 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B1612979 : Blo 1611004 1612979 := bstep (se 1 (by rfl) ⟨1209734, by rfl⟩ : syracuseStep 1612979 = 2419469) B2419469
theorem B2718913 : Blo 1611004 2718913 := bstep (se 2 (by rfl) ⟨1019592, by rfl⟩ : syracuseStep 2718913 = 2039185) B2039185
theorem B1612995 : Blo 1611004 1612995 := bstep (se 1 (by rfl) ⟨1209746, by rfl⟩ : syracuseStep 1612995 = 2419493) B2419493
theorem B39214277 : Blo 1611004 39214277 := bstep (se 4 (by rfl) ⟨3676338, by rfl⟩ : syracuseStep 39214277 = 7352677) B7352677
theorem B3628241 : Blo 1611004 3628241 := bstep (se 2 (by rfl) ⟨1360590, by rfl⟩ : syracuseStep 3628241 = 2721181) B2721181
theorem B2718947 : Blo 1611004 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B3628259 : Blo 1611004 3628259 := bstep (se 1 (by rfl) ⟨2721194, by rfl⟩ : syracuseStep 3628259 = 5442389) B5442389
theorem B13065457 : Blo 1611004 13065457 := bstep (se 2 (by rfl) ⟨4899546, by rfl⟩ : syracuseStep 13065457 = 9799093) B9799093
theorem B2719075 : Blo 1611004 2719075 := bstep (se 1 (by rfl) ⟨2039306, by rfl⟩ : syracuseStep 2719075 = 4078613) B4078613
theorem B11034053 : Blo 1611004 11034053 := bstep (se 4 (by rfl) ⟨1034442, by rfl⟩ : syracuseStep 11034053 = 2068885) B2068885
theorem B6118861 : Blo 1611004 6118861 := bstep (se 3 (by rfl) ⟨1147286, by rfl⟩ : syracuseStep 6118861 = 2294573) B2294573
theorem B2039251 : Blo 1611004 2039251 := bstep (se 1 (by rfl) ⟨1529438, by rfl⟩ : syracuseStep 2039251 = 3058877) B3058877
theorem B2719217 : Blo 1611004 2719217 := bstep (se 2 (by rfl) ⟨1019706, by rfl⟩ : syracuseStep 2719217 = 2039413) B2039413
theorem B3628529 : Blo 1611004 3628529 := bstep (se 2 (by rfl) ⟨1360698, by rfl⟩ : syracuseStep 3628529 = 2721397) B2721397
theorem B3628547 : Blo 1611004 3628547 := bstep (se 1 (by rfl) ⟨2721410, by rfl⟩ : syracuseStep 3628547 = 5442821) B5442821
theorem B6200867 : Blo 1611004 6200867 := bstep (se 1 (by rfl) ⟨4650650, by rfl⟩ : syracuseStep 6200867 = 9301301) B9301301
theorem B2039347 : Blo 1611004 2039347 := bstep (se 1 (by rfl) ⟨1529510, by rfl⟩ : syracuseStep 2039347 = 3059021) B3059021
theorem B2719345 : Blo 1611004 2719345 := bstep (se 2 (by rfl) ⟨1019754, by rfl⟩ : syracuseStep 2719345 = 2039509) B2039509
theorem B2719379 : Blo 1611004 2719379 := bstep (se 1 (by rfl) ⟨2039534, by rfl⟩ : syracuseStep 2719379 = 4079069) B4079069
theorem B5439149 : Blo 1611004 5439149 := bstep (se 3 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 5439149 = 2039681) B2039681
theorem B4079281 : Blo 1611004 4079281 := bstep (se 2 (by rfl) ⟨1529730, by rfl⟩ : syracuseStep 4079281 = 3059461) B3059461
theorem B5439203 : Blo 1611004 5439203 := bstep (se 1 (by rfl) ⟨4079402, by rfl⟩ : syracuseStep 5439203 = 8158805) B8158805
theorem B6889187 : Blo 1611004 6889187 := bstep (se 1 (by rfl) ⟨5166890, by rfl⟩ : syracuseStep 6889187 = 10333781) B10333781
theorem B3628817 : Blo 1611004 3628817 := bstep (se 2 (by rfl) ⟨1360806, by rfl⟩ : syracuseStep 3628817 = 2721613) B2721613
theorem B2719507 : Blo 1611004 2719507 := bstep (se 1 (by rfl) ⟨2039630, by rfl⟩ : syracuseStep 2719507 = 4079261) B4079261
theorem B3628835 : Blo 1611004 3628835 := bstep (se 1 (by rfl) ⟨2721626, by rfl⟩ : syracuseStep 3628835 = 5443253) B5443253
theorem B2178913 : Blo 1611004 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B2416529 : Blo 1611004 2416529 := bstep (se 2 (by rfl) ⟨906198, by rfl⟩ : syracuseStep 2416529 = 1812397) B1812397
theorem B2719649 : Blo 1611004 2719649 := bstep (se 2 (by rfl) ⟨1019868, by rfl⟩ : syracuseStep 2719649 = 2039737) B2039737
theorem B2416547 : Blo 1611004 2416547 := bstep (se 1 (by rfl) ⟨1812410, by rfl⟩ : syracuseStep 2416547 = 3624821) B3624821
theorem B4358051 : Blo 1611004 4358051 := bstep (se 1 (by rfl) ⟨3268538, by rfl⟩ : syracuseStep 4358051 = 6537077) B6537077
theorem B2416577 : Blo 1611004 2416577 := bstep (se 2 (by rfl) ⟨906216, by rfl⟩ : syracuseStep 2416577 = 1812433) B1812433
theorem B4079555 : Blo 1611004 4079555 := bstep (se 1 (by rfl) ⟨3059666, by rfl⟩ : syracuseStep 4079555 = 6119333) B6119333
theorem B4358093 : Blo 1611004 4358093 := bstep (se 3 (by rfl) ⟨817142, by rfl⟩ : syracuseStep 4358093 = 1634285) B1634285
theorem B2416595 : Blo 1611004 2416595 := bstep (se 1 (by rfl) ⟨1812446, by rfl⟩ : syracuseStep 2416595 = 3624893) B3624893
theorem B2416625 : Blo 1611004 2416625 := bstep (se 2 (by rfl) ⟨906234, by rfl⟩ : syracuseStep 2416625 = 1812469) B1812469
theorem B5439473 : Blo 1611004 5439473 := bstep (se 2 (by rfl) ⟨2039802, by rfl⟩ : syracuseStep 5439473 = 4079605) B4079605
theorem B10215409 : Blo 1611004 10215409 := bstep (se 2 (by rfl) ⟨3830778, by rfl⟩ : syracuseStep 10215409 = 7661557) B7661557
theorem B6889495 : Blo 1611004 6889495 := bstep (se 1 (by rfl) ⟨5167121, by rfl⟩ : syracuseStep 6889495 = 10334243) B10334243
theorem B2416715 : Blo 1611004 2416715 := bstep (se 1 (by rfl) ⟨1812536, by rfl⟩ : syracuseStep 2416715 = 3625073) B3625073
theorem B2416727 : Blo 1611004 2416727 := bstep (se 1 (by rfl) ⟨1812545, by rfl⟩ : syracuseStep 2416727 = 3625091) B3625091
theorem B2719831 : Blo 1611004 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B5439581 : Blo 1611004 5439581 := bstep (se 3 (by rfl) ⟨1019921, by rfl⟩ : syracuseStep 5439581 = 2039843) B2039843
theorem B3629195 : Blo 1611004 3629195 := bstep (se 1 (by rfl) ⟨2721896, by rfl⟩ : syracuseStep 3629195 = 5443793) B5443793
theorem B17662103 : Blo 1611004 17662103 := bstep (se 1 (by rfl) ⟨13246577, by rfl⟩ : syracuseStep 17662103 = 26493155) B26493155
theorem B4079767 : Blo 1611004 4079767 := bstep (se 1 (by rfl) ⟨3059825, by rfl⟩ : syracuseStep 4079767 = 6119651) B6119651
theorem B2416793 : Blo 1611004 2416793 := bstep (se 2 (by rfl) ⟨906297, by rfl⟩ : syracuseStep 2416793 = 1812595) B1812595
theorem B3629249 : Blo 1611004 3629249 := bstep (se 2 (by rfl) ⟨1360968, by rfl⟩ : syracuseStep 3629249 = 2721937) B2721937
theorem B2416907 : Blo 1611004 2416907 := bstep (se 1 (by rfl) ⟨1812680, by rfl⟩ : syracuseStep 2416907 = 3625361) B3625361
theorem B2416919 : Blo 1611004 2416919 := bstep (se 1 (by rfl) ⟨1812689, by rfl⟩ : syracuseStep 2416919 = 3625379) B3625379
theorem B3440971 : Blo 1611004 3440971 := bstep (se 1 (by rfl) ⟨2580728, by rfl⟩ : syracuseStep 3440971 = 5161457) B5161457
theorem B2416985 : Blo 1611004 2416985 := bstep (se 2 (by rfl) ⟨906369, by rfl⟩ : syracuseStep 2416985 = 1812739) B1812739
theorem B3268993 : Blo 1611004 3268993 := bstep (se 2 (by rfl) ⟨1225872, by rfl⟩ : syracuseStep 3268993 = 2451745) B2451745
theorem B3269057 : Blo 1611004 3269057 := bstep (se 2 (by rfl) ⟨1225896, by rfl⟩ : syracuseStep 3269057 = 2451793) B2451793
theorem B2417099 : Blo 1611004 2417099 := bstep (se 1 (by rfl) ⟨1812824, by rfl⟩ : syracuseStep 2417099 = 3625649) B3625649
theorem B2417111 : Blo 1611004 2417111 := bstep (se 1 (by rfl) ⟨1812833, by rfl⟩ : syracuseStep 2417111 = 3625667) B3625667
theorem B13763033 : Blo 1611004 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B2417177 : Blo 1611004 2417177 := bstep (se 2 (by rfl) ⟨906441, by rfl⟩ : syracuseStep 2417177 = 1812883) B1812883
theorem B4080203 : Blo 1611004 4080203 := bstep (se 1 (by rfl) ⟨3060152, by rfl⟩ : syracuseStep 4080203 = 6120305) B6120305
theorem B2417291 : Blo 1611004 2417291 := bstep (se 1 (by rfl) ⟨1812968, by rfl⟩ : syracuseStep 2417291 = 3625937) B3625937
theorem B2417303 : Blo 1611004 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B3441305 : Blo 1611004 3441305 := bstep (se 2 (by rfl) ⟨1290489, by rfl⟩ : syracuseStep 3441305 = 2580979) B2580979
theorem B5808833 : Blo 1611004 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B4588235 : Blo 1611004 4588235 := bstep (se 1 (by rfl) ⟨3441176, by rfl⟩ : syracuseStep 4588235 = 6882353) B6882353
theorem B2720459 : Blo 1611004 2720459 := bstep (se 1 (by rfl) ⟨2040344, by rfl⟩ : syracuseStep 2720459 = 4080689) B4080689
theorem B2417369 : Blo 1611004 2417369 := bstep (se 2 (by rfl) ⟨906513, by rfl⟩ : syracuseStep 2417369 = 1813027) B1813027
theorem B4358873 : Blo 1611004 4358873 := bstep (se 2 (by rfl) ⟨1634577, by rfl⟩ : syracuseStep 4358873 = 3269155) B3269155
theorem B2417483 : Blo 1611004 2417483 := bstep (se 1 (by rfl) ⟨1813112, by rfl⟩ : syracuseStep 2417483 = 3626225) B3626225
theorem B2720587 : Blo 1611004 2720587 := bstep (se 1 (by rfl) ⟨2040440, by rfl⟩ : syracuseStep 2720587 = 4080881) B4080881
theorem B2417495 : Blo 1611004 2417495 := bstep (se 1 (by rfl) ⟨1813121, by rfl⟩ : syracuseStep 2417495 = 3626243) B3626243
theorem B2417561 : Blo 1611004 2417561 := bstep (se 2 (by rfl) ⟨906585, by rfl⟩ : syracuseStep 2417561 = 1813171) B1813171
theorem B4080577 : Blo 1611004 4080577 := bstep (se 2 (by rfl) ⟨1530216, by rfl⟩ : syracuseStep 4080577 = 3060433) B3060433
theorem B7357387 : Blo 1611004 7357387 := bstep (se 1 (by rfl) ⟨5518040, by rfl⟩ : syracuseStep 7357387 = 11036081) B11036081
theorem B2720729 : Blo 1611004 2720729 := bstep (se 2 (by rfl) ⟨1020273, by rfl⟩ : syracuseStep 2720729 = 2040547) B2040547
theorem B13771781 : Blo 1611004 13771781 := bstep (se 4 (by rfl) ⟨1291104, by rfl⟩ : syracuseStep 13771781 = 2582209) B2582209
theorem B2417675 : Blo 1611004 2417675 := bstep (se 1 (by rfl) ⟨1813256, by rfl⟩ : syracuseStep 2417675 = 3626513) B3626513
theorem B12100625 : Blo 1611004 12100625 := bstep (se 2 (by rfl) ⟨4537734, by rfl⟩ : syracuseStep 12100625 = 9075469) B9075469
theorem B2417687 : Blo 1611004 2417687 := bstep (se 1 (by rfl) ⟨1813265, by rfl⟩ : syracuseStep 2417687 = 3626531) B3626531
theorem B7750721 : Blo 1611004 7750721 := bstep (se 2 (by rfl) ⟨2906520, by rfl⟩ : syracuseStep 7750721 = 5813041) B5813041
theorem B2417753 : Blo 1611004 2417753 := bstep (se 2 (by rfl) ⟨906657, by rfl⟩ : syracuseStep 2417753 = 1813315) B1813315
theorem B2720857 : Blo 1611004 2720857 := bstep (se 2 (by rfl) ⟨1020321, by rfl⟩ : syracuseStep 2720857 = 2040643) B2040643
theorem B6120593 : Blo 1611004 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B7349399 : Blo 1611004 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B2417867 : Blo 1611004 2417867 := bstep (se 1 (by rfl) ⟨1813400, by rfl⟩ : syracuseStep 2417867 = 3626801) B3626801
theorem B5440715 : Blo 1611004 5440715 := bstep (se 1 (by rfl) ⟨4080536, by rfl⟩ : syracuseStep 5440715 = 8161073) B8161073
theorem B2417879 : Blo 1611004 2417879 := bstep (se 1 (by rfl) ⟨1813409, by rfl⟩ : syracuseStep 2417879 = 3626819) B3626819
theorem B5162201 : Blo 1611004 5162201 := bstep (se 2 (by rfl) ⟨1935825, by rfl⟩ : syracuseStep 5162201 = 3871651) B3871651
theorem B1721579 : Blo 1611004 1721579 := bstep (se 1 (by rfl) ⟨1291184, by rfl⟩ : syracuseStep 1721579 = 2582369) B2582369
theorem B2417945 : Blo 1611004 2417945 := bstep (se 2 (by rfl) ⟨906729, by rfl⟩ : syracuseStep 2417945 = 1813459) B1813459
theorem B8160587 : Blo 1611004 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B2418059 : Blo 1611004 2418059 := bstep (se 1 (by rfl) ⟨1813544, by rfl⟩ : syracuseStep 2418059 = 3627089) B3627089
theorem B5809553 : Blo 1611004 5809553 := bstep (se 2 (by rfl) ⟨2178582, by rfl⟩ : syracuseStep 5809553 = 4357165) B4357165
theorem B2418071 : Blo 1611004 2418071 := bstep (se 1 (by rfl) ⟨1813553, by rfl⟩ : syracuseStep 2418071 = 3627107) B3627107
theorem B2041291 : Blo 1611004 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B2418137 : Blo 1611004 2418137 := bstep (se 2 (by rfl) ⟨906801, by rfl⟩ : syracuseStep 2418137 = 1813603) B1813603
theorem B5440985 : Blo 1611004 5440985 := bstep (se 2 (by rfl) ⟨2040369, by rfl⟩ : syracuseStep 5440985 = 4080739) B4080739
theorem B4081175 : Blo 1611004 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B2418251 : Blo 1611004 2418251 := bstep (se 1 (by rfl) ⟨1813688, by rfl⟩ : syracuseStep 2418251 = 3627377) B3627377
theorem B2418263 : Blo 1611004 2418263 := bstep (se 1 (by rfl) ⟨1813697, by rfl⟩ : syracuseStep 2418263 = 3627395) B3627395
theorem B2721431 : Blo 1611004 2721431 := bstep (se 1 (by rfl) ⟨2041073, by rfl⟩ : syracuseStep 2721431 = 4082147) B4082147
theorem B2418329 : Blo 1611004 2418329 := bstep (se 2 (by rfl) ⟨906873, by rfl⟩ : syracuseStep 2418329 = 1813747) B1813747
theorem B4359901 : Blo 1611004 4359901 := bstep (se 3 (by rfl) ⟨817481, by rfl⟩ : syracuseStep 4359901 = 1634963) B1634963
theorem B2418443 : Blo 1611004 2418443 := bstep (se 1 (by rfl) ⟨1813832, by rfl⟩ : syracuseStep 2418443 = 3627665) B3627665
theorem B2418455 : Blo 1611004 2418455 := bstep (se 1 (by rfl) ⟨1813841, by rfl⟩ : syracuseStep 2418455 = 3627683) B3627683
theorem B2721559 : Blo 1611004 2721559 := bstep (se 1 (by rfl) ⟨2041169, by rfl⟩ : syracuseStep 2721559 = 4082339) B4082339
theorem B6285131 : Blo 1611004 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B6121291 : Blo 1611004 6121291 := bstep (se 1 (by rfl) ⟨4590968, by rfl⟩ : syracuseStep 6121291 = 9181937) B9181937
theorem B2418521 : Blo 1611004 2418521 := bstep (se 2 (by rfl) ⟨906945, by rfl⟩ : syracuseStep 2418521 = 1813891) B1813891
theorem B16770995 : Blo 1611004 16770995 := bstep (se 1 (by rfl) ⟨12578246, by rfl⟩ : syracuseStep 16770995 = 25156493) B25156493
theorem B2418635 : Blo 1611004 2418635 := bstep (se 1 (by rfl) ⟨1813976, by rfl⟩ : syracuseStep 2418635 = 3627953) B3627953
theorem B2418647 : Blo 1611004 2418647 := bstep (se 1 (by rfl) ⟨1813985, by rfl⟩ : syracuseStep 2418647 = 3627971) B3627971
theorem B6203395 : Blo 1611004 6203395 := bstep (se 1 (by rfl) ⟨4652546, by rfl⟩ : syracuseStep 6203395 = 9305093) B9305093
theorem B2418713 : Blo 1611004 2418713 := bstep (se 2 (by rfl) ⟨907017, by rfl⟩ : syracuseStep 2418713 = 1814035) B1814035
theorem B1812523 : Blo 1611004 1812523 := bstep (se 1 (by rfl) ⟨1359392, by rfl⟩ : syracuseStep 1812523 = 2718785) B2718785
theorem B6883379 : Blo 1611004 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B10324043 : Blo 1611004 10324043 := bstep (se 1 (by rfl) ⟨7743032, by rfl⟩ : syracuseStep 10324043 = 15486065) B15486065
theorem B5163097 : Blo 1611004 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B6121565 : Blo 1611004 6121565 := bstep (se 3 (by rfl) ⟨1147793, by rfl⟩ : syracuseStep 6121565 = 2295587) B2295587
theorem B3442817 : Blo 1611004 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B26142851 : Blo 1611004 26142851 := bstep (se 1 (by rfl) ⟨19607138, by rfl⟩ : syracuseStep 26142851 = 39214277) B39214277
theorem B2418827 : Blo 1611004 2418827 := bstep (se 1 (by rfl) ⟨1814120, by rfl⟩ : syracuseStep 2418827 = 3628241) B3628241
theorem B1812631 : Blo 1611004 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B5441687 : Blo 1611004 5441687 := bstep (se 1 (by rfl) ⟨4081265, by rfl⟩ : syracuseStep 5441687 = 8162531) B8162531
theorem B2418839 : Blo 1611004 2418839 := bstep (se 1 (by rfl) ⟨1814129, by rfl⟩ : syracuseStep 2418839 = 3628259) B3628259
theorem B3311819 : Blo 1611004 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B2418905 : Blo 1611004 2418905 := bstep (se 2 (by rfl) ⟨907089, by rfl⟩ : syracuseStep 2418905 = 1814179) B1814179
theorem B17434885 : Blo 1611004 17434885 := bstep (se 4 (by rfl) ⟨1634520, by rfl⟩ : syracuseStep 17434885 = 3269041) B3269041
theorem B4589875 : Blo 1611004 4589875 := bstep (se 1 (by rfl) ⟨3442406, by rfl⟩ : syracuseStep 4589875 = 6884813) B6884813
theorem B4081985 : Blo 1611004 4081985 := bstep (se 2 (by rfl) ⟨1530744, by rfl⟩ : syracuseStep 4081985 = 3061489) B3061489
theorem B1812811 : Blo 1611004 1812811 := bstep (se 1 (by rfl) ⟨1359608, by rfl⟩ : syracuseStep 1812811 = 2719217) B2719217
theorem B2419019 : Blo 1611004 2419019 := bstep (se 1 (by rfl) ⟨1814264, by rfl⟩ : syracuseStep 2419019 = 3628529) B3628529
theorem B2419031 : Blo 1611004 2419031 := bstep (se 1 (by rfl) ⟨1814273, by rfl⟩ : syracuseStep 2419031 = 3628547) B3628547
theorem B88279409 : Blo 1611004 88279409 := bstep (se 2 (by rfl) ⟨33104778, by rfl⟩ : syracuseStep 88279409 = 66209557) B66209557
theorem B2419097 : Blo 1611004 2419097 := bstep (se 2 (by rfl) ⟨907161, by rfl⟩ : syracuseStep 2419097 = 1814323) B1814323
theorem B1812919 : Blo 1611004 1812919 := bstep (se 1 (by rfl) ⟨1359689, by rfl⟩ : syracuseStep 1812919 = 2719379) B2719379
theorem B2419211 : Blo 1611004 2419211 := bstep (se 1 (by rfl) ⟨1814408, by rfl⟩ : syracuseStep 2419211 = 3628817) B3628817
theorem B4590103 : Blo 1611004 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B2419223 : Blo 1611004 2419223 := bstep (se 1 (by rfl) ⟨1814417, by rfl⟩ : syracuseStep 2419223 = 3628835) B3628835
theorem B2296345 : Blo 1611004 2296345 := bstep (se 2 (by rfl) ⟨861129, by rfl⟩ : syracuseStep 2296345 = 1722259) B1722259
theorem B2419289 : Blo 1611004 2419289 := bstep (se 2 (by rfl) ⟨907233, by rfl⟩ : syracuseStep 2419289 = 1814467) B1814467
theorem B1813099 : Blo 1611004 1813099 := bstep (se 1 (by rfl) ⟨1359824, by rfl⟩ : syracuseStep 1813099 = 2719649) B2719649
theorem B5442227 : Blo 1611004 5442227 := bstep (se 1 (by rfl) ⟨4081670, by rfl⟩ : syracuseStep 5442227 = 8163341) B8163341
theorem B5163713 : Blo 1611004 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B2419403 : Blo 1611004 2419403 := bstep (se 1 (by rfl) ⟨1814552, by rfl⟩ : syracuseStep 2419403 = 3629105) B3629105
theorem B1813207 : Blo 1611004 1813207 := bstep (se 1 (by rfl) ⟨1359905, by rfl⟩ : syracuseStep 1813207 = 2719811) B2719811
theorem B2419415 : Blo 1611004 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B6122263 : Blo 1611004 6122263 := bstep (se 1 (by rfl) ⟨4591697, by rfl⟩ : syracuseStep 6122263 = 9183395) B9183395
theorem B2419481 : Blo 1611004 2419481 := bstep (se 2 (by rfl) ⟨907305, by rfl⟩ : syracuseStep 2419481 = 1814611) B1814611
theorem B5163841 : Blo 1611004 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B4082521 : Blo 1611004 4082521 := bstep (se 2 (by rfl) ⟨1530945, by rfl⟩ : syracuseStep 4082521 = 3061891) B3061891
theorem B1813387 : Blo 1611004 1813387 := bstep (se 1 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 1813387 = 2720081) B2720081
theorem B5442497 : Blo 1611004 5442497 := bstep (se 2 (by rfl) ⟨2040936, by rfl⟩ : syracuseStep 5442497 = 4081873) B4081873
theorem B3443671 : Blo 1611004 3443671 := bstep (se 1 (by rfl) ⟨2582753, by rfl⟩ : syracuseStep 3443671 = 5165507) B5165507
theorem B1813495 : Blo 1611004 1813495 := bstep (se 1 (by rfl) ⟨1360121, by rfl⟩ : syracuseStep 1813495 = 2720243) B2720243
theorem B8162369 : Blo 1611004 8162369 := bstep (se 2 (by rfl) ⟨3060888, by rfl⟩ : syracuseStep 8162369 = 6121777) B6121777
theorem B18353303 : Blo 1611004 18353303 := bstep (se 1 (by rfl) ⟨13764977, by rfl⟩ : syracuseStep 18353303 = 27529955) B27529955
theorem B1813675 : Blo 1611004 1813675 := bstep (se 1 (by rfl) ⟨1360256, by rfl⟩ : syracuseStep 1813675 = 2720513) B2720513
theorem B4902067 : Blo 1611004 4902067 := bstep (se 1 (by rfl) ⟨3676550, by rfl⟩ : syracuseStep 4902067 = 7353101) B7353101
theorem B1633483 : Blo 1611004 1633483 := bstep (se 1 (by rfl) ⟨1225112, by rfl⟩ : syracuseStep 1633483 = 2450225) B2450225
theorem B1813783 : Blo 1611004 1813783 := bstep (se 1 (by rfl) ⟨1360337, by rfl⟩ : syracuseStep 1813783 = 2720675) B2720675
theorem B12234077 : Blo 1611004 12234077 := bstep (se 3 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 12234077 = 4587779) B4587779
theorem B3059059 : Blo 1611004 3059059 := bstep (se 1 (by rfl) ⟨2294294, by rfl⟩ : syracuseStep 3059059 = 4588589) B4588589
theorem B1813963 : Blo 1611004 1813963 := bstep (se 1 (by rfl) ⟨1360472, by rfl⟩ : syracuseStep 1813963 = 2720945) B2720945
theorem B5443037 : Blo 1611004 5443037 := bstep (se 3 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 5443037 = 2041139) B2041139
theorem B56618513 : Blo 1611004 56618513 := bstep (se 2 (by rfl) ⟨21231942, by rfl⟩ : syracuseStep 56618513 = 42463885) B42463885
theorem B6123053 : Blo 1611004 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B1814071 : Blo 1611004 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B1814251 : Blo 1611004 1814251 := bstep (se 1 (by rfl) ⟨1360688, by rfl⟩ : syracuseStep 1814251 = 2721377) B2721377
theorem B3444491 : Blo 1611004 3444491 := bstep (se 1 (by rfl) ⟨2583368, by rfl⟩ : syracuseStep 3444491 = 5166737) B5166737
theorem B3059507 : Blo 1611004 3059507 := bstep (se 1 (by rfl) ⟨2294630, by rfl⟩ : syracuseStep 3059507 = 4589261) B4589261
theorem B1814359 : Blo 1611004 1814359 := bstep (se 1 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 1814359 = 2721539) B2721539
theorem B2903897 : Blo 1611004 2903897 := bstep (se 2 (by rfl) ⟨1088961, by rfl⟩ : syracuseStep 2903897 = 2177923) B2177923
theorem B3059545 : Blo 1611004 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B3624857 : Blo 1611004 3624857 := bstep (se 2 (by rfl) ⟨1359321, by rfl⟩ : syracuseStep 3624857 = 2718643) B2718643
theorem B6983597 : Blo 1611004 6983597 := bstep (se 3 (by rfl) ⟨1309424, by rfl⟩ : syracuseStep 6983597 = 2618849) B2618849
theorem B58806233 : Blo 1611004 58806233 := bstep (se 2 (by rfl) ⟨22052337, by rfl⟩ : syracuseStep 58806233 = 44104675) B44104675
theorem B3624947 : Blo 1611004 3624947 := bstep (se 1 (by rfl) ⟨2718710, by rfl⟩ : syracuseStep 3624947 = 5437421) B5437421
theorem B1814539 : Blo 1611004 1814539 := bstep (se 1 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 1814539 = 2721809) B2721809
theorem B3624983 : Blo 1611004 3624983 := bstep (se 1 (by rfl) ⟨2718737, by rfl⟩ : syracuseStep 3624983 = 5437475) B5437475
theorem B3870785 : Blo 1611004 3870785 := bstep (se 2 (by rfl) ⟨1451544, by rfl⟩ : syracuseStep 3870785 = 2903089) B2903089
theorem B3625163 : Blo 1611004 3625163 := bstep (se 1 (by rfl) ⟨2718872, by rfl⟩ : syracuseStep 3625163 = 5437745) B5437745
theorem B1937623 : Blo 1611004 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B3625217 : Blo 1611004 3625217 := bstep (se 2 (by rfl) ⟨1359456, by rfl⟩ : syracuseStep 3625217 = 2718913) B2718913
theorem B3059993 : Blo 1611004 3059993 := bstep (se 2 (by rfl) ⟨1147497, by rfl⟩ : syracuseStep 3059993 = 2294995) B2294995
theorem B17420609 : Blo 1611004 17420609 := bstep (se 2 (by rfl) ⟨6532728, by rfl⟩ : syracuseStep 17420609 = 13065457) B13065457
theorem B4591961 : Blo 1611004 4591961 := bstep (se 2 (by rfl) ⟨1721985, by rfl⟩ : syracuseStep 4591961 = 3443971) B3443971
theorem B6533507 : Blo 1611004 6533507 := bstep (se 1 (by rfl) ⟨4900130, by rfl⟩ : syracuseStep 6533507 = 9800261) B9800261
theorem B3625433 : Blo 1611004 3625433 := bstep (se 2 (by rfl) ⟨1359537, by rfl⟩ : syracuseStep 3625433 = 2719075) B2719075
theorem B5812739 : Blo 1611004 5812739 := bstep (se 1 (by rfl) ⟨4359554, by rfl⟩ : syracuseStep 5812739 = 8719109) B8719109
theorem B3625523 : Blo 1611004 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B3625559 : Blo 1611004 3625559 := bstep (se 1 (by rfl) ⟨2719169, by rfl⟩ : syracuseStep 3625559 = 5438339) B5438339
theorem B1634999 : Blo 1611004 1634999 := bstep (se 1 (by rfl) ⟨1226249, by rfl⟩ : syracuseStep 1634999 = 2452499) B2452499
theorem B3625739 : Blo 1611004 3625739 := bstep (se 1 (by rfl) ⟨2719304, by rfl⟩ : syracuseStep 3625739 = 5438609) B5438609
theorem B46486325 : Blo 1611004 46486325 := bstep (se 5 (by rfl) ⟨2179046, by rfl⟩ : syracuseStep 46486325 = 4358093) B4358093
theorem B3625793 : Blo 1611004 3625793 := bstep (se 2 (by rfl) ⟨1359672, by rfl⟩ : syracuseStep 3625793 = 2719345) B2719345
theorem B20665205 : Blo 1611004 20665205 := bstep (se 5 (by rfl) ⟨968681, by rfl⟩ : syracuseStep 20665205 = 1937363) B1937363
theorem B11613107 : Blo 1611004 11613107 := bstep (se 1 (by rfl) ⟨8709830, by rfl⟩ : syracuseStep 11613107 = 17419661) B17419661
theorem B8164313 : Blo 1611004 8164313 := bstep (se 2 (by rfl) ⟨3061617, by rfl⟩ : syracuseStep 8164313 = 6123235) B6123235
theorem B5813213 : Blo 1611004 5813213 := bstep (se 3 (by rfl) ⟨1089977, by rfl⟩ : syracuseStep 5813213 = 2179955) B2179955
theorem B3060737 : Blo 1611004 3060737 := bstep (se 2 (by rfl) ⟨1147776, by rfl⟩ : syracuseStep 3060737 = 2295553) B2295553
theorem B4133911 : Blo 1611004 4133911 := bstep (se 1 (by rfl) ⟨3100433, by rfl⟩ : syracuseStep 4133911 = 6200867) B6200867
theorem B3626009 : Blo 1611004 3626009 := bstep (se 2 (by rfl) ⟨1359753, by rfl⟩ : syracuseStep 3626009 = 2719507) B2719507
theorem B5166173 : Blo 1611004 5166173 := bstep (se 3 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 5166173 = 1937315) B1937315
theorem B3626099 : Blo 1611004 3626099 := bstep (se 1 (by rfl) ⟨2719574, by rfl⟩ : syracuseStep 3626099 = 5439149) B5439149
theorem B2905217 : Blo 1611004 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B3626135 : Blo 1611004 3626135 := bstep (se 1 (by rfl) ⟨2719601, by rfl⟩ : syracuseStep 3626135 = 5439203) B5439203
theorem B4592791 : Blo 1611004 4592791 := bstep (se 1 (by rfl) ⟨3444593, by rfl⟩ : syracuseStep 4592791 = 6889187) B6889187
theorem B1611019 : Blo 1611004 1611019 := bstep (se 1 (by rfl) ⟨1208264, by rfl⟩ : syracuseStep 1611019 = 2416529) B2416529
theorem B3061003 : Blo 1611004 3061003 := bstep (se 1 (by rfl) ⟨2295752, by rfl⟩ : syracuseStep 3061003 = 4591505) B4591505
theorem B1611031 : Blo 1611004 1611031 := bstep (se 1 (by rfl) ⟨1208273, by rfl⟩ : syracuseStep 1611031 = 2416547) B2416547
theorem B2905367 : Blo 1611004 2905367 := bstep (se 1 (by rfl) ⟨2179025, by rfl⟩ : syracuseStep 2905367 = 4358051) B4358051
theorem B1611051 : Blo 1611004 1611051 := bstep (se 1 (by rfl) ⟨1208288, by rfl⟩ : syracuseStep 1611051 = 2416577) B2416577
theorem B1611063 : Blo 1611004 1611063 := bstep (se 1 (by rfl) ⟨1208297, by rfl⟩ : syracuseStep 1611063 = 2416595) B2416595
theorem B13620545 : Blo 1611004 13620545 := bstep (se 2 (by rfl) ⟨5107704, by rfl⟩ : syracuseStep 13620545 = 10215409) B10215409
theorem B1611083 : Blo 1611004 1611083 := bstep (se 1 (by rfl) ⟨1208312, by rfl⟩ : syracuseStep 1611083 = 2416625) B2416625
theorem B3626315 : Blo 1611004 3626315 := bstep (se 1 (by rfl) ⟨2719736, by rfl⟩ : syracuseStep 3626315 = 5439473) B5439473
theorem B1611095 : Blo 1611004 1611095 := bstep (se 1 (by rfl) ⟨1208321, by rfl⟩ : syracuseStep 1611095 = 2416643) B2416643
theorem B1611115 : Blo 1611004 1611115 := bstep (se 1 (by rfl) ⟨1208336, by rfl⟩ : syracuseStep 1611115 = 2416673) B2416673
theorem B1611127 : Blo 1611004 1611127 := bstep (se 1 (by rfl) ⟨1208345, by rfl⟩ : syracuseStep 1611127 = 2416691) B2416691
theorem B3626369 : Blo 1611004 3626369 := bstep (se 2 (by rfl) ⟨1359888, by rfl⟩ : syracuseStep 3626369 = 2719777) B2719777
theorem B1611147 : Blo 1611004 1611147 := bstep (se 1 (by rfl) ⟨1208360, by rfl⟩ : syracuseStep 1611147 = 2416721) B2416721
theorem B2905483 : Blo 1611004 2905483 := bstep (se 1 (by rfl) ⟨2179112, by rfl⟩ : syracuseStep 2905483 = 4358225) B4358225
theorem B1611159 : Blo 1611004 1611159 := bstep (se 1 (by rfl) ⟨1208369, by rfl⟩ : syracuseStep 1611159 = 2416739) B2416739
theorem B1611179 : Blo 1611004 1611179 := bstep (se 1 (by rfl) ⟨1208384, by rfl⟩ : syracuseStep 1611179 = 2416769) B2416769
theorem B18609587 : Blo 1611004 18609587 := bstep (se 1 (by rfl) ⟨13957190, by rfl⟩ : syracuseStep 18609587 = 27914381) B27914381
theorem B1611191 : Blo 1611004 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B1611211 : Blo 1611004 1611211 := bstep (se 1 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 1611211 = 2416817) B2416817
theorem B1611223 : Blo 1611004 1611223 := bstep (se 1 (by rfl) ⟨1208417, by rfl⟩ : syracuseStep 1611223 = 2416835) B2416835
theorem B1611243 : Blo 1611004 1611243 := bstep (se 1 (by rfl) ⟨1208432, by rfl⟩ : syracuseStep 1611243 = 2416865) B2416865
theorem B1611255 : Blo 1611004 1611255 := bstep (se 1 (by rfl) ⟨1208441, by rfl⟩ : syracuseStep 1611255 = 2416883) B2416883
theorem B1611275 : Blo 1611004 1611275 := bstep (se 1 (by rfl) ⟨1208456, by rfl⟩ : syracuseStep 1611275 = 2416913) B2416913
theorem B1611287 : Blo 1611004 1611287 := bstep (se 1 (by rfl) ⟨1208465, by rfl⟩ : syracuseStep 1611287 = 2416931) B2416931
theorem B1611307 : Blo 1611004 1611307 := bstep (se 1 (by rfl) ⟨1208480, by rfl⟩ : syracuseStep 1611307 = 2416961) B2416961
theorem B1611319 : Blo 1611004 1611319 := bstep (se 1 (by rfl) ⟨1208489, by rfl⟩ : syracuseStep 1611319 = 2416979) B2416979
theorem B1611339 : Blo 1611004 1611339 := bstep (se 1 (by rfl) ⟨1208504, by rfl⟩ : syracuseStep 1611339 = 2417009) B2417009
theorem B1611351 : Blo 1611004 1611351 := bstep (se 1 (by rfl) ⟨1208513, by rfl⟩ : syracuseStep 1611351 = 2417027) B2417027
theorem B3626585 : Blo 1611004 3626585 := bstep (se 2 (by rfl) ⟨1359969, by rfl⟩ : syracuseStep 3626585 = 2719939) B2719939
theorem B1611371 : Blo 1611004 1611371 := bstep (se 1 (by rfl) ⟨1208528, by rfl⟩ : syracuseStep 1611371 = 2417057) B2417057
theorem B1611383 : Blo 1611004 1611383 := bstep (se 1 (by rfl) ⟨1208537, by rfl⟩ : syracuseStep 1611383 = 2417075) B2417075
theorem B1611403 : Blo 1611004 1611403 := bstep (se 1 (by rfl) ⟨1208552, by rfl⟩ : syracuseStep 1611403 = 2417105) B2417105
theorem B1611415 : Blo 1611004 1611415 := bstep (se 1 (by rfl) ⟨1208561, by rfl⟩ : syracuseStep 1611415 = 2417123) B2417123
theorem B2758295 : Blo 1611004 2758295 := bstep (se 1 (by rfl) ⟨2068721, by rfl⟩ : syracuseStep 2758295 = 4137443) B4137443
theorem B1611435 : Blo 1611004 1611435 := bstep (se 1 (by rfl) ⟨1208576, by rfl⟩ : syracuseStep 1611435 = 2417153) B2417153
theorem B3626675 : Blo 1611004 3626675 := bstep (se 1 (by rfl) ⟨2720006, by rfl⟩ : syracuseStep 3626675 = 5440013) B5440013
theorem B1611447 : Blo 1611004 1611447 := bstep (se 1 (by rfl) ⟨1208585, by rfl⟩ : syracuseStep 1611447 = 2417171) B2417171
theorem B1611467 : Blo 1611004 1611467 := bstep (se 1 (by rfl) ⟨1208600, by rfl⟩ : syracuseStep 1611467 = 2417201) B2417201
theorem B3061451 : Blo 1611004 3061451 := bstep (se 1 (by rfl) ⟨2296088, by rfl⟩ : syracuseStep 3061451 = 4592177) B4592177
theorem B1611479 : Blo 1611004 1611479 := bstep (se 1 (by rfl) ⟨1208609, by rfl⟩ : syracuseStep 1611479 = 2417219) B2417219
theorem B3626711 : Blo 1611004 3626711 := bstep (se 1 (by rfl) ⟨2720033, by rfl⟩ : syracuseStep 3626711 = 5440067) B5440067
theorem B1611499 : Blo 1611004 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B1611511 : Blo 1611004 1611511 := bstep (se 1 (by rfl) ⟨1208633, by rfl⟩ : syracuseStep 1611511 = 2417267) B2417267
theorem B1611531 : Blo 1611004 1611531 := bstep (se 1 (by rfl) ⟨1208648, by rfl⟩ : syracuseStep 1611531 = 2417297) B2417297
theorem B1611543 : Blo 1611004 1611543 := bstep (se 1 (by rfl) ⟨1208657, by rfl⟩ : syracuseStep 1611543 = 2417315) B2417315
theorem B1611563 : Blo 1611004 1611563 := bstep (se 1 (by rfl) ⟨1208672, by rfl⟩ : syracuseStep 1611563 = 2417345) B2417345
theorem B1611575 : Blo 1611004 1611575 := bstep (se 1 (by rfl) ⟨1208681, by rfl⟩ : syracuseStep 1611575 = 2417363) B2417363
theorem B5437259 : Blo 1611004 5437259 := bstep (se 1 (by rfl) ⟨4077944, by rfl⟩ : syracuseStep 5437259 = 8155889) B8155889
theorem B1611595 : Blo 1611004 1611595 := bstep (se 1 (by rfl) ⟨1208696, by rfl⟩ : syracuseStep 1611595 = 2417393) B2417393
theorem B1611607 : Blo 1611004 1611607 := bstep (se 1 (by rfl) ⟨1208705, by rfl⟩ : syracuseStep 1611607 = 2417411) B2417411
theorem B61962083 : Blo 1611004 61962083 := bstep (se 1 (by rfl) ⟨46471562, by rfl⟩ : syracuseStep 61962083 = 92943125) B92943125
theorem B1611627 : Blo 1611004 1611627 := bstep (se 1 (by rfl) ⟨1208720, by rfl⟩ : syracuseStep 1611627 = 2417441) B2417441
theorem B1611639 : Blo 1611004 1611639 := bstep (se 1 (by rfl) ⟨1208729, by rfl⟩ : syracuseStep 1611639 = 2417459) B2417459
theorem B3061633 : Blo 1611004 3061633 := bstep (se 2 (by rfl) ⟨1148112, by rfl⟩ : syracuseStep 3061633 = 2296225) B2296225
theorem B1611659 : Blo 1611004 1611659 := bstep (se 1 (by rfl) ⟨1208744, by rfl⟩ : syracuseStep 1611659 = 2417489) B2417489
theorem B3626891 : Blo 1611004 3626891 := bstep (se 1 (by rfl) ⟨2720168, by rfl⟩ : syracuseStep 3626891 = 5440337) B5440337
theorem B1611671 : Blo 1611004 1611671 := bstep (se 1 (by rfl) ⟨1208753, by rfl⟩ : syracuseStep 1611671 = 2417507) B2417507
theorem B1611691 : Blo 1611004 1611691 := bstep (se 1 (by rfl) ⟨1208768, by rfl⟩ : syracuseStep 1611691 = 2417537) B2417537
theorem B25499569 : Blo 1611004 25499569 := bstep (se 2 (by rfl) ⟨9562338, by rfl⟩ : syracuseStep 25499569 = 19124677) B19124677
theorem B1611703 : Blo 1611004 1611703 := bstep (se 1 (by rfl) ⟨1208777, by rfl⟩ : syracuseStep 1611703 = 2417555) B2417555
theorem B3626945 : Blo 1611004 3626945 := bstep (se 2 (by rfl) ⟨1360104, by rfl⟩ : syracuseStep 3626945 = 2720209) B2720209
theorem B1611723 : Blo 1611004 1611723 := bstep (se 1 (by rfl) ⟨1208792, by rfl⟩ : syracuseStep 1611723 = 2417585) B2417585
theorem B1611735 : Blo 1611004 1611735 := bstep (se 1 (by rfl) ⟨1208801, by rfl⟩ : syracuseStep 1611735 = 2417603) B2417603
theorem B1611755 : Blo 1611004 1611755 := bstep (se 1 (by rfl) ⟨1208816, by rfl⟩ : syracuseStep 1611755 = 2417633) B2417633
theorem B1611767 : Blo 1611004 1611767 := bstep (se 1 (by rfl) ⟨1208825, by rfl⟩ : syracuseStep 1611767 = 2417651) B2417651
theorem B3266561 : Blo 1611004 3266561 := bstep (se 2 (by rfl) ⟨1224960, by rfl⟩ : syracuseStep 3266561 = 2449921) B2449921
theorem B1611787 : Blo 1611004 1611787 := bstep (se 1 (by rfl) ⟨1208840, by rfl⟩ : syracuseStep 1611787 = 2417681) B2417681
theorem B1611799 : Blo 1611004 1611799 := bstep (se 1 (by rfl) ⟨1208849, by rfl⟩ : syracuseStep 1611799 = 2417699) B2417699
theorem B2758679 : Blo 1611004 2758679 := bstep (se 1 (by rfl) ⟨2069009, by rfl⟩ : syracuseStep 2758679 = 4138019) B4138019
theorem B1611819 : Blo 1611004 1611819 := bstep (se 1 (by rfl) ⟨1208864, by rfl⟩ : syracuseStep 1611819 = 2417729) B2417729
theorem B1611831 : Blo 1611004 1611831 := bstep (se 1 (by rfl) ⟨1208873, by rfl⟩ : syracuseStep 1611831 = 2417747) B2417747
theorem B1611851 : Blo 1611004 1611851 := bstep (se 1 (by rfl) ⟨1208888, by rfl⟩ : syracuseStep 1611851 = 2417777) B2417777
theorem B1611863 : Blo 1611004 1611863 := bstep (se 1 (by rfl) ⟨1208897, by rfl⟩ : syracuseStep 1611863 = 2417795) B2417795
theorem B5437529 : Blo 1611004 5437529 := bstep (se 2 (by rfl) ⟨2039073, by rfl⟩ : syracuseStep 5437529 = 4078147) B4078147
theorem B13768805 : Blo 1611004 13768805 := bstep (se 4 (by rfl) ⟨1290825, by rfl⟩ : syracuseStep 13768805 = 2581651) B2581651
theorem B1611883 : Blo 1611004 1611883 := bstep (se 1 (by rfl) ⟨1208912, by rfl⟩ : syracuseStep 1611883 = 2417825) B2417825
theorem B1611895 : Blo 1611004 1611895 := bstep (se 1 (by rfl) ⟨1208921, by rfl⟩ : syracuseStep 1611895 = 2417843) B2417843
theorem B1611915 : Blo 1611004 1611915 := bstep (se 1 (by rfl) ⟨1208936, by rfl⟩ : syracuseStep 1611915 = 2417873) B2417873
theorem B1611927 : Blo 1611004 1611927 := bstep (se 1 (by rfl) ⟨1208945, by rfl⟩ : syracuseStep 1611927 = 2417891) B2417891
theorem B3627161 : Blo 1611004 3627161 := bstep (se 2 (by rfl) ⟨1360185, by rfl⟩ : syracuseStep 3627161 = 2720371) B2720371
theorem B1611947 : Blo 1611004 1611947 := bstep (se 1 (by rfl) ⟨1208960, by rfl⟩ : syracuseStep 1611947 = 2417921) B2417921
theorem B1611959 : Blo 1611004 1611959 := bstep (se 1 (by rfl) ⟨1208969, by rfl⟩ : syracuseStep 1611959 = 2417939) B2417939
theorem B4356299 : Blo 1611004 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B1611979 : Blo 1611004 1611979 := bstep (se 1 (by rfl) ⟨1208984, by rfl⟩ : syracuseStep 1611979 = 2417969) B2417969
theorem B1611991 : Blo 1611004 1611991 := bstep (se 1 (by rfl) ⟨1208993, by rfl⟩ : syracuseStep 1611991 = 2417987) B2417987
theorem B3061975 : Blo 1611004 3061975 := bstep (se 1 (by rfl) ⟨2296481, by rfl⟩ : syracuseStep 3061975 = 4592963) B4592963
theorem B1612011 : Blo 1611004 1612011 := bstep (se 1 (by rfl) ⟨1209008, by rfl⟩ : syracuseStep 1612011 = 2418017) B2418017
theorem B3627251 : Blo 1611004 3627251 := bstep (se 1 (by rfl) ⟨2720438, by rfl⟩ : syracuseStep 3627251 = 5440877) B5440877
theorem B1612023 : Blo 1611004 1612023 := bstep (se 1 (by rfl) ⟨1209017, by rfl⟩ : syracuseStep 1612023 = 2418035) B2418035
theorem B6887683 : Blo 1611004 6887683 := bstep (se 1 (by rfl) ⟨5165762, by rfl⟩ : syracuseStep 6887683 = 10331525) B10331525
theorem B1612043 : Blo 1611004 1612043 := bstep (se 1 (by rfl) ⟨1209032, by rfl⟩ : syracuseStep 1612043 = 2418065) B2418065
theorem B1612055 : Blo 1611004 1612055 := bstep (se 1 (by rfl) ⟨1209041, by rfl⟩ : syracuseStep 1612055 = 2418083) B2418083
theorem B3627287 : Blo 1611004 3627287 := bstep (se 1 (by rfl) ⟨2720465, by rfl⟩ : syracuseStep 3627287 = 5440931) B5440931
theorem B1612075 : Blo 1611004 1612075 := bstep (se 1 (by rfl) ⟨1209056, by rfl⟩ : syracuseStep 1612075 = 2418113) B2418113
theorem B6117677 : Blo 1611004 6117677 := bstep (se 3 (by rfl) ⟨1147064, by rfl⟩ : syracuseStep 6117677 = 2294129) B2294129
theorem B1612087 : Blo 1611004 1612087 := bstep (se 1 (by rfl) ⟨1209065, by rfl⟩ : syracuseStep 1612087 = 2418131) B2418131
theorem B6117707 : Blo 1611004 6117707 := bstep (se 1 (by rfl) ⟨4588280, by rfl⟩ : syracuseStep 6117707 = 9176561) B9176561
theorem B1612107 : Blo 1611004 1612107 := bstep (se 1 (by rfl) ⟨1209080, by rfl⟩ : syracuseStep 1612107 = 2418161) B2418161
theorem B1612119 : Blo 1611004 1612119 := bstep (se 1 (by rfl) ⟨1209089, by rfl⟩ : syracuseStep 1612119 = 2418179) B2418179
theorem B1612139 : Blo 1611004 1612139 := bstep (se 1 (by rfl) ⟨1209104, by rfl⟩ : syracuseStep 1612139 = 2418209) B2418209
theorem B1612151 : Blo 1611004 1612151 := bstep (se 1 (by rfl) ⟨1209113, by rfl⟩ : syracuseStep 1612151 = 2418227) B2418227
theorem B1612171 : Blo 1611004 1612171 := bstep (se 1 (by rfl) ⟨1209128, by rfl⟩ : syracuseStep 1612171 = 2418257) B2418257
theorem B1612183 : Blo 1611004 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B1612203 : Blo 1611004 1612203 := bstep (se 1 (by rfl) ⟨1209152, by rfl⟩ : syracuseStep 1612203 = 2418305) B2418305
theorem B9181619 : Blo 1611004 9181619 := bstep (se 1 (by rfl) ⟨6886214, by rfl⟩ : syracuseStep 9181619 = 13772429) B13772429
theorem B1612215 : Blo 1611004 1612215 := bstep (se 1 (by rfl) ⟨1209161, by rfl⟩ : syracuseStep 1612215 = 2418323) B2418323
theorem B3627467 : Blo 1611004 3627467 := bstep (se 1 (by rfl) ⟨2720600, by rfl⟩ : syracuseStep 3627467 = 5441201) B5441201
theorem B1612235 : Blo 1611004 1612235 := bstep (se 1 (by rfl) ⟨1209176, by rfl⟩ : syracuseStep 1612235 = 2418353) B2418353
theorem B1612247 : Blo 1611004 1612247 := bstep (se 1 (by rfl) ⟨1209185, by rfl⟩ : syracuseStep 1612247 = 2418371) B2418371
theorem B1612267 : Blo 1611004 1612267 := bstep (se 1 (by rfl) ⟨1209200, by rfl⟩ : syracuseStep 1612267 = 2418401) B2418401
theorem B1612279 : Blo 1611004 1612279 := bstep (se 1 (by rfl) ⟨1209209, by rfl⟩ : syracuseStep 1612279 = 2418419) B2418419
theorem B3627521 : Blo 1611004 3627521 := bstep (se 2 (by rfl) ⟨1360320, by rfl⟩ : syracuseStep 3627521 = 2720641) B2720641
theorem B1612299 : Blo 1611004 1612299 := bstep (se 1 (by rfl) ⟨1209224, by rfl⟩ : syracuseStep 1612299 = 2418449) B2418449
theorem B1612311 : Blo 1611004 1612311 := bstep (se 1 (by rfl) ⟨1209233, by rfl⟩ : syracuseStep 1612311 = 2418467) B2418467
theorem B1612331 : Blo 1611004 1612331 := bstep (se 1 (by rfl) ⟨1209248, by rfl⟩ : syracuseStep 1612331 = 2418497) B2418497
theorem B1612343 : Blo 1611004 1612343 := bstep (se 1 (by rfl) ⟨1209257, by rfl⟩ : syracuseStep 1612343 = 2418515) B2418515
theorem B5306945 : Blo 1611004 5306945 := bstep (se 2 (by rfl) ⟨1990104, by rfl⟩ : syracuseStep 5306945 = 3980209) B3980209
theorem B1612363 : Blo 1611004 1612363 := bstep (se 1 (by rfl) ⟨1209272, by rfl⟩ : syracuseStep 1612363 = 2418545) B2418545
theorem B1612375 : Blo 1611004 1612375 := bstep (se 1 (by rfl) ⟨1209281, by rfl⟩ : syracuseStep 1612375 = 2418563) B2418563
theorem B1612395 : Blo 1611004 1612395 := bstep (se 1 (by rfl) ⟨1209296, by rfl⟩ : syracuseStep 1612395 = 2418593) B2418593
theorem B1612407 : Blo 1611004 1612407 := bstep (se 1 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 1612407 = 2418611) B2418611
theorem B1612427 : Blo 1611004 1612427 := bstep (se 1 (by rfl) ⟨1209320, by rfl⟩ : syracuseStep 1612427 = 2418641) B2418641
theorem B1612439 : Blo 1611004 1612439 := bstep (se 1 (by rfl) ⟨1209329, by rfl⟩ : syracuseStep 1612439 = 2418659) B2418659
theorem B1612459 : Blo 1611004 1612459 := bstep (se 1 (by rfl) ⟨1209344, by rfl⟩ : syracuseStep 1612459 = 2418689) B2418689
theorem B4078259 : Blo 1611004 4078259 := bstep (se 1 (by rfl) ⟨3058694, by rfl⟩ : syracuseStep 4078259 = 6117389) B6117389
theorem B4356787 : Blo 1611004 4356787 := bstep (se 1 (by rfl) ⟨3267590, by rfl⟩ : syracuseStep 4356787 = 6535181) B6535181
theorem B1612471 : Blo 1611004 1612471 := bstep (se 1 (by rfl) ⟨1209353, by rfl⟩ : syracuseStep 1612471 = 2418707) B2418707
theorem B1612491 : Blo 1611004 1612491 := bstep (se 1 (by rfl) ⟨1209368, by rfl⟩ : syracuseStep 1612491 = 2418737) B2418737
theorem B1612503 : Blo 1611004 1612503 := bstep (se 1 (by rfl) ⟨1209377, by rfl⟩ : syracuseStep 1612503 = 2418755) B2418755
theorem B3627737 : Blo 1611004 3627737 := bstep (se 2 (by rfl) ⟨1360401, by rfl⟩ : syracuseStep 3627737 = 2720803) B2720803
theorem B1612523 : Blo 1611004 1612523 := bstep (se 1 (by rfl) ⟨1209392, by rfl⟩ : syracuseStep 1612523 = 2418785) B2418785
theorem B1612535 : Blo 1611004 1612535 := bstep (se 1 (by rfl) ⟨1209401, by rfl⟩ : syracuseStep 1612535 = 2418803) B2418803
theorem B1612555 : Blo 1611004 1612555 := bstep (se 1 (by rfl) ⟨1209416, by rfl⟩ : syracuseStep 1612555 = 2418833) B2418833
theorem B5438231 : Blo 1611004 5438231 := bstep (se 1 (by rfl) ⟨4078673, by rfl⟩ : syracuseStep 5438231 = 8157347) B8157347
theorem B1612567 : Blo 1611004 1612567 := bstep (se 1 (by rfl) ⟨1209425, by rfl⟩ : syracuseStep 1612567 = 2418851) B2418851
theorem B1612587 : Blo 1611004 1612587 := bstep (se 1 (by rfl) ⟨1209440, by rfl⟩ : syracuseStep 1612587 = 2418881) B2418881
theorem B3627827 : Blo 1611004 3627827 := bstep (se 1 (by rfl) ⟨2720870, by rfl⟩ : syracuseStep 3627827 = 5441741) B5441741
theorem B1612599 : Blo 1611004 1612599 := bstep (se 1 (by rfl) ⟨1209449, by rfl⟩ : syracuseStep 1612599 = 2418899) B2418899
theorem B1612619 : Blo 1611004 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B2177879 : Blo 1611004 2177879 := bstep (se 1 (by rfl) ⟨1633409, by rfl⟩ : syracuseStep 2177879 = 3266819) B3266819
theorem B3627863 : Blo 1611004 3627863 := bstep (se 1 (by rfl) ⟨2720897, by rfl⟩ : syracuseStep 3627863 = 5441795) B5441795
theorem B1612631 : Blo 1611004 1612631 := bstep (se 1 (by rfl) ⟨1209473, by rfl⟩ : syracuseStep 1612631 = 2418947) B2418947
theorem B1612651 : Blo 1611004 1612651 := bstep (se 1 (by rfl) ⟨1209488, by rfl⟩ : syracuseStep 1612651 = 2418977) B2418977
theorem B1612663 : Blo 1611004 1612663 := bstep (se 1 (by rfl) ⟨1209497, by rfl⟩ : syracuseStep 1612663 = 2418995) B2418995
theorem B1612683 : Blo 1611004 1612683 := bstep (se 1 (by rfl) ⟨1209512, by rfl⟩ : syracuseStep 1612683 = 2419025) B2419025
theorem B1612695 : Blo 1611004 1612695 := bstep (se 1 (by rfl) ⟨1209521, by rfl⟩ : syracuseStep 1612695 = 2419043) B2419043
theorem B1612715 : Blo 1611004 1612715 := bstep (se 1 (by rfl) ⟨1209536, by rfl⟩ : syracuseStep 1612715 = 2419073) B2419073
theorem B7748531 : Blo 1611004 7748531 := bstep (se 1 (by rfl) ⟨5811398, by rfl⟩ : syracuseStep 7748531 = 11622797) B11622797
theorem B1612727 : Blo 1611004 1612727 := bstep (se 1 (by rfl) ⟨1209545, by rfl⟩ : syracuseStep 1612727 = 2419091) B2419091
theorem B1612747 : Blo 1611004 1612747 := bstep (se 1 (by rfl) ⟨1209560, by rfl⟩ : syracuseStep 1612747 = 2419121) B2419121
theorem B1612759 : Blo 1611004 1612759 := bstep (se 1 (by rfl) ⟨1209569, by rfl⟩ : syracuseStep 1612759 = 2419139) B2419139
theorem B6118361 : Blo 1611004 6118361 := bstep (se 2 (by rfl) ⟨2294385, by rfl⟩ : syracuseStep 6118361 = 4588771) B4588771
theorem B1612779 : Blo 1611004 1612779 := bstep (se 1 (by rfl) ⟨1209584, by rfl⟩ : syracuseStep 1612779 = 2419169) B2419169
theorem B1612791 : Blo 1611004 1612791 := bstep (se 1 (by rfl) ⟨1209593, by rfl⟩ : syracuseStep 1612791 = 2419187) B2419187
theorem B12409861 : Blo 1611004 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B2718731 : Blo 1611004 2718731 := bstep (se 1 (by rfl) ⟨2039048, by rfl⟩ : syracuseStep 2718731 = 4078097) B4078097
theorem B3628043 : Blo 1611004 3628043 := bstep (se 1 (by rfl) ⟨2721032, by rfl⟩ : syracuseStep 3628043 = 5442065) B5442065
theorem B1612811 : Blo 1611004 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B1612823 : Blo 1611004 1612823 := bstep (se 1 (by rfl) ⟨1209617, by rfl⟩ : syracuseStep 1612823 = 2419235) B2419235
theorem B1612843 : Blo 1611004 1612843 := bstep (se 1 (by rfl) ⟨1209632, by rfl⟩ : syracuseStep 1612843 = 2419265) B2419265
theorem B1612855 : Blo 1611004 1612855 := bstep (se 1 (by rfl) ⟨1209641, by rfl⟩ : syracuseStep 1612855 = 2419283) B2419283
theorem B3628097 : Blo 1611004 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B1612875 : Blo 1611004 1612875 := bstep (se 1 (by rfl) ⟨1209656, by rfl⟩ : syracuseStep 1612875 = 2419313) B2419313
theorem B1612887 : Blo 1611004 1612887 := bstep (se 1 (by rfl) ⟨1209665, by rfl⟩ : syracuseStep 1612887 = 2419331) B2419331
theorem B1612907 : Blo 1611004 1612907 := bstep (se 1 (by rfl) ⟨1209680, by rfl⟩ : syracuseStep 1612907 = 2419361) B2419361
theorem B1612919 : Blo 1611004 1612919 := bstep (se 1 (by rfl) ⟨1209689, by rfl⟩ : syracuseStep 1612919 = 2419379) B2419379
theorem B2718859 : Blo 1611004 2718859 := bstep (se 1 (by rfl) ⟨2039144, by rfl⟩ : syracuseStep 2718859 = 4078289) B4078289
theorem B1612939 : Blo 1611004 1612939 := bstep (se 1 (by rfl) ⟨1209704, by rfl⟩ : syracuseStep 1612939 = 2419409) B2419409
theorem B1612951 : Blo 1611004 1612951 := bstep (se 1 (by rfl) ⟨1209713, by rfl⟩ : syracuseStep 1612951 = 2419427) B2419427
theorem B1612971 : Blo 1611004 1612971 := bstep (se 1 (by rfl) ⟨1209728, by rfl⟩ : syracuseStep 1612971 = 2419457) B2419457
theorem B1612983 : Blo 1611004 1612983 := bstep (se 1 (by rfl) ⟨1209737, by rfl⟩ : syracuseStep 1612983 = 2419475) B2419475
theorem B4136129 : Blo 1611004 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B4078795 : Blo 1611004 4078795 := bstep (se 1 (by rfl) ⟨3059096, by rfl⟩ : syracuseStep 4078795 = 6118193) B6118193
theorem B1613003 : Blo 1611004 1613003 := bstep (se 1 (by rfl) ⟨1209752, by rfl⟩ : syracuseStep 1613003 = 2419505) B2419505
theorem B11771153 : Blo 1611004 11771153 := bstep (se 2 (by rfl) ⟨4414182, by rfl⟩ : syracuseStep 11771153 = 8828365) B8828365
theorem B8158481 : Blo 1611004 8158481 := bstep (se 2 (by rfl) ⟨3059430, by rfl⟩ : syracuseStep 8158481 = 6118861) B6118861
theorem B6118679 : Blo 1611004 6118679 := bstep (se 1 (by rfl) ⟨4589009, by rfl⟩ : syracuseStep 6118679 = 9178019) B9178019
theorem B2719001 : Blo 1611004 2719001 := bstep (se 2 (by rfl) ⟨1019625, by rfl⟩ : syracuseStep 2719001 = 2039251) B2039251
theorem B3628313 : Blo 1611004 3628313 := bstep (se 2 (by rfl) ⟨1360617, by rfl⟩ : syracuseStep 3628313 = 2721235) B2721235
theorem B5438771 : Blo 1611004 5438771 := bstep (se 1 (by rfl) ⟨4079078, by rfl⟩ : syracuseStep 5438771 = 8158157) B8158157
theorem B4078937 : Blo 1611004 4078937 := bstep (se 2 (by rfl) ⟨1529601, by rfl⟩ : syracuseStep 4078937 = 3059203) B3059203
theorem B3267955 : Blo 1611004 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B3628403 : Blo 1611004 3628403 := bstep (se 1 (by rfl) ⟨2721302, by rfl⟩ : syracuseStep 3628403 = 5442605) B5442605
theorem B3628439 : Blo 1611004 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B2719129 : Blo 1611004 2719129 := bstep (se 2 (by rfl) ⟨1019673, by rfl⟩ : syracuseStep 2719129 = 2039347) B2039347
theorem B8158643 : Blo 1611004 8158643 := bstep (se 1 (by rfl) ⟨6118982, by rfl⟩ : syracuseStep 8158643 = 12237965) B12237965
theorem B3268019 : Blo 1611004 3268019 := bstep (se 1 (by rfl) ⟨2451014, by rfl⟩ : syracuseStep 3268019 = 4902029) B4902029
theorem B3538379 : Blo 1611004 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B5439041 : Blo 1611004 5439041 := bstep (se 2 (by rfl) ⟨2039640, by rfl⟩ : syracuseStep 5439041 = 4079281) B4079281
theorem B3628619 : Blo 1611004 3628619 := bstep (se 1 (by rfl) ⟨2721464, by rfl⟩ : syracuseStep 3628619 = 5442929) B5442929
theorem B3628673 : Blo 1611004 3628673 := bstep (se 2 (by rfl) ⟨1360752, by rfl⟩ : syracuseStep 3628673 = 2721505) B2721505
theorem B23600771 : Blo 1611004 23600771 := bstep (se 1 (by rfl) ⟨17700578, by rfl⟩ : syracuseStep 23600771 = 35401157) B35401157
theorem B7356035 : Blo 1611004 7356035 := bstep (se 1 (by rfl) ⟨5517026, by rfl⟩ : syracuseStep 7356035 = 11034053) B11034053
theorem B13770445 : Blo 1611004 13770445 := bstep (se 3 (by rfl) ⟨2581958, by rfl⟩ : syracuseStep 13770445 = 5163917) B5163917
theorem B2039575 : Blo 1611004 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B3628889 : Blo 1611004 3628889 := bstep (se 2 (by rfl) ⟨1360833, by rfl⟩ : syracuseStep 3628889 = 2721667) B2721667
theorem B9183077 : Blo 1611004 9183077 := bstep (se 4 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 9183077 = 1721827) B1721827
theorem B2416523 : Blo 1611004 2416523 := bstep (se 1 (by rfl) ⟨1812392, by rfl⟩ : syracuseStep 2416523 = 3624785) B3624785
theorem B2416535 : Blo 1611004 2416535 := bstep (se 1 (by rfl) ⟨1812401, by rfl⟩ : syracuseStep 2416535 = 3624803) B3624803
theorem B6119347 : Blo 1611004 6119347 := bstep (se 1 (by rfl) ⟨4589510, by rfl⟩ : syracuseStep 6119347 = 9179021) B9179021
theorem B3628979 : Blo 1611004 3628979 := bstep (se 1 (by rfl) ⟨2721734, by rfl⟩ : syracuseStep 3628979 = 5443469) B5443469
theorem B2719703 : Blo 1611004 2719703 := bstep (se 1 (by rfl) ⟨2039777, by rfl⟩ : syracuseStep 2719703 = 4079555) B4079555
theorem B2416601 : Blo 1611004 2416601 := bstep (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) B1812451
theorem B18366425 : Blo 1611004 18366425 := bstep (se 2 (by rfl) ⟨6887409, by rfl⟩ : syracuseStep 18366425 = 13774819) B13774819
theorem B3629015 : Blo 1611004 3629015 := bstep (se 1 (by rfl) ⟨2721761, by rfl⟩ : syracuseStep 3629015 = 5443523) B5443523
theorem B2416655 : Blo 1611004 2416655 := bstep (se 1 (by rfl) ⟨1812491, by rfl⟩ : syracuseStep 2416655 = 3624983) B3624983
theorem B2416697 : Blo 1611004 2416697 := bstep (se 2 (by rfl) ⟨906261, by rfl⟩ : syracuseStep 2416697 = 1812523) B1812523
theorem B2416775 : Blo 1611004 2416775 := bstep (se 1 (by rfl) ⟨1812581, by rfl⟩ : syracuseStep 2416775 = 3625163) B3625163
theorem B2416811 : Blo 1611004 2416811 := bstep (se 1 (by rfl) ⟨1812608, by rfl⟩ : syracuseStep 2416811 = 3625217) B3625217
theorem B10322093 : Blo 1611004 10322093 := bstep (se 3 (by rfl) ⟨1935392, by rfl⟩ : syracuseStep 10322093 = 3870785) B3870785
theorem B2039995 : Blo 1611004 2039995 := bstep (se 1 (by rfl) ⟨1529996, by rfl⟩ : syracuseStep 2039995 = 3059993) B3059993
theorem B2416841 : Blo 1611004 2416841 := bstep (se 2 (by rfl) ⟨906315, by rfl⟩ : syracuseStep 2416841 = 1812631) B1812631
theorem B5439689 : Blo 1611004 5439689 := bstep (se 2 (by rfl) ⟨2039883, by rfl⟩ : syracuseStep 5439689 = 4079767) B4079767
theorem B9175355 : Blo 1611004 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B2416955 : Blo 1611004 2416955 := bstep (se 1 (by rfl) ⟨1812716, by rfl⟩ : syracuseStep 2416955 = 3625433) B3625433
theorem B3875159 : Blo 1611004 3875159 := bstep (se 1 (by rfl) ⟨2906369, by rfl⟩ : syracuseStep 3875159 = 5812739) B5812739
theorem B9183577 : Blo 1611004 9183577 := bstep (se 2 (by rfl) ⟨3443841, by rfl⟩ : syracuseStep 9183577 = 6887683) B6887683
theorem B69714269 : Blo 1611004 69714269 := bstep (se 3 (by rfl) ⟨13071425, by rfl⟩ : syracuseStep 69714269 = 26142851) B26142851
theorem B2417015 : Blo 1611004 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B2720135 : Blo 1611004 2720135 := bstep (se 1 (by rfl) ⟨2040101, by rfl⟩ : syracuseStep 2720135 = 4080203) B4080203
theorem B2417039 : Blo 1611004 2417039 := bstep (se 1 (by rfl) ⟨1812779, by rfl⟩ : syracuseStep 2417039 = 3625559) B3625559
theorem B6119833 : Blo 1611004 6119833 := bstep (se 2 (by rfl) ⟨2294937, by rfl⟩ : syracuseStep 6119833 = 4589875) B4589875
theorem B2417081 : Blo 1611004 2417081 := bstep (se 2 (by rfl) ⟨906405, by rfl⟩ : syracuseStep 2417081 = 1812811) B1812811
theorem B4358657 : Blo 1611004 4358657 := bstep (se 2 (by rfl) ⟨1634496, by rfl⟩ : syracuseStep 4358657 = 3268993) B3268993
theorem B2417159 : Blo 1611004 2417159 := bstep (se 1 (by rfl) ⟨1812869, by rfl⟩ : syracuseStep 2417159 = 3625739) B3625739
theorem B11616797 : Blo 1611004 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B30990883 : Blo 1611004 30990883 := bstep (se 1 (by rfl) ⟨23243162, by rfl⟩ : syracuseStep 30990883 = 46486325) B46486325
theorem B2417195 : Blo 1611004 2417195 := bstep (se 1 (by rfl) ⟨1812896, by rfl⟩ : syracuseStep 2417195 = 3625793) B3625793
theorem B2417225 : Blo 1611004 2417225 := bstep (se 2 (by rfl) ⟨906459, by rfl⟩ : syracuseStep 2417225 = 1812919) B1812919
theorem B7742071 : Blo 1611004 7742071 := bstep (se 1 (by rfl) ⟨5806553, by rfl⟩ : syracuseStep 7742071 = 11613107) B11613107
theorem B2040491 : Blo 1611004 2040491 := bstep (se 1 (by rfl) ⟨1530368, by rfl⟩ : syracuseStep 2040491 = 3060737) B3060737
theorem B2417339 : Blo 1611004 2417339 := bstep (se 1 (by rfl) ⟨1813004, by rfl⟩ : syracuseStep 2417339 = 3626009) B3626009
theorem B6120137 : Blo 1611004 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B2417399 : Blo 1611004 2417399 := bstep (se 1 (by rfl) ⟨1813049, by rfl⟩ : syracuseStep 2417399 = 3626099) B3626099
theorem B4080395 : Blo 1611004 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B4899599 : Blo 1611004 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B2417423 : Blo 1611004 2417423 := bstep (se 1 (by rfl) ⟨1813067, by rfl⟩ : syracuseStep 2417423 = 3626135) B3626135
theorem B2417465 : Blo 1611004 2417465 := bstep (se 2 (by rfl) ⟨906549, by rfl⟩ : syracuseStep 2417465 = 1813099) B1813099
theorem B3441467 : Blo 1611004 3441467 := bstep (se 1 (by rfl) ⟨2581100, by rfl⟩ : syracuseStep 3441467 = 5162201) B5162201
theorem B2417543 : Blo 1611004 2417543 := bstep (se 1 (by rfl) ⟨1813157, by rfl⟩ : syracuseStep 2417543 = 3626315) B3626315
theorem B5440391 : Blo 1611004 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B5809049 : Blo 1611004 5809049 := bstep (se 2 (by rfl) ⟨2178393, by rfl⟩ : syracuseStep 5809049 = 4356787) B4356787
theorem B2417579 : Blo 1611004 2417579 := bstep (se 1 (by rfl) ⟨1813184, by rfl⟩ : syracuseStep 2417579 = 3626369) B3626369
theorem B2417609 : Blo 1611004 2417609 := bstep (se 2 (by rfl) ⟨906603, by rfl⟩ : syracuseStep 2417609 = 1813207) B1813207
theorem B2720783 : Blo 1611004 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B2417723 : Blo 1611004 2417723 := bstep (se 1 (by rfl) ⟨1813292, by rfl⟩ : syracuseStep 2417723 = 3626585) B3626585
theorem B2417783 : Blo 1611004 2417783 := bstep (se 1 (by rfl) ⟨1813337, by rfl⟩ : syracuseStep 2417783 = 3626675) B3626675
theorem B2040967 : Blo 1611004 2040967 := bstep (se 1 (by rfl) ⟨1530725, by rfl⟩ : syracuseStep 2040967 = 3061451) B3061451
theorem B2417807 : Blo 1611004 2417807 := bstep (se 1 (by rfl) ⟨1813355, by rfl⟩ : syracuseStep 2417807 = 3626711) B3626711
theorem B8717485 : Blo 1611004 8717485 := bstep (se 3 (by rfl) ⟨1634528, by rfl⟩ : syracuseStep 8717485 = 3269057) B3269057
theorem B2417849 : Blo 1611004 2417849 := bstep (se 2 (by rfl) ⟨906693, by rfl⟩ : syracuseStep 2417849 = 1813387) B1813387
theorem B5440769 : Blo 1611004 5440769 := bstep (se 2 (by rfl) ⟨2040288, by rfl⟩ : syracuseStep 5440769 = 4080577) B4080577
theorem B2417927 : Blo 1611004 2417927 := bstep (se 1 (by rfl) ⟨1813445, by rfl⟩ : syracuseStep 2417927 = 3626891) B3626891
theorem B2417963 : Blo 1611004 2417963 := bstep (se 1 (by rfl) ⟨1813472, by rfl⟩ : syracuseStep 2417963 = 3626945) B3626945
theorem B2417993 : Blo 1611004 2417993 := bstep (se 2 (by rfl) ⟨906747, by rfl⟩ : syracuseStep 2417993 = 1813495) B1813495
theorem B4588919 : Blo 1611004 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B6882695 : Blo 1611004 6882695 := bstep (se 1 (by rfl) ⟨5162021, by rfl⟩ : syracuseStep 6882695 = 10324043) B10324043
theorem B4081043 : Blo 1611004 4081043 := bstep (se 1 (by rfl) ⟨3060782, by rfl⟩ : syracuseStep 4081043 = 6121565) B6121565
theorem B2295211 : Blo 1611004 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B2418107 : Blo 1611004 2418107 := bstep (se 1 (by rfl) ⟨1813580, by rfl⟩ : syracuseStep 2418107 = 3627161) B3627161
theorem B2418167 : Blo 1611004 2418167 := bstep (se 1 (by rfl) ⟨1813625, by rfl⟩ : syracuseStep 2418167 = 3627251) B3627251
theorem B2418191 : Blo 1611004 2418191 := bstep (se 1 (by rfl) ⟨1813643, by rfl⟩ : syracuseStep 2418191 = 3627287) B3627287
theorem B2721323 : Blo 1611004 2721323 := bstep (se 1 (by rfl) ⟨2040992, by rfl⟩ : syracuseStep 2721323 = 4081985) B4081985
theorem B2418233 : Blo 1611004 2418233 := bstep (se 2 (by rfl) ⟨906837, by rfl⟩ : syracuseStep 2418233 = 1813675) B1813675
theorem B6121079 : Blo 1611004 6121079 := bstep (se 1 (by rfl) ⟨4590809, by rfl⟩ : syracuseStep 6121079 = 9181619) B9181619
theorem B2418311 : Blo 1611004 2418311 := bstep (se 1 (by rfl) ⟨1813733, by rfl⟩ : syracuseStep 2418311 = 3627467) B3627467
theorem B2418347 : Blo 1611004 2418347 := bstep (se 1 (by rfl) ⟨1813760, by rfl⟩ : syracuseStep 2418347 = 3627521) B3627521
theorem B4081337 : Blo 1611004 4081337 := bstep (se 2 (by rfl) ⟨1530501, by rfl⟩ : syracuseStep 4081337 = 3061003) B3061003
theorem B2418377 : Blo 1611004 2418377 := bstep (se 2 (by rfl) ⟨906891, by rfl⟩ : syracuseStep 2418377 = 1813783) B1813783
theorem B18351845 : Blo 1611004 18351845 := bstep (se 4 (by rfl) ⟨1720485, by rfl⟩ : syracuseStep 18351845 = 3440971) B3440971
theorem B9176813 : Blo 1611004 9176813 := bstep (se 3 (by rfl) ⟨1720652, by rfl⟩ : syracuseStep 9176813 = 3441305) B3441305
theorem B3442475 : Blo 1611004 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B2418491 : Blo 1611004 2418491 := bstep (se 1 (by rfl) ⟨1813868, by rfl⟩ : syracuseStep 2418491 = 3627737) B3627737
theorem B4359997 : Blo 1611004 4359997 := bstep (se 3 (by rfl) ⟨817499, by rfl⟩ : syracuseStep 4359997 = 1634999) B1634999
theorem B2418551 : Blo 1611004 2418551 := bstep (se 1 (by rfl) ⟨1813913, by rfl⟩ : syracuseStep 2418551 = 3627827) B3627827
theorem B2418575 : Blo 1611004 2418575 := bstep (se 1 (by rfl) ⟨1813931, by rfl⟩ : syracuseStep 2418575 = 3627863) B3627863
theorem B2418617 : Blo 1611004 2418617 := bstep (se 2 (by rfl) ⟨906981, by rfl⟩ : syracuseStep 2418617 = 1813963) B1813963
theorem B2721721 : Blo 1611004 2721721 := bstep (se 2 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 2721721 = 2041291) B2041291
theorem B1812487 : Blo 1611004 1812487 := bstep (se 1 (by rfl) ⟨1359365, by rfl⟩ : syracuseStep 1812487 = 2718731) B2718731
theorem B2418695 : Blo 1611004 2418695 := bstep (se 1 (by rfl) ⟨1814021, by rfl⟩ : syracuseStep 2418695 = 3628043) B3628043
theorem B9185309 : Blo 1611004 9185309 := bstep (se 3 (by rfl) ⟨1722245, by rfl⟩ : syracuseStep 9185309 = 3444491) B3444491
theorem B5441579 : Blo 1611004 5441579 := bstep (se 1 (by rfl) ⟨4081184, by rfl⟩ : syracuseStep 5441579 = 8162369) B8162369
theorem B2418731 : Blo 1611004 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B2418761 : Blo 1611004 2418761 := bstep (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) B1814071
theorem B1812667 : Blo 1611004 1812667 := bstep (se 1 (by rfl) ⟨1359500, by rfl⟩ : syracuseStep 1812667 = 2719001) B2719001
theorem B2418875 : Blo 1611004 2418875 := bstep (se 1 (by rfl) ⟨1814156, by rfl⟩ : syracuseStep 2418875 = 3628313) B3628313
theorem B2418935 : Blo 1611004 2418935 := bstep (se 1 (by rfl) ⟨1814201, by rfl⟩ : syracuseStep 2418935 = 3628403) B3628403
theorem B2418959 : Blo 1611004 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B18360593 : Blo 1611004 18360593 := bstep (se 2 (by rfl) ⟨6885222, by rfl⟩ : syracuseStep 18360593 = 13770445) B13770445
theorem B2419001 : Blo 1611004 2419001 := bstep (se 2 (by rfl) ⟨907125, by rfl⟩ : syracuseStep 2419001 = 1814251) B1814251
theorem B4082035 : Blo 1611004 4082035 := bstep (se 1 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 4082035 = 6123053) B6123053
theorem B2419079 : Blo 1611004 2419079 := bstep (se 1 (by rfl) ⟨1814309, by rfl⟩ : syracuseStep 2419079 = 3628619) B3628619
theorem B2419115 : Blo 1611004 2419115 := bstep (se 1 (by rfl) ⟨1814336, by rfl⟩ : syracuseStep 2419115 = 3628673) B3628673
theorem B8161721 : Blo 1611004 8161721 := bstep (se 2 (by rfl) ⟨3060645, by rfl⟩ : syracuseStep 8161721 = 6121291) B6121291
theorem B2419145 : Blo 1611004 2419145 := bstep (se 2 (by rfl) ⟨907179, by rfl⟩ : syracuseStep 2419145 = 1814359) B1814359
theorem B4082177 : Blo 1611004 4082177 := bstep (se 2 (by rfl) ⟨1530816, by rfl⟩ : syracuseStep 4082177 = 3061633) B3061633
theorem B1935931 : Blo 1611004 1935931 := bstep (se 1 (by rfl) ⟨1451948, by rfl⟩ : syracuseStep 1935931 = 2903897) B2903897
theorem B2419259 : Blo 1611004 2419259 := bstep (se 1 (by rfl) ⟨1814444, by rfl⟩ : syracuseStep 2419259 = 3628889) B3628889
theorem B33999425 : Blo 1611004 33999425 := bstep (se 2 (by rfl) ⟨12749784, by rfl⟩ : syracuseStep 33999425 = 25499569) B25499569
theorem B6122051 : Blo 1611004 6122051 := bstep (se 1 (by rfl) ⟨4591538, by rfl⟩ : syracuseStep 6122051 = 9183077) B9183077
theorem B15501901 : Blo 1611004 15501901 := bstep (se 3 (by rfl) ⟨2906606, by rfl⟩ : syracuseStep 15501901 = 5813213) B5813213
theorem B4655731 : Blo 1611004 4655731 := bstep (se 1 (by rfl) ⟨3491798, by rfl⟩ : syracuseStep 4655731 = 6983597) B6983597
theorem B2419319 : Blo 1611004 2419319 := bstep (se 1 (by rfl) ⟨1814489, by rfl⟩ : syracuseStep 2419319 = 3628979) B3628979
theorem B1813135 : Blo 1611004 1813135 := bstep (se 1 (by rfl) ⟨1359851, by rfl⟩ : syracuseStep 1813135 = 2719703) B2719703
theorem B2419343 : Blo 1611004 2419343 := bstep (se 1 (by rfl) ⟨1814507, by rfl⟩ : syracuseStep 2419343 = 3629015) B3629015
theorem B2419385 : Blo 1611004 2419385 := bstep (se 2 (by rfl) ⟨907269, by rfl⟩ : syracuseStep 2419385 = 1814539) B1814539
theorem B9185993 : Blo 1611004 9185993 := bstep (se 2 (by rfl) ⟨3444747, by rfl⟩ : syracuseStep 9185993 = 6889495) B6889495
theorem B2419463 : Blo 1611004 2419463 := bstep (se 1 (by rfl) ⟨1814597, by rfl⟩ : syracuseStep 2419463 = 3629195) B3629195
theorem B11774735 : Blo 1611004 11774735 := bstep (se 1 (by rfl) ⟨8831051, by rfl⟩ : syracuseStep 11774735 = 17662103) B17662103
theorem B6884129 : Blo 1611004 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B2419499 : Blo 1611004 2419499 := bstep (se 1 (by rfl) ⟨1814624, by rfl⟩ : syracuseStep 2419499 = 3629249) B3629249
theorem B2583497 : Blo 1611004 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B4082633 : Blo 1611004 4082633 := bstep (se 2 (by rfl) ⟨1530987, by rfl⟩ : syracuseStep 4082633 = 3061975) B3061975
theorem B3058823 : Blo 1611004 3058823 := bstep (se 1 (by rfl) ⟨2294117, by rfl⟩ : syracuseStep 3058823 = 4588235) B4588235
theorem B1813639 : Blo 1611004 1813639 := bstep (se 1 (by rfl) ⟨1360229, by rfl⟩ : syracuseStep 1813639 = 2720459) B2720459
theorem B1813819 : Blo 1611004 1813819 := bstep (se 1 (by rfl) ⟨1360364, by rfl⟩ : syracuseStep 1813819 = 2720729) B2720729
theorem B5442875 : Blo 1611004 5442875 := bstep (se 1 (by rfl) ⟨4082156, by rfl⟩ : syracuseStep 5442875 = 8164313) B8164313
theorem B3444115 : Blo 1611004 3444115 := bstep (se 1 (by rfl) ⟨2583086, by rfl⟩ : syracuseStep 3444115 = 5166173) B5166173
theorem B1936811 : Blo 1611004 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B9080363 : Blo 1611004 9080363 := bstep (se 1 (by rfl) ⟨6810272, by rfl⟩ : syracuseStep 9080363 = 13620545) B13620545
theorem B12406391 : Blo 1611004 12406391 := bstep (se 1 (by rfl) ⟨9304793, by rfl⟩ : syracuseStep 12406391 = 18609587) B18609587
theorem B8163017 : Blo 1611004 8163017 := bstep (se 2 (by rfl) ⟨3061131, by rfl⟩ : syracuseStep 8163017 = 6122263) B6122263
theorem B6885121 : Blo 1611004 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B1838863 : Blo 1611004 1838863 := bstep (se 1 (by rfl) ⟨1379147, by rfl⟩ : syracuseStep 1838863 = 2758295) B2758295
theorem B1814287 : Blo 1611004 1814287 := bstep (se 1 (by rfl) ⟨1360715, by rfl⟩ : syracuseStep 1814287 = 2721431) B2721431
theorem B5443361 : Blo 1611004 5443361 := bstep (se 2 (by rfl) ⟨2041260, by rfl⟩ : syracuseStep 5443361 = 4082521) B4082521
theorem B3624839 : Blo 1611004 3624839 := bstep (se 1 (by rfl) ⟨2718629, by rfl⟩ : syracuseStep 3624839 = 5437259) B5437259
theorem B4190087 : Blo 1611004 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B41308055 : Blo 1611004 41308055 := bstep (se 1 (by rfl) ⟨30981041, by rfl⟩ : syracuseStep 41308055 = 61962083) B61962083
theorem B9809849 : Blo 1611004 9809849 := bstep (se 2 (by rfl) ⟨3678693, by rfl⟩ : syracuseStep 9809849 = 7357387) B7357387
theorem B4591561 : Blo 1611004 4591561 := bstep (se 2 (by rfl) ⟨1721835, by rfl⟩ : syracuseStep 4591561 = 3443671) B3443671
theorem B1839119 : Blo 1611004 1839119 := bstep (se 1 (by rfl) ⟨1379339, by rfl⟩ : syracuseStep 1839119 = 2758679) B2758679
theorem B3625019 : Blo 1611004 3625019 := bstep (se 1 (by rfl) ⟨2718764, by rfl⟩ : syracuseStep 3625019 = 5437529) B5437529
theorem B9179203 : Blo 1611004 9179203 := bstep (se 1 (by rfl) ⟨6884402, by rfl⟩ : syracuseStep 9179203 = 13768805) B13768805
theorem B2207879 : Blo 1611004 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B14151853 : Blo 1611004 14151853 := bstep (se 3 (by rfl) ⟨2653472, by rfl⟩ : syracuseStep 14151853 = 5306945) B5306945
theorem B3625145 : Blo 1611004 3625145 := bstep (se 2 (by rfl) ⟨1359429, by rfl⟩ : syracuseStep 3625145 = 2718859) B2718859
theorem B6123721 : Blo 1611004 6123721 := bstep (se 2 (by rfl) ⟨2296395, by rfl⟩ : syracuseStep 6123721 = 4592791) B4592791
theorem B19616093 : Blo 1611004 19616093 := bstep (se 3 (by rfl) ⟨3678017, by rfl⟩ : syracuseStep 19616093 = 7356035) B7356035
theorem B3625487 : Blo 1611004 3625487 := bstep (se 1 (by rfl) ⟨2719115, by rfl⟩ : syracuseStep 3625487 = 5438231) B5438231
theorem B3625505 : Blo 1611004 3625505 := bstep (se 2 (by rfl) ⟨1359564, by rfl⟩ : syracuseStep 3625505 = 2719129) B2719129
theorem B17429093 : Blo 1611004 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B5165687 : Blo 1611004 5165687 := bstep (se 1 (by rfl) ⟨3874265, by rfl⟩ : syracuseStep 5165687 = 7748531) B7748531
theorem B12235535 : Blo 1611004 12235535 := bstep (se 1 (by rfl) ⟨9176651, by rfl⟩ : syracuseStep 12235535 = 18353303) B18353303
theorem B2757419 : Blo 1611004 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B3625847 : Blo 1611004 3625847 := bstep (se 1 (by rfl) ⟨2719385, by rfl⟩ : syracuseStep 3625847 = 5438771) B5438771
theorem B8156051 : Blo 1611004 8156051 := bstep (se 1 (by rfl) ⟨6117038, by rfl⟩ : syracuseStep 8156051 = 12234077) B12234077
theorem B5813201 : Blo 1611004 5813201 := bstep (se 2 (by rfl) ⟨2179950, by rfl⟩ : syracuseStep 5813201 = 4359901) B4359901
theorem B37745675 : Blo 1611004 37745675 := bstep (se 1 (by rfl) ⟨28309256, by rfl⟩ : syracuseStep 37745675 = 56618513) B56618513
theorem B3626027 : Blo 1611004 3626027 := bstep (se 1 (by rfl) ⟨2719520, by rfl⟩ : syracuseStep 3626027 = 5439041) B5439041
theorem B15733847 : Blo 1611004 15733847 := bstep (se 1 (by rfl) ⟨11800385, by rfl⟩ : syracuseStep 15733847 = 23600771) B23600771
theorem B18363509 : Blo 1611004 18363509 := bstep (se 5 (by rfl) ⟨860789, by rfl⟩ : syracuseStep 18363509 = 1721579) B1721579
theorem B1611015 : Blo 1611004 1611015 := bstep (se 1 (by rfl) ⟨1208261, by rfl⟩ : syracuseStep 1611015 = 2416523) B2416523
theorem B1611023 : Blo 1611004 1611023 := bstep (se 1 (by rfl) ⟨1208267, by rfl⟩ : syracuseStep 1611023 = 2416535) B2416535
theorem B1611067 : Blo 1611004 1611067 := bstep (se 1 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 1611067 = 2416601) B2416601
theorem B39204155 : Blo 1611004 39204155 := bstep (se 1 (by rfl) ⟨29403116, by rfl⟩ : syracuseStep 39204155 = 58806233) B58806233
theorem B12244283 : Blo 1611004 12244283 := bstep (se 1 (by rfl) ⟨9183212, by rfl⟩ : syracuseStep 12244283 = 18366425) B18366425
theorem B8271193 : Blo 1611004 8271193 := bstep (se 2 (by rfl) ⟨3101697, by rfl⟩ : syracuseStep 8271193 = 6203395) B6203395
theorem B1611143 : Blo 1611004 1611143 := bstep (se 1 (by rfl) ⟨1208357, by rfl⟩ : syracuseStep 1611143 = 2416715) B2416715
theorem B1611151 : Blo 1611004 1611151 := bstep (se 1 (by rfl) ⟨1208363, by rfl⟩ : syracuseStep 1611151 = 2416727) B2416727
theorem B3626387 : Blo 1611004 3626387 := bstep (se 1 (by rfl) ⟨2719790, by rfl⟩ : syracuseStep 3626387 = 5439581) B5439581
theorem B1611195 : Blo 1611004 1611195 := bstep (se 1 (by rfl) ⟨1208396, by rfl⟩ : syracuseStep 1611195 = 2416793) B2416793
theorem B3626441 : Blo 1611004 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B1611271 : Blo 1611004 1611271 := bstep (se 1 (by rfl) ⟨1208453, by rfl⟩ : syracuseStep 1611271 = 2416907) B2416907
theorem B1611279 : Blo 1611004 1611279 := bstep (se 1 (by rfl) ⟨1208459, by rfl⟩ : syracuseStep 1611279 = 2416919) B2416919
theorem B1611323 : Blo 1611004 1611323 := bstep (se 1 (by rfl) ⟨1208492, by rfl⟩ : syracuseStep 1611323 = 2416985) B2416985
theorem B3061307 : Blo 1611004 3061307 := bstep (se 1 (by rfl) ⟨2295980, by rfl⟩ : syracuseStep 3061307 = 4591961) B4591961
theorem B1611399 : Blo 1611004 1611399 := bstep (se 1 (by rfl) ⟨1208549, by rfl⟩ : syracuseStep 1611399 = 2417099) B2417099
theorem B1611407 : Blo 1611004 1611407 := bstep (se 1 (by rfl) ⟨1208555, by rfl⟩ : syracuseStep 1611407 = 2417111) B2417111
theorem B23246513 : Blo 1611004 23246513 := bstep (se 2 (by rfl) ⟨8717442, by rfl⟩ : syracuseStep 23246513 = 17434885) B17434885
theorem B1611451 : Blo 1611004 1611451 := bstep (se 1 (by rfl) ⟨1208588, by rfl⟩ : syracuseStep 1611451 = 2417177) B2417177
theorem B1611527 : Blo 1611004 1611527 := bstep (se 1 (by rfl) ⟨1208645, by rfl⟩ : syracuseStep 1611527 = 2417291) B2417291
theorem B1611535 : Blo 1611004 1611535 := bstep (se 1 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 1611535 = 2417303) B2417303
theorem B3872555 : Blo 1611004 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B1611579 : Blo 1611004 1611579 := bstep (se 1 (by rfl) ⟨1208684, by rfl⟩ : syracuseStep 1611579 = 2417369) B2417369
theorem B1611655 : Blo 1611004 1611655 := bstep (se 1 (by rfl) ⟨1208741, by rfl⟩ : syracuseStep 1611655 = 2417483) B2417483
theorem B1611663 : Blo 1611004 1611663 := bstep (se 1 (by rfl) ⟨1208747, by rfl⟩ : syracuseStep 1611663 = 2417495) B2417495
theorem B13776803 : Blo 1611004 13776803 := bstep (se 1 (by rfl) ⟨10332602, by rfl⟩ : syracuseStep 13776803 = 20665205) B20665205
theorem B1611707 : Blo 1611004 1611707 := bstep (se 1 (by rfl) ⟨1208780, by rfl⟩ : syracuseStep 1611707 = 2417561) B2417561
theorem B9181187 : Blo 1611004 9181187 := bstep (se 1 (by rfl) ⟨6885890, by rfl⟩ : syracuseStep 9181187 = 13771781) B13771781
theorem B1611783 : Blo 1611004 1611783 := bstep (se 1 (by rfl) ⟨1208837, by rfl⟩ : syracuseStep 1611783 = 2417675) B2417675
theorem B8067083 : Blo 1611004 8067083 := bstep (se 1 (by rfl) ⟨6050312, by rfl⟩ : syracuseStep 8067083 = 12100625) B12100625
theorem B1611791 : Blo 1611004 1611791 := bstep (se 1 (by rfl) ⟨1208843, by rfl⟩ : syracuseStep 1611791 = 2417687) B2417687
theorem B3061793 : Blo 1611004 3061793 := bstep (se 2 (by rfl) ⟨1148172, by rfl⟩ : syracuseStep 3061793 = 2296345) B2296345
theorem B5167147 : Blo 1611004 5167147 := bstep (se 1 (by rfl) ⟨3875360, by rfl⟩ : syracuseStep 5167147 = 7750721) B7750721
theorem B1611835 : Blo 1611004 1611835 := bstep (se 1 (by rfl) ⟨1208876, by rfl⟩ : syracuseStep 1611835 = 2417753) B2417753
theorem B7747645 : Blo 1611004 7747645 := bstep (se 3 (by rfl) ⟨1452683, by rfl⟩ : syracuseStep 7747645 = 2905367) B2905367
theorem B1611911 : Blo 1611004 1611911 := bstep (se 1 (by rfl) ⟨1208933, by rfl⟩ : syracuseStep 1611911 = 2417867) B2417867
theorem B3627143 : Blo 1611004 3627143 := bstep (se 1 (by rfl) ⟨2720357, by rfl⟩ : syracuseStep 3627143 = 5440715) B5440715
theorem B1611919 : Blo 1611004 1611919 := bstep (se 1 (by rfl) ⟨1208939, by rfl⟩ : syracuseStep 1611919 = 2417879) B2417879
theorem B46454957 : Blo 1611004 46454957 := bstep (se 3 (by rfl) ⟨8710304, by rfl⟩ : syracuseStep 46454957 = 17420609) B17420609
theorem B1611963 : Blo 1611004 1611963 := bstep (se 1 (by rfl) ⟨1208972, by rfl⟩ : syracuseStep 1611963 = 2417945) B2417945
theorem B23230709 : Blo 1611004 23230709 := bstep (se 5 (by rfl) ⟨1088939, by rfl⟩ : syracuseStep 23230709 = 2177879) B2177879
theorem B1612039 : Blo 1611004 1612039 := bstep (se 1 (by rfl) ⟨1209029, by rfl⟩ : syracuseStep 1612039 = 2418059) B2418059
theorem B3873035 : Blo 1611004 3873035 := bstep (se 1 (by rfl) ⟨2904776, by rfl⟩ : syracuseStep 3873035 = 5809553) B5809553
theorem B1612047 : Blo 1611004 1612047 := bstep (se 1 (by rfl) ⟨1209035, by rfl⟩ : syracuseStep 1612047 = 2418071) B2418071
theorem B235411757 : Blo 1611004 235411757 := bstep (se 3 (by rfl) ⟨44139704, by rfl⟩ : syracuseStep 235411757 = 88279409) B88279409
theorem B1612091 : Blo 1611004 1612091 := bstep (se 1 (by rfl) ⟨1209068, by rfl⟩ : syracuseStep 1612091 = 2418137) B2418137
theorem B3627323 : Blo 1611004 3627323 := bstep (se 1 (by rfl) ⟨2720492, by rfl⟩ : syracuseStep 3627323 = 5440985) B5440985
theorem B17422685 : Blo 1611004 17422685 := bstep (se 3 (by rfl) ⟨3266753, by rfl⟩ : syracuseStep 17422685 = 6533507) B6533507
theorem B1612167 : Blo 1611004 1612167 := bstep (se 1 (by rfl) ⟨1209125, by rfl⟩ : syracuseStep 1612167 = 2418251) B2418251
theorem B1612175 : Blo 1611004 1612175 := bstep (se 1 (by rfl) ⟨1209131, by rfl⟩ : syracuseStep 1612175 = 2418263) B2418263
theorem B3627449 : Blo 1611004 3627449 := bstep (se 2 (by rfl) ⟨1360293, by rfl⟩ : syracuseStep 3627449 = 2720587) B2720587
theorem B1612219 : Blo 1611004 1612219 := bstep (se 1 (by rfl) ⟨1209164, by rfl⟩ : syracuseStep 1612219 = 2418329) B2418329
theorem B8714717 : Blo 1611004 8714717 := bstep (se 3 (by rfl) ⟨1634009, by rfl⟩ : syracuseStep 8714717 = 3268019) B3268019
theorem B1612295 : Blo 1611004 1612295 := bstep (se 1 (by rfl) ⟨1209221, by rfl⟩ : syracuseStep 1612295 = 2418443) B2418443
theorem B1612303 : Blo 1611004 1612303 := bstep (se 1 (by rfl) ⟨1209227, by rfl⟩ : syracuseStep 1612303 = 2418455) B2418455
theorem B1612347 : Blo 1611004 1612347 := bstep (se 1 (by rfl) ⟨1209260, by rfl⟩ : syracuseStep 1612347 = 2418521) B2418521
theorem B11180663 : Blo 1611004 11180663 := bstep (se 1 (by rfl) ⟨8385497, by rfl⟩ : syracuseStep 11180663 = 16770995) B16770995
theorem B1612423 : Blo 1611004 1612423 := bstep (se 1 (by rfl) ⟨1209317, by rfl⟩ : syracuseStep 1612423 = 2418635) B2418635
theorem B1612431 : Blo 1611004 1612431 := bstep (se 1 (by rfl) ⟨1209323, by rfl⟩ : syracuseStep 1612431 = 2418647) B2418647
theorem B2177707 : Blo 1611004 2177707 := bstep (se 1 (by rfl) ⟨1633280, by rfl⟩ : syracuseStep 2177707 = 3266561) B3266561
theorem B16546481 : Blo 1611004 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B1612475 : Blo 1611004 1612475 := bstep (se 1 (by rfl) ⟨1209356, by rfl⟩ : syracuseStep 1612475 = 2418713) B2418713
theorem B5511881 : Blo 1611004 5511881 := bstep (se 2 (by rfl) ⟨2066955, by rfl⟩ : syracuseStep 5511881 = 4133911) B4133911
theorem B1612551 : Blo 1611004 1612551 := bstep (se 1 (by rfl) ⟨1209413, by rfl⟩ : syracuseStep 1612551 = 2418827) B2418827
theorem B3627791 : Blo 1611004 3627791 := bstep (se 1 (by rfl) ⟨2720843, by rfl⟩ : syracuseStep 3627791 = 5441687) B5441687
theorem B1612559 : Blo 1611004 1612559 := bstep (se 1 (by rfl) ⟨1209419, by rfl⟩ : syracuseStep 1612559 = 2418839) B2418839
theorem B3627809 : Blo 1611004 3627809 := bstep (se 2 (by rfl) ⟨1360428, by rfl⟩ : syracuseStep 3627809 = 2720857) B2720857
theorem B1612603 : Blo 1611004 1612603 := bstep (se 1 (by rfl) ⟨1209452, by rfl⟩ : syracuseStep 1612603 = 2418905) B2418905
theorem B4078451 : Blo 1611004 4078451 := bstep (se 1 (by rfl) ⟨3058838, by rfl⟩ : syracuseStep 4078451 = 6117677) B6117677
theorem B4078471 : Blo 1611004 4078471 := bstep (se 1 (by rfl) ⟨3058853, by rfl⟩ : syracuseStep 4078471 = 6117707) B6117707
theorem B1612679 : Blo 1611004 1612679 := bstep (se 1 (by rfl) ⟨1209509, by rfl⟩ : syracuseStep 1612679 = 2419019) B2419019
theorem B1612687 : Blo 1611004 1612687 := bstep (se 1 (by rfl) ⟨1209515, by rfl⟩ : syracuseStep 1612687 = 2419031) B2419031
theorem B6536089 : Blo 1611004 6536089 := bstep (se 2 (by rfl) ⟨2451033, by rfl⟩ : syracuseStep 6536089 = 4902067) B4902067
theorem B5438393 : Blo 1611004 5438393 := bstep (se 2 (by rfl) ⟨2039397, by rfl⟩ : syracuseStep 5438393 = 4078795) B4078795
theorem B2177977 : Blo 1611004 2177977 := bstep (se 2 (by rfl) ⟨816741, by rfl⟩ : syracuseStep 2177977 = 1633483) B1633483
theorem B1612731 : Blo 1611004 1612731 := bstep (se 1 (by rfl) ⟨1209548, by rfl⟩ : syracuseStep 1612731 = 2419097) B2419097
theorem B1612807 : Blo 1611004 1612807 := bstep (se 1 (by rfl) ⟨1209605, by rfl⟩ : syracuseStep 1612807 = 2419211) B2419211
theorem B1612815 : Blo 1611004 1612815 := bstep (se 1 (by rfl) ⟨1209611, by rfl⟩ : syracuseStep 1612815 = 2419223) B2419223
theorem B1612859 : Blo 1611004 1612859 := bstep (se 1 (by rfl) ⟨1209644, by rfl⟩ : syracuseStep 1612859 = 2419289) B2419289
theorem B2718839 : Blo 1611004 2718839 := bstep (se 1 (by rfl) ⟨2039129, by rfl⟩ : syracuseStep 2718839 = 4078259) B4078259
theorem B3628151 : Blo 1611004 3628151 := bstep (se 1 (by rfl) ⟨2721113, by rfl⟩ : syracuseStep 3628151 = 5442227) B5442227
theorem B1612935 : Blo 1611004 1612935 := bstep (se 1 (by rfl) ⟨1209701, by rfl⟩ : syracuseStep 1612935 = 2419403) B2419403
theorem B1612943 : Blo 1611004 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B4078745 : Blo 1611004 4078745 := bstep (se 2 (by rfl) ⟨1529529, by rfl⟩ : syracuseStep 4078745 = 3059059) B3059059
theorem B3873977 : Blo 1611004 3873977 := bstep (se 2 (by rfl) ⟨1452741, by rfl⟩ : syracuseStep 3873977 = 2905483) B2905483
theorem B1612987 : Blo 1611004 1612987 := bstep (se 1 (by rfl) ⟨1209740, by rfl⟩ : syracuseStep 1612987 = 2419481) B2419481
theorem B11623661 : Blo 1611004 11623661 := bstep (se 3 (by rfl) ⟨2179436, by rfl⟩ : syracuseStep 11623661 = 4358873) B4358873
theorem B3628331 : Blo 1611004 3628331 := bstep (se 1 (by rfl) ⟨2721248, by rfl⟩ : syracuseStep 3628331 = 5442497) B5442497
theorem B4078907 : Blo 1611004 4078907 := bstep (se 1 (by rfl) ⟨3059180, by rfl⟩ : syracuseStep 4078907 = 6118361) B6118361
theorem B7847435 : Blo 1611004 7847435 := bstep (se 1 (by rfl) ⟨5885576, by rfl⟩ : syracuseStep 7847435 = 11771153) B11771153
theorem B5438987 : Blo 1611004 5438987 := bstep (se 1 (by rfl) ⟨4079240, by rfl⟩ : syracuseStep 5438987 = 8158481) B8158481
theorem B4079119 : Blo 1611004 4079119 := bstep (se 1 (by rfl) ⟨3059339, by rfl⟩ : syracuseStep 4079119 = 6118679) B6118679
theorem B2719291 : Blo 1611004 2719291 := bstep (se 1 (by rfl) ⟨2039468, by rfl⟩ : syracuseStep 2719291 = 4078937) B4078937
theorem B5439095 : Blo 1611004 5439095 := bstep (se 1 (by rfl) ⟨4079321, by rfl⟩ : syracuseStep 5439095 = 8158643) B8158643
theorem B2358919 : Blo 1611004 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3628691 : Blo 1611004 3628691 := bstep (se 1 (by rfl) ⟨2721518, by rfl⟩ : syracuseStep 3628691 = 5443037) B5443037
theorem B2719433 : Blo 1611004 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B3628745 : Blo 1611004 3628745 := bstep (se 2 (by rfl) ⟨1360779, by rfl⟩ : syracuseStep 3628745 = 2721559) B2721559
theorem B4079393 : Blo 1611004 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B2039671 : Blo 1611004 2039671 := bstep (se 1 (by rfl) ⟨1529753, by rfl⟩ : syracuseStep 2039671 = 3059507) B3059507
theorem B8159129 : Blo 1611004 8159129 := bstep (se 2 (by rfl) ⟨3059673, by rfl⟩ : syracuseStep 8159129 = 6119347) B6119347
theorem B2416571 : Blo 1611004 2416571 := bstep (se 1 (by rfl) ⟨1812428, by rfl⟩ : syracuseStep 2416571 = 3624857) B3624857
theorem B2416631 : Blo 1611004 2416631 := bstep (se 1 (by rfl) ⟨1812473, by rfl⟩ : syracuseStep 2416631 = 3624947) B3624947
theorem B2416649 : Blo 1611004 2416649 := bstep (se 2 (by rfl) ⟨906243, by rfl⟩ : syracuseStep 2416649 = 1812487) B1812487
theorem B2416679 : Blo 1611004 2416679 := bstep (se 1 (by rfl) ⟨1812509, by rfl⟩ : syracuseStep 2416679 = 3625019) B3625019
theorem B6889529 : Blo 1611004 6889529 := bstep (se 2 (by rfl) ⟨2583573, by rfl⟩ : syracuseStep 6889529 = 5167147) B5167147
theorem B10330193 : Blo 1611004 10330193 := bstep (se 2 (by rfl) ⟨3873822, by rfl⟩ : syracuseStep 10330193 = 7747645) B7747645
theorem B12238937 : Blo 1611004 12238937 := bstep (se 2 (by rfl) ⟨4589601, by rfl⟩ : syracuseStep 12238937 = 9179203) B9179203
theorem B86048885 : Blo 1611004 86048885 := bstep (se 5 (by rfl) ⟨4033541, by rfl⟩ : syracuseStep 86048885 = 8067083) B8067083
theorem B2416763 : Blo 1611004 2416763 := bstep (se 1 (by rfl) ⟨1812572, by rfl⟩ : syracuseStep 2416763 = 3625145) B3625145
theorem B2416889 : Blo 1611004 2416889 := bstep (se 2 (by rfl) ⟨906333, by rfl⟩ : syracuseStep 2416889 = 1812667) B1812667
theorem B2719993 : Blo 1611004 2719993 := bstep (se 2 (by rfl) ⟨1019997, by rfl⟩ : syracuseStep 2719993 = 2039995) B2039995
theorem B2416991 : Blo 1611004 2416991 := bstep (se 1 (by rfl) ⟨1812743, by rfl⟩ : syracuseStep 2416991 = 3625487) B3625487
theorem B2417003 : Blo 1611004 2417003 := bstep (se 1 (by rfl) ⟨1812752, by rfl⟩ : syracuseStep 2417003 = 3625505) B3625505
theorem B27525581 : Blo 1611004 27525581 := bstep (se 3 (by rfl) ⟨5161046, by rfl⟩ : syracuseStep 27525581 = 10322093) B10322093
theorem B4080091 : Blo 1611004 4080091 := bstep (se 1 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 4080091 = 6120137) B6120137
theorem B2720263 : Blo 1611004 2720263 := bstep (se 1 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 2720263 = 4080395) B4080395
theorem B8159777 : Blo 1611004 8159777 := bstep (se 2 (by rfl) ⟨3059916, by rfl⟩ : syracuseStep 8159777 = 6119833) B6119833
theorem B2417231 : Blo 1611004 2417231 := bstep (se 1 (by rfl) ⟨1812923, by rfl⟩ : syracuseStep 2417231 = 3625847) B3625847
theorem B3875467 : Blo 1611004 3875467 := bstep (se 1 (by rfl) ⟨2906600, by rfl⟩ : syracuseStep 3875467 = 5813201) B5813201
theorem B2417351 : Blo 1611004 2417351 := bstep (se 1 (by rfl) ⟨1813013, by rfl⟩ : syracuseStep 2417351 = 3626027) B3626027
theorem B41321177 : Blo 1611004 41321177 := bstep (se 2 (by rfl) ⟨15495441, by rfl⟩ : syracuseStep 41321177 = 30990883) B30990883
theorem B2581241 : Blo 1611004 2581241 := bstep (se 2 (by rfl) ⟨967965, by rfl⟩ : syracuseStep 2581241 = 1935931) B1935931
theorem B20669201 : Blo 1611004 20669201 := bstep (se 2 (by rfl) ⟨7750950, by rfl⟩ : syracuseStep 20669201 = 15501901) B15501901
theorem B10322761 : Blo 1611004 10322761 := bstep (se 2 (by rfl) ⟨3871035, by rfl⟩ : syracuseStep 10322761 = 7742071) B7742071
theorem B2417513 : Blo 1611004 2417513 := bstep (se 2 (by rfl) ⟨906567, by rfl⟩ : syracuseStep 2417513 = 1813135) B1813135
theorem B4588463 : Blo 1611004 4588463 := bstep (se 1 (by rfl) ⟨3441347, by rfl⟩ : syracuseStep 4588463 = 6882695) B6882695
theorem B2417591 : Blo 1611004 2417591 := bstep (se 1 (by rfl) ⟨1813193, by rfl⟩ : syracuseStep 2417591 = 3626387) B3626387
theorem B2720695 : Blo 1611004 2720695 := bstep (se 1 (by rfl) ⟨2040521, by rfl⟩ : syracuseStep 2720695 = 4081043) B4081043
theorem B2417627 : Blo 1611004 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B2040871 : Blo 1611004 2040871 := bstep (se 1 (by rfl) ⟨1530653, by rfl⟩ : syracuseStep 2040871 = 3061307) B3061307
theorem B4080719 : Blo 1611004 4080719 := bstep (se 1 (by rfl) ⟨3060539, by rfl⟩ : syracuseStep 4080719 = 6121079) B6121079
theorem B2720891 : Blo 1611004 2720891 := bstep (se 1 (by rfl) ⟨2040668, by rfl⟩ : syracuseStep 2720891 = 4081337) B4081337
theorem B2581703 : Blo 1611004 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B2294983 : Blo 1611004 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B9184535 : Blo 1611004 9184535 := bstep (se 1 (by rfl) ⟨6888401, by rfl⟩ : syracuseStep 9184535 = 13776803) B13776803
theorem B6120791 : Blo 1611004 6120791 := bstep (se 1 (by rfl) ⟨4590593, by rfl⟩ : syracuseStep 6120791 = 9181187) B9181187
theorem B2041195 : Blo 1611004 2041195 := bstep (se 1 (by rfl) ⟨1530896, by rfl⟩ : syracuseStep 2041195 = 3061793) B3061793
theorem B2418095 : Blo 1611004 2418095 := bstep (se 1 (by rfl) ⟨1813571, by rfl⟩ : syracuseStep 2418095 = 3627143) B3627143
theorem B2418185 : Blo 1611004 2418185 := bstep (se 2 (by rfl) ⟨906819, by rfl⟩ : syracuseStep 2418185 = 1813639) B1813639
theorem B2721289 : Blo 1611004 2721289 := bstep (se 2 (by rfl) ⟨1020483, by rfl⟩ : syracuseStep 2721289 = 2040967) B2040967
theorem B12240395 : Blo 1611004 12240395 := bstep (se 1 (by rfl) ⟨9180296, by rfl⟩ : syracuseStep 12240395 = 18360593) B18360593
theorem B2418215 : Blo 1611004 2418215 := bstep (se 1 (by rfl) ⟨1813661, by rfl⟩ : syracuseStep 2418215 = 3627323) B3627323
theorem B5441147 : Blo 1611004 5441147 := bstep (se 1 (by rfl) ⟨4080860, by rfl⟩ : syracuseStep 5441147 = 8161721) B8161721
theorem B2418299 : Blo 1611004 2418299 := bstep (se 1 (by rfl) ⟨1813724, by rfl⟩ : syracuseStep 2418299 = 3627449) B3627449
theorem B5809811 : Blo 1611004 5809811 := bstep (se 1 (by rfl) ⟨4357358, by rfl⟩ : syracuseStep 5809811 = 8714717) B8714717
theorem B2721451 : Blo 1611004 2721451 := bstep (se 1 (by rfl) ⟨2041088, by rfl⟩ : syracuseStep 2721451 = 4082177) B4082177
theorem B4081367 : Blo 1611004 4081367 := bstep (se 1 (by rfl) ⟨3061025, by rfl⟩ : syracuseStep 4081367 = 6122051) B6122051
theorem B2418425 : Blo 1611004 2418425 := bstep (se 2 (by rfl) ⟨906909, by rfl⟩ : syracuseStep 2418425 = 1813819) B1813819
theorem B5441309 : Blo 1611004 5441309 := bstep (se 3 (by rfl) ⟨1020245, by rfl⟩ : syracuseStep 5441309 = 2040491) B2040491
theorem B11028257 : Blo 1611004 11028257 := bstep (se 2 (by rfl) ⟨4135596, by rfl⟩ : syracuseStep 11028257 = 8271193) B8271193
theorem B7849823 : Blo 1611004 7849823 := bstep (se 1 (by rfl) ⟨5887367, by rfl⟩ : syracuseStep 7849823 = 11774735) B11774735
theorem B2418527 : Blo 1611004 2418527 := bstep (se 1 (by rfl) ⟨1813895, by rfl⟩ : syracuseStep 2418527 = 3627791) B3627791
theorem B2418539 : Blo 1611004 2418539 := bstep (se 1 (by rfl) ⟨1813904, by rfl⟩ : syracuseStep 2418539 = 3627809) B3627809
theorem B14698349 : Blo 1611004 14698349 := bstep (se 3 (by rfl) ⟨2755940, by rfl⟩ : syracuseStep 14698349 = 5511881) B5511881
theorem B1722331 : Blo 1611004 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B2721755 : Blo 1611004 2721755 := bstep (se 1 (by rfl) ⟨2041316, by rfl⟩ : syracuseStep 2721755 = 4082633) B4082633
theorem B1812559 : Blo 1611004 1812559 := bstep (se 1 (by rfl) ⟨1359419, by rfl⟩ : syracuseStep 1812559 = 2718839) B2718839
theorem B2418767 : Blo 1611004 2418767 := bstep (se 1 (by rfl) ⟨1814075, by rfl⟩ : syracuseStep 2418767 = 3628151) B3628151
theorem B2582651 : Blo 1611004 2582651 := bstep (se 1 (by rfl) ⟨1936988, by rfl⟩ : syracuseStep 2582651 = 3873977) B3873977
theorem B9177245 : Blo 1611004 9177245 := bstep (se 3 (by rfl) ⟨1720733, by rfl⟩ : syracuseStep 9177245 = 3441467) B3441467
theorem B2418887 : Blo 1611004 2418887 := bstep (se 1 (by rfl) ⟨1814165, by rfl⟩ : syracuseStep 2418887 = 3628331) B3628331
theorem B2451817 : Blo 1611004 2451817 := bstep (se 2 (by rfl) ⟨919431, by rfl⟩ : syracuseStep 2451817 = 1838863) B1838863
theorem B2419049 : Blo 1611004 2419049 := bstep (se 2 (by rfl) ⟨907143, by rfl⟩ : syracuseStep 2419049 = 1814287) B1814287
theorem B2419127 : Blo 1611004 2419127 := bstep (se 1 (by rfl) ⟨1814345, by rfl⟩ : syracuseStep 2419127 = 3628691) B3628691
theorem B1812955 : Blo 1611004 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B5442011 : Blo 1611004 5442011 := bstep (se 1 (by rfl) ⟨4081508, by rfl⟩ : syracuseStep 5442011 = 8163017) B8163017
theorem B2419163 : Blo 1611004 2419163 := bstep (se 1 (by rfl) ⟨1814372, by rfl⟩ : syracuseStep 2419163 = 3628745) B3628745
theorem B26159597 : Blo 1611004 26159597 := bstep (se 3 (by rfl) ⟨4904924, by rfl⟩ : syracuseStep 26159597 = 9809849) B9809849
theorem B6122081 : Blo 1611004 6122081 := bstep (se 2 (by rfl) ⟨2295780, by rfl⟩ : syracuseStep 6122081 = 4591561) B4591561
theorem B46476179 : Blo 1611004 46476179 := bstep (se 1 (by rfl) ⟨34857134, by rfl⟩ : syracuseStep 46476179 = 69714269) B69714269
theorem B13077395 : Blo 1611004 13077395 := bstep (se 1 (by rfl) ⟨9808046, by rfl⟩ : syracuseStep 13077395 = 19616093) B19616093
theorem B1813423 : Blo 1611004 1813423 := bstep (se 1 (by rfl) ⟨1360067, by rfl⟩ : syracuseStep 1813423 = 2720135) B2720135
theorem B94202837 : Blo 1611004 94202837 := bstep (se 7 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 94202837 = 2207879) B2207879
theorem B11619395 : Blo 1611004 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B3443791 : Blo 1611004 3443791 := bstep (se 1 (by rfl) ⟨2582843, by rfl⟩ : syracuseStep 3443791 = 5165687) B5165687
theorem B5442713 : Blo 1611004 5442713 := bstep (se 2 (by rfl) ⟨2041017, by rfl⟩ : syracuseStep 5442713 = 4082035) B4082035
theorem B1838279 : Blo 1611004 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B1813855 : Blo 1611004 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B10489231 : Blo 1611004 10489231 := bstep (se 1 (by rfl) ⟨7866923, by rfl⟩ : syracuseStep 10489231 = 15733847) B15733847
theorem B12242339 : Blo 1611004 12242339 := bstep (se 1 (by rfl) ⟨9181754, by rfl⟩ : syracuseStep 12242339 = 18363509) B18363509
theorem B26136103 : Blo 1611004 26136103 := bstep (se 1 (by rfl) ⟨19602077, by rfl⟩ : syracuseStep 26136103 = 39204155) B39204155
theorem B8162855 : Blo 1611004 8162855 := bstep (se 1 (by rfl) ⟨6122141, by rfl⟩ : syracuseStep 8162855 = 12244283) B12244283
theorem B2903609 : Blo 1611004 2903609 := bstep (se 2 (by rfl) ⟨1088853, by rfl⟩ : syracuseStep 2903609 = 2177707) B2177707
theorem B10333757 : Blo 1611004 10333757 := bstep (se 3 (by rfl) ⟨1937579, by rfl⟩ : syracuseStep 10333757 = 3875159) B3875159
theorem B75476549 : Blo 1611004 75476549 := bstep (se 4 (by rfl) ⟨7075926, by rfl⟩ : syracuseStep 75476549 = 14151853) B14151853
theorem B3059279 : Blo 1611004 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B1814215 : Blo 1611004 1814215 := bstep (se 1 (by rfl) ⟨1360661, by rfl⟩ : syracuseStep 1814215 = 2721323) B2721323
theorem B5164829 : Blo 1611004 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B12234563 : Blo 1611004 12234563 := bstep (se 1 (by rfl) ⟨9175922, by rfl⟩ : syracuseStep 12234563 = 18351845) B18351845
theorem B2903969 : Blo 1611004 2903969 := bstep (se 2 (by rfl) ⟨1088988, by rfl⟩ : syracuseStep 2903969 = 2177977) B2177977
theorem B6123539 : Blo 1611004 6123539 := bstep (se 1 (by rfl) ⟨4592654, by rfl⟩ : syracuseStep 6123539 = 9185309) B9185309
theorem B30978125 : Blo 1611004 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B30969971 : Blo 1611004 30969971 := bstep (se 1 (by rfl) ⟨23227478, by rfl⟩ : syracuseStep 30969971 = 46454957) B46454957
theorem B15487139 : Blo 1611004 15487139 := bstep (se 1 (by rfl) ⟨11615354, by rfl⟩ : syracuseStep 15487139 = 23230709) B23230709
theorem B11030987 : Blo 1611004 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B6123995 : Blo 1611004 6123995 := bstep (se 1 (by rfl) ⟨4592996, by rfl⟩ : syracuseStep 6123995 = 9185993) B9185993
theorem B4592153 : Blo 1611004 4592153 := bstep (se 2 (by rfl) ⟨1722057, by rfl⟩ : syracuseStep 4592153 = 3444115) B3444115
theorem B3060281 : Blo 1611004 3060281 := bstep (se 2 (by rfl) ⟨1147605, by rfl⟩ : syracuseStep 3060281 = 2295211) B2295211
theorem B3625595 : Blo 1611004 3625595 := bstep (se 1 (by rfl) ⟨2719196, by rfl⟩ : syracuseStep 3625595 = 5438393) B5438393
theorem B3625721 : Blo 1611004 3625721 := bstep (se 2 (by rfl) ⟨1359645, by rfl⟩ : syracuseStep 3625721 = 2719291) B2719291
theorem B9180161 : Blo 1611004 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B5231623 : Blo 1611004 5231623 := bstep (se 1 (by rfl) ⟨3923717, by rfl⟩ : syracuseStep 5231623 = 7847435) B7847435
theorem B3625991 : Blo 1611004 3625991 := bstep (se 1 (by rfl) ⟨2719493, by rfl⟩ : syracuseStep 3625991 = 5438987) B5438987
theorem B3626063 : Blo 1611004 3626063 := bstep (se 1 (by rfl) ⟨2719547, by rfl⟩ : syracuseStep 3626063 = 5439095) B5439095
theorem B8270927 : Blo 1611004 8270927 := bstep (se 1 (by rfl) ⟨6203195, by rfl⟩ : syracuseStep 8270927 = 12406391) B12406391
theorem B5813329 : Blo 1611004 5813329 := bstep (se 2 (by rfl) ⟨2179998, by rfl⟩ : syracuseStep 5813329 = 4359997) B4359997
theorem B27538703 : Blo 1611004 27538703 := bstep (se 1 (by rfl) ⟨20654027, by rfl⟩ : syracuseStep 27538703 = 41308055) B41308055
theorem B1611047 : Blo 1611004 1611047 := bstep (se 1 (by rfl) ⟨1208285, by rfl⟩ : syracuseStep 1611047 = 2416571) B2416571
theorem B1611087 : Blo 1611004 1611087 := bstep (se 1 (by rfl) ⟨1208315, by rfl⟩ : syracuseStep 1611087 = 2416631) B2416631
theorem B1611103 : Blo 1611004 1611103 := bstep (se 1 (by rfl) ⟨1208327, by rfl⟩ : syracuseStep 1611103 = 2416655) B2416655
theorem B1611131 : Blo 1611004 1611131 := bstep (se 1 (by rfl) ⟨1208348, by rfl⟩ : syracuseStep 1611131 = 2416697) B2416697
theorem B4904317 : Blo 1611004 4904317 := bstep (se 3 (by rfl) ⟨919559, by rfl⟩ : syracuseStep 4904317 = 1839119) B1839119
theorem B1611183 : Blo 1611004 1611183 := bstep (se 1 (by rfl) ⟨1208387, by rfl⟩ : syracuseStep 1611183 = 2416775) B2416775
theorem B1611207 : Blo 1611004 1611207 := bstep (se 1 (by rfl) ⟨1208405, by rfl⟩ : syracuseStep 1611207 = 2416811) B2416811
theorem B1611227 : Blo 1611004 1611227 := bstep (se 1 (by rfl) ⟨1208420, by rfl⟩ : syracuseStep 1611227 = 2416841) B2416841
theorem B3626459 : Blo 1611004 3626459 := bstep (se 1 (by rfl) ⟨2719844, by rfl⟩ : syracuseStep 3626459 = 5439689) B5439689
theorem B6116903 : Blo 1611004 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B1611303 : Blo 1611004 1611303 := bstep (se 1 (by rfl) ⟨1208477, by rfl⟩ : syracuseStep 1611303 = 2416955) B2416955
theorem B1611343 : Blo 1611004 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B1611359 : Blo 1611004 1611359 := bstep (se 1 (by rfl) ⟨1208519, by rfl⟩ : syracuseStep 1611359 = 2417039) B2417039
theorem B8164961 : Blo 1611004 8164961 := bstep (se 2 (by rfl) ⟨3061860, by rfl⟩ : syracuseStep 8164961 = 6123721) B6123721
theorem B1611387 : Blo 1611004 1611387 := bstep (se 1 (by rfl) ⟨1208540, by rfl⟩ : syracuseStep 1611387 = 2417081) B2417081
theorem B1611439 : Blo 1611004 1611439 := bstep (se 1 (by rfl) ⟨1208579, by rfl⟩ : syracuseStep 1611439 = 2417159) B2417159
theorem B8156861 : Blo 1611004 8156861 := bstep (se 3 (by rfl) ⟨1529411, by rfl⟩ : syracuseStep 8156861 = 3058823) B3058823
theorem B1611463 : Blo 1611004 1611463 := bstep (se 1 (by rfl) ⟨1208597, by rfl⟩ : syracuseStep 1611463 = 2417195) B2417195
theorem B1611483 : Blo 1611004 1611483 := bstep (se 1 (by rfl) ⟨1208612, by rfl⟩ : syracuseStep 1611483 = 2417225) B2417225
theorem B12244769 : Blo 1611004 12244769 := bstep (se 2 (by rfl) ⟨4591788, by rfl⟩ : syracuseStep 12244769 = 9183577) B9183577
theorem B1611559 : Blo 1611004 1611559 := bstep (se 1 (by rfl) ⟨1208669, by rfl⟩ : syracuseStep 1611559 = 2417339) B2417339
theorem B1611599 : Blo 1611004 1611599 := bstep (se 1 (by rfl) ⟨1208699, by rfl⟩ : syracuseStep 1611599 = 2417399) B2417399
theorem B3266399 : Blo 1611004 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B8157023 : Blo 1611004 8157023 := bstep (se 1 (by rfl) ⟨6117767, by rfl⟩ : syracuseStep 8157023 = 12235535) B12235535
theorem B1611615 : Blo 1611004 1611615 := bstep (se 1 (by rfl) ⟨1208711, by rfl⟩ : syracuseStep 1611615 = 2417423) B2417423
theorem B1611643 : Blo 1611004 1611643 := bstep (se 1 (by rfl) ⟨1208732, by rfl⟩ : syracuseStep 1611643 = 2417465) B2417465
theorem B1611695 : Blo 1611004 1611695 := bstep (se 1 (by rfl) ⟨1208771, by rfl⟩ : syracuseStep 1611695 = 2417543) B2417543
theorem B3626927 : Blo 1611004 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B5437367 : Blo 1611004 5437367 := bstep (se 1 (by rfl) ⟨4078025, by rfl⟩ : syracuseStep 5437367 = 8156051) B8156051
theorem B3872699 : Blo 1611004 3872699 := bstep (se 1 (by rfl) ⟨2904524, by rfl⟩ : syracuseStep 3872699 = 5809049) B5809049
theorem B1611719 : Blo 1611004 1611719 := bstep (se 1 (by rfl) ⟨1208789, by rfl⟩ : syracuseStep 1611719 = 2417579) B2417579
theorem B1611739 : Blo 1611004 1611739 := bstep (se 1 (by rfl) ⟨1208804, by rfl⟩ : syracuseStep 1611739 = 2417609) B2417609
theorem B25163783 : Blo 1611004 25163783 := bstep (se 1 (by rfl) ⟨18872837, by rfl⟩ : syracuseStep 25163783 = 37745675) B37745675
theorem B10328093 : Blo 1611004 10328093 := bstep (se 3 (by rfl) ⟨1936517, by rfl⟩ : syracuseStep 10328093 = 3873035) B3873035
theorem B1611815 : Blo 1611004 1611815 := bstep (se 1 (by rfl) ⟨1208861, by rfl⟩ : syracuseStep 1611815 = 2417723) B2417723
theorem B1611855 : Blo 1611004 1611855 := bstep (se 1 (by rfl) ⟨1208891, by rfl⟩ : syracuseStep 1611855 = 2417783) B2417783
theorem B1611871 : Blo 1611004 1611871 := bstep (se 1 (by rfl) ⟨1208903, by rfl⟩ : syracuseStep 1611871 = 2417807) B2417807
theorem B1611899 : Blo 1611004 1611899 := bstep (se 1 (by rfl) ⟨1208924, by rfl⟩ : syracuseStep 1611899 = 2417849) B2417849
theorem B6207641 : Blo 1611004 6207641 := bstep (se 2 (by rfl) ⟨2327865, by rfl⟩ : syracuseStep 6207641 = 4655731) B4655731
theorem B3627179 : Blo 1611004 3627179 := bstep (se 1 (by rfl) ⟨2720384, by rfl⟩ : syracuseStep 3627179 = 5440769) B5440769
theorem B1611951 : Blo 1611004 1611951 := bstep (se 1 (by rfl) ⟨1208963, by rfl⟩ : syracuseStep 1611951 = 2417927) B2417927
theorem B1611975 : Blo 1611004 1611975 := bstep (se 1 (by rfl) ⟨1208981, by rfl⟩ : syracuseStep 1611975 = 2417963) B2417963
theorem B1611995 : Blo 1611004 1611995 := bstep (se 1 (by rfl) ⟨1208996, by rfl⟩ : syracuseStep 1611995 = 2417993) B2417993
theorem B1612071 : Blo 1611004 1612071 := bstep (se 1 (by rfl) ⟨1209053, by rfl⟩ : syracuseStep 1612071 = 2418107) B2418107
theorem B1612111 : Blo 1611004 1612111 := bstep (se 1 (by rfl) ⟨1209083, by rfl⟩ : syracuseStep 1612111 = 2418167) B2418167
theorem B1612127 : Blo 1611004 1612127 := bstep (se 1 (by rfl) ⟨1209095, by rfl⟩ : syracuseStep 1612127 = 2418191) B2418191
theorem B1612155 : Blo 1611004 1612155 := bstep (se 1 (by rfl) ⟨1209116, by rfl⟩ : syracuseStep 1612155 = 2418233) B2418233
theorem B1612207 : Blo 1611004 1612207 := bstep (se 1 (by rfl) ⟨1209155, by rfl⟩ : syracuseStep 1612207 = 2418311) B2418311
theorem B1612231 : Blo 1611004 1612231 := bstep (se 1 (by rfl) ⟨1209173, by rfl⟩ : syracuseStep 1612231 = 2418347) B2418347
theorem B15497675 : Blo 1611004 15497675 := bstep (se 1 (by rfl) ⟨11623256, by rfl⟩ : syracuseStep 15497675 = 23246513) B23246513
theorem B1612251 : Blo 1611004 1612251 := bstep (se 1 (by rfl) ⟨1209188, by rfl⟩ : syracuseStep 1612251 = 2418377) B2418377
theorem B6117875 : Blo 1611004 6117875 := bstep (se 1 (by rfl) ⟨4588406, by rfl⟩ : syracuseStep 6117875 = 9176813) B9176813
theorem B5437961 : Blo 1611004 5437961 := bstep (se 2 (by rfl) ⟨2039235, by rfl⟩ : syracuseStep 5437961 = 4078471) B4078471
theorem B8714785 : Blo 1611004 8714785 := bstep (se 2 (by rfl) ⟨3268044, by rfl⟩ : syracuseStep 8714785 = 6536089) B6536089
theorem B1612327 : Blo 1611004 1612327 := bstep (se 1 (by rfl) ⟨1209245, by rfl⟩ : syracuseStep 1612327 = 2418491) B2418491
theorem B1612367 : Blo 1611004 1612367 := bstep (se 1 (by rfl) ⟨1209275, by rfl⟩ : syracuseStep 1612367 = 2418551) B2418551
theorem B1612383 : Blo 1611004 1612383 := bstep (se 1 (by rfl) ⟨1209287, by rfl⟩ : syracuseStep 1612383 = 2418575) B2418575
theorem B1612411 : Blo 1611004 1612411 := bstep (se 1 (by rfl) ⟨1209308, by rfl⟩ : syracuseStep 1612411 = 2418617) B2418617
theorem B11623085 : Blo 1611004 11623085 := bstep (se 3 (by rfl) ⟨2179328, by rfl⟩ : syracuseStep 11623085 = 4358657) B4358657
theorem B1612463 : Blo 1611004 1612463 := bstep (se 1 (by rfl) ⟨1209347, by rfl⟩ : syracuseStep 1612463 = 2418695) B2418695
theorem B3627719 : Blo 1611004 3627719 := bstep (se 1 (by rfl) ⟨2720789, by rfl⟩ : syracuseStep 3627719 = 5441579) B5441579
theorem B1612487 : Blo 1611004 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B1612507 : Blo 1611004 1612507 := bstep (se 1 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 1612507 = 2418761) B2418761
theorem B1612583 : Blo 1611004 1612583 := bstep (se 1 (by rfl) ⟨1209437, by rfl⟩ : syracuseStep 1612583 = 2418875) B2418875
theorem B1612623 : Blo 1611004 1612623 := bstep (se 1 (by rfl) ⟨1209467, by rfl⟩ : syracuseStep 1612623 = 2418935) B2418935
theorem B1612639 : Blo 1611004 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B156941171 : Blo 1611004 156941171 := bstep (se 1 (by rfl) ⟨117705878, by rfl⟩ : syracuseStep 156941171 = 235411757) B235411757
theorem B1612667 : Blo 1611004 1612667 := bstep (se 1 (by rfl) ⟨1209500, by rfl⟩ : syracuseStep 1612667 = 2419001) B2419001
theorem B11623313 : Blo 1611004 11623313 := bstep (se 2 (by rfl) ⟨4358742, by rfl⟩ : syracuseStep 11623313 = 8717485) B8717485
theorem B11615123 : Blo 1611004 11615123 := bstep (se 1 (by rfl) ⟨8711342, by rfl⟩ : syracuseStep 11615123 = 17422685) B17422685
theorem B1612719 : Blo 1611004 1612719 := bstep (se 1 (by rfl) ⟨1209539, by rfl⟩ : syracuseStep 1612719 = 2419079) B2419079
theorem B1612743 : Blo 1611004 1612743 := bstep (se 1 (by rfl) ⟨1209557, by rfl⟩ : syracuseStep 1612743 = 2419115) B2419115
theorem B1612763 : Blo 1611004 1612763 := bstep (se 1 (by rfl) ⟨1209572, by rfl⟩ : syracuseStep 1612763 = 2419145) B2419145
theorem B1612839 : Blo 1611004 1612839 := bstep (se 1 (by rfl) ⟨1209629, by rfl⟩ : syracuseStep 1612839 = 2419259) B2419259
theorem B22666283 : Blo 1611004 22666283 := bstep (se 1 (by rfl) ⟨16999712, by rfl⟩ : syracuseStep 22666283 = 33999425) B33999425
theorem B7453775 : Blo 1611004 7453775 := bstep (se 1 (by rfl) ⟨5590331, by rfl⟩ : syracuseStep 7453775 = 11180663) B11180663
theorem B1612879 : Blo 1611004 1612879 := bstep (se 1 (by rfl) ⟨1209659, by rfl⟩ : syracuseStep 1612879 = 2419319) B2419319
theorem B1612895 : Blo 1611004 1612895 := bstep (se 1 (by rfl) ⟨1209671, by rfl⟩ : syracuseStep 1612895 = 2419343) B2419343
theorem B1612923 : Blo 1611004 1612923 := bstep (se 1 (by rfl) ⟨1209692, by rfl⟩ : syracuseStep 1612923 = 2419385) B2419385
theorem B1612975 : Blo 1611004 1612975 := bstep (se 1 (by rfl) ⟨1209731, by rfl⟩ : syracuseStep 1612975 = 2419463) B2419463
theorem B1612999 : Blo 1611004 1612999 := bstep (se 1 (by rfl) ⟨1209749, by rfl⟩ : syracuseStep 1612999 = 2419499) B2419499
theorem B2718967 : Blo 1611004 2718967 := bstep (se 1 (by rfl) ⟨2039225, by rfl⟩ : syracuseStep 2718967 = 4078451) B4078451
theorem B5438825 : Blo 1611004 5438825 := bstep (se 2 (by rfl) ⟨2039559, by rfl⟩ : syracuseStep 5438825 = 4079119) B4079119
theorem B18357677 : Blo 1611004 18357677 := bstep (se 3 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 18357677 = 6884129) B6884129
theorem B2719163 : Blo 1611004 2719163 := bstep (se 1 (by rfl) ⟨2039372, by rfl⟩ : syracuseStep 2719163 = 4078745) B4078745
theorem B7749107 : Blo 1611004 7749107 := bstep (se 1 (by rfl) ⟨5811830, by rfl⟩ : syracuseStep 7749107 = 11623661) B11623661
theorem B3145225 : Blo 1611004 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B2719271 : Blo 1611004 2719271 := bstep (se 1 (by rfl) ⟨2039453, by rfl⟩ : syracuseStep 2719271 = 4078907) B4078907
theorem B3628583 : Blo 1611004 3628583 := bstep (se 1 (by rfl) ⟨2721437, by rfl⟩ : syracuseStep 3628583 = 5442875) B5442875
theorem B11173565 : Blo 1611004 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B6053575 : Blo 1611004 6053575 := bstep (se 1 (by rfl) ⟨4540181, by rfl⟩ : syracuseStep 6053575 = 9080363) B9080363
theorem B2719561 : Blo 1611004 2719561 := bstep (se 2 (by rfl) ⟨1019835, by rfl⟩ : syracuseStep 2719561 = 2039671) B2039671
theorem B2719595 : Blo 1611004 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B3628907 : Blo 1611004 3628907 := bstep (se 1 (by rfl) ⟨2721680, by rfl⟩ : syracuseStep 3628907 = 5443361) B5443361
theorem B3628961 : Blo 1611004 3628961 := bstep (se 2 (by rfl) ⟨1360860, by rfl⟩ : syracuseStep 3628961 = 2721721) B2721721
theorem B2416559 : Blo 1611004 2416559 := bstep (se 1 (by rfl) ⟨1812419, by rfl⟩ : syracuseStep 2416559 = 3624839) B3624839
theorem B5439419 : Blo 1611004 5439419 := bstep (se 1 (by rfl) ⟨4079564, by rfl⟩ : syracuseStep 5439419 = 8159129) B8159129
theorem B20652083 : Blo 1611004 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B8159291 : Blo 1611004 8159291 := bstep (se 1 (by rfl) ⟨6119468, by rfl⟩ : syracuseStep 8159291 = 12238937) B12238937
theorem B2416745 : Blo 1611004 2416745 := bstep (se 2 (by rfl) ⟨906279, by rfl⟩ : syracuseStep 2416745 = 1812559) B1812559
theorem B18350387 : Blo 1611004 18350387 := bstep (se 1 (by rfl) ⟨13762790, by rfl⟩ : syracuseStep 18350387 = 27525581) B27525581
theorem B5439851 : Blo 1611004 5439851 := bstep (se 1 (by rfl) ⟨4079888, by rfl⟩ : syracuseStep 5439851 = 8159777) B8159777
theorem B2417063 : Blo 1611004 2417063 := bstep (se 1 (by rfl) ⟨1812797, by rfl⟩ : syracuseStep 2417063 = 3625595) B3625595
theorem B3269089 : Blo 1611004 3269089 := bstep (se 2 (by rfl) ⟨1225908, by rfl⟩ : syracuseStep 3269089 = 2451817) B2451817
theorem B2417147 : Blo 1611004 2417147 := bstep (se 1 (by rfl) ⟨1812860, by rfl⟩ : syracuseStep 2417147 = 3625721) B3625721
theorem B13779467 : Blo 1611004 13779467 := bstep (se 1 (by rfl) ⟨10334600, by rfl⟩ : syracuseStep 13779467 = 20669201) B20669201
theorem B2417273 : Blo 1611004 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B5440121 : Blo 1611004 5440121 := bstep (se 2 (by rfl) ⟨2040045, by rfl⟩ : syracuseStep 5440121 = 4080091) B4080091
theorem B6120107 : Blo 1611004 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B2417327 : Blo 1611004 2417327 := bstep (se 1 (by rfl) ⟨1812995, by rfl⟩ : syracuseStep 2417327 = 3625991) B3625991
theorem B2417375 : Blo 1611004 2417375 := bstep (se 1 (by rfl) ⟨1813031, by rfl⟩ : syracuseStep 2417375 = 3626063) B3626063
theorem B5513951 : Blo 1611004 5513951 := bstep (se 1 (by rfl) ⟨4135463, by rfl⟩ : syracuseStep 5513951 = 8270927) B8270927
theorem B2720479 : Blo 1611004 2720479 := bstep (se 1 (by rfl) ⟨2040359, by rfl⟩ : syracuseStep 2720479 = 4080719) B4080719
theorem B1721135 : Blo 1611004 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B18359135 : Blo 1611004 18359135 := bstep (se 1 (by rfl) ⟨13769351, by rfl⟩ : syracuseStep 18359135 = 27538703) B27538703
theorem B4080527 : Blo 1611004 4080527 := bstep (se 1 (by rfl) ⟨3060395, by rfl⟩ : syracuseStep 4080527 = 6120791) B6120791
theorem B2417639 : Blo 1611004 2417639 := bstep (se 1 (by rfl) ⟨1813229, by rfl⟩ : syracuseStep 2417639 = 3626459) B3626459
theorem B83731445 : Blo 1611004 83731445 := bstep (se 5 (by rfl) ⟨3924911, by rfl⟩ : syracuseStep 83731445 = 7849823) B7849823
theorem B8160263 : Blo 1611004 8160263 := bstep (se 1 (by rfl) ⟨6120197, by rfl⟩ : syracuseStep 8160263 = 12240395) B12240395
theorem B12239909 : Blo 1611004 12239909 := bstep (se 4 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 12239909 = 2294983) B2294983
theorem B13763681 : Blo 1611004 13763681 := bstep (se 2 (by rfl) ⟨5161380, by rfl⟩ : syracuseStep 13763681 = 10322761) B10322761
theorem B2720911 : Blo 1611004 2720911 := bstep (se 1 (by rfl) ⟨2040683, by rfl⟩ : syracuseStep 2720911 = 4081367) B4081367
theorem B2417897 : Blo 1611004 2417897 := bstep (se 2 (by rfl) ⟨906711, by rfl⟩ : syracuseStep 2417897 = 1813423) B1813423
theorem B9798899 : Blo 1611004 9798899 := bstep (se 1 (by rfl) ⟨7349174, by rfl⟩ : syracuseStep 9798899 = 14698349) B14698349
theorem B2417951 : Blo 1611004 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B2581799 : Blo 1611004 2581799 := bstep (se 1 (by rfl) ⟨1936349, by rfl⟩ : syracuseStep 2581799 = 3872699) B3872699
theorem B2721161 : Blo 1611004 2721161 := bstep (se 2 (by rfl) ⟨1020435, by rfl⟩ : syracuseStep 2721161 = 2040871) B2040871
theorem B4138427 : Blo 1611004 4138427 := bstep (se 1 (by rfl) ⟨3103820, by rfl⟩ : syracuseStep 4138427 = 6207641) B6207641
theorem B7751105 : Blo 1611004 7751105 := bstep (se 2 (by rfl) ⟨2906664, by rfl⟩ : syracuseStep 7751105 = 5813329) B5813329
theorem B2418119 : Blo 1611004 2418119 := bstep (se 1 (by rfl) ⟨1813589, by rfl⟩ : syracuseStep 2418119 = 3627179) B3627179
theorem B8160749 : Blo 1611004 8160749 := bstep (se 3 (by rfl) ⟨1530140, by rfl⟩ : syracuseStep 8160749 = 3060281) B3060281
theorem B10331783 : Blo 1611004 10331783 := bstep (se 1 (by rfl) ⟨7748837, by rfl⟩ : syracuseStep 10331783 = 15497675) B15497675
theorem B15492829 : Blo 1611004 15492829 := bstep (se 3 (by rfl) ⟨2904905, by rfl⟩ : syracuseStep 15492829 = 5809811) B5809811
theorem B4081387 : Blo 1611004 4081387 := bstep (se 1 (by rfl) ⟨3061040, by rfl⟩ : syracuseStep 4081387 = 6122081) B6122081
theorem B2418473 : Blo 1611004 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B2418479 : Blo 1611004 2418479 := bstep (se 1 (by rfl) ⟨1813859, by rfl⟩ : syracuseStep 2418479 = 3627719) B3627719
theorem B2721593 : Blo 1611004 2721593 := bstep (se 2 (by rfl) ⟨1020597, by rfl⟩ : syracuseStep 2721593 = 2041195) B2041195
theorem B6539089 : Blo 1611004 6539089 := bstep (se 2 (by rfl) ⟨2452158, by rfl⟩ : syracuseStep 6539089 = 4904317) B4904317
theorem B13985641 : Blo 1611004 13985641 := bstep (se 2 (by rfl) ⟨5244615, by rfl⟩ : syracuseStep 13985641 = 10489231) B10489231
theorem B30984119 : Blo 1611004 30984119 := bstep (se 1 (by rfl) ⟨23238089, by rfl⟩ : syracuseStep 30984119 = 46476179) B46476179
theorem B8718263 : Blo 1611004 8718263 := bstep (se 1 (by rfl) ⟨6538697, by rfl⟩ : syracuseStep 8718263 = 13077395) B13077395
theorem B62801891 : Blo 1611004 62801891 := bstep (se 1 (by rfl) ⟨47101418, by rfl⟩ : syracuseStep 62801891 = 94202837) B94202837
theorem B6883309 : Blo 1611004 6883309 := bstep (se 3 (by rfl) ⟨1290620, by rfl⟩ : syracuseStep 6883309 = 2581241) B2581241
theorem B2418953 : Blo 1611004 2418953 := bstep (se 2 (by rfl) ⟨907107, by rfl⟩ : syracuseStep 2418953 = 1814215) B1814215
theorem B8071433 : Blo 1611004 8071433 := bstep (se 2 (by rfl) ⟨3026787, by rfl⟩ : syracuseStep 8071433 = 6053575) B6053575
theorem B8161559 : Blo 1611004 8161559 := bstep (se 1 (by rfl) ⟨6121169, by rfl⟩ : syracuseStep 8161559 = 12242339) B12242339
theorem B1812775 : Blo 1611004 1812775 := bstep (se 1 (by rfl) ⟨1359581, by rfl⟩ : syracuseStep 1812775 = 2719163) B2719163
theorem B1812847 : Blo 1611004 1812847 := bstep (se 1 (by rfl) ⟨1359635, by rfl⟩ : syracuseStep 1812847 = 2719271) B2719271
theorem B5441903 : Blo 1611004 5441903 := bstep (se 1 (by rfl) ⟨4081427, by rfl⟩ : syracuseStep 5441903 = 8162855) B8162855
theorem B2419055 : Blo 1611004 2419055 := bstep (se 1 (by rfl) ⟨1814291, by rfl⟩ : syracuseStep 2419055 = 3628583) B3628583
theorem B1935739 : Blo 1611004 1935739 := bstep (se 1 (by rfl) ⟨1451804, by rfl⟩ : syracuseStep 1935739 = 2903609) B2903609
theorem B50317699 : Blo 1611004 50317699 := bstep (se 1 (by rfl) ⟨37738274, by rfl⟩ : syracuseStep 50317699 = 75476549) B75476549
theorem B7743917 : Blo 1611004 7743917 := bstep (se 3 (by rfl) ⟨1451984, by rfl⟩ : syracuseStep 7743917 = 2903969) B2903969
theorem B7449043 : Blo 1611004 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B3443219 : Blo 1611004 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B1813063 : Blo 1611004 1813063 := bstep (se 1 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 1813063 = 2719595) B2719595
theorem B2419271 : Blo 1611004 2419271 := bstep (se 1 (by rfl) ⟨1814453, by rfl⟩ : syracuseStep 2419271 = 3628907) B3628907
theorem B2419307 : Blo 1611004 2419307 := bstep (se 1 (by rfl) ⟨1814480, by rfl⟩ : syracuseStep 2419307 = 3628961) B3628961
theorem B2296441 : Blo 1611004 2296441 := bstep (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) B1722331
theorem B4082359 : Blo 1611004 4082359 := bstep (se 1 (by rfl) ⟨3061769, by rfl⟩ : syracuseStep 4082359 = 6123539) B6123539
theorem B20646647 : Blo 1611004 20646647 := bstep (se 1 (by rfl) ⟨15484985, by rfl⟩ : syracuseStep 20646647 = 30969971) B30969971
theorem B10324759 : Blo 1611004 10324759 := bstep (se 1 (by rfl) ⟨7743569, by rfl⟩ : syracuseStep 10324759 = 15487139) B15487139
theorem B4082663 : Blo 1611004 4082663 := bstep (se 1 (by rfl) ⟨3061997, by rfl⟩ : syracuseStep 4082663 = 6123995) B6123995
theorem B4902077 : Blo 1611004 4902077 := bstep (se 3 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 4902077 = 1838279) B1838279
theorem B3058975 : Blo 1611004 3058975 := bstep (se 1 (by rfl) ⟨2294231, by rfl⟩ : syracuseStep 3058975 = 4588463) B4588463
theorem B11619713 : Blo 1611004 11619713 := bstep (se 2 (by rfl) ⟨4357392, by rfl⟩ : syracuseStep 11619713 = 8714785) B8714785
theorem B1813927 : Blo 1611004 1813927 := bstep (se 1 (by rfl) ⟨1360445, by rfl⟩ : syracuseStep 1813927 = 2720891) B2720891
theorem B6123023 : Blo 1611004 6123023 := bstep (se 1 (by rfl) ⟨4592267, by rfl⟩ : syracuseStep 6123023 = 9184535) B9184535
theorem B5443307 : Blo 1611004 5443307 := bstep (se 1 (by rfl) ⟨4082480, by rfl⟩ : syracuseStep 5443307 = 8164961) B8164961
theorem B7352171 : Blo 1611004 7352171 := bstep (se 1 (by rfl) ⟨5514128, by rfl⟩ : syracuseStep 7352171 = 11028257) B11028257
theorem B8163179 : Blo 1611004 8163179 := bstep (se 1 (by rfl) ⟨6122384, by rfl⟩ : syracuseStep 8163179 = 12244769) B12244769
theorem B3624911 : Blo 1611004 3624911 := bstep (se 1 (by rfl) ⟨2718683, by rfl⟩ : syracuseStep 3624911 = 5437367) B5437367
theorem B1814503 : Blo 1611004 1814503 := bstep (se 1 (by rfl) ⟨1360877, by rfl⟩ : syracuseStep 1814503 = 2721755) B2721755
theorem B6975497 : Blo 1611004 6975497 := bstep (se 2 (by rfl) ⟨2615811, by rfl⟩ : syracuseStep 6975497 = 5231623) B5231623
theorem B6885395 : Blo 1611004 6885395 := bstep (se 1 (by rfl) ⟨5164046, by rfl⟩ : syracuseStep 6885395 = 10328093) B10328093
theorem B4591721 : Blo 1611004 4591721 := bstep (se 2 (by rfl) ⟨1721895, by rfl⟩ : syracuseStep 4591721 = 3443791) B3443791
theorem B3625289 : Blo 1611004 3625289 := bstep (se 2 (by rfl) ⟨1359483, by rfl⟩ : syracuseStep 3625289 = 2718967) B2718967
theorem B3625307 : Blo 1611004 3625307 := bstep (se 1 (by rfl) ⟨2718980, by rfl⟩ : syracuseStep 3625307 = 5437961) B5437961
theorem B15110855 : Blo 1611004 15110855 := bstep (se 1 (by rfl) ⟨11333141, by rfl⟩ : syracuseStep 15110855 = 22666283) B22666283
theorem B7746263 : Blo 1611004 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B4969183 : Blo 1611004 4969183 := bstep (se 1 (by rfl) ⟨3726887, by rfl⟩ : syracuseStep 4969183 = 7453775) B7453775
theorem B3625883 : Blo 1611004 3625883 := bstep (se 1 (by rfl) ⟨2719412, by rfl⟩ : syracuseStep 3625883 = 5438825) B5438825
theorem B5166071 : Blo 1611004 5166071 := bstep (se 1 (by rfl) ⟨3874553, by rfl⟩ : syracuseStep 5166071 = 7749107) B7749107
theorem B3626081 : Blo 1611004 3626081 := bstep (se 2 (by rfl) ⟨1359780, by rfl⟩ : syracuseStep 3626081 = 2719561) B2719561
theorem B8156375 : Blo 1611004 8156375 := bstep (se 1 (by rfl) ⟨6117281, by rfl⟩ : syracuseStep 8156375 = 12234563) B12234563
theorem B1611039 : Blo 1611004 1611039 := bstep (se 1 (by rfl) ⟨1208279, by rfl⟩ : syracuseStep 1611039 = 2416559) B2416559
theorem B3626279 : Blo 1611004 3626279 := bstep (se 1 (by rfl) ⟨2719709, by rfl⟩ : syracuseStep 3626279 = 5439419) B5439419
theorem B1611099 : Blo 1611004 1611099 := bstep (se 1 (by rfl) ⟨1208324, by rfl⟩ : syracuseStep 1611099 = 2416649) B2416649
theorem B1611119 : Blo 1611004 1611119 := bstep (se 1 (by rfl) ⟨1208339, by rfl⟩ : syracuseStep 1611119 = 2416679) B2416679
theorem B4593019 : Blo 1611004 4593019 := bstep (se 1 (by rfl) ⟨3444764, by rfl⟩ : syracuseStep 4593019 = 6889529) B6889529
theorem B6886795 : Blo 1611004 6886795 := bstep (se 1 (by rfl) ⟨5165096, by rfl⟩ : syracuseStep 6886795 = 10330193) B10330193
theorem B57365923 : Blo 1611004 57365923 := bstep (se 1 (by rfl) ⟨43024442, by rfl⟩ : syracuseStep 57365923 = 86048885) B86048885
theorem B1611175 : Blo 1611004 1611175 := bstep (se 1 (by rfl) ⟨1208381, by rfl⟩ : syracuseStep 1611175 = 2416763) B2416763
theorem B1611259 : Blo 1611004 1611259 := bstep (se 1 (by rfl) ⟨1208444, by rfl⟩ : syracuseStep 1611259 = 2416889) B2416889
theorem B1611327 : Blo 1611004 1611327 := bstep (se 1 (by rfl) ⟨1208495, by rfl⟩ : syracuseStep 1611327 = 2416991) B2416991
theorem B1611335 : Blo 1611004 1611335 := bstep (se 1 (by rfl) ⟨1208501, by rfl⟩ : syracuseStep 1611335 = 2417003) B2417003
theorem B7353991 : Blo 1611004 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B6887069 : Blo 1611004 6887069 := bstep (se 3 (by rfl) ⟨1291325, by rfl⟩ : syracuseStep 6887069 = 2582651) B2582651
theorem B3626657 : Blo 1611004 3626657 := bstep (se 2 (by rfl) ⟨1359996, by rfl⟩ : syracuseStep 3626657 = 2719993) B2719993
theorem B1611487 : Blo 1611004 1611487 := bstep (se 1 (by rfl) ⟨1208615, by rfl⟩ : syracuseStep 1611487 = 2417231) B2417231
theorem B1611567 : Blo 1611004 1611567 := bstep (se 1 (by rfl) ⟨1208675, by rfl⟩ : syracuseStep 1611567 = 2417351) B2417351
theorem B27547451 : Blo 1611004 27547451 := bstep (se 1 (by rfl) ⟨20660588, by rfl⟩ : syracuseStep 27547451 = 41321177) B41321177
theorem B1611675 : Blo 1611004 1611675 := bstep (se 1 (by rfl) ⟨1208756, by rfl⟩ : syracuseStep 1611675 = 2417513) B2417513
theorem B1611727 : Blo 1611004 1611727 := bstep (se 1 (by rfl) ⟨1208795, by rfl⟩ : syracuseStep 1611727 = 2417591) B2417591
theorem B1611751 : Blo 1611004 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B3627017 : Blo 1611004 3627017 := bstep (se 2 (by rfl) ⟨1360131, by rfl⟩ : syracuseStep 3627017 = 2720263) B2720263
theorem B5167289 : Blo 1611004 5167289 := bstep (se 2 (by rfl) ⟨1937733, by rfl⟩ : syracuseStep 5167289 = 3875467) B3875467
theorem B1612063 : Blo 1611004 1612063 := bstep (se 1 (by rfl) ⟨1209047, by rfl⟩ : syracuseStep 1612063 = 2418095) B2418095
theorem B1612123 : Blo 1611004 1612123 := bstep (se 1 (by rfl) ⟨1209092, by rfl⟩ : syracuseStep 1612123 = 2418185) B2418185
theorem B4077935 : Blo 1611004 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B1612143 : Blo 1611004 1612143 := bstep (se 1 (by rfl) ⟨1209107, by rfl⟩ : syracuseStep 1612143 = 2418215) B2418215
theorem B3627431 : Blo 1611004 3627431 := bstep (se 1 (by rfl) ⟨2720573, by rfl⟩ : syracuseStep 3627431 = 5441147) B5441147
theorem B1612199 : Blo 1611004 1612199 := bstep (se 1 (by rfl) ⟨1209149, by rfl⟩ : syracuseStep 1612199 = 2418299) B2418299
theorem B5437907 : Blo 1611004 5437907 := bstep (se 1 (by rfl) ⟨4078430, by rfl⟩ : syracuseStep 5437907 = 8156861) B8156861
theorem B1612283 : Blo 1611004 1612283 := bstep (se 1 (by rfl) ⟨1209212, by rfl⟩ : syracuseStep 1612283 = 2418425) B2418425
theorem B3627539 : Blo 1611004 3627539 := bstep (se 1 (by rfl) ⟨2720654, by rfl⟩ : syracuseStep 3627539 = 5441309) B5441309
theorem B2177599 : Blo 1611004 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B5438015 : Blo 1611004 5438015 := bstep (se 1 (by rfl) ⟨4078511, by rfl⟩ : syracuseStep 5438015 = 8157023) B8157023
theorem B1612351 : Blo 1611004 1612351 := bstep (se 1 (by rfl) ⟨1209263, by rfl⟩ : syracuseStep 1612351 = 2418527) B2418527
theorem B1612359 : Blo 1611004 1612359 := bstep (se 1 (by rfl) ⟨1209269, by rfl⟩ : syracuseStep 1612359 = 2418539) B2418539
theorem B3627593 : Blo 1611004 3627593 := bstep (se 2 (by rfl) ⟨1360347, by rfl⟩ : syracuseStep 3627593 = 2720695) B2720695
theorem B16775855 : Blo 1611004 16775855 := bstep (se 1 (by rfl) ⟨12581891, by rfl⟩ : syracuseStep 16775855 = 25163783) B25163783
theorem B1612511 : Blo 1611004 1612511 := bstep (se 1 (by rfl) ⟨1209383, by rfl⟩ : syracuseStep 1612511 = 2418767) B2418767
theorem B12245741 : Blo 1611004 12245741 := bstep (se 3 (by rfl) ⟨2296076, by rfl⟩ : syracuseStep 12245741 = 4592153) B4592153
theorem B6118163 : Blo 1611004 6118163 := bstep (se 1 (by rfl) ⟨4588622, by rfl⟩ : syracuseStep 6118163 = 9177245) B9177245
theorem B1612591 : Blo 1611004 1612591 := bstep (se 1 (by rfl) ⟨1209443, by rfl⟩ : syracuseStep 1612591 = 2418887) B2418887
theorem B1612699 : Blo 1611004 1612699 := bstep (se 1 (by rfl) ⟨1209524, by rfl⟩ : syracuseStep 1612699 = 2419049) B2419049
theorem B1612751 : Blo 1611004 1612751 := bstep (se 1 (by rfl) ⟨1209563, by rfl⟩ : syracuseStep 1612751 = 2419127) B2419127
theorem B3628007 : Blo 1611004 3628007 := bstep (se 1 (by rfl) ⟨2721005, by rfl⟩ : syracuseStep 3628007 = 5442011) B5442011
theorem B1612775 : Blo 1611004 1612775 := bstep (se 1 (by rfl) ⟨1209581, by rfl⟩ : syracuseStep 1612775 = 2419163) B2419163
theorem B17439731 : Blo 1611004 17439731 := bstep (se 1 (by rfl) ⟨13079798, by rfl⟩ : syracuseStep 17439731 = 26159597) B26159597
theorem B4078583 : Blo 1611004 4078583 := bstep (se 1 (by rfl) ⟨3058937, by rfl⟩ : syracuseStep 4078583 = 6117875) B6117875
theorem B7748723 : Blo 1611004 7748723 := bstep (se 1 (by rfl) ⟨5811542, by rfl⟩ : syracuseStep 7748723 = 11623085) B11623085
theorem B104627447 : Blo 1611004 104627447 := bstep (se 1 (by rfl) ⟨78470585, by rfl⟩ : syracuseStep 104627447 = 156941171) B156941171
theorem B7748875 : Blo 1611004 7748875 := bstep (se 1 (by rfl) ⟨5811656, by rfl⟩ : syracuseStep 7748875 = 11623313) B11623313
theorem B4193633 : Blo 1611004 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B3628385 : Blo 1611004 3628385 := bstep (se 2 (by rfl) ⟨1360644, by rfl⟩ : syracuseStep 3628385 = 2721289) B2721289
theorem B34848137 : Blo 1611004 34848137 := bstep (se 2 (by rfl) ⟨13068051, by rfl⟩ : syracuseStep 34848137 = 26136103) B26136103
theorem B3628475 : Blo 1611004 3628475 := bstep (se 1 (by rfl) ⟨2721356, by rfl⟩ : syracuseStep 3628475 = 5442713) B5442713
theorem B3628601 : Blo 1611004 3628601 := bstep (se 2 (by rfl) ⟨1360725, by rfl⟩ : syracuseStep 3628601 = 2721451) B2721451
theorem B12238451 : Blo 1611004 12238451 := bstep (se 1 (by rfl) ⟨9178838, by rfl⟩ : syracuseStep 12238451 = 18357677) B18357677
theorem B6889171 : Blo 1611004 6889171 := bstep (se 1 (by rfl) ⟨5166878, by rfl⟩ : syracuseStep 6889171 = 10333757) B10333757
theorem B30973661 : Blo 1611004 30973661 := bstep (se 3 (by rfl) ⟨5807561, by rfl⟩ : syracuseStep 30973661 = 11615123) B11615123
theorem B2039519 : Blo 1611004 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B5439527 : Blo 1611004 5439527 := bstep (se 1 (by rfl) ⟨4079645, by rfl⟩ : syracuseStep 5439527 = 8159291) B8159291
theorem B2416859 : Blo 1611004 2416859 := bstep (se 1 (by rfl) ⟨1812644, by rfl⟩ : syracuseStep 2416859 = 3625289) B3625289
theorem B2416871 : Blo 1611004 2416871 := bstep (se 1 (by rfl) ⟨1812653, by rfl⟩ : syracuseStep 2416871 = 3625307) B3625307
theorem B2417033 : Blo 1611004 2417033 := bstep (se 2 (by rfl) ⟨906387, by rfl⟩ : syracuseStep 2417033 = 1812775) B1812775
theorem B4080071 : Blo 1611004 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B2417129 : Blo 1611004 2417129 := bstep (se 2 (by rfl) ⟨906423, by rfl⟩ : syracuseStep 2417129 = 1812847) B1812847
theorem B2580985 : Blo 1611004 2580985 := bstep (se 2 (by rfl) ⟨967869, by rfl⟩ : syracuseStep 2580985 = 1935739) B1935739
theorem B12239423 : Blo 1611004 12239423 := bstep (se 1 (by rfl) ⟨9179567, by rfl⟩ : syracuseStep 12239423 = 18359135) B18359135
theorem B2720351 : Blo 1611004 2720351 := bstep (se 1 (by rfl) ⟨2040263, by rfl⟩ : syracuseStep 2720351 = 4080527) B4080527
theorem B2417255 : Blo 1611004 2417255 := bstep (se 1 (by rfl) ⟨1812941, by rfl⟩ : syracuseStep 2417255 = 3625883) B3625883
theorem B12247685 : Blo 1611004 12247685 := bstep (se 4 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 12247685 = 2296441) B2296441
theorem B55820963 : Blo 1611004 55820963 := bstep (se 1 (by rfl) ⟨41865722, by rfl⟩ : syracuseStep 55820963 = 83731445) B83731445
theorem B5440175 : Blo 1611004 5440175 := bstep (se 1 (by rfl) ⟨4080131, by rfl⟩ : syracuseStep 5440175 = 8160263) B8160263
theorem B8159939 : Blo 1611004 8159939 := bstep (se 1 (by rfl) ⟨6119954, by rfl⟩ : syracuseStep 8159939 = 12239909) B12239909
theorem B9175787 : Blo 1611004 9175787 := bstep (se 1 (by rfl) ⟨6881840, by rfl⟩ : syracuseStep 9175787 = 13763681) B13763681
theorem B2417387 : Blo 1611004 2417387 := bstep (se 1 (by rfl) ⟨1813040, by rfl⟩ : syracuseStep 2417387 = 3626081) B3626081
theorem B2417417 : Blo 1611004 2417417 := bstep (se 2 (by rfl) ⟨906531, by rfl⟩ : syracuseStep 2417417 = 1813063) B1813063
theorem B2417519 : Blo 1611004 2417519 := bstep (se 1 (by rfl) ⟨1813139, by rfl⟩ : syracuseStep 2417519 = 3626279) B3626279
theorem B5440499 : Blo 1611004 5440499 := bstep (se 1 (by rfl) ⟨4080374, by rfl⟩ : syracuseStep 5440499 = 8160749) B8160749
theorem B2417771 : Blo 1611004 2417771 := bstep (se 1 (by rfl) ⟨1813328, by rfl⟩ : syracuseStep 2417771 = 3626657) B3626657
theorem B2418011 : Blo 1611004 2418011 := bstep (se 1 (by rfl) ⟨1813508, by rfl⟩ : syracuseStep 2418011 = 3627017) B3627017
theorem B5441039 : Blo 1611004 5441039 := bstep (se 1 (by rfl) ⟨4080779, by rfl⟩ : syracuseStep 5441039 = 8161559) B8161559
theorem B2418287 : Blo 1611004 2418287 := bstep (se 1 (by rfl) ⟨1813715, by rfl⟩ : syracuseStep 2418287 = 3627431) B3627431
theorem B5162611 : Blo 1611004 5162611 := bstep (se 1 (by rfl) ⟨3871958, by rfl⟩ : syracuseStep 5162611 = 7743917) B7743917
theorem B2295479 : Blo 1611004 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B2418359 : Blo 1611004 2418359 := bstep (se 1 (by rfl) ⟨1813769, by rfl⟩ : syracuseStep 2418359 = 3627539) B3627539
theorem B10331833 : Blo 1611004 10331833 := bstep (se 2 (by rfl) ⟨3874437, by rfl⟩ : syracuseStep 10331833 = 7748875) B7748875
theorem B2418395 : Blo 1611004 2418395 := bstep (se 1 (by rfl) ⟨1813796, by rfl⟩ : syracuseStep 2418395 = 3627593) B3627593
theorem B11183903 : Blo 1611004 11183903 := bstep (se 1 (by rfl) ⟨8387927, by rfl⟩ : syracuseStep 11183903 = 16775855) B16775855
theorem B13764431 : Blo 1611004 13764431 := bstep (se 1 (by rfl) ⟨10323323, by rfl⟩ : syracuseStep 13764431 = 20646647) B20646647
theorem B2418569 : Blo 1611004 2418569 := bstep (se 2 (by rfl) ⟨906963, by rfl⟩ : syracuseStep 2418569 = 1813927) B1813927
theorem B2418671 : Blo 1611004 2418671 := bstep (se 1 (by rfl) ⟨1814003, by rfl⟩ : syracuseStep 2418671 = 3628007) B3628007
theorem B2721775 : Blo 1611004 2721775 := bstep (se 1 (by rfl) ⟨2041331, by rfl⟩ : syracuseStep 2721775 = 4082663) B4082663
theorem B11626487 : Blo 1611004 11626487 := bstep (se 1 (by rfl) ⟨8719865, by rfl⟩ : syracuseStep 11626487 = 17439731) B17439731
theorem B4589693 : Blo 1611004 4589693 := bstep (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) B1721135
theorem B2795755 : Blo 1611004 2795755 := bstep (se 1 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 2795755 = 4193633) B4193633
theorem B2418923 : Blo 1611004 2418923 := bstep (se 1 (by rfl) ⟨1814192, by rfl⟩ : syracuseStep 2418923 = 3628385) B3628385
theorem B9185561 : Blo 1611004 9185561 := bstep (se 2 (by rfl) ⟨3444585, by rfl⟩ : syracuseStep 9185561 = 6889171) B6889171
theorem B2418983 : Blo 1611004 2418983 := bstep (se 1 (by rfl) ⟨1814237, by rfl⟩ : syracuseStep 2418983 = 3628475) B3628475
theorem B5441849 : Blo 1611004 5441849 := bstep (se 2 (by rfl) ⟨2040693, by rfl⟩ : syracuseStep 5441849 = 4081387) B4081387
theorem B4082015 : Blo 1611004 4082015 := bstep (se 1 (by rfl) ⟨3061511, by rfl⟩ : syracuseStep 4082015 = 6123023) B6123023
theorem B2419067 : Blo 1611004 2419067 := bstep (se 1 (by rfl) ⟨1814300, by rfl⟩ : syracuseStep 2419067 = 3628601) B3628601
theorem B8718785 : Blo 1611004 8718785 := bstep (se 2 (by rfl) ⟨3269544, by rfl⟩ : syracuseStep 8718785 = 6539089) B6539089
theorem B18647521 : Blo 1611004 18647521 := bstep (se 2 (by rfl) ⟨6992820, by rfl⟩ : syracuseStep 18647521 = 13985641) B13985641
theorem B17435141 : Blo 1611004 17435141 := bstep (se 4 (by rfl) ⟨1634544, by rfl⟩ : syracuseStep 17435141 = 3269089) B3269089
theorem B4901447 : Blo 1611004 4901447 := bstep (se 1 (by rfl) ⟨3676085, by rfl⟩ : syracuseStep 4901447 = 7352171) B7352171
theorem B5442119 : Blo 1611004 5442119 := bstep (se 1 (by rfl) ⟨4081589, by rfl⟩ : syracuseStep 5442119 = 8163179) B8163179
theorem B2419337 : Blo 1611004 2419337 := bstep (se 2 (by rfl) ⟨907251, by rfl⟩ : syracuseStep 2419337 = 1814503) B1814503
theorem B9177745 : Blo 1611004 9177745 := bstep (se 2 (by rfl) ⟨3441654, by rfl⟩ : syracuseStep 9177745 = 6883309) B6883309
theorem B4590263 : Blo 1611004 4590263 := bstep (se 1 (by rfl) ⟨3442697, by rfl⟩ : syracuseStep 4590263 = 6885395) B6885395
theorem B12233591 : Blo 1611004 12233591 := bstep (se 1 (by rfl) ⟨9175193, by rfl⟩ : syracuseStep 12233591 = 18350387) B18350387
theorem B9186311 : Blo 1611004 9186311 := bstep (se 1 (by rfl) ⟨6889733, by rfl⟩ : syracuseStep 9186311 = 13779467) B13779467
theorem B5164175 : Blo 1611004 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B9932057 : Blo 1611004 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B3444047 : Blo 1611004 3444047 := bstep (se 1 (by rfl) ⟨2583035, by rfl⟩ : syracuseStep 3444047 = 5166071) B5166071
theorem B2903465 : Blo 1611004 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B6884797 : Blo 1611004 6884797 := bstep (se 3 (by rfl) ⟨1290899, by rfl⟩ : syracuseStep 6884797 = 2581799) B2581799
theorem B5443145 : Blo 1611004 5443145 := bstep (se 2 (by rfl) ⟨2041179, by rfl⟩ : syracuseStep 5443145 = 4082359) B4082359
theorem B1814107 : Blo 1611004 1814107 := bstep (se 1 (by rfl) ⟨1360580, by rfl⟩ : syracuseStep 1814107 = 2721161) B2721161
theorem B13766345 : Blo 1611004 13766345 := bstep (se 2 (by rfl) ⟨5162379, by rfl⟩ : syracuseStep 13766345 = 10324759) B10324759
theorem B4591379 : Blo 1611004 4591379 := bstep (se 1 (by rfl) ⟨3443534, by rfl⟩ : syracuseStep 4591379 = 6887069) B6887069
theorem B1814395 : Blo 1611004 1814395 := bstep (se 1 (by rfl) ⟨1360796, by rfl⟩ : syracuseStep 1814395 = 2721593) B2721593
theorem B20656079 : Blo 1611004 20656079 := bstep (se 1 (by rfl) ⟨15492059, by rfl⟩ : syracuseStep 20656079 = 30984119) B30984119
theorem B5812175 : Blo 1611004 5812175 := bstep (se 1 (by rfl) ⟨4359131, by rfl⟩ : syracuseStep 5812175 = 8718263) B8718263
theorem B3444859 : Blo 1611004 3444859 := bstep (se 1 (by rfl) ⟨2583644, by rfl⟩ : syracuseStep 3444859 = 5167289) B5167289
theorem B3625271 : Blo 1611004 3625271 := bstep (se 1 (by rfl) ⟨2718953, by rfl⟩ : syracuseStep 3625271 = 5437907) B5437907
theorem B3625343 : Blo 1611004 3625343 := bstep (se 1 (by rfl) ⟨2719007, by rfl⟩ : syracuseStep 3625343 = 5438015) B5438015
theorem B8163827 : Blo 1611004 8163827 := bstep (se 1 (by rfl) ⟨6122870, by rfl⟩ : syracuseStep 8163827 = 12245741) B12245741
theorem B6124025 : Blo 1611004 6124025 := bstep (se 2 (by rfl) ⟨2296509, by rfl⟩ : syracuseStep 6124025 = 4593019) B4593019
theorem B5165815 : Blo 1611004 5165815 := bstep (se 1 (by rfl) ⟨3874361, by rfl⟩ : syracuseStep 5165815 = 7748723) B7748723
theorem B69751631 : Blo 1611004 69751631 := bstep (se 1 (by rfl) ⟨52313723, by rfl⟩ : syracuseStep 69751631 = 104627447) B104627447
theorem B7746475 : Blo 1611004 7746475 := bstep (se 1 (by rfl) ⟨5809856, by rfl⟩ : syracuseStep 7746475 = 11619713) B11619713
theorem B20657105 : Blo 1611004 20657105 := bstep (se 2 (by rfl) ⟨7746414, by rfl⟩ : syracuseStep 20657105 = 15492829) B15492829
theorem B20649107 : Blo 1611004 20649107 := bstep (se 1 (by rfl) ⟨15486830, by rfl⟩ : syracuseStep 20649107 = 30973661) B30973661
theorem B18601325 : Blo 1611004 18601325 := bstep (se 3 (by rfl) ⟨3487748, by rfl⟩ : syracuseStep 18601325 = 6975497) B6975497
theorem B13768055 : Blo 1611004 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B1611163 : Blo 1611004 1611163 := bstep (se 1 (by rfl) ⟨1208372, by rfl⟩ : syracuseStep 1611163 = 2416745) B2416745
theorem B3061147 : Blo 1611004 3061147 := bstep (se 1 (by rfl) ⟨2295860, by rfl⟩ : syracuseStep 3061147 = 4591721) B4591721
theorem B3626567 : Blo 1611004 3626567 := bstep (se 1 (by rfl) ⟨2719925, by rfl⟩ : syracuseStep 3626567 = 5439851) B5439851
theorem B1611375 : Blo 1611004 1611375 := bstep (se 1 (by rfl) ⟨1208531, by rfl⟩ : syracuseStep 1611375 = 2417063) B2417063
theorem B1611431 : Blo 1611004 1611431 := bstep (se 1 (by rfl) ⟨1208573, by rfl⟩ : syracuseStep 1611431 = 2417147) B2417147
theorem B1611515 : Blo 1611004 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B3626747 : Blo 1611004 3626747 := bstep (se 1 (by rfl) ⟨2720060, by rfl⟩ : syracuseStep 3626747 = 5440121) B5440121
theorem B1611551 : Blo 1611004 1611551 := bstep (se 1 (by rfl) ⟨1208663, by rfl⟩ : syracuseStep 1611551 = 2417327) B2417327
theorem B10073903 : Blo 1611004 10073903 := bstep (se 1 (by rfl) ⟨7555427, by rfl⟩ : syracuseStep 10073903 = 15110855) B15110855
theorem B1611583 : Blo 1611004 1611583 := bstep (se 1 (by rfl) ⟨1208687, by rfl⟩ : syracuseStep 1611583 = 2417375) B2417375
theorem B13072205 : Blo 1611004 13072205 := bstep (se 3 (by rfl) ⟨2451038, by rfl⟩ : syracuseStep 13072205 = 4902077) B4902077
theorem B67090265 : Blo 1611004 67090265 := bstep (se 2 (by rfl) ⟨25158849, by rfl⟩ : syracuseStep 67090265 = 50317699) B50317699
theorem B26130397 : Blo 1611004 26130397 := bstep (se 3 (by rfl) ⟨4899449, by rfl⟩ : syracuseStep 26130397 = 9798899) B9798899
theorem B1611759 : Blo 1611004 1611759 := bstep (se 1 (by rfl) ⟨1208819, by rfl⟩ : syracuseStep 1611759 = 2417639) B2417639
theorem B5437583 : Blo 1611004 5437583 := bstep (se 1 (by rfl) ⟨4078187, by rfl⟩ : syracuseStep 5437583 = 8156375) B8156375
theorem B1611931 : Blo 1611004 1611931 := bstep (se 1 (by rfl) ⟨1208948, by rfl⟩ : syracuseStep 1611931 = 2417897) B2417897
theorem B1611967 : Blo 1611004 1611967 := bstep (se 1 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 1611967 = 2417951) B2417951
theorem B2758951 : Blo 1611004 2758951 := bstep (se 1 (by rfl) ⟨2069213, by rfl⟩ : syracuseStep 2758951 = 4138427) B4138427
theorem B6625577 : Blo 1611004 6625577 := bstep (se 2 (by rfl) ⟨2484591, by rfl⟩ : syracuseStep 6625577 = 4969183) B4969183
theorem B3627305 : Blo 1611004 3627305 := bstep (se 2 (by rfl) ⟨1360239, by rfl⟩ : syracuseStep 3627305 = 2720479) B2720479
theorem B5167403 : Blo 1611004 5167403 := bstep (se 1 (by rfl) ⟨3875552, by rfl⟩ : syracuseStep 5167403 = 7751105) B7751105
theorem B1612079 : Blo 1611004 1612079 := bstep (se 1 (by rfl) ⟨1209059, by rfl⟩ : syracuseStep 1612079 = 2418119) B2418119
theorem B6887855 : Blo 1611004 6887855 := bstep (se 1 (by rfl) ⟨5165891, by rfl⟩ : syracuseStep 6887855 = 10331783) B10331783
theorem B1612315 : Blo 1611004 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B1612319 : Blo 1611004 1612319 := bstep (se 1 (by rfl) ⟨1209239, by rfl⟩ : syracuseStep 1612319 = 2418479) B2418479
theorem B18364967 : Blo 1611004 18364967 := bstep (se 1 (by rfl) ⟨13773725, by rfl⟩ : syracuseStep 18364967 = 27547451) B27547451
theorem B41867927 : Blo 1611004 41867927 := bstep (se 1 (by rfl) ⟨31400945, by rfl⟩ : syracuseStep 41867927 = 62801891) B62801891
theorem B1612635 : Blo 1611004 1612635 := bstep (se 1 (by rfl) ⟨1209476, by rfl⟩ : syracuseStep 1612635 = 2418953) B2418953
theorem B5380955 : Blo 1611004 5380955 := bstep (se 1 (by rfl) ⟨4035716, by rfl⟩ : syracuseStep 5380955 = 8071433) B8071433
theorem B3627881 : Blo 1611004 3627881 := bstep (se 2 (by rfl) ⟨1360455, by rfl⟩ : syracuseStep 3627881 = 2720911) B2720911
theorem B2718623 : Blo 1611004 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B3627935 : Blo 1611004 3627935 := bstep (se 1 (by rfl) ⟨2720951, by rfl⟩ : syracuseStep 3627935 = 5441903) B5441903
theorem B1612703 : Blo 1611004 1612703 := bstep (se 1 (by rfl) ⟨1209527, by rfl⟩ : syracuseStep 1612703 = 2419055) B2419055
theorem B4078633 : Blo 1611004 4078633 := bstep (se 2 (by rfl) ⟨1529487, by rfl⟩ : syracuseStep 4078633 = 3058975) B3058975
theorem B1612847 : Blo 1611004 1612847 := bstep (se 1 (by rfl) ⟨1209635, by rfl⟩ : syracuseStep 1612847 = 2419271) B2419271
theorem B1612871 : Blo 1611004 1612871 := bstep (se 1 (by rfl) ⟨1209653, by rfl⟩ : syracuseStep 1612871 = 2419307) B2419307
theorem B4078775 : Blo 1611004 4078775 := bstep (se 1 (by rfl) ⟨3059081, by rfl⟩ : syracuseStep 4078775 = 6118163) B6118163
theorem B9182393 : Blo 1611004 9182393 := bstep (se 2 (by rfl) ⟨3443397, by rfl⟩ : syracuseStep 9182393 = 6886795) B6886795
theorem B76487897 : Blo 1611004 76487897 := bstep (se 2 (by rfl) ⟨28682961, by rfl⟩ : syracuseStep 76487897 = 57365923) B57365923
theorem B5438717 : Blo 1611004 5438717 := bstep (se 3 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 5438717 = 2039519) B2039519
theorem B14703869 : Blo 1611004 14703869 := bstep (se 3 (by rfl) ⟨2756975, by rfl⟩ : syracuseStep 14703869 = 5513951) B5513951
theorem B2719055 : Blo 1611004 2719055 := bstep (se 1 (by rfl) ⟨2039291, by rfl⟩ : syracuseStep 2719055 = 4078583) B4078583
theorem B9805321 : Blo 1611004 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B23232091 : Blo 1611004 23232091 := bstep (se 1 (by rfl) ⟨17424068, by rfl⟩ : syracuseStep 23232091 = 34848137) B34848137
theorem B8158967 : Blo 1611004 8158967 := bstep (se 1 (by rfl) ⟨6119225, by rfl⟩ : syracuseStep 8158967 = 12238451) B12238451
theorem B3628871 : Blo 1611004 3628871 := bstep (se 1 (by rfl) ⟨2721653, by rfl⟩ : syracuseStep 3628871 = 5443307) B5443307
theorem B2416607 : Blo 1611004 2416607 := bstep (se 1 (by rfl) ⟨1812455, by rfl⟩ : syracuseStep 2416607 = 3624911) B3624911
theorem B2416847 : Blo 1611004 2416847 := bstep (se 1 (by rfl) ⟨1812635, by rfl⟩ : syracuseStep 2416847 = 3625271) B3625271
theorem B2416895 : Blo 1611004 2416895 := bstep (se 1 (by rfl) ⟨1812671, by rfl⟩ : syracuseStep 2416895 = 3625343) B3625343
theorem B2720047 : Blo 1611004 2720047 := bstep (se 1 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 2720047 = 4080071) B4080071
theorem B3727673 : Blo 1611004 3727673 := bstep (se 2 (by rfl) ⟨1397877, by rfl⟩ : syracuseStep 3727673 = 2795755) B2795755
theorem B8159615 : Blo 1611004 8159615 := bstep (se 1 (by rfl) ⟨6119711, by rfl⟩ : syracuseStep 8159615 = 12239423) B12239423
theorem B5439959 : Blo 1611004 5439959 := bstep (se 1 (by rfl) ⟨4079969, by rfl⟩ : syracuseStep 5439959 = 8159939) B8159939
theorem B13771403 : Blo 1611004 13771403 := bstep (se 1 (by rfl) ⟨10328552, by rfl⟩ : syracuseStep 13771403 = 20657105) B20657105
theorem B3441313 : Blo 1611004 3441313 := bstep (se 2 (by rfl) ⟨1290492, by rfl⟩ : syracuseStep 3441313 = 2580985) B2580985
theorem B2417711 : Blo 1611004 2417711 := bstep (se 1 (by rfl) ⟨1813283, by rfl⟩ : syracuseStep 2417711 = 3626567) B3626567
theorem B7742573 : Blo 1611004 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B2417831 : Blo 1611004 2417831 := bstep (se 1 (by rfl) ⟨1813373, by rfl⟩ : syracuseStep 2417831 = 3626747) B3626747
theorem B7455935 : Blo 1611004 7455935 := bstep (se 1 (by rfl) ⟨5591951, by rfl⟩ : syracuseStep 7455935 = 11183903) B11183903
theorem B9176287 : Blo 1611004 9176287 := bstep (se 1 (by rfl) ⟨6882215, by rfl⟩ : syracuseStep 9176287 = 13764431) B13764431
theorem B7750991 : Blo 1611004 7750991 := bstep (se 1 (by rfl) ⟨5813243, by rfl⟩ : syracuseStep 7750991 = 11626487) B11626487
theorem B2418203 : Blo 1611004 2418203 := bstep (se 1 (by rfl) ⟨1813652, by rfl⟩ : syracuseStep 2418203 = 3627305) B3627305
theorem B14714405 : Blo 1611004 14714405 := bstep (se 4 (by rfl) ⟨1379475, by rfl⟩ : syracuseStep 14714405 = 2758951) B2758951
theorem B2721343 : Blo 1611004 2721343 := bstep (se 1 (by rfl) ⟨2041007, by rfl⟩ : syracuseStep 2721343 = 4082015) B4082015
theorem B27911951 : Blo 1611004 27911951 := bstep (se 1 (by rfl) ⟨20933963, by rfl⟩ : syracuseStep 27911951 = 41867927) B41867927
theorem B6121277 : Blo 1611004 6121277 := bstep (se 3 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 6121277 = 2295479) B2295479
theorem B4081529 : Blo 1611004 4081529 := bstep (se 2 (by rfl) ⟨1530573, by rfl⟩ : syracuseStep 4081529 = 3061147) B3061147
theorem B2418587 : Blo 1611004 2418587 := bstep (se 1 (by rfl) ⟨1813940, by rfl⟩ : syracuseStep 2418587 = 3627881) B3627881
theorem B1812415 : Blo 1611004 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B2418623 : Blo 1611004 2418623 := bstep (se 1 (by rfl) ⟨1813967, by rfl⟩ : syracuseStep 2418623 = 3627935) B3627935
theorem B397813781 : Blo 1611004 397813781 := bstep (se 6 (by rfl) ⟨9323760, by rfl⟩ : syracuseStep 397813781 = 18647521) B18647521
theorem B3442783 : Blo 1611004 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B30976121 : Blo 1611004 30976121 := bstep (se 2 (by rfl) ⟨11616045, by rfl⟩ : syracuseStep 30976121 = 23232091) B23232091
theorem B2418809 : Blo 1611004 2418809 := bstep (se 2 (by rfl) ⟨907053, by rfl⟩ : syracuseStep 2418809 = 1814107) B1814107
theorem B6121595 : Blo 1611004 6121595 := bstep (se 1 (by rfl) ⟨4591196, by rfl⟩ : syracuseStep 6121595 = 9182393) B9182393
theorem B26863741 : Blo 1611004 26863741 := bstep (se 3 (by rfl) ⟨5036951, by rfl⟩ : syracuseStep 26863741 = 10073903) B10073903
theorem B6883481 : Blo 1611004 6883481 := bstep (se 2 (by rfl) ⟨2581305, by rfl⟩ : syracuseStep 6883481 = 5162611) B5162611
theorem B6621371 : Blo 1611004 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B1812703 : Blo 1611004 1812703 := bstep (se 1 (by rfl) ⟨1359527, by rfl⟩ : syracuseStep 1812703 = 2719055) B2719055
theorem B2296031 : Blo 1611004 2296031 := bstep (se 1 (by rfl) ⟨1722023, by rfl⟩ : syracuseStep 2296031 = 3444047) B3444047
theorem B9177563 : Blo 1611004 9177563 := bstep (se 1 (by rfl) ⟨6883172, by rfl⟩ : syracuseStep 9177563 = 13766345) B13766345
theorem B2419193 : Blo 1611004 2419193 := bstep (se 2 (by rfl) ⟨907197, by rfl⟩ : syracuseStep 2419193 = 1814395) B1814395
theorem B2419247 : Blo 1611004 2419247 := bstep (se 1 (by rfl) ⟨1814435, by rfl⟩ : syracuseStep 2419247 = 3628871) B3628871
theorem B5442551 : Blo 1611004 5442551 := bstep (se 1 (by rfl) ⟨4081913, by rfl⟩ : syracuseStep 5442551 = 8163827) B8163827
theorem B4082683 : Blo 1611004 4082683 := bstep (se 1 (by rfl) ⟨3062012, by rfl⟩ : syracuseStep 4082683 = 6124025) B6124025
theorem B1813567 : Blo 1611004 1813567 := bstep (se 1 (by rfl) ⟨1360175, by rfl⟩ : syracuseStep 1813567 = 2720351) B2720351
theorem B46501087 : Blo 1611004 46501087 := bstep (se 1 (by rfl) ⟨34875815, by rfl⟩ : syracuseStep 46501087 = 69751631) B69751631
theorem B13766071 : Blo 1611004 13766071 := bstep (se 1 (by rfl) ⟨10324553, by rfl⟩ : syracuseStep 13766071 = 20649107) B20649107
theorem B9178703 : Blo 1611004 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B3059795 : Blo 1611004 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B3625055 : Blo 1611004 3625055 := bstep (se 1 (by rfl) ⟨2718791, by rfl⟩ : syracuseStep 3625055 = 5437583) B5437583
theorem B6123707 : Blo 1611004 6123707 := bstep (se 1 (by rfl) ⟨4592780, by rfl⟩ : syracuseStep 6123707 = 9185561) B9185561
theorem B3444935 : Blo 1611004 3444935 := bstep (se 1 (by rfl) ⟨2583701, by rfl⟩ : syracuseStep 3444935 = 5167403) B5167403
theorem B4591903 : Blo 1611004 4591903 := bstep (se 1 (by rfl) ⟨3443927, by rfl⟩ : syracuseStep 4591903 = 6887855) B6887855
theorem B5812523 : Blo 1611004 5812523 := bstep (se 1 (by rfl) ⟨4359392, by rfl⟩ : syracuseStep 5812523 = 8718785) B8718785
theorem B12243311 : Blo 1611004 12243311 := bstep (se 1 (by rfl) ⟨9182483, by rfl⟩ : syracuseStep 12243311 = 18364967) B18364967
theorem B3060175 : Blo 1611004 3060175 := bstep (se 1 (by rfl) ⟨2295131, by rfl⟩ : syracuseStep 3060175 = 4590263) B4590263
theorem B8155727 : Blo 1611004 8155727 := bstep (se 1 (by rfl) ⟨6116795, by rfl⟩ : syracuseStep 8155727 = 12233591) B12233591
theorem B9179729 : Blo 1611004 9179729 := bstep (se 2 (by rfl) ⟨3442398, by rfl⟩ : syracuseStep 9179729 = 6884797) B6884797
theorem B6124207 : Blo 1611004 6124207 := bstep (se 1 (by rfl) ⟨4593155, by rfl⟩ : syracuseStep 6124207 = 9186311) B9186311
theorem B50991931 : Blo 1611004 50991931 := bstep (se 1 (by rfl) ⟨38243948, by rfl⟩ : syracuseStep 50991931 = 76487897) B76487897
theorem B3625811 : Blo 1611004 3625811 := bstep (se 1 (by rfl) ⟨2719358, by rfl⟩ : syracuseStep 3625811 = 5438717) B5438717
theorem B9802579 : Blo 1611004 9802579 := bstep (se 1 (by rfl) ⟨7351934, by rfl⟩ : syracuseStep 9802579 = 14703869) B14703869
theorem B13775777 : Blo 1611004 13775777 := bstep (se 2 (by rfl) ⟨5165916, by rfl⟩ : syracuseStep 13775777 = 10331833) B10331833
theorem B3060919 : Blo 1611004 3060919 := bstep (se 1 (by rfl) ⟨2295689, by rfl⟩ : syracuseStep 3060919 = 4591379) B4591379
theorem B1611071 : Blo 1611004 1611071 := bstep (se 1 (by rfl) ⟨1208303, by rfl⟩ : syracuseStep 1611071 = 2416607) B2416607
theorem B3626351 : Blo 1611004 3626351 := bstep (se 1 (by rfl) ⟨2719763, by rfl⟩ : syracuseStep 3626351 = 5439527) B5439527
theorem B1611239 : Blo 1611004 1611239 := bstep (se 1 (by rfl) ⟨1208429, by rfl⟩ : syracuseStep 1611239 = 2416859) B2416859
theorem B1611247 : Blo 1611004 1611247 := bstep (se 1 (by rfl) ⟨1208435, by rfl⟩ : syracuseStep 1611247 = 2416871) B2416871
theorem B4593145 : Blo 1611004 4593145 := bstep (se 2 (by rfl) ⟨1722429, by rfl⟩ : syracuseStep 4593145 = 3444859) B3444859
theorem B1611355 : Blo 1611004 1611355 := bstep (se 1 (by rfl) ⟨1208516, by rfl⟩ : syracuseStep 1611355 = 2417033) B2417033
theorem B1611419 : Blo 1611004 1611419 := bstep (se 1 (by rfl) ⟨1208564, by rfl⟩ : syracuseStep 1611419 = 2417129) B2417129
theorem B1611503 : Blo 1611004 1611503 := bstep (se 1 (by rfl) ⟨1208627, by rfl⟩ : syracuseStep 1611503 = 2417255) B2417255
theorem B8165123 : Blo 1611004 8165123 := bstep (se 1 (by rfl) ⟨6123842, by rfl⟩ : syracuseStep 8165123 = 12247685) B12247685
theorem B37213975 : Blo 1611004 37213975 := bstep (se 1 (by rfl) ⟨27910481, by rfl⟩ : syracuseStep 37213975 = 55820963) B55820963
theorem B3626783 : Blo 1611004 3626783 := bstep (se 1 (by rfl) ⟨2720087, by rfl⟩ : syracuseStep 3626783 = 5440175) B5440175
theorem B6117191 : Blo 1611004 6117191 := bstep (se 1 (by rfl) ⟨4587893, by rfl⟩ : syracuseStep 6117191 = 9175787) B9175787
theorem B1611591 : Blo 1611004 1611591 := bstep (se 1 (by rfl) ⟨1208693, by rfl⟩ : syracuseStep 1611591 = 2417387) B2417387
theorem B1611611 : Blo 1611004 1611611 := bstep (se 1 (by rfl) ⟨1208708, by rfl⟩ : syracuseStep 1611611 = 2417417) B2417417
theorem B1611679 : Blo 1611004 1611679 := bstep (se 1 (by rfl) ⟨1208759, by rfl⟩ : syracuseStep 1611679 = 2417519) B2417519
theorem B3626999 : Blo 1611004 3626999 := bstep (se 1 (by rfl) ⟨2720249, by rfl⟩ : syracuseStep 3626999 = 5440499) B5440499
theorem B1611847 : Blo 1611004 1611847 := bstep (se 1 (by rfl) ⟨1208885, by rfl⟩ : syracuseStep 1611847 = 2417771) B2417771
theorem B17668205 : Blo 1611004 17668205 := bstep (se 3 (by rfl) ⟨3312788, by rfl⟩ : syracuseStep 17668205 = 6625577) B6625577
theorem B12236993 : Blo 1611004 12236993 := bstep (se 2 (by rfl) ⟨4588872, by rfl⟩ : syracuseStep 12236993 = 9177745) B9177745
theorem B1612007 : Blo 1611004 1612007 := bstep (se 1 (by rfl) ⟨1209005, by rfl⟩ : syracuseStep 1612007 = 2418011) B2418011
theorem B12400883 : Blo 1611004 12400883 := bstep (se 1 (by rfl) ⟨9300662, by rfl⟩ : syracuseStep 12400883 = 18601325) B18601325
theorem B6887753 : Blo 1611004 6887753 := bstep (se 2 (by rfl) ⟨2582907, by rfl⟩ : syracuseStep 6887753 = 5165815) B5165815
theorem B3627359 : Blo 1611004 3627359 := bstep (se 1 (by rfl) ⟨2720519, by rfl⟩ : syracuseStep 3627359 = 5441039) B5441039
theorem B1612191 : Blo 1611004 1612191 := bstep (se 1 (by rfl) ⟨1209143, by rfl⟩ : syracuseStep 1612191 = 2418287) B2418287
theorem B1612239 : Blo 1611004 1612239 := bstep (se 1 (by rfl) ⟨1209179, by rfl⟩ : syracuseStep 1612239 = 2418359) B2418359
theorem B1612263 : Blo 1611004 1612263 := bstep (se 1 (by rfl) ⟨1209197, by rfl⟩ : syracuseStep 1612263 = 2418395) B2418395
theorem B8714803 : Blo 1611004 8714803 := bstep (se 1 (by rfl) ⟨6536102, by rfl⟩ : syracuseStep 8714803 = 13072205) B13072205
theorem B10328633 : Blo 1611004 10328633 := bstep (se 2 (by rfl) ⟨3873237, by rfl⟩ : syracuseStep 10328633 = 7746475) B7746475
theorem B44726843 : Blo 1611004 44726843 := bstep (se 1 (by rfl) ⟨33545132, by rfl⟩ : syracuseStep 44726843 = 67090265) B67090265
theorem B1612379 : Blo 1611004 1612379 := bstep (se 1 (by rfl) ⟨1209284, by rfl⟩ : syracuseStep 1612379 = 2418569) B2418569
theorem B1612447 : Blo 1611004 1612447 := bstep (se 1 (by rfl) ⟨1209335, by rfl⟩ : syracuseStep 1612447 = 2418671) B2418671
theorem B5438177 : Blo 1611004 5438177 := bstep (se 2 (by rfl) ⟨2039316, by rfl⟩ : syracuseStep 5438177 = 4078633) B4078633
theorem B1612615 : Blo 1611004 1612615 := bstep (se 1 (by rfl) ⟨1209461, by rfl⟩ : syracuseStep 1612615 = 2418923) B2418923
theorem B1612655 : Blo 1611004 1612655 := bstep (se 1 (by rfl) ⟨1209491, by rfl⟩ : syracuseStep 1612655 = 2418983) B2418983
theorem B3627899 : Blo 1611004 3627899 := bstep (se 1 (by rfl) ⟨2720924, by rfl⟩ : syracuseStep 3627899 = 5441849) B5441849
theorem B1612711 : Blo 1611004 1612711 := bstep (se 1 (by rfl) ⟨1209533, by rfl⟩ : syracuseStep 1612711 = 2419067) B2419067
theorem B11623427 : Blo 1611004 11623427 := bstep (se 1 (by rfl) ⟨8717570, by rfl⟩ : syracuseStep 11623427 = 17435141) B17435141
theorem B3267631 : Blo 1611004 3267631 := bstep (se 1 (by rfl) ⟨2450723, by rfl⟩ : syracuseStep 3267631 = 4901447) B4901447
theorem B3628079 : Blo 1611004 3628079 := bstep (se 1 (by rfl) ⟨2721059, by rfl⟩ : syracuseStep 3628079 = 5442119) B5442119
theorem B1612891 : Blo 1611004 1612891 := bstep (se 1 (by rfl) ⟨1209668, by rfl⟩ : syracuseStep 1612891 = 2419337) B2419337
theorem B3587303 : Blo 1611004 3587303 := bstep (se 1 (by rfl) ⟨2690477, by rfl⟩ : syracuseStep 3587303 = 5380955) B5380955
theorem B13073761 : Blo 1611004 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B2719183 : Blo 1611004 2719183 := bstep (se 1 (by rfl) ⟨2039387, by rfl⟩ : syracuseStep 2719183 = 4078775) B4078775
theorem B3628763 : Blo 1611004 3628763 := bstep (se 1 (by rfl) ⟨2721572, by rfl⟩ : syracuseStep 3628763 = 5443145) B5443145
theorem B5439311 : Blo 1611004 5439311 := bstep (se 1 (by rfl) ⟨4079483, by rfl⟩ : syracuseStep 5439311 = 8158967) B8158967
theorem B15499133 : Blo 1611004 15499133 := bstep (se 3 (by rfl) ⟨2906087, by rfl⟩ : syracuseStep 15499133 = 5812175) B5812175
theorem B34840529 : Blo 1611004 34840529 := bstep (se 2 (by rfl) ⟨13065198, by rfl⟩ : syracuseStep 34840529 = 26130397) B26130397
theorem B13770719 : Blo 1611004 13770719 := bstep (se 1 (by rfl) ⟨10328039, by rfl⟩ : syracuseStep 13770719 = 20656079) B20656079
theorem B3629033 : Blo 1611004 3629033 := bstep (se 2 (by rfl) ⟨1360887, by rfl⟩ : syracuseStep 3629033 = 2721775) B2721775
theorem B2416703 : Blo 1611004 2416703 := bstep (se 1 (by rfl) ⟨1812527, by rfl⟩ : syracuseStep 2416703 = 3625055) B3625055
theorem B3875015 : Blo 1611004 3875015 := bstep (se 1 (by rfl) ⟨2906261, by rfl⟩ : syracuseStep 3875015 = 5812523) B5812523
theorem B8159453 : Blo 1611004 8159453 := bstep (se 3 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 8159453 = 3059795) B3059795
theorem B5439743 : Blo 1611004 5439743 := bstep (se 1 (by rfl) ⟨4079807, by rfl⟩ : syracuseStep 5439743 = 8159615) B8159615
theorem B2416937 : Blo 1611004 2416937 := bstep (se 2 (by rfl) ⟨906351, by rfl⟩ : syracuseStep 2416937 = 1812703) B1812703
theorem B6119819 : Blo 1611004 6119819 := bstep (se 1 (by rfl) ⟨4589864, by rfl⟩ : syracuseStep 6119819 = 9179729) B9179729
theorem B19882493 : Blo 1611004 19882493 := bstep (se 3 (by rfl) ⟨3727967, by rfl⟩ : syracuseStep 19882493 = 7455935) B7455935
theorem B2417207 : Blo 1611004 2417207 := bstep (se 1 (by rfl) ⟨1812905, by rfl⟩ : syracuseStep 2417207 = 3625811) B3625811
theorem B4080233 : Blo 1611004 4080233 := bstep (se 2 (by rfl) ⟨1530087, by rfl⟩ : syracuseStep 4080233 = 3060175) B3060175
theorem B9183851 : Blo 1611004 9183851 := bstep (se 1 (by rfl) ⟨6887888, by rfl⟩ : syracuseStep 9183851 = 13775777) B13775777
theorem B5161715 : Blo 1611004 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B4588417 : Blo 1611004 4588417 := bstep (se 2 (by rfl) ⟨1720656, by rfl⟩ : syracuseStep 4588417 = 3441313) B3441313
theorem B2417567 : Blo 1611004 2417567 := bstep (se 1 (by rfl) ⟨1813175, by rfl⟩ : syracuseStep 2417567 = 3626351) B3626351
theorem B2417855 : Blo 1611004 2417855 := bstep (se 1 (by rfl) ⟨1813391, by rfl⟩ : syracuseStep 2417855 = 3626783) B3626783
theorem B4080851 : Blo 1611004 4080851 := bstep (se 1 (by rfl) ⟨3060638, by rfl⟩ : syracuseStep 4080851 = 6121277) B6121277
theorem B2721019 : Blo 1611004 2721019 := bstep (se 1 (by rfl) ⟨2040764, by rfl⟩ : syracuseStep 2721019 = 4081529) B4081529
theorem B2417999 : Blo 1611004 2417999 := bstep (se 1 (by rfl) ⟨1813499, by rfl⟩ : syracuseStep 2417999 = 3626999) B3626999
theorem B265209187 : Blo 1611004 265209187 := bstep (se 1 (by rfl) ⟨198906890, by rfl⟩ : syracuseStep 265209187 = 397813781) B397813781
theorem B4081063 : Blo 1611004 4081063 := bstep (se 1 (by rfl) ⟨3060797, by rfl⟩ : syracuseStep 4081063 = 6121595) B6121595
theorem B2418089 : Blo 1611004 2418089 := bstep (se 2 (by rfl) ⟨906783, by rfl⟩ : syracuseStep 2418089 = 1813567) B1813567
theorem B4588987 : Blo 1611004 4588987 := bstep (se 1 (by rfl) ⟨3441740, by rfl⟩ : syracuseStep 4588987 = 6883481) B6883481
theorem B8267255 : Blo 1611004 8267255 := bstep (se 1 (by rfl) ⟨6200441, by rfl⟩ : syracuseStep 8267255 = 12400883) B12400883
theorem B2418239 : Blo 1611004 2418239 := bstep (se 1 (by rfl) ⟨1813679, by rfl⟩ : syracuseStep 2418239 = 3627359) B3627359
theorem B4081225 : Blo 1611004 4081225 := bstep (se 2 (by rfl) ⟨1530459, by rfl⟩ : syracuseStep 4081225 = 3060919) B3060919
theorem B2418599 : Blo 1611004 2418599 := bstep (se 1 (by rfl) ⟨1813949, by rfl⟩ : syracuseStep 2418599 = 3627899) B3627899
theorem B2418719 : Blo 1611004 2418719 := bstep (se 1 (by rfl) ⟨1814039, by rfl⟩ : syracuseStep 2418719 = 3628079) B3628079
theorem B2419175 : Blo 1611004 2419175 := bstep (se 1 (by rfl) ⟨1814381, by rfl⟩ : syracuseStep 2419175 = 3628763) B3628763
theorem B10332755 : Blo 1611004 10332755 := bstep (se 1 (by rfl) ⟨7749566, by rfl⟩ : syracuseStep 10332755 = 15499133) B15499133
theorem B23227019 : Blo 1611004 23227019 := bstep (se 1 (by rfl) ⟨17420264, by rfl⟩ : syracuseStep 23227019 = 34840529) B34840529
theorem B2419355 : Blo 1611004 2419355 := bstep (se 1 (by rfl) ⟨1814516, by rfl⟩ : syracuseStep 2419355 = 3629033) B3629033
theorem B4082471 : Blo 1611004 4082471 := bstep (se 1 (by rfl) ⟨3061853, by rfl⟩ : syracuseStep 4082471 = 6123707) B6123707
theorem B4590377 : Blo 1611004 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B35818321 : Blo 1611004 35818321 := bstep (se 2 (by rfl) ⟨13431870, by rfl⟩ : syracuseStep 35818321 = 26863741) B26863741
theorem B2485115 : Blo 1611004 2485115 := bstep (se 1 (by rfl) ⟨1863836, by rfl⟩ : syracuseStep 2485115 = 3727673) B3727673
theorem B8162207 : Blo 1611004 8162207 := bstep (se 1 (by rfl) ⟨6121655, by rfl⟩ : syracuseStep 8162207 = 12243311) B12243311
theorem B6122537 : Blo 1611004 6122537 := bstep (se 2 (by rfl) ⟨2295951, by rfl⟩ : syracuseStep 6122537 = 4591903) B4591903
theorem B9186493 : Blo 1611004 9186493 := bstep (se 3 (by rfl) ⟨1722467, by rfl⟩ : syracuseStep 9186493 = 3444935) B3444935
theorem B6122749 : Blo 1611004 6122749 := bstep (se 3 (by rfl) ⟨1148015, by rfl⟩ : syracuseStep 6122749 = 2296031) B2296031
theorem B11619737 : Blo 1611004 11619737 := bstep (se 2 (by rfl) ⟨4357401, by rfl⟩ : syracuseStep 11619737 = 8714803) B8714803
theorem B9809603 : Blo 1611004 9809603 := bstep (se 1 (by rfl) ⟨7357202, by rfl⟩ : syracuseStep 9809603 = 14714405) B14714405
theorem B67989241 : Blo 1611004 67989241 := bstep (se 2 (by rfl) ⟨25495965, by rfl⟩ : syracuseStep 67989241 = 50991931) B50991931
theorem B13070105 : Blo 1611004 13070105 := bstep (se 2 (by rfl) ⟨4901289, by rfl⟩ : syracuseStep 13070105 = 9802579) B9802579
theorem B5443415 : Blo 1611004 5443415 := bstep (se 1 (by rfl) ⟨4082561, by rfl⟩ : syracuseStep 5443415 = 8165123) B8165123
theorem B18607967 : Blo 1611004 18607967 := bstep (se 1 (by rfl) ⟨13955975, by rfl⟩ : syracuseStep 18607967 = 27911951) B27911951
theorem B5443577 : Blo 1611004 5443577 := bstep (se 2 (by rfl) ⟨2041341, by rfl⟩ : syracuseStep 5443577 = 4082683) B4082683
theorem B4591835 : Blo 1611004 4591835 := bstep (se 1 (by rfl) ⟨3443876, by rfl⟩ : syracuseStep 4591835 = 6887753) B6887753
theorem B12235049 : Blo 1611004 12235049 := bstep (se 2 (by rfl) ⟨4588143, by rfl⟩ : syracuseStep 12235049 = 9176287) B9176287
theorem B62001449 : Blo 1611004 62001449 := bstep (se 2 (by rfl) ⟨23250543, by rfl⟩ : syracuseStep 62001449 = 46501087) B46501087
theorem B6885755 : Blo 1611004 6885755 := bstep (se 1 (by rfl) ⟨5164316, by rfl⟩ : syracuseStep 6885755 = 10328633) B10328633
theorem B3625451 : Blo 1611004 3625451 := bstep (se 1 (by rfl) ⟨2719088, by rfl⟩ : syracuseStep 3625451 = 5438177) B5438177
theorem B18354761 : Blo 1611004 18354761 := bstep (se 2 (by rfl) ⟨6883035, by rfl⟩ : syracuseStep 18354761 = 13766071) B13766071
theorem B3625577 : Blo 1611004 3625577 := bstep (se 2 (by rfl) ⟨1359591, by rfl⟩ : syracuseStep 3625577 = 2719183) B2719183
theorem B6124193 : Blo 1611004 6124193 := bstep (se 2 (by rfl) ⟨2296572, by rfl⟩ : syracuseStep 6124193 = 4593145) B4593145
theorem B3626207 : Blo 1611004 3626207 := bstep (se 1 (by rfl) ⟨2719655, by rfl⟩ : syracuseStep 3626207 = 5439311) B5439311
theorem B9180479 : Blo 1611004 9180479 := bstep (se 1 (by rfl) ⟨6885359, by rfl⟩ : syracuseStep 9180479 = 13770719) B13770719
theorem B1611231 : Blo 1611004 1611231 := bstep (se 1 (by rfl) ⟨1208423, by rfl⟩ : syracuseStep 1611231 = 2416847) B2416847
theorem B1611263 : Blo 1611004 1611263 := bstep (se 1 (by rfl) ⟨1208447, by rfl⟩ : syracuseStep 1611263 = 2416895) B2416895
theorem B3626639 : Blo 1611004 3626639 := bstep (se 1 (by rfl) ⟨2719979, by rfl⟩ : syracuseStep 3626639 = 5439959) B5439959
theorem B5437151 : Blo 1611004 5437151 := bstep (se 1 (by rfl) ⟨4077863, by rfl⟩ : syracuseStep 5437151 = 8155727) B8155727
theorem B3626729 : Blo 1611004 3626729 := bstep (se 2 (by rfl) ⟨1360023, by rfl⟩ : syracuseStep 3626729 = 2720047) B2720047
theorem B9180935 : Blo 1611004 9180935 := bstep (se 1 (by rfl) ⟨6885701, by rfl⟩ : syracuseStep 9180935 = 13771403) B13771403
theorem B1611807 : Blo 1611004 1611807 := bstep (se 1 (by rfl) ⟨1208855, by rfl⟩ : syracuseStep 1611807 = 2417711) B2417711
theorem B1611887 : Blo 1611004 1611887 := bstep (se 1 (by rfl) ⟨1208915, by rfl⟩ : syracuseStep 1611887 = 2417831) B2417831
theorem B5167327 : Blo 1611004 5167327 := bstep (se 1 (by rfl) ⟨3875495, by rfl⟩ : syracuseStep 5167327 = 7750991) B7750991
theorem B8165609 : Blo 1611004 8165609 := bstep (se 2 (by rfl) ⟨3062103, by rfl⟩ : syracuseStep 8165609 = 6124207) B6124207
theorem B1612135 : Blo 1611004 1612135 := bstep (se 1 (by rfl) ⟨1209101, by rfl⟩ : syracuseStep 1612135 = 2418203) B2418203
theorem B4078127 : Blo 1611004 4078127 := bstep (se 1 (by rfl) ⟨3058595, by rfl⟩ : syracuseStep 4078127 = 6117191) B6117191
theorem B1612391 : Blo 1611004 1612391 := bstep (se 1 (by rfl) ⟨1209293, by rfl⟩ : syracuseStep 1612391 = 2418587) B2418587
theorem B1612415 : Blo 1611004 1612415 := bstep (se 1 (by rfl) ⟨1209311, by rfl⟩ : syracuseStep 1612415 = 2418623) B2418623
theorem B4356841 : Blo 1611004 4356841 := bstep (se 2 (by rfl) ⟨1633815, by rfl⟩ : syracuseStep 4356841 = 3267631) B3267631
theorem B11778803 : Blo 1611004 11778803 := bstep (se 1 (by rfl) ⟨8834102, by rfl⟩ : syracuseStep 11778803 = 17668205) B17668205
theorem B20650747 : Blo 1611004 20650747 := bstep (se 1 (by rfl) ⟨15488060, by rfl⟩ : syracuseStep 20650747 = 30976121) B30976121
theorem B1612539 : Blo 1611004 1612539 := bstep (se 1 (by rfl) ⟨1209404, by rfl⟩ : syracuseStep 1612539 = 2418809) B2418809
theorem B198474533 : Blo 1611004 198474533 := bstep (se 4 (by rfl) ⟨18606987, by rfl⟩ : syracuseStep 198474533 = 37213975) B37213975
theorem B4414247 : Blo 1611004 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B8157995 : Blo 1611004 8157995 := bstep (se 1 (by rfl) ⟨6118496, by rfl⟩ : syracuseStep 8157995 = 12236993) B12236993
theorem B6118375 : Blo 1611004 6118375 := bstep (se 1 (by rfl) ⟨4588781, by rfl⟩ : syracuseStep 6118375 = 9177563) B9177563
theorem B1612795 : Blo 1611004 1612795 := bstep (se 1 (by rfl) ⟨1209596, by rfl⟩ : syracuseStep 1612795 = 2419193) B2419193
theorem B1612831 : Blo 1611004 1612831 := bstep (se 1 (by rfl) ⟨1209623, by rfl⟩ : syracuseStep 1612831 = 2419247) B2419247
theorem B29817895 : Blo 1611004 29817895 := bstep (se 1 (by rfl) ⟨22363421, by rfl⟩ : syracuseStep 29817895 = 44726843) B44726843
theorem B17431681 : Blo 1611004 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B3628367 : Blo 1611004 3628367 := bstep (se 1 (by rfl) ⟨2721275, by rfl⟩ : syracuseStep 3628367 = 5442551) B5442551
theorem B7748951 : Blo 1611004 7748951 := bstep (se 1 (by rfl) ⟨5811713, by rfl⟩ : syracuseStep 7748951 = 11623427) B11623427
theorem B3628457 : Blo 1611004 3628457 := bstep (se 2 (by rfl) ⟨1360671, by rfl⟩ : syracuseStep 3628457 = 2721343) B2721343
theorem B2391535 : Blo 1611004 2391535 := bstep (se 1 (by rfl) ⟨1793651, by rfl⟩ : syracuseStep 2391535 = 3587303) B3587303
theorem B6119135 : Blo 1611004 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B2416553 : Blo 1611004 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B5439635 : Blo 1611004 5439635 := bstep (se 1 (by rfl) ⟨4079726, by rfl⟩ : syracuseStep 5439635 = 8159453) B8159453
theorem B4079879 : Blo 1611004 4079879 := bstep (se 1 (by rfl) ⟨3059909, by rfl⟩ : syracuseStep 4079879 = 6119819) B6119819
theorem B6889769 : Blo 1611004 6889769 := bstep (se 2 (by rfl) ⟨2583663, by rfl⟩ : syracuseStep 6889769 = 5167327) B5167327
theorem B2416967 : Blo 1611004 2416967 := bstep (se 1 (by rfl) ⟨1812725, by rfl⟩ : syracuseStep 2416967 = 3625451) B3625451
theorem B13254995 : Blo 1611004 13254995 := bstep (se 1 (by rfl) ⟨9941246, by rfl⟩ : syracuseStep 13254995 = 19882493) B19882493
theorem B2417051 : Blo 1611004 2417051 := bstep (se 1 (by rfl) ⟨1812788, by rfl⟩ : syracuseStep 2417051 = 3625577) B3625577
theorem B2720155 : Blo 1611004 2720155 := bstep (se 1 (by rfl) ⟨2040116, by rfl⟩ : syracuseStep 2720155 = 4080233) B4080233
theorem B3441143 : Blo 1611004 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2720567 : Blo 1611004 2720567 := bstep (se 1 (by rfl) ⟨2040425, by rfl⟩ : syracuseStep 2720567 = 4080851) B4080851
theorem B2417471 : Blo 1611004 2417471 := bstep (se 1 (by rfl) ⟨1813103, by rfl⟩ : syracuseStep 2417471 = 3626207) B3626207
theorem B6120319 : Blo 1611004 6120319 := bstep (se 1 (by rfl) ⟨4590239, by rfl⟩ : syracuseStep 6120319 = 9180479) B9180479
theorem B5809121 : Blo 1611004 5809121 := bstep (se 2 (by rfl) ⟨2178420, by rfl⟩ : syracuseStep 5809121 = 4356841) B4356841
theorem B27534329 : Blo 1611004 27534329 := bstep (se 2 (by rfl) ⟨10325373, by rfl⟩ : syracuseStep 27534329 = 20650747) B20650747
theorem B2417759 : Blo 1611004 2417759 := bstep (se 1 (by rfl) ⟨1813319, by rfl⟩ : syracuseStep 2417759 = 3626639) B3626639
theorem B2417819 : Blo 1611004 2417819 := bstep (se 1 (by rfl) ⟨1813364, by rfl⟩ : syracuseStep 2417819 = 3626729) B3626729
theorem B6120623 : Blo 1611004 6120623 := bstep (se 1 (by rfl) ⟨4590467, by rfl⟩ : syracuseStep 6120623 = 9180935) B9180935
theorem B39757193 : Blo 1611004 39757193 := bstep (se 2 (by rfl) ⟨14908947, by rfl⟩ : syracuseStep 39757193 = 29817895) B29817895
theorem B23242241 : Blo 1611004 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B12248657 : Blo 1611004 12248657 := bstep (se 2 (by rfl) ⟨4593246, by rfl⟩ : syracuseStep 12248657 = 9186493) B9186493
theorem B15484679 : Blo 1611004 15484679 := bstep (se 1 (by rfl) ⟨11613509, by rfl⟩ : syracuseStep 15484679 = 23227019) B23227019
theorem B2942831 : Blo 1611004 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B2721647 : Blo 1611004 2721647 := bstep (se 1 (by rfl) ⟨2041235, by rfl⟩ : syracuseStep 2721647 = 4082471) B4082471
theorem B5441417 : Blo 1611004 5441417 := bstep (se 2 (by rfl) ⟨2040531, by rfl⟩ : syracuseStep 5441417 = 4081063) B4081063
theorem B5441471 : Blo 1611004 5441471 := bstep (se 1 (by rfl) ⟨4081103, by rfl⟩ : syracuseStep 5441471 = 8162207) B8162207
theorem B4081691 : Blo 1611004 4081691 := bstep (se 1 (by rfl) ⟨3061268, by rfl⟩ : syracuseStep 4081691 = 6122537) B6122537
theorem B5441633 : Blo 1611004 5441633 := bstep (se 2 (by rfl) ⟨2040612, by rfl⟩ : syracuseStep 5441633 = 4081225) B4081225
theorem B2418911 : Blo 1611004 2418911 := bstep (se 1 (by rfl) ⟨1814183, by rfl⟩ : syracuseStep 2418911 = 3628367) B3628367
theorem B2418971 : Blo 1611004 2418971 := bstep (se 1 (by rfl) ⟨1814228, by rfl⟩ : syracuseStep 2418971 = 3628457) B3628457
theorem B6539735 : Blo 1611004 6539735 := bstep (se 1 (by rfl) ⟨4904801, by rfl⟩ : syracuseStep 6539735 = 9809603) B9809603
theorem B12405311 : Blo 1611004 12405311 := bstep (se 1 (by rfl) ⟨9303983, by rfl⟩ : syracuseStep 12405311 = 18607967) B18607967
theorem B2583343 : Blo 1611004 2583343 := bstep (se 1 (by rfl) ⟨1937507, by rfl⟩ : syracuseStep 2583343 = 3875015) B3875015
theorem B4590503 : Blo 1611004 4590503 := bstep (se 1 (by rfl) ⟨3442877, by rfl⟩ : syracuseStep 4590503 = 6885755) B6885755
theorem B6122567 : Blo 1611004 6122567 := bstep (se 1 (by rfl) ⟨4591925, by rfl⟩ : syracuseStep 6122567 = 9183851) B9183851
theorem B4082795 : Blo 1611004 4082795 := bstep (se 1 (by rfl) ⟨3062096, by rfl⟩ : syracuseStep 4082795 = 6124193) B6124193
theorem B20663869 : Blo 1611004 20663869 := bstep (se 3 (by rfl) ⟨3874475, by rfl⟩ : syracuseStep 20663869 = 7748951) B7748951
theorem B3624767 : Blo 1611004 3624767 := bstep (se 1 (by rfl) ⟨2718575, by rfl⟩ : syracuseStep 3624767 = 5437151) B5437151
theorem B5443739 : Blo 1611004 5443739 := bstep (se 1 (by rfl) ⟨4082804, by rfl⟩ : syracuseStep 5443739 = 8165609) B8165609
theorem B8163665 : Blo 1611004 8163665 := bstep (se 2 (by rfl) ⟨3061374, by rfl⟩ : syracuseStep 8163665 = 6122749) B6122749
theorem B353612249 : Blo 1611004 353612249 := bstep (se 2 (by rfl) ⟨132604593, by rfl⟩ : syracuseStep 353612249 = 265209187) B265209187
theorem B7852535 : Blo 1611004 7852535 := bstep (se 1 (by rfl) ⟨5889401, by rfl⟩ : syracuseStep 7852535 = 11778803) B11778803
theorem B3060251 : Blo 1611004 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B7746491 : Blo 1611004 7746491 := bstep (se 1 (by rfl) ⟨5809868, by rfl⟩ : syracuseStep 7746491 = 11619737) B11619737
theorem B8713403 : Blo 1611004 8713403 := bstep (se 1 (by rfl) ⟨6535052, by rfl⟩ : syracuseStep 8713403 = 13070105) B13070105
theorem B1611035 : Blo 1611004 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B1611135 : Blo 1611004 1611135 := bstep (se 1 (by rfl) ⟨1208351, by rfl⟩ : syracuseStep 1611135 = 2416703) B2416703
theorem B3061223 : Blo 1611004 3061223 := bstep (se 1 (by rfl) ⟨2295917, by rfl⟩ : syracuseStep 3061223 = 4591835) B4591835
theorem B3626495 : Blo 1611004 3626495 := bstep (se 1 (by rfl) ⟨2719871, by rfl⟩ : syracuseStep 3626495 = 5439743) B5439743
theorem B8156699 : Blo 1611004 8156699 := bstep (se 1 (by rfl) ⟨6117524, by rfl⟩ : syracuseStep 8156699 = 12235049) B12235049
theorem B1611291 : Blo 1611004 1611291 := bstep (se 1 (by rfl) ⟨1208468, by rfl⟩ : syracuseStep 1611291 = 2416937) B2416937
theorem B41334299 : Blo 1611004 41334299 := bstep (se 1 (by rfl) ⟨31000724, by rfl⟩ : syracuseStep 41334299 = 62001449) B62001449
theorem B1611471 : Blo 1611004 1611471 := bstep (se 1 (by rfl) ⟨1208603, by rfl⟩ : syracuseStep 1611471 = 2417207) B2417207
theorem B12236507 : Blo 1611004 12236507 := bstep (se 1 (by rfl) ⟨9177380, by rfl⟩ : syracuseStep 12236507 = 18354761) B18354761
theorem B1611711 : Blo 1611004 1611711 := bstep (se 1 (by rfl) ⟨1208783, by rfl⟩ : syracuseStep 1611711 = 2417567) B2417567
theorem B1611903 : Blo 1611004 1611903 := bstep (se 1 (by rfl) ⟨1208927, by rfl⟩ : syracuseStep 1611903 = 2417855) B2417855
theorem B1611999 : Blo 1611004 1611999 := bstep (se 1 (by rfl) ⟨1208999, by rfl⟩ : syracuseStep 1611999 = 2417999) B2417999
theorem B1612059 : Blo 1611004 1612059 := bstep (se 1 (by rfl) ⟨1209044, by rfl⟩ : syracuseStep 1612059 = 2418089) B2418089
theorem B5511503 : Blo 1611004 5511503 := bstep (se 1 (by rfl) ⟨4133627, by rfl⟩ : syracuseStep 5511503 = 8267255) B8267255
theorem B1612159 : Blo 1611004 1612159 := bstep (se 1 (by rfl) ⟨1209119, by rfl⟩ : syracuseStep 1612159 = 2418239) B2418239
theorem B47757761 : Blo 1611004 47757761 := bstep (se 2 (by rfl) ⟨17909160, by rfl⟩ : syracuseStep 47757761 = 35818321) B35818321
theorem B6117889 : Blo 1611004 6117889 := bstep (se 2 (by rfl) ⟨2294208, by rfl⟩ : syracuseStep 6117889 = 4588417) B4588417
theorem B1612399 : Blo 1611004 1612399 := bstep (se 1 (by rfl) ⟨1209299, by rfl⟩ : syracuseStep 1612399 = 2418599) B2418599
theorem B26507893 : Blo 1611004 26507893 := bstep (se 5 (by rfl) ⟨1242557, by rfl⟩ : syracuseStep 26507893 = 2485115) B2485115
theorem B8157833 : Blo 1611004 8157833 := bstep (se 2 (by rfl) ⟨3059187, by rfl⟩ : syracuseStep 8157833 = 6118375) B6118375
theorem B1612479 : Blo 1611004 1612479 := bstep (se 1 (by rfl) ⟨1209359, by rfl⟩ : syracuseStep 1612479 = 2418719) B2418719
theorem B1612783 : Blo 1611004 1612783 := bstep (se 1 (by rfl) ⟨1209587, by rfl⟩ : syracuseStep 1612783 = 2419175) B2419175
theorem B3628025 : Blo 1611004 3628025 := bstep (se 2 (by rfl) ⟨1360509, by rfl⟩ : syracuseStep 3628025 = 2721019) B2721019
theorem B2718751 : Blo 1611004 2718751 := bstep (se 1 (by rfl) ⟨2039063, by rfl⟩ : syracuseStep 2718751 = 4078127) B4078127
theorem B6888503 : Blo 1611004 6888503 := bstep (se 1 (by rfl) ⟨5166377, by rfl⟩ : syracuseStep 6888503 = 10332755) B10332755
theorem B1612903 : Blo 1611004 1612903 := bstep (se 1 (by rfl) ⟨1209677, by rfl⟩ : syracuseStep 1612903 = 2419355) B2419355
theorem B132316355 : Blo 1611004 132316355 := bstep (se 1 (by rfl) ⟨99237266, by rfl⟩ : syracuseStep 132316355 = 198474533) B198474533
theorem B5438663 : Blo 1611004 5438663 := bstep (se 1 (by rfl) ⟨4078997, by rfl⟩ : syracuseStep 5438663 = 8157995) B8157995
theorem B6118649 : Blo 1611004 6118649 := bstep (se 2 (by rfl) ⟨2294493, by rfl⟩ : syracuseStep 6118649 = 4588987) B4588987
theorem B90652321 : Blo 1611004 90652321 := bstep (se 2 (by rfl) ⟨33994620, by rfl⟩ : syracuseStep 90652321 = 67989241) B67989241
theorem B4079423 : Blo 1611004 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B3628943 : Blo 1611004 3628943 := bstep (se 1 (by rfl) ⟨2721707, by rfl⟩ : syracuseStep 3628943 = 5443415) B5443415
theorem B12754853 : Blo 1611004 12754853 := bstep (se 4 (by rfl) ⟨1195767, by rfl⟩ : syracuseStep 12754853 = 2391535) B2391535
theorem B3629051 : Blo 1611004 3629051 := bstep (se 1 (by rfl) ⟨2721788, by rfl⟩ : syracuseStep 3629051 = 5443577) B5443577
theorem B3629159 : Blo 1611004 3629159 := bstep (se 1 (by rfl) ⟨2721869, by rfl⟩ : syracuseStep 3629159 = 5443739) B5443739
theorem B2719919 : Blo 1611004 2719919 := bstep (se 1 (by rfl) ⟨2039939, by rfl⟩ : syracuseStep 2719919 = 4079879) B4079879
theorem B235741499 : Blo 1611004 235741499 := bstep (se 1 (by rfl) ⟨176806124, by rfl⟩ : syracuseStep 235741499 = 353612249) B353612249
theorem B2294095 : Blo 1611004 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B5235023 : Blo 1611004 5235023 := bstep (se 1 (by rfl) ⟨3926267, by rfl⟩ : syracuseStep 5235023 = 7852535) B7852535
theorem B2040167 : Blo 1611004 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B4080415 : Blo 1611004 4080415 := bstep (se 1 (by rfl) ⟨3060311, by rfl⟩ : syracuseStep 4080415 = 6120623) B6120623
theorem B5808935 : Blo 1611004 5808935 := bstep (se 1 (by rfl) ⟨4356701, by rfl⟩ : syracuseStep 5808935 = 8713403) B8713403
theorem B2040815 : Blo 1611004 2040815 := bstep (se 1 (by rfl) ⟨1530611, by rfl⟩ : syracuseStep 2040815 = 3061223) B3061223
theorem B2417663 : Blo 1611004 2417663 := bstep (se 1 (by rfl) ⟨1813247, by rfl⟩ : syracuseStep 2417663 = 3626495) B3626495
theorem B8160425 : Blo 1611004 8160425 := bstep (se 2 (by rfl) ⟨3060159, by rfl⟩ : syracuseStep 8160425 = 6120319) B6120319
theorem B10323119 : Blo 1611004 10323119 := bstep (se 1 (by rfl) ⟨7742339, by rfl⟩ : syracuseStep 10323119 = 15484679) B15484679
theorem B2721127 : Blo 1611004 2721127 := bstep (se 1 (by rfl) ⟨2040845, by rfl⟩ : syracuseStep 2721127 = 4081691) B4081691
theorem B2418683 : Blo 1611004 2418683 := bstep (se 1 (by rfl) ⟨1814012, by rfl⟩ : syracuseStep 2418683 = 3628025) B3628025
theorem B4081711 : Blo 1611004 4081711 := bstep (se 1 (by rfl) ⟨3061283, by rfl⟩ : syracuseStep 4081711 = 6122567) B6122567
theorem B2721863 : Blo 1611004 2721863 := bstep (se 1 (by rfl) ⟨2041397, by rfl⟩ : syracuseStep 2721863 = 4082795) B4082795
theorem B27551825 : Blo 1611004 27551825 := bstep (se 2 (by rfl) ⟨10331934, by rfl⟩ : syracuseStep 27551825 = 20663869) B20663869
theorem B2419295 : Blo 1611004 2419295 := bstep (se 1 (by rfl) ⟨1814471, by rfl⟩ : syracuseStep 2419295 = 3628943) B3628943
theorem B2419367 : Blo 1611004 2419367 := bstep (se 1 (by rfl) ⟨1814525, by rfl⟩ : syracuseStep 2419367 = 3629051) B3629051
theorem B18369341 : Blo 1611004 18369341 := bstep (se 3 (by rfl) ⟨3444251, by rfl⟩ : syracuseStep 18369341 = 6888503) B6888503
theorem B5442443 : Blo 1611004 5442443 := bstep (se 1 (by rfl) ⟨4081832, by rfl⟩ : syracuseStep 5442443 = 8163665) B8163665
theorem B1813711 : Blo 1611004 1813711 := bstep (se 1 (by rfl) ⟨1360283, by rfl⟩ : syracuseStep 1813711 = 2720567) B2720567
theorem B5164327 : Blo 1611004 5164327 := bstep (se 1 (by rfl) ⟨3873245, by rfl⟩ : syracuseStep 5164327 = 7746491) B7746491
theorem B35343857 : Blo 1611004 35343857 := bstep (se 2 (by rfl) ⟨13253946, by rfl⟩ : syracuseStep 35343857 = 26507893) B26507893
theorem B26504795 : Blo 1611004 26504795 := bstep (se 1 (by rfl) ⟨19878596, by rfl⟩ : syracuseStep 26504795 = 39757193) B39757193
theorem B15494827 : Blo 1611004 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B3444457 : Blo 1611004 3444457 := bstep (se 2 (by rfl) ⟨1291671, by rfl⟩ : syracuseStep 3444457 = 2583343) B2583343
theorem B1961887 : Blo 1611004 1961887 := bstep (se 1 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 1961887 = 2942831) B2942831
theorem B1814431 : Blo 1611004 1814431 := bstep (se 1 (by rfl) ⟨1360823, by rfl⟩ : syracuseStep 1814431 = 2721647) B2721647
theorem B3625001 : Blo 1611004 3625001 := bstep (se 2 (by rfl) ⟨1359375, by rfl⟩ : syracuseStep 3625001 = 2718751) B2718751
theorem B3674335 : Blo 1611004 3674335 := bstep (se 1 (by rfl) ⟨2755751, by rfl⟩ : syracuseStep 3674335 = 5511503) B5511503
theorem B31838507 : Blo 1611004 31838507 := bstep (se 1 (by rfl) ⟨23878880, by rfl⟩ : syracuseStep 31838507 = 47757761) B47757761
theorem B8270207 : Blo 1611004 8270207 := bstep (se 1 (by rfl) ⟨6202655, by rfl⟩ : syracuseStep 8270207 = 12405311) B12405311
theorem B3060335 : Blo 1611004 3060335 := bstep (se 1 (by rfl) ⟨2295251, by rfl⟩ : syracuseStep 3060335 = 4590503) B4590503
theorem B3625775 : Blo 1611004 3625775 := bstep (se 1 (by rfl) ⟨2719331, by rfl⟩ : syracuseStep 3625775 = 5438663) B5438663
theorem B120869761 : Blo 1611004 120869761 := bstep (se 2 (by rfl) ⟨45326160, by rfl⟩ : syracuseStep 120869761 = 90652321) B90652321
theorem B3626423 : Blo 1611004 3626423 := bstep (se 1 (by rfl) ⟨2719817, by rfl⟩ : syracuseStep 3626423 = 5439635) B5439635
theorem B4593179 : Blo 1611004 4593179 := bstep (se 1 (by rfl) ⟨3444884, by rfl⟩ : syracuseStep 4593179 = 6889769) B6889769
theorem B1611311 : Blo 1611004 1611311 := bstep (se 1 (by rfl) ⟨1208483, by rfl⟩ : syracuseStep 1611311 = 2416967) B2416967
theorem B8836663 : Blo 1611004 8836663 := bstep (se 1 (by rfl) ⟨6627497, by rfl⟩ : syracuseStep 8836663 = 13254995) B13254995
theorem B1611367 : Blo 1611004 1611367 := bstep (se 1 (by rfl) ⟨1208525, by rfl⟩ : syracuseStep 1611367 = 2417051) B2417051
theorem B3626873 : Blo 1611004 3626873 := bstep (se 2 (by rfl) ⟨1360077, by rfl⟩ : syracuseStep 3626873 = 2720155) B2720155
theorem B1611647 : Blo 1611004 1611647 := bstep (se 1 (by rfl) ⟨1208735, by rfl⟩ : syracuseStep 1611647 = 2417471) B2417471
theorem B3872747 : Blo 1611004 3872747 := bstep (se 1 (by rfl) ⟨2904560, by rfl⟩ : syracuseStep 3872747 = 5809121) B5809121
theorem B18356219 : Blo 1611004 18356219 := bstep (se 1 (by rfl) ⟨13767164, by rfl⟩ : syracuseStep 18356219 = 27534329) B27534329
theorem B8157185 : Blo 1611004 8157185 := bstep (se 2 (by rfl) ⟨3058944, by rfl⟩ : syracuseStep 8157185 = 6117889) B6117889
theorem B1611839 : Blo 1611004 1611839 := bstep (se 1 (by rfl) ⟨1208879, by rfl⟩ : syracuseStep 1611839 = 2417759) B2417759
theorem B1611879 : Blo 1611004 1611879 := bstep (se 1 (by rfl) ⟨1208909, by rfl⟩ : syracuseStep 1611879 = 2417819) B2417819
theorem B5437799 : Blo 1611004 5437799 := bstep (se 1 (by rfl) ⟨4078349, by rfl⟩ : syracuseStep 5437799 = 8156699) B8156699
theorem B27556199 : Blo 1611004 27556199 := bstep (se 1 (by rfl) ⟨20667149, by rfl⟩ : syracuseStep 27556199 = 41334299) B41334299
theorem B8165771 : Blo 1611004 8165771 := bstep (se 1 (by rfl) ⟨6124328, by rfl⟩ : syracuseStep 8165771 = 12248657) B12248657
theorem B8157671 : Blo 1611004 8157671 := bstep (se 1 (by rfl) ⟨6118253, by rfl⟩ : syracuseStep 8157671 = 12236507) B12236507
theorem B17439293 : Blo 1611004 17439293 := bstep (se 3 (by rfl) ⟨3269867, by rfl⟩ : syracuseStep 17439293 = 6539735) B6539735
theorem B3627611 : Blo 1611004 3627611 := bstep (se 1 (by rfl) ⟨2720708, by rfl⟩ : syracuseStep 3627611 = 5441417) B5441417
theorem B3627647 : Blo 1611004 3627647 := bstep (se 1 (by rfl) ⟨2720735, by rfl⟩ : syracuseStep 3627647 = 5441471) B5441471
theorem B3627755 : Blo 1611004 3627755 := bstep (se 1 (by rfl) ⟨2720816, by rfl⟩ : syracuseStep 3627755 = 5441633) B5441633
theorem B1612607 : Blo 1611004 1612607 := bstep (se 1 (by rfl) ⟨1209455, by rfl⟩ : syracuseStep 1612607 = 2418911) B2418911
theorem B1612647 : Blo 1611004 1612647 := bstep (se 1 (by rfl) ⟨1209485, by rfl⟩ : syracuseStep 1612647 = 2418971) B2418971
theorem B5438555 : Blo 1611004 5438555 := bstep (se 1 (by rfl) ⟨4078916, by rfl⟩ : syracuseStep 5438555 = 8157833) B8157833
theorem B88210903 : Blo 1611004 88210903 := bstep (se 1 (by rfl) ⟨66158177, by rfl⟩ : syracuseStep 88210903 = 132316355) B132316355
theorem B4079099 : Blo 1611004 4079099 := bstep (se 1 (by rfl) ⟨3059324, by rfl⟩ : syracuseStep 4079099 = 6118649) B6118649
theorem B2416511 : Blo 1611004 2416511 := bstep (se 1 (by rfl) ⟨1812383, by rfl⟩ : syracuseStep 2416511 = 3624767) B3624767
theorem B2719615 : Blo 1611004 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B8503235 : Blo 1611004 8503235 := bstep (se 1 (by rfl) ⟨6377426, by rfl⟩ : syracuseStep 8503235 = 12754853) B12754853
theorem B2416667 : Blo 1611004 2416667 := bstep (se 1 (by rfl) ⟨1812500, by rfl⟩ : syracuseStep 2416667 = 3625001) B3625001
theorem B21225671 : Blo 1611004 21225671 := bstep (se 1 (by rfl) ⟨15919253, by rfl⟩ : syracuseStep 21225671 = 31838507) B31838507
theorem B3490015 : Blo 1611004 3490015 := bstep (se 1 (by rfl) ⟨2617511, by rfl⟩ : syracuseStep 3490015 = 5235023) B5235023
theorem B5513471 : Blo 1611004 5513471 := bstep (se 1 (by rfl) ⟨4135103, by rfl⟩ : syracuseStep 5513471 = 8270207) B8270207
theorem B4899113 : Blo 1611004 4899113 := bstep (se 2 (by rfl) ⟨1837167, by rfl⟩ : syracuseStep 4899113 = 3674335) B3674335
theorem B2040223 : Blo 1611004 2040223 := bstep (se 1 (by rfl) ⟨1530167, by rfl⟩ : syracuseStep 2040223 = 3060335) B3060335
theorem B2417183 : Blo 1611004 2417183 := bstep (se 1 (by rfl) ⟨1812887, by rfl⟩ : syracuseStep 2417183 = 3625775) B3625775
theorem B5440283 : Blo 1611004 5440283 := bstep (se 1 (by rfl) ⟨4080212, by rfl⟩ : syracuseStep 5440283 = 8160425) B8160425
theorem B6882079 : Blo 1611004 6882079 := bstep (se 1 (by rfl) ⟨5161559, by rfl⟩ : syracuseStep 6882079 = 10323119) B10323119
theorem B5440445 : Blo 1611004 5440445 := bstep (se 3 (by rfl) ⟨1020083, by rfl⟩ : syracuseStep 5440445 = 2040167) B2040167
theorem B2417615 : Blo 1611004 2417615 := bstep (se 1 (by rfl) ⟨1813211, by rfl⟩ : syracuseStep 2417615 = 3626423) B3626423
theorem B5440553 : Blo 1611004 5440553 := bstep (se 2 (by rfl) ⟨2040207, by rfl⟩ : syracuseStep 5440553 = 4080415) B4080415
theorem B2417915 : Blo 1611004 2417915 := bstep (se 1 (by rfl) ⟨1813436, by rfl⟩ : syracuseStep 2417915 = 3626873) B3626873
theorem B2581831 : Blo 1611004 2581831 := bstep (se 1 (by rfl) ⟨1936373, by rfl⟩ : syracuseStep 2581831 = 3872747) B3872747
theorem B18367883 : Blo 1611004 18367883 := bstep (se 1 (by rfl) ⟨13775912, by rfl⟩ : syracuseStep 18367883 = 27551825) B27551825
theorem B27543077 : Blo 1611004 27543077 := bstep (se 4 (by rfl) ⟨2582163, by rfl⟩ : syracuseStep 27543077 = 5164327) B5164327
theorem B2418281 : Blo 1611004 2418281 := bstep (se 2 (by rfl) ⟨906855, by rfl⟩ : syracuseStep 2418281 = 1813711) B1813711
theorem B11626195 : Blo 1611004 11626195 := bstep (se 1 (by rfl) ⟨8719646, by rfl⟩ : syracuseStep 11626195 = 17439293) B17439293
theorem B2418407 : Blo 1611004 2418407 := bstep (se 1 (by rfl) ⟨1813805, by rfl⟩ : syracuseStep 2418407 = 3627611) B3627611
theorem B2418431 : Blo 1611004 2418431 := bstep (se 1 (by rfl) ⟨1813823, by rfl⟩ : syracuseStep 2418431 = 3627647) B3627647
theorem B2418503 : Blo 1611004 2418503 := bstep (se 1 (by rfl) ⟨1813877, by rfl⟩ : syracuseStep 2418503 = 3627755) B3627755
theorem B117614537 : Blo 1611004 117614537 := bstep (se 2 (by rfl) ⟨44105451, by rfl⟩ : syracuseStep 117614537 = 88210903) B88210903
theorem B11782217 : Blo 1611004 11782217 := bstep (se 2 (by rfl) ⟨4418331, by rfl⟩ : syracuseStep 11782217 = 8836663) B8836663
theorem B23562571 : Blo 1611004 23562571 := bstep (se 1 (by rfl) ⟨17671928, by rfl⟩ : syracuseStep 23562571 = 35343857) B35343857
theorem B2615849 : Blo 1611004 2615849 := bstep (se 2 (by rfl) ⟨980943, by rfl⟩ : syracuseStep 2615849 = 1961887) B1961887
theorem B2419241 : Blo 1611004 2419241 := bstep (se 2 (by rfl) ⟨907215, by rfl⟩ : syracuseStep 2419241 = 1814431) B1814431
theorem B5442173 : Blo 1611004 5442173 := bstep (se 3 (by rfl) ⟨1020407, by rfl⟩ : syracuseStep 5442173 = 2040815) B2040815
theorem B5442281 : Blo 1611004 5442281 := bstep (se 2 (by rfl) ⟨2040855, by rfl⟩ : syracuseStep 5442281 = 4081711) B4081711
theorem B2419439 : Blo 1611004 2419439 := bstep (se 1 (by rfl) ⟨1814579, by rfl⟩ : syracuseStep 2419439 = 3629159) B3629159
theorem B1813279 : Blo 1611004 1813279 := bstep (se 1 (by rfl) ⟨1359959, by rfl⟩ : syracuseStep 1813279 = 2719919) B2719919
theorem B3058793 : Blo 1611004 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B1814575 : Blo 1611004 1814575 := bstep (se 1 (by rfl) ⟨1360931, by rfl⟩ : syracuseStep 1814575 = 2721863) B2721863
theorem B3625199 : Blo 1611004 3625199 := bstep (se 1 (by rfl) ⟨2718899, by rfl⟩ : syracuseStep 3625199 = 5437799) B5437799
theorem B18370799 : Blo 1611004 18370799 := bstep (se 1 (by rfl) ⟨13778099, by rfl⟩ : syracuseStep 18370799 = 27556199) B27556199
theorem B5443847 : Blo 1611004 5443847 := bstep (se 1 (by rfl) ⟨4082885, by rfl⟩ : syracuseStep 5443847 = 8165771) B8165771
theorem B3625703 : Blo 1611004 3625703 := bstep (se 1 (by rfl) ⟨2719277, by rfl⟩ : syracuseStep 3625703 = 5438555) B5438555
theorem B4592609 : Blo 1611004 4592609 := bstep (se 2 (by rfl) ⟨1722228, by rfl⟩ : syracuseStep 4592609 = 3444457) B3444457
theorem B3626153 : Blo 1611004 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B1611007 : Blo 1611004 1611007 := bstep (se 1 (by rfl) ⟨1208255, by rfl⟩ : syracuseStep 1611007 = 2416511) B2416511
theorem B157160999 : Blo 1611004 157160999 := bstep (se 1 (by rfl) ⟨117870749, by rfl⟩ : syracuseStep 157160999 = 235741499) B235741499
theorem B3872623 : Blo 1611004 3872623 := bstep (se 1 (by rfl) ⟨2904467, by rfl⟩ : syracuseStep 3872623 = 5808935) B5808935
theorem B1611775 : Blo 1611004 1611775 := bstep (se 1 (by rfl) ⟨1208831, by rfl⟩ : syracuseStep 1611775 = 2417663) B2417663
theorem B3062119 : Blo 1611004 3062119 := bstep (se 1 (by rfl) ⟨2296589, by rfl⟩ : syracuseStep 3062119 = 4593179) B4593179
theorem B161159681 : Blo 1611004 161159681 := bstep (se 2 (by rfl) ⟨60434880, by rfl⟩ : syracuseStep 161159681 = 120869761) B120869761
theorem B12237479 : Blo 1611004 12237479 := bstep (se 1 (by rfl) ⟨9178109, by rfl⟩ : syracuseStep 12237479 = 18356219) B18356219
theorem B1612455 : Blo 1611004 1612455 := bstep (se 1 (by rfl) ⟨1209341, by rfl⟩ : syracuseStep 1612455 = 2418683) B2418683
theorem B5438123 : Blo 1611004 5438123 := bstep (se 1 (by rfl) ⟨4078592, by rfl⟩ : syracuseStep 5438123 = 8157185) B8157185
theorem B5438447 : Blo 1611004 5438447 := bstep (se 1 (by rfl) ⟨4078835, by rfl⟩ : syracuseStep 5438447 = 8157671) B8157671
theorem B1612863 : Blo 1611004 1612863 := bstep (se 1 (by rfl) ⟨1209647, by rfl⟩ : syracuseStep 1612863 = 2419295) B2419295
theorem B1612911 : Blo 1611004 1612911 := bstep (se 1 (by rfl) ⟨1209683, by rfl⟩ : syracuseStep 1612911 = 2419367) B2419367
theorem B3628169 : Blo 1611004 3628169 := bstep (se 2 (by rfl) ⟨1360563, by rfl⟩ : syracuseStep 3628169 = 2721127) B2721127
theorem B12246227 : Blo 1611004 12246227 := bstep (se 1 (by rfl) ⟨9184670, by rfl⟩ : syracuseStep 12246227 = 18369341) B18369341
theorem B3628295 : Blo 1611004 3628295 := bstep (se 1 (by rfl) ⟨2721221, by rfl⟩ : syracuseStep 3628295 = 5442443) B5442443
theorem B20659769 : Blo 1611004 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B2719399 : Blo 1611004 2719399 := bstep (se 1 (by rfl) ⟨2039549, by rfl⟩ : syracuseStep 2719399 = 4079099) B4079099
theorem B17669863 : Blo 1611004 17669863 := bstep (se 1 (by rfl) ⟨13252397, by rfl⟩ : syracuseStep 17669863 = 26504795) B26504795
theorem B5668823 : Blo 1611004 5668823 := bstep (se 1 (by rfl) ⟨4251617, by rfl⟩ : syracuseStep 5668823 = 8503235) B8503235
theorem B2416799 : Blo 1611004 2416799 := bstep (se 1 (by rfl) ⟨1812599, by rfl⟩ : syracuseStep 2416799 = 3625199) B3625199
theorem B12247199 : Blo 1611004 12247199 := bstep (se 1 (by rfl) ⟨9185399, by rfl⟩ : syracuseStep 12247199 = 18370799) B18370799
theorem B3629231 : Blo 1611004 3629231 := bstep (se 1 (by rfl) ⟨2721923, by rfl⟩ : syracuseStep 3629231 = 5443847) B5443847
theorem B4653353 : Blo 1611004 4653353 := bstep (se 2 (by rfl) ⟨1745007, by rfl⟩ : syracuseStep 4653353 = 3490015) B3490015
theorem B31416761 : Blo 1611004 31416761 := bstep (se 2 (by rfl) ⟨11781285, by rfl⟩ : syracuseStep 31416761 = 23562571) B23562571
theorem B2417135 : Blo 1611004 2417135 := bstep (se 1 (by rfl) ⟨1812851, by rfl⟩ : syracuseStep 2417135 = 3625703) B3625703
theorem B2720297 : Blo 1611004 2720297 := bstep (se 2 (by rfl) ⟨1020111, by rfl⟩ : syracuseStep 2720297 = 2040223) B2040223
theorem B2417435 : Blo 1611004 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B9176105 : Blo 1611004 9176105 := bstep (se 2 (by rfl) ⟨3441039, by rfl⟩ : syracuseStep 9176105 = 6882079) B6882079
theorem B2417705 : Blo 1611004 2417705 := bstep (se 2 (by rfl) ⟨906639, by rfl⟩ : syracuseStep 2417705 = 1813279) B1813279
theorem B107439787 : Blo 1611004 107439787 := bstep (se 1 (by rfl) ⟨80579840, by rfl⟩ : syracuseStep 107439787 = 161159681) B161159681
theorem B3442441 : Blo 1611004 3442441 := bstep (se 2 (by rfl) ⟨1290915, by rfl⟩ : syracuseStep 3442441 = 2581831) B2581831
theorem B2418779 : Blo 1611004 2418779 := bstep (se 1 (by rfl) ⟨1814084, by rfl⟩ : syracuseStep 2418779 = 3628169) B3628169
theorem B2418863 : Blo 1611004 2418863 := bstep (se 1 (by rfl) ⟨1814147, by rfl⟩ : syracuseStep 2418863 = 3628295) B3628295
theorem B15501593 : Blo 1611004 15501593 := bstep (se 2 (by rfl) ⟨5813097, by rfl⟩ : syracuseStep 15501593 = 11626195) B11626195
theorem B13773179 : Blo 1611004 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B5163497 : Blo 1611004 5163497 := bstep (se 2 (by rfl) ⟨1936311, by rfl⟩ : syracuseStep 5163497 = 3872623) B3872623
theorem B15116861 : Blo 1611004 15116861 := bstep (se 3 (by rfl) ⟨2834411, by rfl⟩ : syracuseStep 15116861 = 5668823) B5668823
theorem B2419433 : Blo 1611004 2419433 := bstep (se 2 (by rfl) ⟨907287, by rfl⟩ : syracuseStep 2419433 = 1814575) B1814575
theorem B14150447 : Blo 1611004 14150447 := bstep (se 1 (by rfl) ⟨10612835, by rfl⟩ : syracuseStep 14150447 = 21225671) B21225671
theorem B31419245 : Blo 1611004 31419245 := bstep (se 3 (by rfl) ⟨5891108, by rfl⟩ : syracuseStep 31419245 = 11782217) B11782217
theorem B4082825 : Blo 1611004 4082825 := bstep (se 2 (by rfl) ⟨1531059, by rfl⟩ : syracuseStep 4082825 = 3062119) B3062119
theorem B18362051 : Blo 1611004 18362051 := bstep (se 1 (by rfl) ⟨13771538, by rfl⟩ : syracuseStep 18362051 = 27543077) B27543077
theorem B78409691 : Blo 1611004 78409691 := bstep (se 1 (by rfl) ⟨58807268, by rfl⟩ : syracuseStep 78409691 = 117614537) B117614537
theorem B3625415 : Blo 1611004 3625415 := bstep (se 1 (by rfl) ⟨2719061, by rfl⟩ : syracuseStep 3625415 = 5438123) B5438123
theorem B3625631 : Blo 1611004 3625631 := bstep (se 1 (by rfl) ⟨2719223, by rfl⟩ : syracuseStep 3625631 = 5438447) B5438447
theorem B8164151 : Blo 1611004 8164151 := bstep (se 1 (by rfl) ⟨6123113, by rfl⟩ : syracuseStep 8164151 = 12246227) B12246227
theorem B3625865 : Blo 1611004 3625865 := bstep (se 2 (by rfl) ⟨1359699, by rfl⟩ : syracuseStep 3625865 = 2719399) B2719399
theorem B1611111 : Blo 1611004 1611111 := bstep (se 1 (by rfl) ⟨1208333, by rfl⟩ : syracuseStep 1611111 = 2416667) B2416667
theorem B3675647 : Blo 1611004 3675647 := bstep (se 1 (by rfl) ⟨2756735, by rfl⟩ : syracuseStep 3675647 = 5513471) B5513471
theorem B3266075 : Blo 1611004 3266075 := bstep (se 1 (by rfl) ⟨2449556, by rfl⟩ : syracuseStep 3266075 = 4899113) B4899113
theorem B1611455 : Blo 1611004 1611455 := bstep (se 1 (by rfl) ⟨1208591, by rfl⟩ : syracuseStep 1611455 = 2417183) B2417183
theorem B3626855 : Blo 1611004 3626855 := bstep (se 1 (by rfl) ⟨2720141, by rfl⟩ : syracuseStep 3626855 = 5440283) B5440283
theorem B3626963 : Blo 1611004 3626963 := bstep (se 1 (by rfl) ⟨2720222, by rfl⟩ : syracuseStep 3626963 = 5440445) B5440445
theorem B1611743 : Blo 1611004 1611743 := bstep (se 1 (by rfl) ⟨1208807, by rfl⟩ : syracuseStep 1611743 = 2417615) B2417615
theorem B3061739 : Blo 1611004 3061739 := bstep (se 1 (by rfl) ⟨2296304, by rfl⟩ : syracuseStep 3061739 = 4592609) B4592609
theorem B3627035 : Blo 1611004 3627035 := bstep (se 1 (by rfl) ⟨2720276, by rfl⟩ : syracuseStep 3627035 = 5440553) B5440553
theorem B1611943 : Blo 1611004 1611943 := bstep (se 1 (by rfl) ⟨1208957, by rfl⟩ : syracuseStep 1611943 = 2417915) B2417915
theorem B12245255 : Blo 1611004 12245255 := bstep (se 1 (by rfl) ⟨9183941, by rfl⟩ : syracuseStep 12245255 = 18367883) B18367883
theorem B104773999 : Blo 1611004 104773999 := bstep (se 1 (by rfl) ⟨78580499, by rfl⟩ : syracuseStep 104773999 = 157160999) B157160999
theorem B1612187 : Blo 1611004 1612187 := bstep (se 1 (by rfl) ⟨1209140, by rfl⟩ : syracuseStep 1612187 = 2418281) B2418281
theorem B1612271 : Blo 1611004 1612271 := bstep (se 1 (by rfl) ⟨1209203, by rfl⟩ : syracuseStep 1612271 = 2418407) B2418407
theorem B1612287 : Blo 1611004 1612287 := bstep (se 1 (by rfl) ⟨1209215, by rfl⟩ : syracuseStep 1612287 = 2418431) B2418431
theorem B1612335 : Blo 1611004 1612335 := bstep (se 1 (by rfl) ⟨1209251, by rfl⟩ : syracuseStep 1612335 = 2418503) B2418503
theorem B1743899 : Blo 1611004 1743899 := bstep (se 1 (by rfl) ⟨1307924, by rfl⟩ : syracuseStep 1743899 = 2615849) B2615849
theorem B1612827 : Blo 1611004 1612827 := bstep (se 1 (by rfl) ⟨1209620, by rfl⟩ : syracuseStep 1612827 = 2419241) B2419241
theorem B3628115 : Blo 1611004 3628115 := bstep (se 1 (by rfl) ⟨2721086, by rfl⟩ : syracuseStep 3628115 = 5442173) B5442173
theorem B8158319 : Blo 1611004 8158319 := bstep (se 1 (by rfl) ⟨6118739, by rfl⟩ : syracuseStep 8158319 = 12237479) B12237479
theorem B3628187 : Blo 1611004 3628187 := bstep (se 1 (by rfl) ⟨2721140, by rfl⟩ : syracuseStep 3628187 = 5442281) B5442281
theorem B1612959 : Blo 1611004 1612959 := bstep (se 1 (by rfl) ⟨1209719, by rfl⟩ : syracuseStep 1612959 = 2419439) B2419439
theorem B2039195 : Blo 1611004 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B23559817 : Blo 1611004 23559817 := bstep (se 2 (by rfl) ⟨8834931, by rfl⟩ : syracuseStep 23559817 = 17669863) B17669863
theorem B2416943 : Blo 1611004 2416943 := bstep (se 1 (by rfl) ⟨1812707, by rfl⟩ : syracuseStep 2416943 = 3625415) B3625415
theorem B2417087 : Blo 1611004 2417087 := bstep (se 1 (by rfl) ⟨1812815, by rfl⟩ : syracuseStep 2417087 = 3625631) B3625631
theorem B139698665 : Blo 1611004 139698665 := bstep (se 2 (by rfl) ⟨52386999, by rfl⟩ : syracuseStep 139698665 = 104773999) B104773999
theorem B2417243 : Blo 1611004 2417243 := bstep (se 1 (by rfl) ⟨1812932, by rfl⟩ : syracuseStep 2417243 = 3625865) B3625865
theorem B2450431 : Blo 1611004 2450431 := bstep (se 1 (by rfl) ⟨1837823, by rfl⟩ : syracuseStep 2450431 = 3675647) B3675647
theorem B2417903 : Blo 1611004 2417903 := bstep (se 1 (by rfl) ⟨1813427, by rfl⟩ : syracuseStep 2417903 = 3626855) B3626855
theorem B2417975 : Blo 1611004 2417975 := bstep (se 1 (by rfl) ⟨1813481, by rfl⟩ : syracuseStep 2417975 = 3626963) B3626963
theorem B2418023 : Blo 1611004 2418023 := bstep (se 1 (by rfl) ⟨1813517, by rfl⟩ : syracuseStep 2418023 = 3627035) B3627035
theorem B3442331 : Blo 1611004 3442331 := bstep (se 1 (by rfl) ⟨2581748, by rfl⟩ : syracuseStep 3442331 = 5163497) B5163497
theorem B10077907 : Blo 1611004 10077907 := bstep (se 1 (by rfl) ⟨7558430, by rfl⟩ : syracuseStep 10077907 = 15116861) B15116861
theorem B2418743 : Blo 1611004 2418743 := bstep (se 1 (by rfl) ⟨1814057, by rfl⟩ : syracuseStep 2418743 = 3628115) B3628115
theorem B2721883 : Blo 1611004 2721883 := bstep (se 1 (by rfl) ⟨2041412, by rfl⟩ : syracuseStep 2721883 = 4082825) B4082825
theorem B2418791 : Blo 1611004 2418791 := bstep (se 1 (by rfl) ⟨1814093, by rfl⟩ : syracuseStep 2418791 = 3628187) B3628187
theorem B4589921 : Blo 1611004 4589921 := bstep (se 2 (by rfl) ⟨1721220, by rfl⟩ : syracuseStep 4589921 = 3442441) B3442441
theorem B12241367 : Blo 1611004 12241367 := bstep (se 1 (by rfl) ⟨9181025, by rfl⟩ : syracuseStep 12241367 = 18362051) B18362051
theorem B2419487 : Blo 1611004 2419487 := bstep (se 1 (by rfl) ⟨1814615, by rfl⟩ : syracuseStep 2419487 = 3629231) B3629231
theorem B1813531 : Blo 1611004 1813531 := bstep (se 1 (by rfl) ⟨1360148, by rfl⟩ : syracuseStep 1813531 = 2720297) B2720297
theorem B5442767 : Blo 1611004 5442767 := bstep (se 1 (by rfl) ⟨4082075, by rfl⟩ : syracuseStep 5442767 = 8164151) B8164151
theorem B8163503 : Blo 1611004 8163503 := bstep (se 1 (by rfl) ⟨6122627, by rfl⟩ : syracuseStep 8163503 = 12245255) B12245255
theorem B10334395 : Blo 1611004 10334395 := bstep (se 1 (by rfl) ⟨7750796, by rfl⟩ : syracuseStep 10334395 = 15501593) B15501593
theorem B9433631 : Blo 1611004 9433631 := bstep (se 1 (by rfl) ⟨7075223, by rfl⟩ : syracuseStep 9433631 = 14150447) B14150447
theorem B31413089 : Blo 1611004 31413089 := bstep (se 2 (by rfl) ⟨11779908, by rfl⟩ : syracuseStep 31413089 = 23559817) B23559817
theorem B8164637 : Blo 1611004 8164637 := bstep (se 3 (by rfl) ⟨1530869, by rfl⟩ : syracuseStep 8164637 = 3061739) B3061739
theorem B1611199 : Blo 1611004 1611199 := bstep (se 1 (by rfl) ⟨1208399, by rfl⟩ : syracuseStep 1611199 = 2416799) B2416799
theorem B8164799 : Blo 1611004 8164799 := bstep (se 1 (by rfl) ⟨6123599, by rfl⟩ : syracuseStep 8164799 = 12247199) B12247199
theorem B3102235 : Blo 1611004 3102235 := bstep (se 1 (by rfl) ⟨2326676, by rfl⟩ : syracuseStep 3102235 = 4653353) B4653353
theorem B18601589 : Blo 1611004 18601589 := bstep (se 5 (by rfl) ⟨871949, by rfl⟩ : syracuseStep 18601589 = 1743899) B1743899
theorem B20944507 : Blo 1611004 20944507 := bstep (se 1 (by rfl) ⟨15708380, by rfl⟩ : syracuseStep 20944507 = 31416761) B31416761
theorem B1611423 : Blo 1611004 1611423 := bstep (se 1 (by rfl) ⟨1208567, by rfl⟩ : syracuseStep 1611423 = 2417135) B2417135
theorem B1611623 : Blo 1611004 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B6117403 : Blo 1611004 6117403 := bstep (se 1 (by rfl) ⟨4588052, by rfl⟩ : syracuseStep 6117403 = 9176105) B9176105
theorem B1611803 : Blo 1611004 1611803 := bstep (se 1 (by rfl) ⟨1208852, by rfl⟩ : syracuseStep 1611803 = 2417705) B2417705
theorem B2177383 : Blo 1611004 2177383 := bstep (se 1 (by rfl) ⟨1633037, by rfl⟩ : syracuseStep 2177383 = 3266075) B3266075
theorem B5437853 : Blo 1611004 5437853 := bstep (se 3 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 5437853 = 2039195) B2039195
theorem B1612519 : Blo 1611004 1612519 := bstep (se 1 (by rfl) ⟨1209389, by rfl⟩ : syracuseStep 1612519 = 2418779) B2418779
theorem B1612575 : Blo 1611004 1612575 := bstep (se 1 (by rfl) ⟨1209431, by rfl⟩ : syracuseStep 1612575 = 2418863) B2418863
theorem B9182119 : Blo 1611004 9182119 := bstep (se 1 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 9182119 = 13773179) B13773179
theorem B1612955 : Blo 1611004 1612955 := bstep (se 1 (by rfl) ⟨1209716, by rfl⟩ : syracuseStep 1612955 = 2419433) B2419433
theorem B20946163 : Blo 1611004 20946163 := bstep (se 1 (by rfl) ⟨15709622, by rfl⟩ : syracuseStep 20946163 = 31419245) B31419245
theorem B5438879 : Blo 1611004 5438879 := bstep (se 1 (by rfl) ⟨4079159, by rfl⟩ : syracuseStep 5438879 = 8158319) B8158319
theorem B143253049 : Blo 1611004 143253049 := bstep (se 2 (by rfl) ⟨53719893, by rfl⟩ : syracuseStep 143253049 = 107439787) B107439787
theorem B52273127 : Blo 1611004 52273127 := bstep (se 1 (by rfl) ⟨39204845, by rfl⟩ : syracuseStep 52273127 = 78409691) B78409691
theorem B3629177 : Blo 1611004 3629177 := bstep (se 2 (by rfl) ⟨1360941, by rfl⟩ : syracuseStep 3629177 = 2721883) B2721883
theorem B13779193 : Blo 1611004 13779193 := bstep (se 2 (by rfl) ⟨5167197, by rfl⟩ : syracuseStep 13779193 = 10334395) B10334395
theorem B2294887 : Blo 1611004 2294887 := bstep (se 1 (by rfl) ⟨1721165, by rfl⟩ : syracuseStep 2294887 = 3442331) B3442331
theorem B2418041 : Blo 1611004 2418041 := bstep (se 2 (by rfl) ⟨906765, by rfl⟩ : syracuseStep 2418041 = 1813531) B1813531
theorem B49604237 : Blo 1611004 49604237 := bstep (se 3 (by rfl) ⟨9300794, by rfl⟩ : syracuseStep 49604237 = 18601589) B18601589
theorem B8160911 : Blo 1611004 8160911 := bstep (se 1 (by rfl) ⟨6120683, by rfl⟩ : syracuseStep 8160911 = 12241367) B12241367
theorem B27928217 : Blo 1611004 27928217 := bstep (se 2 (by rfl) ⟨10473081, by rfl⟩ : syracuseStep 27928217 = 20946163) B20946163
theorem B13437209 : Blo 1611004 13437209 := bstep (se 2 (by rfl) ⟨5038953, by rfl⟩ : syracuseStep 13437209 = 10077907) B10077907
theorem B13068965 : Blo 1611004 13068965 := bstep (se 4 (by rfl) ⟨1225215, by rfl⟩ : syracuseStep 13068965 = 2450431) B2450431
theorem B5442335 : Blo 1611004 5442335 := bstep (se 1 (by rfl) ⟨4081751, by rfl⟩ : syracuseStep 5442335 = 8163503) B8163503
theorem B2903177 : Blo 1611004 2903177 := bstep (se 2 (by rfl) ⟨1088691, by rfl⟩ : syracuseStep 2903177 = 2177383) B2177383
theorem B20942059 : Blo 1611004 20942059 := bstep (se 1 (by rfl) ⟨15706544, by rfl⟩ : syracuseStep 20942059 = 31413089) B31413089
theorem B5443091 : Blo 1611004 5443091 := bstep (se 1 (by rfl) ⟨4082318, by rfl⟩ : syracuseStep 5443091 = 8164637) B8164637
theorem B5443199 : Blo 1611004 5443199 := bstep (se 1 (by rfl) ⟨4082399, by rfl⟩ : syracuseStep 5443199 = 8164799) B8164799
theorem B12242825 : Blo 1611004 12242825 := bstep (se 2 (by rfl) ⟨4591059, by rfl⟩ : syracuseStep 12242825 = 9182119) B9182119
theorem B3059947 : Blo 1611004 3059947 := bstep (se 1 (by rfl) ⟨2294960, by rfl⟩ : syracuseStep 3059947 = 4589921) B4589921
theorem B3625235 : Blo 1611004 3625235 := bstep (se 1 (by rfl) ⟨2718926, by rfl⟩ : syracuseStep 3625235 = 5437853) B5437853
theorem B3625919 : Blo 1611004 3625919 := bstep (se 1 (by rfl) ⟨2719439, by rfl⟩ : syracuseStep 3625919 = 5438879) B5438879
theorem B8156537 : Blo 1611004 8156537 := bstep (se 2 (by rfl) ⟨3058701, by rfl⟩ : syracuseStep 8156537 = 6117403) B6117403
theorem B1611295 : Blo 1611004 1611295 := bstep (se 1 (by rfl) ⟨1208471, by rfl⟩ : syracuseStep 1611295 = 2416943) B2416943
theorem B1611391 : Blo 1611004 1611391 := bstep (se 1 (by rfl) ⟨1208543, by rfl⟩ : syracuseStep 1611391 = 2417087) B2417087
theorem B93132443 : Blo 1611004 93132443 := bstep (se 1 (by rfl) ⟨69849332, by rfl⟩ : syracuseStep 93132443 = 139698665) B139698665
theorem B1611495 : Blo 1611004 1611495 := bstep (se 1 (by rfl) ⟨1208621, by rfl⟩ : syracuseStep 1611495 = 2417243) B2417243
theorem B66181013 : Blo 1611004 66181013 := bstep (se 6 (by rfl) ⟨1551117, by rfl⟩ : syracuseStep 66181013 = 3102235) B3102235
theorem B1611935 : Blo 1611004 1611935 := bstep (se 1 (by rfl) ⟨1208951, by rfl⟩ : syracuseStep 1611935 = 2417903) B2417903
theorem B1611983 : Blo 1611004 1611983 := bstep (se 1 (by rfl) ⟨1208987, by rfl⟩ : syracuseStep 1611983 = 2417975) B2417975
theorem B1612015 : Blo 1611004 1612015 := bstep (se 1 (by rfl) ⟨1209011, by rfl⟩ : syracuseStep 1612015 = 2418023) B2418023
theorem B1612495 : Blo 1611004 1612495 := bstep (se 1 (by rfl) ⟨1209371, by rfl⟩ : syracuseStep 1612495 = 2418743) B2418743
theorem B1612527 : Blo 1611004 1612527 := bstep (se 1 (by rfl) ⟨1209395, by rfl⟩ : syracuseStep 1612527 = 2418791) B2418791
theorem B25156349 : Blo 1611004 25156349 := bstep (se 3 (by rfl) ⟨4716815, by rfl⟩ : syracuseStep 25156349 = 9433631) B9433631
theorem B1612991 : Blo 1611004 1612991 := bstep (se 1 (by rfl) ⟨1209743, by rfl⟩ : syracuseStep 1612991 = 2419487) B2419487
theorem B191004065 : Blo 1611004 191004065 := bstep (se 2 (by rfl) ⟨71626524, by rfl⟩ : syracuseStep 191004065 = 143253049) B143253049
theorem B3628511 : Blo 1611004 3628511 := bstep (se 1 (by rfl) ⟨2721383, by rfl⟩ : syracuseStep 3628511 = 5442767) B5442767
theorem B27926009 : Blo 1611004 27926009 := bstep (se 2 (by rfl) ⟨10472253, by rfl⟩ : syracuseStep 27926009 = 20944507) B20944507
theorem B34848751 : Blo 1611004 34848751 := bstep (se 1 (by rfl) ⟨26136563, by rfl⟩ : syracuseStep 34848751 = 52273127) B52273127
theorem B2416823 : Blo 1611004 2416823 := bstep (se 1 (by rfl) ⟨1812617, by rfl⟩ : syracuseStep 2416823 = 3625235) B3625235
theorem B4079929 : Blo 1611004 4079929 := bstep (se 2 (by rfl) ⟨1529973, by rfl⟩ : syracuseStep 4079929 = 3059947) B3059947
theorem B2417279 : Blo 1611004 2417279 := bstep (se 1 (by rfl) ⟨1812959, by rfl⟩ : syracuseStep 2417279 = 3625919) B3625919
theorem B35832557 : Blo 1611004 35832557 := bstep (se 3 (by rfl) ⟨6718604, by rfl⟩ : syracuseStep 35832557 = 13437209) B13437209
theorem B5440607 : Blo 1611004 5440607 := bstep (se 1 (by rfl) ⟨4080455, by rfl⟩ : syracuseStep 5440607 = 8160911) B8160911
theorem B62088295 : Blo 1611004 62088295 := bstep (se 1 (by rfl) ⟨46566221, by rfl⟩ : syracuseStep 62088295 = 93132443) B93132443
theorem B16770899 : Blo 1611004 16770899 := bstep (se 1 (by rfl) ⟨12578174, by rfl⟩ : syracuseStep 16770899 = 25156349) B25156349
theorem B1935451 : Blo 1611004 1935451 := bstep (se 1 (by rfl) ⟨1451588, by rfl⟩ : syracuseStep 1935451 = 2903177) B2903177
theorem B2419007 : Blo 1611004 2419007 := bstep (se 1 (by rfl) ⟨1814255, by rfl⟩ : syracuseStep 2419007 = 3628511) B3628511
theorem B8161883 : Blo 1611004 8161883 := bstep (se 1 (by rfl) ⟨6121412, by rfl⟩ : syracuseStep 8161883 = 12242825) B12242825
theorem B2419451 : Blo 1611004 2419451 := bstep (se 1 (by rfl) ⟨1814588, by rfl⟩ : syracuseStep 2419451 = 3629177) B3629177
theorem B3059849 : Blo 1611004 3059849 := bstep (se 2 (by rfl) ⟨1147443, by rfl⟩ : syracuseStep 3059849 = 2294887) B2294887
theorem B27922745 : Blo 1611004 27922745 := bstep (se 2 (by rfl) ⟨10471029, by rfl⟩ : syracuseStep 27922745 = 20942059) B20942059
theorem B8712643 : Blo 1611004 8712643 := bstep (se 1 (by rfl) ⟨6534482, by rfl⟩ : syracuseStep 8712643 = 13068965) B13068965
theorem B18617339 : Blo 1611004 18617339 := bstep (se 1 (by rfl) ⟨13963004, by rfl⟩ : syracuseStep 18617339 = 27926009) B27926009
theorem B18372257 : Blo 1611004 18372257 := bstep (se 2 (by rfl) ⟨6889596, by rfl⟩ : syracuseStep 18372257 = 13779193) B13779193
theorem B5437691 : Blo 1611004 5437691 := bstep (se 1 (by rfl) ⟨4078268, by rfl⟩ : syracuseStep 5437691 = 8156537) B8156537
theorem B1612027 : Blo 1611004 1612027 := bstep (se 1 (by rfl) ⟨1209020, by rfl⟩ : syracuseStep 1612027 = 2418041) B2418041
theorem B33069491 : Blo 1611004 33069491 := bstep (se 1 (by rfl) ⟨24802118, by rfl⟩ : syracuseStep 33069491 = 49604237) B49604237
theorem B18618811 : Blo 1611004 18618811 := bstep (se 1 (by rfl) ⟨13964108, by rfl⟩ : syracuseStep 18618811 = 27928217) B27928217
theorem B44120675 : Blo 1611004 44120675 := bstep (se 1 (by rfl) ⟨33090506, by rfl⟩ : syracuseStep 44120675 = 66181013) B66181013
theorem B3628223 : Blo 1611004 3628223 := bstep (se 1 (by rfl) ⟨2721167, by rfl⟩ : syracuseStep 3628223 = 5442335) B5442335
theorem B127336043 : Blo 1611004 127336043 := bstep (se 1 (by rfl) ⟨95502032, by rfl⟩ : syracuseStep 127336043 = 191004065) B191004065
theorem B3628727 : Blo 1611004 3628727 := bstep (se 1 (by rfl) ⟨2721545, by rfl⟩ : syracuseStep 3628727 = 5443091) B5443091
theorem B3628799 : Blo 1611004 3628799 := bstep (se 1 (by rfl) ⟨2721599, by rfl⟩ : syracuseStep 3628799 = 5443199) B5443199
theorem B46465001 : Blo 1611004 46465001 := bstep (se 2 (by rfl) ⟨17424375, by rfl⟩ : syracuseStep 46465001 = 34848751) B34848751
theorem B2039899 : Blo 1611004 2039899 := bstep (se 1 (by rfl) ⟨1529924, by rfl⟩ : syracuseStep 2039899 = 3059849) B3059849
theorem B2580601 : Blo 1611004 2580601 := bstep (se 2 (by rfl) ⟨967725, by rfl⟩ : syracuseStep 2580601 = 1935451) B1935451
theorem B5439905 : Blo 1611004 5439905 := bstep (se 2 (by rfl) ⟨2039964, by rfl⟩ : syracuseStep 5439905 = 4079929) B4079929
theorem B23888371 : Blo 1611004 23888371 := bstep (se 1 (by rfl) ⟨17916278, by rfl⟩ : syracuseStep 23888371 = 35832557) B35832557
theorem B11616857 : Blo 1611004 11616857 := bstep (se 2 (by rfl) ⟨4356321, by rfl⟩ : syracuseStep 11616857 = 8712643) B8712643
theorem B12411559 : Blo 1611004 12411559 := bstep (se 1 (by rfl) ⟨9308669, by rfl⟩ : syracuseStep 12411559 = 18617339) B18617339
theorem B12248171 : Blo 1611004 12248171 := bstep (se 1 (by rfl) ⟨9186128, by rfl⟩ : syracuseStep 12248171 = 18372257) B18372257
theorem B22046327 : Blo 1611004 22046327 := bstep (se 1 (by rfl) ⟨16534745, by rfl⟩ : syracuseStep 22046327 = 33069491) B33069491
theorem B5441255 : Blo 1611004 5441255 := bstep (se 1 (by rfl) ⟨4080941, by rfl⟩ : syracuseStep 5441255 = 8161883) B8161883
theorem B2418815 : Blo 1611004 2418815 := bstep (se 1 (by rfl) ⟨1814111, by rfl⟩ : syracuseStep 2418815 = 3628223) B3628223
theorem B2419151 : Blo 1611004 2419151 := bstep (se 1 (by rfl) ⟨1814363, by rfl⟩ : syracuseStep 2419151 = 3628727) B3628727
theorem B2419199 : Blo 1611004 2419199 := bstep (se 1 (by rfl) ⟨1814399, by rfl⟩ : syracuseStep 2419199 = 3628799) B3628799
theorem B30976667 : Blo 1611004 30976667 := bstep (se 1 (by rfl) ⟨23232500, by rfl⟩ : syracuseStep 30976667 = 46465001) B46465001
theorem B74460653 : Blo 1611004 74460653 := bstep (se 3 (by rfl) ⟨13961372, by rfl⟩ : syracuseStep 74460653 = 27922745) B27922745
theorem B82784393 : Blo 1611004 82784393 := bstep (se 2 (by rfl) ⟨31044147, by rfl⟩ : syracuseStep 82784393 = 62088295) B62088295
theorem B3625127 : Blo 1611004 3625127 := bstep (se 1 (by rfl) ⟨2718845, by rfl⟩ : syracuseStep 3625127 = 5437691) B5437691
theorem B29413783 : Blo 1611004 29413783 := bstep (se 1 (by rfl) ⟨22060337, by rfl⟩ : syracuseStep 29413783 = 44120675) B44120675
theorem B99300325 : Blo 1611004 99300325 := bstep (se 4 (by rfl) ⟨9309405, by rfl⟩ : syracuseStep 99300325 = 18618811) B18618811
theorem B84890695 : Blo 1611004 84890695 := bstep (se 1 (by rfl) ⟨63668021, by rfl⟩ : syracuseStep 84890695 = 127336043) B127336043
theorem B1611215 : Blo 1611004 1611215 := bstep (se 1 (by rfl) ⟨1208411, by rfl⟩ : syracuseStep 1611215 = 2416823) B2416823
theorem B1611519 : Blo 1611004 1611519 := bstep (se 1 (by rfl) ⟨1208639, by rfl⟩ : syracuseStep 1611519 = 2417279) B2417279
theorem B3627071 : Blo 1611004 3627071 := bstep (se 1 (by rfl) ⟨2720303, by rfl⟩ : syracuseStep 3627071 = 5440607) B5440607
theorem B11180599 : Blo 1611004 11180599 := bstep (se 1 (by rfl) ⟨8385449, by rfl⟩ : syracuseStep 11180599 = 16770899) B16770899
theorem B1612671 : Blo 1611004 1612671 := bstep (se 1 (by rfl) ⟨1209503, by rfl⟩ : syracuseStep 1612671 = 2419007) B2419007
theorem B1612967 : Blo 1611004 1612967 := bstep (se 1 (by rfl) ⟨1209725, by rfl⟩ : syracuseStep 1612967 = 2419451) B2419451
theorem B55189595 : Blo 1611004 55189595 := bstep (se 1 (by rfl) ⟨41392196, by rfl⟩ : syracuseStep 55189595 = 82784393) B82784393
theorem B2416751 : Blo 1611004 2416751 := bstep (se 1 (by rfl) ⟨1812563, by rfl⟩ : syracuseStep 2416751 = 3625127) B3625127
theorem B2719865 : Blo 1611004 2719865 := bstep (se 2 (by rfl) ⟨1019949, by rfl⟩ : syracuseStep 2719865 = 2039899) B2039899
theorem B3440801 : Blo 1611004 3440801 := bstep (se 2 (by rfl) ⟨1290300, by rfl⟩ : syracuseStep 3440801 = 2580601) B2580601
theorem B59629861 : Blo 1611004 59629861 := bstep (se 4 (by rfl) ⟨5590299, by rfl⟩ : syracuseStep 59629861 = 11180599) B11180599
theorem B31851161 : Blo 1611004 31851161 := bstep (se 2 (by rfl) ⟨11944185, by rfl⟩ : syracuseStep 31851161 = 23888371) B23888371
theorem B16548745 : Blo 1611004 16548745 := bstep (se 2 (by rfl) ⟨6205779, by rfl⟩ : syracuseStep 16548745 = 12411559) B12411559
theorem B14697551 : Blo 1611004 14697551 := bstep (se 1 (by rfl) ⟨11023163, by rfl⟩ : syracuseStep 14697551 = 22046327) B22046327
theorem B132400433 : Blo 1611004 132400433 := bstep (se 2 (by rfl) ⟨49650162, by rfl⟩ : syracuseStep 132400433 = 99300325) B99300325
theorem B2418047 : Blo 1611004 2418047 := bstep (se 1 (by rfl) ⟨1813535, by rfl⟩ : syracuseStep 2418047 = 3627071) B3627071
theorem B7744571 : Blo 1611004 7744571 := bstep (se 1 (by rfl) ⟨5808428, by rfl⟩ : syracuseStep 7744571 = 11616857) B11616857
theorem B39218377 : Blo 1611004 39218377 := bstep (se 2 (by rfl) ⟨14706891, by rfl⟩ : syracuseStep 39218377 = 29413783) B29413783
theorem B49640435 : Blo 1611004 49640435 := bstep (se 1 (by rfl) ⟨37230326, by rfl⟩ : syracuseStep 49640435 = 74460653) B74460653
theorem B3626603 : Blo 1611004 3626603 := bstep (se 1 (by rfl) ⟨2719952, by rfl⟩ : syracuseStep 3626603 = 5439905) B5439905
theorem B8165447 : Blo 1611004 8165447 := bstep (se 1 (by rfl) ⟨6124085, by rfl⟩ : syracuseStep 8165447 = 12248171) B12248171
theorem B3627503 : Blo 1611004 3627503 := bstep (se 1 (by rfl) ⟨2720627, by rfl⟩ : syracuseStep 3627503 = 5441255) B5441255
theorem B1612543 : Blo 1611004 1612543 := bstep (se 1 (by rfl) ⟨1209407, by rfl⟩ : syracuseStep 1612543 = 2418815) B2418815
theorem B113187593 : Blo 1611004 113187593 := bstep (se 2 (by rfl) ⟨42445347, by rfl⟩ : syracuseStep 113187593 = 84890695) B84890695
theorem B1612767 : Blo 1611004 1612767 := bstep (se 1 (by rfl) ⟨1209575, by rfl⟩ : syracuseStep 1612767 = 2419151) B2419151
theorem B1612799 : Blo 1611004 1612799 := bstep (se 1 (by rfl) ⟨1209599, by rfl⟩ : syracuseStep 1612799 = 2419199) B2419199
theorem B20651111 : Blo 1611004 20651111 := bstep (se 1 (by rfl) ⟨15488333, by rfl⟩ : syracuseStep 20651111 = 30976667) B30976667
theorem B2293867 : Blo 1611004 2293867 := bstep (se 1 (by rfl) ⟨1720400, by rfl⟩ : syracuseStep 2293867 = 3440801) B3440801
theorem B21234107 : Blo 1611004 21234107 := bstep (se 1 (by rfl) ⟨15925580, by rfl⟩ : syracuseStep 21234107 = 31851161) B31851161
theorem B2417735 : Blo 1611004 2417735 := bstep (se 1 (by rfl) ⟨1813301, by rfl⟩ : syracuseStep 2417735 = 3626603) B3626603
theorem B52291169 : Blo 1611004 52291169 := bstep (se 2 (by rfl) ⟨19609188, by rfl⟩ : syracuseStep 52291169 = 39218377) B39218377
theorem B2418335 : Blo 1611004 2418335 := bstep (se 1 (by rfl) ⟨1813751, by rfl⟩ : syracuseStep 2418335 = 3627503) B3627503
theorem B75458395 : Blo 1611004 75458395 := bstep (se 1 (by rfl) ⟨56593796, by rfl⟩ : syracuseStep 75458395 = 113187593) B113187593
theorem B5163047 : Blo 1611004 5163047 := bstep (se 1 (by rfl) ⟨3872285, by rfl⟩ : syracuseStep 5163047 = 7744571) B7744571
theorem B36793063 : Blo 1611004 36793063 := bstep (se 1 (by rfl) ⟨27594797, by rfl⟩ : syracuseStep 36793063 = 55189595) B55189595
theorem B1813243 : Blo 1611004 1813243 := bstep (se 1 (by rfl) ⟨1359932, by rfl⟩ : syracuseStep 1813243 = 2719865) B2719865
theorem B39193469 : Blo 1611004 39193469 := bstep (se 3 (by rfl) ⟨7348775, by rfl⟩ : syracuseStep 39193469 = 14697551) B14697551
theorem B79506481 : Blo 1611004 79506481 := bstep (se 2 (by rfl) ⟨29814930, by rfl⟩ : syracuseStep 79506481 = 59629861) B59629861
theorem B22064993 : Blo 1611004 22064993 := bstep (se 2 (by rfl) ⟨8274372, by rfl⟩ : syracuseStep 22064993 = 16548745) B16548745
theorem B5443631 : Blo 1611004 5443631 := bstep (se 1 (by rfl) ⟨4082723, by rfl⟩ : syracuseStep 5443631 = 8165447) B8165447
theorem B13767407 : Blo 1611004 13767407 := bstep (se 1 (by rfl) ⟨10325555, by rfl⟩ : syracuseStep 13767407 = 20651111) B20651111
theorem B1611167 : Blo 1611004 1611167 := bstep (se 1 (by rfl) ⟨1208375, by rfl⟩ : syracuseStep 1611167 = 2416751) B2416751
theorem B33093623 : Blo 1611004 33093623 := bstep (se 1 (by rfl) ⟨24820217, by rfl⟩ : syracuseStep 33093623 = 49640435) B49640435
theorem B88266955 : Blo 1611004 88266955 := bstep (se 1 (by rfl) ⟨66200216, by rfl⟩ : syracuseStep 88266955 = 132400433) B132400433
theorem B1612031 : Blo 1611004 1612031 := bstep (se 1 (by rfl) ⟨1209023, by rfl⟩ : syracuseStep 1612031 = 2418047) B2418047
theorem B3629087 : Blo 1611004 3629087 := bstep (se 1 (by rfl) ⟨2721815, by rfl⟩ : syracuseStep 3629087 = 5443631) B5443631
theorem B2417657 : Blo 1611004 2417657 := bstep (se 2 (by rfl) ⟨906621, by rfl⟩ : syracuseStep 2417657 = 1813243) B1813243
theorem B56624285 : Blo 1611004 56624285 := bstep (se 3 (by rfl) ⟨10617053, by rfl⟩ : syracuseStep 56624285 = 21234107) B21234107
theorem B22062415 : Blo 1611004 22062415 := bstep (se 1 (by rfl) ⟨16546811, by rfl⟩ : syracuseStep 22062415 = 33093623) B33093623
theorem B3442031 : Blo 1611004 3442031 := bstep (se 1 (by rfl) ⟨2581523, by rfl⟩ : syracuseStep 3442031 = 5163047) B5163047
theorem B3058489 : Blo 1611004 3058489 := bstep (se 2 (by rfl) ⟨1146933, by rfl⟩ : syracuseStep 3058489 = 2293867) B2293867
theorem B117689273 : Blo 1611004 117689273 := bstep (se 2 (by rfl) ⟨44133477, by rfl⟩ : syracuseStep 117689273 = 88266955) B88266955
theorem B9178271 : Blo 1611004 9178271 := bstep (se 1 (by rfl) ⟨6883703, by rfl⟩ : syracuseStep 9178271 = 13767407) B13767407
theorem B49057417 : Blo 1611004 49057417 := bstep (se 2 (by rfl) ⟨18396531, by rfl⟩ : syracuseStep 49057417 = 36793063) B36793063
theorem B34860779 : Blo 1611004 34860779 := bstep (se 1 (by rfl) ⟨26145584, by rfl⟩ : syracuseStep 34860779 = 52291169) B52291169
theorem B106008641 : Blo 1611004 106008641 := bstep (se 2 (by rfl) ⟨39753240, by rfl⟩ : syracuseStep 106008641 = 79506481) B79506481
theorem B26128979 : Blo 1611004 26128979 := bstep (se 1 (by rfl) ⟨19596734, by rfl⟩ : syracuseStep 26128979 = 39193469) B39193469
theorem B100611193 : Blo 1611004 100611193 := bstep (se 2 (by rfl) ⟨37729197, by rfl⟩ : syracuseStep 100611193 = 75458395) B75458395
theorem B14709995 : Blo 1611004 14709995 := bstep (se 1 (by rfl) ⟨11032496, by rfl⟩ : syracuseStep 14709995 = 22064993) B22064993
theorem B1611823 : Blo 1611004 1611823 := bstep (se 1 (by rfl) ⟨1208867, by rfl⟩ : syracuseStep 1611823 = 2417735) B2417735
theorem B1612223 : Blo 1611004 1612223 := bstep (se 1 (by rfl) ⟨1209167, by rfl⟩ : syracuseStep 1612223 = 2418335) B2418335
theorem B70672427 : Blo 1611004 70672427 := bstep (se 1 (by rfl) ⟨53004320, by rfl⟩ : syracuseStep 70672427 = 106008641) B106008641
theorem B37749523 : Blo 1611004 37749523 := bstep (se 1 (by rfl) ⟨28312142, by rfl⟩ : syracuseStep 37749523 = 56624285) B56624285
theorem B9806663 : Blo 1611004 9806663 := bstep (se 1 (by rfl) ⟨7354997, by rfl⟩ : syracuseStep 9806663 = 14709995) B14709995
theorem B2294687 : Blo 1611004 2294687 := bstep (se 1 (by rfl) ⟨1721015, by rfl⟩ : syracuseStep 2294687 = 3442031) B3442031
theorem B2419391 : Blo 1611004 2419391 := bstep (se 1 (by rfl) ⟨1814543, by rfl⟩ : syracuseStep 2419391 = 3629087) B3629087
theorem B17419319 : Blo 1611004 17419319 := bstep (se 1 (by rfl) ⟨13064489, by rfl⟩ : syracuseStep 17419319 = 26128979) B26128979
theorem B134148257 : Blo 1611004 134148257 := bstep (se 2 (by rfl) ⟨50305596, by rfl⟩ : syracuseStep 134148257 = 100611193) B100611193
theorem B78459515 : Blo 1611004 78459515 := bstep (se 1 (by rfl) ⟨58844636, by rfl⟩ : syracuseStep 78459515 = 117689273) B117689273
theorem B65409889 : Blo 1611004 65409889 := bstep (se 2 (by rfl) ⟨24528708, by rfl⟩ : syracuseStep 65409889 = 49057417) B49057417
theorem B1611771 : Blo 1611004 1611771 := bstep (se 1 (by rfl) ⟨1208828, by rfl⟩ : syracuseStep 1611771 = 2417657) B2417657
theorem B4077985 : Blo 1611004 4077985 := bstep (se 2 (by rfl) ⟨1529244, by rfl⟩ : syracuseStep 4077985 = 3058489) B3058489
theorem B29416553 : Blo 1611004 29416553 := bstep (se 2 (by rfl) ⟨11031207, by rfl⟩ : syracuseStep 29416553 = 22062415) B22062415
theorem B6118847 : Blo 1611004 6118847 := bstep (se 1 (by rfl) ⟨4589135, by rfl⟩ : syracuseStep 6118847 = 9178271) B9178271
theorem B23240519 : Blo 1611004 23240519 := bstep (se 1 (by rfl) ⟨17430389, by rfl⟩ : syracuseStep 23240519 = 34860779) B34860779
theorem B89432171 : Blo 1611004 89432171 := bstep (se 1 (by rfl) ⟨67074128, by rfl⟩ : syracuseStep 89432171 = 134148257) B134148257
theorem B52306343 : Blo 1611004 52306343 := bstep (se 1 (by rfl) ⟨39229757, by rfl⟩ : syracuseStep 52306343 = 78459515) B78459515
theorem B6537775 : Blo 1611004 6537775 := bstep (se 1 (by rfl) ⟨4903331, by rfl⟩ : syracuseStep 6537775 = 9806663) B9806663
theorem B50332697 : Blo 1611004 50332697 := bstep (se 2 (by rfl) ⟨18874761, by rfl⟩ : syracuseStep 50332697 = 37749523) B37749523
theorem B87213185 : Blo 1611004 87213185 := bstep (se 2 (by rfl) ⟨32704944, by rfl⟩ : syracuseStep 87213185 = 65409889) B65409889
theorem B15493679 : Blo 1611004 15493679 := bstep (se 1 (by rfl) ⟨11620259, by rfl⟩ : syracuseStep 15493679 = 23240519) B23240519
theorem B47114951 : Blo 1611004 47114951 := bstep (se 1 (by rfl) ⟨35336213, by rfl⟩ : syracuseStep 47114951 = 70672427) B70672427
theorem B11612879 : Blo 1611004 11612879 := bstep (se 1 (by rfl) ⟨8709659, by rfl⟩ : syracuseStep 11612879 = 17419319) B17419319
theorem B5437313 : Blo 1611004 5437313 := bstep (se 2 (by rfl) ⟨2038992, by rfl⟩ : syracuseStep 5437313 = 4077985) B4077985
theorem B1612927 : Blo 1611004 1612927 := bstep (se 1 (by rfl) ⟨1209695, by rfl⟩ : syracuseStep 1612927 = 2419391) B2419391
theorem B19611035 : Blo 1611004 19611035 := bstep (se 1 (by rfl) ⟨14708276, by rfl⟩ : syracuseStep 19611035 = 29416553) B29416553
theorem B4079231 : Blo 1611004 4079231 := bstep (se 1 (by rfl) ⟨3059423, by rfl⟩ : syracuseStep 4079231 = 6118847) B6118847
theorem B6119165 : Blo 1611004 6119165 := bstep (se 3 (by rfl) ⟨1147343, by rfl⟩ : syracuseStep 6119165 = 2294687) B2294687
theorem B59621447 : Blo 1611004 59621447 := bstep (se 1 (by rfl) ⟨44716085, by rfl⟩ : syracuseStep 59621447 = 89432171) B89432171
theorem B7741919 : Blo 1611004 7741919 := bstep (se 1 (by rfl) ⟨5806439, by rfl⟩ : syracuseStep 7741919 = 11612879) B11612879
theorem B33555131 : Blo 1611004 33555131 := bstep (se 1 (by rfl) ⟨25166348, by rfl⟩ : syracuseStep 33555131 = 50332697) B50332697
theorem B8717033 : Blo 1611004 8717033 := bstep (se 2 (by rfl) ⟨3268887, by rfl⟩ : syracuseStep 8717033 = 6537775) B6537775
theorem B58142123 : Blo 1611004 58142123 := bstep (se 1 (by rfl) ⟨43606592, by rfl⟩ : syracuseStep 58142123 = 87213185) B87213185
theorem B3624875 : Blo 1611004 3624875 := bstep (se 1 (by rfl) ⟨2718656, by rfl⟩ : syracuseStep 3624875 = 5437313) B5437313
theorem B502559477 : Blo 1611004 502559477 := bstep (se 5 (by rfl) ⟨23557475, by rfl⟩ : syracuseStep 502559477 = 47114951) B47114951
theorem B34870895 : Blo 1611004 34870895 := bstep (se 1 (by rfl) ⟨26153171, by rfl⟩ : syracuseStep 34870895 = 52306343) B52306343
theorem B10329119 : Blo 1611004 10329119 := bstep (se 1 (by rfl) ⟨7746839, by rfl⟩ : syracuseStep 10329119 = 15493679) B15493679
theorem B13074023 : Blo 1611004 13074023 := bstep (se 1 (by rfl) ⟨9805517, by rfl⟩ : syracuseStep 13074023 = 19611035) B19611035
theorem B2719487 : Blo 1611004 2719487 := bstep (se 1 (by rfl) ⟨2039615, by rfl⟩ : syracuseStep 2719487 = 4079231) B4079231
theorem B4079443 : Blo 1611004 4079443 := bstep (se 1 (by rfl) ⟨3059582, by rfl⟩ : syracuseStep 4079443 = 6119165) B6119165
theorem B158990525 : Blo 1611004 158990525 := bstep (se 3 (by rfl) ⟨29810723, by rfl⟩ : syracuseStep 158990525 = 59621447) B59621447
theorem B5161279 : Blo 1611004 5161279 := bstep (se 1 (by rfl) ⟨3870959, by rfl⟩ : syracuseStep 5161279 = 7741919) B7741919
theorem B1812991 : Blo 1611004 1812991 := bstep (se 1 (by rfl) ⟨1359743, by rfl⟩ : syracuseStep 1812991 = 2719487) B2719487
theorem B5811355 : Blo 1611004 5811355 := bstep (se 1 (by rfl) ⟨4358516, by rfl⟩ : syracuseStep 5811355 = 8717033) B8717033
theorem B335039651 : Blo 1611004 335039651 := bstep (se 1 (by rfl) ⟨251279738, by rfl⟩ : syracuseStep 335039651 = 502559477) B502559477
theorem B6886079 : Blo 1611004 6886079 := bstep (se 1 (by rfl) ⟨5164559, by rfl⟩ : syracuseStep 6886079 = 10329119) B10329119
theorem B38761415 : Blo 1611004 38761415 := bstep (se 1 (by rfl) ⟨29071061, by rfl⟩ : syracuseStep 38761415 = 58142123) B58142123
theorem B22370087 : Blo 1611004 22370087 := bstep (se 1 (by rfl) ⟨16777565, by rfl⟩ : syracuseStep 22370087 = 33555131) B33555131
theorem B23247263 : Blo 1611004 23247263 := bstep (se 1 (by rfl) ⟨17435447, by rfl⟩ : syracuseStep 23247263 = 34870895) B34870895
theorem B8716015 : Blo 1611004 8716015 := bstep (se 1 (by rfl) ⟨6537011, by rfl⟩ : syracuseStep 8716015 = 13074023) B13074023
theorem B5439257 : Blo 1611004 5439257 := bstep (se 2 (by rfl) ⟨2039721, by rfl⟩ : syracuseStep 5439257 = 4079443) B4079443
theorem B2416583 : Blo 1611004 2416583 := bstep (se 1 (by rfl) ⟨1812437, by rfl⟩ : syracuseStep 2416583 = 3624875) B3624875
theorem B6881705 : Blo 1611004 6881705 := bstep (se 2 (by rfl) ⟨2580639, by rfl⟩ : syracuseStep 6881705 = 5161279) B5161279
theorem B2417321 : Blo 1611004 2417321 := bstep (se 2 (by rfl) ⟨906495, by rfl⟩ : syracuseStep 2417321 = 1812991) B1812991
theorem B4590719 : Blo 1611004 4590719 := bstep (se 1 (by rfl) ⟨3443039, by rfl⟩ : syracuseStep 4590719 = 6886079) B6886079
theorem B25840943 : Blo 1611004 25840943 := bstep (se 1 (by rfl) ⟨19380707, by rfl⟩ : syracuseStep 25840943 = 38761415) B38761415
theorem B14913391 : Blo 1611004 14913391 := bstep (se 1 (by rfl) ⟨11185043, by rfl⟩ : syracuseStep 14913391 = 22370087) B22370087
theorem B223359767 : Blo 1611004 223359767 := bstep (se 1 (by rfl) ⟨167519825, by rfl⟩ : syracuseStep 223359767 = 335039651) B335039651
theorem B11621353 : Blo 1611004 11621353 := bstep (se 2 (by rfl) ⟨4358007, by rfl⟩ : syracuseStep 11621353 = 8716015) B8716015
theorem B3626171 : Blo 1611004 3626171 := bstep (se 1 (by rfl) ⟨2719628, by rfl⟩ : syracuseStep 3626171 = 5439257) B5439257
theorem B1611055 : Blo 1611004 1611055 := bstep (se 1 (by rfl) ⟨1208291, by rfl⟩ : syracuseStep 1611055 = 2416583) B2416583
theorem B105993683 : Blo 1611004 105993683 := bstep (se 1 (by rfl) ⟨79495262, by rfl⟩ : syracuseStep 105993683 = 158990525) B158990525
theorem B7748473 : Blo 1611004 7748473 := bstep (se 2 (by rfl) ⟨2905677, by rfl⟩ : syracuseStep 7748473 = 5811355) B5811355
theorem B15498175 : Blo 1611004 15498175 := bstep (se 1 (by rfl) ⟨11623631, by rfl⟩ : syracuseStep 15498175 = 23247263) B23247263
theorem B4587803 : Blo 1611004 4587803 := bstep (se 1 (by rfl) ⟨3440852, by rfl⟩ : syracuseStep 4587803 = 6881705) B6881705
theorem B148906511 : Blo 1611004 148906511 := bstep (se 1 (by rfl) ⟨111679883, by rfl⟩ : syracuseStep 148906511 = 223359767) B223359767
theorem B2417447 : Blo 1611004 2417447 := bstep (se 1 (by rfl) ⟨1813085, by rfl⟩ : syracuseStep 2417447 = 3626171) B3626171
theorem B10331297 : Blo 1611004 10331297 := bstep (se 2 (by rfl) ⟨3874236, by rfl⟩ : syracuseStep 10331297 = 7748473) B7748473
theorem B19884521 : Blo 1611004 19884521 := bstep (se 2 (by rfl) ⟨7456695, by rfl⟩ : syracuseStep 19884521 = 14913391) B14913391
theorem B20664233 : Blo 1611004 20664233 := bstep (se 2 (by rfl) ⟨7749087, by rfl⟩ : syracuseStep 20664233 = 15498175) B15498175
theorem B15495137 : Blo 1611004 15495137 := bstep (se 2 (by rfl) ⟨5810676, by rfl⟩ : syracuseStep 15495137 = 11621353) B11621353
theorem B3060479 : Blo 1611004 3060479 := bstep (se 1 (by rfl) ⟨2295359, by rfl⟩ : syracuseStep 3060479 = 4590719) B4590719
theorem B1611547 : Blo 1611004 1611547 := bstep (se 1 (by rfl) ⟨1208660, by rfl⟩ : syracuseStep 1611547 = 2417321) B2417321
theorem B70662455 : Blo 1611004 70662455 := bstep (se 1 (by rfl) ⟨52996841, by rfl⟩ : syracuseStep 70662455 = 105993683) B105993683
theorem B17227295 : Blo 1611004 17227295 := bstep (se 1 (by rfl) ⟨12920471, by rfl⟩ : syracuseStep 17227295 = 25840943) B25840943
theorem B99271007 : Blo 1611004 99271007 := bstep (se 1 (by rfl) ⟨74453255, by rfl⟩ : syracuseStep 99271007 = 148906511) B148906511
theorem B2040319 : Blo 1611004 2040319 := bstep (se 1 (by rfl) ⟨1530239, by rfl⟩ : syracuseStep 2040319 = 3060479) B3060479
theorem B13256347 : Blo 1611004 13256347 := bstep (se 1 (by rfl) ⟨9942260, by rfl⟩ : syracuseStep 13256347 = 19884521) B19884521
theorem B3058535 : Blo 1611004 3058535 := bstep (se 1 (by rfl) ⟨2293901, by rfl⟩ : syracuseStep 3058535 = 4587803) B4587803
theorem B47108303 : Blo 1611004 47108303 := bstep (se 1 (by rfl) ⟨35331227, by rfl⟩ : syracuseStep 47108303 = 70662455) B70662455
theorem B13776155 : Blo 1611004 13776155 := bstep (se 1 (by rfl) ⟨10332116, by rfl⟩ : syracuseStep 13776155 = 20664233) B20664233
theorem B1611631 : Blo 1611004 1611631 := bstep (se 1 (by rfl) ⟨1208723, by rfl⟩ : syracuseStep 1611631 = 2417447) B2417447
theorem B6887531 : Blo 1611004 6887531 := bstep (se 1 (by rfl) ⟨5165648, by rfl⟩ : syracuseStep 6887531 = 10331297) B10331297
theorem B11484863 : Blo 1611004 11484863 := bstep (se 1 (by rfl) ⟨8613647, by rfl⟩ : syracuseStep 11484863 = 17227295) B17227295
theorem B10330091 : Blo 1611004 10330091 := bstep (se 1 (by rfl) ⟨7747568, by rfl⟩ : syracuseStep 10330091 = 15495137) B15495137
theorem B2720425 : Blo 1611004 2720425 := bstep (se 2 (by rfl) ⟨1020159, by rfl⟩ : syracuseStep 2720425 = 2040319) B2040319
theorem B9184103 : Blo 1611004 9184103 := bstep (se 1 (by rfl) ⟨6888077, by rfl⟩ : syracuseStep 9184103 = 13776155) B13776155
theorem B4591687 : Blo 1611004 4591687 := bstep (se 1 (by rfl) ⟨3443765, by rfl⟩ : syracuseStep 4591687 = 6887531) B6887531
theorem B17675129 : Blo 1611004 17675129 := bstep (se 2 (by rfl) ⟨6628173, by rfl⟩ : syracuseStep 17675129 = 13256347) B13256347
theorem B7656575 : Blo 1611004 7656575 := bstep (se 1 (by rfl) ⟨5742431, by rfl⟩ : syracuseStep 7656575 = 11484863) B11484863
theorem B6886727 : Blo 1611004 6886727 := bstep (se 1 (by rfl) ⟨5165045, by rfl⟩ : syracuseStep 6886727 = 10330091) B10330091
theorem B31405535 : Blo 1611004 31405535 := bstep (se 1 (by rfl) ⟨23554151, by rfl⟩ : syracuseStep 31405535 = 47108303) B47108303
theorem B66180671 : Blo 1611004 66180671 := bstep (se 1 (by rfl) ⟨49635503, by rfl⟩ : syracuseStep 66180671 = 99271007) B99271007
theorem B2039023 : Blo 1611004 2039023 := bstep (se 1 (by rfl) ⟨1529267, by rfl⟩ : syracuseStep 2039023 = 3058535) B3058535
theorem B6122249 : Blo 1611004 6122249 := bstep (se 2 (by rfl) ⟨2295843, by rfl⟩ : syracuseStep 6122249 = 4591687) B4591687
theorem B6122735 : Blo 1611004 6122735 := bstep (se 1 (by rfl) ⟨4592051, by rfl⟩ : syracuseStep 6122735 = 9184103) B9184103
theorem B4591151 : Blo 1611004 4591151 := bstep (se 1 (by rfl) ⟨3443363, by rfl⟩ : syracuseStep 4591151 = 6886727) B6886727
theorem B81670133 : Blo 1611004 81670133 := bstep (se 5 (by rfl) ⟨3828287, by rfl⟩ : syracuseStep 81670133 = 7656575) B7656575
theorem B47133677 : Blo 1611004 47133677 := bstep (se 3 (by rfl) ⟨8837564, by rfl⟩ : syracuseStep 47133677 = 17675129) B17675129
theorem B3627233 : Blo 1611004 3627233 := bstep (se 2 (by rfl) ⟨1360212, by rfl⟩ : syracuseStep 3627233 = 2720425) B2720425
theorem B20937023 : Blo 1611004 20937023 := bstep (se 1 (by rfl) ⟨15702767, by rfl⟩ : syracuseStep 20937023 = 31405535) B31405535
theorem B44120447 : Blo 1611004 44120447 := bstep (se 1 (by rfl) ⟨33090335, by rfl⟩ : syracuseStep 44120447 = 66180671) B66180671
theorem B2718697 : Blo 1611004 2718697 := bstep (se 2 (by rfl) ⟨1019511, by rfl⟩ : syracuseStep 2718697 = 2039023) B2039023
theorem B2418155 : Blo 1611004 2418155 := bstep (se 1 (by rfl) ⟨1813616, by rfl⟩ : syracuseStep 2418155 = 3627233) B3627233
theorem B4081499 : Blo 1611004 4081499 := bstep (se 1 (by rfl) ⟨3061124, by rfl⟩ : syracuseStep 4081499 = 6122249) B6122249
theorem B4081823 : Blo 1611004 4081823 := bstep (se 1 (by rfl) ⟨3061367, by rfl⟩ : syracuseStep 4081823 = 6122735) B6122735
theorem B54446755 : Blo 1611004 54446755 := bstep (se 1 (by rfl) ⟨40835066, by rfl⟩ : syracuseStep 54446755 = 81670133) B81670133
theorem B3624929 : Blo 1611004 3624929 := bstep (se 2 (by rfl) ⟨1359348, by rfl⟩ : syracuseStep 3624929 = 2718697) B2718697
theorem B29413631 : Blo 1611004 29413631 := bstep (se 1 (by rfl) ⟨22060223, by rfl⟩ : syracuseStep 29413631 = 44120447) B44120447
theorem B3060767 : Blo 1611004 3060767 := bstep (se 1 (by rfl) ⟨2295575, by rfl⟩ : syracuseStep 3060767 = 4591151) B4591151
theorem B31422451 : Blo 1611004 31422451 := bstep (se 1 (by rfl) ⟨23566838, by rfl⟩ : syracuseStep 31422451 = 47133677) B47133677
theorem B13958015 : Blo 1611004 13958015 := bstep (se 1 (by rfl) ⟨10468511, by rfl⟩ : syracuseStep 13958015 = 20937023) B20937023
theorem B2720999 : Blo 1611004 2720999 := bstep (se 1 (by rfl) ⟨2040749, by rfl⟩ : syracuseStep 2720999 = 4081499) B4081499
theorem B2721215 : Blo 1611004 2721215 := bstep (se 1 (by rfl) ⟨2040911, by rfl⟩ : syracuseStep 2721215 = 4081823) B4081823
theorem B41896601 : Blo 1611004 41896601 := bstep (se 2 (by rfl) ⟨15711225, by rfl⟩ : syracuseStep 41896601 = 31422451) B31422451
theorem B8162045 : Blo 1611004 8162045 := bstep (se 3 (by rfl) ⟨1530383, by rfl⟩ : syracuseStep 8162045 = 3060767) B3060767
theorem B37221373 : Blo 1611004 37221373 := bstep (se 3 (by rfl) ⟨6979007, by rfl⟩ : syracuseStep 37221373 = 13958015) B13958015
theorem B19609087 : Blo 1611004 19609087 := bstep (se 1 (by rfl) ⟨14706815, by rfl⟩ : syracuseStep 19609087 = 29413631) B29413631
theorem B72595673 : Blo 1611004 72595673 := bstep (se 2 (by rfl) ⟨27223377, by rfl⟩ : syracuseStep 72595673 = 54446755) B54446755
theorem B1612103 : Blo 1611004 1612103 := bstep (se 1 (by rfl) ⟨1209077, by rfl⟩ : syracuseStep 1612103 = 2418155) B2418155
theorem B2416619 : Blo 1611004 2416619 := bstep (se 1 (by rfl) ⟨1812464, by rfl⟩ : syracuseStep 2416619 = 3624929) B3624929
theorem B49628497 : Blo 1611004 49628497 := bstep (se 2 (by rfl) ⟨18610686, by rfl⟩ : syracuseStep 49628497 = 37221373) B37221373
theorem B5441363 : Blo 1611004 5441363 := bstep (se 1 (by rfl) ⟨4081022, by rfl⟩ : syracuseStep 5441363 = 8162045) B8162045
theorem B1813999 : Blo 1611004 1813999 := bstep (se 1 (by rfl) ⟨1360499, by rfl⟩ : syracuseStep 1813999 = 2720999) B2720999
theorem B1814143 : Blo 1611004 1814143 := bstep (se 1 (by rfl) ⟨1360607, by rfl⟩ : syracuseStep 1814143 = 2721215) B2721215
theorem B27931067 : Blo 1611004 27931067 := bstep (se 1 (by rfl) ⟨20948300, by rfl⟩ : syracuseStep 27931067 = 41896601) B41896601
theorem B26145449 : Blo 1611004 26145449 := bstep (se 2 (by rfl) ⟨9804543, by rfl⟩ : syracuseStep 26145449 = 19609087) B19609087
theorem B1611079 : Blo 1611004 1611079 := bstep (se 1 (by rfl) ⟨1208309, by rfl⟩ : syracuseStep 1611079 = 2416619) B2416619
theorem B48397115 : Blo 1611004 48397115 := bstep (se 1 (by rfl) ⟨36297836, by rfl⟩ : syracuseStep 48397115 = 72595673) B72595673
theorem B18620711 : Blo 1611004 18620711 := bstep (se 1 (by rfl) ⟨13965533, by rfl⟩ : syracuseStep 18620711 = 27931067) B27931067
theorem B2418665 : Blo 1611004 2418665 := bstep (se 2 (by rfl) ⟨906999, by rfl⟩ : syracuseStep 2418665 = 1813999) B1813999
theorem B2418857 : Blo 1611004 2418857 := bstep (se 2 (by rfl) ⟨907071, by rfl⟩ : syracuseStep 2418857 = 1814143) B1814143
theorem B66171329 : Blo 1611004 66171329 := bstep (se 2 (by rfl) ⟨24814248, by rfl⟩ : syracuseStep 66171329 = 49628497) B49628497
theorem B32264743 : Blo 1611004 32264743 := bstep (se 1 (by rfl) ⟨24198557, by rfl⟩ : syracuseStep 32264743 = 48397115) B48397115
theorem B17430299 : Blo 1611004 17430299 := bstep (se 1 (by rfl) ⟨13072724, by rfl⟩ : syracuseStep 17430299 = 26145449) B26145449
theorem B3627575 : Blo 1611004 3627575 := bstep (se 1 (by rfl) ⟨2720681, by rfl⟩ : syracuseStep 3627575 = 5441363) B5441363
theorem B44114219 : Blo 1611004 44114219 := bstep (se 1 (by rfl) ⟨33085664, by rfl⟩ : syracuseStep 44114219 = 66171329) B66171329
theorem B2418383 : Blo 1611004 2418383 := bstep (se 1 (by rfl) ⟨1813787, by rfl⟩ : syracuseStep 2418383 = 3627575) B3627575
theorem B12413807 : Blo 1611004 12413807 := bstep (se 1 (by rfl) ⟨9310355, by rfl⟩ : syracuseStep 12413807 = 18620711) B18620711
theorem B43019657 : Blo 1611004 43019657 := bstep (se 2 (by rfl) ⟨16132371, by rfl⟩ : syracuseStep 43019657 = 32264743) B32264743
theorem B11620199 : Blo 1611004 11620199 := bstep (se 1 (by rfl) ⟨8715149, by rfl⟩ : syracuseStep 11620199 = 17430299) B17430299
theorem B1612443 : Blo 1611004 1612443 := bstep (se 1 (by rfl) ⟨1209332, by rfl⟩ : syracuseStep 1612443 = 2418665) B2418665
theorem B1612571 : Blo 1611004 1612571 := bstep (se 1 (by rfl) ⟨1209428, by rfl⟩ : syracuseStep 1612571 = 2418857) B2418857
theorem B29409479 : Blo 1611004 29409479 := bstep (se 1 (by rfl) ⟨22057109, by rfl⟩ : syracuseStep 29409479 = 44114219) B44114219
theorem B8275871 : Blo 1611004 8275871 := bstep (se 1 (by rfl) ⟨6206903, by rfl⟩ : syracuseStep 8275871 = 12413807) B12413807
theorem B7746799 : Blo 1611004 7746799 := bstep (se 1 (by rfl) ⟨5810099, by rfl⟩ : syracuseStep 7746799 = 11620199) B11620199
theorem B1612255 : Blo 1611004 1612255 := bstep (se 1 (by rfl) ⟨1209191, by rfl⟩ : syracuseStep 1612255 = 2418383) B2418383
theorem B28679771 : Blo 1611004 28679771 := bstep (se 1 (by rfl) ⟨21509828, by rfl⟩ : syracuseStep 28679771 = 43019657) B43019657
theorem B19606319 : Blo 1611004 19606319 := bstep (se 1 (by rfl) ⟨14704739, by rfl⟩ : syracuseStep 19606319 = 29409479) B29409479
theorem B5517247 : Blo 1611004 5517247 := bstep (se 1 (by rfl) ⟨4137935, by rfl⟩ : syracuseStep 5517247 = 8275871) B8275871
theorem B76479389 : Blo 1611004 76479389 := bstep (se 3 (by rfl) ⟨14339885, by rfl⟩ : syracuseStep 76479389 = 28679771) B28679771
theorem B10329065 : Blo 1611004 10329065 := bstep (se 2 (by rfl) ⟨3873399, by rfl⟩ : syracuseStep 10329065 = 7746799) B7746799
theorem B13070879 : Blo 1611004 13070879 := bstep (se 1 (by rfl) ⟨9803159, by rfl⟩ : syracuseStep 13070879 = 19606319) B19606319
theorem B6886043 : Blo 1611004 6886043 := bstep (se 1 (by rfl) ⟨5164532, by rfl⟩ : syracuseStep 6886043 = 10329065) B10329065
theorem B50986259 : Blo 1611004 50986259 := bstep (se 1 (by rfl) ⟨38239694, by rfl⟩ : syracuseStep 50986259 = 76479389) B76479389
theorem B7356329 : Blo 1611004 7356329 := bstep (se 2 (by rfl) ⟨2758623, by rfl⟩ : syracuseStep 7356329 = 5517247) B5517247
theorem B33990839 : Blo 1611004 33990839 := bstep (se 1 (by rfl) ⟨25493129, by rfl⟩ : syracuseStep 33990839 = 50986259) B50986259
theorem B4590695 : Blo 1611004 4590695 := bstep (se 1 (by rfl) ⟨3443021, by rfl⟩ : syracuseStep 4590695 = 6886043) B6886043
theorem B4904219 : Blo 1611004 4904219 := bstep (se 1 (by rfl) ⟨3678164, by rfl⟩ : syracuseStep 4904219 = 7356329) B7356329
theorem B8713919 : Blo 1611004 8713919 := bstep (se 1 (by rfl) ⟨6535439, by rfl⟩ : syracuseStep 8713919 = 13070879) B13070879
theorem B3269479 : Blo 1611004 3269479 := bstep (se 1 (by rfl) ⟨2452109, by rfl⟩ : syracuseStep 3269479 = 4904219) B4904219
theorem B22660559 : Blo 1611004 22660559 := bstep (se 1 (by rfl) ⟨16995419, by rfl⟩ : syracuseStep 22660559 = 33990839) B33990839
theorem B12241853 : Blo 1611004 12241853 := bstep (se 3 (by rfl) ⟨2295347, by rfl⟩ : syracuseStep 12241853 = 4590695) B4590695
theorem B23237117 : Blo 1611004 23237117 := bstep (se 3 (by rfl) ⟨4356959, by rfl⟩ : syracuseStep 23237117 = 8713919) B8713919
theorem B15491411 : Blo 1611004 15491411 := bstep (se 1 (by rfl) ⟨11618558, by rfl⟩ : syracuseStep 15491411 = 23237117) B23237117
theorem B15107039 : Blo 1611004 15107039 := bstep (se 1 (by rfl) ⟨11330279, by rfl⟩ : syracuseStep 15107039 = 22660559) B22660559
theorem B4359305 : Blo 1611004 4359305 := bstep (se 2 (by rfl) ⟨1634739, by rfl⟩ : syracuseStep 4359305 = 3269479) B3269479
theorem B8161235 : Blo 1611004 8161235 := bstep (se 1 (by rfl) ⟨6120926, by rfl⟩ : syracuseStep 8161235 = 12241853) B12241853
theorem B5440823 : Blo 1611004 5440823 := bstep (se 1 (by rfl) ⟨4080617, by rfl⟩ : syracuseStep 5440823 = 8161235) B8161235
theorem B10071359 : Blo 1611004 10071359 := bstep (se 1 (by rfl) ⟨7553519, by rfl⟩ : syracuseStep 10071359 = 15107039) B15107039
theorem B10327607 : Blo 1611004 10327607 := bstep (se 1 (by rfl) ⟨7745705, by rfl⟩ : syracuseStep 10327607 = 15491411) B15491411
theorem B2906203 : Blo 1611004 2906203 := bstep (se 1 (by rfl) ⟨2179652, by rfl⟩ : syracuseStep 2906203 = 4359305) B4359305
theorem B3874937 : Blo 1611004 3874937 := bstep (se 2 (by rfl) ⟨1453101, by rfl⟩ : syracuseStep 3874937 = 2906203) B2906203
theorem B6885071 : Blo 1611004 6885071 := bstep (se 1 (by rfl) ⟨5163803, by rfl⟩ : syracuseStep 6885071 = 10327607) B10327607
theorem B107427829 : Blo 1611004 107427829 := bstep (se 5 (by rfl) ⟨5035679, by rfl⟩ : syracuseStep 107427829 = 10071359) B10071359
theorem B3627215 : Blo 1611004 3627215 := bstep (se 1 (by rfl) ⟨2720411, by rfl⟩ : syracuseStep 3627215 = 5440823) B5440823
theorem B2418143 : Blo 1611004 2418143 := bstep (se 1 (by rfl) ⟨1813607, by rfl⟩ : syracuseStep 2418143 = 3627215) B3627215
theorem B4590047 : Blo 1611004 4590047 := bstep (se 1 (by rfl) ⟨3442535, by rfl⟩ : syracuseStep 4590047 = 6885071) B6885071
theorem B10333165 : Blo 1611004 10333165 := bstep (se 3 (by rfl) ⟨1937468, by rfl⟩ : syracuseStep 10333165 = 3874937) B3874937
theorem B143237105 : Blo 1611004 143237105 := bstep (se 2 (by rfl) ⟨53713914, by rfl⟩ : syracuseStep 143237105 = 107427829) B107427829
theorem B3060031 : Blo 1611004 3060031 := bstep (se 1 (by rfl) ⟨2295023, by rfl⟩ : syracuseStep 3060031 = 4590047) B4590047
theorem B95491403 : Blo 1611004 95491403 := bstep (se 1 (by rfl) ⟨71618552, by rfl⟩ : syracuseStep 95491403 = 143237105) B143237105
theorem B1612095 : Blo 1611004 1612095 := bstep (se 1 (by rfl) ⟨1209071, by rfl⟩ : syracuseStep 1612095 = 2418143) B2418143
theorem B13777553 : Blo 1611004 13777553 := bstep (se 2 (by rfl) ⟨5166582, by rfl⟩ : syracuseStep 13777553 = 10333165) B10333165
theorem B4080041 : Blo 1611004 4080041 := bstep (se 2 (by rfl) ⟨1530015, by rfl⟩ : syracuseStep 4080041 = 3060031) B3060031
theorem B63660935 : Blo 1611004 63660935 := bstep (se 1 (by rfl) ⟨47745701, by rfl⟩ : syracuseStep 63660935 = 95491403) B95491403
theorem B9185035 : Blo 1611004 9185035 := bstep (se 1 (by rfl) ⟨6888776, by rfl⟩ : syracuseStep 9185035 = 13777553) B13777553
theorem B2720027 : Blo 1611004 2720027 := bstep (se 1 (by rfl) ⟨2040020, by rfl⟩ : syracuseStep 2720027 = 4080041) B4080041
theorem B12246713 : Blo 1611004 12246713 := bstep (se 2 (by rfl) ⟨4592517, by rfl⟩ : syracuseStep 12246713 = 9185035) B9185035
theorem B169762493 : Blo 1611004 169762493 := bstep (se 3 (by rfl) ⟨31830467, by rfl⟩ : syracuseStep 169762493 = 63660935) B63660935
theorem B113174995 : Blo 1611004 113174995 := bstep (se 1 (by rfl) ⟨84881246, by rfl⟩ : syracuseStep 113174995 = 169762493) B169762493
theorem B1813351 : Blo 1611004 1813351 := bstep (se 1 (by rfl) ⟨1360013, by rfl⟩ : syracuseStep 1813351 = 2720027) B2720027
theorem B8164475 : Blo 1611004 8164475 := bstep (se 1 (by rfl) ⟨6123356, by rfl⟩ : syracuseStep 8164475 = 12246713) B12246713
theorem B2417801 : Blo 1611004 2417801 := bstep (se 2 (by rfl) ⟨906675, by rfl⟩ : syracuseStep 2417801 = 1813351) B1813351
theorem B150899993 : Blo 1611004 150899993 := bstep (se 2 (by rfl) ⟨56587497, by rfl⟩ : syracuseStep 150899993 = 113174995) B113174995
theorem B5442983 : Blo 1611004 5442983 := bstep (se 1 (by rfl) ⟨4082237, by rfl⟩ : syracuseStep 5442983 = 8164475) B8164475
theorem B100599995 : Blo 1611004 100599995 := bstep (se 1 (by rfl) ⟨75449996, by rfl⟩ : syracuseStep 100599995 = 150899993) B150899993
theorem B1611867 : Blo 1611004 1611867 := bstep (se 1 (by rfl) ⟨1208900, by rfl⟩ : syracuseStep 1611867 = 2417801) B2417801
theorem B3628655 : Blo 1611004 3628655 := bstep (se 1 (by rfl) ⟨2721491, by rfl⟩ : syracuseStep 3628655 = 5442983) B5442983
theorem B2419103 : Blo 1611004 2419103 := bstep (se 1 (by rfl) ⟨1814327, by rfl⟩ : syracuseStep 2419103 = 3628655) B3628655
theorem B67066663 : Blo 1611004 67066663 := bstep (se 1 (by rfl) ⟨50299997, by rfl⟩ : syracuseStep 67066663 = 100599995) B100599995
theorem B89422217 : Blo 1611004 89422217 := bstep (se 2 (by rfl) ⟨33533331, by rfl⟩ : syracuseStep 89422217 = 67066663) B67066663
theorem B1612735 : Blo 1611004 1612735 := bstep (se 1 (by rfl) ⟨1209551, by rfl⟩ : syracuseStep 1612735 = 2419103) B2419103
theorem B59614811 : Blo 1611004 59614811 := bstep (se 1 (by rfl) ⟨44711108, by rfl⟩ : syracuseStep 59614811 = 89422217) B89422217
theorem B39743207 : Blo 1611004 39743207 := bstep (se 1 (by rfl) ⟨29807405, by rfl⟩ : syracuseStep 39743207 = 59614811) B59614811
theorem B26495471 : Blo 1611004 26495471 := bstep (se 1 (by rfl) ⟨19871603, by rfl⟩ : syracuseStep 26495471 = 39743207) B39743207
theorem B70654589 : Blo 1611004 70654589 := bstep (se 3 (by rfl) ⟨13247735, by rfl⟩ : syracuseStep 70654589 = 26495471) B26495471
theorem B47103059 : Blo 1611004 47103059 := bstep (se 1 (by rfl) ⟨35327294, by rfl⟩ : syracuseStep 47103059 = 70654589) B70654589
theorem B31402039 : Blo 1611004 31402039 := bstep (se 1 (by rfl) ⟨23551529, by rfl⟩ : syracuseStep 31402039 = 47103059) B47103059
theorem B41869385 : Blo 1611004 41869385 := bstep (se 2 (by rfl) ⟨15701019, by rfl⟩ : syracuseStep 41869385 = 31402039) B31402039
theorem B27912923 : Blo 1611004 27912923 := bstep (se 1 (by rfl) ⟨20934692, by rfl⟩ : syracuseStep 27912923 = 41869385) B41869385
theorem B18608615 : Blo 1611004 18608615 := bstep (se 1 (by rfl) ⟨13956461, by rfl⟩ : syracuseStep 18608615 = 27912923) B27912923
theorem B12405743 : Blo 1611004 12405743 := bstep (se 1 (by rfl) ⟨9304307, by rfl⟩ : syracuseStep 12405743 = 18608615) B18608615
theorem B8270495 : Blo 1611004 8270495 := bstep (se 1 (by rfl) ⟨6202871, by rfl⟩ : syracuseStep 8270495 = 12405743) B12405743
theorem B5513663 : Blo 1611004 5513663 := bstep (se 1 (by rfl) ⟨4135247, by rfl⟩ : syracuseStep 5513663 = 8270495) B8270495
theorem B3675775 : Blo 1611004 3675775 := bstep (se 1 (by rfl) ⟨2756831, by rfl⟩ : syracuseStep 3675775 = 5513663) B5513663
theorem B4901033 : Blo 1611004 4901033 := bstep (se 2 (by rfl) ⟨1837887, by rfl⟩ : syracuseStep 4901033 = 3675775) B3675775
theorem B13069421 : Blo 1611004 13069421 := bstep (se 3 (by rfl) ⟨2450516, by rfl⟩ : syracuseStep 13069421 = 4901033) B4901033
theorem B8712947 : Blo 1611004 8712947 := bstep (se 1 (by rfl) ⟨6534710, by rfl⟩ : syracuseStep 8712947 = 13069421) B13069421
theorem B5808631 : Blo 1611004 5808631 := bstep (se 1 (by rfl) ⟨4356473, by rfl⟩ : syracuseStep 5808631 = 8712947) B8712947
theorem B7744841 : Blo 1611004 7744841 := bstep (se 2 (by rfl) ⟨2904315, by rfl⟩ : syracuseStep 7744841 = 5808631) B5808631
theorem B5163227 : Blo 1611004 5163227 := bstep (se 1 (by rfl) ⟨3872420, by rfl⟩ : syracuseStep 5163227 = 7744841) B7744841
theorem B3442151 : Blo 1611004 3442151 := bstep (se 1 (by rfl) ⟨2581613, by rfl⟩ : syracuseStep 3442151 = 5163227) B5163227
theorem B2294767 : Blo 1611004 2294767 := bstep (se 1 (by rfl) ⟨1721075, by rfl⟩ : syracuseStep 2294767 = 3442151) B3442151
theorem B3059689 : Blo 1611004 3059689 := bstep (se 2 (by rfl) ⟨1147383, by rfl⟩ : syracuseStep 3059689 = 2294767) B2294767
theorem B4079585 : Blo 1611004 4079585 := bstep (se 2 (by rfl) ⟨1529844, by rfl⟩ : syracuseStep 4079585 = 3059689) B3059689
theorem B2719723 : Blo 1611004 2719723 := bstep (se 1 (by rfl) ⟨2039792, by rfl⟩ : syracuseStep 2719723 = 4079585) B4079585
theorem B3626297 : Blo 1611004 3626297 := bstep (se 2 (by rfl) ⟨1359861, by rfl⟩ : syracuseStep 3626297 = 2719723) B2719723
theorem B2417531 : Blo 1611004 2417531 := bstep (se 1 (by rfl) ⟨1813148, by rfl⟩ : syracuseStep 2417531 = 3626297) B3626297
theorem B1611687 : Blo 1611004 1611687 := bstep (se 1 (by rfl) ⟨1208765, by rfl⟩ : syracuseStep 1611687 = 2417531) B2417531

theorem C0 (j : ℕ) (h1 : 402751 ≤ j) (h2 : j ≤ 403250) : Blo 1611004 (4 * j + 3) := by
  interval_cases j
  · exact B1611007
  · exact B1611011
  · exact B1611015
  · exact B1611019
  · exact B1611023
  · exact B1611027
  · exact B1611031
  · exact B1611035
  · exact B1611039
  · exact B1611043
  · exact B1611047
  · exact B1611051
  · exact B1611055
  · exact B1611059
  · exact B1611063
  · exact B1611067
  · exact B1611071
  · exact B1611075
  · exact B1611079
  · exact B1611083
  · exact B1611087
  · exact B1611091
  · exact B1611095
  · exact B1611099
  · exact B1611103
  · exact B1611107
  · exact B1611111
  · exact B1611115
  · exact B1611119
  · exact B1611123
  · exact B1611127
  · exact B1611131
  · exact B1611135
  · exact B1611139
  · exact B1611143
  · exact B1611147
  · exact B1611151
  · exact B1611155
  · exact B1611159
  · exact B1611163
  · exact B1611167
  · exact B1611171
  · exact B1611175
  · exact B1611179
  · exact B1611183
  · exact B1611187
  · exact B1611191
  · exact B1611195
  · exact B1611199
  · exact B1611203
  · exact B1611207
  · exact B1611211
  · exact B1611215
  · exact B1611219
  · exact B1611223
  · exact B1611227
  · exact B1611231
  · exact B1611235
  · exact B1611239
  · exact B1611243
  · exact B1611247
  · exact B1611251
  · exact B1611255
  · exact B1611259
  · exact B1611263
  · exact B1611267
  · exact B1611271
  · exact B1611275
  · exact B1611279
  · exact B1611283
  · exact B1611287
  · exact B1611291
  · exact B1611295
  · exact B1611299
  · exact B1611303
  · exact B1611307
  · exact B1611311
  · exact B1611315
  · exact B1611319
  · exact B1611323
  · exact B1611327
  · exact B1611331
  · exact B1611335
  · exact B1611339
  · exact B1611343
  · exact B1611347
  · exact B1611351
  · exact B1611355
  · exact B1611359
  · exact B1611363
  · exact B1611367
  · exact B1611371
  · exact B1611375
  · exact B1611379
  · exact B1611383
  · exact B1611387
  · exact B1611391
  · exact B1611395
  · exact B1611399
  · exact B1611403
  · exact B1611407
  · exact B1611411
  · exact B1611415
  · exact B1611419
  · exact B1611423
  · exact B1611427
  · exact B1611431
  · exact B1611435
  · exact B1611439
  · exact B1611443
  · exact B1611447
  · exact B1611451
  · exact B1611455
  · exact B1611459
  · exact B1611463
  · exact B1611467
  · exact B1611471
  · exact B1611475
  · exact B1611479
  · exact B1611483
  · exact B1611487
  · exact B1611491
  · exact B1611495
  · exact B1611499
  · exact B1611503
  · exact B1611507
  · exact B1611511
  · exact B1611515
  · exact B1611519
  · exact B1611523
  · exact B1611527
  · exact B1611531
  · exact B1611535
  · exact B1611539
  · exact B1611543
  · exact B1611547
  · exact B1611551
  · exact B1611555
  · exact B1611559
  · exact B1611563
  · exact B1611567
  · exact B1611571
  · exact B1611575
  · exact B1611579
  · exact B1611583
  · exact B1611587
  · exact B1611591
  · exact B1611595
  · exact B1611599
  · exact B1611603
  · exact B1611607
  · exact B1611611
  · exact B1611615
  · exact B1611619
  · exact B1611623
  · exact B1611627
  · exact B1611631
  · exact B1611635
  · exact B1611639
  · exact B1611643
  · exact B1611647
  · exact B1611651
  · exact B1611655
  · exact B1611659
  · exact B1611663
  · exact B1611667
  · exact B1611671
  · exact B1611675
  · exact B1611679
  · exact B1611683
  · exact B1611687
  · exact B1611691
  · exact B1611695
  · exact B1611699
  · exact B1611703
  · exact B1611707
  · exact B1611711
  · exact B1611715
  · exact B1611719
  · exact B1611723
  · exact B1611727
  · exact B1611731
  · exact B1611735
  · exact B1611739
  · exact B1611743
  · exact B1611747
  · exact B1611751
  · exact B1611755
  · exact B1611759
  · exact B1611763
  · exact B1611767
  · exact B1611771
  · exact B1611775
  · exact B1611779
  · exact B1611783
  · exact B1611787
  · exact B1611791
  · exact B1611795
  · exact B1611799
  · exact B1611803
  · exact B1611807
  · exact B1611811
  · exact B1611815
  · exact B1611819
  · exact B1611823
  · exact B1611827
  · exact B1611831
  · exact B1611835
  · exact B1611839
  · exact B1611843
  · exact B1611847
  · exact B1611851
  · exact B1611855
  · exact B1611859
  · exact B1611863
  · exact B1611867
  · exact B1611871
  · exact B1611875
  · exact B1611879
  · exact B1611883
  · exact B1611887
  · exact B1611891
  · exact B1611895
  · exact B1611899
  · exact B1611903
  · exact B1611907
  · exact B1611911
  · exact B1611915
  · exact B1611919
  · exact B1611923
  · exact B1611927
  · exact B1611931
  · exact B1611935
  · exact B1611939
  · exact B1611943
  · exact B1611947
  · exact B1611951
  · exact B1611955
  · exact B1611959
  · exact B1611963
  · exact B1611967
  · exact B1611971
  · exact B1611975
  · exact B1611979
  · exact B1611983
  · exact B1611987
  · exact B1611991
  · exact B1611995
  · exact B1611999
  · exact B1612003
  · exact B1612007
  · exact B1612011
  · exact B1612015
  · exact B1612019
  · exact B1612023
  · exact B1612027
  · exact B1612031
  · exact B1612035
  · exact B1612039
  · exact B1612043
  · exact B1612047
  · exact B1612051
  · exact B1612055
  · exact B1612059
  · exact B1612063
  · exact B1612067
  · exact B1612071
  · exact B1612075
  · exact B1612079
  · exact B1612083
  · exact B1612087
  · exact B1612091
  · exact B1612095
  · exact B1612099
  · exact B1612103
  · exact B1612107
  · exact B1612111
  · exact B1612115
  · exact B1612119
  · exact B1612123
  · exact B1612127
  · exact B1612131
  · exact B1612135
  · exact B1612139
  · exact B1612143
  · exact B1612147
  · exact B1612151
  · exact B1612155
  · exact B1612159
  · exact B1612163
  · exact B1612167
  · exact B1612171
  · exact B1612175
  · exact B1612179
  · exact B1612183
  · exact B1612187
  · exact B1612191
  · exact B1612195
  · exact B1612199
  · exact B1612203
  · exact B1612207
  · exact B1612211
  · exact B1612215
  · exact B1612219
  · exact B1612223
  · exact B1612227
  · exact B1612231
  · exact B1612235
  · exact B1612239
  · exact B1612243
  · exact B1612247
  · exact B1612251
  · exact B1612255
  · exact B1612259
  · exact B1612263
  · exact B1612267
  · exact B1612271
  · exact B1612275
  · exact B1612279
  · exact B1612283
  · exact B1612287
  · exact B1612291
  · exact B1612295
  · exact B1612299
  · exact B1612303
  · exact B1612307
  · exact B1612311
  · exact B1612315
  · exact B1612319
  · exact B1612323
  · exact B1612327
  · exact B1612331
  · exact B1612335
  · exact B1612339
  · exact B1612343
  · exact B1612347
  · exact B1612351
  · exact B1612355
  · exact B1612359
  · exact B1612363
  · exact B1612367
  · exact B1612371
  · exact B1612375
  · exact B1612379
  · exact B1612383
  · exact B1612387
  · exact B1612391
  · exact B1612395
  · exact B1612399
  · exact B1612403
  · exact B1612407
  · exact B1612411
  · exact B1612415
  · exact B1612419
  · exact B1612423
  · exact B1612427
  · exact B1612431
  · exact B1612435
  · exact B1612439
  · exact B1612443
  · exact B1612447
  · exact B1612451
  · exact B1612455
  · exact B1612459
  · exact B1612463
  · exact B1612467
  · exact B1612471
  · exact B1612475
  · exact B1612479
  · exact B1612483
  · exact B1612487
  · exact B1612491
  · exact B1612495
  · exact B1612499
  · exact B1612503
  · exact B1612507
  · exact B1612511
  · exact B1612515
  · exact B1612519
  · exact B1612523
  · exact B1612527
  · exact B1612531
  · exact B1612535
  · exact B1612539
  · exact B1612543
  · exact B1612547
  · exact B1612551
  · exact B1612555
  · exact B1612559
  · exact B1612563
  · exact B1612567
  · exact B1612571
  · exact B1612575
  · exact B1612579
  · exact B1612583
  · exact B1612587
  · exact B1612591
  · exact B1612595
  · exact B1612599
  · exact B1612603
  · exact B1612607
  · exact B1612611
  · exact B1612615
  · exact B1612619
  · exact B1612623
  · exact B1612627
  · exact B1612631
  · exact B1612635
  · exact B1612639
  · exact B1612643
  · exact B1612647
  · exact B1612651
  · exact B1612655
  · exact B1612659
  · exact B1612663
  · exact B1612667
  · exact B1612671
  · exact B1612675
  · exact B1612679
  · exact B1612683
  · exact B1612687
  · exact B1612691
  · exact B1612695
  · exact B1612699
  · exact B1612703
  · exact B1612707
  · exact B1612711
  · exact B1612715
  · exact B1612719
  · exact B1612723
  · exact B1612727
  · exact B1612731
  · exact B1612735
  · exact B1612739
  · exact B1612743
  · exact B1612747
  · exact B1612751
  · exact B1612755
  · exact B1612759
  · exact B1612763
  · exact B1612767
  · exact B1612771
  · exact B1612775
  · exact B1612779
  · exact B1612783
  · exact B1612787
  · exact B1612791
  · exact B1612795
  · exact B1612799
  · exact B1612803
  · exact B1612807
  · exact B1612811
  · exact B1612815
  · exact B1612819
  · exact B1612823
  · exact B1612827
  · exact B1612831
  · exact B1612835
  · exact B1612839
  · exact B1612843
  · exact B1612847
  · exact B1612851
  · exact B1612855
  · exact B1612859
  · exact B1612863
  · exact B1612867
  · exact B1612871
  · exact B1612875
  · exact B1612879
  · exact B1612883
  · exact B1612887
  · exact B1612891
  · exact B1612895
  · exact B1612899
  · exact B1612903
  · exact B1612907
  · exact B1612911
  · exact B1612915
  · exact B1612919
  · exact B1612923
  · exact B1612927
  · exact B1612931
  · exact B1612935
  · exact B1612939
  · exact B1612943
  · exact B1612947
  · exact B1612951
  · exact B1612955
  · exact B1612959
  · exact B1612963
  · exact B1612967
  · exact B1612971
  · exact B1612975
  · exact B1612979
  · exact B1612983
  · exact B1612987
  · exact B1612991
  · exact B1612995
  · exact B1612999
  · exact B1613003

theorem solution (m : ℕ) (hlo : 1611004 ≤ m) (hhi : m ≤ 1613004) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 402751 ≤ j := by omega
    have hj2 : j ≤ 403250 := by omega
    have hb : Blo 1611004 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
